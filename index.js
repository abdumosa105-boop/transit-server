// خادم Fil Bleu (Tours): يدمج GTFS الثابت (الجدول) + GTFS-RT (الوقت الحقيقي)
// يحتاج Node.js 18 أو أحدث
const http = require('http');
const os = require('os');
const { Readable } = require('stream');
const AdmZip = require('adm-zip');
const { parse } = require('csv-parse');
const { parse: parseSync } = require('csv-parse/sync');
const GtfsRT = require('gtfs-realtime-bindings');

const PORT = process.env.PORT || 3000;
const GTFS_URL =
  'https://data.tours-metropole.fr/api/v2/catalog/datasets/horaires-temps-reel-gtfsrt-reseau-filbleu-tmvl/alternative_exports/filbleu_gtfszip';
const TRIP_UPDATES_URL = 'https://data.filbleu.fr/ws-tr/gtfs-rt/opendata/trip-updates';
const ALERTS_URL = 'https://data.filbleu.fr/ws-tr/gtfs-rt/opendata/service-alerts';
const TZ = 'Europe/Paris';
const WINDOW_MS = 120 * 60000;   // نافذة العرض: ساعتان
const FAR_MS = 6 * 3600000;      // أفق الرحلات التالية: 6 ساعات
const MERGE_KM = 0.6;            // ندمج المحطات التي لها الاسم نفسه إن كانت أقرب من 600 م
const PER_LINE = 8;              // أقصى عدد رحلات قادمة لكل (خط + وجهة)

let stations = new Map();   // stationId -> { id, name, lat, lon, stopIds[] }
let alias = new Map();      // معرّف قديم -> معرّف المحطة بعد الدمج
let rawStations = new Map();  // المحطات قبل الدمج (للفحص)
let routes = new Map();     // routeId -> { short, long, type, color }
let trips = new Map();      // tripId -> { route_id, headsign, service_id }
let stopTimes = new Map();  // stopId -> [[tripId, secondsSinceMidnight], ...]
let lastStop = new Map();   // tripId -> { seq, stop }  (المحطة الأخيرة للرحلة)
let tripStops = new Map();  // tripId -> [[seq, stopId, secs], ...] مرتبة
let stopNames = new Map();  // stopId -> اسم المحطة
let stopLines = new Map();  // stopId -> Map(routeId -> Set(serviceId))
let stopStation = new Map();  // stopId -> stationId (بعد الدمج)
let stopCoords = new Map();   // stopId -> [lat, lon]
let shapes = new Map();       // shapeId -> [[lat, lon], ...]
let calendar = [];
let calendarDates = [];
let loadedAt = null;
let stopTimesCount = 0;
const activeCache = new Map();

const norm = (s) =>
  (s || '').normalize('NFD').replace(/[\u0300-\u036f]/g, '').toLowerCase().trim();
const num = (v) =>
  v == null ? null : typeof v === 'number' ? v : v.toNumber ? v.toNumber() : Number(v);

const toSecs = (s) => {
  if (!s) return null;
  const [h, m, sec] = s.split(':').map(Number);
  if (isNaN(h) || isNaN(m)) return null;
  return h * 3600 + m * 60 + (sec || 0);
};

// ───────── توقيت باريس ─────────
function tzOffsetMs(ms) {
  const f = new Intl.DateTimeFormat('en-US', {
    timeZone: TZ, hourCycle: 'h23', year: 'numeric', month: '2-digit', day: '2-digit',
    hour: '2-digit', minute: '2-digit', second: '2-digit',
  });
  const p = Object.fromEntries(f.formatToParts(new Date(ms)).map((x) => [x.type, x.value]));
  return Date.UTC(+p.year, +p.month - 1, +p.day, +p.hour, +p.minute, +p.second) - ms;
}
function parisYMD(ms) {
  const f = new Intl.DateTimeFormat('en-US', { timeZone: TZ, year: 'numeric', month: '2-digit', day: '2-digit' });
  const p = Object.fromEntries(f.formatToParts(new Date(ms)).map((x) => [x.type, x.value]));
  return { y: +p.year, m: +p.month, d: +p.day };
}
function parisMidnight(y, m, d) {
  const guess = Date.UTC(y, m - 1, d, 0, 0, 0);
  const off1 = tzOffsetMs(guess);
  return guess - tzOffsetMs(guess - off1);
}

// ───────── الخدمات النشطة في تاريخ معيّن ─────────
const DAY_NAMES = ['sunday', 'monday', 'tuesday', 'wednesday', 'thursday', 'friday', 'saturday'];
function activeServices(y, m, d) {
  const ymd = `${y}${String(m).padStart(2, '0')}${String(d).padStart(2, '0')}`;
  if (activeCache.has(ymd)) return activeCache.get(ymd);
  const dow = new Date(Date.UTC(y, m - 1, d)).getUTCDay();
  const set = new Set();
  for (const c of calendar) {
    if (c.start_date <= ymd && ymd <= c.end_date && c[DAY_NAMES[dow]] === '1') set.add(c.service_id);
  }
  for (const e of calendarDates) {
    if (e.date !== ymd) continue;
    if (e.exception_type === '1') set.add(e.service_id);
    else if (e.exception_type === '2') set.delete(e.service_id);
  }
  activeCache.set(ymd, set);
  return set;
}

// ───────── قراءة GTFS ─────────
function readCsv(zip, name) {
  const entry = zip.getEntry(name);
  if (!entry) return [];
  return parseSync(entry.getData(), {
    columns: true, skip_empty_lines: true, bom: true, relax_column_count: true, trim: true,
  });
}

async function readStopTimes(zip, keepTrips) {
  const byStop = new Map();
  const last = new Map();
  const tStops = new Map();
  let count = 0;
  const entry = zip.getEntry('stop_times.txt');
  if (!entry) return { byStop, last, count, tStops };
  const parser = Readable.from([entry.getData()], { objectMode: false }).pipe(
    parse({ columns: true, skip_empty_lines: true, bom: true, relax_column_count: true, trim: true })
  );
  for await (const r of parser) {
    if (keepTrips && !keepTrips.has(r.trip_id)) continue;
    const seq = parseInt(r.stop_sequence, 10);
    const cur = last.get(r.trip_id);
    if (!cur || seq > cur.seq) last.set(r.trip_id, { seq, stop: r.stop_id });
    const secs = toSecs(r.arrival_time) ?? toSecs(r.departure_time);
    if (secs == null) continue;
    let arr = byStop.get(r.stop_id);
    if (!arr) { arr = []; byStop.set(r.stop_id, arr); }
    arr.push([r.trip_id, secs]);
    let ts = tStops.get(r.trip_id);
    if (!ts) { ts = []; tStops.set(r.trip_id, ts); }
    ts.push([seq, r.stop_id, secs]);
    count++;
  }
  for (const ts of tStops.values()) ts.sort((x, y) => x[0] - y[0]);
  return { byStop, last, count, tStops };
}

// الخطوط التي تخدم مجموعة توقفات
function linesOf(stopIds) {
  const set = new Set();
  for (const sid of stopIds) {
    for (const [tripId] of stopTimes.get(sid) || []) {
      const tr = trips.get(tripId);
      const r = tr && routes.get(tr.route_id);
      if (r && r.short) set.add(r.short);
    }
  }
  return [...set].sort((a, b) => a.localeCompare(b, undefined, { numeric: true }));
}

async function readShapes(zip, keepShapes) {
  const raw = new Map();
  const entry = zip.getEntry('shapes.txt');
  if (!entry) return raw;
  const parser = Readable.from([entry.getData()], { objectMode: false }).pipe(
    parse({ columns: true, skip_empty_lines: true, bom: true, relax_column_count: true, trim: true })
  );
  for await (const r of parser) {
    if (keepShapes && !keepShapes.has(r.shape_id)) continue;
    const lat = parseFloat(r.shape_pt_lat), lon = parseFloat(r.shape_pt_lon);
    const seq = parseInt(r.shape_pt_sequence, 10);
    if (isNaN(lat) || isNaN(lon)) continue;
    let a = raw.get(r.shape_id);
    if (!a) { a = []; raw.set(r.shape_id, a); }
    a.push([seq, lat, lon]);
  }
  const out = new Map();
  for (const [id, a] of raw) {
    a.sort((x, y) => x[0] - y[0]);
    out.set(id, a.map((x) => [x[1], x[2]]));
  }
  return out;
}

async function loadStatic() {
  console.log('تحميل جدول GTFS الثابت...');
  const res = await fetch(GTFS_URL);
  if (!res.ok) throw new Error('GTFS HTTP ' + res.status);
  const zip = new AdmZip(Buffer.from(await res.arrayBuffer()));

  const stops = readCsv(zip, 'stops.txt');
  const byId = new Map(stops.map((s) => [s.stop_id, s]));
  const st = new Map();
  for (const s of stops) {
    if (s.location_type && s.location_type !== '0') continue;
    const sid = s.parent_station && byId.has(s.parent_station) ? s.parent_station : s.stop_id;
    const base = byId.get(sid) || s;
    if (!st.has(sid)) {
      let lat = parseFloat(base.stop_lat), lon = parseFloat(base.stop_lon);
      if (isNaN(lat) || isNaN(lon)) { lat = parseFloat(s.stop_lat); lon = parseFloat(s.stop_lon); }
      st.set(sid, { id: sid, name: base.stop_name, lat, lon, stopIds: [] });
    }
    st.get(sid).stopIds.push(s.stop_id);
  }

  // دمج المحطات القريبة (أقل من 300 م) التي لها الاسم نفسه: اتجاها الذهاب والعودة
  const groups = new Map();
  for (const s of st.values()) {
    const k = norm(s.name);
    if (!groups.has(k)) groups.set(k, []);
    groups.get(k).push(s);
  }
  const merged = new Map();
  const al = new Map();
  for (const list of groups.values()) {
    const reps = [];
    for (const s of list) {
      const near = reps.find(
        (r) => !isNaN(s.lat) && !isNaN(r.lat) && distKm(s.lat, s.lon, r.lat, r.lon) <= MERGE_KM
      );
      if (near) {
        near.stopIds.push(...s.stopIds);
        al.set(s.id, near.id);
      } else {
        reps.push({ ...s, stopIds: [...s.stopIds] });
      }
    }
    for (const r of reps) merged.set(r.id, r);
  }

  const rt = new Map();
  for (const r of readCsv(zip, 'routes.txt')) {
    rt.set(r.route_id, { short: r.route_short_name, long: r.route_long_name, type: r.route_type, color: r.route_color });
  }
  const tr = new Map();
  for (const t of readCsv(zip, 'trips.txt')) {
    tr.set(t.trip_id, { route_id: t.route_id, headsign: t.trip_headsign, service_id: t.service_id, shape_id: t.shape_id });
  }
  const cal = readCsv(zip, 'calendar.txt');
  const calDates = readCsv(zip, 'calendar_dates.txt');

  // لتوفير الذاكرة: نحتفظ فقط بالرحلات العاملة خلال الأيام السبعة القادمة
  calendar = cal; calendarDates = calDates; activeCache.clear();
  const keepServices = new Set();
  const nowMs = Date.now();
  for (let off = -1; off <= 7; off++) {
    const pp = parisYMD(nowMs + off * 86400000);
    for (const sv of activeServices(pp.y, pp.m, pp.d)) keepServices.add(sv);
  }
  let activeTrips = new Map();
  for (const [id, t] of tr) if (keepServices.has(t.service_id)) activeTrips.set(id, t);
  if (activeTrips.size === 0) activeTrips = tr; // احتياط إن لم نجد تقويماً صالحاً
  const keepShapes = new Set();
  for (const t of activeTrips.values()) if (t.shape_id) keepShapes.add(t.shape_id);

  const times = await readStopTimes(zip, activeTrips);
  const shp = await readShapes(zip, keepShapes);

  stations = merged; alias = al; routes = rt; trips = activeTrips; calendar = cal; calendarDates = calDates;
  stopTimes = times.byStop; lastStop = times.last; stopTimesCount = times.count;
  tripStops = times.tStops;
  stopNames = new Map(stops.map((x) => [x.stop_id, x.stop_name]));
  shapes = shp;
  stopCoords = new Map(
    stops
      .filter((x) => !isNaN(parseFloat(x.stop_lat)) && !isNaN(parseFloat(x.stop_lon)))
      .map((x) => [x.stop_id, [parseFloat(x.stop_lat), parseFloat(x.stop_lon)]])
  );
  // الخطوط التي تمر بكل توقف
  const sl = new Map();
  for (const [stopId, rows] of times.byStop) {
    const m = new Map();
    for (const [tripId] of rows) {
      const t2 = tr.get(tripId);
      if (!t2) continue;
      let set = m.get(t2.route_id);
      if (!set) { set = new Set(); m.set(t2.route_id, set); }
      set.add(t2.service_id);
    }
    sl.set(stopId, m);
  }
  stopLines = sl;
  const ss = new Map();
  for (const stn of merged.values()) for (const sid of stn.stopIds) ss.set(sid, stn.id);
  stopStation = ss;
  activeCache.clear();
  rawStations = st;
  for (const x of stations.values()) x.lines = linesOf(x.stopIds);
  loadedAt = new Date();
  console.log(`جاهز: ${merged.size} محطة، ${rt.size} خط، ${activeTrips.size} رحلة، ${times.count} توقف مجدول`);
  console.log(`الذاكرة: ${Math.round(process.memoryUsage().rss / 1048576)} MB`);
}

// ───────── الوقت الحقيقي ─────────
let cache = { at: 0, feed: null };
async function getFeed() {
  if (cache.feed && Date.now() - cache.at < 10000) return cache.feed;
  const res = await fetch(TRIP_UPDATES_URL);
  if (!res.ok) throw new Error('trip-updates HTTP ' + res.status);
  const feed = GtfsRT.transit_realtime.FeedMessage.decode(new Uint8Array(await res.arrayBuffer()));
  cache = { at: Date.now(), feed };
  return feed;
}

// الرحلات المجدولة عند محطة (من الجدول الثابت)
function serviceDays(now) {
  const days = [];
  const seen = new Set();
  for (const off of [-1, 0, 1]) {
    const p = parisYMD(now + off * 86400000);
    const key = `${p.y}-${p.m}-${p.d}`;
    if (seen.has(key)) continue;
    seen.add(key);
    days.push({ midnight: parisMidnight(p.y, p.m, p.d), active: activeServices(p.y, p.m, p.d) });
  }
  return days;
}

function scheduledAt(st, now) {
  const days = serviceDays(now);
  const out = [];
  for (const stopId of st.stopIds) {
    for (const [tripId, secs] of stopTimes.get(stopId) || []) {
      const trip = trips.get(tripId);
      if (!trip) continue;
      const li = lastStop.get(tripId);
      if (li && li.stop === stopId) continue; // لا نعرض وصولاً إلى المحطة الأخيرة
      for (const day of days) {
        if (!day.active.has(trip.service_id)) continue;
        const ms = day.midnight + secs * 1000;
        if (ms < now - 30000 - 3600000 || ms > now + FAR_MS + 3600000) continue;
        out.push({ tripId, trip, ms });
      }
    }
  }
  return out;
}

async function arrivalsFor(stationId) {
  const st = stations.get(stationId) || stations.get(alias.get(stationId));
  if (!st) return null;
  const mine = new Set(st.stopIds);
  const feed = await getFeed();
  const now = Date.now();

  const live = [];
  const rtKeys = new Set();     // رحلات لها بيانات حية عند هذه المحطة
  const skipKeys = new Set();   // رحلات ملغاة أو متخطاة
  const canceled = new Set();
  const delays = new Map();     // رحلات فيها تأخير فقط بلا وقت مطلق
  const unknown = [];            // رحلات حية غير موجودة في الجدول الثابت

  for (const e of feed.entity) {
    const tu = e.tripUpdate;
    if (!tu || !tu.trip) continue;
    const tripId = tu.trip.tripId;
    if (tu.trip.scheduleRelationship === 3) { canceled.add(tripId); continue; }
    const info = trips.get(tripId) || {};
    const route = routes.get(tu.trip.routeId || info.route_id) || {};
    for (const u of tu.stopTimeUpdate || []) {
      if (!mine.has(u.stopId)) continue;
      const key = tripId + '|' + st.id;
      const li = lastStop.get(tripId);
      if (u.scheduleRelationship === 1 || u.scheduleRelationship === 2 || (li && li.stop === u.stopId)) {
        skipKeys.add(key);
        continue;
      }
      const ev = u.arrival && (num(u.arrival.time) || num(u.arrival.delay) != null) ? u.arrival : u.departure;
      const t = ev ? num(ev.time) : null;
      if (!t) {
        const dl = ev ? num(ev.delay) : null;
        if (dl != null) delays.set(key, dl);
        continue;
      }
      const known = !!(route.short || info.route_id || tu.trip.routeId);
      const ms = t * 1000;
      if (!known) {
        unknown.push({ tripId, ms, stopIds: (tu.stopTimeUpdate || []).map((x) => x.stopId) });
        continue;
      }
      rtKeys.add(key);
      if (ms < now - 30000 || ms > now + FAR_MS) continue;
      const type = route.type === '0' ? 'tram' : 'bus';
      const line = route.short || tu.trip.routeId || '?';
      live.push({
        id: key, tripId, rtId: tripId, type, line, name: (type === 'tram' ? 'Tram ' : 'Bus ') + line,
        dest: info.headsign || route.long || '', arrivesAt: ms, color: route.color || null, live: true,
      });
    }
  }

  const schedRaw = scheduledAt(st, now);

  // رحلات حية لا يوجد رقمها في الجدول الثابت: نبحث عن الرحلة المجدولة التي
  // تمر بالمحطات نفسها وبوقت قريب، فنأخذ منها الخط والوجهة
  const stopSetCache = new Map();
  const usedSched = new Set();
  for (const u of unknown) {
    let best = null;
    for (const c of schedRaw) {
      const diff = Math.abs(c.ms - u.ms);
      if (diff > 15 * 60000 || usedSched.has(c.tripId + '|' + c.ms)) continue;
      let set = stopSetCache.get(c.tripId);
      if (!set) {
        set = new Set((tripStops.get(c.tripId) || []).map((x) => x[1]));
        stopSetCache.set(c.tripId, set);
      }
      let hit = 0;
      for (const sid of u.stopIds) if (set.has(sid)) hit++;
      const frac = u.stopIds.length ? hit / u.stopIds.length : 0;
      if (frac < 0.8) continue;
      const score = frac * 1000 - diff / 60000;
      if (!best || score > best.score) best = { c, score };
    }
    if (!best) continue; // لا نعرض رحلة لا نعرف خطها
    const c = best.c;
    usedSched.add(c.tripId + '|' + c.ms);
    const key = c.tripId + '|' + st.id;
    rtKeys.add(key);
    if (u.ms < now - 30000 || u.ms > now + FAR_MS) continue;
    const route = routes.get(c.trip.route_id) || {};
    const type = route.type === '0' ? 'tram' : 'bus';
    const line = route.short || c.trip.route_id || '?';
    live.push({
      id: key, tripId: c.tripId, rtId: u.tripId, type, line,
      name: (type === 'tram' ? 'Tram ' : 'Bus ') + line,
      dest: c.trip.headsign || route.long || '', arrivesAt: u.ms, color: route.color || null, live: true,
    });
  }

  // الجدول النظري كاحتياط للرحلات التي ليس لها وقت حقيقي
  const sched = [];
  for (const s of schedRaw) {
    const key = s.tripId + '|' + st.id;
    if (canceled.has(s.tripId) || skipKeys.has(key) || rtKeys.has(key)) continue;
    const dl = delays.get(key);
    const ms = s.ms + (dl ? dl * 1000 : 0);
    if (ms < now - 30000 || ms > now + FAR_MS) continue;
    const route = routes.get(s.trip.route_id) || {};
    const type = route.type === '0' ? 'tram' : 'bus';
    const line = route.short || s.trip.route_id || '?';
    const dest = s.trip.headsign || route.long || '';
    // إن وُجدت رحلة حية لنفس الخط والوجهة خلال 3 دقائق نعتبرها نفسها
    if (live.some((r) => r.line === line && r.dest === dest && Math.abs(r.arrivesAt - ms) <= 3 * 60000)) continue;
    sched.push({
      id: key, tripId: s.tripId, type, line, name: (type === 'tram' ? 'Tram ' : 'Bus ') + line,
      dest, arrivesAt: ms, color: route.color || null, live: dl != null,
    });
  }

  // نأخذ الأقرب أولاً، وبحد أقصى PER_LINE لكل (خط + وجهة) حتى لا يختفي أي خط
  const all = [...live, ...sched].sort((a, b) => a.arrivesAt - b.arrivesAt);
  const count = new Map();
  const picked = [];
  for (const it of all) {
    const k = it.line + '|' + it.dest;
    const n = count.get(k) || 0;
    if (n === 0 && it.arrivesAt > now + WINDOW_MS) continue; // أول رحلة يجب أن تكون خلال ساعتين
    if (n >= PER_LINE) continue;
    count.set(k, n + 1);
    picked.push(it);
  }
  return { station: { id: st.id, name: st.name }, arrivals: picked.slice(0, 200) };
}

// ───────── رحلات مباشرة بين محطتين ─────────
function pairTrips(aRows, bRows) {
  const out = [];
  for (const [tripId, aList] of aRows) {
    const bList = bRows.get(tripId);
    if (!bList) continue;
    for (const sA of aList) {
      let best = null;
      for (const sB of bList) if (sB > sA && (best === null || sB < best)) best = sB;
      if (best !== null) out.push({ tripId, sA, sB: best });
    }
  }
  return out;
}

async function routeFor(fromId, toId) {
  const A = stations.get(fromId) || stations.get(alias.get(fromId));
  const B = stations.get(toId) || stations.get(alias.get(toId));
  if (!A || !B) return null;
  const now = Date.now();
  const result = { from: { id: A.id, name: A.name }, to: { id: B.id, name: B.name }, trips: [] };
  if (A.id === B.id) return result;

  const collect = (st) => {
    const m = new Map();
    for (const sid of st.stopIds) {
      for (const [tripId, secs] of stopTimes.get(sid) || []) {
        const l = m.get(tripId);
        if (l) l.push(secs); else m.set(tripId, [secs]);
      }
    }
    return m;
  };
  const pairs = pairTrips(collect(A), collect(B));
  if (!pairs.length) return result;

  // الوقت الحقيقي إن توفر
  const aStops = new Set(A.stopIds), bStops = new Set(B.stopIds);
  const rt = new Map();
  const canceled = new Set();
  try {
    const feed = await getFeed();
    const ev = (u, preferDep) => {
      const first = preferDep ? u.departure : u.arrival;
      const second = preferDep ? u.arrival : u.departure;
      const ok = (x) => x && (num(x.time) || num(x.delay) != null);
      const x = ok(first) ? first : ok(second) ? second : null;
      if (!x) return null;
      const tm = num(x.time);
      return { t: tm ? tm * 1000 : null, d: num(x.delay) };
    };
    for (const e of feed.entity) {
      const tu = e.tripUpdate;
      if (!tu || !tu.trip) continue;
      const tripId = tu.trip.tripId;
      if (tu.trip.scheduleRelationship === 3) { canceled.add(tripId); continue; }
      for (const u of tu.stopTimeUpdate || []) {
        const isA = aStops.has(u.stopId), isB = bStops.has(u.stopId);
        if (!isA && !isB) continue;
        const rec = rt.get(tripId) || {};
        if (isA) rec.a = ev(u, true);
        if (isB) rec.b = ev(u, false);
        rt.set(tripId, rec);
      }
    }
  } catch (e) { /* نكمل بالجدول فقط */ }

  const days = serviceDays(now);
  const seen = new Set();
  for (const p of pairs) {
    const trip = trips.get(p.tripId);
    if (!trip || canceled.has(p.tripId)) continue;
    const route = routes.get(trip.route_id) || {};
    const r = rt.get(p.tripId) || {};
    for (const day of days) {
      if (!day.active.has(trip.service_id)) continue;
      let dep = day.midnight + p.sA * 1000;
      let arr = day.midnight + p.sB * 1000;
      if (dep < now - 3 * 3600000 || dep > now + WINDOW_MS + 3 * 3600000) continue;
      let live = false;
      if (Math.abs(dep - now) < 3 * 3600000) {
        if (r.a && r.a.t) { arr += r.a.t - dep; dep = r.a.t; live = true; }
        else if (r.a && r.a.d != null) { dep += r.a.d * 1000; arr += r.a.d * 1000; live = true; }
        if (r.b && r.b.t) { arr = r.b.t; live = true; }
      }
      if (dep < now - 30000 || dep > now + WINDOW_MS || arr <= dep) continue;
      const key = p.tripId + '|' + dep;
      if (seen.has(key)) continue;
      seen.add(key);
      const type = route.type === '0' ? 'tram' : 'bus';
      const line = route.short || trip.route_id || '?';
      result.trips.push({
        id: key, tripId: p.tripId, type, line, name: (type === 'tram' ? 'Tram ' : 'Bus ') + line,
        dest: trip.headsign || route.long || '', depMs: dep, arrMs: arr, live,
      });
    }
  }
  result.trips.sort((x, y) => x.depMs - y.depMs);
  result.trips = result.trips.slice(0, 25);
  return result;
}

// أقرب نقطة في المسار إلى إحداثية معينة (بدءاً من فهرس معيّن)
function nearestIdx(pts, lat, lon, start) {
  const k = Math.cos((lat * Math.PI) / 180);
  let best = start, bd = Infinity;
  for (let i = start; i < pts.length; i++) {
    const dLat = pts[i][0] - lat, dLon = (pts[i][1] - lon) * k;
    const d = dLat * dLat + dLon * dLon;
    if (d < bd) { bd = d; best = i; }
  }
  return best;
}

// مسار الرحلة على الخريطة (بين محطتين، أو من محطتك حتى نهاية الخط)
function tripShape(tripId, fromId, toId) {
  const trip = trips.get(tripId);
  const list = tripStops.get(tripId);
  if (!trip || !list) return null;
  const pick = (id) => (id ? stations.get(id) || stations.get(alias.get(id)) : null);
  const A = pick(fromId), B = pick(toId);
  const aSet = new Set(A ? A.stopIds : []), bSet = new Set(B ? B.stopIds : []);
  let ia = A ? list.findIndex((x) => aSet.has(x[1])) : 0;
  if (ia < 0) ia = 0;
  let ib = list.length - 1;
  if (B) {
    for (let k = ia + 1; k < list.length; k++) {
      if (bSet.has(list[k][1])) { ib = k; break; }
    }
  }
  const stops = list
    .slice(ia, ib + 1)
    .map((x) => {
      const c = stopCoords.get(x[1]);
      return c ? { name: stopNames.get(x[1]) || x[1], latitude: c[0], longitude: c[1] } : null;
    })
    .filter(Boolean);

  let coords = null;
  const pts = trip.shape_id ? shapes.get(trip.shape_id) : null;
  if (pts && pts.length > 1 && stops.length >= 2) {
    const first = stops[0], last = stops[stops.length - 1];
    const i = nearestIdx(pts, first.latitude, first.longitude, 0);
    const j = nearestIdx(pts, last.latitude, last.longitude, i);
    coords = pts.slice(i, j + 1).map((p) => ({ latitude: p[0], longitude: p[1] }));
  }
  if (!coords || coords.length < 2) {
    coords = stops.map((x) => ({ latitude: x.latitude, longitude: x.longitude }));
  }
  if (coords.length > 600) {
    const step = Math.ceil(coords.length / 600);
    coords = coords.filter((_, k) => k % step === 0 || k === coords.length - 1);
  }
  const route = routes.get(trip.route_id) || {};
  return {
    trip: { id: tripId, type: route.type === '0' ? 'tram' : 'bus', line: route.short || trip.route_id || '?' },
    coords, stops, fromShape: !!(pts && pts.length > 1),
  };
}

// الخطوط العاملة اليوم عند محطة (بعد الدمج)
function linesAtStation(st, days) {
  const out = new Map();
  for (const sid of st.stopIds) {
    const m = stopLines.get(sid);
    if (!m) continue;
    for (const [routeId, services] of m) {
      let ok = false;
      for (const d of days) {
        for (const sv of services) if (d.active.has(sv)) { ok = true; break; }
        if (ok) break;
      }
      if (!ok) continue;
      const r = routes.get(routeId);
      if (!r) continue;
      out.set(r.short || routeId, r.type === '0' ? 'tram' : 'bus');
    }
  }
  return [...out]
    .map(([line, type]) => ({ line, type }))
    .sort((a, b) =>
      (a.type === 'tram' ? 0 : 1) - (b.type === 'tram' ? 0 : 1) ||
      String(a.line).localeCompare(String(b.line), undefined, { numeric: true })
    );
}

// ───────── كل محطات رحلة معينة ─────────
async function tripDetail(tripId, stationId, ref, rtId, toId) {
  const trip = trips.get(tripId);
  const list = tripStops.get(tripId);
  if (!trip || !list) return null;
  const st = stationId ? stations.get(stationId) || stations.get(alias.get(stationId)) : null;
  const mine = new Set(st ? st.stopIds : []);
  const toSt = toId ? stations.get(toId) || stations.get(alias.get(toId)) : null;
  const toSet = new Set(toSt ? toSt.stopIds : []);
  const now = Date.now();
  const days = serviceDays(now);

  // نحدد يوم الخدمة الصحيح: الأقرب لوقت الوصول المعروض
  const anchor = list.find((x) => mine.has(x[1])) || list[0];
  const refMs = ref && !isNaN(ref) ? ref : now;
  let best = days[0], bestD = Infinity;
  for (const d of days) {
    const diff = Math.abs(d.midnight + anchor[2] * 1000 - refMs);
    if (diff < bestD) { bestD = diff; best = d; }
  }

  // الوقت الحقيقي لهذه الرحلة
  const rt = new Map();
  try {
    const feed = await getFeed();
    for (const e of feed.entity) {
      const tu = e.tripUpdate;
      if (!tu || !tu.trip || tu.trip.tripId !== (rtId || tripId)) continue;
      for (const u of tu.stopTimeUpdate || []) {
        const x = u.arrival && (num(u.arrival.time) || num(u.arrival.delay) != null) ? u.arrival : u.departure;
        if (!x) continue;
        const tm = num(x.time);
        rt.set(u.stopId, { t: tm ? tm * 1000 : null, d: num(x.delay) });
      }
      break;
    }
  } catch (e) { /* نكمل بالجدول فقط */ }

  const route0 = routes.get(trip.route_id) || {};
  const own = route0.short || trip.route_id;
  const lineCache = new Map();
  let curDelay = null;
  const stops = list.map(([seq, stopId, secs]) => {
    const sched = best.midnight + secs * 1000;
    let ms = sched, live = false;
    const r = rt.get(stopId);
    if (r && r.t) { ms = r.t; curDelay = r.t - sched; live = true; }
    else if (r && r.d != null) { curDelay = r.d * 1000; ms = sched + curDelay; live = true; }
    else if (curDelay != null) { ms = sched + curDelay; live = true; }
    const sid = stopStation.get(stopId);
    const stn = sid ? stations.get(sid) : null;
    let others = [];
    if (stn) {
      if (!lineCache.has(stn.id)) {
        lineCache.set(stn.id, linesAtStation(stn, days).filter((x) => x.line !== own));
      }
      others = lineCache.get(stn.id);
    }
    return {
      stopId, stationId: stn ? stn.id : null, name: stopNames.get(stopId) || stopId, ms, live,
      isHere: mine.has(stopId), isDest: toSet.has(stopId), passed: ms < now - 30000, others,
    };
  });
  const route = routes.get(trip.route_id) || {};
  const type = route.type === '0' ? 'tram' : 'bus';
  const line = route.short || trip.route_id || '?';
  return { trip: { id: tripId, type, line, dest: trip.headsign || route.long || '' }, stops };
}

// ───────── تنبيهات الشبكة ─────────
let alertsCache = { at: 0, data: [] };
const pickText = (ts) => {
  const tr = ts && ts.translation;
  if (!tr || !tr.length) return '';
  const fr = tr.find((x) => x.language === 'fr') || tr[0];
  return fr.text || '';
};
async function getAlerts() {
  if (Date.now() - alertsCache.at < 60000) return alertsCache.data;
  const res = await fetch(ALERTS_URL);
  if (!res.ok) throw new Error('alerts HTTP ' + res.status);
  const feed = GtfsRT.transit_realtime.FeedMessage.decode(new Uint8Array(await res.arrayBuffer()));
  const nowS = Date.now() / 1000;
  const out = [];
  for (const e of feed.entity) {
    const a = e.alert;
    if (!a) continue;
    const periods = a.activePeriod || [];
    const active = !periods.length || periods.some((p) => {
      const st = num(p.start), en = num(p.end);
      return (!st || st <= nowS) && (!en || en >= nowS);
    });
    if (!active) continue;
    const lines = new Set();
    for (const i of a.informedEntity || []) {
      const r = routes.get(i.routeId);
      if (r && r.short) lines.add(r.short);
    }
    out.push({ id: e.id, title: pickText(a.headerText), text: pickText(a.descriptionText), lines: [...lines] });
  }
  alertsCache = { at: Date.now(), data: out };
  return out;
}

function distKm(lat1, lon1, lat2, lon2) {
  const R = 6371, rad = Math.PI / 180;
  const dLat = (lat2 - lat1) * rad, dLon = (lon2 - lon1) * rad;
  const a = Math.sin(dLat / 2) ** 2 +
    Math.cos(lat1 * rad) * Math.cos(lat2 * rad) * Math.sin(dLon / 2) ** 2;
  return 2 * R * Math.asin(Math.sqrt(a));
}

const pub = (s) => ({ id: s.id, name: s.name, lat: s.lat, lon: s.lon, lines: s.lines || [] });

const server = http.createServer(async (req, res) => {
  const url = new URL(req.url, 'http://localhost');
  const send = (code, obj) => {
    res.writeHead(code, {
      'Content-Type': 'application/json; charset=utf-8',
      'Access-Control-Allow-Origin': '*',
    });
    res.end(JSON.stringify(obj));
  };
  try {
    if (url.pathname === '/') return send(200, { ok: true, ready: !!loadedAt });
    if (!loadedAt) return send(503, { error: 'loading' });

    if (url.pathname === '/stations') {
      const q = norm(url.searchParams.get('q'));
      if (!q) return send(200, []);
      const list = [...stations.values()]
        .filter((s) => norm(s.name).includes(q))
        .sort((a, b) => {
          const sa = norm(a.name).startsWith(q) ? 0 : 1;
          const sb = norm(b.name).startsWith(q) ? 0 : 1;
          return sa - sb || a.name.localeCompare(b.name);
        })
        .slice(0, 20)
        .map(pub);
      return send(200, list);
    }

    if (url.pathname === '/stations/bbox') {
      const g = (k) => parseFloat(url.searchParams.get(k));
      const minLat = g('minLat'), maxLat = g('maxLat'), minLon = g('minLon'), maxLon = g('maxLon');
      if ([minLat, maxLat, minLon, maxLon].some(isNaN)) return send(400, { error: 'bbox' });
      const cLat = (minLat + maxLat) / 2, cLon = (minLon + maxLon) / 2;
      const list = [...stations.values()]
        .filter((s) => !isNaN(s.lat) && s.lat >= minLat && s.lat <= maxLat && s.lon >= minLon && s.lon <= maxLon)
        .map((s) => ({ ...pub(s), km: distKm(cLat, cLon, s.lat, s.lon) }))
        .sort((a, b) => a.km - b.km)
        .slice(0, 100)
        .map(({ km, ...rest }) => rest);
      return send(200, list);
    }

    if (url.pathname === '/stations/nearby') {
      const lat = parseFloat(url.searchParams.get('lat'));
      const lon = parseFloat(url.searchParams.get('lon'));
      if (isNaN(lat) || isNaN(lon)) return send(400, { error: 'lat/lon' });
      const list = [...stations.values()]
        .filter((s) => !isNaN(s.lat))
        .map((s) => ({ ...pub(s), km: distKm(lat, lon, s.lat, s.lon) }))
        .sort((a, b) => a.km - b.km)
        .slice(0, 8);
      return send(200, list);
    }

    if (url.pathname === '/arrivals') {
      const r = await arrivalsFor(url.searchParams.get('station'));
      return r ? send(200, r) : send(404, { error: 'station' });
    }

    if (url.pathname === '/inspect') {
      const q = norm(url.searchParams.get('q'));
      const list = [...rawStations.values()]
        .filter((x) => norm(x.name).includes(q))
        .slice(0, 30)
        .map((x) => ({
          name: x.name, lat: x.lat, lon: x.lon, stops: x.stopIds,
          mergedInto: alias.get(x.id) || x.id, lines: linesOf(x.stopIds),
        }));
      return send(200, list);
    }

    if (url.pathname === '/trip/shape') {
      const r = tripShape(url.searchParams.get('trip'), url.searchParams.get('from'), url.searchParams.get('to'));
      return r ? send(200, r) : send(404, { error: 'trip' });
    }

    if (url.pathname === '/trip') {
      const r = await tripDetail(
        url.searchParams.get('trip'), url.searchParams.get('station'), parseFloat(url.searchParams.get('ref')),
        url.searchParams.get('rt') || null, url.searchParams.get('to') || null
      );
      return r ? send(200, r) : send(404, { error: 'trip' });
    }

    if (url.pathname === '/route') {
      const r = await routeFor(url.searchParams.get('from'), url.searchParams.get('to'));
      return r ? send(200, r) : send(404, { error: 'station' });
    }

    if (url.pathname === '/alerts') return send(200, await getAlerts());

    if (url.pathname === '/debug') {
      const feed = await getFeed();
      let withTime = 0, withoutTime = 0, total = 0;
      for (const e of feed.entity) {
        for (const u of (e.tripUpdate && e.tripUpdate.stopTimeUpdate) || []) {
          total++;
          const ev = (u.arrival && num(u.arrival.time) ? u.arrival : u.departure);
          if (ev && num(ev.time)) withTime++; else withoutTime++;
        }
      }
      return send(200, {
        rssMB: Math.round(process.memoryUsage().rss / 1048576),
        loadedAt, stations: stations.size, routes: routes.size, trips: trips.size,
        scheduledStops: stopTimesCount, feedEntities: feed.entity.length,
        stopTimeUpdates: total, withTime, withoutTime,
      });
    }

    send(404, { error: 'not found' });
  } catch (e) {
    console.error(e);
    send(500, { error: String(e.message || e) });
  }
});

async function loadWithRetry(tries) {
  for (let i = 0; i < tries; i++) {
    try { await loadStatic(); return; }
    catch (e) {
      console.error('فشل تحميل GTFS:', e.message);
      await new Promise((ok) => setTimeout(ok, 60000));
    }
  }
}

// نفرّغ البيانات القديمة قبل التحميل الجديد حتى لا تتضاعف الذاكرة (مهم في الاستضافة المجانية 512MB)
function clearData() {
  loadedAt = null;
  stations = new Map(); alias = new Map(); routes = new Map(); trips = new Map();
  stopTimes = new Map(); lastStop = new Map(); tripStops = new Map(); stopNames = new Map();
  stopLines = new Map(); stopStation = new Map(); stopCoords = new Map(); shapes = new Map();
  calendar = []; calendarDates = []; activeCache.clear();
  cache = { at: 0, feed: null };
}

// إعادة تحميل الجدول مرة كل يوم الساعة 04:00 بتوقيت باريس
function msUntilNextReload() {
  const now = Date.now();
  const p = parisYMD(now);
  let t = parisMidnight(p.y, p.m, p.d) + 4 * 3600000;
  if (t <= now + 60000) {
    const q = parisYMD(now + 86400000);
    t = parisMidnight(q.y, q.m, q.d) + 4 * 3600000;
  }
  return t - now;
}
function scheduleReload() {
  setTimeout(async () => {
    clearData();
    await loadWithRetry(10);
    scheduleReload();
  }, msUntilNextReload());
}

loadWithRetry(10);
scheduleReload();

server.listen(PORT, '0.0.0.0', () => {
  console.log(`\nالخادم يعمل على المنفذ ${PORT}. عناوين حاسوبك على الشبكة:`);
  for (const list of Object.values(os.networkInterfaces())) {
    for (const i of list || []) if (i.family === 'IPv4' && !i.internal) console.log(`  http://${i.address}:${PORT}`);
  }
});

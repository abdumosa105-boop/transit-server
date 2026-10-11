// خادم Fil Bleu (Tours): يقرأ GTFS + GTFS-RT ويعطي التطبيق JSON بسيطاً
// يحتاج Node.js 18 أو أحدث
const http = require('http');
const os = require('os');
const AdmZip = require('adm-zip');
const { parse } = require('csv-parse/sync');
const GtfsRT = require('gtfs-realtime-bindings');

const PORT = process.env.PORT || 3000;
const GTFS_URL =
  'https://data.tours-metropole.fr/api/v2/catalog/datasets/horaires-temps-reel-gtfsrt-reseau-filbleu-tmvl/alternative_exports/filbleu_gtfszip';
const TRIP_UPDATES_URL = 'https://data.filbleu.fr/ws-tr/gtfs-rt/opendata/trip-updates';

let stations = new Map(); // stationId -> { id, name, lat, lon, stopIds[] }
let routes = new Map();   // routeId -> { short, long, type, color }
let trips = new Map();    // tripId -> { route_id, headsign }
let loadedAt = null;

const norm = (s) =>
  (s || '').normalize('NFD').replace(/[\u0300-\u036f]/g, '').toLowerCase().trim();
const num = (v) =>
  v == null ? null : typeof v === 'number' ? v : v.toNumber ? v.toNumber() : Number(v);

function readCsv(zip, name) {
  const entry = zip.getEntry(name);
  if (!entry) return [];
  return parse(entry.getData(), {
    columns: true, skip_empty_lines: true, bom: true, relax_column_count: true, trim: true,
  });
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
    if (s.location_type && s.location_type !== '0') continue; // تخطَّ المحطات الأم والمداخل
    const sid = s.parent_station && byId.has(s.parent_station) ? s.parent_station : s.stop_id;
    const base = byId.get(sid) || s;
    if (!st.has(sid)) {
      let lat = parseFloat(base.stop_lat), lon = parseFloat(base.stop_lon);
      if (isNaN(lat) || isNaN(lon)) { lat = parseFloat(s.stop_lat); lon = parseFloat(s.stop_lon); }
      st.set(sid, { id: sid, name: base.stop_name, lat, lon, stopIds: [] });
    }
    st.get(sid).stopIds.push(s.stop_id);
  }

  const rt = new Map();
  for (const r of readCsv(zip, 'routes.txt')) {
    rt.set(r.route_id, {
      short: r.route_short_name, long: r.route_long_name, type: r.route_type, color: r.route_color,
    });
  }
  const tr = new Map();
  for (const t of readCsv(zip, 'trips.txt')) {
    tr.set(t.trip_id, { route_id: t.route_id, headsign: t.trip_headsign });
  }

  stations = st; routes = rt; trips = tr; loadedAt = new Date();
  console.log(`جاهز: ${st.size} محطة، ${rt.size} خط، ${tr.size} رحلة`);
}

let cache = { at: 0, feed: null };
async function getFeed() {
  if (cache.feed && Date.now() - cache.at < 10000) return cache.feed;
  const res = await fetch(TRIP_UPDATES_URL);
  if (!res.ok) throw new Error('trip-updates HTTP ' + res.status);
  const feed = GtfsRT.transit_realtime.FeedMessage.decode(new Uint8Array(await res.arrayBuffer()));
  cache = { at: Date.now(), feed };
  return feed;
}

async function arrivalsFor(stationId) {
  const st = stations.get(stationId);
  if (!st) return null;
  const mine = new Set(st.stopIds);
  const feed = await getFeed();
  const now = Date.now();
  const out = [];
  const seen = new Set();
  for (const e of feed.entity) {
    const tu = e.tripUpdate;
    if (!tu || !tu.trip) continue;
    const tripId = tu.trip.tripId;
    const info = trips.get(tripId) || {};
    const route = routes.get(tu.trip.routeId || info.route_id) || {};
    for (const u of tu.stopTimeUpdate || []) {
      if (!mine.has(u.stopId)) continue;
      if (u.scheduleRelationship === 1 || u.scheduleRelationship === 2) continue; // ملغاة
      const ev = u.arrival && num(u.arrival.time) ? u.arrival : u.departure;
      const t = ev ? num(ev.time) : null;
      if (!t) continue;
      const ms = t * 1000;
      if (ms < now - 30000 || ms > now + 90 * 60000) continue;
      const key = tripId + '|' + st.id;
      if (seen.has(key)) continue;
      seen.add(key);
      const type = route.type === '0' ? 'tram' : 'bus';
      const line = route.short || tu.trip.routeId || '?';
      out.push({
        id: key, type, line,
        name: (type === 'tram' ? 'Tram ' : 'Bus ') + line,
        dest: info.headsign || route.long || '',
        arrivesAt: ms, color: route.color || null,
      });
    }
  }
  out.sort((a, b) => a.arrivesAt - b.arrivesAt);
  return { station: { id: st.id, name: st.name }, arrivals: out.slice(0, 15) };
}

function distKm(lat1, lon1, lat2, lon2) {
  const R = 6371, rad = Math.PI / 180;
  const dLat = (lat2 - lat1) * rad, dLon = (lon2 - lon1) * rad;
  const a = Math.sin(dLat / 2) ** 2 +
    Math.cos(lat1 * rad) * Math.cos(lat2 * rad) * Math.sin(dLon / 2) ** 2;
  return 2 * R * Math.asin(Math.sqrt(a));
}

const pub = (s) => ({ id: s.id, name: s.name, lat: s.lat, lon: s.lon });

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
        loadedAt, stations: stations.size, routes: routes.size, trips: trips.size,
        feedEntities: feed.entity.length, stopTimeUpdates: total, withTime, withoutTime,
      });
    }

    send(404, { error: 'not found' });
  } catch (e) {
    console.error(e);
    send(500, { error: String(e.message || e) });
  }
});

loadStatic().catch((e) => console.error('فشل تحميل GTFS:', e.message));
setInterval(() => loadStatic().catch((e) => console.error('فشل التحديث:', e.message)), 6 * 3600 * 1000);

server.listen(PORT, '0.0.0.0', () => {
  console.log(`\nالخادم يعمل على المنفذ ${PORT}. عناوين حاسوبك على الشبكة:`);
  for (const list of Object.values(os.networkInterfaces())) {
    for (const i of list || []) if (i.family === 'IPv4' && !i.internal) console.log(`  http://${i.address}:${PORT}`);
  }
});

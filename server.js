const express = require('express');
const http = require('http');
const { Server } = require('socket.io');
const path = require('path');
const fs = require('fs');

const app = express();
const server = http.createServer(app);
const io = new Server(server);
app.use(express.static(path.join(__dirname, 'public')));

// ---- CONSTANTS ----
const ARENA_W = 3200, ARENA_H = 3200;
const CELL    = 50;               // slightly bigger than player diameter
const GRID_W  = ARENA_W / CELL;  // 64
const GRID_H  = ARENA_H / CELL;  // 64

const PLAYER_RADIUS  = 20;
const PLAYER_SPEED   = 230;
const BULLET_SPEED   = 520;
const BULLET_RADIUS  = 5;
const BULLET_DAMAGE  = 300;
const MAX_HEALTH     = 5000;
const RESPAWN_DELAY  = 2500;
const FIRE_RATE      = 280;
const BULLET_MAX_RANGE = 450;
const MUZZLE_OFFSET  = 42;
const MAGS_MAX       = 3;
const BULLETS_PER_MAG = 10;
const MAG_REGEN_TIME = 2500;
const REGEN_DELAY    = 2000;
const REGEN_RATE     = 300;

const GRENADE_SPEED            = 380;
const GRENADE_LIFETIME         = 1800;
const GRENADE_RADIUS           = 10;
const GRENADE_EXPLOSION_RADIUS = 160;
const GRENADE_DAMAGE           = 80;
const GRENADE_MAX_BOUNCES      = 3;
const SUPER_CHARGE_PER_DAMAGE  = 0.2;
const SUPER_CHARGE_PER_KILL    = 10;

const COIN_PICKUP_RADIUS = 28;
const COIN_LIFETIME      = 25000;
const GRASS_REGEN_TIME   = 22000;

const CHEST_HEALTH            = 3500;
const CHEST_RADIUS            = 22;
const MONEY_BAG_PICKUP_RADIUS = 34;
const MONEY_BAG_LIFETIME      = 45000;
const COIN_FILE = path.join(__dirname, 'coins.json');
let coinData = {};
try { coinData = JSON.parse(fs.readFileSync(COIN_FILE, 'utf8')); } catch (_) {}
function saveCoinData() { fs.writeFileSync(COIN_FILE, JSON.stringify(coinData)); }

// ---- MAP ----
// GRID: flat Uint8Array, 0=empty  1=wall  2=grass
function createMap() {
  const grid = new Uint8Array(GRID_W * GRID_H);

  function set(gx, gy, type) {
    if (gx >= 1 && gx < GRID_W - 1 && gy >= 1 && gy < GRID_H - 1)
      grid[gy * GRID_W + gx] = type;
  }
  function get(gx, gy) {
    if (gx < 0 || gx >= GRID_W || gy < 0 || gy >= GRID_H) return 0;
    return grid[gy * GRID_W + gx];
  }

  // Wall shapes — small cover structures that feel intentional
  const wallShapes = [
    [[0,0],[1,0]],                           // 2-wide bar
    [[0,0],[0,1]],                           // 2-tall bar
    [[0,0],[1,0],[2,0]],                     // 3-wide bar
    [[0,0],[0,1],[0,2]],                     // 3-tall bar
    [[0,0],[1,0],[0,1]],                     // L corner
    [[0,0],[1,0],[1,1]],                     // L corner flipped
    [[0,1],[1,0],[1,1]],                     // L corner other
    [[0,0],[0,1],[1,1]],                     // L corner last
    [[0,0],[1,0],[2,0],[1,1]],               // T shape
    [[0,0],[1,0],[2,0],[0,1],[2,1]],         // U shape (open top cover)
    [[0,0],[2,0],[0,1],[1,1],[2,1]],         // U facing up
    [[0,0],[1,0],[2,0],[2,1],[2,2]],         // long L
    [[0,0],[0,1],[1,1],[0,2]],               // zigzag
  ];

  const wallSeeds = [];
  function wallTooClose(gx, gy) {
    return wallSeeds.some(([sx, sy]) => Math.abs(sx - gx) < 4 && Math.abs(sy - gy) < 4);
  }

  // Place ~30 wall structures spread across the map
  let placed = 0, tries = 0;
  while (placed < 30 && tries++ < 600) {
    const gx = 2 + Math.floor(Math.random() * (GRID_W - 5));
    const gy = 2 + Math.floor(Math.random() * (GRID_H - 5));
    if (wallTooClose(gx, gy)) continue;
    const shape = wallShapes[Math.floor(Math.random() * wallShapes.length)];
    shape.forEach(([dx, dy]) => set(gx + dx, gy + dy, 1));
    wallSeeds.push([gx, gy]);
    placed++;
  }

  // Place ~18 grass patches — rectangular, spread out, never on top of walls
  const grassSeeds = [];
  function grassTooClose(gx, gy) {
    return grassSeeds.some(([sx, sy]) => Math.abs(sx - gx) < 5 && Math.abs(sy - gy) < 5);
  }

  placed = 0; tries = 0;
  while (placed < 18 && tries++ < 600) {
    const pw = 2 + Math.floor(Math.random() * 3); // 2–4 wide
    const ph = 2 + Math.floor(Math.random() * 3); // 2–4 tall
    const gx = 2 + Math.floor(Math.random() * (GRID_W - pw - 2));
    const gy = 2 + Math.floor(Math.random() * (GRID_H - ph - 2));
    if (grassTooClose(gx, gy)) continue;
    // Skip if any cell in the patch is already a wall
    let blocked = false;
    for (let dy = 0; dy < ph && !blocked; dy++)
      for (let dx = 0; dx < pw && !blocked; dx++)
        if (get(gx + dx, gy + dy) === 1) blocked = true;
    if (blocked) continue;
    for (let dy = 0; dy < ph; dy++)
      for (let dx = 0; dx < pw; dx++)
        set(gx + dx, gy + dy, 2);
    grassSeeds.push([gx, gy]);
    placed++;
  }

  return grid;
}

const GRID = createMap();

// ---- HELPERS ----
function circleRect(cx, cy, cr, rx, ry, rw, rh) {
  const nx = Math.max(rx, Math.min(cx, rx + rw));
  const ny = Math.max(ry, Math.min(cy, ry + rh));
  return (cx - nx) ** 2 + (cy - ny) ** 2 < cr * cr;
}

// Fast grid-based collision — only checks cells the circle overlaps
function hitsWall(cx, cy, cr) {
  const minGX = Math.max(0, Math.floor((cx - cr) / CELL));
  const maxGX = Math.min(GRID_W - 1, Math.floor((cx + cr) / CELL));
  const minGY = Math.max(0, Math.floor((cy - cr) / CELL));
  const maxGY = Math.min(GRID_H - 1, Math.floor((cy + cr) / CELL));
  for (let gy = minGY; gy <= maxGY; gy++) {
    for (let gx = minGX; gx <= maxGX; gx++) {
      if (GRID[gy * GRID_W + gx] === 1 &&
          circleRect(cx, cy, cr, gx * CELL, gy * CELL, CELL, CELL)) return true;
    }
  }
  return false;
}

function dist2(ax, ay, bx, by) { return (ax - bx) ** 2 + (ay - by) ** 2; }

// Returns the separation vector needed to push a circle out of any overlapping wall corners.
// Used to smoothly slide around corners instead of getting stuck.
function wallCornerPush(cx, cy, cr) {
  const minGX = Math.max(0, Math.floor((cx - cr) / CELL));
  const maxGX = Math.min(GRID_W - 1, Math.floor((cx + cr) / CELL));
  const minGY = Math.max(0, Math.floor((cy - cr) / CELL));
  const maxGY = Math.min(GRID_H - 1, Math.floor((cy + cr) / CELL));
  let px = 0, py = 0;
  for (let gy = minGY; gy <= maxGY; gy++) {
    for (let gx = minGX; gx <= maxGX; gx++) {
      if (GRID[gy * GRID_W + gx] !== 1) continue;
      const rx = gx * CELL, ry = gy * CELL;
      const npx = Math.max(rx, Math.min(cx, rx + CELL));
      const npy = Math.max(ry, Math.min(cy, ry + CELL));
      const dx = cx - npx, dy = cy - npy;
      const d = Math.hypot(dx, dy);
      if (d < 0.001 || d >= cr) continue;
      const f = (cr - d) / d;
      px += dx * f; py += dy * f;
    }
  }
  return [px, py];
}

function safeSpawn() {
  for (let i = 0; i < 100; i++) {
    const x = CELL * 2 + Math.random() * (ARENA_W - CELL * 4);
    const y = CELL * 2 + Math.random() * (ARENA_H - CELL * 4);
    if (hitsWall(x, y, PLAYER_RADIUS + 4)) continue;
    if (Object.values(players).some(p => p.alive && dist2(x, y, p.x, p.y) < 200 ** 2)) continue;
    return { x, y };
  }
  return { x: ARENA_W / 2, y: ARENA_H / 2 };
}

function dropCoins(p, now) {
  const count = 3 + Math.floor(Math.random() * 5);
  for (let i = 0; i < count; i++) {
    const a = Math.random() * Math.PI * 2;
    const d = 15 + Math.random() * 55;
    const v = 1 + Math.floor(Math.random() * 4);
    const id = coinId++;
    worldCoins[id] = { id, x: p.x + Math.cos(a) * d, y: p.y + Math.sin(a) * d, value: v, born: now };
  }
  const bonus = Math.min(50, Math.floor((coinData[p.userId] || 0) * 0.08));
  if (bonus > 0) {
    const id = coinId++;
    worldCoins[id] = { id, x: p.x, y: p.y, value: bonus, born: now };
  }
}

const COLORS = ['#ff4757','#ffa502','#2ed573','#1e90ff','#eccc68','#ff6b81',
                '#7bed9f','#70a1ff','#ff6348','#5352ed','#ff4d4d','#00d2d3',
                '#ff9f43','#48dbfb','#ff6b6b','#a29bfe'];
let colorIdx = 0;
function nextColor() { return COLORS[colorIdx++ % COLORS.length]; }

// ---- STATE ----
const players = {};
const bullets = {};
let bulletId = 0;
const worldCoins = {};
let coinId = 0;
const destroyedGrass = {};
const grenades = {};
let grenadeId = 0;
const killFeed = [];

const chests = {};
const moneyBags = {};
let chestId = 0;
let moneyBagId = 0;

function spawnChest() {
  let tries = 0;
  while (tries++ < 600) {
    const x = CELL * 4 + Math.random() * (ARENA_W - CELL * 8);
    const y = CELL * 4 + Math.random() * (ARENA_H - CELL * 8);
    if (hitsWall(x, y, CHEST_RADIUS + 10)) continue;
    const cgx = Math.floor(x / CELL), cgy = Math.floor(y / CELL);
    if (GRID[cgy * GRID_W + cgx] === 2) continue;
    if (Object.values(chests).some(c => dist2(x, y, c.x, c.y) < 280 ** 2)) continue;
    const id = chestId++;
    chests[id] = { id, x, y, health: CHEST_HEALTH };
    return true;
  }
  return false;
}

// Generate 10 chests at startup
(function() { for (let i = 0; i < 10; i++) spawnChest(); })();

// ---- GAME LOOP ----
let lastTick = Date.now();
setInterval(() => {
  const now = Date.now();
  const dt  = Math.min((now - lastTick) / 1000, 0.05);
  lastTick  = now;

  for (const id in players) {
    const p = players[id];
    if (!p.alive) {
      if (now >= p.respawnAt) {
        const pos = safeSpawn();
        p.x = pos.x; p.y = pos.y;
        p.health = MAX_HEALTH; p.alive = true;
      }
      continue;
    }

    const inp = p.input;
    let dx = 0, dy = 0;
    if (inp.up)    dy -= 1;
    if (inp.down)  dy += 1;
    if (inp.left)  dx -= 1;
    if (inp.right) dx += 1;
    if (dx && dy) { dx *= 0.707; dy *= 0.707; }

    const nx = Math.max(PLAYER_RADIUS, Math.min(ARENA_W - PLAYER_RADIUS, p.x + dx * PLAYER_SPEED * dt));
    const ny = Math.max(PLAYER_RADIUS, Math.min(ARENA_H - PLAYER_RADIUS, p.y + dy * PLAYER_SPEED * dt));

    if (!hitsWall(nx, ny, PLAYER_RADIUS)) { p.x = nx; p.y = ny; }
    else {
      if (!hitsWall(nx, p.y, PLAYER_RADIUS)) {
        p.x = nx;
      } else if (nx !== p.x) {
        const [, pushY] = wallCornerPush(nx, p.y, PLAYER_RADIUS);
        const cy2 = Math.max(PLAYER_RADIUS, Math.min(ARENA_H - PLAYER_RADIUS, p.y + pushY));
        if (Math.abs(pushY) > 0.1 && !hitsWall(nx, cy2, PLAYER_RADIUS)) { p.x = nx; p.y = cy2; }
      }
      if (!hitsWall(p.x, ny, PLAYER_RADIUS)) {
        p.y = ny;
      } else if (ny !== p.y) {
        const [pushX] = wallCornerPush(p.x, ny, PLAYER_RADIUS);
        const cx2 = Math.max(PLAYER_RADIUS, Math.min(ARENA_W - PLAYER_RADIUS, p.x + pushX));
        if (Math.abs(pushX) > 0.1 && !hitsWall(cx2, ny, PLAYER_RADIUS)) { p.y = ny; p.x = cx2; }
      }
    }
    p.angle = inp.angle;

    if (p.mags < MAGS_MAX && now - p.lastMagAt >= MAG_REGEN_TIME) {
      p.mags++;
      p.lastMagAt = now;
    }

    if (now - p.lastHit > REGEN_DELAY && p.health < MAX_HEALTH)
      p.health = Math.min(MAX_HEALTH, p.health + REGEN_RATE * dt);
  }

  for (const bid in bullets) {
    const b = bullets[bid];
    b.x += b.vx * dt; b.y += b.vy * dt;

    if (dist2(b.x, b.y, b.sx, b.sy) > BULLET_MAX_RANGE ** 2 ||
        b.x < 0 || b.x > ARENA_W || b.y < 0 || b.y > ARENA_H ||
        hitsWall(b.x, b.y, BULLET_RADIUS)) { delete bullets[bid]; continue; }

    let hit = false;
    for (const pid in players) {
      if (pid === b.ownerId) continue;
      const p = players[pid];
      if (!p.alive) continue;
      if (dist2(b.x, b.y, p.x, p.y) < (PLAYER_RADIUS + BULLET_RADIUS) ** 2) {
        p.health -= BULLET_DAMAGE; p.lastHit = now; hit = true;
        const shooter = players[b.ownerId];
        if (shooter) shooter.superCharge = Math.min(100, shooter.superCharge + BULLET_DAMAGE * SUPER_CHARGE_PER_DAMAGE);
        if (p.health <= 0) {
          p.health = 0; p.alive = false; p.respawnAt = now + RESPAWN_DELAY; p.deaths++;
          dropCoins(p, now);
          if (shooter) {
            shooter.kills++;
            shooter.superCharge = Math.min(100, shooter.superCharge + SUPER_CHARGE_PER_KILL);
          }
          const entry = { killer: shooter ? shooter.name : '?', victim: p.name };
          killFeed.unshift(entry);
          if (killFeed.length > 6) killFeed.pop();
          io.emit('killed', { killer: entry.killer, victim: entry.victim, victimId: pid });
        }
        break;
      }
    }
    // Check chest hits
    if (!hit) {
      for (const cid in chests) {
        const c = chests[cid];
        if (dist2(b.x, b.y, c.x, c.y) < (CHEST_RADIUS + BULLET_RADIUS) ** 2) {
          c.health -= BULLET_DAMAGE;
          hit = true;
          if (c.health <= 0) {
            const bid2 = moneyBagId++;
            const value = 1 + Math.floor(Math.random() * 30);
            moneyBags[bid2] = { id: bid2, x: c.x, y: c.y, value, born: now };
            io.emit('chestDestroyed', { x: Math.round(c.x), y: Math.round(c.y) });
            delete chests[cid];
          }
          break;
        }
      }
    }
    if (hit) delete bullets[bid];
  }
  // Money bag pickup + expiry
  for (const bid in moneyBags) {
    const bag = moneyBags[bid];
    if (now - bag.born > MONEY_BAG_LIFETIME) { delete moneyBags[bid]; continue; }
    for (const pid in players) {
      const p = players[pid];
      if (!p.alive) continue;
      if (dist2(bag.x, bag.y, p.x, p.y) < MONEY_BAG_PICKUP_RADIUS ** 2) {
        p.coins = (p.coins || 0) + bag.value;
        coinData[p.userId] = p.coins;
        saveCoinData();
        io.emit('coinPickup', { pickerId: pid, value: bag.value, x: Math.round(bag.x), y: Math.round(bag.y) });
        delete moneyBags[bid];
        break;
      }
    }
  }
  // Coin pickup + expiry
  for (const cid in worldCoins) {
    const c = worldCoins[cid];
    if (now - c.born > COIN_LIFETIME) { delete worldCoins[cid]; continue; }
    for (const pid in players) {
      const p = players[pid];
      if (!p.alive) continue;
      if (dist2(c.x, c.y, p.x, p.y) < COIN_PICKUP_RADIUS ** 2) {
        p.coins = (p.coins || 0) + c.value;
        coinData[p.userId] = p.coins;
        saveCoinData();
        io.emit('coinPickup', { pickerId: pid, value: c.value, x: Math.round(c.x), y: Math.round(c.y) });
        delete worldCoins[cid];
        break;
      }
    }
  }

  // Grenade physics
  for (const gid in grenades) {
    const g = grenades[gid];
    const nx = g.x + g.vx * dt;
    const ny = g.y + g.vy * dt;

    let hitWall = false;
    if (nx < GRENADE_RADIUS || nx > ARENA_W - GRENADE_RADIUS || hitsWall(nx, g.y, GRENADE_RADIUS)) {
      hitWall = true;
    } else g.x = nx;
    if (ny < GRENADE_RADIUS || ny > ARENA_H - GRENADE_RADIUS || hitsWall(g.x, ny, GRENADE_RADIUS)) {
      hitWall = true;
    } else g.y = ny;

    // Check if grenade hit any enemy directly
    let hitEnemy = false;
    for (const pid in players) {
      if (pid === g.ownerId) continue;
      const p = players[pid];
      if (!p.alive) continue;
      if (dist2(g.x, g.y, p.x, p.y) < (PLAYER_RADIUS + GRENADE_RADIUS) ** 2) {
        hitEnemy = true; break;
      }
    }

    if (hitEnemy || hitWall || now - g.born >= GRENADE_LIFETIME) {
      const thrower = players[g.ownerId];
      for (const pid in players) {
        if (pid === g.ownerId) continue;
        const p = players[pid];
        if (!p.alive) continue;
        const d2 = dist2(g.x, g.y, p.x, p.y);
        if (d2 < GRENADE_EXPLOSION_RADIUS ** 2) {
          const falloff = 1 - Math.sqrt(d2) / GRENADE_EXPLOSION_RADIUS;
          p.health -= Math.round(GRENADE_DAMAGE * falloff);
          p.lastHit = now;
          if (p.health <= 0 && p.alive) {
            p.health = 0; p.alive = false; p.respawnAt = now + RESPAWN_DELAY; p.deaths++;
            dropCoins(p, now);
            if (thrower) {
              thrower.kills++;
              thrower.superCharge = Math.min(100, thrower.superCharge + SUPER_CHARGE_PER_KILL);
            }
            const entry = { killer: thrower ? thrower.name : '?', victim: p.name };
            killFeed.unshift(entry);
            if (killFeed.length > 6) killFeed.pop();
            io.emit('killed', { killer: entry.killer, victim: entry.victim, victimId: pid });
          }
        }
      }
      // Damage chests in blast radius
      for (const cid in chests) {
        const c = chests[cid];
        if (dist2(g.x, g.y, c.x, c.y) < GRENADE_EXPLOSION_RADIUS ** 2) {
          c.health -= GRENADE_DAMAGE;
          if (c.health <= 0) {
            const bid2 = moneyBagId++;
            const value = 1 + Math.floor(Math.random() * 30);
            moneyBags[bid2] = { id: bid2, x: c.x, y: c.y, value, born: now };
            io.emit('chestDestroyed', { x: Math.round(c.x), y: Math.round(c.y) });
            delete chests[cid];
          }
        }
      }
      // Destroy nearby walls and grass cells
      const changedCells = [];
      const minGX = Math.max(0, Math.floor((g.x - GRENADE_EXPLOSION_RADIUS) / CELL));
      const maxGX = Math.min(GRID_W - 1, Math.floor((g.x + GRENADE_EXPLOSION_RADIUS) / CELL));
      const minGY = Math.max(0, Math.floor((g.y - GRENADE_EXPLOSION_RADIUS) / CELL));
      const maxGY = Math.min(GRID_H - 1, Math.floor((g.y + GRENADE_EXPLOSION_RADIUS) / CELL));
      for (let gy = minGY; gy <= maxGY; gy++) {
        for (let gx = minGX; gx <= maxGX; gx++) {
          const idx = gy * GRID_W + gx;
          if (GRID[idx] === 1 || GRID[idx] === 2) {
            const cx = gx * CELL + CELL / 2, cy = gy * CELL + CELL / 2;
            if (dist2(g.x, g.y, cx, cy) < GRENADE_EXPLOSION_RADIUS ** 2) {
              const newType = GRID[idx] === 2 ? 4 : 3;
              if (GRID[idx] === 2) destroyedGrass[idx] = now;
              GRID[idx] = newType;
              changedCells.push({ gx, gy, t: newType });
            }
          }
        }
      }
      if (changedCells.length > 0) io.emit('cellsCleared', changedCells);
      io.emit('explosion', { x: Math.round(g.x), y: Math.round(g.y) });
      delete grenades[gid];
    }
  }
}, 1000 / 60);

// Broadcast at 20fps
setInterval(() => {
  const now = Date.now();
  io.emit('state', {
    t: now,
    players: Object.values(players).map(p => ({
      id: p.id, n: p.name, c: p.color,
      x: Math.round(p.x), y: Math.round(p.y),
      a: Math.round(p.angle * 1000) / 1000,
      hp: Math.round(p.health), alive: p.alive,
      k: p.kills, d: p.deaths,
      ri: p.alive ? 0 : Math.max(0, p.respawnAt - now),
      sc: Math.round(p.superCharge),
      uid: p.userId,
      co: p.coins || 0,
      mg: p.mags,
      mgP: p.mags < MAGS_MAX ? Math.min(1, (now - p.lastMagAt) / MAG_REGEN_TIME) : 0,
    })),
    bullets: Object.values(bullets).map(b => ({
      id: b.id, x: Math.round(b.x), y: Math.round(b.y),
      vx: Math.round(b.vx), vy: Math.round(b.vy), c: b.ownerColor,
    })),
    worldCoins: Object.values(worldCoins).map(c => ({ id: c.id, x: Math.round(c.x), y: Math.round(c.y), v: c.value })),
    chests: Object.values(chests).map(c => ({ id: c.id, x: Math.round(c.x), y: Math.round(c.y), hp: Math.round(c.health) })),
    moneyBags: Object.values(moneyBags).map(b => ({ id: b.id, x: Math.round(b.x), y: Math.round(b.y), v: b.value })),
    grenades: Object.values(grenades).map(g => ({
      id: g.id, x: Math.round(g.x), y: Math.round(g.y),
      vx: Math.round(g.vx), vy: Math.round(g.vy),
      born: g.born, lifetime: GRENADE_LIFETIME,
    })),
  });
}, 1000 / 20);

// Grass regeneration
setInterval(() => {
  const now = Date.now();
  const restored = [];
  for (const idxStr in destroyedGrass) {
    if (now - destroyedGrass[idxStr] >= GRASS_REGEN_TIME) {
      const idx = Number(idxStr);
      GRID[idx] = 2;
      restored.push({ gx: idx % GRID_W, gy: Math.floor(idx / GRID_W) });
      delete destroyedGrass[idxStr];
    }
  }
  if (restored.length > 0) io.emit('cellsRestored', restored);
}, 1000);

// ---- SOCKETS ----
io.on('connection', (socket) => {
  socket.on('join', ({ name, userId }) => {
    const pos = safeSpawn();
    players[socket.id] = {
      id: socket.id, name: (name || 'Player').substring(0, 16), color: nextColor(),
      userId: (userId || '').replace(/[^A-Z0-9]/g, '').substring(0, 8),
      coins: coinData[(userId || '').replace(/[^A-Z0-9]/g, '').substring(0, 8)] || 0,
      x: pos.x, y: pos.y, angle: 0, health: MAX_HEALTH, alive: true,
      kills: 0, deaths: 0, lastShot: 0, lastHit: 0, respawnAt: 0,
      superCharge: 0, mags: MAGS_MAX, lastMagAt: 0,
      input: { up: false, down: false, left: false, right: false, angle: 0 },
    };
    socket.emit('init', {
      id: socket.id, color: players[socket.id].color,
      grid: Array.from(GRID),
      gridW: GRID_W, gridH: GRID_H, cell: CELL,
      arenaW: ARENA_W, arenaH: ARENA_H,
      coins: players[socket.id].coins,
      killFeed,
    });
    console.log(`${players[socket.id].name} joined (${Object.keys(players).length} players)`);
  });

  socket.on('input', (inp) => { const p = players[socket.id]; if (p) p.input = inp; });

  socket.on('fireMag', (data) => {
    const p = players[socket.id];
    if (!p || !p.alive || p.mags <= 0) return;
    const fireAngle = (data && typeof data.angle === 'number') ? data.angle : p.angle;
    p.mags--;
    p.lastMagAt = Date.now();
    for (let i = 0; i < BULLETS_PER_MAG; i++) {
      setTimeout(() => {
        if (!p.alive) return;
        const spread = (Math.random() - 0.5) * 0.1;
        const a = fireAngle + spread;
        const bsx = p.x + Math.cos(a) * MUZZLE_OFFSET;
        const bsy = p.y + Math.sin(a) * MUZZLE_OFFSET;
        bullets[bulletId++] = {
          id: bulletId, ownerId: socket.id, ownerColor: p.color,
          x: bsx, y: bsy, sx: bsx, sy: bsy,
          vx: Math.cos(a) * BULLET_SPEED,
          vy: Math.sin(a) * BULLET_SPEED,
        };
      }, i * 75);
    }
  });

  socket.on('super', () => {
    const p = players[socket.id];
    if (!p || !p.alive || p.superCharge < 100) return;
    p.superCharge = 0;
    const a = p.angle;
    const gid = grenadeId++;
    grenades[gid] = {
      id: gid, ownerId: socket.id,
      x: p.x + Math.cos(a) * (PLAYER_RADIUS + GRENADE_RADIUS + 2),
      y: p.y + Math.sin(a) * (PLAYER_RADIUS + GRENADE_RADIUS + 2),
      vx: Math.cos(a) * GRENADE_SPEED,
      vy: Math.sin(a) * GRENADE_SPEED,
      bounces: 0, born: Date.now(),
    };
  });

  socket.on('disconnect', () => {
    const p = players[socket.id];
    if (p) console.log(`${p.name} left`);
    delete players[socket.id];
  });
});

const PORT = process.env.PORT || 3000;
server.listen(PORT, '0.0.0.0', () => console.log(`Battle Royale on http://0.0.0.0:${PORT}`));

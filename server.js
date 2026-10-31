var __defProp = Object.defineProperty;
var __export = (target, all) => {
  for (var name in all)
    __defProp(target, name, { get: all[name], enumerable: true });
};

// server/index.js
import http from "node:http";
import { randomInt as randomInt2, randomUUID, createHash as createHash2 } from "node:crypto";
import { readFile, stat } from "node:fs/promises";
import { extname, join, normalize, dirname, sep } from "node:path";
import { fileURLToPath } from "node:url";
import { WebSocketServer } from "ws";

// server/games.js
import { randomInt } from "node:crypto";

// src/rules/engine.js
var BAR = "bar";
var OFF = "off";
var CHECKERS = 15;
var DEFAULT_MATCH_TARGET = 5;
var other = (p) => 1 - p;
var dirOf = (p) => p === 0 ? -1 : 1;
function createInitialPosition() {
  const points2 = new Array(24).fill(0);
  points2[23] = 2;
  points2[12] = 5;
  points2[7] = 3;
  points2[5] = 5;
  points2[0] = -2;
  points2[11] = -5;
  points2[16] = -3;
  points2[18] = -5;
  return { points: points2, bar: [0, 0], off: [0, 0] };
}
function clonePosition(pos) {
  return { points: pos.points.slice(), bar: pos.bar.slice(), off: pos.off.slice() };
}
function positionKey(pos) {
  return pos.points.join(",") + "|" + pos.bar.join(",") + "|" + pos.off.join(",");
}
function countAt(pos, player, idx) {
  const v = pos.points[idx];
  return player === 0 ? v > 0 ? v : 0 : v < 0 ? -v : 0;
}
function addAt(pos, player, idx, n) {
  pos.points[idx] += player === 0 ? n : -n;
}
function entryPoint(player, die) {
  return player === 0 ? 24 - die : die - 1;
}
function distanceHome(player, idx) {
  return player === 0 ? idx + 1 : 24 - idx;
}
function allHome(pos, player) {
  if (pos.bar[player] > 0) return false;
  for (let i = 0; i < 24; i++) {
    if (countAt(pos, player, i) === 0) continue;
    if (player === 0 ? i > 5 : i < 18) return false;
  }
  return true;
}
function isOpenFor(pos, player, idx) {
  return countAt(pos, other(player), idx) <= 1;
}
function singleMoves(pos, player, die) {
  const moves = [];
  if (pos.bar[player] > 0) {
    const to = entryPoint(player, die);
    if (isOpenFor(pos, player, to)) moves.push({ from: BAR, to, die });
    return moves;
  }
  const home = allHome(pos, player);
  const dir = dirOf(player);
  for (let from = 0; from < 24; from++) {
    if (countAt(pos, player, from) === 0) continue;
    const to = from + dir * die;
    if (to >= 0 && to <= 23) {
      if (isOpenFor(pos, player, to)) moves.push({ from, to, die });
      continue;
    }
    if (!home) continue;
    const dist = distanceHome(player, from);
    if (die === dist) {
      moves.push({ from, to: OFF, die });
    } else if (die > dist) {
      let farther = false;
      if (player === 0) {
        for (let i = from + 1; i <= 5; i++) if (countAt(pos, 0, i)) {
          farther = true;
          break;
        }
      } else {
        for (let i = from - 1; i >= 18; i--) if (countAt(pos, 1, i)) {
          farther = true;
          break;
        }
      }
      if (!farther) moves.push({ from, to: OFF, die });
    }
  }
  return moves;
}
function applyMove(pos, player, move4) {
  const next2 = clonePosition(pos);
  if (move4.from === BAR) next2.bar[player] -= 1;
  else addAt(next2, player, move4.from, -1);
  if (move4.to === OFF) {
    next2.off[player] += 1;
  } else {
    const opp = other(player);
    if (countAt(next2, opp, move4.to) === 1) {
      addAt(next2, opp, move4.to, -1);
      next2.bar[opp] += 1;
    }
    addAt(next2, player, move4.to, 1);
  }
  return next2;
}
function isHit(pos, player, move4) {
  return move4.to !== OFF && countAt(pos, other(player), move4.to) === 1;
}
function diceForRoll(a, b) {
  return a === b ? [a, a, a, a] : [a, b];
}
function removeOneDie(dice, die) {
  const i = dice.indexOf(die);
  const out = dice.slice();
  out.splice(i, 1);
  return out;
}
function uniqueDice(dice) {
  return [...new Set(dice)];
}
function maxPlayable(pos, player, dice, memo = /* @__PURE__ */ new Map()) {
  if (!dice.length) return 0;
  const key = positionKey(pos) + "#" + dice.slice().sort().join("");
  const cached = memo.get(key);
  if (cached !== void 0) return cached;
  let best = 0;
  for (const die of uniqueDice(dice)) {
    const rest = removeOneDie(dice, die);
    for (const m of singleMoves(pos, player, die)) {
      const n = 1 + maxPlayable(applyMove(pos, player, m), player, rest, memo);
      if (n > best) best = n;
      if (best === dice.length) break;
    }
    if (best === dice.length) break;
  }
  memo.set(key, best);
  return best;
}
function legalMoves(pos, player, dice) {
  if (!dice.length) return [];
  const memo = /* @__PURE__ */ new Map();
  const target = maxPlayable(pos, player, dice, memo);
  if (target === 0) return [];
  let result = [];
  for (const die of uniqueDice(dice)) {
    const rest = removeOneDie(dice, die);
    for (const m of singleMoves(pos, player, die)) {
      if (1 + maxPlayable(applyMove(pos, player, m), player, rest, memo) === target) result.push(m);
    }
  }
  const distinct = uniqueDice(dice);
  if (target === 1 && distinct.length === 2) {
    const high = Math.max(...distinct);
    const withHigh = result.filter((m) => m.die === high);
    if (withHigh.length) result = withHigh;
  }
  return result;
}
function sameMove(a, b) {
  return a.from === b.from && a.to === b.to && a.die === b.die;
}
function winnerOf(pos) {
  if (pos.off[0] === CHECKERS) return 0;
  if (pos.off[1] === CHECKERS) return 1;
  return null;
}
function gameResult(pos) {
  const winner = winnerOf(pos);
  if (winner === null) return null;
  const loser = other(winner);
  const mars = pos.off[loser] === 0;
  return { winner, points: mars ? 2 : 1, mars };
}
var randomDie = () => Math.floor(Math.random() * 6) + 1;
function createMatch({ target = DEFAULT_MATCH_TARGET } = {}) {
  const m = {
    target,
    score: [0, 0],
    gameNo: 0,
    matchWinner: null,
    history: []
  };
  startGame(m);
  return m;
}
function startGame(m) {
  m.gameNo += 1;
  m.pos = createInitialPosition();
  m.phase = "opening";
  m.turn = null;
  m.openingDice = [null, null];
  m.rolled = [];
  m.dice = [];
  m.turnMoves = [];
  m.turnStart = null;
  m.lastTurn = null;
  m.gameResult = null;
}
function nextGame(m) {
  if (m.phase !== "gameover" || m.matchWinner !== null) return fail("\u0644\u0627 \u064A\u0645\u0643\u0646 \u0628\u062F\u0621 \u062C\u0648\u0644\u0629 \u062C\u062F\u064A\u062F\u0629 \u0627\u0644\u0622\u0646");
  startGame(m);
  return ok();
}
var ok = (extra = {}) => ({ ok: true, ...extra });
var fail = (error) => ({ ok: false, error });
function rollOpening(m, player, rng = randomDie) {
  if (m.phase !== "opening") return fail("\u0644\u064A\u0633\u062A \u0645\u0631\u062D\u0644\u0629 \u0631\u0645\u064A\u0629 \u0627\u0644\u0628\u062F\u0627\u064A\u0629");
  if (m.openingDice[player] !== null) return fail("\u0631\u0645\u064A\u062A \u0632\u0627\u0631\u0643 \u0628\u0627\u0644\u0641\u0639\u0644");
  m.openingDice[player] = rng();
  const [a, b] = m.openingDice;
  if (a === null || b === null) return ok({ waiting: true });
  if (a === b) {
    m.lastOpening = { dice: [a, b], tie: true };
    m.openingDice = [null, null];
    return ok({ tie: true, dice: [a, b] });
  }
  const starter = a > b ? 0 : 1;
  m.lastOpening = { dice: [a, b], tie: false, starter };
  m.turn = starter;
  beginMovePhase(m, [a, b]);
  return ok({ starter, dice: [a, b] });
}
function beginMovePhase(m, rolled) {
  m.rolled = rolled.slice();
  m.dice = diceForRoll(rolled[0], rolled[1]);
  m.turnMoves = [];
  m.turnStart = { pos: clonePosition(m.pos), dice: m.dice.slice() };
  m.phase = "move";
  if (!legalMoves(m.pos, m.turn, m.dice).length) finishTurn(m, true);
}
function roll(m, player, rng = randomDie) {
  if (m.phase !== "roll") return fail("\u0644\u064A\u0633 \u0648\u0642\u062A \u0631\u0645\u064A \u0627\u0644\u0646\u0631\u062F");
  if (m.turn !== player) return fail("\u0644\u064A\u0633 \u062F\u0648\u0631\u0643");
  const a = rng();
  const b = rng();
  beginMovePhase(m, [a, b]);
  return ok({ dice: [a, b] });
}
function move(m, player, mv) {
  if (m.phase !== "move") return fail("\u0644\u064A\u0633 \u0648\u0642\u062A \u0627\u0644\u062A\u062D\u0631\u064A\u0643");
  if (m.turn !== player) return fail("\u0644\u064A\u0633 \u062F\u0648\u0631\u0643");
  if (!mv || typeof mv !== "object") return fail("\u062D\u0631\u0643\u0629 \u063A\u064A\u0631 \u0635\u0627\u0644\u062D\u0629");
  const legal = legalMoves(m.pos, player, m.dice);
  const chosen = legal.find((l) => sameMove(l, mv));
  if (!chosen) return fail("\u062D\u0631\u0643\u0629 \u063A\u064A\u0631 \u0642\u0627\u0646\u0648\u0646\u064A\u0629");
  const hit = isHit(m.pos, player, chosen);
  m.pos = applyMove(m.pos, player, chosen);
  m.dice = removeOneDie(m.dice, chosen.die);
  m.turnMoves.push({ ...chosen, hit });
  const res = gameResult(m.pos);
  if (res) {
    finishTurn(m, false);
    endGame(m, res);
    return ok({ hit, gameOver: true });
  }
  if (!legalMoves(m.pos, player, m.dice).length) finishTurn(m, false);
  return ok({ hit, turnEnded: m.turn !== player });
}
function undo(m, player) {
  if (m.phase !== "move" || m.turn !== player) return fail("\u0644\u0627 \u064A\u0645\u0643\u0646 \u0627\u0644\u062A\u0631\u0627\u062C\u0639 \u0627\u0644\u0622\u0646");
  if (!m.turnMoves.length) return fail("\u0644\u0627 \u062A\u0648\u062C\u062F \u062D\u0631\u0643\u0629 \u0644\u0644\u062A\u0631\u0627\u062C\u0639");
  const replay = m.turnMoves.slice(0, -1);
  m.pos = clonePosition(m.turnStart.pos);
  m.dice = m.turnStart.dice.slice();
  m.turnMoves = [];
  for (const mv of replay) {
    m.pos = applyMove(m.pos, player, mv);
    m.dice = removeOneDie(m.dice, mv.die);
    m.turnMoves.push(mv);
  }
  return ok();
}
function finishTurn(m, blocked) {
  m.lastTurn = { player: m.turn, rolled: m.rolled.slice(), moves: m.turnMoves.slice(), blocked };
  m.dice = [];
  m.turnStart = null;
  if (!gameResult(m.pos)) {
    m.turn = other(m.turn);
    m.phase = "roll";
  }
}
function endGame(m, res) {
  m.phase = "gameover";
  m.gameResult = res;
  m.score[res.winner] += res.points;
  m.history.push({ game: m.gameNo, ...res });
  if (m.score[res.winner] >= m.target) m.matchWinner = res.winner;
}
function forfeit(m, loser) {
  if (m.matchWinner !== null) return fail("\u0627\u0644\u0645\u0628\u0627\u0631\u0627\u0629 \u0645\u0646\u062A\u0647\u064A\u0629");
  const winner = other(loser);
  m.phase = "gameover";
  m.gameResult = { winner, points: 0, mars: false, forfeit: true };
  m.matchWinner = winner;
  return ok();
}

// src/games/domino/engine.js
var engine_exports = {};
__export(engine_exports, {
  DEFAULT_TARGET: () => DEFAULT_TARGET,
  DOUBLE_SIX: () => DOUBLE_SIX,
  HAND_SIZE: () => HAND_SIZE,
  createMatch: () => createMatch2,
  forfeit: () => forfeit2,
  fullSet: () => fullSet,
  handPips: () => handPips,
  isDouble: () => isDouble,
  legalPlays: () => legalPlays,
  newRound: () => newRound,
  nextRound: () => nextRound,
  nextSeat: () => nextSeat,
  openingLead: () => openingLead,
  partnerOf: () => partnerOf,
  pips: () => pips,
  play: () => play,
  sideOf: () => sideOf,
  tileId: () => tileId,
  tileOf: () => tileOf,
  viewFor: () => viewFor
});
var DEFAULT_TARGET = 101;
var HAND_SIZE = 7;
var DOUBLE_SIX = 6 * 7 + 6;
var tileId = (a, b) => a <= b ? a * 7 + b : b * 7 + a;
var tileOf = (id) => {
  const a = Math.floor(id / 7);
  return [a, id - a * 7];
};
var pips = (id) => {
  const [a, b] = tileOf(id);
  return a + b;
};
var isDouble = (id) => {
  const [a, b] = tileOf(id);
  return a === b;
};
var handPips = (hand) => hand.reduce((s, id) => s + pips(id), 0);
var sideOf = (match, p) => match.players === 4 ? p % 2 : p;
var partnerOf = (match, p) => match.players === 4 ? (p + 2) % 4 : null;
var nextSeat = (match, p) => (p + 1) % match.players;
function fullSet() {
  const ids = [];
  for (let a = 0; a <= 6; a++) for (let b = a; b <= 6; b++) ids.push(tileId(a, b));
  return ids;
}
function shuffle(list, rand2) {
  const a = list.slice();
  for (let i = a.length - 1; i > 0; i--) {
    const j = rand2(i + 1);
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
}
var mathRand = (n) => Math.floor(Math.random() * n);
function openingLead(hands) {
  for (let p = 0; p < hands.length; p++) if (hands[p].includes(DOUBLE_SIX)) return { player: p, tile: DOUBLE_SIX };
  let best = null;
  for (let p = 0; p < hands.length; p++) {
    for (const id of hands[p]) {
      const score = (isDouble(id) ? 100 : 0) + pips(id) * 2 + Math.max(...tileOf(id)) / 10;
      if (!best || score > best.score) best = { player: p, tile: id, score };
    }
  }
  return { player: best.player, tile: best.tile };
}
function newRound(match, rand2 = mathRand) {
  const n = match.players;
  const deck = shuffle(fullSet(), rand2);
  const hands = [];
  for (let p = 0; p < n; p++) hands.push(deck.slice(p * HAND_SIZE, (p + 1) * HAND_SIZE).sort((x, y) => x - y));
  const aside = deck.slice(n * HAND_SIZE);
  let turn, mustLead = null;
  if (match.lastWinner === null || match.lastWinner === void 0) {
    const lead = openingLead(hands);
    turn = lead.player;
    mustLead = lead.tile;
  } else turn = match.lastWinner;
  match.round = {
    hands,
    aside,
    line: [],
    // [{ id, a, b }] left to right; a = left face, b = right face
    ends: null,
    // [left, right]
    turn,
    mustLead,
    passes: 0,
    // knocks in a row (n = blocked)
    missing: hands.map(() => []),
    // numbers each player knocked on (public information)
    log: [],
    // last actions [{ p, kind: 'play'|'pass', id?, side? }]
    result: null
  };
  match.phase = "play";
  return match;
}
function createMatch2({ players: players2 = 2, target = DEFAULT_TARGET, rand: rand2 = mathRand } = {}) {
  if (players2 !== 2 && players2 !== 4) throw new Error("players must be 2 or 4");
  const match = { game: "domino", players: players2, target, scores: [0, 0], roundNo: 1, lastWinner: null, phase: "play", matchWinner: null, round: null };
  return newRound(match, rand2);
}
function fit(ends, id, side) {
  const [x, y] = tileOf(id);
  if (!ends) return { a: x, b: y };
  const end = side === "L" ? ends[0] : ends[1];
  if (side === "L") {
    if (y === end) return { a: x, b: y };
    if (x === end) return { a: y, b: x };
  } else {
    if (x === end) return { a: x, b: y };
    if (y === end) return { a: y, b: x };
  }
  return null;
}
function legalPlays(match, p) {
  const r = match.round;
  if (!r || match.phase !== "play" || r.turn !== p || !r.hands[p]) return [];
  const out = [];
  for (const id of r.hands[p]) {
    if (!r.ends) {
      if (r.mustLead === null || r.mustLead === id) out.push({ id, side: "R" });
      continue;
    }
    if (fit(r.ends, id, "L")) out.push({ id, side: "L" });
    if (fit(r.ends, id, "R")) out.push({ id, side: "R" });
  }
  return out;
}
function pushLog(r, entry) {
  r.log.push(entry);
  if (r.log.length > 8) r.log.shift();
}
function endRound(match, winnerSide, reason, outPlayer = null) {
  const r = match.round;
  const n = match.players;
  const sidePips = [0, 0];
  for (let p = 0; p < n; p++) sidePips[sideOf(match, p)] += handPips(r.hands[p]);
  const points2 = winnerSide === null ? 0 : sidePips[1 - winnerSide];
  if (winnerSide !== null) match.scores[winnerSide] += points2;
  r.result = { winner: winnerSide, reason, points: points2, outPlayer, sidePips, handPips: r.hands.map(handPips), hands: r.hands.map((h) => h.slice()) };
  if (outPlayer !== null) match.lastWinner = outPlayer;
  else if (winnerSide !== null) {
    let best = null;
    for (let p = 0; p < n; p++) if (sideOf(match, p) === winnerSide && (best === null || handPips(r.hands[p]) < handPips(r.hands[best]))) best = p;
    match.lastWinner = best;
  } else match.lastWinner = match.lastWinner ?? r.turn;
  if (winnerSide !== null && match.scores[winnerSide] >= match.target) {
    match.matchWinner = winnerSide;
    match.phase = "matchover";
  } else match.phase = "roundover";
}
function noteMissing(r, p) {
  if (!r.ends) return;
  for (const v of r.ends) if (!r.missing[p].includes(v)) r.missing[p].push(v);
}
function advance(match) {
  const r = match.round;
  const n = match.players;
  for (let guard = 0; guard <= n && match.phase === "play"; guard++) {
    const p = r.turn;
    if (legalPlays(match, p).length) return;
    r.passes += 1;
    noteMissing(r, p);
    pushLog(r, { p, kind: "pass" });
    if (r.passes >= n) {
      const sp = [0, 0];
      for (let q = 0; q < n; q++) sp[sideOf(match, q)] += handPips(r.hands[q]);
      endRound(match, sp[0] === sp[1] ? null : sp[0] < sp[1] ? 0 : 1, "blocked");
      return;
    }
    r.turn = nextSeat(match, p);
  }
}
function play(match, p, { id, side }) {
  const r = match.round;
  if (match.phase !== "play") return { ok: false, error: "not playing" };
  if (r.turn !== p) return { ok: false, error: "not your turn" };
  const options = legalPlays(match, p).filter((x) => x.id === id);
  const chosen = options.find((x) => x.side === side) || (!r.ends || options.length === 1 ? options[0] : null);
  if (!chosen) return { ok: false, error: "illegal tile" };
  const usedSide = chosen.side;
  const o = fit(r.ends, id, usedSide);
  if (!r.ends) {
    r.line.push({ id, a: o.a, b: o.b });
    r.ends = [o.a, o.b];
  } else if (usedSide === "L") {
    r.line.unshift({ id, a: o.a, b: o.b });
    r.ends = [o.a, r.ends[1]];
  } else {
    r.line.push({ id, a: o.a, b: o.b });
    r.ends = [r.ends[0], o.b];
  }
  r.hands[p] = r.hands[p].filter((x) => x !== id);
  r.missing[p] = r.missing[p].filter((v) => v !== o.a && v !== o.b);
  r.mustLead = null;
  r.passes = 0;
  pushLog(r, { p, kind: "play", id, side: usedSide });
  if (r.hands[p].length === 0) {
    endRound(match, sideOf(match, p), "domino", p);
    return { ok: true, side: usedSide, roundOver: true };
  }
  r.turn = nextSeat(match, p);
  advance(match);
  return { ok: true, side: usedSide, roundOver: match.phase !== "play" };
}
function nextRound(match, rand2 = mathRand) {
  if (match.phase !== "roundover") return { ok: false, error: "round not over" };
  match.roundNo += 1;
  newRound(match, rand2);
  return { ok: true };
}
function forfeit2(match, p) {
  if (match.matchWinner !== null) return { ok: false, error: "over" };
  match.matchWinner = 1 - sideOf(match, p);
  match.phase = "matchover";
  match.forfeitedBy = p;
  return { ok: true };
}
function viewFor(match, seat) {
  const r = match.round;
  const showAll = match.phase !== "play";
  return {
    ...match,
    round: r && {
      ...r,
      hands: r.hands.map((h, i) => i === seat || showAll ? h.slice() : null),
      handCounts: r.hands.map((h) => h.length),
      aside: void 0,
      asideCount: r.aside.length
    }
  };
}

// src/games/domino/ai.js
var { legalPlays: legalPlays2, tileOf: tileOf2, pips: pips2, isDouble: isDouble2, nextSeat: nextSeat2, partnerOf: partnerOf2, sideOf: sideOf2 } = engine_exports;
function after(ends, id, side) {
  const [x, y] = tileOf2(id);
  if (!ends) return [x, y];
  if (side === "L") return [ends[0] === y ? x : y, ends[1]];
  return [ends[0], ends[1] === x ? y : x];
}
function heuristic(match, me, options, rand2) {
  const r = match.round;
  const hand = r.hands[me];
  const next2 = nextSeat2(match, me);
  const partner = partnerOf2(match, me);
  const nextMisses = new Set(r.missing[next2] || []);
  const partnerMisses = partner === null ? /* @__PURE__ */ new Set() : new Set(r.missing[partner] || []);
  let best = null;
  for (const o of options) {
    const rest = hand.filter((x) => x !== o.id);
    const ends = after(r.ends, o.id, o.side);
    let score = pips2(o.id) * 2 + (isDouble2(o.id) ? 10 : 0);
    score += rest.filter((t) => {
      const [a, b] = tileOf2(t);
      return a === ends[0] || b === ends[0] || a === ends[1] || b === ends[1];
    }).length * 3;
    score += new Set(rest.flatMap(tileOf2)).size * 1.5;
    for (const e of new Set(ends)) {
      if (nextMisses.has(e)) score += 8;
      if (partnerMisses.has(e)) score -= 5;
      score += rest.filter((t) => tileOf2(t).includes(e)).length * 2;
    }
    score += rand2() * 0.5;
    if (!best || score > best.score) best = { ...o, score };
  }
  return { id: best.id, side: best.side };
}
function sampleDeal(match, me, rand2) {
  const r = match.round;
  const n = match.players;
  const seen = /* @__PURE__ */ new Set([...r.hands[me], ...r.line.map((x) => x.id)]);
  const pool = fullSet().filter((id) => !seen.has(id));
  const counts = r.handCounts || r.hands.map((h) => h.length);
  for (let attempt = 0; attempt < 25; attempt++) {
    for (let i = pool.length - 1; i > 0; i--) {
      const j = Math.floor(rand2() * (i + 1));
      [pool[i], pool[j]] = [pool[j], pool[i]];
    }
    const hands = Array.from({ length: n }, (_, q) => q === me ? r.hands[me].slice() : []);
    const aside = [];
    const strict = attempt < 20;
    for (const id of pool) {
      const [a, b] = tileOf2(id);
      let placed = false;
      for (let k = 1; k < n && !placed; k++) {
        const q = (me + k) % n;
        if (hands[q].length >= counts[q]) continue;
        if (strict && (r.missing[q].includes(a) || r.missing[q].includes(b))) continue;
        hands[q].push(id);
        placed = true;
      }
      if (!placed) aside.push(id);
    }
    if (hands.every((h, q) => h.length === counts[q])) return { hands, aside };
  }
  return null;
}
function simulate(match, me, options, rand2, samples) {
  const mySide = sideOf2(match, me);
  const total = options.map(() => 0);
  for (let k = 0; k < samples; k++) {
    const deal = sampleDeal(match, me, rand2);
    if (!deal) break;
    options.forEach((o, i) => {
      const w = { ...match, scores: match.scores.slice(), round: { ...match.round, hands: deal.hands.map((h) => h.slice()), aside: deal.aside, line: match.round.line.slice(), missing: match.round.missing.map((x) => x.slice()), log: [], ends: match.round.ends && match.round.ends.slice() } };
      play(w, me, o);
      for (let s = 0; s < 60 && w.phase === "play"; s++) {
        const p = w.round.turn;
        play(w, p, heuristic(w, p, legalPlays2(w, p), rand2));
      }
      const res = w.round.result;
      if (res && res.winner !== null) total[i] += (res.winner === mySide ? 1 : -1) * res.points;
    });
  }
  let bi = 0;
  for (let i = 1; i < options.length; i++) if (total[i] > total[bi]) bi = i;
  return { id: options[bi].id, side: options[bi].side };
}
function choosePlay(match, me, level = "medium", rand2 = Math.random) {
  const options = legalPlays2(match, me);
  if (!options.length) return null;
  if (level === "easy") return options[Math.floor(rand2() * options.length)];
  if (level === "hard" && options.length > 1) return simulate(match, me, options, rand2, 24);
  return heuristic(match, me, options, rand2);
}

// src/games/xo/engine.js
var LINES = [[0, 1, 2], [3, 4, 5], [6, 7, 8], [0, 3, 6], [1, 4, 7], [2, 5, 8], [0, 4, 8], [2, 4, 6]];
var DEFAULT_TARGET2 = 3;
function winnerOf2(board) {
  for (const l of LINES) {
    const [a, b, c] = l;
    if (board[a] && board[a] === board[b] && board[a] === board[c]) return { mark: board[a], line: l };
  }
  return board.every(Boolean) ? { mark: null, line: null } : null;
}
var markOf = (g, p) => g % 2 === 1 === (p === 0) ? "X" : "O";
function createMatch3({ target = DEFAULT_TARGET2 } = {}) {
  return { game: "xo", target, scores: [0, 0], gameNo: 1, board: Array(9).fill(null), turn: 0, phase: "play", result: null, matchWinner: null, lastMove: null };
}
function move2(m, p, cell) {
  if (m.phase !== "play") return { ok: false, error: "not playing" };
  if (m.turn !== p) return { ok: false, error: "not your turn" };
  if (!Number.isInteger(cell) || cell < 0 || cell > 8 || m.board[cell]) return { ok: false, error: "illegal" };
  m.board = m.board.slice();
  m.board[cell] = markOf(m.gameNo, p);
  m.lastMove = cell;
  const w = winnerOf2(m.board);
  if (w) {
    const winner = w.mark === null ? null : markOf(m.gameNo, 0) === w.mark ? 0 : 1;
    if (winner !== null) m.scores[winner] += 1;
    m.result = { winner, line: w.line };
    if (winner !== null && m.scores[winner] >= m.target) {
      m.matchWinner = winner;
      m.phase = "matchover";
    } else m.phase = "gameover";
    return { ok: true, gameOver: true };
  }
  m.turn = 1 - p;
  return { ok: true };
}
function nextGame2(m) {
  if (m.phase !== "gameover") return { ok: false, error: "game not over" };
  m.gameNo += 1;
  m.board = Array(9).fill(null);
  m.result = null;
  m.lastMove = null;
  m.phase = "play";
  m.turn = markOf(m.gameNo, 0) === "X" ? 0 : 1;
  return { ok: true };
}
function forfeit3(m, p) {
  if (m.matchWinner !== null) return { ok: false, error: "over" };
  m.matchWinner = 1 - p;
  m.phase = "matchover";
  m.forfeitedBy = p;
  return { ok: true };
}

// src/games/ludo/engine.js
var TRACK = 52;
var HOME = 56;
var START = [0, 13, 26, 39];
var SAFE = /* @__PURE__ */ new Set([0, 8, 13, 21, 26, 34, 39, 47]);
var absOf = (seat, rel) => rel >= 0 && rel <= 50 ? (START[seat] + rel) % TRACK : null;
var mathDie = () => 1 + Math.floor(Math.random() * 6);
function createMatch4({ active = [true, false, true, false] } = {}) {
  const seats = active.map(Boolean);
  if (seats.filter(Boolean).length < 2) throw new Error("need at least 2 players");
  return {
    game: "ludo",
    active: seats,
    pieces: seats.map((on) => on ? [-1, -1, -1, -1] : null),
    turn: seats.indexOf(true),
    phase: "roll",
    dice: null,
    sixes: 0,
    finished: [],
    winner: null,
    matchWinner: null,
    lastMove: null,
    lastRoll: null
  };
}
function nextActive(m, p) {
  for (let k = 1; k <= 4; k++) {
    const q = (p + k) % 4;
    if (m.active[q] && !m.finished.includes(q)) return q;
  }
  return p;
}
function legalMoves2(m, p = m.turn, dice = m.dice) {
  if (m.phase !== "move" || p !== m.turn || !dice) return [];
  const out = [];
  m.pieces[p].forEach((rel, token) => {
    let to;
    if (rel === -1) {
      if (dice !== 6) return;
      to = 0;
    } else if (rel === HOME) return;
    else {
      to = rel + dice;
      if (to > HOME) return;
    }
    out.push({ token, from: rel, to, capture: capturesAt(m, p, to) });
  });
  return out;
}
function capturesAt(m, p, rel) {
  const abs = absOf(p, rel);
  if (abs === null || SAFE.has(abs)) return [];
  const hits = [];
  m.pieces.forEach((list, q) => {
    if (!list || q === p) return;
    list.forEach((r, t) => {
      if (absOf(q, r) === abs) hits.push({ seat: q, token: t });
    });
  });
  return hits;
}
function roll2(m, p, die = mathDie) {
  if (m.phase !== "roll") return { ok: false, error: "not rolling" };
  if (m.turn !== p) return { ok: false, error: "not your turn" };
  const d = die();
  m.dice = d;
  m.lastRoll = { seat: p, dice: d };
  if (d === 6) m.sixes += 1;
  if (d === 6 && m.sixes >= 3) {
    endTurn(m, true);
    return { ok: true, dice: d, lost: true };
  }
  m.phase = "move";
  if (!legalMoves2(m).length) {
    afterMove(m, d);
    return { ok: true, dice: d, noMove: true };
  }
  return { ok: true, dice: d };
}
function endTurn(m, forced = false) {
  m.sixes = 0;
  m.dice = null;
  m.phase = "roll";
  m.turn = nextActive(m, m.turn);
  return forced;
}
function afterMove(m, d) {
  if (m.winner !== null) return;
  if (d === 6 && m.sixes < 3) {
    m.dice = null;
    m.phase = "roll";
    return;
  }
  endTurn(m);
}
function move3(m, p, token) {
  if (m.phase !== "move") return { ok: false, error: "not moving" };
  if (m.turn !== p) return { ok: false, error: "not your turn" };
  const mv = legalMoves2(m).find((x) => x.token === token);
  if (!mv) return { ok: false, error: "illegal" };
  m.pieces[p] = m.pieces[p].slice();
  m.pieces[p][token] = mv.to;
  for (const c of mv.capture) {
    m.pieces[c.seat] = m.pieces[c.seat].slice();
    m.pieces[c.seat][c.token] = -1;
  }
  m.lastMove = { seat: p, token, from: mv.from, to: mv.to, capture: mv.capture };
  if (m.pieces[p].every((r) => r === HOME)) {
    m.finished.push(p);
    m.winner = p;
    m.matchWinner = p;
    m.phase = "matchover";
    return { ok: true, ...mv, won: true };
  }
  afterMove(m, m.dice);
  return { ok: true, ...mv };
}
function forfeit4(m, p) {
  if (m.matchWinner !== null) return { ok: false, error: "over" };
  m.active = m.active.slice();
  m.active[p] = false;
  m.pieces = m.pieces.slice();
  m.pieces[p] = null;
  const left = m.active.map((on, q) => on ? q : -1).filter((q) => q >= 0);
  if (left.length === 1) {
    m.matchWinner = left[0];
    m.winner = left[0];
    m.phase = "matchover";
    m.forfeitedBy = p;
  } else if (m.turn === p) {
    m.turn = nextActive(m, p);
    m.phase = "roll";
    m.dice = null;
    m.sixes = 0;
  }
  return { ok: true };
}

// src/games/ludo/ai.js
function danger(m, p, rel) {
  const abs = absOf(p, rel);
  if (abs === null || SAFE.has(abs)) return 0;
  let n = 0;
  m.pieces.forEach((list, q) => {
    if (!list || q === p) return;
    for (const r of list) {
      const a = absOf(q, r);
      if (a === null) {
        if (r === -1 && (abs - absOf(q, 0) + 52) % 52 <= 5) n += 0.3;
        continue;
      }
      const gap = (abs - a + 52) % 52;
      if (gap >= 1 && gap <= 6) n += 1;
    }
  });
  return n;
}
function chooseMove(m, p, level = "medium", rand2 = Math.random) {
  const moves = legalMoves2(m, p);
  if (!moves.length) return null;
  if (level === "easy") return moves[Math.floor(rand2() * moves.length)].token;
  if (level === "medium") {
    const cap = moves.find((x) => x.capture.length);
    if (cap) return cap.token;
    const enter = moves.find((x) => x.from === -1);
    if (enter) return enter.token;
    return moves.reduce((a, b) => b.from > a.from ? b : a).token;
  }
  let best = null;
  for (const mv of moves) {
    let s = 0;
    s += mv.capture.length * (30 + mv.capture.reduce((t, c) => t + Math.max(0, m.pieces[c.seat][c.token]), 0) * 0.4);
    if (mv.from === -1) s += 18;
    if (mv.to === HOME) s += 25;
    if (mv.to > 50 && mv.from <= 50) s += 14;
    s += (mv.to - Math.max(mv.from, 0)) * 0.6;
    if (mv.from >= 0 && mv.from <= 50) s += danger(m, p, mv.from) * 9;
    if (mv.to <= 50) s -= danger(m, p, mv.to) * 11;
    if (SAFE.has(absOf(p, mv.to) ?? -1)) s += 6;
    s += rand2() * 0.5;
    if (!best || s > best.s) best = { token: mv.token, s };
  }
  return best.token;
}

// src/games/kunkan/engine.js
var OPEN_MIN = 51;
var NOT_OPENED = 100;
var JOKER_IN_HAND = 25;
var DECK = 106;
var isJoker = (id) => id >= 104;
var suitOf = (id) => isJoker(id) ? -1 : Math.floor(id % 52 / 13);
var rankOf = (id) => isJoker(id) ? 0 : id % 52 % 13 + 1;
var rankValue = (r) => r === 1 ? 1 : r === 14 ? 10 : Math.min(r, 10);
var handValue = (id) => isJoker(id) ? JOKER_IN_HAND : rankOf(id) === 1 ? 10 : Math.min(rankOf(id), 10);
function analyse(cards) {
  if (!Array.isArray(cards) || cards.length < 3) return null;
  if (new Set(cards).size !== cards.length) return null;
  const nat = cards.filter((c) => !isJoker(c));
  if (nat.length < 2) return null;
  return analyseSet(cards, nat) || analyseRun(cards, nat);
}
function analyseSet(cards, nat) {
  if (cards.length > 4) return null;
  const r = rankOf(nat[0]);
  if (!nat.every((c) => rankOf(c) === r)) return null;
  if (new Set(nat.map(suitOf)).size !== nat.length) return null;
  const v = r === 1 ? 10 : rankValue(r);
  return { type: "set", rank: r, value: v * cards.length };
}
function analyseRun(cards, nat) {
  if (cards.length > 14) return null;
  const s = suitOf(nat[0]);
  if (!nat.every((c) => suitOf(c) === s)) return null;
  const len = cards.length;
  const aces = nat.filter((c) => rankOf(c) === 1);
  const others = nat.filter((c) => rankOf(c) !== 1).map(rankOf);
  if (new Set(others).size !== others.length) return null;
  const choices = aces.length === 0 ? [[]] : aces.length === 1 ? [[1], [14]] : aces.length === 2 ? [[1, 14]] : [];
  let best = null;
  for (const aceVals of choices) {
    const vals = [...others, ...aceVals];
    const lo = Math.min(...vals), hi = Math.max(...vals);
    if (hi - lo + 1 > len) continue;
    for (let start = Math.min(lo, 15 - len); start >= Math.max(1, hi - len + 1); start--) {
      let value = 0;
      for (let k = start; k < start + len; k++) value += rankValue(k);
      if (!best || value > best.value) best = { type: "run", suit: s, start, value };
      break;
    }
  }
  if (!best) return null;
  const slots = new Array(len).fill(null);
  const jokers = cards.filter(isJoker);
  const acePlaced = [];
  for (const c of nat) {
    let r = rankOf(c);
    if (r === 1) {
      r = best.start === 1 && !acePlaced.includes(1) ? 1 : 14;
      acePlaced.push(r);
    }
    slots[r - best.start] = c;
  }
  for (let i = 0; i < len; i++) if (slots[i] === null) slots[i] = jokers.pop();
  best.ordered = slots;
  best.layout = slots.map((_, i) => best.start + i);
  return best;
}
function shuffle2(arr, rand2) {
  for (let i = arr.length - 1; i > 0; i--) {
    const j = rand2(i + 1);
    [arr[i], arr[j]] = [arr[j], arr[i]];
  }
  return arr;
}
var defaultRand = (n) => Math.floor(Math.random() * n);
function nextActive2(m, seat) {
  const n = m.active.length;
  for (let k = 1; k <= n; k++) {
    const s = (seat + k) % n;
    if (m.active[s]) return s;
  }
  return seat;
}
function createMatch5({ active = [true, true, false, false, false], rand: rand2 = defaultRand, dealer = null } = {}) {
  const seats = active.map((a, i) => a ? i : -1).filter((i) => i >= 0);
  const m = {
    active: active.slice(),
    scores: active.map((a) => a ? 0 : null),
    roundNo: 0,
    dealer: dealer ?? seats[rand2(seats.length)],
    phase: "draw",
    matchWinner: null,
    history: [],
    round: null
  };
  newRound2(m, rand2);
  return m;
}
function newRound2(m, rand2 = defaultRand) {
  const deck = shuffle2(Array.from({ length: DECK }, (_, i) => i), rand2);
  const hands = m.active.map(() => null);
  let s = m.dealer;
  for (let k = 0; k < m.active.filter(Boolean).length; k++) {
    hands[s] = deck.splice(0, s === m.dealer ? 15 : 14);
    s = nextActive2(m, s);
  }
  m.roundNo += 1;
  m.round = {
    hands,
    stock: deck,
    discard: [],
    melds: [],
    nextMeldId: 1,
    opened: m.active.map(() => false),
    acted: false,
    turn: m.dealer,
    took: null,
    mustOpen: false,
    reshuffles: 0,
    result: null,
    last: null
  };
  m.phase = "play";
  return m;
}
var err = (e) => ({ ok: false, error: e });
function draw(m, seat, from = "stock", rand2 = defaultRand) {
  const r = m.round;
  if (m.phase !== "draw" || r.turn !== seat) return err("notYourTurn");
  if (from === "discard") {
    if (!r.discard.length) return err("emptyDiscard");
    const c2 = r.discard.pop();
    r.hands[seat].push(c2);
    r.took = c2;
    r.mustOpen = !r.opened[seat];
    m.phase = "play";
    r.last = { kind: "take", seat, card: c2 };
    return { ok: true, card: c2 };
  }
  if (!r.stock.length) {
    if (r.discard.length <= 1) {
      endRound2(m, null);
      return { ok: true, card: null, exhausted: true };
    }
    const top = r.discard.pop();
    r.stock = shuffle2(r.discard, rand2);
    r.discard = [top];
    r.reshuffles += 1;
  }
  const c = r.stock.pop();
  r.hands[seat].push(c);
  r.took = null;
  r.mustOpen = false;
  m.phase = "play";
  r.last = { kind: "draw", seat };
  return { ok: true, card: c };
}
function undoTake(m, seat) {
  const r = m.round;
  if (m.phase !== "play" || r.turn !== seat || r.took === null || r.acted) return err("cannotUndo");
  const i = r.hands[seat].indexOf(r.took);
  if (i < 0) return err("cannotUndo");
  r.hands[seat].splice(i, 1);
  r.discard.push(r.took);
  r.took = null;
  r.mustOpen = false;
  m.phase = "draw";
  r.last = { kind: "untake", seat };
  return { ok: true };
}
function ownsAll(hand, cards) {
  const h = hand.slice();
  for (const c of cards) {
    const i = h.indexOf(c);
    if (i < 0) return false;
    h.splice(i, 1);
  }
  return true;
}
function meld(m, seat, groups) {
  const r = m.round;
  if (m.phase !== "play" || r.turn !== seat) return err("notYourTurn");
  if (!Array.isArray(groups) || !groups.length) return err("badMeld");
  const all = groups.flat();
  if (!all.every(Number.isInteger) || new Set(all).size !== all.length || !ownsAll(r.hands[seat], all)) return err("badMeld");
  const infos = groups.map(analyse);
  if (infos.some((x) => !x)) return err("badMeld");
  const total = infos.reduce((t, x) => t + x.value, 0);
  if (!r.opened[seat] && total < OPEN_MIN) return err("needOpen");
  r.hands[seat] = r.hands[seat].filter((c) => !all.includes(c));
  const ids = [];
  groups.forEach((g, i) => {
    const info = infos[i];
    const cards = info.type === "run" ? info.ordered : g.slice();
    const id = r.nextMeldId++;
    r.melds.push({ id, owner: seat, cards, type: info.type });
    ids.push(id);
  });
  r.opened[seat] = true;
  r.acted = true;
  r.mustOpen = false;
  r.last = { kind: "meld", seat, melds: ids };
  if (!r.hands[seat].length) endRound2(m, seat);
  return { ok: true, melds: ids, total };
}
function layoff(m, seat, card, meldId) {
  const r = m.round;
  if (m.phase !== "play" || r.turn !== seat) return err("notYourTurn");
  if (!r.opened[seat]) return err("needOpenFirst");
  const md = r.melds.find((x) => x.id === meldId);
  if (!md || !ownsAll(r.hands[seat], [card])) return err("badLayoff");
  const next2 = tryExtend(md, card);
  if (!next2) return err("badLayoff");
  md.cards = next2;
  r.hands[seat].splice(r.hands[seat].indexOf(card), 1);
  r.acted = true;
  r.last = { kind: "layoff", seat, card, meld: meldId };
  if (!r.hands[seat].length) endRound2(m, seat);
  return { ok: true };
}
function tryExtend(md, card) {
  const info = analyse([...md.cards, card]);
  if (!info || info.type !== md.type) return null;
  return info.type === "run" ? info.ordered : [...md.cards, card];
}
function discard(m, seat, card) {
  const r = m.round;
  if (m.phase !== "play" || r.turn !== seat) return err("notYourTurn");
  if (!ownsAll(r.hands[seat], [card])) return err("badCard");
  if (r.mustOpen && !r.opened[seat]) return err("mustOpen");
  if (r.took !== null && card === r.took) return err("sameCard");
  r.hands[seat].splice(r.hands[seat].indexOf(card), 1);
  r.discard.push(card);
  r.last = { kind: "discard", seat, card };
  if (!r.hands[seat].length) {
    endRound2(m, seat);
    return { ok: true, out: true };
  }
  r.turn = nextActive2(m, seat);
  r.took = null;
  r.mustOpen = false;
  r.acted = false;
  m.phase = "draw";
  return { ok: true };
}
function endRound2(m, winner) {
  const r = m.round;
  const points2 = m.active.map((a, s) => {
    if (!a) return null;
    if (winner === null) return 0;
    if (s === winner) return 0;
    if (!r.opened[s]) return NOT_OPENED;
    return r.hands[s].reduce((t, c) => t + handValue(c), 0);
  });
  points2.forEach((p, s) => {
    if (p !== null) m.scores[s] += p;
  });
  r.result = { winner, points: points2, hands: r.hands.map((h) => h ? h.slice() : null), totals: m.scores.slice() };
  m.history.push(points2);
  m.phase = "roundover";
  if (winner !== null) m.dealer = winner;
}
function nextRound2(m, rand2 = defaultRand) {
  if (m.phase !== "roundover") return err("notOver");
  newRound2(m, rand2);
  return { ok: true };
}
function forfeit5(m, seat) {
  if (m.matchWinner !== null) return err("over");
  let best = null;
  m.active.forEach((a, s) => {
    if (a && s !== seat && (best === null || m.scores[s] < m.scores[best])) best = s;
  });
  m.matchWinner = best;
  m.forfeitBy = seat;
  m.phase = "matchover";
  return { ok: true };
}
function viewFor2(m, seat) {
  const r = m.round;
  const showAll = m.phase === "roundover" || m.phase === "matchover";
  return {
    ...m,
    round: {
      ...r,
      hands: r.hands.map((h, s) => h === null ? null : s === seat || showAll ? h.slice() : h.length),
      stock: r.stock.length,
      discard: r.discard.slice(-1),
      discardCount: r.discard.length
    }
  };
}

// src/games/kunkan/ai.js
function candidates(hand) {
  const nat = hand.filter((c) => !isJoker(c));
  const jokers = hand.filter(isJoker);
  const out = [];
  const seen = /* @__PURE__ */ new Set();
  const add = (cards) => {
    const key = cards.slice().sort((a, b) => a - b).join(",");
    if (seen.has(key)) return;
    if (analyse(cards)) {
      seen.add(key);
      out.push(cards);
    }
  };
  const byRank = /* @__PURE__ */ new Map();
  for (const c of nat) {
    const r = rankOf(c);
    if (!byRank.has(r)) byRank.set(r, /* @__PURE__ */ new Map());
    const m = byRank.get(r);
    if (!m.has(suitOf(c))) m.set(suitOf(c), c);
  }
  for (const m of byRank.values()) {
    const cs = [...m.values()];
    const subsets = (k) => {
      const res = [];
      const rec = (i, acc) => {
        if (acc.length === k) {
          res.push(acc.slice());
          return;
        }
        for (let j = i; j < cs.length; j++) {
          acc.push(cs[j]);
          rec(j + 1, acc);
          acc.pop();
        }
      };
      rec(0, []);
      return res;
    };
    for (const k of [3, 4]) for (const s of subsets(k)) add(s);
    if (jokers.length) for (const s of subsets(2)) add([...s, jokers[0]]);
    if (jokers.length) for (const s of subsets(3)) add([...s, jokers[0]]);
  }
  for (let s = 0; s < 4; s++) {
    const byR = /* @__PURE__ */ new Map();
    for (const c of nat) if (suitOf(c) === s) {
      const r = rankOf(c);
      if (!byR.has(r)) byR.set(r, c);
    }
    const at = (r) => byR.get(r === 14 ? 1 : r);
    for (let start = 1; start <= 12; start++) {
      for (let end = start + 2; end <= 14; end++) {
        const cards = [];
        let gaps = 0;
        let gapOk = true;
        for (let r = start; r <= end; r++) {
          const c = at(r);
          if (c === void 0 || r === 14 && start === 1) {
            gaps++;
            if (gaps > Math.min(1, jokers.length)) {
              gapOk = false;
              break;
            }
            cards.push(jokers[0]);
          } else cards.push(c);
        }
        if (!gapOk) break;
        add(cards);
      }
    }
  }
  return out;
}
function bestMelds(hand, { maxCards = Infinity } = {}) {
  const cands = candidates(hand).map((cards) => ({ cards, value: analyse(cards).value }));
  cands.sort((a, b) => b.value - a.value);
  let best = { groups: [], value: 0, used: 0 };
  let nodes = 0;
  const rec = (i, used, groups, value, n) => {
    if (++nodes > 2e4) return;
    if (value > best.value) best = { groups: groups.slice(), value, used: n };
    for (let j = i; j < cands.length; j++) {
      const c = cands[j];
      if (n + c.cards.length > maxCards) continue;
      if (c.cards.some((x) => used.has(x))) continue;
      c.cards.forEach((x) => used.add(x));
      groups.push(c.cards);
      rec(j + 1, used, groups, value + c.value, n + c.cards.length);
      groups.pop();
      c.cards.forEach((x) => used.delete(x));
    }
  };
  rec(0, /* @__PURE__ */ new Set(), [], 0, 0);
  return best;
}
function connections(hand, c) {
  if (isJoker(c)) return 99;
  const r = rankOf(c), s = suitOf(c);
  let n = 0;
  for (const o of hand) {
    if (o === c || isJoker(o)) continue;
    const ro = rankOf(o);
    if (ro === r && suitOf(o) !== s) n += 2;
    if (suitOf(o) === s) {
      const d = Math.min(Math.abs(ro - r), Math.abs((ro === 1 ? 14 : ro) - (r === 1 ? 14 : r)));
      if (d === 1) n += 2;
      else if (d === 2) n += 1;
    }
  }
  return n;
}
function chooseDiscard(m, seat, level, rand2) {
  const r = m.round;
  const hand = r.hands[seat];
  const pool = hand.filter((c) => c !== r.took);
  const nonJ = pool.filter((c) => !isJoker(c));
  const list = nonJ.length ? nonJ : pool;
  if (level === "easy") return list[Math.floor(rand2() * list.length)];
  const next2 = nextSeat3(m, seat);
  let best = null;
  for (const c of list) {
    let s = connections(hand, c) * 10 - handValue(c);
    if (level === "hard" && r.opened[next2] && r.melds.some((md) => tryExtend(md, c))) s += 25;
    s += rand2() * 0.5;
    if (!best || s < best.s) best = { c, s };
  }
  return best.c;
}
function nextSeat3(m, seat) {
  const n = m.active.length;
  for (let k = 1; k <= n; k++) {
    const s = (seat + k) % n;
    if (m.active[s]) return s;
  }
  return seat;
}
function chooseAction(m, seat, level = "medium", rand2 = Math.random) {
  const r = m.round;
  const hand = r.hands[seat];
  if (m.phase === "draw") {
    const top = Array.isArray(r.discard) ? r.discard[r.discard.length - 1] : void 0;
    if (level !== "easy" && top !== void 0) {
      if (r.opened[seat]) {
        const before = bestMelds(hand).used;
        const after2 = bestMelds([...hand, top]);
        if (after2.used > before && after2.groups.some((g) => g.includes(top))) return { a: "draw", from: "discard" };
        if (!isJoker(top) && r.melds.some((md) => tryExtend(md, top))) return { a: "draw", from: "discard" };
      } else {
        const after2 = bestMelds([...hand, top]);
        if (after2.value >= OPEN_MIN && after2.groups.some((g) => g.includes(top)) && after2.used < hand.length + 1) return { a: "draw", from: "discard" };
      }
    }
    return { a: "draw", from: "stock" };
  }
  if (!r.opened[seat]) {
    const bm = bestMelds(hand, { maxCards: hand.length - 1 });
    const bmAll = bestMelds(hand);
    if (bmAll.used === hand.length && bmAll.value >= OPEN_MIN) return { a: "meld", groups: bmAll.groups };
    if (bm.value >= OPEN_MIN) return { a: "meld", groups: bm.groups };
  } else {
    const all = bestMelds(hand);
    if (all.used === hand.length && all.groups.length) return { a: "meld", groups: all.groups };
    const bm = bestMelds(hand, { maxCards: hand.length - 1 });
    if (bm.groups.length) return { a: "meld", groups: [bm.groups[0]] };
    for (const c of hand) {
      if (isJoker(c) && hand.length > 2) continue;
      const md = r.melds.find((x) => tryExtend(x, c));
      if (md) return { a: "layoff", card: c, meld: md.id };
    }
  }
  if (r.mustOpen && !r.opened[seat]) return { a: "undoTake" };
  return { a: "discard", card: chooseDiscard(m, seat, level, rand2) };
}

// src/games/snakes/engine.js
var LADDERS = { 1: 38, 4: 14, 9: 31, 21: 42, 28: 84, 36: 44, 51: 67, 71: 91, 80: 100 };
var SNAKES = { 16: 6, 47: 26, 49: 11, 56: 53, 62: 19, 64: 60, 87: 24, 93: 73, 95: 75, 98: 78 };
var GOAL = 100;
var mathDie2 = () => 1 + Math.floor(Math.random() * 6);
function nextActive3(m, seat) {
  for (let k = 1; k <= 4; k++) {
    const s = (seat + k) % 4;
    if (m.active[s]) return s;
  }
  return seat;
}
function createMatch6({ active = [true, false, true, false] } = {}) {
  return { active: active.slice(), pos: active.map((a) => a ? 0 : null), turn: active.indexOf(true), phase: "roll", lastRoll: null, matchWinner: null, rolls: 0 };
}
function roll3(m, p, die = mathDie2) {
  if (m.matchWinner !== null || m.phase !== "roll") return { ok: false, error: "over" };
  if (m.turn !== p) return { ok: false, error: "notYourTurn" };
  const d = die();
  const from = m.pos[p];
  let land = from + d;
  let to = land, via = null;
  if (land > GOAL) {
    land = from;
    to = from;
  } else if (LADDERS[land]) {
    to = LADDERS[land];
    via = "ladder";
  } else if (SNAKES[land]) {
    to = SNAKES[land];
    via = "snake";
  }
  m.pos[p] = to;
  m.rolls += 1;
  m.lastRoll = { seat: p, dice: d, from, land, to, via, n: m.rolls };
  if (to === GOAL) {
    m.matchWinner = p;
    m.phase = "over";
    return { ok: true, ...m.lastRoll, won: true };
  }
  if (d !== 6) m.turn = nextActive3(m, p);
  return { ok: true, ...m.lastRoll };
}
function forfeit6(m, seat) {
  if (m.matchWinner !== null) return { ok: false, error: "over" };
  const others = m.active.map((a, s) => a && s !== seat ? s : -1).filter((s) => s >= 0);
  m.matchWinner = others.sort((a, b) => m.pos[b] - m.pos[a])[0] ?? null;
  m.forfeitedBy = seat;
  m.phase = "over";
  return { ok: true };
}

// src/games/uno/engine.js
var TARGET = 300;
var SKIP = 10;
var REVERSE = 11;
var DRAW2 = 12;
var WILD = 13;
var WILD4 = 14;
var CARDS = (() => {
  const out = [];
  for (let c = 0; c < 4; c++) {
    out.push({ c, v: 0 });
    for (let v = 1; v <= 12; v++) {
      out.push({ c, v });
      out.push({ c, v });
    }
  }
  for (let k = 0; k < 4; k++) out.push({ c: 4, v: WILD });
  for (let k = 0; k < 4; k++) out.push({ c: 4, v: WILD4 });
  return out;
})();
var DECK2 = CARDS.length;
var points = (id) => {
  const { v } = CARDS[id];
  return v >= WILD ? 50 : v >= SKIP ? 20 : v;
};
var defaultRand2 = (n) => Math.floor(Math.random() * n);
function shuffle3(a, rand2) {
  for (let i = a.length - 1; i > 0; i--) {
    const j = rand2(i + 1);
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
}
function nextSeat4(m, seat, steps = 1) {
  let s = seat;
  for (let k = 0; k < steps; k++) {
    do {
      s = (s + m.dir + 4) % 4;
    } while (!m.active[s]);
  }
  return s;
}
function createMatch7({ active = [true, false, true, false], rand: rand2 = defaultRand2, target = TARGET } = {}) {
  const m = { active: active.slice(), scores: active.map((a) => a ? 0 : null), target, dealer: active.indexOf(true), roundNo: 0, matchWinner: null, phase: "play", round: null, dir: 1 };
  newRound3(m, rand2);
  return m;
}
function newRound3(m, rand2 = defaultRand2) {
  const deck = shuffle3(Array.from({ length: DECK2 }, (_, i) => i), rand2);
  const hands = m.active.map((a) => a ? deck.splice(0, 7) : null);
  let first;
  for (; ; ) {
    first = deck.pop();
    if (CARDS[first].v !== WILD4) break;
    deck.unshift(first);
  }
  m.dir = 1;
  m.roundNo += 1;
  const r = { hands, draw: deck, discard: [first], color: CARDS[first].c === 4 ? rand2(4) : CARDS[first].c, turn: 0, drew: null, result: null, last: null };
  m.round = r;
  m.phase = "play";
  const v = CARDS[first].v;
  if (v === REVERSE) m.dir = -1;
  let start = countActive(m) === 2 && v === REVERSE ? m.dealer : nextSeat4(m, m.dealer);
  if (v === SKIP) start = nextSeat4(m, start);
  if (v === DRAW2) {
    drawCards(m, start, 2, rand2);
    start = nextSeat4(m, start);
  }
  r.turn = start;
  return m;
}
var countActive = (m) => m.active.filter(Boolean).length;
var err2 = (e) => ({ ok: false, error: e });
function refill(m, rand2) {
  const r = m.round;
  if (r.draw.length) return true;
  if (r.discard.length <= 1) return false;
  const top = r.discard.pop();
  r.draw = shuffle3(r.discard, rand2);
  r.discard = [top];
  return true;
}
function drawCards(m, seat, n, rand2) {
  const got = [];
  for (let k = 0; k < n; k++) {
    if (!refill(m, rand2)) break;
    const c = m.round.draw.pop();
    m.round.hands[seat].push(c);
    got.push(c);
  }
  return got;
}
var topCard = (m) => m.round.discard[m.round.discard.length - 1];
function canPlay(m, id) {
  const card = CARDS[id], top = CARDS[topCard(m)];
  if (card.c === 4) return true;
  return card.c === m.round.color || card.v === top.v;
}
function legalPlays3(m, seat) {
  const r = m.round;
  if (m.phase !== "play" || r.turn !== seat || !Array.isArray(r.hands[seat])) return [];
  const hand = r.drew !== null ? [r.drew] : r.hands[seat];
  return hand.filter((id) => canPlay(m, id));
}
function play2(m, seat, id, color = null, rand2 = defaultRand2) {
  const r = m.round;
  if (m.phase !== "play" || r.turn !== seat) return err2("notYourTurn");
  if (!r.hands[seat].includes(id)) return err2("badCard");
  if (r.drew !== null && id !== r.drew) return err2("onlyDrawn");
  if (!canPlay(m, id)) return err2("cantPlay");
  const card = CARDS[id];
  if (card.c === 4 && !(Number.isInteger(color) && color >= 0 && color < 4)) return err2("needColor");
  r.hands[seat].splice(r.hands[seat].indexOf(id), 1);
  r.discard.push(id);
  r.color = card.c === 4 ? color : card.c;
  r.drew = null;
  const res = { ok: true, card: id, color: r.color };
  r.last = { kind: "play", seat, card: id, color: r.color };
  if (!r.hands[seat].length) {
    endRound3(m, seat);
    res.out = true;
    return res;
  }
  let next2 = nextSeat4(m, seat);
  if (card.v === SKIP) {
    res.skipped = next2;
    next2 = nextSeat4(m, next2);
  } else if (card.v === REVERSE) {
    m.dir = -m.dir;
    if (countActive(m) === 2) {
      res.skipped = nextSeat4(m, seat);
      next2 = seat;
    } else next2 = nextSeat4(m, seat);
  } else if (card.v === DRAW2) {
    drawCards(m, next2, 2, rand2);
    res.skipped = next2;
    res.drawn = 2;
    next2 = nextSeat4(m, next2);
  } else if (card.v === WILD4) {
    drawCards(m, next2, 4, rand2);
    res.skipped = next2;
    res.drawn = 4;
    next2 = nextSeat4(m, next2);
  }
  r.turn = next2;
  return res;
}
function draw2(m, seat, rand2 = defaultRand2) {
  const r = m.round;
  if (m.phase !== "play" || r.turn !== seat) return err2("notYourTurn");
  if (r.drew !== null) return err2("alreadyDrew");
  const got = drawCards(m, seat, 1, rand2);
  if (!got.length) {
    r.turn = nextSeat4(m, seat);
    return { ok: true, card: null, passed: true };
  }
  const c = got[0];
  r.last = { kind: "draw", seat };
  if (canPlay(m, c)) {
    r.drew = c;
    return { ok: true, card: c, playable: true };
  }
  r.turn = nextSeat4(m, seat);
  return { ok: true, card: c, playable: false, passed: true };
}
function pass(m, seat) {
  const r = m.round;
  if (m.phase !== "play" || r.turn !== seat || r.drew === null) return err2("cantPass");
  r.drew = null;
  r.turn = nextSeat4(m, seat);
  r.last = { kind: "pass", seat };
  return { ok: true };
}
function endRound3(m, winner) {
  const r = m.round;
  let pts = 0;
  r.hands.forEach((h, s) => {
    if (h && s !== winner) pts += h.reduce((t, c) => t + points(c), 0);
  });
  m.scores[winner] += pts;
  r.result = { winner, points: pts, hands: r.hands.map((h) => h ? h.slice() : null) };
  m.dealer = winner;
  if (m.scores[winner] >= m.target) {
    m.matchWinner = winner;
    m.phase = "matchover";
  } else m.phase = "roundover";
}
function nextRound3(m, rand2 = defaultRand2) {
  if (m.phase !== "roundover") return err2("notOver");
  newRound3(m, rand2);
  return { ok: true };
}
function forfeit7(m, seat) {
  if (m.matchWinner !== null) return err2("over");
  let best = null;
  m.active.forEach((a, s) => {
    if (a && s !== seat && (best === null || m.scores[s] > m.scores[best])) best = s;
  });
  m.matchWinner = best;
  m.forfeitedBy = seat;
  m.phase = "matchover";
  return { ok: true };
}
function viewFor3(m, seat) {
  const r = m.round;
  const showAll = m.phase !== "play";
  return {
    ...m,
    round: { ...r, hands: r.hands.map((h, s) => h === null ? null : s === seat || showAll ? h.slice() : h.length), draw: r.draw.length, discard: r.discard.slice(-3), drew: r.turn === seat ? r.drew : null }
  };
}

// src/games/uno/ai.js
function bestColor(hand, rand2) {
  const n = [0, 0, 0, 0];
  for (const id of hand) if (CARDS[id].c < 4) n[CARDS[id].c] += 1;
  const max = Math.max(...n);
  if (max === 0) return Math.floor(rand2() * 4);
  return n.indexOf(max);
}
function chooseAction2(m, seat, level = "medium", rand2 = Math.random) {
  const r = m.round;
  const hand = r.hands[seat];
  const plays = legalPlays3(m, seat);
  if (!plays.length) return r.drew !== null ? { a: "pass" } : { a: "draw" };
  if (level === "easy") {
    const id2 = plays[Math.floor(rand2() * plays.length)];
    return { a: "play", card: id2, color: CARDS[id2].c === 4 ? Math.floor(rand2() * 4) : void 0 };
  }
  const next2 = nextSeat4(m, seat);
  const nextCount = Array.isArray(r.hands[next2]) ? r.hands[next2].length : r.hands[next2];
  const fav = bestColor(hand.filter((x) => !plays.includes(x) || CARDS[x].c < 4), rand2);
  let best = null;
  for (const id2 of plays) {
    const { c, v } = CARDS[id2];
    let s = 0;
    if (c === 4) s -= v === WILD4 ? 30 : 20;
    if (c === fav) s += 6;
    if (level === "hard") {
      s += points(id2) * 0.3;
      if (nextCount <= 2 && (v === DRAW2 || v === WILD4 || v === SKIP || v === REVERSE)) s += 40;
    }
    if (hand.length <= 2 && c === 4) s += 25;
    s += rand2() * 0.5;
    if (!best || s > best.s) best = { id: id2, s };
  }
  const id = best.id;
  return { a: "play", card: id, color: CARDS[id].c === 4 ? bestColor(hand.filter((x) => x !== id), rand2) : void 0 };
}

// src/games/mheibes/engine.js
var HANDS = 6;
var TARGET2 = 10;
function createMatch8({ firstHider = 1, target = TARGET2, hands = HANDS } = {}) {
  return { scores: [0, 0], target, hands, hider: firstHider, phase: "hide", ring: null, out: [], roundNo: 1, result: null, matchWinner: null, history: [] };
}
var err3 = (e) => ({ ok: false, error: e });
function hide(m, team, hand) {
  if (m.phase !== "hide" || team !== m.hider) return err3("notYourTurn");
  if (!Number.isInteger(hand) || hand < 0 || hand >= m.hands) return err3("badHand");
  m.ring = hand;
  m.out = [];
  m.phase = "guess";
  return { ok: true };
}
function finish(m, found, kind, hand) {
  const guesser = 1 - m.hider;
  const winner = found ? guesser : m.hider;
  m.scores[winner] += 1;
  m.result = { found, kind, hand, ring: m.ring, winner, hider: m.hider };
  m.history.push(m.ring);
  if (found) m.hider = guesser;
  m.phase = m.scores[winner] >= m.target ? "over" : "reveal";
  if (m.phase === "over") m.matchWinner = winner;
}
function guess(m, team, hand, kind) {
  if (m.phase !== "guess" || team !== 1 - m.hider) return err3("notYourTurn");
  if (!Number.isInteger(hand) || hand < 0 || hand >= m.hands || m.out.includes(hand)) return err3("badHand");
  if (kind !== "bat" && kind !== "jib") return err3("badKind");
  if (kind === "jib") {
    finish(m, hand === m.ring, kind, hand);
    return { ok: true, found: hand === m.ring };
  }
  if (hand === m.ring) {
    finish(m, false, kind, hand);
    return { ok: true, found: false };
  }
  m.out.push(hand);
  if (m.out.length === m.hands - 1) {
    finish(m, true, "last", m.ring);
    return { ok: true, found: true, last: true };
  }
  return { ok: true, empty: true };
}
function next(m) {
  if (m.phase !== "reveal") return err3("notOver");
  m.phase = "hide";
  m.ring = null;
  m.out = [];
  m.result = null;
  m.roundNo += 1;
  return { ok: true };
}
function forfeit8(m, team) {
  if (m.matchWinner !== null) return err3("over");
  m.matchWinner = 1 - team;
  m.forfeitedBy = team;
  m.phase = "over";
  return { ok: true };
}
function viewFor4(m, team) {
  const show = m.phase === "reveal" || m.phase === "over" || team === m.hider;
  return { ...m, ring: show ? m.ring : null, out: m.out.slice(), history: void 0 };
}

// server/games.js
var serverDie = () => randomInt(1, 7);
var rand = (n) => randomInt(0, n);
function tawlaAct(m, seat, msg) {
  let res, anim = null;
  switch (msg.a) {
    case "rollOpening": {
      res = rollOpening(m, seat, serverDie);
      if (res.ok) anim = { kind: "opening", player: seat, result: res, openingDice: m.openingDice.slice() };
      break;
    }
    case "roll": {
      res = roll(m, seat, serverDie);
      if (res.ok) {
        const blocked = m.turn !== seat;
        anim = { kind: "roll", player: seat, dice: blocked ? m.lastTurn.rolled : m.rolled, blocked };
      }
      break;
    }
    case "move": {
      const mv = msg.move;
      const valid = mv && typeof mv === "object" && (mv.from === BAR || Number.isInteger(mv.from) && mv.from >= 0 && mv.from < 24) && (mv.to === OFF || Number.isInteger(mv.to) && mv.to >= 0 && mv.to < 24) && Number.isInteger(mv.die) && mv.die >= 1 && mv.die <= 6;
      if (!valid) return { ok: false, error: "\u062D\u0631\u0643\u0629 \u063A\u064A\u0631 \u0635\u0627\u0644\u062D\u0629" };
      const before = m.pos;
      res = move(m, seat, { from: mv.from, to: mv.to, die: mv.die });
      if (res.ok) anim = { kind: "move", player: seat, move: { from: mv.from, to: mv.to, die: mv.die }, hit: res.hit, before };
      break;
    }
    case "undo": {
      const before = m.pos;
      const last = m.turnMoves[m.turnMoves.length - 1];
      res = undo(m, seat);
      if (res.ok) anim = { kind: "undo", player: seat, move: last, before };
      break;
    }
    case "nextGame": {
      res = nextGame(m);
      if (res.ok) anim = { kind: "newgame" };
      break;
    }
    case "resign": {
      res = forfeit(m, seat);
      if (res.ok) anim = { kind: "forfeit", loser: seat };
      break;
    }
    default:
      return { ok: false, error: "\u0625\u062C\u0631\u0627\u0621 \u063A\u064A\u0631 \u0645\u0639\u0631\u0648\u0641" };
  }
  if (!res.ok) return res;
  const anims = [anim];
  if (anim?.kind === "move" && m.phase === "gameover" && m.gameResult) anims.push({ kind: "gameover", result: m.gameResult });
  return { ok: true, anims };
}
function dominoAct(m, seat, msg) {
  let res, anim = null;
  switch (msg.a) {
    case "play": {
      const id = msg.id, side = msg.side;
      if (!Number.isInteger(id) || id < 0 || id > 48 || side !== "L" && side !== "R") return { ok: false, error: "\u062D\u0631\u0643\u0629 \u063A\u064A\u0631 \u0635\u0627\u0644\u062D\u0629" };
      res = play(m, seat, { id, side });
      if (res.ok) anim = { kind: "play", player: seat, id, side: res.side };
      break;
    }
    case "nextRound": {
      res = nextRound(m, rand);
      if (res.ok) anim = { kind: "newround" };
      break;
    }
    case "resign": {
      res = forfeit2(m, seat);
      if (res.ok) anim = { kind: "forfeit", loser: seat };
      break;
    }
    default:
      return { ok: false, error: "\u0625\u062C\u0631\u0627\u0621 \u063A\u064A\u0631 \u0645\u0639\u0631\u0648\u0641" };
  }
  if (!res.ok) return res;
  const anims = [anim];
  if (m.phase === "roundover" || m.phase === "matchover" && anim.kind !== "forfeit") anims.push({ kind: "roundover", result: m.round.result });
  return { ok: true, anims };
}
function xoAct(m, seat, msg) {
  let res, anim = null;
  switch (msg.a) {
    case "move": {
      if (!Number.isInteger(msg.cell)) return { ok: false, error: "\u062D\u0631\u0643\u0629 \u063A\u064A\u0631 \u0635\u0627\u0644\u062D\u0629" };
      res = move2(m, seat, msg.cell);
      if (res.ok) anim = { kind: "move", player: seat, cell: msg.cell };
      break;
    }
    case "nextGame": {
      res = nextGame2(m);
      if (res.ok) anim = { kind: "newgame" };
      break;
    }
    case "resign": {
      res = forfeit3(m, seat);
      if (res.ok) anim = { kind: "forfeit", loser: seat };
      break;
    }
    default:
      return { ok: false, error: "\u0625\u062C\u0631\u0627\u0621 \u063A\u064A\u0631 \u0645\u0639\u0631\u0648\u0641" };
  }
  if (!res.ok) return res;
  return { ok: true, anims: [anim] };
}
function ludoAct(m, seat, msg) {
  let res, anim = null;
  switch (msg.a) {
    case "roll": {
      res = roll2(m, seat, serverDie);
      if (res.ok) anim = { kind: "roll", player: seat, dice: res.dice, noMove: !!res.noMove, lost: !!res.lost };
      break;
    }
    case "move": {
      if (!Number.isInteger(msg.token) || msg.token < 0 || msg.token > 3) return { ok: false, error: "\u062D\u0631\u0643\u0629 \u063A\u064A\u0631 \u0635\u0627\u0644\u062D\u0629" };
      res = move3(m, seat, msg.token);
      if (res.ok) anim = { kind: "move", player: seat, token: msg.token, from: res.from, to: res.to, capture: res.capture };
      break;
    }
    case "resign": {
      res = forfeit4(m, seat);
      if (res.ok) anim = { kind: "forfeit", loser: seat };
      break;
    }
    default:
      return { ok: false, error: "\u0625\u062C\u0631\u0627\u0621 \u063A\u064A\u0631 \u0645\u0639\u0631\u0648\u0641" };
  }
  if (!res.ok) return res;
  return { ok: true, anims: [anim] };
}
var isCard = (c) => Number.isInteger(c) && c >= 0 && c < DECK;
function kunkanAct(m, seat, msg) {
  let res, anim = null;
  switch (msg.a) {
    case "draw": {
      if (msg.from !== "stock" && msg.from !== "discard") return { ok: false, error: "bad" };
      res = draw(m, seat, msg.from, rand);
      if (res.ok) anim = { kind: "draw", player: seat, from: msg.from, card: msg.from === "discard" ? res.card : void 0 };
      break;
    }
    case "meld": {
      const g = msg.groups;
      if (!Array.isArray(g) || !g.length || g.length > 5 || !g.every((x) => Array.isArray(x) && x.length >= 3 && x.length <= 14 && x.every(isCard))) return { ok: false, error: "badMeld" };
      res = meld(m, seat, g);
      if (res.ok) anim = { kind: "meld", player: seat, melds: res.melds };
      break;
    }
    case "layoff": {
      if (!isCard(msg.card) || !Number.isInteger(msg.meld)) return { ok: false, error: "badLayoff" };
      res = layoff(m, seat, msg.card, msg.meld);
      if (res.ok) anim = { kind: "layoff", player: seat, card: msg.card, meld: msg.meld };
      break;
    }
    case "discard": {
      if (!isCard(msg.card)) return { ok: false, error: "badCard" };
      res = discard(m, seat, msg.card);
      if (res.ok) anim = { kind: "discard", player: seat, card: msg.card };
      break;
    }
    case "undoTake": {
      res = undoTake(m, seat);
      if (res.ok) anim = { kind: "untake", player: seat };
      break;
    }
    case "nextRound": {
      res = nextRound2(m, rand);
      if (res.ok) anim = { kind: "newround" };
      break;
    }
    case "resign": {
      res = forfeit5(m, seat);
      if (res.ok) anim = { kind: "forfeit", loser: seat };
      break;
    }
    default:
      return { ok: false, error: "bad" };
  }
  if (!res.ok) return res;
  const anims = [anim];
  if (m.phase === "roundover" && anim.kind !== "newround") anims.push({ kind: "roundover" });
  return { ok: true, anims };
}
function snakesAct(m, seat, msg) {
  let res, anim;
  if (msg.a === "roll") {
    res = roll3(m, seat, serverDie);
    if (res.ok) anim = { kind: "roll", ...res, player: seat };
  } else if (msg.a === "resign") {
    res = forfeit6(m, seat);
    if (res.ok) anim = { kind: "forfeit", loser: seat };
  } else return { ok: false, error: "bad" };
  return res.ok ? { ok: true, anims: [anim] } : res;
}
function unoAct(m, seat, msg) {
  let res, anim;
  switch (msg.a) {
    case "play": {
      if (!Number.isInteger(msg.card) || msg.card < 0 || msg.card >= DECK2) return { ok: false, error: "bad" };
      res = play2(m, seat, msg.card, Number.isInteger(msg.color) ? msg.color : null, rand);
      if (res.ok) anim = { kind: "play", player: seat, card: msg.card, color: res.color, skipped: res.skipped, drawn: res.drawn };
      break;
    }
    case "draw": {
      res = draw2(m, seat, rand);
      if (res.ok) anim = { kind: "draw", player: seat, passed: !!res.passed };
      break;
    }
    case "pass": {
      res = pass(m, seat);
      if (res.ok) anim = { kind: "pass", player: seat };
      break;
    }
    case "nextRound": {
      res = nextRound3(m, rand);
      if (res.ok) anim = { kind: "newround" };
      break;
    }
    case "resign": {
      res = forfeit7(m, seat);
      if (res.ok) anim = { kind: "forfeit", loser: seat };
      break;
    }
    default:
      return { ok: false, error: "bad" };
  }
  return res.ok ? { ok: true, anims: [anim] } : res;
}
function mheibesAct(m, seat, msg) {
  let res, anim;
  switch (msg.a) {
    case "hide": {
      res = hide(m, seat, msg.hand);
      if (res.ok) anim = { kind: "hide", team: seat };
      break;
    }
    case "guess": {
      res = guess(m, seat, msg.hand, msg.how);
      if (res.ok) anim = { kind: "guess", team: seat, hand: msg.hand, how: msg.how, found: res.found, empty: res.empty };
      break;
    }
    case "nextRound": {
      res = next(m);
      if (res.ok) anim = { kind: "newround" };
      break;
    }
    case "resign": {
      res = forfeit8(m, seat);
      if (res.ok) anim = { kind: "forfeit", loser: seat };
      break;
    }
    default:
      return { ok: false, error: "bad" };
  }
  return res.ok ? { ok: true, anims: [anim] } : res;
}
var GAMES = {
  snakes: {
    seats: 4,
    create: (active) => createMatch6({ active: active || [true, false, true, false] }),
    view: (m) => m,
    act: snakesAct,
    forfeit: (m, seat) => forfeit6(m, seat),
    over: (m) => m.matchWinner !== null,
    bots: true,
    startPartial: true,
    turnSeat: (m) => m.matchWinner === null ? m.turn : null,
    botMove: () => ({ a: "roll" })
  },
  uno: {
    seats: 4,
    create: (active) => createMatch7({ active: active || [true, false, true, false], rand }),
    view: (m, seat) => viewFor3(m, seat),
    act: unoAct,
    forfeit: (m, seat) => forfeit7(m, seat),
    over: (m) => m.matchWinner !== null,
    bots: true,
    startPartial: true,
    turnSeat: (m) => m.phase === "play" ? m.round.turn : null,
    botMove: (m, seat) => {
      const a = chooseAction2(m, seat, "medium");
      return a.a === "play" ? { a: "play", card: a.card, color: a.color } : a;
    }
  },
  mheibes: {
    seats: 2,
    create: () => createMatch8({ firstHider: rand(2) }),
    view: (m, seat) => viewFor4(m, seat),
    act: mheibesAct,
    forfeit: (m, seat) => forfeit8(m, seat),
    over: (m) => m.matchWinner !== null
  },
  // Kunkan: 2 to 5 players; start with whoever joined, or let the computer fill the empty seats.
  kunkan: {
    seats: 5,
    create: (active) => createMatch5({ active: active || [true, true, false, false, false], rand }),
    view: (m, seat) => viewFor2(m, seat),
    act: kunkanAct,
    forfeit: (m, seat) => forfeit5(m, seat),
    over: (m) => m.matchWinner !== null,
    bots: true,
    startPartial: true,
    turnSeat: (m) => m.phase === "draw" || m.phase === "play" ? m.round.turn : null,
    botMove: (m, seat) => {
      const a = chooseAction(m, seat, "medium");
      if (kunkanAct(structuredClone(m), seat, a).ok) return a;
      if (m.phase === "draw") return { a: "draw", from: "stock" };
      if (m.round.mustOpen && !m.round.opened[seat]) return { a: "undoTake" };
      return { a: "discard", card: m.round.hands[seat].find((c) => c !== m.round.took) ?? m.round.hands[seat][0] };
    }
  },
  // 2 to 4 players. The room can start with whoever has joined, or fill empty seats with the computer.
  ludo: {
    seats: 4,
    create: (active) => createMatch4({ active: active || [true, false, true, false] }),
    view: (m) => m,
    act: ludoAct,
    forfeit: (m, seat) => forfeit4(m, seat),
    over: (m) => m.matchWinner !== null,
    bots: true,
    startPartial: true,
    turnSeat: (m) => m.phase === "roll" || m.phase === "move" ? m.turn : null,
    botMove: (m, seat) => m.phase === "roll" ? { a: "roll" } : { a: "move", token: chooseMove(m, seat, "medium") }
  },
  xo: {
    seats: 2,
    create: () => createMatch3(),
    view: (m) => m,
    act: xoAct,
    forfeit: (m, seat) => forfeit3(m, seat),
    over: (m) => m.matchWinner !== null
  },
  tawla: {
    seats: 2,
    create: () => createMatch({ target: DEFAULT_MATCH_TARGET }),
    view: (m) => m,
    act: tawlaAct,
    forfeit: (m, seat) => forfeit(m, seat),
    over: (m) => m.matchWinner !== null
  },
  domino: {
    seats: 2,
    create: () => createMatch2({ players: 2, rand }),
    view: (m, seat) => viewFor(m, seat),
    act: dominoAct,
    forfeit: (m, seat) => forfeit2(m, seat),
    over: (m) => m.matchWinner !== null
  },
  // 4 players in two teams. Empty seats can be filled by the computer, and a player who
  // disconnects for good is replaced by the computer so the other three can finish.
  domino4: {
    seats: 4,
    create: () => createMatch2({ players: 4, rand }),
    view: (m, seat) => viewFor(m, seat),
    act: dominoAct,
    forfeit: (m, seat) => forfeit2(m, seat),
    over: (m) => m.matchWinner !== null,
    bots: true,
    turnSeat: (m) => m.phase === "play" ? m.round.turn : null,
    botMove: (m, seat) => {
      const mv = choosePlay(m, seat, "medium");
      return mv && { a: "play", id: mv.id, side: mv.side };
    }
  }
};
var gameOf = (name) => Object.hasOwn(GAMES, name) ? name : "tawla";

// server/music.js
var SEARCH_URL = "https://www.googleapis.com/youtube/v3/search";
var CACHE_TTL = 24 * 60 * 60 * 1e3;
var CACHE_MAX = 500;
var PER_IP_MAX = 12;
var PER_IP_WINDOW = 10 * 6e4;
var decode = (s) => String(s ?? "").replace(/&quot;/g, '"').replace(/&#39;/g, "'").replace(/&apos;/g, "'").replace(/&lt;/g, "<").replace(/&gt;/g, ">").replace(/&amp;/g, "&");
var pacificDay = (t) => new Date(t).toLocaleDateString("en-CA", { timeZone: "America/Los_Angeles" });
function normalizeQuery(q) {
  return String(q ?? "").replace(/[\u0000-\u001f<>]/g, " ").replace(/\s+/g, " ").trim().slice(0, 80);
}
function createMusicSearch({
  apiKey = process.env.YOUTUBE_API_KEY,
  fetchImpl = globalThis.fetch,
  dailyLimit = Number(process.env.MUSIC_DAILY_LIMIT || 95),
  now = Date.now
} = {}) {
  const cache = /* @__PURE__ */ new Map();
  const perIp = /* @__PURE__ */ new Map();
  let day = pacificDay(now()), used = 0;
  function json2(res, status, body) {
    res.writeHead(status, { "content-type": "application/json; charset=utf-8", "cache-control": "no-store" });
    res.end(JSON.stringify(body));
  }
  function allowIp(ip) {
    const t = now();
    const list = (perIp.get(ip) || []).filter((x) => t - x < PER_IP_WINDOW);
    if (list.length >= PER_IP_MAX) {
      perIp.set(ip, list);
      return false;
    }
    list.push(t);
    perIp.set(ip, list);
    if (perIp.size > 5e3) perIp.clear();
    return true;
  }
  function clean(items) {
    const out = [];
    for (const it of items || []) {
      const id = it?.id?.videoId;
      if (typeof id !== "string" || !/^[A-Za-z0-9_-]{11}$/.test(id)) continue;
      const sn = it.snippet || {};
      const thumb = sn.thumbnails?.medium?.url || sn.thumbnails?.default?.url || "";
      out.push({
        id,
        title: decode(sn.title).slice(0, 120),
        channel: decode(sn.channelTitle).slice(0, 60),
        thumb: /^https:\/\/i\.ytimg\.com\//.test(thumb) ? thumb : ""
      });
    }
    return out;
  }
  return async function handle2(req, res, ip) {
    if (!apiKey) return json2(res, 503, { error: "noKey" });
    const q = normalizeQuery(new URL(req.url, "http://x").searchParams.get("q"));
    if (q.length < 2) return json2(res, 400, { error: "short" });
    const key = q.toLowerCase();
    const hit = cache.get(key);
    if (hit && now() - hit.at < CACHE_TTL) return json2(res, 200, { items: hit.items, cached: true });
    if (!allowIp(ip)) return json2(res, 429, { error: "rate" });
    const today = pacificDay(now());
    if (today !== day) {
      day = today;
      used = 0;
    }
    if (used >= dailyLimit) return json2(res, 429, { error: "quota" });
    used += 1;
    const url = `${SEARCH_URL}?part=snippet&type=video&videoEmbeddable=true&maxResults=8&safeSearch=moderate&q=${encodeURIComponent(q)}&key=${encodeURIComponent(apiKey)}`;
    let r;
    try {
      r = await fetchImpl(url, { signal: AbortSignal.timeout(8e3) });
    } catch {
      return json2(res, 502, { error: "upstream" });
    }
    if (!r.ok) {
      let reason = "";
      try {
        reason = (await r.json())?.error?.errors?.[0]?.reason || "";
      } catch {
      }
      if (r.status === 403 && /quota/i.test(reason)) {
        used = dailyLimit;
        return json2(res, 429, { error: "quota" });
      }
      return json2(res, 502, { error: "upstream" });
    }
    let data;
    try {
      data = await r.json();
    } catch {
      return json2(res, 502, { error: "upstream" });
    }
    const items = clean(data.items);
    cache.set(key, { at: now(), items });
    if (cache.size > CACHE_MAX) cache.delete(cache.keys().next().value);
    return json2(res, 200, { items });
  };
}

// server/stats.js
import { timingSafeEqual, createHash } from "node:crypto";
var DAY_TTL = 400 * 24 * 3600;
var EVENT_TYPES = ["match_easy", "match_medium", "match_hard", "match_online", "match_domino_easy", "match_domino_medium", "match_domino_hard", "match_domino_online", "match_xo_easy", "match_xo_medium", "match_xo_hard", "match_xo_online", "match_ludo_easy", "match_ludo_medium", "match_ludo_hard", "match_ludo_online", "match_kunkan_easy", "match_kunkan_medium", "match_kunkan_hard", "match_kunkan_online", "match_snakes_local", "match_snakes_online", "match_uno_easy", "match_uno_medium", "match_uno_hard", "match_uno_online", "match_mheibes_easy", "match_mheibes_medium", "match_mheibes_hard", "match_mheibes_online", "music_search"];
var dayOf = (t = Date.now()) => new Date(t).toLocaleDateString("en-CA", { timeZone: "Asia/Baghdad" });
var daysBack = (n) => Array.from({ length: n }, (_, i) => dayOf(Date.now() - i * 864e5)).reverse();
function memoryStore() {
  const nums = /* @__PURE__ */ new Map(), sets = /* @__PURE__ */ new Map();
  return {
    kind: "memory",
    async run(cmds) {
      return cmds.map(([op, key, val]) => {
        if (op === "INCR") {
          nums.set(key, (nums.get(key) || 0) + 1);
          return nums.get(key);
        }
        if (op === "GET") return nums.get(key) ?? null;
        if (op === "PFADD") {
          if (!sets.has(key)) sets.set(key, /* @__PURE__ */ new Set());
          sets.get(key).add(val);
          return 1;
        }
        if (op === "PFCOUNT") return sets.get(key)?.size || 0;
        return null;
      });
    }
  };
}
function redisStore(url, token, fetchImpl = globalThis.fetch) {
  return {
    kind: "redis",
    async run(cmds) {
      const r = await fetchImpl(`${url.replace(/\/$/, "")}/pipeline`, {
        method: "POST",
        headers: { authorization: `Bearer ${token}`, "content-type": "application/json" },
        body: JSON.stringify(cmds),
        signal: AbortSignal.timeout(5e3)
      });
      if (!r.ok) throw new Error("redis " + r.status);
      const out = await r.json();
      return out.map((x) => x && "result" in x ? x.result : null);
    }
  };
}
function json(res, status, body) {
  res.writeHead(status, { "content-type": "application/json; charset=utf-8", "cache-control": "no-store" });
  res.end(JSON.stringify(body));
}
function readBody(req, limit = 1024) {
  return new Promise((resolve) => {
    let size = 0, data = "";
    req.on("data", (c) => {
      size += c.length;
      if (size > limit) {
        req.destroy();
        resolve(null);
      } else data += c;
    });
    req.on("end", () => {
      try {
        resolve(JSON.parse(data || "{}"));
      } catch {
        resolve(null);
      }
    });
    req.on("error", () => resolve(null));
  });
}
function sameSecret(a, b) {
  const ha = createHash("sha256").update(String(a)).digest();
  const hb = createHash("sha256").update(String(b)).digest();
  return timingSafeEqual(ha, hb);
}
function limiter(max, windowMs) {
  const hits = /* @__PURE__ */ new Map();
  return (key) => {
    const now = Date.now();
    const list = (hits.get(key) || []).filter((t) => now - t < windowMs);
    if (list.length >= max) {
      hits.set(key, list);
      return false;
    }
    list.push(now);
    hits.set(key, list);
    if (hits.size > 1e4) hits.clear();
    return true;
  };
}
function createStats({
  env = process.env,
  live = () => ({ online: 0, matches: 0 }),
  fetchImpl
} = {}) {
  const store = env.UPSTASH_REDIS_REST_URL && env.UPSTASH_REDIS_REST_TOKEN ? redisStore(env.UPSTASH_REDIS_REST_URL, env.UPSTASH_REDIS_REST_TOKEN, fetchImpl) : memoryStore();
  const adminKey = env.ADMIN_KEY || "";
  const startedAt = (/* @__PURE__ */ new Date()).toISOString();
  const hitLimit = limiter(30, 6e4);
  const loginLimit = limiter(10, 15 * 6e4);
  async function hit(req, res, ip) {
    if (!hitLimit(ip)) return json(res, 429, { error: "rate" });
    const body = await readBody(req);
    const vid = body?.vid;
    if (typeof vid !== "string" || !/^[a-z0-9]{12,40}$/.test(vid)) return json(res, 400, { error: "bad" });
    const d = dayOf();
    try {
      await store.run([
        ["INCR", "visits:total"],
        ["INCR", `visits:${d}`],
        ["EXPIRE", `visits:${d}`, DAY_TTL],
        ["PFADD", "uv:all", vid],
        ["PFADD", `uv:${d}`, vid],
        ["EXPIRE", `uv:${d}`, DAY_TTL]
      ]);
    } catch {
    }
    return json(res, 200, { ok: true });
  }
  async function event(req, res, ip) {
    if (!hitLimit(ip)) return json(res, 429, { error: "rate" });
    const body = await readBody(req);
    if (!EVENT_TYPES.includes(body?.type)) return json(res, 400, { error: "bad" });
    const d = dayOf();
    try {
      await store.run([["INCR", `ev:${body.type}`], ["INCR", `ev:${body.type}:${d}`], ["EXPIRE", `ev:${body.type}:${d}`, DAY_TTL]]);
    } catch {
    }
    return json(res, 200, { ok: true });
  }
  async function admin(req, res, ip) {
    if (!adminKey) return json(res, 503, { error: "noAdminKey" });
    if (!loginLimit(ip)) return json(res, 429, { error: "rate" });
    const given = req.headers["x-admin-key"] || "";
    if (!given || !sameSecret(given, adminKey)) return json(res, 401, { error: "wrongKey" });
    const days = daysBack(14);
    const cmds = [
      ["GET", "visits:total"],
      ["PFCOUNT", "uv:all"],
      ...days.flatMap((d) => [["GET", `visits:${d}`], ["PFCOUNT", `uv:${d}`]]),
      ...EVENT_TYPES.flatMap((t) => [["GET", `ev:${t}`], ["GET", `ev:${t}:${days[days.length - 1]}`]])
    ];
    let r;
    try {
      r = await store.run(cmds);
    } catch {
      return json(res, 502, { error: "storage" });
    }
    const n = (v) => Number(v) || 0;
    let i = 0;
    const total = { visits: n(r[i++]), visitors: n(r[i++]) };
    const daily = days.map((d) => ({ day: d, visits: n(r[i++]), visitors: n(r[i++]) }));
    const events = {};
    for (const t of EVENT_TYPES) events[t] = { total: n(r[i++]), today: n(r[i++]) };
    return json(res, 200, { storage: store.kind, since: startedAt, live: live(), total, today: daily[daily.length - 1], daily, events });
  }
  return {
    storageKind: store.kind,
    async route(req, res, ip) {
      const path = (req.url || "").split("?")[0];
      if (req.method === "POST" && path === "/api/hit") {
        await hit(req, res, ip);
        return true;
      }
      if (req.method === "POST" && path === "/api/event") {
        await event(req, res, ip);
        return true;
      }
      if (req.method === "GET" && path === "/api/admin/stats") {
        await admin(req, res, ip);
        return true;
      }
      return false;
    }
  };
}

// server/index.js
var __dirname = dirname(fileURLToPath(import.meta.url));
var DIST = join(__dirname, "..", "dist");
var SINGLE_HTML = "index.html";
var SCRIPT_HASH = "sha256-xUDMcGdKa7Xm83vOmoRXOXyuUMTShhhGx0xS0f7kIEs=";
var GA_ID = /^G-[A-Z0-9]{4,15}$/.test(process.env.GA_ID || "") ? process.env.GA_ID : "";
var GA_INLINE = GA_ID ? `window.dataLayer=window.dataLayer||[];function gtag(){dataLayer.push(arguments)}gtag('js',new Date());gtag('config','${GA_ID}');` : "";
var GA_HASH = GA_ID ? "sha256-" + createHash2("sha256").update(GA_INLINE).digest("base64") : "";
var pageCache = null;
var PORT = Number(process.env.PORT || 8787);
var GRACE_MS = Number(process.env.GRACE_MS || 6e4);
var ROOM_IDLE_MS = 30 * 6e4;
var BOT_DELAY_MS = Number(process.env.BOT_DELAY_MS || 900);
var MAX_MSG_BYTES = 2048;
var RATE_PER_SEC = Number(process.env.RATE_PER_SEC || 20);
var MAX_CONN_PER_IP = Number(process.env.MAX_CONN_PER_IP || 8);
var MAX_CONNECTIONS = Number(process.env.MAX_CONNECTIONS || 500);
var MAX_ROOMS = Number(process.env.MAX_ROOMS || 300);
var EXTRA_ORIGINS = (process.env.ALLOWED_ORIGINS || "").split(",").map((x) => x.trim()).filter(Boolean);
var CODE_ALPHABET = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789";
var players = /* @__PURE__ */ new Map();
var rooms = /* @__PURE__ */ new Map();
var queues = Object.fromEntries(Object.keys(GAMES).map((g) => [g, []]));
function newCode() {
  for (; ; ) {
    let c = "";
    for (let i = 0; i < 6; i++) c += CODE_ALPHABET[randomInt2(0, CODE_ALPHABET.length)];
    if (!rooms.has(c)) return c;
  }
}
function send(ws, msg) {
  if (ws && ws.readyState === 1) ws.send(JSON.stringify(msg));
}
function cleanName(s) {
  return String(s ?? "").replace(/[<>&"'`]/g, "").trim().slice(0, 20);
}
var AVATARS = /* @__PURE__ */ new Set(["\u{1F981}", "\u{1F334}", "\u{1F319}", "\u{1F40E}", "\u{1FAD6}", "\u{1F3FA}", "\u2B50", "\u{1F985}"]);
var cleanAvatar = (a) => AVATARS.has(a) ? a : "\u{1F981}";
var BOT = "BOT";
var EMPTY = "EMPTY";
var isHuman = (tok) => !!tok && tok !== BOT;
function publicPlayers(room) {
  return room.seats.map((tok) => {
    if (tok === BOT) return { name: null, avatar: "\u265C", connected: true, ai: true };
    const p = tok && players.get(tok);
    return p ? { name: p.name, avatar: p.avatar, connected: !!(p.ws && p.ws.readyState === 1) } : null;
  });
}
function broadcastState(room, anim = null) {
  room.lastActive = Date.now();
  room.seats.forEach((tok, seat) => {
    const p = isHuman(tok) && players.get(tok);
    if (p) send(p.ws, { t: "state", code: room.code, game: room.game, you: seat, players: publicPlayers(room), match: GAMES[room.game].view(room.match, seat), anim });
  });
  scheduleBots(room);
}
function broadcastLobby(room) {
  room.seats.forEach((tok, seat) => {
    const p = isHuman(tok) && players.get(tok);
    if (p) send(p.ws, { t: "room", code: room.code, game: room.game, you: seat, seats: publicPlayers(room), canFill: !!GAMES[room.game].bots, canStartPartial: !!GAMES[room.game].startPartial });
  });
}
function scheduleBots(room) {
  const g = GAMES[room.game];
  if (!g.bots || !room.match || room.botTimer || g.over(room.match)) return;
  const seat = g.turnSeat(room.match);
  if (seat === null || room.seats[seat] !== BOT) return;
  room.botTimer = setTimeout(() => {
    room.botTimer = null;
    if (!rooms.has(room.code) || !room.match || g.turnSeat(room.match) !== seat || room.seats[seat] !== BOT) return;
    const msg = g.botMove(room.match, seat);
    const res = msg && g.act(room.match, seat, msg);
    if (res?.ok) for (const anim of res.anims) broadcastState(room, anim);
  }, BOT_DELAY_MS);
}
function createRoom(isPrivate, game) {
  if (rooms.size >= MAX_ROOMS) return null;
  const code = newCode();
  const g = gameOf(game);
  const n = GAMES[g].seats;
  const room = { code, game: g, seats: Array(n).fill(null), match: null, disconnectTimers: Array(n).fill(null), botTimer: null, lastActive: Date.now(), private: isPrivate };
  rooms.set(code, room);
  return room;
}
function seatPlayer(room, token, seat) {
  room.seats[seat] = token;
  const p = players.get(token);
  p.roomCode = room.code;
  p.seat = seat;
}
function startIfFull(room) {
  if (room.seats.every(Boolean) && !room.match) {
    room.match = GAMES[room.game].create(room.seats.map((t) => t !== EMPTY));
    room.seats = room.seats.map((t) => t === EMPTY ? null : t);
    broadcastState(room, { kind: "start" });
  }
}
function leaveQueue(token) {
  for (const q of Object.values(queues)) {
    const i = q.indexOf(token);
    if (i >= 0) q.splice(i, 1);
  }
}
function closeRoom(room) {
  for (const tok of room.seats) {
    const p = tok && players.get(tok);
    if (p && p.roomCode === room.code) {
      p.roomCode = null;
      p.seat = null;
    }
  }
  room.disconnectTimers.forEach((id) => id && clearTimeout(id));
  clearTimeout(room.botTimer);
  rooms.delete(room.code);
}
function leaveRoom(token, { forfeit: forfeit9 = true } = {}) {
  const p = players.get(token);
  if (!p || !p.roomCode) return;
  const room = rooms.get(p.roomCode);
  p.roomCode = null;
  p.seat = null;
  if (!room) return;
  const seat = room.seats.indexOf(token);
  const g = GAMES[room.game];
  if (room.match && room.match.matchWinner === null && forfeit9 && seat >= 0) {
    if (g.bots && room.seats.some((t, i) => i !== seat && isHuman(t))) {
      room.seats[seat] = BOT;
      broadcastState(room, { kind: "botTakeover", player: seat });
    } else {
      g.forfeit(room.match, seat);
      broadcastState(room, { kind: "forfeit", loser: seat });
    }
  }
  if (seat >= 0 && room.seats[seat] === token) room.seats[seat] = null;
  if (!room.seats.some(isHuman)) closeRoom(room);
  else if (!room.match) broadcastLobby(room);
}
function act(token, msg) {
  const p = players.get(token);
  const room = p?.roomCode && rooms.get(p.roomCode);
  if (!room || !room.match) return { ok: false, error: "\u0644\u0627 \u062A\u0648\u062C\u062F \u0645\u0628\u0627\u0631\u0627\u0629" };
  const seat = room.seats.indexOf(token);
  const res = GAMES[room.game].act(room.match, seat, msg);
  if (!res.ok) return res;
  for (const anim of res.anims) broadcastState(room, anim);
  return res;
}
function onHello(ws, msg) {
  if (ws.token) return send(ws, { t: "error", code: "alreadyHello" });
  let p = typeof msg.token === "string" && msg.token.length <= 64 && players.get(msg.token);
  if (p) {
    if (p.ws && p.ws !== ws && p.ws.readyState === 1) p.ws.close(4e3, "replaced");
    p.ws = ws;
  } else {
    p = { token: randomUUID(), ws, roomCode: null, seat: null };
    players.set(p.token, p);
  }
  p.name = cleanName(msg.name);
  p.avatar = cleanAvatar(msg.avatar);
  ws.token = p.token;
  send(ws, { t: "welcome", token: p.token, room: p.roomCode || null });
  const room = p.roomCode && rooms.get(p.roomCode);
  if (room) {
    const seat = room.seats.indexOf(p.token);
    if (room.disconnectTimers[seat]) {
      clearTimeout(room.disconnectTimers[seat]);
      room.disconnectTimers[seat] = null;
    }
    if (room.match) broadcastState(room, { kind: "reconnect", player: seat });
    else broadcastLobby(room);
  }
}
function onClose(ws) {
  const token = ws.token;
  const p = token && players.get(token);
  if (!p || p.ws !== ws) return;
  leaveQueue(token);
  const room = p.roomCode && rooms.get(p.roomCode);
  if (!room) return;
  if (!room.match) {
    leaveRoom(token, { forfeit: false });
    return;
  }
  const seat = room.seats.indexOf(token);
  if (room.match.matchWinner !== null) {
    leaveRoom(token, { forfeit: false });
    return;
  }
  broadcastState(room, { kind: "disconnect", player: seat, graceMs: GRACE_MS });
  room.disconnectTimers[seat] = setTimeout(() => {
    room.disconnectTimers[seat] = null;
    if (rooms.has(room.code) && room.match && room.match.matchWinner === null) {
      const g = GAMES[room.game];
      if (g.bots && room.seats.some((t, i) => i !== seat && isHuman(t))) {
        const p2 = players.get(token);
        if (p2) {
          p2.roomCode = null;
          p2.seat = null;
        }
        room.seats[seat] = BOT;
        broadcastState(room, { kind: "botTakeover", player: seat, timeout: true });
      } else {
        g.forfeit(room.match, seat);
        broadcastState(room, { kind: "forfeit", loser: seat, timeout: true });
      }
    }
  }, GRACE_MS);
}
function handle(ws, msg) {
  if (msg.t === "hello") return onHello(ws, msg);
  const token = ws.token;
  if (!token || !players.has(token)) return send(ws, { t: "error", code: "noHello" });
  const p = players.get(token);
  switch (msg.t) {
    case "quick": {
      if (p.roomCode) leaveRoom(token);
      leaveQueue(token);
      const game = gameOf(msg.game);
      const queue = queues[game];
      const other2 = queue.shift();
      if (other2 && players.get(other2)?.ws?.readyState === 1) {
        const room = createRoom(false, game);
        if (!room) {
          queue.unshift(other2);
          return send(ws, { t: "error", code: "busy" });
        }
        const first = randomInt2(0, 2);
        seatPlayer(room, other2, first);
        seatPlayer(room, token, 1 - first);
        startIfFull(room);
      } else {
        queue.push(token);
        send(ws, { t: "queued" });
      }
      break;
    }
    case "create": {
      if (p.roomCode) leaveRoom(token);
      leaveQueue(token);
      const room = createRoom(true, msg.game);
      if (!room) return send(ws, { t: "error", code: "busy" });
      seatPlayer(room, token, 0);
      broadcastLobby(room);
      break;
    }
    case "join": {
      const code = String(msg.code || "").toUpperCase().replace(/[^A-Z0-9]/g, "").slice(0, 6);
      const room = rooms.get(code);
      if (!room) return send(ws, { t: "error", code: "notFound" });
      if (room.seats.includes(token)) {
        broadcastState(room);
        return;
      }
      const free = room.seats.indexOf(null);
      if (free < 0 || room.match) return send(ws, { t: "error", code: "full" });
      if (p.roomCode) leaveRoom(token);
      leaveQueue(token);
      seatPlayer(room, token, free);
      if (room.seats.every(Boolean)) startIfFull(room);
      else broadcastLobby(room);
      break;
    }
    case "fill": {
      const room = p.roomCode && rooms.get(p.roomCode);
      const g = room && GAMES[room.game];
      if (!room || room.match || !g.bots) return send(ws, { t: "error", code: "cantFill" });
      if (msg.bots === false) {
        if (!g.startPartial || room.seats.filter(Boolean).length < 2) return send(ws, { t: "error", code: "needTwo" });
        room.seats = room.seats.map((t) => t || EMPTY);
      } else room.seats = room.seats.map((t) => t || BOT);
      startIfFull(room);
      break;
    }
    case "cancel":
    case "leave": {
      leaveQueue(token);
      leaveRoom(token);
      send(ws, { t: "left" });
      break;
    }
    case "act": {
      const res = act(token, msg);
      if (!res.ok) send(ws, { t: "error", code: "illegal", msg: res.error });
      break;
    }
    case "ping":
      send(ws, { t: "pong" });
      break;
    default:
      send(ws, { t: "error", code: "unknown" });
  }
}
var MIME = { ".html": "text/html; charset=utf-8", ".js": "text/javascript", ".css": "text/css", ".svg": "image/svg+xml", ".png": "image/png", ".ico": "image/x-icon", ".json": "application/json", ".webmanifest": "application/manifest+json" };
function securityHeaders(req, res) {
  const host = String(req.headers.host || "").replace(/[^A-Za-z0-9.:\-\[\]]/g, "");
  res.setHeader("Content-Security-Policy", [
    "default-src 'self'",
    `script-src 'self'${SCRIPT_HASH ? ` '${SCRIPT_HASH}'` : ""}${GA_HASH ? ` '${GA_HASH}' https://www.googletagmanager.com` : ""} https://www.youtube.com https://s.ytimg.com`,
    "frame-src https://www.youtube.com https://www.youtube-nocookie.com",
    "style-src 'self' 'unsafe-inline' https://fonts.googleapis.com",
    "font-src 'self' https://fonts.gstatic.com",
    "img-src 'self' data: https://i.ytimg.com" + (GA_ID ? " https://*.google-analytics.com https://*.googletagmanager.com" : ""),
    `connect-src 'self' wss://${host} ws://${host}` + (GA_ID ? " https://*.google-analytics.com https://*.analytics.google.com https://*.googletagmanager.com" : ""),
    "frame-ancestors 'none'",
    "base-uri 'none'",
    "form-action 'self'",
    "object-src 'none'"
  ].join("; "));
  res.setHeader("X-Content-Type-Options", "nosniff");
  res.setHeader("X-Frame-Options", "DENY");
  res.setHeader("Referrer-Policy", "strict-origin-when-cross-origin");
  res.setHeader("Permissions-Policy", "camera=(), microphone=(), geolocation=()");
  if (req.headers["x-forwarded-proto"] === "https") res.setHeader("Strict-Transport-Security", "max-age=31536000");
}
var musicSearch = createMusicSearch();
var countClients = () => 0;
var stats = createStats({
  live: () => ({
    online: countClients(),
    matches: [...rooms.values()].filter((r) => r.match && r.match.matchWinner === null).length,
    waiting: Object.values(queues).reduce((n, q) => n + q.length, 0)
  })
});
var ipOf = (req) => String(req.headers["x-forwarded-for"] || "").split(",")[0].trim() || req.socket.remoteAddress || "?";
async function serveStatic(req, res) {
  securityHeaders(req, res);
  if (req.method === "GET" && (req.url || "").startsWith("/api/music/search")) return musicSearch(req, res, ipOf(req));
  if ((req.url || "").startsWith("/api/") && await stats.route(req, res, ipOf(req))) return;
  if (req.method !== "GET" && req.method !== "HEAD") {
    res.writeHead(405);
    return res.end();
  }
  if (req.url === "/healthz") {
    res.writeHead(200, { "content-type": "text/plain" });
    return res.end("ok");
  }
  if (SINGLE_HTML) {
    if (!pageCache) {
      let html = await readFile(join(__dirname, SINGLE_HTML), "utf8");
      if (GA_ID) html = html.replace("</head>", `<script async src="https://www.googletagmanager.com/gtag/js?id=${GA_ID}"></script><script>${GA_INLINE}</script>
</head>`);
      pageCache = Buffer.from(html);
    }
    const body = pageCache;
    res.writeHead(200, { "content-type": MIME[".html"], "cache-control": "no-cache" });
    return res.end(req.method === "HEAD" ? void 0 : body);
  }
  let path;
  try {
    path = decodeURIComponent((req.url || "/").split("?")[0]);
  } catch {
    res.writeHead(400);
    return res.end();
  }
  if (path.includes("\0")) {
    res.writeHead(400);
    return res.end();
  }
  if (path.endsWith("/")) path += "index.html";
  const file = normalize(join(DIST, path));
  if (file !== DIST && !file.startsWith(DIST + sep)) {
    res.writeHead(403);
    return res.end();
  }
  try {
    const s = await stat(file);
    if (!s.isFile()) throw new Error("not file");
    const body = await readFile(file);
    res.writeHead(200, { "content-type": MIME[extname(file)] || "application/octet-stream", "cache-control": path.includes("/assets/") ? "public, max-age=31536000, immutable" : "no-cache" });
    res.end(body);
  } catch {
    try {
      const body = await readFile(join(DIST, "index.html"));
      res.writeHead(200, { "content-type": MIME[".html"] });
      res.end(body);
    } catch {
      res.writeHead(404, { "content-type": "text/plain; charset=utf-8" });
      res.end("TAULA IRAQ server is running. Build the game first: npm run build");
    }
  }
}
function startServer(port = PORT) {
  const server = http.createServer((req, res) => {
    serveStatic(req, res).catch(() => {
      try {
        res.writeHead(500);
        res.end();
      } catch {
      }
    });
  });
  const perIp = /* @__PURE__ */ new Map();
  const clientIp = (req) => String(req.headers["x-forwarded-for"] || "").split(",")[0].trim() || req.socket.remoteAddress || "?";
  const wss = new WebSocketServer({
    server,
    path: "/ws",
    maxPayload: MAX_MSG_BYTES,
    verifyClient: ({ req }, done) => {
      const origin = req.headers.origin;
      if (origin) {
        let ok2 = EXTRA_ORIGINS.includes(origin);
        try {
          ok2 = ok2 || new URL(origin).host === req.headers.host;
        } catch {
          ok2 = false;
        }
        if (!ok2) return done(false, 403, "Origin not allowed");
      }
      if (wss.clients.size >= MAX_CONNECTIONS) return done(false, 503, "Server full");
      if ((perIp.get(clientIp(req)) || 0) >= MAX_CONN_PER_IP) return done(false, 429, "Too many connections");
      done(true);
    }
  });
  countClients = () => wss.clients.size;
  wss.on("connection", (ws, req) => {
    const ip = clientIp(req);
    perIp.set(ip, (perIp.get(ip) || 0) + 1);
    ws.on("close", () => {
      const n = (perIp.get(ip) || 1) - 1;
      if (n <= 0) perIp.delete(ip);
      else perIp.set(ip, n);
    });
    ws.isAlive = true;
    ws.bucket = { tokens: RATE_PER_SEC, at: Date.now() };
    ws.on("pong", () => {
      ws.isAlive = true;
    });
    ws.on("message", (raw) => {
      const now = Date.now();
      const b = ws.bucket;
      b.tokens = Math.min(RATE_PER_SEC, b.tokens + (now - b.at) / 1e3 * RATE_PER_SEC);
      b.at = now;
      if (b.tokens < 1) return send(ws, { t: "error", code: "rate" });
      b.tokens -= 1;
      let msg;
      try {
        msg = JSON.parse(raw.toString());
      } catch {
        return send(ws, { t: "error", code: "badJson" });
      }
      if (!msg || typeof msg !== "object" || typeof msg.t !== "string") return send(ws, { t: "error", code: "badMsg" });
      try {
        handle(ws, msg);
      } catch (err4) {
        console.error(err4);
        send(ws, { t: "error", code: "server" });
      }
    });
    ws.on("error", () => {
    });
    ws.on("close", () => onClose(ws));
  });
  const hb = setInterval(() => {
    for (const ws of wss.clients) {
      if (!ws.isAlive) {
        ws.terminate();
        continue;
      }
      ws.isAlive = false;
      try {
        ws.ping();
      } catch {
      }
    }
    const now = Date.now();
    for (const room of rooms.values()) if (now - room.lastActive > ROOM_IDLE_MS) closeRoom(room);
    for (const [tok, p] of players) if ((!p.ws || p.ws.readyState > 1) && !p.roomCode) players.delete(tok);
  }, 15e3);
  server.on("close", () => clearInterval(hb));
  return new Promise((resolve) => server.listen(port, () => {
    resolve({ server, wss });
  }));
}
if (process.argv[1] && fileURLToPath(import.meta.url) === process.argv[1]) {
  startServer().then(() => console.log(`TAULA IRAQ server on http://localhost:${PORT}  (WebSocket: /ws)`));
}
export {
  startServer
};

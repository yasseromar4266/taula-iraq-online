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
  const points = new Array(24).fill(0);
  points[23] = 2;
  points[12] = 5;
  points[7] = 3;
  points[5] = 5;
  points[0] = -2;
  points[11] = -5;
  points[16] = -3;
  points[18] = -5;
  return { points, bar: [0, 0], off: [0, 0] };
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
function applyMove(pos, player, move2) {
  const next = clonePosition(pos);
  if (move2.from === BAR) next.bar[player] -= 1;
  else addAt(next, player, move2.from, -1);
  if (move2.to === OFF) {
    next.off[player] += 1;
  } else {
    const opp = other(player);
    if (countAt(next, opp, move2.to) === 1) {
      addAt(next, opp, move2.to, -1);
      next.bar[opp] += 1;
    }
    addAt(next, player, move2.to, 1);
  }
  return next;
}
function isHit(pos, player, move2) {
  return move2.to !== OFF && countAt(pos, other(player), move2.to) === 1;
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
  const points = winnerSide === null ? 0 : sidePips[1 - winnerSide];
  if (winnerSide !== null) match.scores[winnerSide] += points;
  r.result = { winner: winnerSide, reason, points, outPlayer, sidePips, handPips: r.hands.map(handPips), hands: r.hands.map((h) => h.slice()) };
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
  const next = nextSeat2(match, me);
  const partner = partnerOf2(match, me);
  const nextMisses = new Set(r.missing[next] || []);
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
var GAMES = {
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
var EVENT_TYPES = ["match_easy", "match_medium", "match_hard", "match_online", "match_domino_easy", "match_domino_medium", "match_domino_hard", "match_domino_online", "music_search"];
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
var SCRIPT_HASH = "sha256-TD6Nkarer+CS5B9NSlV2ProLyNwX7FYTkv6jtFuHnvE=";
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
    if (p) send(p.ws, { t: "room", code: room.code, game: room.game, you: seat, seats: publicPlayers(room), canFill: !!GAMES[room.game].bots });
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
    room.match = GAMES[room.game].create();
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
function leaveRoom(token, { forfeit: forfeit3 = true } = {}) {
  const p = players.get(token);
  if (!p || !p.roomCode) return;
  const room = rooms.get(p.roomCode);
  p.roomCode = null;
  p.seat = null;
  if (!room) return;
  const seat = room.seats.indexOf(token);
  const g = GAMES[room.game];
  if (room.match && room.match.matchWinner === null && forfeit3 && seat >= 0) {
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
      if (!room || room.match || !GAMES[room.game].bots) return send(ws, { t: "error", code: "cantFill" });
      room.seats = room.seats.map((t) => t || BOT);
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
      } catch (err) {
        console.error(err);
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

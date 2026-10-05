// Headless test of Twenty-nine. No browser, no network.
//   node scripts/test-engine.mjs
//
// Sections run in build order, one block per checkpoint:
//
//   1. The pure card layer — the pack, the J-9-A-10 ranking, the 28 points,
//      ANTICLOCKWISE turn order, partnerships, follow-suit, the caller's
//      obligation to trump, and the trick winner before, at and after the
//      reveal.
//   2. Scoring — card points, the deal result, game points under pair,
//      double, redouble and single hand, and the ±6 finish.
//   3. The rules — the four toggles, the presets, the bid range.
//   4. The engine — whole deals and matches, with the concealed trump audited
//      at every state the engine passes through.
//   5. The wire — guards and the one dispatcher.
//   6. The bot — all seats botted under all sixteen toggle combinations, and
//      blind to a trump it is not entitled to know.
//
// Three rules get more attention than everything else, because each produces
// a game that still runs, still finishes, and is quietly wrong:
//
//   * THE TURN DIRECTION. judgement — the repo this one is modelled on — runs
//     CLOCKWISE. A copied helper is wrong in every trick.
//   * THE RANKING. Ace-high comparators sit in two siblings. J-9-A-10 is not
//     ace-high, and copying either scores every jack wrong.
//   * THE CONCEALED TRUMP. A suit only one player knows, which must not leak
//     through the state, the log, the legal set, the sort order or a bot.
//
// Where a rule can be stated as a property it is tested as one rather than as
// a table of expected numbers — a table only ever proves the numbers have not
// changed, which is not the same as proving the rule still holds. The pack's
// twenty-eight points in particular are never typed here: they are summed
// from the point table, which is the brief's instruction and the only way the
// test could disagree with a changed table.

import {
  SUITS, RANKS, PACK_SIZE, PACK_POINTS, POINTS, BATCH, BATCHES, HAND_SIZE, SEATS,
  rankOf, suitOf, rankValue, cardPoints, pointsIn, scores, cardName, cardLabel,
  suitName, suitGlyph, rankLabel, isRedSuit, isRedCard,
  buildPack, shuffle, dealBatch, sortHand, suitCounts,
} from '../js/cards.js';
import {
  CLOCKWISE, ANTICLOCKWISE, TABLE_DIRECTION,
  stepSeat, nextSeat, prevSeat, seatsFrom, nextActiveSeat,
  teamOf, partnerOf, sameTeam, seatsOfTeam,
  ledSuitOf, canCall, legalPlays, canPlay, illegalReason,
  playsAsTrump, winningPlay, trickWinner, wouldWin,
} from '../js/trick.js';
import {
  trickPoints, pointsBySide, PAIR_SHIFT, pairAdjust,
  DEAL_STAKE, SINGLE_HAND_STAKE, DOUBLE_LEVELS, multiplierFor,
  dealResult, singleHandResult, applyDelta, MATCH_TARGET, matchOutcome, leadingTeam,
} from '../js/scoring.js';
import {
  MIN_BID, MAX_BID, BID_STEP, legalBids, bidIsLegal, illegalBidReason,
  TOGGLES, DEFAULT_CONFIG, normalizeConfig, allConfigs,
  PRESETS, presetMatching, presetConfig, TOGGLE_LABELS, toggleLabel,
  MAX_NAME_LEN, cleanName,
} from '../js/rules.js';
import {
  GameEngine, PHASES, FIRST_FOUR_MS, LAST_FOUR_MS, TRICK_PAUSE_MS,
} from '../js/state.js';
import {
  MAX_TYPE_LEN, MAX_RAW_NAME_LEN, MAX_PATCH_KEYS, MAX_FRAME_BYTES,
  TokenBucket, validEnvelope, validClientId, validPlayerId, validCardCode,
  validSeat, validBid, validName, validConfigPatch,
  validPublicState, validPrivateState, decodePeerFrame,
} from '../js/guards.js';
import {
  PLAYER_INTENTS, OWNER_INTENTS, GAME_INTENTS, SELF_GUARDED, LOCAL_ONLY, TOGGLE_INTENTS,
  applyGameIntent,
} from '../js/intents.js';
import {
  SERVER_URL, SERVER_HEALTH, SERVER_TIMEOUT_MS, SERVER_RETRIES, serverConfigured,
} from '../js/config.js';
import {
  BOT_THINK_MS, OFFLINE_GRACE_MS, PARTNER_OVERBID_MARGIN, CALL_FOR_POINTS, BID_CAUTION,
  chooseBid, chooseTrump, chooseCall, chooseCard, chooseDeclare, chooseIntent,
  createBotDriver, botStats, estimateSide, bestTrump, trumpStrength, cannotLose,
} from '../js/bot.js';

let passed = 0, failed = 0;
function ok(cond, msg) {
  if (cond) { passed++; }
  else { failed++; console.error('  ✗ FAIL:', msg); }
}
function eq(actual, expected, msg) {
  ok(actual === expected, `${msg} — expected ${JSON.stringify(expected)}, got ${JSON.stringify(actual)}`);
}
function same(actual, expected, msg) {
  ok(JSON.stringify(actual) === JSON.stringify(expected),
    `${msg} — expected ${JSON.stringify(expected)}, got ${JSON.stringify(actual)}`);
}
function throws(fn, msg) {
  try { fn(); } catch (_) { passed++; return; }
  failed++; console.error('  ✗ FAIL:', msg, '— expected a throw, got none');
}
let SECTION_AT = Date.now();
function section(t) { const now = Date.now(); if (process.env.TIMING) console.log(`  (${now - SECTION_AT}ms)`); SECTION_AT = now; console.log('\n— ' + t); }

// ---------------------------------------------------------------------------
// Deterministic RNG.
//
// cards.js shuffles through crypto.getRandomValues, so an unseeded run deals a
// different game every time and a failure cannot be reproduced. cards.js reads
// `crypto` at call time, so replacing the global here — before anything is
// dealt — is enough. seed(n) restarts the stream.
// ---------------------------------------------------------------------------
let prng = 0;
function seed(n) { prng = n >>> 0; }
function rand32() {
  prng = (prng + 0x6D2B79F5) >>> 0;
  let t = prng;
  t = Math.imul(t ^ (t >>> 15), t | 1);
  t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
  return (t ^ (t >>> 14)) >>> 0;
}
Object.defineProperty(globalThis, 'crypto', {
  configurable: true,
  value: {
    getRandomValues(buf) {
      for (let i = 0; i < buf.length; i++) buf[i] = rand32();
      return buf;
    },
  },
});
seed(1);
const randInt = (n) => rand32() % n;

/** A random hand of `n` distinct cards, for the property sweeps. */
function randomHand(n, exclude = []) {
  const pool = shuffle(buildPack().filter((c) => !exclude.includes(c)));
  return pool.slice(0, n);
}

// ###########################################################################
//
//  CHECKPOINT 1 — THE CARD LAYER
//
// ###########################################################################

// ===========================================================================
section('The pack');
// ===========================================================================
{
  const pack = buildPack();
  eq(pack.length, PACK_SIZE, 'buildPack() deals the whole pack');
  eq(new Set(pack).size, pack.length, 'every card in it is distinct');
  eq(PACK_SIZE, SUITS.length * RANKS.length, 'the pack is every rank of every suit');
  eq(RANKS.length * SUITS.length, BATCH * BATCHES * SEATS, 'and deals exactly into four hands of two batches');
  eq(HAND_SIZE, BATCH * BATCHES, 'a hand is two batches of four');
  // The eight ranks the brief names and no others: J 9 A 10 K Q 8 7.
  same([...RANKS].sort(), ['7', '8', '9', 'A', 'J', 'K', 'Q', 'T'], 'the ranks are J 9 A 10 K Q 8 7 and nothing lower');
  for (const code of pack) {
    ok(RANKS.includes(rankOf(code)) && SUITS.includes(suitOf(code)), `${code} is a rank then a suit`);
  }
  // A fresh array every call, so a caller that shuffles cannot disturb
  // anybody else's pack.
  ok(buildPack() !== buildPack(), 'buildPack() returns a new array each time');
}

// ===========================================================================
section('The ranking is J 9 A 10 K Q 8 7 — NOT ace-high');
// ===========================================================================
{
  // THE RULE, written once as the brief writes it. This string is the spec,
  // not an expected output: everything below is asserted against it pairwise.
  const SPEC = ['J', '9', 'A', 'T', 'K', 'Q', '8', '7'];
  for (const suit of SUITS) {
    for (let i = 0; i < SPEC.length; i++) {
      for (let j = 0; j < SPEC.length; j++) {
        const a = SPEC[i] + suit, b = SPEC[j] + suit;
        ok((rankValue(a) > rankValue(b)) === (i < j),
          `${a} ${i < j ? 'outranks' : 'does not outrank'} ${b}`);
      }
    }
  }
  // The two comparisons an ace-high comparator gets wrong, named so that the
  // failure reads as the bug it is.
  ok(rankValue('JS') > rankValue('AS'), 'the jack beats the ace');
  ok(rankValue('9S') > rankValue('AS'), 'the nine beats the ace');
  ok(rankValue('TS') > rankValue('KS'), 'the ten beats the king');
  ok(rankValue('9S') > rankValue('TS'), 'the nine beats the ten');
  // And through the trick winner, which is where a wrong comparator does its
  // damage: four cards of one suit, every permutation of who played what.
  const four = ['AH', 'JH', 'KH', '9H'];
  let perms = 0;
  const permute = (arr, k = 0) => {
    if (k === arr.length) {
      perms++;
      const plays = arr.map((code, seat) => ({ seat, code, trump: false }));
      eq(winningPlay(plays).code, 'JH', `the jack takes ${arr.join(' ')}`);
      return;
    }
    for (let i = k; i < arr.length; i++) {
      [arr[k], arr[i]] = [arr[i], arr[k]];
      permute(arr, k + 1);
      [arr[k], arr[i]] = [arr[i], arr[k]];
    }
  };
  permute(four.slice());
  eq(perms, 24, 'every order of play was tried');
  eq(rankValue('XS'), 0, 'an unknown rank has no strength rather than a borrowed one');
  eq(rankValue('toString'.slice(0, 2)), 0, 'and a prototype key is a miss, not a function');
}

// ===========================================================================
section('Card points — derived, never typed');
// ===========================================================================
{
  // The 28 is computed from the table and compared with the constant, both
  // ways round. Neither side of this comparison is a literal.
  let derived = 0;
  for (const suit of SUITS) for (const rank of RANKS) derived += POINTS[rank];
  eq(PACK_POINTS, derived, `the pack holds ${derived} card points, summed from the table`);
  eq(pointsIn(buildPack()), PACK_POINTS, 'pointsIn() over the pack agrees');

  // Seven a suit, which is the same number in every suit.
  const perSuit = SUITS.map((s) => pointsIn(buildPack().filter((c) => suitOf(c) === s)));
  ok(perSuit.every((p) => p === perSuit[0]), `every suit is worth the same (${perSuit[0]})`);
  eq(perSuit[0] * SUITS.length, PACK_POINTS, 'and the suits add up to the pack');

  // The brief's table, rank by rank. These four numbers are the rule itself.
  same([POINTS.J, POINTS[9], POINTS.A, POINTS.T], [3, 2, 1, 1], 'J 3, 9 2, A 1, 10 1');
  same([POINTS.K, POINTS.Q, POINTS[8], POINTS[7]], [0, 0, 0, 0], 'K Q 8 7 are worth nothing');
  for (const code of buildPack()) eq(cardPoints(code), POINTS[rankOf(code)], `cardPoints(${code}) reads the table`);

  // STRENGTH AND POINTS AGREE ON THE ORDER OF THE SCORING RANKS, and that is
  // a property worth pinning because it is what makes "feed your partner a
  // jack" and "the jack wins" the same jack.
  const scoring = RANKS.filter((r) => POINTS[r] > 0);
  same(scoring, RANKS.slice(0, scoring.length), 'the ranks that score are exactly the strongest ranks');
  for (const code of buildPack()) eq(scores(code), cardPoints(code) > 0, `scores(${code})`);

  // Any partition of the pack between two sides sums to the pack — the
  // conservation law every deal's scoring rests on.
  for (let i = 0; i < 50; i++) {
    const pack = shuffle(buildPack());
    const cut = randInt(pack.length + 1);
    eq(pointsIn(pack.slice(0, cut)) + pointsIn(pack.slice(cut)), PACK_POINTS, `a split at ${cut} conserves the points`);
  }
}

// ===========================================================================
section('Names, for the screen and the screen reader');
// ===========================================================================
{
  eq(cardName('JS'), 'Jack of spades', 'cardName');
  eq(cardName('TH'), '10 of hearts', 'the ten is spoken as a number');
  eq(cardLabel('JS'), 'Jack of spades, 3 points', 'the brief\'s own aria-label example');
  eq(cardLabel('AD'), 'Ace of diamonds, 1 point', 'one point is singular');
  eq(cardLabel('7C'), '7 of clubs, no points', 'a pointless card says so in words');
  eq(rankLabel('TS'), '10', 'the ten displays as 10');
  for (const s of SUITS) {
    ok(suitName(s).length > 3 && suitGlyph(s).length === 1, `suit ${s} has a name and a glyph`);
  }
  same(SUITS.map(isRedSuit), [false, true, false, true], 'the display order alternates black and red');
  ok(isRedCard('9D') && !isRedCard('9S'), 'isRedCard');
  eq(suitName('toString'), '', 'a prototype key names nothing');
}

// ===========================================================================
section('ANTICLOCKWISE turn order — judgement is clockwise, this is not');
// ===========================================================================
{
  eq(TABLE_DIRECTION, ANTICLOCKWISE, 'Twenty-nine plays anticlockwise');
  ok(CLOCKWISE !== ANTICLOCKWISE, 'the two directions are different constants');
  throws(() => stepSeat(0), 'stepSeat() refuses to guess a direction');
  throws(() => stepSeat(0, 2), 'and refuses a direction that is not one of the two');

  // Seats ascend clockwise, so the player on your RIGHT — next in an
  // anticlockwise game — is one seat lower.
  for (let s = 0; s < SEATS; s++) {
    eq(nextSeat(s), (s - 1 + SEATS) % SEATS, `the seat after ${s} is ${(s - 1 + SEATS) % SEATS}`);
    eq(prevSeat(nextSeat(s)), s, `prevSeat undoes nextSeat from ${s}`);
    ok(stepSeat(s, CLOCKWISE) !== stepSeat(s, ANTICLOCKWISE), `the two directions disagree at seat ${s}`);
    eq(stepSeat(s, ANTICLOCKWISE), nextSeat(s), 'and nextSeat is the anticlockwise one');
  }
  same(seatsFrom(0), [0, 3, 2, 1], 'from seat 0 the order is 0, 3, 2, 1');
  same(seatsFrom(2), [2, 1, 0, 3], 'from seat 2 the order is 2, 1, 0, 3');
  for (let s = 0; s < SEATS; s++) {
    eq(new Set(seatsFrom(s)).size, SEATS, `a full turn from ${s} visits every seat once`);
    eq(seatsFrom(s)[0], s, 'starting where it was asked to');
  }
  // TURN ORDER ALTERNATES PARTNERSHIPS. Every adjacent pair in play order is a
  // pair of opponents — which is the whole point of sitting partners opposite.
  for (let s = 0; s < SEATS; s++) {
    ok(!sameTeam(s, nextSeat(s)), `seat ${s} and the next to play are opponents`);
  }
}

// ===========================================================================
section('Partnerships, and the seat that sits out');
// ===========================================================================
{
  same([0, 1, 2, 3].map(teamOf), [0, 1, 0, 1], 'seats 0 and 2 against 1 and 3');
  for (let s = 0; s < SEATS; s++) {
    eq(partnerOf(s), (s + 2) % SEATS, `seat ${s}'s partner sits opposite`);
    ok(sameTeam(s, partnerOf(s)), 'and is on the same team');
    eq(partnerOf(partnerOf(s)), s, 'partnership is symmetric');
  }
  same(seatsOfTeam(0), [0, 2], 'team 0');
  same(seatsOfTeam(1), [1, 3], 'team 1');

  // Single hand: the declarer's partner is skipped in turn order.
  for (let declarer = 0; declarer < SEATS; declarer++) {
    const out = partnerOf(declarer);
    for (let start = 0; start < SEATS; start++) {
      if (start === out) continue;
      const order = seatsFrom(start, out);
      eq(order.length, SEATS - 1, `with ${out} sitting out, a turn from ${start} has three seats`);
      ok(!order.includes(out), 'and the sitting-out seat is not among them');
      same(order, seatsFrom(start).filter((s) => s !== out), 'in the same anticlockwise order otherwise');
    }
    for (let s = 0; s < SEATS; s++) {
      ok(nextActiveSeat(s, out) !== out, `nextActiveSeat never lands on the sitting-out seat ${out}`);
    }
  }
  eq(nextActiveSeat(1, 0), 3, 'the seat after 1, skipping 0, is 3');
}

// ===========================================================================
section('dealBatch — the order is an argument, never a guess');
// ===========================================================================
{
  const pack = buildPack();
  throws(() => dealBatch(pack), 'dealBatch() refuses to deal without a seat order');
  throws(() => dealBatch(pack.slice(0, 15), [0, 1, 2, 3]), 'and refuses to deal a short batch');
  const order = seatsFrom(nextSeat(0));
  const { hands, stock } = dealBatch(pack, order);
  same(hands[order[0]], pack.slice(0, BATCH), 'the first seat in the order gets the top four, in a block');
  same(hands[order[1]], pack.slice(BATCH, 2 * BATCH), 'the second seat the next four');
  eq(stock.length, PACK_SIZE - SEATS * BATCH, 'four batches of four leave the second half of the pack');
  eq(pack.length, PACK_SIZE, 'and the pack it was handed is untouched');
  const again = dealBatch(stock, order);
  eq(again.stock.length, 0, 'the second batch deals the rest of the pack');
  const all = new Set();
  for (const s of order) for (const c of hands[s].concat(again.hands[s])) all.add(c);
  eq(all.size, PACK_SIZE, 'two batches deal every card exactly once');
}

// ===========================================================================
section('sortHand — trump first only for a seat entitled to know it');
// ===========================================================================
{
  const hand = ['7S', 'JH', 'AS', '9C', 'KD', 'JS', 'TH', '8D'];
  same(sortHand(hand), ['JS', 'AS', '7S', 'JH', 'TH', '9C', 'KD', '8D'],
    'grouped S H C D, strongest first by J-9-A-10');
  same(sortHand(hand, 'D').slice(0, 2), ['KD', '8D'], 'a known trump is pulled to the front');
  ok(sortHand(hand) !== hand, 'a new array, never the caller\'s hand');
  same(suitCounts(hand), { S: 3, H: 2, D: 2, C: 1 }, 'suitCounts');
}

// ===========================================================================
section('Follow-suit, and the void player\'s choice');
// ===========================================================================
{
  const suitsIn = (h) => new Set(h.map(suitOf));
  let leads = 0, follows = 0, voids = 0;
  for (let i = 0; i < 400; i++) {
    const n = 1 + randInt(HAND_SIZE);
    const hand = randomHand(n);
    const led = SUITS[randInt(SUITS.length)];

    // Leading: anything.
    same(legalPlays(hand, null), hand, 'a leader may play any card');
    ok(!canCall(hand, null, false), 'and a leader can never call for trump');
    leads++;

    const holding = hand.filter((c) => suitOf(c) === led);
    if (holding.length) {
      follows++;
      same(legalPlays(hand, led), holding, 'holding the led suit, only the led suit is legal');
      ok(!canCall(hand, led, false), 'and a player who can follow cannot call');
      for (const c of hand) {
        eq(canPlay(hand, c, led), suitOf(c) === led, `canPlay ${c} on a ${led} lead`);
        if (suitOf(c) !== led) eq(illegalReason(hand, c, led), `must follow ${suitName(led)}`, 'and says why');
      }
    } else {
      voids++;
      same(legalPlays(hand, led), hand, 'VOID AND NOT CALLING: any card, whatever its suit');
      ok(canCall(hand, led, false), 'a void player may call for trump before the reveal');
      ok(!canCall(hand, led, true), 'and may not once trump is face up');
    }
  }
  ok(leads > 100 && follows > 50 && voids > 50, `swept ${leads} leads, ${follows} follows, ${voids} voids`);
  ok(!canPlay(['JS'], 'JH', null), 'a card not in the hand is never legal');
  eq(illegalReason(['JS'], 'JH', null), 'not in your hand', 'and says so');
}

// ===========================================================================
section('The caller\'s obligation to trump — one player, one trick, only if able');
// ===========================================================================
{
  let bit = 0, free = 0, followFirst = 0;
  for (let i = 0; i < 600; i++) {
    const hand = randomHand(1 + randInt(HAND_SIZE));
    const led = SUITS[randInt(SUITS.length)];
    const trump = SUITS[randInt(SUITS.length)];
    const holdsLed = hand.some((c) => suitOf(c) === led);
    const trumps = hand.filter((c) => suitOf(c) === trump);
    const legal = legalPlays(hand, led, trump);
    if (holdsLed) {
      // Follow-suit bites first, even for a caller. Only the bidder can be
      // here — their indicator comes back into their hand at the reveal.
      followFirst++;
      same(legal, hand.filter((c) => suitOf(c) === led), 'a caller who holds the led suit still follows it');
    } else if (trumps.length) {
      bit++;
      same(legal, trumps, 'a caller holding a trump must play a trump');
      for (const c of hand) {
        if (suitOf(c) !== trump) {
          ok(/called for trump/.test(illegalReason(hand, c, led, trump)), 'and a non-trump says why');
        }
      }
    } else {
      free++;
      same(legal, hand, 'a caller with no trump may play anything');
    }
    // THE SCOPE. Without the obligation — everybody who did not call, and the
    // caller on any later trick — a void player is free.
    if (!holdsLed) same(legalPlays(hand, led, null), hand, 'without the obligation the same void hand is free');
  }
  ok(bit > 50 && free > 50 && followFirst > 50,
    `the obligation bit ${bit} times, was moot ${free} times, deferred to follow-suit ${followFirst} times`);
}

// ===========================================================================
section('The trick winner — before, at and after the reveal');
// ===========================================================================
{
  const P = (seat, code, trump = false) => ({ seat, code, trump });

  // BEFORE: a trump-suit card is a plain card. Hearts are trumps, nobody has
  // called, and the jack of hearts played on a spade lead is a discard.
  eq(trickWinner([P(0, '7S'), P(3, 'JH'), P(2, 'KS'), P(1, '8S')]), 2,
    'before the reveal, the highest spade wins and an off-suit jack of the trump suit is a discard');

  // AT: seat 3 calls on the second card. Seat 0's earlier jack of hearts was
  // played before the reveal and stays plain; seat 3's seven of hearts plays
  // as a trump and takes it.
  eq(trickWinner([P(0, '9S'), P(3, '7H', true), P(2, 'JS'), P(1, 'AH', true)]), 1,
    'at the reveal, the highest card played AS A TRUMP wins');
  eq(trickWinner([P(0, 'JH'), P(3, '7H', true)]), 3,
    'a plain lead of the trump suit is beaten by any trump played after the reveal, as the rule says');
  eq(trickWinner([P(0, '9C'), P(3, 'JH', false), P(2, '7H', true), P(1, 'AC')]), 2,
    'an earlier trump-suit card stays plain even after a later card trumps');

  // AFTER: ordinary trump play.
  eq(trickWinner([P(0, 'KD'), P(3, '8C', true), P(2, 'JD'), P(1, 'QC', true)]), 1,
    'after the reveal, the highest trump wins');
  eq(trickWinner([P(0, 'KD'), P(3, 'JD'), P(2, 'AS'), P(1, '9D')]), 3,
    'with no trump played, the highest of the led suit wins');
  eq(trickWinner([]), null, 'an empty trick has no winner');

  // A three-card trick under single hand resolves the same way.
  eq(trickWinner([P(0, 'AS'), P(3, 'JS'), P(1, '9S')]), 3, 'three-card tricks resolve the same way');

  // playsAsTrump is decided at play time and never consults the suit before
  // the reveal.
  ok(!playsAsTrump('JH', false, 'H'), 'before the reveal no card plays as a trump');
  ok(playsAsTrump('JH', true, 'H'), 'after it, a card of the trump suit does');
  ok(!playsAsTrump('JS', true, 'H'), 'and a card of another suit does not');
  ok(!playsAsTrump('JH', true, null), 'with no trump at all, nothing does');

  // THE PROPERTY, over random tricks with random reveal points.
  let checked = 0, trumped = 0;
  for (let i = 0; i < 2000; i++) {
    const size = 3 + randInt(2);
    const cards = randomHand(size);
    const trump = SUITS[randInt(SUITS.length)];
    const revealAt = randInt(size + 1);   // the card index the reveal happens at; size = never
    const plays = cards.map((code, k) => ({ seat: k, code, trump: playsAsTrump(code, k >= revealAt, trump) }));
    const w = winningPlay(plays);
    const led = suitOf(plays[0].code);
    ok(plays.includes(w), 'the winner is one of the plays');
    const tp = plays.filter((p) => p.trump);
    if (tp.length) {
      trumped++;
      ok(w.trump, 'if anything played as a trump, a trump won');
      ok(tp.every((p) => rankValue(p.code) <= rankValue(w.code)), 'and it was the highest of them');
    } else {
      eq(suitOf(w.code), led, 'with no trump played, the winner followed the led suit');
      ok(plays.filter((p) => suitOf(p.code) === led).every((p) => rankValue(p.code) <= rankValue(w.code)),
        'and was the highest of it');
    }
    // Plays before the reveal never count as trumps, whatever their suit.
    ok(plays.slice(0, Math.min(revealAt, size)).every((p) => !p.trump), 'nothing before the reveal played as a trump');
    checked++;
  }
  ok(checked === 2000 && trumped > 300, `${checked} random tricks, ${trumped} of them trumped`);

  // wouldWin agrees with trickWinner by construction.
  ok(wouldWin([P(0, 'KS')], 3, 'JS'), 'wouldWin: the jack over the king');
  ok(!wouldWin([P(0, 'KS')], 3, 'JH'), 'a plain off-suit card cannot win');
  ok(wouldWin([P(0, 'KS')], 3, '7H', true), 'a card played as a trump does');
  eq(ledSuitOf([P(2, '7H')]), 'H', 'the led suit is the first card\'s suit, trump or not');
}

// ###########################################################################
//
//  CHECKPOINT 2 — SCORING
//
// ###########################################################################

// ===========================================================================
section('Card points: tricks are worth what is in them, nothing more');
// ===========================================================================
{
  // A random deal played out by random legal-ish cards: every trick a set of
  // four cards, every winner a seat. The point is the conservation law, so
  // the play itself only needs to be a partition of the pack.
  for (let d = 0; d < 300; d++) {
    const pack = shuffle(buildPack());
    const tricks = [];
    for (let t = 0; t < HAND_SIZE; t++) {
      const plays = pack.slice(t * SEATS, t * SEATS + SEATS).map((code, k) => ({ seat: k, code, trump: false }));
      tricks.push({ plays, winner: randInt(SEATS) });
    }
    const sides = pointsBySide(tricks);
    eq(sides[0] + sides[1], PACK_POINTS, 'over a whole deal the two sides\' card points sum to the pack');
    // Each side is exactly the points in the tricks its two seats took.
    for (const team of [0, 1]) {
      const mine = tricks.filter((t) => teamOf(t.winner) === team);
      eq(sides[team], mine.reduce((n, t) => n + trickPoints(t.plays), 0),
        'a side scores the points in tricks won by EITHER partner');
    }
    // TRICKS ARE NOT POINTS: the number of tricks a side took says nothing on
    // its own. Count deals where the side with more tricks had fewer points.
  }
  // The brief's whole point about tricks, made concrete and reversible: six
  // tricks of nothing against two tricks with both red jacks in them.
  const nothing = (seat) => ({ plays: ['7S', '8S', 'KS', 'QS'].map((code, k) => ({ seat: k, code })), winner: seat });
  const jacks = (seat) => ({ plays: ['JH', 'JD', '7C', '8C'].map((code, k) => ({ seat: k, code })), winner: seat });
  const six = Array.from({ length: 6 }, () => nothing(0));
  const sides = pointsBySide([...six, jacks(1), jacks(3)]);
  ok(sides[1] > sides[0], `two tricks with jacks (${sides[1]}) beat six tricks of nothing (${sides[0]})`);
  eq(trickPoints([]), 0, 'an empty trick is worth nothing');
  same(pointsBySide([]), [0, 0], 'no tricks, no points');
}

// ===========================================================================
section('The deal result: made at the bid or better, ±1 doubled and redoubled');
// ===========================================================================
{
  same(DOUBLE_LEVELS.map(multiplierFor), [1, 2, 4], 'undoubled ×1, doubled ×2, redoubled ×4');
  for (const level of DOUBLE_LEVELS) eq(multiplierFor(level), 2 ** level, `level ${level} is 2^${level}`);
  eq(multiplierFor(7), 1, 'a level that does not exist multiplies by nothing');

  let made = 0, missed = 0;
  for (let finalBid = MIN_BID; finalBid <= MAX_BID; finalBid++) {
    for (let bidPoints = 0; bidPoints <= PACK_POINTS; bidPoints++) {
      for (const level of DOUBLE_LEVELS) {
        const r = dealResult({ finalBid, bidPoints, level });
        eq(r.made, bidPoints >= finalBid, `bid ${finalBid}, ${bidPoints} points: made iff at least the bid`);
        eq(Math.abs(r.delta), DEAL_STAKE * multiplierFor(level), 'the stake is one game point times the multiplier');
        eq(Math.sign(r.delta), r.made ? 1 : -1, 'plus for made, minus for missed');
        eq(r.multiplier, multiplierFor(level), 'and the multiplier is reported for the deal-over screen');
        if (r.made) made++; else missed++;
      }
    }
  }
  ok(made > 100 && missed > 100, `swept every bid against every point total: ${made} made, ${missed} missed`);
  // Exactly the bid is enough.
  ok(dealResult({ finalBid: MIN_BID, bidPoints: MIN_BID }).made, 'making exactly the bid makes it');
  ok(!dealResult({ finalBid: MIN_BID, bidPoints: MIN_BID - 1 }).made, 'one short misses');
}

// ===========================================================================
section('Single hand: ±3, never multiplied');
// ===========================================================================
{
  same(singleHandResult({ lost: false }), { made: true, multiplier: 1, delta: SINGLE_HAND_STAKE },
    'all eight tricks scores the single-hand stake');
  same(singleHandResult({ lost: true }), { made: false, multiplier: 1, delta: -SINGLE_HAND_STAKE },
    'one lost trick costs it');
  ok(SINGLE_HAND_STAKE > DEAL_STAKE, 'a single hand is worth more than an ordinary deal');
}

// ===========================================================================
section('The pair: four towards whoever holds it, clamped to the bid range');
// ===========================================================================
{
  let clampedLow = 0, clampedHigh = 0, full = 0;
  for (let bid = MIN_BID; bid <= MAX_BID; bid++) {
    const down = pairAdjust(bid, true);
    const up = pairAdjust(bid, false);
    ok(down >= MIN_BID && down <= bid, `the bidding side's pair lowers ${bid}, never below ${MIN_BID}`);
    ok(up <= MAX_BID && up >= bid, `the opponents' pair raises ${bid}, never above ${MAX_BID}`);
    eq(down, Math.max(MIN_BID, bid - PAIR_SHIFT), `down from ${bid}`);
    eq(up, Math.min(MAX_BID, bid + PAIR_SHIFT), `up from ${bid}`);
    if (bid - PAIR_SHIFT < MIN_BID) clampedLow++; else full++;
    if (bid + PAIR_SHIFT > MAX_BID) clampedHigh++;
  }
  ok(clampedLow > 0 && clampedHigh > 0 && full > 0,
    `the clamp bit at the bottom ${clampedLow} times and the top ${clampedHigh} times, and ${full} moved the full four`);
  eq(pairAdjust(MIN_BID, true), MIN_BID, 'the lowest bid helped by its own pair stays the lowest bid');
  eq(pairAdjust(MAX_BID, false), MAX_BID, 'the highest bid cannot be raised');
}

// ===========================================================================
section('Game points: only the bidding side moves, and negatives are normal');
// ===========================================================================
{
  same(applyDelta([0, 0], 1, -1), [0, -1], 'a failed first bid puts the bidding side on −1');
  const before = [2, -3];
  const after = applyDelta(before, 0, 4);
  same(before, [2, -3], 'applyDelta does not touch its input');
  same(after, [6, -3], 'and moves only the side it was told to');

  eq(leadingTeam([-1, -3]), 0, 'higher is better whatever the sign: −1 leads −3');
  eq(leadingTeam([0, 0]), null, 'level is level');
  eq(leadingTeam([-2, 1]), 1, 'a positive leads a negative');
}

// ===========================================================================
section('The finish: +6 wins, −6 loses');
// ===========================================================================
{
  let overs = 0, continues = 0;
  for (let a = -MATCH_TARGET - 2; a <= MATCH_TARGET + 2; a++) {
    for (let b = -MATCH_TARGET - 2; b <= MATCH_TARGET + 2; b++) {
      // Only reachable pairs: at most one side past a line.
      const past = (x) => x >= MATCH_TARGET || x <= -MATCH_TARGET;
      if (past(a) && past(b)) continue;
      const o = matchOutcome([a, b]);
      eq(o.over, past(a) || past(b), `[${a}, ${b}] is ${past(a) || past(b) ? '' : 'not '}over`);
      if (!o.over) { continues++; continue; }
      overs++;
      const mover = past(a) ? 0 : 1;
      const x = mover === 0 ? a : b;
      if (x >= MATCH_TARGET) {
        eq(o.winner, mover, `reaching +${MATCH_TARGET} wins`);
        eq(o.how, 'reached', 'and says how');
      } else {
        eq(o.loser, mover, `falling to −${MATCH_TARGET} loses`);
        eq(o.winner, 1 - mover, 'and the other side wins');
        eq(o.how, 'fell', 'and says how');
      }
    }
  }
  ok(overs > 20 && continues > 50, `${overs} finished and ${continues} unfinished score pairs swept`);
  eq(matchOutcome([MATCH_TARGET - 1, -(MATCH_TARGET - 1)]).over, false, 'one short of either line is still a match');

  // A random walk of deals, each moving only the bidding side, ends exactly at
  // the first crossing — never before, never after.
  for (let m = 0; m < 300; m++) {
    let gp = [0, 0];
    let deals = 0;
    let endedAt = null;
    while (!matchOutcome(gp).over && deals < 500) {
      const team = randInt(2);
      const single = randInt(10) === 0;
      const r = single
        ? singleHandResult({ lost: randInt(2) === 0 })
        : dealResult({ finalBid: MIN_BID + randInt(MAX_BID - MIN_BID + 1), bidPoints: randInt(PACK_POINTS + 1), level: randInt(3) });
      gp = applyDelta(gp, team, r.delta);
      deals++;
      if (matchOutcome(gp).over) endedAt = deals;
    }
    ok(endedAt !== null, 'every random match finishes');
    const o = matchOutcome(gp);
    ok(gp[o.winner] >= MATCH_TARGET || gp[o.loser] <= -MATCH_TARGET, 'and finishes on a crossed line');
  }
}

// ###########################################################################
//
//  CHECKPOINT 3 — THE RULES
//
// ###########################################################################

// ===========================================================================
section('The bid range: 16 to the whole pack, ascending only');
// ===========================================================================
{
  eq(MAX_BID, PACK_POINTS, 'the highest bid is every point in the pack — derived, not typed');
  ok(MIN_BID * 2 > PACK_POINTS, 'the lowest bid is a claim to more than half the points');
  eq(BID_STEP, 1, 'bids rise by one');
  const opening = legalBids(null);
  eq(opening[0], MIN_BID, 'the opening bid is the minimum');
  eq(opening[opening.length - 1], MAX_BID, 'and any bid up to the maximum may open');
  eq(opening.length, MAX_BID - MIN_BID + 1, 'every step in between');
  for (let high = MIN_BID; high <= MAX_BID; high++) {
    const next = legalBids(high);
    ok(next.every((b) => b > high), `over ${high}, every legal bid is strictly higher`);
    eq(next.length, MAX_BID - high, `and there are ${MAX_BID - high} of them`);
    for (let b = MIN_BID - 2; b <= MAX_BID + 2; b++) {
      eq(bidIsLegal(b, high), b > high && b <= MAX_BID, `bid ${b} over ${high}`);
      if (!bidIsLegal(b, high)) ok(typeof illegalBidReason(b, high) === 'string', 'and a refusal says why');
    }
  }
  same(legalBids(MAX_BID), [], 'nothing beats the maximum, which is why a maximum bid ends the auction');
  ok(!bidIsLegal(16.5, null) && !bidIsLegal('17', null) && !bidIsLegal(NaN, null), 'only integers are bids');
  eq(illegalBidReason(MIN_BID - 1, null), `bids run from ${MIN_BID} to ${MAX_BID}`, 'below the range says the range');
  eq(illegalBidReason(MIN_BID, MIN_BID + 2), `must be higher than ${MIN_BID + 2}`, 'and under the high bid says so');
}

// ===========================================================================
section('Four toggles, sixteen games');
// ===========================================================================
{
  eq(TOGGLES.length, 4, 'exactly four toggles');
  const all = allConfigs();
  eq(all.length, 2 ** TOGGLES.length, `${all.length} combinations`);
  eq(new Set(all.map((c) => JSON.stringify(c))).size, all.length, 'every combination distinct');
  for (const key of TOGGLES) {
    eq(all.filter((c) => c[key]).length, all.length / 2, `${key} is on in exactly half of them`);
  }

  // The allow-list.
  const n = normalizeConfig({ pair: false, double: true, singleHand: true, seventh: false, hook: true, __proto__: { x: 1 } });
  same(Object.keys(n), TOGGLES, 'normalizeConfig keeps the four toggles and nothing else');
  ok(Object.isFrozen(n), 'and freezes the result');
  ok(Object.values(n).every((v) => typeof v === 'boolean'), 'every value a boolean, so the freeze is deep');
  same(normalizeConfig(null), DEFAULT_CONFIG, 'nothing at all is the default');
  same(normalizeConfig({ pair: 'false', seventh: 'true', double: 1, singleHand: null }), DEFAULT_CONFIG,
    'a string, a number or a null is not a boolean, and does not switch anything');
  for (const c of all) same(normalizeConfig(c), c, 'every combination survives normalisation unchanged');
}

// ===========================================================================
section('Presets: three points in the space');
// ===========================================================================
{
  eq(PRESETS.length, 3, 'three presets');
  same(presetConfig('classic'), DEFAULT_CONFIG, 'Classic is the default');
  same(presetConfig('classic'), { pair: true, double: true, singleHand: false, seventh: false },
    'Classic: pair and double on, single hand and seventh card off');
  ok(TOGGLES.every((k) => presetConfig('full')[k] === true), 'Full table: all four on');
  ok(TOGGLES.every((k) => presetConfig('first')[k] === false), 'First game: all four off');
  for (const p of PRESETS) {
    eq(presetMatching(presetConfig(p.id)), p.id, `${p.label} is recognised as itself`);
    ok(p.label && p.blurb.length > 20, `${p.label} has a label and a blurb`);
    // Flip any one toggle and it is Custom — unless that happens to land on
    // another preset, which none of the three single-flips do.
    for (const key of TOGGLES) {
      const c = normalizeConfig({ ...p.config, [key]: !p.config[key] });
      eq(presetMatching(c), null, `${p.label} with ${key} flipped is Custom`);
    }
  }
  same(presetConfig('nonsense'), DEFAULT_CONFIG, 'an unknown preset is the default, cleaned');
  eq(presetMatching(normalizeConfig({ pair: true, double: false, singleHand: true, seventh: false })), null,
    'most of the sixteen are Custom');
}

// ===========================================================================
section('Toggle words, one copy each');
// ===========================================================================
{
  for (const key of TOGGLES) {
    const l = TOGGLE_LABELS[key];
    ok(l && l.label && l.blurb.length > 20 && l.sheet.length > 60, `${key} has a label, a blurb and a sheet sentence`);
    eq(toggleLabel(key), l.label, `toggleLabel(${key})`);
  }
  eq(Object.keys(TOGGLE_LABELS).length, TOGGLES.length, 'and no words for a toggle that does not exist');
  eq(TOGGLE_LABELS.toString, undefined, 'a prototype key finds nothing');
  eq(toggleLabel('hook'), 'hook', 'an unknown toggle renders as itself');
}

// ===========================================================================
section('Names');
// ===========================================================================
{
  eq(cleanName('  Asha   Rao '), 'Asha Rao', 'whitespace collapsed');
  eq(cleanName('W'.repeat(40)).length, MAX_NAME_LEN, `capped at ${MAX_NAME_LEN}`);
  eq(cleanName('a\u0000b\u0007c\u009Fd'), 'abcd', 'control characters dropped');
  eq(cleanName(null), '', 'null is empty');
}

// ###########################################################################
//
//  CHECKPOINT 4 — THE ENGINE
//
// ###########################################################################

// ---------------------------------------------------------------------------
// The table every engine section uses: four humans p0..p3, so the suite can
// act for any seat directly. Bots are the driver's business (checkpoint 6);
// the engine does not care who is behind a seat.
// ---------------------------------------------------------------------------
const IDS = ['p0', 'p1', 'p2', 'p3'];
const NAMES = ['Asha', 'Ben', 'Cleo', 'Dev'];
const ALL_CONFIGS = allConfigs();

function newTable(config = DEFAULT_CONFIG, opts = {}) {
  const g = new GameEngine(opts);
  IDS.forEach((id, i) => g.addPlayer(id, NAMES[i], { clientId: `client-${i}-0123456789` }));
  g.setConfig('p0', config);
  return g;
}

/** An identity "shuffle", or a fixed pack: deal exactly what is given. */
const fixedPack = (pack) => () => pack.slice();

/** Push the clock past whatever transient pause the engine is in. */
function settle(g) {
  let n = 0;
  for (;;) {
    if (g.phase === PHASES.FIRST_FOUR) g.tick(g.phaseAt + FIRST_FOUR_MS);
    else if (g.phase === PHASES.LAST_FOUR) g.tick(g.phaseAt + LAST_FOUR_MS);
    else if (g.sweepAt !== null) g.tick(g.sweepAt + TRICK_PAUSE_MS);
    else return;
    if (++n > 100) throw new Error('settle: the engine is not settling');
  }
}

/** A seeded coin with probability p. */
const coin = (p) => rand32() / 2 ** 32 < p;
const pick = (arr) => arr[randInt(arr.length)];

/**
 * The random policy: every choice uniform-ish over what is legal. It is not
 * trying to play well; it is trying to reach every state the rules allow,
 * which a good player would avoid.
 */
const RANDOM_POLICY = {
  bid: (g, seat, priv) => {
    const legal = priv.bidOptions.filter((o) => o.legal).map((o) => o.bid);
    if (!legal.length || coin(0.45)) return null;
    // Mostly the lowest legal bid, sometimes a jump, occasionally all the way.
    if (coin(0.05)) return legal[legal.length - 1];
    return coin(0.7) ? legal[0] : pick(legal.slice(0, 4));
  },
  trump: (g, seat, priv) => (priv.trumpChoice.seventh && coin(0.3) ? 'seventh' : pick(priv.hand).code),
  declare: (g, seat, options) => (coin(options[0] === 'single' ? 0.08 : 0.35) ? options[0] : 'pass'),
  call: (g, seat, priv) => coin(0.4),
  card: (g, seat, priv) => pick(priv.hand.filter((c) => c.legal)).code,
  pair: () => coin(0.8),
};

/**
 * Take one action for whoever the engine is waiting on, through the engine's
 * public methods exactly as an intent would. Every action taken must be
 * accepted — the policy only chooses among what privateStateFor() offered —
 * and a refusal is a failure of the engine's offer, not of the policy.
 */
let STEP_NOW = 0;
function step(g, policy = RANDOM_POLICY) {
  settle(g);
  const now = ++STEP_NOW;
  const expectOk = (r, what) => {
    if (!r || !r.ok) { failed++; console.error('  ✗ FAIL: engine refused an offered action:', what, r && r.error); }
    return r;
  };
  // A pair is an optional declaration by anybody whose side just won a trick,
  // so it is offered before the turn-holder acts.
  if (g.phase === PHASES.PLAY) {
    for (let s = 0; s < SEATS; s++) {
      if (g.privateStateFor(IDS[s]).canPair && policy.pair(g, s)) {
        expectOk(g.declarePair(IDS[s], now), `declarePair by ${s}`);
        return 'pair';
      }
    }
  }
  const seat = g.turnSeat;
  const id = IDS[seat];
  const priv = g.privateStateFor(id);
  switch (g.phase) {
    case PHASES.AUCTION: {
      const b = policy.bid(g, seat, priv);
      if (b === null) expectOk(g.passBid(id, now), 'pass');
      else expectOk(g.placeBid(id, b, now), `bid ${b}`);
      return 'auction';
    }
    case PHASES.TRUMP_CHOICE: {
      const t = policy.trump(g, seat, priv);
      if (t === 'seventh') expectOk(g.chooseSeventh(id, now), 'seventh');
      else expectOk(g.chooseTrump(id, t, now), `trump ${t}`);
      return 'trump';
    }
    case PHASES.DECLARE: {
      const opts = priv.declareOptions;
      const c = policy.declare(g, seat, opts);
      const fn = { single: 'singleHand', double: 'double', redouble: 'redouble', pass: 'passDeclare' }[c];
      expectOk(g[fn](id, now), c);
      return 'declare';
    }
    case PHASES.PLAY: {
      if (priv.canCall && policy.call(g, seat, priv)) {
        expectOk(g.callTrump(id, now), 'call');
        return 'call';
      }
      const code = policy.card(g, seat, g.privateStateFor(id));
      expectOk(g.playCard(id, code, now), `play ${code}`);
      return 'play';
    }
    case PHASES.DEAL_OVER:
      expectOk(g.nextDeal('p0', now), 'nextDeal');
      return 'next';
    default:
      return null;
  }
}

/** Every card the engine holds anywhere, for the conservation law. */
function everyCard(g) {
  const out = [];
  for (const h of g.hands) out.push(...h);
  out.push(...g.stock);
  if (g.indicator) out.push(g.indicator);
  for (const p of g.plays) out.push(p.code);
  for (const t of g.tricks) for (const p of t.plays) out.push(p.code);
  return out;
}

/** The invariants that must hold in EVERY state of every deal. */
function checkInvariants(g, label) {
  if (g.phase === PHASES.LOBBY || g.phase === PHASES.MATCH_OVER) return;
  const cards = everyCard(g);
  if (g.phase !== PHASES.DEAL_OVER) {
    eq(cards.length, PACK_SIZE, `${label}: every card is somewhere`);
    eq(new Set(cards).size, PACK_SIZE, `${label}: and in exactly one place`);
  }
  // Points won so far are exactly the points in the tricks taken, counting a
  // finished trick still on the table.
  const done = g.tricks.concat(g.sweepAt !== null && g.lastTrick ? [{ plays: g.lastTrick.plays, winner: g.lastTrick.winner }] : []);
  same(g.pointsWon, pointsBySide(done), `${label}: points won match the tricks taken`);
  // Nobody is ever waiting on the seat that sits out.
  if (g.single) ok(g.turnSeat !== g.single.out || g.phase !== PHASES.PLAY, `${label}: the turn never lands on the sitting-out seat`);
  // Before the reveal the public state names no trump at all.
  const pub = g.publicState();
  if (!g.revealed) {
    eq(pub.trump, null, `${label}: no trump in the public state before the reveal`);
    ok(!pub.indicator || pub.indicator.card === null, `${label}: and the indicator is a card back`);
  }
}

/** Play one deal to its end, checking invariants at every state. */
function playDeal(g, policy = RANDOM_POLICY, onState = null) {
  const startDeal = g.dealIndex;
  let guard = 0;
  while (g.phase !== PHASES.DEAL_OVER && g.phase !== PHASES.MATCH_OVER) {
    settle(g);
    checkInvariants(g, `deal ${g.dealIndex}`);
    if (onState) onState(g);
    if (g.phase === PHASES.DEAL_OVER) break;
    step(g, policy);
    if (++guard > 400) { failed++; console.error('  ✗ FAIL: a deal did not finish'); break; }
  }
  return g.dealIndex - startDeal;
}

/** Play a whole match from the lobby. */
function playMatch(config, policy = RANDOM_POLICY, onState = null, maxDeals = 200) {
  const g = newTable(config);
  eq(g.startMatch('p0', 0).ok, true, 'the match starts');
  let deals = 0;
  while (g.phase !== PHASES.MATCH_OVER && deals < maxDeals) {
    playDeal(g, policy, onState);
    if (onState) onState(g);
    if (g.phase === PHASES.DEAL_OVER) step(g, policy);
    deals++;
  }
  return g;
}

/**
 * Where a card is: { where: 'hand', seat, i } | { where: 'stock', i } |
 * { where: 'indicator' } | null if it is face up on the table.
 */
function locate(g, code) {
  for (let s = 0; s < SEATS; s++) {
    const i = g.hands[s].indexOf(code);
    if (i !== -1) return { where: 'hand', seat: s, i };
  }
  const i = g.stock.indexOf(code);
  if (i !== -1) return { where: 'stock', i };
  if (g.indicator === code) return { where: 'indicator' };
  return null;
}

/**
 * Swap two cards between their hidden places, in place. The trump card moves
 * with the indicator before the reveal, because trumpSuit is derived from it.
 */
function swapHidden(g, a, b) {
  const la = locate(g, a), lb = locate(g, b);
  const put = (loc, code) => {
    if (loc.where === 'hand') g.hands[loc.seat][loc.i] = code;
    else if (loc.where === 'stock') g.stock[loc.i] = code;
    else { g.indicator = code; if (!g.revealed) g.trumpCard = code; }
  };
  put(la, b);
  put(lb, a);
}

/** A copy of an engine through the persistence path. */
function cloneEngine(g) {
  const c = new GameEngine();
  c.restore(JSON.parse(JSON.stringify(g.serialize())));
  return c;
}

/** Which cards `seat` can see (its own hand, its own indicator under a
 *  concealed trump); null is the watcher, who sees no hand at all. */
function visibleTo(g, seat) {
  if (seat === null) return new Set();
  const v = new Set(g.hands[seat]);
  if (seat === g.bidder && g.trumpMode === 'concealed' && g.indicator && !g.revealed) v.add(g.indicator);
  return v;
}

// ===========================================================================
section('The engine: the deal goes ANTICLOCKWISE from the dealer\'s right');
// ===========================================================================
{
  // An UNSHUFFLED pack, so the result is readable: the first four codes of
  // the pack must land on the seat to the dealer's right.
  const pack = buildPack();
  const g = newTable(DEFAULT_CONFIG, { shuffle: fixedPack(pack) });
  g.startMatch('p0', 0);
  eq(g.dealerSeat, 0, 'seat zero deals the first deal');
  eq(nextSeat(g.dealerSeat), 3, 'the seat on its right is 3');
  same(g.hands[3], pack.slice(0, BATCH), 'seat 3 — the dealer\'s right — gets the first four, in a block');
  same(g.hands[2], pack.slice(BATCH, 2 * BATCH), 'then seat 2');
  same(g.hands[1], pack.slice(2 * BATCH, 3 * BATCH), 'then seat 1');
  same(g.hands[0], pack.slice(3 * BATCH, 4 * BATCH), 'and the dealer last');
  eq(g.phase, PHASES.FIRST_FOUR, 'the first four are out and the table pauses');
  ok(g.hands.every((h) => h.length === BATCH), 'four cards each');
  eq(g.publicState().seats.map((s) => s.handCount).join(), '4,4,4,4', 'and the counts are public');

  settle(g);
  eq(g.phase, PHASES.AUCTION, 'then the auction');
  eq(g.turnSeat, 3, 'which starts with the player to the dealer\'s right');

  // The dealer rotates anticlockwise, deal after deal — through throw-ins too.
  const dealers = [g.dealerSeat];
  for (let d = 0; d < 7; d++) {
    while (g.phase === PHASES.AUCTION) g.passBid(IDS[g.turnSeat], 0);
    settle(g);
    dealers.push(g.dealerSeat);
  }
  same(dealers, [0, 3, 2, 1, 0, 3, 2, 1], 'the deal passes to the right: 0, 3, 2, 1, 0 …');
}

// ===========================================================================
section('The engine: the auction');
// ===========================================================================
{
  const auction = (config = DEFAULT_CONFIG) => {
    const g = newTable(config);
    g.startMatch('p0', 0);
    settle(g);
    return g;
  };

  // Ascending only, and the public record of every call.
  {
    const g = auction();
    const s0 = g.turnSeat;
    eq(g.placeBid(IDS[s0], MIN_BID - 1, 0).ok, false, 'a bid below the minimum is refused');
    eq(g.placeBid(IDS[s0], MAX_BID + 1, 0).ok, false, 'and above the maximum');
    eq(g.placeBid(IDS[nextSeat(s0)], MIN_BID, 0).ok, false, 'and out of turn');
    ok(g.placeBid(IDS[s0], 18, 0).ok, 'an opening bid of 18');
    const s1 = g.turnSeat;
    eq(s1, nextSeat(s0), 'the turn moves anticlockwise');
    eq(g.placeBid(IDS[s1], 18, 0).ok, false, 'an equal bid is refused — higher or pass');
    eq(g.placeBid(IDS[s1], 17, 0).ok, false, 'and a lower one');
    eq(g.placeBid(IDS[s1], 18, 0).error, 'must be higher than 18', 'with the reason');
    ok(g.placeBid(IDS[s1], 19, 0).ok, 'a higher bid is taken');
    same(g.publicState().auction.calls, [{ seat: s0, bid: 18 }, { seat: s1, bid: 19 }], 'bids are public once made');
    eq(g.publicState().auction.high, 19, 'with the high bid');
    eq(g.publicState().auction.highSeat, s1, 'and who holds it');
    // The private pad offers exactly the legal bids.
    const priv = g.privateStateFor(IDS[g.turnSeat]);
    same(priv.bidOptions.filter((o) => o.legal).map((o) => o.bid), legalBids(19), 'the pad offers only bids above the high bid');
    eq(g.privateStateFor(IDS[s0]).bidOptions, null, 'and only to the seat whose turn it is');
  }

  // A pass is final; the auction ends at three passes.
  {
    const g = auction();
    const order = seatsFrom(g.turnSeat);
    ok(g.passBid(IDS[order[0]], 0).ok, 'the first seat passes');
    ok(g.placeBid(IDS[order[1]], 16, 0).ok, 'the second opens');
    ok(g.placeBid(IDS[order[2]], 17, 0).ok, 'the third raises');
    ok(g.passBid(IDS[order[3]], 0).ok, 'the fourth passes');
    eq(g.turnSeat, order[1], 'the turn skips the seat that passed — a pass is final');
    ok(g.placeBid(IDS[order[1]], 18, 0).ok, 'partners and opponents may keep raising');
    eq(g.turnSeat, order[2], 'and back to the other bidder');
    ok(g.passBid(IDS[order[2]], 0).ok, 'who passes');
    eq(g.phase, PHASES.TRUMP_CHOICE, 'three passes behind a standing bid end the auction');
    eq(g.bidder, order[1], 'the high bidder is the bidder');
    eq(g.bid, 18, 'at their bid');
    eq(g.turnSeat, g.bidder, 'and it is their turn to choose trump');
  }

  // Twenty-eight ends it at once.
  {
    const g = auction();
    const s = g.turnSeat;
    ok(g.placeBid(IDS[s], MAX_BID, 0).ok, 'the first bidder bids the whole pack');
    eq(g.phase, PHASES.TRUMP_CHOICE, 'and nobody else is asked');
    eq(g.bidder, s, 'they are the bidder');
  }

  // Partners may outbid each other.
  {
    const g = auction();
    const s = g.turnSeat;
    ok(g.placeBid(IDS[s], 16, 0).ok, 'a bid');
    ok(g.passBid(IDS[nextSeat(s)], 0).ok, 'an opponent passes');
    ok(g.placeBid(IDS[partnerOf(s)], 20, 0).ok, 'the partner outbids it — legal, if rarely wise');
  }

  // All four pass: thrown in.
  {
    const g = auction();
    const dealer = g.dealerSeat;
    const deal = g.dealIndex;
    for (let i = 0; i < SEATS; i++) ok(g.passBid(IDS[g.turnSeat], 0).ok, `pass ${i + 1}`);
    eq(g.phase, PHASES.FIRST_FOUR, 'four passes throw the deal in and a new one is dealt');
    eq(g.dealerSeat, nextSeat(dealer), 'by the next dealer');
    eq(g.dealIndex, deal + 1, 'as a new deal');
    eq(g.history.length, 1, 'recorded in the history');
    eq(g.history[0].thrownIn, true, 'as thrown in');
    same(g.gamePoints, [0, 0], 'scoring nothing');
    ok(g.log.some((l) => l.kind === 'thrown'), 'and said aloud');
  }

  // Sweep: across many random auctions, the rules hold as properties.
  {
    let ended = 0, thrown = 0, maxed = 0;
    for (let n = 0; n < 400; n++) {
      const g = auction(pick(ALL_CONFIGS));
      const passedAt = new Set();
      let lastHigh = null;
      const startDeal = g.dealIndex;
      while (g.phase === PHASES.AUCTION && g.dealIndex === startDeal) {
        const seat = g.turnSeat;
        ok(!passedAt.has(seat), 'a seat that passed is never asked again');
        step(g);
        const calls = g.auction.calls;
        const last = calls[calls.length - 1];
        if (g.dealIndex !== startDeal) break;
        if (last && last.bid === null) passedAt.add(last.seat);
        if (last && last.bid !== null) {
          ok(lastHigh === null || last.bid > lastHigh, 'every bid is higher than the last');
          lastHigh = last.bid;
        }
      }
      if (g.dealIndex !== startDeal) { thrown++; continue; }
      ended++;
      if (g.bid === MAX_BID) maxed++;
      else eq(g.auction.passed.filter(Boolean).length, SEATS - 1, 'an auction below the maximum ends with three passes');
    }
    ok(ended > 100 && thrown > 10 && maxed > 2, `${ended} auctions won (${maxed} at the maximum), ${thrown} thrown in`);
  }
}

// ===========================================================================
section('The engine: trump — a card face down, or the unseen seventh');
// ===========================================================================
{
  const toTrump = (config, pack = null) => {
    const g = newTable(config, pack ? { shuffle: fixedPack(pack) } : {});
    g.startMatch('p0', 0);
    settle(g);
    g.placeBid(IDS[g.turnSeat], MIN_BID, 0);
    while (g.phase === PHASES.AUCTION) g.passBid(IDS[g.turnSeat], 0);
    return g;
  };

  // Concealed.
  {
    const g = toTrump(DEFAULT_CONFIG);
    const b = g.bidder;
    const four = g.hands[b].slice();
    eq(g.chooseTrump(IDS[(b + 1) % SEATS], four[0], 0).ok, false, 'only the bidder chooses trump');
    eq(g.chooseTrump(IDS[b], g.hands[(b + 1) % SEATS][0], 0).ok, false, 'and only from their own four');
    eq(g.chooseSeventh(IDS[b], 0).ok, false, 'the seventh card is refused while its toggle is off');
    eq(g.chooseSeventh(IDS[b], 0).error, 'the seventh-card rule is off in this game', 'and says so');
    eq(g.privateStateFor(IDS[b]).trumpChoice.seventh, false, 'and is not offered');
    const card = four[2];
    ok(g.chooseTrump(IDS[b], card, 0).ok, 'the bidder places a card face down');
    eq(g.trumpMode, 'concealed', 'concealed');
    ok(!g.hands[b].includes(card), 'the indicator leaves the bidder\'s hand');
    eq(g.phase, PHASES.LAST_FOUR, 'and the last four are dealt');
    eq(g.hands[b].length, HAND_SIZE - 1, 'the bidder holds seven');
    ok([0, 1, 2, 3].filter((s) => s !== b).every((s) => g.hands[s].length === HAND_SIZE), 'everybody else eight');
    eq(g.privateStateFor(IDS[b]).indicator, card, 'the bidder can peek at their indicator');
    eq(g.privateStateFor(IDS[b]).knownTrump, suitOf(card), 'and knows the trump');
    eq(g.privateStateFor(IDS[partnerOf(b)]).indicator, null, 'their partner cannot');
    eq(g.privateStateFor(IDS[partnerOf(b)]).knownTrump, null, 'and does not know the trump');
    const pub = g.publicState();
    same(pub.indicator, { seat: b, faceUp: false, card: null }, 'the table sees a card back by the bidder');
    eq(pub.trump, null, 'and no trump');
    eq(pub.trumpMode, 'concealed', 'only that one was chosen');
    ok(!JSON.stringify(pub).includes(`"${card}"`), 'the indicator\'s code is nowhere in the public state');
    ok(!pub.log.some((l) => l.text.includes(suitName(suitOf(card)))), 'and the log does not name its suit');
  }

  // Seventh card: the bidder's seventh dealt card, unseen by everyone.
  {
    const pack = buildPack();
    const g = toTrump({ ...DEFAULT_CONFIG, seventh: true }, pack);
    const b = g.bidder;
    const before = g.hands[b].slice();
    eq(g.privateStateFor(IDS[b]).trumpChoice.seventh, true, 'the seventh card is offered when its toggle is on');
    ok(g.chooseSeventh(IDS[b], 0).ok, 'the bidder announces seventh card');
    // With an unshuffled pack the second batch is the second half, dealt in
    // blocks from the dealer's right. The bidder's block of four is at their
    // position in that order, and the seventh card is the third of it.
    const order = seatsFrom(nextSeat(g.dealerSeat));
    const block = pack.slice(SEATS * BATCH + order.indexOf(b) * BATCH, SEATS * BATCH + (order.indexOf(b) + 1) * BATCH);
    eq(g.indicator, block[2], 'the indicator is the seventh card dealt to the bidder');
    same(g.hands[b], before.concat(block.filter((_, i) => i !== 2)), 'and the other three join their hand');
    eq(g.hands[b].length, HAND_SIZE - 1, 'so the bidder holds seven');
    eq(g.privateStateFor(IDS[b]).indicator, null, 'and cannot see the indicator');
    eq(g.privateStateFor(IDS[b]).knownTrump, null, 'nor the trump — the bidder included');
    ok(!JSON.stringify(g.privateStateFor(IDS[b])).includes(`"${g.indicator}"`), 'the code is nowhere in the bidder\'s own view');
    same(g.privateStateFor(IDS[b]).hand.map((c) => c.code), sortHand(g.hands[b]), 'and their hand is sorted without a trump');
    eq(g.publicState().trumpMode, 'seventh', 'the table knows it was the seventh card');
  }
}

// ===========================================================================
section('The engine: THE CONCEALED TRUMP — every view that should not know, does not');
// ===========================================================================
//
// THE METHOD. A view leaks the hidden trump if and only if it would be
// different had the hidden card been a different card. So at every state of
// thousands of deals, for every observer — each of the four seats, and a
// watcher with no seat — take a copy of the engine, swap the indicator with
// some other card the observer cannot see, and require the observer's whole
// view (public state + their own private state) to come out byte-identical.
//
// That one property covers the public state, the partner, the opponents, the
// watcher frame, the log (which is in the public state, and is what the live
// region speaks), the sort order of a hand, the legal flags on every card, and
// under seventh card the bidder's own view. It cannot be satisfied by a
// careful field list, because it does not consult one.
{
  let compared = 0, statesPreReveal = 0, seventhBidder = 0, swapsAcrossSuits = 0;
  const observers = [0, 1, 2, 3, null];
  const viewOf = (e, seat) => JSON.stringify({
    pub: e.publicState(),
    priv: seat === null ? null : e.privateStateFor(IDS[seat]),
  });

  const audit = (g) => {
    if (!g.indicator || g.revealed) return;
    statesPreReveal++;
    for (const obs of observers) {
      // The bidder under a concealed trump is ENTITLED to know; skip them.
      if (obs === g.bidder && g.trumpMode === 'concealed') continue;
      const seen = visibleTo(g, obs);
      // Candidates: every hidden card not visible to this observer.
      const hidden = [];
      for (let s = 0; s < SEATS; s++) for (const c of g.hands[s]) if (!seen.has(c)) hidden.push(c);
      for (const c of g.stock) if (!seen.has(c)) hidden.push(c);
      const other = hidden.filter((c) => suitOf(c) !== suitOf(g.indicator));
      if (!other.length) continue;
      const swapWith = pick(other);
      const a = cloneEngine(g);
      const b = cloneEngine(g);
      swapHidden(b, b.indicator, swapWith);
      ok(suitOf(b.trumpCard) !== suitOf(a.trumpCard), 'the swap really did change the trump suit');
      swapsAcrossSuits++;
      const va = viewOf(a, obs), vb = viewOf(b, obs);
      compared++;
      if (va !== vb) {
        failed++;
        console.error(`  ✗ FAIL: ${obs === null ? 'the watcher' : `seat ${obs}`} can tell the hidden trump `
          + `(${a.trumpMode}, bidder ${a.bidder}, phase ${a.phase}): view changed when the indicator became ${swapWith}`);
      } else passed++;
      if (obs === g.bidder && g.trumpMode === 'seventh') seventhBidder++;
    }
  };

  for (const config of ALL_CONFIGS) {
    for (let m = 0; m < 6; m++) {
      const g = newTable(config);
      g.startMatch('p0', 0);
      for (let d = 0; d < 3 && g.phase !== PHASES.MATCH_OVER; d++) {
        playDeal(g, RANDOM_POLICY, audit);
        if (g.phase === PHASES.DEAL_OVER) step(g);
      }
    }
  }
  ok(compared > 5000, `${compared} counterfactual views compared across ${statesPreReveal} pre-reveal states`);
  ok(seventhBidder > 200, `including ${seventhBidder} of the BIDDER'S OWN view under seventh card`);
  eq(swapsAcrossSuits, compared, 'and every swap moved the trump to a different suit');

  // The control: the same comparison for the bidder under a concealed trump
  // MUST differ — they are entitled to know, and the view shows it. A method
  // that could not tell the bidder apart from everyone else would prove
  // nothing about anyone.
  let controls = 0, differed = 0;
  for (let n = 0; n < 200; n++) {
    const g = newTable(DEFAULT_CONFIG);
    g.startMatch('p0', 0);
    settle(g);
    g.placeBid(IDS[g.turnSeat], MIN_BID, 0);
    while (g.phase === PHASES.AUCTION) g.passBid(IDS[g.turnSeat], 0);
    g.chooseTrump(IDS[g.bidder], g.hands[g.bidder][0], 0);
    settle(g);
    const elsewhere = [];
    for (let s = 0; s < SEATS; s++) if (s !== g.bidder) for (const c of g.hands[s]) if (suitOf(c) !== suitOf(g.indicator)) elsewhere.push(c);
    const b = cloneEngine(g);
    swapHidden(b, b.indicator, pick(elsewhere));
    controls++;
    if (viewOf(cloneEngine(g), g.bidder) !== viewOf(b, g.bidder)) differed++;
  }
  eq(differed, controls, `the control: the concealed bidder's own view DOES change, ${differed} of ${controls}`);
}

// ===========================================================================
section('The engine: privacy of hands and the second batch');
// ===========================================================================
{
  // The same method, for the cards every game hides: other players' hands and
  // the undealt second four. Any two cards an observer cannot see may trade
  // places without the observer's view changing.
  let compared = 0;
  for (const config of [ALL_CONFIGS[0], ALL_CONFIGS[15], DEFAULT_CONFIG]) {
    for (let m = 0; m < 4; m++) {
      const g = newTable(config);
      g.startMatch('p0', 0);
      playDeal(g, RANDOM_POLICY, (e) => {
        if (e.phase === PHASES.DEAL_OVER || e.phase === PHASES.MATCH_OVER) return;
        for (const obs of [0, 1, 2, 3, null]) {
          const seen = visibleTo(e, obs);
          const hidden = [];
          for (let s = 0; s < SEATS; s++) for (const c of e.hands[s]) if (!seen.has(c)) hidden.push(c);
          for (const c of e.stock) hidden.push(c);
          if (hidden.length < 2) continue;
          const x = pick(hidden);
          const y = pick(hidden.filter((c) => c !== x));
          // Swapping inside one hand changes nothing worth testing.
          const lx = locate(e, x), ly = locate(e, y);
          if (lx.where === 'hand' && ly.where === 'hand' && lx.seat === ly.seat) continue;
          const a = cloneEngine(e), b = cloneEngine(e);
          swapHidden(b, x, y);
          const v = (en) => JSON.stringify({ pub: en.publicState(), priv: obs === null ? null : en.privateStateFor(IDS[obs]) });
          if (v(a) !== v(b)) { failed++; console.error(`  ✗ FAIL: ${obs === null ? 'the watcher' : `seat ${obs}`} can see ${x}/${y} in phase ${e.phase}`); }
          else passed++;
          compared++;
        }
      });
    }
  }
  ok(compared > 1000, `${compared} hidden-card swaps, none visible to anyone who should not see them`);
}

// ===========================================================================
section('The engine: the call — mid-trick, never a reset, and the obligation\'s exact scope');
// ===========================================================================
{
  let calls = 0, obligedCards = 0, freeAfterCall = 0, nextTrickFree = 0, preRevealPlain = 0, plainChecks = 0;
  for (const config of ALL_CONFIGS) {
    for (let m = 0; m < 8; m++) {
      const g = newTable(config);
      g.startMatch('p0', 0);
      for (let d = 0; d < 3 && g.phase !== PHASES.MATCH_OVER; d++) {
        let callerSeat = null, callTrick = null;
        let guard = 0;
        while (g.phase !== PHASES.DEAL_OVER && g.phase !== PHASES.MATCH_OVER && guard++ < 400) {
          settle(g);
          if (g.phase !== PHASES.PLAY) { step(g); continue; }
          const seat = g.turnSeat;
          const priv = g.privateStateFor(IDS[seat]);
          const led = ledSuitOf(g.plays);

          // BEFORE THE REVEAL, EVERY SEAT'S LEGAL SET IS THE NO-TRUMP ONE.
          // Whatever the hidden suit is, the flags are exactly what follow-
          // suit alone gives.
          if (!g.revealed) {
            for (let s = 0; s < SEATS; s++) {
              const p = g.privateStateFor(IDS[s]);
              if (p.sittingOut) continue;
              const want = legalPlays(g.hands[s], led, null);
              same(p.hand.filter((c) => c.legal).map((c) => c.code).sort(), want.slice().sort(),
                'before the reveal, a seat\'s legal cards are follow-suit alone');
              plainChecks++;
            }
          }

          if (priv.canCall && coin(0.5)) {
            const before = JSON.stringify(g.plays);
            const turn = g.turnSeat;
            const bidderHand = g.hands[g.bidder].length;
            // EVERYTHING ABOUT THE TRICK, before and after. The reveal is an
            // event inside PLAY: the only public fields allowed to move are
            // the ones that ARE the reveal.
            const REVEAL_FIELDS = ['trump', 'revealed', 'revealedBy', 'caller', 'indicator', 'log', 'seats'];
            const trickView = (e) => {
              const p = e.publicState();
              for (const k of REVEAL_FIELDS) delete p[k];
              return JSON.stringify(p);
            };
            const pubBefore = trickView(g);
            ok(g.callTrump(IDS[seat], 0).ok, 'an offered call is accepted');
            calls++;
            eq(trickView(g), pubBefore, 'the call changes nothing about the table but the reveal itself — no reset');
            eq(JSON.stringify(g.plays), before, 'the call does not touch the cards already on the table');
            eq(g.turnSeat, turn, 'and the caller still has to play');
            eq(g.phase, PHASES.PLAY, 'and the phase is still PLAY');
            ok(g.revealed, 'trump is revealed');
            eq(g.publicState().trump, suitOf(g.trumpCard), 'and public');
            eq(g.hands[g.bidder].length, bidderHand + 1, 'the indicator went back into the bidder\'s hand');
            eq(g.indicator, null, 'and is no longer face down');
            eq(g.caller, seat, 'the caller is recorded');
            callerSeat = seat; callTrick = g.trickIndex;
            // THE CALLER'S NARROWED HAND.
            const after = g.privateStateFor(IDS[seat]);
            const trumps = g.hands[seat].filter((c) => suitOf(c) === g.trumpSuit);
            const holdsLed = g.hands[seat].some((c) => suitOf(c) === led);
            const legalNow = after.hand.filter((c) => c.legal).map((c) => c.code).sort();
            if (holdsLed) same(legalNow, g.hands[seat].filter((c) => suitOf(c) === led).sort(), 'a caller now holding the led suit follows it');
            else if (trumps.length) { same(legalNow, trumps.slice().sort(), 'the caller must play a trump'); obligedCards++; ok(after.mustTrump, 'and is told so'); }
            else same(legalNow, g.hands[seat].slice().sort(), 'a caller with no trump plays anything');
            ok(!after.canCall, 'and cannot call twice');
            continue;
          }

          // Everybody who is not the caller on the calling trick is free when
          // void, revealed trump or not.
          if (g.revealed && callerSeat !== null && seat !== g.caller && led && !g.hands[seat].some((c) => suitOf(c) === led)) {
            same(priv.hand.filter((c) => c.legal).map((c) => c.code).sort(), g.hands[seat].slice().sort(),
              'after the reveal, a void player who did not just call may play anything');
            if (g.trickIndex === callTrick) freeAfterCall++; else if (seat === callerSeat) nextTrickFree++;
          }

          const before = g.revealed;
          const code = pick(priv.hand.filter((c) => c.legal)).code;
          const isTrumpSuit = g.trumpSuit && suitOf(code) === g.trumpSuit;
          ok(g.playCard(IDS[seat], code, 0).ok, 'an offered card is accepted');
          const last = g.sweepAt !== null ? g.lastTrick.plays[g.lastTrick.plays.length - 1] : g.plays[g.plays.length - 1];
          eq(last.trump, !!(before && isTrumpSuit), 'a card plays as a trump exactly when trump was face up as it was played');
          if (!before && isTrumpSuit) preRevealPlain++;
          if (g.caller === seat) { failed++; console.error('  ✗ FAIL: the obligation outlived the card that met it'); }
        }
        if (g.phase === PHASES.DEAL_OVER) step(g);
      }
    }
  }
  ok(calls > 300, `${calls} calls made mid-trick`);
  ok(obligedCards > 100, `${obligedCards} times the caller was held to a trump`);
  ok(freeAfterCall > 50, `${freeAfterCall} later players on the calling trick were free when void`);
  ok(nextTrickFree > 10, `${nextTrickFree} times the same caller was free on a LATER trick`);
  ok(preRevealPlain > 100, `${preRevealPlain} trump-suit cards were played before the reveal, as plain cards`);
  ok(plainChecks > 5000, `${plainChecks} pre-reveal legal sets checked against follow-suit alone`);
  console.log(`  calls ${calls}, obliged ${obligedCards}, free after a call ${freeAfterCall}, pre-reveal trump-suit cards ${preRevealPlain}`);
}

// ===========================================================================
section('The engine: an uncalled trump is turned up by the bidder\'s last card');
// ===========================================================================
{
  const NEVER_CALL = { ...RANDOM_POLICY, call: () => false };
  let seen = 0;
  for (const config of ALL_CONFIGS.filter((c) => !c.singleHand)) {
    for (let m = 0; m < 10; m++) {
      const g = newTable(config);
      g.startMatch('p0', 0);
      let check = null;
      playDeal(g, NEVER_CALL, (e) => {
        if (e.phase !== PHASES.PLAY || e.sweepAt !== null || e.single) return;
        if (e.turnSeat === e.bidder && e.trickIndex === HAND_SIZE - 1 && !check) {
          check = true;
          seen++;
          ok(e.revealed, 'on the eighth trick the bidder\'s turn turns the indicator up');
          eq(e.revealedBy, e.bidder, 'by the bidder');
          eq(e.hands[e.bidder].length, 1, 'whose only card is the indicator');
          eq(e.hands[e.bidder][0], e.trumpCard, 'which is the trump card');
          ok(e.log.some((l) => l.kind === 'reveal' && /last card/.test(l.text)), 'and it is announced');
        }
        if (e.trickIndex < HAND_SIZE - 1 && !e.single) ok(!e.revealed, 'nobody called, so trump stays hidden until then');
      });
      // The indicator played to the last trick plays AS A TRUMP.
      if (check && g.history.length) {
        const rec = g.history[g.history.length - 1];
        if (!rec.thrownIn && !rec.single) eq(rec.trump, suitOf(g.trumpCard), 'the deal record carries the trump once it is out');
      }
    }
  }
  ok(seen > 50, `${seen} deals ended with the trump turned up by the bidder's last card`);
}

// ===========================================================================
section('The engine: the pair — after the reveal, K+Q of trump, once, ±4 clamped');
// ===========================================================================
{
  let offers = 0, declared = 0, helps = 0, hurts = 0, clamped = 0, held = 0;
  let offPairMatches = 0;
  for (const config of ALL_CONFIGS) {
    for (let m = 0; m < 20; m++) {
      const g = newTable(config);
      g.startMatch('p0', 0);
      for (let d = 0; d < 6 && g.phase !== PHASES.MATCH_OVER; d++) {
        let declaredIn = null;
        playDeal(g, { ...RANDOM_POLICY, call: () => coin(0.7), pair: () => false }, (e) => {
          if (e.phase !== PHASES.PLAY) return;
          // ONCE PER DEAL, as a property of every later state in the deal and
          // not just of the instant after the declaration.
          if (declaredIn === e.dealIndex) {
            for (let s = 0; s < SEATS; s++) ok(!e.privateStateFor(IDS[s]).canPair, 'after a pair, nobody is offered another this deal');
            eq(e.pairWindow, null, 'and no window opens again');
          }
          // THE WINDOW ITSELF, in every state: open only after the reveal, only
          // for the side that won the trick just finished, and only until the
          // next card is played.
          if (e.pairWindow) {
            ok(e.revealed, 'a pair window is open only after the reveal');
            ok(e.revealTrick !== null && e.pairWindow.trickIndex >= e.revealTrick, 'for a trick won at or after it');
            ok(e.sweepAt !== null || e.plays.length === 0, 'and only until the next card is played');
            eq(e.lastTrick && teamOf(e.lastTrick.winner), e.pairWindow.team, 'for the side that won the last trick');
          }
          if (!e.config.pair) {
            eq(e.pairWindow, null, 'with the pair off, no window ever opens');
            for (let s = 0; s < SEATS; s++) ok(!e.privateStateFor(IDS[s]).canPair, 'and nobody is offered it');
            return;
          }
          for (let s = 0; s < SEATS; s++) {
            if (!e.privateStateFor(IDS[s]).canPair) continue;
            offers++;
            // Sometimes the holder lets the moment pass, so the suite sees the
            // window CLOSE on the next card rather than only ever seeing it
            // used the instant it opens.
            if (coin(0.4)) { held++; ok(e.sweepAt !== null || e.plays.length === 0, 'a held pair is still only offered at the moment'); continue; }
            const t = e.trumpSuit;
            ok(e.revealed, 'the pair is offered only after the reveal');
            ok(e.hands[s].includes(`K${t}`) && e.hands[s].includes(`Q${t}`), 'only to a hand holding both the K and Q of trump');
            eq(e.pairWindow.team, teamOf(s), 'only when their side has just won a trick');
            ok(e.sweepAt !== null || e.plays.length === 0, 'AT THE MOMENT it was won — before the next card is played');
            eq(e.lastTrick && teamOf(e.lastTrick.winner), teamOf(s), 'and the trick that opened it was theirs');
            ok(e.lastTrick && e.revealTrick !== null && e.lastTrick.trickIndex >= e.revealTrick, 'and was won after the reveal');
            eq(e.pair, null, 'and only once');
            const from = e.finalBid;
            const r = e.declarePair(IDS[s], 0);
            ok(r.ok, 'an offered pair is accepted');
            declared++;
            declaredIn = e.dealIndex;
            const mine = sameTeam(s, e.bidder);
            eq(e.finalBid, pairAdjust(from, mine), 'the bid moves by the scoring rule');
            if (mine) helps++; else hurts++;
            if (Math.abs(e.finalBid - from) < PAIR_SHIFT) clamped++;
            ok(e.finalBid >= MIN_BID && e.finalBid <= MAX_BID, 'and stays in the bid range');
            ok(e.log.some((l) => l.kind === 'pair'), 'a declared pair is announced');
            same(e.publicState().pair, { seat: s, team: teamOf(s), from, to: e.finalBid }, 'and public');
            // Never twice.
            for (let x = 0; x < SEATS; x++) {
              eq(e.declarePair(IDS[x], 0).ok, false, 'a second pair in the same deal is refused');
            }
            return;
          }
        });
        if (!config.pair) offPairMatches++;
        if (g.phase === PHASES.DEAL_OVER) step(g);
      }
    }
  }
  ok(declared > 30 && held > 10, `${declared} pairs declared, ${held} held past their moment`);
  ok(helps > 10 && hurts > 10, `${helps} helped the bidders, ${hurts} raised the bid against them`);
  ok(clamped > 0, `${clamped} were clamped at the edge of the range`);

  // The window: a pair declared before the reveal, or after the next card has
  // been played, is refused. Built by hand, so the moment is exact.
  {
    const pack = buildPack();
    const g = newTable(DEFAULT_CONFIG, { shuffle: fixedPack(pack) });
    g.startMatch('p0', 0);
    settle(g);
    const holder = [0, 1, 2, 3].find((s) => g.hands[s].includes('KS') && g.hands[s].includes('QS'));
    ok(holder !== undefined, 'the unshuffled pack puts K and Q of spades in one hand');
    eq(g.declarePair(IDS[holder], 0).ok, false, 'the pair cannot be declared in the auction');
    eq(g.declarePair(IDS[holder], 0).error, 'not playing right now', 'and says why');
  }
}

// ===========================================================================
section('The engine: double and redouble');
// ===========================================================================
{
  let doubled = 0, redoubled = 0, offered = 0;
  for (const config of ALL_CONFIGS) {
    for (let m = 0; m < 10; m++) {
      const g = newTable(config);
      g.startMatch('p0', 0);
      for (let d = 0; d < 3 && g.phase !== PHASES.MATCH_OVER; d++) {
        playDeal(g, RANDOM_POLICY, (e) => {
          if (e.phase !== PHASES.DECLARE) return;
          const stage = e.declare.stage;
          ok(stage !== 'double' || config.double, 'no doubling stage when doubling is off');
          ok(stage !== 'redouble' || config.double, 'and no redoubling');
          ok(stage !== 'single' || config.singleHand, 'no single-hand stage when it is off');
          if (stage === 'double') {
            offered++;
            same(e.declare.order, seatsFrom(nextSeat(e.bidder)).filter((s) => !sameTeam(s, e.bidder)),
              'the opponents are offered the double, the one on the bidder\'s right first');
            eq(e.single, null, 'never in a single-hand deal');
          }
          if (stage === 'redouble') {
            ok(e.declare.order.every((s) => sameTeam(s, e.bidder)), 'only the bidding side may redouble');
            eq(e.level, 1, 'and only once doubled');
          }
        });
        const rec = g.history[g.history.length - 1];
        if (rec && !rec.thrownIn) {
          eq(Math.abs(rec.delta), rec.single ? SINGLE_HAND_STAKE : 2 ** rec.level, 'the deal paid its stake times 2^level');
          if (rec.level === 1) doubled++;
          if (rec.level === 2) redoubled++;
          if (!config.double) eq(rec.level, 0, 'doubling off: never doubled');
        }
        if (g.phase === PHASES.DEAL_OVER) step(g);
      }
    }
  }
  ok(offered > 50 && doubled > 10 && redoubled > 5, `doubling offered ${offered} times; ${doubled} doubled, ${redoubled} redoubled deals scored`);
}

// ===========================================================================
section('The engine: single hand — three-card tricks, the skipped seat, the early end');
// ===========================================================================
{
  let singles = 0, won = 0, lostEarly = 0;
  const SINGLE_POLICY = { ...RANDOM_POLICY, declare: (g, seat, options) => (options[0] === 'single' && coin(0.4) ? 'single' : (coin(0.3) ? options[0] : 'pass')) };
  for (const config of ALL_CONFIGS.filter((c) => c.singleHand)) {
    for (let m = 0; m < 25; m++) {
      const g = newTable(config);
      g.startMatch('p0', 0);
      for (let d = 0; d < 3 && g.phase !== PHASES.MATCH_OVER; d++) {
        let outHand = null;
        playDeal(g, SINGLE_POLICY, (e) => {
          if (!e.single || e.phase !== PHASES.PLAY) return;
          const { seat, out } = e.single;
          if (outHand === null) {
            outHand = e.hands[out].slice();
            eq(e.leadSeat, seat, 'the declarer leads');
            eq(e.indicator, null, 'the indicator went back to the bidder\'s hand');
            ok(e.hands.every((h, s) => s === out || h.length + e.plays.filter((p) => p.seat === s).length === HAND_SIZE - e.trickIndex),
              'every playing hand is whole again');
          }
          same(e.hands[out], outHand, 'the partner\'s hand sits out untouched');
          ok(e.publicState().seats[out].sittingOut, 'and the table is told it sits out');
          ok(e.plays.every((p) => p.seat !== out), 'it never plays to a trick');
          ok(e.tricks.every((t) => t.plays.length === SEATS - 1), 'tricks are three cards');
          eq(e.publicState().trump, null, 'there is no trump');
          eq(e.trumpSuit, null, 'not even in the engine — a played card can never be a trump');
          if (e.sweepAt === null) {
            const p = e.privateStateFor(IDS[e.turnSeat]);
            ok(!p.canCall, 'nobody can call for a trump that does not exist');
            eq(e.callTrump(IDS[e.turnSeat], 0).ok, false, 'and the engine refuses it');
          }
          eq(e.playCard(IDS[out], e.hands[out][0], 0).ok, false, 'the sitting-out seat cannot play');
        });
        const rec = g.history[g.history.length - 1];
        if (rec && rec.single) {
          singles++;
          eq(rec.level, 0, 'a single hand is never doubled');
          eq(rec.trump, null, 'and the hidden trump is never revealed by it');
          if (rec.made) { won++; eq(rec.delta, SINGLE_HAND_STAKE, `all eight tricks: +${SINGLE_HAND_STAKE}`); eq(rec.tricksPlayed, HAND_SIZE, 'all eight were played'); }
          else {
            eq(rec.delta, -SINGLE_HAND_STAKE, `a lost trick: −${SINGLE_HAND_STAKE}`);
            // It ended AT the first lost trick: every trick before it was won.
            const swept = g.tricks;
            eq(swept[swept.length - 1].winner !== rec.single.seat, true, 'the last trick played is the one that was lost');
            ok(swept.slice(0, -1).every((t) => t.winner === rec.single.seat), 'and every one before it was won — the deal ends at once');
            if (rec.tricksPlayed < HAND_SIZE) lostEarly++;
          }
          eq(rec.bidTeam, teamOf(rec.single.seat), 'only the declarer\'s side moves');
        }
        if (g.phase === PHASES.DEAL_OVER) step(g);
      }
    }
  }
  ok(singles > 30 && lostEarly > 20, `${singles} single hands, ${won} won, ${lostEarly} ended early`);
}

// ===========================================================================
section('The engine: a toggle that is off is unreachable');
// ===========================================================================
{
  // Every intent that belongs to a toggle, tried at every state of random
  // deals with that toggle off. Each must be refused, and refused WITHOUT
  // TOUCHING ANYTHING.
  const BY_TOGGLE = {
    pair: [(g, id) => g.declarePair(id, 0)],
    double: [(g, id) => g.double(id, 0), (g, id) => g.redouble(id, 0)],
    singleHand: [(g, id) => g.singleHand(id, 0)],
    seventh: [(g, id) => g.chooseSeventh(id, 0)],
  };
  let tries = 0;
  for (const key of TOGGLES) {
    for (const config of ALL_CONFIGS.filter((c) => !c[key])) {
      const g = newTable(config);
      g.startMatch('p0', 0);
      playDeal(g, RANDOM_POLICY, (e) => {
        const snap = JSON.stringify(e.serialize());
        for (const fn of BY_TOGGLE[key]) {
          for (const id of IDS) {
            const r = fn(e, id);
            tries++;
            if (r.ok) { failed++; console.error(`  ✗ FAIL: ${key} is off and an intent for it was accepted in ${e.phase}`); }
            else passed++;
          }
        }
        eq(JSON.stringify(e.serialize()), snap, `${key} off: the refused intents changed nothing`);
        if (e.declare) ok(!(key === 'double' && /double/.test(e.declare.stage)) && !(key === 'singleHand' && e.declare.stage === 'single'),
          `${key} off: its stage never opens`);
        if (key === 'seventh') ok(e.trumpMode !== 'seventh', 'seventh off: never the seventh card');
        if (key === 'pair') eq(e.pair, null, 'pair off: never a pair');
      });
    }
  }
  ok(tries > 5000, `${tries} intents for switched-off toggles, all refused`);

  // DEFENCE IN DEPTH, tested rather than assumed. The phases above never
  // open for a switched-off toggle, so the methods' own toggle checks are
  // never what refuses in a real game. Here the state is FORGED — a snapshot
  // with the stage open and the toggle off, the kind a corrupt or hostile
  // restore could produce — and each method must still say no on its own.
  {
    const g = newTable(ALL_CONFIGS[0]);
    g.startMatch('p0', 0);
    settle(g);
    g.placeBid(IDS[g.turnSeat], MIN_BID, 0);
    while (g.phase === PHASES.AUCTION) g.passBid(IDS[g.turnSeat], 0);
    const b = g.bidder;
    g.chooseTrump(IDS[b], g.hands[b][0], 0);
    settle(g);
    const forge = (stage, order) => {
      const snap = g.serialize();
      snap.phase = PHASES.DECLARE;
      snap.declare = { stage, order, at: 0 };
      snap.turnSeat = order[0];
      const f = new GameEngine();
      f.restore(snap);
      IDS.forEach((id, i) => f.addPlayer(id, 'x', { clientId: `client-${i}-0123456789` }));
      return f;
    };
    const opp = nextSeat(b);
    const f1 = forge('single', [opp]);
    eq(f1.singleHand(IDS[opp], 0).error, 'single hand is off in this game', 'a forged single-hand stage is still refused by the method');
    const f2 = forge('double', [opp]);
    eq(f2.double(IDS[opp], 0).error, 'doubling is off in this game', 'a forged doubling stage is still refused');
    const f3 = forge('redouble', [b]);
    eq(f3.redouble(IDS[b], 0).error, 'doubling is off in this game', 'and a forged redouble');
    const f4 = forge('single', [opp]);
    f4.phase = PHASES.PLAY; f4.revealed = true; f4.pairWindow = { team: teamOf(opp), trickIndex: 0 };
    eq(f4._pairBlocker(opp), 'the pair is off in this game', 'and a forged pair window is still refused');

    // The same for the pair's own rules: a window forged open BEFORE the
    // reveal, or after a pair has been declared, is refused by the method.
    const t = suitOf(f4.trumpCard);
    const f5 = forge('single', [opp]);
    f5.config = normalizeConfig({ ...f5.config, pair: true });
    f5.phase = PHASES.PLAY; f5.revealed = false; f5.pairWindow = { team: teamOf(opp), trickIndex: 0 };
    f5.hands[opp] = [`K${t}`, `Q${t}`, ...f5.hands[opp].filter((c) => c !== `K${t}` && c !== `Q${t}`).slice(0, 5)];
    eq(f5._pairBlocker(opp), 'the pair can be declared only after trump is revealed', 'a forged pre-reveal window is refused');
    f5.revealed = true;
    eq(f5._pairBlocker(opp), null, 'and the same state revealed is accepted — so the refusal above was about the reveal');
    f5.pair = { seat: opp, team: teamOf(opp), from: 16, to: 20 };
    eq(f5._pairBlocker(opp), 'the pair has already been declared this deal', 'and a second pair in a forged window is refused');
  }

  // Both declaration toggles off: the DECLARE phase is never entered at all.
  let walked = 0;
  for (const config of ALL_CONFIGS.filter((c) => !c.singleHand && !c.double)) {
    const g = newTable(config);
    g.startMatch('p0', 0);
    playDeal(g, RANDOM_POLICY, (e) => { walked++; ok(e.phase !== PHASES.DECLARE, 'no declarations window when both are off'); });
  }
  ok(walked > 50, `${walked} states walked with both declaration toggles off`);
}

// ===========================================================================
section('The engine: scoring a deal from the public record');
// ===========================================================================
{
  let deals = 0, made = 0, missed = 0, negatives = 0, matches = 0;
  for (const config of ALL_CONFIGS) {
    for (let m = 0; m < 4; m++) {
      let prev = [0, 0];
      const seenDeals = new Set();
      const g = playMatch(config, RANDOM_POLICY, (e) => {
        if (!e.history.length) return;
        const rec = e.history[e.history.length - 1];
        // onState fires more than once per state; each record is scored once.
        if (seenDeals.has(rec.deal)) return;
        seenDeals.add(rec.deal);
        if (rec.thrownIn) { same(rec.gamePoints, prev, 'a thrown-in deal scores nothing'); return; }
        deals++;
        same(rec.cardPoints, pointsBySide(e.tricks), 'the record\'s card points are the tricks\' points');
        if (!rec.single) {
          eq(rec.cardPoints[0] + rec.cardPoints[1], PACK_POINTS, 'an ordinary deal accounts for every point in the pack');
          eq(rec.made, rec.cardPoints[rec.bidTeam] >= rec.finalBid, 'made iff the bidding side reached the final bid');
          eq(rec.finalBid, rec.pair ? rec.pair.to : rec.bid, 'the final bid is the bid, moved by any pair');
        }
        if (rec.made) made++; else missed++;
        const moved = [rec.gamePoints[0] - prev[0], rec.gamePoints[1] - prev[1]];
        eq(moved[rec.bidTeam], rec.delta, 'the bidding side moved by the delta');
        eq(moved[1 - rec.bidTeam], 0, 'and the other side did not move at all');
        if (rec.gamePoints.some((n) => n < 0)) negatives++;
        prev = rec.gamePoints.slice();
      });
      if (g.phase === PHASES.MATCH_OVER) {
        matches++;
        const o = g.outcome;
        ok(g.gamePoints[o.winner] >= MATCH_TARGET || g.gamePoints[o.loser] <= -MATCH_TARGET, 'the match ended on a crossed line');
        // It ended at the FIRST crossing: no earlier deal had crossed one.
        const scored = g.history.filter((r) => !r.thrownIn);
        ok(scored.slice(0, -1).every((r) => !matchOutcome(r.gamePoints).over), 'and not a deal later than it should have');
        same(g.publicState().outcome, o, 'and the outcome is public');
      }
    }
  }
  ok(deals > 200 && made > 30 && missed > 30, `${deals} deals scored: ${made} made, ${missed} missed`);
  ok(negatives > 50, `${negatives} deals left a side on negative game points — routine, as the brief says`);
  ok(matches > 30, `${matches} random matches played to ±${MATCH_TARGET}`);
}

// ===========================================================================
section('The engine: the FINAL bid is what is scored — the pair\'s gap, exactly');
// ===========================================================================
//
// A random match almost never lands the bidding side's card points in the gap
// a pair opened, so the property "made iff points ≥ the final bid" can hold
// over thousands of deals while the engine scores the ORIGINAL bid. So the gap
// is built by hand: the last trick of a deal forged on the table, the tricks
// arranged so the bidding side holds a chosen number of points, and the
// sweep left to the engine.
{
  /** Eight tricks from a shuffled pack, with the bidding side taking exactly
   *  `target` points. Searches the 256 ways of assigning tricks to sides. */
  const rigTricks = (bidder, target) => {
    for (let tries = 0; tries < 200; tries++) {
      const pack = shuffle(buildPack());
      const tricks = [];
      for (let t = 0; t < HAND_SIZE; t++) tricks.push(pack.slice(t * SEATS, t * SEATS + SEATS));
      const pts = tricks.map((t) => pointsIn(t));
      for (let mask = 0; mask < 1 << HAND_SIZE; mask++) {
        let sum = 0;
        for (let t = 0; t < HAND_SIZE; t++) if (mask & (1 << t)) sum += pts[t];
        if (sum !== target) continue;
        return tricks.map((cards, t) => ({
          plays: cards.map((code, k) => ({ seat: seatsFrom(bidder)[k], code, trump: false })),
          winner: mask & (1 << t) ? bidder : nextSeat(bidder),
        }));
      }
    }
    throw new Error(`rigTricks: no split gives ${target}`);
  };

  const forgeLastTrick = ({ bid, finalBid, bidPoints, level = 0 }) => {
    const g = newTable(DEFAULT_CONFIG);
    g.startMatch('p0', 0);
    settle(g);
    const bidder = g.turnSeat;
    const tricks = rigTricks(bidder, bidPoints);
    const last = tricks[HAND_SIZE - 1];
    const snap = g.serialize();
    Object.assign(snap, {
      phase: PHASES.PLAY, bidder, bid, finalBid, level,
      trumpMode: 'concealed', trumpCard: last.plays[0].code, indicator: null, revealed: true,
      pair: finalBid !== bid ? { seat: bidder, team: teamOf(bidder), from: bid, to: finalBid } : null,
      hands: [[], [], [], []], stock: [],
      tricks: tricks.slice(0, -1), plays: last.plays,
      trickIndex: HAND_SIZE - 1, lastTrick: { ...last, card: last.plays[0].code, points: pointsIn(last.plays.map((p) => p.code)), trickIndex: HAND_SIZE - 1 },
      sweepAt: 0, pointsWon: [0, 0],
    });
    const f = new GameEngine();
    f.restore(snap);
    f.tick(TRICK_PAUSE_MS);
    return f;
  };

  // The bidders' own pair dropped 20 to 16, and they took 18: made.
  {
    const f = forgeLastTrick({ bid: 20, finalBid: 16, bidPoints: 18 });
    eq(f.phase, PHASES.DEAL_OVER, 'the forged last trick sweeps into the deal-over screen');
    const rec = f.history[f.history.length - 1];
    eq(rec.cardPoints[rec.bidTeam], 18, 'the bidding side took 18');
    eq(rec.made, true, '18 makes a bid that the pair moved down to 16 — though it would miss the 20 bid');
    eq(rec.delta, 1, 'and scores +1');
  }
  // The opponents' pair raised 20 to 24, and the bidders took 22: missed.
  {
    const f = forgeLastTrick({ bid: 20, finalBid: 24, bidPoints: 22 });
    const rec = f.history[f.history.length - 1];
    eq(rec.made, false, '22 misses a bid the opponents\' pair raised to 24 — though it would make the 20 bid');
    eq(rec.delta, -1, 'and scores −1');
  }
  // Doubled and redoubled, from the same forged table.
  {
    const f = forgeLastTrick({ bid: 20, finalBid: 20, bidPoints: 19, level: 2 });
    eq(f.history[f.history.length - 1].delta, -4, 'redoubled and one short: −4');
    const g = forgeLastTrick({ bid: 20, finalBid: 20, bidPoints: 20, level: 1 });
    eq(g.history[g.history.length - 1].delta, 2, 'doubled and exactly made: +2');
  }
}

// ===========================================================================
section('The engine: rejecting an action changes nothing');
// ===========================================================================
{
  let refusals = 0;
  const WRONG = [
    (g) => g.placeBid(IDS[(g.turnSeat + 1) % SEATS], MIN_BID, 0),
    (g) => g.placeBid(IDS[g.turnSeat], 3, 0),
    (g) => g.passBid(IDS[(g.turnSeat + 2) % SEATS], 0),
    (g) => g.chooseTrump(IDS[(g.turnSeat + 1) % SEATS], 'JS', 0),
    (g) => g.chooseTrump(IDS[g.turnSeat], 'XX', 0),
    (g) => g.playCard(IDS[(g.turnSeat + 1) % SEATS], g.hands[(g.turnSeat + 1) % SEATS][0] || 'JS', 0),
    (g) => g.playCard(IDS[g.turnSeat], g.hands[(g.turnSeat + 1) % SEATS][0] || 'JS', 0),
    (g) => g.callTrump(IDS[(g.turnSeat + 1) % SEATS], 0),
    (g) => g.passDeclare(IDS[(g.turnSeat + 1) % SEATS], 0),
    (g) => g.nextDeal('p1', 0),
    (g) => g.setConfig('p0', { pair: false }),
    (g) => g.startMatch('p0', 0),
    (g) => g.addBot('p0'),
    (g) => g.playCard('nobody', 'JS', 0),
  ];
  for (let m = 0; m < 30; m++) {
    const g = newTable(pick(ALL_CONFIGS));
    g.startMatch('p0', 0);
    playDeal(g, RANDOM_POLICY, (e) => {
      const fn = pick(WRONG);
      const snap = JSON.stringify(e.serialize());
      const r = fn(e);
      if (r.ok) return;   // some "wrong" moves are right by coincidence; only refusals are tested
      refusals++;
      ok(typeof r.error === 'string' && r.error.length > 3, 'a refusal says why');
      eq(JSON.stringify(e.serialize()), snap, `a refused action changed nothing (${r.error})`);
    });
  }
  ok(refusals > 500, `${refusals} refusals, none of which moved the engine`);
}

// ===========================================================================
section('The engine: serialize, restore, and a rejoin that brings it all back');
// ===========================================================================
{
  // A restored engine plays on to exactly the same result as the original,
  // given the same choices.
  let replays = 0;
  for (let m = 0; m < 40; m++) {
    const config = pick(ALL_CONFIGS);
    const g = newTable(config);
    g.startMatch('p0', 0);
    const stop = 5 + randInt(40);
    for (let i = 0; i < stop && g.phase !== PHASES.DEAL_OVER; i++) step(g);
    const copy = cloneEngine(g);
    ok(copy.serialize().hands !== g.serialize().hands, 'the copy owns its arrays');
    const at = prng;
    playDeal(g);
    const finalA = JSON.stringify({ h: g.history, gp: g.gamePoints });
    seed(at);
    playDeal(copy);
    eq(JSON.stringify({ h: copy.history, gp: copy.gamePoints }), finalA, 'a restored deal plays out identically');
    replays++;
  }
  ok(replays === 40, `${replays} deals replayed from a snapshot`);

  // History records are sealed, through restore too.
  {
    const g = playMatch(DEFAULT_CONFIG, RANDOM_POLICY, null, 3);
    const rec = g.history.find((r) => !r.thrownIn);
    ok(rec && Object.isFrozen(rec) && Object.isFrozen(rec.gamePoints), 'a deal record is frozen all the way down');
    const back = cloneEngine(g);
    const rec2 = back.history.find((r) => !r.thrownIn);
    ok(Object.isFrozen(rec2) && Object.isFrozen(rec2.cardPoints), 'and so is one that came back through JSON');
  }

  // REJOIN MID-MATCH: the scoreboard, the hand, and — for the bidder — the
  // trump they chose.
  {
    let rejoins = 0, bidders = 0;
    for (let m = 0; m < 60; m++) {
      const g = newTable(pick(ALL_CONFIGS.filter((c) => !c.seventh)));
      g.startMatch('p0', 0);
      // Play a deal or two, then stop somewhere after the trump was chosen.
      for (let d = 0; d < 1 + randInt(2) && g.phase !== PHASES.MATCH_OVER; d++) { playDeal(g); if (g.phase === PHASES.DEAL_OVER) step(g); }
      let guard = 0;
      while (!(g.phase === PHASES.PLAY && g.indicator && !g.revealed) && g.phase !== PHASES.MATCH_OVER && guard++ < 300) {
        if (g.phase === PHASES.DEAL_OVER) step(g); else step(g, { ...RANDOM_POLICY, call: () => false });
      }
      if (g.phase !== PHASES.PLAY) continue;
      const seat = g.bidder;
      const before = { priv: g.privateStateFor(IDS[seat]), pub: g.publicState() };
      // The phone dies. A NEW connection id, the SAME ticket.
      g.disconnect(IDS[seat]);
      ok(!g.seats[seat].connected, 'the bidder is marked away');
      const r = g.addPlayer('newconn', 'whatever', { clientId: `client-${seat}-0123456789` });
      ok(r.ok && r.reclaimed && r.seat === seat, 'the ticket reclaims the same seat');
      const after = g.privateStateFor('newconn');
      same(after.hand, before.priv.hand, 'with the same hand');
      eq(after.indicator, before.priv.indicator, 'and the bidder\'s face-down trump card');
      eq(after.knownTrump, before.priv.knownTrump, 'and the trump they chose');
      same(g.publicState().history, before.pub.history, 'and the whole scoreboard history');
      same(g.publicState().gamePoints, before.pub.gamePoints, 'and the game points');
      // A NAME IS NOT A TICKET.
      const thief = g.addPlayer('thief', g.seats[(seat + 1) % SEATS].name, { clientId: 'someone-else-entirely' });
      eq(thief.ok, false, 'a stranger typing a seated player\'s name gets nothing');
      rejoins++; bidders++;
      // Back to the original id so later checks can act for the seat.
      g.disconnect('newconn');
      g.addPlayer(IDS[seat], 'x', { clientId: `client-${seat}-0123456789` });
    }
    ok(rejoins > 30, `${rejoins} mid-deal rejoins, ${bidders} of them the bidder holding a concealed trump`);
  }

  // The host reloads: restore() brings back a bidder's concealed trump to a
  // seat that reclaims by ticket.
  {
    const g = newTable(DEFAULT_CONFIG);
    g.startMatch('p0', 0);
    settle(g);
    g.placeBid(IDS[g.turnSeat], 20, 0);
    while (g.phase === PHASES.AUCTION) g.passBid(IDS[g.turnSeat], 0);
    const b = g.bidder;
    const card = g.hands[b][1];
    g.chooseTrump(IDS[b], card, 0);
    settle(g);
    const back = cloneEngine(g);
    ok(back.seats.every((s) => !s.connected), 'after a restore everybody is away until they say otherwise');
    back.addPlayer('again', 'x', { clientId: `client-${b}-0123456789` });
    eq(back.privateStateFor('again').indicator, card, 'the bidder who comes back sees their trump card again');
  }

  // LEAVE is not DISCONNECT, and both reclaim the same way.
  {
    const g = newTable(DEFAULT_CONFIG);
    g.startMatch('p0', 0);
    g.disconnect('p2', { left: true });
    ok(g.seats[2].left && !g.seats[2].connected, 'a goodbye marks the seat as left');
    g.disconnect('p3', { left: 'yes' });
    ok(!g.seats[3].left, 'and only a real true does — a stray truthy value is a disconnect');
    g.addPlayer('p2b', 'x', { clientId: 'client-2-0123456789' });
    ok(!g.seats[2].left && g.seats[2].connected, 'and coming back clears it');
  }
}

// ###########################################################################
//
//  CHECKPOINT 5 — THE WIRE
//
// ###########################################################################

// Junk, of every shape a hostile or confused peer can produce.
const JUNK = [
  undefined, null, true, false, 0, -1, 1.5, NaN, Infinity, '', ' ', 'x'.repeat(70000),
  '__proto__', 'constructor', 'toString', [], [1, 2], {}, { type: 'x' }, () => 1,
  Object.create(null), new Date(0), /re/, Symbol.for ? 'sym' : 'sym', 16, 28, 29, 15, '16', 'JS', 'JX', 'jS',
  { __proto__: { evil: true } }, { length: 3 }, new Uint8Array(4), new ArrayBuffer(8),
];

// ===========================================================================
section('Guards: every one returns a value or null, and never throws');
// ===========================================================================
{
  const GUARDS = { validEnvelope, validClientId, validPlayerId, validCardCode, validSeat, validBid, validName, validConfigPatch, validPublicState, validPrivateState, decodePeerFrame };
  let calls = 0;
  for (const [name, fn] of Object.entries(GUARDS)) {
    for (const j of JUNK) {
      let r, threw = false;
      try { r = fn(j); } catch (_) { threw = true; }
      ok(!threw, `${name} does not throw on ${typeof j}`);
      ok(r === null || r === j || (name === 'decodePeerFrame' && typeof r === 'object'), `${name} returns the value or null`);
      calls++;
    }
  }
  ok(calls > 300, `${calls} junk inputs across ${Object.keys(GUARDS).length} guards`);
}

// ===========================================================================
section('Guards: the accept sets, swept rather than sampled');
// ===========================================================================
{
  // Every two-character string over a generous alphabet: exactly the 32 card
  // codes are accepted.
  const ALPHA = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz';
  const accepted = [];
  for (const a of ALPHA) for (const b of ALPHA) if (validCardCode(a + b) !== null) accepted.push(a + b);
  same(accepted.sort(), buildPack().sort(), 'validCardCode accepts exactly the 32 cards of the pack');
  eq(validCardCode('AH '), null, 'and nothing with padding');

  for (let n = -3; n <= SEATS + 3; n++) eq(validSeat(n), n >= 0 && n < SEATS ? n : null, `validSeat(${n})`);
  eq(validSeat('0'), null, 'a seat is a number, not a string');
  eq(validSeat('__proto__'), null, 'and never a prototype key');
  for (let n = 0; n <= MAX_BID + 5; n++) eq(validBid(n), n >= MIN_BID && n <= MAX_BID ? n : null, `validBid(${n})`);
  eq(validName('a'.repeat(MAX_RAW_NAME_LEN)), 'a'.repeat(MAX_RAW_NAME_LEN), 'a long name inside the bound is accepted for cleaning');
  eq(validName('a'.repeat(MAX_RAW_NAME_LEN + 1)), null, 'one over is refused');
  eq(validClientId('a'.repeat(32)), 'a'.repeat(32), 'a 128-bit hex client id is accepted');
  eq(validClientId('short'), null, 'a short one is not');
  eq(validClientId('bad id!'), null, 'nor one with a space');
  const many = {};
  for (let i = 0; i <= MAX_PATCH_KEYS; i++) many[`k${i}`] = true;
  eq(validConfigPatch(many), null, 'a patch with too many keys is refused before it is spread');
  same(validConfigPatch({ pair: false }), { pair: false }, 'a one-key patch is accepted');
  eq(validEnvelope({ type: 'x'.repeat(MAX_TYPE_LEN + 1) }), null, 'an over-long type is not a type');
  eq(validEnvelope([{ type: 'playCard' }]), null, 'an array is not a message');
}

// ===========================================================================
section('Guards: validSeat against the hole it actually closes');
// ===========================================================================
{
  // Reproduced against THIS engine, so the guard is shown to matter here and
  // not merely in judgement.
  const g = new GameEngine();
  g.addPlayer('p0', 'Asha', { clientId: 'client-0-0123456789' });
  g.addBot('p0');
  g.addBot('p0');
  const r = g.removeSeat('p0', '__proto__');
  ok(r.ok && !g.seats.some((s) => s.name === 'Asha'), 'UNGUARDED, the engine removes the owner when handed "__proto__"');
  eq(g.ownerId === null || g.seatOf(g.ownerId) === -1, true, 'and the room is left with nobody able to own it');

  const h = new GameEngine();
  h.addPlayer('p0', 'Asha', { clientId: 'client-0-0123456789' });
  h.addBot('p0');
  const via = applyGameIntent(h, 'p0', { type: 'removeSeat', seat: '__proto__' });
  eq(via.result.ok, false, 'through the dispatcher the same message is refused');
  eq(h.seats[0].name, 'Asha', 'and the owner keeps their seat');
}

// ===========================================================================
section('Guards: the rate limit, with time as a parameter');
// ===========================================================================
{
  const b = new TokenBucket({ capacity: 5, refillPerSec: 2, now: 0 });
  let okCount = 0;
  for (let i = 0; i < 10; i++) if (b.take(0)) okCount++;
  eq(okCount, 5, 'a burst is allowed up to the capacity');
  ok(!b.take(0), 'and then refused');
  ok(b.take(500), 'half a second later one token has come back');
  ok(!b.take(500), 'and only one');
  ok(!b.take(-10000), 'a clock stepping backwards refills nothing');
  ok(b.take(10000), 'and the bucket recovers going forward');
}

// ===========================================================================
section('Guards: decoding a frame off the wire');
// ===========================================================================
{
  same(decodePeerFrame('{"type":"passBid"}'), { type: 'passBid' }, 'a JSON message decodes');
  eq(decodePeerFrame('{"type":'), null, 'truncated JSON is dropped');
  eq(decodePeerFrame('[1,2]'), null, 'an array is dropped');
  eq(decodePeerFrame(`{"type":"x","pad":"${'y'.repeat(MAX_FRAME_BYTES)}"}`), null, 'an oversized frame is dropped before parsing');
  eq(decodePeerFrame(new ArrayBuffer(4)), null, 'binary is dropped');
  same(decodePeerFrame({ type: 'callTrump' }), { type: 'callTrump' }, 'an already-decoded object is checked the same way');
}

// ===========================================================================
section('Guards: what a client accepts back from its host');
// ===========================================================================
{
  // Every real state the engine produces is accepted, at every phase.
  let pubs = 0, privs = 0;
  for (const config of ALL_CONFIGS) {
    const g = newTable(config);
    ok(validPublicState(g.publicState()) !== null, 'a lobby public state is accepted');
    g.startMatch('p0', 0);
    playDeal(g, RANDOM_POLICY, (e) => {
      ok(validPublicState(e.publicState()) !== null, `the public state is accepted in ${e.phase}`);
      pubs++;
      for (const id of IDS) { ok(validPrivateState(e.privateStateFor(id)) !== null, `a private state is accepted in ${e.phase}`); privs++; }
    });
  }
  ok(pubs > 300 && privs > 1200, `${pubs} public and ${privs} private states accepted`);

  const good = newTable().publicState();
  const broken = [
    { ...good, seats: 7 }, { ...good, seats: [1, 2, 3, 4, 5] }, { ...good, plays: null },
    { ...good, log: 'x' }, { ...good, gamePoints: [0] }, { ...good, auction: null },
    { ...good, turnSeat: '__proto__' }, { ...good, turnSeat: -1 }, { ...good, config: [] },
  ];
  for (const b of broken) eq(validPublicState(b), null, 'a malformed public state is refused before render() sees it');
  eq(validPrivateState({ seat: 0, hand: new Array(HAND_SIZE + 1).fill({}) }), null, 'a hand longer than eight is refused');
  eq(validPrivateState({ seat: 9, hand: [] }), null, 'a seat that does not exist is refused');
  eq(validPrivateState({ seat: 0, hand: [], bidOptions: 'all' }), null, 'bid options that are not a list are refused');
}

// ===========================================================================
section('The dispatcher: the lists, and the whole engine surface');
// ===========================================================================
{
  const all = [...GAME_INTENTS, ...LOCAL_ONLY];
  eq(new Set(all).size, all.length, 'no method is in two lists');
  same([...SELF_GUARDED].sort(), [...OWNER_INTENTS].sort(), 'every owner intent says where it is gated');
  eq(new Set(GAME_INTENTS).size, PLAYER_INTENTS.length + OWNER_INTENTS.length, 'player and owner intents are disjoint');

  // EVERY public method of the engine is on one side of the wire or the
  // other. Accessors (the trumpSuit getter) are not methods.
  const proto = GameEngine.prototype;
  const methods = Object.getOwnPropertyNames(proto).filter((k) => {
    if (k === 'constructor' || k.startsWith('_')) return false;
    const d = Object.getOwnPropertyDescriptor(proto, k);
    return typeof d.value === 'function';
  });
  for (const m of methods) ok(all.includes(m), `GameEngine.${m} is either a wire intent or deliberately local`);
  for (const m of all) ok(methods.includes(m), `and ${m} is a real engine method`);
  ok(methods.length > 20, `${methods.length} public engine methods accounted for`);

  // The toggle map: every toggle has intents, every intent is a player intent.
  same(Object.keys(TOGGLE_INTENTS).sort(), [...TOGGLES].sort(), 'every toggle has its intents listed');
  // The seams are blank in v1.
  eq(SERVER_URL, '', 'SERVER_URL is blank');
  eq(SERVER_HEALTH, '', 'SERVER_HEALTH is blank');
  eq(serverConfigured(), false, 'and serverConfigured() is false — the shipping configuration');
  ok(SERVER_TIMEOUT_MS >= 10000 && SERVER_RETRIES >= 1, 'with a generous timeout and a retry, per the standing rule');
}

// ===========================================================================
section('The dispatcher: never throws, whatever arrives');
// ===========================================================================
{
  let sent = 0, unhandled = 0;
  const g = newTable();
  g.startMatch('p0', 0);
  settle(g);
  for (const type of [...GAME_INTENTS, 'nonsense', 'reset', 'restore', 'serialize', 'tick', 'resumeAsOwner', 'addPlayer']) {
    for (const j of JUNK) {
      for (const field of ['bid', 'code', 'patch', 'seat', 'name']) {
        let threw = false, r;
        try { r = applyGameIntent(g, 'p1', { type, [field]: j }, 0); } catch (e) { threw = true; console.error(e); }
        ok(!threw, `${type} with ${field}=${typeof j} does not throw`);
        sent++;
        if (!r.handled) unhandled++;
      }
    }
  }
  for (const j of JUNK) {
    let threw = false;
    try { applyGameIntent(g, 'p1', j, 0); } catch (_) { threw = true; }
    ok(!threw, 'a message that is not even an object does not throw');
  }
  ok(sent > 4000, `${sent} hostile messages dispatched`);
  // LOCAL_ONLY names are not dispatched, however they arrive.
  for (const type of LOCAL_ONLY) eq(applyGameIntent(g, 'p0', { type }, 0).handled, false, `'${type}' is not reachable from the wire`);
  ok(unhandled > 0, 'and unknown types fall through as unhandled');
}

// ===========================================================================
section('The dispatcher: owner intents refused from every other seat');
// ===========================================================================
{
  // Each owner intent, driven into a state where the OWNER's call would
  // succeed, is first tried from every non-owner seat and from a stranger.
  const fresh = () => {
    const g = new GameEngine();
    g.addPlayer('p0', 'Asha', { clientId: 'client-0-0123456789' });
    g.addPlayer('p1', 'Ben', { clientId: 'client-1-0123456789' });
    g.addBot('p0');
    return g;
  };
  const SETUPS = {
    setConfig: () => [fresh(), { type: 'setConfig', patch: { pair: false } }],
    addBot: () => [fresh(), { type: 'addBot' }],
    removeSeat: () => [fresh(), { type: 'removeSeat', seat: 2 }],
    startMatch: () => [fresh(), { type: 'startMatch' }],
    nextDeal: () => {
      const g = newTable();
      g.startMatch('p0', 0);
      playDeal(g);
      return [g, { type: 'nextDeal' }];
    },
  };
  for (const type of SELF_GUARDED) {
    ok(SETUPS[type], `there is a setup that makes '${type}' succeed for the owner`);
    for (const actor of ['p1', 'p2', 'p3', 'stranger']) {
      const [g, msg] = SETUPS[type]();
      const snap = JSON.stringify(g.serialize());
      const r = applyGameIntent(g, actor, msg, 0);
      eq(r.result.ok, false, `${type} from ${actor} is refused`);
      eq(JSON.stringify(g.serialize()), snap, 'and changes nothing');
    }
    const [g, msg] = SETUPS[type]();
    eq(applyGameIntent(g, 'p0', msg, 0).result.ok, true, `while the owner's ${type} succeeds — so the refusals were about the actor`);
  }
}

// ===========================================================================
section('The dispatcher: a switched-off toggle\'s intents, through the wire, in every state');
// ===========================================================================
{
  const MSG = { declarePair: { type: 'declarePair' }, double: { type: 'double' }, redouble: { type: 'redouble' }, singleHand: { type: 'singleHand' }, chooseSeventh: { type: 'chooseSeventh' } };
  let refused = 0;
  for (const key of TOGGLES) {
    for (const config of ALL_CONFIGS.filter((c) => !c[key])) {
      const g = newTable(config);
      g.startMatch('p0', 0);
      playDeal(g, RANDOM_POLICY, (e) => {
        for (const type of TOGGLE_INTENTS[key]) {
          for (const id of IDS) {
            const r = applyGameIntent(e, id, MSG[type], 0);
            if (r.handled && r.result.ok === false) refused++;
            else { failed++; console.error(`  ✗ FAIL: ${type} was accepted with ${key} off`); }
          }
        }
      });
    }
  }
  ok(refused > 3000, `${refused} toggle intents refused through the dispatcher`);
}

// ===========================================================================
section('The dispatcher: a peer with no seat is refused everything');
// ===========================================================================
{
  // A watcher is a connection with no seat. Every intent it could send, in
  // every state, is refused at source — and nothing it sends moves the game.
  let tried = 0;
  for (const config of [DEFAULT_CONFIG, ALL_CONFIGS[15]]) {
    const g = newTable(config);
    g.startMatch('p0', 0);
    playDeal(g, RANDOM_POLICY, (e) => {
      const snap = JSON.stringify(e.serialize());
      for (const type of GAME_INTENTS) {
        const msg = { type, bid: MIN_BID, code: e.hands[e.turnSeat][0] || 'JS', seat: 1, patch: { pair: false } };
        const r = applyGameIntent(e, 'peer:watcher', msg, 0);
        eq(r.result.ok, false, `a watcher's ${type} is refused in ${e.phase}`);
        tried++;
      }
      eq(JSON.stringify(e.serialize()), snap, 'and the watcher moved nothing');
      eq(e.privateStateFor('peer:watcher'), null, 'and has no private state to be sent');
    });
  }
  ok(tried > 900, `${tried} watcher intents refused`);
}

// ===========================================================================
section('The dispatcher: whole matches played through the wire');
// ===========================================================================
{
  // The random policy again, but every action framed as the message main.js
  // will send and dispatched — the way the host applies a peer's move.
  const wire = (g, id, msg) => {
    const r = applyGameIntent(g, id, msg, ++STEP_NOW);
    if (!r.handled || !r.result.ok) { failed++; console.error('  ✗ FAIL: a framed intent was refused', msg, r.result && r.result.error); }
  };
  let matches = 0;
  for (const config of ALL_CONFIGS) {
    const g = newTable(config);
    applyGameIntent(g, 'p0', { type: 'startMatch' }, 0);
    let guard = 0;
    while (g.phase !== PHASES.MATCH_OVER && guard++ < 6000) {
      settle(g);
      const id = IDS[g.turnSeat];
      const priv = g.privateStateFor(id);
      switch (g.phase) {
        case PHASES.AUCTION: {
          const b = RANDOM_POLICY.bid(g, g.turnSeat, priv);
          wire(g, id, b === null ? { type: 'passBid' } : { type: 'placeBid', bid: b });
          break;
        }
        case PHASES.TRUMP_CHOICE: {
          const t = RANDOM_POLICY.trump(g, g.turnSeat, priv);
          wire(g, id, t === 'seventh' ? { type: 'chooseSeventh' } : { type: 'chooseTrump', code: t });
          break;
        }
        case PHASES.DECLARE: {
          const c = RANDOM_POLICY.declare(g, g.turnSeat, priv.declareOptions);
          wire(g, id, { type: { single: 'singleHand', double: 'double', redouble: 'redouble', pass: 'passDeclare' }[c] });
          break;
        }
        case PHASES.PLAY: {
          const holder = IDS.find((x) => g.privateStateFor(x).canPair);
          if (holder) { wire(g, holder, { type: 'declarePair' }); break; }
          if (priv.canCall && coin(0.4)) { wire(g, id, { type: 'callTrump' }); break; }
          wire(g, id, { type: 'playCard', code: RANDOM_POLICY.card(g, g.turnSeat, priv) });
          break;
        }
        case PHASES.DEAL_OVER: wire(g, 'p0', { type: 'nextDeal' }); break;
        default: break;
      }
    }
    if (g.phase === PHASES.MATCH_OVER) matches++;
  }
  eq(matches, ALL_CONFIGS.length, `a whole match under each of the ${ALL_CONFIGS.length} configs, every move through the dispatcher`);
}

// ###########################################################################
//
//  CHECKPOINT 6 — THE BOT
//
// ###########################################################################

/** Freeze a view all the way down, so a bot that writes to its inputs throws
 *  instead of quietly changing what the next bot sees. */
function deepFreeze(o) {
  if (o && typeof o === 'object' && !Object.isFrozen(o)) {
    Object.freeze(o);
    for (const v of Object.values(o)) deepFreeze(v);
  }
  return o;
}

/**
 * Play a whole match with a bot in every seat, calling the pure choosers
 * directly. `observe(e, seat, pub, priv, intent)` sees every decision before
 * it is applied. Returns the engine.
 */
function botMatch(config, observe = null, { shuffle = null, maxActions = 20000 } = {}) {
  const g = newTable(config, shuffle ? { shuffle } : {});
  g.startMatch('p0', 0);
  let actions = 0;
  while (g.phase !== PHASES.MATCH_OVER && actions++ < maxActions) {
    settleWithPairs(g, observe);
    if (g.phase === PHASES.MATCH_OVER) break;
    if (g.phase === PHASES.DEAL_OVER) { g.nextDeal('p0', ++STEP_NOW); continue; }
    const seat = g.phase === PHASES.TRUMP_CHOICE ? g.bidder : g.turnSeat;
    if (!botAct(g, seat, observe)) { failed++; console.error('  ✗ FAIL: a bot had nothing to do on its turn in', g.phase); break; }
  }
  return g;
}

/** Bots holding the pair declare it, including during the sweep pause. */
function settleWithPairs(g, observe) {
  for (let n = 0; n < 100; n++) {
    if (g.phase === PHASES.PLAY) {
      for (let s = 0; s < SEATS; s++) {
        const priv = g.privateStateFor(IDS[s]);
        if (priv.canPair) botAct(g, s, observe);
      }
    }
    if (g.phase === PHASES.FIRST_FOUR) g.tick(g.phaseAt + FIRST_FOUR_MS);
    else if (g.phase === PHASES.LAST_FOUR) g.tick(g.phaseAt + LAST_FOUR_MS);
    else if (g.sweepAt !== null) g.tick(g.sweepAt + TRICK_PAUSE_MS);
    else return;
  }
}

let BOT_REFUSED = 0;
// Views are deep-frozen only while FREEZE_VIEWS is set — the purity section
// sets it. Freezing every view of the thousand-match soak cost most of a
// minute and proves nothing the purity section does not.
let FREEZE_VIEWS = false;
function botAct(g, seat, observe) {
  const pub = FREEZE_VIEWS ? deepFreeze(g.publicState()) : g.publicState();
  const priv = FREEZE_VIEWS ? deepFreeze(g.privateStateFor(IDS[seat])) : g.privateStateFor(IDS[seat]);
  const intent = chooseIntent(pub, priv);
  if (!intent) return false;
  if (observe) observe(g, seat, pub, priv, intent);
  const r = applyGameIntent(g, IDS[seat], intent, ++STEP_NOW);
  if (!r.result.ok) { BOT_REFUSED++; console.error('  ✗ FAIL: the engine refused a bot\'s', intent, r.result.error); failed++; }
  return true;
}

// ===========================================================================
section('Bot — sixteen configurations, two thousand matches, zero illegal moves');
// ===========================================================================
{
  let matches = 0, decisions = 0, deals = 0, made = 0, scored = 0, thrown = 0;
  const kinds = Object.create(null);
  const MATCHES_PER_CONFIG = 120;
  for (const config of ALL_CONFIGS) {
    for (let m = 0; m < MATCHES_PER_CONFIG; m++) {
      const g = botMatch(config, (e, seat, pub, priv, intent) => {
        decisions++;
        kinds[intent.type] = (kinds[intent.type] || 0) + 1;
      });
      if (g.phase === PHASES.MATCH_OVER) matches++;
      for (const r of g.history) {
        deals++;
        if (r.thrownIn) { thrown++; continue; }
        scored++;
        if (r.made) made++;
      }
    }
  }
  eq(matches, ALL_CONFIGS.length * MATCHES_PER_CONFIG, `${matches} all-bot matches finished, ${MATCHES_PER_CONFIG} under each of the 16 configurations`);
  eq(BOT_REFUSED, 0, `and the engine refused none of ${decisions} bot decisions`);
  // The intents a toggle owns are used only where it is on, and every one is
  // used somewhere.
  for (const t of ['placeBid', 'passBid', 'chooseTrump', 'chooseSeventh', 'double', 'redouble', 'passDeclare', 'callTrump', 'playCard', 'declarePair']) {
    ok(kinds[t] > 0, `bots used ${t} (${kinds[t] || 0} times)`);
  }
  const rate = made / scored;
  ok(rate > 0.5 && rate < 0.8, `bot contracts are made ${(rate * 100).toFixed(0)}% of the time — bids that mean something`);
  ok(thrown / deals < 0.25, `${((thrown / deals) * 100).toFixed(0)}% of deals thrown in — bots open when they should`);
  console.log(`  ${matches} matches, ${deals} deals, ${decisions} decisions; made ${(rate * 100).toFixed(1)}%, thrown in ${((thrown / deals) * 100).toFixed(1)}%`);
  console.log(`  ${Object.entries(kinds).map(([k, v]) => `${k} ${v}`).join(', ')}`);
}

// ===========================================================================
section('Bot — the choosers are pure');
// ===========================================================================
{
  // Same views in, same answer out, and the views are not touched: every
  // decision here is made on deep-frozen inputs, so a write would throw — and
  // then the same views are asked a second time.
  FREEZE_VIEWS = true;
  let asked = 0;
  for (let m = 0; m < 20; m++) {
    botMatch(pick(ALL_CONFIGS), (e, seat, pub, priv, intent) => {
      same(chooseIntent(pub, priv), intent, 'the same views give the same decision');
      asked++;
    }, { maxActions: 300 });
  }
  FREEZE_VIEWS = false;
  ok(asked > 3000, `${asked} decisions asked twice, on frozen views`);
}

// ===========================================================================
section('Bot — it plays for its partner');
// ===========================================================================
{
  let overtakeChances = 0, overtook = 0, feedChances = 0, fed = 0, throwChances = 0, threw = 0;
  let partnerOverbids = 0, overbidChances = 0, callsWithPartnerWinning = 0;
  const P = (e, seat, intent) => intent.type === 'playCard' && e.phase === PHASES.PLAY && e.plays.length > 0;
  for (const config of ALL_CONFIGS) {
    for (let m = 0; m < 12; m++) {
      botMatch(config, (e, seat, pub, priv, intent) => {
        // THE AUCTION: never outbids a partner who holds the high bid without
        // an estimate clearly above it.
        if (intent.type === 'placeBid' || intent.type === 'passBid') {
          const high = pub.auction.highSeat;
          if (high !== null && high === partnerOf(seat)) {
            overbidChances++;
            if (intent.type === 'placeBid') {
              partnerOverbids++;
              const calls = pub.auction.calls;
              const est = estimateSide(priv.hand.map((c) => c.code), {
                partnerBid: pub.auction.high, partnerPassed: false,
              });
              ok(Math.floor(est - BID_CAUTION) >= pub.auction.high + PARTNER_OVERBID_MARGIN,
                'a bot outbids its partner only with a hand clearly better than the partner\'s bid');
            }
          }
          return;
        }
        // THE CALL: never with the partner winning.
        if (intent.type === 'callTrump') {
          const w = winningPlay(e.plays);
          if (w && w.seat === partnerOf(seat)) callsWithPartnerWinning++;
          return;
        }
        if (!P(e, seat, intent)) return;
        const w = winningPlay(e.plays);
        const legal = priv.hand.filter((c) => c.legal).map((c) => c.code);
        const revealedTrump = pub.revealed ? pub.trump : null;
        const wins = (c) => wouldWin(e.plays, seat, c, playsAsTrump(c, pub.revealed, revealedTrump));
        const chosen = intent.code;
        if (w.seat === partnerOf(seat)) {
          // NEVER OVERTAKES THE PARTNER, when it has a choice.
          const nonOvertaking = legal.filter((c) => !wins(c));
          if (nonOvertaking.length) {
            overtakeChances++;
            if (wins(chosen)) overtook++;
          }
          // FEEDS POINTS when it is the last to play — the partner's trick is
          // safe — and has a point card that does not overtake.
          const last = e.plays.length === (e.single ? SEATS - 2 : SEATS - 1);
          if (last && nonOvertaking.some((c) => cardPoints(c) > 0)) {
            feedChances++;
            if (cardPoints(chosen) > 0) fed++;
          }
        } else if (!legal.some(wins)) {
          // An opponent is winning and it cannot be beaten: THROW A POINTLESS
          // CARD when there is one.
          if (legal.some((c) => cardPoints(c) === 0)) {
            throwChances++;
            if (cardPoints(chosen) === 0) threw++;
          }
        }
      });
    }
  }
  eq(overtook, 0, `it never overtook its partner — ${overtakeChances} chances`);
  ok(overtakeChances > 1000, 'and the chance came up often');
  ok(fed / feedChances > 0.85, `it fed its winning partner points ${fed} of ${feedChances} times when last to play`);
  eq(threw, throwChances, `it threw a pointless card to an opponent's trick every one of ${throwChances} times it could`);
  eq(callsWithPartnerWinning, 0, 'it never called for trump while its partner was winning the trick');
  ok(overbidChances > 100, `${overbidChances} times its partner held the bid; it overbid ${partnerOverbids} times, each with a reason`);
  ok(partnerOverbids / overbidChances < 0.2, `which is rarely (${partnerOverbids} of ${overbidChances})`);
}

// ===========================================================================
section('Bot — bidding on four cards, and the seventh card');
// ===========================================================================
{
  // Monotone: improving the trump suit or adding a side jack never lowers the
  // estimate.
  for (let n = 0; n < 400; n++) {
    const four = randomHand(BATCH);
    const e = estimateSide(four);
    ok(Number.isFinite(e), 'the estimate is a number');
    ok(estimateSide(four, { partnerBid: 17 }) > e, 'a partner who has bid raises it');
    ok(estimateSide(four, { partnerPassed: true }) < e, 'a partner who has passed lowers it');
  }
  ok(estimateSide(['JS', '9S', 'AS', 'TS']) > estimateSide(['7S', '8S', 'QS', 'KS']),
    'J-9-A-10 of a suit is worth more than K-Q-8-7 of it');
  ok(estimateSide(['JS', 'JH', '7C', '8D']) > estimateSide(['JS', '7H', '7C', '8D']), 'a side jack is worth something');
  eq(bestTrump(['JS', '9S', '7H', '8D']).suit, 'S', 'the best trump is the suit with the jack and nine');
  ok(trumpStrength(['JH', '9H'], 'H') > trumpStrength(['AH', 'TH'], 'H'), 'the jack and nine beat the ace and ten as trumps');

  // The bot chooses the suit it would bid on, and puts down its LOWEST card of
  // that suit so the jack and nine stay in hand.
  const priv = { hand: ['JS', '9S', '7S', 'KD'].map((code) => ({ code, legal: true })), trumpChoice: { seventh: false } };
  same(chooseTrump({}, priv), { code: '7S' }, 'it puts down the seven, keeping the jack and nine');
  const weak = { hand: ['JS', '7H', 'QC', 'KD'].map((code) => ({ code, legal: true })), trumpChoice: { seventh: true } };
  same(chooseTrump({}, weak), { seventh: true }, 'with no strong suit and the seventh card on offer, it takes the seventh');
  same(chooseTrump({}, { ...weak, trumpChoice: { seventh: false } }).seventh, undefined, 'and does not when it is not on offer');
  const strong = { hand: ['JS', '9S', 'AS', 'KD'].map((code) => ({ code, legal: true })), trumpChoice: { seventh: true } };
  ok(chooseTrump({}, strong).code, 'with a strong suit it chooses rather than gamble');
}

// ===========================================================================
section('Bot — single hand only on a hand that cannot lose');
// ===========================================================================
{
  ok(cannotLose(['JS', '9S', 'AS', 'TS', 'KS', 'JH', '9H', 'JD']), 'every suit held from the top cannot lose');
  ok(!cannotLose(['JS', 'AS', 'TS', 'KS', 'QS', 'JH', '9H', 'JD']), 'a missing nine in spades can lose a trick');
  ok(!cannotLose(['9S', '7S', 'JH', '9H', 'AH', 'TH', 'KH', 'QH']), 'a suit without its jack can lose');
  ok(!cannotLose([]), 'an empty hand is not a single hand');
  // As a property over random hands: whenever cannotLose says yes, leading
  // the hand top-down beats every card it does not hold.
  let yes = 0;
  for (let n = 0; n < 20000; n++) {
    const hand = randomHand(HAND_SIZE);
    if (!cannotLose(hand)) continue;
    yes++;
    for (const c of hand) {
      const beaten = buildPack().some((o) => !hand.includes(o) && suitOf(o) === suitOf(c) && rankValue(o) > rankValue(c));
      ok(!beaten, `${c} cannot be beaten by any card outside the hand`);
    }
  }
  // Built by hand too, because random eight-card hands that cannot lose are
  // vanishingly rare — which is the brief's point.
  const rigged = ['JS', '9S', 'AS', 'TS', 'KS', 'QS', '8S', '7S'];
  ok(cannotLose(rigged), 'the whole of a suit cannot lose');
  eq(chooseDeclare({ trumpMode: 'concealed' }, { declareOptions: ['single', 'pass'], hand: rigged.map((code) => ({ code })), indicator: null, isBidder: false }),
    'single', 'and a bot holding it declares single hand');
  eq(chooseDeclare({ trumpMode: 'seventh' }, { declareOptions: ['single', 'pass'], hand: rigged.slice(0, 7).map((code) => ({ code })), indicator: null, isBidder: true }),
    'pass', 'but not a seventh-card bidder, whose eighth card is one it has never seen');
  console.log(`  ${yes} of 20000 random hands could not lose`);

  // A rigged deal: the bot that holds all eight spades declares and wins.
  const pack = buildPack();
  // Deal order from seat 0 dealing: seat 3 first, then 2, 1, 0 — each batch.
  // Give seat 3 the eight spades: first block of each batch.
  const spades = pack.filter((c) => suitOf(c) === 'S');
  const rest = pack.filter((c) => suitOf(c) !== 'S');
  const rigPack = [...spades.slice(0, 4), ...rest.slice(0, 12), ...spades.slice(4), ...rest.slice(12)];
  const g = botMatch(ALL_CONFIGS.find((c) => c.singleHand && !c.double && !c.seventh && !c.pair), null,
    { shuffle: fixedPack(rigPack), maxActions: 60 });
  const rec = g.history.find((r) => r.single);
  ok(rec && rec.single.seat === 3, 'the bot holding every spade declared single hand');
  ok(rec && rec.made && rec.delta === SINGLE_HAND_STAKE, `and took all eight for +${SINGLE_HAND_STAKE}`);
}

// ===========================================================================
section('Bot — blind to a trump it is not entitled to know');
// ===========================================================================
//
// THE BRIEF'S PROOF, as specified: replay the same deal with the indicator's
// suit swapped, and check that every decision made before the reveal by a
// seat not entitled to know the trump is identical.
//
// The swap has to change the trump WITHOUT changing anything the compared
// seats can see — otherwise a different decision proves nothing. So one seat
// absorbs the swap, its moves are REPLAYED from the first run rather than
// chosen again, and it is the one seat not compared:
//
//   concealed  the bidder put down card X; the replay has them put down Y, one
//              of their other three cards, of a different suit. The bidder
//              absorbs it — they are entitled to know anyway.
//   seventh    the pack is rearranged so the bidder's seventh card trades
//              places with a card of a different suit from ONE OPPONENT's
//              second four. That opponent absorbs it, and the bidder — who
//              under seventh card does not know the trump either — is among
//              the seats compared.
//
// Comparison stops at the reveal, and at the first decision whose seat could
// see a different table: the first time the public state of the two runs
// differs, or a replayed move cannot be made.
{
  let deals = 0, compared = 0, seventhBidder = 0, mismatches = 0;

  const record = (config, pack, { force = null, script = null, absorber = null } = {}) => {
    const g = newTable(config, { shuffle: fixedPack(pack) });
    g.startMatch('p0', 0);
    const log = [];
    for (let k = 0; k < 300; k++) {
      settleWithPairs(g, null);
      if (g.phase === PHASES.DEAL_OVER || g.phase === PHASES.MATCH_OVER || g.dealIndex > 0 || g.revealed) break;
      const seat = g.phase === PHASES.TRUMP_CHOICE ? g.bidder : g.turnSeat;
      const pub = g.publicState();
      const priv = g.privateStateFor(IDS[seat]);
      let intent;
      if (g.phase === PHASES.TRUMP_CHOICE && force) intent = force;
      else if (script && seat === absorber && g.phase !== PHASES.AUCTION) intent = script[k] && script[k].intent;
      else intent = chooseIntent(pub, priv);
      if (!intent) break;
      log.push({ seat, phase: g.phase, intent, pub: JSON.stringify(pub), priv: JSON.stringify(priv) });
      // A clock of the run's OWN, so the two runs stamp the same phases with
      // the same times and their public states can be compared byte for byte.
      const r = applyGameIntent(g, IDS[seat], intent, k + 1);
      if (!r.result.ok) { log.pop(); break; }
    }
    return { g, log };
  };

  for (const config of ALL_CONFIGS.filter((c) => !c.singleHand)) {
    for (let m = 0; m < 30; m++) {
      const pack = shuffle(buildPack());
      const a = record(config, pack);
      const ga = a.g;
      if (ga.bidder === null || !ga.trumpCard) continue;
      const b = ga.bidder;
      const order = seatsFrom(nextSeat(ga.dealerSeat));
      let replay, absorber;
      if (ga.trumpMode === 'concealed') {
        const four = pack.slice(order.indexOf(b) * BATCH, (order.indexOf(b) + 1) * BATCH);
        const other = four.find((c) => suitOf(c) !== suitOf(ga.trumpCard));
        if (!other) continue;
        absorber = b;
        replay = record(config, pack, { force: { type: 'chooseTrump', code: other }, script: a.log, absorber });
      } else {
        const opp = nextSeat(b);
        const seventhAt = SEATS * BATCH + order.indexOf(b) * BATCH + 2;
        const oppBase = SEATS * BATCH + order.indexOf(opp) * BATCH;
        const swapAt = [0, 1, 2, 3].map((i) => oppBase + i).find((i) => suitOf(pack[i]) !== suitOf(pack[seventhAt]));
        if (swapAt === undefined) continue;
        const p2 = pack.slice();
        [p2[seventhAt], p2[swapAt]] = [p2[swapAt], p2[seventhAt]];
        absorber = opp;
        replay = record(config, p2, { script: a.log, absorber });
      }
      ok(suitOf(replay.g.trumpCard) !== suitOf(ga.trumpCard), 'the replay really has a different trump');
      deals++;
      const n = Math.min(a.log.length, replay.log.length);
      for (let i = 0; i < n; i++) {
        const x = a.log[i], y = replay.log[i];
        if (x.seat !== y.seat || x.phase !== y.phase || x.pub !== y.pub) break;
        if (x.seat === absorber || x.phase === PHASES.TRUMP_CHOICE) continue;
        // The compared seat sees the same table AND the same hand.
        eq(x.priv, y.priv, 'a compared seat\'s own view is identical in the two runs');
        compared++;
        if (ga.trumpMode === 'seventh' && x.seat === b) seventhBidder++;
        if (JSON.stringify(x.intent) !== JSON.stringify(y.intent)) {
          mismatches++;
          failed++;
          console.error(`  ✗ FAIL: seat ${x.seat} decided differently with the hidden trump swapped (${x.phase}):`, x.intent, y.intent);
        } else passed++;
      }
    }
  }
  ok(deals > 200, `${deals} deals replayed with the hidden trump swapped`);
  ok(compared > 2000, `${compared} decisions by seats not entitled to the trump compared`);
  ok(seventhBidder > 50, `including ${seventhBidder} by the bidder under seventh card`);
  eq(mismatches, 0, 'and none of them changed');
  console.log(`  ${deals} deals, ${compared} decisions compared, ${seventhBidder} of them a seventh-card bidder's`);
}

// ===========================================================================
section('Bot — the driver: the pacing, the grace, and a seat that left');
// ===========================================================================
{
  // One human and three bots: the match the brief says must work.
  const g = new GameEngine();
  g.addPlayer('p0', 'Asha', { clientId: 'client-0-0123456789' });
  g.startMatch('p0', 0);
  eq(g.seats.filter((s) => s.isBot).length, SEATS - 1, 'starting alone fills three seats with bots');
  ok(g.seats.every((s) => s.connected), 'and they are all present');
  ok(teamOf(0) === teamOf(2) && g.seats[2].isBot, 'the human\'s partner is a bot');

  const d = createBotDriver();
  let t = 0;
  settle(g);
  // Whoever is first to bid: if it is a bot it waits BOT_THINK_MS.
  while (g.turnSeat === 0 && g.phase === PHASES.AUCTION) { g.passBid('p0', t); }
  const calls = g.auction.calls.length;
  ok(!d.tick(g, t), 'a bot does not move the instant its turn arrives');
  ok(!d.tick(g, t + BOT_THINK_MS - 1), 'nor a moment before it has thought');
  ok(d.tick(g, t + BOT_THINK_MS), `it moves after ${BOT_THINK_MS}ms`);
  eq(g.auction.calls.length, calls + 1, 'and its move is in the auction');

  // A DROPPED human is waited for; a human who LEFT is not.
  const h = new GameEngine();
  IDS.forEach((id, i) => h.addPlayer(id, NAMES[i], { clientId: `client-${i}-0123456789` }));
  h.startMatch('p0', 0);
  settle(h);
  const seat = h.turnSeat;
  h.disconnect(IDS[seat]);
  const dd = createBotDriver();
  ok(!dd.tick(h, 0) && !dd.tick(h, BOT_THINK_MS), 'a dropped phone is not covered at a bot\'s pace');
  ok(!dd.tick(h, OFFLINE_GRACE_MS - 1), 'nor before the grace period');
  ok(dd.tick(h, OFFLINE_GRACE_MS), `it is covered after ${OFFLINE_GRACE_MS}ms`);
  ok(!h.seats[seat].isBot, 'COVERED, not converted: the seat is still a person\'s');

  const k = new GameEngine();
  IDS.forEach((id, i) => k.addPlayer(id, NAMES[i], { clientId: `client-${i}-0123456789` }));
  k.startMatch('p0', 0);
  settle(k);
  const ls = k.turnSeat;
  k.disconnect(IDS[ls], { left: true });
  const kd = createBotDriver();
  ok(!kd.tick(k, 0), 'a seat that LEFT is covered after a bot\'s pause —');
  ok(kd.tick(k, BOT_THINK_MS), 'not after the offline grace');
  ok(!k.seats[ls].isBot, 'and it too is COVERED, not converted');
  ok(k.publicState().seats[ls].isBot === false, 'the table still sees a person\'s seat');
  // And the ticket reclaims it, after either.
  ok(k.addPlayer('back', 'x', { clientId: `client-${ls}-0123456789` }).reclaimed, 'the same device reclaims the seat it left');
  ok(!k.seats[ls].left && k.seats[ls].connected && !k.seats[ls].isBot, 'and it is a person\'s again');
  ok(h.addPlayer('back2', 'x', { clientId: `client-${seat}-0123456789` }).reclaimed, 'and the dropped one reclaims too');

  // THE DRIVER'S OWN SOAK: one human who LEFT and three bots, every move
  // through createBotDriver() and nothing else, under all sixteen configs.
  botStats.refused = 0; botStats.fallbacks = 0;
  let finished = 0, ticks = 0;
  for (const config of ALL_CONFIGS) {
    for (let m = 0; m < 8; m++) {
      const e = new GameEngine();
      e.addPlayer('p0', 'Asha', { clientId: 'client-0-0123456789' });
      e.setConfig('p0', config);
      e.startMatch('p0', 0);
      e.disconnect('p0', { left: true });
      const drv = createBotDriver();
      let now = 0;
      for (let i = 0; i < 40000 && e.phase !== PHASES.MATCH_OVER; i++) {
        now += BOT_THINK_MS;
        e.tick(now);
        drv.tick(e, now);
        ticks++;
        if (e.phase === PHASES.DEAL_OVER) e.nextDeal('p0', now);
      }
      if (e.phase === PHASES.MATCH_OVER) finished++;
    }
  }
  eq(finished, ALL_CONFIGS.length * 8, `${finished} matches played by the driver alone, a left human covered throughout`);
  eq(botStats.refused, 0, 'the driver had no move refused');
  eq(botStats.fallbacks, 0, 'and never needed its fallback');
}

// ###########################################################################
//
//  SUMMARY
//
// ###########################################################################

console.log(`\n${passed} passed, ${failed} failed`);
if (failed) process.exit(1);

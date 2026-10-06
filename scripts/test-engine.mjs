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
// The renderer, and the DOM it renders into out here. ui.js never touches
// `document` itself — everything goes through util.js's el() and clear().
import { installDOM, walk, byClass, byTag, interactive, dump } from './domshim.mjs';
import {
  el, clear, score as fmtScore, delta as fmtDelta, plural,
  CODE_LENGTH, generateRoomCode, normalizeCode,
  loadName, saveName, loadCode, saveCode, clientId, announcementFor,
  saveSession, loadSession, clearSession, saveEngineSnapshot, loadEngineSnapshot, leftTable,
} from '../js/util.js';
import { render, seatPositions, SCREEN_SLOTS } from '../js/ui.js';
import {
  MAX_HOST_CONNS, MAX_WATCHERS, WATCHER, HOST_ID, peerIdForCode, playerIdForConn,
  createHost, joinHost, stateFrameFor, readStateFrame, rejectFrame, readRejectFrame,
  leaveFrame, hostLeftFrame,
} from '../js/net.js';
import { installPeerJS } from './peershim.mjs';
import {
  BOT_THINK_MS, OFFLINE_GRACE_MS, PARTNER_OVERBID_MARGIN, CALL_FOR_POINTS, BID_CAUTION,
  chooseBid, chooseTrump, chooseCall, chooseCard, chooseDeclare, chooseIntent,
  createBotDriver, botStats, estimateSide, bestTrump, trumpStrength, cannotLose,
} from '../js/bot.js';

import { readFileSync, readdirSync, writeFileSync, existsSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { createHash } from 'node:crypto';

const REPO = fileURLToPath(new URL('../', import.meta.url));
const readRepo = (rel) => readFileSync(REPO + rel, 'utf8');

/**
 * Every flat-bodied rule in a stylesheet, as { sel, body, at }.
 *
 * `at` is the at-rule prelude the rule sits inside — '' for a rule that always
 * applies, '@media (prefers-reduced-motion: reduce)' for one that does not.
 * Recording it is not decoration: the FIRST version of this walked the braces
 * with one regex, which flattens the nesting away, and the hand-geometry
 * section below then read `transform` off `.card-btn.sel .card` and got the
 * `none` from inside the reduced-motion block instead of the translateY from
 * the rule that normally applies. A parser that cannot tell "always" from
 * "sometimes" reports the last thing it saw and calls it the value.
 *
 * Comments are stripped first: this project's stylesheet quotes selectors at
 * length in its prose, and a parser that reads the prose finds rules that do
 * not exist.
 *
 * Up here rather than inside the seat-state section that first needed it,
 * because the hand-geometry section needs the same parse. A stylesheet parser
 * is exactly the kind of thing that gets copied into the second caller and
 * then improved in only one of the two.
 */
function cssRules(rel) {
  const src = readRepo(rel).replace(/\/\*[\s\S]*?\*\//g, '');
  const out = [];
  const stack = [];
  const brace = /[{}]/g;
  let from = 0, m;
  while ((m = brace.exec(src))) {
    const text = src.slice(from, m.index);
    from = m.index + 1;
    if (m[0] === '{') {
      // Whatever we were inside has a nested block, so it is a wrapper and not
      // a rule of its own.
      if (stack.length) stack[stack.length - 1].wrapper = true;
      stack.push({ head: text.trim(), wrapper: false });
    } else {
      const frame = stack.pop();
      if (!frame) continue; // stray '}': malformed CSS, and not this file's job
      if (!frame.wrapper) out.push({ sel: frame.head, body: text, at: stack.map((f) => f.head).join(' ') });
    }
  }
  return out;
}

/**
 * The last value `prop` is given by the rule whose selector is exactly `sel`.
 * Last, not first, because that is what the cascade does with two declarations
 * of the same property at the same specificity — reading the first would make
 * this disagree with the browser precisely when someone has overridden
 * something, which is when it matters.
 *
 * Conditional rules are skipped. A declaration inside @media is the value for
 * the readers that match the query, not the value; callers here are asking
 * what the layout is, and the answer has to be the one that does not depend on
 * who is looking.
 */
function cssDecl(rules, sel, prop) {
  let found = null;
  for (const r of rules) {
    if (r.sel !== sel || r.at) continue;
    for (const d of r.body.split(';')) {
      const m = d.match(/^\s*([\w-]+)\s*:\s*(.+?)\s*$/);
      if (m && m[1] === prop) found = m[2];
    }
  }
  return found;
}

/**
 * sw.js's three constants, obtained by EXECUTING the file rather than by
 * regex — a regex over source is a parser that does not report syntax errors.
 *
 * Up here beside readRepo rather than down in the shell section that used to
 * be its only caller, because --write-stamp needs it too. Two copies of "how
 * you get SHELL out of sw.js" is the same shape of defect as two copies of the
 * seal: they agree until one is updated and the other is not.
 *
 * Returns the parse error rather than asserting on it. One caller counts a
 * failure and carries on with empty constants; the other has to refuse to
 * write anything at all. Neither of those decisions belongs in here.
 */
function loadSwConsts() {
  const src = readRepo('sw.js');
  let factory = null;
  try {
    // eslint-disable-next-line no-new-func
    factory = new Function(
      'self', 'caches', 'fetch', 'Response',
      src + '\n; return { CACHE_NAME, SHELL, SHELL_STAMP };'
    );
  } catch (e) {
    return { src, error: e, CACHE_NAME: '', SHELL: [], SHELL_STAMP: '' };
  }
  // A throwaway instantiation purely to read the constants. The handlers it
  // registers are dropped; the real drive happens in the shell section.
  const consts = factory(
    { addEventListener() {}, location: { origin: 'https://x.test' }, clients: {} },
    {}, () => {}, class {}
  );
  return { src, error: null, ...consts };
}

/**
 * THE FINGERPRINT, in one place. sw.js names its cache after a hash of the
 * files it precaches, so a stale name is a returning visitor pinned to a build
 * that was fixed weeks ago — and the only way to check a fingerprint is to
 * recompute it.
 *
 * This function is the ONLY implementation of that hash in the repository, and
 * that is deliberate rather than tidy. The checker below and the --write-stamp
 * writer both call it, and had the writer been given its own copy the two
 * would have agreed right up until one of them learned something the other did
 * not — a new binary extension, a different separator — at which point the
 * writer would confidently paste a value the checker rejects. That is the same
 * defect as the two sealers in #26 and the hand-written handler lists in #27,
 * and the fix is the same one: derive it once, call it twice.
 *
 * Returns the counts alongside the digest because a hash of nothing is still a
 * hash. Both callers need to know the sweep found something before they
 * believe the twelve characters it produced.
 */
function shellStampOf(SHELL) {
  // './' and './index.html' are the same bytes from any static host; hashing
  // both would count the page twice and, worse, would make the stamp depend on
  // a listing decision rather than on content. Mapped and de-duplicated.
  // Sorted, so the order of the SHELL array — which is written for humans, in
  // dependency order — cannot change the answer.
  const paths = [...new Set(SHELL.map((p) => (p === './' ? './index.html' : p)))].sort();

  const BINARY = /\.(png|jpg|jpeg|ico|woff2?)$/;
  const h = createHash('sha256');
  let hashed = 0;
  let unreadable = 0;
  for (const p of paths) {
    let bytes;
    try { bytes = readFileSync(REPO + p.slice(2)); } catch (_) { unreadable++; continue; }
    // LINE ENDINGS NORMALISED for text. A checkout on Windows and a checkout
    // on Linux hold different bytes for the same commit, and without this the
    // suite would fail on one of them for a reason that has nothing to do with
    // the app. Binaries are hashed as-is — there are no line endings in a PNG,
    // only pixels that happen to be 0x0D.
    if (!BINARY.test(p)) bytes = Buffer.from(bytes.toString('utf8').replace(/\r\n/g, '\n'), 'utf8');
    // The path goes into the hash as well as the contents, with a separator, so
    // that renaming a file changes the stamp even when its bytes do not — and
    // so that two adjacent files cannot be concatenated into the same digest as
    // one longer file.
    h.update(p); h.update('\0'); h.update(bytes); h.update('\0');
    hashed++;
  }
  return { stamp: h.digest('hex').slice(0, 12), hashed, unreadable };
}

/** The one line --write-stamp is allowed to touch. */
const STAMP_ANCHOR = /^const SHELL_STAMP = '([0-9a-f]{12})';$/m;

/**
 * WHAT --write-stamp WOULD DO TO A GIVEN sw.js, decided without touching the
 * disk. Returns `{ refuse, stamp, hashed, unreadable, was, next }`, where
 * `refuse` is a reason string or null, and `next` is the complete new file
 * text or null if it refused.
 *
 * SPLIT OUT FROM THE WRITER SO THE SUITE CAN DRIVE IT. The guards below are
 * the entire reason a test runner is trusted with a write, and as long as they
 * lived inside `if (process.argv.includes(...))` nothing could reach them: the
 * suite never takes that branch, so deleting every one of them would have left
 * 121,000 assertions green and a writer that pastes a hash of an empty sweep
 * over the deploy blocker it was meant to fix. Untested safety code is
 * decoration, and it is the most dangerous kind because of how it reads.
 *
 * Pure, and takes the parsed file rather than reading it, so the suite can
 * hand it a two-anchor sw.js or a SHELL full of paths that do not exist —
 * inputs that cannot be produced any other way without damaging the working
 * tree to test the thing that protects it.
 */
function planStampWrite(sw) {
  const refuse = (why) => ({ refuse: why, stamp: null, hashed: 0, unreadable: 0, was: null, next: null });

  if (sw.error) return refuse(`sw.js does not parse — ${sw.error.message}`);
  if (!Array.isArray(sw.SHELL) || sw.SHELL.length === 0) return refuse('sw.js exports no usable SHELL');

  const { stamp, hashed, unreadable } = shellStampOf(sw.SHELL);
  // THE SAME PAIRING THE CHECKER USES, for a sharper reason. A hash over a
  // sweep that found nothing is a well-formed answer to the wrong question;
  // downstream of the checker that is a confusing failure, but downstream of
  // the writer it is a wrong value written into the file — and once written,
  // the checker agrees with it. The check and the fix cannot both be fooled by
  // the same bad input, so the fix has to be the more suspicious of the two.
  if (unreadable > 0) return refuse(`${unreadable} file(s) in SHELL could not be read off disk`);
  if (hashed < 20) return refuse(`the sweep covered only ${hashed} files — that is not the shell`);

  // The anchor has to be unique. A second occurrence means the file is not
  // shaped the way this assumes, and the honest response is to stop rather
  // than to edit whichever one happens to come first.
  const hits = sw.src.match(new RegExp(STAMP_ANCHOR.source, 'gm')) || [];
  if (hits.length !== 1) return refuse(`found ${hits.length} SHELL_STAMP declarations in sw.js, expected exactly 1`);

  return {
    refuse: null,
    stamp,
    hashed,
    unreadable,
    was: sw.src.match(STAMP_ANCHOR)[1],
    next: sw.src.replace(STAMP_ANCHOR, `const SHELL_STAMP = '${stamp}';`),
  };
}

/**
 * `node scripts/test-engine.mjs --write-stamp` — the one mode in which the
 * test runner writes to the repository.
 *
 * WHY THIS EXISTS. Every legitimate edit to a shell file makes the suite red
 * until somebody pastes twelve hex characters into sw.js. That is correct —
 * the stamp really is stale — but it costs a round trip on every change, and a
 * check that is red for a known and mechanical reason is a check people learn
 * to run last. Printing the answer was the first half of that fix; applying it
 * is the second.
 *
 * WHY IT IS FENCED THIS TIGHTLY. A test runner that can edit the code it
 * grades is exactly the tool you would build if you wanted a green suite that
 * means nothing, so the blast radius is cut down to the smallest thing that
 * still does the job:
 *
 *   - it runs HERE, above SCREENS and above every assertion, and exits. There
 *     is no path on which a run both writes a stamp and reports a pass count,
 *     so `npm test` cannot quietly repair what it was meant to catch. That the
 *     test script does not pass the flag is asserted in the shell section.
 *   - it writes ONE line, and only where planStampWrite() above allows it.
 *   - it reads the file back and re-parses before claiming success.
 *
 * Note it is safe for this to write sw.js at all only because sw.js is not in
 * SHELL: the file holding the hash is not among the files hashed, so writing
 * it does not move the target. That is asserted in the shell section too.
 */
if (process.argv.includes('--write-stamp')) {
  const plan = planStampWrite(loadSwConsts());

  if (plan.refuse) {
    console.error(`--write-stamp refused: ${plan.refuse}`);
    console.error('sw.js is unchanged. Fix the above and run it again.');
    process.exit(1);
  }

  if (plan.was === plan.stamp) {
    console.log(`shell stamp already current: ${plan.stamp} over ${plan.hashed} files. Nothing written.`);
    process.exit(0);
  }

  writeFileSync(REPO + 'sw.js', plan.next, 'utf8');

  // READ IT BACK. The difference between "wrote the file" and "the file now
  // says what I meant" is the whole reason this mode is allowed to exist, and
  // re-parsing is the only way to learn that the replacement landed inside a
  // string literal or broke the syntax on the way past.
  const after = loadSwConsts();
  if (after.error) {
    console.error(`--write-stamp: sw.js no longer parses after the write — ${after.error.message}`);
    process.exit(1);
  }
  if (after.SHELL_STAMP !== plan.stamp) {
    console.error(`--write-stamp: sw.js still reads ${after.SHELL_STAMP} after the write`);
    process.exit(1);
  }

  console.log(`shell stamp: ${plan.was} -> ${plan.stamp}  (over ${plan.hashed} files)`);
  console.log(`cache name:  ${after.CACHE_NAME}`);
  console.log('Review the diff, then run the suite.');
  process.exit(0);
}

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

/**
 * playDeal() without the settling: onState sees every frame, the dealing
 * interstitials and the full trick waiting to be swept included, BEFORE the
 * clock is allowed to move past them.
 */
function playDealUnsettled(g, policy = RANDOM_POLICY, onState = null) {
  let guard = 0;
  while (g.phase !== PHASES.DEAL_OVER && g.phase !== PHASES.MATCH_OVER) {
    if (onState) onState(g);
    const transient = g.phase === PHASES.FIRST_FOUR || g.phase === PHASES.LAST_FOUR || g.sweepAt !== null;
    if (transient) settle(g);
    else step(g, policy);
    if (++guard > 600) { failed++; console.error('  ✗ FAIL: a deal did not finish'); break; }
  }
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
            const REVEAL_FIELDS = ['trump', 'revealed', 'revealedBy', 'revealTrick', 'caller', 'indicator', 'log', 'seats'];
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
//  CHECKPOINT 7 — THE SCREEN
//
// ###########################################################################

const ROOT = installDOM();

/** Every intent ui.js may call, as a recorder. A missing one would be a
 *  TypeError on a tap, so the proxy reports any name it was not given. */
const CALLED = [];
const INTENT_NAMES = [
  'host', 'goJoin', 'join', 'watch', 'cancelJoin', 'leaveGame', 'goHome', 'rejoin', 'resumeTable', 'forgetTable',
  'setName', 'setCode', 'copyCode', 'setConfig', 'applyPreset', 'addBot', 'removeSeat', 'startMatch', 'nextDeal',
  'newMatch', 'selectBid', 'placeBid', 'passBid', 'chooseTrump', 'chooseSeventh', 'declare', 'selectCard',
  'playCard', 'callTrump', 'declarePair', 'togglePad', 'toggleLog', 'toggleLeave', 'toggleRules', 'explain',
  'dismissNetWarning',
];
const UNKNOWN_INTENTS = new Set();
const INTENTS = new Proxy({}, {
  get(_, name) {
    if (typeof name !== 'string') return undefined;
    if (!INTENT_NAMES.includes(name)) UNKNOWN_INTENTS.add(name);
    return (...args) => CALLED.push([name, ...args]);
  },
});

function baseApp(over = {}) {
  return {
    screen: 'game', me: { name: 'Asha' }, code: 'QRTX', pub: null, priv: null, isHost: true, watching: false,
    left: null, error: null, selected: null, selectedBid: null, showPad: false, showLog: false, showLeave: false,
    announce: '', busy: false, reconnecting: false, netWarning: null, ...over,
  };
}

/** Render into the shared root; returns { root, threw }. */
function draw(app) {
  try { render(ROOT, app, INTENTS); return { root: ROOT, threw: null }; }
  catch (e) { return { root: ROOT, threw: e }; }
}

/** What a viewer sees, as text: the dump plus every attribute that is read
 *  aloud or carries meaning. Used for the privacy comparisons. */
function frameText(root) {
  return walk(root).map((n) => (n.nodeType === 3 ? `"${n.data}"` : `<${n.tag} ${JSON.stringify(n.attrs)}>`)).join('\n');
}

const SCREENS = (() => {
  const src = readRepo('js/ui.js');
  const body = src.slice(src.indexOf('switch (app.screen)'));
  const found = [...body.slice(0, body.indexOf('\n  }')).matchAll(/case '([a-z]+)':/g)].map((m) => m[1]);
  if (found.length < 6) throw new Error(`SCREENS found only ${found.length} cases in ui.js`);
  return [...found, 'nonsense'];
})();

const FLAGS = [
  {}, { showPad: true }, { showLog: true }, { showLeave: true }, { error: 'Nope.' }, { busy: true },
  { reconnecting: true }, { netWarning: 'Slow.' }, { isHost: false }, { selectedBid: MIN_BID + 2 },
  { left: { role: 'host', code: 'WXYZ' } }, { left: { role: 'client', code: 'WXYZ' } },
];

// ===========================================================================
section('UI: every screen, every phase, every seat, without throwing');
// ===========================================================================
//
// Every frame of random deals under all sixteen configs, from all four seats
// and from a watcher (priv: null), each under every overlay flag, plus every
// screen with no state at all. Collects the classes for the stylesheet seam
// below at the same time, so the seam is checked over exactly these frames.
const EMITTED = new Set();
const KINDS = new Set();
let FRAMES = 0;
function sweepFrame(app) {
  const r = draw(app);
  FRAMES++;
  if (r.threw) { failed++; console.error(`  ✗ FAIL: render threw on screen ${app.screen}${app.pub ? ` / ${app.pub.phase}` : ''}:`, r.threw.stack.split('\n').slice(0, 3).join(' | ')); return null; }
  for (const n of walk(r.root)) for (const c of n.classList || []) EMITTED.add(c);
  return r.root;
}
{
  for (const screen of SCREENS) for (const f of FLAGS) sweepFrame(baseApp({ screen, pub: null, priv: null, ...f }));
  // The lobby, from an empty table to a full one, from the owner and others.
  for (const n of [1, 2, 3, 4]) {
    const g = new GameEngine();
    for (let i = 0; i < n; i++) g.addPlayer(IDS[i], NAMES[i], { clientId: `client-${i}-0123456789` });
    if (n === 3) g.addBot('p0');
    for (const config of [DEFAULT_CONFIG, ALL_CONFIGS[0], ALL_CONFIGS[15], ALL_CONFIGS[5]]) {
      g.setConfig('p0', config);
      for (const id of ['p0', 'p1', 'nobody']) {
        for (const f of FLAGS) {
          sweepFrame(baseApp({ pub: g.publicState(), priv: g.privateStateFor(id), ...f }));
          sweepFrame(baseApp({ screen: 'watch', pub: g.publicState(), priv: null, ...f }));
        }
      }
    }
  }
  // Whole deals. Selections are taken from the private view, so a selected
  // card, a selected bid and a selected trump card all render too.
  //
  // NOT playDeal(): that settles before every callback, so the two dealing
  // interstitials and the full trick waiting to be swept were never drawn —
  // the stylesheet seam below is what noticed. playDealUnsettled() draws each
  // frame BEFORE it lets the clock move.
  const everyFrame = (e) => {
    const pub = e.publicState();
    for (const l of pub.log) KINDS.add(l.kind);
    for (let s = 0; s < SEATS; s++) {
      const priv = e.privateStateFor(IDS[s]);
      const legal = priv.hand.find((c) => c.legal);
      const illegal = priv.hand.find((c) => !c.legal);
      for (const f of [FLAGS[0], FLAGS[1], FLAGS[2], FLAGS[3], { selected: legal && legal.code }, { selected: illegal && illegal.code }, { isHost: s === 0 }]) {
        sweepFrame(baseApp({ pub, priv, ...f }));
      }
    }
    sweepFrame(baseApp({ screen: 'watch', pub, priv: null }));
  };
  const transient = (e) => e.phase === PHASES.FIRST_FOUR || e.phase === PHASES.LAST_FOUR || e.sweepAt !== null;
  const sweepDeal = (g, policy) => {
    playDealUnsettled(g, policy, everyFrame);
    // And the deal-over and match-over screens.
    const pub = g.publicState();
    for (const id of IDS) sweepFrame(baseApp({ pub, priv: g.privateStateFor(id) }));
    sweepFrame(baseApp({ screen: 'watch', pub, priv: null }));
  };
  let interstitials = 0;
  for (const config of ALL_CONFIGS) {
    for (let m = 0; m < 2; m++) {
      const g = newTable(config);
      g.startMatch('p0', 0);
      if (transient(g)) interstitials++;
      sweepDeal(g, RANDOM_POLICY);
    }
  }
  ok(interstitials === ALL_CONFIGS.length * 2, 'every swept deal was drawn from its first interstitial, before the clock moved');
  // A PAIR, declared — the button and the log line. Random play under sixteen
  // configs reaches one too rarely to rely on, so deals with the pair on are
  // played until one is declared.
  {
    const PAIR_ALWAYS = { ...RANDOM_POLICY, pair: () => true };
    let deals = 0, g = null;
    while (!KINDS.has('pair') && deals < 400) {
      if (!g || g.phase === PHASES.MATCH_OVER) { g = newTable(DEFAULT_CONFIG); g.startMatch('p0', 0); }
      else step(g, PAIR_ALWAYS);
      sweepDeal(g, PAIR_ALWAYS);
      deals++;
    }
    ok(KINDS.has('pair'), `a pair was declared on screen, within ${deals} deals`);
  }
  // Played to the end, for MATCH_OVER from both sides.
  for (const config of [DEFAULT_CONFIG, ALL_CONFIGS[15]]) {
    const g = playMatch(config);
    for (const l of g.publicState().log) KINDS.add(l.kind);
    for (const id of IDS) for (const f of FLAGS) sweepFrame(baseApp({ pub: g.publicState(), priv: g.privateStateFor(id), ...f }));
    sweepFrame(baseApp({ screen: 'watch', pub: g.publicState(), priv: null }));
  }
  ok(FRAMES > 20000, `${FRAMES} frames rendered`);
  eq(UNKNOWN_INTENTS.size, 0, `ui.js calls only intents main.js provides (${[...UNKNOWN_INTENTS].join(', ') || 'none unknown'})`);
}

// ===========================================================================
section('UI: a size container has a height of its own, or cqh is zero');
// ===========================================================================
//
// judgement's lesson, met again here. `container-type: size` costs the box its
// content height, and Chromium resolves cqh — and @container (max-height) —
// only against a DEFINITE height. The felt was `flex: 1 1 auto` in the 100dvh
// play shell: it laid out at its full height while cqh read 0, so every
// short-felt query matched on every screen and the plates were hidden on a
// 1080p monitor. Found in a browser; the DOM shim has no layout.
//
// Two ways to be definite are accepted, and nothing else: a height that does
// not lean on the parent's, or a flex basis of 0 inside a column that has
// one. The second is checked as far as text can: the basis, and that every
// rendered node of that class sits directly in a .shell-play, whose own
// height is checked the first way.
{
  const rules = cssRules('css/app.css');
  const sized = rules.filter((r) => !r.at && /(^|;)\s*container-type\s*:\s*size\s*(;|$)/.test(r.body));
  ok(sized.length >= 2, `found ${sized.length} size containers in app.css (${sized.map((r) => r.sel).join(', ')})`);
  const DEFINITE = /^\d+(\.\d+)?(dvh|svh|lvh|vh|px|rem|em)$/;
  const BASIS_ZERO = /^\d+\s+\d+\s+0(px)?$/;
  eq(cssDecl(rules, '.shell-play', 'height'), '100dvh', 'the play shell has a definite height of its own');
  for (const r of sized) {
    const h = cssDecl(rules, r.sel, 'height');
    const f = cssDecl(rules, r.sel, 'flex');
    if (h && DEFINITE.test(h)) { passed++; continue; }
    if (f && BASIS_ZERO.test(f)) {
      passed++;
      // Then it must only ever be drawn straight inside the play shell.
      const cls = r.sel.replace(/^\./, '');
      let seen = 0, stray = 0;
      for (const config of [DEFAULT_CONFIG, ALL_CONFIGS[15]]) {
        const g = newTable(config);
        g.startMatch('p0', 0);
        playDealUnsettled(g, RANDOM_POLICY, (e) => {
          for (const n of walk(draw(baseApp({ pub: e.publicState(), priv: e.privateStateFor('p1') })).root)) {
            if (!n.classList || !n.classList.includes(cls)) continue;
            seen++;
            if (!n.parent || !n.parent.classList || !n.parent.classList.includes('shell-play')) stray++;
          }
        });
      }
      ok(seen > 50, `${r.sel} was drawn ${seen} times to check`);
      eq(stray, 0, `${r.sel} grows from a 0 basis and is only ever drawn straight inside the 100dvh play shell`);
      continue;
    }
    failed++;
    console.error(`  ✗ FAIL: ${r.sel} is a size container with no definite height (height: ${h || 'none'}, flex: ${f || 'none'}) — its cqh is 0`);
  }
}

// ===========================================================================
section('UI: render() is pure, and it clears');
// ===========================================================================
{
  const g = newTable();
  g.startMatch('p0', 0);
  settle(g);
  const app = baseApp({ pub: g.publicState(), priv: g.privateStateFor('p1') });
  const a = frameText(draw(app).root);
  const b = frameText(draw(app).root);
  eq(a, b, 'the same app renders the same tree');
  eq(ROOT.children.length, 1, 'and render() leaves exactly one child — it cleared the last frame first');
}

// ===========================================================================
section('UI: THE CONCEALED TRUMP never reaches a screen that should not have it');
// ===========================================================================
//
// The engine-level swap again, carried through the renderer. For every seat
// not entitled to the trump, and for the TV, the rendered DOM — every text
// node and every attribute, aria-labels included — must be identical whether
// the hidden card is one suit or another.
{
  let compared = 0;
  for (const config of ALL_CONFIGS) {
    const g = newTable(config);
    g.startMatch('p0', 0);
    // Three deals a configuration, so each one is seen with a fresh bidder.
    for (let d = 0; d < 3 && g.phase !== PHASES.MATCH_OVER; d++) {
      if (g.phase === PHASES.DEAL_OVER) step(g, RANDOM_POLICY);
      playDealUnsettled(g, RANDOM_POLICY, (e) => {
        if (!e.indicator || e.revealed) return;
        const other = [];
        for (let s = 0; s < SEATS; s++) if (s !== e.bidder) for (const c of e.hands[s]) if (suitOf(c) !== suitOf(e.indicator)) other.push([s, c]);
        if (!other.length) return;
        const [holder, card] = pick(other);
        const a = cloneEngine(e), b = cloneEngine(e);
        swapHidden(b, b.indicator, card);
        const observers = [0, 1, 2, 3, null].filter((o) => o !== holder && !(o === e.bidder && e.trumpMode === 'concealed'));
        for (const obs of observers) {
          const view = (en) => frameText(draw(obs === null
            ? baseApp({ screen: 'watch', pub: en.publicState(), priv: null })
            : baseApp({ pub: en.publicState(), priv: en.privateStateFor(IDS[obs]), showLog: true })).root);
          const va = view(a), vb = view(b);
          compared++;
          if (va !== vb) { failed++; console.error(`  ✗ FAIL: ${obs === null ? 'the TV' : `seat ${obs}`}'s screen changed with the hidden trump (${e.phase})`); }
          else passed++;
        }
        // The trump suit's NAME is nowhere on a screen that should not have it.
        const tv = frameText(draw(baseApp({ screen: 'watch', pub: e.publicState(), priv: null })).root);
        ok(!new RegExp(`"[^"]*\\b${suitName(suitOf(e.trumpCard))} are trumps`).test(tv), 'the TV never says which suit is trump before the reveal');
        ok(/trump hidden/.test(tv), 'and says, in words, that it is hidden');
      });
    }
  }
  ok(compared > 2000, `${compared} rendered screens compared with the hidden trump swapped`);
}

// ===========================================================================
section('UI: the bidder\'s peek, and the seventh card\'s honesty');
// ===========================================================================
{
  let peeks = 0, sevenths = 0;
  // Twice a configuration: once as random play has it, and once with a
  // bidder who always takes the seventh card where the option is on, so the
  // seventh branch is not left to a coin.
  const SEVENTH_ALWAYS = { ...RANDOM_POLICY, trump: (g, seat, priv) => (priv.trumpChoice.seventh ? 'seventh' : pick(priv.hand).code) };
  for (const config of ALL_CONFIGS) for (const policy of [RANDOM_POLICY, SEVENTH_ALWAYS]) {
    const g = newTable(config);
    g.startMatch('p0', 0);
    playDeal(g, policy, (e) => {
      if (e.phase !== PHASES.PLAY || e.revealed || !e.trumpMode || e.single) return;
      const root = draw(baseApp({ pub: e.publicState(), priv: e.privateStateFor(IDS[e.bidder]) })).root;
      const peek = byClass(root, 'peek')[0];
      ok(peek, 'the bidder sees a note about their face-down card');
      if (e.trumpMode === 'concealed') {
        peeks++;
        ok(peek && peek.text.includes(suitName(suitOf(e.trumpCard))), 'under a concealed trump, it names their trump — to them');
        ok(peek && /Only you can see this/.test(peek.text), 'and says only they can see it');
      } else {
        sevenths++;
        ok(peek && /unseen, even by you/.test(peek.text), 'under seventh card, it says the card is unseen even by them');
        ok(peek && !SUITS.some((x) => peek.text.includes(suitName(x))), 'and names no suit');
      }
      const partner = draw(baseApp({ pub: e.publicState(), priv: e.privateStateFor(IDS[partnerOf(e.bidder)]) })).root;
      eq(byClass(partner, 'peek').length, 0, 'the partner sees no peek');
    });
  }
  ok(peeks > 50 && sevenths > 20, `${peeks} concealed and ${sevenths} seventh-card bidder frames`);
}

// ===========================================================================
section('UI: the call — two actions, each explained, and the narrowed hand');
// ===========================================================================
{
  let choices = 0, narrowed = 0;
  for (const config of ALL_CONFIGS.filter((c) => !c.singleHand)) {
    for (let m = 0; m < 3; m++) {
      const g = newTable(config);
      g.startMatch('p0', 0);
      playDeal(g, RANDOM_POLICY, (e) => {
        if (e.phase !== PHASES.PLAY || e.sweepAt !== null) return;
        const seat = e.turnSeat;
        const priv = e.privateStateFor(IDS[seat]);
        const root = draw(baseApp({ pub: e.publicState(), priv })).root;
        const callBtn = interactive(root).find((n) => /^call for trump/.test(n.getAttribute('aria-label') || ''));
        if (priv.canCall) {
          choices++;
          ok(callBtn, 'a void player before the reveal is offered CALL FOR TRUMP');
          const led = ledSuitOf(e.plays);
          eq(callBtn && callBtn.getAttribute('aria-label'), `call for trump: you have no ${suitName(led)}`, 'labelled with the reason, as the brief asks');
          ok(byClass(root, 'choice').some((n) => /Play without calling/.test(n.text)), 'and the other choice, playing without calling, is explained beside it');
          ok(byClass(root, 'choice').every((n) => n.text.length > 30), 'each in words');
          CALLED.length = 0;
          if (callBtn) callBtn.click();
          same(CALLED[0], ['callTrump'], 'the button calls for trump and nothing else');
        } else {
          ok(!callBtn, 'nobody else is offered a call');
        }
        if (priv.mustTrump) {
          narrowed++;
          ok(byClass(root, 'why').some((n) => /you called for trump/i.test(n.text)), 'the caller is told why their hand narrowed');
          for (const b of byClass(root, 'card-btn')) {
            const code = priv.hand.find((c) => (b.getAttribute('aria-label') || '').startsWith(cardLabel(c.code)));
            if (code && !code.legal) ok(/called for trump/.test(b.getAttribute('aria-label')), 'and every greyed card says so');
          }
        }
      });
    }
  }
  ok(choices > 30 && narrowed > 5, `${choices} call choices and ${narrowed} narrowed hands rendered`);
}

// ===========================================================================
section('UI: the grey is a convenience, and it is honest');
// ===========================================================================
{
  let cards = 0;
  for (const config of [DEFAULT_CONFIG, ALL_CONFIGS[15]]) {
    const g = newTable(config);
    g.startMatch('p0', 0);
    playDeal(g, RANDOM_POLICY, (e) => {
      if (e.phase !== PHASES.PLAY) return;
      for (let s = 0; s < SEATS; s++) {
        const priv = e.privateStateFor(IDS[s]);
        if (priv.sittingOut) continue;
        const root = draw(baseApp({ pub: e.publicState(), priv })).root;
        const btns = byClass(root, 'card-btn');
        eq(btns.length, priv.hand.length, 'one button per card in hand');
        btns.forEach((b, i) => {
          const c = priv.hand[i];
          cards++;
          eq(b.getAttribute('aria-disabled'), c.legal ? 'false' : 'true', 'aria-disabled exactly when the engine says illegal');
          ok(b.hasClass('illegal') === !c.legal, 'greyed exactly when illegal');
          ok((b.getAttribute('aria-label') || '').startsWith(cardLabel(c.code)), `labelled "${cardLabel(c.code)}"`);
          if (!c.legal) ok((b.getAttribute('aria-label') || '').includes(c.reason), 'and an illegal card says why');
        });
      }
    });
  }
  ok(cards > 500, `${cards} rendered cards checked against the engine's legality`);
}

// ===========================================================================
section('UI: the table is drawn anticlockwise, partner opposite');
// ===========================================================================
{
  for (let me = 0; me < SEATS; me++) {
    const at = seatPositions(me);
    eq(at.bottom, me, 'you are at the bottom');
    eq(at.top, partnerOf(me), 'your partner is opposite, at the top');
    eq(at.right, nextSeat(me), 'the next to play after you — on your right — is drawn on the right');
    eq(at.left, nextSeat(nextSeat(nextSeat(me))), 'and the one before you on the left');
  }
  // The sweep of play order across the screen: bottom, right, top, left.
  same(seatsFrom(0).map((s) => SCREEN_SLOTS.find((k) => seatPositions(0)[k] === s)), ['bottom', 'right', 'top', 'left'],
    'play order sweeps bottom → right → top → left: anticlockwise on screen');
  // And the rendered plates agree.
  const g = newTable();
  g.startMatch('p0', 0);
  settle(g);
  g.placeBid(IDS[g.turnSeat], MIN_BID, 0);
  while (g.phase === PHASES.AUCTION) g.passBid(IDS[g.turnSeat], 0);
  g.chooseTrump(IDS[g.bidder], g.hands[g.bidder][0], 0);
  settle(g);
  while (g.phase === PHASES.DECLARE) g.passDeclare(IDS[g.turnSeat], 0);
  for (let me = 0; me < SEATS; me++) {
    const root = draw(baseApp({ pub: g.publicState(), priv: g.privateStateFor(IDS[me]) })).root;
    for (const slot of SCREEN_SLOTS) {
      const plate = byClass(root, 'plate').find((n) => n.hasClass(slot));
      const seat = seatPositions(me)[slot];
      ok(plate && plate.text.includes(seat === me ? 'You' : NAMES[seat]), `seat ${me}'s ${slot} plate is ${seat === me ? 'You' : NAMES[seat]}`);
      ok(plate && plate.hasClass(teamOf(seat) === teamOf(me) ? 'us' : 'them'), 'and coloured by team relative to the viewer');
    }
  }
}

// ===========================================================================
section('UI: isHost is not isOwner');
// ===========================================================================
{
  const g = new GameEngine();
  g.addPlayer('p0', 'Asha', { clientId: 'client-0-0123456789' });
  g.addPlayer('p1', 'Ben', { clientId: 'client-1-0123456789' });
  const pub = g.publicState();
  for (const [who, isHost] of [['p0', false], ['p1', true], ['p1', false]]) {
    const priv = g.privateStateFor(who);
    const root = draw(baseApp({ pub, priv, isHost })).root;
    const owner = priv.isOwner;
    const start = interactive(root).find((n) => /START/.test(n.text));
    eq(!!start, owner, `${who}${isHost ? ' (host tab)' : ''}: START is drawn only for the owner`);
    for (const n of [...byClass(root, 'toggle'), ...byClass(root, 'preset')]) {
      eq(n.disabled, !owner, 'the settings are live only for the owner, never for the host tab as such');
    }
    eq(byClass(root, 'panel-code').length > 0, isHost, 'the room code is shown on the host\'s device only');
  }
}

// ===========================================================================
section('UI: the rules are one tap away, from every screen there is');
// ===========================================================================
{
  // Rendered from the sweep's own kinds of frame: every screen, every phase.
  let frames = 0;
  const check = (app, what) => {
    const root = draw(app).root;
    frames++;
    const help = interactive(root).filter((n) => n.getAttribute('data-focus') === 'help');
    eq(help.length, 1, `${what}: exactly one How-to-play button`);
    if (help[0]) { CALLED.length = 0; help[0].click(); same(CALLED[0], ['toggleRules'], 'and it opens the rules'); }
  };
  for (const screen of SCREENS) if (screen !== 'game' && screen !== 'watch') check(baseApp({ screen }), screen);
  check(baseApp({ screen: 'watch' }), 'watch before state');
  const g = newTable(ALL_CONFIGS[15]);
  check(baseApp({ pub: g.publicState(), priv: g.privateStateFor('p0') }), 'lobby');
  g.startMatch('p0', 0);
  const seen = new Set();
  playDeal(g, RANDOM_POLICY, (e) => {
    if (seen.has(e.phase)) return;
    seen.add(e.phase);
    check(baseApp({ pub: e.publicState(), priv: e.privateStateFor('p1') }), e.phase);
    check(baseApp({ screen: 'watch', pub: e.publicState(), priv: null }), `TV in ${e.phase}`);
  });
  check(baseApp({ pub: g.publicState(), priv: g.privateStateFor('p1') }), g.phase);
  ok(seen.size >= 5, `checked phases: ${[...seen].join(', ')}`);
}

// ===========================================================================
section('UI: everything reachable has a name');
// ===========================================================================
{
  let controls = 0;
  for (const config of [DEFAULT_CONFIG, ALL_CONFIGS[15]]) {
    const g = newTable(config);
    g.startMatch('p0', 0);
    for (let d = 0; d < 3 && g.phase !== PHASES.MATCH_OVER; d++) {
      if (g.phase === PHASES.DEAL_OVER) step(g, RANDOM_POLICY);
      playDeal(g, RANDOM_POLICY, (e) => {
        for (const id of ['p0', 'p1']) {
          const root = draw(baseApp({ pub: e.publicState(), priv: e.privateStateFor(id), showPad: true })).root;
          for (const n of interactive(root)) {
            controls++;
            const name = (n.getAttribute('aria-label') || n.text || n.getAttribute('placeholder') || '').trim();
            ok(name.length > 0, `a ${n.tag} has an accessible name`);
          }
        }
      });
    }
  }
  ok(controls > 2000, `${controls} controls named`);
  // The brief's own examples.
  const g = newTable();
  g.startMatch('p0', 0);
  settle(g);
  const root = draw(baseApp({ pub: g.publicState(), priv: g.privateStateFor(IDS[g.turnSeat]) })).root;
  ok(interactive(root).some((n) => n.getAttribute('aria-label') === `bid ${MIN_BID}`), `a bid button is labelled "bid ${MIN_BID}"`);
}

// ===========================================================================
section('UI: a switched-off toggle draws nothing of its own');
// ===========================================================================
{
  let frames = 0;
  for (const config of ALL_CONFIGS) {
    const g = newTable(config);
    g.startMatch('p0', 0);
    playDeal(g, RANDOM_POLICY, (e) => {
      for (let s = 0; s < SEATS; s++) {
        const root = draw(baseApp({ pub: e.publicState(), priv: e.privateStateFor(IDS[s]) })).root;
        const t = root.text;
        frames++;
        if (!config.seventh) ok(!interactive(root).some((n) => /seventh card/i.test(n.getAttribute('aria-label') || '')), 'seventh off: no seventh-card choice');
        if (!config.pair) ok(!byClass(root, 'pair-btn').length, 'pair off: no pair button');
        if (!config.double) ok(!/Redouble\?|Double\?/.test(t), 'double off: no doubling question');
        if (!config.singleHand) ok(!/Single hand\?/.test(t), 'single hand off: no single-hand question');
      }
    });
  }
  ok(frames > 1000, `${frames} frames under switched-off toggles`);
}

// ===========================================================================
section('UI: nothing a peer can say becomes markup');
// ===========================================================================
{
  const EVIL = '<img src=x onerror=alert(1)>';
  const g = new GameEngine();
  g.addPlayer('p0', EVIL, { clientId: 'client-0-0123456789' });
  g.addPlayer('p1', '"><script>', { clientId: 'client-1-0123456789' });
  g.startMatch('p0', 0);
  settle(g);
  for (const screen of ['game', 'watch']) {
    const root = draw(baseApp({ screen, pub: g.publicState(), priv: screen === 'game' ? g.privateStateFor('p0') : null, showLog: true })).root;
    ok(walk(root).every((n) => n.tag !== 'img' && n.tag !== 'script'), `${screen}: a name never becomes an element`);
    ok(root.text.includes(cleanName(EVIL)), `${screen}: it is shown as the text it is`);
  }
}

// ===========================================================================
section('The rules sheet says what the code actually does');
// ===========================================================================
//
// index.html's <dialog id="rules"> is static prose, so nothing keeps it honest
// but this. Three kinds of check: each option's sentence appears verbatim, as
// js/rules.js writes it; every NUMBER the sheet quotes is derived here from
// the constant it describes, and a number nobody accounts for is a failure;
// and the sheet's few claims about order and seating are played out.
{
  const html = readRepo('index.html');
  const dialog = (html.match(/<dialog id="rules"[\s\S]*?<\/dialog>/) || [''])[0];
  ok(dialog.length > 1000, 'the rules dialog was found in index.html');
  const text = dialog.replace(/<!--[\s\S]*?-->/g, '').replace(/<[^>]+>/g, '').replace(/\s+/g, ' ');

  // --- the options, word for word ------------------------------------------
  for (const t of TOGGLES) {
    const { label, sheet } = TOGGLE_LABELS[t];
    ok(dialog.includes(`<li><b>${label}</b> — ${sheet}</li>`), `the sheet states the '${t}' option exactly as js/rules.js does`);
  }
  eq((dialog.match(/<h3>Options the host can switch on<\/h3>\s*<ul>([\s\S]*?)<\/ul>/) || ['', ''])[1].match(/<li>/g).length,
    TOGGLES.length, 'and lists no option the code does not have');

  // --- the numbers, each derived from what it describes --------------------
  const rankWord = (r) => (r === 'T' ? '10' : r);
  const ranking = RANKS.map(rankWord).join(' ');
  ok(dialog.includes(`<b>${ranking}</b>`), `the ranking is ${ranking}, the order js/cards.js uses`);
  const RANK_WORD = { J: 'jack', 9: 'nine', A: 'ace', T: 'ten', K: 'king', Q: 'queen', 8: 'eight', 7: 'seven' };
  eq(RANKS.filter((r) => RANK_WORD[r]).length, RANKS.length, 'every rank has its word here');
  const counted = RANKS.filter((r) => POINTS[r] > 0).map((r) => `${RANK_WORD[r]} ${POINTS[r]}`).join(', ');
  ok(text.includes(counted), `the card points read "${counted}"`);
  const blank = RANKS.filter((r) => POINTS[r] === 0).map((r) => RANK_WORD[r]);
  ok(text.includes(`${blank.slice(0, -1).join(', ')} and ${blank[blank.length - 1]} nothing`), 'and the four that count nothing are named');
  ok(text.includes(`${PACK_POINTS / SUITS.length} a suit and ${PACK_POINTS} in the pack`), `${PACK_POINTS / SUITS.length} a suit, ${PACK_POINTS} in all`);
  ok(text.includes(`A ${PACK_SIZE}-card pack`), `a ${PACK_SIZE}-card pack`);
  ok(text.includes(`Bids run from ${MIN_BID} to ${MAX_BID}`), `bids ${MIN_BID} to ${MAX_BID}`);
  ok(text.includes(`as soon as someone bids ${MAX_BID}`), 'the auction ends at the top bid');
  ok(text.includes(`+${DEAL_STAKE} game point`) && text.includes(`otherwise −${DEAL_STAKE}`), `a deal is worth ${DEAL_STAKE}`);
  ok(text.includes(`first side to +${MATCH_TARGET} wins`) && text.includes(`falls to −${MATCH_TARGET} loses`), `the match is to ±${MATCH_TARGET}`);
  ok(TOGGLE_LABELS.pair.sheet.includes(`goes down ${PAIR_SHIFT} (never below ${MIN_BID})`)
    && TOGGLE_LABELS.pair.sheet.includes(`goes up ${PAIR_SHIFT} (never above ${MAX_BID})`), `the pair moves the bid ${PAIR_SHIFT}, clamped to ${MIN_BID}–${MAX_BID}`);
  ok(TOGGLE_LABELS.double.sheet.includes(`worth ${DEAL_STAKE * multiplierFor(1)} game points; redoubled, ${DEAL_STAKE * multiplierFor(2)}`),
    `doubled ×${multiplierFor(1)}, redoubled ×${multiplierFor(2)}`);
  ok(TOGGLE_LABELS.singleHand.sheet.includes(`scores ${SINGLE_HAND_STAKE} game points; losing any trick costs ${SINGLE_HAND_STAKE}`),
    `single hand is ±${SINGLE_HAND_STAKE}`);
  const WORDS = ['zero', 'one', 'two', 'three', 'four', 'five', 'six', 'seven', 'eight'];
  ok(TOGGLE_LABELS.singleHand.sheet.includes(`all ${WORDS[HAND_SIZE]} tricks`), `single hand is all ${WORDS[HAND_SIZE]} tricks`);
  ok(text.includes(`${WORDS[SEATS]} players in two partnerships`), `${WORDS[SEATS]} players`);
  ok(text.includes(`gives ${WORDS[BATCH]} cards to each player`) && text.includes(`${WORDS[BATCH]} more each`) && BATCHES === 2,
    `dealt ${WORDS[BATCH]} and ${WORDS[BATCH]}`);
  ok(text.includes(`${WORDS[CODE_LENGTH]}-character room code`), `a ${WORDS[CODE_LENGTH]}-character code`);

  // EVERY NUMERAL ACCOUNTED FOR. The ranking is the one place digits are
  // names rather than quantities; past it, each number must be one of the
  // constants checked above. A new number in the sheet fails here until
  // somebody ties it to the code.
  const accounted = new Set([PACK_SIZE, PACK_POINTS, PACK_POINTS / SUITS.length, MIN_BID, MAX_BID, DEAL_STAKE,
    MATCH_TARGET, PAIR_SHIFT, DEAL_STAKE * multiplierFor(1), DEAL_STAKE * multiplierFor(2), SINGLE_HAND_STAKE,
    ...RANKS.map((r) => POINTS[r]).filter((p) => p > 0)].map(String));
  const strays = [...text.replace(ranking, '').matchAll(/\d+/g)].map((m) => m[0]).filter((n) => !accounted.has(n));
  eq(strays.length, 0, `every number on the sheet is a constant the code uses${strays.length ? ` (strays: ${strays.join(', ')})` : ''}`);

  // --- the claims about order, played out ----------------------------------
  ok(/Everything goes <b>anticlockwise<\/b>/.test(dialog) && TABLE_DIRECTION === ANTICLOCKWISE, 'the sheet and the code both say anticlockwise');
  for (let me = 0; me < SEATS; me++) {
    eq(seatPositions(me).right, nextSeat(me), `"the next player is the one on your right" — seat ${me}`);
    eq(seatPositions(me).top, partnerOf(me), `"partners sit opposite" — seat ${me}`);
  }
  const g = newTable();
  g.startMatch('p0', 0);
  settle(g);
  eq(g.turnSeat, nextSeat(g.dealerSeat), '"starting right of the dealer" — the first to bid');
  for (let i = 0; i < 400 && g.phase !== PHASES.PLAY; i++) { settle(g); if (g.phase !== PHASES.PLAY) step(g); }
  if (g.phase === PHASES.PLAY && !g.single) {
    eq(g.turnSeat, nextSeat(g.dealerSeat), '"the player right of the dealer leads"');
    eq(g.hands[g.bidder].length, HAND_SIZE - 1, '"the indicator is out of the bidder\'s hand until trump is revealed"');
  } else ok(false, 'a deal reached play without a single hand, to check who leads');
  // All four pass: thrown in, and the next dealer deals.
  const t = newTable();
  t.startMatch('p0', 0);
  settle(t);
  const dealer = t.dealerSeat;
  for (let i = 0; i < SEATS; i++) t.passBid(IDS[t.turnSeat], 1);
  settle(t);
  eq(t.dealerSeat, nextSeat(dealer), '"if all four pass, the deal is thrown in and the next dealer deals"');
}

// ===========================================================================
section('The seams: two files, one string, and nothing enforcing it');
// ===========================================================================
//
// Ported from judgement, where every bug its ship audit found sat in this
// shape: two files that must agree on a STRING, each correct and tested in
// isolation, and no test crossing between them — main.js sending `patch`
// while intents.js read `config`; ui.js emitting a class app.css never
// styled; app.css styling a log kind the engine never emitted. These are
// mechanical and STRICT IN BOTH DIRECTIONS, with no exemption list.

{
  const mainSrc = readRepo('js/main.js');
  const intentsSrc = readRepo('js/intents.js');

  // Comments first, always. A substring search over a commented file cannot
  // tell an explanation from the thing being explained, and this codebase has
  // been bitten by that repeatedly — intents.js's own header prose names every
  // intent and every field, and would satisfy any of these checks on its own.
  const stripJs = (s) => s.replace(/\/\*[\s\S]*?\*\//g, '').replace(/^\s*\/\/.*$/gm, '');
  const main = stripJs(mainSrc);
  const intents = stripJs(intentsSrc);

  // Everything outside the outermost braces/brackets, so a nested object
  // literal contributes no keys of its own. `dispatch({ type: 'setConfig',
  // patch: { ...preset.config } })` must yield `patch`, never `maxHand`.
  const flat = (s) => {
    let d = 0, out = '';
    for (const ch of s) {
      if (ch === '{' || ch === '[') d++;
      else if (ch === '}' || ch === ']') d--;
      else if (d === 0) out += ch;
    }
    return out;
  };

  // --- what main.js actually puts on the wire ------------------------------
  const NEEDLE = 'dispatch({';
  const sentBy = new Map();
  for (let i = main.indexOf(NEEDLE); i !== -1; i = main.indexOf(NEEDLE, i + 1)) {
    // Brace-BALANCED, not /[^}]*/. The preset dispatch on main.js:752 carries
    // a nested object, and a non-greedy scan ends the frame at that object's
    // closing brace — quietly dropping every field after it and reporting a
    // frame that nothing sends. A checker that cries wolf gets ignored on the
    // one line that matters, so it is worth the extra ten lines here.
    let d = 0, end = -1;
    for (let j = i + NEEDLE.length - 1; j < main.length; j++) {
      if (main[j] === '{') d++;
      else if (main[j] === '}' && --d === 0) { end = j; break; }
    }
    if (end === -1) continue;
    const body = main.slice(i + NEEDLE.length, end);
    const type = (body.match(/type:\s*'([^']+)'/) || [])[1];
    if (!type) continue;
    if (!sentBy.has(type)) sentBy.set(type, new Set());
    // BOTH SPELLINGS: `code: x` and the `{ type, code }` shorthand carry the
    // field identically. Reading only the colon form reported four healthy
    // intents as broken.
    for (const tok of flat(body).split(',')) {
      const key = (tok.includes(':') ? tok.slice(0, tok.indexOf(':')) : tok).trim();
      if (/^\w+$/.test(key) && key !== 'type') sentBy.get(type).add(key);
    }
  }

  ok(sentBy.size >= 5, `main.js dispatches ${sentBy.size} distinct intent types`);
  for (const type of sentBy.keys()) {
    ok(GAME_INTENTS.includes(type),
      `'${type}' is dispatched by main.js and is a real game intent`);
  }

  // --- what intents.js reads back off the message --------------------------
  const caseBody = (type) => {
    const at = intents.indexOf(`case '${type}':`);
    if (at === -1) return null;
    const rest = intents.slice(at + 6);
    const next = rest.indexOf("case '");
    return next === -1 ? rest : rest.slice(0, next);
  };

  let crossed = 0, optional = 0, requiredMissing = 0, sentNeverRead = 0, noCase = 0;
  for (const [type, sent] of sentBy) {
    const body = caseBody(type);
    if (body === null) { noCase++; console.error(`  ✗ FAIL: main.js dispatches '${type}' and intents.js has no case for it`); continue; }

    const reads = new Set([...body.matchAll(/msg\.(\w+)/g)].map((m) => m[1]));
    for (const f of reads) {
      // A field the case EXPLICITLY handles the absence of is optional by
      // design, and main.js is allowed never to send it. addBot is the real
      // one: the plain "+ ADD A BOT" button sends no name, and the case says
      // so in as many words, because a bot named by nobody is still a bot.
      //
      // Everything else is REQUIRED, and a required field that no producer
      // sends is the dead lobby exactly. This is the distinction that matters,
      // and it is why the check is not simply "every read field is sent".
      const guarded = new RegExp(
        `msg\\.${f}\\s*(===|!==|==|!=)\\s*(undefined|null)`
        + `|(undefined|null)\\s*(===|!==|==|!=)\\s*msg\\.${f}`
        + `|'${f}'\\s+in\\s+msg|msg\\.${f}\\s*\\?\\?`,
      ).test(body);
      if (guarded) { optional++; continue; }
      if (sent.has(f)) { crossed++; continue; }
      requiredMissing++;
      console.error(`  ✗ FAIL: intents.js '${type}' requires msg.${f}, and main.js sends [${[...sent].join(', ') || 'nothing'}]`);
    }
    for (const f of sent) {
      if (!reads.has(f)) {
        sentNeverRead++;
        console.error(`  ✗ FAIL: main.js sends '${type}'.${f} and intents.js never reads it`);
      }
    }
  }

  eq(noCase, 0, 'every intent main.js dispatches has a case in intents.js');
  eq(requiredMissing, 0, 'every field intents.js REQUIRES is a field main.js actually sends');
  eq(sentNeverRead, 0, 'and every field main.js sends is one intents.js actually reads');
  // THE PAIRED POSITIVES. Zero mismatches out of zero fields compared is what
  // a checker that has quietly stopped parsing looks like from the outside,
  // and it is indistinguishable from a clean bill of health. Both counters
  // must be non-trivially large for the zeroes above to mean anything.
  ok(crossed >= 4, `and ${crossed} required (intent, field) pairs were matched across the seam, not zero`);
  ok(optional >= 1, `with ${optional} field(s) exempted as explicitly-optional, so that branch is exercised too`);
  console.log(`  main.js <-> intents.js: ${sentBy.size} intents, ${crossed} required fields matched, ${optional} optional`);
}

{
  // --- seam 2: every class js/ui.js emits, every selector css/app.css has ---
  //
  // Derived by RENDERING, not by regexing ui.js for `class:` — a regex cannot
  // see through a template hole. The emitted set is the one the frame sweep
  // above collected, over exactly the frames it drew, topped up here with the
  // few states that sweep cannot reach by playing.
  const cssSrc = readRepo('css/app.css').replace(/\/\*[\s\S]*?\*\//g, '');
  const styled = new Set();
  for (const m of cssSrc.matchAll(/\.(-?[_a-zA-Z][\w-]*)/g)) styled.add(m[1]);

  const emitted = EMITTED;
  const kinds = KINDS;
  const bothWays = (pub, priv) => {
    for (const f of FLAGS) {
      sweepFrame(baseApp({ screen: 'game', pub, priv, ...f }));
      sweepFrame(baseApp({ screen: 'watch', pub, priv: null, ...f }));
    }
  };

  // A SEAT THAT IS AWAY, and one that LEFT, mid-match: the play strip and the
  // TV both mark them, and random play never disconnects anybody. The log
  // kinds 'leave' and 'join' (a reclaim) come from here too.
  {
    const g = newTable();
    g.startMatch('p0', 0);
    settle(g);
    g.disconnect('p1');
    g.disconnect('p2', { left: true });
    bothWays(g.publicState(), g.privateStateFor('p0'));
    g.addPlayer('p1', NAMES[1], { clientId: 'client-1-0123456789' });
    for (const l of g.publicState().log) kinds.add(l.kind);
    bothWays(g.publicState(), g.privateStateFor('p1'));
  }

  // THE LOBBY HOLDING A SEAT THAT IS AWAY, which no sweep produces: a lobby
  // disconnect splices the seat out. restore() of a snapshot whose phase this
  // build does not know falls back to the lobby with the seats as saved.
  {
    const g = newTable();
    g.startMatch('p0', 0);
    g.disconnect('p1');
    const back = new GameEngine();
    back.restore({ ...g.serialize(), phase: 'a phase from some other build' });
    eq(back.phase, PHASES.LOBBY, 'an unrecognised snapshot phase restores to the lobby');
    const pub = back.publicState();
    ok(pub.seats.some((s) => s && !s.connected && !s.isBot),
      'and a seat that was away is still away — otherwise this frame proves nothing');
    for (const id of ['p0', 'p1', 'nobody']) bothWays(pub, back.privateStateFor(id));
  }
  const seamFrames = FRAMES;

  // Classes that never pass through the renderer: authored into index.html, or
  // put on <body> by main.js. Both are real emissions and app.css styles them.
  const htmlSrc = readRepo('index.html');
  for (const m of htmlSrc.matchAll(/class="([^"]*)"/g)) {
    for (const c of m[1].split(/\s+/)) if (c) emitted.add(c);
  }
  const mainFlat = readRepo('js/main.js').replace(/\/\*[\s\S]*?\*\//g, '').replace(/^\s*\/\/.*$/gm, '');
  for (const m of mainFlat.matchAll(/document\.body\.classList\.\w+\(\s*'([^']+)'/g)) emitted.add(m[1]);

  const unstyled = [...emitted].filter((c) => !styled.has(c)).sort();
  const unused = [...styled].filter((c) => !emitted.has(c)).sort();

  for (const c of unstyled) console.error(`  ✗ FAIL: class "${c}" is emitted and css/app.css has no rule for it`);
  for (const c of unused) console.error(`  ✗ FAIL: css/app.css styles ".${c}" and nothing ever emits it`);
  eq(unstyled.length, 0, 'every class that reaches the DOM has a rule in app.css');
  eq(unused.length, 0, 'and every class rule in app.css matches something that is actually rendered');

  // Paired positives again: both lists above are empty, and that is only worth
  // anything if the sets being compared are big and were really populated.
  ok(seamFrames > 5000, `across ${seamFrames} frames`);
  ok(emitted.size > 100, `with ${emitted.size} distinct classes emitted`);
  ok(styled.size > 100, `and ${styled.size} class selectors in the stylesheet`);

  // --- seam 3: the log kinds, which is where the guessed list showed -------
  //
  // Same comparison, narrowed to the family that actually drifted, because
  // ".log-play exists and matches nothing" and "made/missed render unstyled"
  // are one mistake with two symptoms and neither one looks like a bug on
  // screen. Kinds come from PLAYED MATCHES rather than from a list written
  // here — a list written here is the thing that was wrong.
  const ruleKinds = new Set([...styled].filter((c) => c.startsWith('log-')).map((c) => c.slice(4)));
  const missingRule = [...kinds].filter((k) => !ruleKinds.has(k)).sort();
  const deadRule = [...ruleKinds].filter((k) => !kinds.has(k)).sort();

  for (const k of missingRule) console.error(`  ✗ FAIL: the engine logs kind '${k}' and app.css has no .log-${k}`);
  for (const k of deadRule) console.error(`  ✗ FAIL: app.css styles .log-${k} and the engine never logs that kind`);
  eq(missingRule.length, 0, 'every log kind the engine emits has a .log-<kind> rule');
  eq(deadRule.length, 0, 'and every .log-<kind> rule matches a kind the engine emits');
  ok(kinds.size >= 9, `derived from ${kinds.size} kinds actually observed: ${[...kinds].sort().join(', ')}`);
  console.log(`  ui.js <-> app.css: ${seamFrames} frames, ${emitted.size} classes emitted, ${styled.size} styled, 0 either way`);
  console.log(`  log kinds observed: ${[...kinds].sort().join(', ')}`);

  // --- seam 4: new state arrives, and nothing tells the screen reader -------
  //
  // READ THIS FIRST, because it is the only check in the file that reasons
  // about source text where it would rather run the code. js/main.js cannot be
  // imported here: it touches document, localStorage and the transport at
  // module scope, so importing it in node throws before the first line of any
  // test. That is exactly why announcementFor() was put in util.js — so the
  // hard part could be tested for real. What is left in main.js is the WIRING,
  // three lines of it, and the wiring is what broke: the host's push() updated
  // app.pub and never announced, so a sighted player saw the table move and a
  // screen-reader player heard nothing for the whole match.
  //
  // Deleting announceFrom(pub) from push() leaves this suite green without
  // this check. A mutation run is how that showed; the pass count did not.
  //
  // The rule is: the announcement is computed BEFORE the frame that would show
  // it. So the window searched runs from each app.pub assignment to the next
  // paint() — not a fixed line count, which would be arbitrary, and not the
  // enclosing function, which needs a parser. app.pub = null is exempt and
  // counted separately: goHome() is leaving the table, and there is no news.
  {
    const sites = [...mainFlat.matchAll(/app\.pub\s*=\s*([A-Za-z_$][\w$]*|null)\b/g)];
    const live = sites.filter((m) => m[1] !== 'null');
    const silent = [];
    for (const m of live) {
      const from = m.index;
      const stop = mainFlat.indexOf('paint()', from);
      // No paint() after it at all is itself a finding, and the 400-char cap
      // keeps a missing terminator from swallowing the rest of the file and
      // finding somebody else's announce.
      const window = mainFlat.slice(from, stop === -1 ? from + 400 : stop);
      // The enclosing function's name rather than a line number: mainFlat has
      // had its block comments collapsed, so its line numbers are not the
      // file's, and a wrong line number in a failure message is worse than
      // none. The last declaration above the assignment is the one it is in.
      const decls = [...mainFlat.slice(0, from).matchAll(/(?:function|onState:|onOpen:)\s*([\w$]*)/g)];
      const where = decls.length ? (decls[decls.length - 1][1] || 'onState') : '?';
      if (!window.includes('announceFrom(')) { silent.push(`${where}(): app.pub = ${m[1]}`); continue; }
      // Announced from the value that was just stored, not from some older
      // one still in scope. Only checkable when the right-hand side is a plain
      // variable; if it ever becomes a call expression this quietly relaxes to
      // "something was announced", which is still the check that matters.
      if (!window.includes(`announceFrom(${m[1]})`)) silent.push(`${where}(): announces something other than ${m[1]}`);
    }
    for (const s of silent) console.error(`  ✗ FAIL: js/main.js ${s} — new state, no announcement`);
    eq(silent.length, 0, 'every place main.js takes new public state also feeds the live region');
    ok(live.length >= 2, `checked ${live.length} places state arrives (the host's own push, and a client's onState)`);
    ok(sites.length > live.length, 'and left the one app.pub = null alone, because leaving the table is not news');

    // announceFrom() itself still doing the two things its callers assume. The
    // check above only proves the call is written; a body that had been
    // hollowed out would satisfy it and say nothing.
    const body = (mainFlat.match(/function announceFrom\([\s\S]*?\n}/) || [''])[0];
    ok(/announcementFor\(/.test(body), 'announceFrom() asks announcementFor() what is new');
    ok(/app\.announce\s*=/.test(body), 'and puts the answer where render() will read it');
    ok(/announceCursor\s*=/.test(body), 'and advances the cursor, so the next call does not replay it');
  }

  let guardedNames = [];
  // --- seam 5: the callbacks that outlive the session that made them -------
  //
  // main.js hands net.js nine handlers as a host and eight as a client, and
  // net.js calls them whenever the network feels like it. The session those
  // closures belong to can be gone by then — the player pressed Home, the
  // reconnect ladder moved to the next rung, a reload started a new match —
  // and every one of them still holds the old `engine`, the old `host`, and
  // a reference to `app`.
  //
  // Three things went wrong here, and they look like three bugs but are one:
  //
  //   * onOpen from an abandoned join sets app.screen='game', dragging a
  //     player who is on the home screen back into a table they left.
  //   * onClose from a destroyed client calls scheduleReconnect(), which sets
  //     a NEW reconnectTimer — after teardown() cleared the old one. The tab
  //     then re-dials, on a ladder, a room nobody is in. teardown() looks
  //     like it prevents this. It does not: clearing a timer does nothing
  //     about the code that creates another one.
  //   * onJoin/onData/onDisconnect dereference `engine`, which teardown()
  //     sets to null.
  //
  // The fix is one epoch counter and a uniform `if (!live()) return;`. This
  // checks it is uniform, because a guard applied to eight of nine handlers
  // is the ninth handler's bug. Source-level for the same reason as seam 4 —
  // main.js cannot be imported headless.
  {
    // The contents of a balanced {...} starting at the first brace after
    // `needle`. Same brace-walk as seam 1 and for the same reason: these
    // literals contain nested objects and arrow bodies, and a non-greedy
    // match ends at the first inner `}`.
    const balanced = (src, needle) => {
      const at = src.indexOf(needle);
      if (at === -1) return null;
      const open = src.indexOf('{', at);
      if (open === -1) return null;
      let d = 0;
      for (let j = open; j < src.length; j++) {
        if (src[j] === '{') d++;
        else if (src[j] === '}' && --d === 0) return src.slice(open + 1, j);
      }
      return null;
    };

    // Handler keys at the TOP level of the literal only. Depth-tracked rather
    // than regexed over the whole blob, so an `onclick:` inside a rendered
    // element or a nested options object can never be mistaken for one of the
    // transport's own handlers.
    const topHandlers = (lit) => {
      const found = [];
      let d = 0;
      for (let i = 0; i < lit.length; i++) {
        const ch = lit[i];
        if (ch === '{' || ch === '(' || ch === '[') d++;
        else if (ch === '}' || ch === ')' || ch === ']') d--;
        else if (d === 0) {
          const m = /^(on[A-Z]\w*)\s*:\s*(?:\([^)]*\)|\w+)\s*=>\s*\{/.exec(lit.slice(i));
          if (m) found.push([m[1], lit.slice(i + m[0].length, i + m[0].length + 120)]);
        }
      }
      return found;
    };

    const hostLit = balanced(mainFlat, 'host = createHost(');
    const clientLit = balanced(mainFlat, 'client = joinHost(');
    ok(hostLit !== null, 'the host handler literal was located in js/main.js');
    ok(clientLit !== null, 'and the client handler literal too');

    const unguarded = [];
    const seen = [];
    for (const [role, lit] of [['host', hostLit], ['client', clientLit]]) {
      const hs = topHandlers(lit || '');
      ok(hs.length >= 8, `${role}: found ${hs.length} transport handlers to check`);
      for (const [name, head] of hs) {
        seen.push(`${role}.${name}`);
        if (!/^\s*if\s*\(!live\(\)\)\s*return;/.test(head)) unguarded.push(`${role}.${name}`);
      }
    }
    for (const h of unguarded) {
      console.error(`  ✗ FAIL: js/main.js ${h} does not open with the epoch guard — it can run after teardown`);
    }
    eq(unguarded.length, 0, 'every transport handler refuses to act for a session that has ended');

    // BY NAME, not by count. A count tuned to today's number still passes on
    // the day somebody adds a handler and forgets the guard — which is the
    // exact failure being prevented.
    //
    // A count is also unreadable when it is wrong. The first version of this
    // check asserted `guarded >= 16` and printed a hard-coded 16 in the
    // summary line; the scanner was in fact finding 17 the whole time, and
    // there was no way to tell the two apart from the output. Naming them
    // costs two lines and makes the summary say what was actually examined.
    //
    // -----------------------------------------------------------------------
    // AND THE NAMES ARE READ OUT OF js/net.js RATHER THAN WRITTEN DOWN HERE
    // -----------------------------------------------------------------------
    // They were written down here, and they were right: nine host names and
    // nine client names, matching net.js exactly. Right by hand, though, with
    // nothing holding them there — and the paragraph above had already made
    // the argument ("net.js decides which handlers exist") before going on to
    // hard-code the names net.js decided on that afternoon.
    //
    // The hole that leaves is specific, and it is not the one the guard check
    // closes. The scanner above only inspects handlers it FINDS in main.js, so
    // a handler main.js never wires at all is invisible to it. This list is
    // what is supposed to notice the absence — and a list cannot notice a name
    // it does not contain. Add onFoo to net.js, wire it nowhere, and the suite
    // stays green over a callback firing into nothing.
    //
    // THE SOURCE OF TRUTH IS THE CALL, NOT THE DOC BLOCK. net.js sets out both
    // handler sets in prose above createHost and joinHost, and parsing that
    // would be less code than what follows. It would also just move the
    // hand-written list into the other file, where a doc comment drifts from
    // the code in precisely the way this list did. `handlers.onX(...)` cannot
    // drift, because it IS the call: if it is reachable, the handler can fire.
    const netFlat = readRepo('js/net.js')
      .replace(/\/\*[\s\S]*?\*\//g, '').replace(/^\s*\/\/.*$/gm, '');

    // The body of a named function. NOT balanced() above — that takes the
    // first `{` after the needle, and every function in play here is declared
    // `(handlers = {})`, so it would return the default value as the body and
    // every set would come back empty. Walk the parameter list to its closing
    // paren first, then find the brace.
    const funcBody = (src, name) => {
      const at = src.search(new RegExp(`function\\s+${name}\\s*\\(`));
      if (at === -1) return null;
      let i = src.indexOf('(', at), d = 0;
      for (; i < src.length; i++) {
        if (src[i] === '(') d++;
        else if (src[i] === ')' && --d === 0) { i++; break; }
      }
      const open = src.indexOf('{', i);
      if (open === -1) return null;
      d = 0;
      for (let j = open; j < src.length; j++) {
        if (src[j] === '{') d++;
        else if (src[j] === '}' && --d === 0) return src.slice(open + 1, j);
      }
      return null;
    };
    const fires = (body) => new Set([...(body || '')
      .matchAll(/handlers\.(on[A-Z]\w*)\s*\(/g)].map((m) => m[1]));

    // ONE LEVEL OF CALL GRAPH, because four of the nine are not in either
    // entry point. onBrokerUp/Down/Lost fire inside attachBrokerRecovery and
    // onError's no-transport path fires inside inertTransport; both roles call
    // both helpers, and neither helper's names appear in createHost or
    // joinHost directly. A helper can only fire what it is handed, so the ones
    // worth following are exactly those called with `handlers` as an argument
    // — which is also why this needs no recursion or import graph: the set of
    // functions that can reach a caller's handler is the set that is given it.
    const roleHandlers = (entry) => {
      const body = funcBody(netFlat, entry);
      if (body === null) throw new Error(`net.js: could not find ${entry}()`);
      const names = fires(body);
      for (const m of body.matchAll(/\b([a-z]\w*)\s*\([^)]*\bhandlers\b/g)) {
        const helper = funcBody(netFlat, m[1]);
        if (helper) for (const n of fires(helper)) names.add(n);
      }
      return [...names].sort();
    };
    const HOST_HANDLERS = roleHandlers('createHost');
    const CLIENT_HANDLERS = roleHandlers('joinHost');

    // A SCAN THAT QUIETLY FINDS NOTHING MAKES EVERY ASSERTION BELOW VACUOUS,
    // so a broken parse stops the run instead of passing it. Same reasoning as
    // SCREENS at the top of this file: a derived list is only worth more than
    // a typed one while the derivation is known to be working, and `0 of 0
    // handlers were checked` is a green suite that has tested nothing.
    if (HOST_HANDLERS.length < 8 || CLIENT_HANDLERS.length < 8) {
      throw new Error('net.js handler scan found '
        + `${HOST_HANDLERS.length} host and ${CLIENT_HANDLERS.length} client handlers`);
    }
    // onReplaced needs the guard more than most of these, not less. It is the
    // only handler whose body calls teardown() itself, so an unguarded one
    // running late would bump the epoch a second time and tear down whatever
    // session had started since. Asserted by name because the derivation
    // cannot know that one of the names it finds matters more than the others.
    ok(CLIENT_HANDLERS.includes('onReplaced'),
      'onReplaced is among the client handlers the scan found — the one that tears down from inside');

    for (const [role, names] of [['host', HOST_HANDLERS], ['client', CLIENT_HANDLERS]]) {
      for (const want of names) {
        ok(seen.includes(`${role}.${want}`),
          `${role}.${want} — js/net.js can fire it, so js/main.js wires it and the scanner checked it`);
      }
    }

    // AND THE OTHER DIRECTION. The loop above is satisfied by a main.js that
    // wires twenty handlers so long as the right nine are among them, and a
    // handler net.js never calls is dead code wearing a live name — nothing
    // distinguishes it from the real ones when read, and it will be maintained
    // as though it fires. Before the lists were derived this direction was an
    // equality on the total, which caught a spurious handler only when it was
    // not offset by a missing one.
    const offered = new Set([
      ...HOST_HANDLERS.map((n) => `host.${n}`),
      ...CLIENT_HANDLERS.map((n) => `client.${n}`),
    ]);
    const orphans = seen.filter((s) => !offered.has(s));
    for (const o of orphans) {
      console.error(`  ✗ FAIL: js/main.js wires ${o}, which js/net.js never calls`);
    }
    eq(orphans.length, 0, 'and js/main.js wires no transport handler that net.js cannot fire');
    eq(seen.length, HOST_HANDLERS.length + CLIENT_HANDLERS.length,
      `all ${HOST_HANDLERS.length + CLIENT_HANDLERS.length} transport handlers net.js offers were seen, and every one is guarded`);
    guardedNames = seen;

    // The counter those guards read has to actually move, and it has to move
    // in teardown() — a `live()` that is never falsified is decoration.
    const td = balanced(mainFlat, 'function teardown(');
    ok(td !== null && /netEpoch\s*\+\+/.test(td || ''),
      'teardown() invalidates the epoch, so every handler above goes dead at once');

    // The two timers. Neither is a transport handler, both outlive a
    // teardown, and the reconnect one is the whole reason this seam exists.
    const sr = balanced(mainFlat, 'function scheduleReconnect(');
    ok(sr !== null && /epoch\s*!==\s*netEpoch/.test(sr || ''),
      'the reconnect timer checks the epoch before it re-dials — clearTimeout is not enough on its own');

    // --- and the order of the two lines that retire a superseded tab -------
    //
    // THE ONLY PLACE THIS ORDERING IS ENFORCED. The live transport test for
    // the second tab builds its own host, because liveTable's does not retire
    // anything — so it asserts against a COPY of this handler, and a copy
    // agrees with itself forever. What follows is the part that checks the
    // copy is still describing main.js.
    //
    // Both statements are required and the order is the whole fix: a close
    // that arrives with no explanation is indistinguishable from a channel
    // that died, and the other end will redial, reclaim, and send the tab
    // that just took the seat the same close. Swap these two lines and the
    // frame is sent on a connection that is already shut — trySend() eats
    // the InvalidStateError, nothing throws, nothing is logged, and the loop
    // is back with a passing suite.
    const oj = balanced(mainFlat, 'onJoin: (playerId, hello) =>');
    ok(oj !== null, 'the host onJoin handler was found to check');
    if (oj) {
      const farewell = oj.indexOf('replacedFrame()');
      const retire = oj.indexOf('dropConnection(stale)');
      ok(farewell !== -1, 'onJoin tells a superseded connection why before it goes');
      ok(retire !== -1, 'and still retires it, so the host is not left holding two channels for one player');
      ok(farewell !== -1 && retire !== -1 && farewell < retire,
        'and it says so BEFORE closing the channel it is saying it on, which is the entire fix');
    }
    ok(/replacedFrame/.test(readRepo('js/main.js').slice(0, 4000)),
      'main.js imports the builder rather than writing the type string itself');

    // --- and the other half of it, on the receiving side -------------------
    //
    // THE SESSION RECORD IS SHARED BY EVERY TAB ON THE ORIGIN, which is the
    // same fact that causes this bug in the first place: one localStorage,
    // one ticket, two tabs. So the tab that just LOST the seat must not tidy
    // up after itself. The record it would delete was written moments ago by
    // the tab that WON, and deleting it means THAT tab cannot resume after a
    // reload. The cost of leaving it is this tab pulling the seat back over
    // once if the player reloads here, which settles immediately, because the
    // other tab then lands on this same screen in turn.
    //
    // Checked at the source, and it has to be: the live transport test above
    // runs against a model of this handler, and a model has no localStorage
    // to clobber, so no behavioural test in this suite can see the
    // difference. This is also exactly the edit a tidy-up pass would make —
    // clearSession() is right on the other three terminal screens — and
    // until this assertion the only thing standing in its way was a comment.
    const orp = balanced(mainFlat, 'onReplaced: () =>');
    ok(orp !== null, 'the client onReplaced handler was found to check');
    if (orp) {
      ok(orp.includes('teardown()'),
        'onReplaced tears the session down itself rather than letting the close that follows do it');
      ok(!orp.includes('clearSession'),
        'and does NOT clear the stored session — that record belongs to the tab that took the seat');
      ok(/app\.screen\s*=\s*'replaced'/.test(orp),
        'and lands on the screen that names the cause, rather than the generic error');
    }

    // --- and the amplifier, which lives in the same handler ----------------
    //
    // An unrecognised frame never reaches the engine, so nothing changed and
    // there is nothing to send. It used to push anyway: one junk frame in,
    // seven serialised public states out, and free to the sender because an
    // intent the dispatcher does not recognise can never be refused by the
    // engine either. A REFUSED intent still pushes, deliberately — that
    // client's view has probably drifted and the answer is the truth.
    const onData = balanced(hostLit || '', 'onData:');
    ok(onData !== null, 'the host onData body was located');
    const bail = (onData || '').indexOf('if (!handled) return;');
    const pushes = (onData || '').indexOf('push()');
    ok(bail !== -1, 'the host returns early on a frame the dispatcher did not recognise');
    ok(bail !== -1 && pushes !== -1 && bail < pushes,
      'and returns BEFORE push(), so junk cannot fan one frame out to the whole table');

    // --- seam 6: leaving, parking, and coming back -------------------------
    //
    // SOURCE-LEVEL FOR THE SAME REASON AS EVERYTHING ELSE IN THIS BLOCK, and
    // with more at stake than most of it. Every other part of this feature is
    // exercised for real above: the engine keeps the seat, the driver paces
    // it, the transport delivers the goodbye, leftTable() reads the record,
    // the renderer offers the buttons. What is left is the ORDER in which
    // main.js does five things, and each of the orders below is one that
    // reads as equivalent, runs without an error, and loses something:
    //
    //   * say goodbye AFTER tearing down, and the frame goes onto a channel
    //     that is already shut — trySend() eats the error and the other end
    //     climbs the reconnect ladder exactly as if no frame existed;
    //   * park the session AFTER going home, and goHome() has already cleared
    //     it — for a host that is the only copy of the match;
    //   * resume at boot BEFORE looking at `left`, and a player who pressed
    //     LEAVE is back in their seat the next time the page loads.
    //
    // None of those fails a behavioural test, because main.js cannot be
    // imported here. They are checked as text because the alternative is that
    // they are checked by a comment.
    {
      const before = (body, a, b) => body.indexOf(a) !== -1 && body.indexOf(b) !== -1
        && body.indexOf(a) < body.indexOf(b);

      const lg = balanced(mainFlat, 'leaveGame() {');
      ok(lg !== null, 'leaveGame() was found to check');
      if (lg) {
        // THE HOST'S HALF.
        ok(before(lg, 'saveEngineSnapshot(engine.serialize())', 'partWith(host)'),
          'a host flushes the engine to disk before letting go of it — the debounced write may be seconds behind');
        ok(before(lg, 'host.broadcast(hostLeftFrame())', 'partWith(host)'),
          'and tells the table it is going BEFORE the transport is put down');
        ok(before(lg, 'partWith(host)', 'host = null') && before(lg, 'host = null', 'intents.goHome()'),
          'and takes the handle out of `host` before goHome() tears down, or teardown() destroys it with the goodbye still queued');
        // THE PLAYER'S HALF.
        ok(before(lg, 'client.send(leaveFrame())', 'partWith(client)'),
          'a player says goodbye before the transport is put down');
        ok(before(lg, 'partWith(client)', 'client = null') && before(lg, 'client = null', 'intents.goHome()'),
          'and likewise keeps the handle out of teardown()\'s reach');
        // BOTH RECORDS ARE WRITTEN BEFORE goHome(), which decides what to keep
        // by reading them. The other order clears first and parks nothing.
        const parks = [...lg.matchAll(/saveSession\(\{[^}]*\}\)/g)];
        eq(parks.length, 2, 'leaveGame() parks a session in two places — one per role');
        for (const p of parks) {
          ok(/left:\s*true/.test(p[0]), `and marks it left: ${p[0].replace(/\s+/g, ' ').slice(0, 60)}…`);
          ok(p.index < lg.indexOf('intents.goHome()'), 'before goHome() reads it');
        }
        ok(/role:\s*'host'/.test(parks.map((p) => p[0]).join()) && /role:\s*'client'/.test(parks.map((p) => p[0]).join()),
          'under the role that was actually being played');
        // GATED ON THERE BEING SOMETHING TO COME BACK TO. An unconditional
        // park would offer RESUME for a lobby, and "your seat is kept" for a
        // seat the engine has already removed.
        ok(before(lg, 'matchUnderWay(engine.phase)', "role: 'host'"),
          'a host parks only a match that is under way');
        ok(before(lg, 'holdsSeatInMatch()', "role: 'client'"),
          'and a player only a seat that is actually being held for them');
        ok(!lg.includes('clearSession'),
          'and leaveGame() clears nothing itself — that is goHome()\'s decision, made after the record exists');
        ok(!lg.includes('teardown()'),
          'nor tears down directly, which would run before the goodbye had a handle to linger on');
      }

      // goHome() KEEPS A PARKED TABLE AND CLEARS A LIVE ONE, and asks
      // leftTable() which is which. An unconditional clearSession() here is
      // the old behaviour and is the edit a tidy-up would make: it reads as
      // simpler, passes everything else in this file, and deletes a host's
      // game the first time a resume fails on a flaky broker.
      const gh = balanced(mainFlat, 'goHome() {');
      ok(gh !== null, 'goHome() was found to check');
      if (gh) {
        ok(/app\.left\s*=\s*leftTable\(\)/.test(gh), 'goHome() asks storage whether a table was left');
        ok(/if\s*\(!app\.left\)\s*clearSession\(\)/.test(gh), 'and clears the session only when none was');
        eq((gh.match(/clearSession\(/g) || []).length, 1, 'with no second, unconditional clear anywhere in it');
        ok(before(gh, 'teardown()', 'leftTable()'), 'after tearing down, so nothing still running can write a record behind it');
      }

      // BOOT OFFERS A PARKED TABLE; IT DOES NOT RESUME IT.
      const rs = funcBody(mainFlat, 'resume');
      ok(rs !== null, 'resume() was found to check');
      if (rs) {
        ok(/session\.left\s*===\s*true/.test(rs), 'resume() looks at whether the session was left');
        const gate = rs.search(/session\.left\s*===\s*true/);
        ok(gate !== -1 && gate < rs.indexOf('beginHost(') && gate < rs.indexOf('beginJoin('),
          'and does so before it would dial anything');
      }
      // Scoped to what follows resume(), which is boot. goHome() makes the
      // same assignment four hundred lines up, and a search of the whole file
      // would be satisfied by that one with the boot line deleted.
      const boot = mainFlat.slice(mainFlat.search(/function\s+resume\s*\(/));
      ok(before(boot, 'app.left = leftTable();', 'const watchCode'),
        'and the offer is read into app before boot paints the home screen');

      // THE HOME CARD'S INTENT RE-READS STORAGE AT THE TAP. app.left is a copy
      // made when the card was drawn; acting on it would resume whatever the
      // record USED to say.
      const rt = balanced(mainFlat, 'resumeTable() {');
      ok(rt !== null, 'resumeTable() was found to check');
      if (rt) {
        ok(before(rt, 'leftTable()', 'beginHost(') && before(rt, 'leftTable()', 'beginJoin('),
          'resumeTable() asks storage again before it dials');
        ok(!/beginHost\(app\.left|beginJoin\(app\.left/.test(rt), 'and never dials from the copy in app');
        ok(/beginHost\(table\.code,\s*loadEngineSnapshot\(\)\)/.test(rt),
          'a host goes back through the same call a host reload makes, with the snapshot');
        ok(!rt.includes('clearSession'),
          'and a record that is no longer the one on the card is left alone — it may be another tab\'s');
      }

      // THE TABLE GOING AWAY, from the client's side. Both routes into it —
      // the host's goodbye and the ladder running out — end in the same
      // function, and it tears down BEFORE anything else so the close behind
      // a goodbye cannot start the ladder.
      const hg = funcBody(mainFlat, 'hostGone');
      ok(hg !== null, 'hostGone() was found to check');
      if (hg) {
        ok(before(hg, 'teardown()', 'saveSession('), 'hostGone() tears down first');
        ok(/left:\s*true/.test(hg), 'and parks the session rather than leaving it live — a reload must offer, not redial');
        ok(/app\.screen\s*=\s*'hostleft'/.test(hg), 'and lands on the screen that says what happened');
        ok(!hg.includes('clearSession'), 'without clearing the record that the REJOIN button depends on');
      }
      const ohl = balanced(clientLit || '', 'onHostLeft:');
      ok(ohl !== null && ohl.includes('hostGone()'), 'the host\'s goodbye goes through hostGone()');
      const sr2 = funcBody(mainFlat, 'scheduleReconnect');
      ok(sr2 !== null && sr2.includes('hostGone()'), 'and so does a reconnect ladder that has run out of rungs');

      // THE LADDER MOVES ON WHEN A RUNG IS REFUSED. A redial of a host that
      // has gone is answered 'peer-unavailable', as an ERROR — and onError
      // cancels the join timer on its first line. With no reschedule in it,
      // that was the last thing that ever happened: the table sat under
      // "reconnecting…" for good. It is asserted here because a liveTable
      // test cannot see it — the ladder is main.js's, and main.js is not here.
      const oe = balanced(clientLit || '', 'onError:');
      ok(oe !== null, 'the client onError body was located');
      if (oe) {
        ok(oe.includes('clearJoinTimer()') && oe.includes('scheduleReconnect()'),
          'an error on a redial books the next rung, since it has just cancelled the timer that would have');
        ok(/resuming\s*&&/.test(oe), 'and only on a redial — a first join that fails is still an error screen');
      }
      const oo = balanced(clientLit || '', 'onOpen:');
      ok(oo !== null && /clearTimeout\(reconnectTimer\)/.test(oo),
        'and a rung that opens after all cancels the one booked behind it');

      // THE HOST'S onLeave marks the seat as gone on purpose, which is the
      // only thing that distinguishes it from onDisconnect one handler up.
      const ol = balanced(hostLit || '', 'onLeave:');
      ok(ol !== null && /engine\.disconnect\(playerId,\s*\{\s*left:\s*true\s*\}\)/.test(ol),
        'the host tells the engine a seat LEFT, not merely dropped');
      ok(ol !== null && ol.includes('push()'), 'and pushes, so the table sees it at once');
      const od = balanced(hostLit || '', 'onDisconnect:');
      ok(od !== null && /engine\.disconnect\(playerId\)/.test(od),
        'while a plain disconnect still says nothing of the kind');

      // A LINGERING PEER IS FINISHED OFF BEFORE A NEW ONE IS OPENED. For a
      // host the lingering peer is holding the room code on the broker, and
      // RESUME dials that very code.
      const bh = funcBody(mainFlat, 'beginHost');
      ok(bh !== null && before(bh, 'finishParting()', 'createHost('),
        'beginHost() finishes any parting handle before it listens on the code');
      const bj = funcBody(mainFlat, 'beginJoin');
      ok(bj !== null && before(bj, 'finishParting()', 'joinHost('),
        'and beginJoin() before it dials');
      const td2 = balanced(mainFlat, 'function teardown(');
      ok(td2 !== null && !td2.includes('finishParting'),
        'teardown() itself does NOT — it runs straight after the goodbye, and would destroy the handle the goodbye is waiting on');

      ok(/leaveFrame/.test(readRepo('js/main.js').slice(0, 4000)) && /hostLeftFrame/.test(readRepo('js/main.js').slice(0, 4000)),
        'main.js imports both goodbye builders rather than writing the type strings itself');
    }
  }

  console.log(`  main.js teardown discipline: ${guardedNames.join(', ')}`);
}

// ###########################################################################
//
//  CHECKPOINT 9 — THE TRANSPORT, ON A FAKE NETWORK
//
// ###########################################################################

// A table wired the way js/main.js wires it: createHost + applyGameIntent +
// pushState IS the controller, with nothing standing in for one. Each remote
// device chooses its move from the frames IT WAS SENT — through the bot's
// chooser, which takes exactly (pub, priv) — so a whole match played here is
// a match played on what the wire carried and nothing else.
let broker = null;
function liveTable(clock, { code = 'QRTX', config = DEFAULT_CONFIG } = {}) {
  if (peerIdForCode(code) === null) throw new Error(`liveTable: '${code}' is not a room code`);
  const engine = new GameEngine();
  engine.addPlayer(HOST_ID, 'Asha', { clientId: 'host-ticket-0001', isOwner: true });
  engine.setConfig(HOST_ID, config);
  const seen = { open: null, joins: [], watches: [], drops: [], leaves: [], pushes: 0 };
  const clients = [];
  let audit = null;
  const push = () => {
    seen.pushes++;
    host.pushState(engine.publicState(), (id) => engine.privateStateFor(id));
    if (audit) audit();
  };
  const host = createHost(code, {
    onOpen: (c) => { seen.open = c; },
    onJoin: (pid, hello) => {
      seen.joins.push(pid);
      if (!hello) { host.sendTo(pid, rejectFrame('Enter a name first.')); return; }
      const r = engine.addPlayer(pid, hello.name, { clientId: hello.clientId });
      if (!r.ok) { host.sendTo(pid, rejectFrame(r.error)); return; }
      push();
    },
    onWatch: (pid, accepted) => {
      seen.watches.push([pid, accepted]);
      if (!accepted) host.sendTo(pid, rejectFrame('This table already has as many screens watching as it can carry.'));
    },
    onData: (pid, msg) => {
      const { handled, result } = applyGameIntent(engine, pid, msg, clock.elapsed());
      if (!handled) return;
      if (!result.ok) host.sendTo(pid, rejectFrame(result.error));
      push();
    },
    onDisconnect: (pid) => { seen.drops.push(pid); engine.disconnect(pid); push(); },
    onLeave: (pid) => { seen.leaves.push(pid); engine.disconnect(pid, { left: true }); push(); },
  });
  clock.advance(10);

  const join = (name, ticket, identity) => {
    const box = { name, ticket, states: [], rejects: [], hostLeft: 0, closes: 0 };
    box.net = joinHost(code, {
      onState: (pub, priv) => box.states.push({ pub, priv }),
      onHostLeft: () => { box.hostLeft++; },
      onData: (msg) => { const r = readRejectFrame(msg); if (r) box.rejects.push(r); },
      onClose: () => { box.closes++; },
    }, identity === undefined ? { name, clientId: ticket } : identity);
    box.last = () => box.states[box.states.length - 1] || null;
    box.seat = () => (box.last() && box.last().priv ? box.last().priv.seat : -1);
    clients.push(box);
    clock.advance(10);
    return box;
  };
  const setAudit = (fn) => { audit = fn; };
  return { engine, host, seen, clients, join, push, setAudit };
}

/**
 * One step of a table on the wire: the host ticks the clock and its bot
 * driver; then whichever device owes a move makes it — a remote one by
 * sending a frame chosen from its own last frame, the host by a local call.
 * Returns false once there is nothing left to do but the owner's next-deal.
 */
function wireStep(clock, table, bots) {
  const { engine, push } = table;
  clock.advance(50);
  const now = clock.elapsed();
  // As main.js's loop does it: both asked, the answers OR-ed, one push.
  const moved = engine.tick(now);
  const acted = bots.tick(engine, now);
  if (moved || acted) push();
  if (engine.phase === PHASES.FIRST_FOUR || engine.phase === PHASES.LAST_FOUR || engine.sweepAt !== null) {
    clock.advance(Math.max(FIRST_FOUR_MS, LAST_FOUR_MS, TRICK_PAUSE_MS));
    if (engine.tick(clock.elapsed())) push();
    return true;
  }
  for (const c of table.clients) {
    const last = c.last();
    if (!last || !last.priv || !c.net.isOpen()) continue;
    const intent = chooseIntent(last.pub, last.priv);
    if (intent) { c.net.send(intent); clock.advance(5); return true; }
  }
  const hostPriv = engine.privateStateFor(HOST_ID);
  const intent = chooseIntent(engine.publicState(), hostPriv);
  if (intent) {
    const { result } = applyGameIntent(engine, HOST_ID, intent, clock.elapsed());
    if (!result.ok) { failed++; console.error('  ✗ FAIL: the host\'s own move was refused:', result.error); }
    push();
    return true;
  }
  if (engine.phase === PHASES.DEAL_OVER) {
    applyGameIntent(engine, HOST_ID, { type: 'nextDeal' }, clock.elapsed());
    push();
    return true;
  }
  // Somebody covered is thinking: let the bot clock run.
  clock.advance(BOT_THINK_MS);
  return engine.phase !== PHASES.MATCH_OVER;
}

// ===========================================================================
section('The transport: four devices and a TV, a whole match on the wire');
// ===========================================================================
{
  const net = installPeerJS();
  broker = net.broker;
  const { clock } = net;
  const table = liveTable(clock, { config: ALL_CONFIGS[15] });
  eq(table.seen.open, 'QRTX', 'the host listens on the code');
  const devices = ['Ben', 'Cleo', 'Dev'].map((n, i) => table.join(n, `ticket-${n.toLowerCase()}-000${i}`));
  const tv = table.join(null, null, WATCHER);
  clock.advance(20);
  eq(table.engine.seats.filter(Boolean).length, SEATS, 'three joiners and the host make four seats');
  same(table.seen.watches.map(([, a]) => a), [true], 'and the TV was let in as a watcher');
  eq(table.engine.seats.filter((s) => s && s.isBot).length, 0, 'with no bot needed');
  ok(table.engine.startMatch(HOST_ID, clock.elapsed()).ok, 'the owner starts the match');
  table.push();

  // --- the audit, at push time -------------------------------------------
  //
  // After every push, while the engine still holds exactly what was sent: each
  // connection's last frame is decoded through the client's own front door; a
  // seat's frame carries THAT seat's private half and nobody else's; the TV's
  // carries none; and — the concealed trump, on the wire — each frame not
  // entitled to the trump is byte-identical to the frame the same connection
  // would have been sent had the hidden card been a different suit.
  let frames = 0, misrouted = 0, tvPriv = 0, leaks = 0, swapped = 0, structural = 0, undecodable = 0, unfaithful = 0;
  table.setAudit(() => {
    const e = table.engine;
    let alt = null, same0 = null, entitled = -1;
    if (e.indicator && !e.revealed) {
      const pool = [];
      for (let s = 0; s < SEATS; s++) if (s !== e.bidder) for (const c of e.hands[s]) if (suitOf(c) !== suitOf(e.indicator)) pool.push(c);
      if (pool.length) {
        alt = cloneEngine(e);
        same0 = cloneEngine(e);
        swapHidden(alt, alt.indicator, pick(pool));
        entitled = e.trumpMode === 'concealed' ? e.bidder : -1;
      }
    }
    for (const [connId, conn] of table.host.connections) {
      const raw = conn.sent[conn.sent.length - 1];
      if (raw === undefined) continue;
      frames++;
      const msg = decodePeerFrame(raw);
      const read = msg && readStateFrame(msg);
      if (!read) { undecodable++; continue; }
      if ('hands' in read.pub || 'stock' in read.pub || 'trumpCard' in read.pub
        || (read.pub.indicator && read.pub.indicator.card && !read.pub.revealed)) structural++;
      const pid = playerIdForConn(connId);
      const seat = e.seatOf(pid);
      if (JSON.stringify(msg) !== JSON.stringify(JSON.parse(JSON.stringify(stateFrameFor(connId, e.publicState(), (id) => e.privateStateFor(id)))))) unfaithful++;
      if (seat === -1) { if (read.priv) tvPriv++; }
      else if (!read.priv || read.priv.seat !== seat) misrouted++;
      if (alt && seat !== entitled) {
        // A seat that holds the card swapped in sees its own hand change, and
        // is entitled to; the comparison is for everybody else.
        const holder = seat !== -1 && alt.hands[seat].join() !== e.hands[seat].join();
        if (holder) continue;
        swapped++;
        const would = stateFrameFor(connId, alt.publicState(), (id) => alt.privateStateFor(id));
        // Clone against clone: cloneEngine() goes through serialize/restore,
        // which marks every seat away, so the original's frame is not the
        // baseline — an unswapped clone is.
        const base = stateFrameFor(connId, same0.publicState(), (id) => same0.privateStateFor(id));
        if (JSON.stringify(would) !== JSON.stringify(base)) leaks++;
      }
    }
  });

  const bots = createBotDriver();
  let guard = 0;
  while (table.engine.phase !== PHASES.MATCH_OVER && guard++ < 20000) wireStep(clock, table, bots);
  eq(table.engine.phase, PHASES.MATCH_OVER, `the match was played to the end over the wire (${table.engine.history.length} deals)`);
  eq(undecodable, 0, `all ${frames} frames read back through the client's own front door`);
  eq(unfaithful, 0, 'every frame on the wire is exactly what the engine says that connection may see');
  eq(misrouted, 0, 'every seat was sent its own private half, and only its own');
  eq(tvPriv, 0, 'the TV was never sent a private half');
  eq(structural, 0, 'no frame carried the hands, the stock or the hidden card');
  eq(leaks, 0, `and no frame changed with the hidden trump swapped (${swapped} compared at push time)`);
  ok(swapped > 500, 'over enough frames for that to mean something');
  console.log(`  ${table.engine.history.length} deals, ${table.seen.pushes} pushes, ${frames} frames audited, ${swapped} of them against a swapped trump`);
  clock.advance(50);   // the last push is still in flight
  for (const c of [...devices, tv]) eq(c.rejects.length, 0, `${c.name || 'the TV'} had nothing refused`);
  const final = table.engine.publicState();
  for (const c of [...devices, tv]) same(c.last().pub, JSON.parse(JSON.stringify(final)), `${c.name || 'the TV'} ends on the host's final state`);
  net.uninstall();
}

// ===========================================================================
section('The transport: the TV cap, and a fifth screen turned away');
// ===========================================================================
{
  const net = installPeerJS();
  broker = net.broker;
  const { clock } = net;
  const table = liveTable(clock);
  const screens = [];
  for (let i = 0; i <= MAX_WATCHERS; i++) screens.push(table.join(null, null, WATCHER));
  clock.advance(50);
  eq(MAX_WATCHERS, MAX_HOST_CONNS - 4 * (SEATS - 1), `the watcher cap is derived — ${MAX_WATCHERS}`);
  eq(table.seen.watches.filter(([, a]) => a).length, MAX_WATCHERS, `${MAX_WATCHERS} screens were let in`);
  eq(table.seen.watches.filter(([, a]) => !a).length, 1, 'and the one past the cap was turned away');
  ok(screens[MAX_WATCHERS].rejects.length === 1, 'and told why');
  // A watcher never takes a seat, so the seats are still all there for players.
  for (const n of ['Ben', 'Cleo', 'Dev']) table.join(n, `ticket-${n.toLowerCase()}-0000`);
  clock.advance(20);
  eq(table.engine.seats.filter(Boolean).length, SEATS, 'with the TVs at their cap, three players still sit down');
  net.uninstall();
}

// ===========================================================================
section('The transport: a phone dies mid-match, a player leaves, and both come back');
// ===========================================================================
{
  const net = installPeerJS();
  broker = net.broker;
  const { clock } = net;
  const table = liveTable(clock);
  const [ben, cleo, dev] = ['Ben', 'Cleo', 'Dev'].map((n, i) => table.join(n, `ticket-${n.toLowerCase()}-000${i}`));
  clock.advance(20);
  table.engine.startMatch(HOST_ID, clock.elapsed());
  table.push();
  const bots = createBotDriver();
  // Play until a deal is scored and the next has a concealed trump held by a
  // remote seat, so the rejoin has a scoreboard AND a bidder's trump to bring
  // back.
  let guard = 0;
  const remote = { [ben.ticket]: ben, [cleo.ticket]: cleo, [dev.ticket]: dev };
  const bidderBox = () => {
    const e = table.engine;
    if (e.bidder === null || e.trumpMode !== 'concealed' || e.revealed || e.phase !== PHASES.PLAY) return null;
    const s = e.seats[e.bidder];
    return Object.values(remote).find((c) => c.seat() === e.bidder && s.id !== HOST_ID) || null;
  };
  while (guard++ < 20000 && !(table.engine.history.length >= 1 && bidderBox())) {
    if (table.engine.phase === PHASES.MATCH_OVER) break;
    wireStep(clock, table, bots);
  }
  const victim = bidderBox();
  ok(victim, 'reached a deal with a remote bidder holding a concealed trump, after a scored deal');
  if (victim) {
    const seat = victim.seat();
    const before = victim.last();
    ok(before.priv.indicator, 'the bidder was sent their own hidden card');
    const scoreBefore = JSON.stringify(table.engine.publicState().gamePoints);
    const historyBefore = table.engine.history.length;

    // THE PHONE DIES. The seat is kept, marked away; nobody moves for it
    // until the grace period has run.
    victim.net.destroy();
    clock.advance(100);
    ok(table.seen.drops.length === 1, 'the host saw the drop');
    const kept = table.engine.seats[seat];
    ok(kept && !kept.connected && !kept.left && !kept.isBot, 'the seat is kept, away, and not turned into a bot');

    // AND COMES BACK on the same ticket.
    const back = table.join(victim.name, victim.ticket);
    clock.advance(20);
    eq(back.seat(), seat, 'the same ticket gets the same seat back');
    eq(JSON.stringify(back.last().pub.gamePoints), scoreBefore, 'with the scoreboard as it was');
    eq(back.last().pub.history.length, historyBefore, 'and every deal of the history');
    eq(back.last().priv.indicator, before.priv.indicator, 'and the bidder\'s own hidden trump, still known only to them');
    same(back.last().priv.hand.map((c) => c.code), before.priv.hand.map((c) => c.code), 'and the same hand');

    // LEAVING ON PURPOSE: covered at bot pace at once, not after the grace.
    const leaver = [ben, cleo, dev].find((c) => c !== victim && c.net.isOpen());
    const lseat = leaver.seat();
    leaver.net.send(leaveFrame());
    clock.advance(20);
    eq(table.seen.leaves.length, 1, 'the host heard the goodbye as a LEAVE, not a drop');
    ok(table.engine.seats[lseat].left, 'and marked the seat as left');
    ok(!table.engine.seats[lseat].isBot, 'covered, not converted');
    // Drive the others until the table waits on the seat that left, then time
    // how long the cover takes: a bot's think, not the dropped-phone grace.
    const others = { ...table, clients: table.clients.filter((c) => c !== leaver) };
    const owes = (e) => (e.phase === PHASES.PLAY && e.sweepAt === null && e.turnSeat === lseat)
      || ((e.phase === PHASES.AUCTION || e.phase === PHASES.DECLARE) && e.turnSeat === lseat)
      || (e.phase === PHASES.TRUMP_CHOICE && e.bidder === lseat);
    const moment = (e) => JSON.stringify([e.phase, e.dealIndex, e.plays.length, e.auction.calls.length, e.trickIndex, e.declare && e.declare.at]);
    let waited = null;
    for (let i = 0; i < 4000 && waited === null && table.engine.phase !== PHASES.MATCH_OVER; i++) {
      const e = table.engine;
      if (!owes(e)) { wireStep(clock, others, bots); continue; }
      const key = moment(e);
      const from = clock.elapsed();
      bots.tick(e, from);
      for (let t = 0; t <= OFFLINE_GRACE_MS && moment(e) === key; t += 100) {
        clock.advance(100);
        if (bots.tick(e, clock.elapsed())) table.push();
      }
      waited = clock.elapsed() - from;
    }
    console.log(`  rejoined seat ${seat} at ${scoreBefore} after ${historyBefore} deal(s); a left seat covered in ${waited}ms`);
    ok(waited !== null && waited <= BOT_THINK_MS + 100, `a seat that LEFT is covered at bot pace (${waited}ms), not after the ${OFFLINE_GRACE_MS}ms grace`);

    // AND THE ONE WHO LEFT COMES BACK too.
    const back2 = table.join(leaver.name, leaver.ticket);
    clock.advance(20);
    eq(back2.seat(), lseat, 'the player who left reclaims their seat on the same ticket');
    ok(!table.engine.seats[lseat].left && table.engine.seats[lseat].connected, 'and it is theirs again, not covered');

    // A STRANGER'S TICKET gets no seat at a full table mid-match.
    const stranger = table.join('Mallory', 'ticket-mallory-0000');
    clock.advance(20);
    eq(stranger.seat(), -1, 'a new ticket mid-match takes nobody\'s seat');
  }

  // THE HOST LEAVING: every device is told, and told why.
  table.host.broadcast(hostLeftFrame());
  clock.advance(20);
  ok(table.clients.filter((c) => c.hostLeft === 1).length >= 3, 'the host\'s goodbye reached every connected device');
  net.uninstall();
}

// ===========================================================================
section('The shell: every asset shipped, and every asset cached');

{
  // --- SHELL against the disk, in both directions ---------------------------
  //
  // The rule sw.js states is "everything in js/ and css/ and icons/". A rule
  // is only worth writing down if something checks it, and the thing that
  // would otherwise check it is somebody remembering, three weeks from now,
  // while adding a module. The failure they would cause is invisible online
  // and total offline, which is the worst place for it to hide.
  //
  // DERIVED FROM THE DISK, not from a second copy of the list. A hand-written
  // expected list here would agree with a hand-written SHELL exactly as often
  // as both were edited together, which is the thing being guarded against.

  // Executing the file rather than regexing it, via loadSwConsts() at the top
  // — shared with --write-stamp so that the writer and the checker cannot
  // disagree about what sw.js says.
  const constsOnly = loadSwConsts();
  if (constsOnly.error) {
    failed++;
    console.error('  ✗ FAIL: sw.js does not parse —', constsOnly.error.message);
  } else {
    passed++;
  }

  const SHELL = constsOnly.SHELL;
  const CACHE_NAME = constsOnly.CACHE_NAME;
  const SHELL_STAMP = constsOnly.SHELL_STAMP;

  ok(Array.isArray(SHELL) && SHELL.length > 0, 'sw.js exports a non-empty SHELL');
  ok(typeof CACHE_NAME === 'string' && /^twentynine-/.test(CACHE_NAME),
    `the cache name is namespaced to this app — got ${JSON.stringify(CACHE_NAME)}`);

  // EVERY PATH RELATIVE. A leading slash resolves to the origin root, and on a
  // GitHub Pages project site the app lives at /<repo>/ — so '/js/main.js'
  // would 404 during install, addAll would reject, and the worker would never
  // activate at all. Silently: the only symptom is that offline never works.
  let absolute = 0;
  for (const p of SHELL) if (!p.startsWith('./')) { absolute++; console.error('  ✗ not relative:', p); }
  eq(absolute, 0, `all ${SHELL.length} SHELL paths are relative, so a Pages subpath survives`);

  // No duplicates. addAll tolerates them, but a duplicate means the list was
  // edited twice by two people who each thought they were adding it.
  eq(new Set(SHELL).size, SHELL.length, 'and no path is listed twice');

  // --- direction one: everything in SHELL exists ----------------------------
  let missing = 0;
  for (const p of SHELL) {
    // './' is the directory, served as index.html — there is no file of that
    // name to stat, and it is listed deliberately (see the comment in sw.js).
    if (p === './') continue;
    try { readFileSync(REPO + p.slice(2)); } catch (_) {
      missing++; console.error('  ✗ SHELL lists a file that is not there:', p);
    }
  }
  eq(missing, 0, 'every file SHELL precaches is actually in the repository');

  // --- direction two: everything on disk is in SHELL ------------------------
  //
  // This is the direction that catches the real mistake. The one above only
  // fails when a file is DELETED, which somebody notices; this one fails when
  // a file is ADDED, which is the case nobody notices.
  const listed = new Set(SHELL);
  let unlisted = 0;
  let onDisk = 0;
  for (const dir of ['js', 'css', 'icons']) {
    for (const name of readdirSync(REPO + dir)) {
      onDisk++;
      if (!listed.has(`./${dir}/${name}`)) {
        unlisted++;
        console.error(`  ✗ ${dir}/${name} is shipped but never precached`);
      }
    }
  }
  eq(unlisted, 0, `and all ${onDisk} files under js/, css/ and icons/ are in it`);
  // The pairing. "Nothing unlisted" is also true of an empty directory, and an
  // empty directory is what a broken REPO path would produce.
  ok(onDisk >= 17, `with ${onDisk} files actually found to check — the sweep is not empty`);

  // The page and the manifest are not under those three directories, so they
  // are named rather than swept. Without this, deleting './index.html' from
  // SHELL would pass everything above and break offline completely.
  for (const must of ['./', './index.html', './manifest.webmanifest']) {
    ok(listed.has(must), `SHELL precaches ${must}`);
  }

  // NOTHING CROSS-ORIGIN, EVER. This is the beacon rule stated as an
  // assertion: a precached PeerJS bundle is a stale library, and a precached
  // signalling response is a room code that connects to a conversation that
  // ended yesterday.
  let external = 0;
  for (const p of SHELL) if (/^https?:|^\/\//.test(p)) { external++; console.error('  ✗ external:', p); }
  eq(external, 0, 'and not one byte of anybody else’s origin is precached');

  // --- the stamp ------------------------------------------------------------
  //
  // THE CHECK THIS WHOLE SECTION EXISTED WITHOUT. Everything above asks
  // "does SHELL name the right files"; none of it asks "does CACHE_NAME
  // change when those files do", and that second question is the one that
  // decides whether a returning visitor ever sees a fix.
  //
  // The failure is not hypothetical and it is not rare. caches.addAll() is a
  // no-op against a cache that already exists under the name being opened, so
  // a deploy that keeps the name keeps serving the old bytes to everyone who
  // has visited before — forever, silently, with a green suite. It happened
  // here: five user-visible bugs were fixed across six files with the cache
  // name left at 'v1', and the only thing between those fixes and the people
  // they were for was somebody remembering to edit one line.
  //
  // A hand-written version number cannot be checked, because no test can know
  // whether you MEANT the bytes to change. A fingerprint of the bytes can, and
  // that is the entire reason sw.js carries a hash instead of a counter.
  //
  // NOTE WHAT MAKES THIS COMPUTABLE AT ALL: sw.js is not in SHELL. A worker
  // does not precache itself, so the file holding the hash is not among the
  // files being hashed, and there is no fixed point to solve for. If somebody
  // ever adds './sw.js' to the list, this stops being arithmetic and starts
  // being impossible — so that is asserted rather than assumed.
  ok(!SHELL.includes('./sw.js'),
    'sw.js does not precache itself — which is what makes a content stamp computable');

  // The hash itself lives in shellStampOf() at the top of this file, because
  // --write-stamp computes the same number and a second copy of the rule is a
  // second rule. See the comment there.
  //
  // Hoisted out of the block below because the writer section further down
  // compares against `computed` rather than against SHELL_STAMP. That is not a
  // style choice: comparing the writer's answer to the file's literal would
  // make the writer's assertions fail on every legitimately stale stamp, which
  // in the mutation table means every row in it — and a diagnosis column that
  // says the same thing for sixty different mutations has stopped being a
  // diagnosis. Writer-agrees-with-checker is the property; is-the-file-current
  // is already asserted once, below, and does not need saying twice.
  const { stamp: computed, hashed, unreadable } = shellStampOf(SHELL);

  {
    // The pairing. A hash of nothing is still a hash, and it would compare
    // unequal and print a confident-looking value to paste. If the files could
    // not be read, say THAT instead.
    eq(unreadable, 0, 'every file in the stamp could be read off disk');
    ok(hashed >= 20, `the stamp is computed over ${hashed} files, not over an empty sweep`);

    if (SHELL_STAMP !== computed) {
      // THE FAILURE FIXES ITSELF. This is the difference between a check that
      // enforces a rule and a check that nags about one: nobody has to work
      // out what the new stamp is, or know that line endings are normalised.
      // They run one command. "Remember to bump this" becomes "the suite bumps
      // it" — and the paste-this line stays below it for anyone who would
      // rather see the twelve characters before a script touches their file.
      console.error('  ✗ FAIL: sw.js SHELL_STAMP is stale — the shell changed and the cache name did not.');
      console.error('           Returning visitors would keep the old build. Fix it with:');
      console.error('               npm run stamp');
      console.error(`           (or paste: const SHELL_STAMP = '${computed}';`);
      console.error(`            currently '${SHELL_STAMP}', over ${hashed} files)`);
    }
    eq(SHELL_STAMP, computed, 'SHELL_STAMP is the fingerprint of the files SHELL precaches');

    // And the stamp has to actually be the cache name, or it is decoration.
    // DERIVED from SHELL_STAMP rather than written out: a literal here would
    // be a third copy of the same string to keep in step, and the prefix is
    // load-bearing on its own — the activate handler deletes by it, which is
    // what stops this worker clearing a sibling project's caches on the same
    // github.io origin.
    eq(CACHE_NAME, `twentynine-shell-${SHELL_STAMP}`,
      'and the cache is named after it, with the prefix activate() deletes by');

    console.log(`  shell stamp: ${SHELL_STAMP} over ${hashed} files`);
  }

  // --- the writer that fixes a stale stamp ----------------------------------
  //
  // `npm run stamp` rewrites the line the check above enforces, which makes it
  // the one piece of tooling in the repository that can turn this section
  // green without anybody fixing anything. Its guards are therefore not a
  // convenience — they are the reason it is allowed to exist — and they are
  // driven here with inputs that could not be produced any other way without
  // damaging the working tree to test the thing that protects it.
  {
    const realSw = loadSwConsts();
    const plan = planStampWrite(realSw);

    // THE HAPPY PATH FIRST, because every refusal below is only interesting if
    // the writer would otherwise have said yes.
    eq(plan.refuse, null, 'the stamp writer accepts the repository as it stands');
    // AGAINST `computed`, NOT AGAINST THE FILE'S LITERAL. The property is that
    // the writer and the checker arrive at the same number, and that stays
    // true while the stamp is stale — which is the state the writer exists to
    // resolve and the state every mutation in the table puts the tree into.
    eq(plan.stamp, computed,
      'and the number it would write is the number the check above demands — the writer and the checker cannot disagree');
    eq(plan.was, SHELL_STAMP, 'it read the current value out of the file correctly');

    // It rewrites the declaration and NOTHING ELSE. The sharpest way to say
    // that is by length: a replacement of one twelve-character stamp with
    // another leaves the file exactly as long, and any collateral edit —
    // dropping the rest of the line, matching inside a comment, eating a
    // newline — moves it. Derived from the real file so it stays true when
    // sw.js grows.
    const rewritten = realSw.src.replace(STAMP_ANCHOR, `const SHELL_STAMP = '${'0'.repeat(12)}';`);
    eq(rewritten.length, realSw.src.length, 'writing a stamp changes the file length by nothing');
    eq((rewritten.match(new RegExp(STAMP_ANCHOR.source, 'gm')) || []).length, 1,
      'and leaves exactly one stamp declaration behind');
    ok(rewritten.includes("const SHELL_STAMP = '000000000000';"),
      'and the line it leaves is the one it meant to write');

    // IDEMPOTENT. Running it twice must not produce a different file the
    // second time, or "run it until it settles" becomes a real instruction.
    eq(planStampWrite(realSw).next, plan.next, 'planning the same write twice plans the same bytes');

    // --- and now every way it must refuse ------------------------------------
    //
    // Each of these is a state in which the writer would otherwise paste a
    // confident-looking twelve characters over the deploy blocker, and the
    // checker would then agree with it. A wrong stamp is strictly worse than a
    // stale one: stale is caught on the next run, wrong is never caught again.
    const refusals = [
      ['sw.js does not parse',
        { ...realSw, error: new Error('Unexpected token') }, /does not parse/],
      ['SHELL comes back empty',
        { ...realSw, SHELL: [] }, /no usable SHELL/],
      ['SHELL is not an array at all',
        { ...realSw, SHELL: null }, /no usable SHELL/],
      // The one that matters most. A rename that misses this list leaves paths
      // that read perfectly well and hash to nothing, and the digest of the
      // remaining files is a real number that is not the right number.
      ['a file in SHELL is not on disk',
        { ...realSw, SHELL: [...realSw.SHELL, './js/does-not-exist.js'] }, /could not be read/],
      ['the sweep is too small to be the shell',
        { ...realSw, SHELL: ['./index.html', './css/app.css'] }, /only 2 files/],
      // Two anchors means the file is not shaped the way the writer assumes,
      // and "edit the first one" is a guess. Built by duplicating the real
      // line rather than by writing a second one out, so it stays a duplicate.
      // These two match on `^found N ` rather than on the full refusal text,
      // and that is about the MUTATION HARNESS rather than about the writer.
      // scripts/_mutate-fixes.mjs decides which failure line to report by
      // stepping over anything matching /SHELL_STAMP/ — every mutation makes
      // the stamp stale, so that line is noise in sixty rows out of sixty. A
      // failure message here that quoted the token verbatim would be swept up
      // by that filter and scored as "only the stamp moved", i.e. as a
      // mutation nothing caught. The assertion still checks the real string;
      // it just does not repeat the word in its own name.
      ['sw.js carries two stamp declarations',
        { ...realSw, src: realSw.src.replace(STAMP_ANCHOR, (m) => `${m}\n${m}`) }, /^found 2 /],
      ['sw.js carries none the writer recognises',
        { ...realSw, src: realSw.src.replace(STAMP_ANCHOR, 'const SHELL_STAMP = shellStamp();') },
        /^found 0 /],
    ];

    for (const [what, broken, why] of refusals) {
      const got = planStampWrite(broken);
      ok(typeof got.refuse === 'string' && why.test(got.refuse),
        `the stamp writer refuses when ${what} — expected /${why.source}/, got ${JSON.stringify(got.refuse)}`);
      // AND THE REFUSAL IS THE WHOLE ANSWER. A reason string beside a usable
      // `next` is a writer that explains itself and then does it anyway, which
      // is the failure mode a caller reading only one field would never see.
      //
      // ok() AND NOT eq(), which is not a style preference. eq() prints the
      // value it got, and the value here would be an entire copy of sw.js:
      // unreadable on its own terms, and — because that copy contains the
      // string SHELL_STAMP — swept up by the mutation harness's noise filter,
      // which steps over stamp failures because every mutation causes one.
      // The row for this assertion came back ONLY THE STAMP, scoring a caught
      // mutation as an uncaught one, while the assertion underneath it was
      // firing exactly as intended. An assertion message is read by tooling as
      // well as by people.
      ok(got.next === null, `and produces no replacement text when ${what}`);
    }

    // Nothing above touched the disk — the point of planning separately from
    // writing — so say so rather than leaving it to be inferred.
    eq(loadSwConsts().SHELL_STAMP, SHELL_STAMP,
      'and none of that moved the stamp in the actual file');
  }

  // --- and the writer cannot be smuggled into the check ---------------------
  //
  // THE ONE WAY THE ABOVE CAN BE MADE MEANINGLESS. --write-stamp gives this
  // file permission to edit sw.js, and the assertion three lines up is the
  // thing it is allowed to edit its way out of. Those two facts are safe apart
  // and dangerous together, and the only thing keeping them apart is that
  // nobody runs the writer as part of the check.
  //
  // "Nobody does that today" is a property of the callers, not of the code —
  // the same sentence that preceded half the findings in this repository. The
  // realistic version is not malice: it is a green suite on a machine where
  // the stamp keeps going stale, somebody appends the flag to the test script
  // to stop the noise, and from then on every run repairs the deploy blocker
  // it was written to catch and reports 121,000 passes while doing it. There
  // would be no failing test, because the test would have been fixed.
  //
  // So the fence is asserted, not just described in the comment beside it.
  // Checking process.argv here would prove nothing — this line only runs on
  // the branch where the flag was absent. What has to be checked is the
  // COMMAND, which is the thing a future reader would actually edit.
  {
    const pkg = JSON.parse(readRepo('package.json'));
    const scripts = pkg.scripts || {};

    ok(typeof scripts.test === 'string' && scripts.test.includes('test-engine.mjs'),
      'package.json still runs the suite from npm test');
    ok(!/--write-stamp/.test(scripts.test || ''),
      'and npm test does NOT pass --write-stamp — the runner cannot rewrite the stamp it is checking');

    // The writer needs a way in of its own, or the pressure to put it in the
    // test script comes straight back. Derived from the flag string rather
    // than from a copy of the whole command: what matters is that some script
    // offers it and that it is not the one CI runs.
    const offering = Object.entries(scripts).filter(([, cmd]) => /--write-stamp/.test(cmd));
    eq(offering.length, 1, 'exactly one npm script offers --write-stamp');
    ok(offering.length === 1 && offering[0][0] !== 'test',
      `and it is not the test script — it is npm run ${offering.length === 1 ? offering[0][0] : '?'}`);

    // The failure message above tells the reader to run it by that name, so
    // the name is part of the contract and not a detail of package.json.
    ok(Object.prototype.hasOwnProperty.call(scripts, 'stamp'),
      'the script is called "stamp", which is what the stale-stamp failure tells you to run');
  }

  // --- where the worker lives, as stated in prose ---------------------------
  //
  // sw.js is at the repository ROOT and that is forced, not chosen: a worker's
  // default scope is the directory it is served from, so a worker at
  // ./js/sw.js could only ever control ./js/* and would never see a navigation
  // to the page. Widening scope needs a Service-Worker-Allowed response
  // header, which GitHub Pages does not let you set. So the location is a
  // constraint of the platform, and "move it in with the other modules" is a
  // tidy-up that silently turns offline support off.
  //
  // js/config.js told the next reader to look in js/ for it. That is the
  // cheapest possible bug to ship and among the more expensive to act on,
  // because the person following the instruction concludes the file is missing
  // and writes a new one. Prose is not tested by anything else in this file,
  // so the two halves are asserted TOGETHER: the location is read off the
  // disk, and then no source file is allowed to contradict it. A check that
  // only banned the string would keep passing on the day somebody actually
  // did move the worker.
  let atRoot = true;
  try { readFileSync(REPO + 'sw.js'); } catch (_) { atRoot = false; }
  let inJs = true;
  try { readFileSync(REPO + 'js/sw.js'); } catch (_) { inJs = false; }
  ok(atRoot, 'the service worker is at the repository root, where its scope covers the page');
  ok(!inJs, 'and there is no second copy under js/, which could only ever scope js/*');

  if (atRoot && !inJs) {
    // ONE FILE IS EXEMPT, AND THE EXEMPTION IS A REQUIREMENT.
    //
    // The first version of this check scanned sw.js too and failed on its own
    // header — which says "a worker at ./js/sw.js could only ever control
    // ./js/*". That is the explanation of why the file is not there, not an
    // instruction to look there, and a substring search cannot tell those
    // apart. This project has now been caught by that distinction twice; the
    // rule it keeps learning is that a checker which cries wolf gets ignored
    // on the one line that matters, so the exception is made explicit rather
    // than the check being weakened into uselessness.
    //
    // Making it an exception alone would be a hole big enough to hide the
    // original bug in, so it is inverted: sw.js is the ONE place required to
    // name the path it is not at, because it is the only place a reader will
    // think to ask why. If that explanation ever disappears, this fails.
    const swHeader = readRepo('sw.js').slice(0, 2000);
    ok(/js\/sw\.js/.test(swHeader) && /scope/.test(swHeader),
      'sw.js explains in its own header why it is not under js/ — scope, not preference');

    const PROSE = ['js/main.js', 'js/net.js', 'js/ui.js', 'js/util.js', 'js/bot.js',
      'js/intents.js', 'js/guards.js', 'js/config.js', 'js/state.js', 'js/rules.js',
      'js/scoring.js', 'js/cards.js', 'js/trick.js', 'css/app.css',
      'index.html', 'manifest.webmanifest', 'README.md'];
    const liars = [];
    let scanned = 0;
    for (const f of PROSE) {
      let src;
      try { src = readRepo(f); } catch (_) { continue; }
      scanned++;
      // Both spellings; they send the reader to the same place that is not
      // there, and './' in front changes nothing about that.
      for (const m of src.matchAll(/\.?\/?js\/sw\.js/g)) {
        const line = src.slice(0, m.index).split('\n').length;
        liars.push(`${f}:${line} says ${m[0]}`);
      }
    }
    for (const l of liars) console.error(`  ✗ FAIL: ${l} — the worker is at the repository root`);
    eq(liars.length, 0, 'and no other file tells the next reader to look in js/ for it');
    ok(scanned >= 14, `checked ${scanned} files for it — the sweep is not empty`);
  }
}

{
  // --- driving the worker ---------------------------------------------------
  //
  // A fake Cache API, a fake origin, and — importantly — a fake origin WITH A
  // SUBPATH. Everything below runs as if deployed to
  // https://pages.test/twentynine/, because that is where this is going and
  // because a root-hosted fake would pass happily on paths that 404 on Pages.

  const ORIGIN = 'https://pages.test';
  const BASE = `${ORIGIN}/twentynine/`;
  const abs = (u) => new URL(u, BASE).href;

  let writesOutsideInstall = 0;
  let installing = false;

  class Res {
    constructor(tag, init = {}) { this.tag = tag; this.status = init.status ?? 200; this.type = init.type || 'basic'; }
    static error() { return new Res(null, { status: 0, type: 'error' }); }
  }

  // What the "server" has. Keyed by absolute URL. The directory URL and
  // index.html return the same bytes, exactly as a static host does.
  const SERVER = new Map();
  const publish = (path, tag) => SERVER.set(abs(path), tag);
  publish('./', 'index.html');
  publish('./index.html', 'index.html');
  publish('./manifest.webmanifest', 'manifest');
  publish('./css/app.css', 'app.css');
  for (const m of ['main', 'ui', 'net', 'bot', 'intents', 'guards', 'state', 'rules', 'scoring', 'cards', 'trick', 'util', 'config']) {
    publish(`./js/${m}.js`, `${m}.js`);
  }
  for (const i of ['icon-32', 'icon-192', 'icon-512', 'icon-maskable-512', 'apple-touch-icon']) {
    publish(`./icons/${i}.png`, `${i}.png`);
  }
  publish('./late-addition.txt', 'late'); // on the server, not in SHELL

  let offline = false;
  let networkHits = 0;

  const fakeFetch = async (req) => {
    networkHits++;
    const url = typeof req === 'string' ? abs(req) : req.url;
    if (offline) throw new TypeError('Failed to fetch');
    if (!SERVER.has(url)) return new Res(null, { status: 404 });
    return new Res(SERVER.get(url));
  };

  class FakeCache {
    constructor() { this.store = new Map(); }
    async addAll(paths) {
      // Real addAll is atomic: one rejection and NOTHING is written. Modelled,
      // because the whole argument for using it over a tolerant loop is that
      // a partial cache never exists.
      const fetched = [];
      for (const p of paths) {
        const r = await fakeFetch(abs(p));
        if (r.status !== 200) throw new TypeError(`addAll failed on ${p}`);
        fetched.push([abs(p), r]);
      }
      for (const [k, v] of fetched) this.store.set(k, v);
    }
    async put(req, res) {
      if (!installing) writesOutsideInstall++;
      this.store.set(typeof req === 'string' ? abs(req) : req.url, res);
    }
    async match(req, opts = {}) {
      let url = typeof req === 'string' ? abs(req) : req.url;
      if (this.store.has(url)) return this.store.get(url);
      if (opts.ignoreSearch) {
        const bare = url.split('?')[0];
        for (const [k, v] of this.store) if (k.split('?')[0] === bare) return v;
      }
      return undefined;
    }
    async keys() { return [...this.store.keys()]; }
  }

  const caches_ = new Map();
  const fakeCaches = {
    async open(name) {
      if (!caches_.has(name)) caches_.set(name, new FakeCache());
      return caches_.get(name);
    },
    async keys() { return [...caches_.keys()]; },
    async delete(name) { return caches_.delete(name); },
  };

  // The global scope.
  const handlers = new Map();
  let claimed = 0;
  let skipped = 0;
  const fakeSelf = {
    addEventListener(type, fn) { handlers.set(type, fn); },
    location: { origin: ORIGIN, href: BASE + 'sw.js' },
    clients: { async claim() { claimed++; } },
    // Present so that calling it is OBSERVED rather than thrown. A fake that
    // lacks the method would also "catch" a skipWaiting being added, but as a
    // TypeError — which reports the shape of the fake, not the decision.
    skipWaiting() { skipped++; },
  };

  const swSrc = readRepo('sw.js');
  // eslint-disable-next-line no-new-func
  const meta = new Function('self', 'caches', 'fetch', 'Response',
    swSrc + '\n; return { CACHE_NAME, SHELL };')(fakeSelf, fakeCaches, fakeFetch, Res);

  const CACHE_NAME = meta.CACHE_NAME;

  for (const type of ['install', 'activate', 'fetch']) {
    ok(handlers.has(type), `sw.js registers a ${type} handler`);
  }

  // A browser hands each handler an event and waits on what it is given.
  const fire = async (type, extra = {}) => {
    let waited = null, responded = null;
    const ev = {
      ...extra,
      waitUntil(p) { waited = p; },
      respondWith(p) { responded = p; },
    };
    handlers.get(type)(ev);
    if (waited) await waited;
    return responded ? await responded : null;
  };

  const req = (path, { method = 'GET', mode = 'no-cors', absolute: a = null } = {}) =>
    ({ url: a || abs(path), method, mode });

  // ---------------------------------------------------------------------
  // INSTALL
  // ---------------------------------------------------------------------
  installing = true;
  await fire('install');
  installing = false;

  const cache = await fakeCaches.open(CACHE_NAME);
  ok(caches_.has(CACHE_NAME), 'install opens the cache its version names');
  eq((await cache.keys()).length, meta.SHELL.length,
    'and precaches exactly as many entries as SHELL lists — no more, no fewer');

  // THE CACHE IS KEYED ON THE DEPLOYED URL, not on the relative string. If the
  // worker resolved './js/main.js' against anything but its own scope, this is
  // where a Pages subpath deploy would come apart.
  ok((await cache.match(abs('./js/main.js'))) !== undefined,
    'a module is cached under its subpath-resolved URL, not its relative one');
  ok((await cache.match(`${ORIGIN}/js/main.js`)) === undefined,
    'and NOT under the origin root, which is where a leading slash would have put it');

  eq(claimed, 0, 'install does not claim clients — that is activate’s job');

  // NO skipWaiting, AND THIS IS THE UNPOPULAR CHOICE. Taking over immediately
  // is what most workers do. Here a match runs for nineteen rounds and can
  // outlast a deploy, and a worker that activates underneath a live page lets
  // it load the new js/state.js having already loaded the old js/ui.js. A
  // mixed-version module graph does not throw; it misbehaves, and it
  // misbehaves in the middle of somebody's game. The cost is that an update
  // lands one visit late, which the footer's reset button pays off on demand.
  eq(skipped, 0, 'and does not skip the waiting phase — an update never lands underneath a live match');

  // ---------------------------------------------------------------------
  // ACTIVATE
  // ---------------------------------------------------------------------
  // Seed three caches it should not be confused by: an older version of this
  // app, and two belonging to other apps on the same github.io user.
  caches_.set('twentynine-shell-v0', new FakeCache());
  caches_.set('sequence-shell-v4', new FakeCache());
  caches_.set('courtpiece-v2', new FakeCache());

  await fire('activate');

  ok(!caches_.has('twentynine-shell-v0'), 'activate deletes the previous version of this app');
  ok(caches_.has(CACHE_NAME), 'and keeps the current one');
  // THE ONE THAT MATTERS. A sibling project deployed under the same origin —
  // which is exactly what a user.github.io account is — must not have its
  // offline support wiped by this app shipping an update.
  ok(caches_.has('sequence-shell-v4') && caches_.has('courtpiece-v2'),
    'while leaving both sibling apps on the same origin entirely alone');
  eq(claimed, 1, 'and takes over the page that was already open');

  // ---------------------------------------------------------------------
  // FETCH: what it refuses to touch
  // ---------------------------------------------------------------------
  // `null` back from fire() means respondWith was never called, which is the
  // worker handing the request to the browser untouched.

  // THE BEACON. Every kind of third party the page talks to, all of which
  // must pass straight through. The signalling one is the dangerous one: a
  // cached handshake response is a room code that dials a dead conversation.
  // The last three are GoatCounter — the script, the pageview, and the
  // footer's visitor count — where a cached answer records nothing and shows
  // a number that never moves.
  const foreign = [
    'https://unpkg.com/peerjs@1.5.4/dist/peerjs.min.js',
    'https://fonts.gstatic.com/s/inter/v13/x.woff2',
    'https://0.peerjs.com/peerjs/id?ts=1',
    'https://gc.zgo.at/count.js',
    'https://yvj.goatcounter.com/count?p=%2Ftwentynine%2F',
    'https://yvj.goatcounter.com/counter/%2Ftwentynine%2F.json?start=2026-01-01',
  ];
  let intercepted = 0;
  for (const u of foreign) {
    if (await fire('fetch', { request: req(null, { absolute: u }) }) !== null) {
      intercepted++; console.error('  ✗ intercepted cross-origin:', u);
    }
  }
  eq(intercepted, 0, 'not one cross-origin request is intercepted — the beacon is never touched');

  // The analytics beacon must never be cached: a beacon answered from cache
  // records nothing. The worker does not name either GoatCounter host at all,
  // so no branch can route them and no list can precache them.
  ok(!/gc\.zgo\.at|goatcounter/.test(swSrc.replace(/\/\/[^\n]*/g, '')),
    'the analytics beacon is not routed or precached by the worker');

  // And nothing cross-origin ended up in the cache as a side effect.
  let foreignCached = 0;
  for (const k of await cache.keys()) if (!k.startsWith(ORIGIN)) foreignCached++;
  eq(foreignCached, 0, 'and nothing on anybody else’s origin is in the cache afterwards');

  eq(await fire('fetch', { request: req('./index.html', { method: 'POST' }) }), null,
    'a POST is left to the browser — it is not cacheable and never will be');

  // ---------------------------------------------------------------------
  // FETCH: offline, which is the entire point
  // ---------------------------------------------------------------------
  offline = true;
  const before = networkHits;

  const page = await fire('fetch', { request: req('./', { mode: 'navigate' }) });
  eq(page && page.tag, 'index.html', 'offline, a navigation still gets the page');

  // A DEEP LINK, offline. Somebody's bookmark, or a path that existed in an
  // older version. There is one page in this app and every route is it.
  const deep = await fire('fetch', { request: req('./room/QRTX', { mode: 'navigate' }) });
  eq(deep && deep.tag, 'index.html', 'and so does a deep link to a path that never existed');

  const mod = await fire('fetch', { request: req('./js/state.js') });
  eq(mod && mod.tag, 'state.js', 'offline, a module comes out of the cache');

  const css = await fire('fetch', { request: req('./css/app.css') });
  eq(css && css.tag, 'app.css', 'and so does the stylesheet');

  const icon = await fire('fetch', { request: req('./icons/icon-192.png') });
  eq(icon && icon.tag, 'icon-192.png', 'and so do the icons');

  // The whole shell, not just the three sampled above. An app that serves
  // index.html and one module offline is not an app that works offline.
  let served = 0;
  for (const p of meta.SHELL) {
    const r = await fire('fetch', { request: req(p, { mode: p === './' ? 'navigate' : 'no-cors' }) });
    if (r && r.status === 200) served++;
  }
  eq(served, meta.SHELL.length,
    `all ${meta.SHELL.length} precached assets are served with the network down`);

  eq(networkHits, before, 'and none of that touched the network at all');

  // The cache-buster. ./js/main.js?v=2 must still hit ./js/main.js, or one
  // stray query string during debugging turns offline support off.
  const busted = await fire('fetch', { request: req('./js/main.js?v=2') });
  eq(busted && busted.tag, 'main.js', 'a query string does not defeat the precache');

  // Not ours and not reachable. This has to fail like a network failure,
  // because the page's own error handling is written against one.
  const gone = await fire('fetch', { request: req('./late-addition.txt') });
  ok(gone && gone.type === 'error',
    'something never precached, requested offline, fails as a network error rather than a fake 200');

  // ---------------------------------------------------------------------
  // FETCH: back online, and STILL no runtime caching
  // ---------------------------------------------------------------------
  offline = false;
  const sizeBefore = (await cache.keys()).length;

  const late = await fire('fetch', { request: req('./late-addition.txt') });
  eq(late && late.tag, 'late', 'online, something outside the shell is fetched normally');
  eq((await cache.keys()).length, sizeBefore,
    'and is NOT written to the cache — the health-probe rule, enforced by having no write path');
  eq(writesOutsideInstall, 0, 'nothing anywhere writes to the cache outside install');

  // A PRECACHED asset online still comes from the cache, not the network. That
  // is what makes the version consistent: js/ui.js and js/state.js can never
  // come from two different deploys.
  const netBefore = networkHits;
  const uiAgain = await fire('fetch', { request: req('./js/ui.js') });
  eq(uiAgain && uiAgain.tag, 'ui.js', 'online, a precached module still comes from the cache');
  eq(networkHits, netBefore, 'without a network request, so the whole shell is one version');
}

{
  // --- install is all-or-nothing --------------------------------------------
  //
  // Re-run install against a server that is missing one module — a rename that
  // did not update SHELL, a bad deploy. The install MUST reject, so the worker
  // never activates and the previous version keeps serving. The alternative is
  // a cache with a hole in it, which is an app that works online and is broken
  // offline: the single hardest bug report to act on.

  const ORIGIN = 'https://pages.test';
  const BASE = `${ORIGIN}/twentynine/`;
  const abs = (u) => new URL(u, BASE).href;

  class Res { constructor(t, i = {}) { this.tag = t; this.status = i.status ?? 200; } static error() { return new Res(null, { status: 0 }); } }

  const store = new Map();
  let broken = null;
  const fakeFetch = async (r) => {
    const url = typeof r === 'string' ? abs(r) : r.url;
    return new Res('x', { status: url === abs(broken) ? 404 : 200 });
  };
  class FakeCache {
    constructor() { this.store = store; }
    async addAll(paths) {
      const got = [];
      for (const p of paths) {
        const r = await fakeFetch(abs(p));
        if (r.status !== 200) throw new TypeError(`addAll: ${p}`);
        got.push(abs(p));
      }
      for (const k of got) this.store.set(k, new Res('x'));
    }
    async keys() { return [...this.store.keys()]; }
    async match() { return undefined; }
    async put() {}
  }
  const handlers = new Map();
  const fakeSelf = {
    addEventListener(t, f) { handlers.set(t, f); },
    location: { origin: ORIGIN, href: BASE + 'sw.js' },
    clients: { async claim() {} },
  };
  const swSrc = readRepo('sw.js');
  // eslint-disable-next-line no-new-func
  const meta = new Function('self', 'caches', 'fetch', 'Response',
    swSrc + '\n; return { CACHE_NAME, SHELL };')(
    fakeSelf,
    { async open() { return new FakeCache(); }, async keys() { return []; }, async delete() {} },
    fakeFetch, Res);

  // Break each entry in turn. Every single one must be load-bearing — if any
  // module can 404 and the install still succeeds, that module is not really
  // being precached and its absence would only show up offline.
  let survived = 0;
  for (const p of meta.SHELL) {
    broken = p;
    store.clear();
    let rejected = false;
    let waited = null;
    handlers.get('install')({ waitUntil(x) { waited = x; } });
    try { await waited; } catch (_) { rejected = true; }
    if (!rejected) { survived++; console.error('  ✗ install tolerated a missing', p); }
    else if (store.size !== 0) { survived++; console.error('  ✗ install left a partial cache after', p); }
  }
  eq(survived, 0,
    `install refuses to complete with any one of the ${meta.SHELL.length} assets missing, and leaves nothing behind`);
}

// ===========================================================================
section('The shell: the page, the manifest and the icons');
// ===========================================================================

{
  // --- index.html -----------------------------------------------------------
  const html = readRepo('index.html');

  // THE THREE SIBLINGS. js/main.js does getElementById on all three at module
  // scope, and js/ui.js's render() wipes everything inside #app on every
  // frame. If any of these moved inside #app, the symptom would be a screen
  // reader that goes silent after the first frame and a rules button that
  // stops working — neither of which throws, and neither of which any other
  // test in this file can see.
  for (const id of ['app', 'announce', 'rules']) {
    ok(new RegExp(`id="${id}"`).test(html), `index.html has #${id}`);
  }

  // Positional, because "present" is not the property that matters — "outside
  // #app" is. #app is written as an empty element, so everything after it in
  // the source is a sibling.
  const appAt = html.indexOf('<div id="app"></div>');
  ok(appAt > 0, '#app is empty in the markup — the renderer fills it');
  for (const marker of ['id="announce"', '<footer', '<dialog id="rules"']) {
    ok(html.indexOf(marker) > appAt,
      `${marker} comes after #app closes, so clear(root) cannot destroy it`);
  }

  // The live region must survive AND be announced. display:none and hidden
  // both remove it from the accessibility tree, which is the usual way this
  // gets quietly broken by someone tidying up.
  const announceTag = html.slice(html.indexOf('id="announce"') - 60, html.indexOf('id="announce"') + 140);
  ok(/aria-live="polite"/.test(announceTag), 'the live region is polite');
  ok(/class="sr-only"/.test(announceTag), 'and hidden with .sr-only');
  ok(!/hidden/.test(announceTag) && !/display:\s*none/.test(announceTag),
    'and NOT with hidden or display:none, either of which would silence it');

  // EVERY LOCAL PATH RELATIVE. Same reason as SHELL: a project site lives at
  // /<repo>/ and a leading slash escapes it.
  const localRefs = [...html.matchAll(/(?:href|src)="(?!https?:|data:|#)([^"]+)"/g)].map((m) => m[1]);

  // Named rather than counted. A floor like `length >= 8` is a number that has
  // to be edited every time an icon is added or removed, and it passes just as
  // happily when the stylesheet reference is the one that went missing and two
  // icons were added. These four are the ones whose absence breaks something:
  // no stylesheet is an unstyled page, no module is no game, no manifest is no
  // install prompt, and no icon is a blank tile.
  for (const must of ['./css/app.css', './js/main.js', './manifest.webmanifest']) {
    ok(localRefs.includes(must), `index.html loads ${must}`);
  }
  ok(localRefs.some((r) => r.startsWith('./icons/')), 'and references at least one icon');

  let rooted = 0;
  for (const r of localRefs) if (!r.startsWith('./')) { rooted++; console.error('  ✗ not relative:', r); }
  eq(rooted, 0, 'and every one of them is relative, so a Pages subpath survives');

  // And every one of them is a file that exists. A typo in an icon path is a
  // broken install prompt that nobody notices until somebody tries.
  let dangling = 0;
  for (const r of new Set(localRefs)) {
    try { readFileSync(REPO + r.slice(2)); } catch (_) { dangling++; console.error('  ✗ dangling:', r); }
  }
  eq(dangling, 0, 'and points at a file that is actually in the repository');

  // PeerJS: a script tag, never an import, which is what keeps "zero
  // dependencies" literally true. `defer` is load-bearing — deferred classic
  // scripts and module scripts share one queue in document order, so this is
  // what guarantees window.Peer exists before js/main.js evaluates and calls
  // peerAvailable() from resume().
  const peerTag = html.match(/<script[^>]*peerjs[^>]*><\/script>/);
  ok(peerTag, 'PeerJS arrives as a <script> tag');
  ok(peerTag && /\sdefer\b/.test(peerTag[0]), 'deferred, so it runs before the module that needs it');
  // Against the position of the TAG, not of the first mention of the string
  // './js/main.js' — which is in the comment above the PeerJS tag explaining
  // this very ordering, and which therefore made this assertion measure the
  // prose rather than the document.
  ok(peerTag && html.indexOf(peerTag[0]) < html.indexOf('<script type="module"'),
    'and earlier in the document than the module script, which is what makes defer ordered');
  ok(!/import[^\n]*peerjs/i.test(html), 'and is never imported');

  // The reset button, and the rule it must never break.
  ok(/id="reset-btn"/.test(html), 'the footer carries the clear-cache button');
  const script = html.slice(html.lastIndexOf('<script>'));
  // #####################################################################
  // THE ONE THAT WOULD BE UNRECOVERABLE. localStorage holds
  // twentynine.clientId, which IS a player's claim to their seat. Clearing
  // it does not sign them out and back in; it makes them a stranger to the
  // host, so the rejoin is refused and their seat and their entire
  // scoreboard are gone for the rest of a nineteen-round match. It would
  // also drop twentynine.engine, the host's only copy of the game.
  // #####################################################################
  //
  // CHECKED AGAINST THE CODE WITH THE COMMENTS STRIPPED. The first version of
  // this assertion ran against the raw file and failed — on the paragraph
  // above, which says "localStorage" four times while explaining why nothing
  // may touch it. A test that cannot tell an explanation from an instruction
  // would force the explanation to be deleted to make it pass, which is the
  // exact wrong outcome.
  const strip = (s) => s.replace(/\/\*[\s\S]*?\*\//g, '').replace(/^\s*\/\/.*$/gm, '');
  const executable = strip(script);
  ok(/caches/.test(executable), 'the stripper left the executable code intact');
  ok(!/localStorage|sessionStorage/.test(executable),
    'and no executable line in the page touches localStorage — clientId and the snapshot survive a reset');

  // BOTH HALVES OF THE BUTTON, ASSERTED SEPARATELY.
  //
  // This was one line reading /caches\.delete|caches\.keys/, and a mutation
  // that deleted the delete outright walked straight past it: the enumeration
  // above it still matched, so the OR was still satisfied. The button would
  // have unregistered the worker, reloaded, and left every stale byte exactly
  // where it was — the one thing it exists to prevent.
  //
  // AN ALTERNATION IS THE WEAKEST SHAPE A TEST CAN TAKE. It keeps passing
  // while either half rots, which means it stops measuring the thing it was
  // written for at the moment that thing breaks. Two assertions cost one line
  // and cannot do that.
  ok(/caches\.keys\(\)/.test(executable), 'whose handler enumerates Cache Storage');
  ok(/caches\.delete\(/.test(executable),
    'and deletes what it finds — without this the button only unregisters and reloads');
  ok(/unregister\(\)/.test(executable), 'and unregisters the service worker');

  // AGAINST THE TAG, NOT THE DOCUMENT — the same trap as the localStorage
  // check above, found the same way. This read /viewport-fit=cover/ over the
  // whole file and passed with the attribute deleted, because the HTML comment
  // four lines above the tag explains what viewport-fit=cover buys. A
  // substring search over a commented file cannot tell the explanation from
  // the thing being explained, so it has to be pointed at the tag itself.
  //
  // It matters: css/app.css pads the play dock with env(safe-area-inset-bottom),
  // and without the opt-in that function returns zero on every browser. The
  // failure is silent on a desktop and is the home indicator sitting on top of
  // the card you are trying to tap on a phone.
  const viewport = (html.match(/<meta\s+name="viewport"[^>]*>/) || [''])[0];
  ok(viewport !== '', 'the page declares a viewport');
  ok(/viewport-fit=cover/.test(viewport),
    'whose tag opts into the safe-area insets css/app.css pays for');
  ok(/width=device-width/.test(viewport), 'and scales to the device rather than a fixed page width');
  ok(/name="theme-color" content="#0C1207"/.test(html), 'and the browser chrome matches --bg');
}

{
  // --- manifest.webmanifest -------------------------------------------------
  let manifest = null;
  try { manifest = JSON.parse(readRepo('manifest.webmanifest')); passed++; }
  catch (e) { failed++; console.error('  ✗ FAIL: the manifest is not valid JSON —', e.message); }

  if (manifest) {
    eq(manifest.name, 'Twenty-nine', 'the manifest names the app');
    // Relative, for the third time and the same reason. An installed PWA whose
    // start_url is '/' opens the github.io user root, not this game.
    for (const key of ['start_url', 'scope', 'id']) {
      ok(typeof manifest[key] === 'string' && manifest[key].startsWith('./'),
        `manifest ${key} is relative — got ${JSON.stringify(manifest[key])}`);
    }
    // These two are what an installed app paints before any CSS has loaded. If
    // they drift from --bg the splash flashes a different colour than the app.
    eq(manifest.background_color, '#0C1207', 'the splash background matches --bg');
    eq(manifest.theme_color, '#0C1207', 'and so does the theme colour');

    // A maskable icon is not optional on Android: without one the launcher
    // takes the "any" icon and shrink-wraps it inside a white circle.
    const purposes = manifest.icons.map((i) => i.purpose);
    ok(purposes.includes('maskable'), 'a maskable icon is declared, so Android does not letterbox it');
    ok(manifest.icons.some((i) => i.sizes === '512x512' && i.purpose === 'any'),
      'and a 512 "any" icon, which is the one install prompts use');

    let badIcon = 0;
    for (const i of manifest.icons) {
      if (!i.src.startsWith('./')) { badIcon++; console.error('  ✗ icon path not relative:', i.src); continue; }
      try { readFileSync(REPO + i.src.slice(2)); } catch (_) { badIcon++; console.error('  ✗ icon missing:', i.src); }
    }
    eq(badIcon, 0, `all ${manifest.icons.length} declared icons are relative and present`);
  }
}

{
  // --- the icons themselves -------------------------------------------------
  //
  // Read as bytes, because "the file exists" is also true of a zero-byte file
  // and of an HTML 404 page saved with a .png extension. The PNG header
  // carries the real dimensions, and they are checked against what the
  // manifest and index.html promise — a 512 icon that is really 192 is
  // upscaled by the launcher and looks soft on exactly the devices that show
  // it largest.

  const expected = [
    ['icons/icon-32.png', 32],
    ['icons/icon-192.png', 192],
    ['icons/icon-512.png', 512],
    ['icons/icon-maskable-512.png', 512],
    ['icons/apple-touch-icon.png', 180],
  ];

  let bad = 0;
  for (const [path, size] of expected) {
    const buf = readFileSync(REPO + path);
    // Signature, then IHDR at a fixed offset: length(4) type(4) w(4) h(4).
    const sig = buf.subarray(0, 8).toString('hex');
    if (sig !== '89504e470d0a1a0a') { bad++; console.error('  ✗ not a PNG:', path); continue; }
    const w = buf.readUInt32BE(16), h = buf.readUInt32BE(20);
    if (w !== size || h !== size) { bad++; console.error(`  ✗ ${path} is ${w}x${h}, expected ${size}x${size}`); }
    if (buf[24] !== 8 || buf[25] !== 2) { bad++; console.error(`  ✗ ${path} is not 8-bit truecolour`); }
  }
  eq(bad, 0, `all ${expected.length} icons are real PNGs at the size they claim`);

  // OPAQUE. Colour type 2 has no alpha channel at all, which is checked above
  // — and that is the property iOS needs, because it composites the
  // apple-touch-icon over nothing and a transparent one comes out black.
  // Stated separately so the reason survives if the check above is edited.
  const apple = readFileSync(REPO + 'icons/apple-touch-icon.png');
  eq(apple[25], 2, 'and the apple-touch icon has no alpha, so iOS cannot render it on black');
}

// ###########################################################################
//
//  SUMMARY
//
// ###########################################################################

console.log(`\n${passed} passed, ${failed} failed`);
if (failed) process.exit(1);

// ============================================================================
// cards.js — The 32-card pack, its ranking, what each card is worth, and how
// the two batches of four are dealt.
//
// ############################################################################
// #  THE RANKING IS J 9 A 10 K Q 8 7, HIGH TO LOW. IT IS NOT ACE-HIGH.       #
// #  judgement's and courtpiece's comparators both put the ace on top. Copy  #
// #  either and the game still runs, still finishes, and every trick that   #
// #  has a jack or a nine in it goes to the wrong player.                    #
// ############################################################################
//
// TWO NUMBERS PER CARD, AND THEY ARE DIFFERENT THINGS.
//
//   rankValue   how strong it is in a trick. Only ever compared against a
//               card of the same suit — across suits, whether a card wins is
//               a question about trump and the led suit (js/trick.js).
//   cardPoints  what it is worth to the side that wins the trick it is in.
//               J 3, 9 2, A 1, 10 1, everything else 0. Seven a suit,
//               twenty-eight in the pack.
//
// They happen to agree on the order of the top four, which is exactly why
// they must not be merged: K is stronger than 8 and both are worth nothing,
// and a single "value" field would have to lie about one of those facts.
//
// TWENTY-EIGHT IS NEVER TYPED. PACK_POINTS is summed from POINTS over the
// pack below, the bid ceiling in js/rules.js is that sum, and the suite
// derives it a third time from the table. If somebody changes a point value,
// everything that depends on it moves with it rather than disagreeing.
//
// Imports nothing. The deal takes its seat ORDER as an argument rather than
// asking js/trick.js for it, so the turn direction is decided in exactly one
// module and this one cannot have an opinion about it. See deal() below.
// ============================================================================

/**
 * A frozen lookup table with NO PROTOTYPE.
 *
 * Every table in this file is keyed by a character that arrived over the
 * wire. A plain object literal answers `table['toString']` with an inherited
 * function, which then sails past an `|| 0` fallback and gets used as a
 * number. A null prototype makes the miss a miss.
 */
function table(obj) { return Object.freeze(Object.assign(Object.create(null), obj)); }

// ---------------------------------------------------------------------------
// Suits and ranks
// ---------------------------------------------------------------------------

// Black, red, black, red. Adjacent suits differ in colour, which is what stops
// a fan of eight cards reading as one undifferentiated block on a phone. There
// is no fixed suit order in the rules of Twenty-nine — trump is whatever the
// bidder chooses — so the display order and the pack order can be one array.
export const SUITS = Object.freeze(['S', 'H', 'C', 'D']);

// DESCENDING, by trick-taking strength. The order of this array IS the
// strength order — see rankValue() — so reversing it, or "fixing" it to put
// the ace first, silently inverts the game. 'T' is the ten, stored as one
// character so every code is exactly two.
export const RANKS = Object.freeze(['J', '9', 'A', 'T', 'K', 'Q', '8', '7']);

export const PACK_SIZE = SUITS.length * RANKS.length;

// A card is a two-character code: rank then suit, e.g. 'JS', '9H', 'TD'. One
// pack, so the code is unique and doubles as the card's identity — hands are
// plain arrays of these strings.
export function rankOf(code) { return code[0]; }
export function suitOf(code) { return code[1]; }

// J highest. Derived from RANKS rather than written out, so the two cannot
// drift apart: J is 8 and 7 is 1.
const RANK_VALUE = table(
  RANKS.reduce((acc, rank, i) => { acc[rank] = RANKS.length - i; return acc; }, {}),
);

/** Strength in a trick. Higher wins, within one suit. */
export function rankValue(code) { return RANK_VALUE[rankOf(code)] || 0; }

// ---------------------------------------------------------------------------
// Points
// ---------------------------------------------------------------------------

/**
 * Card points, by rank. THE ONE PLACE A POINT VALUE IS WRITTEN.
 *
 * Every rank is listed, including the four that are worth nothing, so that a
 * rank missing from this table is a visible absence rather than a quiet zero.
 */
export const POINTS = table({ J: 3, 9: 2, A: 1, T: 1, K: 0, Q: 0, 8: 0, 7: 0 });

/** What one card is worth to the side that takes it. */
export function cardPoints(code) { return POINTS[rankOf(code)] || 0; }

/** The sum over any collection of codes. */
export function pointsIn(codes) {
  let n = 0;
  for (const code of codes) n += cardPoints(code);
  return n;
}

/** True for the four ranks that score. The bot's whole idea of "feeding" its
 *  partner and "throwing" to an opponent is a question about this. */
export function scores(code) { return cardPoints(code) > 0; }

// ---------------------------------------------------------------------------
// Names, for the screen and for the screen reader
// ---------------------------------------------------------------------------

const SUIT_GLYPHS = table({ S: '♠', H: '♥', D: '♦', C: '♣' });
const SUIT_NAMES  = table({ S: 'spades', H: 'hearts', D: 'diamonds', C: 'clubs' });
const SUIT_SINGULAR = table({ S: 'spade', H: 'heart', D: 'diamond', C: 'club' });
const RANK_NAMES  = table({
  J: 'Jack', 9: '9', A: 'Ace', T: '10', K: 'King', Q: 'Queen', 8: '8', 7: '7',
});

export function suitGlyph(suit) { return SUIT_GLYPHS[suit] || ''; }
export function suitName(suit)  { return SUIT_NAMES[suit] || ''; }
export function suitSingular(suit) { return SUIT_SINGULAR[suit] || ''; }

export function isRedSuit(suit) { return suit === 'H' || suit === 'D'; }
export function isRedCard(code) { return isRedSuit(suitOf(code)); }

/** Display rank — 'T' is stored for the ten so every code is two characters. */
export function rankLabel(code) { return rankOf(code) === 'T' ? '10' : rankOf(code); }

/** Spoken form: "Jack of spades". */
export function cardName(code) {
  return `${RANK_NAMES[rankOf(code)] || rankOf(code)} of ${suitName(suitOf(code))}`;
}

/** The aria-label the brief asks for: "Jack of spades, 3 points". A card worth
 *  nothing says "no points" rather than "0 points", which a screen reader reads
 *  as "oh points" in at least one common voice. */
export function cardLabel(code) {
  const p = cardPoints(code);
  return `${cardName(code)}, ${p === 0 ? 'no points' : `${p} point${p === 1 ? '' : 's'}`}`;
}

// ---------------------------------------------------------------------------
// The pack
// ---------------------------------------------------------------------------

/** A fresh, ordered 32-card pack: every suit, strongest rank first. */
export function buildPack() {
  const pack = [];
  for (const suit of SUITS) {
    for (const rank of RANKS) pack.push(rank + suit);
  }
  return pack;
}

/**
 * Twenty-eight. DERIVED, from POINTS over the pack, and exported so the bid
 * ceiling in js/rules.js and the scoring in js/scoring.js can both read one
 * number that nobody typed.
 */
export const PACK_POINTS = pointsIn(buildPack());

/** Fisher-Yates, returning a new array. */
export function shuffle(arr) {
  const a = arr.slice();
  for (let i = a.length - 1; i > 0; i--) {
    const j = randomBelow(i + 1);
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
}

// Read at call time, not captured at module load, so a test can replace
// globalThis.crypto before constructing anything and still be obeyed — the
// same indirection judgement and sequence use, so a seeded stream reproduces a
// failing deal.
function randomBelow(n) {
  try {
    const source = typeof crypto !== 'undefined' ? crypto : globalThis.crypto;
    if (source && source.getRandomValues) {
      const buf = new Uint32Array(1);
      source.getRandomValues(buf);
      return buf[0] % n;
    }
  } catch (_) { /* fall through */ }
  return Math.floor(Math.random() * n);
}

// ---------------------------------------------------------------------------
// The deal: two batches of four
// ---------------------------------------------------------------------------

/** Cards in each batch, and batches in a deal. Four and two, so eight a hand
 *  and the whole pack dealt — nothing is left in a stock. */
export const BATCH = 4;
export const BATCHES = 2;
export const HAND_SIZE = BATCH * BATCHES;

/** Four players. DERIVED — the whole pack is dealt and nothing is left over,
 *  so the seat count is the pack divided by a hand. Twenty-nine is a game for
 *  exactly four, in two partnerships, and every module reads this rather than
 *  writing a 4 of its own. */
export const SEATS = PACK_SIZE / HAND_SIZE;

/**
 * Deal one batch: BATCH cards to each seat, IN THE ORDER GIVEN, a block of
 * four at a time, off the top of `stock`.
 *
 * THE ORDER IS AN ARGUMENT, and it has no default. The rule is "the dealer
 * gives four cards to each player, starting on their right", and which seat is
 * on the dealer's right is the anticlockwise question js/trick.js exists to
 * answer once. A deal that computed its own order would be a second copy of
 * that answer — and the copy is where judgement's clockwise helper would land
 * if somebody ported it. So js/state.js asks trick.js for the order and hands
 * it in, and this function cannot get the direction wrong because it does not
 * know what a direction is.
 *
 * A BLOCK OF FOUR, NOT ROUND-ROBIN. That is how the game is dealt, and against
 * an UNSHUFFLED pack it makes the result readable: the first seat in `order`
 * holds the first four codes. scripts/test-engine.mjs deals a known pack
 * through the engine and reads the dealer's-right seat straight out of it —
 * a second, independent pin on the anticlockwise rule.
 *
 * Returns { hands, stock } with new arrays. `hands` is indexed by seat and has
 * an entry for every seat in `order`; the caller appends it to what each seat
 * already holds. Throws rather than dealing a quiet short hand.
 */
export function dealBatch(stock, order) {
  if (!Array.isArray(order) || order.length === 0) {
    throw new Error('dealBatch: an explicit seat order is required');
  }
  const needed = order.length * BATCH;
  if (stock.length < needed) {
    throw new Error(`dealBatch: ${order.length} seats x ${BATCH} cards needs ${needed}, stock has ${stock.length}`);
  }
  const rest = stock.slice();
  const hands = [];
  for (const seat of order) hands[seat] = rest.splice(0, BATCH);
  return { hands, stock: rest };
}

// ---------------------------------------------------------------------------
// Sorting a hand for display
// ---------------------------------------------------------------------------

/**
 * Group by suit, strongest first within a suit — by the J-9-A-10 order, so the
 * jack sits at the head of its suit where a player looks for it.
 *
 * `trump` pulls a suit to the front, and it is a parameter the CALLER decides,
 * because in this game who is allowed to know the trump changes over a deal.
 * js/state.js passes the suit only to a seat entitled to it: the bidder who
 * chose a concealed trump, or anybody after the reveal. Sorting a non-bidder's
 * hand by the real trump before the reveal would leak it through the order of
 * their own cards, which is a leak nobody would think to look for.
 */
export function sortHand(hand, trump = null) {
  const order = trump && SUITS.includes(trump)
    ? [trump, ...SUITS.filter((s) => s !== trump)]
    : SUITS;
  return hand.slice().sort((a, b) => {
    const suitDiff = order.indexOf(suitOf(a)) - order.indexOf(suitOf(b));
    if (suitDiff !== 0) return suitDiff;
    return rankValue(b) - rankValue(a);
  });
}

/** How many of each suit a hand holds. */
export function suitCounts(hand) {
  const counts = { S: 0, H: 0, D: 0, C: 0 };
  for (const code of hand) counts[suitOf(code)] += 1;
  return counts;
}

// A pack that is not 32 cards would break the deal arithmetic, and the
// symptom — a hand one card short on the eighth trick — would surface a long
// way from the cause. Cheap to check once at load, in node and the browser.
if (!Number.isInteger(SEATS) || SEATS !== 4) {
  throw new Error(`cards.js: the pack deals into ${SEATS} hands, and Twenty-nine is for four`);
}

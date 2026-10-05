// ============================================================================
// trick.js — Turn order, partnerships, follow-suit, the caller's obligation to
// trump, and who won the trick across the reveal.
//
// ############################################################################
// #  TWENTY-NINE RUNS ANTICLOCKWISE.  nextSeat() IS -1.                      #
// #  judgement — THE REPO THIS ONE IS MODELLED ON — RUNS CLOCKWISE AND ITS   #
// #  nextSeat() IS +1. Copying its turn-order helper is the single most      #
// #  likely bug in this build: the game would still deal, still bid, still   #
// #  finish, and every turn would go to the wrong player.                    #
// ############################################################################
//
// So the direction is not a sign buried in an expression. It is a named
// constant, passed as a REQUIRED argument to one piece of arithmetic, with a
// test pinned to both values and to the constant this repo chose.
//
// THE GEOMETRY, once, so nothing below has to re-derive it.
//
// Picture the table from above, everyone facing the centre. Seats 0..3 are
// numbered CLOCKWISE — the direction you read positions off a clock face. A
// player facing inward has the anticlockwise direction on their RIGHT. So:
//
//     next in turn order  ==  the player on your right  ==  seat - 1 (mod 4)
//
// Three rules lean on that directly:
//
//   * "The dealer gives four cards to each player, starting on their right."
//   * "The auction starts with the player to the dealer's right."
//   * "The dealer rotates anticlockwise from deal to deal."
//
// All three are nextSeat(), and nextSeat() is the only place the sign lives.
//
// The renderer owes the other half (js/ui.js): with seats numbered clockwise
// and the viewer at the bottom, offsets 0,1,2,3 from the viewer are drawn
// bottom, left, top, right — courtpiece's layout — so play visibly sweeps
// bottom -> right -> top -> left. Partners are always two apart, which is
// true whichever way you count, and is why they always sit opposite.
//
// ---------------------------------------------------------------------------
// THE CONCEALED TRUMP, AND WHAT THIS FILE IS NOT ALLOWED TO KNOW
// ---------------------------------------------------------------------------
// Until somebody calls for it, the trump suit is a secret held by the engine
// and by the bidder alone. Nothing a non-bidder may do can depend on it, or
// the legal set would leak it — a card that greys out only when hearts are
// trumps tells you hearts are trumps.
//
// So legalPlays() does not take the trump suit. It takes an OBLIGATION, which
// is the trump suit only for the one player who has just called for it, on the
// trick they called on — and by then the trump is face up for everyone. Before
// the reveal there is no argument through which the secret could get in.
//
// The trick winner does not take the trump suit either. Each play carries a
// `trump` flag fixed WHEN IT WAS PLAYED: true only if trump had been revealed
// at that moment and the card is of that suit. A trump-suit card played before
// the reveal was a plain card when it hit the table and stays one, which is
// the rule — and it is also what keeps a pre-reveal trick resolvable from
// public information alone.
//
// Imports only cards.js, which imports nothing. Node-safe and DOM-free.
// ============================================================================

import { SEATS, rankValue, suitOf, suitName, suitSingular } from './cards.js';

// ---------------------------------------------------------------------------
// Turn order
// ---------------------------------------------------------------------------

/** Seat numbers ascend clockwise, so +1 is clockwise and -1 is anticlockwise. */
export const CLOCKWISE = 1;
export const ANTICLOCKWISE = -1;

/** Twenty-nine's direction. The single place the choice is recorded. */
export const TABLE_DIRECTION = ANTICLOCKWISE;

/**
 * One seat along, in whichever direction you ask for.
 *
 * `direction` is REQUIRED and has no default. That is the whole point of this
 * function existing separately from nextSeat(): a default would let a call
 * copied in from judgement keep working and quietly take judgement's answer.
 */
export function stepSeat(seat, direction) {
  if (direction !== CLOCKWISE && direction !== ANTICLOCKWISE) {
    throw new Error(`stepSeat: direction must be CLOCKWISE or ANTICLOCKWISE, got ${direction}`);
  }
  return (seat + direction + SEATS) % SEATS;
}

/** The next player to act: anticlockwise, the player on your right. */
export function nextSeat(seat) {
  return stepSeat(seat, TABLE_DIRECTION);
}

/** The player who acted before this one — clockwise, on your left. */
export function prevSeat(seat) {
  return stepSeat(seat, -TABLE_DIRECTION);
}

/**
 * Every seat in turn order, starting at `startSeat`.
 *
 * `skip` is a seat that is not playing — under single hand, the declarer's
 * partner sits out with their cards face down, and a trick is three cards.
 * The skipped seat is removed from the order rather than given an empty turn,
 * so nothing downstream ever waits on it.
 *
 * Used for the deal, the auction, the declarations and the play, which are
 * all the same ordering. One function rather than four loops is what makes
 * the direction testable in one place.
 */
export function seatsFrom(startSeat, skip = null) {
  const order = [];
  let s = startSeat;
  for (let i = 0; i < SEATS; i++) {
    if (s !== skip) order.push(s);
    s = nextSeat(s);
  }
  return order;
}

/** The next seat in turn order that is actually playing. */
export function nextActiveSeat(seat, skip = null) {
  let s = nextSeat(seat);
  for (let i = 0; i < SEATS && s === skip; i++) s = nextSeat(s);
  return s;
}

// ---------------------------------------------------------------------------
// Partnerships
//
// Seats 0 & 2 against 1 & 3. DERIVED from the seat rather than stored, so a
// partnership cannot be dealt inconsistently and cannot be changed mid-match:
// the seat decides it, as in courtpiece.
// ---------------------------------------------------------------------------

/** Team 0 is seats 0 and 2; team 1 is seats 1 and 3. */
export function teamOf(seat) { return seat % 2; }

/** Two seats away — true counting either way, so it has no handedness. */
export function partnerOf(seat) { return (seat + 2) % SEATS; }

export function sameTeam(a, b) { return teamOf(a) === teamOf(b); }

/** The two seats of a team, lower seat first. */
export function seatsOfTeam(team) { return [team, team + 2]; }

// ---------------------------------------------------------------------------
// Follow-suit, and the one obligation to trump
// ---------------------------------------------------------------------------

/** The suit that was led — the suit of the first card played, always. A
 *  trump-suit card led before the reveal leads its own suit as a plain card. */
export function ledSuitOf(plays) {
  return plays && plays.length ? suitOf(plays[0].code) : null;
}

/**
 * Whether this player may call for trump right now.
 *
 * Three conditions, and none of them is the trump suit:
 *
 *   * there is a lead to follow — you cannot be void in a suit nobody led, so
 *     the player leading a trick can never call;
 *   * trump has not been revealed — once it is face up there is nothing to
 *     call for;
 *   * the player holds no card of the led suit.
 *
 * The bidder may call too ("the bidder, when void, may reveal trump the same
 * way"). Their indicator is not in their hand until the reveal, so it does not
 * count towards following — it is face down on the table, not held.
 */
export function canCall(hand, led, revealed) {
  if (!led || revealed) return false;
  return !hand.some((c) => suitOf(c) === led);
}

/**
 * The cards in `hand` that may legally be played.
 *
 * `obligation` is null for everybody except the player who has just called
 * for trump on this trick, for whom it is the trump suit. The rules, in the
 * order they bite:
 *
 *   1. Leading: anything.
 *   2. Holding the led suit: one of those. Always, and before anything else —
 *      even a caller who holds the led suit follows it. (Only the bidder can be
 *      in that position: their indicator comes back into their hand at the
 *      reveal, and it can be of the suit that was led.)
 *   3. A caller holding a trump: one of those. THIS IS THE ONLY OBLIGATION TO
 *      TRUMP IN THE GAME, and it reaches exactly one player on exactly one
 *      trick. judgement has none at all, which is why its legality function
 *      must not be ported: it would be right for 31 of 32 situations.
 *   4. Otherwise: anything. Void without calling is a plain discard, whatever
 *      its suit; void after the reveal is free too. There is no general
 *      obligation to trump.
 *
 * Returns a NEW array, never the caller's hand.
 */
export function legalPlays(hand, led, obligation = null) {
  if (!led) return hand.slice();
  const following = hand.filter((c) => suitOf(c) === led);
  if (following.length) return following;
  if (obligation) {
    const trumps = hand.filter((c) => suitOf(c) === obligation);
    if (trumps.length) return trumps;
  }
  return hand.slice();
}

/** Whether one specific card may be played. The host's enforcement point; the
 *  UI's greying-out is a convenience that mirrors it, never a substitute. */
export function canPlay(hand, code, led, obligation = null) {
  if (!hand.includes(code)) return false;
  return legalPlays(hand, led, obligation).includes(code);
}

/**
 * Why a card cannot be played, phrased for an aria-label. Null when it can.
 *
 * The obligation reason names the trump suit, and that is safe: it is only
 * ever produced for a caller, after the reveal, about a suit that is face up
 * on the table for everyone.
 */
export function illegalReason(hand, code, led, obligation = null) {
  if (canPlay(hand, code, led, obligation)) return null;
  if (!hand.includes(code)) return 'not in your hand';
  if (hand.some((c) => suitOf(c) === led)) return `must follow ${suitName(led)}`;
  return `you called for trump, so you must play a ${suitSingular(obligation)}`;
}

// ---------------------------------------------------------------------------
// Resolving a trick
// ---------------------------------------------------------------------------

/**
 * Whether a card being played NOW plays as a trump. Decided once, at the
 * moment it is played, and stored on the play — see the header. Before the
 * reveal the answer is false whatever the card, and the trump suit is not
 * even consulted.
 */
export function playsAsTrump(code, revealed, trump) {
  return !!revealed && !!trump && suitOf(code) === trump;
}

/**
 * The winning play of a trick, or null on an empty one.
 *
 * `plays` is [{ seat, code, trump }] in the order the cards hit the table.
 * It may be part-played — the UI and the bot both ask who is winning so far.
 *
 * The highest card that played AS A TRUMP wins. If none did, the highest card
 * of the suit led. A trump-suit card played before the reveal has `trump:
 * false` and competes only as a card of its own suit — which is the rule, and
 * which means the same card can lose a trick it would have won ten seconds
 * later.
 *
 * One consequence worth saying out loud, because it looks like a bug: if the
 * led suit IS the trump suit, a plain lead of it made before the reveal is
 * beaten by ANY trump played after the reveal, even a lower one. The rule
 * says the trick goes to "the highest trump played at or after the reveal",
 * and a card played before the reveal was not one.
 */
export function winningPlay(plays) {
  if (!plays || !plays.length) return null;
  const trumps = plays.filter((p) => p.trump === true);
  const led = ledSuitOf(plays);
  const pool = trumps.length ? trumps : plays.filter((p) => suitOf(p.code) === led);
  let best = null;
  for (const play of pool) {
    if (!best || rankValue(play.code) > rankValue(best.code)) best = play;
  }
  return best;
}

/** Which seat took (or is taking) the trick. */
export function trickWinner(plays) {
  const best = winningPlay(plays);
  return best ? best.seat : null;
}

/**
 * Would playing `code` into this part-played trick take the lead right now?
 *
 * `asTrump` is whether the card would play as a trump — the caller decides,
 * because only the caller knows whether it is entitled to know the suit. A
 * non-bidder before the reveal always passes false, and gets the answer a
 * human in that seat would work out.
 */
export function wouldWin(plays, seat, code, asTrump = false) {
  const after = (plays || []).concat([{ seat, code, trump: !!asTrump }]);
  return trickWinner(after) === seat;
}

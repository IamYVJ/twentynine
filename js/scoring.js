// ============================================================================
// scoring.js — Card points and game points. PURE.
//
// TWO KINDS OF POINTS, AND THE GAME TURNS ON NOT CONFUSING THEM.
//
//   card points  what is in the tricks. J 3, 9 2, A 1, 10 1, nothing else.
//                Twenty-eight in the pack. TRICKS ARE WORTH NOTHING — a side
//                can take six tricks of sevens and eights and score zero card
//                points, and the side that took two tricks with both red jacks
//                in them has six. Every trick-counting game in this family
//                (judgement, courtpiece) counts tricks, and a port of either
//                scoring would count the wrong thing.
//
//   game points  the match score. Only the bidding side's moves, by one a
//                deal, doubled or redoubled, or by three for a single hand.
//                The match ends when a side reaches +6 (it wins) or falls to
//                −6 (it loses).
//
// GAME POINTS GO NEGATIVE ROUTINELY. A side that bids and fails on the first
// deal is on −1 before anybody has scored anything, and nothing here treats
// that as a corner case. The scoreboard, the leader indicator and the TV are
// built for a minus sign from deal one; see score() in js/util.js for the
// glyph.
//
// Imports cards.js for the point table, trick.js for which seat is on which
// side, and rules.js for the bid range the pair is clamped to. Nothing here
// holds state; the engine hands in facts and gets numbers back.
// ============================================================================

import { pointsIn } from './cards.js';
import { teamOf } from './trick.js';
import { MIN_BID, MAX_BID } from './rules.js';

// ---------------------------------------------------------------------------
// Card points
// ---------------------------------------------------------------------------

/** Card points in one trick, whoever took it. */
export function trickPoints(plays) {
  return pointsIn((plays || []).map((p) => p.code));
}

/**
 * Card points taken by each side so far: [team 0, team 1].
 *
 * `tricks` is [{ plays, winner }] — the completed tricks of a deal. Both
 * partners' tricks count for their side: "the bidding side's card points are
 * all the points in tricks won by either partner."
 *
 * Over a complete deal the two numbers sum to the whole pack, every time. That
 * is a conservation law the suite holds every deal to, and it is the reason a
 * single-hand deal that ends early does NOT: the cards still in hand were never
 * won by anybody.
 */
export function pointsBySide(tricks) {
  const out = [0, 0];
  for (const t of tricks || []) {
    if (t && Number.isInteger(t.winner)) out[teamOf(t.winner)] += trickPoints(t.plays);
  }
  return out;
}

// ---------------------------------------------------------------------------
// The pair
// ---------------------------------------------------------------------------

/** How far the pair moves the bid. */
export const PAIR_SHIFT = 4;

/**
 * The bid after a pair has been declared.
 *
 * The bidding side holding the pair makes their contract EASIER — the bid
 * goes down four, never below MIN_BID. The opponents holding it make it
 * HARDER — up four, never above MAX_BID. Clamped at both ends, so a pair can
 * move a bid by less than four and sometimes by nothing at all: a bid of 16
 * helped by the bidder's own pair stays 16.
 */
export function pairAdjust(bid, holderIsBiddingSide) {
  return holderIsBiddingSide
    ? Math.max(MIN_BID, bid - PAIR_SHIFT)
    : Math.min(MAX_BID, bid + PAIR_SHIFT);
}

// ---------------------------------------------------------------------------
// Game points
// ---------------------------------------------------------------------------

/** One game point a deal, before doubling. */
export const DEAL_STAKE = 1;

/** Single hand is worth three, win or lose, and is never doubled. */
export const SINGLE_HAND_STAKE = 3;

/** Doubling levels: 0 none, 1 doubled, 2 redoubled. The multiplier is 2^level,
 *  so the three stakes are 1, 2 and 4 — derived, so they cannot disagree. */
export const DOUBLE_LEVELS = Object.freeze([0, 1, 2]);
export function multiplierFor(level) {
  return DOUBLE_LEVELS.includes(level) ? 2 ** level : 1;
}

/**
 * The result of an ordinary deal for the bidding side.
 *
 * `finalBid` is the bid after any pair. MADE when the side's card points are
 * at least that — "≥ the final bid" — so making it exactly counts. The delta
 * is ±DEAL_STAKE times the multiplier, and it is the BIDDING side's to add:
 * the other side's game points never move.
 */
export function dealResult({ finalBid, bidPoints, level = 0 }) {
  const made = bidPoints >= finalBid;
  const mult = multiplierFor(level);
  return { made, multiplier: mult, delta: (made ? 1 : -1) * DEAL_STAKE * mult };
}

/**
 * The result of a single hand for the declarer's side. Won only by taking all
 * eight tricks; a single lost trick loses it and ends the deal at once. Not
 * multiplied — doubling never happens in a single-hand deal, and the stake
 * would not be multiplied even if it had.
 */
export function singleHandResult({ lost }) {
  const made = !lost;
  return { made, multiplier: 1, delta: (made ? 1 : -1) * SINGLE_HAND_STAKE };
}

/** A new game-points pair with `delta` applied to `team`. */
export function applyDelta(gamePoints, team, delta) {
  const out = gamePoints.slice();
  out[team] += delta;
  return out;
}

// ---------------------------------------------------------------------------
// The finish
// ---------------------------------------------------------------------------

/** Reach this and you win; fall to its negative and you lose. */
export const MATCH_TARGET = 6;

/**
 * Whether the match is over, and who won.
 *
 * Returns { over: false } or { over: true, winner, loser, how } where `how` is
 * 'reached' (the winner got to +MATCH_TARGET) or 'fell' (the loser got to
 * −MATCH_TARGET and the winner is simply the other side).
 *
 * Only one side's points move in a deal, so the two cannot cross a line at the
 * same time from a legal history. A hand-built pair that has both is answered
 * by the side that won, which is the reading that hands nobody a win they did
 * not get.
 */
export function matchOutcome(gamePoints) {
  for (let team = 0; team < 2; team++) {
    if (gamePoints[team] >= MATCH_TARGET) return { over: true, winner: team, loser: 1 - team, how: 'reached' };
  }
  for (let team = 0; team < 2; team++) {
    if (gamePoints[team] <= -MATCH_TARGET) return { over: true, winner: 1 - team, loser: team, how: 'fell' };
  }
  return { over: false };
}

/** Which side is ahead, or null when level. Higher is better whatever the
 *  sign: −1 leads −3. The scoreboard's leader marker reads this. */
export function leadingTeam(gamePoints) {
  if (gamePoints[0] === gamePoints[1]) return null;
  return gamePoints[0] > gamePoints[1] ? 0 : 1;
}

// ============================================================================
// guards.js — Bounds on anything that arrived from another device.
//
// WHY A PEER-TO-PEER GAME NEEDS THESE AT ALL
//   PeerJS signalling goes through a broker on the public internet and the
//   data channel falls back to a relay, so the host tab is reachable from
//   anywhere by anyone who has — or guesses — the room code. The host is
//   somebody's phone: the weaker machine, the one with a battery, and the one
//   holding every hand and the concealed trump. It deserves tighter bounds
//   than a server would get.
//
// WHAT THESE ARE FOR, AND WHAT THEY ARE NOT
//   Not rule enforcement. js/state.js is the enforcement point and is
//   defensive on its own account: playCard() runs canPlay() against the hand
//   the HOST holds, placeBid() runs bidIsLegal(), callTrump() runs canCall(),
//   and every declaration checks its toggle, its stage and its seat. Deleting
//   this whole file would not make one illegal move legal.
//
//   What it does instead is bound WORK AND MEMORY before the engine is
//   reached — a 60 KiB string compared against a hand, a ten-thousand-key
//   patch spread into an object, a megabyte name walked a codepoint at a time.
//
//   There is exactly ONE guard here that prevents a real exploit rather than a
//   cost, and it is validSeat(): see judgement's account of '__proto__'
//   reaching removeSeat(), reproduced against this engine in the suite.
//
//   NOTHING INBOUND CARRIES A SUIT. The bidder chooses trump by handing over a
//   CARD — "this one, face down" — and the suit is read off the card on the
//   host. A wire field naming a suit would be a field that could disagree with
//   the card, and there is no validSuit() here so that adding one is a visible
//   decision rather than a quiet one.
//
// Imports cards.js and rules.js for the shapes it derives — the card alphabet,
// the seat count, the hand size, the bid range — so none is typed twice.
// ============================================================================

import { RANKS, SUITS, SEATS, HAND_SIZE } from './cards.js';
import { MIN_BID, MAX_BID } from './rules.js';

// A type is a short verb like 'playCard'. Anything longer is not a type.
export const MAX_TYPE_LEN = 40;

/**
 * The shape every wire message must have, checked after parsing and before any
 * dispatch. An ARRAY parses fine as JSON and would sail past a typeof check
 * while having no `.type`, so it is excluded by name.
 */
export function validEnvelope(msg) {
  if (!msg || typeof msg !== 'object' || Array.isArray(msg)) return null;
  if (typeof msg.type !== 'string' || msg.type.length > MAX_TYPE_LEN) return null;
  return msg;
}

// ---------------------------------------------------------------------------
// Per-connection message rate limit. In FRONT of the dispatch, because every
// accepted message fans out into a push to the whole table. A refill rate
// rather than a window, because real play is bursty. `now` is a parameter for
// the same reason tick() takes one: a bucket that reads the clock itself can
// only be tested by sleeping.
// ---------------------------------------------------------------------------
export class TokenBucket {
  constructor({ capacity = 40, refillPerSec = 15, now = Date.now() } = {}) {
    this.capacity = capacity;
    this.refillPerSec = refillPerSec;
    this.tokens = capacity;
    this.stamp = now;
  }

  /** True if this message may proceed. Costs one token. */
  take(now = Date.now()) {
    // Clamped so a clock that steps backwards refills nothing rather than
    // draining the bucket by a negative amount.
    const elapsed = Math.max(0, now - this.stamp) / 1000;
    this.stamp = now;
    this.tokens = Math.min(this.capacity, this.tokens + elapsed * this.refillPerSec);
    if (this.tokens < 1) return false;
    this.tokens -= 1;
    return true;
  }
}

// ---------------------------------------------------------------------------
// Input validation. Every one returns a usable value or null — never throws,
// never hands back something half-cleaned — so the cleaned value and the
// verdict are the same expression.
// ---------------------------------------------------------------------------

// Long enough that collisions are impossible, short enough to be obviously
// not a payload. 8 rather than 32 so that a shorter id minted by a sibling
// build is still accepted; a length check is not what stops anyone guessing.
const CLIENT_ID_RE = /^[A-Za-z0-9_-]{8,64}$/;

export function validClientId(raw) {
  return typeof raw === 'string' && CLIENT_ID_RE.test(raw) ? raw : null;
}

/** A PeerJS connection id. Minted by the broker, so length only. */
export function validPlayerId(raw) {
  return typeof raw === 'string' && raw.length > 0 && raw.length <= 64 ? raw : null;
}

// Rank then suit, exactly two characters, built from the arrays in cards.js.
const CARD_CODE_RE = new RegExp(`^[${RANKS.join('')}][${SUITS.join('')}]$`);

/** A card code as this app writes them: 'JS', '9H', 'TD'. */
export function validCardCode(raw) {
  return typeof raw === 'string' && CARD_CODE_RE.test(raw) ? raw : null;
}

/**
 * A seat index. THE ONE GUARD THAT STOPS AN ACTUAL EXPLOIT: `this.seats
 * ['__proto__']` is Array.prototype, truthy and with no isBot or connected,
 * so removeSeat()'s checks pass — and splice() coerces the string to 0 and
 * removes the owner. Integer-only closes it here.
 */
export function validSeat(raw) {
  return Number.isInteger(raw) && raw >= 0 && raw < SEATS ? raw : null;
}

/**
 * A bid: a whole number in the bid range. NOT LOAD-BEARING — the engine's
 * bidIsLegal() refuses all of these already, with the right reason. It is the
 * one written-down answer to "what shape is a bid".
 */
export function validBid(raw) {
  return Number.isInteger(raw) && raw >= MIN_BID && raw <= MAX_BID ? raw : null;
}

// cleanName() in rules.js caps a name at sixteen, but walks the whole string
// first, so it must not be handed a megabyte. Generous relative to the sixteen
// that survive, for alphabets with combining marks.
export const MAX_RAW_NAME_LEN = 256;

export function validName(raw) {
  return typeof raw === 'string' && raw.length > 0 && raw.length <= MAX_RAW_NAME_LEN ? raw : null;
}

/**
 * A config patch as the lobby sends it. THE CAP IS THE POINT: setConfig()
 * spreads the patch BEFORE normalizeConfig() drops unknown keys. Four real
 * keys; sixteen leaves room without a second thought.
 */
export const MAX_PATCH_KEYS = 16;

export function validConfigPatch(raw) {
  if (!raw || typeof raw !== 'object' || Array.isArray(raw)) return null;
  const keys = Object.keys(raw);
  if (keys.length === 0 || keys.length > MAX_PATCH_KEYS) return null;
  return raw;
}

// ---------------------------------------------------------------------------
// The other direction: what a CLIENT accepts from its host.
//
// A room code is four characters on a public broker, so a code typed one
// character wrong resolves to whoever else holds that id — and render() reads
// pub.seats.map(...) without looking. Shape checks, deliberately only shape:
// whether the host is dealing itself jacks is not knowable from here.
// ---------------------------------------------------------------------------

export function validPublicState(raw) {
  if (!raw || typeof raw !== 'object' || Array.isArray(raw)) return null;
  if (typeof raw.phase !== 'string' || raw.phase.length > MAX_TYPE_LEN) return null;
  if (!Array.isArray(raw.seats) || raw.seats.length > SEATS) return null;
  // The arrays every screen walks unconditionally.
  for (const key of ['plays', 'log', 'history', 'tricks']) if (!Array.isArray(raw[key])) return null;
  if (!Array.isArray(raw.gamePoints) || raw.gamePoints.length !== 2) return null;
  if (!Array.isArray(raw.points) || raw.points.length !== 2) return null;
  if (!raw.config || typeof raw.config !== 'object' || Array.isArray(raw.config)) return null;
  if (!raw.auction || typeof raw.auction !== 'object' || !Array.isArray(raw.auction.calls)) return null;
  // The seat pointers, each used as an index. Small non-negative integers;
  // not checked against seats.length, because an empty lobby honestly reports
  // dealerSeat 0 with no seats.
  for (const key of ['dealerSeat', 'leadSeat', 'turnSeat', 'trickIndex']) {
    const n = raw[key];
    if (!Number.isInteger(n) || n < 0 || n > SEATS * HAND_SIZE) return null;
  }
  return raw;
}

/** One device's own hand. Null is legitimate — a device not seated yet has no
 *  private state — so the caller checks for null before calling this. */
export function validPrivateState(raw) {
  if (!raw || typeof raw !== 'object' || Array.isArray(raw)) return null;
  if (!Array.isArray(raw.hand) || raw.hand.length > HAND_SIZE) return null;
  if (validSeat(raw.seat) === null) return null;
  for (const key of ['bidOptions', 'declareOptions']) {
    if (raw[key] !== null && raw[key] !== undefined && !Array.isArray(raw[key])) return null;
  }
  return raw;
}

// ---------------------------------------------------------------------------
// Frame decoding for the PeerJS transport. 64 KiB is comfortably above the
// largest thing this app sends: a full publicState deep into a match is a few
// kilobytes. Character count rather than encoded bytes — stricter, never
// looser, and no TextEncoder per frame.
// ---------------------------------------------------------------------------
export const MAX_FRAME_BYTES = 65536;

export function decodePeerFrame(raw, { maxBytes = MAX_FRAME_BYTES } = {}) {
  if (typeof raw === 'string') {
    if (raw.length > maxBytes) return null;
    let msg;
    try { msg = JSON.parse(raw); } catch (_) { return null; }
    return validEnvelope(msg);
  }
  if (raw instanceof ArrayBuffer || ArrayBuffer.isView(raw)) return null;
  return validEnvelope(raw);
}

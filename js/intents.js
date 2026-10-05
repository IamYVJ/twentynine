// ============================================================================
// intents.js — The one place a message from a device turns into a call on the
// engine.
//
// WHY ONE DISPATCHER, AND WHY ON DAY ONE
//   Two things will eventually be authoritative: the host tab today, and a
//   server later (js/config.js carries the seams). If each wrote its own switch
//   they would drift — one would accept a field the other ignores — and the bug
//   would surface as two devices disagreeing about who took a trick. In
//   `sequence` this file was retrofitted and the rework was the expensive kind.
//   Here it exists from the first intent, and the answer to "what can a client
//   ask the host to do?" is a list at the top of a file.
//
// WHAT THIS IS NOT
//   Not a transport: it takes an actor id and a plain object and returns a
//   plain object. Not the whole protocol: joining, leaving, watching and state
//   sync are about the connection and stay in js/net.js. And not rule
//   enforcement: every case calls straight through to a method that checks
//   the phase, the seat, the turn, the card, the toggle and the owner itself.
//   What this file adds is turning wire values into arguments the engine can
//   be handed safely.
//
// THE CLOCK IS A PARAMETER, defaulting to 0 rather than Date.now(): a caller
// that forgets gets a phase stamped at zero, which any test notices at once.
// ============================================================================

import { validBid, validCardCode, validConfigPatch, validName, validSeat } from './guards.js';

/**
 * Anything a seated player may send about their own turn. Every one is checked
 * BY SEAT inside the engine — only the engine knows whose turn it is, and the
 * answer changes between a message being framed and arriving.
 */
export const PLAYER_INTENTS = Object.freeze([
  // The auction.
  'placeBid', 'passBid',
  // The bidder's trump.
  'chooseTrump', 'chooseSeventh',
  // The declarations window.
  'singleHand', 'double', 'redouble', 'passDeclare',
  // Play: the call and the card are two separate intents, because they are
  // two separate decisions — see callTrump() in js/state.js.
  'callTrump', 'playCard',
  // The pair, by whoever holds it, when their side wins a trick.
  'declarePair',
]);

/**
 * Anything only the room's owner may send. `isOwner` is who holds the
 * controls; `isHost` is which tab runs the engine, lives in js/net.js, and is
 * kept apart from the start so a server can take one without the other.
 */
export const OWNER_INTENTS = Object.freeze(['setConfig', 'addBot', 'removeSeat', 'startMatch', 'nextDeal']);

export const GAME_INTENTS = Object.freeze([...PLAYER_INTENTS, ...OWNER_INTENTS]);

/**
 * Which intents belong to which toggle. When the toggle is off, each of these
 * is refused by the engine in every state — and the suite drives every one of
 * them through THIS dispatcher in every state of random deals to prove it,
 * rather than trusting the engine method alone. A fifth toggle with an intent
 * of its own must appear here or the module refuses to load (below).
 */
export const TOGGLE_INTENTS = Object.freeze({
  pair: Object.freeze(['declarePair']),
  double: Object.freeze(['double', 'redouble']),
  singleHand: Object.freeze(['singleHand']),
  seventh: Object.freeze(['chooseSeventh']),
});

/**
 * WHERE THE OWNER CHECK HAPPENS: in the engine, every time, and only there.
 * Every owner method takes `actorId` first and runs _isOwner() on it, and a
 * future server calls the engine directly without passing through here. So
 * SELF_GUARDED is a claim about the engine; the loop below makes the claim
 * total at import, and the suite exercises it from a non-owner seat.
 */
export const SELF_GUARDED = Object.freeze(['setConfig', 'addBot', 'removeSeat', 'startMatch', 'nextDeal']);

for (const type of OWNER_INTENTS) {
  if (!SELF_GUARDED.includes(type)) throw new Error(`intents.js: owner intent '${type}' does not say where it is gated`);
}
for (const type of SELF_GUARDED) {
  if (!OWNER_INTENTS.includes(type)) throw new Error(`intents.js: '${type}' is claimed owner-guarded but is not an owner intent`);
}
for (const list of Object.values(TOGGLE_INTENTS)) {
  for (const type of list) {
    if (!PLAYER_INTENTS.includes(type)) throw new Error(`intents.js: toggle intent '${type}' is not a player intent`);
  }
}

/**
 * Every OTHER public method of GameEngine: callable, deliberately not
 * reachable from the wire. COMPLETE ON PURPOSE — the suite asserts that every
 * public method on GameEngine.prototype is in exactly one of GAME_INTENTS and
 * this list, so a new method fails the suite until somebody has decided which
 * side of the wire it lives on.
 *
 *   reset                  a one-message wipe of the match.
 *   addPlayer, disconnect  connection lifecycle; js/net.js knows who connected.
 *   tick                   the clock, driven by the host, never by a peer —
 *                          a peer that could tick could sweep a trick off the
 *                          table before anybody had looked.
 *   serialize, restore     host-local persistence. serialize() holds EVERY
 *                          HAND AND THE CONCEALED TRUMP; restore() would let a
 *                          peer install a match of its own choosing.
 *   resumeAsOwner          hands the room to an id with no check — correct for
 *                          the host tab after a restore, an ownership grab for
 *                          anybody else.
 *   seatOf, startBlocker,  read-only; the answers are already in the state
 *   publicState,           every device is sent.
 *   privateStateFor
 */
export const LOCAL_ONLY = Object.freeze([
  'reset', 'addPlayer', 'disconnect', 'seatOf', 'resumeAsOwner', 'startBlocker',
  'tick', 'publicState', 'privateStateFor', 'serialize', 'restore',
]);

for (const type of LOCAL_ONLY) {
  if (GAME_INTENTS.includes(type)) throw new Error(`intents.js: '${type}' is both wire-reachable and local-only`);
}

/**
 * Apply one game message. Returns `{ handled, result }`:
 *
 *   handled false  not a game intent — a join, a heartbeat, something from a
 *                  newer client. The transport keeps looking.
 *   handled true   it WAS one, and `result` is `{ ok: true, … }` or
 *                  `{ ok: false, error }`. A refusal goes to the sender alone.
 *
 * NEVER THROWS ON A MESSAGE, whatever arrives. It does NOT catch exceptions
 * from the engine: those are invariant violations in this code, and swallowing
 * them would turn a bug into a tap that quietly did nothing.
 */
export function applyGameIntent(engine, actorId, msg, now = 0) {
  const type = msg && msg.type;
  if (typeof type !== 'string') return { handled: false, result: null };

  switch (type) {
    // --- the auction --------------------------------------------------------
    case 'placeBid': {
      // Shape only. Whether 21 is legal depends on the high bid, which the
      // engine has and this file does not.
      const bid = validBid(msg.bid);
      if (bid === null) return done({ ok: false, error: 'That is not a bid.' });
      return done(engine.placeBid(actorId, bid, now));
    }
    case 'passBid': return done(engine.passBid(actorId, now));

    // --- trump ---------------------------------------------------------------
    case 'chooseTrump': {
      // A CARD, not a suit — see the header of js/guards.js.
      const code = validCardCode(msg.code);
      if (code === null) return done({ ok: false, error: 'That is not a card.' });
      return done(engine.chooseTrump(actorId, code, now));
    }
    case 'chooseSeventh': return done(engine.chooseSeventh(actorId, now));

    // --- declarations --------------------------------------------------------
    case 'singleHand':  return done(engine.singleHand(actorId, now));
    case 'double':      return done(engine.double(actorId, now));
    case 'redouble':    return done(engine.redouble(actorId, now));
    case 'passDeclare': return done(engine.passDeclare(actorId, now));

    // --- play ----------------------------------------------------------------
    case 'callTrump': return done(engine.callTrump(actorId, now));
    case 'playCard': {
      const code = validCardCode(msg.code);
      if (code === null) return done({ ok: false, error: 'That is not a card.' });
      return done(engine.playCard(actorId, code, now));
    }
    case 'declarePair': return done(engine.declarePair(actorId, now));

    // --- the lobby, owner-checked inside the engine --------------------------
    case 'setConfig': {
      // `msg.patch` — and judgement's lobby was dead for a while because this
      // line read `msg.config` while main.js sent `patch`. The suite's
      // main.js <-> intents.js field check crosses that seam mechanically.
      const patch = validConfigPatch(msg.patch);
      if (patch === null) return done({ ok: false, error: 'That is not a setting.' });
      return done(engine.setConfig(actorId, patch));
    }
    case 'addBot': {
      // A name that fails the guard is treated as an absent one: the bot gets
      // a name from the list either way.
      const name = msg.name === undefined || msg.name === null ? null : validName(msg.name);
      return done(engine.addBot(actorId, name));
    }
    case 'removeSeat': {
      // Refused rather than defaulted — see validSeat() for what '__proto__'
      // would do to this room.
      const seat = validSeat(msg.seat);
      if (seat === null) return done({ ok: false, error: 'That is not a seat.' });
      return done(engine.removeSeat(actorId, seat));
    }
    case 'startMatch': return done(engine.startMatch(actorId, now));
    case 'nextDeal':   return done(engine.nextDeal(actorId, now));

    default:
      return { handled: false, result: null };
  }
}

// Every engine method reachable from here returns `{ ok, … }`; the fallback
// covers the one that later does not.
function done(result) {
  return { handled: true, result: result || { ok: true } };
}

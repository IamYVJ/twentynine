// ============================================================================
// rules.js — The host's choices, and the shape of a legal bid.
//
// No state and no engine here. Everything is a constant or a pure function of
// its arguments, so this module is safe to import from the bot, the tests, the
// UI and a future server alike.
//
// Three things live here:
//
//   * THE BID RANGE. Sixteen to twenty-eight in steps of one, ascending only.
//     The ceiling is not typed: it is PACK_POINTS from js/cards.js, summed
//     from the point table, because a bid is a claim on card points and you
//     cannot claim more than the pack holds.
//   * THE FOUR TOGGLES and the three presets that set them. normalizeConfig()
//     is the ALLOW-LIST every config crosses on its way in from the wire.
//   * THE WORDS for each toggle — the lobby label, the lobby blurb, and the
//     sentence the rules sheet in index.html carries. The sheet is static
//     prose in a <dialog> (so it works even if the modules fail to load), and
//     the suite checks that it says, verbatim, what this file says — and that
//     every number it quotes is the number js/scoring.js actually uses.
//
// Imports only js/cards.js. `node` can exercise every rule in here and the
// browser can load it with no build step.
// ============================================================================

import { PACK_POINTS } from './cards.js';

/**
 * A frozen lookup table with NO PROTOTYPE. Keyed by strings off the wire —
 * see the note on table() in js/cards.js.
 */
function table(obj) { return Object.freeze(Object.assign(Object.create(null), obj)); }

// ---------------------------------------------------------------------------
// The bid range
// ---------------------------------------------------------------------------

/** The opening bid. A rule of the game rather than arithmetic: it is just
 *  over half the pack's points, so a contract is always a claim to take more
 *  than the other side. */
export const MIN_BID = 16;

/** The highest bid: every point in the pack. DERIVED, never typed. */
export const MAX_BID = PACK_POINTS;

/** Bids rise by one. */
export const BID_STEP = 1;

/**
 * Every bid that may be made over the current high bid, ascending.
 *
 * `high` is null before anybody has bid, and then the floor is MIN_BID.
 * Otherwise it is strictly higher — "each player either bids higher than the
 * current high bid or passes". Empty once the high bid is MAX_BID, which is
 * also the moment the auction ends.
 */
export function legalBids(high) {
  const floor = high === null || high === undefined ? MIN_BID : high + BID_STEP;
  const out = [];
  for (let b = Math.max(MIN_BID, floor); b <= MAX_BID; b += BID_STEP) out.push(b);
  return out;
}

/** Whether one specific bid may be made. The host's enforcement point; the
 *  auction pad's greying-out mirrors it and is never a substitute for it. */
export function bidIsLegal(bid, high) {
  return Number.isInteger(bid) && legalBids(high).includes(bid);
}

/** Why a bid cannot be made, phrased for an aria-label. Null when it can. */
export function illegalBidReason(bid, high) {
  if (bidIsLegal(bid, high)) return null;
  if (!Number.isInteger(bid) || bid < MIN_BID || bid > MAX_BID) {
    return `bids run from ${MIN_BID} to ${MAX_BID}`;
  }
  return `must be higher than ${high}`;
}

// ###########################################################################
//
//  THE FOUR TOGGLES
//
//  Everything below is the host's choice of game. There are exactly four
//  toggles, they are booleans, they are independent, and together they make
//  2^4 = 16 games — few enough that the suite plays bot matches under every
//  one of them rather than sampling. That count is asserted, not because 16
//  matters but because a fifth toggle added quietly here is a fifth toggle
//  the bot, the declarations window and the rules sheet were never told
//  about.
//
//    pair        K and Q of trump in one hand moves the bid by four
//    double      the opponents may double, the bidders redouble
//    singleHand  any player may undertake to win all eight tricks alone
//    seventh     the bidder may take an unseen seventh card as trump
//
//  No combination is illegal and no pair is special-cased. The presets are
//  three POINTS in the space rather than three games with their own code.
//
// ###########################################################################

export const TOGGLES = Object.freeze(['pair', 'double', 'singleHand', 'seventh']);

export const DEFAULT_CONFIG = Object.freeze({ pair: true, double: true, singleHand: false, seventh: false });

/**
 * Clean an untrusted config into a frozen, playable one.
 *
 * THE ONLY PLACE A CONFIG IS CHECKED. Built from the fixed list of toggle
 * names, so an unknown key is dropped rather than carried, and each value
 * must be an actual boolean — the string "false" is truthy, and a host on a
 * strange client sending it must not switch a rule ON. Anything that is not a
 * boolean falls back to the default for that toggle.
 *
 * Frozen, and every value a primitive, which makes the shallow freeze a deep
 * one. js/state.js hands this object straight out in publicState() on the
 * strength of that.
 */
export function normalizeConfig(raw) {
  const c = raw && typeof raw === 'object' ? raw : {};
  const out = {};
  for (const key of TOGGLES) out[key] = typeof c[key] === 'boolean' ? c[key] : DEFAULT_CONFIG[key];
  return Object.freeze(out);
}

/** Every one of the sixteen configs, in a fixed order. The suite's soak and
 *  the "each toggle off is unreachable" sweep both walk this. */
export function allConfigs() {
  const out = [];
  for (let mask = 0; mask < 2 ** TOGGLES.length; mask++) {
    const c = {};
    TOGGLES.forEach((key, i) => { c[key] = !!(mask & (1 << i)); });
    out.push(normalizeConfig(c));
  }
  return out;
}

// ---------------------------------------------------------------------------
// Presets
//
// The family's presets-plus-toggles pattern: picking a preset sets all four
// toggles and nothing else happens, and the toggles stay exposed underneath.
// Changing one afterwards leaves you on a config that matches no preset,
// which is what presetMatching() is for and what the lobby shows as "Custom".
// ---------------------------------------------------------------------------

export const PRESETS = Object.freeze([
  Object.freeze({
    id: 'classic',
    label: 'Classic',
    blurb: 'Pair and doubling on. The game as most tables play it.',
    config: Object.freeze({ pair: true, double: true, singleHand: false, seventh: false }),
  }),
  Object.freeze({
    id: 'full',
    label: 'Full table',
    blurb: 'Every option on: pair, doubling, single hand and the seventh card.',
    config: Object.freeze({ pair: true, double: true, singleHand: true, seventh: true }),
  }),
  Object.freeze({
    id: 'first',
    label: 'First game',
    blurb: 'Every option off. Just bid, hide a trump and play.',
    config: Object.freeze({ pair: false, double: false, singleHand: false, seventh: false }),
  }),
]);

/** The preset this config IS, or null for a custom one. */
export function presetMatching(config) {
  const hit = PRESETS.find((p) => TOGGLES.every((k) => p.config[k] === config[k]));
  return hit ? hit.id : null;
}

/** A preset's config, cleaned through the same allow-list as anything else. */
export function presetConfig(id) {
  const hit = PRESETS.find((p) => p.id === id);
  return normalizeConfig(hit ? hit.config : DEFAULT_CONFIG);
}

// ---------------------------------------------------------------------------
// The words
//
// Here rather than in js/ui.js because the lobby, the declarations window and
// the rules sheet all name the same toggle, and three copies of "Seventh card"
// is three chances to disagree about what the host chose.
//
// `sheet` is the sentence index.html's rules <dialog> carries for the toggle,
// VERBATIM — the suite checks it is there, and checks every number in it
// against js/scoring.js. The dialog stays static HTML so it opens even when
// the modules fail to load, and this is what keeps the static copy honest.
// ---------------------------------------------------------------------------

export const TOGGLE_LABELS = table({
  pair: {
    label: 'Pair',
    blurb: 'King and queen of trump in one hand moves the bid by four, once the trump is shown.',
    sheet: 'Once trump has been revealed, a player holding the King and Queen of trump can declare the pair when their side wins a trick. If the bidding side holds it, the bid goes down 4 (never below 16); if the opponents hold it, the bid goes up 4 (never above 28). Once per deal.',
  },
  double: {
    label: 'Double',
    blurb: 'The opponents may double before the first lead, and the bidders may redouble.',
    sheet: 'Before the first lead, each opponent of the bidder may double, and if they do, the bidding side may redouble. Doubled, the deal is worth 2 game points; redoubled, 4.',
  },
  singleHand: {
    label: 'Single hand',
    blurb: 'Anyone may undertake to win all eight tricks alone, with no trump. Worth three.',
    sheet: 'After the last four cards, any player may declare single hand: a promise to win all eight tricks alone. The bid is void and there is no trump; the declarer leads and their partner sits out. Winning every trick scores 3 game points; losing any trick costs 3 and ends the deal at once.',
  },
  seventh: {
    label: 'Seventh card',
    blurb: 'The bidder may let their unseen seventh card choose the trump — hidden even from them.',
    sheet: 'Instead of choosing, the bidder may announce seventh card: the seventh card dealt to them becomes the face-down indicator, unseen by everyone — the bidder included.',
  },
});

/** Label for a toggle, falling back to the key so an unknown one renders as
 *  itself rather than as blank space. */
export function toggleLabel(key) {
  const hit = TOGGLE_LABELS[key];
  return hit ? hit.label : String(key);
}

// ---------------------------------------------------------------------------
// Names
// ---------------------------------------------------------------------------

export const MAX_NAME_LEN = 16;

/**
 * Collapse whitespace, drop control characters, cap the length.
 *
 * Written as a codepoint filter rather than a regex because the character
 * class it would need is made of literal control bytes, and a source file
 * containing a raw NUL is a hazard to every tool that later reads it.
 */
export function cleanName(raw) {
  let out = '';
  for (const ch of String(raw == null ? '' : raw)) {
    const cp = ch.codePointAt(0);
    if (cp < 0x20 || (cp >= 0x7F && cp <= 0x9F)) continue;
    out += ch;
  }
  return out.replace(/\s+/g, ' ').trim().slice(0, MAX_NAME_LEN);
}

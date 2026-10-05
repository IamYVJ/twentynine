// ============================================================================
// bot.js — A computer player, and the paced driver that lets it take a turn.
//
// WHY A BOT EXISTS AT ALL
//   Twenty-nine needs exactly four. Bots fill the empty chairs — one person
//   and three bots is a match — and cover the seat of a phone that has gone
//   dark, so a match never stops because somebody's battery did.
//
// ############################################################################
// #  THREE THINGS MAKE THIS BOT DIFFERENT FROM judgement'S, AND ALL THREE    #
// #  ARE ESSENTIAL:                                                          #
// #                                                                          #
// #  1. IT PLAYS FOR ITS PARTNER. It feeds points (J 9 A 10) to a partner    #
// #     who is winning a trick and likely to keep it, throws pointless cards #
// #     (K Q 8 7) when an opponent is winning, never overtakes its partner,  #
// #     and does not outbid its partner without a reason.                    #
// #                                                                          #
// #  2. IT PLAYS BLIND TO THE TRUMP. A seat that is not entitled to know the #
// #     trump decides from exactly the view a human in that seat gets, so    #
// #     its only question when void is whether CALLING is worth it.          #
// #                                                                          #
// #  3. IT BIDS ON FOUR CARDS. Jacks, nines, suit length, and an estimate of #
// #     what a partner brings — and, under seventh card, whether its four    #
// #     cards show no suit worth choosing.                                   #
// ############################################################################
//
// THE SHAPE. chooseBid(), chooseTrump(), chooseCall(), chooseCard() and
// chooseDeclare() are PURE: each reads the two views the engine already hands
// a human — publicState() and privateStateFor() — holds nothing between calls,
// and returns a decision. The config arrives inside the public view
// (pub.config) and is never assumed. That buys:
//
//   * No second copy of the rules. privateStateFor() has already run the
//     engine's legality over every card (`legal`), offered the bids
//     (`bidOptions`), the declarations (`declareOptions`), the call
//     (`canCall`) and the pair (`canPair`). This file only ranks what it was
//     offered, so it cannot make an illegal move even when the ranking is
//     wrong — and the soak counts the refusals to prove it.
//   * NO CHEATING, BY CONSTRUCTION. Bots run on the host, and the host knows
//     every hand and the concealed trump. The only thing keeping a bot honest
//     is that it is handed publicState() and ONE seat's private view —
//     nothing else, ever. Do not add a third parameter. The suite replays
//     deals with the hidden trump swapped and requires every decision made
//     before the reveal by a seat not entitled to it to come out the same.
//
// NO TIMERS IN THE THINKING, AND NO THINKING IN THE TIMER. The pause before a
// bot moves is the driver's business, at the bottom of this file, and time is
// a parameter there as it is in js/state.js.
//
// Node-safe: imports cards.js, trick.js, rules.js, intents.js and state.js,
// none of which touch the DOM.
// ============================================================================

import { SUITS, RANKS, buildPack, suitOf, rankOf, rankValue, cardPoints, pointsIn, PACK_POINTS } from './cards.js';
import { nextSeat, partnerOf, sameTeam, teamOf, ledSuitOf, winningPlay, wouldWin, seatsFrom } from './trick.js';
import { MIN_BID, MAX_BID } from './rules.js';
import { applyGameIntent } from './intents.js';
// Only for the phase names. state.js does not import this module, so there is
// no cycle, and taking the constants rather than writing 'play' here is what
// stops a renamed phase leaving every bot quietly asleep.
import { PHASES } from './state.js';

// ---------------------------------------------------------------------------
// Tuning. Every number here is an admission that this is an estimate, not a
// solver. Exported so the suite can read them and a change is a visible diff.
// They were set by running the soak and measuring how often bot contracts are
// made — see the bot section of scripts/test-engine.mjs — not by reasoning.
// ---------------------------------------------------------------------------

/** The points a side takes on an average deal: half the pack. DERIVED. */
const EVEN = PACK_POINTS / 2;

/** How far below its own estimate the bot stops bidding. A bid AT the
 *  estimate is made about half the time, and an undoubled contract made half
 *  the time is worth nothing on average — while a thrown-in deal is worth
 *  nothing for certain. Measured over the soak: at 1 a fifth of all deals were
 *  thrown in by four cautious bots; at 0 the bidders made 59%; a quarter of a
 *  point gives about one throw-in in eight and contracts made three in five. */
export const BID_CAUTION = 0.25;

/**
 * The weights of the four-card estimate, FITTED rather than chosen: a least-
 * squares regression of the bidding side's card points on the bidder's first
 * four cards, over twelve thousand bot-played deals. Points in hand dropped
 * out entirely once trump strength and side jacks were in the model — a jack
 * already counts in both — which is why they are not a term. The residual is
 * about 4.7 points: four cards really do not say much about eight.
 */
export const TRUMP_WEIGHT = 0.7;
export const SIDE_JACK_WEIGHT = 1.9;
export const PARTNER_BID_BONUS = 1.5;
export const PARTNER_PASS_PENALTY = 1;

/** A bot outbids its own partner only when its estimate beats the partner's
 *  bid by at least this much. Raising your own side's contract only makes it
 *  harder, so the reason has to be a real one. */
export const PARTNER_OVERBID_MARGIN = 4;

/** The points on the table that make a call worth it. Calling commits a void
 *  player to trumping if they can and shows the suit to everybody; for a trick
 *  of sevens and eights that is a bad trade. */
export const CALL_FOR_POINTS = 2;

// ---------------------------------------------------------------------------
// Small shared helpers
// ---------------------------------------------------------------------------

const PACK = Object.freeze(buildPack());

/** Accepts plain codes and the `{ code, legal }` objects privateStateFor()
 *  sends, because both callers exist. */
function codesOf(hand) {
  if (!Array.isArray(hand)) return [];
  return hand.map((c) => (typeof c === 'string' ? c : (c && c.code))).filter((c) => typeof c === 'string' && c.length === 2);
}

function bySuit(codes) {
  const out = Object.create(null);
  for (const s of SUITS) out[s] = [];
  for (const c of codes) if (out[suitOf(c)]) out[suitOf(c)].push(c);
  for (const s of SUITS) out[s].sort((a, b) => rankValue(b) - rankValue(a));
  return out;
}

/** Deterministic argmax/argmin: ties break on the code string, so the same
 *  position always produces the same card and a soak failure can be replayed. */
function pickBy(codes, score, want = 'max') {
  let best = null;
  let bestScore = 0;
  for (const code of codes) {
    const s = score(code);
    if (best === null || (want === 'max' ? s > bestScore : s < bestScore) || (s === bestScore && code < best)) {
      best = code; bestScore = s;
    }
  }
  return best;
}

const lowest = (codes) => pickBy(codes, (c) => rankValue(c) * 10 + cardPoints(c), 'min');

// ===========================================================================
//
//  BIDDING, ON FOUR CARDS
//
// ===========================================================================

/**
 * How good a suit would be as trump, from what this hand holds of it.
 *
 * The jack and the nine are the two top trumps and carry five of the suit's
 * seven points between them; length is what lets trumps win tricks the side
 * would otherwise lose. Read off four cards in the auction, or eight later.
 */
export function trumpStrength(codes, suit) {
  const cards = codes.filter((c) => suitOf(c) === suit);
  if (!cards.length) return 0;
  const has = (r) => cards.some((c) => rankOf(c) === r);
  return 3 * has('J') + 2 * has('9') + has('A') + has('T') + 1.5 * (cards.length - 1);
}

/** The suit this hand would choose as trump, with its strength. Ties go to the
 *  longer suit, then to the suit order — deterministic, so a bot that bid on
 *  a suit is a bot that chooses it. */
export function bestTrump(codes) {
  let best = null;
  for (const suit of SUITS) {
    const s = trumpStrength(codes, suit);
    const len = codes.filter((c) => suitOf(c) === suit).length;
    if (!best || s > best.strength || (s === best.strength && len > best.len)) best = { suit, strength: s, len };
  }
  return best;
}

/**
 * The card points this hand's SIDE expects to take if it wins the auction,
 * from four cards.
 *
 * Half the pack is the baseline, because a partnership with average cards
 * takes half. On top of that: the points in hand (a four-card hand averages
 * PACK_POINTS / 8), how strong the best trump suit is, and the side jacks —
 * each one a likely trick that takes other cards' points with it. The partner
 * is assumed average unless they have said otherwise in the auction: a bid
 * says they are strong, a pass says they are not.
 *
 * The weights came from the soak, not from a formula; see BID_CAUTION.
 */
export function estimateSide(codes, { partnerBid = null, partnerPassed = false } = {}) {
  const t = bestTrump(codes);
  const sideJacks = codes.filter((c) => rankOf(c) === 'J' && suitOf(c) !== t.suit).length;
  let e = EVEN + TRUMP_WEIGHT * t.strength + SIDE_JACK_WEIGHT * sideJacks;
  if (partnerBid !== null) e += PARTNER_BID_BONUS;
  else if (partnerPassed) e -= PARTNER_PASS_PENALTY;
  return e;
}

/** Everything chooseBid() reads, off the two views. */
function auctionView(pub, priv) {
  const seat = priv.seat;
  const partner = partnerOf(seat);
  const calls = (pub.auction && pub.auction.calls) || [];
  const partnerBid = calls.filter((c) => c.seat === partner && c.bid !== null).map((c) => c.bid).pop() ?? null;
  const partnerPassed = calls.some((c) => c.seat === partner && c.bid === null);
  return {
    codes: codesOf(priv.hand),
    high: pub.auction ? pub.auction.high : null,
    highSeat: pub.auction ? pub.auction.highSeat : null,
    partner, partnerBid, partnerPassed,
    legal: (priv.bidOptions || []).filter((o) => o && o.legal).map((o) => o.bid),
  };
}

/**
 * The bid: a number, or null to pass. PURE.
 *
 * Bids the lowest legal number when that is within its estimate, and passes
 * otherwise. It does not jump: in a simple ascending auction a jump only
 * spends the side's own headroom.
 */
export function chooseBid(pub, priv) {
  const v = auctionView(pub, priv);
  if (!v.legal.length) return null;
  const est = estimateSide(v.codes, { partnerBid: v.partnerBid, partnerPassed: v.partnerPassed });
  const ceiling = Math.min(MAX_BID, Math.floor(est - BID_CAUTION));
  const next = v.legal[0];
  if (next > ceiling) return null;
  // DO NOT OUTBID THE PARTNER WITHOUT A REASON. Their bid already stands for
  // the side; raising it only makes the contract harder to make. The reason
  // that justifies it is a hand clearly stronger than theirs looked.
  if (v.highSeat !== null && v.highSeat === v.partner) {
    if (ceiling < v.high + PARTNER_OVERBID_MARGIN) return null;
  }
  return next;
}

// ===========================================================================
//
//  TRUMP
//
// ===========================================================================

/** How far short of the bid this side must expect to leave the bidders before
 *  doubling. See chooseDeclare(). */
export const DOUBLE_MARGIN = 6;

/** Below this, the four cards show no suit worth naming, and under seventh
 *  card the bidder lets the pack choose. */
export const SEVENTH_BELOW = 4;

/**
 * The bidder's choice: { seventh: true } or { code } — the card to put face
 * down. PURE.
 *
 * The indicator is the LOWEST card of the chosen suit. It is out of the hand
 * until the reveal, so it should be the trump the bidder will miss least: the
 * jack and nine stay in hand where they can win tricks.
 */
export function chooseTrump(pub, priv) {
  const codes = codesOf(priv.hand);
  const best = bestTrump(codes);
  const offered = priv.trumpChoice && priv.trumpChoice.seventh === true;
  if (offered && best.strength < SEVENTH_BELOW) return { seventh: true };
  const suitCards = codes.filter((c) => suitOf(c) === best.suit);
  return { code: lowest(suitCards) };
}

// ===========================================================================
//
//  DECLARATIONS
//
// ===========================================================================

/**
 * Could this hand win all eight tricks alone, with no trump and the lead?
 *
 * Only if every suit it holds is held FROM THE TOP: the jack, then the nine,
 * then the ace, unbroken. Led in that order, no card it leads can be beaten,
 * because with no trump only a higher card of the same suit wins and every
 * higher card is in this hand. Anything less can lose a trick to a card it
 * cannot see — and a lost trick ends the deal at −3. So in practice: almost
 * never, as the brief says.
 */
export function cannotLose(codes) {
  if (codes.length === 0) return false;
  const held = bySuit(codes);
  for (const suit of SUITS) {
    const cards = held[suit];
    for (let i = 0; i < cards.length; i++) {
      if (rankOf(cards[i]) !== RANKS[i]) return false;
    }
  }
  return true;
}

/**
 * One of priv.declareOptions: 'single', 'double', 'redouble' or 'pass'. PURE.
 *
 *   single    only on a hand that cannot lose a trick (see cannotLose). The
 *             bidder's eight include the indicator, which comes back to them
 *             under single hand — but only a bidder who chose it can count
 *             it; under seventh card it is a card they have never seen.
 *   double    an opponent of the bidder, when its own eight cards make the
 *             contract look unlikely: if this side's likely points leave the
 *             bidders short of their bid.
 *   redouble  rarely: the bidding side, when it expects comfortably more than
 *             the contract.
 */
export function chooseDeclare(pub, priv) {
  const opts = priv.declareOptions || [];
  const offer = opts.find((o) => o !== 'pass');
  if (!offer) return 'pass';
  const codes = codesOf(priv.hand);

  if (offer === 'single') {
    const eight = priv.indicator ? codes.concat([priv.indicator]) : codes;
    const known = priv.isBidder ? (pub.trumpMode === 'concealed' && priv.indicator !== null) : true;
    return known && eight.length === 8 && cannotLose(eight) ? 'single' : 'pass';
  }

  // Our side's likely points from our eight cards: half the pack, adjusted by
  // how far this hand's points and jacks are from an average hand's.
  const avg = (PACK_POINTS / PACK.length) * codes.length;
  const jacks = codes.filter((c) => rankOf(c) === 'J').length;
  const mine = EVEN + 1.2 * (pointsIn(codes) - avg) + 1.0 * (jacks - 1);
  const bid = pub.finalBid ?? pub.bid ?? MIN_BID;

  if (offer === 'double') {
    // The bidders need `bid`; we expect to leave them PACK_POINTS - mine. A
    // double pays only when the contract is made less than half the time, and
    // measured over the soak, doubled contracts were still made 52% of the
    // time at a margin of 2 and 41% at DOUBLE_MARGIN.
    return PACK_POINTS - mine < bid - DOUBLE_MARGIN ? 'double' : 'pass';
  }
  if (offer === 'redouble') {
    return mine >= bid + 5 ? 'redouble' : 'pass';
  }
  return 'pass';
}

// ===========================================================================
//
//  PLAY
//
// ===========================================================================

/**
 * Everything the play decisions need, read off the two views once per turn.
 *
 * The bot holds no memory between calls, so what has gone and who is void in
 * what are rebuilt from pub.tricks every time — which is why they can never
 * drift from the real game, and why a bot covering a seat mid-deal knows
 * exactly what the seat's previous occupant could have known.
 *
 * `trump` is what THIS SEAT may know: the revealed suit, or the bidder's own
 * concealed choice — and null for everybody else before the reveal. It is
 * read from priv.knownTrump, which the engine fills only for a seat entitled
 * to it, and from nowhere else.
 */
function playView(pub, priv) {
  const seat = priv.seat;
  const plays = Array.isArray(pub.plays) ? pub.plays : [];
  const tricks = Array.isArray(pub.tricks) ? pub.tricks : [];
  const hand = codesOf(priv.hand);
  const out = pub.single ? pub.single.out : null;

  const seen = new Set();
  const voids = [new Set(), new Set(), new Set(), new Set()];
  const watch = (trickPlays) => {
    const led = trickPlays.length ? suitOf(trickPlays[0].code) : null;
    for (const p of trickPlays) {
      seen.add(p.code);
      if (led && suitOf(p.code) !== led) voids[p.seat].add(led);
    }
  };
  for (const t of tricks) watch(t.plays || []);
  watch(plays);

  // What this seat cannot see: the pack, less its own hand, less the table,
  // less its own face-down indicator if it chose one.
  const mine = new Set(hand);
  if (priv.indicator) mine.add(priv.indicator);
  // After the reveal the indicator is a known card in the bidder's hand: not
  // in play yet, but not unknown either.
  const unseen = PACK.filter((c) => !seen.has(c) && !mine.has(c));

  // Seats still to play to this trick, in order.
  const order = plays.length ? seatsFrom(plays[0].seat, out) : seatsFrom(seat, out);
  const toAct = order.slice(plays.length + 1);

  const best = winningPlay(plays);
  return {
    seat, hand, plays, unseen, voids, out, toAct,
    partner: partnerOf(seat),
    led: ledSuitOf(plays),
    revealed: pub.revealed === true,
    trump: priv.knownTrump || null,
    publicTrump: pub.trump || null,
    winning: best,
    tablePoints: pointsIn(plays.map((p) => p.code)),
    legal: (priv.hand || []).filter((c) => c && c.legal).map((c) => c.code),
    bidder: pub.bidder,
    single: pub.single,
  };
}

/** Would this card play AS A TRUMP if played now? Only after the reveal —
 *  before it, even the bidder's trumps are plain cards. */
function asTrump(v, code) {
  return v.revealed && v.publicTrump !== null && suitOf(code) === v.publicTrump;
}

/** Does this card win the trick as it stands? Asked of trick.js, so the bot's
 *  idea of who is winning cannot drift from the engine's. */
function takes(v, code) {
  return wouldWin(v.plays, v.seat, code, asTrump(v, code));
}

/** No unseen card of its suit outranks it. */
function isBoss(v, code) {
  const s = suitOf(code);
  const r = rankValue(code);
  return !v.unseen.some((u) => suitOf(u) === s && rankValue(u) > r);
}

/**
 * Will the trick as it stands stay with whoever is winning it?
 *
 * Safe when nobody is left to play, or when every seat still to play is a
 * partner — or when the winning card is the boss of its suit and no opponent
 * still to play can trump it. An opponent can trump when they are known to be
 * void in the led suit AND trump is either revealed (and the card is not
 * already a trump that beats theirs) or still hidden (they could call). This
 * seat cannot know who holds trumps, so a known void is enough to worry.
 */
function holds(v, play) {
  const opponents = v.toAct.filter((s) => !sameTeam(s, play.seat));
  if (!opponents.length) return true;
  if (play.trump) {
    // A trump that is the highest trump still out cannot be beaten.
    return isBoss(v, play.code);
  }
  if (!isBoss(v, play.code)) return false;
  // Boss of the led suit — beaten only by a trump from somebody void in it.
  const led = v.led || suitOf(play.code);
  return !opponents.some((s) => v.voids[s].has(led));
}

/**
 * Whether to call for trump, given the choice. PURE.
 *
 * Called only when priv.canCall is true: this seat is void in the led suit,
 * trump is still hidden, and it is its turn.
 *
 * A SEAT THAT DOES NOT KNOW THE TRUMP — every non-bidder, and the bidder under
 * seventh card — calls when the trick holds points worth taking and its
 * partner is not already winning it. Calling commits it to trumping if it can,
 * and it cannot see whether it can; so for a trick of nothing, or one its
 * partner already has, it plays a plain discard instead.
 *
 * THE BIDDER WITH A CONCEALED TRUMP knows the suit and its own trumps. It
 * reveals when the same test passes AND it will hold a trump to win with —
 * which it always will, because the indicator comes back to its hand.
 */
export function chooseCall(pub, priv) {
  if (!priv || !priv.canCall) return false;
  const v = playView(pub, priv);
  const partnerWinning = v.winning && v.winning.seat === v.partner;
  if (partnerWinning) return false;
  if (v.tablePoints >= CALL_FOR_POINTS) return true;
  // The bidder can also reveal to win a trick its side needs that holds any
  // points at all, knowing the indicator will come back as a trump.
  if (v.trump && priv.isBidder && v.tablePoints >= 1) return true;
  return false;
}

/** The playCard choice: one code from priv.hand's legal cards. PURE. */
export function chooseCard(pub, priv) {
  const v = playView(pub, priv);
  if (!v.legal.length) return null;
  if (v.legal.length === 1) return v.legal[0];
  return v.plays.length ? follow(v) : lead(v);
}

// ---------------------------------------------------------------------------
// Leading
// ---------------------------------------------------------------------------

function lead(v) {
  const legal = v.legal;
  const held = bySuit(legal);
  const trumpKnown = v.trump;

  // 1. Cash a boss card — one nothing unseen can beat in its own suit. A jack
  //    is the commonest, and leading it draws the suit's other points into a
  //    trick it will win. Not a trump-suit card the bidder knows is trump
  //    before the reveal: led then, it is a plain card, and the bidder wants
  //    its trumps for later. After the reveal, leading a boss trump draws
  //    the opposition's.
  const bosses = legal.filter((c) => isBoss(v, c)
    && !(trumpKnown && !v.revealed && suitOf(c) === trumpKnown));
  if (bosses.length) {
    // The boss in the suit with the most points still out, so the trick it
    // wins is worth the most.
    return pickBy(bosses, (c) => {
      const outPts = pointsIn(v.unseen.filter((u) => suitOf(u) === suitOf(c)));
      return outPts * 10 + held[suitOf(c)].length;
    }, 'max');
  }

  // 2. Otherwise lead something that costs nothing: the lowest pointless card
  //    from the longest suit that is not a known trump before the reveal.
  const cheap = legal.filter((c) => cardPoints(c) === 0
    && !(trumpKnown && !v.revealed && suitOf(c) === trumpKnown));
  if (cheap.length) {
    return pickBy(cheap, (c) => held[suitOf(c)].length * 100 - rankValue(c), 'max');
  }
  return lowest(legal);
}

// ---------------------------------------------------------------------------
// Following
// ---------------------------------------------------------------------------

function follow(v) {
  const legal = v.legal;
  const partnerWinning = v.winning && v.winning.seat === v.partner;
  const winners = legal.filter((c) => takes(v, c));
  const losers = legal.filter((c) => !takes(v, c));

  if (partnerWinning) {
    // NEVER OVERTAKE THE PARTNER. A card that would take the trick off them
    // spends a strong card to win what the side already has.
    const kind = losers.length ? losers : legal;
    if (holds(v, v.winning)) {
      // FEED THE PARTNER: the most points that are not themselves a future
      // winner — a boss jack fed here is a trick thrown away later.
      return pickBy(kind, (c) => cardPoints(c) * 10 - (isBoss(v, c) && cardPoints(c) >= 2 ? 25 : 0) - rankValue(c) * 0.1, 'max');
    }
    // The partner may lose it: give away nothing.
    return pickBy(kind, (c) => cardPoints(c) * 1000 + rankValue(c), 'min');
  }

  // An opponent is winning.
  if (winners.length) {
    // Take it with the cheapest card that keeps it. If nobody after us can
    // beat a card, the cheapest winner is enough; otherwise prefer a winner
    // that holds.
    const keepers = winners.filter((c) => holds(v, { seat: v.seat, code: c, trump: asTrump(v, c) }));
    const pool = keepers.length ? keepers : winners;
    const worth = v.tablePoints + Math.max(...pool.map((c) => cardPoints(c)));
    // A trick of nothing is not worth a winner that will not hold — and not
    // worth a boss we can use later — unless it costs us nothing.
    if (worth > 0 || keepers.length) {
      return pickBy(pool, (c) => rankValue(c) * 10 + (asTrump(v, c) ? 100 : 0) - cardPoints(c), 'min');
    }
  }
  // Cannot (or should not) win it: THROW A POINTLESS CARD to the opponents —
  // K Q 8 7 before anything that scores, whatever else is true of it. Among
  // the pointless cards, keep a boss back if another will do, then the lowest.
  const pool = losers.length ? losers : legal;
  return pickBy(pool, (c) => cardPoints(c) * 1000 + (isBoss(v, c) ? 50 : 0) + rankValue(c), 'min');
}

// ===========================================================================
//
//  WHAT A BOT DOES WITH A TURN, WHATEVER KIND OF TURN IT IS
//
// ===========================================================================

/**
 * The one intent this seat owes the table right now, or null.
 *
 * The pair comes first and is not a turn: whoever holds it may declare it the
 * moment their side wins a trick, whoever's turn it is. "It declares the pair
 * whenever that is legal, because it always helps the side that holds it."
 */
export function chooseIntent(pub, priv) {
  if (!pub || !priv) return null;
  if (priv.canPair) return { type: 'declarePair' };
  if (!priv.isTurn) return null;
  switch (pub.phase) {
    case PHASES.AUCTION: {
      const bid = chooseBid(pub, priv);
      return bid === null ? { type: 'passBid' } : { type: 'placeBid', bid };
    }
    case PHASES.TRUMP_CHOICE: {
      const t = chooseTrump(pub, priv);
      return t.seventh ? { type: 'chooseSeventh' } : { type: 'chooseTrump', code: t.code };
    }
    case PHASES.DECLARE: {
      const c = chooseDeclare(pub, priv);
      return { type: { single: 'singleHand', double: 'double', redouble: 'redouble', pass: 'passDeclare' }[c] };
    }
    case PHASES.PLAY: {
      if (priv.canCall && chooseCall(pub, priv)) return { type: 'callTrump' };
      const code = chooseCard(pub, priv);
      return code ? { type: 'playCard', code } : null;
    }
    default:
      return null;
  }
}

/** How long a bot appears to think — judgement's number, for judgement's
 *  reason: long enough that the table sees what happened, short enough not
 *  to drag across eight tricks. */
export const BOT_THINK_MS = 1500;

/** How long the table waits for a DROPPED human before covering their turn.
 *  The project's standing ten seconds: a screen lock or a 4G handover is
 *  invisible, and the table does not sit staring at a game that has stopped.
 *  A seat that LEFT is not waited for at all — see coverage(). */
export const OFFLINE_GRACE_MS = 10000;

/** Should the driver move for this seat? A bot, at a bot's pace. A human who
 *  pressed LEAVE, at a bot's pace — they said they are not coming back soon.
 *  A human whose connection dropped, after the grace period. The seat is
 *  COVERED, never converted: the ticket takes it back the same way. */
function coverage(seat) {
  if (!seat) return null;
  if (seat.isBot) return 'bot';
  if (!seat.connected) return seat.left ? 'left' : 'offline';
  return null;
}

/** Whose move the table is waiting for, in every phase that can wait on one.
 *  Not during the sweep pause: turnSeat names the trick's winner then, and the
 *  engine would refuse a card anyway. */
function waitingOn(engine) {
  switch (engine.phase) {
    case PHASES.AUCTION:
    case PHASES.DECLARE:
      return engine.seats[engine.turnSeat] || null;
    case PHASES.TRUMP_CHOICE:
      return engine.seats[engine.bidder] || null;
    case PHASES.PLAY:
      return engine.sweepAt === null ? engine.seats[engine.turnSeat] || null : null;
    default:
      return null;
  }
}

/**
 * A stateful ticker, one per game, driven from whatever loop already calls
 * engine.tick() — js/main.js today, a server later. It holds only "which turn
 * am I waiting on, and until when", and is never serialised.
 *
 * DELIBERATELY DOES NOT ADVANCE PAST DEAL_OVER. nextDeal() is owner-gated and
 * the owner is always a human, so the deal-over screen waits for a person.
 */
export function createBotDriver({ thinkMs = BOT_THINK_MS, offlineMs = OFFLINE_GRACE_MS } = {}) {
  let pending = null;

  return {
    /** @returns true if the engine changed and the caller should broadcast. */
    tick(engine, now = Date.now()) {
      if (!engine) return false;

      // The pair first, and at once: it is offered only until the next card,
      // and a bot that thought for a second and a half would miss it behind
      // the sweep. It is a declaration, not a turn, so nobody waits on it.
      if (engine.phase === PHASES.PLAY) {
        for (const seat of engine.seats) {
          if (!coverage(seat)) continue;
          const priv = engine.privateStateFor(seat.id);
          if (priv && priv.canPair) {
            const { result } = applyGameIntent(engine, seat.id, { type: 'declarePair' }, now);
            if (result && result.ok) return true;
          }
        }
      }

      const player = waitingOn(engine);
      const cover = coverage(player);
      if (!cover) { pending = null; return false; }

      // The key has to change on every distinct action a seat could take, or
      // the second is mistaken for the first and never happens. A call is
      // followed by a card from the same seat in the same trick, so whether
      // trump is revealed is part of the key.
      const key = [
        engine.phase, player.id, cover, engine.dealIndex, engine.trickIndex, engine.plays.length,
        engine.auction.calls.length, engine.declare ? `${engine.declare.stage}${engine.declare.at}` : '-',
        engine.revealed ? 'r' : 'h',
      ].join(':');

      const wait = cover === 'offline' ? offlineMs : thinkMs;
      if (!pending || pending.key !== key) pending = { key, dueAt: now + wait, acted: false };
      if (pending.acted || now < pending.dueAt) return false;

      // One attempt per step, whatever happens below.
      pending.acted = true;
      return act(engine, player, now);
    },

    /** Forget the pause in progress. */
    reset() { pending = null; },
  };
}

/** Counted, so the soak can assert a bot never needed its fallback. */
export const botStats = { refused: 0, fallbacks: 0 };

function act(engine, player, now) {
  const priv = engine.privateStateFor(player.id);
  let intent = null;
  try {
    intent = chooseIntent(engine.publicState(), priv);
  } catch (err) {
    console.warn('[bot] chooseIntent threw', err);
  }
  if (intent) {
    const { result } = applyGameIntent(engine, player.id, intent, now);
    if (result && result.ok) return true;
    botStats.refused += 1;
    console.warn('[bot] move refused:', result && result.error, intent);
  }
  // Last resort, and it should be unreachable: the table cannot proceed past a
  // seat that will not act, so a bad move beats no move.
  botStats.fallbacks += 1;
  const fallback = panic(priv);
  if (!fallback) return false;
  const { result } = applyGameIntent(engine, player.id, fallback, now);
  return !!(result && result.ok);
}

function panic(priv) {
  if (!priv) return null;
  if (Array.isArray(priv.bidOptions)) return { type: 'passBid' };
  if (priv.trumpChoice) return priv.hand[0] ? { type: 'chooseTrump', code: priv.hand[0].code } : null;
  if (Array.isArray(priv.declareOptions)) return { type: 'passDeclare' };
  const card = Array.isArray(priv.hand) ? priv.hand.find((c) => c && c.legal) : null;
  return card ? { type: 'playCard', code: card.code } : null;
}

export { teamOf, nextSeat };

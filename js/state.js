// ============================================================================
//
//  js/state.js — the game engine
//
//  One object holds the whole match. The host's tab owns it, every intent is
//  applied here, and every other tab sees only what publicState() and
//  privateStateFor() choose to hand out.
//
//  FOUR RULES SHAPE EVERYTHING BELOW.
//
//  1. THE ENGINE IS THE ENFORCEMENT POINT. Follow-suit, the caller's
//     obligation to trump, bids, calls and declarations are all decided here,
//     on the host, against the host's own copy of every hand. The client greys
//     out an illegal card as a courtesy. It is never what stops the card.
//
//  2. NOTHING MUTATES ON A REJECTED ACTION. Every action returns { ok: true }
//     or { ok: false, error }, and every early return is before the first
//     write. Half of a rejected call landing — the trump revealed but the
//     obligation not set — is worse than the call landing.
//
//  3. TIME IS A PARAMETER. There is not one timer in here. `now` arrives from
//     the caller and tick(now) advances the display pauses, so the suite can
//     play thousands of matches in seconds and a replay lands exactly.
//
//  4. THE CONCEALED TRUMP. Until somebody calls for it, the trump suit is
//     known to this object and to the bidder — and under the seventh-card
//     rule, not even to the bidder. It is held in exactly two fields,
//     `indicator` (the face-down card) and `trumpCard` (the card that set the
//     suit, which outlives the indicator going back into the bidder's hand).
//     Neither is ever read by publicState(), and privateStateFor() reads them
//     only for the one seat entitled to them. The suite does not trust this
//     paragraph: it swaps the hidden card for another one, in every state of
//     thousands of deals, and requires every view that should not know to
//     come out byte-identical.
//
//  isHost vs isOwner — kept apart from the first line, as in judgement:
//
//    isOwner  a PLAYER who controls the lobby and moves the match on from
//             DEAL_OVER. It lives in this file, on a seat, and survives a
//             reconnect through clientId.
//    isHost   a TAB that happens to be running this engine. NOT IN THIS FILE.
//             js/net.js knows which tab that is.
//
// ============================================================================

import {
  SEATS, HAND_SIZE, buildPack, shuffle as shufflePack, dealBatch, sortHand,
  suitOf, rankOf, cardName, suitName,
} from './cards.js';
import {
  nextSeat, prevSeat, seatsFrom, nextActiveSeat, teamOf, partnerOf, sameTeam,
  ledSuitOf, canCall, legalPlays, canPlay, illegalReason, playsAsTrump, winningPlay,
} from './trick.js';
import {
  MIN_BID, MAX_BID, legalBids, bidIsLegal, illegalBidReason,
  normalizeConfig, DEFAULT_CONFIG, cleanName,
} from './rules.js';
import {
  trickPoints, pointsBySide, pairAdjust, dealResult, singleHandResult,
  applyDelta, matchOutcome, multiplierFor, leadingTeam,
} from './scoring.js';

// ---------------------------------------------------------------------------
// Phases
//
// Exactly the ladder the brief draws:
//
//   LOBBY -> FIRST_FOUR -> AUCTION -> TRUMP_CHOICE -> LAST_FOUR -> DECLARE*
//        -> PLAY -> DEAL_OVER -> (next deal | MATCH_OVER)
//
//   AUCTION with four passes throws the deal in and goes straight back to
//   FIRST_FOUR with the next dealer. DECLARE is skipped entirely when both of
//   its toggles are off.
//
// What is NOT a phase, on purpose:
//
//   * THE REVEAL and THE PAIR. Both happen mid-trick and must not reset it —
//     a call is the second action of a player's turn, between seeing the lead
//     and playing a card. They are fields (`revealed`, `pair`), not states.
//   * THE SWEEP. After the last card of a trick the trick stays on the table
//     and every play is refused until it is cleared. That is `sweepAt`, a
//     timestamp tick() reads, and publicState() reports it as `sweeping` so a
//     client can tell the two halves of PLAY apart.
// ---------------------------------------------------------------------------

export const PHASES = Object.freeze({
  LOBBY: 'lobby',
  FIRST_FOUR: 'firstFour',
  AUCTION: 'auction',
  TRUMP_CHOICE: 'trumpChoice',
  LAST_FOUR: 'lastFour',
  DECLARE: 'declare',
  PLAY: 'play',
  DEAL_OVER: 'dealOver',
  MATCH_OVER: 'matchOver',
});

// How long the transient phases hold. Display timings, not rules — the engine
// works the same at zero, and the tests mostly run at zero.
export const FIRST_FOUR_MS = 900;
export const LAST_FOUR_MS = 900;
export const TRICK_PAUSE_MS = 1400;

// The rolling log is pushed to every peer on every send, so it is capped.
const LOG_CAP = 60;

// Short, and distinguishable when spoken across a table.
const BOT_NAMES = Object.freeze(['Robin', 'Asha', 'Kito', 'Vera', 'Milo', 'Noor', 'Dara']);

/**
 * Seal a completed deal record: copied and frozen all the way down, so that
 * nothing reachable through it is shared with the caller or writable. THE ONLY
 * PLACE A RECORD IS SEALED — both _endDeal() and restore() come here, and it
 * takes no list of fields so a field added later is sealed by the same rule.
 * judgement's freezeRound(), for judgement's reasons.
 */
function freezeRecord(v) {
  if (Array.isArray(v)) return Object.freeze(v.map((x) => freezeRecord(x)));
  if (!v || typeof v !== 'object') return v;
  const proto = Object.getPrototypeOf(v);
  if (proto !== Object.prototype && proto !== null) return v;
  const out = {};
  for (const [k, val] of Object.entries(v)) out[k] = freezeRecord(val);
  return Object.freeze(out);
}

export class GameEngine {
  /**
   * `shuffle` is the one seam a test may use to choose the pack. Defaults to
   * the real Fisher-Yates. It is a constructor argument rather than a method
   * so that nothing on the wire can ever reach it — js/intents.js dispatches
   * to methods, and this is not one.
   */
  constructor({ shuffle = shufflePack } = {}) {
    this.shuffler = shuffle;
    this.reset();
  }

  // -------------------------------------------------------------------------
  // The whole of the state, in one place. A field that first appears halfway
  // down a method is a field serialize() will eventually forget.
  // -------------------------------------------------------------------------
  reset() {
    this.phase = PHASES.LOBBY;
    this.phaseAt = 0;
    this.config = normalizeConfig(DEFAULT_CONFIG);
    this.ownerId = null;

    // --- the table: index IS the seat; teams are seat % 2 ---
    this.seats = [];

    // --- the match ---
    this.dealIndex = -1;
    this.dealerSeat = 0;
    this.gamePoints = [0, 0];
    this.history = [];
    this.outcome = null;      // matchOutcome() once a side crosses a line

    this._resetDeal();
    this.log = [];
  }

  /** Everything that belongs to ONE deal, cleared at the start of the next. */
  _resetDeal() {
    this.hands = [[], [], [], []];   // never public, never sent to anyone but its owner
    this.stock = [];                 // the second batch, before it is dealt: never public

    // The auction. Bids are public the moment they are made; a bid being
    // composed on a phone never reaches this object at all.
    this.auction = { high: null, highSeat: null, passed: [false, false, false, false], calls: [] };
    this.bidder = null;
    this.bid = null;                 // the winning bid
    this.finalBid = null;            // after any pair

    // THE SECRET. See rule 4 in the header.
    this.trumpMode = null;           // 'concealed' | 'seventh' — public: everybody saw it chosen
    this.indicator = null;           // the face-down card, until it goes back to the bidder
    this.trumpCard = null;           // the card that set the suit; outlives the indicator
    this.revealed = false;
    this.revealedBy = null;
    this.revealTrick = null;
    this.caller = null;              // who called on the CURRENT trick and still owes a trump

    // Declarations.
    this.declare = null;             // { stage, order, at } while DECLARE is open
    this.level = 0;                  // 0 none, 1 doubled, 2 redoubled
    this.doubledBy = null;
    this.redoubledBy = null;
    this.single = null;              // { seat, out } — the declarer and the partner who sits out
    this.singleLost = false;
    this.pair = null;                // { seat, team, from, to }
    this.pairWindow = null;          // { team, trickIndex } — open after a trick, until the next card

    // Play.
    this.plays = [];                 // [{ seat, code, trump }]
    this.tricks = [];                // completed and swept: [{ plays, winner }]
    this.trickIndex = 0;
    this.leadSeat = 0;
    this.turnSeat = 0;
    this.lastTrick = null;
    this.sweepAt = null;
    this.pointsWon = [0, 0];
    this.tricksWon = [0, 0, 0, 0];
  }

  /** The trump suit, or null. Derived, so it cannot disagree with the card
   *  that set it — and null in a single-hand deal, where there is no trump. */
  get trumpSuit() {
    return this.trumpCard && !this.single ? suitOf(this.trumpCard) : null;
  }

  // ###########################################################################
  //
  //  SEATING
  //
  // ###########################################################################

  /**
   * Seat a player, or give them back the seat they already had.
   *
   * Reclaim is by clientId and BY NOTHING ELSE, in any phase. A name is never
   * a seat ticket: the scoreboard is public, so a seat that could be reclaimed
   * by naming it could be stolen by naming it — and with it, a hand.
   */
  addPlayer(id, name, { clientId = null, isOwner = false } = {}) {
    const clean = cleanName(name) || 'Player';

    if (clientId) {
      const seat = this.seats.findIndex((s) => s.clientId && s.clientId === clientId);
      if (seat !== -1) return this._reclaim(seat, id, clean);
    }

    if (this.phase !== PHASES.LOBBY) return { ok: false, error: 'the match has already started' };
    if (this.seats.length >= SEATS) return { ok: false, error: `the table is full at ${SEATS}` };

    const seat = this.seats.length;
    this.seats.push({
      id, clientId,
      name: this._uniqueName(clean),
      isOwner: isOwner || seat === 0,
      isBot: false,
      connected: true,
      left: false,
    });
    if (this.seats[seat].isOwner) this.ownerId = id;
    this._say(`${this.seats[seat].name} joined`, 'join', seat);
    return { ok: true, seat };
  }

  _reclaim(seat, id, name) {
    const s = this.seats[seat];
    const fresh = !s.connected;
    s.id = id;
    s.connected = true;
    s.left = false;
    if (this.phase === PHASES.LOBBY && name) s.name = this._uniqueName(name, seat);
    if (s.isOwner) this.ownerId = id;
    if (fresh) this._say(`${s.name} reconnected`, 'join', seat);
    return { ok: true, seat, reclaimed: true };
  }

  _uniqueName(name, exceptSeat = -1) {
    const taken = new Set(this.seats.filter((_, i) => i !== exceptSeat).map((s) => s.name));
    if (!taken.has(name)) return name;
    for (let n = 2; n <= SEATS + 1; n++) {
      const tryName = `${name.slice(0, 13)} ${n}`;
      if (!taken.has(tryName)) return tryName;
    }
    return name;
  }

  /**
   * A connection dropped — or, with { left: true }, a player said goodbye.
   *
   * In the LOBBY the seat is removed: it holds nothing, and an empty chair
   * would block the start. MID-MATCH the seat stays exactly where it is with
   * its hand and its game points, so the clientId can claim it back.
   *
   * `left` is the difference between a tunnel and a goodbye. js/bot.js covers
   * a dropped seat after a grace period and a seat that left at once.
   */
  disconnect(id, options = null) {
    const left = !!options && options.left === true;
    const seat = this.seatOf(id);
    if (seat === -1) return { ok: false, error: 'not seated' };
    const who = this.seats[seat].name;

    if (this.phase === PHASES.LOBBY) {
      const wasOwner = this.seats[seat].isOwner;
      this.seats.splice(seat, 1);
      if (wasOwner) this._promoteOwner();
      this._say(`${who} left`, 'leave');
      return { ok: true, removed: true };
    }

    this.seats[seat].connected = false;
    this.seats[seat].left = left;
    this._say(`${who} ${left ? 'left' : 'disconnected'}`, 'leave', seat);
    return { ok: true, seat };
  }

  _promoteOwner() {
    this.ownerId = null;
    const heir = this.seats.findIndex((s) => !s.isBot);
    if (heir === -1) return;
    this.seats[heir].isOwner = true;
    this.ownerId = this.seats[heir].id;
  }

  addBot(actorId, name = null) {
    if (!this._isOwner(actorId)) return { ok: false, error: 'only the owner can add a bot' };
    if (this.phase !== PHASES.LOBBY) return { ok: false, error: 'the match has already started' };
    if (this.seats.length >= SEATS) return { ok: false, error: `the table is full at ${SEATS}` };
    return this._seatBot(name);
  }

  _seatBot(name = null) {
    const seat = this.seats.length;
    this.seats.push({
      id: `bot:${seat}`,
      clientId: null,
      name: this._uniqueName(cleanName(name) || BOT_NAMES[seat % BOT_NAMES.length]),
      isOwner: false,
      isBot: true,
      connected: true,
      left: false,
    });
    this._say(`${this.seats[seat].name} (bot) joined`, 'join', seat);
    return { ok: true, seat };
  }

  /** Vacate a lobby chair: a bot, or a human who is not here. Refuses to remove
   *  a connected player — that is kicking, and the brief does not ask for it. */
  removeSeat(actorId, seat) {
    if (!this._isOwner(actorId)) return { ok: false, error: 'only the owner can remove a seat' };
    if (this.phase !== PHASES.LOBBY) return { ok: false, error: 'the match has already started' };
    const s = this.seats[seat];
    if (!s) return { ok: false, error: 'no such seat' };
    if (!s.isBot && s.connected) return { ok: false, error: `${s.name} is still here` };
    this.seats.splice(seat, 1);
    if (s.isOwner) this._promoteOwner();
    this._say(`${s.name} left`, 'leave');
    return { ok: true };
  }

  setConfig(actorId, patch) {
    if (!this._isOwner(actorId)) return { ok: false, error: 'only the owner can change the game' };
    // A toggle switched mid-match would open or close a phase the table is
    // already in. The lobby is the only time the rules may change.
    if (this.phase !== PHASES.LOBBY) return { ok: false, error: 'the match has already started' };
    this.config = normalizeConfig({ ...this.config, ...patch });
    return { ok: true, config: this.config };
  }

  seatOf(id) { return this.seats.findIndex((s) => s.id === id); }

  _isOwner(id) {
    const seat = this.seatOf(id);
    return seat !== -1 && this.seats[seat].isOwner;
  }

  /** Hand ownership to a seat with no check of any kind — the host tab's own
   *  call after restore(). Kept off the wire for exactly that reason; see
   *  LOCAL_ONLY in js/intents.js. */
  resumeAsOwner(ownerId) {
    const seat = this.seatOf(ownerId);
    if (seat === -1) return { ok: false, error: 'not seated' };
    for (const s of this.seats) s.isOwner = false;
    this.seats[seat].isOwner = true;
    this.ownerId = ownerId;
    this._say(`${this.seats[seat].name} is now the host`, 'system', seat);
    return { ok: true, seat };
  }

  // ###########################################################################
  //
  //  THE MATCH
  //
  // ###########################################################################

  /** Why the match cannot start yet, or null. Fewer than four is NOT a blocker:
   *  startMatch() fills the empty chairs with bots, which is the brief's "bots
   *  fill empty seats" — one person and three bots is a match. */
  startBlocker() {
    if (this.phase !== PHASES.LOBBY) return 'the match has already started';
    if (!this.seats.length) return 'nobody is seated';
    if (this.seats.some((s) => !s.connected && !s.isBot)) return 'somebody is disconnected';
    return null;
  }

  startMatch(actorId, now = 0) {
    if (!this._isOwner(actorId)) return { ok: false, error: 'only the owner can start' };
    const blocker = this.startBlocker();
    if (blocker) return { ok: false, error: blocker };

    while (this.seats.length < SEATS) this._seatBot();
    this.gamePoints = [0, 0];
    this.history = [];
    this.outcome = null;
    this.dealIndex = -1;
    // Seat zero deals first. _beginDeal() moves the dealer one seat on before
    // dealing, so it starts one seat BEFORE zero in turn order.
    this.dealerSeat = prevSeat(0);
    const names = (team) => [team, team + 2].map((s) => this.seats[s].name).join(' & ');
    this._say(`Match on: ${names(0)} against ${names(1)}. First to +6 wins; −6 loses.`, 'system');
    return this._beginDeal(now);
  }

  // -------------------------------------------------------------------------
  // The deal, in two batches
  // -------------------------------------------------------------------------

  _beginDeal(now) {
    this.dealIndex += 1;
    // ANTICLOCKWISE, through trick.js. The dealer moves to the right.
    this.dealerSeat = nextSeat(this.dealerSeat);
    this._resetDeal();

    // "The dealer gives four cards to each player, starting on their right."
    // The order comes from trick.js and is handed to the deal — see dealBatch()
    // in js/cards.js for why the deal does not compute it itself.
    const order = seatsFrom(nextSeat(this.dealerSeat));
    const { hands, stock } = dealBatch(this.shuffler(buildPack()), order);
    for (const seat of order) this.hands[seat] = hands[seat];
    this.stock = stock;

    this._say(`Deal ${this.dealIndex + 1}: ${this._name(this.dealerSeat)} deals`, 'deal');
    this._enter(PHASES.FIRST_FOUR, now);
    return { ok: true, phase: this.phase };
  }

  /**
   * Advance anything waiting on the clock. Idempotent: every branch either
   * fires once and moves the state on, or does nothing.
   */
  tick(now = 0) {
    if (this.phase === PHASES.FIRST_FOUR && now - this.phaseAt >= FIRST_FOUR_MS) {
      this._beginAuction(now);
      return true;
    }
    if (this.phase === PHASES.LAST_FOUR && now - this.phaseAt >= LAST_FOUR_MS) {
      this._afterLastFour(now);
      return true;
    }
    if (this.sweepAt !== null && now - this.sweepAt >= TRICK_PAUSE_MS) {
      this._sweepTrick(now);
      return true;
    }
    return false;
  }

  // -------------------------------------------------------------------------
  // The auction
  // -------------------------------------------------------------------------

  _beginAuction(now) {
    // "It starts with the player to the dealer's right."
    this.turnSeat = nextSeat(this.dealerSeat);
    this._enter(PHASES.AUCTION, now);
  }

  placeBid(actorId, bid, now = 0) {
    if (this.phase !== PHASES.AUCTION) return { ok: false, error: 'not bidding right now' };
    const seat = this.seatOf(actorId);
    if (seat === -1) return { ok: false, error: 'not seated' };
    if (seat !== this.turnSeat) return { ok: false, error: `it is ${this._name(this.turnSeat)}'s bid` };
    const high = this.auction.high;
    if (!bidIsLegal(bid, high)) return { ok: false, error: illegalBidReason(bid, high) };

    this.auction.high = bid;
    this.auction.highSeat = seat;
    this.auction.calls.push({ seat, bid });
    this._say(`${this._name(seat)} bids ${bid}`, 'bid', seat);

    // Twenty-eight cannot be beaten, so nobody is asked.
    if (bid === MAX_BID) return this._endAuction(now);
    return this._nextBidder(now);
  }

  passBid(actorId, now = 0) {
    if (this.phase !== PHASES.AUCTION) return { ok: false, error: 'not bidding right now' };
    const seat = this.seatOf(actorId);
    if (seat === -1) return { ok: false, error: 'not seated' };
    if (seat !== this.turnSeat) return { ok: false, error: `it is ${this._name(this.turnSeat)}'s bid` };

    // A PASS IS FINAL for this deal: the seat is never asked again.
    this.auction.passed[seat] = true;
    this.auction.calls.push({ seat, bid: null });
    this._say(`${this._name(seat)} passes`, 'pass', seat);

    const passes = this.auction.passed.filter(Boolean).length;
    if (passes === SEATS) return this._throwIn(now);
    if (this.auction.high !== null && passes === SEATS - 1) return this._endAuction(now);
    return this._nextBidder(now);
  }

  /** The next seat anticlockwise that has not passed. It cannot be the high
   *  bidder while anybody else is still in — getting back round to the high
   *  bidder means everybody between has passed, which ended the auction. */
  _nextBidder() {
    let s = nextSeat(this.turnSeat);
    while (this.auction.passed[s]) s = nextSeat(s);
    this.turnSeat = s;
    return { ok: true, phase: this.phase };
  }

  /** All four passed: no contract, no score, the next dealer deals. Recorded in
   *  the history so the deal count on the scoreboard tells the truth. */
  _throwIn(now) {
    this._say(`All four passed — the deal is thrown in`, 'thrown');
    this.history.push(freezeRecord({
      deal: this.dealIndex, dealer: this.dealerSeat, thrownIn: true,
      gamePoints: this.gamePoints,
    }));
    return this._beginDeal(now);
  }

  _endAuction(now) {
    this.bidder = this.auction.highSeat;
    this.bid = this.auction.high;
    this.finalBid = this.bid;
    this._say(`${this._name(this.bidder)} wins the auction at ${this.bid}`, 'auction', this.bidder);
    this.turnSeat = this.bidder;
    this._enter(PHASES.TRUMP_CHOICE, now);
    return { ok: true, phase: this.phase };
  }

  // -------------------------------------------------------------------------
  // Trump
  // -------------------------------------------------------------------------

  /**
   * The bidder places one of their four cards face down. Its suit is trump.
   *
   * The log line says THAT a card went down and nothing about WHICH. Every
   * sentence this engine writes is read aloud by the live region on every
   * device at the table, and on the television.
   */
  chooseTrump(actorId, code, now = 0) {
    if (this.phase !== PHASES.TRUMP_CHOICE) return { ok: false, error: 'not choosing trump right now' };
    const seat = this.seatOf(actorId);
    if (seat === -1) return { ok: false, error: 'not seated' };
    if (seat !== this.bidder) return { ok: false, error: `${this._name(this.bidder)} chooses the trump` };
    const hand = this.hands[seat];
    if (!hand.includes(code)) return { ok: false, error: 'that card is not in your hand' };

    hand.splice(hand.indexOf(code), 1);
    this.trumpMode = 'concealed';
    this.indicator = code;
    this.trumpCard = code;
    this._say(`${this._name(seat)} places a card face down as the trump indicator`, 'trump', seat);
    return this._beginLastFour(now);
  }

  /** "Seventh card": the bidder declines to choose, and the seventh card dealt
   *  to them becomes the indicator unseen — by them too. Refused when the
   *  toggle is off, which is what makes the toggle real. */
  chooseSeventh(actorId, now = 0) {
    if (!this.config.seventh) return { ok: false, error: 'the seventh-card rule is off in this game' };
    if (this.phase !== PHASES.TRUMP_CHOICE) return { ok: false, error: 'not choosing trump right now' };
    const seat = this.seatOf(actorId);
    if (seat === -1) return { ok: false, error: 'not seated' };
    if (seat !== this.bidder) return { ok: false, error: `${this._name(this.bidder)} chooses the trump` };

    this.trumpMode = 'seventh';
    this._say(`${this._name(seat)} calls for the seventh card — trump will be set face down, unseen by anyone`, 'trump', seat);
    return this._beginLastFour(now);
  }

  _beginLastFour(now) {
    const order = seatsFrom(nextSeat(this.dealerSeat));
    const { hands } = dealBatch(this.stock, order);
    for (const seat of order) {
      let batch = hands[seat];
      if (this.trumpMode === 'seventh' && seat === this.bidder) {
        // The bidder's seventh card is the third of their second four. It goes
        // face down straight off the pack and never touches their hand, so
        // there is no instant at which privateStateFor() could show it.
        const seventh = batch[2];
        batch = batch.filter((_, i) => i !== 2);
        this.indicator = seventh;
        this.trumpCard = seventh;
      }
      this.hands[seat] = this.hands[seat].concat(batch);
    }
    this.stock = [];
    this.turnSeat = this.bidder;
    this._enter(PHASES.LAST_FOUR, now);
    return { ok: true, phase: this.phase };
  }

  // -------------------------------------------------------------------------
  // Declarations — only the toggles that are on
  // -------------------------------------------------------------------------

  _afterLastFour(now) {
    if (this.config.singleHand) {
      // "Starting right of the dealer, each player may declare single hand."
      return this._openDeclare('single', seatsFrom(nextSeat(this.dealerSeat)), now);
    }
    if (this.config.double) return this._openDoubling(now);
    return this._beginPlay(now);
  }

  _openDeclare(stage, order, now) {
    this.declare = { stage, order, at: 0 };
    this.turnSeat = order[0];
    this._enter(PHASES.DECLARE, now);
    return { ok: true, phase: this.phase };
  }

  /** "Each opponent of the bidder may double, in turn" — the opponent on the
   *  bidder's right first, then the other. */
  _openDoubling(now) {
    const order = seatsFrom(nextSeat(this.bidder)).filter((s) => !sameTeam(s, this.bidder));
    return this._openDeclare('double', order, now);
  }

  /** Shared front half of every declaration: right phase, right stage, right
   *  seat. Returns the seat or a refusal. */
  _declarant(actorId, stage) {
    if (this.phase !== PHASES.DECLARE || !this.declare) return { error: 'no declarations are open' };
    const seat = this.seatOf(actorId);
    if (seat === -1) return { error: 'not seated' };
    if (seat !== this.turnSeat) return { error: `it is ${this._name(this.turnSeat)}'s turn to declare` };
    if (stage && this.declare.stage !== stage) return { error: 'that is not on offer right now' };
    return { seat };
  }

  singleHand(actorId, now = 0) {
    if (!this.config.singleHand) return { ok: false, error: 'single hand is off in this game' };
    const d = this._declarant(actorId, 'single');
    if (d.error) return { ok: false, error: d.error };

    const seat = d.seat;
    this.single = { seat, out: partnerOf(seat) };
    // "The original bid is void and there is no trump; the indicator goes back
    // to the bidder's hand." It goes back FACE DOWN — nobody is shown it, and
    // the suit it would have set is never revealed. trumpSuit reads null from
    // here on because `single` is set; trumpCard is kept only so a host
    // snapshot can be replayed exactly.
    if (this.indicator) {
      this.hands[this.bidder].push(this.indicator);
      this.indicator = null;
    }
    this._say(`${this._name(seat)} declares single hand — no trump, ${this._name(this.single.out)} sits out`, 'declare', seat);
    this.declare = null;
    return this._beginPlay(now);
  }

  double(actorId, now = 0) {
    if (!this.config.double) return { ok: false, error: 'doubling is off in this game' };
    const d = this._declarant(actorId, 'double');
    if (d.error) return { ok: false, error: d.error };
    this.level = 1;
    this.doubledBy = d.seat;
    this._say(`${this._name(d.seat)} doubles`, 'declare', d.seat);
    // "If doubled, the bidding side may redouble" — whichever of them comes
    // first after the doubler.
    const order = seatsFrom(nextSeat(d.seat)).filter((s) => sameTeam(s, this.bidder));
    return this._openDeclare('redouble', order, now);
  }

  redouble(actorId, now = 0) {
    if (!this.config.double) return { ok: false, error: 'doubling is off in this game' };
    const d = this._declarant(actorId, 'redouble');
    if (d.error) return { ok: false, error: d.error };
    this.level = 2;
    this.redoubledBy = d.seat;
    this._say(`${this._name(d.seat)} redoubles`, 'declare', d.seat);
    this.declare = null;
    return this._beginPlay(now);
  }

  passDeclare(actorId, now = 0) {
    const d = this._declarant(actorId, null);
    if (d.error) return { ok: false, error: d.error };
    const stage = this.declare.stage;
    this._say(`${this._name(d.seat)} ${stage === 'single' ? 'does not declare single hand' : `does not ${stage}`}`, 'pass', d.seat);
    this.declare.at += 1;
    if (this.declare.at < this.declare.order.length) {
      this.turnSeat = this.declare.order[this.declare.at];
      return { ok: true, phase: this.phase };
    }
    this.declare = null;
    if (stage === 'single' && this.config.double) return this._openDoubling(now);
    return this._beginPlay(now);
  }

  // -------------------------------------------------------------------------
  // Play
  // -------------------------------------------------------------------------

  _beginPlay(now) {
    this.trickIndex = 0;
    this.plays = [];
    // "The player to the dealer's right leads the first trick. Under single
    // hand, the declarer leads."
    this.leadSeat = this.single ? this.single.seat : nextSeat(this.dealerSeat);
    this._enter(PHASES.PLAY, now);
    this._setTurn(this.leadSeat);
    return { ok: true, phase: this.phase };
  }

  /** How many cards make a trick: four, or three while somebody sits out. */
  _trickSize() { return this.single ? SEATS - 1 : SEATS; }

  /**
   * Hand the turn to `seat`, and turn the indicator up if that seat is the
   * bidder with nothing left in hand.
   *
   * "If trump is never called, the indicator is the bidder's last card, and
   * playing it to the eighth trick reveals it." The bidder holds seven cards
   * and the indicator for eight tricks, so their hand is empty exactly when
   * the indicator is the only card they have — and their only legal play. It
   * is turned up as their turn arrives rather than as it lands; nobody can do
   * anything with the interval, and it keeps the card in the hand it is
   * played from like every other card.
   */
  _setTurn(seat) {
    this.turnSeat = seat;
    if (!this.single && !this.revealed && this.indicator
      && seat === this.bidder && this.hands[seat].length === 0) {
      this._reveal(seat, 'last');
    }
  }

  /**
   * THE REVEAL. The indicator is turned up for everyone and goes back into the
   * bidder's hand, and from this instant — not one send earlier — the trump
   * suit is in publicState(). The trick in progress is not touched: cards
   * already on the table keep the role they were played in.
   */
  _reveal(seat, how) {
    this.revealed = true;
    this.revealedBy = seat;
    this.revealTrick = this.trickIndex;
    this.hands[this.bidder].push(this.indicator);
    const shown = this.indicator;
    this.indicator = null;
    const suit = suitName(suitOf(this.trumpCard));
    this._say(how === 'call'
      ? `${this._name(seat)} calls for trump — ${suit} are trumps. The indicator was the ${cardName(shown)}`
      : `${this._name(seat)} turns up the indicator with their last card — the ${cardName(shown)}: ${suit} are trumps`,
    'reveal', seat);
  }

  /**
   * Call for trump. The SECOND of a void player's two choices — the first,
   * playing any card without calling, is just playCard().
   *
   * It does not play a card. The caller's turn continues, now with an
   * obligation: they must play a trump if they hold one. Splitting the two is
   * what lets the UI show the revealed trump and the narrowed hand before the
   * player commits to a card, and it is what makes "call" and "play" two
   * distinct actions rather than a modal that appears halfway through a play.
   */
  callTrump(actorId, now = 0) {
    if (this.phase !== PHASES.PLAY) return { ok: false, error: 'not playing right now' };
    if (this.sweepAt !== null) return { ok: false, error: 'the trick is still on the table' };
    const seat = this.seatOf(actorId);
    if (seat === -1) return { ok: false, error: 'not seated' };
    if (seat !== this.turnSeat) return { ok: false, error: `it is ${this._name(this.turnSeat)}'s turn` };
    if (this.single) return { ok: false, error: 'there is no trump in a single hand' };
    if (this.revealed) return { ok: false, error: 'trump is already face up' };
    const led = ledSuitOf(this.plays);
    if (!led) return { ok: false, error: 'you are leading — you can call only when you cannot follow suit' };
    if (!canCall(this.hands[seat], led, false)) return { ok: false, error: `you can follow ${suitName(led)}, so you cannot call` };

    this._reveal(seat, 'call');
    this.caller = seat;
    return { ok: true, phase: this.phase, revealed: true };
  }

  playCard(actorId, code, now = 0) {
    if (this.phase !== PHASES.PLAY) return { ok: false, error: 'not playing right now' };
    if (this.sweepAt !== null) return { ok: false, error: 'the trick is still on the table' };
    const seat = this.seatOf(actorId);
    if (seat === -1) return { ok: false, error: 'not seated' };
    if (this.single && seat === this.single.out) return { ok: false, error: 'you are sitting out this deal' };
    if (seat !== this.turnSeat) return { ok: false, error: `it is ${this._name(this.turnSeat)}'s turn` };

    // Checked against the HOST'S copy of the hand. The obligation is the trump
    // suit only for the seat that called on this trick — see legalPlays().
    const hand = this.hands[seat];
    const led = ledSuitOf(this.plays);
    const obligation = this.caller === seat ? this.trumpSuit : null;
    if (!canPlay(hand, code, led, obligation)) {
      return { ok: false, error: illegalReason(hand, code, led, obligation) };
    }

    hand.splice(hand.indexOf(code), 1);
    // The role is fixed NOW. A trump-suit card played before the reveal is a
    // plain card for the rest of the trick, and the flag says so.
    this.plays.push({ seat, code, trump: playsAsTrump(code, this.revealed, this.trumpSuit) });
    // The obligation was for this one card, and it has been met.
    if (this.caller === seat) this.caller = null;
    // Any card played closes the pair window: "at the moment their side wins
    // a trick" is over once the table has moved on.
    this.pairWindow = null;

    if (this.plays.length < this._trickSize()) {
      this._setTurn(nextActiveSeat(seat, this.single ? this.single.out : null));
      return { ok: true, phase: this.phase };
    }
    return this._finishTrick(now);
  }

  /**
   * Everybody has played. Decide it, credit the card points, and LEAVE THE
   * CARDS WHERE THEY ARE — the sweep is a separate step on the clock.
   */
  _finishTrick(now) {
    const best = winningPlay(this.plays);
    const winner = best.seat;
    const points = trickPoints(this.plays);
    this.pointsWon[teamOf(winner)] += points;
    this.tricksWon[winner] += 1;
    this.lastTrick = {
      plays: this.plays.map((p) => ({ ...p })),
      winner, card: best.code, points, trickIndex: this.trickIndex,
    };
    this._say(
      `${this._name(winner)} takes trick ${this.trickIndex + 1} with the ${cardName(best.code)}`
      + `${best.trump ? ' (trump)' : ''}${points ? ` — ${points} point${points === 1 ? '' : 's'}` : ''}`,
      'trick', winner,
    );

    if (this.single && winner !== this.single.seat) this.singleLost = true;
    // The pair window opens on any trick won after the reveal, for the side
    // that won it. Whether anybody on that side HOLDS the pair is private, and
    // privateStateFor() answers it per seat.
    if (this.config.pair && this.revealed && !this.single && !this.pair) {
      this.pairWindow = { team: teamOf(winner), trickIndex: this.trickIndex };
    }
    this.sweepAt = now;
    return { ok: true, phase: this.phase, trickWinner: winner };
  }

  _sweepTrick(now) {
    const winner = this.lastTrick.winner;
    this.tricks.push({ plays: this.plays.map((p) => ({ ...p })), winner });
    this.plays = [];
    this.sweepAt = null;
    this.trickIndex += 1;

    // "Losing any trick scores −3 and ends the deal at once." At once means
    // after the table has seen the trick that lost it, which is this sweep.
    if (this.singleLost) return this._endDeal(now);
    if (this.trickIndex >= HAND_SIZE) return this._endDeal(now);

    this.leadSeat = winner;
    this.phaseAt = now;
    this._setTurn(winner);
    return { ok: true, phase: this.phase };
  }

  // -------------------------------------------------------------------------
  // The pair
  // -------------------------------------------------------------------------

  /** Why this seat cannot declare the pair now, or null if it can. Separate
   *  from declarePair() so privateStateFor() can offer the button exactly when
   *  the engine would accept it. */
  _pairBlocker(seat) {
    if (!this.config.pair) return 'the pair is off in this game';
    if (this.phase !== PHASES.PLAY) return 'not playing right now';
    if (this.single) return 'there is no trump in a single hand';
    if (this.pair) return 'the pair has already been declared this deal';
    if (!this.revealed) return 'the pair can be declared only after trump is revealed';
    if (!this.pairWindow || this.pairWindow.team !== teamOf(seat)) {
      return 'the pair is declared when your side wins a trick';
    }
    const t = this.trumpSuit;
    const hand = this.hands[seat] || [];
    if (!hand.includes(`K${t}`) || !hand.includes(`Q${t}`)) return 'you do not hold the King and Queen of trump';
    return null;
  }

  declarePair(actorId, now = 0) {
    const seat = this.seatOf(actorId);
    if (seat === -1) return { ok: false, error: 'not seated' };
    const blocker = this._pairBlocker(seat);
    if (blocker) return { ok: false, error: blocker };

    const helps = sameTeam(seat, this.bidder);
    const from = this.finalBid;
    this.finalBid = pairAdjust(this.finalBid, helps);
    this.pair = { seat, team: teamOf(seat), from, to: this.finalBid };
    this.pairWindow = null;
    this._say(
      `${this._name(seat)} declares the pair — the bid ${helps ? 'drops' : 'rises'} from ${from} to ${this.finalBid}`,
      'pair', seat,
    );
    return { ok: true, phase: this.phase, finalBid: this.finalBid };
  }

  // -------------------------------------------------------------------------
  // Scoring the deal
  // -------------------------------------------------------------------------

  _endDeal(now) {
    const bidTeam = this.single ? teamOf(this.single.seat) : teamOf(this.bidder);
    const sides = pointsBySide(this.tricks);
    const r = this.single
      ? singleHandResult({ lost: this.singleLost })
      : dealResult({ finalBid: this.finalBid, bidPoints: sides[bidTeam], level: this.level });
    this.gamePoints = applyDelta(this.gamePoints, bidTeam, r.delta);
    const outcome = matchOutcome(this.gamePoints);
    if (outcome.over) this.outcome = outcome;

    // The record is complete on its own, so a client that joins in deal nine
    // draws the whole scoreboard from history without having seen deals one
    // to eight. Raw values in; freezeRecord() copies and seals.
    this.history.push(freezeRecord({
      deal: this.dealIndex,
      dealer: this.dealerSeat,
      thrownIn: false,
      bidder: this.bidder,
      bid: this.bid,
      finalBid: this.finalBid,
      pair: this.pair,
      trumpMode: this.trumpMode,
      // Public only if it was revealed — always, in an ordinary deal, because
      // the indicator is played to the last trick at the latest. Never in a
      // single hand, where it went back face down.
      trump: this.revealed ? suitOf(this.trumpCard) : null,
      single: this.single,
      level: this.level,
      multiplier: r.multiplier,
      bidTeam,
      cardPoints: sides,
      tricksPlayed: this.tricks.length,
      made: r.made,
      delta: r.delta,
      gamePoints: this.gamePoints,
    }));

    const side = (team) => `${this._name(team)} & ${this._name(team + 2)}`;
    const line = this.single
      ? `${this._name(this.single.seat)}'s single hand ${r.made ? 'takes all eight' : 'is beaten'}`
      : `${side(bidTeam)} ${r.made ? 'make' : 'miss'} ${this.finalBid} with ${sides[bidTeam]}`;
    this._say(
      `${line}: ${r.delta > 0 ? '+' : '−'}${Math.abs(r.delta)}${r.multiplier > 1 ? ` (×${r.multiplier})` : ''}. `
      + `Game points ${this._gp(0)} to ${this._gp(1)}`,
      r.made ? 'made' : 'missed', this.single ? this.single.seat : this.bidder,
    );
    this._enter(PHASES.DEAL_OVER, now);
    return { ok: true, phase: this.phase };
  }

  _gp(team) {
    const n = this.gamePoints[team];
    return n < 0 ? `−${Math.abs(n)}` : String(n);
  }

  /** Leave the deal-over screen: the next deal, or the end. Owner-driven, like
   *  judgement's nextRound — DEAL_OVER is a real phase, not a modal, and no
   *  timeout is right for four people reading a result. */
  nextDeal(actorId, now = 0) {
    if (this.phase !== PHASES.DEAL_OVER) return { ok: false, error: 'the deal is not over' };
    if (!this._isOwner(actorId)) return { ok: false, error: 'only the owner can move on' };
    if (this.outcome) return this._endMatch(now);
    return this._beginDeal(now);
  }

  _endMatch(now) {
    const o = this.outcome;
    const side = (team) => `${this._name(team)} & ${this._name(team + 2)}`;
    this._say(o.how === 'reached'
      ? `${side(o.winner)} reach +6 and win the match`
      : `${side(o.loser)} fall to −6 — ${side(o.winner)} win the match`, 'match');
    this._enter(PHASES.MATCH_OVER, now);
    return { ok: true, phase: this.phase, winner: o.winner };
  }

  // ###########################################################################
  //
  //  VIEWS — the privacy boundary
  //
  //  publicState() is sent to everybody, including a peer nobody has verified
  //  and a television in the corner of the room. privateStateFor() is sent to
  //  exactly one player. If a field is in the wrong one of these, the game is
  //  broken and will look fine.
  //
  // ###########################################################################

  /** What this seat is entitled to know about the trump, or null. Revealed:
   *  everyone. Concealed and not yet revealed: the bidder alone. Seventh card
   *  and not yet revealed: nobody. Single hand: there is none. */
  _trumpKnownTo(seat) {
    if (this.single || !this.trumpCard) return null;
    if (this.revealed) return this.trumpSuit;
    if (seat === this.bidder && this.trumpMode === 'concealed') return this.trumpSuit;
    return null;
  }

  /**
   * What every peer may see.
   *
   * MISSING ON PURPOSE: every hand, the undealt second batch, and — until the
   * reveal — the indicator card and the trump suit. Before the reveal the
   * indicator is reported as `{ seat, faceUp: false, card: null }`: a card
   * back on the table by the bidder, which is exactly what the table can see.
   * `trumpMode` IS here, because the table watched the bidder choose between
   * a card and the seventh card, and that choice carries no suit.
   *
   * Every array is rebuilt per call and every record frozen at birth, so
   * nothing reachable from here can move the engine.
   */
  publicState() {
    const out = this.single ? this.single.out : null;
    const indicatorFor = () => {
      if (this.bidder === null || !this.trumpMode || this.single) return null;
      if (!this.revealed) return { seat: this.bidder, faceUp: false, card: null };
      return { seat: this.bidder, faceUp: true, card: this.trumpCard };
    };
    return {
      phase: this.phase,
      phaseAt: this.phaseAt,
      config: this.config,
      seats: this.seats.map((s, seat) => ({
        seat,
        team: teamOf(seat),
        name: s.name,
        isOwner: s.isOwner,
        isBot: s.isBot,
        connected: s.connected,
        handCount: this.hands[seat] ? this.hands[seat].length : 0,
        tricks: this.tricksWon[seat] || 0,
        sittingOut: seat === out,
      })),

      dealIndex: this.dealIndex,
      dealerSeat: this.dealerSeat,
      leadSeat: this.leadSeat,
      turnSeat: this.turnSeat,
      trickIndex: this.trickIndex,

      auction: {
        high: this.auction.high,
        highSeat: this.auction.highSeat,
        passed: this.auction.passed.slice(),
        calls: this.auction.calls.map((c) => ({ ...c })),
      },
      bidder: this.bidder,
      bid: this.bid,
      finalBid: this.finalBid,

      trumpMode: this.trumpMode,
      indicator: indicatorFor(),
      // null until the reveal. Before it, a client cannot tell a concealed
      // trump from a seventh card from the suit of anything at all.
      trump: this.revealed && !this.single ? this.trumpSuit : null,
      revealed: this.revealed,
      revealedBy: this.revealedBy,
      // Which trick the reveal happened in, so a screen can say "called this
      // trick" and a TV can mark the moment. Public once there was a reveal.
      revealTrick: this.revealTrick,
      caller: this.caller,

      declare: this.declare ? { stage: this.declare.stage, order: this.declare.order.slice(), at: this.declare.at } : null,
      level: this.level,
      multiplier: multiplierFor(this.level),
      doubledBy: this.doubledBy,
      redoubledBy: this.redoubledBy,
      single: this.single ? { ...this.single } : null,
      pair: this.pair ? { ...this.pair } : null,
      pairWindow: this.pairWindow ? { ...this.pairWindow } : null,

      plays: this.plays.map((p) => ({ ...p })),
      tricks: this.tricks.map((t) => ({ plays: t.plays.map((p) => ({ ...p })), winner: t.winner })),
      lastTrick: this.lastTrick ? {
        plays: this.lastTrick.plays.map((p) => ({ ...p })),
        winner: this.lastTrick.winner, card: this.lastTrick.card, points: this.lastTrick.points,
      } : null,
      sweeping: this.sweepAt !== null,
      points: this.pointsWon.slice(),

      gamePoints: this.gamePoints.slice(),
      leader: leadingTeam(this.gamePoints),
      outcome: this.outcome ? { ...this.outcome } : null,
      history: this.history.slice(),

      startBlocker: this.startBlocker(),
      log: this.log.slice(-LOG_CAP),
    };
  }

  /**
   * What one player may see that the others may not.
   *
   * THE TRUMP-DEPENDENT FIELDS, and who gets them:
   *
   *   hand order   sorted with trump first only for a seat that knows it —
   *                otherwise the order of a non-bidder's own cards would
   *                carry the suit.
   *   indicator    the face-down card, to the bidder alone, under a concealed
   *                trump, until the reveal. Under seventh card, to nobody.
   *   knownTrump   the suit, to the same seat on the same terms, and to
   *                everybody after the reveal (when it is public anyway).
   *   legal        computed WITHOUT the trump for everybody before the reveal
   *                — see legalPlays() — and with it only for the caller.
   *
   * Returns null for someone with no seat: a watcher is a peer with no seat,
   * and this is what that looks like in the code.
   */
  privateStateFor(playerId) {
    const seat = this.seatOf(playerId);
    if (seat === -1) return null;

    const hand = this.hands[seat] || [];
    const known = this._trumpKnownTo(seat);
    const playing = this.phase === PHASES.PLAY;
    const led = ledSuitOf(this.plays);
    const obligation = this.caller === seat ? this.trumpSuit : null;
    const sittingOut = !!this.single && this.single.out === seat;
    const isTurn = this._isTurn(seat);
    const choosingTrump = this.phase === PHASES.TRUMP_CHOICE && seat === this.bidder;

    const cards = sortHand(hand, known).map((code) => {
      if (choosingTrump) return { code, legal: true, reason: null };
      if (!playing || sittingOut) return { code, legal: false, reason: sittingOut ? 'you are sitting out this deal' : 'not playing right now' };
      return {
        code,
        legal: canPlay(hand, code, led, obligation),
        reason: illegalReason(hand, code, led, obligation),
      };
    });

    const mayCall = playing && isTurn && !this.single && canCall(hand, led, this.revealed);

    return {
      seat,
      team: teamOf(seat),
      isOwner: this.seats[seat].isOwner,
      isTurn,
      isDealer: seat === this.dealerSeat,
      isBidder: seat === this.bidder,
      sittingOut,
      hand: cards,
      legalCount: playing && !sittingOut ? legalPlays(hand, led, obligation).length : 0,
      indicator: seat === this.bidder && this.trumpMode === 'concealed' && !this.revealed && !this.single
        ? this.indicator : null,
      knownTrump: known,
      canCall: mayCall,
      // The caller's narrowed hand, said in words. Only ever true after the
      // reveal, about a suit that is face up on the table.
      mustTrump: obligation !== null && hand.some((c) => suitOf(c) === obligation)
        && !hand.some((c) => suitOf(c) === led),
      bidOptions: this.phase === PHASES.AUCTION && isTurn ? this._bidOptions() : null,
      trumpChoice: choosingTrump ? { seventh: this.config.seventh } : null,
      declareOptions: this.phase === PHASES.DECLARE && isTurn ? this._declareOptions() : null,
      canPair: this._pairBlocker(seat) === null,
    };
  }

  _isTurn(seat) {
    switch (this.phase) {
      case PHASES.AUCTION:
      case PHASES.DECLARE:
        return this.turnSeat === seat;
      case PHASES.TRUMP_CHOICE:
        return this.bidder === seat;
      case PHASES.PLAY:
        return this.sweepAt === null && this.turnSeat === seat;
      default:
        return false;
    }
  }

  /** Every bid on the pad, with a reason against each one that cannot be made.
   *  The pad offers only legal bids; the reasons are for the greyed numbers
   *  below the current high bid, so a tap on one is told why. */
  _bidOptions() {
    const high = this.auction.high;
    const out = [];
    for (let bid = MIN_BID; bid <= MAX_BID; bid++) {
      const legal = bidIsLegal(bid, high);
      out.push({ bid, legal, reason: legal ? null : illegalBidReason(bid, high) });
    }
    return out;
  }

  /** The calls this seat may make in the declarations window. Pass is always
   *  among them — the brief asks for a clear pass. */
  _declareOptions() {
    if (!this.declare) return null;
    return [this.declare.stage, 'pass'];
  }

  // ###########################################################################
  //
  //  PERSISTENCE
  //
  // ###########################################################################

  /**
   * The whole engine, hands and hidden trump and all, as plain JSON.
   *
   * THIS IS NOT A VIEW AND MUST NEVER BE SENT TO A PEER. It is the host's own
   * snapshot, for localStorage under `twentynine.`. It is the one object in
   * the app that contains the concealed trump in plain sight.
   */
  serialize() {
    return {
      v: 1,
      phase: this.phase,
      phaseAt: this.phaseAt,
      config: this.config,
      ownerId: this.ownerId,
      seats: this.seats.map((s) => ({ ...s })),
      dealIndex: this.dealIndex,
      dealerSeat: this.dealerSeat,
      gamePoints: this.gamePoints.slice(),
      history: this.history.slice(),
      outcome: this.outcome ? { ...this.outcome } : null,
      hands: this.hands.map((h) => h.slice()),
      stock: this.stock.slice(),
      auction: {
        high: this.auction.high, highSeat: this.auction.highSeat,
        passed: this.auction.passed.slice(), calls: this.auction.calls.map((c) => ({ ...c })),
      },
      bidder: this.bidder,
      bid: this.bid,
      finalBid: this.finalBid,
      trumpMode: this.trumpMode,
      indicator: this.indicator,
      trumpCard: this.trumpCard,
      revealed: this.revealed,
      revealedBy: this.revealedBy,
      revealTrick: this.revealTrick,
      caller: this.caller,
      declare: this.declare ? { ...this.declare, order: this.declare.order.slice() } : null,
      level: this.level,
      doubledBy: this.doubledBy,
      redoubledBy: this.redoubledBy,
      single: this.single ? { ...this.single } : null,
      singleLost: this.singleLost,
      pair: this.pair ? { ...this.pair } : null,
      pairWindow: this.pairWindow ? { ...this.pairWindow } : null,
      plays: this.plays.map((p) => ({ ...p })),
      tricks: this.tricks.map((t) => ({ plays: t.plays.map((p) => ({ ...p })), winner: t.winner })),
      trickIndex: this.trickIndex,
      leadSeat: this.leadSeat,
      turnSeat: this.turnSeat,
      lastTrick: this.lastTrick ? { ...this.lastTrick, plays: this.lastTrick.plays.map((p) => ({ ...p })) } : null,
      sweepAt: this.sweepAt,
      pointsWon: this.pointsWon.slice(),
      tricksWon: this.tricksWon.slice(),
      log: this.log.slice(),
    };
  }

  /**
   * Rebuild from a snapshot. reset() first, so a missing field lands on a sane
   * default; every array COPIED on the way in, so the engine never writes into
   * an object its caller still holds; every record re-sealed, because JSON
   * forgets what frozen means.
   */
  restore(snapshot) {
    if (!snapshot || typeof snapshot !== 'object') return { ok: false, error: 'no snapshot' };
    this.reset();
    const s = snapshot;
    const own = (v) => (Array.isArray(v) ? v.slice() : []);
    const int = (v, d = null) => (Number.isInteger(v) ? v : d);
    const obj = (v) => (v && typeof v === 'object' && !Array.isArray(v) ? { ...v } : null);
    const four = (v, fill) => { const a = own(v); while (a.length < SEATS) a.push(fill); return a.slice(0, SEATS); };

    this.phase = Object.values(PHASES).includes(s.phase) ? s.phase : PHASES.LOBBY;
    this.phaseAt = Number(s.phaseAt) || 0;
    this.config = normalizeConfig(s.config);
    this.ownerId = s.ownerId ?? null;
    this.seats = own(s.seats).slice(0, SEATS).map((seat) => ({ ...seat }));
    this.dealIndex = int(s.dealIndex, -1);
    this.dealerSeat = int(s.dealerSeat, 0);
    this.gamePoints = Array.isArray(s.gamePoints) && s.gamePoints.length === 2 ? s.gamePoints.map((n) => Number(n) || 0) : [0, 0];
    this.history = own(s.history).map(freezeRecord);
    this.outcome = obj(s.outcome);
    this.hands = four(s.hands, []).map((h) => own(h));
    this.stock = own(s.stock);
    const a = obj(s.auction) || {};
    this.auction = {
      high: int(a.high), highSeat: int(a.highSeat),
      passed: four(a.passed, false).map((p) => p === true),
      calls: own(a.calls).map((c) => ({ ...c })),
    };
    this.bidder = int(s.bidder);
    this.bid = int(s.bid);
    this.finalBid = int(s.finalBid);
    this.trumpMode = s.trumpMode === 'concealed' || s.trumpMode === 'seventh' ? s.trumpMode : null;
    this.indicator = typeof s.indicator === 'string' ? s.indicator : null;
    this.trumpCard = typeof s.trumpCard === 'string' ? s.trumpCard : null;
    this.revealed = s.revealed === true;
    this.revealedBy = int(s.revealedBy);
    this.revealTrick = int(s.revealTrick);
    this.caller = int(s.caller);
    this.declare = s.declare && typeof s.declare === 'object'
      ? { stage: s.declare.stage, order: own(s.declare.order), at: int(s.declare.at, 0) } : null;
    this.level = [0, 1, 2].includes(s.level) ? s.level : 0;
    this.doubledBy = int(s.doubledBy);
    this.redoubledBy = int(s.redoubledBy);
    this.single = obj(s.single);
    this.singleLost = s.singleLost === true;
    this.pair = obj(s.pair);
    this.pairWindow = obj(s.pairWindow);
    this.plays = own(s.plays).map((p) => ({ ...p }));
    this.tricks = own(s.tricks).map((t) => ({ plays: own(t && t.plays).map((p) => ({ ...p })), winner: t && t.winner }));
    this.trickIndex = int(s.trickIndex, 0);
    this.leadSeat = int(s.leadSeat, 0);
    this.turnSeat = int(s.turnSeat, 0);
    this.lastTrick = s.lastTrick && typeof s.lastTrick === 'object'
      ? { ...s.lastTrick, plays: own(s.lastTrick.plays).map((p) => ({ ...p })) } : null;
    this.sweepAt = s.sweepAt ?? null;
    this.pointsWon = Array.isArray(s.pointsWon) && s.pointsWon.length === 2 ? s.pointsWon.slice() : [0, 0];
    this.tricksWon = four(s.tricksWon, 0);
    this.log = own(s.log).map((l) => Object.freeze({ ...l }));

    // Everyone is assumed gone until they say otherwise; bots are always here.
    for (const seat of this.seats) if (!seat.isBot) seat.connected = false;
    return { ok: true, phase: this.phase };
  }

  // ###########################################################################
  //
  //  INTERNALS
  //
  // ###########################################################################

  _enter(phase, now) {
    this.phase = phase;
    this.phaseAt = now;
  }

  _name(seat) {
    return this.seats[seat] ? this.seats[seat].name : `seat ${seat}`;
  }

  /**
   * Append a line to the rolling log.
   *
   * These strings are the ONLY narration there is: js/main.js pushes them into
   * the aria-live region on every device, and onto the television. So they
   * are written to be read aloud, and — because the live region is the one
   * place everybody in the room hears the same thing — NOT ONE OF THEM may
   * name the trump before the reveal. The suite checks that by swapping the
   * hidden card and requiring the log to come out identical.
   *
   * Frozen, because publicState() slices the array but hands out the lines.
   */
  _say(text, kind = 'system', seat = null) {
    this.log.push(Object.freeze({ text, kind, seat, deal: this.dealIndex }));
    if (this.log.length > LOG_CAP) this.log.splice(0, this.log.length - LOG_CAP);
  }
}

// Re-exported so the UI and the bot can import the vocabulary they need from
// the engine they are already importing.
export { rankOf, teamOf, partnerOf };

// ============================================================================
// ui.js — all rendering, and nothing else.
//
//   render(root, app, intents)
//
// A PURE VIEW. Given the same `app` it builds the same DOM, every time. It
// never touches the network, never calls the engine, never reads a clock and
// keeps no state of its own. Everything it can do to the world it does by
// calling something on `intents`.
//
// ---------------------------------------------------------------------------
// THE CONTRACT — what `app` must hold (js/main.js satisfies it)
// ---------------------------------------------------------------------------
//   screen    'home' | 'join' | 'connecting' | 'error' | 'hostleft'
//             | 'replaced' | 'game' | 'watch'
//   me        { name }
//   code      the room code
//   pub       publicState() | null
//   priv      privateStateFor() | null
//   isHost    boolean — THIS DEVICE RUNS THE ENGINE
//   left      { role, code } | null — a table this device walked away from
//   error, selected, selectedBid, showPad, showLog, showLeave, announce,
//   busy, reconnecting, netWarning
//
// isHost IS NOT isOwner. Every owner-only control is gated on priv.isOwner;
// only the room code and the leave sheet's wording are keyed to isHost,
// because those are facts about the device rather than permissions.
//
// ---------------------------------------------------------------------------
// WHAT THIS FILE CANNOT LEAK
// ---------------------------------------------------------------------------
// It renders `pub` and `priv` and nothing else, and before the reveal neither
// carries the trump to anybody but the bidder who chose it. So the screen
// cannot name the trump early — not in text, not in an aria-label, not in the
// order of a hand — because the data is not in the building. The suite renders
// every frame of thousands of deals with the hidden card swapped and requires
// the DOM of every seat not entitled to it to come out identical.
//
// Legality is the same story from the other side: greyed cards come from
// priv.hand[].legal, computed by the engine's own canPlay(). The grey is a
// convenience; the host is the enforcement point.
// ============================================================================

import { el, clear, score as fmtScore, delta as fmtDelta, plural } from './util.js';
import {
  SEATS, suitOf, suitGlyph, suitName, suitSingular, rankLabel, isRedCard, isRedSuit, cardName, cardLabel, cardPoints,
} from './cards.js';
import {
  MIN_BID, MAX_BID, TOGGLES, TOGGLE_LABELS, PRESETS, presetMatching, MAX_NAME_LEN,
} from './rules.js';
import { MATCH_TARGET } from './scoring.js';
import { teamOf, partnerOf, nextSeat, ledSuitOf, winningPlay } from './trick.js';
import { PHASES } from './state.js';

// ###########################################################################
//
//  ENTRY
//
// ###########################################################################

export function render(root, app, intents) {
  // #announce, the footer and the rules <dialog> are SIBLINGS of #app in
  // index.html, because this wipes every child of root on every frame.
  clear(root);

  let node;
  switch (app.screen) {
    case 'home':       node = homeScreen(app, intents); break;
    case 'join':       node = joinScreen(app, intents); break;
    case 'connecting': node = connectingScreen(app, intents); break;
    case 'error':      node = errorScreen(app, intents); break;
    case 'hostleft':   node = hostLeftScreen(app, intents); break;
    case 'replaced':   node = replacedScreen(app, intents); break;
    case 'game':       node = gameScreen(app, intents); break;
    case 'watch':      node = watchScreen(app, intents); break;
    default:           node = homeScreen(app, intents);
  }
  root.appendChild(node);

  if (app.showPad && app.pub) root.appendChild(padOverlay(app, intents));
  if (app.showLog && app.pub) root.appendChild(logOverlay(app, intents));
  if (app.showLeave && app.pub && app.screen === 'game') root.appendChild(leaveOverlay(app, intents));
  if (app.reconnecting) root.appendChild(reconnectBanner());
  else if (app.netWarning) root.appendChild(netBanner(app, intents));
}

// ###########################################################################
//
//  SHARED CHROME
//
// ###########################################################################

function shell(...kids) { return el('main', { class: 'shell' }, ...kids); }
function playShell(...kids) { return el('main', { class: 'shell shell-play' }, ...kids); }

/** THE ONLY WAY INTO THE RULES: one button, the same name and focus token
 *  everywhere, on every screen — including the play screens, which is where a
 *  new player needs it. */
function helpBtn(intents, cls = 'help-btn') {
  return el('button', {
    class: cls, 'aria-label': 'How to play', title: 'How to play',
    'data-focus': 'help', onclick: () => intents.toggleRules(),
  }, '?');
}

function wordmark(intents) {
  return el('div', { class: 'wordmark' },
    el('span', { class: 'wordmark-dot' }),
    el('span', { class: 'wordmark-text' }, 'TWENTY-NINE'),
    helpBtn(intents),
  );
}

/** Carries the frame's announcement as an ATTRIBUTE; main.js copies it into
 *  the persistent #announce region outside #app. */
function liveRegion(text) {
  return el('div', { class: 'sr-only', 'data-announce': text || '' });
}

function errorNote(app) {
  if (!app.error) return null;
  return el('p', { class: 'error-note', role: 'alert' }, app.error);
}

function reconnectBanner() {
  return el('div', { class: 'reconnect-banner', role: 'status', 'aria-live': 'polite' },
    el('span', { class: 'spinner spinner-sm' }),
    el('span', {}, 'Lost the host — reconnecting…'));
}

function netBanner(app, intents) {
  return el('div', { class: 'net-banner', role: 'status', 'aria-live': 'polite' },
    el('span', {}, app.netWarning),
    el('button', { class: 'banner-close', 'aria-label': 'Dismiss', onclick: intents.dismissNetWarning }, '✕'));
}

function backRow(label, onclick) {
  return el('div', { class: 'btn-row' }, el('button', { class: 'btn btn-secondary', onclick }, label));
}

function leaveBtn(intents, label) {
  return el('button', { class: 'btn btn-ghost btn-wide', onclick: () => intents.toggleLeave() }, label);
}

function nameOf(pub, seat) {
  const s = pub.seats[seat];
  return s ? s.name : '';
}

/** "Asha & Cleo" — a team is two names, partners opposite. */
function teamNames(pub, team) {
  return [team, team + 2].map((s) => nameOf(pub, s)).filter(Boolean).join(' & ');
}

/** The seat this device looks from: its own, or seat 0 for a device with no
 *  seat — somebody has to be at the bottom of the picture. */
function mySeat(app) {
  return app.priv ? app.priv.seat : 0;
}

/** "us" or "them", relative to whoever is holding the phone — the class that
 *  sets --team for every team-coloured thing in the stylesheet. */
function side(app, team) {
  return app.priv && teamOf(app.priv.seat) === team ? 'us' : 'them';
}

// ###########################################################################
//
//  HOME, JOIN, AND THE DEAD ENDS
//
// ###########################################################################

function nameField(app, intents) {
  return el('input', {
    class: 'field', type: 'text', maxlength: String(MAX_NAME_LEN),
    placeholder: 'Your name', value: app.me.name || '',
    'aria-label': 'Your name', 'data-focus': 'name',
    oninput: (e) => intents.setName(e.target.value),
  });
}

/** The way back to a table this device walked away from. Above the name
 *  field, because somebody who left a game and came back wants that game. */
function leftCard(app, intents) {
  const table = app.left;
  if (!table) return null;
  const hosting = table.role === 'host';
  return el('div', { class: 'panel' },
    el('h2', {}, hosting ? 'Your game is waiting' : 'You left a game'),
    el('p', {}, hosting
      ? `Room ${table.code} is paused on this device, exactly where you left it. Resume it and the others rejoin with the same code.`
      : `Your seat in room ${table.code} is kept for this device while the game is on. Rejoin and it is yours again.`),
    el('div', { class: 'btn-row' },
      el('button', { class: 'btn btn-primary', onclick: () => intents.resumeTable() }, hosting ? 'RESUME GAME' : `REJOIN ${table.code}`),
      el('button', { class: 'btn btn-ghost', onclick: () => intents.forgetTable() }, hosting ? 'DISCARD' : 'FORGET IT')),
    el('p', { class: 'hint' }, hosting
      ? 'Discarding it ends the game for everyone. So does hosting or joining another one.'
      : 'JOIN A GAME with the same code gets you back there too.'));
}

function homeScreen(app, intents) {
  const named = !!(app.me.name || '').trim();
  return shell(
    wordmark(intents),
    el('p', { class: 'tagline' }, 'Bid on four cards. Hide a trump. Count the points, not the tricks.'),
    leftCard(app, intents),
    el('div', { class: 'panel' },
      nameField(app, intents),
      el('div', { class: 'btn-row' },
        el('button', { class: 'btn btn-primary', disabled: !named, onclick: () => intents.host() }, 'HOST A GAME'),
        el('button', { class: 'btn btn-secondary', disabled: !named, onclick: () => intents.goJoin() }, 'JOIN A GAME')),
      !named && el('p', { class: 'hint' }, 'Put a name in first — the table needs something to call you.')),
    errorNote(app),
    liveRegion(app.announce),
  );
}

function joinScreen(app, intents) {
  const four = (app.code || '').length === 4;
  return shell(
    wordmark(intents),
    el('div', { class: 'panel' },
      el('h2', {}, 'Join a game'),
      el('input', {
        class: 'field field-code', type: 'text', inputmode: 'latin',
        autocapitalize: 'characters', autocomplete: 'off', spellcheck: 'false',
        maxlength: '4', placeholder: 'CODE', value: app.code || '',
        'aria-label': 'Room code', 'data-focus': 'code',
        oninput: (e) => intents.setCode(e.target.value),
      }),
      el('p', { class: 'hint' }, 'Four characters, from whoever is hosting.'),
      el('div', { class: 'btn-row' },
        el('button', { class: 'btn btn-primary', disabled: !four, onclick: () => intents.join(app.code) }, 'JOIN'),
        el('button', { class: 'btn btn-secondary', onclick: intents.goHome }, 'BACK')),
      // Below the row, not in it: watching is a different kind of thing from
      // joining, and beside JOIN it would be a coin toss at the wrong moment.
      el('button', { class: 'btn btn-ghost btn-wide', disabled: !four, onclick: () => intents.watch(app.code) }, 'WATCH ON A BIG SCREEN')),
    errorNote(app),
    liveRegion(app.announce),
  );
}

function connectingScreen(app, intents) {
  return shell(
    wordmark(intents),
    el('div', { class: 'panel panel-centre' },
      el('span', { class: 'spinner' }),
      el('h2', {}, 'Connecting…'),
      el('p', { class: 'hint' }, `Looking for room ${app.code}. This can take a few seconds.`),
      backRow('✕ CANCEL', intents.cancelJoin)),
    liveRegion(app.announce),
  );
}

function errorScreen(app, intents) {
  return shell(
    wordmark(intents),
    el('div', { class: 'panel' },
      el('h2', {}, 'That did not work'),
      el('p', {}, app.error || 'Something went wrong.'),
      backRow('‹ BACK HOME', intents.goHome)),
    liveRegion(app.announce),
  );
}

function hostLeftScreen(app, intents) {
  return shell(
    wordmark(intents),
    el('div', { class: 'panel' },
      el('h2', {}, 'Host left'),
      el('p', {}, 'The game runs on the host’s device, so it stops when they go. If they come back to it, rejoin and you pick up where it stopped.'),
      el('div', { class: 'btn-row' },
        el('button', { class: 'btn btn-primary', onclick: () => intents.rejoin() }, app.code ? `REJOIN ${app.code}` : 'REJOIN'),
        el('button', { class: 'btn btn-secondary', onclick: intents.goHome }, '‹ BACK HOME'))),
    liveRegion(app.announce),
  );
}

function replacedScreen(app, intents) {
  return shell(
    wordmark(intents),
    el('div', { class: 'panel' },
      el('h2', {}, 'Open in another tab'),
      el('p', {}, 'This table is open in a newer tab on this device, and your seat went with it. You can close this one.'),
      backRow('‹ BACK HOME', intents.goHome)),
    liveRegion(app.announce),
  );
}

// ###########################################################################
//
//  CARDS
//
// ###########################################################################

/** One card face: ivory on dark felt, judgement's treatment. `asTrump` marks a
 *  card that PLAYED as a trump — a trump-suit card played before the reveal
 *  did not, and must not look as though it did. */
function cardFace(code, { cls = '', asTrump = false } = {}) {
  return el('span', { class: `card${isRedCard(code) ? ' red' : ''}${asTrump ? ' as-trump' : ''}${cls ? ` ${cls}` : ''}` },
    el('span', { class: 'card-rank' }, rankLabel(code)),
    el('span', { class: 'card-suit' }, suitGlyph(suitOf(code))));
}

/** A face-down card. The indicator before the reveal, everywhere. Its only
 *  text is its label, and its label says nothing about any suit. */
function cardBack(cls = '', label = 'trump hidden') {
  return el('span', { class: `card card-back${cls ? ` ${cls}` : ''}`, role: 'img', 'aria-label': label });
}

// ###########################################################################
//
//  THE TV — a read-only board, the table seen from above
//
// ###########################################################################
//
// A spectator is a peer with no seat: it reads app.pub and NEVER app.priv,
// which is null for it in every phase. Nothing is pressable but the two
// discreet controls in the corner. Sized in container units so 1366x768 and
// 1920x1080 are the same drawing — the numbers came out of _tvsketch.html,
// measured for overflow at both sizes with four sixteen-character names.
//
// THE TV MUST NEVER SHOW THE TRUMP BEFORE THE REVEAL. It cannot: pub.trump is
// null and pub.indicator.card is null until the call, and this screen draws
// what it is given.

function watchScreen(app, intents) {
  const { pub } = app;
  if (!pub) {
    return el('main', { class: 'tv' },
      el('div', { class: 'tv-wait' }, el('span', { class: 'spinner' }), el('p', {}, `Joining room ${app.code || ''}…`)),
      tvChrome(intents), liveRegion(app.announce));
  }
  if (pub.phase === PHASES.LOBBY) {
    return el('main', { class: 'tv' },
      el('div', { class: 'tv-lobby' },
        el('p', { class: 'tv-lede' }, 'Join this game with the code'),
        el('span', { class: 'tv-bigcode' }, app.code || ''),
        el('div', { class: 'tv-teams' }, [0, 1].map((team) => el('div', { class: `tv-team ${team === 0 ? 'us' : 'them'}` },
          el('span', { class: 'tv-k' }, `Team ${team + 1}`),
          el('span', { class: 'tv-tname' }, teamNames(pub, team) || 'waiting for players')))),
        el('p', { class: 'tv-lede' }, `${plural(pub.seats.length, 'player')} in — empty seats are filled by bots. Partners sit opposite.`)),
      tvChrome(intents), liveRegion(app.announce));
  }
  return el('main', { class: 'tv' },
    tvBar(app),
    el('div', { class: 'tv-main' },
      tvFelt(pub),
      el('div', { class: 'tv-side' }, tvContract(pub), tvScores(pub))),
    tvChrome(intents),
    liveRegion(app.announce));
}

/** The help button and the exit, as one node pinned to the corner. */
function tvChrome(intents) {
  return el('div', { class: 'tv-chrome' },
    helpBtn(intents, 'tv-help'),
    el('button', { class: 'tv-exit', onclick: intents.goHome, 'aria-label': 'Stop watching' }, '✕'));
}

function tvBar(app) {
  const pub = app.pub;
  return el('div', { class: 'tv-bar' },
    el('span', {}, el('b', {}, `Deal ${pub.dealIndex + 1}`), ` · ${nameOf(pub, pub.dealerSeat)} deals`),
    el('span', { class: 'tv-trump' }, 'Trump ', trumpChip(pub, 'tv-trumpcard')),
    el('span', { class: 'tv-code' }, app.code || ''));
}

/** The trump as everybody may know it: a card back, a suit, or none. */
function trumpChip(pub, cardCls) {
  if (pub.single) return el('span', { class: 'trump-chip', 'aria-label': 'no trump: single hand' }, el('b', {}, 'none · single hand'));
  if (pub.revealed && pub.trump) {
    return el('span', { class: `trump-chip${isRedSuit(pub.trump) ? ' red' : ''}`, 'aria-label': `${suitName(pub.trump)} are trumps` },
      el('span', { class: 'trump-glyph' }, suitGlyph(pub.trump)), el('b', {}, suitName(pub.trump)));
  }
  if (pub.indicator) return el('span', { class: 'trump-chip', 'aria-label': 'trump hidden' }, cardBack(cardCls), el('b', {}, 'hidden'));
  return el('span', { class: 'trump-chip', 'aria-label': 'trump not chosen yet' }, el('b', {}, 'not chosen'));
}

function tvFelt(pub) {
  const at = seatPositions(0);
  const plays = pub.sweeping && pub.lastTrick ? pub.lastTrick.plays : pub.plays;
  const best = winningPlay(plays);
  const order = new Map(plays.map((p, i) => [p.seat, { ...p, i }]));
  const plate = (slot) => {
    const seat = at[slot];
    const s = pub.seats[seat];
    const turn = isWaitingOn(pub, seat);
    return el('div', { class: `tv-seat ${slot} ${teamOf(seat) === 0 ? 'us' : 'them'}${turn ? ' turn' : ''}${s && !s.connected && !s.isBot ? ' gone' : ''}` },
      el('span', { class: 'tv-nm' }, s ? s.name : '—'),
      el('span', { class: 'tv-meta' }, s ? seatRole(pub, seat) : ''),
      seat === pub.bidder && indicatorMark(pub, 'tv-ind'));
  };
  const slotCard = (slot) => {
    const p = order.get(at[slot]);
    return el('div', { class: `tv-slot ${slot}` }, p
      ? cardFace(p.code, { cls: best && best.seat === p.seat ? `win ${teamOf(p.seat) === 0 ? 'us' : 'them'}` : '', asTrump: p.trump })
      : null);
  };
  return el('div', { class: 'tv-felt' },
    plate('top'), plate('left'), plate('right'), plate('bottom'),
    el('div', { class: 'tv-trick' }, slotCard('top'), slotCard('left'), slotCard('right'), slotCard('bottom')));
}

function tvContract(pub) {
  const c = contract(pub);
  if (!c) {
    return el('div', { class: 'tv-box' },
      el('span', { class: 'tv-k' }, phaseLede(pub)),
      el('span', { class: 'tv-big' }, pub.auction.high === null ? 'No bid yet' : `${pub.auction.high}`),
      pub.auction.highSeat !== null && el('span', { class: 'tv-lede' }, `held by ${nameOf(pub, pub.auction.highSeat)}`));
  }
  return el('div', { class: `tv-box ${c.team === 0 ? 'us' : 'them'}` },
    el('span', { class: 'tv-k' }, `Contract · ${teamNames(pub, c.team)}`),
    el('span', { class: 'tv-big' }, c.single ? 'Single hand' : [c.moved && el('s', {}, String(c.bid)), ` ${c.finalBid}`]),
    contractTags(pub, 'tv-tags'),
    el('div', { class: 'tv-drama' }, el('span', {}, el('b', {}, String(c.made)), c.single ? ' tricks taken' : ' so far'),
      el('span', {}, el('b', {}, String(c.toGo)), c.single ? ' to take' : ' to go')),
    meter(c));
}

function tvScores(pub) {
  return el('div', { class: 'tv-box' },
    el('span', { class: 'tv-k' }, `Game points · first to +${MATCH_TARGET}`),
    [0, 1].map((team) => scoreTrack(pub, team, team === 0 ? 'us' : 'them', 'tv-track')),
    el('div', { class: 'tv-ends' }, el('span', { class: 'lose' }, `−${MATCH_TARGET} loses`), el('span', {}, '0'), el('span', { class: 'win' }, `+${MATCH_TARGET} wins`)));
}

// ###########################################################################
//
//  THE GAME — one dispatch on phase
//
// ###########################################################################

function gameScreen(app, intents) {
  const { pub } = app;
  if (!pub) return connectingScreen(app, intents);
  switch (pub.phase) {
    case PHASES.LOBBY:        return lobbyScreen(app, intents);
    case PHASES.FIRST_FOUR:   return dealScreen(app, intents, 'first');
    case PHASES.AUCTION:      return auctionScreen(app, intents);
    case PHASES.TRUMP_CHOICE: return trumpScreen(app, intents);
    case PHASES.LAST_FOUR:    return dealScreen(app, intents, 'last');
    case PHASES.DECLARE:      return declareScreen(app, intents);
    case PHASES.PLAY:         return playScreen(app, intents);
    case PHASES.DEAL_OVER:    return dealOverScreen(app, intents);
    case PHASES.MATCH_OVER:   return matchOverScreen(app, intents);
    default:                  return lobbyScreen(app, intents);
  }
}

// ###########################################################################
//
//  LOBBY
//
// ###########################################################################

function lobbyScreen(app, intents) {
  const { pub, priv } = app;
  const owner = !!(priv && priv.isOwner);
  const n = pub.seats.length;
  const blocker = pub.startBlocker;
  const empty = SEATS - n;

  return shell(
    wordmark(intents),
    roomCard(app, intents),
    el('div', { class: 'panel' },
      el('h2', {}, `Table · ${plural(n, 'player')}`),
      el('p', { class: 'hint' }, 'Partners sit opposite: seats 1 and 3 against 2 and 4. The seat decides it.'),
      el('ul', { class: 'seat-list' }, Array.from({ length: SEATS }, (_, seat) => seatRow(app, intents, seat, owner))),
      owner && n < SEATS && el('div', { class: 'btn-row' },
        el('button', { class: 'btn btn-ghost', onclick: () => intents.addBot() }, '+ ADD A BOT'))),
    configCard(app, intents, owner),
    el('div', { class: 'panel' },
      owner
        ? el('button', { class: 'btn btn-primary btn-wide', disabled: !!blocker || app.busy, onclick: () => intents.startMatch() },
          blocker ? 'NOT READY' : (empty ? `START — ${plural(empty, 'bot')} fill in` : 'START THE MATCH'))
        : el('p', { class: 'hint' }, 'Waiting for the owner to start.'),
      blocker && owner && el('p', { class: 'hint' }, blocker),
      leaveBtn(intents, 'LEAVE THE TABLE')),
    errorNote(app),
    liveRegion(app.announce),
  );
}

function roomCard(app, intents) {
  if (!app.isHost || !app.code) return null;
  return el('div', { class: 'panel panel-code' },
    el('p', { class: 'code-lede' }, 'Others join with'),
    el('p', { class: 'code' }, app.code),
    el('button', { class: 'btn btn-ghost', onclick: () => intents.copyCode() }, 'COPY'));
}

function seatRow(app, intents, seat, owner) {
  const { pub } = app;
  const s = pub.seats[seat];
  const team = teamOf(seat);
  const cls = `seat-row ${side(app, team)}`;
  if (!s) {
    return el('li', { class: `${cls} open` },
      el('span', { class: 'seat-no' }, String(seat + 1)),
      el('span', { class: 'seat-row-name' }, 'Empty — a bot will sit here'),
      el('span', { class: 'tag' }, `TEAM ${team + 1}`));
  }
  const me = app.priv && app.priv.seat === seat;
  return el('li', { class: `${cls}${me ? ' me' : ''}${s.connected ? '' : ' gone'}` },
    el('span', { class: 'seat-no' }, String(seat + 1)),
    el('span', { class: 'seat-row-name' }, s.name),
    el('span', { class: 'tag' }, `TEAM ${team + 1}`),
    s.isOwner && el('span', { class: 'tag tag-owner' }, 'OWNER'),
    s.isBot && el('span', { class: 'tag tag-bot' }, 'BOT'),
    !s.connected && !s.isBot && el('span', { class: 'tag tag-gone' }, 'AWAY'),
    owner && !s.isOwner && el('button', { class: 'seat-kick', 'aria-label': `Remove ${s.name}`, onclick: () => intents.removeSeat(seat) }, '✕'));
}

/** Presets plus toggles: the family's pattern. A preset sets all four, and the
 *  four stay exposed underneath. */
function configCard(app, intents, owner) {
  const cfg = app.pub.config;
  const preset = presetMatching(cfg);
  return el('div', { class: 'panel' },
    el('h2', {}, 'The game'),
    el('div', { class: 'preset-row' }, PRESETS.map((p) => el('button', {
      class: `preset${preset === p.id ? ' on' : ''}`, disabled: !owner,
      'aria-pressed': preset === p.id ? 'true' : 'false', onclick: () => intents.applyPreset(p.id),
    }, p.label))),
    el('p', { class: 'hint' }, preset ? PRESETS.find((p) => p.id === preset).blurb : 'Custom — your own mix of the options.'),
    TOGGLES.map((key) => el('div', { class: 'axis' },
      el('button', {
        class: `toggle${cfg[key] ? ' on' : ''}`, disabled: !owner, role: 'switch',
        'aria-checked': cfg[key] ? 'true' : 'false', 'aria-label': TOGGLE_LABELS[key].label,
        onclick: () => intents.setConfig({ [key]: !cfg[key] }),
      }, el('span', { class: 'toggle-name' }, TOGGLE_LABELS[key].label), el('span', { class: 'toggle-state' }, cfg[key] ? 'ON' : 'OFF')),
      el('p', { class: 'hint' }, TOGGLE_LABELS[key].blurb))));
}

// ###########################################################################
//
//  THE TABLE STRIP — teams, not individuals
//
//  "Bid 20 · 14 so far · 6 to go" is the whole drama, so the contract and the
//  meter are the strip. Us in the accent, them in ivory: one accent only, and
//  partners share a colour everywhere they appear.
//
// ###########################################################################

/** The contract as everybody may know it, or null before there is one. */
function contract(pub) {
  if (pub.single) {
    const tricks = pub.tricks.filter((t) => t.winner === pub.single.seat).length
      + (pub.sweeping && pub.lastTrick && pub.lastTrick.winner === pub.single.seat ? 1 : 0);
    const played = pub.tricks.length + (pub.sweeping ? 1 : 0);
    return { single: true, team: teamOf(pub.single.seat), made: tricks, toGo: 8 - played, target: 8, progress: tricks };
  }
  if (pub.bidder === null || pub.bid === null) return null;
  const team = teamOf(pub.bidder);
  const made = pub.points[team];
  return {
    single: false, team, bid: pub.bid, finalBid: pub.finalBid,
    moved: pub.finalBid !== pub.bid, made, toGo: Math.max(0, pub.finalBid - made),
    target: pub.finalBid, progress: made,
  };
}

function contractTags(pub, cls = 'tags') {
  const tags = [];
  if (pub.pair) tags.push(el('span', { class: 'tag tag-hot' }, `pair ${pub.pair.to < pub.pair.from ? '−' : '+'}${Math.abs(pub.pair.to - pub.pair.from)} · ${nameOf(pub, pub.pair.seat)}`));
  if (pub.level === 1) tags.push(el('span', { class: 'tag tag-warn' }, 'doubled ×2'));
  if (pub.level === 2) tags.push(el('span', { class: 'tag tag-warn' }, 'redoubled ×4'));
  if (pub.trumpMode === 'seventh' && !pub.single) tags.push(el('span', { class: 'tag' }, 'seventh card'));
  return tags.length ? el('div', { class: cls }, tags) : null;
}

/** Points against the target, with a tick at the target. Drawn only for the
 *  side that has a target: the bidders, or a single-hand declarer. */
function meter(c) {
  const pct = (n) => `${Math.max(0, Math.min(100, (n / 28) * 100)).toFixed(1)}%`;
  const scale = c.single ? 8 : 28;
  const at = (n) => `${Math.max(0, Math.min(100, (n / scale) * 100)).toFixed(1)}%`;
  return el('div', { class: 'meter', role: 'img', 'aria-label': c.single ? `${c.made} of 8 tricks taken` : `${c.made} of ${c.target} points` },
    el('i', { class: 'meter-fill', style: `width: ${c.single ? at(c.made) : pct(c.made)}` }),
    !c.single && el('i', { class: 'meter-tick', style: `left: ${pct(c.target)}` }));
}

function playStrip(app, intents) {
  const { pub } = app;
  const c = contract(pub);
  const auctioning = pub.phase === PHASES.AUCTION;

  return el('div', { class: 'play-strip' },
    el('div', { class: 'strip-head' },
      el('span', {}, `Deal ${pub.dealIndex + 1} · ${nameOf(pub, pub.dealerSeat)} deals`),
      trumpChip(pub, 'card-mini'),
      helpBtn(intents, 'help-btn help-btn-sm'),
      el('button', { class: 'strip-btn strip-pad-btn', 'aria-label': 'Show the score pad', onclick: () => intents.togglePad() }, 'PAD'),
      el('button', { class: 'strip-btn', 'aria-label': 'Show what happened', onclick: () => intents.toggleLog() }, 'LOG'),
      el('button', { class: 'strip-btn strip-exit', 'aria-label': 'Leave the game', title: 'Leave the game', onclick: () => intents.toggleLeave() }, '✕')),
    c
      ? el('div', { class: `contract ${side(app, c.team)}` },
        el('div', { class: 'contract-main' },
          el('span', { class: 'contract-bid' }, c.single ? 'Single hand' : [c.moved && el('s', {}, String(c.bid)), c.moved ? ` ${c.finalBid}` : `Bid ${c.finalBid}`]),
          el('span', { class: 'contract-by' }, c.single
            ? `${nameOf(pub, pub.single.seat)} alone · ${nameOf(pub, pub.single.out)} sits out`
            : `${nameOf(pub, pub.bidder)} · ${side(app, c.team)}`)),
        contractTags(pub))
      : el('div', { class: 'contract' },
        el('div', { class: 'contract-main' },
          el('span', { class: 'contract-bid' }, auctioning && pub.auction.high !== null ? `High ${pub.auction.high}` : 'No bid yet'),
          el('span', { class: 'contract-by' }, auctioning && pub.auction.highSeat !== null ? nameOf(pub, pub.auction.highSeat) : 'the auction is open'))),
    c && (pub.phase === PHASES.PLAY || pub.phase === PHASES.DECLARE) && el('div', { class: `meter-wrap ${side(app, c.team)}` },
      el('div', { class: 'meter-line' },
        el('span', {}, el('b', {}, String(c.made)), c.single ? ' tricks taken' : ' so far'),
        el('span', {}, el('b', {}, String(c.toGo)), c.single ? ' to take' : (c.toGo === 0 ? ' — made' : ' to go'))),
      meter(c)),
    el('div', { class: 'teams' }, [teamOf(mySeat(app)), 1 - teamOf(mySeat(app))].map((team) => teamCard(app, team, c))));
}

function teamCard(app, team, c) {
  const { pub } = app;
  const gp = pub.gamePoints[team];
  const s = side(app, team);
  const waiting = [team, team + 2].some((seat) => isWaitingOn(pub, seat));
  return el('div', {
    class: `team ${s}`,
    'aria-label': `${s === 'us' ? 'Us' : 'Them'}: ${teamNames(pub, team)}, ${gp} game points, ${pub.points[team]} card points this deal`,
  },
    el('div', { class: 'team-top' },
      el('span', { class: 'team-label' }, `${s === 'us' ? 'Us' : 'Them'}${c && c.team === team ? ' · bidding' : ''}`),
      el('span', { class: `team-gp${gp < 0 ? ' neg' : ''}` }, fmtScore(gp))),
    el('div', { class: 'team-names' }, teamNames(pub, team), waiting ? ' ▸' : ''),
    el('div', { class: 'team-pts' }, `${pub.points[team]} card pts · ${plural(pub.seats.filter((x) => teamOf(x.seat) === team).reduce((n, x) => n + x.tricks, 0), 'trick')}`));
}

/** Whether the table is waiting on this seat. */
function isWaitingOn(pub, seat) {
  switch (pub.phase) {
    case PHASES.AUCTION: case PHASES.DECLARE: return pub.turnSeat === seat;
    case PHASES.TRUMP_CHOICE: return pub.bidder === seat;
    case PHASES.PLAY: return !pub.sweeping && pub.turnSeat === seat;
    default: return false;
  }
}

function phaseLede(pub) {
  switch (pub.phase) {
    case PHASES.AUCTION: return `${nameOf(pub, pub.turnSeat)} to bid`;
    case PHASES.TRUMP_CHOICE: return `${nameOf(pub, pub.bidder)} is choosing trump`;
    case PHASES.FIRST_FOUR: case PHASES.LAST_FOUR: return 'dealing';
    case PHASES.DEAL_OVER: return 'deal over';
    case PHASES.MATCH_OVER: return 'match over';
    default: return '';
  }
}

// ###########################################################################
//
//  THE TABLE — four plates, partner opposite
//
//  Seats are numbered clockwise and the viewer is at the bottom, so the
//  screen reads bottom S, left S+1, top S+2, right S+3 — courtpiece's layout.
//  Turn order SUBTRACTS one (js/trick.js), so play sweeps bottom -> right ->
//  top -> left: anticlockwise on screen, with nothing reversed to make it so.
//
// ###########################################################################

export const SCREEN_SLOTS = Object.freeze(['bottom', 'left', 'top', 'right']);

/** Which seat sits at each screen position, viewed from `seat`. */
export function seatPositions(seat) {
  const out = {};
  for (let i = 0; i < SEATS; i++) out[SCREEN_SLOTS[i]] = (seat + i) % SEATS;
  return out;
}

function seatRole(pub, seat) {
  const parts = [];
  const s = pub.seats[seat];
  if (pub.single && pub.single.out === seat) parts.push('sits out');
  else if (pub.single && pub.single.seat === seat) parts.push('single hand');
  else if (seat === pub.bidder) parts.push('bidder');
  if (seat === pub.dealerSeat) parts.push('dealer');
  if (s.isBot) parts.push('bot');
  else if (!s.connected) parts.push('away');
  parts.push(plural(s.handCount, 'card'));
  return parts.join(' · ');
}

/** The indicator beside the bidder's plate: a card back before the reveal,
 *  the card face up while it is back in their hand, nothing once played. */
function indicatorMark(pub, cls) {
  if (!pub.indicator) return null;
  if (!pub.indicator.faceUp) return el('span', { class: cls }, cardBack('card-mini'), el('span', { class: 'ind-label' }, 'trump'));
  const code = pub.indicator.card;
  const played = pub.plays.some((p) => p.code === code) || pub.tricks.some((t) => t.plays.some((p) => p.code === code));
  if (played) return null;
  return el('span', { class: cls }, cardFace(code, { cls: 'card-mini' }), el('span', { class: 'ind-label' }, 'in hand'));
}

function tableArea(app) {
  const { pub } = app;
  const me = mySeat(app);
  const at = seatPositions(me);
  const plays = pub.sweeping && pub.lastTrick ? pub.lastTrick.plays : pub.plays;
  const best = winningPlay(plays);
  const byseat = new Map(plays.map((p, i) => [p.seat, { ...p, i }]));

  const plate = (slot) => {
    const seat = at[slot];
    const s = pub.seats[seat];
    if (!s) return el('div', { class: `plate ${slot}` }, el('span', { class: 'plate-name' }, '—'));
    const turn = isWaitingOn(pub, seat);
    const you = app.priv && app.priv.seat === seat;
    return el('div', {
      class: `plate ${slot} ${side(app, teamOf(seat))}${turn ? ' turn' : ''}${!s.connected && !s.isBot ? ' gone' : ''}`
        + `${pub.single && pub.single.out === seat ? ' out' : ''}`,
      'aria-label': [you ? 'You' : s.name, seat === partnerOf(me) && app.priv ? 'your partner' : (teamOf(seat) === teamOf(me) && app.priv ? 'your team' : 'opponent'),
        seatRole(pub, seat), turn ? 'to play' : null].filter(Boolean).join(', '),
    },
    el('span', { class: 'plate-name' }, you ? 'You' : s.name),
    el('span', { class: 'plate-meta' }, seatRole(pub, seat)),
    seat === pub.bidder && indicatorMark(pub, 'ind'));
  };

  const slot = (pos) => {
    const p = byseat.get(at[pos]);
    if (!p) return el('div', { class: `slot ${pos}` });
    const win = best && best.seat === p.seat;
    return el('div', { class: `slot ${pos}` },
      el('span', {
        class: `played ${side(app, teamOf(p.seat))}${win ? ' winning' : ''}`,
        'aria-label': `${nameOf(pub, p.seat)} played ${cardLabel(p.code)}${p.trump ? ', as a trump' : ''}${win ? (pub.sweeping ? ', takes the trick' : ', winning') : ''}`,
      },
      cardFace(p.code, { asTrump: p.trump }),
      el('span', { class: 'pip', 'aria-hidden': 'true' }, String(p.i + 1))));
  };

  return el('div', { class: 'table' },
    plate('top'), plate('left'), plate('right'), plate('bottom'),
    el('div', { class: 'trick-grid' }, slot('top'), slot('left'), slot('right'), slot('bottom')));
}

// ###########################################################################
//
//  THE HAND
//
// ###########################################################################

/** The hand for LOOKING AT — the deal, the auction, the declarations. Fanned,
 *  because nothing in it is a tap target. */
function lookHand(app, hint) {
  const { priv } = app;
  if (!priv) return null;
  return el('div', { class: 'hand-dock' },
    el('p', { class: 'turn-hint' }, hint),
    bidderPeek(app),
    el('div', { class: 'hand fan' }, priv.hand.map((c) => el('span', { class: 'card-btn static', 'aria-label': cardLabel(c.code) }, cardFace(c.code)))));
}

/** The bidder's private look at their own face-down card — or, under seventh
 *  card, the plain statement that there is nothing to look at. */
function bidderPeek(app) {
  const { pub, priv } = app;
  if (!priv || !priv.isBidder || pub.revealed || pub.single) return null;
  if (priv.indicator) {
    return el('div', { class: 'peek' },
      cardFace(priv.indicator, { cls: 'card-mini' }),
      el('span', {}, el('b', {}, 'Only you can see this. '),
        `Your trump card, face down: ${suitName(priv.knownTrump)} are trumps. Nobody else knows yet, not even your partner.`));
  }
  if (pub.trumpMode === 'seventh') {
    return el('div', { class: 'peek' }, cardBack('card-mini', 'your seventh card, face down'),
      el('span', {}, el('b', {}, 'Seventh card. '), 'Your seventh card is face down — unseen, even by you.'));
  }
  return null;
}

function playHand(app, intents) {
  const { pub, priv } = app;
  if (!priv) return null;
  const led = ledSuitOf(pub.plays);
  const sel = app.selected;

  const cards = priv.hand.map((c) => {
    const illegal = !c.legal && !priv.sittingOut;
    const isSel = sel === c.code;
    return el('button', {
      class: `card-btn${isSel ? ' sel' : ''}${illegal ? ' illegal' : ''}`,
      'aria-disabled': illegal || priv.sittingOut ? 'true' : 'false',
      'aria-pressed': isSel ? 'true' : 'false',
      'aria-label': illegal ? `${cardLabel(c.code)}, unavailable: ${c.reason}` : cardLabel(c.code),
      onclick: () => (illegal || priv.sittingOut ? intents.explain(c.reason) : intents.selectCard(c.code)),
    }, cardFace(c.code));
  });

  return el('div', { class: 'hand-dock' },
    el('p', { class: `turn-hint${priv.isTurn ? ' mine' : ''}` }, turnHint(app, led)),
    bidderPeek(app),
    priv.canCall && callChoice(app, intents, led),
    priv.mustTrump && el('p', { class: 'why' }, `You called for trump, so you must play a ${suitSingular(pub.trump)} — for this card, on this trick.`),
    priv.canPair && el('button', { class: 'btn btn-primary btn-wide pair-btn', onclick: () => intents.declarePair() },
      `DECLARE THE PAIR — K and Q of ${suitName(pub.trump)}`),
    el('div', { class: `hand${priv.sittingOut ? ' out' : ''}` }, cards),
    !priv.sittingOut && actionRow(app, intents));
}

function turnHint(app, led) {
  const { pub, priv } = app;
  if (priv.sittingOut) return 'You sit out this deal — your partner plays alone';
  if (pub.sweeping && pub.lastTrick) return `${nameOf(pub, pub.lastTrick.winner)} takes it${pub.lastTrick.points ? ` — ${plural(pub.lastTrick.points, 'point')}` : ''}`;
  if (!priv.isTurn) return `Waiting for ${nameOf(pub, pub.turnSeat)}`;
  if (!led) return 'Your turn · you lead';
  if (priv.canCall) return `Your turn · you have no ${suitName(led)}`;
  if (priv.legalCount === 1) return 'Your turn · one card is legal';
  return `Your turn · follow ${suitName(led)}`;
}

/** THE VOID PLAYER'S CHOICE, before the reveal: two actions, each explained,
 *  neither a surprise. Playing a card without calling is the action row
 *  below; calling is this button. */
function callChoice(app, intents, led) {
  const { pub } = app;
  const best = winningPlay(pub.plays);
  const pts = pub.plays.reduce((n, p) => n + cardPoints(p.code), 0);
  return el('div', { class: 'call-choice' },
    best && el('p', { class: 'why' }, `${nameOf(pub, best.seat)} is winning with the ${cardName(best.code)} — ${plural(pts, 'point')} on the table.`),
    el('div', { class: 'choice-row' },
      el('div', { class: 'choice' },
        el('b', {}, 'Play without calling'),
        el('span', {}, 'Pick any card below. It is a plain discard, whatever its suit.')),
      el('button', {
        class: 'choice primary', onclick: () => intents.callTrump(), disabled: app.busy,
        'aria-label': `call for trump: you have no ${suitName(led)}`,
      },
      el('b', {}, 'Call for trump'),
      el('span', {}, 'Turns the trump up for everyone. You must then play a trump if you hold one.'))));
}

/** Two taps to play: select, look, confirm. A misplay cannot be taken back. */
function actionRow(app, intents) {
  const { pub, priv } = app;
  const sel = app.selected;
  const card = sel ? priv.hand.find((c) => c.code === sel) : null;
  const canPlayIt = !!card && card.legal && priv.isTurn && pub.phase === PHASES.PLAY;
  const stale = !!card && !card.legal && priv.isTurn;
  const label = (code) => `${rankLabel(code)}${suitGlyph(suitOf(code))}`;
  return el('div', { class: 'action-row' },
    sel && el('button', { class: 'btn btn-ghost', onclick: () => intents.selectCard(null) }, 'CANCEL'),
    el('button', {
      class: 'btn btn-primary', disabled: !canPlayIt || app.busy, onclick: () => intents.playCard(sel),
      'aria-label': stale ? `Cannot play ${cardName(sel)}: ${card.reason}` : null,
    }, stale ? `Cannot play ${label(sel)}`
      : (sel ? `Play ${label(sel)}${priv.canCall ? ' without calling' : ''}` : (priv.mustTrump ? 'Pick a trump' : 'Pick a card'))),
    stale && el('p', { class: 'hint' }, card.reason));
}

/** The banner for the trick in which trump was revealed: who called, what the
 *  indicator was, what is trump now. */
function revealBanner(app) {
  const { pub } = app;
  if (!pub.revealed || pub.revealTrick !== pub.trickIndex || !pub.indicator) return null;
  const who = pub.revealedBy === (app.priv && app.priv.seat) ? 'You' : nameOf(pub, pub.revealedBy);
  return el('div', { class: 'reveal-banner', role: 'status' },
    cardFace(pub.indicator.card, { cls: 'card-mini' }),
    el('span', {}, pub.revealedBy === pub.bidder && !pub.caller
      ? `${who} turned up the indicator — the ${cardName(pub.indicator.card)}. `
      : `${who} called for trump — the indicator was the ${cardName(pub.indicator.card)}. `,
    el('b', {}, `${suitName(pub.trump)} are trumps.`)));
}

// ###########################################################################
//
//  THE PHASE SCREENS
//
// ###########################################################################

function dealScreen(app, intents, which) {
  const { pub } = app;
  return playShell(
    playStrip(app, intents),
    el('div', { class: 'interstitial' },
      el('p', { class: 'inter-big' }, which === 'first' ? `Deal ${pub.dealIndex + 1}` : 'The last four'),
      el('p', { class: 'inter-sub' }, which === 'first'
        ? `${nameOf(pub, pub.dealerSeat)} deals four each, starting on their right`
        : (pub.trumpMode === 'seventh' ? 'the seventh card goes face down, unseen' : 'four more each')),
      el('span', { class: 'spinner' })),
    lookHand(app, which === 'first' ? 'Your first four — the auction is bid on these' : 'Your hand'),
    liveRegion(app.announce),
  );
}

function auctionScreen(app, intents) {
  const { pub, priv } = app;
  const mine = priv && priv.isTurn && Array.isArray(priv.bidOptions);
  return playShell(
    playStrip(app, intents),
    el('div', { class: 'bid-wrap' },
      mine ? bidPad(app, intents) : el('p', { class: 'bid-lede' }, `Waiting for ${nameOf(pub, pub.turnSeat)} to bid`),
      auctionLog(app)),
    errorNote(app),
    lookHand(app, 'Your first four'),
    liveRegion(app.announce),
  );
}

/** The calls so far, public once made. A bid being composed on somebody's
 *  phone is not here — it never left their device. */
function auctionLog(app) {
  const { pub } = app;
  const calls = pub.auction.calls;
  if (!calls.length) return el('p', { class: 'bid-meta' }, `Bidding opens at ${MIN_BID}, right of the dealer, and goes anticlockwise. A pass is final.`);
  return el('ol', { class: 'calls' }, calls.map((c) => el('li', { class: `call ${side(app, teamOf(c.seat))}${c.bid === null ? ' passed' : ''}` },
    el('span', { class: 'call-name' }, nameOf(pub, c.seat)),
    el('span', { class: 'call-bid' }, c.bid === null ? 'pass' : String(c.bid)))));
}

function bidPad(app, intents) {
  const { pub, priv } = app;
  const sel = app.selectedBid;
  const high = pub.auction.high;
  const partnerHigh = pub.auction.highSeat !== null && pub.auction.highSeat === partnerOf(priv.seat);
  return el('div', { class: 'bid-pad' },
    el('p', { class: 'bid-lede' }, high === null ? 'Open the bidding?' : `Beat ${high}?`),
    el('p', { class: 'bid-meta' }, high === null
      ? `Any bid from ${MIN_BID} to ${MAX_BID}. The bid is how many card points your side will take.`
      : `${nameOf(pub, pub.auction.highSeat)} holds ${high}${partnerHigh ? ' — that is your partner' : ''}.`),
    el('div', { class: 'bid-grid', role: 'group', 'aria-label': 'Your bid' },
      priv.bidOptions.filter((o) => o.legal).map((o) => el('button', {
        class: `bid-btn${sel === o.bid ? ' sel' : ''}`,
        'aria-pressed': sel === o.bid ? 'true' : 'false', 'aria-label': `bid ${o.bid}`,
        onclick: () => intents.selectBid(o.bid),
      }, String(o.bid)))),
    el('div', { class: 'action-row' },
      el('button', { class: 'btn btn-secondary', disabled: app.busy, onclick: () => intents.passBid(), 'aria-label': 'pass — final for this deal' }, 'PASS'),
      el('button', {
        class: 'btn btn-primary', disabled: sel === null || sel === undefined || app.busy,
        onclick: () => intents.placeBid(sel),
      }, sel === null || sel === undefined ? 'Pick a bid' : `Bid ${sel}`)));
}

function trumpScreen(app, intents) {
  const { pub, priv } = app;
  if (!priv || !priv.trumpChoice) {
    return playShell(
      playStrip(app, intents),
      el('div', { class: 'bid-wrap' },
        el('p', { class: 'bid-lede' }, `${nameOf(pub, pub.bidder)} is choosing trump`),
        el('p', { class: 'bid-meta' }, 'They place one card face down, or take the seventh card. Nobody else will know the suit until somebody calls for it.')),
      lookHand(app, 'Your first four'),
      liveRegion(app.announce));
  }
  const sel = app.selected;
  return playShell(
    playStrip(app, intents),
    el('div', { class: 'bid-wrap' },
      el('p', { class: 'bid-lede' }, 'Choose your trump'),
      el('p', { class: 'bid-meta' }, 'Place one card face down. Its suit is trump — known to you alone until somebody calls for it. It comes back to your hand at the reveal.'),
      el('div', { class: 'hand trump-pick' }, priv.hand.map((c) => el('button', {
        class: `card-btn${sel === c.code ? ' sel' : ''}`, 'aria-pressed': sel === c.code ? 'true' : 'false',
        'aria-label': `${cardLabel(c.code)}: make ${suitName(suitOf(c.code))} trumps`,
        onclick: () => intents.selectCard(c.code),
      }, cardFace(c.code)))),
      el('div', { class: 'action-row' },
        el('button', { class: 'btn btn-primary', disabled: !sel || app.busy, onclick: () => intents.chooseTrump(sel) },
          sel ? `Place ${rankLabel(sel)}${suitGlyph(suitOf(sel))} face down` : 'Pick a card')),
      priv.trumpChoice.seventh && el('button', {
        class: 'choice', onclick: () => intents.chooseSeventh(), disabled: app.busy,
        'aria-label': 'seventh card: let the seventh card dealt to you choose the trump, unseen',
      }, el('b', {}, 'Seventh card'), el('span', {}, 'Let the seventh card dealt to you be the trump, face down — unseen, even by you.'))),
    errorNote(app),
    liveRegion(app.announce),
  );
}

const DECLARE_WORDS = Object.freeze({
  single: { verb: 'Declare single hand', why: 'Win all eight tricks alone, with no trump; your partner sits out. Worth +3, or −3 the moment you lose a trick.' },
  double: { verb: 'Double', why: 'You think the bidders will fail. Their contract becomes worth 2 game points either way.' },
  redouble: { verb: 'Redouble', why: 'You are sure of the contract. It becomes worth 4 game points either way.' },
});

function declareScreen(app, intents) {
  const { pub, priv } = app;
  const stage = pub.declare ? pub.declare.stage : null;
  const mine = priv && priv.isTurn && Array.isArray(priv.declareOptions);
  return playShell(
    playStrip(app, intents),
    el('div', { class: 'bid-wrap' },
      mine
        ? el('div', { class: 'declare' },
          el('p', { class: 'bid-lede' }, stage === 'single' ? 'Single hand?' : (stage === 'double' ? 'Double?' : 'Redouble?')),
          el('p', { class: 'bid-meta' }, DECLARE_WORDS[stage].why),
          el('div', { class: 'action-row' },
            el('button', { class: 'btn btn-secondary', disabled: app.busy, onclick: () => intents.declare('pass') }, 'PASS'),
            el('button', { class: 'btn btn-primary', disabled: app.busy, onclick: () => intents.declare(stage) }, DECLARE_WORDS[stage].verb.toUpperCase())))
        : el('p', { class: 'bid-lede' }, `${nameOf(pub, pub.turnSeat)} is deciding whether to ${stage === 'single' ? 'declare single hand' : stage}`)),
    errorNote(app),
    lookHand(app, 'Your hand'),
    liveRegion(app.announce),
  );
}

function playScreen(app, intents) {
  return playShell(
    playStrip(app, intents),
    revealBanner(app),
    tableArea(app),
    errorNote(app),
    playHand(app, intents),
    liveRegion(app.announce),
  );
}

function dealOverScreen(app, intents) {
  const { pub, priv } = app;
  const last = pub.history[pub.history.length - 1];
  const owner = !!(priv && priv.isOwner);
  return shell(
    el('div', { class: 'over-head' },
      el('div', { class: 'over-title' },
        el('h2', {}, last && !last.thrownIn ? resultHeadline(pub, last) : `Deal ${pub.dealIndex + 1} over`),
        el('p', {}, pub.outcome ? 'That settles the match' : `${nameOf(pub, nextSeat(pub.dealerSeat))} deals next`)),
      helpBtn(intents)),
    last && !last.thrownIn && dealResult(app, last),
    el('div', { class: 'panel' }, scoreTracks(app)),
    el('div', { class: 'panel' },
      owner
        ? el('button', { class: 'btn btn-primary btn-wide', disabled: app.busy, onclick: () => intents.nextDeal() }, pub.outcome ? 'FINISH' : 'NEXT DEAL')
        : el('p', { class: 'hint' }, 'Waiting for the owner to deal the next one.'),
      leaveBtn(intents, 'LEAVE THE GAME')),
    errorNote(app),
    liveRegion(app.announce),
  );
}

function resultHeadline(pub, rec) {
  const team = teamNames(pub, rec.bidTeam);
  if (rec.single) return rec.made ? `${nameOf(pub, rec.single.seat)} takes all eight` : `${nameOf(pub, rec.single.seat)}'s single hand is beaten`;
  return `${team} ${rec.made ? 'make' : 'miss'} ${rec.finalBid}`;
}

/** Everything the brief asks the deal-over screen to show: the bid and any
 *  pair, the card points, the result, the multiplier and the game points. */
function dealResult(app, rec) {
  const { pub } = app;
  const rows = [];
  if (rec.single) {
    rows.push(['Single hand', `${nameOf(pub, rec.single.seat)}, ${nameOf(pub, rec.single.out)} sat out`]);
    rows.push(['Tricks', `${rec.tricksPlayed} played${rec.made ? ', all won' : ', the last one lost'}`]);
  } else {
    rows.push(['Bid', `${rec.bid} by ${nameOf(pub, rec.bidder)}`]);
    if (rec.pair) rows.push(['Pair', `${nameOf(pub, rec.pair.seat)}: ${rec.pair.from} → ${rec.pair.to}`]);
    rows.push(['Card points', `${teamNames(pub, rec.bidTeam)} ${rec.cardPoints[rec.bidTeam]} · ${teamNames(pub, 1 - rec.bidTeam)} ${rec.cardPoints[1 - rec.bidTeam]}`]);
    if (rec.trump) rows.push(['Trump', `${suitName(rec.trump)}${rec.trumpMode === 'seventh' ? ' (seventh card)' : ''}`]);
  }
  rows.push(['Multiplier', rec.multiplier > 1 ? `×${rec.multiplier}` : '×1']);
  return el('div', { class: `panel result ${rec.made ? 'made' : 'missed'}` },
    el('ul', { class: 'result-list' }, rows.map(([k, v]) => el('li', {}, el('span', { class: 'result-k' }, k), el('span', { class: 'result-v' }, v)))),
    el('p', { class: 'result-delta' }, `${teamNames(pub, rec.bidTeam)} ${fmtDelta(rec.delta)}`));
}

function matchOverScreen(app, intents) {
  const { pub, priv } = app;
  const o = pub.outcome;
  return shell(
    el('div', { class: 'over-head' },
      el('div', { class: 'over-title' },
        el('h2', {}, o ? `${teamNames(pub, o.winner)} win` : 'Match over'),
        el('p', {}, o ? (o.how === 'reached' ? `They reached +${MATCH_TARGET}` : `${teamNames(pub, o.loser)} fell to −${MATCH_TARGET}`) : '')),
      helpBtn(intents)),
    el('div', { class: 'panel' }, scoreTracks(app), historyTable(app)),
    el('div', { class: 'panel' },
      priv && priv.isOwner
        ? el('button', { class: 'btn btn-primary btn-wide', onclick: () => intents.newMatch() }, 'PLAY AGAIN')
        : el('p', { class: 'hint' }, 'Waiting for the owner.'),
      el('button', { class: 'btn btn-secondary btn-wide', onclick: () => intents.leaveGame() }, 'LEAVE')),
    liveRegion(app.announce),
  );
}

// ###########################################################################
//
//  THE SCOREBOARD
//
//  Each side on a −6 … +6 scale with the finish lines at both ends, so a
//  negative total and the ±6 finish read at a glance; then deal by deal.
//
// ###########################################################################

function scoreTrack(pub, team, cls, extra = 'track') {
  const gp = pub.gamePoints[team];
  const span = MATCH_TARGET * 2;
  const pct = (n) => `${((Math.min(Math.abs(n), MATCH_TARGET) / span) * 100).toFixed(1)}%`;
  const lead = pub.leader === team;
  const left = gp >= 0 ? MATCH_TARGET - gp : MATCH_TARGET + gp;
  return el('div', {
    class: `${extra} ${cls}`,
    'aria-label': `${teamNames(pub, team)}, ${gp < 0 ? 'minus ' : 'plus '}${Math.abs(gp)} game points, `
      + `${gp >= 0 ? `${left} from winning` : `${left} from losing`}`,
  },
  el('div', { class: 'track-head' },
    el('span', { class: 'track-name' }, teamNames(pub, team), lead ? ' ★' : ''),
    el('span', { class: `track-gp${gp < 0 ? ' neg' : ''}` }, fmtScore(gp))),
  el('div', { class: 'scale' },
    el('i', { class: 'scale-axis' }),
    gp !== 0 && el('i', { class: `scale-fill${gp < 0 ? ' neg' : ''}`, style: gp > 0 ? `left: 50%; width: ${pct(gp)}` : `right: 50%; width: ${pct(gp)}` }),
    el('i', { class: 'scale-zero' })));
}

function scoreTracks(app) {
  const { pub } = app;
  const mine = teamOf(mySeat(app));
  return el('div', { class: 'tracks' },
    [mine, 1 - mine].map((team) => scoreTrack(pub, team, side(app, team))),
    el('div', { class: 'scale-ends' }, el('span', { class: 'lose' }, `−${MATCH_TARGET} loses`), el('span', {}, '0'), el('span', { class: 'win' }, `+${MATCH_TARGET} wins`)));
}

function historyTable(app) {
  const { pub } = app;
  if (!pub.history.length) return el('p', { class: 'hint' }, 'No deals played yet.');
  return el('table', { class: 'hist' },
    el('thead', {}, el('tr', {}, ['#', 'Bidder', 'Bid → final', 'Pts', '×', 'Result'].map((h) => el('th', { scope: 'col' }, h)))),
    el('tbody', {}, pub.history.map((r, i) => {
      if (r.thrownIn) return el('tr', { class: 'thrown' }, el('td', {}, String(i + 1)), el('td', { colspan: '5' }, 'all passed · thrown in'));
      const who = r.single ? r.single.seat : r.bidder;
      return el('tr', {},
        el('td', {}, String(i + 1)),
        el('td', { class: side(app, teamOf(who)) }, el('i', { class: 'sw' }), nameOf(pub, who)),
        el('td', {}, r.single ? 'single' : (r.pair ? `${r.bid} → ${r.finalBid}` : String(r.bid))),
        el('td', {}, r.single ? `${r.tricksPlayed}/8` : String(r.cardPoints[r.bidTeam])),
        el('td', {}, r.multiplier > 1 ? String(r.multiplier) : '1'),
        el('td', { class: r.made ? 'made' : 'missed' }, `${side(app, r.bidTeam)} ${fmtDelta(r.delta)}`));
    })));
}

function padOverlay(app, intents) {
  return el('div', { class: 'sheet', role: 'dialog', 'aria-modal': 'true', 'aria-label': 'Score pad' },
    el('div', { class: 'sheet-inner' },
      el('button', { class: 'sheet-close', 'aria-label': 'Close', onclick: () => intents.togglePad() }, '✕'),
      el('h2', { class: 'sheet-title' }, 'Game points'),
      scoreTracks(app),
      historyTable(app)));
}

// ###########################################################################
//
//  LEAVING, AND THE LOG
//
// ###########################################################################

function leaveConsequence(app) {
  const { pub, priv } = app;
  const underWay = pub.phase !== PHASES.LOBBY && pub.phase !== PHASES.MATCH_OVER;
  if (app.isHost) {
    return underWay
      ? `You are hosting, so the game stops for everyone while you are away. It is kept on this device: RESUME on the home screen picks it up where it stopped, and the others rejoin room ${app.code}.`
      : 'You are hosting, so this closes the table for everyone at it.';
  }
  if (!priv) return 'You do not have a seat at this table, so nothing changes for the players.';
  if (!underWay) return 'Your seat is given up. The same code gets you back in while the table is open.';
  return `Your seat is kept, and a bot plays your cards while you are away. Rejoin room ${app.code} from this device to take it back.`;
}

function leaveOverlay(app, intents) {
  return el('div', { class: 'sheet', role: 'dialog', 'aria-modal': 'true', 'aria-label': 'Leave the game' },
    el('div', { class: 'sheet-inner leave-sheet' },
      el('button', { class: 'sheet-close', 'aria-label': 'Close', onclick: () => intents.toggleLeave() }, '✕'),
      el('h2', {}, 'Leave the game?'),
      el('p', {}, leaveConsequence(app)),
      el('div', { class: 'btn-row' },
        el('button', { class: 'btn btn-primary', onclick: () => intents.leaveGame() }, 'LEAVE'),
        el('button', { class: 'btn btn-secondary', onclick: () => intents.toggleLeave() }, 'STAY'))));
}

function logOverlay(app, intents) {
  const lines = app.pub.log || [];
  return el('div', { class: 'sheet', role: 'dialog', 'aria-modal': 'true', 'aria-label': 'What happened' },
    el('div', { class: 'sheet-inner' },
      el('button', { class: 'sheet-close', 'aria-label': 'Close', onclick: () => intents.toggleLog() }, '✕'),
      el('h2', { class: 'sheet-title' }, 'What happened'),
      el('ul', { class: 'log' }, lines.slice().reverse().map((l) => el('li', { class: `log-${l.kind}` }, l.text)))));
}

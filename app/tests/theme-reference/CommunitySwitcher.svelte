<script lang="ts">
  import Dialog from "./Dialog.svelte";
  import Glyph from "./Glyph.svelte";
  import Icon from "./Icon.svelte";
  import type { Actions, State } from "./model";
  import { short } from "./dom";
  import CommunityUnread from "./CommunityUnread.svelte";
  import { rowMenu } from "./contextmenu";
  import { holdMenu } from "./holdmenu";
  import { unreadInCommunity } from "./community-unread";
  import SquareAvatar from "./SquareAvatar.svelte";
  import { communityPhoto } from "./photo";
  import { ASKING_TO_JOIN, waitRow } from "./waiting";

  let { view, actions }: { view: State; actions: Actions } = $props();

  /**
   * The joins this node is still waiting on, minus any that have landed.
   *
   * `waiting` is the node's own durable record and `communities` is what
   * this node is actually in, and the two overlap for as long as it takes a
   * completed join to be cleared - so without this a community appears
   * twice for a moment, once as itself and once as still arriving.
   */
  let arriving = $derived(
    view.waiting.filter((join) => !view.communities.includes(join.community)),
  );

  /** The selected community first, then the rest in the node's order: the
   * one the reader is in is always the top row (decided 2026-09-22). */
  let ordered = $derived(
    view.community === null
      ? view.communities
      : [view.community, ...view.communities.filter((id) => id !== view.community)].filter((id) =>
          view.communities.includes(id),
        ),
  );
  /** A row's label: the name the node has, or the bracketed id. */
  const named = (id: string): string => view.communityNames[id] ?? `<${short(id)}>`;

</script>

<!--
  Which community the window is looking at.

  This was a second section at the bottom of the chats list, under the
  channels - so switching meant scrolling past every channel of the
  community you were leaving, and it was reachable from exactly one of the
  three screens. A sheet off the header is reachable from the one place a
  reader looks to find out where they are.

  A sheet rather than a seventh entry in `SHEETS`: that table asks one
  question with one text field, and this is a list whose length is the
  node's business.
-->
<!--
  Both bodies are one snippet, drawn twice: the phone's side sheet and the
  desktop's panel are the library's `Community switcher` (`5476:43210`)
  `Type=Mobile` and `Type=Desktop` over the same `Community switcher
  content` (`5476:40251`), and they differ in size and in where they hang,
  not in what they carry. `phone` picks the few things the frames draw
  differently - the close glyph - and the containers' rules do the rest.

  The rows: a close and the centred title over a hairline, one row per
  community on a 36px square tile with the current community first and
  outlined, add-member and settings at the far end of that row, then Join a
  community, Create a community and Linked devices on grey tiles. Add-member
  is the invitation - the prototype's "Add members" screen is a copy-link,
  QR and share list, which the invite overlay already is. Settings opens the
  settings drawer on the community's list, the prototype's "<community>
  options" screen, and closes this on the way.

  Neither body carries this device's own row. On the desktop that is the
  sidebar's `Profile summary`, pinned to the bottom of the column; on the
  phone it is the avatar at the right of the home head (2026-09-22).
-->
{#snippet body(phone: boolean)}
  <div class="panel-head">
    <button type="button" class="panel-close" aria-label="Close" onclick={actions.closeSwitcher}
      >{#if phone}<Glyph name="close" />{:else}<Icon name="close" />{/if}</button
    >
    <h2 class="panel-title">Communities</h2>
  </div>
  <div class="panel-list">
    {#each ordered as id (id)}
      {@const here = id === view.community}
      <div class="sw-row" data-current={here ? "true" : "false"}>
        <button
          type="button"
          class="sw-pick"
          aria-current={here ? "true" : undefined}
          onclick={() => actions.selectCommunity(id)}
          oncontextmenu={(event) => rowMenu(event, () => actions.communityMenu(id))}
          use:holdMenu={{ open: () => actions.communityMenu(id, "sheet") }}
        >
          <span class="sw-tile" class:sw-tile-here={here}>
            <SquareAvatar {id} name={view.communityNames[id] ?? null} size={36} photo={communityPhoto(view, id)} />
            <CommunityUnread unread={unreadInCommunity(view, id)} outlined={here} />
          </span>
          <span class="sw-label" title={id}>{named(id)}</span>
        </button>
        {#if here}
          <span class="sw-tools">
            <button type="button" class="sw-tool" aria-label="Add members" onclick={actions.issueInvite}
              ><Glyph name="add-person" /></button
            >
            <button
              type="button"
              class="sw-tool"
              aria-label="Community settings"
              onclick={() => actions.openSettings("community")}><Glyph name="gear" /></button
            >
          </span>
        {/if}
      </div>
    {/each}
    <!-- A join that has not been answered yet, which is a community this
         node cannot enter: selecting one would ask for channels and members
         that do not exist here. So it is a row and not a button - it is
         here to say the ask is still out, and whose move it is: members, the
         reader's own other device for a device link, or nobody at all on
         a link that needs no vouch - `waitRow` words it off the link. -->
    {#each arriving as join (join.community)}
      {@const said = waitRow(join)}
      <p class="sw-row sw-arriving" data-kind={join.kind}>
        <!-- JoinInFlight.name is the joiner's chosen user name. The node
             cannot read the community name until it is let in and synced. -->
        <span class="sw-tile"><SquareAvatar id={join.community} name={view.communityNames[join.community] ?? null} size={36} /></span>
        <span class="sw-wait">
          <span class="sw-label" title={join.community}>{named(join.community)}</span>
          <span class="sw-wait-line">{said.line}</span>
        </span>
        <span class="chip">{said.chip}</span>
      </p>
    {/each}
    <!-- The ask itself, before the node has a record of it: `join` dials
         every hint in the link before it returns, and a reader who closed
         the doors meanwhile would otherwise see nothing at all. -->
    {#if view.joining}
      <p class="sw-row sw-arriving" data-kind="asking">
        <span class="sw-tile sw-tile-grey"><Glyph name="add-person" /></span>
        <span class="sw-wait"><span class="sw-label">{ASKING_TO_JOIN}</span></span>
        <span class="chip">joining</span>
      </p>
    {/if}
  </div>
  <div class="panel-actions">
    <!-- The way in the blank slate takes, at the stage each row names. -->
    <button type="button" class="sw-pick sw-action" onclick={() => actions.showEntry("join")}>
      <span class="sw-tile sw-tile-grey"><Glyph name="add-person" /></span>
      <span class="sw-label">Join a community</span>
    </button>
    <button type="button" class="sw-pick sw-action" onclick={() => actions.showEntry("create")}>
      <span class="sw-tile sw-tile-grey"><Glyph name="add" /></span>
      <span class="sw-label">Create a community</span>
    </button>
    <!-- The doorway to the account's other devices, and the sharing side's
         way in. The action closes this, so the screen is what the reader
         lands on and not this over it. -->
    <button type="button" class="sw-pick sw-action" onclick={actions.openLinking}>
      <span class="sw-tile sw-tile-grey"><Glyph name="linked-devices" /></span>
      <span class="sw-label">Linked devices</span>
    </button>
  </div>
{/snippet}

<Dialog label="Communities" extra="switcher-overlay" close={actions.closeSwitcher}>
  <!--
    The phone's: the library's `Type=Mobile` and the prototype's
    `Sidepanel` (`8R3jXuoUxhNyczcClFTrDm`, `1085:24631`) - a 320px sheet
    from the left edge over the darkened window, its right corners at 16.
    `only-narrow`, so the stylesheet decides between it and the panel below,
    the same rule `Shell` uses for its two navigations.
  -->
  <div class="panel sw-phone only-narrow" data-switcher="phone">
    {@render body(true)}
  </div>

  <!--
    The desktop's: a popover rather than a centred dialog, hung off the head
    it was opened from, which is the frame's own reading of where the
    community name leads, and the mask behind it is clear, so the window it
    is over stays legible. Escape is `App.svelte`'s, a tap outside is the
    overlay's, and choosing a row closes it because the action does.
  -->
  <div class="panel only-wide" data-switcher="desktop">
    {@render body(false)}
  </div>
</Dialog>

<style>
  /* Under the sidebar head: the head is 32px under the column's 12px of
     air, below whatever band the platform puts over the window, and the
     panel starts 4px under it, 8px in from the column's edge - the head's
     own inset. 300 wide is the library's panel; its height is the rows',
     bounded by the window with the same 8px kept at the foot. */
  .panel {
    position: absolute;
    top: calc(var(--titlebar, 0px) + 48px);
    left: 8px;
    width: 300px;
    max-height: calc(100% - var(--titlebar, 0px) - 56px);
    overflow-y: auto;
    /* Panning and overscroll stop here rather than at `html` - see `styles.css`. */
    touch-action: pan-y;
    overscroll-behavior-y: contain;
    padding: 0 8px 8px;
    border: 1px solid var(--gray-06);
    border-radius: 16px;
    background: var(--panel);
    color: var(--fg);
    box-shadow: 0 8px 24px var(--mask);
    font-family: var(--font-sans);
    /* `fade` is the stylesheet's own keyframe, the lightbox's: a popover
       has no edge to arrive from either. */
    animation: fade var(--enter) var(--ease);
  }
  .panel-head {
    display: grid;
    grid-template-columns: 40px 1fr 40px;
    align-items: center;
    min-height: 56px;
    border-bottom: 1px solid var(--gray-06);
  }
  .panel-close {
    display: inline-flex;
    align-items: center;
    justify-content: center;
    width: 40px;
    height: 40px;
    min-height: 0;
    padding: 0;
    border: 0;
    border-radius: 8px;
    background: none;
    color: var(--fg);
  }
  .panel-close:hover {
    background: var(--gray-06);
  }
  .panel-close :global(svg) {
    width: 20px;
    height: 20px;
  }
  /* The library's title: 16/26 500 in ink, as written. The stylesheet's
     `h2` is the sheets' small capitals, and this is not a sheet. */
  .panel-title {
    grid-column: 2;
    margin: 0;
    text-align: center;
    color: var(--fg);
    font-size: 16px;
    line-height: 26px;
    font-weight: 500;
    letter-spacing: 0;
    text-transform: none;
  }
  .panel-list,
  .panel-actions {
    display: flex;
    flex-direction: column;
    gap: 4px;
    padding: 8px 0;
  }
  .panel-actions {
    border-top: 1px solid var(--gray-06);
  }
  .sw-row {
    position: relative;
    display: flex;
    align-items: center;
    margin: 0;
    border-radius: 8px;
  }
  .sw-row:hover {
    background: var(--gray-06);
  }
  .sw-pick {
    display: flex;
    flex: 1;
    min-width: 0;
    align-items: center;
    gap: 12px;
    min-height: 48px;
    padding: 8px;
    border: 0;
    border-radius: 8px;
    background: none;
    color: inherit;
    font: inherit;
    font-size: 14px;
    line-height: 20px;
    text-align: left;
  }
  .sw-pick:hover,
  .sw-action:hover {
    background: var(--gray-06);
  }
  .sw-tile {
    position: relative;
    display: inline-flex;
    flex: none;
    align-items: center;
    justify-content: center;
    width: 36px;
    height: 36px;
    border-radius: 4px;
    --dot-ring: var(--panel);
  }
  /* The current community: the library's `Outline`, a 42px square at
     radius 7 three pixels outside the 36px tile, stroked 2px inside in the
     library's vivid purple (`Channel avatars/Letter`, #9c00ff). Drawn as
     `::before` so the badge, a later sibling, paints over it - the badge
     sits on the outline's corner in the library and the outline must not
     cut through it. */
  .sw-tile-here::before {
    content: "";
    position: absolute;
    inset: -3px;
    border: 2px solid var(--channel-avatar-letter);
    border-radius: 7px;
    pointer-events: none;
  }
  /* The three ways out share the tile's footprint on a Gray 06 square, so
     their labels line up with the community names above them. */
  .sw-tile-grey {
    background: var(--gray-06);
    color: var(--fg);
  }
  /* The frame's `Avatar type` Type=Icon: a 16px glyph in the 6% tile, at
     both widths. */
  .sw-tile-grey :global(svg) {
    width: 16px;
    height: 16px;
  }
  .sw-label {
    flex: 1;
    min-width: 0;
    overflow: hidden;
    text-overflow: ellipsis;
    white-space: nowrap;
  }
  /* The two icons on the current row, in Gray 30 until the row is hovered
     and in ink under the pointer - the library's `Default`, `Hover` and
     `Hover action-icons` states. */
  .sw-tools {
    display: flex;
    flex: none;
    align-items: center;
    gap: 4px;
    padding-right: 8px;
    color: var(--gray-30);
  }
  .sw-tool {
    display: inline-flex;
    align-items: center;
    justify-content: center;
    width: 32px;
    height: 32px;
    min-height: 0;
    padding: 0;
    border: 0;
    border-radius: 6px;
    background: none;
    color: inherit;
  }
  .sw-tool:hover,
  .sw-tool:focus-visible {
    color: var(--fg);
    background: var(--gray-10);
  }
  .sw-tool :global(svg) {
    width: 20px;
    height: 20px;
  }
  .sw-arriving {
    padding: 8px;
    gap: 12px;
    min-height: 48px;
    color: var(--muted);
  }
  .sw-arriving:hover {
    background: none;
  }
  .sw-wait {
    display: flex;
    flex: 1;
    flex-direction: column;
    min-width: 0;
  }
  .sw-wait .sw-label {
    flex: none;
  }
  .sw-wait-line {
    overflow: hidden;
    font-size: 12px;
    line-height: 16px;
    text-overflow: ellipsis;
    white-space: nowrap;
  }
  .sw-arriving .chip {
    flex: none;
  }

  /* The phone's sheet: `Type=Mobile`, 320 wide from the left edge and the
     window's full height, its right corners at 16, over the overlay's
     darkened mask. The sheet starts below the status bar, while the mask
     covers the whole window so the band fades with the exposed Home. The
     sheet pays the home indicator's inset at the foot. */
  .panel.sw-phone {
    position: relative;
    top: auto;
    left: auto;
    display: flex;
    flex-direction: column;
    flex: 1;
    align-self: flex-start;
    width: min(320px, calc(100% - 56px));
    max-height: none;
    margin-top: env(safe-area-inset-top, 0px);
    padding: 0 0 var(--safe-bottom, env(safe-area-inset-bottom, 0px));
    border: 0;
    border-radius: 0 16px 16px 0;
    box-sizing: border-box;
    animation: sw-in var(--enter-far) var(--ease);
  }
  @keyframes sw-in {
    from {
      transform: translateX(-100%);
    }
  }
  /* `Title bar/Logged in` with `Left=Close`: 60 tall, the close glyph's
     28px box at 14 inside a 44px target, the title centred at 16/26 500,
     and the hairline edge to edge. */
  .sw-phone .panel-head {
    grid-template-columns: 44px 1fr 44px;
    min-height: 60px;
    padding: 0 8px 0 6px;
  }
  .sw-phone .panel-close {
    width: 44px;
    height: 44px;
  }
  .sw-phone .panel-close :global(svg) {
    width: 28px;
    height: 28px;
  }
  /* `Community nav row`, `Platform=Mobile`: 58 tall, the 36px tile three
     inside its 42px outline box at 16, the name at 70 in 16px ink. The row
     is inset 8 from the sheet's edges and rounded at 8, which is the shape
     a press fills - the desktop panel's, rather than the set's edge-to-edge
     wash. The list's 16 of foot and 8 more above the actions are the set's
     24 between the two groups, with no hairline. */
  .sw-phone .panel-list {
    gap: 0;
    padding: 8px 8px 16px;
  }
  .sw-phone .panel-actions {
    gap: 0;
    padding: 0 8px 8px;
    border-top: 0;
  }
  .sw-phone .sw-pick {
    min-height: 58px;
    font-size: 16px;
    line-height: 20px;
  }
  .sw-phone .sw-tile {
    margin: 3px;
  }
  .sw-phone .sw-arriving {
    min-height: 58px;
    font-size: 16px;
  }
  /* The two tools in ink, as the mobile row draws them: 24px glyphs 16
     apart with the gear 16 from the edge, each a 40x44 target. */
  .sw-phone .sw-tools {
    gap: 0;
    padding-right: 0;
    color: var(--fg);
  }
  .sw-phone .sw-tool {
    width: 40px;
    height: 44px;
  }
  .sw-phone .sw-tool :global(svg) {
    width: 24px;
    height: 24px;
  }
  /* A press on a phone, where nothing hovers: the same inset shape, a
     step darker. */
  .sw-phone .sw-row:active:not(.sw-arriving),
  .sw-phone .sw-action:active {
    background: var(--gray-10);
  }
  /* A scoped rule outranks the stylesheet's `.only-narrow`, so the sheet
     says for itself that the desktop does not draw it. */
  @media (min-width: 45rem) {
    .panel.sw-phone {
      display: none;
    }
  }
</style>

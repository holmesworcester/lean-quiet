<script lang="ts">
  /**
   * Why `--accent-ink` exists, and the rule it leaves behind.
   *
   * `theme.css` is mostly aliases, and it says why: the library's grays invert
   * as a couple, so `--fg` on `--bg` is the same relationship in both themes
   * without anybody restating it. Several roles are choices in dark rather
   * than an inversion, and `--accent` is one - it becomes the library's own
   * `Purple dark mode`, #2f193d.
   *
   * That colour is a FILL. Against the surfaces around it (#242424, #222222)
   * it is 1.01:1 - the same luminance, differing only in hue. A large area is
   * still perceptible, which is why the pane heads read as purple bands and
   * the designer's choice is working as intended. Anything small enough to
   * depend on luminance is not.
   *
   * The app had been light-only, so no rule pairing those two had ever been
   * looked at in dark, and adopting the library gave it a dark mode for the
   * first time. Eleven rules went with it. They are fixed now - `--accent-ink`
   * carries purple-as-ink and `--on-accent` carries white-on-the-accent - so
   * this story is the argument rather than the bug report, kept because the
   * distinction it draws is the standing rule and one case is still open.
   *
   * Every colour here is a literal rather than a token. The page has one theme
   * at a time and the comparison needs both, so a token would draw the same
   * half twice.
   */
  import Glyph from "../Glyph.svelte"

  let { view }: { view: "rule" | "mechanism" } = $props()

  const LIGHT = { bg: "#f7f7f7", accent: "#7647c7", ink: "#7647c7", fg: "#222222", panel: "#ffffff" }
  const DARK = { bg: "#242424", accent: "#2f193d", ink: "#dbbcf0", fg: "#eaeaea", panel: "#222222" }

  /**
   * The two jobs, and what each token measures at.
   *
   * `--accent` as a fill with `--on-accent` on it, and `--accent-ink` as ink
   * on a panel. Both hold in both themes, which is the whole point of their
   * being two names.
   */
  const JOBS = [
    {
      title: "A fill, with white on it",
      token: "--accent",
      ink: "--on-accent",
      was: "was --bg: 5.61:1 light, 1.02:1 dark",
      light: 6.01,
      dark: 15.82,
      who: "Accent bands and completed step marks. Filled buttons use --button-bg/--button-hover; the ordinary composer send is a blue glyph without a fill.",
    },
    {
      title: "Ink on a panel",
      token: "--panel",
      ink: "--accent-ink",
      was: "was --accent: 6.01:1 light, 1.01:1 dark",
      light: 6.01,
      dark: 9.44,
      who: ".wordmark, .waiting-mark, .channel-on, the focus ring, and a dozen more.",
    },
  ] as const

  /**
   * The last rule of this family to be fixed, drawn both ways.
   *
   * `was` is the old pairing and `now` is what `styles.css` reads today -
   * both drawn, because a specimen that shows only the defect asserts a bug
   * that is closed, and one that shows only the fix teaches nothing about the
   * shape it had. `foundations.test.ts` is what keeps the `now` column
   * honest: it reads the rule off `styles.css` and recomputes these numbers
   * from `theme.css`, so a colour moving under this file fails a test rather
   * than quietly making the page lie.
   */
  const INVERSION = {
    was: { bg: "panel", ink: "ink", light: 6.01, dark: 1.01 },
    now: { bg: "onaccent", ink: "accent", light: 6.01, dark: 15.82 },
  }
</script>

<div class="spec">
  {#if view === "rule"}
    <header>
      <h1>The accent is a fill; <code>--accent-ink</code> is an ink</h1>
      <p>
        One colour was being asked to do two jobs, and the library only has a
        colour for one of them. Dark mode is where they came apart: the
        library's <code>Purple dark mode</code> is #2f193d, which against a
        #222222 panel is 1.01:1 - fine as a band, invisible as a letter.
      </p>
      <p>
        Both columns below are literal hex, so this page says the same thing
        whichever theme you are reading it in.
      </p>
    </header>

    <ul class="jobs">
      {#each JOBS as job (job.token)}
        <li>
          <div class="head">
            <b>{job.title}</b>
            <code>{job.ink} on {job.token}</code>
          </div>
          <div class="pair">
            <span class="side" style:background={LIGHT.panel}>
              {#if job.token === "--accent"}
                <span class="sample-pill" style:background={LIGHT.accent} style:color="#ffffff">12</span>
              {:else}
                <span class="mark" style:color={LIGHT.ink}>Quiet</span>
              {/if}
              <span class="tag" style:color={LIGHT.fg}>light · {job.light.toFixed(2)}:1</span>
            </span>
            <span class="side" style:background={DARK.panel}>
              {#if job.token === "--accent"}
                <span class="sample-pill" style:background={DARK.accent} style:color="#ffffff">12</span>
              {:else}
                <span class="mark" style:color={DARK.ink}>Quiet</span>
              {/if}
              <span class="tag" style:color={DARK.fg}>dark · {job.dark.toFixed(2)}:1</span>
            </span>
          </div>
          <p class="note"><b>Before:</b> {job.was}</p>
          <p class="note">{job.who}</p>
        </li>
      {/each}
    </ul>

    <section>
      <h2>Current app roles</h2>
      <div class="runtime-examples">
        <div><button type="button" class="button">Filled action</button><p class="note">Shared button fill: --button-bg; hover: --button-hover.</p></div>
        <div class="composer-row"><button type="button" class="send send-ready" aria-label="Send example"><span class="send-mark"><Glyph name="send" /></span></button></div>
        <p class="note">Ordinary text-message send: blue glyph with no filled background. Recording send retains its filled action.</p>
        <div class="step-done"><span class="step-mark">1</span></div>
        <p class="note">Completed onboarding step: --on-accent on --accent.</p>
      </div>
      <p class="lede">
        The comparison above teaches the band’s fill and panel ink, and
        the runtime controls above it keep their own roles. Every rule that put <code>--bg</code> on the accent or
        <code>--accent</code> on a panel now takes the token that means it,
        <code>.avatar</code> included. The last one to go is kept below,
        because it is the shape the next one of these will take and a
        text-contrast sweep structurally cannot find it: not an ink against a
        fill, but an <em>inversion</em> that stopped inverting.
      </p>

      <ul class="jobs">
        <li>
          <div class="head">
            <b>The community mark on the chats head</b>
            <code>.avatar-on-accent</code>
          </div>
          <p class="note"><b>Was</b> <code>background: var(--panel)</code></p>
          <div class="pair">
            <span class="side" style:background={LIGHT.accent}>
              <span class="sq" style:background={LIGHT.panel} style:color={LIGHT.ink}>R</span>
              <span class="tag" style:color="#ffffff">light · {INVERSION.was.light.toFixed(2)}:1</span>
            </span>
            <span class="side" style:background={DARK.accent}>
              <span class="sq" style:background={DARK.panel} style:color={DARK.ink}>R</span>
              <span class="tag" style:color="#ffffff">dark · <b>{INVERSION.was.dark.toFixed(2)}:1</b></span>
            </span>
          </div>
          <p class="note"><b>Now</b> <code>background: var(--on-accent); color: var(--accent)</code></p>
          <div class="pair">
            <span class="side" style:background={LIGHT.accent}>
              <span class="sq" style:background="#ffffff" style:color={LIGHT.accent}>R</span>
              <span class="tag" style:color="#ffffff">light · {INVERSION.now.light.toFixed(2)}:1</span>
            </span>
            <span class="side" style:background={DARK.accent}>
              <span class="sq" style:background="#ffffff" style:color={DARK.accent}>R</span>
              <span class="tag" style:color="#ffffff">dark · {INVERSION.now.dark.toFixed(2)}:1</span>
            </span>
          </div>
          <p class="note">
            The <em>ink</em> moved to <code>--accent-ink</code> with the rest,
            which was correct and not enough: <code>--panel</code> inverts to
            #222222, so on the #2f193d band the square <em>was</em> the band.
            The prop exists to invert against that band and in dark it did not
            invert at all.
          </p>
          <p class="note">
            And <code>--accent</code> as the mark, not
            <code>--accent-ink</code>: the rule this story states is about
            accent on a <em>panel</em>, and on a fixed white there is no theme
            to survive - the ink there would be 1.68:1. Worth stating, because
            otherwise the surface and its ink eventually go pale together.
          </p>
        </li>
      </ul>
    </section>

  {:else}
    <header>
      <h1>Why it happened</h1>
      <p>
        Nothing in either file was wrong on its own, which is why this is worth
        a page rather than a line in a diff.
      </p>
    </header>

    <ol class="why">
      <li>
        <h2>Most of <code>theme.css</code> is an alias, and that is the whole design</h2>
        <p>
          The library's grays invert as a couple - <code>White</code> is
          #ffffff in light and #222222 in dark - so
          <code>--panel: var(--white)</code> is the entire statement of
          "panels are the raised surface in both themes". A pair built from
          two such aliases keeps its relationship for free, in both
          directions, with nobody restating it.
        </p>
        <div class="demo">
          <span class="swatch-chip" style:background={LIGHT.bg} style:color={LIGHT.fg}>--fg on --bg</span>
          <span class="swatch-chip" style:background={DARK.bg} style:color={DARK.fg}>--fg on --bg</span>
        </div>
      </li>
      <li>
        <h2>Some roles are choices in dark, not an inversion</h2>
        <p>
          <code>--accent</code> is one. It is a <em>fill</em> for the sidebar and desktop pane bands -
          phone pane heads and the Threads head use <code>--panel</code> - and the library ships a colour for exactly
          that case, so dark swaps in <code>Purple dark mode</code> rather
          than letting a light purple invert into something nobody picked.
          That is the right call and it is argued for in
          <code>theme.css</code>.
        </p>
        <div class="demo">
          <span class="swatch-chip" style:background={LIGHT.accent} style:color="#ffffff">#7647c7</span>
          <span class="swatch-chip" style:background={DARK.accent} style:color="#ffffff">#2f193d</span>
        </div>
      </li>
      <li class="broken">
        <h2>So the accent stopped moving with the ground</h2>
        <p>
          In light, <code>--bg</code> is #f7f7f7 and <code>--accent</code> is
          #7647c7: a near-white ink on a dark fill, 5.6:1, and a rule written
          that way looks deliberate. In dark, <code>--bg</code> goes to
          #242424 and <code>--accent</code> goes to #2f193d - the same
          luminance, differing only in hue. No rule changed; one of the two
          tokens under it stopped being the other's opposite.
        </p>
        <p>
          Which is why the symptom was selective rather than total, and why
          looking at a screenshot of a pane head would not have found it. A
          band of #2f193d on #242424 is perfectly visible - hue is enough at
          that size, and it is what the designer picked for a dark ground.
          Twelve-point digits inside it are not.
        </p>
        <div class="demo">
          <span class="swatch-chip" style:background={LIGHT.accent} style:color={LIGHT.bg}>5.61:1</span>
          <span class="swatch-chip" style:background={DARK.accent} style:color={DARK.bg}>1.02:1</span>
        </div>
      </li>
      <li>
        <h2>The library already had the missing colour</h2>
        <p>
          <code>Channel avatars/Letter</code> - #9c00ff light, #dbbcf0 dark -
          is the library's purple that is meant to be <em>read</em> rather
          than filled, and its partner is already aliased here as
          <code>--tint</code>. <code>--accent-ink</code> borrows its dark
          value and keeps #7647c7 in light, so nothing moved in the theme the
          app had actually been looked at in.
        </p>
        <div class="demo">
          <span class="swatch-chip" style:background={LIGHT.panel} style:color={LIGHT.ink}>#7647c7 · 6.01:1</span>
          <span class="swatch-chip" style:background={DARK.panel} style:color={DARK.ink}>#dbbcf0 · 9.44:1</span>
        </div>
      </li>
    </ol>

    <p class="warn">
      The general form is worth stating because it will happen again: <b>a
      pair of tokens is only a pair while both are aliases to things that
      invert together.</b> The moment one is given a hand-picked dark value,
      every rule pairing it with an inverting token is making a claim that is
      true in one theme and unchecked in the other. <code>--accent</code>,
      <code>--accent-line</code> and <code>--warning</code> are the three, and
      <code>--mask</code> and <code>--on-accent</code> exist because somebody
      had already found two more of these and fixed them the same way.
    </p>
    <p class="warn">
      Nothing here was found by reading. The app had no
      <code>prefers-color-scheme</code> rule at all before
      <code>theme.css</code>, so every one of these rules had been correct for
      as long as it had been looked at.
    </p>
  {/if}
</div>

<style>
  /* Scrolls inside itself - see `Palette.svelte`. */
  .spec {
    padding: 1.5rem;
    background: var(--bg);
    color: var(--fg);
    height: 100%;
    overflow: auto;
    box-sizing: border-box;
  }
  header { max-width: 52ch; margin-bottom: 1.5rem; }
  h1 { font-size: 1.25rem; margin: 0 0 0.5rem; }
  h2 { font-size: 0.875rem; margin: 0 0 0.375rem; }
  header p { margin: 0 0 0.5rem; color: var(--muted); font-size: 0.8125rem; line-height: 1.5; }
  code { font-family: ui-monospace, SFMono-Regular, monospace; font-size: 0.9em; }
  .note { margin: 0.5rem 0 0; color: var(--muted); font-size: 0.75rem; line-height: 1.5; }
  section { margin-top: 1.5rem; }

  .warn {
    max-width: 52ch;
    margin: 1rem 0 0;
    padding: 0.75rem;
    border-radius: 0.5rem;
    background: var(--highlight);
    font-size: 0.8125rem;
    line-height: 1.55;
  }

  ul, ol { list-style: none; margin: 0; padding: 0; display: grid; gap: 0.5rem; max-width: 40rem; }
  li {
    background: var(--panel);
    border: 1px solid var(--line);
    border-radius: 0.5rem;
    padding: 0.875rem;
  }
  li.broken { border-left: 3px solid var(--error); }
  .head { display: flex; flex-wrap: wrap; align-items: baseline; gap: 0.5rem; margin-bottom: 0.625rem; }
  .head b { font-size: 0.8125rem; }
  .head code { font-size: 0.75rem; color: var(--muted); margin-left: auto; }

  .pair, .demo { display: grid; grid-template-columns: 1fr 1fr; gap: 0.5rem; }
  /* A mid-grey outline rather than `--line`: the dark swatch is #222222 and
     so is `--panel` in dark, so without an edge that half of every row
     dissolves into the card behind it - and a token would invert and leave
     the other half edgeless instead. This grey is legible against both. */
  .side {
    display: flex;
    align-items: center;
    gap: 0.625rem;
    border-radius: 0.375rem;
    padding: 0.625rem 0.75rem;
    box-shadow: inset 0 0 0 1px #7f7f7f;
  }
  /* `.badge`'s geometry restated: a specimen that borrowed the class would
     take the tokens with it, and taking the tokens is what this page is about
     not doing. Same for `.avatar` below it. */
  .sample-pill {
    min-width: 1.25rem;
    padding: 0 0.375rem;
    border-radius: 999px;
    font-size: 0.75rem;
    font-variant-numeric: tabular-nums;
    line-height: 1.25rem;
    text-align: center;
  }
  /* The square avatar mark, restated rather than borrowed for the reason
     `.sample-pill` is. */
  .sq {
    display: flex;
    align-items: center;
    justify-content: center;
    width: 1.75rem;
    height: 1.75rem;
    flex: none;
    border-radius: 4px;
    font-size: 0.75rem;
    font-weight: 600;
    line-height: 1;
  }
  .tag { font-size: 0.6875rem; }
  .mark { font-size: 1.125rem; font-weight: 600; letter-spacing: -0.01em; }

  .swatch-chip {
    display: flex;
    align-items: center;
    justify-content: center;
    border-radius: 0.375rem;
    padding: 0.875rem 0.5rem;
    font-family: ui-monospace, SFMono-Regular, monospace;
    font-size: 0.75rem;
  }

  .why p { margin: 0 0 0.625rem; font-size: 0.8125rem; line-height: 1.55; color: var(--muted); }

  @media (max-width: 30rem) {
    .pair, .demo { grid-template-columns: 1fr; }
  }
</style>

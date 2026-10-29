<script lang="ts">
  import Icon from "./Icon.svelte";
  import type { IconName } from "./icons";
  import type { Actions, State } from "./model";
  import { showing, type ToastTone } from "./toast";

  let {
    view,
    actions,
  }: { view: Pick<State, "status" | "note" | "noteTone">; actions: Pick<Actions, "dismissNotice"> } = $props();

  let toast = $derived(showing(view));

  /**
   * The card's own identity, so a new one is a fresh mount rather than a
   * re-render of the last - which is what restarts the fade in, and the fade
   * out that ends a note's life.
   *
   * The text is part of it: two failures in a row are two things to read,
   * and an animation that carried on from the first would give the second
   * whatever was left of it.
   */
  let key = $derived(toast === null ? null : `${toast.tone}:${toast.text}`);

  const marks: Record<ToastTone, IconName> = { ok: "check", info: "info", error: "alert" };

  // No timer here, deliberately, and this comment is the guard on that. The
  // life belongs to `controller.ts`'s `noteThat`, which is the one place a
  // note is raised and so the one place that can reset the clock when the
  // same sentence is raised twice - a `$effect` keyed on the card cannot see
  // that happen, because nothing about the card changed. A timer here as well
  // is not belt and braces: the two disagree, and the one that fires first
  // wins.
</script>

<!--
  The one card that floats over the app - see `toast.ts` for why there is
  one of them now and what went where.

  A `<section>` rather than a `Dialog`: it is not a layer, nothing is
  trapped in it, and `dismissTop` deliberately does not name it. Escape and
  a back gesture are for undoing where a reader *is*, and a toast is not
  somewhere they went - answering the back gesture with it would spend a
  press that was meant for the channel underneath.

  `aria-live="polite"` is what makes it reach a reader who is not looking at
  this part of the window. Polite rather than assertive even for a failure:
  nothing here is worth interrupting a sentence being read aloud, and every
  one of these is also either recoverable or already over.
-->
{#if toast !== null}
  {#key key}
    <section class="toast toast-{toast.tone}" class:toast-timed={toast.timed} aria-live="polite">
      <Icon name={marks[toast.tone]} />
      <span class="toast-text">{toast.text}</span>
      <!-- Only `status` stands; even an error-toned note fades on its own. -->
      {#if !toast.timed}
        <button type="button" class="toast-dismiss" aria-label="Dismiss" onclick={() => actions.dismissNotice("status")}
          ><Icon name="close" /></button
        >
      {/if}
    </section>
  {/key}
{/if}

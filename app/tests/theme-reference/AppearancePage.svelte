<script lang="ts">
  import type { Theme } from "./api";
  import Icon from "./Icon.svelte";
  import type { Actions, State } from "./model";
  import { THEMES } from "./theme";

  let { view, actions }: { view: State; actions: Actions } = $props();
  // Unread is drawn as System, which is what the page is doing until it is.
  let current = $derived<Theme>(view.theme ?? "system");
</script>

<div class="page" data-appearance>
  <p class="section-title">Theme</p>
  {#each THEMES as choice (choice.value)}
    <button type="button" class="set-row" aria-pressed={current === choice.value}
      onclick={() => actions.setTheme(choice.value)}>
      <span class="set-label">{choice.label}</span>
      {#if current === choice.value}<span class="set-check"><Icon name="check" /></span>{/if}
    </button>
  {/each}
</div>

<style>
  .page { display: flex; flex-direction: column; }
  .section-title { margin: 0; padding: 16px 16px 8px; color: var(--gray-50); font-size: 11px; line-height: 16px; letter-spacing: .06em; text-transform: uppercase; }
</style>

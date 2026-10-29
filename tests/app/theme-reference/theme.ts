import type { Theme } from "./api";

/**
 * Put the reader's theme on the root, where the design sheets' `[data-theme]`
 * blocks win over `prefers-color-scheme` in both directions. System - or a
 * setting not read yet - names none, so the sheets answer the platform; see
 * `app/AGENTS.md`, "The app follows the system's dark mode".
 */
export function applyTheme(root: HTMLElement, theme: Theme | null): void {
  if (theme === "light" || theme === "dark") root.dataset.theme = theme;
  else delete root.dataset.theme;
}

/** Whether the page is drawn dark: the reader's pick, or else the system's. */
export function drawnDark(theme: Theme | null, scheme: MediaQueryList | undefined): boolean {
  if (theme === "light") return false;
  if (theme === "dark") return true;
  return scheme?.matches ?? false;
}

/** The Appearance page's choices, in the order it draws them. */
export const THEMES: readonly { value: Theme; label: string }[] = [
  { value: "system", label: "System" },
  { value: "light", label: "Light" },
  { value: "dark", label: "Dark" },
];

export function themeLabel(theme: Theme | null): string {
  return THEMES.find((choice) => choice.value === (theme ?? "system"))!.label;
}

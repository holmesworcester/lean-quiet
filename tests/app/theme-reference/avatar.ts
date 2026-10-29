// The colour an identity is drawn in, derived from its id.
//
// From the *id* and never from the name, which is the whole point: a name is
// free-form and non-unique, so a colour keyed on one would give an
// impersonator their target's badge as well as their label. Keyed on the id
// it is a second rendering of the identifier - two people who pick the same
// name still differ here - and it is stable for as long as the id is.
//
// The avatar colour is a visual cue, not a readable identifier. `Identity`
// retains the full id on the name's title for inspection.

import type { HexId } from "./api";

/**
 * The colours an avatar can take.
 *
 * Picked in oklch at the accent's own lightness (L 0.52) with the chroma
 * sRGB has left at each hue, so they are siblings of `--accent` rather than
 * a second palette - the same relationship `--self` has to it.
 *
 * **They do not invert, so the ink on them may not either.** These eight are
 * literals and hold still between themes; `.avatar` therefore draws its glyph
 * in `--on-accent`, which is the fixed colour white, and not in `--bg`, which
 * is the ground and flips to near-black - 2.6:1 at worst on these discs
 * against 5.2:1 for the fixed ink.
 *
 * Hue 240 is deliberately absent: that is `--self`, which marks *this
 * device* wherever a roster names it, and an unrelated member wearing it
 * would spend the one colour that means something.
 */
export const AVATAR_COLORS = [
  "#af3c40", // 22
  "#9f5102", // 55
  "#786900", // 100
  "#047e39", // 150
  "#037879", // 196
  "#4860be", // 270
  "#7252b4", // 296
  "#974391", // 330
] as const;

/**
 * Which of them an id wears.
 *
 * The whole id is folded rather than its first byte: ids are compared by
 * their first eight characters everywhere a reader sees one, so a hash over
 * a prefix would collide exactly where two ids already look alike.
 */
export function avatarColor(id: HexId): string {
  let hash = 0;
  for (let i = 0; i < id.length; i += 1) {
    hash = (Math.imul(hash, 31) + id.charCodeAt(i)) >>> 0;
  }
  return AVATAR_COLORS[hash % AVATAR_COLORS.length] as string;
}

/**
 * What an avatar draws for someone with no name.
 *
 * Two characters of the id rather than a silhouette or a question mark: the
 * row beside it is already the bracketed id, so this is the same identifier
 * at a glance instead of a picture saying "unknown" twice.
 */
export function avatarFallback(id: HexId): string {
  return id.slice(0, 2);
}

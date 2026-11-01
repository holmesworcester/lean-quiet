import { createHighlighterCore } from 'shiki/core';
import { createJavaScriptRegexEngine } from 'shiki/engine/javascript';
import lean from '@shikijs/langs/lean';
import javascript from '@shikijs/langs/javascript';
import markdown from '@shikijs/langs/markdown';
import rust from '@shikijs/langs/rust';
import light from '@shikijs/themes/github-light';
import dark from '@shikijs/themes/github-dark';

let highlighter;
export const highlightingReady = createHighlighterCore({
  langs: [lean, javascript, markdown, rust],
  themes: [light, dark],
  engine: createJavaScriptRegexEngine(),
}).then(value => { highlighter = value; });

const escape = value => value.replace(/[&<>"']/g, c => ({'&':'&amp;', '<':'&lt;', '>':'&gt;', '"':'&quot;', "'":'&#39;'}[c]));
export const languageFor = path => path.endsWith('.lean') ? 'lean' : path.endsWith('.rs') ? 'rust' : path.endsWith('.js') ? 'javascript' : path.endsWith('.md') ? 'markdown' : 'text';

// Tokenize the whole document so multiline comments and strings retain scope.
// A small cache keeps normal SPA state changes from re-tokenizing long sources.
const cache = new Map();
export function highlightedLines(source, lang = 'lean', isDark = false) {
  const key = `${isDark}:${lang}:${source}`;
  if (cache.has(key)) return cache.get(key);
  const { tokens } = highlighter.codeToTokens(source, {lang, theme: isDark ? 'github-dark' : 'github-light'});
  const lines = tokens.map(line => line.map(token => `<span style="color:${token.color}">${escape(token.content)}</span>`).join(''));
  if (cache.size >= 40) cache.delete(cache.keys().next().value);
  cache.set(key, lines);
  return lines;
}

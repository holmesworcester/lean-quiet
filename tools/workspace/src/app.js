// The Quiet workspace: the project's file tree is the only navigation.
// Folders under app/ are ops and their families as they are on disk
// (tools/plan.py); each file shows its code, and a planned one says so.
import { initialState, act, verdict, scenarios } from "./state.js";
import { proofs, threats } from "./data.js";
import { previews as previewDocs } from "./documents.js";
import { definitionRange, replaceDefinition } from "./source-tools.js";
import { highlightingReady, highlightedLines, languageFor } from "./highlight.js";
import { index, href, sourceHref, canonical, laws, ROOTS } from "./tree.js";

const $ = s => document.querySelector(s);
const esc = s => String(s).replace(/[&<>"']/g, c => ({"&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;"})[c]);
const paths = {
  gear: "M12 3v3M12 18v3M3 12h3M18 12h3M5.6 5.6l2.1 2.1M16.3 16.3l2.1 2.1M5.6 18.4l2.1-2.1M16.3 7.7l2.1-2.1M17 12a5 5 0 1 1-10 0 5 5 0 0 1 10 0",
  arrow: "M5 12h14M14 7l5 5-5 5", search: "M15 15l6 6M17 10a7 7 0 1 1-14 0 7 7 0 0 1 14 0",
  play: "M7 4l14 8-14 8z", refresh: "M20 8A9 9 0 1 0 21 15M20 3v5h-5", clock: "M12 7v5l3 2M22 12a10 10 0 1 1-20 0 10 10 0 0 1 20 0",
  shield: "M12 3l8 3v6c0 5-8 9-8 9s-8-4-8-9V6z", menu: "M4 6h16M4 12h16M4 18h16",
  leaf: "M20 3C4 2 1 12 8 17s14-1 12-14zM4 21L16 8",
};
const icon = (name, cls = "") => `<svg class="${cls}" viewBox="0 0 24 24" aria-hidden="true"><path d="${paths[name]}"/></svg>`;

let saved = {};
try { saved = JSON.parse(sessionStorage.getItem("quiet-workspace-state") || "{}"); } catch {}
let state = initialState(saved), kernel, evidence, sourceIndex, plan, tree, kernelSource = "", route;
let proofSession = {busy: false, loaded: false, output: "", status: "idle", hint: false, job: 0};
let search = "", mobileOpen = false, renderedHash = "";
const expandedTree = new Set(["app", "app/community"]), expandedDetails = new Set(), sourceCache = new Map();
const persist = () => { try { sessionStorage.setItem("quiet-workspace-state", JSON.stringify(state)); } catch {} };
const toast = text => { $("#toast").textContent = text; $("#toast").classList.add("show"); clearTimeout(toast.t); toast.t = setTimeout(() => $("#toast").classList.remove("show"), 3000); };
function dispatch(action, redraw = true) { state = act(state, action, kernel); persist(); if (redraw) render(); }

// ---- Routes ----------------------------------------------------------------
function parseRoute() {
  const parts = location.hash.replace(/^#\/?/, "").split("/");
  if (parts[0] === "tree") {
    const segs = parts.slice(1).map(decodeURIComponent).filter(Boolean);
    const line = /^\d+$/.test(segs.at(-1) || "") && segs.at(-2)?.endsWith(".lean") ? Number(segs.pop()) : 0;
    return {section: "tree", path: segs.join("/") || "app", line};
  }
  if (parts[0] === "network") return {section: "network"};
  if (parts[0] === "ops") return {section: "tree", path: tree.previews[decodeURIComponent(parts[1] || "")] || "app"};
  if (parts[0] === "source") return {section: "source", path: decodeURIComponent(parts[1] || ""), line: Number(parts[2] || 1)};
  return {section: parts[0] || "tree", id: decodeURIComponent(parts[1] || ""), path: "app"};
}
const previewOf = path => tree.nodes.get(path)?.preview;
const isNetwork = () => route.section === "network";
const previewHref = id => id === "network" ? "#/network" : href(tree.previews[id] || "app");

// ---- Code -------------------------------------------------------------------
function codeBlock(text, lang = "lean") {
  return `<pre class="syntax"><code>${highlightedLines(text, lang, state.shellDark).join("\n")}</code></pre>`;
}
function codeEditor(id, label, value, disabled = false) {
  return `<div class="highlight-editor"><pre class="syntax editor-paint" aria-hidden="true"><code>${highlightedLines(value, "lean", state.shellDark).join("\n")}\n</code></pre><textarea id="${id}" aria-label="${label}" spellcheck="false" autocapitalize="off" autocomplete="off" autocorrect="off" wrap="off" ${disabled ? "disabled" : ""}>${esc(value)}</textarea></div>`;
}
function refreshEditor(editor) {
  const pre = editor.previousElementSibling;
  pre.firstElementChild.innerHTML = highlightedLines(editor.value, "lean", state.shellDark).join("\n") + "\n";
  pre.scrollTop = editor.scrollTop; pre.scrollLeft = editor.scrollLeft;
}
const trim = text => text.replace(/\n$/, "");
// A file under app/: short ones inline, long ones folded and filled on open.
function fileCode(path, file) {
  if (file.lines <= 40) return `<div class="file-code">${codeBlock(trim(file.text))}</div>`;
  const count = path.endsWith("/Proofs.lean") ? ` · ${laws(file.text).length} laws` : "";
  return `<details class="file-code" data-detail="${esc(path)}" data-file="${esc(path)}"><summary><code>${esc(path.split("/").at(-1))}</code><span class="lines">${file.lines} lines${count}</span></summary><div class="file-code-body"></div></details>`;
}
function fillFile(el) {
  const box = el.querySelector(".file-code-body");
  if (box && !box.innerHTML) box.innerHTML = codeBlock(trim(plan.files[el.dataset.file].text));
}
// A whole file, numbered; each line links to itself.
function sourceLines(path, text, line = 0) {
  const at = n => route.section === "source" ? sourceHref(path, n) : href(path, n);
  return `<div class="source-document syntax">${highlightedLines(trim(text), languageFor(path), state.shellDark).map((l, i) => `<div class="source-line ${line === i + 1 ? "selected-line" : ""}" id="line-${i + 1}"><a class="line-number" href="${at(i + 1)}" aria-label="Line ${i + 1}">${i + 1}</a><code>${l || " "}</code></div>`).join("")}</div>`;
}

// ---- Sidebar -----------------------------------------------------------------
function revealTree(path) {
  const parts = (path || "").split("/");
  for (let i = 1; i < parts.length; i++) expandedTree.add(parts.slice(0, i).join("/"));
  if (tree.entries.get(path)?.kind === "dir") expandedTree.add(path);
}
function sidebar() {
  const selected = route.section === "tree" ? route.path : null, query = search.trim().toLowerCase();
  let visible = null;
  if (query) {
    visible = new Set();
    for (const e of tree.entries.values()) if (`${e.path} ${canonical(e.path)}`.toLowerCase().includes(query)) {
      const parts = e.path.split("/");
      for (let i = 1; i <= parts.length; i++) visible.add(parts.slice(0, i).join("/"));
    }
  }
  const branch = e => {
    if (visible && !visible.has(e.path)) return "";
    const dir = e.kind === "dir", open = query ? true : expandedTree.has(e.path), node = tree.nodes.get(e.path);
    const cls = [selected === e.path ? "active" : "", e.planned || node?.planned ? "planned" : "", node?.kind === "op" ? "op" : ""].join(" ").trim();
    return `<li data-entry-path="${esc(e.path)}" data-entry-kind="${e.kind}">` +
      `<div class="tree-row">${dir ? `<button class="tree-toggle" data-action="tree-toggle" data-path="${esc(e.path)}" aria-label="${open ? "Collapse" : "Expand"} ${esc(e.path)}" aria-expanded="${open}">${open ? "▾" : "▸"}</button>` : '<span class="tree-indent"></span>'}` +
      `<a class="nav-item ${cls}" href="${href(e.path)}" title="${esc(e.path)}" ${selected === e.path ? 'aria-current="page"' : ""}>${esc(e.name)}${dir ? "/" : ""}</a></div>` +
      `${dir && open ? `<ul>${tree.children(e.path).map(branch).join("")}</ul>` : ""}</li>`;
  };
  const roots = ROOTS.map(r => tree.entries.get(r)).filter(Boolean).map(branch).join("");
  return `<aside class="sidebar ${mobileOpen ? "open" : ""}"><button class="mobile-menu close-navigation" data-action="menu" aria-label="Close navigation">Close</button>` +
    `<div class="searchbox">${icon("search")}<input id="nav-search" aria-label="Find a file" placeholder="Find a file…" value="${esc(search)}"><span class="key">/</span></div>` +
    `<nav class="file-navigation" aria-label="Project file tree"><ul class="file-tree">${roots || '<li class="empty">No matching files</li>'}</ul></nav>` +
    `<div class="sidebar-note"><button class="theme-toggle" data-action="shell-theme">${state.shellDark ? "Light mode" : "Dark mode"}</button></div></aside>`;
}
function breadcrumbs() {
  const path = ["tree", "source"].includes(route.section) ? route.path : "app";
  const parts = path.split("/");
  const crumbs = parts.map((p, i) => route.section === "source" ? `<span>${esc(p)}</span>` : `<a href="${href(parts.slice(0, i + 1).join("/"))}">${esc(p)}</a>`);
  if (isNetwork()) crumbs.push("<span>network</span>");
  return `<div class="breadcrumb"><button class="icon-btn mobile-menu" data-action="menu" aria-label="Toggle navigation">${icon("menu")}</button>${crumbs.join("<span>/</span>")}</div>`;
}

// ---- Live previews (one fixture store, shared by every view) ---------------
function reaction(i, dark) {
  return `<button class="reaction ${i === state.selectedClient ? "active" : ""}" data-action="react" data-client="${i}" aria-label="${state.clients[i].name}: add leaf reaction"><canvas width="65" height="27" data-paint="${i}" data-dark="${dark}" data-x="52" data-y="135" aria-hidden="true"></canvas><span class="emoji">🌱</span><span data-reaction-count="${i}">${state.clients[i].reactions}</span></button>`;
}
function contextClient(i, dark) {
  const c = state.clients[i], v = verdict(state, kernel);
  return `<div class="client-window ${dark ? "dark-client" : ""}" data-client-window="${i}"><canvas width="304" height="398" data-paint="${i}" data-dark="${dark}" aria-hidden="true"></canvas><div class="client-content"><div class="client-header"><div><strong>Quiet</strong><div class="meta">2 members</div></div><a href="${previewHref("settings.appearance")}" aria-label="Open settings">${icon("gear")}</a></div><div class="msg"><a class="avatar" href="${previewHref("profile")}" aria-label="Maya profile">M</a><div class="msg-body"><div class="msg-meta"><a href="${previewHref("profile")}"><strong>Maya</strong></a><time>10:42</time></div><p>The next build is ready to try.</p>${reaction(i, dark)}</div></div><div class="msg second"><span class="avatar">R</span><div class="msg-body"><div class="msg-meta"><strong>Rowan</strong><time>10:43</time></div><p>Testing the reaction sync now.</p><a class="reaction" href="${previewHref("emoji")}" aria-label="Explore emoji component"><span class="emoji">✨</span><span>1</span></a></div></div>${v !== 1 ? `<div class="pending-banner">${icon(v === 0 ? "clock" : "shield")}<span>${v === 0 ? "Incoming reaction is waiting for its message." : "Incoming reaction rejected."}</span></div>` : c.messages.length ? `<div class="sent-message">${esc(c.messages.at(-1))}</div>` : ""}<form class="composer" data-composer="${i}"><input aria-label="${c.name} message draft" placeholder="Message" value="${esc(c.draft)}" data-draft="${i}"><button type="submit" aria-label="Send as ${c.name}">${icon("arrow")}</button></form></div></div>`;
}
function component(id, i, dark) {
  const c = state.clients[i];
  let body;
  if (id === "message.reaction") body = reaction(i, dark);
  else if (id === "message") body = `<article class="message-fragment"><a class="avatar" href="${previewHref("profile")}" aria-label="Maya profile">M</a><div class="msg-body"><div class="msg-meta"><a href="${previewHref("profile")}"><strong>Maya</strong></a><time>10:42</time></div><p>The next build is ready to try.</p>${reaction(i, dark)}</div></article>`;
  else if (id === "message.draft") body = `<form class="draft-fragment" data-composer="${i}"><input aria-label="${c.name} message draft" placeholder="Message" value="${esc(c.draft)}" data-draft="${i}"><button class="icon-btn" type="submit" aria-label="Send as ${c.name}">${icon("arrow")}</button></form>`;
  else if (id === "settings.appearance") body = `<div class="appearance-fragment"><select data-theme="${i}" aria-label="Appearance">${["System", "Light", "Dark"].map((l, v) => `<option value="${v}" ${c.preference === v ? "selected" : ""}>${l}</option>`).join("")}</select><button class="btn small" data-action="os">OS: ${state.osDark ? "dark" : "light"}</button></div>`;
  else if (id === "profile") body = `<div class="profile-preview"><div class="avatar-large">M</div><h2>Maya Chen</h2></div>`;
  else if (id === "emoji") {
    const q = state.emojiSearch.toLowerCase();
    const list = sourceIndex.catalog.filter(e => !q || `${e.label} ${e.tags} ${e.emoji}`.toLowerCase().includes(q));
    body = `<div class="emoji-preview"><input data-emoji-search aria-label="Search emoji" placeholder="Search emoji" value="${esc(state.emojiSearch)}"><div class="emoji-grid">${list.slice(0, 56).map(e => `<button class="emoji-tile" data-action="emoji" data-emoji="${esc(e.emoji)}" aria-label="${esc(e.label)}" title="${esc(e.label)}" aria-pressed="${state.selectedEmoji === e.emoji}">${e.emoji}</button>`).join("")}</div>${list.length ? "" : "<p>No matching entries.</p>"}</div>`;
  } else if (id === "sync") body = `<div class="sync-preview"><span>${state.queue.filter(d => d.to === i).length} incoming</span><a href="#/network">network →</a></div>`;
  else return contextClient(i, dark);
  return `<div class="client-window specimen ${dark ? "dark-client" : ""}" data-component="${id}" data-client-window="${i}">${body}</div>`;
}
function sceneControls(id) {
  if (!["app", "message", "message.reaction"].includes(id) && !isNetwork()) return "";
  return `<div class="fixture-bar"><select id="scenario" aria-label="Scenario">${Object.entries(scenarios).map(([k, s]) => `<option value="${k}" ${state.scenario === k ? "selected" : ""}>${s.label}</option>`).join("")}</select><div class="transport">${isNetwork() ? `<button class="btn small" data-action="pause" aria-label="${state.paused ? "Resume" : "Pause"} delivery">${state.paused ? "Resume" : "Pause"}</button>` : ""}<button class="icon-btn" data-action="reset" aria-label="Reset scenario">${icon("refresh")}</button></div></div>${state.scenario === "missing" ? '<button class="source-link resolve-link" data-action="resolve">Deliver missing message →</button>' : ""}`;
}
function previewSection(id) {
  const stage = isNetwork()
    ? state.clients.map((c, i) => `<div class="client-wrap"><div class="client-label"><strong>${c.name}</strong><button class="source-link" data-action="open-client" data-client="${i}">Open app →</button><select aria-label="${c.name} appearance" data-theme="${i}">${["System", "Light", "Dark"].map((x, n) => `<option value="${n}" ${c.preference === n ? "selected" : ""}>${x}</option>`).join("")}</select></div>${contextClient(i, kernel.quiet_theme(c.preference, state.osDark))}</div>`).join("")
    : `<div class="client-wrap theme-pair ${id === "app" ? "app-pair" : ""}">${[0, 1].map(dark => `<div class="theme-preview ${dark ? "dark-preview" : "light-preview"}" data-preview-theme="${dark ? "dark" : "light"}" role="group" aria-label="${dark ? "Dark" : "Light"} preview">${component(id, state.selectedClient, dark)}</div>`).join("")}</div>`;
  return `${sceneControls(id)}<section class="component-preview ${isNetwork() ? "network-preview" : "paired-preview"}" aria-label="Live component previews"><div class="preview-stage">${stage}</div></section>${stateDetails(id)}${kernelDetails(id)}`;
}
function stateRows(id) {
  const fixture = scenarios[state.scenario], c = state.clients[state.selectedClient];
  if (isNetwork()) return [["delivery", state.paused ? "paused" : "running"], ["queue", JSON.stringify(state.queue, null, 2)], ...state.clients.flatMap(c => [[`${c.name}.reactions`, c.reactions], [`${c.name}.draft`, c.draft || "∅"]])];
  if (id === "emoji") { const e = sourceIndex.catalog.find(e => e.emoji === state.selectedEmoji) || sourceIndex.catalog[0]; return [["emoji", e.emoji], ["name", e.label], ["code points", [...e.emoji].map(ch => "U+" + ch.codePointAt(0).toString(16).toUpperCase()).join(" ")], ["catalogue", `${sourceIndex.catalog.length} entries`]]; }
  if (id === "settings.appearance") return [["preference", ["system", "light", "dark"][c.preference]], ["osDark", state.osDark], ["theme", kernel.quiet_theme(c.preference, state.osDark)]];
  if (id === "message.draft") return [["draft", c.draft || "∅"], ["sent", JSON.stringify(c.messages)]];
  if (id === "sync") return [["incoming", JSON.stringify(state.queue.filter(d => d.to === state.selectedClient), null, 2)]];
  if (id === "profile") return [["name", "Maya Chen"]];
  return [...(id === "message.reaction" ? [["result", ["Waiting for dependency", "Reaction accepted", "Reaction rejected"][verdict(state, kernel)]], ["message.community", fixture.same ? "same" : "another"], ["author.member", !!fixture.member]] : []), ["message.available", !!fixture.present], ["message.valid", !!fixture.valid], ["reaction.count", c.reactions], ...(id === "app" ? [["draft", c.draft || "∅"]] : [])];
}
function stateDetails(id) {
  const rows = stateRows(id);
  const log = state.log.slice(0, 7).map(l => `<div class="trace-row ${l.kind}"><span class="number">${String(l.id).padStart(2, "0")}</span><span>${esc(l.text)}</span></div>`).join("");
  return `<details class="document-section state-details" data-detail="state" id="state-section"><summary>State</summary><table class="op-table"><tbody>${rows.map(([k, v]) => `<tr><th scope="row"><code>${esc(k)}</code></th><td><pre>${esc(v)}</pre></td></tr>`).join("")}</tbody></table>${isNetwork() && state.queue.length ? `<div class="row"><span class="queue-number">${state.queue.length} queued</span><button class="btn small" data-action="deliver">${icon("play")}Deliver next</button></div>` : ""}<div class="trace">${log || '<div class="empty">No events</div>'}</div><p class="layout-note">${esc(previewDocs[isNetwork() ? "network" : id]?.gap || "")}</p></details>`;
}
// The preview's validator, compiled from Lean to WASM: edit it and check it in the browser.
function kernelDetails(id) {
  const target = previewDocs[id]?.target;
  if (!target) return "";
  const draft = state.definitionDrafts[target];
  const list = proofs.filter(p => p.target === target);
  return `<details class="document-section kernel-details" data-detail="kernel" id="source-section"><summary>Workspace.${target}</summary>` +
    `<p class="source-origin"><a href="${sourceHref("tools/workspace/lean/Kernel.lean")}">tools/workspace/lean/Kernel.lean</a> · compiled to WASM · <code>${evidence.sourceSha256.slice(0, 12)}</code> <span id="source-badge">${draft !== undefined ? "· unbuilt draft" : ""}</span></p>` +
    `${codeEditor("source-editor", `Lean ${target} definition`, draft ?? definitionRange(kernelSource, target).text, proofSession.busy)}` +
    `<div class="source-actions row wrap"><button class="btn" data-action="check-source" ${proofSession.busy ? "disabled" : ""}>${proofSession.busy ? "Checking…" : "Check definition & proofs"}</button><button class="btn" data-action="restore-source">Restore</button>${proofSession.busy ? '<button class="btn" data-action="cancel-proof">Cancel</button>' : ""}</div><pre id="source-output" role="status">${esc(proofSession.output)}</pre>` +
    `<div class="proof-group"><div class="assumptions"><h4>Assumed:</h4><p><a href="#/about/assumptions">Standard assumptions</a>. Fixture inputs stand in for the facts.</p></div><div class="proven"><h4>Proven:</h4><div class="check-list">${list.map(p => `<details class="check" data-detail="kernel/${p.id}"><summary class="check-title"><code>${p.name}</code></summary><p class="proof-description">${esc(p.description)}</p>${codeBlock(p.code)}<div class="check-links"><a href="#/proofs/${p.id}">Explore proof →</a>${p.threat ? `<a href="#/threats/${p.threat}">${p.threat} →</a>` : ""}</div></details>`).join("")}</div></div></div></details>`;
}

// ---- Op documents --------------------------------------------------------------
function identityLine(node) {
  if (node.path === "app") return "";
  const bits = [node.planned ? `planned ${node.kind}` : node.kind];
  if (node.planned && node.planned !== "family") bits.push(esc(node.planned));
  if (node.tag !== undefined) bits.push(`tag ${node.tag}`);
  return `<div class="operation-identity">${bits.join("<span>·</span>")}</div>`;
}
function opIndex(node) {
  const kids = tree.children(node.path).filter(e => e.kind === "dir");
  if (!kids.length) return "";
  const row = (e, depth = 0) => {
    const n = tree.nodes.get(e.path), sub = tree.children(e.path).filter(k => k.kind === "dir");
    return `<li><div class="operation-row ${n.planned ? "planned" : ""} ${n.kind === "op" ? "op" : ""}" style="--depth:${depth}" data-op-owner="${esc(e.path)}"><a href="${href(e.path)}"><code>${esc(e.name)}/</code></a><span>${esc(n.summary || "")}</span></div>${sub.length ? `<ul>${sub.map(k => row(k, depth + 1)).join("")}</ul>` : ""}</li>`;
  };
  return `<section class="document-section operation-index"><h2>${node.path === "app" ? "Ops" : "Nested ops"}</h2><ul>${kids.map(k => row(k)).join("")}</ul></section>`;
}
function fileBody(node, role) {
  const path = `${node.path}/${role}`, file = plan.files[path];
  if (file) return fileCode(path, file);
  const tests = role === "Tests.lean" ? node.tests : [];
  return `<p class="planned-note">Planned.${tests.length ? " Today these import this folder:" : ""}</p>${tests.length ? `<div class="component-links">${tests.map(t => `<a href="${sourceHref(t)}"><code>${esc(t)}</code></a>`).join("")}</div>` : ""}`;
}
function fileSection(node, role) {
  return `<section class="document-section file-section" id="file-${role.replace(".", "-")}"><div class="section-heading"><h2><a href="${href(`${node.path}/${role}`)}">${role}</a></h2></div>${fileBody(node, role)}</section>`;
}
function folderPage(node) {
  const id = previewOf(node.path), isRoot = node.path === "app";
  const sections = node.files.map(f => fileSection(node, f)).join("");
  return `<div class="heading op-heading"><h1>${canonical(node.path).split(".").map(esc).join(".<wbr>")}</h1>${isRoot ? `<div class="root-actions"><a href="#/network">network</a><a href="/op-tree.txt" download>op-tree.txt</a></div>` : ""}</div>` +
    `<div class="op-document">${identityLine(node)}<p class="doc-summary">${esc(node.summary || "")}</p>${id ? previewSection(id) : ""}` +
    `${node.kind === "op" ? sections + opIndex(node) : opIndex(node) + sections}</div>`;
}
// A file page: what the file holds, then the file. Proofs.lean lists its laws first.
function filePage(entry) {
  const node = entry.node, id = previewOf(node.path), file = entry.file;
  const list = file && entry.name === "Proofs.lean" ? laws(file.text) : [];
  const lawIndex = list.length ? `<details class="document-section law-list" data-detail="laws:${esc(entry.path)}"><summary>${list.length} laws</summary><div class="component-links">${list.map(l => `<a href="${href(entry.path, l.line)}"><code>${esc(l.name)}</code></a>`).join("")}</div></details>` : "";
  return `<div class="heading op-heading"><h1>${esc(entry.name)}</h1><a href="${href(node.path)}">${esc(canonical(node.path))} →</a></div>` +
    `<div class="op-document"><p class="doc-summary">${esc(plan.roles[entry.name])}</p>${entry.name === "View.lean" && id ? previewSection(id) : ""}` +
    `${file ? lawIndex + sourceLines(entry.path, file.text, route.line) : fileBody(node, entry.name)}</div>`;
}
// engine/ and platforms/: folders list their files; a file shows its source.
// An engine file that imports the app is marked (LAYOUT06).
const importsApp = info => info.path.startsWith("engine/") && info.importsApp.length ? info.importsApp : [];
function outsideFolderPage(entry) {
  const note = tree.nodes.get(entry.path), id = note?.preview;
  const row = k => `<a href="${href(k.path)}"><code>${esc(k.name)}${k.kind === "dir" ? "/" : ""}</code><span>${k.info ? [`${k.info.lines} lines`, importsApp(k.info).length ? `imports the app: ${importsApp(k.info).map(esc).join(", ")}` : ""].filter(Boolean).join(" · ") : ""}</span></a>`;
  return `<div class="heading op-heading"><h1>${esc(entry.path)}/</h1></div><div class="op-document"><p class="doc-summary">${esc(note?.summary || "")}</p>${id ? previewSection(id) : ""}<div class="directory-list">${tree.children(entry.path).map(row).join("")}</div></div>`;
}
function outsideFilePage(entry) {
  const m = importsApp(entry.info);
  return sourcePage(entry.path, route.line, m.length ? `<p class="imports-app">Imports the app: ${m.map(x => `<code>${esc(x)}</code>`).join(", ")}</p>` : "");
}
function sourcePage(path, line, note = "") {
  const text = plan.files[path]?.text ?? sourceIndex.files[path]?.text ?? sourceCache.get(path);
  if (text === undefined) { loadSource(path); return `<div class="heading op-heading"><h1>${esc(path)}</h1></div><p class="layout-note">Loading…</p>`; }
  if (text === null) return `<div class="heading op-heading"><h1>${esc(path)}</h1></div><p>Source unavailable.</p>`;
  return `<div class="heading op-heading"><h1>${esc(path)}</h1></div>${note}${sourceLines(path, text, line)}`;
}
async function loadSource(path) {
  if (sourceCache.has(path)) return;
  sourceCache.set(path, undefined);
  let text = null;
  try { const r = await fetch("/src/" + path.split("/").map(encodeURIComponent).join("/")); if (r.ok) text = await r.text(); } catch {}
  sourceCache.set(path, text);
  render(); scrollToSection();
}

// ---- Kernel proofs, threats, assumptions -------------------------------------------
function proofPage() {
  const p = proofs.find(p => p.id === route.id);
  if (!p) return `<div class="heading"><h1>Kernel proofs</h1></div><div class="proof-list">${proofs.map(p => `<a class="proof-card" href="#/proofs/${p.id}"><code>${p.name}</code><p>${esc(p.description)}</p></a>`).join("")}</div>`;
  const draft = state.proofDrafts[p.id] ?? "", home = p.target === "theme" ? "settings.appearance" : "message.reaction";
  return `<div class="heading"><div><h1>${p.title}</h1><p>${p.description}</p></div></div><div class="op-document"><div class="proof-goal"><div class="goal-label">Goal</div>${codeBlock(p.goal)}</div><div class="proof-tactics"><h3>Tactics</h3>${codeEditor("proof-editor", "Lean proof tactics", draft, proofSession.busy)}<div class="row wrap" style="margin-top:12px"><button class="btn primary" data-action="check-proof" ${proofSession.busy ? "disabled" : ""}>${icon("play")}${proofSession.busy ? "Checking…" : proofSession.loaded ? "Check proof" : "Load Lean & check"}</button><button class="btn" data-action="hint">${icon("leaf")}Hint</button><button class="btn ghost" data-action="solution">Try the solution</button>${proofSession.busy ? '<button class="btn small" data-action="cancel-proof">Cancel</button>' : ""}</div>${proofSession.hint ? `<div class="hint">${p.hint}</div>` : ""}<div class="proof-output" id="proof-output" role="status">${esc(proofSession.output || "Load Lean to check locally. About 310 MiB on first use.")}</div></div><details class="scope-note"><summary>Checked proof</summary>${codeBlock(p.code)}</details><ol class="levels">${proofs.map(q => `<li><a href="#/${route.section}/${q.id}" ${q.id === p.id ? 'aria-current="page"' : ""}>${esc(q.title)}</a></li>`).join("")}</ol><div class="component-links"><a href="${previewHref(home)}">${esc(canonical(tree.previews[home]))} →</a>${p.threat ? `<a href="#/threats/${p.threat}">${p.threat} →</a>` : ""}</div></div>`;
}
function threatPage() {
  const t = threats.find(t => t.id === route.id);
  const docs = `<div class="component-links"><a href="${sourceHref("docs/security/auditician/THREATMODEL.md")}">Auditician threat model →</a><a href="${sourceHref("docs/security/auditician/ICTM-REVIEW-DECISIONS.md")}">Review decisions →</a></div>`;
  if (!t) return `<div class="heading"><h1>Threat model</h1></div>${docs}<div class="proof-list">${threats.map(t => `<a class="proof-card" href="#/threats/${t.id}"><code>${t.id} · ${t.title}</code><p>${t.summary}</p><p>${esc(t.status)}</p></a>`).join("")}</div>`;
  return `<div class="heading"><div><h1>${t.id} · ${t.title}</h1><p>${t.summary}</p></div></div><div class="op-document"><p>${esc(t.status)}</p><h3>Kernel evidence</h3>${t.proofs.length ? t.proofs.map(id => `<a href="#/proofs/${id}"><code>${id}</code></a>`).join("<br>") : "<p>None.</p>"}<h3>Open</h3><ul>${t.gaps.map(g => `<li>${esc(g)}</li>`).join("")}</ul>${docs}</div>`;
}
function assumptionsPage() {
  return `<div class="heading"><h1>Standard assumptions</h1></div><div class="op-document assumptions-document"><dl><dt>Lean kernel and axioms</dt><dd>Lean checks every theorem. <code>tests/Axioms.lean</code> audits that main's laws use only the standard axioms. The workspace build rejects <code>sorryAx</code>.</dd><dt>Compilation</dt><dd>Lean's C backend, Clang's WASM output and the browser preserve the checked definitions. Native/WASM parity tests are evidence, not a proof.</dd><dt>Cryptography</dt><dd>Signatures are a parameter (<code>Crypto</code>). What unforgeability buys is stated as a hypothesis where it is used.</dd><dt>Host integration</dt><dd>The platform seam, the DOM, storage and sockets are outside the proofs.</dd></dl><div class="component-links"><a href="/evidence.json">Build evidence →</a><a href="#/threats/all">Threat model →</a></div></div>`;
}

// ---- Render -----------------------------------------------------------------------
function page() {
  if (route.section === "proofs" || route.section === "game") return proofPage();
  if (route.section === "threats") return threatPage();
  if (route.section === "about") return assumptionsPage();
  if (route.section === "source") return sourcePage(route.path, route.line);
  if (isNetwork()) return `<div class="heading op-heading"><h1>network</h1></div><div class="op-document">${previewSection("network")}</div>`;
  const entry = tree.entries.get(route.path);
  if (!entry) return `<h1>Not in the tree</h1><p><a href="${href("app")}">app/ →</a></p>`;
  if (entry.outside) return entry.kind === "dir" ? outsideFolderPage(entry) : outsideFilePage(entry);
  return entry.kind === "dir" ? folderPage(entry.node) : filePage(entry);
}
function render() {
  route = parseRoute();
  const navigationChanged = renderedHash !== location.hash;
  if (navigationChanged && route.section === "tree") revealTree(route.path);
  renderedHash = location.hash;
  document.body.classList.toggle("dark", state.shellDark);
  document.querySelector('meta[name="theme-color"]').content = state.shellDark ? "#000000" : "#ffffff";
  const content = page();
  const focus = document.activeElement, focusId = focus?.id, caret = focus?.selectionStart, scroll = window.scrollY;
  const draftFocus = focus?.dataset?.draft !== undefined ? [focus.dataset.draft, [...document.querySelectorAll(`[data-draft="${focus.dataset.draft}"]`)].indexOf(focus)] : null;
  document.querySelectorAll("details[data-detail]").forEach(e => { if (e.open) expandedDetails.add(e.dataset.detail); else expandedDetails.delete(e.dataset.detail); });
  $("#app").innerHTML = `${sidebar()}<main class="main" id="main">${breadcrumbs()}${content}</main><footer class="statusbar"><a href="#/about/assumptions">Lean WASM</a>${isNetwork() ? `<span>${state.queue.length} queued</span>` : ""}<span class="right">${plan.revision.slice(0, 9)}</span></footer>`;
  document.querySelectorAll("details[data-detail]").forEach(e => { if (expandedDetails.has(e.dataset.detail)) e.open = true; if (e.open && e.dataset.file) fillFile(e); });
  paint(); bind();
  if (navigationChanged) document.querySelector(".file-tree [aria-current]")?.scrollIntoView({block: "nearest"});
  if (focusId && document.getElementById(focusId)) { const e = document.getElementById(focusId); e.focus({preventScroll: true}); if (caret != null && e.setSelectionRange) try { e.setSelectionRange(caret, caret); } catch {} }
  else if (draftFocus) document.querySelectorAll(`[data-draft="${draftFocus[0]}"]`)[draftFocus[1]]?.focus({preventScroll: true});
  window.scrollTo(0, scroll);
}
function paint() {
  document.querySelectorAll("[data-paint]").forEach(canvas => {
    const dark = Number(canvas.dataset.dark), ctx = canvas.getContext("2d"), w = canvas.width, h = canvas.height;
    const frame = ctx.createImageData(w, h);
    for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
      const c = kernel.quiet_pixel(x + +(canvas.dataset.x || 0), y + +(canvas.dataset.y || 0), dark, state.accent), o = (y * w + x) * 4;
      frame.data[o] = (c >>> 16) & 255; frame.data[o + 1] = (c >>> 8) & 255; frame.data[o + 2] = c & 255; frame.data[o + 3] = 255;
    }
    ctx.putImageData(frame, 0, 0);
  });
}
function bind() {
  document.querySelectorAll("[data-action]").forEach(b => b.addEventListener("click", () => handle(b.dataset.action, b.dataset)));
  $("#scenario")?.addEventListener("change", e => dispatch({type: "scenario", value: e.target.value}));
  document.querySelectorAll("[data-theme]").forEach(e => e.addEventListener("change", () => dispatch({type: "theme", client: +e.dataset.theme, value: e.value})));
  document.querySelectorAll("[data-draft]").forEach(e => e.addEventListener("input", () => {
    dispatch({type: "draft", client: +e.dataset.draft, value: e.value}, false);
    document.querySelectorAll(`[data-draft="${e.dataset.draft}"]`).forEach(peer => { if (peer !== e) peer.value = e.value; });
  }));
  document.querySelectorAll("[data-composer]").forEach(e => e.addEventListener("submit", ev => { ev.preventDefault(); dispatch({type: "send", client: +e.dataset.composer}); }));
  $("#nav-search")?.addEventListener("input", e => { search = e.target.value; render(); });
  document.querySelectorAll("[data-emoji-search]").forEach(i => i.addEventListener("input", e => dispatch({type: "emoji-search", value: e.target.value})));
  document.querySelectorAll(".highlight-editor textarea").forEach(ed => {
    ed.addEventListener("input", () => refreshEditor(ed));
    ed.addEventListener("scroll", () => { ed.previousElementSibling.scrollTop = ed.scrollTop; ed.previousElementSibling.scrollLeft = ed.scrollLeft; });
  });
  $("#source-editor")?.addEventListener("input", e => {
    dispatch({type: "definition", name: previewDocs[previewOf(route.path)].target, value: e.target.value}, false);
    $("#source-badge").textContent = "· unbuilt draft";
    proofSession.output = "Draft changed. Earlier checks apply to the earlier version.";
    $("#source-output").textContent = proofSession.output;
  });
  $("#proof-editor")?.addEventListener("input", e => { state.proofDrafts[route.id] = e.target.value; proofSession.output = "Draft changed."; if ($("#proof-output")) $("#proof-output").textContent = proofSession.output; persist(); });
  document.querySelectorAll("details[data-file]").forEach(d => d.addEventListener("toggle", () => { if (d.open) fillFile(d); }));
}
async function handle(action, data) {
  switch (action) {
    case "tree-toggle": expandedTree.has(data.path) ? expandedTree.delete(data.path) : expandedTree.add(data.path); render(); break;
    case "menu": mobileOpen = !mobileOpen; render(); break;
    case "shell-theme": state.shellDark = !state.shellDark; persist(); render(); break;
    case "reset": dispatch({type: "scenario", value: state.scenario}); toast("Scenario reset"); break;
    case "pause": case "deliver": case "resolve": case "os": dispatch({type: action}); break;
    case "react": dispatch({type: "react", client: +data.client}); break;
    case "open-client": dispatch({type: "client", client: +data.client}, false); history.pushState(null, "", href("app")); routeChanged(); break;
    case "emoji": dispatch({type: "emoji", value: data.emoji}); break;
    case "restore-source": delete state.definitionDrafts[previewDocs[previewOf(route.path)].target]; proofSession.output = ""; persist(); render(); break;
    case "hint": proofSession.hint = !proofSession.hint; render(); break;
    case "solution": { const p = proofs.find(p => p.id === route.id); state.proofDrafts[p.id] = p.tactic; persist(); render(); break; }
    case "check-proof": case "check-source": await checkLean(action === "check-source"); break;
    case "cancel-proof": await cancelLean(); break;
  }
}

// ---- The browser prover ---------------------------------------------------------------
let proverModule;
async function cancelLean() {
  proofSession.job++; proverModule?.cancel();
  Object.assign(proofSession, {busy: false, loaded: false, output: "Cancelled."});
  render();
}
async function checkLean(fullSource) {
  if (proofSession.busy) return;
  const job = ++proofSession.job, p = proofs.find(p => p.id === route.id), tactics = state.proofDrafts[p?.id] || "";
  if (!fullSource && !tactics.trim()) { toast("Write a tactic, ask for a hint, or try the solution first."); return; }
  const target = fullSource && previewDocs[previewOf(route.path)].target;
  const text = fullSource
    ? replaceDefinition(kernelSource, target, state.definitionDrafts[target] ?? definitionRange(kernelSource, target).text)
    : kernelSource.slice(0, kernelSource.indexOf("theorem waits_for_dependency")) + p.code.replace(/:= by[\s\S]*/, ":= by\n  " + tactics.split("\n").join("\n  ")) + "\nend Workspace\n#print axioms Workspace." + p.name;
  Object.assign(proofSession, {busy: true, output: "Preparing the browser prover…"});
  render();
  try {
    proverModule ??= await import("./prover.js");
    const result = await proverModule.check(text, msg => { if (job !== proofSession.job) return; proofSession.output = msg; const el = $("#proof-output") || $("#source-output"); if (el) el.textContent = msg; });
    if (job !== proofSession.job) return;
    proofSession.loaded = true;
    const raw = [result.stdout, result.stderr].filter(Boolean).join("\n");
    const output = result.stdout.split("\n").map(line => { try { const d = JSON.parse(line); return `${d.severity || "info"}${d.pos ? " · line " + d.pos.line : ""}: ${d.data || line}`; } catch { return line; } }).filter(Boolean).join("\n")
      || result.stderr.split("\n").filter(l => !l.startsWith("[DEBUG:") && !l.startsWith("wasm streaming") && !l.startsWith("falling back")).join("\n");
    const unsound = /sorryAx|declaration uses ['‘]sorry|declaration uses.*sorry/.test(raw);
    proofSession.status = result.exitCode === 0 && !unsound ? "success" : "error";
    proofSession.output = (proofSession.status === "success" ? "Lean accepted the proof.\n\n" : "Lean did not establish this proof.\n\n") + output + (unsound ? "\nA proof containing sorry is incomplete." : "");
  } catch (e) {
    if (job !== proofSession.job) return;
    proofSession.output = "Browser prover: " + e.message;
  } finally {
    if (job === proofSession.job) { proofSession.busy = false; render(); }
  }
}
function routeChanged() {
  if (location.hash === renderedHash) return;
  if (proofSession.busy) { proofSession.job++; proverModule?.cancel(); proofSession.busy = false; proofSession.loaded = false; }
  mobileOpen = false; proofSession.hint = false; proofSession.output = "";
  render(); scrollToSection();
}
function scrollToSection() {
  const target = route.line ? document.getElementById("line-" + route.line) : null;
  if (target) target.scrollIntoView({block: "center"}); else window.scrollTo(0, 0);
}
window.addEventListener("hashchange", routeChanged);
window.addEventListener("popstate", routeChanged);
document.addEventListener("click", event => {
  if (event.button !== 0 || event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) return;
  const link = event.target.closest?.('a[href^="#/"]');
  if (!link) return;
  event.preventDefault();
  const to = link.getAttribute("href");
  if (to !== location.hash) history.pushState(null, "", to);
  routeChanged();
});
window.addEventListener("keydown", e => {
  if (e.key === "/" && !["INPUT", "TEXTAREA", "SELECT"].includes(document.activeElement.tagName)) { e.preventDefault(); mobileOpen = true; render(); $("#nav-search").focus(); }
  if (e.key === "Escape" && mobileOpen) { mobileOpen = false; render(); }
});

const sha256 = async bytes => Array.from(new Uint8Array(await crypto.subtle.digest("SHA-256", bytes)), x => x.toString(16).padStart(2, "0")).join("");
async function init() {
  try {
    await highlightingReady;
    if (saved.shellDark === undefined) state.shellDark = matchMedia("(prefers-color-scheme: dark)").matches;
    const get = (url, kind) => fetch(url).then(r => { if (!r.ok) throw Error(`${url} unavailable`); return r[kind](); });
    const [bytes, ev, src, indexBytes, planBytes] = await Promise.all([get("/kernel.wasm", "arrayBuffer"), get("/evidence.json", "json"), get("/Kernel.lean", "text"), get("/sources.json", "arrayBuffer"), get("/plan.json", "arrayBuffer")]);
    if (await sha256(bytes) !== ev.wasmSha256) throw Error("WASM evidence hash mismatch");
    if (await sha256(new TextEncoder().encode(src)) !== ev.sourceSha256) throw Error("Lean source evidence hash mismatch");
    if (await sha256(indexBytes) !== ev.sourceIndexSha256) throw Error("Source index evidence hash mismatch");
    if (await sha256(planBytes) !== ev.planSha256) throw Error("Plan evidence hash mismatch");
    kernel = (await WebAssembly.instantiate(bytes)).instance.exports;
    evidence = ev; kernelSource = src;
    sourceIndex = JSON.parse(new TextDecoder().decode(indexBytes));
    plan = JSON.parse(new TextDecoder().decode(planBytes));
    tree = index(plan);
    const media = matchMedia("(prefers-color-scheme: dark)");
    state.osDark = media.matches ? 1 : 0;
    media.addEventListener("change", e => { state.osDark = e.matches ? 1 : 0; render(); });
    if (!location.hash) history.replaceState(null, "", href("app"));
    render(); scrollToSection();
    window.__quiet = {getState: () => structuredClone(state), kernel, evidence, plan};
  } catch (e) {
    $("#app").innerHTML = `<div class="loading"><div><h1>Could not open the workspace</h1><p>${esc(e.message)}</p></div></div>`;
    console.error(e);
  }
}
init();

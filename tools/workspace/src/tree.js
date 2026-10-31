// The project tree, from the plan main's sources produce (tools/plan.py).
// Pure: the page and the tests both use it.
export const ORDER = ['Op.lean', 'Validate.lean', 'View.lean', 'Commands.lean', 'Screen.lean', 'Proofs.lean', 'Tests.lean', 'Family.lean'];
export const ROOTS = ['app', 'engine', 'platforms'];
export const parentOf = path => path.includes('/') ? path.slice(0, path.lastIndexOf('/')) : null;

export function index(plan) {
  const nodes = new Map(plan.nodes.map(n => [n.path, n]));
  const entries = new Map();
  const put = e => { if (!entries.has(e.path)) entries.set(e.path, e); };
  for (const n of plan.nodes) {
    put({path: n.path, name: n.name, kind: 'dir', node: n});
    for (const f of n.files) put({path: `${n.path}/${f}`, name: f, kind: 'file', node: n, role: f,
      planned: !plan.fragments[`${n.path}/${f}`]});
  }
  for (const info of [...plan.engine, ...plan.platforms]) {
    const parts = info.path.split('/');
    for (let i = 1; i < parts.length; i++) put({path: parts.slice(0, i).join('/'), name: parts[i - 1], kind: 'dir', outside: true});
    put({path: info.path, name: parts.at(-1), kind: 'file', outside: true, info});
  }
  const kids = new Map();
  for (const e of entries.values()) {
    const p = parentOf(e.path);
    if (p === null) continue;
    if (!kids.has(p)) kids.set(p, []);
    kids.get(p).push(e);
  }
  const rank = e => e.kind === 'dir' ? -1 : ORDER.includes(e.name) ? ORDER.indexOf(e.name) : 100;
  for (const list of kids.values()) list.sort((a, b) => rank(a) - rank(b) || a.name.localeCompare(b.name, 'en'));
  const children = path => kids.get(path) || [];
  const opsUnder = path => plan.nodes.filter(n => n.kind === 'op' && (n.path === path || n.path.startsWith(path + '/')));
  const previews = Object.fromEntries(plan.nodes.filter(n => n.preview).map(n => [n.preview, n.path]));
  return {nodes, entries, children, opsUnder, previews};
}

export const href = path => '#/tree/' + path.split('/').map(encodeURIComponent).join('/');
export const sourceHref = (path, line = 1) => `#/source/${encodeURIComponent(path)}/${line}`;
export const canonical = path => path === 'app' ? 'app' : path.startsWith('app/') ? path.slice(4).replaceAll('/', '.') : path;

export function identity(node) {
  const op = node.op;
  if (node.planned) return {kind: 'planned', scope: node.planned};
  if (!op) return null;
  if (op.family === 'sync') return {kind: 'op', tag: op.kind, scope: 'never stored'};
  return {kind: 'op', family: op.family, body: op.body, facts: op.facts};
}

// Where each of main's files goes, folded by target folder.
export function movesByFolder(plan) {
  const out = new Map();
  for (const [source, targets] of Object.entries(plan.moves)) for (const t of targets || []) {
    const folder = parentOf(t);
    if (!out.has(folder)) out.set(folder, new Set());
    out.get(folder).add(source);
  }
  return out;
}

export function treeText(plan) {
  const {children, nodes} = index(plan);
  const lines = ['app/'];
  const visit = (path, indent) => children(path).forEach((e, i, list) => {
    const last = i === list.length - 1;
    if (e.kind === 'dir') {
      lines.push(`${indent}${last ? '└── ' : '├── '}${e.name}/${nodes.get(e.path)?.planned ? '   (planned op)' : ''}`);
      visit(e.path, indent + (last ? '    ' : '│   '));
    } else lines.push(`${indent}${last ? '└── ' : '├── '}${e.name}${e.planned ? '   (planned)' : ''}`);
  });
  visit('app', '');
  return lines;
}

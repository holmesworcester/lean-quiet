// The project tree, from the plan of the tree on disk (tools/plan.py).
// Pure: the page and the tests both use it.
export const ORDER = ['Op.lean', 'Validate.lean', 'View.lean', 'Commands.lean', 'Screen.lean', 'Proofs.lean', 'Tests.lean', 'Family.lean'];
export const ROOTS = ['app', 'engine', 'platforms'];
export const parentOf = path => path.includes('/') ? path.slice(0, path.lastIndexOf('/')) : null;

export function index(plan) {
  const nodes = new Map([...plan.notes, ...plan.nodes].map(n => [n.path, n]));
  const entries = new Map();
  const put = e => { if (!entries.has(e.path)) entries.set(e.path, e); };
  for (const n of plan.nodes) {
    put({path: n.path, name: n.name, kind: 'dir', node: n});
    for (const f of n.files) {
      const path = `${n.path}/${f}`;
      put({path, name: f, kind: 'file', node: n, file: plan.files[path], planned: !plan.files[path]});
    }
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
  const previews = Object.fromEntries([...nodes.values()].filter(n => n.preview).map(n => [n.preview, n.path]));
  return {nodes, entries, children, previews};
}

// A file route may end in a line: #/tree/app/x/Proofs.lean/120.
export const href = (path, line = 0) => '#/tree/' + path.split('/').map(encodeURIComponent).join('/') + (line ? `/${line}` : '');
export const sourceHref = (path, line = 1) => `#/source/${encodeURIComponent(path)}/${line}`;
export const canonical = path => path === 'app' ? 'app' : path.startsWith('app/') ? path.slice(4).replaceAll('/', '.') : path;

// The laws a file states, with their lines.
export const laws = text => text.split('\n').flatMap((l, i) => {
  const m = /^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|nonrec)\s+)*(?:theorem|lemma)\s+([^\s:({[]+)/.exec(l);
  return m ? [{name: m[1], line: i + 1}] : [];
});

export function treeText(plan) {
  const {children, nodes} = index(plan);
  const lines = ['app/'];
  const visit = (path, indent) => children(path).forEach((e, i, list) => {
    const last = i === list.length - 1, n = nodes.get(e.path);
    if (e.kind === 'dir') {
      lines.push(`${indent}${last ? '└── ' : '├── '}${e.name}/${n.planned ? `   (planned ${n.kind})` : ''}`);
      visit(e.path, indent + (last ? '    ' : '│   '));
    } else lines.push(`${indent}${last ? '└── ' : '├── '}${e.name}${e.planned ? '   (planned)' : ''}`);
  });
  visit('app', '');
  return lines;
}

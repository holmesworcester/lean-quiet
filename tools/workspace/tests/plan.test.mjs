// The op tree is a plan over main's real sources: these check that it loses
// nothing, owns every op once, and places each law where it can see what it names.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { execFileSync } from 'node:child_process';
import { index, treeText, ORDER } from '../src/tree.js';

const repo = new URL('../../../', import.meta.url);
const plan = JSON.parse(await readFile(new URL('dist/plan.json', new URL('../', import.meta.url)), 'utf8'));
const layout = JSON.parse(await readFile(new URL('layout/tree.json', new URL('../', import.meta.url)), 'utf8'));
const tree = index(plan);
const read = path => readFile(new URL(path, repo), 'utf8');
const ancestors = path => { const out = []; for (let p = path; p; p = p.includes('/') ? p.slice(0, p.lastIndexOf('/')) : null) out.push(p); return out; };

test('every Lean file of the app and its op families has a destination in the tree', () => {
  const files = execFileSync('git', ['ls-files', 'ops/*.lean', 'App.lean', 'AppTypes.lean', 'AppLife.lean'], {cwd: repo, encoding: 'utf8'}).split('\n').filter(Boolean);
  assert.ok(files.length > 100);
  for (const f of files) {
    assert.ok(plan.moves[f]?.length, `${f} has no destination`);
    for (const t of plan.moves[f]) assert.ok(t.startsWith('app/') || t.startsWith('engine/'), `${f} → ${t}`);
  }
});

test('the split and placed files lose no line and copy none', async () => {
  const cut = Object.entries(layout.sources).filter(([, r]) => typeof r === 'object').map(([s]) => s);
  assert.ok(cut.includes('ops/community/Facts.lean') && cut.includes('ops/community/Laws.lean'));
  for (const source of cut) {
    const lines = (await read(source)).split('\n');
    const seen = new Array(lines.length + 1).fill(0);
    for (const frs of Object.values(plan.fragments)) for (const fr of frs) if (fr.from === source)
      for (let n = fr.start; n <= fr.end; n++) seen[n]++;
    lines.forEach((line, i) => {
      if (line.trim()) assert.equal(seen[i + 1], 1, `${source}:${i + 1} is placed ${seen[i + 1]} times: ${line}`);
    });
  }
});

test('folders use only the fixed file names, and every op folder has its own', () => {
  for (const n of plan.nodes) {
    for (const f of n.files) assert.ok(ORDER.includes(f), `${n.path}/${f}`);
    if (n.kind === 'op') for (const f of ['Op.lean', 'Validate.lean', 'Proofs.lean', 'Tests.lean']) assert.ok(n.files.includes(f), `${n.path} lacks ${f}`);
    assert.equal(n.files.includes('Family.lean'), n.children.length > 0, `${n.path}: Family.lean iff it has child folders`);
    assert.deepEqual(n.files, ORDER.filter(f => n.files.includes(f)));
  }
  for (const target of Object.keys(plan.fragments)) {
    if (target.startsWith('engine/')) continue;
    assert.ok(tree.entries.get(target)?.kind === 'file', `${target} is not a file in the tree`);
  }
});

test('every op type on main has exactly one folder, holding its constructors and its validator', async () => {
  for (const [family, source] of [['community', 'ops/community/Facts.lean'], ['connection', 'ops/connection/Types.lean']]) {
    const text = await read(source);
    const body = text.slice(text.indexOf('inductive Body where'), text.indexOf('deriving', text.indexOf('inductive Body where')));
    const ctors = [...body.matchAll(/^\s+\| (\w+)/gm)].map(m => m[1]);
    assert.ok(ctors.length >= 8);
    for (const c of ctors) {
      const owners = plan.nodes.filter(n => n.op?.family === family && n.op.body === c);
      assert.equal(owners.length, 1, `${family} Body.${c} has ${owners.length} owners`);
      const op = plan.fragments[`${owners[0].path}/Op.lean`] || [];
      assert.ok(op.some(fr => fr.label === 'Body' && new RegExp(`\\| ${c}\\b`).test(fr.text)), `${owners[0].path}/Op.lean lacks Body.${c}`);
      if (family === 'community') assert.ok((plan.fragments[`${owners[0].path}/Validate.lean`] || []).some(fr => fr.label === 'check'), `${owners[0].path} lacks its check case`);
    }
  }
  const sync = plan.nodes.filter(n => n.op?.family === 'sync').map(n => n.op.kind).sort();
  assert.deepEqual(sync, [240, 241, 242]);
  assert.match(await read('ops/sync/Wire.lean'), /kRbsr : UInt8 := 240[\s\S]*kHave : UInt8 := 241[\s\S]*kWant : UInt8 := 242/);
});

test('a law or command lives where it sees every op it names: its own subtree or what it cites above', () => {
  let checked = 0;
  for (const [target, frs] of Object.entries(plan.fragments)) for (const fr of frs) {
    if (!fr.names) continue;
    const folder = target.slice(0, target.lastIndexOf('/'));
    for (const op of fr.names) {
      const visible = ancestors(folder).includes(op) || op.startsWith(folder + '/');
      assert.ok(visible, `${fr.label} in ${target} names ${op}, which it cannot see`);
    }
    const leaves = fr.names.filter(op => !fr.names.some(o => o !== op && o.startsWith(op + '/')));
    // Not deeper than it must be: a single deepest op is the home; branches meet at their common ancestor.
    if (leaves.length === 1) assert.equal(folder, leaves[0], `${fr.label} should live in ${leaves[0]}`);
    else assert.ok(new Set(leaves.map(op => op.slice(folder.length + 1).split('/')[0])).size >= 2, `${fr.label} in ${target}: branches must meet here, not above`);
    checked++;
  }
  assert.ok(checked > 150, `${checked} placed declarations`);
  const at = name => Object.entries(plan.fragments).filter(([, frs]) => frs.some(fr => fr.label === name)).map(([t]) => t);
  assert.deepEqual(at('message_authorized'), ['app/community/channel/message/Proofs.lean']);
  assert.deepEqual(at('check_request'), ['app/community/member/invite/request/Proofs.lean']);
  assert.deepEqual(at('admin_removal_stands'), ['app/community/member/remove/Proofs.lean']);
  assert.deepEqual(at('reactTo'), ['app/community/channel/message/reaction/Commands.lean']);
});

test('the checked-in tree is the plan, and the page draws the same tree', async () => {
  const doc = await read('docs/OP_TREE.txt');
  const body = doc.slice(doc.indexOf('app/\n')).trimEnd().split('\n');
  assert.deepEqual(body, treeText(plan));
});

test('files that name a kind do not stay in the engine unnoticed', () => {
  const data = plan.engine.find(e => e.path === 'engine/renderer/Data.lean');
  assert.ok(data.namesKinds.includes('ops.community.Community'));
  const theme = plan.engine.find(e => e.path === 'engine/renderer/ThemeStore.lean');
  assert.equal(theme.leaves, 'app/settings/appearance/Op.lean');
  assert.ok(plan.engine.some(e => e.path === 'engine/core/Merkle.lean' && e.arrives === 'engine/core/Merkle.lean'));
});

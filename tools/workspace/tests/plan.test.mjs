// The workspace draws the op tree on disk: these check the plan against the
// repository itself, file by file, and that planned entries are only what
// LAYOUT02 requires and is missing.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFile, writeFile, mkdtemp, rm } from 'node:fs/promises';
import { existsSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { execFileSync, spawnSync } from 'node:child_process';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { index, treeText, laws, ORDER, parentOf } from '../src/tree.js';

const repo = new URL('../../../', import.meta.url);
const workspace = new URL('../', import.meta.url);
const plan = JSON.parse(await readFile(new URL('dist/plan.json', workspace), 'utf8'));
const layout = JSON.parse(await readFile(new URL('layout/tree.json', workspace), 'utf8'));
const tree = index(plan);
const read = path => readFile(new URL(path, repo), 'utf8');
const git = (...args) => execFileSync('git', args, {cwd: repo, encoding: 'utf8'}).split('\n').filter(Boolean);
const onDisk = path => existsSync(new URL(path, repo));
const lineCount = text => text.split('\n').length - (text.endsWith('\n') ? 1 : 0);
const imports = text => [...text.matchAll(/^import (app\.\S+)/gm)].map(m => m[1]);
const REQUIRED = ['Op.lean', 'Validate.lean', 'Proofs.lean', 'Tests.lean'];
const appFiles = git('ls-files', 'app');
const realFolders = new Set(appFiles.flatMap(f => { const out = []; for (let d = parentOf(f); d; d = parentOf(d)) out.push(d); return out; }));
const nodes = new Map(plan.nodes.map(n => [n.path, n]));

test('every tracked file under app/ is in the plan exactly once, with its real text, line count and hash', async () => {
  assert.ok(appFiles.length > 100, `${appFiles.length} files under app/`);
  assert.deepEqual(Object.keys(plan.files).sort(), [...appFiles].sort());
  for (const f of appFiles) {
    const text = await read(f), file = plan.files[f];
    assert.equal(file.text, text, `${f}: text differs from disk`);
    assert.equal(file.lines, lineCount(text), `${f}: line count`);
    assert.equal(file.sha256, createHash('sha256').update(text).digest('hex'), `${f}: hash`);
    const holders = plan.nodes.filter(n => n.files.some(name => `${n.path}/${name}` === f));
    assert.equal(holders.length, 1, `${f} is listed by ${holders.length} folders`);
    assert.equal(tree.entries.get(f)?.kind, 'file');
    assert.equal(tree.entries.get(f).planned, false, `${f} is on disk, not planned`);
  }
});

test('every folder of the plan is a real folder under app/ or planned, and every real folder is in the plan', () => {
  for (const d of realFolders) assert.ok(nodes.has(d), `${d}/ is on disk but not in the plan`);
  for (const n of plan.nodes) {
    assert.ok(n.path === 'app' || n.path.startsWith('app/'), n.path);
    if (!realFolders.has(n.path)) {
      assert.ok(n.planned, `${n.path}/ is neither on disk nor planned`);
      assert.ok(!onDisk(n.path), `${n.path}/ exists on disk but is untracked`);
    }
    if (plan.files[`${n.path}/Op.lean`]) assert.ok(n.kind === 'op' && !n.planned, `${n.path} has Op.lean: an op, not planned`);
    else if (n.planned) assert.equal(n.kind, n.planned === 'family' ? 'family' : 'op', n.path);
    else assert.ok(n.kind === 'family' && (n.children.length || n.path === 'app'), `${n.path}: a family has child folders`);
  }
  // The folders on disk that are planned ops are the ones ci/layout.py lets stand without Op.lean.
  const allowed = JSON.parse(execFileSync('python3', ['-c', 'import json, sys; sys.path.insert(0, "ci"); import layout; print(json.dumps(sorted(layout.PLANNED)))'], {cwd: repo, encoding: 'utf8'}));
  assert.deepEqual(plan.nodes.filter(n => n.planned && realFolders.has(n.path)).map(n => n.path).sort(), allowed);
});

test('every file has one of the eight names; every planned file is absent from disk and required by LAYOUT02', () => {
  const tracked = new Set(git('ls-files'));
  let planned = 0;
  for (const f of appFiles) assert.ok(ORDER.includes(f.split('/').at(-1)), `${f} is not one of the eight names`);
  for (const n of plan.nodes) {
    assert.deepEqual(n.files, ORDER.filter(f => n.files.includes(f)), `${n.path}: files in the fixed order`);
    if (n.kind === 'op') for (const f of REQUIRED) assert.ok(n.files.includes(f), `${n.path} lacks ${f}`);
    if (n.children.length) assert.ok(n.files.includes('Family.lean'), `${n.path} has child folders but no Family.lean`);
    for (const f of n.files) {
      const path = `${n.path}/${f}`;
      if (plan.files[path]) continue;
      planned++;
      assert.ok(!onDisk(path) && !tracked.has(path), `${path} is marked planned but exists`);
      assert.equal(tree.entries.get(path)?.planned, true, path);
      const required = (n.kind === 'op' && REQUIRED.includes(f)) || (f === 'Family.lean' && n.children.length > 0) ||
        (f === 'View.lean' && n.view) || (f === 'Screen.lean' && n.screen);
      assert.ok(required, `${path} is planned, but LAYOUT02 does not require it`);
    }
  }
  assert.ok(planned > 50, `${planned} planned files`);
});

test('every op on disk declares exactly one body tag, and no two ops share one', () => {
  const seen = new Map();
  for (const n of plan.nodes) {
    const op = plan.files[`${n.path}/Op.lean`];
    if (!op) { assert.equal(n.tag, undefined, n.path); continue; }
    const tags = [...op.text.matchAll(/Codec Body := Codec\.tagged (\d+)/g)].map(m => Number(m[1]));
    assert.deepEqual(tags, [n.tag], `${n.path}: body tags ${tags}`);
    assert.ok(!seen.has(n.tag), `${n.path} and ${seen.get(n.tag)} share tag ${n.tag}`);
    seen.set(n.tag, n.path);
  }
  assert.ok(seen.size >= 28, `${seen.size} ops`);
  assert.equal(nodes.get('app/community/channel/message/reaction').tag, 9);
});

test('layout/tree.json names only real or planned folders, and no code', async () => {
  assert.deepEqual(Object.keys(layout).sort(), ['nodes', 'roles']);
  assert.deepEqual(Object.keys(layout.roles), ORDER);
  const notes = new Set(plan.notes.map(n => n.path));
  for (const n of layout.nodes) {
    assert.ok(nodes.has(n.path) || notes.has(n.path), `${n.path} is not in the plan`);
    assert.deepEqual(Object.keys(n).filter(k => !['path', 'summary', 'preview', 'planned', 'view', 'screen'].includes(k)), [], n.path);
    if (notes.has(n.path)) assert.ok(git('ls-files', n.path).length > 0, `${n.path} is not a folder on disk`);
  }
  assert.equal(tree.previews.sync, 'engine/sync');
  // plan.py refuses a tree.json that invents a folder, plans an op that exists, or plans under nothing.
  const dir = await mkdtemp(join(tmpdir(), 'workspace-layout-'));
  try {
    const bad = {
      'not on disk': {path: 'app/community/ghost', summary: 'x'},
      'still marked planned': {path: 'app/community/channel/message/reaction', planned: 'shared'},
      'neither on disk nor planned': {path: 'app/ghost/child', planned: 'local'},
      'not a folder of app/': {path: 'engine/ghost', summary: 'x'},
    };
    for (const [message, node] of Object.entries(bad)) {
      const path = join(dir, 'tree.json');
      await writeFile(path, JSON.stringify({...layout, nodes: [...layout.nodes.filter(n => n.path !== node.path), node]}));
      const run = spawnSync('python3', ['tools/plan.py', '--layout', path, '--out', join(dir, 'plan.json')], {cwd: fileURLToPath(workspace), encoding: 'utf8'});
      assert.notEqual(run.status, 0, `plan.py accepted ${node.path}`);
      assert.match(run.stderr, new RegExp(message), run.stderr);
    }
  } finally {
    await rm(dir, {recursive: true, force: true});
  }
});

test('engine/ and platforms/ list exactly their tracked Lean files, and no engine file imports the app', async () => {
  for (const [root, list] of [['engine', plan.engine], ['platforms', plan.platforms]]) {
    assert.deepEqual(list.map(e => e.path), git('ls-files', `${root}/*.lean`), root);
    for (const e of list) {
      const text = await read(e.path);
      assert.equal(e.lines, lineCount(text), e.path);
      assert.deepEqual(e.importsApp, imports(text), e.path);
      assert.equal(tree.entries.get(e.path)?.kind, 'file', e.path);
    }
  }
  assert.ok(plan.engine.some(e => e.path.startsWith('engine/sync/')));
  for (const e of plan.engine) assert.deepEqual(e.importsApp, [], `${e.path} imports the app`);
  assert.ok(plan.platforms.some(e => e.importsApp.length), 'the shells import the app');
});

test('a planned Tests.lean lists the tests that import its folder today', async () => {
  let listed = 0;
  for (const n of plan.nodes) for (const t of n.tests) {
    assert.ok(imports(await read(t)).some(m => parentOf(m.replaceAll('.', '/')) === n.path), `${t} does not import ${n.path}`);
    listed++;
  }
  assert.ok(listed > 10, `${listed} listed`);
});

test('a Proofs.lean lists each of its laws at its line', async () => {
  const path = 'app/community/channel/message/Proofs.lean', text = await read(path);
  const at = text.split('\n').findIndex(l => l.startsWith('theorem message_authorized')) + 1;
  assert.ok(at > 0);
  assert.deepEqual(laws(text).find(l => l.name === 'message_authorized'), {name: 'message_authorized', line: at});
  for (const f of appFiles.filter(f => f.endsWith('/Proofs.lean'))) {
    const lines = plan.files[f].text.split('\n'), found = laws(plan.files[f].text);
    for (const l of found) assert.match(lines[l.line - 1], new RegExp(`(theorem|lemma) ${l.name.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}(?![\\w'.])`), `${f}:${l.line}`);
    assert.ok(found.length >= lines.filter(l => l.startsWith('theorem ')).length, f);
  }
});

test('the checked-in tree is the plan, and the page draws the same tree', async () => {
  const doc = await read('docs/OP_TREE.txt');
  assert.match(doc, /from the files on disk under app\//);
  const body = doc.slice(doc.indexOf('app/\n')).trimEnd().split('\n');
  assert.deepEqual(body, treeText(plan));
});

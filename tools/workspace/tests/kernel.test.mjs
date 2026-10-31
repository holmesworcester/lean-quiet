import { test } from "node:test";
import assert from "node:assert/strict";
import { readFile, mkdtemp, writeFile, rm } from "node:fs/promises";
import { spawnSync } from "node:child_process";
import { existsSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { initialState, act, verdict } from "../src/state.js";
import { definitionRange, replaceDefinition } from "../src/source-tools.js";
const bytes = await readFile(new URL("../dist/kernel.wasm", import.meta.url));
const module = await WebAssembly.compile(bytes);
const { exports: k } = await WebAssembly.instantiate(module);
test("WASM is standalone and exports actual compiled Lean functions", () => {
  assert.deepEqual(WebAssembly.Module.imports(module), []);
  for (const x of [
    "quiet_pixel",
    "quiet_validate",
    "quiet_theme",
    "quiet_color",
  ])
    assert.equal(typeof k[x], "function");
});
test("actual verdicts distinguish waiting, invalid, and valid contexts", () => {
  for (const present of [0, 1])
    for (const valid of [0, 1])
      for (const member of [0, 1])
        for (const same of [0, 1])
          for (const strict of [0, 1]) {
            const expected = !present
              ? 0
              : !valid || !member || (strict && !same)
                ? 2
                : 1;
            assert.equal(
              k.quiet_validate(present, valid, member, same, strict),
              expected,
            );
          }
});
test("a permissive policy produces a real cross-community counterexample", () => {
  assert.equal(k.quiet_validate(1, 1, 1, 0, 1), 2);
  assert.equal(k.quiet_validate(1, 1, 1, 0, 0), 1);
});
test("themes follow OS only in system mode", () => {
  for (const os of [0, 1]) {
    assert.equal(k.quiet_theme(0, os), os);
    assert.equal(k.quiet_theme(1, os), 0);
    assert.equal(k.quiet_theme(2, os), 1);
  }
  assert.equal(k.quiet_pixel(150, 300, 0, 0), 0xffffff);
  assert.equal(k.quiet_pixel(150, 300, 1, 0), 0x0d1117);
  assert.equal(k.quiet_pixel(280, 370, 0, 0xaabbcc), 0xaabbcc);
});
test("two clients converge only after their queued deliveries arrive", () => {
  let s = initialState();
  s = act(s, { type: "pause" }, k);
  s = act(s, { type: "react", client: 0 }, k);
  assert.deepEqual(
    s.clients.map((c) => c.reactions),
    [2, 1],
  );
  assert.equal(s.queue.length, 1);
  s = act(s, { type: "deliver" }, k);
  assert.deepEqual(
    s.clients.map((c) => c.reactions),
    [2, 2],
  );
  assert.equal(s.queue.length, 0);
});
test("invalid and missing references do not leak reactions into the query", () => {
  for (const fixture of ["missing", "foreign", "invalid", "outsider"]) {
    let s = act(initialState(), { type: "scenario", value: fixture }, k);
    s = act(s, { type: "react", client: 0 }, k);
    assert.deepEqual(
      s.clients.map((c) => c.reactions),
      [1, 1],
    );
    assert.equal(s.queue.length, 0);
    assert.notEqual(verdict(s, k), 1);
  }
});
test("client appearance and drafts remain local; store updates preserve inherited state", () => {
  let s = act(
    initialState(),
    { type: "draft", client: 0, value: "not finished" },
    k,
  );
  s = act(s, { type: "theme", client: 1, value: 1 }, k);
  assert.equal(s.clients[0].draft, "not finished");
  assert.equal(s.clients[1].draft, "");
  assert.equal(s.clients[0].preference, 0);
  assert.equal(s.clients[1].preference, 1);
  assert.equal(s.selectedOp, "reaction:3f8a");
});
test("WASM matches native Lean on exhaustive fixture inputs and representative painted pixels", async () => {
  const native = await readFile(
    new URL("../build/native-parity.txt", import.meta.url),
    "utf8",
  );
  const lines = native.split("\n").filter((x) => x.startsWith("CASE|"));
  assert.equal(lines.length, 284);
  for (const line of lines) {
    const [, fn, inputs, expected] = line.split("|");
    assert.equal(
      k["quiet_" + fn](...inputs.split(",").map(Number)),
      Number(expected),
      line,
    );
  }
});

test("definition edits are checked against the retained module and its actual proofs", async () => {
  const root = fileURLToPath(new URL("../", import.meta.url));
  const source = await readFile(new URL("../lean/Kernel.lean", import.meta.url), "utf8");
  const directory = await mkdtemp(root + "build/definition-test-");
  const installed = "/mnt/storage/elan/toolchains/leanprover--lean4---v4.34.0/bin/lean";
  const lean = process.env.LEAN || (existsSync(installed) ? installed : "lean");
  const definition = definitionRange(source, "validate").text;
  const check = async draft => {
    const path = directory + "/Draft.lean";
    await writeFile(path, replaceDefinition(source, "validate", draft));
    return spawnSync(lean, ["-R", ".", path], {cwd: root, encoding: "utf8"});
  };
  try {
    const valid = await check(definition);
    assert.equal(valid.status, 0, valid.stdout + valid.stderr);
    assert.match(valid.stdout, /Workspace.explicit_dark_overrides_os/);
    const broken = await check(definition.replace("else 1", "else 2"));
    assert.notEqual(broken.status, 0);
    assert.match(broken.stdout, /error:|unsolved goals/);
    assert.match(broken.stdout, /validate 1 1 1 1 1|evaluates to `false`/);
  } finally {
    await rm(directory, {recursive: true, force: true});
  }
});

import { test, expect } from "@playwright/test";

const errorsOf = page => {
  const errors = [];
  page.on("pageerror", e => errors.push(e.message));
  page.on("console", m => { if (m.type() === "error") errors.push(m.text()); });
  return errors;
};
const planOf = page => page.evaluate(() => window.__quiet.plan);
const ready = async page => { await expect(page.locator(".file-tree")).toBeAttached(); };
const open = (page, selector) => page.locator(selector).evaluate(e => { e.open = true; });

const go = (page, path) => page.evaluate(h => { location.hash = h; }, "#/tree/" + path);
const shownLines = page => page.locator(".source-line code").allTextContents();
const fileLines = text => text.replace(/\n$/, "").split("\n").map(l => l.trimEnd());

test("the sidebar is the tree on disk, and every folder and file under app/ opens to its real contents", async ({page}) => {
  test.setTimeout(300000);
  const errors = errorsOf(page);
  await page.goto("/");
  await expect(page).toHaveURL(/#\/tree\/app$/);
  await ready(page);
  const plan = await planOf(page);
  await expect(page.locator('.file-tree > li[data-entry-path]')).toHaveText([/app\//, /engine\//, /platforms\//]);
  await expect(page.locator("main")).not.toContainText(/main's files|where its code is|from ops\//i);
  expect(await (await page.request.get("/op-tree.txt")).text()).toContain("from the files on disk under app/");
  for (const node of plan.nodes) {
    await go(page, node.path);
    await expect(page.locator('.file-tree a[aria-current="page"]')).toHaveAttribute("title", node.path);
    await expect(page.locator("h1")).toHaveText(node.path === "app" ? "app" : node.path.slice(4).replaceAll("/", "."));
    await expect(page.locator(".file-section h2")).toHaveText(node.files);
    for (const f of node.files) {
      const path = `${node.path}/${f}`, file = plan.files[path], section = page.locator(`#file-${f.replace(".", "-")}`);
      const row = page.locator(`.file-tree li[data-entry-path="${path}"] a.nav-item`);
      if (file) await expect(row).not.toHaveClass(/planned/); else await expect(row).toHaveClass(/planned/);
      if (!file) await expect(section.locator(".planned-note")).toContainText("Planned.");
      else if (file.lines > 40) await expect(section.locator("summary .lines")).toContainText(`${file.lines} lines`);
      else await expect(section.locator(".file-code pre")).toHaveText(file.text.replace(/\n$/, ""));
    }
  }
  for (const node of plan.nodes) for (const f of node.files) {
    const path = `${node.path}/${f}`, file = plan.files[path];
    await go(page, path);
    await expect(page.locator('.file-tree a[aria-current="page"]')).toHaveAttribute("title", path);
    await expect(page.locator("h1")).toHaveText(f);
    await expect(page.locator(".doc-summary")).toHaveText(plan.roles[f]);
    if (!file) { await expect(page.locator(".planned-note")).toContainText("Planned."); continue; }
    await expect(page.locator(".source-line")).toHaveCount(file.lines);
    expect((await shownLines(page)).map(l => l.trimEnd()), path).toEqual(fileLines(file.text));
  }
  expect(errors).toEqual([]);
});

test("an op reads as its files, and a planned file says so", async ({page}) => {
  const errors = errorsOf(page);
  await page.goto("/#/tree/app/community/channel/message/reaction");
  await ready(page);
  await expect(page.locator(".operation-identity")).toHaveText(/^op·tag 9$/);
  await open(page, "#file-Op-lean details.file-code");
  await expect(page.locator("#file-Op-lean")).toContainText("structure Body where");
  await expect(page.locator("#file-Op-lean")).toContainText('"react", "byMessage"');
  await expect(page.locator("#file-Validate-lean")).toContainText("def check (C : Crypto)");
  await expect(page.locator("#file-Commands-lean")).toContainText("def reactTo");
  await expect(page.locator("#file-Proofs-lean .planned-note")).toHaveText("Planned.");
  const tests = page.locator("#file-Tests-lean");
  await expect(tests.locator(".planned-note")).toContainText("Today these import this folder");
  await tests.getByRole("link", {name: "tests/vacuity/ChatPresentation.lean"}).click();
  await expect(page).toHaveURL(/#\/source\/tests%2Fvacuity%2FChatPresentation\.lean\/1$/);
  await expect(page.locator(".source-document")).toContainText("import app.community.channel.message.reaction");
  await page.goto("/#/tree/app/community/channel");
  await expect(page.locator(".operation-identity")).toHaveText(/^planned op·shared$/);
  await page.goto("/#/tree/app/settings");
  await expect(page.locator(".operation-identity")).toHaveText(/^planned family$/);
  await expect(page.locator('.file-tree a[title="app/settings/appearance"]')).toHaveClass(/planned/);
  expect(errors).toEqual([]);
});

test("a law opens at its line, and a family page lists its ops before its files", async ({page}) => {
  const errors = errorsOf(page);
  const plan = (await page.goto("/"), await ready(page), await planOf(page));
  const path = "app/community/channel/message/Proofs.lean";
  const line = plan.files[path].text.split("\n").findIndex(l => l.startsWith("theorem message_authorized")) + 1;
  await page.goto("/#/tree/" + path);
  await page.locator(".law-list summary").click();
  await page.locator(".law-list").getByRole("link", {name: "message_authorized", exact: true}).click();
  await expect(page).toHaveURL(new RegExp(`#/tree/app/community/channel/message/Proofs\\.lean/${line}$`));
  await expect(page.locator(".selected-line")).toHaveCount(1);
  await expect(page.locator(".selected-line")).toHaveId(`line-${line}`);
  await expect(page.locator(".selected-line")).toContainText("theorem message_authorized");
  await expect(page.locator('.file-tree a[aria-current="page"]')).toHaveAttribute("title", path);
  await page.goto("/#/tree/app/community/member");
  const index = page.locator(".operation-index");
  await expect(index.locator(".operation-row a").first()).toHaveText("admin/");
  const indexTop = await index.boundingBox(), filesTop = await page.locator(".file-section").first().boundingBox();
  expect(indexTop.y).toBeLessThan(filesTop.y);
  expect(errors).toEqual([]);
});

test("engine and platforms are browsable, sync is in the engine, and no engine file imports the app", async ({page}) => {
  const errors = errorsOf(page);
  await page.goto("/#/tree/engine/sync");
  await ready(page);
  await expect(page.locator("h1")).toHaveText("engine/sync/");
  await expect(page.locator(".doc-summary")).toContainText("Range-based set reconciliation for every op type");
  await expect(page.locator('[data-component="sync"]')).toHaveCount(2);
  await expect(page.locator(".directory-list a", {hasText: "Wire.lean"})).toContainText(/\d+ lines/);
  await page.goto("/#/tree/engine/sync/Wire.lean");
  await expect(page.locator(".source-document")).toContainText("def kRbsr : UInt8 := 240");
  await page.goto("/#/tree/app/sync");
  await expect(page.locator("h1")).toHaveText("Not in the tree");
  for (const dir of ["engine", "engine/core", "engine/renderer"]) {
    await page.goto("/#/tree/" + dir);
    await expect(page.locator(".directory-list a").first()).toBeVisible();
    await expect(page.locator(".directory-list")).not.toContainText("imports the app");
  }
  await page.goto("/#/tree/engine/core/Codec.lean");
  await expect(page.locator(".source-document")).toContainText("namespace Engine");
  await page.goto("/#/tree/platforms/headless");
  await expect(page.locator(".directory-list a", {hasText: "Appearance.lean"})).toBeVisible();
  expect(errors).toEqual([]);
});

test("one fixture store flows through every view; only network shows two clients", async ({page}) => {
  const errors = errorsOf(page);
  await page.goto("/#/tree/app/community/channel/message/reaction");
  await ready(page);
  await expect(page.locator(".theme-preview")).toHaveCount(2);
  await page.getByRole("button", {name: "Maya: add leaf reaction"}).first().click();
  await expect(page.locator('[data-reaction-count="0"]').first()).toHaveText("2");
  await page.goto("/#/tree/app/community/channel/message");
  await expect(page.locator('[data-reaction-count="0"]').first()).toHaveText("2");
  await page.getByLabel("Scenario", {exact: true}).selectOption("missing");
  await open(page, "#state-section");
  await expect(page.locator("#state-section")).toContainText("message.available");
  await page.goto("/#/tree/app/community/channel/message/reaction");
  await expect(page.locator("#state-section")).toContainText("Waiting for dependency");
  await page.getByRole("button", {name: "Deliver missing message"}).click();
  await expect(page.locator("#state-section")).toContainText("Reaction accepted");
  await page.goto("/#/tree/app/community/channel/message/draft");
  await page.getByLabel("Maya message draft").first().fill("Kept across views");
  await page.goto("/#/tree/app");
  await expect(page.getByLabel("Maya message draft").first()).toHaveValue("Kept across views");
  await expect(page.locator(".client-wrap")).toHaveCount(1);
  await page.getByRole("link", {name: "network", exact: true}).click();
  await expect(page.locator(".client-wrap")).toHaveCount(2);
  await page.getByRole("button", {name: "Pause delivery"}).click();
  await page.getByRole("button", {name: "Maya: add leaf reaction"}).first().click();
  await open(page, "#state-section");
  await expect(page.locator('[data-reaction-count="1"]').first()).toHaveText("1");
  await expect(page.locator(".queue-number")).toHaveText("1 queued");
  await page.getByRole("button", {name: "Deliver next"}).click();
  await expect(page.locator('[data-reaction-count="1"]').first()).toHaveText("2");
  expect(errors).toEqual([]);
});

test("the preview's validator is real Lean compiled to WASM, with its kernel proofs", async ({page}) => {
  await page.goto("/#/tree/app/community/channel/message/reaction");
  await ready(page);
  await open(page, "#source-section");
  await expect(page.getByLabel("Lean validate definition")).toHaveValue(/def validate/);
  await expect(page.locator("#source-section .check-title")).toHaveCount(5);
  expect(await page.evaluate(() => window.__quiet.kernel.quiet_validate(1, 1, 1, 1, 1))).toBe(1);
});

test("phones get the same tree behind a menu, without sideways scrolling", async ({browser}) => {
  const page = await browser.newPage({viewport: {width: 390, height: 844}});
  await page.goto("/#/tree/app/community/channel/message/reaction");
  await ready(page);
  await expect(page.locator(".sidebar")).not.toBeInViewport();
  await page.getByRole("button", {name: "Toggle navigation"}).click();
  await expect(page.locator(".sidebar")).toBeInViewport();
  await page.locator('.file-tree a[title="app/community/profile"]').click();
  await expect(page.locator("h1")).toHaveText("community.profile");
  for (const path of ["app", "app/community/channel/message/reaction", "app/community"]) {
    await page.goto("/#/tree/" + path);
    await ready(page);
    expect(await page.evaluate(() => document.documentElement.scrollWidth)).toBeLessThanOrEqual(390);
  }
  await page.close();
});

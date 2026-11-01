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

test("the sidebar is the project tree, and every folder and file under app/ opens", async ({page}) => {
  const errors = errorsOf(page);
  await page.goto("/");
  await expect(page).toHaveURL(/#\/tree\/app$/);
  await ready(page);
  const plan = await planOf(page);
  await expect(page.locator('.file-tree > li[data-entry-path]')).toHaveText([/app\//, /engine\//, /platforms\//]);
  for (const node of plan.nodes) {
    await page.goto("/#/tree/" + node.path);
    await expect(page.locator("h1")).toHaveText(node.path === "app" ? "app" : node.path.slice(4).replaceAll("/", "."));
    await expect(page.locator(`.file-tree a[aria-current="page"]`)).toHaveAttribute("title", node.path);
    for (const f of node.files) await expect(page.locator(`.file-tree li[data-entry-path="${node.path}/${f}"]`)).toHaveCount(1);
    await expect(page.locator(".file-section h2")).toHaveText(node.files);
  }
  for (const file of ["app/community/channel/message/reaction/Validate.lean", "app/community/Family.lean", "app/sync/rbsr/Proofs.lean"]) {
    await page.goto("/#/tree/" + file);
    await expect(page.locator("h1")).toHaveText(file.split("/").at(-1));
  }
  expect(errors).toEqual([]);
});

test("an op reads as its files: constructors, validator and what it requires, linked to their producers", async ({page}) => {
  const errors = errorsOf(page);
  await page.goto("/#/tree/app/community/channel/message/reaction");
  await ready(page);
  await expect(page.locator(".operation-identity")).toContainText("tag 9");
  const op = page.locator("#file-Op-lean");
  await expect(op).toContainText("| react (c u target : Id) (emoji : ByteArray) (time : Nat)");
  await expect(op).toContainText('"react", "byMessage"');
  const validate = page.locator("#file-Validate-lean");
  await expect(validate).toContainText(".react e tm s, [.admission c u0 _ _, .admission c1 u d _, .message");
  await expect(page.locator("#file-Commands-lean")).toContainText("def reactTo");
  await validate.getByRole("link", {name: "community.channel.message", exact: true}).click();
  await expect(page).toHaveURL(/#\/tree\/app\/community\/channel\/message$/);
  await expect(page.locator("#file-Proofs-lean")).toContainText("message_authorized");
  await page.locator("#file-Op-lean .source-origin a").first().click();
  await expect(page).toHaveURL(/#\/source\/ops%2Fcommunity%2FFacts\.lean\/\d+$/);
  await expect(page.locator(".selected-line")).toHaveCount(1);
  await expect(page.locator(".selected-line")).toContainText("message");
  expect(errors).toEqual([]);
});

test("a law opens to its Lean, and a group page lists its ops before its files", async ({page}) => {
  await page.goto("/#/tree/app/community/member/invite/request");
  await ready(page);
  const law = page.locator("#file-Proofs-lean details.fragment", {hasText: "check_request"});
  await law.locator("summary").click();
  await expect(law).toContainText("theorem check_request");
  await page.goto("/#/tree/app/community/member");
  const index = page.locator(".operation-index");
  await expect(index.locator(".operation-row a").first()).toHaveText("admin/");
  const indexTop = await index.boundingBox(), filesTop = await page.locator(".file-section").first().boundingBox();
  expect(indexTop.y).toBeLessThan(filesTop.y);
});

test("engine and platforms are browsable, and code that names a kind is marked", async ({page}) => {
  await page.goto("/#/tree/engine/renderer");
  await ready(page);
  await expect(page.locator(".directory-list a", {hasText: "ThemeStore.lean"})).toContainText("moves to app/settings/appearance/Op.lean");
  await expect(page.locator(".directory-list a", {hasText: "Data.lean"})).toContainText("names kinds");
  await page.goto("/#/tree/engine/core/Merkle.lean");
  await expect(page.locator(".doc-summary")).toContainText("engine/core/Merkle.lean");
  await page.goto("/#/tree/engine/core/Codec.lean");
  await expect(page.locator(".source-document")).toContainText("namespace Engine");
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

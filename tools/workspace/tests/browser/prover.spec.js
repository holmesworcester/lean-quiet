import { test, expect } from "@playwright/test";
test.use({ actionTimeout: 15000 });
test("real browser Lean checks tactics and retained proofs after a definition edit", async ({
  page,
}) => {
  test.skip(
    !process.env.QUIET_TEST_PROVER,
    "Optional full Lean runtime; run mise workspace:prover",
  );
  test.setTimeout(360000);
  const errors = [];
  page.on("pageerror", (e) => errors.push(e.message));
  page.on("console", (m) => {
    if (m.text().startsWith("[lean4 timing]")) console.log(m.text());
  });
  await page.goto("/#/game/waits_for_dependency", {
    waitUntil: "domcontentloaded",
  });
  await expect(
    page.getByRole("heading", { name: "Wait for the message" }),
  ).toBeVisible();
  await page.getByRole("button", { name: "Try the solution" }).click();
  await page.getByRole("button", { name: "Load Lean & check" }).click();
  await expect(page.locator("#proof-output")).toContainText(
    /Lean accepted the proof|Lean did not establish|Browser prover:/,
    { timeout: 240000 },
  );
  console.log(
    "PROVER RESULT:",
    await page.locator("#proof-output").innerText(),
  );
  await expect(page.locator("#proof-output")).toContainText(
    "Lean accepted the proof",
  );
  await expect(page.locator("#proof-output")).toContainText(
    "Workspace.waits_for_dependency",
  );
  console.log("VALID PROOF COMPLETE; preparing counterexample");
  // A concrete false equality must be rejected, independently of tactic syntax.
  await page.getByRole("link", { name: /Keep community boundaries/ }).click();
  console.log("COUNTEREXAMPLE ROUTE OPEN");
  await page.getByLabel("Lean proof tactics").fill("exact Nat.zero_ne_one");
  await page.getByRole("button", { name: "Check proof", exact: true }).click();
  await expect(page.locator("#proof-output")).toContainText(
    "Lean did not establish this proof",
    { timeout: 180000 },
  );
  await page.goto('/#/tree/app/community/channel/message/reaction');
  await page.locator('#source-section').evaluate(e => { e.open = true; });
  const definition = page.getByLabel('Lean validate definition');
  await definition.fill((await definition.inputValue()).replace('else 1','else 2'));
  await page.getByRole('button',{name:'Check definition & proofs',exact:true}).click();
  await expect(page.locator('#source-output')).toContainText('Lean did not establish this proof',{timeout:180000});
  // Failed draft checking leaves both running code and its build evidence intact.
  expect(await page.evaluate(()=>window.__quiet.kernel.quiet_validate(1,1,1,1,1))).toBe(1);
  await expect(page.locator('#source-badge')).toContainText('unbuilt draft');
  expect(errors).toEqual([]);
});

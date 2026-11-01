import { Lean4 } from "lean4.js";
let instance = null,
  generation = 0;
export function cancel() {
  generation++;
  instance?.dispose();
  instance = null;
}
export async function check(code, onProgress) {
  const current = generation;
  if (!crossOriginIsolated)
    throw new Error(
      "This host needs HTTPS plus COOP/COEP headers. Use the supplied Tailscale HTTPS link.",
    );
  if (!instance)
    instance = new Lean4({
      basePath: "/lean-runtime",
      timeout: 180000,
      onProgress,
    });
  const runner = instance;
  runner.onProgress = onProgress;
  await runner.init();
  if (current !== generation) { runner.dispose(); throw new Error("Cancelled"); }
  onProgress(
    "Lean is checking your proof locally. Each execution can take about a minute…",
  );
  // This exported-only browser runtime cannot inspect imported proof bodies.
  // Keep theorem code unchanged; use type diagnostics instead of native axiom reports.
  const result = await runner.run(code.replace(/#print axioms /g, "#check "));
  if (current !== generation) throw new Error("Cancelled");
  return result;
}

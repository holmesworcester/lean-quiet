import tests.vacuity.RendererRuntime

-- App.start owns dedicated writer loops; terminate after the suite result,
-- as the repository's other headless executables do.
def main : IO Unit := do
  let code ← Vacuity.RendererRuntime.main
  (← IO.getStdout).flush
  IO.Process.exit code.toUInt8

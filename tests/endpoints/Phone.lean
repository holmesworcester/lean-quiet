import tests.endpoints.Harness
import engine.renderer.Slide

def main : IO Unit := do
  IO.sleep 1500
  let hints := Link.hints (← Link.local?) 49302
  let address := (hints.head?.bind String.fromUTF8?).getD "127.0.0.1:49302"
  let code ← EndpointNetwork.main ["B", "endpoint.db", "49302", "lan", address, "75", ""]
  IO.FS.writeFile "endpoint-result" (toString code)

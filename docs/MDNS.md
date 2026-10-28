# lean-mdns

mDNS / DNS-SD in Lean 4 with no dependencies: a DNS message codec with
proofs, the service logic (announce, browse, answer) as pure functions, and
a small loop over Lean's own `Std.Async.UDP`.

## The laws (engine/wire/mdns/Laws.lean)

They are proven on the functions the program runs, not on a model of them:

- **`decode_encode`**: `m.Valid → decode (encode m) = some m`. A valid
  message survives the wire, field for field.
- **`decode_valid`**: `decode p = some m → m.Valid`. Whatever the decoder
  accepts is valid: labels of 1 to 63 bytes, names of at most 255 wire bytes
  however their compression pointers were laid out, 4-byte A and 16-byte
  AAAA, TXT strings that fit their length byte, rdata that fits 16 bits.
- **`decode_roundtrip`**: the two together. Every packet the decoder accepts
  decodes to a message the encoder can send back unchanged.

The decoder ends on every input. Lean checks that when it accepts
`nameAt`, which is defined by well-founded recursion with no fuel and no
`partial`: a compression pointer must aim before the start of the name it
is in, so each jump moves strictly backwards. The decoder reads only
through `b[i]?` and size-checked `extract`. The laws use only Lean's
standard axioms (`propext`, `Classical.choice`, `Quot.sound`); the gate
checks this.

The encoder never compresses. The decoder accepts compression, since
avahi, mDNSResponder and routers all use it.

## API

```lean
import Mdns
open Mdns

-- Pure: the codec
encode : Msg → ByteArray
decode : ByteArray → Option Msg

-- Pure: DNS-SD
structure Service where inst type host : String; port : UInt16; txt : List String; addrs : List (List UInt8)
announce : Service → Msg          -- PTR, SRV, TXT, A/AAAA (TTL 120)
goodbye  : Service → Msg          -- the same with TTL 0
query    : String → Msg           -- PTR question for "_type._udp"
found    : String → Msg → List Found    -- services of a type an answer tells about
react    : List Service → Msg → Option Msg   -- a responder's answer to a query

-- Network (Mdns.Net): IPv4 224.0.0.251:5353
Net.open       : IO UDP.Socket                 -- bound with REUSEADDR, group joined
Net.send       : UDP.Socket → Msg → Async Unit
Net.loop       : UDP.Socket → (self : List Service) → (browse : List String)
                 → (onFound : Found → IO Unit) → (stop : IO Bool := pure false) → Async Unit
Net.localAddrs : IO (List (List UInt8))       -- non-loopback IPv4 addresses
```

`Net.loop` answers queries about `self`, ignores packets that don't
decode, and calls `onFound` for every service of a browsed type that an
answer mentions (your own services are left out). `stop` is checked after
each packet. Send `announce` or `query` from another task while it runs;
`tests/mdns/Demo.lean` does this.

In this repository: `import engine.wire.mdns.Mdns`.

## Tests

- `mise run test:mdns` is the deterministic gate (tests/mdns/check.sh;
  `mise run check` audits the laws' axioms). It builds the library, which
  checks the proofs. It scans the codec for `sorry`, `partial`, `panic`,
  `!`-indexing and `native_decide`. Then it runs `tests/mdns/Check.lean`:
  - 22 packets captured on a LAN (avahi, eero routers, a Sonos)
  - hostile packets: pointer loops, self and forward pointers, 64-byte
    labels, 257- and 321-byte names built from pointer chains, and every
    truncation of every fixture
  - 200,000 mutated packets, every one of which is checked to round-trip
  - the service logic

  Finally it runs negative controls. Each control breaks the codec on
  purpose (for example: pointers that may aim at themselves, names over 255
  bytes, a little-endian u16), and each must be refused by the proofs or by
  the checks.
- `mise run mdns:e2e` uses real multicast on this machine's network:
  Lean→Lean, Lean→avahi (avahi-browse resolves the Lean service) and
  avahi→Lean (Lean finds an `avahi-publish`ed service).

## Limits

- IPv4 only (no `ff02::fb` socket).
- No probing or conflict resolution (RFC 6762 §8). Pick an instance name
  that is unique, for example by adding a device id.
- No known-answer suppression, and every answer is multicast.
- `Net.localAddrs` lists every interface, including Docker bridges. On a
  phone, pass just the Wi-Fi address.
- Android: take a `WifiManager.MulticastLock`, and add the `INTERNET` and
  `CHANGE_WIFI_MULTICAST_STATE` permissions.
- iOS: raw multicast needs Apple's multicast entitlement.

import ops.connection.Commands
import ops.connection.Family
import ops.connection.Proofs
import ops.connection.connection.Commands
import ops.connection.connection.Op
import ops.connection.connection.Proofs
import ops.connection.connection.Validate
import ops.connection.eph.Commands
import ops.connection.eph.Op
import ops.connection.eph.Validate
import ops.connection.established.Commands
import ops.connection.established.Op
import ops.connection.established.Proofs
import ops.connection.established.Validate
import ops.connection.given.Commands
import ops.connection.given.Op
import ops.connection.given.Validate
import ops.connection.opened.Commands
import ops.connection.opened.Op
import ops.connection.opened.Proofs
import ops.connection.opened.Validate
import ops.connection.recv.Commands
import ops.connection.recv.Op
import ops.connection.recv.Validate
import ops.connection.request.Commands
import ops.connection.request.Op
import ops.connection.request.Validate
import ops.connection.send.Commands
import ops.connection.send.Op
import ops.connection.send.Proofs
import ops.connection.send.Validate
import engine.wire.Noise
import engine.wire.NoiseSymbolic
import ops.Commands
import ops.Proofs

/-!
The connection family, whole, with the node's commands and laws that
span both families (ops/Commands, ops/Proofs).
-/

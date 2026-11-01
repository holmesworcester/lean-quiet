# Android semantic action ownership

Android now captures the text that a Send or Continue action selected. Previously,
`TEXT(A), SEND, TEXT(B)` could reach Lean as a Send event followed by a read of the
latest editor text, causing B to be committed. The retained original diagnostic
used the real Field, JNI callbacks, Main loop and SQLite; its decrypted message
was B. The repaired diagnostic commits A once and retains B as the draft.

This is the first semantic-action stage. It does not bound all native event
queues, draft storage, text shaping, attachment work or the whole application.
The other platform shells explicitly expose the legacy capability until they
implement the owned-editor seam.

## Runtime contract

One native action slot retains an immutable UTF-8 snapshot, selection, monotone
nonzero ticket, text revision, editor incarnation and attachment/content
revision. Admission refuses a second outstanding action explicitly. It checks
the existing 1 MiB message byte limit before copying the action snapshot; saved
drafts and the editable Field are not truncated to that limit. Existing encoded
operation/frame admission remains authoritative for actual writes.

Java text callbacks and native terminal touch admission use the same mutex and
event FIFO. This orders actual callback admission, not physical OS timestamps.
A terminal touch owns its complete Lean classification, including an empty or
multi-event result. Its semantic owner comes from Down's displayed context;
Up captures the text revision. Rejected terminals still clean up pointer and
drag state. Long presses cannot activate Send or Continue without a snapshot.
Physical Enter is consumed once, including explicit busy refusal.

Editor identity includes the page, community/acceptance, exact text target and
semantic mount epoch. IME animation and safe-area geometry do not change that
identity. Touch still needs its displayed geometry lease. Photo/chip changes
advance a separate content revision, which is also checked against current App
state even when a latest-text read fails. Home and other pages with no visible
field do not edit or send the saved conversation draft.

Clear and install commands are asynchronous. They never wait for the Java UI
thread from the Lean/frame thread. A clear compares its captured owner and
revision, so later typing survives. A consumed-revision marker survives slot
retirement and suspension until the consumed empty value or newer typing is
adopted; a delayed callback cannot resurrect a sent draft after recreation.
The same already-consumed raw revision cannot be admitted again if posting
the Java clear throws; newer typing advances the revision and remains admissible.
Same-editor handoff preserves intervening Java typing. Every decoded ticket is
retired on normal completion, lifecycle early return and exception cleanup.

An initial/recreated Field is visibly disabled and exposes no InputConnection
until Java has installed and native code has acknowledged the authoritative
owner/text revision. A first tap retains its pending IME request; hide/revoke
cancels it. This is an initial/recreation admission guarantee, not a claim that
every later readiness failure disables Java (for example revision exhaustion
fails action admission closed).

Allocation failure at either actual snapshot-copy or latest-draft-copy site is
an explicit error, never a successful empty string. Ticket/owner counters fail
closed at exhaustion rather than wrapping.

## Gates

- `mise run test:owned-input` builds the actual Session dependency and runs the
  native action core and Lean decoder/Session tests, six compiling controls,
  and restored checks. Local app CI invokes this same named task.
- `mise run android:owned-input-e2e` builds actual Main, the instrumentation APK
  and test IME, provisions an owned emulator, then runs the actual JNI/App/SQLite
  scenarios, fourteen compiling APK controls and a restored baseline.
- `ci/local.sh android-owned-input` invokes the Android task. The scheduled,
  release and manual workflow template is `ci/android-owned-input.workflow.yml`.
  As with the repository's other platform templates, this file is not an active
  GitHub workflow until installed under `.github/workflows` with a provisioned
  runner and suitable repository permissions.

The provisioned Linux runner needs working user systemd scopes, KVM, JDK17+,
Android SDK/NDK29, API36 Google APIs x86_64 image, the repository's pinned
Lean/libuv sources and Rust Android target, SQLite and libsodium. Use a storage
workspace, `ELAN_HOME=/mnt/storage/elan`, `TMPDIR=/mnt/storage/holmes-tmp`, and
`ANDROID_AVD_HOME=/mnt/storage/holmes-avd`. Every build/run stays in a 48 GiB
scope. By default the task refuses an occupied port and reaps only the emulator
it starts. `OWNED_INPUT_PORT`/`OWNED_INPUT_AVD` select its owned instance.

Failure artifacts, exact APK hashes, process liveness, logcat, screenshots and
actual SQLite copies remain under `out/owned-input-android`. Controls require
successful compilation, runtime exit 1, the specific intended assertion and a
still-running target process. Compiler errors, crashes, unrelated failures and
timeouts are gate failures. Test-only gates delay original callbacks or force
particular allocation failures; they are never compiled into shipping sources.

Private diagnostics can explicitly reuse a verified existing AVD with
`OWNED_INPUT_REUSE_AVD=1` and previously compiled exact local IR with
`OWNED_INPUT_PRIVATE_REUSE_IR=1`. The manifest records IR reuse. These settings
are not evidence of a clean default build. The per-module native cache hashes
compiler version, flags, runtime headers and generated C contents; controls
substitute actual mutated generated app.Screen C and get distinct objects.

## Evidence and limits

The actual scenarios cover captured A versus later B, real touch Up, physical
Enter, busy refusal, stale editor after navigation, same-turn geometry change,
long-press refusal, changed photos with failed refresh, both allocation failures,
delayed clearing through background/checkpoint/recreation, same-editor typing
during delayed handoff, initial disabled editor, first-tap IME and canceled focus,
Home's saved draft, and Continue creating a community/profile from captured
values. Database assertions read real valid verdicts and authenticate encrypted
messages independently with libsodium; synthetic fixture content is used.

Native milliseconds are regression observations (including the unchanged
five-second message observation and three-second IME checks). They are separate
from bounds counted in each pipeline stage's completed service steps. Eventual
Java/native worker service still requires the platform to schedule those stages;
no fixed global App-frame or physical-display deadline follows from this patch.

The Lean `into_target` and `into_native` proofs still prove the actual pure text
routing functions used by App. Native action, JNI ownership, Java clearing and
SQLite behavior are tested runtime contracts, not kernel proofs of C/JVM/SQLite.
Existing native UInt32 displayed-frame identity/wrap behavior remains a
separate input-geometry boundary; semantic owner/ticket exhaustion here does
not prove that wider protocol.

The original isolated old-layout gate passed 209 baseline and restored checks
and fourteen compiling APK controls. This map-aware port targets 45f60e2 and
retains the current Reader/Demand and native-receipt code. That earlier result
is not validation of this port: the normal default build and combined platform
compatibility gates must run on its immutable integrated commit.

The integrated source passes the full 1,294-law and 670-entry vacuity gates,
30 native and 22 Input/Session assertions, all six compiling controls and
restored checks, 82 demand/34 component and 39 lifecycle assertions. The actual
CI dispatcher passes ten route/failure cases, including the earlier three photo
cases. Windows host input checks and all 45 Linux native input checks pass;
these do not stand in for a Windows runtime gate.

The first integrated compilation exposed the new platform capability missing
from the desktop adapter and the semantic editor revocation missing from two
full-state navigation specifications. The adapter now supplies its legacy
capability. The exact navigation laws include one epoch increment for Back and
two for Open followed by Back; their other state assertions remain intact.
The failed compilation and passing rerun are retained in
`out/ci/owned-input-integrated.log` and
`out/ci/owned-input-integrated-fixed.log`. The default integrated Android and
full app compatibility runs remain outstanding at this milestone.

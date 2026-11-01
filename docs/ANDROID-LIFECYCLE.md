# Android Activity ownership and IME regression

Android may destroy and replace a `NativeActivity` while retaining its process.
Previously that callback closed the process-global Lean run unconditionally;
the replacement then reused a run which was already shutting down. A final
`exit()` also ran Android/HWUI global destructors while their workers remained
alive. The observed failure ended in a destroyed-mutex abort.

The native boundary now queries the destroyed Activity's actual
`isChangingConfigurations()` result. Configuration replacement releases its
surface and Java owner without closing the Lean run; a real finish still closes
it. Native calls acquire their own JNI local reference under the owner mutex,
release the mutex before calling Java, and release the reference afterward.
Callbacks carry their originating Activity and cannot change a replacement
owner's state. Scroll physics retain the application context. After Lean's main
returns, stdio is flushed and `_Exit` terminates the dedicated native app process
without invoking concurrent global destructors.

The keyboard keeps a pending show request until the current Activity has window
focus, then posts the actual IME call. An explicit hide or an observed visible to
hidden transition cancels the request, including user Back. Posted work from a
destroyed owner is ignored. This follows Android's documented requirement that
the focused editor and window be ready before requesting the keyboard.

An independent test setup defect was also observed: APK installation completed
before the package-replacement broadcasts updated the IME service. IMMS had no
current method and the test IME never started. Draining broadcasts alone did not
resolve every case: repeatedly replacing the selected IME left a dangling bound
service record. The suite now unselects the old IME before installing its APK
once, then keeps that unchanged service throughout all app mutations. Tests
drain the actual Android broadcast queues and observe IME registration before
measuring app latency. The keyboard is not preopened; the first actual composer
tap must open it. The original 1.2-second keyboard waits are unchanged.

## Reproduce and review

Run `mise run android:lifecycle-e2e`, or `ci/local.sh android-lifecycle`.
`ci/local.sh android-ui` invokes both the existing twin UI suite and this task.
The lifecycle task builds the actual TwinDemo APK, a separate instrumentation
APK, and the test IME; creates its own `lean-quiet-lifecycle` AVD; then runs the
baseline, eight independently compiled runtime mutations, and the restored
baseline. The default owned emulator port is 5646 (`LIFECYCLE_PORT` overrides it).
It refuses to replace an occupied emulator and tears down its own process.

The fixture uses actual `Activity.recreate()` three times, checks the same live
PID and retained Lean state, delivers stale JNI text callbacks, taps the actual
composer, and opens a real dialog to remove window focus. It checks pending show,
pending hide, user Back, and a real `Activity.finish()` which removes all process
workers. A test-only native `atexit` probe makes global-destructor regression
observable without provoking a secondary HWUI crash. Nothing from the probe APK
is linked into the shipped app.

Each instrumentation invocation supplies a fresh token with its observations.
An earlier control exposed a fixture defect: a terminated run's retained
`ready` file was accepted before the next process existed. Captured evidence
showed an empty actual PID paired with the old run's PID. Replaying the same
saved APKs after tagging observations reached the intended stale-callback
assertion; no production code or assertion deadline changed for this repair.

The first six controls separately restore configuration-close behavior, permit stale
callbacks, restore `exit`, drop unfocused show, ignore pending hide, and retain
user-dismissed show. Each mutant must compile and fail its exact unchanged UI
assertion. Build failure, host exception, signal, native crash, and Java crash
in the captured app/instrumentation process are rejected as invalid control
results. Android's threadtime PID identifies the owner; unparseable fatal lines
also fail, as do target-process PANIC and uncaught-exception reports. Unrelated
OS crashes are retained separately with the complete log
(an emulator Bluetooth service abort exposed this attribution requirement).
Logs, screenshots from the original
UI suite, APK hashes, mutated source diffs, and OS IME/window diagnostics are
retained under `out/lifecycle` and `out/e2e-twin`.

## Runner and limits

Validated with the reviewed Android presentation completion bridge applied:
40/0 baseline, all six independently compiled controls rejected at their exact
assertions, and 40/0 restored. All eight app logs also passed the strict
native/Java/PANIC/uncaught-exception audit. The original named
`android:twin-demo-e2e` passed unchanged keyboard, text, composition, send,
scrolling and crash checks, including seven completed composer positions against
the original minimum of six. That task rebuilt both x86_64 and arm64-v8a APK
libraries under the 48GB cap. The comparable original-layer run passed with six
positions; its earlier two-host-core failure remains diagnostic evidence.

This is a provisioned Linux/KVM suite: Android SDK platform/build tools 35+,
NDK, API36 Google APIs x86_64 system image, JDK17+, Python3, Rust Android targets,
the repository's pinned Lean/libuv source trees, and a user systemd manager are
required. Give the four-vCPU emulator at least four host CPUs; the validated
comparisons used six host CPUs and serialized their UI timing suites. All
Lean/Lake builds use `MemoryMax=48G` and `MemorySwapMax=0`; private
mutation snapshots, runtime output and emulator images belong on `/mnt/storage`.
The checked-in `ci/android-lifecycle.workflow.yml` invokes the same named task on
a provisioned runner for scheduled, manual, and release runs. As with the other
workflow templates, remote activation must be reported separately.

These are realistic Android regressions, not a theorem that arbitrary native
OS scheduling, IME services, or compositor callbacks terminate. They do not add
an all-app memory or wall-clock bound. The JNI ownership change covers callbacks
including photo results, but this fixture exercises text callback rejection;
photo, scanner, and complete app checks remain their existing separate suites.
The subsequent [photo lifetime repair](ANDROID-PHOTO-LIFETIME.md) adds the
terminal cancellation result for recreation during pending selection/decode.
Its actual photo fixture is separate from this text-callback check. A blocked
content provider can still retain an old decoder thread; a global worker
bound remains open.
Windows is unchanged. No iOS runtime was available for this milestone; the
separate presentation work's C seam checks are not an iOS device test.

References: [Activity lifecycle](https://developer.android.com/guide/components/activities/activity-lifecycle),
[Activity.isChangingConfigurations](https://developer.android.com/reference/android/app/Activity#isChangingConfigurations()),
[native callbacks](https://developer.android.com/ndk/reference/struct/a-native-activity-callbacks),
and [keyboard visibility](https://developer.android.com/develop/ui/views/touch-and-input/keyboard-input/visibility).

The integrated photo-request follow-up is described in
[ANDROID-PHOTO-LIFETIME.md](ANDROID-PHOTO-LIFETIME.md). Native input ownership
and total event/worker bounds remain separate open work.


## Avoiding unchanged native transactions

Later validation of combined production `425979e` retained two failures of the
original keyboard animation check: five completed composer positions, below
its unchanged minimum of six. A trace-only Java build with identical native
libraries and assets observed 19 distinct inset heights. The compositor also
submitted unchanged idle geometry on every vsync, occupying its sole pending
callback slot.

The native renderer now skips a geometry-only transaction when the rounded
scroll sample equals the last submitted sample. A fresh publication always
gets its own transaction and exact receipt, even at unchanged geometry. Real
scroll changes, surface replacement, and the one-outstanding-callback limit
are preserved. The regression sends 10,000 unchanged ticks, checks rounded
subpixel motion, and requires a new unchanged publication to receive its own
acknowledgement. Restoring idle submissions must fail the callback-slot check.

On the private pre-reorganization candidate, both Android ABIs built, the
original device suite passed 17/0 with six positions, and all 13 native
controls were rejected; its host suite passed 42 checks. The integrated host
suite passes 44 checks, including the later refused-staging receipt tests.
All 40 integrated seam controls are rejected, including the 13 native controls;
the restored host suites pass. The original named `android:twin-demo-e2e`
then passes on exact integrated commit `ce76360`: 17/0, seven completed
positions against the unchanged minimum six, and both x86_64/arm64-v8a
ABIs built. All 1,682 tracked source hashes match before and after; no
source/test overlay is present. Three separate 120-frame aggregates measured
Lean 0.4–0.5 ms, copying 0.6–0.8 ms and native show/wait 40.9–44.5 ms per
frame. These are not controlled timing comparisons or theorem bounds. Exact
APK/source hashes, logs and screenshots are retained in
`/mnt/storage/holmes-tmp/android-combined-ce76360`. Newer semantic-input work
is separate. Original failures and diagnostics are retained in
`/mnt/storage/holmes-tmp/android-final-425979e`; main host logs are in
`out/ci/native-idle-main.log`.

Host CPU affinity was not exclusive. Aggregate native handoff time was
58.9 ms versus 56 ms before, so these results establish neither a timing
improvement nor a universal elapsed-time bound. The theorem target remains
each pipeline stage's completed steps; native timing is a separate measurement.

The owned-editor boundary adds a seventh control for the explicit legacy
TwinDemo client. Activity recreation retains its running Lean main, so opting
into legacy editing only once leaves a new Field disabled. TwinDemo reasserts
that capability on an actual available-surface event; Main continues to use
semantic owner installation. Removing that branch must fail the original
first-composer-tap-after-recreation assertion at its unchanged 1.2-second limit.
The preceding six-control results remain historical evidence for their stated
source. The combined follow-up below records the extended gate separately.

The eighth control removes the Activity startup correction that restores the
manifest's `stateHidden|adjustResize` policy after `NativeActivity.onCreate`
overrides it with `STATE_UNSPECIFIED|ADJUST_RESIZE`. Enabling the replacement
editor exposed automatic keyboard showing before any composer tap. The cold
launch check observes the actual window mode and hidden IME, then tests an
explicit first tap and Back at the original 1.2-second limits. The policy does
not clear pending explicit focus requests or hide the keyboard on each editor
installation. The combined follow-up passes 43 baseline assertions, all eight
strict compiling controls, and 43 restored assertions. The original twin UI
task passes all 17 checks, with seven completed composer positions against
the unchanged minimum of six. Both Android ABIs build successfully. This run
uses integrated commit `8bd282c7beb064e43260522b83ff897a752083e3` plus the
tracked compatibility follow-up; hashes and artifacts are retained in
`/mnt/storage/holmes-tmp/lean-quiet-owned-input/out/owned-input-integrated-8bd282c`.
The earlier cold-start failure and its actual window/IME trace remain separate
in `out/e2e-twin-initial-owned-input-failed` and `out/twin-owned-start-trace`.

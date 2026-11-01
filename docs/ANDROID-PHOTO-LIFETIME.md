# Pending photos across Android Activity replacement

Configuration recreation preserves the native Lean run. The old Java Activity
previously cleared its photo token and stopped its decoder executor without
publishing a terminal result. `App.photoStep` then retained `photoRequest`, so a
later attachment request could remain stuck behind a destroyed owner's work.

`LeanActivity.onDestroy` now publishes cancellation for its exact current token
before `super.onDestroy` releases the native owner. It clears the Java token
before stopping the worker. Native first-result-wins semantics still apply if
decoding already completed. A regular pause does not cancel the request: opening
the actual system picker itself pauses the Activity.

The separate `android:photo-lifecycle-e2e` Mise task builds the actual `Main` APK
and a test-only instrumentation APK, provisions its own emulator, seeds a real
EXIF-oriented photograph, and exercises `Main` with SQLite. It checks ordinary
picker selection, bounded decode and send; recreation while the picker is open;
recreation while the Activity's actual executor holds a queued decode; and a
late callback from the destroyed Activity deliberately using the replacement's
current finite token. The replacement must neither stay pending nor accept that
stale photo. The original `android:photo-e2e` suite remains separate and unchanged
in its behavior assertions. `ci/local.sh android-photo` invokes both named tasks.

The new suite requires four independently compiled controls to fail unchanged
assertions: omit destruction cancellation, cancel the wrong token, cancel
ordinary pause, and accept a retired Activity's photo callback. Baseline and
restored runs must pass; host exceptions, build failures, signals, target-process
native/Java crashes and PANIC reports do not count as valid control results.
The named gate passed26/0 baseline, all four independently compiled controls
failed their exact assertions, and the restored run passed26/0. The existing
named `android:photo-e2e` also passed its unchanged actual picker cancellation,
selection, EXIF orientation, bounded decode, attachment and send assertions.
That task rebuilt both x86_64 and arm64-v8a against the reviewed presentation
completion bridge under the48GB cap.

The shared `seed_photo.sh` setup helper first observes that the emulator's media
directory is writable. On a new AVD, `sys.boot_completed` preceded MediaProvider's
external volume attachment: an actual push failed at22:42:20.617 with
`Volume external_primary not found`, followed by attachment at22:42:20.649.
The helper waits on a real bounded write probe before seeding; it does not change
any app action or UI deadline. Both photo tasks call this helper.

The combined production revision `425979e` built both ABIs and passed 27 checks,
all four compiled controls and the restored 27-check run with an additional
setup barrier. A navigation command can reply before its cold first chat frame:
the original immediate status request took 0.790 seconds against its 0.5-second
limit; after that frame, the same request took 0.042 seconds. Those failure logs
are retained. Setup now requires a new, retained chat publication serial within
its existing 30-second navigation budget before starting photo measurements.
This is publication acceptance, not native display completion. All subsequent
0.5-second status and 3/15-second action deadlines are unchanged. Validation used
the same recorded baseline and four compiled mutant APK hashes; the additional
check does not turn a setup timeout into an accepted mutation failure.

Runner requirements are the provisioned Android/KVM prerequisites in
[ANDROID-LIFECYCLE.md](ANDROID-LIFECYCLE.md), plus Pillow for the fixture image.
The owned four-vCPU AVD defaults to emulator5650 (`PHOTO_LIFECYCLE_PORT`), and
requires at least four host CPUs. Builds remain capped at48GB with no swap.
Failure artifacts include APK hashes, source mutations, instrumentation,
actual app/OS logs, picker XML and screenshots under `out/photo-lifecycle`;
the existing suite retains `out/photo/android`. The scheduled/manual/release
workflow template invokes the same `android-photo` local CI gate; remote
activation must be reported separately.

This is a cancellation and ownership regression, not a proof that arbitrary
content-provider I/O returns. `shutdownNow` cannot force a blocked provider to
finish. The executor remains per Activity, so bounding retained old worker
threads needs a separate process-wide admission/lifetime policy. The fixture's
gate deliberately survives interruption until explicitly released; cancellation
must clear the app request before that release. Windows and iOS are unchanged.


A subsequent CI dispatcher check found an earlier duplicate `android-photo`
case that stopped after the picker task. Removing it makes the existing route
run both named suites. `mise run ci:driver-test` executes the actual dispatcher
with a recording task runner and checks both calls, first-task short circuit,
and second-task failure propagation. It failed before repair and passes all
three cases afterward. The default local gate and ready workflow templates
include this test; templates remain inactive until separately enabled.

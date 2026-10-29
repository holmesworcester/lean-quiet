package com.holmes.leanquiet;

import java.util.ArrayList;

/** The production lifecycle controller on a JVM, without an Android device. */
public final class BarsTest {
  static final class Fake implements BarState.Window {
    final ArrayList<Runnable> queue = new ArrayList<>();
    BarState.Choice shown;
    int paints;
    final ArrayList<BarState.Choice> history = new ArrayList<>();
    public void postBars(Runnable work) { queue.add(work); }
    public void paintBars(BarState.Choice choice) { shown = choice; paints++; history.add(choice); }
    void drain() { queue.forEach(Runnable::run); queue.clear(); }
  }
  static int checks;
  static void check(boolean yes, String message) {
    if (!yes) throw new AssertionError(message);
    checks++;
  }
  public static void main(String[] args) {
    BarState state = new BarState();
    Fake first = new Fake();
    state.attach(first);
    check(first.shown == null, "no policy before Lean's first frame");
    var dark = new BarState.Choice(0x16181b, 0x222529, true, true);
    var light = new BarState.Choice(0xffffff, 0xffffff, false, false);
    state.set(dark); first.drain();
    check(dark.equals(first.shown), "Lean's values applied exactly");
    state.set(light);
    Fake second = new Fake();
    state.attach(second);
    check(light.equals(second.shown), "latest choice survives recreation");
    first.drain();
    check(dark.equals(first.shown), "queued work cannot update outgoing window");
    state.detach(first);
    int before = second.paints;
    state.set(dark); state.set(light); second.drain();
    check(second.history.subList(before, second.paints).stream().allMatch(light::equals), "queued frames never flash an older choice");
    check(light.equals(second.shown), "queued work reads latest choice; old detach leaves new window attached");
    int painted = second.paints;
    state.set(light); second.drain();
    check(second.paints == painted, "identical frames do not enqueue bar work");
    state.detach(second);
    state.set(dark);
    Fake third = new Fake(); state.attach(third);
    check(dark.equals(third.shown), "choice made with no window is replayed on attach");
    System.out.println(checks + " bar lifecycle checks passed");
  }
}

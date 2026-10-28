/-
Offering the app's writes to the node without waiting (App.submit and
App.flushNode run `offerList` with the node channel's `trySend`): each
write in order until one is refused; the refused one and those after it
stay, to be offered again first.

The laws are about `offerList` itself, read in a model of the channel
(`Chan`): a channel answers each offer yes or no, in any sequence (full,
emptying, refusing for good), and takes what it says yes to.

- `offer_split`: what the channel took, then what stays, is exactly what
  was offered, in order: no write lost, none twice, none overtaken;
- `offer_runs`: so over any run of sends and re-offers, what the channel
  has taken, then what waits, is every write submitted, in submission
  order.
-/
namespace NodeOffer

variable {α : Type}

/-- Offer each in order until one is refused; the rest, from it on. -/
def offerList {m : Type → Type} [Monad m] (offer : α → m Bool) : List α → m (List α)
  | [] => pure []
  | a :: t => do if ← offer a then offerList offer t else pure (a :: t)

/-- A channel, as the app sees it: its answers to come, and what it took. -/
abbrev Chan (α : Type) := StateM (List Bool × List α)

/-- One offer: the channel's next answer (no, once it has none left);
taken if yes. -/
def offerM (a : α) : Chan α Bool := do
  let (ans, took) ← get
  match ans with
  | b :: r => set (r, if b then took ++ [a] else took); pure b
  | [] => pure false

/-- **What the channel took, then what stays, is what was offered, in
order**, whatever the channel answers. -/
theorem offer_split : ∀ (q : List α) (ans : List Bool) (took : List α),
    let r := (offerList offerM q).run (ans, took)
    r.2.2 ++ r.1 = took ++ q
  | [], ans, took => by simp [offerList, StateT.run, pure, StateT.pure]
  | a :: t, ans, took => by
    cases ans with
    | nil =>
      simp [offerList, offerM, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        pure, StateT.pure]
    | cons b r =>
      cases b with
      | true =>
        have ih := offer_split t r (took ++ [a])
        simp only [StateT.run] at ih ⊢
        simp only [offerList, offerM, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, set,
          MonadStateOf.set, StateT.set, pure, StateT.pure, ite_true] at ih ⊢
        simpa using ih
      | false =>
        simp [offerList, offerM, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, set,
          MonadStateOf.set, StateT.set, pure, StateT.pure]

/-- A run of the app's offers: each a write submitted (appended behind
those waiting) or a frame's re-offer, against the channel's answers. -/
def run : List (Option α) → List α → Chan α (List α)
  | [], waiting => pure waiting
  | some w :: t, waiting => do run t (← offerList offerM (waiting ++ [w]))
  | none :: t, waiting => do run t (← offerList offerM waiting)

/-- The writes a run submits, in order. -/
def submitted : List (Option α) → List α
  | [] => []
  | some w :: t => w :: submitted t
  | none :: t => submitted t

/-- **Over any run, what the channel has taken, then what waits, is every
write submitted, in submission order**: none lost, none twice, none
overtaken, however the channel answers. -/
theorem offer_runs : ∀ (steps : List (Option α)) (waiting : List α) (ans : List Bool) (took : List α),
    let r := (run steps waiting).run (ans, took)
    r.2.2 ++ r.1 = took ++ waiting ++ submitted steps
  | [], waiting, ans, took => by simp [run, submitted, StateT.run, pure, StateT.pure]
  | some w :: t, waiting, ans, took => by
    have hs := offer_split (waiting ++ [w]) ans took
    simp only [StateT.run] at hs ⊢
    generalize hq : offerList offerM (waiting ++ [w]) (ans, took) = q at hs
    obtain ⟨rest, ans', took'⟩ := q
    have ih := offer_runs t rest ans' took'
    simp only [StateT.run] at ih
    simp only [run, submitted, bind, StateT.bind, hq]
    rw [ih]; simp only at hs; rw [hs]; simp
  | none :: t, waiting, ans, took => by
    have hs := offer_split waiting ans took
    simp only [StateT.run] at hs ⊢
    generalize hq : offerList offerM waiting (ans, took) = q at hs
    obtain ⟨rest, ans', took'⟩ := q
    have ih := offer_runs t rest ans' took'
    simp only [StateT.run] at ih
    simp only [run, submitted, bind, StateT.bind, hq]
    rw [ih]; simp only at hs; rw [hs]

end NodeOffer

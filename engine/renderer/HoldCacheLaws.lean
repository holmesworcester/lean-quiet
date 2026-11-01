import engine.renderer.HoldCache

namespace Hold

/-- Cell size and hover never enter placeholder geometry or colors. -/
theorem messageLine_key (s : St) (line : Nat) :
    messageLine (MessageKey.ofState s).state line = messageLine s line := by rfl

theorem prepare_key (cache : MessageCache) (s : St) :
    (cache.prepare s).key = MessageKey.ofState s := by
  cases cache with
  | none => rfl
  | some old =>
    simp only [MessageCache.prepare]
    split <;> simp_all [MessageTile.make]

theorem prepare_reuses (old : MessageTile) (s : St)
    (same : old.key = MessageKey.ofState s) :
    MessageCache.prepare (some old) s = old := by
  simp [MessageCache.prepare, same]

theorem prepare_rows (cache : MessageCache) (s : St) :
    (cache.prepare s).rows = (MessageKey.ofState s).rows := by
  rw [(cache.prepare s).exact, prepare_key]

/-- No native renderer assumption: every returned row is definitionally the
original generator's row, for every valid cache and every height. -/
theorem cachedMessagePlane_exact (cache : MessageCache) (s : St) (height : Nat) :
    (cachedMessagePlane cache s height).1 = messagePlane s height := by
  simp only [cachedMessagePlane, MessageTile.plane, prepare_key, prepare_rows,
    MessageKey.rows, MessageKey.ofState, MessageKey.state, messagePlane]
  rfl

/-- Repeated frames retain the tile, independently of viewport height. -/
theorem cachedMessagePlane_reuses (cache : MessageCache) (s : St) (h h' : Nat) :
    (cachedMessagePlane (cachedMessagePlane cache s h).2 s h').2 =
      (cachedMessagePlane cache s h).2 := by
  simp only [cachedMessagePlane]
  rw [prepare_reuses _ _ (prepare_key cache s)]

end Hold

module

public import MeyerGeneralProblem.Cardinal.Strong.ReflectedPrimeSchedule
public import MeyerGeneralProblem.Cardinal.Strong.OriginalSheetAllocation

@[expose] public section

/-!
# Internally supplied global sheet-prime scales

The whole reflected order sequence is allocated to ALL global sheet indices.
Every block receives its own searched prime on every one of its sheets. Future
protected-window bounds cannot alter this actual finite scale prefix.
-/

namespace MeyerGeneralProblem.StrongParity

/-- Every actual reflected block has a positive complete sheet count. -/
theorem originalReflectedOrderSchedule_pos (bound : ℕ → ℕ) (n : ℕ) :
    0 < originalReflectedOrderSchedule bound n := by
  have h := (originalReflectedSchedule_spec bound n).2.2.1
  omega

/-- The ordinary global offset of the entire scheduled private block. -/
abbrev originalScheduledSheetOffset (bound : ℕ → ℕ) :=
  originalBlockSheetOffset (originalReflectedOrderSchedule bound)

/-- The ordinary block owner of EVERY actual global sheet. -/
abbrev originalScheduledSheetOwner (bound : ℕ → ℕ) :=
  originalBlockSheetOwner (originalReflectedOrderSchedule bound) (originalReflectedOrderSchedule_pos bound)

/-- ALL private block sheet labels, with their complete searched orders. -/
abbrev OriginalScheduledSheetLabel (bound : ℕ → ℕ) := Σ n, Fin (originalReflectedOrderSchedule bound n)

/-- Flatten an actual scheduled private sheet to its global index. -/
abbrev originalScheduledSheetIndex (bound : ℕ → ℕ) :=
  originalBlockSheetIndex (originalReflectedOrderSchedule bound)

/-- The computed bijection includes EVERY sheet of EVERY scheduled block. -/
def originalScheduledSheetEquiv (bound : ℕ → ℕ) : OriginalScheduledSheetLabel bound ≃ ℕ :=
  originalBlockSheetEquiv (originalReflectedOrderSchedule bound) (originalReflectedOrderSchedule_pos bound)

/-- Actual ordinary per-sheet scales supplied internally to the coupled construction. -/
def originalScheduledSheetScales (bound : ℕ → ℕ) (q : ℕ) : ℕ :=
  originalReflectedPrimeSchedule bound (originalScheduledSheetOwner bound q)

/-- All actual per-sheet scales are positive, with no positivity certificate supplied by a caller. -/
theorem originalScheduledSheetScales_pos (bound : ℕ → ℕ) (q : ℕ) :
    0 < originalScheduledSheetScales bound q := by
  have h := originalReflectedPrimeSchedule_large bound (originalScheduledSheetOwner bound q)
  change 0 < originalReflectedPrimeSchedule bound (originalScheduledSheetOwner bound q)
  omega

/-- EVERY sheet in a complete block has precisely that block's selected prime. -/
theorem originalScheduledSheetScales_block (bound : ℕ → ℕ) (n : ℕ)
    (i : Fin (originalReflectedOrderSchedule bound n)) :
    originalScheduledSheetScales bound (originalScheduledSheetOffset bound n + i.val) =
      originalReflectedPrimeSchedule bound n := by
  change originalReflectedPrimeSchedule bound
    (originalBlockSheetOwner (originalReflectedOrderSchedule bound) (originalReflectedOrderSchedule_pos bound)
      (originalBlockSheetIndex (originalReflectedOrderSchedule bound) ⟨n, i⟩)) = _
  rw [originalBlockSheetOwner_index]

/-- The actual increasing prime recursion is fixed by its finite window-bound prefix. -/
theorem originalPrivatePrimeSchedule_prefix_congr (bound bound' : ℕ → ℕ) (n : ℕ)
    (hb : ∀ j ≤ n, bound j = bound' j) :
    originalPrivatePrimeSchedule bound n = originalPrivatePrimeSchedule bound' n := by
  induction n with
  | zero => simp only [originalPrivatePrimeSchedule, hb 0 le_rfl]
  | succ n ih =>
    simp only [originalPrivatePrimeSchedule, ih (fun j hj => hb j (by omega)), hb (n + 1) le_rfl]

/-- The literal reflected prime also ignores all future requested bounds. -/
theorem originalReflectedPrimeSchedule_prefix_congr (bound bound' : ℕ → ℕ) (n : ℕ)
    (hb : ∀ j ≤ n, bound j = bound' j) :
    originalReflectedPrimeSchedule bound n = originalReflectedPrimeSchedule bound' n := by
  apply originalPrivatePrimeSchedule_prefix_congr
  intro j hj
  simp only [originalReflectedWindowBounds, hb j hj]

/-- The whole reflected block order ignores all future requested bounds. -/
theorem originalReflectedOrderSchedule_prefix_congr (bound bound' : ℕ → ℕ) (n : ℕ)
    (hb : ∀ j ≤ n, bound j = bound' j) :
    originalReflectedOrderSchedule bound n = originalReflectedOrderSchedule bound' n := by
  change originalPrivateOrder (originalReflectedPrimeSchedule bound n) =
    originalPrivateOrder (originalReflectedPrimeSchedule bound' n)
  rw [originalReflectedPrimeSchedule_prefix_congr bound bound' n hb]

/-- Future requested bounds cannot alter the global endpoint of an earlier complete prefix. -/
theorem originalScheduledSheetOffset_prefix_congr (bound bound' : ℕ → ℕ) (n : ℕ)
    (hb : ∀ j < n, bound j = bound' j) :
    originalScheduledSheetOffset bound n = originalScheduledSheetOffset bound' n :=
  originalBlockSheetOffset_prefix_congr _ _ n
    (fun j hj => originalReflectedOrderSchedule_prefix_congr bound bound' j (fun k hk => hb k (hk.trans_lt hj)))

/-- ALL scales of ALL sheets before an endpoint are fixed by the actual earlier window bounds. -/
theorem originalScheduledSheetScales_prefix_congr (bound bound' : ℕ → ℕ) (n q : ℕ)
    (hb : ∀ j < n, bound j = bound' j) (hq : q < originalScheduledSheetOffset bound n) :
    originalScheduledSheetScales bound q = originalScheduledSheetScales bound' q := by
  have hs : ∀ j < n, originalReflectedOrderSchedule bound j = originalReflectedOrderSchedule bound' j :=
    fun j hj => originalReflectedOrderSchedule_prefix_congr bound bound' j (fun k hk => hb k (hk.trans_lt hj))
  have hk := originalBlockSheetOwner_lt (originalReflectedOrderSchedule bound)
    (originalReflectedOrderSchedule_pos bound) q n hq
  have he := originalBlockSheetOwner_prefix_congr (originalReflectedOrderSchedule bound)
    (originalReflectedOrderSchedule bound') (originalReflectedOrderSchedule_pos bound)
    (originalReflectedOrderSchedule_pos bound') q n hs hq
  unfold originalScheduledSheetScales
  change originalReflectedPrimeSchedule bound (originalBlockSheetOwner _ _ q) =
    originalReflectedPrimeSchedule bound' (originalBlockSheetOwner _ _ q)
  rw [← he]
  exact originalReflectedPrimeSchedule_prefix_congr bound bound' _ (fun k hkle => hb k (hkle.trans_lt hk))

end MeyerGeneralProblem.StrongParity

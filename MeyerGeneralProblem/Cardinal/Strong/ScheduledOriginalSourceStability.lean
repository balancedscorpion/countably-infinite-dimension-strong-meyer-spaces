module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalBlockSourceStability
public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalRootAnchors

@[expose] public section

/-! The actual scheduled source and complete allowed carriers depend only on
the requested windows through their block index. The complete prefix is fixed
by its finite window history, including every retained coarse or zero-mass point. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- The dictionary at the common rewritten block coordinates ignores future windows. -/
theorem originalScheduledBlockNames_prefix_congr (bound bound' : ℕ → ℕ) (n : ℕ)
    (hb : ∀ j ≤ n, bound j = bound' j)
    (i : Fin (originalReflectedOrderSchedule bound' n)) :
    coupledOriginalParameterNames (originalScheduledSheetScales bound)
      (originalScheduledSheetScales_pos bound) disjointOriginalParameterSlot
        (originalScheduledSheetOffset bound' n + i.val) =
    coupledOriginalParameterNames (originalScheduledSheetScales bound')
      (originalScheduledSheetScales_pos bound') disjointOriginalParameterSlot
        (originalScheduledSheetOffset bound' n + i.val) := by
  apply originalScheduledParameterName_prefix_congr bound bound' (n + 1) _
    (fun j hj => hb j (by omega))
  change originalScheduledSheetOffset bound' n + i.val <
    originalScheduledSheetOffset bound n + originalReflectedOrderSchedule bound n
  rw [originalScheduledSheetOffset_prefix_congr bound bound' n (fun j hj => hb j hj.le),
    originalReflectedOrderSchedule_prefix_congr bound bound' n hb]
  exact Nat.add_lt_add_left i.isLt _

/-- The whole actual original source is fixed by its finite requested-window history. -/
theorem originalScheduledPrivateLineSource_prefix_congr (bound bound' : ℕ → ℕ) (n : ℕ)
    (hb : ∀ j ≤ n, bound j = bound' j) :
    originalScheduledPrivateLineSource bound n = originalScheduledPrivateLineSource bound' n := by
  unfold originalScheduledPrivateLineSource
  simp only [originalScheduledSheetOffset_prefix_congr bound bound' n (fun j hj => hb j hj.le),
    originalReflectedOrderSchedule_prefix_congr bound bound' n hb,
    originalReflectedPrimeSchedule_prefix_congr bound bound' n hb]
  exact coupledComputedOriginalPrivateLineSource_eq_of_names _ _ _ _ _ _
    (originalScheduledBlockNames_prefix_congr bound bound' n hb) _ _ _

/-- The ENTIRE privately deleted physical carrier ignores all future requested windows. -/
theorem originalScheduledPrivatePhysicalCarrier_prefix_congr (bound bound' : ℕ → ℕ) (n : ℕ)
    (hb : ∀ j ≤ n, bound j = bound' j) :
    originalScheduledPrivatePhysicalCarrier bound n = originalScheduledPrivatePhysicalCarrier bound' n := by
  unfold originalScheduledPrivatePhysicalCarrier
  simp only [originalScheduledSheetOffset_prefix_congr bound bound' n (fun j hj => hb j hj.le),
    originalReflectedOrderSchedule_prefix_congr bound bound' n hb,
    originalReflectedPrimeSchedule_prefix_congr bound bound' n hb]
  exact coupledComputedOriginalPrivatePhysicalCarrier_eq_of_names _ _ _ _ _ _
    (originalScheduledBlockNames_prefix_congr bound bound' n hb) _ _ _

/-- The ENTIRE allowed spectral cone and its actual noncoarse deletion are stable. -/
theorem originalScheduledPrivateSpectralCarrier_prefix_congr (bound bound' : ℕ → ℕ) (n : ℕ)
    (hb : ∀ j ≤ n, bound j = bound' j) :
    originalScheduledPrivateSpectralCarrier bound n = originalScheduledPrivateSpectralCarrier bound' n := by
  unfold originalScheduledPrivateSpectralCarrier
  simp only [originalReflectedOrderSchedule_prefix_congr bound bound' n hb,
    originalReflectedPrimeSchedule_prefix_congr bound bound' n hb]

/-- The complete finite mixed carrier is literally fixed by its requested finite history. -/
theorem originalScheduledPrefixCarrier_prefix_congr (bound bound' : ℕ → ℕ) (k : ℕ)
    (hb : ∀ j < k, bound j = bound' j) :
    originalScheduledPrefixCarrier bound k = originalScheduledPrefixCarrier bound' k := by
  apply LocallyFiniteCarrier.ext
  change originalSharedCoarseCone.carrier ∪ (⋃ i : Fin k,
    (originalScheduledPrivatePhysicalCarrier bound i.val).carrier ∪
      (originalScheduledPrivateSpectralCarrier bound i.val).carrier) = _
  congr 1
  apply congrArg Set.iUnion
  funext i
  rw [originalScheduledPrivatePhysicalCarrier_prefix_congr bound bound' i.val
      (fun j hj => hb j (hj.trans_lt i.isLt)),
    originalScheduledPrivateSpectralCarrier_prefix_congr bound bound' i.val
      (fun j hj => hb j (hj.trans_lt i.isLt))]

end
end MeyerGeneralProblem.StrongParity

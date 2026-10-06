module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalSourceStability
public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalProjectionResidual

@[expose] public section

/-! The SAME actual root-anchor tests and projection survive every future
change to requested windows. All equalities follow from finite history. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section
open scoped FourierTransform

/-- Equal carrier/source data give the same chosen nonzero root, independently of proof fields. -/
theorem originalIsolatingRootChoice_congr (S S' : LocallyFiniteCarrier)
    (T T' : TemperedDistribution ℝ ℂ)
    (hT : HasLocallyAtomicAction S T) (hT' : HasLocallyAtomicAction S' T')
    (hne : T ≠ 0) (hne' : T' ≠ 0) (hS : S = S') (hsource : T = T') :
    (Classical.choose (locallyAtomic_exists_isolationAction_ne_zero S T hT hne)).val =
      (Classical.choose (locallyAtomic_exists_isolationAction_ne_zero S' T' hT' hne')).val := by
  subst S'
  subst T'
  rfl

/-- Equal whole carrier/source data give identical normalized full Schwartz tests. -/
theorem originalNormalizedRootTest_congr (S S' U U' : LocallyFiniteCarrier)
    (T T' : TemperedDistribution ℝ ℂ)
    (hT : HasLocallyAtomicAction S T) (hT' : HasLocallyAtomicAction S' T')
    (hne : T ≠ 0) (hne' : T' ≠ 0) (hsub : S.carrier ⊆ U.carrier)
    (hsub' : S'.carrier ⊆ U'.carrier) (hS : S = S') (hU : U = U') (hsource : T = T') :
    let a := Classical.choose (locallyAtomic_exists_isolationAction_ne_zero S T hT hne)
    let a' := Classical.choose (locallyAtomic_exists_isolationAction_ne_zero S' T' hT' hne')
    (T (S.isolationSchwartz a))⁻¹ • U.isolationSchwartz (LocallyFiniteCarrier.inclusion hsub a) =
      (T' (S'.isolationSchwartz a'))⁻¹ • U'.isolationSchwartz (LocallyFiniteCarrier.inclusion hsub' a') := by
  subst S'
  subst U'
  subst T'
  rfl

/-- The actual chosen anchor has the same literal real coordinate after future changes. -/
theorem originalScheduledRootAnchor_prefix_congr (bound bound' : ℕ → ℕ) (n : ℕ)
    (hb : ∀ j ≤ n, bound j = bound' j) :
    (originalScheduledRootAnchor bound n : ℝ) = (originalScheduledRootAnchor bound' n : ℝ) := by
  exact originalIsolatingRootChoice_congr _ _ _ _
    (originalScheduledPrivateLineSource_both_strong bound n).1.1
    (originalScheduledPrivateLineSource_both_strong bound' n).1.1
    (originalScheduledPrivateLineSource_ne_zero bound n)
    (originalScheduledPrivateLineSource_ne_zero bound' n)
    (originalScheduledPrivatePhysicalCarrier_prefix_congr bound bound' n hb)
    (originalScheduledPrivateLineSource_prefix_congr bound bound' n hb)

/-- The normalized FULL Schwartz anchor test is literally unchanged, not merely equal on modes. -/
theorem originalScheduledPrefixAnchorTest_prefix_congr (bound bound' : ℕ → ℕ) (r : ℕ)
    (hb : ∀ j < r, bound j = bound' j) (i : Fin r) :
    originalScheduledPrefixAnchorTest bound r i = originalScheduledPrefixAnchorTest bound' r i := by
  have hi : ∀ j ≤ i.val, bound j = bound' j := fun j hj => hb j (hj.trans_lt i.isLt)
  exact originalNormalizedRootTest_congr _ _ _ _ _ _
    (originalScheduledPrivateLineSource_both_strong bound i.val).1.1
    (originalScheduledPrivateLineSource_both_strong bound' i.val).1.1
    (originalScheduledPrivateLineSource_ne_zero bound i.val)
    (originalScheduledPrivateLineSource_ne_zero bound' i.val)
    (originalScheduledPrivatePhysicalCarrier_subset_prefix bound r i)
    (originalScheduledPrivatePhysicalCarrier_subset_prefix bound' r i)
    (originalScheduledPrivatePhysicalCarrier_prefix_congr bound bound' i.val hi)
    (originalScheduledPrefixCarrier_prefix_congr bound bound' r hb)
    (originalScheduledPrivateLineSource_prefix_congr bound bound' i.val hi)

/-- The actual finite-rank projection is the SAME operator under future-window changes. -/
theorem originalScheduledAnchorProjection_prefix_congr (bound bound' : ℕ → ℕ) (r : ℕ)
    (hb : ∀ j < r, bound j = bound' j) :
    originalScheduledAnchorProjection bound r = originalScheduledAnchorProjection bound' r := by
  funext T
  unfold originalScheduledAnchorProjection
  have hs (i : Fin r) := originalScheduledPrivateLineSource_prefix_congr bound bound' i.val
    (fun j hj => hb j (hj.trans_lt i.isLt))
  simp only [originalScheduledPrefixAnchorTest_prefix_congr bound bound' r hb, hs]

/-- The entire physical Schwartz transpose test is stable under future-window changes. -/
theorem originalScheduledResidualPhysicalTest_prefix_congr (bound bound' : ℕ → ℕ) (r : ℕ)
    (hb : ∀ j < r, bound j = bound' j) (f : SchwartzMap ℝ ℂ) :
    originalScheduledResidualPhysicalTest bound r f = originalScheduledResidualPhysicalTest bound' r f := by
  unfold originalScheduledResidualPhysicalTest
  have hs (i : Fin r) := originalScheduledPrivateLineSource_prefix_congr bound bound' i.val
    (fun j hj => hb j (hj.trans_lt i.isLt))
  simp only [originalScheduledPrefixAnchorTest_prefix_congr bound bound' r hb, hs]

/-- The entire spectral Schwartz transpose test is stable under future-window changes. -/
theorem originalScheduledResidualSpectralTest_prefix_congr (bound bound' : ℕ → ℕ) (r : ℕ)
    (hb : ∀ j < r, bound j = bound' j) (f : SchwartzMap ℝ ℂ) :
    originalScheduledResidualSpectralTest bound r f = originalScheduledResidualSpectralTest bound' r f := by
  unfold originalScheduledResidualSpectralTest
  have hs (i : Fin r) := originalScheduledPrivateLineSource_prefix_congr bound bound' i.val
    (fun j hj => hb j (hj.trans_lt i.isLt))
  simp only [originalScheduledPrefixAnchorTest_prefix_congr bound bound' r hb, hs]

end
end MeyerGeneralProblem.StrongParity

module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalPrefixNumerator
public import Mathlib.Analysis.Complex.RealDeriv

@[expose] public section

/-! The ACTUAL complete mixed original real product has simple roots.
Every full root, including roots later deleted, is retained. Common-root exclusion
comes from the actual globally coupled root labels, not a separation certificate. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section
open scoped ContDiff

/-- The full undeleted finite mixed original root carrier, internally locally finite. -/
def originalScheduledPrefixFullRootCarrier (bound : ℕ → ℕ) (k : ℕ) : LocallyFiniteCarrier where
  carrier := originalScheduledPrefixRootSet bound k
  finite_inter_Icc a b := by
    rw [originalScheduledPrefixRootSet, Set.iUnion_inter]
    exact Set.finite_iUnion fun i => (originalScheduledFullPhysicalCarrier bound i.val).finite_inter_Icc a b

/-- Literal real block factor at its original private scale. -/
def originalScheduledScaledBlockSymbol (bound : ℕ → ℕ) (i : ℕ) (x : ℝ) : ℂ :=
  compactOriginalRealSheetProduct (originalScheduledParameterBlock bound i)
    (x / originalPrivateScale (originalReflectedPrimeSchedule bound i))

/-- The actual scaled block derivative retains its genuine nonzero private scale. -/
theorem originalScheduledScaledBlockSymbol_hasDerivAt (bound : ℕ → ℕ) (i : ℕ) (x : ℝ) :
    HasDerivAt (originalScheduledScaledBlockSymbol bound i)
      ((1 / originalPrivateScale (originalReflectedPrimeSchedule bound i) : ℝ) •
        deriv (compactOriginalComplexSheetProduct (originalScheduledParameterBlock bound i))
          (x / originalPrivateScale (originalReflectedPrimeSchedule bound i) : ℝ)) x := by
  have hc := (compactOriginalComplexSheetProduct_hasDerivAt (originalScheduledParameterBlock bound i)
    (x / originalPrivateScale (originalReflectedPrimeSchedule bound i) : ℝ)).differentiableAt.hasDerivAt
  change HasDerivAt (fun y : ℝ => compactOriginalRealSheetProduct (originalScheduledParameterBlock bound i)
    (y / originalPrivateScale (originalReflectedPrimeSchedule bound i))) _ x
  simpa only [compactOriginalComplexSheetProduct_ofReal, id_eq, Function.comp_def] using
    hc.comp_ofReal.scomp x ((hasDerivAt_id x).div_const (originalPrivateScale (originalReflectedPrimeSchedule bound i)))

/-- EVERY real root of each genuine private block remains simple after scaling. -/
theorem originalScheduledScaledBlockSymbol_deriv_ne_zero (bound : ℕ → ℕ) (i : ℕ) (x : ℝ)
    (hx : originalScheduledScaledBlockSymbol bound i x = 0) :
    deriv (originalScheduledScaledBlockSymbol bound i) x ≠ 0 := by
  rw [(originalScheduledScaledBlockSymbol_hasDerivAt bound i x).deriv]
  apply smul_ne_zero
  · exact one_div_ne_zero (originalPrivateScale_pos _ (originalScheduledBlockPrime_pos bound i)).ne'
  · apply compactOriginalComplexSheetProduct_deriv_ne_zero
    simpa only [compactOriginalComplexSheetProduct_ofReal, originalScheduledScaledBlockSymbol] using hx

/-- ALL distinct actual scheduled block factors have disjoint complete real root sets. -/
theorem originalScheduledScaledBlockSymbol_roots_disjoint (bound : ℕ → ℕ) (i j : ℕ)
    (hij : i ≠ j) (x : ℝ) (hi : originalScheduledScaledBlockSymbol bound i x = 0) :
    originalScheduledScaledBlockSymbol bound j x ≠ 0 := by
  intro hj
  have hi' := (originalScheduledBlockRealSymbol_zero_iff bound i x).mp hi
  have hj' := (originalScheduledBlockRealSymbol_zero_iff bound j x).mp hj
  obtain ⟨a, n, hn⟩ := (originalScheduledFullPhysicalCarrier_iff_label bound i x).mp hi'
  obtain ⟨b, m, hm⟩ := (originalScheduledFullPhysicalCarrier_iff_label bound j x).mp hj'
  have he := originalScheduledPhysicalRoot_injective bound (hn.trans hm.symm)
  exact hij (congrArg (fun z : OriginalScheduledSheetLabel bound × ℤ => z.1.1) he)

/-- The full real mixed product rule applies to EVERY original block. -/
theorem originalScheduledPrefixRealSymbol_hasDerivAt (bound : ℕ → ℕ) (k : ℕ) (x : ℝ) :
    HasDerivAt (originalScheduledPrefixRealSymbol bound k)
      (∑ i : Fin k, (∏ j ∈ (Finset.univ : Finset (Fin k)).erase i,
        originalScheduledScaledBlockSymbol bound j.val x) *
          deriv (originalScheduledScaledBlockSymbol bound i.val) x) x := by
  have hf (i : Fin k) : HasDerivAt (originalScheduledScaledBlockSymbol bound i.val)
      (deriv (originalScheduledScaledBlockSymbol bound i.val) x) x :=
    (originalScheduledScaledBlockSymbol_hasDerivAt bound i.val x).differentiableAt.hasDerivAt
  convert! HasDerivAt.fun_finsetProd (u := Finset.univ) (fun i _ => hf i) using 1

/-- Every zero of the ACTUAL complete mixed real product is simple, internally. -/
theorem originalScheduledPrefixRealSymbol_deriv_ne_zero (bound : ℕ → ℕ) (k : ℕ) (x : ℝ)
    (hx : originalScheduledPrefixRealSymbol bound k x = 0) :
    deriv (originalScheduledPrefixRealSymbol bound k) x ≠ 0 := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hx
  rw [(originalScheduledPrefixRealSymbol_hasDerivAt bound k x).deriv]
  have he : (∑ j : Fin k, (∏ l ∈ (Finset.univ : Finset (Fin k)).erase j,
      originalScheduledScaledBlockSymbol bound l.val x) * deriv (originalScheduledScaledBlockSymbol bound j.val) x) =
      (∏ l ∈ (Finset.univ : Finset (Fin k)).erase i,
        originalScheduledScaledBlockSymbol bound l.val x) * deriv (originalScheduledScaledBlockSymbol bound i.val) x := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      have hp : (∏ l ∈ (Finset.univ : Finset (Fin k)).erase j,
          originalScheduledScaledBlockSymbol bound l.val x) = 0 :=
        Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji.symm, Finset.mem_univ i⟩) hi
      rw [hp, zero_mul]
    · simp
  rw [he]
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    apply originalScheduledScaledBlockSymbol_roots_disjoint bound i.val j.val
      (fun h => (Finset.mem_erase.mp hj).1 (Fin.ext h).symm) x hi
  · exact originalScheduledScaledBlockSymbol_deriv_ne_zero bound i.val x hi

/-- Smoothness of the WHOLE actual real symbol, from its literal finite character motif. -/
theorem originalScheduledPrefixRealSymbol_contDiff (bound : ℕ → ℕ) (k : ℕ) :
    ContDiff ℝ ∞ (originalScheduledPrefixRealSymbol bound k) := by
  have he : originalScheduledPrefixRealSymbol bound k = finitePositiveExponentialSymbol
      (originalPositivePolynomialFrequency (originalPrivateScale (originalScheduledPrefixDenominator bound k))
        (originalScheduledPrefixPolynomialCoordinates bound k))
      (originalScheduledPrefixPolynomialCoefficient bound k) := by
    funext x
    exact (originalScheduledPrefixPolynomial_finiteSymbol bound k x).symm
  rw [he]
  unfold finitePositiveExponentialSymbol
  exact ContDiff.sum fun i _ => contDiff_const.mul (contDiff_combModulationCharacter _ _)

end
end MeyerGeneralProblem.StrongParity

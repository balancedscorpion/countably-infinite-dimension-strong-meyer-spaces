module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalSheets
public import MeyerGeneralProblem.Cardinal.Strong.CoupledOriginalPrefixStability
public import MeyerGeneralProblem.Cardinal.Strong.ComputedOriginalPrivateLine

@[expose] public section

/-!
# Complete scheduled original blocks with internally supplied coupled scales

Only natural protected-window bounds are supplied. Primes, orders, all sheet
indices, positive per-sheet scales, parameters, root deletions and complete
private strong lines are constructed by the implemented programs. ALL physical
roots obey the coupled cross-block exclusions. This does not yet assemble the
common carrier or prove mixed-prefix or infinite exhaustion.
-/

namespace MeyerGeneralProblem.StrongParity

/-- Every scheduled private order meets the complete original product hypothesis. -/
theorem originalScheduledBlockOrder_two_le (bound : ℕ → ℕ) (n : ℕ) :
    2 ≤ originalReflectedOrderSchedule bound n := (originalReflectedSchedule_spec bound n).2.2.1

/-- Every selected block prime is positive without a caller certificate. -/
theorem originalScheduledBlockPrime_pos (bound : ℕ → ℕ) (n : ℕ) :
    0 < originalReflectedPrimeSchedule bound n := by
  have h := originalReflectedPrimeSchedule_large bound n
  omega

/-- The actual ordinary coupled name at EVERY globally assigned original sheet. -/
def originalScheduledParameterName (bound : ℕ → ℕ) (q : ℕ) : CertifiedOriginalParameterName :=
  coupledOriginalParameterNames (originalScheduledSheetScales bound) (originalScheduledSheetScales_pos bound)
    disjointOriginalParameterSlot q

/-- EVERY earlier parameter name program is unchanged by future requested windows. -/
theorem originalScheduledParameterName_prefix_congr (bound bound' : ℕ → ℕ) (n q : ℕ)
    (hb : ∀ j < n, bound j = bound' j) (hq : q < originalScheduledSheetOffset bound n) :
    originalScheduledParameterName bound q = originalScheduledParameterName bound' q :=
  coupledOriginalParameterNames_prefix_congr _ _ _ _ _ _ q
    (fun j hj => originalScheduledSheetScales_prefix_congr bound bound' n j hb (hj.trans_lt hq))
    (fun _ _ => rfl)

/-- Ordinary binary physical-root names for EVERY root of EVERY scheduled block. -/
def originalScheduledPhysicalRootName (bound : ℕ → ℕ) (label : OriginalScheduledSheetLabel bound × ℤ)
    (p : ℕ) : ℚ :=
  coupledCompactOriginalPhysicalRootName (originalScheduledSheetScales bound)
    (originalScheduledSheetScales_pos bound) (originalScheduledSheetOffset bound label.1.1)
    (originalReflectedOrderSchedule bound label.1.1) (originalReflectedPrimeSchedule bound label.1.1)
    label.1.2 label.2 p

noncomputable section

/-- The actual complete compact parameter block, with all parameters and proof fields constructed internally. -/
def originalScheduledParameterBlock (bound : ℕ → ℕ) (n : ℕ) :
    CompactOriginalParameterBlock (originalReflectedOrderSchedule bound n) :=
  coupledCompactOriginalParameterBlock (originalScheduledSheetScales bound)
    (originalScheduledSheetScales_pos bound) (originalScheduledSheetOffset bound n)
    (originalReflectedOrderSchedule bound n)

/-- EVERY original physical root, with its literal private prime scale. -/
def originalScheduledPhysicalRoot (bound : ℕ → ℕ) (label : OriginalScheduledSheetLabel bound × ℤ) : ℝ :=
  scaledCompactOriginalRoot (originalReflectedPrimeSchedule bound label.1.1) label.2
    ((originalScheduledParameterBlock bound label.1.1).parameter label.1.2)

/-- All complete-block roots agree with the actual global coupled exclusion family. -/
theorem originalScheduledPhysicalRoot_eq (bound : ℕ → ℕ) (label : OriginalScheduledSheetLabel bound × ℤ) :
    originalScheduledPhysicalRoot bound label =
      coupledOriginalPhysicalRoot (originalScheduledSheetScales bound) (originalScheduledSheetScales_pos bound)
        disjointOriginalParameterSlot (originalScheduledSheetIndex bound label.1) label.2 :=
  coupledCompactOriginalPhysicalRoot_eq _ _ _ _ _ (originalScheduledSheetScales_block bound label.1.1) _ _

/-- Every implemented scheduled binary root name has its proved actual real error. -/
theorem originalScheduledPhysicalRootName_error (bound : ℕ → ℕ)
    (label : OriginalScheduledSheetLabel bound × ℤ) (p : ℕ) :
    |(originalScheduledPhysicalRootName bound label p : ℝ) - originalScheduledPhysicalRoot bound label| ≤
      1 / (2 : ℝ) ^ p := coupledCompactOriginalPhysicalRootName_error _ _ _ _ _ _ _ _

/-- EVERY scheduled original root avoids the full rational coarse module. -/
theorem originalScheduledPhysicalRoot_not_mem (bound : ℕ → ℕ) (label : OriginalScheduledSheetLabel bound × ℤ) :
    originalScheduledPhysicalRoot bound label ∉ parityRationalCoarseModule := by
  rw [originalScheduledPhysicalRoot_eq]
  exact coupledOriginalPhysicalRoot_not_mem _ _ _ _ _

/-- The actual root family is injective across ALL blocks, ALL sheets and ALL integer labels. -/
theorem originalScheduledPhysicalRoot_injective (bound : ℕ → ℕ) :
    Function.Injective (originalScheduledPhysicalRoot bound) := by
  intro z w he
  rw [originalScheduledPhysicalRoot_eq, originalScheduledPhysicalRoot_eq] at he
  have hg := @coupledOriginalPhysicalRoot_injective (originalScheduledSheetScales bound)
    (originalScheduledSheetScales_pos bound) disjointOriginalParameterSlot
    (originalScheduledSheetIndex bound z.1, z.2) (originalScheduledSheetIndex bound w.1, w.2) he
  have hsheet : z.1 = w.1 := originalBlockSheetIndex_injective (originalReflectedOrderSchedule bound)
    (originalReflectedOrderSchedule_pos bound) (congrArg (fun v : ℕ × ℤ => v.1) hg)
  have hint : z.2 = w.2 := congrArg (fun v : ℕ × ℤ => v.2) hg
  exact Prod.ext hsheet hint

/-- ALL distinct original root differences avoid the coarse module, including across different blocks. -/
theorem originalScheduledPhysicalRoot_difference_not_mem (bound : ℕ → ℕ)
    (z w : OriginalScheduledSheetLabel bound × ℤ) (hzw : z ≠ w) :
    originalScheduledPhysicalRoot bound z - originalScheduledPhysicalRoot bound w ∉ parityRationalCoarseModule := by
  rw [originalScheduledPhysicalRoot_eq, originalScheduledPhysicalRoot_eq]
  apply coupledOriginalPhysicalRoot_difference_not_mem
  intro he
  apply hzw
  have hsheet : z.1 = w.1 := originalBlockSheetIndex_injective (originalReflectedOrderSchedule bound)
    (originalReflectedOrderSchedule_pos bound) (congrArg (fun v : ℕ × ℤ => v.1) he)
  have hint : z.2 = w.2 := congrArg (fun v : ℕ × ℤ => v.2) he
  exact Prod.ext hsheet hint

/-- ALL original root sums avoid the coarse module, including cross-block and self-sums. -/
theorem originalScheduledPhysicalRoot_sum_not_mem (bound : ℕ → ℕ)
    (z w : OriginalScheduledSheetLabel bound × ℤ) :
    originalScheduledPhysicalRoot bound z + originalScheduledPhysicalRoot bound w ∉ parityRationalCoarseModule := by
  rw [originalScheduledPhysicalRoot_eq, originalScheduledPhysicalRoot_eq]
  exact coupledOriginalPhysicalRoot_sum_not_mem _ _ _ _ _ _ _

/-- The full undeleted physical carrier of the entire actual scheduled block. -/
def originalScheduledFullPhysicalCarrier (bound : ℕ → ℕ) (n : ℕ) : LocallyFiniteCarrier :=
  compactOriginalPhysicalSheetCarrier (originalScheduledParameterBlock bound n)
    (originalReflectedPrimeSchedule bound n) (originalScheduledBlockPrime_pos bound n)

/-- EVERY allowed undeleted physical point of a block has its actual scheduled root label. -/
theorem originalScheduledFullPhysicalCarrier_iff_label (bound : ℕ → ℕ) (n : ℕ) (x : ℝ) :
    x ∈ (originalScheduledFullPhysicalCarrier bound n).carrier ↔
      ∃ i : Fin (originalReflectedOrderSchedule bound n), ∃ k : ℤ,
        originalScheduledPhysicalRoot bound (⟨n, i⟩, k) = x :=
  compactOriginalPhysicalSheetCarrier_iff_label _ _ _ x

/-- The ENTIRE scheduled physical block escapes its requested window. -/
theorem originalScheduledFullPhysicalCarrier_escape (bound : ℕ → ℕ) (n : ℕ) {x : ℝ}
    (hx : x ∈ (originalScheduledFullPhysicalCarrier bound n).carrier) : (bound n : ℝ) + 1 < |x| :=
  (originalReflectedSchedule_escape bound n).2.trans
    (compactOriginalPhysicalSheetCarrier_gap _ _ _ hx)

/-- The entire private physical carrier with THIS implemented root selector's deletion. -/
def originalScheduledPrivatePhysicalCarrier (bound : ℕ → ℕ) (n : ℕ) : LocallyFiniteCarrier :=
  coupledComputedOriginalPrivatePhysicalCarrier (originalScheduledSheetScales bound)
    (originalScheduledSheetScales_pos bound) (originalScheduledSheetOffset bound n)
    (originalReflectedOrderSchedule bound n) (originalScheduledBlockOrder_two_le bound n)
    (originalReflectedPrimeSchedule bound n) (originalScheduledBlockPrime_pos bound n)

/-- The full private spectral carrier with its literal noncoarse head deletion. -/
def originalScheduledPrivateSpectralCarrier (bound : ℕ → ℕ) (n : ℕ) : LocallyFiniteCarrier :=
  computedOriginalPrivateSpectralCarrier (originalReflectedOrderSchedule bound n)
    (originalReflectedPrimeSchedule bound n) (originalScheduledBlockPrime_pos bound n)

/-- EVERY shared coarse point survives in EVERY actual scheduled private spectral carrier. -/
theorem originalScheduledPrivateSpectralCarrier_coarse (bound : ℕ → ℕ) (n : ℕ) :
    originalSharedCoarseCone.carrier ⊆ (originalScheduledPrivateSpectralCarrier bound n).carrier :=
  originalSharedCoarseCone_subset_computedPrivate _ _ _

/-- The COMPLETE original two-record strong pair on the actual internally scheduled private carriers. -/
def originalScheduledPrivateStrongPair (bound : ℕ → ℕ) (n : ℕ) : Submodule ℂ (TemperedDistribution ℝ ℂ) :=
  StronglyTemperedAtomicOnCarrier (originalScheduledPrivatePhysicalCarrier bound n) ⊓
    (StronglyTemperedAtomicOnCarrier (originalScheduledPrivateSpectralCarrier bound n)).comap
      temperedFourierLinearMap

/-- The actual internally scheduled nonzero original private source. -/
def originalScheduledPrivateLineSource (bound : ℕ → ℕ) (n : ℕ) : TemperedDistribution ℝ ℂ :=
  coupledComputedOriginalPrivateLineSource (originalScheduledSheetScales bound)
    (originalScheduledSheetScales_pos bound) (originalScheduledSheetOffset bound n)
    (originalReflectedOrderSchedule bound n) (originalScheduledBlockOrder_two_le bound n)
    (originalReflectedPrimeSchedule bound n) (originalScheduledBlockPrime_pos bound n)

/-- The complete actual scheduled private strong pair is exactly one complex line. -/
theorem originalScheduledPrivateStrongPair_finrank_one (bound : ℕ → ℕ) (n : ℕ) :
    Module.finrank ℂ (originalScheduledPrivateStrongPair bound n) = 1 :=
  coupledComputedOriginalPrivateStrongPair_finrank_one _ _ _ _ _ _ _

/-- The actual scheduled private line source is nonzero, with no source certificate input. -/
theorem originalScheduledPrivateLineSource_ne_zero (bound : ℕ → ℕ) (n : ℕ) :
    originalScheduledPrivateLineSource bound n ≠ 0 :=
  coupledComputedOriginalPrivateLineSource_ne_zero _ _ _ _ _ _ _

/-- EVERY original strongly tempered pair on these whole carriers belongs to the actual source line. -/
theorem originalScheduledPrivateStrongPair_complete_span (bound : ℕ → ℕ) (n : ℕ)
    (T : TemperedDistribution ℝ ℂ) :
    T ∈ originalScheduledPrivateStrongPair bound n ↔
      ∃ a : ℂ, T = a • originalScheduledPrivateLineSource bound n :=
  coupledComputedOriginalPrivateStrongPair_complete_span _ _ _ _ _ _ _ T

open scoped FourierTransform

/-- BOTH actual original weighted-TV records are admitted for every scheduled private source. -/
theorem originalScheduledPrivateLineSource_both_strong (bound : ℕ → ℕ) (n : ℕ) :
    originalScheduledPrivateLineSource bound n ∈ stronglyTemperedAtomicAtExponent
      (originalScheduledPrivatePhysicalCarrier bound n) ((originalReflectedOrderSchedule bound n - 1) + 2) ∧
    𝓕 (originalScheduledPrivateLineSource bound n) ∈ stronglyTemperedAtomicAtExponent
      (originalScheduledPrivateSpectralCarrier bound n) (originalReflectedOrderSchedule bound n + 3) :=
  coupledComputedOriginalPrivateLineSource_both_strong _ _ _ _ _ _ _

/-- EVERY nonzero original pair on an actual scheduled private block fails any exponent below its order. -/
theorem originalScheduledPrivateStrongPair_not_lowExponent (bound : ℕ → ℕ) (n N : ℕ)
    (hN : N < originalReflectedOrderSchedule bound n) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ originalScheduledPrivateStrongPair bound n) (hT0 : T ≠ 0) :
    T ∉ stronglyTemperedAtomicAtExponent (originalScheduledPrivatePhysicalCarrier bound n) N :=
  coupledComputedOriginalPrivateStrongPair_not_lowExponent _ _ _ _ _ _ _ N hN T hT hT0

end

end MeyerGeneralProblem.StrongParity

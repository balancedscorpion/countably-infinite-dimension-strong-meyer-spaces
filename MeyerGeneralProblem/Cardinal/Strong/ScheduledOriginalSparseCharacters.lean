module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalSparseArray
public import MeyerGeneralProblem.Cardinal.Strong.LaurentCharacterTwists
public import Mathlib.RingTheory.RootsOfUnity.Basic

@[expose] public section

/-! The ACTUAL finite root-of-unity torus of each scheduled prime. Its action
on the original sparse array is derived from the literal carrier geometry,
including the common coarse cone. There is no supplied character certificate. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- The actual two-coordinate integer character, including negative powers. -/
def originalIntegerTorusCharacter (ζ η : ℂˣ) : Multiplicative (ℤ × ℤ) →* ℂˣ where
  toFun n := ζ ^ n.toAdd.1 * η ^ n.toAdd.2
  map_one' := by simp
  map_mul' n m := by
    change ζ ^ (n.toAdd.1 + m.toAdd.1) * η ^ (n.toAdd.2 + m.toAdd.2) = _
    simp only [zpow_add]
    ac_rfl

/-- Both coordinates of the ACTUAL scheduled prime's root-of-unity group. -/
def OriginalScheduledPrimeTorus (bound : ℕ → ℕ) (i : ℕ) :=
  rootsOfUnity (originalReflectedPrimeSchedule bound i) ℂ ×
    rootsOfUnity (originalReflectedPrimeSchedule bound i) ℂ

/-- No root-power assumption is supplied: membership in the actual prime torus pays it. -/
def originalScheduledPrimeCharacter (bound : ℕ → ℕ) (i : ℕ)
    (g : OriginalScheduledPrimeTorus bound i) : Multiplicative (ℤ × ℤ) →* ℂˣ :=
  originalIntegerTorusCharacter g.1.val g.2.val

/-- A root of unity is trivial on EVERY signed multiple of any multiple of its order. -/
theorem originalRootOfUnity_zpow_dilation (m d : ℕ) (ζ : rootsOfUnity m ℂ)
    (hmd : m ∣ d) (a : ℤ) : ζ.val ^ ((d : ℤ) * a) = 1 := by
  obtain ⟨b, rfl⟩ := hmd
  have hm : ζ.val ^ m = 1 := (mem_rootsOfUnity m ζ.val).mp ζ.property
  rw [zpow_mul, zpow_natCast, pow_mul, hm, one_pow, one_zpow]

/-- The actual prime character fixes ALL labels of every other private block. -/
theorem originalScheduledPrimeCharacter_other_dilation (bound : ℕ → ℕ) (k : ℕ)
    (i j : Fin k) (hij : i ≠ j) (g : OriginalScheduledPrimeTorus bound i.val) (w : ℤ × ℤ) :
    originalScheduledPrimeCharacter bound i.val g
      (Multiplicative.ofAdd (originalIntegerCoordinateDilation
        (originalScheduledPrefixCoordinateDilation bound k j) w)) = 1 := by
  change g.1.val ^ ((originalScheduledPrefixCoordinateDilation bound k j : ℤ) * w.1) *
    g.2.val ^ ((originalScheduledPrefixCoordinateDilation bound k j : ℤ) * w.2) = 1
  rw [originalRootOfUnity_zpow_dilation _ _ _
      (originalScheduledOtherPrime_dvd_coordinateDilation bound k i j hij),
    originalRootOfUnity_zpow_dilation _ _ _
      (originalScheduledOtherPrime_dvd_coordinateDilation bound k i j hij), one_mul]

/-- EVERY sparse original row is fixed by at least one of two distinct ACTUAL prime actions. -/
theorem originalScheduledPrimeCharacters_sparse_alternative (bound : ℕ → ℕ) (k : ℕ)
    (i j : Fin k) (hij : i ≠ j) (g : OriginalScheduledPrimeTorus bound i.val)
    (h : OriginalScheduledPrimeTorus bound j.val) (z : ℤ × ℤ)
    (hz : z ∈ originalScheduledPrefixSparseLabels bound k) :
    originalScheduledPrimeCharacter bound i.val g (Multiplicative.ofAdd z) = 1 ∨
      originalScheduledPrimeCharacter bound j.val h (Multiplicative.ofAdd z) = 1 := by
  obtain ⟨l, w, rfl⟩ := Set.mem_iUnion.mp hz
  by_cases hil : i = l
  · subst l
    exact Or.inr (originalScheduledPrimeCharacter_other_dilation bound k j i hij.symm h w)
  · exact Or.inl (originalScheduledPrimeCharacter_other_dilation bound k i l hil g w)

/-- ALL-label mixed character differences vanish for EVERY actual original complete
strong pair. Sparse support and prime arithmetic are supplied internally. -/
theorem originalScheduledPrefixFourierArray_mixed_character_zero (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k))
    (i j : Fin k) (hij : i ≠ j) (g : OriginalScheduledPrimeTorus bound i.val)
    (h : OriginalScheduledPrimeTorus bound j.val) (z : ℤ × ℤ) :
    ((originalScheduledPrimeCharacter bound i.val g (Multiplicative.ofAdd z) : ℂ) - 1) *
      ((originalScheduledPrimeCharacter bound j.val h (Multiplicative.ofAdd z) : ℂ) - 1) *
        originalScheduledPrefixFourierArray bound k T z = 0 := by
  by_cases hz : z ∈ originalScheduledPrefixSparseLabels bound k
  · rcases originalScheduledPrimeCharacters_sparse_alternative bound k i j hij g h z hz with hg | hh
    · simp only [hg, Units.val_one, sub_self, zero_mul]
    · simp only [hh, Units.val_one, sub_self, mul_zero, zero_mul]
  · rw [originalScheduledPrefixFourierArray_zero_off_sparse bound k T hT z hz, mul_zero]

/-- The literal positive half-line cut retains the same mixed character identity, including zero. -/
theorem originalScheduledPrefixPositiveCut_mixed_character_zero (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k))
    (i j : Fin k) (hij : i ≠ j) (g : OriginalScheduledPrimeTorus bound i.val)
    (h : OriginalScheduledPrimeTorus bound j.val) (z : ℤ × ℤ) :
    ((originalScheduledPrimeCharacter bound i.val g (Multiplicative.ofAdd z) : ℂ) - 1) *
      ((originalScheduledPrimeCharacter bound j.val h (Multiplicative.ofAdd z) : ℂ) - 1) *
        arrayPositiveCut
          (originalScaledModuleFrequencyHom (originalPrivateScale (originalScheduledPrefixDenominator bound k)))
          0 (originalScheduledPrefixFourierArray bound k T) z = 0 := by
  classical
  unfold arrayPositiveCut
  split_ifs
  · exact originalScheduledPrefixFourierArray_mixed_character_zero bound k T hT i j hij g h z
  · exact mul_zero _

/-- The other ORIGINAL cut is strict at zero and retains EVERY exterior and negative row. -/
theorem originalScheduledPrefixNegativeCut_mixed_character_zero (bound : ℕ → ℕ) (k : ℕ)
    (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ StronglyTemperedMeyerSpace (originalScheduledPrefixCarrier bound k))
    (i j : Fin k) (hij : i ≠ j) (g : OriginalScheduledPrimeTorus bound i.val)
    (h : OriginalScheduledPrimeTorus bound j.val) (z : ℤ × ℤ) :
    ((originalScheduledPrimeCharacter bound i.val g (Multiplicative.ofAdd z) : ℂ) - 1) *
      ((originalScheduledPrimeCharacter bound j.val h (Multiplicative.ofAdd z) : ℂ) - 1) *
        arrayNegativeCut
          (originalScaledModuleFrequencyHom (originalPrivateScale (originalScheduledPrefixDenominator bound k)))
          0 (originalScheduledPrefixFourierArray bound k T) z = 0 := by
  classical
  unfold arrayNegativeCut
  split_ifs
  · exact originalScheduledPrefixFourierArray_mixed_character_zero bound k T hT i j hij g h z
  · exact mul_zero _

end
end MeyerGeneralProblem.StrongParity

module

public import MeyerGeneralProblem.Cardinal.Strong.ProductPairClassification

@[expose] public section

/-! Exact complete strong spaces for the original TWO distinct containers.
These statements do not replace the missing common-carrier mixed-source theorem. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

open scoped FourierTransform

/-- All pairs with both ORIGINAL records strongly tempered on the two actual carriers. -/
def productOriginalStrongPairSpace (s : ℕ) : Submodule ℂ (TemperedDistribution ℝ ℂ) :=
  StronglyTemperedAtomicOnCarrier (productSheetCarrier s) ⊓
    (StronglyTemperedAtomicOnCarrier spectralConeCarrier).comap temperedFourierLinearMap

/-- Both original weighted variations are summable at the same explicit exponent. -/
def productOriginalStrongExponentPairSpace (s N : ℕ) : Submodule ℂ (TemperedDistribution ℝ ℂ) :=
  stronglyTemperedAtomicAtExponent (productSheetCarrier s) N ⊓
    (stronglyTemperedAtomicAtExponent spectralConeCarrier N).comap temperedFourierLinearMap

theorem productOriginalStrongExponentPairSpace_le_pair (s N : ℕ) :
    productOriginalStrongExponentPairSpace s N ≤ productOriginalPairSpace s := by
  intro T hT
  exact ⟨hasLocallyAtomicAction_atomicOnCarrier _ _ hT.1.1,
    hasLocallyAtomicAction_atomicOnCarrier _ _ hT.2.1⟩

theorem productOriginalStrongPairSpace_le_pair (s : ℕ) :
    productOriginalStrongPairSpace s ≤ productOriginalPairSpace s := by
  intro T hT
  obtain ⟨N, hN⟩ := (mem_stronglyTemperedAtomicOnCarrier_iff _ T).mp hT.1
  obtain ⟨M, hM⟩ := (mem_stronglyTemperedAtomicOnCarrier_iff _ (𝓕 T)).mp hT.2
  exact ⟨hasLocallyAtomicAction_atomicOnCarrier _ _ hN.1,
    hasLocallyAtomicAction_atomicOnCarrier _ _ hM.1⟩

theorem productOriginalPairSpace_le_strongExponentPairSpace (s N : ℕ) (hN : s + 3 ≤ N) :
    productOriginalPairSpace s ≤ productOriginalStrongExponentPairSpace s N := by
  intro T hT
  exact ⟨stronglyTemperedAtomicAtExponent_mono _ (by omega)
      (productOriginalPair_physical_mem_strongExponent s ⟨T, hT⟩),
    stronglyTemperedAtomicAtExponent_mono _ hN
      (productOriginalPair_spectral_mem_strongExponent s ⟨T, hT⟩)⟩

/-- The COMPLETE original pair space is a fixed absolute-TV layer once the
exponent is at least the actual proved bound. -/
theorem productOriginalStrongExponentPairSpace_eq_pair (s N : ℕ) (hN : s + 3 ≤ N) :
    productOriginalStrongExponentPairSpace s N = productOriginalPairSpace s :=
  le_antisymm (productOriginalStrongExponentPairSpace_le_pair s N)
    (productOriginalPairSpace_le_strongExponentPairSpace s N hN)

theorem productOriginalStrongPairSpace_eq_pair (s : ℕ) :
    productOriginalStrongPairSpace s = productOriginalPairSpace s := by
  apply le_antisymm (productOriginalStrongPairSpace_le_pair s)
  intro T hT
  exact productOriginalPair_both_strong s ⟨T, hT⟩

/-- Exact strong finite-pair classification with no extra admission or
exhaustion hypotheses. Both original records are used in the source space. -/
def productOriginalStrongPairEquiv (s : ℕ) :
    productOriginalStrongPairSpace s ≃ₗ[ℂ] (productNumeratorIndex s → ℂ) :=
  (LinearEquiv.ofEq _ _ (productOriginalStrongPairSpace_eq_pair s)).trans
    (productOriginalPairEquiv s)

theorem productOriginalStrongPairSpace_finrank_eq (s : ℕ) :
    Module.finrank ℂ (productOriginalStrongPairSpace s) = (s + 1) ^ 2 - 1 := by
  simpa only [Module.finrank_fintype_fun_eq_card, productNumeratorIndex_card] using
    (productOriginalStrongPairEquiv s).finrank_eq

theorem productOriginalStrongExponentPairSpace_finrank_eq (s N : ℕ) (hN : s + 3 ≤ N) :
    Module.finrank ℂ (productOriginalStrongExponentPairSpace s N) = (s + 1) ^ 2 - 1 := by
  rw [productOriginalStrongExponentPairSpace_eq_pair s N hN,
    productOriginalPairSpace_finrank_eq]

end

end MeyerGeneralProblem.StrongParity

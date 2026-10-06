module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductAnnihilator
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductNumeratorSlab
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductReverseNumerator
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.ProductPairFiniteDimension

@[expose] public section

/-! Complete original ProductPairFiniteDimension for actual compact parameter blocks.
Every original supported pair is retained, without a constructed-image premise. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

open scoped SchwartzMap FourierTransform

/-- Every original atomic pair on the complete root and coarse-cone carriers. -/
def productOriginalPairSpace {s : ℕ} (block : CompactOriginalParameterBlock s) : Submodule ℂ (TemperedDistribution ℝ ℂ) :=
  schwartzAnnihilator (schwartzVanishingSubmodule (compactOriginalProductSheetCarrier block)) ⊓
    (schwartzAnnihilator (schwartzVanishingSubmodule spectralConeCarrier)).comap temperedFourierLinearMap

/-- Actual original slab coordinates: divide out the retained quarter phase. -/
def productOriginalPairNumeratorMap {s : ℕ} (block : CompactOriginalParameterBlock s) :
    productOriginalPairSpace block →ₗ[ℂ] (productNumeratorIndex s → ℂ) where
  toFun T ij := cutArrayNumerator rankTwoFrequencyHom (productLaurentCoefficients block) 0
      (originalFourierArray rankTwoFrequencyHom spectralConeCarrier T) (productNumeratorIntegerIndex s ij) /
    complexUnitPhase (-1 / 4) ^ (ij.val.2 : ℕ)
  map_add' T U := by
    funext ij
    simp only [Submodule.coe_add, originalFourierArray_add, cutArrayNumerator_add,
      Pi.add_apply, add_div]
  map_smul' c T := by
    funext ij
    simp only [Submodule.coe_smul, originalFourierArray_smul, cutArrayNumerator_smul,
      Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_div_assoc]

/-- The whole original pair space embeds in the finite original slab. -/
theorem productOriginalPairNumeratorMap_injective {s : ℕ} (block : CompactOriginalParameterBlock s) :
    Function.Injective (productOriginalPairNumeratorMap block) := by
  classical
  intro T U heq
  apply Subtype.ext
  apply product_originalFourierPair_cutNumerator_injective block T U T.property.1 U.property.1
    T.property.2 U.property.2 0
  funext n
  by_cases hsome :
      cutArrayNumerator rankTwoFrequencyHom (productLaurentCoefficients block) 0
        (originalFourierArray rankTwoFrequencyHom spectralConeCarrier T) n ≠ 0 ∨
      cutArrayNumerator rankTwoFrequencyHom (productLaurentCoefficients block) 0
        (originalFourierArray rankTwoFrequencyHom spectralConeCarrier U) n ≠ 0
  · have hb : 0 ≤ n.1 ∧ n.1 ≤ s ∧ 0 ≤ n.2 ∧ n.2 ≤ s ∧ n ≠ ((s : ℤ), (s : ℤ)) := by
      rcases hsome with h | h
      · exact product_originalCutNumerator_support_slab block T T.property.1 T.property.2 h
      · exact product_originalCutNumerator_support_slab block U U.property.1 U.property.2 h
    let i : Fin (s + 1) := ⟨n.1.toNat, by omega⟩
    let j : Fin (s + 1) := ⟨n.2.toNat, by omega⟩
    have hcorner : (i, j) ≠ (Fin.last s, Fin.last s) := by
      intro h
      have hi := congrArg (fun p : Fin (s + 1) × Fin (s + 1) => (p.1 : ℕ)) h
      have hj := congrArg (fun p : Fin (s + 1) × Fin (s + 1) => (p.2 : ℕ)) h
      apply hb.2.2.2.2
      apply Prod.ext <;> dsimp [i, j] at hi hj <;> omega
    let ij : productNumeratorIndex s := ⟨(i, j), hcorner⟩
    have hn : productNumeratorIntegerIndex s ij = n := by
      apply Prod.ext <;> dsimp [productNumeratorIntegerIndex, ij, i, j] <;> omega
    have h := congrFun heq ij
    change _ / complexUnitPhase (-1 / 4) ^ (ij.val.2 : ℕ) =
      _ / complexUnitPhase (-1 / 4) ^ (ij.val.2 : ℕ) at h
    have hphase : complexUnitPhase (-1 / 4) ^ (ij.val.2 : ℕ) ≠ 0 :=
      pow_ne_zero _ (Complex.exp_ne_zero _)
    rw [hn] at h
    exact (div_left_inj' hphase).mp h
  · push Not at hsome
    rw [hsome.1, hsome.2]

/-- A genuine finite-dimensional upper bound for the COMPLETE original pair
space, rather than only the span of forward constructed distributions. -/
theorem productOriginalPairSpace_finiteDimensional {s : ℕ} (block : CompactOriginalParameterBlock s) :
    FiniteDimensional ℂ (productOriginalPairSpace block) :=
  FiniteDimensional.of_injective (productOriginalPairNumeratorMap block)
    (productOriginalPairNumeratorMap_injective block)

/-- The complete original pair space obeys the exact finite slab upper bound. -/
theorem productOriginalPairSpace_finrank_le {s : ℕ} (block : CompactOriginalParameterBlock s) :
    Module.finrank ℂ (productOriginalPairSpace block) ≤ (s + 1) ^ 2 - 1 := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (f := productOriginalPairNumeratorMap block) (productOriginalPairNumeratorMap_injective block)
  simpa only [Module.finrank_fintype_fun_eq_card, productNumeratorIndex_card] using h

end

end MeyerGeneralProblem.StrongParity.CompactOriginal

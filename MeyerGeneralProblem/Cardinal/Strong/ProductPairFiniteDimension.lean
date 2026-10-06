module

public import MeyerGeneralProblem.Cardinal.Strong.ProductNumeratorSlab
public import MeyerGeneralProblem.Cardinal.Strong.ProductResidues
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

@[expose] public section

/-! The COMPLETE original supported pair space embeds in the actual finite
original numerator slab. The quarter-phase coordinate conversion is retained.
This upper bound does not assert surjectivity or infinite-carrier exhaustion. -/

namespace MeyerGeneralProblem

noncomputable section

open scoped SchwartzMap FourierTransform

variable {G : Type*} [AddCommGroup G]

theorem originalFourierArray_add (L : G →+ ℝ) (S : LocallyFiniteCarrier)
    (T U : TemperedDistribution ℝ ℂ) :
    originalFourierArray L S (T + U) = originalFourierArray L S T + originalFourierArray L S U := by
  classical
  funext n
  by_cases hx : L n ∈ S.carrier <;>
    simp [originalFourierArray, extendedAtomicCoefficient, hx, FourierTransform.fourier_add]

theorem originalFourierArray_smul (L : G →+ ℝ) (S : LocallyFiniteCarrier)
    (c : ℂ) (T : TemperedDistribution ℝ ℂ) :
    originalFourierArray L S (c • T) = c • originalFourierArray L S T := by
  classical
  funext n
  by_cases hx : L n ∈ S.carrier <;>
    simp [originalFourierArray, extendedAtomicCoefficient, hx, FourierTransform.fourier_smul]

theorem cutArrayNumerator_add (L : G →+ ℝ) (p : G →₀ ℂ) (s : ℝ) (u v : G → ℂ) :
    cutArrayNumerator L p s (u + v) = cutArrayNumerator L p s u + cutArrayNumerator L p s v := by
  classical
  have heq : arrayPositiveCut L s (u + v) = arrayPositiveCut L s u + arrayPositiveCut L s v := by
    funext n
    by_cases h : s ≤ L n <;> simp [arrayPositiveCut, h]
  funext n
  exact (congrFun (congrArg (annihilatorArrayConvolution p) heq) n).trans
    (annihilatorArrayConvolution_add p _ _ n)

theorem cutArrayNumerator_smul (L : G →+ ℝ) (p : G →₀ ℂ) (s : ℝ) (c : ℂ) (u : G → ℂ) :
    cutArrayNumerator L p s (c • u) = c • cutArrayNumerator L p s u := by
  classical
  funext n
  unfold cutArrayNumerator annihilatorArrayConvolution
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  by_cases h : s ≤ L (n - m) <;>
    simp only [arrayPositiveCut, h, ite_true, ite_false, Pi.smul_apply, smul_eq_mul]
  · ring
  · ring

namespace StrongParity

/-- Every original atomic pair on the complete root and coarse-cone carriers. -/
def productOriginalPairSpace (s : ℕ) : Submodule ℂ (TemperedDistribution ℝ ℂ) :=
  schwartzAnnihilator (schwartzVanishingSubmodule (productSheetCarrier s)) ⊓
    (schwartzAnnihilator (schwartzVanishingSubmodule spectralConeCarrier)).comap temperedFourierLinearMap

/-- The actual integer exponent represented by an original slab coordinate. -/
def productNumeratorIntegerIndex (s : ℕ) (ij : productNumeratorIndex s) : ℤ × ℤ :=
  ((ij.val.1 : ℕ), (ij.val.2 : ℕ))

/-- Actual original slab coordinates: divide out the retained quarter phase. -/
def productOriginalPairNumeratorMap (s : ℕ) :
    productOriginalPairSpace s →ₗ[ℂ] (productNumeratorIndex s → ℂ) where
  toFun T ij := cutArrayNumerator rankTwoFrequencyHom (productLaurentCoefficients s) 0
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
theorem productOriginalPairNumeratorMap_injective (s : ℕ) :
    Function.Injective (productOriginalPairNumeratorMap s) := by
  classical
  intro T U heq
  apply Subtype.ext
  apply product_originalFourierPair_cutNumerator_injective s T U T.property.1 U.property.1
    T.property.2 U.property.2 0
  funext n
  by_cases hsome :
      cutArrayNumerator rankTwoFrequencyHom (productLaurentCoefficients s) 0
        (originalFourierArray rankTwoFrequencyHom spectralConeCarrier T) n ≠ 0 ∨
      cutArrayNumerator rankTwoFrequencyHom (productLaurentCoefficients s) 0
        (originalFourierArray rankTwoFrequencyHom spectralConeCarrier U) n ≠ 0
  · have hb : 0 ≤ n.1 ∧ n.1 ≤ s ∧ 0 ≤ n.2 ∧ n.2 ≤ s ∧ n ≠ ((s : ℤ), (s : ℤ)) := by
      rcases hsome with h | h
      · exact product_originalCutNumerator_support_slab s T T.property.1 T.property.2 h
      · exact product_originalCutNumerator_support_slab s U U.property.1 U.property.2 h
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
theorem productOriginalPairSpace_finiteDimensional (s : ℕ) :
    FiniteDimensional ℂ (productOriginalPairSpace s) :=
  FiniteDimensional.of_injective (productOriginalPairNumeratorMap s)
    (productOriginalPairNumeratorMap_injective s)

theorem productNumeratorIndex_card (s : ℕ) :
    Fintype.card (productNumeratorIndex s) = (s + 1) ^ 2 - 1 := by
  change Fintype.card {ij : Fin (s + 1) × Fin (s + 1) // ¬ij = (Fin.last s, Fin.last s)} = _
  rw [Fintype.card_subtype_compl (fun ij : Fin (s + 1) × Fin (s + 1) =>
    ij = (Fin.last s, Fin.last s))]
  simp [pow_two]

/-- The complete original pair space obeys the exact finite slab upper bound. -/
theorem productOriginalPairSpace_finrank_le (s : ℕ) :
    Module.finrank ℂ (productOriginalPairSpace s) ≤ (s + 1) ^ 2 - 1 := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (f := productOriginalPairNumeratorMap s) (productOriginalPairNumeratorMap_injective s)
  simpa only [Module.finrank_fintype_fun_eq_card, productNumeratorIndex_card] using h

end StrongParity

end

end MeyerGeneralProblem

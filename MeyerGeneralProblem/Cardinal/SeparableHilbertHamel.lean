module

public import MeyerGeneralProblem.Atomic.RieszSynthesis
public import Mathlib.Analysis.Complex.Cardinality
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.SetTheory.Cardinal.Continuum

@[expose] public section

/-!
# Continuum Hamel bounds for countable coefficient and Hilbert spaces

This file isolates the cardinal arithmetic used by the dimension-classification layer.  It does
not refer to the Meyer filtration: later modules may apply these results to any subtype or linear
subspace once the corresponding coefficient-space representation has been proved.
-/

namespace MeyerGeneralProblem

noncomputable section

open Cardinal Set
open scoped lp

/-- The underlying set of the countable complex coefficient space has cardinality at most the
continuum. -/
theorem cardinalMk_coefficientSpace_nat_le_complex :
    Cardinal.mk (CoefficientSpace ℕ) ≤ Cardinal.mk ℂ := by
  calc
    Cardinal.mk (CoefficientSpace ℕ) ≤ Cardinal.mk (ℕ → ℂ) :=
      Cardinal.mk_le_of_injective Subtype.val_injective
    _ = Cardinal.mk ℂ ^ Cardinal.mk ℕ := by
      rw [Cardinal.mk_arrow, Cardinal.lift_id, Cardinal.lift_uzero]
    _ = Cardinal.continuum ^ Cardinal.aleph0 := by
      rw [Cardinal.mk_complex, Cardinal.mk_nat]
    _ = Cardinal.continuum := Cardinal.continuum_power_aleph0
    _ = Cardinal.mk ℂ := Cardinal.mk_complex.symm

/-- Any type which injects into the countable complex coefficient space has cardinality at most
the continuum. -/
theorem cardinalMk_le_complex_of_injective_to_coefficientSpace {X : Type}
    (f : X → CoefficientSpace ℕ) (hf : Function.Injective f) :
    Cardinal.mk X ≤ Cardinal.mk ℂ :=
  (Cardinal.mk_le_of_injective hf).trans cardinalMk_coefficientSpace_nat_le_complex

/-- In particular, every subtype of the countable complex coefficient space has cardinality at
most the continuum. -/
theorem cardinalMk_coefficientSpaceSubtype_le_complex (s : Set (CoefficientSpace ℕ)) :
    Cardinal.mk s ≤ Cardinal.mk ℂ :=
  cardinalMk_le_complex_of_injective_to_coefficientSpace Subtype.val Subtype.val_injective

/-- The same upper bound, specialized to a complex linear subspace. -/
theorem cardinalMk_coefficientSpaceSubmodule_le_complex
    (V : Submodule ℂ (CoefficientSpace ℕ)) : Cardinal.mk V ≤ Cardinal.mk ℂ :=
  cardinalMk_le_complex_of_injective_to_coefficientSpace Subtype.val Subtype.val_injective

/-- Every complex linear subspace of the countable coefficient space has Hamel dimension at most
the continuum. -/
theorem coefficientSpaceSubmodule_rank_le_complex (V : Submodule ℂ (CoefficientSpace ℕ)) :
    Module.rank ℂ V ≤ Cardinal.mk ℂ :=
  (rank_le_card ℂ V).trans (cardinalMk_coefficientSpaceSubmodule_le_complex V)

/-- The geometric sequence `(1, z, z², ...)`, viewed as a square-summable coefficient vector for
`0 < z < 1`.  Finite coordinate minors of this family are Vandermonde matrices. -/
def vandermondeCoefficientVector (z : Set.Ioo (0 : ℝ) 1) : CoefficientSpace ℕ :=
  ⟨(fun n ↦ (z.1 : ℂ) ^ n : PreLp (fun _ : ℕ ↦ ℂ)), by
    change Memℓp (fun n : ℕ ↦ (z.1 : ℂ) ^ n) 2
    rw [memℓp_gen_iff (by norm_num)]
    norm_num
    have hz : |z.1 ^ 2| < 1 := by
      rw [abs_pow, abs_of_pos z.2.1]
      nlinarith [z.2.1, z.2.2]
    have hfun :
        (fun n : ℕ ↦ (|z.1| ^ n) ^ (2 : ℕ)) = (fun n : ℕ ↦ (z.1 ^ 2) ^ n) := by
      funext n
      rw [abs_of_pos z.2.1]
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [hfun]
    exact summable_geometric_of_abs_lt_one hz⟩

@[simp]
theorem vandermondeCoefficientVector_apply (z : Set.Ioo (0 : ℝ) 1) (n : ℕ) :
    vandermondeCoefficientVector z n = (z.1 : ℂ) ^ n :=
  rfl

/-- The multiplicative character whose values are the coordinates of
`vandermondeCoefficientVector`. -/
def geometricCharacter (z : ℂ) : Multiplicative ℕ →* ℂ where
  toFun n := z ^ n.toAdd
  map_one' := by simp
  map_mul' m n := by simp [pow_add]

private theorem geometricCharacter_injective :
    Function.Injective (fun z : Set.Ioo (0 : ℝ) 1 ↦ geometricCharacter (z.1 : ℂ)) := by
  intro z w h
  apply Subtype.ext
  have hzw := DFunLike.congr_fun h (Multiplicative.ofAdd 1)
  simpa [geometricCharacter] using hzw

/-- Forget square summability and reindex a coefficient vector by the multiplicative copy of
`ℕ`. -/
def coefficientSequenceLinearMap :
    CoefficientSpace ℕ →ₗ[ℂ] (Multiplicative ℕ → ℂ) where
  toFun c n := c n.toAdd
  map_add' x y := by
    ext n
    rfl
  map_smul' c x := by
    ext n
    rfl

/-- The continuum-sized geometric family is linearly independent.  Dedekind independence of
multiplicative characters is the coordinate-free Vandermonde argument: restricting to any finite
subfamily evaluates to the usual nonsingular Vandermonde system. -/
theorem linearIndependent_vandermondeCoefficientVector :
    LinearIndependent ℂ vandermondeCoefficientVector := by
  apply LinearIndependent.of_comp coefficientSequenceLinearMap
  have hcharacters : LinearIndependent ℂ
      (fun z : Set.Ioo (0 : ℝ) 1 ↦
        (geometricCharacter (z.1 : ℂ) : Multiplicative ℕ → ℂ)) :=
    (linearIndependent_monoidHom (Multiplicative ℕ) ℂ).comp
      (fun z : Set.Ioo (0 : ℝ) 1 ↦ geometricCharacter (z.1 : ℂ))
      geometricCharacter_injective
  simpa [Function.comp_def, coefficientSequenceLinearMap, vandermondeCoefficientVector,
    geometricCharacter] using hcharacters

/-- The countable complex coefficient space has Hamel dimension at least the continuum. -/
theorem complex_le_coefficientSpace_nat_rank :
    Cardinal.mk ℂ ≤ Module.rank ℂ (CoefficientSpace ℕ) := by
  calc
    Cardinal.mk ℂ = Cardinal.continuum := Cardinal.mk_complex
    _ = Cardinal.mk (Set.Ioo (0 : ℝ) 1) := (Cardinal.mk_Ioo_real zero_lt_one).symm
    _ ≤ Module.rank ℂ (CoefficientSpace ℕ) :=
      linearIndependent_vandermondeCoefficientVector.cardinal_le_rank

/-- The countable complex coefficient space has Hamel dimension at most the continuum. -/
theorem coefficientSpace_nat_rank_le_complex :
    Module.rank ℂ (CoefficientSpace ℕ) ≤ Cardinal.mk ℂ :=
  (rank_le_card ℂ (CoefficientSpace ℕ)).trans cardinalMk_coefficientSpace_nat_le_complex

/-- The Hamel dimension of the countable complex coefficient space is exactly the continuum. -/
theorem coefficientSpace_nat_rank_eq_complex :
    Module.rank ℂ (CoefficientSpace ℕ) = Cardinal.mk ℂ :=
  le_antisymm coefficientSpace_nat_rank_le_complex complex_le_coefficientSpace_nat_rank

/-- An injective linear copy of the countable complex coefficient space forces continuum Hamel
dimension in its codomain. -/
theorem complex_le_rank_of_coefficientSpace_injection
    {H : Type} [AddCommGroup H] [Module ℂ H]
    (T : CoefficientSpace ℕ →ₗ[ℂ] H) (hT : Function.Injective T) :
    Cardinal.mk ℂ ≤ Module.rank ℂ H := by
  have hLI : LinearIndependent ℂ (T ∘ vandermondeCoefficientVector) :=
    linearIndependent_vandermondeCoefficientVector.map' T
      (LinearMap.ker_eq_bot.mpr hT)
  calc
    Cardinal.mk ℂ = Cardinal.continuum := Cardinal.mk_complex
    _ = Cardinal.mk (Set.Ioo (0 : ℝ) 1) := (Cardinal.mk_Ioo_real zero_lt_one).symm
    _ ≤ Module.rank ℂ H := hLI.cardinal_le_rank

/-- Every infinite-dimensional complex Hilbert space has Hamel dimension at least the continuum.

The proof chooses a Hilbert basis, extracts a countable orthonormal subfamily, embeds
`CoefficientSpace ℕ` isometrically, and transports the explicit Vandermonde family above. -/
theorem complex_le_rank_of_infiniteDimensional_complexHilbert
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (hH : ¬FiniteDimensional ℂ H) : Cardinal.mk ℂ ≤ Module.rank ℂ H := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ H
  let _ : Infinite w := not_finite_iff_infinite.mp fun hw ↦ by
    let _ : Finite w := hw
    let _ : Fintype w := Fintype.ofFinite w
    exact hH b.toOrthonormalBasis.toBasis.finiteDimensional_of_finite
  let e : ℕ ↪ w := Infinite.natEmbedding w
  have hv : Orthonormal ℂ (b ∘ e) := b.orthonormal.comp e e.injective
  let T : CoefficientSpace ℕ →ₗᵢ[ℂ] H := hv.orthogonalFamily.linearIsometry
  exact complex_le_rank_of_coefficientSpace_injection T.toLinearMap T.injective

end

end MeyerGeneralProblem

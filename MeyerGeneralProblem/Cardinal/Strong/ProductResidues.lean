module

public import MeyerGeneralProblem.Cardinal.Strong.ProductSeparation

@[expose] public section

/-!
# Absolute weighted residues on the complete original finite carrier

The complete product root set is identified with the disjoint union of
its literal sheets. The finite Newton slab is evaluated on unit phases,
and the proved denominator bounds give absolute weighted summability
of the original physical residues. A Fourier identity is not asserted
by this module.
-/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- A sheet root as an actual root of the full original product. -/
def productSheetRootInclusion (s : ℕ) (i : Fin s)
    (x : (sheetCarrier (productSheetParameter s i)
      (productSheetParameter_bounds s i).1.le (productSheetParameter_bounds s i).2).subtype) :
    (productSheetCarrier s).subtype :=
  ⟨x, by
    change (x : ℝ) ∈ productSheetRoots s
    rw [productSheetRoots_eq_union]
    exact Set.mem_iUnion.mpr ⟨i, x.property⟩⟩

/-- The disjoint union contains every root, with no multiplicity. -/
def productSheetRootUnion (s : ℕ)
    (x : Σ i : Fin s, (sheetCarrier (productSheetParameter s i)
      (productSheetParameter_bounds s i).1.le (productSheetParameter_bounds s i).2).subtype) :
    (productSheetCarrier s).subtype := productSheetRootInclusion s x.1 x.2

theorem productSheetRootUnion_bijective (s : ℕ) :
    Function.Bijective (productSheetRootUnion s) := by
  constructor
  · rintro ⟨i, x⟩ ⟨j, y⟩ heq
    have hxy : (x : ℝ) = (y : ℝ) :=
      congrArg (fun t : (productSheetCarrier s).subtype => (t : ℝ)) heq
    have hij : i = j := by
      by_contra hne
      have hab : (productSheetParameter s i : ℂ) ≠ (productSheetParameter s j : ℂ) := by
        intro h
        exact hne ((productSheetParameter_injective s) (Complex.ofReal_inj.mp h))
      have hdis := quarterFlow_sheet_roots_disjoint hab (x : ℝ) x.property
      apply hdis
      have hy : sheetFlow (productSheetParameter s j) y = 0 := y.property
      simpa only [hxy, sheetFlow] using hy
    subst j
    congr 1
    exact Subtype.ext hxy
  · intro x
    have hx : (x : ℝ) ∈ ⋃ i : Fin s, sheetRoots (productSheetParameter s i) := by
      rw [← productSheetRoots_eq_union]
      exact x.property
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact ⟨⟨i, ⟨x, hi⟩⟩, Subtype.ext rfl⟩

/-- Nonnegative summability over the complete carrier is exactly
summability over each of its finitely many actual sheets. -/
theorem productSheetCarrier_summable_iff (s : ℕ)
    (f : (productSheetCarrier s).subtype → ℝ) (hf : ∀ x, 0 ≤ f x) :
    Summable f ↔ ∀ i : Fin s, Summable (fun x => f (productSheetRootInclusion s i x)) := by
  let e := Equiv.ofBijective (productSheetRootUnion s) (productSheetRootUnion_bijective s)
  rw [← e.summable_iff]
  exact (summable_sigma_of_nonneg (fun x => hf (e x))).trans
    (and_iff_left (hasSum_fintype _).summable)

/-- The original square Newton slab, with its upper corner deleted. -/
def productNumeratorIndex (s : ℕ) :=
  {ij : Fin (s + 1) × Fin (s + 1) // ij ≠ (Fin.last s, Fin.last s)}

instance (s : ℕ) : Fintype (productNumeratorIndex s) := by
  unfold productNumeratorIndex
  infer_instance

/-- The complete literal finite slab numerator evaluated on the original flow. -/
def productSlabNumerator (s : ℕ) (r : productNumeratorIndex s → ℂ) (x : ℝ) : ℂ :=
  ∑ ij, r ij * unitPhase x ^ (ij.val.1 : ℕ) *
    unitPhase (beta * x - 1 / 4) ^ (ij.val.2 : ℕ)

/-- The finite sum of original slab coefficient norms bounds its torus values. -/
def productSlabCoefficientBound (s : ℕ) (r : productNumeratorIndex s → ℂ) : ℝ :=
  ∑ ij, ‖r ij‖

theorem productSlabNumerator_norm_upper (s : ℕ) (r : productNumeratorIndex s → ℂ) (x : ℝ) :
    ‖productSlabNumerator s r x‖ ≤ productSlabCoefficientBound s r := by
  unfold productSlabNumerator productSlabCoefficientBound
  calc
    _ ≤ ∑ ij, ‖r ij * unitPhase x ^ (ij.val.1 : ℕ) *
        unitPhase (beta * x - 1 / 4) ^ (ij.val.2 : ℕ)‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, norm_pow, unitPhase_norm, one_pow, mul_one]

/-- The actual original physical residue, with its torus derivative denominator. -/
def productPhysicalResidue (s : ℕ) (r : productNumeratorIndex s → ℂ)
    (x : (productSheetCarrier s).subtype) : ℂ :=
  -productSlabNumerator s r x / productSheetTorusDerivative s
    (unitPhase x) (unitPhase (beta * x - 1 / 4))

/-- Every slab residue has absolute polynomial weighted summability
on the COMPLETE product root carrier, at exponent `(s-1)+2`. -/
theorem productPhysicalResidue_weight_summable (s : ℕ) (r : productNumeratorIndex s → ℂ) :
    Summable (fun x : (productSheetCarrier s).subtype =>
      ‖productPhysicalResidue s r x‖ / (1 + |(x : ℝ)|) ^ ((s - 1) + 2)) := by
  apply (productSheetCarrier_summable_iff s _ (fun x => by positivity)).mpr
  intro i
  apply sheetCarrier_polynomial_weight_summable
    (productSheetParameter_bounds s i).1.le (productSheetParameter_bounds s i).2
    (fun x => productPhysicalResidue s r (productSheetRootInclusion s i x))
    (productSlabCoefficientBound s r * productSheetResidueConstant s i) (s - 1)
  intro x
  exact productSheetResidue_norm_upper s i x x.property
    (productSlabNumerator s r x) (productSlabCoefficientBound s r)
    (productSlabNumerator_norm_upper s r x)

end

end MeyerGeneralProblem.StrongParity

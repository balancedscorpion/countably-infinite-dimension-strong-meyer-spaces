module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.Interface
public import MeyerGeneralProblem.Cardinal.Strong.ProductResidues
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductSeparation

@[expose] public section

/-! Original ProductResidues for actual compact parameter blocks.
The literal full numerator slab and original records are retained. -/

namespace MeyerGeneralProblem.StrongParity.CompactOriginal

noncomputable section

/-- A sheet root as an actual root of the full original product. -/
def productSheetRootInclusion {s : ℕ} (block : CompactOriginalParameterBlock s) (i : Fin s)
    (x : (sheetCarrier (block.parameter i)
      (block.parameter_bounds i).1.le (block.parameter_bounds i).2).subtype) :
    (compactOriginalProductSheetCarrier block).subtype :=
  ⟨x, by
    change (x : ℝ) ∈ compactOriginalProductSheetRoots block
    rw [compactOriginalProductSheetRoots_eq_union block]
    exact Set.mem_iUnion.mpr ⟨i, x.property⟩⟩

/-- The disjoint union contains every root, with no multiplicity. -/
def productSheetRootUnion {s : ℕ} (block : CompactOriginalParameterBlock s)
    (x : Σ i : Fin s, (sheetCarrier (block.parameter i)
      (block.parameter_bounds i).1.le (block.parameter_bounds i).2).subtype) :
    (compactOriginalProductSheetCarrier block).subtype := productSheetRootInclusion block x.1 x.2

theorem productSheetRootUnion_bijective {s : ℕ} (block : CompactOriginalParameterBlock s) :
    Function.Bijective (productSheetRootUnion block) := by
  constructor
  · rintro ⟨i, x⟩ ⟨j, y⟩ heq
    have hxy : (x : ℝ) = (y : ℝ) :=
      congrArg (fun t : (compactOriginalProductSheetCarrier block).subtype => (t : ℝ)) heq
    have hij : i = j := by
      by_contra hne
      have hab : (block.parameter i : ℂ) ≠ (block.parameter j : ℂ) := by
        intro h
        exact hne ((block.injective) (Complex.ofReal_inj.mp h))
      have hdis := quarterFlow_sheet_roots_disjoint hab (x : ℝ) x.property
      apply hdis
      have hy : sheetFlow (block.parameter j) y = 0 := y.property
      simpa only [hxy, sheetFlow] using hy
    subst j
    congr 1
    exact Subtype.ext hxy
  · intro x
    have hx : (x : ℝ) ∈ ⋃ i : Fin s, sheetRoots (block.parameter i) := by
      rw [← compactOriginalProductSheetRoots_eq_union block]
      exact x.property
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact ⟨⟨i, ⟨x, hi⟩⟩, Subtype.ext rfl⟩

/-- Nonnegative summability over the complete carrier is exactly
summability over each of its finitely many actual sheets. -/
theorem productSheetCarrier_summable_iff {s : ℕ} (block : CompactOriginalParameterBlock s)
    (f : (compactOriginalProductSheetCarrier block).subtype → ℝ) (hf : ∀ x, 0 ≤ f x) :
    Summable f ↔ ∀ i : Fin s, Summable (fun x => f (productSheetRootInclusion block i x)) := by
  let e := Equiv.ofBijective (productSheetRootUnion block) (productSheetRootUnion_bijective block)
  rw [← e.summable_iff]
  exact (summable_sigma_of_nonneg (fun x => hf (e x))).trans
    (and_iff_left (hasSum_fintype _).summable)

/-- The actual original physical residue, with its torus derivative denominator. -/
def productPhysicalResidue {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ)
    (x : (compactOriginalProductSheetCarrier block).subtype) : ℂ :=
  -productSlabNumerator s r x / compactOriginalSheetTorusDerivative block
    (unitPhase x) (unitPhase (beta * x - 1 / 4))

/-- Every slab residue has absolute polynomial weighted summability
on the COMPLETE product root carrier, at exponent `(s-1)+2`. -/
theorem productPhysicalResidue_weight_summable {s : ℕ} (block : CompactOriginalParameterBlock s) (r : productNumeratorIndex s → ℂ) :
    Summable (fun x : (compactOriginalProductSheetCarrier block).subtype =>
      ‖productPhysicalResidue block r x‖ / (1 + |(x : ℝ)|) ^ ((s - 1) + 2)) := by
  apply (productSheetCarrier_summable_iff block _ (fun x => by positivity)).mpr
  intro i
  apply sheetCarrier_polynomial_weight_summable
    (block.parameter_bounds i).1.le (block.parameter_bounds i).2
    (fun x => productPhysicalResidue block r (productSheetRootInclusion block i x))
    (productSlabCoefficientBound s r * productSheetResidueConstant block i) (s - 1)
  intro x
  exact productSheetResidue_norm_upper block i x x.property
    (productSlabNumerator s r x) (productSlabCoefficientBound s r)
    (productSlabNumerator_norm_upper s r x)

end

end MeyerGeneralProblem.StrongParity.CompactOriginal

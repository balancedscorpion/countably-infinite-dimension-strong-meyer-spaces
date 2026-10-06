module

public import MeyerGeneralProblem.Cardinal.Strong.ComputedOriginalWRootExistence
public import MeyerGeneralProblem.Cardinal.Strong.RationalComplexApartness
public import Mathlib.Logic.Encodable.Pi
public import Mathlib.Data.Nat.Find

@[expose] public section

/-! An ordinary sequential search over ALL exact-size original-root tuples and
binary precisions. Termination is proved from the full algebraic original W
rank, the bijective native root labels and the complete determinant error bound. -/

namespace MeyerGeneralProblem.StrongParity

/-- Explicit encoding of the top-deleted original finite numerator box. -/
instance originalNumeratorIndex_encodable (s : ℕ) : Encodable (productNumeratorIndex s) := by
  unfold productNumeratorIndex
  infer_instance

/-- Bounded original coordinates and the computed finite mask have ordinary encodings. -/
instance computedOriginalWIndex_encodable (s : ℕ) (hs : 2 ≤ s) (m : ℕ) :
    Encodable (computedOriginalWIndex s hs m) := inferInstance

/-- Ordinary decoded exact-size root tuple and precision test. Both distinctness
and the full Gaussian-rational determinant margin are decided internally. -/
def coupledComputedOriginalWRootProbe (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (m code : ℕ) : Bool :=
  match (Encodable.decode code : Option ((computedOriginalWIndex s hs m → Fin s × ℤ) × ℕ)) with
  | none => false
  | some (roots, p) => decide (Function.Injective roots) &&
      rationalComplexApart (coupledComputedOriginalWRootDetName scales hpos offset s hs m roots p) p

noncomputable section

/-- A passing implemented probe decodes a distinct full-size tuple with a literal
strict rational determinant margin. -/
theorem coupledComputedOriginalWRootProbe_spec (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (m code : ℕ)
    (hk : coupledComputedOriginalWRootProbe scales hpos offset s hs m code = true) :
    ∃ roots : computedOriginalWIndex s hs m → Fin s × ℤ, ∃ p : ℕ,
      (Encodable.decode code : Option ((computedOriginalWIndex s hs m → Fin s × ℤ) × ℕ)) =
        some (roots, p) ∧ Function.Injective roots ∧
        rationalComplexApart (coupledComputedOriginalWRootDetName scales hpos offset s hs m roots p) p = true := by
  unfold coupledComputedOriginalWRootProbe at hk
  cases hd : (Encodable.decode code : Option ((computedOriginalWIndex s hs m → Fin s × ℤ) × ℕ)) with
  | none => simp only [hd, Bool.false_eq_true] at hk
  | some pair =>
    rcases pair with ⟨roots, p⟩
    simp only [hd, Bool.and_eq_true, decide_eq_true_eq] at hk
    exact ⟨roots, p, rfl, hk.1, hk.2⟩

/-- Actual ENTIRE original W rank pays termination of the ordinary exact-size
root/determinant search. No external certificate or rank decision is an input. -/
theorem coupledComputedOriginalWRootProbe_exists (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) :
    ∃ code, coupledComputedOriginalWRootProbe scales hpos offset s hs m code = true := by
  obtain ⟨roots, hi, hd⟩ := coupledComputedOriginalWRootMatrix_det_ne_zero_exists scales hpos offset s hs m
  obtain ⟨p, hp⟩ := (rationalComplexApart_eventually
    (coupledComputedOriginalWRootDetName scales hpos offset s hs m roots)
    (coupledComputedOriginalWRootDetName_error scales hpos offset s hs m roots) hd).exists
  refine ⟨Encodable.encode (roots, p), ?_⟩
  simp only [coupledComputedOriginalWRootProbe, Encodable.encodek, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hi, hp⟩

end

/-- Ordinary sequential exhaustive root/determinant search, with internally proved termination. -/
def coupledComputedOriginalWRootSearchCode (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) : ℕ :=
  Nat.find (coupledComputedOriginalWRootProbe_exists scales hpos offset s hs m)

/-- The ordinary search returns a passing finite probe. -/
theorem coupledComputedOriginalWRootSearchCode_spec (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) :
    coupledComputedOriginalWRootProbe scales hpos offset s hs m
      (coupledComputedOriginalWRootSearchCode scales hpos offset s hs m) = true :=
  Nat.find_spec (coupledComputedOriginalWRootProbe_exists scales hpos offset s hs m)

/-- The implemented terminating search returns the actual decoded tuple and precision,
with no fallback value and no classical choice in the data program. -/
def coupledComputedOriginalWSelectedRoots (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) : (computedOriginalWIndex s hs m → Fin s × ℤ) × ℕ :=
  (Encodable.decode (coupledComputedOriginalWRootSearchCode scales hpos offset s hs m)).get (by
    obtain ⟨roots, p, hd, _, _⟩ := coupledComputedOriginalWRootProbe_spec scales hpos offset s hs m
      (coupledComputedOriginalWRootSearchCode scales hpos offset s hs m)
      (coupledComputedOriginalWRootSearchCode_spec scales hpos offset s hs m)
    simp only [hd, Option.isSome_some])

/-- The implemented exact-size deletion labels are a finite ordinary list-set. -/
def coupledComputedOriginalWSelectedLabels (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) : Finset (Fin s × ℤ) :=
  Finset.univ.image (coupledComputedOriginalWSelectedRoots scales hpos offset s hs m).1

noncomputable section

/-- The ordinary selected tuple is distinct and its ENTIRE ACTUAL original
physical-row matrix on the ENTIRE W basis has nonzero determinant. -/
theorem coupledComputedOriginalWSelectedRoots_spec (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) :
    Function.Injective (coupledComputedOriginalWSelectedRoots scales hpos offset s hs m).1 ∧
      Matrix.det (coupledComputedOriginalWRootMatrix scales hpos offset s hs m
        (coupledComputedOriginalWSelectedRoots scales hpos offset s hs m).1) ≠ 0 := by
  obtain ⟨roots, p, hd, hi, hm⟩ := coupledComputedOriginalWRootProbe_spec scales hpos offset s hs m
    (coupledComputedOriginalWRootSearchCode scales hpos offset s hs m)
    (coupledComputedOriginalWRootSearchCode_spec scales hpos offset s hs m)
  have heq : coupledComputedOriginalWSelectedRoots scales hpos offset s hs m = (roots, p) := by
    simp only [coupledComputedOriginalWSelectedRoots, hd, Option.get_some]
  rw [heq]
  exact ⟨hi, rationalComplexApart_sound
    (coupledComputedOriginalWRootDetName_error scales hpos offset s hs m roots p) hm⟩

/-- The implemented root-deletion set has exactly the full proved W dimension,
including EVERY original noncoarse forbidden-head constraint. -/
theorem coupledComputedOriginalWSelectedLabels_card (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) :
    (coupledComputedOriginalWSelectedLabels scales hpos offset s hs m).card +
      (computedOriginalNoncoarseHeadLabels s m).card + 2 = (s + 1) ^ 2 := by
  rw [coupledComputedOriginalWSelectedLabels, Finset.card_image_of_injective _
    (coupledComputedOriginalWSelectedRoots_spec scales hpos offset s hs m).1, Finset.card_univ]
  exact computedOriginalWIndex_card (coupledCompactOriginalParameterBlock scales hpos offset s) hs m

end

end MeyerGeneralProblem.StrongParity

module

public import MeyerGeneralProblem.Carrier.UniformDensity
public import Mathlib.Data.Set.SymmDiff

@[expose] public section

/-!
# Uniform density under finite extensional modifications

This file uses finite symmetric difference of the physical carrier sets.  It
is independent of the legacy indexwise tail-equivalence relation for ordered
two-sided enumerations.
-/

namespace MeyerGeneralProblem

open scoped symmDiff

namespace LocallyFiniteCarrier

/-- Two extensional carriers differ at only finitely many physical nodes. -/
def FiniteSymmetricDifference (S T : LocallyFiniteCarrier) : Prop :=
  (S.carrier ∆ T.carrier).Finite

/-- Extensional tail equivalence is finite symmetric difference of carriers. -/
abbrev TailEquivalent (S T : LocallyFiniteCarrier) : Prop :=
  S.FiniteSymmetricDifference T

/-- The total number of exceptional physical nodes.  This is used only under
a proof that the symmetric difference is finite. -/
noncomputable def finiteDifferenceCard (S T : LocallyFiniteCarrier) : ℕ :=
  Set.ncard (S.carrier ∆ T.carrier)

namespace TailEquivalent

variable {S T U : LocallyFiniteCarrier}

theorem refl (S : LocallyFiniteCarrier) : S.TailEquivalent S := by
  unfold TailEquivalent FiniteSymmetricDifference
  rw [symmDiff_self]
  exact Set.finite_empty

theorem symm (h : S.TailEquivalent T) : T.TailEquivalent S := by
  unfold TailEquivalent FiniteSymmetricDifference at h ⊢
  rwa [symmDiff_comm]

theorem trans (hST : S.TailEquivalent T) (hTU : T.TailEquivalent U) :
    S.TailEquivalent U := by
  unfold TailEquivalent FiniteSymmetricDifference at hST hTU ⊢
  exact (hST.union hTU).subset (symmDiff_triangle S.carrier T.carrier U.carrier)

/-- A window count for `S` exceeds the corresponding count for `T` by at
most the total number of exceptional nodes. -/
theorem windowCount_le_add (h : S.TailEquivalent T) (a L : ℝ) :
    windowCount S a L ≤ windowCount T a L + S.finiteDifferenceCard T := by
  let W : Set ℝ := Set.Ico a (a + L)
  have hsubset :
      S.carrier ∩ W ⊆ (T.carrier ∩ W) ∪ (S.carrier ∆ T.carrier) := by
    intro x hx
    by_cases hxT : x ∈ T.carrier
    · exact Or.inl ⟨hxT, hx.2⟩
    · exact Or.inr (Set.mem_symmDiff.mpr (Or.inl ⟨hx.1, hxT⟩))
  have htarget :
      ((T.carrier ∩ W) ∪ (S.carrier ∆ T.carrier)).Finite :=
    (T.finite_window a L).union h
  calc
    windowCount S a L = Set.ncard (S.carrier ∩ W) := rfl
    _ ≤ Set.ncard ((T.carrier ∩ W) ∪ (S.carrier ∆ T.carrier)) :=
      Set.ncard_le_ncard hsubset htarget
    _ ≤ Set.ncard (T.carrier ∩ W) + Set.ncard (S.carrier ∆ T.carrier) :=
      Set.ncard_union_le _ _
    _ = windowCount T a L + S.finiteDifferenceCard T := rfl

/-- Symmetric uniform window-count discrepancy bound. -/
theorem windowCount_discrepancy (h : S.TailEquivalent T) (a L : ℝ) :
    windowCount S a L ≤ windowCount T a L + S.finiteDifferenceCard T ∧
      windowCount T a L ≤ windowCount S a L + S.finiteDifferenceCard T := by
  refine ⟨h.windowCount_le_add a L, ?_⟩
  simpa [finiteDifferenceCard, symmDiff_comm] using
    h.symm.windowCount_le_add a L

/-- Strict uniform lower-density estimates survive finite extensional
modification. -/
theorem uniformLowerDensityGT (h : S.TailEquivalent T) {c : ℝ}
    (hS : UniformLowerDensityGT S c) : UniformLowerDensityGT T c := by
  rcases hS with ⟨ε, hε, L₀, hL₀, hbound⟩
  let C : ℝ := S.finiteDifferenceCard T
  have hC : 0 ≤ C := by positivity
  refine ⟨ε / 2, half_pos hε, max L₀ (2 * C / ε),
    hL₀.trans_le (le_max_left _ _), ?_⟩
  intro L hL a
  have hL₀L : L₀ ≤ L := (le_max_left _ _).trans hL
  have hratio : 2 * C / ε ≤ L := (le_max_right _ _).trans hL
  have hCle : C ≤ (ε / 2) * L := by
    calc
      C = (ε / 2) * (2 * C / ε) := by field_simp
      _ ≤ (ε / 2) * L := mul_le_mul_of_nonneg_left hratio (half_pos hε).le
  have hdiscrepancyNat := h.windowCount_le_add a L
  have hdiscrepancy :
      (windowCount S a L : ℝ) ≤ (windowCount T a L : ℝ) + C := by
    dsimp [C]
    exact_mod_cast hdiscrepancyNat
  have hlower := hbound L hL₀L a
  nlinarith

/-- Strict uniform upper-density estimates survive finite extensional
modification. -/
theorem uniformUpperDensityLT (h : S.TailEquivalent T) {c : ℝ}
    (hS : UniformUpperDensityLT S c) : UniformUpperDensityLT T c := by
  rcases hS with ⟨ε, hε, L₀, hL₀, hbound⟩
  let C : ℝ := S.finiteDifferenceCard T
  have hC : 0 ≤ C := by positivity
  refine ⟨ε / 2, half_pos hε, max L₀ (2 * C / ε),
    hL₀.trans_le (le_max_left _ _), ?_⟩
  intro L hL a
  have hL₀L : L₀ ≤ L := (le_max_left _ _).trans hL
  have hratio : 2 * C / ε ≤ L := (le_max_right _ _).trans hL
  have hCle : C ≤ (ε / 2) * L := by
    calc
      C = (ε / 2) * (2 * C / ε) := by field_simp
      _ ≤ (ε / 2) * L := mul_le_mul_of_nonneg_left hratio (half_pos hε).le
  have hdiscrepancyNat := (h.windowCount_discrepancy a L).2
  have hdiscrepancy :
      (windowCount T a L : ℝ) ≤ (windowCount S a L : ℝ) + C := by
    dsimp [C]
    exact_mod_cast hdiscrepancyNat
  have hupper := hbound L hL₀L a
  calc
    (windowCount T a L : ℝ) ≤ (windowCount S a L : ℝ) + C := hdiscrepancy
    _ ≤ (c - ε) * L + C := by linarith
    _ ≤ (c - ε / 2) * L := by nlinarith

theorem uniformLowerDensityGT_iff (h : S.TailEquivalent T) (c : ℝ) :
    UniformLowerDensityGT S c ↔ UniformLowerDensityGT T c :=
  ⟨h.uniformLowerDensityGT, h.symm.uniformLowerDensityGT⟩

theorem uniformUpperDensityLT_iff (h : S.TailEquivalent T) (c : ℝ) :
    UniformUpperDensityLT S c ↔ UniformUpperDensityLT T c :=
  ⟨h.uniformUpperDensityLT, h.symm.uniformUpperDensityLT⟩

/-- Lower uniform Beurling density is invariant under finite symmetric
difference. -/
theorem lowerDensity_eq (h : S.TailEquivalent T) :
    lowerUniformBeurlingDensity S = lowerUniformBeurlingDensity T := by
  apply eq_of_forall_lt_iff
  intro z
  cases z with
  | top => simp
  | coe r =>
      rw [ENNReal.coe_nnreal_eq]
      rw [← uniformLowerDensityGT_iff_lt_lowerUniformBeurlingDensity S
          (show 0 ≤ (r : ℝ) by positivity),
        ← uniformLowerDensityGT_iff_lt_lowerUniformBeurlingDensity T
          (show 0 ≤ (r : ℝ) by positivity)]
      exact h.uniformLowerDensityGT_iff (r : ℝ)

/-- Upper uniform Beurling density is invariant under finite symmetric
difference. -/
theorem upperDensity_eq (h : S.TailEquivalent T) :
    upperUniformBeurlingDensity S = upperUniformBeurlingDensity T := by
  apply eq_of_forall_gt_iff
  intro z
  cases z with
  | top =>
      constructor
      · intro hStop
        obtain ⟨r, hSr, hrTop⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hStop
        have hTr : upperUniformBeurlingDensity T < (r : ENNReal) := by
          rw [ENNReal.coe_nnreal_eq] at hSr ⊢
          have hSr' : UniformUpperDensityLT S (r : ℝ) :=
            (uniformUpperDensityLT_iff_upperUniformBeurlingDensity_lt S
              (show 0 ≤ (r : ℝ) by positivity)).2 hSr
          exact (uniformUpperDensityLT_iff_upperUniformBeurlingDensity_lt T
            (show 0 ≤ (r : ℝ) by positivity)).1
              ((h.uniformUpperDensityLT_iff (r : ℝ)).1 hSr')
        exact hTr.trans hrTop
      · intro hTtop
        obtain ⟨r, hTr, hrTop⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hTtop
        have hSr : upperUniformBeurlingDensity S < (r : ENNReal) := by
          rw [ENNReal.coe_nnreal_eq] at hTr ⊢
          have hTr' : UniformUpperDensityLT T (r : ℝ) :=
            (uniformUpperDensityLT_iff_upperUniformBeurlingDensity_lt T
              (show 0 ≤ (r : ℝ) by positivity)).2 hTr
          exact (uniformUpperDensityLT_iff_upperUniformBeurlingDensity_lt S
            (show 0 ≤ (r : ℝ) by positivity)).1
              ((h.uniformUpperDensityLT_iff (r : ℝ)).2 hTr')
        exact hSr.trans hrTop
  | coe r =>
      rw [ENNReal.coe_nnreal_eq]
      rw [← uniformUpperDensityLT_iff_upperUniformBeurlingDensity_lt S
          (show 0 ≤ (r : ℝ) by positivity),
        ← uniformUpperDensityLT_iff_upperUniformBeurlingDensity_lt T
          (show 0 ≤ (r : ℝ) by positivity)]
      exact h.uniformUpperDensityLT_iff (r : ℝ)

/-- Explicit lower-density finite-modification law. -/
theorem density_finiteModification_lower (h : S.TailEquivalent T) :
    lowerUniformBeurlingDensity S = lowerUniformBeurlingDensity T :=
  h.lowerDensity_eq

/-- Explicit upper-density finite-modification law. -/
theorem density_finiteModification_upper (h : S.TailEquivalent T) :
    upperUniformBeurlingDensity S = upperUniformBeurlingDensity T :=
  h.upperDensity_eq

/-- Both numerical uniform densities are unchanged by a finite extensional
modification. -/
theorem density_finiteModification (h : S.TailEquivalent T) :
    lowerUniformBeurlingDensity S = lowerUniformBeurlingDensity T ∧
      upperUniformBeurlingDensity S = upperUniformBeurlingDensity T :=
  ⟨h.lowerDensity_eq, h.upperDensity_eq⟩

theorem lowerDensity_gt_one_iff (h : S.TailEquivalent T) :
    1 < lowerUniformBeurlingDensity S ↔ 1 < lowerUniformBeurlingDensity T := by
  rw [h.lowerDensity_eq]

theorem upperDensity_lt_one_iff (h : S.TailEquivalent T) :
    upperUniformBeurlingDensity S < 1 ↔ upperUniformBeurlingDensity T < 1 := by
  rw [h.upperDensity_eq]

theorem uniformLowerDensityGT_one_iff (h : S.TailEquivalent T) :
    UniformLowerDensityGT S 1 ↔ UniformLowerDensityGT T 1 :=
  h.uniformLowerDensityGT_iff 1

theorem uniformUpperDensityLT_one_iff (h : S.TailEquivalent T) :
    UniformUpperDensityLT S 1 ↔ UniformUpperDensityLT T 1 :=
  h.uniformUpperDensityLT_iff 1

end TailEquivalent

/-- Delete an arbitrary set of physical nodes from a carrier. -/
def delete (S : LocallyFiniteCarrier) (F : Set ℝ) : LocallyFiniteCarrier :=
  S.restrict (S.carrier \ F) Set.sdiff_subset

@[simp]
theorem delete_carrier (S : LocallyFiniteCarrier) (F : Set ℝ) :
    (S.delete F).carrier = S.carrier \ F := rfl

/-- Deleting finitely many nodes is an extensional tail equivalence. -/
theorem tailEquivalent_delete (S : LocallyFiniteCarrier) {F : Set ℝ}
    (hF : F.Finite) : S.TailEquivalent (S.delete F) := by
  unfold TailEquivalent FiniteSymmetricDifference
  apply hF.subset
  intro x hx
  rw [Set.mem_symmDiff] at hx
  rcases hx with hx | hx
  · by_contra hxF
    exact hx.2 ⟨hx.1, hxF⟩
  · exact (hx.2 hx.1.1).elim

theorem lowerDensity_delete_finite (S : LocallyFiniteCarrier) {F : Set ℝ}
    (hF : F.Finite) :
    lowerUniformBeurlingDensity (S.delete F) = lowerUniformBeurlingDensity S := by
  exact (S.tailEquivalent_delete hF).lowerDensity_eq.symm

theorem upperDensity_delete_finite (S : LocallyFiniteCarrier) {F : Set ℝ}
    (hF : F.Finite) :
    upperUniformBeurlingDensity (S.delete F) = upperUniformBeurlingDensity S := by
  exact (S.tailEquivalent_delete hF).upperDensity_eq.symm

end LocallyFiniteCarrier

end MeyerGeneralProblem

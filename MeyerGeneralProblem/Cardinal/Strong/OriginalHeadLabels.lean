module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalSlabPivots

@[expose] public section

/-! The COMPLETE original signed head label type is finite. Upper and reversed
lower pivots are genuine original slab coordinates; their two regions are
disjoint at the actual smaller radius floor(s/2)/2. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- Original nonnegative coordinates of either actual signed cone label. -/
def spectralConeIndexCoordinates : spectralConeIndex → ℕ × ℕ
  | .inl p => p
  | .inr p => p.val

theorem spectralConeIndexFrequency_abs (p : spectralConeIndex) :
    |spectralConeIndexFrequency p| = positiveConeFrequency (spectralConeIndexCoordinates p) := by
  rcases p with p | p
  · exact abs_of_nonneg (positiveConeFrequency_nonneg p)
  · exact (abs_neg _).trans (abs_of_nonneg (positiveConeFrequency_nonneg p.val))

/-- Every original signed label in the ACTUAL smaller central spectral head.
The positive zero appears once, with no negative zero label. -/
def productOriginalHeadLabel (s : ℕ) :=
  {p : spectralConeIndex // |spectralConeIndexFrequency p| ≤ ((s / 2 : ℕ) : ℝ) / 2}

instance productOriginalHeadLabel_finite (s : ℕ) : Finite (productOriginalHeadLabel s) := by
  classical
  let b : ℝ := ((s / 2 : ℕ) : ℝ) / 2
  let A : Set ℝ := spectralConeCarrier.carrier ∩ Set.Icc (-b) b
  let : Fintype A := (spectralConeCarrier.finite_inter_Icc (-b) b).fintype
  let f : productOriginalHeadLabel s → A := fun p =>
    ⟨spectralConeIndexFrequency p.val,
      (spectralConeIndexPoint p.val).property, abs_le.mp p.property⟩
  apply Finite.of_injective f
  intro p q hpq
  apply Subtype.ext
  apply spectralConeIndexFrequency_injective
  exact congrArg Subtype.val hpq

instance productOriginalHeadLabel_fintype (s : ℕ) : Fintype (productOriginalHeadLabel s) :=
  Fintype.ofFinite _

theorem productOriginalHeadCoordinates_bound (s : ℕ) (p : productOriginalHeadLabel s) :
    ((spectralConeIndexCoordinates p.val).1 : ℝ) ≤ ((s / 2 : ℕ) : ℝ) / 2 ∧
    ((spectralConeIndexCoordinates p.val).2 : ℝ) ≤ ((s / 2 : ℕ) : ℝ) / 2 := by
  have hp := p.property
  rw [spectralConeIndexFrequency_abs] at hp
  exact ⟨(positiveConeFrequency_coordinate_le _).1.trans hp,
    (positiveConeFrequency_coordinate_le _).2.trans hp⟩

theorem productOriginalHeadCoordinates_lt (s : ℕ) (hs : 2 ≤ s)
    (p : productOriginalHeadLabel s) :
    (spectralConeIndexCoordinates p.val).1 < s ∧ (spectralConeIndexCoordinates p.val).2 < s := by
  have hhalf : ((s / 2 : ℕ) : ℝ) ≤ (s : ℝ) := by exact_mod_cast Nat.div_le_self s 2
  have hpos : 0 < (s : ℝ) := by exact_mod_cast (show 0 < s by omega)
  have hbound := productOriginalHeadCoordinates_bound s p
  constructor
  · exact_mod_cast (show ((spectralConeIndexCoordinates p.val).1 : ℝ) < (s : ℝ) by linarith)
  · exact_mod_cast (show ((spectralConeIndexCoordinates p.val).2 : ℝ) < (s : ℝ) by linarith)

theorem productOriginalHead_low_lt_high (s : ℕ) (hs : 2 ≤ s)
    (p q : productOriginalHeadLabel s) :
    (spectralConeIndexCoordinates p.val).1 < s - (spectralConeIndexCoordinates q.val).1 ∧
    (spectralConeIndexCoordinates p.val).2 < s - (spectralConeIndexCoordinates q.val).2 := by
  have hhalf : ((s / 2 : ℕ) : ℝ) < (s : ℝ) := by
    exact_mod_cast (show s / 2 < s by omega)
  have hp := productOriginalHeadCoordinates_bound s p
  have hq := productOriginalHeadCoordinates_bound s q
  have hfst : (spectralConeIndexCoordinates p.val).1 +
      (spectralConeIndexCoordinates q.val).1 < s := by
    exact_mod_cast (show ((spectralConeIndexCoordinates p.val).1 : ℝ) +
      (spectralConeIndexCoordinates q.val).1 < (s : ℝ) by linarith)
  have hsnd : (spectralConeIndexCoordinates p.val).2 +
      (spectralConeIndexCoordinates q.val).2 < s := by
    exact_mod_cast (show ((spectralConeIndexCoordinates p.val).2 : ℝ) +
      (spectralConeIndexCoordinates q.val).2 < (s : ℝ) by linarith)
  constructor <;> omega

/-- Each actual upper/lower head row's ORIGINAL slab pivot. -/
def productOriginalHeadPivotIndex (s : ℕ) (hs : 2 ≤ s) :
    productOriginalHeadLabel s → productNumeratorIndex s
  | ⟨.inl p, hp⟩ => by
    have hlt := productOriginalHeadCoordinates_lt s hs ⟨.inl p, hp⟩
    change p.1 < s ∧ p.2 < s at hlt
    refine ⟨(⟨p.1, by omega⟩, ⟨p.2, by omega⟩), ?_⟩
    intro heq
    have hfst := congrArg (fun ij : Fin (s + 1) × Fin (s + 1) => (ij.1 : ℕ)) heq
    change p.1 = s at hfst
    omega
  | ⟨.inr p, hp⟩ => by
    have hlt := productOriginalHeadCoordinates_lt s hs ⟨.inr p, hp⟩
    change p.val.1 < s ∧ p.val.2 < s at hlt
    refine ⟨(⟨s - p.val.1, by omega⟩, ⟨s - p.val.2, by omega⟩), ?_⟩
    intro heq
    have hfst := congrArg (fun ij : Fin (s + 1) × Fin (s + 1) => (ij.1 : ℕ)) heq
    have hsnd := congrArg (fun ij : Fin (s + 1) × Fin (s + 1) => (ij.2 : ℕ)) heq
    change s - p.val.1 = s at hfst
    change s - p.val.2 = s at hsnd
    exact p.property (Prod.ext (by omega) (by omega))

/-- Original degree keys for a maximal nonzero coefficient argument. -/
def productOriginalHeadDegree (s : ℕ) (p : productOriginalHeadLabel s) : ℕ :=
  (spectralConeIndexCoordinates p.val).1 + (spectralConeIndexCoordinates p.val).2

/-- Every original head row, before any noncoarse subset is selected. -/
def productOriginalHeadRow (s : ℕ) (p : productOriginalHeadLabel s) :
    (productNumeratorIndex s → ℂ) →ₗ[ℂ] ℂ :=
  productOriginalSpectralRow s (spectralConeIndexPoint p.val)

end

end MeyerGeneralProblem.StrongParity

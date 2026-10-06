module

public import MeyerGeneralProblem.Cardinal.Strong.SpectralCone
public import MeyerGeneralProblem.Carrier.Dilation

@[expose] public section

/-!
# Complete translated two-quadrant cones

The original integer quadrants, including their full shifted reflected cone,
are locally finite. ALL integer coordinates have a global polynomial bound,
which will control the literal Liouville finite-difference mask.
-/

namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- Literal translated reflected-cone vertex. -/
def translatedConeVertex (A B : ℤ) : ℝ := (A : ℝ) + beta * (B : ℝ)

/-- Both COMPLETE quadrants, with the translated reflected vertex included. -/
def translatedConeFrequency (A B : ℤ) (z : Bool × (ℕ × ℕ)) : ℝ :=
  if z.1 then translatedConeVertex A B - positiveConeFrequency z.2
  else positiveConeFrequency z.2

/-- The original integer module coordinates of every signed translated label. -/
def translatedConeCoordinates (A B : ℤ) (z : Bool × (ℕ × ℕ)) : ℤ × ℤ :=
  if z.1 then (A - (z.2.1 : ℤ), B - (z.2.2 : ℤ))
  else ((z.2.1 : ℤ), (z.2.2 : ℤ))

theorem translatedConeFrequency_coordinates (A B : ℤ) (z : Bool × (ℕ × ℕ)) :
    translatedConeFrequency A B z =
      ((translatedConeCoordinates A B z).1 : ℝ) +
        beta * ((translatedConeCoordinates A B z).2 : ℝ) := by
  unfold translatedConeFrequency translatedConeCoordinates translatedConeVertex
    positiveConeFrequency
  split_ifs
  · simp only [Int.cast_sub, Int.cast_natCast]
    ring
  · rfl

/-- All native positive coordinates are bounded by the translated physical frequency. -/
theorem translatedConeFrequency_positiveCoordinates_le (A B : ℤ)
    (z : Bool × (ℕ × ℕ)) :
    (z.2.1 : ℝ) ≤ |translatedConeFrequency A B z| + |translatedConeVertex A B| ∧
    (z.2.2 : ℝ) ≤ |translatedConeFrequency A B z| + |translatedConeVertex A B| := by
  have hp := positiveConeFrequency_coordinate_le z.2
  have hfreq : positiveConeFrequency z.2 ≤
      |translatedConeFrequency A B z| + |translatedConeVertex A B| := by
    unfold translatedConeFrequency
    split_ifs
    · have h := abs_sub (translatedConeVertex A B)
        (translatedConeVertex A B - positiveConeFrequency z.2)
      rw [show translatedConeVertex A B -
          (translatedConeVertex A B - positiveConeFrequency z.2) =
          positiveConeFrequency z.2 by ring,
        abs_of_nonneg (positiveConeFrequency_nonneg _)] at h
      linarith
    · rw [abs_of_nonneg (positiveConeFrequency_nonneg _)]
      linarith [abs_nonneg (translatedConeVertex A B)]
  exact ⟨hp.1.trans hfreq, hp.2.trans hfreq⟩

/-- A global bound on the SECOND ORIGINAL integer coordinate, with no cutoff. -/
theorem translatedConeCoordinates_second_abs_le (A B : ℤ) (z : Bool × (ℕ × ℕ)) :
    |((translatedConeCoordinates A B z).2 : ℝ)| ≤
      |translatedConeFrequency A B z| + |translatedConeVertex A B| + |(B : ℝ)| := by
  have h := (translatedConeFrequency_positiveCoordinates_le A B z).2
  unfold translatedConeCoordinates
  split_ifs
  · simp only [Int.cast_sub, Int.cast_natCast]
    have ht := abs_sub (B : ℝ) (z.2.2 : ℝ)
    rw [abs_of_nonneg (Nat.cast_nonneg z.2.2 : (0 : ℝ) ≤ (z.2.2 : ℝ))] at ht
    linarith
  · simp only [Int.cast_natCast]
    rw [abs_of_nonneg (Nat.cast_nonneg z.2.2 : (0 : ℝ) ≤ (z.2.2 : ℝ))]
    linarith [abs_nonneg (B : ℝ)]

/-- The literal complete translated cone set. -/
def translatedConeSet (A B : ℤ) : Set ℝ := Set.range (translatedConeFrequency A B)

/-- EXACT equality with the two original integer quadrants, including all offset axes. -/
theorem translatedConeSet_iff (A B : ℤ) (x : ℝ) :
    x ∈ translatedConeSet A B ↔ ∃ p q : ℤ, x = (p : ℝ) + beta * (q : ℝ) ∧
      ((0 ≤ p ∧ 0 ≤ q) ∨ (p ≤ A ∧ q ≤ B)) := by
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨(translatedConeCoordinates A B z).1,
      (translatedConeCoordinates A B z).2,
      translatedConeFrequency_coordinates A B z, ?_⟩
    unfold translatedConeCoordinates
    split_ifs
    · right
      simp only
      exact ⟨sub_le_self _ (Int.natCast_nonneg _), sub_le_self _ (Int.natCast_nonneg _)⟩
    · left
      exact ⟨Int.natCast_nonneg _, Int.natCast_nonneg _⟩
  · rintro ⟨p, q, rfl, hpq | hpq⟩
    · refine ⟨(false, (p.toNat, q.toNat)), ?_⟩
      simp only [translatedConeFrequency, Bool.false_eq_true, ↓reduceIte, positiveConeFrequency]
      rw [show (p.toNat : ℝ) = p by exact_mod_cast Int.toNat_of_nonneg hpq.1,
        show (q.toNat : ℝ) = q by exact_mod_cast Int.toNat_of_nonneg hpq.2]
    · refine ⟨(true, ((A - p).toNat, (B - q).toNat)), ?_⟩
      simp only [translatedConeFrequency, ↓reduceIte, translatedConeVertex, positiveConeFrequency]
      rw [show ((A - p).toNat : ℝ) = (A : ℝ) - p by
        exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr hpq.1),
        show ((B - q).toNat : ℝ) = (B : ℝ) - q by
        exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr hpq.2)]
      ring

/-- Local finiteness of the WHOLE translated cone, rather than a clipped grid. -/
theorem translatedConeSet_finite_inter_Icc (A B : ℤ) (u v : ℝ) :
    (translatedConeSet A B ∩ Set.Icc u v).Finite := by
  let M : ℝ := max |u| |v| + |translatedConeVertex A B|
  let K : ℕ := ⌈M⌉₊
  have hM : M ≤ (K : ℝ) := Nat.le_ceil _
  let box : Set (Bool × (ℕ × ℕ)) := Set.univ ×ˢ (Set.Iic K ×ˢ Set.Iic K)
  have hbox : box.Finite := (Set.toFinite (Set.univ : Set Bool)).prod
    ((Set.finite_Iic K).prod (Set.finite_Iic K))
  apply (hbox.image (translatedConeFrequency A B)).subset
  rintro x ⟨⟨z, rfl⟩, hx⟩
  have habs : |translatedConeFrequency A B z| ≤ max |u| |v| := by
    apply abs_le.mpr
    constructor
    · linarith [le_max_left |u| |v|, neg_abs_le u, hx.1]
    · linarith [le_max_right |u| |v|, le_abs_self v, hx.2]
  have hcoord := translatedConeFrequency_positiveCoordinates_le A B z
  have hi : z.2.1 ≤ K := by
    have hiR : (z.2.1 : ℝ) ≤ (K : ℝ) := by dsimp [M] at hM; linarith [hcoord.1]
    exact_mod_cast hiR
  have hj : z.2.2 ≤ K := by
    have hjR : (z.2.2 : ℝ) ≤ (K : ℝ) := by dsimp [M] at hM; linarith [hcoord.2]
    exact_mod_cast hjR
  exact ⟨z, ⟨Set.mem_univ _, ⟨hi, hj⟩⟩, rfl⟩

/-- The actual translated two-quadrant carrier with internally proved local finiteness. -/
def translatedConeCarrier (A B : ℤ) : LocallyFiniteCarrier where
  carrier := translatedConeSet A B
  finite_inter_Icc := translatedConeSet_finite_inter_Icc A B

/-- The complete translated cone at any ordinary positive scale. -/
def scaledTranslatedConeCarrier (A B : ℤ) (scale : ℝ) (hscale : 0 < scale) : LocallyFiniteCarrier :=
  (translatedConeCarrier A B).dilate scale⁻¹ (inv_pos.mpr hscale)

/-- Every point of the actual scaled cone has its full original integer label. -/
theorem scaledTranslatedConeCarrier_label (A B : ℤ) (scale : ℝ) (hscale : 0 < scale)
    (x : (scaledTranslatedConeCarrier A B scale hscale).subtype) :
    ∃ z : Bool × (ℕ × ℕ), (x : ℝ) = translatedConeFrequency A B z / scale := by
  obtain ⟨y, ⟨z, rfl⟩, he⟩ := x.property
  exact ⟨z, by simpa only [div_eq_mul_inv, mul_comm] using he.symm⟩

end
end MeyerGeneralProblem.StrongParity

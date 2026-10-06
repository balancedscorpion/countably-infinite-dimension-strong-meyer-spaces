module

public import MeyerGeneralProblem.Cardinal.Strong.LowerQuotientSeries

@[expose] public section

/-! The complete original rank-two nonnegative cone and its reflection,
with actual irrational injectivity and local finiteness. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- The literal original positive cone frequency, before scaling. -/
def positiveConeFrequency (p : ℕ × ℕ) : ℝ := p.1 + beta * p.2

theorem positiveConeFrequency_nonneg (p : ℕ × ℕ) : 0 ≤ positiveConeFrequency p := by
  unfold positiveConeFrequency
  have hb : 0 ≤ beta := le_trans (by norm_num) beta_between_three_four.1.le
  positivity

theorem positiveConeFrequency_coordinate_le (p : ℕ × ℕ) :
    (p.1 : ℝ) ≤ positiveConeFrequency p ∧ (p.2 : ℝ) ≤ positiveConeFrequency p := by
  unfold positiveConeFrequency
  have hb : 1 ≤ beta := le_trans (by norm_num) beta_between_three_four.1.le
  have hn : (0 : ℝ) ≤ p.2 := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ p.1 := Nat.cast_nonneg _
  constructor <;> nlinarith

theorem positiveConeFrequency_injective : Function.Injective positiveConeFrequency := by
  intro p q h
  have hn : p.2 = q.2 := by
    by_contra hn
    have hd : ((p.2 : ℤ) - (q.2 : ℤ)) ≠ 0 := by
      intro hd
      apply hn
      exact_mod_cast sub_eq_zero.mp hd
    apply beta_irrational.ne_rational ((q.1 : ℤ) - (p.1 : ℤ)) ((p.2 : ℤ) - (q.2 : ℤ))
    apply (eq_div_iff (by exact_mod_cast hd :
      ((((p.2 : ℤ) - (q.2 : ℤ)) : ℤ) : ℝ) ≠ 0)).mpr
    simp only [Int.cast_sub, Int.cast_natCast]
    unfold positiveConeFrequency at h
    linarith
  apply Prod.ext
  · unfold positiveConeFrequency at h
    rw [hn] at h
    exact_mod_cast (show (p.1 : ℝ) = q.1 by linarith)
  · exact hn

theorem positiveConeFrequency_eq_zero_iff (p : ℕ × ℕ) :
    positiveConeFrequency p = 0 ↔ p = (0, 0) := by
  constructor
  · intro h
    apply positiveConeFrequency_injective
    simpa only [positiveConeFrequency, Nat.cast_zero, mul_zero, add_zero] using h
  · rintro rfl
    simp [positiveConeFrequency]

/-- Both original cone signs; the set carrier counts their common zero once. -/
def signedConeFrequency (p : Bool × (ℕ × ℕ)) : ℝ :=
  if p.1 then -positiveConeFrequency p.2 else positiveConeFrequency p.2

theorem signedConeFrequency_abs (p : Bool × (ℕ × ℕ)) :
    |signedConeFrequency p| = positiveConeFrequency p.2 := by
  unfold signedConeFrequency
  split_ifs <;> simp [abs_of_nonneg (positiveConeFrequency_nonneg p.2)]

/-- The COMPLETE coarse cone, with both signs and its actual zero. -/
def spectralConeSet : Set ℝ := Set.range signedConeFrequency

theorem spectralConeSet_finite_inter_Icc (u v : ℝ) :
    (spectralConeSet ∩ Set.Icc u v).Finite := by
  let M : ℝ := max |u| |v|
  let K : ℕ := ⌈M⌉₊
  have hM : M ≤ (K : ℝ) := Nat.le_ceil _
  let box : Set (Bool × (ℕ × ℕ)) := Set.univ ×ˢ (Set.Iic K ×ˢ Set.Iic K)
  have hbox : box.Finite := Set.toFinite (Set.univ : Set Bool) |>.prod
    ((Set.finite_Iic K).prod (Set.finite_Iic K))
  apply (hbox.image signedConeFrequency).subset
  rintro x ⟨⟨p, rfl⟩, hx⟩
  have habs : |signedConeFrequency p| ≤ M := by
    apply abs_le.mpr
    constructor
    · have hu : |u| ≤ M := le_max_left _ _
      linarith [neg_abs_le u, hx.1]
    · have hv : |v| ≤ M := le_max_right _ _
      linarith [le_abs_self v, hx.2]
  rw [signedConeFrequency_abs] at habs
  have hi : p.2.1 ≤ K := by
    exact_mod_cast ((positiveConeFrequency_coordinate_le p.2).1.trans (habs.trans hM))
  have hj : p.2.2 ≤ K := by
    exact_mod_cast ((positiveConeFrequency_coordinate_le p.2).2.trans (habs.trans hM))
  exact ⟨p, ⟨Set.mem_univ _, ⟨hi, hj⟩⟩, rfl⟩

/-- The literal coarse spectral record, with proved local finiteness. -/
def spectralConeCarrier : LocallyFiniteCarrier where
  carrier := spectralConeSet
  finite_inter_Icc := spectralConeSet_finite_inter_Icc

end

end MeyerGeneralProblem.StrongParity

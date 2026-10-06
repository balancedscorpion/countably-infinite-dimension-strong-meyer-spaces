module

public import MeyerGeneralProblem.Cardinal.Strong.BidiskSeries

@[expose] public section

/-! Exact zero extension of a two-index series under a nonnegative shift. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- Shift both natural indices and retain zero coefficients outside the image. -/
def natPairShiftCoefficient (i j : ℕ) (c : ℕ × ℕ → ℂ) (p : ℕ × ℕ) : ℂ :=
  if i ≤ p.1 ∧ j ≤ p.2 then c (p.1 - i, p.2 - j) else 0

theorem natPairShift_range (i j : ℕ) (p : ℕ × ℕ) :
    p ∈ Set.range (fun q : ℕ × ℕ => (q.1 + i, q.2 + j)) ↔ i ≤ p.1 ∧ j ≤ p.2 := by
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨Nat.le_add_left _ _, Nat.le_add_left _ _⟩
  · rintro ⟨hi, hj⟩
    exact ⟨(p.1 - i, p.2 - j), Prod.ext (Nat.sub_add_cancel hi) (Nat.sub_add_cancel hj)⟩

/-- A monomial shift of a genuinely summable series has its literal shifted sum. -/
theorem natPairShiftCoefficient_hasSum (i j : ℕ) (c : ℕ × ℕ → ℂ) (Z W A : ℂ)
    (h : HasSum (fun p : ℕ × ℕ => c p * Z ^ p.1 * W ^ p.2) A) :
    HasSum (fun p : ℕ × ℕ => natPairShiftCoefficient i j c p * Z ^ p.1 * W ^ p.2)
      (A * Z ^ i * W ^ j) := by
  let g : ℕ × ℕ → ℕ × ℕ := fun p => (p.1 + i, p.2 + j)
  have hg : Function.Injective g := by
    intro p q hpq
    exact Prod.ext (Nat.add_right_cancel (congrArg Prod.fst hpq))
      (Nat.add_right_cancel (congrArg Prod.snd hpq))
  have hz (p : ℕ × ℕ) (hp : p ∉ Set.range g) :
      natPairShiftCoefficient i j c p * Z ^ p.1 * W ^ p.2 = 0 := by
    have hp' : ¬ (i ≤ p.1 ∧ j ≤ p.2) := by
      simpa only [g, natPairShift_range] using hp
    simp [natPairShiftCoefficient, hp']
  apply (hg.hasSum_iff hz).mp
  convert! (h.mul_right (Z ^ i)).mul_right (W ^ j) using 1
  funext p
  simp only [Function.comp_def, g, natPairShiftCoefficient, Nat.le_add_left,
    and_self, ite_true, Nat.add_sub_cancel, pow_add]
  ring

end

end MeyerGeneralProblem.StrongParity

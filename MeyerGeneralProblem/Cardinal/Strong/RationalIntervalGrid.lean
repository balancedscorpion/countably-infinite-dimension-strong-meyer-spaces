module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.List.Range
public import Mathlib.Tactic

@[expose] public section

/-! A complete executable finite rational grid, with proved nearest-point coverage. -/

namespace MeyerGeneralProblem.StrongParity

/-- An executable rational grid point in the interval of integer radius `B`. -/
def rationalIntervalGridPoint (B K j : ℕ) : ℚ := -(B : ℚ) + (j : ℚ) / K

/-- The COMPLETE finite rational grid, including both endpoints. -/
def rationalIntervalGrid (B K : ℕ) : List ℚ :=
  (List.range (2 * B * K + 1)).map (rationalIntervalGridPoint B K)

noncomputable section

theorem rationalIntervalGridPoint_mem {B K j : ℕ} (hj : j ≤ 2 * B * K) :
    rationalIntervalGridPoint B K j ∈ rationalIntervalGrid B K := by
  apply List.mem_map.mpr
  exact ⟨j, List.mem_range.mpr (Nat.lt_succ_of_le hj), rfl⟩

theorem rationalIntervalGrid_nonempty (B K : ℕ) : rationalIntervalGrid B K ≠ [] := by
  have h := rationalIntervalGridPoint_mem (B := B) (K := K) (j := 0) (by omega)
  intro he
  rw [he] at h
  simp at h

theorem rationalIntervalGridPoint_cast (B K j : ℕ) :
    (rationalIntervalGridPoint B K j : ℝ) = -(B : ℝ) + (j : ℝ) / K := by
  simp [rationalIntervalGridPoint]

/-- Every enumerated grid point really lies inside the stated interval. -/
theorem rationalIntervalGridPoint_bounds {B K j : ℕ} (hK : 0 < K) (hj : j ≤ 2 * B * K) :
    -(B : ℝ) ≤ (rationalIntervalGridPoint B K j : ℝ) ∧
      (rationalIntervalGridPoint B K j : ℝ) ≤ B := by
  have hKR : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hjR : (j : ℝ) ≤ 2 * B * K := by exact_mod_cast hj
  rw [rationalIntervalGridPoint_cast]
  constructor
  · have hd : (0 : ℝ) ≤ (j : ℝ) / K := by positivity
    linarith
  · have hd : (j : ℝ) / K ≤ 2 * B := (div_le_iff₀ hKR).mpr hjR
    linarith

/-- The actual finite grid covers EVERY real point in its interval at spacing `1/K`. -/
theorem rationalIntervalGrid_near_real (B K : ℕ) (hK : 0 < K) {x : ℝ}
    (hx : -(B : ℝ) ≤ x ∧ x ≤ B) :
    ∃ q ∈ rationalIntervalGrid B K, |(q : ℝ) - x| ≤ 1 / (K : ℝ) := by
  have hKR : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  let y : ℝ := (K : ℝ) * (x + B)
  let j : ℕ := Nat.floor y
  have hy : 0 ≤ y := by
    dsimp [y]
    exact mul_nonneg hKR.le (by linarith [hx.1])
  have hyB : y ≤ ((2 * B * K : ℕ) : ℝ) := by
    dsimp [y]
    push_cast
    nlinarith [hx.2]
  have hj : j ≤ 2 * B * K := Nat.floor_le_of_le hyB
  refine ⟨rationalIntervalGridPoint B K j, rationalIntervalGridPoint_mem hj, ?_⟩
  have hf : |(j : ℝ) - y| ≤ 1 := Nat.abs_floor_sub_le hy
  have hi : (rationalIntervalGridPoint B K j : ℝ) - x = ((j : ℝ) - y) / K := by
    rw [rationalIntervalGridPoint_cast]
    dsimp [y]
    field_simp
    ring
  rw [hi, abs_div, abs_of_pos hKR]
  exact div_le_div_of_nonneg_right hf hKR.le

end

end MeyerGeneralProblem.StrongParity

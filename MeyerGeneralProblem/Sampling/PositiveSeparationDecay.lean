module

public import MeyerGeneralProblem.Sampling.PositiveSeparation
public import MeyerGeneralProblem.Carrier.SignedSquareSchur

@[expose] public section

/-!
# Exponential and bounded-band geometry at positive separation

Rescaling before the existing integer-shell estimates gives exponential
summability with finite exceptions, uniform exponential tails, bounded-band
counts, and negative-power summability for every strictly positive gap.
-/

namespace MeyerGeneralProblem

noncomputable section

private theorem scaled_exp_distance {q : ℝ} (hq : 0 < q) (c x a : ℝ) :
    Real.exp (-(c / q) * |q * x - q * a|) = Real.exp (-c * |x - a|) := by
  rw [← mul_sub, abs_mul, abs_of_pos hq]
  congr 1
  field_simp

/-- The explicit exponential row ceiling after dilation to integer shells. -/
def positiveSeparationExpRowConstant (d c : ℝ) : ℝ :=
  ∑' k : ℤ, Real.exp (c / positiveSeparationScale d) *
    Real.exp (-(c / positiveSeparationScale d) * |(k : ℝ)|)

theorem positiveSeparationExpRowConstant_nonneg (d c : ℝ) :
    0 ≤ positiveSeparationExpRowConstant d c :=
  tsum_nonneg fun _ => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le

/-- Exponential rows remain summable with finitely many exceptional points
and an arbitrary positive gap on the complement. -/
theorem summable_exp_neg_abs_sub_of_finite_posSeparated
    {ι : Type*} [DecidableEq ι] (s : ι → ℝ) (F : Finset ι)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c)
    (hsep : ∀ i j, i ∉ F → j ∉ F → i ≠ j → d ≤ |s i - s j|)
    (a : ℝ) : Summable (fun i : ι => Real.exp (-c * |s i - a|)) := by
  let q := positiveSeparationScale d
  have hq : 0 < q := positiveSeparationScale_pos d
  have hsep' : ∀ i j, i ∉ F → j ∉ F → i ≠ j →
      2 ≤ |q * s i - q * s j| := by
    intro i j hi hj hij
    rw [← mul_sub, abs_mul, abs_of_pos hq]
    exact (two_le_positiveSeparationScale_mul hd).trans
      (mul_le_mul_of_nonneg_left (hsep i j hi hj hij) hq.le)
  have h := summable_exp_neg_abs_sub_of_finite_separated
    (fun i => q * s i) F (by norm_num : (1 : ℝ) < 2) (div_pos hc hq) hsep' (q * a)
  simpa only [scaled_exp_distance hq] using h

/-- Uniform exponential row ceiling with finite exceptional points. -/
theorem tsum_exp_neg_abs_sub_le_of_finite_posSeparated
    {ι : Type*} [DecidableEq ι] (s : ι → ℝ) (F : Finset ι)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c)
    (hsep : ∀ i j, i ∉ F → j ∉ F → i ≠ j → d ≤ |s i - s j|)
    (a : ℝ) :
    ∑' i : ι, Real.exp (-c * |s i - a|) ≤
      (F.card : ℝ) + positiveSeparationExpRowConstant d c := by
  let q := positiveSeparationScale d
  have hq : 0 < q := positiveSeparationScale_pos d
  have hsep' : ∀ i j, i ∉ F → j ∉ F → i ≠ j →
      2 ≤ |q * s i - q * s j| := by
    intro i j hi hj hij
    rw [← mul_sub, abs_mul, abs_of_pos hq]
    exact (two_le_positiveSeparationScale_mul hd).trans
      (mul_le_mul_of_nonneg_left (hsep i j hi hj hij) hq.le)
  have h := tsum_exp_neg_abs_sub_le_of_finite_separated
    (fun i => q * s i) F (by norm_num : (1 : ℝ) < 2) (div_pos hc hq) hsep' (q * a)
  simpa only [scaled_exp_distance hq, positiveSeparationExpRowConstant, q] using h

/-- Exponential distance tails are uniformly small under positive separation. -/
theorem exists_uniform_sum_exp_neg_abs_tail_of_posSeparated
    {ι : Type*} [DecidableEq ι] (s : ι → ℝ) {d c : ℝ} (hd : 0 < d) (hc : 0 < c)
    (hsep : ∀ i j, i ≠ j → d ≤ |s i - s j|) :
    ∀ ε > 0, ∃ L ≥ 0, ∀ a : ℝ, ∀ U : Finset ι,
      ∑ i ∈ U with L < |s i - a|, Real.exp (-c * |s i - a|) ≤ ε := by
  intro ε hε
  let q := positiveSeparationScale d
  have hq : 0 < q := positiveSeparationScale_pos d
  obtain ⟨L, hL, htail⟩ := exists_uniform_sum_exp_neg_abs_tail_of_separated
    (fun i => q * s i) (by norm_num : (1 : ℝ) < 2) (div_pos hc hq)
    (positiveSeparationScale_separated s hd hsep) ε hε
  refine ⟨L / q, by positivity, fun a U => ?_⟩
  have hfilter : U.filter (fun i => L / q < |s i - a|) =
      U.filter (fun i => L < |q * s i - q * a|) := by
    apply Finset.filter_congr
    intro i hi
    rw [div_lt_iff₀ hq, ← mul_sub, abs_mul, abs_of_pos hq, mul_comm]
  rw [hfilter]
  simpa only [scaled_exp_distance hq] using htail (q * a) U

/-- Positive-separated metric bands have a uniform finite count bound after
scaling the integer-shell radius. -/
theorem card_metricBand_le_integerFloorBand_of_posSeparated
    {ι : Type*} [DecidableEq ι] (s : ι → ℝ) {d : ℝ} (hd : 0 < d)
    (hsep : ∀ i j, i ≠ j → d ≤ |s i - s j|)
    (L a : ℝ) (U : Finset ι) :
    (U.filter (fun i => |s i - a| ≤ L)).card ≤
      (Finset.Icc ⌊-(positiveSeparationScale d * L)⌋
        ⌊positiveSeparationScale d * L⌋).card := by
  let q := positiveSeparationScale d
  have hq : 0 < q := positiveSeparationScale_pos d
  have h := card_metricBand_le_integerFloorBand_of_separated
    (fun i => q * s i) (by norm_num : (1 : ℝ) < 2)
    (positiveSeparationScale_separated s hd hsep) (q * L) (q * a) U
  have hfilter : U.filter (fun i => |q * s i - q * a| ≤ q * L) =
      U.filter (fun i => |s i - a| ≤ L) := by
    apply Finset.filter_congr
    intro i hi
    rw [← mul_sub, abs_mul, abs_of_pos hq, mul_le_mul_iff_right₀ hq]
  rwa [hfilter] at h

/-- Negative powers are summable on a positively separated family staying
outside the central unit interval. -/
theorem summable_abs_rpow_of_posSeparated_away
    {ι : Type*} [DecidableEq ι] (s : ι → ℝ) {d b : ℝ} (hd : 0 < d) (hb : 1 < b)
    (hsep : ∀ i j, i ≠ j → d ≤ |s i - s j|) (hlarge : ∀ i, 1 ≤ |s i|) :
    Summable (fun i : ι => |s i| ^ (-b)) := by
  let q := positiveSeparationScale d
  have hq : 0 < q := positiveSeparationScale_pos d
  have h := summable_abs_rpow_of_separated_away (fun i => q * s i)
    (by norm_num : (1 : ℝ) < 2) hb (positiveSeparationScale_separated s hd hsep) (by
      intro i
      rw [abs_mul, abs_of_pos hq]
      have hq1 : 1 ≤ q := one_le_positiveSeparationScale d
      nlinarith [hlarge i, mul_nonneg (sub_nonneg.mpr hq1)
        (sub_nonneg.mpr (hlarge i))])
  have hqpow : q ^ (-b) ≠ 0 := (Real.rpow_pos_of_pos hq _).ne'
  have hscaled := h.mul_left (q ^ (-b))⁻¹
  apply hscaled.congr
  intro i
  rw [abs_mul, abs_of_pos hq, Real.mul_rpow hq.le (abs_nonneg _),
    ← mul_assoc, inv_mul_cancel₀ hqpow, one_mul]

end

end MeyerGeneralProblem

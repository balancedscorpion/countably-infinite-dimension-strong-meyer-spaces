module

public import MeyerGeneralProblem.Cardinal.Strong.SheetSpacing
public import MeyerGeneralProblem.Sampling.PositiveSeparationDecay

@[expose] public section

/-!
# Complete actual sheet counts and summable weights

The derived positive separation supplies integer-shell counts for every
actual sheet root in a band, and a summable inverse-square envelope on
the whole sheet. No selected root enumeration or count bound is assumed.
-/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

theorem sheetCarrier_points_separated {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (i j : (sheetCarrier a ha ha1).subtype) (hij : i ≠ j) :
    sheetRootSpacing a ≤ |(i : ℝ) - (j : ℝ)| :=
  sheetFlow_roots_separated ha ha1 i.property j.property
    (fun h => hij (Subtype.ext h))

/-- All actual roots in the closed band, using the proved local finiteness. -/
def sheetRootBand (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (R c : ℝ) :
    Finset (sheetCarrier a ha ha1).subtype :=
  (((sheetCarrier a ha ha1).finite_inter_Icc (c - R) (c + R)).preimage
    (Set.injOn_of_injective Subtype.val_injective)).toFinset

theorem mem_sheetRootBand_iff {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (R c : ℝ)
    (x : (sheetCarrier a ha ha1).subtype) :
    x ∈ sheetRootBand a ha ha1 R c ↔ |(x : ℝ) - c| ≤ R := by
  simp only [sheetRootBand, Set.Finite.mem_toFinset, Set.mem_preimage,
    Set.mem_inter_iff, Set.mem_Icc]
  constructor
  · rintro ⟨_, hlo, hhi⟩
    rw [abs_le]
    constructor <;> linarith
  · intro h
    obtain ⟨hlo, hhi⟩ := abs_le.mp h
    exact ⟨x.property, by linarith, by linarith⟩

/-- The complete band injects into the explicit scaled integer interval. -/
theorem sheetRootBand_card_le_integerBand {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (R c : ℝ) :
    (sheetRootBand a ha ha1 R c).card ≤
      (Finset.Icc ⌊-(positiveSeparationScale (sheetRootSpacing a) * R)⌋
        ⌊positiveSeparationScale (sheetRootSpacing a) * R⌋).card := by
  classical
  have h := card_metricBand_le_integerFloorBand_of_posSeparated
    (fun x : (sheetCarrier a ha ha1).subtype => (x : ℝ)) (sheetRootSpacing_pos ha ha1)
    (sheetCarrier_points_separated ha ha1) R c (sheetRootBand a ha ha1 R c)
  have hfilter : (sheetRootBand a ha ha1 R c).filter
      (fun x : (sheetCarrier a ha ha1).subtype => |(x : ℝ) - c| ≤ R) =
      sheetRootBand a ha ha1 R c := by
    apply Finset.filter_eq_self.mpr
    intro x hx
    exact (mem_sheetRootBand_iff ha ha1 R c x).mp hx
  rwa [hfilter] at h

/-- Uniform linear growth of the COMPLETE actual sheet root count. -/
theorem sheetRootBand_card_le_linear {a R : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (hR : 0 ≤ R) (c : ℝ) :
    ((sheetRootBand a ha ha1 R c).card : ℝ) ≤
      2 * positiveSeparationScale (sheetRootSpacing a) * R + 2 := by
  let q := positiveSeparationScale (sheetRootSpacing a)
  have hq : 0 < q := positiveSeparationScale_pos _
  have hlo : ⌊-(q * R)⌋ ≤ (0 : ℤ) := by
    have h := Int.floor_le (-(q * R))
    have hR' : -(q * R) ≤ 0 := by nlinarith
    exact_mod_cast h.trans hR'
  have hhi : (0 : ℤ) ≤ ⌊q * R⌋ := Int.floor_nonneg.mpr (mul_nonneg hq.le hR)
  have hcard := Int.card_Icc_of_le ⌊-(q * R)⌋ ⌊q * R⌋
    (show ⌊-(q * R)⌋ ≤ ⌊q * R⌋ + 1 by omega)
  have hcardR : ((Finset.Icc ⌊-(q * R)⌋ ⌊q * R⌋).card : ℝ) =
      (⌊q * R⌋ : ℝ) + 1 - ⌊-(q * R)⌋ := by exact_mod_cast hcard
  calc
    _ ≤ ((Finset.Icc ⌊-(q * R)⌋ ⌊q * R⌋).card : ℝ) := by
      exact_mod_cast sheetRootBand_card_le_integerBand ha ha1 R c
    _ = _ := hcardR
    _ ≤ _ := by
      have hupper := Int.floor_le (q * R)
      have hlower := Int.lt_floor_add_one (-(q * R))
      change _ ≤ 2 * q * R + 2
      linarith

/-- The inverse-square envelope is summable over EVERY actual sheet root. -/
theorem sheetCarrier_inverseSquare_summable {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    Summable (fun x : (sheetCarrier a ha ha1).subtype => 1 / (1 + |(x : ℝ)|) ^ 2) := by
  classical
  simpa only [sub_zero] using summable_inverseSquareDistance_of_posSeparated
    (fun x : (sheetCarrier a ha ha1).subtype => (x : ℝ)) (sheetRootSpacing_pos ha ha1)
    (sheetCarrier_points_separated ha ha1) 0

/-- Polynomially bounded coefficients have absolute weighted summability
on the complete actual sheet, at two powers above their growth order. -/
theorem sheetCarrier_polynomial_weight_summable {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (b : (sheetCarrier a ha ha1).subtype → ℂ) (B : ℝ) (d : ℕ)
    (hbound : ∀ x, ‖b x‖ ≤ B * (1 + |(x : ℝ)|) ^ d) :
    Summable (fun x : (sheetCarrier a ha ha1).subtype =>
      ‖b x‖ / (1 + |(x : ℝ)|) ^ (d + 2)) := by
  apply Summable.of_nonneg_of_le (fun x => by positivity) _
    ((sheetCarrier_inverseSquare_summable ha ha1).mul_left B)
  intro x
  have hp : 0 < 1 + |(x : ℝ)| := by positivity
  calc
    _ ≤ (B * (1 + |(x : ℝ)|) ^ d) / (1 + |(x : ℝ)|) ^ (d + 2) :=
      (div_le_div_iff_of_pos_right (by positivity)).mpr (hbound x)
    _ = B * (1 / (1 + |(x : ℝ)|) ^ 2) := by
      rw [pow_add]
      field_simp

end

end MeyerGeneralProblem.StrongParity

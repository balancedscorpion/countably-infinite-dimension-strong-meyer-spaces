module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalHeadLabels

@[expose] public section

/-! Exact geometric coarse membership of the actual signed rank-two cone after
a positive natural private scale. Irrationality proves BOTH coordinate
conditions; the shared coarse cone is never removed from the whole carrier. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- The complete original signed cone is invariant under negation. -/
theorem originalSpectralConeSet_neg_iff (x : ℝ) :
    -x ∈ spectralConeSet ↔ x ∈ spectralConeSet := by
  have h (y : ℝ) (hy : y ∈ spectralConeSet) : -y ∈ spectralConeSet := by
    obtain ⟨⟨b, p⟩, hp⟩ := hy
    refine ⟨(!b, p), ?_⟩
    cases b <;> simp only [signedConeFrequency, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ite_false, ite_true] at hp ⊢ <;> linarith
  exact ⟨fun hx => by simpa only [neg_neg] using h (-x) hx, h x⟩

/-- Multiplying positive cone coordinates by m multiplies the ACTUAL frequency by m. -/
theorem positiveConeFrequency_nat_mul (m : ℕ) (p : ℕ × ℕ) :
    positiveConeFrequency (m * p.1, m * p.2) = (m : ℝ) * positiveConeFrequency p := by
  simp only [positiveConeFrequency, Nat.cast_mul]
  ring

/-- Positive natural multiplication preserves the COMPLETE shared signed cone. -/
theorem originalSpectralConeSet_nat_mul (m : ℕ) (x : ℝ) (hx : x ∈ spectralConeSet) :
    (m : ℝ) * x ∈ spectralConeSet := by
  obtain ⟨⟨b, p⟩, rfl⟩ := hx
  refine ⟨(b, (m * p.1, m * p.2)), ?_⟩
  cases b <;> simp only [signedConeFrequency, Bool.false_eq_true, ite_false, ite_true,
    positiveConeFrequency_nat_mul] <;> ring

/-- A positive original label falls in the shared coarse cone exactly at BOTH private multiples. -/
theorem positiveConeFrequency_div_mem_coarse_iff (m : ℕ) (hm : 0 < m) (p : ℕ × ℕ) :
    positiveConeFrequency p / (m : ℝ) ∈ spectralConeSet ↔ m ∣ p.1 ∧ m ∣ p.2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  constructor
  · rintro ⟨⟨b, q⟩, hq⟩
    cases b with
    | false =>
      have hfreq : positiveConeFrequency p = positiveConeFrequency (m * q.1, m * q.2) := by
        simp only [signedConeFrequency, Bool.false_eq_true, ite_false] at hq
        rw [positiveConeFrequency_nat_mul]
        have hmul := (eq_div_iff hmR.ne').mp hq
        simpa only [mul_comm] using hmul.symm
      have hp := positiveConeFrequency_injective hfreq
      exact ⟨⟨q.1, congrArg Prod.fst hp⟩, ⟨q.2, congrArg Prod.snd hp⟩⟩
    | true =>
      simp only [signedConeFrequency, ite_true] at hq
      have hp0 : positiveConeFrequency p = 0 := by
        have hn := positiveConeFrequency_nonneg q
        have hp := positiveConeFrequency_nonneg p
        have hmul := (eq_div_iff hmR.ne').mp hq
        nlinarith
      rw [(positiveConeFrequency_eq_zero_iff p).mp hp0]
      exact ⟨dvd_zero m, dvd_zero m⟩
  · rintro ⟨⟨k, hk⟩, ⟨n, hn⟩⟩
    refine ⟨(false, (k, n)), ?_⟩
    simp only [signedConeFrequency, Bool.false_eq_true, ite_false]
    have hp : p = (m * k, m * n) := Prod.ext hk hn
    rw [hp, positiveConeFrequency_nat_mul m (k, n)]
    field_simp

/-- BOTH signed original labels have the exact same coarse divisibility condition. -/
theorem spectralConeIndexFrequency_div_mem_coarse_iff (m : ℕ) (hm : 0 < m)
    (label : spectralConeIndex) :
    spectralConeIndexFrequency label / (m : ℝ) ∈ spectralConeSet ↔
      m ∣ (spectralConeIndexCoordinates label).1 ∧ m ∣ (spectralConeIndexCoordinates label).2 := by
  cases label with
  | inl p => exact positiveConeFrequency_div_mem_coarse_iff m hm p
  | inr p =>
    simp only [spectralConeIndexFrequency, spectralConeIndexCoordinates, neg_div,
      originalSpectralConeSet_neg_iff]
    exact positiveConeFrequency_div_mem_coarse_iff m hm p.val

end

end MeyerGeneralProblem.StrongParity

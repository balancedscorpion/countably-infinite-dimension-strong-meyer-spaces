module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalChartLocalTransport

@[expose] public section

/-! Actual algebraic overlap differences of separate-pole lifts. Equality to the
same original numerator gives BOTH pole bounds; clearing pays their intersection,
and the literal coordinate degree bounds pay correct overlap regularity. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- Two separate-pole polynomial lifts of the SAME Laurent numerator differ by
an actual Laurent regular function. Both divisor equations are derived outputs. -/
theorem originalLaurent_separate_lifts_difference
    (q e : AddMonoidAlgebra ℂ (ℕ × ℕ)) (hq : q ≠ 0) (hrel : IsRelPrime q e)
    (r A B A' B' : AddMonoidAlgebra ℂ (ℤ × ℤ))
    (hA : r = originalPositiveLaurentEmbedding e * A + originalPositiveLaurentEmbedding q * B)
    (hA' : r = originalPositiveLaurentEmbedding e * A' + originalPositiveLaurentEmbedding q * B') :
    ∃ H : AddMonoidAlgebra ℂ (ℤ × ℤ),
      originalPositiveLaurentEmbedding q * H = A - A' ∧
      originalPositiveLaurentEmbedding e * H = B' - B := by
  let f := algebraMap (AddMonoidAlgebra ℂ (ℤ × ℤ))
    (FractionRing (AddMonoidAlgebra ℂ (ℤ × ℤ)))
  have hi : Function.Injective f := IsFractionRing.injective _ _
  have hq0 : f (originalPositiveLaurentEmbedding q) ≠ 0 :=
    (map_ne_zero_iff f hi).mpr (originalPositiveLaurentEmbedding_ne_zero q hq)
  have hcross : originalPositiveLaurentEmbedding e * (A - A') =
      originalPositiveLaurentEmbedding q * (B' - B) := by
    linear_combination hA' - hA
  let x := f (A - A') / f (originalPositiveLaurentEmbedding q)
  have hxq : f (originalPositiveLaurentEmbedding q) * x = f (A - A') := by
    dsimp only [x]
    field_simp [hq0]
  have hxe : f (originalPositiveLaurentEmbedding e) * x = f (B' - B) := by
    have hf := congrArg f hcross
    simp only [map_mul] at hf
    dsimp only [x]
    rw [← mul_div_assoc]
    exact (div_eq_iff hq0).mpr (by simpa only [mul_comm] using hf)
  obtain ⟨H, hH⟩ := originalLaurent_fraction_intersection q e hq hrel x (A - A') (B' - B) hxq hxe
  refine ⟨H, ?_, ?_⟩
  · apply hi
    rw [map_mul, hH]
    exact hxq
  · apply hi
    rw [map_mul, hH]
    exact hxe

/-- The exact chart section bound controls the selected signed integer axis. -/
theorem originalLaurentChartBound_axis (c : Bool × Bool) (swap : Bool) (d : ℕ)
    (A : AddMonoidAlgebra ℂ (ℤ × ℤ)) (hA : OriginalLaurentChartBound c d A) :
    let rev := !(if swap then c.2 else c.1)
    ∀ n, A.coeff n ≠ 0 →
      (originalLaurentAxisIndex swap rev n).1 ≤ if rev then 0 else (d : ℤ) := by
  dsimp only
  intro n hn
  have h := hA n hn
  rcases c with ⟨a, b⟩
  cases swap <;> cases a <;> cases b <;>
    simp [originalLaurentAxisIndex] at h ⊢ <;> omega

/-- The actual Laurent difference is regular in ANY coordinate shared by two
charts. Genuine original corner coefficients and coordinate cancellation pay
the bound; a full Laurent polynomial is never silently treated as an overlap. -/
theorem originalLaurent_shared_axis_regular
    (c c' : Bool × Bool) (swap : Bool) (d : ℕ)
    (q : AddMonoidAlgebra ℂ (ℕ × ℕ)) (hq : OriginalPositiveInSquare q d)
    (h0 : q.coeff (0, 0) ≠ 0) (hd : q.coeff (d, d) ≠ 0)
    (A A' H : AddMonoidAlgebra ℂ (ℤ × ℤ))
    (hA : OriginalLaurentChartBound c d A) (hA' : OriginalLaurentChartBound c' d A')
    (hsame : (if swap then c.2 else c.1) = (if swap then c'.2 else c'.1))
    (hH : originalPositiveLaurentEmbedding q * H = A - A') :
    let rev := !(if swap then c.2 else c.1)
    ∀ n, H.coeff n ≠ 0 → (originalLaurentAxisIndex swap rev n).1 ≤ 0 := by
  dsimp only
  let rev := !(if swap then c.2 else c.1)
  have hrev : (!(if swap then c'.2 else c'.1)) = rev := congrArg Bool.not hsame.symm
  have hprod : ∀ n ∈ (originalPositiveLaurentEmbedding q * H).coeff.support,
      (originalLaurentAxisIndex swap rev n).1 ≤ if rev then 0 else (d : ℤ) := by
    intro n hn
    rw [hH] at hn
    have hn0 := Finsupp.mem_support_iff.mp hn
    by_cases ha : A.coeff n = 0
    · have ha' : A'.coeff n ≠ 0 := by
        intro hz
        exact hn0 (by simp [ha, hz])
      simpa only [hrev] using originalLaurentChartBound_axis c' swap d A' hA' n ha'
    · exact originalLaurentChartBound_axis c swap d A hA n ha
  intro n hn
  exact originalLaurent_axis_bound_of_mul swap rev q d hq h0 hd H hprod n
    (Finsupp.mem_support_iff.mpr hn)

end
end MeyerGeneralProblem.StrongParity

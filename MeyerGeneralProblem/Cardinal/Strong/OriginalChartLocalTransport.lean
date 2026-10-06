module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalLaurentAdditiveGluing

@[expose] public section

/-! Literal transport of local separate-pole numerators into the SAME original
Laurent coordinates. Their degree shifts give half-plane bounds, and regular
chart corrections preserve those bounds. No degree bound on a local lift is
assumed: its output becomes bounded only after actual four-chart gluing. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- The original coordinate embedding is the literal pair of integer casts. -/
theorem originalNativeIntegerEmbedding_apply (n : ℕ × ℕ) :
    originalNativeIntegerEmbedding n = ((n.1 : ℤ), (n.2 : ℤ)) := rfl

/-- A section with block degree d is nonnegative on affine coordinates and at
most d on inverted coordinates in the original Laurent variables. -/
def OriginalLaurentChartBound (c : Bool × Bool) (d : ℕ)
    (L : AddMonoidAlgebra ℂ (ℤ × ℤ)) : Prop :=
  ∀ n, L.coeff n ≠ 0 → (if c.1 then n.1 ≤ (d : ℤ) else 0 ≤ n.1) ∧
    (if c.2 then n.2 ≤ (d : ℤ) else 0 ≤ n.2)

/-- Whole integer reflection is globally involutive, even for unbounded native
local lifts. All rows and every coefficient collision are retained. -/
theorem originalLaurentChartReflection_involutive (c : Bool × Bool) (d : ℕ)
    (L : AddMonoidAlgebra ℂ (ℤ × ℤ)) :
    originalLaurentChartReflection c d (originalLaurentChartReflection c d L) = L := by
  apply AddMonoidAlgebra.coeff_injective
  change Finsupp.mapDomain (originalChartIntegerIndex c d)
    (Finsupp.mapDomain (originalChartIntegerIndex c d) L.coeff) = L.coeff
  rw [← Finsupp.mapDomain_comp]
  calc
    _ = L.coeff.mapDomain id := Finsupp.mapDomain_congr fun n _ =>
      originalChartIntegerIndex_involutive c d n
    _ = L.coeff := Finsupp.mapDomain_id

/-- ANY genuine positive local lift pulls back with its exact block-degree
half-plane bound; no upper degree on the local polynomial is assumed. -/
theorem originalPositive_local_pullback_bound (c : Bool × Bool) (d : ℕ)
    (U : AddMonoidAlgebra ℂ (ℕ × ℕ)) :
    OriginalLaurentChartBound c d
      (originalLaurentChartReflection c d (originalPositiveLaurentEmbedding U)) := by
  intro n hn
  have hs := Finsupp.mem_support_iff.mpr hn
  change n ∈ (Finsupp.mapDomain (originalChartIntegerIndex c d)
    (originalPositiveLaurentEmbedding U).coeff).support at hs
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hs)
  rw [originalPositiveLaurentEmbedding_coeff,
    originalPositivePolynomialIntegerCoefficients_support] at hm
  obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hm
  rw [originalNativeIntegerEmbedding_apply]
  rcases c with ⟨a, b⟩
  cases a <;> cases b <;>
    dsimp [originalChartIntegerIndex, originalChartIntegerShift,
      originalChartIntegerSign] <;>
    constructor <;> omega

/-- The literal local polynomial identity becomes the SAME original numerator
identity after the exact degree shifts. No rational transition certificate. -/
theorem originalPositive_local_split_pullback (c : Bool × Bool) (dq de : ℕ)
    (q e r U V : AddMonoidAlgebra ℂ (ℕ × ℕ))
    (hq : OriginalPositiveInSquare q dq) (he : OriginalPositiveInSquare e de)
    (hr : OriginalPositiveInSquare r (dq + de))
    (hsplit : originalPositiveChartReflection c (dq + de) r =
      originalPositiveChartReflection c de e * U + originalPositiveChartReflection c dq q * V) :
    originalPositiveLaurentEmbedding r =
      originalPositiveLaurentEmbedding e *
        originalLaurentChartReflection c dq (originalPositiveLaurentEmbedding U) +
      originalPositiveLaurentEmbedding q *
        originalLaurentChartReflection c de (originalPositiveLaurentEmbedding V) := by
  have ht := congrArg (fun p => originalLaurentChartReflection c (dq + de)
    (originalPositiveLaurentEmbedding p)) hsplit
  have hq' : originalLaurentChartReflection c dq
      (originalPositiveLaurentEmbedding (originalPositiveChartReflection c dq q)) =
        originalPositiveLaurentEmbedding q := by
    rw [originalPositiveChartReflection_laurent c dq q hq,
      originalLaurentChartReflection_involutive]
  have he' : originalLaurentChartReflection c de
      (originalPositiveLaurentEmbedding (originalPositiveChartReflection c de e)) =
        originalPositiveLaurentEmbedding e := by
    rw [originalPositiveChartReflection_laurent c de e he,
      originalLaurentChartReflection_involutive]
  have h1 : originalLaurentChartReflection c (dq + de)
      (originalPositiveLaurentEmbedding (originalPositiveChartReflection c de e) * originalPositiveLaurentEmbedding U) =
        originalPositiveLaurentEmbedding e * originalLaurentChartReflection c dq (originalPositiveLaurentEmbedding U) := by
    rw [Nat.add_comm dq de, originalLaurentChartReflection_mul, he']
  have h2 : originalLaurentChartReflection c (dq + de)
      (originalPositiveLaurentEmbedding (originalPositiveChartReflection c dq q) * originalPositiveLaurentEmbedding V) =
        originalPositiveLaurentEmbedding q * originalLaurentChartReflection c de (originalPositiveLaurentEmbedding V) := by
    rw [originalLaurentChartReflection_mul, hq']
  simp only [map_add, map_mul] at ht
  rw [originalPositiveChartReflection_laurent c (dq + de) r hr,
    originalLaurentChartReflection_involutive, h1, h2] at ht
  exact ht

/-- Two sections with the same chart degree have a difference with that degree. -/
theorem originalLaurentChartBound_sub (c : Bool × Bool) (d : ℕ)
    (A B : AddMonoidAlgebra ℂ (ℤ × ℤ))
    (hA : OriginalLaurentChartBound c d A) (hB : OriginalLaurentChartBound c d B) :
    OriginalLaurentChartBound c d (A - B) := by
  intro n hn
  by_cases ha : A.coeff n = 0
  · have hb : B.coeff n ≠ 0 := by
      intro hb
      exact hn (by simp [ha, hb])
    exact hB n hb
  · exact hA n ha

/-- Adding two sections preserves their actual shared chart degree. -/
theorem originalLaurentChartBound_add (c : Bool × Bool) (d : ℕ)
    (A B : AddMonoidAlgebra ℂ (ℤ × ℤ))
    (hA : OriginalLaurentChartBound c d A) (hB : OriginalLaurentChartBound c d B) :
    OriginalLaurentChartBound c d (A + B) := by
  intro n hn
  by_cases ha : A.coeff n = 0
  · have hb : B.coeff n ≠ 0 := by
      intro hb
      exact hn (by simp [ha, hb])
    exact hB n hb
  · exact hA n ha

/-- A regular chart correction multiplied by the actual bounded divisor stays
within its section degree. Both integer coordinate bounds are proved literally. -/
theorem originalLaurentChartBound_mul_regular (c : Bool × Bool) (d : ℕ)
    (q : AddMonoidAlgebra ℂ (ℕ × ℕ)) (hq : OriginalPositiveInSquare q d)
    (S : AddMonoidAlgebra ℂ (ℤ × ℤ)) (hS : OriginalLaurentChartRegular c S) :
    OriginalLaurentChartBound c d (originalPositiveLaurentEmbedding q * S) := by
  intro n hn
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp
    (AddMonoidAlgebra.support_coeff_mul_subset _ _ (Finsupp.mem_support_iff.mpr hn))
  rw [originalPositiveLaurentEmbedding_coeff,
    originalPositivePolynomialIntegerCoefficients_support] at ha
  obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp ha
  have hq' := hq p hp
  have hs := hS b (Finsupp.mem_support_iff.mp hb)
  rw [originalNativeIntegerEmbedding_apply]
  rcases c with ⟨x, y⟩
  cases x <;> cases y <;>
    simp only [Bool.false_eq_true, reduceIte, Prod.fst_add, Prod.snd_add] at hs ⊢ <;>
    constructor <;> omega

/-- A Laurent section bounded on ALL four charts is a genuine positive global
polynomial of the required square degree. No global-polynomial certificate. -/
theorem originalLaurent_all_chart_bounds_positive (d : ℕ)
    (L : AddMonoidAlgebra ℂ (ℤ × ℤ)) (hL : ∀ c, OriginalLaurentChartBound c d L) :
    ∃ U : AddMonoidAlgebra ℂ (ℕ × ℕ), originalPositiveLaurentEmbedding U = L ∧
      OriginalPositiveInSquare U d := by
  have hnonneg : ∀ n ∈ L.coeff.support, 0 ≤ n.1 ∧ 0 ≤ n.2 := by
    intro n hn
    simpa using hL (false, false) n (Finsupp.mem_support_iff.mp hn)
  obtain ⟨U, hU⟩ := originalLaurent_nonnegative_positive L hnonneg
  refine ⟨U, hU, ?_⟩
  intro n hn
  have hc : L.coeff (originalNativeIntegerEmbedding n) ≠ 0 := by
    rw [← hU, originalPositiveLaurentEmbedding_coeff,
      originalPositivePolynomialIntegerCoefficients_apply]
    exact Finsupp.mem_support_iff.mp hn
  have ht := hL (true, true) (originalNativeIntegerEmbedding n) hc
  change (n.1 : ℤ) ≤ (d : ℤ) ∧ (n.2 : ℤ) ≤ (d : ℤ) at ht
  constructor <;> omega

end
end MeyerGeneralProblem.StrongParity

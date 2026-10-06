module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalChartLaurentFractions

@[expose] public section

/-! Finite Laurent clearing and genuine divisor intersection. A common positive
monomial clears arbitrary Laurent numerators into the original polynomial ring.
Relative primality in that ring then pays the Laurent pole intersection, without
assuming a localization certificate or a multivariate Bezout identity. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- Every Laurent polynomial supported in the nonnegative quadrant is literally
the image of a genuine positive polynomial, retaining all coefficients. -/
theorem originalLaurent_nonnegative_positive (L : AddMonoidAlgebra ℂ (ℤ × ℤ))
    (hL : ∀ n ∈ L.coeff.support, 0 ≤ n.1 ∧ 0 ≤ n.2) :
    ∃ P : AddMonoidAlgebra ℂ (ℕ × ℕ), originalPositiveLaurentEmbedding P = L := by
  let P : AddMonoidAlgebra ℂ (ℕ × ℕ) :=
    AddMonoidAlgebra.ofCoeff (L.coeff.mapDomain (fun n => (n.1.toNat, n.2.toNat)))
  refine ⟨P, ?_⟩
  apply AddMonoidAlgebra.coeff_injective
  change Finsupp.mapDomain originalNativeIntegerEmbedding
    (Finsupp.mapDomain (fun n : ℤ × ℤ => (n.1.toNat, n.2.toNat)) L.coeff) = L.coeff
  rw [← Finsupp.mapDomain_comp]
  calc
    _ = L.coeff.mapDomain id := Finsupp.mapDomain_congr fun n hn => by
      change ((n.1.toNat : ℤ), (n.2.toNat : ℤ)) = n
      exact Prod.ext (Int.toNat_of_nonneg (hL n hn).1) (Int.toNat_of_nonneg (hL n hn).2)
    _ = L.coeff := Finsupp.mapDomain_id

/-- A single finite positive monomial simultaneously clears any two genuine
Laurent numerators. The shift and positive polynomials are derived outputs. -/
theorem originalLaurent_positive_clear_two (A B : AddMonoidAlgebra ℂ (ℤ × ℤ)) :
    ∃ n : ℤ × ℤ, ∃ P Q : AddMonoidAlgebra ℂ (ℕ × ℕ),
      AddMonoidAlgebra.single n (1 : ℂ) * A = originalPositiveLaurentEmbedding P ∧
      AddMonoidAlgebra.single n (1 : ℂ) * B = originalPositiveLaurentEmbedding Q := by
  classical
  let s := A.coeff.support ∪ B.coeff.support
  let n : ℤ × ℤ := ((s.sup (fun p : ℤ × ℤ => (-p.1).toNat) : ℕ),
    (s.sup (fun p : ℤ × ℤ => (-p.2).toNat) : ℕ))
  have hs (p : ℤ × ℤ) (hp : p ∈ s) : 0 ≤ (n + p).1 ∧ 0 ≤ (n + p).2 := by
    have h1 := Finset.le_sup (f := fun p : ℤ × ℤ => (-p.1).toNat) hp
    have h2 := Finset.le_sup (f := fun p : ℤ × ℤ => (-p.2).toNat) hp
    dsimp only [n, Prod.fst_add, Prod.snd_add]
    constructor <;> omega
  have hpos (L : AddMonoidAlgebra ℂ (ℤ × ℤ)) (h : L.coeff.support ⊆ s) :
      ∀ p ∈ (AddMonoidAlgebra.single n (1 : ℂ) * L).coeff.support,
        0 ≤ p.1 ∧ 0 ≤ p.2 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp
      (AddMonoidAlgebra.support_coeff_single_mul_subset L (1 : ℂ) n hp)
    exact hs q (h hq)
  obtain ⟨P, hP⟩ := originalLaurent_nonnegative_positive _ (hpos A Finset.subset_union_left)
  obtain ⟨Q, hQ⟩ := originalLaurent_nonnegative_positive _ (hpos B Finset.subset_union_right)
  exact ⟨n, P, Q, hP.symm, hQ.symm⟩

/-- A rational function simultaneously bounded by two relatively prime original
positive divisors is an actual Laurent polynomial. Common monomial clearing,
divisibility and all field injectivity are paid internally; no Bezout input. -/
theorem originalLaurent_fraction_intersection (q e : AddMonoidAlgebra ℂ (ℕ × ℕ))
    (hq : q ≠ 0) (hrel : IsRelPrime q e)
    (x : FractionRing (AddMonoidAlgebra ℂ (ℤ × ℤ)))
    (A B : AddMonoidAlgebra ℂ (ℤ × ℤ))
    (hA : algebraMap _ _ (originalPositiveLaurentEmbedding q) * x = algebraMap _ _ A)
    (hB : algebraMap _ _ (originalPositiveLaurentEmbedding e) * x = algebraMap _ _ B) :
    ∃ H : AddMonoidAlgebra ℂ (ℤ × ℤ), algebraMap _ _ H = x := by
  let f := algebraMap (AddMonoidAlgebra ℂ (ℤ × ℤ))
    (FractionRing (AddMonoidAlgebra ℂ (ℤ × ℤ)))
  have hi : Function.Injective f := IsFractionRing.injective _ _
  obtain ⟨n, P, Q, hP, hQ⟩ := originalLaurent_positive_clear_two A B
  have hcross : e * P = q * Q := by
    apply originalPositiveLaurentEmbedding_injective
    apply hi
    simp only [map_mul, ← hP, ← hQ]
    rw [← hA, ← hB]
    ring
  have hd : q ∣ P := hrel.dvd_of_dvd_mul_left (by rw [hcross]; exact dvd_mul_right q Q)
  obtain ⟨U, hU⟩ := hd
  let H := AddMonoidAlgebra.single (-n) (1 : ℂ) * originalPositiveLaurentEmbedding U
  have hq0 : f (originalPositiveLaurentEmbedding q) ≠ 0 :=
    (map_ne_zero_iff f hi).mpr (originalPositiveLaurentEmbedding_ne_zero q hq)
  have hmul : originalPositiveLaurentEmbedding q * H = A := by
    dsimp only [H]
    calc
      _ = AddMonoidAlgebra.single (-n) (1 : ℂ) * originalPositiveLaurentEmbedding P := by
        rw [hU, map_mul]; ring
      _ = A := by
        rw [← hP, ← mul_assoc, AddMonoidAlgebra.single_mul_single]
        simp only [neg_add_cancel, one_mul, ← AddMonoidAlgebra.one_def, one_mul]
  refine ⟨H, ?_⟩
  change f H = x
  apply mul_left_cancel₀ hq0
  simpa only [← map_mul, hmul] using hA.symm

end
end MeyerGeneralProblem.StrongParity

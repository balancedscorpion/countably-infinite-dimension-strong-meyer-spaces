module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalLaurentPositiveClearing
public import Mathlib.Algebra.Order.Monoid.Lex
public import Mathlib.Algebra.Order.Monoid.Prod

@[expose] public section

/-! Actual coefficient extremums for Laurent overlap regularity. Relative-prime
intersection only gives a full Laurent polynomial; the nonzero extreme corners
of the original bounded divisor also force the correct coordinate half-plane. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- A chosen coordinate comes first; simultaneous negation selects a minimum
instead of a maximum, without truncating either integer coordinate. -/
def originalLaurentAxisIndex (swap rev : Bool) (n : ℤ × ℤ) : ℤ × ℤ :=
  let p := if swap then (n.2, n.1) else n
  if rev then (-p.1, -p.2) else p

/-- The signed and possibly swapped native index is an exact additive map. -/
theorem originalLaurentAxisIndex_add (swap rev : Bool) (a b : ℤ × ℤ) :
    originalLaurentAxisIndex swap rev (a + b) =
      originalLaurentAxisIndex swap rev a + originalLaurentAxisIndex swap rev b := by
  cases swap <;> cases rev <;> apply Prod.ext <;> simp [originalLaurentAxisIndex, add_comm]

/-- The lexicographic grading is injective on the whole integer lattice. -/
theorem originalLaurentAxisIndex_injective (swap rev : Bool) :
    Function.Injective (originalLaurentAxisIndex swap rev) := by
  intro a b h
  rcases a with ⟨a₁, a₂⟩; rcases b with ⟨b₁, b₂⟩
  cases swap <;> cases rev <;>
    simpa [originalLaurentAxisIndex, Prod.mk.injEq, and_comm] using h

/-- Exact coefficient multiplication at independently bounded extremums. This
uses a linear ordered group directly, so there is no fictitious bottom in Z². -/
theorem originalLaurent_coeff_add_of_support_le
    {B : Type*} [AddCommGroup B] [LinearOrder B]
    [AddLeftStrictMono B] [AddRightStrictMono B]
    (D : (ℤ × ℤ) →+ B) (hD : Function.Injective D)
    (p q : AddMonoidAlgebra ℂ (ℤ × ℤ)) (a b : ℤ × ℤ)
    (hp : ∀ n ∈ p.coeff.support, D n ≤ D a)
    (hq : ∀ n ∈ q.coeff.support, D n ≤ D b) :
    (p * q).coeff (a + b) = p.coeff a * q.coeff b := by
  classical
  have := addLeftMono_of_addLeftStrictMono B
  have := addRightMono_of_addRightStrictMono B
  simp_rw [AddMonoidAlgebra.coeff_mul, Finsupp.sum]
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b, ite_eq_left rfl]
  · intro n hn hne
    apply ite_eq_right
    intro he
    have heD := congrArg D he
    simp only [map_add] at heD
    exact (add_lt_add_right ((hq n hn).lt_of_ne (hD.ne_iff.mpr hne)) (D a)).ne heD
  · intro h
    rw [ite_eq_left rfl, Finsupp.notMem_support_iff.mp h, mul_zero]
  · intro n hn hne
    apply Finset.sum_eq_zero
    intro m hm
    apply ite_eq_right
    intro he
    have heD := congrArg D he
    simp only [map_add] at heD
    exact (add_lt_add_of_lt_of_le ((hp n hn).lt_of_ne (hD.ne_iff.mpr hne)) (hq m hm)).ne heD
  · intro h
    apply Finset.sum_eq_zero
    intro n hn
    split_ifs <;> simp [Finsupp.notMem_support_iff.mp h]

/-- A genuine bounded original divisor with nonzero bottom and top corners
cannot conceal a forbidden overlap coordinate in its Laurent quotient. -/
theorem originalLaurent_axis_bound_of_mul (swap rev : Bool)
    (q : AddMonoidAlgebra ℂ (ℕ × ℕ)) (d : ℕ) (hq : OriginalPositiveInSquare q d)
    (h0 : q.coeff (0, 0) ≠ 0) (hd : q.coeff (d, d) ≠ 0)
    (H : AddMonoidAlgebra ℂ (ℤ × ℤ))
    (hprod : ∀ n ∈ (originalPositiveLaurentEmbedding q * H).coeff.support,
      (originalLaurentAxisIndex swap rev n).1 ≤ if rev then 0 else (d : ℤ)) :
    ∀ n ∈ H.coeff.support, (originalLaurentAxisIndex swap rev n).1 ≤ 0 := by
  classical
  let D : (ℤ × ℤ) →+ Lex (ℤ × ℤ) :=
    { toFun := fun n => toLex (originalLaurentAxisIndex swap rev n)
      map_zero' := by cases swap <;> cases rev <;> rfl
      map_add' := fun a b => congrArg toLex (originalLaurentAxisIndex_add swap rev a b) }
  have hDi : Function.Injective D :=
    toLex.injective.comp (originalLaurentAxisIndex_injective swap rev)
  by_cases hH : H = 0
  · subst H; simp
  have hs : H.coeff.support.Nonempty := by
    simpa [Finsupp.support_nonempty_iff] using hH
  obtain ⟨m, hm, hmax⟩ := H.coeff.support.exists_max_image D hs
  let a : ℤ × ℤ := if rev then (0, 0) else ((d : ℤ), (d : ℤ))
  have ha : (originalPositiveLaurentEmbedding q).coeff a ≠ 0 := by
    cases rev
    · change (originalPositiveLaurentEmbedding q).coeff (originalNativeIntegerEmbedding (d, d)) ≠ 0
      rw [originalPositiveLaurentEmbedding_coeff, originalPositivePolynomialIntegerCoefficients_apply]
      exact hd
    · change (originalPositiveLaurentEmbedding q).coeff (originalNativeIntegerEmbedding (0, 0)) ≠ 0
      rw [originalPositiveLaurentEmbedding_coeff, originalPositivePolynomialIntegerCoefficients_apply]
      exact h0
  have hqD : ∀ n ∈ (originalPositiveLaurentEmbedding q).coeff.support, D n ≤ D a := by
    intro n hn
    rw [originalPositiveLaurentEmbedding_coeff,
      originalPositivePolynomialIntegerCoefficients_support] at hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hn
    have hb := hq p hp
    change toLex (originalLaurentAxisIndex swap rev ((p.1 : ℤ), (p.2 : ℤ))) ≤
      toLex (originalLaurentAxisIndex swap rev a)
    cases swap <;> cases rev <;>
      simp only [a, originalLaurentAxisIndex, Bool.false_eq_true, reduceIte]
    all_goals apply Prod.Lex.toLex_mono
    all_goals constructor <;> omega
  have hc := originalLaurent_coeff_add_of_support_le D hDi _ H a m hqD hmax
  have hm0 := Finsupp.mem_support_iff.mp hm
  have hmem : a + m ∈ (originalPositiveLaurentEmbedding q * H).coeff.support :=
    Finsupp.mem_support_iff.mpr (hc.trans_ne (mul_ne_zero ha hm0))
  have hb := hprod (a + m) hmem
  intro n hn
  have hnm : (originalLaurentAxisIndex swap rev n).1 ≤
      (originalLaurentAxisIndex swap rev m).1 :=
    Prod.Lex.monotone_fst_ofLex (hmax n hn)
  rw [originalLaurentAxisIndex_add] at hb
  cases swap <;> cases rev <;> simp [a, originalLaurentAxisIndex] at hb hnm ⊢ <;> omega

end
end MeyerGeneralProblem.StrongParity

module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalChartCorners

@[expose] public section

/-! Explicit additive gluing in the genuine integer coefficient algebra. The
horizontal split and zero-first-coordinate vertical correction give four actual
regular chart functions. Actual prefix applications must derive the cocycle and
all overlap bounds internally; this helper alone is not a prefix theorem. -/
namespace MeyerGeneralProblem.StrongParity
open scoped Classical
noncomputable section

/-- Retain precisely the literal coefficients satisfying a chosen predicate. -/
def originalLaurentCoefficientCut (p : (ℤ × ℤ) → Prop) :
    AddMonoidAlgebra ℂ (ℤ × ℤ) →ₗ[ℂ] AddMonoidAlgebra ℂ (ℤ × ℤ) := by
  classical
  exact
    { toFun := fun L => AddMonoidAlgebra.ofCoeff (L.coeff.filter p)
      map_add' := fun A B => by
        apply AddMonoidAlgebra.coeff_injective
        simp [Finsupp.filter_add]
      map_smul' := fun a L => by
        apply AddMonoidAlgebra.coeff_injective
        ext n
        simp [Finsupp.filter_apply] }

/-- Every cut is literal on ALL integer rows, including zero coefficients. -/
theorem originalLaurentCoefficientCut_coeff (p : (ℤ × ℤ) → Prop)
    (L : AddMonoidAlgebra ℂ (ℤ × ℤ)) (n : ℤ × ℤ) :
    (originalLaurentCoefficientCut p L).coeff n = if p n then L.coeff n else 0 := by
  classical
  rfl

/-- A genuine regular chart function has nonnegative coordinates on its affine
coordinates and nonpositive coordinates on its inverted coordinates. -/
def OriginalLaurentChartRegular (c : Bool × Bool) (L : AddMonoidAlgebra ℂ (ℤ × ℤ)) : Prop :=
  ∀ n, L.coeff n ≠ 0 → (if c.1 then n.1 ≤ 0 else 0 ≤ n.1) ∧
    (if c.2 then n.2 ≤ 0 else 0 ≤ n.2)

/-- The explicit four-chart coefficient correction splits a genuine additive
overlap cocycle. Its coefficients, chart functions and corrections are outputs. -/
theorem originalLaurent_additive_four_chart_gluing
    (Hp Hm Vp Vm : AddMonoidAlgebra ℂ (ℤ × ℤ))
    (hHp : ∀ n, Hp.coeff n ≠ 0 → 0 ≤ n.2)
    (hHm : ∀ n, Hm.coeff n ≠ 0 → n.2 ≤ 0)
    (hVp : ∀ n, Vp.coeff n ≠ 0 → 0 ≤ n.1)
    (hVm : ∀ n, Vm.coeff n ≠ 0 → n.1 ≤ 0)
    (hcompat : Hp - Hm = Vp - Vm) :
    ∃ S : (Bool × Bool) → AddMonoidAlgebra ℂ (ℤ × ℤ),
      (∀ c, OriginalLaurentChartRegular c (S c)) ∧
      S (false, false) - S (true, false) = Hp ∧
      S (false, true) - S (true, true) = Hm ∧
      S (false, false) - S (false, true) = Vp ∧
      S (true, false) - S (true, true) = Vm := by
  classical
  let P := originalLaurentCoefficientCut (fun n => 0 ≤ n.1)
  let N := originalLaurentCoefficientCut (fun n => n.1 < 0)
  let D := Vp - (P Hp - P Hm)
  let Dp := originalLaurentCoefficientCut (fun n => 0 ≤ n.2) D
  let Dn := originalLaurentCoefficientCut (fun n => n.2 < 0) D
  let S (c : Bool × Bool) :=
    (if c.1 then -N (if c.2 then Hm else Hp) else P (if c.2 then Hm else Hp)) +
      (if c.2 then -Dn else Dp)
  have hDz (n : ℤ × ℤ) (hn : n.1 ≠ 0) : D.coeff n = 0 := by
    have hc := congrArg (fun L : AddMonoidAlgebra ℂ (ℤ × ℤ) => L.coeff n) hcompat
    simp only [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply] at hc
    by_cases h : 0 ≤ n.1
    · have hVm0 : Vm.coeff n = 0 := by
        by_contra he
        have := hVm n he
        omega
      simp only [D, P, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
        originalLaurentCoefficientCut_coeff, h, ite_true]
      rw [hVm0] at hc
      linear_combination -hc
    · have hVp0 : Vp.coeff n = 0 := by
        by_contra he
        exact h (hVp n he)
      simp [D, P, originalLaurentCoefficientCut_coeff, h, hVp0]
  have hS : ∀ c, OriginalLaurentChartRegular c (S c) := by
    rintro ⟨a, b⟩ n hn
    constructor
    · cases a
      · by_contra hb
        have hfirst : n.1 < 0 := by simpa using hb
        have hz := hDz n (by omega)
        have hpos : ¬0 ≤ n.1 := by omega
        apply hn
        cases b <;> simp [S, P, Dp, Dn, originalLaurentCoefficientCut_coeff, hpos, hz]
      · by_contra hb
        have hfirst : 0 < n.1 := by simpa using hb
        have hz := hDz n (by omega)
        have hneg : ¬n.1 < 0 := by omega
        apply hn
        cases b <;> simp [S, N, Dp, Dn, originalLaurentCoefficientCut_coeff, hneg, hz]
    · cases b
      · by_contra hb
        have hsecond : n.2 < 0 := by simpa using hb
        have hz : Hp.coeff n = 0 := by
          by_contra he
          have := hHp n he
          omega
        have hpos : ¬0 ≤ n.2 := by omega
        apply hn
        cases a <;> simp [S, P, N, Dp, originalLaurentCoefficientCut_coeff, hpos, hz]
      · by_contra hb
        have hsecond : 0 < n.2 := by simpa using hb
        have hz : Hm.coeff n = 0 := by
          by_contra he
          have := hHm n he
          omega
        have hneg : ¬n.2 < 0 := by omega
        apply hn
        cases a <;> simp [S, P, N, Dn, originalLaurentCoefficientCut_coeff, hneg, hz]
  refine ⟨S, hS, ?_, ?_, ?_, ?_⟩
  all_goals apply AddMonoidAlgebra.coeff_injective
  all_goals ext n
  all_goals have hc := congrArg (fun L : AddMonoidAlgebra ℂ (ℤ × ℤ) => L.coeff n) hcompat
  all_goals simp only [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply] at hc
  all_goals by_cases h0 : 0 ≤ n.1
  all_goals by_cases h1 : n.1 < 0
  all_goals by_cases h2 : 0 ≤ n.2
  all_goals by_cases h3 : n.2 < 0
  all_goals try omega
  all_goals simp [S, P, N, Dp, Dn, D, originalLaurentCoefficientCut_coeff, h0, h1, h2, h3]
  all_goals first | linear_combination -hc | ring

end
end MeyerGeneralProblem.StrongParity

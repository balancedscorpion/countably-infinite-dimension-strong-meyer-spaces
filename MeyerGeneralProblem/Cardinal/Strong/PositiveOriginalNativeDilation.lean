module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalNativeExponents

@[expose] public section

/-! Exact coefficient descent through a positive native dilation. Division is
used only after EVERY original support exponent is proved divisible. No rows
are discarded: dilating the descended polynomial returns the entire input. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- Literal multiplication of BOTH positive native coordinates. -/
def originalNativePositiveDilation (d : ℕ) : (ℕ × ℕ) →+ (ℕ × ℕ) where
  toFun n := (d * n.1, d * n.2)
  map_zero' := by simp
  map_add' p q := by simp [Nat.mul_add]

/-- Dilation as a genuine algebra map, retaining every coefficient collision. -/
def originalPositiveDilation (d : ℕ) :
    AddMonoidAlgebra ℂ (ℕ × ℕ) →ₐ[ℂ] AddMonoidAlgebra ℂ (ℕ × ℕ) :=
  AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ (originalNativePositiveDilation d)

/-- Positive dilation preserves every distinction of native labels. -/
theorem originalNativePositiveDilation_injective (d : ℕ) (hd : 0 < d) :
    Function.Injective (originalNativePositiveDilation d) := by
  intro a b h
  have h₁ : d * a.1 = d * b.1 := congrArg Prod.fst h
  have h₂ : d * a.2 = d * b.2 := congrArg Prod.snd h
  exact Prod.ext (Nat.eq_of_mul_eq_mul_left hd h₁) (Nat.eq_of_mul_eq_mul_left hd h₂)

/-- The entire dilated coefficient function is the literal label pushforward. -/
theorem originalPositiveDilation_coeff (d : ℕ) (p : AddMonoidAlgebra ℂ (ℕ × ℕ)) :
    (originalPositiveDilation d p).coeff = Finsupp.mapDomain (originalNativePositiveDilation d) p.coeff := rfl

/-- Every single native monomial retains its coefficient and dilated label. -/
theorem originalPositiveDilation_single (d : ℕ) (n : ℕ × ℕ) (c : ℂ) :
    originalPositiveDilation d (AddMonoidAlgebra.single n c) =
      AddMonoidAlgebra.single (d * n.1, d * n.2) c :=
  AddMonoidAlgebra.mapDomain_single

/-- Positive dilation is injective on the whole positive algebra. -/
theorem originalPositiveDilation_injective (d : ℕ) (hd : 0 < d) :
    Function.Injective (originalPositiveDilation d) :=
  AddMonoidAlgebra.mapDomain_injective (originalNativePositiveDilation_injective d hd)

/-- Every native coefficient is retained at its dilated label. -/
theorem originalPositiveDilation_coefficient (d : ℕ) (hd : 0 < d)
    (p : AddMonoidAlgebra ℂ (ℕ × ℕ)) (n : ℕ × ℕ) :
    (originalPositiveDilation d p).coeff (d * n.1, d * n.2) = p.coeff n :=
  Finsupp.mapDomain_apply_of_injective (originalNativePositiveDilation_injective d hd) p.coeff n

/-- All original coefficients descend by division of their two labels. -/
def originalPositiveNativeDescent (d : ℕ) (p : AddMonoidAlgebra ℂ (ℕ × ℕ)) :
    AddMonoidAlgebra ℂ (ℕ × ℕ) :=
  AddMonoidAlgebra.ofCoeff (p.coeff.mapDomain (fun n => (n.1 / d, n.2 / d)))

/-- EVERY divisible support label returns exactly; no support truncation. -/
theorem originalPositiveNativeDescent_roundtrip (d : ℕ) (p : AddMonoidAlgebra ℂ (ℕ × ℕ))
    (hdiv : ∀ n ∈ p.coeff.support, d ∣ n.1 ∧ d ∣ n.2) :
    originalPositiveDilation d (originalPositiveNativeDescent d p) = p := by
  apply AddMonoidAlgebra.coeff_injective
  change Finsupp.mapDomain (originalNativePositiveDilation d)
    (Finsupp.mapDomain (fun n : ℕ × ℕ => (n.1 / d, n.2 / d)) p.coeff) = p.coeff
  rw [← Finsupp.mapDomain_comp]
  calc
    _ = p.coeff.mapDomain id := Finsupp.mapDomain_congr fun n hn => by
      change (d * (n.1 / d), d * (n.2 / d)) = n
      exact Prod.ext (Nat.mul_div_cancel' (hdiv n hn).1) (Nat.mul_div_cancel' (hdiv n hn).2)
    _ = p.coeff := Finsupp.mapDomain_id

/-- A native coefficient is exactly the original coefficient at its dilated label. -/
theorem originalPositiveNativeDescent_coefficient (d : ℕ) (hd : 0 < d)
    (p : AddMonoidAlgebra ℂ (ℕ × ℕ))
    (hdiv : ∀ n ∈ p.coeff.support, d ∣ n.1 ∧ d ∣ n.2) (n : ℕ × ℕ) :
    (originalPositiveNativeDescent d p).coeff n = p.coeff (d * n.1, d * n.2) := by
  rw [← originalPositiveDilation_coefficient d hd, originalPositiveNativeDescent_roundtrip d p hdiv]

/-- The entire scaled square descends to the entire ORIGINAL native square. -/
theorem originalPositiveNativeDescent_inSquare (d s : ℕ) (hd : 0 < d)
    (p : AddMonoidAlgebra ℂ (ℕ × ℕ))
    (hdiv : ∀ n ∈ p.coeff.support, d ∣ n.1 ∧ d ∣ n.2)
    (hp : OriginalPositiveInSquare p (s * d)) :
    OriginalPositiveInSquare (originalPositiveNativeDescent d p) s := by
  intro n hn
  have hc := Finsupp.mem_support_iff.mp hn
  rw [originalPositiveNativeDescent_coefficient d hd p hdiv n] at hc
  have hb := hp _ (Finsupp.mem_support_iff.mpr hc)
  constructor <;> nlinarith [hb.1, hb.2]

/-- Precisely the top corner remains missing after descent. -/
theorem originalPositiveNativeDescent_top_zero (d s : ℕ) (hd : 0 < d)
    (p : AddMonoidAlgebra ℂ (ℕ × ℕ))
    (hdiv : ∀ n ∈ p.coeff.support, d ∣ n.1 ∧ d ∣ n.2)
    (htop : p.coeff (s * d, s * d) = 0) :
    (originalPositiveNativeDescent d p).coeff (s, s) = 0 := by
  rw [originalPositiveNativeDescent_coefficient d hd p hdiv, Nat.mul_comm d s, htop]

/-- Native dilation evaluates at the powers of the original variables. -/
theorem originalPositiveDilation_evaluation (d : ℕ) (p : AddMonoidAlgebra ℂ (ℕ × ℕ))
    (Z W : ℂ) :
    originalPositiveTorusEvaluation Z W (originalPositiveDilation d p) =
      originalPositiveTorusEvaluation (Z ^ d) (W ^ d) p := by
  refine AddMonoidAlgebra.induction_linear p ?_ ?_ ?_
  · simp
  · intro p q hp hq
    simp only [map_add, hp, hq]
  · intro n c
    rw [originalPositiveDilation_single, originalPositiveTorusEvaluation_single,
      originalPositiveTorusEvaluation_single]
    simp only [pow_mul]

end
end MeyerGeneralProblem.StrongParity

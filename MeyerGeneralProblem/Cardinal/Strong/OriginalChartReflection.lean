module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalChartIndices

@[expose] public section

/-! Genuine linear reflection at the complete native square bound. Whole Laurent
rows justify each chart, while fixed support bounds prevent Nat subtraction
from merging unrelated coefficients. Product identities retain all collisions. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- Reflection of native coefficients at the fixed whole square bound. -/
def originalPositiveChartReflection (c : Bool × Bool) (d : ℕ) :
    AddMonoidAlgebra ℂ (ℕ × ℕ) →ₗ[ℂ] AddMonoidAlgebra ℂ (ℕ × ℕ) :=
  AddMonoidAlgebra.mapDomainLinearMap ℂ ℂ (originalChartNativeIndex c d)

/-- Reflection of ALL integer coefficients, without a positivity restriction. -/
def originalLaurentChartReflection (c : Bool × Bool) (d : ℕ) :
    AddMonoidAlgebra ℂ (ℤ × ℤ) →ₗ[ℂ] AddMonoidAlgebra ℂ (ℤ × ℤ) :=
  AddMonoidAlgebra.mapDomainLinearMap ℂ ℂ (originalChartIntegerIndex c d)

/-- Signed coordinate substitution is a genuine Laurent algebra homomorphism. -/
def originalLaurentChartSign (c : Bool × Bool) :
    AddMonoidAlgebra ℂ (ℤ × ℤ) →ₐ[ℂ] AddMonoidAlgebra ℂ (ℤ × ℤ) :=
  AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ (originalChartIntegerSign c)

/-- The affine chart is literally the original coefficient polynomial at ANY fixed degree. -/
theorem originalPositiveChartReflection_affine (d : ℕ) (p : AddMonoidAlgebra ℂ (ℕ × ℕ)) :
    originalPositiveChartReflection (false, false) d p = p := by
  apply AddMonoidAlgebra.coeff_injective
  change Finsupp.mapDomain (originalChartNativeIndex (false, false) d) p.coeff = p.coeff
  have h : originalChartNativeIndex (false, false) d = id := by funext n; rfl
  rw [h, Finsupp.mapDomain_id]

/-- Every native monomial keeps its coefficient under fixed chart reflection. -/
theorem originalPositiveChartReflection_single (c : Bool × Bool) (d : ℕ) (n : ℕ × ℕ) (a : ℂ) :
    originalPositiveChartReflection c d (AddMonoidAlgebra.single n a) =
      AddMonoidAlgebra.single (originalChartNativeIndex c d n) a := by
  exact AddMonoidAlgebra.mapDomainLinearMap_single _ _ _

/-- Whole integer monomials also keep their coefficients under fixed reflection. -/
theorem originalLaurentChartReflection_single (c : Bool × Bool) (d : ℕ) (n : ℤ × ℤ) (a : ℂ) :
    originalLaurentChartReflection c d (AddMonoidAlgebra.single n a) =
      AddMonoidAlgebra.single (originalChartIntegerIndex c d n) a := by
  exact AddMonoidAlgebra.mapDomainLinearMap_single _ _ _

/-- Signed native coordinate substitution is exact on every Laurent monomial. -/
theorem originalLaurentChartSign_single (c : Bool × Bool) (n : ℤ × ℤ) (a : ℂ) :
    originalLaurentChartSign c (AddMonoidAlgebra.single n a) =
      AddMonoidAlgebra.single (originalChartIntegerSign c n) a :=
  AddMonoidAlgebra.mapDomain_single

/-- Fixed reflection is precisely signed Laurent substitution followed by its degree monomial. -/
theorem originalLaurentChartReflection_shift (c : Bool × Bool) (d : ℕ)
    (p : AddMonoidAlgebra ℂ (ℤ × ℤ)) :
    originalLaurentChartReflection c d p =
      AddMonoidAlgebra.single (originalChartIntegerShift c d) 1 * originalLaurentChartSign c p := by
  refine AddMonoidAlgebra.induction_linear p ?_ ?_ ?_
  · simp
  · intro p q hp hq
    simp only [map_add, hp, hq, mul_add]
  · intro n a
    rw [originalLaurentChartReflection_single, originalLaurentChartSign_single,
      AddMonoidAlgebra.single_mul_single, one_mul]
    rfl

/-- Whole Laurent reflection multiplies exactly when complete degree bounds are added. -/
theorem originalLaurentChartReflection_mul (c : Bool × Bool) (d e : ℕ)
    (p q : AddMonoidAlgebra ℂ (ℤ × ℤ)) :
    originalLaurentChartReflection c (d + e) (p * q) =
      originalLaurentChartReflection c d p * originalLaurentChartReflection c e q := by
  rw [originalLaurentChartReflection_shift, originalLaurentChartReflection_shift,
    originalLaurentChartReflection_shift, map_mul, originalChartIntegerShift_add]
  have hs : AddMonoidAlgebra.single (originalChartIntegerShift c d + originalChartIntegerShift c e) (1 : ℂ) =
      AddMonoidAlgebra.single (originalChartIntegerShift c d) (1 : ℂ) *
        AddMonoidAlgebra.single (originalChartIntegerShift c e) (1 : ℂ) := by
    simp only [AddMonoidAlgebra.single_mul_single, one_mul]
  rw [hs]
  ring

/-- The PROVED native square makes the exact embedding commute with whole integer reflection. -/
theorem originalPositiveChartReflection_laurent (c : Bool × Bool) (d : ℕ)
    (p : AddMonoidAlgebra ℂ (ℕ × ℕ)) (hp : OriginalPositiveInSquare p d) :
    originalPositiveLaurentEmbedding (originalPositiveChartReflection c d p) =
      originalLaurentChartReflection c d (originalPositiveLaurentEmbedding p) := by
  apply AddMonoidAlgebra.coeff_injective
  change Finsupp.mapDomain originalNativeIntegerEmbedding
      (Finsupp.mapDomain (originalChartNativeIndex c d) p.coeff) =
    Finsupp.mapDomain (originalChartIntegerIndex c d)
      (Finsupp.mapDomain originalNativeIntegerEmbedding p.coeff)
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  apply Finsupp.mapDomain_congr
  intro n hn
  exact originalChartNativeIndex_integer c d n (hp n hn)

/-- Reflection at the complete fixed degree keeps the actual whole native square. -/
theorem originalPositiveChartReflection_inSquare (c : Bool × Bool) (d : ℕ)
    (p : AddMonoidAlgebra ℂ (ℕ × ℕ)) (hp : OriginalPositiveInSquare p d) :
    OriginalPositiveInSquare (originalPositiveChartReflection c d p) d := by
  classical
  intro n hn
  change n ∈ (p.coeff.mapDomain (originalChartNativeIndex c d)).support at hn
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hn)
  exact originalChartNativeIndex_inSquare c d m (hp m hm)

/-- Under the internally justified whole square, all coefficients survive reflection and return exactly. -/
theorem originalPositiveChartReflection_involutive (c : Bool × Bool) (d : ℕ)
    (p : AddMonoidAlgebra ℂ (ℕ × ℕ)) (hp : OriginalPositiveInSquare p d) :
    originalPositiveChartReflection c d (originalPositiveChartReflection c d p) = p := by
  apply AddMonoidAlgebra.coeff_injective
  change (p.coeff.mapDomain (originalChartNativeIndex c d)).mapDomain (originalChartNativeIndex c d) = p.coeff
  rw [← Finsupp.mapDomain_comp]
  calc
    p.coeff.mapDomain (originalChartNativeIndex c d ∘ originalChartNativeIndex c d) = p.coeff.mapDomain id := by
      apply Finsupp.mapDomain_congr
      intro n hn
      exact originalChartNativeIndex_involutive_on_square c d n (hp n hn)
    _ = p.coeff := Finsupp.mapDomain_id

/-- A nonzero actual polynomial cannot become zero on any fixed chart under its proved square. -/
theorem originalPositiveChartReflection_ne_zero (c : Bool × Bool) (d : ℕ)
    (p : AddMonoidAlgebra ℂ (ℕ × ℕ)) (hp : OriginalPositiveInSquare p d) (hp0 : p ≠ 0) :
    originalPositiveChartReflection c d p ≠ 0 := by
  intro hz
  have h := originalPositiveChartReflection_involutive c d p hp
  rw [hz, map_zero] at h
  exact hp0 h.symm

/-- Native polynomial multiplication transports exactly at the PROVED sum of fixed whole bounds. -/
theorem originalPositiveChartReflection_mul (c : Bool × Bool) (d e : ℕ)
    (p q : AddMonoidAlgebra ℂ (ℕ × ℕ)) (hp : OriginalPositiveInSquare p d)
    (hq : OriginalPositiveInSquare q e) :
    originalPositiveChartReflection c (d + e) (p * q) =
      originalPositiveChartReflection c d p * originalPositiveChartReflection c e q := by
  apply originalPositiveLaurentEmbedding_injective
  rw [originalPositiveChartReflection_laurent c (d + e) (p * q)
    (originalPositiveInSquare_mul p q d e hp hq), map_mul,
    originalLaurentChartReflection_mul, map_mul,
    originalPositiveChartReflection_laurent c d p hp,
    originalPositiveChartReflection_laurent c e q hq]

/-- Every finite native product is reflected using exactly its full sum of sheet bounds. -/
theorem originalPositiveChartReflection_prod {ι : Type*} (c : Bool × Bool) (s : Finset ι)
    (p : ι → AddMonoidAlgebra ℂ (ℕ × ℕ)) (d : ι → ℕ)
    (hp : ∀ i ∈ s, OriginalPositiveInSquare (p i) (d i)) :
    originalPositiveChartReflection c (∑ i ∈ s, d i) (∏ i ∈ s, p i) =
      ∏ i ∈ s, originalPositiveChartReflection c (d i) (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty]
    change originalPositiveChartReflection c 0 (AddMonoidAlgebra.single (0, 0) 1) = _
    rw [originalPositiveChartReflection_single]
    rcases c with ⟨a, b⟩
    cases a <;> cases b <;> rfl
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, Finset.prod_insert hi]
    rw [originalPositiveChartReflection_mul c (d i) (∑ j ∈ s, d j) (p i) (∏ j ∈ s, p j)
      (hp i (Finset.mem_insert_self i s))
      (originalPositiveInSquare_prod s p d (fun j hj => hp j (Finset.mem_insert_of_mem hj)))]
    rw [ih (fun j hj => hp j (Finset.mem_insert_of_mem hj))]

end
end MeyerGeneralProblem.StrongParity

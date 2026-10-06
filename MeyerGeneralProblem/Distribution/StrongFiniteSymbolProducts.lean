module

public import MeyerGeneralProblem.Distribution.StrongFiniteOperations

@[expose] public section

/-!
# Genuine finite root-clearing products and ORIGINAL strong support

Finite translated exponential symbols act by actual continuous Schwartz
multipliers. Their exact ORIGINAL coefficient products, same-exponent strong
records and full Fourier convolution containers are proved internally. Zero
symbol values remove actual original rows before any restriction is made.
-/
namespace MeyerGeneralProblem
noncomputable section
open scoped FourierTransform

/-- Literal positive-phase symbol of the genuine finite exponential multiplier. -/
def finitePositiveExponentialSymbol {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (c : ι → ℂ) (x : ℝ) : ℂ :=
  ∑ i, c i * combModulationCharacter (a i) x

/-- Every ORIGINAL coefficient is multiplied by the actual finite exponential symbol. -/
theorem finiteExponentialMultiplication_isolation_apply {ι : Type*} [Fintype ι]
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hT : HasLocallyAtomicAction S T) (a : ι → ℝ) (c : ι → ℂ) (x : S.subtype) :
    finiteExponentialMultiplication a c T (S.isolationSchwartz x) =
      finitePositiveExponentialSymbol a c x * T (S.isolationSchwartz x) := by
  simp only [finiteExponentialMultiplication, _root_.sum_apply, smul_apply,
    combDistributionModulation_isolation_apply S T hT, smul_eq_mul,
    finitePositiveExponentialSymbol, Finset.sum_mul, mul_assoc]

/-- An actual shifted character has its literal phase product. -/
theorem combModulationCharacter_sub (a x r : ℝ) :
    combModulationCharacter a (-r) * combModulationCharacter a x =
      combModulationCharacter a (x - r) := by
  simp only [combModulationCharacter_eq_exp]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Exact finite coefficients of f(x-r), keeping the original frequencies. -/
def finiteTranslatedSymbolCoefficients {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (c : ι → ℂ) (r : ℝ) (i : ι) : ℂ :=
  c i * combModulationCharacter (a i) (-r)

theorem finitePositiveExponentialSymbol_translated {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (c : ι → ℂ) (r x : ℝ) :
    finitePositiveExponentialSymbol a (finiteTranslatedSymbolCoefficients a c r) x =
      finitePositiveExponentialSymbol a c (x - r) := by
  unfold finitePositiveExponentialSymbol finiteTranslatedSymbolCoefficients
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc, combModulationCharacter_sub]

/-- The actual finite translated root-clearing product, retaining repeated factors. -/
def finiteTranslatedSymbolProduct {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (c : ι → ℂ) (r : List ℝ) (T : TemperedDistribution ℝ ℂ) :
    TemperedDistribution ℝ ℂ :=
  r.foldr (fun s D => finiteExponentialMultiplication a
    (finiteTranslatedSymbolCoefficients a c s) D) T

/-- The exact pointwise root-clearing product, in the same finite order as the actual operator. -/
def finiteTranslatedSymbolProductValue {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (c : ι → ℂ) (r : List ℝ) (x : ℝ) : ℂ :=
  (r.map (fun s => finitePositiveExponentialSymbol a c (x - s))).prod

/-- The whole actual Fourier carrier, with every finite translation and collision retained. -/
def finiteTranslatedSymbolProductFourierCarrier {ι : Type*} [Fintype ι]
    (S : LocallyFiniteCarrier) (a : ι → ℝ) (r : List ℝ) : LocallyFiniteCarrier :=
  r.foldr (fun _ U => finiteCombConvolutionCarrier U a) S

/-- Same-exponent original strong admission holds at every finite multiplication step. -/
theorem stronglyTemperedAtomicAtExponent_finiteTranslatedSymbolProduct {ι : Type*} [Fintype ι]
    (S : LocallyFiniteCarrier) (N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent S N) (a : ι → ℝ) (c : ι → ℂ) (r : List ℝ) :
    finiteTranslatedSymbolProduct a c r T ∈ stronglyTemperedAtomicAtExponent S N := by
  induction r with
  | nil => exact hT
  | cons s r ih =>
    exact stronglyTemperedAtomicAtExponent_finiteExponentialMultiplication S N _ ih a
      (finiteTranslatedSymbolCoefficients a c s)

/-- ALL actual original isolation actions are multiplied by the full literal clearing product. -/
theorem finiteTranslatedSymbolProduct_isolation_apply {ι : Type*} [Fintype ι]
    (S : LocallyFiniteCarrier) (N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent S N) (a : ι → ℝ) (c : ι → ℂ)
    (r : List ℝ) (x : S.subtype) :
    finiteTranslatedSymbolProduct a c r T (S.isolationSchwartz x) =
      finiteTranslatedSymbolProductValue a c r x * T (S.isolationSchwartz x) := by
  induction r with
  | nil => simp [finiteTranslatedSymbolProduct, finiteTranslatedSymbolProductValue]
  | cons s r ih =>
    change finiteExponentialMultiplication a (finiteTranslatedSymbolCoefficients a c s)
      (finiteTranslatedSymbolProduct a c r T) (S.isolationSchwartz x) = _
    rw [finiteExponentialMultiplication_isolation_apply S _
      (stronglyTemperedAtomicAtExponent_finiteTranslatedSymbolProduct S N T hT a c r).1,
      finitePositiveExponentialSymbol_translated, ih]
    simp only [finiteTranslatedSymbolProductValue, List.map_cons, List.prod_cons, mul_assoc]

/-- BOTH genuine original records survive the entire finite product at their SAME exponents. -/
theorem stronglyTemperedOriginalPair_finiteTranslatedSymbolProduct {ι : Type*} [Fintype ι]
    (S U : LocallyFiniteCarrier) (M N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent S M)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent U N)
    (a : ι → ℝ) (c : ι → ℂ) (r : List ℝ) :
    finiteTranslatedSymbolProduct a c r T ∈ stronglyTemperedAtomicAtExponent S M ∧
    𝓕 (finiteTranslatedSymbolProduct a c r T) ∈ stronglyTemperedAtomicAtExponent
      (finiteTranslatedSymbolProductFourierCarrier U a r) N := by
  induction r with
  | nil => exact ⟨hT, hF⟩
  | cons s r ih =>
    exact stronglyTemperedOriginalPair_finiteExponentialMultiplication S
      (finiteTranslatedSymbolProductFourierCarrier U a r) M N _ ih.1 ih.2 a
      (finiteTranslatedSymbolCoefficients a c s)

/-- Zero ORIGINAL rows outside any actual carrier transport the SAME-exponent weighted record.
The smaller support is proved before reindexing; no raw Fourier restriction is assumed. -/
theorem stronglyTemperedAtomicAtExponent_of_originalRows_zero (S U : LocallyFiniteCarrier)
    (N : ℕ) (T : TemperedDistribution ℝ ℂ) (hT : T ∈ stronglyTemperedAtomicAtExponent S N)
    (hz : ∀ x : S.subtype, (x : ℝ) ∉ U.carrier → T (S.isolationSchwartz x) = 0) :
    T ∈ stronglyTemperedAtomicAtExponent U N := by
  let R := S.restrict (S.carrier ∩ U.carrier) Set.inter_subset_left
  have hR : AtomicOnCarrier R T := by
    apply (atomicOnCarrier_restrict_iff S _ Set.inter_subset_left T).mpr
    refine ⟨hasLocallyAtomicAction_atomicOnCarrier S T hT.1, ?_⟩
    intro x hx
    apply hz x
    intro hu
    exact hx ⟨x.property, hu⟩
  exact stronglyTemperedAtomicAtExponent_mono_carrier Set.inter_subset_right N T
    (stronglyTemperedAtomicAtExponent_restrict S _ Set.inter_subset_left N T hR hT)

/-- Genuine zero symbol values remove ORIGINAL rows and preserve their actual weighted mass. -/
theorem stronglyTemperedAtomicAtExponent_finiteTranslatedSymbolProduct_cleared {ι : Type*}
    [Fintype ι] (S U : LocallyFiniteCarrier) (N : ℕ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent S N)
    (a : ι → ℝ) (c : ι → ℂ) (r : List ℝ)
    (hz : ∀ x ∈ S.carrier, x ∉ U.carrier → finiteTranslatedSymbolProductValue a c r x = 0) :
    finiteTranslatedSymbolProduct a c r T ∈ stronglyTemperedAtomicAtExponent U N := by
  apply stronglyTemperedAtomicAtExponent_of_originalRows_zero S U N _
    (stronglyTemperedAtomicAtExponent_finiteTranslatedSymbolProduct S N T hT a c r)
  intro x hx
  rw [finiteTranslatedSymbolProduct_isolation_apply S N T hT, hz x x.property hx, zero_mul]

/-- A retained translated factor genuinely vanishes at every translated original root. -/
theorem finiteTranslatedSymbolProductValue_zero_of_mem {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (c : ι → ℂ) (r : List ℝ) (x s : ℝ) (hs : s ∈ r)
    (hz : finitePositiveExponentialSymbol a c (x - s) = 0) :
    finiteTranslatedSymbolProductValue a c r x = 0 := by
  induction r with
  | nil => simp at hs
  | cons t r ih =>
    simp only [List.mem_cons] at hs
    simp only [finiteTranslatedSymbolProductValue, List.map_cons, List.prod_cons]
    rcases hs with he | hs
    · subst t
      rw [hz, zero_mul]
    · rw [show (r.map (fun s => finitePositiveExponentialSymbol a c (x - s))).prod = 0 from
        ih hs, mul_zero]

/-- The concrete clearing shifts include EVERY input frequency, including repeated values. -/
def finiteRootClearingShifts {ι : Type*} [Fintype ι] (a : ι → ℝ) : List ℝ := by
  classical
  exact Finset.univ.toList.map a

theorem finiteRootClearingShifts_mem {ι : Type*} [Fintype ι] (a : ι → ℝ) (i : ι) :
    a i ∈ finiteRootClearingShifts a := by
  classical
  exact List.mem_map.mpr ⟨i, Finset.mem_toList.mpr (Finset.mem_univ i), rfl⟩

/-- ALL translated root rows are killed by the internally supplied finite clearing product. -/
theorem finiteRootClearingProduct_zero_outside_cone {ι : Type*} [Fintype ι]
    (S K : LocallyFiniteCarrier) (A : Set ℝ) (a : ι → ℝ) (c : ι → ℂ)
    (hS : S.carrier ⊆ A ∪ K.carrier)
    (hroot : ∀ x ∈ A, finitePositiveExponentialSymbol a c x = 0)
    (x : ℝ) (hx : x ∈ (finiteCombConvolutionCarrier S a).carrier)
    (hnot : x ∉ (finiteCombConvolutionCarrier K a).carrier) :
    finiteTranslatedSymbolProductValue a c (finiteRootClearingShifts a) x = 0 := by
  obtain ⟨i, y, hy, he⟩ := Set.mem_iUnion.mp hx
  have hyA : y ∈ A := by
    rcases hS hy with hA | hK
    · exact hA
    · exact False.elim (hnot (Set.mem_iUnion.mpr ⟨i, y, hK, he⟩))
  apply finiteTranslatedSymbolProductValue_zero_of_mem a c _ x (a i)
    (finiteRootClearingShifts_mem a i)
  rw [← he, add_sub_cancel_left]
  exact hroot y hyA

end
end MeyerGeneralProblem

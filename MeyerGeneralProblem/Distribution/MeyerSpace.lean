module

public import MeyerGeneralProblem.Distribution.CompactSchwartzDensity

@[expose] public section

/-!
# Distributional and strongly tempered Meyer spaces

The distributional space is defined by its intrinsic local meaning: both a
tempered distribution and its distributional Fourier transform have locally
finite atomic formulas on the prescribed carrier.  The strongly tempered
space is kept separate by imposing weighted total-variation summability on
the canonical carrier coefficients.
-/

open scoped FourierTransform SchwartzMap

namespace MeyerGeneralProblem

noncomputable section

/-- The distributional Fourier transform as a complex-linear map. -/
def temperedFourierLinearMap :
    TemperedDistribution ℝ ℂ →ₗ[ℂ] TemperedDistribution ℝ ℂ where
  toFun := FourierTransform.fourier
  map_add' := FourierTransform.fourier_add
  map_smul' := FourierTransform.fourier_smul

@[simp]
theorem temperedFourierLinearMap_apply (T : TemperedDistribution ℝ ℂ) :
    temperedFourierLinearMap T = FourierTransform.fourier T :=
  rfl

/-- Tempered distributions which are locally atomic on `S`, and whose
distributional Fourier transforms are locally atomic on `S`. -/
def DistributionalMeyerSpace (S : LocallyFiniteCarrier) :
    Submodule ℂ (TemperedDistribution ℝ ℂ) where
  carrier := {T |
    HasLocallyAtomicAction S T ∧
      HasLocallyAtomicAction S (FourierTransform.fourier T)}
  zero_mem' := by
    constructor
    · exact atomicOnCarrier_hasLocallyAtomicAction S 0 (by
        intro f hf
        simp)
    · exact atomicOnCarrier_hasLocallyAtomicAction S 0 (by
        intro f hf
        simp)
  add_mem' := by
    intro T U hT hU
    constructor
    · rw [← atomicOnCarrier_iff_hasLocallyAtomicAction]
      intro f hf
      change T f + U f = 0
      rw [(hasLocallyAtomicAction_atomicOnCarrier S T hT.1) f hf,
        (hasLocallyAtomicAction_atomicOnCarrier S U hU.1) f hf,
        add_zero]
    · rw [← atomicOnCarrier_iff_hasLocallyAtomicAction]
      simpa only [FourierTransform.fourier_add] using
        (show AtomicOnCarrier S
            (FourierTransform.fourier T + FourierTransform.fourier U) by
          intro f hf
          change FourierTransform.fourier T f +
            FourierTransform.fourier U f = 0
          rw [(hasLocallyAtomicAction_atomicOnCarrier S
              (FourierTransform.fourier T) hT.2) f hf,
            (hasLocallyAtomicAction_atomicOnCarrier S
              (FourierTransform.fourier U) hU.2) f hf,
            add_zero])
  smul_mem' := by
    intro c T hT
    constructor
    · rw [← atomicOnCarrier_iff_hasLocallyAtomicAction]
      intro f hf
      change c * T f = 0
      rw [(hasLocallyAtomicAction_atomicOnCarrier S T hT.1) f hf,
        mul_zero]
    · rw [← atomicOnCarrier_iff_hasLocallyAtomicAction]
      simpa only [FourierTransform.fourier_smul] using
        (show AtomicOnCarrier S
            (c • FourierTransform.fourier T) by
          intro f hf
          change c * FourierTransform.fourier T f = 0
          rw [(hasLocallyAtomicAction_atomicOnCarrier S
              (FourierTransform.fourier T) hT.2) f hf,
            mul_zero])

@[simp]
theorem mem_distributionalMeyerSpace_iff
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ) :
    T ∈ DistributionalMeyerSpace S ↔
      HasLocallyAtomicAction S T ∧
        HasLocallyAtomicAction S (FourierTransform.fourier T) :=
  Iff.rfl

/-- The weighted total variation of the canonical carrier coefficients at
exponent `N`.  For a locally atomic distribution these coefficients are
uniquely recovered by the isolating Schwartz tests. -/
def stronglyTemperedCoefficientTerm
    (S : LocallyFiniteCarrier) (N : ℕ)
    (T : TemperedDistribution ℝ ℂ) (x : S.subtype) : ℝ :=
  ‖T (S.isolationSchwartz x)‖ / (1 + |(x : ℝ)|) ^ N

/-- Locally atomic tempered distributions whose canonical carrier
coefficients have finite weighted total variation at the fixed exponent
`N`. -/
def stronglyTemperedAtomicAtExponent
    (S : LocallyFiniteCarrier) (N : ℕ) :
    Submodule ℂ (TemperedDistribution ℝ ℂ) where
  carrier := {T |
    HasLocallyAtomicAction S T ∧
      Summable (stronglyTemperedCoefficientTerm S N T)}
  zero_mem' := by
    constructor
    · exact atomicOnCarrier_hasLocallyAtomicAction S 0 (by
        intro f hf
        simp)
    · convert (summable_zero : Summable (fun _ : S.subtype => (0 : ℝ))) using 1
      funext x
      change ‖(0 : ℂ)‖ / (1 + |(x : ℝ)|) ^ N = 0
      simp
  add_mem' := by
    intro T U hT hU
    constructor
    · rw [← atomicOnCarrier_iff_hasLocallyAtomicAction]
      intro f hf
      change T f + U f = 0
      rw [(hasLocallyAtomicAction_atomicOnCarrier S T hT.1) f hf,
        (hasLocallyAtomicAction_atomicOnCarrier S U hU.1) f hf,
        add_zero]
    · apply Summable.of_nonneg_of_le
        (fun x => by
          exact div_nonneg (norm_nonneg _)
            (pow_nonneg (by positivity) N))
        (fun x => ?_) (hT.2.add hU.2)
      change ‖T (S.isolationSchwartz x) +
          U (S.isolationSchwartz x)‖ /
          (1 + |(x : ℝ)|) ^ N ≤
        ‖T (S.isolationSchwartz x)‖ /
            (1 + |(x : ℝ)|) ^ N +
          ‖U (S.isolationSchwartz x)‖ /
            (1 + |(x : ℝ)|) ^ N
      rw [← add_div]
      exact div_le_div_of_nonneg_right (norm_add_le _ _)
        (pow_nonneg (by positivity) N)
  smul_mem' := by
    intro c T hT
    constructor
    · rw [← atomicOnCarrier_iff_hasLocallyAtomicAction]
      intro f hf
      change c * T f = 0
      rw [(hasLocallyAtomicAction_atomicOnCarrier S T hT.1) f hf,
        mul_zero]
    · have hs := Summable.mul_left ‖c‖ hT.2
      change Summable (fun x : S.subtype =>
        ‖c * T (S.isolationSchwartz x)‖ /
          (1 + |(x : ℝ)|) ^ N)
      have heq : (fun x : S.subtype =>
          ‖c * T (S.isolationSchwartz x)‖ /
            (1 + |(x : ℝ)|) ^ N) =
          (fun x : S.subtype => ‖c‖ *
            (‖T (S.isolationSchwartz x)‖ /
              (1 + |(x : ℝ)|) ^ N)) := by
        funext x
        rw [norm_mul]
        ring
      rw [heq]
      exact hs

theorem stronglyTemperedAtomicAtExponent_mono
    (S : LocallyFiniteCarrier) {N M : ℕ} (hNM : N ≤ M) :
    stronglyTemperedAtomicAtExponent S N ≤
      stronglyTemperedAtomicAtExponent S M := by
  intro T hT
  refine ⟨hT.1, Summable.of_nonneg_of_le
    (fun x => div_nonneg (norm_nonneg _)
      (pow_nonneg (by positivity) M)) (fun x => ?_) hT.2⟩
  exact div_le_div_of_nonneg_left (norm_nonneg _)
    (pow_pos (by positivity) N)
    (pow_le_pow_right₀
      (le_add_of_nonneg_right (abs_nonneg (x : ℝ))) hNM)

/-- Locally atomic distributions with finite weighted total variation for
some polynomial exponent. -/
def StronglyTemperedAtomicOnCarrier (S : LocallyFiniteCarrier) :
    Submodule ℂ (TemperedDistribution ℝ ℂ) :=
  ⨆ N : ℕ, stronglyTemperedAtomicAtExponent S N

theorem mem_stronglyTemperedAtomicOnCarrier_iff
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ) :
    T ∈ StronglyTemperedAtomicOnCarrier S ↔
      ∃ N : ℕ, HasLocallyAtomicAction S T ∧
        Summable (stronglyTemperedCoefficientTerm S N T) := by
  rw [StronglyTemperedAtomicOnCarrier,
    Submodule.mem_iSup_of_directed]
  · rfl
  · intro N M
    exact ⟨max N M,
      stronglyTemperedAtomicAtExponent_mono S (le_max_left N M),
      stronglyTemperedAtomicAtExponent_mono S (le_max_right N M)⟩

/-- The strongly tempered Meyer space: both carrier coefficient families
have finite weighted total variation for some exponent. -/
def StronglyTemperedMeyerSpace (S : LocallyFiniteCarrier) :
    Submodule ℂ (TemperedDistribution ℝ ℂ) :=
  StronglyTemperedAtomicOnCarrier S ⊓
    (StronglyTemperedAtomicOnCarrier S).comap temperedFourierLinearMap

@[simp]
theorem mem_stronglyTemperedMeyerSpace_iff
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ) :
    T ∈ StronglyTemperedMeyerSpace S ↔
      T ∈ StronglyTemperedAtomicOnCarrier S ∧
        FourierTransform.fourier T ∈ StronglyTemperedAtomicOnCarrier S :=
  Iff.rfl

/-- The strong total-variation condition is additional structure; forgetting
it gives the distributional Meyer space. -/
theorem stronglyTemperedMeyerSpace_le_distributionalMeyerSpace
    (S : LocallyFiniteCarrier) :
    StronglyTemperedMeyerSpace S ≤ DistributionalMeyerSpace S := by
  intro T hT
  rw [mem_distributionalMeyerSpace_iff]
  constructor
  · obtain ⟨N, hN⟩ :=
      (mem_stronglyTemperedAtomicOnCarrier_iff S T).mp hT.1
    exact hN.1
  · obtain ⟨N, hN⟩ :=
      (mem_stronglyTemperedAtomicOnCarrier_iff S
        (FourierTransform.fourier T)).mp hT.2
    exact hN.1

end

end MeyerGeneralProblem

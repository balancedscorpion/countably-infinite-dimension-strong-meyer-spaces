module

public import MeyerGeneralProblem.Distribution.CombScaling
public import MeyerGeneralProblem.Distribution.MeyerSpace
public import MeyerGeneralProblem.Carrier.Dilation

@[expose] public section

/-!
# Dilation of the complete original strong atomic spaces

The actual distributional pushforward transports every isolation coefficient
without changing its mass. Positive dilation preserves weighted absolute
summability at the SAME exponent, in both directions. The reciprocal Fourier
scale and its nonzero Jacobian remain literal.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped SchwartzMap FourierTransform

/-- The actual bijection of ALL carrier points under positive dilation. -/
def LocallyFiniteCarrier.dilationPoint (S : LocallyFiniteCarrier) (c : ℝ) (hc : 0 < c)
    (x : S.subtype) : (S.dilate c hc).subtype :=
  ⟨c * (x : ℝ), ⟨(x : ℝ), x.property, rfl⟩⟩

theorem LocallyFiniteCarrier.dilationPoint_bijective
    (S : LocallyFiniteCarrier) (c : ℝ) (hc : 0 < c) :
    Function.Bijective (S.dilationPoint c hc) := by
  constructor
  · intro x y h
    apply Subtype.ext
    exact mul_left_cancel₀ hc.ne' (congrArg Subtype.val h)
  · rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

/-- Reindexing uses the whole geometric carrier, including zero coefficients. -/
def LocallyFiniteCarrier.dilationEquiv (S : LocallyFiniteCarrier) (c : ℝ) (hc : 0 < c) :
    S.subtype ≃ (S.dilate c hc).subtype :=
  Equiv.ofBijective (S.dilationPoint c hc) (S.dilationPoint_bijective c hc)

theorem LocallyFiniteCarrier.dilationEquiv_val
    (S : LocallyFiniteCarrier) (c : ℝ) (hc : 0 < c) (x : S.subtype) :
    (S.dilationEquiv c hc x : ℝ) = c * (x : ℝ) := rfl

/-- Reciprocal geometric dilation returns the complete original carrier. -/
theorem LocallyFiniteCarrier.dilate_inv_eq_self
    (S : LocallyFiniteCarrier) (c : ℝ) (hc : 0 < c) :
    (S.dilate c hc).dilate c⁻¹ (inv_pos.mpr hc) = S := by
  apply LocallyFiniteCarrier.ext
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    simpa only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] using hx
  · intro hy
    refine ⟨c * y, ⟨y, hy, rfl⟩, ?_⟩
    change c⁻¹ * (c * y) = y
    rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]

/-- Reciprocal pushforward dilation returns the ORIGINAL distribution. -/
theorem combDistributionDilation_inv_apply (c : ℝ) (hc : c ≠ 0)
    (T : TemperedDistribution ℝ ℂ) :
    combDistributionDilation c⁻¹ (inv_ne_zero hc) (combDistributionDilation c hc T) = T := by
  ext f
  rw [combDistributionDilation_apply, combDistributionDilation_apply]
  congr 1
  ext x
  rw [combSchwartzDilation_apply, combSchwartzDilation_apply]
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-- The full original Schwartz vanishing ideal transports under dilation. -/
theorem atomicOnCarrier_combDistributionDilation
    (S : LocallyFiniteCarrier) (c : ℝ) (hc : 0 < c)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier S T) :
    AtomicOnCarrier (S.dilate c hc) (combDistributionDilation c hc.ne' T) := by
  intro f hf
  rw [combDistributionDilation_apply]
  apply hT
  intro x hx
  rw [combSchwartzDilation_apply]
  exact hf _ ⟨x, hx, rfl⟩

theorem hasLocallyAtomicAction_combDistributionDilation
    (S : LocallyFiniteCarrier) (c : ℝ) (hc : 0 < c)
    (T : TemperedDistribution ℝ ℂ) (hT : HasLocallyAtomicAction S T) :
    HasLocallyAtomicAction (S.dilate c hc) (combDistributionDilation c hc.ne' T) :=
  atomicOnCarrier_hasLocallyAtomicAction _ _ (atomicOnCarrier_combDistributionDilation S c hc T
    (hasLocallyAtomicAction_atomicOnCarrier S T hT))

/-- EVERY original isolation coefficient is unchanged, independently of the
chosen geometric isolation bump in the dilated carrier. -/
theorem combDistributionDilation_isolation_apply
    (S : LocallyFiniteCarrier) (c : ℝ) (hc : 0 < c)
    (T : TemperedDistribution ℝ ℂ) (hT : HasLocallyAtomicAction S T) (x : S.subtype) :
    combDistributionDilation c hc.ne' T
      ((S.dilate c hc).isolationSchwartz (S.dilationEquiv c hc x)) =
        T (S.isolationSchwartz x) := by
  have hz : SchwartzVanishesOn S
      (combSchwartzDilation c hc.ne'
        ((S.dilate c hc).isolationSchwartz (S.dilationEquiv c hc x)) - S.isolationSchwartz x) := by
    intro y hy
    let yS : S.subtype := ⟨y, hy⟩
    rw [sub_apply, combSchwartzDilation_apply]
    apply sub_eq_zero.mpr
    change (S.dilate c hc).isolationSchwartz (S.dilationEquiv c hc x)
      (S.dilationEquiv c hc yS) = S.isolationSchwartz x yS
    simp only [LocallyFiniteCarrier.isolationSchwartz_apply_subtype,
      (S.dilationEquiv c hc).injective.eq_iff]
  have hzero := (hasLocallyAtomicAction_atomicOnCarrier S T hT) _ hz
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero

/-- A positive dilation changes polynomial weights by a finite constant. -/
theorem originalDilationWeight_le (c : ℝ) (hc : 0 < c) (x : ℝ) :
    1 + |x| ≤ (1 + c⁻¹) * (1 + |c * x|) := by
  calc
    1 + |x| ≤ (1 + c⁻¹) + (c + 1) * |x| := by
      nlinarith [inv_pos.mpr hc, mul_nonneg hc.le (abs_nonneg x)]
    _ = (1 + c⁻¹) * (1 + |c * x|) := by
      rw [abs_mul, abs_of_pos hc]
      field_simp

/-- Pointwise bound for the actual original coefficient terms at fixed `N`. -/
theorem stronglyTemperedCoefficientTerm_dilation_le
    (S : LocallyFiniteCarrier) (c : ℝ) (hc : 0 < c) (N : ℕ)
    (T : TemperedDistribution ℝ ℂ) (hT : HasLocallyAtomicAction S T) (x : S.subtype) :
    stronglyTemperedCoefficientTerm (S.dilate c hc) N (combDistributionDilation c hc.ne' T)
      (S.dilationEquiv c hc x) ≤
        (1 + c⁻¹) ^ N * stronglyTemperedCoefficientTerm S N T x := by
  unfold stronglyTemperedCoefficientTerm
  rw [combDistributionDilation_isolation_apply S c hc T hT x, S.dilationEquiv_val]
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |(x : ℝ)|)
    (originalDilationWeight_le c hc (x : ℝ)) N
  rw [mul_pow] at hpow
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hmul := mul_le_mul_of_nonneg_left hpow (norm_nonneg (T (S.isolationSchwartz x)))
  nlinarith

/-- Dilation preserves original weighted absolute-TV admission at the SAME
exponent, for arbitrary original atomic distributions. -/
theorem stronglyTemperedAtomicAtExponent_combDistributionDilation
    (S : LocallyFiniteCarrier) (c : ℝ) (hc : 0 < c) (N : ℕ)
    (T : TemperedDistribution ℝ ℂ) (hT : T ∈ stronglyTemperedAtomicAtExponent S N) :
    combDistributionDilation c hc.ne' T ∈ stronglyTemperedAtomicAtExponent (S.dilate c hc) N := by
  refine ⟨hasLocallyAtomicAction_combDistributionDilation S c hc T hT.1, ?_⟩
  rw [← (S.dilationEquiv c hc).summable_iff]
  apply Summable.of_nonneg_of_le
    (fun x => div_nonneg (norm_nonneg _) (pow_nonneg (by positivity) N))
    (stronglyTemperedCoefficientTerm_dilation_le S c hc N T hT.1)
    (hT.2.mul_left ((1 + c⁻¹) ^ N))

/-- Exact membership equivalence for the COMPLETE fixed-exponent spaces. -/
theorem stronglyTemperedAtomicAtExponent_dilation_iff
    (S : LocallyFiniteCarrier) (c : ℝ) (hc : 0 < c) (N : ℕ)
    (T : TemperedDistribution ℝ ℂ) :
    combDistributionDilation c hc.ne' T ∈ stronglyTemperedAtomicAtExponent (S.dilate c hc) N ↔
      T ∈ stronglyTemperedAtomicAtExponent S N := by
  constructor
  · intro h
    have hi := stronglyTemperedAtomicAtExponent_combDistributionDilation (S.dilate c hc)
      c⁻¹ (inv_pos.mpr hc) N _ h
    simpa only [S.dilate_inv_eq_self c hc, combDistributionDilation_inv_apply] using hi
  · exact stronglyTemperedAtomicAtExponent_combDistributionDilation S c hc N T

theorem stronglyTemperedAtomicOnCarrier_dilation_iff
    (S : LocallyFiniteCarrier) (c : ℝ) (hc : 0 < c)
    (T : TemperedDistribution ℝ ℂ) :
    combDistributionDilation c hc.ne' T ∈ StronglyTemperedAtomicOnCarrier (S.dilate c hc) ↔
      T ∈ StronglyTemperedAtomicOnCarrier S := by
  simp only [mem_stronglyTemperedAtomicOnCarrier_iff]
  change (∃ N, combDistributionDilation c hc.ne' T ∈
    stronglyTemperedAtomicAtExponent (S.dilate c hc) N) ↔
    ∃ N, T ∈ stronglyTemperedAtomicAtExponent S N
  exact exists_congr (fun N => stronglyTemperedAtomicAtExponent_dilation_iff S c hc N T)

/-- The genuine dilation is a linear equivalence on the entire original
tempered-distribution space. Its inverse is the actual reciprocal dilation. -/
def combDistributionDilationLinearEquiv (c : ℝ) (hc : 0 < c) :
    TemperedDistribution ℝ ℂ ≃ₗ[ℂ] TemperedDistribution ℝ ℂ where
  toLinearMap := (combDistributionDilation c hc.ne').toLinearMap
  invFun := combDistributionDilation c⁻¹ (inv_ne_zero hc.ne')
  left_inv := combDistributionDilation_inv_apply c hc.ne'
  right_inv := by
    intro T
    change combDistributionDilation c hc.ne'
      (combDistributionDilation c⁻¹ (inv_ne_zero hc.ne') T) = T
    simpa only [inv_inv] using combDistributionDilation_inv_apply c⁻¹ (inv_ne_zero hc.ne') T

/-- Fourier-side ORIGINAL weighted-TV admission is equivalent at the SAME
exponent. The exact inverse Jacobian is nonzero and is removed by scalar
invertibility, not by ignoring its contribution to the original record. -/
theorem stronglyTemperedAtomicAtExponent_fourier_dilation_iff
    (B : LocallyFiniteCarrier) (c : ℝ) (hc : 0 < c) (N : ℕ)
    (T : TemperedDistribution ℝ ℂ) :
    𝓕 (combDistributionDilation c hc.ne' T) ∈
      stronglyTemperedAtomicAtExponent (B.dilate c⁻¹ (inv_pos.mpr hc)) N ↔
        𝓕 T ∈ stronglyTemperedAtomicAtExponent B N := by
  rw [fourier_combDistributionDilation]
  have hj : ((|c|⁻¹ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast inv_ne_zero (abs_ne_zero.mpr hc.ne')
  rw [Submodule.smul_mem_iff _ hj]
  exact stronglyTemperedAtomicAtExponent_dilation_iff B c⁻¹ (inv_pos.mpr hc) N (𝓕 T)

theorem stronglyTemperedAtomicOnCarrier_fourier_dilation_iff
    (B : LocallyFiniteCarrier) (c : ℝ) (hc : 0 < c)
    (T : TemperedDistribution ℝ ℂ) :
    𝓕 (combDistributionDilation c hc.ne' T) ∈
      StronglyTemperedAtomicOnCarrier (B.dilate c⁻¹ (inv_pos.mpr hc)) ↔
        𝓕 T ∈ StronglyTemperedAtomicOnCarrier B := by
  rw [fourier_combDistributionDilation]
  have hj : ((|c|⁻¹ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast inv_ne_zero (abs_ne_zero.mpr hc.ne')
  rw [Submodule.smul_mem_iff _ hj]
  exact stronglyTemperedAtomicOnCarrier_dilation_iff B c⁻¹ (inv_pos.mpr hc) (𝓕 T)

/-- Dilation transports the COMPLETE two-carrier original strong space. Every
distribution in either space is included; no constructed-source premise occurs. -/
def originalStrongPairDilationEquiv
    (A B : LocallyFiniteCarrier) (c : ℝ) (hc : 0 < c) :
    ↥(StronglyTemperedAtomicOnCarrier A ⊓
      (StronglyTemperedAtomicOnCarrier B).comap temperedFourierLinearMap) ≃ₗ[ℂ]
    ↥(StronglyTemperedAtomicOnCarrier (A.dilate c hc) ⊓
      (StronglyTemperedAtomicOnCarrier (B.dilate c⁻¹ (inv_pos.mpr hc))).comap
        temperedFourierLinearMap) := by
  let Q := StronglyTemperedAtomicOnCarrier (A.dilate c hc) ⊓
    (StronglyTemperedAtomicOnCarrier (B.dilate c⁻¹ (inv_pos.mpr hc))).comap temperedFourierLinearMap
  have he : Q.comap (combDistributionDilationLinearEquiv c hc).toLinearMap =
      StronglyTemperedAtomicOnCarrier A ⊓
        (StronglyTemperedAtomicOnCarrier B).comap temperedFourierLinearMap := by
    ext T
    change (combDistributionDilation c hc.ne' T ∈ StronglyTemperedAtomicOnCarrier (A.dilate c hc) ∧
      𝓕 (combDistributionDilation c hc.ne' T) ∈
        StronglyTemperedAtomicOnCarrier (B.dilate c⁻¹ (inv_pos.mpr hc))) ↔
      T ∈ StronglyTemperedAtomicOnCarrier A ∧ 𝓕 T ∈ StronglyTemperedAtomicOnCarrier B
    rw [stronglyTemperedAtomicOnCarrier_dilation_iff A c hc T,
      stronglyTemperedAtomicOnCarrier_fourier_dilation_iff B c hc T]
  exact (LinearEquiv.ofEq _ _ he).symm.trans
    ((combDistributionDilationLinearEquiv c hc).ofSubmodule' Q)

/-- The complete original two-record fixed-exponent layers also transport
by an exact linear equivalence, so low-layer vanishing is retained. -/
def originalExponentPairDilationEquiv
    (A B : LocallyFiniteCarrier) (c : ℝ) (hc : 0 < c) (N : ℕ) :
    ↥(stronglyTemperedAtomicAtExponent A N ⊓
      (stronglyTemperedAtomicAtExponent B N).comap temperedFourierLinearMap) ≃ₗ[ℂ]
    ↥(stronglyTemperedAtomicAtExponent (A.dilate c hc) N ⊓
      (stronglyTemperedAtomicAtExponent (B.dilate c⁻¹ (inv_pos.mpr hc)) N).comap
        temperedFourierLinearMap) := by
  let Q := stronglyTemperedAtomicAtExponent (A.dilate c hc) N ⊓
    (stronglyTemperedAtomicAtExponent (B.dilate c⁻¹ (inv_pos.mpr hc)) N).comap temperedFourierLinearMap
  have he : Q.comap (combDistributionDilationLinearEquiv c hc).toLinearMap =
      stronglyTemperedAtomicAtExponent A N ⊓
        (stronglyTemperedAtomicAtExponent B N).comap temperedFourierLinearMap := by
    ext T
    change (combDistributionDilation c hc.ne' T ∈ stronglyTemperedAtomicAtExponent (A.dilate c hc) N ∧
      𝓕 (combDistributionDilation c hc.ne' T) ∈
        stronglyTemperedAtomicAtExponent (B.dilate c⁻¹ (inv_pos.mpr hc)) N) ↔
      T ∈ stronglyTemperedAtomicAtExponent A N ∧ 𝓕 T ∈ stronglyTemperedAtomicAtExponent B N
    rw [stronglyTemperedAtomicAtExponent_dilation_iff A c hc N T,
      stronglyTemperedAtomicAtExponent_fourier_dilation_iff B c hc N T]
  exact (LinearEquiv.ofEq _ _ he).symm.trans
    ((combDistributionDilationLinearEquiv c hc).ofSubmodule' Q)

end

end MeyerGeneralProblem

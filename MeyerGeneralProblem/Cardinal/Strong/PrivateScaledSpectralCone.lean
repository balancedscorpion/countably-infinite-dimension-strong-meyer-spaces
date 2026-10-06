module

public import MeyerGeneralProblem.Cardinal.Strong.PrivateConeDivisibility
public import MeyerGeneralProblem.Cardinal.Strong.RationalQuarticDilation
public import MeyerGeneralProblem.Carrier.Dilation

@[expose] public section

/-! The actual shared coarse cone and positively dilated private cone. The
private natural scale is construction data; all label/coarse membership and
head-radius identities are proved for the actual geometric carriers. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- The fixed actual shared coarse cone K0=C_beta/c, including its zero. -/
def originalSharedCoarseCone : LocallyFiniteCarrier :=
  spectralConeCarrier.dilate parityDilationUnit⁻¹ (inv_pos.mpr parityDilationUnit_pos)

/-- The actual private cone Ki=C_beta/(c*m) for every positive natural scale. -/
def originalPrivateSpectralCone (m : ℕ) (hm : 0 < m) : LocallyFiniteCarrier :=
  spectralConeCarrier.dilate (parityDilationUnit * (m : ℝ))⁻¹
    (inv_pos.mpr (mul_pos parityDilationUnit_pos (by exact_mod_cast hm)))

/-- The actual physical value of a signed label on the private cone. -/
def originalPrivateSpectralLabelValue (m : ℕ) (label : spectralConeIndex) : ℝ :=
  spectralConeIndexFrequency label / (parityDilationUnit * (m : ℝ))

/-- Every signed private label lies in the complete actual private cone. -/
theorem originalPrivateSpectralLabelValue_mem (m : ℕ) (hm : 0 < m)
    (label : spectralConeIndex) :
    originalPrivateSpectralLabelValue m label ∈ (originalPrivateSpectralCone m hm).carrier := by
  refine ⟨spectralConeIndexFrequency label, (spectralConeIndexPoint label).property, ?_⟩
  simp only [originalPrivateSpectralLabelValue, div_eq_mul_inv, mul_comm]

/-- EVERY point of the actual private cone is reached by an original signed label. -/
theorem originalPrivateSpectralCone_label_surjective (m : ℕ) (hm : 0 < m)
    (x : ℝ) (hx : x ∈ (originalPrivateSpectralCone m hm).carrier) :
    ∃ label : spectralConeIndex, originalPrivateSpectralLabelValue m label = x := by
  obtain ⟨y, hy, hyx⟩ := hx
  obtain ⟨label, hlabel⟩ := spectralConeIndexPoint_bijective.2 ⟨y, hy⟩
  have hf : spectralConeIndexFrequency label = y := congrArg Subtype.val hlabel
  refine ⟨label, ?_⟩
  simpa only [originalPrivateSpectralLabelValue, hf, div_eq_mul_inv, mul_comm] using hyx

/-- The fixed coarse cone is contained in EVERY actual positive-private-scale cone. -/
theorem originalSharedCoarseCone_subset_private (m : ℕ) (hm : 0 < m) :
    originalSharedCoarseCone.carrier ⊆ (originalPrivateSpectralCone m hm).carrier := by
  rintro x ⟨y, hy, rfl⟩
  refine ⟨(m : ℝ) * y, originalSpectralConeSet_nat_mul m y hy, ?_⟩
  have hc : parityDilationUnit ≠ 0 := parityDilationUnit_pos.ne'
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp

/-- Shared-coarse membership is exactly native cone membership after dividing only by m. -/
theorem originalPrivateSpectralLabelValue_mem_coarse_iff (m : ℕ) (hm : 0 < m)
    (label : spectralConeIndex) :
    originalPrivateSpectralLabelValue m label ∈ originalSharedCoarseCone.carrier ↔
      spectralConeIndexFrequency label / (m : ℝ) ∈ spectralConeSet := by
  have hc : parityDilationUnit ≠ 0 := parityDilationUnit_pos.ne'
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  constructor
  · rintro ⟨x, hx, hxeq⟩
    have heq : x = spectralConeIndexFrequency label / (m : ℝ) := by
      dsimp [originalPrivateSpectralLabelValue] at hxeq
      field_simp at hxeq ⊢
      nlinarith
    exact heq ▸ hx
  · intro hx
    refine ⟨spectralConeIndexFrequency label / (m : ℝ), hx, ?_⟩
    dsimp [originalPrivateSpectralLabelValue]
    field_simp

/-- Exact geometric coarse membership of BOTH original signs requires BOTH divisibilities. -/
theorem originalPrivateSpectralLabelValue_coarse_divisibility (m : ℕ) (hm : 0 < m)
    (label : spectralConeIndex) :
    originalPrivateSpectralLabelValue m label ∈ originalSharedCoarseCone.carrier ↔
      m ∣ (spectralConeIndexCoordinates label).1 ∧ m ∣ (spectralConeIndexCoordinates label).2 :=
  (originalPrivateSpectralLabelValue_mem_coarse_iff m hm label).trans
    (spectralConeIndexFrequency_div_mem_coarse_iff m hm label)

/-- The actual private spectral radius rescales the complete original native head exactly. -/
theorem originalPrivateSpectralLabelValue_head_iff (s m : ℕ) (hm : 0 < m)
    (label : spectralConeIndex) :
    |originalPrivateSpectralLabelValue m label| ≤
      (((s / 2 : ℕ) : ℝ) / 2) / (parityDilationUnit * (m : ℝ)) ↔
      |spectralConeIndexFrequency label| ≤ ((s / 2 : ℕ) : ℝ) / 2 := by
  have hscale : 0 < parityDilationUnit * (m : ℝ) :=
    mul_pos parityDilationUnit_pos (by exact_mod_cast hm)
  simp only [originalPrivateSpectralLabelValue, abs_div, abs_of_pos hscale]
  exact (div_le_div_iff_of_pos_right hscale)

end

end MeyerGeneralProblem.StrongParity

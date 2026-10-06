module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalClassicalLayerExhaustion

@[expose] public section

/-! Unconditional strong countable-cardinal realization on the actual classically selected parity carrier. No radius, exhaustion, projection or finite-layer certificate is an input. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section
open scoped FourierTransform

/-- The ENTIRE original strong exponent layer of the internally constructed infinite carrier is finite dimensional. -/
theorem originalClassicalStrongCarrier_finiteLayer (N : ℕ) :
    FiniteDimensional ℂ (StrongMeyerExponentLayer (originalScheduledCommonCarrier originalClassicalAdaptiveBound) N) := by
  let S := originalScheduledCommonCarrier originalClassicalAdaptiveBound
  let φ := originalScheduledPrefixAnchorTest (originalCommonWindowBounds originalClassicalAdaptiveBound) (N + 1)
  let e : StrongMeyerExponentLayer S N →ₗ[ℂ] ((Fin (N + 1) → ℂ) × (Fin (N + 1) → ℂ)) :=
    { toFun := fun T => (fun i => (T : TemperedDistribution ℝ ℂ) (φ i),
        fun i => 𝓕 (T : TemperedDistribution ℝ ℂ) (φ i))
      map_add' := by intro T U; ext i <;> rfl
      map_smul' := by
        intro a T
        ext i
        · rfl
        · simp only [Submodule.coe_smul, FourierTransform.fourier_smul, smul_apply,
            RingHom.id_apply, Prod.smul_snd, Pi.smul_apply] }
  apply FiniteDimensional.of_injective e
  intro T U he
  apply Subtype.ext
  have h₁ : ∀ i, (T : TemperedDistribution ℝ ℂ) (φ i) = (U : TemperedDistribution ℝ ℂ) (φ i) :=
    fun i => congrFun (congrArg Prod.fst he) i
  have h₂ : ∀ i, 𝓕 (T : TemperedDistribution ℝ ℂ) (φ i) = 𝓕 (U : TemperedDistribution ℝ ℂ) (φ i) :=
    fun i => congrFun (congrArg Prod.snd he) i
  rw [originalClassicalStrongCarrier_projection N T T.property.1 T.property.2,
    originalClassicalStrongCarrier_projection N U U.property.1 U.property.2]
  dsimp [φ] at h₁ h₂
  simp only [originalScheduledAnchorProjection, TemperedDistribution.fourier_apply, h₁, h₂]

/-- Unconditional exact complex Hamel rank aleph0 for the COMPLETE original strongly tempered space of the actual classically scheduled parity carrier. -/
theorem originalClassicalStrongCarrier_rank :
    Module.rank ℂ (StronglyTemperedMeyerSpace (originalScheduledCommonCarrier originalClassicalAdaptiveBound)) =
      Cardinal.aleph0 := by
  apply le_antisymm
  · exact strongMeyerRank_le_aleph0_of_finiteExponentLayers _ originalClassicalStrongCarrier_finiteLayer
  · exact originalScheduledCommonStrongSpace_aleph0_le_rank originalClassicalAdaptiveBound

/-- The actual classically scheduled parity carrier as a named locally finite carrier. -/
def originalClassicalStrongCountableCarrier : LocallyFiniteCarrier :=
  originalScheduledCommonCarrier originalClassicalAdaptiveBound

/-- The requested strong countably infinite-dimensional case, with no supplied analytic certificate. -/
theorem exists_stronglyTemperedMeyerSpace_rank_aleph0 :
    ∃ S : LocallyFiniteCarrier, Module.rank ℂ (StronglyTemperedMeyerSpace S) = Cardinal.aleph0 :=
  ⟨originalClassicalStrongCountableCarrier, originalClassicalStrongCarrier_rank⟩

end
end MeyerGeneralProblem.StrongParity

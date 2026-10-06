module

public import MeyerGeneralProblem.Distribution.OriginalStrongFourierSquare

@[expose] public section

/-! Whole-distribution physical reflection is involutive; support can therefore
be recovered from a reflected record on a genuinely symmetric carrier. -/
namespace MeyerGeneralProblem
noncomputable section

/-- Actual physical reflection twice is the identity on all Schwartz tests. -/
theorem originalDistributionReflection_involutive (T : TemperedDistribution ℝ ℂ) :
    originalDistributionReflection (originalDistributionReflection T) = T := by
  ext f
  rw [originalDistributionReflection_apply, originalDistributionReflection_apply]
  congr 1
  ext x
  simp only [combSchwartzDilation_apply, neg_one_mul, neg_neg]

/-- Atomicity of the actual reflection implies original atomicity on a symmetric carrier. -/
theorem atomicOnCarrier_of_originalDistributionReflection (S : LocallyFiniteCarrier)
    (hsym : ∀ x ∈ S.carrier, -x ∈ S.carrier) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier S (originalDistributionReflection T)) : AtomicOnCarrier S T := by
  have h := atomicOnCarrier_originalDistributionReflection S (originalDistributionReflection T) hT
  rw [originalDistributionReflection_involutive] at h
  apply h.mono
  rintro x ⟨y, hy, rfl⟩
  exact hsym y hy

end
end MeyerGeneralProblem

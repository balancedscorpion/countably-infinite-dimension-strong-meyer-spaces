module

public import MeyerGeneralProblem.Distribution.FiniteAnnihilator

@[expose] public section

/-! Exact original coefficients under finite spectral shifts, including
collisions and zero extension outside the original spectral carrier. -/

namespace MeyerGeneralProblem

noncomputable section

open scoped SchwartzMap FourierTransform

/-- The canonical original coefficient, extended by zero at every other point. -/
def extendedAtomicCoefficient (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (x : ℝ) : ℂ := by
  classical
  exact if hx : x ∈ S.carrier then T (S.isolationSchwartz ⟨x, hx⟩) else 0

theorem atomic_action_singleton_values (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier S T)
    (f : SchwartzMap ℝ ℂ) (x : ℝ)
    (hf : ∀ y ∈ S.carrier, y ≠ x → f y = 0) :
    T f = extendedAtomicCoefficient S T x * f x := by
  classical
  unfold extendedAtomicCoefficient
  split_ifs with hx
  · have hv : SchwartzVanishesOn S (f - f x • S.isolationSchwartz ⟨x, hx⟩) := by
      intro y hy
      change f y - f x * S.isolationSchwartz ⟨x, hx⟩ y = 0
      by_cases hyx : y = x
      · subst y
        rw [S.isolationSchwartz_self]
        ring
      · rw [hf y hy hyx, S.isolationSchwartz_of_mem_of_ne _ hy hyx]
        ring
    have h := hT _ hv
    simpa only [map_sub, map_smul, smul_eq_mul, sub_eq_zero, mul_comm] using h
  · rw [zero_mul]
    exact hT f (fun y hy => hf y hy (fun h => hx (h ▸ hy)))

/-- An isolation test on the full translated container recovers the ORIGINAL
coefficient at each preimage, with all coincident shifts retained in the sum. -/
theorem finiteCombConvolution_isolation_apply {ι : Type*} [Fintype ι]
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier S T) (a : ι → ℝ) (c : ι → ℂ)
    (x : (finiteCombConvolutionCarrier S a).subtype) :
    finiteCombConvolution a c T ((finiteCombConvolutionCarrier S a).isolationSchwartz x) =
      ∑ i, c i * extendedAtomicCoefficient S T ((x : ℝ) - a i) := by
  classical
  rw [finiteCombConvolution_apply_test]
  apply Finset.sum_congr rfl
  intro i _
  rw [atomic_action_singleton_values S T hT _ ((x : ℝ) - a i)]
  · rw [combSchwartzTranslation_apply,
      show a i + ((x : ℝ) - a i) = x by ring,
      (finiteCombConvolutionCarrier S a).isolationSchwartz_self, mul_one]
  · intro y hy hyx
    rw [combSchwartzTranslation_apply]
    exact (finiteCombConvolutionCarrier S a).isolationSchwartz_of_mem_of_ne x
      (mem_finiteCombConvolutionCarrier S a i hy) (by
        intro h
        apply hyx
        linarith)

/-- At every real point, zero extension and all original shift collisions
give the exact coefficient of the actual finite convolution. -/
theorem extendedAtomicCoefficient_finiteCombConvolution {ι : Type*} [Fintype ι]
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier S T) (a : ι → ℝ) (c : ι → ℂ) (x : ℝ) :
    extendedAtomicCoefficient (finiteCombConvolutionCarrier S a)
        (finiteCombConvolution a c T) x =
      ∑ i, c i * extendedAtomicCoefficient S T (x - a i) := by
  classical
  unfold extendedAtomicCoefficient
  split_ifs with hx
  · exact finiteCombConvolution_isolation_apply S T hT a c ⟨x, hx⟩
  · apply (Finset.sum_eq_zero _).symm
    intro i _
    have hnot : x - a i ∉ S.carrier := by
      intro h
      apply hx
      convert! mem_finiteCombConvolutionCarrier S a i h using 1
      ring
    rw [dite_eq_right hnot, mul_zero]

end

end MeyerGeneralProblem

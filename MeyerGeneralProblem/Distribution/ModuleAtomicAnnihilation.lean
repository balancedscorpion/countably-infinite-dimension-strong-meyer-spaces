module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalPairNumerator

@[expose] public section

/-! An ALL-label module recurrence annihilates a genuine atomic record.
All real points outside the module are checked as well. The whole finite shifted
carrier is retained, including every coefficient collision and allowed zero point. -/
namespace MeyerGeneralProblem
noncomputable section

/-- Exact ALL-label recurrence and zero coefficients off the module imply a genuine
zero finite convolution, rather than merely a formal array identity. -/
theorem finiteCombConvolution_eq_zero_of_module_recurrence {G : Type*} [AddCommGroup G]
    {ι : Type*} [Fintype ι] (S : LocallyFiniteCarrier) (L : G →+ ℝ)
    (p : ι → G) (c : ι → ℂ) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier S T)
    (hoff : ∀ x, x ∉ Set.range L → extendedAtomicCoefficient S T x = 0)
    (hrec : ∀ n, ∑ i, c i * extendedAtomicCoefficient S T (L (n - p i)) = 0) :
    finiteCombConvolution (fun i => L (p i)) c T = 0 := by
  classical
  have hall (x : ℝ) : ∑ i, c i * extendedAtomicCoefficient S T (x - L (p i)) = 0 := by
    by_cases hx : x ∈ Set.range L
    · obtain ⟨n, rfl⟩ := hx
      simpa only [map_sub] using hrec n
    · apply Finset.sum_eq_zero
      intro i _
      have hi : x - L (p i) ∉ Set.range L := by
        rintro ⟨n, hn⟩
        apply hx
        refine ⟨n + p i, ?_⟩
        rw [map_add, hn]
        ring
      rw [hoff _ hi, mul_zero]
  have hlocal := hasLocallyAtomicAction_finiteCombConvolution S T
    (atomicOnCarrier_hasLocallyAtomicAction S T hT) (fun i => L (p i)) c
  apply atomic_eq_of_coefficients (finiteCombConvolutionCarrier S (fun i => L (p i))) _ _
    (hasLocallyAtomicAction_atomicOnCarrier _ _ hlocal) (by intro f hf; simp)
  intro x
  have h := finiteCombConvolution_isolation_apply S T hT (fun i => L (p i)) c x
  rw [hall x] at h
  simpa using h

end
end MeyerGeneralProblem

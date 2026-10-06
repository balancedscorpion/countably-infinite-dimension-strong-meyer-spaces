module

public import MeyerGeneralProblem.Distribution.FiniteConvolutionCoefficients

@[expose] public section

/-! A genuine finite convolution cannot annihilate a nonzero atomic record
on a singleton module coset. The whole finite motif and ALL real coefficient
rows are used, including shifts which land outside the original carrier. -/
namespace MeyerGeneralProblem
noncomputable section

/-- An isolated module coset has zero original coefficient under a genuine
nonzero finite annihilator with distinct actual shifts. -/
theorem extendedAtomicCoefficient_eq_zero_of_singleton_module_coset
    {G : Type*} [AddCommGroup G] {ι : Type*} [Fintype ι]
    (S : LocallyFiniteCarrier) (L : G →+ ℝ) (p : ι → G) (c : ι → ℂ)
    (hinj : Function.Injective (fun i => L (p i))) (i : ι) (hi : c i ≠ 0)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier S T)
    (hzero : finiteCombConvolution (fun j => L (p j)) c T = 0)
    (x : ℝ) (hcoset : ∀ y ∈ S.carrier, x - y ∈ Set.range L → y = x) :
    extendedAtomicCoefficient S T x = 0 := by
  classical
  have h := extendedAtomicCoefficient_finiteCombConvolution S T hT
    (fun j => L (p j)) c (x + L (p i))
  rw [hzero] at h
  have hsum : ∑ j, c j * extendedAtomicCoefficient S T (x + L (p i) - L (p j)) =
      c i * extendedAtomicCoefficient S T x := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      have hy : x + L (p i) - L (p j) ∉ S.carrier := by
        intro hy
        have he := hcoset _ hy (show x - (x + L (p i) - L (p j)) ∈ Set.range L from
          ⟨p j - p i, by rw [map_sub]; ring⟩)
        have hh : L (p j) = L (p i) := by linarith
        exact hji (hinj hh)
      simp [extendedAtomicCoefficient, hy]
    · simp
  rw [hsum] at h
  have hz : (0 : ℂ) = c i * extendedAtomicCoefficient S T x := by
    simpa [extendedAtomicCoefficient] using h
  exact (mul_eq_zero.mp hz.symm).resolve_left hi

end
end MeyerGeneralProblem

module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalPrefixArray

@[expose] public section
/-! Exact integer coefficients of actual positive original polynomials.
The injective coordinate cast introduces no phases or coefficient changes.
Its whole-lattice convolution is exactly the literal positive motif recurrence. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- Injective exact lift of positive native coordinates to the WHOLE integer lattice. -/
def originalNativeIntegerEmbedding : (ℕ × ℕ) ↪ (ℤ × ℤ) where
  toFun z := ((z.1 : ℤ), (z.2 : ℤ))
  inj' p q h := by
    apply Prod.ext
    · have hf : (p.1 : ℤ) = (q.1 : ℤ) := congrArg Prod.fst h
      exact_mod_cast hf
    · have hf : (p.2 : ℤ) = (q.2 : ℤ) := congrArg Prod.snd h
      exact_mod_cast hf

/-- The ACTUAL coefficients at integer labels, with original phases and all collisions unchanged. -/
def originalPositivePolynomialIntegerCoefficients (q : AddMonoidAlgebra ℂ (ℕ × ℕ)) : (ℤ × ℤ) →₀ ℂ :=
  Finsupp.mapDomain originalNativeIntegerEmbedding q.coeff

/-- The WHOLE actual integer support is precisely the cast of the nonzero native support. -/
theorem originalPositivePolynomialIntegerCoefficients_support (q : AddMonoidAlgebra ℂ (ℕ × ℕ)) :
    (originalPositivePolynomialIntegerCoefficients q).support = q.coeff.support.map originalNativeIntegerEmbedding :=
  Finsupp.support_mapDomain_embedding originalNativeIntegerEmbedding q.coeff

/-- Exact whole-lattice convolution equals the original complete positive-motif sum. -/
theorem originalPositivePolynomialIntegerCoefficients_convolution (q : AddMonoidAlgebra ℂ (ℕ × ℕ)) (u : (ℤ × ℤ) → ℂ) (z : ℤ × ℤ) :
    annihilatorArrayConvolution (originalPositivePolynomialIntegerCoefficients q) u z =
      ∑ i : OriginalPositivePolynomialMotif q, originalPositivePolynomialCoefficient q i *
        u (z - originalPositivePolynomialIntegerCoordinates (originalPositivePolynomialCoordinates q) i) := by
  classical
  change (Finsupp.mapDomain originalNativeIntegerEmbedding q.coeff).sum (fun m c => c * u (z - m)) = _
  rw [Finsupp.sum_mapDomain_index_inj originalNativeIntegerEmbedding.injective]
  exact (q.coeff.support.sum_coe_sort (fun n => q.coeff n * u (z - originalNativeIntegerEmbedding n))).symm

/-- Every lifted coefficient is precisely the original coefficient at that native label. -/
theorem originalPositivePolynomialIntegerCoefficients_apply (q : AddMonoidAlgebra ℂ (ℕ × ℕ)) (n : ℕ × ℕ) :
    originalPositivePolynomialIntegerCoefficients q (originalNativeIntegerEmbedding n) = q.coeff n :=
  Finsupp.mapDomain_apply_of_injective originalNativeIntegerEmbedding.injective q.coeff n

/-- A genuinely nonzero original polynomial remains nonzero after the exact integer lift. -/
theorem originalPositivePolynomialIntegerCoefficients_ne_zero (q : AddMonoidAlgebra ℂ (ℕ × ℕ))
    (hq : q ≠ 0) : originalPositivePolynomialIntegerCoefficients q ≠ 0 := by
  intro h
  apply hq
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.mapDomain_injective originalNativeIntegerEmbedding.injective
  simpa only [originalPositivePolynomialIntegerCoefficients, AddMonoidAlgebra.coeff_zero,
    Finsupp.mapDomain_zero] using h

end
end MeyerGeneralProblem.StrongParity

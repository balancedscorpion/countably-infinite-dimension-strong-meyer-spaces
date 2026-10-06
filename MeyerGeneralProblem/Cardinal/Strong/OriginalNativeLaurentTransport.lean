module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalDilationCoefficients
public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginal.ProductPairClassification

@[expose] public section

/-! Literal Laurent transport of the ENTIRE actual native denominators and
slabs. Both integer coordinates and the once-applied quarter phase are retained. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- Positive integer dilation is injective on every signed native label. -/
theorem originalIntegerCoordinateDilation_injective (d : ℕ) (hd : 0 < d) :
    Function.Injective (originalIntegerCoordinateDilation d) := by
  intro a b h
  have hd' : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  exact Prod.ext (mul_left_cancel₀ hd' (congrArg Prod.fst h))
    (mul_left_cancel₀ hd' (congrArg Prod.snd h))

/-- The full positive embedding commutes with literal signed coordinate dilation. -/
theorem originalPositiveLaurentEmbedding_dilation (d : ℕ)
    (p : AddMonoidAlgebra ℂ (ℕ × ℕ)) :
    originalPositiveLaurentEmbedding (originalPositiveDilation d p) =
      AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ (originalIntegerCoordinateDilation d)
        (originalPositiveLaurentEmbedding p) := by
  refine AddMonoidAlgebra.induction_linear p ?_ ?_ ?_
  · simp
  · intro p q hp hq
    simp only [map_add, hp, hq]
  · intro n c
    rw [originalPositiveDilation_single, originalPositiveLaurentEmbedding_single,
      originalPositiveLaurentEmbedding_single, AddMonoidAlgebra.mapDomainAlgHom_apply,
      AddMonoidAlgebra.mapDomain_single]
    congr 1

/-- The native sheet embeds as its exact original Laurent sheet. -/
theorem originalPositiveLaurentEmbedding_native_sheet (a : ℝ) :
    originalPositiveLaurentEmbedding (originalPositiveSheetPolynomial 1 a) =
      sheetLaurentPolynomial a := by
  simp only [originalPositiveSheetPolynomial, sheetLaurentPolynomial, map_sub, map_add,
    originalPositiveLaurentEmbedding_single, originalNativeIntegerEmbedding]
  rfl

/-- The ENTIRE scheduled native denominator is the actual native annihilator. -/
theorem originalScheduledNativeBlockPolynomial_laurent (bound : ℕ → ℕ) (i : ℕ) :
    originalPositiveLaurentEmbedding (originalScheduledNativeBlockPolynomial bound i) =
      CompactOriginal.productLaurentPolynomial (originalScheduledParameterBlock bound i) := by
  simp only [originalScheduledNativeBlockPolynomial, CompactOriginal.productLaurentPolynomial,
    map_prod, originalPositiveLaurentEmbedding_native_sheet]

/-- The phased full slab embeds with precisely the existing native integer labels. -/
theorem originalPhasedSlabPositivePolynomial_laurent (s : ℕ)
    (r : productNumeratorIndex s → ℂ) :
    originalPositiveLaurentEmbedding (originalPhasedSlabPositivePolynomial s r) =
      productSlabLaurentPolynomial s r := by
  classical
  simp only [originalPhasedSlabPositivePolynomial, originalNativeSlabPositivePolynomial,
    productSlabLaurentPolynomial, map_sum, originalPositiveLaurentEmbedding_single]
  rfl

/-- The scaled block's WHOLE coefficient function is the genuine native pushforward. -/
theorem originalScheduledBlockPositivePolynomial_laurent_coeff (bound : ℕ → ℕ)
    (k : ℕ) (i : Fin k) :
    (originalPositiveLaurentEmbedding (originalScheduledBlockPositivePolynomial bound k i)).coeff =
      (CompactOriginal.productLaurentCoefficients (originalScheduledParameterBlock bound i.val)).mapDomain
        (originalIntegerCoordinateDilation (originalScheduledPrefixCoordinateDilation bound k i)) := by
  rw [originalScheduledBlockPositivePolynomial_native_dilation,
    originalPositiveLaurentEmbedding_dilation, originalScheduledNativeBlockPolynomial_laurent]
  rfl

/-- The native positive cut at zero is unchanged by its genuine positive scale. -/
theorem originalScaledModule_positiveCut_zero (scale : ℝ) (hs : 0 < scale)
    (u : (ℤ × ℤ) → ℂ) :
    arrayPositiveCut (originalScaledModuleFrequencyHom scale) 0 u =
      arrayPositiveCut rankTwoFrequencyHom 0 u := by
  funext n
  have h : 0 ≤ originalScaledModuleFrequencyHom scale n ↔ 0 ≤ rankTwoFrequencyHom n := by
    change 0 ≤ rankTwoFrequencyHom n / scale ↔ _
    simp only [div_nonneg_iff, hs.le, not_le_of_gt hs, and_true, and_false, or_false]
  simp only [arrayPositiveCut, h]

/-- The native strict negative cut preserves its sign and excludes zero after scaling. -/
theorem originalScaledModule_negativeCut_zero (scale : ℝ) (hs : 0 < scale)
    (u : (ℤ × ℤ) → ℂ) :
    arrayNegativeCut (originalScaledModuleFrequencyHom scale) 0 u =
      arrayNegativeCut rankTwoFrequencyHom 0 u := by
  funext n
  have h : originalScaledModuleFrequencyHom scale n < 0 ↔ rankTwoFrequencyHom n < 0 := by
    change rankTwoFrequencyHom n / scale < 0 ↔ _
    simp only [div_neg_iff, hs, not_lt_of_gt hs, and_true, and_false, false_or]
  simp only [arrayNegativeCut, h]

end
end MeyerGeneralProblem.StrongParity

module

public import MeyerGeneralProblem.Cardinal.Strong.RationalOriginalRootMonomials
public import MeyerGeneralProblem.Cardinal.Strong.OriginalCompleteBasisBounds

@[expose] public section

/-! Ordinary binary entries of the ENTIRE specified original W basis evaluated
at EVERY original root. All coefficients, roots and forbidden head data are
computed internally; the literal original physical row is retained. -/

namespace MeyerGeneralProblem.StrongParity

/-- Internally computed size of every actual coefficient of the whole W basis. -/
def originalComputedWCoordinateSize (s m : ℕ) : ℕ :=
  originalHeadCornerProjectionSize s (computedOriginalHeadMask s m)

/-- Internally computed sensitivity of the entire finite original root row. -/
def originalComputedWRootRowSensitivity (s m : ℕ) : ℕ :=
  Fintype.card (productNumeratorIndex s) *
    (originalComputedWCoordinateSize s m + originalRootMonomialSize s)

/-- Integer size of every actual complete W-basis original root evaluation. -/
def originalComputedWRootRowSize (s m : ℕ) : ℕ :=
  Fintype.card (productNumeratorIndex s) * originalComputedWCoordinateSize s m

/-- Full rational original row evaluation on one definite complete W basis vector. -/
def coupledCompactOriginalWRootRowAt (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) (i : Fin s) (n : ℤ)
    (j : CompactOriginal.productOriginalHeadCornerFreeIndex
      (coupledCompactOriginalParameterBlock scales hpos offset s) hs (computedOriginalHeadMask s m))
    (p : ℕ) : ℚ × ℚ :=
  rationalComplexDot
    (fun k => coupledCompactOriginalRootMonomialName scales hpos offset s i n k p)
    (coupledCompactOriginalComputedHeadCornerProjectionName scales hpos offset s hs m j.val.val p)

/-- Ordinary binary original root-row entry, using the complete computed finite error budget. -/
def coupledCompactOriginalWRootRowName (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) (i : Fin s) (n : ℤ)
    (j : CompactOriginal.productOriginalHeadCornerFreeIndex
      (coupledCompactOriginalParameterBlock scales hpos offset s) hs (computedOriginalHeadMask s m))
    (p : ℕ) : ℚ × ℚ :=
  coupledCompactOriginalWRootRowAt scales hpos offset s hs m i n j
    (p + originalComputedWRootRowSensitivity s m)

noncomputable section

/-- The literal original numerator is exactly its complete finite monomial dot product. -/
theorem productSlabNumerator_eq_monomial_dot (s : ℕ) (r : productNumeratorIndex s → ℂ) (x : ℝ) :
    productSlabNumerator s r x = ∑ k : productNumeratorIndex s,
      (unitPhase x ^ k.val.1.val * unitPhase (beta * x - 1 / 4) ^ k.val.2.val) * r k := by
  unfold productSlabNumerator
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The complete original W physical row evaluates the literal original numerator. -/
theorem compactOriginalHeadCornerPhysicalRow_eq_slab {s : ℕ}
    (block : CompactOriginalParameterBlock s) (A : Finset (productOriginalHeadLabel s))
    (x : (compactOriginalProductSheetCarrier block).subtype)
    (v : CompactOriginal.productOriginalHeadCornerKernel block A) :
    CompactOriginal.productOriginalHeadCornerPhysicalRow block A x v =
      productSlabNumerator s v.val.val x.val := rfl

/-- Every entry precision carries the complete coefficient and root-phase error budget. -/
theorem coupledCompactOriginalWRootRowAt_error (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) (i : Fin s) (n : ℤ)
    (j : CompactOriginal.productOriginalHeadCornerFreeIndex
      (coupledCompactOriginalParameterBlock scales hpos offset s) hs (computedOriginalHeadMask s m))
    (p : ℕ) :
    ‖rationalComplexValue (coupledCompactOriginalWRootRowAt scales hpos offset s hs m i n j p) -
      CompactOriginal.productOriginalHeadCornerPhysicalRow
        (coupledCompactOriginalParameterBlock scales hpos offset s) (computedOriginalHeadMask s m)
        (compactOriginalRootPoint (coupledCompactOriginalParameterBlock scales hpos offset s) (i, n))
        (CompactOriginal.productOriginalHeadCornerFreeBasis
          (coupledCompactOriginalParameterBlock scales hpos offset s) hs (computedOriginalHeadMask s m) j)‖ ≤
            (originalComputedWRootRowSensitivity s m : ℝ) * (1 / (2 : ℝ) ^ p) := by
  rw [coupledCompactOriginalWRootRowAt, rationalComplexDot_value,
    compactOriginalHeadCornerPhysicalRow_eq_slab]
  have hcoef (k : productNumeratorIndex s) :=
    coupledCompactOriginalComputedHeadCornerFreeBasisName_error scales hpos offset s hs m j k p
  have hsize (k : productNumeratorIndex s) :=
    compactOriginalHeadCornerFreeBasis_norm_le_size
      (coupledCompactOriginalParameterBlock scales hpos offset s) hs (computedOriginalHeadMask s m) j k
  generalize hw : (CompactOriginal.productOriginalHeadCornerFreeBasis
    (coupledCompactOriginalParameterBlock scales hpos offset s) hs (computedOriginalHeadMask s m) j) = w
    at hcoef hsize ⊢
  let x := compactOriginalRootLabel n
    ((coupledCompactOriginalParameterBlock scales hpos offset s).parameter i)
  have h := finiteComplexDot_sub_norm_le (J := productNumeratorIndex s)
    (fun k => rationalComplexValue (coupledCompactOriginalRootMonomialName scales hpos offset s i n k p))
    (fun k => unitPhase x ^ k.val.1.val * unitPhase (beta * x - 1 / 4) ^ k.val.2.val)
    (fun k => rationalComplexValue (coupledCompactOriginalComputedHeadCornerProjectionName
      scales hpos offset s hs m j.val.val p k)) w.val.val
    (originalRootMonomialSize s) (originalComputedWCoordinateSize s m) 1
    (1 / (2 : ℝ) ^ p) (by positivity)
    (fun k => coupledCompactOriginalRootMonomialName_norm_le_size scales hpos offset s i n k p)
    hsize
    (fun k => coupledCompactOriginalRootMonomialName_error scales hpos offset s i n k p)
    (fun k => (hcoef k).trans_eq (by simp only [Nat.cast_one, one_mul]))
  conv_lhs at h =>
    arg 1
    rhs
    rw [← productSlabNumerator_eq_monomial_dot]
  simpa only [originalComputedWRootRowSensitivity, Nat.cast_one, mul_one,
    x, compactOriginalRootPoint] using h

/-- EVERY actual original root-row entry on EVERY complete W basis vector has binary error. -/
theorem coupledCompactOriginalWRootRowName_error (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) (i : Fin s) (n : ℤ)
    (j : CompactOriginal.productOriginalHeadCornerFreeIndex
      (coupledCompactOriginalParameterBlock scales hpos offset s) hs (computedOriginalHeadMask s m))
    (p : ℕ) :
    ‖rationalComplexValue (coupledCompactOriginalWRootRowName scales hpos offset s hs m i n j p) -
      CompactOriginal.productOriginalHeadCornerPhysicalRow
        (coupledCompactOriginalParameterBlock scales hpos offset s) (computedOriginalHeadMask s m)
        (compactOriginalRootPoint (coupledCompactOriginalParameterBlock scales hpos offset s) (i, n))
        (CompactOriginal.productOriginalHeadCornerFreeBasis
          (coupledCompactOriginalParameterBlock scales hpos offset s) hs (computedOriginalHeadMask s m) j)‖ ≤
            1 / (2 : ℝ) ^ p :=
  (coupledCompactOriginalWRootRowAt_error scales hpos offset s hs m i n j
    (p + originalComputedWRootRowSensitivity s m)).trans
      (integer_sensitivity_binary_shift (originalComputedWRootRowSensitivity s m) p)

/-- The actual ENTIRE W root matrix has its computed integer entry bound. -/
theorem compactOriginalComputedWRootRow_norm_le_size {s : ℕ}
    (block : CompactOriginalParameterBlock s) (hs : 2 ≤ s) (m : ℕ)
    (x : (compactOriginalProductSheetCarrier block).subtype)
    (j : CompactOriginal.productOriginalHeadCornerFreeIndex block hs (computedOriginalHeadMask s m)) :
    ‖CompactOriginal.productOriginalHeadCornerPhysicalRow block (computedOriginalHeadMask s m) x
      (CompactOriginal.productOriginalHeadCornerFreeBasis block hs (computedOriginalHeadMask s m) j)‖ ≤
        (originalComputedWRootRowSize s m : ℝ) := by
  change ‖productSlabNumerator s _ x.val‖ ≤ _
  rw [productSlabNumerator_eq_monomial_dot]
  have h := finiteComplexDot_norm_le
    (fun k : productNumeratorIndex s => unitPhase x.val ^ k.val.1.val *
      unitPhase (beta * x.val - 1 / 4) ^ k.val.2.val)
    (CompactOriginal.productOriginalHeadCornerFreeBasis block hs (computedOriginalHeadMask s m) j).val.val
    1 (originalComputedWCoordinateSize s m)
    (by intro k; simp [norm_mul, norm_pow, unitPhase_norm])
    (fun k => compactOriginalHeadCornerFreeBasis_norm_le_size block hs _ j k)
  simpa only [originalComputedWRootRowSize, mul_one, LinearMap.comp_apply,
    Submodule.subtype_apply] using h

end

end MeyerGeneralProblem.StrongParity

module

public import MeyerGeneralProblem.Cardinal.Strong.RationalOriginalWRootMatrix

@[expose] public section

/-! Ordinary binary determinant names for the ENTIRE original root matrix on
the ENTIRE internally masked W basis of proved exact size. -/

namespace MeyerGeneralProblem.StrongParity

/-- Internally computed whole-permutation determinant precision budget. -/
def originalComputedWRootDetSensitivity (s : ℕ) (hs : 2 ≤ s) (m : ℕ) : ℕ :=
  finiteComplexDetSensitivity (originalComputedWRootRowSize s m + 1)
    (Fintype.card (computedOriginalWIndex s hs m))

/-- Ordinary Gaussian-rational determinant name on every full-size original root tuple. -/
def coupledComputedOriginalWRootDetName (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ)
    (roots : computedOriginalWIndex s hs m → Fin s × ℤ) (p : ℕ) : ℚ × ℚ :=
  rationalComplexDet (coupledComputedOriginalWRootMatrixName scales hpos offset s hs m roots
    (p + originalComputedWRootDetSensitivity s hs m))

noncomputable section

/-- EVERY full original-root determinant has the implemented internally budgeted binary error. -/
theorem coupledComputedOriginalWRootDetName_error (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ)
    (roots : computedOriginalWIndex s hs m → Fin s × ℤ) (p : ℕ) :
    ‖rationalComplexValue (coupledComputedOriginalWRootDetName scales hpos offset s hs m roots p) -
      Matrix.det (coupledComputedOriginalWRootMatrix scales hpos offset s hs m roots)‖ ≤
        1 / (2 : ℝ) ^ p := by
  rw [coupledComputedOriginalWRootDetName, rationalComplexDet_value]
  let q := p + originalComputedWRootDetSensitivity s hs m
  have h := finiteComplexDet_sub_norm_le
    (rationalComplexMatrixValue (coupledComputedOriginalWRootMatrixName scales hpos offset s hs m roots q))
    (coupledComputedOriginalWRootMatrix scales hpos offset s hs m roots)
    (originalComputedWRootRowSize s m + 1) (by omega)
    (1 / (2 : ℝ) ^ q) (by positivity)
    (fun i j => coupledComputedOriginalWRootMatrixName_entry_norm_le scales hpos offset s hs m roots q i j)
    (fun i j => (coupledComputedOriginalWRootMatrix_entry_norm_le scales hpos offset s hs m roots i j).trans
      (by exact_mod_cast Nat.le_succ (originalComputedWRootRowSize s m)))
    (fun i j => coupledComputedOriginalWRootMatrixName_entry_error scales hpos offset s hs m roots q i j)
  exact h.trans (integer_sensitivity_binary_shift (originalComputedWRootDetSensitivity s hs m) p)

end

end MeyerGeneralProblem.StrongParity

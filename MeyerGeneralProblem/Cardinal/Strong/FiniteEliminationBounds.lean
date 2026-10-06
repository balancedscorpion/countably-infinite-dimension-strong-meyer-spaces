module

public import MeyerGeneralProblem.Cardinal.Strong.FiniteComplexBounds

@[expose] public section

/-! Computed natural size and error budgets for every finite degree-elimination
step. The complete coordinate and row families are included in the bounds. -/

namespace MeyerGeneralProblem.StrongParity

/-- Natural size bound for complete degree elimination on bounded rows. -/
def coordinateEliminationSize (M R D t : ℕ) : ℕ := (1 + R * D * M) ^ t

/-- Natural error budget for complete degree elimination with entry error epsilon. -/
def coordinateEliminationSensitivity (M R D : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => coordinateEliminationSensitivity M R D t +
      R * D * (coordinateEliminationSize M R D t + M * coordinateEliminationSensitivity M R D t)

/-- Every complete eliminated vector satisfies the computed integer size bound. -/
theorem complexCoordinateDegreeElimination_norm_le {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (row : I → J → ℂ) (inverse : I → ℂ) (pivot : I → J) (degree : I → ℕ)
    (M : ℕ) (hr : ∀ i j, ‖row i j‖ ≤ (M : ℝ)) (hi : ∀ i, ‖inverse i‖ ≤ 1)
    (v : J → ℂ) (hv : ∀ j, ‖v j‖ ≤ 1) (t : ℕ) (j : J) :
    ‖complexCoordinateDegreeElimination row inverse pivot degree t v j‖ ≤
      (coordinateEliminationSize M (Fintype.card I) (Fintype.card J) t : ℝ) := by
  induction t generalizing j with
  | zero => simpa [complexCoordinateDegreeElimination, coordinateEliminationSize] using hv j
  | succ t ih =>
    simp only [complexCoordinateDegreeElimination]
    let B := coordinateEliminationSize M (Fintype.card I) (Fintype.card J) t
    have hd (i : I) : ‖∑ k : J, row i k * complexCoordinateDegreeElimination row inverse pivot degree t v k‖ ≤
        ((Fintype.card J * M * B : ℕ) : ℝ) :=
      finiteComplexDot_norm_le _ _ M B (hr i) ih
    have hs : ‖∑ i ∈ Finset.univ.filter (fun i => degree i = t ∧ pivot i = j),
        (∑ k : J, row i k * complexCoordinateDegreeElimination row inverse pivot degree t v k) * inverse i‖ ≤
        (Fintype.card I : ℝ) * ((Fintype.card J * M * B : ℕ) : ℝ) := by
      apply finiteFilteredComplexSum_norm_le _ _ _ (by positivity)
      intro i hif
      rw [norm_mul]
      have h := mul_le_mul (hd i) (hi i) (norm_nonneg _) (Nat.cast_nonneg _)
      simpa only [mul_one] using h
    calc
      _ ≤ ‖complexCoordinateDegreeElimination row inverse pivot degree t v j‖ +
          ‖∑ i ∈ Finset.univ.filter (fun i => degree i = t ∧ pivot i = j),
            (∑ k : J, row i k * complexCoordinateDegreeElimination row inverse pivot degree t v k) * inverse i‖ :=
        norm_sub_le _ _
      _ ≤ (B : ℝ) + (Fintype.card I : ℝ) * ((Fintype.card J * M * B : ℕ) : ℝ) :=
        add_le_add (ih j) hs
      _ = _ := by
        simp only [coordinateEliminationSize, pow_succ, B]
        push_cast
        ring

/-- Every complete eliminated vector satisfies the computed entry-error budget. -/
theorem complexCoordinateDegreeElimination_sub_norm_le {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (row other : I → J → ℂ) (inverse : I → ℂ) (pivot : I → J) (degree : I → ℕ)
    (M : ℕ) (hr : ∀ i j, ‖row i j‖ ≤ (M : ℝ))
    (ho : ∀ i j, ‖other i j‖ ≤ (M : ℝ)) (hi : ∀ i, ‖inverse i‖ ≤ 1)
    (epsilon : ℝ) (he : 0 ≤ epsilon) (hro : ∀ i j, ‖row i j - other i j‖ ≤ epsilon)
    (v : J → ℂ) (hv : ∀ j, ‖v j‖ ≤ 1) (t : ℕ) (j : J) :
    ‖complexCoordinateDegreeElimination row inverse pivot degree t v j -
      complexCoordinateDegreeElimination other inverse pivot degree t v j‖ ≤
        (coordinateEliminationSensitivity M (Fintype.card I) (Fintype.card J) t : ℝ) * epsilon := by
  induction t generalizing j with
  | zero => simp [complexCoordinateDegreeElimination, coordinateEliminationSensitivity]
  | succ t ih =>
    let B := coordinateEliminationSize M (Fintype.card I) (Fintype.card J) t
    let L := coordinateEliminationSensitivity M (Fintype.card I) (Fintype.card J) t
    let w := complexCoordinateDegreeElimination row inverse pivot degree t v
    let z := complexCoordinateDegreeElimination other inverse pivot degree t v
    have hz : ∀ k, ‖z k‖ ≤ (B : ℝ) :=
      complexCoordinateDegreeElimination_norm_le other inverse pivot degree M ho hi v hv t
    have hd (i : I) : ‖(∑ k : J, row i k * w k) - (∑ k : J, other i k * z k)‖ ≤
        ((Fintype.card J * (B + M * L) : ℕ) : ℝ) * epsilon :=
      finiteComplexDot_sub_norm_le _ _ _ _ M B L epsilon he (hr i) hz (hro i) ih
    have hs : ‖∑ i ∈ Finset.univ.filter (fun i => degree i = t ∧ pivot i = j),
        ((∑ k : J, row i k * w k) - (∑ k : J, other i k * z k)) * inverse i‖ ≤
        (Fintype.card I : ℝ) * (((Fintype.card J * (B + M * L) : ℕ) : ℝ) * epsilon) := by
      apply finiteFilteredComplexSum_norm_le _ _ _ (by positivity)
      intro i hif
      rw [norm_mul]
      have h := mul_le_mul (hd i) (hi i) (norm_nonneg _) (by positivity)
      simpa only [mul_one] using h
    have heq : complexCoordinateDegreeElimination row inverse pivot degree (t + 1) v j -
        complexCoordinateDegreeElimination other inverse pivot degree (t + 1) v j =
        (w j - z j) - ∑ i ∈ Finset.univ.filter (fun i => degree i = t ∧ pivot i = j),
          ((∑ k : J, row i k * w k) - (∑ k : J, other i k * z k)) * inverse i := by
      simp only [complexCoordinateDegreeElimination, w, z]
      simp only [sub_mul, Finset.sum_sub_distrib]
      ring
    rw [heq]
    calc
      _ ≤ ‖w j - z j‖ + ‖∑ i ∈ Finset.univ.filter (fun i => degree i = t ∧ pivot i = j),
          ((∑ k : J, row i k * w k) - (∑ k : J, other i k * z k)) * inverse i‖ := norm_sub_le _ _
      _ ≤ (L : ℝ) * epsilon + (Fintype.card I : ℝ) *
          (((Fintype.card J * (B + M * L) : ℕ) : ℝ) * epsilon) := add_le_add (ih j) hs
      _ = _ := by simp only [coordinateEliminationSensitivity, L, B]; push_cast; ring

end MeyerGeneralProblem.StrongParity

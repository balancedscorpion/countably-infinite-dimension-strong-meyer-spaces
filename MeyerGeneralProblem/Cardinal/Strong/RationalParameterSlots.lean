module

public import MeyerGeneralProblem.Cardinal.Strong.ProofOnlyExclusionSearch

@[expose] public section

/-! Computed nondegenerate compact rational parameter slots and actual safe shrinking. -/

namespace MeyerGeneralProblem.StrongParity

/-- A rational parameter interval with proved actual original compact-domain bounds. -/
structure RationalParameterSlot where
  /-- The rational lower endpoint. -/
  lower : ℚ
  /-- The rational upper endpoint. -/
  upper : ℚ
  /-- The lower endpoint is strictly positive. -/
  lower_pos : 0 < lower
  /-- The upper endpoint is at most one half. -/
  upper_le_half : upper ≤ 1 / 2
  /-- The interval is nondegenerate. -/
  lower_lt_upper : lower < upper

/-- The actual ordinary search-and-shrink step preserving all slot invariants. -/
def RationalParameterSlot.shrink (slot : RationalParameterSlot) (codes : List ComputedRootExclusion)
    (names : ℕ → ℕ → ℚ) (hvalid : BinaryRationalNamesValid names) (m : ℕ) (hm : 0 < m)
    (stage : ℕ) : RationalParameterSlot :=
  let data := proofOnlyExclusionData codes names hvalid m hm slot.lower slot.upper
    slot.lower_pos slot.upper_le_half slot.lower_lt_upper
  let interval := rationalExclusionInterval codes names m slot.lower slot.upper data.1 data.2 stage
  have hd := proofOnlyExclusionData_spec codes names hvalid m hm slot.lower slot.upper
    slot.lower_pos slot.upper_le_half slot.lower_lt_upper
  have hg := rationalExclusionInterval_geometry codes names m slot.lower slot.upper data.1 data.2
    stage hd.1 hd.2.1 hd.2.2
  { lower := interval.1, upper := interval.2, lower_pos := slot.lower_pos.trans hg.1,
    upper_le_half := hg.2.2.1.le.trans slot.upper_le_half, lower_lt_upper := hg.2.1 }

/-- The computed child is strictly inside its slot and has the requested binary width. -/
theorem RationalParameterSlot.shrink_geometry (slot : RationalParameterSlot)
    (codes : List ComputedRootExclusion) (names : ℕ → ℕ → ℚ)
    (hvalid : BinaryRationalNamesValid names) (m : ℕ) (hm : 0 < m) (stage : ℕ) :
    slot.lower < (slot.shrink codes names hvalid m hm stage).lower ∧
    (slot.shrink codes names hvalid m hm stage).upper < slot.upper ∧
    (slot.shrink codes names hvalid m hm stage).upper -
      (slot.shrink codes names hvalid m hm stage).lower ≤ rationalBinaryRadius stage := by
  let data := proofOnlyExclusionData codes names hvalid m hm slot.lower slot.upper
    slot.lower_pos slot.upper_le_half slot.lower_lt_upper
  have hd := proofOnlyExclusionData_spec codes names hvalid m hm slot.lower slot.upper
    slot.lower_pos slot.upper_le_half slot.lower_lt_upper
  have hg := rationalExclusionInterval_geometry codes names m slot.lower slot.upper data.1 data.2
    stage hd.1 hd.2.1 hd.2.2
  exact ⟨hg.1, hg.2.2.1, hg.2.2.2⟩

noncomputable section

/-- The closed real interval represented by the actual rational slot. -/
def RationalParameterSlot.realInterval (slot : RationalParameterSlot) : Set ℝ :=
  Set.Icc (slot.lower : ℝ) (slot.upper : ℝ)

/-- Every slot is a nonempty actual original compact interval. -/
theorem RationalParameterSlot.realInterval_nonempty (slot : RationalParameterSlot) :
    slot.realInterval.Nonempty := by
  exact Set.nonempty_Icc.mpr (by exact_mod_cast slot.lower_lt_upper.le)

/-- Every slot stays in the domain of the actual original root labels. -/
theorem RationalParameterSlot.realInterval_subset_compact (slot : RationalParameterSlot) :
    slot.realInterval ⊆ Set.Icc (0 : ℝ) (1 / 2) := by
  have hl : (0 : ℝ) ≤ (slot.lower : ℝ) := by exact_mod_cast slot.lower_pos.le
  have hu : (slot.upper : ℝ) ≤ 1 / 2 := by
    have h : (slot.upper : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast slot.upper_le_half
    norm_num at h
    exact h
  exact Set.Icc_subset_Icc hl hu

/-- Every computed child closed interval lies in its parent's closed interval. -/
theorem RationalParameterSlot.shrink_subset (slot : RationalParameterSlot)
    (codes : List ComputedRootExclusion) (names : ℕ → ℕ → ℚ)
    (hvalid : BinaryRationalNamesValid names) (m : ℕ) (hm : 0 < m) (stage : ℕ) :
    (slot.shrink codes names hvalid m hm stage).realInterval ⊆ slot.realInterval := by
  have h := slot.shrink_geometry codes names hvalid m hm stage
  apply Set.Icc_subset_Icc
  · exact_mod_cast h.1.le
  · exact_mod_cast h.2.1.le

/-- ALL points of the actual computed child avoid every listed original equation. -/
theorem RationalParameterSlot.shrink_protects (slot : RationalParameterSlot)
    (codes : List ComputedRootExclusion) (names : ℕ → ℕ → ℚ)
    (hvalid : BinaryRationalNamesValid names) (m : ℕ) (hm : 0 < m) (stage : ℕ)
    (values : ℕ → ℝ) (hname : ∀ i p, |(names i p : ℝ) - values i| ≤ 1 / (2 : ℝ) ^ p)
    {a : ℝ} (ha : a ∈ (slot.shrink codes names hvalid m hm stage).realInterval) :
    ∀ code ∈ codes, (code.semantic values).residual m a ≠ 0 := by
  let data := proofOnlyExclusionData codes names hvalid m hm slot.lower slot.upper
    slot.lower_pos slot.upper_le_half slot.lower_lt_upper
  have hd := proofOnlyExclusionData_spec codes names hvalid m hm slot.lower slot.upper
    slot.lower_pos slot.upper_le_half slot.lower_lt_upper
  exact rationalExclusionInterval_protects codes names values hname m slot.lower slot.upper data.1
    data.2 stage slot.lower_pos slot.upper_le_half hd.1 hd.2.1 hd.2.2 ha

end

end MeyerGeneralProblem.StrongParity

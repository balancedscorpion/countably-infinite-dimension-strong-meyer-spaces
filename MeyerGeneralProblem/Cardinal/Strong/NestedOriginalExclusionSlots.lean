module

public import MeyerGeneralProblem.Cardinal.Strong.RationalParameterSlots

@[expose] public section

/-! The actual ordinary infinite nested original exclusion program. -/

namespace MeyerGeneralProblem.StrongParity

/-- The first k+1 actual computed original equations of the prescribed enumeration. -/
def originalExclusionPrefix (enumerate : ℕ → ComputedRootExclusion) (k : ℕ) :
    List ComputedRootExclusion := (List.range (k + 1)).map enumerate

/-- Every earlier enumerated equation is in the actual finite prefix. -/
theorem originalExclusionPrefix_mem (enumerate : ℕ → ComputedRootExclusion) {i k : ℕ}
    (hik : i ≤ k) : enumerate i ∈ originalExclusionPrefix enumerate k :=
  List.mem_map.mpr ⟨i, List.mem_range.mpr (Nat.lt_succ_of_le hik), rfl⟩

/-- The actual ordinary finite-recursive nested interval program, without supplied intervals. -/
def nestedOriginalExclusionSlots (enumerate : ℕ → ComputedRootExclusion) (names : ℕ → ℕ → ℚ)
    (hvalid : BinaryRationalNamesValid names) (m : ℕ) (hm : 0 < m)
    (initial : RationalParameterSlot) : ℕ → RationalParameterSlot
  | 0 => initial
  | k + 1 => (nestedOriginalExclusionSlots enumerate names hvalid m hm initial k).shrink
      (originalExclusionPrefix enumerate k) names hvalid m hm k

/-- The emitted lower endpoints increase strictly at every step. -/
theorem nestedOriginalExclusionSlots_lower_step (enumerate : ℕ → ComputedRootExclusion)
    (names : ℕ → ℕ → ℚ) (hvalid : BinaryRationalNamesValid names) (m : ℕ) (hm : 0 < m)
    (initial : RationalParameterSlot) (k : ℕ) :
    (nestedOriginalExclusionSlots enumerate names hvalid m hm initial k).lower <
      (nestedOriginalExclusionSlots enumerate names hvalid m hm initial (k + 1)).lower :=
  ((nestedOriginalExclusionSlots enumerate names hvalid m hm initial k).shrink_geometry
    (originalExclusionPrefix enumerate k) names hvalid m hm k).1

/-- The emitted upper endpoints decrease strictly at every step. -/
theorem nestedOriginalExclusionSlots_upper_step (enumerate : ℕ → ComputedRootExclusion)
    (names : ℕ → ℕ → ℚ) (hvalid : BinaryRationalNamesValid names) (m : ℕ) (hm : 0 < m)
    (initial : RationalParameterSlot) (k : ℕ) :
    (nestedOriginalExclusionSlots enumerate names hvalid m hm initial (k + 1)).upper <
      (nestedOriginalExclusionSlots enumerate names hvalid m hm initial k).upper :=
  ((nestedOriginalExclusionSlots enumerate names hvalid m hm initial k).shrink_geometry
    (originalExclusionPrefix enumerate k) names hvalid m hm k).2.1

/-- Every emitted child has the definite requested rational binary width. -/
theorem nestedOriginalExclusionSlots_width (enumerate : ℕ → ComputedRootExclusion)
    (names : ℕ → ℕ → ℚ) (hvalid : BinaryRationalNamesValid names) (m : ℕ) (hm : 0 < m)
    (initial : RationalParameterSlot) (k : ℕ) :
    (nestedOriginalExclusionSlots enumerate names hvalid m hm initial (k + 1)).upper -
      (nestedOriginalExclusionSlots enumerate names hvalid m hm initial (k + 1)).lower ≤
      rationalBinaryRadius k :=
  ((nestedOriginalExclusionSlots enumerate names hvalid m hm initial k).shrink_geometry
    (originalExclusionPrefix enumerate k) names hvalid m hm k).2.2

/-- The actual rational midpoint name emitted at every requested precision. -/
def nestedOriginalParameterName (enumerate : ℕ → ComputedRootExclusion) (names : ℕ → ℕ → ℚ)
    (hvalid : BinaryRationalNamesValid names) (m : ℕ) (hm : 0 < m)
    (initial : RationalParameterSlot) (p : ℕ) : ℚ :=
  let s := nestedOriginalExclusionSlots enumerate names hvalid m hm initial (p + 1)
  (s.lower + s.upper) / 2

/-- Every actual emitted rational name stays in the original compact parameter domain. -/
theorem nestedOriginalParameterName_range (enumerate : ℕ → ComputedRootExclusion)
    (names : ℕ → ℕ → ℚ) (hvalid : BinaryRationalNamesValid names) (m : ℕ) (hm : 0 < m)
    (initial : RationalParameterSlot) (p : ℕ) :
    0 ≤ nestedOriginalParameterName enumerate names hvalid m hm initial p ∧
      nestedOriginalParameterName enumerate names hvalid m hm initial p ≤ 1 / 2 := by
  let s := nestedOriginalExclusionSlots enumerate names hvalid m hm initial (p + 1)
  have hlo := s.lower_pos
  have hhi := s.upper_le_half
  have horder := s.lower_lt_upper
  change 0 ≤ (s.lower + s.upper) / 2 ∧ (s.lower + s.upper) / 2 ≤ 1 / 2
  constructor <;> linarith

noncomputable section

/-- The actual sequence consists of nested closed intervals. -/
theorem nestedOriginalExclusionSlots_step_subset (enumerate : ℕ → ComputedRootExclusion)
    (names : ℕ → ℕ → ℚ) (hvalid : BinaryRationalNamesValid names) (m : ℕ) (hm : 0 < m)
    (initial : RationalParameterSlot) (k : ℕ) :
    (nestedOriginalExclusionSlots enumerate names hvalid m hm initial (k + 1)).realInterval ⊆
      (nestedOriginalExclusionSlots enumerate names hvalid m hm initial k).realInterval :=
  (nestedOriginalExclusionSlots enumerate names hvalid m hm initial k).shrink_subset
    (originalExclusionPrefix enumerate k) names hvalid m hm k

/-- Every later actual closed interval is contained in every earlier one. -/
theorem nestedOriginalExclusionSlots_antitone (enumerate : ℕ → ComputedRootExclusion)
    (names : ℕ → ℕ → ℚ) (hvalid : BinaryRationalNamesValid names) (m : ℕ) (hm : 0 < m)
    (initial : RationalParameterSlot) :
    Antitone (fun k => (nestedOriginalExclusionSlots enumerate names hvalid m hm initial k).realInterval) :=
  antitone_nat_of_succ_le (nestedOriginalExclusionSlots_step_subset enumerate names hvalid m hm initial)

/-- Every earlier original exclusion persists on all subsequent actual computed intervals. -/
theorem nestedOriginalExclusionSlots_protects_earlier (enumerate : ℕ → ComputedRootExclusion)
    (names : ℕ → ℕ → ℚ) (hvalid : BinaryRationalNamesValid names) (m : ℕ) (hm : 0 < m)
    (initial : RationalParameterSlot) (values : ℕ → ℝ)
    (hname : ∀ i p, |(names i p : ℝ) - values i| ≤ 1 / (2 : ℝ) ^ p)
    {i k : ℕ} (hik : i + 1 ≤ k) {a : ℝ}
    (ha : a ∈ (nestedOriginalExclusionSlots enumerate names hvalid m hm initial k).realInterval) :
    ((enumerate i).semantic values).residual m a ≠ 0 := by
  have hmem := (nestedOriginalExclusionSlots_antitone enumerate names hvalid m hm initial hik) ha
  exact (nestedOriginalExclusionSlots enumerate names hvalid m hm initial i).shrink_protects
    (originalExclusionPrefix enumerate i) names hvalid m hm i values hname hmem
    (enumerate i) (originalExclusionPrefix_mem enumerate le_rfl)

end

end MeyerGeneralProblem.StrongParity

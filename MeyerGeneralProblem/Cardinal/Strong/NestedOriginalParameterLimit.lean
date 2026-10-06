module

public import MeyerGeneralProblem.Cardinal.Strong.NestedOriginalExclusionSlots

@[expose] public section

/-! The actual computed nested name has a unique real limit satisfying every original exclusion. -/

namespace MeyerGeneralProblem.StrongParity

open Filter
open scoped Topology

noncomputable section

/-- The actual computed closed nested intervals have a common real point. -/
theorem nestedOriginalParameter_exists (enumerate : ℕ → ComputedRootExclusion)
    (names : ℕ → ℕ → ℚ) (hvalid : BinaryRationalNamesValid names) (m : ℕ) (hm : 0 < m)
    (initial : RationalParameterSlot) :
    ∃ a : ℝ, ∀ k, a ∈ (nestedOriginalExclusionSlots enumerate names hvalid m hm initial k).realInterval := by
  have h := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun k => (nestedOriginalExclusionSlots enumerate names hvalid m hm initial k).realInterval)
    (nestedOriginalExclusionSlots_step_subset enumerate names hvalid m hm initial)
    (fun k => (nestedOriginalExclusionSlots enumerate names hvalid m hm initial k).realInterval_nonempty)
    isCompact_Icc (fun _ => isClosed_Icc)
  obtain ⟨a, ha⟩ := h
  exact ⟨a, Set.mem_iInter.mp ha⟩

/-- The actual real point named by the already defined ordinary nested midpoint program. -/
def nestedOriginalParameterValue (enumerate : ℕ → ComputedRootExclusion) (names : ℕ → ℕ → ℚ)
    (hvalid : BinaryRationalNamesValid names) (m : ℕ) (hm : 0 < m)
    (initial : RationalParameterSlot) : ℝ :=
  Classical.choose (nestedOriginalParameter_exists enumerate names hvalid m hm initial)

/-- The actual constructed value lies in EVERY computed closed interval. -/
theorem nestedOriginalParameterValue_mem (enumerate : ℕ → ComputedRootExclusion)
    (names : ℕ → ℕ → ℚ) (hvalid : BinaryRationalNamesValid names) (m : ℕ) (hm : 0 < m)
    (initial : RationalParameterSlot) (k : ℕ) :
    nestedOriginalParameterValue enumerate names hvalid m hm initial ∈
      (nestedOriginalExclusionSlots enumerate names hvalid m hm initial k).realInterval :=
  Classical.choose_spec (nestedOriginalParameter_exists enumerate names hvalid m hm initial) k

/-- The actual constructed value is strictly inside its assigned original rational slot. -/
theorem nestedOriginalParameterValue_interior (enumerate : ℕ → ComputedRootExclusion)
    (names : ℕ → ℕ → ℚ) (hvalid : BinaryRationalNamesValid names) (m : ℕ) (hm : 0 < m)
    (initial : RationalParameterSlot) :
    (initial.lower : ℝ) < nestedOriginalParameterValue enumerate names hvalid m hm initial ∧
      nestedOriginalParameterValue enumerate names hvalid m hm initial < (initial.upper : ℝ) := by
  have ha := nestedOriginalParameterValue_mem enumerate names hvalid m hm initial 1
  have hl : (initial.lower : ℝ) <
      ((nestedOriginalExclusionSlots enumerate names hvalid m hm initial 1).lower : ℝ) := by
    exact_mod_cast nestedOriginalExclusionSlots_lower_step enumerate names hvalid m hm initial 0
  have hu : ((nestedOriginalExclusionSlots enumerate names hvalid m hm initial 1).upper : ℝ) <
      (initial.upper : ℝ) := by
    exact_mod_cast nestedOriginalExclusionSlots_upper_step enumerate names hvalid m hm initial 0
  exact ⟨hl.trans_le ha.1, ha.2.trans_lt hu⟩

/-- The ordinary midpoint name approximates ANY common point with definite binary error. -/
theorem nestedOriginalParameterName_error_of_mem (enumerate : ℕ → ComputedRootExclusion)
    (names : ℕ → ℕ → ℚ) (hvalid : BinaryRationalNamesValid names) (m : ℕ) (hm : 0 < m)
    (initial : RationalParameterSlot) {a : ℝ}
    (ha : ∀ k, a ∈ (nestedOriginalExclusionSlots enumerate names hvalid m hm initial k).realInterval)
    (p : ℕ) : |(nestedOriginalParameterName enumerate names hvalid m hm initial p : ℝ) - a| ≤
      1 / (2 : ℝ) ^ p := by
  let s := nestedOriginalExclusionSlots enumerate names hvalid m hm initial (p + 1)
  have hmid : (nestedOriginalParameterName enumerate names hvalid m hm initial p : ℝ) =
      ((s.lower : ℝ) + (s.upper : ℝ)) / 2 := by simp [nestedOriginalParameterName, s]
  have hmem : (s.lower : ℝ) ≤ a ∧ a ≤ (s.upper : ℝ) := ha (p + 1)
  have hw : (s.upper : ℝ) - (s.lower : ℝ) ≤ 1 / (2 : ℝ) ^ p := by
    have h := nestedOriginalExclusionSlots_width enumerate names hvalid m hm initial p
    have hh : (((s.upper - s.lower : ℚ) : ℝ)) ≤ (rationalBinaryRadius p : ℝ) := by
      exact_mod_cast h
    simpa only [Rat.cast_sub, rationalBinaryRadius_cast] using hh
  rw [hmid]
  exact (abs_le.mpr ⟨by linarith [hmem.1, hmem.2], by linarith [hmem.1, hmem.2]⟩).trans hw

/-- The actually constructed original parameter has the implemented binary midpoint name. -/
theorem nestedOriginalParameterName_error (enumerate : ℕ → ComputedRootExclusion)
    (names : ℕ → ℕ → ℚ) (hvalid : BinaryRationalNamesValid names) (m : ℕ) (hm : 0 < m)
    (initial : RationalParameterSlot) (p : ℕ) :
    |(nestedOriginalParameterName enumerate names hvalid m hm initial p : ℝ) -
      nestedOriginalParameterValue enumerate names hvalid m hm initial| ≤ 1 / (2 : ℝ) ^ p :=
  nestedOriginalParameterName_error_of_mem enumerate names hvalid m hm initial
    (nestedOriginalParameterValue_mem enumerate names hvalid m hm initial) p

/-- The actual ordinary parameter-name program converges to the constructed original parameter. -/
theorem nestedOriginalParameterName_tendsto (enumerate : ℕ → ComputedRootExclusion)
    (names : ℕ → ℕ → ℚ) (hvalid : BinaryRationalNamesValid names) (m : ℕ) (hm : 0 < m)
    (initial : RationalParameterSlot) :
    Tendsto (fun p => (nestedOriginalParameterName enumerate names hvalid m hm initial p : ℝ))
      atTop (𝓝 (nestedOriginalParameterValue enumerate names hvalid m hm initial)) :=
  rational_binary_name_tendsto (nestedOriginalParameterName_error enumerate names hvalid m hm initial)

/-- The common point of the actual computed nested intervals is unique. -/
theorem nestedOriginalParameterValue_unique (enumerate : ℕ → ComputedRootExclusion)
    (names : ℕ → ℕ → ℚ) (hvalid : BinaryRationalNamesValid names) (m : ℕ) (hm : 0 < m)
    (initial : RationalParameterSlot) {a : ℝ}
    (ha : ∀ k, a ∈ (nestedOriginalExclusionSlots enumerate names hvalid m hm initial k).realInterval) :
    a = nestedOriginalParameterValue enumerate names hvalid m hm initial :=
  tendsto_nhds_unique
    (rational_binary_name_tendsto (nestedOriginalParameterName_error_of_mem enumerate names hvalid m hm initial ha))
    (nestedOriginalParameterName_tendsto enumerate names hvalid m hm initial)

/-- EVERY enumerated literal original equation is nonzero at the actually constructed parameter. -/
theorem nestedOriginalParameterValue_avoids (enumerate : ℕ → ComputedRootExclusion)
    (names : ℕ → ℕ → ℚ) (hvalid : BinaryRationalNamesValid names) (m : ℕ) (hm : 0 < m)
    (initial : RationalParameterSlot) (values : ℕ → ℝ)
    (hname : ∀ i p, |(names i p : ℝ) - values i| ≤ 1 / (2 : ℝ) ^ p) (i : ℕ) :
    ((enumerate i).semantic values).residual m
      (nestedOriginalParameterValue enumerate names hvalid m hm initial) ≠ 0 :=
  nestedOriginalExclusionSlots_protects_earlier enumerate names hvalid m hm initial values hname
    le_rfl (nestedOriginalParameterValue_mem enumerate names hvalid m hm initial (i + 1))

end

end MeyerGeneralProblem.StrongParity

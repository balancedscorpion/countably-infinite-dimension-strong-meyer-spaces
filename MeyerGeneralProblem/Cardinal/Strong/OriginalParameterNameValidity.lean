module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalExclusionEnumeration

@[expose] public section

/-! Proof-only validity of ordinary compact original parameter names. -/

namespace MeyerGeneralProblem.StrongParity

/-- The ordinary name stays compact and binary-approximates an actual compact real value. -/
def OriginalParameterNameValid (name : ℕ → ℚ) : Prop :=
  (∀ p, 0 ≤ name p ∧ name p ≤ 1 / 2) ∧
    ∃ a : ℝ, a ∈ Set.Icc (0 : ℝ) (1 / 2) ∧
      ∀ p, |(name p : ℝ) - a| ≤ 1 / (2 : ℝ) ^ p

/-- A compact original parameter name with proof fields only; its computational data are rational. -/
abbrev CertifiedOriginalParameterName := {name : ℕ → ℚ // OriginalParameterNameValid name}

/-- The implemented all-exclusion program supplies its own compact-name validity. -/
theorem allOriginalExclusionsParameterName_valid (names : ℕ → ℕ → ℚ)
    (hvalid : BinaryRationalNamesValid names) (m : ℕ) (hm : 0 < m)
    (slot : RationalParameterSlot) :
    OriginalParameterNameValid (allOriginalExclusionsParameterName names hvalid m hm slot) := by
  refine ⟨allOriginalExclusionsParameterName_range names hvalid m hm slot,
    allOriginalExclusionsParameterValue names hvalid m hm slot, ?_,
    allOriginalExclusionsParameterName_error names hvalid m hm slot⟩
  have h := allOriginalExclusionsParameterValue_interior names hvalid m hm slot
  have hlo : (0 : ℝ) < (slot.lower : ℝ) := by exact_mod_cast slot.lower_pos
  have hhi : (slot.upper : ℝ) ≤ 1 / 2 := by
    have hh : (slot.upper : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast slot.upper_le_half
    norm_num at hh
    exact hh
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

noncomputable section

/-- The actual unique real value of a proved compact ordinary parameter name. -/
def certifiedOriginalParameterValue (name : CertifiedOriginalParameterName) : ℝ :=
  Classical.choose name.property.2

/-- The actual value of a certified ordinary name is inside the compact original domain. -/
theorem certifiedOriginalParameterValue_compact (name : CertifiedOriginalParameterName) :
    certifiedOriginalParameterValue name ∈ Set.Icc (0 : ℝ) (1 / 2) :=
  (Classical.choose_spec name.property.2).1

/-- The certified ordinary name actually approximates its unique real value at every precision. -/
theorem certifiedOriginalParameterValue_error (name : CertifiedOriginalParameterName) (p : ℕ) :
    |(name.val p : ℝ) - certifiedOriginalParameterValue name| ≤ 1 / (2 : ℝ) ^ p :=
  (Classical.choose_spec name.property.2).2 p

/-- Binary error identifies the actual certified value uniquely. -/
theorem certifiedOriginalParameterValue_unique (name : CertifiedOriginalParameterName) {a : ℝ}
    (he : ∀ p, |(name.val p : ℝ) - a| ≤ 1 / (2 : ℝ) ^ p) :
    certifiedOriginalParameterValue name = a :=
  tendsto_nhds_unique (rational_binary_name_tendsto (certifiedOriginalParameterValue_error name))
    (rational_binary_name_tendsto he)

end

end MeyerGeneralProblem.StrongParity

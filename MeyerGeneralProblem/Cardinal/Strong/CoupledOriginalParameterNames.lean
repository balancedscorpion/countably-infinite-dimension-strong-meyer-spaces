module

public import MeyerGeneralProblem.Cardinal.Strong.EarlierOriginalConstantNames

@[expose] public section

/-! The actual coupled family of ordinary original parameter names.
Every recursive computational call is to an EARLIER sheet. Validity derives
from the constructed earlier names, rather than a supplied final family.
-/

namespace MeyerGeneralProblem.StrongParity

/-- Construct the current certified ordinary parameter from actual earlier certified programs. -/
def nextCoupledOriginalParameterName (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (slots : ℕ → RationalParameterSlot) (i : ℕ)
    (earlier : Fin i → CertifiedOriginalParameterName) : CertifiedOriginalParameterName :=
  ⟨allOriginalExclusionsParameterName (earlierOriginalConstantNames scales earlier)
      (earlierOriginalConstantNames_valid scales earlier) (scales i) (hpos i) (slots i),
    allOriginalExclusionsParameterName_valid (earlierOriginalConstantNames scales earlier)
      (earlierOriginalConstantNames_valid scales earlier) (scales i) (hpos i) (slots i)⟩

/-- The actual ordinary coupled family, constructed by recursion only on smaller sheet indices. -/
def coupledOriginalParameterNames (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (slots : ℕ → RationalParameterSlot) (i : ℕ) : CertifiedOriginalParameterName :=
  nextCoupledOriginalParameterName scales hpos slots i
    (fun k => coupledOriginalParameterNames scales hpos slots k.val)
termination_by i
decreasing_by exact k.isLt

/-- The actual recursive family at each sheet is precisely the implemented complete-exclusion program. -/
theorem coupledOriginalParameterNames_eq (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (slots : ℕ → RationalParameterSlot) (i : ℕ) :
    coupledOriginalParameterNames scales hpos slots i =
      nextCoupledOriginalParameterName scales hpos slots i
        (fun j => coupledOriginalParameterNames scales hpos slots j.val) := by
  rw [coupledOriginalParameterNames]

/-- Every generated coupled name has compact range, proved internally. -/
theorem coupledOriginalParameterNames_range (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (slots : ℕ → RationalParameterSlot) (i p : ℕ) :
    0 ≤ (coupledOriginalParameterNames scales hpos slots i).val p ∧
      (coupledOriginalParameterNames scales hpos slots i).val p ≤ 1 / 2 :=
  (coupledOriginalParameterNames scales hpos slots i).property.1 p

noncomputable section

/-- The actual unique real parameter of each constructed coupled rational name. -/
def coupledOriginalParameterValue (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (slots : ℕ → RationalParameterSlot) (i : ℕ) : ℝ :=
  certifiedOriginalParameterValue (coupledOriginalParameterNames scales hpos slots i)

/-- Every actual coupled parameter is in the compact original domain. -/
theorem coupledOriginalParameterValue_compact (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (slots : ℕ → RationalParameterSlot) (i : ℕ) :
    coupledOriginalParameterValue scales hpos slots i ∈ Set.Icc (0 : ℝ) (1 / 2) :=
  certifiedOriginalParameterValue_compact (coupledOriginalParameterNames scales hpos slots i)

/-- Every actual coupled value has the implemented ordinary binary name at every precision. -/
theorem coupledOriginalParameterNames_error (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (slots : ℕ → RationalParameterSlot) (i p : ℕ) :
    |((coupledOriginalParameterNames scales hpos slots i).val p : ℝ) -
      coupledOriginalParameterValue scales hpos slots i| ≤ 1 / (2 : ℝ) ^ p :=
  certifiedOriginalParameterValue_error (coupledOriginalParameterNames scales hpos slots i) p

/-- The actual coupled value equals the limit of its own internally supplied complete-exclusion program. -/
theorem coupledOriginalParameterValue_eq (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (slots : ℕ → RationalParameterSlot) (i : ℕ) :
    coupledOriginalParameterValue scales hpos slots i =
      allOriginalExclusionsParameterValue
        (earlierOriginalConstantNames scales (fun j : Fin i => coupledOriginalParameterNames scales hpos slots j.val))
        (earlierOriginalConstantNames_valid scales (fun j : Fin i => coupledOriginalParameterNames scales hpos slots j.val))
        (scales i) (hpos i) (slots i) := by
  unfold coupledOriginalParameterValue
  rw [coupledOriginalParameterNames_eq]
  apply certifiedOriginalParameterValue_unique
  exact allOriginalExclusionsParameterName_error _ _ _ _ _

/-- Every actual coupled parameter lies strictly inside its assigned slot. -/
theorem coupledOriginalParameterValue_interior (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (slots : ℕ → RationalParameterSlot) (i : ℕ) :
    ((slots i).lower : ℝ) < coupledOriginalParameterValue scales hpos slots i ∧
      coupledOriginalParameterValue scales hpos slots i < ((slots i).upper : ℝ) := by
  rw [coupledOriginalParameterValue_eq]
  exact allOriginalExclusionsParameterValue_interior _ _ _ _ _

/-- Every original equation against the actual complete prior dictionary is avoided at every sheet. -/
theorem coupledOriginalParameterValue_avoids (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (slots : ℕ → RationalParameterSlot) (i : ℕ) (code : ComputedRootExclusion) :
    (code.semantic (earlierOriginalConstantValues scales
      (fun j : Fin i => coupledOriginalParameterNames scales hpos slots j.val))).residual (scales i)
        (coupledOriginalParameterValue scales hpos slots i) ≠ 0 := by
  rw [coupledOriginalParameterValue_eq]
  exact allOriginalExclusionsParameterValue_avoids _ _ _ _ _ _
    (earlierOriginalConstantNames_error _ _) code

end

end MeyerGeneralProblem.StrongParity

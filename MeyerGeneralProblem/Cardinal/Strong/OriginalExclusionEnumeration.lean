module

public import MeyerGeneralProblem.Cardinal.Strong.NestedOriginalParameterLimit

@[expose] public section

/-! An ordinary complete enumeration of every accepted original equation code. -/

namespace MeyerGeneralProblem.StrongParity

/-- The ordinary encodable sum of the four original equation-data shapes. -/
abbrev OriginalExclusionCodeData :=
  (ℤ × ℚ × ℚ) ⊕ ((ℤ × ℤ × ℚ × ℚ) ⊕ ((ℤ × ℤ × ℚ × ℚ) ⊕ (ℤ × ℕ × ℕ)))

/-- Pack the actual integer/rational original equation data into an ordinary encodable type. -/
def ComputedRootExclusion.pack : ComputedRootExclusion → OriginalExclusionCodeData
  | .root n u v => .inl (n, u, v)
  | .difference n l u v => .inr (.inl (n, l, u, v))
  | .sum n l u v => .inr (.inr (.inl (n, l, u, v)))
  | .fixed n y gamma => .inr (.inr (.inr (n, y, gamma)))

/-- Unpack the ordinary data into the exact original equation code. -/
def unpackOriginalExclusion : OriginalExclusionCodeData → ComputedRootExclusion
  | .inl (n, u, v) => .root n u v
  | .inr (.inl (n, l, u, v)) => .difference n l u v
  | .inr (.inr (.inl (n, l, u, v))) => .sum n l u v
  | .inr (.inr (.inr (n, y, gamma))) => .fixed n y gamma

/-- Packing and unpacking preserve EVERY actual original equation code. -/
theorem unpackOriginalExclusion_pack (code : ComputedRootExclusion) :
    unpackOriginalExclusion code.pack = code := by cases code <;> rfl

/-- Actual ordinary encodability of all four original equation data shapes. -/
instance ComputedRootExclusion.encodable : Encodable ComputedRootExclusion :=
  Encodable.ofLeftInverse ComputedRootExclusion.pack unpackOriginalExclusion unpackOriginalExclusion_pack

/-- The actual complete ordinary original equation enumeration, with ignored self-difference fallback. -/
def enumerateOriginalExclusions (k : ℕ) : ComputedRootExclusion :=
  (Encodable.decode k : Option ComputedRootExclusion).getD (.difference 0 0 0 0)

/-- Every literal original equation has a definite index in the actual implemented enumeration. -/
theorem enumerateOriginalExclusions_encode (code : ComputedRootExclusion) :
    enumerateOriginalExclusions (Encodable.encode code) = code := by
  simp only [enumerateOriginalExclusions, Encodable.encodek, Option.getD_some]

/-- The implemented ordinary enumeration covers ALL original equation codes. -/
theorem enumerateOriginalExclusions_surjective : Function.Surjective enumerateOriginalExclusions :=
  fun code => ⟨Encodable.encode code, enumerateOriginalExclusions_encode code⟩

/-- The actual ordinary all-equations original parameter-name program in any assigned slot. -/
def allOriginalExclusionsParameterName (names : ℕ → ℕ → ℚ)
    (hvalid : BinaryRationalNamesValid names) (m : ℕ) (hm : 0 < m)
    (initial : RationalParameterSlot) (p : ℕ) : ℚ :=
  nestedOriginalParameterName enumerateOriginalExclusions names hvalid m hm initial p

noncomputable section

/-- The actual real parameter constructed by the all-equations ordinary nested program. -/
def allOriginalExclusionsParameterValue (names : ℕ → ℕ → ℚ)
    (hvalid : BinaryRationalNamesValid names) (m : ℕ) (hm : 0 < m)
    (initial : RationalParameterSlot) : ℝ :=
  nestedOriginalParameterValue enumerateOriginalExclusions names hvalid m hm initial

/-- Every actual original equation, not merely a finite head, is avoided by the constructed parameter. -/
theorem allOriginalExclusionsParameterValue_avoids (names : ℕ → ℕ → ℚ)
    (hvalid : BinaryRationalNamesValid names) (m : ℕ) (hm : 0 < m)
    (initial : RationalParameterSlot) (values : ℕ → ℝ)
    (hname : ∀ i p, |(names i p : ℝ) - values i| ≤ 1 / (2 : ℝ) ^ p)
    (code : ComputedRootExclusion) :
    (code.semantic values).residual m (allOriginalExclusionsParameterValue names hvalid m hm initial) ≠ 0 := by
  have h := nestedOriginalParameterValue_avoids enumerateOriginalExclusions names hvalid m hm initial
    values hname (Encodable.encode code)
  simpa only [enumerateOriginalExclusions_encode, allOriginalExclusionsParameterValue] using h

/-- The actual complete-exclusion parameter has the implemented binary rational name. -/
theorem allOriginalExclusionsParameterName_error (names : ℕ → ℕ → ℚ)
    (hvalid : BinaryRationalNamesValid names) (m : ℕ) (hm : 0 < m)
    (initial : RationalParameterSlot) (p : ℕ) :
    |(allOriginalExclusionsParameterName names hvalid m hm initial p : ℝ) -
      allOriginalExclusionsParameterValue names hvalid m hm initial| ≤ 1 / (2 : ℝ) ^ p :=
  nestedOriginalParameterName_error enumerateOriginalExclusions names hvalid m hm initial p

/-- Every emitted name for the actual complete-exclusion parameter stays in the original domain. -/
theorem allOriginalExclusionsParameterName_range (names : ℕ → ℕ → ℚ)
    (hvalid : BinaryRationalNamesValid names) (m : ℕ) (hm : 0 < m)
    (initial : RationalParameterSlot) (p : ℕ) :
    0 ≤ allOriginalExclusionsParameterName names hvalid m hm initial p ∧
      allOriginalExclusionsParameterName names hvalid m hm initial p ≤ 1 / 2 :=
  nestedOriginalParameterName_range enumerateOriginalExclusions names hvalid m hm initial p

/-- The constructed complete-exclusion parameter is strictly inside its assigned slot. -/
theorem allOriginalExclusionsParameterValue_interior (names : ℕ → ℕ → ℚ)
    (hvalid : BinaryRationalNamesValid names) (m : ℕ) (hm : 0 < m)
    (initial : RationalParameterSlot) :
    (initial.lower : ℝ) < allOriginalExclusionsParameterValue names hvalid m hm initial ∧
      allOriginalExclusionsParameterValue names hvalid m hm initial < (initial.upper : ℝ) :=
  nestedOriginalParameterValue_interior enumerateOriginalExclusions names hvalid m hm initial

end

end MeyerGeneralProblem.StrongParity

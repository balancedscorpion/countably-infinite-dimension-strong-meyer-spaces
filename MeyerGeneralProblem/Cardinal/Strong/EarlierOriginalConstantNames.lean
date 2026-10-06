module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalParameterNameValidity
public import MeyerGeneralProblem.Cardinal.Strong.RationalNamedScaledRoot

@[expose] public section

/-! The complete ordinary dictionary of coarse values and signed EARLIER physical roots. -/

namespace MeyerGeneralProblem.StrongParity

/-- Dictionary data contain rational coarse coefficients or an earlier index, integer label and sign. -/
abbrev EarlierOriginalConstantData (i : ℕ) := (ℚ × ℚ) ⊕ (Fin i × ℤ × Bool)

/-- Evaluate actual dictionary data using only ordinary earlier parameter-name programs. -/
def earlierOriginalConstantNameData {i : ℕ} (scales : ℕ → ℕ)
    (earlier : Fin i → CertifiedOriginalParameterName) : EarlierOriginalConstantData i → ℕ → ℚ
  | .inl (u, v), p => rationalCoarseApprox u v p
  | .inr (j, n, negative), p =>
      let r := rationalNamedScaledOriginalRootApprox (earlier j).val (scales j.val) n p
      if negative then -r else r

/-- The complete computed prior dictionary; invalid decoding emits the valid zero name. -/
def earlierOriginalConstantNames {i : ℕ} (scales : ℕ → ℕ)
    (earlier : Fin i → CertifiedOriginalParameterName) (k p : ℕ) : ℚ :=
  match Encodable.decode (α := EarlierOriginalConstantData i) k with
  | none => 0
  | some data => earlierOriginalConstantNameData scales earlier data p

/-- Every coarse coefficient pair and signed prior root has a definite actual dictionary index. -/
theorem earlierOriginalConstantNames_encode {i : ℕ} (scales : ℕ → ℕ)
    (earlier : Fin i → CertifiedOriginalParameterName) (data : EarlierOriginalConstantData i) (p : ℕ) :
    earlierOriginalConstantNames scales earlier (Encodable.encode data) p =
      earlierOriginalConstantNameData scales earlier data p := by
  simp only [earlierOriginalConstantNames, Encodable.encodek]

noncomputable section

/-- The actual value of dictionary data uses the proved values of actual earlier parameter names. -/
def earlierOriginalConstantValueData {i : ℕ} (scales : ℕ → ℕ)
    (earlier : Fin i → CertifiedOriginalParameterName) : EarlierOriginalConstantData i → ℝ
  | .inl (u, v) => rationalCoarseValue u v
  | .inr (j, n, negative) =>
      let r := scaledCompactOriginalRoot (scales j.val) n (certifiedOriginalParameterValue (earlier j))
      if negative then -r else r

/-- Actual real semantics of the complete computed prior dictionary, including valid zero fallback. -/
def earlierOriginalConstantValues {i : ℕ} (scales : ℕ → ℕ)
    (earlier : Fin i → CertifiedOriginalParameterName) (k : ℕ) : ℝ :=
  match Encodable.decode (α := EarlierOriginalConstantData i) k with
  | none => 0
  | some data => earlierOriginalConstantValueData scales earlier data

/-- Every encoded actual dictionary value is exactly its intended coarse value or signed prior root. -/
theorem earlierOriginalConstantValues_encode {i : ℕ} (scales : ℕ → ℕ)
    (earlier : Fin i → CertifiedOriginalParameterName) (data : EarlierOriginalConstantData i) :
    earlierOriginalConstantValues scales earlier (Encodable.encode data) =
      earlierOriginalConstantValueData scales earlier data := by
  simp only [earlierOriginalConstantValues, Encodable.encodek]

/-- Each ordinary dictionary-data evaluator has proved actual binary error, including both root signs. -/
theorem earlierOriginalConstantNameData_error {i : ℕ} (scales : ℕ → ℕ)
    (earlier : Fin i → CertifiedOriginalParameterName) (data : EarlierOriginalConstantData i) (p : ℕ) :
    |(earlierOriginalConstantNameData scales earlier data p : ℝ) -
      earlierOriginalConstantValueData scales earlier data| ≤ 1 / (2 : ℝ) ^ p := by
  rcases data with ⟨u, v⟩ | ⟨j, n, negative⟩
  · exact rationalCoarseApprox_error u v p
  · have h := rationalNamedScaledOriginalRootApprox_error (earlier j).val (scales j.val) n
      (certifiedOriginalParameterValue_compact (earlier j)) (earlier j).property.1
      (certifiedOriginalParameterValue_error (earlier j)) p
    cases negative
    · exact h
    · simpa only [earlierOriginalConstantNameData, earlierOriginalConstantValueData,
        Bool.true_eq, ↓reduceIte, Rat.cast_neg, neg_sub_neg, abs_sub_comm] using h

/-- Every emitted computed prior constant has the proved binary error against its actual value. -/
theorem earlierOriginalConstantNames_error {i : ℕ} (scales : ℕ → ℕ)
    (earlier : Fin i → CertifiedOriginalParameterName) (k p : ℕ) :
    |(earlierOriginalConstantNames scales earlier k p : ℝ) -
      earlierOriginalConstantValues scales earlier k| ≤ 1 / (2 : ℝ) ^ p := by
  unfold earlierOriginalConstantNames earlierOriginalConstantValues
  cases h : Encodable.decode (α := EarlierOriginalConstantData i) k with
  | none => simp
  | some data => exact earlierOriginalConstantNameData_error scales earlier data p

/-- The complete prior dictionary supplies its own proof-only validity from constructed earlier names. -/
theorem earlierOriginalConstantNames_valid {i : ℕ} (scales : ℕ → ℕ)
    (earlier : Fin i → CertifiedOriginalParameterName) :
    BinaryRationalNamesValid (earlierOriginalConstantNames scales earlier) :=
  ⟨earlierOriginalConstantValues scales earlier, earlierOriginalConstantNames_error scales earlier⟩

end

end MeyerGeneralProblem.StrongParity

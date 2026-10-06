module

public import MeyerGeneralProblem.Cardinal.Strong.RationalHeadComparison
public import MeyerGeneralProblem.Cardinal.Strong.OriginalHeadLabels

@[expose] public section

/-! Executable enumeration of ALL original signed head labels. A finite natural
rectangle is filtered by the proved rational decision. Both signs are retained
and zero appears exactly once, through the original spectral label type. -/

namespace MeyerGeneralProblem.StrongParity

/-- Signed label equality uses only its two natural coordinates and sign. -/
instance originalSpectralLabel_decidableEq : DecidableEq spectralConeIndex := by
  unfold spectralConeIndex
  infer_instance

/-- The original smaller central head cutoff, computed exactly as a rational. -/
def originalHeadRationalCutoff (s : ℕ) : ℚ := (s / 2 : ℕ) / (2 : ℚ)

/-- Complete finite natural rectangle containing every possible original head coordinate. -/
def originalHeadCandidatePairs (s : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (s + 1)).product (Finset.range (s + 1))

/-- An ordinary upper label with the original named spectral type. -/
def originalUpperSpectralLabel (p : ℕ × ℕ) : spectralConeIndex := Sum.inl p

/-- An ordinary lower label with zero excluded by the original label type. -/
def originalLowerSpectralLabel (p : {p : ℕ × ℕ // p ≠ (0, 0)}) : spectralConeIndex := Sum.inr p

/-- Both signed copies of that rectangle, with the negative zero omitted. -/
def originalHeadCandidateLabels (s : ℕ) : Finset spectralConeIndex :=
  (originalHeadCandidatePairs s).image originalUpperSpectralLabel ∪
    ((originalHeadCandidatePairs s).filter (fun p => p ≠ (0, 0))).attach.image
      (fun p => originalLowerSpectralLabel (⟨p.val, (Finset.mem_filter.mp (show p.val ∈ (originalHeadCandidatePairs s).filter (fun q : ℕ × ℕ => q ≠ (0, 0)) from p.property)).2⟩ :
        {q : ℕ × ℕ // q ≠ (0, 0)}))

/-- The ordinary complete signed head test, using the same positive magnitude for either sign. -/
def rationalOriginalSignedHeadTest (s : ℕ) : spectralConeIndex → Bool
  | .inl p => rationalHeadContains p.1 p.2 (originalHeadRationalCutoff s)
  | .inr p => rationalHeadContains p.val.1 p.val.2 (originalHeadRationalCutoff s)

/-- The implemented complete original head enumeration, containing no supplied head mask. -/
def computedOriginalSignedHeadLabels (s : ℕ) : Finset spectralConeIndex :=
  (originalHeadCandidateLabels s).filter (fun p => rationalOriginalSignedHeadTest s p = true)

noncomputable section

/-- The rational cutoff is precisely the original real cutoff floor(s/2)/2. -/
theorem originalHeadRationalCutoff_cast (s : ℕ) :
    (originalHeadRationalCutoff s : ℝ) = ((s / 2 : ℕ) : ℝ) / 2 := by
  simp [originalHeadRationalCutoff]

/-- Literal membership of an upper candidate retains the full natural rectangle. -/
theorem mem_originalHeadCandidateLabels_positive (s : ℕ) (p : ℕ × ℕ) :
    originalUpperSpectralLabel p ∈ originalHeadCandidateLabels s ↔ p.1 ≤ s ∧ p.2 ≤ s := by
  unfold originalHeadCandidateLabels
  rw [Finset.mem_union]
  simp only [Finset.mem_image]
  constructor
  · rintro (⟨q, hq, heq⟩ | ⟨q, hq, heq⟩)
    · cases heq
      simpa [originalHeadCandidatePairs] using hq
    · cases heq
  · intro hp
    exact Or.inl ⟨p, by simpa [originalHeadCandidatePairs] using hp, rfl⟩

/-- Literal membership of a lower candidate retains all nonzero natural labels in the rectangle. -/
theorem mem_originalHeadCandidateLabels_negative (s : ℕ) (p : {p : ℕ × ℕ // p ≠ (0, 0)}) :
    originalLowerSpectralLabel p ∈ originalHeadCandidateLabels s ↔ p.val.1 ≤ s ∧ p.val.2 ≤ s := by
  unfold originalHeadCandidateLabels
  rw [Finset.mem_union]
  simp only [Finset.mem_image]
  constructor
  · rintro (⟨q, hq, heq⟩ | ⟨q, hq, heq⟩)
    · cases heq
    · have hval : q.val = p.val := congrArg (fun x => x.val) (Sum.inr.inj heq)
      have hm := (Finset.mem_filter.mp q.property).1
      rw [hval] at hm
      simpa [originalHeadCandidatePairs] using hm
  · intro hp
    have hm : p.val ∈ (originalHeadCandidatePairs s).filter (fun q => q ≠ (0, 0)) :=
      Finset.mem_filter.mpr ⟨by simpa [originalHeadCandidatePairs] using hp, p.property⟩
    exact Or.inr ⟨⟨p.val, hm⟩, Finset.mem_attach _ _, rfl⟩

/-- Every actual head label is inside the finite computed candidate rectangle. -/
theorem actualOriginalHeadLabel_mem_candidates (s : ℕ) (p : spectralConeIndex)
    (hp : |spectralConeIndexFrequency p| ≤ ((s / 2 : ℕ) : ℝ) / 2) :
    p ∈ originalHeadCandidateLabels s := by
  have hb := productOriginalHeadCoordinates_bound s ⟨p, hp⟩
  have hhalf : ((s / 2 : ℕ) : ℝ) ≤ (s : ℝ) := by exact_mod_cast Nat.div_le_self s 2
  have hnonneg : (0 : ℝ) ≤ ((s / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hcoords : (spectralConeIndexCoordinates p).1 ≤ s ∧ (spectralConeIndexCoordinates p).2 ≤ s := by
    constructor
    · exact_mod_cast (by linarith :
        ((spectralConeIndexCoordinates p).1 : ℝ) ≤ (s : ℝ))
    · exact_mod_cast (by linarith :
        ((spectralConeIndexCoordinates p).2 : ℝ) ≤ (s : ℝ))
  cases p with
  | inl p => exact (mem_originalHeadCandidateLabels_positive s p).mpr hcoords
  | inr p => exact (mem_originalHeadCandidateLabels_negative s p).mpr hcoords

/-- The implemented signed Boolean decision matches the exact original head inequality. -/
theorem rationalOriginalSignedHeadTest_iff (s : ℕ) (p : spectralConeIndex) :
    rationalOriginalSignedHeadTest s p = true ↔
      |spectralConeIndexFrequency p| ≤ ((s / 2 : ℕ) : ℝ) / 2 := by
  cases p with
  | inl p =>
    simpa only [rationalOriginalSignedHeadTest, spectralConeIndexFrequency,
      abs_of_nonneg (positiveConeFrequency_nonneg p), originalHeadRationalCutoff_cast] using
      rationalHeadContains_iff p.1 p.2 (originalHeadRationalCutoff s)
  | inr p =>
    simpa only [rationalOriginalSignedHeadTest, spectralConeIndexFrequency, abs_neg,
      abs_of_nonneg (positiveConeFrequency_nonneg p.val), originalHeadRationalCutoff_cast] using
      rationalHeadContains_iff p.val.1 p.val.2 (originalHeadRationalCutoff s)

/-- The ordinary finite output enumerates EVERY actual signed head label and no others. -/
theorem mem_computedOriginalSignedHeadLabels_iff (s : ℕ) (p : spectralConeIndex) :
    p ∈ computedOriginalSignedHeadLabels s ↔
      |spectralConeIndexFrequency p| ≤ ((s / 2 : ℕ) : ℝ) / 2 := by
  rw [computedOriginalSignedHeadLabels, Finset.mem_filter, rationalOriginalSignedHeadTest_iff]
  exact ⟨fun h => h.2, fun h => ⟨actualOriginalHeadLabel_mem_candidates s p h, h⟩⟩

end

end MeyerGeneralProblem.StrongParity

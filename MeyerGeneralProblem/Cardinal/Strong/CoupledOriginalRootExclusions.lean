module

public import MeyerGeneralProblem.Cardinal.Strong.CoupledOriginalParameterNames

@[expose] public section

/-! Whole-family original root, difference and sum exclusions from the actual recursive program. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- The actual physical original root of each constructed coupled sheet and integer label. -/
def coupledOriginalPhysicalRoot (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (slots : ℕ → RationalParameterSlot) (i : ℕ) (n : ℤ) : ℝ :=
  scaledCompactOriginalRoot (scales i) n (coupledOriginalParameterValue scales hpos slots i)

/-- Zero belongs to the full rational coarse module. -/
theorem zero_mem_parityRationalCoarseModule : (0 : ℝ) ∈ parityRationalCoarseModule :=
  ⟨0, 0, by simp⟩

/-- The full rational coarse module is closed under negation. -/
theorem neg_mem_parityRationalCoarseModule {x : ℝ} (h : x ∈ parityRationalCoarseModule) :
    -x ∈ parityRationalCoarseModule := by
  rcases h with ⟨u, v, rfl⟩
  refine ⟨-u, -v, ?_⟩
  push_cast
  ring

/-- Every actual root of EVERY constructed sheet avoids the full rational coarse module. -/
theorem coupledOriginalPhysicalRoot_not_mem (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (slots : ℕ → RationalParameterSlot) (i : ℕ) (n : ℤ) :
    coupledOriginalPhysicalRoot scales hpos slots i n ∉ parityRationalCoarseModule := by
  rintro ⟨u, v, he⟩
  have hn := coupledOriginalParameterValue_avoids scales hpos slots i (.root n u v)
  simp only [ComputedRootExclusion.semantic, OriginalRootExclusion.residual, sub_ne_zero] at hn
  exact hn he

/-- Every distinct-label difference on any constructed sheet avoids the full rational coarse module. -/
theorem coupledOriginalPhysicalRoot_same_difference_not_mem (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (slots : ℕ → RationalParameterSlot) (i : ℕ) (n l : ℤ) (hnl : n ≠ l) :
    coupledOriginalPhysicalRoot scales hpos slots i n -
      coupledOriginalPhysicalRoot scales hpos slots i l ∉ parityRationalCoarseModule := by
  rintro ⟨u, v, he⟩
  have hn := coupledOriginalParameterValue_avoids scales hpos slots i (.difference n l u v)
  simp only [ComputedRootExclusion.semantic, OriginalRootExclusion.residual, ite_eq_right hnl,
    sub_ne_zero] at hn
  exact hn he

/-- Every same-sheet sum, including self-sums, avoids the full rational coarse module. -/
theorem coupledOriginalPhysicalRoot_same_sum_not_mem (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (slots : ℕ → RationalParameterSlot) (i : ℕ) (n l : ℤ) :
    coupledOriginalPhysicalRoot scales hpos slots i n +
      coupledOriginalPhysicalRoot scales hpos slots i l ∉ parityRationalCoarseModule := by
  rintro ⟨u, v, he⟩
  have hn := coupledOriginalParameterValue_avoids scales hpos slots i (.sum n l u v)
  simp only [ComputedRootExclusion.semantic, OriginalRootExclusion.residual, sub_ne_zero] at hn
  exact hn he

/-- Negative earlier-root dictionary entries pay every cross-sheet original difference exclusion. -/
theorem coupledOriginalPhysicalRoot_earlier_difference_not_mem (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (slots : ℕ → RationalParameterSlot) (i j : ℕ) (hji : j < i)
    (n l : ℤ) : coupledOriginalPhysicalRoot scales hpos slots i n -
      coupledOriginalPhysicalRoot scales hpos slots j l ∉ parityRationalCoarseModule := by
  rintro ⟨u, v, he⟩
  let y : EarlierOriginalConstantData i := .inr (⟨j, hji⟩, l, true)
  let gamma : EarlierOriginalConstantData i := .inl (u, v)
  have hn := coupledOriginalParameterValue_avoids scales hpos slots i
    (.fixed n (Encodable.encode y) (Encodable.encode gamma))
  simp only [ComputedRootExclusion.semantic, OriginalRootExclusion.residual,
    earlierOriginalConstantValues_encode, earlierOriginalConstantValueData, y, gamma,
    ↓reduceIte, sub_ne_zero, ← sub_eq_add_neg] at hn
  exact hn he

/-- Positive earlier-root dictionary entries pay every cross-sheet original sum exclusion. -/
theorem coupledOriginalPhysicalRoot_earlier_sum_not_mem (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (slots : ℕ → RationalParameterSlot) (i j : ℕ) (hji : j < i)
    (n l : ℤ) : coupledOriginalPhysicalRoot scales hpos slots i n +
      coupledOriginalPhysicalRoot scales hpos slots j l ∉ parityRationalCoarseModule := by
  rintro ⟨u, v, he⟩
  let y : EarlierOriginalConstantData i := .inr (⟨j, hji⟩, l, false)
  let gamma : EarlierOriginalConstantData i := .inl (u, v)
  have hn := coupledOriginalParameterValue_avoids scales hpos slots i
    (.fixed n (Encodable.encode y) (Encodable.encode gamma))
  simp only [ComputedRootExclusion.semantic, OriginalRootExclusion.residual,
    earlierOriginalConstantValues_encode, earlierOriginalConstantValueData, y, gamma,
    Bool.false_eq, sub_ne_zero] at hn
  exact hn he

/-- EVERY distinct indexed root pair across the WHOLE constructed family avoids Gamma_Q in difference. -/
theorem coupledOriginalPhysicalRoot_difference_not_mem (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (slots : ℕ → RationalParameterSlot) (i j : ℕ) (n l : ℤ)
    (hdistinct : (i, n) ≠ (j, l)) :
    coupledOriginalPhysicalRoot scales hpos slots i n -
      coupledOriginalPhysicalRoot scales hpos slots j l ∉ parityRationalCoarseModule := by
  rcases lt_trichotomy j i with hji | hji | hij
  · exact coupledOriginalPhysicalRoot_earlier_difference_not_mem scales hpos slots i j hji n l
  · subst j
    apply coupledOriginalPhysicalRoot_same_difference_not_mem scales hpos slots i n l
    intro he
    exact hdistinct (by simp [he])
  · intro h
    apply coupledOriginalPhysicalRoot_earlier_difference_not_mem scales hpos slots j i hij l n
    have hh := neg_mem_parityRationalCoarseModule h
    convert hh using 1; ring

/-- EVERY root sum across the WHOLE actual family, including every self-sum, avoids Gamma_Q. -/
theorem coupledOriginalPhysicalRoot_sum_not_mem (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (slots : ℕ → RationalParameterSlot) (i j : ℕ) (n l : ℤ) :
    coupledOriginalPhysicalRoot scales hpos slots i n +
      coupledOriginalPhysicalRoot scales hpos slots j l ∉ parityRationalCoarseModule := by
  rcases lt_trichotomy j i with hji | hji | hij
  · exact coupledOriginalPhysicalRoot_earlier_sum_not_mem scales hpos slots i j hji n l
  · subst j
    exact coupledOriginalPhysicalRoot_same_sum_not_mem scales hpos slots i n l
  · simpa only [add_comm] using
      coupledOriginalPhysicalRoot_earlier_sum_not_mem scales hpos slots j i hij l n

/-- The actual indexed physical roots are injective over ALL sheets and ALL integer labels. -/
theorem coupledOriginalPhysicalRoot_injective (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (slots : ℕ → RationalParameterSlot) :
    Function.Injective (fun z : ℕ × ℤ => coupledOriginalPhysicalRoot scales hpos slots z.1 z.2) := by
  rintro ⟨i, n⟩ ⟨j, l⟩ he
  change coupledOriginalPhysicalRoot scales hpos slots i n =
    coupledOriginalPhysicalRoot scales hpos slots j l at he
  by_contra hne
  have hn := coupledOriginalPhysicalRoot_difference_not_mem scales hpos slots i j n l hne
  rw [he, sub_self] at hn
  exact hn zero_mem_parityRationalCoarseModule

/-- No two actual original physical roots can be reflections, including the same root. -/
theorem coupledOriginalPhysicalRoot_ne_neg (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (slots : ℕ → RationalParameterSlot) (i j : ℕ) (n l : ℤ) :
    coupledOriginalPhysicalRoot scales hpos slots i n ≠
      -coupledOriginalPhysicalRoot scales hpos slots j l := by
  intro he
  have hn := coupledOriginalPhysicalRoot_sum_not_mem scales hpos slots i j n l
  rw [he, neg_add_cancel] at hn
  exact hn zero_mem_parityRationalCoarseModule

end

end MeyerGeneralProblem.StrongParity

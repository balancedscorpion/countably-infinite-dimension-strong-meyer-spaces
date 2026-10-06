module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalStrongNoReturn
public import MeyerGeneralProblem.Distribution.StrongFiniteSymbolProducts
public import MeyerGeneralProblem.Distribution.OriginalStrongFourierSquare

@[expose] public section

/-! Whole-carrier geometry of the actual positive native finite shifts.
All translated axes, repeated frequencies and finite-product convolution
containers lie in internally computed complete two-quadrant carriers. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section
open scoped FourierTransform

/-- Literal positive native frequencies of a finite polynomial at an ordinary geometric scale. -/
def originalPositivePolynomialFrequency {ι : Type*} (scale : ℝ) (p : ι → ℕ × ℕ) (i : ι) : ℝ :=
  positiveConeFrequency (p i) / scale

/-- The complete native cone is exactly the previously implemented two signed quadrants. -/
theorem translatedConeFrequency_zero (z : Bool × (ℕ × ℕ)) :
    translatedConeFrequency 0 0 z = signedConeFrequency z := by
  unfold translatedConeFrequency translatedConeVertex signedConeFrequency
  norm_num

theorem translatedConeSet_zero : translatedConeSet 0 0 = spectralConeSet := by
  unfold translatedConeSet spectralConeSet
  congr 1
  exact funext translatedConeFrequency_zero

/-- Negation preserves the WHOLE native cone, including its axes and zero. -/
theorem scaledTranslatedConeCarrier_zero_reflect (scale : ℝ) (hs : 0 < scale) :
    (scaledTranslatedConeCarrier 0 0 scale hs).reflect =
      scaledTranslatedConeCarrier 0 0 scale hs := by
  apply LocallyFiniteCarrier.ext
  have hneg : ∀ x ∈ (scaledTranslatedConeCarrier 0 0 scale hs).carrier,
      -x ∈ (scaledTranslatedConeCarrier 0 0 scale hs).carrier := by
    intro x hx
    obtain ⟨y, ⟨z, rfl⟩, he⟩ := hx
    refine ⟨translatedConeFrequency 0 0 (!z.1, z.2), ⟨(!z.1, z.2), rfl⟩, ?_⟩
    rw [← he]
    have hz : translatedConeFrequency 0 0 (!z.1, z.2) =
        -translatedConeFrequency 0 0 z := by
      rw [translatedConeFrequency_zero, translatedConeFrequency_zero]
      cases hz : z.1 <;> simp [signedConeFrequency, hz]
    rw [hz]
    ring
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hneg y hy
  · intro hx
    exact ⟨-x, hneg x hx, neg_neg x⟩

/-- Increasing the reflected vertex preserves every original translated-cone point. -/
theorem translatedConeSet_mono {A B D E : ℤ} (hA : A ≤ D) (hB : B ≤ E) :
    translatedConeSet A B ⊆ translatedConeSet D E := by
  intro x hx
  obtain ⟨p, q, he, hpq⟩ := (translatedConeSet_iff A B x).mp hx
  apply (translatedConeSet_iff D E x).mpr
  refine ⟨p, q, he, ?_⟩
  rcases hpq with hpq | hpq
  · exact Or.inl hpq
  · exact Or.inr ⟨hpq.1.trans hA, hpq.2.trans hB⟩

theorem scaledTranslatedConeCarrier_mono {A B D E : ℤ} (hA : A ≤ D) (hB : B ≤ E)
    (scale : ℝ) (hs : 0 < scale) :
    (scaledTranslatedConeCarrier A B scale hs).carrier ⊆
      (scaledTranslatedConeCarrier D E scale hs).carrier := by
  rintro x ⟨y, hy, rfl⟩
  exact ⟨y, translatedConeSet_mono hA hB hy, rfl⟩

/-- Positive native shifts retain the entire positive quadrant and move only the reflected vertex. -/
theorem scaledTranslatedConeCarrier_positive_shift (A B : ℤ) (scale : ℝ) (hs : 0 < scale)
    (p : ℕ × ℕ) (x : ℝ) (hx : x ∈ (scaledTranslatedConeCarrier A B scale hs).carrier) :
    positiveConeFrequency p / scale + x ∈
      (scaledTranslatedConeCarrier (A + p.1) (B + p.2) scale hs).carrier := by
  obtain ⟨y, ⟨z, rfl⟩, he⟩ := hx
  have hfreq : positiveConeFrequency p + translatedConeFrequency A B z ∈
      translatedConeSet (A + p.1) (B + p.2) := by
    by_cases hz : z.1 = true
    · refine ⟨(true, z.2), ?_⟩
      simp only [translatedConeFrequency, hz, ↓reduceIte, translatedConeVertex,
        Int.cast_add, Int.cast_natCast, positiveConeFrequency]
      ring
    · refine ⟨(false, (p.1 + z.2.1, p.2 + z.2.2)), ?_⟩
      simp only [translatedConeFrequency, hz, Bool.false_eq_true, ↓reduceIte,
        positiveConeFrequency, Nat.cast_add]
      ring
  refine ⟨positiveConeFrequency p + translatedConeFrequency A B z, hfreq, ?_⟩
  rw [← he]
  simp only [div_eq_mul_inv]
  ring

/-- Ordinary finite positive-coordinate budgets, not assumed envelope certificates. -/
def originalPositivePolynomialBudget {ι : Type*} [Fintype ι] (p : ι → ℕ × ℕ) : ℕ × ℕ :=
  (∑ i, (p i).1, ∑ i, (p i).2)

/-- The full finite convolution container has an internally computed complete translated cone. -/
theorem finiteCombConvolutionCarrier_positive_cone_subset {ι : Type*} [Fintype ι]
    (A B : ℤ) (scale : ℝ) (hs : 0 < scale) (p : ι → ℕ × ℕ) :
    (finiteCombConvolutionCarrier (scaledTranslatedConeCarrier A B scale hs)
      (originalPositivePolynomialFrequency scale p)).carrier ⊆
      (scaledTranslatedConeCarrier (A + (originalPositivePolynomialBudget p).1)
        (B + (originalPositivePolynomialBudget p).2) scale hs).carrier := by
  intro x hx
  obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
  have hi := scaledTranslatedConeCarrier_positive_shift A B scale hs (p i) y hy
  apply scaledTranslatedConeCarrier_mono (scale := scale) (hs := hs) _ _ hi
  · have h : (p i).1 ≤ ∑ j, (p j).1 := Finset.single_le_sum (f := fun j => (p j).1)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hI : ((p i).1 : ℤ) ≤ ((∑ j, (p j).1 : ℕ) : ℤ) := by exact_mod_cast h
    simpa only [originalPositivePolynomialBudget, add_comm] using add_le_add_left hI A
  · have h : (p i).2 ≤ ∑ j, (p j).2 := Finset.single_le_sum (f := fun j => (p j).2)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hI : ((p i).2 : ℤ) ≤ ((∑ j, (p j).2 : ℕ) : ℤ) := by exact_mod_cast h
    simpa only [originalPositivePolynomialBudget, add_comm] using add_le_add_left hI B

/-- Every nested genuine product-convolution support has its explicit whole-cone coordinate bound. -/
theorem finiteTranslatedSymbolProductFourierCarrier_positive_cone_subset {ι : Type*} [Fintype ι]
    (scale : ℝ) (hs : 0 < scale) (p : ι → ℕ × ℕ) (r : List ℝ) :
    (finiteTranslatedSymbolProductFourierCarrier (scaledTranslatedConeCarrier 0 0 scale hs)
      (originalPositivePolynomialFrequency scale p) r).carrier ⊆
      (scaledTranslatedConeCarrier ((r.length : ℤ) * (originalPositivePolynomialBudget p).1)
        ((r.length : ℤ) * (originalPositivePolynomialBudget p).2) scale hs).carrier := by
  induction r with
  | nil => simpa only [finiteTranslatedSymbolProductFourierCarrier, List.foldr_nil,
      List.length_nil, Nat.cast_zero, zero_mul] using (Set.Subset.refl
        (scaledTranslatedConeCarrier 0 0 scale hs).carrier)
  | cons s r ih =>
    intro x hx
    obtain ⟨i, y, hy, he⟩ := Set.mem_iUnion.mp hx
    have hx' : x ∈ (finiteCombConvolutionCarrier
        (scaledTranslatedConeCarrier ((r.length : ℤ) * (originalPositivePolynomialBudget p).1)
          ((r.length : ℤ) * (originalPositivePolynomialBudget p).2) scale hs)
        (originalPositivePolynomialFrequency scale p)).carrier :=
      Set.mem_iUnion.mpr ⟨i, y, ih hy, he⟩
    have h := finiteCombConvolutionCarrier_positive_cone_subset
      ((r.length : ℤ) * (originalPositivePolynomialBudget p).1)
      ((r.length : ℤ) * (originalPositivePolynomialBudget p).2) scale hs p hx'
    simpa only [List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using h

end
end MeyerGeneralProblem.StrongParity

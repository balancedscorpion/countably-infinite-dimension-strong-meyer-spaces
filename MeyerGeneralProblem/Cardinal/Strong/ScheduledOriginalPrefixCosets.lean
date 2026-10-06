module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalPrefixSourceRecovery
public import MeyerGeneralProblem.Distribution.SingletonModuleCoset
public import MeyerGeneralProblem.Distribution.OriginalStrongFourierSquare

@[expose] public section

/-! Actual whole-prefix reflected root geometry. Every distinct root difference
avoids the full rational module; the complete common cone is symmetric. Thus
each reflected root has a singleton coset for the actual integer module. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- The WHOLE actual common cone is symmetric, including both axes and zero. -/
theorem originalScheduledPrefixCone_neg_iff (bound : ℕ → ℕ) (k : ℕ) (x : ℝ) :
    -x ∈ (originalScheduledPrefixCone bound k).carrier ↔
      x ∈ (originalScheduledPrefixCone bound k).carrier := by
  have h (y : ℝ) (hy : y ∈ (originalScheduledPrefixCone bound k).carrier) :
      -y ∈ (originalScheduledPrefixCone bound k).carrier := by
    obtain ⟨z, hz, rfl⟩ := hy
    refine ⟨-z, ?_, ?_⟩
    · change -z ∈ translatedConeSet 0 0
      rw [translatedConeSet_zero, originalSpectralConeSet_neg_iff]
      change z ∈ translatedConeSet 0 0 at hz
      rwa [translatedConeSet_zero] at hz
    · ring
  exact ⟨fun hx => by simpa only [neg_neg] using h (-x) hx, h x⟩

/-- Every distinct pair of FULL actual prefix roots avoids the rational module in difference. -/
theorem originalScheduledPrefixRootSet_difference_not_mem (bound : ℕ → ℕ) (k : ℕ)
    (x y : ℝ) (hx : x ∈ originalScheduledPrefixRootSet bound k)
    (hy : y ∈ originalScheduledPrefixRootSet bound k) (hxy : x ≠ y) :
    x - y ∉ parityRationalCoarseModule := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
  obtain ⟨a, n, rfl⟩ := (originalScheduledFullPhysicalCarrier_iff_label bound i.val x).mp hi
  obtain ⟨b, m, rfl⟩ := (originalScheduledFullPhysicalCarrier_iff_label bound j.val y).mp hj
  apply originalScheduledPhysicalRoot_difference_not_mem
  intro he
  exact hxy (congrArg (originalScheduledPhysicalRoot bound) he)

/-- A reflected complete root still avoids the whole actual integer module. -/
theorem originalScheduledPrefixReflectedRoot_not_mem_module (bound : ℕ → ℕ) (k : ℕ)
    (x : ℝ) (hx : x ∈ (originalScheduledPrefixFullRootCarrier bound k).reflect.carrier) :
    x ∉ originalScheduledPrefixModuleSet bound k := by
  obtain ⟨y, hy, rfl⟩ := hx
  intro hm
  have hq := neg_mem_parityRationalCoarseModule
    (originalScheduledPrefixModuleSet_subset_rational_module bound k hm)
  rw [neg_neg] at hq
  exact originalScheduledPrefixRootSet_not_mem_module bound k y hy hq

/-- Each actual reflected root has a singleton integer-module coset in the
WHOLE reflected-root/cone carrier, with every allowed zero point retained. -/
theorem originalScheduledPrefixReflectedRoot_singleton_coset (bound : ℕ → ℕ) (k : ℕ)
    (x : ℝ) (hx : x ∈ (originalScheduledPrefixFullRootCarrier bound k).reflect.carrier)
    (y : ℝ) (hy : y ∈ ((originalScheduledPrefixFullRootCarrier bound k).reflect.union
      (originalScheduledPrefixCone bound k)).carrier)
    (hxy : x - y ∈ originalScheduledPrefixModuleSet bound k) : y = x := by
  rcases hy with hy | hy
  · obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    by_contra hne
    apply originalScheduledPrefixRootSet_difference_not_mem bound k b a hb ha
      (fun h => hne (congrArg Neg.neg h))
    convert! originalScheduledPrefixModuleSet_subset_rational_module bound k hxy using 1
    ring
  · obtain ⟨z, hz⟩ := hxy
    obtain ⟨w, hw⟩ := originalScheduledPrefixCone_subset_module bound k hy
    apply False.elim
    apply originalScheduledPrefixReflectedRoot_not_mem_module bound k x hx
    refine ⟨z + w, ?_⟩
    rw [map_add, hz, hw]
    ring

/-- All ACTUAL shifts of the complete native polynomial motif are distinct. -/
theorem originalScheduledPrefixMotifFrequency_injective (bound : ℕ → ℕ) (k : ℕ) :
    Function.Injective (fun i : OriginalScheduledPrefixMotif bound k =>
      originalScaledModuleFrequencyHom (originalPrivateScale (originalScheduledPrefixDenominator bound k))
        (originalPositivePolynomialIntegerCoordinates (originalScheduledPrefixPolynomialCoordinates bound k) i)) := by
  intro i j he
  have he' := originalScaledModuleFrequencyHom_injective _
    (originalPrivateScale_pos _ (originalScheduledPrefixDenominator_pos bound k)).ne' he
  apply Subtype.ext
  exact originalNativeIntegerEmbedding.injective he'

/-- Every ACTUAL coefficient in the complete support motif is nonzero. -/
theorem originalScheduledPrefixMotifCoefficient_ne_zero (bound : ℕ → ℕ) (k : ℕ)
    (i : OriginalScheduledPrefixMotif bound k) : originalScheduledPrefixPolynomialCoefficient bound k i ≠ 0 :=
  Finsupp.mem_support_iff.mp i.property

end
end MeyerGeneralProblem.StrongParity

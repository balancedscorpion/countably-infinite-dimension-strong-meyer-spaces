module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalBlocks
public import MeyerGeneralProblem.Distribution.EscapingCombCarriers
public import MeyerGeneralProblem.Distribution.RestrictedAtomicRows
public import MeyerGeneralProblem.Cardinal.StrongFiltration

@[expose] public section

/-!
# Whole locally finite scheduled common carrier and original source admission

Natural windows are internally enlarged by the block index. The ENTIRE allowed
physical carrier and ENTIRE allowed spectral carrier of each scheduled private
block are retained, including every extra allowed zero-coefficient point and
the fixed shared coarse cone. Original weighted-TV admission is transported by
actual zero-padding. Complete mixed-prefix and infinite exhaustion remain unpaid.
-/

namespace MeyerGeneralProblem.StrongParity

/-- Ordinary windows also include the block index, ensuring escape for all future blocks. -/
def originalCommonWindowBounds (bound : ℕ → ℕ) (n : ℕ) : ℕ := max (bound n) n

noncomputable section

/-- The full scheduled private physical carrier is contained in its whole undeleted block. -/
theorem originalScheduledPrivatePhysicalCarrier_subset_full (bound : ℕ → ℕ) (n : ℕ) :
    (originalScheduledPrivatePhysicalCarrier bound n).carrier ⊆
      (originalScheduledFullPhysicalCarrier bound n).carrier := Set.sdiff_subset

/-- ALL noncoarse allowed spectral points escape the literal protected head. -/
theorem originalScheduledPrivateSpectralCarrier_noncoarse_escape (bound : ℕ → ℕ) (n : ℕ) {x : ℝ}
    (hx : x ∈ ((originalScheduledPrivateSpectralCarrier bound n).delete originalSharedCoarseCone.carrier).carrier) :
    (bound n : ℝ) + 1 < |x| := by
  change (x ∈ (originalPrivateSpectralCone (originalReflectedPrimeSchedule bound n)
      (originalScheduledBlockPrime_pos bound n)).carrier ∧
    x ∉ originalPrivateGeometricHead (originalReflectedOrderSchedule bound n)
      (originalReflectedPrimeSchedule bound n)) ∧ x ∉ originalSharedCoarseCone.carrier at hx
  have hr : originalPrivateBlockHeadRadius (originalReflectedWindowBounds bound) n < |x| := by
    apply lt_of_not_ge
    intro hsmall
    exact hx.1.2 ⟨hsmall, hx.2⟩
  exact (originalReflectedSchedule_escape bound n).1.trans_lt hr

/-- The complete escaping part of a block, retaining all private physical and noncoarse spectral points. -/
def originalScheduledEscapingBlock (bound : ℕ → ℕ) (n : ℕ) : LocallyFiniteCarrier :=
  (originalScheduledPrivatePhysicalCarrier (originalCommonWindowBounds bound) n).union
    ((originalScheduledPrivateSpectralCarrier (originalCommonWindowBounds bound) n).delete
      originalSharedCoarseCone.carrier)

/-- EVERY allowed point of an entire future block escapes beyond its index. -/
theorem originalScheduledEscapingBlock_gap (bound : ℕ → ℕ) (n : ℕ) {x : ℝ}
    (hx : x ∈ (originalScheduledEscapingBlock bound n).carrier) : (n : ℝ) + 1 < |x| := by
  have hidx : (n : ℝ) ≤ (originalCommonWindowBounds bound n : ℝ) := by
    exact_mod_cast le_max_right (bound n) n
  have hgap : (originalCommonWindowBounds bound n : ℝ) + 1 < |x| := by
    rcases hx with hx | hx
    · exact originalScheduledFullPhysicalCarrier_escape _ _
        (originalScheduledPrivatePhysicalCarrier_subset_full _ _ hx)
    · exact originalScheduledPrivateSpectralCarrier_noncoarse_escape _ _ hx
  linarith

/-- Complete blocks eventually miss EVERY compact interval, with the escape proof supplied internally. -/
theorem originalScheduledEscapingBlock_escape (bound : ℕ → ℕ) :
    ∀ a b : ℝ, ∃ N : ℕ, ∀ n, N ≤ n →
      (originalScheduledEscapingBlock bound n).carrier ∩ Set.Icc a b = ∅ := by
  apply escaping_inter_Icc_of_symmetric
  intro R
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt R
  refine ⟨N, ?_⟩
  intro n hn
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hx, hxl, hxr⟩
  have hgap := originalScheduledEscapingBlock_gap bound n hx
  have hle : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsmall := abs_le.mpr ⟨hxl, hxr⟩
  linarith

/-- The ENTIRE locally finite common carrier; no local-finiteness or exhaustion certificate is an input. -/
def originalScheduledCommonCarrier (bound : ℕ → ℕ) : LocallyFiniteCarrier :=
  originalSharedCoarseCone.union (LocallyFiniteCarrier.escapingUnion
    (originalScheduledEscapingBlock bound) (originalScheduledEscapingBlock_escape bound))

/-- Whole-carrier equality retains EVERY allowed point of BOTH records of EVERY block. -/
theorem originalScheduledCommonCarrier_carrier (bound : ℕ → ℕ) :
    (originalScheduledCommonCarrier bound).carrier = originalSharedCoarseCone.carrier ∪
      ⋃ n : ℕ, ((originalScheduledPrivatePhysicalCarrier (originalCommonWindowBounds bound) n).carrier ∪
        (originalScheduledPrivateSpectralCarrier (originalCommonWindowBounds bound) n).carrier) := by
  ext x
  change (x ∈ originalSharedCoarseCone.carrier ∨
    x ∈ ⋃ n : ℕ, ((originalScheduledPrivatePhysicalCarrier (originalCommonWindowBounds bound) n).carrier ∪
      ((originalScheduledPrivateSpectralCarrier (originalCommonWindowBounds bound) n).carrier \
        originalSharedCoarseCone.carrier))) ↔ _
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_sdiff]
  constructor
  · rintro (hc | ⟨n, hx⟩)
    · exact Or.inl hc
    · exact Or.inr ⟨n, hx.elim Or.inl (fun h => Or.inr h.1)⟩
  · rintro (hc | ⟨n, hx⟩)
    · exact Or.inl hc
    · by_cases hc : x ∈ originalSharedCoarseCone.carrier
      · exact Or.inl hc
      · exact Or.inr ⟨n, hx.elim Or.inl (fun h => Or.inr ⟨h, hc⟩)⟩

/-- The ENTIRE private physical allowed carrier embeds in the actual common carrier. -/
theorem originalScheduledPrivatePhysicalCarrier_subset_common (bound : ℕ → ℕ) (n : ℕ) :
    (originalScheduledPrivatePhysicalCarrier (originalCommonWindowBounds bound) n).carrier ⊆
      (originalScheduledCommonCarrier bound).carrier := by
  intro x hx
  rw [originalScheduledCommonCarrier_carrier]
  exact Or.inr (Set.mem_iUnion.mpr ⟨n, Or.inl hx⟩)

/-- The ENTIRE private spectral allowed carrier, including ALL coarse points, embeds in the common carrier. -/
theorem originalScheduledPrivateSpectralCarrier_subset_common (bound : ℕ → ℕ) (n : ℕ) :
    (originalScheduledPrivateSpectralCarrier (originalCommonWindowBounds bound) n).carrier ⊆
      (originalScheduledCommonCarrier bound).carrier := by
  intro x hx
  rw [originalScheduledCommonCarrier_carrier]
  exact Or.inr (Set.mem_iUnion.mpr ⟨n, Or.inr hx⟩)

open scoped FourierTransform

/-- BOTH original weighted-TV records of EVERY actual source are admitted on the SAME whole common carrier. -/
theorem originalScheduledCommonSource_both_strong (bound : ℕ → ℕ) (n : ℕ) :
    originalScheduledPrivateLineSource (originalCommonWindowBounds bound) n ∈
      stronglyTemperedAtomicAtExponent (originalScheduledCommonCarrier bound)
        ((originalReflectedOrderSchedule (originalCommonWindowBounds bound) n - 1) + 2) ∧
    𝓕 (originalScheduledPrivateLineSource (originalCommonWindowBounds bound) n) ∈
      stronglyTemperedAtomicAtExponent (originalScheduledCommonCarrier bound)
        (originalReflectedOrderSchedule (originalCommonWindowBounds bound) n + 3) := by
  have hs := originalScheduledPrivateLineSource_both_strong (originalCommonWindowBounds bound) n
  exact ⟨stronglyTemperedAtomicAtExponent_mono_carrier
    (originalScheduledPrivatePhysicalCarrier_subset_common bound n) _ _ hs.1,
    stronglyTemperedAtomicAtExponent_mono_carrier
      (originalScheduledPrivateSpectralCarrier_subset_common bound n) _ _ hs.2⟩

/-- Every actual nonzero source belongs to the COMPLETE strong Meyer space of the actual common carrier. -/
theorem originalScheduledCommonSource_mem (bound : ℕ → ℕ) (n : ℕ) :
    originalScheduledPrivateLineSource (originalCommonWindowBounds bound) n ∈
      StronglyTemperedMeyerSpace (originalScheduledCommonCarrier bound) := by
  have hs := originalScheduledCommonSource_both_strong bound n
  exact ⟨(mem_stronglyTemperedAtomicOnCarrier_iff _ _).mpr ⟨_, hs.1⟩,
    (mem_stronglyTemperedAtomicOnCarrier_iff _ _).mpr ⟨_, hs.2⟩⟩

/-- The actual complete common strong space is nontrivial, proved by an internally constructed source. -/
theorem originalScheduledCommonStrongSpace_ne_bot (bound : ℕ → ℕ) :
    StronglyTemperedMeyerSpace (originalScheduledCommonCarrier bound) ≠ ⊥ := by
  intro he
  have hm := originalScheduledCommonSource_mem bound 0
  rw [he, Submodule.mem_bot] at hm
  exact originalScheduledPrivateLineSource_ne_zero (originalCommonWindowBounds bound) 0 hm

end

end MeyerGeneralProblem.StrongParity

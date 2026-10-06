module

public import MeyerGeneralProblem.Cardinal.Strong.ComputedOriginalHeadBases

@[expose] public section

/-! Explicit finite enumeration of the ENTIRE original W basis index family.
The analytic basis's classical Fintype instance is not used by this program. -/

namespace MeyerGeneralProblem.StrongParity

/-- Typed ordinary pivot map on the named original head interface. -/
def computedOriginalHeadPivot (s : ℕ) (hs : 2 ≤ s) (head : productOriginalHeadLabel s) :
    productNumeratorIndex s := productOriginalHeadPivotIndex s hs head

/-- Explicit image of every computed original forbidden-head pivot. -/
def computedOriginalWPivots (s : ℕ) (hs : 2 ≤ s) (m : ℕ) : Finset (productNumeratorIndex s) :=
  (computedOriginalHeadMask s m).image (computedOriginalHeadPivot s hs)

/-- Literal ordinary middle coordinate removed from the complete H basis. -/
def computedOriginalMiddleCoordinate (s : ℕ) (hs : 2 ≤ s) : productNumeratorIndex s :=
  productInteriorIndex s (s / 2) (by omega)

/-- Complete finite W-coordinate enumeration, excluding all head pivots and the literal middle. -/
def computedOriginalWCoordinates (s : ℕ) (hs : 2 ≤ s) (m : ℕ) : Finset (productNumeratorIndex s) :=
  Finset.univ.filter (fun k => k ∉ computedOriginalWPivots s hs m ∧ k ≠ computedOriginalMiddleCoordinate s hs)

/-- Ordinary finite W-index type obtained from the explicit enumerated coordinates. -/
abbrev computedOriginalWIndex (s : ℕ) (hs : 2 ≤ s) (m : ℕ) :=
  ↥(computedOriginalWCoordinates s hs m)

/-- The implemented W-index enumeration is a constructive finite type. -/
instance computedOriginalWIndex_fintype (s : ℕ) (hs : 2 ≤ s) (m : ℕ) :
    Fintype (computedOriginalWIndex s hs m) := inferInstance

/-- Implemented W-index equality compares only the original bounded natural coordinates. -/
instance computedOriginalWIndex_decidableEq (s : ℕ) (hs : 2 ≤ s) (m : ℕ) :
    DecidableEq (computedOriginalWIndex s hs m) := inferInstance

/-- The complete computed free-coordinate condition uses every actual original head pivot. -/
theorem mem_computedOriginalWCoordinates_iff (s : ℕ) (hs : 2 ≤ s) (m : ℕ)
    (k : productNumeratorIndex s) :
    k ∈ computedOriginalWCoordinates s hs m ↔
      (∀ head : computedOriginalHeadMask s m, productOriginalHeadPivotIndex s hs head.val ≠ k) ∧
        k ≠ computedOriginalMiddleCoordinate s hs := by
  rw [computedOriginalWCoordinates, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h, hmid⟩
    refine ⟨?_, hmid⟩
    intro head heq
    exact h (Finset.mem_image.mpr ⟨head.val, head.property, heq⟩)
  · rintro ⟨h, hmid⟩
    refine ⟨?_, hmid⟩
    intro hp
    obtain ⟨head, hh, he⟩ := Finset.mem_image.mp hp
    exact h ⟨head, hh⟩ he

/-- Ordinary proof lift from computed coordinates to the definite whole analytic W basis. -/
def computedOriginalWIndexToActual {s : ℕ} (block : CompactOriginalParameterBlock s)
    (hs : 2 ≤ s) (m : ℕ) (k : computedOriginalWIndex s hs m) :
    CompactOriginal.productOriginalHeadCornerFreeIndex block hs (computedOriginalHeadMask s m) := by
  refine ⟨⟨k.val, ?_⟩, ?_⟩
  · rintro ⟨head, heq⟩
    exact ((mem_computedOriginalWCoordinates_iff s hs m k.val).mp k.property).1 head heq
  · rintro ⟨u, heq⟩
    have h := congrArg Subtype.val heq
    exact ((mem_computedOriginalWCoordinates_iff s hs m k.val).mp k.property).2 h.symm

/-- Ordinary inverse lift retaining ALL actual free basis indices. -/
def computedOriginalWIndexFromActual {s : ℕ} (block : CompactOriginalParameterBlock s)
    (hs : 2 ≤ s) (m : ℕ)
    (j : CompactOriginal.productOriginalHeadCornerFreeIndex block hs (computedOriginalHeadMask s m)) :
    computedOriginalWIndex s hs m := by
  refine ⟨j.val.val, (mem_computedOriginalWCoordinates_iff s hs m j.val.val).mpr ⟨?_, ?_⟩⟩
  · intro head heq
    exact j.val.property ⟨head, heq⟩
  · intro heq
    apply j.property
    refine ⟨(), Subtype.ext heq.symm⟩

/-- The explicit ordinary index list is bijective with the ENTIRE specified actual W basis. -/
def computedOriginalWIndexEquivActual {s : ℕ} (block : CompactOriginalParameterBlock s)
    (hs : 2 ≤ s) (m : ℕ) :
    computedOriginalWIndex s hs m ≃
      CompactOriginal.productOriginalHeadCornerFreeIndex block hs (computedOriginalHeadMask s m) where
  toFun := computedOriginalWIndexToActual block hs m
  invFun := computedOriginalWIndexFromActual block hs m
  left_inv k := Subtype.ext rfl
  right_inv j := Subtype.ext (Subtype.ext rfl)

/-- Explicit enumeration has the same proved exact full W dimension. -/
theorem computedOriginalWIndex_card {s : ℕ} (block : CompactOriginalParameterBlock s)
    (hs : 2 ≤ s) (m : ℕ) :
    Fintype.card (computedOriginalWIndex s hs m) +
      (computedOriginalNoncoarseHeadLabels s m).card + 2 = (s + 1) ^ 2 := by
  rw [Fintype.card_congr (computedOriginalWIndexEquivActual block hs m)]
  exact computedOriginalHeadCornerFreeIndex_card block hs m

end MeyerGeneralProblem.StrongParity

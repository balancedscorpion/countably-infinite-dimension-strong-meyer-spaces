module

public import MeyerGeneralProblem.Cardinal.Strong.ComputedNoncoarseHead
public import MeyerGeneralProblem.Cardinal.Strong.RationalOriginalHeadProjection

@[expose] public section

/-! The complete forbidden original head as an ordinary finite subtype mask.
No real-order decision or supplied finite head family is used by the program. -/

namespace MeyerGeneralProblem.StrongParity

/-- Lift an enumerated noncoarse label to the actual original head type. -/
def computedOriginalHeadLift (s m : ℕ) (p : computedOriginalNoncoarseHeadLabels s m) :
    productOriginalHeadLabel s :=
  ⟨p.val, ((mem_computedOriginalNoncoarseHeadLabels_iff s m p.val).mp p.property).1⟩

/-- Internally enumerated complete forbidden head, with the original head proofs erased. -/
def computedOriginalHeadMask (s m : ℕ) : Finset (productOriginalHeadLabel s) :=
  (computedOriginalNoncoarseHeadLabels s m).attach.image (computedOriginalHeadLift s m)

/-- Typed proof-forgetting map retaining the named original head interface. -/
def originalHeadUnderlyingLabel (s : ℕ) (head : productOriginalHeadLabel s) : spectralConeIndex :=
  head.val

/-- The output includes every actual noncoarse head and excludes every coarse head. -/
theorem mem_computedOriginalHeadMask_iff (s m : ℕ) (head : productOriginalHeadLabel s) :
    head ∈ computedOriginalHeadMask s m ↔
      ¬(m ∣ (spectralConeIndexCoordinates head.val).1 ∧
        m ∣ (spectralConeIndexCoordinates head.val).2) := by
  rw [computedOriginalHeadMask, Finset.mem_image]
  constructor
  · rintro ⟨p, _, hp⟩
    have hval : p.val = head.val := congrArg Subtype.val hp
    have h := ((mem_computedOriginalNoncoarseHeadLabels_iff s m p.val).mp p.property).2
    rwa [hval] at h
  · intro h
    have hp : head.val ∈ computedOriginalNoncoarseHeadLabels s m :=
      (mem_computedOriginalNoncoarseHeadLabels_iff s m head.val).mpr ⟨head.property, h⟩
    refine ⟨⟨head.val, hp⟩, Finset.mem_attach _ _, ?_⟩
    exact Subtype.ext rfl

/-- The subtype mask is exactly the geometric private head outside the shared coarse cone. -/
theorem mem_computedOriginalHeadMask_geometric (s m : ℕ) (hm : 0 < m)
    (head : productOriginalHeadLabel s) :
    head ∈ computedOriginalHeadMask s m ↔
      originalPrivateSpectralLabelValue m head.val ∉ originalSharedCoarseCone.carrier := by
  rw [mem_computedOriginalHeadMask_iff,
    originalPrivateSpectralLabelValue_coarse_divisibility m hm head.val]

/-- Forgetting head proofs recovers the entire implemented signed noncoarse enumeration. -/
theorem computedOriginalHeadMask_image_val (s m : ℕ) :
    (computedOriginalHeadMask s m).image (originalHeadUnderlyingLabel s) =
      computedOriginalNoncoarseHeadLabels s m := by
  ext label
  rw [Finset.mem_image]
  constructor
  · rintro ⟨head, hh, rfl⟩
    exact (mem_computedOriginalNoncoarseHeadLabels_iff s m head.val).mpr
      ⟨head.property, (mem_computedOriginalHeadMask_iff s m head).mp hh⟩
  · intro h
    let head : productOriginalHeadLabel s :=
      ⟨label, ((mem_computedOriginalNoncoarseHeadLabels_iff s m label).mp h).1⟩
    exact ⟨head, (mem_computedOriginalHeadMask_iff s m head).mpr
      ((mem_computedOriginalNoncoarseHeadLabels_iff s m label).mp h).2, rfl⟩

/-- Both representations count the same complete signed mask, including no duplicate zero. -/
theorem computedOriginalHeadMask_card (s m : ℕ) :
    (computedOriginalHeadMask s m).card = (computedOriginalNoncoarseHeadLabels s m).card := by
  rw [← computedOriginalHeadMask_image_val s m]
  exact (Finset.card_image_of_injective _
    (show Function.Injective (originalHeadUnderlyingLabel s) from Subtype.val_injective)).symm

/-- The whole unit-scale head remains in the coarse cone, at every original order. -/
theorem computedOriginalHeadMask_one (s : ℕ) : computedOriginalHeadMask s 1 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro head
  rw [mem_computedOriginalHeadMask_iff]
  simp

end MeyerGeneralProblem.StrongParity

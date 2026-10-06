module

public import MeyerGeneralProblem.Cardinal.Strong.ComputedOriginalDirectedLayers
public import MeyerGeneralProblem.Distribution.StrongDilation

@[expose] public section

/-! Positive dilation of the PARTICULAR original physical deletions and the
ENTIRE noncoarse geometric head. The fixed shared coarse cone is retained. -/

namespace MeyerGeneralProblem

noncomputable section

/-- Positive dilation transports ALL actual deleted support points exactly. -/
theorem LocallyFiniteCarrier.dilate_delete (S : LocallyFiniteCarrier) (D : Set ℝ)
    (c : ℝ) (hc : 0 < c) :
    (S.delete D).dilate c hc = (S.dilate c hc).delete ((fun x : ℝ => c * x) '' D) := by
  apply LocallyFiniteCarrier.ext
  exact Set.image_sdiff (mul_right_injective₀ hc.ne') S.carrier D

namespace StrongParity

/-- The literal positive private scale at every positive natural `m`. -/
def originalPrivateScale (m : ℕ) : ℝ := parityDilationUnit * (m : ℝ)

theorem originalPrivateScale_pos (m : ℕ) (hm : 0 < m) : 0 < originalPrivateScale m :=
  mul_pos parityDilationUnit_pos (by exact_mod_cast hm)

/-- The actual smaller original geometric noncoarse head to be removed. -/
def originalPrivateGeometricHead (s m : ℕ) : Set ℝ :=
  {x | |x| ≤ (((s / 2 : ℕ) : ℝ) / 2) / originalPrivateScale m ∧
    x ∉ originalSharedCoarseCone.carrier}

/-- The full computed ORIGINAL deletion mask, after reciprocal dilation,
equals the entire geometric noncoarse head inside the actual private cone. -/
theorem computedOriginalHeadDeletion_scaled_eq (s m : ℕ) (hm : 0 < m) :
    (fun y : ℝ => (originalPrivateScale m)⁻¹ * y) ''
      productOriginalHeadDeletion s (computedOriginalHeadMask s m) =
        (originalPrivateSpectralCone m hm).carrier ∩ originalPrivateGeometricHead s m := by
  ext x
  constructor
  · rintro ⟨y, ⟨head, hh, rfl⟩, rfl⟩
    have hval : (originalPrivateScale m)⁻¹ * spectralConeIndexFrequency head.val =
        originalPrivateSpectralLabelValue m head.val := by
      simp only [originalPrivateScale, originalPrivateSpectralLabelValue, div_eq_mul_inv, mul_comm]
    change (originalPrivateScale m)⁻¹ * spectralConeIndexFrequency head.val ∈
      (originalPrivateSpectralCone m hm).carrier ∩ originalPrivateGeometricHead s m
    rw [hval]
    refine ⟨originalPrivateSpectralLabelValue_mem m hm head.val, ?_⟩
    exact ⟨(originalPrivateSpectralLabelValue_head_iff s m hm head.val).mpr head.property,
      (mem_computedOriginalHeadMask_geometric s m hm head).mp hh⟩
  · rintro ⟨hx, hhead⟩
    obtain ⟨label, hlabel⟩ := originalPrivateSpectralCone_label_surjective m hm x hx
    have hgeom : |originalPrivateSpectralLabelValue m label| ≤
        (((s / 2 : ℕ) : ℝ) / 2) / (parityDilationUnit * (m : ℝ)) ∧
        originalPrivateSpectralLabelValue m label ∉ originalSharedCoarseCone.carrier := by
      rw [hlabel]
      exact hhead
    let head : productOriginalHeadLabel s :=
      ⟨label, (originalPrivateSpectralLabelValue_head_iff s m hm label).mp hgeom.1⟩
    have hh : head ∈ computedOriginalHeadMask s m :=
      (mem_computedOriginalHeadMask_geometric s m hm head).mpr hgeom.2
    refine ⟨spectralConeIndexFrequency label, ⟨head, hh, rfl⟩, ?_⟩
    simpa only [originalPrivateScale, originalPrivateSpectralLabelValue, div_eq_mul_inv, mul_comm]
      using hlabel

/-- The allowed cone retains EVERY coarse point and deletes precisely the
original noncoarse head. This includes all allowed zero-coefficient points. -/
def computedOriginalPrivateSpectralCarrier (s m : ℕ) (hm : 0 < m) : LocallyFiniteCarrier :=
  (originalPrivateSpectralCone m hm).delete (originalPrivateGeometricHead s m)

/-- Whole-carrier equality identifies the computed native support equations
with the literal original scaled cone, rather than a selected label subsystem. -/
theorem computedOriginalPrivateSpectralCarrier_eq_dilate (s m : ℕ) (hm : 0 < m) :
    computedOriginalPrivateSpectralCarrier s m hm =
      (spectralConeCarrier.delete (productOriginalHeadDeletion s (computedOriginalHeadMask s m))).dilate
        (originalPrivateScale m)⁻¹ (inv_pos.mpr (originalPrivateScale_pos m hm)) := by
  rw [LocallyFiniteCarrier.dilate_delete, computedOriginalHeadDeletion_scaled_eq s m hm]
  apply LocallyFiniteCarrier.ext
  change (originalPrivateSpectralCone m hm).carrier \ originalPrivateGeometricHead s m =
    (originalPrivateSpectralCone m hm).carrier \
      ((originalPrivateSpectralCone m hm).carrier ∩ originalPrivateGeometricHead s m)
  ext x
  constructor
  · rintro ⟨hx, hhead⟩
    exact ⟨hx, fun h => hhead h.2⟩
  · rintro ⟨hx, hhead⟩
    exact ⟨hx, fun h => hhead ⟨hx, h⟩⟩

theorem originalSharedCoarseCone_subset_computedPrivate (s m : ℕ) (hm : 0 < m) :
    originalSharedCoarseCone.carrier ⊆ (computedOriginalPrivateSpectralCarrier s m hm).carrier := by
  intro x hx
  exact ⟨originalSharedCoarseCone_subset_private m hm hx, fun h => h.2 hx⟩

/-- The PARTICULAR physical deletion set transported at the actual private scale. -/
def coupledComputedOriginalScaledPhysicalDeletion (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) : Set ℝ :=
  (fun y : ℝ => originalPrivateScale m * y) ''
    coupledComputedOriginalPhysicalDeletion scales hpos offset s hs m

theorem coupledComputedOriginalScaledPhysicalDeletion_finite (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) :
    (coupledComputedOriginalScaledPhysicalDeletion scales hpos offset s hs m).Finite :=
  (coupledComputedOriginalPhysicalDeletion_finite scales hpos offset s hs m).image _

/-- The ENTIRE physical allowed carrier of the original private-scale block. -/
def coupledComputedOriginalPrivatePhysicalCarrier (scales : ℕ → ℕ) (hpos : ∀ i, 0 < scales i)
    (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) (hm : 0 < m) : LocallyFiniteCarrier :=
  (compactOriginalPhysicalSheetCarrier (coupledCompactOriginalParameterBlock scales hpos offset s) m hm).delete
    (coupledComputedOriginalScaledPhysicalDeletion scales hpos offset s hs m)

theorem coupledComputedOriginalPrivatePhysicalCarrier_eq_dilate (scales : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (offset s : ℕ) (hs : 2 ≤ s) (m : ℕ) (hm : 0 < m) :
    coupledComputedOriginalPrivatePhysicalCarrier scales hpos offset s hs m hm =
      ((compactOriginalProductSheetCarrier (coupledCompactOriginalParameterBlock scales hpos offset s)).delete
        (coupledComputedOriginalPhysicalDeletion scales hpos offset s hs m)).dilate
          (originalPrivateScale m) (originalPrivateScale_pos m hm) :=
  (LocallyFiniteCarrier.dilate_delete _ _ _ _).symm

end StrongParity

end

end MeyerGeneralProblem

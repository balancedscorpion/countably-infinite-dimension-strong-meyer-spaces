module

public import MeyerGeneralProblem.Cardinal.Strong.ComputedOriginalWRootSearch
public import MeyerGeneralProblem.Cardinal.Strong.CoupledOriginalPrefixStability

@[expose] public section

/-! Literal equality of the actual block programs from their finite dictionary
of certified parameter names. In particular the terminating deletion search
cannot depend on future parameters through its proof of termination. -/
namespace MeyerGeneralProblem.StrongParity

variable (scales scales' : ℕ → ℕ) (hpos : ∀ i, 0 < scales i) (hpos' : ∀ i, 0 < scales' i)
  (offset s : ℕ)
  (hn : ∀ i : Fin s,
    coupledOriginalParameterNames scales hpos disjointOriginalParameterSlot (offset + i.val) =
    coupledOriginalParameterNames scales' hpos' disjointOriginalParameterSlot (offset + i.val))

include hn

/-- The actual finite parameter-name dictionary is equal as a whole rational program. -/
theorem coupledOriginalBlockNameDictionary_eq :
    (fun i : Fin s => (coupledOriginalParameterNames scales hpos
      disjointOriginalParameterSlot (offset + i.val)).val) =
    (fun i : Fin s => (coupledOriginalParameterNames scales' hpos'
      disjointOriginalParameterSlot (offset + i.val)).val) := by
  funext i
  rw [hn i]

/-- Every native root-name program is unchanged, at ALL precisions and integer labels. -/
theorem coupledCompactOriginalNativeRootName_eq_of_names (i : Fin s) (n : ℤ) :
    coupledCompactOriginalNativeRootName scales hpos offset s i n =
      coupledCompactOriginalNativeRootName scales' hpos' offset s i n := by
  funext p
  unfold coupledCompactOriginalNativeRootName
  rw [hn i]

/-- Every complete original slab monomial program is unchanged. -/
theorem coupledCompactOriginalRootMonomialName_eq_of_names (i : Fin s) (n : ℤ)
    (j : productNumeratorIndex s) (p : ℕ) :
    coupledCompactOriginalRootMonomialName scales hpos offset s i n j p =
      coupledCompactOriginalRootMonomialName scales' hpos' offset s i n j p := by
  simp only [coupledCompactOriginalRootMonomialName, coupledCompactOriginalRootMonomialAt,
    coupledCompactOriginalRootUName, coupledCompactOriginalRootVName,
    coupledCompactOriginalNativeRootName_eq_of_names scales scales' hpos hpos' offset s hn]

/-- The entire signed original spectral-coordinate program uses only the finite name dictionary. -/
theorem coupledCompactOriginalSpectralCoordinateName_eq_of_names (j : productNumeratorIndex s)
    (label : spectralConeIndex) (p : ℕ) :
    coupledCompactOriginalSpectralCoordinateName scales hpos offset s j label p =
      coupledCompactOriginalSpectralCoordinateName scales' hpos' offset s j label p := by
  unfold coupledCompactOriginalSpectralCoordinateName
  rw [coupledOriginalBlockNameDictionary_eq scales scales' hpos hpos' offset s hn]

/-- The full head/corner elimination program, including all coordinates, is unchanged. -/
theorem coupledCompactOriginalComputedHeadCornerProjectionName_eq_of_names (hs : 2 ≤ s) (m : ℕ)
    (j : productNumeratorIndex s) (p : ℕ) :
    coupledCompactOriginalComputedHeadCornerProjectionName scales hpos offset s hs m j p =
      coupledCompactOriginalComputedHeadCornerProjectionName scales' hpos' offset s hs m j p := by
  simp only [coupledCompactOriginalComputedHeadCornerProjectionName,
    coupledCompactOriginalHeadCornerProjectionName, coupledCompactOriginalHeadProjectionAt,
    coupledCompactOriginalSpectralCoordinateName_eq_of_names scales scales' hpos hpos' offset s hn]

/-- The literal whole rational root matrix is unchanged, not just its real limit. -/
theorem coupledComputedOriginalWRootMatrixName_eq_of_names (hs : 2 ≤ s) (m : ℕ)
    (roots : computedOriginalWIndex s hs m → Fin s × ℤ) (p : ℕ) :
    coupledComputedOriginalWRootMatrixName scales hpos offset s hs m roots p =
      coupledComputedOriginalWRootMatrixName scales' hpos' offset s hs m roots p := by
  funext i j
  simp only [coupledComputedOriginalWRootMatrixName, coupledCompactOriginalWRootRowName,
    coupledCompactOriginalWRootRowAt,
    coupledCompactOriginalRootMonomialName_eq_of_names scales scales' hpos hpos' offset s hn]
  change rationalComplexDot _ (coupledCompactOriginalComputedHeadCornerProjectionName
    scales hpos offset s hs m j.val _) = rationalComplexDot _
      (coupledCompactOriginalComputedHeadCornerProjectionName scales' hpos' offset s hs m j.val _)
  rw [coupledCompactOriginalComputedHeadCornerProjectionName_eq_of_names scales scales' hpos hpos' offset s hn]

/-- The whole determinant approximation program is unchanged at every precision. -/
theorem coupledComputedOriginalWRootDetName_eq_of_names (hs : 2 ≤ s) (m : ℕ)
    (roots : computedOriginalWIndex s hs m → Fin s × ℤ) (p : ℕ) :
    coupledComputedOriginalWRootDetName scales hpos offset s hs m roots p =
      coupledComputedOriginalWRootDetName scales' hpos' offset s hs m roots p := by
  unfold coupledComputedOriginalWRootDetName
  rw [coupledComputedOriginalWRootMatrixName_eq_of_names scales scales' hpos hpos' offset s hn]

/-- Every candidate code has exactly the same Boolean result under future parameter changes. -/
theorem coupledComputedOriginalWRootProbe_eq_of_names (hs : 2 ≤ s) (m code : ℕ) :
    coupledComputedOriginalWRootProbe scales hpos offset s hs m code =
      coupledComputedOriginalWRootProbe scales' hpos' offset s hs m code := by
  unfold coupledComputedOriginalWRootProbe
  split
  · rfl
  · rw [coupledComputedOriginalWRootDetName_eq_of_names scales scales' hpos hpos' offset s hn]

/-- The actual terminating least-code search returns the SAME natural code. -/
theorem coupledComputedOriginalWRootSearchCode_eq_of_names (hs : 2 ≤ s) (m : ℕ) :
    coupledComputedOriginalWRootSearchCode scales hpos offset s hs m =
      coupledComputedOriginalWRootSearchCode scales' hpos' offset s hs m := by
  apply Nat.le_antisymm
  · apply Nat.find_min'
    rw [coupledComputedOriginalWRootProbe_eq_of_names scales scales' hpos hpos' offset s hn]
    exact coupledComputedOriginalWRootSearchCode_spec scales' hpos' offset s hs m
  · apply Nat.find_min'
    rw [← coupledComputedOriginalWRootProbe_eq_of_names scales scales' hpos hpos' offset s hn]
    exact coupledComputedOriginalWRootSearchCode_spec scales hpos offset s hs m

/-- The actual decoded deletion tuple AND successful precision are unchanged. -/
theorem coupledComputedOriginalWSelectedRoots_eq_of_names (hs : 2 ≤ s) (m : ℕ) :
    coupledComputedOriginalWSelectedRoots scales hpos offset s hs m =
      coupledComputedOriginalWSelectedRoots scales' hpos' offset s hs m := by
  unfold coupledComputedOriginalWSelectedRoots
  simp only [coupledComputedOriginalWRootSearchCode_eq_of_names scales scales' hpos hpos' offset s hn]

end MeyerGeneralProblem.StrongParity

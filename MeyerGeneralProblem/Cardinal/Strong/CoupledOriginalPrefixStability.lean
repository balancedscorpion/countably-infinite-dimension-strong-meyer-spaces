module

public import MeyerGeneralProblem.Cardinal.Strong.CoupledOriginalRootExclusions

@[expose] public section

/-!
# Exact prefix stability of the implemented coupled original names

The actual recursive exclusion program at sheet `i` depends only on scales,
slots and names at indices at most `i`. Agreement of that finite prefix gives
literal equality of ordinary rational programs and their unique real values.
This is the causal interface needed by the later adaptive radius construction.
-/

namespace MeyerGeneralProblem.StrongParity

/-- Equal computational inputs give equal name programs; validity fields are proofs only. -/
theorem allOriginalExclusionsParameterName_congr (names names' : ℕ → ℕ → ℚ)
    (hvalid : BinaryRationalNamesValid names) (hvalid' : BinaryRationalNamesValid names')
    (m m' : ℕ) (hm : 0 < m) (hm' : 0 < m') (slot slot' : RationalParameterSlot)
    (hn : names = names') (hscale : m = m') (hslot : slot = slot') :
    allOriginalExclusionsParameterName names hvalid m hm slot =
      allOriginalExclusionsParameterName names' hvalid' m' hm' slot' := by
  subst names'
  subst m'
  subst slot'
  rfl

/-- The complete earlier dictionary data use scales only at EARLIER indices. -/
theorem earlierOriginalConstantNameData_prefix_congr {i : ℕ} (scales scales' : ℕ → ℕ)
    (earlier : Fin i → CertifiedOriginalParameterName)
    (hs : ∀ j : Fin i, scales j.val = scales' j.val) (data : EarlierOriginalConstantData i) (p : ℕ) :
    earlierOriginalConstantNameData scales earlier data p =
      earlierOriginalConstantNameData scales' earlier data p := by
  rcases data with ⟨u, v⟩ | ⟨j, n, negative⟩
  · rfl
  · simp only [earlierOriginalConstantNameData, hs j]

/-- The ENTIRE encoded earlier dictionary is fixed by its finite scale prefix. -/
theorem earlierOriginalConstantNames_prefix_congr {i : ℕ} (scales scales' : ℕ → ℕ)
    (earlier : Fin i → CertifiedOriginalParameterName)
    (hs : ∀ j : Fin i, scales j.val = scales' j.val) :
    earlierOriginalConstantNames scales earlier = earlierOriginalConstantNames scales' earlier := by
  funext k p
  unfold earlierOriginalConstantNames
  cases h : Encodable.decode (α := EarlierOriginalConstantData i) k with
  | none => rfl
  | some data => exact earlierOriginalConstantNameData_prefix_congr scales scales' earlier hs data p

/-- One step of the actual name program uses only the complete earlier dictionary
and its current scale and slot; future scales cannot affect the step. -/
theorem nextCoupledOriginalParameterName_prefix_congr (scales scales' : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (hpos' : ∀ i, 0 < scales' i)
    (slots slots' : ℕ → RationalParameterSlot) (i : ℕ)
    (earlier : Fin i → CertifiedOriginalParameterName)
    (hs : ∀ j ≤ i, scales j = scales' j) (hslot : slots i = slots' i) :
    nextCoupledOriginalParameterName scales hpos slots i earlier =
      nextCoupledOriginalParameterName scales' hpos' slots' i earlier := by
  have hd := earlierOriginalConstantNames_prefix_congr scales scales' earlier
    (fun j => hs j.val j.isLt.le)
  apply Subtype.ext
  dsimp [nextCoupledOriginalParameterName]
  exact allOriginalExclusionsParameterName_congr _ _ _ _ _ _ _ _ _ _ hd (hs i le_rfl) hslot

/-- EVERY precision of the actual ordinary coupled name is unaffected by future
scales or future slots. Agreement is required only through the current sheet. -/
theorem coupledOriginalParameterNames_prefix_congr (scales scales' : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (hpos' : ∀ i, 0 < scales' i)
    (slots slots' : ℕ → RationalParameterSlot) (i : ℕ)
    (hs : ∀ j ≤ i, scales j = scales' j) (hslot : ∀ j ≤ i, slots j = slots' j) :
    coupledOriginalParameterNames scales hpos slots i =
      coupledOriginalParameterNames scales' hpos' slots' i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    have he : (fun j : Fin i => coupledOriginalParameterNames scales hpos slots j.val) =
        (fun j : Fin i => coupledOriginalParameterNames scales' hpos' slots' j.val) := by
      funext j
      exact ih j.val j.isLt (fun k hk => hs k (hk.trans j.isLt.le))
        (fun k hk => hslot k (hk.trans j.isLt.le))
    rw [coupledOriginalParameterNames_eq, coupledOriginalParameterNames_eq, he]
    exact nextCoupledOriginalParameterName_prefix_congr scales scales' hpos hpos' slots slots' i _
      hs (hslot i le_rfl)

noncomputable section

/-- Prefix equality of the actual name programs also fixes their unique real parameters. -/
theorem coupledOriginalParameterValue_prefix_congr (scales scales' : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (hpos' : ∀ i, 0 < scales' i)
    (slots slots' : ℕ → RationalParameterSlot) (i : ℕ)
    (hs : ∀ j ≤ i, scales j = scales' j) (hslot : ∀ j ≤ i, slots j = slots' j) :
    coupledOriginalParameterValue scales hpos slots i =
      coupledOriginalParameterValue scales' hpos' slots' i := by
  unfold coupledOriginalParameterValue
  rw [coupledOriginalParameterNames_prefix_congr scales scales' hpos hpos' slots slots' i hs hslot]

/-- ALL roots of an earlier sheet retain their literal values under future changes. -/
theorem coupledOriginalPhysicalRoot_prefix_congr (scales scales' : ℕ → ℕ)
    (hpos : ∀ i, 0 < scales i) (hpos' : ∀ i, 0 < scales' i)
    (slots slots' : ℕ → RationalParameterSlot) (i : ℕ) (n : ℤ)
    (hs : ∀ j ≤ i, scales j = scales' j) (hslot : ∀ j ≤ i, slots j = slots' j) :
    coupledOriginalPhysicalRoot scales hpos slots i n =
      coupledOriginalPhysicalRoot scales' hpos' slots' i n := by
  unfold coupledOriginalPhysicalRoot
  rw [hs i le_rfl,
    coupledOriginalParameterValue_prefix_congr scales scales' hpos hpos' slots slots' i hs hslot]

end

end MeyerGeneralProblem.StrongParity

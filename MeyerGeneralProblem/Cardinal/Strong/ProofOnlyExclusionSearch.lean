module

public import MeyerGeneralProblem.Cardinal.Strong.RationalExclusionIntervals

@[expose] public section

/-! Earlier-name validity is proof-only data for the ordinary original exclusion search. -/

namespace MeyerGeneralProblem.StrongParity

/-- There are actual values uniformly approximated by the earlier rational name programs. -/
def BinaryRationalNamesValid (names : ℕ → ℕ → ℚ) : Prop :=
  ∃ values : ℕ → ℝ, ∀ i p, |(names i p : ℝ) - values i| ≤ 1 / (2 : ℝ) ^ p

/-- Actual name validity pays the finite probe search without computational real input. -/
theorem proofOnlyExclusionProbe_exists (codes : List ComputedRootExclusion) (names : ℕ → ℕ → ℚ)
    (hvalid : BinaryRationalNamesValid names) (m : ℕ) (hm : 0 < m)
    (u v : ℚ) (hu : 0 < u) (hv : v ≤ 1 / 2) (huv : u < v) :
    ∃ k, rationalExclusionProbe codes names m u v k = true := by
  obtain ⟨values, hname⟩ := hvalid
  exact rationalExclusionProbe_exists codes names values hname m hm u v hu hv huv

/-- Ordinary finite search with only rational name programs as computational input. -/
def proofOnlyExclusionSearch (codes : List ComputedRootExclusion) (names : ℕ → ℕ → ℚ)
    (hvalid : BinaryRationalNamesValid names) (m : ℕ) (hm : 0 < m)
    (u v : ℚ) (hu : 0 < u) (hv : v ≤ 1 / 2) (huv : u < v) : ℕ :=
  Nat.find (proofOnlyExclusionProbe_exists codes names hvalid m hm u v hu hv huv)

/-- The actual decoded rational center and precision of the proof-only finite search. -/
def proofOnlyExclusionData (codes : List ComputedRootExclusion) (names : ℕ → ℕ → ℚ)
    (hvalid : BinaryRationalNamesValid names) (m : ℕ) (hm : 0 < m)
    (u v : ℚ) (hu : 0 < u) (hv : v ≤ 1 / 2) (huv : u < v) : ℚ × ℕ :=
  (Encodable.decode (proofOnlyExclusionSearch codes names hvalid m hm u v hu hv huv)).getD (0, 0)

/-- The ordinary proof-only search terminates at an actual successful probe. -/
theorem proofOnlyExclusionSearch_success (codes : List ComputedRootExclusion) (names : ℕ → ℕ → ℚ)
    (hvalid : BinaryRationalNamesValid names) (m : ℕ) (hm : 0 < m)
    (u v : ℚ) (hu : 0 < u) (hv : v ≤ 1 / 2) (huv : u < v) :
    rationalExclusionProbe codes names m u v
      (proofOnlyExclusionSearch codes names hvalid m hm u v hu hv huv) = true :=
  Nat.find_spec (proofOnlyExclusionProbe_exists codes names hvalid m hm u v hu hv huv)

/-- The actual decoded data satisfy the slot and ALL finite original certificate tests. -/
theorem proofOnlyExclusionData_spec (codes : List ComputedRootExclusion) (names : ℕ → ℕ → ℚ)
    (hvalid : BinaryRationalNamesValid names) (m : ℕ) (hm : 0 < m)
    (u v : ℚ) (hu : 0 < u) (hv : v ≤ 1 / 2) (huv : u < v) :
    let data := proofOnlyExclusionData codes names hvalid m hm u v hu hv huv
    u < data.1 ∧ data.1 < v ∧ ∀ code ∈ codes, code.certificate names m data.1 data.2 = true := by
  obtain ⟨q, p, hd, hqu, hqv, hc⟩ := rationalExclusionProbe_spec codes names m u v
    (proofOnlyExclusionSearch_success codes names hvalid m hm u v hu hv huv)
  simp only [proofOnlyExclusionData, hd, Option.getD_some]
  exact ⟨hqu, hqv, hc⟩

end MeyerGeneralProblem.StrongParity

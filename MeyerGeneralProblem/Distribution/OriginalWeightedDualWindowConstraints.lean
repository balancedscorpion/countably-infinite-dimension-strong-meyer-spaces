module

public import MeyerGeneralProblem.Distribution.OriginalStrongUnitBallCompactness

@[expose] public section

/-! BOTH full C0 support ideals on arbitrary real sets, specialized to a
locally finite prefix together with the ENTIRE real exterior of a window.
The exterior sets are not locally finite carriers. All closedness and
compactness conclusions concern genuine weighted Fourier duals. -/
namespace MeyerGeneralProblem
noncomputable section
open scoped ZeroAtInfty FourierTransform

/-- BOTH actual C0 records annihilate all value tests vanishing on an arbitrary set. -/
def originalWeightedDualSetConstraints (A : Set ℝ) :
    Set (WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ))) :=
  {q | ∀ g : C₀(ℝ, ℂ), (∀ x ∈ A, g x = 0) → q (g, 0) = 0 ∧ q (0, g) = 0}

/-- The two ENTIRE C0 vanishing ideals are weak-star closed, without atomicity of the set. -/
theorem originalWeightedDualSetConstraints_isClosed (A : Set ℝ) :
    IsClosed (originalWeightedDualSetConstraints A) := by
  have he : originalWeightedDualSetConstraints A =
      ⋂ g : C₀(ℝ, ℂ), ⋂ (_ : ∀ x ∈ A, g x = 0),
        {q : WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ)) | q (g, 0) = 0 ∧ q (0, g) = 0} := by
    ext q
    simp only [originalWeightedDualSetConstraints, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [he]
  apply isClosed_iInter
  intro g
  apply isClosed_iInter
  intro hg
  exact (isClosed_eq (WeakDual.eval_continuous (g, 0)) continuous_const).inter
    (isClosed_eq (WeakDual.eval_continuous (0, g)) continuous_const)

/-- Enlarging the allowed support weakens BOTH original record constraints. -/
theorem originalWeightedDualSetConstraints_mono {A B : Set ℝ} (h : A ⊆ B) :
    originalWeightedDualSetConstraints A ⊆ originalWeightedDualSetConstraints B := by
  intro q hq g hg
  exact hq g (fun x hx => hg x (h hx))

/-- At an actual locally finite carrier these are exactly the already recovered original constraints. -/
theorem originalWeightedDualSetConstraints_eq_carrier (S : LocallyFiniteCarrier) :
    originalWeightedDualSetConstraints S.carrier = originalWeightedDualCarrierConstraints S := by
  ext q
  constructor
  · intro h g hg
    exact h g (fun x hx => hg ⟨x, hx⟩)
  · intro h g hg
    exact h g (fun x => hg x x.property)

/-- The ACTUAL prefix plus FULL real exterior, including its boundary. -/
def originalExteriorWindow (L : Set ℝ) (R : ℝ) : Set ℝ := L ∪ {x | R ≤ |x|}

/-- Increasing a window radius removes allowed exterior points. -/
theorem originalExteriorWindow_antitone (L : Set ℝ) : Antitone (originalExteriorWindow L) := by
  intro R Q h x hx
  rcases hx with hx | hx
  · exact Or.inl hx
  · exact Or.inr (h.trans hx)

/-- Every prefix point remains allowed at every radius. -/
theorem originalExteriorWindow_contains (L : Set ℝ) (R : ℝ) : L ⊆ originalExteriorWindow L R :=
  fun _ hx => Or.inl hx

/-- The genuine Fourier dual unit ball with BOTH prefix-plus-real-exterior support constraints. -/
def originalWeightedDualWindowBall (S : LocallyFiniteCarrier) (N : ℕ) (R : ℝ) :
    Set (WeakDual ℂ (C₀(ℝ, ℂ) × C₀(ℝ, ℂ))) :=
  originalWeightedDualFourierPairBall N ∩
    originalWeightedDualSetConstraints (originalExteriorWindow S.carrier R)

/-- Every actual window ball is compact, with the genuine WHOLE Fourier equation imposed. -/
theorem originalWeightedDualWindowBall_isCompact (S : LocallyFiniteCarrier) (N : ℕ) (R : ℝ) :
    IsCompact (originalWeightedDualWindowBall S N R) :=
  (originalWeightedDualFourierPairBall_isCompact N).inter_right
    (originalWeightedDualSetConstraints_isClosed (originalExteriorWindow S.carrier R))

/-- Every actual window ball is weak-star closed. -/
theorem originalWeightedDualWindowBall_isClosed (S : LocallyFiniteCarrier) (N : ℕ) (R : ℝ) :
    IsClosed (originalWeightedDualWindowBall S N R) :=
  (originalWeightedDualWindowBall_isCompact S N R).isClosed

/-- The actual constrained Fourier unit balls decrease with the real radius. -/
theorem originalWeightedDualWindowBall_antitone (S : LocallyFiniteCarrier) (N : ℕ) :
    Antitone (originalWeightedDualWindowBall S N) := by
  intro R Q h q hq
  exact ⟨hq.1, originalWeightedDualSetConstraints_mono
    (originalExteriorWindow_antitone S.carrier h) hq.2⟩

/-- Every original supported dual lies in EVERY genuine window ball. -/
theorem originalWeightedDualSupportedFourierPairBall_subset_window
    (S : LocallyFiniteCarrier) (N : ℕ) (R : ℝ) :
    originalWeightedDualSupportedFourierPairBall S N ⊆ originalWeightedDualWindowBall S N R := by
  intro q hq
  refine ⟨hq.1, originalWeightedDualSetConstraints_mono
    (originalExteriorWindow_contains S.carrier R) ?_⟩
  rw [originalWeightedDualSetConstraints_eq_carrier]
  exact hq.2

/-- An ACTUAL original unit pair on any locally finite carrier inside the
prefix plus exterior enters the genuine window ball internally. -/
theorem originalStrongPairC0Dual_mem_window_ball
    (A S : LocallyFiniteCarrier) (N : ℕ) (R : ℝ) (T : TemperedDistribution ℝ ℂ)
    (hT : T ∈ stronglyTemperedAtomicAtExponent A N)
    (hF : 𝓕 T ∈ stronglyTemperedAtomicAtExponent A N)
    (hunit : originalStrongPairVariation A N T ≤ 1)
    (hA : A.carrier ⊆ originalExteriorWindow S.carrier R) :
    (originalStrongPairC0Dual A N T hT hF).toWeakDual ∈ originalWeightedDualWindowBall S N R := by
  have hq := originalStrongPairC0Dual_mem_supported_ball A N T hT hF hunit
  refine ⟨hq.1, originalWeightedDualSetConstraints_mono hA ?_⟩
  rw [originalWeightedDualSetConstraints_eq_carrier]
  exact hq.2

end
end MeyerGeneralProblem

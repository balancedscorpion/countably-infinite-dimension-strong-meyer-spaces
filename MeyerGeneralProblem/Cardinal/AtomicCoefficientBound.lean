module

public import MeyerGeneralProblem.Distribution.MeyerSpace
public import Mathlib.Analysis.Complex.Cardinality
public import Mathlib.SetTheory.Cardinal.Continuum

@[expose] public section

/-!
# Countable atomic coordinates of the distributional Meyer space

Local atomicity determines a tempered distribution by its carrier masses.
Compact Schwartz cutoff density makes this an injection on the full
distributional space; no growth or total-variation bound on the masses is
assumed.  The resulting set-cardinality bound does not assert the cardinal
trichotomy or exhaustion by fixed-order layers.
-/

open Filter

namespace MeyerGeneralProblem

noncomputable section

/-- An atomic tempered distribution with zero coefficients is zero.  The
finite local formula first gives vanishing on compact Schwartz tests, and
continuity then gives vanishing on every Schwartz test. -/
theorem atomicOnCarrier_eq_zero_of_isolationAction_eq_zero
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier S T)
    (hcoeff : ∀ x : S.subtype, T (S.isolationSchwartz x) = 0) :
    T = 0 := by
  ext f
  have hzero : ∀ N : ℕ, T (compactSchwartzApproximation N f) = 0 := by
    intro N
    obtain ⟨E, _, hsum⟩ :=
      atomicOnCarrier_isLocallyAtomicCoefficientFamily S T hT
        (compactSchwartzApproximation N f)
        (compactSchwartzApproximation_hasCompactSupport N f)
    rw [hsum]
    simp only [hcoeff, zero_mul, Finset.sum_const_zero]
  have hlimit : Tendsto
      (fun N => T (compactSchwartzApproximation N f))
      atTop (nhds (T f)) :=
    (T.continuous.tendsto f).comp (compactSchwartzApproximation_tendsto f)
  have hzeroLimit : Tendsto
      (fun N => T (compactSchwartzApproximation N f))
      atTop (nhds 0) := by
    simpa only [hzero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (nhds 0))
  exact tendsto_nhds_unique hlimit hzeroLimit

/-- Canonical physical atomic coefficients of a distributional Meyer
element, recovered from compact isolating tests. -/
def meyerAtomicCoefficients (S : LocallyFiniteCarrier) :
    DistributionalMeyerSpace S →ₗ[ℂ] (S.subtype → ℂ) where
  toFun T x := (T : TemperedDistribution ℝ ℂ) (S.isolationSchwartz x)
  map_add' T U := by
    funext x
    rfl
  map_smul' c T := by
    funext x
    rfl

/-- The physical coefficients alone determine a distributional Meyer
element; the Fourier coefficients are not needed for this injection. -/
theorem meyerAtomicCoefficients_injective (S : LocallyFiniteCarrier) :
    Function.Injective (meyerAtomicCoefficients S) := by
  intro T U hTU
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply atomicOnCarrier_eq_zero_of_isolationAction_eq_zero S
  · intro f hf
    change (T : TemperedDistribution ℝ ℂ) f -
      (U : TemperedDistribution ℝ ℂ) f = 0
    rw [hasLocallyAtomicAction_atomicOnCarrier S T T.property.1 f hf,
      hasLocallyAtomicAction_atomicOnCarrier S U U.property.1 f hf,
      sub_self]
  · intro x
    change (T : TemperedDistribution ℝ ℂ) (S.isolationSchwartz x) -
      (U : TemperedDistribution ℝ ℂ) (S.isolationSchwartz x) = 0
    exact sub_eq_zero.mpr (congrFun hTU x)

/-- Countably many arbitrary complex masses have cardinality at most the
continuum, even when the carrier is finite or empty. -/
theorem cardinalMk_carrierCoefficientFamily_le_complex
    (S : LocallyFiniteCarrier) :
    Cardinal.mk (S.subtype → ℂ) ≤ Cardinal.mk ℂ := by
  calc
    Cardinal.mk (S.subtype → ℂ) =
        Cardinal.mk ℂ ^ Cardinal.mk S.subtype := by
      rw [Cardinal.mk_arrow, Cardinal.lift_id, Cardinal.lift_uzero]
    _ ≤ Cardinal.mk ℂ ^ Cardinal.aleph0 :=
      Cardinal.power_le_power_left (Cardinal.mk_ne_zero ℂ) Cardinal.mk_le_aleph0
    _ = Cardinal.mk ℂ := by
      rw [Cardinal.mk_complex, Cardinal.continuum_power_aleph0]

/-- The underlying set of the distributional Meyer space has cardinality
at most the continuum, without any coefficient growth assumption. -/
theorem cardinalMk_distributionalMeyerSpace_le_complex
    (S : LocallyFiniteCarrier) :
    Cardinal.mk (DistributionalMeyerSpace S) ≤ Cardinal.mk ℂ :=
  (Cardinal.mk_le_of_injective (meyerAtomicCoefficients_injective S)).trans
    (cardinalMk_carrierCoefficientFamily_le_complex S)

end

end MeyerGeneralProblem

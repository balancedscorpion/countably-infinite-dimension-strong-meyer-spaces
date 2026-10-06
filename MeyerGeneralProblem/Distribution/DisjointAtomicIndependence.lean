module

public import MeyerGeneralProblem.Distribution.DisjointAtomicSeries
public import Mathlib.LinearAlgebra.Dimension.Free

@[expose] public section

/-!
# Independence of nonzero actual atomic sources on disjoint carriers

The full Schwartz continuity/density argument makes some original isolation
coefficient nonzero. Common-carrier bumps then isolate each summand in every
finite relation. This is independence of actual distributions, without a
coefficient surrogate, assumed source series or rank oracle.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter

/-- A nonzero locally atomic distribution has a nonzero ORIGINAL isolation coefficient. -/
theorem locallyAtomic_exists_isolationAction_ne_zero (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : HasLocallyAtomicAction S T) (hT0 : T ≠ 0) :
    ∃ x : S.subtype, T (S.isolationSchwartz x) ≠ 0 := by
  by_contra hn
  push Not at hn
  apply hT0
  ext f
  have hz (N : ℕ) : T (compactSchwartzApproximation N f) = 0 := by
    obtain ⟨E, _, he⟩ := atomicOnCarrier_isLocallyAtomicCoefficientFamily S T
      (hasLocallyAtomicAction_atomicOnCarrier S T hT) (compactSchwartzApproximation N f)
      (compactSchwartzApproximation_hasCompactSupport N f)
    rw [he]
    simp only [hn, zero_mul, Finset.sum_const_zero]
  have ht := (T.continuous.tendsto f).comp (compactSchwartzApproximation_tendsto f)
  have hzero : Tendsto (fun N => T (compactSchwartzApproximation N f)) atTop (nhds (0 : ℂ)) := by
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (nhds 0))
  exact tendsto_nhds_unique ht hzero

/-- ALL nonzero actual atomic sources on pairwise disjoint included carriers are independent. -/
theorem locallyAtomic_linearIndependent_of_disjoint {ι : Type*} (U : LocallyFiniteCarrier)
    (S : ι → LocallyFiniteCarrier) (P : ι → TemperedDistribution ℝ ℂ)
    (hsub : ∀ i, (S i).carrier ⊆ U.carrier) (hP : ∀ i, HasLocallyAtomicAction (S i) (P i))
    (hP0 : ∀ i, P i ≠ 0) (hdisj : Pairwise fun i j => Disjoint (S i).carrier (S j).carrier) :
    LinearIndependent ℂ P := by
  classical
  apply linearIndependent_iff'.mpr
  intro F g hsum i hi
  obtain ⟨x, hx⟩ := locallyAtomic_exists_isolationAction_ne_zero (S i) (P i) (hP i) (hP0 i)
  let test := U.isolationSchwartz (LocallyFiniteCarrier.inclusion (hsub i) x)
  have hdiag : P i test ≠ 0 := by
    change P i (U.isolationSchwartz (LocallyFiniteCarrier.inclusion (hsub i) x)) ≠ 0
    rwa [isolationAction_eq_of_carrier_subset (hsub i) (P i) (hP i) x]
  have hoff (j : ι) (hji : j ≠ i) : P j test = 0 := by
    apply locallyAtomic_isolationAction_eq_zero_of_not_mem U S P hsub hP j
    intro hxj
    exact Set.disjoint_left.mp (hdisj hji) hxj x.property
  let eval : TemperedDistribution ℝ ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun T => T test
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have he := congrArg eval hsum
  simp only [map_sum, map_smul, map_zero, smul_eq_mul] at he
  change (∑ j ∈ F, g j * P j test) = 0 at he
  rw [Finset.sum_eq_single i] at he
  · exact (mul_eq_zero.mp he).resolve_right hdiag
  · intro j _ hji
    rw [hoff j hji, mul_zero]
  · intro hinot
    exact (hinot hi).elim

end

end MeyerGeneralProblem

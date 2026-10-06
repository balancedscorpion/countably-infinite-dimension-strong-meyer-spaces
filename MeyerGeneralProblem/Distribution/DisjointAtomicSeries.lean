module

public import MeyerGeneralProblem.Distribution.CarrierUnion

@[expose] public section

/-!
# Atomic support and coefficient recovery for actual distribution series

The input is an existing tempered distribution with an exact scalar series
identity on every Schwartz function. Local atomicity of its summands gives
local atomicity on any genuine locally finite common carrier. Disjoint
supports then recover each summand's coefficients without cancellation from
the other summands. No existence, continuity, or convergence of the series is
asserted here, and no absolute coefficient growth condition is imposed.
-/

namespace MeyerGeneralProblem

noncomputable section

variable {ι : Type*} (U : LocallyFiniteCarrier) (S : ι → LocallyFiniteCarrier)
  (P : ι → TemperedDistribution ℝ ℂ) (T : TemperedDistribution ℝ ℂ)

/-- An actual scalar action series of locally atomic summands annihilates
every Schwartz function vanishing on a genuine locally finite common carrier.
The supports need not be disjoint for this conclusion. -/
theorem atomicOnCarrier_of_action_tsum
    (hsub : ∀ i, (S i).carrier ⊆ U.carrier)
    (hP : ∀ i, HasLocallyAtomicAction (S i) (P i))
    (hsum : ∀ f : SchwartzMap ℝ ℂ, T f = ∑' i, P i f) :
    AtomicOnCarrier U T := by
  intro f hf
  rw [hsum]
  have hz (i : ι) : P i f = 0 :=
    hasLocallyAtomicAction_atomicOnCarrier (S i) (P i) (hP i) f
      (fun x hx => hf x (hsub i hx))
  simp only [hz, tsum_zero]

/-- The actual series distribution has a finite atomic action on each
compactly supported Schwartz function, with its own isolation coefficients. -/
theorem hasLocallyAtomicAction_of_action_tsum
    (hsub : ∀ i, (S i).carrier ⊆ U.carrier)
    (hP : ∀ i, HasLocallyAtomicAction (S i) (P i))
    (hsum : ∀ f : SchwartzMap ℝ ℂ, T f = ∑' i, P i f) :
    HasLocallyAtomicAction U T :=
  atomicOnCarrier_hasLocallyAtomicAction U T
    (atomicOnCarrier_of_action_tsum U S P T hsub hP hsum)

/-- A summand supported away from the selected point annihilates the
common carrier's actual isolating Schwartz function. -/
theorem locallyAtomic_isolationAction_eq_zero_of_not_mem
    (hsub : ∀ i, (S i).carrier ⊆ U.carrier)
    (hP : ∀ i, HasLocallyAtomicAction (S i) (P i))
    (i : ι) (x : U.subtype) (hx : (x : ℝ) ∉ (S i).carrier) :
    P i (U.isolationSchwartz x) = 0 := by
  apply hasLocallyAtomicAction_atomicOnCarrier (S i) (P i) (hP i)
  intro y hy
  exact U.isolationSchwartz_of_mem_of_ne x (hsub i hy)
    (fun h => hx (h ▸ hy))

/-- At a point in one of the disjoint supports, the global isolation
coefficient equals that summand's own isolation coefficient exactly. -/
theorem isolationAction_tsum_eq
    (hsub : ∀ i, (S i).carrier ⊆ U.carrier)
    (hP : ∀ i, HasLocallyAtomicAction (S i) (P i))
    (hsum : ∀ f : SchwartzMap ℝ ℂ, T f = ∑' i, P i f)
    (hdisj : Pairwise fun i j => Disjoint (S i).carrier (S j).carrier)
    (i : ι) (x : (S i).subtype) :
    T (U.isolationSchwartz (LocallyFiniteCarrier.inclusion (hsub i) x)) =
      P i ((S i).isolationSchwartz x) := by
  rw [hsum]
  rw [tsum_eq_single i]
  · exact isolationAction_eq_of_carrier_subset (hsub i) (P i) (hP i) x
  · intro j hji
    apply locallyAtomic_isolationAction_eq_zero_of_not_mem U S P hsub hP j
    intro hxj
    exact Set.disjoint_left.mp (hdisj hji) hxj x.property

/-- A point of the common carrier outside every summand support has zero
coefficient in the actual series distribution. -/
theorem isolationAction_tsum_eq_zero_of_not_mem
    (hsub : ∀ i, (S i).carrier ⊆ U.carrier)
    (hP : ∀ i, HasLocallyAtomicAction (S i) (P i))
    (hsum : ∀ f : SchwartzMap ℝ ℂ, T f = ∑' i, P i f)
    (x : U.subtype) (hx : ∀ i, (x : ℝ) ∉ (S i).carrier) :
    T (U.isolationSchwartz x) = 0 := by
  rw [hsum]
  simp only [locallyAtomic_isolationAction_eq_zero_of_not_mem U S P hsub hP _ x
    (hx _), tsum_zero]

/-- The precise weighted strong-coefficient term on an included block
is recovered from the global distribution, without assuming summability. -/
theorem stronglyTemperedCoefficientTerm_tsum_inclusion
    (hsub : ∀ i, (S i).carrier ⊆ U.carrier)
    (hP : ∀ i, HasLocallyAtomicAction (S i) (P i))
    (hsum : ∀ f : SchwartzMap ℝ ℂ, T f = ∑' i, P i f)
    (hdisj : Pairwise fun i j => Disjoint (S i).carrier (S j).carrier)
    (i : ι) (N : ℕ) (x : (S i).subtype) :
    stronglyTemperedCoefficientTerm U N T (LocallyFiniteCarrier.inclusion (hsub i) x) =
      stronglyTemperedCoefficientTerm (S i) N (P i) x := by
  unfold stronglyTemperedCoefficientTerm
  rw [isolationAction_tsum_eq U S P T hsub hP hsum hdisj i x]
  rfl

/-- Every finite block atom set has exactly the same coefficient variation
after its coordinate-preserving inclusion into the global carrier. -/
theorem finiteSetVariation_tsum_inclusion
    (hsub : ∀ i, (S i).carrier ⊆ U.carrier)
    (hP : ∀ i, HasLocallyAtomicAction (S i) (P i))
    (hsum : ∀ f : SchwartzMap ℝ ℂ, T f = ∑' i, P i f)
    (hdisj : Pairwise fun i j => Disjoint (S i).carrier (S j).carrier)
    (i : ι) (E : Finset (S i).subtype) :
    (∑ x ∈ E.map (LocallyFiniteCarrier.inclusion (hsub i)),
      ‖T (U.isolationSchwartz x)‖) =
      ∑ x ∈ E, ‖P i ((S i).isolationSchwartz x)‖ := by
  classical
  simp only [Finset.sum_map, isolationAction_tsum_eq U S P T hsub hP hsum hdisj]

/-- Finite atom variation from any block is a genuine lower bound on
the full common-carrier finite-ball variation at the same physical radius. -/
theorem finiteSetVariation_le_finiteBallVariation_of_action_tsum
    (hsub : ∀ i, (S i).carrier ⊆ U.carrier)
    (hP : ∀ i, HasLocallyAtomicAction (S i) (P i))
    (hsum : ∀ f : SchwartzMap ℝ ℂ, T f = ∑' i, P i f)
    (hdisj : Pairwise fun i j => Disjoint (S i).carrier (S j).carrier)
    (i : ι) (E : Finset (S i).subtype) (R : ℝ)
    (hE : ∀ x ∈ E, |(x : ℝ)| ≤ R) :
    (∑ x ∈ E, ‖P i ((S i).isolationSchwartz x)‖) ≤
      ∑ x ∈ carrierFiniteBall U R, ‖T (U.isolationSchwartz x)‖ := by
  classical
  rw [← finiteSetVariation_tsum_inclusion U S P T hsub hP hsum hdisj i E]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact (mem_carrierFiniteBall_iff U R _).mpr (hE y hy)
  · intro x _ _
    exact norm_nonneg _

end

end MeyerGeneralProblem

module

public import MeyerGeneralProblem.UniformDiscrete.FiniteRows

@[expose] public section

/-! Selection of finitely many ORIGINAL separating rows while preserving a
nonzero specified functional. This proves compatibility with the surviving
line, which an arbitrary finite-kernel reduction does not give. -/

namespace MeyerGeneralProblem.UniformDiscrete

noncomputable section

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- A separating original row family cuts any finite-dimensional subspace
admitting `J ≠ 0` to exactly one line, still admitting `J ≠ 0`.
The new row is corrected using a vector in `ker J`, so compatibility is proved. -/
theorem exists_compatible_selected_line (row : I → V →ₗ[K] K)
    (hsep : ∀ v : V, (∀ i, row i v = 0) → v = 0)
    (H : Submodule K V) (J : V →ₗ[K] K)
    (hJ : ∃ v ∈ H, J v ≠ 0) :
    ∃ E : Finset I,
      Module.finrank K ↥(H ⊓ LinearMap.ker (selectedRowMap row E)) = 1 ∧
      ∃ v ∈ (H ⊓ LinearMap.ker (selectedRowMap row E)), J v ≠ 0 := by
  classical
  let P : ℕ → Prop := fun n => ∃ E : Finset I,
    Module.finrank K ↥(H ⊓ LinearMap.ker (selectedRowMap row E)) = n ∧
    ∃ v ∈ (H ⊓ LinearMap.ker (selectedRowMap row E)), J v ≠ 0
  have hP : ∃ n, P n := by
    obtain ⟨v, hv, hj⟩ := hJ
    refine ⟨_, ∅, rfl, v, ⟨hv, ?_⟩, hj⟩
    exact (mem_ker_selectedRowMap row ∅ v).mpr (by simp)
  obtain ⟨E, hdim, v, hv, hj⟩ := Nat.find_spec hP
  let A : Submodule K V := H ⊓ LinearMap.ker (selectedRowMap row E)
  have hker (w : V) (hw : w ∈ A) (hjw : J w = 0) : w = 0 := by
    by_contra hw0
    have hrow : ∃ i, row i w ≠ 0 := by
      by_contra hh
      push Not at hh
      exact hw0 (hsep w hh)
    obtain ⟨i, hi⟩ := hrow
    let B : Submodule K V := H ⊓ LinearMap.ker (selectedRowMap row (insert i E))
    have hle : B ≤ A := inf_le_inf_left H
      (ker_selectedRowMap_antitone row (Finset.subset_insert i E))
    let u : V := row i w • v - row i v • w
    have huA : u ∈ A := A.sub_mem (A.smul_mem _ hv) (A.smul_mem _ hw)
    have hui : row i u = 0 := by
      simp only [u, map_sub, map_smul, smul_eq_mul]
      ring
    have huB : u ∈ B := by
      refine ⟨huA.1, (mem_ker_selectedRowMap row (insert i E) u).mpr ?_⟩
      intro j hje
      rcases Finset.mem_insert.mp hje with rfl | hjE
      · exact hui
      · exact (mem_ker_selectedRowMap row E u).mp huA.2 j hjE
    have hJu : J u ≠ 0 := by
      simpa only [u, map_sub, map_smul, smul_eq_mul, hjw, mul_zero, sub_zero] using
        mul_ne_zero hi hj
    have hdimle : Module.finrank K A ≤ Module.finrank K B := by
      rw [hdim]
      exact Nat.find_min' hP ⟨insert i E, rfl, u, huB, hJu⟩
    have heq : B = A := Submodule.eq_of_le_of_finrank_le hle hdimle
    have hwB : w ∈ B := heq.symm ▸ hw
    exact hi ((mem_ker_selectedRowMap row (insert i E) w).mp hwB.2 i
      (Finset.mem_insert_self i E))
  let f : A →ₗ[K] K := J.comp A.subtype
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply hker _ (A.sub_mem a.property b.property)
    rw [map_sub]
    exact sub_eq_zero.mpr hab
  have hupper : Module.finrank K A ≤ 1 := by
    simpa using f.finrank_le_finrank_of_injective hf
  have hlower : 1 ≤ Module.finrank K A := Submodule.one_le_finrank_iff.mpr (by
    intro hbot
    have hvA : v ∈ A := hv
    have hv0 : v = 0 := by simpa only [hbot, Submodule.mem_bot] using hvA
    exact hj (hv0 ▸ J.map_zero))
  exact ⟨E, Nat.le_antisymm hupper hlower, v, hv, hj⟩

end

end MeyerGeneralProblem.UniformDiscrete

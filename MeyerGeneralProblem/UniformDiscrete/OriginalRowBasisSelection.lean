module

public import MeyerGeneralProblem.UniformDiscrete.CompatibleFiniteRows
public import MeyerGeneralProblem.UniformDiscrete.IndependentRowRank
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

@[expose] public section

/-! Known-size selection of ORIGINAL separating rows. The finite selector
has exactly the dual dimension; compatibility with a specified functional
is retained by selecting a basis from a previously compatible subsystem.
The selectors here are classical, not a computable root-isolation algorithm. -/

namespace MeyerGeneralProblem.UniformDiscrete

open Module

noncomputable section

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- A separating original row family contains exactly `finrank V` original
rows that still separate every vector, including the zero-dimensional case. -/
theorem exists_original_separating_rows_exact_card (row : I → V →ₗ[K] K)
    (hsep : ∀ v : V, (∀ i, row i v = 0) → v = 0) :
    ∃ E : Finset I, E.card = Module.finrank K V ∧
      ∀ v : V, (∀ i ∈ E, row i v = 0) → v = 0 := by
  classical
  have hspan : Submodule.span K (Set.range row) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro v hv
    have hh : ∃ i, row i v ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hv (hsep v hn)
    obtain ⟨i, hi⟩ := hh
    exact ⟨row i, ⟨i, rfl⟩, hi⟩
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K row
  let : Finite κ := hli.finite
  let : Fintype κ := Fintype.ofFinite κ
  let E : Finset I := Finset.univ.image a
  have hcard : E.card = Module.finrank K V := by
    have hdim := finrank_span_eq_card hli
    rw [hsp, hspan] at hdim
    simpa only [E, Finset.card_image_of_injective _ ha, Finset.card_univ,
      finrank_top, Subspace.dual_finrank_eq] using hdim.symm
  refine ⟨E, hcard, ?_⟩
  intro v hv
  have hk : v ∈ rowKernel (row ∘ a) := by
    intro i
    exact hv (a i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  rw [rowKernel_eq_dualCoannihilator, hsp, hspan,
    Submodule.dualCoannihilator_top, Submodule.mem_bot] at hk
  exact hk

/-- For ANY prescribed finite basis, some known-size tuple of ORIGINAL
evaluations has nonzero determinant. This pays the algebraic termination
obligation; effective root enumeration and certified interval search are separate. -/
theorem exists_original_evaluation_det_ne_zero {J : Type*} [Fintype J] [DecidableEq J]
    (row : I → V →ₗ[K] K) (hsep : ∀ v : V, (∀ i, row i v = 0) → v = 0)
    (b : Basis J K V) :
    ∃ E : Finset I, ∃ e : E ≃ J,
      E.card = Module.finrank K V ∧
      Matrix.det (fun i j : J => row (e.symm i) (b j)) ≠ 0 := by
  classical
  obtain ⟨E, hcard, hsepE⟩ := exists_original_separating_rows_exact_card row hsep
  have hcardJ : Fintype.card E = Fintype.card J := by
    rw [Fintype.card_coe, hcard, Module.finrank_eq_card_basis b]
  let e : E ≃ J := Fintype.equivOfCardEq hcardJ
  refine ⟨E, e, hcard, ?_⟩
  let M : Matrix J J K := fun i j => row (e.symm i) (b j)
  change M.det ≠ 0
  intro hz
  obtain ⟨x, hx, hMx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hz
  have hw : b.equivFun.symm x = 0 := hsepE _ (by
    intro i hi
    have hh := congrFun hMx (e ⟨i, hi⟩)
    simpa only [M, Matrix.mulVec, dotProduct, e.symm_apply_apply, Pi.zero_apply,
      Basis.equivFun_symm_apply, map_sum, map_smul, smul_eq_mul, mul_comm] using hh)
  exact hx (b.equivFun.symm.injective (by simpa only [map_zero] using hw))

/-- Exactly `finrank H - 1` original rows cut `H` to a line on which `J`
is nonzero. The count is proved on the complete original `H ∩ ker J`,
and the surviving witness comes from the original compatible subsystem. -/
theorem exists_compatible_selected_line_exact_card (row : I → V →ₗ[K] K)
    (hsep : ∀ v : V, (∀ i, row i v = 0) → v = 0)
    (H : Submodule K V) (J : V →ₗ[K] K)
    (hJ : ∃ v ∈ H, J v ≠ 0) :
    ∃ E : Finset I,
      E.card + 1 = Module.finrank K H ∧
      Module.finrank K ↥(H ⊓ LinearMap.ker (selectedRowMap row E)) = 1 ∧
      ∃ v ∈ (H ⊓ LinearMap.ker (selectedRowMap row E)), J v ≠ 0 := by
  classical
  obtain ⟨E₀, hdim₀, v, hv, hj⟩ := exists_compatible_selected_line row hsep H J hJ
  let W : Submodule K H := LinearMap.ker (J.comp H.subtype)
  let rowW : E₀ → W →ₗ[K] K := fun i => (row i).comp (H.subtype.comp W.subtype)
  have hspan₀ : H ⊓ LinearMap.ker (selectedRowMap row E₀) = Submodule.span K {v} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hdim₀ hv (by
      intro hz
      exact hj (hz ▸ J.map_zero))
  have hsepW : ∀ w : W, (∀ i, rowW i w = 0) → w = 0 := by
    intro w hw
    have hwA : (w.val : V) ∈ H ⊓ LinearMap.ker (selectedRowMap row E₀) :=
      ⟨w.val.property, (mem_ker_selectedRowMap row E₀ _).mpr
        (fun i hi => hw ⟨i, hi⟩)⟩
    rw [hspan₀] at hwA
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hwA
    have hcj : c * J v = 0 := by
      rw [← smul_eq_mul, ← map_smul, hc]
      exact w.property
    have hc0 : c = 0 := (mul_eq_zero.mp hcj).resolve_right hj
    apply Subtype.ext
    apply Subtype.ext
    change (w.val : V) = 0
    simpa only [hc0, zero_smul] using hc.symm
  obtain ⟨B, hcardB, hsepB⟩ := exists_original_separating_rows_exact_card rowW hsepW
  let E : Finset I := B.image Subtype.val
  have hEE : E ⊆ E₀ := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact j.property
  let A : Submodule K V := H ⊓ LinearMap.ker (selectedRowMap row E)
  have hker : ∀ w ∈ A, J w = 0 → w = 0 := by
    intro w hw hjw
    let wW : W := ⟨⟨w, hw.1⟩, hjw⟩
    have hwW : wW = 0 := hsepB wW (by
      intro i hi
      exact (mem_ker_selectedRowMap row E w).mp hw.2 i
        (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
    exact congrArg (fun z : W => (z.val : V)) hwW
  have hvA : v ∈ A := ⟨hv.1, ker_selectedRowMap_antitone row hEE hv.2⟩
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
    have hv0 : v = 0 := by simpa only [hbot, Submodule.mem_bot] using hvA
    exact hj (hv0 ▸ J.map_zero))
  have hJ₀ : J.comp H.subtype ≠ 0 := by
    intro hz
    obtain ⟨u, hu, hju⟩ := hJ
    exact hju (LinearMap.congr_fun hz ⟨u, hu⟩)
  have hdimW : Module.finrank K W + 1 = Module.finrank K H :=
    Module.Dual.finrank_ker_add_one_of_ne_zero hJ₀
  refine ⟨E, ?_, Nat.le_antisymm hupper hlower, v, hvA, hj⟩
  have hcardE : E.card = B.card := Finset.card_image_of_injective _ Subtype.val_injective
  omega

end

end MeyerGeneralProblem.UniformDiscrete

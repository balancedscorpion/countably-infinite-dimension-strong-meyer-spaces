module

public import MeyerGeneralProblem.Cardinal.Strong.FiniteSeriesProducts
public import MeyerGeneralProblem.Cardinal.Strong.ProductZCoefficients

@[expose] public section

/-! Exact degree regrouping of the complete original reciprocal product.
Every degree fiber is identified with its full finite composition box;
the original absolutely convergent multi-index sum is retained. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- The complete natural degree fiber equals the literal finite composition set. -/
def productZDegreeFiberEquiv (s k : ℕ) :
    {v : Fin s → ℕ // ∑ i : Fin s, v i = k} ≃ (productZCompositions s k) where
  toFun v := ⟨fun i => ⟨v.val i, by
    have hi : v.val i ≤ ∑ j : Fin s, v.val j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (v.val j)) (Finset.mem_univ i)
    rw [v.property] at hi
    omega⟩, by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, v.property⟩⟩
  invFun v := ⟨fun i => (v.val i : ℕ), (Finset.mem_filter.mp v.property).2⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    rfl
  right_inv v := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    rfl

/-- The actual original product reciprocal has exactly the literal finite Z coefficients. -/
theorem productZCoefficient_hasSum (s : ℕ) {Z W : ℂ}
    (hZ : ‖Z‖ < 1) (hW : ‖W‖ ≤ 1) :
    HasSum (fun k : ℕ => productZCoefficient s k W * Z ^ k)
      (productSheetPolynomial s Z W)⁻¹ := by
  let F : (Fin s → ℕ) → ℂ := fun v =>
    ∏ i : Fin s, sheetZCoefficient (productSheetParameter s i) (v i) W * Z ^ (v i)
  have hmulti : HasSum F (productSheetPolynomial s Z W)⁻¹ :=
    productSheetReciprocal_multi_hasSum s hZ hW
  have hfiber (k : ℕ) :
      (∑' v : {v : Fin s → ℕ // ∑ i : Fin s, v i = k}, F v.val) =
        productZCoefficient s k W * Z ^ k := by
    rw [← (productZDegreeFiberEquiv s k).symm.tsum_eq
      (fun v : {v : Fin s → ℕ // ∑ i : Fin s, v i = k} => F v.val), tsum_fintype]
    calc
      _ = ∑ v : (productZCompositions s k),
          (∏ i : Fin s, sheetZCoefficient (productSheetParameter s i) (v.val i) W) * Z ^ k := by
        apply Finset.sum_congr rfl
        intro v _
        change (∏ i : Fin s,
          sheetZCoefficient (productSheetParameter s i) (v.val i) W * Z ^ (v.val i : ℕ)) = _
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
        have hdegree : ∑ i : Fin s, (v.val i : ℕ) = k := (Finset.mem_filter.mp v.property).2
        rw [hdegree]
      _ = _ := by
        rw [← Finset.sum_mul]
        exact congrArg (fun u : ℂ => u * Z ^ k)
          (Finset.sum_coe_sort (productZCompositions s k)
            (fun v : Fin s → Fin (k + 1) =>
              ∏ i : Fin s, sheetZCoefficient (productSheetParameter s i) (v i) W))
  have hgroup := hmulti.tsum_fiberwise (fun v : Fin s → ℕ => ∑ i : Fin s, v i)
  exact hgroup.congr_fun (fun k => (hfiber k).symm)

end

end MeyerGeneralProblem.StrongParity

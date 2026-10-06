module

public import MeyerGeneralProblem.Cardinal.Strong.CompactOriginalBidiskCoefficients
public import MeyerGeneralProblem.Cardinal.Strong.FiniteTaylorProducts

@[expose] public section

/-! Finite ring arithmetic for ALL original compact reciprocal coefficients.
The two-index formula retains every degree composition.  The equality to the
actual Cauchy/derivative coefficients is proved internally.  A quantitative
binary-name error budget is a separate obligation. -/

namespace MeyerGeneralProblem.StrongParity

/-- A finite ring program for every original reciprocal coefficient. -/
def finiteOriginalUpperCoefficient {R : Type*} [CommRing R] {s : ℕ}
    (a : Fin s → R) (k n : ℕ) : R :=
  ∑ v ∈ productZCompositions s k,
    finiteTaylorProduct (fun i j => sheetFiniteWCoefficient (a i) (v i) j) n

theorem sheetFiniteWCoefficient_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (a : R) (k n : ℕ) :
    φ (sheetFiniteWCoefficient a k n) = sheetFiniteWCoefficient (φ a) k n := by
  induction k generalizing n with
  | zero => simp [sheetFiniteWCoefficient]
  | succ k ih =>
    induction n with
    | zero => simp [sheetFiniteWCoefficient]
    | succ n ihn => simp only [sheetFiniteWCoefficient, map_sub, map_add, map_mul, ihn, ih]

theorem finiteTaylorProduct_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) {s : ℕ} (f : Fin s → ℕ → R) (n : ℕ) :
    φ (finiteTaylorProduct f n) = finiteTaylorProduct (fun i j => φ (f i j)) n := by
  induction s generalizing n with
  | zero => by_cases hn : n = 0 <;> simp [finiteTaylorProduct, hn]
  | succ s ih =>
    simp only [finiteTaylorProduct, map_sum, map_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [ih]

/-- The same finite program commutes with every coefficient-ring map. -/
theorem finiteOriginalUpperCoefficient_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) {s : ℕ} (a : Fin s → R) (k n : ℕ) :
    φ (finiteOriginalUpperCoefficient a k n) =
      finiteOriginalUpperCoefficient (fun i => φ (a i)) k n := by
  simp only [finiteOriginalUpperCoefficient, map_sum, finiteTaylorProduct_map,
    sheetFiniteWCoefficient_map]

noncomputable section

/-- The finite formula equals EVERY actual compact original coefficient. -/
theorem finiteOriginalUpperCoefficient_eq_actual {s : ℕ}
    (block : CompactOriginalParameterBlock s) (k n : ℕ) :
    finiteOriginalUpperCoefficient (fun i => (block.parameter i : ℂ)) k n =
      compactOriginalUpperCoefficient block k n := by
  change _ = originalTaylorCoefficient (compactOriginalZCoefficient block k) n
  unfold compactOriginalZCoefficient
  rw [originalTaylorCoefficient_sum (productZCompositions s k)
    (fun v W => ∏ i : Fin s, sheetZCoefficient (block.parameter i) (v i) W) n
    (by
      intro v hv
      have hsheets : ∀ i : Fin s, AnalyticAt ℂ
          (sheetZCoefficient (block.parameter i) (v i)) 0 :=
        fun i => sheetZCoefficient_analyticAt_zero (block.parameter i) (v i)
      apply AnalyticAt.contDiffAt
      fun_prop)]
  unfold finiteOriginalUpperCoefficient
  apply Finset.sum_congr rfl
  intro v hv
  rw [← finiteTaylorProduct_eq_taylor
    (fun i W => sheetZCoefficient (block.parameter i) (v i) W)
    (fun i => sheetZCoefficient_analyticAt_zero (block.parameter i) (v i)) n]
  congr 1
  funext i j
  exact sheetFiniteWCoefficient_eq_taylor (block.parameter i) (v i) j

/-- No imaginary approximation is needed for the original reciprocal coefficients. -/
theorem compactOriginalUpperCoefficient_eq_real_finite_formula {s : ℕ}
    (block : CompactOriginalParameterBlock s) (k n : ℕ) :
    compactOriginalUpperCoefficient block k n =
      ((finiteOriginalUpperCoefficient (R := ℝ) block.parameter k n : ℝ) : ℂ) := by
  rw [← finiteOriginalUpperCoefficient_eq_actual]
  exact (finiteOriginalUpperCoefficient_map Complex.ofRealHom block.parameter k n).symm

end

end MeyerGeneralProblem.StrongParity

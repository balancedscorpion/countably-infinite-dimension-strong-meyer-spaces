module

public import MeyerGeneralProblem.Cardinal.Strong.QuotientTubeSeries
public import Mathlib.Analysis.Complex.RemovableSingularity

@[expose] public section

/-! A literal continuous principal-part remainder at a simple zero.
The holomorphy and derivative assumptions are discharged on the original
entire product in the next module; no boundary-jump identity is assumed. -/

namespace MeyerGeneralProblem.StrongParity

noncomputable section

/-- Remove the literal simple zero factor from the denominator. -/
def simplePoleRegularFactor (f g : ℂ → ℂ) (a z : ℂ) : ℂ := g z / dslope f a z

/-- The actual divided difference of the regular factor at the pole. -/
def simplePoleRemainder (f g : ℂ → ℂ) (a : ℂ) : ℂ → ℂ :=
  dslope (simplePoleRegularFactor f g a) a

theorem simplePoleRegularFactor_differentiableAt (f g : ℂ → ℂ) (a : ℂ)
    (hf : Differentiable ℂ f) (hg : DifferentiableAt ℂ g a) (hdf : deriv f a ≠ 0) :
    DifferentiableAt ℂ (simplePoleRegularFactor f g a) a := by
  have hds : Differentiable ℂ (dslope f a) :=
    differentiableOn_univ.mp ((Complex.differentiableOn_dslope (s := Set.univ) (c := a)
      Filter.univ_mem).mpr hf.differentiableOn)
  exact hg.div (hds a) (by simpa only [dslope_same] using hdf)

theorem simplePoleRemainder_continuousAt (f g : ℂ → ℂ) (a : ℂ)
    (hf : Differentiable ℂ f) (hg : DifferentiableAt ℂ g a) (hdf : deriv f a ≠ 0) :
    ContinuousAt (simplePoleRemainder f g a) a :=
  continuousAt_dslope_same.mpr (simplePoleRegularFactor_differentiableAt f g a hf hg hdf)

/-- The actual open domain on which the removed denominator has no further zero. -/
def simplePoleRegularDomain (f : ℂ → ℂ) (a : ℂ) : Set ℂ := {z | dslope f a z ≠ 0}

theorem simplePoleRegularDomain_isOpen (f : ℂ → ℂ) (a : ℂ)
    (hf : Differentiable ℂ f) : IsOpen (simplePoleRegularDomain f a) := by
  have hds : Differentiable ℂ (dslope f a) :=
    differentiableOn_univ.mp ((Complex.differentiableOn_dslope (s := Set.univ) (c := a)
      Filter.univ_mem).mpr hf.differentiableOn)
  exact isOpen_ne_fun hds.continuous continuous_const

/-- The principal-part remainder is genuinely continuous on a whole open
neighborhood, allowing a bounded integrated remainder argument. -/
theorem simplePoleRemainder_continuousOn (f g : ℂ → ℂ) (a : ℂ)
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (hdf : deriv f a ≠ 0) :
    ContinuousOn (simplePoleRemainder f g a) (simplePoleRegularDomain f a) := by
  have hds : Differentiable ℂ (dslope f a) :=
    differentiableOn_univ.mp ((Complex.differentiableOn_dslope (s := Set.univ) (c := a)
      Filter.univ_mem).mpr hf.differentiableOn)
  have hreg : DifferentiableOn ℂ (simplePoleRegularFactor f g a)
      (simplePoleRegularDomain f a) :=
    hg.differentiableOn.div hds.differentiableOn (fun _ hz => hz)
  have ha : a ∈ simplePoleRegularDomain f a := by
    simpa only [simplePoleRegularDomain, Set.mem_ofPred_eq, dslope_same] using hdf
  exact ((Complex.differentiableOn_dslope
    ((simplePoleRegularDomain_isOpen f a hf).mem_nhds ha)).mpr hreg).continuousOn

theorem complex_dslope_measurable (f : ℂ → ℂ) (a : ℂ) (hf : Measurable f) :
    Measurable (dslope f a) := by
  classical
  have heq : dslope f a = fun z : ℂ =>
      if z = a then deriv f a else (f z - f a) / (z - a) := by
    funext z
    by_cases hz : z = a
    · subst z
      simp only [dslope_same, ite_true]
    · simp only [hz, ite_false, dslope_of_ne f hz, slope_def_field]
  rw [heq]
  exact Measurable.ite (measurableSet_singleton a) measurable_const
    ((hf.sub_const (f a)).div (measurable_id.sub_const a))

theorem simplePoleRemainder_measurable (f g : ℂ → ℂ) (a : ℂ)
    (hf : Measurable f) (hg : Measurable g) : Measurable (simplePoleRemainder f g a) :=
  complex_dslope_measurable _ a (hg.div (complex_dslope_measurable f a hf))

/-- The quotient is its literal principal part plus the actual continuous remainder. -/
theorem simplePoleRemainder_identity (f g : ℂ → ℂ) (a : ℂ) (hfa : f a = 0)
    {z : ℂ} (hz : z ≠ a) :
    g z / f z = (g a / deriv f a) / (z - a) + simplePoleRemainder f g a z := by
  have hfactor : f z = (z - a) * dslope f a z := by
    simpa only [smul_eq_mul, hfa, sub_zero] using (sub_smul_dslope f a z).symm
  have hquot : g z / f z = simplePoleRegularFactor f g a z / (z - a) := by
    rw [hfactor]
    unfold simplePoleRegularFactor
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hquot, simplePoleRemainder, dslope_of_ne _ hz, slope_def_field]
  have ha : simplePoleRegularFactor f g a a = g a / deriv f a := by
    simp only [simplePoleRegularFactor, dslope_same]
  rw [ha, ← add_div]
  congr 1
  ring

end

end MeyerGeneralProblem.StrongParity

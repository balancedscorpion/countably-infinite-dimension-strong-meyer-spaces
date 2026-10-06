module

public import MeyerGeneralProblem.Cardinal.Strong.RationalExclusionSearch

@[expose] public section

/-! Ordinary positive-margin interval shrinking for the actual original exclusions. -/

namespace MeyerGeneralProblem.StrongParity

/-- The finite rational minimum margin, with a positive fallback for the empty list. -/
def rationalExclusionMargin (names : ℕ → ℕ → ℚ) (m : ℕ) (q : ℚ) (p : ℕ) :
    List ComputedRootExclusion → ℚ
  | [] => 1
  | code :: codes => min (code.margin names m q p) (rationalExclusionMargin names m q p codes)

/-- The rational radius paying the slot, prescribed binary width and actual 8*m residual bound. -/
def rationalExclusionRadius (codes : List ComputedRootExclusion) (names : ℕ → ℕ → ℚ)
    (m : ℕ) (u v q : ℚ) (p stage : ℕ) : ℚ :=
  min ((q - u) / 2) (min ((v - q) / 2) (min (rationalBinaryRadius stage / 2)
    (rationalExclusionMargin names m q p codes / (16 * (m + 1)))))

/-- The ordinary rational interval around the certified center. -/
def rationalExclusionInterval (codes : List ComputedRootExclusion) (names : ℕ → ℕ → ℚ)
    (m : ℕ) (u v q : ℚ) (p stage : ℕ) : ℚ × ℚ :=
  let radius := rationalExclusionRadius codes names m u v q p stage
  (q - radius, q + radius)

/-- Decode the actual search output, with an unused totalization on unsuccessful codes. -/
def rationalExclusionSearchData (codes : List ComputedRootExclusion) (names : ℕ → ℕ → ℚ)
    (values : ℕ → ℝ) (hname : ∀ i p, |(names i p : ℝ) - values i| ≤ 1 / (2 : ℝ) ^ p)
    (m : ℕ) (hm : 0 < m) (u v : ℚ) (hu : 0 < u) (hv : v ≤ 1 / 2) (huv : u < v) : ℚ × ℕ :=
  (Encodable.decode (rationalExclusionSearch codes names values hname m hm u v hu hv huv)).getD (0, 0)

/-- The actual ordinary finite safe-interval program, using the proved terminating search. -/
def rationalSafeExclusionInterval (codes : List ComputedRootExclusion) (names : ℕ → ℕ → ℚ)
    (values : ℕ → ℝ) (hname : ∀ i p, |(names i p : ℝ) - values i| ≤ 1 / (2 : ℝ) ^ p)
    (m : ℕ) (hm : 0 < m) (u v : ℚ) (hu : 0 < u) (hv : v ≤ 1 / 2) (huv : u < v)
    (stage : ℕ) : ℚ × ℚ :=
  let data := rationalExclusionSearchData codes names values hname m hm u v hu hv huv
  rationalExclusionInterval codes names m u v data.1 data.2 stage

noncomputable section

/-- Every successful finite certificate family has a strictly positive computed minimum margin. -/
theorem rationalExclusionMargin_pos (codes : List ComputedRootExclusion) (names : ℕ → ℕ → ℚ)
    (m : ℕ) (q : ℚ) (p : ℕ) (hc : ∀ code ∈ codes, code.certificate names m q p = true) :
    0 < rationalExclusionMargin names m q p codes := by
  induction codes with
  | nil => norm_num [rationalExclusionMargin]
  | cons code codes ih =>
      apply lt_min
      · exact (code.certificate_iff names m q p).mp (hc code List.mem_cons_self)
      · exact ih (fun c h => hc c (List.mem_cons_of_mem _ h))

/-- The computed finite minimum bounds every listed rational margin from below. -/
theorem rationalExclusionMargin_le (codes : List ComputedRootExclusion) (names : ℕ → ℕ → ℚ)
    (m : ℕ) (q : ℚ) (p : ℕ) {code : ComputedRootExclusion} (hc : code ∈ codes) :
    rationalExclusionMargin names m q p codes ≤ code.margin names m q p := by
  induction codes with
  | nil => simp only [List.not_mem_nil] at hc
  | cons c codes ih =>
      rcases List.mem_cons.mp hc with he | ht
      · subst code
        exact min_le_left _ _
      · exact (min_le_right _ _).trans (ih ht)

/-- The emitted radius is positive and pays all four explicit rational bounds. -/
theorem rationalExclusionRadius_bounds (codes : List ComputedRootExclusion) (names : ℕ → ℕ → ℚ)
    (m : ℕ) (u v q : ℚ) (p stage : ℕ) (hqu : u < q) (hqv : q < v)
    (hc : ∀ code ∈ codes, code.certificate names m q p = true) :
    0 < rationalExclusionRadius codes names m u v q p stage ∧
    rationalExclusionRadius codes names m u v q p stage ≤ (q - u) / 2 ∧
    rationalExclusionRadius codes names m u v q p stage ≤ (v - q) / 2 ∧
    rationalExclusionRadius codes names m u v q p stage ≤ rationalBinaryRadius stage / 2 ∧
    rationalExclusionRadius codes names m u v q p stage ≤
      rationalExclusionMargin names m q p codes / (16 * (m + 1)) := by
  have hm := rationalExclusionMargin_pos codes names m q p hc
  dsimp [rationalExclusionRadius]
  refine ⟨lt_min (by linarith) (lt_min (by linarith) (lt_min (by
    dsimp [rationalBinaryRadius]; positivity) (by positivity))), min_le_left _ _, ?_⟩
  refine ⟨(min_le_right _ _).trans (min_le_left _ _), ?_⟩
  exact ⟨(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))⟩

/-- Every certified interval is nondegenerate, strictly inside its slot and has prescribed width. -/
theorem rationalExclusionInterval_geometry (codes : List ComputedRootExclusion) (names : ℕ → ℕ → ℚ)
    (m : ℕ) (u v q : ℚ) (p stage : ℕ) (hqu : u < q) (hqv : q < v)
    (hc : ∀ code ∈ codes, code.certificate names m q p = true) :
    u < (rationalExclusionInterval codes names m u v q p stage).1 ∧
    (rationalExclusionInterval codes names m u v q p stage).1 <
      (rationalExclusionInterval codes names m u v q p stage).2 ∧
    (rationalExclusionInterval codes names m u v q p stage).2 < v ∧
    (rationalExclusionInterval codes names m u v q p stage).2 -
      (rationalExclusionInterval codes names m u v q p stage).1 ≤ rationalBinaryRadius stage := by
  have h := rationalExclusionRadius_bounds codes names m u v q p stage hqu hqv hc
  dsimp [rationalExclusionInterval]
  exact ⟨by linarith [h.1, h.2.1], by linarith [h.1],
    by linarith [h.1, h.2.2.1], by linarith [h.2.2.2.1]⟩

/-- Every point of a computed certified interval avoids ALL literal original equations. -/
theorem rationalExclusionInterval_protects (codes : List ComputedRootExclusion)
    (names : ℕ → ℕ → ℚ) (values : ℕ → ℝ)
    (hname : ∀ i p, |(names i p : ℝ) - values i| ≤ 1 / (2 : ℝ) ^ p)
    (m : ℕ) (u v q : ℚ) (p stage : ℕ) (hu : 0 < u) (hv : v ≤ 1 / 2)
    (hqu : u < q) (hqv : q < v) (hc : ∀ code ∈ codes, code.certificate names m q p = true)
    {a : ℝ} (ha : a ∈ Set.Icc
      ((rationalExclusionInterval codes names m u v q p stage).1 : ℝ)
      ((rationalExclusionInterval codes names m u v q p stage).2 : ℝ)) :
    ∀ code ∈ codes, (code.semantic values).residual m a ≠ 0 := by
  let r := rationalExclusionRadius codes names m u v q p stage
  let margin := rationalExclusionMargin names m q p codes
  have hb := rationalExclusionRadius_bounds codes names m u v q p stage hqu hqv hc
  have hg := rationalExclusionInterval_geometry codes names m u v q p stage hqu hqv hc
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (hu.trans hqu).le
  have hq2 : (q : ℝ) ≤ 1 / 2 := by
    have h : (q : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast hqv.le.trans hv
    norm_num at h
    exact h
  have ha0 : (0 : ℝ) ≤ a := by
    have h : (u : ℝ) < ((rationalExclusionInterval codes names m u v q p stage).1 : ℝ) := by
      exact_mod_cast hg.1
    have huR : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu
    linarith [ha.1]
  have ha2 : a ≤ 1 / 2 := by
    have h : ((rationalExclusionInterval codes names m u v q p stage).2 : ℝ) < (v : ℝ) := by
      exact_mod_cast hg.2.2.1
    have hvR : (v : ℝ) ≤ 1 / 2 := by
      have hh : (v : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast hv
      norm_num at hh
      exact hh
    linarith [ha.2]
  have hd : |a - (q : ℝ)| ≤ (r : ℝ) := by
    simp only [rationalExclusionInterval, Rat.cast_sub, Rat.cast_add] at ha
    exact abs_le.mpr ⟨by linarith [ha.1], by linarith [ha.2]⟩
  have hr : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hb.1
  have hcap : (r : ℝ) * (16 * ((m : ℝ) + 1)) ≤ (margin : ℝ) := by
    have h := (le_div_iff₀ (by positivity : (0 : ℚ) < 16 * (m + 1))).mp hb.2.2.2.2
    exact_mod_cast h
  have hsmall : 8 * (m : ℝ) * (r : ℝ) < (margin : ℝ) := by
    have hn : (0 : ℝ) ≤ m := by positivity
    nlinarith [mul_nonneg hn hr.le]
  intro code hcode
  have hm : (margin : ℝ) ≤ (code.margin names m q p : ℝ) := by
    exact_mod_cast rationalExclusionMargin_le codes names m q p hcode
  apply (code.semantic values).ne_of_radius_margin m ⟨hq0, hq2⟩ ⟨ha0, ha2⟩ hd
  exact hsmall.trans_le (hm.trans (code.margin_le names values hname m (hu.trans hqu).le
    (hqv.le.trans hv) p))

/-- The actual search-and-shrink program returns a nondegenerate safe interval of binary width. -/
theorem rationalSafeExclusionInterval_spec (codes : List ComputedRootExclusion)
    (names : ℕ → ℕ → ℚ) (values : ℕ → ℝ)
    (hname : ∀ i p, |(names i p : ℝ) - values i| ≤ 1 / (2 : ℝ) ^ p)
    (m : ℕ) (hm : 0 < m) (u v : ℚ) (hu : 0 < u) (hv : v ≤ 1 / 2) (huv : u < v)
    (stage : ℕ) :
    let s := rationalSafeExclusionInterval codes names values hname m hm u v hu hv huv stage
    u < s.1 ∧ s.1 < s.2 ∧ s.2 < v ∧ s.2 - s.1 ≤ rationalBinaryRadius stage ∧
      ∀ a ∈ Set.Icc (s.1 : ℝ) (s.2 : ℝ), ∀ code ∈ codes,
        (code.semantic values).residual m a ≠ 0 := by
  obtain ⟨q, p, hd, hqu, hqv, hc⟩ := rationalExclusionProbe_spec codes names m u v
    (rationalExclusionSearch_success codes names values hname m hm u v hu hv huv)
  have hdata : rationalExclusionSearchData codes names values hname m hm u v hu hv huv = (q, p) := by
    simp only [rationalExclusionSearchData, hd, Option.getD_some]
  simp only [rationalSafeExclusionInterval, hdata]
  have hg := rationalExclusionInterval_geometry codes names m u v q p stage hqu hqv hc
  exact ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2,
    fun a ha => rationalExclusionInterval_protects codes names values hname m u v q p stage
      hu hv hqu hqv hc ha⟩

end

end MeyerGeneralProblem.StrongParity

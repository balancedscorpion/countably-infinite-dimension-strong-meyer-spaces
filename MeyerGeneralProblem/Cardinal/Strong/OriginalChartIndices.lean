module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalChartBounds

@[expose] public section

/-! The actual four projective charts act by signed integer coordinates and
reflection at the fixed native degree. No coefficient is rephased. -/
namespace MeyerGeneralProblem.StrongParity
noncomputable section

/-- Each Boolean selects whether its native coordinate is reversed. -/
def originalChartNativeIndex (c : Bool × Bool) (d : ℕ) (n : ℕ × ℕ) : ℕ × ℕ :=
  (if c.1 then d - n.1 else n.1, if c.2 then d - n.2 else n.2)

/-- The globally signed coordinate homomorphism of the selected chart. -/
def originalChartIntegerSign (c : Bool × Bool) : (ℤ × ℤ) →+ (ℤ × ℤ) where
  toFun n := (if c.1 then -n.1 else n.1, if c.2 then -n.2 else n.2)
  map_zero' := by rcases c with ⟨a, b⟩; cases a <;> cases b <;> simp
  map_add' n m := by
    rcases c with ⟨a, b⟩
    cases a <;> cases b <;> apply Prod.ext <;> simp [add_comm]

/-- The monomial shift uses the complete fixed degree in each reversed coordinate. -/
def originalChartIntegerShift (c : Bool × Bool) (d : ℕ) : ℤ × ℤ :=
  (if c.1 then (d : ℤ) else 0, if c.2 then (d : ℤ) else 0)

/-- Reflection on the whole integer lattice, with no positivity truncation. -/
def originalChartIntegerIndex (c : Bool × Bool) (d : ℕ) (n : ℤ × ℤ) : ℤ × ℤ :=
  originalChartIntegerShift c d + originalChartIntegerSign c n

/-- Signed native chart coordinates preserve addition and invert themselves. -/
theorem originalChartIntegerSign_involutive (c : Bool × Bool) :
    Function.Involutive (originalChartIntegerSign c) := by
  intro n
  rcases c with ⟨a, b⟩
  cases a <;> cases b <;> simp [originalChartIntegerSign]

/-- The fixed integer reflection inverts itself on EVERY original integer row. -/
theorem originalChartIntegerIndex_involutive (c : Bool × Bool) (d : ℕ) :
    Function.Involutive (originalChartIntegerIndex c d) := by
  intro n
  rcases c with ⟨a, b⟩
  cases a <;> cases b <;> apply Prod.ext <;>
    simp [originalChartIntegerIndex, originalChartIntegerShift, originalChartIntegerSign]

/-- Integer chart reflection is globally injective, before pulling back positive rows. -/
theorem originalChartIntegerIndex_injective (c : Bool × Bool) (d : ℕ) :
    Function.Injective (originalChartIntegerIndex c d) :=
  (originalChartIntegerIndex_involutive c d).injective

/-- Fixed native reflection keeps both coordinates in the PROVED whole square. -/
theorem originalChartNativeIndex_inSquare (c : Bool × Bool) (d : ℕ) (n : ℕ × ℕ)
    (hn : n.1 ≤ d ∧ n.2 ≤ d) :
    (originalChartNativeIndex c d n).1 ≤ d ∧ (originalChartNativeIndex c d n).2 ≤ d := by
  rcases c with ⟨a, b⟩
  cases a <;> cases b <;> simp [originalChartNativeIndex, hn]

/-- Positive chart reflection inverts itself ONLY under its explicit fixed square bounds. -/
theorem originalChartNativeIndex_involutive_on_square (c : Bool × Bool) (d : ℕ) (n : ℕ × ℕ)
    (hn : n.1 ≤ d ∧ n.2 ≤ d) :
    originalChartNativeIndex c d (originalChartNativeIndex c d n) = n := by
  rcases c with ⟨a, b⟩
  cases a <;> cases b <;> simp [originalChartNativeIndex, Nat.sub_sub_self hn.1, Nat.sub_sub_self hn.2]

/-- The actual native cast commutes with reflection at the fixed whole square bound. -/
theorem originalChartNativeIndex_integer (c : Bool × Bool) (d : ℕ) (n : ℕ × ℕ)
    (hn : n.1 ≤ d ∧ n.2 ≤ d) :
    originalNativeIntegerEmbedding (originalChartNativeIndex c d n) =
      originalChartIntegerIndex c d (originalNativeIntegerEmbedding n) := by
  change (((if c.1 then d - n.1 else n.1 : ℕ) : ℤ),
    ((if c.2 then d - n.2 else n.2 : ℕ) : ℤ)) =
    ((if c.1 then (d : ℤ) else 0) + (if c.1 then -(n.1 : ℤ) else (n.1 : ℤ)),
      (if c.2 then (d : ℤ) else 0) + (if c.2 then -(n.2 : ℤ) else (n.2 : ℤ)))
  rcases c with ⟨a, b⟩
  cases a <;> cases b <;> simp [Int.ofNat_sub hn.1, Int.ofNat_sub hn.2, sub_eq_add_neg]

/-- Whole-degree shifts add under genuine polynomial multiplication. -/
theorem originalChartIntegerShift_add (c : Bool × Bool) (d e : ℕ) :
    originalChartIntegerShift c (d + e) = originalChartIntegerShift c d + originalChartIntegerShift c e := by
  rcases c with ⟨a, b⟩
  cases a <;> cases b <;> simp [originalChartIntegerShift, Nat.cast_add]

end
end MeyerGeneralProblem.StrongParity

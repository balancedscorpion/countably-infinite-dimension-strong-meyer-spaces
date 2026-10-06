module

public import MeyerGeneralProblem.Cardinal.Strong.ScheduledOriginalFutureWindowBounds

@[expose] public section

/-! Causal protected-window recursion. The recursion is ordinary when the radius selector is ordinary. -/
namespace MeyerGeneralProblem.StrongParity

/-- The causal finite history obtained by writing only the next bound, preserving every earlier entry. -/
def originalProtectedWindowHistory (next : (ℕ → ℕ) → ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0 => fun _ => 0
  | n + 1 => Function.update (originalProtectedWindowHistory next n) n
      (max (originalProtectedWindowHistory next n (n - 1) + 1) (next (originalProtectedWindowHistory next n) n))

/-- The completed natural bound chosen at its own finite stage. -/
def originalProtectedWindowBound (next : (ℕ → ℕ) → ℕ → ℕ) (n : ℕ) : ℕ :=
  originalProtectedWindowHistory next (n + 1) n

/-- Each actual bound dominates both the previous bound and its own requested radius. -/
theorem originalProtectedWindowBound_eq (next : (ℕ → ℕ) → ℕ → ℕ) (n : ℕ) :
    originalProtectedWindowBound next n =
      max (originalProtectedWindowHistory next n (n - 1) + 1) (next (originalProtectedWindowHistory next n) n) := by
  simp only [originalProtectedWindowBound, originalProtectedWindowHistory, Function.update_self]

/-- EVERY finite history equals the completed history on its entire earlier prefix. -/
theorem originalProtectedWindowHistory_prefix (next : (ℕ → ℕ) → ℕ → ℕ) (k j : ℕ) (hj : j < k) :
    originalProtectedWindowHistory next k j = originalProtectedWindowBound next j := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases he : j = k
    · subst j
      rfl
    · rw [originalProtectedWindowHistory, Function.update_of_ne he]
      exact ih (by omega)

/-- The internally constructed protected bounds strictly increase. -/
theorem originalProtectedWindowBound_strictMono (next : (ℕ → ℕ) → ℕ → ℕ) :
    StrictMono (originalProtectedWindowBound next) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [originalProtectedWindowBound_eq next (n + 1)]
  simp only [Nat.add_sub_cancel]
  exact (Nat.lt_succ_self (originalProtectedWindowBound next n)).trans_le (le_max_left _ _)

/-- EVERY future bound protects the radius selected from an earlier finite history. -/
theorem originalProtectedWindowBound_future (next : (ℕ → ℕ) → ℕ → ℕ) (k n : ℕ) (hkn : k ≤ n) :
    next (originalProtectedWindowHistory next k) k ≤ originalProtectedWindowBound next n := by
  have hk : next (originalProtectedWindowHistory next k) k ≤ originalProtectedWindowBound next k := by
    rw [originalProtectedWindowBound_eq]
    exact le_max_right _ _
  exact hk.trans ((originalProtectedWindowBound_strictMono next).monotone hkn)

end MeyerGeneralProblem.StrongParity

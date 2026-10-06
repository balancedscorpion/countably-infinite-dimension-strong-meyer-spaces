module

public import MeyerGeneralProblem.Cardinal.Strong.PrivatePrimeSchedule

@[expose] public section

/-!
# Complete ordinary allocation of contiguous original sheets

For any positive block lengths, cumulative offsets partition ALL natural sheet
indices. The ordinary least-index search has an internal termination proof;
its inverse labels are computed by natural subtraction. No selected subfamily
or supplied ownership certificate enters the allocation.
-/

namespace MeyerGeneralProblem.StrongParity

/-- Ordinary cumulative offsets of the complete block-length sequence. -/
def originalBlockSheetOffset (sizes : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => originalBlockSheetOffset sizes n + sizes n

/-- Positive complete block lengths give strictly increasing offsets. -/
theorem originalBlockSheetOffset_strictMono (sizes : ℕ → ℕ) (hpos : ∀ n, 0 < sizes n) :
    StrictMono (originalBlockSheetOffset sizes) := by
  apply strictMono_nat_of_lt_succ
  intro n
  change originalBlockSheetOffset sizes n < originalBlockSheetOffset sizes n + sizes n
  exact Nat.lt_add_of_pos_right (hpos n)

/-- Offsets grow at least as fast as their natural index. -/
theorem originalBlockSheetOffset_index_le (sizes : ℕ → ℕ) (hpos : ∀ n, 0 < sizes n) (n : ℕ) :
    n ≤ originalBlockSheetOffset sizes n := by
  have h := (originalBlockSheetOffset_strictMono sizes hpos).add_le_nat n 0
  simpa only [Nat.add_zero, originalBlockSheetOffset] using h

/-- Every natural sheet is below some complete block endpoint. -/
theorem originalBlockSheetOwner_exists (sizes : ℕ → ℕ) (hpos : ∀ n, 0 < sizes n) (q : ℕ) :
    ∃ n : ℕ, q < originalBlockSheetOffset sizes (n + 1) :=
  ⟨q, (Nat.lt_succ_self q).trans_le (originalBlockSheetOffset_index_le sizes hpos (q + 1))⟩

/-- Ordinary terminating least-index search for the unique owner of EVERY sheet. -/
def originalBlockSheetOwner (sizes : ℕ → ℕ) (hpos : ∀ n, 0 < sizes n) (q : ℕ) : ℕ :=
  Nat.find (originalBlockSheetOwner_exists sizes hpos q)

/-- The computed owner contains the sheet in its full half-open block interval. -/
theorem originalBlockSheetOwner_spec (sizes : ℕ → ℕ) (hpos : ∀ n, 0 < sizes n) (q : ℕ) :
    originalBlockSheetOffset sizes (originalBlockSheetOwner sizes hpos q) ≤ q ∧
      q < originalBlockSheetOffset sizes (originalBlockSheetOwner sizes hpos q + 1) := by
  refine ⟨?_, Nat.find_spec (originalBlockSheetOwner_exists sizes hpos q)⟩
  cases he : originalBlockSheetOwner sizes hpos q with
  | zero => simp only [originalBlockSheetOffset]; exact Nat.zero_le q
  | succ n =>
    have hn : n < originalBlockSheetOwner sizes hpos q := by omega
    have h := Nat.find_min (originalBlockSheetOwner_exists sizes hpos q) hn
    change ¬ q < originalBlockSheetOffset sizes (n + 1) at h
    omega

/-- Containment in ANY full block interval determines the searched owner uniquely. -/
theorem originalBlockSheetOwner_eq_iff (sizes : ℕ → ℕ) (hpos : ∀ n, 0 < sizes n) (q n : ℕ) :
    originalBlockSheetOwner sizes hpos q = n ↔
      originalBlockSheetOffset sizes n ≤ q ∧ q < originalBlockSheetOffset sizes (n + 1) := by
  constructor
  · intro he
    simpa only [he] using originalBlockSheetOwner_spec sizes hpos q
  · rintro ⟨hlo, hhi⟩
    have hs := originalBlockSheetOwner_spec sizes hpos q
    have hmono := (originalBlockSheetOffset_strictMono sizes hpos).monotone
    apply le_antisymm
    · by_contra hn
      have h := hmono (by omega : n + 1 ≤ originalBlockSheetOwner sizes hpos q)
      omega
    · by_contra hn
      have h := hmono (by omega : originalBlockSheetOwner sizes hpos q + 1 ≤ n)
      omega

/-- Flatten a complete block label to its global natural sheet index. -/
def originalBlockSheetIndex (sizes : ℕ → ℕ) (label : Σ n, Fin (sizes n)) : ℕ :=
  originalBlockSheetOffset sizes label.1 + label.2.val

/-- Every flattened label is assigned to its original block by the actual owner search. -/
theorem originalBlockSheetOwner_index (sizes : ℕ → ℕ) (hpos : ∀ n, 0 < sizes n)
    (label : Σ n, Fin (sizes n)) :
    originalBlockSheetOwner sizes hpos (originalBlockSheetIndex sizes label) = label.1 := by
  apply (originalBlockSheetOwner_eq_iff sizes hpos _ _).mpr
  dsimp [originalBlockSheetIndex]
  change originalBlockSheetOffset sizes label.1 ≤ originalBlockSheetOffset sizes label.1 + label.2.val ∧
    originalBlockSheetOffset sizes label.1 + label.2.val < originalBlockSheetOffset sizes label.1 + sizes label.1
  exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left label.2.isLt _⟩

/-- Compute the full block-and-sheet label for EVERY natural sheet index. -/
def originalBlockSheetLabel (sizes : ℕ → ℕ) (hpos : ∀ n, 0 < sizes n) (q : ℕ) :
    Σ n, Fin (sizes n) :=
  ⟨originalBlockSheetOwner sizes hpos q,
    ⟨q - originalBlockSheetOffset sizes (originalBlockSheetOwner sizes hpos q), by
      have h := originalBlockSheetOwner_spec sizes hpos q
      rw [originalBlockSheetOffset] at h
      omega⟩⟩

/-- Flattening the computed label recovers EVERY original natural sheet. -/
theorem originalBlockSheetIndex_label (sizes : ℕ → ℕ) (hpos : ∀ n, 0 < sizes n) (q : ℕ) :
    originalBlockSheetIndex sizes (originalBlockSheetLabel sizes hpos q) = q := by
  dsimp [originalBlockSheetIndex, originalBlockSheetLabel]
  have h := (originalBlockSheetOwner_spec sizes hpos q).1
  omega

/-- The complete flattened label map is injective, including across distinct blocks. -/
theorem originalBlockSheetIndex_injective (sizes : ℕ → ℕ) (hpos : ∀ n, 0 < sizes n) :
    Function.Injective (originalBlockSheetIndex sizes) := by
  rintro ⟨n, i⟩ ⟨m, j⟩ he
  have hn := originalBlockSheetOwner_index sizes hpos ⟨n, i⟩
  have hm := originalBlockSheetOwner_index sizes hpos ⟨m, j⟩
  rw [he] at hn
  have hnm : n = m := hn.symm.trans hm
  subst m
  have hij : i = j := Fin.ext (Nat.add_left_cancel he)
  subst j
  rfl

/-- Computing a label after flattening recovers the entire original block label. -/
theorem originalBlockSheetLabel_index (sizes : ℕ → ℕ) (hpos : ∀ n, 0 < sizes n)
    (label : Σ n, Fin (sizes n)) :
    originalBlockSheetLabel sizes hpos (originalBlockSheetIndex sizes label) = label :=
  originalBlockSheetIndex_injective sizes hpos (originalBlockSheetIndex_label sizes hpos _)

/-- ALL complete block labels and ALL natural sheet indices are in bijection. -/
def originalBlockSheetEquiv (sizes : ℕ → ℕ) (hpos : ∀ n, 0 < sizes n) :
    (Σ n, Fin (sizes n)) ≃ ℕ where
  toFun := originalBlockSheetIndex sizes
  invFun := originalBlockSheetLabel sizes hpos
  left_inv := originalBlockSheetLabel_index sizes hpos
  right_inv := originalBlockSheetIndex_label sizes hpos

/-- The complete endpoint of a prefix depends only on the lengths in that prefix. -/
theorem originalBlockSheetOffset_prefix_congr (sizes sizes' : ℕ → ℕ) (n : ℕ)
    (hs : ∀ j < n, sizes j = sizes' j) :
    originalBlockSheetOffset sizes n = originalBlockSheetOffset sizes' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change originalBlockSheetOffset sizes n + sizes n = originalBlockSheetOffset sizes' n + sizes' n
    rw [ih (fun j hj => hs j (by omega)), hs n (by omega)]

/-- EVERY sheet before a complete prefix endpoint is owned by a block in that prefix. -/
theorem originalBlockSheetOwner_lt (sizes : ℕ → ℕ) (hpos : ∀ n, 0 < sizes n) (q n : ℕ)
    (hq : q < originalBlockSheetOffset sizes n) : originalBlockSheetOwner sizes hpos q < n := by
  have hs := (originalBlockSheetOwner_spec sizes hpos q).1
  by_contra hn
  have h := (originalBlockSheetOffset_strictMono sizes hpos).monotone
    (by omega : n ≤ originalBlockSheetOwner sizes hpos q)
  omega

/-- Future block lengths cannot change the computed ownership of any earlier sheet. -/
theorem originalBlockSheetOwner_prefix_congr (sizes sizes' : ℕ → ℕ)
    (hpos : ∀ n, 0 < sizes n) (hpos' : ∀ n, 0 < sizes' n) (q n : ℕ)
    (hs : ∀ j < n, sizes j = sizes' j) (hq : q < originalBlockSheetOffset sizes n) :
    originalBlockSheetOwner sizes hpos q = originalBlockSheetOwner sizes' hpos' q := by
  have hk := originalBlockSheetOwner_lt sizes hpos q n hq
  have h := originalBlockSheetOwner_spec sizes hpos q
  have hlo := originalBlockSheetOffset_prefix_congr sizes sizes' (originalBlockSheetOwner sizes hpos q)
    (fun j hj => hs j (hj.trans hk))
  have hhi := originalBlockSheetOffset_prefix_congr sizes sizes' (originalBlockSheetOwner sizes hpos q + 1)
    (fun j hj => hs j (by omega))
  apply ((originalBlockSheetOwner_eq_iff sizes' hpos' q _).mpr ?_).symm
  exact ⟨hlo ▸ h.1, hhi ▸ h.2⟩

end MeyerGeneralProblem.StrongParity

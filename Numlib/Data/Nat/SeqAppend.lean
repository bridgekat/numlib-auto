import Mathlib.Order.Basic
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Stream.Init

/-!
# Appending a sequence to a finite prefix

`Nat.seqAppend κ a b` is the sequence that follows `a` for the indices `k < κ` and then the shifted
sequence `b`, `k ↦ b (k - κ)`, from `κ` on. It splices a finite prefix of one run of an iterative
method (e.g. a slow run up to its first hit) with a run started at the state reached at `κ`.

## Main definitions

* `Nat.seqAppend κ a b`: `k ↦ if k < κ then a k else b (k - κ)`.

## Main results

* `Nat.seqAppend_of_lt`, `Nat.seqAppend_of_le`, `Nat.seqAppend_succ_of_le`, `Nat.seqAppend_add`:
  evaluation before and after `κ`;
* `Nat.seqAppend_eq_of_le`: if `b 0 = a κ`, the spliced sequence agrees with `a` up to `κ`;
* `Nat.seqAppend_eq_append_take`: as streams, `seqAppend κ a b = Stream'.take κ a ++ₛ b`.
-/

namespace Nat

variable {α : Type*} {κ k : ℕ} {a b : ℕ → α}

/-- The sequence equal to `a` before `κ` and to `b` shifted by `κ` from `κ` on:
`k ↦ if k < κ then a k else b (k - κ)`. -/
def seqAppend (κ : ℕ) (a b : ℕ → α) (k : ℕ) : α :=
  if k < κ then a k else b (k - κ)

theorem seqAppend_def (κ : ℕ) (a b : ℕ → α) (k : ℕ) :
    seqAppend κ a b k = if k < κ then a k else b (k - κ) :=
  rfl

/-- Before `κ`, the spliced sequence is the prefix. -/
@[simp]
theorem seqAppend_of_lt (h : k < κ) : seqAppend κ a b k = a k :=
  ite_eq_left_of_eq_true _ _ (eq_true h)

/-- From `κ` on, the spliced sequence is the appended sequence shifted by `κ`. -/
theorem seqAppend_of_le (h : κ ≤ k) : seqAppend κ a b k = b (k - κ) :=
  ite_eq_right_of_eq_false _ _ (eq_false (not_lt.2 h))

/-- The successor of an index `k ≥ κ`, in the form used to splice one-step transitions. -/
theorem seqAppend_succ_of_le (h : κ ≤ k) : seqAppend κ a b (k + 1) = b (k - κ + 1) := by
  rw [seqAppend_of_le (h.trans k.le_succ)]
  congr 1
  omega

/-- The term `κ + k` of the spliced sequence is the term `k` of the appended sequence. -/
@[simp]
theorem seqAppend_add (κ : ℕ) (a b : ℕ → α) (k : ℕ) : seqAppend κ a b (k + κ) = b k := by
  rw [seqAppend_of_le (Nat.le_add_left κ k), Nat.add_sub_cancel]

/-- The term `κ` of the spliced sequence is the first term of the appended sequence. -/
@[simp]
theorem seqAppend_self (κ : ℕ) (a b : ℕ → α) : seqAppend κ a b κ = b 0 := by
  simpa using seqAppend_add κ a b 0

/-- If the appended sequence starts at the last term of the prefix (`b 0 = a κ`), the spliced
sequence agrees with `a` up to and including `κ`. -/
theorem seqAppend_eq_of_le (h0 : b 0 = a κ) (h : k ≤ κ) : seqAppend κ a b k = a k := by
  rcases h.lt_or_eq with h | rfl
  · exact seqAppend_of_lt h
  · rw [seqAppend_self, h0]

/-- Shifting the spliced sequence by `κ` gives the appended sequence. -/
theorem seqAppend_comp_add (κ : ℕ) (a b : ℕ → α) : (fun k => seqAppend κ a b (k + κ)) = b :=
  funext fun k => seqAppend_add κ a b k

/-- `Nat.seqAppend κ a b` is Mathlib's stream append of the first `κ` terms of `a` to `b`. -/
theorem seqAppend_eq_append_take (κ : ℕ) (a b : Stream' α) :
    seqAppend κ a.get b.get = (Stream'.take κ a ++ₛ b).get := by
  funext k
  rcases lt_or_ge k κ with hk | hk
  · rw [seqAppend_of_lt hk, Stream'.get_append_left _ _ _ (by rwa [Stream'.length_take]),
      Stream'.take_get]
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [Nat.add_comm, seqAppend_add]
    have := Stream'.get_append_right n (Stream'.take κ a) b
    rw [Stream'.length_take] at this
    rw [Nat.add_comm, this]

end Nat

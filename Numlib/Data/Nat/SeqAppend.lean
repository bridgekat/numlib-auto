/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Order.Basic
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Stream.Init

/-!
# Appending a sequence to a finite prefix

Let $a, b \colon \mathbb{N} \to \alpha$ be sequences and let $\kappa \in \mathbb{N}$. The spliced
sequence `Nat.seqAppend κ a b` follows $a$ at the indices $k < \kappa$, and then the shifted
sequence $k \mapsto b_{k - \kappa}$ from $\kappa$ on. It joins a finite prefix of one run of an
iterative method (for example, a slow run up to its first hit) with a run that starts at the state
reached at $\kappa$.

## Main definitions

* `Nat.seqAppend`: the sequence $k \mapsto a_k$ for $k < \kappa$ and $k \mapsto b_{k - \kappa}$ for
  $k \ge \kappa$.

## Main results

* `Nat.seqAppend_of_lt`, `Nat.seqAppend_of_le`, `Nat.seqAppend_succ_of_le`, `Nat.seqAppend_add`,
  `Nat.seqAppend_self`: the terms before and after $\kappa$.
* `Nat.seqAppend_eq_of_le`: if $b_0 = a_\kappa$, the spliced sequence agrees with $a$ at every index
  $k \le \kappa$.
* `Nat.seqAppend_comp_add`: the spliced sequence shifted by $\kappa$ is $b$.
* `Nat.seqAppend_eq_append_take`: for streams, the spliced sequence is the stream append
  `Stream'.take κ a ++ₛ b`.
-/

namespace Nat

variable {α : Type*} {κ k : ℕ} {a b : ℕ → α}

/-- Let $\kappa \in \mathbb{N}$ and let $a, b \colon \mathbb{N} \to \alpha$. The **spliced
sequence** `Nat.seqAppend κ a b` is
$$k \mapsto \begin{cases} a_k & \text{if } k < \kappa, \\
  b_{k - \kappa} & \text{if } k \ge \kappa. \end{cases}$$
-/
def seqAppend (κ : ℕ) (a b : ℕ → α) (k : ℕ) : α :=
  if k < κ then a k else b (k - κ)

/-- The defining equation of `Nat.seqAppend`: the term $k$ of `Nat.seqAppend κ a b` is $a_k$ if
$k < \kappa$, and $b_{k - \kappa}$ otherwise. -/
theorem seqAppend_def (κ : ℕ) (a b : ℕ → α) (k : ℕ) :
    seqAppend κ a b k = if k < κ then a k else b (k - κ) :=
  rfl

/-- If $k < \kappa$, then the term $k$ of `Nat.seqAppend κ a b` is $a_k$. -/
@[simp]
theorem seqAppend_of_lt (h : k < κ) : seqAppend κ a b k = a k :=
  ite_eq_left_of_eq_true _ _ (eq_true h)

/-- If $\kappa \le k$, then the term $k$ of `Nat.seqAppend κ a b` is $b_{k - \kappa}$. -/
theorem seqAppend_of_le (h : κ ≤ k) : seqAppend κ a b k = b (k - κ) :=
  ite_eq_right_of_eq_false _ _ (eq_false (not_lt.2 h))

/-- If $\kappa \le k$, then the term $k + 1$ of `Nat.seqAppend κ a b` is $b_{k - \kappa + 1}$. This
is the form used to splice one-step transitions. -/
theorem seqAppend_succ_of_le (h : κ ≤ k) : seqAppend κ a b (k + 1) = b (k - κ + 1) := by
  rw [seqAppend_of_le (h.trans k.le_succ)]
  congr 1
  omega

/-- For every $k \in \mathbb{N}$, the term $k + \kappa$ of `Nat.seqAppend κ a b` is $b_k$. -/
@[simp]
theorem seqAppend_add (κ : ℕ) (a b : ℕ → α) (k : ℕ) : seqAppend κ a b (k + κ) = b k := by
  rw [seqAppend_of_le (Nat.le_add_left κ k), Nat.add_sub_cancel]

/-- The term $\kappa$ of `Nat.seqAppend κ a b` is $b_0$. -/
@[simp]
theorem seqAppend_self (κ : ℕ) (a b : ℕ → α) : seqAppend κ a b κ = b 0 := by
  simpa using seqAppend_add κ a b 0

/-- If $b_0 = a_\kappa$ and $k \le \kappa$, then the term $k$ of `Nat.seqAppend κ a b` is $a_k$. So
when $b$ starts at the term $a_\kappa$, the spliced sequence agrees with $a$ up to and including
the index $\kappa$. -/
theorem seqAppend_eq_of_le (h0 : b 0 = a κ) (h : k ≤ κ) : seqAppend κ a b k = a k := by
  rcases h.lt_or_eq with h | rfl
  · exact seqAppend_of_lt h
  · rw [seqAppend_self, h0]

/-- The spliced sequence shifted by $\kappa$ is the appended sequence: the sequence $k \mapsto$
(term $k + \kappa$ of `Nat.seqAppend κ a b`) is $b$. -/
theorem seqAppend_comp_add (κ : ℕ) (a b : ℕ → α) : (fun k => seqAppend κ a b (k + κ)) = b :=
  funext fun k => seqAppend_add κ a b k

/-- Let $a$ and $b$ be streams (infinite sequences) of elements of $\alpha$, and let
$\kappa \in \mathbb{N}$. The spliced sequence `Nat.seqAppend κ a.get b.get` is the sequence of
terms of the stream `Stream'.take κ a ++ₛ b`, which lists the first $\kappa$ terms of $a$ and
then all terms of $b$. -/
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

/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.EReal.Inv
import Mathlib.Data.EReal.Operations

/-!
# Order and arithmetic of the extended real numbers

The extended real line $\overline{\mathbb{R}} = [-\infty, +\infty]$ is Mathlib's `EReal`. Convex
analysis over $\overline{\mathbb{R}}$ needs a number of order and arithmetic facts that Mathlib does
not state directly. This module collects them. They include cancellation and scaling by positive
reals, the behaviour of a real constant under negation and subtraction, and the exchange of
addition, subtraction and multiplication by a positive real with suprema and infima. Most
hypotheses serve to avoid the expression $\infty - \infty$, and many results need no hypothesis
because one of the terms is a real number. The applications are in the convex analysis of
[rockafellar1970convex].

## Main results

* `EReal.coe_sub_le_comm`: for real $a$, $a - z \le w$ if and only if $a - w \le z$, with no side
  condition.
* `EReal.le_coe_sub_comm`: for real $a$, $z \le a - w$ if and only if $w \le a - z$, with no side
  condition.
* `EReal.coe_sub_coe_sub`: for real $a, b$, $b - (a - z) = (b - a) + z$.
* `EReal.neg_iSup`: $-\sup_i u_i = \inf_i (-u_i)$.
* `EReal.iSup_add`: $(\sup_i u_i) + c = \sup_i (u_i + c)$ for every $c \in \overline{\mathbb{R}}$.
* `EReal.add_iInf_of_ne_bot`: $a + \inf_i u_i = \inf_i (a + u_i)$ when $\inf_i u_i \neq -\infty$.
* `EReal.biSup_sum_univ_pi`: the supremum of a separable sum over a product set is the sum of the
  suprema.
* `EReal.iInf_prod_add`: the infimum of $\psi(a) + \varphi(b)$ over pairs is
  $\inf \psi + \inf \varphi$ when neither infimum is $+\infty$.
* `EReal.le_coe_of_sum_le_coe_sum`: if $c_i \le u_i$ for all $i$ and $\sum_i u_i \le \sum_i c_i$,
  then $u_i \le c_i$ for all $i$.
* `EReal.coe_sSup_of_bddAbove`: the embedding of $\mathbb{R}$ in $\overline{\mathbb{R}}$ preserves
  the supremum of a nonempty set that is bounded above.

## Notation

* $+\infty$ and $-\infty$ are `⊤` and `⊥`. A real number $r$ in $\overline{\mathbb{R}}$ is the
  coercion `(r : EReal)`.

## Implementation notes

* The module is written to Mathlib conventions, and its natural home is
  `Mathlib.Data.EReal.Operations`. Nothing in it is specific to numerical analysis.
* Results that Mathlib states are used directly and not restated. Examples are
  `EReal.le_of_forall_lt_iff_le`, `EReal.exists_between_coe_real`, `EReal.coe_mul`, `EReal.neg_add`,
  `EReal.neg_sub` and `EReal.left_distrib_of_nonneg_of_ne_top`.
* Subtraction is $x - y = x + (-y)$, and Mathlib's addition satisfies
  $-\infty + x = x + (-\infty) = -\infty$ for every $x$ (`EReal.bot_add`, `EReal.add_bot`). So
  $\infty - \infty = -\infty$.
* Multiplication on `EReal` is monotone under multiplication by a nonnegative element
  (`PosMulMono`), but it is not strictly monotone under multiplication by a positive element
  (`PosMulStrictMono`), since $\infty \cdot 1 = \infty \cdot 2$. Several proofs of a reverse
  inequality for a real factor $a > 0$ therefore multiply by $a^{-1}$.
-/

/-!
### The arithmetic conventions of Rockafellar

Section 4 of [rockafellar1970convex] fixes the conventions $\alpha + \infty = \infty$ for
$-\infty < \alpha \le \infty$, $\alpha - \infty = -\infty$ for $-\infty \le \alpha < \infty$,
$0 \cdot \infty = 0$, $\inf \emptyset = +\infty$ and $\sup \emptyset = -\infty$. It leaves
$\infty - \infty$ undefined, and avoids it by properness hypotheses. Each of these conventions
agrees with the corresponding fact about `EReal` in Mathlib, so no special arithmetic type is
needed. The examples below check the conventions for real $\alpha$, together with
$-(-\infty) = +\infty$.
-/

section Conventions

example (r : ℝ) : (r : EReal) + ⊤ = ⊤ := by simp
example (r : ℝ) : (r : EReal) - ⊤ = ⊥ := by simp
example : (0 : EReal) * ⊤ = 0 := by simp
example : -(⊥ : EReal) = ⊤ := by simp
example : (⨆ _ : (∅ : Set ℝ), (0 : EReal)) = ⊥ := by simp

end Conventions

namespace EReal

/-- Let $z \in \overline{\mathbb{R}}$ with $z \neq -\infty$ and $z < +\infty$. Then $z = r$ for some
real number $r$.

This is the existential form of `EReal.coe_toReal`, for use with `obtain` where `lift` would
substitute the value away. -/
theorem exists_coe_of_ne_bot_of_lt_top {z : EReal} (h₁ : z ≠ ⊥) (h₂ : z < ⊤) :
    ∃ r : ℝ, z = (r : EReal) :=
  ⟨z.toReal, (coe_toReal h₂.ne h₁).symm⟩

/-- Let $a > 0$ be real and let $u \in \overline{\mathbb{R}}$ with $u \neq +\infty$. Then
$a u \neq +\infty$. -/
theorem coe_mul_ne_top {a : ℝ} (ha : 0 < a) {u : EReal} (hu : u ≠ ⊤) : (a : EReal) * u ≠ ⊤ := by
  rw [EReal.mul_ne_top]
  exact ⟨Or.inl (EReal.coe_ne_bot a), Or.inl (by exact_mod_cast ha.le),
    Or.inl (EReal.coe_ne_top a), Or.inr hu⟩

/-- Let $a, b > 0$ be real and let $u, v \in \overline{\mathbb{R}}$ with $u \neq +\infty$ and
$v \neq +\infty$. Then
$$a(-u) + b(-v) = -(au + bv).$$

The hypotheses are needed: for $a = b = 1$, $u = +\infty$ and $v = -\infty$, the left side is
$-\infty$ and the right side is $+\infty$. -/
theorem neg_combo {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {u v : EReal} (hu : u ≠ ⊤) (hv : v ≠ ⊤) :
    (a : EReal) * -u + (b : EReal) * -v = -((a : EReal) * u + (b : EReal) * v) := by
  rw [EReal.neg_add (.inr (coe_mul_ne_top hb hv)) (.inl (coe_mul_ne_top ha hu)), sub_eq_add_neg,
    mul_neg, mul_neg]

/-!
### The hypotheses of `EReal.neg_combo` are needed

At $u = +\infty$ and $v = -\infty$, with $a = b = 1$, the two sides of `EReal.neg_combo` are
$-\infty$ and $+\infty$.
-/

example : (1 : EReal) * -(⊤ : EReal) + (1 : EReal) * -(⊥ : EReal) = ⊥ := by simp

example : -((1 : EReal) * (⊤ : EReal) + (1 : EReal) * (⊥ : EReal)) = ⊤ := by simp

/-- Let $a > 0$ be real and let $z, w \in \overline{\mathbb{R}}$. Then $az \le aw$ if and only if
$z \le w$.

The reverse direction multiplies by $a^{-1}$, because `EReal` has `PosMulMono` but not
`PosMulStrictMono`. -/
theorem coe_mul_le_coe_mul_iff {a : ℝ} (ha : 0 < a) {z w : EReal} :
    (a : EReal) * z ≤ (a : EReal) * w ↔ z ≤ w := by
  refine ⟨fun h => ?_, fun h => mul_le_mul_of_nonneg_left h (by exact_mod_cast ha.le)⟩
  have ha' : (0 : EReal) ≤ ((a⁻¹ : ℝ) : EReal) := by exact_mod_cast (inv_pos.2 ha).le
  have h' := mul_le_mul_of_nonneg_left h ha'
  rwa [← mul_assoc, ← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ ha.ne',
    EReal.coe_one, one_mul, one_mul] at h'

/-- Let $z \in \overline{\mathbb{R}}$ with $z \le \varepsilon$ for every real $\varepsilon > 0$.
Then $z \le 0$.

The conclusion is weaker than $z \le r$ for a fixed $r$: $z$ may be any extended real with
$z \le 0$. This is how "the optimal value is not positive" follows from feasible solutions whose
values tend to $0$. -/
theorem le_zero_of_forall_le_pos {z : EReal} (h : ∀ ε : ℝ, 0 < ε → z ≤ (ε : EReal)) : z ≤ 0 := by
  by_contra hc
  obtain ⟨q, hq0, hqz⟩ := EReal.lt_iff_exists_real_btwn.1 (not_le.1 hc)
  exact absurd (h q (by exact_mod_cast hq0)) (not_le.2 hqz)

/-- **Scaling an inequality with a real offset.** Let $c > 0$ and $t$ be real and let
$A, B \in \overline{\mathbb{R}}$. Then
$$cA + ct \le cB \iff A + t \le B.$$

This is what a positive Lagrange multiplier does to a constraint. -/
theorem coe_mul_add_coe_le_coe_mul_iff {c : ℝ} (hc : 0 < c) (A B : EReal) (t : ℝ) :
    (c : EReal) * A + ((c * t : ℝ) : EReal) ≤ (c : EReal) * B ↔ A + (t : EReal) ≤ B := by
  rw [EReal.coe_mul, ← left_distrib_of_nonneg_of_ne_top (by exact_mod_cast hc.le) (coe_ne_top c),
    coe_mul_le_coe_mul_iff hc]

/-- Let $z, w \in \overline{\mathbb{R}}$ such that, for every real $r$, $z \le r$ if and only if
$w \le r$. Then $z = w$. So an extended real is determined by the real numbers above it. -/
theorem eq_of_forall_le_coe_iff {z w : EReal}
    (h : ∀ r : ℝ, z ≤ (r : EReal) ↔ w ≤ (r : EReal)) : z = w := by
  refine le_antisymm ?_ ?_
  · induction w with
    | bot => exact le_of_forall_lt_iff_le.1 fun r _ => (h r).2 bot_le
    | top => exact le_top
    | coe s => exact (h s).2 le_rfl
  · induction z with
    | bot => exact le_of_forall_lt_iff_le.1 fun r _ => (h r).1 bot_le
    | top => exact le_top
    | coe s => exact (h s).1 le_rfl

/-- Let $a \neq 1$ be real and let $z \in \overline{\mathbb{R}}$ with $az = z$. Then $z = 0$,
$z = +\infty$ or $z = -\infty$.

This is the content of the remark that positive homogeneity of a function $f$ says nothing about
$f(0)$. -/
theorem eq_zero_or_eq_top_or_eq_bot {a : ℝ} (ha : a ≠ 1) {z : EReal} (h : (a : EReal) * z = z) :
    z = 0 ∨ z = ⊤ ∨ z = ⊥ := by
  induction z with
  | bot => exact Or.inr (Or.inr rfl)
  | top => exact Or.inr (Or.inl rfl)
  | coe r =>
    left
    rw [← EReal.coe_mul] at h
    have hr : a * r = r := by exact_mod_cast h
    have hz : (a - 1) * r = 0 := by rw [sub_mul, one_mul, hr, _root_.sub_self]
    rcases mul_eq_zero.1 hz with h1 | h1
    · exact absurd (by linarith : a = 1) ha
    · rw [h1, EReal.coe_zero]

/-- Let $z \in \overline{\mathbb{R}}$ with $-z = z$. Then $z = 0$. -/
theorem eq_zero_of_neg_eq {z : EReal} (h : -z = z) : z = 0 := by
  induction z with
  | bot => rw [EReal.neg_bot] at h; exact absurd h (by simp)
  | top => rw [EReal.neg_top] at h; exact absurd h (by simp)
  | coe r =>
    have hr : (-r : ℝ) = r := by exact_mod_cast h
    rw [(by linarith : r = (0 : ℝ)), EReal.coe_zero]

/-- Let $u, v \in \overline{\mathbb{R}}$ with $u \neq -\infty$ and $0 \le u + v$. Then $-u \le v$.
-/
theorem neg_le_of_zero_le_add {u v : EReal} (hu : u ≠ ⊥) (h : 0 ≤ u + v) : -u ≤ v := by
  induction u with
  | bot => exact absurd rfl hu
  | top => rw [EReal.neg_top]; exact bot_le
  | coe r =>
    induction v with
    | bot => rw [EReal.add_bot] at h; simp at h
    | top => exact le_top
    | coe s =>
      rw [← EReal.coe_add] at h
      have hrs : (0 : ℝ) ≤ r + s := by exact_mod_cast h
      rw [← EReal.coe_neg]
      exact_mod_cast (by linarith : -r ≤ s)

/-- Let $s$ be a finite set and let $g_i \in \overline{\mathbb{R}}$ with $g_i \neq -\infty$ for all
$i \in s$. Then $\sum_{i \in s} g_i \neq -\infty$. -/
theorem sum_ne_bot {ι : Type*} {s : Finset ι} {g : ι → EReal} (h : ∀ i ∈ s, g i ≠ ⊥) :
    ∑ i ∈ s, g i ≠ ⊥ := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i t hi ih =>
    rw [Finset.sum_cons]
    exact EReal.add_ne_bot_iff.2 ⟨h i (by simp), ih fun j hj => h j (by simp [hj])⟩

/-- Let $a > 0$ and $r$ be real and let $z \in \overline{\mathbb{R}}$. Then
$$az \le r \iff z \le r / a.$$

This is the form in which a hypothesis $az \le r$ is used: it turns a statement about $af$ into
a statement about $f$. -/
theorem coe_mul_le_coe_iff {a : ℝ} (ha : 0 < a) {z : EReal} {r : ℝ} :
    (a : EReal) * z ≤ (r : EReal) ↔ z ≤ ((r / a : ℝ) : EReal) := by
  induction z with
  | bot => simp [EReal.coe_mul_bot_of_pos ha]
  | top => simp [EReal.coe_mul_top_of_pos ha]
  | coe s =>
    rw [← coe_mul, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff, le_div_iff₀ ha,
      mul_comm]

/-- Let $a > 0$ and $r$ be real and let $z \in \overline{\mathbb{R}}$. Then
$$r \le az \iff r / a \le z.$$
This is the version of `EReal.coe_mul_le_coe_iff` for a lower bound. -/
theorem coe_le_coe_mul_iff {a : ℝ} (ha : 0 < a) {z : EReal} {r : ℝ} :
    (r : EReal) ≤ (a : EReal) * z ↔ ((r / a : ℝ) : EReal) ≤ z := by
  induction z with
  | bot => simp [EReal.coe_mul_bot_of_pos ha]
  | top => simp [EReal.coe_mul_top_of_pos ha]
  | coe s =>
    rw [← coe_mul, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff, div_le_iff₀ ha,
      mul_comm]

variable {κ : Type*}

/-- The embedding of $\mathbb{R}$ in $\overline{\mathbb{R}}$ commutes with finite sums: for real
$r_i$, the real sum $\sum_{i \in t} r_i$ is the extended real sum of the $r_i$. -/
theorem coe_sum (t : Finset κ) (r : κ → ℝ) :
    ((∑ i ∈ t, r i : ℝ) : EReal) = ∑ i ∈ t, ((r i : ℝ) : EReal) := by
  induction t using Finset.cons_induction with
  | empty => simp
  | cons i t hi ih => rw [Finset.sum_cons, Finset.sum_cons, EReal.coe_add, ih]

/-- **A difference of finite sums is the sum of the differences.** Let $t$ be a finite set and let
$a_j, v_j \in \overline{\mathbb{R}}$ with $v_j \neq -\infty$ for all $j \in t$. Then
$$\sum_{j \in t} a_j - \sum_{j \in t} v_j = \sum_{j \in t} (a_j - v_j).$$

The $a_j$ are arbitrary. This is the form for finite sums of Mathlib's `EReal.add_sub_add_comm`. -/
theorem sum_sub_sum (t : Finset κ) (a v : κ → EReal) (hv : ∀ j ∈ t, v j ≠ ⊥) :
    ∑ j ∈ t, a j - ∑ j ∈ t, v j = ∑ j ∈ t, (a j - v j) := by
  induction t using Finset.cons_induction with
  | empty => simp
  | cons j t hj ih =>
    rw [Finset.sum_cons, Finset.sum_cons, Finset.sum_cons, ← ih fun k hk => hv k (by simp [hk])]
    exact EReal.add_sub_add_comm (.inl (hv j (by simp)))
      (.inr (sum_ne_bot fun k hk => hv k (by simp [hk])))

/-- Let $a \ge 0$ be real and let $z \in \overline{\mathbb{R}}$ with $z \neq -\infty$. Then
$az \neq -\infty$.

The coefficient $a = 0$ is allowed because `EReal` satisfies the convention $0 \cdot \infty = 0$
of [rockafellar1970convex]. -/
theorem coe_mul_ne_bot {a : ℝ} (ha : 0 ≤ a) {z : EReal} (hz : z ≠ ⊥) : (a : EReal) * z ≠ ⊥ := by
  rcases eq_or_lt_of_le ha with h | h
  · rw [← h, EReal.coe_zero, zero_mul]; simp
  · induction z with
    | bot => exact absurd rfl hz
    | top => rw [EReal.coe_mul_top_of_pos h]; exact top_ne_bot
    | coe r => rw [← coe_mul]; exact EReal.coe_ne_bot _

/-- Let $t$ be a finite set and let $z_i \in \overline{\mathbb{R}}$ with $z_i \neq -\infty$ for all
$i \in t$. If $\sum_{i \in t} z_i \neq +\infty$, then $z_i \neq +\infty$ for all $i \in t$.

This is how a finite upper bound on a sum gives a finite upper bound on each term. -/
theorem forall_ne_top_of_sum_ne_top (t : Finset κ) (z : κ → EReal) :
    (∀ i ∈ t, z i ≠ ⊥) → (∑ i ∈ t, z i ≠ ⊤) → ∀ i ∈ t, z i ≠ ⊤ := by
  induction t using Finset.cons_induction with
  | empty => simp
  | cons j t hj ih =>
    intro hbot hsum i hi
    rw [Finset.sum_cons] at hsum
    have h₁ : z j ≠ ⊥ := hbot j (by simp)
    have h₂ : (∑ k ∈ t, z k) ≠ ⊥ := sum_ne_bot fun k hk => hbot k (by simp [hk])
    obtain ⟨hj', ht'⟩ := (EReal.add_ne_top_iff_ne_top₂ h₁ h₂).1 hsum
    rcases Finset.mem_cons.1 hi with rfl | hi'
    · exact hj'
    · exact ih (fun k hk => hbot k (by simp [hk])) ht' i hi'

/-- Let $a$ be real and let $z \in \overline{\mathbb{R}}$. Then $a - z = -\infty$ if and only if
$z = +\infty$. -/
theorem coe_sub_eq_bot_iff {a : ℝ} {z : EReal} : (a : EReal) - z = ⊥ ↔ z = ⊤ := by
  induction z with
  | bot => simp
  | top => simp
  | coe r =>
    refine ⟨fun h => absurd h ?_, fun h => absurd h (by simp)⟩
    rw [← EReal.coe_sub]
    exact EReal.coe_ne_bot _

/-- Let $c, m$ be real and let $z \in \overline{\mathbb{R}}$. Then $z + c \le m$ if and only if
$z \le m - c$. -/
theorem add_coe_le_coe_iff {z : EReal} {c m : ℝ} :
    z + (c : EReal) ≤ (m : EReal) ↔ z ≤ ((m - c : ℝ) : EReal) := by
  rw [EReal.coe_sub, EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot c))
    (.inl (EReal.coe_ne_top c))]

/-- Let $a$ be real and let $z \in \overline{\mathbb{R}}$ with $z \neq +\infty$. Then
$a - z \neq -\infty$. -/
theorem coe_sub_ne_bot {a : ℝ} {z : EReal} (h : z ≠ ⊤) : (a : EReal) - z ≠ ⊥ := fun hc =>
  h (coe_sub_eq_bot_iff.1 hc)

/-- The **symmetry of Fenchel's inequality**. Let $a$ be real and let
$z, w \in \overline{\mathbb{R}}$. Then
$$a - z \le w \iff a - w \le z.$$

There is no side condition. All degenerate combinations of $\pm\infty$ work, because $a$ is
finite. This is the fact about $\overline{\mathbb{R}}$ that the theory of conjugate functions in
§12 of [rockafellar1970convex] rests on. -/
theorem coe_sub_le_comm {a : ℝ} {z w : EReal} : (a : EReal) - z ≤ w ↔ (a : EReal) - w ≤ z := by
  induction z with
  | bot => simpa using coe_sub_eq_bot_iff.symm
  | top => simp
  | coe r =>
    induction w with
    | bot => simp [coe_sub_eq_bot_iff]
    | top => simp
    | coe s =>
      rw [← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff,
        EReal.coe_le_coe_iff]
      constructor <;> intro h <;> linarith

/-- Let $a$ be real and let $z, w \in \overline{\mathbb{R}}$. Then
$$z \le a - w \iff w \le a - z.$$

This is the version of `EReal.coe_sub_le_comm` for the concave side of the theory. It says that
$z \mapsto a - z$ is an order-reversing involution of $\overline{\mathbb{R}}$. There is no side
condition. -/
theorem le_coe_sub_comm {a : ℝ} {z w : EReal} :
    z ≤ (a : EReal) - w ↔ w ≤ (a : EReal) - z := by
  induction z with
  | bot => simp
  | top =>
    induction w with
    | bot => simp
    | top => simp
    | coe s =>
      rw [EReal.sub_top, le_bot_iff, top_le_iff, ← EReal.coe_sub]
      exact iff_of_false (EReal.coe_ne_top _) (EReal.coe_ne_bot _)
  | coe r =>
    induction w with
    | bot => simp
    | top =>
      rw [EReal.sub_top, le_bot_iff, top_le_iff, ← EReal.coe_sub]
      exact iff_of_false (EReal.coe_ne_bot _) (EReal.coe_ne_top _)
    | coe s =>
      rw [← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff,
        EReal.coe_le_coe_iff]
      constructor <;> intro h <;> linarith

/-- Let $a, b$ be real and let $z \in \overline{\mathbb{R}}$. Then
$$b - (a - z) = (b - a) + z.$$
In particular $a - (a - z) = z$, so $z \mapsto a - z$ is an involution of
$\overline{\mathbb{R}}$ for every real $a$. -/
theorem coe_sub_coe_sub (a b : ℝ) (z : EReal) :
    (b : EReal) - ((a : EReal) - z) = ((b - a : ℝ) : EReal) + z := by
  induction z with
  | bot => rw [EReal.coe_sub_bot, EReal.sub_top, EReal.add_bot]
  | coe r =>
    rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_add,
      EReal.coe_eq_coe_iff]
    ring
  | top => rw [EReal.sub_top, EReal.coe_sub_bot, EReal.coe_add_top]

/-- Let $u, v \in \overline{\mathbb{R}}$ such that $u \le s$ for every real $s$ with $v \le s$. Then
$u \le v$. -/
theorem le_of_forall_coe_le {u v : EReal} (h : ∀ s : ℝ, v ≤ (s : EReal) → u ≤ (s : EReal)) :
    u ≤ v := by
  induction v with
  | bot => exact le_of_forall_lt_iff_le.1 fun s _ => h s bot_le
  | coe t => exact h t le_rfl
  | top => exact le_top

/-- Let $a > 0$ be real and let $(g_i)_{i \in \iota}$ be a family in $\overline{\mathbb{R}}$. Then
$$a \inf_i g_i = \inf_i (a g_i).$$

The index type may be empty. The reverse inequality multiplies by $a^{-1}$, because `EReal` has
`PosMulMono` but not `PosMulStrictMono`. -/
theorem coe_mul_iInf {ι : Sort*} {a : ℝ} (ha : 0 < a) (g : ι → EReal) :
    (a : EReal) * ⨅ i, g i = ⨅ i, (a : EReal) * g i := by
  have hcancel : ∀ z : EReal, ((a⁻¹ : ℝ) : EReal) * ((a : EReal) * z) = z := fun z => by
    rw [← mul_assoc, ← coe_mul, inv_mul_cancel₀ ha.ne', EReal.coe_one, one_mul]
  refine le_antisymm (le_iInf fun i => (coe_mul_le_coe_mul_iff ha).2 (iInf_le g i)) ?_
  rw [← coe_mul_le_coe_mul_iff (a := a⁻¹) (inv_pos.2 ha), hcancel]
  exact le_iInf fun i =>
    (hcancel (g i)) ▸ (coe_mul_le_coe_mul_iff (inv_pos.2 ha)).2 (iInf_le _ i)

/-- Let $r, m$ and $a > 0$ be real and let $u \in \overline{\mathbb{R}}$. Then the difference
quotient satisfies
$$\frac{u - r}{a} \le m \iff u \le r + ma.$$
-/
theorem sub_div_le_coe_iff {r m a : ℝ} (ha : 0 < a) (u : EReal) :
    (u - (r : EReal)) / (a : EReal) ≤ (m : EReal) ↔ u ≤ ((r + m * a : ℝ) : EReal) := by
  rw [EReal.div_le_iff_le_mul (mod_cast ha) (EReal.coe_ne_top a),
    EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot r))
      (.inl (EReal.coe_ne_top r)), ← coe_mul, ← EReal.coe_add,
    show (a * m + r : ℝ) = r + m * a from by ring]

/-- Let $r, m$ and $a > 0$ be real and let $u \in \overline{\mathbb{R}}$. Then the difference
quotient satisfies
$$m \le \frac{u - r}{a} \iff r + ma \le u.$$
-/
theorem coe_le_sub_div_iff {r m a : ℝ} (ha : 0 < a) (u : EReal) :
    (m : EReal) ≤ (u - (r : EReal)) / (a : EReal) ↔ ((r + m * a : ℝ) : EReal) ≤ u := by
  rw [EReal.le_div_iff_mul_le (mod_cast ha) (EReal.coe_ne_top a),
    EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot r))
      (.inl (EReal.coe_ne_top r)), ← coe_mul, ← EReal.coe_add,
    show (m * a + r : ℝ) = r + m * a from by ring]

/-- **Negation exchanges suprema and infima.** For every family $(u_i)$ in $\overline{\mathbb{R}}$,
$$-\sup_i u_i = \inf_i (-u_i).$$

Negation is an order-reversing involution of $\overline{\mathbb{R}}$ with no exceptional values,
so no hypothesis is needed. This turns every statement about convex conjugates into one about
concave conjugates. -/
theorem neg_iSup {ι : Sort*} (u : ι → EReal) : -(⨆ i, u i) = ⨅ i, -(u i) :=
  eq_of_forall_le_iff fun z => by
    simp only [le_iInf_iff, EReal.le_neg, iSup_le_iff]

/-- For every family $(u_i)$ in $\overline{\mathbb{R}}$, $-\inf_i u_i = \sup_i (-u_i)$. -/
theorem neg_iInf {ι : Sort*} (u : ι → EReal) : -(⨅ i, u i) = ⨆ i, -(u i) :=
  eq_of_forall_ge_iff fun z => by
    simp only [iSup_le_iff, EReal.neg_le, le_iInf_iff]

/-- **Negation reverses a difference with a real minuend.** Let $r$ be real and let
$z \in \overline{\mathbb{R}}$. Then
$$-(r - z) = z - r.$$

There is no side condition: the finite term excludes both cases of $\infty - \infty$. The
general `EReal.neg_sub` needs two hypotheses. -/
theorem neg_coe_sub (r : ℝ) (z : EReal) : -((r : EReal) - z) = z - (r : EReal) := by
  induction z with
  | bot => simp
  | coe s => norm_cast; ring
  | top => simp

/-- **Negation reverses a difference.** Let $a, b \in \overline{\mathbb{R}}$ such that $a$ or $b$ is
not $-\infty$, and $a$ or $b$ is not $+\infty$. Then
$$-(a - b) = b - a.$$

This is Mathlib's `EReal.neg_sub`, whose right side is $-a + b$, with the difference written as
$b - a$. The hypotheses are Mathlib's. `EReal.neg_coe_sub` is the case of a real minuend, which
satisfies both hypotheses. -/
theorem neg_sub_comm {a b : EReal} (h₁ : a ≠ ⊥ ∨ b ≠ ⊥) (h₂ : a ≠ ⊤ ∨ b ≠ ⊤) :
    -(a - b) = b - a := by
  rw [EReal.neg_sub h₁ h₂, sub_eq_add_neg, add_comm]

/-- Let $u, v \in \overline{\mathbb{R}}$ with $u \neq -\infty$ and $v \neq -\infty$. Then
$-(u + v) = -u + -v$. This is a symmetric special case of Mathlib's `EReal.neg_add`. -/
theorem neg_add_of_ne_bot {u v : EReal} (hu : u ≠ ⊥) (hv : v ≠ ⊥) : -(u + v) = -u + -v :=
  (EReal.neg_add (.inl hu) (.inr hv)).trans (sub_eq_add_neg _ _)

/-- Let $a, b \in \overline{\mathbb{R}}$ with $a \neq -\infty$ and $b \neq -\infty$. Then
$$-(-a + -b) = a + b.$$

So the concave sum $-(-a + -b)$ agrees with the convex sum $a + b$ away from $-\infty$. The case
$a = b = +\infty$ is included: $-(-\infty + -\infty) = +\infty = +\infty + +\infty$. The
identity is Mathlib's `EReal.neg_add` for $-a$ and $-b$, whose two side conditions hold because
$a \neq -\infty$ and $b \neq -\infty$. -/
theorem neg_neg_add_neg {a b : EReal} (ha : a ≠ ⊥) (hb : b ≠ ⊥) :
    -(-a + -b) = a + b := by
  rcases eq_or_ne a ⊤ with rfl | hat
  · rw [EReal.neg_top, EReal.bot_add, EReal.neg_bot,
      EReal.top_add_of_ne_bot hb]
  · rcases eq_or_ne b ⊤ with rfl | hbt
    · rw [EReal.neg_top, EReal.add_bot, EReal.neg_bot,
        EReal.add_top_of_ne_bot ha]
    · rw [EReal.neg_add (.inl (by rw [Ne, EReal.neg_eq_bot_iff]; exact hat))
        (.inl (by rw [Ne, EReal.neg_eq_top_iff]; exact ha)), neg_neg]
      change a + -(-b) = a + b
      rw [neg_neg]

/-- Let $a, b, c \in \overline{\mathbb{R}}$ with $a \neq -\infty$ and $b \neq -\infty$. Then
$$c - (a + b) = (c - b) - a.$$
The element $c$ is arbitrary. This is the form for `EReal` of `sub_add_eq_sub_sub_swap`. -/
protected theorem sub_add_eq_sub_sub_swap (c : EReal) {a b : EReal} (ha : a ≠ ⊥) (hb : b ≠ ⊥) :
    c - (a + b) = c - b - a := by
  have h : -(a + b) = -b + -a := by
    rw [add_comm a b]
    exact EReal.neg_add (.inl hb) (.inr ha)
  change c + -(a + b) = (c + -b) + -a
  rw [h, ← add_assoc]

/-- Let $a, b, c \in \overline{\mathbb{R}}$ with $a \neq -\infty$ and $c \neq +\infty$. Then
$$b - (a - c) = (b + c) - a.$$
The two hypotheses exclude both cases of $\infty - \infty$ in $a - c$. This is the form for
`EReal` of `sub_sub_eq_add_sub`. -/
protected theorem sub_sub_eq_add_sub {a b c : EReal} (ha : a ≠ ⊥) (hc : c ≠ ⊤) :
    b - (a - c) = (b + c) - a := by
  have h : -(a - c) = c - a := neg_sub_comm (.inl ha) (.inr hc)
  change b + -(a - c) = b + c + -a
  rw [h]
  change b + (c + -a) = b + c + -a
  rw [← add_assoc]

/-- Let $a > 0$ be real and let $(u_i)$ be a family in $\overline{\mathbb{R}}$. Then
$a \sup_i u_i = \sup_i (a u_i)$. -/
theorem coe_mul_iSup {a : ℝ} (ha : 0 < a) {ι : Sort*} (u : ι → EReal) :
    (a : EReal) * ⨆ i, u i = ⨆ i, (a : EReal) * u i := by
  have key : ∀ b : ℝ, 0 < b → ∀ v : ι → EReal,
      (⨆ i, (b : EReal) * v i) ≤ (b : EReal) * ⨆ i, v i := fun b hb v =>
    iSup_le fun i => mul_le_mul_of_nonneg_left (le_iSup v i) (by exact_mod_cast hb.le)
  refine le_antisymm ?_ (key a ha u)
  have h := key a⁻¹ (inv_pos.2 ha) fun i => (a : EReal) * u i
  have hid : ∀ i, ((a⁻¹ : ℝ) : EReal) * ((a : EReal) * u i) = u i := fun i => by
    rw [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ ha.ne', EReal.coe_one, one_mul]
  simp only [hid] at h
  calc (a : EReal) * ⨆ i, u i
      ≤ (a : EReal) * (((a⁻¹ : ℝ) : EReal) * ⨆ i, (a : EReal) * u i) :=
        mul_le_mul_of_nonneg_left h (by exact_mod_cast ha.le)
    _ = ⨆ i, (a : EReal) * u i := by
        rw [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ ha.ne', EReal.coe_one,
          one_mul]

/-- Let $(u_i)$ be a family in $\overline{\mathbb{R}}$ and let $r$ be real. Then
$$\Bigl(\sup_i u_i\Bigr) + r = \sup_i (u_i + r).$$

The constant $r$ is finite, so no $\infty - \infty$ occurs and no hypothesis is needed. The
empty index type is allowed, since $-\infty + r = -\infty$. -/
theorem iSup_add_coe {ι : Sort*} (u : ι → EReal) (r : ℝ) :
    (⨆ i, u i) + (r : EReal) = ⨆ i, (u i + (r : EReal)) := by
  have key : ∀ (c : ℝ) (v : ι → EReal), (⨆ i, (v i + (c : EReal))) ≤ (⨆ i, v i) + (c : EReal) :=
    fun c v => iSup_le fun i => add_le_add (le_iSup v i) le_rfl
  refine le_antisymm ?_ (key r u)
  have h := key (-r) fun i => u i + (r : EReal)
  have hid : ∀ i, u i + (r : EReal) + ((-r : ℝ) : EReal) = u i := fun i => by
    rw [EReal.coe_neg, ← sub_eq_add_neg, EReal.add_sub_cancel_right]
  simp only [hid] at h
  calc (⨆ i, u i) + (r : EReal)
      ≤ ((⨆ i, (u i + (r : EReal))) + ((-r : ℝ) : EReal)) + (r : EReal) := add_le_add h le_rfl
    _ = ⨆ i, (u i + (r : EReal)) := by
        rw [EReal.coe_neg, ← sub_eq_add_neg, EReal.sub_add_cancel]

/-- **A constant moves out of a supremum.** Let $(u_i)$ be a family in $\overline{\mathbb{R}}$ and
let $c \in \overline{\mathbb{R}}$. Then
$$\Bigl(\sup_i u_i\Bigr) + c = \sup_i (u_i + c).$$

There is no hypothesis, because $x \mapsto x + c$ preserves arbitrary suprema on
$\overline{\mathbb{R}}$. For $c = +\infty$ it maps $-\infty$ to $-\infty$ and every other
element to $+\infty$. For $c = -\infty$ it is constant. For real $c$ it is an order isomorphism.
For the empty index type, both sides are $-\infty + c = -\infty$. Infima behave differently; see
`EReal.add_iInf_of_ne_bot`. -/
theorem iSup_add {ι : Sort*} (u : ι → EReal) (c : EReal) :
    (⨆ i, u i) + c = ⨆ i, (u i + c) := by
  induction c with
  | bot => simp
  | coe r => exact iSup_add_coe u r
  | top =>
    by_cases h : ∀ i, u i = ⊥
    · simp [h]
    · push Not at h
      obtain ⟨i, hi⟩ := h
      have hne : (⨆ i, u i) ≠ ⊥ := fun hc => hi (le_bot_iff.1 (hc ▸ le_iSup u i))
      rw [add_top_of_ne_bot hne]
      exact le_antisymm (le_iSup_of_le i (add_top_of_ne_bot hi).ge) le_top

/-- Let $c \in \overline{\mathbb{R}}$ and let $(u_i)$ be a family in $\overline{\mathbb{R}}$. Then
$c + \sup_i u_i = \sup_i (c + u_i)$. This is `EReal.iSup_add` with the constant on the left. -/
theorem add_iSup {ι : Sort*} (c : EReal) (u : ι → EReal) :
    c + (⨆ i, u i) = ⨆ i, (c + u i) := by
  rw [add_comm, iSup_add]
  exact iSup_congr fun i => add_comm _ _

/-- **A constant minus an infimum is the supremum of the differences.** Let
$c \in \overline{\mathbb{R}}$ and let $(u_i)$ be a family in $\overline{\mathbb{R}}$. Then
$$c - \inf_i u_i = \sup_i (c - u_i).$$

There is no hypothesis: $c - x = c + (-x)$, and negation exchanges infima and suprema. -/
theorem sub_iInf {ι : Sort*} (c : EReal) (u : ι → EReal) :
    c - ⨅ i, u i = ⨆ i, (c - u i) := by
  rw [sub_eq_add_neg, neg_iInf, add_iSup]
  exact iSup_congr fun i => (sub_eq_add_neg _ _).symm

/-- **A constant other than $-\infty$ moves out of a supremum as a subtrahend.** Let $(u_i)$ be a
family in $\overline{\mathbb{R}}$ and let $c \in \overline{\mathbb{R}}$ with $c \neq -\infty$.
Then
$$\Bigl(\sup_i u_i\Bigr) - c = \sup_i (u_i - c).$$

For the empty index type, both sides are $-\infty$. The identity also holds at $c = -\infty$, so
the hypothesis is not necessary: since $x - c = x + (-c)$, the identity is `EReal.iSup_add` with
the constant $-c$, which needs no hypothesis. -/
theorem iSup_sub_of_ne_bot {ι : Sort*} (u : ι → EReal) {c : EReal} (hc : c ≠ ⊥) :
    (⨆ i, u i) - c = ⨆ i, (u i - c) := by
  induction c with
  | bot => exact absurd rfl hc
  | coe r =>
    rw [sub_eq_add_neg, ← EReal.coe_neg, iSup_add_coe]
    exact iSup_congr fun i => by rw [sub_eq_add_neg, ← EReal.coe_neg]
  | top =>
    have h : ∀ x : EReal, x - (⊤ : EReal) = ⊥ := fun x => by
      rw [sub_eq_add_neg, EReal.neg_top, EReal.add_bot]
    simp only [h, iSup_bot]

/-- Let $(u_i)$ be a family in $\overline{\mathbb{R}}$ and let $r$ be real. Then
$$\Bigl(\inf_i u_i\Bigr) + r = \inf_i (u_i + r).$$

There is no hypothesis. The empty index type is allowed, since $+\infty + r = +\infty$. This is
the version of `EReal.iSup_add_coe` for infima. -/
theorem iInf_add_coe {ι : Sort*} (u : ι → EReal) (r : ℝ) :
    (⨅ i, u i) + (r : EReal) = ⨅ i, (u i + (r : EReal)) := by
  have key : ∀ (c : ℝ) (v : ι → EReal), (⨅ i, v i) + (c : EReal) ≤ ⨅ i, (v i + (c : EReal)) :=
    fun c v => le_iInf fun i => add_le_add (iInf_le v i) le_rfl
  refine le_antisymm (key r u) ?_
  have h := key (-r) fun i => u i + (r : EReal)
  have hid : ∀ i, u i + (r : EReal) + ((-r : ℝ) : EReal) = u i := fun i => by
    rw [EReal.coe_neg, ← sub_eq_add_neg, EReal.add_sub_cancel_right]
  simp only [hid] at h
  calc (⨅ i, (u i + (r : EReal)))
      = ((⨅ i, (u i + (r : EReal))) + ((-r : ℝ) : EReal)) + (r : EReal) := by
        rw [EReal.coe_neg, ← sub_eq_add_neg, EReal.sub_add_cancel]
    _ ≤ (⨅ i, u i) + (r : EReal) := add_le_add h le_rfl

/-- Let $s$ be a set, let $u \colon \alpha \to \overline{\mathbb{R}}$ and let $r$ be real. Then
$(\sup_{a \in s} u(a)) + r = \sup_{a \in s} (u(a) + r)$. This is the form of
`EReal.iSup_add_coe` for a supremum over a set. -/
theorem biSup_add_coe {α : Type*} (s : Set α) (u : α → EReal) (r : ℝ) :
    (⨆ a ∈ s, u a) + (r : EReal) = ⨆ a ∈ s, (u a + (r : EReal)) := by
  rw [iSup_add_coe]
  exact iSup_congr fun a => iSup_add_coe _ r

/-- **A real summand cancels on the right.** Let $u, v \in \overline{\mathbb{R}}$ and let $r$ be
real. If $u + r = v + r$, then $u = v$.

No hypothesis is needed, because $r$ is finite and so $u + r - r = u$ for every $u$. -/
theorem add_coe_right_cancel {u v : EReal} {r : ℝ} (h : u + (r : EReal) = v + (r : EReal)) :
    u = v := by
  rw [← EReal.add_sub_cancel_right (a := u) (b := r),
    ← EReal.add_sub_cancel_right (a := v) (b := r), h]

/-- Let $S \in \overline{\mathbb{R}}$ and let $k, m$ be real. If $S + k = m$, then $S$ is the real
number $m - k$. -/
theorem eq_coe_sub_of_add_coe_eq_coe {S : EReal} {k m : ℝ} (h : S + (k : EReal) = (m : EReal)) :
    S = ((m - k : ℝ) : EReal) := by
  induction S with
  | bot =>
      rw [EReal.bot_add] at h
      exact absurd h.symm (EReal.coe_ne_bot m)
  | coe s =>
      rw [← EReal.coe_add, EReal.coe_eq_coe_iff] at h
      rw [EReal.coe_eq_coe_iff]
      linarith
  | top =>
      rw [EReal.top_add_of_ne_bot (EReal.coe_ne_bot k)] at h
      exact absurd h.symm (EReal.coe_ne_top m)

/-- Let $s$ be a set, let $u \colon \alpha \to \overline{\mathbb{R}}$ and let $r$ be real. Then
$(\inf_{a \in s} u(a)) + r = \inf_{a \in s} (u(a) + r)$. This is the form of
`EReal.iInf_add_coe` for an infimum over a set. -/
theorem biInf_add_coe {α : Type*} (s : Set α) (u : α → EReal) (r : ℝ) :
    (⨅ a ∈ s, u a) + (r : EReal) = ⨅ a ∈ s, (u a + (r : EReal)) := by
  rw [iInf_add_coe]
  exact iInf_congr fun a => iInf_add_coe _ r

/-- Let $s$ be a set, let $u \colon \alpha \to \overline{\mathbb{R}}$ with $u(a) \neq -\infty$ for
all $a \in s$, and let $M \in \overline{\mathbb{R}}$. Then
$$\Bigl(\sup_{a \in s} u(a)\Bigr) + M = \sup_{a \in s} (u(a) + M).$$
-/
theorem biSup_add_of_ne_bot {α : Type*} {s : Set α} {u : α → EReal} (hu : ∀ a ∈ s, u a ≠ ⊥)
    (M : EReal) : (⨆ a ∈ s, u a) + M = ⨆ a ∈ s, (u a + M) := by
  induction M with
  | bot => simp
  | coe r => exact biSup_add_coe s u r
  | top =>
    rcases s.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
    · simp
    · have hne : (⨆ a ∈ s, u a) ≠ ⊥ := fun hc =>
        hu a₀ ha₀ (le_bot_iff.1 (hc ▸ le_iSup₂ (f := fun a (_ : a ∈ s) => u a) a₀ ha₀))
      rw [EReal.add_top_of_ne_bot hne]
      refine (top_le_iff.1 ?_).symm
      calc (⊤ : EReal) = u a₀ + ⊤ := (EReal.add_top_of_ne_bot (hu a₀ ha₀)).symm
        _ ≤ ⨆ a ∈ s, (u a + (⊤ : EReal)) :=
          le_iSup₂ (f := fun a (_ : a ∈ s) => u a + (⊤ : EReal)) a₀ ha₀

/-- **The supremum of a sum splits.** Let $s$ and $t$ be sets, and let
$u \colon \alpha \to \overline{\mathbb{R}}$ and $v \colon \beta \to \overline{\mathbb{R}}$ with
$u(a) \neq -\infty$ for $a \in s$ and $v(b) \neq -\infty$ for $b \in t$. Then
$$\sup_{a \in s} u(a) + \sup_{b \in t} v(b) = \sup_{a \in s} \sup_{b \in t} (u(a) + v(b)).$$

If $s$ or $t$ is empty, both sides are $-\infty$. This turns the fact that the epigraph of an
infimal convolution is a sum of epigraphs into the fact that the conjugate of an infimal
convolution is a sum of conjugates (Theorem 16.4 of [rockafellar1970convex]). -/
theorem biSup_add_biSup {α β : Type*} {s : Set α} {t : Set β} {u : α → EReal} {v : β → EReal}
    (hu : ∀ a ∈ s, u a ≠ ⊥) (hv : ∀ b ∈ t, v b ≠ ⊥) :
    (⨆ a ∈ s, u a) + (⨆ b ∈ t, v b) = ⨆ a ∈ s, ⨆ b ∈ t, (u a + v b) := by
  rw [biSup_add_of_ne_bot hu]
  refine iSup_congr fun a => iSup_congr fun _ => ?_
  rw [add_comm (u a), biSup_add_of_ne_bot hv]
  exact iSup_congr fun _ => iSup_congr fun _ => add_comm _ _

/-- **The supremum of a separable sum over a product set splits** coordinate by coordinate. Let
$C_i \subseteq \alpha$, $i \in \iota$, be nonempty sets, let
$u_i \colon \alpha \to \overline{\mathbb{R}}$ with $u_i(z) \neq -\infty$ for $z \in C_i$, and
let $t$ be a finite set of indices. Then
$$\sup_{x \in \prod_i C_i} \sum_{i \in t} u_i(x_i) = \sum_{i \in t} \sup_{z \in C_i} u_i(z).$$

The values need to avoid $-\infty$ only on the sets $C_i$. Nonemptiness is needed for the
indices $i \notin t$: if such a $C_i$ is empty, then the product set is empty and the left side
is $-\infty$. For example, for $t = \emptyset$ the left side is the supremum of the constant
$0$, which must be $0$ and not $-\infty$. The product set is `Set.univ.pi C`. -/
theorem biSup_sum_univ_pi {ι α : Type*} {C : ι → Set α} (hne : ∀ i, (C i).Nonempty)
    (u : ι → α → EReal) (hu : ∀ i, ∀ z ∈ C i, u i z ≠ ⊥) (t : Finset ι) :
    (⨆ x ∈ Set.univ.pi C, ∑ i ∈ t, u i (x i)) = ∑ i ∈ t, ⨆ z ∈ C i, u i z := by
  classical
  obtain ⟨x₀, hx₀⟩ : (Set.univ.pi C).Nonempty := Set.univ_pi_nonempty_iff.2 hne
  induction t using Finset.cons_induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact le_antisymm (iSup₂_le fun _ _ => le_rfl)
      (le_iSup₂_of_le (f := fun x (_ : x ∈ Set.univ.pi C) => (0 : EReal)) x₀ hx₀ le_rfl)
  | cons i t hi ih =>
    have hgne : ∀ x ∈ Set.univ.pi C, (∑ j ∈ t, u j (x j)) ≠ ⊥ := fun x hx =>
      sum_ne_bot fun j _ => hu j (x j) (hx j (Set.mem_univ j))
    have key : (⨆ x ∈ Set.univ.pi C, (u i (x i) + ∑ j ∈ t, u j (x j)))
        = (⨆ z ∈ C i, u i z) + ⨆ x ∈ Set.univ.pi C, ∑ j ∈ t, u j (x j) := by
      rw [biSup_add_biSup (hu i) hgne]
      refine le_antisymm (iSup₂_le fun x hx => ?_) (iSup₂_le fun z hz => iSup₂_le fun x hx => ?_)
      · exact le_iSup₂_of_le (x i) (hx i (Set.mem_univ i)) (le_iSup₂_of_le x hx le_rfl)
      · refine le_iSup₂_of_le (Function.update x i z) (fun j _ => ?_) ?_
        · rcases eq_or_ne j i with rfl | hj
          · rw [Function.update_self]; exact hz
          · rw [Function.update_of_ne hj]; exact hx j (Set.mem_univ j)
        · have hsum : ∑ j ∈ t, u j (Function.update x i z j) = ∑ j ∈ t, u j (x j) :=
            Finset.sum_congr rfl fun j hj => by
              rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)]
          rw [Function.update_self, hsum]
    simp only [Finset.sum_cons]
    rw [key, ih]

/-- Let $r$ be real and let $(u_i)$ be a family in $\overline{\mathbb{R}}$. Then
$r + \inf_i u_i = \inf_i (r + u_i)$. This is `EReal.iInf_add_coe` with the constant on the left. -/
theorem coe_add_iInf {ι : Sort*} (r : ℝ) (u : ι → EReal) :
    (r : EReal) + (⨅ i, u i) = ⨅ i, ((r : EReal) + u i) := by
  rw [add_comm, iInf_add_coe]
  exact iInf_congr fun i => add_comm _ _

/-- **A real constant minus an infimum is a supremum.** Let $r$ be real and let $(u_i)$ be a family
in $\overline{\mathbb{R}}$. Then
$$r - \inf_i u_i = \sup_i (r - u_i).$$
-/
theorem coe_sub_iInf {ι : Sort*} (r : ℝ) (u : ι → EReal) :
    (r : EReal) - ⨅ i, u i = ⨆ i, ((r : EReal) - u i) :=
  sub_iInf r u

/-- Let $\iota$ be a nonempty index type, let $a \in \overline{\mathbb{R}}$, and let
$(u_i)_{i \in \iota}$ be a family in $\overline{\mathbb{R}}$ with $\inf_i u_i \neq -\infty$.
Then
$$a + \inf_i u_i = \inf_i (a + u_i).$$

For suprema (`EReal.biSup_add_of_ne_bot`) the hypothesis is on the values. Here it is on the
infimum itself. -/
theorem add_iInf_of_ne_bot {ι : Sort*} [Nonempty ι] (a : EReal) (u : ι → EReal)
    (hu : (⨅ i, u i) ≠ ⊥) : a + (⨅ i, u i) = ⨅ i, (a + u i) := by
  have hui : ∀ i, u i ≠ ⊥ := fun i h => hu (le_bot_iff.1 (h ▸ iInf_le u i))
  induction a with
  | bot =>
    have h : ∀ i, (⊥ : EReal) + u i = ⊥ := fun i => EReal.bot_add (u i)
    rw [EReal.bot_add]
    simp only [h, iInf_const]
  | coe r =>
    rw [add_comm, iInf_add_coe]
    exact iInf_congr fun i => add_comm _ _
  | top =>
    have h : ∀ i, (⊤ : EReal) + u i = ⊤ := fun i => by
      rw [add_comm]; exact EReal.add_top_of_ne_bot (hui i)
    rw [add_comm, EReal.add_top_of_ne_bot hu]
    simp only [h, iInf_const]

/-- Let $\iota$ be a nonempty index type, let $(u_i)_{i \in \iota}$ be a family in
$\overline{\mathbb{R}}$ with $\inf_i u_i \neq -\infty$, and let $c \in \overline{\mathbb{R}}$.
Then $(\inf_i u_i) + c = \inf_i (u_i + c)$. This is `EReal.add_iInf_of_ne_bot` with the constant
on the right. -/
theorem iInf_add_of_ne_bot {ι : Sort*} [Nonempty ι] (u : ι → EReal)
    (hu : (⨅ i, u i) ≠ ⊥) (c : EReal) : (⨅ i, u i) + c = ⨅ i, (u i + c) := by
  rw [add_comm, add_iInf_of_ne_bot c u hu]
  exact iInf_congr fun i => add_comm _ _

/-- **An infimum $-\infty$ stays $-\infty$ after adding any constant except $+\infty$.** Let $\iota$
be a nonempty index type, let $(u_i)_{i \in \iota}$ be a family in $\overline{\mathbb{R}}$ with
$\inf_i u_i = -\infty$, and let $c \in \overline{\mathbb{R}}$ with $c \neq +\infty$. Then
$\inf_i (u_i + c) = -\infty$. -/
theorem iInf_add_eq_bot {ι : Sort*} [Nonempty ι] {u : ι → EReal} (hu : (⨅ i, u i) = ⊥)
    {c : EReal} (hc : c ≠ ⊤) : (⨅ i, (u i + c)) = ⊥ := by
  induction c with
  | bot => simp
  | coe r => rw [← iInf_add_coe, hu, EReal.bot_add]
  | top => exact absurd rfl hc

/-- **The infimum of a sum splits.** Let $\iota$ and $\kappa$ be nonempty index types, and let
$(u_i)_{i \in \iota}$ and $(v_j)_{j \in \kappa}$ be families in $\overline{\mathbb{R}}$ with
$\inf_i u_i \neq -\infty$ and $\inf_j v_j \neq -\infty$. Then
$$\inf_i u_i + \inf_j v_j = \inf_i \inf_j (u_i + v_j).$$

This is the version of `EReal.biSup_add_biSup` for infima, but with a different hypothesis.
`EReal.biSup_add_biSup` assumes that the values avoid $-\infty$. Here the hypothesis is that the
two infima avoid $-\infty$. -/
theorem iInf_add_iInf_of_ne_bot {ι κ : Sort*} [Nonempty ι] [Nonempty κ]
    (u : ι → EReal) (v : κ → EReal) (hu : (⨅ i, u i) ≠ ⊥) (hv : (⨅ j, v j) ≠ ⊥) :
    (⨅ i, u i) + (⨅ j, v j) = ⨅ i, ⨅ j, (u i + v j) := by
  rw [iInf_add_of_ne_bot u hu]
  exact iInf_congr fun i => add_iInf_of_ne_bot (u i) v hv

/-- **The infimum of a separated sum over a product splits.** Let $\alpha$ and $\beta$ be nonempty
types, and let $\psi \colon \alpha \to \overline{\mathbb{R}}$ and
$\varphi \colon \beta \to \overline{\mathbb{R}}$ with $\inf_a \psi(a) \neq +\infty$ and
$\inf_b \varphi(b) \neq +\infty$. Then
$$\inf_{(a, b) \in \alpha \times \beta} \bigl(\psi(a) + \varphi(b)\bigr) = \inf_a \psi(a) +
  \inf_b \varphi(b).$$

Unlike `EReal.iInf_add_iInf_of_ne_bot`, this result handles the cases with $-\infty$ instead of
excluding them: when one infimum is $-\infty$, the other infimum is less than $+\infty$, and
both sides are $-\infty$. Some hypothesis is necessary. For $\psi(i) = -i$ on $\mathbb{N}$ and
$\varphi \equiv +\infty$, the left side is $+\infty$ and the right side is $-\infty$. -/
theorem iInf_prod_add {α β : Type*} [Nonempty α] [Nonempty β] (ψ : α → EReal) (φ : β → EReal)
    (hψ : (⨅ a, ψ a) ≠ ⊤) (hφ : (⨅ b, φ b) ≠ ⊤) :
    (⨅ p : α × β, (ψ p.1 + φ p.2)) = (⨅ a, ψ a) + ⨅ b, φ b := by
  have hprod : (⨅ p : α × β, (ψ p.1 + φ p.2)) = ⨅ a, ⨅ b, (ψ a + φ b) := iInf_prod
  rw [hprod]
  by_cases hψb : (⨅ a, ψ a) = ⊥
  · obtain ⟨b₀, hb₀⟩ : ∃ b, φ b ≠ ⊤ := by
      by_contra hcon
      exact hφ (le_antisymm le_top (le_iInf fun b => ge_of_eq (not_not.1 (not_exists.1 hcon b))))
    rw [hψb, EReal.bot_add]
    refine le_antisymm (le_trans (iInf_mono fun a => iInf_le _ b₀) ?_) bot_le
    exact le_of_eq (iInf_add_eq_bot hψb hb₀)
  by_cases hφb : (⨅ b, φ b) = ⊥
  · obtain ⟨a₀, ha₀⟩ : ∃ a, ψ a ≠ ⊤ := by
      by_contra hcon
      exact hψ (le_antisymm le_top (le_iInf fun a => ge_of_eq (not_not.1 (not_exists.1 hcon a))))
    rw [hφb, EReal.add_bot]
    refine le_antisymm (le_trans (iInf_le _ a₀) ?_) bot_le
    refine le_of_eq ?_
    rw [← iInf_add_eq_bot (u := φ) hφb ha₀]
    exact iInf_congr fun b => add_comm _ _
  · exact (iInf_add_iInf_of_ne_bot ψ φ hψb hφb).symm

/-- **A real summand moves out of a difference.** Let $p, q$ be real and let
$u \in \overline{\mathbb{R}}$. Then
$$(p + q) - u = (p - u) + q.$$
-/
theorem coe_add_sub (p q : ℝ) (u : EReal) :
    ((p + q : ℝ) : EReal) - u = (((p : ℝ) : EReal) - u) + ((q : ℝ) : EReal) := by
  rw [EReal.coe_add]
  change ((p : EReal) + (q : EReal)) + -u = ((p : EReal) + -u) + (q : EReal)
  rw [add_assoc, add_assoc, add_comm ((q : ℝ) : EReal) (-u)]

/-- **A real summand moves out of the subtrahend.** Let $p, q$ be real and let
$u \in \overline{\mathbb{R}}$. Then
$$p - (u + q) = (p - q) - u.$$

Both $p$ and $q$ are finite, so no $\infty - \infty$ occurs: at $u = +\infty$ both sides are
$-\infty$, and at $u = -\infty$ both sides are $+\infty$. -/
theorem coe_sub_add_coe (p q : ℝ) (u : EReal) :
    ((p : ℝ) : EReal) - (u + ((q : ℝ) : EReal)) = ((p - q : ℝ) : EReal) - u := by
  induction u with
  | bot =>
    rw [EReal.bot_add, EReal.sub_bot (EReal.coe_ne_bot p),
      EReal.sub_bot (EReal.coe_ne_bot _)]
  | coe r =>
    rw [← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_sub,
      EReal.coe_eq_coe_iff]
    ring
  | top => rw [EReal.top_add_coe, EReal.sub_top, EReal.sub_top]

/-- Let $p, q$ be real and let $u \in \overline{\mathbb{R}}$. Then
$$p - (u + q) = (p - u) + (-q).$$

This is `EReal.coe_sub_add_coe` in another form: `EReal.coe_sub_add_coe` collects both real
numbers on the left, and this form keeps $p - u$ intact. Each form follows from the other, but a
rewrite matches only one of them. -/
theorem coe_sub_add_coe' (p q : ℝ) (u : EReal) :
    ((p : ℝ) : EReal) - (u + ((q : ℝ) : EReal)) = (((p : ℝ) : EReal) - u) + ((-q : ℝ) : EReal) := by
  induction u with
  | bot => simp
  | coe r =>
    rw [← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_sub,
      ← EReal.coe_add, EReal.coe_eq_coe_iff]
    ring
  | top => simp

/-- **The difference quotient of a sum splits.** Let $c > 0$, $p$ and $q$ be real, and let
$u, v \in \overline{\mathbb{R}}$ with $u \neq -\infty$ and $v \neq -\infty$. Then
$$c(u - p) + c(v - q) = c\bigl((u + v) - (p + q)\bigr).$$

This is the arithmetic behind the part of Theorem 9.3 of [rockafellar1970convex] on recession
functions: the difference quotients that define $f0^+$ and $g0^+$ add up to the difference
quotient that defines $(f + g)0^+$. -/
theorem coe_mul_sub_add_coe_mul_sub {c : ℝ} (hc : 0 < c) {u v : EReal} (hu : u ≠ ⊥) (hv : v ≠ ⊥)
    (p q : ℝ) :
    (c : EReal) * (u - (p : ℝ)) + (c : EReal) * (v - (q : ℝ))
      = (c : EReal) * ((u + v) - ((p + q : ℝ) : EReal)) := by
  have hsubne : ∀ {w : EReal}, w ≠ ⊥ → ∀ r : ℝ, w - (r : ℝ) ≠ ⊥ := by
    intro w hw r
    rw [sub_eq_add_neg, ← EReal.coe_neg]
    exact EReal.add_ne_bot_iff.2 ⟨hw, EReal.coe_ne_bot _⟩
  have hcn : ¬ ((c : EReal) < 0) := by
    simp only [not_lt]
    exact_mod_cast hc.le
  have hmulne : ∀ {w : EReal}, w ≠ ⊥ → (c : EReal) * w ≠ ⊥ := by
    intro w hw hbot
    rw [EReal.mul_eq_bot] at hbot
    rcases hbot with ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨h3, -⟩ | ⟨h4, -⟩
    · exact EReal.coe_ne_bot c h1
    · exact hw h2
    · exact EReal.coe_ne_top c h3
    · exact hcn h4
  rcases eq_top_or_lt_top u with hut | hut
  · have huv : u + v = ⊤ := by rw [hut]; exact EReal.top_add_of_ne_bot hv
    rw [huv, hut, EReal.top_sub_coe, EReal.top_sub_coe,
      EReal.coe_mul_top_of_pos hc,
      EReal.top_add_of_ne_bot (hmulne (hsubne hv q))]
  rcases eq_top_or_lt_top v with hvt | hvt
  · have huv : u + v = ⊤ := by rw [hvt]; exact EReal.add_top_of_ne_bot hu
    rw [huv, hvt, EReal.top_sub_coe, EReal.top_sub_coe,
      EReal.coe_mul_top_of_pos hc,
      EReal.add_top_of_ne_bot (hmulne (hsubne hu p))]
  obtain ⟨r, hr⟩ := exists_coe_of_ne_bot_of_lt_top hu hut
  obtain ⟨s, hs⟩ := exists_coe_of_ne_bot_of_lt_top hv hvt
  rw [hr, hs, ← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_sub,
    ← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_mul,
    ← EReal.coe_mul, ← EReal.coe_add]
  norm_cast
  ring

/-- **Two slack inequalities cannot compensate each other.** Let $p, q$ be real and let
$u, v \in \overline{\mathbb{R}}$ with $p \le u$, $q \le v$ and $u + v \le p + q$. Then
$u \le p$, so $u = p$.

The statement is for the first summand only. For the second summand, apply it again with the
summands exchanged. Theorem 23.8 of [rockafellar1970convex] needs it: the exact-sum hypothesis
gives one joint equality in Fenchel's inequality, and this result splits it into
$y_1 \in \partial f(x)$ and $y_2 \in \partial g(x)$. -/
theorem le_coe_of_add_le_coe_add {p q : ℝ} {u v : EReal} (hp : (p : EReal) ≤ u)
    (hq : (q : EReal) ≤ v) (h : u + v ≤ ((p + q : ℝ) : EReal)) : u ≤ (p : EReal) := by
  have hub : u ≠ ⊥ := ((EReal.bot_lt_coe p).trans_le hp).ne'
  have hvb : v ≠ ⊥ := ((EReal.bot_lt_coe q).trans_le hq).ne'
  have hsum : u + v ≠ ⊤ := fun hc =>
    EReal.coe_ne_top _ (top_le_iff.1 (hc ▸ h))
  obtain ⟨hut, hvt⟩ := (EReal.add_ne_top_iff_ne_top₂ hub hvb).1 hsum
  obtain ⟨a, rfl⟩ := exists_coe_of_ne_bot_of_lt_top hub (lt_top_iff_ne_top.2 hut)
  obtain ⟨b, rfl⟩ := exists_coe_of_ne_bot_of_lt_top hvb (lt_top_iff_ne_top.2 hvt)
  rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h
  rw [EReal.coe_le_coe_iff] at hp hq ⊢
  linarith

/-- **The version of `EReal.le_coe_of_add_le_coe_add` for finite sums.** Let $s$ be a finite set,
let $c_i$ be real and $u_i \in \overline{\mathbb{R}}$ with $c_i \le u_i$ for all $i \in s$, and
suppose that
$$\sum_{i \in s} u_i \le \sum_{i \in s} c_i.$$
Then $u_j \le c_j$, and so $u_j = c_j$, for every $j \in s$.

The two-summand version does not iterate, because $\overline{\mathbb{R}}$ has no subtraction
that removes a summand. So the proof splits $s$ as $\{j\} \cup (s \setminus \{j\})$ and applies
the two-summand version once, with the two partial sums as the second pair. -/
theorem le_coe_of_sum_le_coe_sum {ι : Type*} {s : Finset ι} {c : ι → ℝ} {u : ι → EReal}
    (hle : ∀ i ∈ s, ((c i : ℝ) : EReal) ≤ u i)
    (hsum : ∑ i ∈ s, u i ≤ ((∑ i ∈ s, c i : ℝ) : EReal)) {j : ι} (hj : j ∈ s) :
    u j ≤ ((c j : ℝ) : EReal) := by
  classical
  have hq : ((∑ i ∈ s.erase j, c i : ℝ) : EReal) ≤ ∑ i ∈ s.erase j, u i := by
    rw [coe_sum]
    exact Finset.sum_le_sum fun i hi => hle i (Finset.mem_of_mem_erase hi)
  have hadd : u j + ∑ i ∈ s.erase j, u i
      ≤ ((c j + ∑ i ∈ s.erase j, c i : ℝ) : EReal) := by
    rw [Finset.add_sum_erase s u hj, Finset.add_sum_erase s c hj]
    exact hsum
  exact le_coe_of_add_le_coe_add (hle j hj) hq hadd

/-!
### The embedding of $\mathbb{R}$ in $\overline{\mathbb{R}}$ and conditionally complete extrema
-/

/-- Let $s \subseteq \mathbb{R}$ be nonempty and bounded above. Then the embedding of $\mathbb{R}$
in $\overline{\mathbb{R}}$ maps $\sup s$ to the supremum in $\overline{\mathbb{R}}$ of the image
of $s$:
$$\sup s = \sup_{a \in s} a \quad \text{in } \overline{\mathbb{R}}.$$

The embedding is an order embedding, but the supremum on $\mathbb{R}$ is only conditionally
complete, so the statement needs both hypotheses. -/
theorem coe_sSup_of_bddAbove {s : Set ℝ} (hne : s.Nonempty) (hbdd : BddAbove s) :
    ((sSup s : ℝ) : EReal) = ⨆ a ∈ s, (a : EReal) := by
  rw [← sSup_image]
  refine (IsLUB.sSup_eq ⟨?_, ?_⟩).symm
  · rintro _ ⟨a, ha, rfl⟩
    exact EReal.coe_le_coe_iff.2 (le_csSup hbdd ha)
  · intro b hb
    induction b with
    | bot =>
      obtain ⟨a, ha⟩ := hne
      exact absurd (le_bot_iff.1 (hb ⟨a, ha, rfl⟩)) (EReal.coe_ne_bot a)
    | coe r =>
      exact EReal.coe_le_coe_iff.2
        (csSup_le hne fun a ha => EReal.coe_le_coe_iff.1 (hb ⟨a, ha, rfl⟩))
    | top => exact le_top

/-- Let $s \subseteq \mathbb{R}$ be nonempty and bounded below. Then the embedding of $\mathbb{R}$
in $\overline{\mathbb{R}}$ maps $\inf s$ to the infimum in $\overline{\mathbb{R}}$ of the image
of $s$. -/
theorem coe_sInf_of_bddBelow {s : Set ℝ} (hne : s.Nonempty) (hbdd : BddBelow s) :
    ((sInf s : ℝ) : EReal) = ⨅ a ∈ s, (a : EReal) := by
  rw [← sInf_image]
  refine (IsGLB.sInf_eq ⟨?_, ?_⟩).symm
  · rintro _ ⟨a, ha, rfl⟩
    exact EReal.coe_le_coe_iff.2 (csInf_le hbdd ha)
  · intro b hb
    induction b with
    | bot => exact bot_le
    | coe r =>
      exact EReal.coe_le_coe_iff.2
        (le_csInf hne fun a ha => EReal.coe_le_coe_iff.1 (hb ⟨a, ha, rfl⟩))
    | top =>
      obtain ⟨a, ha⟩ := hne
      exact absurd (top_le_iff.1 (hb ⟨a, ha, rfl⟩)) (EReal.coe_ne_top a)

end EReal

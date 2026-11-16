/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Basic

/-!
# The Schur–Cohn test for roots inside the unit disc

A real polynomial $P$ is **Schur stable** when all of its complex roots have modulus less than $1$.
For the first characteristic polynomial of a linear multistep method, this condition makes every
solution of the associated difference equation tend to zero. The classical recursion of Schur (1918)
and Cohn (1922), tabulated by Jury, decides Schur stability. Let $P$ have formal degree $n$, with
coefficients $a_n$ and $a_0$ of $X^n$ and $X^0$, and let $P^\sharp(X) = X^n P(1/X)$ be the
polynomial with the coefficients in reverse order. Then
$$Q = \frac{a_n P - a_0 P^\sharp}{X}$$
is a polynomial of formal degree $n - 1$, and if $|a_0| < |a_n|$, then $P$ is Schur stable as soon
as $Q$ is. Repeated down to a nonzero constant, the recursion decides Schur stability by rational
arithmetic alone.

In this library, the test is used for the root condition of [quarteroni2000numerical], §11.6.3: the
zero-stability of the backward differentiation formulae is the Schur stability of the spurious
factor of the first characteristic polynomial $\rho$.

## Main definitions

* `Polynomial.IsSchurStable`: every complex root of $P$ has modulus less than $1$.
* `Polynomial.IsSchurCohnPair`: for every $z \in \mathbb{C}$ with $|z| \ge 1$, $P(z) \neq 0$ and
  $|P^\sharp(z)| \le |P(z)|$, for a given companion polynomial $P^\sharp$.

## Main results

* `Polynomial.IsSchurCohnPair.isSchurStable`: the invariant implies Schur stability.
* `Polynomial.isSchurCohnPair_C`: a nonzero constant, with itself as companion, satisfies the
  invariant.
* `Polynomial.IsSchurCohnPair.step`: if $|B| < |A|$, $c \neq 0$, $c X Q = A P - B P^\sharp$ and
  $c Q^\sharp = A P^\sharp - B P$, then the invariant passes from $(Q, Q^\sharp)$ to
  $(P, P^\sharp)$.
* `Polynomial.IsSchurCohnPair.reflect_step`: the same step in its classical form, with the
  coefficient reversals as companions.

## Proof outline

The proof uses neither Rouché's theorem nor the argument principle, which Mathlib does not have.
Instead it carries a stronger invariant down the recursion: for every $z$ with $|z| \ge 1$,
$P(z) \neq 0$ and $|P^\sharp(z)| \le |P(z)|$. One step uses the two identities
$$c X Q = A P - B P^\sharp, \qquad c Q^\sharp = A P^\sharp - B P,$$
with $A = a_n$ and $B = a_0$; the second follows from the first by reversal of the coefficients.
They give $c (A z Q + B Q^\sharp) = (A^2 - B^2) P$ and
$c (B z Q + A Q^\sharp) = (A^2 - B^2) P^\sharp$. Then $|A z Q(z) + B Q^\sharp(z)| \ge (|A| - |B|)
|Q(z)| > 0$, so $P(z) \neq 0$. The identity
$$|A u + B v|^2 - |B u + A v|^2 = (A^2 - B^2)(|u|^2 - |v|^2)$$
for real $A$, $B$ and complex $u$, $v$, applied with $u = z Q(z)$ and $v = Q^\sharp(z)$ and
$|z| \ge 1$, gives $|P^\sharp(z)| \le |P(z)|$. At the base of the recursion, a nonzero constant, the
invariant is trivial.

## Implementation notes

* `Polynomial.IsSchurCohnPair` takes an arbitrary companion polynomial instead of
  `Polynomial.reflect n P`. A concrete chain is then checked by two polynomial identities per step
  (by `ring`) and one numerical inequality (by `norm_num`), without bookkeeping of
  `Polynomial.natDegree`. `Polynomial.IsSchurCohnPair.reflect_step` is the classical statement, in
  which the companion is the reversal and the second identity is automatic.
* Only the sufficiency half of the Schur–Cohn criterion is proved, because it is what decides a
  concrete polynomial. The converse, that Schur stability forces $|a_0| < |a_n|$ and passes to $Q$,
  is not needed here.
* The material is general and is a candidate for Mathlib, with natural home
  `Mathlib.Analysis.Polynomial`.
-/

open Polynomial

namespace Polynomial

/-- A real polynomial $P$ is **Schur stable** if every complex root $z$ of $P$ satisfies $|z| < 1$.

For the first characteristic polynomial of a difference equation, this is the condition that
makes every solution tend to zero ([quarteroni2000numerical], §11.6.3). -/
def IsSchurStable (P : ℝ[X]) : Prop := ∀ z : ℂ, aeval z P = 0 → ‖z‖ < 1

/-- The **Schur–Cohn invariant** of a pair of real polynomials $P$ and $P^\sharp$: for every
$z \in \mathbb{C}$ with $|z| \ge 1$,
$$P(z) \neq 0 \quad \text{and} \quad |P^\sharp(z)| \le |P(z)|.$$

In the intended use, the companion $P^\sharp$ is the coefficient reversal
`Polynomial.reflect n P`; see `Polynomial.IsSchurCohnPair.reflect_step`. -/
def IsSchurCohnPair (P Ps : ℝ[X]) : Prop :=
  ∀ z : ℂ, 1 ≤ ‖z‖ → aeval z P ≠ 0 ∧ ‖aeval z Ps‖ ≤ ‖aeval z P‖

variable {P Ps Q Qs : ℝ[X]}

/-- If $(P, P^\sharp)$ satisfies the Schur–Cohn invariant, then $P$ is Schur stable: a polynomial
that does not vanish for $|z| \ge 1$ has all its roots in the open unit disc. -/
theorem IsSchurCohnPair.isSchurStable (h : IsSchurCohnPair P Ps) : IsSchurStable P := by
  refine fun z hz => ?_
  by_contra hlt
  exact (h z (not_lt.1 hlt)).1 hz

/-- If the real polynomial $P$ is Schur stable, then $P(z) \neq 0$ for every $z \in \mathbb{C}$ with
$|z| \ge 1$. -/
theorem IsSchurStable.aeval_ne_zero (h : IsSchurStable P) {z : ℂ} (hz : 1 ≤ ‖z‖) :
    aeval z P ≠ 0 := fun h0 => absurd (h z h0) (not_lt.2 hz)

/-- A Schur stable real polynomial is nonzero. -/
theorem IsSchurStable.ne_zero (h : IsSchurStable P) : P ≠ 0 := by
  intro h0
  exact h.aeval_ne_zero (z := 1) (by simp) (by simp [h0])

/-- The **base of the Schur–Cohn recursion**. For a real number $c \neq 0$, the pair of constant
polynomials $(c, c)$ satisfies the Schur–Cohn invariant `Polynomial.IsSchurCohnPair`. -/
theorem isSchurCohnPair_C {c : ℝ} (hc : c ≠ 0) : IsSchurCohnPair (C c) (C c) := by
  refine fun z _ => ?_
  refine ⟨?_, le_rfl⟩
  simpa using hc

/-- For real $A$, $B$ and complex $u$, $v$, $|A u + B v|^2 - |B u + A v|^2 = (A^2 - B^2)(|u|^2 -
|v|^2)$.
-/
private theorem normSq_add_sub_normSq_add_swap (A B : ℝ) (u v : ℂ) :
    Complex.normSq ((A : ℂ) * u + (B : ℂ) * v) - Complex.normSq ((B : ℂ) * u + (A : ℂ) * v) =
      (A ^ 2 - B ^ 2) * (Complex.normSq u - Complex.normSq v) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **One step of the Schur–Cohn recursion.** Let $P$, $P^\sharp$, $Q$, $Q^\sharp$ be real
polynomials and $A, B, c \in \mathbb{R}$ with $c \neq 0$ and $|B| < |A|$. Suppose that
$$c X Q = A P - B P^\sharp \quad \text{and} \quad c Q^\sharp = A P^\sharp - B P.$$
If $(Q, Q^\sharp)$ satisfies the Schur–Cohn invariant `Polynomial.IsSchurCohnPair`, then so does
$(P, P^\sharp)$.

In the intended use, $A$ and $B$ are the leading and constant coefficients $a_n$ and $a_0$ of
$P$, the two companions are the reversals `Polynomial.reflect n P` and
`Polynomial.reflect (n - 1) Q`, and $c$ is any nonzero factor scaled out of $Q$; see
`Polynomial.IsSchurCohnPair.reflect_step`. -/
theorem IsSchurCohnPair.step {A B c : ℝ} (hc : c ≠ 0) (hAB : |B| < |A|)
    (h1 : C c * (X * Q) = C A * P - C B * Ps)
    (h2 : C c * Qs = C A * Ps - C B * P)
    (h : IsSchurCohnPair Q Qs) : IsSchurCohnPair P Ps := by
  refine fun z hz => ?_
  obtain ⟨hq, hqs⟩ := h z hz
  have hD : 0 < A ^ 2 - B ^ 2 := by nlinarith [sq_abs A, sq_abs B, abs_nonneg B]
  have e1 : (c : ℂ) * (z * aeval z Q) = (A : ℂ) * aeval z P - (B : ℂ) * aeval z Ps := by
    have := congrArg (aeval z) h1
    simpa using this
  have e2 : (c : ℂ) * aeval z Qs = (A : ℂ) * aeval z Ps - (B : ℂ) * aeval z P := by
    have := congrArg (aeval z) h2
    simpa using this
  set p := aeval z P with hpdef
  set ps := aeval z Ps with hpsdef
  set q := aeval z Q with hqdef
  set qs := aeval z Qs with hqsdef
  set S : ℂ := (A : ℂ) * (z * q) + (B : ℂ) * qs with hSdef
  set T : ℂ := (B : ℂ) * (z * q) + (A : ℂ) * qs with hTdef
  have hS : (c : ℂ) * S = ((A ^ 2 - B ^ 2 : ℝ) : ℂ) * p := by
    rw [hSdef]; push_cast; linear_combination (A : ℂ) * e1 + (B : ℂ) * e2
  have hT : (c : ℂ) * T = ((A ^ 2 - B ^ 2 : ℝ) : ℂ) * ps := by
    rw [hTdef]; push_cast; linear_combination (B : ℂ) * e1 + (A : ℂ) * e2
  have hqpos : 0 < ‖q‖ := norm_pos_iff.2 hq
  have hzq : ‖q‖ ≤ ‖z * q‖ := by
    rw [norm_mul]; nlinarith
  have hlt : ‖(B : ℂ) * qs‖ < ‖(A : ℂ) * (z * q)‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    calc |B| * ‖qs‖ ≤ |B| * ‖q‖ := by gcongr
      _ < |A| * ‖q‖ := mul_lt_mul_of_pos_right hAB hqpos
      _ ≤ |A| * ‖z * q‖ := by gcongr
  have hSne : S ≠ 0 := by
    intro h0
    have he : (A : ℂ) * (z * q) = -((B : ℂ) * qs) := by
      rw [hSdef] at h0; linear_combination h0
    rw [he, norm_neg] at hlt
    exact lt_irrefl _ hlt
  refine ⟨?_, ?_⟩
  · intro h0
    rw [h0, mul_zero] at hS
    exact (mul_ne_zero (by exact_mod_cast hc) hSne) hS
  · have hkey := normSq_add_sub_normSq_add_swap A B (z * q) qs
    rw [← hSdef, ← hTdef] at hkey
    have hns : Complex.normSq qs ≤ Complex.normSq (z * q) := by
      rw [← Complex.sq_norm, ← Complex.sq_norm]
      nlinarith [norm_nonneg qs, norm_nonneg (z * q)]
    have hTS : Complex.normSq T ≤ Complex.normSq S := by nlinarith
    have hnTS : ‖T‖ ≤ ‖S‖ := by
      rw [← Complex.sq_norm, ← Complex.sq_norm] at hTS
      nlinarith [norm_nonneg T, norm_nonneg S]
    have hnS := congrArg norm hS
    have hnT := congrArg norm hT
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hD] at hnS hnT
    nlinarith [abs_nonneg c, norm_nonneg S, norm_nonneg T]

/-- **One step of the Schur–Cohn recursion, in its classical form.** Let $P$ and $Q$ be real
polynomials, let $m \in \mathbb{N}$ with $\deg Q \le m$, and let $p_0$ and $p_{m+1}$ be the
coefficients of $X^0$ and $X^{m+1}$ in $P$, with $|p_0| < |p_{m+1}|$. Suppose that
$$c X Q = p_{m+1} P - p_0 P^\sharp$$
for some real $c \neq 0$, where $P^\sharp$ is the reversal of $P$ with respect to degree
$m + 1$. If $Q$, with its reversal with respect to degree $m$ as companion, satisfies the
Schur–Cohn invariant, then so does $P$ with companion $P^\sharp$.

The reversals are `Polynomial.reflect (m + 1) P` and `Polynomial.reflect m Q`. No bound on the
degree of $P$ is assumed; the identity forces $\deg P \le m + 1$. The second identity of
`Polynomial.IsSchurCohnPair.step` is the reversal of the first, by
`reflect (m + 1) (X * Q) = reflect m Q` and the involutivity of `Polynomial.reflect`. -/
theorem IsSchurCohnPair.reflect_step {m : ℕ} {c : ℝ} (hc : c ≠ 0) (hQ : Q.natDegree ≤ m)
    (hAB : |P.coeff 0| < |P.coeff (m + 1)|)
    (h1 : C c * (X * Q) = C (P.coeff (m + 1)) * P - C (P.coeff 0) * P.reflect (m + 1))
    (h : IsSchurCohnPair Q (Q.reflect m)) : IsSchurCohnPair P (P.reflect (m + 1)) := by
  refine h.step hc hAB h1 ?_
  have hXQ : reflect (m + 1) (X * Q) = reflect m Q := by
    rw [show m + 1 = 1 + m from Nat.add_comm _ _, reflect_mul _ _ natDegree_X_le hQ,
      reflect_one_X, one_mul]
  have h2 := congrArg (reflect (m + 1)) h1
  rwa [reflect_C_mul, hXQ, reflect_sub, reflect_C_mul, reflect_C_mul, reflect_reflect] at h2

end Polynomial

/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Polynomial

/-!
# Powers at zero: big-O comparisons and the vanishing of low-order terms

Mathlib's `Asymptotics.isLittleO_pow_pow` says that $x^n = o(x^m)$ as $x \to 0$ when $m < n$. This
module adds the non-strict companion, $x^n = O(x^m)$ as $x \to 0$ when $m \le n$, and two
consequences of the form "a quantity of a given order in the step $h$ that is also of a higher order
vanishes". A real coefficient $c$ with $c h^m = O(h^{m+1})$ as $h \to 0^+$ is zero. A complex
polynomial $p$ of degree at most $n$ with $p(h) = O(h^{n+1})$ as the real number $h$ tends to $0^+$
is zero.

The order conditions of numerical methods for ordinary differential equations use these facts. The
truncation error of a method of order $q$, tested on a polynomial solution, is a polynomial or a
monomial in $h$. The lemmas turn the statement "the error is $O(h^q)$" into equations on its
coefficients, which are the algebraic order conditions.

## Main results

* `Asymptotics.isBigO_pow_pow`: $x^n = O(x^m)$ as $x \to 0$ for $m \le n$.
* `eq_zero_of_isBigO_pow_succ`: if $c h^m = O(h^{m+1})$ as $h \to 0^+$, then $c = 0$.
* `Polynomial.eq_zero_of_isBigO_pow_succ`: a complex polynomial of degree at most $n$ that is
  $O(h^{n+1})$ as the real number $h$ tends to $0^+$ is zero.

## Proof outline

If $c \neq 0$, then $h^m = c^{-1} (c h^m)$ is $O(h^{m+1})$, hence $o(h^m)$, which is false. The
statement on polynomials follows by induction on $n$: the constant term of $p$ is the limit of
$p(h)$ at $0$, hence zero, and then $p / X$ is $O(h^n)$.
-/

open Filter Topology Asymptotics

namespace Asymptotics

variable {𝕜 : Type*} [NormedDivisionRing 𝕜]

/-- Let $\mathbb{K}$ be a normed division ring and let $m \le n$ be natural numbers. Then
$x^n = O(x^m)$ as $x \to 0$ in $\mathbb{K}$. This is the non-strict companion of
`Asymptotics.isLittleO_pow_pow`. -/
theorem isBigO_pow_pow {m n : ℕ} (h : m ≤ n) :
    (fun x : 𝕜 => x ^ n) =O[𝓝 0] fun x => x ^ m := by
  rcases h.lt_or_eq with hlt | rfl
  · exact (isLittleO_pow_pow hlt).isBigO
  · exact isBigO_refl _ _

end Asymptotics

/-- Let $c \in \mathbb{R}$ and $m \in \mathbb{N}$. If
$$c h^m = O(h^{m+1}) \qquad \text{as } h \to 0^+,$$
then $c = 0$.

If $c \neq 0$, then $h^m = c^{-1} (c h^m)$ would be $O(h^{m+1}) = o(h^m)$. The limit $h \to 0^+$
is the filter `nhdsWithin 0 (Set.Ioi 0)` on $\mathbb{R}$. -/
theorem eq_zero_of_isBigO_pow_succ {c : ℝ} {m : ℕ}
    (h : (fun h : ℝ => c * h ^ m) =O[𝓝[>] 0] fun h => h ^ (m + 1)) : c = 0 := by
  by_contra hc
  have h₁ : (fun h : ℝ => h ^ m) =O[𝓝[>] 0] fun h => h ^ (m + 1) := by
    simpa [inv_mul_cancel_left₀ hc] using h.const_mul_left c⁻¹
  refine isLittleO_irrefl ?_
    (h₁.trans_isLittleO ((isLittleO_pow_pow m.lt_succ_self).mono nhdsWithin_le_nhds))
  have hne : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ^ m ≠ 0 :=
    eventually_mem_nhdsWithin.mono fun x hx => pow_ne_zero m (ne_of_gt hx)
  exact hne.frequently

/-- Let $n \in \mathbb{N}$ and let $p$ be a polynomial with complex coefficients of degree at most
$n$. If
$$p(h) = O(h^{n+1}) \qquad \text{as the real number } h \text{ tends to } 0^+,$$
then $p = 0$.

The degree is `Polynomial.natDegree`, and $p$ is evaluated at the complex number $h$. The proof
is by induction on $n$. For a constant polynomial it is the case $m = 0$ of
`eq_zero_of_isBigO_pow_succ`, applied to the norm. In general the constant term is the limit of
$p(h)$ at $0$, hence zero, and $p / X$ is $O(h^n)$. -/
theorem Polynomial.eq_zero_of_isBigO_pow_succ :
    ∀ (n : ℕ) (p : Polynomial ℂ), p.natDegree ≤ n →
      (fun h : ℝ => p.eval (h : ℂ)) =O[𝓝[>] 0] (fun h => h ^ (n + 1)) → p = 0 := by
  intro n
  induction n with
  | zero =>
    intro p hp h
    rw [Polynomial.eq_C_of_natDegree_le_zero hp] at h ⊢
    have := _root_.eq_zero_of_isBigO_pow_succ (c := ‖p.coeff 0‖) (m := 0)
      (by simpa using h.norm_left)
    rw [norm_eq_zero.1 this, map_zero]
  | succ n ih =>
    intro p hp h
    -- the constant term vanishes
    have h0 : p.coeff 0 = 0 := by
      have hlim : Tendsto (fun h : ℝ => p.eval (h : ℂ)) (𝓝[>] 0) (𝓝 (p.eval 0)) := by
        have : Tendsto (fun h : ℝ => p.eval (h : ℂ)) (𝓝 0) (𝓝 (p.eval ((0 : ℝ) : ℂ))) :=
          (p.continuous.comp Complex.continuous_ofReal).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      have hzero : Tendsto (fun h : ℝ => p.eval (h : ℂ)) (𝓝[>] 0) (𝓝 0) :=
        h.trans_tendsto <| ((continuous_pow (n + 1 + 1)).tendsto' 0 0 (by simp)).mono_left
          nhdsWithin_le_nhds
      rw [Polynomial.coeff_zero_eq_eval_zero]
      exact tendsto_nhds_unique hlim hzero
    -- so `p = divX p * X` and `divX p` is `O(h^{n+1})`
    have hpX : p = p.divX * Polynomial.X := by
      conv_lhs => rw [← p.divX_mul_X_add]
      rw [h0, map_zero, add_zero]
    have hdiv : (fun h : ℝ => p.divX.eval (h : ℂ)) =O[𝓝[>] 0] (fun h => h ^ (n + 1)) := by
      obtain ⟨C, hC⟩ := h.bound
      refine IsBigO.of_bound C ?_
      filter_upwards [hC, eventually_mem_nhdsWithin] with h hh (hpos : 0 < h)
      rw [hpX, Polynomial.eval_mul, Polynomial.eval_X, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hpos.le, Real.norm_of_nonneg (pow_pos hpos _).le, pow_succ,
        ← mul_assoc] at hh
      rw [Real.norm_of_nonneg (pow_pos hpos _).le]
      exact le_of_mul_le_mul_right hh hpos
    have := ih p.divX (by
      have := p.natDegree_divX_eq_natDegree_tsub_one
      omega) hdiv
    rw [hpX, this, zero_mul]

/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Numlib.FloatingPoint.InnerProduct
import Numlib.Stationary.Basic

/-!
# Stationary iterations in finite precision

A stationary iteration $x \mapsto Gx + c$ run in floating-point arithmetic is the exact iteration
perturbed at every step. Its accuracy is limited by the size of that perturbation, not by the number
of steps. This module proves the two halves of Theorem 17.1 of [higham2002accuracy] separately. The
first half is a statement in exact arithmetic about rounding-free perturbations: a sequence with
$x_{k+1} = G x_k + f + \xi_k$, $\|\xi_k\| \le \varepsilon$ and $\|G\| < 1$ stays within
$\|G\|^k \|x_0 - x'\| + \varepsilon/(1 - \|G\|)$ of the fixed point $x'$. The first term tends to
$0$ and the second does not, so the limiting accuracy of the iteration is $\varepsilon/(1 - \|G\|)$.
The second half is about finite precision: one computed step, formed as a matrix–vector product
followed by a rounded addition, is the exact step plus a perturbation bounded entrywise by
$\gamma_{n+1} (|G| |x| + |c|)$, which is (17.5)–(17.6) of [higham2002accuracy].

## Main definitions

* `FloatingPoint.RoundsAffineStep`: $y$ is an admissible computed value of the affine step $Gx + c$.

## Main results

* `Stationary.norm_perturbed_iterate_sub_le`: the error bound $\|x_k - x'\| \le \|G\|^k \|x_0 -
  x'\| + \varepsilon/(1 - \|G\|)$ for a perturbed stationary iteration.
* `Stationary.limsup_norm_perturbed_iterate_sub_le`: the limiting accuracy $\limsup_k \|x_k - x'\|
  \le \varepsilon/(1 - \|G\|)$.
* `FloatingPoint.exists_roundsAffineStep_eq_add`: a computed affine step is $Gx + c + \xi$ with
  $|\xi| \le \gamma_{n+1} (|G| |x| + |c|)$ entrywise.

## Implementation notes

* The two halves meet at the bound $\|\xi_k\| \le \varepsilon$, which needs a norm. The
  finite-precision half is stated over an ordered field, in the entrywise order of
  `Numlib.LinearAlgebra.Matrix.Order`. For a reader who wants the shape of an $\infty$-norm bound
  without passing to $\mathbb{R}$, `FloatingPoint.abs_sub_le_of_roundsMulVec_of_abs_le` of
  `Numlib.FloatingPoint.InnerProduct` gives the bound in terms of row sums.
* The splitting form of the computed step, $M x_{k+1} = N x_k + b$ with $M$ triangular and solved by
  substitution, is not covered by this module. The affine form here covers every splitting whose
  iteration operator $G$ has already been formed, and this is the form that the exact-arithmetic
  half uses.
-/

open scoped Matrix

namespace Stationary

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **The error of a perturbed stationary iteration.** Let $E$ be a normed space over a nontrivially
normed field, let $G$ be a continuous linear operator on $E$ with $\|G\| < 1$, and let
$f \in E$. Let $(x_k)$ and $(\xi_k)$ be sequences in $E$ with $$x_{k+1} = G x_k + f + \xi_k,
\qquad \|\xi_k\| \le \varepsilon$$ for every $k$. If $x'$ is a fixed point of the unperturbed
step, $Gx' + f = x'$, then for every $k$ $$\|x_k - x'\| \le \|G\|^k \|x_0 - x'\| +
\frac{\varepsilon}{1 - \|G\|}.$$

This is the exact-arithmetic core of Theorem 17.1 of [higham2002accuracy]. The transient term
decays geometrically, and the perturbation contributes the limiting accuracy
$\varepsilon/(1 - \|G\|)$ (see `Stationary.limsup_norm_perturbed_iterate_sub_le`). The norm
$\|G\|$ is the operator norm. -/
theorem norm_perturbed_iterate_sub_le {G : E →L[𝕜] E} {f : E} {x ξ : ℕ → E}
    (hstep : ∀ k, x (k + 1) = G (x k) + f + ξ k) {ε : ℝ} (hξ : ∀ k, ‖ξ k‖ ≤ ε) (hG : ‖G‖ < 1)
    {x' : E} (hfix : G x' + f = x') (k : ℕ) :
    ‖x k - x'‖ ≤ ‖G‖ ^ k * ‖x 0 - x'‖ + ε / (1 - ‖G‖) := by
  have hq0 : (0 : ℝ) ≤ ‖G‖ := norm_nonneg _
  have hpos : (0 : ℝ) < 1 - ‖G‖ := by linarith
  have hε : (0 : ℝ) ≤ ε := le_trans (norm_nonneg _) (hξ 0)
  have hrec : ∀ j, ‖x (j + 1) - x'‖ ≤ ‖G‖ * ‖x j - x'‖ + ε := by
    intro j
    have hsplit : x (j + 1) - x' = G (x j - x') + ξ j :=
      calc x (j + 1) - x' = G (x j) + f + ξ j - (G x' + f) := by rw [hstep j, hfix]
        _ = G (x j) - G x' + ξ j := by abel
        _ = G (x j - x') + ξ j := by rw [map_sub]
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add (G.le_opNorm _) (hξ j))
  induction k with
  | zero =>
    rw [pow_zero, one_mul]
    have : (0 : ℝ) ≤ ε / (1 - ‖G‖) := div_nonneg hε hpos.le
    linarith
  | succ k ih =>
    refine (hrec k).trans ?_
    have h1 : ‖G‖ * ‖x k - x'‖
        ≤ ‖G‖ * (‖G‖ ^ k * ‖x 0 - x'‖) + ‖G‖ * (ε / (1 - ‖G‖)) := by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left ih hq0
    have h2 : ‖G‖ * (ε / (1 - ‖G‖)) + ε = ε / (1 - ‖G‖) := by
      field_simp
      ring
    have h3 : ‖G‖ * (‖G‖ ^ k * ‖x 0 - x'‖) = ‖G‖ ^ (k + 1) * ‖x 0 - x'‖ := by ring
    linarith

/-- **The limiting accuracy of a perturbed stationary iteration** (Theorem 17.1 of
[higham2002accuracy]). Under the hypotheses of `Stationary.norm_perturbed_iterate_sub_le` (a
continuous linear $G$ with $\|G\| < 1$, $x_{k+1} = G x_k + f + \xi_k$ with
$\|\xi_k\| \le \varepsilon$, and $Gx' + f = x'$), $$\limsup_{k \to \infty} \|x_k - x'\| \le
\frac{\varepsilon}{1 - \|G\|}.$$ So the error of a contracting iteration that is perturbed by at
most $\varepsilon$ at every step is asymptotically at most $\varepsilon/(1 - \|G\|)$, however
many steps are taken. -/
theorem limsup_norm_perturbed_iterate_sub_le {G : E →L[𝕜] E} {f : E} {x ξ : ℕ → E}
    (hstep : ∀ k, x (k + 1) = G (x k) + f + ξ k) {ε : ℝ} (hξ : ∀ k, ‖ξ k‖ ≤ ε) (hG : ‖G‖ < 1)
    {x' : E} (hfix : G x' + f = x') :
    Filter.limsup (fun k => ‖x k - x'‖) Filter.atTop ≤ ε / (1 - ‖G‖) := by
  have hv : Filter.Tendsto (fun k : ℕ => ‖G‖ ^ k * ‖x 0 - x'‖ + ε / (1 - ‖G‖)) Filter.atTop
      (nhds (0 * ‖x 0 - x'‖ + ε / (1 - ‖G‖))) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hG).mul_const _).add_const _
  have hle : Filter.limsup (fun k => ‖x k - x'‖) Filter.atTop
      ≤ Filter.limsup (fun k : ℕ => ‖G‖ ^ k * ‖x 0 - x'‖ + ε / (1 - ‖G‖)) Filter.atTop :=
    Filter.limsup_le_limsup
      (Filter.Eventually.of_forall fun k => norm_perturbed_iterate_sub_le hstep hξ hG hfix k)
      (Filter.isCoboundedUnder_le_of_le _ fun k => norm_nonneg (x k - x'))
      hv.isBoundedUnder_le
  rw [hv.limsup_eq] at hle
  simpa using hle

end Stationary

namespace FloatingPoint

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {μ ν : Type*}

/-- Let $m$ be a rounding model, $G \in K^{\mu \times \nu}$, $c \in K^\mu$ and $x \in K^\nu$. A
vector $y \in K^\mu$ is an **admissible computed affine step** $Gx + c$ if there is an
admissible computed matrix–vector product $z$ of $G$ and $x$ (`FloatingPoint.RoundsMulVec`, one
inner product per row) such that $y_i$ is an admissible rounding of $z_i + c_i$ for every $i$.

This is one step of a stationary iteration whose iteration operator $G$ and constant $c$ have
already been formed. -/
def RoundsAffineStep (m : RoundingModel K) (G : Matrix μ ν K) (c : μ → K) (x : ν → K)
    (y : μ → K) : Prop :=
  ∃ z : μ → K, RoundsMulVec m G x z ∧ ∀ i, m.Rounds (z i + c i) (y i)

variable [Fintype ν]

/-- **One computed step of a stationary iteration is the exact step plus a small perturbation**
([higham2002accuracy], (17.5)–(17.6)). Let $m$ be a rounding model with unit roundoff $u < 1$,
let $n = |\nu|$ be the inner dimension, and let $(n + 1)u < 1$. If $y$ is an admissible computed
affine step $Gx + c$, then there is $\xi \in K^\mu$ with $$y = Gx + c + \xi, \qquad |\xi| \le
\gamma_{n+1} (|G| |x| + |c|),$$ where the absolute values and the inequality are entrywise.

With `Stationary.norm_perturbed_iterate_sub_le`, this gives the finite-precision half of Theorem
17.1 of [higham2002accuracy]: the perturbation is proportional to the data of the step and not
to the number of steps, so the iteration has a limiting accuracy. The matrix $|G|$ is
`Matrix.abs G`. See also Theorems 17.1–17.2 of [higham2002accuracy]. -/
theorem exists_roundsAffineStep_eq_add {m : RoundingModel K} (hu : m.u < 1)
    (hcard : ((Fintype.card ν + 1 : ℕ) : K) * m.u < 1) {G : Matrix μ ν K} {c : μ → K}
    {x : ν → K} {y : μ → K} (h : RoundsAffineStep m G c x y) :
    ∃ ξ : μ → K, y = G *ᵥ x + c + ξ ∧
      |ξ| ≤ gamma m.u (Fintype.card ν + 1) • (G.abs *ᵥ |x| + |c|) := by
  obtain ⟨z, hz, hadd⟩ := h
  have hu0 : (0 : K) ≤ m.u := m.u_nonneg
  have hcard' : (Fintype.card ν : K) * m.u < 1 := by
    have hle : (Fintype.card ν : K) * m.u ≤ ((Fintype.card ν + 1 : ℕ) : K) * m.u := by
      push_cast
      nlinarith
    linarith
  refine ⟨y - (G *ᵥ x + c), by abel, Pi.le_def.2 fun i => ?_⟩
  -- the two error contributions, and the row sum they are measured against
  set n : ℕ := Fintype.card ν with hn
  set P : K := (G.abs *ᵥ |x|) i with hP
  have hPnonneg : 0 ≤ P := by
    rw [hP]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hmul : |(G *ᵥ x) i| ≤ P := Matrix.abs_mulVec_le G x i
  have hzi : |z i - (G *ᵥ x) i| ≤ gamma m.u n * P :=
    abs_sub_le_of_roundsMulVec hu hcard' hz i
  have hyi : |y i - (z i + c i)| ≤ m.u * |z i + c i| := m.abs_sub_le (hadd i)
  -- the size of the rounded quantity
  have hzc : |z i + c i| ≤ (1 + gamma m.u n) * P + |c i| := by
    have h1 : |z i| ≤ P + gamma m.u n * P := by
      have := abs_sub_abs_le_abs_sub (z i) ((G *ᵥ x) i)
      linarith [hzi, hmul]
    calc |z i + c i| ≤ |z i| + |c i| := abs_add_le _ _
      _ ≤ (P + gamma m.u n * P) + |c i| := by linarith
      _ = (1 + gamma m.u n) * P + |c i| := by ring
  -- collect
  have hstep : gamma m.u n * (1 + m.u) + m.u ≤ gamma m.u (n + 1) :=
    gamma_mul_one_add_add_le hu0 hu hcard
  have hun : m.u ≤ gamma m.u (n + 1) :=
    le_trans (le_gamma_one hu0 hu) (gamma_mono hu0 (Nat.le_add_left 1 n) hcard)
  have hci : 0 ≤ |c i| := abs_nonneg _
  have hbound : |(y - (G *ᵥ x + c)) i| ≤ m.u * ((1 + gamma m.u n) * P + |c i|)
      + gamma m.u n * P := by
    have hsplit : (y - (G *ᵥ x + c)) i = (y i - (z i + c i)) + (z i - (G *ᵥ x) i) := by
      simp only [Pi.sub_apply, Pi.add_apply]
      ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    have := mul_le_mul_of_nonneg_left hzc hu0
    linarith
  have htarget : (gamma m.u (n + 1) • (G.abs *ᵥ |x| + |c|)) i
      = gamma m.u (n + 1) * (P + |c i|) := by
    rw [hP]
    simp [Pi.smul_apply, smul_eq_mul]
  rw [htarget]
  refine hbound.trans ?_
  nlinarith [mul_le_mul_of_nonneg_right hstep hPnonneg,
    mul_le_mul_of_nonneg_right hun hci]

end FloatingPoint

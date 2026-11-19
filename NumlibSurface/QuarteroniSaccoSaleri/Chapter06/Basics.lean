/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Nonlinear.Order

/-!
# Quarteroni, Sacco and Saleri, Chapter 6: The order of convergence

This module formalizes the opening of Chapter 6 of [quarteroni2000numerical]: Definition 6.1 of the
order of convergence of a sequence of real approximations, and the remark that follows it on the
convergence factor for $p = 1$. A sequence $x^{(k)}$ converges to $\alpha$ with order $p \ge 1$ if
it converges and the quotients $|x^{(k+1)} - \alpha| / |x^{(k)} - \alpha|^p$ are bounded by a
constant $C > 0$ from some index $k_0$ on (6.2). The module proves that this quotient form agrees
with the product form `ConvergesWithOrder` of `Numlib.Nonlinear.Order` for sequences that eventually
avoid $\alpha$.

## Main definitions

* Definition 6.1, `QuarteroniSaccoSaleri.Chapter06.definition_6_1`: convergence with order
  $p \ge 1$, in the quotient form (6.2).

## Main results

* Definition 6.1, `QuarteroniSaccoSaleri.Chapter06.definition_6_1_of_convergesWithOrder` and
  `QuarteroniSaccoSaleri.Chapter06.definition_6_1_iff`: the product form implies Definition 6.1, and
  the two agree for a sequence that eventually avoids $\alpha$.
* Remark after Definition 6.1, `QuarteroniSaccoSaleri.Chapter06.definition_6_1_convergenceFactor`: a
  bound $|x^{(k+1)} - \alpha| \le C |x^{(k)} - \alpha|$ with $0 < C < 1$ gives convergence with
  order $1$.

## Implementation notes

* In Lean, division by zero gives zero, so the quotient of (6.2) is $0$ at a term with
  $x^{(k)} = \alpha$. This is harmless in an upper bound. So Definition 6.1 follows from
  `ConvergesWithOrder` without any hypothesis, while the converse needs the sequence to avoid
  $\alpha$ eventually.

## Deviations from the source

* **Convention.** At an exact root the totalized quotient is zero and does not constrain the next
  iterate. See `QuarteroniSaccoSaleri.Chapter06.definition_6_1`.
* **Correction.** A uniform factor below one suffices for convergence, and convergent errors can
  have ratios tending to one. See
  `QuarteroniSaccoSaleri.Chapter06.definition_6_1_convergenceFactor`.
* **Remark after Definition 6.1** (correction). The source says that for $p = 1$ a factor $C < 1$ is
  necessary for convergence; it is sufficient, and a bound (6.2) with $p = 1$ and $C \ge 1$ says
  nothing about convergence. See `QuarteroniSaccoSaleri.Chapter06.definition_6_1_convergenceFactor`.
-/

open Filter Topology

namespace QuarteroniSaccoSaleri.Chapter06

/-- **Definition 6.1** of [quarteroni2000numerical]. Let $x^{(k)}$ be a sequence of real numbers,
let $\alpha \in \mathbb{R}$ and $p \ge 1$. The sequence **converges to $\alpha$ with order $p$**
if $x^{(k)} \to \alpha$ and there are $C > 0$ and $k_0$ such that $$\frac{|x^{(k+1)} -
\alpha|}{|x^{(k)} - \alpha|^p} \le C \quad \text{for all } k \ge k_0.$$ This bound is the
displayed condition (6.2).

The condition $p \ge 1$ is part of the Lean definition. At a term with $x^{(k)} = \alpha$ the
quotient is $0$, by the convention that division by zero gives zero.

**Reading.** The quotient is defined as zero when an iterate equals the root. Unlike the product
inequality this places no restriction on the next iterate.
-/
def definition_6_1 (x : ℕ → ℝ) (α : ℝ) (p : ℝ) : Prop :=
  1 ≤ p ∧ Tendsto x atTop (𝓝 α) ∧
    ∃ C > 0, ∃ k₀ : ℕ, ∀ k ≥ k₀, |x (k + 1) - α| / |x k - α| ^ p ≤ C

/-- Let $x^{(k)}$ be a real sequence, $\alpha \in \mathbb{R}$ and $p \ge 1$. If $x^{(k)}$ converges
to $\alpha$ with order $p$ in the product form of the backbone, `ConvergesWithOrder`
($x^{(k)} \to \alpha$ and $|x^{(k+1)} - \alpha| \le C |x^{(k)} - \alpha|^p$ for some $C > 0$ and
all large $k$), then it converges with order $p$ in the sense of Definition 6.1 of
[quarteroni2000numerical]. No hypothesis on the sequence is needed, because the quotient is $0$
at a term with $x^{(k)} = \alpha$. -/
theorem definition_6_1_of_convergesWithOrder {x : ℕ → ℝ} {α p : ℝ} (hp : 1 ≤ p)
    (h : ConvergesWithOrder x α p) : definition_6_1 x α p := by
  obtain ⟨hlim, C, hC, hbound⟩ := h
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hbound
  refine ⟨hp, hlim, C, hC, k₀, fun k hk => ?_⟩
  have hk' := hk₀ k hk
  simp only [Real.norm_eq_abs] at hk'
  rcases eq_or_ne (x k) α with hxk | hxk
  · rw [hxk, sub_self, abs_zero, Real.zero_rpow (by linarith), div_zero]
    exact hC.le
  · exact (div_le_iff₀ (Real.rpow_pos_of_pos (abs_pos.2 (sub_ne_zero.2 hxk)) p)).2 hk'

/-- Let $x^{(k)}$ be a real sequence and $\alpha, p \in \mathbb{R}$, and assume that
$x^{(k)} \neq \alpha$ for all large $k$. Then $x^{(k)}$ converges to $\alpha$ with order $p$ in
the sense of Definition 6.1 of [quarteroni2000numerical] if and only if $p \ge 1$ and
`ConvergesWithOrder x α p` holds.

The hypothesis is needed for the forward direction: at a term with $x^{(k)} = \alpha$ the
quotient form reads $0 \le C$, while the product form forces $x^{(k+1)} = \alpha$. -/
theorem definition_6_1_iff {x : ℕ → ℝ} {α p : ℝ} (hx : ∀ᶠ k in atTop, x k ≠ α) :
    definition_6_1 x α p ↔ 1 ≤ p ∧ ConvergesWithOrder x α p := by
  refine ⟨fun ⟨hp, hlim, C, hC, k₀, hk₀⟩ => ⟨hp, hlim, C, hC, ?_⟩,
    fun ⟨hp, h⟩ => definition_6_1_of_convergesWithOrder hp h⟩
  filter_upwards [hx, eventually_ge_atTop k₀] with k hk hk₀'
  have := hk₀ k hk₀'
  simp only [Real.norm_eq_abs]
  exact (div_le_iff₀ (Real.rpow_pos_of_pos (abs_pos.2 (sub_ne_zero.2 hk)) p)).1 this

/-- **Remark after Definition 6.1** of [quarteroni2000numerical], the convergence factor. Let
$x^{(k)}$ be a real sequence, $\alpha \in \mathbb{R}$, $0 < C < 1$ and $k_0 \in \mathbb{N}$ with
$$|x^{(k+1)} - \alpha| \le C\, |x^{(k)} - \alpha| \quad \text{for all } k \ge k_0.$$ Then
$x^{(k)}$ converges to $\alpha$ with order $1$. The constant $C$ is called the convergence
factor.

**Correction.** The source says that for $p = 1$ a factor $C < 1$ is necessary for convergence.
The condition is sufficient, as stated here. A bound (6.2) with $p = 1$ and $C \ge 1$ holds for
many sequences that do not converge, so it says nothing about convergence.

The proof uses `tendsto_of_eventually_norm_sub_succ_le` for the convergence.

**Correction.** An eventual factor below one is sufficient. It cannot be necessary for convergence:
the errors $1/(k+1)$ tend to zero with ratios tending to one.
-/
theorem definition_6_1_convergenceFactor {x : ℕ → ℝ} {α C : ℝ} {k₀ : ℕ} (hC0 : 0 < C)
    (hC : C < 1) (h : ∀ k ≥ k₀, |x (k + 1) - α| ≤ C * |x k - α|) : definition_6_1 x α 1 :=
  definition_6_1_of_convergesWithOrder le_rfl
    (convergesWithOrder_one_of_eventually_norm_sub_succ_le hC0 hC
      (eventually_atTop.2 ⟨k₀, fun k hk => by simpa [Real.norm_eq_abs] using h k hk⟩))

end QuarteroniSaccoSaleri.Chapter06

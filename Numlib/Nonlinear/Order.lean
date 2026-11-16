/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Taylor
import Numlib.Analysis.Calculus.RootMultiplicity
import Numlib.Nonlinear.FixedPoint

/-!
# Order of convergence, Aitken's $\Delta^2$ extrapolation and Steffensen's method

A sequence $(x_k)$ in a normed group converges to $\alpha$ with order $p$ if $x_k \to \alpha$ and
$\|x_{k+1} - \alpha\| \le C \|x_k - \alpha\|^p$ for some $C > 0$ and all large $k$ (Definition 6.1
of [quarteroni2000numerical]). The order $p$ is real, so that non-integer orders such as the golden
ratio are allowed. A fixed-point iteration $x \mapsto \varphi(x)$ has order $p$ at $\alpha$ if every
orbit that starts close to $\alpha$ converges to $\alpha$ with order $p$. These notions are stated
in a normed group, so that the methods for $\mathbb{R}^n$ of Chapter 7 of [quarteroni2000numerical]
can use them, together with $Q$-superlinear convergence. For a scalar iteration the module reads the
order off the ratio limit $(\varphi(x) - \alpha)/(x - \alpha)^n \to c$, and proves Property 6.4 of
[quarteroni2000numerical], the increment stopping criterion (6.31) of §6.5, Aitken's $\Delta^2$
extrapolation with its order (Property 6.7), and Steffensen's method (§6.6.1 and Exercise 6.5 of
[quarteroni2000numerical]; §3.3 of [isaacson1994analysis]).

Three statements of [quarteroni2000numerical] are repaired here. The remark after Definition 6.1
calls a factor $C < 1$ necessary for convergence of order $1$; it is sufficient
(`tendsto_of_eventually_norm_sub_succ_le`). In Property 6.4 the range $0 \le i \le p$ must read
$1 \le i \le p$. The last clause of Property 6.7, that Aitken's method at a multiple root converges
linearly with factor $1 - 1/m$, is false as printed, since $\varphi_\Delta'(\alpha) = 0$ for every
$\varphi$ with $\varphi'(\alpha) \neq 1$; it is the statement of [isaacson1994analysis] about
Steffensen's method, and it is proved as `tendsto_steffensenStep_sub_div_of_isRootOfMultiplicity`.

## Main definitions

* `ConvergesWithOrder`: convergence of a sequence with order $p$.
* `HasIterationOrder`: a fixed-point iteration has local order $p$.
* `ConvergesSuperlinearly`: $Q$-superlinear convergence.
* `aitkenRatio`: the ratio $(x_{k+2} - x_{k+1})/(x_{k+1} - x_k)$ of successive increments.
* `aitkenExtrapolation`: Aitken's extrapolation formula.
* `aitkenIterationFunction`: Aitken's iteration function $\varphi_\Delta$.
* `steffensenStep`: Steffensen's step $x - f(x)^2 / (f(x + f(x)) - f(x))$.

## Main results

* `tendsto_of_eventually_norm_sub_succ_le`: a linear error bound with factor $C < 1$ forces
  convergence.
* `hasIterationOrder_of_eventually_norm_sub_le`: a bound
  $\|\varphi(x) - \alpha\| \le C \|x - \alpha\|^n$ near $\alpha$ with $n \ge 2$ gives order $n$.
* `hasIterationOrder_one_of_tendsto_sub_div`: a ratio limit $|c| < 1$ gives order $1$.
* `tendsto_sub_div_sub_of_hasDerivAt`: the error ratios of a convergent orbit tend to
  $\varphi'(\alpha)$.
* `tendsto_sub_div_sub_succ_of_hasDerivAt`: the increment test (6.31).
* `hasIterationOrder_of_iteratedDeriv_eq_zero`: Property 6.4, order $p + 1$ when
  $\varphi^{(i)}(\alpha) = 0$ for $1 \le i \le p$.
* `tendsto_aitkenRatio`: the increment ratios tend to the limit of the error ratios (6.34).
* `hasDerivAt_aitkenIterationFunction_zero`: $\varphi_\Delta'(\alpha) = 0$ when
  $\varphi'(\alpha) \neq 1$.
* `hasIterationOrder_aitkenIterationFunction_two`: Property 6.7 for $p = 1$, order $2$.
* `hasIterationOrder_aitkenIterationFunction_of_iteratedDeriv_eq_zero`: Property 6.7 for $p \ge 2$,
  order $2p - 1$.
* `hasIterationOrder_steffensenStep_two`: Steffensen's method has order $2$ at a simple root.
* `tendsto_steffensenStep_sub_div_of_isRootOfMultiplicity`: at a root of multiplicity $m \ge 2$,
  Steffensen's method is linear with factor $1 - 1/m$.

## Proof outline

The order of a one-step scalar method comes from a ratio limit
$(\varphi(x) - \alpha)/(x - \alpha)^n \to c$ as $x \to \alpha$, $x \neq \alpha$. For $n \ge 2$ the
bound $|\varphi(x) - \alpha| \le C |x - \alpha|^n$ that the limit implies is enough for local
convergence. For $n = 1$ with $|c| < 1$, Ostrowski's theorem gives local convergence. Property 6.4,
Aitken's method, Steffensen's method and Newton's method (`Numlib.Nonlinear.ScalarNewton`) are all
instances. The ratio limits come from the slope function
$s(x) = (\varphi(x) - \alpha)/(x - \alpha)$, which is continuous at $\alpha$ when $\varphi$ is
differentiable there and $C^1$ when $\varphi$ is $C^2$ (Hadamard's lemma), and for higher orders
from the Taylor factorization of a function with vanishing derivatives.

## Implementation notes

* Every limit of error ratios assumes $x_k \neq \alpha$: an orbit that reaches the fixed point is
  constant from then on, and its ratios are $0/0$.
* The slope function is Mathlib's `dslope φ α`, and Hadamard's lemma is `ContDiffAt.dslope_same`.
  The Taylor factorization is `IsRootOfMultiplicity.exists_eq_pow_mul` of
  `Numlib.Analysis.Calculus.RootMultiplicity`.
* Aitken's iteration function $\varphi_\Delta$ is extended by $x$ itself where its denominator
  vanishes, so that a fixed point of $\varphi$ is a fixed point of $\varphi_\Delta$. The identity
  $\varphi_\Delta(x) - \alpha = ((x - \alpha)(\varphi(\varphi(x)) - \alpha) - (\varphi(x) -
  \alpha)^2) / (\varphi(\varphi(x)) - 2\varphi(x) + x)$ (`aitkenIterationFunction_sub_eq`) reduces
  all statements about $\varphi_\Delta$ to the expansions of $\varphi(x) - \alpha$ and
  $\varphi(\varphi(x)) - \alpha$.
-/

open Filter Topology Set
open scoped fwdDiff

section NormedGroup

variable {E : Type*} [NormedAddCommGroup E]

/-! ### Order of convergence in a normed group -/

/-- Let $E$ be a normed additive group, $(x_k)$ a sequence in $E$, $\alpha \in E$ and
$p \in \mathbb{R}$. The sequence **converges to $\alpha$ with order $p$** if $x_k \to \alpha$
and there is $C > 0$ such that
$$\|x_{k+1} - \alpha\| \le C \|x_k - \alpha\|^p \qquad \text{for all sufficiently large } k.$$

This is Definition 6.1 of [quarteroni2000numerical]: the inequality is (6.2) of the definition,
and the condition $x_k \to \alpha$ is the word "converges" in it. The power is the real power,
so non-integer orders are allowed, and the definition does not require $p \ge 1$. -/
def ConvergesWithOrder (x : ℕ → E) (α : E) (p : ℝ) : Prop :=
  Tendsto x atTop (𝓝 α) ∧ ∃ C > 0, ∀ᶠ k in atTop, ‖x (k + 1) - α‖ ≤ C * ‖x k - α‖ ^ p

/-- Let $E$ be a normed additive group, $\varphi \colon E \to E$ and $\alpha \in E$. The iteration
$x \mapsto \varphi(x)$ has **(local) order $p$ at $\alpha$** if there is $\varepsilon > 0$ such
that for every $x_0 \in B(\alpha, \varepsilon)$ the orbit $(\varphi^k(x_0))_k$ converges to
$\alpha$ with order $p$ in the sense of `ConvergesWithOrder`.

This is the sense in which [quarteroni2000numerical] says that a fixed-point method has order
$p$, in the sentence before Property 6.4. -/
def HasIterationOrder (φ : E → E) (α : E) (p : ℝ) : Prop :=
  ∃ ε > 0, ∀ x₀ ∈ Metric.ball α ε, ConvergesWithOrder (fun k => φ^[k] x₀) α p

/-- If $(x_k)$ converges to $\alpha$ with order $p$, then $x_k \to \alpha$. -/
theorem ConvergesWithOrder.tendsto {x : ℕ → E} {α : E} {p : ℝ} (h : ConvergesWithOrder x α p) :
    Tendsto x atTop (𝓝 α) :=
  h.1

/-- **A linear error bound with factor below one forces convergence.** Let $E$ be a normed additive
group, $(x_k)$ a sequence in $E$, $\alpha \in E$ and $C < 1$. If
$\|x_{k+1} - \alpha\| \le C \|x_k - \alpha\|$ for all sufficiently large $k$, then
$x_k \to \alpha$.

The remark after Definition 6.1 of [quarteroni2000numerical] calls the condition $C < 1$
necessary for convergence when $p = 1$. It is sufficient, as this theorem shows; the word
"necessary" is a slip. -/
theorem tendsto_of_eventually_norm_sub_succ_le {x : ℕ → E} {α : E} {C : ℝ} (hC : C < 1)
    (h : ∀ᶠ k in atTop, ‖x (k + 1) - α‖ ≤ C * ‖x k - α‖) : Tendsto x atTop (𝓝 α) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h
  have hC'0 : 0 ≤ max C 0 := le_max_right _ _
  have hC'1 : max C 0 < 1 := max_lt hC one_pos
  have hbound : ∀ n, ‖x (n + N) - α‖ ≤ max C 0 ^ n * ‖x N - α‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc ‖x (n + 1 + N) - α‖ = ‖x (n + N + 1) - α‖ := by rw [Nat.add_right_comm]
        _ ≤ C * ‖x (n + N) - α‖ := hN _ (Nat.le_add_left N n)
        _ ≤ max C 0 * ‖x (n + N) - α‖ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
        _ ≤ max C 0 * (max C 0 ^ n * ‖x N - α‖) := by gcongr
        _ = max C 0 ^ (n + 1) * ‖x N - α‖ := by ring
  rw [← Filter.tendsto_add_atTop_iff_nat N]
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun n => norm_nonneg _) hbound ?_)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hC'0 hC'1).mul_const ‖x N - α‖

/-- **Linear convergence with factor $C$.** Let $E$ be a normed additive group, $(x_k)$ a sequence
in $E$, $\alpha \in E$ and $0 < C < 1$. If $\|x_{k+1} - \alpha\| \le C \|x_k - \alpha\|$ for all
sufficiently large $k$, then $(x_k)$ converges to $\alpha$ with order $1$ in the sense of
Definition 6.1 of [quarteroni2000numerical], and $C$ is the convergence factor. -/
theorem convergesWithOrder_one_of_eventually_norm_sub_succ_le {x : ℕ → E} {α : E} {C : ℝ}
    (hC0 : 0 < C) (hC : C < 1) (h : ∀ᶠ k in atTop, ‖x (k + 1) - α‖ ≤ C * ‖x k - α‖) :
    ConvergesWithOrder x α 1 :=
  ⟨tendsto_of_eventually_norm_sub_succ_le hC h, C, hC0, h.mono fun k hk => by rwa [Real.rpow_one]⟩

/-- Let $E$ be a normed additive group, $(x_k)$ a sequence in $E$, $\alpha \in E$ and
$p, c \in \mathbb{R}$. If $x_k \neq \alpha$ for all sufficiently large $k$ and
$$\frac{\|x_{k+1} - \alpha\|}{\|x_k - \alpha\|^p} \to c,$$
then there is $C > 0$ with $\|x_{k+1} - \alpha\| \le C \|x_k - \alpha\|^p$ for all sufficiently
large $k$.

The proof takes $C = |c| + 1$. Every theorem that gives a ratio limit yields an order in the
sense of `ConvergesWithOrder` in this way. -/
theorem exists_eventually_norm_sub_succ_le_of_tendsto_ratio {x : ℕ → E} {α : E} {p c : ℝ}
    (hx : ∀ᶠ k in atTop, x k ≠ α)
    (h : Tendsto (fun k => ‖x (k + 1) - α‖ / ‖x k - α‖ ^ p) atTop (𝓝 c)) :
    ∃ C > 0, ∀ᶠ k in atTop, ‖x (k + 1) - α‖ ≤ C * ‖x k - α‖ ^ p := by
  refine ⟨|c| + 1, by positivity, ?_⟩
  filter_upwards [hx, h.eventually (gt_mem_nhds (lt_of_le_of_lt (le_abs_self c) (lt_add_one _)))]
    with k hk hlt
  have hpos : 0 < ‖x k - α‖ ^ p := Real.rpow_pos_of_pos (norm_pos_iff.2 (sub_ne_zero.2 hk)) _
  exact (div_le_iff₀ hpos).1 hlt.le

/-- Let $E$ be a normed additive group and $0 \le q \le p$. If $(x_k)$ converges to $\alpha$ with
order $p$, then it converges to $\alpha$ with order $q$.

Once the errors are below $1$, $\|x_k - \alpha\|^p \le \|x_k - \alpha\|^q$. This is why
Definition 6.1 of [quarteroni2000numerical] is in practice read as "order at least $p$". -/
theorem ConvergesWithOrder.of_le {x : ℕ → E} {α : E} {p q : ℝ} (hq : 0 ≤ q) (hpq : q ≤ p)
    (h : ConvergesWithOrder x α p) : ConvergesWithOrder x α q := by
  obtain ⟨hlim, C, hC, hbound⟩ := h
  refine ⟨hlim, C, hC, ?_⟩
  have h1 : ∀ᶠ k in atTop, ‖x k - α‖ ≤ 1 :=
    (tendsto_iff_norm_sub_tendsto_zero.1 hlim).eventually (ge_mem_nhds one_pos)
  filter_upwards [hbound, h1] with k hk hk1
  exact hk.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) hk1 hq hpq) hC.le)

/-- Let $E$ be a normed additive group, $\varphi \colon E \to E$, $\alpha \in E$, $p \in \mathbb{R}$
and $C > 0$. Suppose that $\|\varphi(x) - \alpha\| \le C \|x - \alpha\|^p$ for all $x$ in a
neighbourhood of $\alpha$, and that there is $\delta > 0$ such that the orbit
$(\varphi^k(x_0))_k$ converges to $\alpha$ for every $x_0 \in B(\alpha, \delta)$. Then the
iteration $x \mapsto \varphi(x)$ has order $p$ at $\alpha$. -/
theorem hasIterationOrder_of_eventually_of_tendsto {φ : E → E} {α : E} {p C : ℝ} (hC : 0 < C)
    (hbound : ∀ᶠ x in 𝓝 α, ‖φ x - α‖ ≤ C * ‖x - α‖ ^ p)
    (hconv : ∃ δ > 0, ∀ x₀ ∈ Metric.ball α δ, Tendsto (fun k => φ^[k] x₀) atTop (𝓝 α)) :
    HasIterationOrder φ α p := by
  obtain ⟨δ, hδ, hconv⟩ := hconv
  refine ⟨δ, hδ, fun x₀ hx₀ => ⟨hconv x₀ hx₀, C, hC, ?_⟩⟩
  filter_upwards [(hconv x₀ hx₀).eventually hbound] with k hk
  rwa [Function.iterate_succ_apply']

/-- **Order $n \ge 2$ from a bound alone.** Let $E$ be a normed additive group,
$\varphi \colon E \to E$, $\alpha \in E$, $C \in \mathbb{R}$, and $n \ge 2$ a natural number. If
$\|\varphi(x) - \alpha\| \le C \|x - \alpha\|^n$ for all $x$ in a neighbourhood of $\alpha$,
then the iteration $x \mapsto \varphi(x)$ has order $n$ at $\alpha$.

The bound at $x = \alpha$ forces $\varphi(\alpha) = \alpha$. On a small enough ball the bound
makes $\varphi$ contract towards $\alpha$ by the factor $1/2$, so orbits stay in the ball and
converge. -/
theorem hasIterationOrder_of_eventually_norm_sub_le {φ : E → E} {α : E} {C : ℝ} {n : ℕ}
    (hn : 2 ≤ n) (h : ∀ᶠ x in 𝓝 α, ‖φ x - α‖ ≤ C * ‖x - α‖ ^ n) : HasIterationOrder φ α n := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 h
  set C' : ℝ := max C 0 + 1 with hC'
  have hC'0 : 0 < C' := by positivity
  have hCC' : C ≤ C' := (le_max_left _ _).trans (lt_add_one _).le
  -- a radius on which `C' ‖x - α‖ ^ (n - 1) ≤ 1 / 2`
  obtain ⟨δ', hδ'0, hδ'δ, hδ'half⟩ : ∃ δ' > 0, δ' ≤ δ ∧ C' * δ' ^ (n - 1) ≤ 1 / 2 := by
    refine ⟨min δ (min 1 (1 / (2 * C'))), by positivity, min_le_left _ _, ?_⟩
    have h1 : min δ (min 1 (1 / (2 * C'))) ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
    have h2 : min δ (min 1 (1 / (2 * C'))) ≤ 1 / (2 * C') :=
      (min_le_right _ _).trans (min_le_right _ _)
    have h0 : 0 ≤ min δ (min 1 (1 / (2 * C'))) := by positivity
    calc C' * min δ (min 1 (1 / (2 * C'))) ^ (n - 1)
        ≤ C' * min δ (min 1 (1 / (2 * C'))) ^ 1 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one h0 h1 (by omega)) hC'0.le
      _ ≤ C' * (1 / (2 * C')) := by rw [pow_one]; gcongr
      _ = 1 / 2 := by field_simp
  have hhalf : ∀ x ∈ Metric.ball α δ', ‖φ x - α‖ ≤ 1 / 2 * ‖x - α‖ := by
    intro x hx
    have hxδ : dist x α < δ := lt_of_lt_of_le (Metric.mem_ball.1 hx) hδ'δ
    have hxδ' : ‖x - α‖ ≤ δ' := by rw [← dist_eq_norm]; exact (Metric.mem_ball.1 hx).le
    calc ‖φ x - α‖ ≤ C * ‖x - α‖ ^ n := hball hxδ
      _ ≤ C' * ‖x - α‖ ^ n := mul_le_mul_of_nonneg_right hCC' (by positivity)
      _ = C' * ‖x - α‖ ^ (n - 1) * ‖x - α‖ := by
          rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel (by omega)]
      _ ≤ C' * δ' ^ (n - 1) * ‖x - α‖ := by gcongr
      _ ≤ 1 / 2 * ‖x - α‖ := by gcongr
  refine hasIterationOrder_of_eventually_of_tendsto hC'0 ?_ ⟨δ', hδ'0, fun x₀ hx₀ => ?_⟩
  · filter_upwards [h] with x hx
    rw [Real.rpow_natCast]
    exact hx.trans (mul_le_mul_of_nonneg_right hCC' (by positivity))
  · refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun k => norm_nonneg _)
      (fun k => (norm_iterate_sub_le_pow_mul_of_ball (by norm_num) (by norm_num) hhalf hx₀ k).2)
      ?_)
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)).mul_const ‖x₀ - α‖

/-- Let $E$ be a normed additive group, $(x_k)$ a sequence in $E$ and $\alpha \in E$. The sequence
**converges $Q$-superlinearly to $\alpha$** if there are reals $c_k \to 0$ with
$\|x_{k+1} - \alpha\| \le c_k \|x_k - \alpha\|$ for all $k$.

Sequences that reach $\alpha$ after finitely many steps are included. -/
def ConvergesSuperlinearly (x : ℕ → E) (α : E) : Prop :=
  ∃ c : ℕ → ℝ, Tendsto c atTop (𝓝 0) ∧ ∀ k, ‖x (k + 1) - α‖ ≤ c k * ‖x k - α‖

/-- If $(x_k)$ converges $Q$-superlinearly to $\alpha$, then $x_k \to \alpha$. -/
theorem ConvergesSuperlinearly.tendsto {x : ℕ → E} {α : E} (h : ConvergesSuperlinearly x α) :
    Tendsto x atTop (𝓝 α) := by
  obtain ⟨c, hc, hle⟩ := h
  refine tendsto_of_eventually_norm_sub_succ_le (C := 1 / 2) (by norm_num) ?_
  filter_upwards [hc.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with k hk
  exact (hle k).trans (mul_le_mul_of_nonneg_right hk.le (norm_nonneg _))

/-- If $(x_k)$ converges $Q$-superlinearly to $\alpha$, then it converges to $\alpha$ with order
$1$, with constant $C = 1$. -/
theorem ConvergesSuperlinearly.convergesWithOrder_one {x : ℕ → E} {α : E}
    (h : ConvergesSuperlinearly x α) : ConvergesWithOrder x α 1 := by
  refine ⟨h.tendsto, 1, one_pos, ?_⟩
  obtain ⟨c, hc, hle⟩ := h
  filter_upwards [hc.eventually (gt_mem_nhds one_pos)] with k hk
  rw [Real.rpow_one]
  exact (hle k).trans (mul_le_mul_of_nonneg_right hk.le (norm_nonneg _))

/-- Let $(x_k)$ be a sequence with $x_k \neq \alpha$ for all $k$. Then $(x_k)$ converges
$Q$-superlinearly to $\alpha$ if and only if $\|x_{k+1} - \alpha\| / \|x_k - \alpha\| \to 0$. -/
theorem convergesSuperlinearly_iff_tendsto_ratio {x : ℕ → E} {α : E} (hne : ∀ k, x k ≠ α) :
    ConvergesSuperlinearly x α ↔
      Tendsto (fun k => ‖x (k + 1) - α‖ / ‖x k - α‖) atTop (𝓝 0) := by
  have hpos : ∀ k, 0 < ‖x k - α‖ := fun k => norm_pos_iff.2 (sub_ne_zero.2 (hne k))
  constructor
  · rintro ⟨c, hc, hle⟩
    refine squeeze_zero (fun k => div_nonneg (norm_nonneg _) (norm_nonneg _)) (fun k => ?_) hc
    exact (div_le_iff₀ (hpos k)).2 (hle k)
  · intro h
    exact ⟨_, h, fun k => (div_mul_cancel₀ _ (hpos k).ne').ge⟩

end NormedGroup

section Scalar

variable {φ : ℝ → ℝ} {α : ℝ}

/-!
### Ratio limits for scalar iterations

In this section $\varphi \colon \mathbb{R} \to \mathbb{R}$ and $\alpha \in \mathbb{R}$.
-/

/-- Let $\varphi(\alpha) = \alpha$, let $c \in \mathbb{R}$ and $n \in \mathbb{N}$, and suppose that
$(\varphi(x) - \alpha)/(x - \alpha)^n \to c$ as $x \to \alpha$, $x \neq \alpha$. Then
$|\varphi(x) - \alpha| \le (|c| + 1) |x - \alpha|^n$ for all $x$ in a neighbourhood of $\alpha$. -/
theorem eventually_abs_sub_le_mul_abs_pow_of_tendsto (hα : φ α = α) {c : ℝ} {n : ℕ}
    (h : Tendsto (fun x => (φ x - α) / (x - α) ^ n) (𝓝[≠] α) (𝓝 c)) :
    ∀ᶠ x in 𝓝 α, |φ x - α| ≤ (|c| + 1) * |x - α| ^ n := by
  have h1 := h.eventually (gt_mem_nhds (lt_of_le_of_lt (le_abs_self c) (lt_add_one _)))
  have h2 := h.eventually (lt_mem_nhds (neg_lt_of_abs_lt (lt_add_one |c|)))
  rw [eventually_nhdsWithin_iff] at h1 h2
  filter_upwards [h1, h2] with x hx1 hx2
  by_cases hxα : x = α
  · simp only [hxα, hα, sub_self, abs_zero]
    positivity
  · have hpos : 0 < |(x - α) ^ n| := abs_pos.2 (pow_ne_zero _ (sub_ne_zero.2 hxα))
    rw [← abs_pow, ← div_le_iff₀ hpos, ← abs_div]
    exact abs_le.2 ⟨(hx2 hxα).le, (hx1 hxα).le⟩

/-- **Order $n \ge 2$ from a ratio limit.** Let $\varphi(\alpha) = \alpha$, let $c \in \mathbb{R}$,
let $n \ge 2$ be a natural number, and suppose that
$$\frac{\varphi(x) - \alpha}{(x - \alpha)^n} \to c \qquad \text{as } x \to \alpha,\ x \neq
  \alpha.$$
Then the iteration $x \mapsto \varphi(x)$ has order $n$ at $\alpha$. -/
theorem hasIterationOrder_of_tendsto_sub_div_pow (hα : φ α = α) {c : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (h : Tendsto (fun x => (φ x - α) / (x - α) ^ n) (𝓝[≠] α) (𝓝 c)) :
    HasIterationOrder φ α n :=
  hasIterationOrder_of_eventually_norm_sub_le hn
    (by simpa [Real.norm_eq_abs] using eventually_abs_sub_le_mul_abs_pow_of_tendsto hα h)

/-- **Order $1$ from a ratio limit below one.** Let $\varphi(\alpha) = \alpha$, let $|c| < 1$, and
suppose that $(\varphi(x) - \alpha)/(x - \alpha) \to c$ as $x \to \alpha$, $x \neq \alpha$. Then
the iteration $x \mapsto \varphi(x)$ has order $1$ at $\alpha$.

The limit $c$ is $\varphi'(\alpha)$, and Ostrowski's theorem gives the convergence. -/
theorem hasIterationOrder_one_of_tendsto_sub_div (hα : φ α = α) {c : ℝ} (hc : |c| < 1)
    (h : Tendsto (fun x => (φ x - α) / (x - α)) (𝓝[≠] α) (𝓝 c)) : HasIterationOrder φ α 1 := by
  have hderiv : HasDerivAt φ c α := by
    rw [hasDerivAt_iff_tendsto_slope]
    refine h.congr fun x => ?_
    rw [slope_def_field, hα]
  obtain ⟨q, hq, hq1⟩ := exists_between hc
  have hq0 : 0 < q := lt_of_le_of_lt (abs_nonneg _) hq
  refine hasIterationOrder_of_eventually_of_tendsto hq0 ?_ ?_
  · filter_upwards [eventually_abs_sub_le_mul_of_hasDerivAt hα hderiv hq] with x hx
    simpa [Real.norm_eq_abs] using hx
  · obtain ⟨δ, hδ, hconv⟩ := tendsto_iterate_of_abs_deriv_lt_one hα hderiv hc
    exact ⟨δ, hδ, fun x₀ hx₀ => hconv x₀ (by simpa [Metric.mem_ball, Real.dist_eq] using hx₀)⟩

/-- **The error ratios tend to $\varphi'(\alpha)$.** Let $\varphi$ have derivative $\varphi'$ at
$\alpha$, with $\varphi(\alpha) = \alpha$. Let $(x_k)$ be a sequence with
$x_{k+1} = \varphi(x_k)$ and $x_k \neq \alpha$ for all $k$, and with $x_k \to \alpha$. Then
$$\frac{x_{k+1} - \alpha}{x_k - \alpha} \to \varphi'.$$

This is (6.18) in Theorem 6.1 of [quarteroni2000numerical]. The source derives it with the mean
value theorem for $\varphi \in C^1[a, b]$; differentiability at the fixed point is enough. -/
theorem tendsto_sub_div_sub_of_hasDerivAt {φ' : ℝ} (hφ : HasDerivAt φ φ' α) (hα : φ α = α)
    {x : ℕ → ℝ} (hx : ∀ k, x (k + 1) = φ (x k)) (hne : ∀ k, x k ≠ α)
    (hlim : Tendsto x atTop (𝓝 α)) :
    Tendsto (fun k => (x (k + 1) - α) / (x k - α)) atTop (𝓝 φ') := by
  have := (hasDerivAt_iff_tendsto_slope.1 hφ).comp
    (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hne⟩)
  refine this.congr fun k => ?_
  simp [slope, hx, hα, Function.comp, vsub_eq_sub, div_eq_inv_mul]

/-- **The error ratios tend to the derivative within a set.** Let $s \subseteq \mathbb{R}$, and let
$\varphi$ have derivative $\varphi'_\alpha$ at $\alpha$ within $s$, with
$\varphi(\alpha) = \alpha$. Let $(x_k)$ be a sequence in $s$ with $x_{k+1} = \varphi(x_k)$ and
$x_k \neq \alpha$ for all $k$, and with $x_k \to \alpha$. Then $(x_{k+1} - \alpha)/(x_k -
\alpha) \to \varphi'_\alpha$.

This form of (6.18) of [quarteroni2000numerical] is needed when $\alpha$ is an endpoint of
$[a, b]$. -/
theorem tendsto_sub_div_sub_of_hasDerivWithinAt {s : Set ℝ} {φ'α : ℝ}
    (hφ : HasDerivWithinAt φ φ'α s α) (hα : φ α = α) {x : ℕ → ℝ} (hx : ∀ k, x (k + 1) = φ (x k))
    (hs : ∀ k, x k ∈ s) (hne : ∀ k, x k ≠ α) (hlim : Tendsto x atTop (𝓝 α)) :
    Tendsto (fun k => (x (k + 1) - α) / (x k - α)) atTop (𝓝 φ'α) := by
  have hmem : Tendsto x atTop (𝓝[s \ {α}] α) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun k => ⟨hs k, hne k⟩⟩
  have := (hasDerivWithinAt_iff_tendsto_slope.1 hφ).comp hmem
  refine this.congr fun k => ?_
  simp [slope, hx, hα, Function.comp, vsub_eq_sub, div_eq_inv_mul]

/-- Let $(x_k)$ be a real sequence with $x_k \neq \alpha$ for all $k$, and suppose that
$(x_{k+1} - \alpha)/(x_k - \alpha) \to l$ with $l \neq 1$. Then $x_{k+1} - x_k \neq 0$ for all
sufficiently large $k$.

The proof writes $x_{k+1} - x_k = (x_k - \alpha)(r_k - 1)$ with $r_k \to l$. -/
theorem eventually_sub_succ_ne_zero_of_tendsto_ratio {x : ℕ → ℝ} {l : ℝ} (hne : ∀ k, x k ≠ α)
    (h : Tendsto (fun k => (x (k + 1) - α) / (x k - α)) atTop (𝓝 l)) (hl : l ≠ 1) :
    ∀ᶠ k in atTop, x (k + 1) - x k ≠ 0 := by
  filter_upwards [h.eventually (isOpen_ne.mem_nhds hl)] with k hk
  have he : x k - α ≠ 0 := sub_ne_zero.2 (hne k)
  intro h0
  apply hk
  rw [show x (k + 1) - α = x k - α by linarith, div_self he]

/-- **The increment test from a ratio limit.** Let $(x_k)$ be a real sequence with $x_k \neq \alpha$
for all $k$, and suppose that $(x_{k+1} - \alpha)/(x_k - \alpha) \to l$ with $l \neq 1$. Then
$$\frac{\alpha - x_k}{x_{k+1} - x_k} \to \frac{1}{1 - l}.$$

This is the stopping criterion (6.31) of [quarteroni2000numerical]: the error $\alpha - x_k$ is
asymptotically $1/(1 - l)$ times the last increment. The error has the sign convention of the
source, which gives the constant as printed. -/
theorem tendsto_sub_div_sub_succ_of_tendsto_ratio {x : ℕ → ℝ} {l : ℝ} (hne : ∀ k, x k ≠ α)
    (h : Tendsto (fun k => (x (k + 1) - α) / (x k - α)) atTop (𝓝 l)) (hl : l ≠ 1) :
    Tendsto (fun k => (α - x k) / (x (k + 1) - x k)) atTop (𝓝 (1 / (1 - l))) := by
  refine (tendsto_const_nhds.div (tendsto_const_nhds.sub h) (sub_ne_zero.2 hl.symm)).congr
    fun k => ?_
  have he : x k - α ≠ 0 := sub_ne_zero.2 (hne k)
  simp only [Pi.div_apply]
  rw [show (1 : ℝ) - (x (k + 1) - α) / (x k - α) = (x k - α - (x (k + 1) - α)) / (x k - α) by
    field_simp, one_div_div]
  rw [show x k - α - (x (k + 1) - α) = -(x (k + 1) - x k) by ring, div_neg,
    show α - x k = -(x k - α) by ring, neg_div]

/-- **The increment test.** Let $\varphi$ have derivative $\varphi' \neq 1$ at $\alpha$, with
$\varphi(\alpha) = \alpha$. Let $(x_k)$ be a sequence with $x_{k+1} = \varphi(x_k)$ and
$x_k \neq \alpha$ for all $k$, and with $x_k \to \alpha$. Then $x_{k+1} - x_k \neq 0$ for all
sufficiently large $k$, and
$$\frac{\alpha - x_k}{x_{k+1} - x_k} \to \frac{1}{1 - \varphi'}.$$

This is the stopping criterion (6.31) of [quarteroni2000numerical]. The test is reliable when
$\varphi'(\alpha)$ is far from $1$, and optimal for methods of second order, where
$\varphi'(\alpha) = 0$. -/
theorem tendsto_sub_div_sub_succ_of_hasDerivAt {φ' : ℝ} (hφ : HasDerivAt φ φ' α) (hα : φ α = α)
    (h1 : φ' ≠ 1) {x : ℕ → ℝ} (hx : ∀ k, x (k + 1) = φ (x k)) (hne : ∀ k, x k ≠ α)
    (hlim : Tendsto x atTop (𝓝 α)) :
    (∀ᶠ k in atTop, x (k + 1) - x k ≠ 0) ∧
      Tendsto (fun k => (α - x k) / (x (k + 1) - x k)) atTop (𝓝 (1 / (1 - φ'))) :=
  ⟨eventually_sub_succ_ne_zero_of_tendsto_ratio hne
      (tendsto_sub_div_sub_of_hasDerivAt hφ hα hx hne hlim) h1,
    tendsto_sub_div_sub_succ_of_tendsto_ratio hne
      (tendsto_sub_div_sub_of_hasDerivAt hφ hα hx hne hlim) h1⟩

end Scalar

section Taylor

variable {f : ℝ → ℝ} {α : ℝ}

/-! ### Taylor expansion and Property 6.4 -/

/-- **Taylor's theorem with Peano remainder at a point.** Let $f \colon \mathbb{R} \to \mathbb{R}$
be $C^n$ at $\alpha$. Then
$$\frac{f(x) - \sum_{i=0}^{n} \frac{f^{(i)}(\alpha)}{i!} (x - \alpha)^i}{(x - \alpha)^n} \to 0
  \qquad \text{as } x \to \alpha.$$

This is Mathlib's `Real.taylor_tendsto` on a ball, with the derivatives within the open ball
replaced by the derivatives `iteratedDeriv`. -/
theorem tendsto_sub_taylor_div_pow {n : ℕ} (hf : ContDiffAt ℝ n f α) :
    Tendsto (fun x => (f x - ∑ i ∈ Finset.range (n + 1),
      iteratedDeriv i f α / i.factorial * (x - α) ^ i) / (x - α) ^ n) (𝓝 α) (𝓝 0) := by
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨r, hr, hru⟩ := Metric.mem_nhds_iff.1 hu
  have h := Real.taylor_tendsto (convex_ball α r) (Metric.mem_ball_self hr) (hfu.mono hru)
  rw [nhdsWithin_eq_nhds.2 (Metric.ball_mem_nhds α hr)] at h
  refine h.congr fun x => ?_
  rw [taylor_within_apply]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedDerivWithin_of_isOpen Metric.isOpen_ball (Metric.mem_ball_self hr), smul_eq_mul]
  ring

/-- **The limit (6.21) of Property 6.4, as a statement about $\varphi$.** Let $p \in \mathbb{N}$,
let $\varphi \colon \mathbb{R} \to \mathbb{R}$ be $C^{p+1}$ at $\alpha$ with
$\varphi(\alpha) = \alpha$, and let $\varphi^{(i)}(\alpha) = 0$ for $1 \le i \le p$. Then
$$\frac{\varphi(x) - \alpha}{(x - \alpha)^{p+1}} \to \frac{\varphi^{(p+1)}(\alpha)}{(p+1)!}
  \qquad \text{as } x \to \alpha,\ x \neq \alpha.$$

Property 6.4 of [quarteroni2000numerical] prints the range $0 \le i \le p$. This is a misprint,
since $i = 0$ would say $\varphi(\alpha) = 0$. The proof is Taylor's theorem with all
intermediate terms zero. -/
theorem tendsto_sub_div_pow_nhdsNE_of_iteratedDeriv_eq_zero {φ : ℝ → ℝ} {p : ℕ}
    (hφ : ContDiffAt ℝ (p + 1 : ℕ) φ α) (hα : φ α = α)
    (hzero : ∀ i, 1 ≤ i → i ≤ p → iteratedDeriv i φ α = 0) :
    Tendsto (fun x => (φ x - α) / (x - α) ^ (p + 1)) (𝓝[≠] α)
      (𝓝 (iteratedDeriv (p + 1) φ α / (p + 1).factorial)) := by
  have hT : ∀ x, ∑ i ∈ Finset.range (p + 1 + 1),
      iteratedDeriv i φ α / i.factorial * (x - α) ^ i =
      α + iteratedDeriv (p + 1) φ α / (p + 1).factorial * (x - α) ^ (p + 1) := by
    intro x
    rw [Finset.sum_range_succ, Finset.sum_eq_single 0]
    · simp [hα]
    · intro i hi hi0
      rw [hzero i (by omega) (by simpa [Nat.lt_succ_iff] using hi), zero_div, zero_mul]
    · simp
  have h := (tendsto_sub_taylor_div_pow hφ).mono_left (nhdsWithin_le_nhds (s := {α}ᶜ))
  simp_rw [hT] at h
  have h' := h.add_const (iteratedDeriv (p + 1) φ α / (p + 1).factorial)
  rw [zero_add] at h'
  refine h'.congr' (eventually_mem_nhdsWithin.mono fun x hx => ?_)
  have hne : (x - α) ^ (p + 1) ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hx)
  field_simp
  ring

/-- **The limit (6.21) of Property 6.4 along an orbit.** Let $p \in \mathbb{N}$, let
$\varphi \colon \mathbb{R} \to \mathbb{R}$ be $C^{p+1}$ at $\alpha$ with
$\varphi(\alpha) = \alpha$, and let $\varphi^{(i)}(\alpha) = 0$ for $1 \le i \le p$. Let $(x_k)$
be a sequence with $x_{k+1} = \varphi(x_k)$ and $x_k \neq \alpha$ for all $k$, and with
$x_k \to \alpha$. Then
$$\frac{x_{k+1} - \alpha}{(x_k - \alpha)^{p+1}} \to \frac{\varphi^{(p+1)}(\alpha)}{(p+1)!}.$$

This is Property 6.4 of [quarteroni2000numerical], with the range $1 \le i \le p$ in place of
the misprinted $0 \le i \le p$. The hypothesis $\varphi^{(p+1)}(\alpha) \neq 0$ of the source is
not needed for the limit; it makes the order exactly $p + 1$. -/
theorem tendsto_sub_div_pow_of_iteratedDeriv_eq_zero {φ : ℝ → ℝ} {p : ℕ}
    (hφ : ContDiffAt ℝ (p + 1 : ℕ) φ α) (hα : φ α = α)
    (hzero : ∀ i, 1 ≤ i → i ≤ p → iteratedDeriv i φ α = 0)
    {x : ℕ → ℝ} (hx : ∀ k, x (k + 1) = φ (x k)) (hne : ∀ k, x k ≠ α)
    (hlim : Tendsto x atTop (𝓝 α)) :
    Tendsto (fun k => (x (k + 1) - α) / (x k - α) ^ (p + 1)) atTop
      (𝓝 (iteratedDeriv (p + 1) φ α / (p + 1).factorial)) := by
  have := (tendsto_sub_div_pow_nhdsNE_of_iteratedDeriv_eq_zero hφ hα hzero).comp
    (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hne⟩)
  refine this.congr fun k => ?_
  simp [Function.comp, hx]

/-- **Property 6.4, the order.** Let $p \ge 1$, let $\varphi \colon \mathbb{R} \to \mathbb{R}$ be
$C^{p+1}$ at $\alpha$ with $\varphi(\alpha) = \alpha$, and let $\varphi^{(i)}(\alpha) = 0$ for
$1 \le i \le p$. Then the iteration $x \mapsto \varphi(x)$ has order $p + 1$ at $\alpha$.

This is Property 6.4 of [quarteroni2000numerical], with the range $1 \le i \le p$ in place of
the misprinted $0 \le i \le p$. The case $p = 0$ is excluded, because the property presupposes
convergence, and for $p = 0$ only $|\varphi'(\alpha)| < 1$ would give it. -/
theorem hasIterationOrder_of_iteratedDeriv_eq_zero {φ : ℝ → ℝ} {p : ℕ} (hp : 1 ≤ p)
    (hφ : ContDiffAt ℝ (p + 1 : ℕ) φ α) (hα : φ α = α)
    (hzero : ∀ i, 1 ≤ i → i ≤ p → iteratedDeriv i φ α = 0) :
    HasIterationOrder φ α (p + 1) := by
  have := hasIterationOrder_of_tendsto_sub_div_pow hα (by omega)
    (tendsto_sub_div_pow_nhdsNE_of_iteratedDeriv_eq_zero hφ hα hzero)
  simpa using this

end Taylor

section Aitken

variable {φ : ℝ → ℝ} {α : ℝ}

/-!
### Aitken's $\Delta^2$ extrapolation

In this section $\varphi \colon \mathbb{R} \to \mathbb{R}$ and $\alpha \in \mathbb{R}$. Aitken's
iteration function is $\varphi_\Delta$ of (6.38) of [quarteroni2000numerical].
-/

/-- The **ratio of successive increments** of a real sequence $(x_k)$:
$$\lambda_k = \frac{x_{k+2} - x_{k+1}}{x_{k+1} - x_k},$$
with $\lambda_k = 0$ when $x_{k+1} = x_k$.

This is $\lambda^{(k+2)}$ of (6.33) of [quarteroni2000numerical], with the index shifted to
start at $k = 0$. It estimates the asymptotic convergence factor from the iterates alone and, in
§6.6.2 of the source, the multiplicity of a root. -/
noncomputable def aitkenRatio (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  (x (k + 2) - x (k + 1)) / (x (k + 1) - x k)

/-- Let $(x_k)$ be a real sequence with $x_k \neq \alpha$ for all $k$, and suppose that
$(x_{k+1} - \alpha)/(x_k - \alpha) \to l$ with $l \neq 1$. Then the increment ratios
`aitkenRatio x k` also tend to $l$.

This is (6.34) of [quarteroni2000numerical]. With $r_k = (x_{k+1} - \alpha)/(x_k - \alpha)$, the
increment ratio is $r_k (r_{k+1} - 1)/(r_k - 1)$. Together with
`tendsto_sub_div_sub_of_hasDerivAt`, it gives $\lambda_k \to \varphi'(\alpha)$ for a fixed-point
orbit. -/
theorem tendsto_aitkenRatio {x : ℕ → ℝ} {l : ℝ} (hne : ∀ k, x k ≠ α)
    (h : Tendsto (fun k => (x (k + 1) - α) / (x k - α)) atTop (𝓝 l)) (hl : l ≠ 1) :
    Tendsto (aitkenRatio x) atTop (𝓝 l) := by
  have h1 := (h.mul ((h.comp (tendsto_add_atTop_nat 1)).sub_const 1)).div (h.sub_const 1)
    (sub_ne_zero.2 hl)
  rw [mul_div_assoc, div_self (sub_ne_zero.2 hl), mul_one] at h1
  refine h1.congr fun k => ?_
  have e0 : x k - α ≠ 0 := sub_ne_zero.2 (hne k)
  have e1 : x (k + 1) - α ≠ 0 := sub_ne_zero.2 (hne (k + 1))
  simp only [Pi.div_apply, Function.comp]
  rw [aitkenRatio, ← div_div_div_cancel_right₀ e0 (x (k + 2) - x (k + 1)) (x (k + 1) - x k)]
  congr 1
  · field_simp
    ring
  · field_simp
    ring

/-- **Aitken's extrapolation formula**: from $x_k$, $x_{k+1}$, $x_{k+2}$ it produces
$$\hat x_{k+2} = x_{k+2} - \frac{(x_{k+2} - x_{k+1})^2}{(x_{k+2} - x_{k+1}) - (x_{k+1} -
  x_k)}.$$
When the denominator is zero, the value is $x_{k+2}$.

This is (6.36) of [quarteroni2000numerical]. The value at a zero denominator comes from the
convention $a/0 = 0$. -/
noncomputable def aitkenExtrapolation (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  x (k + 2) - (x (k + 2) - x (k + 1)) ^ 2 / ((x (k + 2) - x (k + 1)) - (x (k + 1) - x k))

/-- **The $\Delta^2$ form of Aitken's formula.** With the forward difference
$\Delta x_j = x_{j+1} - x_j$ and $\Delta^2 x_k = \Delta x_{k+1} - \Delta x_k$,
$$\hat x_{k+2} = x_{k+2} - \frac{(\Delta x_{k+1})^2}{\Delta^2 x_k}.$$

This is (6.37) of [quarteroni2000numerical]. The source writes the same identity with the
backward difference $\Delta x^{(k)} = x^{(k)} - x^{(k-1)}$. The forward difference is Mathlib's
`Δ_[1]`. -/
theorem aitkenExtrapolation_eq_sub_div_fwdDiff (x : ℕ → ℝ) (k : ℕ) :
    aitkenExtrapolation x k = x (k + 2) - (Δ_[1] x (k + 1)) ^ 2 / (Δ_[1]^[2] x k) := by
  simp only [aitkenExtrapolation, fwdDiff, Function.iterate_succ, Function.iterate_zero,
    Function.comp, id]

/-- **Aitken's iteration function**:
$$\varphi_\Delta(x) = \frac{x \varphi(\varphi(x)) - \varphi(x)^2}{\varphi(\varphi(x)) -
  2\varphi(x) + x},$$
with $\varphi_\Delta(x) = x$ where the denominator is zero.

This is (6.38) of [quarteroni2000numerical]. At a fixed point of $\varphi$ the formula is $0/0$,
and the extension by $x$ makes every fixed point of $\varphi$ a fixed point of $\varphi_\Delta$.
One step of the accelerated method is Aitken's formula applied to $x$, $\varphi(x)$ and
$\varphi(\varphi(x))$. -/
noncomputable def aitkenIterationFunction (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  if φ (φ x) - 2 * φ x + x = 0 then x
  else (x * φ (φ x) - φ x ^ 2) / (φ (φ x) - 2 * φ x + x)

/-- If $\varphi(\alpha) = \alpha$, then $\varphi_\Delta(\alpha) = \alpha$. -/
theorem aitkenIterationFunction_apply_self (hα : φ α = α) :
    aitkenIterationFunction φ α = α := by
  have : α - 2 * α + α = 0 := by ring
  simp [aitkenIterationFunction, hα, this]

/-- Let $x \in \mathbb{R}$ with $\varphi(\varphi(x)) - 2\varphi(x) + x \neq 0$. Then
$\varphi_\Delta(x) = x$ if and only if $\varphi(x) = x$.

The proof uses the identity $\varphi_\Delta(x) - x = -(\varphi(x) - x)^2 /
(\varphi(\varphi(x)) - 2\varphi(x) + x)$ (§6.6.1 of [quarteroni2000numerical]; pp. 104–106 of
[isaacson1994analysis]). -/
theorem aitkenIterationFunction_eq_self_iff {x : ℝ} (h : φ (φ x) - 2 * φ x + x ≠ 0) :
    aitkenIterationFunction φ x = x ↔ φ x = x := by
  simp only [aitkenIterationFunction, h, ↓reduceIte]
  rw [div_eq_iff h]
  constructor
  · intro hx
    have : (φ x - x) ^ 2 = 0 := by linarith
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  · intro hx
    rw [hx]
    ring

/-- Let $x \in \mathbb{R}$ with $\varphi(\varphi(x)) - 2\varphi(x) + x \neq 0$, and let
$\alpha \in \mathbb{R}$. Then
$$\varphi_\Delta(x) - \alpha = \frac{(x - \alpha)(\varphi(\varphi(x)) - \alpha) - (\varphi(x) -
  \alpha)^2}{\varphi(\varphi(x)) - 2\varphi(x) + x}.$$
-/
theorem aitkenIterationFunction_sub_eq {x : ℝ} (h : φ (φ x) - 2 * φ x + x ≠ 0) (α : ℝ) :
    aitkenIterationFunction φ x - α =
      ((x - α) * (φ (φ x) - α) - (φ x - α) ^ 2) / (φ (φ x) - 2 * φ x + x) := by
  simp only [aitkenIterationFunction, h, ↓reduceIte]
  rw [eq_div_iff h, sub_mul, div_mul_cancel₀ _ h]
  ring

/-- **The slope form of Aitken's error.** Let $\varphi(\alpha) = \alpha$, and let $s$ be the slope
function of $\varphi$ at $\alpha$: $s(y) = (\varphi(y) - \alpha)/(y - \alpha)$ for
$y \neq \alpha$, and $s(\alpha)$ the derivative of $\varphi$ at $\alpha$. Put
$Q(x) = s(x) s(\varphi(x)) - 2 s(x) + 1$. If $x \neq \alpha$ and $Q(x) \neq 0$, then
$\varphi(\varphi(x)) - 2\varphi(x) + x \neq 0$ and
$$\varphi_\Delta(x) - \alpha = \frac{(x - \alpha) s(x) \bigl(s(\varphi(x)) -
  s(x)\bigr)}{Q(x)}.$$

The slope function is `dslope φ α`. The denominator of $\varphi_\Delta$ is $(x - \alpha) Q(x)$.
Since $s(x), s(\varphi(x)) \to \varphi'(\alpha)$ and $Q(x) \to (\varphi'(\alpha) - 1)^2$, this
identity carries the whole local analysis of Aitken's method. -/
theorem aitkenIterationFunction_sub_eq_dslope (hα : φ α = α) {x : ℝ} (hx : x ≠ α)
    (hQ : dslope φ α x * dslope φ α (φ x) - 2 * dslope φ α x + 1 ≠ 0) :
    φ (φ x) - 2 * φ x + x ≠ 0 ∧
      aitkenIterationFunction φ x - α =
        (x - α) * dslope φ α x * (dslope φ α (φ x) - dslope φ α x) /
          (dslope φ α x * dslope φ α (φ x) - 2 * dslope φ α x + 1) := by
  have h1 : φ x - α = (x - α) * dslope φ α x := by
    have := sub_smul_dslope φ α x
    rw [hα, smul_eq_mul] at this
    exact this.symm
  have h2 : φ (φ x) - α = (φ x - α) * dslope φ α (φ x) := by
    have := sub_smul_dslope φ α (φ x)
    rw [hα, smul_eq_mul] at this
    exact this.symm
  have hD : φ (φ x) - 2 * φ x + x =
      (x - α) * (dslope φ α x * dslope φ α (φ x) - 2 * dslope φ α x + 1) := by
    rw [show φ (φ x) - 2 * φ x + x = (φ (φ x) - α) - 2 * (φ x - α) + (x - α) by ring, h2, h1]
    ring
  have hD' : φ (φ x) - 2 * φ x + x ≠ 0 := hD ▸ mul_ne_zero (sub_ne_zero.2 hx) hQ
  refine ⟨hD', ?_⟩
  rw [aitkenIterationFunction_sub_eq hD' α, hD, h2, h1]
  field_simp

/-- Let $\varphi$ have derivative $\varphi'$ at $\alpha$, with $\varphi(\alpha) = \alpha$, and let
$s$ be the slope function `dslope φ α`. Then, as $x \to \alpha$,
$$s(x) \to \varphi', \qquad s(\varphi(x)) \to \varphi', \qquad s(x) s(\varphi(x)) - 2 s(x) + 1
  \to (\varphi' - 1)^2.$$
-/
theorem tendsto_dslope_aitken {φ' : ℝ} (hφ : HasDerivAt φ φ' α) (hα : φ α = α) :
    Tendsto (dslope φ α) (𝓝 α) (𝓝 φ') ∧ Tendsto (fun x => dslope φ α (φ x)) (𝓝 α) (𝓝 φ') ∧
      Tendsto (fun x => dslope φ α x * dslope φ α (φ x) - 2 * dslope φ α x + 1) (𝓝 α)
        (𝓝 ((φ' - 1) ^ 2)) := by
  have hs₁ : Tendsto (dslope φ α) (𝓝 α) (𝓝 φ') := by
    have := (continuousAt_dslope_same.2 hφ.differentiableAt).tendsto
    rwa [dslope_same, hφ.deriv] at this
  have hφc : Tendsto φ (𝓝 α) (𝓝 α) := by simpa [hα] using hφ.continuousAt.tendsto
  have hs₂ : Tendsto (fun x => dslope φ α (φ x)) (𝓝 α) (𝓝 φ') := hs₁.comp hφc
  refine ⟨hs₁, hs₂, ?_⟩
  have := ((hs₁.mul hs₂).sub (hs₁.const_mul 2)).add_const 1
  convert this using 2
  ring

/-- Let $\varphi$ have derivative $\varphi' \neq 1$ at $\alpha$, with $\varphi(\alpha) = \alpha$.
Then $\varphi(\varphi(x)) - 2\varphi(x) + x \neq 0$ for all $x \neq \alpha$ in a neighbourhood
of $\alpha$, so the guard in `aitkenIterationFunction` is not used there. -/
theorem eventually_aitken_denom_ne_zero {φ' : ℝ} (hφ : HasDerivAt φ φ' α) (hα : φ α = α)
    (h1 : φ' ≠ 1) : ∀ᶠ x in 𝓝[≠] α, φ (φ x) - 2 * φ x + x ≠ 0 := by
  obtain ⟨-, -, hQ⟩ := tendsto_dslope_aitken hφ hα
  have hQne : (φ' - 1) ^ 2 ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 h1)
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (hQ.eventually (isOpen_ne.mem_nhds hQne))] with x hx hQx
  exact (aitkenIterationFunction_sub_eq_dslope hα hx hQx).1

/-- **Aitken's iteration function has derivative $0$ at the fixed point.** Let $\varphi$ have
derivative $\varphi' \neq 1$ at $\alpha$, with $\varphi(\alpha) = \alpha$. Then $\varphi_\Delta$
has derivative $0$ at $\alpha$.

So Aitken's iteration converges superlinearly under differentiability alone, and in particular
$\varphi_\Delta$ is continuous at $\alpha$; the source obtains this continuous extension at
$\alpha$ by L'Hôpital's rule (§6.6.1 of [quarteroni2000numerical]). By
`aitkenIterationFunction_sub_eq_dslope`, the slope of $\varphi_\Delta$ at $\alpha$ is
$s(x)(s(\varphi(x)) - s(x))/Q(x) \to \varphi'(\varphi' - \varphi')/(\varphi' - 1)^2 = 0$. -/
theorem hasDerivAt_aitkenIterationFunction_zero {φ' : ℝ} (hφ : HasDerivAt φ φ' α) (hα : φ α = α)
    (h1 : φ' ≠ 1) : HasDerivAt (aitkenIterationFunction φ) 0 α := by
  obtain ⟨hs₁, hs₂, hQ⟩ := tendsto_dslope_aitken hφ hα
  have hQne : (φ' - 1) ^ 2 ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 h1)
  rw [hasDerivAt_iff_tendsto_slope]
  have hlim : Tendsto (fun x => dslope φ α x * (dslope φ α (φ x) - dslope φ α x) /
      (dslope φ α x * dslope φ α (φ x) - 2 * dslope φ α x + 1)) (𝓝[≠] α)
      (𝓝 (φ' * (φ' - φ') / (φ' - 1) ^ 2)) :=
    ((hs₁.mul (hs₂.sub hs₁)).div hQ hQne).mono_left nhdsWithin_le_nhds
  rw [sub_self, mul_zero, zero_div] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (hQ.eventually (isOpen_ne.mem_nhds hQne))] with x hx hQx
  obtain ⟨-, hformula⟩ := aitkenIterationFunction_sub_eq_dslope hα hx hQx
  rw [slope_def_field, aitkenIterationFunction_apply_self hα, hformula]
  have he : x - α ≠ 0 := sub_ne_zero.2 hx
  field_simp

/-- **Property 6.7 for $p = 1$, the sharp constant.** Let $\varphi \colon \mathbb{R} \to \mathbb{R}$
be $C^2$ at $\alpha$, with $\varphi(\alpha) = \alpha$ and $\varphi'(\alpha) \neq 1$. Then
$$\frac{\varphi_\Delta(x) - \alpha}{(x - \alpha)^2} \to \frac{\varphi'(\alpha)
  \varphi''(\alpha)}{2(\varphi'(\alpha) - 1)} \qquad \text{as } x \to \alpha,\ x \neq \alpha.$$

Hence Aitken's method has order exactly $2$ when $\varphi'(\alpha) \varphi''(\alpha) \neq 0$,
and it converges locally even when $|\varphi'(\alpha)| > 1$; this is the remark of
[quarteroni2000numerical] that the method converges even if the fixed-point method does not. The
proof writes $s(\varphi(x)) - s(x) = (x - \alpha)(s(x) \, t(\varphi(x)) - t(x))$, where $t$ is
the slope function of $s$ at $\alpha$, which is continuous at $\alpha$ with value
$\varphi''(\alpha)/2$ by Hadamard's lemma. -/
theorem tendsto_aitkenIterationFunction_sub_div_sq (hφ : ContDiffAt ℝ 2 φ α) (hα : φ α = α)
    (h1 : deriv φ α ≠ 1) :
    Tendsto (fun x => (aitkenIterationFunction φ x - α) / (x - α) ^ 2) (𝓝[≠] α)
      (𝓝 (deriv φ α * iteratedDeriv 2 φ α / (2 * (deriv φ α - 1)))) := by
  have hφ' : ContDiffAt ℝ (1 + 1 : ℕ) φ α := by simpa using hφ
  have hφd : HasDerivAt φ (deriv φ α) α := (hφ.differentiableAt (by norm_num)).hasDerivAt
  obtain ⟨hs₁, hs₂, hQ⟩ := tendsto_dslope_aitken hφd hα
  have hQne : (deriv φ α - 1) ^ 2 ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 h1)
  -- `t = dslope (dslope φ α) α` is continuous at `α` with value `φ''(α) / 2`
  have hs₁d : HasDerivAt (dslope φ α) (iteratedDeriv 2 φ α / 2) α := by
    have := ((ContDiffAt.dslope_same (n := 1) hφ').differentiableAt (by simp)).hasDerivAt
    rwa [← iteratedDeriv_one, iteratedDeriv_dslope_same hφ', show ((1 : ℕ) : ℝ) + 1 = 2 by norm_num]
      at this
  have ht : Tendsto (dslope (dslope φ α) α) (𝓝 α) (𝓝 (iteratedDeriv 2 φ α / 2)) := by
    have := (continuousAt_dslope_same.2 hs₁d.differentiableAt).tendsto
    rwa [dslope_same, hs₁d.deriv] at this
  have hφc : Tendsto φ (𝓝 α) (𝓝 α) := by simpa [hα] using hφd.continuousAt.tendsto
  have htφ : Tendsto (fun x => dslope (dslope φ α) α (φ x)) (𝓝 α) (𝓝 (iteratedDeriv 2 φ α / 2)) :=
    ht.comp hφc
  have hlim : Tendsto (fun x => dslope φ α x *
      (dslope φ α x * dslope (dslope φ α) α (φ x) - dslope (dslope φ α) α x) /
      (dslope φ α x * dslope φ α (φ x) - 2 * dslope φ α x + 1)) (𝓝[≠] α)
      (𝓝 (deriv φ α * (deriv φ α * (iteratedDeriv 2 φ α / 2) - iteratedDeriv 2 φ α / 2) /
        (deriv φ α - 1) ^ 2)) :=
    ((hs₁.mul ((hs₁.mul htφ).sub ht)).div hQ hQne).mono_left nhdsWithin_le_nhds
  rw [show deriv φ α * (deriv φ α * (iteratedDeriv 2 φ α / 2) - iteratedDeriv 2 φ α / 2) /
      (deriv φ α - 1) ^ 2 = deriv φ α * iteratedDeriv 2 φ α / (2 * (deriv φ α - 1)) by
    field_simp] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (hQ.eventually (isOpen_ne.mem_nhds hQne))] with x hx hQx
  obtain ⟨-, hformula⟩ := aitkenIterationFunction_sub_eq_dslope hα hx hQx
  have he : x - α ≠ 0 := sub_ne_zero.2 hx
  -- `s₂ x - s₁ x = (φ x - α) t (φ x) - (x - α) t x`, and `φ x - α = (x - α) s₁ x`
  have hu : φ x - α = (x - α) * dslope φ α x := by
    have := sub_smul_dslope φ α x
    rw [hα, smul_eq_mul] at this
    exact this.symm
  have hdiff : dslope φ α (φ x) - dslope φ α x =
      (x - α) * (dslope φ α x * dslope (dslope φ α) α (φ x) - dslope (dslope φ α) α x) := by
    have e1 := sub_smul_dslope (dslope φ α) α (φ x)
    have e2 := sub_smul_dslope (dslope φ α) α x
    rw [smul_eq_mul] at e1 e2
    rw [show dslope φ α (φ x) - dslope φ α x =
      (dslope φ α (φ x) - dslope φ α α) - (dslope φ α x - dslope φ α α) by ring, ← e1, ← e2, hu]
    ring
  rw [hformula, hdiff]
  field_simp

/-- **Property 6.7 for $p = 1$, the order.** Let $\varphi \colon \mathbb{R} \to \mathbb{R}$ be $C^2$
at $\alpha$, with $\varphi(\alpha) = \alpha$ and $\varphi'(\alpha) \neq 1$. Then the iteration
$x \mapsto \varphi_\Delta(x)$ has order $2$ at $\alpha$.

This is Property 6.7 of [quarteroni2000numerical] for a method $x \mapsto \varphi(x)$ of order
$1$. -/
theorem hasIterationOrder_aitkenIterationFunction_two (hφ : ContDiffAt ℝ 2 φ α) (hα : φ α = α)
    (h1 : deriv φ α ≠ 1) : HasIterationOrder (aitkenIterationFunction φ) α 2 := by
  have := hasIterationOrder_of_tendsto_sub_div_pow (aitkenIterationFunction_apply_self hα) le_rfl
    (tendsto_aitkenIterationFunction_sub_div_sq hφ hα h1)
  simpa using this

/-- **Property 6.7 for $p \ge 2$, the limit.** Let $p \ge 2$, let
$\varphi \colon \mathbb{R} \to \mathbb{R}$ be $C^p$ at $\alpha$ with $\varphi(\alpha) = \alpha$,
let $\varphi^{(i)}(\alpha) = 0$ for $1 \le i < p$, and let $\varphi^{(p)}(\alpha) \neq 0$. Then
$$\frac{\varphi_\Delta(x) - \alpha}{(x - \alpha)^{2p-1}} \to
  -\Bigl(\frac{\varphi^{(p)}(\alpha)}{p!}\Bigr)^2 \qquad \text{as } x \to \alpha,\ x \neq
  \alpha.$$

The hypotheses say that $x \mapsto \varphi(x)$ has order $p$ in the sense of Property 6.4 of
[quarteroni2000numerical]. With $e = x - \alpha$, write $\varphi(x) - \alpha = e^p h(x)$ with
$h$ continuous and $h(\alpha) = c$. Then $\varphi(\varphi(x)) - \alpha = O(e^{p^2})$, so the
numerator of Aitken's error is $-c^2 e^{2p} + o(e^{2p})$ and the denominator is $e(1 + o(1))$. -/
theorem tendsto_aitkenIterationFunction_sub_div_pow_of_iteratedDeriv_eq_zero {p : ℕ}
    (hp : 2 ≤ p) (hφ : ContDiffAt ℝ p φ α) (hα : φ α = α)
    (hzero : ∀ i, 1 ≤ i → i < p → iteratedDeriv i φ α = 0) (hp' : iteratedDeriv p φ α ≠ 0) :
    Tendsto (fun x => (aitkenIterationFunction φ x - α) / (x - α) ^ (2 * p - 1)) (𝓝[≠] α)
      (𝓝 (-(iteratedDeriv p φ α / p.factorial) ^ 2)) := by
  -- the factorization `φ x - α = (x - α) ^ p * h x`
  have hiter : ∀ i, 1 ≤ i → iteratedDeriv i (fun x => φ x - α) α = iteratedDeriv i φ α := by
    intro i hi
    rw [show (fun x => φ x - α) = fun x => -α + φ x from funext fun x => by ring,
      iteratedDeriv_const_add (by omega)]
  have hroot : IsRootOfMultiplicity (fun x => φ x - α) α p := by
    refine ⟨fun i hi => ?_, by rwa [hiter p (by omega)]⟩
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp [hα]
    · rw [hiter i hi0]
      exact hzero i hi0 hi
  obtain ⟨h, hh, hhα, hfh⟩ := hroot.exists_eq_pow_mul (n := 0)
    (by simpa using hφ.sub contDiffAt_const)
  rw [hiter p (by omega)] at hhα
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hq : 1 ≤ q := by omega
  have hc : Tendsto h (𝓝 α) (𝓝 (h α)) := hh.continuousAt.tendsto
  have hφc : Tendsto φ (𝓝 α) (𝓝 α) := by simpa [hα] using hφ.continuousAt.tendsto
  have hcφ : Tendsto (fun x => h (φ x)) (𝓝 α) (𝓝 (h α)) := hc.comp hφc
  have hpow : ∀ n, 1 ≤ n → Tendsto (fun x : ℝ => (x - α) ^ n) (𝓝 α) (𝓝 0) := by
    intro n hn
    have := ((continuous_id.sub (continuous_const (y := α))).tendsto α).pow n
    simpa [zero_pow (by omega : n ≠ 0)] using this
  -- `R x = 1 - 2 e^q h x + e^{q² + 2q} h x ^ (q+1) h (φ x) → 1`
  have hR : Tendsto (fun x => 1 - 2 * (x - α) ^ q * h x +
      (x - α) ^ (q * q + 2 * q) * h x ^ (q + 1) * h (φ x)) (𝓝 α) (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub (((hpow q hq).const_mul 2).mul hc)).add
      (((hpow (q * q + 2 * q) (by nlinarith)).mul (hc.pow (q + 1))).mul hcφ)
    simpa using this
  -- `M x = e^{q²} h x ^ (q+1) h (φ x) - h x ^ 2 → -(h α)²`
  have hM : Tendsto (fun x => (x - α) ^ (q * q) * h x ^ (q + 1) * h (φ x) - h x ^ 2) (𝓝 α)
      (𝓝 (-(h α) ^ 2)) := by
    have := (((hpow (q * q) (by nlinarith)).mul (hc.pow (q + 1))).mul hcφ).sub (hc.pow 2)
    simpa using this
  have hlim := ((hM.div hR one_ne_zero).mono_left (nhdsWithin_le_nhds (s := {α}ᶜ)))
  rw [div_one, hhα] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (hR.eventually (isOpen_ne.mem_nhds one_ne_zero))] with x hx hRx
  have he : x - α ≠ 0 := sub_ne_zero.2 hx
  have hu : φ x - α = (x - α) ^ (q + 1) * h x := hfh x
  have hv : φ (φ x) - α = (φ x - α) ^ (q + 1) * h (φ x) := hfh (φ x)
  have hD : φ (φ x) - 2 * φ x + x = (x - α) * (1 - 2 * (x - α) ^ q * h x +
      (x - α) ^ (q * q + 2 * q) * h x ^ (q + 1) * h (φ x)) := by
    rw [show φ (φ x) - 2 * φ x + x = (φ (φ x) - α) - 2 * (φ x - α) + (x - α) by ring, hv, hu]
    generalize x - α = e
    ring
  have hD' : φ (φ x) - 2 * φ x + x ≠ 0 := hD ▸ mul_ne_zero he hRx
  simp only [Pi.div_apply]
  rw [aitkenIterationFunction_sub_eq hD' α, hD, hv, hu, show 2 * (q + 1) - 1 = 2 * q + 1 by omega]
  generalize x - α = e at he hRx ⊢
  field_simp
  ring

/-- **Property 6.7 for $p \ge 2$, the order.** Let $p \ge 2$, let
$\varphi \colon \mathbb{R} \to \mathbb{R}$ be $C^p$ at $\alpha$ with $\varphi(\alpha) = \alpha$,
let $\varphi^{(i)}(\alpha) = 0$ for $1 \le i < p$, and let $\varphi^{(p)}(\alpha) \neq 0$. Then
the iteration $x \mapsto \varphi_\Delta(x)$ has order $2p - 1$ at $\alpha$.

This is Property 6.7 of [quarteroni2000numerical], which the source states without proof (pp.
104–108 of [isaacson1994analysis]). -/
theorem hasIterationOrder_aitkenIterationFunction_of_iteratedDeriv_eq_zero {p : ℕ} (hp : 2 ≤ p)
    (hφ : ContDiffAt ℝ p φ α) (hα : φ α = α)
    (hzero : ∀ i, 1 ≤ i → i < p → iteratedDeriv i φ α = 0) (hp' : iteratedDeriv p φ α ≠ 0) :
    HasIterationOrder (aitkenIterationFunction φ) α (2 * p - 1) := by
  have := hasIterationOrder_of_tendsto_sub_div_pow (aitkenIterationFunction_apply_self hα)
    (by omega) (tendsto_aitkenIterationFunction_sub_div_pow_of_iteratedDeriv_eq_zero hp hφ hα
      hzero hp')
  rwa [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at this

end Aitken

section Steffensen

variable {f : ℝ → ℝ} {α : ℝ}

/-!
### Steffensen's method

In this section $f \colon \mathbb{R} \to \mathbb{R}$ and $\alpha \in \mathbb{R}$.
-/

/-- **Steffensen's step** for $f$:
$$x \mapsto x - \frac{f(x)}{\bigl(f(x + f(x)) - f(x)\bigr) / f(x)},$$
which is Newton's step with $f'(x)$ replaced by the difference quotient over the step $f(x)$.
Where $f(x) = 0$ or $f(x + f(x)) = f(x)$, the value is $x$.

This is Exercise 6.5 of [quarteroni2000numerical]. The value at a zero denominator comes from
the convention $a/0 = 0$. -/
noncomputable def steffensenStep (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  x - f x / ((f (x + f x) - f x) / f x)

/-- If $f(\alpha) = 0$, then $\alpha$ is a fixed point of Steffensen's step. -/
theorem steffensenStep_apply_self (hα : f α = 0) : steffensenStep f α = α := by
  simp [steffensenStep, hα]

/-- **Steffensen's method is Aitken's method for $x \mapsto x + f(x)$.** For every $x$ with
$f(x + f(x)) - f(x) \neq 0$, Steffensen's step at $x$ equals $\varphi_\Delta(x)$ for
$\varphi(y) = y + f(y)$.

The denominators agree, $\varphi(\varphi(x)) - 2\varphi(x) + x = f(x + f(x)) - f(x)$, and so do
the numerators after the factor $f(x)$ is cleared. -/
theorem steffensenStep_eq_aitkenIterationFunction (f : ℝ → ℝ) (x : ℝ)
    (h : f (x + f x) - f x ≠ 0) :
    steffensenStep f x = aitkenIterationFunction (fun y => y + f y) x := by
  have hden : x + f x + f (x + f x) - 2 * (x + f x) + x ≠ 0 := by
    convert h using 1
    ring
  simp only [steffensenStep, aitkenIterationFunction, hden, ↓reduceIte]
  rw [div_div_eq_mul_div, show x + f x + f (x + f x) - 2 * (x + f x) + x = f (x + f x) - f x by
    ring, eq_div_iff h, sub_mul, div_mul_cancel₀ _ h]
  ring

/-- **Steffensen's method has order $2$ at a simple root.** Let $f(\alpha) = 0$, let $f$ be $C^2$ at
$\alpha$, and let $f'(\alpha) \neq 0$. Then the iteration of Steffensen's step has order $2$ at
$\alpha$.

This is Exercise 6.5 of [quarteroni2000numerical]. With $\varphi(y) = y + f(y)$, one has
$\varphi'(\alpha) = 1 + f'(\alpha) \neq 1$, so `hasIterationOrder_aitkenIterationFunction_two`
applies through `steffensenStep_eq_aitkenIterationFunction`. The asymptotic constant is
$(1 + f'(\alpha)) f''(\alpha) / (2 f'(\alpha))$. -/
theorem hasIterationOrder_steffensenStep_two (hα : f α = 0) (hf : ContDiffAt ℝ 2 f α)
    (hf' : deriv f α ≠ 0) : HasIterationOrder (steffensenStep f) α 2 := by
  set φ : ℝ → ℝ := fun y => y + f y with hφdef
  have hφα : φ α = α := by simp [hφdef, hα]
  have hφ : ContDiffAt ℝ 2 φ α := contDiffAt_id.add hf
  have hfd : HasDerivAt f (deriv f α) α := (hf.differentiableAt (by norm_num)).hasDerivAt
  have hφd : HasDerivAt φ (1 + deriv f α) α := (hasDerivAt_id α).add hfd
  have hφ1 : deriv φ α ≠ 1 := by
    rw [hφd.deriv]
    intro h
    exact hf' (by linarith)
  have hlim := tendsto_aitkenIterationFunction_sub_div_sq hφ hφα hφ1
  have heq : ∀ᶠ x in 𝓝[≠] α, (steffensenStep f x - α) / (x - α) ^ 2 =
      (aitkenIterationFunction φ x - α) / (x - α) ^ 2 := by
    filter_upwards [eventually_aitken_denom_ne_zero hφd hφα (by rwa [hφd.deriv] at hφ1)]
      with x hx
    rw [steffensenStep_eq_aitkenIterationFunction f x (by convert hx using 1; simp [hφdef]; ring)]
  have := hasIterationOrder_of_tendsto_sub_div_pow (steffensenStep_apply_self hα) le_rfl
    (hlim.congr' (heq.mono fun x hx => hx.symm))
  simpa using this

end Steffensen

section SteffensenMultiple

variable {f : ℝ → ℝ} {α : ℝ}

/-! ### Steffensen's method at a multiple root -/

/-- As $w \to 0$ with $w \neq 0$, $((1 + w)^n - 1)/w \to n$. -/
private theorem tendsto_one_add_pow_sub_one_div (n : ℕ) :
    Tendsto (fun w : ℝ => ((1 + w) ^ n - 1) / w) (𝓝[≠] 0) (𝓝 n) := by
  have hd : HasDerivAt (fun w : ℝ => (1 + w) ^ n) ((n : ℝ) * (1 + 0) ^ (n - 1) * 1) 0 :=
    (hasDerivAt_pow n (1 + 0)).comp 0 ((hasDerivAt_id 0).const_add 1)
  have := hasDerivAt_iff_tendsto_slope.1 hd
  simp only [add_zero, one_pow, mul_one] at this
  refine this.congr fun w => ?_
  simp [slope_def_field]

/-- **Steffensen's method at a multiple root.** Let $m \ge 2$, let
$f \colon \mathbb{R} \to \mathbb{R}$ be $C^{m+1}$ at $\alpha$, and let $\alpha$ be a root of $f$
of multiplicity $m$, that is, $f^{(i)}(\alpha) = 0$ for $i < m$ and $f^{(m)}(\alpha) \neq 0$.
Then Steffensen's iteration converges only linearly, with factor $1 - 1/m$:
$$\frac{\operatorname{St}(x) - \alpha}{x - \alpha} \to 1 - \frac{1}{m} \qquad \text{as } x \to
  \alpha,\ x \neq \alpha,$$
where $\operatorname{St}$ is Steffensen's step `steffensenStep f`.

This is the correct reading of the last clause of Property 6.7 of [quarteroni2000numerical],
which says that Aitken's method converges linearly with factor $1 - 1/m$ at a multiple root. As
printed, the clause cannot hold: for every $\varphi$ with $\varphi'(\alpha) \neq 1$, Aitken's
method is superlinear by `hasDerivAt_aitkenIterationFunction_zero`. The statement proved here is
that of [isaacson1994analysis], which the source paraphrases. The degenerate behaviour occurs
because $\varphi = \mathrm{id} + f$ has $\varphi'(\alpha) = 1$ at a multiple root.

With $e = x - \alpha$, write $f(x) = e^m h(x)$, where $h$ is $C^1$, hence Lipschitz near
$\alpha$, with $h(\alpha) = c \neq 0$, and put $w = e^{m-1} h(x)$. Then
$x + f(x) - \alpha = e(1 + w)$, so $f(x + f(x)) - f(x) = e^m [((1 + w)^m - 1) h(x + f(x)) +
(h(x + f(x)) - h(x))]$, where the bracket is $e^{m-1}(m c^2 + o(1))$. Hence
$(\operatorname{St}(x) - \alpha)/e = 1 - h(x)^2 / (m c^2 + o(1)) \to 1 - 1/m$. -/
theorem tendsto_steffensenStep_sub_div_of_isRootOfMultiplicity {m : ℕ} (hm : 2 ≤ m)
    (hf : ContDiffAt ℝ (m + 1 : ℕ) f α) (hα : IsRootOfMultiplicity f α m) :
    Tendsto (fun x => (steffensenStep f x - α) / (x - α)) (𝓝[≠] α) (𝓝 (1 - 1 / m)) := by
  obtain ⟨h, hh, hhα, hfh⟩ := hα.exists_eq_pow_mul (n := 1) hf
  have hc0 : h α ≠ 0 := hhα ▸ hα.iteratedDeriv_div_factorial_ne_zero
  obtain ⟨K, t, ht, hK⟩ := hh.exists_lipschitzOnWith
  obtain ⟨q, rfl⟩ : ∃ q, m = q + 1 := ⟨m - 1, by omega⟩
  have hq : 1 ≤ q := by omega
  have hfα : f α = 0 := hα.eq_zero (by omega)
  have hc : Tendsto h (𝓝 α) (𝓝 (h α)) := hh.continuousAt.tendsto
  have hfc : Tendsto f (𝓝 α) (𝓝 0) := by simpa [hfα] using hf.continuousAt.tendsto
  have hy : Tendsto (fun x => x + f x) (𝓝 α) (𝓝 α) := by
    simpa using (continuous_id.tendsto α).add hfc
  have hcy : Tendsto (fun x => h (x + f x)) (𝓝 α) (𝓝 (h α)) := hc.comp hy
  have hpow : Tendsto (fun x : ℝ => (x - α) ^ q) (𝓝 α) (𝓝 0) := by
    have := ((continuous_id.sub (continuous_const (y := α))).tendsto α).pow q
    simpa [zero_pow (by omega : q ≠ 0)] using this
  -- `w x = (x - α) ^ q * h x → 0`, and `w x ≠ 0` away from `α`
  have hw : Tendsto (fun x => (x - α) ^ q * h x) (𝓝 α) (𝓝 0) := by simpa using hpow.mul hc
  have hh_ne : ∀ᶠ x in 𝓝 α, h x ≠ 0 := hc.eventually (isOpen_ne.mem_nhds hc0)
  have hw_ne : ∀ᶠ x in 𝓝[≠] α, (x - α) ^ q * h x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hh_ne] with x hx hhx
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.2 hx)) hhx
  -- the first part of the bracket, divided by `e ^ q`: `→ (q + 1) c²`
  have h1 : Tendsto (fun x => ((1 + (x - α) ^ q * h x) ^ (q + 1) - 1) / ((x - α) ^ q * h x) *
      h x * h (x + f x)) (𝓝[≠] α) (𝓝 (((q + 1 : ℕ) : ℝ) * h α * h α)) :=
    (((tendsto_one_add_pow_sub_one_div (q + 1)).comp
      (tendsto_nhdsWithin_iff.2 ⟨hw.mono_left nhdsWithin_le_nhds, hw_ne⟩)).mul
      (hc.mono_left nhdsWithin_le_nhds)).mul (hcy.mono_left nhdsWithin_le_nhds)
  -- the second part, divided by `e ^ q`: `→ 0` by the Lipschitz bound
  have h2 : Tendsto (fun x => (h (x + f x) - h x) / (x - α) ^ q) (𝓝[≠] α) (𝓝 0) := by
    have hbound : ∀ᶠ x in 𝓝[≠] α,
        ‖(h (x + f x) - h x) / (x - α) ^ q‖ ≤ (K : ℝ) * |x - α| * |h x| := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds ht, nhdsWithin_le_nhds (hy ht)]
        with x hx hxt hyt
      have hK' := hK.dist_le_mul (x + f x) hyt x hxt
      rw [Real.dist_eq, Real.dist_eq, add_sub_cancel_left] at hK'
      rw [Real.norm_eq_abs, abs_div, abs_pow,
        div_le_iff₀ (pow_pos (abs_pos.2 (sub_ne_zero.2 hx)) q)]
      calc |h (x + f x) - h x| ≤ K * |f x| := hK'
        _ = K * (|x - α| ^ (q + 1) * |h x|) := by rw [hfh x, abs_mul, abs_pow]
        _ = K * |x - α| * |h x| * |x - α| ^ q := by ring
    refine squeeze_zero_norm' hbound ?_
    have := ((tendsto_const_nhds (x := (K : ℝ))).mul
      ((continuous_id.sub (continuous_const (y := α))).abs.tendsto α)).mul hc.abs
    simpa using this.mono_left nhdsWithin_le_nhds
  have hB := h1.add h2
  rw [add_zero] at hB
  have hBne : ((q + 1 : ℕ) : ℝ) * h α * h α ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by positivity) hc0) hc0
  have hlim := (tendsto_const_nhds (x := (1 : ℝ))).sub
    (((hc.mono_left nhdsWithin_le_nhds).pow 2).div hB hBne)
  rw [show (1 : ℝ) - h α ^ 2 / (((q + 1 : ℕ) : ℝ) * h α * h α) = 1 - 1 / ((q + 1 : ℕ) : ℝ) by
    field_simp] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hh_ne] with x hx hhx
  have he : x - α ≠ 0 := sub_ne_zero.2 hx
  -- the identity `f (x + f x) - f x = e ^ (q + 1) * (e ^ q * B x)`
  have hyα : x + f x - α = (x - α) * (1 + (x - α) ^ q * h x) := by rw [hfh x]; ring
  have hD : f (x + f x) - f x = (x - α) ^ (q + 1) * ((x - α) ^ q *
      (((1 + (x - α) ^ q * h x) ^ (q + 1) - 1) / ((x - α) ^ q * h x) * h x * h (x + f x) +
        (h (x + f x) - h x) / (x - α) ^ q)) := by
    rw [hfh (x + f x), hyα, hfh x, mul_pow]
    generalize x - α = e at he ⊢
    field_simp
    ring
  have hS : (steffensenStep f x - α) / (x - α) =
      1 - f x * f x / (f (x + f x) - f x) / (x - α) := by
    rw [steffensenStep, div_div_eq_mul_div, sub_right_comm, sub_div, div_self he]
  simp only [Pi.div_apply]
  rw [hS, hD, hfh x]
  congr 1
  generalize x - α = e at he ⊢
  rw [div_div, ← mul_div_mul_left (h x ^ 2) _ (pow_ne_zero (2 * q + 2) he)]
  congr 1 <;> ring

end SteffensenMultiple

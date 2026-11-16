/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Complexity.Basic
import Numlib.Optimization.Complexity.SlowExample.Basic
import Numlib.Optimization.Complexity.SlowExample.Ridge
import Numlib.Optimization.Complexity.SlowExample.ZigZag
import Numlib.Optimization.LineSearch.Backtracking
import NumlibSurface.CartisGouldToint.Chapter02.Section01

/-!
# Cartis, Gould and Toint, Section 2.2: Linesearch algorithms

This module formalizes §2.2 of [cartis2022evaluation]: steepest descent
$x_{k+1} = x_k - t_k \nabla f(x_k)$ on $\mathbb{R}^n$ with a backtracking-Armijo linesearch (SDBA,
Algorithm 2.2.1) and with an exact linesearch (SDEX). Under f.Bb and f.gL both methods find a point
with $\|\nabla f(x_k)\| \le \varepsilon$ within $O(\varepsilon^{-2})$ iterations (Theorems 2.2.2 and
2.2.4), and examples show that $\varepsilon^{-2}$ iterations can be needed (Theorems 2.2.3 and
2.2.5). The SDBA step is $t_k = 2^{-i_k} t_{\mathrm{ini}}$, where $i_k$ is the least $i$ for which
the Armijo condition (2.2.1)
$$f(x_k - t \nabla f(x_k)) \le f(x_k) - \alpha t \|\nabla f(x_k)\|^2$$
holds at $t = 2^{-i} t_{\mathrm{ini}}$. The SDEX step $t_k$ is the first global minimizer of
$t \mapsto f(x_k - t \nabla f(x_k))$ on $t \ge 0$ (2.2.26). The proofs use the backbone modules
`Numlib.Optimization.LineSearch.Backtracking`, `Numlib.Optimization.Complexity.Basic` and the slow
examples of `Numlib.Optimization.Complexity.SlowExample.Ridge` and
`Numlib.Optimization.Complexity.SlowExample.ZigZag`.

## Main definitions

* Algorithm 2.2.1, `CartisGouldToint.Chapter02.algorithm_2_2_1`: SDBA as a run predicate, with
  iterates $x_k$ and backtracking indices $i_k$.
* Theorem 2.2.2, `CartisGouldToint.Chapter02.sdbaFunEvalCount`: the number
  $1 + \sum_{j<k} (i_j + 1)$ of objective evaluations of SDBA before iteration $k$.
* Theorem 2.2.2, `CartisGouldToint.Chapter02.kappaSDBA`: the constant $\kappa = 1/(\alpha
  \min(t_{\mathrm{ini}}, (1-\alpha)/L))$, which is the book's
  $\kappa_{\mathrm{SDBA}} = L/(\alpha(1-\alpha))$ when $t_{\mathrm{ini}} \ge (1-\alpha)/L$.
* Section 2.2.3.4, `CartisGouldToint.Chapter02.IsSDEXRun`: SDEX, steepest descent with the exact
  linesearch (2.2.26), as a run predicate.

## Main results

* Lemma 2.2.1, `CartisGouldToint.Chapter02.lemma_2_2_1`: the Armijo condition holds for every
  $t \in [0, 2(1-\alpha)/L]$.
* Lemma 2.2.1, `CartisGouldToint.Chapter02.lemma_2_2_1_index`: the consequences (2.2.6)–(2.2.7) for
  the backtracking index and the accepted step.
* Algorithm 2.2.1, `CartisGouldToint.Chapter02.exists_algorithm_2_2_1`: under f.gL an SDBA run
  exists from every starting point.
* Theorem 2.2.2, `CartisGouldToint.Chapter02.theorem_2_2_2`: the bounds on the iterations and the
  evaluations of SDBA, with a corrected bound on the objective evaluations.
* Theorem 2.2.3, `CartisGouldToint.Chapter02.theorem_2_2_3`: SDBA may need $\varepsilon^{-2}$
  iterations and $\varepsilon^{-2} + 1$ evaluations.
* Section 2.2.3.4, `CartisGouldToint.Chapter02.IsSDEXRun.exists`: an SDEX run exists when the
  initial sublevel set is bounded.
* Theorem 2.2.4, `CartisGouldToint.Chapter02.theorem_2_2_4`: SDEX needs at most
  $2L(f(x_0) - f_{\mathrm{low}})/\varepsilon^2$ iterations.
* Theorem 2.2.5, `CartisGouldToint.Chapter02.theorem_2_2_5`: SDEX may need $\varepsilon^{-2}$
  iterations.

## Conventions

* $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)`.
* An algorithm is a run predicate on the sequence of iterates: a run is any sequence that obeys the
  rules of the algorithm at every iteration before the termination test
  $\|\nabla f(x_k)\| \le \varepsilon$ of Step 1 first holds (`Optimization.UntilHit`). The
  termination index is the first $k$ at which the test holds (`Optimization.IsFirstHit`).

## Deviations from the source

* **Lemma 2.2.1, (2.2.7)** (correction). The bound $t_k \ge t_{\mathrm{low}}/2$ holds only when
  $t_{\mathrm{ini}} \ge t_{\mathrm{low}}/2$; in general $t_k \ge \min(t_{\mathrm{ini}},
  t_{\mathrm{low}}/2)$. See `CartisGouldToint.Chapter02.lemma_2_2_1_index`.
* **Theorem 2.2.2** (correction). Because of the corrected (2.2.7), the constant is $\kappa =
  1/(\alpha \min(t_{\mathrm{ini}}, (1-\alpha)/L))$. The printed bound (2.2.8) on the objective
  evaluations is false, and the corrected bound is $1 + (\lceil \log_2(L
  t_{\mathrm{ini}}/(2(1-\alpha))) \rceil + 1) \kappa (f(x_0) - f_{\mathrm{low}})/\varepsilon^2$. See
  `CartisGouldToint.Chapter02.theorem_2_2_2`.
* **Theorem 2.2.3** (generalization). The hypothesis $t_{\mathrm{ini}} \ge \alpha$ of the proof is
  not needed. See `CartisGouldToint.Chapter02.theorem_2_2_3`.
* **Theorems 2.2.3 and 2.2.5** (reading). The number $\varepsilon^{-2}$ is assumed to be an integer,
  as the proof does in (2.2.14). See `CartisGouldToint.Chapter02.theorem_2_2_3` and
  `CartisGouldToint.Chapter02.theorem_2_2_5`.

## Not formalized

* **The variants of §§2.2.3.1–2.2.3.3 and §2.2.3.5**: the flexible Armijo condition, the
  Goldstein–Armijo conditions, Nesterov's view and nonmonotone methods. These sections contain no
  numbered results.
-/

open Set Finset Optimization LineSearch
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter02

variable {n : ℕ}

/-! ### Lemma 2.2.1 -/

section Lemma221

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {L α tini : ℝ}

/-- **Lemma 2.2.1** of [cartis2022evaluation], (2.2.3)–(2.2.4). Let
$f : \mathbb{R}^n \to \mathbb{R}$ satisfy f.gL with constant $L = L_{f,1}$, let
$\alpha \in \mathbb{R}$, and let $x \in \mathbb{R}^n$. Then the Armijo condition
$$f(x - t \nabla f(x)) \le f(x) - \alpha t \|\nabla f(x)\|^2$$
holds for every $t \in [0, t_{\mathrm{low}}]$, where $t_{\mathrm{low}} = 2(1-\alpha)/L$.

No condition on $\alpha$ is needed; for $\alpha \ge 1$ the interval is $\{0\}$ or empty. -/
theorem lemma_2_2_1 (hf : AssumptionGL f L) (x : EuclideanSpace ℝ (Fin n)) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ 2 * (1 - α) / L) :
    f (x - t • gradient f x) ≤ f x - α * t * ‖gradient f x‖ ^ 2 :=
  armijo_neg_gradient_of_le hf.differentiable hf.lipschitz hf.pos x ht0 ht

/-- **Lemma 2.2.1** of [cartis2022evaluation], consequences (2.2.6)–(2.2.7). Let $f$ satisfy f.gL
with constant $L$, let $\alpha < 1$ and $t_{\mathrm{ini}} > 0$, and let $x \in \mathbb{R}^n$.
Let $i$ be the backtracking index, the least $i$ such that the step $2^{-i} t_{\mathrm{ini}}$
satisfies the Armijo condition (2.2.1). Then
$$i \le \Bigl\lceil \log_2 \frac{L t_{\mathrm{ini}}}{2(1-\alpha)} \Bigr\rceil \quad \text{and}
  \quad 2^{-i} t_{\mathrm{ini}} \ge \min\Bigl(t_{\mathrm{ini}}, \frac{1-\alpha}{L}\Bigr).$$

**Correction.** The book's (2.2.7) is $t_k \ge t_{\mathrm{low}}/2 = (1-\alpha)/L$. This holds
only when $t_{\mathrm{ini}} \ge t_{\mathrm{low}}/2$: if $t_{\mathrm{ini}} < t_{\mathrm{low}}/2$,
the first trial step is accepted and $t_k = t_{\mathrm{ini}}$.

The backtracking index is `LineSearch.backtrackingIndex f α tini x`. The ceiling is the
natural-number ceiling `⌈·⌉₊`, which is $0$ for a nonpositive argument. -/
theorem lemma_2_2_1_index (hf : AssumptionGL f L) (hα : α < 1) (htini : 0 < tini)
    (x : EuclideanSpace ℝ (Fin n)) :
    backtrackingIndex f α tini x ≤ ⌈Real.logb 2 (L * tini / (2 * (1 - α)))⌉₊ ∧
      min tini ((1 - α) / L) ≤ tini * 2⁻¹ ^ backtrackingIndex f α tini x :=
  backtrackingIndex_le hf.differentiable hf.lipschitz hf.pos hα htini x

/-- Let $f$ satisfy f.gL, let $\alpha < 1$ and $t_{\mathrm{ini}} > 0$. Then for every $x$ some trial
step $2^{-i} t_{\mathrm{ini}}$ of the backtracking linesearch satisfies the Armijo condition
(2.2.1). -/
theorem exists_backtrackingTest (hf : AssumptionGL f L) (hα : α < 1) (htini : 0 < tini)
    (x : EuclideanSpace ℝ (Fin n)) : ∃ i, BacktrackingTest f α tini x i := by
  have hpos : 0 < 2 * (1 - α) / L / tini := by
    have := hf.pos; have : 0 < 1 - α := sub_pos.2 hα; positivity
  obtain ⟨i, hi⟩ := exists_pow_lt_of_lt_one hpos (by norm_num : (2⁻¹ : ℝ) < 1)
  refine ⟨i, backtrackingTest_of_le hf.differentiable hf.lipschitz hf.pos htini x ?_⟩
  rw [lt_div_iff₀ htini] at hi
  linarith

end Lemma221

/-! ### Algorithm 2.2.1 (SDBA) -/

/-- **Algorithm 2.2.1** of [cartis2022evaluation] (SDBA), as a run predicate. Let
$f : \mathbb{R}^n \to \mathbb{R}$, and let $\alpha$, $t_{\mathrm{ini}}$ and $\varepsilon$ be
real numbers. A sequence of iterates $(x_k)$, with the given starting point $x_0$, and a
sequence of backtracking indices $(i_k)$ form a **run of SDBA** if $t_{\mathrm{ini}} > 0$ and
$0 < \alpha < 1$ (2.2.2), $\varepsilon > 0$, and at every iteration $k$ before the termination
test $\|\nabla f(x_k)\| \le \varepsilon$ first holds:

* the step $t_k = 2^{-i_k} t_{\mathrm{ini}}$ satisfies the Armijo condition (2.2.1), $f(x_k -
  t_k \nabla f(x_k)) \le f(x_k) - \alpha t_k \|\nabla f(x_k)\|^2$ (Step 3);
* the steps $2^{-j} t_{\mathrm{ini}}$ with $j < i_k$ violate (2.2.1) (Step 3);
* $x_{k+1} = x_k - t_k \nabla f(x_k)$ (Step 4).

The Armijo test is `LineSearch.BacktrackingTest`, and "before the test first holds" is
`Optimization.UntilHit`. -/
structure algorithm_2_2_1 (f : EuclideanSpace ℝ (Fin n) → ℝ) (α tini ε : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (i : ℕ → ℕ) : Prop where
  /-- $t_{\mathrm{ini}} > 0$, part of (2.2.2). -/
  tini_pos : 0 < tini
  /-- $\alpha > 0$, part of (2.2.2). -/
  α_pos : 0 < α
  /-- $\alpha < 1$, part of (2.2.2). -/
  α_lt_one : α < 1
  /-- The accuracy level is positive: $\varepsilon > 0$. -/
  ε_pos : 0 < ε
  /-- Step 3: before termination, the accepted trial step satisfies (2.2.1). -/
  armijo : UntilHit (fun k => ‖gradient f (x k)‖ ≤ ε) fun k =>
    BacktrackingTest f α tini (x k) (i k)
  /-- Step 3: before termination, the earlier trial steps of the iteration violate (2.2.1). -/
  minimal : UntilHit (fun k => ‖gradient f (x k)‖ ≤ ε) fun k =>
    ∀ j < i k, ¬ BacktrackingTest f α tini (x k) j
  /-- Step 4: before termination, $x_{k+1} = x_k - 2^{-i_k} t_{\mathrm{ini}} \nabla f(x_k)$. -/
  step : UntilHit (fun k => ‖gradient f (x k)‖ ≤ ε) fun k =>
    x (k + 1) = x k - (tini * 2⁻¹ ^ i k) • gradient f (x k)

namespace algorithm_2_2_1

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {α tini ε L : ℝ} {x : ℕ → EuclideanSpace ℝ (Fin n)}
  {i : ℕ → ℕ}

/-- Let $(x, i)$ be a run of SDBA, and let the termination test fail at all iterations $j \le k$.
Then $i_k$ is the backtracking index `LineSearch.backtrackingIndex` at $x_k$. -/
theorem index_eq (h : algorithm_2_2_1 f α tini ε x i) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ ‖gradient f (x j)‖ ≤ ε) : i k = backtrackingIndex f α tini (x k) := by
  have ht := h.armijo k hk
  refine le_antisymm ?_ (backtrackingIndex_le_of_test ht)
  by_contra hlt
  exact h.minimal k hk _ (not_le.1 hlt) (backtrackingIndex_spec ⟨_, ht⟩)

/-- **SDBA is deterministic.** Let $(x, i)$ and $(x', i')$ be runs of SDBA with $x'_0 = x_0$, and
let the termination test fail at $x_j$ for all $j < K$. Then $x'_j = x_j$ for all $j \le K$, and
$i'_j = i_j$ for all $j < K$. -/
theorem eq_of_eq {x' : ℕ → EuclideanSpace ℝ (Fin n)} {i' : ℕ → ℕ}
    (h : algorithm_2_2_1 f α tini ε x i) (h' : algorithm_2_2_1 f α tini ε x' i')
    (h0 : x' 0 = x 0) {K : ℕ} (hK : ∀ j < K, ¬ ‖gradient f (x j)‖ ≤ ε) :
    ∀ k ≤ K, (∀ j ≤ k, x' j = x j) ∧ ∀ j < k, i' j = i j := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨fun j hj => by rw [Nat.le_zero.1 hj, h0], fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro hk
    obtain ⟨hx, -⟩ := ih (Nat.le_of_succ_le hk)
    have hstop : ∀ j ≤ k, ¬ ‖gradient f (x j)‖ ≤ ε := fun j hj => hK j (by omega)
    have hstop' : ∀ j ≤ k, ¬ ‖gradient f (x' j)‖ ≤ ε := fun j hj => by
      rw [hx j hj]; exact hstop j hj
    have hi : ∀ j ≤ k, i' j = i j := fun j hj => by
      have hj1 : ∀ l ≤ j, ¬ ‖gradient f (x l)‖ ≤ ε := fun l hl => hstop l (hl.trans hj)
      have hj2 : ∀ l ≤ j, ¬ ‖gradient f (x' l)‖ ≤ ε := fun l hl => hstop' l (hl.trans hj)
      rw [h'.index_eq hj2, h.index_eq hj1, hx j hj]
    refine ⟨fun j hj => ?_, fun j hj => hi j (Nat.lt_succ_iff.1 hj)⟩
    rcases Nat.lt_or_eq_of_le hj with hj | rfl
    · exact hx j (Nat.lt_succ_iff.1 hj)
    · rw [h.step k hstop, h'.step k hstop', hx k le_rfl, hi k le_rfl]

/-- **Decrease of SDBA** ([cartis2022evaluation], (2.2.10)). Let $(x, i)$ be a run of SDBA, let $f$
satisfy f.gL with constant $L$, and let the termination test fail at all iterations $j \le k$.
Then
$$f(x_k) - f(x_{k+1}) \ge \alpha \min\Bigl(t_{\mathrm{ini}}, \frac{1-\alpha}{L}\Bigr) \|\nabla
  f(x_k)\|^2.$$
-/
theorem sub_ge (h : algorithm_2_2_1 f α tini ε x i) (hf : AssumptionGL f L) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ ‖gradient f (x j)‖ ≤ ε) :
    α * min tini ((1 - α) / L) * ‖gradient f (x k)‖ ^ 2 ≤ f (x k) - f (x (k + 1)) := by
  have ht : f (x k - (tini * 2⁻¹ ^ i k) • gradient f (x k)) ≤
      f (x k) - α * (tini * 2⁻¹ ^ i k) * ‖gradient f (x k)‖ ^ 2 := h.armijo k hk
  rw [← h.step k hk] at ht
  have hlow := (lemma_2_2_1_index hf h.α_lt_one h.tini_pos (x k)).2
  rw [← h.index_eq hk] at hlow
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlow h.α_pos.le)
    (sq_nonneg ‖gradient f (x k)‖)
  linarith

end algorithm_2_2_1

/-- **Algorithm 2.2.1** of [cartis2022evaluation], existence of runs. Let $f$ satisfy f.gL, let
$t_{\mathrm{ini}} > 0$ and $0 < \alpha < 1$ (2.2.2), and let $\varepsilon > 0$. Then for every
starting point $x_0$ there is a run $(x, i)$ of SDBA with that starting point.

The algorithm is well defined by Lemma 2.2.1. -/
theorem exists_algorithm_2_2_1 {f : EuclideanSpace ℝ (Fin n) → ℝ} {L α tini ε : ℝ}
    (hf : AssumptionGL f L) (htini : 0 < tini) (hα0 : 0 < α) (hα1 : α < 1) (hε : 0 < ε)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∃ x i, x 0 = x₀ ∧ algorithm_2_2_1 f α tini ε x i := by
  let next : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun y =>
    y - (tini * 2⁻¹ ^ backtrackingIndex f α tini y) • gradient f y
  let x : ℕ → EuclideanSpace ℝ (Fin n) := fun k => Nat.rec x₀ (fun _ y => next y) k
  refine ⟨x, fun k => backtrackingIndex f α tini (x k), rfl,
    ⟨htini, hα0, hα1, hε, fun k _ => ?_, fun k _ j hj => not_backtrackingTest_of_lt hj,
      fun k _ => rfl⟩⟩
  exact backtrackingIndex_spec (exists_backtrackingTest hf hα1 htini (x k))

/-! ### Theorem 2.2.2 -/

/-- **Theorem 2.2.2** of [cartis2022evaluation], the evaluation count. For backtracking indices
$(i_j)$, the number of objective evaluations of SDBA before iteration $k$ is
$$1 + \sum_{j<k} (i_j + 1):$$
one evaluation at Step 0, and $i_j + 1$ evaluations at iteration $j$, in Step 2 and in each
backtrack of Step 3. -/
def sdbaFunEvalCount (i : ℕ → ℕ) (k : ℕ) : ℕ :=
  1 + ∑ j ∈ range k, (i j + 1)

/-- The evaluation count of SDBA before iteration $k$ is $1 + \sum_{j<k} (i_j + 1)$. -/
theorem sdbaFunEvalCount_def (i : ℕ → ℕ) (k : ℕ) :
    sdbaFunEvalCount i k = 1 + ∑ j ∈ range k, (i j + 1) := rfl

/-- If $i_j = 0$ for all $j < k$, that is, no backtracking takes place before iteration $k$, then
SDBA has evaluated $f$ exactly $k + 1$ times before iteration $k$. -/
theorem sdbaFunEvalCount_of_forall_eq_zero {i : ℕ → ℕ} {k : ℕ} (hi : ∀ j < k, i j = 0) :
    sdbaFunEvalCount i k = k + 1 := by
  rw [sdbaFunEvalCount_def, sum_congr rfl fun j hj => by rw [hi j (mem_range.1 hj)]]
  simp [add_comm]

/-- **Theorem 2.2.2** of [cartis2022evaluation], the constant. For $L$, $\alpha$ and
$t_{\mathrm{ini}}$, the complexity constant of SDBA is
$$\kappa = \frac{1}{\alpha \min(t_{\mathrm{ini}}, (1-\alpha)/L)},$$
the reciprocal of the guaranteed decrease per unit of $\|\nabla f\|^2$ in (2.2.10).

**Correction.** The book's constant is $\kappa_{\mathrm{SDBA}} = L/(\alpha(1-\alpha))$ (2.2.13).
It rests on the bound (2.2.7), which holds only when $t_{\mathrm{ini}} \ge (1-\alpha)/L$; in
that case the two constants agree, see `CartisGouldToint.Chapter02.kappaSDBA_of_le`. -/
noncomputable def kappaSDBA (L α tini : ℝ) : ℝ :=
  1 / (α * min tini ((1 - α) / L))

/-- If $L > 0$, $\alpha < 1$ and $t_{\mathrm{ini}} \ge (1-\alpha)/L$, then
$\kappa = L/(\alpha(1-\alpha))$, the book's constant $\kappa_{\mathrm{SDBA}}$ of (2.2.13). -/
theorem kappaSDBA_of_le {L α tini : ℝ} (hL : 0 < L) (hα : α < 1) (h : (1 - α) / L ≤ tini) :
    kappaSDBA L α tini = L / (α * (1 - α)) := by
  have : 0 < 1 - α := sub_pos.2 hα
  rw [kappaSDBA, min_eq_right h]
  field_simp

/-- If $L > 0$, $0 < \alpha < 1$ and $t_{\mathrm{ini}} > 0$, then $\kappa > 0$. -/
theorem kappaSDBA_pos {L α tini : ℝ} (hL : 0 < L) (hα0 : 0 < α) (hα : α < 1) (htini : 0 < tini) :
    0 < kappaSDBA L α tini := by
  have : 0 < 1 - α := sub_pos.2 hα
  unfold kappaSDBA
  have : 0 < min tini ((1 - α) / L) := lt_min htini (by positivity)
  positivity

/-- **Theorem 2.2.2** of [cartis2022evaluation]. Let $f : \mathbb{R}^n \to \mathbb{R}$ satisfy f.Bb
with constant $f_{\mathrm{low}}$ and f.gL with constant $L$, and let $(x, i)$ be a run of SDBA
(Algorithm 2.2.1). Let $\kappa = 1/(\alpha \min(t_{\mathrm{ini}}, (1-\alpha)/L))$ and
$i_{\max} = \lceil \log_2(L t_{\mathrm{ini}}/(2(1-\alpha))) \rceil$ (2.2.6). Then the algorithm
terminates at a first iteration $k_\varepsilon$ with $\|\nabla f(x_{k_\varepsilon})\| \le
\varepsilon$, and
$$k_\varepsilon \le \kappa \frac{f(x_0) - f_{\mathrm{low}}}{\varepsilon^2}$$
(2.2.13). The number of objective evaluations is at most
$$1 + (i_{\max} + 1) \kappa \frac{f(x_0) - f_{\mathrm{low}}}{\varepsilon^2},$$
and the number $k_\varepsilon + 1$ of gradient evaluations is at most $\kappa (f(x_0) -
f_{\mathrm{low}})/\varepsilon^2 + 1$ (2.2.9).

**Correction.** The book's constant is $\kappa_{\mathrm{SDBA}} = L/(\alpha(1-\alpha))$; it
agrees with $\kappa$ when $t_{\mathrm{ini}} \ge (1-\alpha)/L$
(`CartisGouldToint.Chapter02.kappaSDBA_of_le`), and the general constant follows from the
corrected (2.2.7). The printed bound (2.2.8) on the objective evaluations, $i_{\max}
\kappa_{\mathrm{SDBA}} (f(x_0) - f_{\mathrm{low}})/\varepsilon^2$, is false: it ignores the
initial evaluation and the first trial point of each iteration, and it vanishes when
$t_{\mathrm{ini}} \le 2(1-\alpha)/L$, although the algorithm evaluates $f$ at least once.

The constant $\kappa$ is `CartisGouldToint.Chapter02.kappaSDBA L α tini`, the objective
evaluations are counted by `CartisGouldToint.Chapter02.sdbaFunEvalCount`, and $i_{\max}$ uses
the natural-number ceiling `⌈·⌉₊`. -/
theorem theorem_2_2_2 {f : EuclideanSpace ℝ (Fin n) → ℝ} {flow L α tini ε : ℝ}
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {i : ℕ → ℕ} (hb : AssumptionBb f flow)
    (hf : AssumptionGL f L) (h : algorithm_2_2_1 f α tini ε x i) :
    ∃ kε, IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) kε ∧
      (kε : ℝ) ≤ kappaSDBA L α tini * (f (x 0) - flow) / ε ^ 2 ∧
      (sdbaFunEvalCount i kε : ℝ) ≤
        1 + (⌈Real.logb 2 (L * tini / (2 * (1 - α)))⌉₊ + 1) *
          (kappaSDBA L α tini * (f (x 0) - flow) / ε ^ 2) ∧
      ((kε + 1 : ℕ) : ℝ) ≤ kappaSDBA L α tini * (f (x 0) - flow) / ε ^ 2 + 1 := by
  set tmin := min tini ((1 - α) / L)
  have h1α : 0 < 1 - α := sub_pos.2 h.α_lt_one
  have htmin : 0 < tmin := lt_min h.tini_pos (div_pos h1α hf.pos)
  have hε2 : 0 < ε ^ 2 := pow_pos h.ε_pos 2
  have hc : 0 < α * tmin * ε ^ 2 := by have := h.α_pos; positivity
  obtain ⟨kε, hk, hkle⟩ := exists_isFirstHit_of_sub_ge (φ := fun k => f (x k))
    (test := fun k => ‖gradient f (x k)‖ ≤ ε) hc (fun k hk => by
      have h1 := h.sub_ge hf hk
      have hg : ε ≤ ‖gradient f (x k)‖ := (not_le.1 (hk k le_rfl)).le
      have h2 : ε ^ 2 ≤ ‖gradient f (x k)‖ ^ 2 := pow_le_pow_left₀ h.ε_pos.le hg 2
      have := mul_le_mul_of_nonneg_left h2 (mul_pos h.α_pos htmin).le
      linarith) (fun k => hb (x k))
  have hkε : (kε : ℝ) ≤ kappaSDBA L α tini * (f (x 0) - flow) / ε ^ 2 := by
    rw [kappaSDBA, div_mul_eq_mul_div, one_mul, div_div, le_div_iff₀ (by positivity)]
    simpa [mul_assoc] using hkle
  refine ⟨kε, hk, hkε, ?_, by push_cast; linarith⟩
  -- objective evaluations
  set imax := ⌈Real.logb 2 (L * tini / (2 * (1 - α)))⌉₊
  have hsum : (sdbaFunEvalCount i kε : ℝ) ≤ 1 + (imax + 1) * kε := by
    rw [sdbaFunEvalCount_def]
    push_cast
    have : ∑ j ∈ range kε, ((i j : ℝ) + 1) ≤ ∑ _j ∈ range kε, ((imax : ℝ) + 1) := by
      refine sum_le_sum fun j hj => ?_
      have hj : ∀ l ≤ j, ¬ ‖gradient f (x l)‖ ≤ ε :=
        fun l hl => hk.not_test_of_lt (hl.trans_lt (mem_range.1 hj))
      rw [h.index_eq hj]
      have := (lemma_2_2_1_index hf h.α_lt_one h.tini_pos (x j)).1
      have : (backtrackingIndex f α tini (x j) : ℝ) ≤ imax := by exact_mod_cast this
      linarith
    rw [sum_const, card_range, nsmul_eq_mul] at this
    linarith
  have := mul_le_mul_of_nonneg_left hkε (by positivity : (0 : ℝ) ≤ imax + 1)
  linarith

/-! ### Theorem 2.2.3 -/

/-- The unit vector $e_0$ of $\mathbb{R}^1$, along which the one-dimensional examples are laid out.
-/
noncomputable abbrev e₀ : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1

/-- $\|e_0\| = 1$. -/
theorem norm_e₀ : ‖e₀‖ = 1 := by simp [e₀]

/-- For $c \in \mathbb{R}$, $\langle e_0, c e_0\rangle = c$. -/
theorem inner_e₀_smul (c : ℝ) : ⟪e₀, c • e₀⟫ = c := by
  rw [inner_smul_right, real_inner_self_eq_norm_sq, norm_e₀]; ring

/-- For $c \in \mathbb{R}$, $\|c e_0\| = |c|$. -/
theorem norm_smul_e₀ (c : ℝ) : ‖c • e₀‖ = |c| := by
  rw [norm_smul, norm_e₀, mul_one, Real.norm_eq_abs]

/-- Let $G : \mathbb{R} \to \mathbb{R}$ be continuously differentiable with
$|G'(s) - G'(t)| \le L |s - t|$ and $|G(t)| \le B$ for all $s, t$. Then the function
$x \mapsto G(\langle e_0, x\rangle)$ on $\mathbb{R}^1$ satisfies f.Bb with
$f_{\mathrm{low}} = -B$ and f.gL with the constant $\max(L, 1)$, and its gradient at $y$ is
$G'(\langle e_0, y\rangle) e_0$.

The function is `Optimization.ridge G e₀`. -/
theorem ridge_assumptions {G : ℝ → ℝ} {L B : ℝ} (hG : ContDiff ℝ 1 G)
    (hGL : ∀ s t, |deriv G s - deriv G t| ≤ L * |s - t|) (hGB : ∀ t, |G t| ≤ B) :
    AssumptionBb (ridge G e₀) (-B) ∧ AssumptionGL (ridge G e₀) (max L 1) ∧
      ∀ y, gradient (ridge G e₀) y = deriv G ⟪e₀, y⟫ • e₀ := by
  have hgrad : ∀ y, gradient (ridge G e₀) y = deriv G ⟪e₀, y⟫ • e₀ :=
    gradient_ridge (hG.differentiable one_ne_zero)
  refine ⟨fun y => by rw [ridge_apply]; linarith [neg_abs_le (G ⟪e₀, y⟫), hGB ⟪e₀, y⟫],
    .of_lipschitz (contDiff_ridge hG) (le_max_right _ _) fun y z => ?_, hgrad⟩
  rw [hgrad, hgrad, ← sub_smul, norm_smul, norm_e₀, mul_one, Real.norm_eq_abs]
  have h1 := hGL ⟪e₀, y⟫ ⟪e₀, z⟫
  have h2 : |⟪e₀, y⟫ - ⟪e₀, z⟫| ≤ ‖y - z‖ := by
    rw [← inner_sub_right]
    exact (abs_real_inner_le_norm _ _).trans (by rw [norm_e₀, one_mul])
  have hL0 : 0 ≤ L := by
    by_contra hneg
    have := (abs_nonneg _).trans (hGL 1 0)
    simp at this
    linarith
  calc |deriv G ⟪e₀, y⟫ - deriv G ⟪e₀, z⟫| ≤ L * |⟪e₀, y⟫ - ⟪e₀, z⟫| := h1
    _ ≤ L * ‖y - z‖ := mul_le_mul_of_nonneg_left h2 hL0
    _ ≤ max L 1 * ‖y - z‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)

/-- The quantity $\omega_k = \varepsilon (k_\varepsilon - k)/k_\varepsilon$ of the data
(2.2.15)–(2.2.19) of the slow example in the proof of Theorem 2.2.3 ([cartis2022evaluation]). -/
noncomputable def slowOmega (ε : ℝ) (kε k : ℕ) : ℝ := ε * ((kε : ℝ) - k) / kε

/-- $\omega_k = \varepsilon (k_\varepsilon - k)/k_\varepsilon$. -/
theorem slowOmega_def (ε : ℝ) (kε k : ℕ) : slowOmega ε kε k = ε * ((kε : ℝ) - k) / kε := rfl

/-- The abscissae $x_k = \sum_{j<k} \theta (\varepsilon + \omega_j)$ of the one-dimensional slow
example with the constant step factor $\theta$, from the proof of Theorem 2.2.3 of
[cartis2022evaluation]. -/
noncomputable def slowX (θ ε : ℝ) (kε k : ℕ) : ℝ := ∑ j ∈ range k, θ * (ε + slowOmega ε kε j)

/-- The function values $f_k = 4\theta - \sum_{j<k} \theta (\varepsilon + \omega_j)^2$ of the
one-dimensional slow example with the constant step factor $\theta$, from the proof of Theorem
2.2.3 of [cartis2022evaluation]. -/
noncomputable def slowF (θ ε : ℝ) (kε k : ℕ) : ℝ :=
  4 * θ - ∑ j ∈ range k, θ * (ε + slowOmega ε kε j) ^ 2

/-- $\omega_{k_\varepsilon} = 0$. -/
theorem slowOmega_self {ε : ℝ} {kε : ℕ} : slowOmega ε kε kε = 0 := by simp [slowOmega]

/-- If $\varepsilon > 0$ and $k < k_\varepsilon$, then $\omega_k > 0$. -/
theorem slowOmega_pos {ε : ℝ} (hε : 0 < ε) {kε k : ℕ} (hk : k < kε) : 0 < slowOmega ε kε k := by
  have : (k : ℝ) < kε := by exact_mod_cast hk
  have : (0 : ℝ) < kε := by have := Nat.zero_le k; exact_mod_cast (Nat.zero_le k).trans_lt hk
  unfold slowOmega
  apply div_pos (mul_pos hε (by linarith)) this

/-- **The slow example for first-order methods** ([cartis2022evaluation], proof of Theorem 2.2.3).
For every step factor $\theta > 0$ there are $L \ge 1$ and $f_{\mathrm{low}}$ with the following
property. For every $\varepsilon \in (0, 1]$ and $k_\varepsilon \in \mathbb{N}$ with
$k_\varepsilon \varepsilon^2 = 1$ there is $f : \mathbb{R}^1 \to \mathbb{R}$ that satisfies f.Bb
with $f_{\mathrm{low}}$ and f.gL with $L$, and such that for all $k \le k_\varepsilon$ the point
$x_k e_0$ has the value $f(x_k e_0) = f_k$ and the gradient $\nabla f(x_k e_0) = -(\varepsilon +
\omega_k) e_0$.

The abscissae and values are `CartisGouldToint.Chapter02.slowX θ ε k_ε k` and
`CartisGouldToint.Chapter02.slowF θ ε k_ε k`. -/
theorem exists_slow_example {θ : ℝ} (hθ : 0 < θ) :
    ∃ L flow : ℝ, 1 ≤ L ∧ ∀ (ε : ℝ) (kε : ℕ), 0 < ε → ε ≤ 1 → (kε : ℝ) * ε ^ 2 = 1 →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, AssumptionBb f flow ∧ AssumptionGL f L ∧
        ∀ k ≤ kε, f (slowX θ ε kε k • e₀) = slowF θ ε kε k ∧
          gradient f (slowX θ ε kε k • e₀) = -(ε + slowOmega ε kε k) • e₀ := by
  obtain ⟨L, B, -, -, H⟩ := exists_slowFirstOrder_interpolant hθ le_rfl
  refine ⟨max L 1, -B, le_max_right _ _, fun ε kε hε hε1 hkε => ?_⟩
  obtain ⟨G, hG, hGL, hGB, -, hGk⟩ := H ε kε (fun _ => θ) (slowX θ ε kε) (slowF θ ε kε) hε hε1
    hkε (fun _ _ => ⟨le_rfl, le_rfl⟩) (fun k _ => by simp [slowX, slowOmega, sum_range_succ])
    (by simp [slowF]) (fun k _ => by simp [slowF, slowOmega, sum_range_succ]; ring)
  obtain ⟨hb, hgl, hgrad⟩ := ridge_assumptions hG hGL hGB
  refine ⟨ridge G e₀, hb, hgl, fun k hk => ?_⟩
  rw [hgrad, ridge_apply, inner_e₀_smul, (hGk k hk).1, (hGk k hk).2]
  exact ⟨rfl, by simp [slowOmega]⟩

/-- $x_{k+1} = x_k + \theta (\varepsilon + \omega_k)$ for the abscissae of the slow example. -/
theorem slowX_succ (θ ε : ℝ) (kε k : ℕ) :
    slowX θ ε kε (k + 1) = slowX θ ε kε k + θ * (ε + slowOmega ε kε k) := by
  simp [slowX, sum_range_succ]

/-- $f_{k+1} = f_k - \theta (\varepsilon + \omega_k)^2$ for the function values of the slow example.
-/
theorem slowF_succ (θ ε : ℝ) (kε k : ℕ) :
    slowF θ ε kε (k + 1) = slowF θ ε kε k - θ * (ε + slowOmega ε kε k) ^ 2 := by
  simp [slowF, sum_range_succ]; ring

/-- Let $\varepsilon > 0$, let $f : \mathbb{R}^1 \to \mathbb{R}$ satisfy
$\nabla f(x_k e_0) = -(\varepsilon + \omega_k) e_0$ at the points $x_k e_0$ of the slow example
for $k \le k_\varepsilon$, and let $(z_k)$ be a sequence with $z_k = x_k e_0$ for
$k \le k_\varepsilon$. Then $k_\varepsilon$ is the first index $k$ with
$\|\nabla f(z_k)\| \le \varepsilon$, since $\|\nabla f(z_k)\| = \varepsilon + \omega_k$ exceeds
$\varepsilon$ for $k < k_\varepsilon$ and equals $\varepsilon$ at $k_\varepsilon$. -/
theorem isFirstHit_slow {f : EuclideanSpace ℝ (Fin 1) → ℝ} {θ ε : ℝ} {kε : ℕ} (hε : 0 < ε)
    {x : ℕ → EuclideanSpace ℝ (Fin 1)} (hx : ∀ k ≤ kε, x k = slowX θ ε kε k • e₀)
    (hg : ∀ k ≤ kε, gradient f (slowX θ ε kε k • e₀) = -(ε + slowOmega ε kε k) • e₀) :
    IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) kε := by
  have hnorm : ∀ k ≤ kε, ‖gradient f (x k)‖ = ε + slowOmega ε kε k := fun k hk => by
    rw [hx k hk, hg k hk, norm_smul, norm_e₀, mul_one, norm_neg, Real.norm_eq_abs, abs_of_nonneg]
    have : (k : ℝ) ≤ kε := by exact_mod_cast hk
    have : 0 ≤ slowOmega ε kε k := by
      unfold slowOmega; positivity
    linarith
  refine ⟨by simp only; rw [hnorm kε le_rfl, slowOmega_self, add_zero], fun j hj => ?_⟩
  simp only
  rw [hnorm j hj.le, not_le]
  linarith [slowOmega_pos hε hj]

/-- **Theorem 2.2.3** of [cartis2022evaluation] (sharpness of SDBA). For every
$t_{\mathrm{ini}} > 0$ there are $L \ge 1$ and $f_{\mathrm{low}}$, which depend only on
$t_{\mathrm{ini}}$, with the following property. For every $\alpha \in (0, 1)$, every
$\varepsilon \in (0, 1]$ and every integer $k_\varepsilon$ with
$k_\varepsilon \varepsilon^2 = 1$ there is $f : \mathbb{R}^1 \to \mathbb{R}$ that satisfies f.Bb
with $f_{\mathrm{low}}$ and f.gL with $L$, such that a run of SDBA from $x_0 = 0$ exists, and
every run $(x, i)$ of SDBA from $x_0 = 0$ satisfies: $i_k = 0$ for all $k < k_\varepsilon$, the
run terminates exactly at iteration $k_\varepsilon$, and it uses $k_\varepsilon + 1$ evaluations
of $f$.

**Generalization.** The book's proof assumes $t_{\mathrm{ini}} \ge \alpha$; this hypothesis is
not needed.

**Reading.** The number $\varepsilon^{-2}$ is assumed to be an integer $k_\varepsilon$, as the
proof does in (2.2.14).

Since the run terminates at $k_\varepsilon$, it also evaluates $\nabla f$ exactly
$k_\varepsilon + 1$ times. The function evaluations are counted by
`CartisGouldToint.Chapter02.sdbaFunEvalCount`. -/
theorem theorem_2_2_3 {tini : ℝ} (htini : 0 < tini) :
    ∃ L flow : ℝ, 1 ≤ L ∧ ∀ α : ℝ, 0 < α → α < 1 → ∀ (ε : ℝ) (kε : ℕ), 0 < ε → ε ≤ 1 →
      (kε : ℝ) * ε ^ 2 = 1 →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, AssumptionBb f flow ∧ AssumptionGL f L ∧
        (∃ x i, x 0 = 0 ∧ algorithm_2_2_1 f α tini ε x i) ∧
        ∀ x i, x 0 = 0 → algorithm_2_2_1 f α tini ε x i →
          (∀ k < kε, i k = 0) ∧ IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) kε ∧
            sdbaFunEvalCount i kε = kε + 1 := by
  obtain ⟨L, flow, hL, H⟩ := exists_slow_example htini
  refine ⟨L, flow, hL, fun α hα0 hα1 ε kε hε hε1 hkε => ?_⟩
  obtain ⟨f, hb, hgl, hfk⟩ := H ε kε hε hε1 hkε
  set x : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => slowX tini ε kε k • e₀
  have hhit : IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) kε :=
    isFirstHit_slow hε (fun _ _ => rfl) fun k hk => (hfk k hk).2
  -- the constructed run never backtracks
  have hbefore : ∀ k, (∀ j ≤ k, ¬ ‖gradient f (x j)‖ ≤ ε) → k < kε := fun k hk =>
    not_le.1 fun hle => hk kε hle hhit.test
  have hstep : ∀ k < kε, x (k + 1) = x k - (tini * 2⁻¹ ^ 0) • gradient f (x k) := fun k hk => by
    simp only [x, pow_zero, mul_one]
    rw [(hfk k hk.le).2, slowX_succ]
    module
  have hrun : algorithm_2_2_1 f α tini ε x fun _ => 0 := by
    refine ⟨htini, hα0, hα1, hε, fun k hk => ?_, fun k _ j hj => absurd hj (Nat.not_lt_zero _),
      fun k hk => hstep k (hbefore k hk)⟩
    have hk := hbefore k hk
    change f (x k - (tini * 2⁻¹ ^ 0) • gradient f (x k)) ≤
      f (x k) - α * (tini * 2⁻¹ ^ 0) * ‖gradient f (x k)‖ ^ 2
    rw [← hstep k hk]
    simp only [x]
    rw [(hfk (k + 1) hk).1, (hfk k hk.le).1, (hfk k hk.le).2, slowF_succ, norm_smul, norm_neg,
      norm_e₀, mul_one, Real.norm_eq_abs, sq_abs, pow_zero, mul_one]
    have : 0 ≤ tini * (ε + slowOmega ε kε k) ^ 2 := by positivity
    nlinarith
  refine ⟨f, hb, hgl, ⟨x, _, by simp [x, slowX], hrun⟩, fun x' i' hx0 h' => ?_⟩
  obtain ⟨hx, hi⟩ := hrun.eq_of_eq h' (by rw [hx0]; simp [x, slowX]) hhit.2 kε le_rfl
  refine ⟨hi, ?_, sdbaFunEvalCount_of_forall_eq_zero hi⟩
  exact ⟨by simp only; rw [hx kε le_rfl]; exact hhit.test,
    fun j hj => by simp only; rw [hx j hj.le]; exact hhit.not_test_of_lt hj⟩

/-! ### The exact linesearch (SDEX) and Theorem 2.2.4 -/

section SDEX

variable {f : EuclideanSpace ℝ (Fin n) → ℝ}

/-- **Section 2.2.3.4** of [cartis2022evaluation], the SDEX algorithm. Let
$f : \mathbb{R}^n \to \mathbb{R}$ and $\varepsilon \in \mathbb{R}$. A sequence of iterates
$(x_k)$ and a sequence of steps $(t_k)$ form a **run of SDEX**, steepest descent with the exact
linesearch (2.2.26), if $\varepsilon > 0$ and at every iteration $k$ before the termination test
$\|\nabla f(x_k)\| \le \varepsilon$ first holds, $t_k$ is the first global minimizer of
$t \mapsto f(x_k - t \nabla f(x_k))$ on $t \ge 0$ and $x_{k+1} = x_k - t_k \nabla f(x_k)$.

The exact linesearch is `LineSearch.IsExactLineMin`. -/
structure IsSDEXRun (f : EuclideanSpace ℝ (Fin n) → ℝ) (ε : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (t : ℕ → ℝ) : Prop where
  /-- The accuracy level is positive: $\varepsilon > 0$. -/
  ε_pos : 0 < ε
  /-- Before termination, $t_k$ satisfies the exact linesearch (2.2.26). -/
  exact : UntilHit (fun k => ‖gradient f (x k)‖ ≤ ε) fun k => IsExactLineMin f (x k) (t k)
  /-- Before termination, $x_{k+1} = x_k - t_k \nabla f(x_k)$. -/
  step : UntilHit (fun k => ‖gradient f (x k)‖ ≤ ε) fun k =>
    x (k + 1) = x k - t k • gradient f (x k)

/-- **Section 2.2.3.4** of [cartis2022evaluation], existence of SDEX runs. Let
$f : \mathbb{R}^n \to \mathbb{R}$ be continuous, let $\varepsilon > 0$, and let
$x_0 \in \mathbb{R}^n$ be such that the sublevel set $\{y : f(y) \le f(x_0)\}$ is bounded. Then
there is a run of SDEX from $x_0$. -/
theorem IsSDEXRun.exists (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) {x₀ : EuclideanSpace ℝ (Fin n)}
    (hbdd : Bornology.IsBounded {y | f y ≤ f x₀}) :
    ∃ x t, x 0 = x₀ ∧ IsSDEXRun f ε x t := by
  classical
  let T : EuclideanSpace ℝ (Fin n) → ℝ := fun y =>
    if h : Bornology.IsBounded {z | f z ≤ f y} then (exists_isExactLineMin hf h).choose else 0
  have hT : ∀ y, Bornology.IsBounded {z | f z ≤ f y} → IsExactLineMin f y (T y) := fun y h => by
    simp only [T, h, dite_true]
    exact (exists_isExactLineMin hf h).choose_spec
  let x : ℕ → EuclideanSpace ℝ (Fin n) := fun k =>
    Nat.rec x₀ (fun _ y => y - T y • gradient f y) k
  have hle : ∀ k, f (x k) ≤ f x₀ := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
      have hb : Bornology.IsBounded {z | f z ≤ f (x k)} :=
        hbdd.subset fun z hz => (show f z ≤ f (x k) from hz).trans ih
      have := (hT (x k) hb).1.2 0 le_rfl
      simp only [zero_smul, sub_zero] at this
      exact this.trans ih
  refine ⟨x, fun k => T (x k), rfl, hε, fun k _ => hT _ ?_, fun k _ => rfl⟩
  exact hbdd.subset fun z hz => (show f z ≤ f (x k) from hz).trans (hle k)

/-- **Theorem 2.2.4** of [cartis2022evaluation]. Let $f : \mathbb{R}^n \to \mathbb{R}$ satisfy f.Bb
with constant $f_{\mathrm{low}}$ and f.gL with constant $L = L_{f,1}$, and let $(x, t)$ be a run
of SDEX. Then the run terminates at a first iteration $k_\varepsilon$ with $\|\nabla
f(x_{k_\varepsilon})\| \le \varepsilon$, and
$$k_\varepsilon \le \kappa_{\mathrm{SDEX}} \frac{f(x_0) - f_{\mathrm{low}}}{\varepsilon^2},
  \qquad \kappa_{\mathrm{SDEX}} = 2L.$$

This is (2.2.27). It bounds the iterations, not the evaluations, since the exact linesearch has
no evaluation count. -/
theorem theorem_2_2_4 {flow L ε : ℝ} {x : ℕ → EuclideanSpace ℝ (Fin n)} {t : ℕ → ℝ}
    (hb : AssumptionBb f flow) (hf : AssumptionGL f L) (h : IsSDEXRun f ε x t) :
    ∃ kε, IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) kε ∧
      (kε : ℝ) ≤ 2 * L * (f (x 0) - flow) / ε ^ 2 := by
  have hε2 : 0 < ε ^ 2 := pow_pos h.ε_pos 2
  have hL := hf.pos
  obtain ⟨kε, hk, hkle⟩ := exists_isFirstHit_of_sub_ge (φ := fun k => f (x k))
    (test := fun k => ‖gradient f (x k)‖ ≤ ε) (c := ε ^ 2 / (2 * L)) (by positivity)
    (fun k hk => by
      have hg : ε < ‖gradient f (x k)‖ := not_le.1 (hk k le_rfl)
      have hne : gradient f (x k) ≠ 0 := norm_pos_iff.1 (h.ε_pos.trans hg)
      have hdec := (decrease_ge_of_exactLineMin hf.differentiable hf.lipschitz hL hne
        (Or.inl (h.exact k hk).isGlobalLineMin)).2
      rw [← h.step k hk] at hdec
      have : ε ^ 2 ≤ ‖gradient f (x k)‖ ^ 2 := pow_le_pow_left₀ h.ε_pos.le hg.le 2
      have : ε ^ 2 / (2 * L) ≤ ‖gradient f (x k)‖ ^ 2 / (2 * L) :=
        div_le_div_of_nonneg_right this (by positivity)
      linarith) (fun k => hb (x k))
  refine ⟨kε, hk, ?_⟩
  rw [le_div_iff₀ hε2]
  have : (kε : ℝ) * (ε ^ 2 / (2 * L)) * (2 * L) ≤ (f (x 0) - flow) * (2 * L) :=
    mul_le_mul_of_nonneg_right hkle (by positivity)
  field_simp at this
  linarith

/-- **Theorem 2.2.5** of [cartis2022evaluation] (sharpness of SDEX). There are $L \ge 1$ and
$f_{\mathrm{low}}$ with the following property. For every $\varepsilon > 0$ and every integer
$k_\varepsilon$ with $k_\varepsilon \varepsilon^2 = 1$ there is
$f : \mathbb{R}^2 \to \mathbb{R}$ that satisfies f.Bb with $f_{\mathrm{low}}$ and f.gL with $L$,
such that a run of SDEX from $x_0 = 0$ exists, and every run $(x, t)$ of SDEX from $x_0 = 0$
takes the steps $t_k = \sqrt{2}$ for $k < k_\varepsilon$ and terminates exactly at iteration
$k_\varepsilon$.

**Reading.** The number $\varepsilon^{-2}$ is assumed to be an integer $k_\varepsilon$, as in
Theorem 2.2.3.

SDEX is deterministic, since the first global line minimizer is unique. The function is the
zig-zag example `Optimization.zigZagFunction ε k_ε` of Appendix B; see Lemmas B.2.2–B.2.6 in
`NumlibSurface.CartisGouldToint.AppendixB.Chapter02`. The book's proof has a gap: with the
book's corridor function (B.2.19) the iterates are only first local line minimizers. The
modified corridor function of the construction closes the gap; see
`CartisGouldToint.AppendixB.lemma_B_2_6`. -/
theorem theorem_2_2_5 :
    ∃ L flow : ℝ, 1 ≤ L ∧ ∀ (ε : ℝ) (kε : ℕ), 0 < ε → (kε : ℝ) * ε ^ 2 = 1 →
      ∃ f : EuclideanSpace ℝ (Fin 2) → ℝ, AssumptionBb f flow ∧ AssumptionGL f L ∧
        (∃ x t, x 0 = 0 ∧ IsSDEXRun f ε x t) ∧
        ∀ x t, x 0 = 0 → IsSDEXRun f ε x t →
          (∀ k < kε, t k = √2) ∧ IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) kε := by
  obtain ⟨M, L, -, hL, H⟩ := zigZag_bounds
  refine ⟨L, -M, hL, fun ε kε hε hkε => ?_⟩
  have hadm : ZigZag.IsAdmissible ε kε := ⟨hε, hkε⟩
  obtain ⟨hC, hlow, hlip⟩ := H ε kε hadm
  set f := zigZagFunction ε kε
  set z : ℕ → EuclideanSpace ℝ (Fin 2) := zigZagIterate ε kε
  have hz0 : z 0 = 0 := ZigZag.zigZagIterate_zero ε kε
  have hnorm : ∀ k ≤ kε, ‖gradient f (z k)‖ = ε + ZigZag.omega ε kε k :=
    fun k hk => (zigZag_gradient hadm hk).2.1
  have hhit : IsFirstHit (fun k => ‖gradient f (z k)‖ ≤ ε) kε := by
    refine ⟨by simp only; rw [hnorm kε le_rfl, ZigZag.omega_self, add_zero], fun j hj => ?_⟩
    simp only
    rw [hnorm j hj.le, not_le]
    linarith [hadm.omega_pos hj]
  have hbefore : ∀ k, (∀ j ≤ k, ¬ ‖gradient f (z j)‖ ≤ ε) → k < kε := fun k hk =>
    not_le.1 fun hle => hk kε hle hhit.test
  have hrun : IsSDEXRun f ε z fun _ => √2 :=
    ⟨hε, fun k hk => zigZag_isExactLineMin hadm (hbefore k hk),
      fun k hk => (zigZag_gradient hadm (hbefore k hk).le).2.2⟩
  refine ⟨f, hlow, .of_lipschitz hC hL hlip, ⟨z, _, hz0, hrun⟩, fun x t hx0 h => ?_⟩
  -- every run follows the zig-zag iterates
  have heq : ∀ k ≤ kε, (∀ j ≤ k, x j = z j) ∧ ∀ j < k, t j = √2 := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨fun j hj => by rw [Nat.le_zero.1 hj, hx0, hz0],
        fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨hx, ht⟩ := ih (Nat.le_of_succ_le hk)
      have hstop : ∀ j ≤ k, ¬ ‖gradient f (x j)‖ ≤ ε := fun j hj => by
        rw [hx j hj]; exact hhit.not_test_of_lt (by omega)
      have htk : t k = √2 := by
        have h1 : IsExactLineMin f (x k) (t k) := h.exact k hstop
        rw [hx k le_rfl] at h1
        exact h1.unique (zigZag_isExactLineMin hadm (by omega))
      refine ⟨fun j hj => ?_, fun j hj => ?_⟩
      · rcases Nat.lt_or_eq_of_le hj with hj | rfl
        · exact hx j (Nat.lt_succ_iff.1 hj)
        · rw [h.step k hstop, hx k le_rfl, htk]
          exact ((zigZag_gradient hadm (k := k) (by omega)).2.2).symm
      · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 hj) with hj | rfl
        · exact ht j hj
        · exact htk
  obtain ⟨hx, ht⟩ := heq kε le_rfl
  exact ⟨ht, ⟨by simp only; rw [hx kε le_rfl]; exact hhit.test,
    fun j hj => by simp only; rw [hx j hj.le]; exact hhit.not_test_of_lt hj⟩⟩

end SDEX

end CartisGouldToint.Chapter02

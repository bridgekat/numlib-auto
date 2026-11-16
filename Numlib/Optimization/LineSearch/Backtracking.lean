/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Numlib.Analysis.Calculus.MeanValue
import Numlib.Optimization.LineSearch

/-!
# Steepest descent: backtracking-Armijo and exact line searches

This file studies step-size rules for the steepest-descent iteration $x^+ = x - t \nabla f(x)$ on a
real Hilbert space, as analysed in [cartis2022evaluation], §2.2. The objective $f$ is
differentiable, and its gradient is $L$-Lipschitz: $\|\nabla f(y) - \nabla f(z)\| \le L \|y - z\|$.
The descent lemma $f(x + d) \le f(x) + \langle \nabla f(x), d\rangle + \tfrac{L}{2} \|d\|^2$ then
shows that the Armijo condition (2.2.1)
$$f(x - t \nabla f(x)) \le f(x) - \alpha t \|\nabla f(x)\|^2$$
holds for every $t \in [0, 2(1 - \alpha)/L]$ (Lemma 2.2.1).

The backtracking-Armijo line search of Algorithm 2.2.1 tries the steps $t_{\mathrm{ini}} 2^{-i}$ for
$i = 0, 1, \dots$ and accepts the first one that satisfies (2.2.1). The file bounds the number of
trials and the accepted step. The exact line search (2.2.26) takes the first global minimizer of
$t \mapsto f(x - t \nabla f(x))$ on $t \ge 0$; the file shows that it is well defined, and that it
and the first-local-minimizer rule give a decrease of at least $\|\nabla f(x)\|^2 / (2L)$, the core
of Theorem 2.2.4.

## Main definitions

* `LineSearch.backtrackingIndex`: the number of halvings in Algorithm 2.2.1, the least $i$ such that
  $t_{\mathrm{ini}} 2^{-i}$ satisfies (2.2.1).
* `LineSearch.IsExactLineMin`: the exact line search (2.2.26), the first global minimizer of
  $t \mapsto f(x - t \nabla f(x))$ on $t \ge 0$.
* `LineSearch.IsFirstLocalLineMin`: the first stationary point along the ray, with negative slope
  before it. This is the rule that the sharpness example for the exact line search (Theorem 2.2.5,
  Lemma B.2.6) realises.

## Main results

* `LineSearch.le_add_inner_add_of_lipschitz_gradient`: the descent lemma, (A.19) with $p = 1$.
* `LineSearch.armijo_neg_gradient_of_le`: Lemma 2.2.1, the Armijo condition (2.2.1) for every
  $t \in [0, 2(1 - \alpha)/L]$.
* `LineSearch.backtrackingIndex_le`: the bound (2.2.6) on the number of halvings, and the lower
  bound $t \ge \min\{t_{\mathrm{ini}}, (1 - \alpha)/L\}$ on the accepted step.
* `LineSearch.IsExactLineMin.unique` and `LineSearch.exists_isExactLineMin`: the exact line search
  is unique, and it exists when $f$ is continuous with a bounded sublevel set.
* `LineSearch.decrease_ge_of_exactLineMin`: for a global line minimizer or a first-local-minimizer
  step, $t \ge 1/L$ and the decrease is at least $\|\nabla f(x)\|^2 / (2L)$, (2.2.28).

## Implementation notes

* The source gives the step bound (2.2.7) as $t \ge (1 - \alpha)/L$. This holds when
  $t_{\mathrm{ini}} \ge (1 - \alpha)/L$, but not in general, because the first trial step may
  already be shorter. `LineSearch.backtrackingIndex_le` proves
  $t \ge \min\{t_{\mathrm{ini}}, (1 - \alpha)/L\}$.
-/

open Set
open scoped RealInnerProductSpace

namespace LineSearch

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f : E → ℝ} {L α : ℝ}

/-! ### The descent lemma -/

/-- The derivative of $f$ at $x$ applied to $d$ is $\langle \nabla f(x), d\rangle$. -/
theorem fderiv_apply_eq_inner_gradient (f : E → ℝ) (x d : E) :
    fderiv ℝ f x d = ⟪gradient f x, d⟫ := by
  rw [gradient, InnerProductSpace.toDual_symm_apply]

/-- The operator norm of the difference of two derivatives of $f$ is the norm of the difference of
the gradients: $\|f'(y) - f'(z)\| = \|\nabla f(y) - \nabla f(z)\|$. -/
theorem norm_fderiv_sub_fderiv_eq (f : E → ℝ) (y z : E) :
    ‖fderiv ℝ f y - fderiv ℝ f z‖ = ‖gradient f y - gradient f z‖ := by
  have h : fderiv ℝ f y - fderiv ℝ f z =
      InnerProductSpace.toDual ℝ E (gradient f y - gradient f z) := by
    simp [gradient]
  rw [h, LinearIsometryEquiv.norm_map]

/-- The **descent lemma**, (A.19) of [cartis2022evaluation] with $p = 1$. Let $f : E \to \mathbb{R}$
be differentiable on a real Hilbert space $E$, with
$\|\nabla f(y) - \nabla f(z)\| \le L \|y - z\|$ for all $y, z$. Then for all $x, d \in E$,
$$f(x + d) \le f(x) + \langle \nabla f(x), d\rangle + \frac{L}{2} \|d\|^2.$$
-/
theorem le_add_inner_add_of_lipschitz_gradient (hf : Differentiable ℝ f)
    (hL : ∀ y z, ‖gradient f y - gradient f z‖ ≤ L * ‖y - z‖) (x d : E) :
    f (x + d) ≤ f x + ⟪gradient f x, d⟫ + L / 2 * ‖d‖ ^ 2 := by
  have h := Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le (𝕜 := ℝ) convex_univ
    (fun z _ => (hf z).hasFDerivAt) (mem_univ x) (mem_univ (x + d)) (C := L)
    (fun z _ => by rw [norm_fderiv_sub_fderiv_eq]; exact hL z x)
  simp only [add_sub_cancel_left, Real.norm_eq_abs, fderiv_apply_eq_inner_gradient] at h
  linarith [le_abs_self (f (x + d) - f x - ⟪gradient f x, d⟫)]

/-! ### Armijo condition along the steepest-descent direction -/

/-- Along $d = -\nabla f(x)$, the Armijo condition `LineSearch.Armijo` with the derivative
`fderiv ℝ f` is the inequality (2.2.1) of [cartis2022evaluation]:
$$f(x - t \nabla f(x)) \le f(x) - \alpha t \|\nabla f(x)\|^2.$$
-/
theorem armijo_neg_gradient_iff {x : E} {t : ℝ} :
    Armijo f (fderiv ℝ f) α x (-gradient f x) t ↔
      f (x - t • gradient f x) ≤ f x - α * t * ‖gradient f x‖ ^ 2 := by
  rw [Armijo, fderiv_apply_eq_inner_gradient, inner_neg_right, real_inner_self_eq_norm_sq,
    smul_neg, ← sub_eq_add_neg]
  constructor <;> intro h <;> linarith

/-- **Lemma 2.2.1** of [cartis2022evaluation], (2.2.3)–(2.2.4). Let $f : E \to \mathbb{R}$ be
differentiable on a real Hilbert space $E$, with $\|\nabla f(y) - \nabla f(z)\| \le L \|y - z\|$
for all $y, z$ and $L > 0$. Then for every $x \in E$ and every step
$t \in [0, 2(1 - \alpha)/L]$, the Armijo condition along the steepest-descent direction holds:
$$f(x - t \nabla f(x)) \le f(x) - \alpha t \|\nabla f(x)\|^2.$$
-/
theorem armijo_neg_gradient_of_le (hf : Differentiable ℝ f)
    (hL : ∀ y z, ‖gradient f y - gradient f z‖ ≤ L * ‖y - z‖) (hL0 : 0 < L) (x : E) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ 2 * (1 - α) / L) :
    f (x - t • gradient f x) ≤ f x - α * t * ‖gradient f x‖ ^ 2 := by
  have h := le_add_inner_add_of_lipschitz_gradient hf hL x (-(t • gradient f x))
  rw [← sub_eq_add_neg, inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq,
    norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0] at h
  have hLt : L * t ≤ 2 * (1 - α) := by rwa [le_div_iff₀ hL0, mul_comm] at ht
  have hg := sq_nonneg ‖gradient f x‖
  nlinarith [mul_nonneg (mul_nonneg ht0 hg) (sub_nonneg.2 hLt)]

/-! ### The backtracking index -/

/-- The Armijo test (2.2.1) of Algorithm 2.2.1 of [cartis2022evaluation] at the $i$-th trial step
$t_i = t_{\mathrm{ini}} 2^{-i}$:
$$f(x - t_i \nabla f(x)) \le f(x) - \alpha t_i \|\nabla f(x)\|^2.$$
-/
def BacktrackingTest (f : E → ℝ) (α tini : ℝ) (x : E) (i : ℕ) : Prop :=
  f (x - (tini * 2⁻¹ ^ i) • gradient f x) ≤ f x - α * (tini * 2⁻¹ ^ i) * ‖gradient f x‖ ^ 2

open Classical in
/-- The **backtracking index** of Algorithm 2.2.1 of [cartis2022evaluation], Steps 2–3: the least
$i \in \mathbb{N}$ such that the trial step $t_{\mathrm{ini}} 2^{-i}$ satisfies the Armijo
condition (2.2.1), `LineSearch.BacktrackingTest`. If no trial step satisfies it, the value is
$0$.

The accepted step is $t_{\mathrm{ini}} 2^{-i}$, and the line search evaluates $f$ at $i + 1$
trial points. -/
noncomputable def backtrackingIndex (f : E → ℝ) (α tini : ℝ) (x : E) : ℕ :=
  if h : ∃ i, BacktrackingTest f α tini x i then Nat.find h else 0

/-- If some trial step satisfies the Armijo test, the backtracking index is the least index whose
trial step satisfies it, as given by `Nat.find`. -/
theorem backtrackingIndex_eq_find {tini : ℝ} {x : E} (h : ∃ i, BacktrackingTest f α tini x i)
    [DecidablePred (BacktrackingTest f α tini x)] :
    backtrackingIndex f α tini x = Nat.find h := by
  rw [backtrackingIndex, dite_eq_left_of_eq_true (eq_true h)]
  congr

/-- If some trial step satisfies the Armijo test, then the trial step at the backtracking index
satisfies it. -/
theorem backtrackingIndex_spec {tini : ℝ} {x : E} (h : ∃ i, BacktrackingTest f α tini x i) :
    BacktrackingTest f α tini x (backtrackingIndex f α tini x) := by
  classical
  rw [backtrackingIndex_eq_find h]
  exact Nat.find_spec h

/-- Every trial step before the backtracking index fails the Armijo test. -/
theorem not_backtrackingTest_of_lt {tini : ℝ} {x : E} {i : ℕ}
    (hi : i < backtrackingIndex f α tini x) : ¬ BacktrackingTest f α tini x i := by
  classical
  by_cases h : ∃ i, BacktrackingTest f α tini x i
  · rw [backtrackingIndex_eq_find h] at hi
    exact Nat.find_min h hi
  · exact fun hi' => h ⟨i, hi'⟩

/-- The backtracking index is at most every index whose trial step satisfies the Armijo test. -/
theorem backtrackingIndex_le_of_test {tini : ℝ} {x : E} {i : ℕ}
    (hi : BacktrackingTest f α tini x i) : backtrackingIndex f α tini x ≤ i :=
  not_lt.1 fun h => not_backtrackingTest_of_lt h hi

/-- If the first trial step $t_{\mathrm{ini}}$ satisfies the Armijo test, the backtracking index is
$0$: no backtracking takes place. -/
theorem backtrackingIndex_eq_zero {tini : ℝ} {x : E} (h : BacktrackingTest f α tini x 0) :
    backtrackingIndex f α tini x = 0 :=
  Nat.le_zero.1 (backtrackingIndex_le_of_test h)

/-- Under the hypotheses of Lemma 2.2.1 of [cartis2022evaluation], with $t_{\mathrm{ini}} > 0$,
every trial step $t_{\mathrm{ini}} 2^{-i} \le 2(1 - \alpha)/L$ satisfies the Armijo test. -/
theorem backtrackingTest_of_le (hf : Differentiable ℝ f)
    (hL : ∀ y z, ‖gradient f y - gradient f z‖ ≤ L * ‖y - z‖) (hL0 : 0 < L) {tini : ℝ}
    (htini : 0 < tini) (x : E) {i : ℕ} (hi : tini * 2⁻¹ ^ i ≤ 2 * (1 - α) / L) :
    BacktrackingTest f α tini x i :=
  armijo_neg_gradient_of_le hf hL hL0 x (by positivity) hi

/-- **Bounds (2.2.6)–(2.2.7)** of [cartis2022evaluation]. Let $f : E \to \mathbb{R}$ be
differentiable on a real Hilbert space $E$, with $\|\nabla f(y) - \nabla f(z)\| \le L \|y - z\|$
for all $y, z$ and $L > 0$. Let $\alpha < 1$, $t_{\mathrm{ini}} > 0$ and $x \in E$, and let $i$
be the backtracking index. Then
$$i \le \left\lceil \log_2 \frac{L t_{\mathrm{ini}}}{2(1 - \alpha)} \right\rceil,$$
and the accepted step $t = t_{\mathrm{ini}} 2^{-i}$ satisfies
$t \ge \min\{t_{\mathrm{ini}}, (1 - \alpha)/L\}$.

The source states (2.2.7) as $t \ge (1 - \alpha)/L$. That bound needs
$t_{\mathrm{ini}} \ge (1 - \alpha)/L$, because the first trial step may already be shorter. The
ceiling is the natural-number ceiling `Nat.ceil`, which is $0$ for a negative argument. -/
theorem backtrackingIndex_le (hf : Differentiable ℝ f)
    (hL : ∀ y z, ‖gradient f y - gradient f z‖ ≤ L * ‖y - z‖) (hL0 : 0 < L) (hα : α < 1)
    {tini : ℝ} (htini : 0 < tini) (x : E) :
    backtrackingIndex f α tini x ≤ ⌈Real.logb 2 (L * tini / (2 * (1 - α)))⌉₊ ∧
      min tini ((1 - α) / L) ≤ tini * 2⁻¹ ^ backtrackingIndex f α tini x := by
  have h1α : 0 < 1 - α := sub_pos.2 hα
  set N := ⌈Real.logb 2 (L * tini / (2 * (1 - α)))⌉₊
  have hpos : 0 < L * tini / (2 * (1 - α)) := by positivity
  have hN : tini * 2⁻¹ ^ N ≤ 2 * (1 - α) / L := by
    have h2N : L * tini / (2 * (1 - α)) ≤ 2 ^ N := by
      rw [← Real.rpow_natCast, ← Real.logb_le_iff_le_rpow (by norm_num) hpos]
      exact Nat.le_ceil _
    rw [div_le_iff₀ (by positivity)] at h2N
    rw [le_div_iff₀ hL0, inv_pow]
    have h2 : (0 : ℝ) < 2 ^ N := by positivity
    calc tini * (2 ^ N)⁻¹ * L = L * tini / 2 ^ N := by ring
      _ ≤ 2 * (1 - α) := by rw [div_le_iff₀ h2]; linarith
  refine ⟨backtrackingIndex_le_of_test (backtrackingTest_of_le hf hL hL0 htini x hN), ?_⟩
  rcases Nat.eq_zero_or_pos (backtrackingIndex f α tini x) with h0 | hpos'
  · rw [h0]
    simp
  · obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_lt hpos'
    rw [zero_add] at hj
    have hfail : ¬ BacktrackingTest f α tini x j :=
      not_backtrackingTest_of_lt (by omega)
    have hlt : 2 * (1 - α) / L < tini * 2⁻¹ ^ j :=
      not_le.1 fun h => hfail (backtrackingTest_of_le hf hL hL0 htini x h)
    refine min_le_of_right_le ?_
    rw [hj, pow_succ]
    have : (1 - α) / L = 2 * (1 - α) / L * 2⁻¹ := by ring
    rw [this, ← mul_assoc]
    exact (mul_le_mul_iff_left₀ (by norm_num)).2 hlt.le

/-! ### Exact line searches -/

/-- A number $t \ge 0$ is a **global line minimizer** if it minimizes
$\tau \mapsto f(x - \tau \nabla f(x))$ on $[0, \infty)$. -/
def IsGlobalLineMin (f : E → ℝ) (x : E) (t : ℝ) : Prop :=
  0 ≤ t ∧ ∀ τ : ℝ, 0 ≤ τ → f (x - t • gradient f x) ≤ f (x - τ • gradient f x)

/-- The **exact line search** (2.2.26) of [cartis2022evaluation]: $t \ge 0$ is the first global
minimizer of $\tau \mapsto f(x - \tau \nabla f(x))$ on $[0, \infty)$. That is, $t$ is a global
line minimizer, and $f(x - t \nabla f(x)) < f(x - \tau \nabla f(x))$ for every
$\tau \in [0, t)$. -/
def IsExactLineMin (f : E → ℝ) (x : E) (t : ℝ) : Prop :=
  IsGlobalLineMin f x t ∧ ∀ τ ∈ Ico 0 t, f (x - t • gradient f x) < f (x - τ • gradient f x)

/-- An exact line-search step is a global line minimizer. -/
theorem IsExactLineMin.isGlobalLineMin {x : E} {t : ℝ} (h : IsExactLineMin f x t) :
    IsGlobalLineMin f x t :=
  h.1

/-- The exact line-search step (2.2.26) of [cartis2022evaluation] is unique: if $t$ and $t'$ are
both first global minimizers of $\tau \mapsto f(x - \tau \nabla f(x))$ on $[0, \infty)$, then
$t = t'$. -/
theorem IsExactLineMin.unique {x : E} {t t' : ℝ} (h : IsExactLineMin f x t)
    (h' : IsExactLineMin f x t') : t = t' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := h'.2 t ⟨h.1.1, hlt⟩
    linarith [h.1.2 t' h'.1.1]
  · have := h.2 t' ⟨h'.1.1, hlt⟩
    linarith [h'.1.2 t h.1.1]

/-- **The exact line search (2.2.26) of [cartis2022evaluation] is well defined.** Let
$f : E \to \mathbb{R}$ be continuous on a real Hilbert space $E$, and let the sublevel set
$\{y : f(y) \le f(x)\}$ be bounded. Then a first global minimizer of
$t \mapsto f(x - t \nabla f(x))$ on $t \ge 0$ exists. -/
theorem exists_isExactLineMin (hf : Continuous f) {x : E}
    (hbdd : Bornology.IsBounded {y | f y ≤ f x}) : ∃ t, IsExactLineMin f x t := by
  set g := gradient f x
  rcases eq_or_ne g 0 with hg | hg
  · refine ⟨0, ⟨⟨le_rfl, fun τ _ => by simp [g, hg]⟩, fun τ hτ => ?_⟩⟩
    exact absurd hτ.2 (not_lt.2 hτ.1)
  have hgpos : 0 < ‖g‖ := norm_pos_iff.2 hg
  set φ : ℝ → ℝ := fun t => f (x - t • g)
  have hφ : Continuous φ := hf.comp (continuous_const.sub (continuous_id.smul continuous_const))
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : E)).1 hbdd
  set T : Set ℝ := {t | 0 ≤ t ∧ φ t ≤ f x}
  have hTsub : T ⊆ Icc 0 ((R + ‖x‖) / ‖g‖) := by
    intro t ⟨ht0, ht⟩
    refine ⟨ht0, ?_⟩
    have hmem := hR (show x - t • g ∈ {y | f y ≤ f x} from ht)
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    rw [le_div_iff₀ hgpos]
    have : ‖t • g‖ ≤ ‖x - t • g‖ + ‖x‖ := by
      have := norm_sub_le x (x - t • g)
      rw [sub_sub_cancel] at this
      linarith
    rw [norm_smul, Real.norm_of_nonneg ht0] at this
    linarith
  have hTclosed : IsClosed T := isClosed_Ici.inter (isClosed_le hφ continuous_const)
  have hTcpt : IsCompact T := isCompact_Icc.of_isClosed_subset hTclosed hTsub
  have h0T : (0 : ℝ) ∈ T := ⟨le_rfl, by simp [φ]⟩
  obtain ⟨t₀, ht₀, hmin⟩ := hTcpt.exists_isMinOn ⟨0, h0T⟩ hφ.continuousOn
  have hm0 : φ t₀ ≤ f x := by simpa [φ] using hmin h0T
  set M : Set ℝ := {t | 0 ≤ t ∧ φ t ≤ φ t₀}
  have hMsub : M ⊆ T := fun t ht => ⟨ht.1, ht.2.trans hm0⟩
  have hMcpt : IsCompact M :=
    hTcpt.of_isClosed_subset (isClosed_Ici.inter (isClosed_le hφ continuous_const)) hMsub
  obtain ⟨t, htM, hleast⟩ := hMcpt.exists_isLeast ⟨t₀, ht₀.1, le_rfl⟩
  have hglob : ∀ τ, 0 ≤ τ → φ t ≤ φ τ := fun τ hτ => by
    by_cases hτT : τ ∈ T
    · exact htM.2.trans (hmin hτT)
    · have : f x < φ τ := not_le.1 fun h' => hτT ⟨hτ, h'⟩
      linarith [htM.2]
  refine ⟨t, ⟨htM.1, hglob⟩, fun τ hτ => lt_of_le_of_ne (hglob τ hτ.1) fun heq => ?_⟩
  have : φ τ ≤ φ t₀ := by
    have h2 : φ t = φ τ := heq
    rw [← h2]; exact htM.2
  exact absurd (hleast ⟨hτ.1, this⟩) (not_le.2 hτ.2)

/-- The **first-local-minimizer line search**: $t > 0$ is the first stationary point of
$\varphi(\tau) = f(x - \tau \nabla f(x))$ on $[0, \infty)$, and $\varphi$ has negative slope
before it. That is, $\langle \nabla f(x - t \nabla f(x)), \nabla f(x)\rangle = 0$, and $\langle
\nabla f(x - \tau \nabla f(x)), \nabla f(x)\rangle > 0$ for every $\tau \in [0, t)$. The slope
of $\varphi$ is $\varphi'(\tau) = -\langle \nabla f(x - \tau \nabla f(x)), \nabla f(x)\rangle$.

The iterates of the sharpness example of Theorem 2.2.5 of [cartis2022evaluation] (Lemma B.2.6)
have this property. -/
def IsFirstLocalLineMin (f : E → ℝ) (x : E) (t : ℝ) : Prop :=
  0 < t ∧ ⟪gradient f (x - t • gradient f x), gradient f x⟫ = 0 ∧
    ∀ τ ∈ Ico 0 t, 0 < ⟪gradient f (x - τ • gradient f x), gradient f x⟫

/-- If $f$ is differentiable, then $\varphi(\tau) = f(x - \tau \nabla f(x))$ has the derivative
$\varphi'(\tau) = -\langle \nabla f(x - \tau \nabla f(x)), \nabla f(x)\rangle$. -/
theorem hasDerivAt_lineFun (hf : Differentiable ℝ f) (x : E) (τ : ℝ) :
    HasDerivAt (fun τ : ℝ => f (x - τ • gradient f x))
      (-⟪gradient f (x - τ • gradient f x), gradient f x⟫) τ := by
  have hl : HasDerivAt (fun τ : ℝ => x - τ • gradient f x) (-gradient f x) τ := by
    simpa using ((hasDerivAt_id τ).smul_const (gradient f x)).const_sub x
  have h := (hf (x - τ • gradient f x)).hasFDerivAt.comp_hasDerivAt τ hl
  rwa [map_neg, fderiv_apply_eq_inner_gradient] at h

/-- Let $f$ be differentiable with $\nabla f(x) \neq 0$. Then a global line minimizer $t$ is
positive and stationary: $t > 0$ and $\langle \nabla f(x - t \nabla f(x)), \nabla f(x)\rangle =
0$. -/
theorem IsGlobalLineMin.pos_and_inner_eq_zero (hf : Differentiable ℝ f) {x : E} {t : ℝ}
    (h : IsGlobalLineMin f x t) (hg : gradient f x ≠ 0) :
    0 < t ∧ ⟪gradient f (x - t • gradient f x), gradient f x⟫ = 0 := by
  have hpos : 0 < t := by
    rcases h.1.lt_or_eq with ht | ht
    · exact ht
    · -- at `t = 0` the slope `-‖∇f(x)‖²` is negative, so `0` is not a minimizer on `[0, ∞)`
      exfalso
      have hd := hasDerivAt_lineFun hf x 0
      simp only [zero_smul, sub_zero, real_inner_self_eq_norm_sq] at hd
      have hneg : -‖gradient f x‖ ^ 2 < 0 := by
        have := norm_pos_iff.2 hg
        nlinarith
      have hlim := hd.tendsto_slope_zero_right
      have hev : ∀ᶠ τ in nhdsWithin (0 : ℝ) (Ioi 0),
          0 ≤ τ⁻¹ • (f (x - (0 + τ) • gradient f x) - f (x - (0 : ℝ) • gradient f x)) := by
        filter_upwards [self_mem_nhdsWithin] with τ hτ
        have hmin := h.2 τ (le_of_lt hτ)
        rw [← ht] at hmin
        simp only [zero_add, smul_eq_mul]
        exact mul_nonneg (inv_nonneg.2 (le_of_lt hτ)) (sub_nonneg.2 hmin)
      have := ge_of_tendsto hlim hev
      linarith
  refine ⟨hpos, ?_⟩
  have hmin : IsLocalMin (fun τ : ℝ => f (x - τ • gradient f x)) t :=
    Filter.mem_of_superset (Ioi_mem_nhds hpos) fun τ hτ => h.2 τ (le_of_lt hτ)
  have := hmin.hasDerivAt_eq_zero (hasDerivAt_lineFun hf x t)
  linarith

/-- Let $\nabla f$ be $L$-Lipschitz with $L > 0$, and let $\nabla f(x) \neq 0$. If $t \ge 0$ is a
stationary step, $\langle \nabla f(x - t \nabla f(x)), \nabla f(x)\rangle = 0$, then
$t \ge 1/L$.

This follows from $0 = \langle \nabla f(x - t \nabla f(x)), \nabla f(x)\rangle \ge \|\nabla
f(x)\|^2 (1 - Lt)$. -/
theorem one_div_le_of_inner_eq_zero (hL : ∀ y z, ‖gradient f y - gradient f z‖ ≤ L * ‖y - z‖)
    (hL0 : 0 < L) {x : E} (hg : gradient f x ≠ 0) {t : ℝ} (ht : 0 ≤ t)
    (h0 : ⟪gradient f (x - t • gradient f x), gradient f x⟫ = 0) : 1 / L ≤ t := by
  set g := gradient f x
  have hng : 0 < ‖g‖ := norm_pos_iff.2 hg
  have hd := hL (x - t • g) x
  rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] at hd
  have hcs := real_inner_le_norm (g - gradient f (x - t • g)) g
  have hexp : ⟪g - gradient f (x - t • g), g⟫ = ‖g‖ ^ 2 := by
    rw [inner_sub_left, h0, real_inner_self_eq_norm_sq, sub_zero]
  rw [hexp, norm_sub_rev] at hcs
  have : 1 * ‖g‖ ^ 2 ≤ (L * t) * ‖g‖ ^ 2 := by nlinarith
  have h1 := le_of_mul_le_mul_right this (by positivity)
  rw [div_le_iff₀ hL0]
  linarith

/-- The decrease at the step $1/L$, (2.2.28) of [cartis2022evaluation]: if $f$ is differentiable
with $L$-Lipschitz gradient and $L > 0$, then
$$f(x - \nabla f(x)/L) \le f(x) - \frac{\|\nabla f(x)\|^2}{2L}.$$
-/
theorem le_sub_of_step_inv (hf : Differentiable ℝ f)
    (hL : ∀ y z, ‖gradient f y - gradient f z‖ ≤ L * ‖y - z‖) (hL0 : 0 < L) (x : E) :
    f (x - (1 / L) • gradient f x) ≤ f x - ‖gradient f x‖ ^ 2 / (2 * L) := by
  have h := le_add_inner_add_of_lipschitz_gradient hf hL x (-((1 / L) • gradient f x))
  rw [← sub_eq_add_neg, inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq,
    norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)] at h
  have : f x + -(1 / L * ‖gradient f x‖ ^ 2) + L / 2 * (1 / L * ‖gradient f x‖) ^ 2 =
      f x - ‖gradient f x‖ ^ 2 / (2 * L) := by
    field_simp
    ring
  linarith

/-- **Theorem 2.2.4** of [cartis2022evaluation], core of the proof. Let $f : E \to \mathbb{R}$ be
differentiable on a real Hilbert space $E$, with $\|\nabla f(y) - \nabla f(z)\| \le L \|y - z\|$
for all $y, z$ and $L > 0$, and let $\nabla f(x) \neq 0$. Let $t$ be a global line minimizer
(`LineSearch.IsGlobalLineMin`, for example the exact line search (2.2.26)
`LineSearch.IsExactLineMin`) or a first-local-minimizer step (`LineSearch.IsFirstLocalLineMin`).
Then $t \ge 1/L$ and
$$f(x) - f(x - t \nabla f(x)) \ge \frac{\|\nabla f(x)\|^2}{2L}.$$
-/
theorem decrease_ge_of_exactLineMin (hf : Differentiable ℝ f)
    (hL : ∀ y z, ‖gradient f y - gradient f z‖ ≤ L * ‖y - z‖) (hL0 : 0 < L) {x : E}
    (hg : gradient f x ≠ 0) {t : ℝ} (ht : IsGlobalLineMin f x t ∨ IsFirstLocalLineMin f x t) :
    1 / L ≤ t ∧ ‖gradient f x‖ ^ 2 / (2 * L) ≤ f x - f (x - t • gradient f x) := by
  have hstep := le_sub_of_step_inv hf hL hL0 x
  rcases ht with ht | ht
  · obtain ⟨hpos, h0⟩ := ht.pos_and_inner_eq_zero hf hg
    refine ⟨one_div_le_of_inner_eq_zero hL hL0 hg hpos.le h0, ?_⟩
    have := ht.2 (1 / L) (by positivity)
    linarith
  · have h1L := one_div_le_of_inner_eq_zero hL hL0 hg ht.1.le ht.2.1
    refine ⟨h1L, ?_⟩
    -- `φ` is antitone on `[0, t]`, hence `φ t ≤ φ (1/L)`
    have hanti : AntitoneOn (fun τ : ℝ => f (x - τ • gradient f x)) (Icc 0 t) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 0 t) ?_ ?_ ?_
      · exact fun τ _ => (hasDerivAt_lineFun hf x τ).continuousAt.continuousWithinAt
      · exact fun τ _ => (hasDerivAt_lineFun hf x τ).differentiableAt.differentiableWithinAt
      · intro τ hτ
        rw [interior_Icc] at hτ
        rw [(hasDerivAt_lineFun hf x τ).deriv]
        exact (neg_neg_of_pos (ht.2.2 τ ⟨hτ.1.le, hτ.2⟩)).le
    have := hanti ⟨by positivity, h1L⟩ ⟨ht.1.le, le_rfl⟩ h1L
    simp only at this
    linarith

end LineSearch

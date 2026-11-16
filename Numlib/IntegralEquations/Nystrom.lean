/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.MeasureTheory.Integral.Prod
import Numlib.Analysis.Normed.Operator.CollectivelyCompact
import Numlib.Approximation.Quadrature
import Numlib.IntegralEquations.Basic

/-!
# Nyström operators

Let $X$ be a compact space with a finite Borel measure $\mu$, and let $k$ be a continuous real
kernel on $X \times X$. A quadrature rule with weights $w_1, \dots, w_m$ and nodes
$x_1, \dots, x_m \in X$ gives the **Nyström operator**
$$(K_n u)(t) = \sum_j w_j \, k(t, x_j) \, u(x_j)$$
on $C(X)$. It is the integral operator $(Ku)(t) = \int k(t, y) u(y) \, d\mu(y)$ of
`IntegralOperator.kernelCLM` with the integral replaced by the rule. The Nyström operator has finite
rank. For a sequence of rules with uniformly bounded sums of absolute weights, the Nyström operators
form a collectively compact family. If the rules converge, the family converges pointwise to $K$,
but in general not in operator norm. Anselone's theory of collectively compact operators
[anselone1971collectively] is made for this situation. The presentation follows
[han2009theoretical], §12.4 (Lemma 12.4.2 and Theorem 12.4.4); see also [kress1989linear], §12.2.

## Main definitions

* `IntegralOperator.integralCLM`: integration against $\mu$, as a bounded linear functional on
  $C(X)$.
* `IntegralOperator.nystromCLM`: the Nyström operator $K_n$ of a quadrature rule and a kernel.
* `IntegralOperator.compKernel`: the kernel $e(t, s) = \int k(t, v) k(v, s) \, d\mu(v) - \sum_j w_j
  k(t, x_j) k(x_j, s)$, the quadrature error for the composed kernel.

## Main results

* `IntegralOperator.norm_nystromCLM`: $\|K_n\| = \max_t \sum_j |w_j k(t, x_j)|$ for distinct nodes.
* `IntegralOperator.tendsto_norm_of_tendsto_functional`: pointwise convergence of functionals on
  $C(X)$ is uniform along a continuous family of integrands.
* `IntegralOperator.tendsto_nystromCLM`: for a convergent sequence of quadrature rules,
  $K_n u \to K u$ in $C(X)$ for every $u$.
* `IntegralOperator.isCollectivelyCompact_nystromCLM`: uniformly bounded sums of absolute weights
  make the Nyström family collectively compact.
* `IntegralOperator.kernelCLM_sub_nystromCLM_comp_kernelCLM` and
  `IntegralOperator.kernelCLM_sub_nystromCLM_comp_nystromCLM`: $(K - K_n) K$ is the integral
  operator of $e$, and $(K - K_n) K_n$ is the Nyström operator of $e$.
* `IntegralOperator.tendsto_norm_compKernel`: for a convergent sequence of quadrature rules,
  $\|e\| \to 0$.

## Proof outline

For a fixed $t$, both $(Ku)(t)$ and $(K_n u)(t)$ are bounded linear functionals evaluated at the
same integrand $y \mapsto k(t, y) u(y)$ in $C(X)$ (`IntegralOperator.rowMul`). This integrand
depends continuously on $t$, so it takes values in a compact subset of $C(X)$. On a compact set, a
pointwise convergent sequence of bounded functionals converges uniformly
(`tendstoUniformlyOn_of_tendsto_of_isCompact`). This one argument gives the convergence
$K_n u \to K u$ in the uniform norm, and the uniform convergence $\|e\| \to 0$ of the composed
kernels.
-/

open Filter MeasureTheory Metric Set Topology

namespace IntegralOperator

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-! ### Rows and columns of a kernel -/

/-- The **row** $y \mapsto k(t, y)$ of a continuous kernel $k$ on $X \times X$, as a continuous map
from the row index $t \in X$ to $C(X)$. -/
noncomputable def row (k : C(X × X, ℝ)) : C(X, C(X, ℝ)) := k.curry

omit [CompactSpace X] in
/-- The row of $k$ at $t$, evaluated at $s$, is $k(t, s)$. -/
@[simp]
theorem row_apply (k : C(X × X, ℝ)) (t s : X) : row k t s = k (t, s) := rfl

/-- The **column** $t \mapsto k(t, s)$ of a continuous kernel $k$ on $X \times X$, as an element of
$C(X)$. -/
def col (k : C(X × X, ℝ)) (s : X) : C(X, ℝ) :=
  ⟨fun t => k (t, s), by fun_prop⟩

omit [CompactSpace X] in
/-- The column of $k$ at $s$, evaluated at $t$, is $k(t, s)$. -/
@[simp]
theorem col_apply (k : C(X × X, ℝ)) (s t : X) : col k s t = k (t, s) := rfl

/-- For a continuous kernel $k$ and $u \in C(X)$, the integrand $y \mapsto k(t, y) u(y)$ of a kernel
operator, as a continuous map from the row index $t \in X$ to $C(X)$. The integral operator and
its Nyström approximation are both a bounded functional applied to this integrand. -/
noncomputable def rowMul (k : C(X × X, ℝ)) (u : C(X, ℝ)) : C(X, C(X, ℝ)) :=
  ContinuousMap.curry ⟨fun p => k p * u p.2, by fun_prop⟩

omit [CompactSpace X] in
/-- The integrand `IntegralOperator.rowMul k u` at $t$, evaluated at $s$, is $k(t, s) u(s)$. -/
@[simp]
theorem rowMul_apply (k : C(X × X, ℝ)) (u : C(X, ℝ)) (t s : X) :
    rowMul k u t s = k (t, s) * u s := rfl

/-- For a continuous kernel $k$, the integrand $v \mapsto k(t, v) k(v, s)$ of the composed kernel,
as a continuous map from the pair $(t, s) \in X \times X$ to $C(X)$. -/
noncomputable def rowCol (k : C(X × X, ℝ)) : C(X × X, C(X, ℝ)) :=
  ContinuousMap.curry ⟨fun p : (X × X) × X => k (p.1.1, p.2) * k (p.2, p.1.2), by fun_prop⟩

omit [CompactSpace X] in
/-- The integrand `IntegralOperator.rowCol k` at $(t, s)$, evaluated at $v$, is $k(t, v) k(v, s)$.
-/
@[simp]
theorem rowCol_apply (k : C(X × X, ℝ)) (p : X × X) (v : X) :
    rowCol k p v = k (p.1, v) * k (v, p.2) := rfl

/-! ### Integration as a functional -/

section Integral

variable [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]

/-- Let $X$ be a compact space with a finite Borel measure $\mu$. **Integration against $\mu$** is
the bounded linear functional
$$u \mapsto \int u(y) \, d\mu(y)$$
on $C(X)$. A quadrature rule (`Quadrature.functional`) is an approximation of this functional.

The functional is built with the bound $\mu(X)$, so its norm is at most $\mu(X)$. -/
noncomputable def integralCLM : C(X, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun u => ∫ y, u y ∂μ
      map_add' := fun u v => by
        simp only [ContinuousMap.add_apply]
        exact integral_add (integrable_of_continuousMap μ u) (integrable_of_continuousMap μ v)
      map_smul' := fun r u => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        exact integral_const_mul r _ }
    (μ.real univ) fun u => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      calc ‖∫ y, u y ∂μ‖
          ≤ ‖u‖ * μ.real univ :=
            norm_integral_le_of_norm_le_const
              (Filter.Eventually.of_forall fun y => u.norm_coe_le_norm y)
        _ = μ.real univ * ‖u‖ := mul_comm _ _

/-- `IntegralOperator.integralCLM μ u` is the integral $\int u \, d\mu$. -/
@[simp]
theorem integralCLM_apply (u : C(X, ℝ)) : integralCLM μ u = ∫ y, u y ∂μ := rfl

/-- A continuous real function on a compact space is integrable for every finite measure. This is
the form of `IntegralOperator.integrable_of_continuousMap` for an unbundled function. -/
theorem integrable_of_continuous {f : X → ℝ} (hf : Continuous f) : Integrable f μ :=
  integrable_of_continuousMap μ ⟨f, hf⟩

/-- The kernel operator of $k$ at the point $t$ is integration against $\mu$ applied to the
integrand $y \mapsto k(t, y) u(y)$:
$$(Ku)(t) = \int k(t, y) u(y) \, d\mu(y).$$
-/
theorem kernelCLM_apply_eq_integralCLM (k : C(X × X, ℝ)) (u : C(X, ℝ)) (t : X) :
    kernelCLM μ k u t = integralCLM μ (rowMul k u t) := rfl

/-- The kernel operator of $-k$ is the negative of the kernel operator of $k$. -/
@[simp]
theorem kernelCLM_neg (k : C(X × X, ℝ)) : kernelCLM μ (-k) = -kernelCLM μ k := by
  refine ContinuousLinearMap.ext fun u => ContinuousMap.ext fun t => ?_
  rw [neg_apply, ContinuousMap.neg_apply, kernelCLM_apply, kernelCLM_apply, ← integral_neg]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => by simp)

end Integral

/-! ### The Nyström operator -/

section Nystrom

variable {m : ℕ} {w : Fin m → ℝ} {x : Fin m → X} {k : C(X × X, ℝ)}

/-- Let $X$ be a compact space, let $k$ be a continuous real kernel on $X \times X$, and let a
quadrature rule have weights $w_1, \dots, w_m \in \mathbb{R}$ and nodes $x_1, \dots, x_m \in X$.
The **Nyström operator** is the bounded linear operator on $C(X)$ given by
$$(K_n u)(t) = \sum_{j=1}^m w_j \, k(t, x_j) \, u(x_j).$$
This is (12.4.4) of [han2009theoretical]. It is the kernel operator `IntegralOperator.kernelCLM`
with the integral replaced by the quadrature rule.

The operator is the sum over $j$ of the rank-one operators
$u \mapsto w_j u(x_j) \, k(\cdot, x_j)$, so it has finite rank. -/
noncomputable def nystromCLM {m : ℕ} (w : Fin m → ℝ) (x : Fin m → X) (k : C(X × X, ℝ)) :
    C(X, ℝ) →L[ℝ] C(X, ℝ) :=
  ∑ j, (w j • ContinuousMap.evalCLM ℝ (x j)).smulRight (col k (x j))

/-- The Nyström operator of the weights $w$, the nodes $x$ and the kernel $k$ maps $u$ to
$t \mapsto \sum_j w_j \, k(t, x_j) \, u(x_j)$. -/
@[simp]
theorem nystromCLM_apply (w : Fin m → ℝ) (x : Fin m → X) (k : C(X × X, ℝ)) (u : C(X, ℝ)) (t : X) :
    nystromCLM w x k u t = ∑ j, w j * k (t, x j) * u (x j) := by
  simp only [nystromCLM, sum_apply, ContinuousMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, smul_apply,
    ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply, smul_eq_mul, col_apply]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The Nyström operator of $-k$ is the negative of the Nyström operator of $k$. -/
@[simp]
theorem nystromCLM_neg (w : Fin m → ℝ) (x : Fin m → X) (k : C(X × X, ℝ)) :
    nystromCLM w x (-k) = -nystromCLM w x k := by
  refine ContinuousLinearMap.ext fun u => ContinuousMap.ext fun t => ?_
  rw [neg_apply, ContinuousMap.neg_apply, nystromCLM_apply, nystromCLM_apply,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by simp

/-- The Nyström operator at the point $t$ is the quadrature rule applied to the integrand
$y \mapsto k(t, y) u(y)$, in the same way as the kernel operator at $t$ is the integral of this
integrand. -/
theorem nystromCLM_apply_eq_functional (w : Fin m → ℝ) (x : Fin m → X) (k : C(X × X, ℝ))
    (u : C(X, ℝ)) (t : X) :
    nystromCLM w x k u t = Quadrature.functional w x (rowMul k u t) := by
  rw [Quadrature.functional_apply, nystromCLM_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [rowMul_apply, mul_assoc]

/-- Let $C \ge 0$. If $\sum_j |w_j \, k(t, x_j)| \le C$ for every $t \in X$, then the Nyström
operator has norm at most $C$. This is the easy half of `IntegralOperator.norm_nystromCLM`. -/
theorem norm_nystromCLM_le {C : ℝ} (hC : 0 ≤ C) (h : ∀ t, ∑ j, |w j * k (t, x j)| ≤ C) :
    ‖nystromCLM w x k‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun u => ?_
  rw [ContinuousMap.norm_le _ (mul_nonneg hC (norm_nonneg u))]
  intro t
  rw [nystromCLM_apply, Real.norm_eq_abs]
  calc |∑ j, w j * k (t, x j) * u (x j)|
      ≤ ∑ j, |w j * k (t, x j) * u (x j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |w j * k (t, x j)| * ‖u‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (u.norm_coe_le_norm _) (abs_nonneg _)
    _ = (∑ j, |w j * k (t, x j)|) * ‖u‖ := by rw [Finset.sum_mul]
    _ ≤ C * ‖u‖ := mul_le_mul_of_nonneg_right (h t) (norm_nonneg u)

/-- Let $X$ be a nonempty compact Hausdorff space, let $k$ be a continuous real kernel on
$X \times X$, and let the quadrature rule have weights $w_1, \dots, w_m$ and distinct nodes
$x_1, \dots, x_m$. Then the Nyström operator $K_n$ has the norm
$$\|K_n\| = \max_{t \in X} \sum_{j=1}^m |w_j \, k(t, x_j)|.$$
This is (12.4.17) of [han2009theoretical], and it is the analogue of
`IntegralOperator.norm_kernelCLM` for a quadrature rule in place of an integral.

The maximum is the supremum `⨆ t`. For the lower bound, take $t_0$ where the sum is largest and
apply `Quadrature.norm_functional` to the rule with weights $w_j k(t_0, x_j)$. This rule is the
Nyström operator evaluated at $t_0$, so its norm is at most $\|K_n\|$. The nodes must be
distinct for `Quadrature.norm_functional`. -/
theorem norm_nystromCLM [T2Space X] [Nonempty X] (hx : Function.Injective x) :
    ‖nystromCLM w x k‖ = ⨆ t, ∑ j, |w j * k (t, x j)| := by
  set g : C(X, ℝ) :=
    ⟨fun t => ∑ j, |w j * k (t, x j)|, by fun_prop⟩ with hg
  have hgapp : ∀ t, g t = ∑ j, |w j * k (t, x j)| := fun _ => rfl
  have hgnonneg : ∀ t, 0 ≤ g t := fun t => by
    rw [hgapp]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨t₀, -, ht₀⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty g.continuous.continuousOn
  have hmax : ∀ t, g t ≤ g t₀ := fun t => isMaxOn_iff.1 ht₀ t (mem_univ t)
  have hsup : ⨆ t, ∑ j, |w j * k (t, x j)| = g t₀ :=
    le_antisymm (ciSup_le hmax) (le_ciSup ⟨g t₀, by rintro _ ⟨t, rfl⟩; exact hmax t⟩ t₀)
  rw [hsup]
  refine le_antisymm (norm_nystromCLM_le (hgnonneg t₀) hmax) ?_
  -- the rule with weights `w j * k (t₀, x j)` is the Nyström operator read off at `t₀`
  have hrow : ‖Quadrature.functional (fun j => w j * k (t₀, x j)) x‖ ≤ ‖nystromCLM w x k‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun u => ?_
    have hval : Quadrature.functional (fun j => w j * k (t₀, x j)) x u
        = nystromCLM w x k u t₀ := by
      rw [Quadrature.functional_apply, nystromCLM_apply]
    rw [hval, Real.norm_eq_abs, ← Real.norm_eq_abs]
    calc ‖nystromCLM w x k u t₀‖ ≤ ‖nystromCLM w x k u‖ :=
          (nystromCLM w x k u).norm_coe_le_norm t₀
      _ ≤ ‖nystromCLM w x k‖ * ‖u‖ := (nystromCLM w x k).le_opNorm u
  rwa [Quadrature.norm_functional _ hx, ← hgapp] at hrow

end Nystrom

/-! ### Uniform convergence along a continuous family of integrands -/

/-- Let $X$ and $Y$ be compact spaces, let $A_n$ and $L$ be bounded linear functionals on $C(X)$
with $A_n v \to L v$ for every $v \in C(X)$, and let $F \colon Y \to C(X)$ be continuous. Let
$g_n \in C(Y)$ be the functions $g_n(y) = L(F(y)) - A_n(F(y))$. Then
$$\sup_{y \in Y} |L(F(y)) - A_n(F(y))| = \|g_n\| \to 0.$$

The range of $F$ is a compact subset of $C(X)$, and a pointwise convergent sequence of bounded
operators converges uniformly on compact sets (`tendstoUniformlyOn_of_tendsto_of_isCompact`).
This is the only analytic step of the Nyström theory in this module. -/
theorem tendsto_norm_of_tendsto_functional {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    {A : ℕ → C(X, ℝ) →L[ℝ] ℝ} {L : C(X, ℝ) →L[ℝ] ℝ}
    (hA : ∀ v, Tendsto (fun n => A n v) atTop (𝓝 (L v))) (F : C(Y, C(X, ℝ)))
    {g : ℕ → C(Y, ℝ)} (hg : ∀ n y, g n y = L (F y) - A n (F y)) :
    Tendsto (fun n => ‖g n‖) atTop (𝓝 0) := by
  have hS : IsCompact (Set.range F) := isCompact_range (map_continuous F)
  have hunif : TendstoUniformlyOn (fun n => (A n : C(X, ℝ) → ℝ)) L atTop (Set.range F) :=
    tendstoUniformlyOn_of_tendsto_of_isCompact hA hS
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hunif (ε / 2) (by positivity))
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  have hle : ‖g n‖ ≤ ε / 2 := by
    rw [ContinuousMap.norm_le _ (by positivity)]
    intro y
    rw [hg n y, Real.norm_eq_abs, ← Real.dist_eq]
    exact (hN n hn (F y) ⟨y, rfl⟩).le
  linarith

/-! ### The Nyström family of a sequence of quadrature rules -/

section Family

variable [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
  {m : ℕ → ℕ} {w : ∀ n, Fin (m n) → ℝ} {x : ∀ n, Fin (m n) → X} {k : C(X × X, ℝ)}

/-- Let $X$ be a compact space with a finite Borel measure $\mu$, let $k$ be a continuous real
kernel on $X \times X$, and let a sequence of quadrature rules with weights $w^{(n)}$ and nodes
$x^{(n)}$ converge: $\sum_j w^{(n)}_j v(x^{(n)}_j) \to \int v \, d\mu$ for every $v \in C(X)$.
Then for every $u \in C(X)$, the Nyström operators satisfy
$$K_n u \to K u \quad \text{in } C(X),$$
that is, uniformly on $X$.

This is assumption A2 of the theory of collectively compact operators ([han2009theoretical],
§12.4.1). In general $K_n$ does not converge to $K$ in operator norm. -/
theorem tendsto_nystromCLM
    (hQ : ∀ v : C(X, ℝ), Tendsto (fun n => Quadrature.functional (w n) (x n) v) atTop
      (𝓝 (integralCLM μ v))) (u : C(X, ℝ)) :
    Tendsto (fun n => nystromCLM (w n) (x n) k u) atTop (𝓝 (kernelCLM μ k u)) := by
  have hg : ∀ n t, (kernelCLM μ k u - nystromCLM (w n) (x n) k u) t
      = integralCLM μ (rowMul k u t) - Quadrature.functional (w n) (x n) (rowMul k u t) := by
    intro n t
    rw [ContinuousMap.sub_apply, kernelCLM_apply_eq_integralCLM,
      nystromCLM_apply_eq_functional]
  have h := tendsto_norm_of_tendsto_functional hQ (rowMul k u) hg
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [norm_sub_rev] using h

omit [MeasurableSpace X] [BorelSpace X] in
/-- Let $X$ be a compact space, let $k$ be a continuous real kernel on $X \times X$, and let
$(w^{(n)}, x^{(n)})$ be a sequence of quadrature rules with $\sum_j |w^{(n)}_j| \le W$ for every
$n$. Then the sequence of Nyström operators of these rules and $k$ is collectively compact.

This is assumption A3 of the theory of collectively compact operators, and the hypothesis on the
weights is (12.4.3) of [han2009theoretical], §12.4.1.

The images of the closed unit ball are uniformly bounded by $W \|k\|$. They are equicontinuous,
because the difference of $K_n u$ at two points $t, t'$ is at most $W \|u\|$ times the uniform
distance between the rows $k(t, \cdot)$ and $k(t', \cdot)$. The Arzelà–Ascoli theorem then gives
compactness. -/
theorem isCollectivelyCompact_nystromCLM (k : C(X × X, ℝ)) {W : ℝ}
    (hW : ∀ n, ∑ j, |w n j| ≤ W) :
    IsCollectivelyCompact (fun n => nystromCLM (w n) (x n) k) := by
  refine ⟨closedBall 0 1, closedBall_mem_nhds 0 one_pos, ?_⟩
  -- the pointwise bound `|K_n u t| ≤ W ‖k‖`, uniform in `n`, `u` and `t`
  have hbdd : ∀ n (u : C(X, ℝ)), ‖u‖ ≤ 1 → ∀ t s : X,
      |nystromCLM (w n) (x n) k u t - nystromCLM (w n) (x n) k u s|
        ≤ W * ‖row k t - row k s‖ := by
    intro n u hu t s
    have hstep : ∀ j, |w n j * k (t, x n j) * u (x n j) - w n j * k (s, x n j) * u (x n j)|
        ≤ |w n j| * ‖row k t - row k s‖ := by
      intro j
      have h1 : |k (t, x n j) - k (s, x n j)| ≤ ‖row k t - row k s‖ := by
        have := (row k t - row k s).norm_coe_le_norm (x n j)
        simpa [Real.norm_eq_abs] using this
      have h2 : |u (x n j)| ≤ 1 := le_trans (by simpa using u.norm_coe_le_norm (x n j)) hu
      have hrw : w n j * k (t, x n j) * u (x n j) - w n j * k (s, x n j) * u (x n j)
          = w n j * ((k (t, x n j) - k (s, x n j)) * u (x n j)) := by ring
      rw [hrw, abs_mul, abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      calc |k (t, x n j) - k (s, x n j)| * |u (x n j)|
          ≤ ‖row k t - row k s‖ * 1 := by
            refine mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
        _ = ‖row k t - row k s‖ := mul_one _
    rw [nystromCLM_apply, nystromCLM_apply, ← Finset.sum_sub_distrib]
    calc |∑ j, (w n j * k (t, x n j) * u (x n j) - w n j * k (s, x n j) * u (x n j))|
        ≤ ∑ j, |w n j * k (t, x n j) * u (x n j) - w n j * k (s, x n j) * u (x n j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |w n j| * ‖row k t - row k s‖ := Finset.sum_le_sum fun j _ => hstep j
      _ = (∑ j, |w n j|) * ‖row k t - row k s‖ := by rw [Finset.sum_mul]
      _ ≤ W * ‖row k t - row k s‖ :=
          mul_le_mul_of_nonneg_right (hW n) (norm_nonneg _)
  refine ContinuousMap.isCompact_closure_of_forall_norm_le (M := W * ‖k‖) ?_ ?_
  · rintro f hf t
    obtain ⟨n, u, hu, rfl⟩ := Set.mem_iUnion.1 hf
    have hu1 : ‖u‖ ≤ 1 := mem_closedBall_zero_iff.1 hu
    have hstep : ∀ j, |w n j * k (t, x n j) * u (x n j)| ≤ |w n j| * ‖k‖ := by
      intro j
      have h1 : |k (t, x n j)| ≤ ‖k‖ := by simpa using k.norm_coe_le_norm (t, x n j)
      have h2 : |u (x n j)| ≤ 1 := le_trans (by simpa using u.norm_coe_le_norm (x n j)) hu1
      rw [abs_mul, abs_mul, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      calc |k (t, x n j)| * |u (x n j)| ≤ ‖k‖ * 1 :=
            mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
        _ = ‖k‖ := mul_one _
    rw [nystromCLM_apply, Real.norm_eq_abs]
    calc |∑ j, w n j * k (t, x n j) * u (x n j)|
        ≤ ∑ j, |w n j * k (t, x n j) * u (x n j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |w n j| * ‖k‖ := Finset.sum_le_sum fun j _ => hstep j
      _ = (∑ j, |w n j|) * ‖k‖ := by rw [Finset.sum_mul]
      _ ≤ W * ‖k‖ := mul_le_mul_of_nonneg_right (hW n) (norm_nonneg _)
  · intro t₀
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    have hcont : Continuous fun t => W * ‖row k t₀ - row k t‖ := by fun_prop
    have hlim : Tendsto (fun t => W * ‖row k t₀ - row k t‖) (𝓝 t₀) (𝓝 0) := by
      have := hcont.tendsto t₀
      simpa using this
    filter_upwards [hlim.eventually_lt_const hε] with t ht
    rintro ⟨f, hf⟩
    obtain ⟨n, u, hu, rfl⟩ := Set.mem_iUnion.1 hf
    have hu1 : ‖u‖ ≤ 1 := mem_closedBall_zero_iff.1 hu
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (hbdd n u hu1 t₀ t) ht

end Family

/-! ### The composition kernel -/

section Composition

variable [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]

/-- Let $X$ be a compact space with a finite Borel measure $\mu$, let $k$ be a continuous real
kernel on $X \times X$, and let a quadrature rule have weights $w_j$ and nodes $x_j$. The
**composition kernel** is the quadrature error for the composed kernel,
$$e(t, s) = \int k(t, v) \, k(v, s) \, d\mu(v) - \sum_j w_j \, k(t, x_j) \, k(x_j, s).$$
This is (12.4.15) of [han2009theoretical].

The two compositions $(K - K_n) K$ and $(K - K_n) K_n$ are the kernel operator and the Nyström
operator of this kernel, so their norms are given by $e$. -/
noncomputable def compKernel {m : ℕ} (w : Fin m → ℝ) (x : Fin m → X) (k : C(X × X, ℝ)) :
    C(X × X, ℝ) :=
  ⟨fun p => integralCLM μ (rowCol k p) - Quadrature.functional w x (rowCol k p), by
    exact ((integralCLM μ).continuous.comp (map_continuous (rowCol k))).sub
      ((Quadrature.functional w x).continuous.comp (map_continuous (rowCol k)))⟩

/-- The defining formula of `IntegralOperator.compKernel`: $e(t, s) = \int k(t, v) k(v, s) \,
d\mu(v) - \sum_j w_j k(t, x_j) k(x_j, s)$. -/
@[simp]
theorem compKernel_apply {m : ℕ} (w : Fin m → ℝ) (x : Fin m → X) (k : C(X × X, ℝ)) (p : X × X) :
    compKernel μ w x k p =
      (∫ v, k (p.1, v) * k (v, p.2) ∂μ) - ∑ j, w j * (k (p.1, x j) * k (x j, p.2)) := by
  change integralCLM μ (rowCol k p) - Quadrature.functional w x (rowCol k p) = _
  rw [integralCLM_apply, Quadrature.functional_apply]
  simp only [rowCol_apply]

/-- Let $X$ be a compact space with a finite Borel measure $\mu$, let $k$ be a continuous real
kernel on $X \times X$, and let a sequence of quadrature rules with weights $w^{(n)}$ and nodes
$x^{(n)}$ converge: $\sum_j w^{(n)}_j v(x^{(n)}_j) \to \int v \, d\mu$ for every $v \in C(X)$.
Then the composition kernels $e_n$ of these rules satisfy
$$\|e_n\| = \max_{t, s \in X} |e_n(t, s)| \to 0.$$
This is (12.4.18) of [han2009theoretical].

The integrands $v \mapsto k(t, v) k(v, s)$ form a continuous family indexed by the compact space
$X \times X$, so `IntegralOperator.tendsto_norm_of_tendsto_functional` applies. -/
theorem tendsto_norm_compKernel {m : ℕ → ℕ} {w : ∀ n, Fin (m n) → ℝ} {x : ∀ n, Fin (m n) → X}
    (k : C(X × X, ℝ))
    (hQ : ∀ v : C(X, ℝ), Tendsto (fun n => Quadrature.functional (w n) (x n) v) atTop
      (𝓝 (integralCLM μ v))) :
    Tendsto (fun n => ‖compKernel μ (w n) (x n) k‖) atTop (𝓝 0) :=
  tendsto_norm_of_tendsto_functional hQ (rowCol k) fun _ _ => rfl

variable {m : ℕ} (w : Fin m → ℝ) (x : Fin m → X) (k : C(X × X, ℝ))

/-- Let $X$ be a compact second-countable space with a finite Borel measure $\mu$, let $k$ be a
continuous real kernel on $X \times X$, and let $K_n$ be the Nyström operator of a quadrature
rule. Then
$$(K - K_n) K = K_e,$$
where $K_e$ is the kernel operator of the composition kernel $e$. This is (12.4.14) of
[han2009theoretical].

This is the only place where the Fubini theorem is used: the double integral $\int k(t, v) \int
k(v, s) u(s) \, d\mu(s) \, d\mu(v)$ is rewritten with the order of integration reversed. For
this reason $X$ is second-countable here, and nowhere else in the module. -/
theorem kernelCLM_sub_nystromCLM_comp_kernelCLM [SecondCountableTopology X] :
    (kernelCLM μ k - nystromCLM w x k) ∘L kernelCLM μ k = kernelCLM μ (compKernel μ w x k) := by
  refine ContinuousLinearMap.ext fun u => ContinuousMap.ext fun t => ?_
  -- the two halves of the composition kernel, as continuous functions of the column index
  have hAcont : Continuous fun s : X => ∫ v, k (t, v) * k (v, s) ∂μ :=
    continuous_integral_row μ ⟨fun p => k (t, p.2) * k (p.2, p.1), by fun_prop⟩
  have hBcont : Continuous fun s : X => ∑ j, w j * (k (t, x j) * k (x j, s)) := by fun_prop
  have hA : Integrable (fun s => (∫ v, k (t, v) * k (v, s) ∂μ) * u s) μ :=
    integrable_of_continuous μ (hAcont.mul u.continuous)
  have hB : Integrable (fun s => (∑ j, w j * (k (t, x j) * k (x j, s))) * u s) μ :=
    integrable_of_continuous μ (hBcont.mul u.continuous)
  -- Fubini on the double integral
  have hint : Integrable
      (Function.uncurry fun v s : X => k (t, v) * k (v, s) * u s) (μ.prod μ) := by
    have hc : Continuous (Function.uncurry fun v s : X => k (t, v) * k (v, s) * u s) := by
      unfold Function.uncurry
      fun_prop
    refine (integrable_const (‖k‖ * ‖k‖ * ‖u‖)).mono' hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    have h1 : |k (t, p.1)| ≤ ‖k‖ := by simpa using k.norm_coe_le_norm (t, p.1)
    have h2 : |k (p.1, p.2)| ≤ ‖k‖ := by simpa using k.norm_coe_le_norm (p.1, p.2)
    have h3 : |u p.2| ≤ ‖u‖ := by simpa using u.norm_coe_le_norm p.2
    have hk : (0 : ℝ) ≤ ‖k‖ := norm_nonneg k
    change ‖k (t, p.1) * k (p.1, p.2) * u p.2‖ ≤ ‖k‖ * ‖k‖ * ‖u‖
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) hk) h3 (abs_nonneg _)
      (mul_nonneg hk hk)
  have hL : ∀ v : X, (∫ s, k (t, v) * k (v, s) * u s ∂μ) = k (t, v) * ∫ s, k (v, s) * u s ∂μ := by
    intro v
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun s => by ring)
  have hfub : (∫ v, k (t, v) * (∫ s, k (v, s) * u s ∂μ) ∂μ)
      = ∫ s, (∫ v, k (t, v) * k (v, s) ∂μ) * u s ∂μ :=
    calc (∫ v, k (t, v) * (∫ s, k (v, s) * u s ∂μ) ∂μ)
        = ∫ v, ∫ s, k (t, v) * k (v, s) * u s ∂μ ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall fun v => (hL v).symm)
      _ = ∫ s, ∫ v, k (t, v) * k (v, s) * u s ∂μ ∂μ := integral_integral_swap hint
      _ = ∫ s, (∫ v, k (t, v) * k (v, s) ∂μ) * u s ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall fun s => integral_mul_const _ _)
  -- the finite sum comes out of the integral
  have hterm : ∀ j : Fin m,
      Integrable (fun s => w j * k (t, x j) * (k (x j, s) * u s)) μ := fun j =>
    (integrable_kernel_mul μ k u (x j)).const_mul _
  have hsum : (∫ s, (∑ j, w j * (k (t, x j) * k (x j, s))) * u s ∂μ)
      = ∑ j, w j * k (t, x j) * ∫ s, k (x j, s) * u s ∂μ := by
    rw [show (fun s => (∑ j, w j * (k (t, x j) * k (x j, s))) * u s)
        = fun s => ∑ j, w j * k (t, x j) * (k (x j, s) * u s) from
      funext fun s => by rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring,
      integral_finsetSum _ fun j _ => hterm j]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  rw [ContinuousLinearMap.comp_apply, sub_apply, ContinuousMap.sub_apply,
    kernelCLM_apply, nystromCLM_apply, kernelCLM_apply]
  simp only [kernelCLM_apply, compKernel_apply]
  rw [integral_congr_ae (Filter.Eventually.of_forall fun s =>
      (sub_mul (∫ v, k (t, v) * k (v, s) ∂μ) (∑ j, w j * (k (t, x j) * k (x j, s))) (u s))),
    integral_sub hA hB, ← hfub, ← hsum]

/-- Let $X$ be a compact space with a finite Borel measure $\mu$, let $k$ be a continuous real
kernel on $X \times X$, and let $K_n$ be the Nyström operator of a quadrature rule. Then
$$(K - K_n) K_n$$
is the Nyström operator, for the same rule, of the composition kernel $e$. This is (12.4.14) of
[han2009theoretical].

The proof uses only the linearity of the integral over a finite sum, so $X$ need not be
second-countable. -/
theorem kernelCLM_sub_nystromCLM_comp_nystromCLM :
    (kernelCLM μ k - nystromCLM w x k) ∘L nystromCLM w x k
      = nystromCLM w x (compKernel μ w x k) := by
  refine ContinuousLinearMap.ext fun u => ContinuousMap.ext fun t => ?_
  have hterm : ∀ i : Fin m, Integrable (fun v => w i * u (x i) * (k (t, v) * k (v, x i))) μ :=
    fun i => (integrable_kernel_mul μ k (col k (x i)) t).const_mul _
  have hfirst : (∫ v, k (t, v) * ∑ i, w i * k (v, x i) * u (x i) ∂μ)
      = ∑ i, w i * u (x i) * ∫ v, k (t, v) * k (v, x i) ∂μ := by
    rw [show (fun v => k (t, v) * ∑ i, w i * k (v, x i) * u (x i))
        = fun v => ∑ i, w i * u (x i) * (k (t, v) * k (v, x i)) from
      funext fun v => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring,
      integral_finsetSum _ fun i _ => hterm i]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  have hswap : (∑ j, w j * k (t, x j) * ∑ i, w i * k (x j, x i) * u (x i))
      = ∑ i, w i * u (x i) * ∑ j, w j * (k (t, x j) * k (x j, x i)) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [ContinuousLinearMap.comp_apply, sub_apply, ContinuousMap.sub_apply,
    kernelCLM_apply, nystromCLM_apply, nystromCLM_apply]
  simp only [nystromCLM_apply, compKernel_apply]
  rw [hfirst, hswap, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

end Composition

end IntegralOperator

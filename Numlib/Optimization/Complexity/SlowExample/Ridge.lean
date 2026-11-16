/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Numlib.Analysis.Calculus.MultivariateTaylor.DerivBound
import Numlib.Analysis.Calculus.MultivariateTaylor.Remainder
import Numlib.Analysis.InnerProductSpace.MinCurvature
import Numlib.Analysis.InnerProductSpace.PiL2
import Numlib.Optimization.Optimality.Approximate

/-!
# Ridge functions

Let $E$ be a real inner product space, let $g \colon \mathbb{R} \to \mathbb{R}$ and let $e \in E$.
The **ridge function** of $g$ along $e$ is $x \mapsto g(\langle e, x \rangle)$; it lifts a function
of one variable to $E$. The one-dimensional slow-convergence examples of [cartis2022evaluation]
(footnote 10) are ridge functions, and every quantity that their analysis needs is a one-dimensional
quantity along $e$: the derivatives
$$\nabla^j (g \circ \langle e, \cdot \rangle)(x)[m_1, \dots, m_j] = g^{(j)}(\langle e, x \rangle)
  \prod_{i=1}^j \langle e, m_i \rangle,$$
the gradient $g'(\langle e, x \rangle)\, e$, the Hessian $u \mapsto g''(\langle e, x \rangle)
\langle e, u \rangle\, e$, the least curvature and the Taylor polynomials. The module also shows
that the iterated derivatives and the Taylor decrements of a function along a line are those of its
restriction to the line.

## Main definitions

* `Optimization.ridge`: the ridge function $x \mapsto g(\langle e, x \rangle)$.

## Main results

* `Optimization.iteratedFDeriv_ridge_apply`: the $j$-th derivative of a ridge function is
  $g^{(j)}(\langle e, x \rangle) \prod_i \langle e, m_i \rangle$.
* `Optimization.norm_iteratedFDeriv_ridge`: for a unit vector $e$, $\|\nabla^j (g \circ \langle e,
  \cdot \rangle)(x)\| = |g^{(j)}(\langle e, x \rangle)|$.
* `Optimization.iteratedFDerivLipschitzOn_ridge`: for $\|e\| \le 1$, a Lipschitz constant of
  $g^{(j)}$ is a Lipschitz constant of the $j$-th derivative of the ridge function.
* `Optimization.gradient_ridge`: the gradient is $g'(\langle e, x \rangle)\, e$.
* `Optimization.hessianOperator_ridge`: the Hessian maps $u$ to $g''(\langle e, x \rangle) \langle
  e, u \rangle\, e$.
* `Optimization.minCurvature_iteratedFDeriv_ridge`: if $e$ is a unit vector and some unit vector is
  orthogonal to $e$, the least curvature is $\min\{0, g''(\langle e, x \rangle)\}$.
* `Optimization.taylorPolynomial_ridge`: the Taylor polynomial of degree $p$ is $\sum_{i \le p}
  g^{(i)}(\langle e, x \rangle) \langle e, s \rangle^i / i!$.
* `Optimization.iteratedFDeriv_apply_const_eq_line`, `Optimization.taylorDecrement_eq_of_line`:
  iterated derivatives and Taylor decrements along a line are those of the restriction to the line.
* `Optimization.hessianOperator_ridge_single`: on $\mathbb{R}^1$, the Hessian of the ridge function
  along the coordinate direction is multiplication by $g''$.
-/

open Set Finset
open scoped Nat RealInnerProductSpace

namespace Optimization

/-! ### Ridge functions -/

section Ridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {g : ℝ → ℝ} {e : E}

/-- Let $E$ be a real inner product space, let $g \colon \mathbb{R} \to \mathbb{R}$ and let
$e \in E$. The **ridge function** of $g$ along $e$ is the function $E \to \mathbb{R}$
$$x \mapsto g(\langle e, x \rangle).$$
-/
def ridge (g : ℝ → ℝ) (e : E) (x : E) : ℝ :=
  g ⟪e, x⟫

/-- The ridge function takes the value $g(\langle e, x \rangle)$ at $x$. -/
theorem ridge_apply (g : ℝ → ℝ) (e x : E) : ridge g e x = g ⟪e, x⟫ :=
  rfl

/-- The ridge function of $g$ along $e$ is the composition of $g$ with the continuous linear
functional $x \mapsto \langle e, x \rangle$. -/
theorem ridge_eq_comp (g : ℝ → ℝ) (e : E) : ridge g e = g ∘ innerSL ℝ e :=
  rfl

/-- If $g$ is of class $C^n$, then the ridge function of $g$ along $e$ is of class $C^n$. -/
theorem contDiff_ridge {n : WithTop ℕ∞} (hg : ContDiff ℝ n g) : ContDiff ℝ n (ridge g e) :=
  hg.comp (innerSL ℝ e).contDiff

/-- Let $g$ be of class $C^n$ and let $j \le n$. For $x \in E$ and $m_1, \dots, m_j \in E$, the
$j$-th derivative of the ridge function of $g$ along $e$ is
$$\nabla^j (g \circ \langle e, \cdot \rangle)(x)[m_1, \dots, m_j] = \Bigl(\prod_{i=1}^j \langle
  e, m_i \rangle\Bigr) g^{(j)}(\langle e, x \rangle).$$
-/
theorem iteratedFDeriv_ridge_apply {n : WithTop ℕ∞} (hg : ContDiff ℝ n g) {j : ℕ}
    (hj : (j : WithTop ℕ∞) ≤ n) (x : E) (m : Fin j → E) :
    iteratedFDeriv ℝ j (ridge g e) x m = (∏ i, ⟪e, m i⟫) * iteratedDeriv j g ⟪e, x⟫ := by
  rw [ridge_eq_comp, (innerSL ℝ e).iteratedFDeriv_comp_right hg x hj,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul]
  simp

/-- Let $g$ be of class $C^n$ and let $j \le n$. For $x, d \in E$, the $j$-th derivative of the
ridge function of $g$ along $e$ in the direction $d$ is
$$\nabla^j (g \circ \langle e, \cdot \rangle)(x)[d]^j = g^{(j)}(\langle e, x \rangle) \langle e,
  d \rangle^j.$$
-/
theorem iteratedFDeriv_ridge_apply_diag {n : WithTop ℕ∞} (hg : ContDiff ℝ n g) {j : ℕ}
    (hj : (j : WithTop ℕ∞) ≤ n) (x d : E) :
    iteratedFDeriv ℝ j (ridge g e) x (fun _ => d) = iteratedDeriv j g ⟪e, x⟫ * ⟪e, d⟫ ^ j := by
  rw [iteratedFDeriv_ridge_apply hg hj, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    mul_comm]

/-- Let $g$ be of class $C^n$, let $j \le n$ and let $\|e\| \le 1$. Then for every $x \in E$ the
$j$-th derivative of the ridge function of $g$ along $e$ has norm $\|\nabla^j (g \circ \langle
e, \cdot \rangle)(x)\| \le |g^{(j)}(\langle e, x \rangle)|$. -/
theorem norm_iteratedFDeriv_ridge_le {n : WithTop ℕ∞} (hg : ContDiff ℝ n g) {j : ℕ}
    (hj : (j : WithTop ℕ∞) ≤ n) (he : ‖e‖ ≤ 1) (x : E) :
    ‖iteratedFDeriv ℝ j (ridge g e) x‖ ≤ |iteratedDeriv j g ⟪e, x⟫| := by
  rw [ridge_eq_comp, (innerSL ℝ e).iteratedFDeriv_comp_right hg x hj]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  refine mul_le_of_le_one_right (abs_nonneg _) ?_
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun _ _ => by rwa [innerSL_apply_norm]

/-- Let $g$ be of class $C^n$, let $j \le n$ and let $\|e\| = 1$. Then for every $x \in E$ the
$j$-th derivative of the ridge function of $g$ along $e$ has norm $\|\nabla^j (g \circ \langle
e, \cdot \rangle)(x)\| = |g^{(j)}(\langle e, x \rangle)|$. -/
theorem norm_iteratedFDeriv_ridge {n : WithTop ℕ∞} (hg : ContDiff ℝ n g) {j : ℕ}
    (hj : (j : WithTop ℕ∞) ≤ n) (he : ‖e‖ = 1) (x : E) :
    ‖iteratedFDeriv ℝ j (ridge g e) x‖ = |iteratedDeriv j g ⟪e, x⟫| := by
  refine le_antisymm (norm_iteratedFDeriv_ridge_le hg hj he.le x) ?_
  have h := (iteratedFDeriv ℝ j (ridge g e) x).le_opNorm fun _ => e
  rw [iteratedFDeriv_ridge_apply_diag hg hj, real_inner_self_eq_norm_sq, he] at h
  simpa [he] using h

/-- Let $g$ be of class $C^n$, let $j \le n$, let $\|e\| \le 1$ and let $L \ge 0$. If
$|g^{(j)}(s) - g^{(j)}(t)| \le L |s - t|$ for all $s, t \in \mathbb{R}$, then the $j$-th
derivative of the ridge function of $g$ along $e$ is $L$-Lipschitz on all of $E$. -/
theorem iteratedFDerivLipschitzOn_ridge {n : WithTop ℕ∞} (hg : ContDiff ℝ n g) {j : ℕ}
    (hj : (j : WithTop ℕ∞) ≤ n) (he : ‖e‖ ≤ 1) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ s t, |iteratedDeriv j g s - iteratedDeriv j g t| ≤ L * |s - t|) :
    IteratedFDerivLipschitzOn (ridge g e) j L univ := by
  rw [iteratedFDerivLipschitzOn_iff]
  intro x _ y _
  rw [ridge_eq_comp, (innerSL ℝ e).iteratedFDeriv_comp_right hg x hj,
    (innerSL ℝ e).iteratedFDeriv_comp_right hg y hj]
  have hsub : (iteratedFDeriv ℝ j g ⟪e, x⟫).compContinuousLinearMap (fun _ => innerSL ℝ e) -
      (iteratedFDeriv ℝ j g ⟪e, y⟫).compContinuousLinearMap (fun _ => innerSL ℝ e) =
      (iteratedFDeriv ℝ j g ⟪e, x⟫ - iteratedFDeriv ℝ j g ⟪e, y⟫).compContinuousLinearMap
        (fun _ => innerSL ℝ e) := by
    ext m
    simp
  rw [innerSL_apply_apply, innerSL_apply_apply, hsub]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hp : ∏ _i : Fin j, ‖innerSL ℝ e‖ ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun _ _ => by rwa [innerSL_apply_norm]
  have hd : ‖iteratedFDeriv ℝ j g ⟪e, x⟫ - iteratedFDeriv ℝ j g ⟪e, y⟫‖ =
      |iteratedDeriv j g ⟪e, x⟫ - iteratedDeriv j g ⟪e, y⟫| := by
    rw [iteratedFDeriv_eq_equiv_comp, Function.comp_apply,
      Function.comp_apply, ← map_sub, LinearIsometryEquiv.norm_map, Real.norm_eq_abs]
  have hxy : |⟪e, x⟫ - ⟪e, y⟫| ≤ ‖x - y‖ := by
    rw [← inner_sub_right]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_of_le_one_left (norm_nonneg _) he)
  calc ‖iteratedFDeriv ℝ j g ⟪e, x⟫ - iteratedFDeriv ℝ j g ⟪e, y⟫‖ * ∏ _i : Fin j, ‖innerSL ℝ e‖
      ≤ ‖iteratedFDeriv ℝ j g ⟪e, x⟫ - iteratedFDeriv ℝ j g ⟪e, y⟫‖ :=
        mul_le_of_le_one_right (norm_nonneg _) hp
    _ ≤ L * ‖x - y‖ := by
        rw [hd]
        exact (hL _ _).trans (mul_le_mul_of_nonneg_left hxy hL0)

/-- Let $g$ be of class $C^2$ and let $\|e\| = 1$. For every $x \in E$, the least curvature
$\lambda_{\min} = \inf_{\|d\| = 1} \nabla^2 (g \circ \langle e, \cdot \rangle)(x)[d, d]$ of the
ridge function satisfies
$$\min\{0, g''(\langle e, x \rangle)\} \le \lambda_{\min} \le g''(\langle e, x \rangle).$$

The upper bound is the curvature in the direction $e$. The least curvature is
`minCurvature`. -/
theorem min_le_minCurvature_iteratedFDeriv_ridge (hg : ContDiff ℝ 2 g) (he : ‖e‖ = 1) (x : E) :
    min 0 (iteratedDeriv 2 g ⟪e, x⟫) ≤ minCurvature (iteratedFDeriv ℝ 2 (ridge g e) x) ∧
      minCurvature (iteratedFDeriv ℝ 2 (ridge g e) x) ≤ iteratedDeriv 2 g ⟪e, x⟫ := by
  have hdiag : ∀ d : E, iteratedFDeriv ℝ 2 (ridge g e) x (fun _ => d) =
      iteratedDeriv 2 g ⟪e, x⟫ * ⟪e, d⟫ ^ 2 := fun d =>
    iteratedFDeriv_ridge_apply_diag hg (by norm_num) x d
  have hE : Nontrivial E := ⟨⟨e, 0, fun h => by simp [h] at he⟩⟩
  refine ⟨le_minCurvature_iff.2 fun d => ?_, ?_⟩
  · rw [hdiag]
    have h1 : ⟪e, d⟫ ^ 2 ≤ ‖d‖ ^ 2 := by
      have := abs_real_inner_le_norm e d
      rw [he, one_mul] at this
      nlinarith [abs_nonneg ⟪e, d⟫, sq_abs ⟪e, d⟫]
    rcases le_total 0 (iteratedDeriv 2 g ⟪e, x⟫) with h | h
    · rw [min_eq_left h, zero_mul]
      positivity
    · rw [min_eq_right h]
      nlinarith [sq_nonneg ⟪e, d⟫]
  · have := minCurvature_le_apply (iteratedFDeriv ℝ 2 (ridge g e) x) he
    rwa [hdiag, real_inner_self_eq_norm_sq, he, one_pow, one_pow, mul_one] at this

/-- The **least curvature of a ridge function**. Let $g$ be of class $C^2$, let $\|e\| = 1$, and
assume that some unit vector $d \in E$ is orthogonal to $e$ (for example, $\dim E \ge 2$). Then
for every $x \in E$,
$$\lambda_{\min}\bigl[\nabla^2 (g \circ \langle e, \cdot \rangle)(x)\bigr] = \min\{0,
  g''(\langle e, x \rangle)\}.$$

The least curvature $\lambda_{\min}[A] = \inf_{\|d\| = 1} A[d, d]$ is
`minCurvature`. The curvature in the orthogonal direction $d$ is $0$, and the
curvature in the direction $e$ is $g''(\langle e, x \rangle)$. -/
theorem minCurvature_iteratedFDeriv_ridge (hg : ContDiff ℝ 2 g) (he : ‖e‖ = 1)
    (hperp : ∃ d : E, ‖d‖ = 1 ∧ ⟪e, d⟫ = 0) (x : E) :
    minCurvature (iteratedFDeriv ℝ 2 (ridge g e) x) = min 0 (iteratedDeriv 2 g ⟪e, x⟫) := by
  obtain ⟨h1, h2⟩ := min_le_minCurvature_iteratedFDeriv_ridge hg he x
  obtain ⟨d, hd, hed⟩ := hperp
  have h3 := minCurvature_le_apply (iteratedFDeriv ℝ 2 (ridge g e) x) hd
  rw [iteratedFDeriv_ridge_apply_diag hg (by norm_num), hed] at h3
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h3
  exact le_antisymm (le_min h3 h2) h1

/-- Let $g$ be of class $C^2$, let $\|e\| = 1$, and assume that $\langle e, d \rangle^2 = \|d\|^2$
for every $d \in E$, so that every vector is a multiple of $e$ (dimension one). Then for every
$x \in E$ the least curvature of the ridge function of $g$ along $e$ at $x$ is
$g''(\langle e, x \rangle)$. -/
theorem minCurvature_iteratedFDeriv_ridge_of_forall (hg : ContDiff ℝ 2 g) (he : ‖e‖ = 1)
    (hspan : ∀ d : E, ⟪e, d⟫ ^ 2 = ‖d‖ ^ 2) (x : E) :
    minCurvature (iteratedFDeriv ℝ 2 (ridge g e) x) = iteratedDeriv 2 g ⟪e, x⟫ := by
  have hE : Nontrivial E := ⟨⟨e, 0, fun h => by simp [h] at he⟩⟩
  refine le_antisymm (min_le_minCurvature_iteratedFDeriv_ridge hg he x).2
    (le_minCurvature_iff.2 fun d => ?_)
  rw [iteratedFDeriv_ridge_apply_diag hg (by norm_num), hspan]

/-- Let $E$ be a complete real inner product space and let $g$ be differentiable. For every
$x \in E$, the gradient of the ridge function of $g$ along $e$ is
$$\nabla (g \circ \langle e, \cdot \rangle)(x) = g'(\langle e, x \rangle)\, e.$$
-/
theorem gradient_ridge [CompleteSpace E] (hg : Differentiable ℝ g) (x : E) :
    gradient (ridge g e) x = deriv g ⟪e, x⟫ • e := by
  have h : HasFDerivAt (ridge g e) (deriv g ⟪e, x⟫ • innerSL ℝ e) x := by
    have := (hg ⟪e, x⟫).hasDerivAt.comp_hasFDerivAt x (innerSL ℝ e).hasFDerivAt
    simpa [ridge_eq_comp] using this
  have h' : HasGradientAt (ridge g e) (deriv g ⟪e, x⟫ • e) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert h using 1
    ext v
    simp [InnerProductSpace.toDual_apply_apply]
  exact h'.gradient

/-- Let $E$ be a complete real inner product space and let $g$ be of class $C^2$. For all
$x, u \in E$, the Hessian of the ridge function of $g$ along $e$ satisfies
$$\nabla^2 (g \circ \langle e, \cdot \rangle)(x)\, u = g''(\langle e, x \rangle) \langle e, u
  \rangle\, e.$$

The Hessian is `Optimization.hessianOperator`, the derivative of the gradient, as an operator on
$E$. -/
theorem hessianOperator_ridge [CompleteSpace E] (hg : ContDiff ℝ 2 g) (x u : E) :
    hessianOperator (ridge g e) x u = (iteratedDeriv 2 g ⟪e, x⟫ * ⟪e, u⟫) • e := by
  refine ext_inner_left ℝ fun w => ?_
  rw [inner_hessianOperator_apply (contDiff_ridge hg).contDiffAt,
    iteratedFDeriv_ridge_apply hg (by norm_num), Fin.prod_univ_two, inner_smul_right,
    real_inner_comm e w]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

end Ridge

/-! ### Restriction to a line -/

section Line

/-- **Iterated derivatives along a line.** Let $E$ be a real normed space, let
$F \colon E \to \mathbb{R}$ be of class $C^n$ with $n \in \mathbb{N}$, and let $i \le n$. For
all $s, d \in E$, the $i$-th derivative of $F$ at $s$ in the direction $d$ is the $i$-th
derivative at $0$ of the restriction of $F$ to the line through $s$ in the direction $d$:
$$\nabla^i F(s)[d]^i = \frac{\mathrm{d}^i}{\mathrm{d}\tau^i} F(s + \tau d) \Big|_{\tau = 0}.$$
-/
theorem iteratedFDeriv_apply_const_eq_line {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : E → ℝ} {n : ℕ} (hF : ContDiff ℝ n F) {i : ℕ} (hi : i ≤ n) (s d : E) :
    iteratedFDeriv ℝ i F s (fun _ => d) = iteratedDeriv i (fun τ : ℝ => F (s + τ • d)) 0 := by
  have hcomp : (fun τ : ℝ => F (s + τ • d)) =
      (fun v => F (s + v)) ∘ ContinuousLinearMap.toSpanSingleton ℝ d := by
    funext τ; simp [ContinuousLinearMap.toSpanSingleton_apply]
  have hg : ContDiff ℝ n (fun v => F (s + v)) := hF.comp (contDiff_const.add contDiff_id)
  rw [hcomp, iteratedDeriv_eq_iteratedFDeriv,
    (ContinuousLinearMap.toSpanSingleton ℝ d).iteratedFDeriv_comp_right hg 0
      (by exact_mod_cast hi),
    ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_comp_add_left]
  simp [ContinuousLinearMap.toSpanSingleton_apply]

/-- **Taylor decrements along a line.** Let $E$ be a real normed space, let
$F \colon E \to \mathbb{R}$ and $F_1 \colon \mathbb{R} \to \mathbb{R}$ be of class $C^n$ with
$n \in \mathbb{N}$, and let $s, d \in E$ and $t, a \in \mathbb{R}$. If
$F(s + \tau d) = F_1(t + \tau a)$ for every $\tau \in \mathbb{R}$, then for every $\ell \le n$
the Taylor decrement of order $\ell$ of $F$ at $s$ along $d$ equals that of $F_1$ at $t$ along
$a$:
$$T_{F,\ell}(s, 0) - T_{F,\ell}(s, d) = T_{F_1,\ell}(t, 0) - T_{F_1,\ell}(t, a).$$

The Taylor decrement is `FormalMultilinearSeries.taylorDecrement` of the jet
`ftaylorSeries ℝ F s`. -/
theorem taylorDecrement_eq_of_line {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : E → ℝ} {F₁ : ℝ → ℝ} {n : ℕ} (hF : ContDiff ℝ n F)
    (hF₁ : ContDiff ℝ n F₁) {s d : E} {t a : ℝ} (hline : ∀ τ : ℝ, F (s + τ • d) = F₁ (t + τ * a))
    {ℓ : ℕ} (hℓ : ℓ ≤ n) :
    (ftaylorSeries ℝ F s).taylorDecrement ℓ d = (ftaylorSeries ℝ F₁ t).taylorDecrement ℓ a := by
  rw [FormalMultilinearSeries.taylorDecrement_eq, FormalMultilinearSeries.taylorDecrement_eq]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hin : i ≤ n := (Finset.mem_Icc.1 hi).2.trans hℓ
  change (i ! : ℝ)⁻¹ * iteratedFDeriv ℝ i F s (fun _ => d) =
    (i ! : ℝ)⁻¹ * iteratedFDeriv ℝ i F₁ t (fun _ => a)
  rw [iteratedFDeriv_apply_const_eq_line hF hin, iteratedFDeriv_apply_const_eq_line hF₁ hin]
  congr 2
  funext τ
  rw [hline, smul_eq_mul]

end Line

section RidgeTaylor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Let $G$ be of class $C^p$ and let $e, x, s \in E$. The Taylor polynomial of degree $p$ of the
ridge function of $G$ along $e$, at $x$ and with increment $s$, is
$$T_p(x, s) = \sum_{i=0}^p \frac{1}{i!} G^{(i)}(\langle e, x \rangle) \langle e, s \rangle^i.$$

The Taylor polynomial is `taylorPolynomial`. -/
theorem taylorPolynomial_ridge {G : ℝ → ℝ} {p : ℕ} (hG : ContDiff ℝ p G) (e x s : E) :
    taylorPolynomial (ridge G e) p x s =
      ∑ i ∈ range (p + 1), (i.factorial : ℝ)⁻¹ * (iteratedDeriv i G ⟪e, x⟫ * ⟪e, s⟫ ^ i) := by
  rw [taylorPolynomial_apply]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ p := Nat.lt_succ_iff.1 (mem_range.1 hi)
  rw [smul_eq_mul, iteratedFDeriv_ridge_apply_diag hG (by exact_mod_cast hi')]

end RidgeTaylor

/-- Let $g$ be of class $C^2$ and let $e_1$ be the coordinate unit vector of $\mathbb{R}^1$. For all
$x, u \in \mathbb{R}^1$, the Hessian of the ridge function of $g$ along $e_1$ is multiplication
by $g''$:
$$\nabla^2 (g \circ \langle e_1, \cdot \rangle)(x)\, u = g''(\langle e_1, x \rangle)\, u.$$

Here $\mathbb{R}^1$ is `EuclideanSpace ℝ (Fin 1)` and $e_1$ is `EuclideanSpace.single 0 1`. -/
theorem hessianOperator_ridge_single {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (x u : EuclideanSpace ℝ (Fin 1)) :
    hessianOperator (ridge g (EuclideanSpace.single 0 1)) x u =
      iteratedDeriv 2 g ⟪EuclideanSpace.single 0 1, x⟫ • u := by
  rw [hessianOperator_ridge hg, mul_smul, ← EuclideanSpace.eq_inner_single_smul]

end Optimization

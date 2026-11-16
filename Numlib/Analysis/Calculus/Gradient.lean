/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Calculus.Gradient.Basic`, beside `gradient` and `HasGradientAt`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.Analysis.InnerProductSpace.Dual

/-!
# The gradient: the Riesz map, and coordinates on $\mathbb{R}^d$

Let $E$ be a real Hilbert space and $f : E \to \mathbb{R}$. Mathlib's gradient $\nabla f(x)$ is the
vector that represents the derivative $Df(x)$ through the Riesz map, so that
$Df(x)\, d = \langle \nabla f(x), d \rangle$ for all $d$. This module collects small facts about it.
In general, the gradient is the inverse of the real-linear Riesz map applied to the derivative. On
$\mathbb{R}^d$, the coordinates of the gradient are the partial derivatives, the inner product of
two gradients is $\sum_i \partial_i u\, \partial_i v$, and the operator norm of $Du(x)$ is the
Euclidean norm of the vector of partial derivatives. A function whose gradient is $C$-Lipschitz has
its second derivative bounded by $C$. The modules under `Numlib.Analysis.Sobolev.Boundary` use these
facts.

## Main results

* `gradient_eq_toDualReal_symm`: the gradient through the real-linear Riesz map
  `InnerProductSpace.toDualReal`, so that the calculus lemmas for linear isometry equivalences
  apply.
* `fderiv_eq_innerSL_gradient`: $Df(x) = \langle \nabla f(x), \cdot \rangle$.
* `EuclideanSpace.gradient_apply`: the $i$-th coordinate of the gradient is the $i$-th partial
  derivative.
* `EuclideanSpace.inner_gradient_eq_fderiv`, `EuclideanSpace.inner_gradient_eq_sum`,
  `EuclideanSpace.norm_gradient_eq`, `EuclideanSpace.norm_fderiv_eq`: the gradient on $\mathbb{R}^d$
  in coordinates.
* `EuclideanSpace.continuous_gradient`: the gradient of a $C^1$ function is continuous.
* `EuclideanSpace.abs_apply_sub_le`, `EuclideanSpace.norm_toLp_two_le`: the coordinate bounds
  $|x_i - y_i| \le \|x - y\|$ and $\|(a, b)\| \le |a| + |b|$.
* `norm_iteratedFDeriv_two_le_of_gradient`, `contDiff_two_of_gradient`: second derivatives from the
  gradient.

## Implementation notes

* The gradient is Mathlib's `gradient f x`, defined as `(toDual ℝ E).symm (fderiv ℝ f x)`. Where $f$
  is not differentiable, the derivative and the gradient are both $0$.
* The space $\mathbb{R}^d$ is `EuclideanSpace ℝ (Fin d)`, and the $i$-th partial derivative of $u$
  at $x$ is `fderiv ℝ u x (EuclideanSpace.single i 1)`.
-/

open scoped InnerProductSpace

section ToDualReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Let $E$ be a real Hilbert space and $f : E \to \mathbb{R}$. Then the gradient of $f$ at $x$ is
the inverse of the real-linear Riesz map `InnerProductSpace.toDualReal` applied to $Df(x)$. -/
theorem gradient_eq_toDualReal_symm (f : E → ℝ) :
    gradient f = fun x ↦ (InnerProductSpace.toDualReal E).symm (fderiv ℝ f x) := rfl

/-- Let $E$ be a real Hilbert space, $f : E \to \mathbb{R}$ and $x \in E$. Then the derivative is
the inner product with the gradient: $Df(x) = \langle \nabla f(x), \cdot \rangle$ as a
continuous linear map, so that $Df(x)\, d = \langle \nabla f(x), d \rangle$ for all $d \in E$.

No differentiability is needed, since both sides are $0$ when $f$ is not differentiable at $x$.
This is the form in which derivative data of the form `f' x = innerSL ℝ (g x)`, as in
`Numlib.Optimization.Descent`, meet Mathlib's gradient. Compare Mathlib's `toDual_gradient`. -/
theorem fderiv_eq_innerSL_gradient (f : E → ℝ) (x : E) :
    fderiv ℝ f x = innerSL ℝ (gradient f x) := by
  ext d
  rw [innerSL_apply_apply, inner_gradient_left]

end ToDualReal

namespace EuclideanSpace

/-- For a finite index type $\iota$ and $v, w \in \mathbb{R}^\iota$ with the Euclidean inner
product, $\langle v, w \rangle = \sum_j v_j w_j$. This is the real case of
`EuclideanSpace.inner_eq_star_dotProduct`, written as a sum. -/
theorem real_inner_eq_sum {ι : Type*} [Fintype ι] (v w : EuclideanSpace ℝ ι) :
    ⟪v, w⟫_ℝ = ∑ j, v j * w j := by
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- For a finite index type $\iota$ and $v \in \mathbb{R}^\iota$, the functional
$\langle v, \cdot \rangle$ is $\sum_j v_j \pi_j$, where $\pi_j$ is the $j$-th coordinate
projection. This is how a gradient is read off from the partial derivatives.

The projection $\pi_j$ is `EuclideanSpace.proj j`. -/
theorem innerSL_eq_sum_smul_proj {ι : Type*} [Fintype ι] (v : EuclideanSpace ℝ ι) :
    innerSL ℝ v = ∑ j, v j • EuclideanSpace.proj (𝕜 := ℝ) j := by
  ext w
  rw [innerSL_apply_apply, real_inner_eq_sum]
  simp

variable {d : ℕ} {g : EuclideanSpace ℝ (Fin d) → ℝ}

/-- Let $g : \mathbb{R}^d \to \mathbb{R}$ be $C^1$. Then its gradient $\nabla g$ is continuous. -/
theorem continuous_gradient (hg : ContDiff ℝ 1 g) : Continuous (gradient g) := by
  change Continuous fun x' ↦ (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm
    (fderiv ℝ g x')
  exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.continuous.comp
    (hg.continuous_fderiv one_ne_zero)

/-- For $g : \mathbb{R}^d \to \mathbb{R}$ and $x \in \mathbb{R}^d$, the norm of the gradient is the
operator norm of the derivative: $\|\nabla g(x)\| = \|Dg(x)\|$. -/
theorem norm_gradient_eq (x' : EuclideanSpace ℝ (Fin d)) : ‖gradient g x'‖ = ‖fderiv ℝ g x'‖ :=
  LinearIsometryEquiv.norm_map _ _

/-- For $g : \mathbb{R}^d \to \mathbb{R}$ and $x, v \in \mathbb{R}^d$, the inner product of the
gradient with $v$ is the derivative in the direction $v$:
$\langle \nabla g(x), v \rangle = Dg(x)\, v$. -/
theorem inner_gradient_eq_fderiv (x' v : EuclideanSpace ℝ (Fin d)) :
    ⟪gradient g x', v⟫_ℝ = fderiv ℝ g x' v :=
  InnerProductSpace.toDual_symm_apply

/-- For $g : \mathbb{R}^d \to \mathbb{R}$, $x \in \mathbb{R}^d$ and $i < d$, the $i$-th coordinate
of the gradient is the $i$-th partial derivative: $(\nabla g(x))_i = Dg(x)\, e_i$, where $e_i$
is the $i$-th unit vector.

The unit vector $e_i$ is `EuclideanSpace.single i 1`. -/
theorem gradient_apply (g : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d))
    (i : Fin d) : gradient g x i = fderiv ℝ g x (EuclideanSpace.single i 1) := by
  have h : gradient g x i = ⟪gradient g x, EuclideanSpace.single i 1⟫_ℝ := by
    rw [EuclideanSpace.inner_single_right, conj_trivial, one_mul]
  rw [h, gradient, InnerProductSpace.toDual_symm_apply]

/-- For $u, v : \mathbb{R}^d \to \mathbb{R}$ and $x \in \mathbb{R}^d$, the inner product of the two
gradients in coordinates is
$$\langle \nabla u(x), \nabla v(x) \rangle = \sum_{i} \partial_i u(x)\, \partial_i v(x),$$
where $\partial_i u(x) = Du(x)\, e_i$. -/
theorem inner_gradient_eq_sum (u v : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    ⟪gradient u x, gradient v x⟫_ℝ
      = ∑ i, fderiv ℝ u x (EuclideanSpace.single i 1)
        * fderiv ℝ v x (EuclideanSpace.single i 1) := by
  simp only [real_inner_eq_sum, gradient_apply]

/-- For $u : \mathbb{R}^d \to \mathbb{R}$ and $x \in \mathbb{R}^d$, the operator norm of $Du(x)$ is
the Euclidean norm of the vector of partial derivatives $(\partial_i u(x))_i$, where
$\partial_i u(x) = Du(x)\, e_i$.

The vector of partial derivatives is an element of `PiLp 2 (fun _ : Fin d ↦ ℝ)`. -/
theorem norm_fderiv_eq (u : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    ‖fderiv ℝ u x‖
      = ‖(WithLp.toLp 2 fun i ↦ fderiv ℝ u x (EuclideanSpace.single i 1) :
          PiLp 2 fun _ : Fin d ↦ ℝ)‖ := by
  have h : gradient u x
      = (WithLp.toLp 2 fun i ↦ fderiv ℝ u x (EuclideanSpace.single i 1) :
          PiLp 2 fun _ : Fin d ↦ ℝ) := by
    ext i
    rw [gradient, PiLp.toLp_apply]
    have h2 : ∀ w : EuclideanSpace ℝ (Fin d), w i = ⟪w, EuclideanSpace.single i 1⟫_ℝ := fun w ↦ by
      rw [EuclideanSpace.inner_single_right, conj_trivial, one_mul]
    rw [h2, InnerProductSpace.toDual_symm_apply]
  rw [← h, gradient, LinearIsometryEquiv.norm_map]

/-- For a finite index type $\iota$, $x, y \in \mathbb{R}^\iota$ and $i \in \iota$, a coordinate
difference is at most the Euclidean distance: $|x_i - y_i| \le \|x - y\|$. -/
theorem abs_apply_sub_le {ι : Type*} [Fintype ι] (x y : EuclideanSpace ℝ ι) (i : ι) :
    |x i - y i| ≤ ‖x - y‖ := by
  have := PiLp.norm_apply_le (x - y) i
  rwa [PiLp.sub_apply, Real.norm_eq_abs] at this

/-- For $a, b \in \mathbb{R}$, the Euclidean norm of $(a, b) \in \mathbb{R}^2$ is at most
$|a| + |b|$. -/
theorem norm_toLp_two_le (a b : ℝ) : ‖!₂[a, b]‖ ≤ |a| + |b| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.norm_eq_abs, sq_abs]
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [abs_nonneg a, abs_nonneg b, sq_abs a, sq_abs b]

end EuclideanSpace

/-! ### Second derivatives from the gradient -/

section SecondDerivative

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {F : E → ℝ} {G : E → E}

/-- Let $E$ be a real Hilbert space, let $F : E \to \mathbb{R}$ have the gradient $G(z)$ at every
$z$, and let $C \ge 0$ with $\|G(z) - G(z')\| \le C \|z - z'\|$ for all $z, z'$. Then
$\|D^2 F(z)\| \le C$ for every $z \in E$.

The second derivative $D^2 F(z)$ is `iteratedFDeriv ℝ 2 F z`. -/
theorem norm_iteratedFDeriv_two_le_of_gradient {C : ℝ} (hC : 0 ≤ C)
    (hG : ∀ z, HasGradientAt F (G z) z) (hL : ∀ z z', ‖G z - G z'‖ ≤ C * ‖z - z'‖) (z : E) :
    ‖iteratedFDeriv ℝ 2 F z‖ ≤ C := by
  have hfd : fderiv ℝ F = fun z => InnerProductSpace.toDual ℝ E (G z) :=
    funext fun z => ((hasGradientAt_iff_hasFDerivAt).1 (hG z)).fderiv
  rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
  refine norm_fderiv_le_of_lip' ℝ hC (Filter.Eventually.of_forall fun x => ?_)
  rw [hfd, ← map_sub, LinearIsometryEquiv.norm_map]
  exact hL x z

/-- Let $E$ be a real Hilbert space, and let $F : E \to \mathbb{R}$ have the gradient $G(z)$ at
every $z$. If $G$ is $C^1$, then $F$ is $C^2$. -/
theorem contDiff_two_of_gradient (hG : ∀ z, HasGradientAt F (G z) z) (hGc : ContDiff ℝ 1 G) :
    ContDiff ℝ 2 F := by
  have hfd : fderiv ℝ F = fun z => InnerProductSpace.toDual ℝ E (G z) :=
    funext fun z => ((hasGradientAt_iff_hasFDerivAt).1 (hG z)).fderiv
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_fderiv]
  refine ⟨fun z => (hG z).differentiableAt, by simp, ?_⟩
  rw [hfd]
  exact ((InnerProductSpace.toDual ℝ E).contDiff (n := 1)).comp hGc

end SecondDerivative

/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.Analysis.Calculus.Gradient
import Numlib.Analysis.Calculus.MultivariateTaylor.Remainder
import Numlib.Analysis.Normed.Lp.PiLp
import Numlib.Optimization.ModelBased.InexactTaylor
import Numlib.Optimization.Optimality.Approximate

/-!
# Forward-difference gradients and Hessians

Let $f : \mathbb{R}^n \to \mathbb{R}$, let $e_1, \dots, e_n$ be the unit vectors and let $h > 0$.
The forward-difference gradient approximates $\nabla f(x)$ from $n + 1$ values of $f$, and the
forward-difference Hessian approximates $\nabla^2 f(x)$ from $n + 1$ values of $\nabla f$
([cartis2022evaluation], §13.2):
$$[\overline\nabla f(x)]_i = \frac{f(x + h e_i) - f(x)}{h},
  \qquad [\overline\nabla^2 f(x)]_{\cdot, j} = \frac{\nabla f(x + h e_j) - \nabla f(x)}{h}.$$
More generally, the forward-difference derivative of a map $g : \mathbb{R}^n \to F$ has the columns
$(g(x + h e_j) - g(x))/h$. If the derivative that is approximated is Lipschitz continuous with
constant $L$, the error is at most $\sqrt n\, L h/2$. This bound has the "dynamic accuracy" form
$\|\text{approximation} - \text{exact}\| \le \kappa h$ of (13.1.2) in [cartis2022evaluation], with
the difference step $h$ as the requested accuracy. Hence these schemes produce inexact jets in the
sense of `Optimization.JetApprox`: the inexact-derivative framework of Chapter 13 is realized by
oracles of degree $0$ (for gradients) and $1$ (for Hessians).

General stencils ((13.2.1) in [cartis2022evaluation]) are in `Numlib.FiniteDifference.MixedPartial`,
and interpolation models ((13.2.2)–(13.2.4)) are in `Numlib.Approximation.MvLagrange`.

## Main definitions

* `FiniteDifference.fdGradient`: the forward-difference gradient $\overline\nabla f(x)$.
* `FiniteDifference.fdFDeriv`: the forward-difference derivative of a map $g$.
* `FiniteDifference.fdHessian`: the forward-difference Hessian, the forward-difference derivative of
  $\nabla f$.

## Main results

* `FiniteDifference.norm_fdGradient_sub_gradient_le_of_convex`,
  `FiniteDifference.norm_fdGradient_sub_gradient_le`: $\|\overline\nabla f(x) - \nabla f(x)\| \le
  \sqrt n\, L h/2$, on a convex set and globally.
* `FiniteDifference.norm_fdFDeriv_sub_le_of_convex`, `FiniteDifference.norm_fdFDeriv_sub_le`: the
  same bound for the forward-difference derivative of any map.
* `FiniteDifference.norm_fdHessian_sub_hessianOperator_le`: $\|\overline\nabla^2 f(x) - \nabla^2
  f(x)\| \le \sqrt n\, L h/2$.
* `FiniteDifference.jetApprox_fdGradient`, `FiniteDifference.jetApprox_fdHessian`: the
  forward-difference gradient and Hessian give inexact jets.

## Implementation notes

* The space $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)` with the Euclidean norm, and $e_i$ is
  `EuclideanSpace.single i 1`. The forward-difference derivative and Hessian are continuous linear
  maps, and their errors are measured in the operator norm.
* The inexact jets are `Optimization.gradientJet` and `Optimization.hessianJet` of
  `Numlib.Optimization.ModelBased.InexactTaylor`. The Hessian of $f$ is
  `Optimization.hessianOperator f x`, the derivative of the gradient.
-/

open Finset
open scoped Nat RealInnerProductSpace

namespace FiniteDifference


/-! ### Coordinates of Euclidean space -/

section Euclid

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin n)

/-- If every coordinate of $w \in \mathbb{R}^n$ satisfies $|w_i| \le c$, then
$\|w\| \le \sqrt n\, c$.

This follows from `PiLp.norm_toLp_two_le_sqrt_card_mul_norm_toLp_top`. -/
theorem norm_le_sqrt_card_mul_of_forall_abs_le {w : 𝔼} {c : ℝ} (h : ∀ i, |w i| ≤ c) :
    ‖w‖ ≤ √n * c := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Subsingleton.elim w 0]
  have := PiLp.norm_toLp_two_le_sqrt_card_mul_norm_toLp_top (β := fun _ : Fin n => ℝ)
    (WithLp.ofLp w)
  simp only [WithLp.toLp_ofLp, Fintype.card_fin] at this
  refine this.trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
  rw [PiLp.norm_eq_ciSup]
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact ciSup_le fun i => by simpa using h i

/-- For $v \in \mathbb{R}^n$, $\sum_i |v_i| \le \sqrt n\, \|v\|$.

This follows from `PiLp.norm_toLp_one_le_sqrt_card_mul_norm_toLp_two`. -/
theorem sum_abs_le_sqrt_card_mul_norm (v : 𝔼) : ∑ i, |v i| ≤ √n * ‖v‖ := by
  have := PiLp.norm_toLp_one_le_sqrt_card_mul_norm_toLp_two (β := fun _ : Fin n => ℝ)
    (WithLp.ofLp v)
  simpa [PiLp.norm_eq_of_L1, Real.norm_eq_abs] using this

/-- A vector $v \in \mathbb{R}^n$ is the sum $\sum_j v_j e_j$ of its coordinates times the unit
vectors. -/
theorem sum_smul_single (v : 𝔼) : ∑ j, v j • EuclideanSpace.single j (1 : ℝ) = v := by
  ext i
  simp [Pi.single_apply]

end Euclid

/-! ### Forward-difference gradient -/

section Gradient

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin n)

/-- The **forward-difference gradient** ([cartis2022evaluation], §13.2). For
$f : \mathbb{R}^n \to \mathbb{R}$, a step $h$ and a point $x$, it is the vector with the
coordinates
$$[\overline\nabla f(x)]_i = \frac{f(x + h e_i) - f(x)}{h}, \qquad i = 1, \dots, n.$$
It is $0$ at $h = 0$. -/
noncomputable def fdGradient (f : 𝔼 → ℝ) (h : ℝ) (x : 𝔼) : 𝔼 :=
  WithLp.toLp 2 fun i => (f (x + h • EuclideanSpace.single i 1) - f x) / h

/-- The $i$-th coordinate of the forward-difference gradient is $(f(x + h e_i) - f(x))/h$. -/
@[simp]
theorem fdGradient_apply (f : 𝔼 → ℝ) (h : ℝ) (x : 𝔼) (i : Fin n) :
    fdGradient f h x i = (f (x + h • EuclideanSpace.single i 1) - f x) / h :=
  rfl

/-- **Forward-difference gradient error on a convex set.** Let $C \subseteq \mathbb{R}^n$ be convex,
let $f : \mathbb{R}^n \to \mathbb{R}$ be continuously differentiable at every point of $C$, and
let its derivative satisfy $\|f'(y) - f'(z)\| \le L \|y - z\|$ for $y, z \in C$. Let $h > 0$,
$x \in C$ and $x + h e_i \in C$ for every $i$. Then
$$\|\overline\nabla f(x) - \nabla f(x)\| \le \frac{\sqrt n\, L h}{2}.$$

The Lipschitz condition is `IteratedFDerivLipschitzOn f 1 L C`, a condition on the first
iterated derivative. -/
theorem norm_fdGradient_sub_gradient_le_of_convex {f : 𝔼 → ℝ} {L h : ℝ} {C : Set 𝔼} {x : 𝔼}
    (hC : Convex ℝ C) (hf : ∀ y ∈ C, ContDiffAt ℝ 1 f y) (hL : IteratedFDerivLipschitzOn f 1 L C)
    (hx : x ∈ C) (hxe : ∀ i, x + h • EuclideanSpace.single i (1 : ℝ) ∈ C) (hh : 0 < h) :
    ‖fdGradient f h x - gradient f x‖ ≤ √n * L / 2 * h := by
  rw [mul_div_assoc, mul_assoc]
  refine norm_le_sqrt_card_mul_of_forall_abs_le fun i => ?_
  have hb := norm_sub_sub_fderiv_le_of_lipschitz hC hf hL hx (hxe i)
  rw [map_smul, smul_eq_mul, norm_smul, PiLp.norm_single, norm_one, mul_one,
    Real.norm_of_nonneg hh.le, Real.norm_eq_abs] at hb
  have : fdGradient f h x i - gradient f x i =
      (f (x + h • EuclideanSpace.single i 1) - f x - h * fderiv ℝ f x (EuclideanSpace.single i 1)) /
        h := by
    rw [fdGradient_apply, EuclideanSpace.gradient_apply]
    field_simp
  rw [PiLp.sub_apply, this, abs_div, abs_of_pos hh, div_le_iff₀ hh]
  calc _ ≤ L / 2 * h ^ 2 := hb
    _ = L / 2 * h * h := by ring

/-- **Forward-difference gradient error** ([cartis2022evaluation], §13.2, first display). Let
$f : \mathbb{R}^n \to \mathbb{R}$ be continuously differentiable with
$\|f'(y) - f'(z)\| \le L \|y - z\|$ for all $y, z$, and let $h > 0$. Then for every $x$,
$$\|\overline\nabla f(x) - \nabla f(x)\| \le \frac{\sqrt n\, L h}{2}.$$
-/
theorem norm_fdGradient_sub_gradient_le {f : 𝔼 → ℝ} {L h : ℝ} (hf : ContDiff ℝ 1 f)
    (hL : ∀ y z, ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ L * ‖y - z‖) (hh : 0 < h) (x : 𝔼) :
    ‖fdGradient f h x - gradient f x‖ ≤ √n * L / 2 * h :=
  norm_fdGradient_sub_gradient_le_of_convex convex_univ (fun _ _ => hf.contDiffAt)
    (iteratedFDerivLipschitzOn_one_iff.2 fun y _ z _ => hL y z) (Set.mem_univ x)
    (fun _ => Set.mem_univ _) hh

end Gradient


/-! ### Forward-difference derivatives of maps -/

section Jacobian

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "𝔼" => EuclideanSpace ℝ (Fin n)

/-- The **forward-difference derivative** of a map $g : \mathbb{R}^n \to F$ into a normed space
([cartis2022evaluation], §13.2). For a step $h$ and a point $x$, it is the linear map
$\mathbb{R}^n \to F$ whose $j$-th column is
$$\frac{g(x + h e_j) - g(x)}{h},$$
that is, $v \mapsto \sum_j v_j\, h^{-1} (g(x + h e_j) - g(x))$. It is $0$ at $h = 0$.

For $g = \nabla f$ this is the forward-difference Hessian `FiniteDifference.fdHessian`. -/
noncomputable def fdFDeriv (g : 𝔼 → F) (h : ℝ) (x : 𝔼) : 𝔼 →L[ℝ] F :=
  ∑ j, (EuclideanSpace.proj j : 𝔼 →L[ℝ] ℝ).smulRight
    (h⁻¹ • (g (x + h • EuclideanSpace.single j 1) - g x))

/-- The forward-difference derivative maps $v$ to $\sum_j v_j\, h^{-1} (g(x + h e_j) - g(x))$. -/
theorem fdFDeriv_apply (g : 𝔼 → F) (h : ℝ) (x v : 𝔼) :
    fdFDeriv g h x v = ∑ j, v j • h⁻¹ • (g (x + h • EuclideanSpace.single j 1) - g x) := by
  simp [fdFDeriv]

/-- The $j$-th column of the forward-difference derivative is $h^{-1} (g(x + h e_j) - g(x))$. -/
theorem fdFDeriv_apply_single (g : 𝔼 → F) (h : ℝ) (x : 𝔼) (j : Fin n) :
    fdFDeriv g h x (EuclideanSpace.single j 1) =
      h⁻¹ • (g (x + h • EuclideanSpace.single j 1) - g x) := by
  rw [fdFDeriv_apply]
  simp

/-- **Forward-difference derivative error on a convex set.** Let $F$ be a real normed space, let
$C \subseteq \mathbb{R}^n$ be convex, let $g : \mathbb{R}^n \to F$ be continuously
differentiable at every point of $C$, and let its derivative satisfy
$\|g'(y) - g'(z)\| \le L \|y - z\|$ for $y, z \in C$. Let $h > 0$, $x \in C$ and
$x + h e_j \in C$ for every $j$. Then, with $\overline\nabla g(x)$ the forward-difference
derivative,
$$\|\overline\nabla g(x) - g'(x)\| \le \frac{\sqrt n\, L h}{2}.$$

The Lipschitz condition is `IteratedFDerivLipschitzOn g 1 L C`, and the norm on the left is the
operator norm. -/
theorem norm_fdFDeriv_sub_le_of_convex {g : 𝔼 → F} {L h : ℝ} {C : Set 𝔼} {x : 𝔼}
    (hC : Convex ℝ C) (hg : ∀ y ∈ C, ContDiffAt ℝ 1 g y) (hL : IteratedFDerivLipschitzOn g 1 L C)
    (hx : x ∈ C) (hxe : ∀ j, x + h • EuclideanSpace.single j (1 : ℝ) ∈ C) (hh : 0 < h) :
    ‖fdFDeriv g h x - fderiv ℝ g x‖ ≤ √n * L / 2 * h := by
  -- each column has error at most `L h / 2`
  have hcol : ∀ j, ‖h⁻¹ • (g (x + h • EuclideanSpace.single j 1) - g x) -
      fderiv ℝ g x (EuclideanSpace.single j 1)‖ ≤ L / 2 * h := by
    intro j
    have hb := norm_sub_sub_fderiv_le_of_lipschitz hC hg hL hx (hxe j)
    rw [norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_of_nonneg hh.le,
      map_smul] at hb
    have : h⁻¹ • (g (x + h • EuclideanSpace.single j 1) - g x) -
        fderiv ℝ g x (EuclideanSpace.single j 1) =
        h⁻¹ • (g (x + h • EuclideanSpace.single j 1) - g x -
          h • fderiv ℝ g x (EuclideanSpace.single j 1)) := by
      rw [smul_sub (h⁻¹) _ (h • _), smul_smul, inv_mul_cancel₀ hh.ne', one_smul]
    rw [this, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hh.le)]
    calc h⁻¹ * ‖_‖ ≤ h⁻¹ * (L / 2 * h ^ 2) := by gcongr
      _ = L / 2 * h := by field_simp
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : fdFDeriv g h x - fderiv ℝ g x = 0 := by
      ext v
      simp [Subsingleton.elim v 0]
    simp [this]
  have hM : 0 ≤ L / 2 * h := (norm_nonneg _).trans (hcol ⟨0, hn⟩)
  have hM' : 0 ≤ √n * L / 2 * h := by
    rw [mul_div_assoc, mul_assoc]; positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hM' fun v => ?_
  have hv : (fdFDeriv g h x - fderiv ℝ g x) v = ∑ j, v j •
      (h⁻¹ • (g (x + h • EuclideanSpace.single j 1) - g x) -
        fderiv ℝ g x (EuclideanSpace.single j 1)) := by
    conv_lhs => rw [← sum_smul_single v]
    simp [map_sum, map_smul, smul_sub, Finset.sum_sub_distrib, fdFDeriv_apply_single]
  rw [hv]
  calc ‖∑ j, v j • _‖ ≤ ∑ j, |v j| * (L / 2 * h) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hcol j) (abs_nonneg _)
    _ = (∑ j, |v j|) * (L / 2 * h) := by rw [Finset.sum_mul]
    _ ≤ √n * ‖v‖ * (L / 2 * h) := by gcongr; exact sum_abs_le_sqrt_card_mul_norm v
    _ = √n * L / 2 * h * ‖v‖ := by ring

/-- **Forward-difference derivative error.** Let $F$ be a real normed space, let
$g : \mathbb{R}^n \to F$ be continuously differentiable with $\|g'(y) - g'(z)\| \le L \|y - z\|$
for all $y, z$, and let $h > 0$. Then for every $x$, with $\overline\nabla g(x)$ the
forward-difference derivative,
$$\|\overline\nabla g(x) - g'(x)\| \le \frac{\sqrt n\, L h}{2}.$$
-/
theorem norm_fdFDeriv_sub_le {g : 𝔼 → F} {L h : ℝ} (hg : ContDiff ℝ 1 g)
    (hL : ∀ y z, ‖fderiv ℝ g y - fderiv ℝ g z‖ ≤ L * ‖y - z‖) (hh : 0 < h) (x : 𝔼) :
    ‖fdFDeriv g h x - fderiv ℝ g x‖ ≤ √n * L / 2 * h :=
  norm_fdFDeriv_sub_le_of_convex convex_univ (fun _ _ => hg.contDiffAt)
    (iteratedFDerivLipschitzOn_one_iff.2 fun y _ z _ => hL y z) (Set.mem_univ x)
    (fun _ => Set.mem_univ _) hh

/-- The **forward-difference Hessian** ([cartis2022evaluation], §13.2, fourth display). For
$f : \mathbb{R}^n \to \mathbb{R}$, a step $h$ and a point $x$, it is the linear map
$\overline\nabla^2 f(x)$ on $\mathbb{R}^n$ with the entries
$$[\overline\nabla^2 f(x)]_{i,j} = \frac{[\nabla f(x + h e_j)]_i - [\nabla f(x)]_i}{h},$$
the forward-difference derivative of the gradient. -/
noncomputable def fdHessian (f : 𝔼 → ℝ) (h : ℝ) (x : 𝔼) : 𝔼 →L[ℝ] 𝔼 :=
  fdFDeriv (gradient f) h x

/-- The forward-difference Hessian is the forward-difference derivative of the gradient $\nabla f$.
-/
theorem fdHessian_eq (f : 𝔼 → ℝ) (h : ℝ) (x : 𝔼) :
    fdHessian f h x = fdFDeriv (gradient f) h x :=
  rfl

/-- **Forward-difference Hessian error** ([cartis2022evaluation], §13.2, fourth display). Let
$f : \mathbb{R}^n \to \mathbb{R}$ be of class $C^2$, let its Hessian satisfy $\|\nabla^2 f(y) -
\nabla^2 f(z)\| \le L \|y - z\|$ for all $y, z$, and let $h > 0$. Then for every $x$,
$$\|\overline\nabla^2 f(x) - \nabla^2 f(x)\| \le \frac{\sqrt n\, L h}{2}.$$

The Hessian $\nabla^2 f(y)$ is `Optimization.hessianOperator f y`, and the norms are operator
norms. -/
theorem norm_fdHessian_sub_hessianOperator_le {f : 𝔼 → ℝ} {L h : ℝ} (hf : ContDiff ℝ 2 f)
    (hL : ∀ y z, ‖Optimization.hessianOperator f y - Optimization.hessianOperator f z‖ ≤
      L * ‖y - z‖) (hh : 0 < h) (x : 𝔼) :
    ‖fdHessian f h x - Optimization.hessianOperator f x‖ ≤ √n * L / 2 * h := by
  have hg : ContDiff ℝ 1 (gradient f) := by
    rw [gradient_eq_toDualReal_symm]
    exact (InnerProductSpace.toDualReal 𝔼).symm.toContinuousLinearEquiv.contDiff.comp
      (hf.fderiv_right (m := 1) (by norm_num))
  exact norm_fdFDeriv_sub_le hg hL hh x

/-- The forward-difference Hessian gives an **inexact jet of order $2$** ((13.1.2) of
[cartis2022evaluation] with $o = 1$). Under the hypotheses of
`FiniteDifference.norm_fdHessian_sub_hessianOperator_le`, let $D$ be the Taylor jet of $f$ at
$x$ and let $\overline D$ be $D$ with its second-order term replaced by the bilinear form $(u,
w) \mapsto \langle u, \overline\nabla^2 f(x)\, w \rangle$. Then $\overline D$ approximates $D$
up to order $2$ with error $0$ at order $1$ and error $\sqrt n\, L h/2$ at order $2$:
$$\|\overline D_1 - D_1\| \le 0, \qquad \|\overline D_2 - D_2\| \le \frac{\sqrt n\, L h}{2}.$$

The modified jet is `Optimization.hessianJet`. The jet $D$ is `ftaylorSeries ℝ f x`. -/
theorem jetApprox_fdHessian {f : 𝔼 → ℝ} {L h : ℝ} (hf : ContDiff ℝ 2 f)
    (hL : ∀ y z, ‖Optimization.hessianOperator f y - Optimization.hessianOperator f z‖ ≤
      L * ‖y - z‖) (hh : 0 < h) (x : 𝔼) :
    Optimization.JetApprox (ftaylorSeries ℝ f x)
      (Optimization.hessianJet (ftaylorSeries ℝ f x) (fdHessian f h x)) 2
      (fun i => if i = 2 then √n * L / 2 * h else 0) :=
  Optimization.jetApprox_hessianJet hf.contDiffAt (norm_fdHessian_sub_hessianOperator_le hf hL hh x)

end Jacobian

section GradientJet

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin n)

/-- The forward-difference gradient gives an **inexact jet of order $1$** ((13.1.2) of
[cartis2022evaluation] with $o = 0$). Under the hypotheses of
`FiniteDifference.norm_fdGradient_sub_gradient_le`, let $D$ be the Taylor jet of $f$ at $x$ and
let $\overline D$ be $D$ with its first-order term replaced by the linear form $v \mapsto
\langle \overline\nabla f(x), v \rangle$. Then
$$\|\overline D_1 - D_1\| \le \frac{\sqrt n\, L h}{2}.$$

The modified jet is `Optimization.gradientJet`, and the approximation is `Optimization.JetApprox`
with the constant error $\sqrt n\, L h/2$. The jet $D$ is `ftaylorSeries ℝ f x`. -/
theorem jetApprox_fdGradient {f : 𝔼 → ℝ} {L h : ℝ} (hf : ContDiff ℝ 1 f)
    (hL : ∀ y z, ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ L * ‖y - z‖) (hh : 0 < h) (x : 𝔼) :
    Optimization.JetApprox (ftaylorSeries ℝ f x)
      (Optimization.gradientJet (ftaylorSeries ℝ f x) (fdGradient f h x)) 1
      (fun _ => √n * L / 2 * h) :=
  Optimization.jetApprox_gradientJet (norm_fdGradient_sub_gradient_le hf hL hh x)

end GradientJet

end FiniteDifference

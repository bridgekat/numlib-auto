/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The Laplacian in polar and spherical coordinates

Let $f$ be a twice continuously differentiable function on a Euclidean plane or a Euclidean
three-space. This module writes the Laplacian $\Delta f = \sum_i \partial^2 f / \partial x_i^2$
along the coordinate curves of polar and of spherical coordinates:
$$\Delta = \frac{\partial^2}{\partial r^2} + \frac{1}{r} \frac{\partial}{\partial r} + \frac{1}{r^2}
  \frac{\partial^2}{\partial \theta^2}$$
in the plane, and
$$\Delta = \frac{\partial^2}{\partial r^2} + \frac{2}{r} \frac{\partial}{\partial r} + \frac{1}{r^2}
  \Bigl(\frac{1}{\sin^2 \varphi} \frac{\partial^2}{\partial \theta^2} + \cot \varphi
  \frac{\partial}{\partial \varphi} + \frac{\partial^2}{\partial \varphi^2}\Bigr)$$
in three-space.

The point with given coordinates is expressed in an arbitrary orthonormal frame $v$. Hence the
statements apply to every real inner product space of dimension two or three. The Laplacian is
`InnerProductSpace.laplacian`, whose value does not depend on the frame used to compute it.

## Main definitions

* `Curvilinear.polarPoint`: the point $r \cos\theta\, v_0 + r \sin\theta\, v_1$.
* `Curvilinear.sphericalPoint`: the point with coordinates $x_1 = r \cos\theta \sin\varphi$,
  $x_2 = r \sin\theta \sin\varphi$ and $x_3 = r \cos\varphi$.

## Main results

* `deriv_comp_curve`, `deriv_deriv_comp_curve`: the first and second derivatives of $f \circ \gamma$
  along a curve $\gamma$. The second is the chain rule together with the product rule, $(f \circ
  \gamma)'' = D^2 f(\gamma', \gamma') + Df(\gamma'')$, and it makes both coordinate computations
  short.
* `Curvilinear.laplacian_eq_polar`, `Curvilinear.laplacian_eq_spherical`: the two displayed
  identities.

## Implementation notes

* The proofs do not use the symmetry of the second derivative: the mixed terms cancel between the
  radial and the angular contributions in the order in which they arise.
* No rotated orthonormal basis is built. The Laplacian is evaluated once in the frame $v$, the
  coordinate frame is expanded in $v$ by bilinearity, and the identity then reduces to
  $\cos^2 + \sin^2 = 1$ on each of the four (respectively twelve) coefficients.
* The derivatives along the coordinate curves are ordinary derivatives `deriv` of the functions
  $s \mapsto f(\text{point}(s, \dots))$ of one real variable.
-/

open InnerProductSpace Laplacian

section Curve

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The **chain rule along a curve**. Let $E$ and $F$ be real normed spaces, let
$\gamma : \mathbb{R} \to E$ have the derivative $w$ at $t$, and let $f : E \to F$ be
differentiable at $\gamma(t)$. Then $s \mapsto f(\gamma(s))$ has the derivative
$Df(\gamma(t))\, w$ at $t$. -/
theorem hasDerivAt_comp_curve {f : E → F} {γ : ℝ → E} {w : E} {t : ℝ}
    (hf : DifferentiableAt ℝ f (γ t)) (hγ : HasDerivAt γ w t) :
    HasDerivAt (fun s => f (γ s)) (fderiv ℝ f (γ t) w) t :=
  hf.hasFDerivAt.comp_hasDerivAt t hγ

/-- Let $f : E \to F$ be differentiable, and let $\gamma : \mathbb{R} \to E$ have the derivative
$\gamma'(s)$ at every $s$. Then the derivative of $f \circ \gamma$ is the function
$s \mapsto Df(\gamma(s))\, \gamma'(s)$. -/
theorem deriv_comp_curve {f : E → F} {γ γ' : ℝ → E} (hf : Differentiable ℝ f)
    (hγ : ∀ s, HasDerivAt γ (γ' s) s) :
    deriv (fun s => f (γ s)) = fun s => fderiv ℝ f (γ s) (γ' s) :=
  funext fun s => (hasDerivAt_comp_curve (hf _) (hγ s)).deriv

/-- The **second derivative along a curve**. Let $f : E \to F$ be $C^2$, let
$\gamma : \mathbb{R} \to E$ have the derivative $\gamma'(s)$ at every $s$, and let $\gamma'$
have the derivative $a$ at $t$. Then
$$(f \circ \gamma)''(t) = D^2 f(\gamma(t))\bigl(\gamma'(t), \gamma'(t)\bigr) + Df(\gamma(t))\,
  a.$$

The second derivative $D^2 f$ is `fderiv ℝ (fderiv ℝ f)`, and $(f \circ \gamma)''$ is
`deriv (deriv (f ∘ γ))`. -/
theorem deriv_deriv_comp_curve {f : E → F} {γ γ' : ℝ → E} {a : E} {t : ℝ}
    (hf : ContDiff ℝ 2 f) (hγ : ∀ s, HasDerivAt γ (γ' s) s) (hγ' : HasDerivAt γ' a t) :
    deriv (deriv fun s => f (γ s)) t
      = fderiv ℝ (fderiv ℝ f) (γ t) (γ' t) (γ' t) + fderiv ℝ f (γ t) a := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) le_rfl).differentiable (by norm_num)
  rw [deriv_comp_curve hd hγ]
  exact (((hd2 _).hasFDerivAt.comp_hasDerivAt t (hγ t)).clm_apply hγ').deriv

end Curve

namespace Curvilinear

open Real

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### Polar coordinates in the plane -/

/-- Let $v = (v_0, v_1)$ be an orthonormal basis of a real inner product space $E$ of dimension two.
The point with **polar coordinates** $(r, \theta)$ in the frame $v$ is
$r \cos\theta\, v_0 + r \sin\theta\, v_1$, that is $x_1 = r \cos\theta$ and
$x_2 = r \sin\theta$.

The radius $r$ may be any real number, including $0$ and negative values. -/
noncomputable def polarPoint (v : OrthonormalBasis (Fin 2) ℝ E) (r θ : ℝ) : E :=
  (r * cos θ) • v 0 + (r * sin θ) • v 1

/-- The velocity $-r \sin\theta\, v_0 + r \cos\theta\, v_1$ of the circle $\theta \mapsto$
`Curvilinear.polarPoint v r θ` of radius $r$. -/
noncomputable def polarAngularVel (v : OrthonormalBasis (Fin 2) ℝ E) (r θ : ℝ) : E :=
  (r * -sin θ) • v 0 + (r * cos θ) • v 1

variable (v : OrthonormalBasis (Fin 2) ℝ E)

/-- The ray $s \mapsto$ `Curvilinear.polarPoint v s θ` has at every $t$ the derivative
$\cos\theta\, v_0 + \sin\theta\, v_1$, the point with polar coordinates $(1, \theta)$. -/
theorem hasDerivAt_polarPoint_fst (θ t : ℝ) :
    HasDerivAt (fun s : ℝ => polarPoint v s θ) (polarPoint v 1 θ) t :=
  (((hasDerivAt_id t).mul_const (cos θ)).smul_const (v 0)).add
    (((hasDerivAt_id t).mul_const (sin θ)).smul_const (v 1))

/-- The circle $\psi \mapsto$ `Curvilinear.polarPoint v r ψ` has at $\theta$ the derivative
$-r \sin\theta\, v_0 + r \cos\theta\, v_1$, which is `Curvilinear.polarAngularVel v r θ`. -/
theorem hasDerivAt_polarPoint_snd (r θ : ℝ) :
    HasDerivAt (fun ψ : ℝ => polarPoint v r ψ) (polarAngularVel v r θ) θ :=
  (((Real.hasDerivAt_cos θ).const_mul r).smul_const (v 0)).add
    (((Real.hasDerivAt_sin θ).const_mul r).smul_const (v 1))

/-- The velocity of the circle of radius $r$ has at $\theta$ the derivative
$-r \cos\theta\, v_0 - r \sin\theta\, v_1$, which is minus the point with polar coordinates
$(r, \theta)$: the acceleration points to the centre. -/
theorem hasDerivAt_polarAngularVel (r θ : ℝ) :
    HasDerivAt (fun ψ : ℝ => polarAngularVel v r ψ)
      ((r * -cos θ) • v 0 + (r * -sin θ) • v 1) θ :=
  ((((Real.hasDerivAt_sin θ).neg).const_mul r).smul_const (v 0)).add
    (((Real.hasDerivAt_cos θ).const_mul r).smul_const (v 1))

/-- The **Laplacian in polar coordinates**. Let $E$ be a real inner product space of dimension two
with an orthonormal basis $v$, let $f : E \to F$ be $C^2$, let $r \neq 0$, and let
$\theta \in \mathbb{R}$. At the point $x$ with polar coordinates $(r, \theta)$,
$$\Delta f(x) = \frac{\partial^2 f}{\partial r^2} + \frac{1}{r} \frac{\partial f}{\partial r} +
  \frac{1}{r^2} \frac{\partial^2 f}{\partial \theta^2}.$$
The derivatives on the right are taken along the ray of angle $\theta$, $s \mapsto$
`Curvilinear.polarPoint v s θ`, at $s = r$, and along the circle of radius $r$, $\psi \mapsto$
`Curvilinear.polarPoint v r ψ`, at $\psi = \theta$.

The dimension of $E$ is fixed by the orthonormal basis indexed by `Fin 2`. The Laplacian is
`InnerProductSpace.laplacian`, and the derivatives are `deriv` of functions of one real
variable. -/
theorem laplacian_eq_polar [FiniteDimensional ℝ E] {f : E → F} (hf : ContDiff ℝ 2 f)
    {r : ℝ} (hr : r ≠ 0) (θ : ℝ) :
    Δ f (polarPoint v r θ)
      = deriv (deriv fun s : ℝ => f (polarPoint v s θ)) r
        + r⁻¹ • deriv (fun s : ℝ => f (polarPoint v s θ)) r
        + (r ^ 2)⁻¹ • deriv (deriv fun ψ : ℝ => f (polarPoint v r ψ)) θ := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hrad2 := deriv_deriv_comp_curve (f := f) (γ := fun s : ℝ => polarPoint v s θ)
    (γ' := fun _ : ℝ => polarPoint v 1 θ) (a := 0) (t := r) hf
    (fun s => hasDerivAt_polarPoint_fst v θ s) (hasDerivAt_const r _)
  have hrad1 := congrFun (deriv_comp_curve (f := f) (γ := fun s : ℝ => polarPoint v s θ)
    (γ' := fun _ : ℝ => polarPoint v 1 θ) hd (fun s => hasDerivAt_polarPoint_fst v θ s)) r
  have hang2 := deriv_deriv_comp_curve (f := f) (γ := fun ψ : ℝ => polarPoint v r ψ)
    (γ' := fun ψ : ℝ => polarAngularVel v r ψ)
    (a := (r * -cos θ) • v 0 + (r * -sin θ) • v 1) (t := θ) hf
    (fun ψ => hasDerivAt_polarPoint_snd v r ψ) (hasDerivAt_polarAngularVel v r θ)
  rw [hrad2, hrad1, hang2, laplacian_eq_iteratedFDeriv_orthonormalBasis f v]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.sum_univ_two, polarPoint, polarAngularVel, map_add, map_smul, map_zero, add_apply,
    smul_apply, smul_add, smul_smul, add_zero]
  match_scalars <;> field_simp <;> (try simp only [Real.cos_sq']) <;> ring

/-! ### Spherical coordinates in three-space -/

/-- Let $w = (w_0, w_1, w_2)$ be an orthonormal basis of a real inner product space $E$ of dimension
three. The point with **spherical coordinates** $(r, \theta, \varphi)$ in the frame $w$ has the
coordinates $x_1 = r \cos\theta \sin\varphi$, $x_2 = r \sin\theta \sin\varphi$ and
$x_3 = r \cos\varphi$.

Here $\theta$ is the azimuth and $\varphi$ the inclination from the axis $w_2$. -/
noncomputable def sphericalPoint (v : OrthonormalBasis (Fin 3) ℝ E) (r θ φ : ℝ) : E :=
  (r * cos θ * sin φ) • v 0 + (r * sin θ * sin φ) • v 1 + (r * cos φ) • v 2

/-- The velocity $-r \sin\theta \sin\varphi\, w_0 + r \cos\theta \sin\varphi\, w_1$ of the circle of
latitude $\theta \mapsto$ `Curvilinear.sphericalPoint w r θ φ`. -/
noncomputable def sphericalAzimuthVel (v : OrthonormalBasis (Fin 3) ℝ E) (r θ φ : ℝ) : E :=
  (r * -sin θ * sin φ) • v 0 + (r * cos θ * sin φ) • v 1 + (0 : ℝ) • v 2

/-- The velocity $r \cos\theta \cos\varphi\, w_0 + r \sin\theta \cos\varphi\, w_1 - r \sin\varphi\,
w_2$ of the circle of longitude $\varphi \mapsto$ `Curvilinear.sphericalPoint w r θ φ`. -/
noncomputable def sphericalInclinationVel (v : OrthonormalBasis (Fin 3) ℝ E) (r θ φ : ℝ) : E :=
  (r * cos θ * cos φ) • v 0 + (r * sin θ * cos φ) • v 1 + (r * -sin φ) • v 2

variable (w : OrthonormalBasis (Fin 3) ℝ E)

/-- The ray $s \mapsto$ `Curvilinear.sphericalPoint w s θ φ` has at every $t$ the derivative given
by the point with spherical coordinates $(1, \theta, \varphi)$. -/
theorem hasDerivAt_sphericalPoint_fst (θ φ t : ℝ) :
    HasDerivAt (fun s : ℝ => sphericalPoint w s θ φ) (sphericalPoint w 1 θ φ) t :=
  (((((hasDerivAt_id t).mul_const (cos θ)).mul_const (sin φ)).smul_const (w 0)).add
    ((((hasDerivAt_id t).mul_const (sin θ)).mul_const (sin φ)).smul_const (w 1))).add
      (((hasDerivAt_id t).mul_const (cos φ)).smul_const (w 2))

/-- The circle of latitude $\psi \mapsto$ `Curvilinear.sphericalPoint w r ψ φ` has at $\theta$ the
derivative `Curvilinear.sphericalAzimuthVel w r θ φ`. -/
theorem hasDerivAt_sphericalPoint_snd (r θ φ : ℝ) :
    HasDerivAt (fun ψ : ℝ => sphericalPoint w r ψ φ) (sphericalAzimuthVel w r θ φ) θ :=
  (((((Real.hasDerivAt_cos θ).const_mul r).mul_const (sin φ)).smul_const (w 0)).add
    ((((Real.hasDerivAt_sin θ).const_mul r).mul_const (sin φ)).smul_const (w 1))).add
      ((hasDerivAt_const θ (r * cos φ)).smul_const (w 2))

/-- The velocity of the circle of latitude has at $\theta$ the derivative $-r \cos\theta
\sin\varphi\, w_0 - r \sin\theta \sin\varphi\, w_1$. This acceleration points to the centre of
the circle of latitude, which lies on the axis $w_2$ and not at the origin. -/
theorem hasDerivAt_sphericalAzimuthVel (r θ φ : ℝ) :
    HasDerivAt (fun ψ : ℝ => sphericalAzimuthVel w r ψ φ)
      ((r * -cos θ * sin φ) • w 0 + (r * -sin θ * sin φ) • w 1 + (0 : ℝ) • w 2) θ :=
  ((((((Real.hasDerivAt_sin θ).neg).const_mul r).mul_const (sin φ)).smul_const (w 0)).add
    ((((Real.hasDerivAt_cos θ).const_mul r).mul_const (sin φ)).smul_const (w 1))).add
      ((hasDerivAt_const θ (0 : ℝ)).smul_const (w 2))

/-- The circle of longitude $\chi \mapsto$ `Curvilinear.sphericalPoint w r θ χ` has at $\varphi$ the
derivative `Curvilinear.sphericalInclinationVel w r θ φ`. -/
theorem hasDerivAt_sphericalPoint_thd (r θ φ : ℝ) :
    HasDerivAt (fun χ : ℝ => sphericalPoint w r θ χ) (sphericalInclinationVel w r θ φ) φ :=
  ((((Real.hasDerivAt_sin φ).const_mul (r * cos θ)).smul_const (w 0)).add
    (((Real.hasDerivAt_sin φ).const_mul (r * sin θ)).smul_const (w 1))).add
      (((Real.hasDerivAt_cos φ).const_mul r).smul_const (w 2))

/-- The velocity of the circle of longitude has at $\varphi$ the derivative $-r \cos\theta
\sin\varphi\, w_0 - r \sin\theta \sin\varphi\, w_1 - r \cos\varphi\, w_2$, which is minus the
point with spherical coordinates $(r, \theta, \varphi)$: the acceleration points to the origin. -/
theorem hasDerivAt_sphericalInclinationVel (r θ φ : ℝ) :
    HasDerivAt (fun χ : ℝ => sphericalInclinationVel w r θ χ)
      ((r * cos θ * -sin φ) • w 0 + (r * sin θ * -sin φ) • w 1 + (r * -cos φ) • w 2) φ :=
  ((((Real.hasDerivAt_cos φ).const_mul (r * cos θ)).smul_const (w 0)).add
    (((Real.hasDerivAt_cos φ).const_mul (r * sin θ)).smul_const (w 1))).add
      ((((Real.hasDerivAt_sin φ).neg).const_mul r).smul_const (w 2))

/-- The **Laplacian in spherical coordinates**. Let $E$ be a real inner product space of dimension
three with an orthonormal basis $w$, let $f : E \to F$ be $C^2$, let $r \neq 0$ and
$\sin\varphi \neq 0$, and let $\theta \in \mathbb{R}$. At the point $x$ with spherical
coordinates $(r, \theta, \varphi)$,
$$\Delta f(x) = \frac{\partial^2 f}{\partial r^2} + \frac{2}{r} \frac{\partial f}{\partial r} +
  \frac{1}{r^2} \Bigl(\frac{1}{\sin^2 \varphi} \frac{\partial^2 f}{\partial \theta^2} +
  \frac{\cos\varphi}{\sin\varphi} \frac{\partial f}{\partial \varphi} + \frac{\partial^2
  f}{\partial \varphi^2}\Bigr).$$
The derivatives on the right are taken along the ray through $x$ at $s = r$, along its circle of
latitude at $\psi = \theta$, and along its circle of longitude at $\chi = \varphi$.

The dimension of $E$ is fixed by the orthonormal basis indexed by `Fin 3`. The Laplacian is
`InnerProductSpace.laplacian`, and the derivatives are `deriv` of functions of one real
variable. -/
theorem laplacian_eq_spherical [FiniteDimensional ℝ E] {f : E → F} (hf : ContDiff ℝ 2 f)
    {r φ : ℝ} (hr : r ≠ 0) (hφ : sin φ ≠ 0) (θ : ℝ) :
    Δ f (sphericalPoint w r θ φ)
      = deriv (deriv fun s : ℝ => f (sphericalPoint w s θ φ)) r
        + (2 / r) • deriv (fun s : ℝ => f (sphericalPoint w s θ φ)) r
        + (r ^ 2)⁻¹ • ((sin φ ^ 2)⁻¹ • deriv (deriv fun ψ : ℝ => f (sphericalPoint w r ψ φ)) θ
            + (cos φ / sin φ) • deriv (fun χ : ℝ => f (sphericalPoint w r θ χ)) φ
            + deriv (deriv fun χ : ℝ => f (sphericalPoint w r θ χ)) φ) := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hrad2 := deriv_deriv_comp_curve (f := f) (γ := fun s : ℝ => sphericalPoint w s θ φ)
    (γ' := fun _ : ℝ => sphericalPoint w 1 θ φ) (a := 0) (t := r) hf
    (fun s => hasDerivAt_sphericalPoint_fst w θ φ s) (hasDerivAt_const r _)
  have hrad1 := congrFun (deriv_comp_curve (f := f) (γ := fun s : ℝ => sphericalPoint w s θ φ)
    (γ' := fun _ : ℝ => sphericalPoint w 1 θ φ) hd
    (fun s => hasDerivAt_sphericalPoint_fst w θ φ s)) r
  have hazi2 := deriv_deriv_comp_curve (f := f) (γ := fun ψ : ℝ => sphericalPoint w r ψ φ)
    (γ' := fun ψ : ℝ => sphericalAzimuthVel w r ψ φ)
    (a := (r * -cos θ * sin φ) • w 0 + (r * -sin θ * sin φ) • w 1 + (0 : ℝ) • w 2) (t := θ) hf
    (fun ψ => hasDerivAt_sphericalPoint_snd w r ψ φ) (hasDerivAt_sphericalAzimuthVel w r θ φ)
  have hinc2 := deriv_deriv_comp_curve (f := f) (γ := fun χ : ℝ => sphericalPoint w r θ χ)
    (γ' := fun χ : ℝ => sphericalInclinationVel w r θ χ)
    (a := (r * cos θ * -sin φ) • w 0 + (r * sin θ * -sin φ) • w 1 + (r * -cos φ) • w 2)
    (t := φ) hf
    (fun χ => hasDerivAt_sphericalPoint_thd w r θ χ) (hasDerivAt_sphericalInclinationVel w r θ φ)
  have hinc1 := congrFun (deriv_comp_curve (f := f) (γ := fun χ : ℝ => sphericalPoint w r θ χ)
    (γ' := fun χ : ℝ => sphericalInclinationVel w r θ χ) hd
    (fun χ => hasDerivAt_sphericalPoint_thd w r θ χ)) φ
  rw [hrad2, hrad1, hazi2, hinc2, hinc1, laplacian_eq_iteratedFDeriv_orthonormalBasis f w]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.sum_univ_three, sphericalPoint, sphericalAzimuthVel, sphericalInclinationVel, map_add,
    map_smul, map_zero, add_apply, smul_apply, smul_add, smul_smul, add_zero]
  match_scalars <;> field_simp <;> (try simp only [Real.cos_sq']) <;> ring

end Curvilinear

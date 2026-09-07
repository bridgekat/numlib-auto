import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The Laplacian in polar and spherical coordinates

The Laplacian `Δ = ∑ᵢ ∂²/∂xᵢ²` of a twice continuously differentiable function on a Euclidean plane
or a Euclidean three-space, rewritten along the coordinate curves of polar and of spherical
coordinates:

`Δ = ∂²/∂r² + r⁻¹ ∂/∂r + r⁻² ∂²/∂θ²` in the plane, and
`Δ = ∂²/∂r² + 2 r⁻¹ ∂/∂r + r⁻² ((sin φ)⁻² ∂²/∂θ² + cot φ ∂/∂φ + ∂²/∂φ²)` in three-space.

The point of the plane (respectively of three-space) at given coordinates is expressed in an
arbitrary orthonormal frame `v`, so that the statements apply to any two- or three-dimensional real
inner product space; `Δ` is `InnerProductSpace.laplacian`, whose value does not depend on the frame
used to compute it.

## Main definitions

* `Curvilinear.polarPoint v r θ` — the point `r cos θ • v 0 + r sin θ • v 1`.
* `Curvilinear.sphericalPoint v r θ φ` — the point with `x₁ = r cos θ sin φ`,
  `x₂ = r sin θ sin φ` and `x₃ = r cos φ`.

## Main results

* `deriv_comp_curve` and `deriv_deriv_comp_curve` — the first and second derivatives of `f ∘ γ`
  along a curve, in terms of `fderiv ℝ f` and `fderiv ℝ (fderiv ℝ f)` at `γ t`. The second is the
  chain rule together with the product rule, `(f ∘ γ)'' = D²f(γ', γ') + Df(γ'')`, and it is what
  makes both coordinate computations short.
* `Curvilinear.laplacian_eq_polar` and `Curvilinear.laplacian_eq_spherical` — the two displayed
  identities.

## Implementation notes

Nothing here needs the symmetry of the second derivative: the mixed terms that appear already
cancel between the radial and the angular contributions, in the order in which they arise. No
rotated orthonormal basis is constructed either: the Laplacian is evaluated once and for all in the
frame `v`, the coordinate frame is expanded in `v` by bilinearity, and the identity then reduces to
`cos² + sin² = 1` on each of the four (respectively twelve) coefficients.
-/

open InnerProductSpace Laplacian

section Curve

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The chain rule along a curve: `(f ∘ γ)'(t) = Df(γ t) (γ' t)`. -/
theorem hasDerivAt_comp_curve {f : E → F} {γ : ℝ → E} {w : E} {t : ℝ}
    (hf : DifferentiableAt ℝ f (γ t)) (hγ : HasDerivAt γ w t) :
    HasDerivAt (fun s => f (γ s)) (fderiv ℝ f (γ t) w) t :=
  hf.hasFDerivAt.comp_hasDerivAt t hγ

/-- The derivative of `f ∘ γ`, as a function of the parameter. -/
theorem deriv_comp_curve {f : E → F} {γ γ' : ℝ → E} (hf : Differentiable ℝ f)
    (hγ : ∀ s, HasDerivAt γ (γ' s) s) :
    deriv (fun s => f (γ s)) = fun s => fderiv ℝ f (γ s) (γ' s) :=
  funext fun s => (hasDerivAt_comp_curve (hf _) (hγ s)).deriv

/-- **The second derivative of `f` along a curve**: `(f ∘ γ)'' = D²f(γ', γ') + Df(γ'')`. -/
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

/-- The point with polar coordinates `(r, θ)` in the orthonormal frame `v`: `x₁ = r cos θ` and
`x₂ = r sin θ`. -/
noncomputable def polarPoint (v : OrthonormalBasis (Fin 2) ℝ E) (r θ : ℝ) : E :=
  (r * cos θ) • v 0 + (r * sin θ) • v 1

/-- The velocity of the curve `θ ↦ polarPoint v r θ`, the circle of radius `r`. -/
noncomputable def polarAngularVel (v : OrthonormalBasis (Fin 2) ℝ E) (r θ : ℝ) : E :=
  (r * -sin θ) • v 0 + (r * cos θ) • v 1

variable (v : OrthonormalBasis (Fin 2) ℝ E)

/-- The ray `s ↦ polarPoint v s θ` has constant velocity `polarPoint v 1 θ`. -/
theorem hasDerivAt_polarPoint_fst (θ t : ℝ) :
    HasDerivAt (fun s : ℝ => polarPoint v s θ) (polarPoint v 1 θ) t :=
  (((hasDerivAt_id t).mul_const (cos θ)).smul_const (v 0)).add
    (((hasDerivAt_id t).mul_const (sin θ)).smul_const (v 1))

/-- The circle `θ ↦ polarPoint v r θ` has velocity `polarAngularVel v r θ`. -/
theorem hasDerivAt_polarPoint_snd (r θ : ℝ) :
    HasDerivAt (fun ψ : ℝ => polarPoint v r ψ) (polarAngularVel v r θ) θ :=
  (((Real.hasDerivAt_cos θ).const_mul r).smul_const (v 0)).add
    (((Real.hasDerivAt_sin θ).const_mul r).smul_const (v 1))

/-- The circle of radius `r` has acceleration `-polarPoint v r θ`, pointing at the centre. -/
theorem hasDerivAt_polarAngularVel (r θ : ℝ) :
    HasDerivAt (fun ψ : ℝ => polarAngularVel v r ψ)
      ((r * -cos θ) • v 0 + (r * -sin θ) • v 1) θ :=
  ((((Real.hasDerivAt_sin θ).neg).const_mul r).smul_const (v 0)).add
    (((Real.hasDerivAt_cos θ).const_mul r).smul_const (v 1))

/-- **The Laplacian in polar coordinates**: for `f` twice continuously differentiable on a Euclidean
plane and `r ≠ 0`,

`Δ f = ∂²f/∂r² + r⁻¹ ∂f/∂r + r⁻² ∂²f/∂θ²`,

the derivatives on the right being taken along the ray of angle `θ` and along the circle of radius
`r`. -/
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

/-- The point with spherical coordinates `(r, θ, φ)` in the orthonormal frame `v`:
`x₁ = r cos θ sin φ`, `x₂ = r sin θ sin φ` and `x₃ = r cos φ`. -/
noncomputable def sphericalPoint (v : OrthonormalBasis (Fin 3) ℝ E) (r θ φ : ℝ) : E :=
  (r * cos θ * sin φ) • v 0 + (r * sin θ * sin φ) • v 1 + (r * cos φ) • v 2

/-- The velocity of the curve `θ ↦ sphericalPoint v r θ φ`, a circle of latitude. -/
noncomputable def sphericalAzimuthVel (v : OrthonormalBasis (Fin 3) ℝ E) (r θ φ : ℝ) : E :=
  (r * -sin θ * sin φ) • v 0 + (r * cos θ * sin φ) • v 1 + (0 : ℝ) • v 2

/-- The velocity of the curve `φ ↦ sphericalPoint v r θ φ`, a circle of longitude. -/
noncomputable def sphericalInclinationVel (v : OrthonormalBasis (Fin 3) ℝ E) (r θ φ : ℝ) : E :=
  (r * cos θ * cos φ) • v 0 + (r * sin θ * cos φ) • v 1 + (r * -sin φ) • v 2

variable (w : OrthonormalBasis (Fin 3) ℝ E)

/-- The ray `s ↦ sphericalPoint w s θ φ` has constant velocity `sphericalPoint w 1 θ φ`. -/
theorem hasDerivAt_sphericalPoint_fst (θ φ t : ℝ) :
    HasDerivAt (fun s : ℝ => sphericalPoint w s θ φ) (sphericalPoint w 1 θ φ) t :=
  (((((hasDerivAt_id t).mul_const (cos θ)).mul_const (sin φ)).smul_const (w 0)).add
    ((((hasDerivAt_id t).mul_const (sin θ)).mul_const (sin φ)).smul_const (w 1))).add
      (((hasDerivAt_id t).mul_const (cos φ)).smul_const (w 2))

/-- The circle of latitude has velocity `sphericalAzimuthVel w r θ φ`. -/
theorem hasDerivAt_sphericalPoint_snd (r θ φ : ℝ) :
    HasDerivAt (fun ψ : ℝ => sphericalPoint w r ψ φ) (sphericalAzimuthVel w r θ φ) θ :=
  (((((Real.hasDerivAt_cos θ).const_mul r).mul_const (sin φ)).smul_const (w 0)).add
    ((((Real.hasDerivAt_sin θ).const_mul r).mul_const (sin φ)).smul_const (w 1))).add
      ((hasDerivAt_const θ (r * cos φ)).smul_const (w 2))

/-- The circle of latitude has acceleration pointing at the centre of that circle, which is on the
axis rather than at the origin. -/
theorem hasDerivAt_sphericalAzimuthVel (r θ φ : ℝ) :
    HasDerivAt (fun ψ : ℝ => sphericalAzimuthVel w r ψ φ)
      ((r * -cos θ * sin φ) • w 0 + (r * -sin θ * sin φ) • w 1 + (0 : ℝ) • w 2) θ :=
  ((((((Real.hasDerivAt_sin θ).neg).const_mul r).mul_const (sin φ)).smul_const (w 0)).add
    ((((Real.hasDerivAt_cos θ).const_mul r).mul_const (sin φ)).smul_const (w 1))).add
      ((hasDerivAt_const θ (0 : ℝ)).smul_const (w 2))

/-- The circle of longitude has velocity `sphericalInclinationVel w r θ φ`. -/
theorem hasDerivAt_sphericalPoint_thd (r θ φ : ℝ) :
    HasDerivAt (fun χ : ℝ => sphericalPoint w r θ χ) (sphericalInclinationVel w r θ φ) φ :=
  ((((Real.hasDerivAt_sin φ).const_mul (r * cos θ)).smul_const (w 0)).add
    (((Real.hasDerivAt_sin φ).const_mul (r * sin θ)).smul_const (w 1))).add
      (((Real.hasDerivAt_cos φ).const_mul r).smul_const (w 2))

/-- The circle of longitude has acceleration `-sphericalPoint w r θ φ`, pointing at the origin. -/
theorem hasDerivAt_sphericalInclinationVel (r θ φ : ℝ) :
    HasDerivAt (fun χ : ℝ => sphericalInclinationVel w r θ χ)
      ((r * cos θ * -sin φ) • w 0 + (r * sin θ * -sin φ) • w 1 + (r * -cos φ) • w 2) φ :=
  ((((Real.hasDerivAt_cos φ).const_mul (r * cos θ)).smul_const (w 0)).add
    (((Real.hasDerivAt_cos φ).const_mul (r * sin θ)).smul_const (w 1))).add
      ((((Real.hasDerivAt_sin φ).neg).const_mul r).smul_const (w 2))

/-- **The Laplacian in spherical coordinates**: for `f` twice continuously differentiable on a
Euclidean three-space, `r ≠ 0` and `sin φ ≠ 0`,

`Δ f = ∂²f/∂r² + 2 r⁻¹ ∂f/∂r + r⁻² ((sin φ)⁻² ∂²f/∂θ² + cot φ ∂f/∂φ + ∂²f/∂φ²)`,

the derivatives on the right being taken along the ray through the point, along its circle of
latitude and along its circle of longitude. -/
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

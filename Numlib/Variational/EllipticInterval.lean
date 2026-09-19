import Mathlib.MeasureTheory.Function.Holder
import Numlib.Analysis.Sobolev.Interval
import Numlib.Variational.Galerkin

/-!
# The elliptic two-point boundary value problem in weak form

The weak formulation of the one-dimensional elliptic problem

`-(α u')' + β u' + γ u = f` on `(a, b)`

with Dirichlet, Neumann or mixed boundary conditions ([quarteroni2000numerical] §12.4.1,
§12.4.3–12.4.4): the bilinear form `a(u, v) = ∫_a^b (α u' v' + β u' v + γ u v)` on
`H^1(a, b)`, its boundedness and coercivity constants, existence and uniqueness of the weak
solution in `H^1_0(a, b)` by Lax–Milgram with the stability estimate (12.51), the `H²`
regularity of the weak solution, and the Galerkin error bounds — Céa's lemma with the constant
of Theorem 12.3, and the Aubin–Nitsche `L²` estimate behind (12.60).

## Main definitions

* `EllipticInterval.form a b α β γ`, the bilinear form `(12.44)` as a `SesqForm ℝ (H^1(a, b))`,
  for coefficients `α β γ ∈ L^∞(a, b)` (the book has them continuous on `[a, b]`; `L^∞` costs
  nothing and covers piecewise constant coefficients);
* `EllipticInterval.load a b f`, the load functional `v ↦ ∫_a^b f v` for `f ∈ L²(a, b)`;
* `SesqForm.restrict a K`, the restriction of a bounded form to a subspace.

The weak problem on `H^1_0(a, b)` — find `u ∈ H^1_0` with `a(u, v) = (f, v)` for all
`v ∈ H^1_0` — is `IsGalerkinSolution (form a b α β γ) (load a b f) (SobolevIntervalZero a b) u`,
the Galerkin problem of `Numlib/Variational/Galerkin.lean` with the whole of `H^1_0(a, b)` as
trial space; a Galerkin approximation in a subspace `K ≤ H^1_0(a, b)` is the same predicate with
`K`. Nothing here distinguishes the continuous problem from its discretizations, which is what
lets the stability estimate (12.51) and Céa's lemma be stated once.

## Main statements

* `EllipticInterval.form_apply`: the form is the integral (12.44).
* `EllipticInterval.form_isBoundedWith`: boundedness `|a(u, v)| ≤ (‖α‖_∞ + ‖β‖_∞ + ‖γ‖_∞) ‖u‖ ‖v‖`
  in the `H^1` norm, and `EllipticInterval.abs_form_le_seminorm`, boundedness on `H^1_0(a, b)`
  in the seminorm with the constant `‖α‖_∞ + C_P ‖β‖_∞ + C_P² ‖γ‖_∞`, `C_P = (b - a)/√2`.
* `EllipticInterval.form_isCoerciveWith_seminorm`: coercivity `α₀ |v|² ≤ a(v, v)` in the
  seminorm for `α ≥ α₀`, `β = 0`, `γ ≥ 0`, and `EllipticInterval.form_isCoerciveWith_seminorm_of_le`
  under the book's condition (12.50), `-β'/2 + γ ≥ 0`, for `v ∈ H^1_0(a, b)`.
* `EllipticInterval.existsUnique_isWeakSolution`: **existence and uniqueness of the weak
  solution** by Lax–Milgram, with `EllipticInterval.seminorm_le_of_isGalerkinSolution`, the
  stability estimate `|u|_{H^1} ≤ (C_P/α₀) ‖f‖_{L²}` (12.51) for the solution in any subspace.
* `EllipticInterval.isWeakSolution_of_classical`: **a classical solution is a weak solution**,
  the derivation of (12.43); `EllipticInterval.isWeakSolution_of_classical_neumann`, the same
  for the Neumann and mixed problems, with the boundary terms.
* `EllipticInterval.galerkin_seminorm_sub_le`: **Céa's lemma with the constant of
  Theorem 12.3**, `|u - u_h| ≤ α₀⁻¹ (‖α‖_∞ + C_P² ‖γ‖_∞) |u - w_h|`.
* `EllipticInterval.isWeakSolution_mem_sobolevInterval_two`: **`H²` regularity** of the weak
  solution when `α` is `C¹`, and `EllipticInterval.galerkin_norm_sub_le_l2`, the Aubin–Nitsche
  `L²` estimate.

## Implementation notes

The form is assembled from three `L²` pairings `⟪T u^{(i)}, v^{(j)}⟫` of the components of
`H^1(a, b)`, where `T` is multiplication by an `L^∞` coefficient — Mathlib's Hölder product
`ContinuousLinearMap.holderL` at the exponents `(2, ∞, 2)` — so that continuity in both slots
is inherited and `form_apply` is a computation of inner products. The coefficients are
elements of `Lp ℝ ⊤`; a continuous coefficient enters through
`ContinuousOn.memLp_top_restrict_Ioo`, and the book's `‖α‖_∞` is the norm of `Lp ℝ ⊤`.
-/

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology InnerProductSpace

noncomputable section

/-! ### Restriction of a form to a subspace -/

section Restrict

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- The restriction of a bounded sesquilinear form on `V` to a subspace `K`, as a bounded form
on `K`. Belongs beside `SesqForm` in `Numlib/Variational/Forms.lean`. -/
def SesqForm.restrict (a : SesqForm 𝕜 V) (K : Submodule 𝕜 V) : SesqForm 𝕜 K :=
  ((a.comp K.subtypeL).flip.comp K.subtypeL).flip

/-- The restricted form is the form. -/
@[simp]
theorem SesqForm.restrict_apply (a : SesqForm 𝕜 V) (K : Submodule 𝕜 V) (u v : K) :
    a.restrict K u v = a u v := rfl

/-- The restriction of a Hermitian form to a subspace is Hermitian. -/
theorem SesqForm.IsHermitian.restrict {a : SesqForm 𝕜 V} (h : a.IsHermitian) (K : Submodule 𝕜 V) :
    (a.restrict K).IsHermitian := fun u v ↦ by
  rw [SesqForm.restrict_apply, SesqForm.restrict_apply]
  exact h u v

end Restrict

namespace EllipticInterval

variable {a b : ℝ}

/-! ### The bilinear form -/

/-- Multiplication by an `L^∞(a, b)` coefficient, as a continuous linear map on `L²(a, b)`:
Mathlib's Hölder product at the exponents `(2, ∞, 2)`. -/
def mulL (α : Lp ℝ ⊤ (volume.restrict (Ioo a b))) :
    Lp ℝ 2 (volume.restrict (Ioo a b)) →L[ℝ] Lp ℝ 2 (volume.restrict (Ioo a b)) :=
  ((ContinuousLinearMap.mul ℝ ℝ).holderL (volume.restrict (Ioo a b)) 2 ⊤ 2).flip α

/-- `EllipticInterval.mulL α f` is the pointwise product `α f` almost everywhere. -/
theorem coeFn_mulL (α : Lp ℝ ⊤ (volume.restrict (Ioo a b)))
    (f : Lp ℝ 2 (volume.restrict (Ioo a b))) :
    mulL α f =ᵐ[volume.restrict (Ioo a b)] fun x ↦ α x * f x := by
  refine ((ContinuousLinearMap.mul ℝ ℝ).coeFn_holder f α).trans (Eventually.of_forall fun x ↦ ?_)
  simp [mul_comm]

/-- `‖α f‖_{L²} ≤ ‖α‖_∞ ‖f‖_{L²}`. -/
theorem norm_mulL_apply_le (α : Lp ℝ ⊤ (volume.restrict (Ioo a b)))
    (f : Lp ℝ 2 (volume.restrict (Ioo a b))) : ‖mulL α f‖ ≤ ‖α‖ * ‖f‖ := by
  refine ((ContinuousLinearMap.mul ℝ ℝ).norm_holder_apply_apply_le f α).trans ?_
  calc ‖ContinuousLinearMap.mul ℝ ℝ‖ * ‖f‖ * ‖α‖ ≤ 1 * ‖f‖ * ‖α‖ := by
        gcongr; exact ContinuousLinearMap.opNorm_mul_le ℝ ℝ
    _ = ‖α‖ * ‖f‖ := by ring

/-! ### Constant coefficients -/

/-- **A constant, as an element of `L^∞(a, b)`**: the coefficients of the elliptic form
`EllipticInterval.form` live in `L^∞(a, b)`, and the constant-coefficient problems — the model
problem of [quarteroni2000numerical] §12.2, the advection-diffusion problem of §12.5 and the
heat equation of §13.2 — need the constants in that space. -/
def constLinf (a b : ℝ) (c : ℝ) : Lp ℝ ⊤ (volume.restrict (Ioo a b)) :=
  (memLp_top_const c).toLp _

/-- The function of `EllipticInterval.constLinf a b c` is the constant `c`. -/
theorem coeFn_constLinf (a b c : ℝ) :
    constLinf a b c =ᵐ[volume.restrict (Ioo a b)] fun _ ↦ c :=
  MemLp.coeFn_toLp _

/-- The `L^∞(a, b)` norm of a constant is its absolute value. -/
theorem norm_constLinf (hab : a < b) (c : ℝ) : ‖constLinf a b c‖ = |c| := by
  have hμ : volume.restrict (Ioo a b) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero, Real.volume_Ioo, ENNReal.ofReal_eq_zero, not_le]
    linarith
  rw [Lp.norm_def, eLpNorm_congr_ae (coeFn_constLinf a b c),
    eLpNorm_exponent_top aestronglyMeasurable_const,
    eLpNormEssSup_const c hμ]
  simp [Real.norm_eq_abs]

/-- The zero constant is the zero element of `L^∞(a, b)`. -/
@[simp]
theorem constLinf_zero (a b : ℝ) : constLinf a b 0 = 0 := by
  refine Lp.ext ?_
  filter_upwards [coeFn_constLinf a b 0, Lp.coeFn_zero ℝ ⊤ (volume.restrict (Ioo a b))]
    with x h1 h2
  rw [h1, h2]
  rfl

/-- Multiplication by a constant coefficient is the scalar multiple. -/
theorem mulL_constLinf (c : ℝ) (f : Lp ℝ 2 (volume.restrict (Ioo a b))) :
    mulL (constLinf a b c) f = c • f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_mulL (constLinf a b c) f, coeFn_constLinf a b c, Lp.coeFn_smul c f]
    with x h1 h2 h3
  rw [h1, h2, h3, Pi.smul_apply, smul_eq_mul]

variable (a b) in
/-- The pairing `(u, v) ↦ ⟪T u^{(i)}, v^{(j)}⟫_{L²(a, b)}` of the derivatives of orders `i, j` of
elements of `H^1(a, b)` through a bounded operator `T` on `L²(a, b)`, as a bounded bilinear
form on `H^1(a, b)`. -/
def pairing (T : Lp ℝ 2 (volume.restrict (Ioo a b)) →L[ℝ] Lp ℝ 2 (volume.restrict (Ioo a b)))
    (i j : Fin 2) : SesqForm ℝ (SobolevInterval 1 a b) :=
  (((innerSL ℝ).comp (T.comp (SobolevInterval.derivL 1 a b i))).flip.comp
    (SobolevInterval.derivL 1 a b j)).flip

/-- `EllipticInterval.pairing` is the inner product it was built from. -/
theorem pairing_apply
    (T : Lp ℝ 2 (volume.restrict (Ioo a b)) →L[ℝ] Lp ℝ 2 (volume.restrict (Ioo a b)))
    (i j : Fin 2) (u v : SobolevInterval 1 a b) :
    pairing a b T i j u v = ⟪T (SobolevInterval.deriv u i), SobolevInterval.deriv v j⟫_ℝ := rfl

variable (a b) in
/-- **The bilinear form of the two-point boundary value problem**,
`a(u, v) = ∫_a^b (α u' v' + β u' v + γ u v)`, [quarteroni2000numerical] (12.44), as a bounded
bilinear form on `H^1(a, b)`, for coefficients `α β γ ∈ L^∞(a, b)`. -/
def form (α β γ : Lp ℝ ⊤ (volume.restrict (Ioo a b))) : SesqForm ℝ (SobolevInterval 1 a b) :=
  pairing a b (mulL α) 1 1 + pairing a b (mulL β) 1 0 + pairing a b (mulL γ) 0 0

/-- The form as a sum of three `L²` inner products. -/
theorem form_apply_inner (α β γ : Lp ℝ ⊤ (volume.restrict (Ioo a b)))
    (u v : SobolevInterval 1 a b) :
    form a b α β γ u v = ⟪mulL α (SobolevInterval.deriv u 1), SobolevInterval.deriv v 1⟫_ℝ +
      ⟪mulL β (SobolevInterval.deriv u 1), SobolevInterval.deriv v 0⟫_ℝ +
      ⟪mulL γ (SobolevInterval.deriv u 0), SobolevInterval.deriv v 0⟫_ℝ := rfl

/-- `⟪α f, g⟫_{L²} = ∫_a^b α f g`. -/
theorem inner_mulL_eq_integral (α : Lp ℝ ⊤ (volume.restrict (Ioo a b)))
    (f g : Lp ℝ 2 (volume.restrict (Ioo a b))) :
    ⟪mulL α f, g⟫_ℝ = ∫ x in Ioo a b, α x * f x * g x := by
  rw [L2.inner_def]
  refine integral_congr_ae ((coeFn_mulL α f).mono fun x hx ↦ ?_)
  simp only [hx, RCLike.inner_apply, conj_trivial]
  ring

/-- The product of an `L^∞` coefficient and two `L²` functions is integrable on `(a, b)`. -/
theorem integrable_mul_mul (α : Lp ℝ ⊤ (volume.restrict (Ioo a b)))
    (f g : Lp ℝ 2 (volume.restrict (Ioo a b))) :
    Integrable (fun x ↦ α x * f x * g x) (volume.restrict (Ioo a b)) := by
  refine (L2.integrable_inner (𝕜 := ℝ) (mulL α f) g).congr ((coeFn_mulL α f).mono fun x hx ↦ ?_)
  simp only [hx, RCLike.inner_apply, conj_trivial]
  ring

/-- **The bilinear form is the integral (12.44)**:
`a(u, v) = ∫_a^b (α u' v' + β u' v + γ u v)`. -/
theorem form_apply (α β γ : Lp ℝ ⊤ (volume.restrict (Ioo a b))) (u v : SobolevInterval 1 a b) :
    form a b α β γ u v = ∫ x in Ioo a b,
      (α x * SobolevInterval.deriv u 1 x * SobolevInterval.deriv v 1 x
      + β x * SobolevInterval.deriv u 1 x * SobolevInterval.deriv v 0 x
      + γ x * SobolevInterval.deriv u 0 x * SobolevInterval.deriv v 0 x) := by
  have h12 : Integrable (fun x ↦ α x * SobolevInterval.deriv u 1 x * SobolevInterval.deriv v 1 x
      + β x * SobolevInterval.deriv u 1 x * SobolevInterval.deriv v 0 x)
      (volume.restrict (Ioo a b)) :=
    (integrable_mul_mul _ _ _).add (integrable_mul_mul _ _ _)
  rw [form_apply_inner, inner_mulL_eq_integral, inner_mulL_eq_integral, inner_mulL_eq_integral,
    ← integral_add (integrable_mul_mul _ _ _) (integrable_mul_mul _ _ _),
    ← integral_add h12 (integrable_mul_mul _ _ _)]

variable (a b) in
/-- **The load functional** `v ↦ (f, v) = ∫_a^b f v` for `f ∈ L²(a, b)`, as a continuous linear
functional on `H^1(a, b)`. -/
def load (f : Lp ℝ 2 (volume.restrict (Ioo a b))) : SobolevInterval 1 a b →L[ℝ] ℝ :=
  (innerSL ℝ f).comp (SobolevInterval.derivL 1 a b 0)

/-- The load functional is the `L²` inner product with `f`. -/
theorem load_apply_inner (f : Lp ℝ 2 (volume.restrict (Ioo a b))) (v : SobolevInterval 1 a b) :
    load a b f v = ⟪f, SobolevInterval.deriv v 0⟫_ℝ := rfl

/-- The load functional is the integral `∫_a^b f v`. -/
theorem load_apply (f : Lp ℝ 2 (volume.restrict (Ioo a b))) (v : SobolevInterval 1 a b) :
    load a b f v = ∫ x in Ioo a b, f x * SobolevInterval.deriv v 0 x := by
  rw [load_apply_inner, L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp [RCLike.inner_apply, mul_comm]

/-- `|(f, v)| ≤ ‖f‖_{L²} ‖v‖_{L²}`. -/
theorem abs_load_le (f : Lp ℝ 2 (volume.restrict (Ioo a b))) (v : SobolevInterval 1 a b) :
    |load a b f v| ≤ ‖f‖ * ‖SobolevInterval.deriv v 0‖ := by
  rw [load_apply_inner]; exact abs_real_inner_le_norm _ _

/-- The load functional has norm at most `‖f‖_{L²}`. -/
theorem norm_load_le (f : Lp ℝ 2 (volume.restrict (Ioo a b))) : ‖load a b f‖ ≤ ‖f‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v ↦ ?_
  rw [Real.norm_eq_abs]
  exact (abs_load_le f v).trans (by gcongr; exact SobolevInterval.norm_deriv_le v 0)

/-! ### Boundedness and coercivity -/

/-- Each pairing through a multiplication operator is bounded by the `L^∞` norm of the
coefficient times the `L²` norms of the derivatives. -/
theorem abs_pairing_mulL_le (α : Lp ℝ ⊤ (volume.restrict (Ioo a b))) (i j : Fin 2)
    (u v : SobolevInterval 1 a b) :
    |pairing a b (mulL α) i j u v|
      ≤ ‖α‖ * ‖SobolevInterval.deriv u i‖ * ‖SobolevInterval.deriv v j‖ := by
  rw [pairing_apply]
  exact (abs_real_inner_le_norm _ _).trans (by gcongr; exact norm_mulL_apply_le α _)

/-- **Boundedness of the form in the `H^1` norm**, [quarteroni2000numerical] (12.55):
`|a(u, v)| ≤ (‖α‖_∞ + ‖β‖_∞ + ‖γ‖_∞) ‖u‖_{H^1} ‖v‖_{H^1}`. -/
theorem form_isBoundedWith (α β γ : Lp ℝ ⊤ (volume.restrict (Ioo a b))) :
    (form a b α β γ).IsBoundedWith (‖α‖ + ‖β‖ + ‖γ‖) := by
  intro u v
  rw [Real.norm_eq_abs, form, add_apply, add_apply, add_apply, add_apply]
  have h1 := abs_pairing_mulL_le α 1 1 u v
  have h2 := abs_pairing_mulL_le β 1 0 u v
  have h3 := abs_pairing_mulL_le γ 0 0 u v
  have hu0 := SobolevInterval.norm_deriv_le u 0
  have hu1 := SobolevInterval.norm_deriv_le u 1
  have hv0 := SobolevInterval.norm_deriv_le v 0
  have hv1 := SobolevInterval.norm_deriv_le v 1
  have hα := norm_nonneg α
  have hβ := norm_nonneg β
  have hγ := norm_nonneg γ
  have hu := norm_nonneg u
  have hv := norm_nonneg v
  calc |pairing a b (mulL α) 1 1 u v + pairing a b (mulL β) 1 0 u v + pairing a b (mulL γ) 0 0 u v|
      ≤ |pairing a b (mulL α) 1 1 u v| + |pairing a b (mulL β) 1 0 u v|
        + |pairing a b (mulL γ) 0 0 u v| := abs_add_three _ _ _
    _ ≤ ‖α‖ * ‖u‖ * ‖v‖ + ‖β‖ * ‖u‖ * ‖v‖ + ‖γ‖ * ‖u‖ * ‖v‖ :=
        add_le_add (add_le_add (h1.trans (by gcongr)) (h2.trans (by gcongr)))
          (h3.trans (by gcongr))
    _ = (‖α‖ + ‖β‖ + ‖γ‖) * ‖u‖ * ‖v‖ := by ring

open SobolevInterval SobolevIntervalZero in
/-- **Boundedness of the form in the `H^1` seminorm on `H^1_0(a, b)`**, with the constant
`‖α‖_∞ + C_P ‖β‖_∞ + C_P² ‖γ‖_∞`, `C_P = (b - a)/√2` — the `M_h = ε_h + |β| C_P` of the proof of
[quarteroni2000numerical] Theorem 12.4, and for `β = 0` the constant of Theorem 12.3. Poincaré's
inequality converts the `L²` norms of `u, v` into their seminorms. -/
theorem abs_form_le_seminorm (hab : a < b) (α β γ : Lp ℝ ⊤ (volume.restrict (Ioo a b)))
    {u v : SobolevInterval 1 a b} (hu : u ∈ SobolevIntervalZero a b)
    (hv : v ∈ SobolevIntervalZero a b) :
    |form a b α β γ u v| ≤ (‖α‖ + (b - a) / Real.sqrt 2 * ‖β‖ + ((b - a) / Real.sqrt 2) ^ 2 * ‖γ‖)
      * seminorm 1 a b u * seminorm 1 a b v := by
  rw [form, add_apply, add_apply, add_apply, add_apply]
  have h1 := abs_pairing_mulL_le α 1 1 u v
  have h2 := abs_pairing_mulL_le β 1 0 u v
  have h3 := abs_pairing_mulL_le γ 0 0 u v
  have hu0 := norm_deriv_zero_le hab hu
  have hv0 := norm_deriv_zero_le hab hv
  have hα := norm_nonneg α
  have hβ := norm_nonneg β
  have hγ := norm_nonneg γ
  have hCP : 0 ≤ (b - a) / Real.sqrt 2 := by
    have := hab.le; positivity
  have hu1 := norm_nonneg (deriv u 1)
  have hv1 := norm_nonneg (deriv v 1)
  simp only [seminorm_apply]
  have e : deriv u (Fin.last 1) = deriv u 1 := rfl
  have e' : deriv v (Fin.last 1) = deriv v 1 := rfl
  rw [e, e']
  calc |pairing a b (mulL α) 1 1 u v + pairing a b (mulL β) 1 0 u v + pairing a b (mulL γ) 0 0 u v|
      ≤ |pairing a b (mulL α) 1 1 u v| + |pairing a b (mulL β) 1 0 u v|
        + |pairing a b (mulL γ) 0 0 u v| := abs_add_three _ _ _
    _ ≤ ‖α‖ * ‖deriv u 1‖ * ‖deriv v 1‖ + ‖β‖ * ‖deriv u 1‖ * ((b - a) / Real.sqrt 2 * ‖deriv v 1‖)
        + ‖γ‖ * ((b - a) / Real.sqrt 2 * ‖deriv u 1‖) * ((b - a) / Real.sqrt 2 * ‖deriv v 1‖) :=
        add_le_add (add_le_add h1 (h2.trans (by gcongr))) (h3.trans (by gcongr))
    _ = (‖α‖ + (b - a) / Real.sqrt 2 * ‖β‖ + ((b - a) / Real.sqrt 2) ^ 2 * ‖γ‖)
        * ‖deriv u 1‖ * ‖deriv v 1‖ := by ring

open SobolevInterval in
/-- **Coercivity in the `H^1` seminorm**, the case `β = 0`, `γ ≥ 0` of
[quarteroni2000numerical] §12.4.4: if `α ≥ α₀` and `γ ≥ 0` almost everywhere on `(a, b)`, then
`α₀ |v|²_{H^1} ≤ a(v, v)` for every `v ∈ H^1(a, b)`. -/
theorem form_isCoerciveWith_seminorm (α γ : Lp ℝ ⊤ (volume.restrict (Ioo a b))) {α₀ : ℝ}
    (hα : ∀ᵐ x ∂(volume.restrict (Ioo a b)), α₀ ≤ α x)
    (hγ : ∀ᵐ x ∂(volume.restrict (Ioo a b)), 0 ≤ γ x) (v : SobolevInterval 1 a b) :
    α₀ * seminorm 1 a b v ^ 2 ≤ form a b α 0 γ v v := by
  rw [seminorm_apply, form_apply]
  have e : deriv v (Fin.last 1) = deriv v 1 := rfl
  rw [e, norm_sq_eq_integral_sq, ← integral_const_mul]
  refine integral_mono_ae ((L2.integrable_inner (𝕜 := ℝ) (deriv v 1) (deriv v 1)).congr
    (Eventually.of_forall fun x ↦ ?_) |>.const_mul α₀) ?_ ?_
  · simp only [RCLike.inner_apply, conj_trivial, sq_abs]; ring
  · exact ((integrable_mul_mul _ _ _).add (integrable_mul_mul _ _ _)).add
      (integrable_mul_mul _ _ _)
  · filter_upwards [hα, hγ, Lp.coeFn_zero ℝ ⊤ (volume.restrict (Ioo a b))] with x hx1 hx2 hx3
    rw [hx3, Pi.zero_apply, zero_mul, zero_mul, add_zero, sq_abs]
    have := mul_nonneg hx2 (mul_self_nonneg (deriv v 0 x))
    nlinarith [mul_self_nonneg (deriv v 1 x)]

/-! ### Lax–Milgram and Céa -/

open SobolevInterval SobolevIntervalZero in
/-- **Coercivity in the `H^1` norm on `H^1_0(a, b)`**: the restriction of the form to
`H^1_0(a, b)` is coercive with constant `α₀ / (1 + C_P²)`, `C_P = (b - a)/√2`, by Poincaré's
inequality; this is what Lax–Milgram consumes for the Dirichlet problem. -/
theorem form_isCoerciveWith_restrict (hab : a < b) (α γ : Lp ℝ ⊤ (volume.restrict (Ioo a b)))
    {α₀ : ℝ} (hα : ∀ᵐ x ∂(volume.restrict (Ioo a b)), α₀ ≤ α x)
    (hγ : ∀ᵐ x ∂(volume.restrict (Ioo a b)), 0 ≤ γ x) (hα₀ : 0 ≤ α₀) :
    ((form a b α 0 γ).restrict (SobolevIntervalZero a b)).IsCoerciveWith
      (α₀ / (1 + (b - a) ^ 2 / 2)) := by
  intro v
  rw [SesqForm.restrict_apply, RCLike.re_to_real, ← Submodule.norm_coe]
  have h1 := form_isCoerciveWith_seminorm α γ hα hγ (v : SobolevInterval 1 a b)
  have h2 := norm_le_seminorm hab v.2
  have h3 : ‖(v : SobolevInterval 1 a b)‖ ^ 2 ≤ (1 + (b - a) ^ 2 / 2) * seminorm 1 a b v ^ 2 := by
    calc ‖(v : SobolevInterval 1 a b)‖ ^ 2
        ≤ (Real.sqrt (1 + (b - a) ^ 2 / 2) * seminorm 1 a b v) ^ 2 := by gcongr
      _ = (1 + (b - a) ^ 2 / 2) * seminorm 1 a b v ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hpos : 0 < 1 + (b - a) ^ 2 / 2 := by positivity
  calc α₀ / (1 + (b - a) ^ 2 / 2) * ‖(v : SobolevInterval 1 a b)‖ ^ 2
      ≤ α₀ / (1 + (b - a) ^ 2 / 2) * ((1 + (b - a) ^ 2 / 2) * seminorm 1 a b v ^ 2) := by
        gcongr
    _ = α₀ * seminorm 1 a b v ^ 2 := by field_simp
    _ ≤ _ := h1

open SobolevInterval in
/-- **Coercivity in the `H^1` norm on all of `H^1(a, b)`** when `γ ≥ γ₀ > 0`, with constant
`min α₀ γ₀`: the case of the Neumann problem, whose test space is `H^1(a, b)` itself
([quarteroni2000numerical] §12.4.1). -/
theorem form_isCoerciveWith_of_pos (α γ : Lp ℝ ⊤ (volume.restrict (Ioo a b))) {α₀ γ₀ : ℝ}
    (hα : ∀ᵐ x ∂(volume.restrict (Ioo a b)), α₀ ≤ α x)
    (hγ : ∀ᵐ x ∂(volume.restrict (Ioo a b)), γ₀ ≤ γ x) :
    (form a b α 0 γ).IsCoerciveWith (min α₀ γ₀) := by
  intro v
  rw [RCLike.re_to_real, norm_sq_eq, Fin.sum_univ_two, form_apply, norm_sq_eq_integral_sq,
    norm_sq_eq_integral_sq, ← integral_add, ← integral_const_mul]
  · refine integral_mono_ae ?_ ?_ ?_
    · refine (Integrable.add ?_ ?_).const_mul _
      · have := (Lp.memLp (deriv v 0)).integrable_norm_rpow two_ne_zero ENNReal.ofNat_ne_top
        simpa [Real.norm_eq_abs] using this
      · have := (Lp.memLp (deriv v 1)).integrable_norm_rpow two_ne_zero ENNReal.ofNat_ne_top
        simpa [Real.norm_eq_abs] using this
    · exact ((integrable_mul_mul _ _ _).add (integrable_mul_mul _ _ _)).add
        (integrable_mul_mul _ _ _)
    · filter_upwards [hα, hγ, Lp.coeFn_zero ℝ ⊤ (volume.restrict (Ioo a b))] with x hx1 hx2 hx3
      rw [hx3, Pi.zero_apply, zero_mul, zero_mul, add_zero, sq_abs, sq_abs]
      have h1 : min α₀ γ₀ ≤ α₀ := min_le_left _ _
      have h2 : min α₀ γ₀ ≤ γ₀ := min_le_right _ _
      nlinarith [mul_self_nonneg (deriv v 1 x), mul_self_nonneg (deriv v 0 x)]
  · have := (Lp.memLp (deriv v 0)).integrable_norm_rpow two_ne_zero ENNReal.ofNat_ne_top
    simpa [Real.norm_eq_abs] using this
  · have := (Lp.memLp (deriv v 1)).integrable_norm_rpow two_ne_zero ENNReal.ofNat_ne_top
    simpa [Real.norm_eq_abs] using this

open SobolevInterval in
/-- **The stability estimate**, [quarteroni2000numerical] (12.51): the solution of the weak
problem in any subspace `K ≤ H^1_0(a, b)` — the continuous problem for `K = H^1_0(a, b)`, the
Galerkin approximation for a finite element space — satisfies `|u|_{H^1} ≤ (C_P/α₀) ‖f‖_{L²}`,
uniformly in the subspace: `α₀ |u|² ≤ a(u, u) = (f, u) ≤ ‖f‖ ‖u‖_{L²} ≤ C_P ‖f‖ |u|`. -/
theorem seminorm_le_of_isGalerkinSolution (hab : a < b) (α γ : Lp ℝ ⊤ (volume.restrict (Ioo a b)))
    {α₀ : ℝ} (hα₀ : 0 < α₀) (hα : ∀ᵐ x ∂(volume.restrict (Ioo a b)), α₀ ≤ α x)
    (hγ : ∀ᵐ x ∂(volume.restrict (Ioo a b)), 0 ≤ γ x) (f : Lp ℝ 2 (volume.restrict (Ioo a b)))
    {K : Submodule ℝ (SobolevInterval 1 a b)} (hK : K ≤ SobolevIntervalZero a b)
    {u : SobolevInterval 1 a b} (hu : IsGalerkinSolution (form a b α 0 γ) (load a b f) K u) :
    seminorm 1 a b u ≤ (b - a) / Real.sqrt 2 / α₀ * ‖f‖ := by
  have hCP : 0 ≤ (b - a) / Real.sqrt 2 := by have := hab.le; positivity
  have h1 := form_isCoerciveWith_seminorm α γ hα hγ u
  rw [hu.2 u hu.1] at h1
  have h2 := (abs_load_le f u).trans (mul_le_mul_of_nonneg_left
    (SobolevIntervalZero.norm_deriv_zero_le hab (hK hu.1)) (norm_nonneg f))
  have h3 : seminorm 1 a b u = ‖deriv u 1‖ := rfl
  rw [h3] at h1 ⊢
  have h4 : α₀ * ‖deriv u 1‖ ^ 2 ≤ ‖f‖ * ((b - a) / Real.sqrt 2 * ‖deriv u 1‖) :=
    h1.trans ((le_abs_self _).trans h2)
  rcases eq_or_lt_of_le (norm_nonneg (deriv u 1)) with h0 | h0
  · rw [← h0]; positivity
  · rw [div_mul_eq_mul_div, le_div_iff₀ hα₀]
    have := norm_nonneg f
    nlinarith

open SobolevInterval in
/-- **Existence and uniqueness of the weak solution** of the Dirichlet problem, the Lax–Milgram
paragraph of [quarteroni2000numerical] §12.4.4: for `α ≥ α₀ > 0`, `γ ≥ 0` and `f ∈ L²(a, b)`
there is exactly one `u ∈ H^1_0(a, b)` with `a(u, v) = (f, v)` for all `v ∈ H^1_0(a, b)`, that
is, exactly one Galerkin solution in the trial space `H^1_0(a, b)`. Lax–Milgram
(`SesqForm.laxMilgram`) applies to the restriction of the form to the Hilbert space
`H^1_0(a, b)`, which is coercive by `EllipticInterval.form_isCoerciveWith_restrict`. -/
theorem existsUnique_isWeakSolution (hab : a < b) (α γ : Lp ℝ ⊤ (volume.restrict (Ioo a b)))
    {α₀ : ℝ} (hα₀ : 0 < α₀) (hα : ∀ᵐ x ∂(volume.restrict (Ioo a b)), α₀ ≤ α x)
    (hγ : ∀ᵐ x ∂(volume.restrict (Ioo a b)), 0 ≤ γ x) (f : Lp ℝ 2 (volume.restrict (Ioo a b))) :
    ∃! u, IsGalerkinSolution (form a b α 0 γ) (load a b f) (SobolevIntervalZero a b) u := by
  have hc : 0 < α₀ / (1 + (b - a) ^ 2 / 2) := by positivity
  obtain ⟨w, hw, hwu⟩ := SesqForm.laxMilgram ((form a b α 0 γ).restrict (SobolevIntervalZero a b))
    ((load a b f).comp (SobolevIntervalZero a b).subtypeL) hc
    (form_isCoerciveWith_restrict hab α γ hα hγ hα₀.le)
  refine ⟨(w : SobolevInterval 1 a b), ⟨w.2, fun v hv ↦ hw ⟨v, hv⟩⟩, ?_⟩
  rintro y ⟨hyK, hy⟩
  exact congrArg Subtype.val (hwu ⟨y, hyK⟩ fun z ↦ hy (z : SobolevInterval 1 a b) z.2)

/-- **Céa's lemma in a seminorm**, relative to a subspace `W`: if the bilinear form `B` is
bounded by `M` and coercive with constant `c` for the seminorm `q` on `W`, then for `u ∈ W` and
`uh ∈ K ≤ W` with the Galerkin orthogonality `B (u - uh) v = 0` on `K`,
`q (u - uh) ≤ (M / c) q (u - w)` for every `w ∈ K`.

This is the general lemma `_root_.seminorm_sub_le_of_galerkin_orthogonal` of
`Numlib/Variational/Galerkin`, restated here in the namespace of its consumer
`galerkin_seminorm_sub_le`; the proof is there. -/
theorem seminorm_sub_le_of_galerkin_orthogonal {V : Type*} [AddCommGroup V] [Module ℝ V]
    (q : Seminorm ℝ V) (B : V → V → ℝ) (hadd : ∀ x y z, B x (y + z) = B x y + B x z)
    {W : Submodule ℝ V} {M c : ℝ} (hc : 0 < c)
    (hM : ∀ u ∈ W, ∀ v ∈ W, |B u v| ≤ M * q u * q v) (hcoer : ∀ v ∈ W, c * q v ^ 2 ≤ B v v)
    {K : Submodule ℝ V} (hK : K ≤ W) {u uh : V} (hu : u ∈ W) (huh : uh ∈ K)
    (horth : ∀ v ∈ K, B (u - uh) v = 0) {w : V} (hw : w ∈ K) :
    q (u - uh) ≤ M / c * q (u - w) :=
  _root_.seminorm_sub_le_of_galerkin_orthogonal q B hadd hc hM hcoer hK hu huh horth hw

open SobolevInterval in
/-- **Céa's lemma with the constant of [quarteroni2000numerical] Theorem 12.3**: for the weak
solution `u ∈ H^1_0(a, b)` and the Galerkin solution `uh` in a subspace `K ≤ H^1_0(a, b)`,
`|u - uh|_{H^1} ≤ α₀⁻¹ (‖α‖_∞ + C_P² ‖γ‖_∞) |u - w|_{H^1}` for every `w ∈ K`, with
`C_P = (b - a)/√2`. The `H^1`-norm form (12.56) with the constant `M/α₀` is
`IsGalerkinSolution.norm_sub_le`. -/
theorem galerkin_seminorm_sub_le (hab : a < b) (α γ : Lp ℝ ⊤ (volume.restrict (Ioo a b)))
    {α₀ : ℝ} (hα₀ : 0 < α₀) (hα : ∀ᵐ x ∂(volume.restrict (Ioo a b)), α₀ ≤ α x)
    (hγ : ∀ᵐ x ∂(volume.restrict (Ioo a b)), 0 ≤ γ x) (f : Lp ℝ 2 (volume.restrict (Ioo a b)))
    {K : Submodule ℝ (SobolevInterval 1 a b)} (hK : K ≤ SobolevIntervalZero a b)
    {u uh : SobolevInterval 1 a b}
    (hu : IsGalerkinSolution (form a b α 0 γ) (load a b f) (SobolevIntervalZero a b) u)
    (huh : IsGalerkinSolution (form a b α 0 γ) (load a b f) K uh) {w : SobolevInterval 1 a b}
    (hw : w ∈ K) :
    seminorm 1 a b (u - uh) ≤ α₀⁻¹ * (‖α‖ + ((b - a) / Real.sqrt 2) ^ 2 * ‖γ‖)
      * seminorm 1 a b (u - w) := by
  have h := seminorm_sub_le_of_galerkin_orthogonal (seminorm 1 a b) (fun u v ↦ form a b α 0 γ u v)
    (fun x y z ↦ map_add _ y z) (W := SobolevIntervalZero a b) hα₀
    (fun u hu v hv ↦ by simpa using abs_form_le_seminorm hab α 0 γ hu hv)
    (fun v _ ↦ form_isCoerciveWith_seminorm α γ hα hγ v) hK hu.1 huh.1
    (fun v hv ↦ by rw [map_sub, sub_apply, hu.2 v (hK hv), huh.2 v hv, sub_self]) hw
  rwa [div_eq_inv_mul] at h

/-! ### Classical solutions are weak solutions -/

/-- The element of `H^1(a, b)` carried by `u ∈ C²[a, b]`. -/
def ofContDiffMapIcc (hab : a < b) (u : ContDiffMapIcc hab.le 2) : SobolevInterval 1 a b :=
  SobolevInterval.inclusionCLM 1 a b (ContDiffMapIcc.toSobolevInterval hab.le hab 2 u)

/-- The function of the element carried by `u ∈ C²[a, b]` is `u` almost everywhere. -/
theorem deriv_ofContDiffMapIcc_zero (hab : a < b) (u : ContDiffMapIcc hab.le 2) :
    (SobolevInterval.deriv (ofContDiffMapIcc hab u) 0 : ℝ → ℝ)
      =ᵐ[volume.restrict (Ioo a b)] u.extend :=
  u.coeFn_derivLp 0

/-- The weak derivative of the element carried by `u ∈ C²[a, b]` is `u'` almost everywhere. -/
theorem deriv_ofContDiffMapIcc_one (hab : a < b) (u : ContDiffMapIcc hab.le 2) :
    (SobolevInterval.deriv (ofContDiffMapIcc hab u) 1 : ℝ → ℝ)
      =ᵐ[volume.restrict (Ioo a b)] u.shift.extend :=
  u.coeFn_derivLp 1

/-- The continuous representative of the element carried by `u ∈ C²[a, b]` is `u`. -/
theorem rep_ofContDiffMapIcc (hab : a < b) (u : ContDiffMapIcc hab.le 2) :
    EqOn (SobolevInterval.rep (ofContDiffMapIcc hab u)) u.extend (Icc a b) :=
  SobolevInterval.rep_eq_of_continuousOn hab _ u.extend.continuous.continuousOn
    (deriv_ofContDiffMapIcc_zero hab u)

open SobolevInterval in
/-- **Green's formula for a classical solution**: for `u ∈ C²[a, b]` with
`-(α u')' + β u' + γ u = f` on `(a, b)` and any `v ∈ H^1(a, b)`,
`a(u, v) = ∫_a^b f g_v + [α u' g_v]_a^b`, the identity of [quarteroni2000numerical] §12.4.1
before the boundary condition on the test function is imposed. -/
theorem form_ofContDiffMapIcc_eq (hab : a < b) {α β γ f : ℝ → ℝ}
    (αL βL γL : Lp ℝ ⊤ (volume.restrict (Ioo a b))) (hαL : αL =ᵐ[volume.restrict (Ioo a b)] α)
    (hβL : βL =ᵐ[volume.restrict (Ioo a b)] β) (hγL : γL =ᵐ[volume.restrict (Ioo a b)] γ)
    (hα : ContDiffOn ℝ 1 α (Icc a b)) (hβ : ContinuousOn β (Icc a b))
    (hγ : ContinuousOn γ (Icc a b)) (u : ContDiffMapIcc hab.le 2)
    (hode : ∀ x ∈ Ioo a b, -deriv (fun t ↦ α t * u.shift.extend t) x
      + β x * u.shift.extend x + γ x * u.extend x = f x) (v : SobolevInterval 1 a b) :
    form a b αL βL γL (ofContDiffMapIcc hab u) v = (∫ x in Ioo a b, f x * rep v x)
      + (rep v b * (α b * u.shift.extend b) - rep v a * (α a * u.shift.extend a)) := by
  set ψ : ℝ → ℝ := fun t ↦ α t * u.shift.extend t with hψ
  have hu1 : ContDiffOn ℝ 1 u.shift.extend (Icc a b) := u.shift.contDiffOn hab
  have hu0 : ContinuousOn u.extend (Icc a b) := u.extend.continuous.continuousOn
  have hψc : ContDiffOn ℝ 1 ψ (Icc a b) := hα.mul hu1
  have hψAC : AbsolutelyContinuousOnInterval ψ a b := by
    rw [← uIcc_of_le hab.le] at hψc; exact hψc.absolutelyContinuousOnInterval
  -- the form as an integral of classical quantities
  have e1 : form a b αL βL γL (ofContDiffMapIcc hab u) v = ∫ x in Ioo a b,
      (deriv v 1 x * ψ x + (β x * u.shift.extend x + γ x * u.extend x) * rep v x) := by
    rw [form_apply]
    refine integral_congr_ae ?_
    filter_upwards [hαL, hβL, hγL, deriv_ofContDiffMapIcc_zero hab u,
      deriv_ofContDiffMapIcc_one hab u, fn_ae_eq_rep hab v] with x h1 h2 h3 h4 h5 h6
    rw [h1, h2, h3, h4, h5, deriv_zero, h6, hψ]
    ring
  -- integration by parts on the first term
  have ibp := integral_deriv_mul_eq_sub_integral_mul_deriv hab v hψAC
  rw [intervalIntegral.integral_eq_setIntegral_Ioo hab.le,
    intervalIntegral.integral_eq_setIntegral_Ioo hab.le] at ibp
  -- integrability of the pieces
  have i1 : IntegrableOn (fun x ↦ deriv v 1 x * ψ x) (Ioo a b) := by
    have := integrableOn_continuousOn_mul hψc.continuousOn (deriv v 1)
    exact this.congr_fun (fun x _ ↦ mul_comm _ _) measurableSet_Ioo
  have i2 : IntegrableOn (fun x ↦ (β x * u.shift.extend x + γ x * u.extend x) * rep v x)
      (Ioo a b) :=
    (((hβ.mul hu1.continuousOn).add (hγ.mul hu0)).mul (continuousOn_rep hab.le v)).integrableOn_Icc
      |>.mono_set Ioo_subset_Icc_self
  have i3 : IntegrableOn (fun x ↦ rep v x * deriv ψ x) (Ioo a b) := by
    have := hψAC.intervalIntegrable_deriv.continuousOn_mul
      (by rw [uIcc_of_le hab.le]; exact continuousOn_rep hab.le v)
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le] at this
    exact this
  have i3' : IntegrableOn (fun x ↦ -(rep v x * deriv ψ x)) (Ioo a b) := i3.neg
  have e2 : ∫ x in Ioo a b, f x * rep v x
      = ∫ x in Ioo a b, (-(rep v x * deriv ψ x) + (β x * u.shift.extend x + γ x * u.extend x)
        * rep v x) := by
    refine setIntegral_congr_fun measurableSet_Ioo fun x hx ↦ ?_
    rw [← hode x hx, hψ]
    ring
  rw [e1, integral_add i1 i2, ibp, e2, integral_add i3' i2, integral_neg]
  ring

open SobolevInterval in
/-- **Classical solutions are weak solutions** ([quarteroni2000numerical] (12.43)): if
`u ∈ C²[a, b]` satisfies `-(α u')' + β u' + γ u = f` on `(a, b)` and `u(a) = u(b) = 0`, then the
element `U` of `H^1(a, b)` it carries lies in `H^1_0(a, b)` and `a(U, v) = (f, v)` for every
`v ∈ H^1_0(a, b)`: `U` is the weak solution of the Dirichlet problem. -/
theorem isWeakSolution_of_classical (hab : a < b) {α β γ f : ℝ → ℝ}
    (αL βL γL : Lp ℝ ⊤ (volume.restrict (Ioo a b))) (fL : Lp ℝ 2 (volume.restrict (Ioo a b)))
    (hαL : αL =ᵐ[volume.restrict (Ioo a b)] α) (hβL : βL =ᵐ[volume.restrict (Ioo a b)] β)
    (hγL : γL =ᵐ[volume.restrict (Ioo a b)] γ) (hfL : fL =ᵐ[volume.restrict (Ioo a b)] f)
    (hα : ContDiffOn ℝ 1 α (Icc a b)) (hβ : ContinuousOn β (Icc a b))
    (hγ : ContinuousOn γ (Icc a b)) (u : ContDiffMapIcc hab.le 2)
    (hode : ∀ x ∈ Ioo a b, -deriv (fun t ↦ α t * u.shift.extend t) x
      + β x * u.shift.extend x + γ x * u.extend x = f x)
    (hua : u.extend a = 0) (hub : u.extend b = 0) :
    IsGalerkinSolution (form a b αL βL γL) (load a b fL) (SobolevIntervalZero a b)
      (ofContDiffMapIcc hab u) := by
  have hmem : ofContDiffMapIcc hab u ∈ SobolevIntervalZero a b :=
    SobolevIntervalZero.mem_of_rep_eq_zero hab _
      (by rw [rep_ofContDiffMapIcc hab u (left_mem_Icc.2 hab.le), hua])
      (by rw [rep_ofContDiffMapIcc hab u (right_mem_Icc.2 hab.le), hub])
  refine ⟨hmem, fun v hv ↦ ?_⟩
  rw [form_ofContDiffMapIcc_eq hab αL βL γL hαL hβL hγL hα hβ hγ u hode v,
    SobolevIntervalZero.rep_left_eq_zero hab hv, SobolevIntervalZero.rep_right_eq_zero hab hv,
    zero_mul, zero_mul, sub_zero, add_zero, load_apply]
  refine integral_congr_ae ?_
  filter_upwards [hfL, fn_ae_eq_rep hab v] with x h1 h2
  rw [h1, deriv_zero, h2]

open SobolevInterval in
/-- **The Neumann and mixed problems** ([quarteroni2000numerical] §12.4.1, Exercise 12.12): for
a classical solution with the flux values `α u'(a) = w₀`, `α u'(b) = w₁`, the element `U` of
`H^1(a, b)` satisfies `a(U, v) = (f, v) + w₁ g_v(b) - w₀ g_v(a)` for every `v ∈ H^1(a, b)`. The
homogeneous Neumann problem is `w₀ = w₁ = 0`, and the mixed problem tests against the `v` with
`g_v(b) = 0`. -/
theorem isWeakSolution_of_classical_neumann (hab : a < b) {α β γ f : ℝ → ℝ}
    (αL βL γL : Lp ℝ ⊤ (volume.restrict (Ioo a b))) (fL : Lp ℝ 2 (volume.restrict (Ioo a b)))
    (hαL : αL =ᵐ[volume.restrict (Ioo a b)] α) (hβL : βL =ᵐ[volume.restrict (Ioo a b)] β)
    (hγL : γL =ᵐ[volume.restrict (Ioo a b)] γ) (hfL : fL =ᵐ[volume.restrict (Ioo a b)] f)
    (hα : ContDiffOn ℝ 1 α (Icc a b)) (hβ : ContinuousOn β (Icc a b))
    (hγ : ContinuousOn γ (Icc a b)) (u : ContDiffMapIcc hab.le 2)
    (hode : ∀ x ∈ Ioo a b, -deriv (fun t ↦ α t * u.shift.extend t) x
      + β x * u.shift.extend x + γ x * u.extend x = f x)
    {w₀ w₁ : ℝ} (hw₀ : α a * u.shift.extend a = w₀) (hw₁ : α b * u.shift.extend b = w₁)
    (v : SobolevInterval 1 a b) :
    form a b αL βL γL (ofContDiffMapIcc hab u) v
      = load a b fL v + w₁ * rep v b - w₀ * rep v a := by
  rw [form_ofContDiffMapIcc_eq hab αL βL γL hαL hβL hγL hα hβ hγ u hode v, hw₀, hw₁, load_apply]
  have : ∫ x in Ioo a b, fL x * deriv v 0 x = ∫ x in Ioo a b, f x * rep v x := by
    refine integral_congr_ae ?_
    filter_upwards [hfL, fn_ae_eq_rep hab v] with x h1 h2
    rw [h1, deriv_zero, h2]
  rw [this]
  ring

/-- **The nonhomogeneous Dirichlet lifting** ([quarteroni2000numerical] §12.4.1): if `U` solves
`a(U, v) = (f, v)` on `H^1_0(a, b)`, then for any lifting `W ∈ H^1(a, b)` of the boundary
values, `U - W` solves `a(U - W, v) = (f, v) - a(W, v)` on `H^1_0(a, b)`. -/
theorem form_sub_eq_of_forall (α β γ : Lp ℝ ⊤ (volume.restrict (Ioo a b)))
    (f : Lp ℝ 2 (volume.restrict (Ioo a b))) {U : SobolevInterval 1 a b}
    (hU : ∀ v ∈ SobolevIntervalZero a b, form a b α β γ U v = load a b f v)
    (W : SobolevInterval 1 a b) {v : SobolevInterval 1 a b} (hv : v ∈ SobolevIntervalZero a b) :
    form a b α β γ (U - W) v = load a b f v - form a b α β γ W v := by
  rw [map_sub, sub_apply, hU v hv]

/-! ### Coercivity under the condition (12.50) -/

open SobolevInterval in
/-- `∫_a^b β (v²)' = -∫_a^b β' v²` for `v ∈ H^1_0(a, b)` and `β` absolutely continuous:
the identity behind the coercivity condition (12.50). -/
theorem integral_mul_deriv_mul_rep_eq (hab : a < b) {β : ℝ → ℝ}
    (hβ : AbsolutelyContinuousOnInterval β a b) {v : SobolevInterval 1 a b}
    (hv : v ∈ SobolevIntervalZero a b) :
    ∫ x in Ioo a b, β x * (deriv v 1 x * rep v x)
      = -(1 / 2) * ∫ x in Ioo a b, deriv β x * (rep v x * rep v x) := by
  set g : ℝ → ℝ := fun t ↦ rep v t * rep v t with hg
  have hrAC := absolutelyContinuousOnInterval_rep hab.le v
  have hgAC : AbsolutelyContinuousOnInterval g a b := hrAC.fun_mul hrAC
  have key := hβ.integral_mul_deriv_eq_deriv_mul hgAC
  have hga : g a = 0 := by
    simp [hg, SobolevIntervalZero.rep_left_eq_zero hab hv]
  have hgb : g b = 0 := by
    simp [hg, SobolevIntervalZero.rep_right_eq_zero hab hv]
  rw [hga, hgb, mul_zero, mul_zero, sub_zero, zero_sub] at key
  -- `deriv g = 2 g_v v'` almost everywhere
  have hderiv : ∀ᵐ t, t ∈ uIoc a b → β t * deriv g t = 2 * (β t * (deriv v 1 t * rep v t)) := by
    filter_upwards [hrAC.ae_differentiableAt, ae_deriv_rep_eq hab.le v] with t h1 h2 ht
    rw [uIoc_of_le hab.le] at ht
    have hd := h1 (uIcc_of_le hab.le ▸ Ioc_subset_Icc_self ht)
    rw [hg, deriv_fun_mul hd hd, h2 ht]
    ring
  rw [intervalIntegral.integral_congr_ae hderiv, intervalIntegral.integral_const_mul] at key
  rw [← intervalIntegral.integral_eq_setIntegral_Ioo hab.le,
    ← intervalIntegral.integral_eq_setIntegral_Ioo hab.le]
  change 2 * ∫ x in a..b, β x * (deriv v 1 x * rep v x) = -∫ x in a..b, deriv β x * g x at key
  linarith

open SobolevInterval SobolevIntervalZero in
/-- **Coercivity under the book's condition (12.50)**, [quarteroni2000numerical] §12.4.4: if
`α ≥ α₀`, `β` is `C¹` on `[a, b]` and `-β'/2 + γ ≥ 0` almost everywhere on `(a, b)`, then
`α₀ |v|²_{H^1} ≤ a(v, v)` for every `v ∈ H^1_0(a, b)`. Since `∫ β v' v = -½ ∫ β' v²`
(`EllipticInterval.integral_mul_deriv_mul_rep_eq`), `a(v, v) = ∫ α v'² + ∫ (γ - β'/2) v²`. For a
constant `β` this is the identity `a_h(v, v) = ε_h |v|²` of §12.5.3. -/
theorem form_isCoerciveWith_seminorm_of_le (hab : a < b)
    (αL βL γL : Lp ℝ ⊤ (volume.restrict (Ioo a b))) {α₀ : ℝ}
    (hα : ∀ᵐ x ∂(volume.restrict (Ioo a b)), α₀ ≤ αL x) {β : ℝ → ℝ}
    (hβL : βL =ᵐ[volume.restrict (Ioo a b)] β) (hβ : ContDiffOn ℝ 1 β (Icc a b))
    (hcond : ∀ᵐ x ∂(volume.restrict (Ioo a b)), deriv β x / 2 ≤ γL x)
    {v : SobolevInterval 1 a b} (hv : v ∈ SobolevIntervalZero a b) :
    α₀ * seminorm 1 a b v ^ 2 ≤ form a b αL βL γL v v := by
  have hβAC : AbsolutelyContinuousOnInterval β a b := by
    rw [← uIcc_of_le hab.le] at hβ; exact hβ.absolutelyContinuousOnInterval
  have hrep := fn_ae_eq_rep hab v
  have hcont := continuousOn_rep hab.le v
  -- the three integrals
  have i1 : IntegrableOn (fun x ↦ αL x * deriv v 1 x * deriv v 1 x) (Ioo a b) :=
    integrable_mul_mul _ _ _
  have i2 : IntegrableOn (fun x ↦ β x * (deriv v 1 x * rep v x)) (Ioo a b) := by
    have := integrableOn_continuousOn_mul (hβ.continuousOn.mul hcont) (deriv v 1)
    exact this.congr_fun (fun x _ ↦ by simp only [Pi.mul_apply]; ring) measurableSet_Ioo
  have i3 : IntegrableOn (fun x ↦ γL x * (rep v x * rep v x)) (Ioo a b) := by
    refine (integrable_mul_mul γL (deriv v 0) (deriv v 0)).congr ?_
    filter_upwards [hrep] with x hx
    rw [SobolevInterval.deriv_zero, hx]; ring
  have i4 : IntegrableOn (fun x ↦ deriv β x * (rep v x * rep v x)) (Ioo a b) := by
    have := hβAC.intervalIntegrable_deriv.mul_continuousOn
      (by rw [uIcc_of_le hab.le]; exact hcont.mul hcont)
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le] at this
    exact this
  have e1 : form a b αL βL γL v v = (∫ x in Ioo a b, αL x * deriv v 1 x * deriv v 1 x)
      + (∫ x in Ioo a b, β x * (deriv v 1 x * rep v x))
      + ∫ x in Ioo a b, γL x * (rep v x * rep v x) := by
    have i12 : IntegrableOn (fun x ↦ αL x * deriv v 1 x * deriv v 1 x
        + β x * (deriv v 1 x * rep v x)) (Ioo a b) := i1.add i2
    rw [form_apply, ← integral_add i1 i2, ← integral_add i12 i3]
    refine integral_congr_ae ?_
    filter_upwards [hβL, hrep] with x h1 h2
    rw [h1, SobolevInterval.deriv_zero, h2]
    ring
  rw [e1, integral_mul_deriv_mul_rep_eq hab hβAC hv]
  have hlow : α₀ * seminorm 1 a b v ^ 2 ≤ ∫ x in Ioo a b, αL x * deriv v 1 x * deriv v 1 x := by
    rw [seminorm_apply]
    have e : deriv v (Fin.last 1) = deriv v 1 := rfl
    rw [e, norm_sq_eq_integral_sq, ← integral_const_mul]
    refine integral_mono_ae ?_ i1 ?_
    · refine ((L2.integrable_inner (𝕜 := ℝ) (deriv v 1) (deriv v 1)).congr
        (Eventually.of_forall fun x ↦ ?_)).const_mul α₀
      simp only [RCLike.inner_apply, conj_trivial, sq_abs]; ring
    · filter_upwards [hα] with x hx
      rw [sq_abs]
      nlinarith [mul_self_nonneg (deriv v 1 x)]
  have hnn : 0 ≤ -(1 / 2) * (∫ x in Ioo a b, deriv β x * (rep v x * rep v x))
      + ∫ x in Ioo a b, γL x * (rep v x * rep v x) := by
    rw [neg_mul, neg_add_eq_sub, ← integral_const_mul, ← integral_sub i3 (i4.const_mul _)]
    refine integral_nonneg_of_ae ?_
    filter_upwards [hcond] with x hx
    have := mul_self_nonneg (rep v x)
    simp only [Pi.zero_apply]
    nlinarith
  linarith

/-! ### `H²` regularity -/

open SobolevInterval in
/-- The weak derivative of an element of `H^1(a, b)` whose function is a test function is the
classical derivative of the test function. -/
theorem deriv_ae_eq_of_fn_ae_eq {v : SobolevInterval 1 a b}
    (φ : 𝓓(Opens.Ioo a b, ℝ)) (hv : fn v =ᵐ[volume.restrict (Ioo a b)] φ) :
    (deriv v 1 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] _root_.deriv φ := by
  have h1 := hasWeakDerivOn_fn v
  have h2 : HasWeakDerivOn (fn v) (_root_.deriv φ) (Opens.Ioo a b) :=
    (hasWeakDerivOn_of_contDiffOn ((φ.contDiff.of_le (by simp)).contDiffOn)).congr_ae hv.symm
      (Eventually.of_forall fun _ ↦ rfl)
  exact (ae_restrict_iff' measurableSet_Ioo).2 (h1.ae_eq h2)

open SobolevInterval in
/-- **The flux `α u'` of a weak solution has a weak derivative**, namely `β u' + γ u - f ∈ L²`:
testing the weak formulation `a(u, v) = (f, v)` against the test functions. -/
theorem hasWeakDerivOn_mulL_deriv (αL βL γL : Lp ℝ ⊤ (volume.restrict (Ioo a b)))
    (f : Lp ℝ 2 (volume.restrict (Ioo a b))) {u : SobolevInterval 1 a b}
    (hu : IsGalerkinSolution (form a b αL βL γL) (load a b f) (SobolevIntervalZero a b) u) :
    HasWeakDerivOn (fun x ↦ αL x * deriv u 1 x)
      (fun x ↦ βL x * deriv u 1 x + γL x * deriv u 0 x - f x) (Opens.Ioo a b) := by
  have hG : MemLp (fun x ↦ αL x * deriv u 1 x) 2 (volume.restrict (Ioo a b)) :=
    (Lp.memLp (mulL αL (deriv u 1))).ae_eq (coeFn_mulL αL (deriv u 1))
  have hW : MemLp (fun x ↦ βL x * deriv u 1 x + γL x * deriv u 0 x - f x) 2
      (volume.restrict (Ioo a b)) :=
    (((Lp.memLp (mulL βL (deriv u 1))).ae_eq (coeFn_mulL βL (deriv u 1))).add
      ((Lp.memLp (mulL γL (deriv u 0))).ae_eq (coeFn_mulL γL (deriv u 0)))).sub (Lp.memLp f)
  refine hasWeakDerivOn_iff.2 ⟨hG.locallyIntegrableOn (Ω := Opens.Ioo a b) one_le_two,
    hW.locallyIntegrableOn (Ω := Opens.Ioo a b) one_le_two, fun φ ↦ ?_⟩
  obtain ⟨v, hvmem, hvφ⟩ := SobolevIntervalZero.exists_mem_fn_ae_eq φ
  have hvφ' := deriv_ae_eq_of_fn_ae_eq φ hvφ
  have key := hu.2 v hvmem
  rw [form_apply, load_apply] at key
  -- rewrite the weak formulation with `φ`
  have e1 : ∫ x in Ioo a b, (αL x * deriv u 1 x * deriv v 1 x + βL x * deriv u 1 x * deriv v 0 x
      + γL x * deriv u 0 x * deriv v 0 x) = ∫ x in Ioo a b,
        (_root_.deriv φ x * (αL x * deriv u 1 x)
          + φ x * (βL x * deriv u 1 x + γL x * deriv u 0 x)) := by
    refine integral_congr_ae ?_
    filter_upwards [hvφ, hvφ'] with x h1 h2
    rw [h2, deriv_zero, h1]
    ring
  have e2 : ∫ x in Ioo a b, f x * deriv v 0 x = ∫ x in Ioo a b, φ x * f x := by
    refine integral_congr_ae ?_
    filter_upwards [hvφ] with x h1
    rw [deriv_zero, h1, mul_comm]
  rw [e1, e2] at key
  have i1 : IntegrableOn (fun x ↦ _root_.deriv φ x * (αL x * deriv u 1 x)) (Ioo a b) :=
    IntegrableOn.continuousOn_mul_of_subset (φ.fderivApply 1).continuous.continuousOn
      (hG.integrable one_le_two) isCompact_Icc measurableSet_Ioo Ioo_subset_Icc_self
  have hW' : MemLp (fun x ↦ βL x * deriv u 1 x + γL x * deriv u 0 x) 2
      (volume.restrict (Ioo a b)) :=
    ((Lp.memLp (mulL βL (deriv u 1))).ae_eq (coeFn_mulL βL (deriv u 1))).add
      ((Lp.memLp (mulL γL (deriv u 0))).ae_eq (coeFn_mulL γL (deriv u 0)))
  have i2 : IntegrableOn (fun x ↦ φ x * (βL x * deriv u 1 x + γL x * deriv u 0 x)) (Ioo a b) :=
    IntegrableOn.continuousOn_mul_of_subset φ.continuous.continuousOn
      (hW'.integrable one_le_two) isCompact_Icc measurableSet_Ioo Ioo_subset_Icc_self
  have i3 : IntegrableOn (fun x ↦ φ x * f x) (Ioo a b) :=
    IntegrableOn.continuousOn_mul_of_subset φ.continuous.continuousOn
      ((Lp.memLp f).integrable one_le_two) isCompact_Icc measurableSet_Ioo Ioo_subset_Icc_self
  rw [integral_add i1 i2] at key
  have e3 : ∫ x in Ioo a b, φ x * (βL x * deriv u 1 x + γL x * deriv u 0 x - f x)
      = (∫ x in Ioo a b, φ x * (βL x * deriv u 1 x + γL x * deriv u 0 x))
        - ∫ x in Ioo a b, φ x * f x := by
    rw [← integral_sub i2 i3]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only
    ring
  rw [Opens.coe_Ioo, e3]
  linarith

open SobolevInterval in
/-- **`H²` regularity of the weak solution in one dimension**: if the coefficient `α` is `C¹`
on `[a, b]` and does not vanish there, then the weak solution `u ∈ H^1_0(a, b)` of
`-(α u')' + β u' + γ u = f` with `f ∈ L²(a, b)` lies in `H²(a, b)`. The flux `α u'` has the weak
derivative `β u' + γ u - f ∈ L²` (`EllipticInterval.hasWeakDerivOn_mulL_deriv`), hence an
absolutely continuous representative `g` (`HasWeakDerivOn.exists_ae_eq_integral`); then
`u' = g / α` is a product of two functions of `H^1(a, b)` and lies in `H^1(a, b)` by the product
rule `SobolevInterval.memSobolevInterval_mul`. This is what the Aubin–Nitsche `L²` estimate
needs of the dual problem; [quarteroni2000numerical] quotes it from [QV94] for (12.60). -/
theorem isWeakSolution_mem_sobolevInterval_two (hab : a < b)
    (αL βL γL : Lp ℝ ⊤ (volume.restrict (Ioo a b))) {α : ℝ → ℝ}
    (hαL : αL =ᵐ[volume.restrict (Ioo a b)] α) (hα : ContDiffOn ℝ 1 α (Icc a b))
    (hα0 : ∀ x ∈ Icc a b, α x ≠ 0) (f : Lp ℝ 2 (volume.restrict (Ioo a b)))
    {u : SobolevInterval 1 a b}
    (hu : IsGalerkinSolution (form a b αL βL γL) (load a b f) (SobolevIntervalZero a b) u) :
    MemSobolevInterval (fn u) 2 a b := by
  -- the flux `α u'` and its weak derivative
  set W : ℝ → ℝ := fun x ↦ βL x * deriv u 1 x + γL x * deriv u 0 x - f x with hWdef
  have hW : MemLp W 2 (volume.restrict (Ioo a b)) :=
    (((Lp.memLp (mulL βL (deriv u 1))).ae_eq (coeFn_mulL βL (deriv u 1))).add
      ((Lp.memLp (mulL γL (deriv u 0))).ae_eq (coeFn_mulL γL (deriv u 0)))).sub (Lp.memLp f)
  have hWint : IntegrableOn W (Ioo a b) := hW.integrable one_le_two
  have hweak := hasWeakDerivOn_mulL_deriv αL βL γL f hu
  obtain ⟨c, hc⟩ := hweak.exists_ae_eq_integral hab hWint
  set g : ℝ → ℝ := fun x ↦ c + ∫ t in a..x, W t with hgdef
  have hgc : ContinuousOn g (Icc a b) :=
    intervalIntegral.continuousOn_integral_of_integrableOn_Ioo hab.le hWint c
  -- `g` as an element of `H^1(a, b)`
  have hg1 : MemSobolevInterval g 1 a b :=
    memSobolevInterval_one_iff.2 ⟨hgc.memLp_two_restrict_Ioo, W,
      hasWeakDerivOn_integral hab.le hWint c, hW⟩
  obtain ⟨Gel, hGel⟩ := MemSobolevMultiIndex.exists_sobolevMultiIndex hg1
  have hGrep : EqOn (rep Gel) g (Icc a b) := rep_eq_of_continuousOn hab Gel hgc hGel
  -- `1/α` as an element of `H^1(a, b)`
  have hαinv : ContDiffOn ℝ ((1 : ℕ) : ℕ∞ω) (fun x ↦ (α x)⁻¹) (Icc a b) := by
    rw [Nat.cast_one]; exact hα.inv hα0
  set Ainv := ContDiffMapIcc.ofContDiffOn hab.le hab hαinv with hAinv
  set AinvH := ContDiffMapIcc.toSobolevInterval hab.le hab 1 Ainv with hAinvH
  have hArep : EqOn (rep AinvH) (fun x ↦ (α x)⁻¹) (Icc a b) := by
    refine rep_eq_of_continuousOn hab AinvH hαinv.continuousOn ?_
    refine (ContDiffMapIcc.fn_toSobolevInterval_ae_eq hab.le hab Ainv).trans ?_
    refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx ↦ ?_)
    rw [ContDiffMapIcc.extend_of_mem Ainv (Ioo_subset_Icc_self hx), hAinv]
    exact ContDiffMapIcc.coe_ofContDiffOn hab.le hab hαinv ⟨x, Ioo_subset_Icc_self hx⟩
  -- the product rule
  have hmul := memSobolevInterval_mul hab Gel AinvH
  have hu' : MemSobolevInterval (deriv u 1) 1 a b := by
    refine hmul.congr_ae ?_
    filter_upwards [hc, hαL, ae_restrict_mem measurableSet_Ioo] with x h1 h2 hx
    have hx' := Ioo_subset_Icc_self hx
    rw [hGrep hx', hArep hx', ← h1, h2]
    field_simp [hα0 x hx']
  exact memSobolevInterval_succ_iff.2 ⟨Lp.memLp _, deriv u 1, hasWeakDerivOn_fn u, hu'⟩

/-! ### The `H²` estimate -/

open SobolevInterval in
/-- An element `u ∈ H^1(a, b)` whose derivative `u'` is the function of an element
`U₁ ∈ H^1(a, b)` is the inclusion of an element `Φ ∈ H²(a, b)`, whose second derivative is
`U₁'`. -/
theorem exists_sobolevInterval_two (u U₁ : SobolevInterval 1 a b)
    (hU₁ : fn U₁ =ᵐ[volume.restrict (Ioo a b)] deriv u 1) :
    ∃ Φ : SobolevInterval 2 a b, inclusionCLM 1 a b Φ = u ∧ deriv Φ 2 = deriv U₁ 1 := by
  have h1 : HasWeakDerivOn (deriv u 0) (deriv u 1) (Opens.Ioo a b) := by
    rw [deriv_zero]; exact hasWeakDerivOn_fn u
  have h2 : HasWeakDerivOn (deriv u 1) (deriv U₁ 1) (Opens.Ioo a b) :=
    (hasWeakDerivOn_fn U₁).congr_ae hU₁ (Eventually.of_forall fun _ ↦ rfl)
  have hv : ∀ j : Fin 3, HasWeakIteratedDerivOn (j : ℕ) (![deriv u 0, deriv u 1, deriv U₁ 1] 0)
      (![deriv u 0, deriv u 1, deriv U₁ 1] j) (Opens.Ioo a b) := by
    intro j
    fin_cases j
    · exact HasWeakIteratedLineDerivOn.of_length_eq_zero rfl _
        ((Lp.memLp _).locallyIntegrableOn (Ω := Opens.Ioo a b) one_le_two)
    · exact h1
    · exact h1.hasWeakIteratedDerivOn_succ h2
  refine ⟨mk _ hv, ?_, rfl⟩
  refine ext fun j ↦ ?_
  fin_cases j <;> rfl

open SobolevInterval in
/-- The `C¹` coefficient `α` as an element of `H^1(a, b)`, with its representative and weak
derivative. -/
theorem exists_sobolevInterval_of_contDiffOn (hab : a < b) {α : ℝ → ℝ}
    (hα : ContDiffOn ℝ 1 α (Icc a b)) :
    ∃ A : SobolevInterval 1 a b, EqOn (rep A) α (Icc a b) ∧
      ∀ᵐ x ∂(volume.restrict (Ioo a b)), deriv A 1 x = derivWithin α (Icc a b) x := by
  have hα' : ContDiffOn ℝ ((1 : ℕ) : ℕ∞ω) α (Icc a b) := by rw [Nat.cast_one]; exact hα
  set A0 := ContDiffMapIcc.ofContDiffOn hab.le hab hα' with hA0
  refine ⟨ContDiffMapIcc.toSobolevInterval hab.le hab 1 A0, ?_, ?_⟩
  · refine rep_eq_of_continuousOn hab _ hα.continuousOn ?_
    refine (ContDiffMapIcc.fn_toSobolevInterval_ae_eq hab.le hab A0).trans ?_
    refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx ↦ ?_)
    rw [ContDiffMapIcc.extend_of_mem A0 (Ioo_subset_Icc_self hx), hA0]
    exact ContDiffMapIcc.coe_ofContDiffOn hab.le hab hα' ⟨x, Ioo_subset_Icc_self hx⟩
  · filter_upwards [A0.coeFn_derivLp 1, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    rw [ContDiffMapIcc.deriv_toSobolevInterval, hx, IccExtend_of_mem hab.le _
      (Ioo_subset_Icc_self hxI), hA0, ContDiffMapIcc.deriv_ofContDiffOn]
    change iteratedDerivWithin 1 α (Icc a b) x = _
    rw [iteratedDerivWithin_one]

open SobolevInterval in
/-- **`H²` regularity of the weak solution, with the estimate**: under the hypotheses of
`EllipticInterval.isWeakSolution_mem_sobolevInterval_two`, with `α ≥ α₀ > 0` and `|α'| ≤ A₁` on
`[a, b]`, the weak solution `u` is the inclusion of an element `Φ ∈ H²(a, b)` with
`‖u''‖_{L²} ≤ α₀⁻¹ (‖β‖_∞ ‖u'‖ + ‖γ‖_∞ ‖u‖ + ‖f‖ + A₁ ‖u'‖)`. The second derivative is identified
through the product rule applied to `α u'`: the two weak derivatives `(α u')' = β u' + γ u - f` and
`(α u')' = α' u' + α u''` agree almost everywhere, so `α u'' = β u' + γ u - f - α' u'`. -/
theorem exists_sobolevInterval_two_of_isWeakSolution (hab : a < b)
    (αL βL γL : Lp ℝ ⊤ (volume.restrict (Ioo a b))) {α : ℝ → ℝ}
    (hαL : αL =ᵐ[volume.restrict (Ioo a b)] α) (hα : ContDiffOn ℝ 1 α (Icc a b))
    {α₀ A₁ : ℝ} (hα₀ : 0 < α₀) (hαpos : ∀ x ∈ Icc a b, α₀ ≤ α x)
    (hA₁ : ∀ x ∈ Icc a b, |derivWithin α (Icc a b) x| ≤ A₁)
    (f : Lp ℝ 2 (volume.restrict (Ioo a b))) {u : SobolevInterval 1 a b}
    (hu : IsGalerkinSolution (form a b αL βL γL) (load a b f) (SobolevIntervalZero a b) u) :
    ∃ Φ : SobolevInterval 2 a b, inclusionCLM 1 a b Φ = u ∧
      ‖deriv Φ 2‖ ≤ α₀⁻¹ * ((‖βL‖ * ‖deriv u 1‖ + ‖γL‖ * ‖deriv u 0‖ + ‖f‖)
        + A₁ * ‖deriv u 1‖) := by
  have hα0 : ∀ x ∈ Icc a b, α x ≠ 0 := fun x hx ↦ (hα₀.trans_le (hαpos x hx)).ne'
  have hA₁0 : 0 ≤ A₁ := (abs_nonneg _).trans (hA₁ a (left_mem_Icc.2 hab.le))
  -- `u' ∈ H^1(a, b)`
  have hu2 := isWeakSolution_mem_sobolevInterval_two hab αL βL γL hαL hα hα0 f hu
  obtain ⟨-, w, hw, hw1⟩ := memSobolevInterval_succ_iff.1 hu2
  have hw' : w =ᵐ[volume.restrict (Ioo a b)] deriv u 1 :=
    (ae_restrict_iff' measurableSet_Ioo).2 (hw.ae_eq (hasWeakDerivOn_fn u))
  obtain ⟨U₁, hU₁⟩ := MemSobolevMultiIndex.exists_sobolevMultiIndex (hw1.congr_ae hw')
  obtain ⟨Φ, hΦ, hΦ2⟩ := exists_sobolevInterval_two u U₁ hU₁
  refine ⟨Φ, hΦ, ?_⟩
  rw [hΦ2]
  -- the flux identity
  set W : ℝ → ℝ := fun x ↦ βL x * deriv u 1 x + γL x * deriv u 0 x - f x with hWdef
  have hW : MemLp W 2 (volume.restrict (Ioo a b)) :=
    (((Lp.memLp (mulL βL (deriv u 1))).ae_eq (coeFn_mulL βL (deriv u 1))).add
      ((Lp.memLp (mulL γL (deriv u 0))).ae_eq (coeFn_mulL γL (deriv u 0)))).sub (Lp.memLp f)
  have hweak := hasWeakDerivOn_mulL_deriv αL βL γL f hu
  obtain ⟨A, hArep, hA'⟩ := exists_sobolevInterval_of_contDiffOn hab hα
  have hprod := hasWeakDerivOn_rep_mul hab A U₁
  have hrepU₁ := fn_ae_eq_rep hab U₁
  -- the two weak derivatives of `α u'` agree
  have hfn : (fun t ↦ rep A t * rep U₁ t) =ᵐ[volume.restrict (Ioo a b)]
      fun x ↦ αL x * deriv u 1 x := by
    filter_upwards [hαL, hU₁, hrepU₁, ae_restrict_mem measurableSet_Ioo] with x h1 h2 h3 hx
    rw [hArep (Ioo_subset_Icc_self hx), h1, ← h3]
    exact congrArg (α x * ·) h2
  have huniq := (ae_restrict_iff' measurableSet_Ioo).2
    ((hprod.congr_ae hfn (Eventually.of_forall fun _ ↦ rfl)).ae_eq hweak)
  -- the norm of `W`
  have hWL : ‖hW.toLp W‖ ≤ ‖βL‖ * ‖deriv u 1‖ + ‖γL‖ * ‖deriv u 0‖ + ‖f‖ := by
    have e : hW.toLp W = mulL βL (deriv u 1) + mulL γL (deriv u 0) - f := by
      refine Lp.ext (hW.coeFn_toLp.trans ?_)
      filter_upwards [Lp.coeFn_sub (mulL βL (deriv u 1) + mulL γL (deriv u 0)) f,
        Lp.coeFn_add (mulL βL (deriv u 1)) (mulL γL (deriv u 0)), coeFn_mulL βL (deriv u 1),
        coeFn_mulL γL (deriv u 0)] with x h1 h2 h3 h4
      rw [h1, Pi.sub_apply, h2, Pi.add_apply, h3, h4]
    rw [e]
    refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add (norm_mulL_apply_le _ _) (norm_mulL_apply_le _ _))) le_rfl)
  -- the pointwise bound on `u''`
  refine (Lp.norm_le_of_abs_le (deriv U₁ 1) (hW.toLp W) (deriv u 1) (inv_nonneg.2 hα₀.le) hA₁0
    ?_).trans (by gcongr)
  filter_upwards [huniq, hA', hU₁, hrepU₁, hW.coeFn_toLp, ae_restrict_mem measurableSet_Ioo]
    with x h1 h2 h3 h4 h5 hx
  have hx' := Ioo_subset_Icc_self hx
  have hαx : α₀ ≤ α x := hαpos x hx'
  have hαx0 : 0 < α x := hα₀.trans_le hαx
  rw [h5]
  -- `α u'' = W - α' u'`
  have e : α x * deriv U₁ 1 x = W x - derivWithin α (Icc a b) x * deriv u 1 x := by
    have h3' : fn U₁ x = deriv u 1 x := h3
    rw [hArep hx', h2, ← h4, h3'] at h1
    simp only [hWdef]
    linarith
  have hbound : |α x * deriv U₁ 1 x| ≤ |W x| + A₁ * |deriv u 1 x| := by
    rw [e]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    gcongr
    exact hA₁ x hx'
  rw [abs_mul, abs_of_pos hαx0] at hbound
  rw [inv_mul_eq_div, le_div_iff₀ hα₀]
  calc |deriv U₁ 1 x| * α₀ ≤ |deriv U₁ 1 x| * α x := by gcongr
    _ = α x * |deriv U₁ 1 x| := mul_comm _ _
    _ ≤ _ := hbound

/-! ### The Aubin–Nitsche `L²` estimate -/

/-- The form with `β = 0` is symmetric. -/
theorem form_comm (αL γL : Lp ℝ ⊤ (volume.restrict (Ioo a b))) (u v : SobolevInterval 1 a b) :
    form a b αL 0 γL u v = form a b αL 0 γL v u := by
  rw [form_apply, form_apply]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_zero ℝ ⊤ (volume.restrict (Ioo a b))] with x hx
  rw [hx, Pi.zero_apply]
  ring

open SobolevInterval in
/-- The norm of an element of `H²(a, b)` is at most the sum of the `L²` norms of its three
derivatives. -/
theorem norm_le_sum_norm_deriv (Φ : SobolevInterval 2 a b) :
    ‖Φ‖ ≤ ‖deriv Φ 0‖ + ‖deriv Φ 1‖ + ‖deriv Φ 2‖ := by
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, norm_sq_eq,
    Fin.sum_univ_three]
  nlinarith [norm_nonneg (deriv Φ 0), norm_nonneg (deriv Φ 1), norm_nonneg (deriv Φ 2)]

open SobolevInterval in
/-- **The Aubin–Nitsche `L²` estimate** in one dimension, the engine of (12.60)
([quarteroni2000numerical] §12.4.4): for `α ≥ α₀ > 0` of class `C¹`, `γ ≥ 0`, `β = 0`, and a
subspace `K ≤ H^1_0(a, b)` with the approximation property
`∀ Φ ∈ H² ∩ H^1_0, ∃ v ∈ K, |Φ - v|_{H¹} ≤ δ ‖Φ‖_{H²}`, the Galerkin error satisfies
`‖u - u_h‖_{L²} ≤ M_s C_reg δ |u - u_h|_{H¹}`, where `M_s` is the seminorm bound of the form
on `H^1_0` and `C_reg` the constant of the `H²` estimate for the dual problem.

Proof: with `e = u - u_h` and `φ ∈ H^1_0` the solution of the dual problem `a(v, φ) = (v, e)`,
`‖e‖² = a(e, φ) = a(e, φ - v)` for every `v ∈ K` by Galerkin orthogonality (the form is
symmetric for `β = 0`), and `φ` lies in `H²` with `‖φ‖_{H²} ≤ C_reg ‖e‖` by
`exists_sobolevInterval_two_of_isWeakSolution`. -/
theorem galerkin_norm_sub_le_l2 (hab : a < b) (αL γL : Lp ℝ ⊤ (volume.restrict (Ioo a b)))
    {α : ℝ → ℝ} (hαL : αL =ᵐ[volume.restrict (Ioo a b)] α) (hα : ContDiffOn ℝ 1 α (Icc a b))
    {α₀ A₁ : ℝ} (hα₀ : 0 < α₀) (hαpos : ∀ x ∈ Icc a b, α₀ ≤ α x)
    (hA₁ : ∀ x ∈ Icc a b, |derivWithin α (Icc a b) x| ≤ A₁)
    (hγ : ∀ᵐ x ∂(volume.restrict (Ioo a b)), 0 ≤ γL x) (f : Lp ℝ 2 (volume.restrict (Ioo a b)))
    {K : Submodule ℝ (SobolevInterval 1 a b)} (hK : K ≤ SobolevIntervalZero a b) {δ : ℝ}
    (hδ : 0 ≤ δ)
    (happrox : ∀ Φ : SobolevInterval 2 a b, inclusionCLM 1 a b Φ ∈ SobolevIntervalZero a b →
      ∃ v ∈ K, seminorm 1 a b (inclusionCLM 1 a b Φ - v) ≤ δ * ‖Φ‖)
    {u uh : SobolevInterval 1 a b}
    (hu : IsGalerkinSolution (form a b αL 0 γL) (load a b f) (SobolevIntervalZero a b) u)
    (huh : IsGalerkinSolution (form a b αL 0 γL) (load a b f) K uh) :
    ‖deriv (u - uh) 0‖ ≤ (‖αL‖ + ((b - a) / Real.sqrt 2) ^ 2 * ‖γL‖)
      * (((b - a) / Real.sqrt 2) ^ 2 / α₀ + (b - a) / Real.sqrt 2 / α₀
        + α₀⁻¹ * (‖γL‖ * (((b - a) / Real.sqrt 2) ^ 2 / α₀) + 1
          + A₁ * ((b - a) / Real.sqrt 2 / α₀)))
      * δ * seminorm 1 a b (u - uh) := by
  set CP := (b - a) / Real.sqrt 2 with hCP
  have hCP0 : 0 ≤ CP := by have := hab.le; positivity
  set Ms := ‖αL‖ + CP ^ 2 * ‖γL‖ with hMs
  set Creg := CP ^ 2 / α₀ + CP / α₀ + α₀⁻¹ * (‖γL‖ * (CP ^ 2 / α₀) + 1 + A₁ * (CP / α₀))
    with hCreg
  have hA₁0 : 0 ≤ A₁ := (abs_nonneg _).trans (hA₁ a (left_mem_Icc.2 hab.le))
  have hCreg0 : 0 ≤ Creg := by positivity
  have hMs0 : 0 ≤ Ms := by positivity
  have hαae : ∀ᵐ x ∂(volume.restrict (Ioo a b)), α₀ ≤ αL x := by
    filter_upwards [hαL, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    rw [hx]; exact hαpos x (Ioo_subset_Icc_self hxI)
  -- the error and its `L²` part
  set e := u - uh with he
  have heK : e ∈ SobolevIntervalZero a b := (SobolevIntervalZero a b).sub_mem hu.1 (hK huh.1)
  set e₀ := deriv e 0 with he₀
  -- the dual problem
  obtain ⟨φ, hφ, -⟩ := existsUnique_isWeakSolution hab αL γL hα₀ hαae hγ e₀
  obtain ⟨Φ, hΦ, hΦ2⟩ := exists_sobolevInterval_two_of_isWeakSolution hab αL 0 γL hαL hα hα₀
    hαpos hA₁ e₀ hφ
  -- `‖e₀‖² = a(e, φ)`
  have h1 : ‖e₀‖ ^ 2 = form a b αL 0 γL e φ := by
    rw [form_comm, hφ.2 e heK, load_apply_inner, ← he₀, real_inner_self_eq_norm_sq]
  -- Galerkin orthogonality
  obtain ⟨v, hvK, hv⟩ := happrox Φ (hΦ ▸ hφ.1)
  rw [hΦ] at hv
  have horth : form a b αL 0 γL e v = 0 := by
    rw [he, map_sub, sub_apply, hu.2 v (hK hvK), huh.2 v hvK, sub_self]
  have h2 : form a b αL 0 γL e φ = form a b αL 0 γL e (φ - v) := by
    rw [map_sub (form a b αL 0 γL e) φ v, horth, sub_zero]
  -- the bound
  have h3 : |form a b αL 0 γL e (φ - v)| ≤ Ms * seminorm 1 a b e * seminorm 1 a b (φ - v) := by
    have := abs_form_le_seminorm hab αL 0 γL heK
      ((SobolevIntervalZero a b).sub_mem hφ.1 (hK hvK))
    rwa [norm_zero, mul_zero, add_zero] at this
  -- the regularity bound `‖Φ‖ ≤ Creg ‖e₀‖`
  have hφsemi : seminorm 1 a b φ ≤ CP / α₀ * ‖e₀‖ :=
    seminorm_le_of_isGalerkinSolution hab αL γL hα₀ hαae hγ e₀ le_rfl hφ
  have hφ0 : ‖deriv φ 0‖ ≤ CP * seminorm 1 a b φ := SobolevIntervalZero.norm_deriv_zero_le hab hφ.1
  have hΦ0 : deriv Φ 0 = deriv φ 0 := by rw [← hΦ, deriv_inclusionCLM]; rfl
  have hΦ1 : deriv Φ 1 = deriv φ 1 := by rw [← hΦ, deriv_inclusionCLM]; rfl
  have hφsemi' : seminorm 1 a b φ = ‖deriv φ 1‖ := rfl
  have hΦnorm : ‖Φ‖ ≤ Creg * ‖e₀‖ := by
    refine (norm_le_sum_norm_deriv Φ).trans ?_
    rw [hΦ0, hΦ1, norm_zero, zero_mul, zero_add] at *
    rw [hΦ0, hΦ1, ← hφsemi']
    have hb0 : ‖deriv φ 0‖ ≤ CP ^ 2 / α₀ * ‖e₀‖ := by
      refine hφ0.trans ?_
      calc CP * seminorm 1 a b φ ≤ CP * (CP / α₀ * ‖e₀‖) := by gcongr
        _ = CP ^ 2 / α₀ * ‖e₀‖ := by ring
    have hb2 : ‖deriv Φ 2‖ ≤ α₀⁻¹ * (‖γL‖ * (CP ^ 2 / α₀) + 1 + A₁ * (CP / α₀)) * ‖e₀‖ := by
      refine hΦ2.trans ?_
      have := norm_nonneg e₀
      have hγ0 := norm_nonneg γL
      calc α₀⁻¹ * (‖γL‖ * ‖deriv φ 0‖ + ‖e₀‖ + A₁ * seminorm 1 a b φ)
          ≤ α₀⁻¹ * (‖γL‖ * (CP ^ 2 / α₀ * ‖e₀‖) + ‖e₀‖ + A₁ * (CP / α₀ * ‖e₀‖)) := by
            gcongr
        _ = α₀⁻¹ * (‖γL‖ * (CP ^ 2 / α₀) + 1 + A₁ * (CP / α₀)) * ‖e₀‖ := by ring
    rw [hCreg]
    linarith
  -- assembling
  have hsq : ‖e₀‖ ^ 2 ≤ Ms * Creg * δ * seminorm 1 a b e * ‖e₀‖ := by
    calc ‖e₀‖ ^ 2 = form a b αL 0 γL e (φ - v) := by rw [h1, h2]
      _ ≤ |form a b αL 0 γL e (φ - v)| := le_abs_self _
      _ ≤ Ms * seminorm 1 a b e * seminorm 1 a b (φ - v) := h3
      _ ≤ Ms * seminorm 1 a b e * (δ * (Creg * ‖e₀‖)) := by
          gcongr
          exact hv.trans (by gcongr)
      _ = Ms * Creg * δ * seminorm 1 a b e * ‖e₀‖ := by ring
  rcases eq_or_lt_of_le (norm_nonneg e₀) with h0 | h0
  · rw [← h0]
    have := apply_nonneg (seminorm 1 a b) e
    positivity
  · rw [sq] at hsq
    exact le_of_mul_le_mul_right hsq h0

end EllipticInterval

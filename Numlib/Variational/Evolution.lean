import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Numlib.Analysis.ODE.Gronwall
import Numlib.Approximation.BrokenPolynomial
import Numlib.Projection.OneDimensional
import Numlib.Variational.Galerkin
import Numlib.Variational.LaxMilgram

/-!
# Galerkin semi-discretizations of evolution problems and the θ-method

Galerkin semi-discretizations of linear evolution problems and their time discretization by the
θ-method, at the level where the estimates are proved: a real inner product space `K` — the trial
space with the `L²` inner product, finite-dimensional in every application — a bounded bilinear
form `a t : SesqForm ℝ K` (the spatial operator, possibly time-dependent) and a source
`F t : K →L[ℝ] ℝ`. The semi-discrete problem is the linear ODE `⟪u'(t), v⟫ + a t (u t) v = F t v`
for all `v ∈ K` (`Variational.IsSemidiscreteGalerkin`, [quarteroni2000numerical] (13.13), (13.65),
(13.68)), and every energy estimate of the parabolic and hyperbolic chapters of that book
(§13.1, §13.3, §13.10) is one of three consequences of the identity
`d/dt ‖u‖² = 2 (F t (u t) - a t (u t) (u t))` (`IsSemidiscreteGalerkin.hasDerivWithinAt_norm_sq`):

* **exponential decay** under `L²`-coercivity `γ ‖v‖² ≤ a v v`
  (`IsSemidiscreteGalerkin.norm_sq_le_exp`) — the heat equation's
  `E(t) ≤ e^{-γt} E(0) + γ⁻¹ ∫ e^{γ(s-t)} F(s) ds`, with `γ = ν / C_P²` from Poincaré;
* **dissipation** under `μ₀ ‖v‖² + ½ Q(v) ≤ a v v` with a nonnegative "boundary/jump" functional
  `Q` (`IsSemidiscreteGalerkin.norm_sq_add_integral_le`) — the transport estimates with the
  outflow term `a(β) u(β)²` and the discontinuous Galerkin jump terms;
* **Gronwall growth** under `-m(t) ‖v‖² + ½ Q(v) ≤ a v v`
  (`IsSemidiscreteGalerkin.norm_sq_add_integral_le_exp`) — the estimate when the reaction term
  has the wrong sign.

All three are instances of the differential Gronwall inequalities of
`Numlib/Analysis/ODE/Gronwall.lean`, with the derivative of the energy taken within `[0, T]`. The
raw integrated form `IsSemidiscreteGalerkin.norm_sq_add_integral_le_integral` sits below the
dissipation estimate: from a pointwise `2 (F(u) - a(u, u)) + w ≤ g` on `[0, T)` with `w`, `g`
continuous it gives `‖u t‖² + ∫₀ᵗ w ≤ ‖u₀‖² + ∫₀ᵗ g`, and `norm_sq_add_integral_le` is that with
Young's inequality already spent on the source. An estimate whose source is absorbed by a
*boundary* term rather than by coercivity — (13.69), where the inflow datum is absorbed by the jump
at `x₀` — has no `φ` to put on the right and needs the raw form.

The θ-method `⟪(u⁺ - u)/Δt, v⟫ + a (θ u⁺ + (1-θ) u) v = θ ℓ₁ v + (1-θ) ℓ₀ v`
(`Variational.IsThetaStep`, [quarteroni2000numerical] (13.17)) is a *relation* between
consecutive iterates, so that the implicit cases need no inverse in the definition; existence and
uniqueness of the step is Lax–Milgram for the form `⟪·, ·⟫ + θ Δt a` (`IsThetaStep.existsUnique`).
It is analysed twice, because the two arguments have different hypotheses. The **energy
identity** `½ (‖u⁺‖² - ‖u‖²) = -Δt a(w, w) - (θ - ½) ‖u⁺ - u‖²`, `w = θ u⁺ + (1-θ) u`
(`IsThetaStep.energy_identity`), needs only positivity of `a` and gives unconditional stability for
`θ ≥ ½` (`IsThetaStep.norm_le_of_half_le`) and, for backward Euler, the telescoping bounds
`‖u^n‖² + 2Δt ∑ a(u^{k+1}, u^{k+1}) ≤ ‖u^0‖²` and their versions with sources
(`IsThetaStep.norm_sq_add_sum_le`, `norm_sq_add_sum_le_of_coercive`, `norm_sq_add_sum_le_of_le`);
it covers the nonsymmetric transport forms. The **spectral argument** needs a symmetric coercive
`a`: the eigenpairs of the form relative to the inner product (`Variational.IsFormEigenpair`,
[quarteroni2000numerical] Definition 13.1 and its discrete form (13.22)) are the eigenvectors of
the operator of the form, so they form an orthonormal basis
(`exists_orthonormalBasis_isFormEigenpair`), and in an eigenvector direction the step multiplies
the coordinate by `r_θ(λ Δt) = (1 - (1-θ) λ Δt) / (1 + θ λ Δt)`
(`IsThetaStep.inner_eq_of_isFormEigenpair`); hence for `θ < ½` the step is nonexpansive for
every datum iff `(1 - 2θ) λ_max Δt ≤ 2` (`IsThetaStep.forall_norm_le_iff_of_lt_half`). The
sufficiency half is obtained without eigenvectors, in any real Hilbert space, from the operator
Cauchy–Schwarz inequality `‖B w‖² ≤ λ_max ⟪B w, w⟫` for the positive symmetric operator `B` of the
form (`IsThetaStep.norm_le_of_le_of_lt_half`), which is what the matrix-level module
`Numlib/FiniteDifference/Parabolic` uses in the `M`-inner product.

The last section is the upwind discontinuous Galerkin form for `u_t + a u_x + a₀ u` on the broken
polynomial space of `Numlib/Approximation/BrokenPolynomial` (`Variational.dgUpwindForm`,
[quarteroni2000numerical] (13.68)), whose energy identity
`b(v, v) = ½ a(β) v⁻(β)² + ½ ∑_j a(x_j) [v]_j² + ∫ (a₀ - a'/2) v²` (`dgUpwindForm_apply_self`) is
what feeds the dissipation estimate; the continuous Galerkin form is its restriction to the
jump-free subspace (`transportForm_apply_self_of_continuous`). The coefficients `a`, `a₀` enter
as functions with an interval integrability hypothesis, which is what makes the forms bilinear;
the energy identities ask for `a` differentiable with continuous derivative, as the book does.
The coordinate descriptions (mass and stiffness matrices) are in
`Numlib/FiniteDifference/Parabolic`, which imports this module.

## Conventions

The trial space is a real inner product space `K` with no completeness assumed where none is
used; `[CompleteSpace K]` appears exactly where the operator `SesqForm.toOperator a` of the form
does (Lax–Milgram, the eigenvector characterization, the operator Cauchy–Schwarz route), and
`[FiniteDimensional ℝ K]` where the spectral theorem does. Positivity of a form is
`a.IsCoerciveWith 0` and coercivity `a.IsCoerciveWith c`, as elsewhere in `Numlib/Variational`.
The time derivative is `HasDerivWithinAt u (u' t) (Icc 0 T) t`, the one-sided convention at the
endpoints, and the derivative `u'` is existentially quantified inside the predicate.
-/

open Set Filter Topology intervalIntegral Real
open scoped RealInnerProductSpace Matrix Interval
open MeasureTheory (volume)

noncomputable section

/-- A bilinear map on a finite-dimensional real inner product space is bounded: the bounded
form it defines. Belongs beside `SesqForm.ofOperator` in `Numlib/Variational/Forms.lean`. -/
def SesqForm.ofBilin {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [FiniteDimensional ℝ K] (b : K →ₗ[ℝ] K →ₗ[ℝ] ℝ) : SesqForm ℝ K :=
  (LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (K →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (K →L[ℝ] ℝ)).toLinearMap ∘ₗ b) :
      K →L[ℝ] K →L[ℝ] ℝ)

/-- The form of a bilinear map is the bilinear map. -/
@[simp]
theorem SesqForm.ofBilin_apply {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [FiniteDimensional ℝ K] (b : K →ₗ[ℝ] K →ₗ[ℝ] ℝ) (u v : K) : SesqForm.ofBilin b u v = b u v :=
  rfl

namespace Variational

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-! ### The semi-discrete Galerkin problem -/

/-- **The semi-discrete Galerkin problem** ([quarteroni2000numerical] (13.13); (13.65) and (13.68)
for the transport equation; with `K` the whole space, the weak formulation (13.12) itself):
`u : ℝ → K` solves `⟪u'(t), v⟫ + a t (u t) v = F t v` for all `v ∈ K` and `t ∈ [0, T]`, with
`u 0 = u₀`. The derivative is taken within `[0, T]`, one-sided at the endpoints, and is
existentially quantified. -/
def IsSemidiscreteGalerkin (a : ℝ → SesqForm ℝ K) (F : ℝ → K →L[ℝ] ℝ) (u₀ : K) (T : ℝ)
    (u : ℝ → K) : Prop :=
  u 0 = u₀ ∧ ∃ u' : ℝ → K, ∀ t ∈ Icc 0 T,
    HasDerivWithinAt u (u' t) (Icc 0 T) t ∧ ∀ v, ⟪u' t, v⟫ + a t (u t) v = F t v

namespace IsSemidiscreteGalerkin

variable {a : ℝ → SesqForm ℝ K} {F : ℝ → K →L[ℝ] ℝ} {u₀ : K} {T : ℝ} {u : ℝ → K}

/-- **The energy identity**: `d/dt ‖u(t)‖² = 2 (F t (u t) - a t (u t) (u t))` within `[0, T]`,
from `HasDerivWithinAt.norm_sq` and the equation tested with `v = u t`. Every energy estimate of
the module is an integration of this identity. -/
theorem hasDerivWithinAt_norm_sq (h : IsSemidiscreteGalerkin a F u₀ T u) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun t => ‖u t‖ ^ 2) (2 * (F t (u t) - a t (u t) (u t))) (Icc 0 T) t := by
  obtain ⟨u', hu'⟩ := h.2
  obtain ⟨hd, heq⟩ := hu' t ht
  have key := hd.norm_sq
  have : ⟪u t, u' t⟫ = F t (u t) - a t (u t) (u t) := by
    rw [real_inner_comm, ← heq (u t)]; ring
  rwa [this] at key

/-- The solution is continuous on `[0, T]`. -/
theorem continuousOn (h : IsSemidiscreteGalerkin a F u₀ T u) : ContinuousOn u (Icc 0 T) := by
  obtain ⟨u', hu'⟩ := h.2
  exact fun t ht => (hu' t ht).1.continuousWithinAt

/-- The squared norm is continuous on `[0, T]`. -/
theorem continuousOn_norm_sq (h : IsSemidiscreteGalerkin a F u₀ T u) :
    ContinuousOn (fun t => ‖u t‖ ^ 2) (Icc 0 T) :=
  (continuous_norm.pow 2).comp_continuousOn h.continuousOn

/-- The one-sided derivative of the squared norm, in the form the Gronwall lemmas take. -/
theorem hasDerivWithinAt_norm_sq_Ici (h : IsSemidiscreteGalerkin a F u₀ T u) {t : ℝ}
    (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt (fun t => ‖u t‖ ^ 2) (2 * (F t (u t) - a t (u t) (u t))) (Ici t) t :=
  (h.hasDerivWithinAt_norm_sq (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
    (Icc_mem_nhdsGE_of_mem ht)

omit [InnerProductSpace ℝ K] in
/-- Young's inequality in the form `2 φ ‖v‖ ≤ γ ‖v‖² + φ² / γ` for `γ > 0`, the step that turns
`2 F(u) ≤ 2 ‖F‖ ‖u‖` into a bound absorbable by coercivity. -/
theorem two_mul_mul_norm_le {γ : ℝ} (hγ : 0 < γ) (φ : ℝ) (v : K) :
    2 * φ * ‖v‖ ≤ γ * ‖v‖ ^ 2 + φ ^ 2 / γ := by
  have h := mul_nonneg hγ.le (sq_nonneg (‖v‖ - φ / γ))
  have : γ * (‖v‖ - φ / γ) ^ 2 = γ * ‖v‖ ^ 2 - 2 * φ * ‖v‖ + φ ^ 2 / γ := by
    field_simp
    ring
  linarith

/-- **The exponential energy estimate** ([quarteroni2000numerical] (13.7) and the estimate after
(13.13)): if the form is `L²`-coercive, `γ ‖v‖² ≤ a t v v` with `γ > 0`, and `‖F t‖ ≤ φ t` with `φ`
continuous on `[0, T]`, then
`‖u t‖² ≤ e^{-γ t} ‖u₀‖² + γ⁻¹ ∫₀ᵗ e^{γ (s - t)} φ(s)² ds`. Proof: `E = ‖u‖²` has
`E' = 2 F(u) - 2 a(u, u) ≤ 2 φ ‖u‖ - 2 γ E ≤ -γ E + φ² / γ`, and the linear differential Gronwall
inequality `Gronwall.le_exp_neg_mul_add_integral_of_hasDerivWithinAt_le` integrates it. For the
heat equation `γ = ν / C_P²` with `C_P` the Poincaré constant and `φ = ‖f(t)‖_{L²}`. -/
theorem norm_sq_le_exp (h : IsSemidiscreteGalerkin a F u₀ T u) {γ : ℝ} (hγ : 0 < γ)
    (hcoer : ∀ t ∈ Icc 0 T, (a t).IsCoerciveWith γ) {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc 0 T))
    (hF : ∀ t ∈ Icc 0 T, ‖F t‖ ≤ φ t) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖u t‖ ^ 2 ≤ exp (-γ * t) * ‖u₀‖ ^ 2 + γ⁻¹ * ∫ s in (0 : ℝ)..t, exp (γ * (s - t)) * φ s ^ 2 := by
  have bound : ∀ s ∈ Ico 0 T,
      2 * (F s (u s) - a s (u s) (u s)) ≤ -γ * ‖u s‖ ^ 2 + φ s ^ 2 / γ := by
    intro s hs
    have hs' : s ∈ Icc 0 T := Ico_subset_Icc_self hs
    have h1 : F s (u s) ≤ φ s * ‖u s‖ :=
      (le_abs_self _).trans (((F s).le_opNorm (u s)).trans
        (mul_le_mul_of_nonneg_right (hF s hs') (norm_nonneg _)))
    have h2 : γ * ‖u s‖ ^ 2 ≤ a s (u s) (u s) := hcoer s hs' (u s)
    have h3 := two_mul_mul_norm_le hγ (φ s) (u s)
    linarith
  have key := Gronwall.le_exp_neg_mul_add_integral_of_hasDerivWithinAt_le
    (g := fun s => φ s ^ 2 / γ) h.continuousOn_norm_sq
    (fun s hs => h.hasDerivWithinAt_norm_sq_Ici hs) ((hφ.pow 2).div_const γ) bound ht
  rw [h.1, sub_zero] at key
  refine key.trans (le_of_eq ?_)
  rw [← integral_const_mul]
  congr 1
  exact integral_congr fun s _ => by ring

/-- **The energy estimate in its raw integrated form**: if the energy identity
`d/dt ‖u‖² = 2 (F(u) - a(u, u))` is dominated by `g - w` pointwise on `[0, T)`, with `w` and `g`
continuous, then `‖u t‖² + ∫₀ᵗ w ≤ ‖u₀‖² + ∫₀ᵗ g`. It is the variation-of-constants inequality with
zero coefficient applied to `Φ = ‖u‖² + ∫₀ᵗ w`.

This is the common form of the three estimates below: `norm_sq_add_integral_le` is this one after
Young's inequality has been spent on the source. Keeping the pointwise bound as a hypothesis is
what estimates whose source is absorbed by a *boundary* term need — [quarteroni2000numerical]
(13.69), where the inflow datum of the discontinuous Galerkin method is absorbed by the jump at
`x₀`, and there is no `φ` to put on the right. -/
theorem norm_sq_add_integral_le_integral (h : IsSemidiscreteGalerkin a F u₀ T u) {w g : ℝ → ℝ}
    (hw : ContinuousOn w (Icc 0 T)) (hg : ContinuousOn g (Icc 0 T))
    (bound : ∀ s ∈ Ico 0 T, 2 * (F s (u s) - a s (u s) (u s)) + w s ≤ g s)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖u t‖ ^ 2 + ∫ s in (0 : ℝ)..t, w s ≤ ‖u₀‖ ^ 2 + ∫ s in (0 : ℝ)..t, g s := by
  set Φ : ℝ → ℝ := fun s => ‖u s‖ ^ 2 + ∫ q in (0 : ℝ)..s, w q with hΦ
  have hΦc : ContinuousOn Φ (Icc 0 T) :=
    h.continuousOn_norm_sq.add (intervalIntegral.continuousOn_integral_Icc hw)
  have hΦ' : ∀ s ∈ Ico 0 T, HasDerivWithinAt Φ
      (2 * (F s (u s) - a s (u s) (u s)) + w s) (Ici s) s := fun s hs =>
    (h.hasDerivWithinAt_norm_sq_Ici hs).add (intervalIntegral.hasDerivWithinAt_integral_Ici hw hs)
  have key := Gronwall.le_exp_integral_mul_of_hasDerivWithinAt_le (p := fun _ => (0 : ℝ)) (q := g)
    hΦc hΦ' continuousOn_const hg (fun s hs => by simpa using bound s hs) ht
  have h1 : ‖u 0‖ ^ 2 = ‖u₀‖ ^ 2 := by rw [h.1]
  simpa [hΦ, h1] using key

/-- **The dissipative energy estimate** ([quarteroni2000numerical] (13.66), (13.69)): if
`μ₀ ‖v‖² + ½ Q t v ≤ a t v v` with `μ₀ > 0` and a functional `Q` continuous along the solution
(the outflow term `a(β) v(β)²` and the jump terms of the discontinuous Galerkin form), and
`‖F t‖ ≤ φ t` with `φ` continuous, then
`‖u t‖² + ∫₀ᵗ (μ₀ ‖u‖² + Q(u)) ≤ ‖u₀‖² + μ₀⁻¹ ∫₀ᵗ φ²`. Proof: `E' + μ₀ ‖u‖² + Q(u) ≤ φ² / μ₀` by
Young's inequality, and then `norm_sq_add_integral_le_integral`. No sign of `Q` is needed. -/
theorem norm_sq_add_integral_le (h : IsSemidiscreteGalerkin a F u₀ T u) {μ₀ : ℝ} (hμ : 0 < μ₀)
    {Q : ℝ → K → ℝ} (hQc : ContinuousOn (fun t => Q t (u t)) (Icc 0 T))
    (hcoer : ∀ t ∈ Icc 0 T, ∀ v, μ₀ * ‖v‖ ^ 2 + Q t v / 2 ≤ a t v v)
    {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc 0 T)) (hF : ∀ t ∈ Icc 0 T, ‖F t‖ ≤ φ t)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖u t‖ ^ 2 + ∫ s in (0 : ℝ)..t, (μ₀ * ‖u s‖ ^ 2 + Q s (u s))
      ≤ ‖u₀‖ ^ 2 + μ₀⁻¹ * ∫ s in (0 : ℝ)..t, φ s ^ 2 := by
  have hwc : ContinuousOn (fun s => μ₀ * ‖u s‖ ^ 2 + Q s (u s)) (Icc 0 T) :=
    (continuousOn_const.mul h.continuousOn_norm_sq).add hQc
  have bound : ∀ s ∈ Ico 0 T,
      2 * (F s (u s) - a s (u s) (u s)) + (μ₀ * ‖u s‖ ^ 2 + Q s (u s)) ≤ φ s ^ 2 / μ₀ := by
    intro s hs
    have hs' : s ∈ Icc 0 T := Ico_subset_Icc_self hs
    have h1 : F s (u s) ≤ φ s * ‖u s‖ :=
      (le_abs_self _).trans (((F s).le_opNorm (u s)).trans
        (mul_le_mul_of_nonneg_right (hF s hs') (norm_nonneg _)))
    have h2 := hcoer s hs' (u s)
    have h3 := two_mul_mul_norm_le hμ (φ s) (u s)
    linarith
  refine (h.norm_sq_add_integral_le_integral (g := fun s => φ s ^ 2 / μ₀) hwc
    ((hφ.pow 2).div_const μ₀) bound ht).trans (le_of_eq ?_)
  rw [← integral_const_mul]
  congr 1
  exact integral_congr fun s _ => by ring

/-- **Energy dissipation without source** ([quarteroni2000numerical] §13.10.1, the "conservation
of the energy" `‖u_h(t)‖ ≤ ‖u_{0h}‖`): if `F = 0` and the form is positive, `t ↦ ‖u t‖` is
antitone on `[0, T]`; in particular `‖u t‖ ≤ ‖u₀‖`. -/
theorem norm_le_of_nonneg (h : IsSemidiscreteGalerkin a F u₀ T u) (hF : ∀ t, F t = 0)
    (hpos : ∀ t ∈ Icc 0 T, (a t).IsCoerciveWith 0) :
    AntitoneOn (fun t => ‖u t‖) (Icc 0 T) := by
  have hsq : AntitoneOn (fun t => ‖u t‖ ^ 2) (Icc 0 T) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T) h.continuousOn_norm_sq
      (f' := fun t => 2 * (F t (u t) - a t (u t) (u t))) (fun t ht => ?_) fun t ht => ?_
    · exact (h.hasDerivWithinAt_norm_sq (interior_subset ht)).mono interior_subset
    · have := hpos t (interior_subset ht) (u t)
      simp only [zero_mul, RCLike.re_to_real] at this
      simp only [hF, zero_apply]
      linarith
  intro s hs t ht hst
  have := hsq hs ht hst
  simpa using pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero |>.1 this

/-- **The Gronwall-type energy estimate for a non-dissipative form**
([quarteroni2000numerical] (13.67)): if `-m(t) ‖v‖² + ½ Q t v ≤ a t v v` with `m ≥ 0` continuous
(the reaction coefficient with the wrong sign), `Q ≥ 0` continuous along the solution, and
`‖F t‖ ≤ φ t`, then
`‖u t‖² + ∫₀ᵗ Q(u) ≤ (‖u₀‖² + ∫₀ᵗ φ²) exp (∫₀ᵗ (1 + 2 m))`. Proof: `Φ = ‖u‖² + ∫₀ᵗ Q(u)` has
`Φ' ≤ (1 + 2 m) ‖u‖² + φ² ≤ (1 + 2 m) Φ + φ²`, and
`Gronwall.le_mul_exp_integral_of_hasDerivWithinAt_le` integrates it. -/
theorem norm_sq_add_integral_le_exp (h : IsSemidiscreteGalerkin a F u₀ T u) {m : ℝ → ℝ}
    (hm : ContinuousOn m (Icc 0 T)) (hm0 : ∀ t ∈ Icc 0 T, 0 ≤ m t)
    {Q : ℝ → K → ℝ} (hQ0 : ∀ t v, 0 ≤ Q t v) (hQc : ContinuousOn (fun t => Q t (u t)) (Icc 0 T))
    (hcoer : ∀ t ∈ Icc 0 T, ∀ v, -(m t) * ‖v‖ ^ 2 + Q t v / 2 ≤ a t v v)
    {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc 0 T)) (hF : ∀ t ∈ Icc 0 T, ‖F t‖ ≤ φ t)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖u t‖ ^ 2 + ∫ s in (0 : ℝ)..t, Q s (u s)
      ≤ (‖u₀‖ ^ 2 + ∫ s in (0 : ℝ)..t, φ s ^ 2) * exp (∫ s in (0 : ℝ)..t, (1 + 2 * m s)) := by
  set Φ : ℝ → ℝ := fun s => ‖u s‖ ^ 2 + ∫ r in (0 : ℝ)..s, Q r (u r) with hΦ
  have hΦc : ContinuousOn Φ (Icc 0 T) :=
    h.continuousOn_norm_sq.add (intervalIntegral.continuousOn_integral_Icc hQc)
  have hΦ' : ∀ s ∈ Ico 0 T, HasDerivWithinAt Φ
      (2 * (F s (u s) - a s (u s) (u s)) + Q s (u s)) (Ici s) s := fun s hs =>
    (h.hasDerivWithinAt_norm_sq_Ici hs).add (intervalIntegral.hasDerivWithinAt_integral_Ici hQc hs)
  have bound : ∀ s ∈ Ico 0 T,
      2 * (F s (u s) - a s (u s) (u s)) + Q s (u s) ≤ (1 + 2 * m s) * Φ s + φ s ^ 2 := by
    intro s hs
    have hs' : s ∈ Icc 0 T := Ico_subset_Icc_self hs
    have h1 : F s (u s) ≤ φ s * ‖u s‖ :=
      (le_abs_self _).trans (((F s).le_opNorm (u s)).trans
        (mul_le_mul_of_nonneg_right (hF s hs') (norm_nonneg _)))
    have h2 := hcoer s hs' (u s)
    have h3 := two_mul_mul_norm_le one_pos (φ s) (u s)
    have h4 : 0 ≤ ∫ r in (0 : ℝ)..s, Q r (u r) :=
      integral_nonneg hs.1 fun r _ => hQ0 r (u r)
    have h5 : 0 ≤ 1 + 2 * m s := by linarith [hm0 s hs']
    have h6 : 0 ≤ (1 + 2 * m s) * ∫ r in (0 : ℝ)..s, Q r (u r) := mul_nonneg h5 h4
    simp only [hΦ, one_mul, div_one] at h3 ⊢
    nlinarith
  have key := Gronwall.le_mul_exp_integral_of_hasDerivWithinAt_le (p := fun s => 1 + 2 * m s)
    (g := fun s => φ s ^ 2) hΦc hΦ' (continuousOn_const.add (continuousOn_const.mul hm))
    (fun s hs => by linarith [hm0 s hs]) (hφ.pow 2) (fun s _ => sq_nonneg _) bound ht
  simpa only [hΦ, h.1, integral_same, add_zero] using key

end IsSemidiscreteGalerkin

/-! ### The θ-method -/

/-- **One step of the θ-method** ([quarteroni2000numerical] (13.17)): `u'` is the θ-update of `u`
for the form `a` and the source functionals `ℓ₀` (at the old time) and `ℓ₁` (at the new time)
when `⟪(u' - u)/Δt, v⟫ + a (θ u' + (1 - θ) u) v = θ ℓ₁ v + (1 - θ) ℓ₀ v` for every `v`. The values
`θ = 0, 1, ½` are the forward Euler, backward Euler and Crank–Nicolson methods. Stated as a
relation, so that the implicit cases need no inverse. -/
def IsThetaStep (a : SesqForm ℝ K) (θ Δt : ℝ) (ℓ₀ ℓ₁ : K →L[ℝ] ℝ) (u u' : K) : Prop :=
  ∀ v, ⟪Δt⁻¹ • (u' - u), v⟫ + a (θ • u' + (1 - θ) • u) v = θ * ℓ₁ v + (1 - θ) * ℓ₀ v

namespace IsThetaStep

variable {a : SesqForm ℝ K} {θ Δt : ℝ} {ℓ₀ ℓ₁ : K →L[ℝ] ℝ} {u u' : K}

/-- The θ-step multiplied out by `Δt ≠ 0`: `⟪u', v⟫ + θ Δt a u' v = ⟪u, v⟫ - (1 - θ) Δt a u v +
Δt (θ ℓ₁ v + (1 - θ) ℓ₀ v)` for every `v`, the form in which the step is a Galerkin problem for
the form `⟪·, ·⟫ + θ Δt a`. -/
theorem iff_forall_inner_add (hΔt : Δt ≠ 0) :
    IsThetaStep a θ Δt ℓ₀ ℓ₁ u u' ↔ ∀ v, ⟪u', v⟫ + θ * Δt * a u' v
      = ⟪u, v⟫ - (1 - θ) * Δt * a u v + Δt * (θ * ℓ₁ v + (1 - θ) * ℓ₀ v) := by
  have e : ∀ v, ⟪Δt⁻¹ • (u' - u), v⟫ + a (θ • u' + (1 - θ) • u) v
      - (θ * ℓ₁ v + (1 - θ) * ℓ₀ v)
      = Δt⁻¹ * ((⟪u', v⟫ + θ * Δt * a u' v)
        - (⟪u, v⟫ - (1 - θ) * Δt * a u v + Δt * (θ * ℓ₁ v + (1 - θ) * ℓ₀ v))) := by
    intro v
    simp only [real_inner_smul_left, inner_sub_left, map_add, map_smul, add_apply, smul_apply,
      smul_eq_mul]
    field_simp
    ring
  refine forall_congr' fun v => ?_
  rw [← sub_eq_zero, e v, mul_eq_zero, or_iff_right (inv_ne_zero hΔt), sub_eq_zero]

/-- The θ-step tested with one vector `v`, in the multiplied-out form. -/
theorem inner_add_eq (h : IsThetaStep a θ Δt ℓ₀ ℓ₁ u u') (hΔt : Δt ≠ 0) (v : K) :
    ⟪u', v⟫ + θ * Δt * a u' v
      = ⟪u, v⟫ - (1 - θ) * Δt * a u v + Δt * (θ * ℓ₁ v + (1 - θ) * ℓ₀ v) :=
  (iff_forall_inner_add hΔt).1 h v

/-- **Existence and uniqueness of the θ-step** ([quarteroni2000numerical] §13.3, the remark that
the system (13.16) is uniquely solvable): on a real Hilbert space, for `0 ≤ θ`, `0 < Δt` and a
positive form `a`, every `u` has exactly one θ-step `u'`. The form `⟪·, ·⟫ + θ Δt a` is coercive
with constant `1`, and `SesqForm.laxMilgram` solves the multiplied-out step. -/
theorem existsUnique [CompleteSpace K] (hθ : 0 ≤ θ) (hΔt : 0 < Δt) (hpos : a.IsCoerciveWith 0)
    (ℓ₀ ℓ₁ : K →L[ℝ] ℝ) (u : K) : ∃! u', IsThetaStep a θ Δt ℓ₀ ℓ₁ u u' := by
  set b : SesqForm ℝ K := innerSL ℝ + (θ * Δt) • a with hb
  set ℓ : K →L[ℝ] ℝ := innerSL ℝ u - ((1 - θ) * Δt) • a u + Δt • (θ • ℓ₁ + (1 - θ) • ℓ₀)
    with hℓ
  have hbc : b.IsCoerciveWith 1 := fun v => by
    have h0 := hpos v
    simp only [zero_mul, RCLike.re_to_real] at h0
    simp only [hb, add_apply, smul_apply, innerSL_apply_apply, real_inner_self_eq_norm_sq,
      smul_eq_mul, RCLike.re_to_real, one_mul]
    nlinarith [mul_nonneg hθ hΔt.le]
  have key := b.laxMilgram ℓ one_pos hbc
  simp_rw [iff_forall_inner_add hΔt.ne']
  convert key using 3 with u' v
  simp only [hb, hℓ, add_apply, smul_apply, sub_apply, innerSL_apply_apply, smul_eq_mul]

end IsThetaStep

/-- `½ (‖u‖² - ‖v‖²) ≤ ⟪u - v, u⟫` in any real inner product space: `⟪u - v, u⟫ = ‖u‖² - ⟪v, u⟫ ≥
‖u‖² - ‖u‖ ‖v‖ ≥ ‖u‖² - ½ (‖u‖² + ‖v‖²)` (the hint of [quarteroni2000numerical] Exercise 13.3).
It is the one inequality behind every backward Euler energy estimate. -/
theorem half_norm_sq_sub_le_inner_sub (u v : K) :
    (1 / 2 : ℝ) * (‖u‖ ^ 2 - ‖v‖ ^ 2) ≤ ⟪u - v, u⟫ := by
  rw [inner_sub_left, real_inner_self_eq_norm_sq]
  have h1 := real_inner_le_norm v u
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

namespace IsThetaStep

variable {a : SesqForm ℝ K} {θ Δt : ℝ} {ℓ₀ ℓ₁ : K →L[ℝ] ℝ} {u u' : K}

/-- **The energy identity of the θ-method**, source-free: with `w = θ u' + (1 - θ) u`,
`½ (‖u'‖² - ‖u‖²) = -Δt a(w, w) - (θ - ½) ‖u' - u‖²`. Test the step with `v = w` and write
`w = ½ (u' + u) + (θ - ½) (u' - u)`, so that `⟪u' - u, w⟫ = ½ (‖u'‖² - ‖u‖²) + (θ - ½) ‖u' - u‖²`.
No symmetry or positivity of `a` is used. -/
theorem energy_identity (h : IsThetaStep a θ Δt 0 0 u u') (hΔt : Δt ≠ 0) :
    (1 / 2 : ℝ) * (‖u'‖ ^ 2 - ‖u‖ ^ 2)
      = -(Δt * a (θ • u' + (1 - θ) • u) (θ • u' + (1 - θ) • u))
        - (θ - 1 / 2) * ‖u' - u‖ ^ 2 := by
  set w := θ • u' + (1 - θ) • u with hw
  have h1 := h w
  simp only [zero_apply, mul_zero, add_zero, real_inner_smul_left] at h1
  have h2 : ⟪u' - u, w⟫ = -(Δt * a w w) := by
    field_simp at h1
    linear_combination h1
  have h3 : ⟪u' - u, w⟫ = (1 / 2 : ℝ) * (‖u'‖ ^ 2 - ‖u‖ ^ 2) + (θ - 1 / 2) * ‖u' - u‖ ^ 2 := by
    have hw' : w = (1 / 2 : ℝ) • (u' + u) + (θ - 1 / 2) • (u' - u) := by
      rw [hw]; module
    rw [hw', inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, inner_sub_left, inner_add_right, inner_add_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm u u']
    ring
  linarith

/-- **Unconditional stability of the θ-method for `θ ≥ ½`** ([quarteroni2000numerical] §13.3.1,
first conclusion): for a positive form and `Δt > 0`, the source-free step is nonexpansive,
`‖u'‖ ≤ ‖u‖`. Both terms on the right of `energy_identity` are `≤ 0`; no symmetry of `a` is needed,
so this covers the nonsymmetric transport forms of §13.10. -/
theorem norm_le_of_half_le (h : IsThetaStep a θ Δt 0 0 u u') (hθ : 1 / 2 ≤ θ) (hΔt : 0 < Δt)
    (hpos : a.IsCoerciveWith 0) : ‖u'‖ ≤ ‖u‖ := by
  have hid := h.energy_identity hΔt.ne'
  have h0 := hpos (θ • u' + (1 - θ) • u)
  simp only [zero_mul, RCLike.re_to_real] at h0
  have : ‖u'‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    nlinarith [mul_nonneg hΔt.le h0, mul_nonneg (sub_nonneg.2 hθ) (sq_nonneg ‖u' - u‖)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

/-- **The backward Euler energy inequality** ([quarteroni2000numerical] (13.19)): for `Δt > 0` and
a source-free backward Euler step, `‖u'‖² + 2 Δt a(u', u') ≤ ‖u‖²`. Test with `v = u'` and use
`half_norm_sq_sub_le_inner_sub`; no positivity of `a` is used. -/
theorem norm_sq_add_two_mul_le (h : IsThetaStep a 1 Δt 0 0 u u') (hΔt : 0 < Δt) :
    ‖u'‖ ^ 2 + 2 * Δt * a u' u' ≤ ‖u‖ ^ 2 := by
  have h1 := h.inner_add_eq hΔt.ne' u'
  simp only [zero_apply, sub_self, zero_mul, mul_zero, add_zero, one_mul, sub_zero] at h1
  have h2 := half_norm_sq_sub_le_inner_sub u' u
  rw [inner_sub_left] at h2
  linarith

/-- The backward Euler energy inequality with a source, one step:
`‖u'‖² + 2 Δt a(u', u') ≤ ‖u‖² + 2 Δt ℓ₁(u')`. -/
theorem norm_sq_add_two_mul_le_add (h : IsThetaStep a 1 Δt ℓ₀ ℓ₁ u u') (hΔt : 0 < Δt) :
    ‖u'‖ ^ 2 + 2 * Δt * a u' u' ≤ ‖u‖ ^ 2 + 2 * Δt * ℓ₁ u' := by
  have h1 := h.inner_add_eq hΔt.ne' u'
  simp only [sub_self, zero_mul, add_zero, one_mul, sub_zero] at h1
  have h2 := half_norm_sq_sub_le_inner_sub u' u
  rw [inner_sub_left] at h2
  linarith

/-- **The telescoped backward Euler estimate** ([quarteroni2000numerical] (13.20)): for a
source-free backward Euler sequence `u k`, `‖u n‖² + 2 Δt ∑_{k<n} a(u (k+1), u (k+1)) ≤ ‖u 0‖²`.
Induction on `norm_sq_add_two_mul_le`. -/
theorem norm_sq_add_sum_le {u : ℕ → K} {n : ℕ} (hΔt : 0 < Δt)
    (h : ∀ k < n, IsThetaStep a 1 Δt 0 0 (u k) (u (k + 1))) :
    ‖u n‖ ^ 2 + 2 * Δt * ∑ k ∈ Finset.range n, a (u (k + 1)) (u (k + 1)) ≤ ‖u 0‖ ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih fun k hk => h k (Nat.lt_succ_of_lt hk)
    have hn := (h n (Nat.lt_succ_self n)).norm_sq_add_two_mul_le hΔt
    rw [Finset.sum_range_succ, mul_add]
    linarith

/-- One backward Euler step with a source, under `L²`-coercivity `α ‖v‖² ≤ a v v`:
`‖u'‖² + Δt a(u', u') ≤ ‖u‖² + α⁻¹ Δt ‖ℓ₁‖²`, from `2 Δt ℓ₁(u') ≤ Δt (‖ℓ₁‖² / α + α ‖u'‖²)` and
`α ‖u'‖² ≤ a(u', u')`. -/
theorem norm_sq_add_mul_le_of_coercive (h : IsThetaStep a 1 Δt ℓ₀ ℓ₁ u u') (hΔt : 0 < Δt)
    {α : ℝ} (hα : 0 < α) (hcoer : a.IsCoerciveWith α) :
    ‖u'‖ ^ 2 + Δt * a u' u' ≤ ‖u‖ ^ 2 + α⁻¹ * (Δt * ‖ℓ₁‖ ^ 2) := by
  have h1 := h.norm_sq_add_two_mul_le_add hΔt
  have h2 : ℓ₁ u' ≤ ‖ℓ₁‖ * ‖u'‖ := (le_abs_self _).trans (ℓ₁.le_opNorm u')
  have h3 : 2 * ‖ℓ₁‖ * ‖u'‖ ≤ α * ‖u'‖ ^ 2 + ‖ℓ₁‖ ^ 2 / α :=
    IsSemidiscreteGalerkin.two_mul_mul_norm_le hα ‖ℓ₁‖ u'
  have h4 : α * ‖u'‖ ^ 2 ≤ a u' u' := hcoer u'
  have h5 : α⁻¹ * (Δt * ‖ℓ₁‖ ^ 2) = Δt * (‖ℓ₁‖ ^ 2 / α) := by ring
  rw [h5]
  nlinarith [mul_le_mul_of_nonneg_left h3 hΔt.le, mul_le_mul_of_nonneg_left h2 hΔt.le]

/-- **The backward Euler estimate with sources under coercivity** ([quarteroni2000numerical]
(13.21), Remark 13.1, Exercise 13.4): for `α ‖v‖² ≤ a v v` with `α > 0`, `Δt > 0`, and a backward
Euler sequence with sources `ℓ k`,
`‖u n‖² + Δt ∑_{k<n} a(u (k+1), u (k+1)) ≤ ‖u 0‖² + α⁻¹ ∑_{k<n} Δt ‖ℓ (k+1)‖²`. The book's constant
`C(n)` is `max 1 α⁻¹` here, independent of `n`, at the price of halving the coefficient of the
form terms. -/
theorem norm_sq_add_sum_le_of_coercive {u : ℕ → K} {ℓ : ℕ → K →L[ℝ] ℝ} {n : ℕ} (hΔt : 0 < Δt)
    {α : ℝ} (hα : 0 < α) (hcoer : a.IsCoerciveWith α)
    (h : ∀ k < n, IsThetaStep a 1 Δt (ℓ k) (ℓ (k + 1)) (u k) (u (k + 1))) :
    ‖u n‖ ^ 2 + Δt * ∑ k ∈ Finset.range n, a (u (k + 1)) (u (k + 1))
      ≤ ‖u 0‖ ^ 2 + α⁻¹ * ∑ k ∈ Finset.range n, Δt * ‖ℓ (k + 1)‖ ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih fun k hk => h k (Nat.lt_succ_of_lt hk)
    have hn := (h n (Nat.lt_succ_self n)).norm_sq_add_mul_le_of_coercive hΔt hα hcoer
    rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add, mul_add]
    linarith

/-- One backward Euler step with a source, for a merely positive form and `0 < Δt ≤ ½`:
`‖u'‖² + 2 Δt a(u', u') ≤ (1 - Δt)⁻¹ (‖u‖² + Δt ‖ℓ₁‖²)`, from `2 Δt ℓ₁(u') ≤ Δt (‖ℓ₁‖² + ‖u'‖²)`. -/
theorem norm_sq_add_two_mul_le_of_le (h : IsThetaStep a 1 Δt ℓ₀ ℓ₁ u u') (hΔt : 0 < Δt)
    (hΔt' : Δt ≤ 1 / 2) (hpos : a.IsCoerciveWith 0) :
    ‖u'‖ ^ 2 + 2 * Δt * a u' u' ≤ (1 - Δt)⁻¹ * (‖u‖ ^ 2 + Δt * ‖ℓ₁‖ ^ 2) := by
  have h1 := h.norm_sq_add_two_mul_le_add hΔt
  have h2 : ℓ₁ u' ≤ ‖ℓ₁‖ * ‖u'‖ := (le_abs_self _).trans (ℓ₁.le_opNorm u')
  have h3 : 2 * ‖ℓ₁‖ * ‖u'‖ ≤ 1 * ‖u'‖ ^ 2 + ‖ℓ₁‖ ^ 2 / 1 :=
    IsSemidiscreteGalerkin.two_mul_mul_norm_le one_pos ‖ℓ₁‖ u'
  have h4 := hpos u'
  simp only [zero_mul, RCLike.re_to_real] at h4
  have hpos1 : 0 < 1 - Δt := by linarith
  have h5 : (1 - Δt) * ‖u'‖ ^ 2 + 2 * Δt * a u' u' ≤ ‖u‖ ^ 2 + Δt * ‖ℓ₁‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left h3 hΔt.le, mul_le_mul_of_nonneg_left h2 hΔt.le]
  rw [← div_eq_inv_mul, le_div_iff₀ hpos1]
  nlinarith [mul_nonneg (mul_nonneg two_pos.le hΔt.le) h4]

/-- **The backward Euler estimate with sources without coercivity** ([quarteroni2000numerical]
(13.21) as printed, with a constant `C(n)` depending on `n`): for a positive form, `0 < Δt ≤ ½`
and a backward Euler sequence with sources,
`‖u n‖² + 2 Δt ∑_{k<n} a(u (k+1), u (k+1)) ≤ (1 - Δt)⁻ⁿ (‖u 0‖² + ∑_{k<n} Δt ‖ℓ (k+1)‖²)`, a
discrete Gronwall inequality in its simplest form; `inv_one_sub_pow_le_exp` bounds the constant by
`exp (2 n Δt)`. -/
theorem norm_sq_add_sum_le_of_le {u : ℕ → K} {ℓ : ℕ → K →L[ℝ] ℝ} {n : ℕ} (hΔt : 0 < Δt)
    (hΔt' : Δt ≤ 1 / 2) (hpos : a.IsCoerciveWith 0)
    (h : ∀ k < n, IsThetaStep a 1 Δt (ℓ k) (ℓ (k + 1)) (u k) (u (k + 1))) :
    ‖u n‖ ^ 2 + 2 * Δt * ∑ k ∈ Finset.range n, a (u (k + 1)) (u (k + 1))
      ≤ (1 - Δt)⁻¹ ^ n * (‖u 0‖ ^ 2 + ∑ k ∈ Finset.range n, Δt * ‖ℓ (k + 1)‖ ^ 2) := by
  have hpos1 : 0 < 1 - Δt := by linarith
  have hinv : 1 ≤ (1 - Δt)⁻¹ := one_le_inv₀ hpos1 |>.2 (by linarith)
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih fun k hk => h k (Nat.lt_succ_of_lt hk)
    have hn := (h n (Nat.lt_succ_self n)).norm_sq_add_two_mul_le_of_le hΔt hΔt' hpos
    have hsum : 0 ≤ ∑ k ∈ Finset.range n, a (u (k + 1)) (u (k + 1)) :=
      Finset.sum_nonneg fun k _ => by simpa using hpos (u (k + 1))
    have hpown : 1 ≤ (1 - Δt)⁻¹ ^ n := one_le_pow₀ hinv
    have hℓn : 0 ≤ Δt * ‖ℓ (n + 1)‖ ^ 2 := by positivity
    calc ‖u (n + 1)‖ ^ 2 + 2 * Δt * ∑ k ∈ Finset.range (n + 1), a (u (k + 1)) (u (k + 1))
        = ‖u (n + 1)‖ ^ 2 + 2 * Δt * a (u (n + 1)) (u (n + 1))
          + 2 * Δt * ∑ k ∈ Finset.range n, a (u (k + 1)) (u (k + 1)) := by
          rw [Finset.sum_range_succ]; ring
      _ ≤ (1 - Δt)⁻¹ * (‖u n‖ ^ 2 + 2 * Δt * ∑ k ∈ Finset.range n, a (u (k + 1)) (u (k + 1))
          + Δt * ‖ℓ (n + 1)‖ ^ 2) := by
          nlinarith [mul_nonneg (mul_nonneg two_pos.le hΔt.le) hsum]
      _ ≤ (1 - Δt)⁻¹ * ((1 - Δt)⁻¹ ^ n * (‖u 0‖ ^ 2 + ∑ k ∈ Finset.range n, Δt * ‖ℓ (k + 1)‖ ^ 2)
          + Δt * ‖ℓ (n + 1)‖ ^ 2) := by gcongr
      _ ≤ (1 - Δt)⁻¹ ^ (n + 1)
          * (‖u 0‖ ^ 2 + ∑ k ∈ Finset.range (n + 1), Δt * ‖ℓ (k + 1)‖ ^ 2) := by
          rw [Finset.sum_range_succ, pow_succ' (1 - Δt)⁻¹ n, mul_assoc]
          gcongr
          nlinarith

/-- `(1 - Δt)⁻ⁿ ≤ exp (2 n Δt)` for `0 ≤ Δt ≤ ½`: the constant of `norm_sq_add_sum_le_of_le` is
bounded by `exp (2 t_n)` at the time `t_n = n Δt`. -/
theorem inv_one_sub_pow_le_exp {Δt : ℝ} (hΔt : 0 ≤ Δt) (hΔt' : Δt ≤ 1 / 2) (n : ℕ) :
    (1 - Δt)⁻¹ ^ n ≤ exp (2 * n * Δt) := by
  have hpos1 : 0 < 1 - Δt := by linarith
  have h1 : (1 - Δt)⁻¹ ≤ 1 + 2 * Δt := by
    rw [inv_le_iff_one_le_mul₀ hpos1]
    nlinarith
  have h2 : 1 + 2 * Δt ≤ exp (2 * Δt) := by
    have := add_one_le_exp (2 * Δt)
    linarith
  calc (1 - Δt)⁻¹ ^ n ≤ exp (2 * Δt) ^ n :=
        pow_le_pow_left₀ (inv_nonneg.2 hpos1.le) (h1.trans h2) n
    _ = exp (2 * n * Δt) := by rw [← exp_nat_mul]; ring_nf

end IsThetaStep

/-! ### Eigenpairs of a form -/

/-- **Eigenpairs of a bilinear form** relative to the inner product ([quarteroni2000numerical]
Definition 13.1, and its discrete form (13.22) on `V_h`): `(lam, w)` is an eigenpair of `a` when
`w ≠ 0` and `a w v = lam ⟪w, v⟫` for every `v`. -/
def IsFormEigenpair (a : SesqForm ℝ K) (lam : ℝ) (w : K) : Prop :=
  w ≠ 0 ∧ ∀ v, a w v = lam * ⟪w, v⟫

/-- On a Hilbert space the eigenpairs of a form are the eigenvectors of its operator
`SesqForm.toOperator a`, the `A` with `⟪A u, v⟫ = a u v`. -/
theorem isFormEigenpair_iff_hasEigenvector [CompleteSpace K] (a : SesqForm ℝ K) (lam : ℝ)
    (w : K) :
    IsFormEigenpair a lam w ↔
      Module.End.HasEigenvector (SesqForm.toOperator a : K →ₗ[ℝ] K) lam w := by
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, IsFormEigenpair, and_comm]
  refine and_congr_left fun _ => ?_
  simp only [ContinuousLinearMap.coe_coe]
  constructor
  · intro h
    exact ext_inner_right ℝ fun v => by
      rw [SesqForm.inner_toOperator, h v, real_inner_smul_left]
  · intro h v
    rw [← SesqForm.inner_toOperator, h, real_inner_smul_left]

namespace IsFormEigenpair

variable {a : SesqForm ℝ K} {lam : ℝ} {w : K}

/-- The eigenvalue is the Rayleigh quotient of the eigenvector: `a w w = lam ‖w‖²`. -/
theorem apply_self (h : IsFormEigenpair a lam w) : a w w = lam * ‖w‖ ^ 2 := by
  rw [h.2 w, real_inner_self_eq_norm_sq]

/-- A coercivity constant of the form bounds every eigenvalue from below: `c ‖v‖² ≤ a v v` gives
`c ≤ lam`. -/
theorem le_of_coercive {c : ℝ} (hcoer : a.IsCoerciveWith c) (h : IsFormEigenpair a lam w) :
    c ≤ lam := by
  have h1 := hcoer w
  rw [RCLike.re_to_real, h.apply_self] at h1
  exact le_of_mul_le_mul_right h1 (pow_pos (norm_pos_iff.2 h.1) 2)

/-- Every eigenvalue of a coercive form is positive ([quarteroni2000numerical] §13.3.1, "the
eigenvalues are positive"). -/
theorem pos_of_coercive {c : ℝ} (hc : 0 < c) (hcoer : a.IsCoerciveWith c)
    (h : IsFormEigenpair a lam w) : 0 < lam :=
  hc.trans_le (h.le_of_coercive hcoer)

/-- An upper bound of the quadratic form, `a v v ≤ lmax ‖v‖²`, bounds every eigenvalue from
above. -/
theorem le_of_le {lmax : ℝ} (hle : ∀ v, a v v ≤ lmax * ‖v‖ ^ 2) (h : IsFormEigenpair a lam w) :
    lam ≤ lmax := by
  have h1 := hle w
  rw [h.apply_self] at h1
  exact le_of_mul_le_mul_right h1 (pow_pos (norm_pos_iff.2 h.1) 2)

end IsFormEigenpair

/-- **The orthonormal eigenbasis of a symmetric form** ([quarteroni2000numerical] §13.3.1, the
eigenvectors of a symmetric coercive form on `V_h` form an `L²`-orthonormal basis): on a
finite-dimensional real inner product space, a symmetric form has eigenvalues
`lam : Fin (finrank ℝ K) → ℝ` and an orthonormal basis `b` of eigenvectors, `IsFormEigenpair a
(lam i) (b i)`. The spectral theorem `LinearMap.IsSymmetric.eigenvectorBasis` for the operator of
the form, symmetric by `SesqForm.isHermitian_iff_toOperator_isSymmetric`. -/
theorem exists_orthonormalBasis_isFormEigenpair [FiniteDimensional ℝ K] {a : SesqForm ℝ K}
    (ha : a.IsHermitian) :
    ∃ (lam : Fin (Module.finrank ℝ K) → ℝ) (b : OrthonormalBasis (Fin (Module.finrank ℝ K)) ℝ K),
      ∀ i, IsFormEigenpair a (lam i) (b i) := by
  have : CompleteSpace K := FiniteDimensional.complete ℝ K
  have hsymm := (SesqForm.isHermitian_iff_toOperator_isSymmetric a).1 ha
  refine ⟨hsymm.eigenvalues rfl, hsymm.eigenvectorBasis rfl, fun i => ?_⟩
  rw [isFormEigenpair_iff_hasEigenvector]
  exact hsymm.hasEigenvector_eigenvectorBasis rfl i

/-- **The generalized eigenvalue problem in coordinates** ([quarteroni2000numerical] (13.22),
`A_fe w = λ_h M w`): in a basis `φ`, `(lam, ∑ ξ_j φ_j)` is an eigenpair of `a` iff `ξ ≠ 0` and
`A ξ = lam M ξ` for the stiffness matrix `A = a.gramMatrix φ` and the mass matrix
`M = (innerSL ℝ).gramMatrix φ`. -/
theorem isFormEigenpair_iff_gramMatrix_mulVec {ι : Type*} [Fintype ι] (a : SesqForm ℝ K)
    (φ : Module.Basis ι ℝ K) (lam : ℝ) (ξ : ι → ℝ) :
    IsFormEigenpair a lam (∑ j, ξ j • φ j) ↔
      ξ ≠ 0 ∧ a.gramMatrix φ *ᵥ ξ = lam • SesqForm.gramMatrix (innerSL ℝ) φ *ᵥ ξ := by
  have hexp : ∀ (b : SesqForm ℝ K) (v : K), b (∑ j, ξ j • φ j) v = ∑ j, ξ j * b (φ j) v := by
    intro b v
    simp [map_sum, smul_eq_mul]
  have hmul : ∀ (b : SesqForm ℝ K) (i : ι), (b.gramMatrix φ *ᵥ ξ) i = b (∑ j, ξ j • φ j) (φ i) := by
    intro b i
    rw [hexp, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  refine and_congr ?_ ?_
  · rw [not_iff_not]
    constructor
    · intro h
      exact funext fun i => Fintype.linearIndependent_iff.1 φ.linearIndependent ξ h i
    · rintro rfl
      simp
  · constructor
    · intro h
      ext i
      rw [Pi.smul_apply, hmul, hmul, h (φ i), smul_eq_mul, innerSL_apply_apply]
    · intro h v
      have key : (a (∑ j, ξ j • φ j) : K →ₗ[ℝ] ℝ)
          = ((lam • innerSL ℝ (∑ j, ξ j • φ j) : K →L[ℝ] ℝ) : K →ₗ[ℝ] ℝ) := by
        refine φ.ext fun i => ?_
        have := congrFun h i
        rw [Pi.smul_apply, hmul, hmul, smul_eq_mul, innerSL_apply_apply] at this
        simp only [ContinuousLinearMap.coe_coe, smul_apply, innerSL_apply_apply, smul_eq_mul]
        exact this
      have := LinearMap.congr_fun key v
      simp only [ContinuousLinearMap.coe_coe, smul_apply, innerSL_apply_apply, smul_eq_mul] at this
      exact this

namespace IsThetaStep

variable {a : SesqForm ℝ K} {θ Δt : ℝ} {u u' : K}

/-- **The θ-method in an eigenvector direction** ([quarteroni2000numerical] §13.3.1, the recursion
`u_i^{k+1} = u_i^k [1 - (1-θ) λ_h^i Δt] / [1 + θ λ_h^i Δt]`): for a symmetric form, an eigenpair
`(lam, w)` and a source-free step with `Δt ≠ 0` and `1 + θ lam Δt ≠ 0`,
`⟪u', w⟫ = r_θ(lam Δt) ⟪u, w⟫` with `r_θ(x) = (1 - (1 - θ) x) / (1 + θ x)`. -/
theorem inner_eq_of_isFormEigenpair (h : IsThetaStep a θ Δt 0 0 u u') (ha : a.IsHermitian)
    {lam : ℝ} {w : K} (hw : IsFormEigenpair a lam w) (hΔt : Δt ≠ 0)
    (hden : 1 + θ * lam * Δt ≠ 0) :
    ⟪u', w⟫ = (1 - (1 - θ) * lam * Δt) / (1 + θ * lam * Δt) * ⟪u, w⟫ := by
  have h1 := h.inner_add_eq hΔt w
  have e : ∀ x, a x w = lam * ⟪x, w⟫ := fun x => by
    rw [ha x w, hw.2 x, real_inner_comm, RCLike.conj_to_real]
  simp only [e, zero_apply, mul_zero, add_zero] at h1
  rw [div_mul_eq_mul_div, eq_div_iff hden]
  linear_combination h1

/-- **Conditional stability of the θ-method, the sufficient condition** ([quarteroni2000numerical]
§13.3.1, `Δt ≤ 2 / ((1 - 2θ) λ_h^{N_h})`), without eigenvectors and on any real Hilbert space: for a
symmetric positive form with `a v v ≤ lmax ‖v‖²`, `Δt > 0` and `(1 - 2θ) lmax Δt ≤ 2`, the
source-free step is nonexpansive. By `energy_identity` it suffices that
`(½ - θ) ‖u' - u‖² ≤ Δt a(w, w)`; the step gives `u' - u = -Δt B w` for the operator `B` of the
form, and the operator Cauchy–Schwarz inequality `LinearMap.IsSymmetricBoundedBy.norm_apply_sq_le`
gives `‖B w‖² ≤ lmax ⟪B w, w⟫ = lmax a(w, w)`. The hypothesis `θ < ½` of the book is not needed:
for `θ ≥ ½` the condition holds trivially and so does the conclusion. This is the form the
matrix-level module reads in the `M`-inner product. -/
theorem norm_le_of_le_of_lt_half [CompleteSpace K] (h : IsThetaStep a θ Δt 0 0 u u')
    (ha : a.IsHermitian) (hpos : a.IsCoerciveWith 0) {lmax : ℝ}
    (hle : ∀ v, a v v ≤ lmax * ‖v‖ ^ 2) (hΔt : 0 < Δt)
    (hcfl : (1 - 2 * θ) * lmax * Δt ≤ 2) : ‖u'‖ ≤ ‖u‖ := by
  set B : K →ₗ[ℝ] K := (SesqForm.toOperator a : K →ₗ[ℝ] K) with hB
  have hBs : B.IsSymmetricBoundedBy 0 lmax := by
    refine ⟨(SesqForm.isHermitian_iff_toOperator_isSymmetric a).1 ha, fun x => ?_, fun x => ?_⟩
    · simpa [hB, SesqForm.inner_toOperator] using hpos x
    · simpa [hB, SesqForm.inner_toOperator] using hle x
  set w := θ • u' + (1 - θ) • u with hw
  have hstep : u' - u = -(Δt • B w) := by
    have : Δt⁻¹ • (u' - u) = -(B w) := by
      refine ext_inner_right ℝ fun v => ?_
      rw [inner_neg_left, hB, ContinuousLinearMap.coe_coe, SesqForm.inner_toOperator]
      have := h v
      simp only [zero_apply, mul_zero, add_zero] at this
      rw [← hw] at this
      linarith
    calc u' - u = Δt • (Δt⁻¹ • (u' - u)) := by rw [smul_smul, mul_inv_cancel₀ hΔt.ne', one_smul]
      _ = -(Δt • B w) := by rw [this, smul_neg]
  have hnorm : ‖u' - u‖ ^ 2 ≤ Δt ^ 2 * (lmax * a w w) := by
    rw [hstep, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hΔt, mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    have := hBs.norm_apply_sq_le le_rfl w
    rwa [RCLike.re_to_real, hB, ContinuousLinearMap.coe_coe, SesqForm.inner_toOperator] at this
  have hid := h.energy_identity hΔt.ne'
  rw [← hw] at hid
  have h0 : 0 ≤ a w w := by simpa using hpos w
  have hkey : (1 / 2 - θ) * ‖u' - u‖ ^ 2 ≤ Δt * a w w := by
    rcases le_or_gt (1 / 2) θ with hθ | hθ
    · nlinarith [mul_nonneg hΔt.le h0, sq_nonneg ‖u' - u‖]
    · calc (1 / 2 - θ) * ‖u' - u‖ ^ 2 ≤ (1 / 2 - θ) * (Δt ^ 2 * (lmax * a w w)) :=
            mul_le_mul_of_nonneg_left hnorm (by linarith)
        _ = Δt * a w w * ((1 - 2 * θ) * lmax * Δt / 2) := by ring
        _ ≤ Δt * a w w * 1 :=
            mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hΔt.le h0)
        _ = Δt * a w w := mul_one _
  have : ‖u'‖ ^ 2 ≤ ‖u‖ ^ 2 := by linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

/-- The θ-step of an eigenvector is its multiple by the amplification factor: for an eigenpair
`(lam, w)`, `r_θ(lam Δt) • w` is the source-free θ-step of `w`. -/
theorem smul_of_isFormEigenpair {lam : ℝ} {w : K} (hw : IsFormEigenpair a lam w)
    (hΔt : Δt ≠ 0) (hden : 1 + θ * lam * Δt ≠ 0) :
    IsThetaStep a θ Δt 0 0 w (((1 - (1 - θ) * lam * Δt) / (1 + θ * lam * Δt)) • w) := by
  intro v
  set r := (1 - (1 - θ) * lam * Δt) / (1 + θ * lam * Δt) with hr
  have hr' : r * (1 + θ * lam * Δt) = 1 - (1 - θ) * lam * Δt := by
    rw [hr, div_mul_cancel₀ _ hden]
  have e : θ • (r • w) + (1 - θ) • w = (θ * r + (1 - θ)) • w := by
    rw [smul_smul, add_smul]
  rw [e, map_smulₛₗ, smul_apply, hw.2, RCLike.conj_to_real, smul_eq_mul, real_inner_smul_left,
    inner_sub_left, real_inner_smul_left, zero_apply, mul_zero, mul_zero, add_zero]
  have : Δt⁻¹ * (r - 1) = -(lam * (θ * r + (1 - θ))) := by
    field_simp
    linear_combination hr'
  linear_combination ⟪w, v⟫ * this

/-- **Conditional stability of the θ-method, the sharp condition** ([quarteroni2000numerical]
§13.3.1): for a symmetric coercive form on a real Hilbert space, `θ ≥ 0`, `Δt > 0`, and `lmax`
the largest eigenvalue (an eigenvalue with `a v v ≤ lmax ‖v‖²` for all `v`), the source-free
θ-step is nonexpansive for every datum iff `(1 - 2θ) lmax Δt ≤ 2`. Necessity: the eigenvector `w₀`
is multiplied by `r_θ(lmax Δt)`, whose modulus is at most `1` iff the condition holds;
sufficiency is `norm_le_of_le_of_lt_half`. For `θ ≥ ½` both sides hold. -/
theorem forall_norm_le_iff_of_lt_half [CompleteSpace K] (ha : a.IsHermitian) {c : ℝ}
    (hc : 0 < c) (hcoer : a.IsCoerciveWith c) (hθ0 : 0 ≤ θ) (hΔt : 0 < Δt)
    {lmax : ℝ} {w₀ : K} (hw₀ : IsFormEigenpair a lmax w₀)
    (hle : ∀ v, a v v ≤ lmax * ‖v‖ ^ 2) :
    (∀ u u', IsThetaStep a θ Δt 0 0 u u' → ‖u'‖ ≤ ‖u‖) ↔ (1 - 2 * θ) * lmax * Δt ≤ 2 := by
  have hlmax : 0 < lmax := hw₀.pos_of_coercive hc hcoer
  have hden : 0 < 1 + θ * lmax * Δt := by positivity
  constructor
  · intro hstab
    have h := hstab w₀ _ (smul_of_isFormEigenpair hw₀ hΔt.ne' hden.ne')
    rw [norm_smul, Real.norm_eq_abs] at h
    have hr : |(1 - (1 - θ) * lmax * Δt) / (1 + θ * lmax * Δt)| ≤ 1 :=
      le_of_mul_le_mul_right (by simpa using h) (norm_pos_iff.2 hw₀.1)
    rw [abs_div, abs_of_pos hden, div_le_one hden, abs_le] at hr
    linarith [hr.1]
  · intro hcfl u u' h
    exact h.norm_le_of_le_of_lt_half ha (SesqForm.IsCoerciveWith.mono a hcoer hc.le) hle hΔt hcfl

end IsThetaStep

/-! ### The transport and upwind discontinuous Galerkin forms -/

section Transport

open Polynomial BrokenPolynomial

variable {n : ℕ} {x : Fin (n + 1) → ℝ} {r : ℕ} [hx : Fact (StrictMono x)] {a a₀ : ℝ → ℝ}

/-- A panel `[x i, x (i+1)]` of a monotone partition lies in `[x 0, x n]`. -/
theorem uIcc_panel_subset (i : Fin n) :
    [[x i.castSucc, x i.succ]] ⊆ [[x 0, x (Fin.last n)]] := by
  have hm : Monotone x := hx.out.monotone
  rw [uIcc_of_le (hm (Fin.castSucc_lt_succ (i := i)).le), uIcc_of_le (hm (Fin.zero_le _))]
  exact Icc_subset_Icc (hm (Fin.zero_le _)) (hm (Fin.le_last _))

/-- The integrand `(a p' + a₀ p) q` of the transport form is integrable on every panel when `a`
and `a₀` are integrable on `[x 0, x n]` (polynomials are continuous). -/
theorem intervalIntegrable_transport (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : IntervalIntegrable a₀ volume (x 0) (x (Fin.last n))) (p q : ℝ[X]) (i : Fin n) :
    IntervalIntegrable (fun s => (a s * p.derivative.eval s + a₀ s * p.eval s) * q.eval s) volume
      (x i.castSucc) (x i.succ) :=
  (((ha.mono_set (uIcc_panel_subset i)).mul_continuousOn p.derivative.continuous.continuousOn).add
    ((ha₀.mono_set (uIcc_panel_subset i)).mul_continuousOn
      p.continuous.continuousOn)).mul_continuousOn q.continuous.continuousOn

variable (x r) in
/-- The transport bilinear map `(u, v) ↦ ∑ᵢ ∫_{xᵢ}^{xᵢ₊₁} (a uᵢ' + a₀ uᵢ) vᵢ` on the broken
polynomial space, for coefficients `a`, `a₀` integrable on `[x 0, x n]` (the integrability is what
makes it bilinear). -/
def transportBilin (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : IntervalIntegrable a₀ volume (x 0) (x (Fin.last n))) :
    BrokenPolynomial x r →ₗ[ℝ] BrokenPolynomial x r →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v => ∑ i, ∫ s in x i.castSucc..x i.succ,
      (a s * (u i).derivative.eval s + a₀ s * (u i).eval s) * (v i).eval s)
    (fun u u' v => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← integral_add (intervalIntegrable_transport ha ha₀ _ _ i)
        (intervalIntegrable_transport ha ha₀ _ _ i)]
      exact integral_congr fun s _ => by
        simp only [BrokenPolynomial.add_apply, derivative_add, eval_add]; ring)
    (fun c u v => by
      rw [smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← integral_const_mul]
      exact integral_congr fun s _ => by
        simp only [BrokenPolynomial.smul_apply, derivative_smul, eval_smul, smul_eq_mul]; ring)
    (fun u v v' => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← integral_add (intervalIntegrable_transport ha ha₀ _ _ i)
        (intervalIntegrable_transport ha ha₀ _ _ i)]
      exact integral_congr fun s _ => by simp only [BrokenPolynomial.add_apply, eval_add]; ring)
    (fun c u v => by
      rw [smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← integral_const_mul]
      exact integral_congr fun s _ => by
        simp only [BrokenPolynomial.smul_apply, eval_smul, smul_eq_mul]; ring)

variable (x r) in
/-- **The transport form** `(u, v) ↦ ∑ᵢ ∫_{xᵢ}^{xᵢ₊₁} (a uᵢ' + a₀ uᵢ) vᵢ` on the broken polynomial
space `BrokenPolynomial x r` of a strictly increasing partition, as a bounded form for the `L²`
inner product ([quarteroni2000numerical] §13.10.1, the form of the continuous Galerkin
semi-discretization (13.65) of `u_t + a u_x + a₀ u = f`). The coefficient `a₀` is taken at a fixed
time; a time-dependent reaction coefficient gives a family `t ↦ transportForm x r ha (ha₀ t)`. -/
def transportForm (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : IntervalIntegrable a₀ volume (x 0) (x (Fin.last n))) :
    SesqForm ℝ (BrokenPolynomial x r) :=
  SesqForm.ofBilin (transportBilin x r ha ha₀)

/-- The transport form is the sum of the panel integrals `∫ (a u' + a₀ u) v`. -/
theorem transportForm_apply (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : IntervalIntegrable a₀ volume (x 0) (x (Fin.last n))) (u v : BrokenPolynomial x r) :
    transportForm x r ha ha₀ u v = ∑ i, ∫ s in x i.castSucc..x i.succ,
      (a s * (u i).derivative.eval s + a₀ s * (u i).eval s) * (v i).eval s := rfl

variable (x r) in
/-- **The upwind discontinuous Galerkin form** ([quarteroni2000numerical] (13.68)):
`(u, v) ↦ ∑ᵢ ∫_{xᵢ}^{xᵢ₊₁} (a uᵢ' + a₀ uᵢ) vᵢ + ∑ᵢ a(xᵢ) [u]ᵢ v⁺(xᵢ)` on the broken polynomial
space, with the jump `[u]ᵢ = u⁺(xᵢ) - u⁻(xᵢ)` and the inflow convention `u⁻(x₀) = 0`
(`BrokenPolynomial.jump`); the inflow datum `φ(t)` of the book enters the right-hand side as
`a(x₀) φ(t) v⁺(x₀)`. -/
def dgUpwindForm (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : IntervalIntegrable a₀ volume (x 0) (x (Fin.last n))) :
    SesqForm ℝ (BrokenPolynomial x r) :=
  SesqForm.ofBilin (transportBilin x r ha ha₀
    + ∑ i : Fin n, a (x i.castSucc) • (jumpₗ x r i).smulRight (traceRightₗ x r i))

/-- The upwind form is the transport form plus the jump terms `∑ᵢ a(xᵢ) [u]ᵢ v⁺(xᵢ)`. -/
theorem dgUpwindForm_apply (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : IntervalIntegrable a₀ volume (x 0) (x (Fin.last n))) (u v : BrokenPolynomial x r) :
    dgUpwindForm x r ha ha₀ u v
      = transportForm x r ha ha₀ u v
        + ∑ i : Fin n, a (x i.castSucc) * jump u i * traceRight v i := by
  simp only [dgUpwindForm, transportForm, SesqForm.ofBilin_apply, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, jumpₗ_apply,
    traceRightₗ_apply, smul_eq_mul]
  simp only [mul_assoc]

/-- **The energy identity of the upwind discontinuous Galerkin form** ([quarteroni2000numerical]
§13.10.1, the computation behind (13.69)): for `a` differentiable on `[x 0, x n]` with continuous
derivative,
`b(v, v) = ½ a(xₙ) v⁻(xₙ)² + ½ ∑ᵢ a(xᵢ) [v]ᵢ² + ∑ᵢ ∫_{xᵢ}^{xᵢ₊₁} (a₀ - a'/2) vᵢ²`. Panel
integration by parts `∫ a v v' = ½ [a v²] - ½ ∫ a' v²`
(`BrokenPolynomial.sum_integral_mul_deriv_mul_eq`), then at each node
`½ a v⁻² - ½ a v⁺² + a [v] v⁺ = ½ a [v]²`. With `a₀ - a'/2 ≥ 0` the form is positive, and the
identity is the hypothesis of the dissipative energy estimate with `Q` the boundary and jump
terms. -/
theorem dgUpwindForm_apply_self (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : IntervalIntegrable a₀ volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) (v : BrokenPolynomial x r) :
    dgUpwindForm x r ha ha₀ v v
      = a (x (Fin.last n)) * traceLeft v (Fin.last n) ^ 2 / 2
        + ∑ i : Fin n, a (x i.castSucc) * jump v i ^ 2 / 2
        + ∑ i, ∫ s in x i.castSucc..x i.succ, (a₀ s - deriv a s / 2) * (v i).eval s ^ 2 := by
  have hm : Monotone x := hx.out.monotone
  have hIcc : ∀ i : Fin n, [[x i.castSucc, x i.succ]] ⊆ Icc (x 0) (x (Fin.last n)) := fun i =>
    (uIcc_panel_subset i).trans (uIcc_of_le (hm (Fin.zero_le _))).le
  -- the panel integrals split into the `a v v'` part and the `a₀ v²` part
  have hsplit : ∀ i : Fin n, ∫ s in x i.castSucc..x i.succ,
      (a s * (v i).derivative.eval s + a₀ s * (v i).eval s) * (v i).eval s
      = (∫ s in x i.castSucc..x i.succ, a s * (v i).eval s * (v i).derivative.eval s)
        + ∫ s in x i.castSucc..x i.succ, a₀ s * (v i).eval s ^ 2 := by
    intro i
    rw [← integral_add]
    · exact integral_congr fun s _ => by ring
    · exact ((ha.mono_set (uIcc_panel_subset i)).mul_continuousOn
        (v i).continuous.continuousOn).mul_continuousOn (v i).derivative.continuous.continuousOn
    · exact (ha₀.mono_set (uIcc_panel_subset i)).mul_continuousOn
        ((v i).continuous.pow 2).continuousOn
  have hibp := sum_integral_mul_deriv_mul_eq hm hd hd' v
  have hsub : ∀ i : Fin n, ∫ s in x i.castSucc..x i.succ, (a₀ s - deriv a s / 2) * (v i).eval s ^ 2
      = (∫ s in x i.castSucc..x i.succ, a₀ s * (v i).eval s ^ 2)
        - (1 / 2) * ∫ s in x i.castSucc..x i.succ, deriv a s * (v i).eval s ^ 2 := by
    intro i
    rw [← integral_const_mul, ← integral_sub]
    · exact integral_congr fun s _ => by ring
    · exact (ha₀.mono_set (uIcc_panel_subset i)).mul_continuousOn
        ((v i).continuous.pow 2).continuousOn
    · exact (((hd'.mono (hIcc i)).intervalIntegrable).mul_continuousOn
        ((v i).continuous.pow 2).continuousOn).const_mul _
  rw [dgUpwindForm_apply, transportForm_apply]
  simp only [hsplit, hsub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hibp]
  have hnode : ∑ i : Fin n, a (x i.castSucc) * jump v i ^ 2 / 2
      = ∑ i : Fin n, a (x i.castSucc) * jump v i * traceRight v i
        - ∑ i : Fin n,
          a (x i.castSucc) * (traceRight v i ^ 2 - traceLeft v i.castSucc ^ 2) / 2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [jump_apply]; ring
  rw [hnode]
  ring

/-- **The energy identity of the transport form on the continuous subspace**
([quarteroni2000numerical] §13.10.1, the identity behind (13.66)): for `v` with no interior
jumps, `∑ᵢ ∫ (a v' + a₀ v) v = ½ a(xₙ) v⁻(xₙ)² - ½ a(x₀) v⁺(x₀)² + ∑ᵢ ∫ (a₀ - a'/2) vᵢ²`. From
`dgUpwindForm_apply_self`: the jump terms vanish except at `x₀`, where `[v]₀ = v⁺(x₀)`. -/
theorem transportForm_apply_self_of_continuous
    (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : IntervalIntegrable a₀ volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) (hn : 0 < n)
    {v : BrokenPolynomial x r} (hv : v ∈ continuous x r) :
    transportForm x r ha ha₀ v v
      = a (x (Fin.last n)) * traceLeft v (Fin.last n) ^ 2 / 2
        - a (x 0) * traceRight v ⟨0, hn⟩ ^ 2 / 2
        + ∑ i, ∫ s in x i.castSucc..x i.succ, (a₀ s - deriv a s / 2) * (v i).eval s ^ 2 := by
  have h := dgUpwindForm_apply_self ha ha₀ hd hd' v
  rw [dgUpwindForm_apply] at h
  have hjump : ∀ i : Fin n, i ≠ ⟨0, hn⟩ → jump v i = 0 := fun i hi =>
    hv i (Nat.pos_of_ne_zero fun h0 => hi (Fin.ext h0))
  have h1 : ∑ i : Fin n, a (x i.castSucc) * jump v i * traceRight v i
      = a (x 0) * traceRight v ⟨0, hn⟩ ^ 2 := by
    rw [Finset.sum_eq_single ⟨0, hn⟩ (fun i _ hi => by rw [hjump i hi, mul_zero, zero_mul])
      (fun h => absurd (Finset.mem_univ _) h), jump_zero]
    simp only [sq, mul_assoc]
    rfl
  have h2 : ∑ i : Fin n, a (x i.castSucc) * jump v i ^ 2 / 2
      = a (x 0) * traceRight v ⟨0, hn⟩ ^ 2 / 2 := by
    rw [Finset.sum_eq_single ⟨0, hn⟩ (fun i _ hi => by rw [hjump i hi]; ring)
      (fun h => absurd (Finset.mem_univ _) h), jump_zero]
    rfl
  rw [h1] at h
  rw [h2] at h
  linarith

end Transport

end Variational

end

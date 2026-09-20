import Numlib.Analysis.PDE.Transport
import Numlib.Variational.EllipticInterval
import Numlib.Variational.Evolution
import Numlib.Variational.SpaceTimeGalerkin

/-!
# Quarteroni–Sacco–Saleri §13.10: finite elements for the transport equation

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §13.10 and its Exercises 9 and 10.

The problem is the scalar hyperbolic initial boundary value problem (13.64)
`u_t + a u_x + a₀ u = f` on `Q_T = (α, β) × (0, T)` with `a = a(x) > 0`, so that `x = α` is the
inflow boundary and the datum `φ` is prescribed there; its classical solutions are
`Transport.IsInflowSolution` (`equation_13_64`).

Both semi-discretizations of §13.10.1 live on the broken polynomial space
`W_h = Y_h^r = BrokenPolynomial x r` of the partition `α = x 0 < ⋯ < x n = β`
(`Numlib/Approximation/BrokenPolynomial`), carrying the `L²(α, β)` inner product:

* the **continuous** Galerkin method (13.65) uses `V_h = X_h^r`, the subspace
  `BrokenPolynomial.continuous x r` of zero interior jumps, and tests against
  `V_h^{in} = {v ∈ V_h | v(α) = 0}` (`inflowSpace`), with the form
  `b_t(u, v) = ∑_j ∫_{I_j} (a u' + a₀(·, t) u) v` (`transportForm`);
* the **discontinuous** Galerkin method (13.68) uses all of `W_h` with the upwind flux form
  `b^{DG}_t(u, v) = b_t(u, v) + ∑_j a(x_j) [u]_j v⁺(x_j)` (`Variational.dgUpwindForm`), the
  inflow value `φ` being moved to the right-hand side as the source `a(α) φ(t) v⁺(α)`; the jumps
  are `BrokenPolynomial.jump`, with the convention `u⁻(x 0) = 0`.

Both are `Variational.IsSemidiscreteGalerkin` (`equation_13_65`, `equation_13_68`), and every
estimate of the section is the energy identity of the respective form fed into one of the
abstract estimates of `Numlib/Variational/Evolution`:

`b^{DG}_t(v, v) = ½ a(β) v⁻(β)² + ½ ∑_j a(x_j) [v]_j² + ∫_α^β (a₀(·, t) - a'/2) v²`

(`dgUpwindForm_apply_self`), of which the continuous identity `transportForm_apply_self` is the
special case of zero jumps. Under `0 < μ₀ ≤ a₀ - a'/2` the identity gives the coercivity
inequalities `le_transportForm_restrict` and `le_dgUpwindForm`, and then (13.66), (13.67)
(= Exercise 9), (13.69) and Exercise 10 follow. §13.10.2 discretizes (13.65) in time by backward
Euler (13.70), which is unconditionally stable (`equation_13_70_stability`, `equation_13_70_sum`,
`equation_13_70_norm_le`).

The two convergence rates quoted in §13.10.1 from [QV94] — `O(h^r)` for `cG(r)` and
`O(h^{r+1/2})` for `dG(r)` — are `cG_convergence` and `dG_convergence`, restatements of
`Variational.cG_error_le` and `Variational.dG_error_sq_le` (`Numlib/Variational/SpaceTimeGalerkin`)
with the regularity of the exact solution as hypotheses (`u(·, t) ∈ H^{r+1}(α, β)` uniformly in
`t`, and for `cG` also `∂ₜu(·, t)`) and explicit constants in place of the `O(·)`.

## Readings and errata

* In (13.66), (13.67) and the display after (13.70) the boundary term is printed
  `a(β) ∫₀ᵗ u_h²(τ) dτ`, resp. `a(β)(u_h^{j+1}(β))²` summed over `j = 1..m`; read `u_h(β, τ)²`
  and `u_h^j(β)²`.
* The display after (13.70) prints `a(β)(u_h^{n+1}(β))²`; the derivation the book describes
  (test (13.70) with `v_h = u_h^{n+1}` and use the energy identity, whose outflow term carries a
  factor `½`) gives `½ a(β)(u_h^{n+1}(β))²`, which is what `equation_13_70_stability` states. The
  printed inequality is strictly stronger and does not follow. The summed display likewise drops
  `μ₀` from `2Δt ∑_j μ₀ ‖u_h^j‖²`.
* "Conservation of the energy when `f` and `a₀` vanish" needs `a' ≤ 0` as well (automatic for a
  constant convective term); `equation_13_66_conservation` asks for `0 ≤ a₀ - a'/2`.
* (13.69) is stated by the book with an unspecified constant `C` and the jump sum
  `∑_{j=0}^{n-1}`; `equation_13_69` gives explicit constants, with the inflow contribution
  appearing as `a(α)(u_h⁺(α) - φ)²` — the book's own `[u_h]_0`, since `U_h^-(x_0, t) = φ(t)` —
  and the outflow term `a(β) u_h⁻(β)²` surviving in addition.

## Conventions

The partition is `x : Fin (n + 1) → ℝ` with `[Fact (StrictMono x)]`, so `α = x 0` and
`β = x (Fin.last n)`; `n ≥ 1` is the hypothesis `hn : 0 < n`. The coefficients are functions
`a : ℝ → ℝ` and `a₀ : ℝ → ℝ → ℝ` written as in the book, `a₀ s t` for `a₀(x, t)`, with interval
integrability on `[α, β]` as the hypothesis that makes the forms bilinear, and `a` differentiable
with continuous derivative where the integration by parts needs it. The source `f(t)` is taken in
the discrete space, so that `‖f t‖` is its `L²(α, β)` norm; a general `f(t) ∈ L²(α, β)` enters
(13.65) and (13.68) only through its `L²` projection, whose norm is at most `‖f(t)‖_{L²}`, so the
estimates below are the book's.
-/

open Set MeasureTheory Polynomial Real
open scoped RealInnerProductSpace Interval

noncomputable section

namespace QuarteroniSaccoSaleri.Chapter13

section Transport

variable {n : ℕ} {x : Fin (n + 1) → ℝ} {r : ℕ} [hx : Fact (StrictMono x)] {a : ℝ → ℝ}
  {a₀ : ℝ → ℝ → ℝ}

/-! ### The transport problem (13.64) -/

/-- **The transport initial boundary value problem** ([quarteroni2000numerical] (13.64)) on
`Q_T = (α, β) × (0, T)`: `u_t + a u_x + a₀ u = f` with `a = a(x)`, `a₀ = a₀(x, t)`, `f = f(x, t)`,
the inflow datum `u(α, t) = φ(t)` and the initial datum `u(x, 0) = u₀(x)`. The book assumes
`a(x) > 0` on `[α, β]`, which is what makes `x = α` the inflow boundary; positivity is not part
of the definition but is a hypothesis of the results that need it. -/
def equation_13_64 (a : ℝ → ℝ) (a₀ f : ℝ → ℝ → ℝ) (φ u₀ : ℝ → ℝ) (α β T : ℝ)
    (u : ℝ → ℝ → ℝ) : Prop :=
  Transport.IsInflowSolution a a₀ f φ u₀ α β T u

omit hx in
/-- (13.64) spelled out: the partial derivatives of `u` on the strip `[α, β] × [0, T]` exist, the
equation holds there, and the two side conditions hold. -/
theorem equation_13_64_def (a : ℝ → ℝ) (a₀ f : ℝ → ℝ → ℝ) (φ u₀ : ℝ → ℝ) (α β T : ℝ)
    (u : ℝ → ℝ → ℝ) :
    equation_13_64 a a₀ f φ u₀ α β T u ↔
      ∃ ux ut : ℝ → ℝ → ℝ, Transport.HasPartialsOn (Icc α β ×ˢ Icc 0 T) u ux ut ∧
        (∀ y ∈ Icc α β, ∀ t ∈ Icc (0 : ℝ) T,
          ut y t + a y * ux y t + a₀ y t * u y t = f y t) ∧
        (∀ t ∈ Icc (0 : ℝ) T, u α t = φ t) ∧ ∀ y ∈ Icc α β, u y 0 = u₀ y :=
  Iff.rfl

/-! ### The finite element spaces and the transport form -/

/-- **The test space `V_h^{in}`** ([quarteroni2000numerical] §13.10.1): the continuous piecewise
polynomials of degree at most `r` that vanish at the inflow end `α = x 0`, as a subspace of the
broken polynomial space. `V_h = X_h^r` itself is `BrokenPolynomial.continuous x r`. -/
def inflowSpace (x : Fin (n + 1) → ℝ) (r : ℕ) (hn : 0 < n) :
    Submodule ℝ (BrokenPolynomial x r) :=
  BrokenPolynomial.continuous x r ⊓ LinearMap.ker (BrokenPolynomial.traceRightₗ x r ⟨0, hn⟩)

omit hx in
/-- Membership of `V_h^{in}`: continuity, and a vanishing value at the inflow end. -/
theorem mem_inflowSpace_iff {hn : 0 < n} {v : BrokenPolynomial x r} :
    v ∈ inflowSpace x r hn ↔
      v ∈ BrokenPolynomial.continuous x r ∧ BrokenPolynomial.traceRight v ⟨0, hn⟩ = 0 :=
  Iff.rfl

variable (x r) in
/-- **The transport form** ([quarteroni2000numerical] §13.10.1, the spatial part of (13.65)):
`b_t(u, v) = ∑_j ∫_{I_j} (a u' + a₀(·, t) u) v` on the broken polynomial space of the partition
`α = x 0 < ⋯ < x n = β`, one bounded form for each time `t`. -/
def transportForm (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n))) (t : ℝ) :
    SesqForm ℝ (BrokenPolynomial x r) :=
  Variational.transportForm x r ha (ha₀ t)

/-- The transport form is the sum of the panel integrals `∫ (a u' + a₀ u) v`. -/
theorem transportForm_apply (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n))) (t : ℝ)
    (u v : BrokenPolynomial x r) :
    transportForm x r ha ha₀ t u v = ∑ i, ∫ s in x i.castSucc..x i.succ,
      (a s * (u i).derivative.eval s + a₀ s t * (u i).eval s) * (v i).eval s := rfl

/-! ### The continuous Galerkin semi-discretization (13.65) -/

/-- **The continuous Galerkin semi-discretization** ([quarteroni2000numerical] (13.65)) with a
vanishing inflow datum `φ = 0`, so that `u_h(t) ∈ V_h^{in}`: find `u_h : ℝ → V_h^{in}` with
`⟪∂ₜ u_h(t), v_h⟫_{L²} + b_t(u_h(t), v_h) = ⟪f(t), v_h⟫_{L²}` for every `v_h ∈ V_h^{in}` and
`t ∈ [0, T]`, and `u_h(0) = u_{0,h}`. The inhomogeneous case `u_h(α, t) = φ_h(t)` is the same
equation on the affine space `φ_h(t) + V_h^{in}` and is not stated separately. -/
def equation_13_65 (hn : 0 < n) (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (f : ℝ → BrokenPolynomial x r) (u₀h : inflowSpace x r hn) (T : ℝ)
    (uh : ℝ → inflowSpace x r hn) : Prop :=
  Variational.IsSemidiscreteGalerkin
    (fun t => (transportForm x r ha ha₀ t).restrict (inflowSpace x r hn))
    (fun t => (innerSL ℝ (f t)).comp (inflowSpace x r hn).subtypeL) u₀h T uh

/-- **The energy identity of the transport form on `V_h`** ([quarteroni2000numerical] §13.10.1,
the computation behind (13.66)): for a continuous piecewise polynomial `v`,
`b_t(v, v) = ½ a(β) v(β)² - ½ a(α) v(α)² + ∫_α^β (a₀(·, t) - a'/2) v²`. Panel integration by
parts, the boundary terms telescoping because `v` has no interior jumps. -/
theorem transportForm_apply_self (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) (hn : 0 < n) (t : ℝ)
    {v : BrokenPolynomial x r} (hv : v ∈ BrokenPolynomial.continuous x r) :
    transportForm x r ha ha₀ t v v
      = a (x (Fin.last n)) * BrokenPolynomial.traceLeft v (Fin.last n) ^ 2 / 2
        - a (x 0) * BrokenPolynomial.traceRight v ⟨0, hn⟩ ^ 2 / 2
        + ∑ i, ∫ s in x i.castSucc..x i.succ, (a₀ s t - deriv a s / 2) * (v i).eval s ^ 2 :=
  Variational.transportForm_apply_self_of_continuous ha (ha₀ t) hd hd' hn hv

omit hx in
/-- The coefficient `a₀(·, t) - a'/2` of the energy identity is interval integrable on `[α, β]`. -/
private theorem intervalIntegrable_reaction
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) (hle : x 0 ≤ x (Fin.last n))
    (t : ℝ) :
    IntervalIntegrable (fun s => a₀ s t - deriv a s / 2) volume (x 0) (x (Fin.last n)) :=
  (ha₀ t).sub
    (((by rwa [uIcc_of_le hle] : ContinuousOn (deriv a) [[x 0, x (Fin.last n)]]).intervalIntegrable
      ).div_const 2)

/-- **The dissipativity of the transport form on `V_h^{in}`** ([quarteroni2000numerical]
§13.10.1, the inequality behind (13.66) and (13.67)): if `c ≤ a₀(·, t) - a'/2` on `[α, β]` then
`c ‖v‖²_{L²} + ½ a(β) v(β)² ≤ b_t(v, v)` for every `v ∈ V_h^{in}`, the inflow term of
`transportForm_apply_self` vanishing. Taking `c = μ₀ > 0` gives (13.66) and `c = -μ*` gives
(13.67). -/
theorem le_transportForm_restrict (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) (hn : 0 < n) {t c : ℝ}
    (hc : ∀ s ∈ Icc (x 0) (x (Fin.last n)), c ≤ a₀ s t - deriv a s / 2)
    (v : inflowSpace x r hn) :
    c * ‖v‖ ^ 2
        + a (x (Fin.last n))
          * BrokenPolynomial.traceLeft (v : BrokenPolynomial x r) (Fin.last n) ^ 2 / 2
      ≤ (transportForm x r ha ha₀ t).restrict (inflowSpace x r hn) v v := by
  have hle : x 0 ≤ x (Fin.last n) := hx.out.monotone (Fin.zero_le _)
  have h0 : BrokenPolynomial.traceRight (v : BrokenPolynomial x r) ⟨0, hn⟩ = 0 := v.2.2
  have key := transportForm_apply_self ha ha₀ hd hd' hn t v.2.1
  have hlow := BrokenPolynomial.mul_norm_sq_le_sum_integral
    (intervalIntegrable_reaction ha₀ hd' hle t) hc (v : BrokenPolynomial x r)
  rw [SesqForm.restrict_apply, key, h0, ← Submodule.norm_coe]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
    sub_zero]
  linarith

/-- The outflow functional `t ↦ a(β) u_h(β, t)²` is continuous along a continuous curve. -/
private theorem continuousOn_outflow {hn : 0 < n} {T : ℝ} {uh : ℝ → inflowSpace x r hn}
    (h : ContinuousOn uh (Icc 0 T)) :
    ContinuousOn (fun s => a (x (Fin.last n))
      * BrokenPolynomial.traceLeft (uh s : BrokenPolynomial x r) (Fin.last n) ^ 2) (Icc 0 T) := by
  have hc : Continuous fun v : inflowSpace x r hn =>
      BrokenPolynomial.traceLeft (v : BrokenPolynomial x r) (Fin.last n) :=
    (BrokenPolynomial.continuous_traceLeft (Fin.last n)).comp continuous_subtype_val
  exact continuousOn_const.mul ((hc.comp_continuousOn h).pow 2)

/-- The `L²` source functional `v ↦ ⟪g, v⟫` of `V_h^{in}` has norm at most `‖g‖_{L²}`. -/
private theorem norm_source_le {hn : 0 < n} (g : BrokenPolynomial x r) :
    ‖(innerSL ℝ g).comp (inflowSpace x r hn).subtypeL‖ ≤ ‖g‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => by
    simpa using abs_real_inner_le_norm g (v : BrokenPolynomial x r)

/-- **(13.66)** ([quarteroni2000numerical] (13.66)): under `0 < μ₀ ≤ a₀(x, t) - a'(x)/2` on
`[α, β] × [0, T]`, the solution of (13.65) with `φ = 0` satisfies, for `t ∈ [0, T]`,
`‖u_h(t)‖²_{L²} + ∫₀ᵗ (μ₀ ‖u_h(τ)‖²_{L²} + a(β) u_h(β, τ)²) dτ
  ≤ ‖u_{0,h}‖²_{L²} + μ₀⁻¹ ∫₀ᵗ ‖f(τ)‖²_{L²} dτ`.
`Variational.IsSemidiscreteGalerkin.norm_sq_add_integral_le` with the dissipativity
`le_transportForm_restrict` and `Q_t(v) = a(β) v(β)²`. -/
theorem equation_13_66 (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) {hn : 0 < n}
    {f : ℝ → BrokenPolynomial x r} {u₀h : inflowSpace x r hn} {T : ℝ}
    {uh : ℝ → inflowSpace x r hn} (h : equation_13_65 hn ha ha₀ f u₀h T uh)
    {μ₀ : ℝ} (hμ : 0 < μ₀)
    (hμ₀ : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc (x 0) (x (Fin.last n)), μ₀ ≤ a₀ s t - deriv a s / 2)
    (hf : ContinuousOn (fun s => ‖f s‖) (Icc 0 T)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖uh t‖ ^ 2 + ∫ s in (0 : ℝ)..t, (μ₀ * ‖uh s‖ ^ 2 + a (x (Fin.last n))
          * BrokenPolynomial.traceLeft (uh s : BrokenPolynomial x r) (Fin.last n) ^ 2)
      ≤ ‖u₀h‖ ^ 2 + μ₀⁻¹ * ∫ s in (0 : ℝ)..t, ‖f s‖ ^ 2 :=
  h.norm_sq_add_integral_le (Q := fun _ v => a (x (Fin.last n))
      * BrokenPolynomial.traceLeft (v : BrokenPolynomial x r) (Fin.last n) ^ 2) hμ
    (continuousOn_outflow h.continuousOn)
    (fun s hs v => le_transportForm_restrict ha ha₀ hd hd' hn (hμ₀ s hs) v) hf
    (fun s _ => norm_source_le (f s)) ht

/-- **Conservation of the energy** ([quarteroni2000numerical] §13.10.1, the display after
(13.66)): if `f = 0` and `0 ≤ a₀ - a'/2` — the book says `f = a₀ = 0`, and then `a' ≤ 0` is what
the identity needs, automatic for a constant convective term — then `t ↦ ‖u_h(t)‖_{L²}` is
antitone on `[0, T]`. -/
theorem equation_13_66_conservation (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) {hn : 0 < n}
    {u₀h : inflowSpace x r hn} {T : ℝ} {uh : ℝ → inflowSpace x r hn}
    (h : equation_13_65 hn ha ha₀ 0 u₀h T uh) (hβ : 0 ≤ a (x (Fin.last n)))
    (hpos : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc (x 0) (x (Fin.last n)), 0 ≤ a₀ s t - deriv a s / 2) :
    AntitoneOn (fun t => ‖uh t‖) (Icc 0 T) := by
  refine h.norm_le_of_nonneg (fun t => by simp) fun t htmem v => ?_
  have := le_transportForm_restrict ha ha₀ hd hd' hn (hpos t htmem) v
  simp only [RCLike.re_to_real, zero_mul]
  nlinarith [sq_nonneg (BrokenPolynomial.traceLeft (v : BrokenPolynomial x r) (Fin.last n))]

/-- Conservation of the energy as the book prints it ([quarteroni2000numerical] §13.10.1):
`‖u_h(t)‖_{L²} ≤ ‖u_{0,h}‖_{L²}` for every `t ∈ [0, T]`. -/
theorem equation_13_66_conservation_le (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) {hn : 0 < n}
    {u₀h : inflowSpace x r hn} {T : ℝ} {uh : ℝ → inflowSpace x r hn}
    (h : equation_13_65 hn ha ha₀ 0 u₀h T uh) (hβ : 0 ≤ a (x (Fin.last n)))
    (hpos : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc (x 0) (x (Fin.last n)), 0 ≤ a₀ s t - deriv a s / 2)
    {t : ℝ} (ht : t ∈ Icc 0 T) : ‖uh t‖ ≤ ‖u₀h‖ := by
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_refl 0, ht.1.trans ht.2⟩
  have h1 : uh 0 = u₀h := h.1
  simpa [h1] using equation_13_66_conservation ha ha₀ hd hd' h hβ hpos h0 ht ht.1

/-- **(13.67)**, Exercise 9 ([quarteroni2000numerical] (13.67) and Exercise 13.9): when (13.66)
fails, with `μ*(t)` any bound for `max_{[α,β]} |a₀(x, t) - a'(x)/2|` (the book's `μ` is
`a₀ - a'/2`), Gronwall's lemma gives
`‖u_h(t)‖² + a(β) ∫₀ᵗ u_h(β, τ)² dτ
  ≤ (‖u_{0,h}‖² + ∫₀ᵗ ‖f(τ)‖² dτ) exp ∫₀ᵗ (1 + 2 μ*(τ)) dτ`.
`Variational.IsSemidiscreteGalerkin.norm_sq_add_integral_le_exp` with the dissipativity
`le_transportForm_restrict` at `c = -μ*(t)`. -/
theorem equation_13_67 (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) {hn : 0 < n}
    {f : ℝ → BrokenPolynomial x r} {u₀h : inflowSpace x r hn} {T : ℝ}
    {uh : ℝ → inflowSpace x r hn} (h : equation_13_65 hn ha ha₀ f u₀h T uh)
    (hβ : 0 ≤ a (x (Fin.last n))) {m : ℝ → ℝ} (hm : ContinuousOn m (Icc 0 T))
    (hm0 : ∀ t ∈ Icc 0 T, 0 ≤ m t)
    (hmax : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc (x 0) (x (Fin.last n)), |a₀ s t - deriv a s / 2| ≤ m t)
    (hf : ContinuousOn (fun s => ‖f s‖) (Icc 0 T)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖uh t‖ ^ 2 + ∫ s in (0 : ℝ)..t, a (x (Fin.last n))
          * BrokenPolynomial.traceLeft (uh s : BrokenPolynomial x r) (Fin.last n) ^ 2
      ≤ (‖u₀h‖ ^ 2 + ∫ s in (0 : ℝ)..t, ‖f s‖ ^ 2) * exp (∫ s in (0 : ℝ)..t, (1 + 2 * m s)) :=
  h.norm_sq_add_integral_le_exp (Q := fun _ v => a (x (Fin.last n))
      * BrokenPolynomial.traceLeft (v : BrokenPolynomial x r) (Fin.last n) ^ 2) hm hm0
    (fun _ _ => mul_nonneg hβ (sq_nonneg _)) (continuousOn_outflow h.continuousOn)
    (fun s hs v => le_transportForm_restrict ha ha₀ hd hd' hn
      (fun y hy => neg_le_of_abs_le (hmax s hs y hy)) v) hf
    (fun s _ => norm_source_le (f s)) ht

/-- **Exercise 9** ([quarteroni2000numerical] Exercise 13.9): prove (13.67). The exercise is the
statement `equation_13_67`, recorded here under its own name. -/
theorem exercise_13_9 (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) {hn : 0 < n}
    {f : ℝ → BrokenPolynomial x r} {u₀h : inflowSpace x r hn} {T : ℝ}
    {uh : ℝ → inflowSpace x r hn} (h : equation_13_65 hn ha ha₀ f u₀h T uh)
    (hβ : 0 ≤ a (x (Fin.last n))) {m : ℝ → ℝ} (hm : ContinuousOn m (Icc 0 T))
    (hm0 : ∀ t ∈ Icc 0 T, 0 ≤ m t)
    (hmax : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc (x 0) (x (Fin.last n)), |a₀ s t - deriv a s / 2| ≤ m t)
    (hf : ContinuousOn (fun s => ‖f s‖) (Icc 0 T)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖uh t‖ ^ 2 + ∫ s in (0 : ℝ)..t, a (x (Fin.last n))
          * BrokenPolynomial.traceLeft (uh s : BrokenPolynomial x r) (Fin.last n) ^ 2
      ≤ (‖u₀h‖ ^ 2 + ∫ s in (0 : ℝ)..t, ‖f s‖ ^ 2) * exp (∫ s in (0 : ℝ)..t, (1 + 2 * m s)) :=
  equation_13_67 ha ha₀ hd hd' h hβ hm hm0 hmax hf ht

/-! ### The discontinuous Galerkin semi-discretization (13.68) -/

/-- **The discontinuous Galerkin semi-discretization** ([quarteroni2000numerical] (13.68)): find
`u_h : ℝ → W_h` with
`⟪∂ₜ u_h(t), v_h⟫ + b^{DG}_t(u_h(t), v_h) = ⟪f(t), v_h⟫ + a(α) φ(t) v_h⁺(α)` for every
`v_h ∈ W_h = Y_h^r` and `t ∈ [0, T]`, where
`b^{DG}_t(u, v) = ∑_i [∫_{I_i} (a u' + a₀(·, t) u) v + a(x_i) (u⁺(x_i) - u⁻(x_i)) v⁺(x_i)]` is the
upwind form `Variational.dgUpwindForm` with the convention `u⁻(x 0) = 0`; the book's inflow value
`U_h^-(x_0, t) = φ(t)` is carried by the source term on the right. -/
def equation_13_68 (hn : 0 < n) (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (φ : ℝ → ℝ) (f : ℝ → BrokenPolynomial x r) (u₀h : BrokenPolynomial x r) (T : ℝ)
    (uh : ℝ → BrokenPolynomial x r) : Prop :=
  Variational.IsSemidiscreteGalerkin (fun t => Variational.dgUpwindForm x r ha (ha₀ t))
    (fun t => innerSL ℝ (f t) + (a (x 0) * φ t) • BrokenPolynomial.traceRightL x r ⟨0, hn⟩)
    u₀h T uh

/-- **The energy identity of the upwind form** ([quarteroni2000numerical] §13.10.1, the
computation behind (13.69)): for every `v ∈ W_h`,
`b^{DG}_t(v, v) = ½ a(β) v⁻(β)² + ½ ∑_j a(x_j) [v]_j² + ∫_α^β (a₀(·, t) - a'/2) v²`,
with `[v]_0 = v⁺(α)`. Panel integration by parts, then at each node
`½ a v⁻² - ½ a v⁺² + a [v] v⁺ = ½ a [v]²`. -/
theorem dgUpwindForm_apply_self (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) (t : ℝ)
    (v : BrokenPolynomial x r) :
    Variational.dgUpwindForm x r ha (ha₀ t) v v
      = a (x (Fin.last n)) * BrokenPolynomial.traceLeft v (Fin.last n) ^ 2 / 2
        + ∑ i : Fin n, a (x i.castSucc) * BrokenPolynomial.jump v i ^ 2 / 2
        + ∑ i, ∫ s in x i.castSucc..x i.succ, (a₀ s t - deriv a s / 2) * (v i).eval s ^ 2 :=
  Variational.dgUpwindForm_apply_self ha (ha₀ t) hd hd' v

/-- **The dissipativity of the upwind form** ([quarteroni2000numerical] §13.10.1, the inequality
behind (13.69)): if `c ≤ a₀(·, t) - a'/2` on `[α, β]` then
`c ‖v‖²_{L²} + ½ a(β) v⁻(β)² + ½ ∑_j a(x_j) [v]_j² ≤ b^{DG}_t(v, v)` for every `v ∈ W_h`. -/
theorem le_dgUpwindForm (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) {t c : ℝ}
    (hc : ∀ s ∈ Icc (x 0) (x (Fin.last n)), c ≤ a₀ s t - deriv a s / 2)
    (v : BrokenPolynomial x r) :
    c * ‖v‖ ^ 2 + a (x (Fin.last n)) * BrokenPolynomial.traceLeft v (Fin.last n) ^ 2 / 2
        + ∑ i : Fin n, a (x i.castSucc) * BrokenPolynomial.jump v i ^ 2 / 2
      ≤ Variational.dgUpwindForm x r ha (ha₀ t) v v := by
  have hle : x 0 ≤ x (Fin.last n) := hx.out.monotone (Fin.zero_le _)
  have hlow := BrokenPolynomial.mul_norm_sq_le_sum_integral
    (intervalIntegrable_reaction ha₀ hd' hle t) hc v
  rw [dgUpwindForm_apply_self ha ha₀ hd hd' t v]
  linarith

/-- **(13.69)** ([quarteroni2000numerical] (13.69)): under `0 < μ₀ ≤ a₀ - a'/2`, the
discontinuous Galerkin solution satisfies, for `t ∈ [0, T]`,
`‖u_h(t)‖² + ∫₀ᵗ (μ₀ ‖u_h(τ)‖² + a(β) u_h⁻(β, τ)² + a(α) (u_h⁺(α, τ) - φ(τ))²
    + ∑_{j=1}^{n-1} a(x_j) [u_h(τ)]_j²) dτ
  ≤ ‖u_{0,h}‖² + ∫₀ᵗ (μ₀⁻¹ ‖f(τ)‖² + a(α) φ(τ)²) dτ`,
the book's estimate with explicit constants: its `j = 0` jump term is `a(α)(u_h⁺(α) - φ)²`
because `U_h^-(x_0, t) = φ(t)`, and the outflow term survives in addition. Test with
`v_h = u_h(t)`; the inflow source is absorbed by `2 a(α) φ u_h⁺(α) ≤ a(α) φ² + a(α) u_h⁺(α)²`
against the `j = 0` jump term of `le_dgUpwindForm`, and `2⟪f, u_h⟫ ≤ μ₀⁻¹ ‖f‖² + μ₀ ‖u_h‖²`; the
resulting pointwise inequality is integrated by
`Variational.IsSemidiscreteGalerkin.norm_sq_add_integral_le_integral`. -/
theorem equation_13_69 (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) {hn : 0 < n} {φ : ℝ → ℝ}
    {f : ℝ → BrokenPolynomial x r} {u₀h : BrokenPolynomial x r} {T : ℝ}
    {uh : ℝ → BrokenPolynomial x r} (h : equation_13_68 hn ha ha₀ φ f u₀h T uh)
    {μ₀ : ℝ} (hμ : 0 < μ₀)
    (hμ₀ : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc (x 0) (x (Fin.last n)), μ₀ ≤ a₀ s t - deriv a s / 2)
    (hf : ContinuousOn (fun s => ‖f s‖) (Icc 0 T)) (hφ : ContinuousOn φ (Icc 0 T))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖uh t‖ ^ 2 + ∫ s in (0 : ℝ)..t, (μ₀ * ‖uh s‖ ^ 2
          + a (x (Fin.last n)) * BrokenPolynomial.traceLeft (uh s) (Fin.last n) ^ 2
          + a (x 0) * (BrokenPolynomial.traceRight (uh s) ⟨0, hn⟩ - φ s) ^ 2
          + ∑ j ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
              a (x j.castSucc) * BrokenPolynomial.jump (uh s) j ^ 2)
      ≤ ‖u₀h‖ ^ 2 + ∫ s in (0 : ℝ)..t, (μ₀⁻¹ * ‖f s‖ ^ 2 + a (x 0) * φ s ^ 2) := by
  have hcont := h.continuousOn
  have hw : ContinuousOn (fun s => μ₀ * ‖uh s‖ ^ 2
      + a (x (Fin.last n)) * BrokenPolynomial.traceLeft (uh s) (Fin.last n) ^ 2
      + a (x 0) * (BrokenPolynomial.traceRight (uh s) ⟨0, hn⟩ - φ s) ^ 2
      + ∑ j ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
          a (x j.castSucc) * BrokenPolynomial.jump (uh s) j ^ 2) (Icc 0 T) := by
    refine ((((continuousOn_const.mul h.continuousOn_norm_sq).add (continuousOn_const.mul
      (((BrokenPolynomial.continuous_traceLeft (Fin.last n)).comp_continuousOn hcont).pow
        2))).add (continuousOn_const.mul
      ((((BrokenPolynomial.continuous_traceRight ⟨0, hn⟩).comp_continuousOn hcont).sub
        hφ).pow 2))).add ?_)
    exact continuousOn_finsetSum _ fun j _ => continuousOn_const.mul
      (((BrokenPolynomial.continuous_jump j).comp_continuousOn hcont).pow 2)
  have hg : ContinuousOn (fun s => μ₀⁻¹ * ‖f s‖ ^ 2 + a (x 0) * φ s ^ 2) (Icc 0 T) :=
    (continuousOn_const.mul (hf.pow 2)).add (continuousOn_const.mul (hφ.pow 2))
  refine h.norm_sq_add_integral_le_integral hw hg (fun s hs => ?_) ht
  have hs' : s ∈ Icc 0 T := Ico_subset_Icc_self hs
  set v := uh s with hv
  have hb := le_dgUpwindForm ha ha₀ hd hd' (hμ₀ s hs') v
  have hjump0 : BrokenPolynomial.jump v ⟨0, hn⟩ = BrokenPolynomial.traceRight v ⟨0, hn⟩ :=
    BrokenPolynomial.jump_zero v hn
  have hcast : (⟨0, hn⟩ : Fin n).castSucc = (0 : Fin (n + 1)) := rfl
  have hsum : a (x 0) * BrokenPolynomial.traceRight v ⟨0, hn⟩ ^ 2
      + ∑ j ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
          a (x j.castSucc) * BrokenPolynomial.jump v j ^ 2
      = ∑ j : Fin n, a (x j.castSucc) * BrokenPolynomial.jump v j ^ 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨0, hn⟩ : Fin n)), hjump0, hcast]
  have hhalf : ∑ j : Fin n, a (x j.castSucc) * BrokenPolynomial.jump v j ^ 2 / 2
      = (∑ j : Fin n, a (x j.castSucc) * BrokenPolynomial.jump v j ^ 2) / 2 :=
    (Finset.sum_div _ _ _).symm
  have hexp : a (x 0) * (BrokenPolynomial.traceRight v ⟨0, hn⟩ - φ s) ^ 2
      = a (x 0) * BrokenPolynomial.traceRight v ⟨0, hn⟩ ^ 2
        - 2 * (a (x 0) * φ s * BrokenPolynomial.traceRight v ⟨0, hn⟩) + a (x 0) * φ s ^ 2 := by
    ring
  have hfv : ⟪f s, v⟫ ≤ ‖f s‖ * ‖v‖ := real_inner_le_norm _ _
  have hY := Variational.IsSemidiscreteGalerkin.two_mul_mul_norm_le hμ (‖f s‖) v
  have hdiv : ‖f s‖ ^ 2 / μ₀ = μ₀⁻¹ * ‖f s‖ ^ 2 := by ring
  have hF : (innerSL ℝ (f s) + (a (x 0) * φ s) • BrokenPolynomial.traceRightL x r ⟨0, hn⟩) v
      = ⟪f s, v⟫ + a (x 0) * φ s * BrokenPolynomial.traceRight v ⟨0, hn⟩ := by simp
  simp only [hF]
  linarith

/-- **Exercise 10** ([quarteroni2000numerical] Exercise 13.10): prove (13.69) when `f = 0`. With
`f = 0` and `φ = 0` nothing has to be absorbed, so the full jump sum survives with the sharp
coefficient `2 μ₀`:
`‖u_h(t)‖² + ∫₀ᵗ (2 μ₀ ‖u_h(τ)‖² + a(β) u_h⁻(β, τ)² + ∑_{j=0}^{n-1} a(x_j) [u_h(τ)]_j²) dτ
  ≤ ‖u_{0,h}‖²`.
As the hint says, take `v_h = u_h(t)` in (13.68). -/
theorem exercise_13_10 (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) {hn : 0 < n}
    {u₀h : BrokenPolynomial x r} {T : ℝ} {uh : ℝ → BrokenPolynomial x r}
    (h : equation_13_68 hn ha ha₀ 0 0 u₀h T uh) {μ₀ : ℝ}
    (hμ₀ : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc (x 0) (x (Fin.last n)), μ₀ ≤ a₀ s t - deriv a s / 2)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖uh t‖ ^ 2 + ∫ s in (0 : ℝ)..t, (2 * μ₀ * ‖uh s‖ ^ 2
          + a (x (Fin.last n)) * BrokenPolynomial.traceLeft (uh s) (Fin.last n) ^ 2
          + ∑ j : Fin n, a (x j.castSucc) * BrokenPolynomial.jump (uh s) j ^ 2)
      ≤ ‖u₀h‖ ^ 2 := by
  have hcont := h.continuousOn
  have hw : ContinuousOn (fun s => 2 * μ₀ * ‖uh s‖ ^ 2
      + a (x (Fin.last n)) * BrokenPolynomial.traceLeft (uh s) (Fin.last n) ^ 2
      + ∑ j : Fin n, a (x j.castSucc) * BrokenPolynomial.jump (uh s) j ^ 2) (Icc 0 T) := by
    refine (((continuousOn_const.mul h.continuousOn_norm_sq).add (continuousOn_const.mul
      (((BrokenPolynomial.continuous_traceLeft (Fin.last n)).comp_continuousOn hcont).pow
        2))).add ?_)
    exact continuousOn_finsetSum _ fun j _ => continuousOn_const.mul
      (((BrokenPolynomial.continuous_jump j).comp_continuousOn hcont).pow 2)
  have key := h.norm_sq_add_integral_le_integral (g := fun _ => (0 : ℝ)) hw continuousOn_const
    (fun s hs => ?_) ht
  · simpa using key
  · have hs' : s ∈ Icc 0 T := Ico_subset_Icc_self hs
    have hb := le_dgUpwindForm ha ha₀ hd hd' (hμ₀ s hs') (uh s)
    have hhalf : ∑ j : Fin n, a (x j.castSucc) * BrokenPolynomial.jump (uh s) j ^ 2 / 2
        = (∑ j : Fin n, a (x j.castSucc) * BrokenPolynomial.jump (uh s) j ^ 2) / 2 :=
      (Finset.sum_div _ _ _).symm
    have hF : (innerSL ℝ ((0 : ℝ → BrokenPolynomial x r) s)
        + (a (x 0) * (0 : ℝ → ℝ) s) • BrokenPolynomial.traceRightL x r ⟨0, hn⟩) (uh s) = 0 := by
      simp
    simp only [hF]
    linarith

/-! ### The convergence estimate of the continuous Galerkin method -/

/-- **The error estimate for continuous finite elements of degree `r ≥ 1`**
([quarteroni2000numerical] §13.10.1, quoted there from [QV94] §14.3.1 without proof; proved here
with explicit constants, as `Variational.cG_error_le`). The book says "for a smooth solution `u`";
the regularity is taken as hypotheses: `u` is a classical solution of (13.64) with `φ = 0`
(`equation_13_64`), its time derivative is `ut`, continuous in `x`, and for every `t ∈ [0, T]`
`u(·, t) ∈ H^{r+1}(α, β)` with `|u(·, t)|_{H^{r+1}} ≤ M` and `ut(·, t) ∈ H^{r+1}(α, β)` with
`|ut(·, t)|_{H^{r+1}} ≤ M'`. The discrete source `f_h(t)` is the `L²` projection of `f(·, t)` onto
`V_h^{in}` (the hypothesis `hfh`), the partition has mesh at most `h` and carries a Lagrange node
system of degree `r` (`BrokenPolynomial.IsLagrangeNodes`; `r ≥ 1` is forced by the node system),
and (13.66) holds with `|a| ≤ A`, `|a₀| ≤ A₀`, `a(β) ≥ 0`. Then for every `t ∈ [0, T]`

`‖u(t) - u_h(t)‖_{L²(α,β)} + (∫₀ᵗ a(β) |u(β, τ) - u_h(β, τ)|² dτ)^{1/2}
  ≤ √2 (‖u₀ - u_{0,h}‖_{L²(α,β)} + h^r (2 h M + √(T/μ₀) (A M + h (M' + A₀ M))))`,

which is the book's `O(‖u₀ - u_{0,h}‖ + h^r)` with the constant made explicit (the `L²` norms are
written as sums of panel integrals, and the bound is uniform in `t`, which is the `max` of the
book). **Reading**: the book prints the boundary term at the inflow end `α`, where it vanishes
identically (both `u` and `u_h` satisfy the inflow condition); the term the energy estimate
(13.66) controls, and the one stated here, is at the outflow end `β`. -/
theorem cG_convergence (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) {hn : 0 < n} {T : ℝ} (hT : 0 < T)
    {μ₀ : ℝ} (hμ : 0 < μ₀)
    (hμ₀ : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc (x 0) (x (Fin.last n)), μ₀ ≤ a₀ s t - deriv a s / 2)
    (hβ : 0 ≤ a (x (Fin.last n))) {A A₀ : ℝ}
    (hA : ∀ s ∈ Icc (x 0) (x (Fin.last n)), |a s| ≤ A)
    (hA₀ : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc (x 0) (x (Fin.last n)), |a₀ s t| ≤ A₀)
    {f : ℝ → ℝ → ℝ} {u₀ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hu : equation_13_64 a a₀ f 0 u₀ (x 0) (x (Fin.last n)) T u) {ut : ℝ → ℝ → ℝ}
    (hut : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun t => u y t) (ut y t) (Icc 0 T) t)
    (hutc : ∀ t ∈ Icc 0 T, ContinuousOn (fun y => ut y t) (Icc (x 0) (x (Fin.last n))))
    {M M' : ℝ}
    (hreg : ∀ t ∈ Icc 0 T, ∃ U : SobolevInterval (r + 1) (x 0) (x (Fin.last n)),
      SobolevInterval.fn U =ᵐ[volume.restrict (Ioo (x 0) (x (Fin.last n)))] (fun y => u y t) ∧
        SobolevInterval.seminorm (r + 1) (x 0) (x (Fin.last n)) U ≤ M)
    (hreg' : ∀ t ∈ Icc 0 T, ∃ U : SobolevInterval (r + 1) (x 0) (x (Fin.last n)),
      SobolevInterval.fn U =ᵐ[volume.restrict (Ioo (x 0) (x (Fin.last n)))] (fun y => ut y t) ∧
        SobolevInterval.seminorm (r + 1) (x 0) (x (Fin.last n)) U ≤ M')
    {node : Fin n → Fin (r + 1) → ℝ} (hnode : BrokenPolynomial.IsLagrangeNodes x r node) {h : ℝ}
    (hmesh : ∀ i : Fin n, x i.succ - x i.castSucc ≤ h) {fh : ℝ → BrokenPolynomial x r}
    (hfh : ∀ t ∈ Icc 0 T, ∀ v ∈ inflowSpace x r hn,
      ⟪fh t, v⟫ = BrokenPolynomial.pairing (fun y => f y t) v)
    {u₀h : inflowSpace x r hn} {uh : ℝ → inflowSpace x r hn}
    (huh : equation_13_65 hn ha ha₀ fh u₀h T uh) {t : ℝ} (ht : t ∈ Icc 0 T) :
    √(∑ i, ∫ s in x i.castSucc..x i.succ, (u s t - ((uh t : BrokenPolynomial x r) i).eval s) ^ 2)
      + √(∫ τ in (0 : ℝ)..t, a (x (Fin.last n)) * (u (x (Fin.last n)) τ
          - BrokenPolynomial.traceLeft (uh τ : BrokenPolynomial x r) (Fin.last n)) ^ 2)
    ≤ √2 * (√(∑ i, ∫ s in x i.castSucc..x i.succ,
          (u₀ s - ((u₀h : BrokenPolynomial x r) i).eval s) ^ 2)
        + h ^ r * (2 * h * M + √(T / μ₀) * (A * M + h * (M' + A₀ * M)))) := by
  obtain ⟨ux, ut₀, hpart, hpde, hin, hinit⟩ := hu
  have hm : Monotone x := hx.out.monotone
  have hux : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun y => u y t) (ux y t) (Icc (x 0) (x (Fin.last n))) y :=
    fun y hy t ht => hpart.hasDerivWithinAt_fst hy ht
  have hut₀ : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc 0 T, ut₀ y t = ut y t :=
    fun y hy t ht =>
      (uniqueDiffOn_Icc hT t ht).eq_deriv _ (hpart.hasDerivWithinAt_snd hy ht) (hut y hy t ht)
  have hpde' : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc 0 T,
      ut y t + a y * ux y t + a₀ y t * u y t = f y t := fun y hy t ht => by
    rw [← hut₀ y hy t ht]
    exact hpde y hy t ht
  have hin' : ∀ t ∈ Icc 0 T, u (x 0) t = 0 := fun t ht => by simpa using hin t ht
  have key := Variational.cG_error_le hn hT ha ha₀ hd hd' hμ hμ₀ hβ hA hA₀ hux hut hutc hpde' hin'
    hreg hreg' (fun v => mem_inflowSpace_iff) hnode hmesh hfh huh ht
  have e : ∑ i, ∫ s in x i.castSucc..x i.succ, (u s 0 - ((u₀h : BrokenPolynomial x r) i).eval s) ^ 2
      = ∑ i, ∫ s in x i.castSucc..x i.succ, (u₀ s - ((u₀h : BrokenPolynomial x r) i).eval s) ^ 2 :=
    Finset.sum_congr rfl fun i _ => intervalIntegral.integral_congr fun s hs => by
      rw [uIcc_of_le (hm (Fin.castSucc_lt_succ (i := i)).le)] at hs
      rw [hinit s (BrokenPolynomial.Icc_panel_subset hm i hs)]
  rwa [e] at key

/-! ### The convergence estimate of the discontinuous Galerkin method -/

/-- `√(p + q) ≤ √p + √q` for `p, q ≥ 0`. -/
private theorem sqrt_add_le_sqrt_add_sqrt {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    √(p + q) ≤ √p + √q := by
  calc √(p + q) ≤ √((√p + √q) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        rw [add_sq, Real.sq_sqrt hp, Real.sq_sqrt hq]
        nlinarith [mul_nonneg (Real.sqrt_nonneg p) (Real.sqrt_nonneg q)]
    _ = √p + √q := Real.sqrt_sq (by positivity)

/-- `√p + √q ≤ √2 √(p + q)` for `p, q ≥ 0`. -/
private theorem sqrt_add_sqrt_le_sqrt_two_mul {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    √p + √q ≤ √2 * √(p + q) := by
  have hsq : (√p + √q) ^ 2 ≤ (√2 * √(p + q)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (add_nonneg hp hq), add_sq,
      Real.sq_sqrt hp, Real.sq_sqrt hq]
    nlinarith [sq_nonneg (√p - √q), Real.sq_sqrt hp, Real.sq_sqrt hq]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hsq

/-- **The convergence estimate for discontinuous finite elements of degree `r ≥ 0`**
([quarteroni2000numerical] §13.10.1, quoted there from [QV94] §14.3.3 without proof; proved here
with explicit constants, as `Variational.dG_error_sq_le`). The book says "for a smooth solution
`u`"; the regularity is taken as hypotheses: `u` is a classical solution of (13.64)
(`equation_13_64`) continuous on the strip, its time derivative `ut` is continuous on the strip,
and `u(·, t) ∈ H^{r+1}(α, β)` with `|u(·, t)|_{H^{r+1}} ≤ M` for every `t ∈ [0, T]`. The discrete
source `f_h(t)` is the `L²` projection of `f(·, t)` onto `W_h` (the hypothesis `hfh`), the
partition has panels of length between `h_min` and `h` and carries a node system of degree `r`,
and (13.66) holds with `0 ≤ a ≤ A`, `|a'| ≤ A'`, `|a₀| ≤ A₀`. Then for every `t ∈ [0, T]`

`‖u(t) - u_h(t)‖_{L²}
  + (∫₀ᵗ (‖u(τ) - u_h(τ)‖²_{L²} + ∑_{j=0}^{n-1} a(x_j) [u(τ) - u_h(τ)]_j²) dτ)^{1/2}
  ≤ √2 (√(16 + 4/μ₀) ‖u₀ - u_{0,h}‖_{L²} + √(dgConst) h^{r+1/2})`,

the book's `O(‖u₀ - u_{0,h}‖ + h^{r+1/2})` with the constant `Variational.dgConst` made
explicit; `h^{r+1/2}` is written `h^r √h`. **Reading**: the book's printed left side has a
garbled `∫_{j=0}^{T_{n-1}}`, read as `∫₀ᵀ ∑_{j=0}^{n-1}`; the jumps of `u - u_h` are those of
`-u_h` at the interior nodes (`u` is continuous), and at `x_0 = α` the jump is `φ - u_h⁺(α)` by the
convention `U_h^-(x_0, t) = φ(t)` of (13.68). -/
theorem dG_convergence (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) {hn : 0 < n} {T : ℝ} (hT : 0 < T)
    {μ₀ : ℝ} (hμ : 0 < μ₀)
    (hμ₀ : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc (x 0) (x (Fin.last n)), μ₀ ≤ a₀ s t - deriv a s / 2)
    (hapos : ∀ s ∈ Icc (x 0) (x (Fin.last n)), 0 ≤ a s) {A A' A₀ : ℝ}
    (hA : ∀ s ∈ Icc (x 0) (x (Fin.last n)), |a s| ≤ A)
    (hA' : ∀ s ∈ Icc (x 0) (x (Fin.last n)), |deriv a s| ≤ A')
    (hA₀ : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc (x 0) (x (Fin.last n)), |a₀ s t| ≤ A₀)
    {f : ℝ → ℝ → ℝ} {φ u₀ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hu : equation_13_64 a a₀ f φ u₀ (x 0) (x (Fin.last n)) T u)
    (huc : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) (Icc (x 0) (x (Fin.last n)) ×ˢ Icc 0 T))
    {ut : ℝ → ℝ → ℝ}
    (hut : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun t => u y t) (ut y t) (Icc 0 T) t)
    (hutc : ContinuousOn (fun p : ℝ × ℝ => ut p.1 p.2) (Icc (x 0) (x (Fin.last n)) ×ˢ Icc 0 T))
    {M : ℝ}
    (hreg : ∀ t ∈ Icc 0 T, ∃ U : SobolevInterval (r + 1) (x 0) (x (Fin.last n)),
      SobolevInterval.fn U =ᵐ[volume.restrict (Ioo (x 0) (x (Fin.last n)))] (fun y => u y t) ∧
        SobolevInterval.seminorm (r + 1) (x 0) (x (Fin.last n)) U ≤ M)
    {node : Fin n → Fin (r + 1) → ℝ} (hnode : BrokenPolynomial.IsNodes x r node) {h hmin : ℝ}
    (hmesh : ∀ i : Fin n, x i.succ - x i.castSucc ≤ h) (h0 : 0 < hmin)
    (hminle : ∀ i : Fin n, hmin ≤ x i.succ - x i.castSucc) {fh : ℝ → BrokenPolynomial x r}
    (hfh : ∀ t ∈ Icc 0 T, ∀ v, ⟪fh t, v⟫ = BrokenPolynomial.pairing (fun y => f y t) v)
    {u₀h : BrokenPolynomial x r} {uh : ℝ → BrokenPolynomial x r}
    (huh : equation_13_68 hn ha ha₀ φ fh u₀h T uh) {t : ℝ} (ht : t ∈ Icc 0 T) :
    √(∑ i, ∫ s in x i.castSucc..x i.succ, (u s t - (uh t i).eval s) ^ 2)
      + √(∫ τ in (0 : ℝ)..t, ((∑ i, ∫ s in x i.castSucc..x i.succ, (u s τ - (uh τ i).eval s) ^ 2)
          + (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
              a (x i.castSucc) * BrokenPolynomial.jump (uh τ) i ^ 2)
          + a (x 0) * (BrokenPolynomial.traceRight (uh τ) ⟨0, hn⟩ - φ τ) ^ 2))
    ≤ √2 * (√(16 + 4 / μ₀) * √(∑ i, ∫ s in x i.castSucc..x i.succ, (u₀ s - (u₀h i).eval s) ^ 2)
        + √(Variational.dgConst r A A' A₀ μ₀ T M h hmin) * (h ^ r * √h)) := by
  obtain ⟨ux, ut₀, hpart, hpde, hin, hinit⟩ := hu
  have hm : Monotone x := hx.out.monotone
  have hab : x 0 < x (Fin.last n) := hx.out (Fin.pos_iff_ne_zero.2 (Fin.ne_of_val_ne hn.ne'))
  have hT0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hle : ∀ i : Fin n, x i.castSucc ≤ x i.succ := fun i => hm (Fin.castSucc_lt_succ (i := i)).le
  have hh : 0 ≤ h := (sub_nonneg.2 (hle ⟨0, hn⟩)).trans (hmesh ⟨0, hn⟩)
  obtain ⟨U₀, hU₀, hU₀M⟩ := hreg 0 hT0
  have hM : 0 ≤ M := (apply_nonneg _ _).trans hU₀M
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA (x 0) (left_mem_Icc.2 hab.le))
  have hA'0 : 0 ≤ A' := (abs_nonneg _).trans (hA' (x 0) (left_mem_Icc.2 hab.le))
  have hA₀0 : 0 ≤ A₀ := (abs_nonneg _).trans (hA₀ 0 hT0 (x 0) (left_mem_Icc.2 hab.le))
  have hux : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun y => u y t) (ux y t) (Icc (x 0) (x (Fin.last n))) y :=
    fun y hy t ht => hpart.hasDerivWithinAt_fst hy ht
  have hut₀ : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc 0 T, ut₀ y t = ut y t :=
    fun y hy t ht =>
      (uniqueDiffOn_Icc hT t ht).eq_deriv _ (hpart.hasDerivWithinAt_snd hy ht) (hut y hy t ht)
  have hpde' : ∀ y ∈ Icc (x 0) (x (Fin.last n)), ∀ t ∈ Icc 0 T,
      ut y t + a y * ux y t + a₀ y t * u y t = f y t := fun y hy t ht => by
    rw [← hut₀ y hy t ht]
    exact hpde y hy t ht
  have key := Variational.dG_error_sq_le hn hT ha ha₀ hd hd' hμ hμ₀ hapos hA hA' hA₀ huc hux hut
    hutc hpde' hin hreg hnode hmesh h0 hminle hfh huh ht
  have e : ∑ i, ∫ s in x i.castSucc..x i.succ, (u s 0 - (u₀h i).eval s) ^ 2
      = ∑ i, ∫ s in x i.castSucc..x i.succ, (u₀ s - (u₀h i).eval s) ^ 2 :=
    Finset.sum_congr rfl fun i _ => intervalIntegral.integral_congr fun s hs => by
      rw [uIcc_of_le (hle i)] at hs
      rw [hinit s (BrokenPolynomial.Icc_panel_subset hm i hs)]
  rw [e] at key
  -- nonnegativity of the pieces
  have hY₀ : 0 ≤ ∑ i, ∫ s in x i.castSucc..x i.succ, (u s t - (uh t i).eval s) ^ 2 :=
    Finset.sum_nonneg fun i _ => intervalIntegral.integral_nonneg (hle i) fun _ _ => sq_nonneg _
  have hI : 0 ≤ ∫ τ in (0 : ℝ)..t,
      ((∑ i, ∫ s in x i.castSucc..x i.succ, (u s τ - (uh τ i).eval s) ^ 2)
        + (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
            a (x i.castSucc) * BrokenPolynomial.jump (uh τ) i ^ 2)
        + a (x 0) * (BrokenPolynomial.traceRight (uh τ) ⟨0, hn⟩ - φ τ) ^ 2) := by
    refine intervalIntegral.integral_nonneg ht.1 fun τ _ => ?_
    have h1 : 0 ≤ ∑ i, ∫ s in x i.castSucc..x i.succ, (u s τ - (uh τ i).eval s) ^ 2 :=
      Finset.sum_nonneg fun i _ => intervalIntegral.integral_nonneg (hle i) fun _ _ => sq_nonneg _
    have h2 : 0 ≤ ∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
        a (x i.castSucc) * BrokenPolynomial.jump (uh τ) i ^ 2 :=
      Finset.sum_nonneg fun i _ => mul_nonneg
        (hapos _ (BrokenPolynomial.Icc_panel_subset hm i (left_mem_Icc.2 (hle i)))) (sq_nonneg _)
    have h3 : 0 ≤ a (x 0) * (BrokenPolynomial.traceRight (uh τ) ⟨0, hn⟩ - φ τ) ^ 2 :=
      mul_nonneg (hapos _ (left_mem_Icc.2 hab.le)) (sq_nonneg _)
    linarith
  have hYi : 0 ≤ ∑ i, ∫ s in x i.castSucc..x i.succ, (u₀ s - (u₀h i).eval s) ^ 2 :=
    Finset.sum_nonneg fun i _ => intervalIntegral.integral_nonneg (hle i) fun _ _ => sq_nonneg _
  have hC₁ : 0 ≤ 16 + 4 / μ₀ := by positivity
  have hC₂ : 0 ≤ Variational.dgConst r A A' A₀ μ₀ T M h hmin := by
    unfold Variational.dgConst
    positivity
  have hpow : √(h ^ (2 * r + 1)) = h ^ r * √h := by
    rw [show h ^ (2 * r + 1) = (h ^ r) ^ 2 * h by rw [pow_succ, pow_mul'],
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg hh r)]
  calc √(∑ i, ∫ s in x i.castSucc..x i.succ, (u s t - (uh t i).eval s) ^ 2)
        + √(∫ τ in (0 : ℝ)..t,
          ((∑ i, ∫ s in x i.castSucc..x i.succ, (u s τ - (uh τ i).eval s) ^ 2)
          + (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
              a (x i.castSucc) * BrokenPolynomial.jump (uh τ) i ^ 2)
          + a (x 0) * (BrokenPolynomial.traceRight (uh τ) ⟨0, hn⟩ - φ τ) ^ 2))
      ≤ √2 * √((∑ i, ∫ s in x i.castSucc..x i.succ, (u s t - (uh t i).eval s) ^ 2)
          + ∫ τ in (0 : ℝ)..t,
          ((∑ i, ∫ s in x i.castSucc..x i.succ, (u s τ - (uh τ i).eval s) ^ 2)
          + (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n),
              a (x i.castSucc) * BrokenPolynomial.jump (uh τ) i ^ 2)
          + a (x 0) * (BrokenPolynomial.traceRight (uh τ) ⟨0, hn⟩ - φ τ) ^ 2)) :=
        sqrt_add_sqrt_le_sqrt_two_mul hY₀ hI
    _ ≤ √2 * √((16 + 4 / μ₀) * (∑ i, ∫ s in x i.castSucc..x i.succ, (u₀ s - (u₀h i).eval s) ^ 2)
          + Variational.dgConst r A A' A₀ μ₀ T M h hmin * h ^ (2 * r + 1)) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt key) (Real.sqrt_nonneg _)
    _ ≤ √2 * (√((16 + 4 / μ₀) * (∑ i, ∫ s in x i.castSucc..x i.succ, (u₀ s - (u₀h i).eval s) ^ 2))
          + √(Variational.dgConst r A A' A₀ μ₀ T M h hmin * h ^ (2 * r + 1))) :=
        mul_le_mul_of_nonneg_left (sqrt_add_le_sqrt_add_sqrt (by positivity) (by positivity))
          (Real.sqrt_nonneg _)
    _ = √2 * (√(16 + 4 / μ₀) * √(∑ i, ∫ s in x i.castSucc..x i.succ, (u₀ s - (u₀h i).eval s) ^ 2)
          + √(Variational.dgConst r A A' A₀ μ₀ T M h hmin) * (h ^ r * √h)) := by
        rw [Real.sqrt_mul hC₁, Real.sqrt_mul hC₂, hpow]

/-! ### Time discretization: backward Euler (13.70) -/

/-- **Backward Euler in time for (13.65)** ([quarteroni2000numerical] (13.70)) with a vanishing
inflow datum: `u_h^{n+1} ∈ V_h^{in}` with
`Δt⁻¹ ⟪u_h^{n+1} - u_h^n, v_h⟫ + b_{t^{n+1}}(u_h^{n+1}, v_h) = ⟪f^{n+1}, v_h⟫` for every
`v_h ∈ V_h^{in}`, i.e. the θ-step at `θ = 1` for the transport form at the new time. -/
def equation_13_70 (hn : 0 < n) (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (Δt t₁ : ℝ) (f₁ : BrokenPolynomial x r) (un un1 : inflowSpace x r hn) : Prop :=
  Variational.IsThetaStep ((transportForm x r ha ha₀ t₁).restrict (inflowSpace x r hn)) 1 Δt 0
    ((innerSL ℝ f₁).comp (inflowSpace x r hn).subtypeL) un un1

/-- A source-free step of (13.70) is a backward Euler θ-step with zero right-hand side. -/
theorem isThetaStep_of_equation_13_70 (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    {hn : 0 < n} {Δt t₁ : ℝ} {un un1 : inflowSpace x r hn}
    (h : equation_13_70 hn ha ha₀ Δt t₁ 0 un un1) :
    Variational.IsThetaStep ((transportForm x r ha ha₀ t₁).restrict (inflowSpace x r hn))
      1 Δt 0 0 un un1 := fun v => by simpa using h v

/-- **Unconditional stability of (13.70), one step** ([quarteroni2000numerical] §13.10.2, the
display after (13.70)): with `f = 0`, `φ = 0` and `μ₀ ≤ a₀ - a'/2`,
`(2Δt)⁻¹ (‖u_h^{n+1}‖² - ‖u_h^n‖²) + ½ a(β) u_h^{n+1}(β)² + μ₀ ‖u_h^{n+1}‖² ≤ 0`
for every `Δt > 0`, with no condition relating `Δt` to the mesh. **Erratum**: the book prints
`a(β)(u_h^{n+1}(β))²` without the factor `½`; the derivation it describes — test with
`v_h = u_h^{n+1}`, use `⟪w - u, w⟫ ≥ ½(‖w‖² - ‖u‖²)` and the energy identity, whose outflow term
is `½ a(β) v(β)²` — gives the factor, and the printed inequality is strictly stronger and does
not follow. -/
theorem equation_13_70_stability (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) {hn : 0 < n} {Δt t₁ μ₀ : ℝ}
    (hΔt : 0 < Δt) (hμ₀ : ∀ s ∈ Icc (x 0) (x (Fin.last n)), μ₀ ≤ a₀ s t₁ - deriv a s / 2)
    {un un1 : inflowSpace x r hn} (h : equation_13_70 hn ha ha₀ Δt t₁ 0 un un1) :
    (2 * Δt)⁻¹ * (‖un1‖ ^ 2 - ‖un‖ ^ 2)
        + a (x (Fin.last n))
          * BrokenPolynomial.traceLeft (un1 : BrokenPolynomial x r) (Fin.last n) ^ 2 / 2
        + μ₀ * ‖un1‖ ^ 2 ≤ 0 := by
  have hstep := (isThetaStep_of_equation_13_70 ha ha₀ h).norm_sq_add_two_mul_le hΔt
  have hb := le_transportForm_restrict ha ha₀ hd hd' hn hμ₀ un1
  have hkey : ‖un1‖ ^ 2 - ‖un‖ ^ 2 + 2 * Δt * (a (x (Fin.last n))
      * BrokenPolynomial.traceLeft (un1 : BrokenPolynomial x r) (Fin.last n) ^ 2 / 2
      + μ₀ * ‖un1‖ ^ 2) ≤ 0 := by nlinarith [hstep, hb, hΔt]
  have he : (2 * Δt)⁻¹ * (‖un1‖ ^ 2 - ‖un‖ ^ 2)
        + a (x (Fin.last n))
          * BrokenPolynomial.traceLeft (un1 : BrokenPolynomial x r) (Fin.last n) ^ 2 / 2
        + μ₀ * ‖un1‖ ^ 2
      = (2 * Δt)⁻¹ * (‖un1‖ ^ 2 - ‖un‖ ^ 2 + 2 * Δt * (a (x (Fin.last n))
          * BrokenPolynomial.traceLeft (un1 : BrokenPolynomial x r) (Fin.last n) ^ 2 / 2
          + μ₀ * ‖un1‖ ^ 2)) := by
    field_simp
    ring
  rw [he]
  have hpos : (0 : ℝ) < (2 * Δt)⁻¹ := by positivity
  nlinarith [hkey, hpos]

/-- **Unconditional stability of (13.70), summed** ([quarteroni2000numerical] §13.10.2): summing
`equation_13_70_stability` over `n = 0, …, m - 1`,
`‖u_h^m‖² + 2Δt ∑_{j=1}^m (μ₀ ‖u_h^j‖² + ½ a(β) u_h^j(β)²) ≤ ‖u_h^0‖²`.
The reaction coefficient may depend on time, `τ k` being the time of the `k`-th step. -/
theorem equation_13_70_sum (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) {hn : 0 < n} {Δt μ₀ : ℝ}
    (hΔt : 0 < Δt) {τ : ℕ → ℝ} {uh : ℕ → inflowSpace x r hn} {m : ℕ}
    (hμ₀ : ∀ k, ∀ s ∈ Icc (x 0) (x (Fin.last n)), μ₀ ≤ a₀ s (τ k) - deriv a s / 2)
    (hstep : ∀ k < m, equation_13_70 hn ha ha₀ Δt (τ k) 0 (uh k) (uh (k + 1))) :
    ‖uh m‖ ^ 2 + 2 * Δt * ∑ k ∈ Finset.range m, (μ₀ * ‖uh (k + 1)‖ ^ 2
        + a (x (Fin.last n)) * BrokenPolynomial.traceLeft
            (uh (k + 1) : BrokenPolynomial x r) (Fin.last n) ^ 2 / 2)
      ≤ ‖uh 0‖ ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have ih' := ih fun k hk => hstep k (Nat.lt_succ_of_lt hk)
    have hlast := (isThetaStep_of_equation_13_70 ha ha₀
      (hstep m (Nat.lt_succ_self m))).norm_sq_add_two_mul_le hΔt
    have hb := le_transportForm_restrict ha ha₀ hd hd' hn (hμ₀ m) (uh (m + 1))
    rw [Finset.sum_range_succ, mul_add]
    nlinarith [hlast, hb, hΔt]

/-- **Unconditional stability of (13.70)**, the conclusion the book draws
([quarteroni2000numerical] §13.10.2): `‖u_h^m‖_{L²} ≤ ‖u_h^0‖_{L²}` for every `m ≥ 0` and every
time step `Δt > 0`. -/
theorem equation_13_70_norm_le (ha : IntervalIntegrable a volume (x 0) (x (Fin.last n)))
    (ha₀ : ∀ t, IntervalIntegrable (fun s => a₀ s t) volume (x 0) (x (Fin.last n)))
    (hd : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (hd' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) {hn : 0 < n} {Δt μ₀ : ℝ}
    (hΔt : 0 < Δt) (hμ : 0 ≤ μ₀) (hβ : 0 ≤ a (x (Fin.last n))) {τ : ℕ → ℝ}
    {uh : ℕ → inflowSpace x r hn} {m : ℕ}
    (hμ₀ : ∀ k, ∀ s ∈ Icc (x 0) (x (Fin.last n)), μ₀ ≤ a₀ s (τ k) - deriv a s / 2)
    (hstep : ∀ k < m, equation_13_70 hn ha ha₀ Δt (τ k) 0 (uh k) (uh (k + 1))) :
    ‖uh m‖ ≤ ‖uh 0‖ := by
  have hsum := equation_13_70_sum ha ha₀ hd hd' hΔt hμ₀ hstep
  have hnonneg : 0 ≤ ∑ k ∈ Finset.range m, (μ₀ * ‖uh (k + 1)‖ ^ 2
      + a (x (Fin.last n)) * BrokenPolynomial.traceLeft
          (uh (k + 1) : BrokenPolynomial x r) (Fin.last n) ^ 2 / 2) :=
    Finset.sum_nonneg fun k _ => by positivity
  have hle : ‖uh m‖ ^ 2 ≤ ‖uh 0‖ ^ 2 := by nlinarith [hsum, hnonneg, hΔt]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hle

end Transport

end QuarteroniSaccoSaleri.Chapter13

end

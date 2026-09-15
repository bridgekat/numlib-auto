import Numlib.Variational.AdvectionDiffusion

/-!
# Quarteroni–Sacco–Saleri §12.5: advection–diffusion equations

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §12.5.

The model problem is `-ε u'' + β u' = 0` on `(0, 1)` with `u(0) = 0`, `u(1) = 1` and
`ε, β > 0` with `ε/β ≪ 1` (12.70): advection dominates diffusion, the global Péclet number
`Pe_gl = |β| L/(2ε)` (12.71) is large, and the exact solution
`u(x) = (e^{βx/ε} - 1)/(e^{β/ε} - 1)` has a boundary layer of width `O(ε/β)` at `x = 1`. The
piecewise linear Galerkin method on a uniform mesh produces the difference equation (12.75)–(12.76)
`(Pe - 1) u_{i+1} + 2 u_i - (Pe + 1) u_{i-1} = 0` in the local Péclet number `Pe = |β| h/(2ε)`,
whose solution `u_i = (1 - ρ^i)/(1 - ρ^n)`, `ρ = (1 + Pe)/(1 - Pe)`, **oscillates as soon as
`Pe > 1`**. The same equations are the centred finite differences (12.77); replacing the centred
difference for `u'` by the upwind one (12.78) is the same as keeping the centred scheme and
raising the diffusion to `ε_h = ε (1 + Pe)` (12.79)–(12.81), the *numerical viscosity*. More
generally (12.82) takes `ε_h = ε (1 + φ(Pe))`; `φ^UP(t) = t` is upwinding and
`φ^SG(t) = t - 1 + B(2t)` (12.83), with `B` the Bernoulli function, is exponential fitting
(Scharfetter–Gummel), for which the scheme is *nodally exact* (Remark 12.6). For both the
stabilized Péclet number `Pe* = Pe/(1 + φ(Pe))` is below `1` for every mesh size, so the matrix of
the scheme is an M-matrix (Exercise 12.13) and the discrete solution obeys a maximum principle.
Finally the viscosity is carried over to finite elements of any degree (12.84), and Theorem 12.4
gives the convergence rates.

Everything is a restatement of `Numlib/Variational/AdvectionDiffusion.lean`, whose conventions this
module inherits: grid functions are `ℕ → ℝ` (constrained only at the indices `0, …, n`), the
three-term relations are written at the indices `i`, `i + 1`, `i + 2` rather than
`i - 1`, `i`, `i + 1`, and the bilinear forms are `EllipticInterval.form` on
`SobolevInterval 1 0 1 = H¹(0, 1)` with constant `L^∞` coefficients.

## Main results

* `equation_12_71`, `meshPeclet` — the global and local Péclet numbers.
* `equation_12_70_solution`, `equation_12_70_unique` — the exact solution of (12.70).
* `remark_12_5` — the conservation form (12.74) has the same bilinear form as (12.73) for
  constant coefficients.
* `equation_12_76_solution`, `equation_12_76_unique`, `equation_12_76_oscillates` — the explicit
  solution of the centred difference equation, and its oscillation for `Pe > 1`.
* `equation_12_77` — the centred finite differences are the equations (12.75) of the piecewise
  linear Galerkin method, after multiplication by `h`.
* `equation_12_79`, `equation_12_81`, `equation_12_78_zero_diffusion` — upwinding is centred
  differencing with the artificial viscosity `ε Pe = |β| h/2`.
* `equation_12_82`, `equation_12_83` — the general viscosity and the Scharfetter–Gummel choice.
* `remark_12_6_asymptotics`, `remark_12_6_nodal_exact` — `φ^SG ≃ φ^UP` at infinity, `φ^SG = O(h²)`
  at the origin, and the nodal exactness of the Scharfetter–Gummel scheme.
* `stabilizedPeclet_lt_one` — `Pe* < 1` for the upwind and the Scharfetter–Gummel schemes, for
  every mesh size.
* `exercise_12_13` — the matrix of the stabilized scheme is an M-matrix, hence the discrete
  maximum principle.
* `equation_12_84`, `equation_12_84_self` — the stabilized finite element problem and the energy
  identity `a_h(v, v) = ε_h |v|²_{H¹}` behind it.

## Not formalized here

The identification of the Galerkin problem (12.72)–(12.73) with the difference equation (12.75),
and hence Theorem 12.4, need the Lagrange finite element space `X_h^k` inside `H¹(0, 1)`
(`Numlib/Variational/FiniteElementInterval.lean`); the plan records them as open nodes with the
missing dependency. Remark 12.6's nodal exactness for a piecewise constant right-hand side is
quoted by the book from [HGR96] and is not formalized either; the homogeneous case, which is what
the proof of Theorem 12.4 uses, is `remark_12_6_nodal_exact`. Example 12.3 is a numerical
experiment.
-/

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology

namespace QuarteroniSaccoSaleri.Chapter12

/-! ### The Péclet numbers -/

/-- **The global Péclet number** (12.71), `Pe_gl = |β| L/(2 ε)`, where `L` is the size of the
domain: it measures the dominance of the advective term over the diffusive one. -/
noncomputable def equation_12_71 (β L ε : ℝ) : ℝ := AdvectionDiffusion.globalPeclet β L ε

/-- (12.71) is `|β| L/(2 ε)`. -/
theorem equation_12_71_eq (β L ε : ℝ) : equation_12_71 β L ε = |β| * L / (2 * ε) := rfl

/-- **The local (mesh) Péclet number** of §12.5.1, `Pe = |β| h/(2 ε)`. -/
noncomputable def meshPeclet (β h ε : ℝ) : ℝ := AdvectionDiffusion.localPeclet β h ε

/-- The local Péclet number is `|β| h/(2 ε)`. -/
theorem meshPeclet_eq (β h ε : ℝ) : meshPeclet β h ε = |β| * h / (2 * ε) := rfl

/-- On the unit interval the local Péclet number is `h` times the global one. -/
theorem meshPeclet_eq_equation_12_71_mul (β h ε : ℝ) :
    meshPeclet β h ε = equation_12_71 β 1 ε * h :=
  AdvectionDiffusion.localPeclet_eq_globalPeclet_mul β h ε

/-! ### The exact solution of (12.70) -/

/-- **The exact solution of (12.70)** `-ε u'' + β u' = 0`, `u(0) = 0`, `u(1) = 1`, for
`ε, β > 0`: `u(x) = (exp(βx/ε) - 1)/(exp(β/ε) - 1)`, obtained from the characteristic roots
`λ₁ = 0` and `λ₂ = β/ε`. -/
theorem equation_12_70_solution {ε β : ℝ} (hε : 0 < ε) (hβ : 0 < β) :
    AdvectionDiffusion.exactSolution ε β 0 = 0 ∧ AdvectionDiffusion.exactSolution ε β 1 = 1 ∧
      ∀ x, -ε * deriv (deriv (AdvectionDiffusion.exactSolution ε β)) x
        + β * deriv (AdvectionDiffusion.exactSolution ε β) x = 0 :=
  ⟨AdvectionDiffusion.exactSolution_zero ε β, AdvectionDiffusion.exactSolution_one hε hβ,
    AdvectionDiffusion.exactSolution_solves hε.ne' β⟩

/-- **(12.70) has no other `C²` solution**: the boundary conditions fix the two constants of the
general solution `C₁ + C₂ e^{βx/ε}`. -/
theorem equation_12_70_unique {ε β : ℝ} (hε : 0 < ε) (hβ : 0 < β) {u : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (hode : ∀ x, -ε * deriv (deriv u) x + β * deriv u x = 0)
    (h0 : u 0 = 0) (h1 : u 1 = 1) : u = AdvectionDiffusion.exactSolution ε β :=
  AdvectionDiffusion.exactSolution_unique hε hβ hu hode h0 h1

/-! ### The conservation form (12.74) -/

open SobolevInterval in
/-- **Remark 12.5, the conservation form** (12.74) `-(ε u' - β u)' = 0`: its bilinear form
`b(u, v) = ∫₀¹ (ε u' - β u) v'` coincides with the form `a(u, v) = ∫₀¹ (ε u' v' + β u' v)` of
(12.73) when `ε` and `β` are constant, for `u ∈ H¹(0, 1)` and `v ∈ H¹₀(0, 1)`.  The two differ by
`β ∫ (u' g_v + g_u v') = β [g_u g_v]₀¹`, which vanishes because `v` does at both endpoints. -/
theorem remark_12_5 (ε β : ℝ) (u : SobolevInterval 1 0 1) {v : SobolevInterval 1 0 1}
    (hv : v ∈ SobolevIntervalZero 0 1) :
    EllipticInterval.form 0 1 (AdvectionDiffusion.constLinf 0 1 ε)
        (AdvectionDiffusion.constLinf 0 1 β) 0 u v
      = ∫ x in Ioo (0 : ℝ) 1, (ε * deriv u 1 x - β * rep u x) * deriv v 1 x := by
  have hab : (0 : ℝ) < 1 := one_pos
  have hcε := AdvectionDiffusion.coeFn_constLinf 0 1 ε
  have hcβ := AdvectionDiffusion.coeFn_constLinf 0 1 β
  have hc1 := AdvectionDiffusion.coeFn_constLinf 0 1 1
  have hru := fn_ae_eq_rep hab u
  have hrv := fn_ae_eq_rep hab v
  -- the three integrands, and their integrability
  have i1 : IntegrableOn (fun x => ε * (deriv u 1 x * deriv v 1 x)) (Ioo (0 : ℝ) 1) := by
    refine (EllipticInterval.integrable_mul_mul (AdvectionDiffusion.constLinf 0 1 ε)
      (deriv u 1) (deriv v 1)).congr ?_
    filter_upwards [hcε] with x hx
    rw [hx]
    ring
  have i2 : IntegrableOn (fun x => deriv u 1 x * rep v x) (Ioo (0 : ℝ) 1) := by
    refine (EllipticInterval.integrable_mul_mul (AdvectionDiffusion.constLinf 0 1 1)
      (deriv u 1) (deriv v 0)).congr ?_
    filter_upwards [hc1, hrv] with x h1 h2
    rw [h1, SobolevInterval.deriv_zero, h2]
    ring
  have i3 : IntegrableOn (fun x => rep u x * deriv v 1 x) (Ioo (0 : ℝ) 1) := by
    refine (EllipticInterval.integrable_mul_mul (AdvectionDiffusion.constLinf 0 1 1)
      (deriv u 0) (deriv v 1)).congr ?_
    filter_upwards [hc1, hru] with x h1 h2
    rw [h1, SobolevInterval.deriv_zero, h2]
    ring
  -- the boundary terms of the integration by parts vanish
  have ibp := integral_deriv_mul_add_mul_deriv hab u v
  rw [SobolevIntervalZero.rep_left_eq_zero hab hv, SobolevIntervalZero.rep_right_eq_zero hab hv,
    mul_zero, mul_zero, sub_zero, EllipticInterval.intervalIntegral_eq_setIntegral_Ioo hab.le,
    integral_add i2 i3] at ibp
  rw [EllipticInterval.form_apply]
  have e1 : ∀ x : ℝ, (AdvectionDiffusion.constLinf 0 1 ε : ℝ → ℝ) x = ε →
      (AdvectionDiffusion.constLinf 0 1 β : ℝ → ℝ) x = β → fn v x = rep v x →
      ((0 : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))) : ℝ → ℝ) x = 0 →
      (AdvectionDiffusion.constLinf 0 1 ε : ℝ → ℝ) x * deriv u 1 x * deriv v 1 x
        + (AdvectionDiffusion.constLinf 0 1 β : ℝ → ℝ) x * deriv u 1 x * deriv v 0 x
        + ((0 : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))) : ℝ → ℝ) x * deriv u 0 x * deriv v 0 x
      = ε * (deriv u 1 x * deriv v 1 x) + β * (deriv u 1 x * rep v x) := by
    intro x h1 h2 h3 h4
    rw [h1, h2, h4, SobolevInterval.deriv_zero, h3]
    ring
  have hform : ∫ x in Ioo (0 : ℝ) 1,
      ((AdvectionDiffusion.constLinf 0 1 ε : ℝ → ℝ) x * deriv u 1 x * deriv v 1 x
        + (AdvectionDiffusion.constLinf 0 1 β : ℝ → ℝ) x * deriv u 1 x * deriv v 0 x
        + ((0 : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))) : ℝ → ℝ) x * deriv u 0 x
          * deriv v 0 x)
      = (∫ x in Ioo (0 : ℝ) 1, ε * (deriv u 1 x * deriv v 1 x))
        + ∫ x in Ioo (0 : ℝ) 1, β * (deriv u 1 x * rep v x) := by
    rw [← integral_add i1 (i2.const_mul β)]
    refine integral_congr_ae ?_
    filter_upwards [hcε, hcβ, hrv, Lp.coeFn_zero ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))]
      with x h1 h2 h3 h4
    exact e1 x h1 h2 h3 (by rw [h4]; rfl)
  have e2 : ∫ x in Ioo (0 : ℝ) 1, (ε * deriv u 1 x - β * rep u x) * deriv v 1 x
      = (∫ x in Ioo (0 : ℝ) 1, ε * (deriv u 1 x * deriv v 1 x))
        - ∫ x in Ioo (0 : ℝ) 1, β * (rep u x * deriv v 1 x) := by
    rw [← integral_sub i1 (i3.const_mul β)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    ring
  rw [hform, e2]
  simp only [integral_const_mul]
  linear_combination β * ibp

/-! ### The centred difference equation (12.76) and its oscillation -/

/-- **The solution of the centred difference equation (12.76)** with `u_0 = 0`, `u_n = 1`:
`u_i = (1 - ρ^i)/(1 - ρ^n)` with `ρ = (1 + Pe)/(1 - Pe)`, the roots of the characteristic equation
`(Pe - 1) ρ² + 2 ρ - (Pe + 1) = 0` being `ρ` and `1`. -/
theorem equation_12_76_solution {Pe : ℝ} (hPe : 0 < Pe) (hPe1 : Pe ≠ 1) {n : ℕ} (hn : n ≠ 0) :
    AdvectionDiffusion.centredSolution n Pe 0 = 0 ∧
      AdvectionDiffusion.centredSolution n Pe n = 1 ∧
      ∀ i, i + 2 ≤ n → (Pe - 1) * AdvectionDiffusion.centredSolution n Pe (i + 2)
        + 2 * AdvectionDiffusion.centredSolution n Pe (i + 1)
        - (Pe + 1) * AdvectionDiffusion.centredSolution n Pe i = 0 :=
  ⟨AdvectionDiffusion.centredSolution_zero n Pe,
    AdvectionDiffusion.centredSolution_self hPe hPe1 hn,
    fun i _ => AdvectionDiffusion.centredSolution_solves hPe1 n i⟩

/-- (12.76) has no other solution with the two boundary values. -/
theorem equation_12_76_unique {Pe : ℝ} (hPe : 0 < Pe) (hPe1 : Pe ≠ 1) {n : ℕ} (hn : n ≠ 0)
    {u : ℕ → ℝ} (h0 : u 0 = 0) (hlast : u n = 1)
    (hrec : ∀ i, i + 2 ≤ n → (Pe - 1) * u (i + 2) + 2 * u (i + 1) - (Pe + 1) * u i = 0)
    {i : ℕ} (hi : i ≤ n) : u i = AdvectionDiffusion.centredSolution n Pe i :=
  AdvectionDiffusion.centredSolution_unique hPe hPe1 hn h0 hlast hrec hi

/-- **If `Pe > 1` the solution of (12.76) oscillates**: a power with a negative base appears in the
numerator, so the increments of the discrete solution alternate in sign.  For `Pe < 1` the discrete
solution is increasing, like the exact one. -/
theorem equation_12_76_oscillates {Pe : ℝ} (hPe : 1 < Pe) {n : ℕ} (hn : n ≠ 0) (i : ℕ) :
    0 < (-1) ^ i * (AdvectionDiffusion.centredSolution n Pe (i + 1)
        - AdvectionDiffusion.centredSolution n Pe i)
      * (AdvectionDiffusion.centredSolution n Pe 1 - AdvectionDiffusion.centredSolution n Pe 0) :=
  AdvectionDiffusion.centredSolution_oscillates hPe hn i

/-- The companion of `equation_12_76_oscillates`: for `Pe < 1` the discrete solution is strictly
increasing, which is the monotonicity the mesh refinement `Pe < 1` of §12.5.1 buys. -/
theorem equation_12_76_strictMono {Pe : ℝ} (hPe : 0 < Pe) (hPe1 : Pe < 1) {n : ℕ} (hn : n ≠ 0) :
    StrictMono (AdvectionDiffusion.centredSolution n Pe) :=
  AdvectionDiffusion.centredSolution_strictMono hPe hPe1 hn

/-! ### Finite differences and the numerical viscosity -/

/-- **(12.77), the centred finite difference scheme** `-ε (u_{i+1} - 2u_i + u_{i-1})/h² +
β (u_{i+1} - u_{i-1})/(2h) = 0` with `u_0 = 0`, `u_n = 1`: multiplied by `h` it is exactly the
equation (12.75) produced by the piecewise linear Galerkin method. -/
theorem equation_12_77 {ε β : ℝ} {n : ℕ} (hn : n ≠ 0) (u : ℕ → ℝ) :
    AdvectionDiffusion.viscosityScheme ε β n 0 u ↔ u 0 = 0 ∧ u n = 1 ∧ ∀ i, i + 2 ≤ n →
      ε / AdvectionDiffusion.meshWidth n * (-u i + 2 * u (i + 1) - u (i + 2))
        + β / 2 * (u (i + 2) - u i) = 0 :=
  AdvectionDiffusion.viscosityScheme_zero_iff hn u

/-- **(12.78)–(12.79), upwinding as artificial diffusion**: the upwind scheme
`-ε (u_{i+1} - 2u_i + u_{i-1})/h² + β (u_i - u_{i-1})/h = 0` (for `β > 0`) is the centred scheme
(12.79) with the viscosity `ε_h = ε (1 + Pe)`, by the identity
`(u_i - u_{i-1})/h = (u_{i+1} - u_{i-1})/(2h) - (h/2)(u_{i+1} - 2u_i + u_{i-1})/h²`. -/
theorem equation_12_79 {ε β : ℝ} {n : ℕ} (hε : ε ≠ 0) (hβ : 0 < β) (hn : n ≠ 0) (u : ℕ → ℝ) :
    AdvectionDiffusion.upwindScheme ε β n u
      ↔ AdvectionDiffusion.viscosityScheme ε β n AdvectionDiffusion.phiUpwind u :=
  AdvectionDiffusion.upwindScheme_iff_viscosityScheme hε hβ hn u

/-- **(12.81), the numerical viscosity**: the diffusion of the upwind scheme is
`ε_h = ε (1 + Pe) = ε + |β| h/2`, so the perturbation it introduces is `ε Pe u'' = (β h/2) u''`. -/
theorem equation_12_81 {ε : ℝ} (hε : ε ≠ 0) (β h : ℝ) :
    AdvectionDiffusion.viscosity ε β h AdvectionDiffusion.phiUpwind = ε + |β| * h / 2 :=
  AdvectionDiffusion.viscosity_phiUpwind hε β h

/-- For `ε = 0` the upwind scheme reduces to `u_i = u_{i-1}`, the constant solution of the limit
problem `β u' = 0` ([quarteroni2000numerical] §12.5.2). -/
theorem equation_12_78_zero_diffusion {β : ℝ} {n : ℕ} (hβ : β ≠ 0) (hn : n ≠ 0) {u : ℕ → ℝ}
    (hu : AdvectionDiffusion.upwindScheme 0 β n u) {i : ℕ} (hi : i + 2 ≤ n) :
    u (i + 1) = u i :=
  AdvectionDiffusion.upwindScheme_zero_diffusion hβ hn hu hi

/-- **The viscosity (12.82)** `ε_h = ε (1 + φ(Pe))` of the general centred scheme, for a function
`φ` of the local Péclet number with `φ(t) → 0` as `t → 0⁺`.  `φ = 0` is the centred scheme
(12.77), `φ^UP(t) = t` the upwind scheme (12.78), and `φ^SG` of (12.83) the exponential fitting
scheme. -/
noncomputable def equation_12_82 (ε β : ℝ) (n : ℕ) (φ : ℝ → ℝ) : ℝ :=
  AdvectionDiffusion.viscosity ε β (AdvectionDiffusion.meshWidth n) φ

/-- (12.82) is `ε (1 + φ(Pe))`. -/
theorem equation_12_82_eq (ε β : ℝ) (n : ℕ) (φ : ℝ → ℝ) :
    equation_12_82 ε β n φ
      = ε * (1 + φ (meshPeclet β (AdvectionDiffusion.meshWidth n) ε)) := rfl

/-- The centred scheme is the case `φ = 0` of (12.82). -/
theorem equation_12_82_zero (ε β : ℝ) (n : ℕ) : equation_12_82 ε β n 0 = ε :=
  AdvectionDiffusion.viscosity_zero ε β _

/-- **The Scharfetter–Gummel (exponential fitting) viscosity function (12.83)**,
`φ^SG(t) = t - 1 + B(2t)` with `B(t) = t/(e^t - 1)`, `B(0) = 1`, the Bernoulli function. -/
noncomputable def equation_12_83 (t : ℝ) : ℝ := AdvectionDiffusion.phiSG t

/-- (12.83) is `t - 1 + B(2t)`. -/
theorem equation_12_83_eq (t : ℝ) :
    equation_12_83 t = t - 1 + AdvectionDiffusion.bernoulliFn (2 * t) := rfl

/-- The Bernoulli function of (12.83) is `t/(e^t - 1)` away from the origin, and `1` at it. -/
theorem bernoulliFn_eq {t : ℝ} (ht : t ≠ 0) :
    AdvectionDiffusion.bernoulliFn t = t / (Real.exp t - 1) :=
  AdvectionDiffusion.bernoulliFn_of_ne_zero ht

/-- The identity `B(-t) = t + B(t)` that the hint of Exercise 12.13 uses. -/
theorem bernoulliFn_neg (t : ℝ) :
    AdvectionDiffusion.bernoulliFn (-t) = t + AdvectionDiffusion.bernoulliFn t :=
  AdvectionDiffusion.bernoulliFn_neg t

/-! ### Remark 12.6 -/

/-- **Remark 12.6, the asymptotics of `φ^SG`**: `φ^SG ≃ φ^UP` as `Pe → +∞` (their ratio tends to
`1`; their difference tends to `-1`), while `0 ≤ φ^SG(t) ≤ t²/3` near the origin, so
`φ^SG = O(h²)` where `φ^UP(Pe) = Pe = O(h)`.  This is why the Scharfetter–Gummel method is
second-order accurate. -/
theorem remark_12_6_asymptotics :
    Tendsto (fun t => AdvectionDiffusion.phiSG t / AdvectionDiffusion.phiUpwind t) atTop (𝓝 1) ∧
      ∀ t : ℝ, 0 ≤ t → 0 ≤ AdvectionDiffusion.phiSG t ∧ AdvectionDiffusion.phiSG t ≤ t ^ 2 / 3 :=
  ⟨AdvectionDiffusion.phiSG_div_phiUpwind_tendsto,
    fun _ ht => ⟨AdvectionDiffusion.phiSG_nonneg ht, AdvectionDiffusion.phiSG_le_sq ht⟩⟩

/-- **Remark 12.6, nodal exactness of the Scharfetter–Gummel scheme**: for the problem (12.70) its
solution agrees with the exact solution at every node `x_i = i h`, whatever the mesh size and hence
whatever the local Péclet number. -/
theorem remark_12_6_nodal_exact {ε β : ℝ} {n : ℕ} (hε : 0 < ε) (hβ : 0 < β) (hn : n ≠ 0)
    {u : ℕ → ℝ} (hu : AdvectionDiffusion.viscosityScheme ε β n AdvectionDiffusion.phiSG u)
    {i : ℕ} (hi : i ≤ n) :
    u i = AdvectionDiffusion.exactSolution ε β (i * AdvectionDiffusion.meshWidth n) :=
  AdvectionDiffusion.sg_nodal_exact hε hβ hn hu hi

/-! ### The stabilized Péclet number and the M-matrix property -/

/-- **`Pe* < 1` for the upwind and the Scharfetter–Gummel schemes, for every mesh size**
(§12.5.2): the stabilized local Péclet number `Pe* = |β| h/(2 ε_h) = Pe/(1 + φ(Pe))` is
`Pe/(1 + Pe)` for the upwind viscosity and `tanh Pe` for the Scharfetter–Gummel one. -/
theorem stabilizedPeclet_lt_one {Pe : ℝ} (hPe : 0 < Pe) :
    AdvectionDiffusion.stabilizedPeclet AdvectionDiffusion.phiUpwind Pe = Pe / (1 + Pe) ∧
      AdvectionDiffusion.stabilizedPeclet AdvectionDiffusion.phiUpwind Pe < 1 ∧
      AdvectionDiffusion.stabilizedPeclet AdvectionDiffusion.phiSG Pe = Real.tanh Pe ∧
      AdvectionDiffusion.stabilizedPeclet AdvectionDiffusion.phiSG Pe < 1 :=
  ⟨AdvectionDiffusion.stabilizedPeclet_phiUpwind Pe,
    AdvectionDiffusion.stabilizedPeclet_phiUpwind_lt_one hPe,
    AdvectionDiffusion.stabilizedPeclet_phiSG_eq_tanh hPe,
    AdvectionDiffusion.stabilizedPeclet_phiSG_lt_one hPe⟩

/-- **Exercise 12.13**: the matrix `(ε_h/h²) tridiag(-(1 + Pe*), 2, -(1 - Pe*))` of the stabilized
scheme (12.79) is an M-matrix whenever `|Pe*| ≤ 1` — which `stabilizedPeclet_lt_one` gives for the
upwind and Scharfetter–Gummel viscosities at every mesh size — so the discrete solution satisfies
the maximum principle `A u ≥ 0 ⇒ u ≥ 0` of §12.2.2. -/
theorem exercise_12_13 {ε β : ℝ} {n : ℕ} {φ : ℝ → ℝ} (m : ℕ)
    (hεh : 0 < AdvectionDiffusion.viscosity ε β (AdvectionDiffusion.meshWidth n) φ) (hn : n ≠ 0)
    (hPe : |AdvectionDiffusion.stabilizedPeclet φ
      (meshPeclet β (AdvectionDiffusion.meshWidth n) ε)| ≤ 1) :
    ((AdvectionDiffusion.viscosity ε β (AdvectionDiffusion.meshWidth n) φ
          / AdvectionDiffusion.meshWidth n ^ 2) •
        Matrix.tridiagonalToeplitz m
          (-(1 + AdvectionDiffusion.stabilizedPeclet φ
            (meshPeclet β (AdvectionDiffusion.meshWidth n) ε))) 2
          (-(1 - AdvectionDiffusion.stabilizedPeclet φ
            (meshPeclet β (AdvectionDiffusion.meshWidth n) ε)))).IsMMatrix :=
  AdvectionDiffusion.viscosityScheme_isMMatrix m hεh hn hPe

/-- The discrete maximum principle that Exercise 12.13 is invoked for: an M-matrix `A` with
`A u ≥ 0` entrywise has `u ≥ 0` entrywise. -/
theorem exercise_12_13_maximumPrinciple {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsMMatrix)
    {x : Fin m → ℝ} (hx : 0 ≤ A.mulVec x) : 0 ≤ x :=
  hA.nonneg_of_mulVec_nonneg hx

/-! ### The stabilized finite element method (12.84) -/

/-- **The stabilized bilinear form (12.84)** `a_h(u, v) = a(u, v) + b(u, v)` with the
stabilization term `b(u, v) = ε φ(Pe) ∫₀¹ u' v'`: the elliptic form of §12.4 with the viscosity
`ε_h = ε (1 + φ(Pe))` of (12.82) in place of `ε`.  The stabilized problem of (12.84) — find
`u_h⁰ ∈ X_h^{k,0}` with `a_h(u_h⁰, v_h) = -∫₀¹ β v_h` for all `v_h ∈ X_h^{k,0}` — is
`IsGalerkinSolution (equation_12_84 ε β h φ) ℓ K` for the trial space `K` and the right-hand side
`ℓ` obtained after the lifting `ů = u - x`; the Lagrange space `X_h^{k,0}` itself is
`FiniteElement.lagrangeSpaceZero`, which this module does not yet have. -/
noncomputable def equation_12_84 (ε β h : ℝ) (φ : ℝ → ℝ) : SesqForm ℝ (SobolevInterval 1 0 1) :=
  AdvectionDiffusion.stabilizedForm 0 1 ε β h φ

/-- **The energy identity behind (12.84)**, `a_h(v, v) = ε_h |v|²_{H¹(0,1)}` for
`v ∈ H¹₀(0, 1)`: with `ε_h/ε = 1 + φ(Pe) ≥ 1` it is what gives the stabilized problem its more
favourable monotonicity. -/
theorem equation_12_84_self {ε β h : ℝ} (φ : ℝ → ℝ) {v : SobolevInterval 1 0 1}
    (hv : v ∈ SobolevIntervalZero 0 1) :
    equation_12_84 ε β h φ v v
      = AdvectionDiffusion.viscosity ε β h φ * SobolevInterval.seminorm 1 0 1 v ^ 2 :=
  AdvectionDiffusion.stabilizedForm_self one_pos φ hv

/-- The stabilization term of (12.84) is `b(u, v) = ε φ(Pe) ∫₀¹ u' v'`, the difference between the
stabilized form and the Galerkin form (12.73). -/
theorem equation_12_84_sub (ε β h : ℝ) (φ : ℝ → ℝ) (u v : SobolevInterval 1 0 1) :
    equation_12_84 ε β h φ u v
        - EllipticInterval.form 0 1 (AdvectionDiffusion.constLinf 0 1 ε)
          (AdvectionDiffusion.constLinf 0 1 β) 0 u v
      = ε * φ (meshPeclet β h ε)
        * ⟪SobolevInterval.deriv u 1, SobolevInterval.deriv v 1⟫_ℝ :=
  AdvectionDiffusion.stabilizedForm_sub_form 0 1 ε β h φ u v

end QuarteroniSaccoSaleri.Chapter12

import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Numlib.Variational.EllipticInterval
import Numlib.Variational.FiniteElementInterval

/-!
# Quarteroni–Sacco–Saleri §12.4: the Galerkin method

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §12.4.

The two-point boundary value problem `-(α u')' + β u' + γ u = f` on `(0, 1)` with
`u(0) = u(1) = 0` (12.41) is multiplied by a test function and integrated by parts: a classical
solution `u ∈ C²([0, 1])` satisfies the *weak formulation* (12.43), `a(u, v) = (f, v)` for every
`v` in `V = H^1_0(0, 1)` (12.42), with the bilinear form (12.44). The *Galerkin method* (12.46)
poses the same equation in a finite-dimensional subspace `V_h ≤ V`; in a basis of `V_h` it is the
linear system (12.47)–(12.48) with the stiffness matrix `(A_G)_{ij} = a(φ_j, φ_i)`. §12.4.4
analyses it in the `H¹` seminorm (12.49): coercivity under `β = 0`, `γ ≥ 0` or under (12.50)
gives the stability (12.51) and Theorem 12.3, `|u - u_h| ≤ C min_{w_h} |u - w_h|` with
`C = α₀⁻¹(‖α‖_∞ + C_P² ‖γ‖_∞)`, of which the Lax–Milgram lemma (12.54)–(12.55) and Céa's lemma
(12.56) are the abstract Hilbert-space form; and `A_G` is positive definite, symmetric when the
form is.

## What is here and what is not

The nodes of §12.4.1–12.4.4, the finite element space (12.57) and Example 12.1 are proved. The
rest of §12.4.5–12.4.6 — the interpolation estimate (12.58), Property 12.1, the shape functions
(12.61)–(12.66) and the structure of `A_fe` — waits on the hat-function part of
`Numlib/Variational/FiniteElementInterval.lean`, which is not yet written; so does the spectral
Galerkin method (12.68)–(12.69), which additionally needs §12.3. §12.4.2's distributions are
Mathlib's `Distribution` on `Opens.Ioo 0 1` and are likewise not restated here.

## Conventions

`H^1(0, 1)` is `SobolevInterval 1 0 1` and `H^1_0(0, 1)` is `SobolevIntervalZero 0 1`
(`Numlib/Analysis/Sobolev/Interval.lean`); the coefficients `α, β, γ` are `L^∞(0, 1)` elements
and the datum `f` an `L²(0, 1)` element, so that the form and the load functional are the
bounded `EllipticInterval.form 0 1 α β γ` and `EllipticInterval.load 0 1 f`
(`Numlib/Variational/EllipticInterval.lean`). The Poincaré constant on `(0, 1)` is
`C_P = 1/√2`.

## Main definitions

* `equation_12_42` — `V = H^1_0(0, 1)`.
* `equation_12_44` — the bilinear form `a(u, v)`.
* `equation_12_46` — the Galerkin problem in a subspace `V_h`.
* `equation_12_48_matrix` — the stiffness matrix `A_G` in a basis of `V_h`.
* `equation_12_49` — the `H¹` seminorm `|·|_{H¹(0,1)}`.
* `equation_12_57` — the finite element space `V_h = X_h^{k,0}`.
* `example_12_1_solution` — `u(x) = u₀ cosh(m(L - x))/cosh(mL)` of (12.67).

## Main results

* `equation_12_43`, `equation_12_43_lift`, `equation_12_43_neumann`, `exercise_12_12` — classical
  solutions are weak solutions, with the Dirichlet lifting and the Neumann and mixed cases.
* `equation_12_48` — the Galerkin problem is the linear system `A_G u = f_G`.
* `equation_12_50`, `equation_12_50_of_le`, `equation_12_50_existsUnique` — coercivity and unique
  solvability.
* `equation_12_51` — the stability estimate `|u_h|_{H¹} ≤ (C_P/α₀) ‖f‖_{L²}`.
* `equation_12_53`, `theorem_12_3` — Galerkin orthogonality and Theorem 12.3.
* `laxMilgram_lemma`, `laxMilgram_lemma_bound`, `laxMilgram_lemma_galerkin`, `equation_12_56` —
  Lax–Milgram and Céa in an abstract Hilbert space.
* `galerkinMatrix_posDef`, `galerkinMatrix_isSymm` — the stiffness matrix.
* `example_12_1` — the exact solution of (12.67).
-/

open Set Matrix MeasureTheory SobolevInterval EllipticInterval

namespace QuarteroniSaccoSaleri.Chapter12

/-! ### The weak formulation (12.41)–(12.44) -/

/-- **The space `V = H^1_0(0, 1)`** of [quarteroni2000numerical] (12.42): the elements of
`L²(0, 1)` whose distributional derivative lies in `L²(0, 1)` and which vanish at both ends. -/
noncomputable abbrev equation_12_42 : Submodule ℝ (SobolevInterval 1 0 1) :=
  SobolevIntervalZero 0 1

/-- **(12.42) is the boundary description**: an element of `H^1(0, 1)` lies in `H^1_0(0, 1)`
exactly when its continuous representative vanishes at `0` and at `1`. -/
theorem equation_12_42_iff (u : SobolevInterval 1 0 1) :
    u ∈ equation_12_42 ↔ toContinuousMap zero_lt_one u ⟨0, left_mem_Icc.2 zero_le_one⟩ = 0 ∧
      toContinuousMap zero_lt_one u ⟨1, right_mem_Icc.2 zero_le_one⟩ = 0 :=
  mem_sobolevIntervalZero_iff zero_lt_one u

/-- **The bilinear form (12.44)**, `a(u, v) = ∫₀¹ α u' v' + ∫₀¹ β u' v + ∫₀¹ γ u v`, on
`H^1(0, 1)`. -/
noncomputable abbrev equation_12_44 (α β γ : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))) :
    SesqForm ℝ (SobolevInterval 1 0 1) :=
  EllipticInterval.form 0 1 α β γ

theorem equation_12_44_apply (α β γ : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1)))
    (u v : SobolevInterval 1 0 1) :
    equation_12_44 α β γ u v = ∫ x in Ioo (0 : ℝ) 1,
      (α x * deriv u 1 x * deriv v 1 x + β x * deriv u 1 x * deriv v 0 x
        + γ x * deriv u 0 x * deriv v 0 x) :=
  EllipticInterval.form_apply α β γ u v

/-- **The `L²` product `(f, v) = ∫₀¹ f v`** of the right-hand side of (12.43). -/
theorem load_apply (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) (v : SobolevInterval 1 0 1) :
    EllipticInterval.load 0 1 f v = ∫ x in Ioo (0 : ℝ) 1, f x * deriv v 0 x :=
  EllipticInterval.load_apply f v

/-- **The weak formulation (12.43)**: a classical solution `u ∈ C²([0, 1])` of (12.41) with
`u(0) = u(1) = 0` lies in `V = H^1_0(0, 1)` and satisfies `a(u, v) = (f, v)` for every `v ∈ V`. -/
theorem equation_12_43 {α β γ f : ℝ → ℝ}
    (αL βL γL : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1)))
    (fL : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hαL : αL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] α)
    (hβL : βL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] β)
    (hγL : γL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] γ)
    (hfL : fL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] f)
    (hα : ContDiffOn ℝ 1 α (Icc 0 1)) (hβ : ContinuousOn β (Icc 0 1))
    (hγ : ContinuousOn γ (Icc 0 1)) (u : ContDiffMapIcc zero_le_one 2)
    (hode : ∀ x ∈ Ioo (0 : ℝ) 1, -deriv (fun t ↦ α t * u.shift.extend t) x
      + β x * u.shift.extend x + γ x * u.extend x = f x)
    (hua : u.extend 0 = 0) (hub : u.extend 1 = 0) :
    IsGalerkinSolution (equation_12_44 αL βL γL) (EllipticInterval.load 0 1 fL) equation_12_42
      (EllipticInterval.ofContDiffMapIcc zero_lt_one u) :=
  EllipticInterval.isWeakSolution_of_classical zero_lt_one αL βL γL fL hαL hβL hγL hfL hα hβ hγ
    u hode hua hub

/-- **The nonhomogeneous Dirichlet lifting** of §12.4.1: if `u(0) = u₀` and `u(1) = u₁`, then
with any lifting `W` of the boundary values `ů = u - W ∈ V` satisfies
`a(ů, v) = (f, v) - a(W, v)` for all `v ∈ V`. The book takes `W(x) = x u₁ + (1 - x) u₀`. -/
theorem equation_12_43_lift (α β γ : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1)))
    (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) {U : SobolevInterval 1 0 1}
    (hU : ∀ v ∈ equation_12_42, equation_12_44 α β γ U v = EllipticInterval.load 0 1 f v)
    (W : SobolevInterval 1 0 1) {v : SobolevInterval 1 0 1} (hv : v ∈ equation_12_42) :
    equation_12_44 α β γ (U - W) v
      = EllipticInterval.load 0 1 f v - equation_12_44 α β γ W v :=
  EllipticInterval.form_sub_eq_of_forall α β γ f hU W hv

/-- **The Neumann problem** of §12.4.1: for the homogeneous Neumann conditions
`α u'(0) = α u'(1) = 0` the same weak formulation (12.43) holds with `V = H^1(0, 1)`. -/
theorem equation_12_43_neumann {α β γ f : ℝ → ℝ}
    (αL βL γL : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1)))
    (fL : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hαL : αL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] α)
    (hβL : βL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] β)
    (hγL : γL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] γ)
    (hfL : fL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] f)
    (hα : ContDiffOn ℝ 1 α (Icc 0 1)) (hβ : ContinuousOn β (Icc 0 1))
    (hγ : ContinuousOn γ (Icc 0 1)) (u : ContDiffMapIcc zero_le_one 2)
    (hode : ∀ x ∈ Ioo (0 : ℝ) 1, -deriv (fun t ↦ α t * u.shift.extend t) x
      + β x * u.shift.extend x + γ x * u.extend x = f x)
    (hw₀ : α 0 * u.shift.extend 0 = 0) (hw₁ : α 1 * u.shift.extend 1 = 0)
    (v : SobolevInterval 1 0 1) :
    equation_12_44 αL βL γL (EllipticInterval.ofContDiffMapIcc zero_lt_one u) v
      = EllipticInterval.load 0 1 fL v := by
  have h := EllipticInterval.isWeakSolution_of_classical_neumann zero_lt_one αL βL γL fL hαL hβL
    hγL hfL hα hβ hγ u hode hw₀ hw₁ v
  simpa using h

/-- **Exercise 12.12**, cited at the end of §12.4.1: with the nonhomogeneous Neumann conditions
`α u'(0) = w₀`, `α u'(1) = w₁`, the classical solution satisfies (12.43) on `V = H^1(0, 1)` with
the right-hand side `(f, v) + w₁ v(1) - w₀ v(0)`. The mixed case `α u'(0) = w₀`, `u(1) = u₁` is
this identity tested against the `v` with `v(1) = 0`, after lifting `u₁`. -/
theorem exercise_12_12 {α β γ f : ℝ → ℝ}
    (αL βL γL : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1)))
    (fL : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hαL : αL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] α)
    (hβL : βL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] β)
    (hγL : γL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] γ)
    (hfL : fL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] f)
    (hα : ContDiffOn ℝ 1 α (Icc 0 1)) (hβ : ContinuousOn β (Icc 0 1))
    (hγ : ContinuousOn γ (Icc 0 1)) (u : ContDiffMapIcc zero_le_one 2)
    (hode : ∀ x ∈ Ioo (0 : ℝ) 1, -deriv (fun t ↦ α t * u.shift.extend t) x
      + β x * u.shift.extend x + γ x * u.extend x = f x)
    {w₀ w₁ : ℝ} (hw₀ : α 0 * u.shift.extend 0 = w₀) (hw₁ : α 1 * u.shift.extend 1 = w₁)
    (v : SobolevInterval 1 0 1) :
    equation_12_44 αL βL γL (EllipticInterval.ofContDiffMapIcc zero_lt_one u) v
      = EllipticInterval.load 0 1 fL v + w₁ * rep v 1 - w₀ * rep v 0 :=
  EllipticInterval.isWeakSolution_of_classical_neumann zero_lt_one αL βL γL fL hαL hβL hγL hfL
    hα hβ hγ u hode hw₀ hw₁ v

/-! ### The Galerkin method (12.46)–(12.48) -/

/-- **The Galerkin problem (12.46)**: `u_h ∈ V_h` with `a(u_h, v_h) = (f, v_h)` for all
`v_h ∈ V_h`, for a subspace `V_h` of `V`. -/
abbrev equation_12_46 (α β γ : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1)))
    (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (Vh : Submodule ℝ (SobolevInterval 1 0 1)) (uh : SobolevInterval 1 0 1) : Prop :=
  IsGalerkinSolution (equation_12_44 α β γ) (EllipticInterval.load 0 1 f) Vh uh

/-- **The stiffness matrix** `A_G` of (12.48), `(A_G)_{ij} = a(φ_j, φ_i)` in a basis
`φ_1, …, φ_N` of `V_h`. -/
noncomputable def equation_12_48_matrix {ι : Type*} (α β γ : Lp ℝ ⊤ (volume.restrict
    (Ioo (0 : ℝ) 1))) (φ : ι → SobolevInterval 1 0 1) : Matrix ι ι ℝ :=
  (equation_12_44 α β γ).gramMatrix φ

/-- **(12.47)–(12.48)**: with a basis `φ` of `V_h`, `u_h = ∑ u_j φ_j` solves the Galerkin problem
exactly when the coefficients solve the linear system `A_G u = f_G`, `(f_G)_i = (f, φ_i)`. -/
theorem equation_12_48 {ι : Type*} [Fintype ι] (α β γ : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1)))
    (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    {Vh : Submodule ℝ (SobolevInterval 1 0 1)} (φ : Module.Basis ι ℝ Vh) (ξ : ι → ℝ) :
    equation_12_46 α β γ f Vh (∑ j, ξ j • (φ j : SobolevInterval 1 0 1)) ↔
      equation_12_48_matrix α β γ (fun i ↦ (φ i : SobolevInterval 1 0 1)) *ᵥ ξ
        = fun i ↦ EllipticInterval.load 0 1 f (φ i) := by
  have h := IsGalerkinSolution.iff_gramMatrix_mulVec (a := equation_12_44 α β γ)
    (ℓ := EllipticInterval.load 0 1 f) φ ξ
  simpa [equation_12_46, equation_12_48_matrix] using h

/-! ### Analysis of the Galerkin method (§12.4.4) -/

/-- **The norm (12.49)** on `H^1_0(0, 1)`, `|v|_{H¹(0,1)} = (∫₀¹ |v'|²)^{1/2}`. -/
noncomputable abbrev equation_12_49 : Seminorm ℝ (SobolevInterval 1 0 1) :=
  SobolevInterval.seminorm 1 0 1

theorem equation_12_49_apply (v : SobolevInterval 1 0 1) : equation_12_49 v = ‖deriv v 1‖ := rfl

/-- **Coercivity, the case `β = 0`, `γ ≥ 0`** of §12.4.4: `α₀ |v|²_{H¹} ≤ a(v, v)`. -/
theorem equation_12_50 (α γ : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))) {α₀ : ℝ}
    (hα : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), α₀ ≤ α x)
    (hγ : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), 0 ≤ γ x) (v : SobolevInterval 1 0 1) :
    α₀ * equation_12_49 v ^ 2 ≤ equation_12_44 α 0 γ v v :=
  EllipticInterval.form_isCoerciveWith_seminorm α γ hα hγ v

/-- **Coercivity under (12.50)**, `-β'/2 + γ ≥ 0` on `[0, 1]`: the same bound on `H^1_0(0, 1)`
for a form with a nonvanishing advection coefficient. -/
theorem equation_12_50_of_le (αL βL γL : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))) {α₀ : ℝ}
    (hα : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), α₀ ≤ αL x) {β : ℝ → ℝ}
    (hβL : βL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] β) (hβ : ContDiffOn ℝ 1 β (Icc 0 1))
    (hcond : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), deriv β x / 2 ≤ γL x)
    {v : SobolevInterval 1 0 1} (hv : v ∈ equation_12_42) :
    α₀ * equation_12_49 v ^ 2 ≤ equation_12_44 αL βL γL v v :=
  EllipticInterval.form_isCoerciveWith_seminorm_of_le zero_lt_one αL βL γL hα hβL hβ hcond hv

/-- **Unique solvability of the weak problem**, the consequence of coercivity stated after
(12.50): for `α ≥ α₀ > 0` and `γ ≥ 0` there is exactly one weak solution in `V = H^1_0(0, 1)`. -/
theorem equation_12_50_existsUnique (α γ : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))) {α₀ : ℝ}
    (hα₀ : 0 < α₀) (hα : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), α₀ ≤ α x)
    (hγ : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), 0 ≤ γ x)
    (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    ∃! u, equation_12_46 α 0 γ f equation_12_42 u :=
  EllipticInterval.existsUnique_isWeakSolution zero_lt_one α γ hα₀ hα hγ f

/-- **The stability estimate (12.51)**: the Galerkin solution in any subspace `V_h ≤ V` satisfies
`|u_h|_{H¹(0,1)} ≤ (C_P/α₀) ‖f‖_{L²(0,1)}` with `C_P = 1/√2`, uniformly in `V_h`. -/
theorem equation_12_51 (α γ : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))) {α₀ : ℝ} (hα₀ : 0 < α₀)
    (hα : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), α₀ ≤ α x)
    (hγ : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), 0 ≤ γ x)
    (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    {Vh : Submodule ℝ (SobolevInterval 1 0 1)} (hVh : Vh ≤ equation_12_42)
    {uh : SobolevInterval 1 0 1} (huh : equation_12_46 α 0 γ f Vh uh) :
    equation_12_49 uh ≤ 1 / Real.sqrt 2 / α₀ * ‖f‖ := by
  have h := EllipticInterval.seminorm_le_of_isGalerkinSolution zero_lt_one α γ hα₀ hα hγ f hVh huh
  simpa using h

/-- **Galerkin orthogonality (12.53)**: `a(u - u_h, v_h) = 0` for every `v_h ∈ V_h`. -/
theorem equation_12_53 (α β γ : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1)))
    (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    {Vh : Submodule ℝ (SobolevInterval 1 0 1)} {u uh : SobolevInterval 1 0 1}
    (hu : ∀ v, equation_12_44 α β γ u v = EllipticInterval.load 0 1 f v)
    (huh : equation_12_46 α β γ f Vh uh) {v : SobolevInterval 1 0 1} (hv : v ∈ Vh) :
    equation_12_44 α β γ (u - uh) v = 0 :=
  IsGalerkinSolution.apply_sub_eq_zero huh hu hv

/-- **Theorem 12.3**: for `β = 0` and `γ ≥ 0`, with `C = α₀⁻¹(‖α‖_∞ + C_P² ‖γ‖_∞)` and
`C_P = 1/√2`, the Galerkin error satisfies `|u - u_h|_{H¹(0,1)} ≤ C |u - w_h|_{H¹(0,1)}` for
every `w_h ∈ V_h`, hence `≤ C min_{w_h ∈ V_h} |u - w_h|_{H¹(0,1)}` (12.52). -/
theorem theorem_12_3 (α γ : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))) {α₀ : ℝ} (hα₀ : 0 < α₀)
    (hα : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), α₀ ≤ α x)
    (hγ : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), 0 ≤ γ x)
    (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    {Vh : Submodule ℝ (SobolevInterval 1 0 1)} (hVh : Vh ≤ equation_12_42)
    {u uh : SobolevInterval 1 0 1} (hu : equation_12_46 α 0 γ f equation_12_42 u)
    (huh : equation_12_46 α 0 γ f Vh uh) {w : SobolevInterval 1 0 1} (hw : w ∈ Vh) :
    equation_12_49 (u - uh)
      ≤ α₀⁻¹ * (‖α‖ + (1 / Real.sqrt 2) ^ 2 * ‖γ‖) * equation_12_49 (u - w) := by
  have h := EllipticInterval.galerkin_seminorm_sub_le zero_lt_one α γ hα₀ hα hγ f hVh hu huh hw
  simpa using h

/-! ### Lax–Milgram and Céa in a Hilbert space (12.54)–(12.56) -/

section Abstract

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {a : SesqForm ℝ V} {ℓ : V →L[ℝ] ℝ}

/-- **The Lax–Milgram lemma** ([quarteroni2000numerical] §12.4.4, (12.54)–(12.55)): a bilinear
form on a Hilbert space that is coercive, `a(v, v) ≥ α₀ ‖v‖²` with `α₀ > 0`, makes the problem
`a(u, v) = (f, v)` for all `v ∈ V` uniquely solvable. -/
theorem laxMilgram_lemma {α₀ : ℝ} (hα₀ : 0 < α₀) (hcoer : a.IsCoerciveWith α₀) :
    ∃! u, ∀ v, a u v = ℓ v :=
  SesqForm.laxMilgram a ℓ hα₀ hcoer

omit [CompleteSpace V] in
/-- **The stability bound of Lax–Milgram**: `‖u‖_V ≤ K/α₀` whenever `|(f, v)| ≤ K ‖v‖_V`. -/
theorem laxMilgram_lemma_bound {α₀ K : ℝ} (hα₀ : 0 < α₀) (hcoer : a.IsCoerciveWith α₀)
    (hK : ‖ℓ‖ ≤ K) {u : V} (hu : ∀ v, a u v = ℓ v) : ‖u‖ ≤ K / α₀ :=
  (SesqForm.norm_le_of_forall_apply_eq a ℓ hα₀ hcoer hu).trans (by gcongr)

omit [CompleteSpace V] in
/-- **Lax–Milgram for the Galerkin problem**: the same form has exactly one Galerkin solution in
any complete subspace `V_h`, with the same bound `‖u_h‖_V ≤ K/α₀`. -/
theorem laxMilgram_lemma_galerkin {α₀ : ℝ} (hα₀ : 0 < α₀) (hcoer : a.IsCoerciveWith α₀)
    (Vh : Submodule ℝ V) [CompleteSpace Vh] : ∃! uh, IsGalerkinSolution a ℓ Vh uh :=
  IsGalerkinSolution.existsUnique hα₀ hcoer

omit [CompleteSpace V] in
theorem laxMilgram_lemma_galerkin_bound {α₀ K : ℝ} (hα₀ : 0 < α₀) (hcoer : a.IsCoerciveWith α₀)
    (hK : ‖ℓ‖ ≤ K) {Vh : Submodule ℝ V} {uh : V} (huh : IsGalerkinSolution a ℓ Vh uh) :
    ‖uh‖ ≤ K / α₀ := by
  have h1 : α₀ * ‖uh‖ ^ 2 ≤ RCLike.re (a uh uh) := hcoer uh
  rw [huh.2 uh huh.1] at h1
  have h2 : RCLike.re (ℓ uh) ≤ ‖ℓ‖ * ‖uh‖ := by
    simpa using (RCLike.re_le_norm (ℓ uh)).trans (ℓ.le_opNorm uh)
  have h3 : α₀ * ‖uh‖ ^ 2 ≤ K * ‖uh‖ :=
    h1.trans (h2.trans (mul_le_mul_of_nonneg_right hK (norm_nonneg uh)))
  have hK0 : 0 ≤ K := (norm_nonneg ℓ).trans hK
  rcases eq_or_lt_of_le (norm_nonneg uh) with h | h
  · rw [← h]
    positivity
  · rw [le_div_iff₀ hα₀]
    nlinarith

omit [CompleteSpace V] in
/-- **Céa's lemma (12.56)**: `‖u - u_h‖_V ≤ (M/α₀) ‖u - w_h‖_V` for every `w_h ∈ V_h`, and hence
`≤ (M/α₀) min_{w_h ∈ V_h} ‖u - w_h‖_V`. -/
theorem equation_12_56 {α₀ M : ℝ} (hα₀ : 0 < α₀) (hM : a.IsBoundedWith M)
    (hcoer : a.IsCoerciveWith α₀) {Vh : Submodule ℝ V} {u uh : V}
    (huh : IsGalerkinSolution a ℓ Vh uh) (hu : ∀ v, a u v = ℓ v) {w : V} (hw : w ∈ Vh) :
    ‖u - uh‖ ≤ M / α₀ * ‖u - w‖ :=
  IsGalerkinSolution.norm_sub_le hα₀ hM hcoer huh hu hw

omit [CompleteSpace V] in
/-- **Céa's lemma (12.56) with the infimum**. -/
theorem equation_12_56_infDist {α₀ M : ℝ} (hα₀ : 0 < α₀) (hM : a.IsBoundedWith M)
    (hcoer : a.IsCoerciveWith α₀) {Vh : Submodule ℝ V} {u uh : V}
    (huh : IsGalerkinSolution a ℓ Vh uh) (hu : ∀ v, a u v = ℓ v) :
    ‖u - uh‖ ≤ M / α₀ * Metric.infDist u (Vh : Set V) :=
  IsGalerkinSolution.norm_sub_le_infDist hα₀ hM hcoer huh hu

end Abstract

/-- **The stiffness matrix is positive definite** (§12.4.4, the closing paragraph): under the
coercivity (12.54) and symmetry of the form, `A_G` is positive definite, because
`vᵀ A_G v = a(v_h, v_h) ≥ α₀ ‖v_h‖² > 0` for `v ≠ 0`. For (12.41) with `β = γ = 0` the form is
symmetric, so `A_G` is symmetric positive definite. -/
theorem galerkinMatrix_posDef {ι : Type*} [Finite ι] {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] {a : SesqForm ℝ V} {α₀ : ℝ} (hα₀ : 0 < α₀)
    (hsymm : a.IsHermitian) (hcoer : a.IsCoerciveWith α₀) {φ : ι → V}
    (hφ : LinearIndependent ℝ φ) : (a.gramMatrix φ).PosDef := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  exact SesqForm.gramMatrix_posDef hα₀ hsymm hcoer hφ

/-- **The stiffness matrix is symmetric when the form is** (§12.4.4). -/
theorem galerkinMatrix_isSymm {ι : Type*} {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {a : SesqForm ℝ V} (hsymm : a.IsHermitian) (φ : ι → V) :
    (a.gramMatrix φ).IsHermitian :=
  a.gramMatrix_isHermitian hsymm φ

/-! ### The finite element space (12.57) -/

/-- **The finite element space (12.57)** `V_h = X_h^{k,0} = {v_h ∈ X_h^k : v_h(0) = v_h(1) = 0}`
on a partition `0 = x_0 < ⋯ < x_n = 1` of `[0, 1]`, a subspace of `V = H^1_0(0, 1)`. -/
noncomputable def equation_12_57 (n : ℕ) (x : ℕ → ℝ) (k : ℕ) :
    Submodule ℝ (SobolevInterval 1 0 1) :=
  FiniteElement.lagrangeSpaceZero zero_lt_one n x k

theorem equation_12_57_le (n : ℕ) (x : ℕ → ℝ) (k : ℕ) : equation_12_57 n x k ≤ equation_12_42 :=
  FiniteElement.lagrangeSpaceZero_le_sobolevIntervalZero zero_lt_one n x k

/-- The dimension of `X_h^k` on `n` panels is `n k + 1` — the `n k + 1` nodal values of a
continuous piecewise polynomial of degree `k`. The book's `dim V_h = n k - 1` for `X_h^{k,0}` is
this minus the two endpoint values. -/
theorem equation_12_57_finrank {n : ℕ} {x : ℕ → ℝ} (hx : Spline.IsPartition 0 1 n x)
    (hn : 1 ≤ n) (k : ℕ) :
    Module.finrank ℝ (FiniteElement.lagrangeSpace zero_lt_one n x k) = n * k + 1 :=
  FiniteElement.finrank_lagrangeSpace zero_lt_one hx hn k

/-! ### Example 12.1 -/

/-- **The exact solution of (12.67)**, `u(x) = u₀ cosh(m (L - x)) / cosh(m L)`. -/
noncomputable def example_12_1_solution (L u₀ m : ℝ) : ℝ → ℝ :=
  fun x ↦ u₀ * Real.cosh (m * (L - x)) / Real.cosh (m * L)

theorem hasDerivAt_example_12_1_solution (L u₀ m x : ℝ) :
    HasDerivAt (example_12_1_solution L u₀ m)
      (-(u₀ * m * Real.sinh (m * (L - x))) / Real.cosh (m * L)) x := by
  have h1 : HasDerivAt (fun t : ℝ ↦ m * (L - t)) (-m) x := by
    simpa using ((hasDerivAt_const x L).sub (hasDerivAt_id x)).const_mul m
  have h2 : HasDerivAt (fun t : ℝ ↦ Real.cosh (m * (L - t)))
      (Real.sinh (m * (L - x)) * (-m)) x := h1.cosh
  exact ((h2.const_mul u₀).div_const (Real.cosh (m * L))).congr_deriv (by ring)

theorem deriv_example_12_1_solution (L u₀ m : ℝ) :
    deriv (example_12_1_solution L u₀ m)
      = fun x ↦ -(u₀ * m * Real.sinh (m * (L - x))) / Real.cosh (m * L) :=
  funext fun x ↦ (hasDerivAt_example_12_1_solution L u₀ m x).deriv

theorem iteratedDeriv_two_example_12_1_solution (L u₀ m x : ℝ) :
    iteratedDeriv 2 (example_12_1_solution L u₀ m) x
      = m ^ 2 * example_12_1_solution L u₀ m x := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one,
    deriv_example_12_1_solution]
  have h1 : HasDerivAt (fun t : ℝ ↦ m * (L - t)) (-m) x := by
    simpa using ((hasDerivAt_const x L).sub (hasDerivAt_id x)).const_mul m
  have h2 : HasDerivAt (fun t : ℝ ↦ Real.sinh (m * (L - t)))
      (Real.cosh (m * (L - x)) * (-m)) x := h1.sinh
  have h3 : HasDerivAt (fun t : ℝ ↦ -(u₀ * m * Real.sinh (m * (L - t))) / Real.cosh (m * L))
      (m ^ 2 * example_12_1_solution L u₀ m x) x := by
    refine (((h2.const_mul (u₀ * m)).neg).div_const (Real.cosh (m * L))).congr_deriv ?_
    rw [example_12_1_solution]
    field_simp
  exact h3.deriv

/-- The left boundary condition of (12.67): `u(0) = u₀`. -/
@[simp]
theorem example_12_1_solution_zero (L u₀ m : ℝ) : example_12_1_solution L u₀ m 0 = u₀ := by
  rw [example_12_1_solution, sub_zero, mul_div_assoc, div_self (Real.cosh_pos _).ne', mul_one]

/-- The right boundary condition of (12.67): `u'(L) = 0`. -/
@[simp]
theorem deriv_example_12_1_solution_apply (L u₀ m : ℝ) :
    deriv (example_12_1_solution L u₀ m) L = 0 := by
  rw [deriv_example_12_1_solution]
  simp

/-- **Example 12.1**: `u(x) = u₀ cosh(m (L - x)) / cosh(m L)` with `m² = σ p / (μ A)` solves
`-μ A u'' + σ p u = 0` on `(0, L)` with `u(0) = u₀` and `u'(L) = 0` (12.67). -/
theorem example_12_1 {mu A sigma p L u₀ m : ℝ} (hm : mu * A * m ^ 2 = sigma * p) :
    (∀ x : ℝ, -(mu * A) * iteratedDeriv 2 (example_12_1_solution L u₀ m) x
        + sigma * p * example_12_1_solution L u₀ m x = 0) ∧
      example_12_1_solution L u₀ m 0 = u₀ ∧ deriv (example_12_1_solution L u₀ m) L = 0 := by
  refine ⟨fun x ↦ ?_, example_12_1_solution_zero L u₀ m, deriv_example_12_1_solution_apply L u₀ m⟩
  rw [iteratedDeriv_two_example_12_1_solution, ← hm]
  ring

end QuarteroniSaccoSaleri.Chapter12

import Numlib.FiniteDifference.Hyperbolic

/-!
# Quarteroni–Sacco–Saleri §13.7: the finite difference method for hyperbolic equations

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §13.7 and §13.7.1.

On the grid `x_j = j Δx`, `t^n = n Δt` with `λ = Δt/Δx`, every explicit scheme for (13.26) has the
conservative form (13.36) `u_j^{n+1} = u_j^n - λ (h_{j+1/2} - h_{j-1/2})` for a numerical flux
`h`. The four schemes of §13.7.1 — forward Euler/centred (13.37), Lax–Friedrichs (13.39),
Lax–Wendroff (13.40) and upwind (13.41) — are three-point stencils
(`FiniteDifference.Stencil.threePoint cm c0 cp`, which sends `u` to
`j ↦ cm u_{j-1} + c0 u_j + cp u_{j+1}`), each with its own flux, and each of the last three is the
forward Euler/centred scheme plus an artificial viscosity (13.42) with the coefficient `k` of
Table 13.1. The implicit backward Euler/centred scheme (13.43) is the inverse on `ℓ²(ℤ)` of
`1 + (λa/2) D₀`, which exists because the centred difference `D₀` is skew-adjoint. The leap-frog
(13.44) and Newmark (13.45) schemes for the wave equation are the last two nodes.

The backbone home is `Numlib/FiniteDifference/Hyperbolic` over `Numlib/FiniteDifference/Stencil`.
-/

open FiniteDifference FiniteDifference.Hyperbolic

namespace QuarteroniSaccoSaleri.Chapter13

/-! ### The conservative form (13.36) -/

/-- **(13.36)**, the conservative form: a one-step map is in conservative form with numerical flux
`h` and `λ` when `step u j = u_j - λ (h(u_j, u_{j+1}) - h(u_{j-1}, u_j))`. For a *linear* flux
`h(u, v) = α u + β v` the map is the three-point stencil `Stencil.ofFlux λ α β`. -/
def equation_13_36 (lam : ℝ) (h : ℝ → ℝ → ℝ) (step : (ℤ → ℝ) → ℤ → ℝ) : Prop :=
  FiniteDifference.IsConservativeForm lam h step

/-- Every linear numerical flux gives a three-point stencil in conservative form
(Quarteroni–Sacco–Saleri, *Numerical Mathematics*, equation (13.36)). -/
theorem equation_13_36_ofFlux (lam α β : ℝ) :
    equation_13_36 lam (fun u v => α * u + β * v) (Stencil.apply (Stencil.ofFlux lam α β)) :=
  Stencil.isConservativeForm_ofFlux lam α β

/-! ### The explicit schemes of §13.7.1 -/

/-- **(13.37)**, forward Euler/centred: `u_j^{n+1} = u_j^n - (λa/2)(u_{j+1}^n - u_{j-1}^n)`. -/
noncomputable def equation_13_37 (a lam : ℝ) : Stencil := forwardEulerCentred a lam

/-- **(13.38)**: the forward Euler/centred scheme is in conservative form with the flux
`h(u, v) = ½ a (u + v)` (Quarteroni–Sacco–Saleri, *Numerical Mathematics*, equation (13.38)). -/
theorem equation_13_38 (a lam : ℝ) :
    equation_13_37 a lam = Stencil.ofFlux lam (a / 2) (a / 2) ∧
      equation_13_36 lam (fun u v => a / 2 * u + a / 2 * v)
        (Stencil.apply (equation_13_37 a lam)) := by
  refine ⟨forwardEulerCentred_eq_ofFlux a lam, ?_⟩
  rw [equation_13_37, forwardEulerCentred_eq_ofFlux]
  exact Stencil.isConservativeForm_ofFlux lam (a / 2) (a / 2)

/-- **(13.39)**, Lax–Friedrichs:
`u_j^{n+1} = ½(u_{j+1}^n + u_{j-1}^n) - (λa/2)(u_{j+1}^n - u_{j-1}^n)`. -/
noncomputable def equation_13_39 (a lam : ℝ) : Stencil := laxFriedrichs a lam

/-- **The Lax–Friedrichs flux** `h(u, v) = ½[a(u + v) - λ⁻¹(v - u)]`
(Quarteroni–Sacco–Saleri, *Numerical Mathematics*, §13.7.1). -/
theorem equation_13_39_flux {lam : ℝ} (hlam : lam ≠ 0) (a : ℝ) :
    equation_13_39 a lam = Stencil.ofFlux lam (a / 2 + 1 / (2 * lam)) (a / 2 - 1 / (2 * lam)) :=
  laxFriedrichs_eq_ofFlux hlam a

/-- **(13.40)**, Lax–Wendroff: `u_j^{n+1} = u_j^n - (λa/2)(u_{j+1}^n - u_{j-1}^n) +
(λ²a²/2)(u_{j+1}^n - 2u_j^n + u_{j-1}^n)`. -/
noncomputable def equation_13_40 (a lam : ℝ) : Stencil := laxWendroff a lam

/-- **The Lax–Wendroff flux** `h(u, v) = ½[a(u + v) - λa²(v - u)]`
(Quarteroni–Sacco–Saleri, *Numerical Mathematics*, §13.7.1). -/
theorem equation_13_40_flux (a lam : ℝ) :
    equation_13_40 a lam
      = Stencil.ofFlux lam (a / 2 + lam * a ^ 2 / 2) (a / 2 - lam * a ^ 2 / 2) :=
  laxWendroff_eq_ofFlux a lam

/-- **(13.41)**, upwind: `u_j^{n+1} = u_j^n - (λa/2)(u_{j+1}^n - u_{j-1}^n) +
(λ|a|/2)(u_{j+1}^n - 2u_j^n + u_{j-1}^n)`; for `a > 0` it is (13.50),
`u_j^{n+1} = u_j^n - λa (u_j^n - u_{j-1}^n)`. -/
noncomputable def equation_13_41 (a lam : ℝ) : Stencil := upwind a lam

/-- **(13.50)**: the upwind scheme for `a > 0` (Quarteroni–Sacco–Saleri, *Numerical Mathematics*,
equation (13.50)). -/
theorem equation_13_50 {a : ℝ} (ha : 0 < a) (lam : ℝ) :
    equation_13_41 a lam = Stencil.threePoint (lam * a) (1 - lam * a) 0 :=
  upwind_eq_of_pos ha lam

/-- **The upwind flux** `h(u, v) = ½[a(u + v) - |a|(v - u)]`
(Quarteroni–Sacco–Saleri, *Numerical Mathematics*, §13.7.1). -/
theorem equation_13_41_flux (a lam : ℝ) :
    equation_13_41 a lam = Stencil.ofFlux lam ((a + |a|) / 2) ((a - |a|) / 2) :=
  upwind_eq_ofFlux a lam

/-- **(13.42)**, the artificial-viscosity form: `u_j^{n+1} = u_j^n - (λa/2)(u_{j+1}^n - u_{j-1}^n)
+ (k/2)(u_{j+1}^n - 2u_j^n + u_{j-1}^n)/Δx²`. -/
noncomputable def equation_13_42 (a lam Δx k : ℝ) : Stencil := artificialViscosity a lam Δx k

/-- **Exercise 5 and Table 13.1**: the three schemes are the forward Euler/centred scheme with the
artificial viscosities `k = Δx²`, `k = a²Δt²` and `k = |a| Δx Δt` respectively
(Quarteroni–Sacco–Saleri, *Numerical Mathematics*, Exercise 13.5 and Table 13.1). -/
theorem exercise_13_5 {Δt Δx lam : ℝ} (hΔx : Δx ≠ 0) (hlam : lam = Δt / Δx) (a : ℝ) :
    equation_13_39 a lam = equation_13_42 a lam Δx (Δx ^ 2) ∧
      equation_13_40 a lam = equation_13_42 a lam Δx (a ^ 2 * Δt ^ 2) ∧
      equation_13_41 a lam = equation_13_42 a lam Δx (|a| * Δx * Δt) :=
  ⟨laxFriedrichs_eq_artificialViscosity hΔx a lam, laxWendroff_eq_artificialViscosity hΔx hlam a,
    upwind_eq_artificialViscosity hΔx hlam a⟩

/-! ### The implicit scheme (13.43) -/

/-- **(13.43)**, backward Euler/centred: `u_j^{n+1} + (λa/2)(u_{j+1}^{n+1} - u_{j-1}^{n+1}) =
u_j^n`. On `ℓ²(ℤ)` the operator `B = 1 + (λa/2) D₀` on the left is invertible, because the centred
difference `D₀` is skew-adjoint, and the scheme advances by `B⁻¹`
(`FiniteDifference.Hyperbolic.backwardEulerCentred`). -/
noncomputable def equation_13_43 (a lam : ℝ) :
    lp (fun _ : ℤ => ℝ) 2 →L[ℝ] lp (fun _ : ℤ => ℝ) 2 := backwardEulerCentred a lam

/-- **The implicit scheme (13.43) is solved by `equation_13_43`**: the new level `u^{n+1} =
B⁻¹ u^n` satisfies `u_j^{n+1} + (λa/2)(u_{j+1}^{n+1} - u_{j-1}^{n+1}) = u_j^n`, and the centred
difference is skew-adjoint (Quarteroni–Sacco–Saleri, *Numerical Mathematics*, equation (13.43) and
Exercise 13.7). -/
theorem equation_13_43_spec (a lam : ℝ) (u : lp (fun _ : ℤ => ℝ) 2) (j : ℤ) :
    equation_13_43 a lam u j
        + lam * a / 2 * (equation_13_43 a lam u (j + 1) - equation_13_43 a lam u (j - 1)) = u j ∧
      ∀ v w : lp (fun _ : ℤ => ℝ) 2,
        inner ℝ (centredDiffCLM v) w = -inner ℝ v (centredDiffCLM w) := by
  refine ⟨?_, fun v w => inner_centredDiffCLM_left v w⟩
  have h := backwardEulerCentredOp_apply a lam (backwardEulerCentred a lam u) j
  rw [backwardEulerCentred_spec] at h
  exact h.symm

/-! ### The schemes for the wave equation -/

/-- **(13.44)**, leap-frog: `u_j^{n+1} - 2u_j^n + u_j^{n-1} = (γλ)²(u_{j+1}^n - 2u_j^n +
u_{j-1}^n)`. -/
def equation_13_44 (γ lam : ℝ) (u : ℕ → ℤ → ℝ) : Prop := IsLeapFrog γ lam u

/-- **(13.45)**, Newmark, with the parameters `0 ≤ β ≤ ½` and `0 ≤ θ ≤ 1` and the auxiliary
velocity `v`. -/
def equation_13_45 (γ lam Δt β θ : ℝ) (u v : ℕ → ℤ → ℝ) : Prop := IsNewmark γ lam Δt β θ u v

end QuarteroniSaccoSaleri.Chapter13

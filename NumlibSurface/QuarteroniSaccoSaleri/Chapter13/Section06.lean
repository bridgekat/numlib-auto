import Mathlib.LinearAlgebra.Matrix.ToLin
import NumlibSurface.QuarteroniSaccoSaleri.Chapter13.Section05

/-!
# Quarteroni–Sacco–Saleri §13.6: systems of linear hyperbolic equations

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §13.6 and §13.6.1.

The system (13.30) `u_t + A u_x = 0` with a constant real matrix `A` is *hyperbolic* when `A` is
diagonalizable over `ℝ`, `A = T Λ T⁻¹`, and *strictly hyperbolic* when the eigenvalues are
distinct. The columns `ω^k` of `T` are right eigenvectors; the *characteristic variables*
`w = T⁻¹ u` then solve `p` decoupled scalar transport equations, so §13.5 applies to each and the
solution is `u(x, t) = ∑_k w_k(x - λ_k t, 0) ω^k`. In particular `u(x̄, t̄)` reads the datum only at
the `p` feet `x̄ - λ_k t̄`, the *domain of dependence* (13.31).

Remark 13.2 defines hyperbolicity of the nonlinear system (13.32) through the Jacobian of the flux
function. §13.6.1 rewrites the wave equation (13.33)–(13.34) as the first-order system (13.35) for
`ω = (u_x, u_t)`, whose matrix `!![0, -1; -γ², 0]` has the distinct eigenvalues `±γ`.

The backbone home is `Numlib/Analysis/PDE/Transport`. Remark 13.3 (the conic-section
classification) is heuristic prose and is not formalized; nor is the count of boundary conditions
at each end.
-/

open Matrix

namespace QuarteroniSaccoSaleri.Chapter13

variable {p : ℕ}

/-! ### The system (13.30) and hyperbolicity -/

/-- **(13.30)**: `u` is a classical solution of the system `u_t + A u_x = 0` on `ℝ × [0, ∞)` with
the datum `u₀`. -/
def equation_13_30 (A : Matrix (Fin p) (Fin p) ℝ) (u₀ : ℝ → Fin p → ℝ)
    (u : ℝ → ℝ → Fin p → ℝ) : Prop := Transport.IsSystemSolution A u₀ u

/-- **The system (13.30) is hyperbolic** when `A` is diagonalizable with real eigenvalues,
`A = T Λ T⁻¹`, and **strictly hyperbolic** when the eigenvalues are distinct; the columns of `T`
are then right eigenvectors, `A ω^k = λ_k ω^k` (Quarteroni–Sacco–Saleri, *Numerical Mathematics*,
§13.6). -/
theorem isHyperbolic (A : Matrix (Fin p) (Fin p) ℝ) :
    (Transport.IsStrictlyHyperbolic A → Transport.IsHyperbolic A) ∧
      ∀ (T : Matrix (Fin p) (Fin p) ℝ) (lam : Fin p → ℝ), IsUnit T →
        A = T * diagonal lam * T⁻¹ → ∀ k, A *ᵥ Tᵀ k = lam k • Tᵀ k :=
  ⟨Transport.IsStrictlyHyperbolic.isHyperbolic,
    fun _ _ hT hA k => Transport.mulVec_col_eq_smul hT hA k⟩

/-- **The characteristic variables** `w = T⁻¹ u` decouple the system: each `w_k` solves the scalar
transport equation `∂_t w_k + λ_k ∂_x w_k = 0` with datum `(T⁻¹ u₀)_k`
(Quarteroni–Sacco–Saleri, *Numerical Mathematics*, §13.6). -/
theorem characteristicVariables {A T : Matrix (Fin p) (Fin p) ℝ} {lam : Fin p → ℝ} (hT : IsUnit T)
    (hA : A = T * diagonal lam * T⁻¹) {u₀ : ℝ → Fin p → ℝ} {u : ℝ → ℝ → Fin p → ℝ}
    (hu : equation_13_30 A u₀ u) (k : Fin p) :
    equation_13_26 (lam k) (fun x => (T⁻¹ *ᵥ u₀ x) k) (fun x t => (T⁻¹ *ᵥ u x t) k) :=
  hu.characteristicVariables hT hA k

/-- **The solution formula of a hyperbolic system**: `u(x, t) = ∑_k w_k(x - λ_k t, 0) ω^k` is a
solution, and it is the only one (Quarteroni–Sacco–Saleri, *Numerical Mathematics*, §13.6). -/
theorem hyperbolicSystem_solution {A T : Matrix (Fin p) (Fin p) ℝ} {lam : Fin p → ℝ}
    (hT : IsUnit T) (hA : A = T * diagonal lam * T⁻¹) {u₀ : ℝ → Fin p → ℝ}
    (hu₀ : ∀ k, Differentiable ℝ fun x => (T⁻¹ *ᵥ u₀ x) k) :
    equation_13_30 A u₀ (fun x t => ∑ k, (T⁻¹ *ᵥ u₀ (x - lam k * t)) k • Tᵀ k) ∧
      ∀ u : ℝ → ℝ → Fin p → ℝ, equation_13_30 A u₀ u → ∀ (x t : ℝ), 0 ≤ t →
        u x t = ∑ k, (T⁻¹ *ᵥ u₀ (x - lam k * t)) k • Tᵀ k :=
  ⟨Transport.isSystemSolution_sum hT hA hu₀, fun _ hu x _ ht => hu.eq_sum hT hA x ht⟩

/-- **(13.31)**, the domain of dependence of `u(x̄, t̄)`: the `p` feet `x̄ - λ_k t̄` of the
characteristics through `(x̄, t̄)`; two data agreeing there give solutions agreeing at `(x̄, t̄)`
(Quarteroni–Sacco–Saleri, *Numerical Mathematics*, equation (13.31)). -/
theorem equation_13_31 {A T : Matrix (Fin p) (Fin p) ℝ} {lam : Fin p → ℝ} (hT : IsUnit T)
    (hA : A = T * diagonal lam * T⁻¹) {u₀ v₀ : ℝ → Fin p → ℝ} {u v : ℝ → ℝ → Fin p → ℝ}
    (hu : equation_13_30 A u₀ u) (hv : equation_13_30 A v₀ v) {xb tb : ℝ} (htb : 0 ≤ tb)
    (h : Set.EqOn u₀ v₀ (Transport.domainOfDependence lam xb tb)) : u xb tb = v xb tb :=
  hu.eq_of_eqOn_domainOfDependence hT hA hv htb h

/-- **Remark 13.2**: the nonlinear system (13.32) `u_t + ∂_x g(u) = 0` is hyperbolic at the state
`u` when the Jacobian of the flux `g` there is diagonalizable with real eigenvalues. -/
def remark_13_2 (g : (Fin p → ℝ) → (Fin p → ℝ)) (u : Fin p → ℝ) : Prop :=
  Transport.IsHyperbolic (LinearMap.toMatrix' (fderiv ℝ g u : (Fin p → ℝ) →ₗ[ℝ] (Fin p → ℝ)))

/-! ### §13.6.1, the wave equation -/

/-- **(13.33)–(13.34)**: `u` is a classical solution of the wave equation
`∂_tt u - γ² ∂_xx u = f` on the strip `[α, β] × [0, ∞)` with the initial displacement `u₀`, the
initial velocity `v₀` and homogeneous Dirichlet conditions at the two ends. -/
def equation_13_33 (γ : ℝ) (f : ℝ → ℝ → ℝ) (u₀ v₀ : ℝ → ℝ) (α β : ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  Transport.IsWaveSolution γ f u₀ v₀ α β u

/-- **(13.35)**: the change of variables `ω = (∂_x u, ∂_t u)` turns the homogeneous wave equation
into the first-order system `∂_t ω + A ∂_x ω = 0` with `A = !![0, -1; -γ², 0]` and the initial
data `(u₀', v₀)` (Quarteroni–Sacco–Saleri, *Numerical Mathematics*, equation (13.35)). -/
theorem equation_13_35 {γ : ℝ} {u₀ v₀ : ℝ → ℝ} {α β : ℝ} {u : ℝ → ℝ → ℝ}
    (hu : equation_13_33 γ 0 u₀ v₀ α β u) :
    ∃ w : ℝ → ℝ → Fin 2 → ℝ,
      Transport.IsSystemSolutionOn (Set.Icc α β) (Transport.waveMatrix γ) (fun x => w x 0) w ∧
        (∀ x ∈ Set.Icc α β, HasDerivWithinAt u₀ (w x 0 0) (Set.Icc α β) x) ∧
        ∀ x ∈ Set.Icc α β, w x 0 1 = v₀ x :=
  hu.isSystemSolution

/-- **The matrix of (13.35) is strictly hyperbolic** for `γ ≠ 0`, with the two distinct
eigenvalues `±γ` and the eigenvectors `(1, ∓γ)` — the propagation velocities of the wave
(Quarteroni–Sacco–Saleri, *Numerical Mathematics*, §13.6.1). -/
theorem waveMatrix_isHyperbolic {γ : ℝ} (hγ : γ ≠ 0) :
    Transport.IsStrictlyHyperbolic (Transport.waveMatrix γ) ∧
      Transport.IsHyperbolic (Transport.waveMatrix γ) :=
  ⟨Transport.waveMatrix_isStrictlyHyperbolic hγ,
    (Transport.waveMatrix_isStrictlyHyperbolic hγ).isHyperbolic⟩

end QuarteroniSaccoSaleri.Chapter13

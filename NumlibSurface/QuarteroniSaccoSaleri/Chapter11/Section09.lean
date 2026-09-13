import Numlib.Analysis.ODE.LinearSystem
import NumlibSurface.QuarteroniSaccoSaleri.Chapter11.Section01

/-!
# Quarteroni–Sacco–Saleri §11.9: systems of ODEs

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §11.9.

The vector Cauchy problem (11.78)–(11.79) `y' = F(t, y)`, `y(t₀) = y₀` in `ℝⁿ`; Property 11.5
(global existence and uniqueness under the Lipschitz condition (11.80)); the linear system
`y' = A y` (11.81) with `A ∈ ℝⁿˣⁿ` diagonalizable, its solutions `y(t) = ∑ⱼ Cⱼ e^{λⱼ t} vⱼ`
(11.82), their decay when every eigenvalue has negative real part (11.83)–(11.84), and the
diagonalized system `z' = Λ z`, `z = Q⁻¹ y` (11.85).

The vector Cauchy problem is `ODE.IsSolutionOn` on `EuclideanSpace ℝ (Fin n)` and Property 11.5
is `ODE.existsUnique_isSolutionOn_of_lipschitz` there; the linear system is read on `Fin n → ℝ`,
where matrices act by `Matrix.mulVec`, and its complexification `A.map ofReal` on `Fin n → ℂ`
is the setting of `Numlib/Analysis/ODE/LinearSystem`. The book's hypothesis "`A` has `n` distinct
eigenvalues `λⱼ` with eigenvectors `vⱼ`" is taken in the form it is used, a diagonalization
`A = Q Λ Q⁻¹` over `ℂ` with `Λ = diagonal λ` and the columns of `Q` the eigenvectors.

## Main definitions

* `equation_11_78 F t₀ y₀ I y` — `y` solves the system (11.78)–(11.79) on `I`.

## Main results

* `property_11_5` — existence and uniqueness for a Lipschitz field.
* `linearSystem_complexify` — a real solution of `y' = A y`, read in `ℂ`, solves the
  complexified system.
* `equation_11_82`, `equation_11_83`, `equation_11_85` — the eigen-expansion of the solutions,
  their decay, and the diagonalized system.
-/

open Set Filter Topology Matrix

namespace QuarteroniSaccoSaleri.Chapter11

variable {n : ℕ}

/-- **The vector Cauchy problem (11.78)–(11.79)**: `y' = F(t, y)`, `y(t₀) = y₀`, for
`F : ℝ × ℝⁿ → ℝⁿ`; `ODE.IsSolutionOn` on `EuclideanSpace ℝ (Fin n)`. -/
def equation_11_78 (F : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (t₀ : ℝ)
    (y₀ : EuclideanSpace ℝ (Fin n)) (I : Set ℝ) (y : ℝ → EuclideanSpace ℝ (Fin n)) : Prop :=
  ODE.IsSolutionOn F t₀ y₀ I y

/-- **Property 11.5**: let `F : ℝ × ℝⁿ → ℝⁿ` be continuous on `D = [t₀, T] × ℝⁿ` (`t₀ ≤ T`), and
suppose there is `L ≥ 0` with `‖F(t, y) - F(t, ȳ)‖ ≤ L ‖y - ȳ‖` for all `(t, y), (t, ȳ) ∈ D`
(11.80). Then for every `y₀ ∈ ℝⁿ` there is a unique `y`, continuous and differentiable on
`[t₀, T]`, solving the Cauchy problem (11.78)–(11.79) (pinned to `y₀` off the interval);
`ODE.existsUnique_isSolutionOn_of_lipschitz`. -/
theorem property_11_5 {F : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {t₀ T L : ℝ}
    (hT : t₀ ≤ T) (hL : 0 ≤ L) (hF : ContinuousOn (Function.uncurry F) (Icc t₀ T ×ˢ univ))
    (hlip : ∀ t ∈ Icc t₀ T, ∀ y w : EuclideanSpace ℝ (Fin n), ‖F t y - F t w‖ ≤ L * ‖y - w‖)
    (y₀ : EuclideanSpace ℝ (Fin n)) :
    ∃! y : ℝ → EuclideanSpace ℝ (Fin n), equation_11_78 F t₀ y₀ (Icc t₀ T) y ∧
      ∀ t ∉ Icc t₀ T, y t = y₀ := by
  have e : Icc t₀ T = Icc t₀ (t₀ + (T - t₀)) := by rw [add_sub_cancel]
  simp only [equation_11_78, e]
  rw [e] at hF hlip
  exact ODE.existsUnique_isSolutionOn_of_lipschitz (K := ⟨L, hL⟩) (by linarith) hF
    (fun t ht => LipschitzWith.of_dist_le_mul fun v₁ v₂ => by
      rw [dist_eq_norm, dist_eq_norm]
      exact hlip t ht v₁ v₂) y₀

/-! ### The linear system `y' = A y` -/

variable {A : Matrix (Fin n) (Fin n) ℝ} {y₀ : Fin n → ℝ} {y : ℝ → Fin n → ℝ}

/-- A real solution of the linear system (11.81) `y' = A y`, read in `ℂ` componentwise, solves the
complexified system `z' = (A ⊗ ℂ) z`. -/
theorem linearSystem_complexify {t₀ : ℝ} {I : Set ℝ}
    (hy : ODE.IsSolutionOn (fun _ v => A *ᵥ v) t₀ y₀ I y) :
    ODE.IsSolutionOn (fun _ v => A.map ((↑) : ℝ → ℂ) *ᵥ v) t₀ (fun i => (y₀ i : ℂ)) I
      fun t i => (y t i : ℂ) := by
  refine ⟨by simp [hy.1], fun t ht => ?_⟩
  rw [hasDerivWithinAt_pi]
  intro i
  have := (hasDerivWithinAt_pi.1 (hy.2 t ht) i).ofReal_comp
  refine this.congr_deriv ?_
  change ((A *ᵥ y t) i : ℂ) = (A.map ((↑) : ℝ → ℂ) *ᵥ fun i => (y t i : ℂ)) i
  exact RingHom.map_mulVec Complex.ofRealHom A (y t) i

/-- **The solutions of `y' = A y` (11.81)–(11.82)**: if `A ∈ ℝⁿˣⁿ` is diagonalizable over `ℂ`,
`A = Q Λ Q⁻¹` with `Λ = diagonal λ` (the columns `vⱼ` of `Q` an eigenvector basis, `λⱼ` the
eigenvalues — as when `A` has `n` distinct eigenvalues), then every solution of `y' = A y`,
`y(0) = y₀`, on `[0, T]` is `y(t) = ∑ⱼ Cⱼ e^{λⱼ t} vⱼ` (read in `ℂ`), the constants `C = Q⁻¹ y₀`
being fixed by the initial condition; `ODE.linear_solution_eq_sum_exp_smul`. -/
theorem equation_11_82 {Q : Matrix (Fin n) (Fin n) ℂ} {μ : Fin n → ℂ}
    (hA : A.map ((↑) : ℝ → ℂ) = Q * diagonal μ * Q⁻¹) (hQ : IsUnit Q) {T : ℝ}
    (hy : ODE.IsSolutionOn (fun _ v => A *ᵥ v) 0 y₀ (Icc 0 T) y) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (fun i => (y t i : ℂ)) =
      ∑ j, ((Q⁻¹ *ᵥ fun i => (y₀ i : ℂ)) j * Complex.exp (μ j * t)) • fun i => Q i j :=
  ODE.linear_solution_eq_sum_exp_smul hA hQ (linearSystem_complexify hy) ht

/-- **Decay of the solutions (11.83)–(11.84)**: if `A = Q Λ Q⁻¹` is diagonalizable over `ℂ` and
every eigenvalue has negative real part, every solution of `y' = A y` on `[0, ∞)` satisfies
`‖y(t)‖ → 0` as `t → ∞`, since `e^{λⱼ t} = e^{Re λⱼ t} (cos (Im λⱼ t) + i sin (Im λⱼ t)) → 0`;
`ODE.linear_tendsto_zero_of_re_lt_zero`. -/
theorem equation_11_83 {Q : Matrix (Fin n) (Fin n) ℂ} {μ : Fin n → ℂ}
    (hA : A.map ((↑) : ℝ → ℂ) = Q * diagonal μ * Q⁻¹) (hQ : IsUnit Q) (hμ : ∀ j, (μ j).re < 0)
    (hy : ODE.IsSolutionOn (fun _ v => A *ᵥ v) 0 y₀ (Ici 0) y) :
    Tendsto (fun t => ‖y t‖) atTop (𝓝 0) := by
  have := ODE.linear_tendsto_zero_of_re_lt_zero hA hQ hμ (linearSystem_complexify hy)
  refine this.congr fun t => ?_
  simp only [Pi.norm_def, Complex.nnnorm_real]

/-- **The diagonalized system (11.85)**: with `Λ = Q⁻¹ A Q` diagonal and `z = Q⁻¹ y`, a solution
`y` of `y' = A y` on `I` gives a solution `z` of `z' = Λ z` on `I`, `n` decoupled scalar test
equations `zⱼ' = λⱼ zⱼ`; `ODE.linear_diagonalized_isSolutionOn`, `ODE.isSolutionOn_diagonal_iff`. -/
theorem equation_11_85 {Q : Matrix (Fin n) (Fin n) ℂ} {μ : Fin n → ℂ}
    (hA : A.map ((↑) : ℝ → ℂ) = Q * diagonal μ * Q⁻¹) (hQ : IsUnit Q) {t₀ : ℝ} {I : Set ℝ}
    (hy : ODE.IsSolutionOn (fun _ v => A *ᵥ v) t₀ y₀ I y) :
    ODE.IsSolutionOn (fun _ v => diagonal μ *ᵥ v) t₀ (Q⁻¹ *ᵥ fun i => (y₀ i : ℂ)) I
        (fun t => Q⁻¹ *ᵥ fun i => (y t i : ℂ)) ∧
      ∀ j, ODE.IsSolutionOn (fun _ w => μ j * w) t₀ ((Q⁻¹ *ᵥ fun i => (y₀ i : ℂ)) j) I
        fun t => (Q⁻¹ *ᵥ fun i => (y t i : ℂ)) j := by
  have h := ODE.linear_diagonalized_isSolutionOn hA hQ (linearSystem_complexify hy)
  exact ⟨h, ODE.isSolutionOn_diagonal_iff.1 h⟩

end QuarteroniSaccoSaleri.Chapter11

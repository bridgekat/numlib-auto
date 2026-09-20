import Numlib.Analysis.Sobolev.Interval
import Numlib.Approximation.CompositeQuadrature
import Numlib.Approximation.MarkovInequality
import Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz
import Numlib.FiniteDifference.Parabolic
import Numlib.Variational.FiniteElementInterval
import NumlibSurface.QuarteroniSaccoSaleri.Chapter12.Section03

/-!
# Quarteroni–Sacco–Saleri §13.3: finite elements for the heat equation, the θ-method

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §13.3 and §13.3.1.

The heat equation is put in weak form (13.12) on `V = H¹₀(0, 1)` with the bilinear form
`a(u, v) = ν ∫₀¹ u' v'` (`heatForm`, (13.18)), and discretized in space by a Galerkin method in a
finite-dimensional trial space `V_h` (13.13). The stability analysis of §13.3.1 — the backward
Euler estimates (13.19)–(13.21), Remark 13.1, the eigenpairs of a form (Definition 13.1), the
discrete eigenproblem (13.22), the θ-recursion in the eigenbasis, and the dichotomy
"unconditionally stable for `θ ≥ ½`, stable for `θ < ½` iff `Δt ≤ 2/((1 - 2θ) λ_max)`" — uses
nothing about `V_h` but its inner product and the form, which is exactly what Remark 13.1 and
Exercise 4 of the book say; so it is stated here for an arbitrary real inner product space `V`,
the book's `V_h` carrying the `L²` inner product, and a bounded form `a` on it. Every proof is a
specialization of `Numlib/Variational/Evolution`, and the matrix form (13.14)–(13.16) of
`Numlib/FiniteDifference/Parabolic`.

The concrete side is `heatForm` on `H¹(0, 1)`: (13.18) is `heatForm ν v v = ν ‖v'‖²_{L²}`, and
`heatForm_l2_coercive` is the `L²`-coercivity `γ ‖v‖²_{L²} ≤ a(v, v)` with the book's
`γ = ν / C_P²`, which is `2ν` on `(0, 1)` since `C_P = 1/√2` ([quarteroni2000numerical] (12.16));
that constant is what the energy estimate after (13.13) uses.

The mass matrix of the uniform-mesh piecewise linear space is
`massMatrix n = (h/6) tridiag(1, 4, 1)`, `h = 1/n`, positive definite, and the stiffness matrix
of the heat form is `heatStiffnessMatrix ν n = (ν/h) tridiag(-1, 2, -1)`; both are the Gram
matrices of chapter 12's hat basis (`massMatrix_eq_gram`, `heatStiffnessMatrix_eq_gram`), so
`massMatrix_apply_eq_integral` identifies the entries with the integrals `∫ φ_j φ_i` and
`exercise_13_2` computes the lumped matrix `M̃ = h · I`. Since both matrices are
`Matrix.symmTridiagonalToeplitz`, so is `A_fe - λ M`, and `pencil_hasEigenvalue_iff` reads the
generalized eigenvalues `λ_h^i = (6ν/h²)(1 - cos θ_i)/(2 + cos θ_i)` off the cosine spectrum;
`pencil_maxEigenvalue_bounds` gives `3ν h^{-2} ≤ λ_h^{N_h} ≤ 12ν h^{-2}` and `equation_13_23`
the stability condition `Δt ≤ h²/(6ν(1 - 2θ))`.

The pseudo-spectral Galerkin approximation of (13.24) is `SpectralSpace N x w`, the space
`ℙ_N^0` of §12.3 with the Legendre–Gauss–Lobatto inner product `(·, ·)_N` of (12.37) (an inner
product space under `[Fact (IsLegendreLobatto N x w)]`), with the form
`a_N(u, v) = ν (u', v')_N = ν ∫ u' v'` (`SpectralSpace.spectralForm`). Its eigenvalues are at most
`ν N²(N + 1)²` (`SpectralSpace.spectralForm_eigenvalue_le`, from the `L²` Markov inequality of
`Numlib/Approximation/MarkovInequality` and the norm equivalence of §12.3), so the θ-method with
`θ < 1/2` is stable whenever `Δt ≤ N⁻⁴/(2ν(1 - 2θ))` (`equation_13_24`). The matching lower bound
`λ_max ≥ c N⁴`, which would make the condition necessary, is not proved.

**Erratum**: the hint of Exercise 2 prints
`m_ij = (h/6)·{1/2 (i ≠ j), 1 (i = j)}`; the exact integrals are `∫ φ_i² = 2h/3` and
`∫ φ_i φ_{i±1} = h/6`, i.e. `M = (h/6) tridiag(1, 4, 1)`, which is what Program 100 assembles.

## Conventions

`V` is the book's `V_h`, a real inner product space carrying the `L²` inner product of the book;
`a : SesqForm ℝ V` is the bilinear form restricted to it. Positivity of a form is
`a.IsCoerciveWith 0` and `L²`-coercivity `a.IsCoerciveWith α`, as in `Numlib/Variational`. The
concrete space `H¹(0, 1)` is `SobolevInterval 1 0 1`, whose `j`-th weak derivative in `L²(0, 1)`
is `SobolevInterval.deriv u j`; `‖SobolevInterval.deriv u 0‖` is the book's `‖u‖_{L²(0,1)}` and
`‖SobolevInterval.deriv u 1‖` its `‖∂ₓ u‖_{L²(0,1)}`.
-/

open Set Filter Topology MeasureTheory
open scoped Real Matrix RealInnerProductSpace

namespace QuarteroniSaccoSaleri.Chapter13

noncomputable section

/-! ### The weak formulation (13.12) and its form -/

/-- **The bilinear form of the heat equation** ([quarteroni2000numerical] §13.3, the form
`a(u, v) = ∫₀¹ ν u' v'` of (13.12)), on `H¹(0, 1)`. It is (12.44) at `α = ν`, `β = γ = 0`; the
weak problem lives on the subspace `H¹₀(0, 1)`. -/
def heatForm (ν : ℝ) : SesqForm ℝ (SobolevInterval 1 0 1) :=
  ν • ((((innerSL ℝ : SesqForm ℝ (Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))).comp
    (SobolevInterval.derivL 1 0 1 1)).flip.comp (SobolevInterval.derivL 1 0 1 1)).flip)

/-- The heat form is the `L²` pairing of the weak derivatives. -/
@[simp]
theorem heatForm_apply (ν : ℝ) (u v : SobolevInterval 1 0 1) :
    heatForm ν u v = ν * ⟪SobolevInterval.deriv u 1, SobolevInterval.deriv v 1⟫ := rfl

/-- **(13.18)** ([quarteroni2000numerical] (13.18)): `a(v, v) = ν ‖∂ₓ v‖²_{L²(0,1)}`. -/
theorem equation_13_18 (ν : ℝ) (v : SobolevInterval 1 0 1) :
    heatForm ν v v = ν * ‖SobolevInterval.deriv v 1‖ ^ 2 := by
  rw [heatForm_apply, real_inner_self_eq_norm_sq]

/-- The heat form is symmetric. -/
theorem heatForm_isHermitian (ν : ℝ) : (heatForm ν).IsHermitian := fun u v => by
  simp only [heatForm_apply, RCLike.conj_to_real, real_inner_comm]

/-- **`L²`-coercivity of the heat form on `H¹₀(0, 1)`** ([quarteroni2000numerical] §13.1 and
§13.3, `γ = ν / C_P²`): since Poincaré's constant of `(0, 1)` is `C_P = 1/√2` (12.16), the form
satisfies `2 ν ‖v‖²_{L²} ≤ a(v, v)`. This is the constant `γ` of (13.7) and of the energy
estimate after (13.13). -/
theorem heatForm_l2_coercive {ν : ℝ} (hν : 0 < ν) {u : SobolevInterval 1 0 1}
    (hu : u ∈ SobolevIntervalZero 0 1) :
    2 * ν * ‖SobolevInterval.deriv u 0‖ ^ 2 ≤ heatForm ν u u := by
  have h := SobolevIntervalZero.norm_deriv_zero_le (by norm_num : (0 : ℝ) < 1) hu
  have hsq : ‖SobolevInterval.deriv u 0‖ ^ 2 ≤ 1 / 2 * ‖SobolevInterval.deriv u 1‖ ^ 2 := by
    rw [show ((1 : ℝ) - 0) / Real.sqrt 2 = 1 / Real.sqrt 2 by norm_num] at h
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [mul_pow, div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at h2
    linarith
  rw [equation_13_18]
  nlinarith

/-- **The weak heat equation** ([quarteroni2000numerical] (13.12)): `u : ℝ → H¹₀(0, 1)` with
`⟪∂ₜ u, v⟫_{L²} + a(u, v) = ⟪f, v⟫_{L²}` for every `v ∈ H¹₀(0, 1)` and `t ∈ [0, T]`, and
`u(0) = u₀`; the time derivative is taken in `L²(0, 1)`, within `[0, T]`. Only the definition is
claimed: existence and uniqueness of weak solutions is Bochner-space theory (Lions' theorem) and
is not formalized. -/
def equation_13_12 (ν T : ℝ) (f : ℝ → Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (u₀ : SobolevInterval 1 0 1) (u : ℝ → SobolevInterval 1 0 1) : Prop :=
  (∀ t ∈ Icc (0 : ℝ) T, u t ∈ SobolevIntervalZero 0 1) ∧ u 0 = u₀ ∧
    ∃ u' : ℝ → Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)), ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s => SobolevInterval.deriv (u s) 0) (u' t) (Icc 0 T) t ∧
        ∀ v ∈ SobolevIntervalZero 0 1,
          ⟪u' t, SobolevInterval.deriv v 0⟫ + heatForm ν (u t) v
            = ⟪f t, SobolevInterval.deriv v 0⟫

/-! ### The semi-discrete Galerkin problem (13.13) -/

section Galerkin

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **The semi-discrete Galerkin problem** ([quarteroni2000numerical] (13.13)): on the trial
space `V_h` with the `L²` inner product, `⟪∂ₜ u_h, v_h⟫ + a(u_h, v_h) = F(v_h)` for every
`v_h ∈ V_h` and `t ∈ [0, T]`, with `u_h(0) = u_{0h}`. This is
`Variational.IsSemidiscreteGalerkin` at a time-independent form. -/
def equation_13_13 (a : SesqForm ℝ V) (F : ℝ → V →L[ℝ] ℝ) (u₀ : V) (T : ℝ) (u : ℝ → V) : Prop :=
  Variational.IsSemidiscreteGalerkin (fun _ => a) F u₀ T u

/-- **The a priori estimate for the semi-discrete solution** ([quarteroni2000numerical] §13.3,
the display after (13.13)): `E_h(t) ≤ e^{-γt} E_h(0) + γ⁻¹ ∫₀ᵗ e^{γ(s-t)} F(s) ds` with
`E_h(t) = ‖u_h(t)‖²_{L²}`, for a form that is `L²`-coercive with constant `γ` — for the heat
equation `γ = ν / C_P²` by `heatForm_l2_coercive` — and `‖F(t)‖ ≤ φ(t)`, so that
`F(t) = φ(t)² = ‖f(t)‖²_{L²}`. -/
theorem equation_13_13_energy {a : SesqForm ℝ V} {F : ℝ → V →L[ℝ] ℝ} {u₀ : V} {T : ℝ} {u : ℝ → V}
    (h : equation_13_13 a F u₀ T u) {γ : ℝ} (hγ : 0 < γ) (hcoer : a.IsCoerciveWith γ)
    {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc 0 T)) (hF : ∀ t ∈ Icc 0 T, ‖F t‖ ≤ φ t)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖u t‖ ^ 2 ≤ Real.exp (-γ * t) * ‖u₀‖ ^ 2
      + γ⁻¹ * ∫ s in (0 : ℝ)..t, Real.exp (γ * (s - t)) * φ s ^ 2 :=
  h.norm_sq_le_exp hγ (fun _ _ => hcoer) hφ hF ht

end Galerkin

/-! ### The matrix form (13.14)–(13.16) -/

section MatrixForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type*} [Fintype ι]

/-- **The matrix form of the semi-discrete Galerkin problem** ([quarteroni2000numerical] (13.14)):
in a basis `φ` of `V_h`, `u_h` solves (13.13) if and only if its coordinate vector solves
`M ξ' + A_fe ξ = f_fe`, with the mass matrix `M_{ij} = ⟪φ_j, φ_i⟫`, the stiffness matrix
`(A_fe)_{ij} = a(φ_j, φ_i)` and the load vector `(f_fe)_i = F(φ_i)`. -/
theorem equation_13_14 (φ : Module.Basis ι ℝ V) (a : SesqForm ℝ V) (F : ℝ → V →L[ℝ] ℝ) (u₀ : V)
    (T : ℝ) (u : ℝ → V) :
    equation_13_13 a F u₀ T u ↔
      FiniteDifference.IsSemidiscrete (SesqForm.gramMatrix (innerSL ℝ) φ) (a.gramMatrix φ)
        (fun t i => F t (φ i)) (φ.equivFun u₀) T (fun t => φ.equivFun (u t)) :=
  FiniteDifference.isSemidiscreteGalerkin_iff_isSemidiscrete φ a F u₀ T u

omit [FiniteDimensional ℝ V] in
-- the linter does not see the `Fintype` inside `Matrix.PosDef`
set_option linter.unusedFintypeInType false in
/-- **The mass matrix is positive definite** ([quarteroni2000numerical] §13.3, "Since it is
nonsingular"): the Gram matrix of a basis for the `L²` inner product. -/
theorem massMatrix_gram_posDef (φ : Module.Basis ι ℝ V) :
    (SesqForm.gramMatrix (innerSL ℝ) φ).PosDef :=
  FiniteDifference.massMatrix_posDef φ.linearIndependent

/-- **The normal form** ([quarteroni2000numerical] (13.15)): since the mass matrix is
nonsingular, `M ξ' + A ξ = f` is `ξ' = -M⁻¹ A ξ + M⁻¹ f`. -/
theorem equation_13_15 [DecidableEq ι] {M : Matrix ι ι ℝ} (hM : M.PosDef) (A : Matrix ι ι ℝ)
    (f : ℝ → ι → ℝ) (ξ₀ : ι → ℝ) (T : ℝ) (ξ : ℝ → ι → ℝ) :
    FiniteDifference.IsSemidiscrete M A f ξ₀ T ξ ↔
      FiniteDifference.IsSemidiscrete 1 (M⁻¹ * A) (fun t => M⁻¹ *ᵥ f t) ξ₀ T ξ :=
  FiniteDifference.IsSemidiscrete.iff_normalForm hM.isUnit A f ξ₀ T ξ

/-- **The θ-method for the matrix system** ([quarteroni2000numerical] (13.16)):
`M (ξ' - ξ)/Δt + A (θ ξ' + (1 - θ) ξ) = θ f₁ + (1 - θ) f₀`. -/
def equation_13_16 (M A : Matrix ι ι ℝ) (θ Δt : ℝ) (f₀ f₁ ξ ξ' : ι → ℝ) : Prop :=
  M *ᵥ (Δt⁻¹ • (ξ' - ξ)) + A *ᵥ (θ • ξ' + (1 - θ) • ξ) = θ • f₁ + (1 - θ) • f₀

/-- (13.16) is solved by `FiniteDifference.thetaStep`, the system matrix `M + θ Δt A` being
invertible. -/
theorem equation_13_16_iff [DecidableEq ι] {M A : Matrix ι ι ℝ} (hM : M.PosDef)
    (hA : ∀ x, 0 ≤ x ⬝ᵥ (A *ᵥ x)) {θ Δt : ℝ} (hθ : 0 ≤ θ) (hΔt : 0 < Δt) (f₀ f₁ ξ ξ' : ι → ℝ) :
    equation_13_16 M A θ Δt f₀ f₁ ξ ξ' ↔ ξ' = FiniteDifference.thetaStep M A θ Δt f₀ f₁ ξ :=
  (FiniteDifference.eq_thetaStep_iff_divided
    (FiniteDifference.isUnit_add_smul_of_posDef hM hA (mul_nonneg hθ hΔt.le)) hΔt.ne'
    f₀ f₁ ξ ξ').symm

omit [Fintype ι] in
/-- **The matrix of the θ-method's linear system is symmetric positive definite**
([quarteroni2000numerical] §13.3, `K = Δt⁻¹ M + θ A_fe`), which is what makes its Cholesky
factorization available once and for all. -/
theorem equation_13_16_posDef {M A : Matrix ι ι ℝ} (hM : M.PosDef)
    (hA : A.PosDef) {θ Δt : ℝ} (hθ : 0 ≤ θ) (hΔt : 0 < Δt) :
    (Δt⁻¹ • M + θ • A).PosDef :=
  (hM.smul (inv_pos.2 hΔt)).add_posSemidef (hA.posSemidef.smul hθ)

/-- The mass matrix of the uniform-mesh piecewise linear finite element space of
[quarteroni2000numerical] (12.57), `M = (h/6) tridiag(1, 4, 1)` with `h = 1/n`: `2h/3` on the
diagonal and `h/6` on the two neighbouring diagonals. -/
def massMatrix (n : ℕ) : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ :=
  (1 / (6 * (n : ℝ))) • Matrix.symmTridiagonalToeplitz (n - 1) 1 4

/-- The mass matrix of the uniform-mesh piecewise linear space is symmetric positive definite:
`tridiag(1, 4, 1)` is strictly diagonally dominant. -/
theorem massMatrix_posDef {n : ℕ} (hn : 0 < n) : (massMatrix n).PosDef := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  exact (Matrix.posDef_symmTridiagonalToeplitz (n - 1) (by norm_num)).smul
    (div_pos one_pos (by linarith))

end MatrixForm

/-! ### The mass matrix of the uniform-mesh `P₁` space -/

section MassMatrix

variable {n : ℕ} {x : ℕ → ℝ}

/-- The mass matrix of §13.3 is the Gram matrix of the interior hat functions of the uniform
mesh, `M = (h/6) tridiag(1, 4, 1)` with `h = 1/n`. -/
theorem massMatrix_eq_gram (hx : Spline.IsPartition 0 1 n x) (hn : 1 ≤ n)
    (huni : ∀ k < n, x (k + 1) - x k = 1 / (n : ℝ)) :
    massMatrix n
      = FiniteElement.massMatrix 0 1 fun i : Fin (n - 1) ↦ FiniteElement.hatFunction hx hn
        ((i : ℕ) + 1) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [FiniteElement.massMatrix_uniform_eq hx hn (by positivity) huni, massMatrix]
  congr 1
  field_simp

/-- **The mass matrix is the matrix of the `L²` products of the hat functions**
([quarteroni2000numerical] §13.3, `m_ij = ∫₀¹ φ_j φ_i`): on the uniform mesh
`∫ φ_i² = 2h/3`, `∫ φ_i φ_{i±1} = h/6` and `∫ φ_i φ_j = 0` for `|i - j| ≥ 2`, which is
`M = (h/6) tridiag(1, 4, 1)`.

**Erratum**: the hint of Exercise 13.2 prints `m_ij = (h/6)·{1/2 (i ≠ j), 1 (i = j)}`; the
correct values are those above. -/
theorem massMatrix_apply_eq_integral (hx : Spline.IsPartition 0 1 n x) (hn : 1 ≤ n)
    (huni : ∀ k < n, x (k + 1) - x k = 1 / (n : ℝ)) (i j : Fin (n - 1)) :
    massMatrix n i j = ∫ t in Set.Ioo (0 : ℝ) 1,
      FiniteElement.hatFun n x ((j : ℕ) + 1) t * FiniteElement.hatFun n x ((i : ℕ) + 1) t := by
  rw [massMatrix_eq_gram hx hn huni, FiniteElement.massMatrix, FiniteElement.stiffnessMatrix_apply,
    FiniteElement.form_apply_hatFunction hx hn 0 0 1 ((i : ℕ) + 1) ((j : ℕ) + 1)]
  refine setIntegral_congr_fun measurableSet_Ioo fun t _ ↦ ?_
  simp [FiniteElement.hatFormIntegrand]

/-- **Exercise 13.2, mass lumping**: the composite trapezoidal rule (9.11) on the nodes `x_k`
applied to `∫₀¹ φ_j φ_i` gives `h ∑_k φ_j(x_k) φ_i(x_k) = h δ_{ij}`, so the lumped mass matrix is
`M̃ = h · I`, which is nonsingular; the exact integrals are those of
`massMatrix_apply_eq_integral`. -/
theorem exercise_13_2 (hx : Spline.IsPartition 0 1 n x) (hn : 1 ≤ n) {h : ℝ}
    (hxu : ∀ k ≤ n, x k = (k : ℝ) * h) (i j : Fin (n - 1)) :
    Quadrature.trapezoidSum (fun t ↦ FiniteElement.hatFun n x ((j : ℕ) + 1) t
        * FiniteElement.hatFun n x ((i : ℕ) + 1) t) 0 h n
      = if i = j then h else 0 := by
  have hI : (i : ℕ) + 1 < n := by have := i.isLt; omega
  have hJ : (j : ℕ) + 1 < n := by have := j.isLt; omega
  have hnode : ∀ k : ℕ, k ≤ n → ∀ m : ℕ,
      FiniteElement.hatFun n x m ((0 : ℝ) + (k : ℝ) * h) = if m = k then 1 else 0 := by
    intro k hk m
    rw [show (0 : ℝ) + (k : ℝ) * h = x k by rw [hxu k hk]; ring]
    exact FiniteElement.hatFun_apply_node hx hn hk
  have hterm : ∀ k ∈ Finset.range n,
      h / 2 * (FiniteElement.hatFun n x ((j : ℕ) + 1) ((0 : ℝ) + (k : ℝ) * h)
          * FiniteElement.hatFun n x ((i : ℕ) + 1) ((0 : ℝ) + (k : ℝ) * h)
        + FiniteElement.hatFun n x ((j : ℕ) + 1) ((0 : ℝ) + ((k : ℝ) + 1) * h)
          * FiniteElement.hatFun n x ((i : ℕ) + 1) ((0 : ℝ) + ((k : ℝ) + 1) * h))
      = h / 2 * ((if (j : ℕ) + 1 = k then (1 : ℝ) else 0)
            * (if (i : ℕ) + 1 = k then (1 : ℝ) else 0)
          + (if (j : ℕ) + 1 = k + 1 then (1 : ℝ) else 0)
            * (if (i : ℕ) + 1 = k + 1 then (1 : ℝ) else 0)) := by
    intro k hk
    have hkn : k ≤ n := le_of_lt (Finset.mem_range.1 hk)
    have hk1 : k + 1 ≤ n := Finset.mem_range.1 hk
    have hcast : (0 : ℝ) + ((k : ℝ) + 1) * h = (0 : ℝ) + ((k + 1 : ℕ) : ℝ) * h := by
      push_cast; ring
    rw [hnode k hkn, hnode k hkn, hcast, hnode (k + 1) hk1, hnode (k + 1) hk1]
  rw [Quadrature.trapezoidSum, Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    Finset.sum_add_distrib]
  by_cases hij : i = j
  · subst hij
    have hc1 : ∀ k ∈ Finset.range n, ((if (i : ℕ) + 1 = k then (1 : ℝ) else 0)
        * (if (i : ℕ) + 1 = k then (1 : ℝ) else 0)) = if (i : ℕ) + 1 = k then (1 : ℝ) else 0 :=
      fun k _ ↦ by split_ifs <;> ring
    have hc2 : ∀ k ∈ Finset.range n, ((if (i : ℕ) + 1 = k + 1 then (1 : ℝ) else 0)
        * (if (i : ℕ) + 1 = k + 1 then (1 : ℝ) else 0)) = if (i : ℕ) = k then (1 : ℝ) else 0 := by
      intro k _
      by_cases hk : (i : ℕ) = k
      · simp [hk]
      · simp [hk]
    have e1 : ∑ k ∈ Finset.range n, (if (i : ℕ) + 1 = k then (1 : ℝ) else 0)
        * (if (i : ℕ) + 1 = k then (1 : ℝ) else 0) = 1 := by
      rw [Finset.sum_congr rfl hc1,
        Finset.sum_ite_eq (Finset.range n) ((i : ℕ) + 1) (fun _ ↦ (1 : ℝ))]
      simp [Finset.mem_range, hI]
    have e2 : ∑ k ∈ Finset.range n, (if (i : ℕ) + 1 = k + 1 then (1 : ℝ) else 0)
        * (if (i : ℕ) + 1 = k + 1 then (1 : ℝ) else 0) = 1 := by
      rw [Finset.sum_congr rfl hc2,
        Finset.sum_ite_eq (Finset.range n) ((i : ℕ)) (fun _ ↦ (1 : ℝ))]
      simp [Finset.mem_range]
      omega
    rw [e1, e2]
    simp
    ring
  · have e0 : ∀ k ∈ Finset.range n, ((if (j : ℕ) + 1 = k then (1 : ℝ) else 0)
        * (if (i : ℕ) + 1 = k then (1 : ℝ) else 0)) = 0 := by
      intro k _
      have : ¬ ((j : ℕ) + 1 = k ∧ (i : ℕ) + 1 = k) := by
        rintro ⟨h1, h2⟩
        exact hij (Fin.ext (by omega))
      split_ifs with a1 a2 <;> simp_all
    have e1 : ∀ k ∈ Finset.range n, ((if (j : ℕ) + 1 = k + 1 then (1 : ℝ) else 0)
        * (if (i : ℕ) + 1 = k + 1 then (1 : ℝ) else 0)) = 0 := by
      intro k _
      have : ¬ ((j : ℕ) + 1 = k + 1 ∧ (i : ℕ) + 1 = k + 1) := by
        rintro ⟨h1, h2⟩
        exact hij (Fin.ext (by omega))
      split_ifs with a1 a2 <;> simp_all
    rw [Finset.sum_congr rfl e0, Finset.sum_congr rfl e1]
    simp [hij]

end MassMatrix

/-! ### The eigenvalues of the pencil `(A_fe, M)` (§13.3.1) -/

section Pencil

open scoped Real

/-- The stiffness matrix of the heat form on the uniform-mesh piecewise linear space,
`A_fe = (ν/h) tridiag(-1, 2, -1)` with `h = 1/n` ([quarteroni2000numerical] §13.3). -/
noncomputable def heatStiffnessMatrix (ν : ℝ) (n : ℕ) :
    Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ :=
  (ν * (n : ℝ)) • Matrix.symmTridiagonalToeplitz (n - 1) (-1) 2

/-- The stiffness matrix of §13.3 is the Gram matrix of the interior hat functions for the heat
form `a(u, v) = ν ∫ u' v'` on the uniform mesh. -/
theorem heatStiffnessMatrix_eq_gram {n : ℕ} {x : ℕ → ℝ} (hx : Spline.IsPartition 0 1 n x)
    (hn : 1 ≤ n) (huni : ∀ k < n, x (k + 1) - x k = 1 / (n : ℝ)) (ν : ℝ) :
    heatStiffnessMatrix ν n
      = FiniteElement.stiffnessMatrix 0 1 (EllipticInterval.constLinf 0 1 ν)
        (EllipticInterval.constLinf 0 1 0) (EllipticInterval.constLinf 0 1 0)
        fun i : Fin (n - 1) ↦ FiniteElement.hatFunction hx hn ((i : ℕ) + 1) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [FiniteElement.stiffnessMatrix_uniform_eq hx hn (by positivity) huni ν 0 0,
    heatStiffnessMatrix]
  simp only [zero_div, zero_mul, zero_smul, add_zero]
  congr 1
  field_simp

/-- The difference of two scaled symmetric tridiagonal Toeplitz matrices is one again. -/
theorem smul_sub_smul_symmTridiagonalToeplitz (N : ℕ) (c d a b a' b' : ℝ) :
    c • Matrix.symmTridiagonalToeplitz N a b - d • Matrix.symmTridiagonalToeplitz N a' b'
      = Matrix.symmTridiagonalToeplitz N (c * a - d * a') (c * b - d * b') := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.symmTridiagonalToeplitz_apply']
  split_ifs <;> ring

/-- `0` is an eigenvalue of a matrix exactly when the matrix is singular. -/
theorem hasEigenvalue_zero_iff {N : ℕ} (T : Matrix (Fin N) (Fin N) ℝ) :
    Module.End.HasEigenvalue (Matrix.toEuclideanLin T) 0
      ↔ ∃ ξ : Fin N → ℝ, ξ ≠ 0 ∧ T *ᵥ ξ = 0 := by
  constructor
  · intro hT
    obtain ⟨v, hv, hv0⟩ := hT.exists_hasEigenvector
    rw [Module.End.mem_eigenspace_iff, zero_smul] at hv
    refine ⟨WithLp.ofLp v, fun hc ↦ hv0 ?_, ?_⟩
    · exact (WithLp.ofLp_eq_zero (p := 2)).1 hc
    · have := congrArg (WithLp.ofLp (p := 2)) hv
      rwa [Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_zero] at this
  · rintro ⟨ξ, hξ, hT⟩
    refine Module.End.hasEigenvalue_of_hasEigenvector
      (x := WithLp.toLp 2 ξ) ⟨?_, fun hc ↦ hξ ?_⟩
    · rw [Module.End.mem_eigenspace_iff, zero_smul, Matrix.toEuclideanLin_toLp, hT]
      rfl
    · exact (WithLp.toLp_eq_zero (p := 2)).1 hc

/-- **The eigenvalues of the pencil `(A_fe, M)`** ([quarteroni2000numerical] §13.3.1): on the
uniform mesh with `h = 1/n`, `λ` is a generalized eigenvalue of `A_fe ξ = λ M ξ` exactly when
`λ = (6ν/h²)(1 - cos θ_i)/(2 + cos θ_i)` for one of the angles `θ_i = i π h`,
`i = 1, …, n - 1`. Both matrices are `Matrix.symmTridiagonalToeplitz`, so their difference
`A_fe - λ M` is one too, and it is singular exactly when one of the cosine eigenvalues of
`Matrix.symmTridiagonalToeplitz` vanishes. -/
theorem pencil_hasEigenvalue_iff {n : ℕ} (hn : 1 ≤ n) (ν : ℝ) (lam : ℝ) :
    (∃ ξ : Fin (n - 1) → ℝ, ξ ≠ 0 ∧
        heatStiffnessMatrix ν n *ᵥ ξ = lam • (massMatrix n *ᵥ ξ))
      ↔ ∃ k : Fin (n - 1), lam = 6 * ν * (n : ℝ) ^ 2
        * (1 - Real.cos (((k : ℕ) + 1 : ℝ) * π / (n : ℝ)))
        / (2 + Real.cos (((k : ℕ) + 1 : ℝ) * π / (n : ℝ))) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
    rw [Nat.cast_sub hn, Nat.cast_one]; ring
  set A := -(ν * (n : ℝ)) - lam * (1 / (6 * (n : ℝ))) with hA
  set B := 2 * (ν * (n : ℝ)) - 4 * (lam * (1 / (6 * (n : ℝ)))) with hB
  have hdiff : heatStiffnessMatrix ν n - lam • massMatrix n
      = Matrix.symmTridiagonalToeplitz (n - 1) A B := by
    rw [heatStiffnessMatrix, massMatrix, smul_smul,
      smul_sub_smul_symmTridiagonalToeplitz (n - 1) (ν * (n : ℝ)) (lam * (1 / (6 * (n : ℝ))))
        (-1) 2 1 4]
    congr 1 <;> [rw [hA]; rw [hB]] <;> ring
  have hiff : (∃ ξ : Fin (n - 1) → ℝ, ξ ≠ 0 ∧
      heatStiffnessMatrix ν n *ᵥ ξ = lam • (massMatrix n *ᵥ ξ))
      ↔ ∃ ξ : Fin (n - 1) → ℝ, ξ ≠ 0 ∧
        Matrix.symmTridiagonalToeplitz (n - 1) A B *ᵥ ξ = 0 := by
    refine exists_congr fun ξ ↦ and_congr_right fun _ ↦ ?_
    have hsm : (lam • massMatrix n) *ᵥ ξ = lam • (massMatrix n *ᵥ ξ) := by
      ext i
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    rw [← hdiff, Matrix.sub_mulVec, hsm, sub_eq_zero]
  rw [hiff, ← hasEigenvalue_zero_iff,
    Matrix.symmTridiagonalToeplitz_hasEigenvalue_iff A B 0]
  simp only [hcast]
  refine exists_congr fun k ↦ ?_
  set c := Real.cos (((k : ℕ) + 1 : ℝ) * π / (n : ℝ)) with hc
  have hcpos : 0 < 2 + c := by
    have := Real.neg_one_le_cos (((k : ℕ) + 1 : ℝ) * π / (n : ℝ))
    rw [← hc] at this
    linarith
  constructor
  · intro heq
    rw [hB, hA] at heq
    field_simp at heq ⊢
    nlinarith [heq]
  · intro heq
    rw [hB, hA, heq]
    field_simp
    ring

/-- **The inverse estimate of §13.3.1** (quoted there from [QV94] §6.3.2): on the uniform mesh
with `n ≥ 2`, every eigenvalue of the pencil is at most `12 ν h^{-2}`, and one of them is at
least `3 ν h^{-2}`; so the largest eigenvalue `λ_h^{N_h}` satisfies
`3 ν h^{-2} ≤ λ_h^{N_h} ≤ 12 ν h^{-2}`. The book prints `λ_h^{N_h} = c₂ h^{-2}` for the upper
bound; read `≤`. -/
theorem pencil_maxEigenvalue_bounds {n : ℕ} (hn : 2 ≤ n) {ν : ℝ} (hν : 0 < ν) :
    (∀ lam : ℝ, (∃ ξ : Fin (n - 1) → ℝ, ξ ≠ 0 ∧
        heatStiffnessMatrix ν n *ᵥ ξ = lam • (massMatrix n *ᵥ ξ)) →
      lam ≤ 12 * ν * (n : ℝ) ^ 2) ∧
    ∃ lam : ℝ, (∃ ξ : Fin (n - 1) → ℝ, ξ ≠ 0 ∧
        heatStiffnessMatrix ν n *ᵥ ξ = lam • (massMatrix n *ᵥ ξ)) ∧
      3 * ν * (n : ℝ) ^ 2 ≤ lam := by
  have hn1 : 1 ≤ n := by omega
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  constructor
  · intro lam hlam
    obtain ⟨k, rfl⟩ := (pencil_hasEigenvalue_iff hn1 ν lam).1 hlam
    set θ := ((k : ℕ) + 1 : ℝ) * π / (n : ℝ) with hθ
    have hcpos : 0 < 2 + Real.cos θ := by
      have := Real.neg_one_le_cos θ
      linarith
    rw [div_le_iff₀ hcpos]
    have h1 := Real.neg_one_le_cos θ
    nlinarith [mul_nonneg (mul_nonneg hν.le (sq_nonneg ((n : ℝ))))
      (by linarith : (0 : ℝ) ≤ 1 + Real.cos θ)]
  · have hk : (n - 2 : ℕ) < n - 1 := by omega
    refine ⟨_, (pencil_hasEigenvalue_iff hn1 ν _).2 ⟨⟨n - 2, hk⟩, rfl⟩, ?_⟩
    have hval : (((⟨n - 2, hk⟩ : Fin (n - 1)) : ℕ) + 1 : ℝ) * π / (n : ℝ)
        = π - π / (n : ℝ) := by
      rw [Fin.val_mk]
      have : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
        rw [Nat.cast_sub (by omega)]; norm_num
      rw [this]
      field_simp
      ring
    rw [hval, Real.cos_pi_sub]
    set c := Real.cos (π / (n : ℝ)) with hc
    have hcnn : 0 ≤ c := by
      rw [hc]
      have hpi := Real.pi_pos
      have hpos : (0 : ℝ) < π / (n : ℝ) := by positivity
      refine Real.cos_nonneg_of_mem_Icc ⟨by linarith, ?_⟩
      rw [div_le_div_iff₀ hn' (by norm_num)]
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith [Real.pi_pos]
    have hc1 : c ≤ 1 := Real.cos_le_one _
    have hden : 0 < 2 + -c := by linarith
    rw [le_div_iff₀ hden]
    nlinarith [mul_nonneg (mul_nonneg hν.le (sq_nonneg ((n : ℝ)))) hcnn,
      mul_nonneg (mul_nonneg hν.le (sq_nonneg ((n : ℝ)))) (by linarith : (0 : ℝ) ≤ 1 - c)]

end Pencil

/-! ### The θ-method on the Galerkin problem (13.17)–(13.21) -/

section ThetaMethod

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **The θ-method on the Galerkin problem** ([quarteroni2000numerical] (13.17)):
`⟪(u^{k+1} - u^k)/Δt, v⟫ + a(θ u^{k+1} + (1 - θ) u^k, v) = θ F^{k+1}(v) + (1 - θ) F^k(v)` for
every `v ∈ V_h`. Stated as a relation between consecutive iterates, so that the implicit cases
need no inverse. -/
def equation_13_17 (a : SesqForm ℝ V) (θ Δt : ℝ) (F₀ F₁ : V →L[ℝ] ℝ) (u u' : V) : Prop :=
  Variational.IsThetaStep a θ Δt F₀ F₁ u u'

/-- **(13.17) in coordinates is (13.16)** ([quarteroni2000numerical] (13.17) ⟺ (13.16)): for a
basis `φ` of `V_h`, a positive form, `θ ≥ 0` and `Δt > 0`, the θ-step of the Galerkin problem is
the matrix θ-step of the coordinate vectors for the mass and stiffness matrices. -/
theorem equation_13_17_iff_thetaStep [FiniteDimensional ℝ V] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (φ : Module.Basis ι ℝ V) (a : SesqForm ℝ V) {θ Δt : ℝ} (hθ : 0 ≤ θ)
    (hΔt : 0 < Δt) (hpos : a.IsCoerciveWith 0) (F₀ F₁ : V →L[ℝ] ℝ) (u u' : V) :
    equation_13_17 a θ Δt F₀ F₁ u u' ↔
      φ.equivFun u' = FiniteDifference.thetaStep (SesqForm.gramMatrix (innerSL ℝ) φ)
        (a.gramMatrix φ) θ Δt (fun i => F₀ (φ i)) (fun i => F₁ (φ i)) (φ.equivFun u) :=
  Variational.IsThetaStep.iff_thetaStep φ a hθ hΔt hpos F₀ F₁ u u'

/-- **Exercise 3** ([quarteroni2000numerical] Exercise 13.3, the inequality of its hint):
`⟪u - v, u⟫ ≥ ½ (‖u‖²_{L²} - ‖v‖²_{L²})`, which is what turns the tested backward Euler step
into (13.19). -/
theorem exercise_13_3 (u v : V) : (1 / 2 : ℝ) * (‖u‖ ^ 2 - ‖v‖ ^ 2) ≤ ⟪u - v, u⟫ :=
  Variational.half_norm_sq_sub_le_inner_sub u v

/-- **(13.19)** ([quarteroni2000numerical] (13.19)): one source-free backward Euler step
(`θ = 1`) satisfies `‖u^{k+1}‖² + 2 Δt a(u^{k+1}, u^{k+1}) ≤ ‖u^k‖²`. For the heat form the
middle term is `2 ν Δt ‖∂ₓ u^{k+1}‖²_{L²}` by (13.18). -/
theorem equation_13_19 {a : SesqForm ℝ V} {Δt : ℝ} {u u' : V}
    (h : equation_13_17 a 1 Δt 0 0 u u') (hΔt : 0 < Δt) :
    ‖u'‖ ^ 2 + 2 * Δt * a u' u' ≤ ‖u‖ ^ 2 :=
  h.norm_sq_add_two_mul_le hΔt

/-- **(13.20)** ([quarteroni2000numerical] (13.20)): telescoping (13.19) gives, for every `n`,
`‖u^n‖² + 2 Δt ∑_{k<n} a(u^{k+1}, u^{k+1}) ≤ ‖u^0‖²` — the scheme is unconditionally stable. -/
theorem equation_13_20 {a : SesqForm ℝ V} {Δt : ℝ} {u : ℕ → V} {n : ℕ} (hΔt : 0 < Δt)
    (h : ∀ k < n, equation_13_17 a 1 Δt 0 0 (u k) (u (k + 1))) :
    ‖u n‖ ^ 2 + 2 * Δt * ∑ k ∈ Finset.range n, a (u (k + 1)) (u (k + 1)) ≤ ‖u 0‖ ^ 2 :=
  Variational.IsThetaStep.norm_sq_add_sum_le hΔt h

/-- **(13.21)** ([quarteroni2000numerical] (13.21)): the same estimate with sources, for an
`L²`-coercive form, `‖u^n‖² + Δt ∑_{k<n} a(u^{k+1}, u^{k+1}) ≤ C (‖u^0‖² + ∑_{k<n} Δt ‖F^{k+1}‖²)`
with `C = max 1 α⁻¹` independent of `h` and `Δt`. The book's factor `2` on the form terms becomes
`1` because the source is absorbed against half of the coercive term. -/
theorem equation_13_21 {a : SesqForm ℝ V} {Δt : ℝ} {u : ℕ → V} {F : ℕ → V →L[ℝ] ℝ} {n : ℕ}
    (hΔt : 0 < Δt) {α : ℝ} (hα : 0 < α) (hcoer : a.IsCoerciveWith α)
    (h : ∀ k < n, equation_13_17 a 1 Δt (F k) (F (k + 1)) (u k) (u (k + 1))) :
    ‖u n‖ ^ 2 + Δt * ∑ k ∈ Finset.range n, a (u (k + 1)) (u (k + 1))
      ≤ ‖u 0‖ ^ 2 + α⁻¹ * ∑ k ∈ Finset.range n, Δt * ‖F (k + 1)‖ ^ 2 :=
  Variational.IsThetaStep.norm_sq_add_sum_le_of_coercive hΔt hα hcoer h

/-- **Remark 13.1** ([quarteroni2000numerical] Remark 13.1): (13.20) holds for any bilinear form
that is coercive in the `L²` norm, with `ν ‖∂ₓ u^{k+1}‖²` replaced by `α ‖u^{k+1}‖²`:
`‖u^n‖² + 2 α Δt ∑_{k<n} ‖u^{k+1}‖² ≤ ‖u^0‖²`. Continuity of the form is not needed. -/
theorem remark_13_1 {a : SesqForm ℝ V} {Δt : ℝ} {u : ℕ → V} {n : ℕ} (hΔt : 0 < Δt) {α : ℝ}
    (hcoer : a.IsCoerciveWith α)
    (h : ∀ k < n, equation_13_17 a 1 Δt 0 0 (u k) (u (k + 1))) :
    ‖u n‖ ^ 2 + 2 * α * Δt * ∑ k ∈ Finset.range n, ‖u (k + 1)‖ ^ 2 ≤ ‖u 0‖ ^ 2 := by
  have hmain := equation_13_20 hΔt h
  have hsum : ∑ k ∈ Finset.range n, α * ‖u (k + 1)‖ ^ 2
      ≤ ∑ k ∈ Finset.range n, a (u (k + 1)) (u (k + 1)) :=
    Finset.sum_le_sum fun k _ => hcoer (u (k + 1))
  rw [← Finset.mul_sum] at hsum
  nlinarith [mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ 2 * Δt)]

/-- **Exercise 4** ([quarteroni2000numerical] Exercise 13.4): the estimate (13.21) for any form
coercive in the `L²` norm with constant `α`, with `ν ‖∂ₓ u^{k+1}‖²` replaced by `α ‖u^{k+1}‖²`.
Only coercivity is used; the continuity (12.54) of the form plays no role. -/
theorem exercise_13_4 {a : SesqForm ℝ V} {Δt : ℝ} {u : ℕ → V} {F : ℕ → V →L[ℝ] ℝ} {n : ℕ}
    (hΔt : 0 < Δt) {α : ℝ} (hα : 0 < α) (hcoer : a.IsCoerciveWith α)
    (h : ∀ k < n, equation_13_17 a 1 Δt (F k) (F (k + 1)) (u k) (u (k + 1))) :
    ‖u n‖ ^ 2 + α * Δt * ∑ k ∈ Finset.range n, ‖u (k + 1)‖ ^ 2
      ≤ ‖u 0‖ ^ 2 + α⁻¹ * ∑ k ∈ Finset.range n, Δt * ‖F (k + 1)‖ ^ 2 := by
  have hmain := equation_13_21 hΔt hα hcoer h
  have hsum : ∑ k ∈ Finset.range n, α * ‖u (k + 1)‖ ^ 2
      ≤ ∑ k ∈ Finset.range n, a (u (k + 1)) (u (k + 1)) :=
    Finset.sum_le_sum fun k _ => hcoer (u (k + 1))
  rw [← Finset.mul_sum] at hsum
  nlinarith [mul_le_mul_of_nonneg_left hsum hΔt.le]

end ThetaMethod

/-! ### Eigenpairs of a form and the stability of the θ-method (Definition 13.1, (13.22)) -/

section Eigen

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Definition 13.1** ([quarteroni2000numerical] Definition 13.1): `λ` is an eigenvalue and
`w ≠ 0` an eigenvector of the bilinear form `a` when `a(w, v) = λ ⟪w, v⟫` for every `v`, the
inner product being that of `L²(0, 1)`. The book's following sentence — a symmetric coercive form
on `V = H¹₀` has an unbounded sequence of positive eigenvalues whose eigenfunctions are a basis of
`V` — is the spectral theorem for a compact resolvent and is not claimed; only the
finite-dimensional statement (13.22) is used. -/
def definition_13_1 (a : SesqForm ℝ V) (lam : ℝ) (w : V) : Prop :=
  Variational.IsFormEigenpair a lam w

/-- **(13.22), the algebraic form of the discrete eigenproblem** ([quarteroni2000numerical]
(13.22)): in a basis `φ` of `V_h`, `(λ_h, ∑_j ξ_j φ_j)` is an eigenpair of the form if and only if
`ξ ≠ 0` and `A_fe ξ = λ_h M ξ` — a generalized eigenvalue problem for the pencil `(A_fe, M)`. -/
theorem equation_13_22 {ι : Type*} [Fintype ι] (a : SesqForm ℝ V) (φ : Module.Basis ι ℝ V)
    (lam : ℝ) (ξ : ι → ℝ) :
    definition_13_1 a lam (∑ j, ξ j • φ j) ↔
      ξ ≠ 0 ∧ a.gramMatrix φ *ᵥ ξ = lam • SesqForm.gramMatrix (innerSL ℝ) φ *ᵥ ξ :=
  Variational.isFormEigenpair_iff_gramMatrix_mulVec a φ lam ξ

/-- **All the eigenvalues of a coercive form are positive** ([quarteroni2000numerical] §13.3.1,
"All the eigenvalues `λ_h^1, …, λ_h^{N_h}` are positive"). -/
theorem equation_13_22_pos {a : SesqForm ℝ V} {c : ℝ} (hc : 0 < c) (hcoer : a.IsCoerciveWith c)
    {lam : ℝ} {w : V} (h : definition_13_1 a lam w) : 0 < lam :=
  Variational.IsFormEigenpair.pos_of_coercive hc hcoer h

/-- **The eigenvectors form an `L²`-orthonormal basis** ([quarteroni2000numerical] §13.3.1, "The
corresponding eigenvectors form a basis for the subspace `V_h` and can be chosen in such a way as
to be orthonormal"), for a symmetric form on a finite-dimensional trial space. -/
theorem equation_13_22_basis [FiniteDimensional ℝ V] {a : SesqForm ℝ V} (ha : a.IsHermitian) :
    ∃ (lam : Fin (Module.finrank ℝ V) → ℝ)
      (b : OrthonormalBasis (Fin (Module.finrank ℝ V)) ℝ V), ∀ i, definition_13_1 a (lam i) (b i) :=
  Variational.exists_orthonormalBasis_isFormEigenpair ha

/-- **The θ-method in the eigenbasis** ([quarteroni2000numerical] §13.3.1, the recursion
`u_i^{k+1} = u_i^k [1 - (1 - θ) λ_h^i Δt] / [1 + θ λ_h^i Δt]`): for a symmetric form and an
eigenpair `(λ, w)`, the source-free θ-step multiplies the coordinate along `w` by the
amplification factor. -/
theorem thetaMethod_eigen_recursion {a : SesqForm ℝ V} {θ Δt : ℝ} {u u' : V}
    (h : equation_13_17 a θ Δt 0 0 u u') (ha : a.IsHermitian) {lam : ℝ} {w : V}
    (hw : definition_13_1 a lam w) (hΔt : Δt ≠ 0) (hden : 1 + θ * lam * Δt ≠ 0) :
    ⟪u', w⟫ = (1 - (1 - θ) * lam * Δt) / (1 + θ * lam * Δt) * ⟪u, w⟫ :=
  h.inner_eq_of_isFormEigenpair ha hw hΔt hden

/-- **Unconditional stability for `θ ≥ ½`** ([quarteroni2000numerical] §13.3.1, "if `θ ≥ 1/2` the
θ-method is unconditionally stable"): for a positive form and every `Δt > 0`, the source-free
θ-step is nonexpansive in the `L²` norm. No symmetry of the form is needed, where the book's
eigenbasis proof assumes it. -/
theorem thetaMethod_stable_of_half_le {a : SesqForm ℝ V} {θ Δt : ℝ} {u u' : V}
    (h : equation_13_17 a θ Δt 0 0 u u') (hθ : 1 / 2 ≤ θ) (hΔt : 0 < Δt)
    (hpos : a.IsCoerciveWith 0) : ‖u'‖ ≤ ‖u‖ :=
  h.norm_le_of_half_le hθ hΔt hpos

/-- **Conditional stability for `0 ≤ θ < ½`** ([quarteroni2000numerical] §13.3.1,
`Δt ≤ 2/((1 - 2θ) λ_h^{N_h})`): for a symmetric coercive form with largest eigenvalue `λ_max`
(an eigenvalue that bounds the quadratic form), the source-free θ-step is nonexpansive for every
datum if and only if `Δt ≤ 2 / ((1 - 2θ) λ_max)`. The book derives the strict inequalities and
concludes with `≤`; the non-strict form is the correct statement of `‖u^{k+1}‖ ≤ ‖u^k‖`. -/
theorem thetaMethod_stable_iff_of_lt_half [CompleteSpace V] {a : SesqForm ℝ V}
    (ha : a.IsHermitian) {c : ℝ} (hc : 0 < c) (hcoer : a.IsCoerciveWith c) {θ Δt : ℝ}
    (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (hΔt : 0 < Δt) {lmax : ℝ} {w₀ : V}
    (hw₀ : definition_13_1 a lmax w₀) (hle : ∀ v, a v v ≤ lmax * ‖v‖ ^ 2) :
    (∀ u u' : V, equation_13_17 a θ Δt 0 0 u u' → ‖u'‖ ≤ ‖u‖) ↔
      Δt ≤ 2 / ((1 - 2 * θ) * lmax) := by
  have hlmax : 0 < lmax := Variational.IsFormEigenpair.pos_of_coercive hc hcoer hw₀
  have hpos : 0 < (1 - 2 * θ) * lmax := by nlinarith
  change (∀ u u' : V, Variational.IsThetaStep a θ Δt 0 0 u u' → ‖u'‖ ≤ ‖u‖) ↔
    Δt ≤ 2 / ((1 - 2 * θ) * lmax)
  rw [Variational.IsThetaStep.forall_norm_le_iff_of_lt_half ha hc hcoer hθ0 hΔt hw₀ hle,
    le_div_iff₀ hpos, mul_comm Δt ((1 - 2 * θ) * lmax)]

/-- **(13.23)** ([quarteroni2000numerical] (13.23)): for `0 ≤ θ < 1/2` the θ-method on the
uniform `P₁` mesh is stable — `‖u_h^{k+1}‖ ≤ ‖u_h^k‖` for every datum — whenever
`Δt ≤ C₁(θ) h²` with `C₁(θ) = 1/(6 ν (1 - 2θ))`, because the largest eigenvalue of the pencil
satisfies `λ_h^{N_h} ≤ 12 ν h^{-2}` (`pencil_maxEigenvalue_bounds`) and the sharp condition is
`Δt ≤ 2/((1 - 2θ) λ_h^{N_h})` (`thetaMethod_stable_iff_of_lt_half`). -/
theorem equation_13_23 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] {a : SesqForm ℝ V} (ha : a.IsHermitian) {c : ℝ} (hc : 0 < c)
    (hcoer : a.IsCoerciveWith c) {θ Δt : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (hΔt : 0 < Δt)
    {lmax : ℝ} {w₀ : V} (hw₀ : definition_13_1 a lmax w₀) (hle : ∀ v, a v v ≤ lmax * ‖v‖ ^ 2)
    {ν : ℝ} (hν : 0 < ν) {n : ℕ} (hn : 1 ≤ n) (hlmax : lmax ≤ 12 * ν * (n : ℝ) ^ 2)
    (hstep : Δt ≤ 1 / (6 * ν * (1 - 2 * θ)) * (1 / (n : ℝ)) ^ 2) :
    ∀ u u' : V, equation_13_17 a θ Δt 0 0 u u' → ‖u'‖ ≤ ‖u‖ := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlmaxpos : 0 < lmax := equation_13_22_pos hc hcoer hw₀
  have hθ' : 0 < 1 - 2 * θ := by linarith
  refine (thetaMethod_stable_iff_of_lt_half ha hc hcoer hθ0 hθ hΔt hw₀ hle).2 ?_
  have hpos : 0 < (1 - 2 * θ) * lmax := by positivity
  rw [le_div_iff₀ hpos]
  have hbound : (1 - 2 * θ) * lmax ≤ (1 - 2 * θ) * (12 * ν * (n : ℝ) ^ 2) := by
    exact mul_le_mul_of_nonneg_left hlmax hθ'.le
  have hstep' : Δt * ((1 - 2 * θ) * (12 * ν * (n : ℝ) ^ 2)) ≤ 2 := by
    calc Δt * ((1 - 2 * θ) * (12 * ν * (n : ℝ) ^ 2))
        ≤ (1 / (6 * ν * (1 - 2 * θ)) * (1 / (n : ℝ)) ^ 2)
          * ((1 - 2 * θ) * (12 * ν * (n : ℝ) ^ 2)) := by
          refine mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = 2 := by field_simp; ring
  nlinarith [mul_le_mul_of_nonneg_left hbound hΔt.le]


end Eigen

section Spectral

open Polynomial

/-! ### The pseudo-spectral Galerkin approximation and (13.24) -/

/-- **`ℙ_N^0`**, the polynomials of degree at most `N` vanishing at `±1`, as a submodule of
`ℝ[X]`: the trial space of the spectral collocation method of §12.3. -/
def spectralSubmodule (N : ℕ) : Submodule ℝ ℝ[X] where
  carrier := {p | p.natDegree ≤ N ∧ p.eval (-1) = 0 ∧ p.eval 1 = 0}
  add_mem' {p q} hp hq := ⟨(natDegree_add_le p q).trans (max_le hp.1 hq.1),
    by rw [eval_add, hp.2.1, hq.2.1, add_zero], by rw [eval_add, hp.2.2, hq.2.2, add_zero]⟩
  zero_mem' := ⟨by simp, by simp, by simp⟩
  smul_mem' c {p} hp := ⟨(natDegree_smul_le c p).trans hp.1,
    by rw [eval_smul, hp.2.1, smul_zero], by rw [eval_smul, hp.2.2, smul_zero]⟩

/-- Membership of `ℙ_N^0`: degree at most `N` and vanishing at `±1`. -/
theorem mem_spectralSubmodule_iff {N : ℕ} {p : ℝ[X]} :
    p ∈ spectralSubmodule N ↔ p.natDegree ≤ N ∧ p.eval (-1) = 0 ∧ p.eval 1 = 0 := Iff.rfl

-- the nodes and weights are phantom parameters of the type, there for the inner product instance
set_option linter.unusedVariables false in
/-- **The pseudo-spectral trial space** `V_N = ℙ_N^0` of §13.3.1's "pseudo-spectral Galerkin
approximation", carrying the Legendre–Gauss–Lobatto discrete inner product `(u, v)_N` of (12.37)
in place of the `L²` inner product. The nodes and weights are parameters of the type so that the
inner product can be an instance; it is definite when they are the Gauss–Lobatto ones, which is
why the inner product space instance asks for `[Fact (IsLegendreLobatto N x w)]`. -/
def SpectralSpace (N : ℕ) (x w : Fin (N + 1) → ℝ) : Type := spectralSubmodule N

namespace SpectralSpace

variable {N : ℕ} {x w : Fin (N + 1) → ℝ}

instance : AddCommGroup (SpectralSpace N x w) :=
  inferInstanceAs (AddCommGroup (spectralSubmodule N))

instance : Module ℝ (SpectralSpace N x w) := inferInstanceAs (Module ℝ (spectralSubmodule N))

instance : Inhabited (SpectralSpace N x w) := ⟨0⟩

/-- The polynomial of an element of the trial space. -/
def poly (v : SpectralSpace N x w) : ℝ[X] := (v : spectralSubmodule N).1

theorem poly_mem (v : SpectralSpace N x w) : v.poly ∈ spectralSubmodule N :=
  (v : spectralSubmodule N).2

theorem natDegree_poly_le (v : SpectralSpace N x w) : v.poly.natDegree ≤ N := v.poly_mem.1

theorem eval_neg_one_poly (v : SpectralSpace N x w) : v.poly.eval (-1) = 0 := v.poly_mem.2.1

theorem eval_one_poly (v : SpectralSpace N x w) : v.poly.eval 1 = 0 := v.poly_mem.2.2

@[ext]
theorem ext {u v : SpectralSpace N x w} (h : u.poly = v.poly) : u = v := Subtype.ext h

/-- An element of the trial space from a polynomial of `ℙ_N^0`. -/
def mk (x w : Fin (N + 1) → ℝ) (p : ℝ[X]) (hp : p ∈ spectralSubmodule N) : SpectralSpace N x w :=
  (⟨p, hp⟩ : spectralSubmodule N)

@[simp]
theorem poly_mk (p : ℝ[X]) (hp : p ∈ spectralSubmodule N) : (mk x w p hp).poly = p := rfl

@[simp]
theorem poly_add (u v : SpectralSpace N x w) : (u + v).poly = u.poly + v.poly := rfl

@[simp]
theorem poly_smul (c : ℝ) (v : SpectralSpace N x w) : (c • v).poly = c • v.poly := rfl

@[simp]
theorem poly_zero : (0 : SpectralSpace N x w).poly = 0 := rfl

/-- The trial space is finite-dimensional: it sits inside `ℝ[X]_{< N + 1}`. -/
instance : FiniteDimensional ℝ (SpectralSpace N x w) := by
  have : FiniteDimensional ℝ (Polynomial.degreeLT ℝ (N + 1)) :=
    (Polynomial.degreeLTEquiv ℝ (N + 1)).symm.finiteDimensional
  exact Submodule.finiteDimensional_of_le (S₁ := spectralSubmodule N)
    (S₂ := Polynomial.degreeLT ℝ (N + 1)) fun p hp => mem_degreeLT.2
      ((degree_le_of_natDegree_le hp.1).trans_lt (WithBot.coe_lt_coe.2 (Nat.lt_succ_self N)))

/-- **The Gauss–Lobatto inner product** `(u, v)_N` of (12.37) on the trial space. -/
instance : Inner ℝ (SpectralSpace N x w) :=
  ⟨fun u v => Chapter12.equation_12_37 N x w (fun t => u.poly.eval t) fun t => v.poly.eval t⟩

/-- The inner product of the trial space is the discrete scalar product (12.37) of the
polynomials. -/
theorem inner_def (u v : SpectralSpace N x w) :
    ⟪u, v⟫ = Chapter12.equation_12_37 N x w (fun t => u.poly.eval t) fun t => v.poly.eval t := rfl

instance [hx : Fact (Chapter12.IsLegendreLobatto N x w)] :
    InnerProductSpace.Core ℝ (SpectralSpace N x w) where
  toInner := inferInstance
  conj_inner_symm u v := by
    simp only [conj_trivial, inner_def, Chapter12.equation_12_37]
    exact Quadrature.discreteInner_comm _ _ _ _
  re_inner_nonneg v := by
    simp only [RCLike.re_to_real, inner_def]
    exact Chapter12.equation_12_37_self_nonneg hx.out _
  add_left u v z := by
    simp only [inner_def, poly_add, eval_add, Chapter12.equation_12_37]
    exact Quadrature.discreteInner_add_left _ _ _ _ _
  smul_left u v c := by
    simp only [inner_def, poly_smul, eval_smul, smul_eq_mul, conj_trivial,
      Chapter12.equation_12_37]
    exact Quadrature.discreteInner_smul_left _ _ _ _ _
  definite v hv := by
    simp only [inner_def, Chapter12.equation_12_37] at hv
    by_contra hne
    have hp0 : v.poly ≠ 0 := fun h => hne (ext (by rw [h, poly_zero]))
    have hdeg : v.poly.degree < N + 1 :=
      (degree_le_of_natDegree_le v.natDegree_poly_le).trans_lt
        (WithBot.coe_lt_coe.2 (Nat.lt_succ_self N))
    exact (Quadrature.discreteInner_self_pos hx.out.weight_pos hx.out.injective hp0
      (by exact_mod_cast hdeg)).ne' hv

instance [Fact (Chapter12.IsLegendreLobatto N x w)] : NormedAddCommGroup (SpectralSpace N x w) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

instance [Fact (Chapter12.IsLegendreLobatto N x w)] : InnerProductSpace ℝ (SpectralSpace N x w) :=
  InnerProductSpace.ofCore _

/-- The squared norm is the discrete norm `‖v‖_N² = (v, v)_N`. -/
theorem norm_sq_eq [Fact (Chapter12.IsLegendreLobatto N x w)] (v : SpectralSpace N x w) :
    ‖v‖ ^ 2 = Chapter12.equation_12_37 N x w (fun t => v.poly.eval t) fun t => v.poly.eval t := by
  rw [← real_inner_self_eq_norm_sq, inner_def]

/-- **The pseudo-spectral bilinear form** `a_N(u, v) = ν (u', v')_N`, the discrete form of
`a(u, v) = ν ∫ u' v'`; on `ℙ_N^0` the Gauss–Lobatto rule is exact on `u' v' ∈ ℙ_{2N-2}`, so
`a_N = a` (`spectralForm_apply_eq_integral`). -/
def spectralBilin (N : ℕ) (x w : Fin (N + 1) → ℝ) (ν : ℝ) :
    SpectralSpace N x w →ₗ[ℝ] SpectralSpace N x w →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v => ν * Chapter12.equation_12_37 N x w
      (fun t => (derivative u.poly).eval t) fun t => (derivative v.poly).eval t)
    (fun u u' v => by
      simp only [poly_add, derivative_add, eval_add, Chapter12.equation_12_37,
        Quadrature.discreteInner, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun c u v => by
      simp only [poly_smul, derivative_smul, eval_smul, smul_eq_mul, Chapter12.equation_12_37,
        Quadrature.discreteInner, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun u v v' => by
      simp only [poly_add, derivative_add, eval_add, Chapter12.equation_12_37,
        Quadrature.discreteInner, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun c u v => by
      simp only [poly_smul, derivative_smul, eval_smul, smul_eq_mul, Chapter12.equation_12_37,
        Quadrature.discreteInner, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)

/-- The pseudo-spectral form as a bounded form on the trial space. -/
def spectralForm (N : ℕ) (x w : Fin (N + 1) → ℝ) [Fact (Chapter12.IsLegendreLobatto N x w)]
    (ν : ℝ) : SesqForm ℝ (SpectralSpace N x w) :=
  SesqForm.ofBilin (spectralBilin N x w ν)

/-- The pseudo-spectral form is `ν (u', v')_N`. -/
theorem spectralForm_apply [Fact (Chapter12.IsLegendreLobatto N x w)] (ν : ℝ)
    (u v : SpectralSpace N x w) :
    spectralForm N x w ν u v = ν * Chapter12.equation_12_37 N x w
      (fun t => (derivative u.poly).eval t) fun t => (derivative v.poly).eval t := rfl

/-- **The pseudo-spectral form is the exact form**: `a_N(u, v) = ν ∫_{-1}^1 u' v'`, the
Gauss–Lobatto rule being exact on `ℙ_{2N-1}`. -/
theorem spectralForm_apply_eq_integral [hx : Fact (Chapter12.IsLegendreLobatto N x w)] (ν : ℝ)
    (u v : SpectralSpace N x w) :
    spectralForm N x w ν u v =
      ν * ∫ t in (-1 : ℝ)..1, (derivative u.poly).eval t * (derivative v.poly).eval t := by
  rw [spectralForm_apply, Chapter12.equation_12_37_exact hx.out]
  rw [← natDegree_le_iff_degree_le]
  have d1 := natDegree_derivative_le u.poly
  have d2 := natDegree_derivative_le v.poly
  have hu := u.natDegree_poly_le
  have hv := v.natDegree_poly_le
  have hm := natDegree_mul_le (p := derivative u.poly) (q := derivative v.poly)
  omega

/-- The pseudo-spectral form is symmetric. -/
theorem spectralForm_isHermitian [Fact (Chapter12.IsLegendreLobatto N x w)] (ν : ℝ) :
    (spectralForm N x w ν).IsHermitian := fun u v => by
  simp only [spectralForm_apply, RCLike.conj_to_real, Chapter12.equation_12_37]
  rw [Quadrature.discreteInner_comm]

/-- **The energy of the pseudo-spectral form**: `a_N(v, v) = ν ‖v'‖²_{L²(-1,1)}`, the discrete
counterpart of (13.18). -/
theorem spectralForm_apply_self [Fact (Chapter12.IsLegendreLobatto N x w)] (ν : ℝ)
    (v : SpectralSpace N x w) :
    spectralForm N x w ν v v = ν * ∫ t in (-1 : ℝ)..1, (derivative v.poly).eval t ^ 2 := by
  rw [spectralForm_apply_eq_integral]
  congr 1
  exact intervalIntegral.integral_congr fun t _ => (sq _).symm

/-- **`L²`-coercivity of the pseudo-spectral form**: `(ν/6) ‖v‖_N² ≤ a_N(v, v)`. Poincaré's
inequality (12.16) on `(-1, 1)` gives `∫ v² ≤ 2 ∫ (v')²` for `v ∈ ℙ_N^0`, and the norm
equivalence `‖v‖_N² ≤ 3 ∫ v²` (`Chapter12.equation_12_37_norm_equiv`) converts the discrete norm.
-/
theorem spectralForm_coercive [hx : Fact (Chapter12.IsLegendreLobatto N x w)] (hN : 1 ≤ N) {ν : ℝ}
    (hν : 0 < ν) : (spectralForm N x w ν).IsCoerciveWith (ν / 6) := by
  intro v
  rw [RCLike.re_to_real, spectralForm_apply_self, norm_sq_eq]
  have h1 := (Chapter12.equation_12_37_norm_equiv hN hx.out v.natDegree_poly_le).2
  have h2 := Chapter12.poincare_poly v.eval_neg_one_poly
  nlinarith

/-- **The eigenvalues of the pseudo-spectral discretization are `O(N⁴)`** ([quarteroni2000numerical]
§13.3.1, "the largest eigenvalue of the spectral stiffness matrix grows like `O(N⁴)`"): every
eigenvalue `λ` of the form `a_N(u, v) = ν (u', v')_N` relative to `(·, ·)_N` on `ℙ_N^0`
(Definition 13.1) satisfies `λ ≤ ν N² (N + 1)²`. With `v` an eigenvector,
`λ ‖v‖_N² = a_N(v, v) = ν ‖v'‖²_{L²} ≤ ν N²(N + 1)² ‖v‖²_{L²} ≤ ν N²(N + 1)² ‖v‖_N²` by the `L²`
Markov inequality `Polynomial.integral_derivative_sq_le` and the lower half of the norm
equivalence `Chapter12.equation_12_37_norm_equiv`. The matching lower bound `c N⁴ ≤ λ_max` is not
proved (the open plan node `equation_13_24_lower`). -/
theorem spectralForm_eigenvalue_le [hx : Fact (Chapter12.IsLegendreLobatto N x w)] (hN : 1 ≤ N)
    {ν : ℝ} (hν : 0 ≤ ν) {lam : ℝ} {v : SpectralSpace N x w}
    (h : definition_13_1 (spectralForm N x w ν) lam v) :
    lam ≤ ν * ((N : ℝ) * (N + 1)) ^ 2 := by
  refine Variational.IsFormEigenpair.le_of_le (fun u => ?_) h
  rw [spectralForm_apply_self, norm_sq_eq]
  have h1 := (Chapter12.equation_12_37_norm_equiv hN hx.out u.natDegree_poly_le).1
  have h2 := Polynomial.integral_derivative_sq_le u.natDegree_poly_le
  have h3 : (0 : ℝ) ≤ ((N : ℝ) * (N + 1)) ^ 2 := sq_nonneg _
  calc ν * ∫ t in (-1 : ℝ)..1, (derivative u.poly).eval t ^ 2
      ≤ ν * (((N : ℝ) * (N + 1)) ^ 2 * ∫ t in (-1 : ℝ)..1, u.poly.eval t ^ 2) := by gcongr
    _ ≤ ν * (((N : ℝ) * (N + 1)) ^ 2 *
          Chapter12.equation_12_37 N x w (fun t => u.poly.eval t) fun t => u.poly.eval t) := by
        gcongr
    _ = _ := by ring

end SpectralSpace

/-- **(13.24), the stability condition of the θ-method for the pseudo-spectral Galerkin
approximation** ([quarteroni2000numerical] (13.24)): on `V_N = ℙ_N^0` with the Gauss–Lobatto
inner product and the form `a_N(u, v) = ν (u', v')_N`, the θ-method with `0 ≤ θ < 1/2` is stable
— `‖u_N^{k+1}‖_N ≤ ‖u_N^k‖_N` for every datum — whenever `Δt ≤ C₂(θ) N⁻⁴` with
`C₂(θ) = 1/(2ν(1 - 2θ))`, since every eigenvalue of the form is at most
`ν N²(N + 1)² ≤ 4 ν N⁴` (`SpectralSpace.spectralForm_eigenvalue_le`) and the sharp condition is
`Δt ≤ 2/((1 - 2θ) λ_max)` (`thetaMethod_stable_iff_of_lt_half`). The book's "only if" — the
necessity of `Δt ≤ C N⁻⁴` — needs the matching lower bound `λ_max ≥ c N⁴`, which is not proved
(the open plan node `equation_13_24_lower`). The book's `θ ≥ 0` is not needed for sufficiency.
For `θ ≥ 1/2` the method is unconditionally stable by `thetaMethod_stable_of_half_le`. -/
theorem equation_13_24 {N : ℕ} (hN : 1 ≤ N) {x w : Fin (N + 1) → ℝ}
    [hx : Fact (Chapter12.IsLegendreLobatto N x w)] {ν : ℝ} (hν : 0 < ν) {θ Δt : ℝ}
    (hθ : θ < 1 / 2) (hΔt : 0 < Δt)
    (hstep : Δt ≤ 1 / (2 * ν * (1 - 2 * θ)) * ((N : ℝ) ^ 4)⁻¹) :
    ∀ u u' : SpectralSpace N x w,
      equation_13_17 (SpectralSpace.spectralForm N x w ν) θ Δt 0 0 u u' → ‖u'‖ ≤ ‖u‖ := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hθ' : 0 < 1 - 2 * θ := by linarith
  -- the largest eigenvalue
  obtain ⟨lam, b, hb⟩ := equation_13_22_basis (SpectralSpace.spectralForm_isHermitian (x := x)
    (w := w) ν)
  have hcoer := SpectralSpace.spectralForm_coercive (x := x) (w := w) hN hν
  set lmax : ℝ := ν * ((N : ℝ) * (N + 1)) ^ 2 with hlmax
  -- every eigenvalue is at most `lmax`, hence so is the quadratic form
  have hle : ∀ v : SpectralSpace N x w,
      SpectralSpace.spectralForm N x w ν v v ≤ lmax * ‖v‖ ^ 2 := by
    intro v
    have hexp : v = ∑ i, ⟪b i, v⟫ • b i := (b.sum_repr' v).symm
    have hv : ∀ i, SpectralSpace.spectralForm N x w ν (b i) v = lam i * ⟪b i, v⟫ :=
      fun i => (hb i).2 v
    have hsymm := SpectralSpace.spectralForm_isHermitian (x := x) (w := w) ν
    have hform : SpectralSpace.spectralForm N x w ν v v = ∑ i, lam i * ⟪b i, v⟫ ^ 2 := by
      calc SpectralSpace.spectralForm N x w ν v v
          = SpectralSpace.spectralForm N x w ν (∑ i, ⟪b i, v⟫ • b i) v := by rw [← hexp]
        _ = ∑ i, ⟪b i, v⟫ * SpectralSpace.spectralForm N x w ν (b i) v := by
            rw [map_sum]
            simp only [FunLike.coe_sum, Finset.sum_apply, map_smul, FunLike.coe_smul,
              Pi.smul_apply, smul_eq_mul]
        _ = ∑ i, lam i * ⟪b i, v⟫ ^ 2 := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hv i]; ring
    have hnorm : ‖v‖ ^ 2 = ∑ i, ⟪b i, v⟫ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner v v]
      exact Finset.sum_congr rfl fun i _ => by rw [real_inner_comm v (b i), sq]
    rw [hform, hnorm, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    exact mul_le_mul_of_nonneg_right
      (SpectralSpace.spectralForm_eigenvalue_le hN hν.le (hb i)) (sq_nonneg _)
  have hpos : (SpectralSpace.spectralForm N x w ν).IsCoerciveWith 0 :=
    SesqForm.IsCoerciveWith.mono _ hcoer (by positivity)
  intro u u' h
  refine Variational.IsThetaStep.norm_le_of_le_of_lt_half h
    (SpectralSpace.spectralForm_isHermitian ν) hpos hle hΔt ?_
  -- `(1 - 2θ) lmax Δt ≤ 2`
  have hN4 : ((N : ℝ) * (N + 1)) ^ 2 ≤ 4 * (N : ℝ) ^ 4 := by
    have h1 : (N : ℝ) + 1 ≤ 2 * N := by linarith
    have h2 : (N : ℝ) * (N + 1) ≤ N * (2 * N) := by
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    calc ((N : ℝ) * (N + 1)) ^ 2 ≤ ((N : ℝ) * (2 * N)) ^ 2 := by gcongr
      _ = 4 * (N : ℝ) ^ 4 := by ring
  have hstep' : Δt * (2 * ν * (1 - 2 * θ)) * (N : ℝ) ^ 4 ≤ 1 := by
    have hpos4 : (0 : ℝ) < (N : ℝ) ^ 4 := by positivity
    have := mul_le_mul_of_nonneg_right hstep (by positivity : (0 : ℝ) ≤ 2 * ν * (1 - 2 * θ) * N ^ 4)
    calc Δt * (2 * ν * (1 - 2 * θ)) * (N : ℝ) ^ 4
        = Δt * (2 * ν * (1 - 2 * θ) * N ^ 4) := by ring
      _ ≤ 1 / (2 * ν * (1 - 2 * θ)) * ((N : ℝ) ^ 4)⁻¹ * (2 * ν * (1 - 2 * θ) * N ^ 4) := this
      _ = 1 := by field_simp
  calc (1 - 2 * θ) * lmax * Δt = (1 - 2 * θ) * ν * Δt * ((N : ℝ) * (N + 1)) ^ 2 := by
        rw [hlmax]; ring
    _ ≤ (1 - 2 * θ) * ν * Δt * (4 * (N : ℝ) ^ 4) := by gcongr
    _ = 2 * (Δt * (2 * ν * (1 - 2 * θ)) * (N : ℝ) ^ 4) := by ring
    _ ≤ 2 := by linarith

end Spectral

end

end QuarteroniSaccoSaleri.Chapter13

import Numlib.FiniteDifference.Parabolic

/-!
# Quarteroni–Sacco–Saleri §13.2: finite differences for the heat equation

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §13.2.

The heat equation is first discretized in space by the three-point second difference on the
uniform grid `x_i = i h`, `h = 1 / n`, which leaves the system of ordinary differential equations
(13.8) `u̇ = -ν A_fd u + f` for the `n - 1` interior values, with `A_fd = h⁻² tridiag(-1, 2, -1)`
the matrix (12.8) of chapter 12 (`laplacianFD`). Its time discretization is the θ-method
(13.9)–(13.10), which is `FiniteDifference.thetaStep` at mass matrix `1`
(`equation_13_10`, `equation_13_9_iff`).

Stability is asymptotic stability in the sense of §11.1: the source-free iterates
`u^k = (1 - ν Δt A_fd)^k u^0` (`equation_13_11_iterate`) tend to zero for every datum exactly when
the spectral radius of the iteration matrix is below one (`equation_13_11`), and the eigenvalues
`μ_i = (4 / h²) sin²(i π h / 2)` of `A_fd` (`laplacianFD_hasEigenvalue_iff`) turn that into
`Δt ν μ_max < 2` (`equation_13_11_iff`). The book reads this as `Δt < h² / (2ν)`; that condition
is *sufficient* (`equation_13_11_of_le`, even with equality) but not necessary, since
`μ_max = (4/h²) sin²((n-1)πh/2) < 4/h²` strictly — the book's "if and only if" is inexact and the
exact threshold `2 / (ν μ_max)` is slightly larger. Backward Euler is unconditionally
asymptotically stable (`backwardEuler_tendsto`).

All the work is in `Numlib/FiniteDifference/Parabolic` and
`Numlib/LinearAlgebra/Matrix/TridiagonalToeplitz`; this file is the specialization to
`M = 1`, `A = ν A_fd`.

## Conventions

The grid has `n` subintervals and `h = 1 / n`, so the unknown vector is indexed by
`Fin (n - 1)`, one component per interior node, and `(n : ℝ) = 1 / h`; the statements are written
with `n` and say in their doc comments what they are in the book's `h`. The θ-method is a
function of the previous iterate rather than a relation, since at mass matrix `1` the system
matrix `1 + ν θ Δt A_fd` is always invertible.
-/

open Set Filter Topology
open scoped Real Matrix

namespace QuarteroniSaccoSaleri.Chapter13

variable {n : ℕ}

/-! ### The finite difference Laplacian and the semi-discrete system (13.8) -/

/-- **The finite difference Laplacian** `A_fd = h⁻² tridiag(-1, 2, -1)` of order `n - 1` on the
uniform grid `x_i = i h` of `[0, 1]` with `h = 1 / n` ([quarteroni2000numerical] (12.8), used in
(13.8)). -/
noncomputable def laplacianFD (n : ℕ) : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ :=
  ((n : ℝ) ^ 2) • Matrix.symmTridiagonalToeplitz (n - 1) (-1) 2

/-- `A_fd` is symmetric positive definite. -/
theorem posDef_laplacianFD (hn : 0 < n) : (laplacianFD n).PosDef := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  exact (Matrix.posDef_symmTridiagonalToeplitz_neg_one_two (n - 1)).smul (pow_pos hn' 2)

/-- `ν A_fd` is symmetric positive definite for `ν > 0`: the stiffness matrix of (13.8). -/
theorem posDef_smul_laplacianFD (hn : 0 < n) {ν : ℝ} (hν : 0 < ν) : (ν • laplacianFD n).PosDef :=
  (posDef_laplacianFD hn).smul hν

/-- The quadratic form of `ν A_fd` is nonnegative, the hypothesis under which the θ-method's
system matrix is invertible. -/
theorem dotProduct_mulVec_smul_laplacianFD_nonneg (hn : 0 < n) {ν : ℝ} (hν : 0 < ν)
    (x : Fin (n - 1) → ℝ) : 0 ≤ x ⬝ᵥ ((ν • laplacianFD n) *ᵥ x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have h : 0 < x ⬝ᵥ ((ν • laplacianFD n) *ᵥ x) := by
      simpa using (posDef_smul_laplacianFD hn hν).dotProduct_mulVec_pos hx
    exact h.le

/-- **The semi-discrete finite difference heat equation** ([quarteroni2000numerical] (13.8)):
`u̇(t) = -ν A_fd u(t) + f(t)` on `[0, T]` with `u(0) = u₀`, the system of ordinary differential
equations left by the three-point discretization in space.  Stated as the backbone's
`FiniteDifference.IsSemidiscrete` with mass matrix `1`. -/
def equation_13_8 (n : ℕ) (ν T : ℝ) (f : ℝ → Fin (n - 1) → ℝ) (u₀ : Fin (n - 1) → ℝ)
    (u : ℝ → Fin (n - 1) → ℝ) : Prop :=
  FiniteDifference.IsSemidiscrete 1 (ν • laplacianFD n) f u₀ T u

/-- (13.8) in the book's normal form `u̇ = -ν A_fd u + f`. -/
theorem equation_13_8_iff (ν T : ℝ) (f : ℝ → Fin (n - 1) → ℝ) (u₀ : Fin (n - 1) → ℝ)
    (u : ℝ → Fin (n - 1) → ℝ) :
    equation_13_8 n ν T f u₀ u ↔
      u 0 = u₀ ∧ ∃ u' : ℝ → Fin (n - 1) → ℝ, ∀ t ∈ Icc 0 T,
        HasDerivWithinAt u (u' t) (Icc 0 T) t ∧
          u' t = -((ν • laplacianFD n) *ᵥ u t) + f t := by
  refine and_congr Iff.rfl (exists_congr fun u' => forall_congr' fun t => imp_congr_right fun _ =>
    and_congr_right fun _ => ?_)
  rw [Matrix.one_mulVec]
  constructor
  · intro h; rw [← h]; abel
  · intro h; rw [h]; abel

/-! ### The θ-method (13.9)–(13.10) -/

/-- **One step of the θ-method for (13.8)** ([quarteroni2000numerical] (13.10)):
`u^{k+1} = (1 + ν θ Δt A_fd)⁻¹ ((1 - ν (1 - θ) Δt A_fd) u^k + Δt (θ f^{k+1} + (1 - θ) f^k))`,
the backbone's `FiniteDifference.thetaStep` at mass matrix `1` and stiffness matrix `ν A_fd`. -/
noncomputable def equation_13_10 (n : ℕ) (ν θ Δt : ℝ) (f₀ f₁ u : Fin (n - 1) → ℝ) :
    Fin (n - 1) → ℝ :=
  FiniteDifference.thetaStep 1 (ν • laplacianFD n) θ Δt f₀ f₁ u

/-- **(13.9) and (13.10) are the same recursion** ([quarteroni2000numerical] (13.9) ⟺ (13.10)):
`u'` is the θ-step of `u` iff `(u' - u) / Δt = -ν A_fd (θ u' + (1 - θ) u) + θ f₁ + (1 - θ) f₀`.
The system matrix `1 + ν θ Δt A_fd` is invertible because `A_fd` is positive definite. -/
theorem equation_13_9_iff (hn : 0 < n) {ν θ Δt : ℝ} (hν : 0 < ν) (hθ : 0 ≤ θ) (hΔt : 0 < Δt)
    (f₀ f₁ u u' : Fin (n - 1) → ℝ) :
    u' = equation_13_10 n ν θ Δt f₀ f₁ u ↔
      Δt⁻¹ • (u' - u)
        = -((ν • laplacianFD n) *ᵥ (θ • u' + (1 - θ) • u)) + (θ • f₁ + (1 - θ) • f₀) := by
  have hK : IsUnit ((1 : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ) + (θ * Δt) • (ν • laplacianFD n)) :=
    FiniteDifference.isUnit_add_smul_of_posDef Matrix.PosDef.one
      (dotProduct_mulVec_smul_laplacianFD_nonneg hn hν) (mul_nonneg hθ hΔt.le)
  rw [equation_13_10, FiniteDifference.eq_thetaStep_iff_divided hK hΔt.ne', Matrix.one_mulVec]
  constructor
  · intro h; rw [← h]; abel
  · intro h; rw [h]; abel

/-! ### Asymptotic stability (13.11) -/

/-- The amplification matrix of forward Euler (`θ = 0`) at mass matrix `1` is `1 - ν Δt A_fd`. -/
theorem thetaAmplification_forwardEuler (ν Δt : ℝ) :
    FiniteDifference.thetaAmplification (1 : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ)
        (ν • laplacianFD n) 0 Δt = 1 - (ν * Δt) • laplacianFD n := by
  rw [FiniteDifference.thetaAmplification]
  simp [smul_smul, mul_comm]

/-- **The forward Euler iterates** ([quarteroni2000numerical] §13.2, the display before (13.11)):
with `f = 0` and `θ = 0`, `u^k = (1 - ν Δt A_fd)^k u^0`. -/
theorem equation_13_11_iterate (ν Δt : ℝ) (u₀ : Fin (n - 1) → ℝ) (k : ℕ) :
    (fun u => equation_13_10 n ν 0 Δt 0 0 u)^[k] u₀
      = ((1 - (ν * Δt) • laplacianFD n) ^ k) *ᵥ u₀ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, equation_13_10,
      FiniteDifference.thetaStep_zero_zero, thetaAmplification_forwardEuler,
      Matrix.mulVec_mulVec, ← pow_succ']

/-- **(13.11)** ([quarteroni2000numerical] (13.11)): the forward Euler iterates tend to zero for
every initial datum if and only if the spectral radius of `1 - ν Δt A_fd` is below one. -/
theorem equation_13_11 (ν Δt : ℝ) :
    (∀ u₀ : Fin (n - 1) → ℝ,
        Tendsto (fun k : ℕ => ((1 - (ν * Δt) • laplacianFD n) ^ k) *ᵥ u₀) atTop (𝓝 0)) ↔
      Matrix.complexSpectralRadius (1 - (ν * Δt) • laplacianFD n) < 1 :=
  (FiniteDifference.tendsto_pow_zero_iff_forall_mulVec _).symm.trans
    (Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one _)

/-- **The eigenvalues of `A_fd`** ([quarteroni2000numerical] §13.2, the display after (13.11);
chapter 12, Exercise 3): `μ_i = (4 / h²) sin²(i π h / 2)` for `i = 1, …, n - 1` and `h = 1 / n`. -/
theorem laplacianFD_hasEigenvalue_iff (hn : 0 < n) (μ : ℝ) :
    Module.End.HasEigenvalue (Matrix.toEuclideanLin (laplacianFD n)) μ ↔
      ∃ i : Fin (n - 1),
        μ = 4 * (n : ℝ) ^ 2 * Real.sin ((((i : ℕ) : ℝ) + 1) * π / (2 * n)) ^ 2 := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
    have h1 : (1 : ℕ) ≤ n := hn
    push_cast [h1]
    ring
  rw [Matrix.hasEigenvalue_toEuclideanLin_iff, laplacianFD,
    FiniteDifference.mem_spectrum_smul_symmTridiagonalToeplitz_iff (pow_pos hn' 2) μ]
  refine exists_congr fun k => ?_
  rw [hcast]
  exact ⟨fun h => by rw [h]; ring, fun h => by rw [h]; ring⟩

/-- The largest eigenvalue `μ_{n-1} = (4 / h²) sin²((n - 1) π h / 2)` of `A_fd`, `h = 1 / n`. -/
noncomputable def laplacianFDMaxEigenvalue (n : ℕ) : ℝ :=
  4 * (n : ℝ) ^ 2 * Real.sin (((n : ℝ) - 1) * π / (2 * n)) ^ 2

/-- The largest eigenvalue of `A_fd` is below `4 / h²`, since the sine is below one. -/
theorem laplacianFDMaxEigenvalue_lt (hn : 0 < n) :
    laplacianFDMaxEigenvalue n < 4 * (n : ℝ) ^ 2 := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set x : ℝ := ((n : ℝ) - 1) * π / (2 * n) with hx
  have hxlt : x < π / 2 := by
    rw [hx, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.pi_pos]
  have hx0 : 0 ≤ x := by
    have hnum : (0 : ℝ) ≤ ((n : ℝ) - 1) * π := by nlinarith [Real.pi_pos]
    rw [hx]
    positivity
  have hcos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hxlt⟩
  have hsq : Real.sin x ^ 2 < 1 := by nlinarith [Real.sin_sq_add_cos_sq x]
  have hpos : (0 : ℝ) < 4 * (n : ℝ) ^ 2 := by nlinarith [pow_pos hn' 2]
  rw [laplacianFDMaxEigenvalue, ← hx]
  linarith [mul_lt_mul_of_pos_left hsq hpos]

/-- The iteration matrix of forward Euler in the shape of the backbone theorem, at `h = 1 / n`. -/
theorem smul_laplacianFD_eq (hn : 0 < n) (ν Δt : ℝ) :
    (ν * Δt) • laplacianFD n
      = Δt • ((ν / ((1 : ℝ) / n) ^ 2) • Matrix.symmTridiagonalToeplitz (n - 1) (-1) 2) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [laplacianFD, smul_smul, smul_smul]
  congr 1
  field_simp

/-- **The exact forward Euler stability condition** ([quarteroni2000numerical] §13.2): the
spectral radius of `1 - ν Δt A_fd` is below one exactly when `Δt ν μ_max < 2`, `μ_max` the largest
eigenvalue of `A_fd`. -/
theorem equation_13_11_iff (hn : 0 < n) {ν Δt : ℝ} (hν : 0 < ν) (hΔt : 0 < Δt) :
    Matrix.complexSpectralRadius (1 - (ν * Δt) • laplacianFD n) < 1 ↔
      Δt * (ν * laplacianFDMaxEigenvalue n) < 2 := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hh : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have h1 : (1 : ℕ) ≤ n := hn
    push_cast [h1]
    ring
  have heq : Δt * (4 * ν / ((1 : ℝ) / n) ^ 2 *
        Real.sin (((n : ℝ) - 1) * π / (2 * ((n : ℝ) - 1 + 1))) ^ 2)
      = Δt * (ν * laplacianFDMaxEigenvalue n) := by
    rw [laplacianFDMaxEigenvalue, show (2 : ℝ) * ((n : ℝ) - 1 + 1) = 2 * n by ring]
    field_simp
  rw [← equation_13_11, smul_laplacianFD_eq hn,
    FiniteDifference.forwardEuler_heat_tendsto_iff (n - 1) hν hh hΔt, hcast, heq]

/-- **The book's sufficient condition** ([quarteroni2000numerical] §13.2, `Δt < h²/(2ν)`):
`Δt ≤ h² / (2ν) = 1 / (2 ν n²)` makes forward Euler asymptotically stable.  The book states this
as an equivalence; it is only sufficient, the exact threshold being `2 / (ν μ_max)` with
`μ_max < 4 / h²` (see `equation_13_11_iff` and `laplacianFDMaxEigenvalue_lt`). -/
theorem equation_13_11_of_le (hn : 0 < n) {ν Δt : ℝ} (hν : 0 < ν) (hΔt : 0 < Δt)
    (hle : Δt ≤ 1 / (2 * ν * (n : ℝ) ^ 2)) (u₀ : Fin (n - 1) → ℝ) :
    Tendsto (fun k : ℕ => ((1 - (ν * Δt) • laplacianFD n) ^ k) *ᵥ u₀) atTop (𝓝 0) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hh : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  have hle' : Δt ≤ ((1 : ℝ) / n) ^ 2 / (2 * ν) := by
    have hfa : ((1 : ℝ) / n) ^ 2 / (2 * ν) = 1 / (2 * ν * (n : ℝ) ^ 2) := by
      field_simp
    rw [hfa]
    exact hle
  rw [smul_laplacianFD_eq hn]
  exact FiniteDifference.forwardEuler_heat_tendsto_of_le (n - 1) hν hh hΔt hle' u₀

/-- **Backward Euler is unconditionally asymptotically stable** ([quarteroni2000numerical] §13.2,
the display after (13.11)): for every `ν, Δt > 0` the iterates `[(1 + ν Δt A_fd)⁻¹]^k u^0` tend to
zero, the eigenvalues `1 / (1 + ν Δt μ_i)` lying in `(0, 1)`. -/
theorem backwardEuler_tendsto (hn : 0 < n) {ν Δt : ℝ} (hν : 0 < ν) (hΔt : 0 < Δt)
    (u₀ : Fin (n - 1) → ℝ) :
    Tendsto (fun k : ℕ => (((1 + (ν * Δt) • laplacianFD n)⁻¹) ^ k) *ᵥ u₀) atTop (𝓝 0) := by
  have h := FiniteDifference.backwardEuler_tendsto (M := 1) (A := ν • laplacianFD n)
    Matrix.PosDef.one (posDef_smul_laplacianFD hn hν) hΔt u₀
  have hamp : FiniteDifference.thetaAmplification (1 : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ)
      (ν • laplacianFD n) 1 Δt = (1 + (ν * Δt) • laplacianFD n)⁻¹ := by
    rw [FiniteDifference.thetaAmplification]
    simp [smul_smul, mul_comm]
  rwa [hamp] at h

end QuarteroniSaccoSaleri.Chapter13

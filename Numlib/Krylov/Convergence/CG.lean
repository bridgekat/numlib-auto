import Numlib.Krylov.Iterate
import Numlib.Krylov.Convergence.Polynomial
import Numlib.RingTheory.Polynomial.ChebyshevMinimax
import Numlib.LinearSolve.Projection.OneDimensional

/-!
# Chebyshev convergence bounds for Galerkin (CG) and minimal-residual iterates

For symmetric `A` with `λmin ‖x‖² ≤ re ⟪A x, x⟫ ≤ λmax ‖x‖²` (`LinearMap.IsSymmetricBoundedBy`,
in any inner product space: the proofs go through the compression of `A` to `𝒦_{m+1}`) and *any*
sequence of Galerkin iterates (CG, D-Lanczos, …):
`‖x* - x_m‖_A ≤ ‖x* - x₀‖_A / T_m((λmax + λmin)/(λmax - λmin)) ≤ 2 ((√κ-1)/(√κ+1))^m ‖x* - x₀‖_A`
(Saad, *Iterative Methods*[^saad-iterative] Thm 6.29, (6.123)–(6.128);
Atkinson–Han[^atkinson-han] Thm 5.6.1; Meurant–Strakoš[^meurant-strakos] (3.9)). The
minimal-residual analogue for the residual norm, and Saad Thm 6.30 (restarted minimal-residual
iterations converge for coercive `A`).

Here `κ = λmax / λmin` is the spectral condition number and `T_m` the degree-`m` Chebyshev
polynomial of the first kind.

## References

[^saad-iterative]: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
  SIAM, 2003.
[^atkinson-han]: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
  Analysis Framework*, 3rd edition, Springer, 2009.
[^meurant-strakos]: Gérard Meurant and Zdeněk Strakoš, *The Lanczos and conjugate gradient
  algorithms in finite precision arithmetic*, Acta Numerica (2006), 471–542.
-/

open Polynomial Polynomial.Chebyshev Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {A : E →ₗ[𝕜] E} {b x₀ : E}

namespace Krylov

section Chebyshev

/-! ### The residual polynomial

`shifted m lmin lmax 0` is the Chebyshev polynomial of `[lmin, lmax]` normalized to `1` at `0`;
mapping it into `𝕜` gives the competitor polynomial of the Galerkin / minimal-residual
optimality statements. -/

variable {lmin lmax : ℝ} (hl : 0 < lmin) (hll : lmin < lmax)

private theorem notMem_Icc_zero (h : 0 < lmin) : (0 : ℝ) ∉ Set.Icc lmin lmax := fun hmem =>
  absurd hmem.1 (not_le.mpr h)

include hl hll

private theorem one_le_ratio : 1 ≤ (lmax + lmin) / (lmax - lmin) := by
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- The Chebyshev value appearing in Saad, *Iterative Methods*, (6.123) is at least `1`, in
particular positive. -/
private theorem one_le_eval_T_ratio (m : ℕ) : 1 ≤ (T ℝ m).eval ((lmax + lmin) / (lmax - lmin)) :=
  one_le_eval_T (one_le_ratio hl hll) m

/-- The minimax value of Saad, *Iterative Methods*: the sup of `|shifted|` over
`[lmin, lmax]`. -/
private theorem sSup_abs_eval_shifted_zero (m : ℕ) :
    sSup ((fun t => |(shifted m lmin lmax 0).eval t|) '' Set.Icc lmin lmax) =
      1 / (T ℝ m).eval ((lmax + lmin) / (lmax - lmin)) := by
  rw [sSup_abs_eval_shifted m hll (notMem_Icc_zero hl)]
  rw [show (lmax + lmin - 2 * 0) / (lmax - lmin) = (lmax + lmin) / (lmax - lmin) by ring_nf]
  rw [abs_of_pos (lt_of_lt_of_le zero_lt_one (one_le_eval_T_ratio hl hll m))]

/-- The geometric form of the minimax value (Saad, *Iterative Methods*, (6.128)). -/
private theorem sSup_abs_eval_shifted_le (m : ℕ) :
    sSup ((fun t => |(shifted m lmin lmax 0).eval t|) '' Set.Icc lmin lmax) ≤
      2 * ((Real.sqrt (lmax / lmin) - 1) / (Real.sqrt (lmax / lmin) + 1)) ^ m := by
  rw [sSup_abs_eval_shifted_zero hl hll]
  have hκ : 1 < lmax / lmin := (one_lt_div hl).2 hll
  have harg : (lmax / lmin + 1) / (lmax / lmin - 1) = (lmax + lmin) / (lmax - lmin) := by
    have h2 : lmax - lmin ≠ 0 := sub_ne_zero.mpr hll.ne'
    have h3 : lmax / lmin - 1 ≠ 0 := sub_ne_zero.mpr hκ.ne'
    field_simp
  rw [← harg]
  exact one_div_eval_T_le_two_mul_pow hκ m

omit hl hll

/-- The competitor polynomial over `𝕜`. -/
private noncomputable def chebPoly (𝕜 : Type*) [RCLike 𝕜] (m : ℕ) (lmin lmax : ℝ) : 𝕜[X] :=
  (shifted m lmin lmax 0).map (algebraMap ℝ 𝕜)

private theorem chebPoly_degree_le (m : ℕ) : (chebPoly 𝕜 m lmin lmax).degree ≤ m :=
  degree_map_le.trans (shifted_degree_le m lmin lmax 0)

include hl hll in
private theorem chebPoly_eval_zero (m : ℕ) : (chebPoly 𝕜 m lmin lmax).eval 0 = 1 := by
  rw [chebPoly, eval_zero_map, shifted_eval_self m hll (notMem_Icc_zero hl)]
  simp

end Chebyshev

section Symmetric

variable {lmin lmax : ℝ} (hl : 0 < lmin) (hll : lmin < lmax) (hA : A.IsSymmetricBoundedBy lmin lmax)
include hl hll hA

/-- Sharp Chebyshev form (Saad, *Iterative Methods*, (6.123)):
`‖x* - x_m‖_A ≤ ‖x* - x₀‖_A / T_m((λmax+λmin)/(λmax-λmin))`. -/
theorem IsGalerkinIterate.energyNorm_error_le_div_eval_T {m : ℕ} {x xstar : E}
    (hx : IsGalerkinIterate A b x₀ m x) (hstar : A xstar = b) :
    energyNorm A (xstar - x) ≤
      energyNorm A (xstar - x₀) / (T ℝ m).eval ((lmax + lmin) / (lmax - lmin)) := by
  have h1 := Krylov.IsGalerkinIterate.energyNorm_error_le_energyNorm_aeval
    (hA.isSymmetricCoercive hl) hx hstar (chebPoly 𝕜 m lmin lmax) (chebPoly_degree_le m)
    (chebPoly_eval_zero hl hll m)
  have h2 := hA.energyNorm_aeval_map_apply_le hl (shifted m lmin lmax 0) (xstar - x₀)
  rw [sSup_abs_eval_shifted_zero hl hll] at h2
  rw [div_eq_inv_mul, ← one_div]
  exact h1.trans h2

/-- Saad, *Iterative Methods*, Thm 6.29 / Atkinson–Han (5.6.5): with `κ = λmax / λmin`,
`‖x* - x_m‖_A ≤ 2 ((√κ - 1)/(√κ + 1))^m ‖x* - x₀‖_A`. -/
theorem IsGalerkinIterate.energyNorm_error_le {m : ℕ} {x xstar : E}
    (hx : IsGalerkinIterate A b x₀ m x) (hstar : A xstar = b) :
    energyNorm A (xstar - x) ≤
      2 * ((Real.sqrt (lmax / lmin) - 1) / (Real.sqrt (lmax / lmin) + 1)) ^ m *
        energyNorm A (xstar - x₀) := by
  have h1 := Krylov.IsGalerkinIterate.energyNorm_error_le_energyNorm_aeval
    (hA.isSymmetricCoercive hl) hx hstar (chebPoly 𝕜 m lmin lmax) (chebPoly_degree_le m)
    (chebPoly_eval_zero hl hll m)
  have h2 := hA.energyNorm_aeval_map_apply_le hl (shifted m lmin lmax 0) (xstar - x₀)
  exact h1.trans (h2.trans
    (mul_le_mul_of_nonneg_right (sSup_abs_eval_shifted_le hl hll m) (Real.sqrt_nonneg _)))

/-- Minimal-residual iterates on symmetric coercive systems: the same Chebyshev bound for the
residual norm. -/
theorem IsMinResIterate.norm_residual_le {m : ℕ} {x : E} (hx : IsMinResIterate A b x₀ m x) :
    ‖b - A x‖ ≤
      2 * ((Real.sqrt (lmax / lmin) - 1) / (Real.sqrt (lmax / lmin) + 1)) ^ m * ‖b - A x₀‖ := by
  have h1 := Krylov.IsMinResIterate.norm_residual_le_norm_aeval hx (chebPoly 𝕜 m lmin lmax)
    (chebPoly_degree_le m) (chebPoly_eval_zero hl hll m)
  have h2 := hA.norm_aeval_map_apply_le (shifted m lmin lmax 0) (b - A x₀)
  exact h1.trans (h2.trans
    (mul_le_mul_of_nonneg_right (sSup_abs_eval_shifted_le hl hll m) (norm_nonneg _)))

end Symmetric

/-- One-step comparison (Atkinson–Han (5.6.6)): `(√κ - 1)/(√κ + 1) ≤ (κ - 1)/(κ + 1)`. -/
theorem sqrt_ratio_le_ratio {κ : ℝ} (hκ : 1 ≤ κ) :
    (Real.sqrt κ - 1) / (Real.sqrt κ + 1) ≤ (κ - 1) / (κ + 1) := by
  have hs : 1 ≤ Real.sqrt κ := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hκ
  have hsq : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt (by linarith)
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_nonneg (sub_nonneg.2 hs) (by linarith : (0 : ℝ) ≤ 2 * Real.sqrt κ)]

/-- Saad, *Iterative Methods*, Thm 6.30: for a bounded coercive `A`, restarted minimal-residual
iterations (each cycle a minimal-residual iterate over `𝒦_m`, `m ≥ 1`) converge: each cycle
contracts the residual by at least `√(1 - c²/‖A‖²)`, where `c` is the coercivity constant. -/
theorem IsMinResIterate.norm_residual_le_of_isCoerciveWith {A : E →L[𝕜] E} {c : ℝ} (hc : 0 < c)
    (hA : (A : E →ₗ[𝕜] E).IsCoerciveWith c) {b x₀ x : E} {m : ℕ} (hm : 1 ≤ m)
    (hx : IsMinResIterate (A : E →ₗ[𝕜] E) b x₀ m x) :
    ‖b - A x‖ ≤ Real.sqrt (1 - c ^ 2 / ‖A‖ ^ 2) * ‖b - A x₀‖ := by
  have hmem : Projection.minResStep (A : E →ₗ[𝕜] E) b x₀ - x₀ ∈
      subspace (A : E →ₗ[𝕜] E) (b - A x₀) m := by
    have : Projection.minResStep (A : E →ₗ[𝕜] E) b x₀ - x₀ =
        (inner 𝕜 ((A : E →ₗ[𝕜] E) (b - A x₀)) (b - A x₀) /
          inner 𝕜 ((A : E →ₗ[𝕜] E) (b - A x₀)) ((A : E →ₗ[𝕜] E) (b - A x₀))) • (b - A x₀) := by
      simp [Projection.minResStep, Projection.step1]
    rw [this]
    exact Submodule.smul_mem _ _ (self_mem_subspace _ _ hm)
  exact (hx.min _ hmem).trans (Projection.norm_residual_minResStep_le hc hA b x₀)

theorem restarted_minRes_tendsto {A : E →L[𝕜] E} {c : ℝ} (hc : 0 < c)
    (hA : (A : E →ₗ[𝕜] E).IsCoerciveWith c) {b : E} {m : ℕ} (hm : 1 ≤ m) (x : ℕ → E)
    (hx : ∀ k, IsMinResIterate (A : E →ₗ[𝕜] E) b (x k) m (x (k + 1))) :
    Filter.Tendsto (fun k => ‖b - A (x k)‖) Filter.atTop (nhds 0) := by
  rcases (norm_nonneg A).eq_or_lt with hA0 | hA0
  · -- `A = 0` forces `E = 0` by coercivity, so every residual vanishes.
    have hAz : A = 0 := by rwa [eq_comm, norm_eq_zero] at hA0
    have hzero : ∀ y : E, y = 0 := by
      intro y
      have h1 := hA y
      rw [hAz] at h1
      simp only [ContinuousLinearMap.toLinearMap_zero, LinearMap.zero_apply, inner_zero_left,
        map_zero] at h1
      rw [← norm_eq_zero]
      by_contra hne
      have hpos : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg y) (Ne.symm hne)
      linarith [mul_pos hc (pow_pos hpos 2)]
    have : (fun k => ‖b - A (x k)‖) = fun _ : ℕ => (0 : ℝ) := by
      funext k
      rw [hzero b, hzero (x k)]
      simp
    rw [this]
    exact tendsto_const_nhds
  · set q := Real.sqrt (1 - c ^ 2 / ‖A‖ ^ 2) with hq
    have hq0 : 0 ≤ q := Real.sqrt_nonneg _
    have hq1 : q < 1 := by
      rw [hq, Real.sqrt_lt' one_pos]
      have : 0 < c ^ 2 / ‖A‖ ^ 2 := div_pos (pow_pos hc 2) (pow_pos hA0 2)
      nlinarith
    have hbound : ∀ k, ‖b - A (x k)‖ ≤ q ^ k * ‖b - A (x 0)‖ := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          calc ‖b - A (x (k + 1))‖ ≤ q * ‖b - A (x k)‖ :=
                IsMinResIterate.norm_residual_le_of_isCoerciveWith hc hA hm (hx k)
            _ ≤ q * (q ^ k * ‖b - A (x 0)‖) := by gcongr
            _ = q ^ (k + 1) * ‖b - A (x 0)‖ := by ring
    refine squeeze_zero (fun k => norm_nonneg _) hbound ?_
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const ‖b - A (x 0)‖

end Krylov

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import NumlibSurface.QuarteroniSaccoSaleri.Chapter07.Section03

/-!
# Quarteroni–Sacco–Saleri §7.4: applications

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §7.4.1, the nonlinear system
`F(u) = A u + φ(u) - b = 0` (7.57) of semiconductor device simulation, with
`A = (λ/h)² tridiag(-1, 2, -1)` symmetric positive definite and `φ_i(u) = 2K sinh(u_i)`, and its
variational form (7.58): the identification `F = ∇f` (`equation_7_58`), the uniform convexity of
`f` in the energy norm of Exercise 5 (`exercise_7_5`), and the unique minimizer that Property 7.10
then provides, which is the unique solution of (7.57) (`equation_7_58_existsUnique`).

The damped Newton method (7.59)–(7.61) and the nonlinear Gauss–Seidel method of §7.4.2 are
algorithms for which the text states no result; the superlinear convergence of damped Newton for
this problem is quoted from Ortega–Rheinboldt, *Iterative Solution of Nonlinear Equations in
Several Variables*, Theorem 14.4.3, and is not formalized.

## Conventions

The matrix `A` enters through `Matrix.toEuclideanLin`, as in §7.2; the quadratic part of (7.58) is
the backbone's `energyFunctional (toEuclideanLin A) b` (`equation_7_35` of §7.2), and `‖·‖_A` is
`energyNorm (toEuclideanLin A)`, the energy norm (1.28) of §1.12. Only the *shape* of `A` matters
for the results below, so `A` is an arbitrary symmetric positive definite matrix and the
discretization constants `λ`, `h` are absorbed into it.

## Readings and errata

* (7.58) is printed as `½ uᵀ A u + 2 ∑ cosh(u_i)) - bᵀ u`, with a stray parenthesis and without
  the factor `K`: the gradient of the second term must be `φ_i(u) = 2K sinh(u_i)`, so the term is
  `2K ∑ cosh(u_i)`.
* The uniform-convexity constant of Exercise 5 is `ρ = 1/2` *in the energy norm*; in the Euclidean
  norm of (7.49) it is `c/2` for any coercivity constant `c` of `A` (`exercise_7_5`, second
  clause).
-/

open Filter Matrix Metric Set Topology WithLp
open scoped InnerProductSpace

namespace QuarteroniSaccoSaleri.Chapter07

variable {n : ℕ}

/-! ### The functional (7.58) and the system (7.57) -/

/-- **The nonlinearity of (7.57)**, `φ(u)_i = 2K sinh(u_i)`. -/
noncomputable def semiconductorPhi (K : ℝ) (u : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i => 2 * K * Real.sinh (u i)

/-- The coordinates of `φ(u)`. -/
@[simp] theorem semiconductorPhi_apply (K : ℝ) (u : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    semiconductorPhi K u i = 2 * K * Real.sinh (u i) := rfl

/-- **(7.57).** The nonlinear system of semiconductor device simulation,
`F(u) = A u + φ(u) - b`. -/
noncomputable def semiconductorSystem (A : Matrix (Fin n) (Fin n) ℝ) (K : ℝ)
    (b u : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  toEuclideanLin A u + semiconductorPhi K u - b

/-- **(7.58).** The functional `f(u) = ½ uᵀ A u + 2K ∑ cosh(u_i) - bᵀ u` whose minimizer solves
(7.57); its quadratic part is the backbone's `energyFunctional (toEuclideanLin A) b` of (7.35). -/
noncomputable def semiconductorFunctional (A : Matrix (Fin n) (Fin n) ℝ) (K : ℝ)
    (b u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  energyFunctional (toEuclideanLin A) b u + 2 * K * ∑ i, Real.cosh (u i)

section

variable {A : Matrix (Fin n) (Fin n) ℝ} {K : ℝ} {b : EuclideanSpace ℝ (Fin n)}

/-- **(7.57)–(7.58).** For a symmetric `A`, the functional (7.58) is
`½ uᵀ A u + 2K ∑ cosh(u_i) - bᵀ u`, its gradient is `∇f(u) = A u + φ(u) - b = F(u)`, and hence the
zeros of the system (7.57) are exactly the critical points of (7.58).
`hasGradientAt_energyFunctional` for the quadratic part, `Real.hasDerivAt_cosh` coordinatewise for
the rest. -/
theorem equation_7_58 (hA : A.IsSymm) (u : EuclideanSpace ℝ (Fin n)) :
    semiconductorFunctional A K b u
        = (ofLp u ⬝ᵥ (A *ᵥ ofLp u)) / 2 + 2 * K * ∑ i, Real.cosh (u i) - ofLp b ⬝ᵥ ofLp u ∧
      HasGradientAt (semiconductorFunctional A K b) (semiconductorSystem A K b u) u ∧
      (semiconductorSystem A K b u = 0 ↔ IsCriticalPoint (semiconductorFunctional A K b) u) := by
  have hsymm : (toEuclideanLin A).IsSymmetric := hA.isSymmetric_toEuclideanLin
  -- the quadratic part
  have hquad : HasGradientAt (energyFunctional (toEuclideanLin A) b) (toEuclideanLin A u - b) u :=
    hasGradientAt_energyFunctional_of_finiteDimensional hsymm b u
  -- the `cosh` part
  have hcosh : HasGradientAt (fun y : EuclideanSpace ℝ (Fin n) => 2 * K * ∑ i, Real.cosh (y i))
      (semiconductorPhi K u) u := by
    have h1 : ∀ i : Fin n, HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => Real.cosh (y i))
        (Real.sinh (u i) • EuclideanSpace.proj (𝕜 := ℝ) i) u := fun i => by
      have hp : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => y i)
          (EuclideanSpace.proj (𝕜 := ℝ) i) u := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt
      exact (Real.hasDerivAt_cosh (u i)).comp_hasFDerivAt u hp
    have h2 := (HasFDerivAt.fun_sum (u := Finset.univ) fun i _ => h1 i).const_mul (2 * K)
    rw [hasGradientAt_iff_hasFDerivAt]
    refine h2.congr_fderiv ?_
    have h3 : (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) (semiconductorPhi K u)
        : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) = innerSL ℝ (semiconductorPhi K u) := by
      ext w
      simp [InnerProductSpace.toDual_apply_apply]
    rw [h3, innerSL_eq_sum_smul_proj, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]; rfl
  have hgrad : HasGradientAt (semiconductorFunctional A K b) (semiconductorSystem A K b u) u := by
    rw [hasGradientAt_iff_hasFDerivAt] at hquad hcosh ⊢
    refine (hquad.add hcosh).congr_fderiv ?_
    rw [show semiconductorSystem A K b u
        = toEuclideanLin A u - b + semiconductorPhi K u by rw [semiconductorSystem]; abel, map_add]
  refine ⟨?_, hgrad, ?_⟩
  · rw [semiconductorFunctional, (equation_7_35 (b := b) hA u).1]
    ring
  · rw [IsCriticalPoint, hgrad.gradient]

/-! ### Exercise 5: the uniform convexity of (7.58) -/

/-- The hyperbolic cosine is strictly convex: its second derivative is `cosh > 0`. -/
theorem strictConvexOn_cosh : StrictConvexOn ℝ univ Real.cosh := by
  have h2 : deriv^[2] Real.cosh = Real.cosh := by
    change deriv (deriv Real.cosh) = Real.cosh
    rw [Real.deriv_cosh, Real.deriv_sinh]
  exact strictConvexOn_of_deriv2_pos convex_univ Real.continuous_cosh.continuousOn
    fun x _ => by rw [h2]; exact Real.cosh_pos x

/-- The quadratic part of (7.58) satisfies the convexity identity exactly: the defect of a convex
combination is `½ t (1 - t) ‖u - v‖_A²`. -/
private theorem energyFunctional_combo (hsymm : (toEuclideanLin A).IsSymmetric)
    (u v : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    t * energyFunctional (toEuclideanLin A) b u
        + (1 - t) * energyFunctional (toEuclideanLin A) b v
        - energyFunctional (toEuclideanLin A) b (t • u + (1 - t) • v)
      = t * (1 - t) / 2 * ⟪toEuclideanLin A (u - v), u - v⟫_ℝ := by
  have hsw : ⟪toEuclideanLin A v, u⟫_ℝ = ⟪toEuclideanLin A u, v⟫_ℝ :=
    (hsymm v u).trans (real_inner_comm _ _)
  simp only [energyFunctional, RCLike.re_to_real, map_add, map_smul, map_sub, inner_add_left,
    inner_add_right, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real]
  rw [hsw]
  ring

/-- Convexity of `cosh`, coordinate by coordinate. -/
private theorem coshSum_combo_le {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (u v : EuclideanSpace ℝ (Fin n)) :
    ∑ i, Real.cosh ((t • u + (1 - t) • v) i)
      ≤ t * ∑ i, Real.cosh (u i) + (1 - t) * ∑ i, Real.cosh (v i) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hco : (t • u + (1 - t) • v) i = t * u i + (1 - t) * v i := by simp
  have hcv := strictConvexOn_cosh.convexOn.2 (mem_univ (u i)) (mem_univ (v i)) h0
    (by linarith : (0 : ℝ) ≤ 1 - t) (by ring)
  simp only [smul_eq_mul] at hcv
  rw [hco]
  exact hcv

/-- Strict convexity of `cosh` in the coordinate where `u` and `v` differ. -/
private theorem coshSum_combo_lt {t : ℝ} (h0 : 0 < t) (h1 : t < 1)
    {u v : EuclideanSpace ℝ (Fin n)} (huv : u ≠ v) :
    ∑ i, Real.cosh ((t • u + (1 - t) • v) i)
      < t * ∑ i, Real.cosh (u i) + (1 - t) * ∑ i, Real.cosh (v i) := by
  obtain ⟨i0, hi0⟩ : ∃ i, u i ≠ v i := by
    by_contra hc
    exact huv (by ext i; exact not_not.1 fun h => hc ⟨i, h⟩)
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_lt_sum (fun i _ => ?_) ⟨i0, Finset.mem_univ i0, ?_⟩
  · have hco : (t • u + (1 - t) • v) i = t * u i + (1 - t) * v i := by simp
    have hcv := strictConvexOn_cosh.convexOn.2 (mem_univ (u i)) (mem_univ (v i)) h0.le
      (by linarith : (0 : ℝ) ≤ 1 - t) (by ring)
    simp only [smul_eq_mul] at hcv
    rw [hco]
    exact hcv
  · have hco : (t • u + (1 - t) • v) i0 = t * u i0 + (1 - t) * v i0 := by simp
    have hcv := strictConvexOn_cosh.2 (mem_univ (u i0)) (mem_univ (v i0)) hi0 h0
      (by linarith : (0 : ℝ) < 1 - t) (by ring)
    simp only [smul_eq_mul] at hcv
    rw [hco]
    exact hcv

/-- **Exercise 5, cited in §7.4.1.** For `A` symmetric positive definite and `K > 0` the
functional (7.58) is uniformly convex on `ℝⁿ`:
`λ f(u) + (1 - λ) f(v) - f(λ u + (1 - λ) v) > ½ λ (1 - λ) ‖u - v‖_A²` for `u ≠ v` and
`0 < λ < 1`. The quadratic part contributes the right-hand side exactly and the strict convexity
of `cosh` in a coordinate where `u` and `v` differ contributes the strict inequality. In the
Euclidean norm of (7.49) this is strong convexity with `ρ = c / 2` for any coercivity constant `c`
of `A` (the text's `ρ = 1/2` is in the energy norm), which is the second clause. -/
theorem exercise_7_5 (hA : A.PosDef) (hK : 0 < K) :
    (∀ u v : EuclideanSpace ℝ (Fin n), u ≠ v → ∀ lam : ℝ, 0 < lam → lam < 1 →
        1 / 2 * lam * (1 - lam) * energyNorm (toEuclideanLin A) (u - v) ^ 2
          < lam * semiconductorFunctional A K b u
            + (1 - lam) * semiconductorFunctional A K b v
            - semiconductorFunctional A K b (lam • u + (1 - lam) • v)) ∧
      ∃ ρ > 0, IsStronglyConvexOn (semiconductorFunctional A K b) univ ρ := by
  have hAsc := (Matrix.posDef_iff_isSymmetricCoercive A).1 hA
  obtain ⟨c, hc, hcoer⟩ := hAsc.isCoercive
  have hcombo : ∀ (u v : EuclideanSpace ℝ (Fin n)) (t : ℝ),
      t * semiconductorFunctional A K b u + (1 - t) * semiconductorFunctional A K b v
          - semiconductorFunctional A K b (t • u + (1 - t) • v)
        = t * (1 - t) / 2 * ⟪toEuclideanLin A (u - v), u - v⟫_ℝ
          + 2 * K * (t * ∑ i, Real.cosh (u i) + (1 - t) * ∑ i, Real.cosh (v i)
            - ∑ i, Real.cosh ((t • u + (1 - t) • v) i)) := by
    intro u v t
    rw [semiconductorFunctional, semiconductorFunctional, semiconductorFunctional,
      ← energyFunctional_combo (b := b) hAsc.isSymmetric u v t]
    ring
  constructor
  · intro u v huv lam h0 h1
    rw [hcombo u v lam, hAsc.energyNorm_sq (u - v), RCLike.re_to_real]
    have hcosh := coshSum_combo_lt h0 h1 huv
    nlinarith [mul_pos hK (by linarith : (0 : ℝ) < lam * ∑ i, Real.cosh (u i)
      + (1 - lam) * ∑ i, Real.cosh (v i)
      - ∑ i, Real.cosh ((lam • u + (1 - lam) • v) i))]
  · refine ⟨c / 2, half_pos hc, half_pos hc, fun u _ v _ α hα => ?_⟩
    have hquad : c * ‖u - v‖ ^ 2 ≤ ⟪toEuclideanLin A (u - v), u - v⟫_ℝ := by
      have := hcoer (u - v)
      rwa [RCLike.re_to_real] at this
    have hcosh := coshSum_combo_le hα.1 hα.2 u v
    have hkey := hcombo u v α
    have h1 : (0 : ℝ) ≤ 1 - α := by linarith [hα.2]
    nlinarith [mul_nonneg (mul_nonneg hα.1 h1)
        (by linarith : (0 : ℝ) ≤ ⟪toEuclideanLin A (u - v), u - v⟫_ℝ - c * ‖u - v‖ ^ 2),
      mul_nonneg hK.le (by linarith : (0 : ℝ) ≤ α * ∑ i, Real.cosh (u i)
        + (1 - α) * ∑ i, Real.cosh (v i)
        - ∑ i, Real.cosh ((α • u + (1 - α) • v) i))]

/-- **The consequence drawn in §7.4.1.** By Exercise 5 and Property 7.10 the functional (7.58) has
exactly one minimizer `u*` on `ℝⁿ`, and the minimizers of (7.58) are exactly the solutions of the
nonlinear system (7.57); so (7.57) has exactly one solution. -/
theorem equation_7_58_existsUnique (hA : A.PosDef) (hK : 0 < K) :
    (∃! ustar : EuclideanSpace ℝ (Fin n),
        IsMinOn (semiconductorFunctional A K b) univ ustar) ∧
      ∀ ustar : EuclideanSpace ℝ (Fin n), IsMinOn (semiconductorFunctional A K b) univ ustar
        ↔ semiconductorSystem A K b ustar = 0 := by
  have hsymm : A.IsSymm := Matrix.isHermitian_iff_isSymm.1 hA.1
  have hdiff : ∀ y, DifferentiableAt ℝ (semiconductorFunctional A K b) y := fun y =>
    (hasGradientAt_iff_hasFDerivAt.1 (equation_7_58 (b := b) hsymm y).2.1).differentiableAt
  have hcont : Continuous (semiconductorFunctional A K b) :=
    continuous_iff_continuousAt.2 fun y => (hdiff y).continuousAt
  obtain ⟨⟨ρ, hρ, hsc⟩, -⟩ := (exercise_7_5 (b := b) hA hK).symm
  have hconv : ConvexOn ℝ univ (semiconductorFunctional A K b) := by
    obtain ⟨-, hsc'⟩ := (isStronglyConvexOn_iff (f := semiconductorFunctional A K b)
      convex_univ).1 hsc
    exact hsc'.convexOn fun r => by positivity
  have hmin := (property_7_10 (f := semiconductorFunctional A K b) isClosed_univ convex_univ
    univ_nonempty hsc (hcont.lowerSemicontinuous.lowerSemicontinuousOn univ)).1
  refine ⟨?_, fun ustar => ?_⟩
  · obtain ⟨w, ⟨-, hw⟩, huniq⟩ := hmin
    exact ⟨w, hw, fun y hy => huniq y ⟨mem_univ y, hy⟩⟩
  · rw [(equation_7_58 (b := b) hsymm ustar).2.2]
    refine ⟨fun h => ?_, fun h => isMinOn_of_convexOn_of_isCriticalPoint hconv hdiff h⟩
    exact property_7_4_gradient (h.isLocalMin Filter.univ_mem) (hdiff ustar)

end

end QuarteroniSaccoSaleri.Chapter07

/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import NumlibSurface.QuarteroniSaccoSaleri.Chapter07.Section03

/-!
# Quarteroni, Sacco and Saleri, Section 7.4: Applications

This module formalizes the results of Section 7.4.1 of [quarteroni2000numerical] on the nonlinear
system of semiconductor device simulation,
$$F(u) = Au + \phi(u) - b = 0, \qquad \phi_i(u) = 2K \sinh(u_i), \tag{7.57}$$
where $A = (\lambda/h)^2 \operatorname{tridiag}(-1, 2, -1)$ is symmetric positive definite and
$K > 0$. The system is the condition $\nabla f(u) = 0$ for the functional
$$f(u) = \frac{1}{2} u^T A u + 2K \sum_{i=1}^n \cosh(u_i) - b^T u. \tag{7.58}$$
By Exercise 5 of Chapter 7, $f$ is uniformly convex in the energy norm $\|\cdot\|_A$. By Property
7.10, $f$ then has exactly one minimizer, and it is the unique solution of (7.57).

The proofs use the energy functional and the energy norm of
`Numlib.Analysis.InnerProductSpace.Energy`, the strict convexity of $\cosh$, and Property 7.10 in
`NumlibSurface.QuarteroniSaccoSaleri.Chapter07.Section03`.

## Main definitions

* (7.57), `QuarteroniSaccoSaleri.Chapter07.semiconductorPhi`: the nonlinearity
  $\phi_i(u) = 2K \sinh(u_i)$.
* (7.57), `QuarteroniSaccoSaleri.Chapter07.semiconductorSystem`: the map $F(u) = Au + \phi(u) - b$.
* (7.58), `QuarteroniSaccoSaleri.Chapter07.semiconductorFunctional`: the functional $f$ of (7.58).

## Main results

* (7.57), `QuarteroniSaccoSaleri.Chapter07.semiconductorPhi_apply`: the coordinates of $\phi(u)$.
* (7.58), `QuarteroniSaccoSaleri.Chapter07.equation_7_58`: for symmetric $A$, $\nabla f = F$, so the
  solutions of (7.57) are the critical points of $f$.
* Exercise 5 of Chapter 7, `QuarteroniSaccoSaleri.Chapter07.strictConvexOn_cosh`: $\cosh$ is
  strictly convex on $\mathbb{R}$.
* Exercise 5 of Chapter 7, `QuarteroniSaccoSaleri.Chapter07.exercise_7_5`: $f$ is uniformly convex
  in the energy norm, and strongly convex in the sense of (7.49).
* Section 7.4.1, `QuarteroniSaccoSaleri.Chapter07.equation_7_58_existsUnique`: $f$ has exactly one
  minimizer, and the minimizers of $f$ are the solutions of (7.57).

## Conventions

* The matrix $A$ acts on $\mathbb{R}^n$ = `EuclideanSpace ℝ (Fin n)` through
  `Matrix.toEuclideanLin`, as in Section 7.2. The quadratic part $\frac{1}{2} u^T A u - b^T u$ of
  (7.58) is `energyFunctional (toEuclideanLin A) b`, as in (7.35), and $\|\cdot\|_A$ is
  `energyNorm (toEuclideanLin A)`, the energy norm (1.28).

## Deviations from the source

* **Generalization.** The semiconductor formulas allow arbitrary square matrices and real
  coefficients. See `QuarteroniSaccoSaleri.Chapter07.semiconductorPhi`,
  `QuarteroniSaccoSaleri.Chapter07.semiconductorPhi_apply`,
  `QuarteroniSaccoSaleri.Chapter07.semiconductorSystem`.
* **Correction.** The energy uses the missing factor K and the gradient identity holds for any
  symmetric matrix. See `QuarteroniSaccoSaleri.Chapter07.semiconductorFunctional`,
  `QuarteroniSaccoSaleri.Chapter07.equation_7_58`.
* **Generalization.** The semiconductor minimization result extends to all symmetric positive
  definite matrices. The energy-norm inequality retains coefficient one-half. See
  `QuarteroniSaccoSaleri.Chapter07.exercise_7_5`,
  `QuarteroniSaccoSaleri.Chapter07.equation_7_58_existsUnique`.
* **Section 7.4.1** (generalization). The results hold for every symmetric positive definite matrix
  $A$, not only for $(\lambda/h)^2 \operatorname{tridiag}(-1, 2, -1)$; the constants $\lambda$ and
  $h$ are absorbed into $A$. See `QuarteroniSaccoSaleri.Chapter07.equation_7_58_existsUnique`.
* **Equation (7.58)** (typo). The book prints $\frac{1}{2} u^T A u + 2 \sum \cosh(u_i)) - b^T u$,
  with a stray parenthesis and without the factor $K$; the second term is $2K \sum \cosh(u_i)$. See
  `QuarteroniSaccoSaleri.Chapter07.semiconductorFunctional`.
* **Exercise 5 of Chapter 7** (reading). The uniform convexity constant $\rho = 1/2$ is read in the
  energy norm; in the Euclidean norm of (7.49) the constant is $c/2$ for a coercivity constant $c$
  of $A$. See `QuarteroniSaccoSaleri.Chapter07.exercise_7_5`.

## Not formalized

* **Damped Newton method (7.59)–(7.61).** The book states no result of its own for it; the
  superlinear convergence for this problem is quoted from Ortega and Rheinboldt, *Iterative Solution
  of Nonlinear Equations in Several Variables*, Theorem 14.4.3.
* **Nonlinear Gauss–Seidel method of Section 7.4.2.** The book states no result for it.
-/

open Filter Matrix Metric Set Topology WithLp
open scoped InnerProductSpace

namespace QuarteroniSaccoSaleri.Chapter07

variable {n : ℕ}

/-! ### The functional (7.58) and the system (7.57) -/

/-- **Equation (7.57)** of [quarteroni2000numerical], the nonlinearity. For $K \in \mathbb{R}$ and
$u \in \mathbb{R}^n$, the vector $\phi(u) \in \mathbb{R}^n$ has the coordinates
$\phi_i(u) = 2K \sinh(u_i)$.

**Generalization.** The formula allows arbitrary real K and arbitrary real square A. The model in
the text uses positive K and a scaled tridiagonal matrix.
-/
noncomputable def semiconductorPhi (K : ℝ) (u : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i => 2 * K * Real.sinh (u i)

/-- **Equation (7.57)** of [quarteroni2000numerical], the coordinates of the nonlinearity:
$\phi(u)_i = 2K \sinh(u_i)$.

**Generalization.** The formula allows arbitrary real K and arbitrary real square A. The model in
the text uses positive K and a scaled tridiagonal matrix.
-/
@[simp] theorem semiconductorPhi_apply (K : ℝ) (u : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    semiconductorPhi K u i = 2 * K * Real.sinh (u i) := rfl

/-- **Equation (7.57)** of [quarteroni2000numerical]. For $A \in \mathbb{R}^{n \times n}$,
$K \in \mathbb{R}$ and $b \in \mathbb{R}^n$, the nonlinear system of semiconductor device
simulation is $F(u) = 0$, where
$$F(u) = Au + \phi(u) - b.$$

**Generalization.** The formula allows arbitrary real K and arbitrary real square A. The model in
the text uses positive K and a scaled tridiagonal matrix.
-/
noncomputable def semiconductorSystem (A : Matrix (Fin n) (Fin n) ℝ) (K : ℝ)
    (b u : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  toEuclideanLin A u + semiconductorPhi K u - b

/-- **Equation (7.58)** of [quarteroni2000numerical]. For $A \in \mathbb{R}^{n \times n}$,
$K \in \mathbb{R}$ and $b \in \mathbb{R}^n$, the functional is
$$f(u) = \frac{1}{2} u^T A u - b^T u + 2K \sum_{i=1}^n \cosh(u_i).$$

**Typo.** The book prints $\frac{1}{2} u^T A u + 2 \sum \cosh(u_i)) - b^T u$, with a stray
parenthesis and without the factor $K$. The gradient of the second term must be
$\phi_i(u) = 2K \sinh(u_i)$, so the term is $2K \sum \cosh(u_i)$.

The quadratic part $\frac{1}{2} u^T A u - b^T u$ is the backbone's
`energyFunctional (toEuclideanLin A) b`, as in (7.35).

**Correction.** The hyperbolic-cosine term has coefficient $2K$, required by the $2K\sinh$
nonlinearity in (7.57). The gradient identity uses any symmetric A.
-/
noncomputable def semiconductorFunctional (A : Matrix (Fin n) (Fin n) ℝ) (K : ℝ)
    (b u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  energyFunctional (toEuclideanLin A) b u + 2 * K * ∑ i, Real.cosh (u i)

section

variable {A : Matrix (Fin n) (Fin n) ℝ} {K : ℝ} {b : EuclideanSpace ℝ (Fin n)}

/-- **Equations (7.57)–(7.58)** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$ be
symmetric, $K \in \mathbb{R}$ and $b, u \in \mathbb{R}^n$. Then
$$f(u) = \frac{1}{2} u^T A u + 2K \sum_{i=1}^n \cosh(u_i) - b^T u,$$
the gradient of $f$ at $u$ is $\nabla f(u) = Au + \phi(u) - b = F(u)$, and $F(u) = 0$ if and
only if $u$ is a critical point of $f$. So the solutions of the system (7.57) are exactly the
critical points of (7.58).

The gradient of the quadratic part is `hasGradientAt_energyFunctional`, and the gradient of the
other part follows coordinatewise from `Real.hasDerivAt_cosh`. A critical point is
`QuarteroniSaccoSaleri.Chapter07.IsCriticalPoint`.

**Correction.** The hyperbolic-cosine term has coefficient $2K$, required by the $2K\sinh$
nonlinearity in (7.57). The gradient identity uses any symmetric A.
-/
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
    rw [h3, EuclideanSpace.innerSL_eq_sum_smul_proj, Finset.smul_sum]
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

/-- The hyperbolic cosine is strictly convex on $\mathbb{R}$, because its second derivative $\cosh$
is positive. This supports Exercise 5 of Chapter 7 of [quarteroni2000numerical]. -/
theorem strictConvexOn_cosh : StrictConvexOn ℝ univ Real.cosh := by
  have h2 : deriv^[2] Real.cosh = Real.cosh := by
    change deriv (deriv Real.cosh) = Real.cosh
    rw [Real.deriv_cosh, Real.deriv_sinh]
  exact strictConvexOn_of_deriv2_pos convex_univ Real.continuous_cosh.continuousOn
    fun x _ => by rw [h2]; exact Real.cosh_pos x

/-- For a symmetric $A$, the quadratic part $q$ of (7.58) satisfies $t q(u) + (1 - t) q(v) - q(tu +
(1 - t)v) = \frac{1}{2} t (1 - t) \|u - v\|_A^2$. -/
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

/-- For $0 \le t \le 1$, $\sum_i \cosh((tu + (1 - t)v)_i) \le t \sum_i \cosh(u_i) + (1 - t) \sum_i
\cosh(v_i)$. -/
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

/-- For $0 < t < 1$ and $u \neq v$, $\sum_i \cosh((tu + (1 - t)v)_i) < t \sum_i \cosh(u_i) + (1 - t)
\sum_i \cosh(v_i)$. -/
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

/-- **Exercise 5 of Chapter 7** of [quarteroni2000numerical], cited in Section 7.4.1. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite, $K > 0$ and
$b \in \mathbb{R}^n$. Then the functional $f$ of (7.58) is uniformly convex on $\mathbb{R}^n$ in
the energy norm:
$$\lambda f(u) + (1 - \lambda) f(v) - f(\lambda u + (1 - \lambda) v) > \frac{1}{2} \lambda (1 -
  \lambda) \|u - v\|_A^2$$
for all $u \neq v$ and $0 < \lambda < 1$. Moreover $f$ is strongly convex on $\mathbb{R}^n$ in
the sense of (7.49) for some $\rho > 0$.

**Reading.** The book gives the constant $\rho = 1/2$. This constant is read in the energy norm,
as in the first part. In the Euclidean norm of (7.49), the proof gives $\rho = c/2$ for a
coercivity constant $c$ of $A$; the formal statement asserts only that some $\rho > 0$ exists.

The quadratic part of $f$ gives the right-hand side exactly, and the strict convexity of $\cosh$
in a coordinate where $u$ and $v$ differ gives the strict inequality.

**Generalization.** The energy and minimizer results work for every symmetric positive definite A
and positive K. The strict inequality preserves the source's factor one-half in the energy norm and
separately proves strong convexity with a Euclidean modulus.
-/
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

/-- **Section 7.4.1** of [quarteroni2000numerical], existence and uniqueness. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite, $K > 0$ and
$b \in \mathbb{R}^n$. Then the functional $f$ of (7.58) has exactly one global minimizer $u^*$
on $\mathbb{R}^n$, and a point $u^*$ is a global minimizer of $f$ if and only if $F(u^*) = 0$.
So the system (7.57) has exactly one solution.

**Generalization.** The book takes $A = (\lambda/h)^2 \operatorname{tridiag}(-1, 2, -1)$. The
statement holds for every symmetric positive definite $A$, with the constants $\lambda$ and $h$
absorbed into $A$.

The proof combines Exercise 5 (`QuarteroniSaccoSaleri.Chapter07.exercise_7_5`) with Property
7.10 (`QuarteroniSaccoSaleri.Chapter07.property_7_10`).

**Generalization.** The energy and minimizer results work for every symmetric positive definite A
and positive K. The strict inequality preserves the source's factor one-half in the energy norm and
separately proves strong convexity with a Euclidean modulus.
-/
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

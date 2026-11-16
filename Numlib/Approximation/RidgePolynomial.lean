/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.SpecialFunctions.ChebyshevIntegral
import Numlib.Approximation.DiskQuadrature
import Numlib.RingTheory.MvPolynomial.TotalDegree

/-!
# The Logan–Shepp ridge polynomials on the unit disk

A ridge polynomial in the plane is a polynomial in one variable composed with a linear form
$x\cos\theta + y\sin\theta$. This module takes the Chebyshev polynomial $U_n$ of the second kind and
normalizes it, which gives
$$R_{n,\theta}(x, y) = \frac{1}{\sqrt{\pi}}\, U_n(x\cos\theta + y\sin\theta),$$
a polynomial of total degree at most $n$ with $L^2$ norm $1$ on the closed unit disk $\mathbb{B}_2$.
These are the polynomials of L. A. Shepp and S. Ridgway, "Fourier reconstruction of a head section"
(1974), and of B. F. Logan and L. A. Shepp, "Optimal reconstruction of a function from its
projections" (1975). The main computation of the module is the inner product
$$\int_{\mathbb{B}_2} U_n(x\cos\theta + y\sin\theta)\, U_m(x\cos\varphi + y\sin\varphi)\,d(x, y) =
  \delta_{nm}\, \frac{\pi}{n+1}\, U_n(\cos(\theta - \varphi)).$$

Since $U_n(1) = n + 1$, the value at $n = m$ and $\theta = \varphi$ is $\pi$. Since
$U_n(\cos\gamma)\sin\gamma = \sin((n+1)\gamma)$, the value is $0$ at $\theta - \varphi = k\pi/(n+1)$
for $0 < |k| \le n$. Hence the $n + 1$ ridge polynomials of degree $n$ in the equispaced directions
$\theta_k = k\pi/(n+1)$, $k = 0, \dots, n$, are orthonormal in $L^2(\mathbb{B}_2)$, and they are
orthogonal to every ridge polynomial of a different degree.

## Main definitions

* `Approximation.ridgeForm`: the linear form $x\cos\theta + y\sin\theta$, as a polynomial in two
  variables.
* `Approximation.ridgePoly`: the normalized ridge polynomial $R_{n,\theta} = \pi^{-1/2}\,
  U_n(x\cos\theta + y\sin\theta)$.

## Main results

* `Approximation.setIntegral_diskProd_eval_U_ridge_mul`: the integral over the closed unit disk of
  $U_n(x\cos\theta + y\sin\theta)\, U_m(x\cos\varphi + y\sin\varphi)$ is $\delta_{nm}\, \pi\,
  U_n(\cos(\theta - \varphi))/(n+1)$.
* `Approximation.totalDegree_ridgePoly_le`: $R_{n,\theta}$ has total degree at most $n$.
* `Approximation.integral_unitDisk_ridgePoly_mul`: the $L^2$ inner product of $R_{n,\theta}$ and
  $R_{m,\varphi}$ on the closed unit disk is $\delta_{nm}\, U_n(\cos(\theta - \varphi))/(n+1)$.
* `Approximation.integral_unitDisk_ridgePoly_mul_angle`: the ridge polynomials of degree $n$ in the
  directions $k\pi/(n+1)$, $k = 0, \dots, n$, are orthonormal.

## Proof outline

The inner product is computed by the Radon, or chord, decomposition. A rotation moves one of the two
directions onto the first axis (`Quadrature.setIntegral_diskProd_rotate`). The disk is then cut into
vertical chords (`Quadrature.setIntegral_diskProd_eq_chords`), and the integral along one chord is
`Polynomial.Chebyshev.integral_eval_U_ridge_chord`. The remaining integral over $[-1, 1]$ is the
orthogonality of the $U_n$ for the weight $\sqrt{1 - t^2}$. Polar coordinates do not give this
result: $U_n(r\cos\beta)$ has no closed form for $r < 1$, so the angular integral does not separate.

## Implementation notes

* The closed unit disk has two forms. `Quadrature.diskProd` is the disk in `ℝ × ℝ`.
  `Quadrature.unitDisk` is the disk in `Fin 2 → ℝ`, where the polynomials `MvPolynomial (Fin 2) ℝ`
  are evaluated.
* $U_n$ is `Polynomial.Chebyshev.U ℝ n`.
-/

open MeasureTheory Polynomial.Chebyshev Set

open scoped Real

namespace Approximation

/-! ### The ridge inner product on the disk -/

/-- Let $n, m \in \mathbb{N}$ and $\theta, \varphi \in \mathbb{R}$, and let $U_n$ be the Chebyshev
polynomial of the second kind. On the closed unit disk
$\mathbb{B}_2 = \{(x, y) : x^2 + y^2 \le 1\}$,
$$\int_{\mathbb{B}_2} U_n(x\cos\theta + y\sin\theta)\, U_m(x\cos\varphi + y\sin\varphi)\,d(x,
  y) = \begin{cases} \frac{\pi}{n+1}\, U_n(\cos(\theta - \varphi)) & \text{if } n = m, \\ 0 &
  \text{if } n \ne m. \end{cases}$$

The disk is `Quadrature.diskProd` in `ℝ × ℝ`. The proof rotates by $\varphi$, so that the second
direction becomes the first axis and the first direction has the angle $\theta - \varphi$. It
then cuts the disk into vertical chords, integrates along each chord by
`Polynomial.Chebyshev.integral_eval_U_ridge_chord`, and ends with the orthogonality of the $U_n$
for the weight $\sqrt{1 - t^2}$ on $[-1, 1]$. -/
theorem setIntegral_diskProd_eval_U_ridge_mul (n m : ℕ) (θ φ : ℝ) :
    ∫ q in Quadrature.diskProd,
        (U ℝ (n : ℤ)).eval (q.1 * Real.cos θ + q.2 * Real.sin θ)
          * (U ℝ (m : ℤ)).eval (q.1 * Real.cos φ + q.2 * Real.sin φ)
      = if n = m then π / (n + 1) * (U ℝ (n : ℤ)).eval (Real.cos (θ - φ)) else 0 := by
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hpy : Real.sin φ ^ 2 + Real.cos φ ^ 2 = 1 := Real.sin_sq_add_cos_sq φ
  have hFc : Continuous fun q : ℝ × ℝ =>
      (U ℝ (n : ℤ)).eval (q.1 * Real.cos θ + q.2 * Real.sin θ)
        * (U ℝ (m : ℤ)).eval (q.1 * Real.cos φ + q.2 * Real.sin φ) := by fun_prop
  -- Rotate by `φ`.
  rw [← Quadrature.setIntegral_diskProd_rotate hFc φ]
  have hrot : ∀ q ∈ Quadrature.diskProd,
      (U ℝ (n : ℤ)).eval ((q.1 * Real.cos φ - q.2 * Real.sin φ) * Real.cos θ
          + (q.1 * Real.sin φ + q.2 * Real.cos φ) * Real.sin θ)
        * (U ℝ (m : ℤ)).eval ((q.1 * Real.cos φ - q.2 * Real.sin φ) * Real.cos φ
          + (q.1 * Real.sin φ + q.2 * Real.cos φ) * Real.sin φ)
      = (U ℝ (n : ℤ)).eval (q.1 * Real.cos (θ - φ) + q.2 * Real.sin (θ - φ))
        * (U ℝ (m : ℤ)).eval q.1 := by
    intro q _
    congr 2
    · rw [Real.cos_sub, Real.sin_sub]; ring
    · linear_combination q.1 * hpy
  rw [setIntegral_congr_fun Quadrature.measurableSet_diskProd hrot]
  -- Cut the disk into vertical chords.
  rw [Quadrature.setIntegral_diskProd_eq_chords (by fun_prop : Continuous fun q : ℝ × ℝ =>
    (U ℝ (n : ℤ)).eval (q.1 * Real.cos (θ - φ) + q.2 * Real.sin (θ - φ))
      * (U ℝ (m : ℤ)).eval q.1)]
  -- Integrate along a chord.
  have hinner : ∀ t ∈ uIcc (-1 : ℝ) 1,
      (∫ s in (-√(1 - t ^ 2))..√(1 - t ^ 2),
          (U ℝ (n : ℤ)).eval (t * Real.cos (θ - φ) + s * Real.sin (θ - φ))
            * (U ℝ (m : ℤ)).eval t)
        = 2 / (n + 1) * (U ℝ (n : ℤ)).eval (Real.cos (θ - φ))
            * ((U ℝ (n : ℤ)).eval t * (U ℝ (m : ℤ)).eval t * √(1 - t ^ 2)) := by
    intro t ht
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1), mem_Icc] at ht
    rw [intervalIntegral.integral_mul_const,
      integral_eval_U_ridge_chord n (θ - φ) (abs_le.2 ht)]
    ring
  rw [intervalIntegral.integral_congr hinner, intervalIntegral.integral_const_mul,
    integral_eval_U_mul_eval_U_sqrt]
  split_ifs with h
  · field_simp
  · rw [mul_zero]

/-! ### The ridge polynomials -/

/-- The linear form $(x_0, x_1) \mapsto x_0\cos\theta + x_1\sin\theta$ of the plane, as the
polynomial $\cos\theta\, X_0 + \sin\theta\, X_1$ in two variables with real coefficients. -/
noncomputable def ridgeForm (θ : ℝ) : MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.C (Real.cos θ) * MvPolynomial.X 0 + MvPolynomial.C (Real.sin θ) * MvPolynomial.X 1

/-- The linear form of angle $\theta$ takes at $x \in \mathbb{R}^2$ the value
$x_0\cos\theta + x_1\sin\theta$, which is the inner product of $x$ with the unit vector
$(\cos\theta, \sin\theta)$. -/
@[simp]
theorem eval_ridgeForm (θ : ℝ) (x : Fin 2 → ℝ) :
    MvPolynomial.eval x (ridgeForm θ) = x 0 * Real.cos θ + x 1 * Real.sin θ := by
  simp [ridgeForm, mul_comm]

/-- The linear form of angle $\theta$ has total degree at most $1$. -/
theorem totalDegree_ridgeForm_le (θ : ℝ) : (ridgeForm θ).totalDegree ≤ 1 := by
  refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_) <;>
    exact le_trans (MvPolynomial.totalDegree_mul _ _) (by simp)

/-- The **Logan–Shepp ridge polynomial** of degree $n$ and angle $\theta$ is the polynomial in two
variables
$$R_{n,\theta}(x_0, x_1) = \frac{1}{\sqrt{\pi}}\, U_n(x_0\cos\theta + x_1\sin\theta),$$
where $U_n$ is the Chebyshev polynomial of the second kind. The factor $1/\sqrt{\pi}$ gives it
the $L^2$ norm $1$ on the closed unit disk (`Approximation.integral_unitDisk_ridgePoly_mul`).

The polynomial is $U_n$ composed with `Approximation.ridgeForm θ` by `Polynomial.aeval`. -/
noncomputable def ridgePoly (n : ℕ) (θ : ℝ) : MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.C (√π)⁻¹ * Polynomial.aeval (ridgeForm θ) (U ℝ (n : ℤ))

/-- The ridge polynomial $R_{n,\theta}$ takes at $x \in \mathbb{R}^2$ the value $\pi^{-1/2}\,
U_n(x_0\cos\theta + x_1\sin\theta)$. -/
@[simp]
theorem eval_ridgePoly (n : ℕ) (θ : ℝ) (x : Fin 2 → ℝ) :
    MvPolynomial.eval x (ridgePoly n θ)
      = (√π)⁻¹ * (U ℝ (n : ℤ)).eval (x 0 * Real.cos θ + x 1 * Real.sin θ) := by
  have hcomp : (MvPolynomial.eval x).comp (algebraMap ℝ (MvPolynomial (Fin 2) ℝ))
      = RingHom.id ℝ := by
    ext a; simp
  rw [ridgePoly, map_mul, MvPolynomial.eval_C, Polynomial.aeval_def, Polynomial.hom_eval₂, hcomp,
    Polynomial.eval₂_id, eval_ridgeForm]

/-- The ridge polynomial $R_{n,\theta}$ has total degree at most $n$, because it is $U_n$, of degree
$n$, composed with a linear form. -/
theorem totalDegree_ridgePoly_le (n : ℕ) (θ : ℝ) : (ridgePoly n θ).totalDegree ≤ n := by
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine le_trans (MvPolynomial.totalDegree_aeval_le (totalDegree_ridgeForm_le θ) _) ?_
  rw [one_mul, natDegree_U_natCast]

/-- Let $n, m \in \mathbb{N}$ and $\theta, \varphi \in \mathbb{R}$. On the closed unit disk
$\mathbb{B}_2$, the ridge polynomials $R_{n,\theta}$ and $R_{m,\varphi}$ have the $L^2$ inner
product
$$\int_{\mathbb{B}_2} R_{n,\theta}(x)\, R_{m,\varphi}(x)\,dx = \begin{cases} \frac{1}{n+1}\,
  U_n(\cos(\theta - \varphi)) & \text{if } n = m, \\ 0 & \text{if } n \ne m. \end{cases}$$
For $n = m$ and $\theta = \varphi$ the value is $U_n(1)/(n+1) = 1$, which is the purpose of the
factor $1/\sqrt{\pi}$.

The disk is `Quadrature.unitDisk` in `Fin 2 → ℝ`. The result is
`Approximation.setIntegral_diskProd_eval_U_ridge_mul` divided by $\pi$. -/
theorem integral_unitDisk_ridgePoly_mul (n m : ℕ) (θ φ : ℝ) :
    ∫ x in Quadrature.unitDisk,
        MvPolynomial.eval x (ridgePoly n θ) * MvPolynomial.eval x (ridgePoly m φ)
      = if n = m then (U ℝ (n : ℤ)).eval (Real.cos (θ - φ)) / (n + 1) else 0 := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hne : √π ≠ 0 := by positivity
  have hstep : ∀ x : Fin 2 → ℝ,
      MvPolynomial.eval x (ridgePoly n θ) * MvPolynomial.eval x (ridgePoly m φ)
        = (√π)⁻¹ * (√π)⁻¹ * ((U ℝ (n : ℤ)).eval (x 0 * Real.cos θ + x 1 * Real.sin θ)
            * (U ℝ (m : ℤ)).eval (x 0 * Real.cos φ + x 1 * Real.sin φ)) := by
    intro x; rw [eval_ridgePoly, eval_ridgePoly]; ring
  simp_rw [hstep]
  rw [MeasureTheory.integral_const_mul,
    Quadrature.setIntegral_unitDisk_eq fun q : ℝ × ℝ =>
      (U ℝ (n : ℤ)).eval (q.1 * Real.cos θ + q.2 * Real.sin θ)
        * (U ℝ (m : ℤ)).eval (q.1 * Real.cos φ + q.2 * Real.sin φ),
    setIntegral_diskProd_eval_U_ridge_mul]
  split_ifs with h
  · field_simp
    rw [Real.sq_sqrt hπ.le]
  · rw [mul_zero]

/-- The **Logan–Shepp orthonormal system**. Let $n \in \mathbb{N}$ and $\theta_k = k\pi/(n+1)$. For
$j, k \le n$,
$$\int_{\mathbb{B}_2} R_{n,\theta_j}(x)\, R_{n,\theta_k}(x)\,dx = \begin{cases} 1 & \text{if }
  j = k, \\ 0 & \text{if } j \ne k. \end{cases}$$
So the $n + 1$ ridge polynomials $R_{n,\theta_0}, \dots, R_{n,\theta_n}$ are orthonormal in
$L^2$ of the closed unit disk.

By `Approximation.integral_unitDisk_ridgePoly_mul` the integral is $U_n(\cos\gamma)/(n+1)$ with
$\gamma = (j - k)\pi/(n+1)$. For $j \ne k$, $U_n(\cos\gamma)\sin\gamma = \sin((n+1)\gamma) = 0$
while $\sin\gamma \ne 0$. For $j = k$, $U_n(1) = n + 1$. -/
theorem integral_unitDisk_ridgePoly_mul_angle {n j k : ℕ} (hj : j ≤ n) (hk : k ≤ n) :
    ∫ x in Quadrature.unitDisk,
        MvPolynomial.eval x (ridgePoly n (j * (π / (n + 1))))
          * MvPolynomial.eval x (ridgePoly n (k * (π / (n + 1))))
      = if j = k then 1 else 0 := by
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [integral_unitDisk_ridgePoly_mul, ite_eq_left rfl]
  split_ifs with h
  · subst h
    rw [sub_self, Real.cos_zero, U_eval_one]
    push_cast
    field_simp
  · set γ : ℝ := (j : ℝ) * (π / (n + 1)) - (k : ℝ) * (π / (n + 1)) with hγ
    set d : ℤ := (j : ℤ) - (k : ℤ) with hd
    have hdne : d ≠ 0 := by omega
    have hdabs : d.natAbs ≤ n := by omega
    have hγd : ((n : ℝ) + 1) * γ = (d : ℝ) * π := by
      rw [hγ, hd]; push_cast; field_simp
    -- `sin γ ≠ 0`, because `0 < |j − k| ≤ n < n + 1`.
    have hsin : Real.sin γ ≠ 0 := by
      intro hz
      obtain ⟨l, hl⟩ := Real.sin_eq_zero_iff.1 hz
      have hmul : ((l * ((n : ℤ) + 1) : ℤ) : ℝ) * π = (d : ℝ) * π := by
        push_cast
        rw [← hγd, ← hl]
        ring
      have heq' : ((l * ((n : ℤ) + 1) : ℤ) : ℝ) = ((d : ℤ) : ℝ) :=
        mul_right_cancel₀ Real.pi_ne_zero hmul
      have heq : l * ((n : ℤ) + 1) = d := by exact_mod_cast heq'
      have hl0 : l ≠ 0 := by rintro rfl; simp at heq; exact hdne heq.symm
      have hnat : d.natAbs = l.natAbs * (n + 1) := by
        rw [← heq, Int.natAbs_mul]
        congr 1
      have hl1 : 1 ≤ l.natAbs := Nat.one_le_iff_ne_zero.2 (Int.natAbs_ne_zero.2 hl0)
      have hle : n + 1 ≤ l.natAbs * (n + 1) := Nat.le_mul_of_pos_left _ hl1
      omega
    have hUz : (U ℝ (n : ℤ)).eval (Real.cos γ) = 0 := by
      have hUc := U_real_cos γ (n : ℤ)
      push_cast at hUc
      rw [hγd, Real.sin_int_mul_pi] at hUc
      exact (mul_eq_zero.1 hUc).resolve_right hsin
    rw [hUz, zero_div]

end Approximation

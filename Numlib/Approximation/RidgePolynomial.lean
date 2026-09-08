import Numlib.Analysis.SpecialFunctions.ChebyshevIntegral
import Numlib.Approximation.DiskQuadrature
import Numlib.RingTheory.MvPolynomial.TotalDegree

/-!
# The Logan–Shepp ridge polynomials on the unit disk

A *ridge* polynomial in the plane is a one-variable polynomial of a linear form `x cos θ + y sin θ`.
Taking the one-variable polynomial to be the Chebyshev polynomial `U_n` of the second kind and
normalizing gives

`ridgePoly n θ = (1 / √π) U_n (x cos θ + y sin θ)`,

a polynomial of total degree `n` whose `L²` norm on the closed unit disk is one. These are the
polynomials of L. A. Shepp and S. Ridgway, "Fourier reconstruction of a head section" (1974), and
B. F. Logan and L. A. Shepp, "Optimal reconstruction of a function from its projections" (1975).

The one computation this file makes is their inner product,

`∫_{𝔹₂} U_n(x · u_θ) U_m(x · u_φ) dx = δ_{nm} π U_n(cos (θ − φ)) / (n + 1)`,

which is `setIntegral_diskProd_eval_U_ridge_mul`. Its proof is the Radon, or chord, decomposition:
a rotation moves one of the two directions onto the first axis
(`Quadrature.setIntegral_diskProd_rotate`), the disk is cut into the vertical chords
(`Quadrature.setIntegral_diskProd_eq_chords`), the integral along a chord is
`Polynomial.Chebyshev.integral_eval_U_ridge_chord`, and what is left over `[-1, 1]` is the
orthogonality of `U_n` for the weight `√(1 - t²)`.

Polar coordinates do **not** prove this: `U_n (r cos β)` has no closed form for `r < 1`, so the
angular integral does not separate.

Because `U_n(1) = n + 1`, the value on the diagonal is `π`, and because
`U_n(cos γ) sin γ = sin ((n + 1) γ)` the value vanishes at `γ = k π / (n + 1)` for
`0 < |k| ≤ n`. So the `n + 1` ridge polynomials in the equispaced directions
`θ_k = k π / (n + 1)`, `k = 0, …, n`, are orthonormal on the disk, and orthogonal to every ridge
polynomial of a different degree: `integral_unitDisk_ridgePoly_mul_angle`.

## Main definitions

* `Approximation.ridgePoly n θ` — the normalized ridge polynomial `(1/√π) U_n(x cos θ + y sin θ)`.

## Main statements

* `Approximation.setIntegral_diskProd_eval_U_ridge_mul` — the ridge inner product on the disk.
* `Approximation.totalDegree_ridgePoly_le` — the ridge polynomial has total degree at most `n`.
* `Approximation.integral_unitDisk_ridgePoly_mul` — the same inner product, for `ridgePoly` and the
  unit disk of `Fin 2 → ℝ`.
* `Approximation.integral_unitDisk_ridgePoly_mul_angle` — orthonormality at the `n + 1` equispaced
  directions.
-/

open MeasureTheory Polynomial.Chebyshev Set

open scoped Real

namespace Approximation

/-! ### The ridge inner product on the disk -/

/-- **The inner product of two ridge Chebyshev polynomials on the closed unit disk**:
`∫_{𝔹₂} U_n(x cos θ + y sin θ) U_m(x cos φ + y sin φ) = δ_{nm} π U_n(cos (θ − φ)) / (n + 1)`.

The proof rotates by `φ`, so that the second direction becomes the first axis and the first becomes
`θ − φ`; cuts the disk into vertical chords; integrates along a chord by
`Polynomial.Chebyshev.integral_eval_U_ridge_chord`; and closes with the orthogonality of the
Chebyshev polynomials of the second kind for the weight `√(1 - t²)`. -/
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

/-- The linear form `x cos θ + y sin θ` of the plane, as a polynomial. -/
noncomputable def ridgeForm (θ : ℝ) : MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.C (Real.cos θ) * MvPolynomial.X 0 + MvPolynomial.C (Real.sin θ) * MvPolynomial.X 1

/-- The linear form evaluates to the inner product of `x` with the unit vector of angle `θ`. -/
@[simp]
theorem eval_ridgeForm (θ : ℝ) (x : Fin 2 → ℝ) :
    MvPolynomial.eval x (ridgeForm θ) = x 0 * Real.cos θ + x 1 * Real.sin θ := by
  simp [ridgeForm, mul_comm]

/-- The linear form has total degree at most one. -/
theorem totalDegree_ridgeForm_le (θ : ℝ) : (ridgeForm θ).totalDegree ≤ 1 := by
  refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_) <;>
    exact le_trans (MvPolynomial.totalDegree_mul _ _) (by simp)

/-- **The Logan–Shepp ridge polynomial** `(1 / √π) U_n(x cos θ + y sin θ)`: the Chebyshev polynomial
of the second kind of a linear form, normalized to have `L²` norm one on the closed unit disk. -/
noncomputable def ridgePoly (n : ℕ) (θ : ℝ) : MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.C (√π)⁻¹ * Polynomial.aeval (ridgeForm θ) (U ℝ (n : ℤ))

/-- The ridge polynomial evaluates to `(1/√π) U_n(x cos θ + y sin θ)`. -/
@[simp]
theorem eval_ridgePoly (n : ℕ) (θ : ℝ) (x : Fin 2 → ℝ) :
    MvPolynomial.eval x (ridgePoly n θ)
      = (√π)⁻¹ * (U ℝ (n : ℤ)).eval (x 0 * Real.cos θ + x 1 * Real.sin θ) := by
  have hcomp : (MvPolynomial.eval x).comp (algebraMap ℝ (MvPolynomial (Fin 2) ℝ))
      = RingHom.id ℝ := by
    ext a; simp
  rw [ridgePoly, map_mul, MvPolynomial.eval_C, Polynomial.aeval_def, Polynomial.hom_eval₂, hcomp,
    Polynomial.eval₂_id, eval_ridgeForm]

/-- A ridge polynomial of degree `n` has total degree at most `n`: the substituted form is linear,
and `U_n` has degree `n`. -/
theorem totalDegree_ridgePoly_le (n : ℕ) (θ : ℝ) : (ridgePoly n θ).totalDegree ≤ n := by
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine le_trans (MvPolynomial.totalDegree_aeval_le (totalDegree_ridgeForm_le θ) _) ?_
  rw [one_mul, natDegree_U_natCast]

/-- **The inner product of two ridge polynomials in `L²` of the closed unit disk**:
`(φ_{n,θ}, φ_{m,ψ}) = δ_{nm} U_n(cos (θ − ψ)) / (n + 1)`. On the diagonal `n = m`, `θ = ψ` it is
`1`, which is what the normalization `1/√π` is for. -/
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

/-- **The Logan–Shepp orthonormal system.** At the `n + 1` equispaced directions
`θ_k = k π / (n + 1)`, `k = 0, …, n`, the ridge polynomials of degree `n` are orthonormal in `L²` of
the closed unit disk: `U_n(cos γ) sin γ = sin ((n + 1) γ)` vanishes at `γ = (j − k) π / (n + 1)`
while `sin γ` does not, and `U_n(1) = n + 1`. -/
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

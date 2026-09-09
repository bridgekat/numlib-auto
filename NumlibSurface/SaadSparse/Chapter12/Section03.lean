import Mathlib.Analysis.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Numlib.LinearSolve.Preconditioner.Chebyshev
import Numlib.LinearSolve.Preconditioner.Polynomial
import Numlib.RingTheory.Polynomial.KernelPolynomial
import NumlibSurface.SaadSparse.Common

/-!
# Saad §12.3: polynomial preconditioners

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §12.3: preconditioners of the form `M⁻¹ = s(A)` for a low-degree polynomial `s`, so that
applying the preconditioner costs only matrix–vector products. Three ways of choosing `s`: Neumann
series (§12.3.1), Chebyshev acceleration (§12.3.2, Algorithm 12.1) and least-squares polynomials
(§12.3.3).

The section carries no numbered result, so the declarations here are named for the book's
displayed equations. Everything specializes `Numlib/LinearSolve/Preconditioner/Polynomial`,
`Numlib/LinearSolve/Preconditioner/Chebyshev` and `Numlib/RingTheory/Polynomial/KernelPolynomial`;
what the surface adds is the real-matrix reading and the identification of Saad's residual
polynomial `T_k(t) = C_k((θ - t)/δ)/C_k(θ/δ)` with `Polynomial.Chebyshev.shifted k α β 0`
(`T_k_eq_shifted`), which is the point at which this chapter meets the Chebyshev min–max theorem
of §6.11.

The Jacobi weight (12.15) enters through `equation_12_16`, the closed form Saad gives for its
residual polynomial. That closed form is carried as a *definition* rather than identified with
`IsLeastSquaresResidual`, because the identification is the one step of §12.3.3 that needs Jacobi
polynomials with their orthogonality, and Mathlib has none. `example_12_1` is what the book
computes from it: the table of the eight least-squares polynomials `s_1, …, s_8` for
`μ = 1/2`, `ν = -1/2`, each identity cleared of the division by `λ`.

§12.3.4 — the nonsymmetric case, with Chebyshev polynomials on an ellipse and the Remez algorithm
on a polygon — is not stated here: its results are Saad Lemma 6.26 and Theorem 6.27, and the
polygonal case is a numerical procedure with no theorem attached. Example 12.2, a table of measured
iteration counts and timings, is not stated either.
-/

open Matrix Polynomial
open scoped SaadSparse

namespace SaadSparse.Chapter12

variable {n : ℕ}

/-- Over `ℝ` the scalar map of the backbone's `Polynomial.map (algebraMap ℝ 𝕜)` is the identity. -/
private theorem map_algebraMap_real (p : Polynomial ℝ) : p.map (algebraMap ℝ ℝ) = p := by
  simp

/-! ### §12.3.1 Neumann polynomial preconditioners -/

/-- Saad (12.3): with `N = I - ω D⁻¹ A` the truncated Neumann preconditioner
`M⁻¹ = (I + N + ⋯ + N^s) D⁻¹` satisfies `M⁻¹ A = ω⁻¹ (I - N^{s+1})`. So a Neumann polynomial
preconditioner differs from the identity by exactly the `(s+1)`-st power of the iteration matrix
of the underlying relaxation: it *is* `s + 1` steps of that relaxation, folded into one
preconditioner. -/
theorem equation_12_3 {ω : ℝ} (hω : ω ≠ 0) (A D : Matrix (Fin n) (Fin n) ℝ) (s : ℕ) :
    Preconditioner.neumannPolyOf (1 - ω • (D⁻¹ * A)) s * D⁻¹ * A =
      ω⁻¹ • (1 - (1 - ω • (D⁻¹ * A)) ^ (s + 1)) := by
  have h := Preconditioner.neumannPoly_mul_eq (ω • D⁻¹) A s
  rw [Matrix.smul_mul] at h
  rw [← h, mul_smul_comm, smul_smul, inv_mul_cancel₀ hω, one_smul, Matrix.mul_assoc]

/-- Saad's remark closing §12.3.1, his Exercise 12.1: for symmetric positive definite `A` and `D`
the preconditioned matrix `s(D⁻¹A) D⁻¹A` is *not* symmetric, but it is self-adjoint for the
`D`-inner product, so the conjugate gradient method may still be used with it. -/
theorem neumann_isSymmetric_withEnergy {A D : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (hD : D.PosDef) (s : Polynomial ℝ) :
    ((WithEnergy.equiv (Matrix.toEuclideanLin D)
        ((Matrix.posDef_iff_isSymmetricCoercive D).1 hD)).conj
      (aeval (Matrix.toEuclideanLin (D⁻¹ * A)) s *
        Matrix.toEuclideanLin (D⁻¹ * A))).IsSymmetric := by
  have hDc := (Matrix.posDef_iff_isSymmetricCoercive D).1 hD
  have hDinv : D * D⁻¹ = 1 :=
    Matrix.mul_nonsing_inv D (isUnit_iff_ne_zero.2 (Matrix.PosDef.det_pos hD).ne')
  have hcomp : Matrix.toEuclideanLin D ∘ₗ Matrix.toEuclideanLin (D⁻¹ * A)
      = Matrix.toEuclideanLin A := by
    rw [← Matrix.toEuclideanLin_mul, ← Matrix.mul_assoc, hDinv, Matrix.one_mul]
  have hB := Preconditioner.energyInner_comm_of_comp_eq hDc.isSymmetric
    (Matrix.isSymmetric_toEuclideanLin_iff.2 (Matrix.PosDef.isHermitian hA)) hcomp
  have h := Preconditioner.isSymmetric_withEnergy_aeval_mul hDc hB s
  rwa [map_algebraMap_real] at h

/-! ### §12.3.2 The optimality criterion (12.4)–(12.5) -/

/-- Saad (12.5): the criterion that selects the polynomial. For a symmetric matrix whose
quadratic form lies in `[α, β]` — an interval enclosing the spectrum — and any real polynomial
`s`, the preconditioned operator `s(A) A` differs from the identity by at most
`max_{λ ∈ [α, β]} |1 - λ s(λ)|`. Making that maximum small is therefore the whole design problem
of a polynomial preconditioner. -/
theorem equation_12_5 {A : Matrix (Fin n) (Fin n) ℝ} {α β : ℝ}
    (hA : (Matrix.toEuclideanLin A).IsSymmetricBoundedBy α β) (s : Polynomial ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖x - aeval (Matrix.toEuclideanLin A) s (A ⬝ x)‖ ≤
      sSup ((fun t => |1 - t * s.eval t|) '' Set.Icc α β) * ‖x‖ := by
  have h := Preconditioner.norm_sub_aeval_mul_apply_le hA s x
  rwa [map_algebraMap_real] at h

/-- Saad (12.4)–(12.5), the min–max problem the criterion poses, answered on the enclosing
interval `E = [α, β]` of (12.5) for `γ = 0`: no
polynomial `s` of degree at most `k` makes `max_{[α, β]} |1 - λ s(λ)|` smaller than
`1 / C_{k+1}((β + α)/(β - α))`, the value attained by the shifted Chebyshev polynomial of
Theorem 6.25. The residual polynomials `1 - λ s(λ)` are exactly the polynomials of degree at most
`k + 1` taking the value `1` at `0`. -/
theorem equation_12_4 {α β : ℝ} (hα : 0 < α) (hαβ : α < β) {k : ℕ} {s : Polynomial ℝ}
    (hs : s.degree ≤ (k : WithBot ℕ)) :
    1 / eval ((β + α) / (β - α)) (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)) ≤
      sSup ((fun t => |1 - t * s.eval t|) '' Set.Icc α β) := by
  have hdeg : ((1 : Polynomial ℝ) - X * s).degree ≤ ((k + 1 : ℕ) : WithBot ℕ) := by
    refine (degree_sub_le _ _).trans (max_le (degree_one_le.trans ?_) ?_)
    · exact_mod_cast Nat.zero_le (k + 1)
    · refine (degree_mul_le _ _).trans ?_
      refine le_trans (add_le_add degree_X_le hs) ?_
      exact_mod_cast le_of_eq (by ring)
  have h0 : eval 0 ((1 : Polynomial ℝ) - X * s) = 1 := by simp
  have h := Chebyshev.one_div_eval_T_le_sSup_abs_eval_of_eval_zero (k + 1) hα hαβ _ hdeg h0
  have himg : (fun t => |eval t ((1 : Polynomial ℝ) - X * s)|) = fun t => |1 - t * s.eval t| := by
    funext t
    simp
  rwa [himg] at h

/-! ### §12.3.2 Chebyshev acceleration, Algorithm 12.1 -/

/-- Saad's residual polynomial of §12.3.2, `T_k(t) = C_k((θ - t)/δ) / C_k(θ/δ)` with
`θ = (β + α)/2` and `δ = (β - α)/2`, is the shifted Chebyshev polynomial
`Polynomial.Chebyshev.shifted k α β 0` of §6.11. This identification is why Chebyshev acceleration
inherits the min–max optimality already proved for `shifted`. -/
theorem T_k_eq_shifted {α β : ℝ} (hαβ : α < β) (k : ℕ) (t : ℝ) :
    eval t (Chebyshev.shifted k α β 0) =
      eval (((β + α) / 2 - t) / ((β - α) / 2)) (Chebyshev.T ℝ (k : ℤ)) /
        eval ((β + α) / 2 / ((β - α) / 2)) (Chebyshev.T ℝ (k : ℤ)) := by
  have hd : β - α ≠ 0 := sub_ne_zero_of_ne hαβ.ne'
  have e1 : ((β + α) / 2 - t) / ((β - α) / 2) = (β + α) / (β - α) - 2 / (β - α) * t := by
    field_simp
  have e2 : (β + α) / 2 / ((β - α) / 2) = (β + α) / (β - α) := by
    field_simp
  rw [Chebyshev.shifted, e1, e2]
  simp only [eval_mul, eval_C, eval_comp, eval_sub, eval_X, mul_zero, sub_zero]
  ring

/-- Saad Algorithm 12.1, Chebyshev acceleration for a real symmetric matrix whose spectrum lies
in `[α, β]`: the state after `k` steps, carrying the iterate `x_k`, the residual `r_k`, the search
direction `d_k` and the scalar `ρ_k`. One step costs one matrix–vector product and no inner
product at all, which is the practical point of the method. It is
`Preconditioner.Chebyshev.iterate` at `θ = (β + α)/2` and `δ = (β - α)/2`. -/
noncomputable abbrev chebyshevIterate (A : Matrix (Fin n) (Fin n) ℝ)
    (b x₀ : EuclideanSpace ℝ (Fin n)) (α β : ℝ) (k : ℕ) :
    Preconditioner.Chebyshev.State (EuclideanSpace ℝ (Fin n)) :=
  Preconditioner.Chebyshev.iterate (Matrix.toEuclideanLin A) b x₀ ((β + α) / 2) ((β - α) / 2) k

/-- The Chebyshev values `σ_k = C_k(θ/δ)` obey the three-term recurrence of the Chebyshev
polynomials themselves. This is the display just before Saad (12.6) and carries no number of
its own; the declaration keeps the name the plan gave it. The numbered (12.7) is the `ρ`
recurrence, which is `equation_12_6`. -/
theorem equation_12_7 (θ δ : ℝ) (k : ℕ) :
    Preconditioner.Chebyshev.sigma θ δ (k + 2) =
      2 * (θ / δ) * Preconditioner.Chebyshev.sigma θ δ (k + 1) -
        Preconditioner.Chebyshev.sigma θ δ k :=
  Preconditioner.Chebyshev.sigma_add_two θ δ k

/-- **Saad (12.7)**: the scalar `ρ_k = σ_k/σ_{k+1}` of (12.6), which the algorithm carries,
obeys `ρ_{k+1} = (2 σ₁ - ρ_k)⁻¹` — what removes the Chebyshev values from the implementation.
(12.6) itself is the definition of `ρ_k`, which is `Preconditioner.Chebyshev.rho`; the
declaration keeps the name the plan gave it. -/
theorem equation_12_6 {θ δ : ℝ} (hδ : 0 < δ) (hθδ : δ < θ) (k : ℕ) :
    Preconditioner.Chebyshev.rho θ δ (k + 1) =
      (2 * (θ / δ) - Preconditioner.Chebyshev.rho θ δ k)⁻¹ :=
  Preconditioner.Chebyshev.rho_succ hδ hθδ k

/-- Saad (12.8): the three-term recurrence of the residual polynomials,
`T_{k+2} = ρ_{k+1} (2 (σ₁ - t/δ) T_{k+1} - ρ_k T_k)`. It is the Chebyshev recurrence divided by
`σ_{k+2}`, and it is what makes the vector recurrence of Algorithm 12.1 produce Chebyshev
residuals. -/
theorem equation_12_8 {θ δ : ℝ} (hδ : 0 < δ) (hθδ : δ < θ) (k : ℕ) :
    Preconditioner.Chebyshev.resPoly θ δ (k + 2) =
      C (2 * Preconditioner.Chebyshev.rho θ δ (k + 1)) *
          (Preconditioner.Chebyshev.shift θ δ * Preconditioner.Chebyshev.resPoly θ δ (k + 1)) -
        C (Preconditioner.Chebyshev.rho θ δ k * Preconditioner.Chebyshev.rho θ δ (k + 1)) *
          Preconditioner.Chebyshev.resPoly θ δ k :=
  Preconditioner.Chebyshev.resPoly_add_two hδ hθδ k

/-- Saad (12.9): the direction recurrence of Algorithm 12.1,
`d_{k+1} = ρ_k ρ_{k+1} d_k + (2 ρ_{k+1}/δ) r_{k+1}`. -/
theorem equation_12_9 (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : EuclideanSpace ℝ (Fin n))
    (α β : ℝ) (k : ℕ) :
    (chebyshevIterate A b x₀ α β (k + 1)).d =
      ((chebyshevIterate A b x₀ α β k).ρ * (chebyshevIterate A b x₀ α β (k + 1)).ρ : ℝ) •
          (chebyshevIterate A b x₀ α β k).d +
        (2 * (chebyshevIterate A b x₀ α β (k + 1)).ρ / ((β - α) / 2) : ℝ) •
          (chebyshevIterate A b x₀ α β (k + 1)).r := by
  simp only [chebyshevIterate, Preconditioner.Chebyshev.iterate_succ]
  exact Preconditioner.Chebyshev.step_d _

/-- The residual of Saad Algorithm 12.1 is `r_k = T_k(A) r_0`, the shifted Chebyshev polynomial of
`[α, β]` applied to the initial residual. -/
theorem chebyshev_residual_eq {A : Matrix (Fin n) (Fin n) ℝ} {b x₀ : EuclideanSpace ℝ (Fin n)}
    {α β : ℝ} (hα : 0 < α) (hαβ : α < β) (k : ℕ) :
    (chebyshevIterate A b x₀ α β k).r =
      aeval (Matrix.toEuclideanLin A) (Chebyshev.shifted k α β 0) (b - (A ⬝ x₀)) := by
  have h := Preconditioner.Chebyshev.residual_iterate_eq
    (A := Matrix.toEuclideanLin A) (b := b) (x₀ := x₀) hα hαβ k
  rwa [map_algebraMap_real] at h

/-- The convergence rate of Chebyshev acceleration:
`‖r_k‖ ≤ 2 ((√κ - 1)/(√κ + 1))^k ‖r_0‖` with `κ = β/α` the condition number of the enclosing
interval. -/
theorem norm_chebyshev_residual_le {A : Matrix (Fin n) (Fin n) ℝ}
    {b x₀ : EuclideanSpace ℝ (Fin n)} {α β : ℝ}
    (hA : (Matrix.toEuclideanLin A).IsSymmetricBoundedBy α β) (hα : 0 < α) (hαβ : α < β) (k : ℕ) :
    ‖(chebyshevIterate A b x₀ α β k).r‖ ≤
      2 * ((Real.sqrt (β / α) - 1) / (Real.sqrt (β / α) + 1)) ^ k * ‖b - (A ⬝ x₀)‖ :=
  Preconditioner.Chebyshev.norm_residual_iterate_le_pow hA hα hαβ k

/-- Chebyshev acceleration is not Krylov-optimal: a minimal-residual iterate of the same degree is
never worse, because the Chebyshev residual polynomial is only one competitor in the minimization.
This is the comparison that makes CG or GMRES preferable wherever inner products are affordable,
and Chebyshev acceleration preferable where they are not. -/
theorem norm_residual_minRes_le_chebyshev {A : Matrix (Fin n) (Fin n) ℝ}
    {b x₀ y : EuclideanSpace ℝ (Fin n)} {α β : ℝ} (hα : 0 < α) (hαβ : α < β) {k : ℕ}
    (hy : Krylov.IsMinResIterate (Matrix.toEuclideanLin A) b x₀ k y) :
    ‖b - (A ⬝ y)‖ ≤ ‖(chebyshevIterate A b x₀ α β k).r‖ :=
  Preconditioner.Chebyshev.norm_residual_minRes_le_norm_residual_iterate hα hαβ hy

/-! ### §12.3.3 Least-squares polynomials -/

section LeastSquares

open MeasureTheory

variable {α β : ℝ} {w : ℝ → ℝ}

/-- Saad (12.10): the weighted inner product `⟨p, q⟩_w = ∫_α^β p(λ) q(λ) w(λ) dλ` on the
polynomials, presented as a bilinear form, which is the shape the backbone statements of
`Numlib/RingTheory/Polynomial/KernelPolynomial` take. Bilinearity needs only that `w` is
integrable over the interval; nonnegativity of `w` is used where the form has to be positive
semidefinite (`bilinFormOfWeight_le`), and nowhere else. -/
noncomputable def bilinFormOfWeight (α β : ℝ) (w : ℝ → ℝ)
    (hw : IntervalIntegrable w volume α β) : LinearMap.BilinForm ℝ (Polynomial ℝ) :=
  LinearMap.mk₂ ℝ (fun p q => ∫ t in α..β, p.eval t * q.eval t * w t)
    (fun p₁ p₂ q => by
      have h1 : IntervalIntegrable (fun t => p₁.eval t * q.eval t * w t) volume α β :=
        hw.continuousOn_mul (p₁.continuous.mul q.continuous).continuousOn
      have h2 : IntervalIntegrable (fun t => p₂.eval t * q.eval t * w t) volume α β :=
        hw.continuousOn_mul (p₂.continuous.mul q.continuous).continuousOn
      rw [← intervalIntegral.integral_add h1 h2]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [eval_add]
      ring)
    (fun c p q => by
      rw [smul_eq_mul, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [eval_smul, smul_eq_mul]
      ring)
    (fun p q₁ q₂ => by
      have h1 : IntervalIntegrable (fun t => p.eval t * q₁.eval t * w t) volume α β :=
        hw.continuousOn_mul (p.continuous.mul q₁.continuous).continuousOn
      have h2 : IntervalIntegrable (fun t => p.eval t * q₂.eval t * w t) volume α β :=
        hw.continuousOn_mul (p.continuous.mul q₂.continuous).continuousOn
      rw [← intervalIntegral.integral_add h1 h2]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [eval_add]
      ring)
    (fun c p q => by
      rw [smul_eq_mul, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [eval_smul, smul_eq_mul]
      ring)

/-- The weighted form of (12.10) evaluated: `⟨p, q⟩_w = ∫_α^β p q w`. -/
@[simp]
theorem bilinFormOfWeight_apply (hw : IntervalIntegrable w volume α β) (p q : Polynomial ℝ) :
    bilinFormOfWeight α β w hw p q = ∫ t in α..β, p.eval t * q.eval t * w t := rfl

/-- The weighted form of (12.10) is symmetric. -/
theorem bilinFormOfWeight_isSymm (hw : IntervalIntegrable w volume α β) :
    (bilinFormOfWeight α β w hw).IsSymm := by
  refine ⟨fun p q => ?_⟩
  simp only [bilinFormOfWeight_apply]
  refine intervalIntegral.integral_congr fun t _ => ?_
  ring

/-- The weighted form of (12.10) is "supported on `[α, β]`" in the sense the geometric bound of
§12.3.3 needs: for a nonnegative weight, `⟨p, p⟩_w ≤ (max_{[α,β]} |p|)² ⟨1, 1⟩_w`. -/
theorem bilinFormOfWeight_le (hw : IntervalIntegrable w volume α β) (hαβ : α ≤ β)
    (hw0 : ∀ t ∈ Set.Icc α β, 0 ≤ w t) (p : Polynomial ℝ) :
    bilinFormOfWeight α β w hw p p ≤
      sSup ((fun t => |p.eval t|) '' Set.Icc α β) ^ 2 * bilinFormOfWeight α β w hw 1 1 := by
  have hbdd : BddAbove ((fun t => |p.eval t|) '' Set.Icc α β) :=
    (isCompact_Icc.image p.continuous.abs).bddAbove
  have hi1 : IntervalIntegrable (fun t => p.eval t * p.eval t * w t) volume α β :=
    hw.continuousOn_mul ((p.continuous.mul p.continuous).continuousOn)
  have hi2 : IntervalIntegrable
      (fun t => sSup ((fun t => |p.eval t|) '' Set.Icc α β) ^ 2 * w t) volume α β :=
    hw.const_mul _
  have hpt : ∀ t ∈ Set.Icc α β,
      p.eval t * p.eval t * w t ≤ sSup ((fun t => |p.eval t|) '' Set.Icc α β) ^ 2 * w t := by
    intro t ht
    have hple : |p.eval t| ≤ sSup ((fun t => |p.eval t|) '' Set.Icc α β) :=
      le_csSup hbdd ⟨t, ht, rfl⟩
    have hsq : p.eval t * p.eval t ≤ sSup ((fun t => |p.eval t|) '' Set.Icc α β) ^ 2 := by
      rw [← sq, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hple 2
    exact mul_le_mul_of_nonneg_right hsq (hw0 t ht)
  refine (intervalIntegral.integral_mono_on hαβ hi1 hi2 hpt).trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul, bilinFormOfWeight_apply]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp

end LeastSquares

/-- Saad §12.3.3: `R` is a least-squares residual polynomial of degree `k` for the form `B` when
it is admissible — of degree at most `k` and equal to `1` at `0`, which is exactly what
`R = 1 - λ s(λ)` with `deg s ≤ k - 1` means — and minimizes `‖R‖_w` among the admissible
polynomials. Saad's `s_{k-1}` is recovered from `R` as `(1 - R)/λ`. -/
def IsLeastSquaresResidual (B : LinearMap.BilinForm ℝ (Polynomial ℝ)) (k : ℕ)
    (R : Polynomial ℝ) : Prop :=
  R.degree ≤ (k : WithBot ℕ) ∧ R.eval 0 = 1 ∧
    ∀ p : Polynomial ℝ, p.degree ≤ (k : WithBot ℕ) → p.eval 0 = 1 →
      B R R ≤ B p p

/-- Saad (12.12), the kernel polynomial formula: for the polynomials `q_i` orthonormal with
respect to the weight, `R_k = (∑_{i ≤ k} q_i(0) q_i(λ)) / ∑_{i ≤ k} q_i(0)²` — that is,
`Polynomial.kernelPolynomial q 0 k` — is the least-squares residual polynomial of degree `k`. The
normalizing sum must be nonzero, which says exactly that some `q_i` with `i ≤ k` does not vanish
at the origin. -/
theorem equation_12_12 {B : LinearMap.BilinForm ℝ (Polynomial ℝ)} {q : ℕ → Polynomial ℝ}
    (horth : ∀ i j, B (q i) (q j) = if i = j then 1 else 0) (hdeg : ∀ i, (q i).degree = i)
    {k : ℕ} (hS : ∑ i ∈ Finset.range (k + 1), (q i).eval 0 ^ 2 ≠ 0) :
    IsLeastSquaresResidual B k (kernelPolynomial q 0 k) := by
  refine ⟨kernelPolynomial_degree_le hdeg 0 k, kernelPolynomial_eval hS, fun p hp hp0 => ?_⟩
  rw [bilinForm_kernelPolynomial_self horth hS]
  exact (bilinForm_kernelPolynomial_le horth hdeg hS).2 ⟨p, hp, hp0, rfl⟩

/-- Saad (12.13)–(12.14): the least-squares polynomial itself. With
`t_i(λ) = (q_i(0) - q_i(λ))/λ`, which is the polynomial `-(q_i).divX`, the minimizer is
`s_{k-1} = (∑_{i ≤ k} q_i(0) t_i) / ∑_{i ≤ k} q_i(0)²` and the residual polynomial of (12.12) is
`R_k = 1 - λ s_{k-1}(λ)`. -/
theorem equation_12_13 (q : ℕ → Polynomial ℝ) (k : ℕ)
    (hS : ∑ i ∈ Finset.range (k + 1), (q i).eval 0 ^ 2 ≠ 0) :
    kernelPolynomial q 0 k =
      1 - X * ((∑ i ∈ Finset.range (k + 1), (q i).eval 0 ^ 2)⁻¹ •
        ∑ i ∈ Finset.range (k + 1), (q i).eval 0 • (-(q i).divX)) := by
  refine Polynomial.funext fun t => ?_
  have hdiv : ∀ i, t * (q i).divX.eval t + (q i).eval 0 = (q i).eval t := fun i => by
    have h := congrArg (Polynomial.eval t) (X_mul_divX_add (q i))
    simpa [coeff_zero_eq_eval_zero] using h
  have key : ∑ i ∈ Finset.range (k + 1), (q i).eval 0 * -(t * (q i).divX.eval t) =
      ∑ i ∈ Finset.range (k + 1), (q i).eval 0 ^ 2 -
        ∑ i ∈ Finset.range (k + 1), (q i).eval 0 * (q i).eval t := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ =>
      by linear_combination (-(q i).eval 0) * hdiv i
  have hrhs : ∑ i ∈ Finset.range (k + 1),
        t * ((∑ j ∈ Finset.range (k + 1), (q j).eval 0 ^ 2)⁻¹ *
          ((q i).eval 0 * -(q i).divX.eval t)) =
      (∑ j ∈ Finset.range (k + 1), (q j).eval 0 ^ 2)⁻¹ *
        ∑ i ∈ Finset.range (k + 1), (q i).eval 0 * -(t * (q i).divX.eval t) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [kernelPolynomial, eval_smul, eval_finsetSum, eval_sub, eval_one, eval_mul, eval_X,
    eval_neg, smul_eq_mul, Finset.mul_sum]
  rw [hrhs, key, mul_sub, inv_mul_cancel₀ hS, sub_sub_cancel, Finset.mul_sum]

/-- Saad's second route to the least-squares polynomial: the residual polynomials are orthogonal
with respect to the weight `λ w(λ)`. Equivalently, the normal equations
`⟨1 - λ s_{k-1}(λ), λ Q(λ)⟩_w = 0` hold for every `Q` of degree less than `k` — the admissible
directions are exactly those preserving both the degree bound and the value `1` at the origin. -/
theorem leastSquaresResidual_orthogonal {B : LinearMap.BilinForm ℝ (Polynomial ℝ)}
    {q : ℕ → Polynomial ℝ} (hsymm : B.IsSymm)
    (horth : ∀ i j, B (q i) (q j) = if i = j then 1 else 0) (hdeg : ∀ i, (q i).degree = i)
    {k : ℕ} (hS : ∑ i ∈ Finset.range (k + 1), (q i).eval 0 ^ 2 ≠ 0)
    {p : Polynomial ℝ} (hp : p.degree < (k : WithBot ℕ)) :
    B (X * p) (kernelPolynomial q 0 k) = 0 :=
  bilinForm_kernelPolynomial_mul_X hsymm horth hdeg hS hp

/-- The theoretical consideration closing §12.3.3: for `0 < α < β` the least-squares residual
polynomial decays geometrically, `‖R_k‖_w² ≤ ((β - α)/(β + α))^{2k} ‖1‖_w²`, because
`(1 - λ/θ)^k` with `θ = (α + β)/2` is an admissible competitor. The hypothesis on `B` is what
`bilinFormOfWeight_le` supplies for a nonnegative weight supported on `[α, β]`.

The case `α = 0`, where the decay is only `1/k` and the constant is a ratio of Gamma functions of
the Jacobi weights, is not stated: Mathlib has no Jacobi polynomials. -/
theorem norm_leastSquaresResidual_le {B : LinearMap.BilinForm ℝ (Polynomial ℝ)}
    {q : ℕ → Polynomial ℝ} (horth : ∀ i j, B (q i) (q j) = if i = j then 1 else 0)
    (hdeg : ∀ i, (q i).degree = i) {α β : ℝ} (hα : 0 < α) (hαβ : α < β)
    (hB : ∀ p : Polynomial ℝ, B p p ≤ sSup ((fun t => |p.eval t|) '' Set.Icc α β) ^ 2 * B 1 1)
    {k : ℕ} (hS : ∑ i ∈ Finset.range (k + 1), (q i).eval 0 ^ 2 ≠ 0) :
    B (kernelPolynomial q 0 k) (kernelPolynomial q 0 k) ≤
      ((β - α) / (β + α)) ^ (2 * k) * B 1 1 :=
  bilinForm_kernelPolynomial_le_pow horth hdeg hα hαβ hB hS

/-! ### §12.3.3 The Jacobi weight (12.15)–(12.16) and Example 12.1 -/

/-- The coefficient `κ_j^{(k)}` of Saad (12.16), for the Jacobi weight (12.15) with exponents
`μ > 0` and `ν ≥ -1/2`: `κ_j^{(k)} = C(k, j) ∏_{i < j} (k - i + ν)/(i + 1 + μ)`. -/
noncomputable def kappa_12_16 (mu nu : ℝ) (k j : ℕ) : ℝ :=
  (k.choose j : ℝ) * ∏ i ∈ Finset.range j, ((k : ℝ) - i + nu) / ((i : ℝ) + 1 + mu)

/-- **Saad (12.16)**, the closed form of the least-squares residual polynomial for the Jacobi
weight (12.15) on `[0, 1]`:
`R_k(λ) = ∑_{j ≤ k} κ_j^{(k)} (1 - λ)^{k - j} (-λ)^j`.

This is a *definition*, not an identification: that this polynomial is the least-squares residual
polynomial of `IsLeastSquaresResidual` for the Jacobi weight is what Saad says can "be derived
easily from the explicit expression of the Jacobi polynomials and the fact that `{R_k}` is
orthogonal with respect to the weight `λ w(λ)`", and it needs Jacobi polynomials with their
orthogonality, which Mathlib does not have — the same gap
`plans/NumlibSurface/SaadSparse/Chapter12.toml` records for (12.15)–(12.16). What is stated here is
what the book computes from the formula, which is Example 12.1. -/
noncomputable def equation_12_16 (mu nu : ℝ) (k : ℕ) (l : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), kappa_12_16 mu nu k j * (1 - l) ^ (k - j) * (-l) ^ j

/-- **Saad Example 12.1**: the least-squares polynomials `s_k` for `k = 1, …, 8` and the Jacobi
weight with `μ = 1/2`, `ν = -1/2`, as the book tabulates them.

The table lists the polynomials on `[0, 4]`, "as this leads to integer coefficients", each rescaled
by `(3 + 2k)/4`; on a general interval `[0, β]` the degree `k` polynomial is `s_k(4λ/β)`, so at
`β = 1` — the interval the weight (12.15) lives on — the tabulated `s_k` read at `4λ` is
`(3 + 2k)/4` times `(1 - R_{k+1}(λ))/λ`, with `R_{k+1}` the residual polynomial (12.16). That is the
eight identities below, cleared of the division by `λ`, so they hold at `λ = 0` too. The
coefficients are the eight rows of the table, `s_1 = 5 - λ` through
`s_8 = 285 - 1254 λ + ⋯ + λ⁸`.

The scaling factor is, as Saad says, unimportant for preconditioning; it is carried here because it
is what makes the printed coefficients integers. -/
theorem example_12_1 (l : ℝ) :
      (5 / 4) * (1 - equation_12_16 (1 / 2) (-1 / 2) 2 l) =
        l * (5 - (4 * l)) ∧
      (7 / 4) * (1 - equation_12_16 (1 / 2) (-1 / 2) 3 l) =
        l * (14 - 7 * (4 * l) + (4 * l) ^ 2) ∧
      (9 / 4) * (1 - equation_12_16 (1 / 2) (-1 / 2) 4 l) =
        l * (30 - 27 * (4 * l) + 9 * (4 * l) ^ 2 - (4 * l) ^ 3) ∧
      (11 / 4) * (1 - equation_12_16 (1 / 2) (-1 / 2) 5 l) =
        l * (55 - 77 * (4 * l) + 44 * (4 * l) ^ 2 - 11 * (4 * l) ^ 3 + (4 * l) ^ 4) ∧
      (13 / 4) * (1 - equation_12_16 (1 / 2) (-1 / 2) 6 l) =
        l * (91 - 182 * (4 * l) + 156 * (4 * l) ^ 2 - 65 * (4 * l) ^ 3 + 13 * (4 * l) ^ 4
          - (4 * l) ^ 5) ∧
      (15 / 4) * (1 - equation_12_16 (1 / 2) (-1 / 2) 7 l) =
        l * (140 - 378 * (4 * l) + 450 * (4 * l) ^ 2 - 275 * (4 * l) ^ 3 + 90 * (4 * l) ^ 4
          - 15 * (4 * l) ^ 5 + (4 * l) ^ 6) ∧
      (17 / 4) * (1 - equation_12_16 (1 / 2) (-1 / 2) 8 l) =
        l * (204 - 714 * (4 * l) + 1122 * (4 * l) ^ 2 - 935 * (4 * l) ^ 3 + 442 * (4 * l) ^ 4
          - 119 * (4 * l) ^ 5 + 17 * (4 * l) ^ 6 - (4 * l) ^ 7) ∧
      (19 / 4) * (1 - equation_12_16 (1 / 2) (-1 / 2) 9 l) =
        l * (285 - 1254 * (4 * l) + 2508 * (4 * l) ^ 2 - 2717 * (4 * l) ^ 3 + 1729 * (4 * l) ^ 4
          - 665 * (4 * l) ^ 5 + 152 * (4 * l) ^ 6 - 19 * (4 * l) ^ 7 + (4 * l) ^ 8) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [equation_12_16, kappa_12_16, Finset.sum_range_succ, Finset.sum_range_zero,
      Finset.prod_range_succ, Finset.prod_range_zero, Nat.choose] <;>
    norm_num <;> ring

end SaadSparse.Chapter12

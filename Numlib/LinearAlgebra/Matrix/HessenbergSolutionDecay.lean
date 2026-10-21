import Mathlib.Algebra.Order.Star.Real
import Numlib.Krylov.Convergence.CG
import Numlib.LinearAlgebra.Matrix.UnreducedHessenberg
import Numlib.Analysis.Matrix.ToEuclideanLin

/-!
# Decay of solution coordinates in positive definite Hessenberg systems

A residual polynomial applied to a solution gives an approximation from the Krylov
space of its right-hand side. Upper Hessenberg bandwidth forces the far coordinates
of this approximation to vanish. Chebyshev approximation therefore bounds the actual
solution coordinates, including a scalar spectral interval.
-/

noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped InnerProductSpace

namespace Matrix

/-- The actual normalized shifted Chebyshev residual polynomial has its uniform
geometric operator bound on every positive nondegenerate spectral interval. -/
theorem norm_aeval_shifted_le {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hB : (toEuclideanLin B).IsSymmetricBoundedBy a b)
    (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖aeval (toEuclideanLin B) (shifted k a b 0) x‖ ≤
      (2 * ((Real.sqrt (b / a) - 1) / (Real.sqrt (b / a) + 1)) ^ k) * ‖x‖ := by
  have harg : (b / a + 1) / (b / a - 1) = (b + a) / (b - a) := by field_simp
  have hκ : 1 < b / a := (one_lt_div ha).mpr hab
  apply hB.isSymmetric.norm_aeval_apply_le (shifted k a b 0)
  intro μ hμ
  have hmem := hB.re_mem_Icc_of_hasEigenvalue hμ
  have hpoint := abs_eval_shifted_le (γ := 0) k hab hmem
  have hOne : 1 ≤ (b + a) / (b - a) := by
    rw [le_div_iff₀ (sub_pos.mpr hab)]
    linarith
  have hpos := one_le_eval_T hOne k
  simp only [mul_zero, sub_zero] at hpoint
  rw [abs_of_nonneg (by linarith : 0 ≤ (Polynomial.Chebyshev.T ℝ k).eval
    ((b + a) / (b - a)))] at hpoint
  rw [← harg] at hpoint
  simpa only [RCLike.re_to_real, Real.norm_eq_abs] using
    hpoint.trans (one_div_eval_T_le_two_mul_pow hκ k)

variable {N : ℕ} {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}

/-- An upper Hessenberg system started in its first coordinate has no Krylov
components beyond the polynomial degree. -/
theorem IsUpperHessenberg.apply_eq_zero_of_mem_krylov
    (hT : T.IsUpperHessenberg) {c : ℝ} {m : ℕ}
    {z : EuclideanSpace ℝ (Fin (N + 1))}
    (hz : z ∈ Krylov.subspace (toEuclideanLin T)
      (c • EuclideanSpace.single 0 1) m) {i : Fin (N + 1)} (hi : m ≤ i) : z i = 0 := by
  induction hz using Submodule.span_induction with
  | mem v hv =>
    rcases hv with ⟨j, rfl⟩
    change ((toEuclideanLin T ^ (j : ℕ)) (c • EuclideanSpace.single 0 1)) i = 0
    rw [map_smul, PiLp.smul_apply, smul_eq_mul, ← toEuclideanLin_pow]
    change c * (T ^ (j : ℕ) *ᵥ Pi.single 0 1) i = 0
    rw [hT.pow_mulVec_single_zero_apply_of_lt (by omega), mul_zero]
  | zero => rfl
  | add v w _ _ hv hw => simp only [PiLp.add_apply, hv, hw, add_zero]
  | smul r v _ hv => simp only [PiLp.smul_apply, hv, smul_zero]

/-- A solution of a positive definite upper Hessenberg system with first-coordinate
right-hand side has geometrically decreasing coordinates. The spectral interval may
be degenerate, and the first coordinate uses exponent zero. -/
theorem IsUpperHessenberg.solution_coordinate_le
    (hT : T.IsUpperHessenberg) {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hB : (toEuclideanLin T).IsSymmetricBoundedBy a b)
    {x : EuclideanSpace ℝ (Fin (N + 1))}
    (hx : toEuclideanLin T x = c • EuclideanSpace.single 0 1) (i : Fin (N + 1)) :
    |x i| ≤ 2 * ((Real.sqrt (b / a) - 1) / (Real.sqrt (b / a) + 1)) ^ (i : ℕ) * ‖x‖ := by
  rcases hab.lt_or_eq with hab | rfl
  · let p := shifted (i : ℕ) a b 0
    have hp : p.eval 0 = 1 := shifted_eval_self (i : ℕ) hab (by
      intro h; exact (not_le_of_gt ha) h.1)
    obtain ⟨z, hz, hres⟩ := Krylov.exists_mem_of_residual_poly
      (A := toEuclideanLin T) (b := toEuclideanLin T x) (x₀ := 0)
      p (shifted_degree_le _ _ _ _) hp
    simp only [map_zero, sub_zero] at hz hres
    have herror : x - z = aeval (toEuclideanLin T) p x := by
      apply (hB.isSymmetricCoercive ha).isCoercive.injective
      rw [map_sub, hres, Module.End.aeval_apply_apply]
    have hzi : z i = 0 := hT.apply_eq_zero_of_mem_krylov (by rwa [hx] at hz) le_rfl
    have hpoly : ‖aeval (toEuclideanLin T) p x‖ ≤
        (2 * ((Real.sqrt (b / a) - 1) / (Real.sqrt (b / a) + 1)) ^ (i : ℕ)) * ‖x‖ :=
      norm_aeval_shifted_le ha hab hB (i : ℕ) x
    calc |x i| = ‖(x - z) i‖ := by simp [PiLp.sub_apply, hzi, Real.norm_eq_abs]
      _ ≤ ‖x - z‖ := PiLp.norm_apply_le _ _
      _ = ‖aeval (toEuclideanLin T) p x‖ := congrArg norm herror
      _ ≤ _ := hpoly
  · by_cases hi : (i : ℕ) = 0
    · simp only [hi, pow_zero, mul_one]
      exact (show |x i| ≤ ‖x‖ by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i).trans
        (by nlinarith [norm_nonneg x])
    · have hscalar := hB.apply_eq_smul x
      rw [hx] at hscalar
      have he : x = a⁻¹ • (c • EuclideanSpace.single 0 1) := by
        simpa only [RCLike.ofReal_real_eq_id, id_eq, smul_smul,
          inv_mul_cancel₀ ha.ne', one_smul] using (congrArg (fun v => a⁻¹ • v) hscalar).symm
      have hi0 : i ≠ 0 := fun h => hi (congrArg Fin.val h)
      simp [he, PiLp.smul_apply, hi0,
        div_self ha.ne', Real.sqrt_one, zero_pow hi]

/-- Cyclicity rules out a singular positive semidefinite Hessenberg matrix whose
range contains a nonzero first coordinate vector. No optimizer is assumed. -/
theorem IsUnreducedUpperHessenberg.posDef_of_posSemidef_of_solve_first
    (hT : T.IsUnreducedUpperHessenberg) (hP : T.PosSemidef) {c : ℝ} (hc : c ≠ 0)
    {x : EuclideanSpace ℝ (Fin (N + 1))}
    (hx : toEuclideanLin T x = c • EuclideanSpace.single 0 1) : T.PosDef := by
  let A := toEuclideanLin T
  have hstart : EuclideanSpace.single (0 : Fin (N + 1)) 1 ∈ A.range := by
    refine ⟨c⁻¹ • x, ?_⟩
    rw [map_smul, hx, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hK : Krylov.fullSubspace A (EuclideanSpace.single 0 1) ≤ A.range :=
    Krylov.fullSubspace_le_of_mem_invtSubmodule A _
      (fun z hz => ⟨z, rfl⟩) hstart
  have hcols : (toEuclideanLin (krylovMatrix T (Pi.single 0 1) (N + 1))).range ≤
      A.range := by
    rw [range_toEuclideanLin_eq_span_col]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    apply hK
    apply Submodule.subset_span
    refine ⟨(j : ℕ), ?_⟩
    change (toEuclideanLin T ^ (j : ℕ)) (EuclideanSpace.single 0 1) =
      WithLp.toLp 2 ((krylovMatrix T (Pi.single 0 1) (N + 1)).col j)
    rw [col_krylovMatrix, ← toEuclideanLin_pow]
    rfl
  have hsurjK : Function.Surjective
      (toEuclideanLin (krylovMatrix T (Pi.single 0 1) (N + 1))) := by
    intro y
    obtain ⟨w, hw⟩ := mulVec_surjective_iff_isUnit.mpr hT.isUnit_krylovMatrix
      (WithLp.ofLp y)
    exact ⟨WithLp.toLp 2 w, congrArg (WithLp.toLp 2) hw⟩
  rw [LinearMap.range_eq_top.mpr hsurjK] at hcols
  have hsurj : Function.Surjective A := LinearMap.range_eq_top.mp (top_le_iff.mp hcols)
  apply hP.posDef_iff_isUnit.mpr
  apply mulVec_surjective_iff_isUnit.mp
  intro y
  obtain ⟨z, hz⟩ := hsurj (WithLp.toLp 2 y)
  exact ⟨WithLp.ofLp z, congrArg WithLp.ofLp hz⟩

end Matrix

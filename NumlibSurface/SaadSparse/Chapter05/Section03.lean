import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.LinearSolve.Projection.Basic
import Numlib.LinearSolve.Projection.OneDimensional
import NumlibSurface.SaadSparse.Chapter05.Section01

/-!
# Saad §5.3: one-dimensional projection processes

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §5.3: the elementary step (5.12), steepest descent (Algorithm 5.2), Kantorovich's inequality
(Lemma 5.8) and Theorem 5.9, the minimal-residual iteration (Algorithm 5.3) and Theorem 5.10, and
the residual-norm steepest descent (Algorithm 5.4).

All three steps are the backbone's `Projection.step1` for `Matrix.toEuclideanLin A`
(`step1_eq`, `sdStep_eq`, `mrStep_eq` are `rfl`), so the convergence estimates specialize
`Numlib/LinearSolve/Projection/OneDimensional.lean`.

The exact one-step identities specialize the backbone's
`Projection.norm_residual_minResStep_sq_eq` and `Projection.energyNorm_steepestDescentStep_sq_eq`:
`equation_5_18` is the book's (5.16)–(5.18), `norm_residual_mrStep_eq_sin` is the `sin ∠` reading
of (5.18), and `energyNorm_sdStep_sq_eq` is the unnumbered display closing the proof of Theorem
5.9.  Saad's own (5.20), the alternative residual bound
`‖r_{k+1}‖₂² ≤ (1 - μ(A) μ(A⁻¹)) ‖r_k‖₂²`, is `equation_5_20`; the convergence factor
`ρ = sup_{x ≠ 0} sin ∠(x, A x) < 1` that §5.3.2 reads off (5.18) is `sinAngleSup`.

Each of Algorithms 5.2–5.4 is printed with a *recursively updated* residual, one matrix–vector
product per step; `sdAlgStep`, `mrAlgStep` and `rnsdAlgStep` are those state machines and
`sdAlg_spec`, `mrAlg_spec`, `rnsdAlg_spec` say that the carried vector really is `b - A x_k`, so
that each algorithm computes the corresponding projection iterate.

Example 5.1 is `example_5_1`: the elementary relaxation step at coordinate `i` is the projection
step onto `span {e_i}` orthogonally to `span {e_i}`, and it annihilates component `i` of the
residual, which is Saad's (4.6).
-/

open Matrix Module Filter Topology
open scoped SaadSparse

namespace SaadSparse.Chapter05

variable {n : ℕ}

/-- Saad Chapter 5 works in `ℝⁿ`. -/
local notation "E" n => EuclideanSpace ℝ (Fin n)

variable {A : Matrix (Fin n) (Fin n) ℝ} {b x₀ x : E n}

/-! ### The elementary step (5.12) -/

/-- Saad (5.12): the one-dimensional projection step onto `span {v}` orthogonally to
`span {w}`. -/
noncomputable def step1 (A : Matrix (Fin n) (Fin n) ℝ) (b v w x : E n) : E n :=
  x + (inner ℝ w (b - (A ⬝ x)) / inner ℝ w (A ⬝ v)) • v

/-- Saad (5.12) is the backbone's `Projection.step1`. -/
theorem step1_eq (A : Matrix (Fin n) (Fin n) ℝ) (b v w x : E n) :
    step1 A b v w x = Projection.step1 (toEuclideanLin A) b v w x := rfl

/-- Saad (5.12): the step is a projection step onto `span {v}` orthogonally to `span {w}`. -/
theorem step1_isProjectionApprox (v w : E n) (h : inner ℝ w (A ⬝ v) ≠ 0) :
    IsProjectionApprox A b x (ℝ ∙ v) (ℝ ∙ w) (step1 A b v w x) :=
  isProjectionApprox_iff.mpr (Projection.step1_isPetrovGalerkin v w x h)

/-- Saad (5.12): the step is the *unique* such approximation. -/
theorem isProjectionApprox_span_singleton_iff {v w x' : E n} (h : inner ℝ w (A ⬝ v) ≠ 0) :
    IsProjectionApprox A b x (ℝ ∙ v) (ℝ ∙ w) x' ↔ x' = step1 A b v w x := by
  refine ⟨fun hx' => ?_, fun hx' => hx' ▸ step1_isProjectionApprox v w h⟩
  refine (isProjectionApprox_iff.mp hx').eq_of_forall
    (isProjectionApprox_iff.mp (step1_isProjectionApprox v w h)) fun z hz hAz => ?_
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have h0 : inner ℝ w (toEuclideanLin A (c • v)) = 0 :=
    (Submodule.mem_orthogonal _ _).1 hAz w (Submodule.mem_span_singleton_self w)
  rw [map_smul, inner_smul_right] at h0
  rcases mul_eq_zero.mp h0 with hc | hcon
  · rw [hc, zero_smul]
  · exact absurd hcon h

/-! ### Steepest descent (Algorithm 5.2) and minimal residual (Algorithm 5.3) -/

/-- Saad, Algorithm 5.2: the steepest-descent step `v = w = r`. -/
noncomputable def sdStep (A : Matrix (Fin n) (Fin n) ℝ) (b x : E n) : E n :=
  step1 A b (b - (A ⬝ x)) (b - (A ⬝ x)) x

/-- Saad, Algorithm 5.3: the minimal-residual step `v = r`, `w = A r`. -/
noncomputable def mrStep (A : Matrix (Fin n) (Fin n) ℝ) (b x : E n) : E n :=
  step1 A b (b - (A ⬝ x)) (A ⬝ (b - (A ⬝ x))) x

/-- Saad, Algorithm 5.4: the residual-norm steepest-descent step `v = Aᵀ r`, `w = A v`. -/
noncomputable def rnsdStep (A : Matrix (Fin n) (Fin n) ℝ) (b x : E n) : E n :=
  step1 A b (Aᵀ ⬝ (b - (A ⬝ x))) (A ⬝ (Aᵀ ⬝ (b - (A ⬝ x)))) x

theorem sdStep_eq (A : Matrix (Fin n) (Fin n) ℝ) (b x : E n) :
    sdStep A b x = Projection.steepestDescentStep (toEuclideanLin A) b x := rfl

theorem mrStep_eq (A : Matrix (Fin n) (Fin n) ℝ) (b x : E n) :
    mrStep A b x = Projection.minResStep (toEuclideanLin A) b x := rfl

/-- Saad, Algorithm 5.2: each steepest-descent step is an orthogonal projection step onto the
residual direction. -/
theorem sdStep_isProjectionApprox (hA : A.IsPositiveReal) (b x : E n) :
    IsProjectionApprox A b x (ℝ ∙ (b - (A ⬝ x))) (ℝ ∙ (b - (A ⬝ x))) (sdStep A b x) :=
  isProjectionApprox_iff.mpr
    (Projection.steepestDescentStep_isGalerkin x ((Matrix.isPositiveReal_iff_isCoercive A).mp hA))

/-- Saad, Algorithm 5.2: the steepest-descent step minimizes the energy norm of the error along
the residual line. -/
theorem sdStep_min (hA : A.PosDef) {xstar : E n} (hstar : (A ⬝ xstar) = b) (x y : E n)
    (hy : y - x ∈ (ℝ ∙ (b - (A ⬝ x)))) : E_A A xstar (sdStep A b x) ≤ E_A A xstar y := by
  have hpr : A.IsPositiveReal := by
    rw [Matrix.isPositiveReal_iff_isCoercive]
    exact ((Matrix.posDef_iff_isSymmetricCoercive A).mp hA).isCoercive
  exact ((proposition_5_2 hA hstar).mp (sdStep_isProjectionApprox hpr b x)).2 y hy

/-- Saad, Algorithm 5.3: each minimal-residual step minimizes the residual norm along the
residual line. -/
theorem mrStep_min (b x y : E n)
    (hy : y - x ∈ (ℝ ∙ (b - (A ⬝ x)))) : R_A A b (mrStep A b x) ≤ R_A A b y :=
  (Projection.minResStep_isMinRes x).min y hy

/-! ### Lemma 5.8 (Kantorovich) -/

variable [NeZero n]

/-- `λ_min` of a symmetric positive definite matrix is positive, every eigenvalue of it being
positive.  This is the hypothesis all the estimates of §5.3 take. -/
private theorem lambdaMin_pos {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosDef) :
    0 < lambdaMin hB.1 := by
  rw [lambdaMin, Finset.lt_inf'_iff]
  exact fun i _ => Matrix.PosDef.eigenvalues_pos hB i

/-- Saad, Lemma 5.8 (Kantorovich's inequality): for a real SPD `B`,
`(Bx, x)(B⁻¹x, x) ≤ (λ_max + λ_min)²/(4 λ_max λ_min) (x, x)²`. -/
theorem lemma_5_8 {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosDef) (x : Fin n → ℝ) :
    ((B *ᵥ x) ⬝ᵥ x) * ((B⁻¹ *ᵥ x) ⬝ᵥ x) ≤
      (lambdaMax hB.1 + lambdaMin hB.1) ^ 2 / (4 * lambdaMax hB.1 * lambdaMin hB.1) *
        (x ⬝ᵥ x) ^ 2 := by
  have hl : 0 < lambdaMin hB.1 := lambdaMin_pos hB
  have hsb := isSymmetricBoundedBy_toEuclideanLin hB.1
  have hdet : IsUnit B.det := (isUnit_iff_isUnit_det B).mp hB.isUnit
  have hBB : B *ᵥ (B⁻¹ *ᵥ x) = x := by
    rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  have hy : toEuclideanLin B (WithLp.toLp 2 (B⁻¹ *ᵥ x)) = (WithLp.toLp 2 x : E n) :=
    congrArg (WithLp.toLp 2) hBB
  have hk := Projection.kantorovich_inequality hl hsb (WithLp.toLp 2 x : E n) hy
  rw [real_inner_apply_self] at hk
  have h1 : (inner ℝ (WithLp.toLp 2 (B⁻¹ *ᵥ x) : E n) (WithLp.toLp 2 x : E n))
      = (B⁻¹ *ᵥ x) ⬝ᵥ x := by
    rw [inner_eq_dotProduct_star, dotProduct_comm]
    simp
  have h4 : ‖(WithLp.toLp 2 x : E n)‖ ^ 4 = (x ⬝ᵥ x) ^ 2 := by
    have h2 : ‖(WithLp.toLp 2 x : E n)‖ ^ 2 = x ⬝ᵥ x := real_norm_sq_eq_dotProduct _
    calc ‖(WithLp.toLp 2 x : E n)‖ ^ 4 = (‖(WithLp.toLp 2 x : E n)‖ ^ 2) ^ 2 := by ring
      _ = (x ⬝ᵥ x) ^ 2 := by rw [h2]
  rw [h1, h4] at hk
  simpa [RCLike.re_to_real] using hk

/-! ### Theorem 5.9 -/

/-- Saad, Theorem 5.9: the steepest-descent step contracts the energy norm of the error by the
factor `(λ_max - λ_min)/(λ_max + λ_min)`. -/
theorem theorem_5_9_step (hA : A.PosDef) {xstar : E n} (hstar : (A ⬝ xstar) = b) (x : E n) :
    E_A A xstar (sdStep A b x) ≤
      (lambdaMax hA.1 - lambdaMin hA.1) / (lambdaMax hA.1 + lambdaMin hA.1) *
        E_A A xstar x :=
  Projection.energyNorm_steepestDescentStep_le (lambdaMin_pos hA)
    (isSymmetricBoundedBy_toEuclideanLin hA.1) hstar x

/-- The contraction factor of Theorem 5.9 lies in `[0, 1)`. -/
theorem theorem_5_9_factor_lt_one {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosDef) :
    0 ≤ (lambdaMax hH.1 - lambdaMin hH.1) / (lambdaMax hH.1 + lambdaMin hH.1) ∧
      (lambdaMax hH.1 - lambdaMin hH.1) / (lambdaMax hH.1 + lambdaMin hH.1) < 1 := by
  have hl : 0 < lambdaMin hH.1 := lambdaMin_pos hH
  have hle : lambdaMin hH.1 ≤ lambdaMax hH.1 := lambdaMin_le_lambdaMax hH.1
  have hsum : 0 < lambdaMax hH.1 + lambdaMin hH.1 := by linarith
  refine ⟨div_nonneg (by linarith) hsum.le, ?_⟩
  rw [div_lt_one hsum]
  linarith

/-- Saad, Theorem 5.9: geometric decay of the energy norm of the error along Algorithm 5.2. -/
theorem theorem_5_9 (hA : A.PosDef) {xstar : E n} (hstar : (A ⬝ xstar) = b) (x₀ : E n) (k : ℕ) :
    E_A A xstar ((sdStep A b)^[k] x₀) ≤
      ((lambdaMax hA.1 - lambdaMin hA.1) / (lambdaMax hA.1 + lambdaMin hA.1)) ^ k *
        E_A A xstar x₀ := by
  obtain ⟨hnn, -⟩ := theorem_5_9_factor_lt_one hA
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ]
    refine (theorem_5_9_step hA hstar _).trans ?_
    calc (lambdaMax hA.1 - lambdaMin hA.1) / (lambdaMax hA.1 + lambdaMin hA.1) *
            E_A A xstar ((sdStep A b)^[k] x₀)
        ≤ (lambdaMax hA.1 - lambdaMin hA.1) / (lambdaMax hA.1 + lambdaMin hA.1) *
            (((lambdaMax hA.1 - lambdaMin hA.1) / (lambdaMax hA.1 + lambdaMin hA.1)) ^ k *
              E_A A xstar x₀) := mul_le_mul_of_nonneg_left ih hnn
      _ = ((lambdaMax hA.1 - lambdaMin hA.1) / (lambdaMax hA.1 + lambdaMin hA.1)) ^ k *
            ((lambdaMax hA.1 - lambdaMin hA.1) / (lambdaMax hA.1 + lambdaMin hA.1)) *
            E_A A xstar x₀ := by ring

/-- Saad, Theorem 5.9: Algorithm 5.2 converges to the solution from every starting vector. -/
theorem theorem_5_9_tendsto (hA : A.PosDef) {xstar : E n} (hstar : (A ⬝ xstar) = b) (x₀ : E n) :
    Tendsto (fun k => (sdStep A b)^[k] x₀) atTop (𝓝 xstar) := by
  have hl : 0 < lambdaMin hA.1 := lambdaMin_pos hA
  obtain ⟨hnn, hlt⟩ := theorem_5_9_factor_lt_one hA
  set ρ := (lambdaMax hA.1 - lambdaMin hA.1) / (lambdaMax hA.1 + lambdaMin hA.1) with hρ
  have hs : 0 < Real.sqrt (lambdaMin hA.1) := Real.sqrt_pos.mpr hl
  have hcoer : (toEuclideanLin A).IsCoerciveWith (lambdaMin hA.1) :=
    (isSymmetricBoundedBy_toEuclideanLin hA.1).isCoerciveWith
  have hbound : ∀ k, ‖(sdStep A b)^[k] x₀ - xstar‖ ≤
      (Real.sqrt (lambdaMin hA.1))⁻¹ * (ρ ^ k * E_A A xstar x₀) := by
    intro k
    have h1 := hcoer.norm_le_energyNorm hl.le (xstar - (sdStep A b)^[k] x₀)
    have h2 : energyNorm (toEuclideanLin A) (xstar - (sdStep A b)^[k] x₀)
        ≤ ρ ^ k * E_A A xstar x₀ := theorem_5_9 hA hstar x₀ k
    rw [← norm_neg, neg_sub, inv_mul_eq_div, le_div_iff₀ hs, mul_comm]
    exact h1.trans h2
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm hbound ?_
  have hpow : Tendsto (fun k => ρ ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hnn hlt
  simpa using ((hpow.mul_const (E_A A xstar x₀)).const_mul (Real.sqrt (lambdaMin hA.1))⁻¹)

/-! ### Theorem 5.10 -/

omit [NeZero n] in
/-- The Hermitian part of a positive real matrix is SPD. -/
theorem posDef_hermitianPart (hA : A.IsPositiveReal) : (Matrix.hermitianPart A).PosDef := by
  rw [Matrix.posDef_iff_isSymmetricCoercive]
  obtain ⟨c, hc, hcA⟩ := (Matrix.isPositiveReal_iff_isCoercive A).mp hA
  refine ⟨isSymmetric_toEuclideanLin_iff.mpr (Matrix.hermitianPart_isHermitian A), c, hc, ?_⟩
  intro u
  rw [Matrix.re_inner_hermitianPart A u]
  exact hcA u

/-- Saad, Theorem 5.10: `μ = λ_min((A + Aᵀ)/2) > 0` for a positive real `A`. -/
theorem lambdaMin_hermitianPart_pos (hA : A.IsPositiveReal) :
    0 < lambdaMin (Matrix.hermitianPart_isHermitian A) :=
  lambdaMin_pos (posDef_hermitianPart hA)

open scoped Matrix.Norms.L2Operator in
/-- Saad, Theorem 5.10: the minimal-residual step contracts the residual by the factor
`(1 - μ²/σ²)^{1/2}` with `μ = λ_min((A + Aᵀ)/2)` and `σ = ‖A‖₂`. -/
theorem theorem_5_10_step (hA : A.IsPositiveReal) (b x : E n) :
    ‖b - (A ⬝ mrStep A b x)‖ ≤
      Real.sqrt (1 - lambdaMin (Matrix.hermitianPart_isHermitian A) ^ 2 / ‖A‖ ^ 2) *
        ‖b - (A ⬝ x)‖ := by
  have hpos := lambdaMin_hermitianPart_pos hA
  have hcoer := Chapter01.isCoerciveWith_lambdaMin A
  rw [Matrix.l2_opNorm_eq_norm_toEuclideanLin A]
  exact Projection.norm_residual_minResStep_le
    (A := LinearMap.toContinuousLinearMap (toEuclideanLin A)) hpos hcoer b x

open scoped Matrix.Norms.L2Operator in
/-- Saad, Theorem 5.10: `μ = λ_min((A + Aᵀ)/2)` never exceeds `σ = ‖A‖₂`, because the coercivity
constant is a lower bound for `‖A u‖/‖u‖`.  This is what makes the factor of Theorem 5.10 real and
less than `1`. -/
theorem lambdaMin_hermitianPart_le_opNorm (A : Matrix (Fin n) (Fin n) ℝ) :
    lambdaMin (Matrix.hermitianPart_isHermitian A) ≤ ‖A‖ := by
  obtain ⟨i⟩ : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  set u : E n := EuclideanSpace.single i (1 : ℝ) with hudef
  have hu : ‖u‖ = 1 := by simp [hudef]
  have h1 := (Chapter01.isCoerciveWith_lambdaMin A).norm_le_norm_apply u
  have h2 : ‖LinearMap.toContinuousLinearMap (toEuclideanLin A) u‖
      ≤ ‖LinearMap.toContinuousLinearMap (toEuclideanLin A)‖ * ‖u‖ :=
    ContinuousLinearMap.le_opNorm _ u
  have heq : LinearMap.toContinuousLinearMap (toEuclideanLin A) u = (A ⬝ u) := rfl
  rw [heq, hu, mul_one] at h2
  rw [hu, mul_one] at h1
  rw [Matrix.l2_opNorm_eq_norm_toEuclideanLin A]
  linarith

open scoped Matrix.Norms.L2Operator in
/-- The contraction factor of Theorem 5.10 lies in `[0, 1)`. -/
theorem theorem_5_10_factor_lt_one (hA : A.IsPositiveReal) :
    Real.sqrt (1 - lambdaMin (Matrix.hermitianPart_isHermitian A) ^ 2 / ‖A‖ ^ 2) < 1 := by
  have hpos := lambdaMin_hermitianPart_pos hA
  have hnorm : 0 < ‖A‖ := lt_of_lt_of_le hpos (lambdaMin_hermitianPart_le_opNorm A)
  have hfrac : 0 < lambdaMin (Matrix.hermitianPart_isHermitian A) ^ 2 / ‖A‖ ^ 2 := by positivity
  rw [Real.sqrt_lt' one_pos, one_pow]
  linarith

open scoped Matrix.Norms.L2Operator in
/-- Saad, Theorem 5.10: geometric decay of the residual along Algorithm 5.3,
`‖r_k‖₂ ≤ (1 - μ²/σ²)^{k/2} ‖r_0‖₂`. -/
theorem theorem_5_10 (hA : A.IsPositiveReal) (b x₀ : E n) (k : ℕ) :
    ‖b - (A ⬝ ((mrStep A b)^[k] x₀))‖ ≤
      Real.sqrt (1 - lambdaMin (Matrix.hermitianPart_isHermitian A) ^ 2 / ‖A‖ ^ 2) ^ k *
        ‖b - (A ⬝ x₀)‖ := by
  set ρ := Real.sqrt (1 - lambdaMin (Matrix.hermitianPart_isHermitian A) ^ 2 / ‖A‖ ^ 2) with hρ
  have hnn : 0 ≤ ρ := Real.sqrt_nonneg _
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ]
    refine (theorem_5_10_step hA b _).trans ?_
    calc ρ * ‖b - (A ⬝ ((mrStep A b)^[k] x₀))‖
        ≤ ρ * (ρ ^ k * ‖b - (A ⬝ x₀)‖) := mul_le_mul_of_nonneg_left ih hnn
      _ = ρ ^ k * ρ * ‖b - (A ⬝ x₀)‖ := by ring

/-- Saad, Theorem 5.10: Algorithm 5.3 converges to the solution from every starting vector.  The
error is controlled by the residual through the coercivity bound `μ ‖x‖₂ ≤ ‖A x‖₂`, so the
geometric decay of `theorem_5_10` carries over to the iterates themselves. -/
theorem theorem_5_10_tendsto (hA : A.IsPositiveReal) (b x₀ : E n) :
    Tendsto (fun k => (mrStep A b)^[k] x₀) atTop (𝓝 (A⁻¹ ⬝ b)) := by
  have hdet : IsUnit A.det := (isUnit_iff_isUnit_det A).mp (Chapter01.theorem_1_34 hA).1
  have hpos := lambdaMin_hermitianPart_pos hA
  have hb : A *ᵥ (A⁻¹ *ᵥ WithLp.ofLp b) = WithLp.ofLp b := by
    rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  have hstar : (A ⬝ (A⁻¹ ⬝ b)) = b := congrArg (WithLp.toLp 2) hb
  have hres : ∀ y : E n, (A ⬝ ((A⁻¹ ⬝ b) - y)) = b - (A ⬝ y) := fun y => by
    rw [map_sub, hstar]
  refine Projection.tendsto_of_forall_norm_succ_le
    (N := fun v => ‖(A ⬝ v)‖) (C := (lambdaMin (Matrix.hermitianPart_isHermitian A))⁻¹)
    (fun v => ?_) (fun _ => norm_nonneg _) (Real.sqrt_nonneg _)
    (theorem_5_10_factor_lt_one hA) (fun k => ?_)
  · have h := (Chapter01.isCoerciveWith_lambdaMin A).norm_le_norm_apply v
    rw [inv_mul_eq_div, le_div_iff₀ hpos]
    linarith
  · simp only [hres, Function.iterate_succ_apply']
    exact theorem_5_10_step hA b _

/-! ### Algorithm 5.4 -/

omit [NeZero n] in
/-- Over `ℝ`, `Aᵀ` is the adjoint of `A`: `(A u, v) = (u, Aᵀ v)`. -/
theorem real_inner_transpose (A : Matrix (Fin n) (Fin n) ℝ) (u v : E n) :
    inner ℝ (A ⬝ u) v = inner ℝ u (Aᵀ ⬝ v) := by
  rw [real_inner_apply, real_inner_toEuclideanLin', dotProduct_mulVec, mulVec_transpose]

omit [NeZero n] in
/-- Saad §5.3.3: `AᵀA` is SPD for a nonsingular `A`. -/
theorem posDef_transpose_mul_self (hA : IsUnit A) : (Aᵀ * A).PosDef := by
  have hinj : Function.Injective A.mulVec := mulVec_injective_iff_isUnit.mpr hA
  rw [← Matrix.isSPD_iff_posDef]
  refine ⟨?_, fun u hu => ?_⟩
  · change (Aᵀ * A)ᵀ = Aᵀ * A
    rw [transpose_mul, transpose_transpose]
  · have hAu : A *ᵥ u ≠ 0 := fun h => hu (hinj (by rw [h, mulVec_zero]))
    have hkey : ((Aᵀ * A) *ᵥ u) ⬝ᵥ u = (A *ᵥ u) ⬝ᵥ (A *ᵥ u) := by
      rw [← mulVec_mulVec, dotProduct_comm, dotProduct_mulVec, vecMul_transpose]
    obtain ⟨i, hi⟩ : ∃ i, (A *ᵥ u) i ≠ 0 := Function.ne_iff.mp hAu
    rw [hkey, dotProduct]
    exact Finset.sum_pos' (fun j _ => mul_self_nonneg _)
      ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩

omit [NeZero n] in
/-- The normal-equations operator: `AᵀA x` is `Aᵀ (A x)`. -/
private theorem toEuclideanLin_normal (A : Matrix (Fin n) (Fin n) ℝ) (z : E n) :
    ((Aᵀ * A) ⬝ z) = Aᵀ ⬝ (A ⬝ z) := by
  have h : (Aᵀ * A) *ᵥ WithLp.ofLp z = Aᵀ *ᵥ (A *ᵥ WithLp.ofLp z) := (mulVec_mulVec _ _ _).symm
  exact congrArg (WithLp.toLp 2) h

omit [NeZero n] in
/-- Saad §5.3.3: Algorithm 5.4 is steepest descent applied to the normal equations
`AᵀA x = Aᵀ b`. -/
theorem rnsdStep_eq_sdStep_normal (A : Matrix (Fin n) (Fin n) ℝ) (b x : E n) :
    rnsdStep A b x = sdStep (Aᵀ * A) (Aᵀ ⬝ b) x := by
  have hAA : ∀ z : E n, ((Aᵀ * A) ⬝ z) = Aᵀ ⬝ (A ⬝ z) := by
    intro z
    have h : (Aᵀ * A) *ᵥ WithLp.ofLp z = Aᵀ *ᵥ (A *ᵥ WithLp.ofLp z) :=
      (mulVec_mulVec _ _ _).symm
    exact congrArg (WithLp.toLp 2) h
  have hres : (Aᵀ ⬝ b) - ((Aᵀ * A) ⬝ x) = Aᵀ ⬝ (b - (A ⬝ x)) := by
    rw [hAA, ← map_sub]
  have hnum : inner ℝ (A ⬝ (Aᵀ ⬝ (b - (A ⬝ x)))) (b - (A ⬝ x))
      = inner ℝ (Aᵀ ⬝ (b - (A ⬝ x))) (Aᵀ ⬝ (b - (A ⬝ x))) :=
    real_inner_transpose A (Aᵀ ⬝ (b - (A ⬝ x))) (b - (A ⬝ x))
  have hden : inner ℝ (A ⬝ (Aᵀ ⬝ (b - (A ⬝ x)))) (A ⬝ (Aᵀ ⬝ (b - (A ⬝ x))))
      = inner ℝ (Aᵀ ⬝ (b - (A ⬝ x))) (Aᵀ ⬝ (A ⬝ (Aᵀ ⬝ (b - (A ⬝ x))))) :=
    real_inner_transpose A (Aᵀ ⬝ (b - (A ⬝ x))) (A ⬝ (Aᵀ ⬝ (b - (A ⬝ x))))
  rw [rnsdStep, sdStep, hres]
  simp only [step1]
  rw [hres, hAA, hnum, hden]

omit [NeZero n] in
/-- Saad §5.3.3: `(A x, A x)` is the `AᵀA`-energy of `x`, so the energy norm of the error of the
normal equations is the `2`-norm of the residual, `‖x* - x‖_{AᵀA} = ‖b - A x‖₂`.  This is what
turns Theorem 5.9 for `AᵀA` into a statement about the residuals of Algorithm 5.4. -/
theorem energyNorm_normal_eq_norm_residual (A : Matrix (Fin n) (Fin n) ℝ) {b xstar : E n}
    (hstar : (A ⬝ xstar) = b) (x : E n) : E_A (Aᵀ * A) xstar x = ‖b - (A ⬝ x)‖ := by
  have hAA := toEuclideanLin_normal A (xstar - x)
  have hd : (A ⬝ (xstar - x)) = b - (A ⬝ x) := by rw [map_sub, hstar]
  have hinner : inner ℝ ((Aᵀ * A) ⬝ (xstar - x)) (xstar - x) = ‖b - (A ⬝ x)‖ ^ 2 := by
    rw [hAA, real_inner_transpose Aᵀ (A ⬝ (xstar - x)) (xstar - x), transpose_transpose, hd,
      real_inner_self_eq_norm_sq]
  rw [E_A, hinner, Real.sqrt_sq (norm_nonneg _)]

omit [NeZero n] in
/-- Saad, Algorithm 5.4: each RNSD step minimizes the residual norm along the direction
`-∇f/2 = Aᵀ r`, since it is the projection step onto `span {Aᵀ r}` orthogonally to
`A span {Aᵀ r}` (Proposition 5.3). -/
theorem rnsdStep_min (hA : IsUnit A) (b x y : E n)
    (hy : y - x ∈ (ℝ ∙ (Aᵀ ⬝ (b - (A ⬝ x))))) : R_A A b (rnsdStep A b x) ≤ R_A A b y := by
  rcases eq_or_ne (Aᵀ ⬝ (b - (A ⬝ x))) 0 with h0 | h0
  · have hstep : rnsdStep A b x = x := by
      simp only [rnsdStep, step1, h0, smul_zero, add_zero]
    rw [Submodule.span_singleton_eq_bot.mpr h0, Submodule.mem_bot, sub_eq_zero] at hy
    exact le_of_eq (by rw [hy, hstep])
  · have hAv : (A ⬝ (Aᵀ ⬝ (b - (A ⬝ x)))) ≠ 0 :=
      fun hc => h0 (injective_toEuclideanLin hA (by rw [hc, map_zero]))
    have hne : inner ℝ (A ⬝ (Aᵀ ⬝ (b - (A ⬝ x)))) (A ⬝ (Aᵀ ⬝ (b - (A ⬝ x)))) ≠ 0 :=
      fun hc => hAv (inner_self_eq_zero.mp hc)
    have hmap : (ℝ ∙ (Aᵀ ⬝ (b - (A ⬝ x)))).map (toEuclideanLin A)
        = ℝ ∙ (A ⬝ (Aᵀ ⬝ (b - (A ⬝ x)))) := by
      rw [Submodule.map_span, Set.image_singleton]
    have hproj := step1_isProjectionApprox (A := A) (b := b) (x := x)
      (Aᵀ ⬝ (b - (A ⬝ x))) (A ⬝ (Aᵀ ⬝ (b - (A ⬝ x)))) hne
    rw [← hmap] at hproj
    exact (proposition_5_3.mp hproj).2 y hy

/-- Saad §5.3.3: the residuals of Algorithm 5.4 contract by the factor
`(λ_max(AᵀA) - λ_min(AᵀA))/(λ_max(AᵀA) + λ_min(AᵀA))`, which is Theorem 5.9 for the normal
equations read through `energyNorm_normal_eq_norm_residual`. -/
theorem rnsd_norm_residual_le (hA : IsUnit A) (b x₀ : E n) (k : ℕ) :
    ‖b - (A ⬝ ((rnsdStep A b)^[k] x₀))‖ ≤
      ((lambdaMax (posDef_transpose_mul_self hA).1 - lambdaMin (posDef_transpose_mul_self hA).1) /
          (lambdaMax (posDef_transpose_mul_self hA).1 +
            lambdaMin (posDef_transpose_mul_self hA).1)) ^ k * ‖b - (A ⬝ x₀)‖ := by
  have hdet : IsUnit A.det := (isUnit_iff_isUnit_det A).mp hA
  have hb : A *ᵥ (A⁻¹ *ᵥ WithLp.ofLp b) = WithLp.ofLp b := by
    rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  have hstar : (A ⬝ (A⁻¹ ⬝ b)) = b := congrArg (WithLp.toLp 2) hb
  have hnormal : ((Aᵀ * A) ⬝ (A⁻¹ ⬝ b)) = Aᵀ ⬝ b := by
    rw [toEuclideanLin_normal, hstar]
  have hfun : rnsdStep A b = sdStep (Aᵀ * A) (Aᵀ ⬝ b) := funext (rnsdStep_eq_sdStep_normal A b)
  have h := theorem_5_9 (posDef_transpose_mul_self hA) hnormal x₀ k
  rw [← hfun] at h
  rwa [energyNorm_normal_eq_norm_residual A hstar, energyNorm_normal_eq_norm_residual A hstar] at h

/-- Saad §5.3.3: Algorithm 5.4 converges to the solution from every starting vector whenever `A`
is nonsingular — it is Algorithm 5.2 for the SPD normal equations `AᵀA x = Aᵀ b`, so Theorem 5.9
applies. -/
theorem rnsd_tendsto (hA : IsUnit A) (b x₀ : E n) :
    Tendsto (fun k => (rnsdStep A b)^[k] x₀) atTop (𝓝 (A⁻¹ ⬝ b)) := by
  have hdet : IsUnit A.det := (isUnit_iff_isUnit_det A).mp hA
  have hb : A *ᵥ (A⁻¹ *ᵥ WithLp.ofLp b) = WithLp.ofLp b := by
    rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  have hstar : (A ⬝ (A⁻¹ ⬝ b)) = b := congrArg (WithLp.toLp 2) hb
  have hnormal : ((Aᵀ * A) ⬝ (A⁻¹ ⬝ b)) = Aᵀ ⬝ b := by
    rw [toEuclideanLin_normal, hstar]
  have hfun : rnsdStep A b = sdStep (Aᵀ * A) (Aᵀ ⬝ b) := funext (rnsdStep_eq_sdStep_normal A b)
  rw [hfun]
  exact theorem_5_9_tendsto (posDef_transpose_mul_self hA) hnormal x₀

/-! ### The exact one-step identities (5.16)–(5.18) and (5.20) -/

omit [NeZero n] in
/-- Saad (5.16)–(5.18): the exact one-step residual identity of the minimal-residual iteration,
`‖r_{k+1}‖² = ‖r_k‖² (1 - (A r_k, r_k)² / ((r_k, r_k) (A r_k, A r_k)))`.

No hypothesis is needed: at a breakdown, where `r_k = 0` or `A r_k = 0`, both sides read `‖r_k‖²`,
because division by zero is zero. -/
theorem equation_5_18 (A : Matrix (Fin n) (Fin n) ℝ) (b x : E n) :
    ‖b - (A ⬝ mrStep A b x)‖ ^ 2 =
      ‖b - (A ⬝ x)‖ ^ 2 *
        (1 - inner ℝ (A ⬝ (b - (A ⬝ x))) (b - (A ⬝ x)) ^ 2 /
          (‖b - (A ⬝ x)‖ ^ 2 * ‖A ⬝ (b - (A ⬝ x))‖ ^ 2)) := by
  have h := Projection.norm_residual_minResStep_sq_eq (A := toEuclideanLin A) (b := b) x
  rw [mrStep_eq]
  simpa only [Real.norm_eq_abs, sq_abs] using h

omit [NeZero n] in
/-- Saad §5.3.2, the geometric reading of (5.18): `‖r_{k+1}‖ = ‖r_k‖ sin ∠(r_k, A r_k)`, where
`cos ∠(r_k, A r_k) = (A r_k, r_k) / (‖A r_k‖ ‖r_k‖)`. -/
theorem norm_residual_mrStep_eq_sin (A : Matrix (Fin n) (Fin n) ℝ) (b x : E n) :
    ‖b - (A ⬝ mrStep A b x)‖ =
      ‖b - (A ⬝ x)‖ * Real.sin (InnerProductGeometry.angle (b - (A ⬝ x)) (A ⬝ (b - (A ⬝ x)))) := by
  set r : E n := b - (A ⬝ x) with hr
  have hnn : 0 ≤ ‖r‖ * Real.sin (InnerProductGeometry.angle r (A ⬝ r)) :=
    mul_nonneg (norm_nonneg _) (InnerProductGeometry.sin_angle_nonneg _ _)
  refine ((pow_left_inj₀ (norm_nonneg _) hnn two_ne_zero).mp ?_)
  rw [mul_pow, Real.sin_sq, InnerProductGeometry.cos_angle, equation_5_18]
  rw [real_inner_comm (A ⬝ r) r, div_pow, mul_pow]

omit [NeZero n] in
/-- The exact one-step identity of steepest descent in the `A`-norm,
`‖d_{k+1}‖_A² = ‖d_k‖_A² (1 - (r_k, r_k)² / ((A r_k, r_k) (A⁻¹ r_k, r_k)))`, from which
Theorem 5.9 follows by Kantorovich's inequality (Lemma 5.8).

This is the last display in the proof of Theorem 5.9 in §5.3.1, which the book leaves unnumbered;
Saad's (5.20) is the *residual* bound `equation_5_20` of §5.3.2 below. -/
theorem energyNorm_sdStep_sq_eq (hA : A.PosDef) {xstar : E n} (hstar : (A ⬝ xstar) = b) (x : E n) :
    E_A A xstar (sdStep A b x) ^ 2 =
      E_A A xstar x ^ 2 *
        (1 - inner ℝ (b - (A ⬝ x)) (b - (A ⬝ x)) ^ 2 /
          (inner ℝ (A ⬝ (b - (A ⬝ x))) (b - (A ⬝ x)) *
            inner ℝ (A⁻¹ ⬝ (b - (A ⬝ x))) (b - (A ⬝ x)))) := by
  have hsc : (toEuclideanLin A).IsSymmetricCoercive :=
    (Matrix.posDef_iff_isSymmetricCoercive A).mp hA
  have hdet : IsUnit A.det := (isUnit_iff_isUnit_det A).mp hA.isUnit
  -- the error is `A⁻¹ r`, so the energy norm of the error is `⟪A⁻¹ r, r⟫`
  have hAd : (A ⬝ (xstar - x)) = b - (A ⬝ x) := by rw [map_sub, hstar]
  have hd : xstar - x = (A⁻¹ ⬝ (b - (A ⬝ x))) := by
    have h1 : A⁻¹ *ᵥ (A *ᵥ WithLp.ofLp (xstar - x)) = WithLp.ofLp (xstar - x) := by
      rw [mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]
    have h2 : (A⁻¹ ⬝ (A ⬝ (xstar - x))) = xstar - x := congrArg (WithLp.toLp 2) h1
    rw [← hAd, h2]
  have henergy : E_A A xstar x ^ 2 = inner ℝ (A⁻¹ ⬝ (b - (A ⬝ x))) (b - (A ⬝ x)) := by
    rw [E_A_eq_energyNorm, hsc.energyNorm_sq, hAd, ← hd, RCLike.re_to_real,
      real_inner_comm (b - (A ⬝ x)) (xstar - x), hd]
  have hnorm : ‖b - (A ⬝ x)‖ ^ 4 = inner ℝ (b - (A ⬝ x)) (b - (A ⬝ x)) ^ 2 := by
    rw [real_inner_self_eq_norm_sq]
    ring
  have h := Projection.energyNorm_steepestDescentStep_sq_eq (A := toEuclideanLin A) (b := b)
    hsc hstar x
  rw [E_A_eq_energyNorm, sdStep_eq, h, ← E_A_eq_energyNorm, henergy, hnorm, RCLike.re_to_real]

omit [NeZero n] in
/-- Saad §5.3.2, "`A⁻¹` is also positive definite": the inverse of a positive real matrix is
positive real, since `(A⁻¹ u, u) = (A v, v)` at `v = A⁻¹ u`. -/
theorem isPositiveReal_inv (hA : A.IsPositiveReal) : A⁻¹.IsPositiveReal := by
  have hdet : IsUnit A.det := (isUnit_iff_isUnit_det A).mp (Chapter01.theorem_1_34 hA).1
  intro u hu
  have hv : A *ᵥ (A⁻¹ *ᵥ u) = u := by rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  have hne : A⁻¹ *ᵥ u ≠ 0 := fun hc => hu (by rw [← hv, hc, mulVec_zero])
  have h := hA (A⁻¹ *ᵥ u) hne
  rwa [hv, dotProduct_comm] at h

/-- **Saad (5.20)**: the alternative one-step bound of §5.3.2 for the minimal-residual iteration,
`‖r_{k+1}‖₂² ≤ (1 - μ(A) μ(A⁻¹)) ‖r_k‖₂²` with `μ(B) = λ_min((B + Bᵀ)/2)`.  It bounds the two
quotients of (5.18) separately: `(A r, r)/(r, r) ≥ μ(A)` is Theorem 1.34, and
`(A r, r)/(A r, A r) = (A⁻¹ w, w)/(w, w) ≥ μ(A⁻¹)` at `w = A r`, `A⁻¹` being positive real too
(`isPositiveReal_inv`). -/
theorem equation_5_20 (hA : A.IsPositiveReal) (b x : E n) :
    ‖b - (A ⬝ mrStep A b x)‖ ^ 2 ≤
      (1 - lambdaMin (Matrix.hermitianPart_isHermitian A) *
          lambdaMin (Matrix.hermitianPart_isHermitian A⁻¹)) * ‖b - (A ⬝ x)‖ ^ 2 := by
  rw [equation_5_18]
  rcases eq_or_ne (b - (A ⬝ x)) 0 with h0 | h0
  · rw [h0]
    simp
  set r : E n := b - (A ⬝ x) with hrdef
  set μ := lambdaMin (Matrix.hermitianPart_isHermitian A) with hμ
  set μ' := lambdaMin (Matrix.hermitianPart_isHermitian A⁻¹) with hμ'
  have hunit : IsUnit A := (Chapter01.theorem_1_34 hA).1
  have hdet : IsUnit A.det := (isUnit_iff_isUnit_det A).mp hunit
  have hAr : (A ⬝ r) ≠ 0 := fun hc => h0 (injective_toEuclideanLin hunit (by rw [hc, map_zero]))
  have hrn : (0 : ℝ) < ‖r‖ ^ 2 := by positivity
  have hArn : (0 : ℝ) < ‖A ⬝ r‖ ^ 2 := by positivity
  have hμpos : 0 < μ := lambdaMin_hermitianPart_pos hA
  have hμ'pos : 0 < μ' := lambdaMin_hermitianPart_pos (isPositiveReal_inv hA)
  have h1 : μ * ‖r‖ ^ 2 ≤ inner ℝ (A ⬝ r) r := by
    simpa [RCLike.re_to_real] using (Chapter01.isCoerciveWith_lambdaMin A) r
  have hinv : (A⁻¹ ⬝ (A ⬝ r)) = r := by
    have hrr : A⁻¹ *ᵥ (A *ᵥ WithLp.ofLp r) = WithLp.ofLp r := by
      rw [mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]
    exact congrArg (WithLp.toLp 2) hrr
  have h2 : μ' * ‖A ⬝ r‖ ^ 2 ≤ inner ℝ (A ⬝ r) r := by
    have hc := (Chapter01.isCoerciveWith_lambdaMin A⁻¹) (A ⬝ r)
    rw [hinv] at hc
    rw [← real_inner_comm (A ⬝ r) r]
    simpa [RCLike.re_to_real] using hc
  have hp1 : (0 : ℝ) < μ * ‖r‖ ^ 2 := by positivity
  have hp2 : (0 : ℝ) < μ' * ‖A ⬝ r‖ ^ 2 := by positivity
  have hq : μ * μ' ≤ inner ℝ (A ⬝ r) r ^ 2 / (‖r‖ ^ 2 * ‖A ⬝ r‖ ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    calc μ * μ' * (‖r‖ ^ 2 * ‖A ⬝ r‖ ^ 2) = (μ * ‖r‖ ^ 2) * (μ' * ‖A ⬝ r‖ ^ 2) := by ring
      _ ≤ inner ℝ (A ⬝ r) r * inner ℝ (A ⬝ r) r := mul_le_mul h1 h2 hp2.le (hp1.le.trans h1)
      _ = inner ℝ (A ⬝ r) r ^ 2 := by ring
  nlinarith [hq, hrn]

/-! ### §5.3.2: the convergence factor `ρ = max sin ∠(x, A x)` -/

/-- Saad §5.3.2: `ρ = sup_{x ≠ 0} sin ∠(x, A x)`, the convergence factor the book reads off the
geometric form `‖r_{k+1}‖₂ = ‖r_k‖₂ sin ∠(r_k, A r_k)` of (5.18).  The supremum runs over the
nonzero vectors, so it is `0` when there are none. -/
noncomputable def sinAngleSup (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ⨆ v : {v : E n // v ≠ 0}, Real.sin (InnerProductGeometry.angle (v : E n) (A ⬝ (v : E n)))

omit [NeZero n] in
/-- The sines of the angles are bounded by `1`, so `sinAngleSup` is a genuine supremum. -/
private theorem bddAbove_sinAngle (A : Matrix (Fin n) (Fin n) ℝ) :
    BddAbove (Set.range fun v : {v : E n // v ≠ 0} =>
      Real.sin (InnerProductGeometry.angle (v : E n) (A ⬝ (v : E n)))) := by
  refine ⟨1, ?_⟩
  rintro y ⟨i, rfl⟩
  exact Real.sin_le_one _

omit [NeZero n] in
/-- Every angle sine is bounded by `sinAngleSup`. -/
theorem sin_angle_le_sinAngleSup (A : Matrix (Fin n) (Fin n) ℝ) {v : E n} (hv : v ≠ 0) :
    Real.sin (InnerProductGeometry.angle v (A ⬝ v)) ≤ sinAngleSup A :=
  le_ciSup (bddAbove_sinAngle A) (⟨v, hv⟩ : {v : E n // v ≠ 0})

omit [NeZero n] in
/-- Saad §5.3.2: the reduction of one minimal-residual step is at most `ρ = sinAngleSup A`. -/
theorem norm_residual_mrStep_le_sinAngleSup (A : Matrix (Fin n) (Fin n) ℝ) (b x : E n) :
    ‖b - (A ⬝ mrStep A b x)‖ ≤ sinAngleSup A * ‖b - (A ⬝ x)‖ := by
  rcases eq_or_ne (b - (A ⬝ x)) 0 with h0 | h0
  · have hstep : mrStep A b x = x := by simp only [mrStep, step1, h0, smul_zero, add_zero]
    rw [hstep, h0]
    simp
  · rw [norm_residual_mrStep_eq_sin, mul_comm ‖b - (A ⬝ x)‖]
    exact mul_le_mul_of_nonneg_right (sin_angle_le_sinAngleSup A h0) (norm_nonneg _)

open scoped Matrix.Norms.L2Operator in
/-- Saad §5.3.2: for a positive real `A` the maximal angle between `x` and `A x` is acute, so
`ρ = sup_{x ≠ 0} sin ∠(x, A x) < 1`.  The uniform bound is Theorem 5.10: taking `b = x` and the
starting vector `0` makes `x` the residual, and `(5.15)` bounds its angle sine by
`√(1 - μ²/σ²) < 1`.  No compactness argument is needed. -/
theorem sinAngleSup_lt_one (hA : A.IsPositiveReal) : sinAngleSup A < 1 := by
  have hbound : ∀ v : {v : E n // v ≠ 0},
      Real.sin (InnerProductGeometry.angle (v : E n) (A ⬝ (v : E n)))
        ≤ Real.sqrt (1 - lambdaMin (Matrix.hermitianPart_isHermitian A) ^ 2 / ‖A‖ ^ 2) := by
    rintro ⟨v, hv⟩
    have h1 := norm_residual_mrStep_eq_sin A v 0
    have h2 := theorem_5_10_step hA v 0
    simp only [map_zero, sub_zero] at h1 h2
    rw [h1] at h2
    have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
    nlinarith [h2, hvpos]
  exact lt_of_le_of_lt (Real.iSup_le hbound (Real.sqrt_nonneg _)) (theorem_5_10_factor_lt_one hA)

/-- Saad §5.3.2: the minimal-residual iteration contracts the residual by the factor
`ρ = sup_{x ≠ 0} sin ∠(x, A x)`, and `ρ < 1` for a positive real `A`. -/
theorem norm_mrStep_le_sup_sin (hA : A.IsPositiveReal) (b x : E n) :
    ‖b - (A ⬝ mrStep A b x)‖ ≤ sinAngleSup A * ‖b - (A ⬝ x)‖ ∧ sinAngleSup A < 1 :=
  ⟨norm_residual_mrStep_le_sinAngleSup A b x, sinAngleSup_lt_one hA⟩

/-! ### Example 5.1: a Gauss–Seidel relaxation is a projection step -/

omit [NeZero n] in
/-- Saad's inner product against a coordinate vector reads off a component. -/
private theorem real_inner_single_left (i : Fin n) (z : E n) :
    inner ℝ (EuclideanSpace.single i (1 : ℝ) : E n) z = WithLp.ofLp z i := by
  rw [EuclideanSpace.inner_single_left]
  simp

omit [NeZero n] in
/-- The diagonal entry `a_{ii}` is `(A e_i, e_i)`. -/
private theorem real_inner_single_apply_single (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    inner ℝ (EuclideanSpace.single i (1 : ℝ) : E n) (A ⬝ (EuclideanSpace.single i (1 : ℝ) : E n))
      = A i i := by
  rw [real_inner_single_left, ofLp_toEuclideanLin]
  simp

omit [NeZero n] in
/-- **Example 5.1**: the projection step onto `K = L = span {e_i}` is the elementary relaxation
step `x ↦ x + (r_i/a_{ii}) e_i` of Saad (4.6), the inner step of the Gauss–Seidel sweep. -/
theorem example_5_1 (A : Matrix (Fin n) (Fin n) ℝ) (b x : E n) (i : Fin n) :
    step1 A b (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ)) x
      = x + (WithLp.ofLp (b - (A ⬝ x)) i / A i i) •
          (EuclideanSpace.single i (1 : ℝ) : E n) := by
  rw [step1, real_inner_single_left, real_inner_single_apply_single]

omit [NeZero n] in
/-- **Example 5.1**, the Petrov–Galerkin condition for `L = span {e_i}`: the elementary relaxation
step annihilates component `i` of the residual.  This is exactly what Saad (4.6) prescribes. -/
theorem example_5_1_residual (A : Matrix (Fin n) (Fin n) ℝ) (b x : E n) {i : Fin n}
    (hii : A i i ≠ 0) :
    WithLp.ofLp (b - (A ⬝ step1 A b (EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single i (1 : ℝ)) x)) i = 0 := by
  have hne : inner ℝ (EuclideanSpace.single i (1 : ℝ) : E n)
      (A ⬝ (EuclideanSpace.single i (1 : ℝ) : E n)) ≠ 0 := by
    rw [real_inner_single_apply_single]
    exact hii
  have h := (step1_isProjectionApprox (A := A) (b := b) (x := x) _ _ hne).2
    (EuclideanSpace.single i (1 : ℝ)) (Submodule.mem_span_singleton_self _)
  rwa [real_inner_single_left] at h

omit [NeZero n] in
/-- **Example 5.1**: the elementary relaxation step changes only component `i`. -/
theorem example_5_1_apply_of_ne (A : Matrix (Fin n) (Fin n) ℝ) (b x : E n) {i j : Fin n}
    (hij : j ≠ i) :
    WithLp.ofLp (step1 A b (EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single i (1 : ℝ)) x) j = WithLp.ofLp x j := by
  rw [example_5_1]
  simp [hij]

/-! ### The recursive residual of Algorithms 5.2–5.4

Each algorithm is printed with the residual *carried forward* rather than recomputed, so that a
step costs one matrix–vector product.  The state is the pair `(x, r)`, and the specifications
below say that the carried `r` really is `b - A x` at every step, so that each printed algorithm
computes the corresponding projection iterate. -/

/-- **Algorithm 5.2** (steepest descent) as printed: `p ← A r`, `α ← (r, r)/(p, r)`,
`x ← x + α r`, `r ← r - α p`. -/
noncomputable def sdAlgStep (A : Matrix (Fin n) (Fin n) ℝ) : (E n) × (E n) → (E n) × (E n)
  | (x, r) => (x + (inner ℝ r r / inner ℝ r (A ⬝ r)) • r,
      r - (inner ℝ r r / inner ℝ r (A ⬝ r)) • (A ⬝ r))

/-- **Algorithm 5.3** (minimal residual) as printed: `p ← A r`, `α ← (p, r)/(p, p)`,
`x ← x + α r`, `r ← r - α p`. -/
noncomputable def mrAlgStep (A : Matrix (Fin n) (Fin n) ℝ) : (E n) × (E n) → (E n) × (E n)
  | (x, r) => (x + (inner ℝ (A ⬝ r) r / inner ℝ (A ⬝ r) (A ⬝ r)) • r,
      r - (inner ℝ (A ⬝ r) r / inner ℝ (A ⬝ r) (A ⬝ r)) • (A ⬝ r))

/-- **Algorithm 5.4** (residual-norm steepest descent) as printed: `v ← Aᵀ r`, compute `A v`,
`α ← ‖v‖₂²/‖A v‖₂²` (5.21), `x ← x + α v`, `r ← r - α A v`. -/
noncomputable def rnsdAlgStep (A : Matrix (Fin n) (Fin n) ℝ) : (E n) × (E n) → (E n) × (E n)
  | (x, r) =>
      (x + (inner ℝ (A ⬝ (Aᵀ ⬝ r)) r / inner ℝ (A ⬝ (Aᵀ ⬝ r)) (A ⬝ (Aᵀ ⬝ r))) • (Aᵀ ⬝ r),
        r - (inner ℝ (A ⬝ (Aᵀ ⬝ r)) r / inner ℝ (A ⬝ (Aᵀ ⬝ r)) (A ⬝ (Aᵀ ⬝ r))) • (A ⬝ (Aᵀ ⬝ r)))

omit [NeZero n] in
/-- Saad (5.21): the step length of Algorithm 5.4 is `‖v‖₂²/‖A v‖₂²` with `v = Aᵀ r`, because
`(A v, r) = (v, v)`. -/
theorem rnsdAlgStep_alpha (A : Matrix (Fin n) (Fin n) ℝ) (r : E n) :
    inner ℝ (A ⬝ (Aᵀ ⬝ r)) r / inner ℝ (A ⬝ (Aᵀ ⬝ r)) (A ⬝ (Aᵀ ⬝ r))
      = ‖Aᵀ ⬝ r‖ ^ 2 / ‖A ⬝ (Aᵀ ⬝ r)‖ ^ 2 := by
  rw [real_inner_transpose A (Aᵀ ⬝ r) r, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

omit [NeZero n] in
/-- **Algorithm 5.2** computes the steepest-descent iterates, and the residual it carries is the
true residual at every step. -/
theorem sdAlg_spec (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : E n) (k : ℕ) :
    (sdAlgStep A)^[k] (x₀, b - (A ⬝ x₀))
      = ((sdStep A b)^[k] x₀, b - (A ⬝ ((sdStep A b)^[k] x₀))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    simp only [sdAlgStep, Prod.mk.injEq]
    refine ⟨rfl, ?_⟩
    simp only [sdStep, step1, map_add, map_smul]
    module

omit [NeZero n] in
/-- **Algorithm 5.3** computes the minimal-residual iterates, with the true residual carried. -/
theorem mrAlg_spec (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : E n) (k : ℕ) :
    (mrAlgStep A)^[k] (x₀, b - (A ⬝ x₀))
      = ((mrStep A b)^[k] x₀, b - (A ⬝ ((mrStep A b)^[k] x₀))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    simp only [mrAlgStep, Prod.mk.injEq]
    refine ⟨rfl, ?_⟩
    simp only [mrStep, step1, map_add, map_smul]
    module

omit [NeZero n] in
/-- **Algorithm 5.4** computes the residual-norm steepest-descent iterates, with the true
residual carried. -/
theorem rnsdAlg_spec (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : E n) (k : ℕ) :
    (rnsdAlgStep A)^[k] (x₀, b - (A ⬝ x₀))
      = ((rnsdStep A b)^[k] x₀, b - (A ⬝ ((rnsdStep A b)^[k] x₀))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    simp only [rnsdAlgStep, Prod.mk.injEq]
    refine ⟨rfl, ?_⟩
    simp only [rnsdStep, step1, map_add, map_smul]
    module

end SaadSparse.Chapter05

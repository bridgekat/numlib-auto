import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.LinearSolve.Projection.Basic
import Numlib.LinearSolve.Projection.OneDimensional
import NumlibSurface.SaadSparse.Chapter05.Section01

/-!
# §5.3 One-dimensional projection processes

Section 5.3 of Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
SIAM, 2003: the elementary step (5.12), steepest descent (Algorithm 5.2), Kantorovich's
inequality (Lemma 5.8) and Theorem 5.9, the minimal-residual iteration (Algorithm 5.3) and
Theorem 5.10, and the residual-norm steepest descent (Algorithm 5.4).

All three steps are the backbone's `Projection.step1` for `Matrix.toEuclideanLin A`
(`step1_eq`, `sdStep_eq`, `mrStep_eq` are `rfl`), so the convergence estimates specialize
`Numlib/LinearSolve/Projection/OneDimensional.lean`.

The exact one-step identities (5.16)–(5.18) and (5.20) specialize the backbone's
`Projection.norm_residual_minResStep_sq_eq` and `Projection.energyNorm_steepestDescentStep_sq_eq`,
and `norm_residual_mrStep_eq_sin` is the `sin ∠` reading of (5.18).

Left open here: the state-machine bookkeeping of Algorithms 5.2–5.4 (their recursive residual
updates).
-/

open Matrix Module Filter Topology
open scoped SaadSparse

namespace SaadSparse.Ch05

variable {n : ℕ}

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
theorem mrStep_min (hA : A.IsPositiveReal) (b x y : E n)
    (hy : y - x ∈ (ℝ ∙ (b - (A ⬝ x)))) : R_A A b (mrStep A b x) ≤ R_A A b y :=
  (Projection.minResStep_isMinRes x ((Matrix.isPositiveReal_iff_isCoercive A).mp hA)).min y hy

/-! ### Lemma 5.8 (Kantorovich) -/

variable [NeZero n]

/-- Saad, Lemma 5.8 (Kantorovich's inequality): for a real SPD `B`,
`(Bx, x)(B⁻¹x, x) ≤ (λ_max + λ_min)²/(4 λ_max λ_min) (x, x)²`. -/
theorem lemma_5_8 {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosDef) (x : Fin n → ℝ) :
    ((B *ᵥ x) ⬝ᵥ x) * ((B⁻¹ *ᵥ x) ⬝ᵥ x) ≤
      (lambdaMax hB.1 + lambdaMin hB.1) ^ 2 / (4 * lambdaMax hB.1 * lambdaMin hB.1) *
        (x ⬝ᵥ x) ^ 2 := by
  have hl : 0 < lambdaMin hB.1 := by
    rw [lambdaMin, Finset.lt_inf'_iff]
    exact fun i _ => Matrix.PosDef.eigenvalues_pos hB i
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
        E_A A xstar x := by
  have hl : 0 < lambdaMin hA.1 := by
    rw [lambdaMin, Finset.lt_inf'_iff]
    exact fun i _ => Matrix.PosDef.eigenvalues_pos hA i
  exact Projection.energyNorm_steepestDescentStep_le hl (isSymmetricBoundedBy_toEuclideanLin hA.1)
    hstar x

/-- The contraction factor of Theorem 5.9 lies in `[0, 1)`. -/
theorem theorem_5_9_factor_lt_one {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosDef) :
    0 ≤ (lambdaMax hH.1 - lambdaMin hH.1) / (lambdaMax hH.1 + lambdaMin hH.1) ∧
      (lambdaMax hH.1 - lambdaMin hH.1) / (lambdaMax hH.1 + lambdaMin hH.1) < 1 := by
  have hl : 0 < lambdaMin hH.1 := by
    rw [lambdaMin, Finset.lt_inf'_iff]
    exact fun i _ => Matrix.PosDef.eigenvalues_pos hH i
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
  have hl : 0 < lambdaMin hA.1 := by
    rw [lambdaMin, Finset.lt_inf'_iff]
    exact fun i _ => Matrix.PosDef.eigenvalues_pos hA i
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
    0 < lambdaMin (Matrix.hermitianPart_isHermitian A) := by
  have hpd := posDef_hermitianPart hA
  rw [lambdaMin, Finset.lt_inf'_iff]
  exact fun i _ => Matrix.PosDef.eigenvalues_pos hpd i

open scoped Matrix.Norms.L2Operator in
/-- Saad, Theorem 5.10: the minimal-residual step contracts the residual by the factor
`(1 - μ²/σ²)^{1/2}` with `μ = λ_min((A + Aᵀ)/2)` and `σ = ‖A‖₂`. -/
theorem theorem_5_10_step (hA : A.IsPositiveReal) (b x : E n) :
    ‖b - (A ⬝ mrStep A b x)‖ ≤
      Real.sqrt (1 - lambdaMin (Matrix.hermitianPart_isHermitian A) ^ 2 / ‖A‖ ^ 2) *
        ‖b - (A ⬝ x)‖ := by
  have hpos := lambdaMin_hermitianPart_pos hA
  have hcoer := Ch01.isCoerciveWith_lambdaMin A
  rw [Matrix.l2_opNorm_eq_norm_toEuclideanLin A]
  exact Projection.norm_residual_minResStep_le
    (A := LinearMap.toContinuousLinearMap (toEuclideanLin A)) hpos hcoer b x

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
/-- Saad (5.20): the exact one-step identity of steepest descent in the `A`-norm,
`‖d_{k+1}‖_A² = ‖d_k‖_A² (1 - (r_k, r_k)² / ((A r_k, r_k) (A⁻¹ r_k, r_k)))`, from which
Theorem 5.9 follows by Kantorovich's inequality (Lemma 5.8). -/
theorem equation_5_20 (hA : A.PosDef) {xstar : E n} (hstar : (A ⬝ xstar) = b) (x : E n) :
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

end SaadSparse.Ch05

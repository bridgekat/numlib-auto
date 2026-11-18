/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.LeastSquares.Regularized
import Numlib.Analysis.Matrix.OperatorNorm

/-!
# Tikhonov regularization

Section 3.3 of [benIsrael2003generalized] penalizes the squared norm of a least-squares
solution. The unique regularized minimizer decreases in norm as the penalty increases
and converges to the minimum-norm least-squares solution as the penalty tends to zero.
-/

namespace BenIsraelGreville.Chapter03

open Matrix Filter
open scoped Topology

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **Equation (37)** of [benIsrael2003generalized], Chapter 3. With penalty coefficient
$t=\alpha^2$, the Tikhonov objective is $\|Ax-b\|^2+t\|x\|^2$. -/
noncomputable def tikhonovObjective (A : Matrix m n ℂ) (b : EuclideanSpace ℂ m)
    (t : ℝ) (x : EuclideanSpace ℂ n) : ℝ :=
  ‖toEuclideanLin A x - b‖ ^ 2 + t * ‖x‖ ^ 2

variable [DecidableEq m]

/-- **Theorem 3** of [benIsrael2003generalized], Chapter 3. For each positive coefficient
$t$, the unique minimizer is $(A^H A+tI)^{-1}A^H b$. Its norm is antitone on $t>0$. -/
theorem theorem_3 (A : Matrix m n ℂ) (b : EuclideanSpace ℂ m) :
    (∀ t : ℝ, 0 < t → ∀ x : EuclideanSpace ℂ n,
      IsMinOn (tikhonovObjective A b t) Set.univ x ↔
        x = toEuclideanLin ((Aᴴ * A + (t : ℂ) • 1)⁻¹ * Aᴴ) b) ∧
    AntitoneOn (fun t : ℝ =>
      ‖toEuclideanLin ((Aᴴ * A + (t : ℂ) • 1)⁻¹ * Aᴴ) b‖) (Set.Ioi 0) := by
  have horder (t : ℝ) : A.tikhonov t = (Aᴴ * A + (t : ℂ) • 1)⁻¹ * Aᴴ := by
    exact congrArg (fun M : Matrix n n ℂ => M⁻¹ * Aᴴ)
      (add_comm ((t : ℂ) • (1 : Matrix n n ℂ)) (Aᴴ * A))
  constructor
  · intro t ht x
    rw [← horder]
    exact (Matrix.eq_toEuclideanLin_tikhonov_iff_isMinOn A ht b x).symm
  · simpa only [horder] using
      Matrix.antitoneOn_norm_toEuclideanLin_tikhonov A b

/-- **Exercise 25** of [benIsrael2003generalized], Chapter 3. As the positive coefficient
$t=\alpha^2$ tends to zero, the regularized solution converges to $A^\dagger b$. -/
theorem tendsto_tikhonov (A : Matrix m n ℂ) (b : EuclideanSpace ℂ m) :
    Tendsto (fun t : ℝ => toEuclideanLin (A.tikhonov t) b) (𝓝[>] 0)
      (𝓝 (toEuclideanLin A.pinv b)) := by
  let eval : Matrix n m ℂ →ₗ[ℂ] EuclideanSpace ℂ n :=
    ((LinearMap.applyₗ (R := ℂ) (M₂ := EuclideanSpace ℂ n)) b).comp toEuclideanLin.toLinearMap
  have hEval : Continuous eval := eval.continuous_of_finiteDimensional
  exact hEval.continuousAt.tendsto.comp A.tendsto_tikhonov_pinv

section ComplexShift

omit [DecidableEq m] in
private theorem complexShiftedGram_eq_diagonal (A : Matrix m n ℂ) (zeta : ℂ) :
    zeta • 1 + Aᴴ * A = A.rightSingularUnitary *
      diagonal (fun i => zeta + ((A.colSingularValues i ^ 2 : ℝ) : ℂ)) *
        star A.rightSingularUnitary := by
  have hc : (diagonal fun _ : n => zeta) = zeta • (1 : Matrix n n ℂ) := by
    ext i j
    by_cases h : i = j <;> simp [h, diagonal_apply_eq]
  have hI : zeta • (1 : Matrix n n ℂ) =
      A.rightSingularUnitary * diagonal (fun _ : n => zeta) * star A.rightSingularUnitary := by
    rw [hc, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, A.rightSingularUnitary_mul_star]
  rw [hI, A.conjTranspose_mul_self_eq_conj_diagonal, ← Matrix.add_mul, ← Matrix.mul_add, diagonal_add]
  rfl

omit [DecidableEq m] in
private theorem complexShiftedGram_inv (A : Matrix m n ℂ) (zeta : ℂ)
    (hzeta : ∀ i, zeta + ((A.colSingularValues i ^ 2 : ℝ) : ℂ) ≠ 0) :
    (zeta • 1 + Aᴴ * A)⁻¹ = A.rightSingularUnitary *
      diagonal (fun i => (zeta + ((A.colSingularValues i ^ 2 : ℝ) : ℂ))⁻¹) *
        star A.rightSingularUnitary := by
  apply inv_eq_right_inv
  rw [complexShiftedGram_eq_diagonal, A.conj_diagonal_mul_conj_diagonal]
  have he : (fun i => (zeta + ((A.colSingularValues i ^ 2 : ℝ) : ℂ)) *
      (zeta + ((A.colSingularValues i ^ 2 : ℝ) : ℂ))⁻¹) = fun _ : n => (1 : ℂ) :=
    funext fun i => mul_inv_cancel₀ (hzeta i)
  rw [he, diagonal_one, Matrix.mul_one, A.rightSingularUnitary_mul_star]

omit [DecidableEq m] in
private theorem complexShiftedGram_pinv_error (A : Matrix m n ℂ) (zeta : ℂ)
    (hzeta : ∀ i, zeta + ((A.colSingularValues i ^ 2 : ℝ) : ℂ) ≠ 0) :
    (zeta • 1 + Aᴴ * A)⁻¹ * Aᴴ =
      A.pinv - A.rightSingularUnitary *
        diagonal (fun i => zeta * ((zeta + ((A.colSingularValues i ^ 2 : ℝ) : ℂ))⁻¹ *
          (((A.colSingularValues i ^ 2 : ℝ) : ℂ))⁻¹)) *
        star A.rightSingularUnitary * Aᴴ := by
  let M := zeta • (1 : Matrix n n ℂ) + Aᴴ * A
  let Q := A.rightSingularUnitary
  have hM : IsUnit M := by
    dsimp only [M]
    rw [complexShiftedGram_eq_diagonal]
    have hQ : IsUnit Q := isUnit_of_mem_unitaryGroup A.rightSingularUnitary_mem_unitaryGroup
    have hD : IsUnit (diagonal (fun i => zeta + ((A.colSingularValues i ^ 2 : ℝ) : ℂ))) := by
      rw [isUnit_diagonal, Pi.isUnit_iff]
      exact fun i => isUnit_iff_ne_zero.mpr (hzeta i)
    exact (hQ.mul hD).mul hQ.star
  have hAH : Aᴴ * A * A.pinv = Aᴴ := by rw [Matrix.mul_assoc, conjTranspose_mul_mul_pinv]
  have hEq : M * A.pinv = Aᴴ + zeta • A.pinv := by
    dsimp only [M]
    rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, hAH, add_comm]
  have he : M⁻¹ * Aᴴ = A.pinv - zeta • (M⁻¹ * A.pinv) := by
    apply eq_sub_iff_add_eq.mpr
    rw [← Matrix.mul_smul, ← Matrix.mul_add, ← hEq,
      ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hM), Matrix.one_mul]
  rw [he]
  congr 1
  rw [show M⁻¹ = Q *
      diagonal (fun i => (zeta + ((A.colSingularValues i ^ 2 : ℝ) : ℂ))⁻¹) * star Q from
      complexShiftedGram_inv A zeta hzeta, pinv_def, gramPinv_def,
    ← Matrix.mul_assoc _ _ Aᴴ, A.conj_diagonal_mul_conj_diagonal]
  rw [← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.mul_smul, ← diagonal_smul]
  rfl

/-- **Exercise 25** of [benIsrael2003generalized], Chapter 3.
The resolvent formula converges along arbitrary nonzero complex shifts. -/
theorem exercise_3_25_complex (A : Matrix m n ℂ) :
    Tendsto (fun zeta : ℂ => (Aᴴ * A + zeta • 1)⁻¹ * Aᴴ) (𝓝[≠] 0) (𝓝 A.pinv) := by
  let s (i : n) : ℂ := ((A.colSingularValues i ^ 2 : ℝ) : ℂ)
  let q (zeta : ℂ) (i : n) : ℂ := zeta * ((zeta + s i)⁻¹ * (s i)⁻¹)
  have hq : Tendsto q (𝓝[≠] 0) (𝓝 0) := by
    rw [tendsto_pi_nhds]
    intro i
    by_cases hi : s i = 0
    · have he : (fun zeta : ℂ => q zeta i) = fun _ => 0 := by
        funext zeta
        simp [q, hi]
      rw [he]
      exact tendsto_const_nhds
    · have hne : (0 : ℂ) + s i ≠ 0 := by rwa [zero_add]
      have hc : ContinuousAt (fun zeta : ℂ => zeta * ((zeta + s i)⁻¹ * (s i)⁻¹)) 0 :=
        continuousAt_id.mul (((continuousAt_id.add continuousAt_const).inv₀ hne).mul
          continuousAt_const)
      simpa [q] using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  have hc : Continuous fun d : n → ℂ => A.pinv - A.rightSingularUnitary *
      diagonal d * star A.rightSingularUnitary * Aᴴ :=
    continuous_const.sub (((continuous_const.matrix_mul continuous_id.matrix_diagonal).matrix_mul
      continuous_const).matrix_mul continuous_const)
  have hlim := (hc.tendsto 0).comp hq
  have h0 : A.pinv - A.rightSingularUnitary * diagonal (0 : n → ℂ) *
      star A.rightSingularUnitary * Aᴴ = A.pinv := by simp
  rw [h0] at hlim
  have hevent : ∀ᶠ zeta : ℂ in 𝓝[≠] 0, ∀ i, zeta + s i ≠ 0 := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : s i = 0
    · filter_upwards [self_mem_nhdsWithin] with zeta hzeta
      simpa only [hi, add_zero, Set.mem_compl_iff, Set.mem_singleton_iff] using hzeta
    · have hcont : ContinuousAt (fun zeta : ℂ => zeta + s i) 0 := continuousAt_id.add continuousAt_const
      have hne : {z : ℂ | z ≠ 0} ∈ 𝓝 ((0 : ℂ) + s i) :=
        isOpen_ne.mem_nhds (by change (0 : ℂ) + s i ≠ 0; rwa [zero_add])
      exact (hcont.tendsto.eventually hne).filter_mono nhdsWithin_le_nhds
  apply hlim.congr'
  filter_upwards [hevent] with zeta hzeta
  simpa only [Function.comp_apply, add_comm (Aᴴ * A)] using
    (complexShiftedGram_pinv_error A zeta hzeta).symm

/-- **Exercise 26** of [benIsrael2003generalized], Chapter 3.
The regularized Gram operator converges to the identity on the range of
the adjoint, including for nonreal complex shifts. -/
theorem exercise_3_26 (A : Matrix m n ℂ) (x : EuclideanSpace ℂ n)
    (hx : x ∈ LinearMap.range (toEuclideanLin Aᴴ)) :
    Tendsto (fun zeta : ℂ => toEuclideanLin ((Aᴴ * A + zeta • 1)⁻¹ * (Aᴴ * A)) x)
      (𝓝[≠] 0) (𝓝 x) := by
  let Eval : Matrix n m ℂ →ₗ[ℂ] EuclideanSpace ℂ n :=
    ((LinearMap.applyₗ (R := ℂ) (M₂ := EuclideanSpace ℂ n)) (toEuclideanLin A x)).comp
      toEuclideanLin.toLinearMap
  have hEval : Continuous Eval := Eval.continuous_of_finiteDimensional
  have hp : Eval A.pinv = x := by
    change toEuclideanLin A.pinv (toEuclideanLin A x) = x
    rw [← toEuclideanLin_mul_apply, A.pinv_mul_eq_starProjection]
    exact Submodule.starProjection_eq_self_iff.mpr hx
  have h := hEval.continuousAt.tendsto.comp (exercise_3_25_complex A)
  rw [hp] at h
  change Tendsto
    (fun zeta : ℂ => toEuclideanLin ((Aᴴ * A + zeta • 1)⁻¹ * Aᴴ) (toEuclideanLin A x))
    (𝓝[≠] 0) (𝓝 x) at h
  simpa only [← toEuclideanLin_mul_apply, Matrix.mul_assoc] using h

section SpectralError

open scoped Matrix.Norms.L2Operator

private theorem norm_shiftedGramInv_mul_gram_le_one (A : Matrix m n ℂ) (t : ℝ) (ht : 0 < t) :
    ‖((t : ℂ) • 1 + Aᴴ * A)⁻¹ * (Aᴴ * A)‖ ≤ 1 := by
  have hV := A.rightSingularUnitary_mem_unitaryGroup
  have ht' (i : n) : (t : ℂ) + ((A.colSingularValues i ^ 2 : ℝ) : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_add, Complex.ofReal_ne_zero]
    positivity
  rw [complexShiftedGram_inv A (t : ℂ) ht',
    A.conjTranspose_mul_self_eq_conj_diagonal, A.conj_diagonal_mul_conj_diagonal,
    l2_opNorm_unitary_mul_mul_unitary hV _ (Unitary.star_mem hV), l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  let s := A.colSingularValues i ^ 2
  have hs : 0 ≤ s := sq_nonneg _
  have hts : 0 < t + s := add_pos_of_pos_of_nonneg ht hs
  change ‖((t : ℂ) + (s : ℂ))⁻¹ * (s : ℂ)‖ ≤ 1
  rw [← Complex.ofReal_add]
  rw [norm_mul, norm_inv, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos hts, abs_of_nonneg hs, inv_mul_eq_div]
  exact (div_le_one hts).mpr (le_add_of_nonneg_left ht.le)

/-- **Exercise 27**, Equation (46), of [benIsrael2003generalized], Chapter 3.
The regularization error in the spectral norm is at most the shift times
the cube of the reciprocal's spectral norm. -/
theorem exercise_3_27 (A : Matrix m n ℂ) (t : ℝ) (ht : 0 < t) :
    ‖A.pinv - A.tikhonov t‖ ≤ t * ‖A.pinv‖ ^ 3 := by
  let G := Aᴴ * A
  let M : Matrix n n ℂ := (t : ℂ) • 1 + G
  let P := A.pinv
  have hGp : G * P = Aᴴ := by
    dsimp only [G, P]
    rw [Matrix.mul_assoc, A.conjTranspose_mul_mul_pinv]
  have hPH : Aᴴ * Pᴴ = P * A := by
    rw [← conjTranspose_mul, A.isHermitian_pinv_mul.eq]
  have hG : G * (P * Pᴴ * P) = P := calc
    _ = (G * P) * Pᴴ * P := by simp only [Matrix.mul_assoc]
    _ = P := by rw [hGp, hPH, A.pinv_mul_self_mul_pinv]
  have h1 : ‖M⁻¹ * G‖ ≤ 1 := norm_shiftedGramInv_mul_gram_le_one A t ht
  have h3 : ‖P * Pᴴ * P‖ ≤ ‖P‖ ^ 3 := calc
    _ ≤ ‖P * Pᴴ‖ * ‖P‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖P‖ * ‖Pᴴ‖) * ‖P‖ :=
      mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ = _ := by rw [l2_opNorm_conjTranspose]; ring
  have htotal : ‖M⁻¹ * P‖ ≤ ‖P‖ ^ 3 := calc
    _ = ‖(M⁻¹ * G) * (P * Pᴴ * P)‖ := by rw [Matrix.mul_assoc, hG]
    _ ≤ ‖M⁻¹ * G‖ * ‖P * Pᴴ * P‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ ‖P‖ ^ 3 := by
      simpa only [one_mul] using mul_le_mul h1 h3 (norm_nonneg _) zero_le_one
  rw [A.tikhonov_eq_pinv_sub t ht, sub_sub_cancel, norm_smul, RCLike.norm_ofReal,
    abs_of_pos ht]
  exact mul_le_mul_of_nonneg_left htotal ht.le

end SpectralError

end ComplexShift

section Radius

open Filter Set
open scoped Topology

/-- **Exercise 28** of [benIsrael2003generalized], Chapter 3.
The minimizers at nonzero penalty parameters tend to the least-norm
least-squares solution as the parameter tends to zero. -/
theorem exercise_3_28 (A : Matrix m n ℂ) (b : EuclideanSpace ℂ m) :
    (∀ α : ℝ, α ≠ 0 → ∀ x : EuclideanSpace ℂ n,
      IsMinOn (tikhonovObjective A b (α ^ 2)) univ x ↔
        x = toEuclideanLin (A.tikhonov (α ^ 2)) b) ∧
    Tendsto (fun α : ℝ => toEuclideanLin (A.tikhonov (α ^ 2)) b) (𝓝[≠] 0)
      (𝓝 (toEuclideanLin A.pinv b)) := by
  constructor
  · intro α hα x
    exact (Matrix.eq_toEuclideanLin_tikhonov_iff_isMinOn A (sq_pos_of_ne_zero hα) b x).symm
  · have hpos : Tendsto (fun α : ℝ => α ^ 2) (𝓝[≠] 0) (𝓝[>] 0) := by
      rw [tendsto_nhdsWithin_iff]
      have hc : Continuous (fun α : ℝ => α ^ 2) := continuous_id.pow 2
      have hz : Tendsto (fun α : ℝ => α ^ 2) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
        simpa using hc.continuousAt (x := (0 : ℝ)).tendsto
      exact ⟨hz.mono_left nhdsWithin_le_nhds,
        eventually_of_mem self_mem_nhdsWithin (fun x hx => sq_pos_of_ne_zero hx)⟩
    exact (tendsto_tikhonov A b).comp hpos

/-- A minimizer of the residual over the closed norm ball of radius p. -/
def IsBallLeastSquaresSolution (A : Matrix m n ℂ) (b : EuclideanSpace ℂ m) (p : ℝ)
    (x : EuclideanSpace ℂ n) : Prop :=
  ‖x‖ ≤ p ∧ ∀ y, ‖y‖ ≤ p → ‖toEuclideanLin A x - b‖ ≤ ‖toEuclideanLin A y - b‖

private theorem unique_ball_min_of_tikhonov_norm (A : Matrix m n ℂ) (b : EuclideanSpace ℂ m)
    {t p : ℝ} (ht : 0 < t) (hp : ‖toEuclideanLin (A.tikhonov t) b‖ = p) :
    ∀ y, IsBallLeastSquaresSolution A b p y ↔ y = toEuclideanLin (A.tikhonov t) b := by
  let x := toEuclideanLin (A.tikhonov t) b
  have hx : IsMinOn (tikhonovObjective A b t) univ x :=
    (Matrix.eq_toEuclideanLin_tikhonov_iff_isMinOn A ht b x).mp rfl
  have hmin (y : EuclideanSpace ℂ n) (hy : ‖y‖ ≤ p) :
      ‖toEuclideanLin A x - b‖ ≤ ‖toEuclideanLin A y - b‖ := by
    have he := hx (mem_univ y)
    have hn : ‖y‖ ^ 2 ≤ ‖x‖ ^ 2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hp ▸ hy)
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖toEuclideanLin A x - b‖ ^ 2 + t * ‖x‖ ^ 2 ≤
      ‖toEuclideanLin A y - b‖ ^ 2 + t * ‖y‖ ^ 2 at he
    linarith [mul_le_mul_of_nonneg_left hn ht.le]
  intro y
  constructor
  · intro hy
    have he := hy.2 x hp.le
    have hres := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr he
    have hn := (sq_le_sq₀ (norm_nonneg y) (norm_nonneg x)).mpr (hp ▸ hy.1)
    have hObj : tikhonovObjective A b t y ≤ tikhonovObjective A b t x :=
      add_le_add hres (mul_le_mul_of_nonneg_left hn ht.le)
    apply (Matrix.eq_toEuclideanLin_tikhonov_iff_isMinOn A ht b y).mpr
    intro z hz
    exact hObj.trans (hx hz)
  · rintro rfl
    exact ⟨hp.le, hmin⟩

private theorem existsUnique_tikhonov_parameter (A : Matrix m n ℂ) (b : EuclideanSpace ℂ m)
    {p : ℝ} (hp : 0 < p) (hlt : p < ‖toEuclideanLin A.pinv b‖) :
    ∃! t : ℝ, 0 < t ∧ ‖toEuclideanLin (A.tikhonov t) b‖ = p := by
  have hb : toEuclideanLin A.pinv b ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlt
    exact (lt_asymm hp) hlt
  have hb' : toEuclideanLin Aᴴ b ≠ 0 := by
    intro h
    apply hb
    rw [pinv_def, toEuclideanLin_mul_apply, h, map_zero]
  exact existsUnique_pos_eq_of_strictAntiOn_Ioi
    (A.strictAntiOn_norm_toEuclideanLin_tikhonov hb') (A.continuousOn_norm_toEuclideanLin_tikhonov b)
    (tendsto_tikhonov A b).norm (A.tendsto_norm_toEuclideanLin_tikhonov_atTop b) hp hlt

/-- **Exercise 29** of [benIsrael2003generalized], Chapter 3.
For radii below the norm of the least-norm least-squares solution, the
unique positive penalty produces the unique minimizer on the sphere.
The threshold is the norm of the least-norm solution in (41). -/
theorem exercise_3_29 (A : Matrix m n ℂ) (b : EuclideanSpace ℂ m)
    {p : ℝ} (hp : 0 < p) (hlt : p < ‖toEuclideanLin A.pinv b‖) :
    (∃! t : ℝ, 0 < t ∧ ‖toEuclideanLin (A.tikhonov t) b‖ = p) ∧
    ∀ t : ℝ, 0 < t → ‖toEuclideanLin (A.tikhonov t) b‖ = p →
      ∀ x : EuclideanSpace ℂ n,
        (‖x‖ = p ∧ ∀ y : EuclideanSpace ℂ n, ‖y‖ = p →
          ‖toEuclideanLin A x - b‖ ≤ ‖toEuclideanLin A y - b‖) ↔
            x = toEuclideanLin (A.tikhonov t) b := by
  refine ⟨existsUnique_tikhonov_parameter A b hp hlt, ?_⟩
  intro t ht hnorm x
  let z := toEuclideanLin (A.tikhonov t) b
  have hb := unique_ball_min_of_tikhonov_norm A b ht hnorm
  have hz := (hb z).mpr rfl
  constructor
  · intro h
    apply (hb x).mp
    exact ⟨h.1.le, fun y hy => (h.2 z hnorm).trans (hz.2 y hy)⟩
  · rintro rfl
    exact ⟨hnorm, fun y hy => hz.2 y hy.le⟩

/-- In the inactive case of **Exercise 30**, the ball minimizers are the
ordinary least-squares solutions that satisfy the norm bound. -/
theorem exercise_3_30_inactive (A : Matrix m n ℂ) (b : EuclideanSpace ℂ m)
    {p : ℝ} (hp : ‖toEuclideanLin A.pinv b‖ ≤ p) (x : EuclideanSpace ℂ n) :
    IsBallLeastSquaresSolution A b p x ↔ ‖x‖ ≤ p ∧ IsLeastSquaresSolution A b x := by
  apply and_congr_right
  intro hx
  constructor
  · intro h y
    exact (h _ hp).trans (isLeastSquaresSolution_pinv A b y)
  · intro h y _
    exact h y

/-- In the inactive case of **Exercise 30**, uniqueness holds at the
boundary radius or when the matrix has a trivial kernel. -/
theorem exercise_3_30_inactive_unique (A : Matrix m n ℂ) (b : EuclideanSpace ℂ m)
    {p : ℝ} (hp : ‖toEuclideanLin A.pinv b‖ ≤ p) :
    (∃! x, IsBallLeastSquaresSolution A b p x) ↔
      ‖toEuclideanLin A.pinv b‖ = p ∨ (toEuclideanLin A).ker = ⊥ := by
  let z := toEuclideanLin A.pinv b
  have hz : IsBallLeastSquaresSolution A b p z :=
    (exercise_3_30_inactive A b hp z).mpr ⟨hp, isLeastSquaresSolution_pinv A b⟩
  constructor
  · intro hu
    by_contra hn
    have hne : ‖z‖ ≠ p := fun h => hn (Or.inl h)
    have hk : (toEuclideanLin A).ker ≠ ⊥ := fun h => hn (Or.inr h)
    obtain ⟨u, huK, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
    let a := (p - ‖z‖) / ‖u‖
    have ha : 0 < a := div_pos (sub_pos.mpr (lt_of_le_of_ne hp hne)) (norm_pos_iff.mpr hu0)
    have huA : toEuclideanLin A u = 0 := huK
    have hx : IsBallLeastSquaresSolution A b p (z + (a : ℂ) • u) := by
      apply (exercise_3_30_inactive A b hp _).mpr
      refine ⟨?_, ?_⟩
      · have he : ‖(a : ℂ) • u‖ = p - ‖z‖ := by
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
          exact div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hu0)
        exact (norm_add_le _ _).trans (by rw [he]; linarith)
      · intro y
        rw [map_add, map_smul, huA, smul_zero, add_zero]
        exact isLeastSquaresSolution_pinv A b y
    have he := hu.unique hx hz
    have hz' : (a : ℂ) • u = 0 := add_left_cancel (he.trans (add_zero z).symm)
    exact (smul_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne') hu0) hz'
  · intro h
    refine ⟨z, hz, fun x hx => ?_⟩
    have hls := (exercise_3_30_inactive A b hp x).mp hx
    rcases h with hbound | hker
    · change ‖z‖ = p at hbound
      have hxnorm : ‖x‖ ≤ ‖z‖ := by rw [hbound]; exact hx.1
      exact (show IsMinNormLeastSquaresSolution A b x from
        ⟨hls.2, fun y hy => hxnorm.trans ((isMinNormLeastSquaresSolution_pinv A b).2 y hy)⟩).eq_pinv
    · have hm : x - z ∈ (toEuclideanLin A).ker :=
        toEuclideanLin_sub_pinv_eq_zero_of_normalEquations
          (isLeastSquaresSolution_iff_normalEquations.mp hls.2)
      rw [hker, Submodule.mem_bot] at hm
      exact sub_eq_zero.mp hm

/-- In the active case of **Exercise 30**, the unique positive penalty
gives the unique minimizer over the closed ball. -/
theorem exercise_3_30_active (A : Matrix m n ℂ) (b : EuclideanSpace ℂ m)
    {p : ℝ} (hp : 0 < p) (hlt : p < ‖toEuclideanLin A.pinv b‖) :
    (∃! t : ℝ, 0 < t ∧ ‖toEuclideanLin (A.tikhonov t) b‖ = p) ∧
    ∀ t : ℝ, 0 < t → ‖toEuclideanLin (A.tikhonov t) b‖ = p →
      ∀ x, IsBallLeastSquaresSolution A b p x ↔ x = toEuclideanLin (A.tikhonov t) b :=
  ⟨existsUnique_tikhonov_parameter A b hp hlt,
    fun _ ht hnorm => unique_ball_min_of_tikhonov_norm A b ht hnorm⟩

end Radius

end BenIsraelGreville.Chapter03

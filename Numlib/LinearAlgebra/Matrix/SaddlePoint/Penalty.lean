import Numlib.LinearAlgebra.Matrix.SaddlePoint
import Numlib.LinearAlgebra.Matrix.SaddlePoint.BlockSolve
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Numlib.Optimization.Optimality.Unconstrained

/-!
# Quadratic penalty and augmented saddle-point systems

For $Ax+B^Ty=f$, $Bx=g$, a penalty of size $\gamma$ replaces the primal block by
$A+\gamma B^TB$. The reduced penalty equations are equivalent to the original block equations
with the lower-right block replaced by $-\gamma^{-1} I$.

## Main results

* Matrix.posDef_saddleAugmentedPrimal: the augmented primal block is positive definite
  when $A$ is positive semidefinite and the common kernel is trivial.
* Matrix.saddlePenalty_equations_iff: the reduced and regularized systems agree.
* Matrix.isLeast_saddleAugmentedLagrangian_iff: minimizing the augmented Lagrangian
  in the primal variable is equivalent to the augmented linear solve.
-/

set_option autoImplicit false

namespace Matrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- Adding a quadratic penalty of size $\gamma$ gives the primal matrix $A+\gamma B^TB$. -/
def saddleAugmentedPrimal (A : Matrix n n ℝ) (B : Matrix m n ℝ) (γ : ℝ) : Matrix n n ℝ :=
  A + γ • (Bᵀ * B)

/-- Augmenting the primal row of the saddle equations gives right-hand side $f+\gamma B^Tg$. -/
def saddleAugmentedRhs (B : Matrix m n ℝ) (γ : ℝ) (f : n → ℝ) (g : m → ℝ) : n → ℝ :=
  f + γ • (Bᵀ *ᵥ g)

omit [DecidableEq n] [DecidableEq m] in
/-- If $A$ is positive semidefinite, $\ker A\cap\ker B=\{0\}$, and $\gamma>0$, then
$A+\gamma B^TB$ is positive definite. -/
theorem posDef_saddleAugmentedPrimal {A : Matrix n n ℝ} (B : Matrix m n ℝ)
    (hA : A.PosSemidef) (hker : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥)
    {γ : ℝ} (hγ : 0 < γ) : (saddleAugmentedPrimal A B γ).PosDef :=
  posDef_add_scaled_gram_of_ker_inf_eq_bot hA hker hγ

omit [DecidableEq m] in
/-- For positive semidefinite $A$ and nonsingular $P=A+\gamma B^TB$, a positive real
eigenvalue $\lambda$ of $BP^{-1}B^T$ satisfies $\gamma\lambda\le1$. -/
theorem mul_le_one_of_saddleAugmentedSchur_eigenvector {A : Matrix n n ℝ}
    (B : Matrix m n ℝ) (hA : A.PosSemidef) (γ : ℝ)
    (hP : IsUnit (saddleAugmentedPrimal A B γ))
    {lam : ℝ} (hlam : 0 < lam) {v : m → ℝ} (hv : v ≠ 0)
    (he : (B * (saddleAugmentedPrimal A B γ)⁻¹ * Bᵀ) *ᵥ v = lam • v) :
    γ * lam ≤ 1 := by
  let P := saddleAugmentedPrimal A B γ
  let w := P⁻¹ *ᵥ (Bᵀ *ᵥ v)
  have hPw : P *ᵥ w = Bᵀ *ᵥ v := by
    dsimp [w]
    rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det P).mp hP), one_mulVec]
  have hBw : B *ᵥ w = lam • v := by
    simpa only [w, mulVec_mulVec, Matrix.mul_assoc, P] using he
  have hq : w ⬝ᵥ (P *ᵥ w) = w ⬝ᵥ (A *ᵥ w) + γ * ((B *ᵥ w) ⬝ᵥ (B *ᵥ w)) := by
    dsimp only [P, saddleAugmentedPrimal]
    rw [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, ← mulVec_mulVec,
      dotProduct_transpose_mulVec]
    rfl
  have hlin : w ⬝ᵥ (P *ᵥ w) = lam * (v ⬝ᵥ v) := by
    rw [hPw, dotProduct_transpose_mulVec, hBw, dotProduct_smul]
    rfl
  have hsq : (B *ᵥ w) ⬝ᵥ (B *ᵥ w) = lam ^ 2 * (v ⬝ᵥ v) := by
    rw [hBw, smul_dotProduct, dotProduct_smul]
    change lam * (lam * (v ⬝ᵥ v)) = _
    ring
  have hAq : 0 ≤ w ⬝ᵥ (A *ᵥ w) := by simpa using hA.dotProduct_mulVec_nonneg w
  have hdot : 0 < v ⬝ᵥ v := lt_of_le_of_ne
    (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
    (fun hz => hv (dotProduct_self_eq_zero.mp hz.symm))
  have hb : (lam * (v ⬝ᵥ v)) * (γ * lam) ≤ (lam * (v ⬝ᵥ v)) * 1 := by
    rw [hlin, hsq] at hq
    nlinarith only [hq, hAq]
  exact (mul_le_mul_iff_right₀ (mul_pos hlam hdot)).mp hb

omit [DecidableEq n] [DecidableEq m] in
/-- If $Bx=g$, adding $\gamma B^T$ times the constraint to the primal equation preserves it.
Thus the original and augmented saddle equations are equivalent. -/
theorem saddleAugmented_equations_iff (A : Matrix n n ℝ) (B : Matrix m n ℝ) (γ : ℝ)
    (f x : n → ℝ) (g y : m → ℝ) :
    ((saddleAugmentedPrimal A B γ) *ᵥ x + Bᵀ *ᵥ y = saddleAugmentedRhs B γ f g ∧
      B *ᵥ x = g) ↔ (A *ᵥ x + Bᵀ *ᵥ y = f ∧ B *ᵥ x = g) := by
  simpa only [saddleAugmentedPrimal, saddleAugmentedRhs, Matrix.smul_mul, smul_mulVec] using
    saddleEquations_augment_iff B (γ • Bᵀ) x y f g (A := A)

/-- The multiplier associated with a penalized primal vector $x$ is $\gamma(Bx-g)$. -/
def saddlePenaltyMultiplier (B : Matrix m n ℝ) (γ : ℝ) (g : m → ℝ) (x : n → ℝ) : m → ℝ :=
  γ • (B *ᵥ x - g)

omit [DecidableEq n] [DecidableEq m] in
/-- For nonzero $\gamma$, the penalty equation and the formula for the penalty multiplier
are equivalent to $Ax+B^Ty=f$, $Bx-\gamma^{-1}y=g$. -/
theorem saddlePenalty_equations_iff (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    {γ : ℝ} (hγ : γ ≠ 0) (f x : n → ℝ) (g y : m → ℝ) :
    ((saddleAugmentedPrimal A B γ) *ᵥ x = saddleAugmentedRhs B γ f g ∧
      y = saddlePenaltyMultiplier B γ g x) ↔
      (A *ᵥ x + Bᵀ *ᵥ y = f ∧ B *ᵥ x - γ⁻¹ • y = g) := by
  have hmul : y = saddlePenaltyMultiplier B γ g x ↔ B *ᵥ x - γ⁻¹ • y = g := by
    unfold saddlePenaltyMultiplier
    rw [sub_eq_iff_eq_add, add_comm g, ← sub_eq_iff_eq_add (a := B *ᵥ x) (b := g)]
    constructor
    · intro hy
      rw [hy, smul_smul, inv_mul_cancel₀ hγ, one_smul]
    · intro hy
      rw [hy, smul_smul, mul_inv_cancel₀ hγ, one_smul]
  rw [← hmul]
  refine and_congr_left fun hy => ?_
  rw [hy]
  simp only [saddleAugmentedPrimal, saddleAugmentedRhs, saddlePenaltyMultiplier, add_mulVec,
    smul_mulVec, ← mulVec_mulVec, mulVec_smul, mulVec_sub, smul_sub]
  rw [← add_sub_assoc, sub_eq_iff_eq_add]

omit [DecidableEq n] in
/-- Let $(x_*,y_*)$ solve the original saddle equations and $(x,y)$ solve the regularized
system with lower-right block $-\varepsilon I$. Applying the regularized matrix to the
error $(x-x_*,y-y_*)$ gives $(0,\varepsilon y_*)$. -/
theorem saddlePenalty_error_mulVec (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    (ε : ℝ) (f x xStar : n → ℝ) (g y yStar : m → ℝ)
    (hsol : A *ᵥ xStar + Bᵀ *ᵥ yStar = f ∧ B *ᵥ xStar = g)
    (hpen : A *ᵥ x + Bᵀ *ᵥ y = f ∧ B *ᵥ x - ε • y = g) :
    (fromBlocks A Bᵀ B (-(ε • 1))) *ᵥ (Sum.elim (x - xStar) (y - yStar)) =
      ε • Sum.elim (0 : n → ℝ) yStar := by
  rw [fromBlocks_mulVec]
  have htop : A *ᵥ (x - xStar) + Bᵀ *ᵥ (y - yStar) = 0 := by
    simp only [mulVec_sub]
    rw [show A *ᵥ x - A *ᵥ xStar + (Bᵀ *ᵥ y - Bᵀ *ᵥ yStar) =
      (A *ᵥ x + Bᵀ *ᵥ y) - (A *ᵥ xStar + Bᵀ *ᵥ yStar) by abel]
    rw [hsol.1, hpen.1, sub_self]
  have hbottom : B *ᵥ (x - xStar) + (-(ε • 1)) *ᵥ (y - yStar) = ε • yStar := by
    rw [mulVec_sub, neg_mulVec, smul_mulVec, one_mulVec, smul_sub, hsol.2]
    rw [show B *ᵥ x - g + -(ε • y - ε • yStar) =
      (B *ᵥ x - ε • y) - g + ε • yStar by abel, hpen.2, sub_self, zero_add]
  change Sum.elim (A *ᵥ (x - xStar) + Bᵀ *ᵥ (y - yStar))
    (B *ᵥ (x - xStar) + (-(ε • 1)) *ᵥ (y - yStar)) = _
  rw [htop, hbottom]
  funext index
  cases index <;> simp

/-- The quadratic with coefficient matrix $A$ and linear term $f$ is
$J(x)=\tfrac12 x^TAx-f^Tx$. -/
noncomputable def saddleQuadratic (A : Matrix n n ℝ) (f x : n → ℝ) : ℝ :=
  (x ⬝ᵥ (A *ᵥ x)) / 2 - f ⬝ᵥ x

omit [DecidableEq n] in
/-- For symmetric $A$, the exact objective change for a displacement $d$ is
$J(x+d)-J(x)=d^T(Ax-f)+\tfrac12 d^TAd$. -/
theorem saddleQuadratic_add_sub (A : Matrix n n ℝ) (hA : A.IsHermitian) (f x d : n → ℝ) :
    saddleQuadratic A f (x + d) - saddleQuadratic A f x =
      d ⬝ᵥ (A *ᵥ x - f) + (d ⬝ᵥ (A *ᵥ d)) / 2 := by
  have hs : x ⬝ᵥ (A *ᵥ d) = d ⬝ᵥ (A *ᵥ x) := by
    simpa only [star_trivial] using hA.star_dotProduct_mulVec_comm x d
  simp only [saddleQuadratic, mulVec_add, dotProduct_add, add_dotProduct, dotProduct_sub, hs]
  rw [dotProduct_comm f d]
  ring

/-- The augmented Lagrangian adds $(Bx-g)^Ty+\frac{\gamma}{2}\|Bx-g\|_2^2$ to
the quadratic objective. -/
noncomputable def saddleAugmentedLagrangian (A : Matrix n n ℝ) (B : Matrix m n ℝ) (γ : ℝ)
    (f x : n → ℝ) (g y : m → ℝ) : ℝ :=
  saddleQuadratic A f x + (B *ᵥ x - g) ⬝ᵥ y +
    γ / 2 * ((B *ᵥ x - g) ⬝ᵥ (B *ᵥ x - g))

omit [DecidableEq n] [DecidableEq m] in
/-- The augmented Lagrangian at fixed multiplier equals the quadratic
with matrix $A+\gamma B^TB$ and linear term $f+\gamma B^Tg-B^Ty$, up to the constant
$-g^Ty+\frac{\gamma}{2}g^Tg$. -/
theorem saddleAugmentedLagrangian_eq_saddleQuadratic (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    (γ : ℝ) (f x : n → ℝ) (g y : m → ℝ) :
    saddleAugmentedLagrangian A B γ f x g y =
      saddleQuadratic (saddleAugmentedPrimal A B γ) (saddleAugmentedRhs B γ f g - Bᵀ *ᵥ y) x -
        g ⬝ᵥ y + γ / 2 * (g ⬝ᵥ g) := by
  simp only [saddleAugmentedLagrangian, saddleQuadratic, saddleAugmentedPrimal, saddleAugmentedRhs,
    add_mulVec, smul_mulVec, ← mulVec_mulVec, dotProduct_add, dotProduct_smul, sub_dotProduct,
    add_dotProduct, smul_dotProduct, dotProduct_sub, dotProduct_transpose_mulVec]
  have hf (w : m → ℝ) : (Bᵀ *ᵥ w) ⬝ᵥ x = w ⬝ᵥ (B *ᵥ x) := by
    rw [dotProduct_comm, dotProduct_transpose_mulVec]
  rw [hf, hf, dotProduct_comm (B *ᵥ x) g, dotProduct_comm (B *ᵥ x) y]
  ring

omit [DecidableEq n] in
/-- If $A$ is positive definite and $Ax=f$, the unique minimizer of
$J(z)=\tfrac12 z^TAz-f^Tz$ is $x$. -/
theorem saddleQuadratic_lt_of_mulVec_eq {A : Matrix n n ℝ} (hA : A.PosDef)
    {f x z : n → ℝ} (hx : A *ᵥ x = f) (hz : z ≠ x) :
    saddleQuadratic A f x < saddleQuadratic A f z := by
  have hpos : 0 < (z - x) ⬝ᵥ (A *ᵥ (z - x)) := by
    simpa using hA.dotProduct_mulVec_pos (sub_ne_zero.mpr hz)
  have hd := saddleQuadratic_add_sub A hA.isHermitian f x (z - x)
  rw [add_sub_cancel, hx, sub_self, dotProduct_zero, zero_add] at hd
  linarith

omit [DecidableEq n] [DecidableEq m] in
/-- If $A$ is positive semidefinite with $\ker A\cap\ker B=\{0\}$, the primal component
$x$ of a saddle solution strictly minimizes the quadratic among $z$ with $Bz=Bx$. -/
theorem saddleQuadratic_lt_of_saddle_solution {A : Matrix n n ℝ} (B : Matrix m n ℝ)
    (hA : A.PosSemidef) (hker : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥)
    {f x z : n → ℝ} {y : m → ℝ} (hx : A *ᵥ x + Bᵀ *ᵥ y = f)
    (hz : B *ᵥ z = B *ᵥ x) (hne : z ≠ x) :
    saddleQuadratic A f x < saddleQuadratic A f z := by
  let d := z - x
  have hB : B *ᵥ d = 0 := by dsimp [d]; rw [mulVec_sub, hz, sub_self]
  have hAq : 0 ≤ d ⬝ᵥ (A *ᵥ d) := by simpa using hA.dotProduct_mulVec_nonneg d
  have hpos : 0 < d ⬝ᵥ (A *ᵥ d) := by
    refine lt_of_le_of_ne hAq fun hzero => ?_
    have hAd := hA.dotProduct_mulVec_zero_iff.mp (by simpa using hzero.symm)
    exact sub_ne_zero.mpr hne ((Submodule.eq_bot_iff _).mp hker d ⟨hAd, hB⟩)
  have htop : A *ᵥ x - f = -(Bᵀ *ᵥ y) := by rw [← hx]; abel
  have hz' : x + d = z := by dsimp [d]; abel
  have hd := saddleQuadratic_add_sub A hA.isHermitian f x d
  rw [hz', htop, dotProduct_neg, dotProduct_transpose_mulVec, hB, dotProduct_zero,
    neg_zero, zero_add] at hd
  linarith

omit [DecidableEq n] [DecidableEq m] in
/-- If the augmented primal block is positive definite, a vector is a global minimizer
of the augmented Lagrangian at fixed $y$ if and only if
$(A+\gamma B^TB)x=f+\gamma B^Tg-B^Ty$. -/
theorem isLeast_saddleAugmentedLagrangian_iff (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    (γ : ℝ) (f x : n → ℝ) (g y : m → ℝ) (hP : (saddleAugmentedPrimal A B γ).PosDef) :
    IsLeast (Set.range fun z => saddleAugmentedLagrangian A B γ f z g y)
      (saddleAugmentedLagrangian A B γ f x g y) ↔
      saddleAugmentedPrimal A B γ *ᵥ x = saddleAugmentedRhs B γ f g - Bᵀ *ᵥ y := by
  classical
  let P := saddleAugmentedPrimal A B γ
  let rhs := saddleAugmentedRhs B γ f g - Bᵀ *ᵥ y
  have hlt (v z : n → ℝ) (hv : P *ᵥ v = rhs) (hz : z ≠ v) :
      saddleAugmentedLagrangian A B γ f v g y < saddleAugmentedLagrangian A B γ f z g y := by
    simp only [saddleAugmentedLagrangian_eq_saddleQuadratic]
    have := saddleQuadratic_lt_of_mulVec_eq hP hv hz
    linarith
  let v := P⁻¹ *ᵥ rhs
  have hv : P *ᵥ v = rhs := by
    rw [show P *ᵥ v = _ from mulVec_mulVec _ _ _,
      mul_nonsing_inv _ ((isUnit_iff_isUnit_det P).mp hP.isUnit), one_mulVec]
  constructor
  · intro h
    by_cases hx : x = v
    · exact hx ▸ hv
    · exact False.elim ((not_lt_of_ge (h.2 ⟨v, rfl⟩)) (hlt v x hv hx))
  · intro hx
    refine ⟨⟨x, rfl⟩, ?_⟩
    rintro _ ⟨z, rfl⟩
    by_cases hz : z = x
    · rw [hz]
    · exact (hlt x z hx hz).le

open Filter Asymptotics
open scoped Topology

/-- Let $M$ be nonsingular and $D$ any square matrix. If
$(M-\gamma^{-1}D)e(\gamma)=\gamma^{-1}v$ for all sufficiently large $\gamma$, then
$\gamma e(\gamma)$ converges to $M^{-1}v$ as $\gamma\to+\infty$. -/
theorem tendsto_smul_error_of_affine_matrix_perturbation (M D : Matrix n n ℝ)
    (hM : IsUnit M) (v : n → ℝ) (e : ℝ → n → ℝ)
    (he : ∀ᶠ γ in atTop, (M - γ⁻¹ • D) *ᵥ e γ = γ⁻¹ • v) :
    Tendsto (fun γ => γ • e γ) atTop (𝓝 (M⁻¹ *ᵥ v)) := by
  let R (γ : ℝ) := M - γ⁻¹ • D
  have hR : Tendsto R atTop (𝓝 M) := by
    simpa only [zero_smul, sub_zero] using
      (tendsto_const_nhds (x := M)).sub
        ((tendsto_inv_atTop_zero (𝕜 := ℝ)).smul (tendsto_const_nhds (x := D)))
  have hdet : M.det ≠ 0 := ((isUnit_iff_isUnit_det M).mp hM).ne_zero
  have hc : ContinuousAt (fun T : Matrix n n ℝ => T⁻¹) M := by
    apply continuousAt_matrix_inv
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hdet
  have hv : Continuous (fun T : Matrix n n ℝ => T *ᵥ v) :=
    continuous_id.matrix_mulVec continuous_const
  have hunit : ∀ᶠ γ in atTop, (R γ).det ≠ 0 :=
    ((continuous_id.matrix_det.tendsto M).comp hR).eventually
      (isOpen_ne.mem_nhds hdet)
  apply ((hv.tendsto M⁻¹).comp (hc.tendsto.comp hR)).congr'
  filter_upwards [he, hunit, eventually_gt_atTop (0 : ℝ)] with γ hγ hRu hpos
  have he' := congrArg (fun z => (R γ)⁻¹ *ᵥ z) hγ
  change (R γ)⁻¹ *ᵥ (R γ *ᵥ e γ) = (R γ)⁻¹ *ᵥ (γ⁻¹ • v) at he'
  rw [mulVec_mulVec, nonsing_inv_mul _ hRu.isUnit, one_mulVec, mulVec_smul] at he'
  change (R γ)⁻¹ *ᵥ v = γ • e γ
  rw [he', smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]

/-- Under the same perturbed system, any continuous linear image of the error is
$O(\gamma^{-1})$. This also gives Euclidean norm estimates for individual blocks. -/
theorem isBigO_saddlePenalty_error {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M D : Matrix n n ℝ) (hM : IsUnit M) (v : n → ℝ) (e : ℝ → n → ℝ)
    (he : ∀ᶠ γ in atTop, (M - γ⁻¹ • D) *ᵥ e γ = γ⁻¹ • v) (L : (n → ℝ) →L[ℝ] E) :
    (fun γ => L (e γ)) =O[atTop] (fun γ : ℝ => γ⁻¹) := by
  refine Optimization.isBigO_of_tendsto_inv_smul (z := L (M⁻¹ *ᵥ v)) ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with γ hγ using inv_pos.mpr hγ
  · simpa only [Function.comp_def, map_smul, inv_inv] using
      (L.continuous.tendsto _).comp
        (tendsto_smul_error_of_affine_matrix_perturbation M D hM v e he)

end Matrix

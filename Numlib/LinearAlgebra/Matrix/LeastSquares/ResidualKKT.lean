import Mathlib.LinearAlgebra.Matrix.Dual
import Numlib.Analysis.Normed.Lp.PiLp
import Numlib.LinearAlgebra.Matrix.LeastSquares.Constrained
import Numlib.LinearAlgebra.Matrix.LeastSquares.Weighted
import Numlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.Optimization.AffineQuadraticKKT

/-!
# Residual formulations of least-squares optimality

Least-squares minimizers satisfy linear optimality equations in the unknown and a
residual variable. This holds for equality constraints, for a positive definite
covariance and a nonnegative Tikhonov penalty, and for possibly singular covariances
in the factored minimum-noise model. The proofs use the affine quadratic
criterion in `Numlib.Optimization.AffineQuadraticKKT`.

## Main definitions

* `Matrix.weightedRegularizedResidualSq`: a squared weighted residual plus a Tikhonov penalty.

## Main results

* `Matrix.isLSESolution_iff_exists_residual_kkt`: augmented equations with equality constraints.
* `Matrix.isMinOn_weightedRegularizedResidualSq_iff`: weighted and regularized augmented equations.
* `Matrix.isGeneralizedLeastSquaresSolution_iff_exists_residual_kkt`: augmentation with
  a noise factor.
-/

namespace Matrix

open LinearMap

variable {n m q k : Type*} [Fintype n] [Fintype m] [Fintype q] [Fintype k]
  [DecidableEq n] [DecidableEq m] [DecidableEq q] [DecidableEq k]

omit [DecidableEq n] in
private theorem dotProduct_eq_zero_of_forall {v : n → ℝ} (h : ∀ w, v ⬝ᵥ w = 0) :
    v = 0 := by
  classical
  exact (dotProductEquiv ℝ n).injective (LinearMap.ext fun w ↦ by simpa using h w)

private noncomputable def residualCost {V : Type*} [AddCommGroup V] [Module ℝ V]
    (W : Matrix m m ℝ) (A : V →ₗ[ℝ] (m → ℝ)) (b : m → ℝ)
    (L : V →ₗ[ℝ] (k → ℝ)) (γ : ℝ) (x : V) : ℝ :=
  let r := b - A x
  r ⬝ᵥ (W *ᵥ r) + γ * (L x ⬝ᵥ L x)

omit [DecidableEq m] [DecidableEq k] in
private theorem isMinOn_residualCost_iff_dual {V Q : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup Q] [Module ℝ Q]
    {W : Matrix m m ℝ} (hW : W.PosSemidef) (A : V →ₗ[ℝ] (m → ℝ)) (b : m → ℝ)
    (L : V →ₗ[ℝ] (k → ℝ)) {γ : ℝ} (hγ : 0 ≤ γ) (E : V →ₗ[ℝ] Q)
    {d : Q} {x : V} (hx : E x = d) :
    IsMinOn (residualCost W A b L γ) {u | E u = d} x ↔
      ∃ multiplier : Module.Dual ℝ Q, ∀ v,
        (W *ᵥ (b - A x)) ⬝ᵥ A v = γ * (L x ⬝ᵥ L v) + multiplier (E v) := by
  classical
  let a := ((dotProductEquiv ℝ m).toLinearMap.compl₁₂ (W.mulVecLin.comp A) A) +
    γ • ((dotProductEquiv ℝ k).toLinearMap.compl₁₂ L L)
  let load := (dotProductEquiv ℝ m (W *ᵥ b)).comp A
  have ha (u v : V) : a u v = (W *ᵥ A u) ⬝ᵥ A v + γ * (L u ⬝ᵥ L v) := rfl
  have hload (v : V) : load v = (W *ᵥ b) ⬝ᵥ A v := rfl
  have hsym (u v : m → ℝ) : (W *ᵥ u) ⬝ᵥ v = (W *ᵥ v) ⬝ᵥ u := by
    rw [dotProduct_comm _ v, dotProduct_comm _ u]
    exact hW.isHermitian.isSymm.dotProduct_mulVec_comm
  have hasymm (u v : V) : a u v = a v u := by
    rw [ha, ha, hsym (A u), dotProduct_comm (L u)]
  have ha₀ (v : V) : 0 ≤ a v v := by
    rw [ha, dotProduct_comm (W *ᵥ A v)]
    exact add_nonneg (by simpa using hW.dotProduct_mulVec_nonneg (A v))
      (mul_nonneg hγ (by rw [dotProduct_self_eq_norm_sq]; positivity))
  have hcost (v : V) : residualCost W A b L γ v =
      2 * quadraticEnergy a load v + b ⬝ᵥ (W *ᵥ b) := by
    rw [residualCost, quadraticEnergy_apply, ha, hload, mulVec_sub, sub_dotProduct,
      dotProduct_sub, dotProduct_sub, dotProduct_comm (A v) (W *ᵥ b),
      dotProduct_comm b (W *ᵥ A v), hsym (A v) b, dotProduct_comm (A v) (W *ᵥ A v)]
    ring
  have hmin : IsMinOn (residualCost W A b L γ) {u | E u = d} x ↔
      IsMinOn (quadraticEnergy a load) {u | E u = d} x := by
    constructor <;> intro h v hv
    · have hh : residualCost W A b L γ x ≤ residualCost W A b L γ v := h hv
      rw [hcost, hcost] at hh
      change quadraticEnergy a load x ≤ quadraticEnergy a load v
      linarith only [hh]
    · change residualCost W A b L γ x ≤ residualCost W A b L γ v
      rw [hcost, hcost]
      have hh : quadraticEnergy a load x ≤ quadraticEnergy a load v := h hv
      linarith only [hh]
  rw [hmin, isMinOn_quadraticEnergy_iff_exists_dual a load E hasymm ha₀ hx]
  apply exists_congr
  intro multiplier
  apply forall_congr'
  intro v
  rw [ha, hload, mulVec_sub, sub_dotProduct]
  constructor <;> intro h <;> linarith

omit [DecidableEq m] [DecidableEq q] in
/-- For real matrices $A,B$ with the same column index, a vector $x$ minimizes
$\|Ax-b\|_2$ subject to $Bx=d$ if and only if there are a residual $r$ and multiplier
$\lambda$ with $r+Ax=b$, $Bx=d$ and $A^T r+B^T\lambda=0$. -/
theorem isLSESolution_iff_exists_residual_kkt (A : Matrix m n ℝ) (B : Matrix q n ℝ)
    (b : m → ℝ) (d : q → ℝ) (x : n → ℝ) :
    IsLSESolution A (WithLp.toLp 2 b) B (WithLp.toLp 2 d) (WithLp.toLp 2 x) ↔
      ∃ (r : m → ℝ) (multiplier : q → ℝ), r + A *ᵥ x = b ∧ B *ᵥ x = d ∧
        Aᵀ *ᵥ r + Bᵀ *ᵥ multiplier = 0 := by
  classical
  have hcost (v : n → ℝ) :
      residualCost (1 : Matrix m m ℝ) A.mulVecLin b (0 : (n → ℝ) →ₗ[ℝ] (m → ℝ)) 0 v =
        ‖toEuclideanLin A (WithLp.toLp 2 v) - WithLp.toLp 2 b‖ ^ 2 := by
    simp only [residualCost, mulVecLin_apply, one_mulVec, zero_mul, add_zero,
      dotProduct_self_eq_norm_sq, toEuclideanLin_toLp]
    rw [WithLp.toLp_sub, norm_sub_rev]
  have hbridge :
      IsLSESolution A (WithLp.toLp 2 b) B (WithLp.toLp 2 d) (WithLp.toLp 2 x) ↔
        B *ᵥ x = d ∧
          IsMinOn (residualCost (1 : Matrix m m ℝ) A.mulVecLin b
            (0 : (n → ℝ) →ₗ[ℝ] (m → ℝ)) 0) {v | B *ᵥ v = d} x := by
    constructor
    · intro h
      refine ⟨WithLp.toLp_injective 2 (by simpa only [toEuclideanLin_toLp] using h.feasible), ?_⟩
      intro v hv
      change residualCost _ _ _ _ _ x ≤ residualCost _ _ _ _ _ v
      rw [hcost, hcost]
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
        (h.le (WithLp.toLp 2 v) (by rw [toEuclideanLin_toLp, show B *ᵥ v = d from hv]))
    · rintro ⟨hx, h⟩
      refine ⟨by rw [toEuclideanLin_toLp, hx], fun v hv ↦ ?_⟩
      obtain ⟨v, rfl⟩ := (WithLp.toLp_surjective (p := 2) (V := n → ℝ)) v
      have hle : residualCost (1 : Matrix m m ℝ) A.mulVecLin b
          (0 : (n → ℝ) →ₗ[ℝ] (m → ℝ)) 0 x ≤ residualCost _ _ _ _ _ v :=
        h (show v ∈ {w | B *ᵥ w = d} from
          WithLp.toLp_injective 2 (by simpa only [toEuclideanLin_toLp] using hv))
      rw [hcost, hcost] at hle
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hle
  rw [hbridge]
  constructor
  · rintro ⟨hx, hmin⟩
    obtain ⟨multiplier, h⟩ :=
      (isMinOn_residualCost_iff_dual (PosSemidef.one : (1 : Matrix m m ℝ).PosSemidef)
        A.mulVecLin b (0 : (n → ℝ) →ₗ[ℝ] (m → ℝ)) le_rfl B.mulVecLin hx).mp hmin
    obtain ⟨multiplierVec, rfl⟩ := (dotProductEquiv ℝ q).surjective multiplier
    refine ⟨b - A *ᵥ x, -multiplierVec, sub_add_cancel _ _, hx,
      dotProduct_eq_zero_of_forall fun v ↦ ?_⟩
    simp only [add_dotProduct, mulVec_neg, neg_dotProduct]
    rw [dotProduct_comm (Aᵀ *ᵥ _), dotProduct_comm (Bᵀ *ᵥ _),
      dotProduct_transpose_mulVec, dotProduct_transpose_mulVec, ← sub_eq_add_neg]
    exact sub_eq_zero.mpr (by simpa using h v)
  · rintro ⟨r, multiplier, hr, hx, hstat⟩
    refine ⟨hx, (isMinOn_residualCost_iff_dual
      (PosSemidef.one : (1 : Matrix m m ℝ).PosSemidef) A.mulVecLin b
      (0 : (n → ℝ) →ₗ[ℝ] (m → ℝ)) le_rfl B.mulVecLin hx).mpr
        ⟨dotProductEquiv ℝ q (-multiplier), ?_⟩⟩
    intro v
    have heq := congrArg (fun w ↦ v ⬝ᵥ w) hstat
    rw [dotProduct_add, dotProduct_zero, dotProduct_transpose_mulVec,
      dotProduct_transpose_mulVec] at heq
    simp [← eq_sub_of_add_eq hr, eq_neg_of_add_eq_zero_left heq]

/-- The **weighted regularized squared residual** for covariance $W$, design $A$, data $b$,
penalty matrix $L$, and weight $\gamma$ is $(b-Ax)^TW^{-1}(b-Ax)+\gamma\|Lx\|_2^2$.
Here the inverse is totalized to zero at a singular matrix. -/
noncomputable def weightedRegularizedResidualSq (W : Matrix m m ℝ) (A : Matrix m n ℝ)
    (b : m → ℝ) (L : Matrix k n ℝ) (γ : ℝ) (x : n → ℝ) : ℝ :=
  residualCost W⁻¹ A.mulVecLin b L.mulVecLin γ x

omit [DecidableEq n] [DecidableEq k] in
/-- The weighted regularized residual evaluates to a quadratic form in $b-Ax$ plus the
weighted squared Euclidean norm of $Lx$. -/
theorem weightedRegularizedResidualSq_apply (W : Matrix m m ℝ) (A : Matrix m n ℝ)
    (b : m → ℝ) (L : Matrix k n ℝ) (γ : ℝ) (x : n → ℝ) :
    weightedRegularizedResidualSq W A b L γ x =
      (b - A *ᵥ x) ⬝ᵥ (W⁻¹ *ᵥ (b - A *ᵥ x)) +
        γ * ‖(WithLp.toLp 2 (L *ᵥ x) : EuclideanSpace ℝ k)‖ ^ 2 := by
  rw [weightedRegularizedResidualSq, residualCost, dotProduct_self_eq_norm_sq]
  rfl

omit [DecidableEq n] [DecidableEq k] in
/-- For a positive definite covariance $W$ and nonnegative penalty weight $\gamma$, the
weighted regularized squared residual is minimal at $x$ if and only if some $r$ satisfies
$Wr+Ax=b$ and $A^T r=\gamma(L^T L)x$. -/
theorem isMinOn_weightedRegularizedResidualSq_iff (W : Matrix m m ℝ) (A : Matrix m n ℝ)
    (b : m → ℝ) (L : Matrix k n ℝ) (γ : ℝ) (x : n → ℝ) (hW : W.PosDef) (hγ : 0 ≤ γ) :
    IsMinOn (weightedRegularizedResidualSq W A b L γ) Set.univ x ↔
      ∃ r : m → ℝ, W *ᵥ r + A *ᵥ x = b ∧ Aᵀ *ᵥ r = γ • ((Lᵀ * L) *ᵥ x) := by
  classical
  let residual := W⁻¹ *ᵥ (b - A *ᵥ x)
  have hres (r : m → ℝ) : W *ᵥ r + A *ᵥ x = b ↔ r = residual := by
    rw [← eq_sub_iff_add_eq]
    constructor
    · intro hr
      simpa [residual, ← hr] using (nonsing_inv_mulVec_mulVec hW.isUnit r).symm
    · rintro rfl
      exact mulVec_nonsing_inv_mulVec hW.isUnit _
  rw [show (∃ r : m → ℝ, W *ᵥ r + A *ᵥ x = b ∧ Aᵀ *ᵥ r = γ • ((Lᵀ * L) *ᵥ x)) ↔
      Aᵀ *ᵥ residual = γ • ((Lᵀ * L) *ᵥ x) by simp only [hres, exists_eq_left]]
  have huniv : {v | (0 : (n → ℝ) →ₗ[ℝ] ℝ) v = 0} = Set.univ := by simp
  change IsMinOn (residualCost W⁻¹ A.mulVecLin b L.mulVecLin γ) Set.univ x ↔ _
  rw [← huniv]
  rw [isMinOn_residualCost_iff_dual hW.inv.posSemidef A.mulVecLin b L.mulVecLin hγ
    (0 : (n → ℝ) →ₗ[ℝ] ℝ) (show (0 : (n → ℝ) →ₗ[ℝ] ℝ) x = 0 from rfl)]
  simp only [LinearMap.zero_apply, map_zero, add_zero, mulVecLin_apply]
  constructor
  · rintro ⟨_, h⟩
    apply sub_eq_zero.mp
    apply dotProduct_eq_zero_of_forall
    intro v
    rw [sub_dotProduct, smul_dotProduct, ← mulVec_mulVec,
      dotProduct_comm (Aᵀ *ᵥ _), dotProduct_comm (Lᵀ *ᵥ _),
      dotProduct_transpose_mulVec, dotProduct_transpose_mulVec, smul_eq_mul]
    exact sub_eq_zero.mpr (h v)
  · intro h
    refine ⟨0, fun v ↦ ?_⟩
    have heq := congrArg (fun w ↦ v ⬝ᵥ w) h
    rwa [dotProduct_smul, ← mulVec_mulVec, dotProduct_transpose_mulVec,
      dotProduct_transpose_mulVec, smul_eq_mul] at heq

omit [DecidableEq m] in
/-- Let $A$ be a real design matrix and $F$ a real noise factor with the same number of rows.
A feasible pair $(x,v)$ minimizes $\|v\|_2$ under $Ax+Fv=b$ if and only if some $r$
satisfies $(FF^T)r+Ax=b$, $A^T r=0$ and $v=F^T r$. The factor can be rectangular or singular. -/
theorem isGeneralizedLeastSquaresSolution_iff_exists_residual_kkt
    (A : Matrix m n ℝ) (F : Matrix m k ℝ) (b : m → ℝ) (x : n → ℝ) (v : k → ℝ) :
    IsGeneralizedLeastSquaresSolution A F (WithLp.toLp 2 b) (WithLp.toLp 2 x) (WithLp.toLp 2 v) ↔
      ∃ r : m → ℝ, (F * Fᵀ) *ᵥ r + A *ᵥ x = b ∧ Aᵀ *ᵥ r = 0 ∧ Fᵀ *ᵥ r = v := by
  classical
  let E := A.mulVecLin.coprod F.mulVecLin
  let L := LinearMap.snd ℝ (n → ℝ) (k → ℝ)
  let J := residualCost (1 : Matrix k k ℝ) L (0 : k → ℝ) L 0
  have hE (x' : n → ℝ) (v' : k → ℝ) : E (x', v') = A *ᵥ x' + F *ᵥ v' := rfl
  have hJ (x' : n → ℝ) (v' : k → ℝ) : J (x', v') = ‖WithLp.toLp 2 v'‖ ^ 2 := by
    simp [J, residualCost, L, dotProduct_self_eq_norm_sq]
  have hfeas (x' : n → ℝ) (v' : k → ℝ) :
      WithLp.toLp 2 b =
          toEuclideanLin A (WithLp.toLp 2 x') + toEuclideanLin F (WithLp.toLp 2 v') ↔
        E (x', v') = b := by
    rw [hE, toEuclideanLin_toLp, toEuclideanLin_toLp, ← WithLp.toLp_add,
      (WithLp.toLp_injective 2).eq_iff, eq_comm]
  have hbridge :
      IsGeneralizedLeastSquaresSolution A F (WithLp.toLp 2 b) (WithLp.toLp 2 x) (WithLp.toLp 2 v) ↔
        E (x, v) = b ∧ IsMinOn J {p | E p = b} (x, v) := by
    constructor
    · intro h
      refine ⟨(hfeas x v).mp h.eq_add, ?_⟩
      rintro ⟨x', v'⟩ hp
      change J (x, v) ≤ J (x', v')
      rw [hJ, hJ]
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
        (h.norm_le (WithLp.toLp 2 x') (WithLp.toLp 2 v') ((hfeas x' v').mpr hp))
    · rintro ⟨hf, hmin⟩
      refine ⟨(hfeas x v).mpr hf, fun x' v' hp ↦ ?_⟩
      obtain ⟨x', rfl⟩ := (WithLp.toLp_surjective (p := 2) (V := n → ℝ)) x'
      obtain ⟨v', rfl⟩ := (WithLp.toLp_surjective (p := 2) (V := k → ℝ)) v'
      have hle : J (x, v) ≤ J (x', v') := hmin ((hfeas x' v').mp hp)
      rw [hJ, hJ] at hle
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hle
  have hstat (hf : E (x, v) = b) : IsMinOn J {p | E p = b} (x, v) ↔
      ∃ r : m → ℝ, ∀ (dx : n → ℝ) (dv : k → ℝ),
        v ⬝ᵥ dv = r ⬝ᵥ (A *ᵥ dx + F *ᵥ dv) := by
    change IsMinOn (residualCost _ _ _ _ _) _ _ ↔ _
    rw [isMinOn_residualCost_iff_dual (PosSemidef.one : (1 : Matrix k k ℝ).PosSemidef)
      L (0 : k → ℝ) L le_rfl E hf]
    constructor
    · rintro ⟨functional, h⟩
      obtain ⟨r, rfl⟩ := (dotProductEquiv ℝ m).surjective functional
      refine ⟨-r, fun dx dv ↦ ?_⟩
      simpa [L, hE, add_comm] using congrArg Neg.neg (h (dx, dv))
    · rintro ⟨r, h⟩
      refine ⟨dotProductEquiv ℝ m (-r), fun p ↦ ?_⟩
      obtain ⟨dx, dv⟩ := p
      simpa [L, hE] using congrArg Neg.neg (h dx dv)
  rw [hbridge]
  constructor
  · rintro ⟨hf, hmin⟩
    obtain ⟨r, h⟩ := (hstat hf).mp hmin
    have hA : Aᵀ *ᵥ r = 0 := dotProduct_eq_zero_of_forall fun dx ↦ by
      rw [dotProduct_comm, dotProduct_transpose_mulVec]
      simpa using (h dx 0).symm
    have hF : Fᵀ *ᵥ r = v := sub_eq_zero.mp (dotProduct_eq_zero_of_forall fun dv ↦ by
      rw [sub_dotProduct, dotProduct_comm (Fᵀ *ᵥ r), dotProduct_transpose_mulVec]
      simpa using sub_eq_zero.mpr (h 0 dv).symm)
    exact ⟨r, by rw [← mulVec_mulVec, hF, add_comm, ← hE]; exact hf, hA, hF⟩
  · rintro ⟨r, htop, hA, hF⟩
    have hf : E (x, v) = b := by rwa [hE, ← hF, add_comm, mulVec_mulVec]
    refine ⟨hf, (hstat hf).mpr ⟨r, fun dx dv ↦ ?_⟩⟩
    rw [dotProduct_add, ← dotProduct_transpose_mulVec, hA, dotProduct_zero,
      zero_add, ← dotProduct_transpose_mulVec, hF, dotProduct_comm]

end Matrix

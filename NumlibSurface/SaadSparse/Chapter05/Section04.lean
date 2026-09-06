import Numlib.LinearSolve.Projection.Additive
import NumlibSurface.SaadSparse.Chapter05.Section01

/-!
# Saad §5.4: additive and multiplicative projection processes

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §5.4: the additive procedure (Algorithm 5.5) with relaxation parameters, its residual identity
(5.22)–(5.23), the projectors `P_i = A V_i (V_iᵀ A V_i)⁻¹ V_iᵀ`, and the multiplicative procedure
(Algorithm 5.6).

Saad's remark that each inner step of the block relaxations of §4.1.1 is an orthogonal
projection step over `K_i = span(V_i)` is `blockCorrection_eq_projStep`: (4.17) is literally
(5.7) with `W = V = V_i`.

With `K_i = span(V_i)` (`ProjFamily.subspace`) and `V_iᵀ A V_i` nonsingular, the pair `(K_i, K_i)`
is nondegenerate in the sense of the backbone, and Algorithms 5.5 and 5.6 are the backbone's
`Projection.additiveStep` and `Projection.multiplicativeStep` (`additiveStep_eq`,
`multiplicativeSweep_eq`), so their residual identities are `Projection.residual_additiveStep`
and `Projection.residual_multiplicativeStep`.  `P_i_isProjOnto` is the second half of
(5.22)–(5.23), and `leastSquares_P_i_eq_starProjection` with `sum_P_i_eq_one` are the
least-squares option and its exactness criterion.
-/

open Matrix Module Finset
open scoped SaadSparse

namespace SaadSparse.Chapter05

variable {n : ℕ}

local notation "E" n => EuclideanSpace ℝ (Fin n)

/-- Saad §5.4: a family of `p` subspaces of `ℝⁿ`, each given by a matrix of basis columns. -/
structure ProjFamily (n : ℕ) where
  /-- The number of subspaces. -/
  p : ℕ
  /-- The dimension of the `i`-th subspace. -/
  size : Fin p → ℕ
  /-- The `i`-th matrix of basis columns. -/
  V : ∀ i, Matrix (Fin n) (Fin (size i)) ℝ

/-- Saad §5.4: the subspace `K_i = span(V_i)` spanned by the columns of the `i`-th basis
matrix. -/
def ProjFamily.subspace (𝒱 : ProjFamily n) (i : Fin 𝒱.p) : Submodule ℝ (E n) :=
  Submodule.span ℝ (Set.range (𝒱.V i).cols)

variable (𝒱 : ProjFamily n) (A : Matrix (Fin n) (Fin n) ℝ)

/-- Saad §5.4: the local correction matrix `V_i (V_iᵀ A V_i)⁻¹ V_iᵀ` of the `i`-th subspace. -/
noncomputable def corrector (i : Fin 𝒱.p) : Matrix (Fin n) (Fin n) ℝ :=
  𝒱.V i * ((𝒱.V i)ᵀ * A * 𝒱.V i)⁻¹ * (𝒱.V i)ᵀ

/-- Saad (5.22): the projector `P_i = A V_i (V_iᵀ A V_i)⁻¹ V_iᵀ` onto `A K_i` orthogonally to
`K_i`. -/
noncomputable def P_i (i : Fin 𝒱.p) : Matrix (Fin n) (Fin n) ℝ :=
  A * 𝒱.V i * ((𝒱.V i)ᵀ * A * 𝒱.V i)⁻¹ * (𝒱.V i)ᵀ

/-- Saad, Algorithm 5.5, with relaxation parameters `ω_i`. -/
noncomputable def additiveStep (ω : Fin 𝒱.p → ℝ) (b x : E n) : E n :=
  x + ∑ i, ω i • ((corrector 𝒱 A i) ⬝ (b - (A ⬝ x)))

/-- Saad, Algorithm 5.6: one multiplicative sweep, successive projection steps over
`K_1, …, K_p`. -/
noncomputable def multiplicativeSweep (b : E n) (x : E n) : E n :=
  (List.finRange 𝒱.p).foldl (fun y i => projStep A b (𝒱.V i) (𝒱.V i) y) x

variable {𝒱 A}

/-- `P_i` is Saad's (1.66) projector for the bases `A V_i` and `V_i`. -/
theorem P_i_eq_obliqueProj (i : Fin 𝒱.p) :
    P_i 𝒱 A i = Matrix.obliqueProj (A * 𝒱.V i) (𝒱.V i) := by
  rw [P_i, Matrix.obliqueProj, conjTranspose_eq_transpose, Matrix.mul_assoc (𝒱.V i)ᵀ A]

/-- `A` times the local corrector is the projector `P_i`. -/
theorem mul_corrector (i : Fin 𝒱.p) : A * corrector 𝒱 A i = P_i 𝒱 A i := by
  rw [corrector, P_i, ← Matrix.mul_assoc, ← Matrix.mul_assoc]

/-- Matrices act on `ℝⁿ` through `toEuclideanLin` multiplicatively. -/
theorem toEuclideanLin_mul_apply (M N : Matrix (Fin n) (Fin n) ℝ) (z : E n) :
    ((M * N) ⬝ z) = M ⬝ (N ⬝ z) := by
  have h : (M * N) *ᵥ WithLp.ofLp z = M *ᵥ (N *ᵥ WithLp.ofLp z) := (mulVec_mulVec _ _ _).symm
  exact congrArg (WithLp.toLp 2) h

/-- Saad (5.22)–(5.23): the residual of the additive procedure is
`r_{k+1} = (I - ∑ ω_i P_i) r_k`. -/
theorem residual_additiveStep (ω : Fin 𝒱.p → ℝ) (b x : E n) :
    b - (A ⬝ additiveStep 𝒱 A ω b x) =
      (b - (A ⬝ x)) - ∑ i, ω i • ((P_i 𝒱 A i) ⬝ (b - (A ⬝ x))) := by
  rw [additiveStep, map_add, map_sum]
  simp only [map_smul, ← toEuclideanLin_mul_apply, mul_corrector]
  abel

/-- Saad §5.4: (4.17), the block-relaxation correction, is the projection step (5.7) with
`W = V = V_i`. -/
theorem blockCorrection_eq_projStep {m : ℕ} (V : Matrix (Fin n) (Fin m) ℝ) (b x : E n) :
    x + ((V * (Vᵀ * A * V)⁻¹ * Vᵀ) ⬝ (b - (A ⬝ x))) = projStep A b V V x := rfl

/-! ### §5.4 as the backbone's additive and multiplicative projection processes -/

section Backbone

variable {m : ℕ}

/-- The columns of `A V` are the images of the columns of `V`. -/
theorem cols_mul (A : Matrix (Fin n) (Fin n) ℝ) (V : Matrix (Fin n) (Fin m) ℝ) (j : Fin m) :
    (A * V).cols j = (A ⬝ V.cols j) :=
  congrArg (WithLp.toLp 2) (funext fun i => by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply])

/-- `span (A V) = A (span V)`: the test space of the least-squares option is the image of the
trial space. -/
theorem span_cols_mul (A : Matrix (Fin n) (Fin n) ℝ) (V : Matrix (Fin n) (Fin m) ℝ) :
    Submodule.span ℝ (Set.range (A * V).cols) =
      (Submodule.span ℝ (Set.range V.cols)).map (toEuclideanLin A) := by
  rw [Submodule.map_span, ← Set.range_comp]
  exact congrArg (Submodule.span ℝ) (congrArg Set.range (funext (cols_mul A V)))

/-- The inner product of a column of `X` and a column of `Y` is the corresponding entry of the
cross Gram matrix `Xᵀ Y`. -/
theorem inner_cols {m' : ℕ} (X : Matrix (Fin n) (Fin m) ℝ) (Y : Matrix (Fin n) (Fin m') ℝ)
    (k : Fin m) (l : Fin m') : inner ℝ (X.cols k) (Y.cols l) = (Xᵀ * Y) k l := by
  rw [SaadSparse.inner_eq_dotProduct_star, Matrix.mul_apply]
  simp [dotProduct, Matrix.transpose_apply, mul_comm]

variable {A : Matrix (Fin n) (Fin n) ℝ} {V : Matrix (Fin n) (Fin m) ℝ}

/-- If `VᵀAV` is nonsingular then the columns of `V` are linearly independent: a dependence
`V c = 0` would give `(VᵀAV) c = 0`. -/
theorem linearIndependent_cols_of_isUnit (h : IsUnit (Vᵀ * A * V)) :
    LinearIndependent ℝ V.cols := by
  refine Fintype.linearIndependent_iff.mpr fun c hc => ?_
  have hV : V *ᵥ c = 0 := by
    have h0 : (V ⬝ (WithLp.toLp 2 c : E m)) = 0 := by
      rw [toEuclideanLin_apply_eq_sum]; exact hc
    exact congrArg WithLp.ofLp h0
  have hz : (Vᵀ * A * V) *ᵥ c = 0 := by
    rw [← mulVec_mulVec, hV, mulVec_zero]
  exact congrFun (mulVec_injective_iff_isUnit.mpr h (a₁ := c) (a₂ := 0)
    (by rw [hz, mulVec_zero]))

/-- If `VᵀAV` is nonsingular then the columns of `A V` are linearly independent too. -/
theorem linearIndependent_cols_mul_of_isUnit (h : IsUnit (Vᵀ * A * V)) :
    LinearIndependent ℝ (A * V).cols := by
  refine Fintype.linearIndependent_iff.mpr fun c hc => ?_
  have hAV : (A * V) *ᵥ c = 0 := by
    have h0 : ((A * V) ⬝ (WithLp.toLp 2 c : E m)) = 0 := by
      rw [toEuclideanLin_apply_eq_sum]; exact hc
    exact congrArg WithLp.ofLp h0
  have hz : (Vᵀ * A * V) *ᵥ c = 0 := by
    rw [Matrix.mul_assoc, ← mulVec_mulVec, hAV, mulVec_zero]
  exact congrFun (mulVec_injective_iff_isUnit.mpr h (a₁ := c) (a₂ := 0)
    (by rw [hz, mulVec_zero]))

/-- `V` is a basis of the space its columns span, as soon as `VᵀAV` is nonsingular. -/
theorem isBasisOf_of_isUnit (h : IsUnit (Vᵀ * A * V)) :
    V.IsBasisOf (Submodule.span ℝ (Set.range V.cols)) :=
  ⟨linearIndependent_cols_of_isUnit h, rfl⟩

/-- `A V` is a basis of `A (span V)`, as soon as `VᵀAV` is nonsingular. -/
theorem isBasisOf_mul_of_isUnit (h : IsUnit (Vᵀ * A * V)) :
    (A * V).IsBasisOf ((Submodule.span ℝ (Set.range V.cols)).map (toEuclideanLin A)) :=
  ⟨linearIndependent_cols_mul_of_isUnit h, span_cols_mul A V⟩

/-- Saad, Proposition 5.1: `IsUnit (VᵀAV)` is exactly the backbone's nondegeneracy of the
Petrov–Galerkin pair `(span V, span V)`. -/
theorem isNondegeneratePair_of_isUnit (h : IsUnit (Vᵀ * A * V)) :
    Projection.IsNondegeneratePair (toEuclideanLin A) (Submodule.span ℝ (Set.range V.cols))
      (Submodule.span ℝ (Set.range V.cols)) :=
  ⟨rfl, (isUnit_transpose_mul_mul_iff (isBasisOf_of_isUnit h) (isBasisOf_of_isUnit h)).mp h⟩

/-- Saad (5.7): the projection step `x + V (WᵀAV)⁻¹ Wᵀ r` is a projection approximation onto
`span V` orthogonally to `span W`. -/
theorem projStep_isProjectionApprox {W : Matrix (Fin n) (Fin m) ℝ} {K L : Submodule ℝ (E n)}
    (hV : V.IsBasisOf K) (hW : W.IsBasisOf L) (h : IsUnit (Wᵀ * A * V)) (b x : E n) :
    IsProjectionApprox A b x K L (projStep A b V W x) := by
  have hstep : projStep A b V W x = x +
      (V ⬝ (WithLp.toLp 2 ((Wᵀ * A * V)⁻¹ *ᵥ (Wᵀ *ᵥ WithLp.ofLp (b - (A ⬝ x)))) : E m)) := by
    have hmul : (V * (Wᵀ * A * V)⁻¹ * Wᵀ) *ᵥ WithLp.ofLp (b - (A ⬝ x))
        = V *ᵥ ((Wᵀ * A * V)⁻¹ *ᵥ (Wᵀ *ᵥ WithLp.ofLp (b - (A ⬝ x)))) := by
      rw [← mulVec_mulVec, ← mulVec_mulVec]
    exact congrArg (fun z : E n => x + z) (congrArg (WithLp.toLp 2) hmul)
  rw [hstep, isProjectionApprox_add_iff hV hW, mulVec_mulVec,
    mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp h), one_mulVec]

/-- Saad (5.7): with `W = V` the projection step is the backbone's Petrov–Galerkin step of the
pair `(span V, span V)`. -/
theorem projStep_eq_pairStep (h : IsUnit (Vᵀ * A * V)) (b x : E n) :
    projStep A b V V x =
      Projection.pairStep (toEuclideanLin A) b (Submodule.span ℝ (Set.range V.cols))
        (Submodule.span ℝ (Set.range V.cols)) (isNondegeneratePair_of_isUnit h) x :=
  (isProjectionApprox_iff.mp
      (projStep_isProjectionApprox (isBasisOf_of_isUnit h) (isBasisOf_of_isUnit h) h b
        x)).eq_of_forall
    (Projection.pairStep_isPetrovGalerkin (isNondegeneratePair_of_isUnit h) x)
    (isNondegeneratePair_of_isUnit h).eq_zero_of_mem_orthogonal

end Backbone

section Family

variable {𝒲 : ProjFamily n} {A : Matrix (Fin n) (Fin n) ℝ}

/-- Saad §5.4: `IsUnit (V_iᵀ A V_i)` for every `i` makes each `(K_i, K_i)` a nondegenerate pair,
which is the hypothesis the backbone's additive and multiplicative processes take. -/
theorem isNondegeneratePair_subspace (h : ∀ i, IsUnit ((𝒲.V i)ᵀ * A * 𝒲.V i)) (i : Fin 𝒲.p) :
    Projection.IsNondegeneratePair (toEuclideanLin A) (𝒲.subspace i) (𝒲.subspace i) :=
  isNondegeneratePair_of_isUnit (h i)

/-- Saad (5.7) for the `i`-th subspace of the family. -/
theorem projStep_eq_pairStep_subspace (h : ∀ i, IsUnit ((𝒲.V i)ᵀ * A * 𝒲.V i)) (i : Fin 𝒲.p)
    (b x : E n) :
    projStep A b (𝒲.V i) (𝒲.V i) x =
      Projection.pairStep (toEuclideanLin A) b (𝒲.subspace i) (𝒲.subspace i)
        (isNondegeneratePair_subspace h i) x :=
  projStep_eq_pairStep (h i) b x

/-- Saad (5.22)–(5.23), the second half: `P_i = A V_i (V_iᵀ A V_i)⁻¹ V_iᵀ` is the projector onto
`A K_i` orthogonally to `K_i`. -/
theorem P_i_isProjOnto {i : Fin 𝒲.p} (h : IsUnit ((𝒲.V i)ᵀ * A * 𝒲.V i)) (z : E n) :
    SaadSparse.IsProjOnto ((𝒲.subspace i).map (toEuclideanLin A)) (𝒲.subspace i) z
      ((P_i 𝒲 A i) ⬝ z) := by
  have hunit : IsUnit ((𝒲.V i)ᴴ * (A * 𝒲.V i)) := by
    rwa [conjTranspose_eq_transpose, ← Matrix.mul_assoc]
  rw [P_i_eq_obliqueProj]
  exact SaadSparse.Chapter01.obliqueProj_isProjOnto (isBasisOf_mul_of_isUnit h)
    (isBasisOf_of_isUnit h) hunit z

/-- Saad, Algorithm 5.5 is the backbone's additive projection step, so its residual identity
(5.23) is `Projection.residual_additiveStep`. -/
theorem additiveStep_eq (h : ∀ i, IsUnit ((𝒲.V i)ᵀ * A * 𝒲.V i)) (ω : Fin 𝒲.p → ℝ) (b x : E n) :
    additiveStep 𝒲 A ω b x =
      Projection.additiveStep (toEuclideanLin A) b 𝒲.subspace 𝒲.subspace
        (isNondegeneratePair_subspace h) ω x := by
  have hlhs : additiveStep 𝒲 A ω b x
      = x + ∑ i, ω i • ((corrector 𝒲 A i) ⬝ (b - (A ⬝ x))) := rfl
  have hrhs : Projection.additiveStep (toEuclideanLin A) b 𝒲.subspace 𝒲.subspace
        (isNondegeneratePair_subspace h) ω x
      = x + ∑ i, ω i • (Projection.pairStep (toEuclideanLin A) b (𝒲.subspace i) (𝒲.subspace i)
          (isNondegeneratePair_subspace h i) x - x) := rfl
  rw [hlhs, hrhs]
  refine congrArg (fun z : E n => x + z) (Finset.sum_congr rfl fun i _ => ?_)
  refine congrArg (fun z : E n => ω i • z) ?_
  have hstep : projStep A b (𝒲.V i) (𝒲.V i) x = x + ((corrector 𝒲 A i) ⬝ (b - (A ⬝ x))) := rfl
  rw [← projStep_eq_pairStep_subspace h i b x, hstep]
  abel

/-- Saad, Algorithm 5.6 is the backbone's multiplicative projection sweep, so its residual is
the product of the `1 - P_i` (`Projection.residual_multiplicativeStep`). -/
theorem multiplicativeSweep_eq (h : ∀ i, IsUnit ((𝒲.V i)ᵀ * A * 𝒲.V i)) (b x : E n) :
    multiplicativeSweep 𝒲 A b x =
      Projection.multiplicativeStep (toEuclideanLin A) b 𝒲.subspace 𝒲.subspace
        (isNondegeneratePair_subspace h) (List.finRange 𝒲.p) x := by
  have hfun : (fun (y : E n) (i : Fin 𝒲.p) => projStep A b (𝒲.V i) (𝒲.V i) y) =
      fun (y : E n) (i : Fin 𝒲.p) => Projection.pairStep (toEuclideanLin A) b (𝒲.subspace i)
        (𝒲.subspace i) (isNondegeneratePair_subspace h i) y :=
    funext fun y => funext fun i => projStep_eq_pairStep_subspace h i b y
  have hlhs : multiplicativeSweep 𝒲 A b x
      = (List.finRange 𝒲.p).foldl (fun y i => projStep A b (𝒲.V i) (𝒲.V i) y) x := rfl
  have hrhs : Projection.multiplicativeStep (toEuclideanLin A) b 𝒲.subspace 𝒲.subspace
        (isNondegeneratePair_subspace h) (List.finRange 𝒲.p) x
      = (List.finRange 𝒲.p).foldl (fun y i => Projection.pairStep (toEuclideanLin A) b
          (𝒲.subspace i) (𝒲.subspace i) (isNondegeneratePair_subspace h i) y) x := rfl
  rw [hlhs, hrhs, hfun]

/-! ### The least-squares option -/

/-- Saad, the remark after (5.23): with `L_i = A K_i` the projector
`P_i = A V_i ((A V_i)ᵀ A V_i)⁻¹ (A V_i)ᵀ` is the *orthogonal* projector onto `A K_i`. -/
theorem leastSquares_P_i_eq_starProjection {i : Fin 𝒲.p}
    (h : IsUnit ((A * 𝒲.V i)ᵀ * (A * 𝒲.V i))) :
    toEuclideanLin (Matrix.obliqueProj (A * 𝒲.V i) (A * 𝒲.V i)) =
      (((𝒲.subspace i).map (toEuclideanLin A)).starProjection : (E n) →ₗ[ℝ] (E n)) := by
  have hg : IsUnit (LinearMap.crossGram ℝ (A * 𝒲.V i).cols (A * 𝒲.V i).cols) := by
    rw [Matrix.crossGram_cols, conjTranspose_eq_transpose]
    exact h
  have hmap : ((𝒲.subspace i).map (toEuclideanLin A))
      = Submodule.span ℝ (Set.range (A * 𝒲.V i).cols) := (span_cols_mul A (𝒲.V i)).symm
  rw [Matrix.toEuclideanLin_obliqueProj]
  refine LinearMap.ext fun z => (Submodule.eq_starProjection_of_mem_orthogonal ?_ ?_).symm
  · rw [hmap, ← LinearMap.range_obliqueProjectionOfBases _ _ hg]
    exact LinearMap.mem_range_self _ z
  · rw [hmap]
    exact LinearMap.sub_obliqueProjectionOfBases_apply_mem_orthogonal _ _ hg z

/-- Saad, the exactness remark after (5.23): if the `A V_i` are mutually orthogonal and the
dimensions of the `A K_i` add up to `n`, then `∑ P_i = 1`, so one unrelaxed outer step of the
least-squares additive process produces the exact solution. -/
theorem sum_P_i_eq_one (horth : ∀ i j, i ≠ j → (A * 𝒲.V i)ᵀ * (A * 𝒲.V j) = 0)
    (h : ∀ i, IsUnit ((A * 𝒲.V i)ᵀ * (A * 𝒲.V i)))
    (hdim : ∑ i, finrank ℝ ((𝒲.subspace i).map (toEuclideanLin A)) = n) :
    ∑ i, Matrix.obliqueProj (A * 𝒲.V i) (A * 𝒲.V i) = 1 := by
  have hspan : ∀ i, ((𝒲.subspace i).map (toEuclideanLin A))
      = Submodule.span ℝ (Set.range (A * 𝒲.V i).cols) :=
    fun i => (span_cols_mul A (𝒲.V i)).symm
  have horth' : ∀ i j, i ≠ j → Submodule.IsOrtho ((𝒲.subspace i).map (toEuclideanLin A))
      ((𝒲.subspace j).map (toEuclideanLin A)) := by
    intro i j hij
    rw [hspan i, hspan j, Submodule.isOrtho_span]
    rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩
    rw [inner_cols, horth i j hij, Matrix.zero_apply]
  have hkey := Projection.sum_starProjection_eq_one_of_orthogonal
    (fun i => (𝒲.subspace i).map (toEuclideanLin A)) horth'
    (by rw [hdim, finrank_euclideanSpace_fin])
  refine toEuclideanLin.injective ?_
  rw [map_sum, toEuclideanLin_one]
  simp only [fun i => leastSquares_P_i_eq_starProjection (𝒲 := 𝒲) (A := A) (i := i) (h i)]
  rw [← ContinuousLinearMap.toLinearMap_sum, hkey]
  rfl

end Family

end SaadSparse.Chapter05

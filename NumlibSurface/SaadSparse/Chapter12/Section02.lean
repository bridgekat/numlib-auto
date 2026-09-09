import Numlib.LinearSolve.DomainDecomposition.Schwarz
import Numlib.LinearSolve.Multigrid.Basic
import Numlib.LinearSolve.Projection.Additive
import NumlibSurface.SaadSparse.Common

/-!
# Saad §12.2: overlapping block-Jacobi preconditioners

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §12.2.

The section takes index sets `S_1, …, S_p` that *overlap* and runs block Jacobi on them: with
`V_i = [e_j : j ∈ S_i]` and `A_i = V_iᵀ A V_i`, one step with relaxation weights `ω_i` is

`x_{k+1} = x_k + ∑ ω_i V_i A_i⁻¹ V_iᵀ r_k`,   `r_k = b - A x_k`,

and the residual it produces is `r_{k+1} = [I - ∑ ω_i A V_i A_i⁻¹ V_iᵀ] r_k`.

Saad's `V_i` here is the transpose of the boolean restriction `R_i` that §14.3.1 will write, and
`V_i A_i⁻¹ V_iᵀ` is the subdomain solve `T_i` of (14.31): §12.2 and §14.3.3 are the *same*
operator, and the book says so in §14.3.3.  This is the first of the two places, so the vocabulary
is named here — `restrictSubset` for the boolean matrix, `subdomainSpace` for `K_i = span{V_i}`,
`localMatrix` for `A_i = V_iᵀ A V_i`, `subdomainInverse` for `V_i A_i⁻¹ V_iᵀ` and
`subdomainProjector` for `A`-orthogonal projector onto `K_i` — and §14.3 opens this namespace
rather than naming them again.  What §12.2 adds on top are the weights, which §14.3.3 does not
carry.

* `blockJacobiStep` is the weighted step, `pairStep_eq` identifies one block correction with the
  Petrov–Galerkin step of the backbone's `Projection.pairStep` on the pair
  `(span {e_j : j ∈ S_i}, span {e_j : j ∈ S_i})`, and `blockJacobiStep_eq_additiveStep` says that
  the whole step is `Projection.additiveStep`.
* `equation_12_1` is the residual identity, a specialization of
  `Projection.residual_additiveStep`.

Saad also mentions weighting by a *nonnegative diagonal matrix* `D_i` instead of a scalar `ω_i`;
the identity he states is the scalar one, and that is what is proved here.  The subdomain solves
need `A_i` nonsingular, which the section supplies by assuming `A` positive definite
(`posDef_localMatrix`).
-/

open Matrix

open scoped ComplexOrder SaadSparse

namespace SaadSparse.Chapter12

section Subdomains

variable {n : ℕ}

/-! ### §12.2: the restriction matrices and the subdomain spaces

Saad writes `V_i = [e_{l_i}, …, e_{r_i}]` here and `R_i = V_iᵀ` in §14.3.1; the boolean matrix is
named for the later notation, since that is the one the convergence theory of §14.3 is written in,
but it is defined here, where the book introduces it. -/

/-- **Saad §12.2**: the boolean matrix of an index set `S ⊆ {1, …, n}`, Saad's `V_S = [e_j : j ∈ S]`
read as its transpose, whose rows are the `e_jᵀ` for `j ∈ S`.  `R_S x` is the sub-vector of `x`
indexed by `S`, and `R_Sᵀ y = V_S y` extends a vector on `S` by zero.  §14.3.1 calls it `R_i`. -/
def restrictSubset (𝕜 : Type*) [RCLike 𝕜] (S : Finset (Fin n)) : Matrix ↥S (Fin n) 𝕜 :=
  Matrix.of fun i j => if (i : Fin n) = j then 1 else 0

/-- **Saad §12.2**: the subspace `K_S = span{V_S} = Ran(R_Sᵀ) = span {e_j : j ∈ S}` of the vectors
supported on `S`, which is the subspace the additive projection process projects onto, and on which
the subdomain problem of the Schwarz procedure of §14.3 is solved. -/
def subdomainSpace (𝕜 : Type*) [RCLike 𝕜] (S : Finset (Fin n)) :
    Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n)) :=
  Submodule.span 𝕜 (Set.range fun j : ↥S => EuclideanSpace.single (j : Fin n) (1 : 𝕜))

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The entries of `R_S`, read off its definition. -/
theorem restrictSubset_apply (S : Finset (Fin n)) (i : ↥S) (j : Fin n) :
    restrictSubset 𝕜 S i j = if (i : Fin n) = j then 1 else 0 := rfl

/-- The rows of `R_S` are orthonormal: `R_S R_Sᵀ = I`.  In particular `R_Sᵀ` has full column
rank, which is what makes the local matrix `A_S` nonsingular. -/
theorem restrictSubset_mul_transpose (S : Finset (Fin n)) :
    restrictSubset 𝕜 S * (restrictSubset 𝕜 S)ᵀ = 1 := by
  ext i k
  rw [Matrix.mul_apply]
  simp only [restrictSubset_apply, Matrix.transpose_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (i : Fin n)]
  · have h : ((k : Fin n) = (i : Fin n)) ↔ i = k := by
      rw [Subtype.ext_iff]; exact eq_comm
    simp [h]
  · exact fun j _ hj => by rw [ite_eq_right (Ne.symm hj), zero_mul]
  · exact fun h => absurd (Finset.mem_univ (i : Fin n)) h

/-- The entries of `R_S` are `0` and `1`, so its conjugate transpose is its transpose: the
adjoint of the extension `R_Sᵀ` is the restriction `R_S`. -/
theorem conjTranspose_transpose_restrictSubset (S : Finset (Fin n)) :
    ((restrictSubset 𝕜 S)ᵀ)ᴴ = restrictSubset 𝕜 S := by
  ext i j
  rw [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  simp only [restrictSubset_apply]
  split_ifs <;> simp

/-- **Saad §12.2**: the range of the extension `V_S = R_Sᵀ` is `K_S = span {e_j : j ∈ S}`.  This is
the subspace the block correction lands in, and the one §14.3.1 poses the local problem on. -/
theorem range_restrictSubset_transpose (S : Finset (Fin n)) :
    LinearMap.range (Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ) = subdomainSpace 𝕜 S := by
  have hbasis : (⊤ : Submodule 𝕜 (EuclideanSpace 𝕜 ↥S))
      = Submodule.span 𝕜 (Set.range fun j : ↥S => EuclideanSpace.single j (1 : 𝕜)) := by
    have h := (EuclideanSpace.basisFun (ι := ↥S) (𝕜 := 𝕜)).toBasis.span_eq
    rw [← h]
    congr 1
    exact congrArg Set.range (funext fun j => by
      rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply])
  have happ : ∀ j : ↥S, Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ
      (EuclideanSpace.single j (1 : 𝕜)) = EuclideanSpace.single (j : Fin n) (1 : 𝕜) := by
    intro j
    have hcol : (restrictSubset 𝕜 S)ᵀ *ᵥ Pi.single j (1 : 𝕜)
        = Pi.single (j : Fin n) (1 : 𝕜) := by
      rw [Matrix.mulVec_single_one]
      funext k
      rw [Matrix.col_apply, Matrix.transpose_apply, restrictSubset_apply, Pi.single_apply]
      by_cases h : (j : Fin n) = k
      · simp [h]
      · simp [h, Ne.symm h]
    rw [Matrix.toLpLin_apply, PiLp.ofLp_single, hcol, PiLp.toLp_single]
  rw [LinearMap.range_eq_map, hbasis, Submodule.map_span, ← Set.range_comp, subdomainSpace]
  exact congrArg _ (congrArg Set.range (funext happ))

/-! ### §12.2: the local matrices and the subdomain projectors -/

variable {A : Matrix (Fin n) (Fin n) 𝕜}

/-- **Saad §12.2**: the local matrix `A_S = V_Sᵀ A V_S = R_S A R_Sᵀ`, the submatrix of `A` on the
rows and columns of `S`.  §14.3.1 calls it `A_i` too. -/
def localMatrix (A : Matrix (Fin n) (Fin n) 𝕜) (S : Finset (Fin n)) : Matrix ↥S ↥S 𝕜 :=
  restrictSubset 𝕜 S * A * (restrictSubset 𝕜 S)ᵀ

/-- **Saad §12.2**: the block correction `V_S A_S⁻¹ V_Sᵀ = R_Sᵀ A_S⁻¹ R_S`, which restricts a
residual to `S`, solves the local system there, and extends the correction by zero.  It is the
subdomain solve `T_i` of (14.31). -/
noncomputable def subdomainInverse (A : Matrix (Fin n) (Fin n) 𝕜) (S : Finset (Fin n)) :
    Matrix (Fin n) (Fin n) 𝕜 :=
  (restrictSubset 𝕜 S)ᵀ * (localMatrix A S)⁻¹ * restrictSubset 𝕜 S

/-- The subdomain projector `P_S = R_Sᵀ A_S⁻¹ R_S A = T_S A`, which is `P_i` of (14.24). -/
noncomputable def subdomainProjector (A : Matrix (Fin n) (Fin n) 𝕜) (S : Finset (Fin n)) :
    Matrix (Fin n) (Fin n) 𝕜 :=
  subdomainInverse A S * A

/-- `P_S = T_S A`, that is (14.24) written through (14.31). -/
theorem subdomainProjector_eq_mul (A : Matrix (Fin n) (Fin n) 𝕜) (S : Finset (Fin n)) :
    subdomainProjector A S = subdomainInverse A S * A := rfl

/-- `(I - M) z = z - M z`: unfolding a projector complement one application at a time, which is
what every error recurrence of the section needs. -/
theorem toEuclideanLin_one_sub_apply (M : Matrix (Fin n) (Fin n) 𝕜)
    (z : EuclideanSpace 𝕜 (Fin n)) : ((1 - M) ⬝ z) = z - (M ⬝ z) := by
  have hmat : Matrix.toEuclideanLin (1 - M)
      = (LinearMap.id : EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n))
        - Matrix.toEuclideanLin M := by
    rw [map_sub, Matrix.toLpLin_one]
  rw [hmat, LinearMap.sub_apply, LinearMap.id_apply]

/-- A symmetric positive definite matrix is a symmetric coercive operator; this is the hypothesis
under which the `A`-orthogonal projector below, and the energy inner product `(x, y)_A` of §14.3.4,
exist. -/
theorem isSymmetricCoercive_toEuclideanLin (hA : A.PosDef) :
    (Matrix.toEuclideanLin A).IsSymmetricCoercive :=
  (Matrix.posDef_iff_isSymmetricCoercive A).1 hA

/-- The adjoint of the extension `R_Sᵀ` is the restriction `R_S`. -/
theorem adjoint_toEuclideanLin_transpose (S : Finset (Fin n)) :
    LinearMap.adjoint (Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ)
      = Matrix.toEuclideanLin (restrictSubset 𝕜 S) := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, conjTranspose_transpose_restrictSubset]

/-- The extension `R_Sᵀ` is injective, since `R_S R_Sᵀ = I`. -/
theorem injective_toEuclideanLin_transpose (S : Finset (Fin n)) :
    Function.Injective (Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ) := by
  have h : Matrix.toEuclideanLin (restrictSubset 𝕜 S) ∘ₗ
      Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ = LinearMap.id := by
    rw [← Matrix.toLpLin_mul_same, restrictSubset_mul_transpose, Matrix.toLpLin_one]
  exact Function.LeftInverse.injective (g := Matrix.toEuclideanLin (restrictSubset 𝕜 S))
    fun x => DFunLike.congr_fun h x

/-- The local matrix `A_S = R_S A R_Sᵀ` is the Galerkin coarse operator of the extension `R_Sᵀ`:
this is the sentence that makes the whole section a specialization of the abstract theory. -/
theorem galerkinCoarse_eq (A : Matrix (Fin n) (Fin n) 𝕜) (S : Finset (Fin n)) :
    Multigrid.galerkinCoarse (Matrix.toEuclideanLin A)
        (Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ)
      = Matrix.toEuclideanLin (localMatrix A S) := by
  have hdef : Multigrid.galerkinCoarse (Matrix.toEuclideanLin A)
      (Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ)
        = LinearMap.adjoint (Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ) ∘ₗ
            Matrix.toEuclideanLin A ∘ₗ Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ := rfl
  rw [hdef, adjoint_toEuclideanLin_transpose, localMatrix, Matrix.toLpLin_mul_same,
    Matrix.toLpLin_mul_same, LinearMap.comp_assoc]

/-- **The local problem is well posed**: for symmetric positive definite `A` the local matrix
`A_S` is symmetric positive definite, so the `A_S⁻¹` of the block correction makes sense. -/
theorem posDef_localMatrix (hA : A.PosDef) (S : Finset (Fin n)) : (localMatrix A S).PosDef := by
  rw [Matrix.posDef_iff_isSymmetricCoercive, ← galerkinCoarse_eq]
  exact Multigrid.galerkinCoarse_isSymmetricCoercive (isSymmetricCoercive_toEuclideanLin hA)
    (injective_toEuclideanLin_transpose S)

/-- The subspace argument of `Schwarz.energyProjection` may be rewritten. -/
private theorem energyProjection_congr {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {T : E →ₗ[𝕜] E} (hT : T.IsSymmetricCoercive)
    {K L : Submodule 𝕜 E} [FiniteDimensional 𝕜 K] [FiniteDimensional 𝕜 L] (h : K = L) :
    Schwarz.energyProjection T hT K = Schwarz.energyProjection T hT L := by
  subst h; rfl

/-- **The key identification**: the subdomain projector `P_S = R_Sᵀ A_S⁻¹ R_S A` is the
`A`-orthogonal projector onto the subdomain space `span {e_j : j ∈ S}`.  Everything §12.2 and
§14.3 prove follows from it and the abstract Schwarz theory; it is (14.24) when read in §14.3. -/
theorem subdomainProjector_eq_energyProjection (hA : A.PosDef) (S : Finset (Fin n)) :
    Matrix.toEuclideanLin (subdomainProjector A S)
      = Schwarz.energyProjection (Matrix.toEuclideanLin A)
          (isSymmetricCoercive_toEuclideanLin hA) (subdomainSpace 𝕜 S) := by
  have hinv : localMatrix A S * (localMatrix A S)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (posDef_localMatrix hA S).isUnit)
  refine LinearMap.ext fun x => ?_
  have hy : Multigrid.galerkinCoarse (Matrix.toEuclideanLin A)
      (Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ)
      (Matrix.toEuclideanLin ((localMatrix A S)⁻¹ * restrictSubset 𝕜 S * A) x)
        = LinearMap.adjoint (Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ)
            (Matrix.toEuclideanLin A x) := by
    rw [galerkinCoarse_eq, adjoint_toEuclideanLin_transpose, ← LinearMap.comp_apply,
      ← Matrix.toLpLin_mul_same, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hinv, Matrix.one_mul,
      Matrix.toLpLin_mul_same]
    rfl
  have hproj := Schwarz.energyProjection_eq_of_galerkinCoarse (Matrix.toEuclideanLin A)
    (isSymmetricCoercive_toEuclideanLin hA) (Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ) hy
  rw [energyProjection_congr (isSymmetricCoercive_toEuclideanLin hA)
    (range_restrictSubset_transpose (𝕜 := 𝕜) S).symm, hproj, ← LinearMap.comp_apply,
    ← Matrix.toLpLin_mul_same]
  rw [subdomainProjector, subdomainInverse, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]

/-- Saad's computation that `P_S² = P_S`: the subdomain projector is idempotent. -/
theorem subdomainProjector_mul_self (hA : A.PosDef) (S : Finset (Fin n)) :
    subdomainProjector A S * subdomainProjector A S = subdomainProjector A S := by
  refine (Matrix.toEuclideanLin (𝕜 := 𝕜)).injective ?_
  rw [Matrix.toLpLin_mul_same, subdomainProjector_eq_energyProjection hA S]
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply]
  exact Schwarz.energyProjection_apply_of_mem (Matrix.toEuclideanLin A)
    (isSymmetricCoercive_toEuclideanLin hA) (subdomainSpace 𝕜 S)
    (Schwarz.energyProjection_apply_mem (Matrix.toEuclideanLin A)
      (isSymmetricCoercive_toEuclideanLin hA) (subdomainSpace 𝕜 S) x)

end Subdomains

section BlockJacobi

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι]
variable {A : Matrix (Fin n) (Fin n) 𝕜}

/-- **§12.2**, one weighted step of the overlapping block-Jacobi iteration:
`x_{k+1} = x_k + ∑ ω_i V_i A_i⁻¹ V_iᵀ r_k`, all the corrections being computed from the same
iterate and added at once.  With `ω = 1` this is the additive
Schwarz procedure of §14.3.3. -/
noncomputable def blockJacobiStep (A : Matrix (Fin n) (Fin n) 𝕜) (S : ι → Finset (Fin n))
    (ω : ι → 𝕜) (b x : EuclideanSpace 𝕜 (Fin n)) : EuclideanSpace 𝕜 (Fin n) :=
  x + ∑ i, ω i • (subdomainInverse A (S i) ⬝ (b - (A ⬝ x)))

/-- The block-Jacobi step, unfolded. -/
theorem blockJacobiStep_def (A : Matrix (Fin n) (Fin n) 𝕜) (S : ι → Finset (Fin n)) (ω : ι → 𝕜)
    (b x : EuclideanSpace 𝕜 (Fin n)) :
    blockJacobiStep A S ω b x
      = x + ∑ i, ω i • (subdomainInverse A (S i) ⬝ (b - (A ⬝ x))) := rfl

/-- The Galerkin pairs of §12.2: for a positive definite `A`, each coordinate subspace
`span {e_j : j ∈ S}` is a nondegenerate Petrov–Galerkin pair with itself, which is what makes the
projection processes of the backbone available here. -/
theorem isNondegeneratePair_subdomainSpace (hA : A.PosDef) (S : Finset (Fin n)) :
    Projection.IsNondegeneratePair (Matrix.toEuclideanLin A) (subdomainSpace 𝕜 S)
      (subdomainSpace 𝕜 S) :=
  Schwarz.isNondegeneratePair_self (isSymmetricCoercive_toEuclideanLin hA) _

/-- **One block correction is one Galerkin step.** The correction `V_i A_i⁻¹ V_iᵀ r` of (12.1) is
exactly the Petrov–Galerkin step of the backbone on the pair `(K_i, K_i)` with
`K_i = span {e_j : j ∈ S_i}`: it lands in `K_i` and leaves a residual orthogonal to `K_i`.  This is
what makes §12.2 an instance of the additive projection process of §5.4. -/
theorem pairStep_eq (hA : A.PosDef) (S : Finset (Fin n)) (b x : EuclideanSpace 𝕜 (Fin n)) :
    Projection.pairStep (Matrix.toEuclideanLin A) b (subdomainSpace 𝕜 S)
        (subdomainSpace 𝕜 S) (isNondegeneratePair_subdomainSpace hA S) x
      = x + (subdomainInverse A S ⬝ (b - (A ⬝ x))) := by
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hA.isUnit
  have hstar : Matrix.toEuclideanLin A (A⁻¹ ⬝ b) = b := by
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, Matrix.mul_nonsing_inv A hAdet,
      Matrix.toLpLin_one, LinearMap.id_apply]
  have hcorr : (subdomainProjector A S ⬝ ((A⁻¹ ⬝ b) - x))
      = (subdomainInverse A S ⬝ (b - (A ⬝ x))) := by
    rw [subdomainProjector, Matrix.toLpLin_mul_same, LinearMap.comp_apply, map_sub,
      hstar]
  have hgal : IsGalerkin (Matrix.toEuclideanLin A) b x (subdomainSpace 𝕜 S)
      (x + (subdomainInverse A S ⬝ (b - (A ⬝ x)))) := by
    rw [← hcorr, subdomainProjector_eq_energyProjection hA S]
    exact Schwarz.energyProjection_isGalerkin _ _ _ hstar
  exact (Projection.pairStep_isPetrovGalerkin (isNondegeneratePair_subdomainSpace hA S)
    x).eq_of_forall hgal (isNondegeneratePair_subdomainSpace hA S).eq_zero_of_mem_orthogonal

/-- **§12.2 is the additive projection process of §5.4**: the weighted overlapping block-Jacobi
step is `Projection.additiveStep` on the family of coordinate subspaces
`K_i = span {e_j : j ∈ S_i}`. -/
theorem blockJacobiStep_eq_additiveStep (hA : A.PosDef) (S : ι → Finset (Fin n)) (ω : ι → 𝕜)
    (b x : EuclideanSpace 𝕜 (Fin n)) :
    blockJacobiStep A S ω b x
      = Projection.additiveStep (Matrix.toEuclideanLin A) b
          (fun i => subdomainSpace 𝕜 (S i))
          (fun i => subdomainSpace 𝕜 (S i))
          (fun i => isNondegeneratePair_subdomainSpace hA (S i)) ω x := by
  have hdef : Projection.additiveStep (Matrix.toEuclideanLin A) b
      (fun i => subdomainSpace 𝕜 (S i)) (fun i => subdomainSpace 𝕜 (S i))
      (fun i => isNondegeneratePair_subdomainSpace hA (S i)) ω x
        = x + ∑ i, ω i • (Projection.pairStep (Matrix.toEuclideanLin A) b
            (subdomainSpace 𝕜 (S i)) (subdomainSpace 𝕜 (S i))
            (isNondegeneratePair_subdomainSpace hA (S i)) x - x) := rfl
  rw [hdef, blockJacobiStep_def]
  exact congrArg _ (Finset.sum_congr rfl fun i _ => by
    rw [pairStep_eq hA (S i) b x, add_sub_cancel_left])

omit [Fintype ι] in
/-- The projector `P_i` of the pair `(K_i, K_i)` is Saad's `A V_i A_i⁻¹ V_iᵀ = A T_i`. -/
theorem additiveProjector_eq (hA : A.PosDef) (S : ι → Finset (Fin n)) (i : ι) :
    Projection.additiveProjector (Matrix.toEuclideanLin A)
        (fun i => subdomainSpace 𝕜 (S i)) (fun i => subdomainSpace 𝕜 (S i))
        (fun i => isNondegeneratePair_subdomainSpace hA (S i)) i
      = Matrix.toEuclideanLin (A * subdomainInverse A (S i)) := by
  refine LinearMap.ext fun r => ?_
  have hstep := Projection.apply_pairStep_sub (A := Matrix.toEuclideanLin A) (b := r)
    (K := subdomainSpace 𝕜 (S i)) (L := subdomainSpace 𝕜 (S i))
    (isNondegeneratePair_subdomainSpace hA (S i)) 0
  rw [pairStep_eq hA (S i) r 0] at hstep
  simp only [map_zero, sub_zero, zero_add] at hstep
  rw [show Projection.additiveProjector (Matrix.toEuclideanLin A)
      (fun i => subdomainSpace 𝕜 (S i)) (fun i => subdomainSpace 𝕜 (S i))
      (fun i => isNondegeneratePair_subdomainSpace hA (S i)) i
        = Projection.pairProjector (Matrix.toEuclideanLin A) (subdomainSpace 𝕜 (S i))
            (subdomainSpace 𝕜 (S i)) (isNondegeneratePair_subdomainSpace hA (S i)) from
      rfl, ← hstep, ← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same]

/-- **§12.2, the residual of an overlapping block-Jacobi step**:
`r_{k+1} = [I - ∑ ω_i A V_i (V_iᵀ A V_i)⁻¹ V_iᵀ] r_k`, with `V_i = R_iᵀ` and
`V_i (V_iᵀ A V_i)⁻¹ V_iᵀ = T_i` the subdomain solve of (14.31).  This is
`Projection.residual_additiveStep` — Saad's (5.22)–(5.23) — with `K_i = L_i` the coordinate
subspace of `S_i`. -/
theorem equation_12_1 (hA : A.PosDef) (S : ι → Finset (Fin n)) (ω : ι → 𝕜)
    (b x : EuclideanSpace 𝕜 (Fin n)) :
    b - (A ⬝ blockJacobiStep A S ω b x)
      = ((1 - ∑ i, ω i • (A * subdomainInverse A (S i))) ⬝ (b - (A ⬝ x))) := by
  have hmat : Matrix.toEuclideanLin
      (1 - ∑ i, ω i • (A * subdomainInverse A (S i)))
        = 1 - ∑ i, ω i • Projection.additiveProjector (Matrix.toEuclideanLin A)
            (fun i => subdomainSpace 𝕜 (S i))
            (fun i => subdomainSpace 𝕜 (S i))
            (fun i => isNondegeneratePair_subdomainSpace hA (S i)) i := by
    simp only [additiveProjector_eq hA S, map_sub, map_sum, map_smul, Matrix.toLpLin_one]
    rfl
  rw [blockJacobiStep_eq_additiveStep hA S ω b x, Projection.residual_additiveStep, hmat]

end BlockJacobi

end SaadSparse.Chapter12

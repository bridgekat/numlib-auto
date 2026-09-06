import NumlibSurface.SaadSparse.Chapter14.Section03

/-!
# Saad §12.2: overlapping block-Jacobi preconditioners

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §12.2.

The section takes index sets `S_1, …, S_p` that *overlap* and runs block Jacobi on them: with
`V_i = [e_j : j ∈ S_i]` and `A_i = V_iᵀ A V_i`, one step with relaxation weights `ω_i` is

`x_{k+1} = x_k + ∑ ω_i V_i A_i⁻¹ V_iᵀ r_k`,   `r_k = b - A x_k`,

and the residual it produces is `r_{k+1} = [I - ∑ ω_i A V_i A_i⁻¹ V_iᵀ] r_k`.

Saad's `V_i` is the transpose of the boolean restriction `R_i` of §14.3.1, and `V_i A_i⁻¹ V_iᵀ` is
the subdomain solve `T_i` of (14.31): §12.2 and §14.3.3 are the *same* operator, and the book says
so in §14.3.3.  So this file reuses `SaadSparse.Chapter14.restrictSubset`,
`SaadSparse.Chapter14.localMatrix` and `SaadSparse.Chapter14.subdomainInverse` rather than naming
them again, and adds only the weights, which §14.3.3 does not carry.

* `blockJacobiStep` is the weighted step, `pairStep_eq` identifies one block correction with the
  Petrov–Galerkin step of the backbone's `Projection.pairStep` on the pair
  `(span {e_j : j ∈ S_i}, span {e_j : j ∈ S_i})`, and `blockJacobiStep_eq_additiveStep` says that
  the whole step is `Projection.additiveStep`.
* `equation_12_1` is the residual identity, a specialization of
  `Projection.residual_additiveStep`.

Saad also mentions weighting by a *nonnegative diagonal matrix* `D_i` instead of a scalar `ω_i`;
the identity he states is the scalar one, and that is what is proved here.  The subdomain solves
need `A_i` nonsingular, which the section supplies by assuming `A` positive definite
(`SaadSparse.Chapter14.posDef_localMatrix`).
-/

open Matrix

open scoped ComplexOrder SaadSparse

namespace SaadSparse.Chapter12

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι]
variable {A : Matrix (Fin n) (Fin n) 𝕜}

/-- **§12.2**, one weighted step of the overlapping block-Jacobi iteration:
`x_{k+1} = x_k + ∑ ω_i V_i A_i⁻¹ V_iᵀ r_k`, all the corrections being computed from the same
iterate and added at once.  With `ω = 1` this is `SaadSparse.Chapter14.additiveSweep`, the additive
Schwarz procedure of §14.3.3. -/
noncomputable def blockJacobiStep (A : Matrix (Fin n) (Fin n) 𝕜) (S : ι → Finset (Fin n))
    (ω : ι → 𝕜) (b x : EuclideanSpace 𝕜 (Fin n)) : EuclideanSpace 𝕜 (Fin n) :=
  x + ∑ i, ω i • (Chapter14.subdomainInverse A (S i) ⬝ (b - (A ⬝ x)))

/-- The block-Jacobi step, unfolded. -/
theorem blockJacobiStep_def (A : Matrix (Fin n) (Fin n) 𝕜) (S : ι → Finset (Fin n)) (ω : ι → 𝕜)
    (b x : EuclideanSpace 𝕜 (Fin n)) :
    blockJacobiStep A S ω b x
      = x + ∑ i, ω i • (Chapter14.subdomainInverse A (S i) ⬝ (b - (A ⬝ x))) := rfl

/-- The Galerkin pairs of §12.2: for a positive definite `A`, each coordinate subspace
`span {e_j : j ∈ S}` is a nondegenerate Petrov–Galerkin pair with itself, which is what makes the
projection processes of the backbone available here. -/
theorem isNondegeneratePair_subdomainSpace (hA : A.PosDef) (S : Finset (Fin n)) :
    Projection.IsNondegeneratePair (Matrix.toEuclideanLin A) (Chapter14.subdomainSpace 𝕜 S)
      (Chapter14.subdomainSpace 𝕜 S) :=
  Schwarz.isNondegeneratePair_self (Chapter14.isSymmetricCoercive_toEuclideanLin hA) _

/-- **One block correction is one Galerkin step.** The correction `V_i A_i⁻¹ V_iᵀ r` of (12.1) is
exactly the Petrov–Galerkin step of the backbone on the pair `(K_i, K_i)` with
`K_i = span {e_j : j ∈ S_i}`: it lands in `K_i` and leaves a residual orthogonal to `K_i`.  This is
what makes §12.2 an instance of the additive projection process of §5.4. -/
theorem pairStep_eq (hA : A.PosDef) (S : Finset (Fin n)) (b x : EuclideanSpace 𝕜 (Fin n)) :
    Projection.pairStep (Matrix.toEuclideanLin A) b (Chapter14.subdomainSpace 𝕜 S)
        (Chapter14.subdomainSpace 𝕜 S) (isNondegeneratePair_subdomainSpace hA S) x
      = x + (Chapter14.subdomainInverse A S ⬝ (b - (A ⬝ x))) := by
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hA.isUnit
  have hstar : Matrix.toEuclideanLin A (A⁻¹ ⬝ b) = b := by
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, Matrix.mul_nonsing_inv A hAdet,
      Matrix.toLpLin_one, LinearMap.id_apply]
  have hcorr : (Chapter14.subdomainProjector A S ⬝ ((A⁻¹ ⬝ b) - x))
      = (Chapter14.subdomainInverse A S ⬝ (b - (A ⬝ x))) := by
    rw [Chapter14.subdomainProjector, Matrix.toLpLin_mul_same, LinearMap.comp_apply, map_sub,
      hstar]
  have hgal : IsGalerkin (Matrix.toEuclideanLin A) b x (Chapter14.subdomainSpace 𝕜 S)
      (x + (Chapter14.subdomainInverse A S ⬝ (b - (A ⬝ x)))) := by
    rw [← hcorr, Chapter14.subdomainProjector_eq_energyProjection hA S]
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
          (fun i => Chapter14.subdomainSpace 𝕜 (S i))
          (fun i => Chapter14.subdomainSpace 𝕜 (S i))
          (fun i => isNondegeneratePair_subdomainSpace hA (S i)) ω x := by
  have hdef : Projection.additiveStep (Matrix.toEuclideanLin A) b
      (fun i => Chapter14.subdomainSpace 𝕜 (S i)) (fun i => Chapter14.subdomainSpace 𝕜 (S i))
      (fun i => isNondegeneratePair_subdomainSpace hA (S i)) ω x
        = x + ∑ i, ω i • (Projection.pairStep (Matrix.toEuclideanLin A) b
            (Chapter14.subdomainSpace 𝕜 (S i)) (Chapter14.subdomainSpace 𝕜 (S i))
            (isNondegeneratePair_subdomainSpace hA (S i)) x - x) := rfl
  rw [hdef, blockJacobiStep_def]
  exact congrArg _ (Finset.sum_congr rfl fun i _ => by
    rw [pairStep_eq hA (S i) b x, add_sub_cancel_left])

omit [Fintype ι] in
/-- The projector `P_i` of the pair `(K_i, K_i)` is Saad's `A V_i A_i⁻¹ V_iᵀ = A T_i`. -/
theorem additiveProjector_eq (hA : A.PosDef) (S : ι → Finset (Fin n)) (i : ι) :
    Projection.additiveProjector (Matrix.toEuclideanLin A)
        (fun i => Chapter14.subdomainSpace 𝕜 (S i)) (fun i => Chapter14.subdomainSpace 𝕜 (S i))
        (fun i => isNondegeneratePair_subdomainSpace hA (S i)) i
      = Matrix.toEuclideanLin (A * Chapter14.subdomainInverse A (S i)) := by
  refine LinearMap.ext fun r => ?_
  have hstep := Projection.apply_pairStep_sub (A := Matrix.toEuclideanLin A) (b := r)
    (K := Chapter14.subdomainSpace 𝕜 (S i)) (L := Chapter14.subdomainSpace 𝕜 (S i))
    (isNondegeneratePair_subdomainSpace hA (S i)) 0
  rw [pairStep_eq hA (S i) r 0] at hstep
  simp only [map_zero, sub_zero, zero_add] at hstep
  rw [show Projection.additiveProjector (Matrix.toEuclideanLin A)
      (fun i => Chapter14.subdomainSpace 𝕜 (S i)) (fun i => Chapter14.subdomainSpace 𝕜 (S i))
      (fun i => isNondegeneratePair_subdomainSpace hA (S i)) i
        = Projection.pairProjector (Matrix.toEuclideanLin A) (Chapter14.subdomainSpace 𝕜 (S i))
            (Chapter14.subdomainSpace 𝕜 (S i)) (isNondegeneratePair_subdomainSpace hA (S i)) from
      rfl, ← hstep, ← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same]

/-- **§12.2, the residual of an overlapping block-Jacobi step**:
`r_{k+1} = [I - ∑ ω_i A V_i (V_iᵀ A V_i)⁻¹ V_iᵀ] r_k`, with `V_i = R_iᵀ` and
`V_i (V_iᵀ A V_i)⁻¹ V_iᵀ = T_i` the subdomain solve of (14.31).  This is
`Projection.residual_additiveStep` — Saad's (5.22)–(5.23) — with `K_i = L_i` the coordinate
subspace of `S_i`. -/
theorem equation_12_1 (hA : A.PosDef) (S : ι → Finset (Fin n)) (ω : ι → 𝕜)
    (b x : EuclideanSpace 𝕜 (Fin n)) :
    b - (A ⬝ blockJacobiStep A S ω b x)
      = ((1 - ∑ i, ω i • (A * Chapter14.subdomainInverse A (S i))) ⬝ (b - (A ⬝ x))) := by
  have hmat : Matrix.toEuclideanLin
      (1 - ∑ i, ω i • (A * Chapter14.subdomainInverse A (S i)))
        = 1 - ∑ i, ω i • Projection.additiveProjector (Matrix.toEuclideanLin A)
            (fun i => Chapter14.subdomainSpace 𝕜 (S i))
            (fun i => Chapter14.subdomainSpace 𝕜 (S i))
            (fun i => isNondegeneratePair_subdomainSpace hA (S i)) i := by
    simp only [additiveProjector_eq hA S, map_sub, map_sum, map_smul, Matrix.toLpLin_one]
    rfl
  rw [blockJacobiStep_eq_additiveStep hA S ω b x, Projection.residual_additiveStep, hmat]

end SaadSparse.Chapter12

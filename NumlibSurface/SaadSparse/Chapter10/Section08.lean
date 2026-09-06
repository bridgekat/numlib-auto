import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import NumlibSurface.SaadSparse.Common

/-!
# Saad, §10.8: preconditioners for the normal equations

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
SIAM, 2003, §10.8.

**Algorithm 10.17**, the incomplete Gram–Schmidt process of §10.8.3, is `imgsHat` (the vector
`q̂_i` of line 3), `imgsQ` (its normalization `q_i` of line 5) and `imgsL` (the coefficients
`l_{ij}`), assembled into the matrices `imgsLMat` and `imgsQMat`. The dropping rule of line 6 is
a predicate `dropL : ℕ → ℕ → Bool`, the book's set `P_L`: `dropL i j = true` discards the entry
`l_{ij}`. No dropping is applied to `Q`, which is the hypothesis `P_Q = ∅` of Proposition 10.17.

The point of the algorithm is that dropping in `L` alone costs nothing in exactness: the vector
subtracted on line 3 is built from the *retained* coefficients, so `a_i = ∑_{j ≤ i} l_{ij} q_j`
holds however much is dropped (`rowVec_eq_sum`), and `A = L Q` is an exact factorization
(`imgsLMat_mul_imgsQMat`). What is lost is the orthogonality of `Q`.

§10.8.1 (CGNE/SSOR and CGNR/SSOR) constructs no new object: it is the normal equations of
`Numlib/Krylov/NormalEquations` preconditioned by the SSOR splitting of `A Aᵀ` or `Aᵀ A`, and its
only claim — that the methods do not break down, because `Aᵀ A` and `A Aᵀ` are positive definite
for a nonsingular `A` — is `Krylov.adjoint_comp_isSymmetricCoercive`. §10.8.2 (shifted IC(0)) is
an algorithm with an empirical discussion of the shift and no theorem. Theorem 10.18 Saad states
without proof, citing the literature.

Indices are `0`-based: `imgsQ A dropL j` is the book's `q_{j+1}`, and the rows are indexed by `ℕ`
and padded by `0` past `n`, so that the recursion of Algorithm 10.17 needs no dependent
arithmetic.
-/

namespace SaadSparse.Ch10

section IncompleteGramSchmidt

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-- The `i`-th row `a_i` of `A` as a vector of `𝕜ⁿ`, padded by `0` past `n`. -/
noncomputable def rowVec (A : Matrix (Fin n) (Fin n) 𝕜) (i : ℕ) : EuclideanSpace 𝕜 (Fin n) :=
  if h : i < n then WithLp.toLp 2 (A ⟨i, h⟩) else 0

@[simp]
theorem rowVec_coe (A : Matrix (Fin n) (Fin n) 𝕜) (i : Fin n) :
    rowVec A (i : ℕ) = WithLp.toLp 2 (A i) := by
  simp [rowVec, i.isLt]

/-- One term of the sum on line 3 of **Algorithm 10.17**: the retained multiple of the normalized
`q_j` that is subtracted from the row `a_i`. Splitting it out of `imgsHat` keeps the recursion to
a single recursive call. -/
private noncomputable def imgsTerm (A : Matrix (Fin n) (Fin n) 𝕜) (dropL : ℕ → ℕ → Bool)
    (i j : ℕ) (qhat : EuclideanSpace 𝕜 (Fin n)) : EuclideanSpace 𝕜 (Fin n) :=
  (if dropL i j then 0
    else inner 𝕜 (((‖qhat‖ : 𝕜))⁻¹ • qhat) (rowVec A i)) • ((‖qhat‖ : 𝕜))⁻¹ • qhat

/-- **Algorithm 10.17**, lines 2–3: the unnormalized vector
`q̂_i = a_i - ∑_{j < i} l_{ij} q_j`, where the sum runs over the coefficients the dropping rule
`dropL` retains. -/
noncomputable def imgsHat (A : Matrix (Fin n) (Fin n) 𝕜) (dropL : ℕ → ℕ → Bool) :
    ℕ → EuclideanSpace 𝕜 (Fin n)
  | i => rowVec A i - ∑ j : Finset.range i, imgsTerm A dropL i j (imgsHat A dropL j)
  decreasing_by exact Finset.mem_range.1 j.2

/-- **Algorithm 10.17**, line 5: the normalized vector `q_i = q̂_i / l_{ii}`. The book's "if
`l_{ii} = 0` then Stop" is Lean's `x / 0 = 0`, which makes `q_i = 0` at a breakdown. -/
noncomputable def imgsQ (A : Matrix (Fin n) (Fin n) 𝕜) (dropL : ℕ → ℕ → Bool) (i : ℕ) :
    EuclideanSpace 𝕜 (Fin n) :=
  ((‖imgsHat A dropL i‖ : 𝕜))⁻¹ • imgsHat A dropL i

/-- **Algorithm 10.17**, lines 2 and 4: the coefficient `l_{ij}`, which is `(a_i, q_j)` below the
diagonal unless the dropping rule discards it, `‖q̂_i‖₂` on the diagonal, and `0` above it. -/
noncomputable def imgsL (A : Matrix (Fin n) (Fin n) 𝕜) (dropL : ℕ → ℕ → Bool) (i j : ℕ) : 𝕜 :=
  if j < i then (if dropL i j then 0 else inner 𝕜 (imgsQ A dropL j) (rowVec A i))
  else if j = i then ((‖imgsHat A dropL i‖ : ℝ) : 𝕜)
  else 0

/-- The lower triangular factor `L` of Algorithm 10.17. -/
noncomputable def imgsLMat (A : Matrix (Fin n) (Fin n) 𝕜) (dropL : ℕ → ℕ → Bool) :
    Matrix (Fin n) (Fin n) 𝕜 :=
  Matrix.of fun i j => imgsL A dropL (i : ℕ) (j : ℕ)

/-- The factor `Q` of Algorithm 10.17, whose rows are the vectors `q_i`. It is not orthogonal,
because entries are dropped from `L`. -/
noncomputable def imgsQMat (A : Matrix (Fin n) (Fin n) 𝕜) (dropL : ℕ → ℕ → Bool) :
    Matrix (Fin n) (Fin n) 𝕜 :=
  Matrix.of fun i j => WithLp.ofLp (imgsQ A dropL (i : ℕ)) j

variable (A : Matrix (Fin n) (Fin n) 𝕜) (dropL : ℕ → ℕ → Bool)

@[simp]
theorem imgsLMat_apply (i j : Fin n) : imgsLMat A dropL i j = imgsL A dropL (i : ℕ) (j : ℕ) := rfl

@[simp]
theorem imgsQMat_apply (i j : Fin n) :
    imgsQMat A dropL i j = WithLp.ofLp (imgsQ A dropL (i : ℕ)) j := rfl

theorem imgsL_of_lt {i j : ℕ} (h : i < j) : imgsL A dropL i j = 0 := by
  have h1 : ¬(j < i) := by omega
  have h2 : ¬(j = i) := by omega
  simp [imgsL, h1, h2]

theorem imgsL_diag (i : ℕ) : imgsL A dropL i i = ((‖imgsHat A dropL i‖ : ℝ) : 𝕜) := by
  simp [imgsL]

/-- Below the diagonal, `l_{ij}` is `(a_i, q_j)` unless the dropping rule discards it. -/
theorem imgsL_of_gt {i j : ℕ} (h : j < i) :
    imgsL A dropL i j =
      if dropL i j then 0 else inner 𝕜 (imgsQ A dropL j) (rowVec A i) := by
  simp [imgsL, h]

/-- **Algorithm 10.17**, line 3, in terms of the coefficients it produces. -/
theorem imgsHat_eq (i : ℕ) :
    imgsHat A dropL i =
      rowVec A i - ∑ j ∈ Finset.range i, imgsL A dropL i j • imgsQ A dropL j := by
  rw [imgsHat, ← Finset.sum_coe_sort (Finset.range i)]
  refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
  rw [imgsTerm, imgsL_of_gt A dropL (Finset.mem_range.1 j.2)]
  rfl

/-- **Algorithm 10.17**, lines 3–5: `a_i = ∑_{j ≤ i} l_{ij} q_j`, exactly, however much is
dropped from `L`. This is why dropping in `L` alone still gives an exact factorization: the
subtracted vector on line 3 is built from the retained coefficients themselves. -/
theorem rowVec_eq_sum {i : ℕ} (h : imgsHat A dropL i ≠ 0) :
    rowVec A i = ∑ j ∈ Finset.range (i + 1), imgsL A dropL i j • imgsQ A dropL j := by
  have hnorm : ((‖imgsHat A dropL i‖ : ℝ) : 𝕜) ≠ 0 := by
    simpa using norm_ne_zero_iff.2 h
  rw [Finset.sum_range_succ, imgsL_diag, imgsQ, smul_smul, mul_inv_cancel₀ hnorm, one_smul,
    imgsHat_eq]
  abel

/-- Every vector of Algorithm 10.17 lies in the span of the rows that produced it. -/
theorem imgsHat_mem_span (i : ℕ) :
    imgsHat A dropL i ∈ Submodule.span 𝕜 (rowVec A '' Set.Iic i) := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rw [imgsHat_eq]
    refine Submodule.sub_mem _ (Submodule.subset_span ⟨i, Set.mem_Iic.2 le_rfl, rfl⟩)
      (Submodule.sum_mem _ ?_)
    intro j hj
    have hji : j < i := Finset.mem_range.1 hj
    refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_)
    exact Submodule.span_mono (Set.image_mono (Set.Iic_subset_Iic.2 hji.le)) (ih j hji)

/-- The rows of a nonsingular matrix, read as vectors of `𝕜ⁿ`, are linearly independent. -/
theorem linearIndependent_rowVec {A : Matrix (Fin n) (Fin n) 𝕜} (hA : IsUnit A) :
    LinearIndependent 𝕜 fun i : Fin n => rowVec A (i : ℕ) := by
  have hrows : LinearIndependent 𝕜 A.row := Matrix.linearIndependent_rows_iff_isUnit.2 hA
  have hmap := hrows.map' (WithLp.linearEquiv 2 𝕜 (Fin n → 𝕜)).symm.toLinearMap
    (LinearEquiv.ker _)
  have heq : (fun i : Fin n => rowVec A (i : ℕ)) =
      ⇑(WithLp.linearEquiv 2 𝕜 (Fin n → 𝕜)).symm.toLinearMap ∘ A.row := by
    funext i
    rw [rowVec_coe]
    rfl
  rw [heq]
  exact hmap

/-- **Proposition 10.17**. Let `A` be a nonsingular matrix and assume that no dropping is applied
to `Q`. Then the incomplete Gram–Schmidt algorithm 10.17 does not break down — every `l_{ii}` is
positive — and it computes an exact factorization `A = L Q`, in which `L` is lower triangular with
positive diagonal and `Q` is nonsingular, though not orthogonal.

The proof is Saad's: were `l_{ii} = 0`, line 3 would exhibit the `i`-th row of `A` as a
combination of the earlier ones, contradicting nonsingularity. -/
theorem proposition_10_17 {A : Matrix (Fin n) (Fin n) ℝ} (dropL : ℕ → ℕ → Bool)
    (hA : IsUnit A) :
    (∀ i : Fin n, 0 < imgsL A dropL (i : ℕ) (i : ℕ)) ∧
      (∀ i j : Fin n, (i : ℕ) < (j : ℕ) → imgsL A dropL (i : ℕ) (j : ℕ) = 0) ∧
      imgsLMat A dropL * imgsQMat A dropL = A ∧ IsUnit (imgsQMat A dropL) := by
  -- no breakdown: `q̂_i = 0` would make row `i` a combination of the earlier rows
  have hne : ∀ i : Fin n, imgsHat A dropL (i : ℕ) ≠ 0 := by
    intro i h0
    have hspan : rowVec A (i : ℕ) ∈
        Submodule.span ℝ ((fun j : Fin n => rowVec A (j : ℕ)) ''
          {j : Fin n | (j : ℕ) < (i : ℕ)}) := by
      have hsum : rowVec A (i : ℕ) =
          ∑ j ∈ Finset.range (i : ℕ), imgsL A dropL (i : ℕ) j • imgsQ A dropL j := by
        rw [imgsHat_eq] at h0
        rw [← sub_eq_zero]
        exact h0
      rw [hsum]
      refine Submodule.sum_mem _ fun j hj => ?_
      have hji : j < (i : ℕ) := Finset.mem_range.1 hj
      have hjn : j < n := hji.trans i.isLt
      refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_)
      refine Submodule.span_mono ?_ (imgsHat_mem_span A dropL j)
      rintro _ ⟨k, hk, rfl⟩
      exact ⟨⟨k, (hk.trans hji.le).trans_lt i.isLt⟩, lt_of_le_of_lt hk hji, rfl⟩
    exact (linearIndependent_rowVec hA).notMem_span_image (s := {j : Fin n | (j : ℕ) < (i : ℕ)})
      (by simp) hspan
  have hdiag : ∀ i : Fin n, 0 < imgsL A dropL (i : ℕ) (i : ℕ) := by
    intro i
    rw [imgsL_diag]
    simpa using norm_pos_iff.2 (hne i)
  have hlower : ∀ i j : Fin n, (i : ℕ) < (j : ℕ) → imgsL A dropL (i : ℕ) (j : ℕ) = 0 :=
    fun i j h => imgsL_of_lt A dropL h
  have hfac : imgsLMat A dropL * imgsQMat A dropL = A := by
    ext i k
    have hrow := congrArg (fun z : EuclideanSpace ℝ (Fin n) => WithLp.ofLp z k)
      (rowVec_eq_sum A dropL (hne i))
    simp only [rowVec_coe, WithLp.ofLp_toLp, WithLp.ofLp_sum, WithLp.ofLp_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hrow
    have hconv : ∑ j : Fin n, imgsLMat A dropL i j * imgsQMat A dropL j k
        = ∑ j ∈ Finset.range n,
            imgsL A dropL (i : ℕ) j * WithLp.ofLp (imgsQ A dropL j) k :=
      Fin.sum_univ_eq_sum_range
        (fun j => imgsL A dropL (i : ℕ) j * WithLp.ofLp (imgsQ A dropL j) k) n
    rw [Matrix.mul_apply, hconv, hrow]
    have hsub : Finset.range ((i : ℕ) + 1) ⊆ Finset.range n := fun j hj =>
      Finset.mem_range.2 (by have := Finset.mem_range.1 hj; have := i.isLt; omega)
    refine (Finset.sum_subset hsub fun j _ hj => ?_).symm
    rw [Finset.mem_range, not_lt] at hj
    rw [imgsL_of_lt A dropL (by omega), zero_mul]
  refine ⟨hdiag, hlower, hfac, ?_⟩
  -- `A = L Q` with `A` nonsingular forces `det Q ≠ 0`
  have hdetA : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hA
  rw [← hfac, Matrix.det_mul] at hdetA
  exact (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right hdetA)

end IncompleteGramSchmidt

end SaadSparse.Ch10

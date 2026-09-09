import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.LinearSolve.Preconditioner.ILU
import NumlibSurface.SaadSparse.Common

/-!
# Saad §10.8: preconditioners for the normal equations

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §10.8.

**Algorithm 10.17**, the incomplete Gram–Schmidt process of §10.8.3, is `imgsHat` (the vector
`q̂_i` of line 4), `imgsQ` (its normalization `q_i` of line 7) and `imgsL` (the coefficients
`l_{ij}` of lines 2 and 6), assembled into the matrices `imgsLMat` and `imgsQMat`. The dropping
rule of line 3 is a predicate `dropL : ℕ → ℕ → Bool`, the book's set `P_L`: `dropL i j = true`
discards the entry `l_{ij}`. No dropping is applied to `Q` — line 5 is not modelled — which is
the hypothesis `P_Q = ∅` of Proposition 10.17.

The point of the algorithm is that dropping in `L` alone costs nothing in exactness: the vector
subtracted on line 4 is built from the *retained* coefficients, so `a_i = ∑_{j ≤ i} l_{ij} q_j`
holds however much is dropped (`rowVec_eq_sum`, the book's (10.83) with `r_i = 0`), and
`A = L Q` is an exact factorization — the third clause of `proposition_10_17`, which is (10.84)
with `R = 0`. What is lost is the orthogonality of `Q`.

**Theorem 10.18** is `theorem_10_18`. Its hypothesis on `P_L` says that two coefficients retained
in one row of `L` link rows that are themselves linked; from that, the rows of `Q` retained in a
row of `L` are pairwise orthogonal (`inner_imgsQ_eq_zero`), the cross terms of `(a_i, a_j)`
disappear, and `L Lᵀ` agrees with `B = A Aᵀ` off the pattern. So `L` is an incomplete Cholesky
factor of `B` in the sense of `Matrix.IsIC` of `Numlib/LinearSolve/Preconditioner/ILU`, which was
added for this statement, and `Matrix.IsIC.eq_of_diag_pos` makes it *the* factor. Saad states the
theorem without proof, citing the literature; the proof here is the induction described at
`inner_imgsQ_eq_zero`. Two readings that the printed statement leaves open — the symmetry of
`P_L`, and Algorithm 10.17 in place of the book's Algorithm 10.18 — are argued in the docstring of
`theorem_10_18`.

§10.8.1 (CGNE/SSOR and CGNR/SSOR) constructs no new object: it is the normal equations of
`Numlib/Krylov/NormalEquations` preconditioned by the SSOR splitting of `A Aᵀ` or `Aᵀ A`, and its
only claim — that the methods do not break down, because `Aᵀ A` and `A Aᵀ` are positive definite
for a nonsingular `A` — is `Krylov.adjoint_comp_isSymmetricCoercive`. §10.8.2 (shifted IC(0)) is
an algorithm with an empirical discussion of the shift and no theorem.

`A` is `n × m`, as in Theorem 10.18; Proposition 10.17, which the book states for a nonsingular
`A`, is the square case, and `imgsL_diag_pos` is the rectangular form of its no-breakdown clause,
for a matrix with linearly independent rows. Indices are `0`-based: `imgsQ A dropL j` is the
book's `q_{j+1}`, and the rows are indexed by `ℕ` and padded by `0` past `n`, so that the
recursion of Algorithm 10.17 needs no dependent arithmetic. The set `P_L` is the predicate
`dropL`, and Theorem 10.18's hypotheses on it are bundled as `IsICPattern`.
-/

namespace SaadSparse.Chapter10

section IncompleteGramSchmidt

variable {n m : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-- The `i`-th row `a_i` of `A` as a vector of `𝕜ⁿ`, padded by `0` past `n`. -/
noncomputable def rowVec (A : Matrix (Fin n) (Fin m) 𝕜) (i : ℕ) : EuclideanSpace 𝕜 (Fin m) :=
  if h : i < n then WithLp.toLp 2 (A ⟨i, h⟩) else 0

/-- On a genuine row index, `rowVec` is that row of `A`. -/
@[simp]
theorem rowVec_coe (A : Matrix (Fin n) (Fin m) 𝕜) (i : Fin n) :
    rowVec A (i : ℕ) = WithLp.toLp 2 (A i) := by
  simp [rowVec, i.isLt]

/-- One term of the sum on line 3 of **Algorithm 10.17**: the retained multiple of the normalized
`q_j` that is subtracted from the row `a_i`. Splitting it out of `imgsHat` keeps the recursion to
a single recursive call. -/
private noncomputable def imgsTerm (A : Matrix (Fin n) (Fin m) 𝕜) (dropL : ℕ → ℕ → Bool)
    (i j : ℕ) (qhat : EuclideanSpace 𝕜 (Fin m)) : EuclideanSpace 𝕜 (Fin m) :=
  (if dropL i j then 0
    else inner 𝕜 (((‖qhat‖ : 𝕜))⁻¹ • qhat) (rowVec A i)) • ((‖qhat‖ : 𝕜))⁻¹ • qhat

/-- **Algorithm 10.17**, lines 2–4: the unnormalized vector
`q̂_i = a_i - ∑_{j < i} l_{ij} q_j`, where the sum runs over the coefficients the dropping rule
`dropL` retains. -/
noncomputable def imgsHat (A : Matrix (Fin n) (Fin m) 𝕜) (dropL : ℕ → ℕ → Bool) :
    ℕ → EuclideanSpace 𝕜 (Fin m)
  | i => rowVec A i - ∑ j : Finset.range i, imgsTerm A dropL i j (imgsHat A dropL j)
  decreasing_by exact Finset.mem_range.1 j.2

/-- **Algorithm 10.17**, line 7: the normalized vector `q_i = q̂_i / l_{ii}`. The book's "if
`l_{ii} = 0` then Stop" is Lean's `x / 0 = 0`, which makes `q_i = 0` at a breakdown. -/
noncomputable def imgsQ (A : Matrix (Fin n) (Fin m) 𝕜) (dropL : ℕ → ℕ → Bool) (i : ℕ) :
    EuclideanSpace 𝕜 (Fin m) :=
  ((‖imgsHat A dropL i‖ : 𝕜))⁻¹ • imgsHat A dropL i

/-- **Algorithm 10.17**, lines 2–3 and 6: the coefficient `l_{ij}`, which is `(a_i, q_j)` below the
diagonal unless the dropping rule discards it, `‖q̂_i‖₂` on the diagonal, and `0` above it. -/
noncomputable def imgsL (A : Matrix (Fin n) (Fin m) 𝕜) (dropL : ℕ → ℕ → Bool) (i j : ℕ) : 𝕜 :=
  if j < i then (if dropL i j then 0 else inner 𝕜 (imgsQ A dropL j) (rowVec A i))
  else if j = i then ((‖imgsHat A dropL i‖ : ℝ) : 𝕜)
  else 0

/-- The lower triangular factor `L` of Algorithm 10.17. -/
noncomputable def imgsLMat (A : Matrix (Fin n) (Fin m) 𝕜) (dropL : ℕ → ℕ → Bool) :
    Matrix (Fin n) (Fin n) 𝕜 :=
  Matrix.of fun i j => imgsL A dropL (i : ℕ) (j : ℕ)

/-- The factor `Q` of Algorithm 10.17, whose rows are the vectors `q_i`. It is not orthogonal,
because entries are dropped from `L`. -/
noncomputable def imgsQMat (A : Matrix (Fin n) (Fin m) 𝕜) (dropL : ℕ → ℕ → Bool) :
    Matrix (Fin n) (Fin m) 𝕜 :=
  Matrix.of fun i j => WithLp.ofLp (imgsQ A dropL (i : ℕ)) j

variable (A : Matrix (Fin n) (Fin m) 𝕜) (dropL : ℕ → ℕ → Bool)

/-- The entries of `L` are the coefficients `l_{ij}`. -/
@[simp]
theorem imgsLMat_apply (i j : Fin n) : imgsLMat A dropL i j = imgsL A dropL (i : ℕ) (j : ℕ) := rfl

/-- The rows of `Q` are the vectors `q_i`. -/
@[simp]
theorem imgsQMat_apply (i : Fin n) (j : Fin m) :
    imgsQMat A dropL i j = WithLp.ofLp (imgsQ A dropL (i : ℕ)) j := rfl

/-- `L` is lower triangular: `l_{ij} = 0` above the diagonal. -/
theorem imgsL_of_lt {i j : ℕ} (h : i < j) : imgsL A dropL i j = 0 := by
  have h1 : ¬(j < i) := by omega
  have h2 : ¬(j = i) := by omega
  simp [imgsL, h1, h2]

/-- **Algorithm 10.17**, line 6: the diagonal coefficient is `l_{ii} = ‖q̂_i‖₂`. -/
theorem imgsL_diag (i : ℕ) : imgsL A dropL i i = ((‖imgsHat A dropL i‖ : ℝ) : 𝕜) := by
  simp [imgsL]

/-- Below the diagonal, `l_{ij}` is `(a_i, q_j)` unless the dropping rule discards it. -/
theorem imgsL_of_gt {i j : ℕ} (h : j < i) :
    imgsL A dropL i j =
      if dropL i j then 0 else inner 𝕜 (imgsQ A dropL j) (rowVec A i) := by
  simp [imgsL, h]

/-- **Algorithm 10.17**, line 3: a discarded coefficient below the diagonal is `0`. -/
theorem imgsL_of_drop {i j : ℕ} (h : j < i) (hd : dropL i j) : imgsL A dropL i j = 0 := by
  simp [imgsL_of_gt A dropL h, hd]

/-- **Algorithm 10.17**, line 2: a retained coefficient below the diagonal is `(a_i, q_j)`. -/
theorem imgsL_of_not_drop {i j : ℕ} (h : j < i) (hd : ¬ dropL i j) :
    imgsL A dropL i j = inner 𝕜 (imgsQ A dropL j) (rowVec A i) := by
  simp [imgsL_of_gt A dropL h, hd]

/-- **Algorithm 10.17**, line 4, in terms of the coefficients it produces. -/
theorem imgsHat_eq (i : ℕ) :
    imgsHat A dropL i =
      rowVec A i - ∑ j ∈ Finset.range i, imgsL A dropL i j • imgsQ A dropL j := by
  rw [imgsHat, ← Finset.sum_coe_sort (Finset.range i)]
  refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
  rw [imgsTerm, imgsL_of_gt A dropL (Finset.mem_range.1 j.2)]
  rfl

/-- **Algorithm 10.17**, line 7 read backwards: `l_{ii} q_i = q̂_i`. At a breakdown both sides are
`0`, so no hypothesis is needed. -/
theorem imgsL_diag_smul_imgsQ (i : ℕ) :
    imgsL A dropL i i • imgsQ A dropL i = imgsHat A dropL i := by
  rcases eq_or_ne (imgsHat A dropL i) 0 with h | h
  · simp [imgsQ, h]
  · have hnorm : ((‖imgsHat A dropL i‖ : ℝ) : 𝕜) ≠ 0 := by
      simpa using norm_ne_zero_iff.2 h
    rw [imgsL_diag, imgsQ, smul_smul, mul_inv_cancel₀ hnorm, one_smul]

/-- **Saad (10.83)** at `P_Q = ∅`: `a_i = ∑_{j ≤ i} l_{ij} q_j`, exactly, however much is
dropped from `L`. This is why dropping in `L` alone still gives an exact factorization: the
vector subtracted on line 4 is built from the retained coefficients themselves. -/
theorem rowVec_eq_sum (i : ℕ) :
    rowVec A i = ∑ j ∈ Finset.range (i + 1), imgsL A dropL i j • imgsQ A dropL j := by
  rw [Finset.sum_range_succ, imgsL_diag_smul_imgsQ, imgsHat_eq]
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

/-- **Algorithm 10.17** does not break down when the rows of `A` are linearly independent: no
`q̂_i` vanishes. Were `q̂_i = 0`, (10.83) would exhibit the `i`-th row of `A` as a combination of
the earlier ones — each `q_k` being, inductively, a combination of `a_1, …, a_k`. -/
theorem imgsHat_ne_zero (hA : LinearIndependent 𝕜 fun i : Fin n => rowVec A (i : ℕ)) (i : Fin n) :
    imgsHat A dropL (i : ℕ) ≠ 0 := by
  intro h0
  have hspan : rowVec A (i : ℕ) ∈
      Submodule.span 𝕜 ((fun j : Fin n => rowVec A (j : ℕ)) ''
        {j : Fin n | (j : ℕ) < (i : ℕ)}) := by
    have hsum : rowVec A (i : ℕ) =
        ∑ j ∈ Finset.range (i : ℕ), imgsL A dropL (i : ℕ) j • imgsQ A dropL j := by
      rw [imgsHat_eq] at h0
      rw [← sub_eq_zero]
      exact h0
    rw [hsum]
    refine Submodule.sum_mem _ fun j hj => ?_
    have hji : j < (i : ℕ) := Finset.mem_range.1 hj
    refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_)
    refine Submodule.span_mono ?_ (imgsHat_mem_span A dropL j)
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨⟨k, (hk.trans hji.le).trans_lt i.isLt⟩, lt_of_le_of_lt hk hji, rfl⟩
  exact hA.notMem_span_image (s := {j : Fin n | (j : ℕ) < (i : ℕ)}) (by simp) hspan

/-- **Algorithm 10.17**, line 6: the diagonal coefficients `l_{ii} = ‖q̂_i‖₂` are positive when the
rows of `A` are linearly independent, so the algorithm runs to completion. -/
theorem imgsL_diag_pos {A : Matrix (Fin n) (Fin m) ℝ} (dropL : ℕ → ℕ → Bool)
    (hA : LinearIndependent ℝ fun i : Fin n => rowVec A (i : ℕ)) (i : Fin n) :
    0 < imgsL A dropL (i : ℕ) (i : ℕ) := by
  rw [imgsL_diag]
  simpa using norm_pos_iff.2 (imgsHat_ne_zero A dropL hA i)

/-- **Proposition 10.17**. Let `A` be a nonsingular matrix and assume that no dropping is applied
to `Q`. Then the incomplete Gram–Schmidt algorithm 10.17 does not break down — every `l_{ii}` is
positive — and it computes an exact factorization `A = L Q`, in which `L` is lower triangular with
positive diagonal and `Q` is nonsingular, though not orthogonal.

The proof is Saad's: were `l_{ii} = 0`, (10.83) would exhibit the `i`-th row of `A` as a
combination of the earlier ones, contradicting nonsingularity. -/
theorem proposition_10_17 {A : Matrix (Fin n) (Fin n) ℝ} (dropL : ℕ → ℕ → Bool)
    (hA : IsUnit A) :
    (∀ i : Fin n, 0 < imgsL A dropL (i : ℕ) (i : ℕ)) ∧
      (∀ i j : Fin n, (i : ℕ) < (j : ℕ) → imgsL A dropL (i : ℕ) (j : ℕ) = 0) ∧
      imgsLMat A dropL * imgsQMat A dropL = A ∧ IsUnit (imgsQMat A dropL) := by
  have hdiag : ∀ i : Fin n, 0 < imgsL A dropL (i : ℕ) (i : ℕ) :=
    imgsL_diag_pos dropL (linearIndependent_rowVec hA)
  have hlower : ∀ i j : Fin n, (i : ℕ) < (j : ℕ) → imgsL A dropL (i : ℕ) (j : ℕ) = 0 :=
    fun i j h => imgsL_of_lt A dropL h
  have hfac : imgsLMat A dropL * imgsQMat A dropL = A := by
    ext i k
    have hrow := congrArg (fun z : EuclideanSpace ℝ (Fin n) => WithLp.ofLp z k)
      (rowVec_eq_sum A dropL (i : ℕ))
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

section IncompleteCholesky

open scoped Matrix RealInnerProductSpace

variable {n m : ℕ}

/-! ### The zero-pattern hypothesis of Theorem 10.18 -/

/-- **The zero-pattern hypothesis of Theorem 10.18**: `P_L` avoids the diagonal, is symmetric, and
is such that for any `i, j, k` with `i < j` and `i < k`,

`(i, j) ∈ P_L` and `(i, k) ∉ P_L` imply `(j, k) ∈ P_L`.

Read on the entries the algorithm actually drops — the pairs `(i, j)` with `j < i` — the last
clause becomes two statements, `IsICPattern.notDrop_row` and `IsICPattern.notDrop_trans`, and
those are all the proof of Theorem 10.18 uses.

Symmetry is not printed in the book, and is not redundant: the printed clause constrains the pairs
`(i, j)` with `i < j`, while the algorithm drops the entries `l_{ij}` with `j < i`, so without a
link between the two triangles the hypothesis would say nothing about what is dropped, and
Theorem 10.18 would be false. A Cholesky zero pattern is symmetric — it is the pattern of both `L`
and `Lᵀ` — which is the link, and is what `Matrix.IsIC` asks for as well. -/
structure IsICPattern (dropL : ℕ → ℕ → Bool) : Prop where
  /-- `P_L ⊆ {(i, j) | i ≠ j}`, the only restriction the book places on `P_L` in general. -/
  notDrop_diag : ∀ i, ¬ dropL i i
  /-- `P_L` is symmetric, as the zero pattern of a Cholesky factorization is. -/
  symm : ∀ i j, dropL i j = dropL j i
  /-- The condition displayed in Theorem 10.18. -/
  drop_of_notDrop : ∀ i j k, i < j → i < k → dropL i j → ¬ dropL i k → dropL j k

section Pattern

variable {dropL : ℕ → ℕ → Bool} (hP : IsICPattern dropL)
include hP

namespace IsICPattern

/-- **Coefficients retained in one row are retained between themselves.** If neither `l_{ik}` nor
`l_{il}` is dropped and `l < k ≤ i`, then `l_{kl}` is not dropped either.

This is the condition of Theorem 10.18 with its two later indices in the order `j < k`, read on
the lower triangle through the symmetry of `P_L`. -/
theorem notDrop_row {i k l : ℕ} (hlk : l < k) (hki : k ≤ i) (hik : ¬ dropL i k)
    (hil : ¬ dropL i l) : ¬ dropL k l := fun h => hik <| by
  have h1 : dropL l k := by rw [hP.symm l k]; exact h
  have h2 : ¬ dropL l i := by rw [hP.symm l i]; exact hil
  rw [hP.symm i k]
  exact hP.drop_of_notDrop l k i hlk (hlk.trans_le hki) h1 h2

/-- **Retention is transitive down the rows.** If `l_{ij}` and `l_{jl}` are both retained, with
`l < j < i`, then `l_{il}` is retained.

This is the condition of Theorem 10.18 with its two later indices in the order `k < j`, read on
the lower triangle through the symmetry of `P_L`. -/
theorem notDrop_trans {i j l : ℕ} (hlj : l < j) (hji : j < i) (hij : ¬ dropL i j)
    (hjl : ¬ dropL j l) : ¬ dropL i l := fun h => hij <| by
  have h1 : dropL l i := by rw [hP.symm l i]; exact h
  have h2 : ¬ dropL l j := by rw [hP.symm l j]; exact hjl
  exact hP.drop_of_notDrop l i j (hlj.trans hji) hlj h1 h2

end IsICPattern

end Pattern

/-! ### Orthogonality off the pattern -/

variable (A : Matrix (Fin n) (Fin m) ℝ) (dropL : ℕ → ℕ → Bool)

/-- Over `ℝ` the normalization of line 7 of **Algorithm 10.17** is by the real number `‖q̂_i‖⁻¹`. -/
theorem imgsQ_real (i : ℕ) :
    imgsQ A dropL i = (‖imgsHat A dropL i‖)⁻¹ • imgsHat A dropL i := by
  simp [imgsQ]

/-- A breakdown at step `j` zeroes the whole `j`-th column of `L`: `q_j = 0`, so every later
coefficient `l_{ij} = (a_i, q_j)` vanishes, and `l_{jj} = ‖q̂_j‖₂` vanishes too. -/
theorem imgsL_eq_zero_of_imgsHat_eq_zero {j : ℕ} (h : imgsHat A dropL j = 0) (i : ℕ) :
    imgsL A dropL i j = 0 := by
  rcases lt_trichotomy j i with hji | hji | hji
  · have hq : imgsQ A dropL j = 0 := by simp [imgsQ, h]
    simp [imgsL_of_gt A dropL hji, hq]
  · subst hji
    simp [imgsL_diag, h]
  · exact imgsL_of_lt A dropL hji

/-- `l_{ik} (q_k, q_k) = l_{ik}`: the rows of `Q` are unit vectors, except at a breakdown, where
the coefficients `l_{ik}` vanish instead. -/
theorem imgsL_mul_inner_self (i k : ℕ) :
    imgsL A dropL i k * ⟪imgsQ A dropL k, imgsQ A dropL k⟫ = imgsL A dropL i k := by
  rcases eq_or_ne (imgsHat A dropL k) 0 with h | h
  · rw [imgsL_eq_zero_of_imgsHat_eq_zero A dropL h i, zero_mul]
  · have hnorm : ‖imgsQ A dropL k‖ = 1 := by
      rw [imgsQ_real, norm_smul, norm_inv, Real.norm_eq_abs, abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.2 h)]
    rw [real_inner_self_eq_norm_sq, hnorm, one_pow, mul_one]

/-- `A Aᵀ` is the Gram matrix of the rows of `A`. -/
theorem mul_transpose_apply (i j : Fin n) :
    (A * Aᵀ) i j = ⟪rowVec A (i : ℕ), rowVec A (j : ℕ)⟫ := by
  simp [Matrix.mul_apply, PiLp.inner_apply, rowVec_coe, mul_comm]

/-- A Gram matrix is symmetric. -/
theorem mul_transpose_apply_comm (i j : Fin n) : (A * Aᵀ) i j = (A * Aᵀ) j i := by
  rw [mul_transpose_apply A, mul_transpose_apply A, real_inner_comm]

section Factorization

variable {dropL} (hP : IsICPattern dropL)
include hP

namespace IsICPattern

/-- A nonzero coefficient at or below the diagonal is one the dropping rule retained. -/
theorem notDrop_of_imgsL_ne_zero {i k : ℕ} (hki : k ≤ i) (h : imgsL A dropL i k ≠ 0) :
    ¬ dropL i k := by
  rcases eq_or_lt_of_le hki with hk | hk
  · rw [hk]; exact hP.notDrop_diag i
  · exact fun hd => h (imgsL_of_drop A dropL hk hd)

/-- **The orthogonality on which Theorem 10.18 rests.** Whenever the coefficient `l_{ij}` is
retained by the dropping rule, the rows `q_i` and `q_j` of `Q` are orthogonal — so `Q Qᵀ` differs
from the identity only inside the pattern, and only there does `L Lᵀ` differ from `A Aᵀ`.

The induction is on `i`. In `(q̂_i, q_j) = (a_i, q_j) - ∑_{k < i} l_{ik} (q_k, q_j)` the term
`k = j` cancels `(a_i, q_j)` exactly, and every other term vanishes: a nonzero `l_{ik}` means that
`l_{ik}` and `l_{ij}` are both retained in row `i`, so `IsICPattern.notDrop_row` retains the
coefficient linking `k` and `j`, and the inductive hypothesis applies to it. -/
theorem inner_imgsQ_eq_zero (i : ℕ) :
    ∀ j < i, ¬ dropL i j → ⟪imgsQ A dropL i, imgsQ A dropL j⟫ = 0 := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro j hji hij
    have key : ⟪imgsHat A dropL i, imgsQ A dropL j⟫ = 0 := by
      rw [imgsHat_eq, inner_sub_left, sum_inner]
      have hterm : ∀ k ∈ Finset.range i, k ≠ j →
          ⟪imgsL A dropL i k • imgsQ A dropL k, imgsQ A dropL j⟫ = 0 := by
        intro k hk hkj
        rw [real_inner_smul_left]
        rcases eq_or_ne (imgsL A dropL i k) 0 with h0 | h0
        · rw [h0, zero_mul]
        have hki : k < i := Finset.mem_range.1 hk
        have hik : ¬ dropL i k := fun hd => h0 (imgsL_of_drop A dropL hki hd)
        rcases lt_or_gt_of_ne hkj with hkj' | hkj'
        · rw [← real_inner_comm (imgsQ A dropL k) (imgsQ A dropL j),
            ih j hji k hkj' (hP.notDrop_row hkj' hji.le hij hik), mul_zero]
        · rw [ih k hki j hkj' (hP.notDrop_row hkj' hki.le hik hij), mul_zero]
      rw [Finset.sum_eq_single j hterm fun h => absurd (Finset.mem_range.2 hji) h,
        real_inner_smul_left, imgsL_mul_inner_self, imgsL_of_not_drop A dropL hji hij,
        real_inner_comm, sub_self]
    rw [imgsQ_real, real_inner_smul_left, key, mul_zero]

/-- The cross terms of `(a_i, a_j)` vanish. If `l_{ij}`, `l_{ik}` and `l_{jl}` are all retained,
with `j ≤ i`, `k ≤ i` and `l ≤ j`, then `q_k ⟂ q_l` unless `k = l`.

Both `k` and `l` are retained *in row `i`* — `l` by `IsICPattern.notDrop_trans` — so
`IsICPattern.notDrop_row` and `IsICPattern.inner_imgsQ_eq_zero` apply to the pair. -/
theorem inner_imgsQ_eq_zero_of_ne {i j k l : ℕ} (hji : j ≤ i) (hij : ¬ dropL i j) (hki : k ≤ i)
    (hlj : l ≤ j) (hik : ¬ dropL i k) (hjl : ¬ dropL j l) (hkl : k ≠ l) :
    ⟪imgsQ A dropL k, imgsQ A dropL l⟫ = 0 := by
  have hil : ¬ dropL i l := by
    rcases eq_or_lt_of_le hlj with h | h
    · rw [h]; exact hij
    · rcases eq_or_lt_of_le hji with h' | h'
      · rw [← h']; exact hjl
      · exact hP.notDrop_trans h h' hij hjl
  rcases lt_or_gt_of_ne hkl with h | h
  · rw [← real_inner_comm (imgsQ A dropL k) (imgsQ A dropL l)]
    exact hP.inner_imgsQ_eq_zero A l k h (hP.notDrop_row h (hlj.trans hji) hil hik)
  · exact hP.inner_imgsQ_eq_zero A k l h (hP.notDrop_row h hki hik hil)

/-- **Why Algorithm 10.17 and Algorithm 10.18 agree here.** The incomplete *modified* Gram–Schmidt
process of Algorithm 10.18 computes `l_{ij}` against the partially updated row
`a_i - ∑_{k < j} l_{ik} q_k` rather than against `a_i`, so it differs from Algorithm 10.17 by the
corrections `l_{ik} (q_k, q_j)` for `k < j < i`; and each of those inner products vanishes,
because `k` and `j` are both retained in row `i`.

An induction on `j` therefore gives the same coefficients from both algorithms whenever the
pattern satisfies `IsICPattern`. Algorithm 10.18 itself is not formalized. -/
theorem inner_imgsQ_eq_zero_of_lt {i j k : ℕ} (hji : j < i) (hkj : k < j) (hij : ¬ dropL i j)
    (hik : ¬ dropL i k) : ⟪imgsQ A dropL k, imgsQ A dropL j⟫ = 0 :=
  hP.inner_imgsQ_eq_zero_of_ne A hji.le hij (hkj.trans hji).le le_rfl hik
    (hP.notDrop_diag j) hkj.ne

/-- **The identity behind Theorem 10.18**: off the pattern and below the diagonal, the entry
`b_{ij} = (a_i, a_j)` of `B = A Aᵀ` is the entry `∑_{k ≤ j} l_{ik} l_{jk}` of `L Lᵀ`.

Expanding both rows by (10.83) turns `(a_i, a_j)` into a double sum over the rows of `Q`, whose
off-diagonal terms vanish by `IsICPattern.inner_imgsQ_eq_zero_of_ne` and whose diagonal terms are
the `l_{ik} l_{jk}` by `imgsL_mul_inner_self`. -/
theorem inner_rowVec_eq_sum {i j : ℕ} (hji : j ≤ i) (hij : ¬ dropL i j) :
    ⟪rowVec A i, rowVec A j⟫
      = ∑ k ∈ Finset.range (j + 1), imgsL A dropL i k * imgsL A dropL j k := by
  rw [rowVec_eq_sum A dropL i, rowVec_eq_sum A dropL j, sum_inner]
  simp only [inner_sum, real_inner_smul_left, real_inner_smul_right]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hlj : l ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
  rw [Finset.sum_eq_single_of_mem l (Finset.mem_range.2 (by omega)) ?_]
  · rw [← mul_assoc, mul_comm (imgsL A dropL i l), mul_assoc, imgsL_mul_inner_self, mul_comm]
  · intro k hk hkl
    have hki : k ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    rcases eq_or_ne (imgsL A dropL i k) 0 with h0 | h0
    · rw [h0, zero_mul, mul_zero]
    rcases eq_or_ne (imgsL A dropL j l) 0 with h1 | h1
    · rw [h1, zero_mul]
    rw [hP.inner_imgsQ_eq_zero_of_ne A hji hij hki hlj (hP.notDrop_of_imgsL_ne_zero A hki h0)
      (hP.notDrop_of_imgsL_ne_zero A hlj h1) hkl, mul_zero, mul_zero]

/-- Below the diagonal and off the pattern, `L Lᵀ` reproduces `B = A Aᵀ`. -/
theorem imgsLMat_mul_transpose_apply {i j : Fin n} (hji : (j : ℕ) ≤ (i : ℕ))
    (hij : ¬ dropL (i : ℕ) (j : ℕ)) :
    (imgsLMat A dropL * (imgsLMat A dropL)ᵀ) i j = (A * Aᵀ) i j := by
  rw [mul_transpose_apply A, hP.inner_rowVec_eq_sum A hji hij, Matrix.mul_apply]
  have hentry : ∀ k : Fin n, imgsLMat A dropL i k * (imgsLMat A dropL)ᵀ k j
      = imgsL A dropL (i : ℕ) (k : ℕ) * imgsL A dropL (j : ℕ) (k : ℕ) := fun _ => rfl
  rw [Finset.sum_congr rfl fun k _ => hentry k,
    Fin.sum_univ_eq_sum_range
      (fun k => imgsL A dropL (i : ℕ) k * imgsL A dropL (j : ℕ) k) n]
  refine (Finset.sum_subset (fun k hk => ?_) fun k _ hk => ?_).symm
  · exact Finset.mem_range.2 (by
      have := Finset.mem_range.1 hk
      have := i.isLt
      omega)
  · rw [Finset.mem_range, not_lt] at hk
    rw [imgsL_of_lt A dropL (by omega : (j : ℕ) < k), mul_zero]

end IsICPattern

/-- **Theorem 10.18**. Let `A` be an `n × m` matrix and let `B = A Aᵀ`. Consider a zero-pattern
set `P_L` satisfying `IsICPattern`, that is, avoiding the diagonal and such that for any
`i, j, k` with `i < j` and `i < k`,

`(i, j) ∈ P_L` and `(i, k) ∉ P_L` imply `(j, k) ∈ P_L`.

Then the matrix `L` obtained from the incomplete Gram–Schmidt algorithm with the zero-pattern set
`P_L` is identical with the `L` factor that would be obtained from the incomplete Cholesky
factorization applied to `B` with the same zero-pattern set: `Matrix.IsIC P_L B L` holds, and by
`Matrix.IsIC.eq_of_diag_pos` no other lower triangular factor with a positive diagonal does — a
positive diagonal being what `imgsL_diag_pos` gives when the rows of `A` are independent.

The proof is not the book's, which states the theorem without proof and cites the literature. It
is the orthogonality `IsICPattern.inner_imgsQ_eq_zero`: what the hypothesis on `P_L` buys is that
the rows of `Q` retained in a row of `L` are pairwise orthogonal, so all the cross terms of
`(a_i, a_j) = ∑_{k, l} l_{ik} l_{jl} (q_k, q_l)` disappear and what is left is the `(i, j)` entry
of `L Lᵀ`.

Two readings the printed statement leaves open are fixed. Symmetry of `P_L` is part of
`IsICPattern`, and its docstring says why it is needed. And the book attaches the theorem to its
Algorithm 10.18, the *modified* Gram–Schmidt process, whereas `imgsL` is Algorithm 10.17; under
this hypothesis the two compute the same `L`, because every correction the modified process makes
to a coefficient is an inner product that `IsICPattern.inner_imgsQ_eq_zero_of_lt` shows to
vanish. -/
theorem theorem_10_18 :
    Matrix.IsIC {p : Fin n × Fin n | dropL (p.1 : ℕ) (p.2 : ℕ)} (A * Aᵀ) (imgsLMat A dropL) where
  l_eq_zero_of_lt i j hij := imgsL_of_lt A dropL hij
  l_eq_zero_of_mem i j hij := by
    rcases lt_trichotomy (j : ℕ) (i : ℕ) with h | h | h
    · exact imgsL_of_drop A dropL h hij
    · exact absurd (by simpa [h] using hij) (hP.notDrop_diag (i : ℕ))
    · exact imgsL_of_lt A dropL h
  agree i j hij := by
    rcases le_total (j : ℕ) (i : ℕ) with h | h
    · exact hP.imgsLMat_mul_transpose_apply A h hij
    · rw [mul_transpose_apply_comm A i j,
        ← hP.imgsLMat_mul_transpose_apply A h (by rw [hP.symm]; exact hij)]
      exact mul_transpose_apply_comm (imgsLMat A dropL) i j

end Factorization

end IncompleteCholesky

end SaadSparse.Chapter10

import Numlib.Krylov.Hessenberg
import Numlib.Krylov.Lanczos
import Numlib.Krylov.ToEuclideanLin
import Numlib.LinearAlgebra.Matrix.KrylovDecomposition
import Numlib.LinearAlgebra.Matrix.QR

/-!
# Krylov and Arnoldi decompositions in matrix and operator form

The Krylov layer states the Arnoldi and Lanczos processes for an operator on an inner product
space with `ℕ`-indexed vectors (`Arnoldi.vec`, `Arnoldi.coeff`, `Lanczos.tridiag`); the books
(Saad §6.3, Quarteroni–Sacco–Saleri §5.11, [golub2013matrix] §10.1 and §10.5) state them for a
matrix as the identity `A Q_k = Q_k H_k + r_k e_kᵀ`. This module is that reading, once.

## Main definitions

* `Krylov.lastVec β k`: the vector `β e_k` of `𝕜^k` (zero for `k = 0`), the sibling of
  `Krylov.firstVec`; `Krylov.lastVec_succ` identifies it with `Pi.single (Fin.last k) β`.
* `Arnoldi.basisMatrix A q k`: the `n × k` matrix `Q_k = [q_1 | ⋯ | q_k]` of Arnoldi vectors of
  `Matrix.toEuclideanLin A` from `q`.
* `Krylov.IsKrylovDecomposition A q B r b`, `Krylov.IsArnoldiDecomposition A q H r`: Krylov and
  Arnoldi decompositions of an operator on an orthonormal family (the form of Saad's eigenvalue
  book, Parlett and Stewart); `Matrix.isKrylovDecomposition_iff` and
  `Matrix.isArnoldiDecomposition_iff` make the matrix predicates of
  `Numlib/LinearAlgebra/Matrix/KrylovDecomposition` their `toEuclideanLin` instances.

## Main results

* `Arnoldi.mul_basisMatrix` ([golub2013matrix] (10.5.2)) and `Lanczos.mul_basisMatrix`
  ((10.1.4)): the Arnoldi and Lanczos relations in matrix form, at every step;
  `Arnoldi.conjTranspose_basisMatrix_mul_self`, `Arnoldi.conjTranspose_basisMatrix_mulVec_w`,
  `Arnoldi.conjTranspose_basisMatrix_mul_mul_basisMatrix`: orthonormal columns below the grade,
  residual orthogonal to them, and `Qᴴ A Q = H`; `Arnoldi.range_basisMatrix`: the columns span the
  Krylov subspace.
* `Arnoldi.isArnoldiDecomposition`, `Arnoldi.isArnoldiDecomposition_basisMatrix`: the Arnoldi
  process gives an Arnoldi decomposition below the grade.
* `Krylov.IsArnoldiDecomposition.span_eq_subspace`: with an unreduced `H` the leading vectors of
  any Arnoldi decomposition span the Krylov subspaces of its first vector.
* `Matrix.IsArnoldiDecomposition.eq_basisMatrix`: the uniqueness of the Arnoldi process given its
  first column — an Arnoldi decomposition with positive subdiagonal *is* the Arnoldi process. A
  corollary of the implicit Q engine `Matrix.IsArnoldiDecomposition.implicitQ`.
* `Matrix.range_krylovMatrix`, `Krylov.grade_eq_rank_krylovMatrix`: the Krylov subspace is the
  range of the Krylov matrix, and the grade is its rank (the index `m = rank K(A, q₁, n)` of
  [golub2013matrix] Theorem 10.1.1).
* `Krylov.IsArnoldiDecomposition.hessenbergRelation`: every Arnoldi decomposition is a two-family
  Hessenberg relation `Krylov.HessenbergRelation₂`, so the FOM/GMRES residual formulas apply to it.
* `Matrix.exists_isUpperHessenberg_conj_lastCol` ([golub2013matrix] P10.5.2): a unitary reduction
  to Hessenberg form sending a prescribed vector to a multiple of the last unit vector, which
  Krylov–Schur restarting uses to return to Arnoldi form.

Indices are `0`-based: column `j` of `Arnoldi.basisMatrix A q k` is the book's `q_{j+1}`.
-/

open Matrix Finset

variable {𝕜 : Type*} [RCLike 𝕜]

namespace Krylov

/-- `β e_k ∈ 𝕜^k`, the last unit vector scaled by `β` (the zero vector when `k = 0`); the sibling
of `Krylov.firstVec`. -/
def lastVec (β : 𝕜) (k : ℕ) : Fin k → 𝕜 :=
  fun j => if (j : ℕ) + 1 = k then β else 0

/-- On `Fin (k + 1)` the last unit vector is `Pi.single (Fin.last k)`: the Krylov layer's `β e_k`
meets the matrix layer's (`Matrix.IsArnoldiDecomposition`). -/
theorem lastVec_succ (β : 𝕜) (k : ℕ) :
    lastVec β (k + 1) = Pi.single (Fin.last k) β := by
  ext j
  simp [lastVec, Pi.single_apply, Fin.ext_iff]

/-! ### Operator-level decompositions -/

section Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {m : Type*} [Fintype m]

/-- A **Krylov decomposition** of an operator (Stewart; [golub2013matrix] §10.5.4 in matrix form):
an orthonormal family `q`, a residual `r` orthogonal to it, and `A q_j = ∑ᵢ B i j q_i + b_j r`. No
completeness or finite dimension is assumed. -/
structure IsKrylovDecomposition (A : E →ₗ[𝕜] E) (q : m → E) (B : Matrix m m 𝕜) (r : E)
    (b : m → 𝕜) : Prop where
  /-- The family is orthonormal. -/
  orthonormal : Orthonormal 𝕜 q
  /-- The residual is orthogonal to the family. -/
  inner_residual : ∀ j, inner 𝕜 (q j) r = 0
  /-- The decomposition, column by column. -/
  apply_eq : ∀ j, A (q j) = ∑ i, B i j • q i + b j • r

/-- An **Arnoldi decomposition** of an operator with `k + 1` vectors: a Krylov decomposition with
upper Hessenberg `H` and `b = e_last`, i.e. `A q_j = ∑_{i ≤ j+1} h_{ij} q_i` for `j < k` and
`A q_k = ∑_{i ≤ k} h_{ik} q_i + r`. -/
structure IsArnoldiDecomposition {k : ℕ} (A : E →ₗ[𝕜] E) (q : Fin (k + 1) → E)
    (H : Matrix (Fin (k + 1)) (Fin (k + 1)) 𝕜) (r : E) : Prop
    extends IsKrylovDecomposition A q H r (Pi.single (Fin.last k) 1) where
  /-- The coefficient matrix is upper Hessenberg. -/
  isUpperHessenberg : H.IsUpperHessenberg

namespace IsArnoldiDecomposition

variable {k : ℕ} {A : E →ₗ[𝕜] E} {q : Fin (k + 1) → E}
  {H : Matrix (Fin (k + 1)) (Fin (k + 1)) 𝕜} {r : E}

/-- The Arnoldi recurrence of an operator-level decomposition, for `i < k`:
`h_{i+1,i} q_{i+1} = A q_i − ∑_{l ≤ i} h_{l,i} q_l`. -/
theorem smul_succ (h : IsArnoldiDecomposition A q H r) (i : Fin k) :
    H i.succ i.castSucc • q i.succ =
      A (q i.castSucc) - ∑ l ∈ Iic i.castSucc, H l i.castSucc • q l := by
  rw [h.apply_eq, Pi.single_eq_of_ne (Fin.castSucc_lt_last i).ne, zero_smul, add_zero,
    ← sum_add_sum_compl (Iic i.castSucc), add_sub_cancel_left]
  rw [sum_eq_single_of_mem i.succ
    (by simp only [mem_compl, mem_Iic, not_le]; exact Fin.castSucc_lt_succ)]
  intro l hl hne
  simp only [mem_compl, mem_Iic, not_le] at hl
  have hsl : i.succ < l := by
    rw [Fin.lt_def] at hl ⊢
    have : (l : ℕ) ≠ i + 1 := fun h' => hne (Fin.ext (by simpa using h'))
    simp only [Fin.val_castSucc] at hl
    simp only [Fin.val_succ]
    omega
  rw [h.isUpperHessenberg l i.castSucc ⟨i.succ, Fin.castSucc_lt_succ, hsl⟩, zero_smul]

/-- The vectors of an Arnoldi decomposition with unreduced `H` lie in the Krylov subspaces of the
first one: `q_j ∈ 𝒦_{t+1}(A, q_0)` for `j ≤ t`. -/
theorem mem_subspace (h : IsArnoldiDecomposition A q H r) (hH : H.IsUnreducedUpperHessenberg)
    (t : ℕ) : ∀ j : Fin (k + 1), (j : ℕ) ≤ t → q j ∈ subspace A (q 0) (t + 1) := by
  induction t with
  | zero =>
    intro j hj
    obtain rfl : j = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    simpa using pow_apply_mem_subspace A (q 0) (i := 0) (m := 1) one_pos
  | succ t ih =>
    intro j hj
    rcases Nat.lt_or_ge (j : ℕ) (t + 1) with hlt | hge
    · exact subspace_mono A (q 0) (by omega) (ih j (by omega))
    have htk : t < k := by have := j.isLt; omega
    set i : Fin k := ⟨t, htk⟩ with hi
    obtain rfl : j = i.succ := Fin.ext (by simp [hi]; omega)
    have hne := hH.apply_succ_castSucc_ne_zero i
    have hq : q i.succ = (H i.succ i.castSucc)⁻¹ •
        (A (q i.castSucc) - ∑ l ∈ Iic i.castSucc, H l i.castSucc • q l) := by
      rw [← h.smul_succ, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [hq]
    refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ (Submodule.sum_mem _ fun l hl => ?_))
    · exact map_subspace_le A (q 0) (t + 1) ⟨_, ih i.castSucc (by simp [hi]), rfl⟩
    · refine Submodule.smul_mem _ _ (subspace_mono A (q 0) (by omega) (ih l ?_))
      have := Fin.le_def.1 (mem_Iic.1 hl)
      simpa [hi] using this

/-- With an unreduced `H`, the leading `i` vectors of an Arnoldi decomposition span the Krylov
subspace `𝒦_i(A, q_0)` ([golub2013matrix] §10.5.3: after a restart "we are all set to perform
step `j + 1` of the Arnoldi iteration"). The inclusion is `mem_subspace`; both sides have dimension
`i`, the left one because the vectors are orthonormal. -/
theorem span_eq_subspace (h : IsArnoldiDecomposition A q H r) (hH : H.IsUnreducedUpperHessenberg)
    {i : ℕ} (hi : i ≤ k + 1) :
    Submodule.span 𝕜 (Set.range fun a : Fin i => q (Fin.castLE hi a)) = subspace A (q 0) i := by
  have hle : Submodule.span 𝕜 (Set.range fun a : Fin i => q (Fin.castLE hi a)) ≤
      subspace A (q 0) i := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by have := a.isLt; omega⟩
    exact h.mem_subspace hH i _ (by simp; omega)
  have hli : LinearIndependent 𝕜 fun a : Fin i => q (Fin.castLE hi a) :=
    h.orthonormal.linearIndependent.comp _ (Fin.castLE_injective hi)
  have : FiniteDimensional 𝕜 (subspace A (q 0) i) :=
    FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _)
  refine Submodule.eq_of_le_of_finrank_le hle ?_
  rw [finrank_span_eq_card hli, Fintype.card_fin]
  calc Module.finrank 𝕜 (subspace A (q 0) i) ≤ Fintype.card (Fin i) := finrank_range_le_card _
    _ = i := Fintype.card_fin i

/-- **The bridge to the Hessenberg relation** (`Krylov.HessenbergRelation₂`,
`Numlib/Krylov/Hessenberg`): extending an Arnoldi decomposition by `z_j = q_j` (`0` beyond `k`),
`v_j = q_j` for `j ≤ k`, `v_{k+1} = r` (`0` beyond), `h_{ij} = H_{ij}` for `i, j ≤ k`,
`h_{k+1,k} = 1` (`0` otherwise), gives a two-family Hessenberg relation, so that every FOM/GMRES
residual formula stated through it applies to an Arnoldi decomposition. -/
theorem hessenbergRelation (h : IsArnoldiDecomposition A q H r) :
    ∃ (z v : ℕ → E) (c : ℕ → ℕ → 𝕜), HessenbergRelation₂ A z v c ∧
      (∀ j : Fin (k + 1), z j = q j ∧ v j = q j) ∧ v (k + 1) = r ∧
      ∀ i j : Fin (k + 1), c i j = H i j := by
  classical
  let z : ℕ → E := fun j => if hj : j < k + 1 then q ⟨j, hj⟩ else 0
  let v : ℕ → E := fun j => if hj : j < k + 1 then q ⟨j, hj⟩ else if j = k + 1 then r else 0
  let c : ℕ → ℕ → 𝕜 := fun i j =>
    if hi : i < k + 1 then (if hj : j < k + 1 then H ⟨i, hi⟩ ⟨j, hj⟩ else 0)
    else if i = k + 1 ∧ j = k then 1 else 0
  have hfin : ∀ j : Fin (k + 1), ∑ i ∈ range (k + 1), c i j • v i = ∑ i, H i j • q i := by
    intro j
    rw [← Fin.sum_univ_eq_sum_range (fun i => c i j • v i) (k + 1)]
    refine sum_congr rfl fun i _ => ?_
    simp only [c, v, i.isLt, j.isLt, dite_true]
  refine ⟨z, v, c, ⟨fun j => ?_, fun i j hij => ?_⟩, fun j => ?_, ?_, fun i j => ?_⟩
  · rcases lt_trichotomy j k with hj | rfl | hj
    · -- a column with no residual term
      have hz : z j = q ⟨j, by omega⟩ := by simp only [z, show j < k + 1 by omega, dite_true]
      rw [hz, h.apply_eq, Pi.single_eq_of_ne (by simp [Fin.ext_iff]; omega), zero_smul, add_zero,
        ← hfin]
      refine (sum_subset (by intro i hi; simp at hi ⊢; omega) fun i hi hi' => ?_).symm
      simp only [mem_range, not_lt] at hi hi'
      have hik : i < k + 1 := hi
      simp only [c, hik, show j < k + 1 by omega, dite_true]
      rw [h.isUpperHessenberg _ _ ⟨⟨j + 1, by omega⟩, by simp [Fin.lt_def], by
        simp [Fin.lt_def]; omega⟩, zero_smul]
    · have hz : z j = q (Fin.last j) := by simp only [z, lt_add_one, dite_true]; rfl
      rw [hz, h.apply_eq, Pi.single_eq_same, one_smul, sum_range_succ, ← hfin (Fin.last j),
        Fin.val_last]
      congr 1
      simp [c, v]
    · have hz : z j = 0 := by simp only [z, show ¬ j < k + 1 by omega, dite_false]
      rw [hz, map_zero]
      refine (sum_eq_zero fun i _ => ?_).symm
      have : c i j = 0 := by
        simp only [c, show ¬ j < k + 1 by omega, dite_false]
        split_ifs with h1 h2 <;> first | rfl | omega
      rw [this, zero_smul]
  · simp only [c]
    split_ifs with h1 h2 h3
    · exact h.isUpperHessenberg _ _ ⟨⟨j + 1, by omega⟩, by simp [Fin.lt_def], by
        simp [Fin.lt_def]; omega⟩
    · rfl
    · omega
    · rfl
  · simp only [z, v, j.isLt, dite_true, and_self]
  · simp only [v, lt_irrefl, dite_false, ite_true]
  · simp only [c, i.isLt, j.isLt, dite_true]

end IsArnoldiDecomposition

end Operator

end Krylov

namespace Arnoldi

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The Arnoldi relation at every step, column by column: for `j ≤ k`,
`A v_j = ∑_{i ≤ k} h_{ij} v_i + [j = k] w_k` ([golub2013matrix] (10.5.2)). It holds past
breakdown, where both sides vanish. -/
theorem apply_vec_eq_sum_add_lastVec (A : E →ₗ[𝕜] E) (b : E) (k : ℕ) (j : Fin (k + 1)) :
    A (vec A b j) = ∑ i : Fin (k + 1), hessenbergSq A b (k + 1) i j • vec A b i +
      Krylov.lastVec (1 : 𝕜) (k + 1) j • w A b k := by
  have hsum : ∑ i : Fin (k + 1), hessenbergSq A b (k + 1) i j • vec A b i =
      ∑ i ∈ range (k + 1), coeff A b i j • vec A b i :=
    Fin.sum_univ_eq_sum_range (fun i => coeff A b i j • vec A b i) (k + 1)
  rw [hsum]
  by_cases hj : (j : ℕ) = k
  · simp only [Krylov.lastVec, hj, ↓reduceIte, one_smul]
    rw [w]
    abel
  · have hj' : ¬ ((j : ℕ) + 1 = k + 1) := by omega
    simp only [Krylov.lastVec, hj', ↓reduceIte, zero_smul, add_zero]
    exact apply_vec_of_le A b (n := k + 1) (by have := j.isLt; omega)

/-- The Arnoldi process gives an Arnoldi decomposition below the grade: for `k + 1 ≤ grade A b`,
the vectors `v_0, …, v_k` are orthonormal, `w_k` is orthogonal to them, and
`A v_j = ∑ h_{ij} v_i + [j = k] w_k` with `H_{k+1}` upper Hessenberg. -/
theorem isArnoldiDecomposition (A : E →ₗ[𝕜] E) (b : E)
    [FiniteDimensional 𝕜 (Krylov.fullSubspace A b)] {k : ℕ} (hk : k + 1 ≤ Krylov.grade A b) :
    Krylov.IsArnoldiDecomposition A (fun j : Fin (k + 1) => vec A b j) (hessenbergSq A b (k + 1))
      (w A b k) where
  orthonormal := ⟨fun j => norm_vec_eq_one_of_lt_grade A b (by have := j.isLt; omega),
    fun i j hij => inner_vec_eq_zero A b fun h => hij (Fin.ext h)⟩
  inner_residual j := by
    rw [w_eq_sub_starProjection]
    exact Submodule.inner_right_of_mem_orthogonal (vec_mem_subspace_of_lt A b j.isLt)
      (Submodule.sub_starProjection_mem_orthogonal _)
  apply_eq j := by
    simpa only [Krylov.lastVec_succ] using apply_vec_eq_sum_add_lastVec A b k j
  isUpperHessenberg := hessenbergSq_isUpperHessenberg A b (k + 1)

end Arnoldi

/-! ### The matrix reading -/

namespace Matrix

/-- The range of `toEuclideanLin M` is the span of the columns of `M`. (Belongs with
`Matrix.toEuclideanLin_apply_eq_sum` in `Numlib/Analysis/Matrix/ToEuclideanLin`.) -/
theorem range_toEuclideanLin_eq_span_col {n m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix n m 𝕜) :
    LinearMap.range (toEuclideanLin M) =
      Submodule.span 𝕜 (Set.range fun j => WithLp.toLp 2 (M.col j)) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    have hx := toEuclideanLin_apply_eq_sum M (WithLp.ofLp x)
    simp only [WithLp.toLp_ofLp] at hx
    rw [hx]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact ⟨WithLp.toLp 2 (Pi.single j 1), by rw [toEuclideanLin_toLp, mulVec_single_one]⟩

/-- `Qᴴ Q = 1` iff the columns of `Q` are orthonormal in `EuclideanSpace`. -/
theorem conjTranspose_mul_self_eq_one_iff_orthonormal {n m : Type*} [Fintype n]
    [DecidableEq m] {Q : Matrix n m 𝕜} :
    Qᴴ * Q = 1 ↔ Orthonormal 𝕜 fun j => WithLp.toLp 2 (Q.col j) := by
  rw [orthonormal_iff_ite, ← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, one_apply, mul_apply]
  rfl

/-- `Qᴴ r = 0` iff `r` is orthogonal to the columns of `Q`. -/
theorem conjTranspose_mulVec_eq_zero_iff {n m : Type*} [Fintype n] {Q : Matrix n m 𝕜}
    {r : n → 𝕜} :
    Qᴴ *ᵥ r = 0 ↔ ∀ j, inner 𝕜 (WithLp.toLp 2 (Q.col j)) (WithLp.toLp 2 r) = 0 := by
  rw [funext_iff]
  refine forall_congr' fun j => ?_
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  rfl

end Matrix

section MatrixForm

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace Matrix

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The matrix Krylov decomposition is the `toEuclideanLin` instance of the operator one. -/
theorem isKrylovDecomposition_iff {A : Matrix n n 𝕜} {Q : Matrix n m 𝕜} {B : Matrix m m 𝕜}
    {r : n → 𝕜} {b : m → 𝕜} :
    IsKrylovDecomposition A Q B r b ↔
      Krylov.IsKrylovDecomposition (toEuclideanLin A) (fun j => WithLp.toLp 2 (Q.col j)) B
        (WithLp.toLp 2 r) b := by
  have hcol : A * Q = Q * B + vecMulVec r b ↔
      ∀ j, A *ᵥ Q.col j = ∑ i, B i j • Q.col i + b j • r := by
    rw [← Matrix.ext_iff]
    refine ⟨fun h j => ?_, fun h x j => ?_⟩
    · ext x
      rw [← col_mul_eq_mulVec_col, col_apply, h]
      simp [mul_apply, vecMulVec_apply, Finset.sum_apply, mul_comm]
    · have := congrFun (h j) x
      rw [← col_mul_eq_mulVec_col, col_apply] at this
      rw [this]
      simp [mul_apply, vecMulVec_apply, Finset.sum_apply, mul_comm]
  constructor
  · intro h
    refine ⟨conjTranspose_mul_self_eq_one_iff_orthonormal.1 h.conjTranspose_mul_self,
      conjTranspose_mulVec_eq_zero_iff.1 h.conjTranspose_mulVec, fun j => ?_⟩
    rw [toEuclideanLin_toLp, (hcol.1 h.mul_eq) j]
    simp only [WithLp.toLp_add, WithLp.toLp_sum, WithLp.toLp_smul]
  · intro h
    refine ⟨conjTranspose_mul_self_eq_one_iff_orthonormal.2 h.orthonormal,
      conjTranspose_mulVec_eq_zero_iff.2 h.inner_residual, hcol.2 fun j => ?_⟩
    have := h.apply_eq j
    rw [toEuclideanLin_toLp] at this
    apply (WithLp.toLp_injective 2)
    rw [this]
    simp only [WithLp.toLp_add, WithLp.toLp_sum, WithLp.toLp_smul]

/-- The matrix Arnoldi decomposition is the `toEuclideanLin` instance of the operator one. -/
theorem isArnoldiDecomposition_iff {k : ℕ} {A : Matrix n n 𝕜} {Q : Matrix n (Fin (k + 1)) 𝕜}
    {H : Matrix (Fin (k + 1)) (Fin (k + 1)) 𝕜} {r : n → 𝕜} :
    IsArnoldiDecomposition A Q H r ↔
      Krylov.IsArnoldiDecomposition (toEuclideanLin A) (fun j => WithLp.toLp 2 (Q.col j)) H
        (WithLp.toLp 2 r) :=
  ⟨fun h => ⟨isKrylovDecomposition_iff.1 h.toIsKrylovDecomposition, h.isUpperHessenberg⟩,
    fun h => ⟨isKrylovDecomposition_iff.2 h.toIsKrylovDecomposition, h.isUpperHessenberg⟩⟩

/-- With an unreduced `H`, the leading `i` columns of an Arnoldi decomposition span the Krylov
subspace of `A` on the first column (`Krylov.IsArnoldiDecomposition.span_eq_subspace`, read for
matrices). -/
theorem IsArnoldiDecomposition.range_eq_subspace {k : ℕ} {A : Matrix n n 𝕜}
    {Q : Matrix n (Fin (k + 1)) 𝕜} {H : Matrix (Fin (k + 1)) (Fin (k + 1)) 𝕜} {r : n → 𝕜}
    (h : IsArnoldiDecomposition A Q H r) (hH : H.IsUnreducedUpperHessenberg) {i : ℕ}
    (hi : i ≤ k + 1) :
    Submodule.span 𝕜 (Set.range fun a : Fin i => WithLp.toLp 2 (Q.col (Fin.castLE hi a))) =
      Krylov.subspace (toEuclideanLin A) (WithLp.toLp 2 (Q *ᵥ Pi.single 0 1)) i := by
  rw [mulVec_single_one]
  exact (isArnoldiDecomposition_iff.1 h).span_eq_subspace hH hi

/-- `K(A, q, k)` spans the Krylov subspace: the range of the Krylov matrix is `𝒦_k(A, q)`
([golub2013matrix] §10.1.1). -/
theorem range_krylovMatrix (A : Matrix n n 𝕜) (q : n → 𝕜) (k : ℕ) :
    LinearMap.range (toEuclideanLin (krylovMatrix A q k)) =
      Krylov.subspace (toEuclideanLin A) (WithLp.toLp 2 q) k := by
  rw [range_toEuclideanLin_eq_span_col, krylov_subspace_toEuclideanLin]
  rfl

end Matrix

/-- The grade is the rank of the Krylov matrix: the termination index `m = rank K(A, q₁, n)` of
[golub2013matrix] Theorem 10.1.1. -/
theorem Krylov.grade_eq_rank_krylovMatrix (A : Matrix n n 𝕜) (q : n → 𝕜) :
    Krylov.grade (toEuclideanLin A) (WithLp.toLp 2 q) =
      (krylovMatrix A q (Fintype.card n)).rank := by
  rw [rank_eq_finrank_range_toLin _ (EuclideanSpace.basisFun n 𝕜).toBasis
    (EuclideanSpace.basisFun (Fin (Fintype.card n)) 𝕜).toBasis]
  change _ = Module.finrank 𝕜 (LinearMap.range (toEuclideanLin (krylovMatrix A q _)))
  rw [range_krylovMatrix, Krylov.finrank_subspace, min_eq_right]
  calc Krylov.grade (toEuclideanLin A) (WithLp.toLp 2 q)
      ≤ Module.finrank 𝕜 (EuclideanSpace 𝕜 n) := Krylov.grade_le_finrank _ _
    _ = Fintype.card n := finrank_euclideanSpace

namespace Arnoldi

/-- The matrix `Q_k = [q_1 | ⋯ | q_k]` of Arnoldi vectors of `toEuclideanLin A` from `q` (for
Hermitian `A`, Lanczos vectors). Past the grade its columns are `0`. -/
noncomputable def basisMatrix (A : Matrix n n 𝕜) (q : EuclideanSpace 𝕜 n) (k : ℕ) :
    Matrix n (Fin k) 𝕜 :=
  Matrix.of fun i j => (vec (toEuclideanLin A) q j).ofLp i

variable (A : Matrix n n 𝕜) (q : EuclideanSpace 𝕜 n)

/-- The columns of `Q_k` are the Arnoldi vectors. -/
theorem col_basisMatrix (k : ℕ) (j : Fin k) :
    (basisMatrix A q k).col j = (vec (toEuclideanLin A) q j).ofLp :=
  rfl

/-- The columns of `Q_k` span the Krylov subspace, for every `k` ([golub2013matrix] (10.5.1),
Theorem 10.1.1). -/
theorem range_basisMatrix (k : ℕ) :
    LinearMap.range (toEuclideanLin (basisMatrix A q k)) =
      Krylov.subspace (toEuclideanLin A) q k := by
  rw [Matrix.range_toEuclideanLin_eq_span_col, ← span_vec]
  congr 1
  ext x
  simp only [col_basisMatrix, WithLp.toLp_ofLp, Set.mem_range, Set.mem_image, Set.mem_Iio]
  exact ⟨fun ⟨j, hj⟩ => ⟨j, j.isLt, hj⟩, fun ⟨j, hj, hx⟩ => ⟨⟨j, hj⟩, hx⟩⟩

/-- Orthonormal columns below the grade: `Q_kᴴ Q_k = 1` for `k ≤ grade`. -/
theorem conjTranspose_basisMatrix_mul_self {k : ℕ} (hk : k ≤ Krylov.grade (toEuclideanLin A) q) :
    (basisMatrix A q k)ᴴ * basisMatrix A q k = 1 := by
  rw [Matrix.conjTranspose_mul_self_eq_one_iff_orthonormal]
  simp only [col_basisMatrix, WithLp.toLp_ofLp]
  exact ⟨fun j => norm_vec_eq_one_of_lt_grade _ q (by have := j.isLt; omega),
    fun i j hij => inner_vec_eq_zero _ q fun h => hij (Fin.ext h)⟩

/-- The residual `w_k` is orthogonal to the columns of `Q_{k+1}`. -/
theorem conjTranspose_basisMatrix_mulVec_w (k : ℕ) :
    (basisMatrix A q (k + 1))ᴴ *ᵥ (w (toEuclideanLin A) q k).ofLp = 0 := by
  rw [Matrix.conjTranspose_mulVec_eq_zero_iff]
  intro j
  simp only [col_basisMatrix, WithLp.toLp_ofLp]
  rw [w_eq_sub_starProjection]
  exact Submodule.inner_right_of_mem_orthogonal (vec_mem_subspace_of_lt _ q j.isLt)
    (Submodule.sub_starProjection_mem_orthogonal _)

/-- **The Arnoldi relation in matrix form** ([golub2013matrix] (10.5.2), [saad2003iterative]
(6.7)), at every step: `A Q_{k+1} = Q_{k+1} H_{k+1} + w_k e_{k+1}ᵀ`. -/
theorem mul_basisMatrix (k : ℕ) :
    A * basisMatrix A q (k + 1) =
      basisMatrix A q (k + 1) * hessenbergSq (toEuclideanLin A) q (k + 1) +
        vecMulVec (w (toEuclideanLin A) q k).ofLp (Krylov.lastVec 1 (k + 1)) := by
  ext x j
  have := congrArg WithLp.ofLp (apply_vec_eq_sum_add_lastVec (toEuclideanLin A) q k j)
  rw [ofLp_toEuclideanLin] at this
  have hx := congrFun this x
  rw [← col_basisMatrix, ← col_mul_eq_mulVec_col, col_apply] at hx
  rw [hx]
  simp [mul_apply, vecMulVec_apply, Finset.sum_apply, basisMatrix, mul_comm]

/-- The Arnoldi process gives an Arnoldi decomposition of the matrix below the grade:
`Q_{k+1}`, `H_{k+1}`, `w_k` for `k + 1 ≤ grade`. -/
theorem isArnoldiDecomposition_basisMatrix {k : ℕ}
    (hk : k + 1 ≤ Krylov.grade (toEuclideanLin A) q) :
    Matrix.IsArnoldiDecomposition A (basisMatrix A q (k + 1))
      (hessenbergSq (toEuclideanLin A) q (k + 1)) (w (toEuclideanLin A) q k).ofLp := by
  rw [Matrix.isArnoldiDecomposition_iff]
  simpa only [col_basisMatrix, WithLp.toLp_ofLp] using
    isArnoldiDecomposition (toEuclideanLin A) q hk

/-- `Q_kᴴ A Q_k = H_k` below the grade ([golub2013matrix] (10.1.6) and §10.5.1). -/
theorem conjTranspose_basisMatrix_mul_mul_basisMatrix {k : ℕ}
    (hk : k ≤ Krylov.grade (toEuclideanLin A) q) :
    (basisMatrix A q k)ᴴ * A * basisMatrix A q k = hessenbergSq (toEuclideanLin A) q k := by
  cases k with
  | zero => exact Subsingleton.elim _ _
  | succ k => exact (isArnoldiDecomposition_basisMatrix A q hk).conjTranspose_mul_mul

end Arnoldi

/-- **The Lanczos relation in matrix form** ([golub2013matrix] (10.1.4)): for Hermitian `A`,
`A Q_{k+1} = Q_{k+1} T_{k+1} + w_k e_{k+1}ᵀ` with the real tridiagonal `T_{k+1}`. -/
theorem Lanczos.mul_basisMatrix {A : Matrix n n 𝕜} (hA : (toEuclideanLin A).IsSymmetric)
    (q : EuclideanSpace 𝕜 n) (k : ℕ) :
    A * Arnoldi.basisMatrix A q (k + 1) =
      Arnoldi.basisMatrix A q (k + 1) *
          (Lanczos.tridiag (toEuclideanLin A) q (k + 1)).map (algebraMap ℝ 𝕜) +
        vecMulVec (Arnoldi.w (toEuclideanLin A) q k).ofLp (Krylov.lastVec 1 (k + 1)) := by
  rw [← Lanczos.hessenbergSq_eq_map_tridiag (hA := hA)]
  exact Arnoldi.mul_basisMatrix A q k

open scoped ComplexOrder in
/-- **Uniqueness of the Arnoldi process given its first column** (the `k`-step implicit Q theorem
with positive normalization): an Arnoldi decomposition with `k + 1` columns and positive real
subdiagonal *is* the Arnoldi process from its first column `q`: `k + 1 ≤ grade`, `Q = Q_{k+1}`,
`H = H_{k+1}` and `r = w_k`. The engine `Matrix.IsArnoldiDecomposition.implicitQ` compares it with
`Arnoldi.isArnoldiDecomposition_basisMatrix`; both subdiagonals are positive, which forces the
unimodular diagonal to be `1`. -/
theorem Matrix.IsArnoldiDecomposition.eq_basisMatrix {k : ℕ} {A : Matrix n n 𝕜}
    {Q : Matrix n (Fin (k + 1)) 𝕜} {H : Matrix (Fin (k + 1)) (Fin (k + 1)) 𝕜} {r : n → 𝕜}
    (h : IsArnoldiDecomposition A Q H r) (hpos : ∀ i : Fin k, 0 < H i.succ i.castSucc) :
    k + 1 ≤ Krylov.grade (toEuclideanLin A) (WithLp.toLp 2 (Q *ᵥ Pi.single 0 1)) ∧
      Q = Arnoldi.basisMatrix A (WithLp.toLp 2 (Q *ᵥ Pi.single 0 1)) (k + 1) ∧
      H = Arnoldi.hessenbergSq (toEuclideanLin A) (WithLp.toLp 2 (Q *ᵥ Pi.single 0 1)) (k + 1) ∧
      r = (Arnoldi.w (toEuclideanLin A) (WithLp.toLp 2 (Q *ᵥ Pi.single 0 1)) k).ofLp := by
  set q := WithLp.toLp 2 (Q *ᵥ Pi.single 0 1) with hq
  set T := toEuclideanLin A
  have hH : H.IsUnreducedUpperHessenberg :=
    isUnreducedUpperHessenberg_iff_succ.2 ⟨h.isUpperHessenberg, fun i => (hpos i).ne'⟩
  have hop := isArnoldiDecomposition_iff.1 h
  -- the grade
  have hgrade : k + 1 ≤ Krylov.grade T q := by
    have hspan := h.range_eq_subspace hH (le_refl (k + 1))
    have hli : LinearIndependent 𝕜 fun a : Fin (k + 1) =>
        WithLp.toLp 2 (Q.col (Fin.castLE (le_refl (k + 1)) a)) :=
      hop.orthonormal.linearIndependent.comp _ (Fin.castLE_injective _)
    have := congrArg (fun S : Submodule 𝕜 (EuclideanSpace 𝕜 n) => Module.finrank 𝕜 S) hspan
    rw [finrank_span_eq_card hli, Fintype.card_fin, Krylov.finrank_subspace] at this
    exact min_eq_left_iff.1 (this.symm : min (k + 1) (Krylov.grade T q) = k + 1)
  -- the first column is a unit vector
  have hq1 : ‖q‖ = 1 := by
    rw [hq, mulVec_single_one]
    exact hop.orthonormal.1 0
  have hq0 : q ≠ 0 := fun h0 => by simp [h0] at hq1
  have hP := Arnoldi.isArnoldiDecomposition_basisMatrix A q hgrade
  have hfirst : Arnoldi.basisMatrix A q (k + 1) *ᵥ Pi.single 0 1 = Q *ᵥ Pi.single 0 1 := by
    rw [mulVec_single_one, Arnoldi.col_basisMatrix, Fin.val_zero, Arnoldi.vec_zero _ _ hq0, hq1,
      RCLike.ofReal_one, inv_one, one_smul, hq]
  obtain ⟨d, hd1, hd0, hQP, hHP, hrP⟩ := h.implicitQ hP hH hfirst
  -- positivity forces `d = 1`
  have hsub : ∀ i : Fin k, 0 < Arnoldi.hessenbergSq T q (k + 1) i.succ i.castSucc := by
    intro i
    have hlt : (i : ℕ) + 1 < Krylov.grade T q := by have := i.isLt; omega
    change 0 < Arnoldi.coeff T q ((i : ℕ) + 1) i
    rw [Arnoldi.coeff_succ_self, RCLike.ofReal_pos, norm_pos_iff]
    intro hw
    have h0 := (Arnoldi.coeff_succ_self_eq_zero_iff T q i).1
      (by rw [Arnoldi.coeff_succ_self, hw, norm_zero, RCLike.ofReal_zero])
    omega
  have hd : ∀ l, d l = 1 := by
    intro l
    induction l using Fin.induction with
    | zero => exact hd0
    | succ i ih =>
      have he := congrFun (congrFun hHP i.succ) i.castSucc
      rw [star_diagonal_mul_mul_diagonal_apply, ih, mul_one] at he
      obtain ⟨a, ha, hHa⟩ := RCLike.pos_iff_exists_ofReal.1 (hpos i)
      obtain ⟨a', ha', hHa'⟩ := RCLike.pos_iff_exists_ofReal.1 (hsub i)
      rw [← hHa, ← hHa'] at he
      have hstar : star (d i.succ) = ((a' / a : ℝ) : 𝕜) := by
        rw [RCLike.ofReal_div, he, mul_div_assoc, div_self (by exact_mod_cast ha.ne'), mul_one]
      have hn : ‖star (d i.succ)‖ = 1 := by rw [norm_star, hd1]
      rw [hstar, RCLike.norm_ofReal, abs_of_pos (div_pos ha' ha)] at hn
      rw [← star_star (d i.succ), hstar, hn, RCLike.ofReal_one, star_one]
  have hD : diagonal d = 1 := by rw [show d = fun _ => 1 from funext hd, diagonal_one]
  rw [hD, Matrix.mul_one] at hQP
  rw [hD, star_one, Matrix.one_mul, Matrix.mul_one] at hHP
  rw [hd, one_smul] at hrP
  exact ⟨hgrade, hQP.symm, hHP.symm, hrP.symm⟩

end MatrixForm

/-! ### Hessenberg reduction with a prescribed last column -/

section LastCol

/-- The Householder reduction to Hessenberg form fixes the first unit vector: all its reflectors
act on the coordinates `≥ 1`. (Belongs with `Matrix.hessenbergQ` in
`Numlib/LinearAlgebra/Matrix/QR`.) -/
theorem Matrix.hessenbergQ_mulVec_single_zero {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) 𝕜) :
    hessenbergQ A *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  have hstep : ∀ (B : Matrix (Fin (N + 1)) (Fin (N + 1)) 𝕜) (k : ℕ),
      hessenbergReflector B k *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    intro B k
    by_cases hk : k < N + 1
    · rw [hessenbergReflector_of_lt B hk]
      refine householder_mulVec_eq_self_of_apply_eq_zero fun r hr => ?_
      have hr0 : r ≠ 0 := by
        rintro rfl
        exact hr (householderTail_apply_of_lt _ (by simp))
      exact Pi.single_eq_of_ne hr0 _
    · rw [hessenbergReflector_of_le B (not_lt.1 hk), one_mulVec]
  have hiter : ∀ k, hessenbergQIter A k *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    intro k
    induction k with
    | zero => rw [hessenbergQIter_zero, one_mulVec]
    | succ k ih => rw [hessenbergQIter_succ, ← mulVec_mulVec, hstep, ih]
  exact hiter _

/-- **Hessenberg reduction with a prescribed last column** ([golub2013matrix] P10.5.2, cited in
§10.5.4): for `C` and `u` there is a unitary `Z` with `Zᴴ C Z` upper Hessenberg and
`Zᴴ u = τ e_last`. A reflector `P` sends `u` to a multiple of `e₀`; the Householder reduction
`Q` of `Pᴴ Cᴴ P` fixes `e₀`, so `W = P Q` has `Wᴴ u ∥ e₀` and `Wᴴ Cᴴ W` upper Hessenberg, i.e.
`Wᴴ C W` lower Hessenberg; reversing the order of the columns of `W` turns lower into upper
Hessenberg and `e₀` into `e_last`. -/
theorem Matrix.exists_isUpperHessenberg_conj_lastCol {j : ℕ}
    (C : Matrix (Fin (j + 1)) (Fin (j + 1)) 𝕜) (u : Fin (j + 1) → 𝕜) :
    ∃ Z ∈ unitaryGroup (Fin (j + 1)) 𝕜, (star Z * C * Z).IsUpperHessenberg ∧
      ∃ τ : 𝕜, star Z *ᵥ u = Pi.single (Fin.last j) τ := by
  obtain ⟨P, hP, hPH, α, hPu⟩ : ∃ P ∈ unitaryGroup (Fin (j + 1)) 𝕜, Pᴴ = P ∧
      ∃ α : 𝕜, P *ᵥ u = α • Pi.single 0 1 := by
    by_cases hu : u = 0
    · exact ⟨1, one_mem _, conjTranspose_one, 0, by rw [hu, mulVec_zero, zero_smul]⟩
    · exact ⟨_, householder_householderVec_mem_unitaryGroup hu 0, isHermitian_householder _, _,
        householder_mulVec_eq_smul_single hu 0⟩
  set B := Pᴴ * Cᴴ * P with hB
  have hQ := hessenbergQ_mem_unitaryGroup B
  set W := P * hessenbergQ B with hWdef
  have hW : W ∈ unitaryGroup (Fin (j + 1)) 𝕜 := mul_mem hP hQ
  have hG : (Wᴴ * Cᴴ * W).IsUpperHessenberg := by
    have : Wᴴ * Cᴴ * W = hessenbergReduce B := by
      rw [hessenbergReduce_eq_conj, hWdef, hB, conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [this]
    exact isUpperHessenberg_hessenbergReduce B
  have hWu : Wᴴ *ᵥ u = α • Pi.single 0 1 := by
    have hQe : (hessenbergQ B)ᴴ *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
      conv_lhs => rw [← hessenbergQ_mulVec_single_zero B]
      rw [mulVec_mulVec, ← star_eq_conjTranspose, (mem_unitaryGroup_iff').1 hQ, one_mulVec]
    rw [hWdef, conjTranspose_mul, ← mulVec_mulVec, hPH, hPu, mulVec_smul, hQe]
  refine ⟨W.submatrix id Fin.rev, ?_, ?_, α, ?_⟩
  · rw [mem_unitaryGroup_iff', star_eq_conjTranspose, conjTranspose_submatrix,
      ← submatrix_mul _ _ _ id _ Function.bijective_id, ← star_eq_conjTranspose,
      (mem_unitaryGroup_iff').1 hW, submatrix_one _ Fin.rev_injective]
  · have hconj : star (W.submatrix id Fin.rev) * C * W.submatrix id Fin.rev =
        (Wᴴ * Cᴴ * W)ᴴ.submatrix Fin.rev Fin.rev := by
      have h1 : (Wᴴ * Cᴴ * W)ᴴ = Wᴴ * C * W := by
        simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      rw [h1, star_eq_conjTranspose, conjTranspose_submatrix]
      ext a b
      simp only [mul_apply, submatrix_apply, id_eq]
    rw [hconj, isUpperHessenberg_iff_fin]
    intro a b hab
    rw [submatrix_apply, conjTranspose_apply, (isUpperHessenberg_iff_fin.1 hG) _ _
      (by have := a.isLt; have := b.isLt; simp only [Fin.val_rev]; omega), star_zero]
  · ext i
    have := congrFun hWu (Fin.rev i)
    change (Wᴴ *ᵥ u) (Fin.rev i) = _
    rw [this, Pi.smul_apply, smul_eq_mul]
    by_cases hi : i = Fin.last j
    · subst hi
      rw [Fin.rev_last, Pi.single_eq_same, Pi.single_eq_same, mul_one]
    · have hr : Fin.rev i ≠ 0 := fun h => hi (by rw [← Fin.rev_rev i, h, Fin.rev_zero])
      rw [Pi.single_eq_of_ne hr, Pi.single_eq_of_ne hi, mul_zero]

end LastCol

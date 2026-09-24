/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.RCLike.Basic
import Numlib.LinearAlgebra.Matrix.UnreducedHessenberg

/-!
# Krylov and Arnoldi decompositions, and the implicit Q theorem

A *Krylov decomposition* (Stewart) of a square matrix `A` is an identity
`A Q = Q B + r bᵀ` in which `Q` has orthonormal columns and the residual `r` is orthogonal to
them; an *Arnoldi decomposition* is the case of an upper Hessenberg `B = H` and `b = e_last`
([golub2013matrix] §10.5.1, the definition after (10.5.2)). A unitary reduction `Qᴴ A Q = H` to
Hessenberg form is an Arnoldi decomposition with zero residual, and so are its leading columns
with residual `h_{j+1,j} q_{j+1}`; the Arnoldi process produces one at every step
(`Numlib/Krylov/Decomposition`).

## Main definitions

* `Matrix.IsKrylovDecomposition A Q B r b`: `Qᴴ Q = 1`, `Qᴴ r = 0` and `A Q = Q B + r bᵀ`.
* `Matrix.IsArnoldiDecomposition A Q H r`: a Krylov decomposition with `k + 1` columns, `H` upper
  Hessenberg and `b = Pi.single (Fin.last k) 1`. The column count is `k + 1` so that the last
  unit vector and the first column `Q *ᵥ Pi.single 0 1` are well typed.

## Main results

* `Matrix.IsKrylovDecomposition.conjTranspose_mul_mul`: `B = Qᴴ A Q`.
* `Matrix.IsKrylovDecomposition.mul_unitary`: a change of basis `Q ↦ Q U`, `B ↦ Uᴴ B U`
  ([golub2013matrix] (10.5.9), §10.5.4).
* `Matrix.IsKrylovDecomposition.leading`: truncation to the leading `j + 1` columns, the residual
  collecting what the discarded columns contributed to column `j` — the one lemma behind implicit
  restarting, Krylov–Schur restarting and the square implicit Q theorem.
* `Matrix.IsArnoldiDecomposition.implicitQ`: **the implicit Q theorem**, once, for decompositions
  with any number of columns: two Arnoldi decompositions of `A` with the same first column, the
  first with unreduced `H`, agree up to a unimodular diagonal, `Q' = Q D`, `H' = Dᴴ H D`,
  `r' = d_k r`. The proof is the column recursion of [golub2013matrix] Theorem 7.4.2:
  `h_{i+1,i} q_{i+1} = A q_i − ∑_{l ≤ i} h_{l,i} q_l` for `i < k`.
* The square theorems of [golub2013matrix] Theorem 7.4.2, as corollaries:
  `Matrix.implicitQ_of_apply_eq_zero` (the book's form, with the first vanishing subdiagonal
  entry), `Matrix.implicitQ` (the unreduced case), and their real forms
  `Matrix.implicitQ_of_apply_eq_zero_real`, `Matrix.implicitQ_real`.

## Implementation notes

The predicates are pure matrix statements over `[RCLike 𝕜]`; the operator-level predicates on an
orthonormal family in an inner product space are `Krylov.IsKrylovDecomposition` and
`Krylov.IsArnoldiDecomposition` of `Numlib/Krylov/Decomposition`, which proves that these are their
`toEuclideanLin` instances. The implicit Q theorem needs neither a square `Q` nor a unitary
`Vᴴ Q`: orthonormal columns and the Hessenberg shape carry the induction.
-/

open Finset

namespace Matrix

/-- A submatrix of an upper Hessenberg matrix along a strictly monotone reindexing is upper
Hessenberg. (Belongs with `Matrix.IsUpperHessenberg` in `Numlib/LinearAlgebra/Matrix/Hessenberg`.)
-/
theorem IsUpperHessenberg.submatrix_of_strictMono {n m R : Type*} [LinearOrder n] [LinearOrder m]
    [Zero R] {H : Matrix n n R} (hH : H.IsUpperHessenberg) {f : m → n} (hf : StrictMono f) :
    (H.submatrix f f).IsUpperHessenberg :=
  fun _ _ ⟨c, hjc, hci⟩ => hH _ _ ⟨f c, hf hjc, hf hci⟩

/-- Splitting a sum over `Fin k` at `j`: the leading `j + 1` indices, read through `Fin.castLE`,
and the indices after `j`. -/
theorem sum_fin_eq_sum_castLE_add_sum_Ioi {M : Type*} [AddCommMonoid M] {k : ℕ} (j : Fin k)
    (g : Fin k → M) :
    ∑ i, g i = ∑ a : Fin (j + 1), g (Fin.castLE j.isLt a) + ∑ i ∈ Ioi j, g i := by
  rw [← sum_filter_add_sum_filter_not univ (· ≤ j)]
  congr 1
  · refine (sum_bij (fun a _ => Fin.castLE j.isLt a) (fun a _ => ?_)
      (fun a _ b _ hab => Fin.castLE_injective _ hab) (fun i hi => ?_) (fun _ _ => rfl)).symm
    · simp only [mem_filter, mem_univ, true_and, Fin.le_def, Fin.val_castLE]
      have := a.isLt
      omega
    · simp only [mem_filter, mem_univ, true_and, Fin.le_def] at hi
      exact ⟨⟨i, by omega⟩, mem_univ _, Fin.ext (by simp)⟩
  · refine sum_congr ?_ fun _ _ => rfl
    ext i
    simp

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

/-- A scalar with `star c * c = 1` has norm `1`. -/
theorem _root_.RCLike.norm_eq_one_of_star_mul_self_eq_one {c : 𝕜} (hc : star c * c = 1) :
    ‖c‖ = 1 := by
  have h1 : ‖star c * c‖ = 1 := by rw [hc, norm_one]
  rw [norm_mul, norm_star] at h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg c) two_ne_zero).1 (by rw [sq]; exact h1)

/-- The entries of `Dᴴ M D` for a diagonal `D = diagonal d`: `star (d i) * M i j * d j`. -/
theorem star_diagonal_mul_mul_diagonal_apply {m : Type*} [Fintype m] [DecidableEq m]
    (d : m → 𝕜) (M : Matrix m m 𝕜) (i j : m) :
    (star (diagonal d) * M * diagonal d) i j = star (d i) * M i j * d j := by
  rw [mul_diagonal, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul, Pi.star_apply]

/-! ### Krylov decompositions -/

section Krylov

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- A **Krylov decomposition** (Stewart; [golub2013matrix] §10.5.4) `A Q = Q B + r bᵀ` of
`A : Matrix n n 𝕜`: `Q` has orthonormal columns, the residual `r` is orthogonal to them, and
`B`, `b` are arbitrary. -/
structure IsKrylovDecomposition (A : Matrix n n 𝕜) (Q : Matrix n m 𝕜) (B : Matrix m m 𝕜)
    (r : n → 𝕜) (b : m → 𝕜) : Prop where
  /-- The columns of `Q` are orthonormal. -/
  conjTranspose_mul_self : Qᴴ * Q = 1
  /-- The residual is orthogonal to the columns of `Q`. -/
  conjTranspose_mulVec : Qᴴ *ᵥ r = 0
  /-- The decomposition itself. -/
  mul_eq : A * Q = Q * B + vecMulVec r b

namespace IsKrylovDecomposition

variable {A : Matrix n n 𝕜} {Q : Matrix n m 𝕜} {B : Matrix m m 𝕜} {r : n → 𝕜} {b : m → 𝕜}

/-- The columns of `Q` are orthonormal, entrywise: `⟪q_i, q_j⟫ = δ_ij`. -/
theorem star_col_dotProduct_col (h : IsKrylovDecomposition A Q B r b) (i j : m) :
    star (Q.col i) ⬝ᵥ Q.col j = (1 : Matrix m m 𝕜) i j := by
  rw [← h.conjTranspose_mul_self, mul_apply]
  rfl

/-- The residual is orthogonal to every column of `Q`. -/
theorem star_col_dotProduct_residual (h : IsKrylovDecomposition A Q B r b) (i : m) :
    star (Q.col i) ⬝ᵥ r = 0 :=
  congrFun h.conjTranspose_mulVec i

/-- Column `j` of the decomposition: `A q_j = ∑ᵢ B i j q_i + b_j r`. -/
theorem mulVec_col (h : IsKrylovDecomposition A Q B r b) (j : m) :
    A *ᵥ Q.col j = ∑ i, B i j • Q.col i + b j • r := by
  have hc := congrArg (fun M : Matrix n m 𝕜 => M.col j) h.mul_eq
  simp only [col_mul_eq_mulVec_col] at hc
  rw [hc]
  ext x
  simp [mul_apply, vecMulVec_apply, Finset.sum_apply, mul_comm]

/-- The entries of `B` are those of the compression: `B i j = ⟪q_i, A q_j⟫`. -/
theorem apply_eq_star_col_dotProduct (h : IsKrylovDecomposition A Q B r b) (i j : m) :
    B i j = star (Q.col i) ⬝ᵥ (A *ᵥ Q.col j) := by
  rw [h.mulVec_col, dotProduct_add, dotProduct_sum, dotProduct_smul,
    h.star_col_dotProduct_residual]
  simp [dotProduct_smul, h.star_col_dotProduct_col, one_apply]

/-- `B = Qᴴ A Q`: the matrix of a Krylov decomposition is the compression of `A`. -/
theorem conjTranspose_mul_mul (h : IsKrylovDecomposition A Q B r b) : Qᴴ * A * Q = B := by
  rw [Matrix.mul_assoc, h.mul_eq, Matrix.mul_add, ← Matrix.mul_assoc, h.conjTranspose_mul_self,
    Matrix.one_mul, mul_vecMulVec, h.conjTranspose_mulVec, zero_vecMulVec, add_zero]

/-- **Change of basis** ([golub2013matrix] (10.5.9) and §10.5.4): for a unitary `U`,
`A (Q U) = (Q U) (Uᴴ B U) + r (Uᵀ b)ᵀ` is again a Krylov decomposition. -/
theorem mul_unitary (h : IsKrylovDecomposition A Q B r b) {U : Matrix m m 𝕜}
    (hU : Uᴴ * U = 1) : IsKrylovDecomposition A (Q * U) (Uᴴ * B * U) r (b ᵥ* U) where
  conjTranspose_mul_self := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Qᴴ, h.conjTranspose_mul_self,
      Matrix.one_mul, hU]
  conjTranspose_mulVec := by
    rw [conjTranspose_mul, ← mulVec_mulVec, h.conjTranspose_mulVec, mulVec_zero]
  mul_eq := by
    have hU' : U * Uᴴ = 1 := mul_eq_one_comm.1 hU
    rw [← Matrix.mul_assoc, h.mul_eq, Matrix.add_mul, vecMulVec_mul]
    congr 1
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc Q U Uᴴ, hU', Matrix.mul_one]

/-- **Truncation to the leading `j + 1` columns.** If the entries of `B` below row `j` vanish in
the columns before `j`, and so do those of `b`, then the leading `j + 1` columns form a Krylov
decomposition with `b = e_last`, whose residual collects what the discarded columns contributed to
column `j`: `r' = ∑_{i > j} B i j q_i + b_j r`. For a Hessenberg `B` the first hypothesis always
holds and `r' = B (j+1) j q_{j+1} + b_j r`. -/
theorem leading {k : ℕ} {Q : Matrix n (Fin k) 𝕜} {B : Matrix (Fin k) (Fin k) 𝕜}
    {b : Fin k → 𝕜} (h : IsKrylovDecomposition A Q B r b) (j : Fin k)
    (hB : ∀ i l : Fin k, l < j → j < i → B i l = 0) (hb : ∀ l : Fin k, l < j → b l = 0) :
    IsKrylovDecomposition A (Q.submatrix id (Fin.castLE j.isLt))
      (B.submatrix (Fin.castLE j.isLt) (Fin.castLE j.isLt))
      (∑ i ∈ Ioi j, B i j • Q.col i + b j • r) (Pi.single (Fin.last j) 1) where
  conjTranspose_mul_self := by
    rw [conjTranspose_submatrix, ← submatrix_mul _ _ _ id _ Function.bijective_id,
      h.conjTranspose_mul_self, submatrix_one _ (Fin.castLE_injective _)]
  conjTranspose_mulVec := by
    ext a
    change star (Q.col (Fin.castLE j.isLt a)) ⬝ᵥ _ = 0
    rw [dotProduct_add, dotProduct_sum, dotProduct_smul, h.star_col_dotProduct_residual,
      smul_zero, add_zero]
    refine sum_eq_zero fun i hi => ?_
    rw [dotProduct_smul, h.star_col_dotProduct_col, one_apply_ne, smul_zero]
    intro hai
    have hi' := mem_Ioi.1 hi
    rw [← hai, Fin.lt_def, Fin.val_castLE] at hi'
    have := a.isLt
    omega
  mul_eq := by
    ext x a
    have hcol := congrFun (congrFun h.mul_eq x) (Fin.castLE j.isLt a)
    simp only [mul_apply, add_apply, vecMulVec_apply, submatrix_apply, id] at hcol ⊢
    rw [hcol, sum_fin_eq_sum_castLE_add_sum_Ioi j (fun i => Q x i * B i (Fin.castLE j.isLt a)),
      add_assoc]
    congr 1
    by_cases ha : a = Fin.last j
    · have hf : Fin.castLE j.isLt (Fin.last j) = j := Fin.ext (by simp)
      rw [ha, Pi.single_eq_same, mul_one, hf, Pi.add_apply, Finset.sum_apply]
      simp [mul_comm]
    · have hlt : Fin.castLE j.isLt a < j := by
        rw [Fin.lt_def, Fin.val_castLE]; exact Fin.val_lt_last ha
      rw [Pi.single_eq_of_ne ha, mul_zero, hb _ hlt, mul_zero, add_zero]
      exact sum_eq_zero fun i hi => by rw [hB i _ hlt (mem_Ioi.1 hi), mul_zero]

end IsKrylovDecomposition

/-- A unitary `Q` gives a Krylov decomposition with zero residual: `A Q = Q (Qᴴ A Q)`. -/
theorem isKrylovDecomposition_of_mem_unitaryGroup {Q : Matrix m m 𝕜}
    (hQ : Q ∈ unitaryGroup m 𝕜) (A : Matrix m m 𝕜) (b : m → 𝕜) :
    IsKrylovDecomposition A Q (star Q * A * Q) 0 b where
  conjTranspose_mul_self := (mem_unitaryGroup_iff').1 hQ
  conjTranspose_mulVec := mulVec_zero _
  mul_eq := by
    rw [zero_vecMulVec, add_zero, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      (mem_unitaryGroup_iff).1 hQ, Matrix.one_mul]

end Krylov

/-! ### Arnoldi decompositions and the implicit Q theorem -/

section Arnoldi

/-- An **Arnoldi decomposition** with `k + 1` columns ([golub2013matrix] §10.5.1, the definition
after (10.5.2)): a Krylov decomposition `A Q = Q H + r e_lastᵀ` with `H` upper Hessenberg. The
book's `k`-step decomposition is the case `k = k' + 1` of this one. -/
structure IsArnoldiDecomposition {k : ℕ} (A : Matrix n n 𝕜) (Q : Matrix n (Fin (k + 1)) 𝕜)
    (H : Matrix (Fin (k + 1)) (Fin (k + 1)) 𝕜) (r : n → 𝕜) : Prop
    extends IsKrylovDecomposition A Q H r (Pi.single (Fin.last k) 1) where
  /-- The coefficient matrix is upper Hessenberg. -/
  isUpperHessenberg : H.IsUpperHessenberg

/-- The leading `j + 1` columns of a Krylov decomposition with Hessenberg `B` (and `b` vanishing
before `j`) form an Arnoldi decomposition. -/
theorem IsKrylovDecomposition.isArnoldiDecomposition_leading {k : ℕ} {A : Matrix n n 𝕜}
    {Q : Matrix n (Fin k) 𝕜} {B : Matrix (Fin k) (Fin k) 𝕜} {r : n → 𝕜} {b : Fin k → 𝕜}
    (h : IsKrylovDecomposition A Q B r b) (hB : B.IsUpperHessenberg) (j : Fin k)
    (hb : ∀ l : Fin k, l < j → b l = 0) :
    IsArnoldiDecomposition A (Q.submatrix id (Fin.castLE j.isLt))
      (B.submatrix (Fin.castLE j.isLt) (Fin.castLE j.isLt))
      (∑ i ∈ Ioi j, B i j • Q.col i + b j • r) where
  toIsKrylovDecomposition := h.leading j (fun i l hl hi => hB i l ⟨j, hl, hi⟩) hb
  isUpperHessenberg := hB.submatrix_of_strictMono fun _ _ hab => by
    rw [Fin.lt_def, Fin.val_castLE, Fin.val_castLE]; exact hab

/-- A unitary reduction to Hessenberg form is an Arnoldi decomposition with zero residual. -/
theorem isArnoldiDecomposition_of_mem_unitaryGroup {N : ℕ}
    {Q : Matrix (Fin (N + 1)) (Fin (N + 1)) 𝕜} (hQ : Q ∈ unitaryGroup (Fin (N + 1)) 𝕜)
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) 𝕜} (hH : (star Q * A * Q).IsUpperHessenberg) :
    IsArnoldiDecomposition A Q (star Q * A * Q) 0 :=
  ⟨isKrylovDecomposition_of_mem_unitaryGroup hQ A _, hH⟩

namespace IsArnoldiDecomposition

variable {k : ℕ} {A : Matrix n n 𝕜} {Q : Matrix n (Fin (k + 1)) 𝕜}
  {H : Matrix (Fin (k + 1)) (Fin (k + 1)) 𝕜} {r : n → 𝕜}

/-- The Arnoldi recurrence read off column `i < k` of an Arnoldi decomposition:
`h_{i+1,i} q_{i+1} = A q_i − ∑_{l ≤ i} h_{l,i} q_l`. -/
theorem smul_col_succ (h : IsArnoldiDecomposition A Q H r) (i : Fin k) :
    H i.succ i.castSucc • Q.col i.succ =
      A *ᵥ Q.col i.castSucc - ∑ l ∈ Iic i.castSucc, H l i.castSucc • Q.col l := by
  rw [h.mulVec_col, Pi.single_eq_of_ne (Fin.castSucc_lt_last i).ne, zero_smul, add_zero,
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

/-- **The implicit Q theorem for Arnoldi decompositions** — the one uniqueness engine
([golub2013matrix] Theorem 7.4.2 and §10.5.1, in `k`-step form). Two Arnoldi decompositions of the
same `A` with `k + 1` columns and the same first column, the first with unreduced `H`, agree up to
a unimodular diagonal `D = diagonal d` with `d 0 = 1`: `Q' = Q D`, `H' = Dᴴ H D`, `r' = d_k r`.

By induction on `i`, `q'_l = d_l q_l` for `l ≤ i` gives `h'_{l,i} = conj (d_l) h_{l,i} d_i`, so the
recurrences `h_{i+1,i} q_{i+1} = A q_i − ∑_{l ≤ i} h_{l,i} q_l` for `Q` and `Q'` give
`h'_{i+1,i} q'_{i+1} = d_i h_{i+1,i} q_{i+1}` with a nonzero right side; both are unit vectors. -/
theorem implicitQ {Q' : Matrix n (Fin (k + 1)) 𝕜} {H' : Matrix (Fin (k + 1)) (Fin (k + 1)) 𝕜}
    {r' : n → 𝕜} (h : IsArnoldiDecomposition A Q H r) (h' : IsArnoldiDecomposition A Q' H' r')
    (hH : H.IsUnreducedUpperHessenberg) (h0 : Q' *ᵥ Pi.single 0 1 = Q *ᵥ Pi.single 0 1) :
    ∃ d : Fin (k + 1) → 𝕜, (∀ i, ‖d i‖ = 1) ∧ d 0 = 1 ∧ Q' = Q * diagonal d ∧
      H' = star (diagonal d) * H * diagonal d ∧ r' = d (Fin.last k) • r := by
  set d : Fin (k + 1) → 𝕜 := fun l => star (Q.col l) ⬝ᵥ Q'.col l with hd
  have hq0 : Q'.col 0 = Q.col 0 := by rwa [← mulVec_single_one, ← mulVec_single_one]
  have hd0 : d 0 = 1 := by
    simp only [hd]
    rw [hq0, h.star_col_dotProduct_col, one_apply_eq]
  have key : ∀ t : ℕ, ∀ l : Fin (k + 1), (l : ℕ) ≤ t →
      Q'.col l = d l • Q.col l ∧ star (d l) * d l = 1 := by
    intro t
    induction t with
    | zero =>
      intro l hl
      obtain rfl : l = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
      rw [hd0, one_smul, star_one, one_mul]
      exact ⟨hq0, rfl⟩
    | succ t ih =>
      intro l hl
      rcases Nat.lt_or_ge (l : ℕ) (t + 1) with hlt | hge
      · exact ih l (by omega)
      have htk : t < k := by have := l.isLt; omega
      set i : Fin k := ⟨t, htk⟩ with hi
      obtain rfl : l = i.succ := Fin.ext (by simp [hi]; omega)
      have ihc : ∀ l ∈ Iic i.castSucc, Q'.col l = d l • Q.col l ∧ star (d l) * d l = 1 :=
        fun l hl => ih l (by
          have := Fin.le_def.1 (mem_Iic.1 hl); simp only [Fin.val_castSucc] at this; omega)
      obtain ⟨hqc, hdc⟩ := ihc i.castSucc (mem_Iic.2 le_rfl)
      -- the coefficients of the second decomposition
      have hH' : ∀ l ∈ Iic i.castSucc,
          H' l i.castSucc = star (d l) * d i.castSucc * H l i.castSucc := by
        intro l hl
        rw [h'.apply_eq_star_col_dotProduct, h.apply_eq_star_col_dotProduct, (ihc l hl).1, hqc,
          star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
          mul_assoc]
      have hsum : ∑ l ∈ Iic i.castSucc, H' l i.castSucc • Q'.col l =
          d i.castSucc • ∑ l ∈ Iic i.castSucc, H l i.castSucc • Q.col l := by
        rw [smul_sum]
        refine sum_congr rfl fun l hl => ?_
        rw [hH' l hl, (ihc l hl).1, smul_smul, smul_smul]
        congr 1
        calc star (d l) * d i.castSucc * H l i.castSucc * d l
            = d i.castSucc * H l i.castSucc * (star (d l) * d l) := by ring
          _ = d i.castSucc * H l i.castSucc := by rw [(ihc l hl).2, mul_one]
      have hrec : H' i.succ i.castSucc • Q'.col i.succ =
          (d i.castSucc * H i.succ i.castSucc) • Q.col i.succ := by
        rw [h'.smul_col_succ, hsum, hqc, mulVec_smul, ← smul_sub, ← h.smul_col_succ, smul_smul]
      have hc0 : d i.castSucc * H i.succ i.castSucc ≠ 0 := by
        refine mul_ne_zero (fun h0 => ?_) (hH.apply_succ_castSucc_ne_zero i)
        rw [h0, mul_zero] at hdc
        exact zero_ne_one hdc
      -- dot the recurrence with `q_{i+1}`
      have hdot : H' i.succ i.castSucc * d i.succ = d i.castSucc * H i.succ i.castSucc := by
        have := congrArg (star (Q.col i.succ) ⬝ᵥ ·) hrec
        simp only [dotProduct_smul, smul_eq_mul, h.star_col_dotProduct_col, one_apply_eq,
          mul_one] at this
        exact this
      have hH'0 : H' i.succ i.castSucc ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hdot
        exact hc0 hdot.symm
      have hq : Q'.col i.succ = d i.succ • Q.col i.succ := by
        rw [← hdot, ← smul_smul] at hrec
        exact smul_right_injective _ hH'0 hrec
      refine ⟨hq, ?_⟩
      have := h'.star_col_dotProduct_col i.succ i.succ
      rw [hq, star_smul, smul_dotProduct, dotProduct_smul, h.star_col_dotProduct_col,
        one_apply_eq, smul_eq_mul, smul_eq_mul, mul_one] at this
      exact this
  have hcol : ∀ l, Q'.col l = d l • Q.col l := fun l => (key l l le_rfl).1
  have hunit : ∀ l, star (d l) * d l = 1 := fun l => (key l l le_rfl).2
  have hQ' : Q' = Q * diagonal d := by
    ext x l
    rw [mul_diagonal]
    have := congrFun (hcol l) x
    simpa [mul_comm] using this
  have hH' : H' = star (diagonal d) * H * diagonal d := by
    rw [← h'.conjTranspose_mul_mul, ← h.conjTranspose_mul_mul, hQ', conjTranspose_mul,
      star_eq_conjTranspose]
    simp only [Matrix.mul_assoc]
  refine ⟨d, fun l => RCLike.norm_eq_one_of_star_mul_self_eq_one (hunit l), hd0, hQ', hH', ?_⟩
  -- the residuals
  have hDD : diagonal d * star (diagonal d) = 1 := by
    rw [star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext l
    rw [Pi.star_apply, mul_comm]
    exact hunit l
  have hr : vecMulVec r' (Pi.single (Fin.last k) 1) =
      vecMulVec r (Pi.single (Fin.last k) 1) * diagonal d := by
    rw [eq_sub_of_add_eq' h'.mul_eq.symm, eq_sub_of_add_eq' h.mul_eq.symm, hQ', hH',
      Matrix.sub_mul]
    congr 1
    · rw [Matrix.mul_assoc]
    · simp only [← Matrix.mul_assoc]
      rw [Matrix.mul_assoc Q (diagonal d) (star (diagonal d)), hDD, Matrix.mul_one]
  rw [vecMulVec_mul, single_vecMul_diagonal, one_mul] at hr
  ext x
  have := congrFun (congrFun hr x) (Fin.last k)
  simpa [vecMulVec_apply, mul_comm] using this

/-- For `i ≤ k`, `A^i q_0 = Q H^i e_0`: the residual term of `A Q = Q H + r e_kᵀ` does not reach
`H^i e_0`, which is supported on the first `i + 1` coordinates. -/
theorem pow_mulVec_first [DecidableEq n] (h : IsArnoldiDecomposition A Q H r) {i : ℕ}
    (hi : i ≤ k) : A ^ i *ᵥ (Q *ᵥ Pi.single 0 1) = Q *ᵥ (H ^ i *ᵥ Pi.single 0 1) := by
  induction i with
  | zero => rw [pow_zero, pow_zero, one_mulVec, one_mulVec]
  | succ i ih =>
    have hlast : (H ^ i *ᵥ Pi.single 0 1) (Fin.last k) = 0 :=
      h.isUpperHessenberg.pow_mulVec_single_zero_apply_of_lt (by simp only [Fin.val_last]; omega)
    calc A ^ (i + 1) *ᵥ (Q *ᵥ Pi.single 0 1) = A *ᵥ (A ^ i *ᵥ (Q *ᵥ Pi.single 0 1)) := by
          rw [pow_succ', ← mulVec_mulVec]
      _ = A *ᵥ (Q *ᵥ (H ^ i *ᵥ Pi.single 0 1)) := by rw [ih (by omega)]
      _ = (A * Q) *ᵥ (H ^ i *ᵥ Pi.single 0 1) := mulVec_mulVec _ _ _
      _ = Q *ᵥ (H *ᵥ (H ^ i *ᵥ Pi.single 0 1)) := by
          rw [h.mul_eq, add_mulVec, vecMulVec_mulVec, single_one_dotProduct, hlast,
            MulOpposite.op_zero, zero_smul, add_zero]
          exact (mulVec_mulVec _ Q H).symm
      _ = Q *ᵥ (H ^ (i + 1) *ᵥ Pi.single 0 1) := by rw [pow_succ', ← mulVec_mulVec]

/-- **Polynomial filtering of the first column** ([golub2013matrix] §10.5.3, "`(A − μI) Q_c e₁ =
Q_c (H_c − μI) e₁` … and so `q₊ = p(A) q₁`"): for an Arnoldi decomposition with `k + 1` columns
and a polynomial of degree at most `k`, `p(A) (Q e₀) = Q (p(H) e₀)`. -/
theorem aeval_mulVec_first [DecidableEq n] (h : IsArnoldiDecomposition A Q H r)
    {p : Polynomial 𝕜} (hp : p.natDegree ≤ k) :
    Polynomial.aeval A p *ᵥ (Q *ᵥ Pi.single 0 1) =
      Q *ᵥ (Polynomial.aeval H p *ᵥ Pi.single 0 1) := by
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, sum_mulVec, sum_mulVec,
    mulVec_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [smul_mulVec, smul_mulVec, mulVec_smul,
    h.pow_mulVec_first (by have := mem_range.1 hi; omega)]

end IsArnoldiDecomposition

end Arnoldi

/-! ### The square implicit Q theorems -/

section Square

variable {N : ℕ} {A Q V : Matrix (Fin (N + 1)) (Fin (N + 1)) 𝕜}

/-- **The implicit Q theorem**, unreduced case ([golub2013matrix] Theorem 7.4.2 and the remark
after it: `G` and `H` are "essentially equal"): if `Q`, `V` are unitary with the same first column,
`H = Qᴴ A Q` is unreduced upper Hessenberg and `G = Vᴴ A V` is upper Hessenberg, then
`V = Q D` and `G = Dᴴ H D` for a unimodular diagonal `D` with `d 0 = 1`. -/
theorem implicitQ (hQ : Q ∈ unitaryGroup (Fin (N + 1)) 𝕜) (hV : V ∈ unitaryGroup (Fin (N + 1)) 𝕜)
    (hH : (star Q * A * Q).IsUnreducedUpperHessenberg) (hG : (star V * A * V).IsUpperHessenberg)
    (h0 : V.col 0 = Q.col 0) :
    ∃ d : Fin (N + 1) → 𝕜, (∀ i, ‖d i‖ = 1) ∧ d 0 = 1 ∧ V = Q * diagonal d ∧
      star V * A * V = star (diagonal d) * (star Q * A * Q) * diagonal d := by
  obtain ⟨d, hd1, hd0, hVQ, hGH, -⟩ :=
    (isArnoldiDecomposition_of_mem_unitaryGroup hQ hH.1).implicitQ
      (isArnoldiDecomposition_of_mem_unitaryGroup hV hG) hH
      (by rw [mulVec_single_one, mulVec_single_one, h0])
  exact ⟨d, hd1, hd0, hVQ, hGH⟩

/-- [golub2013matrix] **Theorem 7.4.2 (implicit Q theorem)**, the book's form: let `Q`, `V` be
unitary with the same first column, `H = Qᴴ A Q` and `G = Vᴴ A V` upper Hessenberg, and let the
first `k` subdiagonal entries of `H` be nonzero (`k ≤ N`). Then
(a) the columns `i ≤ k` of `V` are unimodular multiples of those of `Q`;
(b) `|g_{i+1,i}| = |h_{i+1,i}|` for `i < k`;
(c) if `h_{k+1,k} = 0` then `g_{k+1,k} = 0`.
(The book takes `k` to be the first index with `h_{k+1,k} = 0`, and indexes from `1`.) The leading
`k + 1` columns of both reductions are Arnoldi decompositions (`IsKrylovDecomposition.leading`),
with residuals `h_{k+1,k} q_{k+1}` and `g_{k+1,k} v_{k+1}`, and the engine
`Matrix.IsArnoldiDecomposition.implicitQ` compares them. -/
theorem implicitQ_of_apply_eq_zero (hQ : Q ∈ unitaryGroup (Fin (N + 1)) 𝕜)
    (hV : V ∈ unitaryGroup (Fin (N + 1)) 𝕜) (hH : (star Q * A * Q).IsUpperHessenberg)
    (hG : (star V * A * V).IsUpperHessenberg) (h0 : V.col 0 = Q.col 0) {k : ℕ} (hk : k ≤ N)
    (hsub : ∀ i : Fin N, (i : ℕ) < k → (star Q * A * Q) i.succ i.castSucc ≠ 0) :
    (∀ i : Fin (N + 1), (i : ℕ) ≤ k → ∃ c : 𝕜, ‖c‖ = 1 ∧ V.col i = c • Q.col i) ∧
      (∀ i : Fin N, (i : ℕ) < k →
        ‖(star V * A * V) i.succ i.castSucc‖ = ‖(star Q * A * Q) i.succ i.castSucc‖) ∧
      (∀ i : Fin N, (i : ℕ) = k → (star Q * A * Q) i.succ i.castSucc = 0 →
        (star V * A * V) i.succ i.castSucc = 0) := by
  set j : Fin (N + 1) := ⟨k, by omega⟩ with hj
  have hKQ := isKrylovDecomposition_of_mem_unitaryGroup hQ A 0
  have hKV := isKrylovDecomposition_of_mem_unitaryGroup hV A 0
  have hAQ := hKQ.isArnoldiDecomposition_leading hH j fun _ _ => rfl
  have hAV := hKV.isArnoldiDecomposition_leading hG j fun _ _ => rfl
  have hunred : ((star Q * A * Q).submatrix (Fin.castLE j.isLt)
      (Fin.castLE j.isLt)).IsUnreducedUpperHessenberg := by
    refine isUnreducedUpperHessenberg_iff_succ.2 ⟨hAQ.isUpperHessenberg, fun i => ?_⟩
    have hik : (i : ℕ) < k := i.isLt
    have h1 : Fin.castLE j.isLt i.succ = (⟨i, by omega⟩ : Fin N).succ := Fin.ext (by simp)
    have h2 : Fin.castLE j.isLt i.castSucc = (⟨i, by omega⟩ : Fin N).castSucc :=
      Fin.ext (by simp)
    rw [submatrix_apply, h1, h2]
    exact hsub _ hik
  have hfirst : V.submatrix id (Fin.castLE j.isLt) *ᵥ Pi.single 0 1 =
      Q.submatrix id (Fin.castLE j.isLt) *ᵥ Pi.single 0 1 := by
    rw [mulVec_single_one, mulVec_single_one]
    ext x
    have := congrFun h0 x
    simpa using this
  obtain ⟨d, hd1, -, hVQ, hGH, hr⟩ := hAQ.implicitQ hAV hunred hfirst
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi hz => ?_⟩
  · -- (a)
    refine ⟨d ⟨i, by simp [hj]; omega⟩, hd1 _, ?_⟩
    ext x
    have := congrFun (congrFun hVQ x) ⟨i, by simp [hj]; omega⟩
    rw [mul_diagonal] at this
    simpa [mul_comm] using this
  · -- (b)
    set a : Fin j := ⟨i, by simpa [hj] using hi⟩
    have := congrFun (congrFun hGH a.succ) a.castSucc
    rw [star_diagonal_mul_mul_diagonal_apply] at this
    have h1 : Fin.castLE j.isLt a.succ = i.succ := Fin.ext (by simp [a])
    have h2 : Fin.castLE j.isLt a.castSucc = i.castSucc := Fin.ext (by simp [a])
    simp only [submatrix_apply, h1, h2] at this
    rw [this, norm_mul, norm_mul, norm_star, hd1, hd1, one_mul, mul_one]
  · -- (c)
    have hjc : j = i.castSucc := Fin.ext (by simp [hj, hi])
    have hrQ : ∑ l ∈ Ioi j, (star Q * A * Q) l j • Q.col l +
        (0 : Fin (N + 1) → 𝕜) j • (0 : Fin (N + 1) → 𝕜) = 0 := by
      rw [smul_zero, add_zero]
      refine sum_eq_zero fun l hl => ?_
      rcases eq_or_ne l i.succ with rfl | hne
      · rw [hjc, hz, zero_smul]
      · have hl' := mem_Ioi.1 hl
        have hsl : i.succ < l := by
          rw [Fin.lt_def] at hl' ⊢
          have : (l : ℕ) ≠ i + 1 := fun h' => hne (Fin.ext (by simpa using h'))
          simp only [hj] at hl'
          simp only [Fin.val_succ]
          omega
        rw [hH l j ⟨i.succ, by rw [hjc]; exact Fin.castSucc_lt_succ, hsl⟩, zero_smul]
    rw [hrQ, smul_zero] at hr
    have hdot := congrArg (star (V.col i.succ) ⬝ᵥ ·) hr
    simp only [dotProduct_sum, dotProduct_smul, smul_eq_mul, hKV.star_col_dotProduct_col,
      hKV.star_col_dotProduct_residual, mul_zero, add_zero, one_apply] at hdot
    rw [sum_eq_single_of_mem i.succ (mem_Ioi.2 (by rw [hjc]; exact Fin.castSucc_lt_succ))
      (fun l _ hne => by rw [ite_eq_right_iff.2 fun h' => absurd h'.symm hne, mul_zero]),
      hjc] at hdot
    simpa using hdot

variable {A Q V : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}

/-- For real matrices `star` is the transpose. -/
private theorem star_eq_transpose_real (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    star M = Mᵀ :=
  conjTranspose_eq_transpose_of_trivial M

/-- The implicit Q theorem for real orthogonal matrices, unreduced case: `V = Q D` and
`Vᵀ A V = D (Qᵀ A Q) D` with `D = diag(±1)`, `d 0 = 1`. -/
theorem implicitQ_real (hQ : Q ∈ orthogonalGroup (Fin (N + 1)) ℝ)
    (hV : V ∈ orthogonalGroup (Fin (N + 1)) ℝ) (hH : (Qᵀ * A * Q).IsUnreducedUpperHessenberg)
    (hG : (Vᵀ * A * V).IsUpperHessenberg) (h0 : V.col 0 = Q.col 0) :
    ∃ d : Fin (N + 1) → ℝ, (∀ i, d i = 1 ∨ d i = -1) ∧ d 0 = 1 ∧ V = Q * diagonal d ∧
      Vᵀ * A * V = diagonal d * (Qᵀ * A * Q) * diagonal d := by
  rw [← star_eq_transpose_real] at hH hG
  obtain ⟨d, hd1, hd0, hVQ, hGH⟩ := implicitQ hQ hV hH hG h0
  refine ⟨d, fun i => ?_, hd0, hVQ, ?_⟩
  · have := hd1 i
    rwa [Real.norm_eq_abs, abs_eq zero_le_one] at this
  · rw [← star_eq_transpose_real, ← star_eq_transpose_real, hGH, star_eq_transpose_real,
      diagonal_transpose]

/-- [golub2013matrix] **Theorem 7.4.2**, as the book states it, for real orthogonal `Q`, `V`: the
columns `i ≤ k` of `V` are `± ` those of `Q`, `|g_{i+1,i}| = |h_{i+1,i}|` for `i < k`, and
`h_{k+1,k} = 0` forces `g_{k+1,k} = 0`. Chapter 8's Theorem 8.3.2 is its symmetric-tridiagonal
instance. -/
theorem implicitQ_of_apply_eq_zero_real (hQ : Q ∈ orthogonalGroup (Fin (N + 1)) ℝ)
    (hV : V ∈ orthogonalGroup (Fin (N + 1)) ℝ) (hH : (Qᵀ * A * Q).IsUpperHessenberg)
    (hG : (Vᵀ * A * V).IsUpperHessenberg) (h0 : V.col 0 = Q.col 0) {k : ℕ} (hk : k ≤ N)
    (hsub : ∀ i : Fin N, (i : ℕ) < k → (Qᵀ * A * Q) i.succ i.castSucc ≠ 0) :
    (∀ i : Fin (N + 1), (i : ℕ) ≤ k → V.col i = Q.col i ∨ V.col i = -Q.col i) ∧
      (∀ i : Fin N, (i : ℕ) < k →
        |(Vᵀ * A * V) i.succ i.castSucc| = |(Qᵀ * A * Q) i.succ i.castSucc|) ∧
      (∀ i : Fin N, (i : ℕ) = k → (Qᵀ * A * Q) i.succ i.castSucc = 0 →
        (Vᵀ * A * V) i.succ i.castSucc = 0) := by
  rw [← star_eq_transpose_real] at hH hG hsub ⊢
  rw [← star_eq_transpose_real]
  obtain ⟨ha, hb, hc⟩ := implicitQ_of_apply_eq_zero hQ hV hH hG h0 hk hsub
  refine ⟨fun i hi => ?_, fun i hi => ?_, hc⟩
  · obtain ⟨c, hc1, hVc⟩ := ha i hi
    rw [Real.norm_eq_abs, abs_eq zero_le_one] at hc1
    rcases hc1 with rfl | rfl
    · exact Or.inl (by rw [hVc, one_smul])
    · exact Or.inr (by rw [hVc, neg_one_smul])
  · have := hb i hi
    rwa [Real.norm_eq_abs, Real.norm_eq_abs] at this

end Square

end Matrix

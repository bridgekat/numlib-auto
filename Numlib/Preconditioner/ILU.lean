/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.LU.Elimination
import Numlib.LinearAlgebra.Matrix.SchurComplement
import Numlib.Stationary.RegularSplitting

/-!
# Incomplete LU factorizations

Let $A$ be a square matrix and let $P$ be a set of positions, the *zero pattern*. An *incomplete LU
factorization* of $A$ for $P$ is a pair of matrices $L$ and $U$, with $L$ unit lower triangular and
$U$ upper triangular, such that both vanish on $P$ and $(LU)_{ij} = a_{ij}$ for every position
$(i, j) \notin P$ ([saad2003iterative], §10.3). With the residual $R = LU - A$, the factorization
gives the splitting $A = LU - R$, whose first part is cheap to invert, and $R$ is supported in $P$.
The level-zero factorization $\mathrm{ILU}(0)$ takes for $P$ the off-diagonal zero pattern of $A$.
The modified factorization $\mathrm{MILU}$ replaces the condition on the diagonal by the condition
that $LU$ and $A$ have the same row sums. The incomplete Cholesky factorization of a symmetric
matrix $B$ is one lower triangular factor $L$ that vanishes on $P$, with $(L L^T)_{ij} = b_{ij}$ for
$(i, j) \notin P$.

The main theorem is due to [meijerink1977iterative]. An M-matrix $A$ has an incomplete LU
factorization for every zero pattern that avoids the diagonal, no pivot vanishes, and $A = LU - R$
is a regular splitting, so the iteration that it defines converges (Theorem 10.2 of
[saad2003iterative]). In the symmetric case, a Stieltjes matrix has an incomplete Cholesky factor
with a positive diagonal for every symmetric zero pattern that avoids the diagonal
([meijerink1977iterative]; [golub2013matrix], §11.5.8). For the threshold factorization
$\mathrm{ILUT}$, a row recurrence for matrices of the class $\hat{M}$ of [saad2003iterative] keeps a
positive pivot (Theorem 10.8 of [saad2003iterative]).

## Main definitions

* `Matrix.zeroPattern`: the off-diagonal positions at which a matrix vanishes.
* `Matrix.IsILU`: $L$ and $U$ form an incomplete LU factorization of $A$ for the zero pattern $P$.
* `Matrix.IsMILU`: the modified incomplete LU factorization.
* `Matrix.IsILU0`: the factorization $\mathrm{ILU}(0)$.
* `Matrix.IsIC`: $L$ is an incomplete Cholesky factor of $B$ for the zero pattern $P$.
* `Matrix.IsIC0`: the factorization $\mathrm{IC}(0)$.
* `Matrix.IsMHat`: the class of $\hat{M}$ matrices of [saad2003iterative].

## Main results

* `Matrix.IsILU.sub_eq_zero_of_notMem`: the residual $LU - A$ vanishes off the zero pattern.
* `Matrix.IsILU.dropStrategy_rowSum`: the residual has zero row sums if and only if $LU$ and $A$
  have the same row sums.
* `Matrix.IsIC.sub_eq_zero_of_notMem`: the residual $L L^T - B$ vanishes off the zero pattern.
* `Matrix.IsIC.isILU`: an incomplete Cholesky factorization, rescaled by its diagonal, is an
  incomplete LU factorization.
* `Matrix.IsIC.eq_of_diag_pos`: an incomplete Cholesky factor with a positive diagonal is unique.
* `Matrix.IsMHat.ilut_rows_nonpos`, `Matrix.IsMHat.ilut_rows_diag_nonneg`,
  `Matrix.IsMHat.ilut_rows`: the sign pattern, the row sums and the pivot of the working row in the
  threshold elimination of an $\hat{M}$ matrix.
* `Matrix.IsMMatrix.isMMatrix_elimStep`: one step of Gaussian elimination maps an M-matrix to an
  M-matrix.
* `Matrix.IsMMatrix.exists_isILU_isMMatrix`, `Matrix.IsMMatrix.exists_isILU`: an M-matrix has an
  incomplete LU factorization for every zero pattern that avoids the diagonal, and the splitting is
  regular.
* `Matrix.IsILU.eq_of_diag_ne_zero`: incomplete LU factors with nonzero pivots are unique.
* `Matrix.IsILU.eq_diagonal_mul_transpose`: for a symmetric matrix and a symmetric pattern,
  $U = D L^T$ with $D$ the diagonal of $U$.
* `Matrix.IsStieltjes.exists_isIC`: a Stieltjes matrix has an incomplete Cholesky factor with a
  positive diagonal.
* `Matrix.IsILU.isRegular`, `Matrix.IsILU.complexSpectralRadius_lt_one`: the splitting $A = LU - R$
  is regular, and for an M-matrix the iteration converges.

## Proof outline

The existence theorem for M-matrices is an induction over the pivots in increasing order. At each
step, Gaussian elimination below the pivot keeps the working matrix an M-matrix, by the theorem of
[fan1960note] (`Matrix.IsMMatrix.schurComplementSingle`). Then the entries in the zero pattern are
dropped. A dropped off-diagonal entry is nonpositive, so dropping moves the matrix up in the
entrywise order, and the comparison theorem `Matrix.IsMMatrix.of_entrywiseLE` keeps it an M-matrix.
For a Stieltjes matrix, the incomplete LU factorization is symmetric, $U = D L^T$
(`Matrix.IsILU.eq_diagonal_mul_transpose`), and the pivots are positive because the last working
matrix is an M-matrix (`Matrix.IsMMatrix.exists_isILU_isMMatrix`). So $L D^{1/2}$ is the incomplete
Cholesky factor.

## Implementation notes

* `Matrix.IsILU` states the constraints on the factors and not an algorithm. [saad2003iterative],
  §10.3.1, gives several loop orders (KIJ, IKJ) that compute such factors, proves that two of them
  agree, and observes before Algorithm 10.4 that the factors are in general not unique. Each loop
  order gives factors that satisfy `Matrix.IsILU`, and all later statements of §10.3–10.5 use only
  these constraints. When the pivots are nonzero the factors are unique
  (`Matrix.IsILU.eq_of_diag_ne_zero`), so the non-uniqueness comes only from a zero pivot.
* `Matrix.IsIC` is normalized by a positive diagonal and not by a unit diagonal, so it is not
  literally an incomplete LU factorization. `Matrix.IsIC.isILU` rescales it into one,
  $B = (L D^{-1})(D L^T)$. The uniqueness `Matrix.IsIC.eq_of_diag_pos` lets a theorem speak of the
  incomplete Cholesky factor of $B$.
* The elimination step is `Matrix.elimStep` of `Numlib.LinearAlgebra.Matrix.LU.Elimination`, which
  keeps the index type fixed. It is $G^{-1} A$ for the unipotent matrix $G$ = `Matrix.elimMul A p`
  that carries the multipliers of column $p$. So the accumulated factor $L$ is a product of such
  matrices, without reindexing. The Schur complement `Matrix.schurComplementSingle` of
  `Numlib.LinearAlgebra.Matrix.SchurComplement` is the same step on the smaller index type, and the
  theorem of [fan1960note] is stated for it in `Numlib.LinearAlgebra.Matrix.MMatrix`.
* The class `Matrix.IsMHat` assumes neither nonsingularity nor a nonnegative inverse. The theorem
  `Matrix.IsMHat.ilut_rows` is stated for an abstract row recurrence and not for an algorithm.
-/

open Finset
open scoped Matrix

namespace Matrix

variable {n α : Type*}

/-! ### The declarative definition -/

section ZeroPattern

variable [Zero α]

/-- The **off-diagonal zero pattern** of a square matrix $A$ (§10.3.2 of [saad2003iterative]): the
set of positions $(i, j)$ with $i \neq j$ and $a_{ij} = 0$.

The incomplete factorization with this zero pattern is $\mathrm{ILU}(0)$, whose factors have the
sparsity of the lower and the upper part of $A$. -/
def zeroPattern (A : Matrix n n α) : Set (n × n) := {p | A p.1 p.2 = 0 ∧ p.1 ≠ p.2}

/-- A position $(i, j)$ is in the off-diagonal zero pattern of $A$ if and only if $a_{ij} = 0$ and
$i \neq j$. -/
@[simp]
theorem mem_zeroPattern {A : Matrix n n α} {p : n × n} :
    p ∈ A.zeroPattern ↔ A p.1 p.2 = 0 ∧ p.1 ≠ p.2 := Iff.rfl

/-- The off-diagonal zero pattern contains no diagonal position. This is the hypothesis of the
existence theorem `Matrix.IsMMatrix.exists_isILU`. -/
theorem diag_notMem_zeroPattern (A : Matrix n n α) (i : n) : (i, i) ∉ A.zeroPattern :=
  fun h => h.2 rfl

end ZeroPattern

section Defs

variable [Fintype n] [Preorder n] [Semiring α]

/-- The **shape constraints** on a pair of incomplete factors for the zero pattern $P$: $L$ is unit
lower triangular, $U$ is upper triangular, and both vanish on $P$.

This is the part of `Matrix.IsILU` that does not mention the factored matrix. The modified
factorization `Matrix.IsMILU` uses it too. -/
structure IsILUFactors (P : Set (n × n)) (L U : Matrix n n α) : Prop where
  /-- The diagonal entries of $L$ are $1$. -/
  l_diag : ∀ i, L i i = 1
  /-- $L$ is lower triangular: $L_{ij} = 0$ for $i < j$. -/
  l_eq_zero_of_lt : ∀ i j, i < j → L i j = 0
  /-- $U$ is upper triangular: $U_{ij} = 0$ for $j < i$. -/
  u_eq_zero_of_gt : ∀ i j, j < i → U i j = 0
  /-- $L$ vanishes on the zero pattern. -/
  l_eq_zero_of_mem : ∀ i j, (i, j) ∈ P → L i j = 0
  /-- $U$ vanishes on the zero pattern. -/
  u_eq_zero_of_mem : ∀ i j, (i, j) ∈ P → U i j = 0

/-- An **incomplete LU factorization** of $A$ for the zero pattern $P$ (§10.3.2 of
[saad2003iterative]). Let $A$, $L$ and $U$ be square matrices over a semiring, indexed by a
preordered finite type, and let $P$ be a set of positions. Then $(L, U)$ is an incomplete LU
factorization of $A$ for $P$ if $L$ is unit lower triangular, $U$ is upper triangular,
$L_{ij} = U_{ij} = 0$ for $(i, j) \in P$, and
$$(LU)_{ij} = a_{ij} \quad \text{for } (i, j) \notin P.$$

The definition states constraints and not an algorithm. Every loop order of §10.3.1 of
[saad2003iterative] gives factors that satisfy it, and the factors that it describes are in
general not unique. -/
structure IsILU (P : Set (n × n)) (A L U : Matrix n n α) : Prop extends IsILUFactors P L U where
  /-- Off the zero pattern, the product $LU$ agrees with $A$. -/
  agree : ∀ i j, (i, j) ∉ P → (L * U) i j = A i j

/-- The **modified incomplete LU factorization** $\mathrm{MILU}$ (§10.3.5 of [saad2003iterative]).
The pair $(L, U)$ satisfies the shape constraints of `Matrix.IsILU` for the zero pattern $P$,
$(LU)_{ij} = a_{ij}$ for $i \neq j$ and $(i, j) \notin P$, and the row sums agree:
$$(LU) e = A e,$$
where $e$ is the vector of ones.

The entries that an ordinary incomplete factorization drops are added to the diagonal instead.
So the preconditioner is exact on constant vectors, and this is its justification. -/
structure IsMILU (P : Set (n × n)) (A L U : Matrix n n α) : Prop extends IsILUFactors P L U where
  /-- Off the diagonal and off the zero pattern, the product $LU$ agrees with $A$. -/
  agree_of_ne : ∀ i j, i ≠ j → (i, j) ∉ P → (L * U) i j = A i j
  /-- The row sums of $LU$ and of $A$ agree. -/
  mulVec_one : (L * U) *ᵥ 1 = A *ᵥ 1

/-- The factorization $\mathrm{ILU}(0)$ (§10.3.2 and Algorithm 10.4 of [saad2003iterative]): an
incomplete LU factorization of $A$ whose zero pattern is the off-diagonal zero pattern of $A$.

Then $L$ and $U$ have the sparsity of the lower and the upper part of $A$, and $LU$ agrees with
$A$ at every position where $A$ is nonzero. -/
abbrev IsILU0 (A L U : Matrix n n α) : Prop := IsILU A.zeroPattern A L U

/-- An **incomplete Cholesky factorization** of a symmetric matrix $B$ for the zero pattern $P$
(§10.8.2 and §10.4.5 of [saad2003iterative]). The matrix $L$ is an incomplete Cholesky factor of
$B$ if $L$ is lower triangular, $L_{ij} = 0$ for $(i, j) \in P$, and
$$(L L^T)_{ij} = b_{ij} \quad \text{for } (i, j) \notin P.$$
It is the symmetric case of `Matrix.IsILU`, which the book does not treat in a section of its
own. Section 10.8.2 of [saad2003iterative] uses it to precondition the normal equations.

Like `Matrix.IsILU`, the definition states constraints and not an algorithm. The difference in
shape is the normalization. `Matrix.IsILU` requires a unit diagonal of the lower factor, but a
Cholesky factor carries the scaling itself and is normalized by a positive diagonal. Positivity
cannot be expressed over a semiring, so it is a hypothesis of the results that need it
(`Matrix.IsIC.eq_of_diag_pos`) and not a field of the structure. `Matrix.IsIC.isILU` rescales an
incomplete Cholesky factorization with an invertible diagonal into an incomplete LU
factorization.

The factorization uses the transpose, $B = L L^T$, which is the real symmetric case. A Hermitian
variant with $L^H$ is not defined here. -/
structure IsIC (P : Set (n × n)) (B L : Matrix n n α) : Prop where
  /-- $L$ is lower triangular: $L_{ij} = 0$ for $i < j$. -/
  l_eq_zero_of_lt : ∀ i j, i < j → L i j = 0
  /-- $L$ vanishes on the zero pattern. -/
  l_eq_zero_of_mem : ∀ i j, (i, j) ∈ P → L i j = 0
  /-- Off the zero pattern, $L L^T$ agrees with $B$. -/
  agree : ∀ i j, (i, j) ∉ P → (L * Lᵀ) i j = B i j

/-- The factorization $\mathrm{IC}(0)$ (§10.8.2 of [saad2003iterative]): an incomplete Cholesky
factorization of $B$ whose zero pattern is the off-diagonal zero pattern of $B$. Then $L$ has
the sparsity of the lower part of $B$. -/
abbrev IsIC0 (B L : Matrix n n α) : Prop := IsIC B.zeroPattern B L

end Defs

section Residual

variable [Fintype n] [Preorder n] [Ring α] {P : Set (n × n)} {A L U : Matrix n n α}

/-- **Proposition 10.4** of [saad2003iterative]. Let $(L, U)$ be an incomplete LU factorization of
$A$ for the zero pattern $P$, over a ring. Then the residual $R = LU - A$ satisfies
$$R_{ij} = 0 \quad \text{for } (i, j) \notin P,$$
so $A = LU - R$ with $R$ supported in $P$.

In this form $R$ enters the regular splitting `Matrix.IsILU.isRegular` and the error analysis of
§10.5. -/
theorem IsILU.sub_eq_zero_of_notMem (h : IsILU P A L U) {i j : n} (hij : (i, j) ∉ P) :
    (L * U - A) i j = 0 := by
  rw [Matrix.sub_apply, h.agree i j hij, sub_self]

omit [Preorder n] in
/-- The row-sum identity behind $\mathrm{MILU}$ ((10.21) of [saad2003iterative]). For square
matrices $A$, $L$ and $U$ over a ring, the residual $R = LU - A$ has zero row sums if and only
if $LU$ and $A$ have the same row sums:
$$R e = 0 \iff (LU) e = A e,$$
where $e$ is the vector of ones.

The correction of each diagonal entry of $U$ by the sum of the entries dropped in its row makes
the left side hold. The right side is the defining property `Matrix.IsMILU.mulVec_one` of the
modified factorization. -/
theorem IsILU.dropStrategy_rowSum (A L U : Matrix n n α) :
    (L * U - A) *ᵥ (1 : n → α) = 0 ↔ (L * U) *ᵥ (1 : n → α) = A *ᵥ 1 := by
  rw [sub_mulVec, sub_eq_zero]

/-- The residual $LU - A$ of a modified incomplete LU factorization has zero row sums. In this sense
$\mathrm{MILU}$ is exact on constant vectors. -/
theorem IsMILU.residual_mulVec_one (h : IsMILU P A L U) : (L * U - A) *ᵥ (1 : n → α) = 0 :=
  (IsILU.dropStrategy_rowSum A L U).2 h.mulVec_one

/-- Let $L$ be an incomplete Cholesky factor of $B$ for the zero pattern $P$, over a ring. Then the
residual $R = L L^T - B$ satisfies $R_{ij} = 0$ for $(i, j) \notin P$, so $B = L L^T - R$ with
$R$ supported in $P$. This is the analogue of `Matrix.IsILU.sub_eq_zero_of_notMem` for
incomplete Cholesky factorizations. -/
theorem IsIC.sub_eq_zero_of_notMem {B : Matrix n n α} (h : IsIC P B L) {i j : n}
    (hij : (i, j) ∉ P) : (L * Lᵀ - B) i j = 0 := by
  rw [Matrix.sub_apply, h.agree i j hij, sub_self]

end Residual

/-! ### Rescaling and uniqueness of incomplete Cholesky factors -/

section ICRescale

variable [Fintype n] [Preorder n] [DecidableEq n] [Field α] {P : Set (n × n)}
variable {B L : Matrix n n α}

omit [Preorder n] in
/-- If the diagonal entries of $L$ are nonzero, then $(L D^{-1})(D L^T) = L L^T$, where $D$ is the
diagonal of $L$. -/
private theorem mul_diagInv_mul_diag_mul_transpose (hd : ∀ i, L i i ≠ 0) :
    (L * diagonal fun i => (L i i)⁻¹) * (diagonal (fun i => L i i) * Lᵀ) = L * Lᵀ := by
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_diagonal, diagonal_mul, transpose_apply, mul_assoc, ← mul_assoc ((L k k)⁻¹),
    inv_mul_cancel₀ (hd k), one_mul]

/-- An incomplete Cholesky factorization is an incomplete LU factorization after rescaling. Let $L$
be an incomplete Cholesky factor of $B$ over a field for a zero pattern $P$ that is symmetric,
that is, $(i, j) \in P$ implies $(j, i) \in P$. If the diagonal $D$ of $L$ has nonzero entries,
then $(L D^{-1}, D L^T)$ is an incomplete LU factorization of $B$ for $P$.

The pattern must be symmetric because `Matrix.IsILU` imposes one pattern on both factors, and
the upper factor of a Cholesky factorization is the transpose of the lower factor. -/
theorem IsIC.isILU (h : IsIC P B L) (hP : ∀ i j, (i, j) ∈ P → (j, i) ∈ P) (hd : ∀ i, L i i ≠ 0) :
    IsILU P B (L * diagonal fun i => (L i i)⁻¹) (diagonal (fun i => L i i) * Lᵀ) where
  l_diag i := by rw [mul_diagonal, mul_inv_cancel₀ (hd i)]
  l_eq_zero_of_lt i j hij := by rw [mul_diagonal, h.l_eq_zero_of_lt i j hij, zero_mul]
  u_eq_zero_of_gt i j hij := by
    rw [diagonal_mul, transpose_apply, h.l_eq_zero_of_lt j i hij, mul_zero]
  l_eq_zero_of_mem i j hij := by rw [mul_diagonal, h.l_eq_zero_of_mem i j hij, zero_mul]
  u_eq_zero_of_mem i j hij := by
    rw [diagonal_mul, transpose_apply, h.l_eq_zero_of_mem j i (hP i j hij), mul_zero]
  agree i j hij := by
    rw [mul_diagInv_mul_diag_mul_transpose hd]
    exact h.agree i j hij

end ICRescale

section ICUnique

variable [Fintype n] [LinearOrder n] {P : Set (n × n)} {B L₁ L₂ : Matrix n n ℝ}

/-- An incomplete Cholesky factor with a positive diagonal is unique. Let $B$ be a real square
matrix, indexed by a linearly ordered finite type, and let $P$ be a zero pattern that contains
no diagonal position. If $L_1$ and $L_2$ are incomplete Cholesky factors of $B$ for $P$ with
positive diagonal entries, then $L_1 = L_2$.

In this respect incomplete Cholesky differs from incomplete LU, whose factors are in general not
unique. The uniqueness lets a statement speak of the incomplete Cholesky factor. The proof goes
row by row. When the earlier rows and the entries of row $i$ before column $j$ agree, the
constraint at $(i, j)$ gives $(L_1 - L_2)_{ij} (L_1)_{jj} = 0$ off the diagonal and
$(L_1)_{ii}^2 = (L_2)_{ii}^2$ on the diagonal. -/
theorem IsIC.eq_of_diag_pos (h₁ : IsIC P B L₁) (h₂ : IsIC P B L₂) (hP : ∀ i, (i, i) ∉ P)
    (hp₁ : ∀ i, 0 < L₁ i i) (hp₂ : ∀ i, 0 < L₂ i i) : L₁ = L₂ := by
  classical
  have key : ∀ i j, L₁ i j = L₂ i j := by
    intro i
    induction i using WellFoundedLT.induction with
    | ind i ihrow =>
      intro j
      induction j using WellFoundedLT.induction with
      | ind j ihcol =>
        by_cases hmem : (i, j) ∈ P
        · rw [h₁.l_eq_zero_of_mem i j hmem, h₂.l_eq_zero_of_mem i j hmem]
        rcases lt_trichotomy i j with hij | hij | hij
        · rw [h₁.l_eq_zero_of_lt i j hij, h₂.l_eq_zero_of_lt i j hij]
        · -- the diagonal entry: `L i i ^ 2` is determined, and positivity fixes the sign
          subst hij
          have e₁ := h₁.agree i i (hP i)
          have e₂ := h₂.agree i i (hP i)
          rw [Matrix.mul_apply] at e₁ e₂
          simp only [transpose_apply] at e₁ e₂
          have hsum : ∑ k, L₁ i k * L₁ i k = ∑ k, L₂ i k * L₂ i k := by rw [e₁, e₂]
          rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
            ← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hsum
          have hcongr : ∑ k ∈ Finset.univ.erase i, L₁ i k * L₁ i k
              = ∑ k ∈ Finset.univ.erase i, L₂ i k * L₂ i k :=
            Finset.sum_congr rfl fun k hk => by
              rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hk) with hk' | hk'
              · rw [ihcol k hk']
              · rw [h₁.l_eq_zero_of_lt i k hk', h₂.l_eq_zero_of_lt i k hk']
          rw [hcongr] at hsum
          exact (mul_self_inj (hp₁ i).le (hp₂ i).le).1 (add_left_cancel hsum)
        · -- below the diagonal: row `j` is already known, so the entry is forced
          have e₁ := h₁.agree i j hmem
          have e₂ := h₂.agree i j hmem
          rw [Matrix.mul_apply] at e₁ e₂
          simp only [transpose_apply] at e₁ e₂
          have e₂' : ∑ k, L₂ i k * L₁ j k = B i j := by
            rw [← e₂]
            exact Finset.sum_congr rfl fun k _ => by rw [ihrow j hij k]
          have hzero : ∑ k, (L₁ i k - L₂ i k) * L₁ j k = 0 := by
            simp only [sub_mul, Finset.sum_sub_distrib]
            rw [e₁, e₂', sub_self]
          rw [Finset.sum_eq_single j (fun k _ hk => ?_) fun hk => absurd (Finset.mem_univ j) hk]
            at hzero
          · rcases mul_eq_zero.1 hzero with h | h
            · exact sub_eq_zero.1 h
            · exact absurd h (hp₁ j).ne'
          · rcases lt_or_gt_of_ne hk with hk' | hk'
            · rw [ihcol k hk', sub_self, zero_mul]
            · rw [h₁.l_eq_zero_of_lt j k hk', mul_zero]
  exact Matrix.ext fun i j => key i j

end ICUnique

/-! ### Threshold factorizations and the matrices of class $\hat{M}$ -/

section MHat

variable [Fintype n] [LinearOrder n]

/-- An **$\hat{M}$ matrix** ((10.25)–(10.27) of [saad2003iterative]). A real square matrix $H$,
indexed by a linearly ordered finite type, is an $\hat{M}$ matrix if:
* $h_{ii} > 0$ for every row $i$ other than the last row, and $h_{ii} \ge 0$ in the last row;
* $h_{ij} \le 0$ for $i \neq j$;
* $\sum_{j > i} h_{ij} < 0$ for every row $i$ other than the last row.

Unlike the definition of an M-matrix (`Matrix.IsMMatrix`), it requires neither nonsingularity
nor a nonnegative inverse. It is the class for which [saad2003iterative], §10.4, shows that the
threshold factorization $\mathrm{ILUT}$ does not break down. The last row is the row indexed by
the greatest element, `IsMax i`. -/
structure IsMHat (H : Matrix n n ℝ) : Prop where
  /-- The diagonal entries are positive in every row other than the last row. -/
  diag_pos : ∀ i, ¬ IsMax i → 0 < H i i
  /-- The diagonal entry of the last row is nonnegative. -/
  diag_nonneg_of_isMax : ∀ i, IsMax i → 0 ≤ H i i
  /-- The off-diagonal entries are nonpositive. -/
  offDiag_nonpos : ∀ i j, i ≠ j → H i j ≤ 0
  /-- In every row other than the last row, the entries to the right of the diagonal have a negative
  sum. In particular, each such row has a nonzero entry to the right of the diagonal. -/
  sum_gt_neg : ∀ i, ¬ IsMax i → ∑ j ∈ Finset.univ.filter (fun j => i < j), H i j < 0

/-- Every diagonal entry of an $\hat{M}$ matrix is nonnegative. -/
theorem IsMHat.diag_nonneg {H : Matrix n n ℝ} (hH : H.IsMHat) (i : n) : 0 ≤ H i i := by
  by_cases hi : IsMax i
  · exact hH.diag_nonneg_of_isMax i hi
  · exact (hH.diag_pos i hi).le

/-- A **diagonally dominant $\hat{M}$ matrix** (§10.4.1 of [saad2003iterative]): an $\hat{M}$ matrix
whose row sums are all nonnegative. This is the hypothesis of the $\mathrm{ILUT}$ existence
theorem `Matrix.IsMHat.ilut_rows`. -/
structure IsMHat.IsDiagDominant (H : Matrix n n ℝ) : Prop extends IsMHat H where
  /-- Every row sum is nonnegative. -/
  rowSum_nonneg : ∀ i, 0 ≤ ∑ j, H i j

/-- If $x_j \le 0$ for $j \neq d$, then $\sum_{j \neq d} x_j \le \sum_{j > d} x_j$. -/
private theorem sum_erase_le_sum_gt (x : n → ℝ) (d : n) (hoff : ∀ j, j ≠ d → x j ≤ 0) :
    ∑ j ∈ Finset.univ.erase d, x j ≤ ∑ j ∈ Finset.univ.filter (fun j => d < j), x j := by
  have hsub : Finset.univ.filter (fun j => d < j) ⊆ Finset.univ.erase d := fun j hj =>
    Finset.mem_erase.2 ⟨(Finset.mem_filter.1 hj).2.ne', Finset.mem_univ j⟩
  have hsd := Finset.sum_sdiff (f := x) hsub
  have hnp : ∑ j ∈ Finset.univ.erase d \ Finset.univ.filter (fun j => d < j), x j ≤ 0 :=
    Finset.sum_nonpos fun j hj => hoff j (Finset.mem_erase.1 (Finset.mem_sdiff.1 hj).1).1
  linarith

omit [Fintype n] in
/-- If $a \in s$ and $x_j \le 0$ for $j \in s$ with $j \neq a$, then $\sum_{j \in s} x_j \le x_a$.
-/
private theorem sum_le_of_mem (x : n → ℝ) (s : Finset n) {a : n} (ha : a ∈ s)
    (hnp : ∀ j ∈ s, j ≠ a → x j ≤ 0) : ∑ j ∈ s, x j ≤ x a := by
  have hsplit := Finset.add_sum_erase s x ha
  have hrest : ∑ j ∈ s.erase a, x j ≤ 0 :=
    Finset.sum_nonpos fun j hj => hnp j (Finset.mem_of_mem_erase hj) (Finset.mem_erase.1 hj).1
  linarith

/-- If $x_j \le 0$ for $j \neq d$, $\sum_j x_j \ge 0$ and $\sum_{j > d} x_j < 0$, then $x_d > 0$. -/
private theorem pos_of_sum_nonneg_of_sum_gt_neg (x : n → ℝ) (d : n) (hoff : ∀ j, j ≠ d → x j ≤ 0)
    (hsum : 0 ≤ ∑ j, x j) (hgt : ∑ j ∈ Finset.univ.filter (fun j => d < j), x j < 0) : 0 < x d := by
  have h1 := Finset.add_sum_erase Finset.univ x (Finset.mem_univ d)
  have h2 := sum_erase_le_sum_gt x d hoff
  linarith

/-- The sign pattern and the row sums in a threshold elimination ((10.28) and (10.29) of
[saad2003iterative]). Let $H$ be a real square matrix, indexed by a linearly ordered finite
type, that is a diagonally dominant $\hat{M}$ matrix, and let $d$ be a row index. Let
$u_k, w_k, r_k \in \mathbb{R}^n$, $l_k \in \mathbb{R}$ and pivot indices $p_k$ for
$k \in \mathbb{N}$ satisfy, for all $k$ and $j$:
* $u_0$ is row $d$ of $H$, and $u_{k+1} = u_k - l_k w_k - r_k$;
* $(w_k)_j \le 0$ for $j \neq p_k$, $\sum_j (w_k)_j \ge 0$, and $l_k \le 0$;
* $l_k (w_k)_{p_k} = (u_k)_{p_k}$;
* $(r_k)_j = 0$ or $(r_k)_j = (u_k)_j - l_k (w_k)_j$, and $(r_k)_d = 0$.

Then for every $k$, $(u_k)_j \le 0$ for all $j \neq d$, and
$$0 \le \sum_j (u_k)_j \le \sum_j (u_{k+1})_j.$$

This is the half of Theorem 10.8 of [saad2003iterative] that needs neither the negative sum to
the right of the diagonal, (10.27), which does not constrain the last row, nor the protected
entry of the drop strategy. So it holds in every row. The meaning of the data is explained at
`Matrix.IsMHat.ilut_rows`, which states the full theorem with the positive pivot. In the last
row, `Matrix.IsMHat.ilut_rows_diag_nonneg` remains. -/
theorem IsMHat.ilut_rows_nonpos {H : Matrix n n ℝ} (hH : IsMHat.IsDiagDominant H) (d : n)
    (u w : ℕ → n → ℝ) (l : ℕ → ℝ) (r : ℕ → n → ℝ) (p : ℕ → n)
    (hu0 : u 0 = H d) (hrec : ∀ k, u (k + 1) = u k - l k • w k - r k)
    (hw : ∀ k j, j ≠ p k → w k j ≤ 0) (hwsum : ∀ k, 0 ≤ ∑ j, w k j) (hl : ∀ k, l k ≤ 0)
    (hpivot : ∀ k, l k * w k (p k) = u k (p k))
    (hdrop : ∀ k j, r k j = 0 ∨ r k j = u k j - l k * w k j) (hdropDiag : ∀ k, r k d = 0) (k : ℕ) :
    (∀ j, j ≠ d → u k j ≤ 0) ∧ 0 ≤ ∑ j, u k j ∧ ∑ j, u k j ≤ ∑ j, u (k + 1) j := by
  have step : ∀ k, (∀ j, j ≠ d → u k j ≤ 0) →
      (∀ j, j ≠ d → u (k + 1) j ≤ 0) ∧ ∑ j, u k j ≤ ∑ j, u (k + 1) j := by
    intro k hoff
    have hu : ∀ j, u (k + 1) j = u k j - l k * w k j - r k j := fun j => by
      rw [hrec k]; simp
    -- the value computed at step `k`, before dropping, is nonpositive off the diagonal
    have hv : ∀ j, j ≠ d → u k j - l k * w k j ≤ 0 := by
      intro j hj
      rcases eq_or_ne j (p k) with rfl | hjp
      · rw [hpivot k, sub_self]
      · have : 0 ≤ l k * w k j := mul_nonneg_of_nonpos_of_nonpos (hl k) (hw k j hjp)
        linarith [hoff j hj]
    have hnext : ∀ j, j ≠ d → u (k + 1) j ≤ 0 := by
      intro j hj
      rcases hdrop k j with h | h
      · rw [hu j, h, sub_zero]; exact hv j hj
      · rw [hu j, h, sub_self]
    have hrnp : ∀ j, r k j ≤ 0 := by
      intro j
      rcases eq_or_ne j d with rfl | hj
      · rw [hdropDiag k]
      · rcases hdrop k j with h | h
        · rw [h]
        · rw [h]; exact hv j hj
    have hsplit : ∑ j, u (k + 1) j = (∑ j, u k j) - l k * ∑ j, w k j - ∑ j, r k j := by
      simp only [hu]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    refine ⟨hnext, ?_⟩
    have h1 : l k * ∑ j, w k j ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (hl k) (hwsum k)
    have h2 : ∑ j, r k j ≤ 0 := Finset.sum_nonpos fun j _ => hrnp j
    rw [hsplit]; linarith
  induction k with
  | zero =>
    have hoff : ∀ j, j ≠ d → u 0 j ≤ 0 := fun j hj => by
      rw [hu0]; exact hH.toIsMHat.offDiag_nonpos d j (Ne.symm hj)
    have hsum : 0 ≤ ∑ j, u 0 j := by
      simp only [hu0]; exact hH.rowSum_nonneg d
    exact ⟨hoff, hsum, (step 0 hoff).2⟩
  | succ k ih =>
    obtain ⟨hoff, hsum, hmono⟩ := ih
    exact ⟨(step k hoff).1, hsum.trans hmono, (step (k + 1) (step k hoff).1).2⟩

/-- The last-row part of (10.30) of [saad2003iterative], $u^n_n \ge 0$. Under the hypotheses of
`Matrix.IsMHat.ilut_rows_nonpos`, the diagonal entry of the working row is nonnegative:
$(u_k)_d \ge 0$ for every $k$.

The proof uses only the sign pattern and the nonnegative row sum of
`Matrix.IsMHat.ilut_rows_nonpos`. So it needs neither (10.27) nor the modification of the drop
strategy, and it holds in every row. In the last row, where `Matrix.IsMHat.ilut_rows` does not
apply, it is the only available result. -/
theorem IsMHat.ilut_rows_diag_nonneg {H : Matrix n n ℝ} (hH : IsMHat.IsDiagDominant H) (d : n)
    (u w : ℕ → n → ℝ) (l : ℕ → ℝ) (r : ℕ → n → ℝ) (p : ℕ → n)
    (hu0 : u 0 = H d) (hrec : ∀ k, u (k + 1) = u k - l k • w k - r k)
    (hw : ∀ k j, j ≠ p k → w k j ≤ 0) (hwsum : ∀ k, 0 ≤ ∑ j, w k j) (hl : ∀ k, l k ≤ 0)
    (hpivot : ∀ k, l k * w k (p k) = u k (p k))
    (hdrop : ∀ k j, r k j = 0 ∨ r k j = u k j - l k * w k j) (hdropDiag : ∀ k, r k d = 0) (k : ℕ) :
    0 ≤ u k d := by
  obtain ⟨hoff, hsum, -⟩ :=
    IsMHat.ilut_rows_nonpos hH d u w l r p hu0 hrec hw hwsum hl hpivot hdrop hdropDiag k
  exact hsum.trans
    (sum_le_of_mem (u k) Finset.univ (Finset.mem_univ d) fun j _ hj => hoff j hj)

/-- **Theorem 10.8** of [saad2003iterative], the existence theorem for the threshold factorization
$\mathrm{ILUT}$. Let $H$ be a real square matrix, indexed by a linearly ordered finite type,
that is a diagonally dominant $\hat{M}$ matrix, and let $d$ be a row index other than the last.
Let $u_k, w_k, r_k \in \mathbb{R}^n$, $l_k \in \mathbb{R}$ and pivot indices $p_k$ for
$k \in \mathbb{N}$ satisfy, for all $k$ and $j$:
* $u_0$ is row $d$ of $H$, and $u_{k+1} = u_k - l_k w_k - r_k$;
* $(w_k)_j \le 0$ for $j \neq p_k$, $\sum_j (w_k)_j \ge 0$, and $l_k \le 0$;
* $p_k < d$ and $l_k (w_k)_{p_k} = (u_k)_{p_k}$;
* $(r_k)_j = 0$ or $(r_k)_j = (u_k)_j - l_k (w_k)_j$, and $(r_k)_d = 0$;
* there is $j_0 > d$ with $(r_k)_{j_0} = 0$ and $(u_k)_{j_0} - l_k (w_k)_{j_0} \le (u_k)_j - l_k
  (w_k)_j$ for all $j > d$.

Then for every $k$: $(u_k)_j \le 0$ for all $j \neq d$;
$0 \le \sum_j (u_k)_j \le \sum_j (u_{k+1})_j$; $\sum_{j > d} (u_k)_j < 0$; and $(u_k)_d > 0$. So
the factorization does not break down.

The data is the row recurrence (10.23) of §10.4.1 of [saad2003iterative] and not an algorithm.
The vector $u_k$ is the working copy of row $d$ after $k$ elimination steps. The vector $w_k$ is
the pivot row of step $k$, a row of the factor $U$ that is already computed, with the pivot
index $p_k$ to the left of $d$. The number $l_k$ is the multiplier, and $r_k$ is the part of the
row that the drop strategy drops. The hypotheses say that the pivot rows have the sign pattern
and the nonnegative row sums of an $\hat{M}$ matrix, that the multiplier eliminates the pivot
entry, that each entry is either kept or dropped completely, that the diagonal entry is never
dropped, and that the entry of largest modulus to the right of the diagonal is never dropped.
The last condition is the modification of §10.4.2 of [saad2003iterative]. Since the entries to
the right of the diagonal are nonpositive, the entry of largest modulus is the least entry.

In the last row, the hypothesis that $d$ is not the last index fails and (10.27) does not apply.
There, the first two conclusions alone give $(u_k)_d \ge 0$, which is $u^n_n \ge 0$ of
[saad2003iterative] (`Matrix.IsMHat.ilut_rows_diag_nonneg`). -/
theorem IsMHat.ilut_rows {H : Matrix n n ℝ} (hH : IsMHat.IsDiagDominant H) {d : n}
    (hd : ¬ IsMax d) (u w : ℕ → n → ℝ) (l : ℕ → ℝ) (r : ℕ → n → ℝ) (p : ℕ → n)
    (hu0 : u 0 = H d) (hrec : ∀ k, u (k + 1) = u k - l k • w k - r k)
    (hw : ∀ k j, j ≠ p k → w k j ≤ 0) (hwsum : ∀ k, 0 ≤ ∑ j, w k j) (hl : ∀ k, l k ≤ 0)
    (hp : ∀ k, p k < d) (hpivot : ∀ k, l k * w k (p k) = u k (p k))
    (hdrop : ∀ k j, r k j = 0 ∨ r k j = u k j - l k * w k j) (hdropDiag : ∀ k, r k d = 0)
    (hkeep : ∀ k, ∃ j₀, d < j₀ ∧ r k j₀ = 0 ∧
      ∀ j, d < j → u k j₀ - l k * w k j₀ ≤ u k j - l k * w k j) (k : ℕ) :
    (∀ j, j ≠ d → u k j ≤ 0) ∧ (0 ≤ ∑ j, u k j ∧ ∑ j, u k j ≤ ∑ j, u (k + 1) j) ∧
      ∑ j ∈ Finset.univ.filter (fun j => d < j), u k j < 0 ∧ 0 < u k d := by
  have base : ∀ m, (∀ j, j ≠ d → u m j ≤ 0) ∧ 0 ≤ ∑ j, u m j ∧ ∑ j, u m j ≤ ∑ j, u (m + 1) j :=
    fun m => IsMHat.ilut_rows_nonpos hH d u w l r p hu0 hrec hw hwsum hl hpivot hdrop hdropDiag m
  -- the entries to the right of the diagonal keep a strictly negative sum, by induction on `m`
  have hgt : ∀ m, ∑ j ∈ Finset.univ.filter (fun j => d < j), u m j < 0 := by
    intro m
    induction m with
    | zero => simp only [hu0]; exact hH.toIsMHat.sum_gt_neg d hd
    | succ m ih =>
      have hu : ∀ j, u (m + 1) j = u m j - l m * w m j - r m j := fun j => by
        rw [hrec m]; simp
      obtain ⟨j₀, hj₀, hj₀drop, hj₀min⟩ := hkeep m
      have hvsum : ∑ j ∈ Finset.univ.filter (fun j => d < j), (u m j - l m * w m j) < 0 := by
        refine lt_of_le_of_lt (Finset.sum_le_sum fun j hj => ?_) ih
        have hjd : d < j := (Finset.mem_filter.1 hj).2
        have hjp : j ≠ p m := ne_of_gt ((hp m).trans hjd)
        have : 0 ≤ l m * w m j := mul_nonneg_of_nonpos_of_nonpos (hl m) (hw m j hjp)
        linarith
      have hlt : ∑ j ∈ Finset.univ.filter (fun j => d < j), (u m j - l m * w m j)
          < ∑ _j ∈ Finset.univ.filter (fun j => d < j), (0 : ℝ) := by
        rw [Finset.sum_const_zero]; exact hvsum
      obtain ⟨j₁, hj₁mem, hj₁⟩ := Finset.exists_lt_of_sum_lt hlt
      have hj₀neg : u (m + 1) j₀ < 0 := by
        rw [hu j₀, hj₀drop, sub_zero]
        exact lt_of_le_of_lt (hj₀min j₁ (Finset.mem_filter.1 hj₁mem).2) hj₁
      exact lt_of_le_of_lt (sum_le_of_mem _ _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj₀⟩)
        fun j hj _ => (base (m + 1)).1 j (Finset.mem_filter.1 hj).2.ne') hj₀neg
  obtain ⟨hoff, hsum, hmono⟩ := base k
  exact ⟨hoff, ⟨hsum, hmono⟩, hgt k,
    pos_of_sum_nonneg_of_sum_gt_neg _ d hoff hsum (hgt k)⟩

end MHat

/-! ### One step of Gaussian elimination on the whole index type -/

section ElimStep

variable [Fintype n] [LinearOrder n] [DecidableEq n]

set_option linter.unusedDecidableInType false in
/-- For a linearly ordered finite index type and a point $p$, $\sum_c f(c) = f(p) + \sum_{c < p}
f(c) + \sum_{c > p} f(c)$. -/
private theorem sum_split_at (p : n) (f : n → ℝ) :
    ∑ c, f c = f p + (∑ c ∈ Finset.univ.filter (fun c => c < p), f c
      + ∑ c ∈ Finset.univ.filter (fun c => p < c), f c) := by
  rw [← Finset.add_sum_erase _ f (Finset.mem_univ p)]
  congr 1
  have hu : Finset.univ.erase p
      = Finset.univ.filter (fun c => c < p) ∪ Finset.univ.filter (fun c => p < c) := by
    ext c
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_filter,
      true_and]
    exact ⟨fun hc => lt_or_gt_of_ne hc, fun hc => hc.elim ne_of_lt ne_of_gt⟩
  rw [hu, Finset.sum_union]
  exact Finset.disjoint_left.2 fun c hc hc' =>
    absurd ((Finset.mem_filter.1 hc).2.trans (Finset.mem_filter.1 hc').2) (lt_irrefl c)

/-- The theorem of [fan1960note] on the whole index type (Theorem 10.1 of [saad2003iterative]). Let
$M$ be a real square M-matrix, indexed by a linearly ordered finite type, and let $p$ be an
index. Then the matrix `Matrix.elimStep M p`, obtained from $M$ by one step of Gaussian
elimination at the pivot $p$, is an M-matrix.

Off the diagonal, the argument is the argument of the book. For the inverse, $M_1 = (1 - N) M$
gives $M_1^{-1} = M^{-1}(1 + N)$. This agrees with $M^{-1}$ off the pivot column. In the pivot
column, its entry in row $i$ is
$$(m_{pp})^{-1} \Bigl(\delta_{ip} - \sum_{c < p} (M^{-1})_{ic} \, m_{cp}\Bigr),$$
which is nonnegative because $M^{-1}$ is nonnegative and the off-diagonal entries of $M$ are
nonpositive. The argument in [saad2003iterative] covers only the first pivot, where the pivot
column of $M_1$ is $m_{pp} e_p$. This form of the argument works at every pivot. -/
theorem IsMMatrix.isMMatrix_elimStep {M : Matrix n n ℝ} (hM : M.IsMMatrix) (p : n) :
    (elimStep M p).IsMMatrix := by
  have hpp : 0 < M p p := hM.diag_pos p
  have hdet : IsUnit M.det := (isUnit_iff_isUnit_det _).1 hM.isUnit
  have hMM : M * M⁻¹ = 1 := mul_nonsing_inv M hdet
  have hMinvM : M⁻¹ * M = 1 := nonsing_inv_mul M hdet
  have hE : elimStep M p = (1 - elimMultipliers M p) * M := by
    rw [elimStep, sub_mul, Matrix.one_mul]
  have hfac : elimStep M p * (M⁻¹ * elimMul M p) = 1 := by
    rw [hE, Matrix.mul_assoc, ← Matrix.mul_assoc M M⁻¹ (elimMul M p), hMM, Matrix.one_mul,
      one_sub_mul_elimMul]
  have hunit : IsUnit (elimStep M p) := ⟨⟨_, _, hfac, _root_.mul_eq_one_comm.1 hfac⟩, rfl⟩
  refine ⟨fun i j hij => ?_, hunit, ?_⟩
  · by_cases hi : p < i
    · rw [elimStep_apply_of_lt M hi]
      rcases eq_or_ne j p with rfl | hjp
      · rw [mul_assoc, inv_mul_cancel₀ hpp.ne', mul_one, sub_self]
      · have h1 : M i j ≤ 0 := hM.offDiag_nonpos i j hij
        have h3 : M p j ≤ 0 := hM.offDiag_nonpos p j (Ne.symm hjp)
        have h5 : M i p * (M p p)⁻¹ ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (hM.offDiag_nonpos i p (ne_of_gt hi))
            (inv_pos.2 hpp).le
        nlinarith [h5, h3]
    · rw [elimStep_apply_of_not_lt M hi]
      exact hM.offDiag_nonpos i j hij
  · rw [Matrix.inv_eq_right_inv hfac]
    refine entrywiseNonneg_iff.2 fun i j => ?_
    rw [elimMul, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
    rcases eq_or_ne j p with rfl | hjp
    · have hNsum : (M⁻¹ * elimMultipliers M j) i j
          = (∑ c ∈ Finset.univ.filter (fun c => j < c), M⁻¹ i c * M c j) * (M j j)⁻¹ := by
        rw [Matrix.mul_apply, Finset.sum_mul, Finset.sum_filter]
        refine Finset.sum_congr rfl fun c _ => ?_
        simp only [elimMultipliers_apply, and_true]
        split_ifs with h
        · ring
        · rw [mul_zero]
      have hall : M⁻¹ i j * M j j
          + ((∑ c ∈ Finset.univ.filter (fun c => c < j), M⁻¹ i c * M c j)
            + ∑ c ∈ Finset.univ.filter (fun c => j < c), M⁻¹ i c * M c j)
          = (1 : Matrix n n ℝ) i j := by
        rw [← sum_split_at j fun c => M⁻¹ i c * M c j, ← Matrix.mul_apply, hMinvM]
      have hlt : (∑ c ∈ Finset.univ.filter (fun c => c < j), M⁻¹ i c * M c j) ≤ 0 :=
        Finset.sum_nonpos fun c hc =>
          mul_nonpos_of_nonneg_of_nonpos (hM.inv_entrywiseNonneg.apply i c)
            (hM.offDiag_nonpos c j (ne_of_lt (Finset.mem_filter.1 hc).2))
      have hone : (0 : ℝ) ≤ (1 : Matrix n n ℝ) i j := by
        rcases eq_or_ne i j with rfl | h
        · rw [Matrix.one_apply_eq]; norm_num
        · rw [Matrix.one_apply_ne h]
      have hgoal : M⁻¹ i j
            + (∑ c ∈ Finset.univ.filter (fun c => j < c), M⁻¹ i c * M c j) * (M j j)⁻¹
          = ((1 : Matrix n n ℝ) i j
            - ∑ c ∈ Finset.univ.filter (fun c => c < j), M⁻¹ i c * M c j) * (M j j)⁻¹ := by
        have hSgt : (∑ c ∈ Finset.univ.filter (fun c => j < c), M⁻¹ i c * M c j)
            = (1 : Matrix n n ℝ) i j - M⁻¹ i j * M j j
              - ∑ c ∈ Finset.univ.filter (fun c => c < j), M⁻¹ i c * M c j := by
          linarith [hall]
        rw [hSgt, sub_mul, sub_mul, mul_assoc, mul_inv_cancel₀ hpp.ne', mul_one]
        ring
      rw [hNsum, hgoal]
      exact mul_nonneg (by linarith) (inv_pos.2 hpp).le
    · have h0 : (M⁻¹ * elimMultipliers M p) i j = 0 := by
        rw [Matrix.mul_apply]
        exact Finset.sum_eq_zero fun c _ => by simp [hjp]
      rw [h0, add_zero]
      exact hM.inv_entrywiseNonneg.apply i j

end ElimStep

/-! ### Existence for M-matrices, and the regular splitting -/

section Existence

variable [Fintype n] [LinearOrder n] [DecidableEq n]

open scoped Classical in
/-- The matrix obtained from $M$ by replacing the entries in the zero pattern $P$ by $0$. -/
private noncomputable def dropPattern (P : Set (n × n)) (M : Matrix n n ℝ) : Matrix n n ℝ :=
  Matrix.of fun i j => if (i, j) ∈ P then 0 else M i j

omit [Fintype n] [LinearOrder n] [DecidableEq n] in
/-- Inside the zero pattern, the dropped matrix has the entry $0$. -/
private theorem dropPattern_of_mem {P : Set (n × n)} {M : Matrix n n ℝ} {i j : n}
    (h : (i, j) ∈ P) : dropPattern P M i j = 0 := by
  classical
  simp [dropPattern, h]

omit [Fintype n] [LinearOrder n] [DecidableEq n] in
/-- Outside the zero pattern, the dropped matrix has the entries of $M$. -/
private theorem dropPattern_of_notMem {P : Set (n × n)} {M : Matrix n n ℝ} {i j : n}
    (h : (i, j) ∉ P) : dropPattern P M i j = M i j := by
  classical
  simp [dropPattern, h]

omit [LinearOrder n] in
/-- If $P$ contains no diagonal position and $M$ is an M-matrix, then the matrix obtained from $M$
by dropping the entries in $P$ is an M-matrix. -/
private theorem isMMatrix_dropPattern {P : Set (n × n)} (hP : ∀ i, (i, i) ∉ P)
    {M : Matrix n n ℝ} (hM : M.IsMMatrix) : (dropPattern P M).IsMMatrix := by
  refine hM.of_entrywiseLE (fun i j => ?_) fun i j hij => ?_
  · rcases Classical.em ((i, j) ∈ P) with h | h
    · rw [dropPattern_of_mem h]
      exact hM.offDiag_nonpos i j fun hc => hP i (hc ▸ h)
    · rw [dropPattern_of_notMem h]
  · rcases Classical.em ((i, j) ∈ P) with h | h
    · rw [dropPattern_of_mem h]
    · rw [dropPattern_of_notMem h]
      exact hM.offDiag_nonpos i j hij

/-- The invariant of the induction that proves Theorem 10.2 of [saad2003iterative]: after $k$
elimination steps, $L$ is the accumulated unipotent factor, $M$ is the working matrix, and
$LM - A$ is the residual so far; `rank` gives the position of an index in the increasing
enumeration, so that $\operatorname{rank} j < k$ means that column $j$ is already eliminated. -/
private structure ILUState (P : Set (n × n)) (A : Matrix n n ℝ) (rank : n → ℕ) (k : ℕ)
    (L M : Matrix n n ℝ) : Prop where
  /-- The diagonal entries of $L$ are $1$. -/
  l_diag : ∀ i, L i i = 1
  /-- $L$ is lower triangular. -/
  l_upper : ∀ i j, i < j → L i j = 0
  /-- $L$ differs from the identity only in the columns that are already eliminated. -/
  l_late : ∀ i j, i ≠ j → k ≤ rank j → L i j = 0
  /-- $L$ vanishes on the zero pattern. -/
  l_pattern : ∀ i j, (i, j) ∈ P → L i j = 0
  /-- The inverse of $L$ is entrywise nonnegative. -/
  l_inv_nonneg : L⁻¹.EntrywiseNonneg
  /-- $L$ is nonsingular. -/
  l_unit : IsUnit L
  /-- The working matrix is an M-matrix. -/
  m_mmatrix : M.IsMMatrix
  /-- The working matrix vanishes on the zero pattern. -/
  m_pattern : ∀ i j, (i, j) ∈ P → M i j = 0
  /-- The columns that are already eliminated are zero below the diagonal. -/
  m_lower : ∀ i j, j < i → rank j < k → M i j = 0
  /-- The residual is entrywise nonnegative. -/
  res_nonneg : (L * M - A).EntrywiseNonneg
  /-- The residual vanishes off the zero pattern. -/
  res_pattern : ∀ i j, (i, j) ∉ P → (L * M - A) i j = 0

/-- Let $A$ be a real square M-matrix, indexed by a linearly ordered finite type, and let $P$ be a
zero pattern that contains no diagonal position. Then there is an incomplete LU factorization
$(L, U)$ of $A$ for $P$ such that $U$ is an M-matrix, $LU$ is nonsingular, $(LU)^{-1}$ is
entrywise nonnegative, and $LU - A$ is entrywise nonnegative.

This strengthens `Matrix.IsMMatrix.exists_isILU` by the property that $U$ is an M-matrix. In
particular the pivots $U_{ii}$ are positive. -/
theorem IsMMatrix.exists_isILU_isMMatrix {A : Matrix n n ℝ} (hA : A.IsMMatrix) (P : Set (n × n))
    (hP : ∀ i, (i, i) ∉ P) :
    ∃ L U : Matrix n n ℝ, IsILU P A L U ∧ U.IsMMatrix ∧ IsUnit (L * U) ∧
      ((L * U)⁻¹).EntrywiseNonneg ∧ (L * U - A).EntrywiseNonneg := by
  classical
  obtain ⟨e⟩ : Nonempty (n ≃o Fin (Fintype.card n)) := ⟨(monoEquivOfFin n rfl).symm⟩
  have hlt : ∀ i j : n, i < j ↔ (e i : ℕ) < (e j : ℕ) := fun i j =>
    Iff.symm (Fin.lt_def.symm.trans e.lt_iff_lt)
  have key : ∀ k : ℕ, ∃ L M : Matrix n n ℝ, ILUState P A (fun j => (e j : ℕ)) k L M := by
    intro k
    induction k with
    | zero =>
      refine ⟨1, dropPattern P A, ?_⟩
      refine ⟨fun i => Matrix.one_apply_eq i, fun i j hij => Matrix.one_apply_ne (ne_of_lt hij),
        fun i j hij _ => Matrix.one_apply_ne hij,
        fun i j hij => Matrix.one_apply_ne fun hc => hP i (hc ▸ hij), ?_, isUnit_one,
        isMMatrix_dropPattern hP hA, fun i j hij => dropPattern_of_mem hij,
        fun i j _ hk => absurd hk (Nat.not_lt_zero _), ?_, ?_⟩
      · rw [_root_.inv_one]
        exact entrywiseNonneg_one
      · refine entrywiseNonneg_iff.2 fun i j => ?_
        rw [Matrix.sub_apply, Matrix.one_mul]
        rcases Classical.em ((i, j) ∈ P) with h | h
        · rw [dropPattern_of_mem h, zero_sub, neg_nonneg]
          exact hA.offDiag_nonpos i j fun hc => hP i (hc ▸ h)
        · rw [dropPattern_of_notMem h, sub_self]
      · intro i j h
        rw [Matrix.sub_apply, Matrix.one_mul, dropPattern_of_notMem h, sub_self]
    | succ k ih =>
      obtain ⟨L, M, hst⟩ := ih
      by_cases hk : k < Fintype.card n
      · obtain ⟨p, hp⟩ : ∃ p : n, (e p : ℕ) = k := ⟨e.symm ⟨k, hk⟩, by simp⟩
        have hplt : ∀ j : n, j < p ↔ (e j : ℕ) < k := fun j => by rw [hlt j p, hp]
        have hpgt : ∀ j : n, p < j ↔ k < (e j : ℕ) := fun j => by rw [hlt p j, hp]
        have hpne : ∀ j : n, p < j → (e j : ℕ) ≠ k := fun j hj => ((hpgt j).1 hj).ne'
        have hMpp : 0 < M p p := hst.m_mmatrix.diag_pos p
        -- the eliminated matrix and the dropped one
        have hEM : (elimStep M p).IsMMatrix := hst.m_mmatrix.isMMatrix_elimStep p
        refine ⟨L * elimMul M p, dropPattern P (elimStep M p), ?_⟩
        -- the accumulated factor, entrywise
        have hL' : ∀ i j : n, (L * elimMul M p) i j
            = L i j + if p < i ∧ j = p then M i p * (M p p)⁻¹ else 0 := by
          intro i j
          have hLN : (L * elimMultipliers M p) i j
              = if p < i ∧ j = p then M i p * (M p p)⁻¹ else 0 := by
            rw [Matrix.mul_apply]
            rcases eq_or_ne j p with rfl | hjp
            · have hterm : ∀ c : n, elimMultipliers M j c j
                  = if j < c then M c j * (M j j)⁻¹ else 0 := fun c => by simp
              rw [Finset.sum_congr rfl fun c _ => by rw [hterm c],
                Finset.sum_eq_single i (fun c _ hc => ?_) (by simp)]
              · simp only [and_true]
                split_ifs with h
                · rw [hst.l_diag i, one_mul]
                · rw [mul_zero]
              · split_ifs with h
                · rw [hst.l_late i c (Ne.symm hc) (le_of_lt ((hpgt c).1 h)), zero_mul]
                · rw [mul_zero]
            · rw [ite_eq_right fun h => hjp h.2]
              refine Finset.sum_eq_zero fun c _ => ?_
              rw [elimMultipliers_apply, ite_eq_right fun h => hjp h.2, mul_zero]
          rw [elimMul, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, hLN]
        -- the dropped mass
        obtain ⟨D, hD⟩ : ∃ D : Matrix n n ℝ,
            dropPattern P (elimStep M p) = elimStep M p + D :=
          ⟨dropPattern P (elimStep M p) - elimStep M p, by abel⟩
        have hDapply : ∀ i j : n, D i j = if (i, j) ∈ P then -(elimStep M p i j) else 0 := by
          intro i j
          have hDsub : D i j = dropPattern P (elimStep M p) i j - elimStep M p i j := by
            rw [hD]; simp
          rw [hDsub]
          rcases Classical.em ((i, j) ∈ P) with h | h
          · rw [dropPattern_of_mem h, zero_sub, ite_eq_left h]
          · rw [dropPattern_of_notMem h, sub_self, ite_eq_right h]
        have hDrow : ∀ i j : n, ¬ p < i → D i j = 0 := by
          intro i j hi
          rw [hDapply]
          rcases Classical.em ((i, j) ∈ P) with h | h
          · rw [ite_eq_left h, elimStep_apply_of_not_lt M hi, hst.m_pattern i j h, neg_zero]
          · rw [ite_eq_right h]
        have hDnonneg : ∀ i j : n, 0 ≤ D i j := by
          intro i j
          rw [hDapply]
          rcases Classical.em ((i, j) ∈ P) with h | h
          · rw [ite_eq_left h, neg_nonneg]
            exact hEM.offDiag_nonpos i j fun hc => hP i (hc ▸ h)
          · rw [ite_eq_right h]
        have hDpattern : ∀ i j : n, (i, j) ∉ P → D i j = 0 := fun i j h => by
          rw [hDapply, ite_eq_right h]
        -- the accumulated factor lets the dropped mass through unchanged
        have hLD : (L * elimMul M p) * D = D := by
          ext i j
          rw [Matrix.mul_apply, Finset.sum_eq_single i (fun c _ hc => ?_) (by simp)]
          · have hcond : ¬ (p < i ∧ i = p) := by rintro ⟨h1, rfl⟩; exact absurd h1 (lt_irrefl _)
            rw [hL' i i, ite_eq_right hcond, add_zero, hst.l_diag i, one_mul]
          · by_cases hc' : p < c
            · have hcond : ¬ (p < i ∧ c = p) := fun h => absurd h.2 (ne_of_gt hc')
              rw [hL' i c, hst.l_late i c (Ne.symm hc) (le_of_lt ((hpgt c).1 hc')),
                ite_eq_right hcond, add_zero, zero_mul]
            · rw [hDrow c j hc', mul_zero]
        -- the residual after the step
        have hres : (L * elimMul M p) * dropPattern P (elimStep M p) - A = (L * M - A) + D := by
          rw [hD, Matrix.mul_add, hLD, Matrix.mul_assoc, elimMul_mul_elimStep]
          abel
        refine ⟨fun i => ?_, fun i j hij => ?_, fun i j hij hkj => ?_, fun i j hij => ?_, ?_,
          hst.l_unit.mul (isUnit_elimMul M p), isMMatrix_dropPattern hP hEM,
          fun i j hij => dropPattern_of_mem hij, ?_, ?_, ?_⟩
        · have hcond : ¬ (p < i ∧ i = p) := by rintro ⟨h1, rfl⟩; exact absurd h1 (lt_irrefl _)
          rw [hL' i i, ite_eq_right hcond, add_zero, hst.l_diag i]
        · have hcond : ¬ (p < i ∧ j = p) := by
            rintro ⟨h1, rfl⟩; exact absurd (h1.trans hij) (lt_irrefl _)
          rw [hL' i j, hst.l_upper i j hij, ite_eq_right hcond, add_zero]
        · have hcond : ¬ (p < i ∧ j = p) := by
            rintro ⟨-, rfl⟩; omega
          rw [hL' i j, hst.l_late i j hij (by omega), ite_eq_right hcond, add_zero]
        · rcases Classical.em (p < i ∧ j = p) with h | h
          · rw [hL' i j, hst.l_pattern i j hij, ite_eq_left h, zero_add,
              hst.m_pattern i p (by rw [← h.2]; exact hij), zero_mul]
          · rw [hL' i j, hst.l_pattern i j hij, ite_eq_right h, add_zero]
        · rw [Matrix.mul_inv_rev, inv_elimMul]
          refine EntrywiseNonneg.mul (entrywiseNonneg_iff.2 fun i j => ?_) hst.l_inv_nonneg
          rw [Matrix.sub_apply, elimMultipliers_apply]
          rcases Classical.em (p < i ∧ j = p) with h | h
          · rw [ite_eq_left h, h.2, Matrix.one_apply_ne (ne_of_gt h.1), zero_sub, neg_nonneg]
            exact mul_nonpos_of_nonpos_of_nonneg
              (hst.m_mmatrix.offDiag_nonpos i p (ne_of_gt h.1)) (inv_pos.2 hMpp).le
          · rw [ite_eq_right h, sub_zero]
            rcases eq_or_ne i j with rfl | hij
            · rw [Matrix.one_apply_eq]; norm_num
            · rw [Matrix.one_apply_ne hij]
        · intro i j hji hkj
          rcases Classical.em ((i, j) ∈ P) with h | h
          · exact dropPattern_of_mem h
          rw [dropPattern_of_notMem h]
          rcases Nat.lt_succ_iff_lt_or_eq.1 hkj with hlt' | heq
          · have hMpj : M p j = 0 := hst.m_lower p j ((hplt j).2 hlt') hlt'
            rw [elimStep_apply_of_pivot_row_eq_zero M p i hMpj]
            exact hst.m_lower i j hji hlt'
          · have hjp : j = p := e.injective (Fin.ext (by rw [heq, hp]))
            rw [hjp] at hji ⊢
            exact elimStep_apply_pivot M hji hMpp.ne'
        · refine entrywiseNonneg_iff.2 fun i j => ?_
          rw [hres, Matrix.add_apply]
          exact add_nonneg (hst.res_nonneg.apply i j) (hDnonneg i j)
        · intro i j hij
          rw [hres, Matrix.add_apply, hst.res_pattern i j hij, hDpattern i j hij, add_zero]
      · exact ⟨L, M, hst.l_diag, hst.l_upper,
          fun i j hij hkj => hst.l_late i j hij (by omega),
          hst.l_pattern, hst.l_inv_nonneg, hst.l_unit, hst.m_mmatrix, hst.m_pattern,
          fun i j hji hkj => hst.m_lower i j hji (by
            omega),
          hst.res_nonneg, hst.res_pattern⟩
  obtain ⟨L, U, hst⟩ := key (Fintype.card n)
  have hupper : ∀ i j : n, j < i → U i j = 0 := fun i j hji =>
    hst.m_lower i j hji (e j).isLt
  have hLU : IsUnit (L * U) := hst.l_unit.mul hst.m_mmatrix.isUnit
  refine ⟨L, U, ⟨⟨hst.l_diag, hst.l_upper, hupper, hst.l_pattern, hst.m_pattern⟩, ?_⟩,
    hst.m_mmatrix, hLU, ?_, hst.res_nonneg⟩
  · intro i j hij
    have := hst.res_pattern i j hij
    rw [Matrix.sub_apply, sub_eq_zero] at this
    exact this
  · rw [Matrix.mul_inv_rev]
    exact hst.m_mmatrix.inv_entrywiseNonneg.mul hst.l_inv_nonneg

/-- The theorem of Meijerink and van der Vorst [meijerink1977iterative] (Theorem 10.2 of
[saad2003iterative]). Let $A$ be a real square M-matrix, indexed by a linearly ordered finite
type, and let $P$ be a zero pattern that contains no diagonal position. Then there is an
incomplete LU factorization $(L, U)$ of $A$ for $P$ such that $LU$ is nonsingular, $(LU)^{-1}$
is entrywise nonnegative, and the residual $LU - A$ is entrywise nonnegative. So no pivot
vanishes, and $A = LU - R$ is a regular splitting.

The proof is an induction over the pivots in increasing order. At each step, the working matrix
is eliminated below the pivot (`Matrix.elimStep`), which keeps it an M-matrix by the theorem of
[fan1960note] (`Matrix.IsMMatrix.isMMatrix_elimStep`). Then the entries in the zero pattern are
dropped. This moves the matrix up in the entrywise order, so it stays an M-matrix by the
comparison theorem `Matrix.IsMMatrix.of_entrywiseLE`. The accumulated factor $L$ differs from
the identity only in the columns that are already eliminated. So the dropped entries pass
through $L$ unchanged, and the residual is a sum of nonnegative matrices.

See `Matrix.IsILU.isRegular` for the conclusion as a regular splitting
`Stationary.Splitting.IsRegular`, and for the convergence of the iteration that it defines. -/
theorem IsMMatrix.exists_isILU {A : Matrix n n ℝ} (hA : A.IsMMatrix) (P : Set (n × n))
    (hP : ∀ i, (i, i) ∉ P) :
    ∃ L U : Matrix n n ℝ, IsILU P A L U ∧ IsUnit (L * U) ∧ ((L * U)⁻¹).EntrywiseNonneg ∧
      (L * U - A).EntrywiseNonneg := by
  obtain ⟨L, U, h, -, hu, hinv, hres⟩ := exists_isILU_isMMatrix hA P hP
  exact ⟨L, U, h, hu, hinv, hres⟩

end Existence

/-! ### Uniqueness of incomplete LU factors, and incomplete Cholesky for Stieltjes matrices -/

section ICExistence

variable [Fintype n] [LinearOrder n] [DecidableEq n] {P : Set (n × n)}

omit [DecidableEq n] in
/-- Incomplete LU factors with nonzero pivots are unique. Let $A$ be a real square matrix, indexed
by a linearly ordered finite type, and let $(L_1, U_1)$ and $(L_2, U_2)$ be incomplete LU
factorizations of $A$ for the same zero pattern $P$. If $(U_1)_{ii} \neq 0$ for every $i$, then
$L_1 = L_2$ and $U_1 = U_2$.

The proof goes row by row, and in each row from left to right. The constraint at $(i, j)$
determines $U_{ij}$ for $i \le j$, and $L_{ij} U_{jj}$ for $j < i$, from the entries that are
already known. -/
theorem IsILU.eq_of_diag_ne_zero {A L₁ U₁ L₂ U₂ : Matrix n n ℝ} (h₁ : IsILU P A L₁ U₁)
    (h₂ : IsILU P A L₂ U₂) (hd : ∀ i, U₁ i i ≠ 0) : L₁ = L₂ ∧ U₁ = U₂ := by
  classical
  have key : ∀ i j, L₁ i j = L₂ i j ∧ U₁ i j = U₂ i j := by
    intro i
    induction i using WellFoundedLT.induction with
    | ind i ihrow =>
      intro j
      induction j using WellFoundedLT.induction with
      | ind j ihcol =>
        by_cases hmem : (i, j) ∈ P
        · exact ⟨by rw [h₁.l_eq_zero_of_mem i j hmem, h₂.l_eq_zero_of_mem i j hmem],
            by rw [h₁.u_eq_zero_of_mem i j hmem, h₂.u_eq_zero_of_mem i j hmem]⟩
        have e₁ := h₁.agree i j hmem
        have e₂ := h₂.agree i j hmem
        rw [← e₂, Matrix.mul_apply, Matrix.mul_apply] at e₁
        rcases lt_or_ge j i with hji | hij
        · -- below the diagonal: `U` vanishes, and `L i j` is forced by the pivot `U j j`
          refine ⟨?_, by rw [h₁.u_eq_zero_of_gt i j hji, h₂.u_eq_zero_of_gt i j hji]⟩
          rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j),
            ← Finset.sum_erase_add _ _ (Finset.mem_univ j)] at e₁
          have hrest : ∑ k ∈ Finset.univ.erase j, L₁ i k * U₁ k j
              = ∑ k ∈ Finset.univ.erase j, L₂ i k * U₂ k j :=
            Finset.sum_congr rfl fun k hk => by
              rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hk) with hk' | hk'
              · rw [(ihcol k hk').1, (ihrow k (hk'.trans hji) j).2]
              · rw [h₁.u_eq_zero_of_gt k j hk', h₂.u_eq_zero_of_gt k j hk', mul_zero, mul_zero]
          rw [hrest, add_left_cancel_iff, ← (ihrow j hji j).2] at e₁
          exact mul_right_cancel₀ (hd j) e₁
        · -- on and above the diagonal: `L i i = 1`, and `U i j` is forced
          refine ⟨?_, ?_⟩
          · rcases hij.lt_or_eq with hij' | rfl
            · rw [h₁.l_eq_zero_of_lt i j hij', h₂.l_eq_zero_of_lt i j hij']
            · rw [h₁.l_diag, h₂.l_diag]
          rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
            ← Finset.sum_erase_add _ _ (Finset.mem_univ i), h₁.l_diag, h₂.l_diag, one_mul,
            one_mul] at e₁
          have hrest : ∑ k ∈ Finset.univ.erase i, L₁ i k * U₁ k j
              = ∑ k ∈ Finset.univ.erase i, L₂ i k * U₂ k j :=
            Finset.sum_congr rfl fun k hk => by
              rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hk) with hk' | hk'
              · rw [(ihcol k (hk'.trans_le hij)).1, (ihrow k hk' j).2]
              · rw [h₁.l_eq_zero_of_lt i k hk', h₂.l_eq_zero_of_lt i k hk', zero_mul, zero_mul]
          rw [hrest] at e₁
          exact add_left_cancel e₁
  exact ⟨Matrix.ext fun i j => (key i j).1, Matrix.ext fun i j => (key i j).2⟩

/-- The incomplete LU factorization of a symmetric matrix is symmetric. Let $A$ be a real symmetric
matrix, indexed by a linearly ordered finite type, let $P$ be a symmetric zero pattern, and let
$(L, U)$ be an incomplete LU factorization of $A$ for $P$ with $U_{ii} \neq 0$ for every $i$.
Then
$$U = D L^T, \qquad D = \operatorname{diag}(U_{11}, \dots, U_{nn}).$$

The pair $(U^T D^{-1}, D L^T)$ is also an incomplete LU factorization of $A^T = A$, so
`Matrix.IsILU.eq_of_diag_ne_zero` applies. -/
theorem IsILU.eq_diagonal_mul_transpose {A L U : Matrix n n ℝ} (h : IsILU P A L U)
    (hA : A.IsSymm) (hP : ∀ i j, (i, j) ∈ P → (j, i) ∈ P) (hd : ∀ i, U i i ≠ 0) :
    U = diagonal (fun i => U i i) * Lᵀ := by
  have h' : IsILU P A (Uᵀ * diagonal fun i => (U i i)⁻¹) (diagonal (fun i => U i i) * Lᵀ) :=
   { l_diag := fun i => by rw [mul_diagonal, transpose_apply, mul_inv_cancel₀ (hd i)]
     l_eq_zero_of_lt := fun i j hij => by
      rw [mul_diagonal, transpose_apply, h.u_eq_zero_of_gt j i hij, zero_mul]
     u_eq_zero_of_gt := fun i j hij => by
      rw [diagonal_mul, transpose_apply, h.l_eq_zero_of_lt j i hij, mul_zero]
     l_eq_zero_of_mem := fun i j hij => by
      rw [mul_diagonal, transpose_apply, h.u_eq_zero_of_mem j i (hP i j hij), zero_mul]
     u_eq_zero_of_mem := fun i j hij => by
      rw [diagonal_mul, transpose_apply, h.l_eq_zero_of_mem j i (hP i j hij), mul_zero]
     agree := fun i j hij => by
      have hji : (j, i) ∉ P := fun h => hij (hP j i h)
      have e : (Uᵀ * diagonal fun i => (U i i)⁻¹) * (diagonal (fun i => U i i) * Lᵀ)
          = (L * U)ᵀ := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), diagonal_mul_diagonal,
          show (fun i => (U i i)⁻¹ * U i i) = fun _ => (1 : ℝ) from
            funext fun i => inv_mul_cancel₀ (hd i),
          diagonal_one, Matrix.one_mul, transpose_mul]
      rw [e, transpose_apply, h.agree j i hji, hA.apply i j] }
  exact (h.eq_of_diag_ne_zero h' hd).2

omit [DecidableEq n] in
/-- Incomplete Cholesky factors exist for Stieltjes matrices ([meijerink1977iterative], the
symmetric case; [golub2013matrix], §11.5.8). Let $A$ be a real Stieltjes matrix, indexed by a
linearly ordered finite type, and let $P$ be a symmetric zero pattern that contains no diagonal
position. Then $A$ has an incomplete Cholesky factor $L$ for $P$ with $L_{ii} > 0$ for every
$i$. By `Matrix.IsIC.eq_of_diag_pos`, this factor is unique.

A Stieltjes matrix is an M-matrix, so it has an incomplete LU factorization whose upper factor
has positive pivots $d_i$ (`Matrix.IsMMatrix.exists_isILU_isMMatrix`). By symmetry $U = D L^T$
(`Matrix.IsILU.eq_diagonal_mul_transpose`), and $L D^{1/2}$ is the incomplete Cholesky factor.
The recursive algorithm incChol of [golub2013matrix], §11.5.8, keeps each Schur complement a
Stieltjes matrix by `Matrix.IsStieltjes.sub_drop`, and it computes the same factor. -/
theorem IsStieltjes.exists_isIC {A : Matrix n n ℝ} (hA : A.IsStieltjes)
    (hPs : ∀ i j, (i, j) ∈ P → (j, i) ∈ P) (hP : ∀ i, (i, i) ∉ P) :
    ∃ L : Matrix n n ℝ, IsIC P A L ∧ ∀ i, 0 < L i i := by
  classical
  obtain ⟨L, U, h, hU, -⟩ := hA.isMMatrix.exists_isILU_isMMatrix P hP
  have hpos : ∀ i, 0 < U i i := hU.diag_pos
  have hUeq := h.eq_diagonal_mul_transpose hA.isSymm hPs fun i => (hpos i).ne'
  refine ⟨L * diagonal fun i => Real.sqrt (U i i), ⟨fun i j hij => ?_, fun i j hij => ?_,
    fun i j hij => ?_⟩, fun i => ?_⟩
  · rw [mul_diagonal, h.l_eq_zero_of_lt i j hij, zero_mul]
  · rw [mul_diagonal, h.l_eq_zero_of_mem i j hij, zero_mul]
  · have e : (L * diagonal fun i => Real.sqrt (U i i)) *
        (L * diagonal fun i => Real.sqrt (U i i))ᵀ = L * U := by
      rw [transpose_mul, diagonal_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _),
        diagonal_mul_diagonal,
        show (fun i => Real.sqrt (U i i) * Real.sqrt (U i i)) = fun i => U i i from
          funext fun i => Real.mul_self_sqrt (hpos i).le, ← hUeq]
    rw [e]
    exact h.agree i j hij
  · rw [mul_diagonal, h.l_diag, one_mul]
    exact Real.sqrt_pos.2 (hpos i)

end ICExistence

section Regular

variable [Fintype n] [LinearOrder n] [DecidableEq n]
variable {P : Set (n × n)} {A L U : Matrix n n ℝ}

/-- The splitting of an incomplete factorization is regular (the remark after Theorem 10.2 of
[saad2003iterative]). Let $(L, U)$ be an incomplete LU factorization of a real square matrix $A$
for the zero pattern $P$. Assume that $LU$ is nonsingular, that $(LU)^{-1}$ is entrywise
nonnegative, and that $(LU - A)_{ij} \ge 0$ for $(i, j) \in P$. Then $A = LU - (LU - A)$ is a
regular splitting.

Off the pattern the residual vanishes, by Proposition 10.4 of [saad2003iterative]
(`Matrix.IsILU.sub_eq_zero_of_notMem`). The splitting is the `Stationary.Splitting A` with first
part $LU$. Together with
`Stationary.Splitting.IsRegular.complexSpectralRadius_lt_one_of_isMMatrix`, this gives the
convergence of the fixed-point iteration preconditioned by the incomplete factorization, for an
M-matrix. -/
theorem IsILU.isRegular (h : IsILU P A L U) (hu : IsUnit (L * U))
    (hinv : ((L * U)⁻¹).EntrywiseNonneg)
    (hres : ∀ i j, (i, j) ∈ P → 0 ≤ (L * U - A) i j) :
    (⟨L * U, hu⟩ : Stationary.Splitting A).IsRegular := by
  refine ⟨?_, entrywiseNonneg_iff.2 fun i j => ?_⟩
  · rwa [show Ring.inverse (L * U) = (L * U)⁻¹ from (nonsing_inv_eq_ringInverse _).symm]
  · by_cases hij : (i, j) ∈ P
    · exact hres i j hij
    · exact (h.sub_eq_zero_of_notMem hij).ge

/-- The fixed-point iteration preconditioned by an incomplete LU factorization converges for an
M-matrix (the corollary of Theorem 10.2 of [saad2003iterative]). Let $A$ be a real square
M-matrix, and let $(L, U)$ be an incomplete LU factorization of $A$ for the zero pattern $P$.
Assume that $LU$ is nonsingular, that $(LU)^{-1}$ is entrywise nonnegative, and that
$(LU - A)_{ij} \ge 0$ for $(i, j) \in P$. Then the iteration operator $I - (LU)^{-1} A$ has
spectral radius less than $1$.

The spectral radius is `Matrix.complexSpectralRadius`, the spectral radius of the real matrix as
a complex matrix. -/
theorem IsILU.complexSpectralRadius_lt_one (hA : A.IsMMatrix) (h : IsILU P A L U)
    (hu : IsUnit (L * U)) (hinv : ((L * U)⁻¹).EntrywiseNonneg)
    (hres : ∀ i j, (i, j) ∈ P → 0 ≤ (L * U - A) i j) :
    (⟨L * U, hu⟩ : Stationary.Splitting A).iterationOperator.complexSpectralRadius < 1 :=
  (h.isRegular hu hinv hres).complexSpectralRadius_lt_one_of_isMMatrix hA

end Regular

end Matrix

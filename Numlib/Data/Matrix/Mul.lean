/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Data.Matrix.Mul`, beside `Matrix.col_mul_eq_mulVec_col`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Columns and rows of products

Write $X_{:,q}$ for column $q$ of a matrix $X$, and $X_{r,:}$ for row $r$. This module proves column
and row identities for matrix products. The columns of $B - MA$ are $B_{:,q} - M A_{:,q}$, and the
rows of $B - AM$ are $B_{r,:} - A_{r,:} M$. These are the forms in which a columnwise or rowwise
error bound for one step of an elimination or of an orthogonal update is read off a matrix
statement. A matrix that acts on each column of $V$ as a scalar is diagonalized by $V$: if
$A V_{:,k} = \gamma_k V_{:,k}$ for all $k$, then $AV = V \operatorname{diag}(\gamma)$. Dually, if
$V_{k,:} A = \gamma_k V_{k,:}$ for all $k$, then $\operatorname{diag}(\gamma) V = VA$.

Selecting and inserting rows and columns commutes with multiplication in the expected way. For a
column $z$ inserted into a matrix, $P [A_1 \mid z \mid A_2] = [P A_1 \mid P z \mid P A_2]$. A
selection of rows of the left factor selects the same rows of the product. A submatrix applied to a
vector is the matrix applied to the extension of the vector by zero, restricted to the selected
rows. A diagonal congruence scales the entries: $(D^* M D)_{ij} = d_i^* M_{ij} d_j$ for
$D = \operatorname{diag}(d)$.

## Main results

* `Matrix.col_sub_mul`: $(B - MA)_{:,q} = B_{:,q} - M A_{:,q}$.
* `Matrix.row_sub_mul_eq_sub_vecMul`: $(B - AM)_{r,:} = B_{r,:} - A_{r,:} M$.
* `Matrix.row_sub_mul`: over a commutative ring, $(B - AM)_{r,:} = B_{r,:} - M^T A_{r,:}$.
* `Matrix.mul_eq_mul_diagonal_of_forall_mulVec_col`: if $A V_{:,k} = \gamma_k V_{:,k}$ for all $k$,
  then $AV = V \operatorname{diag}(\gamma)$.
* `Matrix.diagonal_mul_eq_mul_of_forall_vecMul_row`: if $V_{k,:} A = \gamma_k V_{k,:}$ for all $k$,
  then $\operatorname{diag}(\gamma) V = VA$.
* `Matrix.star_diagonal_mul_mul_diagonal_apply`: $(D^* M D)_{ij} = d_i^* M_{ij} d_j$ for
  $D = \operatorname{diag}(d)$.
* `Matrix.mul_of_insertNth`: $P [A_1 \mid z \mid A_2] = [P A_1 \mid P z \mid P A_2]$.
* `Matrix.submatrix_id_mul`: selecting rows of the left factor selects the same rows of the product.
* `Matrix.submatrix_mulVec_eq_comp_mulVec_extend`: a submatrix applied to a vector is the matrix
  applied to the extension of the vector by zero, restricted to the selected rows.

## Implementation notes

* Column $q$ of $X$ is `X.col q`, and row $r$ is `X.row r`. A matrix times a vector is
  `Matrix.mulVec`, written `*ᵥ`, and a row vector times a matrix is `Matrix.vecMul`, written `ᵥ*`.
* The three column and row identities hold by definition, like Mathlib's
  `Matrix.col_mul_eq_mulVec_col` and `Matrix.row_mul_eq_vecMul_row`.
-/

namespace Matrix

variable {ι κ R : Type*} [Fintype ι]

/-- Let $R$ be a non-unital non-associative ring, let $\iota$ be finite, and let
$B, A \in R^{\iota \times \kappa}$ and $M \in R^{\iota \times \iota}$. For every column index
$q \in \kappa$, $$(B - MA)_{:,q} = B_{:,q} - M A_{:,q}.$$
-/
theorem col_sub_mul [NonUnitalNonAssocRing R] (B : Matrix ι κ R) (M : Matrix ι ι R)
    (A : Matrix ι κ R) (q : κ) : (B - M * A).col q = B.col q - M *ᵥ A.col q :=
  rfl

/-- Let $R$ be a non-unital non-associative ring, let $\iota$ be finite, and let
$B, A \in R^{\kappa \times \iota}$ and $M \in R^{\iota \times \iota}$. For every row index
$r \in \kappa$, $$(B - AM)_{r,:} = B_{r,:} - A_{r,:} M,$$ where $A_{r,:} M$ is the product of a
row vector and a matrix (`Matrix.vecMul`). -/
theorem row_sub_mul_eq_sub_vecMul [NonUnitalNonAssocRing R] (B : Matrix κ ι R)
    (A : Matrix κ ι R) (M : Matrix ι ι R) (r : κ) :
    (B - A * M).row r = B.row r - A.row r ᵥ* M :=
  rfl

/-- Let $R$ be a non-unital commutative ring, let $\iota$ be finite, and let
$B, A \in R^{\kappa \times \iota}$ and $M \in R^{\iota \times \iota}$. For every row index
$r \in \kappa$, $$(B - AM)_{r,:} = B_{r,:} - M^T A_{r,:},$$ where $M^T A_{r,:}$ is the product
of a matrix and a vector (`Matrix.mulVec`). This is the form of
`Matrix.row_sub_mul_eq_sub_vecMul` over a commutative ring. -/
theorem row_sub_mul [NonUnitalCommRing R] (B : Matrix κ ι R) (A : Matrix κ ι R)
    (M : Matrix ι ι R) (r : κ) : (B - A * M).row r = B.row r - Mᵀ *ᵥ A.row r := by
  rw [row_sub_mul_eq_sub_vecMul, mulVec_transpose]

/-- Let $R$ be a commutative semiring, let $\iota$ and $\kappa$ be finite, and let
$A \in R^{\iota \times \iota}$, $V \in R^{\iota \times \kappa}$ and
$\gamma \colon \kappa \to R$. If $A V_{:,k} = \gamma_k V_{:,k}$ for every $k \in \kappa$, then
$$AV = V \operatorname{diag}(\gamma).$$

The column $V_{:,k}$ is `V.col k`, and the diagonal matrix is `Matrix.diagonal γ`. -/
theorem mul_eq_mul_diagonal_of_forall_mulVec_col [CommSemiring R] [Fintype κ] [DecidableEq κ]
    {A : Matrix ι ι R} {V : Matrix ι κ R} {γ : κ → R} (h : ∀ k, A *ᵥ V.col k = γ k • V.col k) :
    A * V = V * diagonal γ := by
  ext j k
  have hk := congrFun (h k) j
  rw [Pi.smul_apply, smul_eq_mul] at hk
  rw [mul_diagonal, mul_comm (V j k)]
  exact hk

/-- Let $R$ be a non-unital non-associative semiring, let $\iota$ and $\kappa$ be finite, and let
$A \in R^{\iota \times \iota}$, $V \in R^{\kappa \times \iota}$ and
$\gamma \colon \kappa \to R$. If $V_{k,:} A = \gamma_k V_{k,:}$ for every $k \in \kappa$, then
$$\operatorname{diag}(\gamma) V = VA.$$ This is the row form of
`Matrix.mul_eq_mul_diagonal_of_forall_mulVec_col`.

The row $V_{k,:}$ is `V.row k`, the product of a row vector and a matrix is `Matrix.vecMul`, and
the diagonal matrix is `Matrix.diagonal γ`. -/
theorem diagonal_mul_eq_mul_of_forall_vecMul_row [NonUnitalNonAssocSemiring R] [Fintype κ]
    [DecidableEq κ] {A : Matrix ι ι R} {V : Matrix κ ι R} {γ : κ → R}
    (h : ∀ k, V.row k ᵥ* A = γ k • V.row k) : diagonal γ * V = V * A := by
  ext k j
  have hk := congrFun (h k) j
  rw [Pi.smul_apply, smul_eq_mul] at hk
  rw [diagonal_mul]
  exact hk.symm

/-- Let $R$ be a semiring with an involution $x \mapsto x^*$ (a star ring), let $\iota$ be finite,
let $d \colon \iota \to R$ with $D = \operatorname{diag}(d)$, and let
$M \in R^{\iota \times \iota}$. Then for all $i, j \in \iota$,
$$(D^* M D)_{ij} = d_i^* M_{ij} d_j,$$
where $D^*$ is the conjugate transpose `star D`. -/
theorem star_diagonal_mul_mul_diagonal_apply [Semiring R] [StarRing R] [DecidableEq ι]
    (d : ι → R) (M : Matrix ι ι R) (i j : ι) :
    (star (diagonal d) * M * diagonal d) i j = star (d i) * M i j * d j := by
  rw [mul_diagonal, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul, Pi.star_apply]

/-- Let $R$ be a non-unital non-associative semiring, let $P \in R^{l \times m}$, $z \in R^m$,
$A \in R^{m \times n}$, and $k \in \{0, \dots, n\}$. Insert $z$ into $A$ as a new column at
position $k$, which gives an $m \times (n + 1)$ matrix $[A_1 \mid z \mid A_2]$. Then
$$P [A_1 \mid z \mid A_2] = [P A_1 \mid P z \mid P A_2],$$
that is, the product is $PA$ with the column $Pz$ inserted at position $k$.

The insertion is `Fin.insertNth k` applied to each row. -/
theorem mul_of_insertNth {l : Type*} [NonUnitalNonAssocSemiring R] {m n : ℕ}
    (P : Matrix l (Fin m) R) (z : Fin m → R) (A : Matrix (Fin m) (Fin n) R) (k : Fin (n + 1)) :
    P * of (fun i => Fin.insertNth k (z i) (A i)) =
      of fun i => Fin.insertNth k ((P *ᵥ z) i) ((P * A) i) := by
  ext i j
  obtain rfl | ⟨j, rfl⟩ := Fin.eq_self_or_eq_succAbove k j
  · simp [Matrix.mul_apply, mulVec, dotProduct]
  · simp [Matrix.mul_apply]

/-- Let $R$ be a non-unital non-associative semiring, let $\iota$ be finite, and let
$X \in R^{\iota' \times \iota}$, $Y \in R^{\iota \times \kappa}$ and
$e \colon \iota'' \to \iota'$. Selecting the rows $e$ of $X$ and then multiplying by $Y$ gives
the rows $e$ of $XY$: the matrix with entries $(XY)_{e(i), j}$. This is Mathlib's
`Matrix.submatrix_mul` with identity maps on the other indices, in a form suited to rewriting. -/
theorem submatrix_id_mul [NonUnitalNonAssocSemiring R] {ι' ι'' : Type*} (X : Matrix ι' ι R)
    (Y : Matrix ι κ R) (e : ι'' → ι') : X.submatrix e id * Y = (X * Y).submatrix e id := by
  rw [submatrix_mul X Y e id id Function.bijective_id, submatrix_id_id]

/-- Let $R$ be a non-unital non-associative semiring, let $n$ and $n'$ be finite, and let
$B \in R^{m \times n}$, $f \colon m' \to m$, an injective map $g \colon n' \to n$, and
$x \in R^{n'}$. Let $\tilde{x} \in R^n$ be the extension of $x$ by zero along $g$:
$\tilde{x}_{g(j)} = x_j$, and $\tilde{x}_c = 0$ for $c$ outside the image of $g$. Then the
submatrix $B_{f,g}$ with entries $B_{f(i), g(j)}$ satisfies
$$(B_{f,g}\, x)_i = (B \tilde{x})_{f(i)} \quad \text{for all } i \in m'.$$

The submatrix $B_{f,g}$ is `B.submatrix f g`, and the extension by zero is
`Function.extend g x 0`. -/
theorem submatrix_mulVec_eq_comp_mulVec_extend {m m' n n' : Type*}
    [NonUnitalNonAssocSemiring R] [Fintype n] [Fintype n'] (B : Matrix m n R) (f : m' → m)
    {g : n' → n} (hg : Function.Injective g) (x : n' → R) :
    B.submatrix f g *ᵥ x = (B *ᵥ Function.extend g x 0) ∘ f := by
  funext i
  simp only [mulVec, dotProduct, submatrix_apply, Function.comp_apply]
  exact Fintype.sum_of_injective g hg _ _ (fun k hk => by
    rw [Function.extend_apply' _ _ _ (by simpa using hk), Pi.zero_apply, mul_zero]) fun j => by
    rw [hg.extend_apply]

end Matrix

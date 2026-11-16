/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Block
import Numlib.LinearAlgebra.Matrix.Products

/-!
# The WY representation of a product of reflectors

Let $Q = Q_1 \cdots Q_r$ be a product of rank-one modifications of the identity,
$Q_j = I - \beta_j v_j v_j^H$, for example of Householder reflectors. Let
$Y = [v_1 \mid \cdots \mid v_r]$ be the matrix whose columns are the vectors $v_j$. Then $Q$ is a
modification of the identity of rank at most $r$ in two forms ([golub2013matrix], §5.1.7):

* $Q = I - W Y^H$ for a matrix $W$ with $r$ columns, the **WY representation** ((5.1.6) of
  [golub2013matrix], due to Bischof and Van Loan (1987));
* $Q = I - Y T Y^H$ for an upper triangular $r \times r$ matrix $T$, the **compact WY
  representation** (due to Schreiber and Van Loan (1989)), the form that blocked Householder
  algorithms use.

The module also proves that a *block reflector* $I - 2 V V^H$ with $V^H V = I$ is unitary (Schreiber
and Parlett (1987)).

## Main definitions

* `Matrix.IsWY`: the statement $Q = I - W Y^H$.
* `Matrix.wyW`: the factor $W$ of the WY representation, built by the recursion of Algorithm 5.1.2
  of [golub2013matrix].

## Main results

* `Matrix.IsWY.mul_one_sub_smul_vecMulVec`: Lemma 5.1.1 of [golub2013matrix]. Multiplication on the
  right by $I - \beta v v^H$ appends the column $z = \beta Q v$ to $W$ and the column $v$ to $Y$.
* `Matrix.isWY_prod`, `Matrix.isWY_prodFwd`: the matrix `Matrix.wyW` represents the whole product
  $Q_1 \cdots Q_r$.
* `Matrix.wyW_apply_eq_zero_of_apply_eq_zero`: a row on which every vector $v_j$ vanishes is a zero
  row of $W$.
* `Matrix.exists_compactWY`, `Matrix.exists_compactWY_prodFwd`: the compact representation
  $Q = I - Y T Y^H$ with $T$ upper triangular.
* `Matrix.one_sub_two_mul_conjTranspose_mem_unitaryGroup`: a block reflector $I - 2 V V^H$ with
  $V^H V = I$ is unitary.

## Implementation notes

* The algebra holds over any commutative ring with involution. None of it needs $Q$ or the factors
  $Q_j$ to be unitary: Lemma 5.1.1 of [golub2013matrix] assumes orthogonality, but its proof does
  not use it.
* The factors are indexed by `Fin r`. The product of the factors, in increasing order of the index,
  is `(List.ofFn fun j => 1 - β j • vecMulVec (v j) (star (v j))).prod`, which is `prodFwd` of the
  factors (`prodFwd_eq_prod_ofFn`).
* A column $z$ is appended to $W$ with `Fin.snoc` on the column index, as
  `Matrix.of fun i => Fin.snoc (W i) (z i)`. This is how the recursion grows $W$ and $Y$.
-/

open scoped Matrix

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] {r : ℕ}

/-- **The WY representation** ((5.1.6) of [golub2013matrix]). Let $Q$ be an $n \times n$ matrix and
let $W$ and $Y$ be $n \times r$ matrices over a ring with involution. Then $(W, Y)$ is a WY
representation of $Q$ if
$$Q = I - W Y^H.$$
Thus $Q$ is a modification of the identity of rank at most $r$. -/
def IsWY [Ring R] [Star R] (Q : Matrix n n R) (W Y : Matrix n (Fin r) R) : Prop :=
  Q = 1 - W * Yᴴ

section CommRing

variable [CommRing R] [StarRing R]

omit [Fintype n] [DecidableEq n] in
/-- Let $W$ and $Y$ be $n \times r$ matrices and $z$ and $v$ vectors of length $n$, over a
commutative ring with involution. Appending $z$ to $W$ and $v$ to $Y$ as last columns adds the
outer product of the new columns:
$$[W \mid z] \, [Y \mid v]^H = W Y^H + z v^H.$$
-/
theorem of_snoc_mul_conjTranspose_of_snoc (W Y : Matrix n (Fin r) R) (z v : n → R) :
    (of fun i => Fin.snoc (W i) (z i) : Matrix n (Fin (r + 1)) R) *
        (of fun i => Fin.snoc (Y i) (v i) : Matrix n (Fin (r + 1)) R)ᴴ =
      W * Yᴴ + vecMulVec z (star v) := by
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_castSucc, vecMulVec_apply]

/-- Let $Q = I - W Y^H$, where $W$ and $Y$ are $n \times r$ matrices over a commutative ring with
involution, and let $P = I - \beta v v^H$ for a scalar $\beta$ and a vector $v$. Then
$$Q P = I - [W \mid z] \, [Y \mid v]^H, \qquad z = \beta Q v.$$
This is Lemma 5.1.1 of [golub2013matrix].

No orthogonality of $Q$ or $P$ is needed. -/
theorem IsWY.mul_one_sub_smul_vecMulVec {Q : Matrix n n R} {W Y : Matrix n (Fin r) R}
    (h : IsWY Q W Y) (β : R) (v : n → R) :
    IsWY (Q * (1 - β • vecMulVec v (star v))) (of fun i => Fin.snoc (W i) ((β • (Q *ᵥ v)) i))
      (of fun i => Fin.snoc (Y i) (v i)) := by
  rw [IsWY, of_snoc_mul_conjTranspose_of_snoc, smul_vecMulVec, ← sub_sub, ← h, mul_sub, mul_one,
    mul_smul_comm, mul_vecMulVec]

/-- **The factor $W$ of the WY representation** of $Q_1 \cdots Q_r$, $Q_j = I - \beta_j v_j v_j^H$,
by the recursion of Algorithm 5.1.2 of [golub2013matrix]. Let
$Y_j = [v_1 \mid \cdots \mid v_j]$. Then $W_0$ is the empty $n \times 0$ matrix, and
$$W_{j+1} = [W_j \mid \beta_{j+1} (I - W_j Y_j^H) v_{j+1}].$$
In particular $W_1 = \beta_1 v_1$. -/
def wyW : {r : ℕ} → (Fin r → R) → (Fin r → n → R) → Matrix n (Fin r) R
  | 0, _, _ => 0
  | r + 1, β, v =>
    of fun i => Fin.snoc (α := fun _ => R) (wyW (Fin.init β) (Fin.init v) i)
      ((β (Fin.last r) • ((1 - wyW (Fin.init β) (Fin.init v) *
        (of fun i j => Fin.init v j i : Matrix n (Fin r) R)ᴴ) *ᵥ v (Fin.last r))) i)

/-- The recursion that defines `Matrix.wyW`: the factor $W$ for $r + 1$ terms is the factor $W_r$
for the first $r$ terms, with the column $\beta_{r+1} (I - W_r Y_r^H) v_{r+1}$ appended. -/
theorem wyW_succ (β : Fin (r + 1) → R) (v : Fin (r + 1) → n → R) :
    wyW β v = of fun i => Fin.snoc (α := fun _ => R) (wyW (Fin.init β) (Fin.init v) i)
      ((β (Fin.last r) • ((1 - wyW (Fin.init β) (Fin.init v) *
        (of fun i j => Fin.init v j i : Matrix n (Fin r) R)ᴴ) *ᵥ v (Fin.last r))) i) :=
  rfl

/-- **Every product of $r$ rank-one modifications of the identity has a WY representation** ((5.1.6)
and Algorithm 5.1.2 of [golub2013matrix]). Let $\beta_1, \dots, \beta_r$ be scalars and
$v_1, \dots, v_r$ vectors of length $n$ over a commutative ring with involution. Then
$$(I - \beta_1 v_1 v_1^H) \cdots (I - \beta_r v_r v_r^H) = I - W Y^H,$$
where $W$ is `Matrix.wyW β v` and $Y$ is the matrix whose columns are the vectors $v_j$. -/
theorem isWY_prod (β : Fin r → R) (v : Fin r → n → R) :
    IsWY (List.ofFn fun j => 1 - β j • vecMulVec (v j) (star (v j))).prod (wyW β v)
      (of fun i j => v j i) := by
  induction r with
  | zero => simp [IsWY]
  | succ r ih =>
    have h := ih (Fin.init β) (Fin.init v)
    have h' := h.mul_one_sub_smul_vecMulVec (β (Fin.last r)) (v (Fin.last r))
    rw [IsWY] at h
    convert h' using 1
    · rw [List.ofFn_succ', List.prod_concat]
      rfl
    · rw [wyW_succ, h]
    · ext i j
      refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [Fin.init]

/-- **Rows on which every vector vanishes are zero rows of $W$** ([golub2013matrix], §5.2.3: "the
first $\lambda - 1$ rows of $W_k$ and $Y_k$ are zero"). Let $S$ be a set of row indices with
$(v_j)_i = 0$ for all $j$ and all $i \in S$. Then the factor $W$ of `Matrix.wyW β v` has
$w_{ik} = 0$ for all $i \in S$ and all $k$.

Each new column $\beta (I - W Y^H) v$ of $W$ is a linear combination of the vectors $v_j$. -/
theorem wyW_apply_eq_zero_of_apply_eq_zero {S : Set n} (β : Fin r → R) (v : Fin r → n → R)
    (hv : ∀ j, ∀ i ∈ S, v j i = 0) : ∀ i ∈ S, ∀ k, wyW β v i k = 0 := by
  induction r with
  | zero => exact fun _ _ k => k.elim0
  | succ r ih =>
    intro i hi k
    have ih' := ih (Fin.init β) (Fin.init v) (fun j => hv j.castSucc) i hi
    rw [wyW_succ, of_apply]
    refine Fin.lastCases ?_ (fun k => ?_) k
    · rw [Fin.snoc_last, Pi.smul_apply, sub_mulVec, one_mulVec, ← mulVec_mulVec, Pi.sub_apply,
        hv _ i hi, mulVec, dotProduct]
      simp [ih']
    · rw [Fin.snoc_castSucc, ih']

omit [StarRing R] in
/-- The bordered matrix $\begin{bmatrix} T & t \\ 0 & b \end{bmatrix}$ of the recursion for the
compact WY representation. -/
private def compactWYStep (T : Matrix (Fin r) (Fin r) R) (t : Fin r → R) (b : R) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
  of (Fin.snoc (α := fun _ => Fin (r + 1) → R) (fun i => Fin.snoc (α := fun _ => R) (T i) (t i))
    (Fin.snoc (α := fun _ => R) 0 b))

omit [StarRing R] in
private theorem compactWYStep_isUpperTriangular {T : Matrix (Fin r) (Fin r) R}
    (hT : T.IsUpperTriangular) (t : Fin r → R) (b : R) :
    (compactWYStep T t b).IsUpperTriangular := by
  intro i j hji
  change j < i at hji
  induction i using Fin.lastCases with
  | last =>
    obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.2 (Fin.ne_last_of_lt hji)
    simp [compactWYStep]
  | cast i =>
    induction j using Fin.lastCases with
    | last => exact absurd hji (not_lt.2 (Fin.castSucc_lt_last i).le)
    | cast j => simpa [compactWYStep] using hT (Fin.castSucc_lt_castSucc_iff.1 hji)

omit [Fintype n] [DecidableEq n] [StarRing R] in
private theorem of_snoc_mul_compactWYStep (Y : Matrix n (Fin r) R) (w : n → R)
    (T : Matrix (Fin r) (Fin r) R) (t : Fin r → R) (b : R) :
    (of fun i => Fin.snoc (Y i) (w i) : Matrix n (Fin (r + 1)) R) * compactWYStep T t b =
      of fun i => Fin.snoc ((Y * T) i) ((Y *ᵥ t + b • w) i) := by
  ext i j
  refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [compactWYStep, Matrix.mul_apply, Fin.sum_univ_castSucc, mulVec, dotProduct, mul_comm]

/-- One step of the recursion for the compact WY representation: if $Q = I - Y T Y^H$, then $Q (I -
b w w^H) = I - [Y \mid w] \begin{bmatrix} T & t \\ 0 & b \end{bmatrix} [Y \mid w]^H$ with
$t = -b T Y^H w$. -/
private theorem compactWY_step {Q : Matrix n n R} {Y : Matrix n (Fin r) R}
    {T : Matrix (Fin r) (Fin r) R} (hQ : Q = 1 - Y * T * Yᴴ) (b : R) (w : n → R) :
    Q * (1 - b • vecMulVec w (star w)) =
      1 - (of fun i => Fin.snoc (Y i) (w i) : Matrix n (Fin (r + 1)) R) *
        compactWYStep T (-b • (T *ᵥ (Yᴴ *ᵥ w))) b *
        (of fun i => Fin.snoc (Y i) (w i) : Matrix n (Fin (r + 1)) R)ᴴ := by
  have h := IsWY.mul_one_sub_smul_vecMulVec (W := Y * T) hQ b w
  rw [IsWY, of_snoc_mul_conjTranspose_of_snoc] at h
  rw [h, of_snoc_mul_compactWYStep, of_snoc_mul_conjTranspose_of_snoc, hQ, sub_mulVec,
    one_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_smul, smul_sub, neg_smul, add_comm]
  abel_nf

/-- **The compact WY representation** (Schreiber and Van Loan (1989); [golub2013matrix], §5.1.7).
Let $\beta_1, \dots, \beta_r$ be scalars and $v_1, \dots, v_r$ vectors of length $n$ over a
commutative ring with involution, and let $Y$ be the matrix whose columns are the vectors $v_j$.
Then there is an upper triangular $r \times r$ matrix $T$ with
$$(I - \beta_1 v_1 v_1^H) \cdots (I - \beta_r v_r v_r^H) = I - Y T Y^H.$$

The proof builds $T$ by the recursion $T_1 = \beta_1$ and $T_{j+1} = \begin{bmatrix} T_j &
-\beta_{j+1} T_j Y_j^H v_{j+1} \\ 0 & \beta_{j+1} \end{bmatrix}$, with
$Y_j = [v_1 \mid \cdots \mid v_j]$. -/
theorem exists_compactWY (β : Fin r → R) (v : Fin r → n → R) :
    ∃ T : Matrix (Fin r) (Fin r) R, T.IsUpperTriangular ∧
      (List.ofFn fun j => 1 - β j • vecMulVec (v j) (star (v j))).prod =
        1 - (of fun i j => v j i) * T * (of fun i j => v j i)ᴴ := by
  induction r with
  | zero => exact ⟨0, fun i => i.elim0, by simp⟩
  | succ r ih =>
    obtain ⟨T, hT, hQ⟩ := ih (Fin.init β) (Fin.init v)
    have hY : (of fun i j => v j i : Matrix n (Fin (r + 1)) R) =
        of fun i => Fin.snoc ((of fun i j => Fin.init v j i : Matrix n (Fin r) R) i)
          (v (Fin.last r) i) := by
      ext i j
      refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [Fin.init]
    refine ⟨_, compactWYStep_isUpperTriangular hT (-β (Fin.last r) • (T *ᵥ
      ((of fun i j => Fin.init v j i : Matrix n (Fin r) R)ᴴ *ᵥ v (Fin.last r))))
      (β (Fin.last r)), ?_⟩
    rw [List.ofFn_succ', List.prod_concat, hY]
    exact compactWY_step hQ _ _

/-- **The WY representation of a forward product**: `Matrix.isWY_prod` for `prodFwd`. Let
$(\beta_k)_{k \in \mathbb{N}}$ be scalars and $(v_k)_{k \in \mathbb{N}}$ vectors of length $n$,
and let $r \in \mathbb{N}$. Then the product of the first $r$ factors $I - \beta_k v_k v_k^H$,
in increasing order of $k$, is $I - W Y^H$, where $W$ is `Matrix.wyW` of the first $r$ terms and
$Y$ is the matrix with columns $v_0, \dots, v_{r-1}$. -/
theorem isWY_prodFwd (β : ℕ → R) (v : ℕ → n → R) (r : ℕ) :
    IsWY (prodFwd (fun k => 1 - β k • vecMulVec (v k) (star (v k))) r)
      (wyW (fun j : Fin r => β j) fun j => v j) (of fun i (j : Fin r) => v j i) := by
  rw [prodFwd_eq_prod_ofFn]
  exact isWY_prod _ _

/-- **The compact WY representation of a forward product**: `Matrix.exists_compactWY` for `prodFwd`.
Let $(\beta_k)_{k \in \mathbb{N}}$ be scalars and $(v_k)_{k \in \mathbb{N}}$ vectors of length
$n$, and let $r \in \mathbb{N}$. Then there is an upper triangular $r \times r$ matrix $T$ such
that the product of the first $r$ factors $I - \beta_k v_k v_k^H$, in increasing order of $k$,
is $I - Y T Y^H$, where $Y$ is the matrix with columns $v_0, \dots, v_{r-1}$. -/
theorem exists_compactWY_prodFwd (β : ℕ → R) (v : ℕ → n → R) (r : ℕ) :
    ∃ T : Matrix (Fin r) (Fin r) R, T.IsUpperTriangular ∧
      prodFwd (fun k => 1 - β k • vecMulVec (v k) (star (v k))) r =
        1 - (of fun i (j : Fin r) => v j i) * T * (of fun i (j : Fin r) => v j i)ᴴ := by
  rw [prodFwd_eq_prod_ofFn]
  exact exists_compactWY (fun j : Fin r => β j) fun j => v j

/-- **Block reflectors are unitary** ([golub2013matrix], §5.1.7; Schreiber and Parlett (1987)). Let
$V$ be an $n \times k$ matrix over a commutative ring with involution, with $V^H V = I$. Then
$I - 2 V V^H$ is unitary.

The matrix $I - 2 V V^H$ is Hermitian and is its own inverse. -/
theorem one_sub_two_mul_conjTranspose_mem_unitaryGroup {κ : Type*} [Fintype κ]
    [DecidableEq κ] {V : Matrix n κ R} (hV : Vᴴ * V = 1) :
    1 - (2 : R) • (V * Vᴴ) ∈ unitaryGroup n R := by
  have hX : V * Vᴴ * (V * Vᴴ) = V * Vᴴ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ, hV, Matrix.one_mul]
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose, conjTranspose_sub, conjTranspose_one,
    conjTranspose_smul, conjTranspose_mul, conjTranspose_conjTranspose, star_ofNat, two_smul]
  simp only [sub_mul, mul_sub, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, hX]
  abel

end CommRing

end Matrix

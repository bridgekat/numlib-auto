/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.PlaneRotation`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Basic.Sign.Defs
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Plane embeddings and plane rotations

Let $n$ be an index type, let $j, k \in n$ with $j \neq k$, and let
$G = (g_{ab})_{a, b \in \{0, 1\}}$ be a $2 \times 2$ matrix. The **plane embedding** $E_{jk}(G)$ is
the $n \times n$ matrix that agrees with the identity outside the rows and columns $j$ and $k$, and
that carries $g_{00}, g_{01}, g_{10}, g_{11}$ at the positions $(j, j), (j, k), (k, j), (k, k)$.
Multiplication by $E_{jk}(G)$ changes a vector or a matrix only through the coordinates $j$ and $k$.
Embeddings in one plane compose as their $2 \times 2$ blocks, $E_{jk}(G) E_{jk}(G') = E_{jk}(G G')$,
$E_{jk}(G)$ is unitary exactly when $G$ is, and $\det E_{jk}(G) = \det G$. These facts are proved
once, for an arbitrary semiring or commutative ring.

The **plane rotation** is the real instance $R_{jk}(c, s) = E_{jk}\left(\begin{bmatrix} c & -s \\ s
& c \end{bmatrix}\right)$. For $c = \cos \theta$ and $s = \sin \theta$ it rotates the
$(j, k)$-coordinate plane by the angle $\theta$ and fixes its orthogonal complement. It is the
Givens rotation of numerical linear algebra. The **Givens pair** of $(a, b) \neq (0, 0)$ is
$(c, s) = (a, b) / \sqrt{a^2 + b^2}$, and $R_{jk}(c, s)^T$ then sends $(a, b)$ to
$(\sqrt{a^2 + b^2}, 0)$; this is the elementary step of a Givens $QR$ factorization. The
**hyperbolic rotation** $H_{jk}(c, s) = E_{jk}\left(\begin{bmatrix} c & -s \\ -s & c
\end{bmatrix}\right)$ with $c^2 - s^2 = 1$ is the indefinite counterpart: it satisfies $H J H^T = J$
for every diagonal signature $J$ with $J_{jj} = 1$ and $J_{kk} = -1$. The **hyperbolic pair** of
(6.5.13) in [golub2013matrix] makes it annihilate the $k$-th entry of $x$ when $|x_k| < |x_j|$, and
no hyperbolic rotation does so when $|x_j| \le |x_k|$ and $x_k \neq 0$.

## Main definitions

* `Matrix.planeEmbed`: the plane embedding $E_{jk}(G)$ of a $2 \times 2$ matrix $G$.
* `Matrix.adjacentEmbed`: the plane embedding in the adjacent plane $(j, j + 1)$ of
  $\{0, \dots, M - 1\}$, indexed by $j \in \mathbb{N}$, and the identity when $j + 1 \ge M$.
* `Matrix.planeRotation`: the plane rotation $R_{jk}(c, s)$ with cosine $c$ and sine $s$.
* `Matrix.givensPair`: the Givens pair $(a, b) / \sqrt{a^2 + b^2}$, and $(1, 0)$ when $a = b = 0$.
* `Matrix.planeReflector`: the $2 \times 2$ reflection $\begin{bmatrix} -\cos \varphi & \sin \varphi
  \\ \sin \varphi & \cos \varphi \end{bmatrix}$ of [golub2013matrix], §12.2.10, an involution of
  determinant $-1$.
* `Matrix.IsJOrthogonal`: the condition $H J H^T = J$, which [golub2013matrix], (6.5.11), calls
  $S$-orthogonality.
* `Matrix.jOrthogonalSubmonoid`: the submonoid of the $J$-orthogonal matrices.
* `Matrix.hyperbolicRotation`, `Matrix.hyperbolicPair`: the hyperbolic rotation and the pair
  $(c, s)$ that makes it introduce a zero ([golub2013matrix], §6.5.4).

## Main results

* `Matrix.planeEmbed_mul_apply`, `Matrix.mul_planeEmbed_apply`, `Matrix.planeEmbed_mulVec_apply`:
  left multiplication by $E_{jk}(G)$ combines the rows $j$ and $k$ of a possibly rectangular matrix,
  right multiplication combines the columns $j$ and $k$, and all other entries stay the same.
* `Matrix.commute_planeEmbed_planeEmbed`: plane embeddings in disjoint planes commute.
* `Matrix.planeEmbed_mul_planeEmbed`: $E_{jk}(G) E_{jk}(G') = E_{jk}(G G')$.
* `Matrix.planeEmbed_transpose`, `Matrix.planeEmbed_conjTranspose`: $E_{jk}(G)^T = E_{jk}(G^T)$ and
  $E_{jk}(G)^H = E_{jk}(G^H)$.
* `Matrix.det_planeEmbed`: $\det E_{jk}(G) = \det G$.
* `Matrix.planeEmbed_mem_unitaryGroup_iff`: $E_{jk}(G)$ is unitary if and only if $G$ is unitary.
* `Matrix.transpose_planeRotation_mul_self`, `Matrix.planeRotation_mem_orthogonalGroup`: a plane
  rotation with $c^2 + s^2 = 1$ is orthogonal.
* `Matrix.transpose_planeRotation_givensPair_mulVec`: the transpose of the rotation built from the
  Givens pair of $(x_j, x_k)$ annihilates the $k$-th entry of $x$ and puts $\sqrt{x_j^2 + x_k^2}$ in
  the $j$-th entry.
* `Matrix.conj_planeRotation_apply_of_ne`, `Matrix.conj_planeRotation_apply_jj`,
  `Matrix.conj_planeRotation_apply_kk`, `Matrix.conj_planeRotation_apply_jk`,
  `Matrix.conj_planeRotation_apply_col_j`, `Matrix.conj_planeRotation_apply_col_k`,
  `Matrix.conj_planeRotation_apply_row_j`, `Matrix.conj_planeRotation_apply_row_k`: the entries of
  $R^T M R$ for a square matrix $M$ and a plane rotation $R$, in the form in which an algorithm
  reads off what one rotation did.
* `Matrix.isJOrthogonal_hyperbolicRotation`: a hyperbolic rotation with $c^2 - s^2 = 1$ is
  $J$-orthogonal.
* `Matrix.hyperbolicRotation_hyperbolicPair_mulVec`: if $|x_k| < |x_j|$, the hyperbolic rotation
  built from the hyperbolic pair of $(x_j, x_k)$ annihilates the $k$-th entry of $x$.
* `Matrix.not_exists_hyperbolic_of_abs_le`: if $|x_1| \le |x_2|$ and $x_2 \neq 0$, no hyperbolic
  pair annihilates $x_2$.
* `Matrix.isJOrthogonal_iff_mem_symplecticGroup`: for Mathlib's symplectic form `Matrix.J`,
  $J$-orthogonality is membership in `Matrix.symplecticGroup`.

## Implementation notes

* The sign convention of the rotation is that of Jacobi's method: the rows $j$ and $k$ of
  $R_{jk}(c, s)$ are $(c, -s)$ and $(s, c)$ in the columns $j$ and $k$. For $c = \cos \theta$ and
  $s = \sin \theta$, the matrix $R_{jk}(c, s)$ turns $e_j$ towards $e_k$ by the angle $\theta$, and
  $R_{jk}(c, s)^T$ turns it by $-\theta$.
* The Givens matrix $G(i, k, \theta)$ of [quarteroni2000numerical], (5.43), carries $\sin \theta$ in
  position $(i, k)$, so it is `Matrix.planeRotation i k (cos θ) (-sin θ)`. The pair $(c, s)$ of
  (5.44) and (5.51) there is $(c, -s)$ here. `Matrix.givensPair` is written in the convention of
  this module.
* Only the orthogonality statements assume $c^2 + s^2 = 1$. No result needs an order on the index
  type.
* The definition of `Matrix.planeEmbed` is degenerate at $j = k$. Every lemma that needs $j \neq k$
  has it as a hypothesis.
* The plane rotations are used in Jacobi's eigenvalue algorithm (`Numlib.Eigen.Jacobi`), which
  conjugates a symmetric matrix by a rotation chosen to annihilate one off-diagonal entry, and in
  the Givens $QR$ factorization of a Hessenberg matrix (`Numlib.LinearAlgebra.Matrix.QR`). The
  complex Givens rotations `Krylov.givensMatrix` of the progressive $QR$ factorization in
  `Numlib.Krylov.Hessenberg` are $E_{k, k+1}\left(\begin{bmatrix} \bar c & \bar s \\ -s & c
  \end{bmatrix}\right)$ (`Krylov.givensMatrix_eq_planeEmbed`).
* `Matrix.adjacentEmbed` indexes the adjacent planes by $j \in \mathbb{N}$, so that a sweep over the
  planes $(j, j + 1)$ is a product over a list of natural numbers, with no bounds to carry.
-/

open Finset

namespace Matrix

variable {n R : Type*} [DecidableEq n]

/-! ### Embedding a $2 \times 2$ matrix in a coordinate plane -/

section PlaneEmbed

variable [Zero R] [One R]

/-- The **plane embedding** of a $2 \times 2$ matrix $G = (g_{ab})_{a, b \in \{0, 1\}}$ over $R$ in
the $(j, k)$ coordinate plane is the matrix $E_{jk}(G) \in R^{n \times n}$ defined as follows.
In the row $j$, it has $g_{00}$ in the column $j$, $g_{01}$ in the column $k$ and $0$ elsewhere.
In the row $k$, it has $g_{10}$ in the column $j$, $g_{11}$ in the column $k$ and $0$ elsewhere.
Every other row is the corresponding row of the identity matrix.

Here $R$ needs only a zero and a one. The cases are tested in the order row $j$, row $k$, and
within a row column $j$, column $k$. For $j = k$ the definition is degenerate, and no lemma
assumes anything about it. -/
def planeEmbed (j k : n) (G : Matrix (Fin 2) (Fin 2) R) : Matrix n n R :=
  Matrix.of fun p q =>
    if p = j then (if q = j then G 0 0 else if q = k then G 0 1 else 0)
    else if p = k then (if q = j then G 1 0 else if q = k then G 1 1 else 0)
    else if p = q then 1 else 0

variable {j k : n} (G : Matrix (Fin 2) (Fin 2) R)

/-- The entries of a plane embedding: $E_{jk}(G)_{pq}$ is given by the case distinction of the
definition, first on the row $p$ and then on the column $q$. This holds for all $j$ and $k$,
also for $j = k$. -/
theorem planeEmbed_apply (p q : n) :
    planeEmbed j k G p q =
      if p = j then (if q = j then G 0 0 else if q = k then G 0 1 else 0)
      else if p = k then (if q = j then G 1 0 else if q = k then G 1 1 else 0)
      else if p = q then 1 else 0 := rfl

/-- Outside the rows $j$ and $k$, a plane embedding agrees with the identity: if $p \neq j$ and
$p \neq k$, then $E_{jk}(G)_{pq} = \delta_{pq}$ for every $q$. -/
theorem planeEmbed_apply_of_ne_left {p : n} (hpj : p ≠ j) (hpk : p ≠ k) (q : n) :
    planeEmbed j k G p q = if p = q then 1 else 0 := by
  simp [planeEmbed_apply, hpj, hpk]

/-- Outside the columns $j$ and $k$, a plane embedding agrees with the identity: if $q \neq j$ and
$q \neq k$, then $E_{jk}(G)_{pq} = \delta_{pq}$ for every $p$. -/
theorem planeEmbed_apply_of_ne_right (p : n) {q : n} (hqj : q ≠ j) (hqk : q ≠ k) :
    planeEmbed j k G p q = if p = q then 1 else 0 := by
  rw [planeEmbed_apply]
  split_ifs <;> simp_all

/-- For $j \neq k$, the $2 \times 2$ block of a plane embedding is the embedded matrix: with
$i_0 = j$ and $i_1 = k$,
$$E_{jk}(G)_{i_a i_b} = g_{ab} \qquad \text{for all } a, b \in \{0, 1\}.$$

In Lean the map $a \mapsto i_a$ is `![j, k]`. -/
theorem planeEmbed_apply_vecCons (hjk : j ≠ k) (a b : Fin 2) :
    planeEmbed j k G (![j, k] a) (![j, k] b) = G a b := by
  fin_cases a <;> fin_cases b <;> simp [planeEmbed_apply, hjk.symm]

/-- For $j \neq k$, a plane embedding determines its block: the map $G \mapsto E_{jk}(G)$ from
$R^{2 \times 2}$ to $R^{n \times n}$ is injective. -/
theorem planeEmbed_injective (hjk : j ≠ k) :
    Function.Injective (planeEmbed j k : Matrix (Fin 2) (Fin 2) R → Matrix n n R) := by
  intro G G' h
  ext a b
  rw [← planeEmbed_apply_vecCons G hjk a b, ← planeEmbed_apply_vecCons G' hjk a b, h]

/-- For $j \neq k$, the plane embedding of the $2 \times 2$ identity is the $n \times n$ identity:
$E_{jk}(I_2) = I$. -/
theorem planeEmbed_one (hjk : j ≠ k) : planeEmbed j k (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  ext p q
  simp only [planeEmbed_apply, Matrix.one_apply]
  split_ifs <;> simp_all

/-- For $j \neq k$, a plane embedding is the identity if and only if its block is: $E_{jk}(G) = I$
if and only if $G = I_2$. -/
theorem planeEmbed_eq_one_iff (hjk : j ≠ k) : planeEmbed j k G = 1 ↔ G = 1 :=
  ⟨fun h => planeEmbed_injective hjk (h.trans (planeEmbed_one hjk).symm),
    fun h => h ▸ planeEmbed_one hjk⟩

/-- For $j \neq k$, transposition commutes with the plane embedding: $E_{jk}(G)^T = E_{jk}(G^T)$. -/
theorem planeEmbed_transpose (hjk : j ≠ k) : (planeEmbed j k G)ᵀ = planeEmbed j k Gᵀ := by
  ext p q
  simp only [transpose_apply, planeEmbed_apply]
  split_ifs <;> subst_vars <;> simp_all

end PlaneEmbed

/-- Let $R$ be a semiring with a star operation. For $j \neq k$ and $G \in R^{2 \times 2}$,
conjugate transposition commutes with the plane embedding: $E_{jk}(G)^H = E_{jk}(G^H)$. -/
theorem planeEmbed_conjTranspose [NonAssocSemiring R] [StarRing R] {j k : n} (hjk : j ≠ k)
    (G : Matrix (Fin 2) (Fin 2) R) : (planeEmbed j k G)ᴴ = planeEmbed j k Gᴴ := by
  ext p q
  simp only [conjTranspose_apply, planeEmbed_apply]
  split_ifs <;> subst_vars <;> simp_all

/-! ### The action of a plane embedding on rows and columns -/

section Mul

variable [Fintype n] [NonAssocSemiring R] {j k : n} (G : Matrix (Fin 2) (Fin 2) R)

/-- For $j \neq k$ and $f \colon n \to R$, the sum $\sum_r E_{jk}(G)_{pr} f_r$ is
$g_{00} f_j + g_{01} f_k$ for $p = j$, $g_{10} f_j + g_{11} f_k$ for $p = k$, and $f_p$
otherwise. -/
private theorem sum_planeEmbed_mul (hjk : j ≠ k) (f : n → R) (p : n) :
    ∑ r, planeEmbed j k G p r * f r =
      if p = j then G 0 0 * f j + G 0 1 * f k
      else if p = k then G 1 0 * f j + G 1 1 * f k
      else f p := by
  by_cases hpj : p = j
  · subst hpj
    rw [ite_eq_left rfl, Fintype.sum_eq_add _ _ hjk fun r ⟨hrj, hrk⟩ => by
      simp [planeEmbed_apply, hrj, hrk]]
    simp [planeEmbed_apply, hjk.symm]
  by_cases hpk : p = k
  · subst hpk
    rw [ite_eq_right hpj, ite_eq_left rfl, Fintype.sum_eq_add _ _ hjk fun r ⟨hrj, hrk⟩ => by
      simp [planeEmbed_apply, hrj, hrk, hpj]]
    simp [planeEmbed_apply, hjk.symm]
  · rw [ite_eq_right hpj, ite_eq_right hpk]
    simp [planeEmbed_apply_of_ne_left G hpj hpk, ite_mul, Finset.sum_ite_eq]

/-- For $j \neq k$ and $f \colon n \to R$, the sum $\sum_r f_r E_{jk}(G)_{rq}$ is
$f_j g_{00} + f_k g_{10}$ for $q = j$, $f_j g_{01} + f_k g_{11}$ for $q = k$, and $f_q$
otherwise. -/
private theorem sum_mul_planeEmbed (hjk : j ≠ k) (f : n → R) (q : n) :
    ∑ r, f r * planeEmbed j k G r q =
      if q = j then f j * G 0 0 + f k * G 1 0
      else if q = k then f j * G 0 1 + f k * G 1 1
      else f q := by
  by_cases hqj : q = j
  · subst hqj
    rw [ite_eq_left rfl, Fintype.sum_eq_add _ _ hjk fun r ⟨hrj, hrk⟩ => by
      simp [planeEmbed_apply, hrj, hrk]]
    simp [planeEmbed_apply, hjk.symm]
  by_cases hqk : q = k
  · subst hqk
    rw [ite_eq_right hqj, ite_eq_left rfl, Fintype.sum_eq_add _ _ hjk fun r ⟨hrj, hrk⟩ => by
      simp [planeEmbed_apply, hrj, hrk]]
    simp [planeEmbed_apply, hjk.symm]
  · rw [ite_eq_right hqj, ite_eq_right hqk]
    simp [planeEmbed_apply_of_ne_right G _ hqj hqk, mul_ite, Finset.sum_ite_eq']

/-- Let $R$ be a semiring, let $n$ be finite, and let $j \neq k$. For a matrix
$M \in R^{n \times m}$, where $m$ is any index type, left multiplication by a plane embedding
combines the rows $j$ and $k$ of $M$ and leaves the other rows unchanged:
$$(E_{jk}(G) M)_{pq} = \begin{cases} g_{00} M_{jq} + g_{01} M_{kq} & \text{if } p = j, \\ g_{10}
  M_{jq} + g_{11} M_{kq} & \text{if } p = k, \\ M_{pq} & \text{otherwise.} \end{cases}$$

This is the row update of Program 34 of [quarteroni2000numerical]. -/
theorem planeEmbed_mul_apply {m : Type*} (hjk : j ≠ k) (M : Matrix n m R) (p : n) (q : m) :
    (planeEmbed j k G * M) p q =
      if p = j then G 0 0 * M j q + G 0 1 * M k q
      else if p = k then G 1 0 * M j q + G 1 1 * M k q
      else M p q := by
  rw [Matrix.mul_apply]
  exact sum_planeEmbed_mul G hjk (fun r => M r q) p

/-- Let $R$ be a semiring, let $n$ be finite, and let $j \neq k$. For a matrix
$M \in R^{m \times n}$, where $m$ is any index type, right multiplication by a plane embedding
combines the columns $j$ and $k$ of $M$ and leaves the other columns unchanged:
$$(M E_{jk}(G))_{pq} = \begin{cases} M_{pj} g_{00} + M_{pk} g_{10} & \text{if } q = j, \\ M_{pj}
  g_{01} + M_{pk} g_{11} & \text{if } q = k, \\ M_{pq} & \text{otherwise.} \end{cases}$$

This is the column update of Program 35 of [quarteroni2000numerical]. -/
theorem mul_planeEmbed_apply {m : Type*} (hjk : j ≠ k) (M : Matrix m n R) (p : m) (q : n) :
    (M * planeEmbed j k G) p q =
      if q = j then M p j * G 0 0 + M p k * G 1 0
      else if q = k then M p j * G 0 1 + M p k * G 1 1
      else M p q := by
  rw [Matrix.mul_apply]
  exact sum_mul_planeEmbed G hjk (fun r => M p r) q

/-- Let $R$ be a semiring, let $n$ be finite, and let $j \neq k$. A plane embedding acts on a vector
$x \in R^n$ through the entries $x_j$ and $x_k$ alone:
$$(E_{jk}(G) x)_p = \begin{cases} g_{00} x_j + g_{01} x_k & \text{if } p = j, \\ g_{10} x_j +
  g_{11} x_k & \text{if } p = k, \\ x_p & \text{otherwise.} \end{cases}$$
-/
theorem planeEmbed_mulVec_apply (hjk : j ≠ k) (x : n → R) (p : n) :
    (planeEmbed j k G *ᵥ x) p =
      if p = j then G 0 0 * x j + G 0 1 * x k
      else if p = k then G 1 0 * x j + G 1 1 * x k
      else x p :=
  sum_planeEmbed_mul G hjk x p

/-- Let $R$ be a semiring, let $n$ be finite, and let $j \neq k$. For $x \in R^n$ and
$p \notin \{j, k\}$, a plane embedding leaves the entry $p$ unchanged: $(E_{jk}(G) x)_p = x_p$. -/
theorem planeEmbed_mulVec_apply_of_ne (hjk : j ≠ k) (x : n → R) {p : n} (hpj : p ≠ j)
    (hpk : p ≠ k) : (planeEmbed j k G *ᵥ x) p = x p := by
  rw [planeEmbed_mulVec_apply G hjk, ite_eq_right hpj, ite_eq_right hpk]

/-- Let $R$ be a semiring, let $n$ be finite, and let $j \neq k$. A row vector $x \in R^n$ times a
plane embedding is
$$(x^T E_{jk}(G))_q = \begin{cases} x_j g_{00} + x_k g_{10} & \text{if } q = j, \\ x_j g_{01} +
  x_k g_{11} & \text{if } q = k, \\ x_q & \text{otherwise.} \end{cases}$$

This is the transposed form of `Matrix.planeEmbed_mulVec_apply`. -/
theorem vecMul_planeEmbed_apply (hjk : j ≠ k) (x : n → R) (q : n) :
    (x ᵥ* planeEmbed j k G) q =
      if q = j then x j * G 0 0 + x k * G 1 0
      else if q = k then x j * G 0 1 + x k * G 1 1
      else x q :=
  sum_mul_planeEmbed G hjk x q

/-- Let $R$ be a semiring, let $n$ be finite, and let $j \neq k$. Two plane embeddings in the same
plane compose as their blocks: for $G, G' \in R^{2 \times 2}$,
$$E_{jk}(G) \, E_{jk}(G') = E_{jk}(G G').$$
-/
theorem planeEmbed_mul_planeEmbed (hjk : j ≠ k) (G' : Matrix (Fin 2) (Fin 2) R) :
    planeEmbed j k G * planeEmbed j k G' = planeEmbed j k (G * G') := by
  ext p q
  rw [planeEmbed_mul_apply G hjk]
  simp only [planeEmbed_apply, Matrix.mul_apply, Fin.sum_univ_two]
  split_ifs <;> simp_all [hjk.symm]

end Mul

/-! ### Determinant and unitarity -/

section CommRing

variable [Fintype n] [CommRing R] {j k : n} (G : Matrix (Fin 2) (Fin 2) R)

/-- For $j \neq k$, the equivalence between $\{0, 1\}$ and the two-element set $\{j, k\}$ that sends
$0$ to $j$ and $1$ to $k$. -/
private def planeEquiv (hjk : j ≠ k) : Fin 2 ≃ {i : n // i = j ∨ i = k} where
  toFun a := ![⟨j, Or.inl rfl⟩, ⟨k, Or.inr rfl⟩] a
  invFun i := if (i : n) = j then 0 else 1
  left_inv a := by fin_cases a <;> simp [hjk.symm]
  right_inv := by
    rintro ⟨i, hi | hi⟩ <;> subst hi <;> simp [hjk.symm]

/-- Let $R$ be a commutative ring, let $n$ be finite, and let $j \neq k$. The determinant of a plane
embedding is the determinant of its block:
$$\det E_{jk}(G) = \det G.$$

The proof uses that $E_{jk}(G)$ is block triangular with the diagonal blocks $G$ and an
identity. -/
theorem det_planeEmbed (hjk : j ≠ k) : (planeEmbed j k G).det = G.det := by
  rw [twoBlockTriangular_det (planeEmbed j k G) (fun i => i = j ∨ i = k) fun i hi l hl => by
    rw [planeEmbed_apply_of_ne_left G (fun h => hi (Or.inl h)) fun h => hi (Or.inr h)]
    exact ite_eq_right fun h : i = l => hi (h ▸ hl)]
  have hone : toSquareBlockProp (planeEmbed j k G) (fun i => ¬(i = j ∨ i = k)) = 1 := by
    ext ⟨a, ha⟩ ⟨b, hb⟩
    rw [toSquareBlockProp_def, of_apply, Matrix.one_apply,
      planeEmbed_apply_of_ne_left G (fun h => ha (Or.inl h)) fun h => ha (Or.inr h)]
    simp [Subtype.ext_iff]
  rw [hone, det_one, mul_one, ← det_submatrix_equiv_self (planeEquiv hjk)]
  congr 1
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [planeEquiv, toSquareBlockProp_def, planeEmbed_apply, hjk.symm]

/-- Let $R$ be a commutative ring with a star operation, let $n$ be finite, and let $j \neq k$. A
plane embedding $E_{jk}(G)$ is unitary if and only if $G$ is unitary.

With `Krylov.givensMatrix_eq_planeEmbed`, this reduces the unitarity of the rotations
`Krylov.givensMatrix` to the unitarity of their $2 \times 2$ blocks. -/
theorem planeEmbed_mem_unitaryGroup_iff [StarRing R] (hjk : j ≠ k) :
    planeEmbed j k G ∈ unitaryGroup n R ↔ G ∈ unitaryGroup (Fin 2) R := by
  rw [mem_unitaryGroup_iff', mem_unitaryGroup_iff', star_eq_conjTranspose, star_eq_conjTranspose,
    planeEmbed_conjTranspose hjk, planeEmbed_mul_planeEmbed _ hjk, planeEmbed_eq_one_iff _ hjk]

/-- Let $R$ be a commutative ring and let $n$ be finite. Plane embeddings in disjoint coordinate
planes commute: if $j \neq k$ and $\{j, k\} \cap \{j', k'\} = \emptyset$, then $E_{jk}(A)$ and
$E_{j'k'}(B)$ commute for all $A, B \in R^{2 \times 2}$. -/
theorem commute_planeEmbed_planeEmbed {j' k' : n} (hjk : j ≠ k) (h₁ : j ≠ j') (h₂ : j ≠ k')
    (h₃ : k ≠ j') (h₄ : k ≠ k') (A B : Matrix (Fin 2) (Fin 2) R) :
    Commute (planeEmbed j k A) (planeEmbed j' k' B) := by
  have hr := planeEmbed_apply_of_ne_left B h₁ h₂
  have hr' := planeEmbed_apply_of_ne_left B h₃ h₄
  have hc := fun p => planeEmbed_apply_of_ne_right B p h₁ h₂
  have hc' := fun p => planeEmbed_apply_of_ne_right B p h₃ h₄
  ext p q
  rw [planeEmbed_mul_apply _ hjk, mul_planeEmbed_apply _ hjk]
  simp only [hr, hr', hc, hc']
  have hkj : k ≠ j := Ne.symm hjk
  by_cases hp : p = j <;> by_cases hp' : p = k <;> by_cases hq : q = j <;>
    by_cases hq' : q = k <;> simp_all [eq_comm (b := q)]

/-- Let $R$ be a commutative ring and let $n$ be finite. If $d \colon n \to R$ satisfies
$d_j = d_k = 1$, then $E_{jk}(A)$ commutes with the diagonal matrix $\operatorname{diag}(d)$ for
every $A \in R^{2 \times 2}$. -/
theorem commute_planeEmbed_diagonal {d : n → R} (hj : d j = 1) (hk : d k = 1)
    (A : Matrix (Fin 2) (Fin 2) R) : Commute (planeEmbed j k A) (diagonal d) := by
  ext p q
  rw [mul_diagonal, diagonal_mul, planeEmbed_apply]
  split_ifs <;> subst_vars <;> simp_all

end CommRing

/-! ### Plane rotations -/

/-- The **plane rotation** of the $(j, k)$-plane with cosine $c$ and sine $s$ is the real matrix
$$R_{jk}(c, s) = E_{jk}\left(\begin{bmatrix} c & -s \\ s & c \end{bmatrix}\right).$$
It is the identity matrix with its rows $j$ and $k$ replaced by $(c, -s)$ and $(s, c)$ in the
columns $j$ and $k$, and by $0$ in the other columns.

No condition on $c$ and $s$ is imposed; the orthogonality results assume $c^2 + s^2 = 1$. The
Givens matrix $G(i, k, \theta)$ of [quarteroni2000numerical], (5.43), is
`Matrix.planeRotation i k (cos θ) (-sin θ)`. -/
def planeRotation (j k : n) (c s : ℝ) : Matrix n n ℝ := planeEmbed j k !![c, -s; s, c]

/-- The transpose of the rotation block is the block of the opposite angle: $\begin{bmatrix} c & -s
\\ s & c \end{bmatrix}^T = \begin{bmatrix} c & s \\ -s & c \end{bmatrix}$. -/
theorem rotationBlock_transpose (c s : ℝ) : !![c, -s; s, c]ᵀ = !![c, s; -s, c] :=
  eta_fin_two _

variable {j k : n} {c s : ℝ}

/-- For $j \neq k$, the entries of a plane rotation, column by column: the column $j$ of
$R_{jk}(c, s)$ is $c e_j + s e_k$, the column $k$ is $-s e_j + c e_k$, and every other column
$q$ is $e_q$. Here $e_q$ is the $q$-th unit vector, and the entry in row $t$ is written as a sum
of Kronecker deltas. -/
theorem planeRotation_apply (hjk : j ≠ k) (t q : n) :
    planeRotation j k c s t q =
      if q = j then (if t = j then c else 0) + (if t = k then s else 0)
      else if q = k then (if t = j then -s else 0) + (if t = k then c else 0)
      else if t = q then 1 else 0 := by
  rw [planeRotation, planeEmbed_apply]
  split_ifs <;> simp_all [hjk.symm]

/-- For $j \neq k$, the transpose of a plane rotation is the rotation by the opposite angle:
$R_{jk}(c, s)^T = R_{jk}(c, -s)$. -/
theorem planeRotation_transpose (hjk : j ≠ k) :
    (planeRotation j k c s)ᵀ = planeRotation j k c (-s) := by
  rw [planeRotation, planeEmbed_transpose _ hjk, planeRotation]
  congr 1
  ext a b
  fin_cases a <;> fin_cases b <;> simp

variable [Fintype n]

/-- Let $n$ be finite and $j \neq k$. Right multiplication of $M \in \mathbb{R}^{n \times n}$ by a
plane rotation combines the columns $j$ and $k$:
$$(M R_{jk}(c, s))_{pq} = \begin{cases} c M_{pj} + s M_{pk} & \text{if } q = j, \\ -s M_{pj} + c
  M_{pk} & \text{if } q = k, \\ M_{pq} & \text{otherwise.} \end{cases}$$
-/
theorem mul_planeRotation_apply (hjk : j ≠ k) (M : Matrix n n ℝ) (p q : n) :
    (M * planeRotation j k c s) p q =
      if q = j then c * M p j + s * M p k
      else if q = k then -s * M p j + c * M p k
      else M p q := by
  rw [planeRotation, mul_planeEmbed_apply _ hjk]
  split_ifs <;> simp <;> ring

/-- Let $n$ be finite and $j \neq k$. Left multiplication of $M \in \mathbb{R}^{n \times n}$ by the
transpose of a plane rotation combines the rows $j$ and $k$:
$$(R_{jk}(c, s)^T M)_{pq} = \begin{cases} c M_{jq} + s M_{kq} & \text{if } p = j, \\ -s M_{jq} +
  c M_{kq} & \text{if } p = k, \\ M_{pq} & \text{otherwise.} \end{cases}$$
-/
theorem transpose_planeRotation_mul_apply (hjk : j ≠ k) (M : Matrix n n ℝ) (p q : n) :
    ((planeRotation j k c s)ᵀ * M) p q =
      if p = j then c * M j q + s * M k q
      else if p = k then -s * M j q + c * M k q
      else M p q := by
  rw [planeRotation_transpose hjk, planeRotation, planeEmbed_mul_apply _ hjk]
  split_ifs <;> simp

/-- Let $n$ be finite and $j \neq k$. The transpose of a plane rotation acts on a vector
$x \in \mathbb{R}^n$ through its entries $x_j$ and $x_k$:
$$(R_{jk}(c, s)^T x)_p = \begin{cases} c x_j + s x_k & \text{if } p = j, \\ -s x_j + c x_k &
  \text{if } p = k, \\ x_p & \text{otherwise.} \end{cases}$$
-/
theorem transpose_planeRotation_mulVec_apply (hjk : j ≠ k) (x : n → ℝ) (p : n) :
    ((planeRotation j k c s)ᵀ *ᵥ x) p =
      if p = j then c * x j + s * x k
      else if p = k then -s * x j + c * x k
      else x p := by
  rw [planeRotation_transpose hjk, planeRotation, planeEmbed_mulVec_apply _ hjk]
  split_ifs <;> simp

/-- Let $n$ be finite and $j \neq k$. If $c^2 + s^2 = 1$, the plane rotation is orthogonal:
$$R_{jk}(c, s)^T R_{jk}(c, s) = I.$$
-/
theorem transpose_planeRotation_mul_self (hjk : j ≠ k) (hcs : c ^ 2 + s ^ 2 = 1) :
    (planeRotation j k c s)ᵀ * planeRotation j k c s = 1 := by
  rw [planeRotation_transpose hjk, planeRotation, planeRotation, planeEmbed_mul_planeEmbed _ hjk,
    planeEmbed_eq_one_iff _ hjk]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [hcs]

/-- Let $n$ be finite and $j \neq k$. If $c^2 + s^2 = 1$, the plane rotation $R_{jk}(c, s)$ belongs
to the orthogonal group of $\mathbb{R}^{n \times n}$. -/
theorem planeRotation_mem_orthogonalGroup (hjk : j ≠ k) (hcs : c ^ 2 + s ^ 2 = 1) :
    planeRotation j k c s ∈ orthogonalGroup n ℝ :=
  (mem_orthogonalGroup_iff' n ℝ).2 (transpose_planeRotation_mul_self hjk hcs)

/-! ### Conjugation by a plane rotation -/

/-- Let $n$ be finite, $j \neq k$ and $M \in \mathbb{R}^{n \times n}$, and write $R = R_{jk}(c, s)$.
Conjugation by $R$ leaves every entry outside the rows and columns $j$ and $k$ unchanged: if
$p, q \notin \{j, k\}$, then
$$(R^T M R)_{pq} = M_{pq}.$$
-/
theorem conj_planeRotation_apply_of_ne (hjk : j ≠ k) (M : Matrix n n ℝ) {p q : n}
    (hpj : p ≠ j) (hpk : p ≠ k) (hqj : q ≠ j) (hqk : q ≠ k) :
    ((planeRotation j k c s)ᵀ * M * planeRotation j k c s) p q = M p q := by
  simp [transpose_planeRotation_mul_apply hjk, mul_planeRotation_apply hjk,
    hpj, hpk, hqj, hqk]

/-- Let $n$ be finite, $j \neq k$ and $M \in \mathbb{R}^{n \times n}$, and write $R = R_{jk}(c, s)$.
The $(j, j)$ entry of the conjugate is
$$(R^T M R)_{jj} = c (c M_{jj} + s M_{jk}) + s (c M_{kj} + s M_{kk}).$$
-/
theorem conj_planeRotation_apply_jj (hjk : j ≠ k) (M : Matrix n n ℝ) :
    ((planeRotation j k c s)ᵀ * M * planeRotation j k c s) j j
      = c * (c * M j j + s * M j k) + s * (c * M k j + s * M k k) := by
  simp [transpose_planeRotation_mul_apply hjk, mul_planeRotation_apply hjk]
  ring

/-- Let $n$ be finite, $j \neq k$ and $M \in \mathbb{R}^{n \times n}$, and write $R = R_{jk}(c, s)$.
The $(k, k)$ entry of the conjugate is
$$(R^T M R)_{kk} = -s (-s M_{jj} + c M_{jk}) + c (-s M_{kj} + c M_{kk}).$$
-/
theorem conj_planeRotation_apply_kk (hjk : j ≠ k) (M : Matrix n n ℝ) :
    ((planeRotation j k c s)ᵀ * M * planeRotation j k c s) k k
      = -s * (-s * M j j + c * M j k) + c * (-s * M k j + c * M k k) := by
  simp [transpose_planeRotation_mul_apply hjk, mul_planeRotation_apply hjk, Ne.symm hjk]
  ring

/-- Let $n$ be finite, $j \neq k$ and $M \in \mathbb{R}^{n \times n}$, and write $R = R_{jk}(c, s)$.
The $(j, k)$ entry of the conjugate is
$$(R^T M R)_{jk} = c (-s M_{jj} + c M_{jk}) + s (-s M_{kj} + c M_{kk}).$$

This is the entry that Jacobi's method chooses the angle to annihilate. -/
theorem conj_planeRotation_apply_jk (hjk : j ≠ k) (M : Matrix n n ℝ) :
    ((planeRotation j k c s)ᵀ * M * planeRotation j k c s) j k
      = c * (-s * M j j + c * M j k) + s * (-s * M k j + c * M k k) := by
  simp [transpose_planeRotation_mul_apply hjk, mul_planeRotation_apply hjk, Ne.symm hjk]
  ring

/-- Let $n$ be finite, $j \neq k$ and $M \in \mathbb{R}^{n \times n}$, and write $R = R_{jk}(c, s)$.
For a row $p \notin \{j, k\}$, the entry of the conjugate in the column $j$ is
$$(R^T M R)_{pj} = c M_{pj} + s M_{pk}.$$
-/
theorem conj_planeRotation_apply_col_j (hjk : j ≠ k) (M : Matrix n n ℝ) {p : n}
    (hpj : p ≠ j) (hpk : p ≠ k) :
    ((planeRotation j k c s)ᵀ * M * planeRotation j k c s) p j = c * M p j + s * M p k := by
  simp [transpose_planeRotation_mul_apply hjk, mul_planeRotation_apply hjk, hpj, hpk]

/-- Let $n$ be finite, $j \neq k$ and $M \in \mathbb{R}^{n \times n}$, and write $R = R_{jk}(c, s)$.
For a row $p \notin \{j, k\}$, the entry of the conjugate in the column $k$ is
$$(R^T M R)_{pk} = -s M_{pj} + c M_{pk}.$$
-/
theorem conj_planeRotation_apply_col_k (hjk : j ≠ k) (M : Matrix n n ℝ) {p : n}
    (hpj : p ≠ j) (hpk : p ≠ k) :
    ((planeRotation j k c s)ᵀ * M * planeRotation j k c s) p k = -s * M p j + c * M p k := by
  simp [transpose_planeRotation_mul_apply hjk, mul_planeRotation_apply hjk, hpj, hpk,
    Ne.symm hjk]

/-- Let $n$ be finite, $j \neq k$ and $M \in \mathbb{R}^{n \times n}$, and write $R = R_{jk}(c, s)$.
For a column $q \notin \{j, k\}$, the entry of the conjugate in the row $j$ is
$$(R^T M R)_{jq} = c M_{jq} + s M_{kq}.$$
-/
theorem conj_planeRotation_apply_row_j (hjk : j ≠ k) (M : Matrix n n ℝ) {q : n}
    (hqj : q ≠ j) (hqk : q ≠ k) :
    ((planeRotation j k c s)ᵀ * M * planeRotation j k c s) j q = c * M j q + s * M k q := by
  simp [transpose_planeRotation_mul_apply hjk, mul_planeRotation_apply hjk, hqj, hqk]

/-- Let $n$ be finite, $j \neq k$ and $M \in \mathbb{R}^{n \times n}$, and write $R = R_{jk}(c, s)$.
For a column $q \notin \{j, k\}$, the entry of the conjugate in the row $k$ is
$$(R^T M R)_{kq} = -s M_{jq} + c M_{kq}.$$
-/
theorem conj_planeRotation_apply_row_k (hjk : j ≠ k) (M : Matrix n n ℝ) {q : n}
    (hqj : q ≠ j) (hqk : q ≠ k) :
    ((planeRotation j k c s)ᵀ * M * planeRotation j k c s) k q = -s * M j q + c * M k q := by
  simp [transpose_planeRotation_mul_apply hjk, mul_planeRotation_apply hjk, hqj, hqk,
    Ne.symm hjk]

/-! ### The Givens pair -/

/-- A **point of the unit circle is $(\cos \theta, \sin \theta)$**: if $c, s \in \mathbb{R}$ satisfy
$c^2 + s^2 = 1$, then there is $\theta \in \mathbb{R}$ with
$$\cos \theta = c \quad \text{and} \quad \sin \theta = s.$$

Hence every plane rotation $R_{jk}(c, s)$ with $c^2 + s^2 = 1$, in particular every rotation
built from a Givens pair (`Matrix.givensPair_sq_add_sq`), is the rotation by an angle $\theta$.
The proof takes $\theta = \arccos c$ if $s \ge 0$ and $\theta = -\arccos c$ if $s < 0$. -/
theorem _root_.Real.exists_cos_eq_sin_eq {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) :
    ∃ θ : ℝ, Real.cos θ = c ∧ Real.sin θ = s := by
  have hc1 : -1 ≤ c := by nlinarith
  have hc1' : c ≤ 1 := by nlinarith
  have hsq : √(1 - c ^ 2) = |s| := by
    rw [show 1 - c ^ 2 = s ^ 2 by linarith, Real.sqrt_sq_eq_abs]
  rcases le_or_gt 0 s with hs | hs
  · exact ⟨Real.arccos c, Real.cos_arccos hc1 hc1',
      by rw [Real.sin_arccos, hsq, abs_of_nonneg hs]⟩
  · exact ⟨-Real.arccos c, by rw [Real.cos_neg, Real.cos_arccos hc1 hc1'],
      by rw [Real.sin_neg, Real.sin_arccos, hsq, abs_of_neg hs, neg_neg]⟩

/-- The **Givens pair** of $a, b \in \mathbb{R}$ is
$$(c, s) = \left(\frac{a}{\sqrt{a^2 + b^2}}, \frac{b}{\sqrt{a^2 + b^2}}\right)$$
if $(a, b) \neq (0, 0)$, and $(c, s) = (1, 0)$ if $a = b = 0$. It is the cosine and sine of the
rotation whose transpose sends $(a, b)$ to $(\sqrt{a^2 + b^2}, 0)$.

This is (5.44) and (5.51) of [quarteroni2000numerical], $c = x_i / \alpha$ and
$s = -x_k / \alpha$, read in the sign convention of `Matrix.planeRotation`: the $s$ of the
source is $-s$ here. It is also Program 33 of the source, up to the choice of branch. -/
noncomputable def givensPair (a b : ℝ) : ℝ × ℝ :=
  if a = 0 ∧ b = 0 then (1, 0) else (a / √(a ^ 2 + b ^ 2), b / √(a ^ 2 + b ^ 2))

/-- If $(a, b) \neq (0, 0)$, the Givens pair of $(a, b)$ is $\left(a / \sqrt{a^2 + b^2}, \, b /
\sqrt{a^2 + b^2}\right)$. -/
theorem givensPair_of_not (a b : ℝ) (h : ¬(a = 0 ∧ b = 0)) :
    givensPair a b = (a / √(a ^ 2 + b ^ 2), b / √(a ^ 2 + b ^ 2)) := by
  rw [givensPair, ite_eq_right h]

/-- The Givens pair of $(0, 0)$ is $(1, 0)$. -/
@[simp]
theorem givensPair_zero_zero : givensPair 0 0 = (1, 0) := by simp [givensPair]

/-- If $(a, b) \neq (0, 0)$, then $a^2 + b^2 > 0$. -/
private theorem sq_add_sq_pos_of_not {a b : ℝ} (h : ¬(a = 0 ∧ b = 0)) : 0 < a ^ 2 + b ^ 2 := by
  rcases not_and_or.1 h with ha | hb
  · positivity
  · positivity

/-- The Givens pair $(c, s)$ of any $a, b \in \mathbb{R}$ lies on the unit circle: $c^2 + s^2 = 1$.
-/
theorem givensPair_sq_add_sq (a b : ℝ) :
    (givensPair a b).1 ^ 2 + (givensPair a b).2 ^ 2 = 1 := by
  by_cases h : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [givensPair_of_not a b h]
    have hpos := sq_add_sq_pos_of_not h
    simp only [div_pow, Real.sq_sqrt hpos.le]
    rw [← add_div, div_self hpos.ne']

/-- The Givens pair $(c, s)$ of any $a, b \in \mathbb{R}$ rotates $(a, b)$ onto the first axis:
$$c a + s b = \sqrt{a^2 + b^2} \quad \text{and} \quad -s a + c b = 0.$$

This is (5.51) of [quarteroni2000numerical], in the sign convention of `Matrix.planeRotation`.
For $a = b = 0$ both sides vanish. -/
theorem givensPair_fst_mul_add_snd_mul (a b : ℝ) :
    (givensPair a b).1 * a + (givensPair a b).2 * b = √(a ^ 2 + b ^ 2) ∧
      -(givensPair a b).2 * a + (givensPair a b).1 * b = 0 := by
  by_cases h : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [givensPair_of_not a b h]
    have hpos := sq_add_sq_pos_of_not h
    have hs : √(a ^ 2 + b ^ 2) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
    refine ⟨?_, by ring⟩
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, ← sq, ← sq,
      div_eq_iff hs, Real.mul_self_sqrt hpos.le]

/-- Let $n$ be finite, let $j \neq k$, and let $x \in \mathbb{R}^n$. Let $(c, s)$ be the Givens pair
of $(x_j, x_k)$ and $R = R_{jk}(c, s)$. Then
$$(R^T x)_k = 0, \qquad (R^T x)_j = \sqrt{x_j^2 + x_k^2}, \qquad (R^T x)_q = x_q \quad \text{for
  } q \notin \{j, k\}.$$

This is (5.44) of [quarteroni2000numerical]. -/
theorem transpose_planeRotation_givensPair_mulVec (hjk : j ≠ k) (x : n → ℝ) :
    ((planeRotation j k (givensPair (x j) (x k)).1 (givensPair (x j) (x k)).2)ᵀ *ᵥ x) k = 0 ∧
      ((planeRotation j k (givensPair (x j) (x k)).1 (givensPair (x j) (x k)).2)ᵀ *ᵥ x) j =
        √(x j ^ 2 + x k ^ 2) ∧
      ∀ q, q ≠ j → q ≠ k →
        ((planeRotation j k (givensPair (x j) (x k)).1 (givensPair (x j) (x k)).2)ᵀ *ᵥ x) q =
          x q := by
  obtain ⟨h1, h2⟩ := givensPair_fst_mul_add_snd_mul (x j) (x k)
  refine ⟨?_, ?_, fun q hqj hqk => ?_⟩
  · rw [transpose_planeRotation_mulVec_apply hjk, ite_eq_right hjk.symm, ite_eq_left rfl, h2]
  · rw [transpose_planeRotation_mulVec_apply hjk, ite_eq_left rfl, h1]
  · rw [transpose_planeRotation_mulVec_apply hjk, ite_eq_right hqj, ite_eq_right hqk]

/-! ### Plane reflections -/

section Reflector

/-- The **plane reflector** with angle $\varphi \in \mathbb{R}$ is the $2 \times 2$ real matrix
$$R(\varphi) = \begin{bmatrix} -\cos \varphi & \sin \varphi \\ \sin \varphi & \cos \varphi
  \end{bmatrix}$$
of [golub2013matrix], §12.2.10. These matrices are the factors of the product form (12.2.18) of
an orthogonal upper Hessenberg matrix in the source. -/
noncomputable def planeReflector (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-Real.cos φ, Real.sin φ; Real.sin φ, Real.cos φ]

/-- A plane reflector is an involution: $R(\varphi) R(\varphi) = I_2$. -/
theorem planeReflector_mul_self (φ : ℝ) : planeReflector φ * planeReflector φ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeReflector, Matrix.mul_apply, Fin.sum_univ_two, ← sq, Real.sin_sq_add_cos_sq,
      Real.cos_sq_add_sin_sq] <;> ring

/-- A plane reflector is symmetric: $R(\varphi)^T = R(\varphi)$. -/
theorem planeReflector_transpose (φ : ℝ) : (planeReflector φ)ᵀ = planeReflector φ := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- A plane reflector has determinant $-1$. -/
theorem det_planeReflector (φ : ℝ) : (planeReflector φ).det = -1 := by
  rw [planeReflector, det_fin_two_of]
  linear_combination -Real.sin_sq_add_cos_sq φ

end Reflector

/-! ### $J$-orthogonal matrices and hyperbolic rotations -/

section JOrthogonal

variable [CommRing R]

/-- Let $R$ be a commutative ring and $J, H \in R^{n \times n}$. The matrix $H$ is
**$J$-orthogonal** if
$$H J H^T = J.$$

This is the $S$-orthogonality of (6.5.11) in [golub2013matrix]; the name $J$-orthogonal follows
Higham, "J-orthogonal matrices", SIAM Review 2003. For $J = I$ it is membership in the
orthogonal group (`Matrix.isJOrthogonal_one_iff_mem_orthogonalGroup`). For Mathlib's symplectic
form `Matrix.J` it is membership in the symplectic group
(`Matrix.isJOrthogonal_iff_mem_symplecticGroup`). -/
def IsJOrthogonal (J H : Matrix n n R) : Prop := H * J * Hᵀ = J

/-- The identity matrix is $J$-orthogonal for every $J$. -/
theorem isJOrthogonal_one (J : Matrix n n R) : IsJOrthogonal J 1 := by
  simp [IsJOrthogonal]

omit [DecidableEq n] in
/-- **Products of $J$-orthogonal matrices are $J$-orthogonal**: let $R$ be a commutative ring and
let $n$ be finite. If $H_1 J H_1^T = J$ and $H_2 J H_2^T = J$, then
$$(H_1 H_2) J (H_1 H_2)^T = J.$$

This fact is stated in §6.5.4 of [golub2013matrix]. -/
theorem IsJOrthogonal.mul {J H₁ H₂ : Matrix n n R} (h₁ : IsJOrthogonal J H₁)
    (h₂ : IsJOrthogonal J H₂) : IsJOrthogonal J (H₁ * H₂) := by
  unfold IsJOrthogonal at *
  calc H₁ * H₂ * J * (H₁ * H₂)ᵀ = H₁ * (H₂ * J * H₂ᵀ) * H₁ᵀ := by
        rw [transpose_mul]
        simp only [Matrix.mul_assoc]
    _ = J := by rw [h₂, h₁]

/-- The $J$-orthogonal matrices form a submonoid of $R^{n \times n}$. When $J$ is invertible, every
$J$-orthogonal matrix is invertible and its inverse is $J$-orthogonal, so they form a group;
only the submonoid is defined here. -/
def jOrthogonalSubmonoid (J : Matrix n n R) : Submonoid (Matrix n n R) where
  carrier := {H | IsJOrthogonal J H}
  mul_mem' := IsJOrthogonal.mul
  one_mem' := isJOrthogonal_one J

/-- A matrix $H$ belongs to `Matrix.jOrthogonalSubmonoid J` if and only if $H$ is $J$-orthogonal. -/
@[simp]
theorem mem_jOrthogonalSubmonoid {J H : Matrix n n R} :
    H ∈ jOrthogonalSubmonoid J ↔ IsJOrthogonal J H :=
  Iff.rfl

/-- The product of a list of $J$-orthogonal matrices is $J$-orthogonal. -/
theorem isJOrthogonal_list_prod {J : Matrix n n R} (l : List (Matrix n n R))
    (h : ∀ H ∈ l, IsJOrthogonal J H) : IsJOrthogonal J l.prod :=
  Submonoid.list_prod_mem (jOrthogonalSubmonoid J) h

/-- If $J J = I$ and $H J H^T = J$, then $H^T J H = J$, because $J H^T J$ is a right inverse of $H$
and hence a left inverse. -/
private theorem transpose_mul_mul_eq_of_isJOrthogonal {J H : Matrix n n R} (hJ : J * J = 1)
    (h : IsJOrthogonal J H) : Hᵀ * J * H = J := by
  have h1 : H * (J * Hᵀ * J) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
    rw [IsJOrthogonal] at h
    rw [h, hJ]
  have h2 : J * Hᵀ * J * H = 1 := mul_eq_one_comm.1 h1
  calc Hᵀ * J * H = J * J * (Hᵀ * J * H) := by rw [hJ, Matrix.one_mul]
    _ = J * (J * Hᵀ * J * H) := by simp only [Matrix.mul_assoc]
    _ = J := by rw [h2, Matrix.mul_one]

/-- Let $R$ be a commutative ring, let $n$ be finite, and let $J \in R^{n \times n}$ satisfy
$J J = I$. If $H$ is $J$-orthogonal, then $H^T$ is $J$-orthogonal, that is
$$H^T J H = J.$$

This is the form of the condition in Problem P6.5.5 of [golub2013matrix]. -/
theorem IsJOrthogonal.transpose {J H : Matrix n n R} (hJ : J * J = 1) (h : IsJOrthogonal J H) :
    IsJOrthogonal J Hᵀ := by
  change Hᵀ * J * Hᵀᵀ = J
  rw [transpose_transpose]
  exact transpose_mul_mul_eq_of_isJOrthogonal hJ h

/-- If $J J = I$, then $H^T$ is $J$-orthogonal if and only if $H$ is $J$-orthogonal. -/
theorem isJOrthogonal_transpose_iff {J H : Matrix n n R} (hJ : J * J = 1) :
    IsJOrthogonal J Hᵀ ↔ IsJOrthogonal J H :=
  ⟨fun h => by simpa using h.transpose hJ, fun h => h.transpose hJ⟩

/-- A matrix $H$ is $I$-orthogonal, that is $H H^T = I$, if and only if $H$ belongs to the
orthogonal group. -/
theorem isJOrthogonal_one_iff_mem_orthogonalGroup {H : Matrix n n R} :
    IsJOrthogonal 1 H ↔ H ∈ Matrix.orthogonalGroup n R := by
  rw [IsJOrthogonal, Matrix.mul_one, mem_orthogonalGroup_iff]

/-- **The bridge to Mathlib's symplectic group**: let $R$ be a commutative ring, let $l$ be a finite
index type, and let $A \in R^{(l \oplus l) \times (l \oplus l)}$. For Mathlib's symplectic form
$J$ (`Matrix.J l R`), the matrix $A$ is $J$-orthogonal if and only if $A$ belongs to the
symplectic group `Matrix.symplecticGroup l R`.

The carrier of `Matrix.symplecticGroup l R` is defined by $A J A^T = J$, so the two conditions
agree by definition. -/
theorem isJOrthogonal_iff_mem_symplecticGroup {l : Type*} [DecidableEq l] [Fintype l]
    {A : Matrix (l ⊕ l) (l ⊕ l) R} :
    IsJOrthogonal (Matrix.J l R) A ↔ A ∈ Matrix.symplecticGroup l R :=
  SymplecticGroup.mem_iff.symm

end JOrthogonal

section Hyperbolic

/-- The **hyperbolic rotation** of the $(j, k)$-plane with parameters $c, s \in \mathbb{R}$ is
$$H_{jk}(c, s) = E_{jk}\left(\begin{bmatrix} c & -s \\ -s & c \end{bmatrix}\right) \in
  \mathbb{R}^{n \times n}.$$

This is the matrix $H_k(\theta)$ of [golub2013matrix], §6.5.4, with $c = \cosh \theta$ and
$s = \sinh \theta$. For $c^2 - s^2 = 1$ it is $J$-orthogonal for every diagonal signature that
is $+1$ at $j$ and $-1$ at $k$ (`Matrix.isJOrthogonal_hyperbolicRotation`). -/
def hyperbolicRotation (j k : n) (c s : ℝ) : Matrix n n ℝ := planeEmbed j k !![c, -s; -s, c]

omit [Fintype n] in
/-- For $j \neq k$, a hyperbolic rotation is symmetric: $H_{jk}(c, s)^T = H_{jk}(c, s)$. -/
theorem hyperbolicRotation_transpose {j k : n} (hjk : j ≠ k) (c s : ℝ) :
    (hyperbolicRotation j k c s)ᵀ = hyperbolicRotation j k c s := by
  rw [hyperbolicRotation, planeEmbed_transpose _ hjk]
  congr 1
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

/-- **Hyperbolic rotations are $J$-orthogonal**: let $n$ be finite, let $j \neq k$, and let
$\varepsilon \colon n \to \mathbb{R}$ satisfy $\varepsilon_j = 1$ and $\varepsilon_k = -1$. If
$c^2 - s^2 = 1$, then $H = H_{jk}(c, s)$ satisfies
$$H \operatorname{diag}(\varepsilon) H^T = \operatorname{diag}(\varepsilon).$$

This is the statement of §6.5.4 of [golub2013matrix] that "the $S$-orthogonality of this matrix
follows from $\cosh(\theta)^2 - \sinh(\theta)^2 = 1$". The entries $\varepsilon_p$ for
$p \notin \{j, k\}$ are arbitrary. -/
theorem isJOrthogonal_hyperbolicRotation {j k : n} (hjk : j ≠ k) {ε : n → ℝ} (hj : ε j = 1)
    (hk : ε k = -1) {c s : ℝ} (hcs : c ^ 2 - s ^ 2 = 1) :
    IsJOrthogonal (diagonal ε) (hyperbolicRotation j k c s) := by
  rw [IsJOrthogonal, hyperbolicRotation_transpose hjk, Matrix.mul_assoc]
  ext p q
  rw [hyperbolicRotation, planeEmbed_mul_apply _ hjk]
  simp only [diagonal_mul, planeEmbed_apply, diagonal_apply, of_apply, cons_val', cons_val_zero,
    cons_val_one, empty_val', cons_val_fin_one, Fin.isValue]
  by_cases hpj : p = j
  · subst hpj
    by_cases hqp : q = p
    · subst hqp
      simp [hjk.symm, hj, hk]
      linear_combination hcs
    by_cases hqk : q = k
    · subst hqk
      simp [hqp, hjk, hj, hk]
      ring
    · simp [hqp, hqk, Ne.symm hqp]
  by_cases hpk : p = k
  · subst hpk
    by_cases hqj : q = j
    · subst hqj
      simp [hjk.symm, hj, hk]
      ring
    by_cases hqp : q = p
    · subst hqp
      simp [hj, hk, hqj]
      nlinarith [hcs]
    · simp [hqp, hqj, Ne.symm hqp]
  · by_cases hqj : q = j
    · subst hqj
      simp [hpj, hpk]
    by_cases hqk : q = k
    · subst hqk
      simp [hpj, hpk]
    · by_cases hpq : p = q
      · subst hpq
        simp [hpj, hpk]
      · simp [hpj, hpk, hpq]

end Hyperbolic

/-- The **hyperbolic pair** of $a, b \in \mathbb{R}$ is
$$(c, s) = \left(\frac{1}{\sqrt{1 - \tau^2}}, \frac{\tau}{\sqrt{1 - \tau^2}}\right), \qquad
  \tau = \frac{b}{a},$$
as in (6.5.13) of [golub2013matrix]. It is the hyperbolic counterpart of `Matrix.givensPair`.

The pair is meaningful when $|b| < |a|$. Outside this case the Lean conventions $b / 0 = 0$,
$\sqrt{t} = 0$ for $t \le 0$ and $1 / 0 = 0$ give the value $(1, 0)$ for $a = 0$, and $(0, 0)$
for $a \neq 0$ with $|b| \ge |a|$. -/
noncomputable def hyperbolicPair (a b : ℝ) : ℝ × ℝ :=
  (1 / √(1 - (b / a) ^ 2), 1 / √(1 - (b / a) ^ 2) * (b / a))

/-- If $|b| < |a|$, then $1 - (b / a)^2 > 0$. -/
private theorem one_sub_div_sq_pos {a b : ℝ} (h : |b| < |a|) : 0 < 1 - (b / a) ^ 2 := by
  have ha : a ≠ 0 := fun ha => by
    rw [ha, abs_zero] at h
    exact absurd h (not_lt.2 (abs_nonneg b))
  have hab : b ^ 2 < a ^ 2 := sq_lt_sq.2 h
  rw [div_pow, sub_pos, div_lt_one (by positivity)]
  exact hab

/-- **The hyperbolic pair is hyperbolic**: if $a, b \in \mathbb{R}$ satisfy $|b| < |a|$ and $(c, s)$
is the hyperbolic pair of $(a, b)$, then
$$c^2 - s^2 = 1 \quad \text{and} \quad c > 0.$$

This is the property of (6.5.13) in [golub2013matrix]. -/
theorem hyperbolicPair_sq_sub_sq {a b : ℝ} (h : |b| < |a|) :
    (hyperbolicPair a b).1 ^ 2 - (hyperbolicPair a b).2 ^ 2 = 1 ∧ 0 < (hyperbolicPair a b).1 := by
  have hpos := one_sub_div_sq_pos h
  have hsq : √(1 - (b / a) ^ 2) ^ 2 = 1 - (b / a) ^ 2 := Real.sq_sqrt hpos.le
  refine ⟨?_, by simp only [hyperbolicPair]; positivity⟩
  simp only [hyperbolicPair]
  generalize b / a = τ at hpos hsq ⊢
  rw [mul_pow, div_pow, one_pow, hsq]
  field_simp [hpos.ne']

/-- **Hyperbolic rotations introduce zeros**: let $n$ be finite, let $j \neq k$, and let
$x \in \mathbb{R}^n$ satisfy $|x_k| < |x_j|$. Let $(c, s)$ be the hyperbolic pair of
$(x_j, x_k)$ and $H = H_{jk}(c, s)$. Then
$$(H x)_k = 0 \quad \text{and} \quad (H x)_j = \operatorname{sign}(x_j) \sqrt{x_j^2 - x_k^2}.$$

This is §6.5.4 and (6.5.13) of [golub2013matrix]. The other entries of $x$ are unchanged, by
`Matrix.planeEmbed_mulVec_apply_of_ne`. -/
theorem hyperbolicRotation_hyperbolicPair_mulVec {j k : n} (hjk : j ≠ k)
    {x : n → ℝ} (h : |x k| < |x j|) :
    (hyperbolicRotation j k (hyperbolicPair (x j) (x k)).1 (hyperbolicPair (x j) (x k)).2 *ᵥ x) k
        = 0 ∧
      (hyperbolicRotation j k (hyperbolicPair (x j) (x k)).1 (hyperbolicPair (x j) (x k)).2 *ᵥ x) j
        = SignType.sign (x j) * √(x j ^ 2 - x k ^ 2) := by
  have ha : x j ≠ 0 := fun ha => by
    rw [ha, abs_zero] at h
    exact absurd h (not_lt.2 (abs_nonneg _))
  have hD : 0 < x j ^ 2 - x k ^ 2 := sub_pos.2 (sq_lt_sq.2 h)
  have hsqrt : √(1 - (x k / x j) ^ 2) = √(x j ^ 2 - x k ^ 2) / |x j| := by
    rw [show 1 - (x k / x j) ^ 2 = (x j ^ 2 - x k ^ 2) / |x j| ^ 2 by
      rw [sq_abs]; field_simp, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq (abs_nonneg _)]
  have hrr : √(x j ^ 2 - x k ^ 2) ^ 2 = x j ^ 2 - x k ^ 2 := Real.sq_sqrt hD.le
  rw [hyperbolicRotation, planeEmbed_mulVec_apply _ hjk, planeEmbed_mulVec_apply _ hjk]
  simp only [hjk.symm, ite_true, ite_false, hyperbolicPair, hsqrt, of_apply, cons_val',
    cons_val_zero, cons_val_one, empty_val', cons_val_fin_one, Fin.isValue]
  refine ⟨?_, ?_⟩
  · field_simp
    ring
  · rcases lt_or_gt_of_ne ha with hneg | hpos
    · rw [abs_of_neg hneg, sign_neg hneg, SignType.coe_neg_one]
      field_simp
      linear_combination hrr
    · rw [abs_of_pos hpos, sign_pos hpos, SignType.coe_one]
      field_simp
      linear_combination -hrr

/-- **The hyperbolic pair may not exist**: let $x_1, x_2 \in \mathbb{R}$ with $|x_1| \le |x_2|$ and
$x_2 \neq 0$. Then there are no $c, s \in \mathbb{R}$ with
$$c^2 - s^2 = 1 \quad \text{and} \quad -s x_1 + c x_2 = 0.$$

Section 6.5.4 of [golub2013matrix] states that "there is no real solution to
$-s x_1 + c x_2 = 0$ if $|x_2| > |x_1|$". The statement here also covers the case
$|x_1| = |x_2|$. -/
theorem not_exists_hyperbolic_of_abs_le {x₁ x₂ : ℝ} (h : |x₁| ≤ |x₂|) (hx₂ : x₂ ≠ 0) :
    ¬ ∃ c s : ℝ, c ^ 2 - s ^ 2 = 1 ∧ -s * x₁ + c * x₂ = 0 := by
  rintro ⟨c, s, hcs, hz⟩
  have h12 : x₁ ^ 2 ≤ x₂ ^ 2 := sq_le_sq.2 h
  have hx : 0 < x₂ ^ 2 := by positivity
  have hsq : c ^ 2 * x₂ ^ 2 = s ^ 2 * x₁ ^ 2 := by
    have : c * x₂ = s * x₁ := by linarith
    rw [← mul_pow, ← mul_pow, this]
  nlinarith [mul_le_mul_of_nonneg_left h12 (sq_nonneg s)]

/-! ### Embeddings in adjacent planes -/

section AdjacentEmbed

variable {α : Type*} {M : ℕ}

/-- The **embedding in an adjacent plane**: for $M, j \in \mathbb{N}$ and
$G \in \alpha^{2 \times 2}$, the matrix $A_j(G) \in \alpha^{M \times M}$, with rows and columns
indexed by $\{0, \dots, M - 1\}$, is the plane embedding $E_{j, j+1}(G)$ (`Matrix.planeEmbed`)
if $j + 1 < M$, and the identity if $j + 1 \ge M$.

Indexing the planes by $j \in \mathbb{N}$ makes a sweep over the planes $(j, j + 1)$ a product
over a list of natural numbers, with no bounds to carry. -/
def adjacentEmbed [Zero α] [One α] (j : ℕ) (G : Matrix (Fin 2) (Fin 2) α) :
    Matrix (Fin M) (Fin M) α :=
  if h : j + 1 < M then planeEmbed ⟨j, by omega⟩ ⟨j + 1, h⟩ G else 1

section Basic

variable [Zero α] [One α] {j : ℕ} (G : Matrix (Fin 2) (Fin 2) α)

/-- If $j + 1 < M$, the adjacent embedding $A_j(G)$ is the plane embedding $E_{j, j+1}(G)$. -/
theorem adjacentEmbed_of_lt (h : j + 1 < M) :
    (adjacentEmbed j G : Matrix (Fin M) (Fin M) α) = planeEmbed ⟨j, by omega⟩ ⟨j + 1, h⟩ G :=
  dite_eq_left h

/-- If $M \le j + 1$, the adjacent embedding $A_j(G)$ is the identity. -/
theorem adjacentEmbed_of_le (h : M ≤ j + 1) : (adjacentEmbed j G : Matrix (Fin M) (Fin M) α) = 1 :=
  dite_eq_right (by omega)

/-- Transposition commutes with the adjacent embedding: $A_j(G)^T = A_j(G^T)$. -/
theorem adjacentEmbed_transpose :
    (adjacentEmbed j G : Matrix (Fin M) (Fin M) α)ᵀ = adjacentEmbed j Gᵀ := by
  unfold adjacentEmbed
  split_ifs
  · exact planeEmbed_transpose G (Fin.ne_of_val_ne (by simp))
  · exact transpose_one

end Basic

section Mul

variable [NonAssocSemiring α] (j : ℕ) (G : Matrix (Fin 2) (Fin 2) α)

/-- Over a semiring, if $i \neq j$ and $i \neq j + 1$, then $(A_j(G) x)_i = x_i$ for every
$x \in \alpha^M$. -/
theorem adjacentEmbed_mulVec_apply_of_ne (x : Fin M → α) {i : Fin M} (h₀ : (i : ℕ) ≠ j)
    (h₁ : (i : ℕ) ≠ j + 1) : (adjacentEmbed j G *ᵥ x) i = x i := by
  unfold adjacentEmbed
  split_ifs with h
  · exact planeEmbed_mulVec_apply_of_ne G (Fin.ne_of_val_ne (by simp)) x (Fin.ne_of_val_ne h₀)
      (Fin.ne_of_val_ne h₁)
  · rw [one_mulVec]

/-- Over a semiring, if $j + 1 < M$, then $(A_j(G) x)_j = g_{00} x_j + g_{01} x_{j+1}$ for every
$x \in \alpha^M$. -/
theorem adjacentEmbed_mulVec_apply_self (h : j + 1 < M) (x : Fin M → α) :
    (adjacentEmbed j G *ᵥ x) ⟨j, by omega⟩ =
      G 0 0 * x ⟨j, by omega⟩ + G 0 1 * x ⟨j + 1, h⟩ := by
  rw [adjacentEmbed_of_lt G h, planeEmbed_mulVec_apply G (Fin.ne_of_val_ne (by simp)),
    ite_eq_left rfl]

/-- Over a semiring, if $j + 1 < M$, then $(A_j(G) x)_{j+1} = g_{10} x_j + g_{11} x_{j+1}$ for every
$x \in \alpha^M$. -/
theorem adjacentEmbed_mulVec_apply_succ (h : j + 1 < M) (x : Fin M → α) :
    (adjacentEmbed j G *ᵥ x) ⟨j + 1, h⟩ =
      G 1 0 * x ⟨j, by omega⟩ + G 1 1 * x ⟨j + 1, h⟩ := by
  rw [adjacentEmbed_of_lt G h, planeEmbed_mulVec_apply G (Fin.ne_of_val_ne (by simp)),
    ite_eq_right (Fin.ne_of_val_ne (by simp)), ite_eq_left rfl]

/-- Over a semiring, if $x \in \alpha^M$ vanishes at every index $r \in \{j, j + 1\}$, then
$A_j(G) x$ also vanishes at every index $i \in \{j, j + 1\}$. -/
theorem adjacentEmbed_mulVec_apply_eq_zero {x : Fin M → α}
    (hx : ∀ r : Fin M, (r : ℕ) = j ∨ (r : ℕ) = j + 1 → x r = 0) {i : Fin M}
    (hi : (i : ℕ) = j ∨ (i : ℕ) = j + 1) : (adjacentEmbed j G *ᵥ x) i = 0 := by
  unfold adjacentEmbed
  split_ifs with h
  · rw [planeEmbed_mulVec_apply G (Fin.ne_of_val_ne (by simp)), hx ⟨j, by omega⟩ (Or.inl rfl),
      hx ⟨j + 1, h⟩ (Or.inr rfl), hx i hi]
    simp
  · rw [one_mulVec, hx i hi]

variable {N : ℕ} (X : Matrix (Fin M) (Fin N) α)

/-- Over a semiring, for $X \in \alpha^{M \times N}$, if $i \neq j$ and $i \neq j + 1$, then
$(A_j(G) X)_{il} = X_{il}$ for every column $l$. -/
theorem adjacentEmbed_mul_apply_of_ne {i : Fin M} (h₀ : (i : ℕ) ≠ j) (h₁ : (i : ℕ) ≠ j + 1)
    (l : Fin N) : ((adjacentEmbed j G : Matrix (Fin M) (Fin M) α) * X) i l = X i l :=
  adjacentEmbed_mulVec_apply_of_ne j G (fun r => X r l) h₀ h₁

/-- Over a semiring, for $X \in \alpha^{M \times N}$ and $j + 1 < M$, the entry in the row $j + 1$
and the column $l$ of $A_j(G) X$ is $g_{10} X_{jl} + g_{11} X_{j+1, l}$. -/
theorem adjacentEmbed_mul_apply_succ (h : j + 1 < M) (l : Fin N) :
    ((adjacentEmbed j G : Matrix (Fin M) (Fin M) α) * X) ⟨j + 1, h⟩ l =
      G 1 0 * X ⟨j, by omega⟩ l + G 1 1 * X ⟨j + 1, h⟩ l :=
  adjacentEmbed_mulVec_apply_succ j G h (fun r => X r l)

/-- Over a semiring, for $X \in \alpha^{M \times N}$ and a column $l$, if $X_{rl} = 0$ for every row
$r \in \{j, j + 1\}$, then $(A_j(G) X)_{il} = 0$ for every row $i \in \{j, j + 1\}$. -/
theorem adjacentEmbed_mul_apply_eq_zero {l : Fin N}
    (hX : ∀ r : Fin M, (r : ℕ) = j ∨ (r : ℕ) = j + 1 → X r l = 0) {i : Fin M}
    (hi : (i : ℕ) = j ∨ (i : ℕ) = j + 1) :
    ((adjacentEmbed j G : Matrix (Fin M) (Fin M) α) * X) i l = 0 :=
  adjacentEmbed_mulVec_apply_eq_zero j G hX hi

end Mul

/-- Over a commutative ring with a star operation, if $G \in \alpha^{2 \times 2}$ is unitary, then
the adjacent embedding $A_j(G) \in \alpha^{M \times M}$ is unitary, for every
$j, M \in \mathbb{N}$. -/
theorem adjacentEmbed_mem_unitaryGroup [CommRing α] [StarRing α] (j : ℕ)
    {G : Matrix (Fin 2) (Fin 2) α} (hG : G ∈ unitaryGroup (Fin 2) α) :
    (adjacentEmbed j G : Matrix (Fin M) (Fin M) α) ∈ unitaryGroup (Fin M) α := by
  unfold adjacentEmbed
  split_ifs
  · exact (planeEmbed_mem_unitaryGroup_iff G (Fin.ne_of_val_ne (by simp))).2 hG
  · exact one_mem _

end AdjacentEmbed

end Matrix

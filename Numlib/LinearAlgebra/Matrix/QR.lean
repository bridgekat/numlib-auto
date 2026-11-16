/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.QR`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Data.Fintype.Sort
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.UnitaryGroup
import Numlib.Analysis.InnerProductSpace.GramSchmidt
import Numlib.Analysis.Normed.Lp.PiLp
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.LinearAlgebra.Matrix.PlaneRotation
import Numlib.LinearAlgebra.Matrix.Products

/-!
# Householder reflectors and the QR factorization

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$. For $w \in \mathbb{K}^n$ the **Householder
reflector** is $P(w) = I - 2 w w^H$. When $w$ is a unit vector, $P(w)$ is the reflection in the
hyperplane orthogonal to $w$; it is Hermitian, involutive and therefore unitary. One reflector
annihilates every entry of a vector but one: for $x \neq 0$ and the unit vector $w$ along
$x + \operatorname{sign}(x_i) \|x\|_2 e_i$, $P(w) x = -\operatorname{sign}(x_i) \|x\|_2 e_i$. An
induction over the columns then reduces any matrix to upper triangular form by a product of
reflectors. The QR factorization is also reached by orthonormalizing the columns: a matrix $A$ with
linearly independent columns factors as $A = QR$ with $Q^H Q = I$ and $R$ upper triangular with a
positive diagonal, where $Q$ is the Gram–Schmidt orthonormalization of the columns and
$r_{ij} = \langle q_i, a_j \rangle$. This factorization is unique, so a product of reflectors,
classical Gram–Schmidt and modified Gram–Schmidt all compute the same $Q$ and the same $R$. The
presentation follows [saad2003iterative], §1.7: the reflector (1.20), its defining conditions
(1.21)–(1.26), the factorization (1.19), the triangularization (1.27)–(1.28) and Algorithm 1.3. It
also follows [kress1998numerical], §5. Below, $x^H$ is the conjugate transpose,
$\langle u, v \rangle = u^H v$, $\|x\|_2$ is the Euclidean norm, $e_i$ is the $i$-th coordinate
vector, and indices start at $0$.

The second half of the file gives the Householder and Givens tools of the eigenvalue algorithms of
[quarteroni2000numerical], §5.6.1–5.6.3, §5.6.5 and §5.8.3. The **tail reflector** keeps the
coordinates of a vector before a pivot $p$ and annihilates those after it. The **Householder
reduction to Hessenberg form** is a unitary similarity $H = Q^H A Q$ by $N - 2$ tail reflectors, and
$H$ is tridiagonal when $A$ is Hermitian. The **Givens QR factorization of a Hessenberg matrix**
uses $N - 1$ plane rotations, and its factor $Q$ is again Hessenberg. The file ends with Hadamard's
determinant inequality. Tail reflectors that alternate on the two sides also give the Golub–Kahan
bidiagonalization, which is in `Numlib.LinearAlgebra.Matrix.Bidiagonal`.

## Main definitions

* `Matrix.householder`: the reflector $P(w) = I - 2 w w^H$.
* `Matrix.reflector`: the reflector $I - (2 / v^H v)\, v v^H$ of an axis $v$ that need not have unit
  length, the matrix $P = I - \beta v v^T$ of [golub2013matrix], (5.1.1).
* `Matrix.phase`: the phase $z / |z|$ of a nonzero scalar, and $1$ at zero; this is the
  $\operatorname{sign}$ of [saad2003iterative], (1.22).
* `Matrix.householderAxis`, `Matrix.householderVec`: the axis
  $x + \operatorname{sign}(x_i) \|x\|_2 e_i$ of the reflector that annihilates every entry of $x$
  but the $i$-th, and its normalization.
* `Matrix.householderTail`: the unit axis of the reflector that acts on the coordinates from a pivot
  on.
* `Matrix.IsThinQR`: the thin QR factorization $A = QR$ with $Q^H Q = I$ and $R$ square upper
  triangular ([golub2013matrix], (5.2.2)).
* `Matrix.gramSchmidtQ`, `Matrix.gramSchmidtR`: the factors of the Gram–Schmidt factorization.
* `Matrix.firstColumns`, `Matrix.lastColumns`, `Matrix.firstRows`, `Matrix.lastRows`: the leading
  and trailing columns and rows of a matrix, such as the blocks $Q_1$, $Q_2$ and $\tilde R$ of a QR
  factorization.
* `Matrix.IsQR`: the full QR factorization $A = QR$ of an $M \times N$ matrix, with $Q$ unitary and
  $R$ upper trapezoidal ([quarteroni2000numerical], Definition 3.1).
* `Matrix.IsPivotedQR`: the QR factorization with column pivoting, $A \Pi = QR$.
* `Matrix.hessenbergReduce`, `Matrix.hessenbergQ`: the Householder reduction to Hessenberg form and
  its unitary factor, built from the steps `Matrix.hessenbergStep`.
* `Matrix.hessenbergGivensQR`: the Givens QR factorization of a real Hessenberg matrix.

## Main results

* `Matrix.householder_mulVec_eq_smul_single`: one reflector sends $x \neq 0$ to
  $-\operatorname{sign}(x_i) \|x\|_2 e_i$.
* `Matrix.det_householder`, `Matrix.det_reflector`: a reflector of a nonzero axis has determinant
  $-1$.
* `Matrix.reflector_mulVec_eq_of_sq`: if $\bar\alpha \alpha = \|x\|_2^2$ and $\bar\alpha x_i$ is
  real, the reflector of $x + \alpha e_i$ sends $x$ to $-\alpha e_i$ ([golub2013matrix], (5.1.2)).
* `Matrix.reflector_eq_householder`, `Matrix.reflector_mem_unitaryGroup`: the reflector of an axis
  is the Householder reflector of the normalized axis, and it is unitary.
* `Matrix.householder_mul_eq_sub_vecMulVec`, `Matrix.mul_householder_eq_sub_vecMulVec`: applying a
  reflector is a rank-one update.
* `Matrix.conj_one_sub_smul_vecMulVec_eq_sub`: $PBP = B - v w^H - w v^H$ for a Hermitian $B$, the
  rank-two form of a two-sided reflection ([golub2013matrix], §8.3.1).
* `Matrix.exists_unitary_mul_upperTriangular`, `Matrix.exists_unitary_mul_isUpperTriangular`: every
  matrix is carried to upper triangular form by a unitary matrix.
* `Matrix.exists_mem_unitaryGroup_mulVec_single_eq`: every unit vector is a column of a unitary
  matrix.
* `Matrix.householder_tail_mulVec`: the tail reflector keeps the coordinates before the pivot and
  annihilates those after it.
* `Matrix.IsThinQR.linearIndependent_iff_isUnit`: the columns of $A$ are linearly independent
  exactly when $R$ is invertible.
* `Matrix.IsThinQR.unique`: the thin QR factorization with a positive diagonal is unique.
* `Matrix.exists_isThinQR`: a matrix with linearly independent columns has a thin QR factorization
  with a positive diagonal ([golub2013matrix], Theorem 5.2.3).
* `Matrix.firstColumns_mul_conjTranspose_add_lastColumns_mul_conjTranspose`: the column blocks of a
  unitary matrix satisfy $Q_1 Q_1^H + Q_2 Q_2^H = I$.
* `Matrix.exists_isQR`, `Matrix.IsQR.isThinQR`: every matrix has a full QR factorization, and its
  leading blocks form a thin QR factorization ([quarteroni2000numerical], Property 3.3).
* `Matrix.IsQR.span_firstColumns_eq`, `Matrix.IsQR.span_col_prefix_eq`: for $A$ with linearly
  independent columns, the leading columns of $A$ and $Q$ span the same subspaces
  ([golub2013matrix], (5.2.1)).
* `Matrix.prodFwd_one_sub_vecMulVec_of_orthogonal`: for pairwise orthogonal $q_i$,
  $\prod_i (I - q_i q_i^H) = I - \sum_i q_i q_i^H$, the identity behind modified Gram–Schmidt
  ([golub2013matrix], §5.2.8).
* `Matrix.hessenbergReduce_eq_conj`, `Matrix.isUpperHessenberg_hessenbergReduce`,
  `Matrix.isTridiagonal_hessenbergReduce_of_isHermitian`: the Householder reduction is a unitary
  similarity to upper Hessenberg form, and it is tridiagonal for Hermitian $A$.
* `Matrix.exists_unitary_conj_isUpperHessenberg`: every square matrix is unitarily similar to an
  upper Hessenberg matrix.
* `Matrix.hasLowerBandwidthRect_zero_of_adjacentRotations`: a sweep of zeroing transformations in
  the adjacent planes $(j, j + 1)$ reduces a Hessenberg matrix to upper trapezoidal form.
* `Matrix.hasLowerBandwidthRect_prodFwd_adjacentEmbed_mul`: a product of transformations in the
  planes $(0, 1), (1, 2), \dots$ in increasing order, times an upper trapezoidal matrix, is upper
  Hessenberg.
* `Matrix.hessenbergGivensQR_spec`: the Givens factorization of a Hessenberg matrix is a QR
  factorization with a Hessenberg $Q$.
* `Matrix.norm_det_le_prod_sqrt_sum_norm_sq`: **Hadamard's determinant inequality**,
  $|\det X| \le \prod_j \|X(:, j)\|_2$, with `Matrix.norm_det_le_of_forall_norm_le` its entrywise
  form.

## Implementation notes

* The file treats exact arithmetic only. It has no stability analysis, no operation counts and no
  pivoting strategy.
* The algorithms of [quarteroni2000numerical], §5.6, step through the columns. They are stated for
  matrices indexed by `Fin N`, with the step index in `ℕ`. A step whose pivot lies beyond $N$ is the
  identity (`Matrix.householderTail` is $0$ there). This makes the folds total, and the invariants
  are proved by induction on `ℕ`. The existence statements are transported to any finite linearly
  ordered index type along `monoEquivOfFin`.
* A vector of `n → 𝕜` is measured with the Euclidean norm of `EuclideanSpace 𝕜 n`, written
  `‖WithLp.toLp 2 x‖`.
-/

open scoped Matrix

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

/-! ### The Euclidean length of a vector of scalars -/

private theorem ofReal_norm_toLp_ne_zero {x : n → 𝕜} (hx : x ≠ 0) :
    ((‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ : 𝕜)) ≠ 0 := by
  have hne : (WithLp.toLp 2 x : EuclideanSpace 𝕜 n) ≠ 0 := by simpa using hx
  simpa using norm_ne_zero_iff.2 hne

private theorem norm_toLp_pos {x : n → 𝕜} (hx : x ≠ 0) :
    (0 : ℝ) < ‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ := by
  have hne : (WithLp.toLp 2 x : EuclideanSpace 𝕜 n) ≠ 0 := by simpa using hx
  exact norm_pos_iff.2 hne

/-- The vector $v / \|v\|_2$, which is $0$ when $v = 0$. -/
private noncomputable def normalize (v : n → 𝕜) : n → 𝕜 :=
  ((‖(WithLp.toLp 2 v : EuclideanSpace 𝕜 n)‖ : 𝕜))⁻¹ • v

private theorem star_dotProduct_normalize_self {v : n → 𝕜} (hv : v ≠ 0) :
    star (normalize v) ⬝ᵥ normalize v = 1 := by
  have hN := ofReal_norm_toLp_ne_zero hv
  rw [normalize, star_smul, smul_dotProduct, dotProduct_smul, RCLike.star_def, RCLike.conj_inv,
    RCLike.conj_ofReal, smul_eq_mul, smul_eq_mul, star_dotProduct_self]
  field_simp

private theorem normalize_apply_eq_zero {v : n → 𝕜} {r : n} (h : v r = 0) :
    normalize v r = 0 := by simp [normalize, h]

/-! ### Householder reflectors -/

variable [DecidableEq n]

/-- The **Householder reflector** of $w \in \mathbb{K}^n$ is
$$P(w) = I - 2 w w^H.$$
When $w$ is a unit vector it is the reflection in the hyperplane orthogonal to $w$. When $w = 0$
it is the identity. -/
def householder (w : n → 𝕜) : Matrix n n 𝕜 := 1 - (2 : 𝕜) • vecMulVec w (star w)

omit [Fintype n] in
/-- The entries of a Householder reflector: $P(w)_{ij} = \delta_{ij} - 2 w_i \overline{w_j}$. -/
theorem householder_apply (w : n → 𝕜) (i j : n) :
    householder w i j = (if i = j then 1 else 0) - 2 * (w i * star (w j)) := by
  simp [householder, Matrix.one_apply, vecMulVec_apply]

omit [Fintype n] in
/-- The reflector of the zero axis is the identity: $P(0) = I$. -/
@[simp]
theorem householder_zero : householder (0 : n → 𝕜) = 1 := by simp [householder]

omit [Fintype n] in
/-- A Householder reflector $P(w)$ is Hermitian, for every $w$. -/
theorem isHermitian_householder (w : n → 𝕜) : IsHermitian (householder w) := by
  ext i j
  simp only [conjTranspose_apply, householder_apply, star_sub, star_mul', RCLike.star_def,
    map_ofNat, apply_ite (starRingEnd 𝕜), map_one, map_zero, starRingEnd_self_apply]
  by_cases h : i = j
  · subst h
    ring
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h]
    ring

/-- A Householder reflector acts by $P(w) x = x - 2 \langle w, x \rangle\, w$. -/
theorem householder_mulVec (w x : n → 𝕜) :
    householder w *ᵥ x = x - (2 * (star w ⬝ᵥ x)) • w := by
  funext i
  have h : ∀ j, householder w i j * x j
      = (if i = j then x j else 0) - 2 * (star (w j) * x j) * w i := by
    intro j
    rw [householder_apply]
    by_cases hij : i = j <;> simp [hij] <;> ring
  have hsum2 : ∑ j : n, 2 * (star (w j) * x j) * w i = (2 * (star w ⬝ᵥ x)) * w i := by
    simp only [dotProduct, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [mulVec, dotProduct, Finset.sum_congr rfl fun j _ => h j, Finset.sum_sub_distrib, hsum2]
  simp

/-- Let $w \in \mathbb{K}^n$ be a unit vector, $w^H w = 1$. Then $P(w)$ is an involution:
$$P(w)\, P(w) = I.$$
-/
theorem householder_mul_self {w : n → 𝕜} (hw : star w ⬝ᵥ w = 1) :
    householder w * householder w = 1 := by
  have hP : vecMulVec w (star w) * vecMulVec w (star w) = vecMulVec w (star w) := by
    rw [vecMulVec_mul_vecMulVec]
    congr 1
    rw [show (star w : n → 𝕜) ⬝ᵥ w = 1 from hw, one_smul]
  have h2 : ((2 : 𝕜) • vecMulVec w (star w)) * ((2 : 𝕜) • vecMulVec w (star w))
      = (4 : 𝕜) • vecMulVec w (star w) := by
    rw [smul_mul_smul_comm, hP]
    norm_num
  simp only [householder, sub_mul, mul_sub, one_mul, mul_one, h2]
  module

/-- Let $w \in \mathbb{K}^n$ be a unit vector, $w^H w = 1$. Then $P(w)$ is unitary. -/
theorem householder_mem_unitaryGroup {w : n → 𝕜} (hw : star w ⬝ᵥ w = 1) :
    householder w ∈ Matrix.unitaryGroup n 𝕜 := by
  rw [mem_unitaryGroup_iff']
  have hs : (star (householder w) : Matrix n n 𝕜) = householder w := isHermitian_householder w
  rw [hs, householder_mul_self hw]

/-- **A Householder reflector has determinant $-1$.** Let $w \in \mathbb{K}^n$ with $w^H w = 1$.
Then $\det P(w) = -1$.

The reflector is $I + u v^T$ with $v^T u = -2 w^H w = -2$, so
`Matrix.det_one_add_replicateCol_mul_replicateRow` applies. -/
theorem det_householder {w : n → 𝕜} (hw : star w ⬝ᵥ w = 1) : (householder w).det = -1 := by
  have e : householder w =
      1 + replicateCol Unit (-(2 : 𝕜) • w) * replicateRow Unit (star w) := by
    rw [householder, ← vecMulVec_eq, smul_vecMulVec, neg_smul, sub_eq_add_neg]
  rw [e, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, hw]
  norm_num

/-- For $v \neq 0$, the reflector of the normalized axis $v / \|v\|_2$ sends $x$ to $x - (2 \langle
v, x \rangle / \langle v, v \rangle)\, v$. -/
private theorem householder_normalize_mulVec {v : n → 𝕜} (hv : v ≠ 0) (x : n → 𝕜) :
    householder (normalize v) *ᵥ x = x - (2 * (star v ⬝ᵥ x) / (star v ⬝ᵥ v)) • v := by
  have hN := ofReal_norm_toLp_ne_zero hv
  rw [householder_mulVec, normalize, star_smul, smul_dotProduct, RCLike.star_def, RCLike.conj_inv,
    RCLike.conj_ofReal, smul_eq_mul, smul_smul, star_dotProduct_self]
  congr 2
  field_simp

/-! ### The reflector that annihilates a column below one entry -/

/-- The **phase** of a scalar $z \in \mathbb{K}$:
$$\operatorname{phase}(z) = \begin{cases} z / |z| & \text{if } z \neq 0, \\ 1 & \text{if }
  z = 0. \end{cases}$$
This is the $\operatorname{sign}$ of [saad2003iterative], (1.22). Over $\mathbb{R}$ it is the
sign $\pm 1$, with the value $1$ at zero. -/
noncomputable def phase (z : 𝕜) : 𝕜 := if z = 0 then 1 else ((‖z‖ : 𝕜))⁻¹ * z

/-- The phase of $0$ is $1$, by convention. -/
@[simp]
theorem phase_zero : phase (0 : 𝕜) = 1 := by simp [phase]

/-- The phase has modulus one: $|\operatorname{phase}(z)| = 1$. -/
@[simp]
theorem norm_phase (z : 𝕜) : ‖phase z‖ = 1 := by
  rw [phase]
  by_cases h : z = 0
  · simp [h]
  · rw [ite_eq_right h, norm_mul, norm_inv, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg z), inv_mul_cancel₀ (norm_ne_zero_iff.2 h)]

/-- The defining property of the phase: $\overline{\operatorname{phase}(z)}\, z = |z|$, a
nonnegative real number. This property keeps the denominator of [saad2003iterative], (1.22),
away from zero. -/
theorem conj_phase_mul_self (z : 𝕜) : starRingEnd 𝕜 (phase z) * z = ((‖z‖ : 𝕜)) := by
  rw [phase]
  by_cases h : z = 0
  · simp [h]
  · rw [ite_eq_right h, map_mul, RCLike.conj_inv, RCLike.conj_ofReal, mul_assoc, RCLike.conj_mul]
    have hz : ((‖z‖ : 𝕜)) ≠ 0 := by simpa using norm_ne_zero_iff.2 h
    field_simp

/-- The **Householder axis** of $x \in \mathbb{K}^n$ at the index $i$, from [saad2003iterative],
(1.22):
$$v = x + \operatorname{phase}(x_i)\, \|x\|_2\, e_i.$$
Its reflector annihilates every entry of $x$ but the $i$-th. -/
noncomputable def householderAxis (x : n → 𝕜) (i : n) : n → 𝕜 :=
  x + (phase (x i) * ((‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ : 𝕜)))
    • (Pi.single i 1 : n → 𝕜)

/-- The **Householder vector** of $x \in \mathbb{K}^n$ at the index $i$, from [saad2003iterative],
(1.22): the Householder axis $v = x + \operatorname{phase}(x_i) \|x\|_2 e_i$ divided by its
length, $w = v / \|v\|_2$. Its reflector annihilates every entry of $x$ but the $i$-th.

When $x = 0$ the axis is $0$, and the Householder vector is $0$ too
(`Matrix.householderVec_zero`). -/
noncomputable def householderVec (x : n → 𝕜) (i : n) : n → 𝕜 := normalize (householderAxis x i)

/-- Away from the pivot, the Householder axis agrees with the vector: for $r \neq i$, the $r$-th
entry of $x + \operatorname{phase}(x_i) \|x\|_2 e_i$ is $x_r$. -/
theorem householderAxis_apply_of_ne (x : n → 𝕜) {r i : n} (h : r ≠ i) :
    householderAxis x i r = x r := by
  simp [householderAxis, Pi.single_eq_of_ne h]

/-- The Householder vector of $x$ at $i$ vanishes where $x$ vanishes away from the pivot: if
$r \neq i$ and $x_r = 0$, then $w_r = 0$. This lets a reflector act on a trailing block of
coordinates only. -/
theorem householderVec_apply_eq_zero {x : n → 𝕜} {r i : n} (hri : r ≠ i) (h : x r = 0) :
    householderVec x i r = 0 :=
  normalize_apply_eq_zero (by rw [householderAxis_apply_of_ne x hri, h])

/-- For the Householder axis $v$ of $x$ at $i$, $\langle v, x \rangle$ is the nonnegative real
number $\|x\|_2^2 + \|x\|_2 |x_i|$. -/
private theorem star_householderAxis_dotProduct (x : n → 𝕜) (i : n) :
    star (householderAxis x i) ⬝ᵥ x
      = (((‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ ^ 2
          + ‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ * ‖x i‖ : ℝ)) : 𝕜) := by
  rw [householderAxis, star_add, add_dotProduct, star_smul, smul_dotProduct,
    ← Pi.single_star, star_one, single_dotProduct, star_dotProduct_self, RCLike.star_def, map_mul,
    RCLike.conj_ofReal, smul_eq_mul]
  push_cast
  linear_combination
    ((‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ : 𝕜)) * conj_phase_mul_self (x i)

/-- For the Householder axis $v$ of $x$ at $i$, $\langle v, v \rangle = 2 \langle v, x \rangle$. The
choice of the phase makes the two agree up to the factor $2$. -/
private theorem star_householderAxis_dotProduct_self (x : n → 𝕜) (i : n) :
    star (householderAxis x i) ⬝ᵥ householderAxis x i
      = 2 * (star (householderAxis x i) ⬝ᵥ x) := by
  have hself : star (householderAxis x i) ⬝ᵥ (Pi.single i 1 : n → 𝕜)
      = starRingEnd 𝕜 (householderAxis x i i) := by
    rw [dotProduct_single, mul_one]
    rfl
  have hval : householderAxis x i i
      = x i + phase (x i) * ((‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ : 𝕜)) := by
    simp [householderAxis]
  have h1 : phase (x i) * starRingEnd 𝕜 (x i) = ((‖x i‖ : 𝕜)) := by
    have h := congrArg (starRingEnd 𝕜) (conj_phase_mul_self (x i))
    rwa [map_mul, starRingEnd_self_apply, RCLike.conj_ofReal] at h
  have h2 : phase (x i) * starRingEnd 𝕜 (phase (x i)) = 1 := by
    rw [RCLike.mul_conj, norm_phase]
    norm_num
  nth_rewrite 2 [householderAxis]
  rw [dotProduct_add, dotProduct_smul, smul_eq_mul, hself, hval, star_householderAxis_dotProduct,
    map_add, map_mul, RCLike.conj_ofReal]
  push_cast
  linear_combination ((‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ : 𝕜)) * h1
    + ((‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ : 𝕜)) ^ 2 * h2

/-- Let $x \in \mathbb{K}^n$ with $x \neq 0$, and let $i$ be an index. Then the Householder axis is
nonzero:
$$x + \operatorname{phase}(x_i)\, \|x\|_2\, e_i \neq 0.$$
-/
theorem householderAxis_ne_zero {x : n → 𝕜} (hx : x ≠ 0) (i : n) :
    householderAxis x i ≠ 0 := by
  intro h
  have hd := star_householderAxis_dotProduct x i
  rw [h] at hd
  simp only [star_zero, zero_dotProduct] at hd
  have hpos : (0 : ℝ) < ‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ ^ 2
      + ‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ * ‖x i‖ := by
    have := norm_toLp_pos hx
    positivity
  rw [eq_comm, RCLike.ofReal_eq_zero] at hd
  exact hpos.ne' hd

/-- Let $x \neq 0$. Then the Householder vector $w$ of $x$ at $i$ is a unit vector, $w^H w = 1$. -/
theorem star_dotProduct_householderVec_self {x : n → 𝕜} (hx : x ≠ 0) (i : n) :
    star (householderVec x i) ⬝ᵥ householderVec x i = 1 :=
  star_dotProduct_normalize_self (householderAxis_ne_zero hx i)

/-- Let $x \neq 0$. Then the reflector of the Householder vector of $x$ at $i$ is unitary. -/
theorem householder_householderVec_mem_unitaryGroup {x : n → 𝕜} (hx : x ≠ 0) (i : n) :
    householder (householderVec x i) ∈ Matrix.unitaryGroup n 𝕜 :=
  householder_mem_unitaryGroup (star_dotProduct_householderVec_self hx i)

/-- [saad2003iterative], (1.21)–(1.22). Let $x \in \mathbb{K}^n$ with $x \neq 0$, let $i$ be an
index, and let $w$ be the Householder vector of $x$ at $i$, the unit vector along
$x + \operatorname{phase}(x_i) \|x\|_2 e_i$. Then
$$P(w)\, x = -\operatorname{phase}(x_i)\, \|x\|_2\, e_i,$$
so a single reflector annihilates every entry of $x$ but the $i$-th.

The vector $w$ is `Matrix.householderVec x i`. -/
theorem householder_mulVec_eq_smul_single {x : n → 𝕜} (hx : x ≠ 0) (i : n) :
    householder (householderVec x i) *ᵥ x
      = (-(phase (x i) * ((‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ : 𝕜))))
        • (Pi.single i 1 : n → 𝕜) := by
  have hv := householderAxis_ne_zero hx i
  have hd : star (householderAxis x i) ⬝ᵥ householderAxis x i
      = 2 * (star (householderAxis x i) ⬝ᵥ x) := star_householderAxis_dotProduct_self x i
  have hvv : star (householderAxis x i) ⬝ᵥ householderAxis x i ≠ 0 := by
    rw [star_dotProduct_self]
    exact pow_ne_zero 2 (ofReal_norm_toLp_ne_zero hv)
  rw [householderVec, householder_normalize_mulVec hv, ← hd, div_self hvv, one_smul,
    householderAxis]
  module

/-- **A unitary Hermitian matrix carries a vector to a multiple of a coordinate vector.** Let
$x \in \mathbb{K}^n$ and let $i$ be an index. Then there are a unitary Hermitian matrix $P$ and
a scalar $\alpha$ with
$$P x = \alpha e_i.$$

For $x \neq 0$, $P$ is the reflector of `Matrix.householder_mulVec_eq_smul_single`. For $x = 0$,
$P = I$. -/
theorem exists_mem_unitaryGroup_mulVec_eq_smul_single (x : n → 𝕜) (i : n) :
    ∃ P ∈ unitaryGroup n 𝕜, P.IsHermitian ∧ ∃ α : 𝕜, P *ᵥ x = α • Pi.single i 1 := by
  by_cases hx : x = 0
  · exact ⟨1, one_mem _, isHermitian_one, 0, by rw [hx, mulVec_zero, zero_smul]⟩
  · exact ⟨_, householder_householderVec_mem_unitaryGroup hx i, isHermitian_householder _, _,
      householder_mulVec_eq_smul_single hx i⟩

/-- **A unitary matrix with a prescribed column.** Let $x \in \mathbb{K}^n$ with $\|x\|_2 = 1$, and
let $i$ be an index. Then there is a unitary matrix $U$ with $U e_i = x$.

The matrix is $U = -\alpha P$, where $P$ is the reflector that sends $x$ to $-\alpha e_i$ and
$\alpha = \operatorname{phase}(x_i)$ has modulus one
(`Matrix.householder_mulVec_eq_smul_single`). -/
theorem exists_mem_unitaryGroup_mulVec_single_eq {x : n → 𝕜}
    (hx : ‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ = 1) (i : n) :
    ∃ U ∈ unitaryGroup n 𝕜, U *ᵥ Pi.single i 1 = x := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hPx : householder (householderVec x i) *ᵥ x = (-phase (x i)) • Pi.single i 1 := by
    rw [householder_mulVec_eq_smul_single hx0, hx, RCLike.ofReal_one, mul_one]
  have hPP : householder (householderVec x i) * householder (householderVec x i) = 1 :=
    householder_mul_self (star_dotProduct_householderVec_self hx0 i)
  have hstar : star (householder (householderVec x i)) = householder (householderVec x i) :=
    (isHermitian_householder _).eq
  have hαα : star (-phase (x i)) * (-phase (x i)) = 1 := by
    rw [star_neg, neg_mul_neg, RCLike.star_def, RCLike.conj_mul, norm_phase]
    simp
  refine ⟨(-phase (x i)) • householder (householderVec x i), ?_, ?_⟩
  · rw [mem_unitaryGroup_iff', star_smul, hstar, smul_mul_smul_comm, hαα, one_smul, hPP]
  · rw [smul_mulVec, ← mulVec_smul, ← hPx, mulVec_mulVec, hPP, one_mulVec]

/-! ### Householder reflectors of an unnormalized axis -/

/-- **The Householder reflector of an axis** $v \in \mathbb{K}^n$, which need not have unit length:
$$\operatorname{reflector}(v) = I - \frac{2}{v^H v}\, v v^H.$$
This is the matrix $P = I - \beta v v^T$, $\beta = 2 / v^T v$, of [golub2013matrix], (5.1.1),
and (19.1) of [higham2002accuracy].

At $v = 0$ it is the identity, because division by zero gives $0$ in Lean. It is the form of
`Matrix.householder` without normalization (`Matrix.reflector_eq_householder`). -/
noncomputable def reflector (v : n → 𝕜) : Matrix n n 𝕜 :=
  1 - (2 / (star v ⬝ᵥ v)) • vecMulVec v (star v)

/-- The reflector of the zero axis is the identity. -/
@[simp]
theorem reflector_zero : reflector (0 : n → 𝕜) = 1 := by simp [reflector]

/-- Let $v \in \mathbb{K}^n$ with $v \neq 0$. Then the reflector of $v$ is the Householder reflector
of the unit vector $v / \|v\|_2$:
$$\operatorname{reflector}(v) = P(v / \|v\|_2).$$
-/
theorem reflector_eq_householder {v : n → 𝕜} (hv : v ≠ 0) :
    reflector v =
      householder (((‖(WithLp.toLp 2 v : EuclideanSpace 𝕜 n)‖ : 𝕜))⁻¹ • v) := by
  have hN := ofReal_norm_toLp_ne_zero hv
  rw [reflector, householder, star_dotProduct_self, star_smul, vecMulVec_smul, smul_vecMulVec,
    smul_smul, smul_smul, RCLike.star_def, RCLike.conj_inv, RCLike.conj_ofReal]
  congr 2
  field_simp

/-- Let $v \neq 0$. Then $\det \operatorname{reflector}(v) = -1$. -/
theorem det_reflector {v : n → 𝕜} (hv : v ≠ 0) : (reflector v).det = -1 := by
  rw [reflector_eq_householder hv]
  exact det_householder (star_dotProduct_normalize_self hv)

/-- The reflector of any axis $v$ is Hermitian. -/
theorem isHermitian_reflector (v : n → 𝕜) : (reflector v).IsHermitian := by
  rcases eq_or_ne v 0 with rfl | hv
  · rw [reflector_zero]
    exact isHermitian_one
  · rw [reflector_eq_householder hv]
    exact isHermitian_householder _

/-- The reflector of any axis $v$ is an involution: $\operatorname{reflector}(v)^2 = I$. -/
theorem reflector_mul_self (v : n → 𝕜) : reflector v * reflector v = 1 := by
  rcases eq_or_ne v 0 with rfl | hv
  · rw [reflector_zero, Matrix.one_mul]
  · rw [reflector_eq_householder hv]
    exact householder_mul_self (star_dotProduct_normalize_self hv)

/-- **A reflector is unitary.** For every $v \in \mathbb{K}^n$, $\operatorname{reflector}(v)$ is
unitary. This is the statement "Householder matrices are symmetric and orthogonal" of
[golub2013matrix], §5.1.2.

The case $v = 0$ is included: the reflector is then the identity. -/
theorem reflector_mem_unitaryGroup (v : n → 𝕜) : reflector v ∈ Matrix.unitaryGroup n 𝕜 := by
  rw [mem_unitaryGroup_iff']
  have hs : (star (reflector v) : Matrix n n 𝕜) = reflector v := isHermitian_reflector v
  rw [hs, reflector_mul_self]

/-- For every $v \in \mathbb{R}^n$, $\operatorname{reflector}(v)$ is orthogonal. -/
theorem reflector_mem_orthogonalGroup (v : n → ℝ) : reflector v ∈ Matrix.orthogonalGroup n ℝ :=
  reflector_mem_unitaryGroup v

/-- For $v \in \mathbb{R}^n$, $\operatorname{reflector}(v) = I - (2 / v^T v)\, v v^T$. -/
theorem reflector_eq_one_sub_smul_vecMulVec (v : n → ℝ) :
    reflector v = 1 - (2 / (v ⬝ᵥ v)) • vecMulVec v v := by
  simp [reflector]

/-- The reflector of $v$ acts by $\operatorname{reflector}(v)\, x = x - (2 v^H x / v^H v)\, v$. -/
theorem reflector_mulVec (v x : n → 𝕜) :
    reflector v *ᵥ x = x - (2 / (star v ⬝ᵥ v) * (star v ⬝ᵥ x)) • v := by
  rw [reflector, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
    smul_smul]

open scoped RealInnerProductSpace in
/-- For $v, x \in \mathbb{R}^n$, the reflector of $v$ acts by
$x \mapsto x - 2 \langle w, x \rangle\, w$ in the Euclidean space $\mathbb{R}^n$, where
$w = v / \|v\|_2$, and $w = 0$ when $v = 0$.

The direction $w$ is `NormedSpace.normalize` of $v$ in `EuclideanSpace ℝ n`. -/
theorem toLp_reflector_mulVec (v x : n → ℝ) :
    (WithLp.toLp 2 (reflector v *ᵥ x) : EuclideanSpace ℝ n) = WithLp.toLp 2 x -
      (2 * ⟪NormedSpace.normalize (WithLp.toLp 2 v : EuclideanSpace ℝ n), WithLp.toLp 2 x⟫) •
        NormedSpace.normalize (WithLp.toLp 2 v : EuclideanSpace ℝ n) := by
  have hvx : v ⬝ᵥ x = ⟪(WithLp.toLp 2 v : EuclideanSpace ℝ n), WithLp.toLp 2 x⟫ := by
    rw [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm]
  rw [reflector_mulVec, star_trivial, dotProduct_self_eq_norm_sq, hvx, WithLp.toLp_sub,
    WithLp.toLp_smul, NormedSpace.normalize, real_inner_smul_left, smul_smul]
  congr 2
  ring

/-- **The defining property of a reflector, with either sign** ([golub2013matrix], (5.1.2), and its
complex form in §5.1.13). Let $x \in \mathbb{K}^n$, let $i$ be an index, and let
$\alpha \in \mathbb{K}$ satisfy $\bar\alpha \alpha = \|x\|_2^2$ and
$\bar\alpha x_i \in \mathbb{R}$. If the axis $v = x + \alpha e_i$ is nonzero, then
$$\operatorname{reflector}(v)\, x = -\alpha e_i.$$

The two conditions say that $\alpha = \pm \operatorname{phase}(x_i) \|x\|_2$ when $x_i \neq 0$.
They give $v^H x = \|x\|_2^2 + \bar\alpha x_i$ and $v^H v = 2 (\|x\|_2^2 + \bar\alpha x_i)$, so
the reflector sends $x$ to $x - v$. Over $\mathbb{R}$ the conditions read
$\alpha = \pm \|x\|_2$, and then $\operatorname{reflector}(v)\, x = \mp \|x\|_2 e_i$. The
condition $\bar\alpha x_i \in \mathbb{R}$ is the hypothesis that $\bar\alpha x_i$ equals its
conjugate. -/
theorem reflector_mulVec_eq_of_sq {x : n → 𝕜} {i : n} {α : 𝕜}
    (hα : star α * α = ((‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ : 𝕜)) ^ 2)
    (hreal : star (star α * x i) = star α * x i)
    (hv : x + α • Pi.single i 1 ≠ 0) :
    reflector (x + α • Pi.single i 1) *ᵥ x = -α • Pi.single i 1 := by
  set v := x + α • (Pi.single i 1 : n → 𝕜) with hvdef
  have hxx : star x ⬝ᵥ x = ((‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ : 𝕜)) ^ 2 :=
    star_dotProduct_self x
  have hsingle : star (Pi.single i 1 : n → 𝕜) = Pi.single i 1 := by
    funext r
    rcases eq_or_ne r i with rfl | h
    · simp
    · simp [Pi.single_eq_of_ne h]
  have hvx : star v ⬝ᵥ x = star x ⬝ᵥ x + star α * x i := by
    rw [hvdef, star_add, add_dotProduct, star_smul, smul_dotProduct, hsingle, single_dotProduct,
      one_mul, smul_eq_mul]
  have hvv : star v ⬝ᵥ v = 2 * (star v ⬝ᵥ x) := by
    have hvi : star v ⬝ᵥ (Pi.single i 1 : n → 𝕜) = star (x i) + star α := by
      rw [dotProduct_single, mul_one, hvdef]
      simp
    have hreal' : star α * x i = α * star (x i) := by
      rw [← hreal, star_mul', star_star, mul_comm]
    rw [show star v ⬝ᵥ v = star v ⬝ᵥ x + α * (star v ⬝ᵥ (Pi.single i 1 : n → 𝕜)) by
      rw [hvdef, dotProduct_add, dotProduct_smul, smul_eq_mul]]
    rw [hvi, hvx, hxx]
    linear_combination hα - hreal'
  have hvv0 : star v ⬝ᵥ v ≠ 0 := by
    rw [star_dotProduct_self]
    exact pow_ne_zero 2 (ofReal_norm_toLp_ne_zero hv)
  have hvx0 : star v ⬝ᵥ x ≠ 0 := fun h0 => hvv0 (by rw [hvv, h0, mul_zero])
  rw [reflector_mulVec, hvv, show 2 / (2 * (star v ⬝ᵥ x)) * (star v ⬝ᵥ x) = 1 by
    field_simp, one_smul, hvdef]
  module

/-! ### Reflectors as rank-one updates, and the coordinates they fix -/

section RankOne

variable {m : Type*}

/-- [quarteroni2000numerical], (5.49). Let $w \in \mathbb{K}^n$ and $M \in \mathbb{K}^{n \times m}$.
Applying a reflector on the left is a rank-one update:
$$P(w)\, M = M - 2 w (w^H M).$$
So $P(w) M$ is computed without a matrix product. -/
theorem householder_mul_eq_sub_vecMulVec (w : n → 𝕜) (M : Matrix n m 𝕜) :
    householder w * M = M - (2 : 𝕜) • vecMulVec w (star w ᵥ* M) := by
  rw [householder, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, vecMulVec_mul]

/-- [quarteroni2000numerical], (5.50). Let $M \in \mathbb{K}^{m \times n}$ and $w \in \mathbb{K}^n$.
Applying a reflector on the right is a rank-one update:
$$M\, P(w) = M - 2 (M w) w^H.$$
-/
theorem mul_householder_eq_sub_vecMulVec (M : Matrix m n 𝕜) (w : n → 𝕜) :
    M * householder w = M - (2 : 𝕜) • vecMulVec (M *ᵥ w) (star w) := by
  rw [householder, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, mul_vecMulVec]

/-- Let $w, x \in \mathbb{K}^n$ and let $i$ be an index with $w_i = 0$. Then $(P(w) x)_i = x_i$: a
reflector keeps the coordinates where its axis vanishes.

This is the block form $P = \operatorname{diag}(I, R)$ of [quarteroni2000numerical], (5.41),
stated without blocks. -/
theorem householder_mulVec_apply_of_apply_eq_zero {w : n → 𝕜} {i : n} (hw : w i = 0)
    (x : n → 𝕜) : (householder w *ᵥ x) i = x i := by
  rw [householder_mulVec, Pi.sub_apply, Pi.smul_apply, hw, smul_zero, sub_zero]

/-- Let $w, x \in \mathbb{K}^n$ with $w^H x = 0$. Then $P(w)\, x = x$: a reflector fixes every
vector orthogonal to its axis. -/
theorem householder_mulVec_eq_self_of_dotProduct_eq_zero {w x : n → 𝕜} (h : star w ⬝ᵥ x = 0) :
    householder w *ᵥ x = x := by
  rw [householder_mulVec, h, mul_zero, zero_smul, sub_zero]

/-- Let $w, x \in \mathbb{K}^n$, and suppose that $x_r = 0$ whenever $w_r \neq 0$. Then
$P(w)\, x = x$: a reflector fixes every vector that vanishes on the support of its axis. -/
theorem householder_mulVec_eq_self_of_apply_eq_zero {w x : n → 𝕜}
    (h : ∀ r, w r ≠ 0 → x r = 0) : householder w *ᵥ x = x := by
  refine householder_mulVec_eq_self_of_dotProduct_eq_zero (Finset.sum_eq_zero fun r _ => ?_)
  by_cases hr : w r = 0
  · rw [Pi.star_apply, hr, star_zero, zero_mul]
  · rw [h r hr, mul_zero]

/-- Let $w \in \mathbb{K}^n$ and $M \in \mathbb{K}^{n \times m}$. The columns of $P(w) M$ are the
images of the columns of $M$: $(P(w) M)_{ij} = (P(w)\, M(:, j))_i$. -/
theorem householder_mul_apply (w : n → 𝕜) (M : Matrix n m 𝕜) (i : n) (j : m) :
    (householder w * M) i j = (householder w *ᵥ fun r => M r j) i := rfl

/-- Let $w \in \mathbb{K}^n$ with $w_i = 0$, and let $M \in \mathbb{K}^{n \times m}$. Then row $i$
of $P(w) M$ is row $i$ of $M$: $(P(w) M)_{ij} = M_{ij}$ for all $j$. -/
theorem householder_mul_apply_of_apply_eq_zero {w : n → 𝕜} {i : n} (hw : w i = 0)
    (M : Matrix n m 𝕜) (j : m) : (householder w * M) i j = M i j := by
  rw [householder_mul_apply, householder_mulVec_apply_of_apply_eq_zero hw]

/-- Let $w \in \mathbb{K}^n$ with $w_j = 0$, and let $M \in \mathbb{K}^{m \times n}$. Then column
$j$ of $M P(w)$ is column $j$ of $M$: $(M P(w))_{ij} = M_{ij}$ for all $i$. -/
theorem mul_householder_apply_of_apply_eq_zero {w : n → 𝕜} {j : n} (hw : w j = 0)
    (M : Matrix m n 𝕜) (i : m) : (M * householder w) i j = M i j := by
  rw [mul_householder_eq_sub_vecMulVec, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply,
    Pi.star_apply, hw, star_zero, mul_zero, smul_zero, sub_zero]

/-- Let $x, u \in \mathbb{K}^n$. The row vector $x^T$ times the reflector of the conjugate axis
$\bar u$ is the transpose of $P(u) x$:
$$x^T P(\bar u) = (P(u)\, x)^T.$$
This is how a reflector acts on the rows of a matrix. -/
theorem vecMul_householder_star (x u : n → 𝕜) :
    x ᵥ* householder (star u) = householder u *ᵥ x := by
  rw [householder_mulVec, householder, vecMul_sub, vecMul_one, vecMul_smul, vecMul_vecMulVec,
    star_star, dotProduct_comm, smul_smul]

/-- Let $M \in \mathbb{K}^{m \times n}$ and $u \in \mathbb{K}^n$. The rows of $M P(\bar u)$ are the
images of the rows of $M$ under $P(u)$: $(M P(\bar u))_{ij} = (P(u)\, M(i, :)^T)_j$. -/
theorem mul_householder_star_apply (M : Matrix m n 𝕜) (u : n → 𝕜) (i : m) (j : n) :
    (M * householder (star u)) i j = (householder u *ᵥ M i) j := by
  rw [← vecMul_householder_star]
  rfl

omit [DecidableEq n] in
/-- Let $u \in \mathbb{K}^n$ with $u^H u = 1$. Then the conjugate vector $\bar u$ is also a unit
vector: $\bar u^H \bar u = 1$. -/
theorem star_dotProduct_star_self {u : n → 𝕜} (hu : star u ⬝ᵥ u = 1) :
    star (star u) ⬝ᵥ star u = 1 := by
  rw [star_star, dotProduct_comm, hu]

end RankOne

/-! ### The two-sided reflection as a rank-two update -/

section ConjReflector

variable {R : Type*} [Field R] [StarRing R]

omit [DecidableEq n] in
/-- Let $R$ be a field with a star operation, let $B \in R^{n \times n}$ with $B^H = B$, and let
$v \in R^n$. Then the quadratic form $v^H B v$ is self-adjoint: $\overline{v^H B v} = v^H B v$. -/
theorem star_dotProduct_mulVec_self_of_conjTranspose_eq {B : Matrix n n R} (hB : Bᴴ = B)
    (v : n → R) : star (star v ⬝ᵥ (B *ᵥ v)) = star v ⬝ᵥ (B *ᵥ v) :=
  IsHermitian.star_dotProduct_mulVec_comm hB v v

/-- **The two-sided reflection as a symmetric rank-two update** ([golub2013matrix], §8.3.1). Let $R$
be a field with a star operation in which $2 \neq 0$. Let $B \in R^{n \times n}$ be Hermitian,
$B^H = B$, let $v \in R^n$, and let $\beta \in R$ be self-adjoint, $\bar\beta = \beta$. Put
$P = I - \beta v v^H$, $p = \beta B v$ and $w = p - (\beta\, v^H p / 2)\, v$. Then
$$P B P = B - v w^H - w v^H.$$

No normalization of $v$ is needed, and $\beta = 0$ is allowed. Over $\mathbb{R}$ this is the
identity $P B P = B - v w^T - w v^T$ of the source. -/
theorem conj_one_sub_smul_vecMulVec_eq_sub (h2 : (2 : R) ≠ 0) {B : Matrix n n R} (hB : Bᴴ = B)
    (v : n → R) {β : R} (hβ : star β = β) {p w : n → R} (hp : p = β • (B *ᵥ v))
    (hw : w = p - ((β * (star v ⬝ᵥ p)) / 2) • v) :
    (1 - β • vecMulVec v (star v)) * B * (1 - β • vecMulVec v (star v)) =
      B - vecMulVec v (star w) - vecMulVec w (star v) := by
  set s := star v ⬝ᵥ (B *ᵥ v) with hs
  have hss : star s = s := star_dotProduct_mulVec_self_of_conjTranspose_eq hB v
  have e1 : vecMulVec v (star v) * B = vecMulVec v (star (B *ᵥ v)) := by
    rw [vecMulVec_mul, star_mulVec, hB]
  have e2 : B * vecMulVec v (star v) = vecMulVec (B *ᵥ v) (star v) := mul_vecMulVec _ _ _
  have e3 : vecMulVec v (star (B *ᵥ v)) * vecMulVec v (star v) = s • vecMulVec v (star v) := by
    rw [vecMulVec_mul_vecMulVec, vecMulVec_smul, star_mulVec, hB, ← dotProduct_mulVec]
  have hexp : (1 - β • vecMulVec v (star v)) * B * (1 - β • vecMulVec v (star v)) =
      B - β • vecMulVec v (star (B *ᵥ v)) - β • vecMulVec (B *ᵥ v) (star v) +
        (β * β * s) • vecMulVec v (star v) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, e1, e2, e3,
      smul_smul]
    module
  rw [hexp]
  subst hw hp
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, Pi.star_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, star_sub, star_mul', hβ, dotProduct_smul, ← hs,
    star_div₀,
    star_ofNat, hss]
  field_simp
  ring

end ConjReflector

/-! ### The matrices $1 - \beta v v^T$ over a commutative ring -/

section OneSubSmulVecMulVec

omit [Fintype n] in
/-- Let $R$ be a commutative ring, $\beta \in R$ and $v \in R^n$. Then the matrix $I - \beta v v^T$
is symmetric. -/
theorem transpose_one_sub_smul_vecMulVec {R : Type*} [CommRing R] (β : R)
    (v : n → R) : (1 - β • vecMulVec v v)ᵀ = 1 - β • vecMulVec v v := by
  rw [transpose_sub, transpose_one, transpose_smul, transpose_vecMulVec]

/-- Let $R$ be a commutative ring, $\beta \in R$ and $v \in R^n$. Then
$$(I - \beta v v^T)^2 = I + \beta (\beta\, v^T v - 2)\, v v^T.$$
-/
theorem one_sub_smul_vecMulVec_mul_self {R : Type*} [CommRing R] (β : R) (v : n → R) :
    (1 - β • vecMulVec v v) * (1 - β • vecMulVec v v) =
      1 + (β * (β * (v ⬝ᵥ v) - 2)) • vecMulVec v v := by
  have hV : vecMulVec v v * vecMulVec v v = (v ⬝ᵥ v) • vecMulVec v v := by
    rw [vecMulVec_mul_vecMulVec, vecMulVec_smul]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, hV, smul_smul]
  module

/-- Let $\beta \in \mathbb{R}$ and $v \in \mathbb{R}^n$ with $\beta (\beta\, v^T v - 2) = 0$. Then
$I - \beta v v^T$ is orthogonal.

The condition holds for a reflector ($\beta\, v^T v = 2$) and for the identity ($\beta = 0$). -/
theorem one_sub_smul_vecMulVec_mem_orthogonalGroup {β : ℝ} {v : n → ℝ}
    (h : β * (β * (v ⬝ᵥ v) - 2) = 0) :
    (1 - β • vecMulVec v v) ∈ Matrix.orthogonalGroup n ℝ := by
  rw [mem_orthogonalGroup_iff, transpose_one_sub_smul_vecMulVec,
    one_sub_smul_vecMulVec_mul_self, h, zero_smul, add_zero]

/-- **Orthogonality forces the dichotomy for $\beta$** ([golub2013matrix], §5.1.2). Let
$\beta \in \mathbb{R}$ and $v \in \mathbb{R}^n$ with $v \neq 0$. If $I - \beta v v^T$ is
orthogonal, then $\beta (\beta\, v^T v - 2) = 0$, that is, $\beta = 0$ or $\beta\, v^T v = 2$.

This is the converse of `Matrix.one_sub_smul_vecMulVec_mem_orthogonalGroup`. The condition
$v \neq 0$ is stated as $v_p \neq 0$ for some index $p$. -/
theorem mul_mul_dotProduct_sub_two_eq_zero_of_mem_orthogonalGroup {v : n → ℝ} {β : ℝ} {p : n}
    (hp : v p ≠ 0) (h : (1 - β • vecMulVec v v) ∈ Matrix.orthogonalGroup n ℝ) :
    β * (β * (v ⬝ᵥ v) - 2) = 0 := by
  have h1 := (mem_orthogonalGroup_iff' n ℝ).1 h
  rw [transpose_one_sub_smul_vecMulVec, one_sub_smul_vecMulVec_mul_self] at h1
  have h2 := congrFun (congrFun h1 p) p
  rw [Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, one_apply_eq, smul_eq_mul,
    add_eq_left] at h2
  rcases mul_eq_zero.1 h2 with h | h
  · exact h
  · exact absurd (mul_self_eq_zero.1 h) hp

/-- Let $\beta \in \mathbb{R}$ and $v \in \mathbb{R}^n$. If $I - \beta v v^T$ is orthogonal, then it
is an involution, $(I - \beta v v^T)^2 = I$, because it is symmetric. -/
theorem one_sub_smul_vecMulVec_mul_self_eq_one {v : n → ℝ} {β : ℝ}
    (h : (1 - β • vecMulVec v v) ∈ Matrix.orthogonalGroup n ℝ) :
    (1 - β • vecMulVec v v) * (1 - β • vecMulVec v v) = 1 := by
  have h1 := (mem_orthogonalGroup_iff' n ℝ).1 h
  rwa [transpose_one_sub_smul_vecMulVec] at h1

end OneSubSmulVecMulVec

/-! ### Triangularization by a product of reflectors -/

section Triangular

variable {N M : ℕ}

/-- One step of [saad2003iterative], Algorithm 1.3: if a unitary $P$ makes $PX$ vanish below the
diagonal in the columns $j < k$, then some unitary $P'$ makes $P'X$ vanish below the diagonal in
the columns $j < k + 1$. -/
private theorem triangular_step (X : Matrix (Fin N) (Fin M) 𝕜) (k : ℕ)
    {P : Matrix (Fin N) (Fin N) 𝕜} (hP : P ∈ Matrix.unitaryGroup (Fin N) 𝕜)
    (hT : ∀ (i : Fin N) (j : Fin M), (j : ℕ) < k → (j : ℕ) < (i : ℕ) → (P * X) i j = 0) :
    ∃ P' ∈ Matrix.unitaryGroup (Fin N) 𝕜,
      ∀ (i : Fin N) (j : Fin M), (j : ℕ) < k + 1 → (j : ℕ) < (i : ℕ) → (P' * X) i j = 0 := by
  by_cases hkM : k < M
  swap
  · exact ⟨P, hP, fun i j hj hij => hT i j (by omega) hij⟩
  by_cases hkN : k < N
  swap
  · refine ⟨P, hP, fun i j hj hij => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | hj'
    · exact hT i j hj' hij
    · exact absurd i.isLt (by omega)
  obtain ⟨κ, hκ⟩ : ∃ κ : Fin N, (κ : ℕ) = k := ⟨⟨k, hkN⟩, rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : Fin M, (μ : ℕ) = k := ⟨⟨k, hkM⟩, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : Fin N → 𝕜, ∀ r : Fin N,
      y r = if k ≤ (r : ℕ) then (P * X) r μ else 0 :=
    ⟨fun r => if k ≤ (r : ℕ) then (P * X) r μ else 0, fun _ => rfl⟩
  by_cases hy0 : y = 0
  · refine ⟨P, hP, fun i j hj hij => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | hj'
    · exact hT i j hj' hij
    · have hjμ : j = μ := Fin.ext (by omega)
      subst hjμ
      have h2 := hy i
      rw [ite_eq_left (show k ≤ (i : ℕ) by omega)] at h2
      rw [← h2, hy0]
      rfl
  · have hwzero : ∀ r : Fin N, (r : ℕ) < k → householderVec y κ r = 0 := by
      intro r hr
      refine householderVec_apply_eq_zero (fun hrk => ?_) ?_
      · rw [hrk] at hr; omega
      · rw [hy r, ite_eq_right (by omega)]
    have hstar0 : ∀ z : Fin N → 𝕜, (∀ r : Fin N, k ≤ (r : ℕ) → z r = 0) →
        star (householderVec y κ) ⬝ᵥ z = 0 := by
      intro z hz
      rw [dotProduct]
      refine Finset.sum_eq_zero fun r _ => ?_
      rcases lt_or_ge (r : ℕ) k with hr | hr
      · rw [Pi.star_apply, hwzero r hr, star_zero, zero_mul]
      · rw [hz r hr, mul_zero]
    have hfix : ∀ z : Fin N → 𝕜, (∀ r : Fin N, k ≤ (r : ℕ) → z r = 0) →
        householder (householderVec y κ) *ᵥ z = z := by
      intro z hz
      rw [householder_mulVec, hstar0 z hz, mul_zero, zero_smul, sub_zero]
    refine ⟨householder (householderVec y κ) * P,
      mul_mem (householder_householderVec_mem_unitaryGroup hy0 κ) hP, fun i j hj hij => ?_⟩
    have hcol : ∀ j : Fin M, (householder (householderVec y κ) * P * X) i j
        = (householder (householderVec y κ) *ᵥ fun r => (P * X) r j) i := fun j =>
      (congrFun₂ (Matrix.mul_assoc (householder (householderVec y κ)) P X) i j).trans rfl
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | hj'
    · rw [hcol j, hfix _ fun r hr => hT r j hj' (by omega)]
      exact hT i j hj' hij
    · have hjμ : j = μ := Fin.ext (by omega)
      subst hjμ
      have hsplit : (fun r => (P * X) r j)
          = (fun r : Fin N => if (r : ℕ) < k then (P * X) r j else 0) + y := by
        funext r
        rw [Pi.add_apply, hy r]
        by_cases hr : (r : ℕ) < k
        · rw [ite_eq_left hr, ite_eq_right (by omega), add_zero]
        · rw [ite_eq_right hr, ite_eq_left (by omega), zero_add]
      have hine : i ≠ κ := fun h => by rw [h] at hij; omega
      rw [hcol j, hsplit, mulVec_add, hfix _ fun r hr => ite_eq_right (by omega),
        householder_mulVec_eq_smul_single hy0 κ]
      rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ite_eq_right (show ¬((i : ℕ) < k) by omega),
        Pi.single_eq_of_ne hine, mul_zero, add_zero]

/-- [saad2003iterative], (1.27)–(1.28) and Algorithm 1.3. Let $X \in \mathbb{K}^{N \times M}$. Then
there is a unitary $P \in \mathbb{K}^{N \times N}$ such that $PX$ is upper triangular in the
rectangular sense:
$$(PX)_{ij} = 0 \quad \text{whenever } j < i.$$

The matrix $P$ is constructed as a product of at most $M$ Householder reflectors, one for each
column. -/
theorem exists_unitary_mul_upperTriangular (X : Matrix (Fin N) (Fin M) 𝕜) :
    ∃ P ∈ Matrix.unitaryGroup (Fin N) 𝕜,
      ∀ (i : Fin N) (j : Fin M), (j : ℕ) < (i : ℕ) → (P * X) i j = 0 := by
  suffices h : ∀ k : ℕ, ∃ P ∈ Matrix.unitaryGroup (Fin N) 𝕜,
      ∀ (i : Fin N) (j : Fin M), (j : ℕ) < k → (j : ℕ) < (i : ℕ) → (P * X) i j = 0 by
    obtain ⟨P, hP, hT⟩ := h M
    exact ⟨P, hP, fun i j hij => hT i j j.isLt hij⟩
  intro k
  induction k with
  | zero => exact ⟨1, one_mem _, fun _ _ hj _ => absurd hj (Nat.not_lt_zero _)⟩
  | succ k ih =>
    obtain ⟨P, hP, hT⟩ := ih
    exact triangular_step X k hP hT

/-- Let $n$ be a finite linearly ordered index type and let $X \in \mathbb{K}^{n \times n}$. Then
there is a unitary $U$ such that $UX$ is upper triangular.

This is `Matrix.exists_unitary_mul_upperTriangular` transported from `Fin N` to $n$ along
`monoEquivOfFin`. -/
theorem exists_unitary_mul_isUpperTriangular [LinearOrder n] (X : Matrix n n 𝕜) :
    ∃ U ∈ Matrix.unitaryGroup n 𝕜, (U * X).IsUpperTriangular := by
  obtain ⟨e, -⟩ : ∃ e : Fin (Fintype.card n) ≃o n, True := ⟨monoEquivOfFin n rfl, trivial⟩
  obtain ⟨P, hP, hT⟩ := exists_unitary_mul_upperTriangular (X.submatrix e.toEquiv e.toEquiv)
  refine ⟨P.submatrix e.toEquiv.symm e.toEquiv.symm, ?_, ?_⟩
  · rw [mem_unitaryGroup_iff', star_eq_conjTranspose, conjTranspose_submatrix,
      submatrix_mul_equiv, ← star_eq_conjTranspose, mem_unitaryGroup_iff'.mp hP,
      submatrix_one_equiv]
  · intro i j hij
    have hX : X = (X.submatrix e.toEquiv e.toEquiv).submatrix e.toEquiv.symm e.toEquiv.symm := by
      rw [submatrix_submatrix]
      ext i j
      simp
    rw [hX, submatrix_mul_equiv, submatrix_apply]
    refine hT _ _ ?_
    change (e.symm j : ℕ) < e.symm i
    exact e.symm.lt_iff_lt.mpr hij

end Triangular

/-! ### The reflector that annihilates the tail of a vector -/

section Tail

variable {N : ℕ}

/-- The **tail axis** of $x \in \mathbb{K}^N$ at the pivot $p \in \mathbb{N}$. For $p < N$, let
$\tilde x$ be the tail of $x$, with $\tilde x_i = x_i$ for $i \ge p$ and $\tilde x_i = 0$ for
$i < p$. The tail axis is the Householder vector of $\tilde x$ at $p$, the unit vector along
$$\tilde x + \operatorname{phase}(x_p)\, \|\tilde x\|_2\, e_p.$$
For $p \ge N$ the tail axis is $0$.

Its reflector keeps the coordinates $i < p$ of $x$, sends the $p$-th coordinate to
$-\operatorname{phase}(x_p) \|\tilde x\|_2$ and annihilates those after it
(`Matrix.householder_tail_mulVec`). The tail axis is also $0$ when the tail $\tilde x$ is zero,
and then the reflector is the identity. It is the vector $w^{(k)}$ of [quarteroni2000numerical],
(5.42), with $p = k + 1$, because the source counts from $1$. -/
noncomputable def householderTail (x : Fin N → 𝕜) (p : ℕ) : Fin N → 𝕜 :=
  if h : p < N then householderVec (fun i : Fin N => if p ≤ (i : ℕ) then x i else 0) ⟨p, h⟩
  else 0

variable (x : Fin N → 𝕜) {p : ℕ}

/-- For a pivot $p < N$, the tail axis of $x$ at $p$ is the Householder vector at $p$ of the tail of
$x$, the vector with entries $x_i$ for $i \ge p$ and $0$ for $i < p$. -/
theorem householderTail_of_lt (h : p < N) :
    householderTail x p =
      householderVec (fun i : Fin N => if p ≤ (i : ℕ) then x i else 0) ⟨p, h⟩ :=
  dite_eq_left h

/-- For a pivot $p \ge N$, the tail axis of $x$ at $p$ is $0$. -/
theorem householderTail_of_le (h : N ≤ p) : householderTail x p = 0 :=
  dite_eq_right (not_lt.2 h)

/-- The tail axis of $x$ at $p$ vanishes before the pivot: its $i$-th entry is $0$ for $i < p$. -/
theorem householderTail_apply_of_lt {i : Fin N} (hi : (i : ℕ) < p) :
    householderTail x p i = 0 := by
  by_cases h : p < N
  · rw [householderTail_of_lt x h]
    refine householderVec_apply_eq_zero (fun hip => ?_) (ite_eq_right (not_le.2 hi))
    rw [hip] at hi
    exact lt_irrefl _ hi
  · rw [householderTail_of_le x (not_lt.1 h), Pi.zero_apply]

/-- The Householder vector of the zero vector is zero, at every index $i$. So its reflector is the
identity. -/
theorem householderVec_zero (i : n) : householderVec (0 : n → 𝕜) i = 0 := by
  have h : householderAxis (0 : n → 𝕜) i = 0 := by
    rw [householderAxis, Pi.zero_apply, phase_zero, one_mul, WithLp.toLp_zero, norm_zero,
      RCLike.ofReal_zero, zero_smul, add_zero]
  rw [householderVec, h, normalize, smul_zero]

/-- Let $x \in \mathbb{K}^N$ and $p \in \mathbb{N}$. Then the reflector of the tail axis of $x$ at
$p$ is unitary, because the axis is a unit vector or zero. -/
theorem householder_householderTail_mem_unitaryGroup (p : ℕ) :
    householder (householderTail x p) ∈ Matrix.unitaryGroup (Fin N) 𝕜 := by
  by_cases h : p < N
  · rw [householderTail_of_lt x h]
    by_cases ht : (fun i : Fin N => if p ≤ (i : ℕ) then x i else 0) = 0
    · rw [ht, householderVec_zero, householder_zero]
      exact one_mem _
    · exact householder_householderVec_mem_unitaryGroup ht _
  · rw [householderTail_of_le x (not_lt.1 h), householder_zero]
    exact one_mem _

/-- Let $x \in \mathbb{K}^N$ and $p \in \mathbb{N}$. Then the reflector of the conjugate of the tail
axis of $x$ at $p$ is unitary. -/
theorem householder_star_householderTail_mem_unitaryGroup (p : ℕ) :
    householder (star (householderTail x p)) ∈ Matrix.unitaryGroup (Fin N) 𝕜 := by
  by_cases h : p < N
  · rw [householderTail_of_lt x h]
    by_cases ht : (fun i : Fin N => if p ≤ (i : ℕ) then x i else 0) = 0
    · rw [ht, householderVec_zero, star_zero, householder_zero]
      exact one_mem _
    · exact householder_mem_unitaryGroup
        (star_dotProduct_star_self (star_dotProduct_householderVec_self ht _))
  · rw [householderTail_of_le x (not_lt.1 h), star_zero, householder_zero]
    exact one_mem _

/-- [quarteroni2000numerical], (5.41)–(5.42). Let $x \in \mathbb{K}^N$, $p \in \mathbb{N}$, let $w$
be the tail axis of $x$ at $p$, and let $\tilde x$ be the tail of $x$, with entries $x_r$ for
$r \ge p$ and $0$ for $r < p$. Then
$$(P(w)\, x)_i = \begin{cases} x_i & \text{if } i < p, \\ -\operatorname{phase}(x_p)\, \|\tilde
  x\|_2 & \text{if } i = p, \\ 0 & \text{if } i > p. \end{cases}$$
So the reflector keeps the coordinates before the pivot and annihilates those after it. -/
theorem householder_tail_mulVec (p : ℕ) (i : Fin N) :
    (householder (householderTail x p) *ᵥ x) i =
      if (i : ℕ) < p then x i
      else if (i : ℕ) = p then
        -(phase (x i) * ((‖(WithLp.toLp 2 (fun r : Fin N => if p ≤ (r : ℕ) then x r else 0) :
          EuclideanSpace 𝕜 (Fin N))‖ : 𝕜)))
      else 0 := by
  by_cases h : p < N
  swap
  · rw [householderTail_of_le x (not_lt.1 h), householder_zero, one_mulVec,
      ite_eq_left (by have := i.isLt; omega)]
  obtain ⟨t, ht⟩ : ∃ t : Fin N → 𝕜, t = fun r : Fin N => if p ≤ (r : ℕ) then x r else 0 :=
    ⟨_, rfl⟩
  have htp : ∀ r : Fin N, p ≤ (r : ℕ) → t r = x r := fun r hr => by
    rw [ht]
    exact ite_eq_left hr
  have htp' : ∀ r : Fin N, (r : ℕ) < p → t r = 0 := fun r hr => by
    rw [ht]
    exact ite_eq_right (not_le.2 hr)
  rw [householderTail_of_lt x h, ← ht]
  by_cases ht0 : t = 0
  · have hx0 : ∀ r : Fin N, p ≤ (r : ℕ) → x r = 0 := fun r hr => by
      rw [← htp r hr, ht0, Pi.zero_apply]
    rw [ht0, householderVec_zero, householder_zero, one_mulVec]
    split_ifs with h1 h2
    · rfl
    · rw [hx0 i (by omega)]
      simp
    · exact hx0 i (by omega)
  · have hw : ∀ r : Fin N, (r : ℕ) < p → householderVec t ⟨p, h⟩ r = 0 := fun r hr =>
      householderVec_apply_eq_zero (fun hrp => by rw [hrp] at hr; exact lt_irrefl _ hr) (htp' r hr)
    have hfix : householder (householderVec t ⟨p, h⟩) *ᵥ (x - t) = x - t :=
      householder_mulVec_eq_self_of_apply_eq_zero fun r hr => by
        rw [Pi.sub_apply, htp r (not_lt.1 fun hrp => hr (hw r hrp)), sub_self]
    have key : householder (householderVec t ⟨p, h⟩) *ᵥ x =
        (x - t) + (-(phase (t ⟨p, h⟩) * ((‖(WithLp.toLp 2 t : EuclideanSpace 𝕜 (Fin N))‖ : 𝕜))))
          • (Pi.single (⟨p, h⟩ : Fin N) 1 : Fin N → 𝕜) := by
      calc householder (householderVec t ⟨p, h⟩) *ᵥ x
          = householder (householderVec t ⟨p, h⟩) *ᵥ ((x - t) + t) := by rw [sub_add_cancel]
        _ = _ := by rw [mulVec_add, hfix, householder_mulVec_eq_smul_single ht0]
    rw [key, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    split_ifs with h1 h2
    · rw [htp' i h1, sub_zero, Pi.single_eq_of_ne (Fin.ne_of_val_ne (show (i : ℕ) ≠ p by omega)),
        mul_zero, add_zero]
    · have hi : i = ⟨p, h⟩ := Fin.ext h2
      subst hi
      rw [htp _ le_rfl, sub_self, zero_add, Pi.single_eq_same, mul_one]
    · rw [htp i (by omega), sub_self, zero_add,
        Pi.single_eq_of_ne (Fin.ne_of_val_ne (show (i : ℕ) ≠ p by omega)), mul_zero]

/-- Let $x \in \mathbb{K}^N$ and $i < p$. Then the reflector of the tail axis of $x$ at $p$ keeps
the $i$-th coordinate of $x$. -/
theorem householder_householderTail_mulVec_apply_of_lt {i : Fin N} (hi : (i : ℕ) < p) :
    (householder (householderTail x p) *ᵥ x) i = x i := by
  rw [householder_tail_mulVec, ite_eq_left hi]

/-- Let $x \in \mathbb{K}^N$ and $i > p$. Then the reflector of the tail axis of $x$ at $p$ sends
the $i$-th coordinate of $x$ to $0$. -/
theorem householder_householderTail_mulVec_apply_of_gt {i : Fin N} (hi : p < (i : ℕ)) :
    (householder (householderTail x p) *ᵥ x) i = 0 := by
  rw [householder_tail_mulVec, ite_eq_right (by omega), ite_eq_right (by omega)]

/-- Let $x \in \mathbb{K}^N$ and $p < N$. Then the reflector of the tail axis of $x$ at $p$ sends
the $p$-th coordinate of $x$ to $-\operatorname{phase}(x_p)\, \|\tilde x\|_2$, where $\tilde x$
is the tail of $x$, with entries $x_r$ for $r \ge p$ and $0$ for $r < p$. -/
theorem householder_householderTail_mulVec_apply_self (h : p < N) :
    (householder (householderTail x p) *ᵥ x) ⟨p, h⟩ =
      -(phase (x ⟨p, h⟩) * ((‖(WithLp.toLp 2 (fun r : Fin N => if p ≤ (r : ℕ) then x r else 0) :
        EuclideanSpace 𝕜 (Fin N))‖ : 𝕜))) := by
  rw [householder_tail_mulVec, ite_eq_right (lt_irrefl p), ite_eq_left rfl]

/-- Let $x \in \mathbb{K}^N$ and $p < N$. After the reflector of the tail axis of $x$ at $p$, the
$p$-th coordinate has modulus $\|\tilde x\|_2$, the Euclidean length of the tail $\tilde x$ of
$x$ from $p$ on. -/
theorem norm_householder_householderTail_mulVec_apply_self (h : p < N) :
    ‖(householder (householderTail x p) *ᵥ x) ⟨p, h⟩‖ =
      ‖(WithLp.toLp 2 (fun r : Fin N => if p ≤ (r : ℕ) then x r else 0) :
        EuclideanSpace 𝕜 (Fin N))‖ := by
  rw [householder_householderTail_mulVec_apply_self x h, norm_neg, norm_mul, norm_phase, one_mul,
    RCLike.norm_ofReal, abs_norm]

end Tail

/-! ### The thin QR factorization -/

section ThinQR

open scoped ComplexOrder

variable {m : Type*} [Fintype m] {N : ℕ}

/-- **The thin (reduced) QR factorization** ([golub2013matrix], (5.2.2) and Theorem 5.2.3). Let
$A \in \mathbb{K}^{m \times N}$, $Q \in \mathbb{K}^{m \times N}$ and
$R \in \mathbb{K}^{N \times N}$. The pair $(Q, R)$ is a **thin QR factorization** of $A$ if
$$A = QR, \qquad Q^H Q = I,$$
and $R$ is upper triangular.

There is no sign condition on the diagonal of $R$; uniqueness (`Matrix.IsThinQR.unique`) needs a
positive diagonal. This is the specification of classical and modified Gram–Schmidt. A full
factorization `Matrix.IsQR` gives a thin one (`Matrix.IsQR.isThinQR`). -/
structure IsThinQR (A : Matrix m (Fin N) 𝕜) (Q : Matrix m (Fin N) 𝕜)
    (R : Matrix (Fin N) (Fin N) 𝕜) : Prop where
  /-- The factors multiply to $A$: $QR = A$. -/
  mul_eq : Q * R = A
  /-- The columns of $Q$ are orthonormal: $Q^H Q = I$. -/
  conjTranspose_mul_self : Qᴴ * Q = 1
  /-- The factor $R$ is upper triangular. -/
  isUpperTriangular : R.IsUpperTriangular

variable {A Q : Matrix m (Fin N) 𝕜} {R : Matrix (Fin N) (Fin N) 𝕜}

/-- If $(Q, R)$ is a thin QR factorization of $A$, then $R = Q^H A$. -/
theorem IsThinQR.conjTranspose_mul_eq (h : IsThinQR A Q R) : Qᴴ * A = R := by
  rw [← h.mul_eq, ← Matrix.mul_assoc, h.conjTranspose_mul_self, Matrix.one_mul]

/-- Let $(Q, R)$ be a thin QR factorization of $A$, and let the columns of $A$ be linearly
independent. Then $R$ is invertible.

The map $x \mapsto Ax = QRx$ is injective, so $x \mapsto Rx$ is injective. -/
theorem IsThinQR.isUnit_of_linearIndependent (h : IsThinQR A Q R) (hA : LinearIndependent 𝕜 Aᵀ) :
    IsUnit R := by
  rw [← mulVec_injective_iff_isUnit]
  intro x y hxy
  apply mulVec_injective_iff.2 hA
  rw [← h.mul_eq, ← mulVec_mulVec, ← mulVec_mulVec, hxy]

/-- Let $(Q, R)$ be a thin QR factorization of $A \in \mathbb{K}^{m \times N}$ with $R$ invertible.
Then the columns of $A$ are linearly independent.

The proof uses $R = Q^H A$: if $Ax = Ay$ then $Rx = Ry$. -/
theorem IsThinQR.linearIndependent (h : IsThinQR A Q R) (hR : IsUnit R) :
    LinearIndependent 𝕜 Aᵀ := by
  refine mulVec_injective_iff.1 fun x y hxy => ?_
  apply mulVec_injective_iff_isUnit.2 hR
  rw [← h.conjTranspose_mul_eq, ← mulVec_mulVec, ← mulVec_mulVec]
  exact congrArg _ hxy

/-- Let $(Q, R)$ be a thin QR factorization of $A$. Then the columns of $A$ are linearly independent
if and only if $R$ is invertible. -/
theorem IsThinQR.linearIndependent_iff_isUnit (h : IsThinQR A Q R) :
    LinearIndependent 𝕜 Aᵀ ↔ IsUnit R :=
  ⟨h.isUnit_of_linearIndependent, h.linearIndependent⟩

/-- **A unitary upper triangular matrix with positive diagonal is the identity.** Let
$S \in \mathbb{K}^{N \times N}$ be upper triangular with $S^H S = I$ and $s_{jj} > 0$ for all
$j$. Then $S = I$.

The condition $s_{jj} > 0$ uses the order of `ComplexOrder`, so it says that $s_{jj}$ is real
and positive. This is the uniqueness argument for orthonormal flags of
`Numlib.Analysis.InnerProductSpace.GramSchmidt`, at the level of matrices. It makes the QR
factorization with a positive diagonal unique. -/
theorem IsUpperTriangular.eq_one_of_conjTranspose_mul_self_eq_one {S : Matrix (Fin N) (Fin N) 𝕜}
    (hS : S.IsUpperTriangular) (hu : Sᴴ * S = 1) (hd : ∀ j, 0 < S j j) : S = 1 := by
  have key : ∀ m : ℕ, ∀ j : Fin N, (j : ℕ) = m →
      ∀ i : Fin N, S i j = if i = j then 1 else 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro j hjm
      have habove : ∀ i : Fin N, (i : ℕ) < (j : ℕ) → S i j = 0 := by
        intro i hi
        have h1 : (Sᴴ * S) i j = 0 := by
          rw [hu, Matrix.one_apply, ite_eq_right fun h => by rw [h] at hi; omega]
        rw [Matrix.mul_apply] at h1
        have h2 : ∀ r : Fin N, Sᴴ i r * S r j = if r = i then S i j else 0 := by
          intro r
          rw [conjTranspose_apply, ih (i : ℕ) (by omega) i rfl r]
          by_cases hr : r = i
          · subst hr; simp
          · simp [hr]
        rw [Finset.sum_congr rfl fun r _ => h2 r,
          Finset.sum_ite_eq' Finset.univ i fun _ => S i j] at h1
        simpa using h1
      have hcol : ∀ r : Fin N, r ≠ j → S r j = 0 := by
        intro r hr
        rcases lt_or_gt_of_ne hr with h | h
        · exact habove r h
        · exact hS h
      have hdiag : star (S j j) * S j j = 1 := by
        have h1 : (Sᴴ * S) j j = 1 := by rw [hu, Matrix.one_apply, ite_eq_left rfl]
        rw [Matrix.mul_apply] at h1
        have h2 : ∀ r : Fin N, Sᴴ j r * S r j = if r = j then star (S j j) * S j j else 0 := by
          intro r
          rw [conjTranspose_apply]
          by_cases hr : r = j
          · subst hr; simp
          · rw [hcol r hr, mul_zero, ite_eq_right hr]
        rw [Finset.sum_congr rfl fun r _ => h2 r,
          Finset.sum_ite_eq' Finset.univ j fun _ => star (S j j) * S j j] at h1
        simpa using h1
      have hjj : S j j = 1 := by
        obtain ⟨r, hr, hrz⟩ := RCLike.pos_iff_exists_ofReal.1 (hd j)
        rw [← hrz] at hdiag ⊢
        rw [RCLike.star_def, RCLike.conj_ofReal, ← RCLike.ofReal_mul, ← RCLike.ofReal_one,
          RCLike.ofReal_inj] at hdiag
        have hr1 : r = 1 := by nlinarith
        rw [hr1, RCLike.ofReal_one]
      intro i
      by_cases hij : i = j
      · subst hij
        rw [ite_eq_left rfl]
        exact hjj
      · rw [ite_eq_right hij]
        exact hcol i hij
  ext i j
  rw [key (j : ℕ) j rfl i, Matrix.one_apply]

/-- **Uniqueness of the thin QR factorization** ([golub2013matrix], Theorem 5.2.3). Let
$A \in \mathbb{K}^{m \times N}$, and let $(Q_1, R_1)$ and $(Q_2, R_2)$ be thin QR factorizations
of $A$ in which $R_1$ and $R_2$ have positive diagonal entries. Then $Q_1 = Q_2$ and
$R_1 = R_2$.

This identifies the product of reflectors of `Matrix.exists_unitary_mul_upperTriangular` with
the Gram–Schmidt factorization of `Matrix.exists_isThinQR`, and either of them with the
factorization of modified Gram–Schmidt, without a comparison of the constructions. Positive
means real and positive, in the order of `ComplexOrder`. The proof:
$A^H A = R_1^H R_1 = R_2^H R_2$, so $R_2 R_1^{-1}$ is unitary, upper triangular and of positive
diagonal, hence the identity. -/
theorem IsThinQR.unique {A Q₁ Q₂ : Matrix m (Fin N) 𝕜} {R₁ R₂ : Matrix (Fin N) (Fin N) 𝕜}
    (h₁ : IsThinQR A Q₁ R₁) (h₂ : IsThinQR A Q₂ R₂) (hd₁ : ∀ j, 0 < R₁ j j)
    (hd₂ : ∀ j, 0 < R₂ j j) : Q₁ = Q₂ ∧ R₁ = R₂ := by
  obtain ⟨hX₁, hQ₁, hR₁⟩ := h₁
  obtain ⟨hX₂, hQ₂, hR₂⟩ := h₂
  have hdet : IsUnit R₁.det := hR₁.isUnit_det_of_diag_ne_zero fun j => (hd₁ j).ne'
  have : Invertible R₁ := invertibleOfIsUnitDet R₁ hdet
  have hRR : R₁ᴴ * R₁ = R₂ᴴ * R₂ := by
    have h1 : Aᴴ * A = R₁ᴴ * R₁ := by
      rw [← hX₁, conjTranspose_mul]
      calc R₁ᴴ * Q₁ᴴ * (Q₁ * R₁) = R₁ᴴ * (Q₁ᴴ * Q₁ * R₁) := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc]
        _ = R₁ᴴ * R₁ := by rw [hQ₁, Matrix.one_mul]
    have h2 : Aᴴ * A = R₂ᴴ * R₂ := by
      rw [← hX₂, conjTranspose_mul]
      calc R₂ᴴ * Q₂ᴴ * (Q₂ * R₂) = R₂ᴴ * (Q₂ᴴ * Q₂ * R₂) := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc]
        _ = R₂ᴴ * R₂ := by rw [hQ₂, Matrix.one_mul]
    rw [← h1, h2]
  have hinvUT : (R₁⁻¹).IsUpperTriangular := blockTriangular_inv_of_blockTriangular hR₁
  have hSUT : (R₂ * R₁⁻¹).IsUpperTriangular := hR₂.mul hinvUT
  have hinvdiag : ∀ j, (R₁⁻¹) j j = (R₁ j j)⁻¹ := by
    intro j
    have h1 : R₁ j j * (R₁⁻¹) j j = 1 := by
      rw [← hR₁.mul_apply_self hinvUT j, mul_nonsing_inv R₁ hdet, one_apply_eq]
    calc (R₁⁻¹) j j = (R₁ j j)⁻¹ * (R₁ j j * (R₁⁻¹) j j) := by
          rw [← mul_assoc, inv_mul_cancel₀ (hd₁ j).ne', one_mul]
      _ = (R₁ j j)⁻¹ := by rw [h1, mul_one]
  have hSd : ∀ j, 0 < (R₂ * R₁⁻¹) j j := fun j => by
    rw [hR₂.mul_apply_self hinvUT j, hinvdiag j]
    exact mul_pos (hd₂ j) (RCLike.inv_pos_of_pos (hd₁ j))
  have hSu : (R₂ * R₁⁻¹)ᴴ * (R₂ * R₁⁻¹) = 1 := by
    have h : (R₂ * R₁⁻¹)ᴴ * (R₂ * R₁⁻¹) = (R₁⁻¹)ᴴ * (R₂ᴴ * R₂ * R₁⁻¹) := by
      rw [conjTranspose_mul]; noncomm_ring
    have h2 : (R₁⁻¹)ᴴ * (R₁ᴴ * R₁ * R₁⁻¹) = (R₁ * R₁⁻¹)ᴴ * (R₁ * R₁⁻¹) := by
      rw [conjTranspose_mul]; noncomm_ring
    rw [h, ← hRR, h2, mul_nonsing_inv R₁ hdet, conjTranspose_one, mul_one]
  have hS1 : R₂ * R₁⁻¹ = 1 := hSUT.eq_one_of_conjTranspose_mul_self_eq_one hSu hSd
  have hR : R₂ = R₁ := by
    calc R₂ = R₂ * (R₁⁻¹ * R₁) := by rw [nonsing_inv_mul R₁ hdet, mul_one]
      _ = R₂ * R₁⁻¹ * R₁ := by rw [mul_assoc]
      _ = R₁ := by rw [hS1, one_mul]
  refine ⟨?_, hR.symm⟩
  calc Q₁ = Q₁ * (R₁ * R₁⁻¹) := by rw [mul_nonsing_inv R₁ hdet, Matrix.mul_one]
    _ = Q₁ * R₁ * R₁⁻¹ := (Matrix.mul_assoc _ _ _).symm
    _ = Q₂ * R₂ * R₁⁻¹ := by rw [hX₁, hX₂]
    _ = Q₂ * (R₂ * R₁⁻¹) := Matrix.mul_assoc _ _ _
    _ = Q₂ := by rw [hS1, Matrix.mul_one]

end ThinQR

/-! ### The Gram–Schmidt factorization -/

section GramSchmidt

open InnerProductSpace
open scoped ComplexOrder

variable {m : Type*} [Fintype m] {N : ℕ} (A : Matrix m (Fin N) 𝕜)

/-- **The orthonormal factor of the Gram–Schmidt factorization.** Let
$A \in \mathbb{K}^{m \times N}$ have the columns $a_0, \dots, a_{N-1}$. Column $j$ of $Q$ is the
normalized Gram–Schmidt vector $q_j$ of $a_0, \dots, a_{N-1}$, in the Euclidean space
$\mathbb{K}^m$.

For linearly independent columns, $Q$ is the factor of the thin QR factorization with positive
diagonal (`Matrix.isThinQR_gramSchmidtQ`). In general, a column whose Gram–Schmidt vector
vanishes is zero. The normalized Gram–Schmidt vector is `InnerProductSpace.gramSchmidtNormed`. -/
noncomputable def gramSchmidtQ : Matrix m (Fin N) 𝕜 :=
  of fun r j => WithLp.ofLp (gramSchmidtNormed 𝕜 (fun j => WithLp.toLp 2 (A.col j)) j) r

/-- **The triangular factor of the Gram–Schmidt factorization.** Let $A \in \mathbb{K}^{m \times N}$
have the columns $a_j$, and let $q_i$ be the columns of `Matrix.gramSchmidtQ A`. Then
$$r_{ij} = \langle q_i, a_j \rangle.$$

The matrix vanishes below the diagonal (`Matrix.gramSchmidtR_apply_of_lt`), and its diagonal
entry $r_{jj}$ is the norm of the Gram–Schmidt vector `InnerProductSpace.gramSchmidt 𝕜 a j`
(`Matrix.gramSchmidtR_apply_self`). -/
noncomputable def gramSchmidtR : Matrix (Fin N) (Fin N) 𝕜 :=
  of fun i j =>
    inner 𝕜 (gramSchmidtNormed 𝕜 (fun j => WithLp.toLp 2 (A.col j)) i) (WithLp.toLp 2 (A.col j))

/-- **The Gram–Schmidt residual of column $k$.** Let $A \in \mathbb{K}^{m \times N}$ have the
columns $a_j$, let $q_i$ be the columns of `Matrix.gramSchmidtQ A` and $r_{ik}$ the entries of
`Matrix.gramSchmidtR A`. The residual of column $k$ is
$$z_k = a_k - \sum_{i < k} r_{ik}\, q_i,$$
the vector that classical Gram–Schmidt normalizes.

It is the Gram–Schmidt vector `InnerProductSpace.gramSchmidt 𝕜 a k`
(`Matrix.toLp_gramSchmidtResidual`). So $q_k = z_k / \|z_k\|_2$ (`Matrix.col_gramSchmidtQ`) and
$r_{kk} = \|z_k\|_2$ (`Matrix.gramSchmidtR_apply_self'`). -/
noncomputable def gramSchmidtResidual (k : Fin N) : m → 𝕜 :=
  A.col k - ∑ i ∈ Finset.Iio k, gramSchmidtR A i k • (gramSchmidtQ A).col i

/-- Column $j$ of `Matrix.gramSchmidtQ A`, as a vector of the Euclidean space $\mathbb{K}^m$, is the
normalized Gram–Schmidt vector of the columns of $A$ at $j$. -/
theorem toLp_col_gramSchmidtQ (j : Fin N) :
    WithLp.toLp 2 ((gramSchmidtQ A).col j) =
      gramSchmidtNormed 𝕜 (fun j => WithLp.toLp 2 (A.col j)) j :=
  rfl

/-- The entries of the Gram–Schmidt triangular factor: $r_{ij} = \langle q_i, a_j \rangle = a_j^T
\bar q_i$. -/
theorem gramSchmidtR_apply (i j : Fin N) :
    gramSchmidtR A i j = A.col j ⬝ᵥ star ((gramSchmidtQ A).col i) :=
  rfl

/-- The Gram–Schmidt triangular factor vanishes below the diagonal: $r_{ij} = 0$ for $j < i$. There
is no hypothesis on $A$. -/
theorem gramSchmidtR_apply_of_lt {i j : Fin N} (h : j < i) : gramSchmidtR A i j = 0 := by
  rw [gramSchmidtR, of_apply, gramSchmidtNormed, inner_smul_left,
    gramSchmidt_inv_triangular 𝕜 _ h, mul_zero]

/-- The diagonal entry $r_{jj}$ of the Gram–Schmidt triangular factor is the norm of the
Gram–Schmidt vector of the columns of $A$ at $j$. -/
theorem gramSchmidtR_apply_self (j : Fin N) :
    gramSchmidtR A j j = (‖gramSchmidt 𝕜 (fun j => WithLp.toLp 2 (A.col j)) j‖ : 𝕜) :=
  inner_gramSchmidtNormed_self (𝕜 := 𝕜) (fun j => WithLp.toLp 2 (A.col j)) j

/-- Distinct columns of `Matrix.gramSchmidtQ A` are orthogonal:
$\langle q_i, q_j \rangle = q_j^T \bar q_i = 0$ for $i \neq j$. There is no hypothesis on $A$. -/
theorem col_gramSchmidtQ_dotProduct_star {i j : Fin N} (h : i ≠ j) :
    (gramSchmidtQ A).col j ⬝ᵥ star ((gramSchmidtQ A).col i) = 0 := by
  change inner 𝕜 (gramSchmidtNormed 𝕜 (fun j => WithLp.toLp 2 (A.col j)) i)
    (gramSchmidtNormed 𝕜 (fun j => WithLp.toLp 2 (A.col j)) j) = 0
  rw [gramSchmidtNormed, gramSchmidtNormed, inner_smul_left, inner_smul_right,
    gramSchmidt_orthogonal 𝕜 _ h, mul_zero, mul_zero]

/-- Let $A \in \mathbb{K}^{m \times N}$. The Gram–Schmidt residual
$z_k = a_k - \sum_{i < k} r_{ik} q_i$ of column $k$ is the Gram–Schmidt vector of the columns of
$A$ at $k$, read in the Euclidean space $\mathbb{K}^m$. -/
theorem toLp_gramSchmidtResidual (k : Fin N) :
    WithLp.toLp 2 (gramSchmidtResidual A k) =
      gramSchmidt 𝕜 (fun j => WithLp.toLp 2 (A.col j)) k := by
  rw [gramSchmidtResidual, WithLp.toLp_sub, WithLp.toLp_sum, sub_eq_iff_eq_add]
  refine (gramSchmidt_def'' 𝕜 (fun j => WithLp.toLp 2 (A.col j)) k).trans
    (congrArg (gramSchmidt 𝕜 (fun j => WithLp.toLp 2 (A.col j)) k + ·)
      (Finset.sum_congr rfl fun i _ => ?_))
  rw [WithLp.toLp_smul, toLp_col_gramSchmidtQ, gramSchmidtR, of_apply,
    inner_gramSchmidtNormed_smul_self]

/-- Column $k$ of `Matrix.gramSchmidtQ A` is the Gram–Schmidt residual divided by its norm:
$q_k = z_k / \|z_k\|_2$. When $z_k = 0$, $q_k = 0$. -/
theorem col_gramSchmidtQ (k : Fin N) :
    (gramSchmidtQ A).col k =
      ((‖WithLp.toLp 2 (gramSchmidtResidual A k)‖ : 𝕜))⁻¹ • gramSchmidtResidual A k := by
  apply WithLp.toLp_injective 2
  rw [toLp_col_gramSchmidtQ, WithLp.toLp_smul, toLp_gramSchmidtResidual, gramSchmidtNormed]

/-- The diagonal entry $r_{kk}$ of `Matrix.gramSchmidtR A` is the norm of the Gram–Schmidt residual:
$r_{kk} = \|z_k\|_2$. -/
theorem gramSchmidtR_apply_self' (k : Fin N) :
    gramSchmidtR A k k = ‖WithLp.toLp 2 (gramSchmidtResidual A k)‖ := by
  rw [gramSchmidtR_apply_self, toLp_gramSchmidtResidual]

/-- For $A \in \mathbb{R}^{m \times N}$, the Gram–Schmidt triangular factor is $r_{ij} = q_i^T a_j$.
-/
theorem gramSchmidtR_apply_eq_dotProduct (A : Matrix m (Fin N) ℝ) (i j : Fin N) :
    gramSchmidtR A i j = (gramSchmidtQ A).col i ⬝ᵥ A.col j := by
  rw [gramSchmidtR_apply, star_trivial, dotProduct_comm]

/-- For $A \in \mathbb{R}^{m \times N}$, distinct columns of `Matrix.gramSchmidtQ A` are orthogonal:
$q_i^T q_j = 0$ for $i \neq j$. -/
theorem col_gramSchmidtQ_dotProduct_col (A : Matrix m (Fin N) ℝ) {i j : Fin N} (h : i ≠ j) :
    (gramSchmidtQ A).col i ⬝ᵥ (gramSchmidtQ A).col j = 0 := by
  rw [dotProduct_comm, ← col_gramSchmidtQ_dotProduct_star A h, star_trivial]

/-- For $A \in \mathbb{R}^{m \times N}$, $q_k = z_k / \sqrt{z_k^T z_k}$, where $z_k$ is the
Gram–Schmidt residual of column $k$. When $z_k = 0$, $q_k = 0$. -/
theorem col_gramSchmidtQ_eq_inv_sqrt_smul (A : Matrix m (Fin N) ℝ) (k : Fin N) :
    (gramSchmidtQ A).col k = (√(gramSchmidtResidual A k ⬝ᵥ gramSchmidtResidual A k))⁻¹ •
      gramSchmidtResidual A k := by
  rw [col_gramSchmidtQ, dotProduct_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  rfl

/-- For $A \in \mathbb{R}^{m \times N}$, $r_{kk} = \sqrt{z_k^T z_k}$, where $z_k$ is the
Gram–Schmidt residual of column $k$. -/
theorem gramSchmidtR_apply_self_eq_sqrt (A : Matrix m (Fin N) ℝ) (k : Fin N) :
    gramSchmidtR A k k = √(gramSchmidtResidual A k ⬝ᵥ gramSchmidtResidual A k) := by
  rw [gramSchmidtR_apply_self', dotProduct_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  rfl

variable {A}

omit [Fintype m] in
/-- Linearly independent columns of $A$ stay linearly independent as vectors of the Euclidean space
$\mathbb{K}^m$. -/
private theorem linearIndependent_toLp_col (hA : LinearIndependent 𝕜 Aᵀ) :
    LinearIndependent 𝕜 (fun j => WithLp.toLp 2 (A.col j) : Fin N → EuclideanSpace 𝕜 m) := by
  refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
  refine Fintype.linearIndependent_iff.1 hA g ?_ i
  funext r
  have h0 := congrArg (fun z : EuclideanSpace 𝕜 m => WithLp.ofLp z r) hg
  simpa using h0

/-- **The Gram–Schmidt factorization is a thin QR factorization** ([saad2003iterative], Algorithm
1.1; [golub2013matrix], Theorem 5.2.3). Let $A \in \mathbb{K}^{m \times N}$ have linearly
independent columns. Then `Matrix.gramSchmidtQ A` and `Matrix.gramSchmidtR A` form a thin QR
factorization of $A$. -/
theorem isThinQR_gramSchmidtQ (hA : LinearIndependent 𝕜 Aᵀ) :
    IsThinQR A (gramSchmidtQ A) (gramSchmidtR A) := by
  set f : Fin N → EuclideanSpace 𝕜 m := fun j => WithLp.toLp 2 (A.col j) with hf_def
  have hf : LinearIndependent 𝕜 f := linearIndependent_toLp_col hA
  have hon : Orthonormal 𝕜 (gramSchmidtNormed 𝕜 f) := gramSchmidtNormed_orthonormal hf
  have hexp : ∀ j : Fin N, f j = ∑ i : Fin N,
      inner 𝕜 (gramSchmidtNormed 𝕜 f i) (f j) • gramSchmidtNormed 𝕜 f i := by
    intro j
    have hsum : ∑ i : Fin N, inner 𝕜 (gramSchmidtNormed 𝕜 f i) (f j) • gramSchmidtNormed 𝕜 f i
        = ∑ i ∈ Finset.Iic j,
            inner 𝕜 (gramSchmidtNormed 𝕜 f i) (f j) • gramSchmidtNormed 𝕜 f i := by
      refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_).symm
      rw [show inner 𝕜 (gramSchmidtNormed 𝕜 f i) (f j) = gramSchmidtR A i j from rfl,
        gramSchmidtR_apply_of_lt A (by simpa using hi), zero_smul]
    have hdiagterm : inner 𝕜 (gramSchmidtNormed 𝕜 f j) (f j) • gramSchmidtNormed 𝕜 f j
        = gramSchmidt 𝕜 f j := by
      have hnne : ((‖gramSchmidt 𝕜 f j‖ : 𝕜)) ≠ 0 := by
        simpa using norm_ne_zero_iff.2 (gramSchmidt_ne_zero j hf)
      rw [inner_gramSchmidtNormed_self, gramSchmidtNormed, smul_smul,
        mul_inv_cancel₀ hnne, one_smul]
    rw [hsum, ← Finset.Iio_insert, Finset.sum_insert (by simp), hdiagterm,
      Finset.sum_congr rfl fun i _ => inner_gramSchmidtNormed_smul_self 𝕜 f i (f j)]
    exact gramSchmidt_def'' 𝕜 f j
  refine ⟨?_, ?_, fun i j hji => gramSchmidtR_apply_of_lt A hji⟩
  · ext r j
    have h : A r j = ∑ i : Fin N, inner 𝕜 (gramSchmidtNormed 𝕜 f i) (f j)
        * WithLp.ofLp (gramSchmidtNormed 𝕜 f i) r := by
      have h0 := congrArg (fun z : EuclideanSpace 𝕜 m => WithLp.ofLp z r) (hexp j)
      simpa [hf_def] using h0
    rw [Matrix.mul_apply, h]
    exact Finset.sum_congr rfl fun i _ => by
      rw [gramSchmidtQ, gramSchmidtR, Matrix.of_apply, Matrix.of_apply, mul_comm]
  · ext i j
    have h : ∑ r : m, starRingEnd 𝕜 (WithLp.ofLp (gramSchmidtNormed 𝕜 f i) r)
          * WithLp.ofLp (gramSchmidtNormed 𝕜 f j) r
        = inner 𝕜 (gramSchmidtNormed 𝕜 f i) (gramSchmidtNormed 𝕜 f j) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
      exact Finset.sum_congr rfl fun r _ => by simp [mul_comm]
    rw [Matrix.mul_apply]
    simp only [gramSchmidtQ, conjTranspose_apply, Matrix.of_apply, RCLike.star_def]
    rw [h, orthonormal_iff_ite.1 hon i j, Matrix.one_apply]

/-- Let $A \in \mathbb{K}^{m \times N}$ have linearly independent columns. Then every diagonal entry
$r_{jj}$ of the Gram–Schmidt triangular factor is real and positive.

Positive is the order of `ComplexOrder`. -/
theorem gramSchmidtR_apply_self_pos (hA : LinearIndependent 𝕜 Aᵀ) (j : Fin N) :
    0 < gramSchmidtR A j j := by
  rw [gramSchmidtR_apply_self]
  exact RCLike.pos_iff_exists_ofReal.2
    ⟨‖gramSchmidt 𝕜 (fun j => WithLp.toLp 2 (A.col j)) j‖,
      norm_pos_iff.2 (gramSchmidt_ne_zero j (linearIndependent_toLp_col hA)), rfl⟩

/-- **Existence of the thin QR factorization** ([saad2003iterative], (1.19); [golub2013matrix],
Theorem 5.2.3). Let $A \in \mathbb{K}^{m \times N}$ have linearly independent columns. Then
there are $Q \in \mathbb{K}^{m \times N}$ and $R \in \mathbb{K}^{N \times N}$ such that $(Q, R)$
is a thin QR factorization of $A$,
$$A = QR, \qquad Q^H Q = I, \qquad R \text{ upper triangular},$$
and every diagonal entry $r_{jj}$ is real and positive.

The factors are the Gram–Schmidt orthonormalization of the columns and the coefficients
$r_{ij} = \langle q_i, a_j \rangle$ (`Matrix.gramSchmidtQ`, `Matrix.gramSchmidtR`), which is
[saad2003iterative], Algorithm 1.1. Algorithm 1.2 (modified Gram–Schmidt) computes the same
pair, by `Matrix.IsThinQR.unique`. -/
theorem exists_isThinQR (A : Matrix m (Fin N) 𝕜) (hA : LinearIndependent 𝕜 Aᵀ) :
    ∃ Q R, IsThinQR A Q R ∧ ∀ j, 0 < R j j :=
  ⟨_, _, isThinQR_gramSchmidtQ hA, gramSchmidtR_apply_self_pos hA⟩

end GramSchmidt

/-! ### Leading and trailing blocks of columns and rows -/

section Blocks

variable {α : Type*} {m' n' : Type*} {M N K : ℕ}

/-- The first $N$ columns of a matrix $Q$ with $M \ge N$ columns: $Q(:, 0{:}N-1)$. This is the block
$\tilde Q = Q(1{:}m, 1{:}n)$ of [quarteroni2000numerical], (3.48), and the block $Q_1$ of
[golub2013matrix], (5.2.2). -/
def firstColumns (Q : Matrix m' (Fin M) α) (h : N ≤ M) : Matrix m' (Fin N) α :=
  Q.submatrix id (Fin.castLE h)

/-- The first $N$ rows of a matrix $R$ with $M \ge N$ rows: $R(0{:}N-1, :)$. This is the block
$\tilde R = R(1{:}n, 1{:}n)$ of [quarteroni2000numerical], (3.48). -/
def firstRows (R : Matrix (Fin M) n' α) (h : N ≤ M) : Matrix (Fin N) n' α :=
  R.submatrix (Fin.castLE h) id

/-- The last $K$ columns of a matrix $Q$ with $M \ge K$ columns: the columns $M - K, \dots, M - 1$.
For $K = M - N$ this is the block $Q_2 = Q(1{:}m, n{+}1{:}m)$ of [golub2013matrix], (5.2.2).
Together with `Matrix.firstColumns` it gives the two blocks of a split $M = N + K$ of the
columns. -/
def lastColumns (Q : Matrix m' (Fin M) α) (h : K ≤ M) : Matrix m' (Fin K) α :=
  Q.submatrix id fun j => ⟨M - K + j, by omega⟩

/-- The last $K$ rows of a matrix $R$ with $M \ge K$ rows: the rows $M - K, \dots, M - 1$. -/
def lastRows (R : Matrix (Fin M) n' α) (h : K ≤ M) : Matrix (Fin K) n' α :=
  R.submatrix (fun i => ⟨M - K + i, by omega⟩) id

/-- The entries of the first $N$ columns: the entry $(i, j)$ of `Matrix.firstColumns Q h` is
$q_{ij}$, for $j < N$. -/
@[simp]
theorem firstColumns_apply (Q : Matrix m' (Fin M) α) (h : N ≤ M) (i : m') (j : Fin N) :
    firstColumns Q h i j = Q i (Fin.castLE h j) := rfl

/-- The entries of the first $N$ rows: the entry $(i, j)$ of `Matrix.firstRows R h` is $r_{ij}$, for
$i < N$. -/
@[simp]
theorem firstRows_apply (R : Matrix (Fin M) n' α) (h : N ≤ M) (i : Fin N) (j : n') :
    firstRows R h i j = R (Fin.castLE h i) j := rfl

/-- The entries of the last $K$ columns: the entry $(i, j)$ of `Matrix.lastColumns Q h` is
$q_{i, M - K + j}$. -/
@[simp]
theorem lastColumns_apply (Q : Matrix m' (Fin M) α) (h : K ≤ M) (i : m') (j : Fin K) :
    lastColumns Q h i j = Q i ⟨M - K + j, by omega⟩ := rfl

/-- The entries of the last $K$ rows: the entry $(i, j)$ of `Matrix.lastRows R h` is
$r_{M - K + i, j}$. -/
@[simp]
theorem lastRows_apply (R : Matrix (Fin M) n' α) (h : K ≤ M) (i : Fin K) (j : n') :
    lastRows R h i j = R ⟨M - K + i, by omega⟩ j := rfl

/-- The last $K$ columns of $Q$ are $Q$ restricted to the columns $e(j)$, for any indexing $e$ with
$e(j) = M - K + j$. -/
theorem lastColumns_eq_submatrix (Q : Matrix m' (Fin M) α) (h : K ≤ M) {e : Fin K → Fin M}
    (he : ∀ j, (e j : ℕ) = M - K + j) : lastColumns Q h = Q.submatrix id e := by
  ext i j
  simp only [lastColumns_apply, submatrix_apply, id]
  congr 1
  exact Fin.ext (he j).symm

/-- The last $K$ of $N + K$ columns are the columns $N + j$, $j < K$. -/
theorem lastColumns_eq_submatrix_natAdd (Q : Matrix m' (Fin (N + K)) α) :
    lastColumns Q (Nat.le_add_left K N) = Q.submatrix id (Fin.natAdd N) :=
  lastColumns_eq_submatrix Q _ fun j => by simp

/-- The last $K$ of $N + K$ rows are the rows $N + i$, $i < K$. -/
theorem lastRows_eq_submatrix_natAdd (R : Matrix (Fin (N + K)) n' α) :
    lastRows R (Nat.le_add_left K N) = R.submatrix (Fin.natAdd N) id := by
  ext i j
  simp only [lastRows_apply, submatrix_apply, id]
  congr 1
  ext
  simp

/-- The transpose of the first $N$ columns of $Q$ is the first $N$ rows of $Q^T$. -/
theorem transpose_firstColumns (Q : Matrix m' (Fin M) α) (h : N ≤ M) :
    (firstColumns Q h)ᵀ = firstRows Qᵀ h := rfl

/-- The transpose of the last $K$ columns of $Q$ is the last $K$ rows of $Q^T$. -/
theorem transpose_lastColumns (Q : Matrix m' (Fin M) α) (h : K ≤ M) :
    (lastColumns Q h)ᵀ = lastRows Qᵀ h := rfl

/-- The transpose of the first $N$ rows of $R$ is the first $N$ columns of $R^T$. -/
theorem transpose_firstRows (R : Matrix (Fin M) n' α) (h : N ≤ M) :
    (firstRows R h)ᵀ = firstColumns Rᵀ h := rfl

/-- The transpose of the last $K$ rows of $R$ is the last $K$ columns of $R^T$. -/
theorem transpose_lastRows (R : Matrix (Fin M) n' α) (h : K ≤ M) :
    (lastRows R h)ᵀ = lastColumns Rᵀ h := rfl

section Star

variable [Star α]

/-- The conjugate transpose of the first $N$ columns of $Q$ is the first $N$ rows of $Q^H$. -/
theorem conjTranspose_firstColumns (Q : Matrix m' (Fin M) α) (h : N ≤ M) :
    (firstColumns Q h)ᴴ = firstRows Qᴴ h := rfl

/-- The conjugate transpose of the last $K$ columns of $Q$ is the last $K$ rows of $Q^H$. -/
theorem conjTranspose_lastColumns (Q : Matrix m' (Fin M) α) (h : K ≤ M) :
    (lastColumns Q h)ᴴ = lastRows Qᴴ h := rfl

/-- The conjugate transpose of the first $N$ rows of $R$ is the first $N$ columns of $R^H$. -/
theorem conjTranspose_firstRows (R : Matrix (Fin M) n' α) (h : N ≤ M) :
    (firstRows R h)ᴴ = firstColumns Rᴴ h := rfl

/-- The conjugate transpose of the last $K$ rows of $R$ is the last $K$ columns of $R^H$. -/
theorem conjTranspose_lastRows (R : Matrix (Fin M) n' α) (h : K ≤ M) :
    (lastRows R h)ᴴ = lastColumns Rᴴ h := rfl

end Star

/-- **A product in block form.** Let $X$ have $M$ columns, let $Y$ have $M$ rows, and let
$M = N + K$. Split the inner index into its first $N$ and its last $K$ values. Then
$$XY = X(:, 0{:}N-1)\, Y(0{:}N-1, :) + X(:, N{:}M-1)\, Y(N{:}M-1, :).$$
-/
theorem firstColumns_mul_firstRows_add_lastColumns_mul_lastRows [NonUnitalNonAssocSemiring α]
    (X : Matrix m' (Fin M) α) (Y : Matrix (Fin M) n' α) (hN : N ≤ M) (hK : K ≤ M)
    (hNK : N + K = M) :
    firstColumns X hN * firstRows Y hN + lastColumns X hK * lastRows Y hK = X * Y := by
  subst hNK
  ext i j
  have e : ∀ k : Fin K, (⟨N + K - K + k, by omega⟩ : Fin (N + K)) = Fin.natAdd N k :=
    fun k => Fin.ext (by simp)
  simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_add, firstColumns_apply,
    firstRows_apply, lastColumns_apply, lastRows_apply, e]
  rfl

variable [Fintype m'] {Q : Matrix m' (Fin M) 𝕜}

/-- Let $Q \in \mathbb{K}^{m \times M}$ have orthonormal columns, $Q^H Q = I$, and let $N \le M$.
Then the first $N$ columns of $Q$ are orthonormal. -/
theorem conjTranspose_firstColumns_mul_firstColumns (hQ : Qᴴ * Q = 1) (h : N ≤ M) :
    (firstColumns Q h)ᴴ * firstColumns Q h = 1 := by
  ext i j
  have := congrFun (congrFun hQ (Fin.castLE h i)) (Fin.castLE h j)
  simp only [Matrix.mul_apply, conjTranspose_apply] at this
  simp only [Matrix.mul_apply, conjTranspose_apply, firstColumns_apply, this, Matrix.one_apply,
      Fin.castLE_inj]

/-- Let $Q \in \mathbb{K}^{m \times M}$ have orthonormal columns, $Q^H Q = I$, and let $K \le M$.
Then the last $K$ columns of $Q$ are orthonormal. -/
theorem conjTranspose_lastColumns_mul_lastColumns (hQ : Qᴴ * Q = 1) (h : K ≤ M) :
    (lastColumns Q h)ᴴ * lastColumns Q h = 1 := by
  ext i j
  have := congrFun (congrFun hQ ⟨M - K + i, by omega⟩) ⟨M - K + j, by omega⟩
  simp only [Matrix.mul_apply, conjTranspose_apply] at this
  simp only [Matrix.mul_apply, conjTranspose_apply, lastColumns_apply, this, Matrix.one_apply,
    Fin.mk.injEq, Nat.add_left_cancel_iff, Fin.val_inj]

/-- Let $Q \in \mathbb{K}^{m \times M}$ have orthonormal columns, and let $N + K \le M$. Then the
last $K$ columns $Q_2$ and the first $N$ columns $Q_1$ of $Q$ are orthogonal to each other:
$Q_2^H Q_1 = 0$. -/
theorem conjTranspose_lastColumns_mul_firstColumns (hQ : Qᴴ * Q = 1) (hN : N ≤ M) (hK : K ≤ M)
    (hNK : N + K ≤ M) : (lastColumns Q hK)ᴴ * firstColumns Q hN = 0 := by
  ext a b
  have := congrFun (congrFun hQ ⟨M - K + a, by omega⟩) (Fin.castLE hN b)
  rw [one_apply_ne fun he => by
    have := congrArg Fin.val he
    simp only [Fin.val_castLE] at this
    omega] at this
  simpa only [Matrix.mul_apply, conjTranspose_apply, lastColumns_apply, firstColumns_apply,
    Matrix.zero_apply] using this

/-- Let $Q \in \mathbb{K}^{m \times M}$ have orthonormal columns, and let $N + K \le M$. Then the
first $N$ columns $Q_1$ and the last $K$ columns $Q_2$ of $Q$ are orthogonal to each other:
$Q_1^H Q_2 = 0$. -/
theorem conjTranspose_firstColumns_mul_lastColumns (hQ : Qᴴ * Q = 1) (hN : N ≤ M) (hK : K ≤ M)
    (hNK : N + K ≤ M) : (firstColumns Q hN)ᴴ * lastColumns Q hK = 0 := by
  have := congrArg conjTranspose (conjTranspose_lastColumns_mul_firstColumns hQ hN hK hNK)
  rwa [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_zero] at this

/-- **The column blocks of a unitary matrix resolve the identity.** Let
$Q \in \mathbb{K}^{M \times M}$ be unitary, and let $M = N + K$. Let $Q_1$ be the first $N$ and
$Q_2$ the last $K$ columns of $Q$. Then
$$Q_1 Q_1^H + Q_2 Q_2^H = I.$$
-/
theorem firstColumns_mul_conjTranspose_add_lastColumns_mul_conjTranspose
    {Q : Matrix (Fin M) (Fin M) 𝕜} (hQ : Q ∈ unitaryGroup (Fin M) 𝕜) (hN : N ≤ M) (hK : K ≤ M)
    (hNK : N + K = M) :
    firstColumns Q hN * (firstColumns Q hN)ᴴ + lastColumns Q hK * (lastColumns Q hK)ᴴ = 1 := by
  rw [conjTranspose_firstColumns, conjTranspose_lastColumns,
    firstColumns_mul_firstRows_add_lastColumns_mul_lastRows Q Qᴴ hN hK hNK,
    ← star_eq_conjTranspose, Unitary.mul_star_self_of_mem hQ]

end Blocks

/-! ### The full QR factorization and its reduced form -/

section FullQR

variable {M N : ℕ}

/-- **The full QR factorization** ([quarteroni2000numerical], Definition 3.1). Let
$A \in \mathbb{K}^{M \times N}$, $Q \in \mathbb{K}^{M \times M}$ and
$R \in \mathbb{K}^{M \times N}$. The pair $(Q, R)$ is a **QR factorization** of $A$ if $Q$ is
unitary, $R$ is upper trapezoidal, that is, $r_{ij} = 0$ for $j < i$, and
$$A = QR.$$

When $N \le M$, the rows of $R$ from the $N$-th on vanish. Upper trapezoidal is lower bandwidth
$0$, `Matrix.HasLowerBandwidthRect R 0`. -/
structure IsQR (A : Matrix (Fin M) (Fin N) 𝕜) (Q : Matrix (Fin M) (Fin M) 𝕜)
    (R : Matrix (Fin M) (Fin N) 𝕜) : Prop where
  /-- The factor $Q$ is unitary. -/
  mem_unitaryGroup : Q ∈ Matrix.unitaryGroup (Fin M) 𝕜
  /-- The factor $R$ is upper trapezoidal: it vanishes below the diagonal. -/
  hasLowerBandwidthRect : R.HasLowerBandwidthRect 0
  /-- The factors multiply to $A$: $QR = A$. -/
  mul_eq : Q * R = A

/-- **Every matrix has a full QR factorization.** Let $A \in \mathbb{K}^{M \times N}$. Then $A$ has
a QR factorization $A = QR$.

By `Matrix.exists_unitary_mul_upperTriangular` there is a unitary $P$ with $PA = R$ upper
trapezoidal, and then $A = P^H R$. -/
theorem exists_isQR (A : Matrix (Fin M) (Fin N) 𝕜) : ∃ Q R, IsQR A Q R := by
  obtain ⟨P, hP, hPA⟩ := exists_unitary_mul_upperTriangular A
  refine ⟨star P, P * A, Unitary.star_mem hP, fun i j hij => hPA i j (by simpa using hij), ?_⟩
  rw [← Matrix.mul_assoc, Unitary.star_mul_self_of_mem hP, Matrix.one_mul]

variable {A : Matrix (Fin M) (Fin N) 𝕜} {Q : Matrix (Fin M) (Fin M) 𝕜}
variable {R : Matrix (Fin M) (Fin N) 𝕜}

/-- If $(Q, R)$ is a QR factorization of $A$, then $r_{ij} = 0$ for $j < i$. -/
theorem IsQR.apply_eq_zero (h : IsQR A Q R) (i : Fin M) (j : Fin N) (hij : (j : ℕ) < i) :
    R i j = 0 :=
  h.hasLowerBandwidthRect i j (by simpa using hij)

/-- Let $(Q, R)$ be a QR factorization of $A \in \mathbb{K}^{M \times N}$. Then the rows of $R$ from
the $N$-th on vanish: $r_{ij} = 0$ for $i \ge N$. -/
theorem IsQR.apply_eq_zero_of_le (h : IsQR A Q R) {i : Fin M} (hi : N ≤ i) (j : Fin N) :
    R i j = 0 :=
  h.apply_eq_zero i j (j.2.trans_le hi)

/-- Let $(Q, R)$ be a QR factorization of $A \in \mathbb{K}^{M \times N}$ with $N \le M$. Then the
last $M - N$ rows of $R$ vanish. -/
theorem IsQR.lastRows_eq_zero (h : IsQR A Q R) (hNM : N ≤ M) :
    lastRows R (Nat.sub_le M N) = 0 := by
  ext i j
  exact h.apply_eq_zero_of_le (show N ≤ M - (M - N) + (i : ℕ) by omega) j

/-- Let $(Q, R)$ be a QR factorization of $A \in \mathbb{K}^{M \times N}$ with $N \le M$, let
$\tilde Q$ be the first $N$ columns of $Q$ and $\tilde R$ the first $N$ rows of $R$. Then
$\tilde Q \tilde R = A$. This is (3.47) of [quarteroni2000numerical].

The trailing rows of $R$ are zero, so only the first $N$ columns of $Q$ contribute to $QR$. -/
theorem IsQR.firstColumns_mul_firstRows (h : IsQR A Q R) (hNM : N ≤ M) :
    firstColumns Q hNM * firstRows R hNM = A := by
  rw [← h.mul_eq, ← firstColumns_mul_firstRows_add_lastColumns_mul_lastRows Q R hNM
    (Nat.sub_le M N) (by omega), h.lastRows_eq_zero hNM, Matrix.mul_zero, add_zero]

/-- Let $(Q, R)$ be a QR factorization of $A \in \mathbb{K}^{M \times N}$ with $N \le M$, and let
$\tilde Q$ be the first $N$ columns of $Q$. Then $\tilde Q$ has orthonormal columns,
$\tilde Q^H \tilde Q = I$, being a block of $Q^H Q = I$. -/
theorem IsQR.conjTranspose_firstColumns_mul_self (h : IsQR A Q R) (hNM : N ≤ M) :
    (firstColumns Q hNM)ᴴ * firstColumns Q hNM = 1 :=
  conjTranspose_firstColumns_mul_firstColumns
    (by rw [← star_eq_conjTranspose]; exact Unitary.star_mul_self_of_mem h.mem_unitaryGroup) hNM

/-- Let $(Q, R)$ be a QR factorization of $A \in \mathbb{K}^{M \times N}$ with $N \le M$. Then the
first $N$ rows $\tilde R$ of $R$ form an upper triangular matrix. -/
theorem IsQR.isUpperTriangular_firstRows (h : IsQR A Q R) (hNM : N ≤ M) :
    (firstRows R hNM).IsUpperTriangular := fun _ _ hij =>
  h.apply_eq_zero _ _ hij

/-- **The reduced QR factorization** ([quarteroni2000numerical], Property 3.3 and (3.47)–(3.48);
[golub2013matrix], (5.2.2)). Let $(Q, R)$ be a QR factorization of
$A \in \mathbb{K}^{M \times N}$ with $N \le M$. Let $\tilde Q$ be the first $N$ columns of $Q$
and $\tilde R$ the first $N$ rows of $R$. Then $(\tilde Q, \tilde R)$ is a thin QR factorization
of $A$:
$$A = \tilde Q \tilde R, \qquad \tilde Q^H \tilde Q = I,$$
and $\tilde R$ is upper triangular.

Property 3.3 also claims uniqueness. Uniqueness holds only with a normalization of the diagonal
of $\tilde R$, such as a positive diagonal (`Matrix.IsThinQR.unique`). -/
theorem IsQR.isThinQR (h : IsQR A Q R) (hNM : N ≤ M) :
    IsThinQR A (firstColumns Q hNM) (firstRows R hNM) :=
  ⟨h.firstColumns_mul_firstRows hNM, h.conjTranspose_firstColumns_mul_self hNM,
    h.isUpperTriangular_firstRows hNM⟩

/-- Let $(Q, R)$ be a QR factorization of $A \in \mathbb{K}^{M \times N}$ with $N \le M$, and let
the columns of $A$ be linearly independent. Then the first $N$ rows $\tilde R$ of $R$ form an
invertible matrix.

The map $x \mapsto Ax = \tilde Q \tilde R x$ is injective, so $x \mapsto \tilde R x$ is
injective. -/
theorem IsQR.isUnit_firstRows_of_linearIndependent (h : IsQR A Q R) (hNM : N ≤ M)
    (hA : LinearIndependent 𝕜 Aᵀ) : IsUnit (firstRows R hNM) :=
  (h.isThinQR hNM).isUnit_of_linearIndependent hA

/-- Let $(Q, R)$ be a QR factorization of $A \in \mathbb{K}^{M \times N}$ with $N \le M$, and let
the columns of $A$ be linearly independent. Then the diagonal entries $r_{ii}$, $i < N$, are
nonzero. -/
theorem IsQR.firstRows_diag_ne_zero_of_linearIndependent (h : IsQR A Q R) (hNM : N ≤ M)
    (hA : LinearIndependent 𝕜 Aᵀ) (i : Fin N) : firstRows R hNM i i ≠ 0 :=
  (h.isUpperTriangular_firstRows hNM).isUnit_iff.1
    (h.isUnit_firstRows_of_linearIndependent hNM hA) i

/-- [quarteroni2000numerical], Property 3.3, the statement on the range. Let $(Q, R)$ be a QR
factorization of $A \in \mathbb{K}^{M \times N}$ with $N \le M$, and let the columns of $A$ be
linearly independent. Then the first $N$ columns of $Q$ span the column space of $A$.

The proof uses $A = \tilde Q \tilde R$ with $\tilde R$ invertible. -/
theorem IsQR.span_firstColumns_eq (h : IsQR A Q R) (hNM : N ≤ M) (hA : LinearIndependent 𝕜 Aᵀ) :
    Submodule.span 𝕜 (Set.range (firstColumns Q hNM)ᵀ) = Submodule.span 𝕜 (Set.range Aᵀ) := by
  have hR := h.isUnit_firstRows_of_linearIndependent hNM hA
  rw [show Set.range Aᵀ = Set.range A.col from rfl,
    show Set.range (firstColumns Q hNM)ᵀ = Set.range (firstColumns Q hNM).col from rfl,
    ← range_mulVecLin, ← range_mulVecLin, ← h.firstColumns_mul_firstRows hNM,
    mulVecLin_mul, LinearMap.range_comp_of_range_eq_top]
  exact LinearMap.range_eq_top.2 (mulVec_surjective_iff_isUnit.2 hR)

/-- If $(Q, R)$ is a QR factorization of $A$, then $R = Q^H A$. -/
theorem IsQR.conjTranspose_mul_eq (h : IsQR A Q R) : Qᴴ * A = R := by
  rw [← h.mul_eq, ← Matrix.mul_assoc, ← star_eq_conjTranspose,
    Unitary.star_mul_self_of_mem h.mem_unitaryGroup, Matrix.one_mul]

/-- Let $A \in \mathbb{K}^{M \times N}$, and let $Q \in \mathbb{K}^{M \times M}$ be unitary with
$Q^H A$ upper trapezoidal. Then $(Q, Q^H A)$ is a QR factorization of $A$. -/
theorem isQR_conjTranspose_mul (hQ : Q ∈ unitaryGroup (Fin M) 𝕜)
    (hR : (Qᴴ * A).HasLowerBandwidthRect 0) : IsQR A Q (Qᴴ * A) :=
  ⟨hQ, hR, by
    rw [← Matrix.mul_assoc, ← star_eq_conjTranspose, Unitary.mul_star_self_of_mem hQ,
      Matrix.one_mul]⟩

/-- **The leading columns of $A$ and $Q$ span the same subspaces** ([golub2013matrix], (5.2.1)). Let
$(Q, R)$ be a QR factorization of $A \in \mathbb{K}^{M \times N}$ with $N \le M$, and let the
columns of $A$ be linearly independent. Then for every $k \le N$,
$$\operatorname{span}\{a_0, \dots, a_{k-1}\} = \operatorname{span}\{q_0, \dots, q_{k-1}\},$$
and the diagonal entries $r_{jj}$ of $R$ are nonzero.

The inclusion follows from $a_j = \sum_{i \le j} r_{ij} q_i$, (5.2.3) of the source; equality
follows from a count of dimensions. -/
theorem IsQR.span_col_prefix_eq (h : IsQR A Q R) (hA : LinearIndependent 𝕜 Aᵀ) (hNM : N ≤ M)
    {k : ℕ} (hk : k ≤ N) :
    Submodule.span 𝕜 (Set.range fun j : Fin k => A.col (Fin.castLE hk j)) =
        Submodule.span 𝕜 (Set.range fun i : Fin k => Q.col (Fin.castLE (hk.trans hNM) i)) ∧
      ∀ (i : Fin M) (j : Fin N), (i : ℕ) = j → R i j ≠ 0 := by
  refine ⟨Submodule.eq_of_le_of_finrank_le ?_ ?_, fun i j hij => ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨c, rfl⟩
    have hcol : A.col (Fin.castLE hk c) = ∑ i : Fin M, R i (Fin.castLE hk c) • Q.col i := by
      funext r
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      change A r _ = ∑ i, R i _ * Q r i
      rw [← h.mul_eq, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    change A.col (Fin.castLE hk c) ∈ _
    rw [hcol]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : (i : ℕ) < k
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi⟩, congrArg _ (Fin.ext rfl)⟩)
    · rw [h.apply_eq_zero i _ (by simp only [Fin.val_castLE]; omega), zero_smul]
      exact Submodule.zero_mem _
  · have hli : LinearIndependent 𝕜 fun j : Fin k => A.col (Fin.castLE hk j) :=
      hA.comp _ (Fin.castLE_injective hk)
    rw [finrank_span_eq_card hli]
    exact (finrank_range_le_card _).trans (by simp)
  · have := h.firstRows_diag_ne_zero_of_linearIndependent hNM hA j
    rwa [firstRows_apply, show Fin.castLE hNM j = i from Fin.ext hij.symm] at this

/-- **QR factorization with column pivoting** ([golub2013matrix], §5.4.2). Let
$A \in \mathbb{K}^{M \times N}$, $Q \in \mathbb{K}^{M \times M}$,
$R \in \mathbb{K}^{M \times N}$, and let $\sigma$ be a permutation of the columns. The triple
$(Q, R, \sigma)$ is a **pivoted QR factorization** of $A$ if $(Q, R)$ is a QR factorization of
$A \Pi$, where $\Pi$ is the permutation matrix of $\sigma$:
$$A \Pi = QR.$$
Column $k$ of $A \Pi$ is column $\sigma(k)$ of $A$.

It is a structure rather than an abbreviation, so that rank-revealing refinements can use dot
notation on it. -/
structure IsPivotedQR (A : Matrix (Fin M) (Fin N) 𝕜) (Q : Matrix (Fin M) (Fin M) 𝕜)
    (R : Matrix (Fin M) (Fin N) 𝕜) (σ : Equiv.Perm (Fin N)) : Prop where
  /-- The matrix $A \Pi$, whose column $k$ is column $\sigma(k)$ of $A$, has the QR factorization
  $(Q, R)$. -/
  isQR : IsQR (A.submatrix id σ) Q R

end FullQR

/-! ### The projector of modified Gram–Schmidt -/

section GramSchmidtProjector

variable {R : Type*} [CommRing R] [StarRing R]

/-- **The projector identity behind modified Gram–Schmidt** ([golub2013matrix], §5.2.8). Let $R$ be
a commutative ring with a star operation, let $k \in \mathbb{N}$, and let
$q_0, q_1, \dots \in R^n$ satisfy $q_i^H q_j = 0$ for $i < j < k$. Then
$$(I - q_0 q_0^H)(I - q_1 q_1^H) \cdots (I - q_{k-1} q_{k-1}^H) = I - \sum_{i < k} q_i q_i^H.$$

The cross terms of the product vanish (`prodFwd_eq_one_add_sum_sub_one`). The $q_i$ need not
have unit length. So in exact arithmetic the successive deflations of modified Gram–Schmidt
compute the vectors $a - \sum_i (q_i^H a)\, q_i$ of classical Gram–Schmidt. The product is
`prodFwd`, with each new factor on the right. -/
theorem prodFwd_one_sub_vecMulVec_of_orthogonal (q : ℕ → n → R) {k : ℕ}
    (hq : ∀ i j, i < j → j < k → star (q i) ⬝ᵥ q j = 0) :
    prodFwd (fun i => 1 - vecMulVec (q i) (star (q i))) k =
      1 - ∑ i ∈ Finset.range k, vecMulVec (q i) (star (q i)) := by
  have h : ∀ i j, i < j → j < k → (1 - vecMulVec (q i) (star (q i)) - 1) *
      (1 - vecMulVec (q j) (star (q j)) - 1) = 0 := fun i j hij hj => by
    rw [sub_sub_cancel_left, sub_sub_cancel_left, neg_mul_neg, vecMulVec_mul_vecMulVec,
      hq i j hij hj, zero_smul, vecMulVec_zero]
  rw [prodFwd_eq_one_add_sum_sub_one h]
  simp only [sub_sub_cancel_left, Finset.sum_neg_distrib, ← sub_eq_add_neg]

end GramSchmidtProjector

/-! ### Reduction to Hessenberg form by Householder reflectors -/

section HessenbergReduction

variable {N : ℕ}

/-- The reflector of step $k$ of the Householder reduction to Hessenberg form. For $k < N$ it is the
reflector of the tail axis of column $k$ of $A$ at the pivot $k + 1$. For $k \ge N$ it is the
identity.

This is the matrix $P_{(k)}$ of [quarteroni2000numerical], (5.41), with $x$ the $k$-th column of
$A^{(k-1)}$. -/
noncomputable def hessenbergReflector (A : Matrix (Fin N) (Fin N) 𝕜) (k : ℕ) :
    Matrix (Fin N) (Fin N) 𝕜 :=
  if h : k < N then householder (householderTail (fun i => A i ⟨k, h⟩) (k + 1)) else 1

variable (A : Matrix (Fin N) (Fin N) 𝕜) {k : ℕ}

/-- For $k < N$, the reflector of step $k$ is the reflector of the tail axis of column $k$ of $A$ at
the pivot $k + 1$. -/
theorem hessenbergReflector_of_lt (h : k < N) :
    hessenbergReflector A k = householder (householderTail (fun i => A i ⟨k, h⟩) (k + 1)) :=
  dite_eq_left h

/-- For $k \ge N$, the reflector of step $k$ is the identity. -/
theorem hessenbergReflector_of_le (h : N ≤ k) : hessenbergReflector A k = 1 :=
  dite_eq_right (not_lt.2 h)

/-- The reflector of step $k$ of the Householder reduction is Hermitian, for every $k$. -/
theorem isHermitian_hessenbergReflector (k : ℕ) : (hessenbergReflector A k).IsHermitian := by
  unfold hessenbergReflector
  split_ifs
  · exact isHermitian_householder _
  · exact isHermitian_one

/-- The reflector of step $k$ of the Householder reduction is unitary, for every $k$. -/
theorem hessenbergReflector_mem_unitaryGroup (k : ℕ) :
    hessenbergReflector A k ∈ Matrix.unitaryGroup (Fin N) 𝕜 := by
  unfold hessenbergReflector
  split_ifs
  · exact householder_householderTail_mem_unitaryGroup _ _
  · exact one_mem _

/-- [quarteroni2000numerical], (5.45). One step of the Householder reduction to Hessenberg form:
with $P$ the reflector of step $k$ for $A$,
$$\operatorname{step}_k(A) = P A P.$$

This is the step $A^{(k)} = P_{(k)}^T A^{(k-1)} P_{(k)}$ of the source. The reflector is
Hermitian, so $P^H A P = P A P$. -/
noncomputable def hessenbergStep (A : Matrix (Fin N) (Fin N) 𝕜) (k : ℕ) :
    Matrix (Fin N) (Fin N) 𝕜 :=
  hessenbergReflector A k * A * hessenbergReflector A k

/-- The matrices $A^{(k)}$ of the Householder reduction to Hessenberg form: $A^{(0)} = A$, and
$A^{(k+1)}$ is step $k$ applied to $A^{(k)}$. -/
noncomputable def hessenbergIter (A : Matrix (Fin N) (Fin N) 𝕜) : ℕ → Matrix (Fin N) (Fin N) 𝕜
  | 0 => A
  | k + 1 => hessenbergStep (hessenbergIter A k) k

/-- The accumulated product $Q_{(k)} = P_{(0)} P_{(1)} \cdots P_{(k-1)}$ of the reflectors of the
Householder reduction, where $P_{(j)}$ is the reflector of step $j$ for $A^{(j)}$. So
$Q_{(0)} = I$. -/
noncomputable def hessenbergQIter (A : Matrix (Fin N) (Fin N) 𝕜) : ℕ → Matrix (Fin N) (Fin N) 𝕜
  | 0 => 1
  | k + 1 => hessenbergQIter A k * hessenbergReflector (hessenbergIter A k) k

/-- **The Householder reduction to Hessenberg form** ([quarteroni2000numerical], §5.6.2, Program
29). For $A \in \mathbb{K}^{N \times N}$ it is the matrix $H = A^{(N-2)}$ after the $N - 2$
similarity steps of `Matrix.hessenbergStep`.

For $N \le 2$ no step is made, and $H = A$, because $N - 2$ is truncated subtraction in `ℕ`. -/
noncomputable def hessenbergReduce (A : Matrix (Fin N) (Fin N) 𝕜) : Matrix (Fin N) (Fin N) 𝕜 :=
  hessenbergIter A (N - 2)

/-- The unitary matrix $Q = P_{(0)} \cdots P_{(N-3)}$ of the Householder reduction to Hessenberg
form, so that $H = Q^H A Q$ (`Matrix.hessenbergReduce_eq_conj`). For $N \le 2$, $Q = I$. -/
noncomputable def hessenbergQ (A : Matrix (Fin N) (Fin N) 𝕜) : Matrix (Fin N) (Fin N) 𝕜 :=
  hessenbergQIter A (N - 2)

/-- The Householder reduction starts at $A$: $A^{(0)} = A$. -/
@[simp]
theorem hessenbergIter_zero : hessenbergIter A 0 = A := rfl

/-- One step of the Householder reduction: $A^{(k+1)}$ is step $k$ applied to $A^{(k)}$. -/
theorem hessenbergIter_succ (k : ℕ) :
    hessenbergIter A (k + 1) = hessenbergStep (hessenbergIter A k) k := rfl

/-- The accumulated reflector product starts at the identity: $Q_{(0)} = I$. -/
@[simp]
theorem hessenbergQIter_zero : hessenbergQIter A 0 = 1 := rfl

/-- One step of the accumulated reflector product: $Q_{(k+1)} = Q_{(k)} P_{(k)}$, where $P_{(k)}$ is
the reflector of step $k$ for $A^{(k)}$. -/
theorem hessenbergQIter_succ (k : ℕ) :
    hessenbergQIter A (k + 1) =
      hessenbergQIter A k * hessenbergReflector (hessenbergIter A k) k := rfl

/-- The accumulated reflector product $Q_{(k)}$ is unitary, for every $k$. -/
theorem hessenbergQIter_mem_unitaryGroup (k : ℕ) :
    hessenbergQIter A k ∈ Matrix.unitaryGroup (Fin N) 𝕜 := by
  induction k with
  | zero => exact one_mem _
  | succ k ih => exact mul_mem ih (hessenbergReflector_mem_unitaryGroup _ _)

/-- [quarteroni2000numerical], (5.45). For every $k$, $A^{(k)} = Q_{(k)}^H A\, Q_{(k)}$. -/
theorem hessenbergIter_eq_conj (k : ℕ) :
    hessenbergIter A k = (hessenbergQIter A k)ᴴ * A * hessenbergQIter A k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [hessenbergIter_succ, hessenbergStep, hessenbergQIter_succ, conjTranspose_mul,
      (isHermitian_hessenbergReflector _ _).eq, ih]
    simp only [Matrix.mul_assoc]

/-- The matrix $Q$ of the Householder reduction to Hessenberg form is unitary. -/
theorem hessenbergQ_mem_unitaryGroup : hessenbergQ A ∈ Matrix.unitaryGroup (Fin N) 𝕜 :=
  hessenbergQIter_mem_unitaryGroup A _

/-- For $A \in \mathbb{R}^{N \times N}$, the matrix $Q$ of the Householder reduction to Hessenberg
form is orthogonal. -/
theorem hessenbergQ_mem_orthogonalGroup (A : Matrix (Fin N) (Fin N) ℝ) :
    hessenbergQ A ∈ Matrix.orthogonalGroup (Fin N) ℝ :=
  hessenbergQ_mem_unitaryGroup A

/-- [quarteroni2000numerical], (5.45). The Householder reduction to Hessenberg form is a unitary
similarity:
$$H = Q^H A Q.$$
-/
theorem hessenbergReduce_eq_conj : hessenbergReduce A = (hessenbergQ A)ᴴ * A * hessenbergQ A :=
  hessenbergIter_eq_conj A _

/-- Let $B$ be a square matrix of order $M + 1$ and $k \in \mathbb{N}$. Then the first column of the
accumulated reflector product $Q_{(k)}$ of $B$ is $e_0$: $(Q_{(k)})_{i0} = \delta_{i0}$.

Every reflector of the reduction is the identity or a tail reflector with pivot at least $1$.
Its axis vanishes at $0$, and right multiplication by such a reflector keeps column $0$
(`Matrix.mul_householder_apply_of_apply_eq_zero`). -/
theorem hessenbergQIter_apply_zero {M : ℕ} (B : Matrix (Fin (M + 1)) (Fin (M + 1)) 𝕜) (k : ℕ)
    (i : Fin (M + 1)) :
    hessenbergQIter B k i 0 = (1 : Matrix (Fin (M + 1)) (Fin (M + 1)) 𝕜) i 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [hessenbergQIter_succ]
    by_cases hk : k < M + 1
    · rw [hessenbergReflector_of_lt _ hk,
        mul_householder_apply_of_apply_eq_zero
          (householderTail_apply_of_lt (p := k + 1) (i := (0 : Fin (M + 1))) _ (by simp)), ih]
    · rw [hessenbergReflector_of_le _ (not_lt.1 hk), Matrix.mul_one, ih]

/-- **The Householder reduction fixes $e_0$** ([golub2013matrix], §8.4.6, Step 2:
"$Q_1(:, 1) = e_1$, observed from the implementation"). Let $B$ be a square matrix of order
$M + 1$, and let $Q$ be the unitary matrix of its reduction $Q^H B Q = H$. Then the first column
of $Q$ is the first coordinate vector: $q_{i0} = \delta_{i0}$.

So a unitary $W$ and $Q^H W$ have the same first row. -/
theorem hessenbergQ_apply_zero {M : ℕ} (B : Matrix (Fin (M + 1)) (Fin (M + 1)) 𝕜)
    (i : Fin (M + 1)) : hessenbergQ B i 0 = (1 : Matrix (Fin (M + 1)) (Fin (M + 1)) 𝕜) i 0 :=
  hessenbergQIter_apply_zero B _ i

/-- The invariant of the Householder reduction: if $B$ vanishes below the first subdiagonal in the
columns $j < k$, then so does step $k$ applied to $B$ in the columns $j < k + 1$. -/
private theorem hessenbergStep_apply_eq_zero {B : Matrix (Fin N) (Fin N) 𝕜} {k : ℕ}
    (hB : ∀ i j : Fin N, (j : ℕ) < k → (j : ℕ) + 1 < (i : ℕ) → B i j = 0) (i j : Fin N)
    (hj : (j : ℕ) < k + 1) (hij : (j : ℕ) + 1 < (i : ℕ)) : hessenbergStep B k i j = 0 := by
  by_cases hk : k < N
  swap
  · rw [hessenbergStep, hessenbergReflector_of_le B (not_lt.1 hk), one_mul, mul_one]
    exact hB i j (by omega) hij
  rw [hessenbergStep, hessenbergReflector_of_lt B hk,
    mul_householder_apply_of_apply_eq_zero (householderTail_apply_of_lt _ (by omega)),
    householder_mul_apply]
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hjk | hjk
  · rw [householder_mulVec_eq_self_of_apply_eq_zero fun r hr => hB r j hjk ?_]
    · exact hB i j hjk hij
    · by_contra hcon
      exact hr (householderTail_apply_of_lt _ (by omega))
  · have hjκ : j = ⟨k, hk⟩ := Fin.ext hjk
    subst hjκ
    exact householder_householderTail_mulVec_apply_of_gt _ hij

/-- Let $A \in \mathbb{K}^{N \times N}$ and $k \in \mathbb{N}$. Then $A^{(k)}$ vanishes below the
first subdiagonal in the columns $j < k$: $A^{(k)}_{ij} = 0$ whenever $j < k$ and $j + 1 < i$. -/
theorem hessenbergIter_apply_eq_zero (k : ℕ) (i j : Fin N) (hj : (j : ℕ) < k)
    (hij : (j : ℕ) + 1 < (i : ℕ)) : hessenbergIter A k i j = 0 := by
  induction k generalizing i j with
  | zero => exact absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
    rw [hessenbergIter_succ]
    exact hessenbergStep_apply_eq_zero (fun i j => ih i j) i j hj hij

/-- **The Householder reduction produces an upper Hessenberg matrix** ([quarteroni2000numerical],
§5.6.2). For every $A \in \mathbb{K}^{N \times N}$, the matrix $H = A^{(N-2)}$ is upper
Hessenberg: $h_{ij} = 0$ whenever $j + 1 < i$. -/
theorem isUpperHessenberg_hessenbergReduce : (hessenbergReduce A).IsUpperHessenberg := by
  rw [isUpperHessenberg_iff_fin]
  intro i j hij
  exact hessenbergIter_apply_eq_zero A (N - 2) i j (by omega) hij

/-- Let $A \in \mathbb{K}^{N \times N}$ be Hermitian. Then the Householder reduction $H$ of $A$ is
Hermitian, because it is a unitary conjugate of $A$ ([quarteroni2000numerical], Remark 5.4). -/
theorem isHermitian_hessenbergReduce (hA : A.IsHermitian) : (hessenbergReduce A).IsHermitian := by
  rw [hessenbergReduce_eq_conj]
  exact isHermitian_conjTranspose_mul_mul _ hA

/-- [quarteroni2000numerical], Remark 5.4. Let $A \in \mathbb{K}^{N \times N}$ be Hermitian. Then
the Householder reduction $H$ of $A$ is tridiagonal. -/
theorem isTridiagonal_hessenbergReduce_of_isHermitian (hA : A.IsHermitian) :
    (hessenbergReduce A).IsTridiagonal :=
  (isUpperHessenberg_hessenbergReduce A).isTridiagonal_of_isHermitian
    (isHermitian_hessenbergReduce A hA)

/-- [quarteroni2000numerical], Remark 5.4, the real case. Let $A \in \mathbb{R}^{N \times N}$ be
symmetric. Then the Householder reduction $H$ of $A$ is symmetric.

With `Matrix.IsUpperHessenberg.isTridiagonal_of_isSymm`, $H$ is then tridiagonal. -/
theorem isSymm_hessenbergReduce {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsSymm) :
    (hessenbergReduce A).IsSymm := by
  have h : (hessenbergReduce A).IsHermitian :=
    isHermitian_hessenbergReduce A (by rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial])
  rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at h

/-- **Every square matrix is unitarily similar to an upper Hessenberg matrix**
([quarteroni2000numerical], §5.6.2). Let $n$ be a finite linearly ordered index type and
$A \in \mathbb{K}^{n \times n}$. Then there is a unitary $Q$ such that $Q^H A Q$ is upper
Hessenberg.

This is the existence form of the Householder reduction, transported from `Fin N` to $n$ along
`monoEquivOfFin`. -/
theorem exists_unitary_conj_isUpperHessenberg [LinearOrder n] (A : Matrix n n 𝕜) :
    ∃ Q ∈ Matrix.unitaryGroup n 𝕜, (Qᴴ * A * Q).IsUpperHessenberg := by
  obtain ⟨e, -⟩ : ∃ e : Fin (Fintype.card n) ≃o n, True := ⟨monoEquivOfFin n rfl, trivial⟩
  obtain ⟨A', hA'⟩ : ∃ A', A' = A.submatrix e.toEquiv e.toEquiv := ⟨_, rfl⟩
  have hA : A = A'.submatrix e.toEquiv.symm e.toEquiv.symm := by
    rw [hA', submatrix_submatrix]
    ext i j
    simp
  refine ⟨(hessenbergQ A').submatrix e.toEquiv.symm e.toEquiv.symm, ?_, ?_⟩
  · rw [mem_unitaryGroup_iff', star_eq_conjTranspose, conjTranspose_submatrix,
      submatrix_mul_equiv, ← star_eq_conjTranspose,
      mem_unitaryGroup_iff'.mp (hessenbergQ_mem_unitaryGroup _), submatrix_one_equiv]
  · rintro i j ⟨l, hjl, hli⟩
    rw [hA, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv,
      ← hessenbergReduce_eq_conj, submatrix_apply]
    exact isUpperHessenberg_hessenbergReduce _ _ _
      ⟨e.symm l, e.symm.lt_iff_lt.mpr hjl, e.symm.lt_iff_lt.mpr hli⟩

/-- Let $B$ be a square matrix of order $M + 1$, and let $Q$ be the unitary matrix of its
Householder reduction to Hessenberg form. Then $Q e_0 = e_0$, because all reflectors of the
reduction act on the coordinates $i \ge 1$. -/
theorem hessenbergQ_mulVec_single_zero {M : ℕ} (B : Matrix (Fin (M + 1)) (Fin (M + 1)) 𝕜) :
    hessenbergQ B *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  have hstep : ∀ (C : Matrix (Fin (M + 1)) (Fin (M + 1)) 𝕜) (k : ℕ),
      hessenbergReflector C k *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    intro C k
    by_cases hk : k < M + 1
    · rw [hessenbergReflector_of_lt C hk]
      refine householder_mulVec_eq_self_of_apply_eq_zero fun r hr => ?_
      have hr0 : r ≠ 0 := by
        rintro rfl
        exact hr (householderTail_apply_of_lt _ (by simp))
      exact Pi.single_eq_of_ne hr0 _
    · rw [hessenbergReflector_of_le C (not_lt.1 hk), one_mulVec]
  have hiter : ∀ k, hessenbergQIter B k *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    intro k
    induction k with
    | zero => rw [hessenbergQIter_zero, one_mulVec]
    | succ k ih => rw [hessenbergQIter_succ, ← mulVec_mulVec, hstep, ih]
  exact hiter _

end HessenbergReduction

/-! ### Sweeps of rotations in adjacent planes on a Hessenberg matrix -/

section AdjacentSweep

variable {α : Type*} {M N : ℕ}

/-- **Rotations from the bottom up turn a triangular matrix into a Hessenberg matrix**
([golub2013matrix], (6.5.2), and the deletion of a row in §6.5.3). Let $\alpha$ be a semiring,
let $T \in \alpha^{M \times N}$ be upper trapezoidal, let $G_j \in \alpha^{2 \times 2}$ be any
blocks, and let $E_j$ be the embedding of $G_j$ in the plane $(j, j + 1)$. Let
$b, n \in \mathbb{N}$ and
$$P = E_b E_{b+1} \cdots E_{b+n-1}.$$
Then $(PT)_{il} = 0$ whenever $l + 1 < i$, or $l < i$ and $l < b$. So $PT$ is upper Hessenberg,
and its columns before the first plane stay triangular.

The product $P$ corresponds to $J_1^T \cdots J_{n-1}^T$ of the source, applied from right to
left. The embedding $E_j$ is `Matrix.adjacentEmbed`, the identity when $j + 1 \ge M$. The proof
is an induction on $n$ from the left: the rows $b$ and $b + 1$ of $E_{b+1} \cdots E_{b+n-1} T$
both vanish before column $b$, so mixing them creates no nonzero entry there. -/
theorem prodFwd_adjacentEmbed_mul_apply_eq_zero [Semiring α] {T : Matrix (Fin M) (Fin N) α}
    (hT : T.HasLowerBandwidthRect 0) (G : ℕ → Matrix (Fin 2) (Fin 2) α) (b n : ℕ) {i : Fin M}
    {l : Fin N} (h : (l : ℕ) + 1 < i ∨ (l : ℕ) < i ∧ (l : ℕ) < b) :
    (prodFwd (fun k => (adjacentEmbed (b + k) (G (b + k)) : Matrix (Fin M) (Fin M) α)) n * T)
      i l = 0 := by
  induction n generalizing b i with
  | zero => simpa using hT i l (by omega)
  | succ n ih =>
    have ih' : ∀ i : Fin M, ((l : ℕ) + 1 < i ∨ (l : ℕ) < i ∧ (l : ℕ) < b + 1) →
        (prodFwd (fun k => (adjacentEmbed (b + (k + 1)) (G (b + (k + 1))) :
          Matrix (Fin M) (Fin M) α)) n * T) i l = 0 := fun i h => by
      simpa only [Nat.add_assoc, Nat.add_comm 1] using ih (b + 1) h
    rw [prodFwd_succ', Matrix.mul_assoc]
    by_cases hi : (i : ℕ) = b ∨ (i : ℕ) = b + 1
    · exact adjacentEmbed_mul_apply_eq_zero b (G b) _ (fun r hr => ih' r (by omega)) hi
    · exact (adjacentEmbed_mul_apply_of_ne b (G b) _ (by omega) (by omega) l).trans
        (ih' i (by omega))

/-- **The square case of (6.5.2)** of [golub2013matrix]. Let $\alpha$ be a semiring, let
$T \in \alpha^{M \times N}$ be upper trapezoidal, let $G_j \in \alpha^{2 \times 2}$ be any
blocks, and let $E_j$ be the embedding of $G_j$ in the plane $(j, j + 1)$. Then for every $n$,
the matrix $E_0 E_1 \cdots E_{n-1} T$ is upper Hessenberg: it has lower bandwidth $1$. -/
theorem hasLowerBandwidthRect_prodFwd_adjacentEmbed_mul [Semiring α]
    {T : Matrix (Fin M) (Fin N) α} (hT : T.HasLowerBandwidthRect 0)
    (G : ℕ → Matrix (Fin 2) (Fin 2) α) (n : ℕ) :
    (prodFwd (fun j => (adjacentEmbed j (G j) : Matrix (Fin M) (Fin M) α)) n *
      T).HasLowerBandwidthRect 1 :=
  fun _ _ h => by
    simpa only [Nat.zero_add] using prodFwd_adjacentEmbed_mul_apply_eq_zero hT G 0 n (Or.inl h)

/-- **Any zeroing sweep reduces a Hessenberg matrix to triangular form** ([golub2013matrix],
§6.5.1–6.5.3: "we compute Givens rotations … $G_{n-1}^T \cdots G_1^T H_1 = R_1$"). Let $\alpha$
be a non-associative semiring, let $H \in \alpha^{M \times N}$ be upper Hessenberg (lower
bandwidth $1$), and suppose that $H$ is already triangular in its first $a$ columns:
$h_{il} = 0$ whenever $l < i$ and $l < a$. Let $L = \min(N, M - 1)$. Let
$G_j \in \alpha^{2 \times 2}$ be any blocks, let $E_j$ be the embedding of $G_j$ in the plane
$(j, j + 1)$, and let $H_0 = H$ and
$$H_{t+1} = E_{a+t} H_t \quad \text{for } a + t < L.$$
Suppose that each step zeroes its target: $(H_{t+1})_{a+t+1,\, a+t} = 0$ for $a + t < L$. Then
$H_{L - a}$ is upper trapezoidal.

The zeroing is a hypothesis, not a choice of the rotation, so any Givens routine is an instance.
This is the rectangular form, with parameters, of the invariant behind
`Matrix.hessenbergGivensQR_spec`. The subtractions $M - 1$ and $L - a$ are truncated subtraction
in `ℕ`. -/
theorem hasLowerBandwidthRect_zero_of_adjacentRotations [NonAssocSemiring α]
    {H : Matrix (Fin M) (Fin N) α} (hH : H.HasLowerBandwidthRect 1) {a : ℕ}
    (ha : ∀ (i : Fin M) (l : Fin N), (l : ℕ) < i → (l : ℕ) < a → H i l = 0)
    (G : ℕ → Matrix (Fin 2) (Fin 2) α) (Hs : ℕ → Matrix (Fin M) (Fin N) α) (h0 : Hs 0 = H)
    (hstep : ∀ t, a + t < min N (M - 1) → Hs (t + 1) =
      (adjacentEmbed (a + t) (G (a + t)) : Matrix (Fin M) (Fin M) α) * Hs t)
    (hzero : ∀ t, a + t < min N (M - 1) → ∀ (i : Fin M) (l : Fin N), (i : ℕ) = a + t + 1 →
      (l : ℕ) = a + t → Hs (t + 1) i l = 0) :
    (Hs (min N (M - 1) - a)).HasLowerBandwidthRect 0 := by
  have key : ∀ t, t ≤ min N (M - 1) - a → (Hs t).HasLowerBandwidthRect 1 ∧
      ∀ (i : Fin M) (l : Fin N), (l : ℕ) < i → (l : ℕ) < a + t → Hs t i l = 0 := by
    intro t
    induction t with
    | zero =>
      intro _
      rw [h0]
      exact ⟨hH, fun i l h₁ h₂ => ha i l h₁ (by omega)⟩
    | succ t ih =>
      intro ht
      obtain ⟨ih₁, ih₂⟩ := ih (by omega)
      have hlt : a + t < min N (M - 1) := by omega
      have hz := hzero t hlt
      rw [hstep t hlt] at hz ⊢
      refine ⟨fun i l hil => ?_, fun i l hil hla => ?_⟩
      · by_cases hi : (i : ℕ) = a + t ∨ (i : ℕ) = a + t + 1
        · exact adjacentEmbed_mul_apply_eq_zero _ _ _
            (fun r hr => ih₂ r l (by omega) (by omega)) hi
        · rw [adjacentEmbed_mul_apply_of_ne _ _ _ (by omega) (by omega)]
          exact ih₁ i l hil
      · by_cases hi : (i : ℕ) = a + t ∨ (i : ℕ) = a + t + 1
        · by_cases hl : (l : ℕ) = a + t
          · exact hz i l (by omega) hl
          · exact adjacentEmbed_mul_apply_eq_zero _ _ _
              (fun r hr => ih₂ r l (by omega) (by omega)) hi
        · rw [adjacentEmbed_mul_apply_of_ne _ _ _ (by omega) (by omega)]
          by_cases hl : (l : ℕ) < a + t
          · exact ih₂ i l hil hl
          · exact ih₁ i l (by omega)
  intro i l hil
  exact (key _ le_rfl).2 i l (by omega) (by omega)

end AdjacentSweep

/-! ### The Givens QR factorization of a Hessenberg matrix -/

section GivensQR

variable {N : ℕ}

/-- The rotation of step $j$ of the Givens QR factorization of a Hessenberg matrix. For
$R \in \mathbb{R}^{N \times N}$ and $j + 1 < N$, it is the rotation in the plane $(j, j + 1)$ by
the Givens pair $(c, s)$ of the entries $r_{jj}$ and $r_{j+1, j}$. Its transpose annihilates the
entry $(j + 1, j)$ of $R$.

This is the matrix $G_j^{(k)}$ of [quarteroni2000numerical], (5.47). The rotation is
`Matrix.planeRotation`, and the pair is `Matrix.givensPair`. -/
noncomputable def hessenbergGivensRotation (R : Matrix (Fin N) (Fin N) ℝ) (j : ℕ)
    (h : j + 1 < N) : Matrix (Fin N) (Fin N) ℝ :=
  planeRotation (⟨j, by omega⟩ : Fin N) ⟨j + 1, h⟩
    (givensPair (R ⟨j, by omega⟩ ⟨j, by omega⟩) (R ⟨j + 1, h⟩ ⟨j, by omega⟩)).1
    (givensPair (R ⟨j, by omega⟩ ⟨j, by omega⟩) (R ⟨j + 1, h⟩ ⟨j, by omega⟩)).2

/-- The rotation of step $j$ of the Givens factorization is orthogonal. -/
theorem hessenbergGivensRotation_mem_orthogonalGroup (R : Matrix (Fin N) (Fin N) ℝ) (j : ℕ)
    (h : j + 1 < N) : hessenbergGivensRotation R j h ∈ Matrix.orthogonalGroup (Fin N) ℝ :=
  planeRotation_mem_orthogonalGroup (Fin.ne_of_val_ne (by simp)) (givensPair_sq_add_sq _ _)

/-- One step of the Givens QR factorization of a Hessenberg matrix, on a pair $(Q, R)$ of real
$N \times N$ matrices ([quarteroni2000numerical], (5.47), Program 31). For $j + 1 < N$, with $G$
the rotation of step $j$ for $R$, the step gives
$$(Q, R) \mapsto (Q G,\ G^T R).$$
So it rotates the rows $j$ and $j + 1$ of $R$ to annihilate the entry $(j + 1, j)$, and it
accumulates the rotation in $Q$. For $j + 1 \ge N$ the step does nothing. -/
noncomputable def hessenbergGivensStep (QR : Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ)
    (j : ℕ) : Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ :=
  if h : j + 1 < N then
    (QR.1 * hessenbergGivensRotation QR.2 j h, (hessenbergGivensRotation QR.2 j h)ᵀ * QR.2)
  else QR

/-- The pairs $(Q, R)$ of the Givens factorization of $H \in \mathbb{R}^{N \times N}$ after $j$
steps, starting from $(I, H)$. -/
noncomputable def hessenbergGivensIter (H : Matrix (Fin N) (Fin N) ℝ) :
    ℕ → Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ
  | 0 => (1, H)
  | j + 1 => hessenbergGivensStep (hessenbergGivensIter H j) j

/-- **The Givens QR factorization of an upper Hessenberg matrix** ([quarteroni2000numerical],
(5.47)–(5.48), Program 31). For $H \in \mathbb{R}^{N \times N}$ it is the pair $(Q, R)$ after
the $N - 1$ rotations $G_0, \dots, G_{N-2}$ in the planes $(j, j + 1)$:
$$Q = G_0 \cdots G_{N-2}, \qquad R = G_{N-2}^T \cdots G_0^T H.$$
Its properties are `Matrix.hessenbergGivensQR_spec`. For $N \le 1$ no step is made, and the pair
is $(I, H)$; for $N = 0$ this is because $N - 1$ is truncated subtraction in `ℕ`. -/
noncomputable def hessenbergGivensQR (H : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ :=
  hessenbergGivensIter H (N - 1)

/-- The $2 \times 2$ block of step $j$ of the Givens factorization: the rotation
$\begin{bmatrix} c & -s \\ s & c \end{bmatrix}$ by the Givens pair of the entries $(j, j)$ and
$(j + 1, j)$ of the current $R$, and the identity once $j + 1 \ge N$. Its embedding in the plane
$(j, j + 1)$ is the rotation of the step (`Matrix.hessenbergGivensRotation`). -/
private noncomputable def givensBlock (H : Matrix (Fin N) (Fin N) ℝ) (j : ℕ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  if h : j + 1 < N then
    !![(givensPair ((hessenbergGivensIter H j).2 ⟨j, by omega⟩ ⟨j, by omega⟩)
        ((hessenbergGivensIter H j).2 ⟨j + 1, h⟩ ⟨j, by omega⟩)).1,
      -(givensPair ((hessenbergGivensIter H j).2 ⟨j, by omega⟩ ⟨j, by omega⟩)
        ((hessenbergGivensIter H j).2 ⟨j + 1, h⟩ ⟨j, by omega⟩)).2;
      (givensPair ((hessenbergGivensIter H j).2 ⟨j, by omega⟩ ⟨j, by omega⟩)
        ((hessenbergGivensIter H j).2 ⟨j + 1, h⟩ ⟨j, by omega⟩)).2,
      (givensPair ((hessenbergGivensIter H j).2 ⟨j, by omega⟩ ⟨j, by omega⟩)
        ((hessenbergGivensIter H j).2 ⟨j + 1, h⟩ ⟨j, by omega⟩)).1]
  else 1

private theorem adjacentEmbed_givensBlock (H : Matrix (Fin N) (Fin N) ℝ) {j : ℕ}
    (h : j + 1 < N) :
    adjacentEmbed j (givensBlock H j) =
      hessenbergGivensRotation (hessenbergGivensIter H j).2 j h := by
  rw [adjacentEmbed_of_lt _ h, givensBlock, dite_eq_left h]
  rfl

/-- One step of the Givens factorization, as a rotation in the adjacent plane $(j, j + 1)$. -/
private theorem hessenbergGivensIter_succ (H : Matrix (Fin N) (Fin N) ℝ) (j : ℕ) :
    hessenbergGivensIter H (j + 1) =
      ((hessenbergGivensIter H j).1 * adjacentEmbed j (givensBlock H j),
        adjacentEmbed j (givensBlock H j)ᵀ * (hessenbergGivensIter H j).2) := by
  rw [← adjacentEmbed_transpose]
  change hessenbergGivensStep (hessenbergGivensIter H j) j = _
  unfold hessenbergGivensStep
  split_ifs with h
  · rw [adjacentEmbed_givensBlock H h]
  · rw [adjacentEmbed_of_le (M := N) (j := j) _ (by omega), transpose_one, Matrix.mul_one,
      Matrix.one_mul]

/-- The rotations of the Givens factorization, as embeddings in adjacent planes, are orthogonal. -/
private theorem adjacentEmbed_givensBlock_mem_orthogonalGroup (H : Matrix (Fin N) (Fin N) ℝ)
    (j : ℕ) : adjacentEmbed j (givensBlock H j) ∈ Matrix.orthogonalGroup (Fin N) ℝ := by
  by_cases h : j + 1 < N
  · rw [adjacentEmbed_givensBlock H h]
    exact hessenbergGivensRotation_mem_orthogonalGroup _ _ h
  · rw [adjacentEmbed_of_le (M := N) (j := j) _ (by omega)]
    exact one_mem _

/-- **The Givens QR factorization of a Hessenberg matrix** ([quarteroni2000numerical], (5.47)–(5.48)
and §5.6.3). Let $H \in \mathbb{R}^{N \times N}$ be upper Hessenberg, and let $(Q, R)$ be its
Givens factorization. Then $Q$ is orthogonal, $R$ is upper triangular,
$$H = QR,$$
and $Q$ is upper Hessenberg.

The factorization is a sweep of rotations in the adjacent planes $(j, j + 1)$, each of which
zeroes the entry $(j + 1, j)$. So $R$ is triangular by
`Matrix.hasLowerBandwidthRect_zero_of_adjacentRotations`. The factor $Q$ is a product of
adjacent rotations in increasing order, so it is Hessenberg by
`Matrix.hasLowerBandwidthRect_prodFwd_adjacentEmbed_mul`. -/
theorem hessenbergGivensQR_spec {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsUpperHessenberg) :
    (hessenbergGivensQR H).1 ∈ Matrix.orthogonalGroup (Fin N) ℝ ∧
      (hessenbergGivensQR H).2.IsUpperTriangular ∧
      H = (hessenbergGivensQR H).1 * (hessenbergGivensQR H).2 ∧
      (hessenbergGivensQR H).1.IsUpperHessenberg := by
  have hQ : ∀ j, (hessenbergGivensIter H j).1 =
      prodFwd (fun t => (adjacentEmbed t (givensBlock H t) : Matrix (Fin N) (Fin N) ℝ)) j := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      simp only [hessenbergGivensIter_succ]
      rw [ih, prodFwd_succ]
  have hmul : ∀ j, (hessenbergGivensIter H j).1 * (hessenbergGivensIter H j).2 = H := by
    intro j
    induction j with
    | zero => exact Matrix.one_mul H
    | succ j ih =>
      simp only [hessenbergGivensIter_succ]
      rw [← adjacentEmbed_transpose, Matrix.mul_assoc,
        ← Matrix.mul_assoc (adjacentEmbed j (givensBlock H j)),
        (mem_orthogonalGroup_iff _ ℝ).1 (adjacentEmbed_givensBlock_mem_orthogonalGroup H j),
        Matrix.one_mul, ih]
  refine ⟨?_, ?_, (hmul _).symm, ?_⟩
  · rw [hessenbergGivensQR, hQ]
    exact prodFwd_mem_orthogonalGroup fun t _ => adjacentEmbed_givensBlock_mem_orthogonalGroup H t
  · have key := hasLowerBandwidthRect_zero_of_adjacentRotations
      (fun i l h => isUpperHessenberg_iff_fin.1 hH i l h) (a := 0)
      (fun _ _ _ h => absurd h (Nat.not_lt_zero _)) (fun t => (givensBlock H t)ᵀ)
      (fun t => (hessenbergGivensIter H t).2) rfl
      (fun t _ => by simp only [zero_add, hessenbergGivensIter_succ])
      (fun t ht i l hi hl => by
        have h : t + 1 < N := by omega
        obtain rfl : i = ⟨t + 1, h⟩ := Fin.ext (by simpa using hi)
        obtain rfl : l = ⟨t, Nat.lt_of_succ_lt h⟩ := Fin.ext (by simpa using hl)
        simp only [hessenbergGivensIter_succ]
        rw [adjacentEmbed_mul_apply_succ t _ _ h]
        simp only [givensBlock, dite_eq_left h, transpose_apply, of_apply, cons_val', cons_val_zero,
          cons_val_one, cons_val_fin_one]
        exact (givensPair_fst_mul_add_snd_mul _ _).2)
    rw [show min N (N - 1) - 0 = N - 1 by omega] at key
    exact fun i l hli => key i l (by simpa using hli)
  · have hQH := hasLowerBandwidthRect_prodFwd_adjacentEmbed_mul
      (T := (1 : Matrix (Fin N) (Fin N) ℝ))
      (fun i l h => one_apply_ne (Fin.ne_of_val_ne (by omega))) (givensBlock H) (N - 1)
    rw [Matrix.mul_one, ← hQ] at hQH
    exact isUpperHessenberg_iff_fin.2 fun i l h => hQH i l h

end GivensQR

/-! ### Hadamard's determinant inequality -/

section Hadamard

/-- A unitary matrix preserves the Euclidean length of a vector. Let $U \in \mathbb{K}^{n \times n}$
be unitary and $v \in \mathbb{K}^n$. Then
$$\sum_i |(Uv)_i|^2 = \sum_i |v_i|^2.$$

Both sides are $w^H w$ for $w = Uv$ and $w = v$, read as real numbers, and $U^H U = I$. -/
theorem sum_norm_sq_mulVec_of_mem_unitaryGroup {U : Matrix n n 𝕜}
    (hU : U ∈ Matrix.unitaryGroup n 𝕜) (v : n → 𝕜) :
    ∑ i, ‖(U *ᵥ v) i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  have key : ∀ w : n → 𝕜, star w ⬝ᵥ w = ((∑ i, ‖w i‖ ^ 2 : ℝ) : 𝕜) := by
    intro w
    rw [dotProduct]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by simpa using RCLike.conj_mul (w i)
  have h : star (U *ᵥ v) ⬝ᵥ (U *ᵥ v) = star v ⬝ᵥ v := by
    rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, ← star_eq_conjTranspose,
      mem_unitaryGroup_iff'.1 hU, vecMul_one]
  rw [key, key] at h
  exact_mod_cast h

/-- Let $U \in \mathbb{K}^{n \times n}$ be unitary. Then $|\det U| = 1$. -/
theorem norm_det_of_mem_unitaryGroup {U : Matrix n n 𝕜} (hU : U ∈ Matrix.unitaryGroup n 𝕜) :
    ‖U.det‖ = 1 := by
  have h1 : ‖star U.det * U.det‖ = 1 := by
    rw [_root_.Unitary.star_mul_self_of_mem (Matrix.det_of_mem_unitary hU), norm_one]
  rw [norm_mul, norm_star] at h1
  nlinarith [norm_nonneg U.det]

variable [LinearOrder n]

/-- **Hadamard's determinant inequality.** Let $X \in \mathbb{K}^{n \times n}$. Then the modulus of
the determinant is at most the product of the Euclidean lengths of the columns:
$$|\det X| \le \prod_j \Bigl(\sum_i |x_{ij}|^2\Bigr)^{1/2}.$$

The statement assumes a linear order on the index type, which only the proof uses. The proof
reduces $X$ to triangular form by a unitary $U$ (`Matrix.exists_unitary_mul_isUpperTriangular`).
The determinant of $UX$ is that of $X$ up to a factor of modulus one, it is the product of the
diagonal of $UX$, and each diagonal entry is bounded by the length of its column, which $U$ does
not change. -/
theorem norm_det_le_prod_sqrt_sum_norm_sq (X : Matrix n n 𝕜) :
    ‖X.det‖ ≤ ∏ j, Real.sqrt (∑ i, ‖X i j‖ ^ 2) := by
  obtain ⟨U, hU, hT⟩ := exists_unitary_mul_isUpperTriangular X
  have hcol : ∀ j, ∑ i, ‖(U * X) i j‖ ^ 2 = ∑ i, ‖X i j‖ ^ 2 := fun j =>
    sum_norm_sq_mulVec_of_mem_unitaryGroup hU _
  have hX : ‖X.det‖ = ‖(U * X).det‖ := by
    rw [det_mul, norm_mul, norm_det_of_mem_unitaryGroup hU, one_mul]
  rw [hX, det_of_isUpperTriangular hT, norm_prod]
  refine Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) fun j _ => ?_
  rw [← hcol j]
  calc ‖(U * X) j j‖ = Real.sqrt (‖(U * X) j j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (∑ i, ‖(U * X) i j‖ ^ 2) :=
        Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun i => ‖(U * X) i j‖ ^ 2)
          (fun i _ => by positivity) (Finset.mem_univ j))

/-- **Hadamard's inequality in entrywise form.** Let $X \in \mathbb{K}^{n \times n}$ and $c \ge 0$
with $|x_{ij}| \le c$ for all $i, j$. Then
$$|\det X| \le (\sqrt{n}\, c)^n = n^{n/2} c^n.$$

The statement assumes a linear order on the index type, which only the proof uses. -/
theorem norm_det_le_of_forall_norm_le {X : Matrix n n 𝕜} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i j, ‖X i j‖ ≤ c) :
    ‖X.det‖ ≤ (Real.sqrt (Fintype.card n) * c) ^ Fintype.card n := by
  refine (norm_det_le_prod_sqrt_sum_norm_sq X).trans ?_
  calc ∏ j, Real.sqrt (∑ i, ‖X i j‖ ^ 2)
      ≤ ∏ _j : n, Real.sqrt (Fintype.card n * c ^ 2) := by
        refine Finset.prod_le_prod₀ (fun j _ => Real.sqrt_nonneg _) fun j _ => Real.sqrt_le_sqrt ?_
        calc ∑ i, ‖X i j‖ ^ 2 ≤ ∑ _i : n, c ^ 2 :=
              Finset.sum_le_sum fun i _ => by nlinarith [h i j, norm_nonneg (X i j)]
          _ = Fintype.card n * c ^ 2 := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (Real.sqrt (Fintype.card n) * c) ^ Fintype.card n := by
        rw [Finset.prod_const, Finset.card_univ, Real.sqrt_mul (by positivity), Real.sqrt_sq hc]

end Hadamard

end Matrix

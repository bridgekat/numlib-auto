/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Numlib.Direct.Refinement
import Numlib.Eigen.Deflation
import Numlib.FloatingPoint.Householder
import NumlibSurface.QuarteroniSaccoSaleri.Chapter05.Section05

/-!
# Quarteroni, Sacco and Saleri, Section 5.6: The QR Method for Matrices in Hessenberg Form

This module formalizes Section 5.6 of [quarteroni2000numerical]. A Householder matrix
$P = I - 2 v v^T / \|v\|_2^2$ (5.38) is a symmetric orthogonal reflection, and a suitable
Householder vector $v$ sets to zero all the components of a vector $x$ but one (5.39)–(5.42). A
Givens matrix $G(i, k, \theta)$ (5.43) rotates the coordinate plane $(x_i, x_k)$, and a suitable
angle sets $x_k$ to zero (5.44), (5.51). Householder reflections deflate a computed eigenpair
(Remark 5.3). The Householder method of Section 5.6.2 reduces any $A \in \mathbb{R}^{n \times n}$ by
$n - 2$ orthogonal similarities $A^{(k)} = P_{(k)}^T A^{(k-1)} P_{(k)}$ (5.45) to an upper
Hessenberg matrix $H = Q^T A Q$, which is tridiagonal when $A$ is symmetric (Remark 5.4), and in
floating-point arithmetic it is backward stable (5.46). Givens rotations factor a Hessenberg matrix
as $H = QR$ (5.47)–(5.48), and the QR iteration preserves Hessenberg form (Section 5.6.4). A
reflector is applied as a rank-one update (5.49)–(5.50).

The proofs specialize the backbone modules `Numlib.LinearAlgebra.Matrix.QR` (Householder reflectors,
the reflector of a tail of coordinates, the Householder reduction to Hessenberg form and the Givens
QR factorization of a Hessenberg matrix), `Numlib.LinearAlgebra.Matrix.PlaneRotation` (plane
rotations and the Givens pair), `Numlib.Eigen.Deflation` (Householder deflation),
`Numlib.Eigen.QRAlgorithm` (the invariance of Hessenberg form under a QR step) and
`Numlib.FloatingPoint.Householder` (the rounding model of the Householder reduction, for (5.46)).

## Main definitions

* Equation (5.38), `QuarteroniSaccoSaleri.Chapter05.equation_5_38`: the Householder matrix
  $I - 2 v v^T / \|v\|_2^2$.
* Equation (5.43), `QuarteroniSaccoSaleri.Chapter05.equation_5_43`: the Givens rotation matrix
  $G(i, k, \theta)$.
* Equation (5.45), `QuarteroniSaccoSaleri.Chapter05.householderStepMatrix`: the Householder matrix
  $P_{(k)}$ of a step of the Householder method.
* Equation (5.45), `QuarteroniSaccoSaleri.Chapter05.hessenbergStep`,
  `QuarteroniSaccoSaleri.Chapter05.hessenbergIter`,
  `QuarteroniSaccoSaleri.Chapter05.hessenbergQIter`: one step, the iterates $A^{(k)}$ and the
  accumulated orthogonal matrices $Q_{(k)}$ of the Householder method.
* Section 5.6.2, `QuarteroniSaccoSaleri.Chapter05.hessenbergReduce`,
  `QuarteroniSaccoSaleri.Chapter05.hessenbergQ`: the Hessenberg form $H = A^{(n-2)}$ and the
  orthogonal matrix $Q$.

## Main results

* Equation (5.38), `QuarteroniSaccoSaleri.Chapter05.equation_5_38_eq_householder`: the Householder
  matrix of the book is the backbone's reflector of $v / \|v\|_2$.
* Equation (5.38), `QuarteroniSaccoSaleri.Chapter05.equation_5_38_isSymm`,
  `QuarteroniSaccoSaleri.Chapter05.equation_5_38_mul_self`,
  `QuarteroniSaccoSaleri.Chapter05.equation_5_38_mem_orthogonalGroup`: a Householder matrix is
  symmetric, an involution, and orthogonal.
* Equations (5.39)–(5.40), `QuarteroniSaccoSaleri.Chapter05.equation_5_40`: the reflector of
  $v = x \pm \|x\|_2 e_m$ maps $x$ to a multiple of $e_m$.
* Equations (5.41)–(5.42), `QuarteroniSaccoSaleri.Chapter05.equation_5_41`: the reflector $P_{(k)}$
  keeps the first $k$ components of $x$ and sets the components after the $(k+1)$-st to zero.
* Equation (5.43), `QuarteroniSaccoSaleri.Chapter05.equation_5_43_apply`,
  `QuarteroniSaccoSaleri.Chapter05.equation_5_43_mem_orthogonalGroup`: the entries of a Givens
  matrix, and its orthogonality.
* Equation (5.44), `QuarteroniSaccoSaleri.Chapter05.equation_5_44`: $G(i, k, \theta)^T x$ rotates
  $x$ by $\theta$ in the plane $(x_i, x_k)$.
* Equations (5.44) and (5.51), `QuarteroniSaccoSaleri.Chapter05.equation_5_51`: a suitable angle
  sets the $k$-th component of $G(i, k, \theta)^T x$ to zero.
* Remark 5.3, `QuarteroniSaccoSaleri.Chapter05.remark_5_3`: Householder deflation of a computed
  eigenpair.
* Equation (5.45), `QuarteroniSaccoSaleri.Chapter05.equation_5_45`: the iterates of the Householder
  method are orthogonally similar to $A$.
* Section 5.6.2, `QuarteroniSaccoSaleri.Chapter05.hessenbergReduce_isUpperHessenberg`: the
  Householder method gives an upper Hessenberg matrix.
* Section 5.6.2, `QuarteroniSaccoSaleri.Chapter05.exists_orthogonal_conj_isUpperHessenberg`: every
  real square matrix is orthogonally similar to an upper Hessenberg matrix.
* Remark 5.4, `QuarteroniSaccoSaleri.Chapter05.remark_5_4`: for a symmetric $A$, the Householder
  method gives a symmetric tridiagonal matrix.
* Equation (5.46), `QuarteroniSaccoSaleri.Chapter05.equation_5_46`: the computed Hessenberg form is
  $\hat H = Q^T (A + E) Q$ with $\|E\|_F \le c n^2 u \|A\|_F$.
* Equations (5.47)–(5.48), `QuarteroniSaccoSaleri.Chapter05.equation_5_47`: the Givens QR
  factorization of a Hessenberg matrix.
* Section 5.6.4, `QuarteroniSaccoSaleri.Chapter05.isUpperHessenberg_qrIterate`: the QR iteration
  preserves upper Hessenberg form.
* Equations (5.49)–(5.50), `QuarteroniSaccoSaleri.Chapter05.equation_5_49`: applying a reflector is
  a rank-one update.

## Conventions

* Vectors are `Fin n → ℝ`, and $\|x\|_2$ is the Euclidean norm
  `‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖`.
* The sign $\pm$ of the book in (5.39) and (5.42) is the backbone's $+\operatorname{sign}(x_m)$
  (`Matrix.householderAxis`), which avoids cancellation. The sign is `Matrix.phase`, with
  $\operatorname{sign} 0 = 1$.
* The Givens matrix (5.43) is `QuarteroniSaccoSaleri.Chapter05.equation_5_43 i k θ`, whose entry
  $(i, k)$ is $\sin \theta$. The backbone's `Matrix.planeRotation i k c s` has the entry $-s$ in
  position $(i, k)$, so the Givens matrix is `planeRotation i k (cos θ) (-sin θ)`. Hence the pair
  $(c, s)$ of (5.44) and (5.51) is the backbone's $(c, -s)$, and `Matrix.givensPair` has the
  opposite sign of $s$.
* Indices start at $0$. The matrix $P_{(k)}$ of the book keeps the first $k$ components and works
  from the $(k+1)$-st on, so its pivot has the index $k$.

## Implementation notes

* The Householder matrix (5.38) is written as the book writes it, and
  `QuarteroniSaccoSaleri.Chapter05.equation_5_38_eq_householder` identifies it with the backbone's
  reflector of the unit axis $v / \|v\|_2$.
* The Householder method of Section 5.6.2 is written as the book's recursion (5.45),
  `QuarteroniSaccoSaleri.Chapter05.hessenbergIter`, and
  `QuarteroniSaccoSaleri.Chapter05.hessenbergIter_eq` identifies it with the backbone's
  `Matrix.hessenbergIter`.
* The Givens QR factorization of Section 5.6.3 is stated for the backbone's
  `Matrix.hessenbergGivensQR`, whose factors are shown to be the products of the book's rotations
  $G_j = G(j, j+1, \theta_j)$.

## Deviations from the source

* **Remark 5.3** (typo). The book prints $H x_1 = \alpha x_1$ for the reflector $H$. It should read
  $H x_1 = \alpha e_1$, which is what $v = x_1 \pm \|x_1\|_2 e_1$ and (5.40) give and what the block
  form of $HAH$ needs. See `QuarteroniSaccoSaleri.Chapter05.remark_5_3`.
* **Equation (5.46)** (reading). The constant $c$ of the book is given explicitly, and "the roundoff
  unit $u$" is qualified by $c n^2 u \le 1$. Program 29 is read as Section 19.3 of
  [higham2002accuracy] reads such an algorithm. See `QuarteroniSaccoSaleri.Chapter05.equation_5_46`.

## Not formalized

* **Equation (5.46) with the Householder vector of Program 32.** Program 32 uses the other sign with
  the rationalized formula, which [higham2002accuracy] covers "similarly".
* **The estimate $\|E\|_2 \simeq u \|A\|_2$ after Program 30** (the Hessenberg-QR iteration). It
  carries a $\simeq$ and is not a proposition.
* **Examples 5.5–5.9.** They are numerical.
* **The operation counts.** They are prose.
* **Programs 29–35.** They are code.
-/

open Finset Matrix Polynomial

namespace QuarteroniSaccoSaleri.Chapter05

variable {N : ℕ}

/-! ### Equation (5.38): Householder reflection matrices -/

/-- **Equation (5.38)** of [quarteroni2000numerical], the Householder reflection matrix. For a
Householder vector $v \in \mathbb{R}^n$, it is the matrix
$$P = I - \frac{2 v v^T}{\|v\|_2^2},$$
the reflection across the hyperplane $\operatorname{span}\{v\}^\perp$.

For $v = 0$, where the formula of the book is undefined, Lean divides by zero to zero, and
$P = I$. -/
noncomputable def equation_5_38 (v : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  1 - (2 / ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin N))‖ ^ 2) • vecMulVec v v

/-- For $v \in \mathbb{R}^n$, $\|v\|_2^2 = v^T v$. -/
theorem norm_toLp_sq_eq_dotProduct (v : Fin N → ℝ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin N))‖ ^ 2 = v ⬝ᵥ v := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [dotProduct, sq]

/-- The Householder matrix of the zero vector is the identity. -/
@[simp]
theorem equation_5_38_zero : equation_5_38 (0 : Fin N → ℝ) = 1 := by
  simp [equation_5_38]

/-- For $v \in \mathbb{R}^n$ with $v \neq 0$, the Householder matrix (5.38) of $v$ is the backbone's
reflector `Matrix.householder` of the normalized axis $v / \|v\|_2$. -/
theorem equation_5_38_eq_householder {v : Fin N → ℝ} (hv : v ≠ 0) :
    equation_5_38 v =
      householder ((‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin N))‖)⁻¹ • v) := by
  have hn : ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin N))‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (by simpa using hv)
  rw [equation_5_38, householder, star_trivial, smul_vecMulVec, vecMulVec_smul, smul_smul,
    smul_smul]
  congr 2
  field_simp

/-- A Householder matrix is symmetric. -/
theorem equation_5_38_isSymm (v : Fin N → ℝ) : (equation_5_38 v).IsSymm := by
  rw [IsSymm, equation_5_38, transpose_sub, transpose_one, transpose_smul, transpose_vecMulVec]

/-- For $v \in \mathbb{R}^n$ with $v \neq 0$, the axis $u = v / \|v\|_2$ is a unit vector,
$u^T u = 1$, in the form that the backbone's lemmas on reflectors take. -/
theorem star_dotProduct_normalize_self {v : Fin N → ℝ} (hv : v ≠ 0) :
    star ((‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin N))‖)⁻¹ • v) ⬝ᵥ
      (‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin N))‖)⁻¹ • v = 1 := by
  have hn : ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin N))‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (by simpa using hv)
  rw [star_trivial, smul_dotProduct, dotProduct_smul, ← norm_toLp_sq_eq_dotProduct, smul_eq_mul,
    smul_eq_mul]
  field_simp

/-- For $v \in \mathbb{R}^n$ with $v \neq 0$, the Householder matrix $P$ of $v$ is an involution,
$P P = I$. This is the backbone's `Matrix.householder_mul_self`. -/
theorem equation_5_38_mul_self {v : Fin N → ℝ} (hv : v ≠ 0) :
    equation_5_38 v * equation_5_38 v = 1 := by
  rw [equation_5_38_eq_householder hv]
  exact householder_mul_self (star_dotProduct_normalize_self hv)

/-- For $v \in \mathbb{R}^n$ with $v \neq 0$, the Householder matrix of $v$ is orthogonal. This is
the backbone's `Matrix.householder_mem_unitaryGroup`. -/
theorem equation_5_38_mem_orthogonalGroup {v : Fin N → ℝ} (hv : v ≠ 0) :
    equation_5_38 v ∈ Matrix.orthogonalGroup (Fin N) ℝ := by
  rw [equation_5_38_eq_householder hv]
  exact householder_mem_unitaryGroup (star_dotProduct_normalize_self hv)

/-! ### Equations (5.39)–(5.42): reflectors that annihilate coordinates -/

/-- The reflector of the axis (5.39) of [quarteroni2000numerical] is the backbone's reflector. For
every $x \in \mathbb{R}^n$ and index $m$, the Householder matrix (5.38) of
`Matrix.householderAxis x m` is `Matrix.householder (Matrix.householderVec x m)`.

The unit vector `Matrix.householderVec x m` is the normalized axis, or $0$ when $x = 0$. In that
case both sides are the identity. -/
theorem equation_5_38_householderAxis (x : Fin N → ℝ) (m : Fin N) :
    equation_5_38 (householderAxis x m) = householder (householderVec x m) := by
  rcases eq_or_ne x 0 with rfl | hx
  · have h : householderAxis (0 : Fin N → ℝ) m = 0 := by
      simp [householderAxis]
    rw [h, householderVec_zero, householder_zero, equation_5_38_zero]
  · exact equation_5_38_eq_householder (householderAxis_ne_zero hx m)

/-- **Equations (5.39)–(5.40)** of [quarteroni2000numerical]. Let $x \in \mathbb{R}^n$ with
$x \neq 0$, let $m$ be an index, and let
$$v = x + \operatorname{sign}(x_m) \|x\|_2 e_m$$
be the Householder vector (5.39). Then the Householder matrix $P$ of $v$ sets to zero all the
components of $x$ except the $m$-th:
$$P x = -\operatorname{sign}(x_m) \|x\|_2 \, e_m,$$
and the remaining entry has modulus $\|x\|_2$.

The book writes $v = x \pm \|x\|_2 e_m$ and $Px = [0, \dots, 0, \mp\|x\|_2, 0, \dots, 0]^T$. The
sign is `Matrix.phase (x m)`, with $\operatorname{sign} 0 = 1$, and $v$ is
`Matrix.householderAxis x m`. The proof specializes the backbone's
`Matrix.householder_mulVec_eq_smul_single`. -/
theorem equation_5_40 {x : Fin N → ℝ} (hx : x ≠ 0) (m : Fin N) :
    let v := householderAxis x m
    v = x + (phase (x m) * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖) •
        (Pi.single m 1 : Fin N → ℝ) ∧
      equation_5_38 v *ᵥ x =
        (-(phase (x m) * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖)) •
          (Pi.single m 1 : Fin N → ℝ) ∧
      |-(phase (x m) * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖)| =
        ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N))‖ := by
  refine ⟨rfl, ?_, ?_⟩
  · rw [equation_5_38_householderAxis]
    exact householder_mulVec_eq_smul_single hx m
  · rw [abs_neg, abs_mul, ← Real.norm_eq_abs, norm_phase, one_mul, abs_norm]

/-- **Equations (5.41)–(5.42)** of [quarteroni2000numerical]. Let $x \in \mathbb{R}^n$ and $k < n$.
Let $x^{(n-k)}$ be the vector of the last $n - k$ components of $x$, embedded in $\mathbb{R}^n$
by zeros in the first $k$ components, and let
$$w^{(k)} = x^{(n-k)} + \operatorname{sign}(x_k) \|x^{(n-k)}\|_2 \, e_k$$
be the Householder vector (5.42). Let $P_{(k)}$ be the Householder matrix of $w^{(k)}$ and
$y = P_{(k)} x$. Then:

1. $w^{(k)}$ vanishes on the first $k$ components, so $P_{(k)}$ has the block form
   $\operatorname{diag}(I_k, R_{n-k})$ of (5.41);
2. $y_j = x_j$ for $j < k$;
3. $y_j = 0$ for $j > k$;
4. $y_k = -\operatorname{sign}(x_k) \|x^{(n-k)}\|_2$, so $|y_k| = \|x^{(n-k)}\|_2$.

The indices start at $0$. The book writes $w^{(k)} = x^{(n-k)} \pm \|x^{(n-k)}\|_2 e_1^{(n-k)}$
and $y_k = \pm\|x^{(n-k)}\|_2$. The proof specializes the backbone's
`Matrix.householder_tail_mulVec` and `Matrix.householderTail_apply_of_lt`. -/
theorem equation_5_41 (x : Fin N → ℝ) {k : ℕ} (hk : k < N) :
    let t : Fin N → ℝ := fun r => if k ≤ (r : ℕ) then x r else 0
    let w := householderAxis t ⟨k, hk⟩
    (∀ i : Fin N, (i : ℕ) < k → w i = 0) ∧
      (∀ i : Fin N, (i : ℕ) < k → (equation_5_38 w *ᵥ x) i = x i) ∧
      (∀ i : Fin N, k < (i : ℕ) → (equation_5_38 w *ᵥ x) i = 0) ∧
      (equation_5_38 w *ᵥ x) ⟨k, hk⟩ =
        -(phase (x ⟨k, hk⟩) * ‖(WithLp.toLp 2 t : EuclideanSpace ℝ (Fin N))‖) ∧
      |(equation_5_38 w *ᵥ x) ⟨k, hk⟩| = ‖(WithLp.toLp 2 t : EuclideanSpace ℝ (Fin N))‖ := by
  intro t w
  have hP : equation_5_38 w = householder (householderTail x k) := by
    rw [householderTail_of_lt x hk]
    exact equation_5_38_householderAxis t ⟨k, hk⟩
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, ?_, ?_⟩
  · have hik : i ≠ ⟨k, hk⟩ := fun h => by rw [h] at hi; exact lt_irrefl _ hi
    change householderAxis t ⟨k, hk⟩ i = 0
    rw [householderAxis_apply_of_ne _ hik]
    exact ite_eq_right (not_le.2 hi)
  · rw [hP]
    exact householder_householderTail_mulVec_apply_of_lt x hi
  · rw [hP]
    exact householder_householderTail_mulVec_apply_of_gt x hi
  · rw [hP]
    exact householder_householderTail_mulVec_apply_self x hk
  · rw [hP, ← Real.norm_eq_abs]
    exact norm_householder_householderTail_mulVec_apply_self x hk

/-! ### Equations (5.43)–(5.44): Givens rotation matrices -/

/-- **Equation (5.43)** of [quarteroni2000numerical], the Givens rotation matrix. For indices
$i \neq k$ and an angle $\theta \in \mathbb{R}$, $G(i, k, \theta) = I_n - Y$ is the identity
except for the entries
$$g_{ii} = g_{kk} = \cos \theta, \qquad g_{ik} = \sin \theta, \qquad g_{ki} = -\sin \theta.$$

The backbone's `Matrix.planeRotation i k c s` has $-s$ in position $(i, k)$, so
$G(i, k, \theta)$ is `planeRotation i k (Real.cos θ) (-Real.sin θ)`. -/
noncomputable def equation_5_43 (i k : Fin N) (θ : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  planeRotation i k (Real.cos θ) (-Real.sin θ)

/-- For indices $i \neq k$ and $\theta \in \mathbb{R}$, the entries of the Givens matrix
$G(i, k, \theta)$ are $\cos \theta$ at $(i, i)$ and $(k, k)$, $\sin \theta$ at $(i, k)$,
$-\sin \theta$ at $(k, i)$, and those of the identity elsewhere. -/
theorem equation_5_43_apply {i k : Fin N} (hik : i ≠ k) (θ : ℝ) (p q : Fin N) :
    equation_5_43 i k θ p q =
      if p = i ∧ q = i then Real.cos θ
      else if p = k ∧ q = k then Real.cos θ
      else if p = i ∧ q = k then Real.sin θ
      else if p = k ∧ q = i then -Real.sin θ
      else if p = q then 1 else 0 := by
  rw [equation_5_43, planeRotation_apply hik]
  by_cases hpi : p = i <;> by_cases hpk : p = k <;> by_cases hqi : q = i <;>
    by_cases hqk : q = k <;> simp_all [hik.symm]

/-- For indices $i \neq k$ and $\theta \in \mathbb{R}$, the Givens matrix $G(i, k, \theta)$ is
orthogonal. This is `Matrix.planeRotation_mem_orthogonalGroup` with
$\cos^2 \theta + \sin^2 \theta = 1$. -/
theorem equation_5_43_mem_orthogonalGroup {i k : Fin N} (hik : i ≠ k) (θ : ℝ) :
    equation_5_43 i k θ ∈ Matrix.orthogonalGroup (Fin N) ℝ :=
  planeRotation_mem_orthogonalGroup hik (by rw [neg_sq]; exact Real.cos_sq_add_sin_sq θ)

/-- **Equation (5.44)** of [quarteroni2000numerical]. Let $i \neq k$ be indices,
$\theta \in \mathbb{R}$ and $x \in \mathbb{R}^n$, and let $c = \cos \theta$ and
$s = \sin \theta$. Then $y = G(i, k, \theta)^T x$ is $x$ rotated counterclockwise by $\theta$ in
the coordinate plane $(x_i, x_k)$:
$$y_j = x_j \quad (j \neq i, k), \qquad y_i = c x_i - s x_k, \qquad y_k = s x_i + c x_k.$$

The proof specializes the backbone's `Matrix.transpose_planeRotation_mulVec_apply`. -/
theorem equation_5_44 {i k : Fin N} (hik : i ≠ k) (θ : ℝ) (x : Fin N → ℝ) :
    let y := (equation_5_43 i k θ)ᵀ *ᵥ x
    (∀ j, j ≠ i → j ≠ k → y j = x j) ∧
      y i = Real.cos θ * x i - Real.sin θ * x k ∧
      y k = Real.sin θ * x i + Real.cos θ * x k := by
  refine ⟨fun j hji hjk => ?_, ?_, ?_⟩
  · rw [equation_5_43, transpose_planeRotation_mulVec_apply hik, ite_eq_right hji, ite_eq_right hjk]
  · rw [equation_5_43, transpose_planeRotation_mulVec_apply hik, ite_eq_left rfl]
    ring
  · rw [equation_5_43, transpose_planeRotation_mulVec_apply hik, ite_eq_right hik.symm,
      ite_eq_left rfl]
    ring

/-- **Equations (5.44) and (5.51)** of [quarteroni2000numerical], the annihilating choice of the
angle. Let $i \neq k$ be indices and $x \in \mathbb{R}^n$ with $(x_i, x_k) \neq (0, 0)$, and let
$\alpha_{ik} = \sqrt{x_i^2 + x_k^2}$. Then there is an angle $\theta$ with
$$c = \cos \theta = \frac{x_i}{\alpha_{ik}}, \qquad s = \sin \theta =
  -\frac{x_k}{\alpha_{ik}},$$
and for this $\theta$ the vector $y = G(i, k, \theta)^T x$ has $y_k = 0$, $y_i = \alpha_{ik}$
and $y_j = x_j$ for $j \neq i, k$. This is the system (5.51),
$$\begin{bmatrix} c & -s \\ s & c \end{bmatrix} \begin{bmatrix} x_i \\ x_k \end{bmatrix} =
  \begin{bmatrix} r \\ 0 \end{bmatrix}.$$

The book writes the angle as $\theta = \arctan(-x_k / x_i)$. This formula gives the right angle
only when $x_i > 0$; the statement gives $\theta$ by its cosine and sine. The pair $(c, -s)$ is
the backbone's `Matrix.givensPair (x i) (x k)`, and the annihilation is
`Matrix.transpose_planeRotation_givensPair_mulVec`. -/
theorem equation_5_51 {i k : Fin N} (hik : i ≠ k) (x : Fin N → ℝ) (hx : ¬ (x i = 0 ∧ x k = 0)) :
    let α := √(x i ^ 2 + x k ^ 2)
    ∃ θ : ℝ, Real.cos θ = x i / α ∧ Real.sin θ = -(x k / α) ∧
      ((equation_5_43 i k θ)ᵀ *ᵥ x) k = 0 ∧ ((equation_5_43 i k θ)ᵀ *ᵥ x) i = α ∧
      ∀ j, j ≠ i → j ≠ k → ((equation_5_43 i k θ)ᵀ *ᵥ x) j = x j := by
  intro α
  have hpair : givensPair (x i) (x k) = (x i / α, x k / α) := givensPair_of_not _ _ hx
  have hsq : (x i / α) ^ 2 + (-(x k / α)) ^ 2 = 1 := by
    have h := givensPair_sq_add_sq (x i) (x k)
    rw [hpair] at h
    rw [neg_sq]
    exact h
  obtain ⟨θ, hc, hs⟩ := Real.exists_cos_eq_sin_eq hsq
  have hG : equation_5_43 i k θ =
      planeRotation i k (givensPair (x i) (x k)).1 (givensPair (x i) (x k)).2 := by
    rw [equation_5_43, hc, hs, neg_neg, hpair]
  obtain ⟨h1, h2, h3⟩ := transpose_planeRotation_givensPair_mulVec hik x
  exact ⟨θ, hc, hs, by rw [hG]; exact h1, by rw [hG]; exact h2, fun j hji hjk => by
    rw [hG]; exact h3 j hji hjk⟩

/-! ### Remark 5.3: Householder deflation -/

/-- **Remark 5.3** of [quarteroni2000numerical] (Householder deflation for power iterations). Let
$A \in \mathbb{R}^{n \times n}$ with $n \ge 1$, and suppose that an eigenpair
$(\lambda_1, x_1)$, $A x_1 = \lambda_1 x_1$ with $x_1 \neq 0$, has been computed. Let $H$ be the
Householder matrix (5.38) of $v = x_1 + \sigma \|x_1\|_2 e_1$, where $\sigma$ is the sign of the
first component of $x_1$, and let $A_1 = H A H$. Then:

1. $H x_1 = \alpha e_1$ for some $\alpha \in \mathbb{R}$;
2. the first column of $A_1$ is $\lambda_1 e_1$, so that $A_1 = \begin{bmatrix} \lambda_1 & b^T
   \\ 0 & A_2 \end{bmatrix}$;
3. the eigenvalues of the trailing block $A_2 \in \mathbb{R}^{(n-1) \times (n-1)}$ are those of
   $A$ except $\lambda_1$, with multiplicities: $\det(\lambda I - A) = (\lambda - \lambda_1)
   \det(\lambda I - A_2)$.

**Typo.** The book prints $H x_1 = \alpha x_1$. It should read $H x_1 = \alpha e_1$, which is
what $v = x_1 \pm \|x_1\|_2 e_1$ and (5.40) give and what the block form of $HAH$ needs.

The matrix has order $N + 1$ in Lean, and $A_2$ is `A₁.submatrix Fin.succ Fin.succ`. The proof
specializes the backbone's `Matrix.householder_conj_eigenvector_apply` and
`Matrix.charpoly_householder_conj_eigenvector`. -/
theorem remark_5_3 {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} {x₁ : Fin (N + 1) → ℝ} {lam₁ : ℝ}
    (hx : A *ᵥ x₁ = lam₁ • x₁) (hx0 : x₁ ≠ 0) :
    let H := equation_5_38 (householderAxis x₁ 0)
    let A₁ := H * A * H
    (∃ α : ℝ, H *ᵥ x₁ = α • (Pi.single 0 1 : Fin (N + 1) → ℝ)) ∧
      (A₁ 0 0 = lam₁ ∧ ∀ i, i ≠ 0 → A₁ i 0 = 0) ∧
      A.charpoly = (X - C lam₁) * (A₁.submatrix Fin.succ Fin.succ).charpoly := by
  intro H A₁
  have hH : H = householder (householderVec x₁ 0) := equation_5_38_householderAxis x₁ 0
  refine ⟨⟨_, by rw [hH]; exact householder_mulVec_eq_smul_single hx0 0⟩, ⟨?_, fun i hi => ?_⟩, ?_⟩
  · have h := householder_conj_eigenvector_apply A hx hx0 0 0
    rwa [ite_eq_left rfl, ← hH] at h
  · have h := householder_conj_eigenvector_apply A hx hx0 0 i
    rwa [ite_eq_right hi, ← hH] at h
  · have h := charpoly_householder_conj_eigenvector A hx hx0
    rwa [← hH] at h

/-! ### Section 5.6.2: the Householder reduction to Hessenberg form -/

/-- **Equation (5.45)** of [quarteroni2000numerical], the Householder matrix $P_{(k)}$ of a step of
the Householder method. For $A \in \mathbb{R}^{n \times n}$ and a step $k$ with $k + 1 < n$, it
is the matrix (5.41) built, as in `QuarteroniSaccoSaleri.Chapter05.equation_5_41`, from the
$k$-th column of $A$ with pivot $k + 1$, so that it sets to zero the entries of that column
after the pivot. It is the identity when there is nothing to set to zero, $k + 1 \ge n$.

The indices start at $0$: the book counts from $1$, and here the column is $k$ and the pivot is
$k + 1$. -/
noncomputable def householderStepMatrix (A : Matrix (Fin N) (Fin N) ℝ) (k : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  if h : k + 1 < N then
    equation_5_38 (householderAxis
      (fun i : Fin N => if k + 1 ≤ (i : ℕ) then A i ⟨k, by omega⟩ else 0) ⟨k + 1, h⟩)
  else 1

/-- **Equation (5.45)** of [quarteroni2000numerical], one step of the Householder method:
$A \mapsto P_{(k)}^T A P_{(k)}$. -/
noncomputable def hessenbergStep (A : Matrix (Fin N) (Fin N) ℝ) (k : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  (householderStepMatrix A k)ᵀ * A * householderStepMatrix A k

/-- **Section 5.6.2** of [quarteroni2000numerical], the Householder method (5.45). For
$A \in \mathbb{R}^{n \times n}$, it is the sequence of matrices $A^{(0)} = A$ and
$A^{(k)} = P_{(k)}^T A^{(k-1)} P_{(k)}$, which are orthogonally similar to $A$. -/
noncomputable def hessenbergIter (A : Matrix (Fin N) (Fin N) ℝ) : ℕ → Matrix (Fin N) (Fin N) ℝ
  | 0 => A
  | k + 1 => hessenbergStep (hessenbergIter A k) k

/-- **Equation (5.45)** of [quarteroni2000numerical], the accumulated orthogonal matrix
$Q_{(k)} = P_{(1)} \cdots P_{(k)}$ of the Householder method, with $Q_{(0)} = I$. -/
noncomputable def hessenbergQIter (A : Matrix (Fin N) (Fin N) ℝ) : ℕ → Matrix (Fin N) (Fin N) ℝ
  | 0 => 1
  | k + 1 => hessenbergQIter A k * householderStepMatrix (hessenbergIter A k) k

/-- **Section 5.6.2** of [quarteroni2000numerical], the Hessenberg form $H = A^{(n-2)}$ produced by
the $n - 2$ steps of the Householder method (Program 29).

For $n < 2$ there are no steps, and $H = A$. -/
noncomputable def hessenbergReduce (A : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  hessenbergIter A (N - 2)

/-- **Section 5.6.2** of [quarteroni2000numerical], the orthogonal matrix
$Q = P_{(1)} \cdots P_{(n-2)}$ of the Householder method, with $H = Q^T A Q$ (Program 29). -/
noncomputable def hessenbergQ (A : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  hessenbergQIter A (N - 2)

/-- The matrix $P_{(k)}$ of the book is the backbone's step reflector:
`QuarteroniSaccoSaleri.Chapter05.householderStepMatrix A k` is `Matrix.hessenbergReflector A k`. -/
theorem householderStepMatrix_eq (A : Matrix (Fin N) (Fin N) ℝ) (k : ℕ) :
    householderStepMatrix A k = hessenbergReflector A k := by
  unfold householderStepMatrix
  by_cases h : k + 1 < N
  · rw [dite_eq_left h, hessenbergReflector_of_lt A (by omega),
      householderTail_of_lt _ (show k + 1 < N from h), equation_5_38_householderAxis]
  · rw [dite_eq_right h]
    by_cases hk : k < N
    · rw [hessenbergReflector_of_lt A hk, householderTail_of_le _ (by omega), householder_zero]
    · rw [hessenbergReflector_of_le A (not_lt.1 hk)]

/-- The step $P_{(k)}^T A P_{(k)}$ of the book is the backbone's `Matrix.hessenbergStep A k`,
because the reflector is symmetric. -/
theorem hessenbergStep_eq (A : Matrix (Fin N) (Fin N) ℝ) (k : ℕ) :
    hessenbergStep A k = Matrix.hessenbergStep A k := by
  rw [hessenbergStep, Matrix.hessenbergStep, householderStepMatrix_eq,
    ← conjTranspose_eq_transpose_of_trivial, (isHermitian_hessenbergReflector A k).eq]

/-- The recursion (5.45) of [quarteroni2000numerical] is the backbone's: for every $k$,
`QuarteroniSaccoSaleri.Chapter05.hessenbergIter A k` is `Matrix.hessenbergIter A k`, and
`QuarteroniSaccoSaleri.Chapter05.hessenbergQIter A k` is `Matrix.hessenbergQIter A k`. -/
theorem hessenbergIter_eq (A : Matrix (Fin N) (Fin N) ℝ) :
    ∀ k, hessenbergIter A k = Matrix.hessenbergIter A k ∧
      hessenbergQIter A k = Matrix.hessenbergQIter A k
  | 0 => ⟨rfl, rfl⟩
  | k + 1 => by
    obtain ⟨h1, h2⟩ := hessenbergIter_eq A k
    rw [hessenbergIter, hessenbergQIter, h1, h2, hessenbergStep_eq, householderStepMatrix_eq,
      Matrix.hessenbergIter_succ, Matrix.hessenbergQIter_succ]
    exact ⟨rfl, rfl⟩

/-- The matrices $H$ and $Q$ of the book are the backbone's `Matrix.hessenbergReduce` and
`Matrix.hessenbergQ`. -/
theorem hessenbergReduce_eq (A : Matrix (Fin N) (Fin N) ℝ) :
    hessenbergReduce A = Matrix.hessenbergReduce A ∧ hessenbergQ A = Matrix.hessenbergQ A :=
  hessenbergIter_eq A (N - 2)

/-- **Equation (5.45)** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$. For every
$k$, the matrix $Q_{(k)} = P_{(1)} \cdots P_{(k)}$ is orthogonal, and the matrix $A^{(k)}$ of
the Householder method is orthogonally similar to $A$:
$$A^{(k)} = P_{(k)}^T A^{(k-1)} P_{(k)} = (P_{(1)} \cdots P_{(k)})^T A \, (P_{(1)} \cdots
  P_{(k)}) = Q_{(k)}^T A Q_{(k)}.$$
In particular, $Q = P_{(1)} \cdots P_{(n-2)}$ is orthogonal and $H = Q^T A Q$ for the Hessenberg
form $H = A^{(n-2)}$, which is the output of Program 29.

The proof specializes the backbone's `Matrix.hessenbergIter_eq_conj`,
`Matrix.hessenbergQIter_mem_unitaryGroup`, `Matrix.hessenbergReduce_eq_conj` and
`Matrix.hessenbergQ_mem_orthogonalGroup`. -/
theorem equation_5_45 (A : Matrix (Fin N) (Fin N) ℝ) :
    (∀ k, hessenbergQIter A k ∈ Matrix.orthogonalGroup (Fin N) ℝ ∧
      hessenbergIter A k = (hessenbergQIter A k)ᵀ * A * hessenbergQIter A k) ∧
      hessenbergQ A ∈ Matrix.orthogonalGroup (Fin N) ℝ ∧
      hessenbergReduce A = (hessenbergQ A)ᵀ * A * hessenbergQ A := by
  have key : ∀ k, hessenbergQIter A k ∈ Matrix.orthogonalGroup (Fin N) ℝ ∧
      hessenbergIter A k = (hessenbergQIter A k)ᵀ * A * hessenbergQIter A k := fun k => by
    rw [(hessenbergIter_eq A k).1, (hessenbergIter_eq A k).2,
      ← conjTranspose_eq_transpose_of_trivial]
    exact ⟨hessenbergQIter_mem_unitaryGroup A k, hessenbergIter_eq_conj A k⟩
  exact ⟨key, (key (N - 2)).1, (key (N - 2)).2⟩

/-- **Section 5.6.2** of [quarteroni2000numerical]. For $A \in \mathbb{R}^{n \times n}$, the matrix
$H = A^{(n-2)}$ obtained after $n - 2$ steps of the Householder method is upper Hessenberg.

This is the backbone's `Matrix.isUpperHessenberg_hessenbergReduce`. -/
theorem hessenbergReduce_isUpperHessenberg (A : Matrix (Fin N) (Fin N) ℝ) :
    (hessenbergReduce A).IsUpperHessenberg := by
  rw [(hessenbergReduce_eq A).1]
  exact isUpperHessenberg_hessenbergReduce A

/-- **Section 5.6.2** of [quarteroni2000numerical], the opening sentence. Every
$A \in \mathbb{R}^{n \times n}$ can be transformed by an orthogonal similarity into upper
Hessenberg form: there is an orthogonal $Q$ such that $Q^T A Q$ is upper Hessenberg.

This is the backbone's `Matrix.exists_unitary_conj_isUpperHessenberg`, or
`QuarteroniSaccoSaleri.Chapter05.equation_5_45` with
`QuarteroniSaccoSaleri.Chapter05.hessenbergReduce_isUpperHessenberg`. -/
theorem exists_orthogonal_conj_isUpperHessenberg (A : Matrix (Fin N) (Fin N) ℝ) :
    ∃ Q ∈ Matrix.orthogonalGroup (Fin N) ℝ, (Qᵀ * A * Q).IsUpperHessenberg :=
  ⟨hessenbergQ A, (equation_5_45 A).2.1,
    (equation_5_45 A).2.2 ▸ hessenbergReduce_isUpperHessenberg A⟩

/-- **Remark 5.4** of [quarteroni2000numerical] (the symmetric case). Let
$A \in \mathbb{R}^{n \times n}$ be symmetric. Then the transformation (5.45) keeps the symmetry,
$(A^{(k)})^T = (Q_{(k)}^T A Q_{(k)})^T = A^{(k)}$ for every $k$. So $H = A^{(n-2)}$ is symmetric
and, because it is upper Hessenberg, tridiagonal.

The proof specializes the backbone's `Matrix.isSymm_hessenbergReduce` and
`Matrix.IsUpperHessenberg.isTridiagonal_of_isSymm`. -/
theorem remark_5_4 {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsSymm) :
    (∀ k, (hessenbergIter A k).IsSymm) ∧ (hessenbergReduce A).IsSymm ∧
      (hessenbergReduce A).IsTridiagonal := by
  have hsymm : ∀ k, (hessenbergIter A k).IsSymm := fun k => by
    rw [((equation_5_45 A).1 k).2, IsSymm, transpose_mul, transpose_mul, transpose_transpose,
      hA.eq, Matrix.mul_assoc]
  exact ⟨hsymm, hsymm (N - 2),
    (hessenbergReduce_isUpperHessenberg A).isTridiagonal_of_isSymm (hsymm (N - 2))⟩

/-! ### Equation (5.46): the stability of the Householder reduction -/

open scoped Matrix.Norms.Frobenius in
/-- **Equation (5.46)** of [quarteroni2000numerical], the backward stability of the Householder
reduction to Hessenberg form. There is a constant $c > 0$ with the following property. Let
$n \in \mathbb{N}$, let a rounding model have the unit roundoff $u$ with $c n^2 u \le 1$, let
$A \in \mathbb{R}^{n \times n}$, and let $\hat H$ be a Hessenberg matrix computed from $A$ by
the Householder reduction in floating-point arithmetic. Then there are an orthogonal $Q$ and a
matrix $E$ with
$$\hat H = Q^T (A + E) Q, \qquad \|E\|_F \le c n^2 u \|A\|_F.$$

**Reading.** The book quotes the estimate, due to Wilkinson, without proof, with an unspecified
constant $c$ and "the roundoff unit $u$". The constant is explicit here, and $u$ is qualified by
$c n^2 u \le 1$. Program 29 is read as Section 19.3 of [higham2002accuracy] reads such an
algorithm: the Householder vector is built as in Lemma 19.1 of [higham2002accuracy], with the
sign $+\operatorname{sign}(x_k)$ of the backbone; the products by $R$ are the rank-one updates
(5.49)–(5.50) with one rounding per operation; and the annihilated entries of column $k$ are set
to zero, rather than left as the small rounding errors that Program 29 leaves. Program 32 uses
the other sign with the rationalized formula, which [higham2002accuracy] covers "similarly", and
this variant is not formalized.

The computation is `FloatingPoint.RoundsHessenbergReduce m A Hhat`, the $n - 2$ steps of Program
29, and $\hat H$ is `Hhat (n - 2)`. The norm is the Frobenius norm. The proof takes $c = 528$,
and $Q$ is the product $P_{(1)} \cdots P_{(n-2)}$ of the exact reflectors of the computed
matrices $\hat A^{(k-1)}$. It specializes the backbone's
`FloatingPoint.exists_roundsHessenbergReduce_eq`, which applies Lemmas 19.1–19.3 of
[higham2002accuracy] to the two sweeps of every step. Its explicit bound $\|E\|_F \le
\gamma_{2(n-2)}(3 \gamma_{13n+27}) \|A\|_F$ becomes $c n^2 u$ by $\gamma_k \le 2 k u$ for
$2 k u \le 1$. -/
theorem equation_5_46 :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (m : FloatingPoint.RoundingModel ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
      (Hhat : ℕ → Matrix (Fin n) (Fin n) ℝ), c * n ^ 2 * m.u ≤ 1 →
      FloatingPoint.RoundsHessenbergReduce m A Hhat →
      ∃ Q ∈ Matrix.orthogonalGroup (Fin n) ℝ, ∃ E : Matrix (Fin n) (Fin n) ℝ,
        Hhat (n - 2) = Qᵀ * (A + E) * Q ∧ ‖E‖ ≤ c * n ^ 2 * m.u * ‖A‖ := by
  refine ⟨528, by norm_num, fun n m A Hhat hu h => ?_⟩
  have hu0 := m.u_nonneg
  have hcnn : 0 ≤ (528 : ℝ) * n ^ 2 * m.u * ‖A‖ := by positivity
  rcases lt_or_ge n 3 with hn | hn
  · -- fewer than three rows: no step is taken, `Ĥ = A`
    have h2 : n - 2 = 0 := by omega
    refine ⟨1, one_mem _, 0, ?_, by simpa using hcnn⟩
    rw [h2, h.1]
    simp
  · have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) ≤ n := by linarith
    -- the smallness hypotheses of the backbone theorem
    have hK : ((13 * n + 27 : ℕ) : ℝ) ≤ 22 * n := by push_cast; linarith
    have hnu : (0 : ℝ) ≤ n * m.u := by positivity
    have hn2u : (n : ℝ) * m.u ≤ n ^ 2 * m.u := by nlinarith
    have h44 : 2 * (((13 * n + 27 : ℕ) : ℝ) * m.u) ≤ 1 := by nlinarith
    have hcard : ((13 * n + 27 : ℕ) : ℝ) * m.u < 1 := by linarith
    have hγ : FloatingPoint.gamma m.u (13 * n + 27) ≤ 2 * (((13 * n + 27 : ℕ) : ℝ) * m.u) :=
      FloatingPoint.gamma_le_two_mul hu0 h44
    have hγ0 : 0 ≤ FloatingPoint.gamma m.u (13 * n + 27) := FloatingPoint.gamma_nonneg hu0 hcard
    set ε := 3 * FloatingPoint.gamma m.u (13 * n + 27) with hε
    have hε0 : 0 ≤ ε := by positivity
    have hεle : ε ≤ 132 * (n * m.u) := by rw [hε]; nlinarith
    have hr2 : ((2 * (n - 2) : ℕ) : ℝ) ≤ 2 * n := by
      have : ((n - 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 2
      push_cast
      linarith
    have hrε : 2 * (((2 * (n - 2) : ℕ) : ℝ) * ε) ≤ 1 := by
      have h1 : ((2 * (n - 2) : ℕ) : ℝ) * ε ≤ 2 * n * (132 * (n * m.u)) :=
        mul_le_mul hr2 hεle hε0 (by positivity)
      nlinarith
    have hr : ((2 * (n - 2) : ℕ) : ℝ) * ε < 1 := by linarith
    obtain ⟨-, Q, hQ, E, hH, hE⟩ := FloatingPoint.exists_roundsHessenbergReduce_eq hcard hr h
    refine ⟨Q, hQ, E, hH, hE.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))⟩
    calc FloatingPoint.gamma ε (2 * (n - 2)) ≤ 2 * (((2 * (n - 2) : ℕ) : ℝ) * ε) :=
          FloatingPoint.gamma_le_two_mul hε0 hrε
      _ ≤ 2 * (2 * n * (132 * (n * m.u))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hr2 hεle hε0 (by positivity)) (by norm_num)
      _ = 528 * n ^ 2 * m.u := by ring

/-! ### Section 5.6.3: the Givens QR factorization of a Hessenberg matrix -/

/-- **Equations (5.47)–(5.48)** of [quarteroni2000numerical], the QR factorization of a Hessenberg
matrix by Givens rotations. Let $H \in \mathbb{R}^{n \times n}$ be upper Hessenberg. Then there
are angles $\theta_j$, $j = 1, \dots, n - 1$, such that, with the Givens rotations
$G_j = G(j, j+1, \theta_j)$ of (5.43), the matrix
$$R = G_{n-1}^T \cdots G_1^T H$$
is upper triangular (5.47), and $H = QR$ with $Q = G_1 \cdots G_{n-1}$ orthogonal and upper
Hessenberg (5.48). The pair $(Q, R)$ is the backbone's `Matrix.hessenbergGivensQR H`.

In the backbone's construction (Program 31), each rotation is chosen according to (5.44) so that
it sets to zero the entry $(j+1, j)$ of $G_{j-1}^T \cdots G_1^T H$, and
`Matrix.hessenbergGivensQR` is the fold of the $n - 1$ rotations of the Givens pairs. The proof
uses `Matrix.hessenbergGivensQR_spec` for the factorization and `Real.exists_cos_eq_sin_eq` for
the angles. -/
theorem equation_5_47 {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsUpperHessenberg) :
    ∃ θ : ℕ → ℝ,
      let G : ℕ → Matrix (Fin N) (Fin N) ℝ := fun j =>
        if h : j + 1 < N then equation_5_43 ⟨j, by omega⟩ ⟨j + 1, h⟩ (θ j) else 1
      let Q := ((List.range (N - 1)).map G).prod
      let R := (((List.range (N - 1)).map G).map transpose).reverse.prod * H
      (hessenbergGivensQR H).1 = Q ∧ (hessenbergGivensQR H).2 = R ∧
        Q ∈ Matrix.orthogonalGroup (Fin N) ℝ ∧ R.IsUpperTriangular ∧ H = Q * R ∧
        Q.IsUpperHessenberg := by
  -- the angles of the rotations along the fold
  have hθ : ∀ j : ℕ, ∃ θ : ℝ, ∀ h : j + 1 < N,
      equation_5_43 ⟨j, by omega⟩ ⟨j + 1, h⟩ θ =
        hessenbergGivensRotation (hessenbergGivensIter H j).2 j h := by
    intro j
    by_cases h : j + 1 < N
    · set R := (hessenbergGivensIter H j).2
      set a := R ⟨j, by omega⟩ ⟨j, by omega⟩
      set b := R ⟨j + 1, h⟩ ⟨j, by omega⟩
      have hsq : (givensPair a b).1 ^ 2 + (-(givensPair a b).2) ^ 2 = 1 := by
        rw [neg_sq]; exact givensPair_sq_add_sq a b
      obtain ⟨θ, hc, hs⟩ := Real.exists_cos_eq_sin_eq hsq
      refine ⟨θ, fun h' => ?_⟩
      rw [equation_5_43, hc, hs, neg_neg]
      rfl
    · exact ⟨0, fun h' => absurd h' h⟩
  choose θ hθ using hθ
  refine ⟨θ, ?_⟩
  intro G Q R
  -- the accumulated factor after `j` steps is the product of the first `j` rotations
  have hiter : ∀ j, (hessenbergGivensIter H j).1 = ((List.range j).map G).prod := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
        List.prod_singleton, ← ih]
      change (hessenbergGivensStep (hessenbergGivensIter H j) j).1 = _
      unfold hessenbergGivensStep
      by_cases h : j + 1 < N
      · rw [dite_eq_left h]
        change _ * hessenbergGivensRotation _ j h = _ * G j
        rw [show G j = equation_5_43 ⟨j, by omega⟩ ⟨j + 1, h⟩ (θ j) from dite_eq_left h, hθ j h]
      · rw [dite_eq_right h, show G j = 1 from dite_eq_right h, Matrix.mul_one]
  obtain ⟨hQ, hR, hQR, hQH⟩ := hessenbergGivensQR_spec hH
  have hQeq : (hessenbergGivensQR H).1 = Q := hiter (N - 1)
  have hQt : Qᵀ * Q = 1 := by
    rw [← hQeq]
    simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
      (mem_orthogonalGroup_iff' (Fin N) ℝ).1 hQ
  have hReq : (hessenbergGivensQR H).2 = R := by
    rw [hQeq] at hQR
    calc (hessenbergGivensQR H).2 = Qᵀ * Q * (hessenbergGivensQR H).2 := by
          rw [hQt, Matrix.one_mul]
      _ = Qᵀ * H := by rw [Matrix.mul_assoc, ← hQR]
      _ = R := by rw [transpose_list_prod]
  rw [hQeq] at hQ hQR hQH
  rw [hReq] at hR hQR
  exact ⟨hQeq, hReq, hQ, hR, hQR, hQH⟩

/-! ### Section 5.6.4: the QR iteration on a Hessenberg matrix -/

/-- **Section 5.6.4** of [quarteroni2000numerical]: the QR iteration preserves upper Hessenberg
form. Let $T^{(0)} = H^{(0)} \in \mathbb{R}^{n \times n}$ be nonsingular and upper Hessenberg.
Then every iterate $T^{(k)}$ of (5.32) is upper Hessenberg, and so is the orthogonal factor
$Q^{(k+1)}$ of each step (Section 5.6.3).

The iterate $T^{(k+1)} = R Q$ is an upper triangular matrix times an upper Hessenberg matrix.
The iterate is `QuarteroniSaccoSaleri.Chapter05.qrIterate A k` and the factor is
`qrQ (qrIterate A k)`. The proof specializes the backbone's `Matrix.isUpperHessenberg_qrIterate`
and `Matrix.isUpperHessenberg_qrQ`. -/
theorem isUpperHessenberg_qrIterate {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsUpperHessenberg)
    (hdet : IsUnit A.det) (k : ℕ) :
    (qrIterate A k).IsUpperHessenberg ∧ (qrQ (qrIterate A k)).IsUpperHessenberg := by
  rw [qrIterate_eq]
  exact ⟨Matrix.isUpperHessenberg_qrIterate hdet hA k,
    isUpperHessenberg_qrQ (isUnit_det_qrIterate hdet k)
      (Matrix.isUpperHessenberg_qrIterate hdet hA k)⟩

/-! ### Section 5.6.5: applying a reflector -/

/-- **Equations (5.49)–(5.50)** of [quarteroni2000numerical]. Let $v \in \mathbb{R}^n$, let
$P = I - \beta v v^T$ be the Householder matrix (5.38) of $v$, with $\beta = 2 / \|v\|_2^2$, and
let $M \in \mathbb{R}^{n \times n}$. Then
$$P M = M - \beta v w^T \quad \text{with } w = M^T v, \qquad M P = M - \beta w v^T \quad
  \text{with } w = M v.$$
So applying a reflector is a matrix–vector product and a rank-one update, and $P$ is never
formed.

For $v = 0$, $\beta = 0$ and both identities are trivial. The backbone's
`Matrix.householder_mul_eq_sub_vecMulVec` and `Matrix.mul_householder_eq_sub_vecMulVec` are the
same identities for the normalized axis; here they follow from (5.38) directly. -/
theorem equation_5_49 (v : Fin N → ℝ) (M : Matrix (Fin N) (Fin N) ℝ) :
    let β := 2 / ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin N))‖ ^ 2
    equation_5_38 v * M = M - β • vecMulVec v (Mᵀ *ᵥ v) ∧
      M * equation_5_38 v = M - β • vecMulVec (M *ᵥ v) v := by
  intro β
  constructor
  · rw [equation_5_38, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, vecMulVec_mul,
      mulVec_transpose]
  · rw [equation_5_38, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, mul_vecMulVec]

end QuarteroniSaccoSaleri.Chapter05

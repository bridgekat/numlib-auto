/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.SingularValues
import Numlib.Krylov.Decomposition
import Numlib.LinearAlgebra.Matrix.Bidiagonal

/-!
# Golub–Kahan bidiagonalization

Let $A : E \to F$ be a linear map between two inner product spaces over $\mathbb{K} = \mathbb{R}$ or
$\mathbb{C}$, and let $A^* : F \to E$ be an adjoint of $A$, that is $\langle A^* u, x \rangle =
\langle u, A x \rangle$ for all $u \in F$ and $x \in E$. From a starting vector $v \in E$, the
Golub–Kahan process builds orthonormal vectors $v_0, v_1, \dots \in E$ and $u_0, u_1, \dots \in F$
and nonnegative reals $\alpha_j$, $\beta_j$ with
$$A v_j = \alpha_j u_j + \beta_{j-1} u_{j-1}, \qquad A^* u_j = \alpha_j v_j + \beta_j v_{j+1}$$
(the term with $\beta_{-1}$ is absent). These are the recurrences (10.4.2)–(10.4.3) of
[golub2013matrix], §10.4.1. The vectors $v_0, \dots, v_{k-1}$ span the Krylov subspace
$\mathcal{K}_k(A^* A, v)$, and $u_0, \dots, u_{k-1}$ span $\mathcal{K}_k(A A^*, A v)$. The
coefficients form an upper bidiagonal matrix $B_k$ with $B_k^T B_k = T_k(A^* A)$, the tridiagonal
Lanczos matrix of $A^* A$, and the Lanczos process of the Jordan–Wielandt operator
$(x, y) \mapsto (A^* y, A x)$ from $(v, 0)$ interleaves the two families ([golub2013matrix],
§10.4.3).

The lower bidiagonalization of Paige and Saunders ([golub2013matrix], Algorithm 10.4.2) is the same
process for the pair $(A^*, A)$, so the module also gives the residual formula of LSQR
([golub2013matrix], §11.4.2): if $b - A x_0 = \beta u_0$, then $b - A(x_0 + V_k y) = U_{k+1}(\beta
e_1 - \bar B_k y)$. For a matrix $A$, the matrices $V_k$ and $U_k$ of the two families satisfy
$A V_k = U_k B_k$ and $A^H U_k = V_{k+1} \bar B_k$, the relations (10.4.9)–(10.4.10) of
[golub2013matrix].

## Main definitions

* `GolubKahan.rightVec`, `GolubKahan.leftVec`: the vectors $v_j$ and $u_j$, as the Arnoldi vectors
  of $A^* A$ from $v$ and of $A A^*$ from $A v$.
* `GolubKahan.alpha`, `GolubKahan.beta`: the coefficients $\alpha_j = \operatorname{Re} \langle u_j,
  A v_j \rangle$ and $\beta_j = \operatorname{Re} \langle v_{j+1}, A^* u_j \rangle$.
* `GolubKahan.bidiag`: the upper bidiagonal $k \times k$ matrix $B_k$.
* `GolubKahan.bidiagLower`: the lower bidiagonal $(k + 1) \times k$ matrix $\bar B_k$.
* `GolubKahan.rightMatrix`, `GolubKahan.leftMatrix`: for a matrix $A$, the matrices $V_k$ and $U_k$
  whose columns are the vectors $v_j$ and $u_j$.

## Main results

* `GolubKahan.apply_rightVec_zero`, `GolubKahan.apply_rightVec`, `GolubKahan.adjoint_apply_leftVec`:
  the coupled recurrences (10.4.2)–(10.4.3).
* `GolubKahan.alpha_nonneg`, `GolubKahan.beta_nonneg`: the coefficients are nonnegative, and the
  inner products that define them are real.
* `GolubKahan.lanczos_alpha_zero`, `GolubKahan.lanczos_alpha_succ`, `GolubKahan.lanczos_beta_eq`,
  `GolubKahan.bidiag_conjTranspose_mul_bidiag`: the Lanczos coefficients of $A^* A$ are
  $\alpha_0^2$, $\alpha_{j+1}^2 + \beta_j^2$ and $\alpha_j \beta_j$, so $B_k^T B_k = T_k(A^* A)$.
* `GolubKahan.grade_comp_adjoint`: the grades of $A A^*$ at $A v$ and of $A^* A$ at $v$ are equal or
  differ by one.
* `GolubKahan.residual_eq`: the LSQR residual $b - A(x_0 + V_k y) = U_{k+1}(\beta e_1 - \bar B_k
  y)$.
* `GolubKahan.lanczos_jordanWielandt`: the Lanczos matrix of the Jordan–Wielandt operator from
  $(v, 0)$ has zero diagonal and off-diagonal $\alpha_0, \beta_0, \alpha_1, \beta_1, \dots$.
* `GolubKahan.mul_rightMatrix`, `GolubKahan.conjTranspose_mul_leftMatrix`: the matrix relations
  $A V_k = U_k B_k$ and $A^H U_k = V_{k+1} \bar B_k$.

## Proof outline

The coupled recurrences are theorems about the two Arnoldi families. The map $A$ intertwines the two
Gram operators, $A (A^* A) = (A A^*) A$, and $A^*$ intertwines them in the other direction. An
intertwining map carries Krylov subspaces to Krylov subspaces (`Krylov.map_subspace_of_semiconj`),
and it carries an Arnoldi vector to a vector whose component along the Arnoldi vector of the same
step is a nonnegative real (`Arnoldi.inner_vec_apply_vec_of_semiconj`). Orthogonality then removes
all other components.

## Implementation notes

* The adjoint is a hypothesis `hadj : LinearMap.IsAdjointPair (innerₛₗ 𝕜).flip (innerₛₗ 𝕜).flip A
  Astar`, which is equivalent to $\langle A^* u, x \rangle = \langle u, A x \rangle$ by
  `LinearMap.isAdjointPair_inner_iff`. As in `Numlib.Krylov.NormalEquations`, neither completeness
  nor finite dimension is needed.
* The vectors are defined as Arnoldi vectors of the two Gram operators, so the span identities
  (10.4.11)–(10.4.12) are instances of `Arnoldi.span_vec`. The recurrences are proved, not imposed.
* Breakdown is uniform: past the grade the vectors are $0$, and every identity holds with both sides
  $0$. In particular the matrix relations hold for every $k$.
* Indices start at $0$: `GolubKahan.rightVec A Astar v 0` is $v / \|v\|$, the vector $v_1$ of
  [golub2013matrix], and `GolubKahan.alpha A Astar v j` and `GolubKahan.beta A Astar v j` are the
  book's $\alpha_{j+1}$ and $\beta_{j+1}$.
* The upper and the lower bidiagonalization are not two processes. The lower one of $A$ from
  $u \in F$ is the Golub–Kahan process of the pair $(A^*, A)$ from $u$, and its matrix is
  `GolubKahan.bidiagLower`, which is also the matrix of $A^*$ in the upper process. The LSQR
  residual formula is therefore an instance of `Krylov.HessenbergRelation₂.residual_eq` through
  `GolubKahan.hessenbergRelation₂`.
* The Jordan–Wielandt operator is `LinearMap.hermitianDilation A Astar` on `WithLp 2 (E × F)`. It
  puts the domain factor $E$ first, while the matrix
  $\begin{bmatrix} 0 & A \\ A^H & 0 \end{bmatrix}$ of [golub2013matrix] acts on $F \times E$ from
  $(0, v)$.
-/

open Krylov Finset

open scoped Matrix

open LinearMap (hermitianDilation)

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### The Golub–Kahan vectors and coefficients -/

namespace GolubKahan

section Operator

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 F] (A : E →ₗ[𝕜] F) (Astar : F →ₗ[𝕜] E) (v : E)

/-- The **right Golub–Kahan vectors** $v_j \in E$: the Arnoldi vectors of $A^* A$ from $v$, that is,
the Gram–Schmidt orthonormalization of $v, (A^* A) v, (A^* A)^2 v, \dots$, with $v_j = 0$ past
breakdown. This is the vector $v_{j+1}$ of Algorithm 10.4.1 of [golub2013matrix].

The definition is `Arnoldi.vec (Astar ∘ₗ A) v j`. In particular $v_0 = v / \|v\|$. -/
noncomputable def rightVec (j : ℕ) : E :=
  Arnoldi.vec (Astar ∘ₗ A) v j

/-- The **left Golub–Kahan vectors** $u_j \in F$: the Arnoldi vectors of $A A^*$ from $A v$, that
is, the Gram–Schmidt orthonormalization of $A v, (A A^*) A v, (A A^*)^2 A v, \dots$, with
$u_j = 0$ past breakdown. This is the vector $u_{j+1}$ of Algorithm 10.4.1 of [golub2013matrix].

The definition is `Arnoldi.vec (A ∘ₗ Astar) (A v) j`. -/
noncomputable def leftVec (j : ℕ) : F :=
  Arnoldi.vec (A ∘ₗ Astar) (A v) j

/-- The **diagonal Golub–Kahan coefficient** $\alpha_j = \operatorname{Re} \langle u_j, A v_j
\rangle$. This is the coefficient $\alpha_{j+1}$ of Algorithm 10.4.1 of [golub2013matrix].

The inner product is real (`GolubKahan.inner_leftVec_apply_rightVec`), so the real part loses
nothing. -/
noncomputable def alpha (j : ℕ) : ℝ :=
  RCLike.re (inner 𝕜 (leftVec A Astar v j) (A (rightVec A Astar v j)))

/-- The **superdiagonal Golub–Kahan coefficient** $\beta_j = \operatorname{Re} \langle v_{j+1}, A^*
u_j \rangle$. This is the coefficient $\beta_{j+1}$ of Algorithm 10.4.1 of [golub2013matrix].

The inner product is real (`GolubKahan.inner_rightVec_adjoint_apply_leftVec`), so the real part
loses nothing. -/
noncomputable def beta (j : ℕ) : ℝ :=
  RCLike.re (inner 𝕜 (rightVec A Astar v (j + 1)) (Astar (leftVec A Astar v j)))

/-- For every $k$, the right Golub–Kahan vectors $v_0, \dots, v_{k-1}$ span the Krylov subspace
$$\operatorname{span}\{v_0, \dots, v_{k-1}\} = \mathcal{K}_k(A^* A, v).$$
This is equation (10.4.11) of [golub2013matrix].

The proof is `Arnoldi.span_vec` for $A^* A$. -/
theorem span_rightVec (k : ℕ) :
    Submodule.span 𝕜 (rightVec A Astar v '' Set.Iio k) = subspace (Astar ∘ₗ A) v k :=
  Arnoldi.span_vec _ _ k

/-- For every $k$, the left Golub–Kahan vectors $u_0, \dots, u_{k-1}$ span the Krylov subspace
$$\operatorname{span}\{u_0, \dots, u_{k-1}\} = \mathcal{K}_k(A A^*, A v).$$
This is equation (10.4.12) of [golub2013matrix].

The proof is `Arnoldi.span_vec` for $A A^*$ from $A v$. -/
theorem span_leftVec (k : ℕ) :
    Submodule.span 𝕜 (leftVec A Astar v '' Set.Iio k) = subspace (A ∘ₗ Astar) (A v) k :=
  Arnoldi.span_vec _ _ k

private theorem semiconj_right : Function.Semiconj A (Astar ∘ₗ A) (A ∘ₗ Astar) := fun _ => rfl

private theorem eq_sum_leftVec {x : F} {m : ℕ} (hx : x ∈ subspace (A ∘ₗ Astar) (A v) m) :
    x = ∑ i ∈ range m, inner 𝕜 (leftVec A Astar v i) x • leftVec A Astar v i :=
  Arnoldi.eq_sum_inner_smul_vec _ _ hx

private theorem eq_sum_rightVec {x : E} {m : ℕ} (hx : x ∈ subspace (Astar ∘ₗ A) v m) :
    x = ∑ i ∈ range m, inner 𝕜 (rightVec A Astar v i) x • rightVec A Astar v i :=
  Arnoldi.eq_sum_inner_smul_vec _ _ hx

/-- The image of a right vector lies in a left Krylov subspace:
$A v_j \in \mathcal{K}_{j+1}(A A^*, A v)$. -/
theorem apply_rightVec_mem (j : ℕ) :
    A (rightVec A Astar v j) ∈ subspace (A ∘ₗ Astar) (A v) (j + 1) :=
  Arnoldi.apply_vec_mem_subspace_of_semiconj (semiconj_right A Astar) (s := 0)
    (by rw [pow_zero, Module.End.one_apply]) j

/-- The image of a left vector lies in a right Krylov subspace:
$A^* u_j \in \mathcal{K}_{j+2}(A^* A, v)$. -/
theorem adjoint_apply_leftVec_mem (j : ℕ) :
    Astar (leftVec A Astar v j) ∈ subspace (Astar ∘ₗ A) v (j + 2) :=
  Arnoldi.apply_vec_mem_subspace_of_semiconj (semiconj_right Astar A) (s := 1)
    (by rw [pow_one]; rfl) j

private theorem alpha_spec (j : ℕ) :
    0 ≤ alpha A Astar v j ∧
      inner 𝕜 (leftVec A Astar v j) (A (rightVec A Astar v j)) = (alpha A Astar v j : 𝕜) ∧
      (alpha A Astar v j = 0 → leftVec A Astar v j = 0) := by
  obtain ⟨r, hr, heq, h0⟩ := Arnoldi.inner_vec_apply_vec_of_semiconj (semiconj_right A Astar)
    (b := v) (c := A v) (s := 0) (by rw [pow_zero, Module.End.one_apply]) j
  have ha : alpha A Astar v j = r := by
    rw [alpha]
    exact (congrArg RCLike.re heq).trans (RCLike.ofReal_re r)
  rw [ha]
  exact ⟨hr, heq, h0⟩

private theorem beta_spec (j : ℕ) :
    0 ≤ beta A Astar v j ∧
      inner 𝕜 (rightVec A Astar v (j + 1)) (Astar (leftVec A Astar v j)) =
        (beta A Astar v j : 𝕜) ∧
      (beta A Astar v j = 0 → rightVec A Astar v (j + 1) = 0) := by
  obtain ⟨r, hr, heq, h0⟩ := Arnoldi.inner_vec_apply_vec_of_semiconj (semiconj_right Astar A)
    (b := A v) (c := v) (s := 1) (by rw [pow_one]; rfl) j
  have hb : beta A Astar v j = r := by
    rw [beta]
    exact (congrArg RCLike.re heq).trans (RCLike.ofReal_re r)
  rw [hb]
  exact ⟨hr, heq, h0⟩

/-- The diagonal coefficients are nonnegative: $\alpha_j \ge 0$ for every $j$.

In Algorithm 10.4.1 of [golub2013matrix], $\alpha_j$ is computed as a norm. -/
theorem alpha_nonneg (j : ℕ) : 0 ≤ alpha A Astar v j :=
  (alpha_spec A Astar v j).1

/-- The superdiagonal coefficients are nonnegative: $\beta_j \ge 0$ for every $j$.

In Algorithm 10.4.1 of [golub2013matrix], $\beta_j$ is computed as a norm. -/
theorem beta_nonneg (j : ℕ) : 0 ≤ beta A Astar v j :=
  (beta_spec A Astar v j).1

/-- The inner product that defines $\alpha_j$ is real:
$$\langle u_j, A v_j \rangle = \alpha_j.$$
-/
theorem inner_leftVec_apply_rightVec (j : ℕ) :
    inner 𝕜 (leftVec A Astar v j) (A (rightVec A Astar v j)) = (alpha A Astar v j : 𝕜) :=
  (alpha_spec A Astar v j).2.1

/-- The inner product that defines $\beta_j$ is real:
$$\langle v_{j+1}, A^* u_j \rangle = \beta_j.$$
-/
theorem inner_rightVec_adjoint_apply_leftVec (j : ℕ) :
    inner 𝕜 (rightVec A Astar v (j + 1)) (Astar (leftVec A Astar v j)) = (beta A Astar v j : 𝕜) :=
  (beta_spec A Astar v j).2.1

/-- Breakdown of the left family: if $\alpha_j = 0$, then $u_j = 0$. -/
theorem leftVec_eq_zero_of_alpha_eq_zero {j : ℕ} (h : alpha A Astar v j = 0) :
    leftVec A Astar v j = 0 :=
  (alpha_spec A Astar v j).2.2 h

/-- Breakdown of the right family: if $\beta_j = 0$, then $v_{j+1} = 0$. -/
theorem rightVec_eq_zero_of_beta_eq_zero {j : ℕ} (h : beta A Astar v j = 0) :
    rightVec A Astar v (j + 1) = 0 :=
  (beta_spec A Astar v j).2.2 h

private theorem inner_leftVec_apply_rightVec_of_lt {i j : ℕ} (h : j < i) :
    inner 𝕜 (leftVec A Astar v i) (A (rightVec A Astar v j)) = 0 :=
  Submodule.inner_left_of_mem_orthogonal
    (subspace_mono (A ∘ₗ Astar) (A v) (by omega : j + 1 ≤ i) (apply_rightVec_mem A Astar v j))
    (Arnoldi.vec_mem_orthogonal _ _ i)

private theorem inner_rightVec_adjoint_apply_leftVec_of_lt {i j : ℕ} (h : j + 1 < i) :
    inner 𝕜 (rightVec A Astar v i) (Astar (leftVec A Astar v j)) = 0 :=
  Submodule.inner_left_of_mem_orthogonal
    (subspace_mono (Astar ∘ₗ A) v (by omega : j + 2 ≤ i) (adjoint_apply_leftVec_mem A Astar v j))
    (Arnoldi.vec_mem_orthogonal _ _ i)

/-- The first step of the recurrence (10.4.2) of [golub2013matrix]:
$$A v_0 = \alpha_0 u_0.$$
-/
theorem apply_rightVec_zero :
    A (rightVec A Astar v 0) = (alpha A Astar v 0 : 𝕜) • leftVec A Astar v 0 := by
  refine (eq_sum_leftVec A Astar v (apply_rightVec_mem A Astar v 0)).trans ?_
  rw [sum_range_one, inner_leftVec_apply_rightVec]

/-! ### The bidiagonal matrices -/

/-- The **upper bidiagonal matrix** $B_k \in \mathbb{R}^{k \times k}$ of equation (10.4.8) of
[golub2013matrix]. Its entries are $(B_k)_{jj} = \alpha_j$, $(B_k)_{j, j+1} = \beta_j$, and $0$
elsewhere:
$$B_k = \begin{bmatrix} \alpha_0 & \beta_0 & & \\ & \alpha_1 & \ddots & \\ & & \ddots &
  \beta_{k-2} \\ & & & \alpha_{k-1} \end{bmatrix}.$$
-/
noncomputable def bidiag (k : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) = j then alpha A Astar v i else if (i : ℕ) + 1 = j then beta A Astar v i else 0

/-- The **lower bidiagonal matrix** $\bar B_k \in \mathbb{R}^{(k+1) \times k}$, with entries
$(\bar B_k)_{jj} = \alpha_j$, $(\bar B_k)_{j+1, j} = \beta_j$, and $0$ elsewhere. Its first $k$
rows form $B_k^T$ (`GolubKahan.bidiagLower_submatrix_castSucc`).

It is the matrix of $A^*$ in (10.4.10) of [golub2013matrix], $A^H U_k = V_{k+1} \bar B_k$. For
the pair $(A^*, A)$ in place of $(A, A^*)$ it is the matrix $B(1{:}k{+}1, 1{:}k)$ of the lower
bidiagonalization of Paige and Saunders, (10.4.18)–(10.4.19) of [golub2013matrix]. -/
noncomputable def bidiagLower (k : ℕ) : Matrix (Fin (k + 1)) (Fin k) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) = j then alpha A Astar v j else if (i : ℕ) = j + 1 then beta A Astar v j else 0

/-- The entries of $B_k$: $(B_k)_{ij} = \alpha_i$ if $i = j$, $(B_k)_{ij} = \beta_i$ if $i + 1 = j$,
and $(B_k)_{ij} = 0$ otherwise. -/
theorem bidiag_apply {k : ℕ} (i j : Fin k) :
    bidiag A Astar v k i j =
      if (i : ℕ) = j then alpha A Astar v i else if (i : ℕ) + 1 = j then beta A Astar v i
      else 0 :=
  rfl

/-- The entries of $\bar B_k$: $(\bar B_k)_{ij} = \alpha_j$ if $i = j$, $(\bar B_k)_{ij} = \beta_j$
if $i = j + 1$, and $(\bar B_k)_{ij} = 0$ otherwise. -/
theorem bidiagLower_apply {k : ℕ} (i : Fin (k + 1)) (j : Fin k) :
    bidiagLower A Astar v k i j =
      if (i : ℕ) = j then alpha A Astar v j else if (i : ℕ) = j + 1 then beta A Astar v j else 0 :=
  rfl

/-- The matrix $B_k$ is upper bidiagonal: its only nonzero entries lie on the diagonal and the first
superdiagonal.

The shape is `Matrix.IsUpperBidiagonal`. -/
theorem bidiag_isUpperBidiagonal (k : ℕ) : (bidiag A Astar v k).IsUpperBidiagonal := by
  intro i j h
  have h' : (j : ℕ) < i ∨ (i : ℕ) + 1 < j := by
    rcases h with h | ⟨l, hil, hlj⟩
    · exact Or.inl (Fin.lt_def.1 h)
    · exact Or.inr (by rw [Fin.lt_def] at hil hlj; omega)
  rw [bidiag_apply]
  split_ifs <;> first | rfl | omega

/-- The matrix $\bar B_k$ is lower bidiagonal: its only nonzero entries lie on the diagonal and the
first subdiagonal.

The shape is `Matrix.IsLowerBidiagonalRect`, for rectangular matrices. -/
theorem bidiagLower_isLowerBidiagonalRect (k : ℕ) :
    (bidiagLower A Astar v k).IsLowerBidiagonalRect := by
  intro i j h1 h2
  rw [bidiagLower_apply, ite_eq_right h1, ite_eq_right h2]

/-- The first $k$ rows of $\bar B_k \in \mathbb{R}^{(k+1) \times k}$ form the transpose $B_k^T$ of
the upper bidiagonal matrix. -/
theorem bidiagLower_submatrix_castSucc (k : ℕ) :
    (bidiagLower A Astar v k).submatrix Fin.castSucc id = (bidiag A Astar v k)ᵀ := by
  ext i j
  simp only [Matrix.submatrix_apply, id, Matrix.transpose_apply, bidiagLower_apply, bidiag_apply,
    Fin.val_castSucc]
  split_ifs <;> first | rfl | omega

/-! ### The Lanczos vectors of the Jordan–Wielandt operator (preliminaries) -/

private theorem hermitianDilation_toLp (a : E) (b : F) :
    hermitianDilation A Astar (WithLp.toLp 2 (a, b)) = WithLp.toLp 2 (Astar b, A a) :=
  rfl

/-- For a real $c \ge 0$ and a vector $x$ that is either a unit vector or $0$, with $c = 0$ when
$x = 0$, the norm of $c x$ is $c$. -/
private theorem norm_ofReal_smul_eq {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    {c : ℝ} (hc : 0 ≤ c) {x : G} (h0 : x = 0 → c = 0) (h1 : x ≠ 0 → ‖x‖ = 1) :
    ‖(c : 𝕜) • x‖ = c := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [smul_zero, norm_zero, h0 rfl]
  · rw [norm_smul, h1 hx, mul_one, RCLike.norm_ofReal, abs_of_nonneg hc]

/-- For a real $c \ge 0$ and a vector $x$ that is either a unit vector or $0$, with $x = 0$ when
$c = 0$, normalizing $c x$ gives $x$. -/
private theorem inv_norm_smul_smul {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    {c : ℝ} (hc : 0 ≤ c) {x : G} (h0 : c = 0 → x = 0) (h1 : x ≠ 0 → ‖x‖ = 1) :
    (‖(c : 𝕜) • x‖ : 𝕜)⁻¹ • ((c : 𝕜) • x) = x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hc0 : c ≠ 0 := fun h => hx (h0 h)
  rw [norm_smul, h1 hx, mul_one, RCLike.norm_ofReal, abs_of_nonneg hc, smul_smul,
    inv_mul_cancel₀ (RCLike.ofReal_ne_zero.2 hc0), one_smul]

/-- The interleaved family $(v_0, 0), (0, u_0), (v_1, 0), (0, u_1), \dots$ in $E \times F$. -/
private noncomputable def dilVec (l : ℕ) : WithLp 2 (E × F) :=
  if l % 2 = 0 then WithLp.toLp 2 (rightVec A Astar v (l / 2), 0)
  else WithLp.toLp 2 (0, leftVec A Astar v (l / 2))

private theorem dilVec_two_mul (j : ℕ) :
    dilVec A Astar v (2 * j) = WithLp.toLp 2 (rightVec A Astar v j, 0) := by
  simp [dilVec]

private theorem dilVec_two_mul_add_one (j : ℕ) :
    dilVec A Astar v (2 * j + 1) = WithLp.toLp 2 (0, leftVec A Astar v j) := by
  simp [dilVec, show (2 * j + 1) % 2 = 1 by omega, show (2 * j + 1) / 2 = j by omega]

/-- The unnormalized next Lanczos vector of the Jordan–Wielandt operator: $(0, \alpha_j u_j)$ after
the even step $2j$, and $(\beta_j v_{j+1}, 0)$ after the odd step $2j + 1$. -/
private noncomputable def dilW (l : ℕ) : WithLp 2 (E × F) :=
  if l % 2 = 0 then WithLp.toLp 2 (0, (alpha A Astar v (l / 2) : 𝕜) • leftVec A Astar v (l / 2))
  else WithLp.toLp 2 ((beta A Astar v (l / 2) : 𝕜) • rightVec A Astar v (l / 2 + 1), 0)

private theorem dilW_two_mul (j : ℕ) :
    dilW A Astar v (2 * j) =
      WithLp.toLp 2 (0, (alpha A Astar v j : 𝕜) • leftVec A Astar v j) := by
  simp [dilW]

private theorem dilW_two_mul_add_one (j : ℕ) :
    dilW A Astar v (2 * j + 1) =
      WithLp.toLp 2 ((beta A Astar v j : 𝕜) • rightVec A Astar v (j + 1), 0) := by
  simp [dilW, show (2 * j + 1) % 2 = 1 by omega, show (2 * j + 1) / 2 = j by omega]

/-- The unnormalized next vector after step $i$ is orthogonal to the first $i + 1$ interleaved
vectors. -/
private theorem inner_dilVec_dilW {l i : ℕ} (hl : l ≤ i) :
    inner 𝕜 (dilVec A Astar v l) (dilW A Astar v i) = 0 := by
  obtain ⟨a, rfl | rfl⟩ := Nat.even_or_odd' l <;> obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' i
  · simp [dilVec_two_mul, dilW_two_mul]
  · have h0 : inner 𝕜 (rightVec A Astar v a) (rightVec A Astar v (j + 1)) = 0 :=
      Arnoldi.inner_vec_eq_zero _ _ (by omega)
    simp [dilVec_two_mul, dilW_two_mul_add_one, inner_smul_right, h0]
  · have h0 : inner 𝕜 (leftVec A Astar v a) (leftVec A Astar v j) = 0 :=
      Arnoldi.inner_vec_eq_zero _ _ (by omega)
    simp [dilVec_two_mul_add_one, dilW_two_mul, inner_smul_right, h0]
  · simp [dilVec_two_mul_add_one, dilW_two_mul_add_one]

private theorem vec_zero_hermitianDilation :
    Arnoldi.vec (hermitianDilation A Astar) (WithLp.toLp 2 (v, 0)) 0 = dilVec A Astar v 0 := by
  rw [show dilVec A Astar v 0 = WithLp.toLp 2 (rightVec A Astar v 0, 0) from
    dilVec_two_mul A Astar v 0]
  rcases eq_or_ne v 0 with rfl | hv
  · have h0 : ∀ {G : Type _} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] (T : G →ₗ[𝕜] G),
        Arnoldi.vec T 0 0 = 0 := fun T =>
      (Arnoldi.vec_eq_zero_iff_pow_apply_mem T 0 0).2 (by simp)
    have hz : (WithLp.toLp 2 ((0 : E), (0 : F)) : WithLp 2 (E × F)) = 0 := by
      rw [Prod.mk_zero_zero, WithLp.toLp_zero]
    rw [rightVec, h0 (Astar ∘ₗ A), hz]
    exact (Arnoldi.vec_eq_zero_iff_pow_apply_mem _ 0 0).2 (by simp)
  · have hz : (WithLp.toLp 2 (v, (0 : F)) : WithLp 2 (E × F)) ≠ 0 := fun h =>
      hv (by simpa using congrArg (fun z : WithLp 2 (E × F) => (WithLp.ofLp z).1) h)
    rw [Arnoldi.vec_zero _ _ hz, rightVec, Arnoldi.vec_zero _ _ hv, WithLp.norm_toLp_fst,
      ← WithLp.toLp_smul, Prod.smul_mk, smul_zero]

/-- One step of the Arnoldi recurrence: if $T q_i = x + y$, where $q_i$ is the Arnoldi vector of
step $i$, $x$ is orthogonal to $\mathcal{K}_{i+1}(T, b)$ and $y \in \mathcal{K}_{i+1}(T, b)$,
then the unnormalized next Arnoldi vector is $x$. -/
private theorem w_eq_of_apply_eq_add {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    {T : G →ₗ[𝕜] G} {b x y : G} {i : ℕ}
    (h : T (Arnoldi.vec T b i) = x + y) (hx : x ∈ (subspace T b (i + 1))ᗮ)
    (hy : y ∈ subspace T b (i + 1)) :
    Arnoldi.w T b i = x := by
  rw [Arnoldi.w_eq_sub_starProjection, h, map_add,
    (Submodule.starProjection_apply_eq_zero_iff (K := subspace T b (i + 1))).2 hx,
    Submodule.starProjection_eq_self_iff.2 hy]
  abel

/-! ### The grades of the two families -/

/-- **Rank–nullity for the two Krylov spaces.** Suppose that the full Krylov space
$\mathcal{K}_\infty(A^* A, v) = \operatorname{span}\{(A^* A)^i v : i \ge 0\}$ is
finite-dimensional. Then
$$\operatorname{grade}(A A^*, A v) + \dim\bigl(\mathcal{K}_\infty(A^* A, v) \cap \ker A\bigr) =
  \operatorname{grade}(A^* A, v).$$

The map $A$ carries $\mathcal{K}_\infty(A^* A, v)$ onto $\mathcal{K}_\infty(A A^*, A v)$, and
the identity is rank–nullity for this restriction. This result does not use that $A^*$ is an
adjoint of $A$. -/
theorem grade_comp_adjoint_add_finrank [FiniteDimensional 𝕜 (fullSubspace (Astar ∘ₗ A) v)] :
    grade (A ∘ₗ Astar) (A v) +
        Module.finrank 𝕜 ↥(fullSubspace (Astar ∘ₗ A) v ⊓ LinearMap.ker A) =
      grade (Astar ∘ₗ A) v := by
  have hmap : (fullSubspace (Astar ∘ₗ A) v).map A = fullSubspace (A ∘ₗ Astar) (A v) :=
    map_fullSubspace_of_semiconj (semiconj_right A Astar) v
  have h := LinearMap.finrank_range_add_finrank_ker (A.domRestrict (fullSubspace (Astar ∘ₗ A) v))
  rw [LinearMap.range_domRestrict, hmap, LinearMap.ker_domRestrict] at h
  have hk : Module.finrank 𝕜 ↥((LinearMap.ker A).comap (fullSubspace (Astar ∘ₗ A) v).subtype) =
      Module.finrank 𝕜 ↥(fullSubspace (Astar ∘ₗ A) v ⊓ LinearMap.ker A) := by
    rw [← Submodule.map_comap_subtype]
    exact ((fullSubspace (Astar ∘ₗ A) v).equivSubtypeMap _).finrank_eq
  unfold grade
  rw [← hk]
  exact h

variable {A Astar} (hadj : LinearMap.IsAdjointPair (innerₛₗ 𝕜).flip (innerₛₗ 𝕜).flip A Astar)
include hadj

private theorem inner_leftVec_apply_rightVec_of_add_two_le {i j : ℕ} (h : i + 2 ≤ j) :
    inner 𝕜 (leftVec A Astar v i) (A (rightVec A Astar v j)) = 0 := by
  rw [← hadj.inner_apply_eq]
  exact Submodule.inner_right_of_mem_orthogonal
    (subspace_mono (Astar ∘ₗ A) v h (adjoint_apply_leftVec_mem A Astar v i))
    (Arnoldi.vec_mem_orthogonal _ _ j)

private theorem inner_rightVec_adjoint_apply_leftVec_of_gt {i j : ℕ} (h : i < j) :
    inner 𝕜 (rightVec A Astar v i) (Astar (leftVec A Astar v j)) = 0 := by
  have h0 : inner 𝕜 (leftVec A Astar v j) (A (rightVec A Astar v i)) = 0 :=
    Submodule.inner_left_of_mem_orthogonal
      (subspace_mono (A ∘ₗ Astar) (A v) (by omega : i + 1 ≤ j) (apply_rightVec_mem A Astar v i))
      (Arnoldi.vec_mem_orthogonal _ _ j)
  rw [← inner_conj_symm, hadj.inner_apply_eq, h0, map_zero]

/-- Let $A^*$ be an adjoint of $A$. Then the left vector $u_j$ has the component $\beta_j$ along
$A v_{j+1}$:
$$\langle u_j, A v_{j+1} \rangle = \beta_j.$$
-/
theorem inner_leftVec_apply_rightVec_succ (j : ℕ) :
    inner 𝕜 (leftVec A Astar v j) (A (rightVec A Astar v (j + 1))) = (beta A Astar v j : 𝕜) := by
  rw [← hadj.inner_apply_eq, ← inner_conj_symm, inner_rightVec_adjoint_apply_leftVec,
    RCLike.conj_ofReal]

/-- Let $A^*$ be an adjoint of $A$. Then the right vector $v_j$ has the component $\alpha_j$ along
$A^* u_j$:
$$\langle v_j, A^* u_j \rangle = \alpha_j.$$
-/
theorem inner_rightVec_adjoint_apply_leftVec_self (j : ℕ) :
    inner 𝕜 (rightVec A Astar v j) (Astar (leftVec A Astar v j)) = (alpha A Astar v j : 𝕜) := by
  rw [← inner_conj_symm, hadj.inner_apply_eq, inner_leftVec_apply_rightVec, RCLike.conj_ofReal]

/-- The recurrence (10.4.2) of [golub2013matrix]. Let $A^*$ be an adjoint of $A$, that is $\langle
A^* u, x \rangle = \langle u, A x \rangle$ for all $u \in F$ and $x \in E$. Then for every
$j \ge 0$,
$$A v_{j+1} = \beta_j u_j + \alpha_{j+1} u_{j+1}.$$

Indices start at $0$, so this is the book's $A v_{j+2} = \beta_{j+1} u_{j+1} + \alpha_{j+2}
u_{j+2}$. The first step $A v_0 = \alpha_0 u_0$ is `GolubKahan.apply_rightVec_zero`. -/
theorem apply_rightVec (j : ℕ) :
    A (rightVec A Astar v (j + 1)) =
      (beta A Astar v j : 𝕜) • leftVec A Astar v j +
        (alpha A Astar v (j + 1) : 𝕜) • leftVec A Astar v (j + 1) := by
  refine (eq_sum_leftVec A Astar v (apply_rightVec_mem A Astar v (j + 1))).trans ?_
  rw [sum_range_succ, sum_range_succ, sum_eq_zero fun i hi => by
      rw [inner_leftVec_apply_rightVec_of_add_two_le v hadj (by simp at hi; omega), zero_smul],
    zero_add, inner_leftVec_apply_rightVec_succ v hadj, inner_leftVec_apply_rightVec]

/-- The recurrence (10.4.3) of [golub2013matrix]. Let $A^*$ be an adjoint of $A$, that is $\langle
A^* u, x \rangle = \langle u, A x \rangle$ for all $u \in F$ and $x \in E$. Then for every
$j \ge 0$,
$$A^* u_j = \alpha_j v_j + \beta_j v_{j+1}.$$

Indices start at $0$, so this is the book's $A^H u_{j+1} = \alpha_{j+1} v_{j+1} + \beta_{j+1}
v_{j+2}$. -/
theorem adjoint_apply_leftVec (j : ℕ) :
    Astar (leftVec A Astar v j) =
      (alpha A Astar v j : 𝕜) • rightVec A Astar v j +
        (beta A Astar v j : 𝕜) • rightVec A Astar v (j + 1) := by
  refine (eq_sum_rightVec A Astar v (adjoint_apply_leftVec_mem A Astar v j)).trans ?_
  rw [show j + 2 = j + 1 + 1 from rfl, sum_range_succ, sum_range_succ, sum_eq_zero fun i hi => by
      rw [inner_rightVec_adjoint_apply_leftVec_of_gt v hadj (by simp at hi; omega), zero_smul],
    zero_add, inner_rightVec_adjoint_apply_leftVec_self v hadj,
    inner_rightVec_adjoint_apply_leftVec]

/-! ### The link to the Lanczos process of $A^* A$ -/

/-- The Gram form of $A^* A$ on the right vectors: $\langle v_i, (A^* A) v_j \rangle = \langle A
v_i, A v_j \rangle$. -/
private theorem inner_rightVec_comp_apply (i j : ℕ) :
    inner 𝕜 (rightVec A Astar v i) ((Astar ∘ₗ A) (rightVec A Astar v j)) =
      inner 𝕜 (A (rightVec A Astar v i)) (A (rightVec A Astar v j)) := by
  rw [LinearMap.comp_apply, LinearMap.inner_apply_eq_inner_apply_of_adjoint hadj]

/-- The first diagonal Lanczos coefficient of $A^* A$ from $v$. Let $A^*$ be an adjoint of $A$. Then
$$\alpha_0(A^* A) = \alpha_0^2,$$
where $\alpha_0(A^* A)$ is the first diagonal coefficient of the Lanczos process of $A^* A$ from
$v$.

This is the remark after (10.4.12) of [golub2013matrix]. The Lanczos coefficient is
`Lanczos.alpha (Astar ∘ₗ A) v 0`. -/
theorem lanczos_alpha_zero : Lanczos.alpha (Astar ∘ₗ A) v 0 = alpha A Astar v 0 ^ 2 := by
  have key : inner 𝕜 (A (rightVec A Astar v 0)) (A (rightVec A Astar v 0)) =
      ((alpha A Astar v 0 ^ 2 : ℝ) : 𝕜) := by
    nth_rewrite 2 [apply_rightVec_zero]
    rw [inner_smul_right, ← inner_conj_symm, inner_leftVec_apply_rightVec, RCLike.conj_ofReal]
    push_cast
    ring
  rw [Lanczos.alpha, Arnoldi.coeff]
  change RCLike.re (inner 𝕜 (rightVec A Astar v 0) ((Astar ∘ₗ A) (rightVec A Astar v 0))) = _
  rw [inner_rightVec_comp_apply v hadj, key, RCLike.ofReal_re]

/-- The later diagonal Lanczos coefficients of $A^* A$ from $v$. Let $A^*$ be an adjoint of $A$.
Then for every $j \ge 0$,
$$\alpha_{j+1}(A^* A) = \alpha_{j+1}^2 + \beta_j^2,$$
where $\alpha_{j+1}(A^* A)$ is the diagonal coefficient of step $j + 1$ of the Lanczos process
of $A^* A$ from $v$.

This is the remark after (10.4.12) of [golub2013matrix]. The Lanczos coefficient is
`Lanczos.alpha (Astar ∘ₗ A) v (j + 1)`. -/
theorem lanczos_alpha_succ (j : ℕ) :
    Lanczos.alpha (Astar ∘ₗ A) v (j + 1) = alpha A Astar v (j + 1) ^ 2 + beta A Astar v j ^ 2 := by
  have key : inner 𝕜 (A (rightVec A Astar v (j + 1))) (A (rightVec A Astar v (j + 1))) =
      ((alpha A Astar v (j + 1) ^ 2 + beta A Astar v j ^ 2 : ℝ) : 𝕜) := by
    nth_rewrite 2 [apply_rightVec v hadj]
    rw [inner_add_right, inner_smul_right, inner_smul_right, ← inner_conj_symm,
      inner_leftVec_apply_rightVec_succ v hadj, ← inner_conj_symm (A _) (leftVec A Astar v (j + 1)),
      inner_leftVec_apply_rightVec, RCLike.conj_ofReal, RCLike.conj_ofReal]
    push_cast
    ring
  rw [Lanczos.alpha, Arnoldi.coeff]
  change RCLike.re (inner 𝕜 (rightVec A Astar v (j + 1))
    ((Astar ∘ₗ A) (rightVec A Astar v (j + 1)))) = _
  rw [inner_rightVec_comp_apply v hadj, key, RCLike.ofReal_re]

/-- The off-diagonal Lanczos coefficients of $A^* A$ from $v$. Let $A^*$ be an adjoint of $A$. Then
for every $j \ge 0$,
$$\beta_j(A^* A) = \alpha_j \beta_j,$$
where $\beta_j(A^* A)$ is the off-diagonal coefficient of step $j$ of the Lanczos process of
$A^* A$ from $v$.

This is the remark after (10.4.12) of [golub2013matrix]. The Lanczos coefficient is
`Lanczos.beta (Astar ∘ₗ A) v j`. -/
theorem lanczos_beta_eq (j : ℕ) :
    Lanczos.beta (Astar ∘ₗ A) v j = alpha A Astar v j * beta A Astar v j := by
  have key : inner 𝕜 (A (rightVec A Astar v (j + 1))) (A (rightVec A Astar v j)) =
      ((alpha A Astar v j * beta A Astar v j : ℝ) : 𝕜) := by
    rw [apply_rightVec v hadj, inner_add_left, inner_smul_left, inner_smul_left,
      inner_leftVec_apply_rightVec, inner_leftVec_apply_rightVec_of_lt A Astar v j.lt_succ_self,
      RCLike.conj_ofReal]
    push_cast
    ring
  refine RCLike.ofReal_injective (K := 𝕜) ?_
  rw [Lanczos.coe_beta, Arnoldi.coeff]
  change inner 𝕜 (rightVec A Astar v (j + 1)) ((Astar ∘ₗ A) (rightVec A Astar v j)) = _
  rw [inner_rightVec_comp_apply v hadj, key]

/-- The bidiagonal matrix factors the Lanczos matrix of $A^* A$. Let $A^*$ be an adjoint of $A$.
Then for every $k$,
$$B_k^H B_k = T_k(A^* A),$$
where $T_k(A^* A)$ is the $k \times k$ tridiagonal Lanczos matrix of $A^* A$ from $v$. Since
$B_k$ is real, $B_k^H = B_k^T$.

So the Golub–Kahan process is the Lanczos process of $A^* A$ with its tridiagonal matrix in
factored form. This is the remark after (10.4.12) of [golub2013matrix]. The Lanczos matrix is
`Lanczos.tridiag (Astar ∘ₗ A) v k`. -/
theorem bidiag_conjTranspose_mul_bidiag (k : ℕ) :
    (bidiag A Astar v k)ᴴ * bidiag A Astar v k = Lanczos.tridiag (Astar ∘ₗ A) v k := by
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  ext i j
  rw [Matrix.mul_apply, Lanczos.tridiag_apply]
  simp only [Matrix.transpose_apply, bidiag_apply]
  rcases lt_trichotomy (i : ℕ) j with hij | hij | hij
  · rw [ite_eq_right hij.ne]
    by_cases h1 : (i : ℕ) + 1 = j
    · rw [ite_eq_left h1, lanczos_beta_eq v hadj, Fintype.sum_eq_single i]
      · rw [ite_eq_left rfl, ite_eq_right (by omega), ite_eq_left h1]
      · intro l hl
        have hl' : (l : ℕ) ≠ i := fun h => hl (Fin.ext h)
        split_ifs <;> first | rfl | omega | ring
    · rw [ite_eq_right h1, ite_eq_right (by omega)]
      refine Fintype.sum_eq_zero _ fun l => ?_
      split_ifs <;> first | rfl | omega | ring
  · have hij' : i = j := Fin.ext hij
    subst hij'
    rw [ite_eq_left rfl]
    rcases Nat.eq_zero_or_eq_succ_pred (i : ℕ) with h0 | hs
    · rw [Fintype.sum_eq_single i, h0, lanczos_alpha_zero v hadj]
      · simp only [ite_eq_left]
        simp [sq]
      · intro l hl
        have hl' : (l : ℕ) ≠ i := fun h => hl (Fin.ext h)
        split_ifs <;> first | rfl | omega | ring
    · have hp : (i : ℕ) - 1 < k := by omega
      rw [Fintype.sum_eq_add i ⟨(i : ℕ) - 1, hp⟩ (fun h => by
          have := congrArg Fin.val h; simp at this; omega) (fun l hl => by
          have h1 : (l : ℕ) ≠ i := fun h => hl.1 (Fin.ext h)
          have h2 : (l : ℕ) ≠ (i : ℕ) - 1 := fun h => hl.2 (Fin.ext h)
          split_ifs <;> first | rfl | omega | ring)]
      have hL : Lanczos.alpha (Astar ∘ₗ A) v i =
          alpha A Astar v i ^ 2 + beta A Astar v ((i : ℕ) - 1) ^ 2 := by
        obtain ⟨i', hi'⟩ : ∃ i', (i : ℕ) = i' + 1 := ⟨(i : ℕ) - 1, by omega⟩
        rw [hi', lanczos_alpha_succ v hadj, Nat.add_sub_cancel]
      rw [hL]
      dsimp only
      split_ifs <;> first | omega | ring
  · rw [ite_eq_right hij.ne', ite_eq_right (by omega)]
    by_cases h1 : (j : ℕ) + 1 = i
    · rw [ite_eq_left h1, lanczos_beta_eq v hadj, Fintype.sum_eq_single j]
      · rw [ite_eq_right (by omega), ite_eq_left h1, ite_eq_left rfl]
        ring
      · intro l hl
        have hl' : (l : ℕ) ≠ j := fun h => hl (Fin.ext h)
        split_ifs <;> first | rfl | omega | ring
    · rw [ite_eq_right h1]
      refine Fintype.sum_eq_zero _ fun l => ?_
      split_ifs <;> first | rfl | omega | ring

/-! ### The bidiagonal relation of $A^*$ as a Hessenberg relation, and the LSQR residual -/

/-- The recurrence (10.4.3) as a Hessenberg relation between two families. Let $A^*$ be an adjoint
of $A$. Then $A^*$ satisfies
$$A^* u_j = \sum_{i \le j+1} h_{ij} v_i$$
with the lower bidiagonal coefficients $h_{jj} = \alpha_j$, $h_{j+1, j} = \beta_j$ and
$h_{ij} = 0$ otherwise, which are the entries of $\bar B_k$.

The relation is `Krylov.HessenbergRelation₂` for $A^*$, from the left vectors $u_j$ to the right
vectors $v_j$. -/
theorem hessenbergRelation₂ :
    HessenbergRelation₂ Astar (leftVec A Astar v) (rightVec A Astar v) fun i j =>
      ((if i = j then alpha A Astar v j else if i = j + 1 then beta A Astar v j else 0 : ℝ) :
        𝕜) := by
  refine ⟨fun j => ?_, fun i j h => ?_⟩
  · rw [adjoint_apply_leftVec v hadj, show j + 2 = j + 1 + 1 from rfl, sum_range_succ,
      sum_range_succ, sum_eq_zero, zero_add]
    · simp
    · intro i hi
      have : i < j := by simpa using hi
      rw [ite_eq_right (by omega), ite_eq_right (by omega), RCLike.ofReal_zero, zero_smul]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), RCLike.ofReal_zero]

/-- Let $A^*$ be an adjoint of $A$. Then the kernel of $A$ meets the full Krylov space
$\mathcal{K}_\infty(A^* A, v)$ in a subspace of dimension at most $1$.

An element $x = c v + A^* y$ of the intersection with $\langle v, x \rangle = 0$ has $\|x\|^2 =
\bar c \, \overline{\langle v, x \rangle} + \overline{\langle y, A x \rangle} = 0$. So the map
$x \mapsto \langle v, x \rangle$ is injective on the intersection. -/
theorem finrank_fullSubspace_inf_ker_le_one :
    Module.finrank 𝕜 ↥(fullSubspace (Astar ∘ₗ A) v ⊓ LinearMap.ker A) ≤ 1 := by
  set S := fullSubspace (Astar ∘ₗ A) v ⊓ LinearMap.ker A
  have hle : fullSubspace (Astar ∘ₗ A) v ≤ (𝕜 ∙ v) ⊔ LinearMap.range Astar := by
    rw [fullSubspace, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    cases i with
    | zero => exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self v)
    | succ i =>
      refine Submodule.mem_sup_right ⟨A (((Astar ∘ₗ A) ^ i) v), ?_⟩
      change Astar (A (((Astar ∘ₗ A) ^ i) v)) = ((Astar ∘ₗ A) ^ (i + 1)) v
      rw [pow_succ', Module.End.mul_apply]
      rfl
  let f : S →ₗ[𝕜] 𝕜 := (innerₛₗ 𝕜 v).comp S.subtype
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨x, hxK, hxA⟩ hx
    rw [LinearMap.mem_ker] at hx
    have hxA' : A x = 0 := hxA
    change inner 𝕜 v x = 0 at hx
    suffices hx0 : x = 0 from Subtype.ext hx0
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (hle hxK)
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    obtain ⟨w, rfl⟩ := LinearMap.mem_range.1 hz
    have e1 : inner 𝕜 x v = 0 := by rw [← inner_conj_symm, hx, map_zero]
    have e2 : inner 𝕜 x (Astar w) = 0 := by
      rw [← inner_conj_symm, hadj.inner_apply_eq, hxA', inner_zero_right, map_zero]
    have hxx : inner 𝕜 x x = 0 := by
      nth_rewrite 2 [← hyz]
      rw [inner_add_right, inner_smul_right, e1, e2, mul_zero, add_zero]
    exact inner_self_eq_zero.1 hxx
  calc Module.finrank 𝕜 S ≤ Module.finrank 𝕜 𝕜 := LinearMap.finrank_le_finrank_of_injective hf
    _ = 1 := Module.finrank_self 𝕜

/-- The grades of the two Golub–Kahan families differ by at most one. Let $A^*$ be an adjoint of
$A$, and suppose that the full Krylov space $\mathcal{K}_\infty(A^* A, v)$ is
finite-dimensional. Then either
$$\operatorname{grade}(A A^*, A v) = \operatorname{grade}(A^* A, v) \quad \text{or} \quad
  \operatorname{grade}(A A^*, A v) + 1 = \operatorname{grade}(A^* A, v).$$

By `GolubKahan.grade_comp_adjoint_add_finrank`, the second case holds exactly when $\ker A$
meets $\mathcal{K}_\infty(A^* A, v)$ nontrivially. This lines up the breakdown statements "if
$\alpha_k = 0$" and "if $\beta_k = 0$" of [golub2013matrix], §10.4.1. -/
theorem grade_comp_adjoint [FiniteDimensional 𝕜 (fullSubspace (Astar ∘ₗ A) v)] :
    grade (A ∘ₗ Astar) (A v) = grade (Astar ∘ₗ A) v ∨
      grade (A ∘ₗ Astar) (A v) + 1 = grade (Astar ∘ₗ A) v := by
  have h1 := grade_comp_adjoint_add_finrank A Astar v
  have h2 := finrank_fullSubspace_inf_ker_le_one v hadj
  omega

omit hadj in
private theorem map_bidiagLower_eq_hessenbergOf (k : ℕ) :
    (bidiagLower A Astar v k).map (algebraMap ℝ 𝕜) =
      hessenbergOf (fun i j =>
        ((if i = j then alpha A Astar v j else if i = j + 1 then beta A Astar v j else 0 : ℝ) : 𝕜))
        k := by
  ext i j
  simp only [Matrix.map_apply, bidiagLower_apply, hessenbergOf, Matrix.of_apply,
    RCLike.algebraMap_eq_ofReal]

/-- **The LSQR residual**, from the lower bidiagonalization (10.4.19) of [golub2013matrix], §11.4.2.
Let $A^*$ be an adjoint of $A$, let $u \in F$ with $\|u\| = 1$, and let $b \in F$, $x_0 \in E$
and $\beta \in \mathbb{K}$ satisfy $b - A x_0 = \beta u$. Run the Golub–Kahan process of the
pair $(A^*, A)$ from $u$: this gives vectors $u_j \in F$, vectors $v_j \in E$, and the lower
bidiagonal matrix $\bar B_k \in \mathbb{R}^{(k+1) \times k}$ of that process. Then for every $k$
and every $y \in \mathbb{K}^k$,
$$b - A\Bigl(x_0 + \sum_{j < k} y_j v_j\Bigr) = \sum_{i \le k} (\beta e_1 - \bar B_k y)_i \,
  u_i.$$
In matrix form, $b - A(x_0 + V_k y) = U_{k+1}(\beta e_1 - \bar B_k y)$.

The process of Paige and Saunders is the Golub–Kahan process of $(A^*, A)$: its $u_j$ are
`GolubKahan.rightVec Astar A u j`, its $v_j$ are `GolubKahan.leftVec Astar A u j`, and its
matrix is `GolubKahan.bidiagLower Astar A u k`. The vector $\beta e_1$ is
`Krylov.firstVec β (k + 1)`. The proof is an instance of
`Krylov.HessenbergRelation₂.residual_eq`. -/
theorem residual_eq {u : F} (hu : ‖u‖ = 1) {b : F} {x₀ : E} {β : 𝕜} (hr : b - A x₀ = β • u)
    (k : ℕ) (y : Fin k → 𝕜) :
    b - A (x₀ + ∑ j, y j • leftVec Astar A u j) =
      ∑ i : Fin (k + 1), (firstVec β (k + 1) -
        ((bidiagLower Astar A u k).map (algebraMap ℝ 𝕜)) *ᵥ y) i • rightVec Astar A u i := by
  have hrel := hessenbergRelation₂ (A := Astar) (Astar := A) u hadj.swap_inner
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have h0 : rightVec Astar A u 0 = u := by
    rw [rightVec, Arnoldi.vec_zero _ _ hu0, hu]
    simp
  rw [map_bidiagLower_eq_hessenbergOf]
  exact hrel.residual_eq (by rw [h0]; exact hr) k y

/-! ### The Lanczos process of the Jordan–Wielandt operator -/

/-- Induction step for the Jordan–Wielandt operator: if its first $i + 1$ Lanczos vectors from
$(v, 0)$ are the interleaved vectors, then its unnormalized next vector after step $i$ is
$(0, \alpha_j u_j)$ for $i = 2j$ and $(\beta_j v_{j+1}, 0)$ for $i = 2j + 1$. -/
private theorem w_hermitianDilation_of_forall {i : ℕ}
    (ih : ∀ l ≤ i, Arnoldi.vec (hermitianDilation A Astar) (WithLp.toLp 2 (v, 0)) l =
      dilVec A Astar v l) :
    Arnoldi.w (hermitianDilation A Astar) (WithLp.toLp 2 (v, 0)) i = dilW A Astar v i := by
  have hx : dilW A Astar v i ∈
      (subspace (hermitianDilation A Astar) (WithLp.toLp 2 (v, 0)) (i + 1))ᗮ := by
    rw [← Arnoldi.span_vec, Submodule.mem_orthogonal_span]
    rintro _ ⟨l, hl, rfl⟩
    rw [ih l (Nat.lt_succ_iff.1 hl)]
    exact inner_dilVec_dilW A Astar v (Nat.lt_succ_iff.1 hl)
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' i
  · rw [dilW_two_mul] at hx ⊢
    cases j with
    | zero =>
      refine w_eq_of_apply_eq_add (y := 0) ?_ hx (Submodule.zero_mem _)
      rw [ih (2 * 0) le_rfl, dilVec_two_mul, hermitianDilation_toLp, map_zero,
        apply_rightVec_zero, add_zero]
    | succ j =>
      refine w_eq_of_apply_eq_add (y := (beta A Astar v j : 𝕜) •
          Arnoldi.vec (hermitianDilation A Astar) (WithLp.toLp 2 (v, 0)) (2 * j + 1)) ?_ hx
        (Submodule.smul_mem _ _ (Arnoldi.vec_mem_subspace_of_lt _ _ (by omega)))
      rw [ih (2 * (j + 1)) le_rfl, ih (2 * j + 1) (by omega), dilVec_two_mul,
        dilVec_two_mul_add_one, hermitianDilation_toLp, map_zero, apply_rightVec v hadj,
        ← WithLp.toLp_smul, ← WithLp.toLp_add, Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero,
        add_comm]
  · rw [dilW_two_mul_add_one] at hx ⊢
    refine w_eq_of_apply_eq_add (y := (alpha A Astar v j : 𝕜) •
        Arnoldi.vec (hermitianDilation A Astar) (WithLp.toLp 2 (v, 0)) (2 * j)) ?_ hx
      (Submodule.smul_mem _ _ (Arnoldi.vec_mem_subspace_of_lt _ _ (by omega)))
    rw [ih (2 * j + 1) le_rfl, ih (2 * j) (by omega), dilVec_two_mul, dilVec_two_mul_add_one,
      hermitianDilation_toLp, map_zero, adjoint_apply_leftVec v hadj, ← WithLp.toLp_smul,
      ← WithLp.toLp_add, Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero, add_comm]

/-- The Lanczos vectors of the Jordan–Wielandt operator from $(v, 0)$ are the interleaved vectors
$(v_0, 0), (0, u_0), (v_1, 0), (0, u_1), \dots$. -/
private theorem vec_hermitianDilation_eq_dilVec (i : ℕ) :
    Arnoldi.vec (hermitianDilation A Astar) (WithLp.toLp 2 (v, 0)) i = dilVec A Astar v i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    cases i with
    | zero => exact vec_zero_hermitianDilation A Astar v
    | succ i =>
      have ih' : ∀ l ≤ i, Arnoldi.vec (hermitianDilation A Astar) (WithLp.toLp 2 (v, 0)) l =
          dilVec A Astar v l := fun l hl => ih l (Nat.lt_succ_of_le hl)
      rw [Arnoldi.vec_succ_eq, w_hermitianDilation_of_forall v hadj ih']
      obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' i
      · rw [dilW_two_mul, dilVec_two_mul_add_one, ← WithLp.toLp_smul, Prod.smul_mk, smul_zero,
          WithLp.norm_toLp_snd, inv_norm_smul_smul (alpha_nonneg A Astar v j)
            (leftVec_eq_zero_of_alpha_eq_zero A Astar v)
            (Arnoldi.norm_vec_eq_one_of_ne_zero _ _)]
      · rw [dilW_two_mul_add_one, show 2 * j + 1 + 1 = 2 * (j + 1) by ring, dilVec_two_mul,
          ← WithLp.toLp_smul, Prod.smul_mk, smul_zero, WithLp.norm_toLp_fst,
          inv_norm_smul_smul (beta_nonneg A Astar v j)
            (rightVec_eq_zero_of_beta_eq_zero A Astar v)
            (Arnoldi.norm_vec_eq_one_of_ne_zero _ _)]

/-- The even Lanczos vectors of the Jordan–Wielandt operator. Let $A^*$ be an adjoint of $A$, and
let $J(x, y) = (A^* y, A x)$ on $E \times F$. Then the Lanczos vector of step $2j$ of $J$ from
$(v, 0)$ is $(v_j, 0)$.

This is part of §10.4.3 of [golub2013matrix]. The operator $J$ is
`LinearMap.hermitianDilation A Astar` on `WithLp 2 (E × F)`. -/
theorem vec_hermitianDilation_two_mul (j : ℕ) :
    Arnoldi.vec (hermitianDilation A Astar) (WithLp.toLp 2 (v, 0)) (2 * j) =
      WithLp.toLp 2 (rightVec A Astar v j, 0) := by
  rw [vec_hermitianDilation_eq_dilVec v hadj, dilVec_two_mul]

/-- The odd Lanczos vectors of the Jordan–Wielandt operator. Let $A^*$ be an adjoint of $A$, and let
$J(x, y) = (A^* y, A x)$ on $E \times F$. Then the Lanczos vector of step $2j + 1$ of $J$ from
$(v, 0)$ is $(0, u_j)$.

This is part of §10.4.3 of [golub2013matrix]. The operator $J$ is
`LinearMap.hermitianDilation A Astar` on `WithLp 2 (E × F)`. -/
theorem vec_hermitianDilation_two_mul_add_one (j : ℕ) :
    Arnoldi.vec (hermitianDilation A Astar) (WithLp.toLp 2 (v, 0)) (2 * j + 1) =
      WithLp.toLp 2 (0, leftVec A Astar v j) := by
  rw [vec_hermitianDilation_eq_dilVec v hadj, dilVec_two_mul_add_one]

/-- The Lanczos process of the Jordan–Wielandt operator has zero diagonal. Let $A^*$ be an adjoint
of $A$, and let $J(x, y) = (A^* y, A x)$ on $E \times F$. Then every diagonal Lanczos
coefficient $\alpha_i(J)$ of $J$ from $(v, 0)$ is $0$. -/
theorem lanczos_alpha_hermitianDilation (i : ℕ) :
    Lanczos.alpha (hermitianDilation A Astar) (WithLp.toLp 2 (v, 0)) i = 0 := by
  rw [Lanczos.alpha, Arnoldi.coeff, vec_hermitianDilation_eq_dilVec v hadj]
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' i
  · simp [dilVec_two_mul]
  · simp [dilVec_two_mul_add_one]

/-- The even off-diagonal Lanczos coefficients of the Jordan–Wielandt operator. Let $A^*$ be an
adjoint of $A$, and let $J(x, y) = (A^* y, A x)$ on $E \times F$. Then the off-diagonal Lanczos
coefficient of step $2j$ of $J$ from $(v, 0)$ is
$$\beta_{2j}(J) = \alpha_j.$$
-/
theorem lanczos_beta_hermitianDilation_two_mul (j : ℕ) :
    Lanczos.beta (hermitianDilation A Astar) (WithLp.toLp 2 (v, 0)) (2 * j) =
      alpha A Astar v j := by
  rw [Lanczos.beta, w_hermitianDilation_of_forall v hadj
    (fun l _ => vec_hermitianDilation_eq_dilVec v hadj l), dilW_two_mul, WithLp.norm_toLp_snd]
  refine norm_ofReal_smul_eq (alpha_nonneg A Astar v j) (fun h => ?_)
    (Arnoldi.norm_vec_eq_one_of_ne_zero _ _)
  rw [alpha, h, inner_zero_left, map_zero]

/-- The odd off-diagonal Lanczos coefficients of the Jordan–Wielandt operator. Let $A^*$ be an
adjoint of $A$, and let $J(x, y) = (A^* y, A x)$ on $E \times F$. Then the off-diagonal Lanczos
coefficient of step $2j + 1$ of $J$ from $(v, 0)$ is
$$\beta_{2j+1}(J) = \beta_j.$$
-/
theorem lanczos_beta_hermitianDilation_two_mul_add_one (j : ℕ) :
    Lanczos.beta (hermitianDilation A Astar) (WithLp.toLp 2 (v, 0)) (2 * j + 1) =
      beta A Astar v j := by
  rw [Lanczos.beta, w_hermitianDilation_of_forall v hadj
    (fun l _ => vec_hermitianDilation_eq_dilVec v hadj l), dilW_two_mul_add_one,
    WithLp.norm_toLp_fst]
  refine norm_ofReal_smul_eq (beta_nonneg A Astar v j) (fun h => ?_)
    (Arnoldi.norm_vec_eq_one_of_ne_zero _ _)
  rw [beta, h, inner_zero_left, map_zero]

/-- **The tridiagonal–bidiagonal connection.** Let $A^*$ be an adjoint of $A$, and let
$J(x, y) = (A^* y, A x)$ be the Jordan–Wielandt operator on $E \times F$. Then for every $k$,
the $k \times k$ Lanczos matrix of $J$ from $(v, 0)$ has zero diagonal and the off-diagonal
$\alpha_0, \beta_0, \alpha_1, \beta_1, \dots$:
$$T_k(J) = \begin{bmatrix} 0 & \alpha_0 & & & \\ \alpha_0 & 0 & \beta_0 & & \\ & \beta_0 & 0 &
  \alpha_1 & \\ & & \alpha_1 & 0 & \ddots \\ & & & \ddots & \ddots \end{bmatrix}.$$
Precisely, the entries at $(i, i + 1)$ and $(i + 1, i)$ are $\alpha_{i/2}$ for even $i$ and
$\beta_{(i-1)/2}$ for odd $i$, and all other entries are $0$.

This is §10.4.3 of [golub2013matrix], with (10.4.17). The operator $J$ is
`LinearMap.hermitianDilation A Astar` on `WithLp 2 (E × F)`. The book's matrix
$\begin{bmatrix} 0 & A \\ A^H & 0 \end{bmatrix}$ acts on $F \times E$ from $(0, v)$; the Lean
operator puts the domain factor $E$ first. -/
theorem lanczos_jordanWielandt (k : ℕ) :
    Lanczos.tridiag (hermitianDilation A Astar) (WithLp.toLp 2 (v, 0)) k =
      Matrix.of fun i j : Fin k =>
        if (i : ℕ) + 1 = j then
          (if (i : ℕ) % 2 = 0 then alpha A Astar v (i / 2) else beta A Astar v (i / 2))
        else if (j : ℕ) + 1 = i then
          (if (j : ℕ) % 2 = 0 then alpha A Astar v (j / 2) else beta A Astar v (j / 2))
        else 0 := by
  have hb : ∀ l : ℕ, Lanczos.beta (hermitianDilation A Astar) (WithLp.toLp 2 (v, 0)) l =
      if l % 2 = 0 then alpha A Astar v (l / 2) else beta A Astar v (l / 2) := fun l => by
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' l
    · rw [lanczos_beta_hermitianDilation_two_mul v hadj]
      simp
    · rw [lanczos_beta_hermitianDilation_two_mul_add_one v hadj]
      simp [show (2 * j + 1) % 2 = 1 by omega, show (2 * j + 1) / 2 = j by omega]
  ext i j
  rw [Lanczos.tridiag_apply, Matrix.of_apply, lanczos_alpha_hermitianDilation v hadj, hb, hb]
  split_ifs <;> first | rfl | omega

end Operator

/-! ### Matrix form -/

section Matrix

open Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  (A : Matrix m n 𝕜) (v : EuclideanSpace 𝕜 n)

/-- The matrix $V_k = [v_0 \mid \cdots \mid v_{k-1}] \in \mathbb{K}^{n \times k}$ of right
Golub–Kahan vectors of a matrix $A \in \mathbb{K}^{m \times n}$ from $v \in \mathbb{K}^n$. This
is the matrix $V_k$ of (10.4.9) of [golub2013matrix].

The process runs for the operators `Matrix.toEuclideanLin A` and `Matrix.toEuclideanLin Aᴴ`. -/
noncomputable def rightMatrix (k : ℕ) : Matrix n (Fin k) 𝕜 :=
  Matrix.of fun i j => (rightVec (toEuclideanLin A) (toEuclideanLin Aᴴ) v j).ofLp i

/-- The matrix $U_k = [u_0 \mid \cdots \mid u_{k-1}] \in \mathbb{K}^{m \times k}$ of left
Golub–Kahan vectors of a matrix $A \in \mathbb{K}^{m \times n}$ from $v \in \mathbb{K}^n$. This
is the matrix $U_k$ of (10.4.9) of [golub2013matrix].

The process runs for the operators `Matrix.toEuclideanLin A` and `Matrix.toEuclideanLin Aᴴ`. -/
noncomputable def leftMatrix (k : ℕ) : Matrix m (Fin k) 𝕜 :=
  Matrix.of fun i j => (leftVec (toEuclideanLin A) (toEuclideanLin Aᴴ) v j).ofLp i

/-- For a matrix $A \in \mathbb{K}^{m \times n}$, the matrix $V_k$ of right Golub–Kahan vectors from
$v$ is the matrix of the first $k$ Lanczos vectors of $A^H A$ from $v$.

The Lanczos matrix is `Arnoldi.basisMatrix (Aᴴ * A) v k`. -/
theorem rightMatrix_eq_basisMatrix (k : ℕ) :
    rightMatrix A v k = Arnoldi.basisMatrix (Aᴴ * A) v k := by
  ext i j
  simp only [rightMatrix, Arnoldi.basisMatrix, Matrix.of_apply, rightVec, toEuclideanLin_mul]

/-- For a matrix $A \in \mathbb{K}^{m \times n}$, the matrix $U_k$ of left Golub–Kahan vectors from
$v$ is the matrix of the first $k$ Lanczos vectors of $A A^H$ from $A v$.

The Lanczos matrix is `Arnoldi.basisMatrix (A * Aᴴ) (toEuclideanLin A v) k`. -/
theorem leftMatrix_eq_basisMatrix (k : ℕ) :
    leftMatrix A v k = Arnoldi.basisMatrix (A * Aᴴ) (toEuclideanLin A v) k := by
  ext i j
  simp only [leftMatrix, Arnoldi.basisMatrix, Matrix.of_apply, leftVec, toEuclideanLin_mul]

/-- Let $A \in \mathbb{K}^{m \times n}$ and $v \in \mathbb{K}^n$. If
$k \le \operatorname{grade}(A^H A, v)$, then $V_k$ has orthonormal columns:
$$V_k^H V_k = I.$$
-/
theorem conjTranspose_rightMatrix_mul_self {k : ℕ}
    (hk : k ≤ grade (toEuclideanLin (Aᴴ * A)) v) :
    (rightMatrix A v k)ᴴ * rightMatrix A v k = 1 := by
  rw [rightMatrix_eq_basisMatrix]
  exact Arnoldi.conjTranspose_basisMatrix_mul_self _ _ hk

/-- Let $A \in \mathbb{K}^{m \times n}$ and $v \in \mathbb{K}^n$. If
$k \le \operatorname{grade}(A A^H, A v)$, then $U_k$ has orthonormal columns:
$$U_k^H U_k = I.$$
-/
theorem conjTranspose_leftMatrix_mul_self {k : ℕ}
    (hk : k ≤ grade (toEuclideanLin (A * Aᴴ)) (toEuclideanLin A v)) :
    (leftMatrix A v k)ᴴ * leftMatrix A v k = 1 := by
  rw [leftMatrix_eq_basisMatrix]
  exact Arnoldi.conjTranspose_basisMatrix_mul_self _ _ hk

/-- Equation (10.4.9) of [golub2013matrix]. Let $A \in \mathbb{K}^{m \times n}$ and
$v \in \mathbb{K}^n$. Then for every $k$,
$$A V_k = U_k B_k.$$

The identity holds for every $k$, also past breakdown, where the columns vanish on both sides.
The real matrix $B_k$ is embedded entrywise in $\mathbb{K}^{k \times k}$. -/
theorem mul_rightMatrix (k : ℕ) :
    A * rightMatrix A v k =
      leftMatrix A v k * (bidiag (toEuclideanLin A) (toEuclideanLin Aᴴ) v k).map
        (algebraMap ℝ 𝕜) := by
  ext x j
  have hl : (A * rightMatrix A v k) x j =
      (toEuclideanLin A (rightVec (toEuclideanLin A) (toEuclideanLin Aᴴ) v j)).ofLp x := by
    rw [ofLp_toEuclideanLin]
    rfl
  rw [hl, Matrix.mul_apply]
  simp only [leftMatrix, Matrix.map_apply, Matrix.of_apply, bidiag_apply,
    RCLike.algebraMap_eq_ofReal]
  obtain ⟨j, hj⟩ := j
  cases j with
  | zero =>
    rw [apply_rightVec_zero, Fintype.sum_eq_single ⟨0, hj⟩]
    · simp [RCLike.real_smul_eq_coe_mul, mul_comm]
    · intro l hl
      have hl' : (l : ℕ) ≠ 0 := fun h => hl (Fin.ext h)
      rw [ite_eq_right (by simpa using hl'), ite_eq_right (by simp), RCLike.ofReal_zero, mul_zero]
  | succ j =>
    rw [apply_rightVec v (LinearMap.isAdjointPair_inner_iff.2 fun u x =>
        toEuclideanLin_conjTranspose_inner_left A x u),
      Fintype.sum_eq_add ⟨j, by omega⟩ ⟨j + 1, hj⟩
      (fun h => by simpa using congrArg Fin.val h) (fun l hl => by
        have h1 : (l : ℕ) ≠ j := fun h => hl.1 (Fin.ext h)
        have h2 : (l : ℕ) ≠ j + 1 := fun h => hl.2 (Fin.ext h)
        rw [ite_eq_right (by simpa using h2), ite_eq_right (by simpa using h1),
          RCLike.ofReal_zero, mul_zero])]
    simp [RCLike.real_smul_eq_coe_mul, mul_comm]

/-- Equation (10.4.10) of [golub2013matrix]. Let $A \in \mathbb{K}^{m \times n}$ and
$v \in \mathbb{K}^n$. Then for every $k$,
$$A^H U_k = V_{k+1} \bar B_k,$$
or equivalently $A^H U_k = V_k B_k^T + \beta_{k-1} v_k e_k^T$.

Applied to $A^H$ in place of $A$, this is the relation (10.4.19) of the lower bidiagonalization
of Paige and Saunders. The real matrix $\bar B_k$ is embedded entrywise in
$\mathbb{K}^{(k+1) \times k}$. -/
theorem conjTranspose_mul_leftMatrix (k : ℕ) :
    Aᴴ * leftMatrix A v k =
      rightMatrix A v (k + 1) * (bidiagLower (toEuclideanLin A) (toEuclideanLin Aᴴ) v k).map
        (algebraMap ℝ 𝕜) := by
  ext x j
  have hl : (Aᴴ * leftMatrix A v k) x j =
      (toEuclideanLin Aᴴ (leftVec (toEuclideanLin A) (toEuclideanLin Aᴴ) v j)).ofLp x := by
    rw [ofLp_toEuclideanLin]
    rfl
  rw [hl, Matrix.mul_apply,
    adjoint_apply_leftVec v (LinearMap.isAdjointPair_inner_iff.2 fun u x =>
      toEuclideanLin_conjTranspose_inner_left A x u),
    Fintype.sum_eq_add j.castSucc j.succ Fin.castSucc_lt_succ.ne (fun l hl => by
      have h1 : (l : ℕ) ≠ j := fun h => hl.1 (Fin.ext h)
      have h2 : (l : ℕ) ≠ j + 1 := fun h => hl.2 (Fin.ext h)
      simp only [Matrix.map_apply, bidiagLower_apply, RCLike.algebraMap_eq_ofReal]
      rw [ite_eq_right h1, ite_eq_right h2, RCLike.ofReal_zero, mul_zero])]
  simp [rightMatrix, bidiagLower_apply, RCLike.real_smul_eq_coe_mul, RCLike.algebraMap_eq_ofReal,
    mul_comm]

end Matrix

end GolubKahan

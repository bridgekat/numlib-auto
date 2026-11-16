/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Lie.Classical
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Numlib.Data.Fin.SuccPred
import Numlib.Data.Matrix.Mul
import Numlib.LinearAlgebra.Matrix.Cholesky
import Numlib.LinearAlgebra.Matrix.UnitaryEquiv

/-!
# Updating the QR and Cholesky factorizations

This module proves that the QR factorization and the Cholesky factorization of a real matrix can be
updated by rotations in a few prescribed planes after a small change of the matrix, as in
[golub2013matrix] §6.5, which follows Gill, Golub, Murray and Saunders (1974). For the full QR
factorization $A = QR$ the changes are a rank-one change $A + uv^T$, the deletion or insertion of a
column, and the insertion or deletion of a row. For a Cholesky factorization $A = H^T H$, with $H$
upper triangular with positive diagonal, the changes are the update $A + zz^T$, done by plane
rotations, and the downdate $A - zz^T$, done by hyperbolic rotations. The matrices are real, as in
the book and as for `Matrix.planeRotation`, except where the argument works over any ring.

Each update is an existence theorem: there are rotations in prescribed planes whose product carries
the old factorization to the new one. The restriction to these planes is the structural fact that
makes an update cost $O(n^2)$. Below, $G_a G_{a+1} \cdots G_{a+n-1}$ is a sweep of rotations $G_j$
in the adjacent planes $(j, j+1)$; $[H; z^T]$ is the matrix $H$ with the row $z^T$ appended at the
bottom; $[w^T; R]$ is the matrix $R$ with the row $w^T$ added at the top; and
$S = \operatorname{diag}(I, -1)$ is the signature matrix of (6.5.9).

## Main definitions

* `Matrix.adjacentRotationProd`: the sweep $G_a \cdots G_{a+n-1}$ of rotations in adjacent planes;
  applied on the left it acts bottom-up, and its transpose acts top-down.

## Main results

* `Matrix.exists_adjacentRotationProd_mulVec_eq_zero`: a bottom-up sweep of Givens rotations can
  zero a block of consecutive entries of a vector.
* `Matrix.exists_rotations_triangularize_of_hessenberg`: a top-down sweep of Givens rotations makes
  an upper Hessenberg matrix upper trapezoidal.
* `Matrix.exists_isQR_rankOne_update`: the QR factorization after a rank-one change (§6.5.1).
* `Matrix.IsQR.exists_deleteColumn` and `Matrix.IsQR.exists_insertColumn`: the QR factorization
  after deleting or inserting a column (§6.5.2), with the shape lemmas
  `Matrix.IsQR.conjTranspose_mul_deleteColumn` and `Matrix.IsQR.conjTranspose_mul_insertColumn`.
* `Matrix.IsQR.exists_insertRow`, `Matrix.IsQR.exists_deleteFirstRow` and
  `Matrix.IsQR.exists_deleteRow`: the QR factorization after inserting or deleting a row (§6.5.3),
  with the shape lemma `Matrix.IsQR.conjTranspose_mul_insertRow`.
* `Matrix.transpose_mul_self_fromRows` and `Matrix.transpose_mul_indefiniteDiagonal_mul_fromRows`:
  $[H; z^T]^T [H; z^T] = H^T H + zz^T$ (6.5.6) and $[H; z^T]^T S [H; z^T] = H^T H - zz^T$ (6.5.10).
* `Matrix.transpose_mul_self_eq_of_mem_orthogonalGroup` and
  `Matrix.transpose_mul_self_sub_eq_of_isJOrthogonal`: an orthogonal or $S$-orthogonal reduction of
  a stacked matrix to $[R; 0]$ gives the new Gram matrix $R^T R$ ((6.5.7), (6.5.11)–(6.5.12)).
* `Matrix.transpose_mul_self_sub_eq_of_isJOrthogonal_of_fromRows`: an $S$-orthogonal map from
  $[H; z^T]$ to $[R; z'^T]$ keeps $H^T H - zz^T = R^T R - z' z'^T$.
* `Matrix.fromRows_rotate_step`: one step of either Cholesky sweep keeps the stacked matrix
  triangular.
* `Matrix.exists_choleskyUpdate` and `Matrix.exists_choleskyDowndate`: the Cholesky factor of
  $A + zz^T$ and of a positive definite $A - zz^T$ (§6.5.4).
* `Matrix.hyperbolicDowndate_step`: one hyperbolic downdating step (Theorem 6.5.1 of
  [golub2013matrix]).
* `Matrix.sq_lt_sq_of_posDef_transpose_mul_self_sub`: the hyperbolic rotation of each downdating
  step exists; its proof uses the quadratic form `Matrix.dotProduct_transpose_mul_self_sub_mulVec`.
* `Matrix.isCholesky_diagonal_sign_mul`: multiplying a triangular factor by the signs of its
  diagonal gives the Cholesky factor.

## Proof outline

The QR updates rest on two sweep lemmas of `Numlib.LinearAlgebra.Matrix.QR`. By
`Matrix.prodFwd_adjacentEmbed_mul_apply_eq_zero` (6.5.2), rotations in adjacent planes applied
bottom-up keep an upper trapezoidal matrix upper Hessenberg. By
`Matrix.hasLowerBandwidthRect_zero_of_adjacentRotations`, a top-down sweep that zeroes the
subdiagonal makes an upper Hessenberg matrix upper trapezoidal. The Cholesky downdate sweeps the
planes $(k, \mathrm{last})$ in order. The invariant is that the current stacked matrix $[R'; z'^T]$
has $R'^T R' - z' z'^T = A - zz^T$. Positive definiteness tested on $R'^{-1} e_k$ gives
$|z'_k| < r'_{kk}$, so the hyperbolic rotation of step $k$ exists.

## Implementation notes

* The theorems state what the updates compute, not how. The step-by-step procedures of §6.5 are not
  defined here; the surface library defines them and proves them correct with the two sweep lemmas.
* The adjacent embeddings `Matrix.adjacentEmbed` are in `Numlib.LinearAlgebra.Matrix.PlaneRotation`,
  and the block diagonal matrix `Matrix.consDiag a Q` of §6.5.3 is in
  `Numlib.LinearAlgebra.Matrix.Block`.
* Rectangular shapes use `Matrix.HasLowerBandwidthRect`: upper Hessenberg is lower bandwidth $1$,
  and upper trapezoidal (the factor $R$ of `Matrix.IsQR`) is lower bandwidth $0$.
* The signature $S = \operatorname{diag}(I_n, -1)$ of (6.5.9) is Mathlib's
  `LieAlgebra.Orthogonal.indefiniteDiagonal n Unit`. The stacked matrix $[H; z^T]$ is
  `Matrix.fromRows H (Matrix.replicateRow Unit z)`, so its last row is indexed by `Sum.inr ()`.
* The Cholesky factor is the upper triangular $H = G^T$ of `Matrix.IsCholesky A H`, which states
  $H^H H = A$; the book works with the lower triangular $G$.
* The downdate does not follow the induction of the book on the order through Theorem 6.5.1 and a
  reindexing `Fin (n + 1) ≃ Unit ⊕ Fin n`. It sweeps the planes $(k, \mathrm{last})$ in order, as in
  the proof outline.
* A Givens sweep can leave negative diagonal entries in a triangular factor; the routine of
  Algorithm 5.1.3 of the book can return a negative $r$. The statement of the book "the updated
  Cholesky factor is $\tilde G = R^T$" holds up to the signs that
  `Matrix.isCholesky_diagonal_sign_mul` normalizes. The sweeps here use `Matrix.givensPair` and
  `Matrix.hyperbolicPair`, which keep the diagonal positive.
* Two slips of the book are recorded at the declarations: the typo $\tilde A = RR^T$ after (6.5.7),
  at `Matrix.transpose_mul_self_eq_of_mem_orthogonalGroup`, and the Schur complement in Theorem
  6.5.1, at `Matrix.hyperbolicDowndate_step`.
-/

open scoped Matrix

namespace Matrix

/-! ### Sweeps of rotations in adjacent planes -/

section AdjacentRotationProd

variable {M : ℕ}

/-- A **sweep of rotations in adjacent planes**. Let $a, n \in \mathbb{N}$ and
$c, s : \mathbb{N} \to \mathbb{R}$. For each $j$, let $G_j$ be the rotation $\begin{bmatrix} c_j
& -s_j \\ s_j & c_j \end{bmatrix}$ placed in the coordinate plane $(j, j+1)$ of $\mathbb{R}^M$,
and the identity when $j + 1 \ge M$. The sweep is the product in increasing order $$G_a G_{a+1}
\cdots G_{a+n-1}.$$

Applied on the left of a matrix, the last factor acts first:
`Matrix.adjacentRotationProd a n c s * X` sweeps the planes bottom-up. Its transpose
`(Matrix.adjacentRotationProd a n c s)ᵀ * X`, the product of the transposed rotations in
decreasing order, sweeps them top-down.

The factor $G_j$ is `Matrix.adjacentEmbed j !![c j, -s j; s j, c j]`. The definition does not
require $c_j^2 + s_j^2 = 1$; the theorems assume it where they need it. -/
noncomputable def adjacentRotationProd (a n : ℕ) (c s : ℕ → ℝ) : Matrix (Fin M) (Fin M) ℝ :=
  ((List.range' a n).map fun j => adjacentEmbed j !![c j, -s j; s j, c j]).prod

variable {a n : ℕ} {c s : ℕ → ℝ}

/-- A sweep is a forward product: $G_a G_{a+1} \cdots G_{a+n-1}$ is `prodFwd` of the sequence
$k \mapsto G_{a+k}$, taken to $n$ factors. -/
theorem adjacentRotationProd_eq_prodFwd :
    (adjacentRotationProd a n c s : Matrix (Fin M) (Fin M) ℝ) =
      prodFwd (fun k => adjacentEmbed (a + k) !![c (a + k), -s (a + k); s (a + k), c (a + k)]) n :=
  prod_map_range'_eq_prodFwd _ a n

/-- The empty sweep, with $n = 0$, is the identity matrix. -/
@[simp]
theorem adjacentRotationProd_zero :
    (adjacentRotationProd a 0 c s : Matrix (Fin M) (Fin M) ℝ) = 1 := by
  simp [adjacentRotationProd]

/-- Splitting off the first rotation of a sweep: $G_a G_{a+1} \cdots G_{a+n} = G_a \, (G_{a+1}
\cdots G_{a+n})$. -/
theorem adjacentRotationProd_succ :
    (adjacentRotationProd a (n + 1) c s : Matrix (Fin M) (Fin M) ℝ) =
      adjacentEmbed a !![c a, -s a; s a, c a] * adjacentRotationProd (a + 1) n c s := by
  simp [adjacentRotationProd, List.range'_succ]

/-- Splitting off the last rotation of a sweep: $G_a \cdots G_{a+n} = (G_a \cdots G_{a+n-1}) \,
G_{a+n}$. -/
theorem adjacentRotationProd_succ' :
    (adjacentRotationProd a (n + 1) c s : Matrix (Fin M) (Fin M) ℝ) =
      adjacentRotationProd a n c s * adjacentEmbed (a + n) !![c (a + n), -s (a + n);
        s (a + n), c (a + n)] := by
  simp [adjacentRotationProd, List.range'_concat]

/-- A sweep depends only on the angles of its own planes: if $c_j = c'_j$ and $s_j = s'_j$ for
$a \le j < a + n$, then the sweeps $G_a \cdots G_{a+n-1}$ for $(c, s)$ and for $(c', s')$ are
equal. -/
theorem adjacentRotationProd_congr {c' s' : ℕ → ℝ}
    (h : ∀ j, a ≤ j → j < a + n → c j = c' j ∧ s j = s' j) :
    (adjacentRotationProd a n c s : Matrix (Fin M) (Fin M) ℝ) = adjacentRotationProd a n c' s' := by
  unfold adjacentRotationProd
  congr 1
  refine List.map_congr_left fun j hj => ?_
  obtain ⟨h₁, h₂⟩ := List.mem_range'_1.1 hj
  obtain ⟨hc, hs⟩ := h j h₁ h₂
  rw [hc, hs]

/-- If $c_j^2 + s_j^2 = 1$ for all $j$, then the sweep $G_a \cdots G_{a+n-1}$ is an orthogonal
matrix. -/
theorem adjacentRotationProd_mem_orthogonalGroup (h : ∀ j, c j ^ 2 + s j ^ 2 = 1) :
    (adjacentRotationProd a n c s : Matrix (Fin M) (Fin M) ℝ) ∈ orthogonalGroup (Fin M) ℝ := by
  refine Submonoid.list_prod_mem _ fun G hG => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hG
  unfold adjacentEmbed
  split_ifs
  · exact planeRotation_mem_orthogonalGroup (Fin.ne_of_val_ne (by simp)) (h j)
  · exact one_mem _

end AdjacentRotationProd

/-! ### Givens sweeps exist -/

section Givens

variable {M N : ℕ}

/-- Bottom-up zeroing of a vector by a sweep of Givens rotations. Let $x \in \mathbb{R}^M$ and
$b, n \in \mathbb{N}$. Then there are $c, s : \mathbb{N} \to \mathbb{R}$ with
$c_j^2 + s_j^2 = 1$ for all $j$ such that the sweep $P = G_b G_{b+1} \cdots G_{b+n-1}$ satisfies
$$(Px)_i = 0 \quad \text{for } b < i \le b + n, \qquad (Px)_i = x_i \quad \text{for } i < b.$$
The last plane $(b + n - 1, b + n)$ acts first. This is the step of [golub2013matrix] §6.5.1
that computes "rotations $J_{n-1}, \dots, J_1$ … such that
$J_1^T \cdots J_{n-1}^T w = \pm \|w\|_2 e_1$".

The sweep $P$ is `Matrix.adjacentRotationProd b n c s`. In the proof, each rotation is
`Matrix.givensPair` of the two entries that it mixes. -/
theorem exists_adjacentRotationProd_mulVec_eq_zero (x : Fin M → ℝ) (b n : ℕ) :
    ∃ c s : ℕ → ℝ, (∀ j, c j ^ 2 + s j ^ 2 = 1) ∧
      (∀ i : Fin M, b < (i : ℕ) → (i : ℕ) ≤ b + n →
        (adjacentRotationProd b n c s *ᵥ x) i = 0) ∧
      ∀ i : Fin M, (i : ℕ) < b → (adjacentRotationProd b n c s *ᵥ x) i = x i := by
  induction n generalizing b with
  | zero =>
    exact ⟨fun _ => 1, fun _ => 0, fun _ => by norm_num, fun i h₁ h₂ => by omega,
      fun i _ => by simp⟩
  | succ n ih =>
    obtain ⟨c, s, hcs, hz, hx⟩ := ih (b + 1)
    by_cases hb : b + 1 < M
    · obtain ⟨p, hp⟩ : ∃ p, p = givensPair ((adjacentRotationProd (b + 1) n c s *ᵥ x)
          ⟨b, by omega⟩) ((adjacentRotationProd (b + 1) n c s *ᵥ x) ⟨b + 1, hb⟩) := ⟨_, rfl⟩
      have hcongr : (adjacentRotationProd (b + 1) n (Function.update c b p.1)
          (Function.update s b (-p.2)) : Matrix (Fin M) (Fin M) ℝ) =
          adjacentRotationProd (b + 1) n c s :=
        adjacentRotationProd_congr fun j hj _ => by
          simp [Function.update_of_ne (show j ≠ b by omega)]
      have hP : (adjacentRotationProd b (n + 1) (Function.update c b p.1)
          (Function.update s b (-p.2)) : Matrix (Fin M) (Fin M) ℝ) *ᵥ x =
          adjacentEmbed b !![p.1, -(-p.2); -p.2, p.1] *ᵥ
            (adjacentRotationProd (b + 1) n c s *ᵥ x) := by
        rw [adjacentRotationProd_succ, ← mulVec_mulVec, hcongr, Function.update_self,
          Function.update_self]
      refine ⟨Function.update c b p.1, Function.update s b (-p.2), fun j => ?_,
        fun i h₁ h₂ => ?_, fun i hi => ?_⟩
      · by_cases hj : j = b
        · subst hj
          simpa [hp] using givensPair_sq_add_sq _ _
        · simpa [Function.update_of_ne hj] using hcs j
      · rw [hP]
        by_cases hi : (i : ℕ) = b + 1
        · obtain rfl : i = ⟨b + 1, hb⟩ := Fin.ext hi
          rw [adjacentEmbed_mulVec_apply_succ b _ hb]
          simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
            cons_val_fin_one, Fin.isValue]
          rw [hp]
          linear_combination (givensPair_fst_mul_add_snd_mul _ _).2
        · rw [adjacentEmbed_mulVec_apply_of_ne _ _ _ (by omega) hi]
          exact hz i (by omega) (by omega)
      · rw [hP, adjacentEmbed_mulVec_apply_of_ne _ _ _ (by omega) (by omega)]
        exact hx i (by omega)
    · refine ⟨c, s, hcs, fun i h₁ _ => by omega, fun i hi => ?_⟩
      rw [adjacentRotationProd_succ, adjacentEmbed_of_le _ (by omega), Matrix.one_mul]
      exact hx i (by omega)

/-- One step of a top-down sweep, on the left of a matrix: $(G_a \cdots G_{a+t})^T X = G_{a+t}^T \,
\bigl((G_a \cdots G_{a+t-1})^T X\bigr)$. -/
private theorem transpose_adjacentRotationProd_succ_mul (a t : ℕ) (c s : ℕ → ℝ)
    (X : Matrix (Fin M) (Fin N) ℝ) :
    (adjacentRotationProd a (t + 1) c s : Matrix (Fin M) (Fin M) ℝ)ᵀ * X =
      adjacentEmbed (a + t) !![c (a + t), s (a + t); -s (a + t), c (a + t)] *
        ((adjacentRotationProd a t c s)ᵀ * X) := by
  rw [adjacentRotationProd_succ', transpose_mul, Matrix.mul_assoc, adjacentEmbed_transpose,
    rotationBlock_transpose]

/-- Givens triangularization of a rectangular upper Hessenberg matrix. Let
$H \in \mathbb{R}^{M \times N}$ be upper Hessenberg, that is, $h_{il} = 0$ for $i > l + 1$. Let
$a \in \mathbb{N}$ be such that the first $a$ columns of $H$ are already triangular:
$h_{il} = 0$ for $l < i$ and $l < a$. Let $L = \min(N, M - 1)$. Then there are
$c, s : \mathbb{N} \to \mathbb{R}$ with $c_j^2 + s_j^2 = 1$ for all $j$ such that, for the sweep
$J = G_a \cdots G_{L-1}$ of rotations in the planes $(j, j + 1)$, the matrix $J^T H$ is upper
trapezoidal. This is the triangularization step of [golub2013matrix] §6.5.1–6.5.3, after
Algorithm 5.2.5.

The sweep $J$ is `Matrix.adjacentRotationProd a (L - a) c s`, with the subtractions in
$\mathbb{N}$; for $a \ge L$ the sweep is empty. $J$ is orthogonal by
`Matrix.adjacentRotationProd_mem_orthogonalGroup`. Upper Hessenberg and upper trapezoidal are
`Matrix.HasLowerBandwidthRect` with bandwidth $1$ and $0$. In the proof, each $G_j$ is the
Givens pair of the current entries $(j, j)$ and $(j + 1, j)$, and the rest is
`Matrix.hasLowerBandwidthRect_zero_of_adjacentRotations`. -/
theorem exists_rotations_triangularize_of_hessenberg {H : Matrix (Fin M) (Fin N) ℝ}
    (hH : H.HasLowerBandwidthRect 1) {a : ℕ}
    (ha : ∀ (i : Fin M) (l : Fin N), (l : ℕ) < i → (l : ℕ) < a → H i l = 0) :
    ∃ c s : ℕ → ℝ, (∀ j, c j ^ 2 + s j ^ 2 = 1) ∧
      ((adjacentRotationProd a (min N (M - 1) - a) c s : Matrix (Fin M) (Fin M) ℝ)ᵀ *
        H).HasLowerBandwidthRect 0 := by
  have key : ∀ t, ∃ c s : ℕ → ℝ, (∀ j, c j ^ 2 + s j ^ 2 = 1) ∧ ∀ t' < t,
      ∀ (i : Fin M) (l : Fin N), (i : ℕ) = a + t' + 1 → (l : ℕ) = a + t' →
        ((adjacentRotationProd a (t' + 1) c s : Matrix (Fin M) (Fin M) ℝ)ᵀ * H) i l = 0 := by
    intro t
    induction t with
    | zero => exact ⟨fun _ => 1, fun _ => 0, fun _ => by norm_num, fun t' ht' => by omega⟩
    | succ t ih =>
      obtain ⟨c, s, hcs, hz⟩ := ih
      by_cases hb : a + t + 1 < M ∧ a + t < N
      · obtain ⟨p, hp⟩ : ∃ p, p = givensPair
            (((adjacentRotationProd a t c s : Matrix (Fin M) (Fin M) ℝ)ᵀ * H) ⟨a + t, by omega⟩
              ⟨a + t, hb.2⟩)
            (((adjacentRotationProd a t c s : Matrix (Fin M) (Fin M) ℝ)ᵀ * H) ⟨a + t + 1, hb.1⟩
              ⟨a + t, hb.2⟩) := ⟨_, rfl⟩
        have hcongr : ∀ u ≤ t, (adjacentRotationProd a u (Function.update c (a + t) p.1)
            (Function.update s (a + t) p.2) : Matrix (Fin M) (Fin M) ℝ) =
            adjacentRotationProd a u c s :=
          fun u hu => adjacentRotationProd_congr fun j _ hj => by
            simp [Function.update_of_ne (show j ≠ a + t by omega)]
        refine ⟨Function.update c (a + t) p.1, Function.update s (a + t) p.2, fun j => ?_,
          fun t' ht' i l hi hl => ?_⟩
        · by_cases hj : j = a + t
          · subst hj
            simpa [hp] using givensPair_sq_add_sq _ _
          · simpa [Function.update_of_ne hj] using hcs j
        · rcases Nat.lt_succ_iff_lt_or_eq.1 ht' with ht' | rfl
          · rw [hcongr (t' + 1) (by omega)]
            exact hz t' ht' i l hi hl
          · obtain rfl : i = ⟨a + t' + 1, hb.1⟩ := Fin.ext hi
            obtain rfl : l = ⟨a + t', hb.2⟩ := Fin.ext hl
            rw [transpose_adjacentRotationProd_succ_mul, hcongr t' le_rfl,
              adjacentEmbed_mul_apply_succ _ _ _ hb.1]
            simp only [Function.update_self, of_apply, cons_val', cons_val_zero, cons_val_one,
              empty_val', cons_val_fin_one, Fin.isValue]
            rw [hp]
            linear_combination (givensPair_fst_mul_add_snd_mul _ _).2
      · refine ⟨c, s, hcs, fun t' ht' i l hi hl => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 ht' with ht' | rfl
        · exact hz t' ht' i l hi hl
        · exact absurd ⟨by omega, by omega⟩ hb
  obtain ⟨c, s, hcs, hz⟩ := key (min N (M - 1) - a)
  exact ⟨c, s, hcs, hasLowerBandwidthRect_zero_of_adjacentRotations hH ha
    (fun j => !![c j, s j; -s j, c j]) (fun t => (adjacentRotationProd a t c s)ᵀ * H)
    (by simp) (fun t _ => transpose_adjacentRotationProd_succ_mul a t c s H)
    (fun t ht i l hi hl => hz t (by omega) i l hi hl)⟩

end Givens

/-! ### QR updating -/

section QR

variable {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ}

/-- QR factorization after a rank-one change. Let $A, Q, R \in \mathbb{R}^{n \times n}$, let
$A = QR$ be a full QR factorization, and let $u, v \in \mathbb{R}^n$. Write $w = Q^T u$. Then
there are two sweeps $P = G_0 \cdots G_{n-2}$ and $P' = G'_0 \cdots G'_{n-2}$ of rotations in
the planes $(k, k + 1)$, with $c_j^2 + s_j^2 = 1$ and $c_j'^2 + s_j'^2 = 1$ for all $j$, such
that $Pw$ is a multiple of $e_0$, that is, $(Pw)_i = 0$ for $i \ne 0$, and $$A + uv^T = (Q P^T
P') \, \bigl(P'^T P \, (R + w v^T)\bigr)$$ is a full QR factorization. This is §6.5.1 of
[golub2013matrix], (6.5.1)–(6.5.3).

In the notation of the book, $J = J_{n-2} \cdots J_0$ is $P^T$ and $G = G_0 \cdots G_{n-2}$ is
$P'$. By (6.5.1), $A + uv^T = Q (R + w v^T)$. The matrix $J^T R$ is upper Hessenberg by
`Matrix.prodFwd_adjacentEmbed_mul_apply_eq_zero`, and $J^T w v^T$ is nonzero only in row $0$.
Thus $H_1 = J^T (R + w v^T)$ is upper Hessenberg (6.5.3), and $G$ triangularizes it by
`Matrix.exists_rotations_triangularize_of_hessenberg`. The two sweeps are
`Matrix.adjacentRotationProd 0 (n - 1) c s` and `Matrix.adjacentRotationProd 0 (n - 1) c' s'`,
and $u v^T$ is `Matrix.vecMulVec u v`. -/
theorem exists_isQR_rankOne_update {A Q R : Matrix (Fin n) (Fin n) ℝ} (h : IsQR A Q R)
    (u v : Fin n → ℝ) :
    ∃ c s c' s' : ℕ → ℝ, (∀ j, c j ^ 2 + s j ^ 2 = 1) ∧ (∀ j, c' j ^ 2 + s' j ^ 2 = 1) ∧
      (∀ i : Fin n, (i : ℕ) ≠ 0 → (adjacentRotationProd 0 (n - 1) c s *ᵥ (Qᵀ *ᵥ u)) i = 0) ∧
      IsQR (A + vecMulVec u v)
        (Q * (adjacentRotationProd 0 (n - 1) c s)ᵀ * adjacentRotationProd 0 (n - 1) c' s')
        ((adjacentRotationProd 0 (n - 1) c' s')ᵀ * adjacentRotationProd 0 (n - 1) c s *
          (R + vecMulVec (Qᵀ *ᵥ u) v)) := by
  obtain ⟨c, s, hcs, hz, -⟩ := exists_adjacentRotationProd_mulVec_eq_zero (Qᵀ *ᵥ u) 0 (n - 1)
  have hz' : ∀ i : Fin n, (i : ℕ) ≠ 0 →
      (adjacentRotationProd 0 (n - 1) c s *ᵥ (Qᵀ *ᵥ u)) i = 0 :=
    fun i hi => hz i (by omega) (by have := i.isLt; omega)
  have hH : ((adjacentRotationProd 0 (n - 1) c s : Matrix (Fin n) (Fin n) ℝ) *
      (R + vecMulVec (Qᵀ *ᵥ u) v)).HasLowerBandwidthRect 1 := by
    intro i l hil
    rw [Matrix.mul_add, Matrix.add_apply, mul_vecMulVec, vecMulVec_apply, hz' i (by omega),
      zero_mul, add_zero]
    rw [adjacentRotationProd_eq_prodFwd]
    exact prodFwd_adjacentEmbed_mul_apply_eq_zero h.hasLowerBandwidthRect
      (fun j => !![c j, -s j; s j, c j]) 0 (n - 1) (Or.inl hil)
  obtain ⟨c', s', hcs', hT⟩ := exists_rotations_triangularize_of_hessenberg hH (a := 0)
    (fun _ _ _ h => absurd h (Nat.not_lt_zero _))
  rw [show min n (n - 1) - 0 = n - 1 by omega] at hT
  refine ⟨c, s, c', s', hcs, hcs', hz', ?_⟩
  have hP := adjacentRotationProd_mem_orthogonalGroup (M := n) (a := 0) (n := n - 1) hcs
  have hG := adjacentRotationProd_mem_orthogonalGroup (M := n) (a := 0) (n := n - 1) hcs'
  have hQ : Q ∈ orthogonalGroup (Fin n) ℝ := h.mem_unitaryGroup
  refine ⟨mul_mem (mul_mem hQ (transpose_mem_unitaryGroup_iff.2 hP)) hG,
    fun i j hij => ?_, ?_⟩
  · rw [Matrix.mul_assoc]
    exact hT i j (by simpa using hij)
  · rw [show Q * (adjacentRotationProd 0 (n - 1) c s)ᵀ * adjacentRotationProd 0 (n - 1) c' s' *
        ((adjacentRotationProd 0 (n - 1) c' s')ᵀ * adjacentRotationProd 0 (n - 1) c s *
          (R + vecMulVec (Qᵀ *ᵥ u) v)) =
        Q * ((adjacentRotationProd 0 (n - 1) c s)ᵀ *
          ((adjacentRotationProd 0 (n - 1) c' s' * (adjacentRotationProd 0 (n - 1) c' s')ᵀ) *
            adjacentRotationProd 0 (n - 1) c s)) * (R + vecMulVec (Qᵀ *ᵥ u) v) by
        simp only [Matrix.mul_assoc],
      (mem_orthogonalGroup_iff (Fin n) ℝ).1 hG, Matrix.one_mul,
      (mem_orthogonalGroup_iff' (Fin n) ℝ).1 hP, Matrix.mul_one, Matrix.mul_add, h.mul_eq,
      mul_vecMulVec, mulVec_mulVec, (mem_orthogonalGroup_iff (Fin n) ℝ).1 hQ, one_mulVec]

/-- Deleting a column of a QR factorization leaves an upper Hessenberg matrix. Let $\mathbb{K}$ be
$\mathbb{R}$ or $\mathbb{C}$, let $A \in \mathbb{K}^{m \times (n+1)}$ have the full QR
factorization $A = QR$, and let $0 \le k \le n$. Let $\tilde A$ and $\tilde R$ be $A$ and $R$
with column $k$ deleted. Then $Q^H \tilde A = \tilde R$, the matrix $\tilde R$ is upper
Hessenberg, and its first $k$ columns are still triangular: $\tilde r_{ij} = 0$ for $j < i$ and
$j < k$. This is §6.5.2 of [golub2013matrix].

The deletion of column $k$ is `A.submatrix id k.succAbove`. -/
theorem IsQR.conjTranspose_mul_deleteColumn {A : Matrix (Fin m) (Fin (n + 1)) 𝕜} {Q R}
    (h : IsQR A Q R) (k : Fin (n + 1)) :
    Qᴴ * A.submatrix id k.succAbove = R.submatrix id k.succAbove ∧
      (R.submatrix id k.succAbove).HasLowerBandwidthRect 1 ∧
      ∀ (i : Fin m) (j : Fin n), (j : ℕ) < i → (j : ℕ) < k →
        R.submatrix id k.succAbove i j = 0 := by
  refine ⟨?_, fun i j hij => h.apply_eq_zero i (k.succAbove j) ?_,
    fun i j hij hjk => h.apply_eq_zero i (k.succAbove j) ?_⟩
  · rw [← h.conjTranspose_mul_eq]
    ext i j
    simp [Matrix.mul_apply]
  · have := Fin.val_succAbove_le k j
    omega
  · rw [Fin.val_succAbove_of_lt hjk]
    exact hij

/-- QR factorization after deleting a column. Let $A \in \mathbb{R}^{m \times (n+1)}$ have the full
QR factorization $A = QR$, let $0 \le k \le n$, and let $\tilde A$ and $\tilde R$ be $A$ and $R$
with column $k$ deleted. Let $L = \min(n, m - 1)$. Then there is a sweep
$G = G_k \cdots G_{L-1}$ of rotations in the planes $(j, j + 1)$, $k \le j < L$, with
$c_j^2 + s_j^2 = 1$ for all $j$, such that $$\tilde A = (QG) \, (G^T \tilde R)$$ is a full QR
factorization. This is §6.5.2 of [golub2013matrix], where $Q_1 = Q G_k \cdots G_{n-1}$.

The sweep $G$ is `Matrix.adjacentRotationProd k (L - k) c s`, with the subtractions in
$\mathbb{N}$. The matrix $\tilde R$ equals $Q^T \tilde A$ by
`Matrix.IsQR.conjTranspose_mul_deleteColumn`. -/
theorem IsQR.exists_deleteColumn {A : Matrix (Fin m) (Fin (n + 1)) ℝ} {Q R} (h : IsQR A Q R)
    (k : Fin (n + 1)) :
    ∃ c s : ℕ → ℝ, (∀ j, c j ^ 2 + s j ^ 2 = 1) ∧
      IsQR (A.submatrix id k.succAbove) (Q * adjacentRotationProd k (min n (m - 1) - k) c s)
        ((adjacentRotationProd k (min n (m - 1) - k) c s)ᵀ * R.submatrix id k.succAbove) := by
  obtain ⟨h₁, h₂, h₃⟩ := h.conjTranspose_mul_deleteColumn k
  obtain ⟨c, s, hcs, hT⟩ := exists_rotations_triangularize_of_hessenberg h₂ h₃
  refine ⟨c, s, hcs, ?_⟩
  have hG := adjacentRotationProd_mem_orthogonalGroup (M := m) (a := k)
    (n := min n (m - 1) - k) hcs
  have e : (Q * adjacentRotationProd k (min n (m - 1) - k) c s)ᴴ * A.submatrix id k.succAbove =
      (adjacentRotationProd k (min n (m - 1) - k) c s)ᵀ * R.submatrix id k.succAbove := by
    rw [conjTranspose_mul, Matrix.mul_assoc, h₁, conjTranspose_eq_transpose_of_trivial]
  have := isQR_conjTranspose_mul (mul_mem h.mem_unitaryGroup hG) (by rw [e]; exact hT)
  rwa [e] at this

/-- Inserting a column into a QR factorization leaves a spike. Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$, let $A \in \mathbb{K}^{m \times n}$ have the full QR factorization $A = QR$, let
$z \in \mathbb{K}^m$, and let $0 \le k \le n$. Let $\tilde A$ be $A$ with $z$ inserted as column
$k$. Then $Q^H \tilde A$ is $R$ with $Q^H z$ inserted as column $k$, and
$(Q^H \tilde A)_{ij} = 0$ for $j < i$ and $j \ne k$: the matrix is upper trapezoidal except
below the diagonal in column $k$. This is §6.5.2 of [golub2013matrix].

The matrix $\tilde A$ is `Matrix.of fun i => Fin.insertNth k (z i) (A i)`. -/
theorem IsQR.conjTranspose_mul_insertColumn {A : Matrix (Fin m) (Fin n) 𝕜} {Q R}
    (h : IsQR A Q R) (z : Fin m → 𝕜) (k : Fin (n + 1)) :
    Qᴴ * of (fun i => Fin.insertNth k (z i) (A i)) =
        of (fun i => Fin.insertNth k ((Qᴴ *ᵥ z) i) (R i)) ∧
      ∀ (i : Fin m) (j : Fin (n + 1)), (j : ℕ) < i → j ≠ k →
        (Qᴴ * of fun i => Fin.insertNth k (z i) (A i)) i j = 0 := by
  have e : Qᴴ * of (fun i => Fin.insertNth k (z i) (A i)) =
      of (fun i => Fin.insertNth k ((Qᴴ *ᵥ z) i) (R i)) := by
    rw [mul_of_insertNth, h.conjTranspose_mul_eq]
  refine ⟨e, fun i j hij hjk => ?_⟩
  obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hjk
  rw [e, of_apply, Fin.insertNth_apply_succAbove]
  exact h.apply_eq_zero i j (by have := Fin.le_val_succAbove k j; omega)

/-- QR factorization after inserting a column. Let $A \in \mathbb{R}^{m \times n}$ have the full QR
factorization $A = QR$, let $z \in \mathbb{R}^m$, let $0 \le k \le n$, and let $\tilde A$ be $A$
with $z$ inserted as column $k$. Then there is a sweep $P = G_k \cdots G_{m-2}$ of rotations in
the planes $(j, j + 1)$, $k \le j < m - 1$, with $c_j^2 + s_j^2 = 1$ for all $j$, such that
$$\tilde A = (Q P^T) \, (P Q^T \tilde A)$$ is a full QR factorization. The sweep acts bottom-up
and zeroes the spike of $Q^T \tilde A$ below row $k$. This is §6.5.2 of [golub2013matrix], with
the rotations $J_{m-1}, \dots, J_{k+1}$; the sweep $P$ is the matrix $J^T$ of the book.

The sweep $P$ is `Matrix.adjacentRotationProd k (m - 1 - k) c s`. The rotations mix only rows
$\ge k$, where the other columns of $Q^T \tilde A$ vanish or are upper Hessenberg, so no fill-in
occurs (`Matrix.prodFwd_adjacentEmbed_mul_apply_eq_zero`). -/
theorem IsQR.exists_insertColumn {A : Matrix (Fin m) (Fin n) ℝ} {Q R} (h : IsQR A Q R)
    (z : Fin m → ℝ) (k : Fin (n + 1)) :
    ∃ c s : ℕ → ℝ, (∀ j, c j ^ 2 + s j ^ 2 = 1) ∧
      IsQR (of fun i => Fin.insertNth k (z i) (A i))
        (Q * (adjacentRotationProd k (m - 1 - k) c s)ᵀ)
        (adjacentRotationProd k (m - 1 - k) c s * (Qᵀ * of fun i => Fin.insertNth k (z i) (A i)))
        := by
  obtain ⟨c, s, hcs, hz, -⟩ := exists_adjacentRotationProd_mulVec_eq_zero (Qᵀ *ᵥ z) k (m - 1 - k)
  refine ⟨c, s, hcs, ?_⟩
  have hP := adjacentRotationProd_mem_orthogonalGroup (M := m) (a := k) (n := m - 1 - k) hcs
  have hQt : Qᴴ = Qᵀ := conjTranspose_eq_transpose_of_trivial Q
  obtain ⟨e, -⟩ := h.conjTranspose_mul_insertColumn z k
  rw [hQt] at e
  have e' : (Q * (adjacentRotationProd k (m - 1 - k) c s)ᵀ)ᴴ *
      (of fun i => Fin.insertNth k (z i) (A i)) =
      adjacentRotationProd k (m - 1 - k) c s * (Qᵀ * of fun i => Fin.insertNth k (z i) (A i)) := by
    rw [conjTranspose_mul, conjTranspose_eq_transpose_of_trivial, transpose_transpose, hQt,
      Matrix.mul_assoc]
  have hT : ((adjacentRotationProd k (m - 1 - k) c s : Matrix (Fin m) (Fin m) ℝ) *
      (Qᵀ * of fun i => Fin.insertNth k (z i) (A i))).HasLowerBandwidthRect 0 := by
    intro i j hij
    rw [e, mul_of_insertNth, of_apply]
    obtain rfl | ⟨j, rfl⟩ := Fin.eq_self_or_eq_succAbove k j
    · rw [Fin.insertNth_apply_same]
      exact hz i (by omega) (by omega)
    · rw [Fin.insertNth_apply_succAbove]
      rw [adjacentRotationProd_eq_prodFwd]
      refine prodFwd_adjacentEmbed_mul_apply_eq_zero h.hasLowerBandwidthRect
        (fun j => !![c j, -s j; s j, c j]) k (m - 1 - k) ?_
      rcases lt_or_ge (j : ℕ) k with hjk | hjk
      · rw [Fin.val_succAbove_of_lt hjk] at hij
        exact Or.inr ⟨by omega, hjk⟩
      · rw [Fin.val_succAbove_of_le hjk] at hij
        exact Or.inl (by omega)
  have := isQR_conjTranspose_mul (mul_mem h.mem_unitaryGroup (transpose_mem_unitaryGroup_iff.2 hP))
    (by rw [e']; exact hT)
  rwa [e'] at this

end QR

/-! ### Rows: the matrix $\operatorname{diag}(a, Q)$ and the cyclic row permutation -/

section ConsDiag

variable {α : Type*} {m n p : ℕ}

/-- Moving an inserted row to the top. Let $A$ be an $m \times n$ matrix, $w$ a row of length $n$,
$0 \le k \le m$, and $\tilde A$ the matrix $A$ with $w$ inserted as row $k$. Let $\sigma$ be the
inverse of the cycle `Fin.cycleRange k`, so that $\sigma(0) = k$ and $\sigma(j + 1)$ is
`k.succAbove j`. Then the matrix whose row $i$ is row $\sigma(i)$ of $\tilde A$ is $[w^T; A]$.
This is the permutation $P$ of [golub2013matrix] §6.5.3. -/
theorem submatrix_insertNth_cycleRange (w : Fin n → α) (A : Matrix (Fin m) (Fin n) α)
    (k : Fin (m + 1)) :
    (of (Fin.insertNth k w A) : Matrix (Fin (m + 1)) (Fin n) α).submatrix
      (Fin.cycleRange k).symm id = of (Fin.cons w A) := by
  ext i j
  induction i using Fin.cases <;> simp [Fin.cycleRange_symm_succ]

end ConsDiag

section QRRows

variable {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ}

/-- Inserting a row into a QR factorization leaves an upper Hessenberg matrix. Let $\mathbb{K}$ be
$\mathbb{R}$ or $\mathbb{C}$, let $A \in \mathbb{K}^{m \times n}$ have the full QR factorization
$A = QR$, let $w \in \mathbb{K}^n$, and let $0 \le k \le m$. Let $\tilde A$ be $A$ with the row
$w^T$ inserted at position $k$, and let $P$ be the row permutation that moves row $k$ to the top
(`Matrix.submatrix_insertNth_cycleRange`). Then $$\operatorname{diag}(1, Q^H) \, P \tilde A =
[w^T; R],$$ and $[w^T; R]$ is upper Hessenberg. This is §6.5.3 of [golub2013matrix].

The matrix $\operatorname{diag}(1, Q^H)$ is `Matrix.consDiag 1 Qᴴ`. The row insertion is
`Fin.insertNth k w A`, and the row permutation $P$ is `Matrix.submatrix` with
`(Fin.cycleRange k).symm` on the rows. -/
theorem IsQR.conjTranspose_mul_insertRow {A : Matrix (Fin m) (Fin n) 𝕜} {Q R} (h : IsQR A Q R)
    (w : Fin n → 𝕜) (k : Fin (m + 1)) :
    consDiag 1 Qᴴ * (of (Fin.insertNth k w A)).submatrix (Fin.cycleRange k).symm id =
        of (Fin.cons w R) ∧
      (of (Fin.cons w R) : Matrix (Fin (m + 1)) (Fin n) 𝕜).HasLowerBandwidthRect 1 := by
  refine ⟨by rw [submatrix_insertNth_cycleRange, consDiag_mul_of_cons, one_smul,
    h.conjTranspose_mul_eq], fun i j hij => ?_⟩
  induction i using Fin.cases with
  | zero => simp at hij
  | succ i =>
    simp only [of_apply, cons_rows_succ]
    exact h.apply_eq_zero i j (by simp at hij; omega)

/-- QR factorization after inserting a row. Let $A \in \mathbb{R}^{m \times n}$ have the full QR
factorization $A = QR$, let $w \in \mathbb{R}^n$, let $0 \le k \le m$, and let $\tilde A$ be $A$
with the row $w^T$ inserted at position $k$. Let $L = \min(n, m)$. Then there is a sweep
$J = J_0 \cdots J_{L-1}$ of rotations in the planes $(j, j + 1)$ of $\mathbb{R}^{m+1}$, with
$c_j^2 + s_j^2 = 1$ for all $j$, such that $$\tilde A = \bigl(P^T \operatorname{diag}(1, Q) \,
J\bigr) \, \bigl(J^T [w^T; R]\bigr)$$ is a full QR factorization. Here $P^T$ is the row
permutation `Fin.cycleRange k`, which puts the top row back at position $k$. This is §6.5.3 of
[golub2013matrix], where $Q_1 = \operatorname{diag}(1, Q) J_1 \cdots J_n$.

The sweep $J$ is `Matrix.adjacentRotationProd 0 (min n m) c s`, and $P^T X$ is
`X.submatrix (Fin.cycleRange k) id`. -/
theorem IsQR.exists_insertRow {A : Matrix (Fin m) (Fin n) ℝ} {Q R} (h : IsQR A Q R)
    (w : Fin n → ℝ) (k : Fin (m + 1)) :
    ∃ c s : ℕ → ℝ, (∀ j, c j ^ 2 + s j ^ 2 = 1) ∧
      IsQR (of (Fin.insertNth k w A))
        ((consDiag 1 Q * adjacentRotationProd 0 (min n m) c s).submatrix (Fin.cycleRange k) id)
        ((adjacentRotationProd 0 (min n m) c s)ᵀ * of (Fin.cons w R)) := by
  obtain ⟨-, hH⟩ := h.conjTranspose_mul_insertRow w k
  obtain ⟨c, s, hcs, hT⟩ := exists_rotations_triangularize_of_hessenberg hH (a := 0)
    (fun _ _ _ h => absurd h (Nat.not_lt_zero _))
  rw [show min n (m + 1 - 1) - 0 = min n m by omega] at hT
  have hG := adjacentRotationProd_mem_orthogonalGroup (M := m + 1) (a := 0) (n := min n m) hcs
  refine ⟨c, s, hcs, submatrix_mem_unitaryGroup (mul_mem (consDiag_mem_unitaryGroup
    (by simp) h.mem_unitaryGroup) hG) _, fun i j hij => hT i j (by simpa using hij), ?_⟩
  rw [submatrix_id_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (adjacentRotationProd 0 (min n m) c s),
    (mem_orthogonalGroup_iff _ ℝ).1 hG, Matrix.one_mul, consDiag_mul_of_cons, one_smul, h.mul_eq,
    ← submatrix_insertNth_cycleRange w A k, submatrix_submatrix, Equiv.symm_comp_self,
    Function.id_comp, submatrix_id_id]

/-- QR factorization after deleting the first row. Let $A \in \mathbb{R}^{(m+1) \times n}$ have the
full QR factorization $A = QR$. Then there are $c, s : \mathbb{N} \to \mathbb{R}$ with
$c_j^2 + s_j^2 = 1$ for all $j$, a sign $a$ with $a^2 = 1$, and matrices
$Q_1 \in \mathbb{R}^{m \times m}$, $R_1 \in \mathbb{R}^{m \times n}$ and a vector
$v \in \mathbb{R}^n$ such that the sweep $P = G_0 \cdots G_{m-1}$ of rotations in the planes
$(j, j + 1)$ satisfies $$Q P^T = \operatorname{diag}(a, Q_1), \qquad P R = [v^T; R_1],$$ and
$A_1 = Q_1 R_1$ is a full QR factorization of the matrix $A_1$ obtained from $A$ by deleting its
first row. This is §6.5.3 of [golub2013matrix].

The sweep $P$ is `Matrix.adjacentRotationProd 0 m c s`, and the matrix $G = G_{m-1} \cdots G_0$
of the book is $P^T$. The sweep acts bottom-up and zeroes the first row $q$ of $Q$:
$P q = a e_0$. The matrix $P R$ is upper Hessenberg by
`Matrix.prodFwd_adjacentEmbed_mul_apply_eq_zero`, so $R_1$ is upper trapezoidal. The first row
of the orthogonal matrix $Q P^T$ is $a e_0^T$, and this forces its first column to be $a e_0$. -/
theorem IsQR.exists_deleteFirstRow {A : Matrix (Fin (m + 1)) (Fin n) ℝ} {Q R} (h : IsQR A Q R) :
    ∃ (c s : ℕ → ℝ) (a : ℝ) (Q₁ : Matrix (Fin m) (Fin m) ℝ) (v : Fin n → ℝ)
      (R₁ : Matrix (Fin m) (Fin n) ℝ), (∀ j, c j ^ 2 + s j ^ 2 = 1) ∧ a ^ 2 = 1 ∧
      Q * (adjacentRotationProd 0 m c s)ᵀ = consDiag a Q₁ ∧
      adjacentRotationProd 0 m c s * R = of (Fin.cons v R₁) ∧
      IsQR (A.submatrix Fin.succ id) Q₁ R₁ := by
  obtain ⟨c, s, hcs, hz, -⟩ := exists_adjacentRotationProd_mulVec_eq_zero (fun j => Q 0 j) 0 m
  have hP := adjacentRotationProd_mem_orthogonalGroup (M := m + 1) (a := 0) (n := m) hcs
  have hQ : Q ∈ orthogonalGroup (Fin (m + 1)) ℝ := h.mem_unitaryGroup
  have hX : Q * (adjacentRotationProd 0 m c s)ᵀ ∈ orthogonalGroup (Fin (m + 1)) ℝ :=
    mul_mem hQ (transpose_mem_unitaryGroup_iff.2 hP)
  set X := Q * (adjacentRotationProd 0 m c s)ᵀ with hXdef
  have hrow : ∀ j : Fin m, X 0 j.succ = 0 := fun j => by
    have e : X 0 j.succ = (adjacentRotationProd 0 m c s *ᵥ fun r => Q 0 r) j.succ := by
      simp [hXdef, Matrix.mul_apply, mulVec, dotProduct, mul_comm]
    rw [e]
    exact hz j.succ (by simp) (by simp)
  have hXX := (mem_orthogonalGroup_iff _ ℝ).1 hX
  have hXX' := (mem_orthogonalGroup_iff' _ ℝ).1 hX
  have ha : X 0 0 ^ 2 = 1 := by
    have := congrFun (congrFun hXX 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, hrow, sq] using this
  have hcol : ∀ i : Fin m, X i.succ 0 = 0 := by
    have h1 := congrFun (congrFun hXX' 0) 0
    simp only [Matrix.mul_apply, transpose_apply, Fin.sum_univ_succ, one_apply_eq] at h1
    have h2 : ∑ i : Fin m, X i.succ 0 * X i.succ 0 = 0 := by nlinarith
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (X i.succ 0))).1 h2 i
      (Finset.mem_univ _)
    exact mul_self_eq_zero.1 this
  have hXcons : X = consDiag (X 0 0) (X.submatrix Fin.succ Fin.succ) := by
    ext i j
    induction i using Fin.cases <;> induction j using Fin.cases <;> simp [hrow, hcol]
  have hQ₁ : X.submatrix Fin.succ Fin.succ ∈ orthogonalGroup (Fin m) ℝ := by
    rw [mem_orthogonalGroup_iff]
    have := hXX
    rw [hXcons, ← conjTranspose_eq_transpose_of_trivial, conjTranspose_consDiag,
      consDiag_mul_consDiag, ← consDiag_one] at this
    ext i j
    simpa [conjTranspose_eq_transpose_of_trivial] using congrFun (congrFun this i.succ) j.succ
  set H := adjacentRotationProd 0 m c s * R with hHdef
  have hH : H.HasLowerBandwidthRect 1 := fun i l hil => by
    rw [hHdef, adjacentRotationProd_eq_prodFwd]
    exact prodFwd_adjacentEmbed_mul_apply_eq_zero h.hasLowerBandwidthRect
      (fun j => !![c j, -s j; s j, c j]) 0 m (Or.inl hil)
  have hHcons : H = of (Fin.cons (H 0) (H.submatrix Fin.succ id)) := by
    ext i j
    induction i using Fin.cases <;> rfl
  refine ⟨c, s, X 0 0, X.submatrix Fin.succ Fin.succ, H 0, H.submatrix Fin.succ id, hcs, ha,
    hXcons, hHcons, hQ₁, fun i j hij => hH i.succ j (by simp; omega), ?_⟩
  have hA : A = X * H := by
    rw [hXdef, hHdef, Matrix.mul_assoc, ← Matrix.mul_assoc _ (adjacentRotationProd 0 m c s),
      (mem_orthogonalGroup_iff' _ ℝ).1 hP, Matrix.one_mul, h.mul_eq]
  rw [hA]
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_succ, hcol]

/-- QR factorization after deleting any row. Let $A \in \mathbb{R}^{(m+1) \times n}$ have the full
QR factorization $A = QR$, and let $0 \le k \le m$. Let $\sigma$ be the inverse of the cycle
`Fin.cycleRange k`, and let $Q_\sigma$ be the matrix whose row $i$ is row $\sigma(i)$ of $Q$;
this permutation moves row $k$ to the top. Then there are $c, s : \mathbb{N} \to \mathbb{R}$
with $c_j^2 + s_j^2 = 1$ for all $j$, a sign $a$ with $a^2 = 1$, and
$Q_1 \in \mathbb{R}^{m \times m}$, $v \in \mathbb{R}^n$ and $R_1 \in \mathbb{R}^{m \times n}$
such that the sweep $P = G_0 \cdots G_{m-1}$ satisfies $$Q_\sigma P^T = \operatorname{diag}(a,
Q_1), \qquad P R = [v^T; R_1],$$ and $A_1 = Q_1 R_1$ is a full QR factorization of the matrix
$A_1$ obtained from $A$ by deleting row $k$. This is §6.5.3 of [golub2013matrix]: "the procedure
is similar when an arbitrary row is deleted".

The proof applies `Matrix.IsQR.exists_deleteFirstRow` to the factorization
$\sigma A = (\sigma Q) R$ of the permuted matrix. The matrix $Q_\sigma$ is
`Q.submatrix (Fin.cycleRange k).symm id`, and the deletion of row $k$ is
`A.submatrix k.succAbove id`. -/
theorem IsQR.exists_deleteRow {A : Matrix (Fin (m + 1)) (Fin n) ℝ} {Q R} (h : IsQR A Q R)
    (k : Fin (m + 1)) :
    ∃ (c s : ℕ → ℝ) (a : ℝ) (Q₁ : Matrix (Fin m) (Fin m) ℝ) (v : Fin n → ℝ)
      (R₁ : Matrix (Fin m) (Fin n) ℝ), (∀ j, c j ^ 2 + s j ^ 2 = 1) ∧ a ^ 2 = 1 ∧
      Q.submatrix (Fin.cycleRange k).symm id * (adjacentRotationProd 0 m c s)ᵀ = consDiag a Q₁ ∧
      adjacentRotationProd 0 m c s * R = of (Fin.cons v R₁) ∧
      IsQR (A.submatrix k.succAbove id) Q₁ R₁ := by
  have h' : IsQR (A.submatrix (Fin.cycleRange k).symm id) (Q.submatrix (Fin.cycleRange k).symm id)
      R := ⟨submatrix_mem_unitaryGroup h.mem_unitaryGroup _, h.apply_eq_zero,
        by rw [submatrix_id_mul, h.mul_eq]⟩
  obtain ⟨c, s, a, Q₁, v, R₁, h₁, h₂, h₃, h₄, h₅⟩ := h'.exists_deleteFirstRow
  refine ⟨c, s, a, Q₁, v, R₁, h₁, h₂, h₃, h₄, ?_⟩
  rwa [submatrix_submatrix, Function.id_comp,
    show (⇑(Fin.cycleRange k).symm ∘ Fin.succ) = k.succAbove from
      funext (Fin.cycleRange_symm_succ k)] at h₅

end QRRows

/-! ### The stacked matrix $[H; z^T]$ and its Gram matrices -/

section Stacked

variable {α : Type*} [CommRing α] {m n p : Type*} [Fintype m]

/-- The Gram matrix of a single row $z^T$ is $z z^T$. -/
private theorem transpose_replicateRow_mul_self (z : n → α) :
    (replicateRow Unit z)ᵀ * replicateRow Unit z = vecMulVec z z := by
  ext i j
  simp [Matrix.mul_apply, vecMulVec_apply]

/-- The stacked Gram matrix. Let $\alpha$ be a commutative ring, let $H$ be a matrix over $\alpha$
with $n$ columns and finitely many rows, and let $z \in \alpha^n$. Appending the row $z^T$ to
$H$ adds $z z^T$ to the Gram matrix: $$[H; z^T]^T [H; z^T] = H^T H + z z^T.$$ This is (6.5.6) of
[golub2013matrix].

The stacked matrix $[H; z^T]$ is `Matrix.fromRows H (Matrix.replicateRow Unit z)`, and $z z^T$
is `Matrix.vecMulVec z z`. -/
theorem transpose_mul_self_fromRows (H : Matrix m n α) (z : n → α) :
    (fromRows H (replicateRow Unit z))ᵀ * fromRows H (replicateRow Unit z) =
      Hᵀ * H + vecMulVec z z := by
  rw [transpose_fromRows, fromCols_mul_fromRows, transpose_replicateRow_mul_self]

/-- The signed stacked Gram matrix. Let $\alpha$ be a commutative ring, let $H$ be a matrix over
$\alpha$ with $n$ columns and finitely many rows, let $z \in \alpha^n$, and let
$S = \operatorname{diag}(I, -1)$. Then $$[H; z^T]^T S \, [H; z^T] = H^T H - z z^T.$$ This is
(6.5.10) of [golub2013matrix].

The signature $S$ is `LieAlgebra.Orthogonal.indefiniteDiagonal m Unit α`. -/
theorem transpose_mul_indefiniteDiagonal_mul_fromRows [DecidableEq m] (H : Matrix m n α)
    (z : n → α) :
    (fromRows H (replicateRow Unit z))ᵀ * LieAlgebra.Orthogonal.indefiniteDiagonal m Unit α *
        fromRows H (replicateRow Unit z) = Hᵀ * H - vecMulVec z z := by
  have hS : LieAlgebra.Orthogonal.indefiniteDiagonal m Unit α * fromRows H (replicateRow Unit z) =
      fromRows H (-replicateRow Unit z) := by
    ext (i | u) j <;> simp [LieAlgebra.Orthogonal.indefiniteDiagonal, diagonal_mul]
  rw [Matrix.mul_assoc, hS, transpose_fromRows, fromCols_mul_fromRows, Matrix.mul_neg,
    transpose_replicateRow_mul_self, sub_eq_add_neg]

variable [DecidableEq m] [Fintype p] [DecidableEq p]

/-- An orthogonal reduction preserves the Gram matrix. Let $\alpha$ be a commutative ring, let $Q$
be an orthogonal matrix with rows and columns indexed by $m \oplus p$, let $M$ be a matrix with
rows indexed by $m \oplus p$, and let $R$ be a matrix with rows indexed by $m$. If
$Q^T M = [R; 0]$, then $$M^T M = R^T R.$$ This is the step from (6.5.7) to $\tilde A = R^T R$ in
[golub2013matrix] §6.5.4.

The book prints $\tilde A = R R^T$, a typo for $R^T R$; it concludes correctly that
$\tilde G = R^T$. The matrix $[R; 0]$ is `Matrix.fromRows R 0`, with the zero block indexed by
$p$. -/
theorem transpose_mul_self_eq_of_mem_orthogonalGroup {Q : Matrix (m ⊕ p) (m ⊕ p) α}
    (hQ : Q ∈ orthogonalGroup (m ⊕ p) α) {M : Matrix (m ⊕ p) n α} {R : Matrix m n α}
    (h : Qᵀ * M = fromRows R 0) : Mᵀ * M = Rᵀ * R := by
  have e : Mᵀ * M = (Qᵀ * M)ᵀ * (Qᵀ * M) := by
    rw [transpose_mul, transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc Q,
      (mem_orthogonalGroup_iff _ α).1 hQ, Matrix.one_mul]
  rw [e, h, transpose_fromRows, fromCols_mul_fromRows, transpose_zero, Matrix.zero_mul,
    add_zero]

/-- A $J$-orthogonal reduction of a stacked matrix preserves its signed Gram matrix. Let $\alpha$ be
a commutative ring, let $H, R$ be matrices over $\alpha$ with rows indexed by a finite type $m$
and $n$ columns, let $z, z' \in \alpha^n$, and let $S = \operatorname{diag}(I, -1)$. Let $Y$ be
$S$-orthogonal, that is, $Y S Y^T = S$. If $Y^T [H; z^T] = [R; z'^T]$, then $$H^T H - z z^T =
R^T R - z' z'^T.$$

The matrix $Y$ is `Hy`, and $S$-orthogonality is `Matrix.IsJOrthogonal` for
`LieAlgebra.Orthogonal.indefiniteDiagonal m Unit α`. -/
theorem transpose_mul_self_sub_eq_of_isJOrthogonal_of_fromRows
    {Hy : Matrix (m ⊕ Unit) (m ⊕ Unit) α}
    (hHy : IsJOrthogonal (LieAlgebra.Orthogonal.indefiniteDiagonal m Unit α) Hy)
    {H R : Matrix m n α} {z z' : n → α}
    (h : Hyᵀ * fromRows H (replicateRow Unit z) = fromRows R (replicateRow Unit z')) :
    Hᵀ * H - vecMulVec z z = Rᵀ * R - vecMulVec z' z' := by
  rw [← transpose_mul_indefiniteDiagonal_mul_fromRows,
    ← transpose_mul_indefiniteDiagonal_mul_fromRows, ← h, transpose_mul, transpose_transpose]
  conv_lhs => rw [← hHy]
  simp only [Matrix.mul_assoc]

/-- A $J$-orthogonal reduction downdates the Gram matrix. Let $\alpha$ be a commutative ring, let
$H, R$ be matrices over $\alpha$ with rows indexed by a finite type $m$ and $n$ columns, let
$z \in \alpha^n$, and let $S = \operatorname{diag}(I, -1)$. If $Y$ is $S$-orthogonal, that is,
$Y S Y^T = S$, and $Y^T [H; z^T] = [R; 0]$, then $$H^T H - z z^T = R^T R.$$ This is
(6.5.10)–(6.5.12) of [golub2013matrix].

The matrix $Y$ is `Hy`, and $S$-orthogonality is `Matrix.IsJOrthogonal`. -/
theorem transpose_mul_self_sub_eq_of_isJOrthogonal {Hy : Matrix (m ⊕ Unit) (m ⊕ Unit) α}
    (hHy : IsJOrthogonal (LieAlgebra.Orthogonal.indefiniteDiagonal m Unit α) Hy)
    {H R : Matrix m n α} {z : n → α}
    (h : Hyᵀ * fromRows H (replicateRow Unit z) = fromRows R 0) :
    Hᵀ * H - vecMulVec z z = Rᵀ * R := by
  rw [transpose_mul_self_sub_eq_of_isJOrthogonal_of_fromRows hHy (z' := 0)
    (by rw [h, replicateRow_zero]), vecMulVec_zero, sub_zero]

end Stacked

section RotateStep

variable {α : Type*} [CommRing α] {n : Type*} [Fintype n] [LinearOrder n]

/-- One step of a Cholesky update or downdate keeps the triangular shape. Let $\alpha$ be a
commutative ring, let the index set $n$ be finite and linearly ordered, let $R$ be an upper
triangular $n \times n$ matrix over $\alpha$, let $k \in n$, and let $z \in \alpha^n$ with
$z_j = 0$ for $j < k$. Let $G = (g_{pq})$ be any $2 \times 2$ matrix, embedded in the plane of
row $k$ and the appended last row of $[R; z^T]$. Then the product of this embedding with
$[R; z^T]$ is a stacked matrix $[R'; z'^T]$, where $R'$ is upper triangular, $R'$ equals $R$
outside row $k$, $z'_j = 0$ for $j < k$, and $$r'_{kj} = g_{00} r_{kj} + g_{01} z_j, \qquad
z'_j = g_{10} r_{kj} + g_{11} z_j.$$ This is one step of the zeroing sequence $Q_1, Q_2, Q_3$ in
[golub2013matrix] §6.5.4, and also the first rotation in Theorem 6.5.1.

The embedding is `Matrix.planeEmbed (Sum.inl k) (Sum.inr ()) G`. The shape is kept because row
$k$ and the last row are both zero before column $k$. The lemma serves both the Givens sweep of
the update and the hyperbolic sweep of the downdate. -/
theorem fromRows_rotate_step {R : Matrix n n α} (hR : R.IsUpperTriangular) {z : n → α} {k : n}
    (hz : ∀ j < k, z j = 0) (G : Matrix (Fin 2) (Fin 2) α) :
    ∃ (R' : Matrix n n α) (z' : n → α),
      planeEmbed (Sum.inl k) (Sum.inr ()) G * fromRows R (replicateRow Unit z) =
        fromRows R' (replicateRow Unit z') ∧
      R'.IsUpperTriangular ∧ (∀ j < k, z' j = 0) ∧ (∀ i, i ≠ k → R' i = R i) ∧
      (∀ j, R' k j = G 0 0 * R k j + G 0 1 * z j) ∧ ∀ j, z' j = G 1 0 * R k j + G 1 1 * z j := by
  have hne : (Sum.inl k : n ⊕ Unit) ≠ Sum.inr () := Sum.inl_ne_inr
  set M := planeEmbed (Sum.inl k) (Sum.inr ()) G * fromRows R (replicateRow Unit z) with hM
  have hinl : ∀ i j, M (Sum.inl i) j =
      if i = k then G 0 0 * R k j + G 0 1 * z j else R i j := fun i j => by
    rw [hM, planeEmbed_mul_apply G hne]
    by_cases hik : i = k
    · subst hik; simp
    · simp [hik]
  have hinr : ∀ j, M (Sum.inr ()) j = G 1 0 * R k j + G 1 1 * z j := fun j => by
    rw [hM, planeEmbed_mul_apply G hne]
    simp
  refine ⟨M.toRows₁, fun j => M (Sum.inr ()) j, ?_, fun i j hji => ?_, fun j hj => ?_,
    fun i hik => funext fun j => ?_, fun j => ?_, hinr⟩
  · ext (i | u) j
    · rfl
    · rfl
  · rw [toRows₁_apply, hinl]
    split_ifs with hik
    · subst hik
      rw [hR hji, hz j hji]
      ring
    · exact hR hji
  · change M (Sum.inr ()) j = 0
    rw [hinr, hR hj, hz j hj]
    ring
  · rw [toRows₁_apply, hinl, ite_eq_right hik]
  · rw [toRows₁_apply, hinl, ite_eq_left rfl]

end RotateStep

/-! ### Cholesky updating and downdating -/

section CholeskyUpdate

/-- Sign normalization of a triangular factor. Let the index set $n$ be finite and linearly ordered,
and let $R \in \mathbb{R}^{n \times n}$ be upper triangular with $r_{ii} \ne 0$ for all $i$ and
$R^T R = A$. Let $D = \operatorname{diag}(\operatorname{sign} r_{ii})$. Then $DR$ is the
Cholesky factor of $A$: it is upper triangular with the positive diagonal $|r_{ii}|$, and
$(DR)^T (DR) = A$ because $D^2 = I$. This makes precise the statement "the updated Cholesky
factor is given by $\tilde G = R^T$" of [golub2013matrix] §6.5.4, which holds up to signs.

The conclusion is `Matrix.IsCholesky A (D * R)`, with $D$ the matrix
`Matrix.diagonal fun i => SignType.sign (R i i)`. -/
theorem isCholesky_diagonal_sign_mul {n : Type*} [Fintype n] [LinearOrder n]
    {A R : Matrix n n ℝ} (hR : R.IsUpperTriangular) (hd : ∀ i, R i i ≠ 0) (hA : Rᵀ * R = A) :
    IsCholesky A (diagonal (fun i => (SignType.sign (R i i) : ℝ)) * R) := by
  have hsq : ∀ i, (SignType.sign (R i i) : ℝ) * SignType.sign (R i i) = 1 := fun i => by
    rcases lt_or_gt_of_ne (hd i) with h | h
    · simp [sign_neg h]
    · simp [sign_pos h]
  refine ⟨(blockTriangular_diagonal _).mul hR, fun i => ?_, ?_⟩
  · rw [diagonal_mul]
    rcases lt_or_gt_of_ne (hd i) with h | h
    · simp [sign_neg h, h]
    · simp [sign_pos h, h]
  · rw [conjTranspose_eq_transpose_of_trivial, transpose_mul, diagonal_transpose,
      Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), diagonal_mul_diagonal]
    simp only [hsq, diagonal_one, Matrix.one_mul, hA]

/-- A sweep through the planes $(0, \mathrm{last}), (1, \mathrm{last}), \dots$: if each step $t < n$
can advance an invariant by some admissible rotation parameters, then there are admissible
parameters for all $n$ steps, and the invariant holds after the sweep $(E_0 \cdots E_{n-1})^T
M_0 = E_{n-1}^T \cdots E_0^T M_0$. -/
private theorem exists_ofFn_prod_transpose_mul {ι κ : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (E : Fin n → ℝ × ℝ → Matrix ι ι ℝ) (Ok : ℝ × ℝ → Prop) (Inv : ℕ → Matrix ι κ ℝ → Prop)
    {M₀ : Matrix ι κ ℝ} (h0 : Inv 0 M₀)
    (hstep : ∀ t (ht : t < n) M, Inv t M → ∃ p, Ok p ∧ Inv (t + 1) ((E ⟨t, ht⟩ p)ᵀ * M)) :
    ∃ cs : Fin n → ℝ × ℝ, (∀ k, Ok (cs k)) ∧
      Inv n ((List.ofFn fun k => E k (cs k)).prodᵀ * M₀) := by
  suffices h : ∀ t (ht : t ≤ n), ∃ cs : Fin t → ℝ × ℝ, (∀ k, Ok (cs k)) ∧
      Inv t ((List.ofFn fun k => E (Fin.castLE ht k) (cs k)).prodᵀ * M₀) by
    obtain ⟨cs, h₁, h₂⟩ := h n le_rfl
    exact ⟨cs, h₁, h₂⟩
  intro t
  induction t with
  | zero => exact fun _ => ⟨Fin.elim0, fun k => k.elim0, by simpa using h0⟩
  | succ t ih =>
    intro ht
    obtain ⟨cs, hok, hinv⟩ := ih (by omega)
    obtain ⟨p, hp, hinv'⟩ := hstep t (by omega) _ hinv
    refine ⟨Fin.snoc (α := fun _ => ℝ × ℝ) cs p, fun k => ?_, ?_⟩
    · induction k using Fin.lastCases with
      | last => simpa using hp
      | cast k => simpa using hok k
    · have e : (List.ofFn fun k : Fin (t + 1) =>
            E (Fin.castLE ht k) (Fin.snoc (α := fun _ => ℝ × ℝ) cs p k)).prod =
          (List.ofFn fun k : Fin t => E (Fin.castLE (by omega) k) (cs k)).prod *
            E ⟨t, by omega⟩ p := by
        rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        rfl
      rw [e, transpose_mul, Matrix.mul_assoc]
      exact hinv'

/-- Cholesky updating by plane rotations. Let $A = H^T H$ be a Cholesky factorization of
$A \in \mathbb{R}^{n \times n}$, and let $z \in \mathbb{R}^n$. Then there are
$c, s \in \mathbb{R}^n$ with $c_k^2 + s_k^2 = 1$ for all $k$, and a matrix
$R \in \mathbb{R}^{n \times n}$, with the following properties. Let $Q_k$ be the rotation with
cosine $c_k$ and sine $s_k$ in the plane of row $k$ and the appended last row of the stacked
matrix $[H; z^T]$, and let $Q = Q_0 Q_1 \cdots Q_{n-1}$. Then $Q$ is orthogonal, $$Q^T [H;
z^T] = [R; 0],$$ and $A + z z^T = R^T R$ is a Cholesky factorization. This is §6.5.4 of
[golub2013matrix], (6.5.5)–(6.5.7); in the words of the book, "the $Q_k$ update involves only
rows $k$ and $n+1$".

The rotation $Q_k$ is `Matrix.planeRotation (Sum.inl k) (Sum.inr ()) (c k) (s k)`, and $Q$ is
the product of the list `List.ofFn` of these rotations. In the proof, $Q_k$ is
`Matrix.givensPair` of the current entries $(k, k)$ and $(\mathrm{last}, k)$. The new diagonal
entry $\sqrt{r_{kk}^2 + z_k'^2}$ is positive, so no sign normalization is needed. -/
theorem exists_choleskyUpdate {n : ℕ} {A H : Matrix (Fin n) (Fin n) ℝ} (hH : IsCholesky A H)
    (z : Fin n → ℝ) :
    ∃ c s : Fin n → ℝ, (∀ k, c k ^ 2 + s k ^ 2 = 1) ∧ ∃ R : Matrix (Fin n) (Fin n) ℝ,
      (List.ofFn fun k => planeRotation (Sum.inl k) (Sum.inr ()) (c k) (s k)).prod ∈
        orthogonalGroup (Fin n ⊕ Unit) ℝ ∧
      (List.ofFn fun k => planeRotation (Sum.inl k) (Sum.inr ()) (c k) (s k)).prodᵀ *
        fromRows H (replicateRow Unit z) = fromRows R 0 ∧
      IsCholesky (A + vecMulVec z z) R := by
  have hne : ∀ k : Fin n, (Sum.inl k : Fin n ⊕ Unit) ≠ Sum.inr () := fun _ => Sum.inl_ne_inr
  obtain ⟨cs, hok, R, z', hM, hRt, hRd, hz'⟩ := exists_ofFn_prod_transpose_mul
    (fun k p => planeRotation (Sum.inl k) (Sum.inr ()) p.1 p.2) (fun p => p.1 ^ 2 + p.2 ^ 2 = 1)
    (fun t M => ∃ (R : Matrix (Fin n) (Fin n) ℝ) (z' : Fin n → ℝ),
      M = fromRows R (replicateRow Unit z') ∧ R.IsUpperTriangular ∧ (∀ i, 0 < R i i) ∧
        ∀ j : Fin n, (j : ℕ) < t → z' j = 0)
    ⟨H, z, rfl, hH.isUpperTriangular, hH.diag_pos, fun _ h => absurd h (Nat.not_lt_zero _)⟩
    (by
      rintro t ht M ⟨R, z', rfl, hRt, hRd, hz'⟩
      set k : Fin n := ⟨t, ht⟩ with hk
      refine ⟨givensPair (R k k) (z' k), givensPair_sq_add_sq _ _, ?_⟩
      rw [planeRotation_transpose (hne k), planeRotation]
      obtain ⟨R', z'', e, hR't, hz'', hR'i, hR'k, hz''k⟩ :=
        fromRows_rotate_step hRt (k := k) (fun j hj => hz' j hj) _
      have hg := givensPair_fst_mul_add_snd_mul (R k k) (z' k)
      refine ⟨R', z'', e, hR't, fun i => ?_, fun j hj => ?_⟩
      · by_cases hik : i = k
        · subst hik
          rw [hR'k]
          simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
            cons_val_fin_one, Fin.isValue, neg_neg]
          rw [hg.1]
          exact Real.sqrt_pos.2 (by nlinarith [hRd k, sq_nonneg (z' k)])
        · rw [hR'i i hik]
          exact hRd i
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
        · exact hz'' j hj
        · obtain rfl : j = k := Fin.ext hj
          rw [hz''k]
          simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
            cons_val_fin_one, Fin.isValue]
          exact hg.2)
  have hz0 : z' = 0 := funext fun j => hz' j j.isLt
  subst hz0
  rw [replicateRow_zero] at hM
  have hQ : (List.ofFn fun k => planeRotation (Sum.inl k) (Sum.inr ()) (cs k).1 (cs k).2).prod ∈
      orthogonalGroup (Fin n ⊕ Unit) ℝ :=
    Submonoid.list_prod_mem _ fun G hG => by
      obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).1 hG
      exact planeRotation_mem_orthogonalGroup (hne k) (hok k)
  refine ⟨fun k => (cs k).1, fun k => (cs k).2, hok, R, hQ, hM, hRt, hRd, ?_⟩
  rw [conjTranspose_eq_transpose_of_trivial,
    ← transpose_mul_self_eq_of_mem_orthogonalGroup hQ hM, transpose_mul_self_fromRows,
    ← hH.conjTranspose_mul_self, conjTranspose_eq_transpose_of_trivial]

/-- The quadratic form of a signed Gram matrix: over a commutative ring, for a square matrix $R$ and
vectors $z$, $x$, $$x^T (R^T R - z z^T) x = (Rx) \cdot (Rx) - (z \cdot x)^2.$$
-/
theorem dotProduct_transpose_mul_self_sub_mulVec {α n : Type*} [CommRing α] [Fintype n]
    (R : Matrix n n α) (z x : n → α) :
    x ⬝ᵥ ((Rᵀ * R - vecMulVec z z) *ᵥ x) = (R *ᵥ x) ⬝ᵥ (R *ᵥ x) - (z ⬝ᵥ x) ^ 2 := by
  have h1 : x ⬝ᵥ ((Rᵀ * R) *ᵥ x) = (R *ᵥ x) ⬝ᵥ (R *ᵥ x) := by
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  have h2 : x ⬝ᵥ (vecMulVec z z *ᵥ x) = (z ⬝ᵥ x) ^ 2 := by
    rw [dotProduct_mulVec, vecMul_vecMulVec, smul_dotProduct, smul_eq_mul, dotProduct_comm x z, sq]
  rw [sub_mulVec, dotProduct_sub, h1, h2]

/-- The hyperbolic rotation exists at every step of a downdate. Let the index set $n$ be finite and
linearly ordered, let $R \in \mathbb{R}^{n \times n}$ be upper triangular with positive
diagonal, let $k \in n$, and let $z \in \mathbb{R}^n$ with $z_j = 0$ for $j < k$. If
$R^T R - z z^T$ is positive definite, then $z_k^2 < r_{kk}^2$.

The proof tests the quadratic form on $x = R^{-1} e_k$, which is supported on the indices
$\le k$. Then $Rx = e_k$ and $z \cdot x = z_k / r_{kk}$, so $0 < 1 - z_k^2 / r_{kk}^2$. -/
theorem sq_lt_sq_of_posDef_transpose_mul_self_sub {n : Type*} [Fintype n] [LinearOrder n]
    {R : Matrix n n ℝ} (hR : R.IsUpperTriangular) (hd : ∀ i, 0 < R i i) {z : n → ℝ} {k : n}
    (hz : ∀ j < k, z j = 0) (hP : (Rᵀ * R - vecMulVec z z).PosDef) : z k ^ 2 < R k k ^ 2 := by
  have hU : IsUnit R.det := hR.isUnit_det_of_diag_ne_zero fun i => (hd i).ne'
  have hT := hR.inv
  set x : n → ℝ := fun j => R⁻¹ j k with hx
  have hRx : R *ᵥ x = Pi.single k 1 := by
    ext i
    have := congrFun (congrFun (mul_nonsing_inv R hU) i) k
    rw [Matrix.mul_apply] at this
    rw [Pi.single_apply, ← Matrix.one_apply, ← this]
    rfl
  have hkk : R⁻¹ k k * R k k = 1 := by
    have := congrFun (congrFun (nonsing_inv_mul R hU) k) k
    rw [Matrix.mul_apply, one_apply_eq, Finset.sum_eq_single k] at this
    · exact this
    · intro j _ hjk
      rcases lt_or_gt_of_ne hjk with h | h
      · rw [hT h, zero_mul]
      · rw [hR h, mul_zero]
    · simp
  have hzx : z ⬝ᵥ x = z k * R⁻¹ k k := by
    rw [dotProduct, Finset.sum_eq_single k]
    · intro j _ hjk
      rcases lt_or_gt_of_ne hjk with h | h
      · rw [hz j h, zero_mul]
      · rw [hx]
        dsimp only
        rw [hT h, mul_zero]
    · simp
  have hx0 : x ≠ 0 := fun h => by
    have := congrFun h k
    simp only [hx, Pi.zero_apply] at this
    rw [this, zero_mul] at hkk
    exact zero_ne_one hkk
  have hpos := hP.dotProduct_mulVec_pos hx0
  rw [star_trivial, dotProduct_transpose_mul_self_sub_mulVec, hRx, hzx] at hpos
  simp only [dotProduct_single, Pi.single_eq_same, mul_one] at hpos
  have hr := hd k
  have e : z k ^ 2 = (z k * R⁻¹ k k) ^ 2 * R k k ^ 2 := by
    rw [mul_pow, mul_assoc, ← mul_pow, hkk, one_pow, mul_one]
  rw [e]
  nlinarith [sq_nonneg (z k * R⁻¹ k k), pow_pos hr 2]

/-- Cholesky downdating by hyperbolic rotations. Let $A = H^T H$ be a Cholesky factorization of
$A \in \mathbb{R}^{n \times n}$, and let $z \in \mathbb{R}^n$ be such that $A - z z^T$ is
positive definite. Then there are $c, s \in \mathbb{R}^n$ with $c_k^2 - s_k^2 = 1$ for all $k$,
and a matrix $R \in \mathbb{R}^{n \times n}$, with the following properties. Let $Y_k$ be the
hyperbolic rotation $\begin{bmatrix} c_k & -s_k \\ -s_k & c_k \end{bmatrix}$ in the plane of row
$k$ and the appended last row of $[H; z^T]$, and let $Y = Y_0 Y_1 \cdots Y_{n-1}$. Then $Y$ is
$S$-orthogonal, that is, $Y S Y^T = S$ for $S = \operatorname{diag}(I_n, -1)$, $$Y^T [H; z^T] =
[R; 0],$$ and $A - z z^T = R^T R$ is a Cholesky factorization. This is §6.5.4 of
[golub2013matrix], where Theorem 6.5.1 "provides the key step in an induction proof that the
factorization (6.5.12) exists".

The rotation $Y_k$ is `Matrix.hyperbolicRotation (Sum.inl k) (Sum.inr ()) (c k) (s k)`, and
$S$-orthogonality is `Matrix.IsJOrthogonal` for `LieAlgebra.Orthogonal.indefiniteDiagonal (Fin
n) Unit ℝ`. At step $k$ the current stacked matrix $[R'; z'^T]$ still has
$R'^T R' - z' z'^T = A - z z^T$ positive definite. This forces $|z'_k| < r'_{kk}$, so the
hyperbolic pair (6.5.13) exists, and the new diagonal entry $\sqrt{r_{kk}'^2 - z_k'^2}$ is
positive. -/
theorem exists_choleskyDowndate {n : ℕ} {A H : Matrix (Fin n) (Fin n) ℝ} (hH : IsCholesky A H)
    {z : Fin n → ℝ} (hA : (A - vecMulVec z z).PosDef) :
    ∃ c s : Fin n → ℝ, (∀ k, c k ^ 2 - s k ^ 2 = 1) ∧ ∃ R : Matrix (Fin n) (Fin n) ℝ,
      IsJOrthogonal (LieAlgebra.Orthogonal.indefiniteDiagonal (Fin n) Unit ℝ)
        (List.ofFn fun k => hyperbolicRotation (Sum.inl k) (Sum.inr ()) (c k) (s k)).prod ∧
      (List.ofFn fun k => hyperbolicRotation (Sum.inl k) (Sum.inr ()) (c k) (s k)).prodᵀ *
        fromRows H (replicateRow Unit z) = fromRows R 0 ∧
      IsCholesky (A - vecMulVec z z) R := by
  have hne : ∀ k : Fin n, (Sum.inl k : Fin n ⊕ Unit) ≠ Sum.inr () := fun _ => Sum.inl_ne_inr
  have hJ : ∀ (k : Fin n) {c s : ℝ}, c ^ 2 - s ^ 2 = 1 →
      IsJOrthogonal (LieAlgebra.Orthogonal.indefiniteDiagonal (Fin n) Unit ℝ)
        (hyperbolicRotation (Sum.inl k) (Sum.inr ()) c s) :=
    fun k _ _ hcs => isJOrthogonal_hyperbolicRotation (hne k) (ε := Sum.elim (fun _ => 1)
      fun _ => -1) rfl rfl hcs
  have hA' : Hᵀ * H = A := by
    rw [← conjTranspose_eq_transpose_of_trivial, hH.conjTranspose_mul_self]
  obtain ⟨cs, hok, R, z', hM, hRt, hRd, hz', hG⟩ := exists_ofFn_prod_transpose_mul
    (fun k p => hyperbolicRotation (Sum.inl k) (Sum.inr ()) p.1 p.2)
    (fun p => p.1 ^ 2 - p.2 ^ 2 = 1)
    (fun t M => ∃ (R : Matrix (Fin n) (Fin n) ℝ) (z' : Fin n → ℝ),
      M = fromRows R (replicateRow Unit z') ∧ R.IsUpperTriangular ∧ (∀ i, 0 < R i i) ∧
        (∀ j : Fin n, (j : ℕ) < t → z' j = 0) ∧ Rᵀ * R - vecMulVec z' z' = A - vecMulVec z z)
    ⟨H, z, rfl, hH.isUpperTriangular, hH.diag_pos, fun _ h => absurd h (Nat.not_lt_zero _),
      by rw [hA']⟩
    (by
      rintro t ht M ⟨R, z', rfl, hRt, hRd, hz', hG⟩
      set k : Fin n := ⟨t, ht⟩ with hk
      have hlt : |z' k| < |R k k| := by
        rw [← sq_lt_sq]
        exact sq_lt_sq_of_posDef_transpose_mul_self_sub hRt hRd (fun j hj => hz' j hj)
          (hG ▸ hA)
      set x : Fin n ⊕ Unit → ℝ := fun r => fromRows R (replicateRow Unit z') r k with hx
      have hxi : x (Sum.inl k) = R k k := rfl
      have hxr : x (Sum.inr ()) = z' k := rfl
      have hxk : |x (Sum.inr ())| < |x (Sum.inl k)| := by rwa [hxi, hxr]
      obtain ⟨p, hp⟩ : ∃ p, p = hyperbolicPair (x (Sum.inl k)) (x (Sum.inr ())) := ⟨_, rfl⟩
      obtain ⟨hcs, -⟩ := hyperbolicPair_sq_sub_sq hxk
      obtain ⟨hzero, hdiag⟩ := hyperbolicRotation_hyperbolicPair_mulVec (hne k) hxk
      rw [← hp] at hcs hzero hdiag
      refine ⟨p, hcs, ?_⟩
      rw [hyperbolicRotation_transpose (hne k)]
      obtain ⟨R', z'', e, hR't, hz'', hR'i, -, -⟩ :=
        fromRows_rotate_step hRt (k := k) (fun j hj => hz' j hj) !![p.1, -p.2; -p.2, p.1]
      have e' : hyperbolicRotation (Sum.inl k) (Sum.inr ()) p.1 p.2 *
          fromRows R (replicateRow Unit z') = fromRows R' (replicateRow Unit z'') := e
      have hcol : ∀ i, fromRows R' (replicateRow Unit z'') i k =
          (hyperbolicRotation (Sum.inl k) (Sum.inr ()) p.1 p.2 *ᵥ x) i := fun i => by
        rw [← e']
        rfl
      refine ⟨R', z'', e', hR't, fun i => ?_, fun j hj => ?_, ?_⟩
      · by_cases hik : i = k
        · rw [hik]
          have h1 := hcol (Sum.inl k)
          rw [hdiag, fromRows_apply_inl, hxi, hxr, sign_pos (hRd k), SignType.coe_one,
            one_mul] at h1
          rw [h1]
          have h2 := hlt
          rw [abs_of_pos (hRd k)] at h2
          exact Real.sqrt_pos.2 (by nlinarith [abs_lt.1 h2])
        · rw [hR'i i hik]
          exact hRd i
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
        · exact hz'' j hj
        · obtain rfl : j = k := Fin.ext hj
          have h1 := hcol (Sum.inr ())
          rw [hzero, fromRows_apply_inr] at h1
          simpa using h1
      · rw [← hG]
        exact (transpose_mul_self_sub_eq_of_isJOrthogonal_of_fromRows (hJ k hcs)
          (by rw [hyperbolicRotation_transpose (hne k)]; exact e')).symm)
  have hz0 : z' = 0 := funext fun j => hz' j j.isLt
  subst hz0
  rw [replicateRow_zero] at hM
  rw [vecMulVec_zero, sub_zero] at hG
  refine ⟨fun k => (cs k).1, fun k => (cs k).2, hok, R,
    isJOrthogonal_list_prod _ fun G hG => ?_, hM, hRt, hRd, ?_⟩
  · obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).1 hG
    exact hJ k (hok k)
  · rw [conjTranspose_eq_transpose_of_trivial, hG]

/-- One hyperbolic downdating step. Let $A = H^T H$ be a Cholesky factorization of
$A \in \mathbb{R}^{(n+1) \times (n+1)}$, and let $z \in \mathbb{R}^{n+1}$ be such that
$A - z z^T$ is positive definite. Write $\alpha = a_{00}$ and $\mu = z_0$, and let $$c =
\frac{\sqrt{\alpha}}{\sqrt{\alpha - \mu^2}}, \qquad s = \frac{\mu}{\sqrt{\alpha - \mu^2}}.$$
Then $\mu^2 < \alpha$ and $c^2 - s^2 = 1$. Let $g_1 = (h_{01}, \dots, h_{0n})$ be the rest of
the first row of $H$, let $w = (z_1, \dots, z_n)$, and let $G_1^T$ be the trailing $n \times n$
block of $H$. The hyperbolic rotation $\begin{bmatrix} c & -s \\ -s & c \end{bmatrix}$ in the
plane of row $0$ and the appended row maps $[H; z^T]$ to a stacked matrix $[R'; z'^T]$ with the
following properties:

* $z'_0 = 0$ and $r'_{00} > 0$;
* the rows $1, \dots, n$ of $R'$ are those of $H$;
* $w_1 = (z'_1, \dots, z'_n)$ is $w_1 = -s g_1 + c w$;
* $G_1 G_1^T - w_1 w_1^T$ is positive definite.

This is Theorem 6.5.1 of [golub2013matrix], with (6.5.14)–(6.5.15).

The matrix $G_1 G_1^T - w_1 w_1^T$ is the Schur complement of the $(0, 0)$ entry
$\alpha - \mu^2$ of $A - z z^T$; the book says that it is the Schur complement "of $\alpha$".
The trailing block $G_1^T$ is `H.submatrix Fin.succ Fin.succ`, and the rotation is
`Matrix.hyperbolicRotation (Sum.inl 0) (Sum.inr ()) c s`. -/
theorem hyperbolicDowndate_step {n : ℕ} {A H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hH : IsCholesky A H) {z : Fin (n + 1) → ℝ} (hA : (A - vecMulVec z z).PosDef) {c s : ℝ}
    (hc : c = √(A 0 0) / √(A 0 0 - z 0 ^ 2)) (hs : s = z 0 / √(A 0 0 - z 0 ^ 2)) :
    z 0 ^ 2 < A 0 0 ∧ c ^ 2 - s ^ 2 = 1 ∧
      ∃ (R' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (z' : Fin (n + 1) → ℝ),
        hyperbolicRotation (Sum.inl (0 : Fin (n + 1))) (Sum.inr ()) c s *
            fromRows H (replicateRow Unit z) =
          fromRows R' (replicateRow Unit z') ∧
        z' 0 = 0 ∧ 0 < R' 0 0 ∧ (∀ i, i ≠ 0 → R' i = H i) ∧
        (∀ j : Fin n, z' j.succ = -s * H 0 j.succ + c * z j.succ) ∧
        ((H.submatrix Fin.succ Fin.succ)ᵀ * H.submatrix Fin.succ Fin.succ -
          vecMulVec (fun j : Fin n => z' j.succ) (fun j : Fin n => z' j.succ)).PosDef := by
  have hA' : Hᵀ * H = A := by
    rw [← conjTranspose_eq_transpose_of_trivial, hH.conjTranspose_mul_self]
  have h00 : A 0 0 = H 0 0 ^ 2 := by
    rw [← hA', Matrix.mul_apply, Finset.sum_eq_single 0]
    · simp [sq]
    · intro j _ hj
      rw [transpose_apply, hH.isUpperTriangular (Fin.pos_iff_ne_zero.2 hj), zero_mul]
    · simp
  have hpos : 0 < A 0 0 - z 0 ^ 2 := by
    simpa [vecMulVec_apply, sq] using hA.diag_pos (i := 0)
  have hH0 := hH.diag_pos 0
  have hsqrtα : √(A 0 0) = H 0 0 := by rw [h00, Real.sqrt_sq hH0.le]
  set d := √(A 0 0 - z 0 ^ 2) with hd
  have hd0 : 0 < d := Real.sqrt_pos.2 hpos
  have hdd : d ^ 2 = A 0 0 - z 0 ^ 2 := Real.sq_sqrt hpos.le
  rw [hsqrtα] at hc
  have hcs : c ^ 2 - s ^ 2 = 1 := by
    rw [hc, hs, div_pow, div_pow, ← sub_div, hdd, ← h00, div_self hpos.ne']
  obtain ⟨R', z', e, -, -, hR'i, hR'k, hz'⟩ :=
    fromRows_rotate_step hH.isUpperTriangular (k := 0)
      (fun j hj => absurd hj (Fin.not_lt_zero j)) !![c, -s; -s, c]
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
    Fin.isValue] at hR'k hz'
  have hz'0 : z' 0 = 0 := by
    rw [hz', hc, hs]
    field_simp
    ring
  have hR'0 : R' 0 0 = d := by
    rw [hR'k, hc, hs]
    field_simp
    rw [hdd, h00]
    ring
  refine ⟨by linarith, hcs, R', z', e, hz'0, hR'0 ▸ hd0, hR'i, fun j => by rw [hz'], ?_⟩
  -- the signed Gram matrix of the rotated stacked matrix is still `A − z zᵀ`
  have hG : R'ᵀ * R' - vecMulVec z' z' = A - vecMulVec z z := by
    rw [← hA']
    exact (transpose_mul_self_sub_eq_of_isJOrthogonal_of_fromRows
      (isJOrthogonal_hyperbolicRotation Sum.inl_ne_inr (ε := Sum.elim (fun _ => 1) fun _ => -1)
        rfl rfl hcs) (by rw [hyperbolicRotation_transpose Sum.inl_ne_inr]; exact e)).symm
  set B := H.submatrix Fin.succ Fin.succ with hB
  set w : Fin n → ℝ := fun j => z' j.succ with hw
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_mul,
      transpose_transpose, transpose_vecMulVec]
  -- test the form of `A − z zᵀ` on `y = [−(r'₁ᵀ x)/r'₀₀; x]`
  set y : Fin (n + 1) → ℝ := Fin.cons (-(∑ j, R' 0 j.succ * x j) / R' 0 0) x with hy
  have hy0 : y ≠ 0 := fun h => hx (funext fun j => by simpa [hy] using congrFun h j.succ)
  have hRy : R' *ᵥ y = Fin.cons 0 (B *ᵥ x) := by
    ext i
    induction i using Fin.cases with
    | zero =>
      have hr : R' 0 0 ≠ 0 := hR'0 ▸ hd0.ne'
      simp only [mulVec, dotProduct, Fin.sum_univ_succ, hy, Fin.cons_zero, Fin.cons_succ]
      field_simp
      ring
    | succ i =>
      have hrow : R' i.succ = H i.succ := hR'i i.succ (Fin.succ_ne_zero i)
      have h0 : H i.succ 0 = 0 := hH.isUpperTriangular (Fin.succ_pos i)
      simp [mulVec, dotProduct, Fin.sum_univ_succ, hrow, hy, hB, h0]
  have hzy : z' ⬝ᵥ y = w ⬝ᵥ x := by
    rw [dotProduct, Fin.sum_univ_succ, hz'0, zero_mul, zero_add]
    simp [hy, hw, dotProduct]
  have key := hA.dotProduct_mulVec_pos hy0
  rw [star_trivial, ← hG, dotProduct_transpose_mul_self_sub_mulVec, hRy, hzy] at key
  rw [star_trivial, dotProduct_transpose_mul_self_sub_mulVec]
  simpa [dotProduct, Fin.sum_univ_succ] using key

end CholeskyUpdate

end Matrix

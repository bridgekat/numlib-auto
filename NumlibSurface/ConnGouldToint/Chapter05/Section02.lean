/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.Krylov.Lanczos
import Numlib.Analysis.Matrix.ToEuclideanLin

/-!
# Conn, Gould and Toint, Section 5.2: The Lanczos basis

This module formalizes Section 5.2 of [conn2000trust]. For a symmetric operator $H$ and a starting
vector $r_0 \neq 0$, the Lanczos method builds an orthonormal basis $q_0, q_1, \dots$ of the Krylov
spaces $\mathcal{K}_{j+1}(H, r_0) = \operatorname{span}\{r_0, H r_0, \dots, H^j r_0\}$ by the
three-term recurrence
$$\gamma_k q_{k+1} = H q_k - \delta_k q_k - \gamma_{k-1} q_{k-1}, \qquad \delta_k = \langle q_k, H
  q_k \rangle$$
(Algorithms 5.2.1–5.2.2). With $Q_k = [q_0 \cdots q_k]$ and the tridiagonal matrix $T_k$ of the
coefficients, this gives $HQ_k - Q_k T_k = \gamma_k q_{k+1} e_{k+1}^T$ (5.2.14), $Q_k^T Q_k = I$
(5.2.16) and $Q_k^T H Q_k = T_k$ (5.2.17). The preconditioned versions (Algorithms 5.2.3–5.2.4) run
the same recurrence on the transformed operator $R^{-T} H R^{-1}$, and their vectors are orthonormal
in the inner product of $M = R^T R$ (5.2.51)–(5.2.53). Finally, a factorization of $T_k$ gives a
basis of the same space that is conjugate with respect to $H$ (5.2.28)–(5.2.32).

The proofs specialize the backbone modules `Numlib.Krylov.Lanczos` and `Numlib.Krylov.Arnoldi`.

## Main definitions

* Section 5.2.1, `ConnGouldToint.Chapter05.lanczosBasisMatrix`: the matrix $Q_k$ of the Lanczos
  vectors $q_0, \dots, q_k$.
* Equation (5.2.29), `ConnGouldToint.Chapter05.lanczosBlockFactor`: the factor $LU$.
* Equation (5.2.31), `ConnGouldToint.Chapter05.lanczosConjugateBasis`: the basis $Q M^{-T}$.

## Main results

* Lemma 5.2.1, `ConnGouldToint.Chapter05.lemma_5_2_1`: a basis of nested Krylov spaces gets its next
  vector from the previous space and the image of its last vector.
* Algorithms 5.2.1–5.2.2, `ConnGouldToint.Chapter05.algorithm_5_2_1`: the Lanczos vectors satisfy
  the three-term recurrence.
* Equation (5.2.14), `ConnGouldToint.Chapter05.lanczos_relation_5_2_14`:
  $HQ_k - Q_k T_k = \gamma_k q_{k+1} e_{k+1}^T$.
* Equation (5.2.16), `ConnGouldToint.Chapter05.lanczos_orthonormal_5_2_16`: $Q_k^T Q_k = I$ and
  $Q_k^T q_{k+1} = 0$ before breakdown.
* Equation (5.2.17), `ConnGouldToint.Chapter05.lanczos_projection_5_2_17`: $Q_k^T H Q_k = T_k$
  before breakdown.
* Algorithms 5.2.3–5.2.4, `ConnGouldToint.Chapter05.algorithms_5_2_3_5_2_4`: the preconditioned
  Lanczos recurrences (5.2.45)–(5.2.50).
* Equation (5.2.51), `ConnGouldToint.Chapter05.preconditioned_lanczos_orthonormal_5_2_51`: the
  preconditioned Lanczos vectors are $M$-orthonormal.
* Equations (5.2.52)–(5.2.53),
  `ConnGouldToint.Chapter05.preconditioned_lanczos_matrix_relations_5_2_52_53`: the preconditioned
  matrix relations from a transformed Lanczos relation.
* Equations (5.2.52)–(5.2.53),
  `ConnGouldToint.Chapter05.preconditioned_lanczos_run_relations_5_2_52_53`: the same relations for
  the Lanczos run on the transformed matrix.
* Equations (5.2.28)–(5.2.32), `ConnGouldToint.Chapter05.lanczos_conjugate_basis_relations`: the
  conjugate basis diagonalizes the projected quadratic form and spans the range of $Q$.

## Conventions

* The Lanczos vectors are `Krylov.Arnoldi.vec`, the Gram–Schmidt orthonormalization of
  $r_0, Hr_0, H^2 r_0, \dots$; after a breakdown they are zero. The unnormalized next vector is
  `Krylov.Arnoldi.w`. Its norm `Krylov.Lanczos.beta` is the coefficient $\gamma_k$.
* The tridiagonal matrix $T_k$ of order $k + 1$ is `Krylov.Lanczos.tridiag`. Indices start at $0$,
  and $e_{k+1}$ is the last coordinate vector `Pi.single (Fin.last k) 1`.

## Deviations from the source

* **Lemma 5.2.1** (generalization). The nested span identities suffice for the conclusion in any
  real vector space. See `ConnGouldToint.Chapter05.lemma_5_2_1`.
* **Algorithms 5.2.1–5.2.4** (reading). The recurrences use Arnoldi vectors and adjoints in
  inner-product spaces. Normalization is totalized when a Lanczos vector vanishes; the
  orthonormality and compression identities assume the active vectors are nonzero.
-/

namespace ConnGouldToint.Chapter05

open Krylov

/-- **Lemma 5.2.1** of [conn2000trust]. Let $E$ be a real vector space, let $H : E \to E$ be linear,
and let $q_0, q_1, \dots \in E$. Let $i \le k$, and suppose that
$$\mathcal{K}_{j+1}(H, q_0) = \operatorname{span}\{q_0, \dots, q_j\} \quad \text{for all } j \le
  k + 1.$$
Then $q_{i+1} \in \operatorname{span}\{q_0, \dots, q_i\} + \operatorname{span}\{H q_i\}$.

**Generalization.** The book assumes that the $q_j$ are mutually orthonormal. The conclusion
follows from the nested span identities alone, so any real vector space suffices. -/
theorem lemma_5_2_1 {E : Type*} [AddCommGroup E] [Module ℝ E]
    (H : E →ₗ[ℝ] E) (q : ℕ → E) {k i : ℕ} (hi : i ≤ k)
    (hspan : ∀ j ≤ k + 1,
      subspace H (q 0) (j + 1) = Submodule.span ℝ (Set.range fun l : Fin (j + 1) => q l)) :
    q (i + 1) ∈ Submodule.span ℝ (Set.range fun l : Fin (i + 1) => q l) ⊔
      Submodule.span ℝ {H (q i)} := by
  let K := subspace H (q 0) (i + 1)
  let W := K ⊔ Submodule.span ℝ {H (q i)}
  have hK : K ≤ W := le_sup_left
  have hmap : K.map H ≤ W := by
    change (subspace H (q 0) (i + 1)).map H ≤ W
    rw [hspan i (by omega), Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    rcases (Nat.le_of_lt_succ j.isLt).lt_or_eq with hj | hj
    · have hqj : q j ∈ subspace H (q 0) i := by
        cases i with
        | zero => omega
        | succ l =>
          rw [hspan l (by omega)]
          exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
      exact hK (map_subspace_le H (q 0) i ⟨_, hqj, rfl⟩)
    · apply Submodule.mem_sup_right
      change H (q j) ∈ Submodule.span ℝ {H (q i)}
      rw [hj]
      exact Submodule.mem_span_singleton_self _
  have hnext : subspace H (q 0) (i + 1 + 1) ≤ W := by
    rw [subspace_succ_eq_sup_map H (q 0) (Nat.succ_pos i)]
    exact sup_le hK hmap
  have hq : q (i + 1) ∈ subspace H (q 0) (i + 1 + 1) := by
    rw [hspan (i + 1) (by omega)]
    exact Submodule.subset_span ⟨⟨i + 1, Nat.lt_succ_self _⟩, rfl⟩
  simpa [W, K, hspan i (by omega)] using hnext hq


open scoped RealInnerProductSpace

/-- **Algorithms 5.2.1–5.2.2** of [conn2000trust] (Lanczos method). Let $H$ be a symmetric operator
on a real inner product space $E$, and let $r_0 \neq 0$. Let $q_k$ be the Lanczos vectors, let
$y_0 = r_0$ and let $y_{k+1}$ be the unnormalized next vector. Then, with $q_{-1} = 0$,
$$q_k = \frac{y_k}{\|y_k\|}, \qquad y_{k+1} = H q_k - \langle q_k, H q_k \rangle q_k - \|y_k\|
  q_{k-1}.$$

When $y_k = 0$, the first formula gives $q_k = 0$ by Lean's convention $0^{-1} = 0$.

**Reading.** Arnoldi realizes the symmetric three-term recurrence in an inner-product space with
totalized normalization.
-/
theorem algorithm_5_2_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) {r₀ : E} (hr₀ : r₀ ≠ 0) (k : ℕ) :
    let q := Arnoldi.vec H r₀
    let y : ℕ → E := fun | 0 => r₀ | j + 1 => Arnoldi.w H r₀ j
    let prev : ℕ → E := fun | 0 => 0 | j + 1 => q j
    q k = ‖y k‖⁻¹ • y k ∧
      y (k + 1) = H (q k) - ⟪q k, H (q k)⟫ • q k - ‖y k‖ • prev k := by
  intro q y prev
  have hd (j : ℕ) : Lanczos.alpha H r₀ j = ⟪q j, H (q j)⟫ := by
    simp [Lanczos.alpha, Arnoldi.coeff, q]
  cases k with
  | zero =>
    refine ⟨by simpa using Arnoldi.vec_zero H r₀ hr₀, ?_⟩
    change Arnoldi.w H r₀ 0 = H (q 0) - ⟪q 0, H (q 0)⟫ • q 0 - ‖r₀‖ • (0 : E)
    have ha : H (q 0) = Lanczos.alpha H r₀ 0 • q 0 + Arnoldi.w H r₀ 0 := by
      have h := Lanczos.apply_vec_zero r₀ hH
      rw [Lanczos.beta, ← Arnoldi.w_eq_norm_smul_vec] at h
      simpa only [q, RCLike.ofReal_real_eq_id, id_eq] using h
    rw [← hd, ha, smul_zero, sub_zero]
    abel
  | succ j =>
    refine ⟨by simpa using Arnoldi.vec_succ_eq H r₀ j, ?_⟩
    change Arnoldi.w H r₀ (j + 1) = H (q (j + 1)) - ⟪q (j + 1), H (q (j + 1))⟫ •
      q (j + 1) - ‖Arnoldi.w H r₀ j‖ • q j
    simpa only [q, hd, Lanczos.beta, RCLike.ofReal_real_eq_id, id_eq] using
      Lanczos.w_succ_eq r₀ hH j


section MatrixLanczos

open Matrix WithLp

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Section 5.2.1** of [conn2000trust], the matrix of the Lanczos vectors. For
$H \in \mathbb{R}^{n \times n}$ and $r_0 \in \mathbb{R}^n$, the matrix
$Q_k \in \mathbb{R}^{n \times (k+1)}$ has the Lanczos vectors $q_0, \dots, q_k$ of $H$ and $r_0$
as its columns. -/
noncomputable def lanczosBasisMatrix (H : Matrix n n ℝ) (r₀ : n → ℝ) (k : ℕ) :
    Matrix n (Fin (k + 1)) ℝ :=
  Matrix.of fun i j => ofLp (Arnoldi.vec (toEuclideanLin H) (toLp 2 r₀) j) i

/-- **Equation (5.2.14)** of [conn2000trust]. Let $H \in \mathbb{R}^{n \times n}$ be symmetric, let
$r_0 \in \mathbb{R}^n$, and let $T_k$ be the tridiagonal Lanczos matrix of order $k + 1$. Then
$$H Q_k - Q_k T_k = \gamma_k q_{k+1} e_{k+1}^T,$$
where $\gamma_k$ is the norm of the unnormalized next vector.

The rank-one remainder has its only nonzero column in the last position. It vanishes at a
breakdown, where $q_{k+1} = 0$.

**Reading.** Matrix relation expressed using totalized Lanczos vectors without an active-vector
restriction.
-/
theorem lanczos_relation_5_2_14 {H : Matrix n n ℝ} (hH : H.IsSymm)
    (r₀ : n → ℝ) (k : ℕ) :
    let A := toEuclideanLin H
    let b : EuclideanSpace ℝ n := toLp 2 r₀
    let Q := lanczosBasisMatrix H r₀ k
    let T := Lanczos.tridiag A b (k + 1)
    let qnext := ofLp (Arnoldi.vec A b (k + 1))
    H * Q - Q * T = Lanczos.beta A b k • Matrix.vecMulVec qnext (Pi.single (Fin.last k) 1) := by
  let A := toEuclideanLin H
  let b : EuclideanSpace ℝ n := toLp 2 r₀
  let Q := lanczosBasisMatrix H r₀ k
  let T := Lanczos.tridiag A b (k + 1)
  let q := Arnoldi.vec A b
  change H * Q - Q * T =
    Lanczos.beta A b k • Matrix.vecMulVec (ofLp (q (k + 1))) (Pi.single (Fin.last k) 1)
  have hQ (z : Fin (k + 1) → ℝ) :
      toLp 2 (Q *ᵥ z) = ∑ j : Fin (k + 1), z j • q j := by
    rw [← Matrix.toEuclideanLin_toLp, Matrix.toEuclideanLin_apply_eq_sum]
    exact Finset.sum_congr rfl fun j _ => by
      change z j • toLp 2 (ofLp (q j)) = z j • q j
      rw [WithLp.toLp_ofLp]
  apply sub_eq_iff_eq_add'.mpr
  apply Matrix.ext_iff_mulVec.mpr
  intro z
  apply WithLp.toLp_injective 2
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec z Q T,
    Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul, single_one_dotProduct,
    smul_smul, WithLp.toLp_add, WithLp.toLp_smul, WithLp.toLp_ofLp,
    ← Matrix.toEuclideanLin_toLp H, hQ, hQ]
  simpa only [A, b, T, q, Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id,
    RCLike.ofReal_real_eq_id, id_eq] using Lanczos.apply_sum b hH.isSymmetric_toEuclideanLin k z

/-- **Equation (5.2.16)** of [conn2000trust]. Let $H \in \mathbb{R}^{n \times n}$ and
$r_0 \in \mathbb{R}^n$, and suppose that the Lanczos vectors $q_0, \dots, q_k$ are nonzero. Then
$$Q_k^T Q_k = I \quad \text{and} \quad Q_k^T q_{k+1} = 0.$$
-/
theorem lanczos_orthonormal_5_2_16 (H : Matrix n n ℝ) (r₀ : n → ℝ) (k : ℕ)
    (hactive : ∀ j : Fin (k + 1), Arnoldi.vec (toEuclideanLin H) (toLp 2 r₀) j ≠ 0) :
    let q := Arnoldi.vec (toEuclideanLin H) (toLp 2 r₀)
    let Q := lanczosBasisMatrix H r₀ k
    Qᵀ * Q = 1 ∧ Qᵀ *ᵥ ofLp (q (k + 1)) = 0 := by
  let A := toEuclideanLin H
  let b : EuclideanSpace ℝ n := toLp 2 r₀
  let q := Arnoldi.vec A b
  let Q := lanczosBasisMatrix H r₀ k
  change Qᵀ * Q = 1 ∧ Qᵀ *ᵥ ofLp (q (k + 1)) = 0
  constructor
  · ext i j
    change ofLp (q i) ⬝ᵥ ofLp (q j) = (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) i j
    rw [← EuclideanSpace.inner_toLp_toLp_real, WithLp.toLp_ofLp, WithLp.toLp_ofLp]
    by_cases h : i = j
    · subst j
      rw [real_inner_self_eq_norm_sq, Arnoldi.norm_vec_eq_one_of_ne_zero A b (hactive i),
        one_pow, Matrix.one_apply_eq]
    · rw [Arnoldi.inner_vec_eq_zero A b (fun he => h (Fin.ext he)), Matrix.one_apply_ne h]
  · ext i
    change ofLp (q i) ⬝ᵥ ofLp (q (k + 1)) = 0
    rw [← EuclideanSpace.inner_toLp_toLp_real, WithLp.toLp_ofLp, WithLp.toLp_ofLp]
    exact Arnoldi.inner_vec_eq_zero A b (ne_of_lt i.isLt)

/-- **Equation (5.2.17)** of [conn2000trust]. Let $H \in \mathbb{R}^{n \times n}$ be symmetric and
$r_0 \in \mathbb{R}^n$, and suppose that the Lanczos vectors $q_0, \dots, q_k$ are nonzero. Then
$$Q_k^T H Q_k = T_k.$$

The proof projects (5.2.14) onto the columns of $Q_k$ and uses (5.2.16). -/
theorem lanczos_projection_5_2_17 {H : Matrix n n ℝ} (hH : H.IsSymm)
    (r₀ : n → ℝ) (k : ℕ)
    (hactive : ∀ j : Fin (k + 1), Arnoldi.vec (toEuclideanLin H) (toLp 2 r₀) j ≠ 0) :
    let Q := lanczosBasisMatrix H r₀ k
    Qᵀ * H * Q = Lanczos.tridiag (toEuclideanLin H) (toLp 2 r₀) (k + 1) := by
  let Q := lanczosBasisMatrix H r₀ k
  obtain ⟨horth, hperp⟩ := lanczos_orthonormal_5_2_16 H r₀ k hactive
  have hrec := sub_eq_iff_eq_add'.mp (lanczos_relation_5_2_14 hH r₀ k)
  change Qᵀ * H * Q = _
  rw [Matrix.mul_assoc, hrec, Matrix.mul_add, ← Matrix.mul_assoc, horth,
    Matrix.one_mul, Matrix.mul_smul, Matrix.mul_vecMulVec, hperp]
  simp

end MatrixLanczos

/-- **Algorithms 5.2.3–5.2.4** of [conn2000trust] and **Equations (5.2.45)–(5.2.50)**
(preconditioned Lanczos method). Let $E$ and $F$ be real Hilbert spaces, let $R : E \to F$ be an
isomorphism with inverse $S$, let $M = R^* R$, so that $M^{-1} = S S^*$, let $H$ be a symmetric
operator on $E$, and let $r_0 \neq 0$. Run the Lanczos method on $\bar{H} = S^* H S$ from
$\bar{r}_0 = S^* r_0$, with vectors $\bar{q}_j$ and unnormalized vectors
$\bar{y}_0 = \bar{r}_0$, $\bar{y}_{j+1}$. Let
$$q_j = S \bar{q}_j, \quad y_j = S \bar{y}_j, \quad w_j = M q_j, \quad t_j = M y_j, \quad
  \gamma_{k-1} = \|\bar{y}_k\|, \quad \delta_k = \langle q_k, H q_k \rangle,$$
with $q_{-1} = w_{-1} = 0$. Then Algorithm 5.2.3 holds:
$$y_0 = M^{-1} r_0, \quad \gamma_{k-1} = \sqrt{\langle y_k, M y_k \rangle}, \quad q_k = y_k /
  \gamma_{k-1}, \quad y_{k+1} = M^{-1} H q_k - \delta_k q_k - \gamma_{k-1} q_{k-1},$$
and Algorithm 5.2.4, with the dual vectors $t_k$ and $w_k$, holds:
$$t_0 = r_0, \quad y_k = M^{-1} t_k, \quad \gamma_{k-1} = \sqrt{\langle t_k, y_k \rangle}, \quad
  w_k = t_k / \gamma_{k-1}, \quad t_{k+1} = H q_k - \delta_k w_k - \gamma_{k-1} w_{k-1}.$$

The number $\gamma_{-1} = \|\bar{r}_0\|$ normalizes the first vector.

**Reading.** Uses Hilbert-space equivalence and adjoints, with totalized normalization.
-/
theorem algorithms_5_2_3_5_2_4
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (R : E ≃L[ℝ] F) {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) {r₀ : E} (hr₀ : r₀ ≠ 0)
    (k : ℕ) :
    let S := R.symm.toContinuousLinearMap
    let L := R.toContinuousLinearMap
    let M := L.adjoint.comp L
    let Minv := S.comp S.adjoint
    let Hbar := S.adjoint.toLinearMap ∘ₗ H ∘ₗ S.toLinearMap
    let rbar := S.adjoint r₀
    let qbar := Arnoldi.vec Hbar rbar
    let ybar : ℕ → F := fun | 0 => rbar | j + 1 => Arnoldi.w Hbar rbar j
    let q (j : ℕ) := S (qbar j)
    let y (j : ℕ) := S (ybar j)
    let w (j : ℕ) := M (q j)
    let t (j : ℕ) := M (y j)
    let prev : ℕ → E := fun | 0 => 0 | j + 1 => q j
    let prevW : ℕ → E := fun | 0 => 0 | j + 1 => w j
    let γ := ‖ybar k‖
    let δ := ⟪q k, H (q k)⟫
    y 0 = Minv r₀ ∧ t 0 = r₀ ∧
      γ = Real.sqrt ⟪y k, M (y k)⟫ ∧ q k = γ⁻¹ • y k ∧
      y (k + 1) = Minv (H (q k)) - δ • q k - γ • prev k ∧
      y k = Minv (t k) ∧ γ = Real.sqrt ⟪t k, y k⟫ ∧ w k = γ⁻¹ • t k ∧
      t (k + 1) = H (q k) - δ • w k - γ • prevW k := by
  intro S L M Minv Hbar rbar qbar ybar q y w t prev prevW γ δ
  have hLS (z : F) : L (S z) = z := R.apply_symm_apply z
  have hSL (z : E) : S (L z) = z := R.symm_apply_apply z
  have hSadL (z : F) : S.adjoint (L.adjoint z) = z := by
    have he : L.comp S = ContinuousLinearMap.id ℝ F := ContinuousLinearMap.ext hLS
    have he' := congrArg ContinuousLinearMap.adjoint he
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] at he'
    exact congrArg (fun B : F →L[ℝ] F ↦ B z) he'
  have hLadS (z : E) : L.adjoint (S.adjoint z) = z := by
    have he : S.comp L = ContinuousLinearMap.id ℝ E := ContinuousLinearMap.ext hSL
    have he' := congrArg ContinuousLinearMap.adjoint he
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] at he'
    exact congrArg (fun B : E →L[ℝ] E ↦ B z) he'
  have hMS (z : F) : M (S z) = L.adjoint z := by
    change L.adjoint (L (S z)) = _
    rw [hLS]
  have hMinv (z : E) : Minv (M z) = z := by
    change S (S.adjoint (L.adjoint (L z))) = z
    rw [hSadL, hSL]
  have hMMinv (z : E) : M (Minv z) = z := by
    change M (S (S.adjoint z)) = z
    rw [hMS, hLadS]
  have hsym : Hbar.IsSymmetric := by
    intro u v
    change ⟪S.adjoint (H (S u)), v⟫ = ⟪u, S.adjoint (H (S v))⟫
    rw [S.adjoint_inner_left, S.adjoint_inner_right, hH]
  have hrbar : rbar ≠ 0 := by
    intro h
    have he := hLadS r₀
    change L.adjoint rbar = r₀ at he
    rw [h, map_zero] at he
    exact hr₀ he.symm
  obtain ⟨hqbar, hybar⟩ := algorithm_5_2_1 hsym hrbar k
  let prevBar : ℕ → F := fun | 0 => 0 | j + 1 => qbar j
  change qbar k = γ⁻¹ • ybar k at hqbar
  change ybar (k + 1) = Hbar (qbar k) - ⟪qbar k, Hbar (qbar k)⟫ • qbar k -
    γ • prevBar k at hybar
  have hδ : ⟪qbar k, Hbar (qbar k)⟫ = δ := S.adjoint_inner_right _ _
  have hprev (j : ℕ) : S (prevBar j) = prev j := by
    cases j <;> simp [prevBar, prev, q]
  have hprevW (j : ℕ) : M (prev j) = prevW j := by
    cases j <;> simp [prevW, prev, w]
  have hy (j : ℕ) : Minv (t j) = y j := hMinv _
  have hq : q k = γ⁻¹ • y k := by
    change S (qbar k) = _
    rw [hqbar, map_smul]
  have hyrec : y (k + 1) = Minv (H (q k)) - δ • q k - γ • prev k := by
    change S (ybar (k + 1)) = _
    rw [hybar, map_sub, map_sub, map_smul, map_smul, hδ, hprev]
    rfl
  have hnorm : γ = Real.sqrt ⟪y k, M (y k)⟫ := by
    change ‖ybar k‖ = Real.sqrt ⟪S (ybar k), M (S (ybar k))⟫
    rw [hMS, L.adjoint_inner_right, hLS, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  refine ⟨rfl, hMMinv r₀, hnorm, hq, hyrec, (hy k).symm, ?_, ?_, ?_⟩
  · simpa only [t, real_inner_comm (M (y k))] using hnorm
  · change M (q k) = _
    rw [hq, map_smul]
  · change M (y (k + 1)) = _
    rw [hyrec, map_sub, map_sub, map_smul, map_smul, hMMinv, hprevW]


/-- **Equation (5.2.51)** of [conn2000trust]. Let $E$ and $F$ be real Hilbert spaces, let
$R : E \to F$ be an isomorphism with inverse $S$, let $M = R^* R$, and let $H$ be linear on $E$
and $r_0 \in E$. Let $\bar{q}_j$ be the Lanczos vectors of $S^* H S$ and $S^* r_0$, and let
$q_j = S \bar{q}_j$. Then
$$\langle q_i, M q_j \rangle = 0 \quad (i \neq j), \qquad \langle q_i, M q_i \rangle = 1 \quad
  \text{if } \bar{q}_i \neq 0.$$

**Reading.** Weighted orthonormality uses the transported Hilbert-space inner products for active
vectors.
-/
theorem preconditioned_lanczos_orthonormal_5_2_51
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (R : E ≃L[ℝ] F) (H : E →ₗ[ℝ] E) (r₀ : E) (i j : ℕ) :
    let S := R.symm.toContinuousLinearMap
    let L := R.toContinuousLinearMap
    let M := L.adjoint.comp L
    let Hbar := S.adjoint.toLinearMap ∘ₗ H ∘ₗ S.toLinearMap
    let qbar := Arnoldi.vec Hbar (S.adjoint r₀)
    let q (k : ℕ) := S (qbar k)
    (i ≠ j → ⟪q i, M (q j)⟫ = 0) ∧ (qbar i ≠ 0 → ⟪q i, M (q i)⟫ = 1) := by
  intro S L M Hbar qbar q
  have hinner (a b : F) : ⟪S a, M (S b)⟫ = ⟪a, b⟫ := by
    change ⟪S a, L.adjoint (L (S b))⟫ = _
    rw [L.adjoint_inner_right]
    change ⟪R (R.symm a), R (R.symm b)⟫ = _
    rw [R.apply_symm_apply, R.apply_symm_apply]
  refine ⟨fun hij ↦ ?_, fun hi ↦ ?_⟩
  · change ⟪S (qbar i), M (S (qbar j))⟫ = 0
    rw [hinner]
    exact Arnoldi.inner_vec_eq_zero Hbar (S.adjoint r₀) hij
  · change ⟪S (qbar i), M (S (qbar i))⟫ = 1
    rw [hinner, real_inner_self_eq_norm_sq, Arnoldi.norm_vec_eq_one_of_ne_zero Hbar
      (S.adjoint r₀) hi, one_pow]

open scoped Matrix in
/-- **Equations (5.2.52)–(5.2.53)** of [conn2000trust]. Let $H, R \in \mathbb{R}^{n \times n}$ with
$R$ invertible, let $\bar{Q} \in \mathbb{R}^{n \times m}$, $T \in \mathbb{R}^{m \times m}$,
$\bar{q} \in \mathbb{R}^n$, $e \in \mathbb{R}^m$ and $\gamma \in \mathbb{R}$. Suppose that
$$R^{-T} H R^{-1} \bar{Q} - \bar{Q} T = \gamma \bar{q} e^T, \qquad \bar{Q}^T \bar{Q} = I, \qquad
  \bar{Q}^T \bar{q} = 0.$$
Then, with $Q = R^{-1} \bar{Q}$ and $M = R^T R$,
$$HQ - MQT = \gamma (R^T \bar{q}) e^T \quad \text{and} \quad Q^T H Q = T.$$

The inverse of $R$ is a matrix `Rinv` with `Rinv * R = 1` and `R * Rinv = 1`. In the
application, $e$ is the last coordinate vector. -/
theorem preconditioned_lanczos_matrix_relations_5_2_52_53
    {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (H R Rinv : Matrix n n ℝ) (Qbar : Matrix n m ℝ) (T : Matrix m m ℝ)
    (qbar : n → ℝ) (e : m → ℝ) (γ : ℝ)
    (hL : Rinv * R = 1) (hR : R * Rinv = 1)
    (hLanczos : (Rinvᵀ * H * Rinv) * Qbar - Qbar * T = γ • Matrix.vecMulVec qbar e)
    (horth : Qbarᵀ * Qbar = 1) (hperp : Qbarᵀ *ᵥ qbar = 0) :
    let Q := Rinv * Qbar
    let M := Rᵀ * R
    H * Q - M * Q * T = γ • Matrix.vecMulVec (Rᵀ *ᵥ qbar) e ∧ Qᵀ * H * Q = T := by
  let Hbar := Rinvᵀ * H * Rinv
  let Q := Rinv * Qbar
  have htrans : Rᵀ * Rinvᵀ = 1 := by
    rw [← Matrix.transpose_mul, hL, Matrix.transpose_one]
  have hleft : Rᵀ * (Hbar * Qbar) = H * Q := by
    change Rᵀ * ((Rinvᵀ * H * Rinv) * Qbar) = H * (Rinv * Qbar)
    simp only [← Matrix.mul_assoc, htrans, Matrix.one_mul]
  have hMQ : (Rᵀ * R) * Q = Rᵀ * Qbar := by
    change (Rᵀ * R) * (Rinv * Qbar) = Rᵀ * Qbar
    calc
      _ = Rᵀ * ((R * Rinv) * Qbar) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hR, Matrix.one_mul]
  change H * Q - (Rᵀ * R) * Q * T = _ ∧ Qᵀ * H * Q = _
  constructor
  · have hr := congrArg (fun X : Matrix n m ℝ ↦ Rᵀ * X) hLanczos
    change Rᵀ * (Hbar * Qbar - Qbar * T) = _ at hr
    rw [Matrix.mul_sub, hleft, ← Matrix.mul_assoc Rᵀ Qbar T, ← hMQ,
      Matrix.mul_smul, Matrix.mul_vecMulVec] at hr
    exact hr
  · have hsum : Hbar * Qbar = Qbar * T + γ • Matrix.vecMulVec qbar e :=
      sub_eq_iff_eq_add'.mp hLanczos
    calc
      Qᵀ * H * Q = Qbarᵀ * (Hbar * Qbar) := by
        change (Rinv * Qbar)ᵀ * H * (Rinv * Qbar) =
          Qbarᵀ * ((Rinvᵀ * H * Rinv) * Qbar)
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = T := by
        rw [hsum, Matrix.mul_add, ← Matrix.mul_assoc Qbarᵀ Qbar T, horth,
          Matrix.one_mul, Matrix.mul_smul, Matrix.mul_vecMulVec, hperp]
        simp

open Matrix WithLp in
/-- **Equations (5.2.52)–(5.2.53)** of [conn2000trust], for the Lanczos run. Let
$H \in \mathbb{R}^{n \times n}$ be symmetric and $R \in \mathbb{R}^{n \times n}$ invertible, and
let $r_0 \in \mathbb{R}^n$. Run the Lanczos method on $\bar{H} = R^{-T} H R^{-1}$ from
$\bar{r}_0 = R^{-T} r_0$, and suppose that its vectors $\bar{q}_0, \dots, \bar{q}_k$ are
nonzero. Let $Q = R^{-1} \bar{Q}_k$, $M = R^T R$ and $T = T_k$. Then
$$HQ - MQT = \gamma_k (R^T \bar{q}_{k+1}) e_{k+1}^T \quad \text{and} \quad Q^T H Q = T.$$

The proof applies (5.2.14) and (5.2.16) to $\bar{H}$. -/
theorem preconditioned_lanczos_run_relations_5_2_52_53
    {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℝ} (hH : H.IsSymm)
    (R Rinv : Matrix n n ℝ) (r₀ : n → ℝ) (k : ℕ)
    (hL : Rinv * R = 1) (hR : R * Rinv = 1)
    (hactive : ∀ j : Fin (k + 1),
      Arnoldi.vec (toEuclideanLin (Rinvᵀ * H * Rinv)) (toLp 2 (Rinvᵀ *ᵥ r₀)) j ≠ 0) :
    let Hbar := Rinvᵀ * H * Rinv
    let rbar := Rinvᵀ *ᵥ r₀
    let A := toEuclideanLin Hbar
    let b : EuclideanSpace ℝ n := toLp 2 rbar
    let Q := Rinv * lanczosBasisMatrix Hbar rbar k
    let M := Rᵀ * R
    let T := Lanczos.tridiag A b (k + 1)
    let qnext := ofLp (Arnoldi.vec A b (k + 1))
    H * Q - M * Q * T =
        Lanczos.beta A b k • Matrix.vecMulVec (Rᵀ *ᵥ qnext) (Pi.single (Fin.last k) 1) ∧
      Qᵀ * H * Q = T := by
  let Hbar := Rinvᵀ * H * Rinv
  let rbar := Rinvᵀ *ᵥ r₀
  let A := toEuclideanLin Hbar
  let b : EuclideanSpace ℝ n := toLp 2 rbar
  have hsym : Hbar.IsSymm := by
    change (Rinvᵀ * H * Rinv)ᵀ = Rinvᵀ * H * Rinv
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hH.eq,
      Matrix.mul_assoc]
  obtain ⟨horth, hperp⟩ := lanczos_orthonormal_5_2_16 Hbar rbar k hactive
  exact preconditioned_lanczos_matrix_relations_5_2_52_53 H R Rinv
    (lanczosBasisMatrix Hbar rbar k) (Lanczos.tridiag A b (k + 1))
    (ofLp (Arnoldi.vec A b (k + 1))) (Pi.single (Fin.last k) 1) (Lanczos.beta A b k)
    hL hR (lanczos_relation_5_2_14 hsym rbar k) horth hperp

section ConjugateBasis

open Matrix

variable {n k : Type*} [Fintype n] [Fintype k] [DecidableEq k]

/-- **Equation (5.2.29)** of [conn2000trust]. For matrices $L, U \in \mathbb{R}^{k \times k}$, the
**block factor** is the product $LU$ of the triangular factor $L$ and the matrix $U$ of
orthonormal eigenvectors of the pivot blocks. -/
def lanczosBlockFactor (L U : Matrix k k ℝ) : Matrix k k ℝ := L * U

/-- **Equation (5.2.31)** of [conn2000trust]. For $Q \in \mathbb{R}^{n \times k}$ and
$M \in \mathbb{R}^{k \times k}$, the **conjugate basis** is the matrix $Q M^{-T}$, whose columns
are obtained from the columns of $Q$ by the inverse transpose of $M$.

The inverse is the matrix inverse `Matrix.inv`, which is zero for a singular matrix.

**Reading.** Same M inverse-transpose formula with totalized matrix inverse.
-/
noncomputable def lanczosConjugateBasis (Q : Matrix n k ℝ) (M : Matrix k k ℝ) :
    Matrix n k ℝ :=
  Q * Mᵀ⁻¹

/-- **Equations (5.2.28)–(5.2.32)** of [conn2000trust]. Let $H \in \mathbb{R}^{n \times n}$,
$Q \in \mathbb{R}^{n \times k}$ and $T, L, B, U, D \in \mathbb{R}^{k \times k}$ with
$$Q^T H Q = T, \qquad T = L B L^T, \qquad B = U D U^T,$$
$L$ invertible and $U^T U = I$. Let $M = LU$ and $S = Q M^{-T}$. Then

* $T = M D M^T$, which is (5.2.28),
* $S M^T = Q$, which is (5.2.32),
* $S^T H S = D$, and
* the columns of $S$ span the same space as the columns of $Q$.

When $D$ is diagonal, the columns of $S$ are conjugate with respect to $H$. -/
theorem lanczos_conjugate_basis_relations
    (H : Matrix n n ℝ) (Q : Matrix n k ℝ) (T L B U D : Matrix k k ℝ)
    (hT : Qᵀ * H * Q = T) (hLDL : T = L * B * Lᵀ)
    (hdiag : B = U * D * Uᵀ) (hL : IsUnit L.det) (hU : Uᵀ * U = 1) :
    let M := lanczosBlockFactor L U
    let S := lanczosConjugateBasis Q M
    T = M * D * Mᵀ ∧ S * Mᵀ = Q ∧ Sᵀ * H * S = D ∧
      Set.range S.mulVec = Set.range Q.mulVec := by
  let M := lanczosBlockFactor L U
  let S := lanczosConjugateBasis Q M
  have hUdet : IsUnit U.det := by
    have hdet := congrArg Matrix.det hU
    rw [det_mul, det_one] at hdet
    exact isUnit_of_mul_isUnit_right (hdet ▸ isUnit_one)
  have hM : IsUnit M.det := by
    dsimp [M, lanczosBlockFactor]
    rw [det_mul]
    exact hL.mul hUdet
  have hMt : IsUnit Mᵀ.det := isUnit_det_transpose M hM
  have hdec : T = M * D * Mᵀ := by
    rw [hLDL, hdiag]
    simp only [M, lanczosBlockFactor, transpose_mul, Matrix.mul_assoc]
  have hrecover : S * Mᵀ = Q := by
    exact nonsing_inv_mul_cancel_right Mᵀ Q hMt
  have hconj : Sᵀ * H * S = D := by
    calc
      Sᵀ * H * S = M⁻¹ * (Qᵀ * H * Q) * Mᵀ⁻¹ := by
        simp [S, lanczosConjugateBasis, transpose_mul, transpose_nonsing_inv,
          transpose_transpose, Matrix.mul_assoc]
      _ = D := by
        rw [hT, hdec, ← Matrix.mul_assoc M⁻¹ (M * D) Mᵀ, ← Matrix.mul_assoc M⁻¹ M D,
          nonsing_inv_mul _ hM, Matrix.one_mul, mul_nonsing_inv_cancel_right _ _ hMt]
  refine ⟨hdec, hrecover, hconj, ?_⟩
  apply Set.Subset.antisymm
  · rintro _ ⟨v, rfl⟩
    refine ⟨Mᵀ⁻¹ *ᵥ v, ?_⟩
    change Q *ᵥ (Mᵀ⁻¹ *ᵥ v) = (Q * Mᵀ⁻¹) *ᵥ v
    rw [mulVec_mulVec]
  · rintro _ ⟨v, rfl⟩
    exact ⟨Mᵀ *ᵥ v, by rw [mulVec_mulVec, hrecover]⟩

end ConjugateBasis

end ConnGouldToint.Chapter05

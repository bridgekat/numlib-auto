/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: a new `Mathlib.LinearAlgebra.Tensor` directory beside `Mathlib.LinearAlgebra.Matrix`.
The exception is `Numlib/Analysis/Matrix/SingularValues` (the Ky Fan maximum principle for the
optimal factors), which is not a candidate and would have to go upstream first; keep it free of
any other dependency on the rest of `Numlib` than other upstreaming candidates.
-/
import Numlib.LinearAlgebra.Tensor.HOSVD

/-!
# The Tucker format and the Tucker approximation problem

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$. A tensor $\mathcal{A}$ over $\mathbb{K}$ is in
Tucker format with multilinear rank at most $r = (r_1, \dots, r_d)$ when it is a multilinear product
$\mathcal{A} = \mathcal{S} \times_1 U_1 \cdots \times_d U_d$ of a core $\mathcal{S} \in
\mathbb{K}^{r_1 \times \cdots \times r_d}$ by factors $U_k$ with $r_k$ orthonormal columns
([golub2013matrix], §12.5.3). The Tucker approximation problem (12.5.12)–(12.5.13) asks for the best
such approximation of a given tensor. For given factors, the best core is $\mathcal{A} \times_1
U_1^H \cdots \times_d U_d^H$. The problem then becomes the maximization of $\|\mathcal{A} \times_1
U_1^H \cdots \times_d U_d^H\|$, and this norm can be computed from any mode-$k$ unfolding of
$\mathcal{A}$.

The alternating least-squares iteration of [golub2013matrix] is an unnumbered "Repeat" framework
without a convergence theorem. This module proves that each of its updates is optimal: with all
factors except $U_k$ fixed, the best $U_k$ attains the sum of the squares of the $r_k$ largest
singular values of a matrix built from the mode-$k$ unfolding.

## Main results

* `Tensor.multilinearRank_le_iff`: a tensor has multilinear rank at most $r$ if and only if it is in
  Tucker format with a core of size $r_1 \times \cdots \times r_d$.
* `Tensor.norm_sub_multilinearProd_sq`: for factors with orthonormal columns, the best core is
  $\mathcal{A} \times_1 U_1^H \cdots \times_d U_d^H$.
* `Tensor.norm_multilinearProd_conjTranspose_eq_modeUnfold`: $\|\mathcal{A} \times_1 U_1^H \cdots
  \times_d U_d^H\| = \|U_k^H \mathcal{A}_{(k)} (\bigotimes_{j \neq k} U_j^H)^T\|_F$.
* `Tensor.isGreatest_tucker_update`: one update of the alternating iteration is optimal, by the Ky
  Fan maximum principle.
-/

universe u v

open Matrix
open scoped InnerProductSpace Matrix.Norms.Frobenius

namespace Tensor

variable {ι : Type u} {κ : ι → Type v} [Fintype ι] [DecidableEq ι] [∀ i, Fintype (κ i)]
  {𝕜 : Type*} [RCLike 𝕜] {r : ι → ℕ}

open scoped ComplexOrder in
/-- The Tucker format characterizes the multilinear rank ([golub2013matrix], §12.5.2–12.5.3). Let
$\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let $\mathcal{A}$ be a tensor over $\mathbb{K}$
with finite index types $\kappa_k$, and let $r_k \le |\kappa_k|$ for every mode $k$. Then
$\operatorname{rank} \mathcal{A}_{(k)} \le r_k$ for every $k$ if and only if there are matrices
$U_k \in \mathbb{K}^{\kappa_k \times r_k}$ with $U_k^H U_k = I$ and a core $\mathcal{S} \in
\mathbb{K}^{r_1 \times \cdots \times r_d}$ such that
$$\mathcal{A} = \mathcal{S} \times_1 U_1 \cdots \times_d U_d.$$

The hypothesis $r_k \le |\kappa_k|$ makes sure that factors with $r_k$ orthonormal columns
exist. The multilinear rank is `Tensor.multilinearRank`. For the forward direction, the proof
chooses the factors among the factors of the higher-order SVD: it keeps a set of $r_k$
directions that contains every nonzero singular value of $\mathcal{A}_{(k)}$, and then the
truncated higher-order SVD is exact. -/
theorem multilinearRank_le_iff (A : Tensor κ 𝕜) (hr : ∀ k, r k ≤ Fintype.card (κ k)) :
    (∀ k, multilinearRank A k ≤ r k) ↔
      ∃ (U : ∀ k, Matrix (κ k) (Fin (r k)) 𝕜) (S : Tensor (fun k => Fin (r k)) 𝕜),
        (∀ k, (U k)ᴴ * U k = 1) ∧ A = multilinearProd U S := by
  classical
  constructor
  · intro h
    have hT : ∀ k, ∃ T : Finset (κ k),
        (∀ i, (A.modeUnfold k)ᴴ.colSingularValues i ≠ 0 → i ∈ T) ∧ T.card = r k := by
      intro k
      obtain ⟨T, hsub, -, hcard⟩ := Finset.exists_subsuperset_card_eq (n := r k)
        (Finset.subset_univ (Finset.univ.filter fun i => (A.modeUnfold k)ᴴ.colSingularValues i ≠ 0))
        (by
          rw [← Fintype.card_subtype, card_colSingularValues_ne_zero,
            rank_conjTranspose]
          exact h k)
        (by simpa using hr k)
      exact ⟨T, fun i hi => hsub (by simpa using hi), hcard⟩
    choose T hTsub hTcard using hT
    let eqv : ∀ k, Fin (r k) ≃ T k :=
      fun k => (finCongr (hTcard k).symm).trans (T k).equivFin.symm
    let U : ∀ k, Matrix (κ k) (Fin (r k)) 𝕜 :=
      fun k => (hosvdFactor A k).submatrix id fun j => (eqv k j : κ k)
    have hinj : ∀ k, Function.Injective fun j => (eqv k j : κ k) :=
      fun k => Subtype.val_injective.comp (eqv k).injective
    have hU : ∀ k, (U k)ᴴ * U k = 1 := by
      intro k
      simp only [U]
      rw [conjTranspose_submatrix, ← submatrix_mul _ _ _ id _ Function.bijective_id,
        conjTranspose_hosvdFactor_mul_hosvdFactor, submatrix_one _ (hinj k)]
    have hproj : ∀ k, U k * (U k)ᴴ = hosvdFactor A k
        * diagonal (fun i => if i ∈ T k then 1 else 0) * (hosvdFactor A k)ᴴ := by
      intro k
      ext x y
      rw [Matrix.mul_apply, Matrix.mul_apply]
      simp only [U, submatrix_apply, id_eq, conjTranspose_apply, mul_diagonal, mul_ite, mul_one,
        mul_zero, ite_mul, zero_mul]
      rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_coe_sort (T k)]
      exact Fintype.sum_equiv (eqv k) _ _ fun _ => rfl
    have hA : A = truncatedHOSVD A T := by
      have hle := norm_sub_truncatedHOSVD_sq_le A T
      have hzero : ∑ k, ∑ i ∈ (T k)ᶜ, (A.modeUnfold k)ᴴ.colSingularValues i ^ 2 = 0 := by
        refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun i hi => ?_
        by_contra hne
        exact (Finset.mem_compl.1 hi) (hTsub k i fun h0 => hne (by rw [h0]; ring))
      rw [hzero] at hle
      exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1
        (le_antisymm hle (sq_nonneg _))))
    refine ⟨U, multilinearProd (fun k => (U k)ᴴ) A, hU, ?_⟩
    rw [multilinearProd_multilinearProd]
    simp_rw [hproj]
    exact hA
  · rintro ⟨U, S, -, rfl⟩ k
    rw [multilinearRank, modeUnfold_multilinearProd]
    calc _ ≤ (U k * S.modeUnfold k).rank := rank_mul_le_left _ _
      _ ≤ (U k).rank := rank_mul_le_left _ _
      _ ≤ Fintype.card (Fin (r k)) := rank_le_card_width _
      _ = r k := Fintype.card_fin _

/-- **The best core** ([golub2013matrix], §12.5.3, the display after "the best $\mathcal{S}$ given
any triplet"). Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let
$U_k \in \mathbb{K}^{\kappa_k \times r_k}$ satisfy $U_k^H U_k = I$, and let $\mathcal{S} \in
\mathbb{K}^{r_1 \times \cdots \times r_d}$. Then
$$\|\mathcal{A} - \mathcal{S} \times_i U_i\|^2 = \|\mathcal{A}\|^2 - \|\mathcal{A} \times_i
  U_i^H\|^2 + \|\mathcal{S} - \mathcal{A} \times_i U_i^H\|^2.$$
Hence for fixed factors, the core $\mathcal{S} = \mathcal{A} \times_i U_i^H$ minimizes the
error.

Here $\mathcal{S} \times_i U_i$ is $\mathcal{S} \times_1 U_1 \cdots \times_d U_d$, and
$\mathcal{A} \times_i U_i^H$ is $\mathcal{A} \times_1 U_1^H \cdots \times_d U_d^H$. -/
theorem norm_sub_multilinearProd_sq {U : ∀ k, Matrix (κ k) (Fin (r k)) 𝕜}
    (hU : ∀ k, (U k)ᴴ * U k = 1) (A : Tensor κ 𝕜) (S : Tensor (fun k => Fin (r k)) 𝕜) :
    ‖A - multilinearProd U S‖ ^ 2
      = ‖A‖ ^ 2 - ‖multilinearProd (fun k => (U k)ᴴ) A‖ ^ 2
        + ‖S - multilinearProd (fun k => (U k)ᴴ) A‖ ^ 2 := by
  classical
  rw [norm_sub_sq (𝕜 := 𝕜), norm_sub_sq (𝕜 := 𝕜) S, inner_multilinearProd_right,
    frobenius_norm_multilinearProd_of_orthonormal hU, inner_re_symm (𝕜 := 𝕜) S]
  ring

/-- The Tucker objective in terms of a mode-$k$ unfolding ([golub2013matrix], §12.5.3, the
three-line display). Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, and let
$U_k \in \mathbb{K}^{\kappa_k \times r_k}$ be any matrices. Then for every mode $k$,
$$\|\mathcal{A} \times_1 U_1^H \cdots \times_d U_d^H\| = \Bigl\|U_k^H \mathcal{A}_{(k)}
  \Bigl(\bigotimes_{j \neq k} U_j^H\Bigr)^T\Bigr\|_F.$$

No orthonormality of the $U_k$ is needed. The norm on the right is the Frobenius norm of a
matrix. -/
theorem norm_multilinearProd_conjTranspose_eq_modeUnfold (U : ∀ k, Matrix (κ k) (Fin (r k)) 𝕜)
    (A : Tensor κ 𝕜) (k : ι) :
    ‖multilinearProd (fun k => (U k)ᴴ) A‖
      = ‖(U k)ᴴ * A.modeUnfold k * (piKronecker fun j : {j // j ≠ k} => (U j)ᴴ)ᵀ‖ := by
  rw [← frobenius_norm_modeUnfold, modeUnfold_multilinearProd]

/-- **One update of the alternating iteration is optimal** ([golub2013matrix], §12.5.3, "By freezing
any two … we can improve the third by solving an optimization problem of the form (12.5.3)").
Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let $U_j \in \mathbb{K}^{\kappa_j \times r_j}$
for every mode $j$, let $k$ be a mode with $r_k \le |\kappa_k|$, and let
$$W = \mathcal{A}_{(k)} \Bigl(\bigotimes_{j \neq k} U_j^H\Bigr)^T.$$
Replace the factor $U_k$ by a matrix $V \in \mathbb{K}^{\kappa_k \times r_k}$ with $V^H V = I$,
and keep the other factors. Then the greatest value of the Tucker objective $\|\mathcal{A}
\times_1 U_1^H \cdots \times_k V^H \cdots \times_d U_d^H\|^2$ over all such $V$ exists and is
$$\sigma_1(W)^2 + \cdots + \sigma_{r_k}(W)^2.$$

The singular values $\sigma_{i+1}(W)$ are `Matrix.sortedSingularValues W i`. By
`Tensor.norm_multilinearProd_conjTranspose_eq_modeUnfold`, the objective is $\|V^H W\|_F^2$, and
the Ky Fan maximum principle `Matrix.isGreatest_frobenius_norm_sq_conjTranspose_mul` gives the
result; the maximum is attained at the leading left singular vectors of $W$. Together with the
best core of `Tensor.norm_sub_multilinearProd_sq`, this is why the error never increases along
the iteration. -/
theorem isGreatest_tucker_update (U : ∀ k, Matrix (κ k) (Fin (r k)) 𝕜) (A : Tensor κ 𝕜) (k : ι)
    (hr : r k ≤ Fintype.card (κ k)) :
    IsGreatest ((fun V => ‖multilinearProd (fun j => (Function.update U k V j)ᴴ) A‖ ^ 2) ''
        {V | Vᴴ * V = 1})
      (∑ i ∈ Finset.range (r k), (A.modeUnfold k *
        (piKronecker fun j : {j // j ≠ k} => (U j)ᴴ)ᵀ).sortedSingularValues i ^ 2) := by
  have hobj : (fun V => ‖multilinearProd (fun j => (Function.update U k V j)ᴴ) A‖ ^ 2) =
      fun V => ‖Vᴴ * (A.modeUnfold k * (piKronecker fun j : {j // j ≠ k} => (U j)ᴴ)ᵀ)‖ ^ 2 := by
    funext V
    have hP : (piKronecker fun j : {j // j ≠ k} => (Function.update U k V j)ᴴ) =
        piKronecker fun j : {j // j ≠ k} => (U j)ᴴ := by
      congr 1
      funext j
      rw [Function.update_of_ne j.2]
    rw [norm_multilinearProd_conjTranspose_eq_modeUnfold, Function.update_self, hP,
      Matrix.mul_assoc]
  rw [hobj]
  exact isGreatest_frobenius_norm_sq_conjTranspose_mul _ hr

end Tensor

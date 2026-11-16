/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.GeneralizedSchur
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.LinearAlgebra.Matrix.RealSchur
import Numlib.LinearAlgebra.Matrix.Schur
import Numlib.LinearAlgebra.Matrix.Triangular

/-!
# The periodic Schur form and the product eigenvalue problem

Let $A_0, A_1, \dots, A_p$ be square matrices of order $n$. The **product eigenvalue problem** asks
for the eigenvalues of the product $A_p \cdots A_1 A_0$ without forming the product
([golub2013matrix], §7.8.2). A **periodic decomposition** is a family of unitary matrices
$U_0, \dots, U_p$ such that $U_{i+1}^H A_i U_i$ is upper triangular for $i < p$ and $U_0^H A_p U_p$
has a prescribed shape. Then
$$U_0^H (A_p \cdots A_0) U_0 = (U_0^H A_p U_p)(U_p^H A_{p-1} U_{p-1}) \cdots (U_1^H A_0 U_0)$$
is the product of the transformed factors, and it has the shape of the last factor. This file proves
the existence of three periodic decompositions, for arbitrary factors: the last factor upper
Hessenberg over $\mathbb{R}$ (the Hessenberg–triangular–triangular form (7.8.5) of
[golub2013matrix]), upper quasi-triangular over $\mathbb{R}$ (the periodic real Schur form (7.8.6)),
and upper triangular over $\mathbb{C}$ (the complex periodic Schur form of Bojanczyk, Golub and Van
Dooren, 1992).

The file also defines the block-cyclic matrix of the family, whose block $(i + 1, i)$ is $A_i$ with
indices modulo $p + 1$. It turns the product problem into a structured problem for one matrix: a
periodic decomposition conjugates it into the block-cyclic matrix of the transformed factors. For
the Hessenberg–triangular–triangular form, that matrix is upper Hessenberg after a perfect shuffle
of the rows and the columns.

## Main definitions

* `Matrix.blockCyclic`: the block-cyclic matrix of a family $A_0, \dots, A_p$.

## Main results

* `Matrix.exists_orthogonal_periodicHessenberg_of_isUnit`,
  `Matrix.exists_orthogonal_periodicHessenberg`: orthogonal $U_i$ with $U_{i+1}^T A_i U_i$ upper
  triangular for $i < p$ and $U_0^T A_p U_p$ upper Hessenberg, first for nonsingular
  $A_0, \dots, A_{p-1}$ and then for arbitrary factors.
* `Matrix.exists_orthogonal_periodicRealSchur_of_isUnit`,
  `Matrix.exists_orthogonal_periodicRealSchur`: the same with $U_0^T A_p U_p$ upper
  quasi-triangular.
* `Matrix.exists_unitary_periodicSchur_of_isUnit`, `Matrix.exists_unitary_periodicSchur`: over
  $\mathbb{C}$, unitary $U_i$ with $U_{i+1}^H A_i U_i$ upper triangular for every $i$, indices
  modulo $p + 1$.
* `Matrix.blockDiagonal_conj_blockCyclic`: conjugation by $\operatorname{diag}(U_0, \dots, U_p)$
  carries the block-cyclic matrix of the $A_i$ to that of the $U_{i+1}^T A_i U_i$.
* `Matrix.isUpperHessenberg_reindex_blockCyclic`: if $A_i$ is upper triangular for $i < p$ and $A_p$
  is upper Hessenberg, the block-cyclic matrix is upper Hessenberg in the interleaved order of the
  indices.

## Proof outline

For nonsingular $A_0, \dots, A_{p-1}$, start from a unitary $U_0$ that puts the product
$\Pi = A_p \cdots A_0$ into the required shape, by a Hessenberg reduction, a real Schur form or a
complex Schur form. Then QR factorizations $A_i U_i = U_{i+1} T_i$ for $i < p$ give upper triangular
$T_i$, and the last factor is forced: $U_0^H A_p U_p = (U_0^H \Pi U_0)(T_{p-1} \cdots T_0)^{-1}$.
Each required shape is preserved by right multiplication with an upper triangular matrix, so the
last factor has the shape. For arbitrary factors, $A_i + tI$ is nonsingular for $i < p$ and all
small $t > 0$ (`Matrix.exists_forall_isUnit_det_add_smul_one`). The unitary families for a sequence
$t_k \to 0$ have a convergent subsequence (`Matrix.isCompact_orthogonalGroup`,
`Matrix.isCompact_unitaryGroup`), and the vanishing conditions on the entries pass to the limit. For
the quasi-triangular shape, a pigeonhole argument over the finitely many relations $q(j) < q(i)$ on
the indices first fixes a common block pattern $q$ of the last factor along the subsequence.

## Implementation notes

* A family is `A : Fin (p + 1) → Matrix (Fin n) (Fin n) 𝕜`. The index $i + 1$ of `Fin (p + 1)` wraps
  around, so in the complex periodic Schur form the condition for $i = p$ is that $U_0^H A_p U_p$ is
  upper triangular.
* In `Matrix.blockCyclic` the block index is the second coordinate of `m × Fin (p + 1)`, as in
  Mathlib's `Matrix.blockDiagonal`.
* [golub2013matrix] states the convergence of a product QR iteration (7.8.7) without any precise
  content, and nothing is formalized for it. Mathlib has no results on periodic forms.
-/

open Filter Topology

namespace Matrix

variable {n : ℕ}

section Engine

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The descending product $B_{k-1} \cdots B_1 B_0$ of a sequence $B$ in a monoid, with the value
$1$ at $k = 0$. -/
private def prodDown {R : Type*} [Monoid R] (B : ℕ → R) : ℕ → R
  | 0 => 1
  | k + 1 => B k * prodDown B k

/-- Let $P$ be a property of matrices that is preserved by right multiplication with an upper
triangular matrix, let $B_i$ be nonsingular for $i < p$, and let $U_0$ be unitary with
$P(U_0^H (B_p \cdots B_0) U_0)$; then successive QR factorizations $B_i U_i = U_{i+1} T_i$ give
unitary $U_1, \dots, U_p$ with $U_{i+1}^H B_i U_i$ upper triangular for $i < p$ and
$P(U_0^H B_p U_p)$. -/
private theorem exists_periodic_of_isUnit (P : Matrix (Fin n) (Fin n) 𝕜 → Prop)
    (hP : ∀ S T : Matrix (Fin n) (Fin n) 𝕜, P S → T.IsUpperTriangular → P (S * T)) (p : ℕ)
    (B : ℕ → Matrix (Fin n) (Fin n) 𝕜) (hB : ∀ i < p, IsUnit (B i))
    (U₀ : Matrix (Fin n) (Fin n) 𝕜) (hU₀ : U₀ ∈ unitaryGroup (Fin n) 𝕜)
    (hprod : P (star U₀ * (B p * prodDown B p) * U₀)) :
    ∃ U : ℕ → Matrix (Fin n) (Fin n) 𝕜, U 0 = U₀ ∧ (∀ i, U i ∈ unitaryGroup (Fin n) 𝕜) ∧
      (∀ i < p, (star (U (i + 1)) * B i * U i).IsUpperTriangular) ∧
      P (star (U 0) * B p * U p) := by
  choose V hV hVT using fun M : Matrix (Fin n) (Fin n) 𝕜 => exists_unitary_mul_isUpperTriangular M
  let U : ℕ → Matrix (Fin n) (Fin n) 𝕜 := fun k => Nat.rec U₀ (fun k Uk => star (V (B k * Uk))) k
  have hU0 : U 0 = U₀ := rfl
  have hUs : ∀ k, U (k + 1) = star (V (B k * U k)) := fun k => rfl
  have hUu : ∀ k, U k ∈ unitaryGroup (Fin n) 𝕜 := by
    intro k
    induction k with
    | zero => exact hU₀
    | succ k _ => rw [hUs]; exact Unitary.star_mem (hV _)
  set T : ℕ → Matrix (Fin n) (Fin n) 𝕜 := fun k => star (U (k + 1)) * B k * U k with hTdef
  have hTu : ∀ k, (T k).IsUpperTriangular := fun k => by
    simp only [hTdef, hUs, star_star, Matrix.mul_assoc]
    exact hVT _
  have hBU : ∀ k, B k * U k = U (k + 1) * T k := fun k => by
    simp only [hTdef, ← Matrix.mul_assoc, mem_unitaryGroup_iff.1 (hUu (k + 1)), Matrix.one_mul]
  -- the partial products
  have hpr : ∀ k, prodDown B (k + 1) = B k * prodDown B k := fun k => rfl
  let tr : ℕ → Matrix (Fin n) (Fin n) 𝕜 := fun k => Nat.rec 1 (fun k t => T k * t) k
  have htrs : ∀ k, tr (k + 1) = T k * tr k := fun k => rfl
  have hprU : ∀ k, prodDown B k * U₀ = U k * tr k := by
    intro k
    induction k with
    | zero => simp [prodDown, tr, hU0]
    | succ k ih => rw [hpr, Matrix.mul_assoc, ih, ← Matrix.mul_assoc, hBU, htrs,
        Matrix.mul_assoc]
  have htru : ∀ k, (tr k).IsUpperTriangular := by
    intro k
    induction k with
    | zero => exact blockTriangular_one
    | succ k ih => rw [htrs]; exact (hTu k).mul ih
  have htrunit : ∀ k ≤ p, IsUnit (tr k) := by
    intro k
    induction k with
    | zero => intro _; exact isUnit_one
    | succ k ih =>
      intro hk
      rw [htrs]
      refine IsUnit.mul ?_ (ih (by omega))
      simp only [hTdef]
      exact ((Unitary.isUnit_coe (U := ⟨_, Unitary.star_mem (hUu (k + 1))⟩)).mul
        (hB k (by omega))).mul
        (Unitary.isUnit_coe (U := ⟨_, hUu k⟩))
  refine ⟨U, hU0, hUu, fun i _ => hTu i, ?_⟩
  -- the last factor
  have hkey : star (U 0) * B p * U p * tr p =
      star U₀ * (B p * prodDown B p) * U₀ := by
    rw [Matrix.mul_assoc, ← hprU p, hU0]
    simp only [Matrix.mul_assoc]
  have hinv : star (U 0) * B p * U p =
      star U₀ * (B p * prodDown B p) * U₀ * (tr p)⁻¹ := by
    rw [← hkey, Matrix.mul_assoc _ (tr p),
      mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 (htrunit p le_rfl)), Matrix.mul_one]
  rw [hinv]
  exact hP _ _ hprod (htru p).inv

end Engine

/-- The family $A_0, \dots, A_p$ extended to a sequence indexed by $\mathbb{N}$, with the value $I$
at the indices $j > p$. -/
private noncomputable def extendFamily {𝕜 : Type*} [RCLike 𝕜] {p : ℕ}
    (A : Fin (p + 1) → Matrix (Fin n) (Fin n) 𝕜) (j : ℕ) : Matrix (Fin n) (Fin n) 𝕜 :=
  if h : j < p + 1 then A ⟨j, h⟩ else 1

private theorem extendFamily_castSucc {𝕜 : Type*} [RCLike 𝕜] {p : ℕ}
    (A : Fin (p + 1) → Matrix (Fin n) (Fin n) 𝕜) (i : Fin p) :
    extendFamily A i = A i.castSucc := by
  rw [extendFamily, dite_eq_left (by omega)]; rfl

private theorem extendFamily_last {𝕜 : Type*} [RCLike 𝕜] {p : ℕ}
    (A : Fin (p + 1) → Matrix (Fin n) (Fin n) 𝕜) : extendFamily A p = A (Fin.last p) := by
  rw [extendFamily, dite_eq_left (by omega)]; rfl

/-- **Hessenberg–triangular–triangular form, nonsingular factors** ([golub2013matrix], (7.8.5)). Let
$A_0, \dots, A_p \in \mathbb{R}^{n \times n}$, with $A_i$ nonsingular for every $i < p$. Then
there are orthogonal matrices $U_0, \dots, U_p$ such that
* $U_{i+1}^T A_i U_i$ is upper triangular for every $i < p$;
* $U_0^T A_p U_p$ is upper Hessenberg.

The proof takes a Hessenberg reduction $U_0$ of the product $A_p \cdots A_0$
(`Matrix.exists_unitary_conj_isUpperHessenberg`) and then successive QR factorizations. -/
theorem exists_orthogonal_periodicHessenberg_of_isUnit {p : ℕ}
    (A : Fin (p + 1) → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i : Fin p, IsUnit (A i.castSucc)) :
    ∃ U : Fin (p + 1) → Matrix (Fin n) (Fin n) ℝ, (∀ i, U i ∈ orthogonalGroup (Fin n) ℝ) ∧
      (∀ i : Fin p, ((U i.succ)ᵀ * A i.castSucc * U i.castSucc).IsUpperTriangular) ∧
      ((U 0)ᵀ * A (Fin.last p) * U (Fin.last p)).IsUpperHessenberg := by
  obtain ⟨U₀, hU₀, hH⟩ := exists_unitary_conj_isUpperHessenberg
    (extendFamily A p * prodDown (extendFamily A) p)
  obtain ⟨U, -, hUu, hT, hlast⟩ := exists_periodic_of_isUnit (𝕜 := ℝ) IsUpperHessenberg
    (fun S T hS hT => hS.mul_isUpperTriangular hT) p (extendFamily A)
    (fun i hi => by simpa [extendFamily_castSucc A ⟨i, hi⟩] using hA ⟨i, hi⟩) U₀ hU₀
    (by rwa [star_eq_conjTranspose])
  refine ⟨fun i => U i, fun i => hUu i, fun i => ?_, ?_⟩
  · have h := hT i i.2
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial, extendFamily_castSucc] at h
    simpa using h
  · rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial, extendFamily_last] at hlast
    simpa using hlast

/-- **The complex periodic Schur decomposition, nonsingular factors.** Let $\mathbb{K}$ be an
algebraically closed `RCLike` field (that is, $\mathbb{C}$), and let
$A_0, \dots, A_p \in \mathbb{K}^{n \times n}$, with $A_i$ nonsingular for every $i < p$. Then
there are unitary matrices $U_0, \dots, U_p$ such that $U_{i+1}^H A_i U_i$ is upper triangular
for every $i \le p$, where $U_{p+1} = U_0$.

This form is due to Bojanczyk, Golub and Van Dooren (1992); it is the complex analogue of
(7.8.6) of [golub2013matrix]. The proof takes a Schur form of the product $A_p \cdots A_0$
(`Matrix.exists_unitary_conj_upperTriangular`) and then successive QR factorizations. -/
theorem exists_unitary_periodicSchur_of_isUnit {𝕜 : Type*} [RCLike 𝕜] [IsAlgClosed 𝕜] {p : ℕ}
    (A : Fin (p + 1) → Matrix (Fin n) (Fin n) 𝕜) (hA : ∀ i : Fin p, IsUnit (A i.castSucc)) :
    ∃ U : Fin (p + 1) → Matrix (Fin n) (Fin n) 𝕜, (∀ i, U i ∈ unitaryGroup (Fin n) 𝕜) ∧
      ∀ i : Fin (p + 1), (star (U (i + 1)) * A i * U i).IsUpperTriangular := by
  obtain ⟨U₀, hU₀, hS, -⟩ := exists_unitary_conj_upperTriangular
    (extendFamily A p * prodDown (extendFamily A) p)
  obtain ⟨U, -, hUu, hT, hlast⟩ := exists_periodic_of_isUnit IsUpperTriangular
    (fun S T hS hT => hS.mul hT) p (extendFamily A)
    (fun i hi => by simpa [extendFamily_castSucc A ⟨i, hi⟩] using hA ⟨i, hi⟩) U₀ hU₀ hS
  refine ⟨fun i => U i, fun i => hUu i, fun i => ?_⟩
  induction i using Fin.lastCases with
  | last =>
    rw [extendFamily_last] at hlast
    simpa [Fin.last_add_one] using hlast
  | cast i =>
    have h := hT i i.2
    rw [extendFamily_castSucc] at h
    simpa [Fin.coeSucc_eq_succ] using h

/-! ### Limits of perturbed families -/

section Limits

variable {𝕜 : Type*} [RCLike 𝕜]

/-- For every family $A_0, \dots, A_p$ there are perturbed families $A^{(k)}$ that converge to it as
$k \to \infty$, with $A^{(k)}_i$ nonsingular for $i < p$ and $A^{(k)}_p = A_p$ for every $k$;
the perturbations are $A_i + t_k I$ with $t_k \to 0$. -/
private theorem exists_perturbed_family {p : ℕ} (A : Fin (p + 1) → Matrix (Fin n) (Fin n) 𝕜) :
    ∃ Ak : ℕ → Fin (p + 1) → Matrix (Fin n) (Fin n) 𝕜,
      (∀ k (i : Fin p), IsUnit (Ak k i.castSucc)) ∧ (∀ k, Ak k (Fin.last p) = A (Fin.last p)) ∧
      ∀ i, Tendsto (fun k => Ak k i) atTop (𝓝 (A i)) := by
  choose δ hδ hδu using fun i : Fin p => exists_forall_isUnit_det_add_smul_one (A i.castSucc)
  set δ₀ := (insert 1 (Finset.univ.image δ)).min' (Finset.insert_nonempty _ _) with hδ₀
  have hδ₀pos : 0 < δ₀ := by
    rw [hδ₀, Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact one_pos
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy; exact hδ i
  have hδ₀le : ∀ i, δ₀ ≤ δ i := fun i =>
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  set t : ℕ → ℝ := fun k => δ₀ / (k + 2) with ht
  have ht0 : ∀ k, 0 < t k := fun k => by positivity
  have htδ : ∀ k, t k < δ₀ := fun k => by
    rw [ht, div_lt_iff₀ (by positivity)]; nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have htlim : Tendsto t atTop (𝓝 0) := by
    have h := tendsto_const_nhds (x := δ₀).div_atTop
      (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (2 : ℝ))))
    simpa [ht] using h
  refine ⟨fun k i => if (i : ℕ) < p then A i + t k • (1 : Matrix (Fin n) (Fin n) 𝕜) else A i,
    fun k i => ?_, fun k => by simp, fun i => ?_⟩
  · simp only [Fin.val_castSucc, i.2, ite_true]
    rw [isUnit_iff_isUnit_det]
    exact hδu i (t k) (ht0 k) ((htδ k).trans_le (hδ₀le i))
  · by_cases hi : (i : ℕ) < p
    · simp only [hi, ite_true]
      have h := tendsto_const_nhds (x := A i).add (htlim.smul_const (1 : Matrix (Fin n) (Fin n) 𝕜))
      simpa using h
    · simp only [hi, ite_false]
      exact tendsto_const_nhds

end Limits

/-- **Hessenberg–triangular–triangular form** ([golub2013matrix], (7.8.5)). Let
$A_0, \dots, A_p \in \mathbb{R}^{n \times n}$ be arbitrary. Then there are orthogonal matrices
$U_0, \dots, U_p$ such that
* $U_{i+1}^T A_i U_i$ is upper triangular for every $i < p$;
* $U_0^T A_p U_p$ is upper Hessenberg.

The source describes the computation by QR factorizations and Givens bulge chasing, without a
proof of existence. The nonsingular case is
`Matrix.exists_orthogonal_periodicHessenberg_of_isUnit`. In general, $A_i + tI$ is nonsingular
for $i < p$ and small $t > 0$ (`Matrix.exists_forall_isUnit_det_add_smul_one`). A subsequence of
the orthogonal families for $t \to 0$ converges (`Matrix.isCompact_orthogonalGroup`), and the
triangular and Hessenberg shapes are closed conditions. -/
theorem exists_orthogonal_periodicHessenberg {p : ℕ}
    (A : Fin (p + 1) → Matrix (Fin n) (Fin n) ℝ) :
    ∃ U : Fin (p + 1) → Matrix (Fin n) (Fin n) ℝ, (∀ i, U i ∈ orthogonalGroup (Fin n) ℝ) ∧
      (∀ i : Fin p, ((U i.succ)ᵀ * A i.castSucc * U i.castSucc).IsUpperTriangular) ∧
      ((U 0)ᵀ * A (Fin.last p) * U (Fin.last p)).IsUpperHessenberg := by
  obtain ⟨Ak, hAku, -, hAkt⟩ := exists_perturbed_family A
  choose Uk hUk hTk hHk using fun k =>
    exists_orthogonal_periodicHessenberg_of_isUnit (Ak k) (hAku k)
  obtain ⟨U, hU, φ, hφ, hlim⟩ := exists_tendsto_subseq_of_mem_unitaryGroup (𝕜 := ℝ) hUk
  refine ⟨U, hU, fun i r c hrc => ?_, fun r c hrc => ?_⟩
  · have h := star_mul_mul_apply_eq_zero_of_tendsto (i := r) (j := c)
      (hlim i.succ) ((hAkt i.castSucc).comp hφ.tendsto_atTop)
      (hlim i.castSucc) fun k => by
        have := hTk (φ k) i hrc
        rwa [← conjTranspose_eq_transpose_of_trivial, ← star_eq_conjTranspose] at this
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h
  · have h := star_mul_mul_apply_eq_zero_of_tendsto (i := r) (j := c)
      (hlim 0) ((hAkt (Fin.last p)).comp hφ.tendsto_atTop)
      (hlim (Fin.last p)) fun k => by
        have := hHk (φ k) r c hrc
        rwa [← conjTranspose_eq_transpose_of_trivial, ← star_eq_conjTranspose] at this
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h

/-- **The complex periodic Schur decomposition.** Let $\mathbb{K}$ be an algebraically closed
`RCLike` field (that is, $\mathbb{C}$), and let $A_0, \dots, A_p \in \mathbb{K}^{n \times n}$ be
arbitrary. Then there are unitary matrices $U_0, \dots, U_p$ such that $U_{i+1}^H A_i U_i$ is
upper triangular for every $i \le p$, where $U_{p+1} = U_0$.

This form is due to Bojanczyk, Golub and Van Dooren (1992); it is the complex analogue of
(7.8.6) of [golub2013matrix]. It follows that $U_0^H (A_p \cdots A_0) U_0$ is upper triangular,
and its diagonal entries are the products of the diagonal entries of the transformed factors.
The nonsingular case is `Matrix.exists_unitary_periodicSchur_of_isUnit`. In general, $A_i + tI$
is nonsingular for $i < p$ and small $t > 0$, a subsequence of the unitary families for
$t \to 0$ converges (`Matrix.isCompact_unitaryGroup`), and triangularity of each factor is a
closed condition. -/
theorem exists_unitary_periodicSchur {𝕜 : Type*} [RCLike 𝕜] [IsAlgClosed 𝕜] {p : ℕ}
    (A : Fin (p + 1) → Matrix (Fin n) (Fin n) 𝕜) :
    ∃ U : Fin (p + 1) → Matrix (Fin n) (Fin n) 𝕜, (∀ i, U i ∈ unitaryGroup (Fin n) 𝕜) ∧
      ∀ i : Fin (p + 1), (star (U (i + 1)) * A i * U i).IsUpperTriangular := by
  obtain ⟨Ak, hAku, -, hAkt⟩ := exists_perturbed_family A
  choose Uk hUk hTk using fun k => exists_unitary_periodicSchur_of_isUnit (Ak k) (hAku k)
  obtain ⟨U, hU, φ, hφ, hlim⟩ := exists_tendsto_subseq_of_mem_unitaryGroup hUk
  refine ⟨U, hU, fun i => ?_⟩
  intro r c hrc
  exact star_mul_mul_apply_eq_zero_of_tendsto (i := r) (j := c)
    (hlim (i + 1)) ((hAkt i).comp hφ.tendsto_atTop)
    (hlim i) fun k => hTk (φ k) i hrc

/-- **Periodic real Schur form, nonsingular factors** ([golub2013matrix], (7.8.6)). Let
$A_0, \dots, A_p \in \mathbb{R}^{n \times n}$, with $A_i$ nonsingular for every $i < p$. Then
there are orthogonal matrices $U_0, \dots, U_p$ such that
* $U_{i+1}^T A_i U_i$ is upper triangular for every $i < p$;
* $U_0^T A_p U_p$ is upper quasi-triangular.

The proof starts from a real Schur form of the product $A_p \cdots A_0$
(`Matrix.exists_orthogonal_conj_isQuasiUpperTriangular`) and uses that quasi-triangularity is
preserved by right multiplication with an upper triangular matrix
(`Matrix.IsQuasiUpperTriangular.mul_isUpperTriangular`). -/
theorem exists_orthogonal_periodicRealSchur_of_isUnit {p : ℕ}
    (A : Fin (p + 1) → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i : Fin p, IsUnit (A i.castSucc)) :
    ∃ U : Fin (p + 1) → Matrix (Fin n) (Fin n) ℝ, (∀ i, U i ∈ orthogonalGroup (Fin n) ℝ) ∧
      (∀ i : Fin p, ((U i.succ)ᵀ * A i.castSucc * U i.castSucc).IsUpperTriangular) ∧
      ((U 0)ᵀ * A (Fin.last p) * U (Fin.last p)).IsQuasiUpperTriangular := by
  obtain ⟨U₀, hU₀, hH⟩ := exists_orthogonal_conj_isQuasiUpperTriangular
    (extendFamily A p * prodDown (extendFamily A) p)
  obtain ⟨U, -, hUu, hT, hlast⟩ := exists_periodic_of_isUnit (𝕜 := ℝ) IsQuasiUpperTriangular
    (fun S T hS hT => hS.mul_isUpperTriangular hT) p (extendFamily A)
    (fun i hi => by simpa [extendFamily_castSucc A ⟨i, hi⟩] using hA ⟨i, hi⟩) U₀ hU₀
    (by rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial])
  refine ⟨fun i => U i, fun i => hUu i, fun i => ?_, ?_⟩
  · have h := hT i i.2
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial, extendFamily_castSucc] at h
    simpa using h
  · rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial, extendFamily_last] at hlast
    simpa using hlast

/-- **The periodic real Schur form** ([golub2013matrix], (7.8.6)). Let
$A_0, \dots, A_p \in \mathbb{R}^{n \times n}$ be arbitrary. Then there are orthogonal matrices
$U_0, \dots, U_p$ such that
* $U_{i+1}^T A_i U_i$ is upper triangular for every $i < p$;
* $U_0^T A_p U_p$ is upper quasi-triangular.

The source states this form without proof. The factors $A_i + tI$ for $i < p$ are nonsingular
for small $t > 0$. Along a sequence $t_k \to 0$, infinitely many $k$ share each relation
$q_k(j) < q_k(i)$ of the block patterns $q_k$ of the last factor; this is a pigeonhole argument
over the finitely many relations on the indices. A further subsequence of the orthogonal
families converges (`Matrix.isCompact_orthogonalGroup`), and the vanishing entries pass to the
limit: triangular for $i < p$, and block triangular for the common pattern at $p$. -/
theorem exists_orthogonal_periodicRealSchur {p : ℕ}
    (A : Fin (p + 1) → Matrix (Fin n) (Fin n) ℝ) :
    ∃ U : Fin (p + 1) → Matrix (Fin n) (Fin n) ℝ, (∀ i, U i ∈ orthogonalGroup (Fin n) ℝ) ∧
      (∀ i : Fin p, ((U i.succ)ᵀ * A i.castSucc * U i.castSucc).IsUpperTriangular) ∧
      ((U 0)ᵀ * A (Fin.last p) * U (Fin.last p)).IsQuasiUpperTriangular := by
  classical
  obtain ⟨Ak, hAku, hAkl, hAkt⟩ := exists_perturbed_family A
  choose Uk hUk hTk hQk using fun k => exists_orthogonal_periodicRealSchur_of_isUnit (Ak k)
    (hAku k)
  choose q hmono hcard htri using hQk
  -- infinitely many `k` share the relation `q_k j < q_k i`
  obtain ⟨R, φ, hφmono, hφmem⟩ := Finite.exists_strictMono_forall_eq
    (fun k => fun i j : Fin n => decide (q k j < q k i))
  replace hφmem : ∀ k, (fun i j : Fin n => decide (q (φ k) j < q (φ k) i)) = R := hφmem
  have hrel : ∀ k i j, q (φ k) j < q (φ k) i ↔ q (φ 0) j < q (φ 0) i := by
    intro k i j
    have h1 := congrFun (congrFun (hφmem k) i) j
    have h2 := congrFun (congrFun (hφmem 0) i) j
    rw [← decide_eq_true_iff (p := q (φ k) j < q (φ k) i), ← decide_eq_true_iff
      (p := q (φ 0) j < q (φ 0) i), h1, h2]
  -- a convergent subsequence
  obtain ⟨U, hU, ψ, hψ, hlim⟩ := exists_tendsto_subseq_of_mem_unitaryGroup (𝕜 := ℝ)
    (U := fun k => Uk (φ k)) fun k i => hUk (φ k) i
  have hχ : Tendsto (fun k => φ (ψ k)) atTop atTop := (hφmono.comp hψ).tendsto_atTop
  refine ⟨U, hU, fun i => ?_, ⟨q (φ 0), hmono _, hcard _, ?_⟩⟩
  · intro r c hrc
    have h := star_mul_mul_apply_eq_zero_of_tendsto (i := r) (j := c)
      (hlim i.succ) ((hAkt i.castSucc).comp hχ)
      (hlim i.castSucc) fun k => by
        have := hTk (φ (ψ k)) i hrc
        rw [← conjTranspose_eq_transpose_of_trivial, ← star_eq_conjTranspose] at this
        exact this
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h
  · intro r c hrc
    have h := star_mul_mul_apply_eq_zero_of_tendsto (i := r) (j := c)
      (hlim 0) ((hAkt (Fin.last p)).comp hχ)
      (hlim (Fin.last p)) fun k => by
        have := htri (φ (ψ k)) ((hrel (ψ k) r c).2 hrc)
        rw [← conjTranspose_eq_transpose_of_trivial, ← star_eq_conjTranspose] at this
        exact this
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h

/-! ### The block-cyclic matrix -/

/-- The **block-cyclic matrix** of a family $A_0, \dots, A_p$ of square matrices indexed by $m$ is
the block matrix with $p + 1$ block rows and columns whose block $(i + 1, i)$ is $A_i$, with
indices modulo $p + 1$, so that block $(0, p)$ is $A_p$; all other blocks are zero
([golub2013matrix], §7.8.2). For $p = 2$ it is
$$\begin{bmatrix} 0 & 0 & A_2 \\ A_0 & 0 & 0 \\ 0 & A_1 & 0 \end{bmatrix}.$$

The rows and columns are indexed by `m × Fin (p + 1)`, with the block index as the second
coordinate, as in Mathlib's `Matrix.blockDiagonal`. The source numbers the factors from $1$. -/
def blockCyclic {R : Type*} [Zero R] {m : Type*} {p : ℕ} (A : Fin (p + 1) → Matrix m m R) :
    Matrix (m × Fin (p + 1)) (m × Fin (p + 1)) R :=
  of fun x y => if x.2 = y.2 + 1 then A y.2 x.1 y.1 else 0

/-- Let $A_0, \dots, A_p$ and $U_0, \dots, U_p$ be square matrices over a commutative ring, and let
$U = \operatorname{diag}(U_0, \dots, U_p)$ be the block diagonal matrix. Then $U^T$ times the
block-cyclic matrix of the $A_i$ times $U$ is the block-cyclic matrix of the transformed factors
$U_{i+1}^T A_i U_i$, with $U_{p+1} = U_0$.

This is the restatement of (7.8.5) in [golub2013matrix], §7.8.2, as the conjugation of the
block-cyclic matrix into a matrix $\tilde{H}$. -/
theorem blockDiagonal_conj_blockCyclic {R : Type*} [CommRing R] {m : Type*} [Fintype m]
    {p : ℕ} (A U : Fin (p + 1) → Matrix m m R) :
    (blockDiagonal U)ᵀ * blockCyclic A * blockDiagonal U =
      blockCyclic fun i => (U (i + 1))ᵀ * A i * U i := by
  classical
  ext ⟨r, b⟩ ⟨c, d⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, blockDiagonal_transpose, blockDiagonal_apply,
    blockCyclic, of_apply, transpose_apply]
  simp only [ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  split_ifs with h
  · subst h
    simp [Finset.sum_mul]
  · simp

/-- Let $A_0, \dots, A_p$ be square matrices of order $n$, with $A_i$ upper triangular for every
$i < p$ and $A_p$ upper Hessenberg. Then the block-cyclic matrix of the family is upper
Hessenberg in the interleaved order of the indices, in which the entry $j$ of block $b$ has the
position $(p + 1) j + b$ ([golub2013matrix], §7.8.2: "a highly structured upper Hessenberg
matrix").

The interleaved order is `finProdFinEquiv`; it is the perfect shuffle $\mathcal{P}$ of
[golub2013matrix], §1.2.11, applied to the block-major order. A nonzero entry $(i, j)$ of block
$(b + 1, b)$ has $i \le j$ and sits at row $(p + 1) i + b + 1$ and column $(p + 1) j + b$. A
nonzero entry $(i, j)$ of block $(0, p)$ has $i \le j + 1$ and sits at row $(p + 1) i$ and column
$(p + 1) j + p$. -/
theorem isUpperHessenberg_reindex_blockCyclic {R : Type*} [Zero R] {p : ℕ}
    {A : Fin (p + 1) → Matrix (Fin n) (Fin n) R}
    (hA : ∀ i : Fin p, (A i.castSucc).IsUpperTriangular)
    (hH : (A (Fin.last p)).IsUpperHessenberg) :
    ((blockCyclic A).submatrix finProdFinEquiv.symm finProdFinEquiv.symm).IsUpperHessenberg := by
  intro r s ⟨k, hsk, hkr⟩
  obtain ⟨⟨i, b⟩, rfl⟩ := finProdFinEquiv.surjective r
  obtain ⟨⟨j, c⟩, rfl⟩ := finProdFinEquiv.surjective s
  have hlt : (c : ℕ) + (p + 1) * j + 1 < b + (p + 1) * i := by
    have h1 := Fin.lt_def.1 hsk
    have h2 := Fin.lt_def.1 hkr
    simp only [finProdFinEquiv_apply_val] at h1 h2
    omega
  simp only [submatrix_apply, Equiv.symm_apply_apply, blockCyclic, of_apply]
  split_ifs with hbc
  · induction c using Fin.lastCases with
    | last =>
      have hb : b = 0 := by rw [hbc, Fin.last_add_one]
      subst hb
      simp only [Fin.val_zero, Fin.val_last] at hlt
      refine hH i j ⟨⟨j + 1, by
        have : (j : ℕ) + 1 < i := by nlinarith
        omega⟩, ?_, ?_⟩
      · rw [Fin.lt_def]; simp
      · rw [Fin.lt_def]; simp only
        nlinarith
    | cast c =>
      have hb : (b : ℕ) = c + 1 := by rw [hbc, Fin.coeSucc_eq_succ, Fin.val_succ]
      rw [hb, Fin.val_castSucc] at hlt
      refine hA c (?_ : j < i)
      rw [Fin.lt_def]
      nlinarith
  · rfl

end Matrix

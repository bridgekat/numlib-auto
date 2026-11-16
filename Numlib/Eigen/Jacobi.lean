/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate for its first section: `Matrix.offDiagNormSq` is general matrix material
with no numerical-analysis-specific content, like the plane rotations of
`Numlib/LinearAlgebra/Matrix/PlaneRotation` that it is used with.
-/
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.Trace
import Numlib.LinearAlgebra.Matrix.PlaneRotation

/-!
# Jacobi's eigenvalue algorithm

Jacobi's method drives a real symmetric matrix $A = (a_{ij})$ of order $n$ towards a diagonal matrix
by a sequence of plane rotations (`Matrix.planeRotation` of
`Numlib.LinearAlgebra.Matrix.PlaneRotation`). Each rotation is chosen so that the similarity it
induces annihilates one off-diagonal entry. The quantity that decreases is the **off-diagonal mass**
$$N(A)^2 = \sum_{i \neq j} a_{ij}^2,$$
the notation of [kress1998numerical]. The classical analysis rests on two facts. First, if $U$ is
the rotation that annihilates $a_{jk}$, then $N(U^T A U)^2 = N(A)^2 - 2 a_{jk}^2$
([kress1998numerical], Lemma 7.13). Second, an off-diagonal entry of largest modulus carries at
least the fraction $1/(n^2 - n)$ of the mass. So the classical method, which annihilates an entry of
largest modulus at each step, reduces the mass by the factor $1 - 2/(n^2 - n)$ per step.

This module proves these facts and the convergence of the classical method ([kress1998numerical],
Theorem 7.14). It also proves that the sequence of matrices converges to a diagonal matrix with the
eigenvalues of $A$, and it relates the rotation to the parametrization of [quarteroni2000numerical].

## Main definitions

* `Matrix.offDiagNormSq`: the off-diagonal mass $N(A)^2$.
* `Matrix.jacobiRotation`: the plane rotation in the $(j, k)$-plane that annihilates $a_{jk}$.
* `Matrix.jacobiStep`: the similarity $U^T A U$ by this rotation.
* `Matrix.classicalJacobiIterate`: the classical Jacobi method, which annihilates an off-diagonal
  entry of largest modulus at each step.

## Main results

* `Matrix.offDiagNormSq_jacobiStep`: a Jacobi step gives $N(U^T A U)^2 = N(A)^2 - 2 a_{jk}^2$.
* `Matrix.offDiagNormSq_classicalJacobiIterate_le`: the iterates satisfy
  $N(A_\nu)^2 \le (1 - 2/(n^2 - n))^\nu N(A)^2$.
* `Matrix.tendsto_offDiagNormSq_classicalJacobiIterate`: the off-diagonal mass of the iterates tends
  to $0$.
* `Matrix.charpoly_classicalJacobiIterate`: every iterate has the characteristic polynomial of $A$.
* `Matrix.tendsto_classicalJacobiIterate`: the iterates converge to a diagonal matrix with the
  characteristic polynomial of $A$.

## Implementation notes

* The method is stated for real symmetric matrices, which plane rotations with a real angle can
  diagonalize. For a complex Hermitian matrix, a rotation with one real parameter cannot annihilate
  a complex entry $a_{jk}$; a phase is also necessary.
* The rotation is parametrized by the tangent $t$ of its angle, not by the angle. With
  $\theta = (a_{kk} - a_{jj}) / (2 a_{jk})$, the tangent `Matrix.jacobiTan` is the root of
  $t^2 - 2 \theta t - 1 = 0$ of smaller modulus, so $|t| \le 1$. Then the annihilation identity is a
  polynomial identity in the cosine $c$ and the sine $s$, and no trigonometry is necessary.
* The choice of the root of smaller modulus is necessary for the convergence of the matrix sequence,
  not only for numerical stability; see `Matrix.jacobiTan`.
* The rotation `Matrix.planeRotation j k c s` has the entries $c$ at $(j, j)$ and $(k, k)$, $-s$ at
  $(j, k)$ and $s$ at $(k, j)$.
-/

open Finset

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The off-diagonal mass -/

section OffDiag

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The **off-diagonal mass** of a square matrix $A$ over $\mathbb{R}$ or $\mathbb{C}$ is
$$N(A)^2 = \sum_{i \neq j} |a_{ij}|^2.$$

The notation $N(A)^2$ is that of [kress1998numerical]. A plane rotation that annihilates
$a_{jk}$ decreases this quantity by exactly $2 |a_{jk}|^2$ (`Matrix.offDiagNormSq_jacobiStep`). -/
noncomputable def offDiagNormSq (A : Matrix n n 𝕜) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ ^ 2

/-- The off-diagonal mass is nonnegative: $N(A)^2 \ge 0$. -/
theorem offDiagNormSq_nonneg (A : Matrix n n 𝕜) : 0 ≤ offDiagNormSq A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The off-diagonal mass and the diagonal mass add up to the squared Frobenius norm:
$$N(A)^2 + \sum_i |a_{ii}|^2 = \sum_{i, j} |a_{ij}|^2.$$

This is Lemma 7.8 of [kress1998numerical]. -/
theorem offDiagNormSq_add_sum_diag_sq (A : Matrix n n 𝕜) :
    offDiagNormSq A + ∑ i, ‖A i i‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  rw [offDiagNormSq, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_erase_add _ _ (Finset.mem_univ i)

/-- The off-diagonal mass vanishes if and only if the matrix is diagonal: $N(A)^2 = 0$ if and only
if $a_{ij} = 0$ for all $i \neq j$. -/
theorem offDiagNormSq_eq_zero_iff {A : Matrix n n 𝕜} :
    offDiagNormSq A = 0 ↔ ∀ i j, i ≠ j → A i j = 0 := by
  rw [offDiagNormSq, Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  constructor
  · intro h i j hij
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 (h i (Finset.mem_univ i))
      j (Finset.mem_erase.2 ⟨hij.symm, Finset.mem_univ j⟩)
    simpa using h1
  · intro h i _
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [h i j (Finset.mem_erase.1 hj).1.symm]
    simp

end OffDiag

/-! ### The Frobenius mass and orthogonal similarity -/

section Frobenius

omit [DecidableEq n] in
/-- For a real square matrix $A$, the trace of $A^T A$ is the squared Frobenius norm:
$\operatorname{tr}(A^T A) = \sum_{i, q} a_{iq}^2$. -/
theorem trace_transpose_mul_self (A : Matrix n n ℝ) :
    (Aᵀ * A).trace = ∑ i, ∑ q, (A i q) ^ 2 := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, sq]
  exact Finset.sum_comm

/-- For a real matrix, the off-diagonal mass is the sum of the squares of the off-diagonal entries:
$N(A)^2 = \sum_{i \neq q} a_{iq}^2$. -/
theorem offDiagNormSq_real (A : Matrix n n ℝ) :
    offDiagNormSq A = ∑ i, ∑ q ∈ Finset.univ.erase i, (A i q) ^ 2 := by
  simp [offDiagNormSq, Real.norm_eq_abs, sq_abs]

/-- For a real square matrix $A$, the off-diagonal mass and the diagonal mass add up to the squared
Frobenius norm:
$$N(A)^2 + \sum_i a_{ii}^2 = \sum_{i, q} a_{iq}^2.$$

This is the real form of `Matrix.offDiagNormSq_add_sum_diag_sq`. -/
theorem offDiagNormSq_add_sum_diag_sq_real (A : Matrix n n ℝ) :
    offDiagNormSq A + ∑ i, (A i i) ^ 2 = ∑ i, ∑ q, (A i q) ^ 2 := by
  simpa [Real.norm_eq_abs, sq_abs] using offDiagNormSq_add_sum_diag_sq A

/-- The squared Frobenius norm is invariant under orthogonal similarity. Let $A$ and $U$ be real
square matrices with $U^T U = I$. Then
$$\sum_{i, q} \bigl( (U^T A U)_{iq} \bigr)^2 = \sum_{i, q} a_{iq}^2.$$
-/
theorem sum_sq_conj_eq (A U : Matrix n n ℝ) (hU : Uᵀ * U = 1) :
    ∑ i, ∑ q, ((Uᵀ * A * U) i q) ^ 2 = ∑ i, ∑ q, (A i q) ^ 2 := by
  have hU' : U * Uᵀ = 1 := _root_.mul_eq_one_comm.1 hU
  have key : (Uᵀ * A * U)ᵀ * (Uᵀ * A * U) = Uᵀ * (Aᵀ * A) * U := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    calc Uᵀ * (Aᵀ * U) * (Uᵀ * A * U)
        = Uᵀ * Aᵀ * (U * Uᵀ) * A * U := by noncomm_ring
      _ = Uᵀ * (Aᵀ * A) * U := by rw [hU']; noncomm_ring
  rw [← trace_transpose_mul_self, ← trace_transpose_mul_self, key, Matrix.trace_mul_cycle,
    ← Matrix.mul_assoc, hU', Matrix.one_mul]

/-- The off-diagonal mass of a real $2 \times 2$ block matrix is the off-diagonal mass of the two
diagonal blocks plus the squared Frobenius norm of the two off-diagonal blocks:
$$N\begin{pmatrix} P & Q \\ R & S \end{pmatrix}^2 = N(P)^2 + N(S)^2 + \sum_{i, j} q_{ij}^2 +
  \sum_{i, j} r_{ij}^2.$$
-/
theorem offDiagNormSq_fromBlocks {κ₁ κ₂ : Type*} [Fintype κ₁] [DecidableEq κ₁]
    [Fintype κ₂] [DecidableEq κ₂] (P : Matrix κ₁ κ₁ ℝ) (Q : Matrix κ₁ κ₂ ℝ) (R : Matrix κ₂ κ₁ ℝ)
    (S : Matrix κ₂ κ₂ ℝ) :
    offDiagNormSq (fromBlocks P Q R S) = offDiagNormSq P + offDiagNormSq S +
      ∑ i, ∑ j, Q i j ^ 2 + ∑ i, ∑ j, R i j ^ 2 := by
  have h := offDiagNormSq_add_sum_diag_sq_real (fromBlocks P Q R S)
  have hP := offDiagNormSq_add_sum_diag_sq_real P
  have hS := offDiagNormSq_add_sum_diag_sq_real S
  simp only [Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
    fromBlocks_apply₂₂, Finset.sum_add_distrib] at h
  linarith

/-- **The off-diagonal mass after a rotation on a set of coordinates.** Let $A$ be a real square
matrix indexed by a finite type $\iota$, let $e : \kappa \to \iota$ be injective, and let $W$ be
a real matrix indexed by $\kappa$ with $W^T W = I$. Let $V$ be the matrix that equals $W$ on the
coordinates $e(\kappa)$ and the identity elsewhere: $V_{e(a), e(b)} = W_{ab}$ for all $a, b$,
and $V_{ij} = \delta_{ij}$ whenever $i$ or $j$ is not in the range of $e$. Let $A_e$ be the
principal submatrix of $A$ on the coordinates $e(\kappa)$. Then
$$N(V^T A V)^2 = N(A)^2 - N(A_e)^2 + N(W^T A_e W)^2.$$

This is the identity behind the block Jacobi method of [golub2013matrix] §8.5.6; the block
Jacobi step is the case where $W$ diagonalizes $A_e$. The principal submatrix $A_e$ is
`A.submatrix e e`. -/
theorem offDiagNormSq_conj_block {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (A : Matrix ι ι ℝ) {e : κ → ι} (he : Function.Injective e)
    {W : Matrix κ κ ℝ} (hW : Wᵀ * W = 1) {V : Matrix ι ι ℝ} (hV : ∀ a b, V (e a) (e b) = W a b)
    (hV' : ∀ i j, (i ∉ Set.range e ∨ j ∉ Set.range e) → V i j = (1 : Matrix ι ι ℝ) i j) :
    offDiagNormSq (Vᵀ * A * V) = offDiagNormSq A - offDiagNormSq (A.submatrix e e) +
      offDiagNormSq (Wᵀ * A.submatrix e e * W) := by
  classical
  let σ : κ ⊕ {i // i ∉ Set.range e} ≃ ι :=
    (Equiv.sumCongr (Equiv.ofInjective e he) (Equiv.refl _)).trans
      (Equiv.sumCompl (· ∈ Set.range e))
  have hσl : ∀ a, σ (Sum.inl a) = e a := fun a => rfl
  have hσr : ∀ b, σ (Sum.inr b) = b.1 := fun b => rfl
  -- reindexing preserves the off-diagonal mass
  have hre : ∀ M : Matrix ι ι ℝ, offDiagNormSq (M.submatrix σ σ) = offDiagNormSq M := fun M => by
    have h1 := offDiagNormSq_add_sum_diag_sq_real (M.submatrix σ σ)
    have h2 := offDiagNormSq_add_sum_diag_sq_real M
    have e1 : ∑ i, (M.submatrix σ σ i i) ^ 2 = ∑ i, M i i ^ 2 :=
      Equiv.sum_comp σ (fun i => M i i ^ 2)
    have e2 : ∑ i, ∑ j, (M.submatrix σ σ i j) ^ 2 = ∑ i, ∑ j, M i j ^ 2 := by
      rw [← Equiv.sum_comp σ (fun i => ∑ j, M i j ^ 2)]
      exact Finset.sum_congr rfl fun i _ => Equiv.sum_comp σ (fun j => M (σ i) j ^ 2)
    linarith
  -- in the reindexed coordinates `V` is `diag(W, I)`
  have hVs : V.submatrix σ σ = fromBlocks W 0 0 1 := by
    ext i j
    rcases i with a | b <;> rcases j with a' | b'
    · exact hV a a'
    · rw [submatrix_apply, hσl, hσr, hV' _ _ (Or.inr b'.2), fromBlocks_apply₁₂, Matrix.zero_apply,
        one_apply_ne]
      intro h
      exact b'.2 ⟨a, h⟩
    · rw [submatrix_apply, hσl, hσr, hV' _ _ (Or.inl b.2), fromBlocks_apply₂₁, Matrix.zero_apply,
        one_apply_ne]
      intro h
      exact b.2 ⟨a', h.symm⟩
    · rw [submatrix_apply, hσr, hσr, hV' _ _ (Or.inl b.2), fromBlocks_apply₂₂]
      by_cases h : b = b'
      · subst h
        simp
      · rw [one_apply_ne (fun h' => h (Subtype.ext h')), one_apply_ne h]
  set U : Matrix (κ ⊕ {i // i ∉ Set.range e}) (κ ⊕ {i // i ∉ Set.range e}) ℝ :=
    fromBlocks W 0 0 1 with hUdef
  have hU : Uᵀ * U = 1 := by
    rw [hUdef, fromBlocks_transpose, fromBlocks_multiply]
    simp [hW, fromBlocks_one]
  have hBs : (Vᵀ * A * V).submatrix σ σ = Uᵀ * A.submatrix σ σ * U := by
    rw [← submatrix_mul_equiv _ _ _ σ _, ← submatrix_mul_equiv _ _ _ σ _, ← transpose_submatrix,
      hVs]
  have hblk : Uᵀ * A.submatrix σ σ * U =
      fromBlocks (Wᵀ * (A.submatrix σ σ).toBlocks₁₁ * W) (Wᵀ * (A.submatrix σ σ).toBlocks₁₂)
        ((A.submatrix σ σ).toBlocks₂₁ * W) (A.submatrix σ σ).toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks (A.submatrix σ σ)]
    simp only [hUdef, fromBlocks_transpose, fromBlocks_multiply, transpose_zero, transpose_one,
      Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.one_mul, Matrix.mul_one]
  have e1 := hre (Vᵀ * A * V)
  rw [hBs] at e1
  have e2 := hre A
  have hT1 := offDiagNormSq_add_sum_diag_sq_real (Uᵀ * A.submatrix σ σ * U)
  have hT2 := offDiagNormSq_add_sum_diag_sq_real (A.submatrix σ σ)
  have hT3 := sum_sq_conj_eq (A.submatrix σ σ) U hU
  have hd1 : ∑ i, (Uᵀ * A.submatrix σ σ * U) i i ^ 2 =
      ∑ a, (Wᵀ * A.submatrix e e * W) a a ^ 2 + ∑ b, (A.submatrix σ σ).toBlocks₂₂ b b ^ 2 := by
    rw [hblk, Fintype.sum_sum_type]
    rfl
  have hd2 : ∑ i, (A.submatrix σ σ) i i ^ 2 =
      ∑ a, (A.submatrix e e) a a ^ 2 + ∑ b, (A.submatrix σ σ).toBlocks₂₂ b b ^ 2 := by
    rw [Fintype.sum_sum_type]
    rfl
  have hW1 := offDiagNormSq_add_sum_diag_sq_real (Wᵀ * A.submatrix e e * W)
  have hW2 := offDiagNormSq_add_sum_diag_sq_real (A.submatrix e e)
  have hW3 := sum_sq_conj_eq (A.submatrix e e) W hW
  linarith

end Frobenius

/-! ### The Jacobi rotation -/

section Jacobi

variable (A : Matrix n n ℝ) (j k : n)

/-- The **Jacobi tangent**: the tangent of the angle of the Jacobi rotation of a real matrix $A$ in
the $(j, k)$-plane. If $a_{jk} = 0$, it is $0$, so that the rotation is the identity. Otherwise
let $\theta = (a_{kk} - a_{jj}) / (2 a_{jk})$; the Jacobi tangent is the root of smaller modulus
of $t^2 - 2 \theta t - 1 = 0$, namely
$$t = \theta - \sqrt{\theta^2 + 1} \ \text{ if } \theta \ge 0, \qquad t = \theta +
  \sqrt{\theta^2 + 1} \ \text{ if } \theta < 0.$$

The two roots of the quadratic have product $-1$, so exactly one of them has $|t| \le 1$. This
is the root that Lemma 7.13 of [kress1998numerical] prescribes: for it,
$\cos 2\varphi = 1 / \sqrt{1 + \tan^2 2\varphi}$ is positive, which means $|\varphi| \le \pi/4$.
The choice is not a matter of numerical stability only. With the other root, the angle of
rotation lies in $(0, \pi/2)$. A step at a pair with $a_{kk} > a_{jj}$ and small $|a_{jk}|$ is
then close to an interchange of the two coordinates, so $A_{\nu+1} - A_\nu$ does not tend to
$0$, and the iterates need not converge. The bound $|t| \le 1$ (`Matrix.abs_jacobiTan_le_one`)
is what `Matrix.abs_jacobiStep_sub_le` uses. -/
noncomputable def jacobiTan : ℝ :=
  if A j k = 0 then 0
  else if 0 ≤ (A k k - A j j) / (2 * A j k) then
    (A k k - A j j) / (2 * A j k) - Real.sqrt (((A k k - A j j) / (2 * A j k)) ^ 2 + 1)
  else (A k k - A j j) / (2 * A j k) + Real.sqrt (((A k k - A j j) / (2 * A j k)) ^ 2 + 1)

/-- The **Jacobi cosine** $c = 1 / \sqrt{1 + t^2}$, where $t$ is the Jacobi tangent
`Matrix.jacobiTan`. -/
noncomputable def jacobiCos : ℝ := 1 / Real.sqrt (1 + jacobiTan A j k ^ 2)

/-- The **Jacobi sine** $s = t c$, where $t$ is the Jacobi tangent and $c$ the Jacobi cosine. -/
noncomputable def jacobiSin : ℝ := jacobiTan A j k * jacobiCos A j k

/-- The **Jacobi rotation** of a real matrix $A$ in the $(j, k)$-plane: the plane rotation
`Matrix.planeRotation j k c s` with the Jacobi cosine $c$ and the Jacobi sine $s$. For a
symmetric $A$ and $j \neq k$, the similarity that it induces annihilates the entry $a_{jk}$
(`Matrix.jacobiStep_apply_eq_zero`).

This is the rotation of [kress1998numerical], Lemma 7.13. -/
noncomputable def jacobiRotation : Matrix n n ℝ :=
  planeRotation j k (jacobiCos A j k) (jacobiSin A j k)

/-- A **Jacobi step**: the orthogonal similarity $U^T A U$ of a real matrix $A$ by its Jacobi
rotation $U$ in the $(j, k)$-plane. -/
noncomputable def jacobiStep : Matrix n n ℝ :=
  (jacobiRotation A j k)ᵀ * A * jacobiRotation A j k

omit [Fintype n] [DecidableEq n] in
/-- The Jacobi cosine $c$ and the Jacobi sine $s$ satisfy $c^2 + s^2 = 1$. -/
theorem jacobiCos_sq_add_jacobiSin_sq : jacobiCos A j k ^ 2 + jacobiSin A j k ^ 2 = 1 := by
  have hpos : (0 : ℝ) < 1 + jacobiTan A j k ^ 2 := by positivity
  have hsq : Real.sqrt (1 + jacobiTan A j k ^ 2) ^ 2 = 1 + jacobiTan A j k ^ 2 :=
    Real.sq_sqrt hpos.le
  have hne : Real.sqrt (1 + jacobiTan A j k ^ 2) ≠ 0 := by positivity
  rw [jacobiSin, jacobiCos]
  field_simp
  linarith [hsq]

omit [Fintype n] [DecidableEq n] in
/-- If $a_{jk} \neq 0$, the Jacobi tangent $t$ satisfies $t^2 = 2 \theta t + 1$, where
$\theta = (a_{kk} - a_{jj}) / (2 a_{jk})$. -/
theorem jacobiTan_sq (h : A j k ≠ 0) :
    jacobiTan A j k ^ 2
      = 2 * ((A k k - A j j) / (2 * A j k)) * jacobiTan A j k + 1 := by
  have hnn : (0 : ℝ) ≤ ((A k k - A j j) / (2 * A j k)) ^ 2 + 1 := by positivity
  have hsq := Real.sq_sqrt hnn
  simp only [jacobiTan, h, ite_false]
  split_ifs <;> nlinarith [hsq]

omit [Fintype n] [DecidableEq n] in
/-- **The Jacobi angle is at most $\pi/4$.** The Jacobi tangent $t$ satisfies $|t| \le 1$.

This bound keeps a Jacobi step close to the identity when the annihilated entry is small. So it
is what makes the classical method converge as a sequence of matrices, and not only in
off-diagonal mass (`Matrix.tendsto_classicalJacobiIterate`). -/
theorem abs_jacobiTan_le_one : |jacobiTan A j k| ≤ 1 := by
  rw [jacobiTan]
  split_ifs with h hθ
  · simp
  · set θ := (A k k - A j j) / (2 * A j k) with hθdef
    have hnn : (0 : ℝ) ≤ θ ^ 2 + 1 := by positivity
    have hsq := Real.sq_sqrt hnn
    have hle : θ ≤ Real.sqrt (θ ^ 2 + 1) := by
      nlinarith [Real.sqrt_nonneg (θ ^ 2 + 1), hsq]
    have hge : Real.sqrt (θ ^ 2 + 1) ≤ θ + 1 := by
      nlinarith [Real.sqrt_nonneg (θ ^ 2 + 1), hsq, hθ]
    rw [abs_le]
    constructor <;> linarith
  · set θ := (A k k - A j j) / (2 * A j k) with hθdef
    have hnn : (0 : ℝ) ≤ θ ^ 2 + 1 := by positivity
    have hsq := Real.sq_sqrt hnn
    have hle : -θ ≤ Real.sqrt (θ ^ 2 + 1) := by
      nlinarith [Real.sqrt_nonneg (θ ^ 2 + 1), hsq]
    have hge : Real.sqrt (θ ^ 2 + 1) ≤ 1 - θ := by
      nlinarith [Real.sqrt_nonneg (θ ^ 2 + 1), hsq]
    rw [abs_le]
    constructor <;> linarith

omit [Fintype n] [DecidableEq n] in
/-- The Jacobi tangent $t$ satisfies $(1 - t^2) a_{jk} + t (a_{kk} - a_{jj}) = 0$. -/
theorem jacobiTan_annihilate :
    (1 - jacobiTan A j k ^ 2) * A j k + jacobiTan A j k * (A k k - A j j) = 0 := by
  by_cases h : A j k = 0
  · simp [jacobiTan, h]
  · have ht := jacobiTan_sq A j k h
    have hθ : A k k - A j j = 2 * ((A k k - A j j) / (2 * A j k)) * A j k := by
      field_simp
    rw [hθ]
    linear_combination (-(A j k)) * ht

omit [Fintype n] [DecidableEq n] in
/-- The Jacobi cosine $c$ and sine $s$ satisfy
$$(c^2 - s^2) a_{jk} + c s (a_{kk} - a_{jj}) = 0.$$

This is the equation which says that the $(j, k)$ entry of the Jacobi step vanishes. -/
theorem jacobi_annihilate :
    (jacobiCos A j k ^ 2 - jacobiSin A j k ^ 2) * A j k
      + jacobiCos A j k * jacobiSin A j k * (A k k - A j j) = 0 := by
  have h := jacobiTan_annihilate A j k
  rw [jacobiSin]
  linear_combination (jacobiCos A j k ^ 2) * h

/-!
### The parametrization of the angle in Quarteroni, Sacco and Saleri

Equations (5.61)–(5.62) of [quarteroni2000numerical], and Algorithm 8.4.1 of the 1989 edition of
Golub and Van Loan, parametrize the rotation by the root of $t^2 + 2 \eta t - 1 = 0$ of modulus at
most one, where $\eta = (a_{kk} - a_{jj}) / (2 a_{jk})$. Their rotation matrix has $+s$ where
`Matrix.planeRotation` has $-s$, and the two sign conventions cancel. Their tangent is the negative
of `Matrix.jacobiTan`, their pair $(c, s)$ is $(c, -s)$ for the Jacobi cosine and sine of this
module, and the rotation matrix that they build is `Matrix.jacobiRotation`. The two tangents are not
the two roots of one quadratic: they are roots of the two quadratics $t^2 \mp 2 \eta t - 1 = 0$,
both have modulus at most one, and each is the negative of the other.
-/

omit [Fintype n] [DecidableEq n] in
/-- The tangent of [quarteroni2000numerical], (5.61)–(5.62). If $a_{jk} = 0$, it is $0$. Otherwise
let $\eta = (a_{kk} - a_{jj}) / (2 a_{jk})$; the tangent is the root of modulus at most one of
$t^2 + 2 \eta t - 1 = 0$, namely
$$t = \frac{1}{\eta + \sqrt{1 + \eta^2}} \ \text{ if } \eta \ge 0, \qquad t = \frac{-1}{-\eta +
  \sqrt{1 + \eta^2}} \ \text{ if } \eta < 0.$$

It is the negative of `Matrix.jacobiTan` (`Matrix.jacobiTanSmall_eq_neg_jacobiTan`). The sign is
compensated by the sign convention of the source for the rotation matrix. -/
noncomputable def jacobiTanSmall : ℝ :=
  if A j k = 0 then 0
  else if 0 ≤ (A k k - A j j) / (2 * A j k) then
    1 / ((A k k - A j j) / (2 * A j k) + Real.sqrt (1 + ((A k k - A j j) / (2 * A j k)) ^ 2))
  else -1 / (-((A k k - A j j) / (2 * A j k)) + Real.sqrt (1 + ((A k k - A j j) / (2 * A j k)) ^ 2))

omit [Fintype n] [DecidableEq n] in
/-- The tangent of [quarteroni2000numerical] is the negative of the Jacobi tangent:
`Matrix.jacobiTanSmall A j k = -Matrix.jacobiTan A j k`.

The key identity is $1 / (\eta + \sqrt{1 + \eta^2}) = \sqrt{1 + \eta^2} - \eta$. -/
theorem jacobiTanSmall_eq_neg_jacobiTan : jacobiTanSmall A j k = -jacobiTan A j k := by
  rw [jacobiTanSmall, jacobiTan]
  split_ifs with h hθ
  · simp
  · set η := (A k k - A j j) / (2 * A j k) with hη
    have hnn : (0 : ℝ) ≤ 1 + η ^ 2 := by positivity
    have hsq := Real.sq_sqrt hnn
    have hs := Real.sqrt_nonneg (1 + η ^ 2)
    have hsq' : Real.sqrt (η ^ 2 + 1) = Real.sqrt (1 + η ^ 2) := by rw [add_comm]
    have hd : η + Real.sqrt (1 + η ^ 2) ≠ 0 := by
      have : 0 < η + Real.sqrt (1 + η ^ 2) := by nlinarith
      exact this.ne'
    rw [hsq', div_eq_iff hd]
    nlinarith [hsq]
  · set η := (A k k - A j j) / (2 * A j k) with hη
    have hnn : (0 : ℝ) ≤ 1 + η ^ 2 := by positivity
    have hsq := Real.sq_sqrt hnn
    have hs := Real.sqrt_nonneg (1 + η ^ 2)
    have hsq' : Real.sqrt (η ^ 2 + 1) = Real.sqrt (1 + η ^ 2) := by rw [add_comm]
    have hd : -η + Real.sqrt (1 + η ^ 2) ≠ 0 := by
      have : 0 < -η + Real.sqrt (1 + η ^ 2) := by nlinarith
      exact this.ne'
    rw [hsq', div_eq_iff hd]
    nlinarith [hsq]

omit [Fintype n] [DecidableEq n] in
/-- If $a_{jk} \neq 0$, the tangent $t$ of [quarteroni2000numerical] is a root of
$t^2 + 2 \eta t - 1 = 0$, where $\eta = (a_{kk} - a_{jj}) / (2 a_{jk})$. -/
theorem jacobiTanSmall_sq (h : A j k ≠ 0) :
    jacobiTanSmall A j k ^ 2 + 2 * ((A k k - A j j) / (2 * A j k)) * jacobiTanSmall A j k - 1
      = 0 := by
  rw [jacobiTanSmall_eq_neg_jacobiTan]
  linear_combination jacobiTan_sq A j k h

omit [Fintype n] [DecidableEq n] in
/-- The tangent $t$ of [quarteroni2000numerical] satisfies $|t| \le 1$. -/
theorem abs_jacobiTanSmall_le_one : |jacobiTanSmall A j k| ≤ 1 := by
  rw [jacobiTanSmall_eq_neg_jacobiTan, abs_neg]
  exact abs_jacobiTan_le_one A j k

/-- The cosine $c = 1 / \sqrt{1 + t^2}$ of the angle of [quarteroni2000numerical], where $t$ is the
tangent `Matrix.jacobiTanSmall`. -/
noncomputable def jacobiCosSmall : ℝ := 1 / Real.sqrt (1 + jacobiTanSmall A j k ^ 2)

/-- The sine $s = t c$ of the angle of [quarteroni2000numerical], where $t$ is the tangent
`Matrix.jacobiTanSmall` and $c$ the cosine `Matrix.jacobiCosSmall`. -/
noncomputable def jacobiSinSmall : ℝ := jacobiTanSmall A j k * jacobiCosSmall A j k

omit [Fintype n] [DecidableEq n] in
/-- The cosine of [quarteroni2000numerical] equals the Jacobi cosine: `Matrix.jacobiCosSmall A j k =
Matrix.jacobiCos A j k`. -/
theorem jacobiCosSmall_eq : jacobiCosSmall A j k = jacobiCos A j k := by
  rw [jacobiCosSmall, jacobiCos, jacobiTanSmall_eq_neg_jacobiTan, neg_sq]

omit [Fintype n] [DecidableEq n] in
/-- The sine of [quarteroni2000numerical] is the negative of the Jacobi sine: `Matrix.jacobiSinSmall
A j k = -Matrix.jacobiSin A j k`. -/
theorem jacobiSinSmall_eq_neg : jacobiSinSmall A j k = -jacobiSin A j k := by
  rw [jacobiSinSmall, jacobiSin, jacobiTanSmall_eq_neg_jacobiTan, jacobiCosSmall_eq, neg_mul]

omit [Fintype n] [DecidableEq n] in
/-- The cosine $c$ and the sine $s$ of [quarteroni2000numerical] satisfy $c^2 + s^2 = 1$. -/
theorem jacobiCosSmall_sq_add_jacobiSinSmall_sq :
    jacobiCosSmall A j k ^ 2 + jacobiSinSmall A j k ^ 2 = 1 := by
  rw [jacobiCosSmall_eq, jacobiSinSmall_eq_neg, neg_sq]
  exact jacobiCos_sq_add_jacobiSin_sq A j k

omit [Fintype n] [DecidableEq n] in
/-- The angle of [quarteroni2000numerical] annihilates the off-diagonal entry, in the sign
convention of the source for the rotation matrix: its cosine $c$ and sine $s$ satisfy
$$(c^2 - s^2) a_{jk} - c s (a_{kk} - a_{jj}) = 0.$$

This is equation (5.60) of [quarteroni2000numerical]. It is `Matrix.jacobi_annihilate` with $s$
replaced by $-s$. -/
theorem jacobiSmall_annihilate :
    (jacobiCosSmall A j k ^ 2 - jacobiSinSmall A j k ^ 2) * A j k
      - jacobiCosSmall A j k * jacobiSinSmall A j k * (A k k - A j j) = 0 := by
  rw [jacobiCosSmall_eq, jacobiSinSmall_eq_neg, neg_sq]
  linear_combination jacobi_annihilate A j k

omit [Fintype n] in
/-- Let $c$ and $s$ be the cosine and the sine of [quarteroni2000numerical]. The rotation matrix
that the source builds from them has $+s$ at position $(j, k)$; in the convention of this module
it is `Matrix.planeRotation j k c (-s)`. This matrix equals the Jacobi rotation
`Matrix.jacobiRotation A j k`. -/
theorem jacobiRotation_eq_planeRotation_small :
    jacobiRotation A j k = planeRotation j k (jacobiCosSmall A j k) (-jacobiSinSmall A j k) := by
  rw [jacobiRotation, jacobiCosSmall_eq, jacobiSinSmall_eq_neg, neg_neg]

/-- For $j \neq k$, the Jacobi rotation $U$ is orthogonal: $U^T U = I$. So a Jacobi step is an
orthogonal similarity. -/
theorem transpose_jacobiRotation_mul_self (hjk : j ≠ k) :
    (jacobiRotation A j k)ᵀ * jacobiRotation A j k = 1 :=
  transpose_planeRotation_mul_self hjk (jacobiCos_sq_add_jacobiSin_sq A j k)

omit [Fintype n] [DecidableEq n] in
/-- The Jacobi cosine is positive: $c > 0$. -/
theorem jacobiCos_pos : 0 < jacobiCos A j k := by
  rw [jacobiCos]
  positivity

omit [Fintype n] [DecidableEq n] in
/-- The Jacobi cosine satisfies $c \le 1$. -/
theorem jacobiCos_le_one : jacobiCos A j k ≤ 1 := by
  nlinarith [jacobiCos_sq_add_jacobiSin_sq A j k, jacobiCos_pos A j k,
    sq_nonneg (jacobiSin A j k)]

omit [Fintype n] [DecidableEq n] in
/-- The Jacobi sine satisfies $|s| \le 1$. -/
theorem abs_jacobiSin_le_one : |jacobiSin A j k| ≤ 1 := by
  have h := jacobiCos_sq_add_jacobiSin_sq A j k
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (jacobiCos A j k), sq_nonneg (jacobiSin A j k + 1),
    sq_nonneg (jacobiSin A j k - 1)]

end Jacobi

/-! ### One Jacobi step -/

section Step

variable {c s : ℝ} {j k : n} (A : Matrix n n ℝ)

/-- **A Jacobi step annihilates the chosen entry** ([kress1998numerical], Lemma 7.13). Let $A$ be
real symmetric and $j \neq k$. Then the $(j, k)$ entry of the Jacobi step $U^T A U$ is $0$. -/
theorem jacobiStep_apply_eq_zero (hA : A.IsSymm) (hjk : j ≠ k) : jacobiStep A j k j k = 0 := by
  have hsym : A k j = A j k := hA.apply j k
  rw [jacobiStep, jacobiRotation, conj_planeRotation_apply_jk hjk, hsym]
  linear_combination jacobi_annihilate A j k

/-- Let $A$ be real symmetric and $j \neq k$, and let $c$ and $s$ be the Jacobi cosine and sine. The
$(j, j)$ entry of the Jacobi step is
$$(U^T A U)_{jj} = c^2 a_{jj} + 2 c s \, a_{jk} + s^2 a_{kk}.$$
-/
theorem jacobiStep_apply_jj (hA : A.IsSymm) (hjk : j ≠ k) :
    jacobiStep A j k j j = jacobiCos A j k ^ 2 * A j j
      + 2 * (jacobiCos A j k * jacobiSin A j k) * A j k + jacobiSin A j k ^ 2 * A k k := by
  have hsym : A k j = A j k := hA.apply j k
  rw [jacobiStep, jacobiRotation, conj_planeRotation_apply_jj hjk, hsym]
  ring

/-- Let $A$ be real symmetric and $j \neq k$, and let $c$ and $s$ be the Jacobi cosine and sine. The
$(k, k)$ entry of the Jacobi step is
$$(U^T A U)_{kk} = s^2 a_{jj} - 2 c s \, a_{jk} + c^2 a_{kk}.$$
-/
theorem jacobiStep_apply_kk (hA : A.IsSymm) (hjk : j ≠ k) :
    jacobiStep A j k k k = jacobiSin A j k ^ 2 * A j j
      - 2 * (jacobiCos A j k * jacobiSin A j k) * A j k + jacobiCos A j k ^ 2 * A k k := by
  have hsym : A k j = A j k := hA.apply j k
  rw [jacobiStep, jacobiRotation, conj_planeRotation_apply_kk hjk, hsym]
  ring

/-- For $j \neq k$, a Jacobi step does not change a diagonal entry outside the rotated plane:
$(U^T A U)_{ii} = a_{ii}$ for $i \neq j, k$. -/
theorem jacobiStep_apply_diag_of_ne (hjk : j ≠ k) {i : n} (hij : i ≠ j) (hik : i ≠ k) :
    jacobiStep A j k i i = A i i := by
  rw [jacobiStep, jacobiRotation, conj_planeRotation_apply_of_ne hjk A hij hik hij hik]

omit [Fintype n] [DecidableEq n] in
/-- If $c^2 + s^2 = 1$ and $(c^2 - s^2) w + c s (v - u) = 0$, then the rotation of the symmetric
block $\begin{pmatrix} u & w \\ w & v \end{pmatrix}$ moves exactly $2 w^2$ of mass onto the
diagonal; this is the algebraic core of Lemma 7.13 of [kress1998numerical]. -/
private theorem sq_add_sq_of_rotation {u v w : ℝ} (h1 : c ^ 2 + s ^ 2 = 1)
    (h2 : (c ^ 2 - s ^ 2) * w + c * s * (v - u) = 0) :
    (c ^ 2 * u + 2 * (c * s) * w + s ^ 2 * v) ^ 2
        + (s ^ 2 * u - 2 * (c * s) * w + c ^ 2 * v) ^ 2
      = u ^ 2 + v ^ 2 + 2 * w ^ 2 := by
  linear_combination (-2 * ((c ^ 2 - s ^ 2) * w + c * s * (v - u))) * h2
    + ((c ^ 2 + s ^ 2 + 1) * (u ^ 2 + v ^ 2 + 2 * w ^ 2)) * h1

private theorem sum_split (hjk : j ≠ k) (f : n → ℝ) :
    ∑ i, f i = f j + f k + ∑ i ∈ (Finset.univ.erase j).erase k, f i := by
  rw [← Finset.add_sum_erase _ f (Finset.mem_univ j),
    ← Finset.add_sum_erase _ f (Finset.mem_erase.2 ⟨Ne.symm hjk, Finset.mem_univ k⟩), add_assoc]

/-- Let $A$ be real symmetric, let $j \neq k$, and let $G$ be the plane rotation
`Matrix.planeRotation j k c s` with $c^2 + s^2 = 1$. If $(G^T A G)_{jk} = 0$, then
$$\sum_i \bigl( (G^T A G)_{ii} \bigr)^2 = \sum_i a_{ii}^2 + 2 a_{jk}^2.$$

So the rotation moves exactly $2 a_{jk}^2$ of mass onto the diagonal, whatever its angle. -/
theorem sum_diag_sq_conj_planeRotation_of_apply_eq_zero (hA : A.IsSymm) (hjk : j ≠ k)
    (hcs : c ^ 2 + s ^ 2 = 1)
    (h0 : ((planeRotation j k c s)ᵀ * A * planeRotation j k c s) j k = 0) :
    ∑ i, (((planeRotation j k c s)ᵀ * A * planeRotation j k c s) i i) ^ 2
      = ∑ i, (A i i) ^ 2 + 2 * (A j k) ^ 2 := by
  have hsym : A k j = A j k := hA.apply j k
  set G := planeRotation j k c s with hG
  have htail : ∑ i ∈ (Finset.univ.erase j).erase k, ((Gᵀ * A * G) i i) ^ 2
      = ∑ i ∈ (Finset.univ.erase j).erase k, (A i i) ^ 2 := by
    refine Finset.sum_congr rfl fun i hi => ?_
    obtain ⟨hik, hi'⟩ := Finset.mem_erase.1 hi
    obtain ⟨hij, -⟩ := Finset.mem_erase.1 hi'
    rw [hG, conj_planeRotation_apply_of_ne hjk A hij hik hij hik]
  rw [hG, conj_planeRotation_apply_jk hjk, hsym] at h0
  have hpoly := sq_add_sq_of_rotation (u := A j j) (v := A k k) (w := A j k) hcs
    (by linear_combination h0)
  rw [sum_split hjk (fun i => ((Gᵀ * A * G) i i) ^ 2), sum_split hjk (fun i => (A i i) ^ 2),
    htail, hG, conj_planeRotation_apply_jj hjk, conj_planeRotation_apply_kk hjk, hsym]
  linarith [hpoly]

/-- **The decrease of the off-diagonal mass for any annihilating rotation.** Let $A$ be real
symmetric, let $j \neq k$, and let $G$ be the plane rotation `Matrix.planeRotation j k c s` with
$c^2 + s^2 = 1$. If $(G^T A G)_{jk} = 0$, then
$$N(G^T A G)^2 = N(A)^2 - 2 a_{jk}^2.$$

This is Lemma 7.13 of [kress1998numerical] and (5.64) of [quarteroni2000numerical]. The
orthogonal similarity does not change the squared Frobenius norm, and the rotation moves
$2 a_{jk}^2$ of it onto the diagonal. Both the Jacobi tangent `Matrix.jacobiTan` and the tangent
`Matrix.jacobiTanSmall` of [quarteroni2000numerical] give such a rotation. -/
theorem offDiagNormSq_conj_planeRotation_of_apply_eq_zero (hA : A.IsSymm) (hjk : j ≠ k)
    (hcs : c ^ 2 + s ^ 2 = 1)
    (h0 : ((planeRotation j k c s)ᵀ * A * planeRotation j k c s) j k = 0) :
    offDiagNormSq ((planeRotation j k c s)ᵀ * A * planeRotation j k c s)
      = offDiagNormSq A - 2 * (A j k) ^ 2 := by
  have hF : ∑ i, ∑ q, (((planeRotation j k c s)ᵀ * A * planeRotation j k c s) i q) ^ 2
      = ∑ i, ∑ q, (A i q) ^ 2 :=
    sum_sq_conj_eq A _ (transpose_planeRotation_mul_self hjk hcs)
  have h1 := offDiagNormSq_add_sum_diag_sq_real
    ((planeRotation j k c s)ᵀ * A * planeRotation j k c s)
  have h2 := offDiagNormSq_add_sum_diag_sq_real A
  have hD := sum_diag_sq_conj_planeRotation_of_apply_eq_zero A hA hjk hcs h0
  linarith

/-- Let $A$ be real symmetric and $j \neq k$. A Jacobi step moves exactly $2 a_{jk}^2$ of mass onto
the diagonal:
$$\sum_i \bigl( (U^T A U)_{ii} \bigr)^2 = \sum_i a_{ii}^2 + 2 a_{jk}^2.$$
-/
theorem sum_diag_sq_jacobiStep (hA : A.IsSymm) (hjk : j ≠ k) :
    ∑ i, (jacobiStep A j k i i) ^ 2 = ∑ i, (A i i) ^ 2 + 2 * (A j k) ^ 2 :=
  sum_diag_sq_conj_planeRotation_of_apply_eq_zero A hA hjk (jacobiCos_sq_add_jacobiSin_sq A j k)
    (jacobiStep_apply_eq_zero A hA hjk)

/-- **The decrease of the off-diagonal mass in a Jacobi step.** Let $A$ be real symmetric and
$j \neq k$, and let $U$ be the Jacobi rotation in the $(j, k)$-plane. Then
$$N(U^T A U)^2 = N(A)^2 - 2 a_{jk}^2.$$

This is Lemma 7.13 of [kress1998numerical]. It is
`Matrix.offDiagNormSq_conj_planeRotation_of_apply_eq_zero` for the Jacobi tangent
`Matrix.jacobiTan`. -/
theorem offDiagNormSq_jacobiStep (hA : A.IsSymm) (hjk : j ≠ k) :
    offDiagNormSq (jacobiStep A j k) = offDiagNormSq A - 2 * (A j k) ^ 2 :=
  offDiagNormSq_conj_planeRotation_of_apply_eq_zero A hA hjk (jacobiCos_sq_add_jacobiSin_sq A j k)
    (jacobiStep_apply_eq_zero A hA hjk)

/-- A Jacobi step of a real symmetric matrix is symmetric, because it is an orthogonal similarity.
-/
theorem isSymm_jacobiStep {A : Matrix n n ℝ} (hA : A.IsSymm) (j k : n) :
    (jacobiStep A j k).IsSymm := by
  rw [Matrix.IsSymm, jacobiStep, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, hA, ← Matrix.mul_assoc]

/-- **The $(j, j)$ entry moves by $t a_{jk}$.** Let $A$ be real symmetric and $j \neq k$, and let
$t$ be the Jacobi tangent. Then
$$(U^T A U)_{jj} - a_{jj} = t \, a_{jk}.$$

Since $|t| \le 1$, the entry moves by at most $|a_{jk}|$. -/
theorem jacobiStep_apply_jj_sub (hA : A.IsSymm) (hjk : j ≠ k) :
    jacobiStep A j k j j - A j j = jacobiTan A j k * A j k := by
  have hcs := jacobiCos_sq_add_jacobiSin_sq A j k
  have hann := jacobiTan_annihilate A j k
  rw [jacobiSin] at hcs
  rw [jacobiStep_apply_jj A hA hjk, jacobiSin]
  linear_combination (A j j + jacobiTan A j k * A j k) * hcs
    + (jacobiTan A j k * jacobiCos A j k ^ 2) * hann

/-- **The $(k, k)$ entry moves by $-t a_{jk}$.** Let $A$ be real symmetric and $j \neq k$, and let
$t$ be the Jacobi tangent. Then
$$(U^T A U)_{kk} - a_{kk} = -t \, a_{jk}.$$
-/
theorem jacobiStep_apply_kk_sub (hA : A.IsSymm) (hjk : j ≠ k) :
    jacobiStep A j k k k - A k k = -(jacobiTan A j k * A j k) := by
  have hcs := jacobiCos_sq_add_jacobiSin_sq A j k
  have hann := jacobiTan_annihilate A j k
  rw [jacobiSin] at hcs
  rw [jacobiStep_apply_kk A hA hjk, jacobiSin]
  linear_combination (A k k - jacobiTan A j k * A j k) * hcs
    - (jacobiTan A j k * jacobiCos A j k ^ 2) * hann

/-- **The distance moved by a Jacobi step.** Let $A$ be real symmetric and $p \neq q$, let $c$ be
the Jacobi cosine, and let $B = U^T A U$ be the Jacobi step in the $(p, q)$-plane. Then
$$\|B - A\|_F^2 = 4 (1 - c) \sum_{i \neq p, q} (a_{ip}^2 + a_{iq}^2) + \frac{2 a_{pq}^2}{c^2}.$$

This is a formula of [golub2013matrix] §8.5.2. The left side is written as the double sum
$\sum_{i, l} (b_{il} - a_{il})^2$. Only the rows and the columns $p$ and $q$ change. The cross
terms simplify by $c^2 + s^2 = 1$, and the two diagonal entries move by $\pm t a_{pq}$
(`Matrix.jacobiStep_apply_jj_sub`). -/
theorem sum_sq_jacobiStep_sub (hA : A.IsSymm) {p q : n} (hpq : p ≠ q) :
    ∑ i, ∑ l, (jacobiStep A p q i l - A i l) ^ 2 =
      4 * (1 - jacobiCos A p q) * ∑ i ∈ (univ.erase p).erase q, (A i p ^ 2 + A i q ^ 2) +
        2 * A p q ^ 2 / jacobiCos A p q ^ 2 := by
  set B := jacobiStep A p q with hBdef
  set C := jacobiCos A p q with hCdef
  set S := jacobiSin A p q with hSdef
  have hB : B = (planeRotation p q C S)ᵀ * A * planeRotation p q C S := rfl
  have hcs : C ^ 2 + S ^ 2 = 1 := jacobiCos_sq_add_jacobiSin_sq A p q
  have hqp : A q p = A p q := hA.apply p q
  have hmem : ∀ i, i ∈ (Finset.univ.erase p).erase q → i ≠ p ∧ i ≠ q := fun i hi => by
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hi
    exact ⟨hi.2, hi.1⟩
  -- the entries of `B`
  have hBij : ∀ i j, i ∈ (Finset.univ.erase p).erase q → j ∈ (Finset.univ.erase p).erase q →
      B i j = A i j := fun i j hi hj => by
    rw [hB]
    exact conj_planeRotation_apply_of_ne hpq A (hmem i hi).1 (hmem i hi).2 (hmem j hj).1
      (hmem j hj).2
  have hBip : ∀ i ∈ (Finset.univ.erase p).erase q, B i p = C * A i p + S * A i q := fun i hi => by
    rw [hB]; exact conj_planeRotation_apply_col_j hpq A (hmem i hi).1 (hmem i hi).2
  have hBiq : ∀ i ∈ (Finset.univ.erase p).erase q, B i q = -S * A i p + C * A i q :=
    fun i hi => by rw [hB]; exact conj_planeRotation_apply_col_k hpq A (hmem i hi).1 (hmem i hi).2
  have hBpj : ∀ j ∈ (Finset.univ.erase p).erase q, B p j = C * A p j + S * A q j := fun j hj => by
    rw [hB]; exact conj_planeRotation_apply_row_j hpq A (hmem j hj).1 (hmem j hj).2
  have hBqj : ∀ j ∈ (Finset.univ.erase p).erase q, B q j = -S * A p j + C * A q j :=
    fun j hj => by rw [hB]; exact conj_planeRotation_apply_row_k hpq A (hmem j hj).1 (hmem j hj).2
  have hBpq : B p q = 0 := jacobiStep_apply_eq_zero A hA hpq
  have hBqp : B q p = 0 := ((isSymm_jacobiStep hA p q).apply p q).trans hBpq
  have hBpp : B p p - A p p = jacobiTan A p q * A p q := jacobiStep_apply_jj_sub A hA hpq
  have hBqq : B q q - A q q = -(jacobiTan A p q * A p q) := jacobiStep_apply_kk_sub A hA hpq
  -- `c² = 1 / (1 + t²)`
  have hC2 : 2 * A p q ^ 2 / C ^ 2 = 2 * A p q ^ 2 * (1 + jacobiTan A p q ^ 2) := by
    have hpos : 0 < 1 + jacobiTan A p q ^ 2 := by positivity
    have : C ^ 2 = 1 / (1 + jacobiTan A p q ^ 2) := by
      rw [hCdef, jacobiCos, div_pow, one_pow, Real.sq_sqrt hpos.le]
    rw [this]
    field_simp
  -- split every sum over `n` at `p` and `q`
  have hsplit : ∀ h : n → ℝ,
      ∑ j, h j = h p + h q + ∑ j ∈ (Finset.univ.erase p).erase q, h j := fun h => by
    rw [← Finset.add_sum_erase Finset.univ h (Finset.mem_univ p),
      ← Finset.add_sum_erase (Finset.univ.erase p) h
        (Finset.mem_erase.2 ⟨hpq.symm, Finset.mem_univ q⟩)]
    ring
  rw [Finset.sum_congr rfl fun i _ => hsplit (fun j => (B i j - A i j) ^ 2),
    hsplit (fun i => (B i p - A i p) ^ 2 + (B i q - A i q) ^ 2 +
      ∑ j ∈ (Finset.univ.erase p).erase q, (B i j - A i j) ^ 2)]
  have h1 : ∑ i ∈ (Finset.univ.erase p).erase q, ((B i p - A i p) ^ 2 + (B i q - A i q) ^ 2 +
      ∑ j ∈ (Finset.univ.erase p).erase q, (B i j - A i j) ^ 2) =
      (2 - 2 * C) * ∑ i ∈ (Finset.univ.erase p).erase q, (A i p ^ 2 + A i q ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_eq_zero fun j hj => by rw [hBij i j hi hj]; ring, hBip i hi, hBiq i hi]
    linear_combination (A i p ^ 2 + A i q ^ 2) * hcs
  have h2 : ∑ j ∈ (Finset.univ.erase p).erase q, (B p j - A p j) ^ 2 +
      ∑ j ∈ (Finset.univ.erase p).erase q, (B q j - A q j) ^ 2 =
      (2 - 2 * C) * ∑ i ∈ (Finset.univ.erase p).erase q, (A i p ^ 2 + A i q ^ 2) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hBpj j hj, hBqj j hj, hA.apply j p, hA.apply j q]
    linear_combination (A j p ^ 2 + A j q ^ 2) * hcs
  rw [h1, hBpp, hBqq, hBpq, hBqp, hqp, hC2]
  linear_combination h2


/-- Let $A$ be a real square matrix and $p \neq q$. Then every off-diagonal entry is at most the
square root of the off-diagonal mass:
$$|a_{pq}| \le \sqrt{N(A)^2} = N(A).$$
-/
theorem abs_le_sqrt_offDiagNormSq (A : Matrix n n ℝ) {p q : n} (hpq : p ≠ q) :
    |A p q| ≤ Real.sqrt (offDiagNormSq A) := by
  have h : (A p q) ^ 2 ≤ offDiagNormSq A := by
    rw [offDiagNormSq_real]
    calc (A p q) ^ 2 ≤ ∑ q' ∈ Finset.univ.erase p, (A p q') ^ 2 :=
          Finset.single_le_sum (f := fun q' => (A p q') ^ 2) (fun i _ => sq_nonneg _)
            (Finset.mem_erase.2 ⟨hpq.symm, Finset.mem_univ q⟩)
      _ ≤ ∑ i, ∑ q' ∈ Finset.univ.erase i, (A i q') ^ 2 :=
          Finset.single_le_sum (f := fun i => ∑ q' ∈ Finset.univ.erase i, (A i q') ^ 2)
            (fun i _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ p)
  calc |A p q| = Real.sqrt ((A p q) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (offDiagNormSq A) := Real.sqrt_le_sqrt h

/-- **A Jacobi step moves no entry by more than $2 N(A)$.** Let $A$ be real symmetric and
$j \neq k$, and let $U$ be the Jacobi rotation in the $(j, k)$-plane. Then for all indices $p$
and $q$
$$|(U^T A U)_{pq} - a_{pq}| \le 2 \sqrt{N(A)^2}.$$

Each entry that changes is a combination of off-diagonal entries of $A$ with coefficients of
modulus at most one, or the annihilated entry multiplied by the tangent; the bound $|t| \le 1$
of `Matrix.abs_jacobiTan_le_one` controls the second case. The convergence of the sequence of
matrices rests on this estimate. It fails for the other root of the Jacobi quadratic. -/
theorem abs_jacobiStep_sub_le (hA : A.IsSymm) (hjk : j ≠ k) (p q : n) :
    |jacobiStep A j k p q - A p q| ≤ 2 * Real.sqrt (offDiagNormSq A) := by
  have hnn : (0 : ℝ) ≤ Real.sqrt (offDiagNormSq A) := Real.sqrt_nonneg _
  have hc1 : jacobiCos A j k ≤ 1 := jacobiCos_le_one A j k
  have hc0 : 0 < jacobiCos A j k := jacobiCos_pos A j k
  have hs1 : |jacobiSin A j k| ≤ 1 := abs_jacobiSin_le_one A j k
  have ht1 : |jacobiTan A j k| ≤ 1 := abs_jacobiTan_le_one A j k
  have hcc : |jacobiCos A j k - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have htwo : ∀ x y u v : ℝ, |x| ≤ 1 → |y| ≤ 1 → |u| ≤ Real.sqrt (offDiagNormSq A) →
      |v| ≤ Real.sqrt (offDiagNormSq A) → |x * u + y * v| ≤ 2 * Real.sqrt (offDiagNormSq A) := by
    intro x y u v hx hy hu hv
    calc |x * u + y * v| ≤ |x * u| + |y * v| := abs_add_le _ _
      _ = |x| * |u| + |y| * |v| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * Real.sqrt (offDiagNormSq A) + 1 * Real.sqrt (offDiagNormSq A) :=
          add_le_add (mul_le_mul hx hu (abs_nonneg _) zero_le_one)
            (mul_le_mul hy hv (abs_nonneg _) zero_le_one)
      _ = 2 * Real.sqrt (offDiagNormSq A) := by ring
  have hone : ∀ u : ℝ, |u| ≤ Real.sqrt (offDiagNormSq A) →
      |u| ≤ 2 * Real.sqrt (offDiagNormSq A) := fun u hu => by linarith
  -- the four entries of the rotated block
  have cjj : |jacobiStep A j k j j - A j j| ≤ 2 * Real.sqrt (offDiagNormSq A) := by
    rw [jacobiStep_apply_jj_sub A hA hjk, abs_mul]
    have h := abs_le_sqrt_offDiagNormSq A hjk
    nlinarith [abs_nonneg (jacobiTan A j k), abs_nonneg (A j k)]
  have ckk : |jacobiStep A j k k k - A k k| ≤ 2 * Real.sqrt (offDiagNormSq A) := by
    rw [jacobiStep_apply_kk_sub A hA hjk, abs_neg, abs_mul]
    have h := abs_le_sqrt_offDiagNormSq A hjk
    nlinarith [abs_nonneg (jacobiTan A j k), abs_nonneg (A j k)]
  have cjk : |jacobiStep A j k j k - A j k| ≤ 2 * Real.sqrt (offDiagNormSq A) := by
    rw [jacobiStep_apply_eq_zero A hA hjk, zero_sub, abs_neg]
    exact hone _ (abs_le_sqrt_offDiagNormSq A hjk)
  have ckj : |jacobiStep A j k k j - A k j| ≤ 2 * Real.sqrt (offDiagNormSq A) := by
    rw [(isSymm_jacobiStep hA j k).apply j k, jacobiStep_apply_eq_zero A hA hjk, zero_sub,
      abs_neg, hA.apply j k]
    exact hone _ (abs_le_sqrt_offDiagNormSq A hjk)
  have cjq : ∀ q' : n, q' ≠ j → q' ≠ k →
      |jacobiStep A j k j q' - A j q'| ≤ 2 * Real.sqrt (offDiagNormSq A) := by
    intro q' hqj hqk
    rw [jacobiStep, jacobiRotation, conj_planeRotation_apply_row_j hjk A hqj hqk]
    have hexp : jacobiCos A j k * A j q' + jacobiSin A j k * A k q' - A j q'
        = (jacobiCos A j k - 1) * A j q' + jacobiSin A j k * A k q' := by ring
    rw [hexp]
    exact htwo _ _ _ _ hcc hs1 (abs_le_sqrt_offDiagNormSq A (Ne.symm hqj))
      (abs_le_sqrt_offDiagNormSq A (Ne.symm hqk))
  have ckq : ∀ q' : n, q' ≠ j → q' ≠ k →
      |jacobiStep A j k k q' - A k q'| ≤ 2 * Real.sqrt (offDiagNormSq A) := by
    intro q' hqj hqk
    rw [jacobiStep, jacobiRotation, conj_planeRotation_apply_row_k hjk A hqj hqk]
    have hexp : -jacobiSin A j k * A j q' + jacobiCos A j k * A k q' - A k q'
        = -jacobiSin A j k * A j q' + (jacobiCos A j k - 1) * A k q' := by ring
    rw [hexp]
    refine htwo _ _ _ _ ?_ hcc (abs_le_sqrt_offDiagNormSq A (Ne.symm hqj))
      (abs_le_sqrt_offDiagNormSq A (Ne.symm hqk))
    rwa [abs_neg]
  have cpj : ∀ p' : n, p' ≠ j → p' ≠ k →
      |jacobiStep A j k p' j - A p' j| ≤ 2 * Real.sqrt (offDiagNormSq A) := by
    intro p' hpj hpk
    rw [jacobiStep, jacobiRotation, conj_planeRotation_apply_col_j hjk A hpj hpk]
    have hexp : jacobiCos A j k * A p' j + jacobiSin A j k * A p' k - A p' j
        = (jacobiCos A j k - 1) * A p' j + jacobiSin A j k * A p' k := by ring
    rw [hexp]
    exact htwo _ _ _ _ hcc hs1 (abs_le_sqrt_offDiagNormSq A hpj)
      (abs_le_sqrt_offDiagNormSq A hpk)
  have cpk : ∀ p' : n, p' ≠ j → p' ≠ k →
      |jacobiStep A j k p' k - A p' k| ≤ 2 * Real.sqrt (offDiagNormSq A) := by
    intro p' hpj hpk
    rw [jacobiStep, jacobiRotation, conj_planeRotation_apply_col_k hjk A hpj hpk]
    have hexp : -jacobiSin A j k * A p' j + jacobiCos A j k * A p' k - A p' k
        = -jacobiSin A j k * A p' j + (jacobiCos A j k - 1) * A p' k := by ring
    rw [hexp]
    refine htwo _ _ _ _ ?_ hcc (abs_le_sqrt_offDiagNormSq A hpj)
      (abs_le_sqrt_offDiagNormSq A hpk)
    rwa [abs_neg]
  by_cases hpj : p = j
  · by_cases hqj : q = j
    · rw [hpj, hqj]; exact cjj
    · by_cases hqk : q = k
      · rw [hpj, hqk]; exact cjk
      · rw [hpj]; exact cjq q hqj hqk
  · by_cases hpk : p = k
    · by_cases hqj : q = j
      · rw [hpk, hqj]; exact ckj
      · by_cases hqk : q = k
        · rw [hpk, hqk]; exact ckk
        · rw [hpk]; exact ckq q hqj hqk
    · by_cases hqj : q = j
      · rw [hqj]; exact cpj p hpj hpk
      · by_cases hqk : q = k
        · rw [hqk]; exact cpk p hpj hpk
        · rw [jacobiStep, jacobiRotation, conj_planeRotation_apply_of_ne hjk A hpj hpk hqj hqk,
            sub_self, abs_zero]
          positivity

end Step

/-!
### The classical Jacobi method

From here on, the index type is nonempty, $n \ge 1$.
-/

section ClassicalJacobi

/-- A matrix of order at most one has no off-diagonal entries, so its off-diagonal mass is $0$.

This is the degenerate case that the geometric decay must treat separately, because the factor
$1/(n^2 - n)$ has no meaning there. -/
theorem offDiagNormSq_eq_zero_of_card_le_one (h : Fintype.card n ≤ 1) (A : Matrix n n ℝ) :
    offDiagNormSq A = 0 := by
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun q hq => ?_
  have hcard : (Finset.univ.erase i).card = 0 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
    omega
  rw [Finset.card_eq_zero] at hcard
  simp [hcard] at hq

variable [Nonempty n]

omit [DecidableEq n] [Nonempty n] in
/-- If $n \ge 2$, there is a pair of distinct indices at which $A$ has an off-diagonal entry of
largest modulus: there are $j \neq k$ with $|a_{pq}| \le |a_{jk}|$ for all $p \neq q$. This is
the choice that the classical method makes at every step. -/
theorem exists_maxOffDiagPair (A : Matrix n n ℝ) (hn : 2 ≤ Fintype.card n) :
    ∃ p : n × n, p.1 ≠ p.2 ∧ ∀ q : n × n, q.1 ≠ q.2 → |A q.1 q.2| ≤ |A p.1 p.2| := by
  classical
  have hnt : Nontrivial n := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨a, b, hab⟩ := exists_pair_ne n
  have hne : (Finset.univ.filter fun p : n × n => p.1 ≠ p.2).Nonempty :=
    ⟨(a, b), by simp [hab]⟩
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image _ (fun p : n × n => |A p.1 p.2|) hne
  exact ⟨p, (Finset.mem_filter.1 hp).2,
    fun q hq => hmax q (Finset.mem_filter.2 ⟨Finset.mem_univ q, hq⟩)⟩

omit [DecidableEq n] in
private theorem exists_maxOffDiagPair_aux (A : Matrix n n ℝ) :
    ∃ p : n × n, 2 ≤ Fintype.card n →
      p.1 ≠ p.2 ∧ ∀ q : n × n, q.1 ≠ q.2 → |A q.1 q.2| ≤ |A p.1 p.2| := by
  by_cases hn : 2 ≤ Fintype.card n
  · obtain ⟨p, hp⟩ := exists_maxOffDiagPair A hn
    exact ⟨p, fun _ => hp⟩
  · exact ⟨(Classical.arbitrary n, Classical.arbitrary n), fun h => absurd h hn⟩

/-- A pair of distinct indices at which the real matrix $A$ of order $n \ge 1$ has an off-diagonal
entry of largest modulus.

If $n < 2$, there is no such pair and the value is an unspecified pair. The two properties of
the pair, `Matrix.maxOffDiagPair_ne` and `Matrix.abs_le_abs_maxOffDiagPair`, both assume
$n \ge 2$. -/
noncomputable def maxOffDiagPair (A : Matrix n n ℝ) : n × n :=
  (exists_maxOffDiagPair_aux A).choose

omit [DecidableEq n] in
/-- If $n \ge 2$, the two indices of `Matrix.maxOffDiagPair` are distinct. -/
theorem maxOffDiagPair_ne (A : Matrix n n ℝ) (hn : 2 ≤ Fintype.card n) :
    (maxOffDiagPair A).1 ≠ (maxOffDiagPair A).2 :=
  ((exists_maxOffDiagPair_aux A).choose_spec hn).1

omit [DecidableEq n] in
/-- If $n \ge 2$, the pair $(j, k)$ given by `Matrix.maxOffDiagPair` has an entry of largest
off-diagonal modulus: $|a_{pq}| \le |a_{jk}|$ for all $p \neq q$. -/
theorem abs_le_abs_maxOffDiagPair (A : Matrix n n ℝ) (hn : 2 ≤ Fintype.card n) (q : n × n)
    (hq : q.1 ≠ q.2) :
    |A q.1 q.2| ≤ |A (maxOffDiagPair A).1 (maxOffDiagPair A).2| :=
  ((exists_maxOffDiagPair_aux A).choose_spec hn).2 q hq

/-- The **classical Jacobi method** for a real matrix $A$ of order $n \ge 1$: the sequence with
$A_0 = A$ in which $A_{\nu+1}$ is the Jacobi step of $A_\nu$ at the pair `Matrix.maxOffDiagPair`
of $A_\nu$, an off-diagonal entry of largest modulus.

This is the method of [kress1998numerical], Section 7.3. -/
noncomputable def classicalJacobiIterate (A : Matrix n n ℝ) : ℕ → Matrix n n ℝ
  | 0 => A
  | ν + 1 => jacobiStep (classicalJacobiIterate A ν)
      (maxOffDiagPair (classicalJacobiIterate A ν)).1
      (maxOffDiagPair (classicalJacobiIterate A ν)).2

/-- The classical Jacobi method starts at the given matrix: $A_0 = A$. -/
@[simp]
theorem classicalJacobiIterate_zero (A : Matrix n n ℝ) : classicalJacobiIterate A 0 = A := rfl

/-- One step of the classical Jacobi method is a Jacobi step at an off-diagonal entry of largest
modulus: $A_{\nu+1}$ is the Jacobi step of $A_\nu$ at `Matrix.maxOffDiagPair` of $A_\nu$. -/
theorem classicalJacobiIterate_succ (A : Matrix n n ℝ) (ν : ℕ) :
    classicalJacobiIterate A (ν + 1)
      = jacobiStep (classicalJacobiIterate A ν) (maxOffDiagPair (classicalJacobiIterate A ν)).1
        (maxOffDiagPair (classicalJacobiIterate A ν)).2 := rfl

/-- If $A$ is real symmetric, every iterate $A_\nu$ of the classical Jacobi method is symmetric. -/
theorem isSymm_classicalJacobiIterate {A : Matrix n n ℝ} (hA : A.IsSymm) :
    ∀ ν, (classicalJacobiIterate A ν).IsSymm
  | 0 => hA
  | ν + 1 => isSymm_jacobiStep (isSymm_classicalJacobiIterate hA ν) _ _

/-- Let $A$ be a real matrix of order $n \ge 1$, and let $|a_{pq}| \le |a_{jk}|$ for all $p \neq q$.
Then
$$N(A)^2 \le (n^2 - n) \, a_{jk}^2.$$

The mass is a sum of $n^2 - n$ terms, and each term is at most $a_{jk}^2$. So an off-diagonal
entry of largest modulus carries at least the fraction $1/(n^2 - n)$ of the mass. -/
theorem offDiagNormSq_le_mul_sq (A : Matrix n n ℝ) {j k : n}
    (hmax : ∀ q : n × n, q.1 ≠ q.2 → |A q.1 q.2| ≤ |A j k|) :
    offDiagNormSq A ≤ ((Fintype.card n : ℝ) ^ 2 - Fintype.card n) * (A j k) ^ 2 := by
  have hcard : (1 : ℕ) ≤ Fintype.card n := Fintype.card_pos
  have hrow : ∀ i : n, ∑ q ∈ Finset.univ.erase i, (A i q) ^ 2
      ≤ ((Fintype.card n : ℝ) - 1) * (A j k) ^ 2 := by
    intro i
    have hle : ∑ q ∈ Finset.univ.erase i, (A i q) ^ 2
        ≤ ∑ _q ∈ Finset.univ.erase i, (A j k) ^ 2 := by
      refine Finset.sum_le_sum fun q hq => ?_
      have h := hmax (i, q) (Ne.symm (Finset.mem_erase.1 hq).1)
      nlinarith [sq_abs (A i q), sq_abs (A j k), abs_nonneg (A i q), abs_nonneg (A j k)]
    refine hle.trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      nsmul_eq_mul, Nat.cast_sub hcard, Nat.cast_one]
  rw [offDiagNormSq_real]
  refine (Finset.sum_le_sum fun i _ => hrow i).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- Let $A$ be real symmetric of order $n \ge 2$. One step of the classical method, at the pair
`Matrix.maxOffDiagPair` of $A$, multiplies the off-diagonal mass by at most $1 - 2/(n^2 - n)$:
$$N(U^T A U)^2 \le \Bigl( 1 - \frac{2}{n^2 - n} \Bigr) N(A)^2.$$
-/
theorem offDiagNormSq_jacobiStep_maxOffDiagPair_le {A : Matrix n n ℝ} (hA : A.IsSymm)
    (hn : 2 ≤ Fintype.card n) :
    offDiagNormSq (jacobiStep A (maxOffDiagPair A).1 (maxOffDiagPair A).2)
      ≤ (1 - 2 / ((Fintype.card n : ℝ) ^ 2 - Fintype.card n)) * offDiagNormSq A := by
  have hc : (2 : ℝ) ≤ (Fintype.card n : ℝ) := by exact_mod_cast hn
  have hd : (0 : ℝ) < (Fintype.card n : ℝ) ^ 2 - Fintype.card n := by nlinarith
  have hb := offDiagNormSq_le_mul_sq A (abs_le_abs_maxOffDiagPair A hn)
  rw [offDiagNormSq_jacobiStep A hA (maxOffDiagPair_ne A hn)]
  have hkey : offDiagNormSq A / ((Fintype.card n : ℝ) ^ 2 - Fintype.card n)
      ≤ (A (maxOffDiagPair A).1 (maxOffDiagPair A).2) ^ 2 := (div_le_iff₀ hd).2 (by linarith)
  have hexp : (1 - 2 / ((Fintype.card n : ℝ) ^ 2 - Fintype.card n)) * offDiagNormSq A
      = offDiagNormSq A
        - 2 * (offDiagNormSq A / ((Fintype.card n : ℝ) ^ 2 - Fintype.card n)) := by
    field_simp
  rw [hexp]
  linarith

/-- **The geometric decay of the off-diagonal mass.** Let $A$ be real symmetric of order $n \ge 1$,
and let $A_\nu$ be the iterates of the classical Jacobi method. Then for every $\nu$
$$N(A_\nu)^2 \le \Bigl( 1 - \frac{2}{n^2 - n} \Bigr)^\nu N(A)^2.$$

This is the estimate in the proof of Theorem 7.14 of [kress1998numerical]. For $n = 1$, the Lean
value of $2 / 0$ is $0$, so the factor is $1$, and both sides are $0$. -/
theorem offDiagNormSq_classicalJacobiIterate_le {A : Matrix n n ℝ} (hA : A.IsSymm) (ν : ℕ) :
    offDiagNormSq (classicalJacobiIterate A ν)
      ≤ (1 - 2 / ((Fintype.card n : ℝ) ^ 2 - Fintype.card n)) ^ ν * offDiagNormSq A := by
  rcases lt_or_ge (Fintype.card n) 2 with hn | hn
  · rw [offDiagNormSq_eq_zero_of_card_le_one (by omega),
      offDiagNormSq_eq_zero_of_card_le_one (by omega) A, mul_zero]
  · have hc : (2 : ℝ) ≤ (Fintype.card n : ℝ) := by exact_mod_cast hn
    have hd : (2 : ℝ) ≤ (Fintype.card n : ℝ) ^ 2 - Fintype.card n := by nlinarith
    have hρ : 0 ≤ 1 - 2 / ((Fintype.card n : ℝ) ^ 2 - Fintype.card n) := by
      rw [sub_nonneg, div_le_one (by linarith)]
      linarith
    induction ν with
    | zero => simp
    | succ ν ih =>
      rw [classicalJacobiIterate_succ, pow_succ, mul_assoc, mul_comm _ (offDiagNormSq A),
        ← mul_assoc]
      refine (offDiagNormSq_jacobiStep_maxOffDiagPair_le (isSymm_classicalJacobiIterate hA ν)
        hn).trans ?_
      calc (1 - 2 / ((Fintype.card n : ℝ) ^ 2 - Fintype.card n))
            * offDiagNormSq (classicalJacobiIterate A ν)
          ≤ (1 - 2 / ((Fintype.card n : ℝ) ^ 2 - Fintype.card n))
              * ((1 - 2 / ((Fintype.card n : ℝ) ^ 2 - Fintype.card n)) ^ ν * offDiagNormSq A) :=
            mul_le_mul_of_nonneg_left ih hρ
        _ = _ := by ring

omit [Nonempty n] in
/-- For $j \neq k$, a Jacobi step is an orthogonal similarity. So it does not change the
characteristic polynomial, and hence it does not change the eigenvalues. -/
theorem charpoly_jacobiStep (A : Matrix n n ℝ) {j k : n} (hjk : j ≠ k) :
    (jacobiStep A j k).charpoly = A.charpoly := by
  have hU : (jacobiRotation A j k)ᵀ * jacobiRotation A j k = 1 :=
    transpose_jacobiRotation_mul_self A j k hjk
  have hU' : jacobiRotation A j k * (jacobiRotation A j k)ᵀ = 1 := _root_.mul_eq_one_comm.1 hU
  rw [jacobiStep, Matrix.mul_assoc, Matrix.charpoly_mul_comm, Matrix.mul_assoc, hU',
    Matrix.mul_one]

/-- **The classical Jacobi method does not change the eigenvalues.** Let $A$ be a real matrix of
order $n \ge 2$. Then every iterate $A_\nu$ of the classical Jacobi method has the
characteristic polynomial of $A$.

Each step is an orthogonal similarity. So the method moves the mass of the matrix onto the
diagonal without a change of the eigenvalues. -/
theorem charpoly_classicalJacobiIterate {A : Matrix n n ℝ} (hn : 2 ≤ Fintype.card n) :
    ∀ ν, (classicalJacobiIterate A ν).charpoly = A.charpoly
  | 0 => rfl
  | ν + 1 => by
    rw [classicalJacobiIterate_succ,
      charpoly_jacobiStep _ (maxOffDiagPair_ne (classicalJacobiIterate A ν) hn)]
    exact charpoly_classicalJacobiIterate hn ν

/-- **The off-diagonal mass tends to zero.** Let $A$ be real symmetric of order $n \ge 2$, and let
$A_\nu$ be the iterates of the classical Jacobi method. Then $N(A_\nu)^2 \to 0$ as
$\nu \to \infty$.

This is the first half of Theorem 7.14 of [kress1998numerical]. It follows from
`Matrix.offDiagNormSq_classicalJacobiIterate_le`, because the factor $1 - 2/(n^2 - n)$ is in
$[0, 1)$ for $n \ge 2$. -/
theorem tendsto_offDiagNormSq_classicalJacobiIterate {A : Matrix n n ℝ} (hA : A.IsSymm)
    (hn : 2 ≤ Fintype.card n) :
    Filter.Tendsto (fun ν => offDiagNormSq (classicalJacobiIterate A ν)) Filter.atTop (nhds 0) := by
  have hc : (2 : ℝ) ≤ (Fintype.card n : ℝ) := by exact_mod_cast hn
  have hd : (0 : ℝ) < (Fintype.card n : ℝ) ^ 2 - Fintype.card n := by nlinarith
  have hρ0 : 0 ≤ 1 - 2 / ((Fintype.card n : ℝ) ^ 2 - Fintype.card n) := by
    rw [sub_nonneg, div_le_one hd]
    nlinarith
  have hρ1 : 1 - 2 / ((Fintype.card n : ℝ) ^ 2 - Fintype.card n) < 1 :=
    sub_lt_self _ (by positivity)
  refine squeeze_zero (fun ν => offDiagNormSq_nonneg _)
    (fun ν => offDiagNormSq_classicalJacobiIterate_le hA ν) ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const (offDiagNormSq A)

/-- **The convergence of the classical Jacobi method.** Let $A$ be real symmetric of order
$n \ge 2$, and let $A_\nu$ be the iterates of the classical Jacobi method. Then there is a
diagonal matrix $\Lambda$ with the characteristic polynomial of $A$ such that
$A_\nu \to \Lambda$ as $\nu \to \infty$. So the diagonal of $\Lambda$ is the list of the
eigenvalues of $A$, with multiplicities.

This is Theorem 7.14 of [kress1998numerical]. That source proves only that the off-diagonal mass
tends to $0$ (`Matrix.tendsto_offDiagNormSq_classicalJacobiIterate`). The convergence of the
sequence of matrices is a separate theorem, usually attributed to Forsythe and Henrici, and it
is usually proved by showing that the limit points lie in the finite set of diagonal matrices
with the correct spectrum. That argument is not necessary here. By
`Matrix.abs_jacobiStep_sub_le`, a step moves each entry by at most $2 N(A_\nu)$, and by
`Matrix.offDiagNormSq_classicalJacobiIterate_le` the quantity $N(A_\nu)$ decays geometrically.
So the steps are bounded by a geometric series, and the sequence is a Cauchy sequence. -/
theorem tendsto_classicalJacobiIterate {A : Matrix n n ℝ} (hA : A.IsSymm)
    (hn : 2 ≤ Fintype.card n) :
    ∃ Λ : Matrix n n ℝ, Matrix.IsDiag Λ ∧ Matrix.charpoly Λ = A.charpoly ∧
      Filter.Tendsto (classicalJacobiIterate A) Filter.atTop (nhds Λ) := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = 1 - 2 / ((Fintype.card n : ℝ) ^ 2 - Fintype.card n) := ⟨_, rfl⟩
  have hc : (2 : ℝ) ≤ (Fintype.card n : ℝ) := by exact_mod_cast hn
  have hd : (0 : ℝ) < (Fintype.card n : ℝ) ^ 2 - Fintype.card n := by nlinarith
  have hρ0 : 0 ≤ ρ := by
    rw [hρ, sub_nonneg, div_le_one hd]
    nlinarith
  have hρ1 : ρ < 1 := by
    rw [hρ]
    exact sub_lt_self _ (by positivity)
  have hr1 : Real.sqrt ρ < 1 := by
    have h := Real.sqrt_lt_sqrt hρ0 hρ1
    rwa [Real.sqrt_one] at h
  have hsp : ∀ m : ℕ, Real.sqrt (ρ ^ m) = Real.sqrt ρ ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg hρ0 m), ih, pow_succ]
  have hstep : ∀ (p q : n) (ν : ℕ),
      dist (classicalJacobiIterate A ν p q) (classicalJacobiIterate A (ν + 1) p q)
        ≤ (2 * Real.sqrt (offDiagNormSq A)) * Real.sqrt ρ ^ ν := by
    intro p q ν
    rw [Real.dist_eq, abs_sub_comm, classicalJacobiIterate_succ]
    refine (abs_jacobiStep_sub_le _ (isSymm_classicalJacobiIterate hA ν)
      (maxOffDiagPair_ne _ hn) p q).trans ?_
    have hle : offDiagNormSq (classicalJacobiIterate A ν) ≤ ρ ^ ν * offDiagNormSq A := by
      rw [hρ]
      exact offDiagNormSq_classicalJacobiIterate_le hA ν
    calc 2 * Real.sqrt (offDiagNormSq (classicalJacobiIterate A ν))
        ≤ 2 * Real.sqrt (ρ ^ ν * offDiagNormSq A) := by
          have h := Real.sqrt_le_sqrt hle
          linarith
      _ = 2 * (Real.sqrt ρ ^ ν * Real.sqrt (offDiagNormSq A)) := by
          rw [Real.sqrt_mul (pow_nonneg hρ0 ν), hsp]
      _ = (2 * Real.sqrt (offDiagNormSq A)) * Real.sqrt ρ ^ ν := by ring
  have hcs : ∀ p q : n, ∃ l : ℝ,
      Filter.Tendsto (fun ν => classicalJacobiIterate A ν p q) Filter.atTop (nhds l) :=
    fun p q => cauchySeq_tendsto_of_complete
      (cauchySeq_of_le_geometric _ _ hr1 (hstep p q))
  choose Λ hΛ using hcs
  have htend : Filter.Tendsto (classicalJacobiIterate A) Filter.atTop (nhds (Matrix.of Λ)) :=
    tendsto_pi_nhds.2 fun p => tendsto_pi_nhds.2 fun q => hΛ p q
  refine ⟨Matrix.of Λ, ?_, ?_, htend⟩
  · have hoff : Filter.Tendsto (fun ν => offDiagNormSq (classicalJacobiIterate A ν))
        Filter.atTop (nhds (offDiagNormSq (Matrix.of Λ))) := by
      simp only [offDiagNormSq_real]
      exact tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun q _ => (hΛ i q).pow 2
    have hzero : offDiagNormSq (Matrix.of Λ) = 0 :=
      tendsto_nhds_unique hoff (tendsto_offDiagNormSq_classicalJacobiIterate hA hn)
    exact fun i j hij => offDiagNormSq_eq_zero_iff.1 hzero i j hij
  · refine Polynomial.funext fun x => ?_
    rw [Matrix.eval_charpoly, Matrix.eval_charpoly]
    have hcont : Continuous fun M : Matrix n n ℝ => (Matrix.scalar n x - M).det :=
      (continuous_const.sub continuous_id).matrix_det
    have hdet : Filter.Tendsto
        (fun ν => (Matrix.scalar n x - classicalJacobiIterate A ν).det) Filter.atTop
        (nhds ((Matrix.scalar n x - Matrix.of Λ).det)) := by
      simpa [Function.comp_def] using (hcont.continuousAt (x := Matrix.of Λ)).tendsto.comp htend
    have hconst : ∀ ν, (Matrix.scalar n x - classicalJacobiIterate A ν).det
        = (Matrix.scalar n x - A).det := by
      intro ν
      rw [← Matrix.eval_charpoly, ← Matrix.eval_charpoly, charpoly_classicalJacobiIterate hn ν]
    simp only [hconst] at hdet
    exact tendsto_nhds_unique hdet tendsto_const_nhds

end ClassicalJacobi

end Matrix

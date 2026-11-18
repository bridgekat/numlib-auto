/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.List.OfFn
import Numlib.Data.Matrix.Mul
import Numlib.LinearAlgebra.Matrix.Cholesky
import NumlibSurface.ConnGouldToint.Chapter07.Section03Matrix

/-!
# Conn, Gould and Toint, Section 7.3.7: Cholesky pivot detection in the Moré–Sorensen algorithm

This module connects the Moré–Sorensen algorithm of Section 7.3 of [conn2000trust] with computed
Cholesky factorizations. Let $M$ be a real symmetric matrix of order $n \ge 1$ with least eigenvalue
$\lambda_1$, and let $\lambda$ be a trial multiplier. The Cholesky recurrence for $M + \lambda I$
either computes a lower triangular factor with positive diagonal, which happens exactly when
$\lambda > -\lambda_1$, or stops at the first nonpositive pivot. In the first case two triangular
solves give the step $s(\lambda)$ and the LINPACK direction of Section 7.3.7. In the second case the
computed part of the factor gives the corrected kernel identity (7.3.17) on a leading principal
block. Either outcome gives a lower estimate of the pole $-\lambda_1$ (Algorithm 7.3.4, Steps 3b–d).
The resulting matrix recurrence agrees with the spectral recurrence of
`NumlibSurface.ConnGouldToint.Chapter07.Section03`, so its hard-case convergence follows from the
spectral results.

## Main definitions

* Algorithm 7.3.4, Step 1, `ConnGouldToint.Chapter07.firstFailedCholeskyPivot`: the first
  nonpositive computed pivot, if any.
* Algorithm 7.3.4, Step 3b(iii), `ConnGouldToint.Chapter07.moreSorensenBestBoundaryCoefficient`: the
  root of the boundary equation with the smaller model value.
* Algorithm 7.3.4, Steps 3b–d, `ConnGouldToint.Chapter07.moreSorensenMatrixLowerEstimate`: the
  computed lower estimate of the pole.
* Algorithm 7.3.4, `ConnGouldToint.Chapter07.moreSorensenMatrixIterates`: the computed multiplier
  orbit.

## Main results

* Algorithm 7.3.4, Step 1, `ConnGouldToint.Chapter07.firstFailedCholeskyPivot_spec` and
  `ConnGouldToint.Chapter07.firstFailedCholeskyPivot_eq_none_iff`: the scan returns a full factor or
  the first failed pivot, and it succeeds exactly for positive definite matrices.
* Algorithm 7.3.4, Steps 1 and 3b, `ConnGouldToint.Chapter07.cholesky_linpack_certificate`: a
  successful factorization gives the LINPACK certificate.
* Equation (7.3.17), `ConnGouldToint.Chapter07.choleskyFailedPivot_certificate`: a failed pivot
  gives the kernel identity of the corrected leading block.
* Algorithm 7.3.4, Step 3d, `ConnGouldToint.Chapter07.choleskyFailedPivot_lower_bound`: the failed
  pivot gives a lower bound on the pole.
* Algorithm 7.3.4, Step 3b(iii),
  `ConnGouldToint.Chapter07.moreSorensenBestBoundaryCoefficient_spec`: the selected root reaches the
  boundary with the least model value.
* Algorithm 7.3.4, Step 1, `ConnGouldToint.Chapter07.shiftedCholesky_succeeds_iff`: the computed
  pivot test succeeds exactly above the pole.
* Algorithm 7.3.4, `ConnGouldToint.Chapter07.moreSorensenMatrixLowerEstimate_spec`,
  `ConnGouldToint.Chapter07.moreSorensenMatrixIterates_succ` and
  `ConnGouldToint.Chapter07.shiftedStep_eq_cholesky_subst`: the computed estimate, recurrence and
  step agree with the spectral ones.
* Theorem 7.3.4, `ConnGouldToint.Chapter07.moreSorensen_computed_hard_matrix_run`: in the hard case
  the computed run converges to the pole, and the computed corrected steps have minimizing model
  values and limit points.

## Implementation notes

* The computed factor is `Matrix.cholesky`, the Cholesky recurrence evaluated without a positivity
  check. Its first nonpositive diagonal entry is the failed pivot.
* A symmetric matrix $M$ acts on `EuclideanSpace ℝ (Fin n)` through `Matrix.toEuclideanCLM`, and
  $\lambda_1$ is `Subproblem.leftmost` of that operator.

## Deviations from the source

* **Equation (7.3.17)** (correction). The kernel identity at a failed pivot holds on the leading
  principal block, not on the full matrix. See
  `ConnGouldToint.Chapter07.choleskyFailedPivot_certificate`.
* **Algorithm 7.3.4, Step 3b(iii)** (reading). When the two roots of the boundary equation give the
  same model value, the root with the positive square root is chosen. See
  `ConnGouldToint.Chapter07.moreSorensenBestBoundaryCoefficient`.
-/

namespace ConnGouldToint.Chapter07

open Matrix

private theorem cholesky_mul_transpose_apply_of_pos {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) {i j : Fin n} (hji : j ≤ i)
    (hpos : 0 < cholesky A j j) :
    (cholesky A * (cholesky A)ᵀ) i j = A i j := by
  let L := cholesky A
  have hrow : (L * Lᵀ) i j = (L *ᵥ L i) j := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  change (L * Lᵀ) i j = A i j
  rw [hrow, Matrix.mulVec_apply_of_isLowerTriangular (isLowerTriangular_cholesky A)]
  change (∑ t ∈ Finset.univ.filter (· < j), L j t * L i t) + L j j * L i j = A i j
  rcases hji.eq_or_lt with he | hlt
  · subst j
    have hp : L i i = √(A i i - ∑ k ∈ Finset.univ.filter (· < i), (L i k)^2) := by
      simpa [L, Real.norm_eq_abs, sq_abs] using cholesky_apply_self A i
    have hd : 0 < A i i - ∑ k ∈ Finset.univ.filter (· < i), (L i k)^2 :=
      Real.sqrt_pos.mp (hp ▸ hpos)
    have hs := Real.sq_sqrt hd.le
    rw [← hp] at hs
    change (∑ t ∈ Finset.univ.filter (· < i), L i t * L i t) + L i i * L i i = A i i
    simp only [← pow_two]
    linarith
  · have hp : L i j =
        (A i j - ∑ k ∈ Finset.univ.filter (· < j), L i k * L j k) / L j j := by
      simpa [L] using cholesky_apply_of_lt A hlt
    have hm := (eq_div_iff hpos.ne').mp hp
    have hsum : (∑ t ∈ Finset.univ.filter (· < j), L j t * L i t) =
        ∑ t ∈ Finset.univ.filter (· < j), L i t * L j t :=
      Finset.sum_congr rfl fun t _ => mul_comm _ _
    rw [hsum, mul_comm (L j j), hm]
    ring

/-- **Algorithm 7.3.4** of [conn2000trust], Step 1, the first failed pivot. For a square matrix $A$
of order $n$, scan the computed Cholesky diagonal entries $L_{11}, L_{22}, \dots$ in order and
return the first index $k$ with $L_{kk} \le 0$, or no index if all are positive. -/
noncomputable def firstFailedCholeskyPivot {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Option (Fin n) :=
  (List.ofFn (id : Fin n → Fin n)).find? (fun i => decide (cholesky A i i ≤ 0))

/-- **Algorithm 7.3.4** of [conn2000trust], Step 1, full factor or first failed pivot. Let $A$ be
symmetric, and let $L$ be its computed Cholesky factor. If the scan finds no failed pivot, then
$L$ is lower triangular with positive diagonal and $L L^T = A$. If the scan returns $k$, then
$L_{kk} \le 0$ and $L_{jj} > 0$ for all $j < k$. -/
theorem firstFailedCholeskyPivot_spec {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsSymm) :
    match firstFailedCholeskyPivot A with
    | none => (cholesky A).IsLowerTriangular ∧ (∀ i, 0 < cholesky A i i) ∧
        cholesky A * (cholesky A)ᵀ = A
    | some k => cholesky A k k ≤ 0 ∧ ∀ j < k, 0 < cholesky A j j := by
  unfold firstFailedCholeskyPivot
  let failed := fun i : Fin n => decide (cholesky A i i ≤ 0)
  change match (List.ofFn (id : Fin n → Fin n)).find? failed with
    | none => _
    | some k => _
  split
  · rename_i h
    have hd (i : Fin n) : 0 < cholesky A i i := by
      have hi := List.find?_eq_none.mp h i (by simp)
      simpa only [failed, decide_eq_true_eq, not_le] using hi
    refine ⟨isLowerTriangular_cholesky A, hd, ?_⟩
    ext i j
    rcases le_total j i with hji | hij
    · exact cholesky_mul_transpose_apply_of_pos A hji (hd j)
    · have ht : (cholesky A * (cholesky A)ᵀ)ᵀ = cholesky A * (cholesky A)ᵀ := by
        rw [Matrix.transpose_mul, Matrix.transpose_transpose]
      rw [← ht, Matrix.transpose_apply, cholesky_mul_transpose_apply_of_pos A hij (hd i)]
      exact hA.apply _ _
  · rename_i k h
    have hk := (List.find?_ofFn_eq_some_of_injective (f := id) Function.injective_id).mp h
    simpa only [id_eq, failed, decide_eq_true_eq, not_le] using hk

/-- **Algorithm 7.3.4** of [conn2000trust], Step 1, the positive definiteness test. For a symmetric
matrix $A$, the scan finds no failed pivot if and only if $A$ is positive definite. -/
theorem firstFailedCholeskyPivot_eq_none_iff {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsSymm) : firstFailedCholeskyPivot A = none ↔ A.PosDef := by
  constructor
  · intro h
    have hs := firstFailedCholeskyPivot_spec hA
    rw [h] at hs
    obtain ⟨hL, hd, hfact⟩ := hs
    have hc : IsCholesky A (cholesky A)ᵀ := by
      refine ⟨fun _ _ hij => hL hij, hd, ?_⟩
      rw [conjTranspose_eq_transpose_of_trivial, transpose_transpose, hfact]
    exact hc.posDef
  · intro hp
    have hd := (isCholesky_cholesky hp).diag_pos
    unfold firstFailedCholeskyPivot
    rw [List.find?_eq_none]
    intro i _ hi
    exact (hd i).not_ge (of_decide_eq_true hi)

/-- **Algorithm 7.3.4** of [conn2000trust], Steps 1 and 3b, the certificate of a successful
factorization. Let $A$ be symmetric and suppose that the scan finds no failed pivot. Let $L$ be
the computed factor, $w$ the greedy forward substitution for $L$,
$v_i = \sigma(\sum_{j < i} L_{ij} w_j)$ with the LINPACK sign $\sigma$, and $y$ the back
substitution solution of $L^T y = w$. Then $L L^T = A$, $L$ is lower triangular with positive
diagonal, and
$$L w = v, \qquad L^T y = w, \qquad v_i = \sigma(v_i - L_{ii} w_i) \text{ for all } i.$$

This is the certificate that `ConnGouldToint.Chapter07.linpackCurvature_bound` uses. -/
theorem cholesky_linpack_certificate {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsSymm) (h : firstFailedCholeskyPivot A = none) :
    let L := cholesky A
    let w := linpackForwardSubst L
    let v := fun i => linpackSign (∑ j ∈ Finset.univ.filter (· < i), L i j * w j)
    let y := Lᵀ.backSubst w
    L * Lᵀ = A ∧ L.IsLowerTriangular ∧ (∀ i, 0 < L i i) ∧
      L *ᵥ w = v ∧ Lᵀ *ᵥ y = w ∧ ∀ i, v i = linpackSign (v i - L i i * w i) := by
  have hs := firstFailedCholeskyPivot_spec hA
  rw [h] at hs
  obtain ⟨hL, hd, hfact⟩ := hs
  exact ⟨hfact, hL, hd, linpack_triangular_solves hL (fun i => (hd i).ne')⟩

/-- **Equation (7.3.17)** of [conn2000trust] and Algorithm 7.3.4, Steps 3c–d, the computed
leading-block correction. Let $A$ be symmetric, and suppose that the scan returns the failed
pivot $k$. Let $B$ be the leading principal block of $A$ on the indices $j \le k$, let $L$ be
the leading $k \times k$ block of the computed factor, let $c$ be row $k$ of the computed factor
in the columns $j < k$, and let $\delta = c c^T - A_{kk}$. Let $v$ be the back solve at the
failed pivot and $e$ the unit vector of the pivot. Then
$$\delta \ge 0, \qquad v_k = 1, \qquad (B + \delta e e^T) v = 0, \qquad v^T B v = -\delta.$$

**Correction.** The kernel identity holds on the leading principal block; it can fail for the
full matrix, as `ConnGouldToint.Chapter07.failedCholeskyPivot_full_residual_counterexample`
shows.

The identity uses only entries that the Cholesky recurrence computed before the failure. -/
theorem choleskyFailedPivot_certificate {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsSymm) {k : Fin n} (hk : firstFailedCholeskyPivot A = some k) :
    let ι := {j : Fin n // j < k}
    let f : ι ⊕ Unit → Fin n := Sum.elim Subtype.val (fun _ => k)
    let B := A.submatrix f f
    let L := (cholesky A).submatrix (Subtype.val : ι → Fin n) (Subtype.val : ι → Fin n)
    let C : Matrix Unit ι ℝ := Matrix.of fun _ j => cholesky A k j
    let δ := (C * Cᵀ) () () - A k k
    let v := failedCholeskyBackSubst L C
    let e : ι ⊕ Unit → ℝ := Sum.elim (0 : ι → ℝ) (fun _ : Unit => 1)
    0 ≤ δ ∧ v (Sum.inr ()) = 1 ∧ (B + δ • vecMulVec e e) *ᵥ v = 0 ∧
      v ⬝ᵥ B *ᵥ v = -δ := by
  have hspec := firstFailedCholeskyPivot_spec hA
  rw [hk] at hspec
  dsimp only at hspec
  let ι := {j : Fin n // j < k}
  let f : ι ⊕ Unit → Fin n := Sum.elim Subtype.val (fun _ => k)
  let B := A.submatrix f f
  let L := (cholesky A).submatrix (Subtype.val : ι → Fin n) (Subtype.val : ι → Fin n)
  let C : Matrix Unit ι ℝ := Matrix.of fun _ j => cholesky A k j
  let δ := (C * Cᵀ) () () - A k k
  let e : ι ⊕ Unit → ℝ := Sum.elim (0 : ι → ℝ) (fun _ : Unit => 1)
  have hsub (g : Fin n → ℝ) :
      (∑ j : ι, g j) = ∑ j ∈ Finset.univ.filter (· < k), g j :=
    (Finset.sum_subtype _ Finset.mem_filter_univ g).symm
  have hδ : 0 ≤ δ := by
    have hp : cholesky A k k =
        √(A k k - ∑ j ∈ Finset.univ.filter (· < k), (cholesky A k j)^2) := by
      simpa [Real.norm_eq_abs, sq_abs] using cholesky_apply_self A k
    have hz : √(A k k - ∑ j ∈ Finset.univ.filter (· < k), (cholesky A k j)^2) = 0 :=
      le_antisymm (hp ▸ hspec.1) (Real.sqrt_nonneg _)
    have hle := Real.sqrt_eq_zero'.mp hz
    change 0 ≤ (∑ j : ι, cholesky A k j * cholesky A k j) - A k k
    rw [hsub (fun j => cholesky A k j * cholesky A k j)]
    simpa only [pow_two] using sub_nonneg.mpr (sub_nonpos.mp hle)
  have hsum (i j : Fin n) (hij : i < k ∨ j < k) :
      (∑ t : ι, cholesky A i t * cholesky A j t) =
        (cholesky A * (cholesky A)ᵀ) i j := by
    rw [hsub (fun t => cholesky A i t * cholesky A j t), Matrix.mul_apply]
    exact Finset.sum_filter_of_ne fun t _ ht => by
      by_contra! htk
      rcases hij with hi | hj
      · exact ht (by rw [cholesky_apply_of_gt A (hi.trans_le htk), zero_mul])
      · exact ht (by rw [cholesky_apply_of_gt A (hj.trans_le htk), mul_zero])
  have hgram (i j : Fin n) (hij : i < k ∨ j < k) :
      (∑ t : ι, cholesky A i t * cholesky A j t) = A i j := by
    rw [hsum i j hij]
    rcases le_total j i with hji | hij'
    · have hj' : j < k := hij.elim (hji.trans_lt ·) id
      exact cholesky_mul_transpose_apply_of_pos A hji (hspec.2 j hj')
    · have hi' : i < k := hij.elim id (hij'.trans_lt ·)
      rw [show (cholesky A * (cholesky A)ᵀ) i j = (cholesky A * (cholesky A)ᵀ) j i by
        simp [Matrix.mul_apply, mul_comm]]
      exact (cholesky_mul_transpose_apply_of_pos A hij' (hspec.2 i hi')).trans (hA.apply _ _)
  have hB : B + δ • vecMulVec e e = fromRows L C * (fromRows L C)ᵀ := by
    ext (i | i) (j | j)
    · change A i j + δ * (0 * 0) = ∑ t : ι, cholesky A i t * cholesky A j t
      rw [mul_zero, mul_zero, add_zero, hgram _ _ (Or.inl i.2)]
    · cases j
      change A i k + δ * (0 * 1) = ∑ t : ι, cholesky A i t * cholesky A k t
      rw [zero_mul, mul_zero, add_zero, hgram _ _ (Or.inl i.2)]
    · cases i
      change A k j + δ * (1 * 0) = ∑ t : ι, cholesky A k t * cholesky A j t
      rw [mul_zero, mul_zero, add_zero, hgram _ _ (Or.inr j.2)]
    · cases i
      cases j
      change A k k + δ * (1 * 1) = (C * Cᵀ) () ()
      dsimp [δ]
      ring
  have hL : L.IsLowerTriangular := fun i j hij =>
    cholesky_apply_of_gt A (show (i : Fin n) < j from hij)
  exact ⟨hδ, failedCholeskyBackSubst_spec hL (fun i => hspec.2 i i.2) C δ B e rfl hB⟩

/-- **Algorithm 7.3.4** of [conn2000trust], Step 3d, the computed lower bound in the full matrix.
Let $A$ be symmetric, and suppose that the scan returns the failed pivot $k$, with $L$, $c$,
$\delta$ and $v$ as in `ConnGouldToint.Chapter07.choleskyFailedPivot_certificate`. If
$(\lambda + \lambda_{\min}) z^T z \le z^T A z$ for all $z$, then
$$\lambda + \frac{\delta}{v^T v} \le -\lambda_{\min}.$$

Here $A = M + \lambda I$ and $\lambda_{\min}$ is a lower bound on the eigenvalues of $M$. The
bound is the Rayleigh quotient of the zero extension of $v$ to the full matrix. -/
theorem choleskyFailedPivot_lower_bound {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsSymm) {k : Fin n} (hk : firstFailedCholeskyPivot A = some k)
    {lam lamMin : ℝ} (hRayleigh : ∀ z, (lam + lamMin) * (z ⬝ᵥ z) ≤ z ⬝ᵥ A *ᵥ z) :
    let ι := {j : Fin n // j < k}
    let L := (cholesky A).submatrix (Subtype.val : ι → Fin n) (Subtype.val : ι → Fin n)
    let C : Matrix Unit ι ℝ := Matrix.of fun _ j => cholesky A k j
    let δ := (C * Cᵀ) () () - A k k
    let v := failedCholeskyBackSubst L C
    lam + δ / (v ⬝ᵥ v) ≤ -lamMin := by
  let ι := {j : Fin n // j < k}
  let f : ι ⊕ Unit → Fin n := Sum.elim Subtype.val (fun _ => k)
  let L := (cholesky A).submatrix (Subtype.val : ι → Fin n) (Subtype.val : ι → Fin n)
  let C : Matrix Unit ι ℝ := Matrix.of fun _ j => cholesky A k j
  let δ := (C * Cᵀ) () () - A k k
  let v := failedCholeskyBackSubst L C
  have hfinj : Function.Injective f := by
    intro i j h
    rcases i with i | i <;> rcases j with j | j
    · exact congrArg Sum.inl (Subtype.ext h)
    · exact (i.2.ne h).elim
    · exact (j.2.ne h.symm).elim
    · exact congrArg Sum.inr (Subsingleton.elim i j)
  let z := Function.extend f v 0
  have hdot (t : Fin n → ℝ) : v ⬝ᵥ (t ∘ f) = z ⬝ᵥ t := by
    unfold dotProduct
    exact Fintype.sum_of_injective f hfinj _ _ (fun i hi => by
      dsimp only [z]
      rw [Function.extend_apply' _ _ _ (by simpa using hi), Pi.zero_apply, zero_mul])
      (fun j => by dsimp only [Function.comp_apply, z]; rw [hfinj.extend_apply])
  have hz : z ∘ f = v := funext (hfinj.extend_apply v 0)
  have hcomp := Matrix.submatrix_mulVec_eq_comp_mulVec_extend A f hfinj v
  have hcert := choleskyFailedPivot_certificate hA hk
  have hv : v (Sum.inr ()) = 1 := hcert.2.1
  have hq : v ⬝ᵥ (A.submatrix f f) *ᵥ v = -δ := hcert.2.2.2
  have hnorm : 0 < v ⬝ᵥ v := by
    have hs : v (Sum.inr ()) ^ 2 ≤ ∑ i, v i ^ 2 :=
      Finset.single_le_sum (fun i _ => sq_nonneg (v i)) (Finset.mem_univ _)
    rw [hv, one_pow] at hs
    rw [show v ⬝ᵥ v = ∑ i, v i ^ 2 by simp [dotProduct, pow_two]]
    exact zero_lt_one.trans_le hs
  have hr := hRayleigh z
  rw [← hdot z, hz, ← hdot (A *ᵥ z), ← hcomp, hq] at hr
  change lam + δ / (v ⬝ᵥ v) ≤ -lamMin
  have hdiv : δ / (v ⬝ᵥ v) ≤ -(lam + lamMin) := by
    apply (div_le_iff₀ hnorm).2
    nlinarith only [hr]
  linarith

section BoundaryRoot

open Subproblem
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Algorithm 7.3.4** of [conn2000trust], Step 3b(iii), the computed model-minimizing boundary
root. For a step $s$ and a unit direction $u$, let
$$a = \sqrt{\Delta^2 - \|s\|^2 + \langle s, u \rangle^2} - \langle s, u \rangle, \qquad b =
  -\sqrt{\Delta^2 - \|s\|^2 + \langle s, u \rangle^2} - \langle s, u \rangle$$
be the two roots of $\|s + \alpha u\| = \Delta$. The **best boundary coefficient** is $a$ if
$q(s + a u) \le q(s + b u)$, and $b$ otherwise.

**Reading.** The source chooses the root with the smaller model value but does not say which
root to take in a tie. A tie gives the root $a$ with the positive square root.

The root $b$ is written as `-moreSorensenBoundaryCoefficient Δ s (-u)`. -/
noncomputable def moreSorensenBestBoundaryCoefficient (g : E) (H : E →L[ℝ] E)
    (Δ : ℝ) (s u : E) : ℝ :=
  let a := moreSorensenBoundaryCoefficient Δ s u
  let b := -moreSorensenBoundaryCoefficient Δ s (-u)
  if quadModel g H (s + a • u) ≤ quadModel g H (s + b • u) then a else b

/-- **Algorithm 7.3.4** of [conn2000trust], Step 3b(iii), boundary and minimum model value. Let
$\|s\| \le \Delta$ and $\|u\| = 1$, and let $\alpha$ be the best boundary coefficient. Then
$\|s + \alpha u\| = \Delta$, and $q(s + \alpha u) \le q(s + t u)$ for every $t$ with
$\|s + t u\| = \Delta$. -/
theorem moreSorensenBestBoundaryCoefficient_spec (g : E) (H : E →L[ℝ] E)
    {Δ : ℝ} {s u : E} (hs : ‖s‖ ≤ Δ) (hu : ‖u‖ = 1) :
    let α := moreSorensenBestBoundaryCoefficient g H Δ s u
    ‖s + α • u‖ = Δ ∧
      ∀ t : ℝ, ‖s + t • u‖ = Δ → quadModel g H (s + α • u) ≤ quadModel g H (s + t • u) := by
  let a := moreSorensenBoundaryCoefficient Δ s u
  let b := -moreSorensenBoundaryCoefficient Δ s (-u)
  have ha : ‖s + a • u‖ = Δ := norm_add_boundaryCorrection hs hu
  have hb : ‖s + b • u‖ = Δ := by
    simpa only [b, neg_smul, smul_neg] using
      norm_add_boundaryCorrection (u := -u) hs (by simpa using hu)
  have hroots (t : ℝ) (ht : ‖s + t • u‖ = Δ) : t = a ∨ t = b := by
    let c := ⟪s, u⟫
    let d := √(Δ ^ 2 - ‖s‖ ^ 2 + c ^ 2)
    have hd : d ^ 2 = Δ ^ 2 - ‖s‖ ^ 2 + c ^ 2 :=
      Real.sq_sqrt
        (add_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ (norm_nonneg s) hs 2)) (sq_nonneg _))
    have hsq := norm_add_sq_real s (t • u)
    rw [ht, real_inner_smul_right, norm_smul, hu, mul_one, Real.norm_eq_abs, sq_abs] at hsq
    change Δ ^ 2 = ‖s‖ ^ 2 + 2 * (t * c) + t ^ 2 at hsq
    have heq : (t + c)^2 = d^2 := by nlinarith only [hd, hsq]
    have ha' : a = d - c := rfl
    have hb' : b = -d - c := by
      simp only [b, d, c, moreSorensenBoundaryCoefficient, inner_neg_right, neg_sq]
      ring
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp heq with ht' | ht'
    · exact Or.inl (by linarith only [ha', ht'])
    · exact Or.inr (by linarith only [hb', ht'])
  let qa := quadModel g H (s + a • u)
  let qb := quadModel g H (s + b • u)
  change ‖s + (if qa ≤ qb then a else b) • u‖ = Δ ∧
    ∀ t : ℝ, ‖s + t • u‖ = Δ →
      quadModel g H (s + (if qa ≤ qb then a else b) • u) ≤ quadModel g H (s + t • u)
  rcases le_or_gt qa qb with h | h
  · rw [ite_eq_left h]
    refine ⟨ha, fun t ht => ?_⟩
    rcases hroots t ht with rfl | rfl
    · exact le_rfl
    · exact h
  · rw [ite_eq_right h.not_ge]
    refine ⟨hb, fun t ht => ?_⟩
    rcases hroots t ht with rfl | rfl
    · exact h.le
    · exact le_rfl

end BoundaryRoot

section Shifted

open Subproblem WithLp
open scoped RealInnerProductSpace

variable {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}

local notation "Mop" => toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M

private theorem isSymm_shift_of_isSymmetric
    (hM : (Mop : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric)
    (x : ℝ) : (M + x • 1).IsSymm := by
  have hsymm : (toEuclideanLin M).IsSymmetric := by
    simpa only [coe_toEuclideanCLM_eq_toEuclideanLin] using hM
  exact (isHermitian_iff_isSymm.mp (isSymmetric_toEuclideanLin_iff.mp hsymm)).add
    (isSymm_one.smul x)

/-- **Algorithm 7.3.4** of [conn2000trust], Step 1, the computed pivot test and the pole. Let $M$ be
symmetric of order $n \ge 1$ with least eigenvalue $\lambda_1$. For every $x \in \mathbb{R}$,
the Cholesky scan of $M + x I$ finds no failed pivot if and only if $x > -\lambda_1$. -/
theorem shiftedCholesky_succeeds_iff (hn : 0 < n)
    (hM : (Mop : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric)
    (x : ℝ) : firstFailedCholeskyPivot (M + x • 1) = none ↔ -leftmost hM < x := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [firstFailedCholeskyPivot_eq_none_iff (isSymm_shift_of_isSymmetric hM x),
    posDef_iff_isSymmetricCoercive, ← coe_toEuclideanCLM_eq_toEuclideanLin,
    toEuclideanCLM_add_smul_one]
  exact isSymmetricCoercive_add_smul_iff (hH := hM) x

/-- **Algorithm 7.3.4** of [conn2000trust], Steps 3b–d, the computed lower estimate. For a square
matrix $M$ and a trial $x$, let $A = M + x I$ with computed factor $L$. If the scan of $A$ finds
no failed pivot, the estimate is $x - c$, where $c$ is the Rayleigh quotient for $L L^T$ of the
LINPACK back solve $y$. If the scan returns the failed pivot $k$, the estimate is
$x + \delta / v^T v$, with $\delta$ and $v$ as in
`ConnGouldToint.Chapter07.choleskyFailedPivot_certificate`. -/
noncomputable def moreSorensenMatrixLowerEstimate (M : Matrix (Fin n) (Fin n) ℝ)
    (x : ℝ) : ℝ :=
  let A := M + x • 1
  let L := cholesky A
  match firstFailedCholeskyPivot A with
  | none =>
    let y := Lᵀ.backSubst (linpackForwardSubst L)
    x - linpackCurvature (L * Lᵀ) y
  | some k =>
    let ι := {j : Fin n // j < k}
    let L₀ := L.submatrix (Subtype.val : ι → Fin n) (Subtype.val : ι → Fin n)
    let C : Matrix Unit ι ℝ := Matrix.of fun _ j => L k j
    let δ := (C * Cᵀ) () () - A k k
    let v := failedCholeskyBackSubst L₀ C
    x + δ / (v ⬝ᵥ v)

/-- **Algorithm 7.3.4** of [conn2000trust], Steps 3b–d, validity of the computed lower estimate. Let
$M$ be symmetric of order $n \ge 1$ with least eigenvalue $\lambda_1$. For every $x$, the
computed lower estimate is at most $-\lambda_1$. If $x > -\lambda_1$, the estimate is exactly
$x - c$, where $c$ is the Rayleigh quotient of the LINPACK back solve for $M + x I$. -/
theorem moreSorensenMatrixLowerEstimate_spec (hn : 0 < n)
    (hM : (Mop : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric)
    (x : ℝ) :
    moreSorensenMatrixLowerEstimate M x ≤ -leftmost hM ∧
      (-leftmost hM < x →
        let L := cholesky (M + x • 1)
        let y := Lᵀ.backSubst (linpackForwardSubst L)
        moreSorensenMatrixLowerEstimate M x = x - linpackCurvature (L * Lᵀ) y) := by
  have hA := isSymm_shift_of_isSymmetric hM x
  have htest := shiftedCholesky_succeeds_iff hn hM x
  cases hp : firstFailedCholeskyPivot (M + x • 1) with
  | none =>
    obtain ⟨hf, _, _, hw, hy, hv⟩ := cholesky_linpack_certificate hA hp
    unfold moreSorensenMatrixLowerEstimate
    dsimp only
    rw [hp]
    exact ⟨linpackEuclidean_lower_bound hn hM hf hw hy hv, fun _ => rfl⟩
  | some k =>
    have hR (z : Fin n → ℝ) : (x + leftmost hM) * (z ⬝ᵥ z) ≤ z ⬝ᵥ (M + x • 1) *ᵥ z := by
      have hr := add_leftmost_mul_norm_sq_le (H := Mop) (hH := hM) x (toLp 2 z)
      rw [real_inner_comm, ← toEuclideanCLM_add_smul_one, toEuclideanCLM_toLp,
        EuclideanSpace.inner_toLp_toLp_real, ← real_inner_self_eq_norm_sq,
        EuclideanSpace.inner_toLp_toLp_real] at hr
      exact hr
    refine ⟨?_, fun hx => ?_⟩
    · unfold moreSorensenMatrixLowerEstimate
      dsimp only
      rw [hp]
      exact choleskyFailedPivot_lower_bound hA hp hR
    · have hnone := htest.mpr hx
      rw [hp] at hnone
      cases hnone

/-- **Algorithm 7.3.4** of [conn2000trust], the computed multiplier orbit. Starting from a triple
(lower end, upper end, trial), each state is obtained by
`ConnGouldToint.Chapter07.moreSorensenSafeguardedStepBy` with the Cholesky scan as the test of
positive definiteness and with the computed lower estimate at the current trial.

The orbit does not need the pole $-\lambda_1$ as an input. -/
noncomputable def moreSorensenMatrixIterates (M : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (Δ θ : ℝ) (initial : ℝ × ℝ × ℝ) :
    ℕ → ℝ × ℝ × ℝ
  | 0 => initial
  | k + 1 =>
    let state := moreSorensenMatrixIterates M g Δ θ initial k
    moreSorensenSafeguardedStepBy g (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M)
      (fun t => firstFailedCholeskyPivot (M + t • 1) = none) Δ θ
      state.1 state.2.1 state.2.2 (moreSorensenMatrixLowerEstimate M state.2.2)

/-- **Algorithm 7.3.4** of [conn2000trust], agreement of the computed recurrence with the spectral
one. Let $M$ be symmetric of order $n \ge 1$ with least eigenvalue $\lambda_1$. Each step of the
computed orbit equals the update `ConnGouldToint.Chapter07.moreSorensenSafeguardedStep` with the
pole $-\lambda_1$ and the computed lower estimate at the current trial. -/
theorem moreSorensenMatrixIterates_succ (hn : 0 < n)
    (hM : (Mop : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric)
    (g : EuclideanSpace ℝ (Fin n)) (Δ θ : ℝ) (initial : ℝ × ℝ × ℝ) (k : ℕ) :
    let state := moreSorensenMatrixIterates M g Δ θ initial k
    moreSorensenMatrixIterates M g Δ θ initial (k + 1) =
      moreSorensenSafeguardedStep g Mop (-leftmost hM) Δ θ
        state.1 state.2.1 state.2.2 (moreSorensenMatrixLowerEstimate M state.2.2) := by
  rw [moreSorensenMatrixIterates]
  simp only [moreSorensenSafeguardedStep, moreSorensenSafeguardedStepBy,
    shiftedCholesky_succeeds_iff hn hM]

/-- **Algorithm 7.3.4** of [conn2000trust], Step 1a, the step by triangular solves. Let $M$ be
symmetric of order $n \ge 1$ with least eigenvalue $\lambda_1$, and let $x > -\lambda_1$. If $L$
is the computed Cholesky factor of $M + x I$, then
$$s(x) = L^{-T} \bigl(L^{-1} (-g)\bigr),$$
computed by forward and backward substitution. -/
theorem shiftedStep_eq_cholesky_subst (hn : 0 < n)
    (hM : (Mop : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric)
    (g : EuclideanSpace ℝ (Fin n)) {x : ℝ} (hx : -leftmost hM < x) :
    let L := cholesky (M + x • 1)
    shiftedStep g Mop x = toLp 2 (Lᵀ.backSubst (L.forwardSubst (-ofLp g))) := by
  have hs := firstFailedCholeskyPivot_spec (isSymm_shift_of_isSymmetric hM x)
  rw [(shiftedCholesky_succeeds_iff hn hM x).mpr hx] at hs
  obtain ⟨hL, hd, hfact⟩ := hs
  let L := cholesky (M + x • 1)
  let w := L.forwardSubst (-ofLp g)
  let y := Lᵀ.backSubst w
  have hw : L *ᵥ w = -ofLp g := Matrix.mulVec_forwardSubst _ hL (fun i => (hd i).ne')
  have hy : Lᵀ *ᵥ y = w := Matrix.mulVec_backSubst _ (fun _ _ hij => hL hij)
    (fun i => (hd i).ne')
  have hsol : (Mop + x • 1) (toLp 2 y) = -g := by
    rw [← toEuclideanCLM_add_smul_one, toEuclideanCLM_toLp, ← hfact,
      ← Matrix.mulVec_mulVec, hy, hw, WithLp.toLp_neg, WithLp.toLp_ofLp]
  exact ((step_spec (H := Mop) (hH := hM) hx).2 _ hsol).symm

/-- **Theorem 7.3.4** of [conn2000trust], the hard case with computed Cholesky and LINPACK data. Let
$M$ be symmetric of order $n \ge 1$ with least eigenvalue $\lambda_1$, $g \neq 0$, $\Delta > 0$
and $\theta \in (0, 1)$. Suppose that $-\lambda_1$ is an optimal multiplier for a global
minimizer $s_M$ with $\|s_M\| \le \Delta$ (the hard case). Let the initial triple satisfy
$0 \le \lambda^L_0 \le -\lambda_1 < \lambda^U_0$ and $\lambda_0 \in [\lambda^L_0, \lambda^U_0]$,
and let $\lambda_k$ be the trials of the computed orbit. Then $\lambda_k \to -\lambda_1$, there
are infinitely many $k$ with $\lambda_k > -\lambda_1$, and along every sequence $k_j \to \infty$
of such indices the corrected steps
$$s_j = s(\lambda_{k_j}) + \alpha_j u_j$$
satisfy $q(s_j) \to q(s_M)$, and every limit of a subsequence of $(s_j)$ lies in the ball and is
a global minimizer of $q$ there. Here $u_j$ is the normalized LINPACK direction for
$M + \lambda_{k_j} I$ and $\alpha_j$ is the best boundary coefficient.

All multiplier and curvature certificates come from the matrix $M$. -/
theorem moreSorensen_computed_hard_matrix_run (hn : 0 < n)
    (hM : (Mop : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric)
    {g sM : EuclideanSpace ℝ (Fin n)} (hg : g ≠ 0)
    {Δ θ : ℝ} {initial : ℝ × ℝ × ℝ}
    (hΔ : 0 < Δ) (hθ : θ ∈ Set.Ioo 0 1)
    (hsM : ‖sM‖ ≤ Δ) (hmul : IsTrustRegionMultiplier g Mop Δ sM (-leftmost hM))
    (hlo : 0 ≤ initial.1) (hlr : initial.1 ≤ -leftmost hM)
    (hhi : -leftmost hM < initial.2.1)
    (hx0 : initial.2.2 ∈ Set.Icc initial.1 initial.2.1) :
    let x := fun k => (moreSorensenMatrixIterates M g Δ θ initial k).2.2
    Filter.Tendsto x Filter.atTop (nhds (-leftmost hM)) ∧
      (∃ j : ℕ → ℕ, Filter.Tendsto j Filter.atTop Filter.atTop ∧
        ∀ k, -leftmost hM < x (j k)) ∧
      ∀ (j : ℕ → ℕ), Filter.Tendsto j Filter.atTop Filter.atTop →
        (∀ k, -leftmost hM < x (j k)) →
        let s := fun k =>
          let L := cholesky (M + x (j k) • 1)
          let y := Lᵀ.backSubst (linpackForwardSubst L)
          let s := shiftedStep g Mop (x (j k))
          let u := linpackEuclideanDirection y
          s + moreSorensenBestBoundaryCoefficient g Mop Δ s u • u
        Filter.Tendsto (fun k => quadModel g Mop (s k)) Filter.atTop
          (nhds (quadModel g Mop sM)) ∧
        ∀ (l : ℕ → ℕ) (z : EuclideanSpace ℝ (Fin n)), Filter.Tendsto l Filter.atTop Filter.atTop →
          Filter.Tendsto (s ∘ l) Filter.atTop (nhds z) →
          z ∈ Metric.closedBall 0 Δ ∧ IsMinOn (quadModel g Mop) (Metric.closedBall 0 Δ) z := by
  let states := moreSorensenMatrixIterates M g Δ θ initial
  let lo := fun k => (states k).1
  let hi := fun k => (states k).2.1
  let x := fun k => (states k).2.2
  let b := fun k => moreSorensenMatrixLowerEstimate M (x k)
  let L := fun k => cholesky (M + x k • 1)
  let w := fun k => linpackForwardSubst (L k)
  let v := fun k i => linpackSign (∑ j ∈ Finset.univ.filter (· < i), L k i j * w k j)
  let y := fun k => (L k)ᵀ.backSubst (w k)
  let α := fun k => moreSorensenBestBoundaryCoefficient g Mop Δ
    (shiftedStep g Mop (x k)) (linpackEuclideanDirection (y k))
  have hb (k : ℕ) := moreSorensenMatrixLowerEstimate_spec hn hM (x k)
  have hcert (k : ℕ) (hk : -leftmost hM < x k) :
      L k * (L k)ᵀ = M + x k • 1 ∧ (L k).IsLowerTriangular ∧ (∀ i, 0 < L k i i) ∧
      L k *ᵥ w k = v k ∧ (L k)ᵀ *ᵥ y k = w k ∧
      ∀ i, v k i = linpackSign (v k i - L k i i * w k i) :=
    cholesky_linpack_certificate (isSymm_shift_of_isSymmetric hM (x k))
      ((shiftedCholesky_succeeds_iff hn hM (x k)).mpr hk)
  have hboundary (k : ℕ) (hk : -leftmost hM < x k) :
      ‖shiftedStep g Mop (x k) + α k • linpackEuclideanDirection (y k)‖ = Δ := by
    have hs := (secular_lt_norm_sq_of_shifted (H := Mop) (hH := hM) hg le_rfl hmul.shifted hk).le
    have hraw : ‖shiftedStep g Mop (x k)‖ ≤ Δ :=
      (pow_le_pow_iff_left₀ (norm_nonneg _) hΔ.le two_ne_zero).mp
        (hs.trans (pow_le_pow_left₀ (norm_nonneg sM) hsM 2))
    obtain ⟨_, _, _, hw, hy, hv⟩ := hcert k hk
    have hunit := (linpackEuclideanDirection_spec hn hw hy hv).1
    exact (moreSorensenBestBoundaryCoefficient_spec g Mop hraw hunit).1
  have hrec (k : ℕ) : (lo (k + 1), hi (k + 1), x (k + 1)) =
      moreSorensenSafeguardedStep g Mop (-leftmost hM) Δ θ (lo k) (hi k) (x k) (b k) :=
    moreSorensenMatrixIterates_succ hn hM g Δ θ initial k
  have hrun := moreSorensen_hard_matrix_run hn hM hg (L := L) (v := v) (w := w) (y := y) (α := α)
    hΔ hθ hsM hmul hlo hlr hhi hx0 (fun k _ => (hb k).1) (fun k => (hb k).2)
    hrec hcert hboundary
  exact ⟨hrun.1, hrun.2.1, fun j hj hjpos => ⟨(hrun.2.2 j hj hjpos).1, (hrun.2.2 j hj hjpos).2.1⟩⟩

end Shifted

end ConnGouldToint.Chapter07

/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.NumberTheory.Real.Irrational
import Numlib.Approximation.Quadrature
import Numlib.Krylov.JacobiReconstruction
import Numlib.LinearAlgebra.Matrix.Complexify

/-!
# Jacobi matrices

The eigenvalues of a real symmetric tridiagonal matrix with positive subdiagonal are simple.
If a unit eigenvector of a leading principal submatrix has small last component, extending the
vector by zeros gives a nearby eigenvalue of the full matrix. These results are from §3.4 of
[liesen2013krylov].

## Main definitions

* `LiesenStrakos.Chapter03.IsStabilisedJacobiEigenvalue` specifies when a larger Jacobi matrix
  has an eigenvalue within the residual tolerance of a prescribed leading-block eigenpair.
* `LiesenStrakos.Chapter03.HasJacobiSpectralData` specifies Jacobi eigenvalues and the first
  components of corresponding orthonormal eigenvectors.

## Main results

* `LiesenStrakos.Chapter03.corollary_3_4_2` proves orthonormality for the discrete pairing.
* `LiesenStrakos.Chapter03.theorem_3_4_1` identifies the Gauss–Christoffel nodes and weights
  with the Jacobi eigenvalues and squared first eigenvector components.
* `LiesenStrakos.Chapter03.theorem_3_4_3` proves simplicity and nonzero first components.
* `LiesenStrakos.Chapter03.remark_3_4_4_consecutive` gives strict interlacing between a
  Jacobi matrix and its penultimate leading block.
* `LiesenStrakos.Chapter03.remark_3_4_4_interior` finds an eigenvalue of a Jacobi matrix
  between any two distinct eigenvalues of a strict leading block.
* `LiesenStrakos.Chapter03.remark_3_4_4_exterior` places the extreme eigenvalues strictly
  outside the eigenvalues of every smaller leading block.
* `LiesenStrakos.Chapter03.remark_3_4_4_charpoly` describes the leading-block characteristic
  polynomials as normalized Lanczos polynomials.
* `LiesenStrakos.Chapter03.remark_3_4_4_eigenvector` gives each normalized eigenvector with
  positive first coordinate by evaluating orthonormal polynomials at its eigenvalue.
* `LiesenStrakos.Chapter03.proposition_3_4_5` reconstructs a Jacobi matrix from its spectral data.
* `LiesenStrakos.Chapter03.theorem_3_4_6_irrational_offDiagonal` exhibits rational spectral
  data whose Jacobi matrix has an irrational subdiagonal entry.
* `LiesenStrakos.Chapter03.theorem_3_4_6_gauss_counterexample` realizes those data as a
  Gauss–Christoffel rule for a measure with three support points.
* `LiesenStrakos.Chapter03.proposition_3_4_7` realizes an orthonormal basis as a Lanczos
  basis with prescribed distinct eigenvalues.
* `LiesenStrakos.Chapter03.proposition_3_4_8` gives the leading-block eigenvalues as weighted
  averages of the full eigenvalues.
* `LiesenStrakos.Chapter03.theorem_3_4_9` bounds the distance from a leading-block Ritz value
  to the full spectrum.
* `LiesenStrakos.Chapter03.theorem_3_4_11` expresses leading-block quadrature weights through
  the full spectral quadrature.
* `LiesenStrakos.Chapter03.theorem_3_4_12` gives a lower bound on the stabilisation tolerance
  when the penultimate block has midpoint eigenvalues.

## Deviations from the source

* **Theorem 3.4.11** (correction). The weight identities evaluate a polynomial quotient, giving
  the removable value at a shared eigenvalue.
* **Theorem 3.4.6** (counterexample). The printed arithmetic restriction is false for the
  off-diagonal entries themselves. Already at order two, addition, multiplication and
  division of rational inputs and constants cannot recover the off-diagonal entry exactly.
* **Proposition 3.4.8** (generalization). The formula applies to real orthogonal
  diagonalizations of any matrix and its leading block.
* **Definition 3.4.10** (reading). The second clause is read as the distance criterion for
  stabilisation.
* **Theorem 3.4.11** (reading). A quotient at a shared spectral node is evaluated as a
  polynomial.

## Not formalized

* **Theorem 3.4.6.** The inverse Jacobi algorithm with square roots for the final
  off-diagonal entries, its operation count and its stability bounds are pending.
-/

open Matrix MeasureTheory OrthogonalPolynomial Polynomial
open scoped Polynomial ComplexOrder ENNReal

namespace LiesenStrakos.Chapter03

/-- **Corollary 3.4.2** of [liesen2013krylov]. The discrete Gauss pairing is positive
definite on polynomials of degree less than $n$, and the first $n$ orthonormal polynomials for
the original measure stay orthonormal for this pairing.

**Generalization.** Any positive exact rule with the stated polynomial integrability and norms
gives orthonormality. -/
theorem corollary_3_4_2 {μ : Measure ℝ}
    (hint : ∀ p : ℝ[X], Integrable (fun t => p.eval t) μ) {n : ℕ}
    (hnorm : ∀ k < n, 0 < normSq μ k) {x w : Fin n → ℝ}
    (hx : Function.Injective x) (hpos : ∀ i, 0 < w i)
    (h : Quadrature.IsExactOnMeasure μ w x (2 * n - 1)) :
    (∀ p : ℝ[X], p ≠ 0 → p.degree < n → 0 < Quadrature.discreteInner w x p.eval p.eval) ∧
    ∀ i j : Fin n, Quadrature.discreteInner w x (orthonormalFamily μ i).eval
      (orthonormalFamily μ j).eval = if i = j then 1 else 0 := by
  refine ⟨fun _ hp hdeg => Quadrature.discreteInner_self_pos hpos hx hp hdeg, ?_⟩
  intro i j
  have hdeg : (orthonormalFamily μ i).degree + (orthonormalFamily μ j).degree ≤
      ((2 * n - 1 : ℕ) : WithBot ℕ) := by
    rw [degree_orthonormalFamily_of_normSq_pos (hnorm _ i.isLt),
      degree_orthonormalFamily_of_normSq_pos (hnorm _ j.isLt)]
    exact_mod_cast (show i.val + j.val ≤ 2 * n - 1 by omega)
  rw [Quadrature.discreteInner_eq_integral_of_degree_le h hdeg]
  exact integral_orthonormalFamily_mul_of_normSq_pos hint hnorm i j

/-- **Theorem 3.4.3** of [liesen2013krylov]. The real eigenvalues of a Jacobi matrix are
pairwise distinct and every nonzero eigenvector has nonzero first component. -/
theorem theorem_3_4_3 {n : ℕ} {T : Matrix (Fin n) (Fin n) ℝ} (hT : T.IsJacobiMatrix)
    (hn : 0 < n) :
    Function.Injective hT.isHermitian.eigenvalues ∧
      ∀ (θ : ℝ) (z : Fin n → ℝ), z ≠ 0 → T.mulVec z = θ • z → z ⟨0, hn⟩ ≠ 0 :=
  ⟨hT.eigenvalues_injective, fun _ _ hz hθ => hT.first_ne_zero hn hz hθ⟩

/-- **Remark 3.4.4, consecutive interlacing** of [liesen2013krylov]. The eigenvalues of a
Jacobi matrix of order $n+1$ and its leading principal matrix of order $n$ strictly
interlace. The eigenvalues are ordered from largest to smallest. -/
theorem remark_3_4_4_consecutive {n : ℕ} {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hT : T.IsJacobiMatrix) :
    let hS := (hT.leadingBlock (Nat.le_succ n)).isHermitian
    ∀ j : Fin n,
      hT.isHermitian.eigenvalues₀ ⟨j.val + 1, by simp⟩ < hS.eigenvalues₀ ⟨j, by simp⟩ ∧
      hS.eigenvalues₀ ⟨j, by simp⟩ < hT.isHermitian.eigenvalues₀ ⟨j, by simp⟩ := by
  obtain ⟨d, b, h, hb⟩ := hT.exists_symmTridiagonalOf
  subst T
  let hS := (hT.leadingBlock (Nat.le_succ n)).isHermitian
  change ∀ j : Fin n,
    hT.isHermitian.eigenvalues₀ ⟨j.val + 1, by simp⟩ < hS.eigenvalues₀ ⟨j, by simp⟩ ∧
    hS.eigenvalues₀ ⟨j, by simp⟩ < hT.isHermitian.eigenvalues₀ ⟨j, by simp⟩
  intro j
  have hbne : Sturm.IsUnreduced b (n + 1) := fun k hk => (hb k hk).ne'
  have h := Sturm.eigenvalues_strictInterlace d b n hbne hT.isHermitian
    (Matrix.isHermitian_symmTridiagonalOf d b n) j
  exact h

/-- **Remark 3.4.4, nonconsecutive interior gaps** of [liesen2013krylov]. Every open gap
between distinct eigenvalues of a strict leading block of a Jacobi matrix contains a
full-matrix eigenvalue. -/
theorem remark_3_4_4_interior {m n : ℕ} {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hT : T.IsJacobiMatrix) (hm : m + 1 < n + 1) (i j : Fin (m + 1))
    (hij : (hT.leadingBlock hm.le).isHermitian.eigenvalues i <
      (hT.leadingBlock hm.le).isHermitian.eigenvalues j) :
    ∃ k, (hT.leadingBlock hm.le).isHermitian.eigenvalues i < hT.isHermitian.eigenvalues k ∧
      hT.isHermitian.eigenvalues k < (hT.leadingBlock hm.le).isHermitian.eigenvalues j :=
  hT.exists_eigenvalue_between_leading hm i j hij

/-- **Remark 3.4.4, nonconsecutive exterior gaps** of [liesen2013krylov]. The smallest
and largest eigenvalues of a Jacobi matrix strictly bound the spectrum of every smaller
leading block. -/
theorem remark_3_4_4_exterior {m n : ℕ} {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hT : T.IsJacobiMatrix) (hm : m + 1 < n + 1) (i : Fin (m + 1)) :
    let hS := (hT.leadingBlock hm.le).isHermitian
    hT.isHermitian.sortedEigenvalues (Fin.last n) < hS.sortedEigenvalues i ∧
      hS.sortedEigenvalues i < hT.isHermitian.sortedEigenvalues 0 := by
  let r : m + 2 ≤ n + 1 := hm
  let hS := (hT.leadingBlock hm.le).isHermitian
  let hP := hT.leadingBlock r
  let hPh := hP.isHermitian
  change hT.isHermitian.sortedEigenvalues (Fin.last n) < hS.sortedEigenvalues i ∧
    hS.sortedEigenvalues i < hT.isHermitian.sortedEigenvalues 0
  have hstrict (j : Fin (m + 1)) :
      hPh.sortedEigenvalues j.succ < hS.sortedEigenvalues j ∧
        hS.sortedEigenvalues j < hPh.sortedEigenvalues j.castSucc :=
    remark_3_4_4_consecutive hP j
  let lo : Fin (Fintype.card (Fin (m + 2))) :=
    Fin.cast (Fintype.card_fin _).symm (Fin.last (m + 1))
  let hi : Fin (Fintype.card (Fin (m + 2))) :=
    Fin.cast (Fintype.card_fin _).symm 0
  have hl := hT.isHermitian.eigenvalues₀_submatrix_interlace (Fin.castLE_injective r) hPh lo
  have hu := hT.isHermitian.eigenvalues₀_submatrix_interlace (Fin.castLE_injective r) hPh hi
  have hlo : hT.isHermitian.sortedEigenvalues (Fin.last n) ≤
      hPh.sortedEigenvalues (Fin.last (m + 1)) := by
    have he : (⟨lo.val + (Fintype.card (Fin (n + 1)) - Fintype.card (Fin (m + 2))), by
        simp only [Fintype.card_fin]
        change (m + 1) + (n + 1 - (m + 2)) < n + 1
        omega⟩ : Fin (Fintype.card (Fin (n + 1)))) =
      Fin.cast (Fintype.card_fin _).symm (Fin.last n) := by
      apply Fin.ext
      simp [lo]
      omega
    change hT.isHermitian.eigenvalues₀ (Fin.cast (Fintype.card_fin _).symm (Fin.last n)) ≤
      hPh.eigenvalues₀ lo
    rw [← he]
    exact hl.1
  have hhi : hPh.sortedEigenvalues 0 ≤ hT.isHermitian.sortedEigenvalues 0 := hu.2
  have hlS := hS.sortedEigenvalues_antitone (Fin.le_last i)
  have hSu := hS.sortedEigenvalues_antitone (Fin.zero_le i)
  exact ⟨hlo.trans_lt ((hstrict (Fin.last m)).1.trans_le hlS),
    hSu.trans_lt ((hstrict 0).2.trans_le hhi)⟩

/-- **Remark 3.4.4, polynomials** of [liesen2013krylov]. The leading-block characteristic
polynomials are the monic versions of the Lanczos polynomials for the full matrix from its
first coordinate vector. These Lanczos polynomials are orthonormal in the pairing
$\langle p(T)e_1,q(T)e_1\rangle$. -/
theorem remark_3_4_4_charpoly {n : ℕ} {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hT : T.IsJacobiMatrix) :
    let v := EuclideanSpace.basisFun (Fin (n + 1)) ℝ 0
    let A := T.toEuclideanLin
    (∀ m (hm : m < n + 1), ∃ c > 0,
      (T.submatrix (Fin.castLE hm.le) (Fin.castLE hm.le)).charpoly = C c * Lanczos.poly A v m) ∧
    ∀ i j : Fin (n + 1),
      Krylov.polyInner A v (Lanczos.poly A v i) (Lanczos.poly A v j) = if i = j then 1 else 0 := by
  let v := EuclideanSpace.basisFun (Fin (n + 1)) ℝ 0
  let A := T.toEuclideanLin
  have hA : A.IsSymmetric := isSymmetric_toEuclideanLin_iff.2 hT.isHermitian
  have hg : Krylov.grade A v = n + 1 := hT.grade_basisFun
  refine ⟨fun _ hm => hT.leadingBlock_charpoly_eq_C_mul_lanczosPoly hm, ?_⟩
  intro i j
  have hi : i.val < Krylov.grade A v := by rw [hg]; exact i.isLt
  have hj : j.val < Krylov.grade A v := by rw [hg]; exact j.isLt
  simpa only [Fin.val_inj] using Lanczos.polyInner_poly hA v hi hj

/-- **Remark 3.4.4, eigenvectors** of [liesen2013krylov]. The normalized eigenvector whose
first coordinate is positive is the vector of orthonormal polynomial evaluations divided
by its Euclidean norm. Its last coordinate is nonzero. -/
theorem remark_3_4_4_eigenvector {n : ℕ} {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hT : T.IsJacobiMatrix) {θ : ℝ} {z : EuclideanSpace ℝ (Fin (n + 1))}
    (hz : ‖z‖ = 1) (hpos : 0 < z 0) (heig : T.toEuclideanLin z = θ • z) :
    let v := EuclideanSpace.basisFun (Fin (n + 1)) ℝ 0
    let Φ : EuclideanSpace ℝ (Fin (n + 1)) :=
      WithLp.toLp 2 fun i => (Lanczos.poly T.toEuclideanLin v i).eval θ
    z = ‖Φ‖⁻¹ • Φ ∧ z (Fin.last n) ≠ 0 := by
  let v := EuclideanSpace.basisFun (Fin (n + 1)) ℝ 0
  let Φ : EuclideanSpace ℝ (Fin (n + 1)) :=
    WithLp.toLp 2 fun i => (Lanczos.poly T.toEuclideanLin v i).eval θ
  change z = ‖Φ‖⁻¹ • Φ ∧ z (Fin.last n) ≠ 0
  have hΦ : z = (z 0) • Φ := by
    apply WithLp.ofLp_injective 2
    funext i
    exact hT.eigenvector_apply_eq_first_mul_eval_lanczosPoly heig i
  have hc : z 0 * ‖Φ‖ = 1 := by
    have h := congrArg norm hΦ
    simpa only [hz, norm_smul, Real.norm_eq_abs, abs_of_pos hpos] using h.symm
  have hz' : z.ofLp ≠ 0 := by
    intro h
    have h0 : z 0 = 0 := congrFun h 0
    exact hpos.ne' h0
  have heig' : T.mulVec z.ofLp = θ • z.ofLp := by
    have h := congrArg (WithLp.ofLp (p := 2)) heig
    rwa [ofLp_toEuclideanLin, WithLp.ofLp_smul] at h
  exact ⟨hΦ.trans (congrArg (fun c : ℝ => c • Φ) (eq_inv_of_mul_eq_one_left hc)),
    hT.last_ne_zero hz' heig'⟩

/-- A Jacobi matrix has spectral data $(\theta,\zeta)$ when it has an orthonormal basis of
eigenvectors of eigenvalues $\theta_i$ whose first coordinates are $\zeta_i$. -/
def HasJacobiSpectralData {n : ℕ} (T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (θ ζ : Fin (n + 1) → ℝ) : Prop :=
  T.IsJacobiMatrix ∧ ∃ Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
    Zᵀ * Z = 1 ∧ T * Z = Z * diagonal θ ∧ ∀ i, Z 0 i = ζ i

/-- **Theorem 3.4.1** of [liesen2013krylov]. For a compactly supported probability measure with
more than $n+1$ support points, the $n+1$ Gauss–Christoffel nodes are the roots of the
orthonormal polynomial of degree $n+1$ and lie in the open interval carrying the measure.
They are also the eigenvalues of the Jacobi matrix. An orthonormal eigenbasis can be chosen
with first components equal to the positive square roots of the Gauss weights.

**Generalization.** The theorem starts from arbitrary distinct exact nodes and allows the
measure to charge the left endpoint. -/
theorem theorem_3_4_1 {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {a b : ℝ} (hsupp : μ (Set.Icc a b)ᶜ = 0) {n : ℕ}
    (hcard : ∀ s : Finset ℝ, s.card ≤ n + 1 → μ (↑s : Set ℝ)ᶜ ≠ 0)
    {x w : Fin (n + 1) → ℝ}
    (hx : Function.Injective x) (hexact : Quadrature.IsExactOnMeasure μ w x (2 * n + 1)) :
    HasJacobiSpectralData (jacobiMatrix μ (n + 1)) x (fun i => √(w i)) ∧
      ∀ i, 0 < w i ∧ x i ∈ Set.Ioo a b ∧ (orthonormalFamily μ (n + 1)).eval (x i) = 0 := by
  let hint := integrable_eval_of_measure_compl_Icc_eq_zero hsupp
  have hnorm (k : ℕ) (hk : k < n + 1) : 0 < normSq μ k :=
    integral_eval_sq_pos_of_degree_le hint hcard (family_ne_zero μ k)
      (by rw [degree_family]; exact_mod_cast hk.le)
  have hpos (i : Fin (n + 1)) : 0 < w i := by
    let l := Lagrange.basis Finset.univ x i
    have hdeg : l.natDegree = n := by
      rw [show l = Lagrange.basis Finset.univ x i from rfl,
        Lagrange.natDegree_basis hx.injOn (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      simp
    have hℓ : 0 < ∫ t, l.eval t ^ 2 ∂μ :=
      integral_eval_sq_pos_of_degree_le hint hcard
        (Lagrange.basis_ne_zero hx.injOn (Finset.mem_univ i))
        (degree_le_of_natDegree_le (by rw [hdeg]; omega))
    have hℓdeg : (l ^ 2).degree ≤ (2 * n + 1 : ℕ) :=
      degree_le_of_natDegree_le (by rw [natDegree_pow, hdeg]; omega)
    have he := hexact (l ^ 2) hℓdeg
    simp only [eval_pow] at he
    rw [← he] at hℓ
    rw [Finset.sum_eq_single i] at hℓ
    · have h : l.eval (x i) = 1 := Lagrange.eval_basis_self hx.injOn (Finset.mem_univ i)
      simpa [h] using hℓ
    · intro j _ hj
      have h : l.eval (x j) = 0 := Lagrange.eval_basis_of_ne hj.symm (Finset.mem_univ j)
      rw [h]
      simp
    · simp
  have hn := ((Quadrature.isExactOnMeasure_two_mul_add_one_iff_of_card_lt hint
    (fun s hs => hcard s hs.le) hx w).1 hexact).1
  have hroot (i : Fin (n + 1)) : (family μ (n + 1)).eval (x i) = 0 := by
    rw [← hn]
    exact Lagrange.eval_nodal_at_node (Finset.mem_univ i)
  have hφ0 (t : ℝ) : (orthonormalFamily μ 0).eval t = 1 := by
    have h0 : normSq μ 0 = 1 := by simp [normSq, family_zero]
    simp [eval_orthonormalFamily, normOf, h0, family_zero]
  let Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    fun i j => √(w j) * (orthonormalFamily μ i).eval (x j)
  have hdiscrete := (corollary_3_4_2 hint hnorm hx hpos (by
    rwa [show 2 * (n + 1) - 1 = 2 * n + 1 by omega])).2
  have hZZ : Z * Zᵀ = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    calc
      (∑ k, Z i k * Zᵀ k j) =
          Quadrature.discreteInner w x (orthonormalFamily μ i).eval
            (orthonormalFamily μ j).eval := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [transpose_apply]
        change (√(w k) * (orthonormalFamily μ i).eval (x k)) *
          (√(w k) * (orthonormalFamily μ j).eval (x k)) = _
        conv_rhs => rw [← Real.sq_sqrt (hpos k).le]
        ring
      _ = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i j := by
        rw [hdiscrete, Matrix.one_apply]
  have hZ : Zᵀ * Z = 1 := mul_eq_one_comm.1 hZZ
  have hdiag : jacobiMatrix μ (n + 1) = Z * diagonal x * Zᵀ := by
    ext i j
    let p := X * orthonormalFamily μ i * orthonormalFamily μ j
    have hp : p.degree ≤ (2 * n + 1 : ℕ) := by
      change (X * orthonormalFamily μ i * orthonormalFamily μ j).degree ≤ _
      rw [degree_mul, degree_mul, degree_X,
        degree_orthonormalFamily_of_normSq_pos (hnorm _ i.isLt),
        degree_orthonormalFamily_of_normSq_pos (hnorm _ j.isLt)]
      exact_mod_cast (show 1 + i.val + j.val ≤ 2 * n + 1 by omega)
    calc jacobiMatrix μ (n + 1) i j =
        ∫ t, t * (orthonormalFamily μ i).eval t * (orthonormalFamily μ j).eval t ∂μ :=
      jacobiMatrix_apply_eq_integral hint hnorm i j
    _ = ∫ t, p.eval t ∂μ := by simp only [p, eval_mul, eval_X]
    _ = ∑ k, w k * p.eval (x k) := (hexact p hp).symm
    _ = (Z * diagonal x * Zᵀ) i j := by
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_diagonal, transpose_apply]
      simp only [p, Z, eval_mul, eval_X]
      conv_lhs => rw [← Real.sq_sqrt (hpos k).le]
      ring
  refine ⟨⟨isJacobiMatrix_jacobiMatrix hnorm, Z, hZ, ?_, ?_⟩, ?_⟩
  · rw [hdiag, Matrix.mul_assoc (Z * diagonal x), hZ, mul_one]
  · intro i
    change √(w i) * (orthonormalFamily μ 0).eval (x i) = _
    rw [hφ0, mul_one]
  · intro i
    refine ⟨hpos i, root_family_mem_Ioo_of_measure_compl_ne_zero hsupp hcard (hroot i), ?_⟩
    rw [eval_orthonormalFamily, hroot, mul_zero]

/-- **Proposition 3.4.5, construction** of [liesen2013krylov]. Apply Lanczos to the diagonal
matrix of the prescribed distinct eigenvalues, starting from the unit vector of prescribed
nonzero first eigenvector coordinates. The full Lanczos matrix has those spectral data. -/
theorem proposition_3_4_5_lanczos {n : ℕ} {θ ζ : Fin (n + 1) → ℝ}
    (hθ : StrictMono θ) (hζ : ∀ i, ζ i ≠ 0)
    (hnorm : ∑ i, ζ i ^ 2 = 1) :
    HasJacobiSpectralData
      (Lanczos.tridiag (diagonal θ).toEuclideanLin (WithLp.toLp 2 ζ) (n + 1)) θ ζ := by
  have hu : ‖(WithLp.toLp 2 ζ : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
    apply (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1
    rw [EuclideanSpace.real_norm_sq_eq, one_pow]
    exact hnorm
  obtain ⟨hT, Z, hZ, hTZ, hfirst⟩ := Lanczos.tridiag_diagonal_spectralData hθ.injective hζ
  exact ⟨hT, Z, hZ, hTZ, fun i => by simpa [hu] using hfirst i⟩

/-- **Proposition 3.4.5, uniqueness** of [liesen2013krylov]. Distinct increasing eigenvalues
and a unit vector of nonzero first eigenvector coordinates determine exactly one Jacobi matrix. -/
theorem proposition_3_4_5 {n : ℕ} {θ ζ : Fin (n + 1) → ℝ}
    (hθ : StrictMono θ) (hζ : ∀ i, ζ i ≠ 0) (hnorm : ∑ i, ζ i ^ 2 = 1) :
    ∃! T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ, HasJacobiSpectralData T θ ζ :=
  ⟨_, proposition_3_4_5_lanczos hθ hζ hnorm, fun _ h => by
    obtain ⟨hT, Z, hZ, hTZ, hfirst⟩ := h
    exact Lanczos.eq_tridiag_diagonal_of_jacobiMatrix hT hZ hTZ hfirst⟩

/-- **Proposition 3.4.5, signs** of [liesen2013krylov]. Changing signs of the first eigenvector
coordinates leaves the reconstructed Lanczos matrix unchanged. -/
theorem proposition_3_4_5_sign {n : ℕ} {θ ζ η : Fin (n + 1) → ℝ}
    (hθ : StrictMono θ) (hζ : ∀ i, ζ i ≠ 0)
    (hnorm : ∑ i, ζ i ^ 2 = 1) (hη : ∀ i, ζ i ^ 2 = η i ^ 2) :
    Lanczos.tridiag (diagonal θ).toEuclideanLin (WithLp.toLp 2 ζ) (n + 1) =
      Lanczos.tridiag (diagonal θ).toEuclideanLin (WithLp.toLp 2 η) (n + 1) := by
  refine Lanczos.tridiag_diagonal_eq_of_sq_eq hθ.injective hζ ?_ hη
  apply (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1
  rw [EuclideanSpace.real_norm_sq_eq, one_pow]
  exact hnorm

/-- The arithmetic assertion in **Theorem 3.4.6** of [liesen2013krylov] needs a square-root
step for the off-diagonal entries. For nodes $1,2$ and weights $1/3,2/3$, the unique Jacobi
matrix has subdiagonal $\sqrt{2}/3$. Addition, multiplication and division starting from
rational inputs and constants can produce only rational outputs. -/
theorem theorem_3_4_6_irrational_offDiagonal :
    let x : Fin 2 → ℝ := ![1, 2]
    let w : Fin 2 → ℝ := ![1 / 3, 2 / 3]
    (∃ T : Matrix (Fin 2) (Fin 2) ℝ, HasJacobiSpectralData T x (fun i => √(w i))) ∧
      ∀ T : Matrix (Fin 2) (Fin 2) ℝ, HasJacobiSpectralData T x (fun i => √(w i)) →
        T 1 0 = √2 / 3 ∧ Irrational (T 1 0) := by
  let x : Fin 2 → ℝ := ![1, 2]
  let w : Fin 2 → ℝ := ![1 / 3, 2 / 3]
  let s : ℝ := √2
  let r : ℝ := √3
  let T : Matrix (Fin 2) (Fin 2) ℝ := !![5 / 3, s / 3; s / 3, 4 / 3]
  let Z : Matrix (Fin 2) (Fin 2) ℝ := !![1 / r, s / r; -s / r, 1 / r]
  have hs : s ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr : r ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hr₀ : 0 < r := Real.sqrt_pos.2 (by norm_num)
  have hT : T.IsJacobiMatrix := by
    refine ⟨?_, Matrix.isTridiagonal_iff_fin.2 ?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> rfl
    · intro i j hij
      have hi := i.isLt
      have hj := j.isLt
      omega
    · intro i j hij
      have hi : i = 1 := Fin.ext (by have := i.isLt; omega)
      have hj : j = 0 := Fin.ext (by have := i.isLt; omega)
      rw [hi, hj]
      change 0 < √(2 : ℝ) / 3
      positivity
  have hZ : Zᵀ * Z = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Z, Matrix.mul_apply, Fin.sum_univ_two] <;>
      field_simp [hr₀.ne'] <;> nlinarith
  have hTZ : T * Z = Z * diagonal x := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [T, Z, x, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply] <;>
      field_simp [hr₀.ne'] <;> nlinarith
  have hfirst (i : Fin 2) : Z 0 i = √(w i) := by
    fin_cases i
    · change 1 / r = √((1 : ℝ) / 3)
      simp [r]
    · change s / r = √((2 : ℝ) / 3)
      simp [s, r, Real.sqrt_div]
  have hdata : HasJacobiSpectralData T x (fun i => √(w i)) :=
    ⟨hT, Z, hZ, hTZ, hfirst⟩
  refine ⟨⟨T, hdata⟩, fun S hS => ?_⟩
  have hx : StrictMono x := by
    intro i j hij
    have hij' := Fin.lt_def.1 hij
    have hi : i = 0 := Fin.ext (by have := j.isLt; omega)
    have hj : j = 1 := Fin.ext (by have := j.isLt; omega)
    rw [hi, hj]
    norm_num [x]
  have hw (i : Fin 2) : 0 < w i := by fin_cases i <;> norm_num [w]
  have hnorm : ∑ i, (√(w i)) ^ 2 = 1 := by
    simp only [Real.sq_sqrt (hw _).le, Fin.sum_univ_two]
    norm_num [w]
  have hunique := proposition_3_4_5 hx (fun i => (Real.sqrt_pos.2 (hw i)).ne') hnorm
  have heq : S = T := hunique.unique hS hdata
  rw [heq]
  refine ⟨rfl, ?_⟩
  change Irrational (√2 / 3)
  simpa using irrational_sqrt_two.div_ratCast (q := 3) (by norm_num)

/-- The two-node counterexample to the arithmetic restriction in **Theorem 3.4.6** of
[liesen2013krylov] occurs for a probability measure with at least three support points.
The Gauss nodes are $1,2$ and the weights are $1/3,2/3$. -/
theorem theorem_3_4_6_gauss_counterexample :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ μ (Set.Icc 0 3)ᶜ = 0 ∧
      (∀ s : Finset ℝ, s.card ≤ 2 → μ (↑s : Set ℝ)ᶜ ≠ 0) ∧
      Quadrature.IsExactOnMeasure μ ![1 / 3, 2 / 3] ![1, 2] 3 ∧
      Irrational (jacobiMatrix μ 2 1 0) := by
  let d (t w : ℝ) := ENNReal.ofReal w • Measure.dirac t
  let μ := d 0 (2 / 45) + d (5 / 3) (9 / 10) + d 3 (1 / 18)
  let x : Fin 2 → ℝ := ![1, 2]
  let w : Fin 2 → ℝ := ![1 / 3, 2 / 3]
  have hmass : IsProbabilityMeasure μ := by
    constructor
    simp only [μ, d, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  let _ := hmass
  have happly {s : Set ℝ} :
      μ s = ENNReal.ofReal (2 / 45) * s.indicator 1 0 +
        ENNReal.ofReal (9 / 10) * s.indicator 1 (5 / 3) +
        ENNReal.ofReal (1 / 18) * s.indicator 1 3 := by
    simp only [μ, d, Measure.add_apply, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply]
  have hsupp : μ (Set.Icc 0 3)ᶜ = 0 := by
    rw [happly]
    have h0 : (0 : ℝ) ∉ (Set.Icc 0 3)ᶜ := by simp
    have h5 : (5 / 3 : ℝ) ∉ (Set.Icc 0 3)ᶜ := by norm_num
    have h3 : (3 : ℝ) ∉ (Set.Icc 0 3)ᶜ := by simp
    simp [Set.indicator_of_notMem, h0, h5, h3]
  have hcard (s : Finset ℝ) (hs : s.card ≤ 2) : μ (↑s : Set ℝ)ᶜ ≠ 0 := by
    classical
    intro h
    rw [happly, add_eq_zero, add_eq_zero] at h
    have h0 : (0 : ℝ) ∈ s := by
      by_contra hn
      have hp : ¬ (2 / 45 : ℝ) ≤ 0 := by norm_num
      exact hp (by simpa [hn, ENNReal.ofReal_eq_zero] using h.1.1)
    have h5 : (5 / 3 : ℝ) ∈ s := by
      by_contra hn
      have hp : ¬ (9 / 10 : ℝ) ≤ 0 := by norm_num
      exact hp (by simpa [hn, ENNReal.ofReal_eq_zero] using h.1.2)
    have h3 : (3 : ℝ) ∈ s := by
      by_contra hn
      simpa [hn, ENNReal.ofReal_eq_zero] using h.2
    have hsub : ({0, 5 / 3, 3} : Finset ℝ) ⊆ s :=
      Finset.insert_subset h0 (Finset.insert_subset h5 (Finset.singleton_subset_iff.2 h3))
    have hh : ({0, 5 / 3, 3} : Finset ℝ).card = 3 := by
      rw [Finset.card_insert_of_notMem (by norm_num), Finset.card_insert_of_notMem (by norm_num)]
      simp
    have := (Finset.card_le_card hsub).trans hs
    omega
  have hint (p : ℝ[X]) (t a : ℝ) : Integrable (fun z => p.eval z) (d t a) :=
    (integrable_dirac (by simp)).smul_measure (by simp)
  have hInt (p : ℝ[X]) :
      ∫ z, p.eval z ∂μ = (2 / 45) * p.eval 0 + (9 / 10) * p.eval (5 / 3) +
        (1 / 18) * p.eval 3 := by
    rw [show μ = d 0 (2 / 45) + d (5 / 3) (9 / 10) + d 3 (1 / 18) from rfl,
      integral_add_measure ((hint _ _ _).add_measure (hint _ _ _)) (hint _ _ _),
      integral_add_measure (hint _ _ _) (hint _ _ _)]
    simp [d, integral_smul_measure, ENNReal.toReal_ofReal, show 0 ≤ (2 / 45 : ℝ) by norm_num,
      show 0 ≤ (9 / 10 : ℝ) by norm_num]
  have hExact : Quadrature.IsExactOnMeasure μ w x 3 := by
    intro p hp
    have hev (z : ℝ) : p.eval z = ∑ k : Fin 4, p.coeff k * z ^ k.val := by
      rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => p.coeff k * z ^ k) 4]
      exact eval_eq_sum_range' (by have := natDegree_le_iff_degree_le.2 hp; omega) z
    rw [hInt, Fin.sum_univ_two]
    change (1 / 3 : ℝ) * p.eval 1 + (2 / 3) * p.eval 2 = _
    simp_rw [hev, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    fin_cases i <;> norm_num <;> ring
  have hx : Function.Injective x := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [x] at hij ⊢
  refine ⟨μ, hmass, hsupp, hcard, hExact, ?_⟩
  have hdata := (theorem_3_4_1 hsupp hcard hx hExact).1
  exact (theorem_3_4_6_irrational_offDiagonal.2 _ hdata).2

/-- **Proposition 3.4.7** of [liesen2013krylov]. For an orthonormal basis of complex Euclidean
space given by the columns of $V$ and any strictly increasing real spectrum $\theta$, there
is a Hermitian matrix with those eigenvalues whose Lanczos basis from the first column of $V$
is the given basis in its prescribed order. For Hermitian matrices the Lanczos and Arnoldi
basis vectors coincide. -/
theorem proposition_3_4_7 {n : ℕ} (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hV : Vᴴ * V = 1) {θ : Fin (n + 1) → ℝ} (hθ : StrictMono θ) :
    ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, A.IsHermitian ∧
      A.charpoly = (∏ i, (X - C (θ i : ℂ))) ∧
      ∀ i : Fin (n + 1), Arnoldi.vec A.toEuclideanLin (WithLp.toLp 2 (V.col 0)) i =
        WithLp.toLp 2 (V.col i) := by
  let D := diagonal θ
  let q : EuclideanSpace ℝ (Fin (n + 1)) := WithLp.toLp 2 fun _ => 1
  let T := Lanczos.tridiag D.toEuclideanLin q (n + 1)
  obtain ⟨hT, Z, hZ, hTZ, _⟩ :=
    Lanczos.tridiag_diagonal_spectralData (ζ := fun _ => 1) hθ.injective (fun _ => one_ne_zero)
  change T.IsJacobiMatrix at hT
  change T * Z = Z * D at hTZ
  let H := T.complexify
  let U := Z.complexify
  let Λ := diagonal (fun i => (θ i : ℂ))
  have hD : D.complexify = Λ := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D, Λ]
    · simp [D, Λ, hij]
  have hZ' : Zᴴ * Z = 1 := by simpa only [conjTranspose_eq_transpose_of_trivial] using hZ
  have hU : Uᴴ * U = 1 := by
    simpa only [complexify_mul, complexify_conjTranspose, complexify_one] using
      congrArg Matrix.complexify hZ'
  have hUU : U * Uᴴ = 1 := mul_eq_one_comm.1 hU
  have hHU : H * U = U * Λ := by
    simpa only [complexify_mul, hD] using congrArg Matrix.complexify hTZ
  have hH : H = U * Λ * Uᴴ := by
    rw [← hHU, Matrix.mul_assoc, hUU, mul_one]
  let A := V * H * Vᴴ
  have hAH : A.IsHermitian := isHermitian_mul_mul_conjTranspose V
    ((isHermitian_complexify_iff T).2 hT.isHermitian)
  have charpoly_conj (B M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hB : Bᴴ * B = 1) :
      (B * M * Bᴴ).charpoly = M.charpoly := calc
    (B * M * Bᴴ).charpoly = (Bᴴ * (B * M)).charpoly := charpoly_mul_comm _ _
    _ = M.charpoly := by rw [← Matrix.mul_assoc, hB, one_mul]
  have hchar : A.charpoly = ∏ i, (X - C (θ i : ℂ)) := by
    rw [show A = V * H * Vᴴ from rfl, charpoly_conj V H hV, hH, charpoly_conj U Λ hU]
    exact charpoly_diagonal _
  have hAV : A * V = V * H := by
    rw [show A = V * H * Vᴴ from rfl, Matrix.mul_assoc (V * H), hV, mul_one]
  refine ⟨A, hAH, hchar, fun i => Arnoldi.vec_eq_col_of_mul_eq_mul hV hAV
    hT.isTridiagonal.complexify.isUpperHessenberg (fun j => ?_) i⟩
  change 0 < (T j.succ j.castSucc : ℂ)
  exact RCLike.ofReal_pos.mpr (hT.subdiagonal_pos _ _ rfl)

/-- The coordinate inclusion sends each coordinate vector of the small space to the coordinate
vector of the larger space with the same index. -/
def leadingCoordinateInclusion {m n : ℕ} (h : m ≤ n) : Matrix (Fin n) (Fin m) ℝ :=
  fun i j => if i = Fin.castLE h j then 1 else 0

/-- **Proposition 3.4.8** of [liesen2013krylov]. For a Jacobi matrix with orthogonal
diagonalization $T=Z\operatorname{diag}(\lambda)Z^\mathsf{T}$ and leading block with
$S=Q\operatorname{diag}(\theta)Q^\mathsf{T}$, let $V$ be the coordinate inclusion. The
column of $W=Z^\mathsf{T}VQ$ corresponding to $\theta_j$ gives weights
$W_{ij}^2$ of sum one, and $\theta_j=\sum_i W_{ij}^2\lambda_i$.

The statement applies to all orthogonally diagonalizable real matrices with orthogonally
diagonalizable leading blocks. In the Jacobi case the Lanczos basis matrix is $V$.

**Reading.** Works for any matrix and leading block with real orthogonal diagonalizations, including
equal size.
-/
theorem proposition_3_4_8 {m n : ℕ} (h : m ≤ n) (T : Matrix (Fin n) (Fin n) ℝ)
    {Z : Matrix (Fin n) (Fin n) ℝ} {Q : Matrix (Fin m) (Fin m) ℝ}
    (hZ : Zᵀ * Z = 1) (hQ : Qᵀ * Q = 1) {e : Fin n → ℝ} {θ : Fin m → ℝ}
    (hT : T = Z * diagonal e * Zᵀ)
    (hS : T.submatrix (Fin.castLE h) (Fin.castLE h) = Q * diagonal θ * Qᵀ) :
    let W := Zᵀ * leadingCoordinateInclusion h * Q
    ∀ j : Fin m, θ j = ∑ i, (W i j) ^ 2 * e i ∧ ∑ i, (W i j) ^ 2 = 1 := by
  let V := leadingCoordinateInclusion h
  let W := Zᵀ * V * Q
  have hV (M : Matrix (Fin n) (Fin n) ℝ) :
      Vᵀ * M * V = M.submatrix (Fin.castLE h) (Fin.castLE h) := by
    have hrow (i : Fin m) (k : Fin n) : (Vᵀ * M) i k = M (Fin.castLE h i) k := by
      simp [Matrix.mul_apply, V, leadingCoordinateInclusion, ite_mul]
    ext i j
    rw [Matrix.mul_apply]
    simp [hrow, V, leadingCoordinateInclusion, mul_ite]
  have hI : Vᵀ * V = 1 := by
    have heval := hV (1 : Matrix (Fin n) (Fin n) ℝ)
    rw [Matrix.mul_one] at heval
    rw [heval]
    ext i j
    simp [Matrix.one_apply]
  have hZ' : Z * Zᵀ = 1 := mul_eq_one_comm.1 hZ
  have hW : Wᵀ * W = 1 := calc
    Wᵀ * W = Qᵀ * (Vᵀ * (Z * Zᵀ) * V) * Q := by simp [W, transpose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [hZ', Matrix.mul_one, hI, mul_one, hQ]
  have hd : Wᵀ * diagonal e * W = diagonal θ := calc
    Wᵀ * diagonal e * W = Qᵀ * (Vᵀ * T * V) * Q := by
      conv_rhs => rw [hT]
      simp [W, transpose_mul, Matrix.mul_assoc]
    _ = diagonal θ := by
      rw [hV, hS]
      calc Qᵀ * (Q * diagonal θ * Qᵀ) * Q =
            (Qᵀ * Q) * diagonal θ * (Qᵀ * Q) := by simp only [Matrix.mul_assoc]
        _ = diagonal θ := by simp [hQ]
  change ∀ j : Fin m, θ j = ∑ i, (W i j) ^ 2 * e i ∧ ∑ i, (W i j) ^ 2 = 1
  intro j
  have hdj := congrFun (congrFun hd j) j
  have hWj := congrFun (congrFun hW j) j
  constructor
  · rw [Matrix.mul_assoc, Matrix.mul_apply, diagonal_apply_eq] at hdj
    rw [← hdj]
    exact Finset.sum_congr rfl fun i _ => by rw [transpose_apply, diagonal_mul]; ring
  · simpa only [Matrix.mul_apply, transpose_apply, Matrix.one_apply_eq, pow_two] using hWj

/-- For an order-$(m+1)$ leading block of a larger Jacobi matrix, the eigenvalue $\theta$ is
stabilised to within $T_{m+1,m}|z_m|$ if the full matrix has an eigenvalue within that distance
of $\theta$, where $z$ is the unit eigenvector of the leading block. This is Definition 3.4.10
of [liesen2013krylov], with zero-based indices.

The printed second clause joins the tolerance and the existence of a nearby eigenvalue with
"and". It is read as specifying the distance criterion for stabilisation.

**Reading.** Encodes distance inequality independently of the Jacobi and eigenpair hypotheses.
-/
def IsStabilisedJacobiEigenvalue {m n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ)
    (h : m + 1 < n) (θ : ℝ) (z : EuclideanSpace ℝ (Fin (m + 1))) : Prop :=
  ∃ μ ∈ spectrum ℝ T, |μ - θ| ≤ T ⟨m + 1, h⟩ ⟨m, by omega⟩ * |z (Fin.last m)|

/-- **Theorem 3.4.9** of [liesen2013krylov]. Each eigenvalue $\theta$ of a strict leading
principal submatrix of a Jacobi matrix has a full-matrix eigenvalue within the tolerance
$T_{m+1,m}|z_m|$, where $z$ is a unit leading-block eigenvector. -/
theorem theorem_3_4_9 {m n : ℕ} {T : Matrix (Fin n) (Fin n) ℝ} (hT : T.IsJacobiMatrix)
    (h : m + 1 < n) {θ : ℝ} {z : EuclideanSpace ℝ (Fin (m + 1))} (hz : ‖z‖ = 1)
    (heig : (T.submatrix (Fin.castLE h.le) (Fin.castLE h.le)).toEuclideanLin z = θ • z) :
    IsStabilisedJacobiEigenvalue T h θ z :=
  hT.leadingBlock_persistence h hz heig

/-- **Theorem 3.4.11** of [liesen2013krylov]. Let $S$ be a leading principal submatrix of a
Jacobi matrix $T$, with eigenvalues $\theta_j$ and first-coordinate spectral weights $v_j$.
Let the corresponding full-matrix eigenvalues and weights be $\lambda_i$ and $w_i$. Then
$$v_j=\sum_i w_i \ell_j(\lambda_i)=\sum_i w_i \ell_j(\lambda_i)^2,$$
where $\ell_j(X)=(\psi(X)/(X-\theta_j))/\psi'(\theta_j)$ for the characteristic polynomial
$\psi$ of $S$. The quotient is a polynomial, including when a full spectral node equals
$\theta_j$.

**Correction.** The displayed scalar quotient in the source has a removable singularity when a
larger eigenvalue equals the smaller eigenvalue. For example, the order-three Jacobi matrix
with zero diagonal and unit subdiagonal shares eigenvalue $0$ with its first leading block. The
polynomial quotient evaluates at the shared eigenvalue by continuation. The result also permits
the two blocks to have equal size. -/
theorem theorem_3_4_11 {m n : ℕ} {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hT : T.IsJacobiMatrix) (hm : m + 1 ≤ n + 1) (j : Fin (m + 1)) :
    let S := T.submatrix (Fin.castLE hm) (Fin.castLE hm)
    let hS := (hT.leadingBlock hm).isHermitian
    let θ := hS.eigenvalues
    let l := Lagrange.basis Finset.univ θ j
    let v := (hS.eigenvectorBasis j 0) ^ 2
    let e := hT.isHermitian.eigenvalues
    let w := fun i => (hT.isHermitian.eigenvectorBasis i 0) ^ 2
    (l = C ((S.charpoly.derivative.eval (θ j))⁻¹) * (S.charpoly / (X - C (θ j)))) ∧
      (v = ∑ i, w i * l.eval (e i)) ∧ (v = ∑ i, w i * l.eval (e i) ^ 2) := by
  let S := T.submatrix (Fin.castLE hm) (Fin.castLE hm)
  let hS := (hT.leadingBlock hm).isHermitian
  let θ := hS.eigenvalues
  let l := Lagrange.basis Finset.univ θ j
  let v := (hS.eigenvectorBasis j 0) ^ 2
  let e := hT.isHermitian.eigenvalues
  let w := fun i => (hT.isHermitian.eigenvectorBasis i 0) ^ 2
  have hθ : Function.Injective θ := (hT.leadingBlock hm).eigenvalues_injective
  have hψ : Lagrange.nodal Finset.univ θ = S.charpoly := by
    rw [Lagrange.nodal_eq, hS.charpoly_eq]
    rfl
  have hl : l = C ((S.charpoly.derivative.eval (θ j))⁻¹) * (S.charpoly / (X - C (θ j))) := by
    rw [show l = Lagrange.basis Finset.univ θ j from rfl,
      Lagrange.basis_eq_prod_sub_inv_mul_nodal_div (Finset.mem_univ j),
      Lagrange.nodalWeight_eq_eval_derivative_nodal (Finset.mem_univ j), hψ]
  have hdeg : l.natDegree = m := by
    rw [show l = Lagrange.basis Finset.univ θ j from rfl,
      Lagrange.natDegree_basis hθ.injOn (Finset.mem_univ j), Finset.card_univ,
      Fintype.card_fin, Nat.add_sub_cancel]
  have hδ (i : Fin (m + 1)) : l.eval (θ i) = if i = j then 1 else 0 := by
    by_cases hij : i = j
    · subst i
      rw [ite_eq_left rfl]
      exact Lagrange.eval_basis_self hθ.injOn (Finset.mem_univ j)
    · rw [ite_eq_right hij]
      exact Lagrange.eval_basis_of_ne (Ne.symm hij) (Finset.mem_univ i)
  have hmatch (p : ℝ[X]) (hp : p.natDegree < 2 * (m + 1)) :
      (∑ i, w i * p.eval (e i)) = ∑ i, (hS.eigenvectorBasis i 0) ^ 2 * p.eval (θ i) := by
    have h := hT.leadingBlock_aeval_apply_first hm hp
    change aeval T p 0 0 = aeval S p 0 0 at h
    rw [Matrix.IsHermitian.aeval_apply_self hT.isHermitian p 0,
      Matrix.IsHermitian.aeval_apply_self hS p 0] at h
    exact h
  change (l = C ((S.charpoly.derivative.eval (θ j))⁻¹) * (S.charpoly / (X - C (θ j)))) ∧
    (v = ∑ i, w i * l.eval (e i)) ∧ (v = ∑ i, w i * l.eval (e i) ^ 2)
  refine ⟨hl, ?_, ?_⟩
  · simpa [hδ, mul_ite, v] using (hmatch l (by rw [hdeg]; omega)).symm
  · have hh := hmatch (l ^ 2) (by rw [natDegree_pow, hdeg]; omega)
    simp_rw [eval_pow, hδ, apply_ite (fun x : ℝ => x ^ 2)] at hh
    simpa [mul_ite, v] using hh.symm

/-- The minimal adjacent gap in a list of at least two increasing eigenvalues. For a strictly
increasing list, it is the least distance between two distinct entries.

**Reading.** Adjacent gaps suffice for the source's minimum pairwise distance on strictly
increasing spectra. -/
noncomputable def minimalJacobiGap {n : ℕ} (e : Fin (n + 2) → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun j : Fin (n + 1) => e j.succ - e j.castSucc

/-- **Theorem 3.4.12** of [liesen2013krylov]. Suppose a Jacobi matrix has ordered spectrum $e$
and its penultimate leading block has precisely the midpoints of the consecutive spectral gaps
as eigenvalues. For every unit eigenvector of a strict leading block, the norm of the
zero-padded residual is its stabilisation tolerance. That tolerance is at least one quarter of
the least spectral gap. -/
theorem theorem_3_4_12 {m n : ℕ} {T : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ}
    (hT : T.IsJacobiMatrix) {e : Fin (n + 2) → ℝ} (he : StrictMono e)
    (hσ : spectrum ℝ T = Set.range e)
    (hmid : spectrum ℝ (T.submatrix (Fin.castSucc : Fin (n + 1) → Fin (n + 2)) Fin.castSucc) =
      Set.range (fun j : Fin (n + 1) => (e j.succ + e j.castSucc) / 2))
    (h : m + 1 < n + 2) {θ : ℝ} {z : EuclideanSpace ℝ (Fin (m + 1))} (hz : ‖z‖ = 1)
    (heig : (T.submatrix (Fin.castLE h.le) (Fin.castLE h.le)).toEuclideanLin z = θ • z) :
    let x := Matrix.leadingZeroPad h.le z
    let tol := T ⟨m + 1, h⟩ ⟨m, by omega⟩ * |z (Fin.last m)|
    ‖T.toEuclideanLin x - θ • x‖ = tol ∧ minimalJacobiGap e / 4 ≤ tol := by
  let tol := T ⟨m + 1, h⟩ ⟨m, by omega⟩ * |z (Fin.last m)|
  refine ⟨hT.leadingBlock_residual_norm h heig, ?_⟩
  change minimalJacobiGap e / 4 ≤ tol
  have htol : 0 ≤ tol :=
    mul_nonneg (hT.subdiagonal_pos _ _ rfl).le (abs_nonneg _)
  let S := T.submatrix (Fin.castSucc : Fin (n + 1) → Fin (n + 2)) Fin.castSucc
  obtain ⟨a, ha, hd⟩ := hT.leadingBlock_persistence h hz heig
  have hnear : ∃ b ∈ spectrum ℝ S, |b - θ| ≤ tol := by
    by_cases hm : m + 1 < n + 1
    · have hS : S.IsJacobiMatrix := hT.leadingBlock (Nat.le_succ (n + 1))
      have hSeig : (S.submatrix (Fin.castLE hm.le) (Fin.castLE hm.le)).toEuclideanLin z =
          θ • z := heig
      obtain ⟨b, hb, hbθ⟩ := hS.leadingBlock_persistence hm hz hSeig
      exact ⟨b, hb, hbθ⟩
    · have hmn : m = n := by omega
      subst m
      have hSeig : S.toEuclideanLin z = θ • z := heig
      have hv : Module.End.HasEigenvector S.toEuclideanLin θ z :=
        Module.End.hasEigenvector_iff.2
          ⟨Module.End.mem_eigenspace_iff.2 hSeig, norm_ne_zero_iff.1 (by rw [hz]; norm_num)⟩
      exact ⟨θ, (hasEigenvalue_toEuclideanLin_iff _ _).1
        (Module.End.hasEigenvalue_of_hasEigenvector hv), by simpa using htol⟩
  obtain ⟨b, hb, hbθ⟩ := hnear
  rw [hσ] at ha
  change b ∈ spectrum ℝ
    (T.submatrix (Fin.castSucc : Fin (n + 1) → Fin (n + 2)) Fin.castSucc) at hb
  rw [hmid] at hb
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  have hg : minimalJacobiGap e ≤ e j.succ - e j.castSucc :=
    Finset.inf'_le _ (Finset.mem_univ j)
  have hj : e j.castSucc < e j.succ := he (by simp)
  have hd' : minimalJacobiGap e / 2 ≤ |e i - (e j.succ + e j.castSucc) / 2| := by
    by_cases hi : i ≤ j.castSucc
    · have hlow := he.monotone hi
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hupper : j.succ ≤ i := by
        have hij := Fin.lt_def.1 (lt_of_not_ge hi)
        exact Fin.le_def.2 (by simpa using hij)
      have hhigh := he.monotone hupper
      rw [abs_of_nonneg (by linarith)]
      linarith
  have htriangle : |e i - (e j.succ + e j.castSucc) / 2| ≤ tol + tol := calc
    _ ≤ |e i - θ| + |θ - (e j.succ + e j.castSucc) / 2| := abs_sub_le _ _ _
    _ ≤ tol + tol := add_le_add hd (by rwa [abs_sub_comm])
  linarith

end LiesenStrakos.Chapter03

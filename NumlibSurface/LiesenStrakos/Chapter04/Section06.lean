import Numlib.Algebra.Polynomial.Commute
import Numlib.Algebra.Polynomial.MinDegreeRepresentation
import Numlib.LinearAlgebra.Matrix.WeightedAdjoint
import NumlibSurface.LiesenStrakos.Chapter04.Section05

/-!
# Liesen and Strakoš, Section 4.6: Matrix formulation and equivalent characterisations

Section 4.6 of [liesen2013krylov] defines normality of prescribed degree for a square matrix
and a positive definite Hermitian inner product matrix $B$. The real eigendecomposition
criterion, its corollary, and the degree-one characterization are in
`NumlibSurface.LiesenStrakos.Chapter04.Section06.Real`.

## Main definitions

* Definition 4.6.1, `LiesenStrakos.IsBNormalOfDegree`: the $B$-adjoint is a polynomial
  in the matrix of prescribed minimum degree.
* `LiesenStrakos.AdmitsOptimalWeightedRecurrence`: an optimal recurrence for the
  weight $B$, expressed in $B$-orthonormal coordinates.
* Equation (4.6.2), `LiesenStrakos.AdmissibleEigenbasisMetric`: weights whose inverses
  factor through an eigenbasis and a positive definite matrix on each equal-eigenvalue block.

## Main results

* Theorem 4.6.2, `LiesenStrakos.theorem_4_6_2`: the short-recurrence criterion
  for a complex matrix with a positive definite weight.
* Theorem 4.6.2, `LiesenStrakos.theorem_4_6_2_sufficient`: weighted normality
  implies the optimal short recurrence over either the real or complex scalars.
* Theorem 4.6.3, `LiesenStrakos.theorem_4_6_3`: the eigenbasis and interpolation
  characterization of weighted normality over the complex numbers.
* Corollary 4.6.4, `LiesenStrakos.corollary_4_6_4`: the interpolation degree and the
  weighted adjoint in an eigenbasis.
* Theorem 4.6.5 (1), `LiesenStrakos.theorem_4_6_5_zero`: some positive definite weight makes
  the matrix normal of degree zero precisely for a nonzero scalar matrix.
* Theorem 4.6.5 (2), `LiesenStrakos.theorem_4_6_5_one`: some positive definite weight makes
  the matrix normal of degree one precisely when it is diagonalizable with collinear
  eigenvalues and minimal polynomial degree at least two.

## Deviations from the source

* **Theorem 4.6.2** (reading). The full equivalence is stated for complex starting vectors.
  Sufficiency also holds for real starts.
* **Theorem 4.6.3, Corollary 4.6.4, and Theorem 4.6.5 (2)** (reading). The eigendecomposition
  uses complex arithmetic, expressed by the algebraic closure of the scalar field.

## Not formalized

* **Theorem 4.6.2, real necessity.** The converse for real starting vectors requires a
  real operator necessity theorem.
-/

namespace LiesenStrakos

open Polynomial
open scoped Matrix ComplexOrder

/-- For a Hermitian positive definite matrix $B$, a square matrix $A$ is $B$-normal of degree
$s$ if the $B$-adjoint $B^{-1}A^HB$ is a polynomial in $A$ of least degree $s$.
This is Definition 4.6.1 of [liesen2013krylov]. -/
def IsBNormalOfDegree {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
    (A B : Matrix n n 𝕜) (s : ℕ) : Prop :=
  B.PosDef ∧ Polynomial.IsMinDegreeRepresentation (R := 𝕜) A (A.weightedAdjoint B) s

section WeightedRecurrence

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- A matrix admits an optimal weighted recurrence if its operator in orthonormal
coordinates for the metric $B$ admits the corresponding optimal Arnoldi recurrence.
The columns of $W$ satisfy $W^H B W = I$ and the operator in those coordinates is
$W^{-1} A W$. -/
def AdmitsOptimalWeightedRecurrence (A B : Matrix n n 𝕜) (s : ℕ) : Prop :=
  ∃ (W : Matrix n n 𝕜) (hW : IsUnit W), Wᴴ * B * W = 1 ∧
    AdmitsOptimalRecurrence (Matrix.toEuclideanLin (Matrix.similarityAlgEquiv W hW A)) s

private theorem isNormalOfDegree_weighted_coordinates_iff (A B W : Matrix n n 𝕜)
    (hB : B.PosDef) (hW : IsUnit W) (hmetric : Wᴴ * B * W = 1) (s : ℕ) :
    IsNormalOfDegree (Matrix.toEuclideanLin (Matrix.similarityAlgEquiv W hW A)) s ↔
      IsBNormalOfDegree A B s := by
  let e := (Matrix.similarityAlgEquiv W hW).trans (Matrix.toLpLinAlgEquiv (R := 𝕜) (n := n) 2)
  change IsNormalOfDegree (e A) s ↔ _
  have hadj : e (A.weightedAdjoint B) = (e A).adjoint := by
    change Matrix.toEuclideanLin (Matrix.similarityAlgEquiv W hW (A.weightedAdjoint B)) =
      (Matrix.toEuclideanLin (Matrix.similarityAlgEquiv W hW A)).adjoint
    rw [Matrix.similarityAlgEquiv_weightedAdjoint hB hW hmetric,
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  unfold IsNormalOfDegree IsBNormalOfDegree
  rw [← hadj, isMinDegreeRepresentation_algEquiv_iff, and_iff_right hB]

/-- When $s+2$ is less than the minimal-polynomial degree of $A$, weighted normality of
degree $s$ implies an optimal $(s+2)$-term recurrence. This is the sufficient direction
of Theorem 4.6.2 of [liesen2013krylov] over the real or complex scalars. -/
theorem theorem_4_6_2_sufficient {A B : Matrix n n 𝕜} {s : ℕ}
    (hmin : s + 2 < (minpoly 𝕜 A).natDegree) (h : IsBNormalOfDegree A B s) :
    AdmitsOptimalWeightedRecurrence A B s := by
  obtain ⟨W, hW, hmetric⟩ := h.1.exists_isUnit_conj_eq_one
  rw [Matrix.star_eq_conjTranspose] at hmetric
  let e := (Matrix.similarityAlgEquiv W hW).trans (Matrix.toLpLinAlgEquiv (R := 𝕜) (n := n) 2)
  have hdeg : s + 2 < operatorMinimalDegree (e A) := by
    change s + 2 < (minpoly 𝕜 (e A)).natDegree
    rwa [minpoly.algEquiv_eq]
  exact ⟨W, hW, hmetric, theorem_4_4_3_admits (e A) hdeg
    ((isNormalOfDegree_weighted_coordinates_iff A B W h.1 hW hmetric s).2 h)⟩

/-- When $s+2$ is less than the minimal-polynomial degree of a complex matrix $A$,
$A$ admits an optimal $(s+2)$-term recurrence for the positive definite weight $B$
if and only if it is $B$-normal of degree $s$.
This is the complex case of Theorem 4.6.2 of [liesen2013krylov].

**Reading.** The equivalence uses complex starting vectors. The sufficiency result also covers
real starts. -/
theorem theorem_4_6_2 (A B : Matrix n n ℂ) (hB : B.PosDef) (s : ℕ)
    (hmin : s + 2 < (minpoly ℂ A).natDegree) :
    AdmitsOptimalWeightedRecurrence A B s ↔ IsBNormalOfDegree A B s := by
  refine ⟨?_, theorem_4_6_2_sufficient hmin⟩
  rintro ⟨W, hW, hmetric, h⟩
  let e := (Matrix.similarityAlgEquiv W hW).trans (Matrix.toLpLinAlgEquiv (R := ℂ) (n := n) 2)
  have hdeg : s + 2 < operatorMinimalDegree (e A) := by
    change s + 2 < (minpoly ℂ (e A)).natDegree
    rwa [minpoly.algEquiv_eq]
  exact (isNormalOfDegree_weighted_coordinates_iff A B W hB hW hmetric s).1
    (theorem_4_5_4 (e A) hdeg h)

end WeightedRecurrence

section Eigenbasis

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- The class of admissible weights $B$ for the eigenvector matrix $Y$ and diagonal
eigenvalue list $d$, from equation (4.6.2) of [liesen2013krylov]. The equal-eigenvalue
blocks are expressed by zero entries between distinct eigenvalues. -/
def AdmissibleEigenbasisMetric (B Y : Matrix n n 𝕜) (d : n → 𝕜) : Prop :=
  ∃ D : Matrix n n 𝕜, D.PosDef ∧ B⁻¹ = Y * D * Yᴴ ∧
    ∀ i j, d i ≠ d j → D i j = 0

private theorem aeval_diagonal (d : n → 𝕜) (p : 𝕜[X]) :
    aeval (Matrix.diagonal d) p = Matrix.diagonal (fun i => p.eval (d i)) := by
  rw [← Matrix.diagonalAlgHom_apply 𝕜, aeval_algHom_apply, aeval_pi_apply]
  simp [coe_aeval_eq_eval]

private theorem aeval_diagonal_eq_conjTranspose_iff (d : n → 𝕜) (p : 𝕜[X]) :
    aeval (Matrix.diagonal d) p = (Matrix.diagonal d)ᴴ ↔ ∀ i, p.eval (d i) = star (d i) := by
  rw [aeval_diagonal, Matrix.diagonal_conjTranspose]
  constructor
  · intro h i
    simpa only [Matrix.diagonal_apply_eq, Pi.star_apply] using
      congrArg (fun M : Matrix n n 𝕜 => M i i) h
  · intro h
    exact congrArg Matrix.diagonal (funext h)

/-- In any eigenbasis of a weighted-normal matrix, the weight factors through
positive definite equal-eigenvalue blocks and the weighted adjoint is diagonal with
conjugated eigenvalues. -/
theorem IsBNormalOfDegree.eigenbasis {A B Y : Matrix n n 𝕜} {d : n → 𝕜} {s : ℕ}
    (h : IsBNormalOfDegree A B s) (hY : IsUnit Y)
    (hdiag : A = Y * Matrix.diagonal d * Y⁻¹) :
    AdmissibleEigenbasisMetric B Y d ∧
      A.weightedAdjoint B = Y * (Matrix.diagonal d)ᴴ * Y⁻¹ ∧
      IsMinDegreeRepresentation (R := 𝕜) (Matrix.diagonal d) (Matrix.diagonal d)ᴴ s := by
  let e := Matrix.similarityAlgEquiv Y hY
  have he : e A = Matrix.diagonal d := (Matrix.similarityAlgEquiv_apply_eq_iff Y hY A _).2 hdiag
  let D := Y⁻¹ * B⁻¹ * (Y⁻¹)ᴴ
  have hD : D.PosDef := h.1.inv.mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_iff_isUnit.mpr (Matrix.isUnit_nonsing_inv_iff.mpr hY))
  have hBD : B⁻¹ = Y * D * Yᴴ := (Matrix.mul_invMetric_mul_conjTranspose hY).symm
  obtain ⟨p, -, hp, -⟩ := h.2
  have hmul := Matrix.similarityAlgEquiv_weightedAdjoint_mul (A := A) h.1.isUnit hY hBD
  change e (A.weightedAdjoint B) * D = D * (e A)ᴴ at hmul
  rw [← hp, ← aeval_algHom_apply e, he, aeval_diagonal, Matrix.diagonal_conjTranspose] at hmul
  have hentry (i j : n) : p.eval (d i) * D i j = D i j * star (d j) := by
    simpa only [Matrix.diagonal_mul, Matrix.mul_diagonal, Pi.star_apply] using
      congrArg (fun M : Matrix n n 𝕜 => M i j) hmul
  have hvalues (i : n) : p.eval (d i) = star (d i) :=
    mul_right_cancel₀ (hD.diag_pos (i := i)).ne' ((hentry i i).trans (mul_comm _ _))
  have hblock (i j : n) (hij : d i ≠ d j) : D i j = 0 := by
    by_contra hne
    apply hij
    apply star_injective
    exact mul_right_cancel₀ hne (by rw [← hvalues i, hentry, mul_comm])
  have hnormal := Matrix.similarityAlgEquiv_weightedAdjoint_of_block h.1.isUnit hY he hD hBD hblock
  refine ⟨⟨D, hD, hBD, hblock⟩, ?_, ?_⟩
  · exact (Matrix.similarityAlgEquiv_apply_eq_iff Y hY _ _).1 hnormal
  · have hmin := (isMinDegreeRepresentation_algEquiv_iff e A (A.weightedAdjoint B) s).2 h.2
    rwa [he, hnormal] at hmin

/-- Weighted normality of degree $s$ is equivalent to a diagonalization with
an admissible weight and a unique least-degree polynomial taking the diagonal
to its conjugate transpose. This is Theorem 4.6.3 of [liesen2013krylov].

The book discusses both real and complex matrices. Here the scalar field is algebraically
closed, so the eigenvectors and polynomial coefficients belong to the same field. The
block condition uses the equality classes of the eigenvalues in any finite indexing.
-/
theorem theorem_4_6_3 [IsAlgClosed 𝕜] (A B : Matrix n n 𝕜) (hB : B.PosDef) (s : ℕ) :
    IsBNormalOfDegree A B s ↔
      ∃ (Y : Matrix n n 𝕜) (d : n → 𝕜), IsUnit Y ∧
        A = Y * Matrix.diagonal d * Y⁻¹ ∧ AdmissibleEigenbasisMetric B Y d ∧
        ∃! p : 𝕜[X], p.degree = s ∧ aeval (Matrix.diagonal d) p = (Matrix.diagonal d)ᴴ ∧
          ∀ q : 𝕜[X], aeval (Matrix.diagonal d) q = (Matrix.diagonal d)ᴴ →
            (s : WithBot ℕ) ≤ q.degree := by
  constructor
  · intro h
    obtain ⟨p, -, hp, -⟩ := h.2
    have hcomm : Commute (A.weightedAdjoint B) A := hp ▸ (Commute.refl A).aeval_left p
    obtain ⟨Y, hY, d, he, -⟩ :=
      Matrix.exists_diagonal_similarity_of_commute_weightedAdjoint hB hcomm
    have hdiag := (Matrix.similarityAlgEquiv_apply_eq_iff Y hY A _).1 he
    obtain ⟨hmetric, -, hmin⟩ := h.eigenbasis hY hdiag
    exact ⟨Y, d, hY, hdiag, hmetric, hmin.existsUnique (IsIntegral.of_finite 𝕜 _)⟩
  · rintro ⟨Y, d, hY, hdiag, ⟨D, hD, hBD, hblock⟩, p, hp, -⟩
    let e := Matrix.similarityAlgEquiv Y hY
    have he : e A = Matrix.diagonal d := (Matrix.similarityAlgEquiv_apply_eq_iff Y hY A _).2 hdiag
    have hAdj := Matrix.similarityAlgEquiv_weightedAdjoint_of_block hB.isUnit hY he hD hBD hblock
    refine ⟨hB, (isMinDegreeRepresentation_algEquiv_iff e A (A.weightedAdjoint B) s).1 ?_⟩
    rw [he, hAdj]
    exact ⟨p, hp⟩

/-- The least polynomial degree of a weighted-normal matrix is determined by the
interpolation problem on its eigenvalues and is at most $d_{\min}(A)-1$. Its weight
is admissible and its weighted adjoint conjugates the diagonal in the given
eigenbasis. This is Corollary 4.6.4 of [liesen2013krylov].

The book discusses both real and complex matrices. Here the eigenbasis and interpolating
polynomials are taken over the same algebraically closed field.
-/
theorem corollary_4_6_4 [IsAlgClosed 𝕜] {A B : Matrix n n 𝕜} {s : ℕ}
    (h : IsBNormalOfDegree A B s) :
    s ≤ (minpoly 𝕜 A).natDegree - 1 ∧
      ∃ (Y : Matrix n n 𝕜) (d : n → 𝕜), IsUnit Y ∧
        A = Y * Matrix.diagonal d * Y⁻¹ ∧ AdmissibleEigenbasisMetric B Y d ∧
        A.weightedAdjoint B = Y * (Matrix.diagonal d)ᴴ * Y⁻¹ ∧
        ∀ t : ℕ, (∃ p : 𝕜[X], p.degree = t ∧ (∀ i, p.eval (d i) = star (d i)) ∧
          ∀ q : 𝕜[X], (∀ i, q.eval (d i) = star (d i)) → (t : WithBot ℕ) ≤ q.degree) ↔
          t = s := by
  have hIntegral := IsIntegral.of_finite 𝕜 A
  have hbound := h.2.degree_lt_minpoly hIntegral
  rw [degree_eq_natDegree (minpoly.ne_zero hIntegral)] at hbound
  have hs : s < (minpoly 𝕜 A).natDegree := WithBot.coe_lt_coe.mp hbound
  refine ⟨by omega, ?_⟩
  obtain ⟨Y, d, hY, hdiag, -, -⟩ := (theorem_4_6_3 A B h.1 s).1 h
  obtain ⟨hmetric, hAdj, p, hpdeg, hp, hmin⟩ := h.eigenbasis hY hdiag
  refine ⟨Y, d, hY, hdiag, hmetric, hAdj, ?_⟩
  intro t
  simp only [← aeval_diagonal_eq_conjTranspose_iff]
  constructor
  · rintro ⟨q, hqdeg, hq, hqmin⟩
    have hst := hmin q hq
    have hts := hqmin p hp
    rw [hqdeg] at hst
    rw [hpdeg] at hts
    exact le_antisymm (WithBot.coe_le_coe.mp hts) (WithBot.coe_le_coe.mp hst)
  · rintro rfl
    exact ⟨p, hpdeg, hp, hmin⟩

private theorem exists_ne_of_two_le_minpoly_diagonal {d : n → 𝕜}
    (hdeg : 2 ≤ (minpoly 𝕜 (Matrix.diagonal d)).natDegree) : ∃ i j, d i ≠ d j := by
  by_contra h
  have heq (i j : n) : d i = d j := by
    by_contra hn
    exact h ⟨i, j, hn⟩
  have hc : ∃ c : 𝕜, ∀ i, d i = c := by
    by_cases hn : Nonempty n
    · let i := Classical.choice hn
      exact ⟨d i, fun j => heq j i⟩
    · exact ⟨0, fun i => (hn ⟨i⟩).elim⟩
  obtain ⟨c, hc⟩ := hc
  have hann : aeval (Matrix.diagonal d) (X - C c) = 0 := by
    rw [aeval_diagonal, ← Matrix.diagonal_zero]
    congr 1
    funext i
    simp [hc i]
  have hle := (minpoly.monic (IsIntegral.of_finite 𝕜 (Matrix.diagonal d))).natDegree_le_of_dvd
    (X_sub_C_ne_zero c) (minpoly.dvd 𝕜 (Matrix.diagonal d) hann)
  rw [natDegree_X_sub_C] at hle
  omega

omit [Fintype n] [DecidableEq n] in
private theorem line_of_affine_conjugation {d : n → 𝕜} {α β : 𝕜}
    (h : ∀ i, β * d i + α = star (d i)) (hvals : ∃ i j, d i ≠ d j) :
    ∃ z w : 𝕜, w ≠ 0 ∧ ∀ i, ∃ t : ℝ, d i = z + (t : 𝕜) * w := by
  obtain ⟨i, j, hij⟩ := hvals
  let z := d j
  let w := d i - z
  have hw : w ≠ 0 := sub_ne_zero.mpr hij
  have hline (k : n) : star (d k - z) = β * (d k - z) := by
    change star (d k - d j) = β * (d k - d j)
    rw [star_sub, ← h k, ← h j]
    ring
  have hwstar : star w = β * w := hline i
  have hβ : β ≠ 0 := by
    intro hb
    exact (star_ne_zero.mpr hw) (by simpa [hb] using hwstar)
  refine ⟨z, w, hw, fun k => ?_⟩
  have hr : star ((d k - z) / w) = (d k - z) / w := by
    rw [star_div₀, hline, hwstar, mul_div_mul_left _ _ hβ]
  rw [RCLike.star_def] at hr
  obtain ⟨t, ht⟩ := RCLike.conj_eq_iff_real.mp hr
  have hdiff := (div_eq_iff hw).1 ht
  exact ⟨t, by rw [← hdiff]; ring⟩

private theorem degreeOne_interpolation_of_line {d : n → 𝕜}
    (hvals : ∃ i j, d i ≠ d j)
    (hline : ∃ z w : 𝕜, w ≠ 0 ∧ ∀ i, ∃ t : ℝ, d i = z + (t : 𝕜) * w) :
    IsMinDegreeRepresentation (R := 𝕜) (Matrix.diagonal d) (Matrix.diagonal d)ᴴ 1 := by
  obtain ⟨z, w, hw, hline⟩ := hline
  let β := star w / w
  have hβ : β ≠ 0 := div_ne_zero (star_ne_zero.mpr hw) hw
  have hβw : β * w = star w := div_mul_cancel₀ _ hw
  refine ⟨C β * X + C (star z - β * z), degree_linear hβ, ?_, ?_⟩
  · apply (aeval_diagonal_eq_conjTranspose_iff _ _).2
    intro i
    obtain ⟨t, ht⟩ := hline i
    have hreal : star (t : 𝕜) = t := RCLike.conj_ofReal t
    simp only [eval_add, eval_mul, eval_X, eval_C, ht, star_add, star_mul, hreal]
    calc
      _ = (β * w) * (t : 𝕜) + star z := by ring
      _ = _ := by rw [hβw]; ring
  · intro q hq
    by_contra hn
    have hqdeg : q.degree ≤ 0 := by
      by_cases hzero : q = 0
      · simp [hzero]
      · rw [degree_eq_natDegree hzero] at hn ⊢
        have hsmall : ¬ 1 ≤ q.natDegree := fun h => hn (WithBot.coe_le_coe.mpr h)
        have hnat : q.natDegree ≤ 0 := by omega
        exact WithBot.coe_le_coe.mpr hnat
    have hqc := degree_le_zero_iff.mp hqdeg
    obtain ⟨i, j, hij⟩ := hvals
    have hvals' := (aeval_diagonal_eq_conjTranspose_iff _ _).1 hq
    have hi := hvals' i
    have hj := hvals' j
    rw [hqc, eval_C] at hi hj
    exact hij (star_injective (hi.symm.trans hj))

/-- A matrix is $B$-normal of degree one for some positive definite $B$ if and only
if it can be diagonalized, its minimal polynomial has degree at least two, and its
eigenvalues lie on an affine real line. This is Theorem 4.6.5 (2) of [liesen2013krylov].

The book discusses real and complex matrices. Here, the scalar field is algebraically
closed, and collinearity is expressed by a common affine line with a real parameter.
-/
theorem theorem_4_6_5_one [IsAlgClosed 𝕜] (A : Matrix n n 𝕜) :
    (∃ B, IsBNormalOfDegree A B 1) ↔
      ∃ (Y : Matrix n n 𝕜) (d : n → 𝕜), IsUnit Y ∧
        A = Y * Matrix.diagonal d * Y⁻¹ ∧ 2 ≤ (minpoly 𝕜 A).natDegree ∧
        ∃ z w : 𝕜, w ≠ 0 ∧ ∀ i, ∃ t : ℝ, d i = z + (t : 𝕜) * w := by
  constructor
  · rintro ⟨B, h⟩
    obtain ⟨Y, d, hY, hdiag, -, p, ⟨hpdeg, hp, -⟩, -⟩ :=
      (theorem_4_6_3 A B h.1 1).1 h
    have hb := (corollary_4_6_4 h).1
    have hdeg : 2 ≤ (minpoly 𝕜 A).natDegree := by omega
    have he := (Matrix.similarityAlgEquiv_apply_eq_iff Y hY A _).2 hdiag
    have hmin : minpoly 𝕜 (Matrix.diagonal d) = minpoly 𝕜 A := by
      rw [← he, minpoly.algEquiv_eq]
    have hvals := exists_ne_of_two_le_minpoly_diagonal (hmin ▸ hdeg)
    have hpvalues := (aeval_diagonal_eq_conjTranspose_iff _ _).1 hp
    have hpn : p.natDegree < 2 := by rw [natDegree_eq_of_degree_eq_some hpdeg]; decide
    have hlin (i : n) : p.coeff 1 * d i + p.coeff 0 = star (d i) := by
      simpa [eval_eq_sum_range' hpn, Finset.sum_range_succ, add_comm] using hpvalues i
    exact ⟨Y, d, hY, hdiag, hdeg, line_of_affine_conjugation hlin hvals⟩
  · rintro ⟨Y, d, hY, hdiag, hdeg, hline⟩
    have he := (Matrix.similarityAlgEquiv_apply_eq_iff Y hY A _).2 hdiag
    have hmin : minpoly 𝕜 (Matrix.diagonal d) = minpoly 𝕜 A := by
      rw [← he, minpoly.algEquiv_eq]
    have hvals : ∃ i j, d i ≠ d j :=
      exists_ne_of_two_le_minpoly_diagonal (by simpa [hmin] using hdeg)
    let B := (Y * Yᴴ)⁻¹
    have hYpos : (Y * Yᴴ).PosDef :=
      Matrix.PosDef.mul_conjTranspose_self Y (Matrix.vecMul_injective_iff_isUnit.mpr hY)
    have hB : B.PosDef := hYpos.inv
    have hBD : B⁻¹ = Y * 1 * Yᴴ := by
      rw [mul_one]
      exact Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hYpos.isUnit)
    refine ⟨B, (theorem_4_6_3 A B hB 1).2 ⟨Y, d, hY, hdiag, ⟨1, Matrix.PosDef.one, hBD, ?_⟩, ?_⟩⟩
    · intro i j hij
      exact Matrix.one_apply_ne (fun heq => hij (congrArg d heq))
    · exact (degreeOne_interpolation_of_line hvals hline).existsUnique
        (IsIntegral.of_finite 𝕜 (Matrix.diagonal d))

end Eigenbasis

/-- For a square matrix of positive order, some positive definite $B$ makes $A$
$B$-normal of degree $0$ if and only if $A=\alpha I$ for a nonzero scalar $\alpha$.
This is Theorem 4.6.5 (1) of [liesen2013krylov]. -/
theorem theorem_4_6_5_zero {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n 𝕜) :
    (∃ B, IsBNormalOfDegree A B 0) ↔ ∃ α : 𝕜, α ≠ 0 ∧ A = α • 1 := by
  constructor
  · rintro ⟨B, hB, p, hpdeg, hp, -⟩
    have hC : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero
      (natDegree_eq_of_degree_eq_some hpdeg)
    have hc : p.coeff 0 ≠ 0 := by
      intro h
      have hpzero : p = 0 := by simpa [h] using hC
      simp [hpzero] at hpdeg
    rw [hC, aeval_C, Algebra.algebraMap_eq_smul_one] at hp
    have hdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det _).mp hB.isUnit
    have hconj : Aᴴ = p.coeff 0 • 1 := calc
      Aᴴ = B * (B⁻¹ * Aᴴ * B) * B⁻¹ := by
        symm
        calc
          B * (B⁻¹ * Aᴴ * B) * B⁻¹ = (B * (B⁻¹ * Aᴴ)) * (B * B⁻¹) := by
            simp only [mul_assoc]
          _ = Aᴴ := by
            simp only [← mul_assoc B B⁻¹ Aᴴ, Matrix.mul_nonsing_inv B hdet, one_mul, mul_one]
      _ = p.coeff 0 • 1 := by
        rw [Matrix.weightedAdjoint] at hp
        rw [← hp, mul_smul_comm, smul_mul_assoc, mul_one, Matrix.mul_nonsing_inv _ hdet]
    refine ⟨star (p.coeff 0), star_ne_zero.2 hc, ?_⟩
    simpa only [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one] using congrArg Matrix.conjTranspose hconj
  · rintro ⟨α, hα, rfl⟩
    refine ⟨1, Matrix.PosDef.one, C (star α), degree_C (star_ne_zero.2 hα), ?_, ?_⟩
    · simp [Matrix.weightedAdjoint, Algebra.algebraMap_eq_smul_one]
    · intro q hq
      change (0 : WithBot ℕ) ≤ q.degree
      rw [zero_le_degree_iff]
      intro h
      let i : n := Classical.choice inferInstance
      have hentry := congrArg (fun M : Matrix n n 𝕜 => M i i) hq
      exact (star_ne_zero.2 hα)
        (by simpa [h, Matrix.weightedAdjoint, Matrix.one_apply] using hentry.symm)

end LiesenStrakos

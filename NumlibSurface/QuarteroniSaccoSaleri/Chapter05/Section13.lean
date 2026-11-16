/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Polynomial.Tower
import Numlib.LinearAlgebra.Matrix.Companion
import NumlibSurface.QuarteroniSaccoSaleri.Chapter05.Section08

/-!
# Quarteroni, Sacco and Saleri, Section 5.13: Exercises

This module formalizes the four exercises of Section 5.13 of [quarteroni2000numerical] that the text
of Chapter 5 uses. Exercise 8 identifies the roots of a polynomial with the eigenvalues of its
companion matrix (5.72); Section 5.4 cites it for the impossibility of a direct method for
eigenvalues. Exercise 9 shows that a unitary similarity moves eigenvectors, which justifies Sections
5.8.1–5.8.2. Exercise 10 is the power method with $\alpha_1 = 0$, cited in Section 5.3.3. Exercise
14 gives a matrix that the QR iteration leaves fixed; Section 5.7.2 cites it, and it is the
counterexample to (5.35). The proofs specialize `Numlib.LinearAlgebra.Matrix.Companion`,
`Numlib.LinearAlgebra.Matrix.Schur` and `Numlib.Eigen.PowerMethod`, and use the power method
`QuarteroniSaccoSaleri.Chapter05.powerIterate` of Section 5.3, the QR iteration
`QuarteroniSaccoSaleri.Chapter05.qrIterate` of Section 5.4 and the Rayleigh-shift iteration
`QuarteroniSaccoSaleri.Chapter05.equation_5_53` of Section 5.7.

## Main definitions

* Equation (5.72), `QuarteroniSaccoSaleri.Chapter05.equation_5_72`: the companion matrix of
  $p_n(x) = a_0 + a_1 x + \dots + a_n x^n$.

## Main results

* Equation (5.72), `QuarteroniSaccoSaleri.Chapter05.equation_5_72_eq`: the companion matrix of the
  book is the backbone's `Matrix.companion` of $p_n / a_n$.
* Exercise 8, `QuarteroniSaccoSaleri.Chapter05.exercise_5_8`: the characteristic polynomial of the
  companion matrix is $p_n / a_n$, and its eigenvalues are the roots of $p_n$.
* Exercise 9, `QuarteroniSaccoSaleri.Chapter05.exercise_5_9`: if $Ax = \lambda x$ and $U$ is
  unitary, then $(U^H A U)(U^H x) = \lambda U^H x$.
* Exercise 10, `QuarteroniSaccoSaleri.Chapter05.exercise_5_10`, with
  `QuarteroniSaccoSaleri.Chapter05.sum_repr_sdiff_mem_iSup_maxGenEigenspace`: if $\alpha_1 = 0$, the
  power method converges to $(\lambda_2, x_2)$.
* Exercise 14, `QuarteroniSaccoSaleri.Chapter05.exercise_5_14`: the QR iteration, with and without
  the Rayleigh shift, leaves the cyclic permutation matrix fixed.

## Conventions

* The companion matrix (5.72) is written as the book writes it, from the coefficients $a_k$
  (`p.coeff k`) of a real polynomial $p$ of degree at most $n$ with $a_n \neq 0$.
* The power method and the Rayleigh quotients of Exercise 10 are
  `QuarteroniSaccoSaleri.Chapter05.powerIterate` and
  `QuarteroniSaccoSaleri.Chapter05.rayleighQuotient` of Section 5.3, with a basis `x` of
  eigenvectors and the coordinates $\alpha_i$ = `x.repr q₀ i`, as there.

## Deviations from the source

* **Exercise 10** (reading). The source assumes all the hypotheses of the power method except
  $\alpha_1 \neq 0$; the theorem assumes that $\lambda_2$ dominates the other eigenvalues except
  $\lambda_1$, and $\alpha_2 \neq 0$. See `QuarteroniSaccoSaleri.Chapter05.exercise_5_10`.

## Not formalized

* **Exercises 1–7 and 11–13.** They are numerical, or the text does not use them.
* **Exercise 14, the claim about Program 37.** It is a computation.
-/

open Filter Finset Matrix Polynomial Topology

namespace QuarteroniSaccoSaleri.Chapter05

variable {n : ℕ}

/-! ### Exercise 8: the companion matrix -/

/-- **Equation (5.72)** of [quarteroni2000numerical], the Frobenius (companion) matrix. Let
$p_n(x) = a_0 + a_1 x + \dots + a_n x^n$ with $a_n \neq 0$. Its **companion matrix**
$C \in \mathbb{R}^{n \times n}$ has the first row $$\Big(-\frac{a_{n-1}}{a_n},
-\frac{a_{n-2}}{a_n}, \dots, -\frac{a_0}{a_n}\Big),$$ ones on the subdiagonal, and zeros
elsewhere.

The Lean definition takes any real polynomial `p` and any `n`, with $a_k$ = `p.coeff k`. If
$a_n = 0$, the first row is zero, by the convention that division by zero gives zero. -/
noncomputable def equation_5_72 (p : ℝ[X]) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun i j =>
    if (i : ℕ) = 0 then -(p.coeff (n - 1 - j) / p.coeff n) else if (i : ℕ) = j + 1 then 1 else 0

/-- For every real polynomial $p$ and every $n$, the companion matrix (5.72) of
[quarteroni2000numerical] is the backbone's `Matrix.companion` of the polynomial $p / a_n$,
which is monic when $p$ has degree $n$. -/
theorem equation_5_72_eq (p : ℝ[X]) (n : ℕ) :
    equation_5_72 p n = companion (C (p.coeff n)⁻¹ * p) n := by
  ext i j
  simp [equation_5_72, companion_apply, coeff_C_mul, div_eq_inv_mul]

/-- **Exercise 8** of [quarteroni2000numerical]. Let $p_n(x) = \sum_{k=0}^n a_k x^k$ be a real
polynomial of degree at most $n$ with $a_n \neq 0$, and let $C$ be its companion matrix (5.72).
Then the characteristic polynomial of $C$ is $p_n / a_n$, and a complex number $z$ is an
eigenvalue of $C$ if and only if $p_n(z) = 0$. So finding the zeros of $p_n$ is equivalent to
finding the spectrum of $C$.

The real matrix $C$ acts on $\mathbb{C}^n$ through `Matrix.map` with `algebraMap ℝ ℂ`. The proof
specializes `Matrix.charpoly_companion` and `Matrix.spectrum_companion`. The consequence that
the text draws in Section 5.4, that by Abel's theorem no direct method computes the eigenvalues
of a general matrix of order $n \ge 5$, is not formalized. -/
theorem exercise_5_8 {p : ℝ[X]} (hdeg : p.natDegree ≤ n) (ha : p.coeff n ≠ 0) :
    (equation_5_72 p n).charpoly = C (p.coeff n)⁻¹ * p ∧
      ∀ z : ℂ, z ∈ spectrum ℂ ((equation_5_72 p n).map (algebraMap ℝ ℂ)) ↔ aeval z p = 0 := by
  have hn : p.natDegree = n := natDegree_eq_of_le_of_coeff_ne_zero hdeg ha
  have hlead : p.leadingCoeff = p.coeff n := by rw [leadingCoeff, hn]
  have hq : (C (p.coeff n)⁻¹ * p).Monic :=
    monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [hlead, inv_mul_cancel₀ ha])
  have hqn : (C (p.coeff n)⁻¹ * p).natDegree = n := by
    rw [natDegree_C_mul (inv_ne_zero ha), hn]
  refine ⟨by rw [equation_5_72_eq, charpoly_companion hq hqn], fun z => ?_⟩
  have hmap : (equation_5_72 p n).map (algebraMap ℝ ℂ) =
      companion ((C (p.coeff n)⁻¹ * p).map (algebraMap ℝ ℂ)) n := by
    rw [equation_5_72_eq]
    ext i j
    simp only [map_apply, companion_apply, coeff_map]
    split_ifs <;> simp
  rw [hmap, spectrum_companion (hq.map _) (by rw [natDegree_map, hqn]),
    mem_rootSet_of_ne (Polynomial.map_ne_zero hq.ne_zero), aeval_map_algebraMap, aeval_mul,
    aeval_C, mul_eq_zero, map_eq_zero_iff _ (algebraMap ℝ ℂ).injective]
  exact or_iff_right (inv_ne_zero ha)

/-! ### Exercise 9: unitary similarity -/

/-- **Exercise 9** of [quarteroni2000numerical]. Let $A \in \mathbb{C}^{n \times n}$,
$\lambda \in \mathbb{C}$ and $x \in \mathbb{C}^n$ with $Ax = \lambda x$, and let
$U \in \mathbb{C}^{n \times n}$ be unitary. Then the matrix $U^H A U$, which is similar to $A$
by a unitary matrix, satisfies $$(U^H A U)(U^H x) = \lambda\, U^H x.$$

The statement does not assume $x \neq 0$. The proof specializes
`Matrix.mulVec_star_conj_eq_smul_of_mulVec_eq_smul`. -/
theorem exercise_5_9 {A U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    {lam : ℂ} {x : Fin n → ℂ} (hx : A *ᵥ x = lam • x) :
    (Uᴴ * A * U) *ᵥ (Uᴴ *ᵥ x) = lam • (Uᴴ *ᵥ x) := by
  have h := mulVec_star_conj_eq_smul_of_mulVec_eq_smul hU hx
  rwa [star_eq_conjTranspose] at h

/-! ### Exercise 10: the power method with $\alpha_1 = 0$ -/

/-- Let $A \in \mathbb{C}^{n \times n}$ have a basis $x_1, \dots, x_n$ of eigenvectors with
eigenvalues $\lambda_1, \dots, \lambda_n$, let $q^{(0)} = \sum_i \alpha_i x_i$, let $s$ be a set
of indices, and let $P$ be a property of complex numbers that holds at $\lambda_i$ for every
$i \notin s$. Then $\sum_{i \notin s} \alpha_i x_i$ lies in the sum of the generalized
eigenspaces of $A$ for the eigenvalues $\mu$ with $P(\mu)$. This supports Exercise 10 of
[quarteroni2000numerical].

It generalizes `QuarteroniSaccoSaleri.Chapter05.sum_repr_erase_mem_iSup_maxGenEigenspace` of
Section 5.3 from one removed index to a set $s$ of indices. -/
theorem sum_repr_sdiff_mem_iSup_maxGenEigenspace {A : Matrix (Fin n) (Fin n) ℂ}
    (x : Module.Basis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) {lam : Fin n → ℂ}
    (hx : ∀ i, toEuclideanLin A (x i) = lam i • x i) (q₀ : EuclideanSpace ℂ (Fin n))
    (s : Finset (Fin n)) {p : ℂ → Prop} (hs : ∀ i ∉ s, p (lam i)) :
    ∑ i ∈ univ \ s, x.repr q₀ i • x i ∈
      ⨆ μ, ⨆ _ : p μ, Module.End.maxGenEigenspace (toEuclideanLin A) μ := by
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
  have hi' : i ∉ s := (Finset.mem_sdiff.mp hi).2
  exact Submodule.mem_iSup_of_mem (lam i) (Submodule.mem_iSup_of_mem (hs i hi')
    (Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr (hx i))))

/-- **Exercise 10** of [quarteroni2000numerical]. Let $A \in \mathbb{C}^{n \times n}$ have a basis
$x_1, \dots, x_n$ of eigenvectors with eigenvalues $\lambda_1, \dots, \lambda_n$ (so $A$ is
diagonalizable), and assume $\lambda_2 \neq 0$ and $|\lambda_i| < |\lambda_2|$ for every
$i \neq 1, 2$. Let $q^{(0)} = \sum_i \alpha_i x_i$ be a unit vector with $\alpha_1 = 0$ and
$\alpha_2 \neq 0$. Then the power method (5.17) converges to the eigenvalue and eigenvector pair
$(\lambda_2, x_2)$: $$c_k\, q^{(k)} \to \frac{x_2}{\|x_2\|_2}, \qquad c_k =
\Big(\frac{|\lambda_2|}{\lambda_2}\Big)^k \frac{|\alpha_2|}{\alpha_2},$$ where the scalars $c_k$
have modulus one, and the Rayleigh quotients satisfy $\nu^{(k)} \to \lambda_2$.

**Reading.** The source assumes "all the assumptions needed to apply the power method except
$\alpha_1 \neq 0$" and concludes convergence to $(\lambda_2, x_2)$. For this, $\lambda_2$ must
dominate the eigenvalues that occur in $q^{(0)}$, so the theorem assumes
$|\lambda_2| > |\lambda_i|$ for $i \ge 3$ and $\alpha_2 \neq 0$. The hypotheses of Theorem 5.6
would require the dominant eigenvalue to dominate all eigenvalues of $A$, which $\lambda_2$ does
not.

The indices $1$ and $2$ of the book are `i₀` and `i₁`, with `i₁ ≠ i₀`. The proof specializes
`Krylov.tendsto_smul_powerIterate_of_mem_iSup`, the form of the power method in which the
domination is needed only on the generalized eigenspaces that the starting vector meets. -/
theorem exercise_5_10 {A : Matrix (Fin n) (Fin n) ℂ}
    (x : Module.Basis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) {lam : Fin n → ℂ}
    (hx : ∀ i, toEuclideanLin A (x i) = lam i • x i) {i₀ i₁ : Fin n} (hi : i₁ ≠ i₀)
    (hl₁ : lam i₁ ≠ 0) (hdom : ∀ i, i ≠ i₀ → i ≠ i₁ → ‖lam i‖ < ‖lam i₁‖)
    {q₀ : EuclideanSpace ℂ (Fin n)} (hq₀ : ‖q₀‖ = 1) (hα₁ : x.repr q₀ i₀ = 0)
    (hα₂ : x.repr q₀ i₁ ≠ 0) :
    Tendsto (fun k => (((‖lam i₁‖ : ℂ) / lam i₁) ^ k * (‖x.repr q₀ i₁‖ / x.repr q₀ i₁)) •
        powerIterate A q₀ k) atTop (𝓝 ((‖x i₁‖ : ℂ)⁻¹ • x i₁)) ∧
      Tendsto (fun k => rayleighQuotient A (powerIterate A q₀ k)) atTop (𝓝 (lam i₁)) := by
  -- the splitting of the starting vector
  set u := x.repr q₀ i₁ • x i₁ with hu_def
  have hu : toEuclideanLin A u = lam i₁ • u := by rw [map_smul, hx, smul_comm]
  have hu0 : u ≠ 0 := smul_ne_zero hα₂ (x.ne_zero i₁)
  have hi' : i₀ ≠ i₁ := hi.symm
  have hsplit : q₀ = u + ∑ i ∈ univ \ {i₀, i₁}, x.repr q₀ i • x i := by
    conv_lhs => rw [← x.sum_repr q₀]
    rw [← Finset.sum_sdiff (Finset.subset_univ {i₀, i₁}), Finset.sum_pair hi', hα₁, zero_smul,
      zero_add, add_comm]
  have hne : ∀ i ∉ ({i₀, i₁} : Finset (Fin n)), ‖lam i‖ < ‖lam i₁‖ := fun i hi' => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi'
    exact hdom i hi'.1 hi'.2
  have hw := sum_repr_sdiff_mem_iSup_maxGenEigenspace x hx q₀ {i₀, i₁}
    (p := fun μ => ‖μ‖ < ‖lam i₁‖) hne
  -- a rate strictly between the subdominant moduli and `‖λ₂‖`
  set S : Finset (Fin n) := univ.filter fun i => ‖lam i‖ < ‖lam i₁‖ with hS
  set m : NNReal := S.sup fun i => ‖lam i‖₊ with hm
  have hmlt : m < ‖lam i₁‖₊ := by
    rw [hm, Finset.sup_lt_iff (bot_lt_iff_ne_bot.mpr (nnnorm_ne_zero_iff.mpr hl₁))]
    intro i hi
    rw [hS, Finset.mem_filter] at hi
    exact_mod_cast hi.2
  have hmlt' : (m : ℝ) < ‖lam i₁‖ := by exact_mod_cast hmlt
  set r : ℝ := ((m : ℝ) + ‖lam i₁‖) / 2 with hr
  have hr0 : 0 ≤ r := by positivity
  have hrl : r < ‖lam i₁‖ := by rw [hr]; linarith
  have hdom' : ∀ μ, ‖μ‖ < ‖lam i₁‖ → Module.End.HasEigenvalue (toEuclideanLin A) μ →
      ‖μ‖ < r := fun μ hμ hev => by
    have hμ' : μ ∈ Set.range lam := by
      rw [← Module.End.spectrum_eq_range_of_basis x hx]
      exact Module.End.hasEigenvalue_iff_mem_spectrum.mp hev
    obtain ⟨i, rfl⟩ := hμ'
    have hiS : i ∈ S := by
      rw [hS, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hμ⟩
    have hle : ‖lam i‖ ≤ (m : ℝ) := by
      rw [hm]
      exact_mod_cast Finset.le_sup (f := fun i => ‖lam i‖₊) hiS
    rw [hr]; linarith
  obtain ⟨hlim, hray⟩ := Krylov.tendsto_smul_powerIterate_of_mem_iSup
    (LinearMap.continuous_of_finiteDimensional _) hl₁ hu hu0 hw hr0 hrl hdom' hsplit
  simp only [powerIterate_eq_krylov A hq₀, rayleighQuotient]
  refine ⟨?_, hray⟩
  -- the phase of `α₂` is absorbed into `c_k`
  have hαn : (‖x.repr q₀ i₁‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hα₂)
  have hcoe : ∀ s : ℝ, (RCLike.ofReal s : ℂ) = (s : ℂ) := fun s => rfl
  simp only [hcoe] at hlim
  have hval : (‖x.repr q₀ i₁‖ / x.repr q₀ i₁ : ℂ) • ((‖u‖ : ℂ)⁻¹ • u) = (‖x i₁‖ : ℂ)⁻¹ • x i₁ := by
    rw [hu_def, norm_smul, smul_smul, smul_smul, Complex.ofReal_mul, mul_inv]
    congr 1
    field_simp
  have h := hlim.const_smul ((‖x.repr q₀ i₁‖ : ℂ) / x.repr q₀ i₁)
  rw [hval] at h
  refine h.congr fun k => ?_
  rw [smul_smul, mul_comm]

/-! ### Exercise 14: a matrix that the QR iteration leaves fixed -/

/-- **Exercise 14** of [quarteroni2000numerical]. Let $$A = \begin{bmatrix} 0 & 0 & 1 \\ 1 & 0 & 0
\\ 0 & 1 & 0 \end{bmatrix}$$ be the cyclic permutation matrix. The QR factorization of $A$ is
$Q = A$, $R = I$, because the columns of $A$ are already orthonormal. Hence the QR iteration
leaves $A$ unchanged, $T^{(k)} = A$ for all $k$, and so does the QR iteration (5.53) with the
Rayleigh shift $\mu = t_{33}^{(k)} = 0$. The eigenvalues of $A$ are the solutions of
$\lambda^3 = 1$, and all have modulus one. Finally, $A$ is not upper triangular, so the
iteration does not approach the conclusion of Property 5.9 or a real Schur form.

The factors are `Matrix.qrQ A` and `Matrix.qrR A`, and the iterations are
`QuarteroniSaccoSaleri.Chapter05.qrIterate` and `QuarteroniSaccoSaleri.Chapter05.equation_5_53`.
The spectrum is taken over $\mathbb{C}$ through `algebraMap ℝ ℂ`. The claim of the exercise
about Program 37, the double-shift variant, which changes only signs, is not formalized. -/
theorem exercise_5_14 :
    let A : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 1; 1, 0, 0; 0, 1, 0]
    qrQ A = A ∧ qrR A = 1 ∧ (∀ k, qrIterate A k = A) ∧ (∀ k, equation_5_53 A k = A) ∧
      (∀ z : ℂ, z ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)) ↔ z ^ 3 = 1) ∧
      (∀ z ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)), ‖z‖ = 1) ∧ ¬ A.IsUpperTriangular := by
  intro A
  have hAA : Aᴴ * A = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A, Matrix.mul_apply, Fin.sum_univ_three]
  have hqr : qrQ A = A ∧ qrR A = 1 :=
    IsThinQR.unique ⟨qrQ_mul_qrR A, conjTranspose_qrQ_mul_self A, isUpperTriangular_qrR A⟩
      ⟨Matrix.mul_one A, hAA, blockTriangular_one⟩
      (qrR_diag_pos ((isUnit_iff_isUnit_det A).mp (isUnit_of_mem_unitaryGroup
        (mem_unitaryGroup_iff'.mpr (by rw [star_eq_conjTranspose]; exact hAA)))))
      (fun j => by simp)
  have hfix : ∀ k, qrIterate A k = A := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [qrIterate, ih, hqr.1, hqr.2, Matrix.one_mul]
  have hfix' : ∀ k, equation_5_53 A k = A := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [equation_5_53, ih, show A (Fin.last 2) (Fin.last 2) = 0 by simp [A], shiftedQrStep,
        zero_smul, sub_zero, add_zero, hqr.1, hqr.2, Matrix.one_mul]
  have hspec : ∀ z : ℂ, z ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)) ↔ z ^ 3 = 1 := by
    have hmap : A.map (algebraMap ℝ ℂ) = companion (X ^ 3 - 1 : ℂ[X]) 3 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [A, companion_apply, coeff_X_pow, coeff_one]
    have hmonic : (X ^ 3 - 1 : ℂ[X]).Monic := monic_X_pow_sub_C 1 (by norm_num)
    have hdeg : (X ^ 3 - 1 : ℂ[X]).natDegree = 3 := natDegree_X_pow_sub_C 1
    intro z
    rw [hmap, spectrum_companion hmonic hdeg, mem_rootSet_of_ne hmonic.ne_zero, aeval_sub,
      aeval_X_pow, aeval_one, sub_eq_zero]
  refine ⟨hqr.1, hqr.2, hfix, hfix', hspec, fun z hz => ?_, fun h => ?_⟩
  · have h3 : ‖z‖ ^ 3 = 1 := by rw [← norm_pow, (hspec z).mp hz, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) (by norm_num)).mp h3
  · have := h (show (0 : Fin 3) < 1 by decide)
    simp [A] at this

end QuarteroniSaccoSaleri.Chapter05

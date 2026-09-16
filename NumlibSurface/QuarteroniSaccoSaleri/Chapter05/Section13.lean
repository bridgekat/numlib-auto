import Mathlib.RingTheory.Polynomial.Tower
import Numlib.LinearAlgebra.Matrix.Companion
import NumlibSurface.QuarteroniSaccoSaleri.Chapter05.Section08

/-!
# Quarteroni–Sacco–Saleri §5.13: exercises

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §5.13, the four exercises the text uses: Exercise 8 (the companion
matrix, cited in §5.4 for the impossibility of a direct eigenvalue method), Exercise 9 (unitary
similarity moves eigenvectors, the justification of §5.8.1–5.8.2), Exercise 10 (the power method
with `α₁ = 0`, cited in §5.3.3) and Exercise 14 (a matrix the QR iteration leaves fixed, cited in
§5.7.2 and the counterexample to (5.35)). Over the backbone `Numlib/LinearAlgebra/Matrix/Companion`,
`Numlib/LinearAlgebra/Matrix/Schur` and `Numlib/Eigen/PowerMethod`, and over §5.3's `powerIterate`,
§5.4's `qrIterate` and §5.7's Rayleigh-shift iteration.

## Conventions

The companion matrix (5.72) is written as the book writes it, `equation_5_72 p n`, from the
coefficients `a_k = p.coeff k` of a real polynomial `p` of degree `≤ n` with `a_n ≠ 0`, and
`equation_5_72_eq` identifies it with the backbone's `Matrix.companion` of the monic polynomial
`p / a_n`. The power method and Rayleigh quotients of Exercise 10 are `powerIterate` and
`rayleighQuotient` of §5.3, with a basis `x` of eigenvectors and the coordinates `α_i = x.repr q₀ i`
as there. Exercises 1–7 and 11–13 are numerical or are not used by the text.

## Contents

* `equation_5_72`, `equation_5_72_eq`, `exercise_5_8` — the companion matrix and the roots of a
  polynomial as eigenvalues.
* `exercise_5_9` — `(λ, Uᴴ x)` is an eigenpair of `Uᴴ A U`.
* `sum_repr_sdiff_mem_iSup_maxGenEigenspace`, `exercise_5_10` — the power method converges to
  the eigenpair dominant *among the components present in `q⁽⁰⁾`*.
* `exercise_5_14` — the cyclic permutation matrix is fixed by the QR iteration, with and without
  the Rayleigh shift, and its eigenvalues are the cube roots of unity.

## Readings

Exercise 10 assumes "all the assumptions needed to apply the power method except `α₁ ≠ 0`" and
concludes convergence to `(λ₂, x₂)`; for that `λ₂` must dominate the eigenvalues that do occur in
`q⁽⁰⁾`, `|λ₂| > |λ_i|` for `i ≥ 3`, which is the hypothesis stated, together with `α₂ ≠ 0`.
The backbone's power-method theorem asks the dominant eigenvalue to dominate *all* eigenvalues of
`A`, which `λ₂` does not; the backbone's `Krylov.tendsto_smul_powerIterate_of_mem_iSup` is the
form with the domination restricted to the generalized eigenspaces the starting vector meets.
Exercise 14's claim about Program 37 (the double-shift variant) is a computation and is not a
node.
-/

open Filter Finset Matrix Polynomial Topology

namespace QuarteroniSaccoSaleri.Chapter05

variable {n : ℕ}

/-! ### Exercise 8: the companion matrix -/

/-- **(5.72), the Frobenius (companion) matrix** of `p_n(x) = a₀ + a₁ x + … + a_n xⁿ`, `a_n ≠ 0`:
first row `(−a_{n−1}/a_n, −a_{n−2}/a_n, …, −a₀/a_n)`, ones on the subdiagonal, zeros elsewhere. -/
noncomputable def equation_5_72 (p : ℝ[X]) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun i j =>
    if (i : ℕ) = 0 then -(p.coeff (n - 1 - j) / p.coeff n) else if (i : ℕ) = j + 1 then 1 else 0

/-- **The book's companion matrix is the backbone's**, `Matrix.companion` of the monic polynomial
`p / a_n`. -/
theorem equation_5_72_eq (p : ℝ[X]) (n : ℕ) :
    equation_5_72 p n = companion (C (p.coeff n)⁻¹ * p) n := by
  ext i j
  simp [equation_5_72, companion_apply, coeff_C_mul, div_eq_inv_mul]

/-- **Exercise 8.** Finding the zeros of a polynomial `p_n(x) = ∑_{k=0}^n a_k x^k` of degree `≤ n`
with real coefficients and `a_n ≠ 0` is equivalent to determining the spectrum of its companion
matrix `C` (5.72): the characteristic polynomial of `C` is `p_n / a_n`, so a complex number is an
eigenvalue of `C` exactly when it is a root of `p_n`. Backbone `Matrix.charpoly_companion` and
`Matrix.spectrum_companion`. The consequence the text draws in §5.4 — by Abel's theorem, no direct
method computes the eigenvalues of a general matrix of order `n ≥ 5` — is not a node. -/
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

/-- **Exercise 9.** If `A ∈ ℂ^{n×n}` admits the eigenvalue/eigenvector pair `(λ, x)`, `A x = λ x`,
then for a unitary `U` the matrix `Uᴴ A U` admits the pair `(λ, Uᴴ x)`: a similarity
transformation by a unitary matrix. Backbone `Matrix.mulVec_star_conj_eq_smul_of_mulVec_eq_smul`.
-/
theorem exercise_5_9 {A U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    {lam : ℂ} {x : Fin n → ℂ} (hx : A *ᵥ x = lam • x) :
    (Uᴴ * A * U) *ᵥ (Uᴴ *ᵥ x) = lam • (Uᴴ *ᵥ x) := by
  have h := mulVec_star_conj_eq_smul_of_mulVec_eq_smul hU hx
  rwa [star_eq_conjTranspose] at h

/-! ### Exercise 10: the power method with `α₁ = 0` -/

/-- The components of `q₀ = ∑ α_i x_i` outside a set `s` of indices lie in the span of the
generalized eigenspaces of the eigenvalues `λ_i`, `i ∉ s`: the `p`-general form of
`sum_repr_erase_mem_iSup_maxGenEigenspace`. -/
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

/-- **Exercise 10.** Suppose the assumptions of Theorem 5.6 hold except that `α₁ = 0` — with
`A` diagonalizable, `x_i` a basis of eigenvectors with eigenvalues `λ_i` (indices `i₀` for `1`,
`i₁` for `2`), `q⁽⁰⁾ = ∑ α_i x_i` a unit vector, `α₁ = 0`, `α₂ ≠ 0`, and `|λ₂| > |λ_i|` for
`i ≥ 3`, `λ₂ ≠ 0`. Then the sequence (5.17) converges to the eigenvalue/eigenvector pair
`(λ₂, x₂)`: `c_k • q⁽ᵏ⁾ → x₂/‖x₂‖₂` for the unimodular scalars
`c_k = (|λ₂|/λ₂)^k |α₂|/α₂`, and `ν⁽ᵏ⁾ → λ₂`. The power method never needed `λ₂` to dominate the
spectrum of `A`, only the components present in `q⁽⁰⁾`
(`Krylov.tendsto_smul_powerIterate_of_mem_iSup`). -/
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

/-! ### Exercise 14: a matrix the QR iteration leaves fixed -/

/-- **Exercise 14.** For the cyclic permutation matrix `A = [0 0 1; 1 0 0; 0 1 0]` the QR
iteration leaves `A` unchanged: `Q⁽ᵏ⁾ = A` and `R⁽ᵏ⁾ = I` at every step (the columns of `A` are
already orthonormal), so `T⁽ᵏ⁾ = A` for all `k`, and the same holds for the QR iteration with the
Rayleigh shift `μ = t_nn^{(k)} = 0` of (5.53). The eigenvalues of `A` are the solutions of
`λ³ − 1 = 0`, `σ(A) = {1, −1/2 ± i√3/2}`, all of modulus one, so neither Property 5.9 nor the
real Schur form is approached: the iterate `A` is not upper triangular. (Program 37, the
double-shift variant, changes only signs; that computation is not a node.) -/
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
    qr_unique (qrQ_mul_qrR A).symm (Matrix.mul_one A).symm (conjTranspose_qrQ_mul_self A) hAA
      (isUpperTriangular_qrR A) blockTriangular_one
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
    have hdeg : (X ^ 3 - 1 : ℂ[X]).natDegree = 3 := natDegree_X_pow_sub_C
    intro z
    rw [hmap, spectrum_companion hmonic hdeg, mem_rootSet_of_ne hmonic.ne_zero, aeval_sub,
      aeval_X_pow, aeval_one, sub_eq_zero]
  refine ⟨hqr.1, hqr.2, hfix, hfix', hspec, fun z hz => ?_, fun h => ?_⟩
  · have h3 : ‖z‖ ^ 3 = 1 := by rw [← norm_pow, (hspec z).mp hz, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) (by norm_num)).mp h3
  · have := h (show (0 : Fin 3) < 1 by decide)
    simp [A] at this

end QuarteroniSaccoSaleri.Chapter05

import NumlibSurface.QuarteroniSaccoSaleri.Chapter05.Section02

/-!
# Quarteroni–Sacco–Saleri §5.3: the power method

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §5.3, over the backbone `Numlib/Eigen/PowerMethod` (the power iteration
in closed form, its convergence and rate, the Rayleigh quotients, the symmetric rate, inverse
iteration) and `Numlib/Eigen/Perturbation` (the backward error of an approximate eigenpair).

## Conventions

The book's `A ∈ ℂ^{n×n}` is `Matrix (Fin n) (Fin n) ℂ` acting on `EuclideanSpace ℂ (Fin n)` through
`Matrix.toEuclideanLin`; the iterations are stated for any `RCLike` field so that the real
symmetric estimate (5.23) reads on `Matrix (Fin n) (Fin n) ℝ`. The power method (5.17) and inverse
iteration (5.28) are written as the book writes them, as recursions `powerIterate` and
`inverseIterate` normalizing after every step, and `powerIterate_eq_krylov`,
`inverseIterate_eq_krylov` identify them with the closed forms `Krylov.powerIterate`,
`Krylov.inverseIterate` of the backbone; the Rayleigh quotients `ν^(k) = (q^(k))ᴴ A q^(k)` and
`σ^(k)` are `rayleighQuotient`. A diagonalizable `A` with the matrix of eigenvectors
`X = (x_1, …, x_n)` is given by a basis `x : Module.Basis (Fin n) ℂ ℂⁿ` of eigenvectors with
eigenvalues `lam`, and the coefficients `α_i` of (5.19) are the coordinates `x.repr q₀ i`. The
ordering (5.16) is carried by two indices: `i₀` (the book's `1`, the dominant eigenvalue) and `i₁`
(the book's `2`), with `‖λ_i‖ ≤ ‖λ_{i₁}‖ < ‖λ_{i₀}‖` for `i ≠ i₀`.

## Contents

* `powerIterate`, `rayleighQuotient`, `powerIterate_eq_krylov`, `equation_5_18` — the method
  (5.17) and its closed form.
* `theorem_5_6`, `theorem_5_6_rayleigh` — the rate (5.21) and `ν^(k) → λ_1`.
* `equation_5_23` — the symmetric case.
* `equation_5_24` — `ν^(k)` is an exact eigenvalue of `A + ε E^(k)` with `ε = ‖r^(k)‖₂`.
* `inverseIterate`, `inverseIterate_eq_krylov`, `inverseIterate_tendsto` — inverse iteration
  (5.28) and its convergence.
* `powerIterate_of_eq` — §5.3.3, coincident dominant eigenvalues.

## Readings and errata

Theorem 5.6's constant `C = (∑_{i ≥ 2} (α_i/α_1)²)^{1/2}` comes from the step
`‖∑ c_i x_i‖₂ ≤ (∑ c_i²)^{1/2}`, which needs the eigenvectors orthonormal (a normal `A`); for a
diagonalizable `A` the triangle inequality gives `C = ∑_{i ≥ 2} |α_i/α_1|`, which is what is proved.
In (5.23) the factor `|λ_1 − λ_n|` is the spread `λ_max − λ_min` of the spectrum: with the modulus
ordering (5.16) it is false as printed (`A = diag(3, −2, 1)` has `|λ_1 − λ_3| = 2` while the error
constant is `5`); the statement here has `(⨆ λ_i) − (⨅ λ_i)`. The a posteriori estimates
(5.25), (5.26) and (5.29) are heuristic (`≃`) and are not nodes; Example 5.3 is numerical.
-/

open Filter Finset Matrix Topology
open scoped Matrix.Norms.L2Operator

namespace QuarteroniSaccoSaleri.Chapter05

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-! ### Bridges to the backbone -/

-- TODO(backbone): the operator form of `Matrix.isSimilar_diagonal_iff_exists_basis_eigenvectors`;
-- natural home `Numlib/LinearAlgebra/Matrix/Similar` or `Numlib/Eigen/PowerMethod`.
/-- The spectrum of an endomorphism with a basis of eigenvectors `b i`, `f (b i) = lam i • b i`, is
the set of the `lam i`: in the basis `b` the endomorphism is the diagonal matrix of the `lam i`,
whose spectrum is `Set.range lam`. -/
theorem spectrum_eq_range_of_basis {E : Type*} [AddCommGroup E] [Module 𝕜 E] {ι : Type*}
    [Finite ι] {f : Module.End 𝕜 E} (b : Module.Basis ι 𝕜 E) {lam : ι → 𝕜}
    (hb : ∀ i, f (b i) = lam i • b i) : spectrum 𝕜 f = Set.range lam := by
  cases nonempty_fintype ι
  classical
  have hmat : LinearMap.toMatrixAlgEquiv b f = diagonal lam := by
    ext i j
    rw [LinearMap.toMatrixAlgEquiv_apply, hb, map_smul, Finsupp.smul_apply, b.repr_self,
      Finsupp.single_apply, diagonal_apply, smul_eq_mul]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [← AlgEquiv.spectrum_eq (LinearMap.toMatrixAlgEquiv b), hmat, spectrum_diagonal]

-- TODO(backbone): natural home `Numlib/Analysis/Matrix/ToEuclideanLin`, beside
-- `Matrix.toEuclideanCLM_nonsing_inv`, of which this is the `Module.End` form.
/-- For a nonsingular `M`, `toEuclideanLin M` is a unit of `Module.End` with `Ring.inverse` equal
to `toEuclideanLin M⁻¹`. -/
theorem ringInverse_toEuclideanLin {M : Matrix (Fin n) (Fin n) 𝕜} (hM : IsUnit M) :
    IsUnit (toEuclideanLin M) ∧ Ring.inverse (toEuclideanLin M) = toEuclideanLin M⁻¹ := by
  have hdet := (isUnit_iff_isUnit_det M).mp hM
  let u : (Module.End 𝕜 (EuclideanSpace 𝕜 (Fin n)))ˣ :=
    ⟨toEuclideanLin M, toEuclideanLin M⁻¹,
      by rw [Module.End.mul_eq_comp, ← toEuclideanLin_mul, mul_nonsing_inv M hdet,
        toEuclideanLin_one, Module.End.one_eq_id],
      by rw [Module.End.mul_eq_comp, ← toEuclideanLin_mul, nonsing_inv_mul M hdet,
        toEuclideanLin_one, Module.End.one_eq_id]⟩
  exact ⟨⟨u, rfl⟩, Ring.inverse_unit u⟩

/-- The shift `A − μ I` is nonsingular exactly when `μ ∉ σ(A)`. -/
theorem isUnit_sub_smul_one_of_notMem_spectrum {A : Matrix (Fin n) (Fin n) 𝕜} {μ : 𝕜}
    (hμ : μ ∉ spectrum 𝕜 A) : IsUnit (A - μ • (1 : Matrix (Fin n) (Fin n) 𝕜)) := by
  have h := (spectrum.notMem_iff.mp hμ).neg
  rwa [Algebra.algebraMap_eq_smul_one, neg_sub] at h

/-! ### (5.17): the power method -/

/-- **(5.17), the power method.** Given `q^(0) ∈ ℂⁿ` of unit Euclidean norm, for `k = 1, 2, …`:
`z^(k) = A q^(k−1)`, `q^(k) = z^(k) / ‖z^(k)‖₂`; the Rayleigh quotient `ν^(k) = (q^(k))ᴴ A q^(k)` is
`rayleighQuotient`. The normalization `(0 : ℝ)⁻¹ = 0` makes the recursion total. -/
noncomputable def powerIterate (A : Matrix (Fin n) (Fin n) 𝕜) (q₀ : EuclideanSpace 𝕜 (Fin n)) :
    ℕ → EuclideanSpace 𝕜 (Fin n)
  | 0 => q₀
  | k + 1 =>
    (‖toEuclideanLin A (powerIterate A q₀ k)‖ : 𝕜)⁻¹ • toEuclideanLin A (powerIterate A q₀ k)

/-- The Rayleigh quotient `qᴴ A q` of a vector `q`: the `ν^(k) = (q^(k))ᴴ A q^(k)` of (5.17) at
`q = q^(k)` and the `σ^(k)` of (5.28) at the inverse iterate. -/
noncomputable def rayleighQuotient (A : Matrix (Fin n) (Fin n) 𝕜) (q : EuclideanSpace 𝕜 (Fin n)) :
    𝕜 :=
  inner 𝕜 q (toEuclideanLin A q)

/-- **The book's recursion (5.17) is the backbone's closed form**: from a unit `q^(0)`,
`powerIterate A q₀ k = Krylov.powerIterate (toEuclideanLin A) q₀ k`
(`Krylov.eq_powerIterate_of_recurrence`). -/
theorem powerIterate_eq_krylov (A : Matrix (Fin n) (Fin n) 𝕜) {q₀ : EuclideanSpace 𝕜 (Fin n)}
    (hq₀ : ‖q₀‖ = 1) (k : ℕ) : powerIterate A q₀ k = Krylov.powerIterate (toEuclideanLin A) q₀ k :=
  Krylov.eq_powerIterate_of_recurrence (toEuclideanLin A) q₀ (y := powerIterate A q₀)
    (by simp [powerIterate, hq₀]) (fun _ => rfl) k

/-- **(5.18).** `q^(k) = A^k q^(0) / ‖A^k q^(0)‖₂` (for every `k`, given `‖q^(0)‖₂ = 1`):
`Krylov.powerIterate_eq_smul`. -/
theorem equation_5_18 (A : Matrix (Fin n) (Fin n) 𝕜) {q₀ : EuclideanSpace 𝕜 (Fin n)}
    (hq₀ : ‖q₀‖ = 1) (k : ℕ) :
    powerIterate A q₀ k =
      (‖toEuclideanLin (A ^ k) q₀‖ : 𝕜)⁻¹ • toEuclideanLin (A ^ k) q₀ := by
  rw [powerIterate_eq_krylov A hq₀, Krylov.powerIterate_eq_smul, toEuclideanLin_pow]

/-- `‖A^k q^(0)‖₂ q^(k) = A^k q^(0)`, the identity that turns the book's rescaled iterate
`q̃^(k) = q^(k) ‖A^k q^(0)‖₂ / (α_1 λ_1^k)` of (5.22) into `A^k q^(0) / (α_1 λ_1^k)`. -/
theorem norm_smul_powerIterate (A : Matrix (Fin n) (Fin n) 𝕜) {q₀ : EuclideanSpace 𝕜 (Fin n)}
    (hq₀ : ‖q₀‖ = 1) (k : ℕ) :
    (‖toEuclideanLin (A ^ k) q₀‖ : 𝕜) • powerIterate A q₀ k = toEuclideanLin (A ^ k) q₀ := by
  rw [equation_5_18 A hq₀, smul_smul]
  rcases eq_or_ne (toEuclideanLin (A ^ k) q₀) 0 with h | h
  · rw [h, smul_zero]
  · rw [mul_inv_cancel₀ (RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h)), one_smul]

/-! ### Theorem 5.6 -/

/-- **Theorem 5.6, (5.21)–(5.22).** Let `A ∈ ℂ^{n×n}` be diagonalizable, with unit eigenvectors
`x_1, …, x_n` forming a basis (the columns of `X`) and eigenvalues ordered as (5.16):
`|λ_1| > |λ_2| ≥ |λ_i|` for `i ≠ 1` (indices `i₀`, `i₁`). Write `q^(0) = ∑ α_i x_i` (5.19) with
`α_1 ≠ 0`. Then for the rescaled iterate `q̃^(k) = q^(k) ‖A^k q^(0)‖₂ / (α_1 λ_1^k)` of (5.22),
`‖q̃^(k) − x_1‖₂ ≤ C |λ_2/λ_1|^k` for every `k`, with the constant `C = ∑_{i ≠ 1} |α_i/α_1|`.
Backbone `Krylov.norm_inv_pow_smul_pow_apply_sub_le_of_eigenbasis`, after
`norm_smul_powerIterate`. Erratum: the book's `C = (∑ (α_i/α_1)²)^{1/2}` needs orthonormal
eigenvectors. -/
theorem theorem_5_6 {A : Matrix (Fin n) (Fin n) ℂ}
    (x : Module.Basis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) {lam : Fin n → ℂ}
    (hx : ∀ i, toEuclideanLin A (x i) = lam i • x i) (hx1 : ∀ i, ‖x i‖ = 1) {i₀ i₁ : Fin n}
    (hgap : ‖lam i₁‖ < ‖lam i₀‖) (hdom : ∀ i, i ≠ i₀ → ‖lam i‖ ≤ ‖lam i₁‖)
    {q₀ : EuclideanSpace ℂ (Fin n)} (hq₀ : ‖q₀‖ = 1) (hα : x.repr q₀ i₀ ≠ 0) (k : ℕ) :
    ‖(x.repr q₀ i₀ * lam i₀ ^ k)⁻¹ •
        ((‖toEuclideanLin (A ^ k) q₀‖ : ℂ) • powerIterate A q₀ k) - x i₀‖ ≤
      (∑ i ∈ univ.erase i₀, ‖x.repr q₀ i / x.repr q₀ i₀‖) * (‖lam i₁‖ / ‖lam i₀‖) ^ k := by
  have hl₀ : lam i₀ ≠ 0 := norm_pos_iff.mp ((norm_nonneg _).trans_lt hgap)
  rw [show ((‖toEuclideanLin (A ^ k) q₀‖ : ℝ) : ℂ) • powerIterate A q₀ k =
      toEuclideanLin (A ^ k) q₀ from norm_smul_powerIterate A hq₀ k, toEuclideanLin_pow]
  exact Krylov.norm_inv_pow_smul_pow_apply_sub_le_of_eigenbasis hx hx1 hl₀ hdom hα
    (x.sum_repr q₀).symm k

/-- The `λ_1`-component and the rest of `q^(0) = ∑ α_i x_i`: the rest lies in the span of the
generalized eigenspaces of the eigenvalues `λ_i ≠ λ_1`, and every eigenvalue of `A` is some
`λ_i`. The bookkeeping shared by `theorem_5_6_rayleigh`, `inverseIterate_tendsto` and
`powerIterate_of_eq`. -/
theorem sum_repr_erase_mem_iSup_maxGenEigenspace {A : Matrix (Fin n) (Fin n) ℂ}
    (x : Module.Basis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) {lam : Fin n → ℂ}
    (hx : ∀ i, toEuclideanLin A (x i) = lam i • x i) (q₀ : EuclideanSpace ℂ (Fin n))
    (s : Finset (Fin n)) {l : ℂ} (hs : ∀ i ∉ s, lam i ≠ l) :
    ∑ i ∈ univ \ s, x.repr q₀ i • x i ∈
      ⨆ μ, ⨆ _ : μ ≠ l, Module.End.maxGenEigenspace (toEuclideanLin A) μ := by
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
  have hi' : i ∉ s := (Finset.mem_sdiff.mp hi).2
  exact Submodule.mem_iSup_of_mem (lam i) (Submodule.mem_iSup_of_mem (hs i hi')
    (Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr (hx i))))

/-- **Theorem 5.6, the consequence drawn after it.** Under its hypotheses the Rayleigh quotients
converge to the dominant eigenvalue: `lim_{k → ∞} ν^(k) = λ_1`. Backbone
`Krylov.tendsto_inner_powerIterate`, with `q^(0) = α_1 x_1 + ∑_{i ≠ 1} α_i x_i` the splitting of the
starting vector along the dominant eigenvector and the other generalized eigenspaces. -/
theorem theorem_5_6_rayleigh {A : Matrix (Fin n) (Fin n) ℂ}
    (x : Module.Basis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) {lam : Fin n → ℂ}
    (hx : ∀ i, toEuclideanLin A (x i) = lam i • x i) {i₀ i₁ : Fin n}
    (hgap : ‖lam i₁‖ < ‖lam i₀‖) (hdom : ∀ i, i ≠ i₀ → ‖lam i‖ ≤ ‖lam i₁‖)
    {q₀ : EuclideanSpace ℂ (Fin n)} (hq₀ : ‖q₀‖ = 1) (hα : x.repr q₀ i₀ ≠ 0) :
    Tendsto (fun k => rayleighQuotient A (powerIterate A q₀ k)) atTop (𝓝 (lam i₀)) := by
  have hl₀ : lam i₀ ≠ 0 := norm_pos_iff.mp ((norm_nonneg _).trans_lt hgap)
  have hlt : ∀ i, i ≠ i₀ → ‖lam i‖ < ‖lam i₀‖ := fun i hi => (hdom i hi).trans_lt hgap
  have hne : ∀ i ∉ ({i₀} : Finset (Fin n)), lam i ≠ lam i₀ := fun i hi h =>
    (hlt i (by simpa using hi)).ne (congrArg norm h)
  have hu : toEuclideanLin A (x.repr q₀ i₀ • x i₀) = lam i₀ • (x.repr q₀ i₀ • x i₀) := by
    rw [map_smul, hx, smul_comm]
  simp only [rayleighQuotient, powerIterate_eq_krylov A hq₀]
  refine Krylov.tendsto_inner_powerIterate (LinearMap.continuous_of_finiteDimensional _) hl₀
    hu (smul_ne_zero hα (x.ne_zero i₀))
    (sum_repr_erase_mem_iSup_maxGenEigenspace x hx q₀ {i₀} hne) (fun μ hμ hev => ?_) ?_
  · have hμ' : μ ∈ Set.range lam := by
      rw [← spectrum_eq_range_of_basis x hx]
      exact Module.End.hasEigenvalue_iff_mem_spectrum.mp hev
    obtain ⟨i, rfl⟩ := hμ'
    exact hlt i fun h => hμ (h ▸ rfl)
  · conv_lhs => rw [← x.sum_repr q₀]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), Finset.sdiff_singleton_eq_erase]

/-! ### (5.23): the symmetric case -/

/-- **(5.23).** If `A` is real and symmetric with orthonormal eigenvectors `x_i` and eigenvalues
`λ_i` (`|λ_1| > |λ_2| ≥ |λ_i|`, `i ≠ 1`, indices `i₀`, `i₁`), and `cos θ_0 = |x_1ᵀ q^(0)| ≠ 0`, then
`|λ_1 − ν^(k)| ≤ (λ_max − λ_min) tan²θ_0 |λ_2/λ_1|^{2k}` for every `k`: the convergence of `ν^(k)`
is quadratic in the ratio `|λ_2/λ_1|`. Backbone
`LinearMap.IsSymmetric.abs_sub_rayleigh_powerIterate_le`, with `tan²θ_0 = (1 − cos²θ_0)/cos²θ_0`.
Erratum: the book prints `|λ_1 − λ_n|` for the spread of the spectrum, which under the modulus
ordering (5.16) is false (`diag(3, −2, 1)`). -/
theorem equation_5_23 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {i₀ i₁ : Fin n}
    (hgap : |(hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin i₁| <
      |(hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin i₀|)
    (hdom : ∀ i, i ≠ i₀ →
      |(hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin i| ≤
        |(hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin i₁|)
    {q₀ : EuclideanSpace ℝ (Fin n)} (hq₀ : ‖q₀‖ = 1)
    (hc : inner ℝ ((hA.isSymmetric_toEuclideanLin).eigenvectorBasis finrank_euclideanSpace_fin i₀)
      q₀ ≠ 0) (k : ℕ) :
    |(hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin i₀ -
        rayleighQuotient A (powerIterate A q₀ k)| ≤
      ((⨆ i, (hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin i) -
          ⨅ i, (hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin i) *
        Real.tan (Real.arccos |inner ℝ
          ((hA.isSymmetric_toEuclideanLin).eigenvectorBasis finrank_euclideanSpace_fin i₀) q₀|)
          ^ 2 *
        (|(hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin i₁| /
          |(hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin i₀|) ^ (2 * k) :=
    by
  set hA' := hA.isSymmetric_toEuclideanLin
  set lam := hA'.eigenvalues finrank_euclideanSpace_fin
  set c := inner ℝ (hA'.eigenvectorBasis finrank_euclideanSpace_fin i₀) q₀
  have hl₀ : lam i₀ ≠ 0 := fun h => by
    rw [h, abs_zero] at hgap
    exact absurd hgap (not_lt.mpr (abs_nonneg _))
  have hab : ∀ i, lam i ∈ Set.Icc (⨅ i, lam i) (⨆ i, lam i) := fun i =>
    ⟨ciInf_le (Set.finite_range _).bddBelow i, le_ciSup (Set.finite_range _).bddAbove i⟩
  have hc1 : |c| ≤ 1 := by
    have h := norm_inner_le_norm (𝕜 := ℝ) (hA'.eigenvectorBasis finrank_euclideanSpace_fin i₀) q₀
    rwa [(hA'.eigenvectorBasis finrank_euclideanSpace_fin).norm_eq_one, hq₀, one_mul,
      Real.norm_eq_abs] at h
  have htan : Real.tan (Real.arccos |c|) ^ 2 = (1 - ‖c‖ ^ 2) / ‖c‖ ^ 2 := by
    rw [Real.tan_arccos, div_pow, Real.sq_sqrt (by nlinarith [abs_nonneg c, sq_abs c]), sq_abs,
      Real.norm_eq_abs, sq_abs]
  have h := hA'.abs_sub_rayleigh_powerIterate_le finrank_euclideanSpace_fin hl₀ hdom hab hq₀ hc k
  rw [htan, rayleighQuotient, powerIterate_eq_krylov A hq₀]
  simpa using h

/-! ### (5.24): the backward error of the iterate -/

/-- **(5.24).** Let `r^(k) = A q^(k) − ν^(k) q^(k)` be the residual at step `k` (with `z^(k) ≠ 0`,
so that `‖q^(k)‖₂ = 1`) and `ε E^(k) = −r^(k) (q^(k))ᴴ ∈ ℂ^{n×n}`. Then `ε E^(k) q^(k) = −r^(k)`,
so `(A + ε E^(k)) q^(k) = ν^(k) q^(k)`: at each step of the power method `ν^(k)` is an eigenvalue
of the perturbed matrix `A + ε E^(k)`; and `ε = ‖ε E^(k)‖₂ = ‖r^(k)‖₂` (so `‖E^(k)‖₂ = 1`), which
is moreover the smallest `2`-norm of a perturbation `ΔA` with `(A + ΔA) q^(k) = ν^(k) q^(k)`.
Backbone `isLeast_eigen_backwardError`; the rank-one matrix `r qᴴ` is
`InnerProductSpace.rankOne ℂ r q` on `ℂⁿ`. -/
theorem equation_5_24 (A : Matrix (Fin n) (Fin n) ℂ) {q₀ : EuclideanSpace ℂ (Fin n)}
    (hq₀ : ‖q₀‖ = 1) {k : ℕ} (hz : toEuclideanLin (A ^ k) q₀ ≠ 0) :
    let q := powerIterate A q₀ k
    let r := toEuclideanLin A q - rayleighQuotient A q • q
    let εE : Matrix (Fin n) (Fin n) ℂ := -vecMulVec (WithLp.ofLp r) (star (WithLp.ofLp q))
    toEuclideanLin εE q = -r ∧ toEuclideanLin (A + εE) q = rayleighQuotient A q • q ∧
      ‖εE‖ = ‖r‖ ∧
      ∀ ΔA : Matrix (Fin n) (Fin n) ℂ,
        toEuclideanLin (A + ΔA) q = rayleighQuotient A q • q → ‖r‖ ≤ ‖ΔA‖ := by
  intro q r εE
  have hq : ‖q‖ = 1 := by
    change ‖powerIterate A q₀ k‖ = 1
    rw [powerIterate_eq_krylov A hq₀]
    exact Krylov.norm_powerIterate_of_ne_zero _ _ _ (by rwa [← toEuclideanLin_pow])
  have hqq : inner ℂ q q = (1 : ℂ) := by rw [inner_self_eq_norm_sq_to_K, hq]; norm_num
  set R : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    InnerProductSpace.rankOne ℂ r q with hR
  -- the rank-one matrix `r qᴴ` is the rank-one operator
  have hlin : toEuclideanLin εE =
      -(R : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) := by
    simp only [εE, map_neg]
    congr 1
    rw [hR, ← InnerProductSpace.symm_toEuclideanLin_rankOne r q, LinearEquiv.apply_symm_apply]
  have hrank : toEuclideanCLM (n := Fin n) (𝕜 := ℂ) εE = -R :=
    ContinuousLinearMap.coe_injective (by rw [coe_toEuclideanCLM_eq_toEuclideanLin, hlin]; rfl)
  have hεEq : toEuclideanLin εE q = -r := by
    rw [hlin, LinearMap.neg_apply, ContinuousLinearMap.coe_coe, hR, InnerProductSpace.rankOne_apply,
      hqq, one_smul]
  refine ⟨hεEq, ?_, ?_, fun ΔA hΔ => ?_⟩
  · rw [map_add, LinearMap.add_apply, hεEq]
    simp [r]
  · rw [← l2_opNorm_toEuclideanCLM, hrank, norm_neg, hR, InnerProductSpace.norm_rankOne, hq,
      mul_one]
  · have hleast := (isLeast_eigen_backwardError (toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A) hq
      (rayleighQuotient A q)).2
    have h := hleast ⟨-toEuclideanCLM (n := Fin n) (𝕜 := ℂ) ΔA, ?_, rfl⟩
    · rwa [norm_neg, l2_opNorm_toEuclideanCLM] at h
    · rw [sub_neg_eq_add, _root_.add_apply]
      rw [map_add, LinearMap.add_apply] at hΔ
      exact hΔ

/-! ### (5.28): inverse iteration -/

/-- **(5.28), inverse iteration** with shift `μ`. Given `q^(0) ∈ ℂⁿ` of unit Euclidean norm, for
`k = 1, 2, …`: solve `(A − μ I) z^(k) = q^(k−1)`, set `q^(k) = z^(k) / ‖z^(k)‖₂`; the Rayleigh
quotient `σ^(k) = (q^(k))ᴴ A q^(k)` is computed on `A` itself, `rayleighQuotient A (q^(k))`. -/
noncomputable def inverseIterate (A : Matrix (Fin n) (Fin n) 𝕜) (μ : 𝕜)
    (q₀ : EuclideanSpace 𝕜 (Fin n)) : ℕ → EuclideanSpace 𝕜 (Fin n)
  | 0 => q₀
  | k + 1 =>
    (‖toEuclideanLin (A - μ • 1)⁻¹ (inverseIterate A μ q₀ k)‖ : 𝕜)⁻¹ •
      toEuclideanLin (A - μ • 1)⁻¹ (inverseIterate A μ q₀ k)

/-- **The book's recursion (5.28) is the backbone's inverse iteration**: for `μ ∉ σ(A)` and a unit
`q^(0)`, `inverseIterate A μ q₀ k = Krylov.inverseIterate (toEuclideanLin A) μ q₀ k`, the power
method on `(A − μ I)⁻¹` (`Krylov.inverseIterate_eq_powerIterate`). -/
theorem inverseIterate_eq_krylov {A : Matrix (Fin n) (Fin n) 𝕜} {μ : 𝕜} (hμ : μ ∉ spectrum 𝕜 A)
    {q₀ : EuclideanSpace 𝕜 (Fin n)} (hq₀ : ‖q₀‖ = 1) (k : ℕ) :
    inverseIterate A μ q₀ k = Krylov.inverseIterate (toEuclideanLin A) μ q₀ k := by
  have hinv := (ringInverse_toEuclideanLin (isUnit_sub_smul_one_of_notMem_spectrum hμ)).2
  rw [map_sub, map_smul, toEuclideanLin_one, ← Module.End.one_eq_id] at hinv
  rw [Krylov.inverseIterate_eq_powerIterate]
  refine Krylov.eq_powerIterate_of_recurrence _ q₀ (y := inverseIterate A μ q₀)
    (by simp [inverseIterate, hq₀]) (fun j => ?_) k
  rw [hinv]
  rfl

/-- **Convergence of inverse iteration** (§5.3.2, after (5.28)). Let `A` be diagonalizable with a
basis of unit eigenvectors `x_i`, `μ ∉ σ(A)`, and let `λ_m` be the eigenvalue closest to `μ`, in
the sense (5.27) `|λ_m − μ| < |λ_i − μ|` for `i ≠ m` (so `λ_m` is simple), with `α_m ≠ 0` in
`q^(0) = ∑ α_i x_i`. Then the iterates converge essentially to `x_m` — `c_k q^(k) → x_m` for the
unimodular scalars `c_k = ((λ_m − μ)/|λ_m − μ|)^k |α_m|/α_m`, the book's `q̃^(k) → x_m` — and
`σ^(k) → λ_m`. Backbone `Krylov.tendsto_smul_inverseIterate` and
`Krylov.tendsto_inner_inverseIterate`. -/
theorem inverseIterate_tendsto {A : Matrix (Fin n) (Fin n) ℂ}
    (x : Module.Basis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) {lam : Fin n → ℂ}
    (hx : ∀ i, toEuclideanLin A (x i) = lam i • x i) (hx1 : ∀ i, ‖x i‖ = 1) {μ : ℂ}
    (hμ : μ ∉ spectrum ℂ A) {m : Fin n} (hclose : ∀ i, i ≠ m → ‖lam m - μ‖ < ‖lam i - μ‖)
    {q₀ : EuclideanSpace ℂ (Fin n)} (hq₀ : ‖q₀‖ = 1) (hα : x.repr q₀ m ≠ 0) :
    Tendsto (fun k => (((lam m - μ) / (‖lam m - μ‖ : ℂ)) ^ k * (‖x.repr q₀ m‖ / x.repr q₀ m)) •
        inverseIterate A μ q₀ k) atTop (𝓝 (x m)) ∧
      Tendsto (fun k => rayleighQuotient A (inverseIterate A μ q₀ k)) atTop (𝓝 (lam m)) := by
  have hne : ∀ i ∉ ({m} : Finset (Fin n)), lam i ≠ lam m := fun i hi h =>
    (hclose i (by simpa using hi)).ne (by rw [h])
  have hσ : IsUnit (toEuclideanLin A - μ • (1 : Module.End ℂ (EuclideanSpace ℂ (Fin n)))) := by
    have h := (ringInverse_toEuclideanLin (isUnit_sub_smul_one_of_notMem_spectrum hμ)).1
    rwa [map_sub, map_smul, toEuclideanLin_one, ← Module.End.one_eq_id] at h
  have hdom : ∀ ν, ν ≠ lam m → Module.End.HasEigenvalue (toEuclideanLin A) ν →
      ‖lam m - μ‖ < ‖ν - μ‖ := fun ν hν hev => by
    have hν' : ν ∈ Set.range lam := by
      rw [← spectrum_eq_range_of_basis x hx]
      exact Module.End.hasEigenvalue_iff_mem_spectrum.mp hev
    obtain ⟨i, rfl⟩ := hν'
    exact hclose i fun h => hν (h ▸ rfl)
  have hsplit : q₀ = x.repr q₀ m • x m + ∑ i ∈ univ \ {m}, x.repr q₀ i • x i := by
    conv_lhs => rw [← x.sum_repr q₀]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m), Finset.sdiff_singleton_eq_erase]
  have hu0 : x.repr q₀ m • x m ≠ 0 := smul_ne_zero hα (x.ne_zero m)
  have hu : toEuclideanLin A (x.repr q₀ m • x m) = lam m • (x.repr q₀ m • x m) := by
    rw [map_smul, hx, smul_comm]
  have hw := sum_repr_erase_mem_iSup_maxGenEigenspace x hx q₀ {m} hne
  simp only [inverseIterate_eq_krylov hμ hq₀, rayleighQuotient]
  refine ⟨?_, Krylov.tendsto_inner_inverseIterate (LinearMap.continuous_of_finiteDimensional _) hσ
    hu hu0 hw hdom hsplit⟩
  have hlim := Krylov.tendsto_smul_inverseIterate hσ hu hu0 hw hdom hsplit
  have hcoe : ∀ r : ℝ, (RCLike.ofReal r : ℂ) = (r : ℂ) := fun r => rfl
  simp only [hcoe] at hlim
  have hαn : (‖x.repr q₀ m‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hα)
  have hval : (‖x.repr q₀ m‖ / x.repr q₀ m : ℂ) • ((‖x.repr q₀ m • x m‖ : ℂ)⁻¹ •
      x.repr q₀ m • x m) = x m := by
    rw [norm_smul, hx1, mul_one, smul_smul, smul_smul]
    rw [show (‖x.repr q₀ m‖ : ℂ) / x.repr q₀ m * (‖x.repr q₀ m‖ : ℂ)⁻¹ * x.repr q₀ m = 1 by
      field_simp, one_smul]
  have h := hlim.const_smul ((‖x.repr q₀ m‖ : ℂ) / x.repr q₀ m)
  rw [hval] at h
  refine h.congr fun k => ?_
  rw [smul_smul, mul_comm]

/-! ### §5.3.3: coincident dominant eigenvalues -/

/-- **§5.3.3, case 1: `λ_2 = λ_1`.** If the two dominant eigenvalues coincide, `λ_{i₁} = λ_{i₀}`
with `|λ_i| < |λ_1|` for the other indices, the power method is still convergent: the iterates
converge essentially to the unit vector in the direction of `α_1 x_1 + α_2 x_2`, which lies in the
subspace spanned by the eigenvectors `x_1`, `x_2`, and `ν^(k) → λ_1`. Backbone
`Krylov.exists_norm_eq_one_tendsto_smul_powerIterate` and `Krylov.tendsto_inner_powerIterate`,
whose `λ_1`-component `u = α_1 x_1 + α_2 x_2` of `q^(0)` is an eigenvector (the backbone never
assumed `λ_1` simple, only that the `λ_1`-component of `q^(0)` is an eigenvector). -/
theorem powerIterate_of_eq {A : Matrix (Fin n) (Fin n) ℂ}
    (x : Module.Basis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) {lam : Fin n → ℂ}
    (hx : ∀ i, toEuclideanLin A (x i) = lam i • x i) {i₀ i₁ : Fin n} (hi : i₁ ≠ i₀)
    (heq : lam i₁ = lam i₀) (hdom : ∀ i, i ≠ i₀ → i ≠ i₁ → ‖lam i‖ < ‖lam i₀‖) (hl₀ : lam i₀ ≠ 0)
    {q₀ : EuclideanSpace ℂ (Fin n)} (hq₀ : ‖q₀‖ = 1) (hα : x.repr q₀ i₀ ≠ 0) :
    let u := x.repr q₀ i₀ • x i₀ + x.repr q₀ i₁ • x i₁
    u ∈ Submodule.span ℂ {x i₀, x i₁} ∧
      (∃ c : ℕ → ℂ, (∀ k, ‖c k‖ = 1) ∧
        Tendsto (fun k => c k • powerIterate A q₀ k) atTop (𝓝 ((‖u‖ : ℂ)⁻¹ • u))) ∧
      Tendsto (fun k => rayleighQuotient A (powerIterate A q₀ k)) atTop (𝓝 (lam i₀)) := by
  intro u
  have hu : toEuclideanLin A u = lam i₀ • u := by
    simp only [u, map_add, map_smul, hx, heq, smul_add, smul_comm (lam i₀)]
  have hu0 : u ≠ 0 := fun h => by
    have := congrArg (fun z => x.repr z i₀) h
    simp only [u, map_add, map_smul, Module.Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply,
      Finsupp.single_eq_same, Finsupp.single_eq_of_ne' hi, smul_eq_mul, mul_one, mul_zero,
      add_zero, map_zero, Finsupp.zero_apply] at this
    exact hα this
  have hne : ∀ i ∉ ({i₀, i₁} : Finset (Fin n)), lam i ≠ lam i₀ := fun i hi' h => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi'
    exact (hdom i hi'.1 hi'.2).ne (congrArg norm h)
  have hw := sum_repr_erase_mem_iSup_maxGenEigenspace x hx q₀ {i₀, i₁} hne
  have hsplit : q₀ = u + ∑ i ∈ univ \ {i₀, i₁}, x.repr q₀ i • x i := by
    conv_lhs => rw [← x.sum_repr q₀]
    rw [← Finset.sum_sdiff (Finset.subset_univ {i₀, i₁}), Finset.sum_pair hi.symm, add_comm]
  have hdom' : ∀ μ, μ ≠ lam i₀ → Module.End.HasEigenvalue (toEuclideanLin A) μ →
      ‖μ‖ < ‖lam i₀‖ := fun μ hμ hev => by
    have hμ' : μ ∈ Set.range lam := by
      rw [← spectrum_eq_range_of_basis x hx]
      exact Module.End.hasEigenvalue_iff_mem_spectrum.mp hev
    obtain ⟨i, rfl⟩ := hμ'
    exact hdom i (fun h => hμ (h ▸ rfl)) (fun h => hμ (h ▸ heq))
  refine ⟨?_, ?_, ?_⟩
  · exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · simp only [powerIterate_eq_krylov A hq₀]
    exact Krylov.exists_norm_eq_one_tendsto_smul_powerIterate hl₀ hu hu0 hw hdom' hsplit
  · simp only [rayleighQuotient, powerIterate_eq_krylov A hq₀]
    exact Krylov.tendsto_inner_powerIterate (LinearMap.continuous_of_finiteDimensional _) hl₀ hu
      hu0 hw hdom' hsplit

end QuarteroniSaccoSaleri.Chapter05

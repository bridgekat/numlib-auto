import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.Eigen.MinMax
import Numlib.Eigen.Normal
import Numlib.Eigen.NumericalRange
import Numlib.Eigen.Pencil

/-!
# Symmetric-definite and definite pencils

Symmetric-definite pencils `A - λ B` (`A` Hermitian, `B` positive definite, or more generally a
positive-semidefinite combination), their sorted eigenvalues and variational characterization, the
Crawford number and Stewart's perturbation bound ([golub2013matrix] §8.7.1–8.7.3; G. W. Stewart,
*Perturbation bounds for the definite generalized eigenvalue problem*, Lin. Alg. Appl. 23 (1979);
Stewart–Sun, *Matrix Perturbation Theory*, §VI.1–VI.3).

`Numlib/Eigen/Pencil` has the pencil vocabulary (`Matrix.pencilSpectrum`,
`Matrix.HasPencilEigenvector`) and the simultaneous diagonalization of a Hermitian/positive-definite
pair (`Matrix.exists_simultaneous_diagonalization`). This module is its symmetric-definite
continuation, kept separate because it is where the *ordering* of the real eigenvalues enters
(min–max, perturbation), which the general pencil theory does not have.

## Main results

* `Matrix.exists_isUnit_conj_diagonal_of_posSemidef_combination`: [golub2013matrix] Theorem 8.7.1,
  simultaneous diagonalization by congruence when some `C = μ A + (1 - μ) B`, `μ ∈ [0, 1]`, is
  positive semidefinite with `ker C = ker A ⊓ ker B`. The engine is
  `Matrix.exists_isUnit_conj_diagonal_of_posSemidef_of_ker_le` (a semidefinite `C` and a Hermitian
  `D` with `ker C ≤ ker D`), through the simultaneous unitary diagonalization of commuting Hermitian
  matrices over any `RCLike` field, `Matrix.IsHermitian.exists_unitary_conj_diagonal_of_commute`
  (in `Numlib/Eigen/Normal`).
* `Matrix.pencilEigenvalues hA hB`: the eigenvalues of the pencil, sorted decreasingly — those of
  `Wᴴ A W` for any `W` with `Wᴴ B W = 1` (`Matrix.pencilEigenvalues_eq_of_conj_eq_one`); they are
  the pencil spectrum (`Matrix.pencilSpectrum_eq_range_pencilEigenvalues`) and satisfy the max–min
  and min–max characterizations `Matrix.isGreatest_pencilEigenvalues`,
  `Matrix.isLeast_pencilEigenvalues` for the generalized Rayleigh quotient
  `re (xᴴ A x) / re (xᴴ B x)`.
* `Matrix.crawfordNumber A B = min_{‖x‖ = 1} √((xᴴ A x)² + (xᴴ B x)²)` (with the square root, as in
  Stewart; the book's display (8.7.4) omits it), positive for a positive definite `B`
  (`Matrix.crawfordNumber_pos_of_posDef`) and 1-Lipschitz in the pair
  (`Matrix.crawfordNumber_sub_le`): a definite pair stays definite under perturbations of size
  `ε < c`.
* `Matrix.sin_abs_arctan_pencilEigenvalues_sub_le`: Stewart's perturbation theorem in its correct
  form, `sin |arctan λ_i - arctan μ_i| ≤ ε / c`. The book's Theorem 8.7.3 asserts
  `|arctan λ_i - arctan μ_i| ≤ arctan(ε / c)`, which is false already for `n = 1` (`A = 0`,
  `B = 1`, `E_A = √3/4`, `E_B = -1/4`: `ε = 1/2 < c = 1`, the difference is `π/6 > arctan(1/2)`),
  and its claim that the perturbed pencil is symmetric-definite fails too; `B + E_B` positive
  definite is a hypothesis here.
* `Matrix.isMinOn_pencil_residual`: the generalized Rayleigh quotient minimizes the `B⁻¹`-norm
  residual `‖A x - λ B x‖_{B⁻¹}` ([golub2013matrix] (8.7.6)–(8.7.7)).
* `Matrix.exists_posDef_rotation_of_crawfordNumber_pos_complex`: over `ℂ` a definite pair is a
  rotation `(A, B) ↦ (sin θ A + cos θ B, …)` of a pair with a positive definite second matrix
  (Crawford 1976; Stewart–Sun Theorem VI.1.18), by the Toeplitz–Hausdorff theorem and a separating
  functional. Over `ℝ` this fails for `n = 2`, where the real joint numerical range need not be
  convex: `A = diag(1, -1)`, `B = [[0, 1], [1, 0]]` have Crawford number `1` but every
  `sin θ A + cos θ B` has trace `0`.
-/

open scoped ComplexOrder

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The sorted eigenvalues of a Hermitian matrix depend only on its characteristic polynomial. -/
private theorem eigenvalues₀_eq_of_charpoly_eq {C C' : Matrix n n 𝕜} (hC : C.IsHermitian)
    (hC' : C'.IsHermitian) (h : C.charpoly = C'.charpoly) :
    hC.eigenvalues₀ = hC'.eigenvalues₀ := by
  rw [← List.ofFn_inj, ← hC.sort_roots_charpoly_eq_eigenvalues₀,
    ← hC'.sort_roots_charpoly_eq_eigenvalues₀, h]

omit [DecidableEq n] in
/-- The congruence `Wᴴ A W` of a Hermitian matrix is Hermitian (Mathlib's
`Matrix.isHermitian_conjTranspose_mul_mul` with `star` for the conjugate transpose). -/
theorem isHermitian_star_mul_mul {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (W : Matrix n n 𝕜) : (star W * A * W).IsHermitian := by
  rw [star_eq_conjTranspose]; exact isHermitian_conjTranspose_mul_mul W hA

/-- **The sorted eigenvalues of a symmetric-definite pencil** `(A, B)` ([golub2013matrix] §8.7,
the `λ₁ ≥ ⋯ ≥ λ_n` of Theorem 8.7.3): the eigenvalues, sorted decreasingly, of the Hermitian
`Wᴴ A W` for a normalizer `W` with `Wᴴ B W = 1` (`Matrix.PosDef.exists_isUnit_conj_eq_one`). They
do not depend on the normalizer (`Matrix.pencilEigenvalues_eq_of_conj_eq_one`) and are the
eigenvalues of the pencil (`Matrix.pencilSpectrum_eq_range_pencilEigenvalues`). -/
noncomputable def pencilEigenvalues {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.PosDef) :
    Fin (Fintype.card n) → ℝ :=
  (isHermitian_star_mul_mul hA hB.exists_isUnit_conj_eq_one.choose).eigenvalues₀

/-- The pencil eigenvalues decrease. -/
theorem pencilEigenvalues_antitone {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.PosDef) :
    Antitone (pencilEigenvalues hA hB) :=
  IsHermitian.eigenvalues₀_antitone _

/-- **Independence of the normalizer**: for any `W` with `Wᴴ B W = 1`, the sorted eigenvalues of
`Wᴴ A W` are `pencilEigenvalues hA hB`. Two normalizers differ by a unitary right factor
`U = W₀⁻¹ W` (`Uᴴ U = Wᴴ B W = 1`), and a unitary similarity preserves the characteristic
polynomial. -/
theorem pencilEigenvalues_eq_of_conj_eq_one {A B W : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.PosDef) (hW : star W * B * W = 1) :
    (isHermitian_star_mul_mul hA W).eigenvalues₀ = pencilEigenvalues hA hB := by
  obtain ⟨hW₀u, hW₀⟩ := hB.exists_isUnit_conj_eq_one.choose_spec
  set W₀ := hB.exists_isUnit_conj_eq_one.choose
  have hd : IsUnit W₀.det := (isUnit_iff_isUnit_det W₀).1 hW₀u
  set U := W₀⁻¹ * W with hU
  have hWU : W = W₀ * U := by rw [hU, mul_nonsing_inv_cancel_left _ _ hd]
  have hUU : star U * U = 1 := by
    calc star U * U = star U * (star W₀ * B * W₀) * U := by rw [hW₀, Matrix.mul_one]
      _ = star (W₀ * U) * B * (W₀ * U) := by
        rw [show star (W₀ * U) = star U * star W₀ from star_mul W₀ U]
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [← hWU, hW]
  have hUu : U ∈ unitaryGroup n 𝕜 := mem_unitaryGroup_iff'.2 hUU
  have hC : star W * A * W = star U * (star W₀ * A * W₀) * U := by
    rw [hWU, star_mul]; simp only [Matrix.mul_assoc]
  refine eigenvalues₀_eq_of_charpoly_eq _ _ ?_
  rw [hC, Matrix.mul_assoc, Matrix.charpoly_mul_comm, Matrix.mul_assoc,
    mem_unitaryGroup_iff.1 hUu, Matrix.mul_one]

/-- **The pencil eigenvalues are the eigenvalues of the pencil**: `σ(A, B)` is the set of the
`pencilEigenvalues hA hB i` (as scalars). -/
theorem pencilSpectrum_eq_range_pencilEigenvalues {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.PosDef) :
    pencilSpectrum A B = Set.range fun i => (pencilEigenvalues hA hB i : 𝕜) := by
  obtain ⟨hW₀u, hW₀⟩ := hB.exists_isUnit_conj_eq_one.choose_spec
  set W₀ := hB.exists_isUnit_conj_eq_one.choose
  set C := star W₀ * A * W₀
  have hC := isHermitian_star_mul_mul hA W₀
  have hpe : pencilEigenvalues hA hB = hC.eigenvalues₀ := rfl
  rw [hpe, ← pencilSpectrum_mul_mul_of_isUnit A B hW₀u.star hW₀u, hW₀, pencilSpectrum_one]
  ext μ
  rw [mem_spectrum_iff_isRoot_charpoly, ← Polynomial.mem_roots (charpoly_monic C).ne_zero,
    hC.roots_charpoly_eq_eigenvalues₀]
  simp [eq_comm]

/-- The generalized Rayleigh quotient `re (xᴴ A x) / re (xᴴ B x)` at `x = W y` is the Rayleigh
quotient of `Wᴴ A W` at `y` when `Wᴴ B W = 1`. -/
private theorem rayleighQuotient_toEuclideanLin_conj {A B W : Matrix n n 𝕜}
    (hW : star W * B * W = 1) (y : EuclideanSpace 𝕜 n) :
    (toEuclideanLin (star W * A * W)).rayleighQuotient y =
      RCLike.re (star (W *ᵥ WithLp.ofLp y) ⬝ᵥ A *ᵥ (W *ᵥ WithLp.ofLp y)) /
        RCLike.re (star (W *ᵥ WithLp.ofLp y) ⬝ᵥ B *ᵥ (W *ᵥ WithLp.ofLp y)) := by
  have hform : ∀ M : Matrix n n 𝕜, star (W *ᵥ WithLp.ofLp y) ⬝ᵥ M *ᵥ (W *ᵥ WithLp.ofLp y) =
      star (WithLp.ofLp y) ⬝ᵥ (star W * M * W) *ᵥ WithLp.ofLp y := fun M => by
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, star_eq_conjTranspose]
  rw [hform, hform, hW, one_mulVec, LinearMap.rayleighQuotient]
  congr 1
  · rw [← inner_conj_symm, RCLike.conj_re, EuclideanSpace.inner_eq_star_dotProduct,
      toEuclideanLin_apply, WithLp.ofLp_toLp, dotProduct_comm]
  · rw [@norm_sq_eq_re_inner 𝕜, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

omit [DecidableEq n] in
/-- The sets of Courant–Fischer bounds are transported by a linear equivalence: if `g (Φ y) = f y`,
the bounds `R c (g x)` holding on the nonzero vectors of some `d`-dimensional subspace of `V'` are
those holding for `f` on some `d`-dimensional subspace of `V`. -/
private theorem setOf_exists_submodule_eq {V V' : Type*} [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup V'] [Module 𝕜 V'] (Φ : V ≃ₗ[𝕜] V') {f : V → ℝ} {g : V' → ℝ}
    (hfg : ∀ y, g (Φ y) = f y) (d : ℕ) (R : ℝ → ℝ → Prop) :
    {c : ℝ | ∃ S : Submodule 𝕜 V', Module.finrank 𝕜 S = d ∧ ∀ x ∈ S, x ≠ 0 → R c (g x)} =
      {c : ℝ | ∃ S : Submodule 𝕜 V, Module.finrank 𝕜 S = d ∧ ∀ y ∈ S, y ≠ 0 → R c (f y)} := by
  ext c
  constructor
  · rintro ⟨S, hS, hSc⟩
    refine ⟨S.map (Φ.symm : V' →ₗ[𝕜] V), by rw [LinearEquiv.finrank_map_eq, hS], ?_⟩
    rintro _ ⟨x, hx, rfl⟩ hx0
    have hx0' : x ≠ 0 := fun h => hx0 (by simp [h])
    have := hSc x hx hx0'
    rwa [← Φ.apply_symm_apply x, hfg] at this
  · rintro ⟨S, hS, hSc⟩
    refine ⟨S.map (Φ : V →ₗ[𝕜] V'), by rw [LinearEquiv.finrank_map_eq, hS], ?_⟩
    rintro _ ⟨y, hy, rfl⟩ hy0
    have hy0' : y ≠ 0 := fun h => hy0 (by simp [h])
    rw [LinearEquiv.coe_coe, hfg]
    exact hSc y hy hy0'

/-- The substitution `x = W y` behind both Courant–Fischer forms for a pencil: with `Wᴴ B W = 1`,
`Φ y = W y` carries the Rayleigh quotient of `Wᴴ A W` to the pencil quotient
`re (xᴴ A x) / re (xᴴ B x)`. -/
private theorem exists_linearEquiv_rayleighQuotient_eq {A B : Matrix n n 𝕜} (hB : B.PosDef) :
    ∃ Φ : EuclideanSpace 𝕜 n ≃ₗ[𝕜] (n → 𝕜), ∀ y,
      RCLike.re (star (Φ y) ⬝ᵥ A *ᵥ Φ y) / RCLike.re (star (Φ y) ⬝ᵥ B *ᵥ Φ y) =
        (toEuclideanLin (star hB.exists_isUnit_conj_eq_one.choose * A *
          hB.exists_isUnit_conj_eq_one.choose)).rayleighQuotient y := by
  obtain ⟨hWu, hW⟩ := hB.exists_isUnit_conj_eq_one.choose_spec
  refine ⟨(WithLp.linearEquiv 2 𝕜 (n → 𝕜)).trans (toLinearEquiv' _ hWu.invertible), fun y => ?_⟩
  exact (rayleighQuotient_toEuclideanLin_conj hW y).symm

/-- **Courant–Fischer for a symmetric-definite pencil** ([golub2013matrix] §8.7.1): the `i`-th
sorted pencil eigenvalue is the greatest `c` such that some `(i+1)`-dimensional subspace has
`c ≤ re (xᴴ A x) / re (xᴴ B x)` at all its nonzero vectors. Substitute `x = W y` (`Wᴴ B W = 1`,
`W` invertible, so subspaces correspond with their dimensions) in
`LinearMap.IsSymmetric.isGreatest_eigenvalues` for `Wᴴ A W`. -/
theorem isGreatest_pencilEigenvalues {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.PosDef)
    (i : Fin (Fintype.card n)) :
    IsGreatest {c : ℝ | ∃ S : Submodule 𝕜 (n → 𝕜), Module.finrank 𝕜 S = (i : ℕ) + 1 ∧
      ∀ x ∈ S, x ≠ 0 →
        c ≤ RCLike.re (star x ⬝ᵥ A *ᵥ x) / RCLike.re (star x ⬝ᵥ B *ᵥ x)}
      (pencilEigenvalues hA hB i) := by
  obtain ⟨Φ, hΦ⟩ := exists_linearEquiv_rayleighQuotient_eq (A := A) hB
  rw [setOf_exists_submodule_eq Φ hΦ _ (· ≤ ·)]
  exact (isSymmetric_toEuclideanLin_iff.mpr (isHermitian_star_mul_mul hA _)).isGreatest_eigenvalues
    finrank_euclideanSpace i

/-- **The min–max twin of `Matrix.isGreatest_pencilEigenvalues`**: the `i`-th sorted pencil
eigenvalue is the least `c` such that some `(card n - i)`-dimensional subspace has
`re (xᴴ A x) / re (xᴴ B x) ≤ c` at all its nonzero vectors. -/
theorem isLeast_pencilEigenvalues {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.PosDef)
    (i : Fin (Fintype.card n)) :
    IsLeast {c : ℝ | ∃ S : Submodule 𝕜 (n → 𝕜), Module.finrank 𝕜 S = Fintype.card n - i ∧
      ∀ x ∈ S, x ≠ 0 →
        RCLike.re (star x ⬝ᵥ A *ᵥ x) / RCLike.re (star x ⬝ᵥ B *ᵥ x) ≤ c}
      (pencilEigenvalues hA hB i) := by
  obtain ⟨Φ, hΦ⟩ := exists_linearEquiv_rayleighQuotient_eq (A := A) hB
  rw [setOf_exists_submodule_eq Φ hΦ _ fun c r => r ≤ c]
  exact (isSymmetric_toEuclideanLin_iff.mpr (isHermitian_star_mul_mul hA _)).isLeast_eigenvalues
    finrank_euclideanSpace i

omit [DecidableEq n] in
/-- The real part `re (xᴴ M x)` of the quadratic form of a matrix at a vector of `EuclideanSpace`:
for Hermitian `A`, `B` the pair `(reQuadForm A x, reQuadForm B x)` over the unit sphere is the
joint numerical range whose distance to the origin is the Crawford number. -/
noncomputable abbrev reQuadForm (M : Matrix n n 𝕜) (x : EuclideanSpace 𝕜 n) : ℝ :=
  RCLike.re (star (WithLp.ofLp x) ⬝ᵥ M *ᵥ WithLp.ofLp x)

omit [DecidableEq n] in
/-- `re (xᴴ M x)` is quadratic under real scaling. -/
private theorem qf_smul (M : Matrix n n 𝕜) (t : ℝ) (x : EuclideanSpace 𝕜 n) :
    reQuadForm M ((t : 𝕜) • x) = t ^ 2 * reQuadForm M x := by
  simp only [reQuadForm, WithLp.ofLp_smul, star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct,
    RCLike.star_def, RCLike.conj_ofReal, smul_eq_mul, ← mul_assoc, ← RCLike.ofReal_mul,
    RCLike.re_ofReal_mul]
  ring

/-- `|re (xᴴ M x)| ≤ ‖M‖₂ ‖x‖²`. -/
private theorem abs_qf_le (M : Matrix n n 𝕜) (x : EuclideanSpace 𝕜 n) :
    |reQuadForm M x| ≤ lpOpNorm 2 M * ‖x‖ ^ 2 := by
  have h1 : star (WithLp.ofLp x) ⬝ᵥ M *ᵥ WithLp.ofLp x = inner 𝕜 x (lpCLM 2 M x) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, lpCLM_apply, dotProduct_comm]
  rw [reQuadForm, h1]
  calc |RCLike.re (inner 𝕜 x (lpCLM 2 M x))| ≤ ‖(inner 𝕜 x (lpCLM 2 M x) : 𝕜)‖ :=
        RCLike.abs_re_le_norm _
    _ ≤ ‖x‖ * ‖lpCLM 2 M x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (lpOpNorm 2 M * ‖x‖) := by gcongr; exact (lpCLM 2 M).le_opNorm x
    _ = lpOpNorm 2 M * ‖x‖ ^ 2 := by ring

omit [DecidableEq n] in
/-- **The Crawford number** of a Hermitian pair ([golub2013matrix] (8.7.4), with Stewart's square
root): `c(A, B) = min_{‖x‖₂ = 1} √((xᴴ A x)² + (xᴴ B x)²)` (real parts). The pair is *definite*
when it is positive. The book's display omits the square root; with it the number scales like
the matrices, which is what the ratio `ε / c(A, B)` of Theorem 8.7.3 needs. It is `0` for an
empty index type. -/
noncomputable def crawfordNumber (A B : Matrix n n 𝕜) : ℝ :=
  ⨅ x : Metric.sphere (0 : EuclideanSpace 𝕜 n) 1,
    Real.sqrt (reQuadForm A x ^ 2 + reQuadForm B x ^ 2)

omit [DecidableEq n] in
/-- The Crawford number is nonnegative. -/
theorem crawfordNumber_nonneg (A B : Matrix n n 𝕜) : 0 ≤ crawfordNumber A B :=
  Real.iInf_nonneg fun _ => Real.sqrt_nonneg _

omit [DecidableEq n] in
/-- **The pointwise Crawford bound**: `c(A, B) ‖x‖² ≤ √((xᴴ A x)² + (xᴴ B x)²)` for every `x`
(homogeneity of degree two). -/
theorem crawfordNumber_le_norm_mul (A B : Matrix n n 𝕜) (x : EuclideanSpace 𝕜 n) :
    crawfordNumber A B * ‖x‖ ^ 2 ≤ Real.sqrt (reQuadForm A x ^ 2 + reQuadForm B x ^ 2) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [norm_zero, zero_pow two_ne_zero, mul_zero]; exact Real.sqrt_nonneg _
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
  set u : EuclideanSpace 𝕜 n := ((‖x‖⁻¹ : ℝ) : 𝕜) • x
  have hu : u ∈ Metric.sphere (0 : EuclideanSpace 𝕜 n) 1 := by
    rw [mem_sphere_zero_iff_norm]
    change ‖((‖x‖⁻¹ : ℝ) : 𝕜) • x‖ = 1
    rw [RCLike.ofReal_inv]
    exact norm_smul_inv_norm hx
  have hle : crawfordNumber A B ≤ Real.sqrt (reQuadForm A u ^ 2 + reQuadForm B u ^ 2) := by
    unfold crawfordNumber
    exact ciInf_le (f := fun y : Metric.sphere (0 : EuclideanSpace 𝕜 n) 1 =>
      Real.sqrt (reQuadForm A y ^ 2 + reQuadForm B y ^ 2))
      ⟨0, by rintro _ ⟨y, rfl⟩; exact Real.sqrt_nonneg _⟩ ⟨u, hu⟩
  have hxu : x = ((‖x‖ : ℝ) : 𝕜) • u := by
    rw [smul_smul, ← RCLike.ofReal_mul, mul_inv_cancel₀ hn.ne', RCLike.ofReal_one, one_smul]
  have hscale : Real.sqrt (reQuadForm A x ^ 2 + reQuadForm B x ^ 2) =
      ‖x‖ ^ 2 * Real.sqrt (reQuadForm A u ^ 2 + reQuadForm B u ^ 2) := by
    have hA' : reQuadForm A x = ‖x‖ ^ 2 * reQuadForm A u := by
      conv_lhs => rw [hxu]
      exact qf_smul A ‖x‖ u
    have hB' : reQuadForm B x = ‖x‖ ^ 2 * reQuadForm B u := by
      conv_lhs => rw [hxu]
      exact qf_smul B ‖x‖ u
    rw [hA', hB', show (‖x‖ ^ 2 * reQuadForm A u) ^ 2 + (‖x‖ ^ 2 * reQuadForm B u) ^ 2 =
      (‖x‖ ^ 2) ^ 2 * (reQuadForm A u ^ 2 + reQuadForm B u ^ 2) by ring,
      Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity)]
  rw [hscale, mul_comm]
  exact mul_le_mul_of_nonneg_left hle (by positivity)

/-- The pair norm through the complex modulus: `√(a² + b²) = ‖a + b i‖`. -/
private theorem sqrt_eq_norm (a b : ℝ) : Real.sqrt (a ^ 2 + b ^ 2) = ‖(a : ℂ) + b * Complex.I‖ :=
  (Complex.norm_add_mul_I a b).symm

/-- The pointwise perturbation of the pair `(xᴴ A x, xᴴ B x)`:
`|(xᴴ(A + E_A)x, xᴴ(B + E_B)x) - (xᴴ A x, xᴴ B x)| ≤ ε ‖x‖²` with `ε = √(‖E_A‖₂² + ‖E_B‖₂²)`. -/
private theorem norm_pair_sub_le (A B EA EB : Matrix n n 𝕜) (x : EuclideanSpace 𝕜 n) :
    ‖((reQuadForm (A + EA) x : ℂ) + reQuadForm (B + EB) x * Complex.I) -
        ((reQuadForm A x : ℂ) + reQuadForm B x * Complex.I)‖ ≤
      Real.sqrt (lpOpNorm 2 EA ^ 2 + lpOpNorm 2 EB ^ 2) * ‖x‖ ^ 2 := by
  have hA : reQuadForm (A + EA) x = reQuadForm A x + reQuadForm EA x := by
    simp only [reQuadForm, add_mulVec, dotProduct_add, map_add]
  have hB : reQuadForm (B + EB) x = reQuadForm B x + reQuadForm EB x := by
    simp only [reQuadForm, add_mulVec, dotProduct_add, map_add]
  have heq : ((reQuadForm (A + EA) x : ℂ) + reQuadForm (B + EB) x * Complex.I) -
      ((reQuadForm A x : ℂ) + reQuadForm B x * Complex.I)
      = (reQuadForm EA x : ℂ) + reQuadForm EB x * Complex.I := by
    rw [hA, hB]; push_cast; ring
  rw [heq, ← sqrt_eq_norm]
  have h1 := abs_qf_le EA x
  have h2 := abs_qf_le EB x
  rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ ‖x‖ ^ 2), ← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  have h1' := sq_le_sq' (abs_le.1 h1).1 (abs_le.1 h1).2
  have h2' := sq_le_sq' (abs_le.1 h2).1 (abs_le.1 h2).2
  nlinarith [h1', h2']

/-- **The Crawford number is 1-Lipschitz in the pair** (Stewart–Sun, *Matrix Perturbation Theory*,
§VI.1.3): `c(A, B) - ε ≤ c(A + E_A, B + E_B)` with `ε = √(‖E_A‖₂² + ‖E_B‖₂²)`. Hence a definite
pair stays definite under perturbations with `ε < c(A, B)` — the correct form of
[golub2013matrix] Theorem 8.7.3's claim that the perturbed pencil is symmetric-definite. -/
theorem crawfordNumber_sub_le (A B EA EB : Matrix n n 𝕜) :
    crawfordNumber A B - Real.sqrt (lpOpNorm 2 EA ^ 2 + lpOpNorm 2 EB ^ 2) ≤
      crawfordNumber (A + EA) (B + EB) := by
  rcases isEmpty_or_nonempty (Metric.sphere (0 : EuclideanSpace 𝕜 n) 1) with he | hne
  · rw [crawfordNumber, crawfordNumber, Real.iInf_of_isEmpty, Real.iInf_of_isEmpty]
    linarith [Real.sqrt_nonneg (lpOpNorm 2 EA ^ 2 + lpOpNorm 2 EB ^ 2)]
  conv_rhs => unfold crawfordNumber
  refine le_ciInf fun x => ?_
  have hx : ‖(x : EuclideanSpace 𝕜 n)‖ = 1 := mem_sphere_zero_iff_norm.1 x.2
  have hc := crawfordNumber_le_norm_mul A B x
  have hd := norm_pair_sub_le A B EA EB x
  rw [hx, one_pow, mul_one] at hc hd
  rw [sqrt_eq_norm] at hc
  change _ ≤ Real.sqrt (reQuadForm (A + EA) x ^ 2 + reQuadForm (B + EB) x ^ 2)
  rw [sqrt_eq_norm (reQuadForm (A + EA) x)]
  have := norm_sub_norm_le ((reQuadForm A x : ℂ) + reQuadForm B x * Complex.I)
    ((reQuadForm (A + EA) x : ℂ) + reQuadForm (B + EB) x * Complex.I)
  rw [norm_sub_rev] at this
  linarith

omit [DecidableEq n] in
/-- A pair with a positive definite second matrix is definite: `c(A, B) > 0`. -/
theorem crawfordNumber_pos_of_posDef [Nonempty n] (A : Matrix n n 𝕜) {B : Matrix n n 𝕜}
    (hB : B.PosDef) : 0 < crawfordNumber A B := by
  -- the minimum of the continuous positive `re (xᴴ B x)` on the compact sphere
  have hcont : Continuous fun x : EuclideanSpace 𝕜 n => reQuadForm B x := by
    unfold reQuadForm; fun_prop
  obtain ⟨x₀, hx₀, hmin⟩ := (isCompact_sphere (0 : EuclideanSpace 𝕜 n) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 zero_le_one) hcont.continuousOn
  have hpos : ∀ x : EuclideanSpace 𝕜 n, x ≠ 0 → 0 < reQuadForm B x := fun x hx => by
    have := hB.dotProduct_mulVec_pos (x := WithLp.ofLp x) (by simpa using hx)
    exact (RCLike.pos_iff.1 this).1
  have hx₀0 : x₀ ≠ 0 := by
    intro h; rw [h, mem_sphere_zero_iff_norm, norm_zero] at hx₀; exact zero_ne_one hx₀
  have hm := hpos x₀ hx₀0
  have : Nonempty (Metric.sphere (0 : EuclideanSpace 𝕜 n) 1) := ⟨⟨x₀, hx₀⟩⟩
  refine lt_of_lt_of_le hm ?_
  unfold crawfordNumber
  refine le_ciInf fun x => ?_
  calc reQuadForm B x₀ ≤ reQuadForm B x := hmin x.2
    _ = Real.sqrt (reQuadForm B x ^ 2) := (Real.sqrt_sq (hpos x fun h => by
        have := x.2; rw [h, mem_sphere_zero_iff_norm, norm_zero] at this
        exact zero_ne_one this).le).symm
    _ ≤ Real.sqrt (reQuadForm A x ^ 2 + reQuadForm B x ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (reQuadForm A x)])


/-! ### Stewart's perturbation theorem -/

section Planar

/-- `sin (arctan (a/b)) = a / √(a² + b²)` for `b > 0`. -/
private theorem sin_arctan_div {a b : ℝ} (hb : 0 < b) :
    Real.sin (Real.arctan (a / b)) = a / Real.sqrt (a ^ 2 + b ^ 2) := by
  have h : Real.sqrt (1 + (a / b) ^ 2) = Real.sqrt (a ^ 2 + b ^ 2) / b := by
    rw [show 1 + (a / b) ^ 2 = (a ^ 2 + b ^ 2) / b ^ 2 by field_simp; ring,
      Real.sqrt_div' _ (sq_nonneg b), Real.sqrt_sq hb.le]
  have hs : 0 < Real.sqrt (a ^ 2 + b ^ 2) := Real.sqrt_pos.2 (by positivity)
  rw [Real.sin_arctan, h]
  field_simp

/-- `cos (arctan (a/b)) = b / √(a² + b²)` for `b > 0`. -/
private theorem cos_arctan_div {a b : ℝ} (hb : 0 < b) :
    Real.cos (Real.arctan (a / b)) = b / Real.sqrt (a ^ 2 + b ^ 2) := by
  have h : Real.sqrt (1 + (a / b) ^ 2) = Real.sqrt (a ^ 2 + b ^ 2) / b := by
    rw [show 1 + (a / b) ^ 2 = (a ^ 2 + b ^ 2) / b ^ 2 by field_simp; ring,
      Real.sqrt_div' _ (sq_nonneg b), Real.sqrt_sq hb.le]
  have hs : 0 < Real.sqrt (a ^ 2 + b ^ 2) := Real.sqrt_pos.2 (by positivity)
  rw [Real.cos_arctan, h]
  field_simp

/-- Cauchy–Schwarz in the plane: `|x b - a y| ≤ √(x² + y²) √(a² + b²)`. -/
private theorem abs_cross_le (x y a b : ℝ) :
    |x * b - a * y| ≤ Real.sqrt (x ^ 2 + y ^ 2) * Real.sqrt (a ^ 2 + b ^ 2) := by
  rw [← Real.sqrt_mul (by positivity)]
  refine Real.abs_le_sqrt ?_
  nlinarith [sq_nonneg (x * a + y * b)]

/-- **The planar angle estimate** behind Stewart's theorem: if `u = (b, a)` and `u' = (b', a')` lie
in the open right half-plane, `|u| ≥ c r` and `|u' - u| ≤ ε r` with `ε < c`, then their angles
`arctan (a/b)` and `arctan (a'/b')` differ by at most `arcsin (ε / c)`: the difference `θ` has
`cos θ > 0` (the disc of radius `ε r` about `u` misses the origin's half-plane) and
`|sin θ| = |a' b - a b'| / (|u| |u'|) ≤ |u' - u| / |u|`. -/
private theorem abs_arctan_div_sub_le {a b a' b' c ε r : ℝ} (hb : 0 < b) (hb' : 0 < b')
    (hε : 0 ≤ ε) (hεc : ε < c) (hr : 0 < r) (hu : c * r ≤ Real.sqrt (a ^ 2 + b ^ 2))
    (hd : Real.sqrt ((a' - a) ^ 2 + (b' - b) ^ 2) ≤ ε * r) :
    |Real.arctan (a' / b') - Real.arctan (a / b)| ≤ Real.arcsin (ε / c) := by
  have hc : 0 < c := hε.trans_lt hεc
  set U := Real.sqrt (a ^ 2 + b ^ 2) with hU
  set U' := Real.sqrt (a' ^ 2 + b' ^ 2) with hU'
  set D := Real.sqrt ((a' - a) ^ 2 + (b' - b) ^ 2) with hD
  have hU0 : 0 < U := Real.sqrt_pos.2 (by positivity)
  have hU'0 : 0 < U' := Real.sqrt_pos.2 (by positivity)
  have hU2 : U ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
  have hU'2 : U' ^ 2 = a' ^ 2 + b' ^ 2 := Real.sq_sqrt (by positivity)
  have hD2 : D ^ 2 = (a' - a) ^ 2 + (b' - b) ^ 2 := Real.sq_sqrt (by positivity)
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hDU : D < U := hd.trans_lt ((mul_lt_mul_of_pos_right hεc hr).trans_le hu)
  set θ := Real.arctan (a' / b') - Real.arctan (a / b) with hθ
  have hsin : Real.sin θ = (a' * b - a * b') / (U' * U) := by
    rw [hθ, Real.sin_sub, sin_arctan_div hb', cos_arctan_div hb, cos_arctan_div hb',
      sin_arctan_div hb]
    field_simp
    ring
  have hcos : Real.cos θ = (a' * a + b' * b) / (U' * U) := by
    rw [hθ, Real.cos_sub, cos_arctan_div hb', cos_arctan_div hb, sin_arctan_div hb',
      sin_arctan_div hb]
    field_simp
    ring
  -- `cos θ > 0`
  have hdot : 0 < a' * a + b' * b := by nlinarith [hD2, hU2, hU'2, mul_self_lt_mul_self hD0 hDU]
  have hcos0 : 0 < Real.cos θ := by rw [hcos]; positivity
  have hθlt : |θ| < Real.pi / 2 := by
    have h1 := Real.neg_pi_div_two_lt_arctan (a' / b')
    have h2 := Real.arctan_lt_pi_div_two (a' / b')
    have h3 := Real.neg_pi_div_two_lt_arctan (a / b)
    have h4 := Real.arctan_lt_pi_div_two (a / b)
    rw [abs_lt]
    constructor
    · by_contra h
      push Not at h
      have : Real.cos θ ≤ 0 := by
        rw [← Real.cos_neg]
        exact Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith)
      linarith
    · by_contra h
      push Not at h
      have : Real.cos θ ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le h (by linarith)
      linarith
  -- `|sin θ| ≤ ε / c`
  have hcross : |a' * b - a * b'| ≤ D * U' := by
    have h := abs_cross_le (a' - a) (b' - b) a' b'
    rw [show (a' - a) * b' - a' * (b' - b) = a' * b - a * b' by ring] at h
    exact h
  have hsinle : |Real.sin θ| ≤ ε / c := by
    rw [hsin, abs_div, abs_of_pos (by positivity : 0 < U' * U), div_le_div_iff₀ (by positivity) hc]
    calc |a' * b - a * b'| * c ≤ D * U' * c := by gcongr
      _ = U' * (c * D) := by ring
      _ ≤ U' * (ε * U) := by
          refine mul_le_mul_of_nonneg_left ?_ hU'0.le
          calc c * D ≤ c * (ε * r) := mul_le_mul_of_nonneg_left hd hc.le
            _ = ε * (c * r) := by ring
            _ ≤ ε * U := mul_le_mul_of_nonneg_left hu hε
      _ = ε * (U' * U) := by ring
  have hθ' := abs_lt.1 hθlt
  have hsabs : Real.sin |θ| = |Real.sin θ| := by
    rcases le_or_gt 0 θ with h | h
    · have h1 : θ ≤ Real.pi := by linarith [hθ'.2, Real.pi_pos]
      rw [abs_of_nonneg h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h h1)]
    · have h1 : -Real.pi < θ := by linarith [hθ'.1, Real.pi_pos]
      rw [abs_of_neg h, Real.sin_neg, abs_of_neg (Real.sin_neg_of_neg_of_neg_pi_lt h h1)]
  calc |θ| = Real.arcsin (Real.sin |θ|) :=
        (Real.arcsin_sin (by linarith [abs_nonneg θ, Real.pi_pos]) hθlt.le).symm
    _ ≤ Real.arcsin (ε / c) := Real.arcsin_le_arcsin (by rw [hsabs]; exact hsinle)

/-- Transfer of a pointwise angle bound through max–min: if the sets `{c | P c}`, `{c | P' c}`
have greatest elements `λ`, `μ`, both of the form "some subspace has `c ≤ R x` at all its nonzero
points", and `arctan (R x) - δ ≤ arctan (R' x)` at all nonzero `x`, then
`arctan λ - δ ≤ arctan μ`. -/
private theorem arctan_sub_le_of_isGreatest {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    {i : ℕ} {R R' : V → ℝ} {l m δ : ℝ} (hδ : 0 ≤ δ)
    (hl : IsGreatest {c : ℝ | ∃ S : Submodule 𝕜 V, Module.finrank 𝕜 S = i ∧
      ∀ x ∈ S, x ≠ 0 → c ≤ R x} l)
    (hm : IsGreatest {c : ℝ | ∃ S : Submodule 𝕜 V, Module.finrank 𝕜 S = i ∧
      ∀ x ∈ S, x ≠ 0 → c ≤ R' x} m)
    (h : ∀ x, x ≠ 0 → Real.arctan (R x) - δ ≤ Real.arctan (R' x)) :
    Real.arctan l - δ ≤ Real.arctan m := by
  rcases le_or_gt (Real.arctan l - δ) (-(Real.pi / 2)) with h1 | h1
  · exact h1.trans (Real.neg_pi_div_two_lt_arctan m).le
  have h2 : Real.arctan l - δ < Real.pi / 2 := by
    linarith [Real.arctan_lt_pi_div_two l]
  set c' := Real.tan (Real.arctan l - δ)
  have hc' : Real.arctan c' = Real.arctan l - δ := Real.arctan_tan h1 h2
  obtain ⟨S, hS, hSl⟩ := hl.1
  have hmem : c' ∈ {c : ℝ | ∃ S : Submodule 𝕜 V, Module.finrank 𝕜 S = i ∧
      ∀ x ∈ S, x ≠ 0 → c ≤ R' x} := by
    refine ⟨S, hS, fun x hx hx0 => ?_⟩
    rw [← Real.arctan_strictMono.le_iff_le, hc']
    have := Real.arctan_strictMono.monotone (hSl x hx hx0)
    linarith [h x hx0]
  rw [← hc']
  exact Real.arctan_strictMono.monotone (hm.2 hmem)

end Planar

/-- **Stewart's perturbation theorem for definite pencils, corrected** ([golub2013matrix]
Theorem 8.7.3; G. W. Stewart, Lin. Alg. Appl. 23 (1979)): let `A`, `A + E_A` be Hermitian, `B`
and `B + E_B` positive definite, `ε = √(‖E_A‖₂² + ‖E_B‖₂²)` and `c = c(A, B)` the Crawford number,
with `ε < c`. Then for every `i` the sorted pencil eigenvalues `λ_i` of `(A, B)` and `μ_i` of the
perturbed pair satisfy `sin |arctan λ_i - arctan μ_i| ≤ ε / c`.

The book's `|arctan λ_i - arctan μ_i| ≤ arctan (ε / c)` is false (`n = 1`, `A = 0`, `B = 1`,
`E_A = √3/4`, `E_B = -1/4`: `ε = 1/2 < c = 1` and the difference is `π/6 > arctan (1/2)`), and so
is its claim that the perturbed pencil is automatically symmetric-definite; the positive
definiteness of `B + E_B` is a hypothesis here (a definite pair stays *definite*,
`Matrix.crawfordNumber_sub_le`). Proof: at each `x ≠ 0` the points `u = (xᴴBx, xᴴAx)` and
`u' = (xᴴ(B+E_B)x, xᴴ(A+E_A)x)` of the right half-plane have `|u| ≥ c ‖x‖²`
(`Matrix.crawfordNumber_le_norm_mul`) and `|u' - u| ≤ ε ‖x‖²`, so their angles, the arctangents
of the two Rayleigh quotients, differ by at most `arcsin (ε / c)`; the max–min characterization
(`Matrix.isGreatest_pencilEigenvalues`) transfers the bound index by index. -/
theorem sin_abs_arctan_pencilEigenvalues_sub_le {A B EA EB : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.PosDef) (hA' : (A + EA).IsHermitian) (hB' : (B + EB).PosDef)
    (hε : Real.sqrt (lpOpNorm 2 EA ^ 2 + lpOpNorm 2 EB ^ 2) < crawfordNumber A B)
    (i : Fin (Fintype.card n)) :
    Real.sin |Real.arctan (pencilEigenvalues hA hB i) -
        Real.arctan (pencilEigenvalues hA' hB' i)| ≤
      Real.sqrt (lpOpNorm 2 EA ^ 2 + lpOpNorm 2 EB ^ 2) / crawfordNumber A B := by
  set ε := Real.sqrt (lpOpNorm 2 EA ^ 2 + lpOpNorm 2 EB ^ 2) with hεdef
  set c := crawfordNumber A B with hcdef
  have hε0 : 0 ≤ ε := Real.sqrt_nonneg _
  have hc : 0 < c := hε0.trans_lt hε
  set δ := Real.arcsin (ε / c) with hδ
  have hδ0 : 0 ≤ δ := Real.arcsin_nonneg.2 (div_nonneg hε0 hc.le)
  have hδle : δ ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  set R : (n → 𝕜) → ℝ := fun x =>
    RCLike.re (star x ⬝ᵥ A *ᵥ x) / RCLike.re (star x ⬝ᵥ B *ᵥ x)
  set R' : (n → 𝕜) → ℝ := fun x =>
    RCLike.re (star x ⬝ᵥ (A + EA) *ᵥ x) / RCLike.re (star x ⬝ᵥ (B + EB) *ᵥ x)
  -- the pointwise bound
  have hpt : ∀ x : n → 𝕜, x ≠ 0 → |Real.arctan (R' x) - Real.arctan (R x)| ≤ δ := by
    intro x hx
    set X : EuclideanSpace 𝕜 n := WithLp.toLp 2 x
    have hX : X ≠ 0 := by simpa [X] using hx
    have hr : 0 < ‖X‖ ^ 2 := by positivity
    have hb := (RCLike.pos_iff.1 (hB.dotProduct_mulVec_pos hx)).1
    have hb' := (RCLike.pos_iff.1 (hB'.dotProduct_mulVec_pos hx)).1
    have hu := crawfordNumber_le_norm_mul A B X
    have hd := norm_pair_sub_le A B EA EB X
    rw [show ((reQuadForm (A + EA) X : ℂ) + reQuadForm (B + EB) X * Complex.I) -
        ((reQuadForm A X : ℂ) + reQuadForm B X * Complex.I)
      = ((reQuadForm (A + EA) X - reQuadForm A X : ℝ) : ℂ) +
        (reQuadForm (B + EB) X - reQuadForm B X : ℝ) * Complex.I by
        push_cast; ring, ← sqrt_eq_norm] at hd
    exact abs_arctan_div_sub_le hb hb' hε0 hε hr hu hd
  have hl := isGreatest_pencilEigenvalues hA hB i
  have hm := isGreatest_pencilEigenvalues hA' hB' i
  have h1 := arctan_sub_le_of_isGreatest (R := R) (R' := R') hδ0 hl hm fun x hx =>
    by linarith [(abs_le.1 (hpt x hx)).1]
  have h2 := arctan_sub_le_of_isGreatest (R := R') (R' := R) hδ0 hm hl fun x hx =>
    by linarith [(abs_le.1 (hpt x hx)).2]
  have habs : |Real.arctan (pencilEigenvalues hA hB i) -
      Real.arctan (pencilEigenvalues hA' hB' i)| ≤ δ := abs_le.2 ⟨by linarith, by linarith⟩
  have hεc1 : ε / c ≤ 1 := (div_le_one hc).2 hε.le
  calc Real.sin |Real.arctan (pencilEigenvalues hA hB i) -
        Real.arctan (pencilEigenvalues hA' hB' i)| ≤ Real.sin δ :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [abs_nonneg (Real.arctan
          (pencilEigenvalues hA hB i) - Real.arctan (pencilEigenvalues hA' hB' i)),
          Real.pi_pos]) hδle habs
    _ = ε / c := Real.sin_arcsin (by linarith [div_nonneg hε0 hc.le]) hεc1

/-- **The generalized Rayleigh quotient minimizes the `B⁻¹`-norm residual** ([golub2013matrix]
(8.7.6)–(8.7.7)): for real `A` (the book's symmetry of `A` is not needed), positive definite `B`
and `x ≠ 0`,
`λ ↦ (A x - λ B x)ᵀ B⁻¹ (A x - λ B x)` (the book's `‖A x - λ B x‖²_{B⁻¹}`) is minimized at
`λ = xᵀAx / xᵀBx`: it is the quadratic `xᵀAB⁻¹Ax - 2 λ xᵀAx + λ² xᵀBx`. -/
theorem isMinOn_pencil_residual {A B : Matrix n n ℝ} (hB : B.PosDef)
    {x : n → ℝ} (hx : x ≠ 0) :
    IsMinOn (fun μ : ℝ => (A *ᵥ x - μ • B *ᵥ x) ⬝ᵥ B⁻¹ *ᵥ (A *ᵥ x - μ • B *ᵥ x)) Set.univ
      ((x ⬝ᵥ A *ᵥ x) / (x ⬝ᵥ B *ᵥ x)) := by
  have hBu : IsUnit B.det := (isUnit_iff_isUnit_det B).1 hB.isUnit
  have hBs : Bᵀ = B := by
    have := hB.1; rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hp : 0 < x ⬝ᵥ B *ᵥ x := by simpa using hB.dotProduct_mulVec_pos hx
  set p := x ⬝ᵥ B *ᵥ x
  set q := x ⬝ᵥ A *ᵥ x
  set r := A *ᵥ x ⬝ᵥ B⁻¹ *ᵥ (A *ᵥ x)
  have hBB : B⁻¹ *ᵥ (B *ᵥ x) = x := by rw [mulVec_mulVec, nonsing_inv_mul _ hBu, one_mulVec]
  have e1 : A *ᵥ x ⬝ᵥ B⁻¹ *ᵥ (B *ᵥ x) = q := by
    rw [hBB, dotProduct_comm]
  have e2 : B *ᵥ x ⬝ᵥ B⁻¹ *ᵥ (A *ᵥ x) = q := by
    rw [← vecMul_transpose, hBs, ← dotProduct_mulVec, mulVec_mulVec, mul_nonsing_inv _ hBu,
      one_mulVec]
  have e3 : B *ᵥ x ⬝ᵥ B⁻¹ *ᵥ (B *ᵥ x) = p := by rw [hBB, dotProduct_comm]
  have hf : ∀ μ : ℝ, (A *ᵥ x - μ • B *ᵥ x) ⬝ᵥ B⁻¹ *ᵥ (A *ᵥ x - μ • B *ᵥ x) =
      r - 2 * μ * q + μ ^ 2 * p := fun μ => by
    simp only [mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, e1, e2, e3]
    ring
  intro μ _
  simp only [Set.mem_ofPred_eq, hf]
  have : r - 2 * (q / p) * q + (q / p) ^ 2 * p + p * (μ - q / p) ^ 2 =
      r - 2 * μ * q + μ ^ 2 * p := by
    field_simp
    ring
  nlinarith [mul_nonneg hp.le (sq_nonneg (μ - q / p))]

/-! ### Simultaneous diagonalization by congruence -/

omit [Fintype n] in
/-- A Hermitian diagonal matrix has a real diagonal. -/
private theorem exists_real_of_diagonal_isHermitian {d : n → 𝕜}
    (h : (diagonal d).IsHermitian) : ∃ a : n → ℝ, d = fun i => (a i : 𝕜) := by
  refine ⟨fun i => RCLike.re (d i), funext fun i => ?_⟩
  have := congrFun (congrFun h i) i
  simp only [conjTranspose_apply, diagonal_apply_eq] at this
  exact (RCLike.conj_eq_iff_re.1 this).symm

/-- The key step of [golub2013matrix] Theorem 8.7.1: if `C` is positive semidefinite, `D` is
Hermitian and `ker C ≤ ker D`, then one invertible congruence diagonalizes both. `C = V diag(d) Vᴴ`;
`W = V diag(w)` with `w_i = d_i^{-1/2}` (or `1` where `d_i = 0`) makes `Wᴴ C W = P` a diagonal
`0/1` projection, `Wᴴ D W` vanishes on the kernel coordinates and so commutes with `P`, and a
simultaneous unitary diagonalization of the two finishes
(`Matrix.IsHermitian.exists_unitary_conj_diagonal_of_commute`). -/
theorem exists_isUnit_conj_diagonal_of_posSemidef_of_ker_le {C D : Matrix n n 𝕜}
    (hC : C.PosSemidef) (hD : D.IsHermitian)
    (hker : ∀ x, C *ᵥ x = 0 → D *ᵥ x = 0) :
    ∃ X : Matrix n n 𝕜, IsUnit X ∧ ∃ c e : n → 𝕜,
      star X * C * X = diagonal c ∧ star X * D * X = diagonal e := by
  classical
  have hCh := hC.isHermitian
  set V : Matrix n n 𝕜 := (hCh.eigenvectorUnitary : Matrix n n 𝕜) with hVdef
  set d := hCh.eigenvalues with hd
  have hd0 : ∀ i, 0 ≤ d i := hC.eigenvalues_nonneg
  have hV : star V * C * V = diagonal (fun i => (d i : 𝕜)) := hCh.star_eigenvectorUnitary_mul_mul
  have hVu : V ∈ unitaryGroup n 𝕜 := hCh.eigenvectorUnitary.2
  set w : n → ℝ := fun i => if 0 < d i then (Real.sqrt (d i))⁻¹ else 1 with hw
  have hw0 : ∀ i, w i ≠ 0 := fun i => by
    simp only [hw]; split_ifs with h
    · exact inv_ne_zero (Real.sqrt_pos.2 h).ne'
    · exact one_ne_zero
  set W := V * diagonal (fun i => (w i : 𝕜)) with hWdef
  have hWu : IsUnit W := by
    refine (Unitary.isUnit_coe (U := ⟨V, hVu⟩)).mul ?_
    rw [isUnit_diagonal]; exact Pi.isUnit_iff.2 fun i => (RCLike.ofReal_ne_zero.2 (hw0 i)).isUnit
  set p : n → 𝕜 := fun i => if 0 < d i then 1 else 0 with hp
  have hpw : ∀ i, (w i : 𝕜) * (d i : 𝕜) * (w i : 𝕜) = p i := fun i => by
    simp only [hw, hp]; split_ifs with h
    · have hs := Real.sq_sqrt (hd0 i)
      have hs0 := (Real.sqrt_pos.2 h).ne'
      set r := Real.sqrt (d i)
      have key : r⁻¹ * d i * r⁻¹ = 1 := by rw [← hs]; field_simp
      rw [← RCLike.ofReal_mul, ← RCLike.ofReal_mul, key, RCLike.ofReal_one]
    · have : d i = 0 := le_antisymm (not_lt.1 h) (hd0 i)
      simp [this]
  have hstarW : star W = diagonal (fun i => (w i : 𝕜)) * star V := by
    rw [hWdef, star_mul, star_eq_conjTranspose (diagonal _), diagonal_conjTranspose]
    congr 2; funext i; simp
  have hWC : star W * C * W = diagonal p := by
    rw [hstarW, show diagonal (fun i => (w i : 𝕜)) * star V * C * (V * diagonal fun i => (w i : 𝕜))
      = diagonal (fun i => (w i : 𝕜)) * (star V * C * V) * diagonal fun i => (w i : 𝕜) by
        simp only [Matrix.mul_assoc], hV, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1; funext i; exact hpw i
  set D₁ := star W * D * W with hD₁
  have hD₁h : D₁.IsHermitian := by
    rw [hD₁, star_eq_conjTranspose]; exact isHermitian_conjTranspose_mul_mul W hD
  -- `D₁` vanishes on the kernel columns
  have hcol : ∀ i j, p j = 0 → D₁ i j = 0 := by
    intro i j hj
    have hdj : d j = 0 := by
      by_contra h
      have : 0 < d j := lt_of_le_of_ne (hd0 j) (Ne.symm h)
      simp [hp, this] at hj
    have hCW : C *ᵥ (W *ᵥ Pi.single j 1) = 0 := by
      have hVV : V * star V = 1 := mem_unitaryGroup_iff.1 hVu
      have hC' : C = V * diagonal (fun i => (d i : 𝕜)) * star V := by
        rw [← hV]; simp only [← Matrix.mul_assoc, hVV, Matrix.one_mul]
        rw [Matrix.mul_assoc, hVV, Matrix.mul_one]
      rw [hC', hWdef, mulVec_mulVec]
      have : V * diagonal (fun i => (d i : 𝕜)) * star V * (V * diagonal fun i => (w i : 𝕜)) =
          V * diagonal (fun i => (d i : 𝕜) * w i) := by
        rw [show V * diagonal (fun i => (d i : 𝕜)) * star V * (V * diagonal fun i => (w i : 𝕜)) =
          V * diagonal (fun i => (d i : 𝕜)) * (star V * V) * diagonal fun i => (w i : 𝕜) by
            simp only [Matrix.mul_assoc], mem_unitaryGroup_iff'.1 hVu, Matrix.mul_one,
          Matrix.mul_assoc, diagonal_mul_diagonal]
      rw [this, ← mulVec_mulVec, diagonal_mulVec_single, hdj]
      simp
    have := hker _ hCW
    have h2 : D₁ *ᵥ Pi.single j 1 = 0 := by
      rw [hD₁, ← mulVec_mulVec, ← mulVec_mulVec, this, mulVec_zero]
    have h3 := congrFun h2 i
    rwa [mulVec_single_one, col_apply] at h3
  have hcomm : Commute (diagonal p) D₁ := by
    ext i j
    rw [diagonal_mul, mul_diagonal]
    by_cases hi : p i = 0
    · have : D₁ i j = 0 := by
        have h := congrFun (congrFun hD₁h i) j
        rw [conjTranspose_apply, hcol j i hi, star_zero] at h
        exact h.symm
      rw [this, mul_zero, zero_mul]
    by_cases hj : p j = 0
    · rw [hcol i j hj, mul_zero, zero_mul]
    · have hpi : p i = 1 := by simp only [hp] at hi ⊢; split_ifs at hi ⊢ <;> simp_all
      have hpj : p j = 1 := by simp only [hp] at hj ⊢; split_ifs at hj ⊢ <;> simp_all
      rw [hpi, hpj, one_mul, mul_one]
  have hPh : (diagonal p).IsHermitian := by
    rw [← hWC, star_eq_conjTranspose]; exact isHermitian_conjTranspose_mul_mul W hC.isHermitian
  obtain ⟨U, hU, c, e, hc, he⟩ := hPh.exists_unitary_conj_diagonal_of_commute hD₁h hcomm
  refine ⟨W * U, hWu.mul (Unitary.isUnit_coe (U := ⟨U, hU⟩)), c, e, ?_, ?_⟩
  · rw [star_mul, show star U * star W * C * (W * U) = star U * (star W * C * W) * U by
      simp only [Matrix.mul_assoc], hWC, hc]
  · rw [star_mul, show star U * star W * D * (W * U) = star U * D₁ * U by
      simp only [hD₁, Matrix.mul_assoc], he]

/-- **Simultaneous diagonalization of a semidefinite combination** ([golub2013matrix] Theorem
8.7.1): for Hermitian `A`, `B` and `μ ∈ [0, 1]`, if `C = μ A + (1 - μ) B` is positive semidefinite
and `ker C = ker A ⊓ ker B`, then one invertible congruence diagonalizes `A` and `B`, with real
diagonals. For `μ ≠ 0` diagonalize `C` and `B` (`ker C ≤ ker B`,
`Matrix.exists_isUnit_conj_diagonal_of_posSemidef_of_ker_le`) and read `A = μ⁻¹ (C - (1-μ) B)`
off; for `μ = 0`, `C = B` and `ker B ≤ ker A`. -/
theorem exists_isUnit_conj_diagonal_of_posSemidef_combination {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {μ : ℝ} (hμ : μ ∈ Set.Icc (0 : ℝ) 1)
    (hC : ((μ : 𝕜) • A + ((1 - μ : ℝ) : 𝕜) • B).PosSemidef)
    (hker : ∀ x, ((μ : 𝕜) • A + ((1 - μ : ℝ) : 𝕜) • B) *ᵥ x = 0 ↔ A *ᵥ x = 0 ∧ B *ᵥ x = 0) :
    ∃ X : Matrix n n 𝕜, IsUnit X ∧ ∃ a b : n → ℝ,
      star X * A * X = diagonal (fun i => (a i : 𝕜)) ∧
        star X * B * X = diagonal (fun i => (b i : 𝕜)) := by
  set C := (μ : 𝕜) • A + ((1 - μ : ℝ) : 𝕜) • B with hCdef
  have hdiag : ∀ {X M : Matrix n n 𝕜} {d : n → 𝕜}, M.IsHermitian → star X * M * X = diagonal d →
      ∃ a : n → ℝ, star X * M * X = diagonal fun i => (a i : 𝕜) := by
    intro X M d hM h
    have hh : (diagonal d).IsHermitian := by
      rw [← h, star_eq_conjTranspose]; exact isHermitian_conjTranspose_mul_mul X hM
    obtain ⟨a, rfl⟩ := exists_real_of_diagonal_isHermitian hh
    exact ⟨a, h⟩
  rcases eq_or_ne μ 0 with rfl | hμ0
  · have hCB : C = B := by simp [hCdef]
    rw [hCB] at hC hker
    obtain ⟨X, hX, c, e, hc, he⟩ := exists_isUnit_conj_diagonal_of_posSemidef_of_ker_le hC hA
      fun x hx => ((hker x).1 hx).1
    obtain ⟨a, ha⟩ := hdiag hA he
    obtain ⟨b, hb⟩ := hdiag hB hc
    exact ⟨X, hX, a, b, ha, hb⟩
  · obtain ⟨X, hX, c, e, hc, he⟩ := exists_isUnit_conj_diagonal_of_posSemidef_of_ker_le hC hB
      fun x hx => ((hker x).1 hx).2
    have hAC : A = ((μ : 𝕜)⁻¹) • (C - ((1 - μ : ℝ) : 𝕜) • B) := by
      rw [hCdef, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ (RCLike.ofReal_ne_zero.2 hμ0),
        one_smul]
    have hXA : star X * A * X = diagonal ((μ : 𝕜)⁻¹ • (c - ((1 - μ : ℝ) : 𝕜) • e)) := by
      rw [hAC, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, hc,
        Matrix.mul_smul, Matrix.smul_mul, he]
      ext i j
      by_cases h : i = j <;> simp [h]
    obtain ⟨a, ha⟩ := hdiag hA hXA
    obtain ⟨b, hb⟩ := hdiag hB he
    exact ⟨X, hX, a, b, ha, hb⟩

omit [DecidableEq n] in
/-- For a Hermitian matrix over `ℂ` the quadratic form is real. -/
private theorem star_dotProduct_mulVec_eq_ofReal {M : Matrix n n ℂ} (hM : M.IsHermitian)
    (v : n → ℂ) : star v ⬝ᵥ M *ᵥ v = ((star v ⬝ᵥ M *ᵥ v).re : ℂ) :=
  Complex.ext (by simp) (by simpa using hM.im_star_dotProduct_mulVec_self v)

omit [DecidableEq n] in
/-- **Definite pairs are rotations of pairs with a positive definite second matrix** (Crawford 1976;
Stewart–Sun, *Matrix Perturbation Theory*, Theorem VI.1.18), over `ℂ`: for Hermitian `A`, `B` with
`c(A, B) > 0` there is `θ` with `sin θ A + cos θ B` positive definite. The joint numerical range
`{(xᴴ B x + i xᴴ A x) / ‖x‖²}` is the numerical range of `B + i A`, convex by the
Toeplitz–Hausdorff theorem (`LinearMap.convex_numericalRange`), and its closure misses the disc of
radius `c` about `0`; a real linear functional `z ↦ α re z + β im z` separating it from `0`
(`geometric_hahn_banach_compact_closed`) gives `θ = arg (α + β i)`.

Over `ℝ` the statement is false for `n = 2`: `A = diag(1, -1)`, `B = [[0, 1], [1, 0]]` have
`c(A, B) = 1` (the real joint range is the unit circle) but every `sin θ A + cos θ B` has trace
`0`. -/
theorem exists_posDef_rotation_of_crawfordNumber_pos_complex {A B : Matrix n n ℂ}
    (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hc : 0 < crawfordNumber A B) :
    ∃ θ : ℝ, ((Real.sin θ : ℂ) • A + (Real.cos θ : ℂ) • B).PosDef := by
  classical
  set c := crawfordNumber A B
  have hherm : ∀ θ : ℝ, ((Real.sin θ : ℂ) • A + (Real.cos θ : ℂ) • B).IsHermitian := fun θ =>
    (hA.smul (Complex.conj_ofReal _)).add (hB.smul (Complex.conj_ofReal _))
  rcases isEmpty_or_nonempty n with hn | hn
  · refine ⟨0, posDef_iff_dotProduct_mulVec.2 ⟨hherm 0, fun x hx => ?_⟩⟩
    exact absurd (Subsingleton.elim x 0) hx
  set T : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n := toEuclideanLin (B + Complex.I • A)
  -- the values of the numerical range
  have hinner : ∀ x : EuclideanSpace ℂ n, (inner ℂ x (T x) : ℂ) =
      (reQuadForm B x : ℂ) + (reQuadForm A x : ℂ) * Complex.I := by
    intro x
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    simp only [T, toEuclideanLin_apply, WithLp.ofLp_toLp, add_mulVec, smul_mulVec,
      dotProduct_add, dotProduct_smul, smul_eq_mul, reQuadForm]
    rw [star_dotProduct_mulVec_eq_ofReal hB, star_dotProduct_mulVec_eq_ofReal hA]
    simp only [RCLike.re_to_complex, Complex.ofReal_re]
    ring
  have hself : ∀ x : EuclideanSpace ℂ n, (inner ℂ x x : ℂ) = ((‖x‖ ^ 2 : ℝ) : ℂ) := fun x => by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  have hmem : ∀ z ∈ T.numericalRange, c ≤ ‖z‖ := by
    rintro z ⟨x, hx, rfl⟩
    have hn2 : 0 < ‖x‖ ^ 2 := by positivity
    rw [hinner, hself, norm_div, Complex.norm_add_mul_I, Complex.norm_real,
      Real.norm_of_nonneg hn2.le, le_div_iff₀ hn2, add_comm]
    exact crawfordNumber_le_norm_mul A B x
  set S := closure T.numericalRange
  have hS : Convex ℝ S := (LinearMap.convex_numericalRange T).closure
  have hS0 : (0 : ℂ) ∉ S := by
    have hsub : S ⊆ {z : ℂ | c ≤ ‖z‖} :=
      closure_minimal hmem (isClosed_le continuous_const continuous_norm)
    intro h
    have := hsub h
    simp only [Set.mem_ofPred_eq, norm_zero] at this
    linarith
  obtain ⟨f, u, v, hfu, huv, hfv⟩ := geometric_hahn_banach_compact_closed
    (convex_singleton (0 : ℂ)) isCompact_singleton hS isClosed_closure
    (Set.disjoint_singleton_left.2 hS0)
  have hu : 0 < u := by simpa using hfu 0 rfl
  have hfz : ∀ z : ℂ, f z = f 1 * z.re + f Complex.I * z.im := by
    intro z
    conv_lhs => rw [← Complex.re_add_im z]
    rw [show (z.re : ℂ) + z.im * Complex.I = z.re • (1 : ℂ) + z.im • Complex.I by
      rw [Complex.real_smul, Complex.real_smul, mul_one], map_add, map_smul, map_smul,
      smul_eq_mul, smul_eq_mul]
    ring
  set α := f 1
  set β := f Complex.I
  set w : ℂ := (α : ℂ) + (β : ℂ) * Complex.I with hwdef
  have hwre : w.re = α := by simp [hwdef]
  have hwim : w.im = β := by simp [hwdef]
  -- a value of the numerical range
  have hval : ∀ x : EuclideanSpace ℂ n, x ≠ 0 →
      u < (α * reQuadForm B x + β * reQuadForm A x) / ‖x‖ ^ 2 := by
    intro x hx
    have hzS : inner ℂ x (T x) / inner ℂ x x ∈ S := subset_closure ⟨x, hx, rfl⟩
    have h := huv.trans (hfv _ hzS)
    rw [hfz, hinner, hself, Complex.div_ofReal_re, Complex.div_ofReal_im] at h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, mul_one, sub_zero, Complex.add_im, Complex.mul_im,
      add_zero, zero_add] at h
    rw [add_div, mul_div_assoc, mul_div_assoc]
    exact h
  have hw0 : w ≠ 0 := by
    intro h0
    have h1 : α = 0 := by rw [← hwre, h0, Complex.zero_re]
    have h2 : β = 0 := by rw [← hwim, h0, Complex.zero_im]
    obtain ⟨i⟩ := hn
    have hx : (EuclideanSpace.single i (1 : ℂ)) ≠ 0 := by
      simp
    have := hval _ hx
    rw [h1, h2] at this
    simp at this
    linarith
  refine ⟨Complex.arg w, posDef_iff_dotProduct_mulVec.2 ⟨hherm _, fun y hy => ?_⟩⟩
  set x : EuclideanSpace ℂ n := WithLp.toLp 2 y
  have hx : x ≠ 0 := by simpa [x] using hy
  have hn2 : 0 < ‖x‖ ^ 2 := by positivity
  have hpos : 0 < α * reQuadForm B x + β * reQuadForm A x :=
    (div_pos_iff_of_pos_right hn2).1 (hu.trans (hval x hx))
  rw [add_mulVec, smul_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, dotProduct_smul,
    star_dotProduct_mulVec_eq_ofReal hA, star_dotProduct_mulVec_eq_ofReal hB, smul_eq_mul,
    smul_eq_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add,
    Complex.zero_lt_real, Complex.cos_arg hw0, Complex.sin_arg, hwre, hwim]
  have hnw : 0 < ‖w‖ := norm_pos_iff.2 hw0
  change 0 < β / ‖w‖ * reQuadForm A x + α / ‖w‖ * reQuadForm B x
  rw [show β / ‖w‖ * reQuadForm A x + α / ‖w‖ * reQuadForm B x =
    (α * reQuadForm B x + β * reQuadForm A x) / ‖w‖ by ring]
  exact div_pos hpos hnw

end Matrix

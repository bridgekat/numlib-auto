import Numlib.Analysis.Matrix.SpectralNorm
import Numlib.Analysis.Normed.Ring.CondNumber
import Numlib.Krylov.Subspace
import Numlib.Projection.OneDimensional
import Numlib.Stationary.SPD

/-!
# Richardson's iteration

Richardson's iteration with a preconditioner, `x_{k+1} = x_k + α P⁻¹ (b - A x_k)`, stationary (`α`
fixed) and nonstationary (`α_k`), [quarteroni2000numerical] §4.3.1, (4.23)–(4.30);
[saad2003iterative] Example 4.1 is `P = 1`, [kress1998numerical] §4.4 and [han2009theoretical]
Exercise 5.2.3 are the unpreconditioned case.

* The stationary method is the splitting `M = α⁻¹ P`
  (`Stationary.Splitting.preconditionedRichardson`), which specializes to
  `Stationary.Splitting.richardson` (`P = 1`) and to `Matrix.jorSplitting` (`P = D`); its
  iteration matrix is `R_α = 1 - α P⁻¹ A`
  (`Stationary.Splitting.preconditionedRichardson_iterationOperator`).
* **Theorem 4.8 of [quarteroni2000numerical]**: for any real `α` and any real matrix `M`
  (`= P⁻¹ A`), `ρ(1 - α M) < 1` iff `2 Re λ / (α |λ|²) > 1` for every complex eigenvalue `λ` of `M`
  (`Stationary.Splitting.complexSpectralRadius_one_sub_smul_lt_one_iff_forall`).  Theorem 4.9 —
  real positive spectrum in `[lmin, lmax]`, convergence iff `0 < α < 2/lmax`, optimal parameter
  `2/(lmin + lmax)` — is `Stationary.Splitting.complexSpectralRadius_one_sub_smul_lt_one_iff` and
  `Stationary.Splitting.isMinOn_complexSpectralRadius_one_sub_smul` of `Numlib/Stationary/SPD`.
* **Corollary 4.1** in the generality of the book's closing remark: for positive definite `P` and
  `A` and every `α`, `‖e_{k+1}‖_A ≤ ρ(R_α) ‖e_k‖_A`
  (`Stationary.Splitting.energyNorm_preconditionedRichardson_mulVec_le`); no hypothesis on `P⁻¹ A`.
* **(4.29)**: for a symmetric positive definite `M`, the optimal radius is `(κ₂(M) - 1)/(κ₂(M) + 1)`
  and the optimal parameter `2 ‖M⁻¹‖₂ / (κ₂(M) + 1)`
  (`Stationary.Splitting.complexSpectralRadius_one_sub_smul_optimal_eq_condNumber`,
  `Stationary.Splitting.two_div_add_eq_mul_norm_inv_div_condNumber`).
* The nonstationary iteration `Richardson.iterate`, on a module over a field, with its residual
  update (4.25) (`Richardson.residual_iterate_succ`), the polynomial form of its residuals
  `r_k = p_k(A) r_0` with `p_k = ∏_{j<k} (1 - α_j X)` ((4.51),
  `Richardson.residual_iterate_eq_prod`), its iterates in `x_0 + 𝒦_k(A, r_0)` ((4.53),
  `Richardson.iterate_sub_mem_subspace`), and the gradient method of §4.3.3 as its instance with
  `α_k = ⟪r_k, r_k⟫ / ⟪r_k, A r_k⟫` (`Richardson.iterate_gradient_eq_steepestDescentStep`), whose
  step is `Projection.steepestDescentStep`.
-/

open Filter Topology
open scoped ENNReal NNReal ComplexOrder

namespace Stationary

namespace Splitting

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {𝕜 : Type*} [Field 𝕜]

/-- **The preconditioned Richardson splitting** `M = α⁻¹ P` of `A`, for an invertible preconditioner
`P` and a nonzero parameter `α` ([quarteroni2000numerical] (4.23)); `n = α⁻¹ P - A`. -/
noncomputable def preconditionedRichardson (A : Matrix n n 𝕜) {P : Matrix n n 𝕜} (hP : IsUnit P)
    {α : 𝕜} (hα : α ≠ 0) : Splitting A :=
  ⟨α⁻¹ • P, by
    rw [Algebra.smul_def]
    exact ((isUnit_iff_ne_zero.mpr (inv_ne_zero hα)).map (algebraMap 𝕜 (Matrix n n 𝕜))).mul hP⟩

/-- The `m` of the preconditioned Richardson splitting. -/
@[simp]
theorem preconditionedRichardson_m (A : Matrix n n 𝕜) {P : Matrix n n 𝕜} (hP : IsUnit P) {α : 𝕜}
    (hα : α ≠ 0) : (preconditionedRichardson A hP hα).m = α⁻¹ • P := rfl

/-- The inverse of a nonzero scalar multiple of a unit. -/
private theorem ringInverse_smul {c : 𝕜} (hc : c ≠ 0) {m : Matrix n n 𝕜} (hm : IsUnit m) :
    Ring.inverse (c • m) = c⁻¹ • Ring.inverse m := by
  have h1 : (c • m) * (c⁻¹ • Ring.inverse m) = 1 := by
    rw [smul_mul_smul_comm, mul_inv_cancel₀ hc, Ring.mul_inverse_cancel _ hm, one_smul]
  have h2 : (c⁻¹ • Ring.inverse m) * (c • m) = 1 := by
    rw [smul_mul_smul_comm, inv_mul_cancel₀ hc, Ring.inverse_mul_cancel _ hm, one_smul]
  exact Ring.inverse_unit ⟨c • m, c⁻¹ • Ring.inverse m, h1, h2⟩

/-- **The Richardson iteration matrix** `R_α = 1 - α P⁻¹ A` ([quarteroni2000numerical] §4.3;
`R_P = 1 - P⁻¹ A` at `α = 1`). -/
theorem preconditionedRichardson_iterationOperator (A : Matrix n n 𝕜) {P : Matrix n n 𝕜}
    (hP : IsUnit P) {α : 𝕜} (hα : α ≠ 0) :
    (preconditionedRichardson A hP hα).iterationOperator = 1 - α • (P⁻¹ * A) := by
  rw [Splitting.iterationOperator, preconditionedRichardson_m, ringInverse_smul (inv_ne_zero hα) hP,
    inv_inv, smul_mul_assoc, nonsing_inv_eq_ringInverse]

/-- The unpreconditioned method is `P = 1`: `preconditionedRichardson A isUnit_one hα` is
`Stationary.Splitting.richardson A hα`. -/
theorem preconditionedRichardson_one (A : Matrix n n 𝕜) {α : 𝕜} (hα : α ≠ 0) :
    preconditionedRichardson A isUnit_one hα = richardson A hα := rfl

/-- JOR is Richardson with `P = D` and `α = ω` ([quarteroni2000numerical], the sentence after
(4.24)): `preconditionedRichardson A h hω = jorSplitting A h hω`. -/
theorem preconditionedRichardson_diagPart (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) {ω : 𝕜}
    (hω : ω ≠ 0) : preconditionedRichardson A h hω = jorSplitting A h hω := rfl

/-- The scalar inequality of Theorem 4.8: `|1 - α μ|² < 1 ↔ 1 < 2 Re μ / (α |μ|²)` for `α ≠ 0`,
with Lean's `x / 0 = 0` making both sides false at `μ = 0`. -/
private theorem sq_lt_one_iff_one_lt_div {α r i : ℝ} (hα : α ≠ 0) :
    (1 - α * r) ^ 2 + (α * i) ^ 2 < 1 ↔ 1 < 2 * r / (α * (r ^ 2 + i ^ 2)) := by
  rcases eq_or_ne (r ^ 2 + i ^ 2) 0 with h0 | h0
  · have hr : r = 0 := by nlinarith [sq_nonneg r, sq_nonneg i]
    have hi : i = 0 := by nlinarith [sq_nonneg r, sq_nonneg i]
    subst hr hi
    simp
  · have hpos : 0 < r ^ 2 + i ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h0)
    rcases lt_or_gt_of_ne hα with hneg | hposα
    · rw [one_lt_div_of_neg (mul_neg_of_neg_of_pos hneg hpos)]
      constructor
      · intro h
        nlinarith [mul_pos (neg_pos.mpr hneg) hpos]
      · intro h
        nlinarith [mul_pos (neg_pos.mpr hneg) hpos]
    · rw [one_lt_div (mul_pos hposα hpos)]
      constructor
      · intro h
        nlinarith [mul_pos hposα hpos]
      · intro h
        nlinarith [mul_pos hposα hpos]

/-- **Theorem 4.8 of [quarteroni2000numerical]**: for a real matrix `M` on a nonempty index type
and every real `α`, the stationary Richardson iteration `1 - α M` converges iff
`2 Re λ / (α |λ|²) > 1` for every complex eigenvalue `λ` of `M`.  Applied to `M = P⁻¹ A` and
`Stationary.Splitting.preconditionedRichardson_iterationOperator` this is the book's statement for
any nonsingular `P`.  Lean's `x / 0 = 0` makes the right side false at `α = 0` and at `λ = 0`,
exactly when the left side is. -/
theorem complexSpectralRadius_one_sub_smul_lt_one_iff_forall [Nonempty n] (M : Matrix n n ℝ)
    (α : ℝ) :
    complexSpectralRadius (1 - α • M) < 1 ↔
      ∀ μ ∈ spectrum ℂ (Matrix.complexify M), 1 < 2 * μ.re / (α * ‖μ‖ ^ 2) := by
  obtain ⟨μ₀, v, hv, hμ₀v, -⟩ := exists_eigenvector_norm_eq_complexSpectralRadius M
  have hμ₀ : μ₀ ∈ spectrum ℂ (Matrix.complexify M) :=
    (mem_spectrum_iff_exists_mulVec_eq_smul _ _).mpr ⟨v, hv, hμ₀v⟩
  rw [complexSpectralRadius_lt_one_iff_forall_norm_lt]
  rcases eq_or_ne α 0 with rfl | hα
  · simp only [zero_smul, sub_zero, zero_mul, div_zero]
    constructor
    · intro h
      exfalso
      have h1 : ((1 : ℝ) : ℂ) ∈ spectrum ℂ (Matrix.complexify (1 : Matrix n n ℝ)) := by
        have : Nontrivial (Matrix n n ℂ) := by
          by_contra hcon
          rw [not_nontrivial_iff_subsingleton] at hcon
          exact spectrum.mem_iff.mp hμ₀ (isUnit_of_subsingleton _)
        rw [Matrix.complexify_one, Complex.ofReal_one, spectrum.mem_iff, map_one, sub_self]
        exact not_isUnit_zero
      have := h _ h1
      simp at this
    · intro h
      exact absurd (h μ₀ hμ₀) (by norm_num)
  · have hspec : spectrum ℂ (Matrix.complexify (1 - α • M)) =
        (fun μ : ℂ => ((1 : ℝ) : ℂ) + ((-α : ℝ) : ℂ) * μ) '' spectrum ℂ (Matrix.complexify M) := by
      rw [← spectrum_complexify_affine M (neg_ne_zero.mpr hα)]
      congr 2
      module
    rw [hspec, Set.forall_mem_image]
    refine forall₂_congr fun μ _ => ?_
    have hnorm : ‖((1 : ℝ) : ℂ) + ((-α : ℝ) : ℂ) * μ‖ ^ 2
        = (1 - α * μ.re) ^ 2 + (α * μ.im) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul,
        sub_zero, Complex.add_im, Complex.mul_im, zero_add]
      ring
    rw [← pow_lt_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, hnorm, Complex.sq_norm,
      Complex.normSq_apply, ← sq, ← sq]
    exact sq_lt_one_iff_one_lt_div hα

/-- **Corollary 4.1 of [quarteroni2000numerical]**, in the generality of its closing remark: for
positive definite `P` and `A` and every `α ≠ 0`, the error of the preconditioned Richardson
iteration contracts in the `A`-norm by the spectral radius of `R_α = 1 - α P⁻¹ A`:
`‖R_α e‖_A² ≤ ρ(R_α)² ‖e‖_A²`.  No hypothesis on `P⁻¹ A` is needed; the convergence clause of the
corollary additionally needs `0 < α < 2/λmax` (`complexSpectralRadius_one_sub_smul_lt_one_iff`),
which the book omits. -/
theorem energyNorm_preconditionedRichardson_mulVec_le {A P : Matrix n n ℝ} (hA : A.PosDef)
    (hP : P.PosDef) {α : ℝ} (hα : α ≠ 0) (e : n → ℝ) :
    (A *ᵥ ((1 - α • (P⁻¹ * A)) *ᵥ e)) ⬝ᵥ ((1 - α • (P⁻¹ * A)) *ᵥ e) ≤
      (complexSpectralRadius (1 - α • (P⁻¹ * A))).toReal ^ 2 * ((A *ᵥ e) ⬝ᵥ e) := by
  have hM : (preconditionedRichardson A hP.isUnit hα).m.IsHermitian := by
    rw [preconditionedRichardson_m, IsHermitian, conjTranspose_smul, hP.1.eq]
    simp
  have h := energyNorm_mulVec_iterationOperator_le_complexSpectralRadius
    (preconditionedRichardson A hP.isUnit hα) hA hM e
  rwa [preconditionedRichardson_iterationOperator] at h

section CondNumber

open scoped Matrix.Norms.L2Operator NormedRing

/-- The `ℓ²` operator norm of a real symmetric `M` whose eigenvalues lie in `[lmin, lmax]` with
`0 < lmin` and `lmax` attained is `lmax`. -/
private theorem l2_opNorm_eq_of_spectrum {M : Matrix n n ℝ} (hM : M.IsHermitian) {lmin lmax : ℝ}
    (hsub : spectrum ℝ M ⊆ Set.Icc lmin lmax) (hmax : lmax ∈ spectrum ℝ M) (hpos : 0 < lmin) :
    ‖M‖ = lmax := by
  refine hM.l2_opNorm_eq (fun μ hμ => ?_) ⟨lmax, ?_, ?_⟩
  · rw [hasEigenvalue_toEuclideanLin_iff] at hμ
    have := hsub hμ
    rw [RCLike.re_to_real, abs_of_pos (by linarith [this.1])]
    exact this.2
  · exact (hasEigenvalue_toEuclideanLin_iff M lmax).mpr hmax
  · rw [RCLike.re_to_real, abs_of_pos (by linarith [(hsub hmax).1])]

/-- The `ℓ²` operator norm of the inverse of a real symmetric `M` whose eigenvalues lie in
`[lmin, lmax]` with `0 < lmin` attained is `lmin⁻¹`. -/
private theorem l2_opNorm_inv_eq_of_spectrum {M : Matrix n n ℝ} (hM : M.IsHermitian)
    {lmin lmax : ℝ} (hsub : spectrum ℝ M ⊆ Set.Icc lmin lmax) (hmin : lmin ∈ spectrum ℝ M)
    (hpos : 0 < lmin) : ‖M⁻¹‖ = lmin⁻¹ := by
  refine hM.l2_opNorm_inv_eq hpos (fun μ hμ => ?_) ⟨lmin, ?_, ?_⟩
  · rw [hasEigenvalue_toEuclideanLin_iff] at hμ
    have := hsub hμ
    rw [RCLike.re_to_real, abs_of_pos (by linarith [this.1])]
    exact this.1
  · exact (hasEigenvalue_toEuclideanLin_iff M lmin).mpr hmin
  · rw [RCLike.re_to_real, abs_of_pos hpos]

/-- The `ℓ²` condition number of a real symmetric positive definite `M` is `lmax / lmin`. -/
theorem condNumber_eq_div_of_spectrum {M : Matrix n n ℝ} (hM : M.IsHermitian) {lmin lmax : ℝ}
    (hsub : spectrum ℝ M ⊆ Set.Icc lmin lmax) (hmin : lmin ∈ spectrum ℝ M)
    (hmax : lmax ∈ spectrum ℝ M) (hpos : 0 < lmin) : κ M = lmax / lmin := by
  rw [NormedRing.condNumber, ← nonsing_inv_eq_ringInverse,
    l2_opNorm_eq_of_spectrum hM hsub hmax hpos, l2_opNorm_inv_eq_of_spectrum hM hsub hmin hpos,
    div_eq_mul_inv]

/-- **(4.29) of [quarteroni2000numerical], the optimal radius**: for a real symmetric positive
definite `M` (the book's `P⁻¹ A` when it is symmetric) with `ℓ²` condition number `κ`,
`ρ(1 - (2/(lmin + lmax)) M) = (κ - 1)/(κ + 1)`. -/
theorem complexSpectralRadius_one_sub_smul_optimal_eq_condNumber {M : Matrix n n ℝ}
    (hM : M.IsHermitian) {lmin lmax : ℝ} (hsub : spectrum ℝ M ⊆ Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ M) (hmax : lmax ∈ spectrum ℝ M) (hpos : 0 < lmin) :
    complexSpectralRadius (1 - (2 / (lmin + lmax)) • M)
      = ENNReal.ofReal ((κ M - 1) / (κ M + 1)) := by
  rw [complexSpectralRadius_one_sub_smul_optimal_eq (hM.spectrum_complexify_subset hsub) hmin hmax
    hpos, condNumber_eq_div_of_spectrum hM hsub hmin hmax hpos]
  congr 1
  have hle : lmin ≤ lmax := (hsub hmin).2
  field_simp

/-- **(4.29) of [quarteroni2000numerical], the optimal parameter**: `2/(lmin + lmax) = 2 ‖M⁻¹‖₂ /
(κ₂(M) + 1)` for a real symmetric positive definite `M` (the book writes `‖A⁻¹ P‖₂` for
`‖(P⁻¹ A)⁻¹‖₂`). -/
theorem two_div_add_eq_mul_norm_inv_div_condNumber {M : Matrix n n ℝ} (hM : M.IsHermitian)
    {lmin lmax : ℝ} (hsub : spectrum ℝ M ⊆ Set.Icc lmin lmax) (hmin : lmin ∈ spectrum ℝ M)
    (hmax : lmax ∈ spectrum ℝ M) (hpos : 0 < lmin) :
    2 / (lmin + lmax) = 2 * ‖M⁻¹‖ / (κ M + 1) := by
  rw [condNumber_eq_div_of_spectrum hM hsub hmin hmax hpos,
    l2_opNorm_inv_eq_of_spectrum hM hsub hmin hpos]
  have hle : lmin ≤ lmax := (hsub hmin).2
  field_simp
  ring

end CondNumber

end Splitting

end Stationary

/-! ### The nonstationary iteration -/

namespace Richardson

open Polynomial

section Module

variable {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- **The nonstationary preconditioned Richardson iteration** ([quarteroni2000numerical] (4.24)):
`x_0 = x₀` and `x_{k+1} = x_k + α_k Pinv (b - A x_k)`, for a linear map `A`, a preconditioner
inverse `Pinv`, parameters `α : ℕ → 𝕜`, right-hand side `b` and start `x₀`.  `Pinv = LinearMap.id`
is the unpreconditioned method; the stationary case `α = const` is `Stationary.step` for
`1 - α Pinv A`. -/
noncomputable def iterate (A Pinv : E →ₗ[𝕜] E) (α : ℕ → 𝕜) (b x₀ : E) : ℕ → E
  | 0 => x₀
  | k + 1 => iterate A Pinv α b x₀ k + α k • Pinv (b - A (iterate A Pinv α b x₀ k))

variable (A Pinv : E →ₗ[𝕜] E) (α : ℕ → 𝕜) (b x₀ : E)

/-- The iteration starts at `x₀`. -/
@[simp]
theorem iterate_zero : iterate A Pinv α b x₀ 0 = x₀ := rfl

/-- One step of the iteration: `x_{k+1} = x_k + α_k z_k` with the preconditioned residual
`z_k = Pinv (b - A x_k)`. -/
theorem iterate_succ (k : ℕ) :
    iterate A Pinv α b x₀ (k + 1)
      = iterate A Pinv α b x₀ k + α k • Pinv (b - A (iterate A Pinv α b x₀ k)) := rfl

/-- **The residual update** ([quarteroni2000numerical] (4.25)): `r_{k+1} = r_k - α_k A z_k`, with
`r_k = b - A x_k` and `z_k = Pinv r_k`. -/
theorem residual_iterate_succ (k : ℕ) :
    b - A (iterate A Pinv α b x₀ (k + 1)) =
      (b - A (iterate A Pinv α b x₀ k)) - α k • A (Pinv (b - A (iterate A Pinv α b x₀ k))) := by
  rw [iterate_succ, map_add, map_smul]
  abel

/-- The residual polynomial `p_k = ∏_{j<k} (1 - α_j X)` of the unpreconditioned iteration. -/
noncomputable def residualPoly (k : ℕ) : 𝕜[X] := ∏ j ∈ Finset.range k, (1 - C (α j) * X)

/-- `p_0 = 1`. -/
@[simp]
theorem residualPoly_zero : residualPoly α 0 = 1 := by simp [residualPoly]

/-- `p_{k+1} = p_k (1 - α_k X)`. -/
theorem residualPoly_succ (k : ℕ) :
    residualPoly α (k + 1) = residualPoly α k * (1 - C (α k) * X) := by
  rw [residualPoly, residualPoly, Finset.prod_range_succ]

/-- The residual polynomial takes the value `1` at `0`. -/
@[simp]
theorem residualPoly_eval_zero (k : ℕ) : (residualPoly α k).eval 0 = 1 := by
  simp [residualPoly, eval_prod]

/-- The residual polynomial has degree at most `k`. -/
theorem natDegree_residualPoly_le (k : ℕ) : (residualPoly α k).natDegree ≤ k := by
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ j ∈ Finset.range k, (1 - C (α j) * X : 𝕜[X]).natDegree
      ≤ ∑ _j ∈ Finset.range k, 1 := Finset.sum_le_sum fun j _ => by
        refine (natDegree_sub_le _ _).trans ?_
        rw [natDegree_one, max_eq_right (Nat.zero_le _)]
        exact (natDegree_C_mul_le _ _).trans natDegree_X_le
    _ = k := by simp

/-- **The residuals of the unpreconditioned Richardson iteration** are polynomials in `A` applied
to the initial residual ([quarteroni2000numerical] (4.51)): `r_k = p_k(A) r_0` with
`p_k = ∏_{j<k} (1 - α_j X)`, a polynomial of degree at most `k` with `p_k(0) = 1`.  This is the
observation that opens the Krylov chapter of the book. -/
theorem residual_iterate_eq_prod (k : ℕ) :
    b - A (iterate A LinearMap.id α b x₀ k) = aeval A (residualPoly α k) (b - A x₀) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp : aeval A (1 - C (α k) * X) = 1 - α k • A := by
      rw [map_sub, map_one, map_mul, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one,
        smul_mul_assoc, one_mul]
    rw [residual_iterate_succ, residualPoly_succ, mul_comm, map_mul, Module.End.mul_apply, hp, ih,
      LinearMap.id_apply, LinearMap.sub_apply, Module.End.one_apply, LinearMap.smul_apply]

/-- **The Richardson iterates lie in the affine Krylov space** `x_0 + 𝒦_k(A, r_0)`
([quarteroni2000numerical] (4.53)): `x_k - x_0 = ∑_{j<k} α_j r_j` and `r_j ∈ 𝒦_{j+1}(A, r_0)`. -/
theorem iterate_sub_mem_subspace (k : ℕ) :
    iterate A LinearMap.id α b x₀ k - x₀ ∈ Krylov.subspace A (b - A x₀) k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ, LinearMap.id_apply, add_sub_right_comm]
    refine Submodule.add_mem _ (Krylov.subspace_mono A (b - A x₀) (Nat.le_succ k) ih)
      (Submodule.smul_mem _ _ ?_)
    rw [residual_iterate_eq_prod]
    refine Krylov.aeval_apply_mem_subspace A _ ?_
    exact (degree_le_natDegree.trans
      (WithBot.coe_le_coe.mpr (natDegree_residualPoly_le α k))).trans_lt
        (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self k))

end Module

section Gradient

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **The gradient method is nonstationary Richardson** with `α_k = ⟪r_k, r_k⟫ / ⟪r_k, A r_k⟫`
([quarteroni2000numerical] (4.36)–(4.37)): a sequence `x` with `x 0 = x₀` and
`x (k+1) = Projection.steepestDescentStep A b (x k)` is `Richardson.iterate A id α b x₀` for the
parameters `α k = ⟪r_k, r_k⟫ / ⟪r_k, A r_k⟫` read off along it, `r_k = b - A (x k)`. -/
theorem iterate_gradient_eq_steepestDescentStep (A : E →ₗ[𝕜] E) (b : E) (x : ℕ → E)
    (hsucc : ∀ k, x (k + 1) = Projection.steepestDescentStep A b (x k)) (k : ℕ) :
    x k = iterate A LinearMap.id
      (fun j => inner 𝕜 (b - A (x j)) (b - A (x j)) / inner 𝕜 (b - A (x j)) (A (b - A (x j))))
      b (x 0) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ, hsucc, Projection.steepestDescentStep, Projection.step1, LinearMap.id_apply,
      ← ih]

end Gradient

end Richardson

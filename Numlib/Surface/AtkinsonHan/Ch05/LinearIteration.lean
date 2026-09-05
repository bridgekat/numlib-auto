import Numlib.Surface.AtkinsonHan.Ch05.FixedPoint

/-!
# Atkinson–Han §5.2: applications of the fixed-point theorem to iterative methods

Surface formalization of §5.2.1 and §5.2.2 of Kendall Atkinson and Weimin Han, *Theoretical
Numerical Analysis: A Functional Analysis Framework*, 3rd edition, Springer, 2009.

* Theorem 5.2.1, the scalar case of Theorem 5.1.3 on an interval `[a, b]`, together with the
  derivative criterion `sup_{[a,b]} |T'| ≤ α < 1` for contractivity.
* §5.2.2: the book's matrix splitting `A = N - M` (`BookSplitting`), its iteration matrix
  `N⁻¹ M` and iteration `N x_n = M x_{n-1} + b`; the error equation (5.2.5); convergence when
  `‖N⁻¹ M‖ < 1`; `Gᵏ → 0` iff `r_σ(G) < 1`; convergence for every `x₀` iff `(N⁻¹M)ᵏ → 0` iff
  `r_σ(N⁻¹M) < 1`; and the Jacobi, Gauss–Seidel and SOR splittings.

The Fredholm, Urysohn, Volterra and Picard applications of §5.2.3–§5.2.4 (Theorems 5.2.2–5.2.4)
are deferred: they need the phase-3 `C[a,b]` integral-operator toolkit of `tracker/backbone.md` §7
(bundled integral operators on `C(Icc a b, ℝ)`, their Lipschitz bounds, the Volterra factorial
estimate and the Bielecki norm); see `tracker/atkinsonhan-ch5.md` §3 item 1.

Proofs specialize `Numlib/LinearSolve/Stationary/{Basic,Splitting}.lean`,
`Numlib/LinearAlgebra/Matrix/{Complexify,Hessenberg}.lean` and `Numlib/Nonlinear/FixedPoint.lean`.
-/

open Filter Set Topology
open scoped Matrix

namespace AtkinsonHan.Ch05

section Scalar

variable {a b α : ℝ} {T : ℝ → ℝ}

/-- On `ℝ` the norm of Definition 5.1.2 is the absolute value, which is how the book writes
Theorem 5.2.1. -/
theorem contractiveOn_real_iff {K : Set ℝ} :
    ContractiveOn T K α ↔ 0 ≤ α ∧ α < 1 ∧ ∀ u ∈ K, ∀ v ∈ K, |T u - T v| ≤ α * |u - v| := by
  simp only [ContractiveOn, Real.norm_eq_abs]

/-- **Theorem 5.2.1**: the scalar case of the Banach fixed-point theorem.  A contractive
`T : [a, b] → [a, b]` has a unique fixed point in `[a, b]`, the iteration converges to it from
every starting point, and the three error bounds (5.1.4)–(5.1.6) hold. -/
theorem thm_5_2_1 (hab : a ≤ b) (hT : MapsTo T (Icc a b) (Icc a b))
    (hα : ContractiveOn T (Icc a b) α) :
    (∃! u, u ∈ Icc a b ∧ T u = u) ∧
      ∀ u₀ ∈ Icc a b, ∃ u ∈ Icc a b, T u = u ∧ Tendsto (fun n => T^[n] u₀) atTop (𝓝 u) ∧
        (∀ n, ‖T^[n] u₀ - u‖ ≤ α ^ n / (1 - α) * ‖u₀ - T u₀‖) ∧
        (∀ n, ‖T^[n + 1] u₀ - u‖ ≤ α / (1 - α) * ‖T^[n] u₀ - T^[n + 1] u₀‖) ∧
        (∀ n, ‖T^[n + 1] u₀ - u‖ ≤ α * ‖T^[n] u₀ - u‖) :=
  thm_5_1_3 isClosed_Icc (nonempty_Icc.2 hab) hT hα

/-- The derivative criterion accompanying Theorem 5.2.1: if `|T'| ≤ α < 1` on `[a, b]` then `T` is
contractive there with constant `α`.  This is the scalar case of the backbone's
`lipschitzOnWith_of_hasFDerivWithinAt` (`Numlib/Nonlinear/FixedPoint.lean`), i.e. Mathlib's
`Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le`. -/
theorem thm_5_2_1_deriv {T' : ℝ → ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hT : ∀ x ∈ Icc a b, HasDerivWithinAt T (T' x) (Icc a b) x)
    (hbound : ∀ x ∈ Icc a b, |T' x| ≤ α) : ContractiveOn T (Icc a b) α :=
  (contractiveOn_iff hα0).2
    ⟨hα1, (convex_Icc a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hT hbound⟩

end Scalar

section Splittings

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A square matrix acting on `ι → ℝ` as a continuous linear map; the ambient normed space in
which the backbone's `Stationary.step` operates. -/
noncomputable def mulVecCLM (G : Matrix ι ι ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin G)

omit [DecidableEq ι] in
@[simp]
theorem mulVecCLM_apply (G : Matrix ι ι ℝ) (x : ι → ℝ) : mulVecCLM G x = G *ᵥ x := rfl

theorem mulVecCLM_pow (G : Matrix ι ι ℝ) (k : ℕ) :
    ∀ x : ι → ℝ, (mulVecCLM G ^ k) x = G ^ k *ᵥ x := by
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [pow_succ, pow_succ]
    change (mulVecCLM G ^ k) (mulVecCLM G x) = (G ^ k * G) *ᵥ x
    rw [mulVecCLM_apply, ih, Matrix.mulVec_mulVec]

omit [DecidableEq ι] in
private theorem norm_mulVecCLM_pow_le (G : Matrix ι ι ℝ) (k : ℕ) :
    ‖mulVecCLM G ^ k‖ ≤ ‖mulVecCLM G‖ ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    exact ContinuousLinearMap.norm_id_le
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg _))

/-- Convergence of the matrix powers to `0` is convergence of `Gᵏ v` for every vector `v`. -/
private theorem tendsto_pow_zero_iff_mulVec (G : Matrix ι ι ℝ) :
    Tendsto (fun k => G ^ k) atTop (𝓝 0) ↔
      ∀ v : ι → ℝ, Tendsto (fun k => G ^ k *ᵥ v) atTop (𝓝 0) := by
  constructor
  · intro h v
    have hc : Continuous fun M : Matrix ι ι ℝ => M *ᵥ v :=
      continuous_id.matrix_mulVec continuous_const
    have hcomp := (hc.tendsto 0).comp h
    simpa [Function.comp_def] using hcomp
  · intro h
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    have hj := tendsto_pi_nhds.1 (h (Pi.single j 1)) i
    simpa using hj

/-- §5.2.2: the book's splitting `A = N - M` of a square matrix, with `N` nonsingular. -/
structure BookSplitting (A : Matrix ι ι ℝ) where
  /-- The nonsingular part `N`. -/
  N : Matrix ι ι ℝ
  /-- The remaining part `M`. -/
  M : Matrix ι ι ℝ
  /-- The splitting identity `A = N - M`. -/
  eq : A = N - M
  /-- `N` is nonsingular. -/
  isUnit : IsUnit N

namespace BookSplitting

variable {A : Matrix ι ι ℝ} (s : BookSplitting A)

/-- The iteration matrix `N⁻¹ M` of the splitting. -/
noncomputable def iterMatrix : Matrix ι ι ℝ := s.N⁻¹ * s.M

/-- One step of the iteration `N x_n = M x_{n-1} + b`, that is
`x_n = N⁻¹ M x_{n-1} + N⁻¹ b`. -/
noncomputable def iterStep (b x : ι → ℝ) : ι → ℝ := s.iterMatrix *ᵥ x + s.N⁻¹ *ᵥ b

/-- The corresponding backbone splitting (`Numlib/LinearSolve/Stationary/Splitting.lean`).  Note
the naming swap: the backbone writes `a = m - n` with `m` invertible, the book `A = N - M` with
`N` nonsingular, so `m = N` and `n = M`. -/
def toSplitting : Stationary.Splitting A := ⟨s.N, s.isUnit⟩

@[simp]
theorem toSplitting_m : s.toSplitting.m = s.N := rfl

theorem toSplitting_n : s.toSplitting.n = s.M := by
  have h : s.toSplitting.n = s.N - A := rfl
  have h2 : s.N - A = s.N - (s.N - s.M) := by rw [← s.eq]
  rw [h, h2, sub_sub_cancel]

theorem toSplitting_iterationOperator : s.toSplitting.iterationOperator = s.iterMatrix := by
  rw [Stationary.Splitting.iterationOperator_eq, toSplitting_n, toSplitting_m, iterMatrix,
    Matrix.nonsing_inv_eq_ringInverse]

/-- The book's iteration is the backbone's affine step
(`Stationary.step`, `Numlib/LinearSolve/Stationary/Basic.lean`). -/
theorem iterStep_eq_stationary_step (b : ι → ℝ) :
    s.iterStep b = Stationary.step (mulVecCLM s.iterMatrix) (s.N⁻¹ *ᵥ b) := rfl

/-- The solution of `A x = b` is the fixed point of the iteration. -/
theorem step_fixed {x b : ι → ℝ} (hx : A *ᵥ x = b) :
    mulVecCLM s.iterMatrix x + s.N⁻¹ *ᵥ b = x := by
  have hdet : IsUnit s.N.det := (Matrix.isUnit_iff_isUnit_det _).mp s.isUnit
  have hkey : s.N⁻¹ * (s.N - s.M) = 1 - s.iterMatrix := by
    rw [Matrix.mul_sub, Matrix.nonsing_inv_mul _ hdet, iterMatrix]
  have hb : s.N⁻¹ *ᵥ b = x - s.iterMatrix *ᵥ x := by
    have h1 : s.N⁻¹ *ᵥ b = s.N⁻¹ *ᵥ ((s.N - s.M) *ᵥ x) := by rw [← hx, ← s.eq]
    rw [h1, Matrix.mulVec_mulVec, hkey, Matrix.sub_mulVec, Matrix.one_mulVec]
  simp [hb]

/-- **(5.2.5)**: the error equation `x - x_n = (N⁻¹M)ⁿ (x - x₀)`. -/
theorem eq_5_2_5 {x b : ι → ℝ} (hx : A *ᵥ x = b) (x₀ : ι → ℝ) (k : ℕ) :
    x - (s.iterStep b)^[k] x₀ = s.iterMatrix ^ k *ᵥ (x - x₀) := by
  have h := Stationary.step_iterate_sub (mulVecCLM s.iterMatrix) (s.N⁻¹ *ᵥ b) (s.step_fixed hx)
    x₀ k
  rw [mulVecCLM_pow] at h
  rw [← neg_sub ((s.iterStep b)^[k] x₀) x, iterStep_eq_stationary_step, h, Matrix.mulVec_sub,
    Matrix.mulVec_sub]
  abel

/-- §5.2.2(b): the iteration converges from every `x₀` whenever the iteration matrix has operator
norm less than `1`.  This is the backbone's `Stationary.norm_iterate_sub_le`. -/
theorem tendsto_of_opNorm_lt_one (hG : ‖mulVecCLM s.iterMatrix‖ < 1) {x b : ι → ℝ}
    (hx : A *ᵥ x = b) (x₀ : ι → ℝ) :
    Tendsto (fun k => (s.iterStep b)^[k] x₀) atTop (𝓝 x) := by
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun k => norm_nonneg _)
    (fun k => Stationary.norm_iterate_sub_le _ _ hG (s.step_fixed hx) x₀ k) ?_)
  have h1 : Tendsto (fun k : ℕ => ‖mulVecCLM s.iterMatrix‖ ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hG
  simpa using (h1.div_const (1 - ‖mulVecCLM s.iterMatrix‖)).mul_const
    ‖Stationary.step (mulVecCLM s.iterMatrix) (s.N⁻¹ *ᵥ b) x₀ - x₀‖

/-- §5.2.2(d): the iteration converges from *every* starting point exactly when the powers of the
iteration matrix tend to `0`. -/
theorem forall_tendsto_iff {x b : ι → ℝ} (hx : A *ᵥ x = b) :
    (∀ x₀, Tendsto (fun k => (s.iterStep b)^[k] x₀) atTop (𝓝 x)) ↔
      Tendsto (fun k => s.iterMatrix ^ k) atTop (𝓝 0) := by
  rw [tendsto_pow_zero_iff_mulVec]
  constructor
  · intro h v
    have hv := (h (x - v)).const_sub x
    rw [sub_self] at hv
    have heq : (fun k => x - (s.iterStep b)^[k] (x - v)) = fun k => s.iterMatrix ^ k *ᵥ v := by
      funext k
      simpa using s.eq_5_2_5 hx (x - v) k
    rwa [heq] at hv
  · intro h x₀
    refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
    have heq : (fun k => ‖(s.iterStep b)^[k] x₀ - x‖)
        = fun k => ‖s.iterMatrix ^ k *ᵥ (x - x₀)‖ := by
      funext k
      rw [← norm_neg, neg_sub, s.eq_5_2_5 hx x₀]
    rw [heq]
    simpa using (h (x - x₀)).norm

end BookSplitting

/-- §5.2.2(c): `Gᵏ → 0` if and only if the spectral radius `r_σ(G)`, computed over `ℂ`, is less
than `1`.  This is the backbone's `Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one`. -/
theorem tendsto_pow_iff_complexSpectralRadius_lt_one (G : Matrix ι ι ℝ) :
    Tendsto (fun k => G ^ k) atTop (𝓝 0) ↔ Matrix.complexSpectralRadius G < 1 :=
  Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one G

/-- §5.2.2(c)+(d): the classical criterion — the iteration `N x_n = M x_{n-1} + b` converges for
every starting point if and only if `r_σ(N⁻¹M) < 1`. -/
theorem BookSplitting.forall_tendsto_iff_complexSpectralRadius_lt_one {A : Matrix ι ι ℝ}
    (s : BookSplitting A) {x b : ι → ℝ} (hx : A *ᵥ x = b) :
    (∀ x₀, Tendsto (fun k => (s.iterStep b)^[k] x₀) atTop (𝓝 x)) ↔
      Matrix.complexSpectralRadius s.iterMatrix < 1 :=
  (s.forall_tendsto_iff hx).trans
    (Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one s.iterMatrix)

/-- §5.2.2, relation 1, in the form the book uses it: an operator norm of the iteration matrix
below `1` forces `r_σ < 1`, hence convergence.  The inequality `r_σ(G) ≤ ‖G‖` for an arbitrary
submultiplicative, absolutely homogeneous, positive definite matrix norm is the backbone's
`Matrix.complexSpectralRadius_le_of_norm`, and its instance for the maximum absolute row sum —
which is `‖mulVecCLM G‖`, by Mathlib's `Matrix.linfty_opNorm_eq_opNorm` — is
`Matrix.complexSpectralRadius_le_linfty_opNNNorm`.  Both are stated under the scoped norm
instance on `Matrix ι ι ℝ` that this file deliberately does not open, so the proof below goes
through `Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one` instead. -/
theorem complexSpectralRadius_lt_one_of_opNorm_lt_one {G : Matrix ι ι ℝ}
    (hG : ‖mulVecCLM G‖ < 1) : Matrix.complexSpectralRadius G < 1 := by
  rw [← Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one, tendsto_pow_zero_iff_mulVec]
  intro v
  have hb : ∀ k : ℕ, ‖G ^ k *ᵥ v‖ ≤ ‖mulVecCLM G‖ ^ k * ‖v‖ := fun k =>
    calc ‖G ^ k *ᵥ v‖ = ‖(mulVecCLM G ^ k) v‖ := by rw [mulVecCLM_pow]
      _ ≤ ‖mulVecCLM G ^ k‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖mulVecCLM G‖ ^ k * ‖v‖ :=
          mul_le_mul_of_nonneg_right (norm_mulVecCLM_pow_le G k) (norm_nonneg _)
  have hlim : Tendsto (fun k : ℕ => ‖mulVecCLM G‖ ^ k * ‖v‖) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hG).mul_const ‖v‖
  exact squeeze_zero_norm hb hlim

section Classical

variable [LinearOrder ι]

/-- The Jacobi splitting `N = D`, `M = -(L + U)`, where `A = D + L + U` splits `A` into its
diagonal, strictly lower and strictly upper parts (§5.2.2). -/
noncomputable def jacobi (A : Matrix ι ι ℝ) (h : IsUnit A.diagPart) : BookSplitting A :=
  ⟨A.diagPart, -(A.strictLower + A.strictUpper), by
    rw [sub_neg_eq_add, ← add_assoc, Matrix.diagPart_add_strictLower_add_strictUpper], h⟩

/-- The Gauss–Seidel splitting `N = D + L`, `M = -U` (§5.2.2). -/
noncomputable def gaussSeidel (A : Matrix ι ι ℝ) (h : IsUnit A.diagPart) : BookSplitting A :=
  ⟨A.diagPart + A.strictLower, -A.strictUpper, by
    rw [sub_neg_eq_add, Matrix.diagPart_add_strictLower_add_strictUpper],
    (Matrix.gaussSeidelSplitting A h).isUnit⟩

/-- The SOR splitting `N = D/ω + L`, `M = N - A = (1/ω - 1) D - U` (§5.2.2). -/
noncomputable def sor (A : Matrix ι ι ℝ) (h : IsUnit A.diagPart) {ω : ℝ} (hω : ω ≠ 0) :
    BookSplitting A :=
  ⟨ω⁻¹ • A.diagPart + A.strictLower, (ω⁻¹ - 1) • A.diagPart - A.strictUpper, by
    have hsub : ω⁻¹ • A.diagPart + A.strictLower - ((ω⁻¹ - 1) • A.diagPart - A.strictUpper)
        = A.diagPart + A.strictLower + A.strictUpper := by
      rw [sub_smul, one_smul]
      abel
    rw [hsub, Matrix.diagPart_add_strictLower_add_strictUpper],
    (Matrix.sorSplitting A h hω).isUnit⟩

@[simp]
theorem jacobi_toSplitting (A : Matrix ι ι ℝ) (h : IsUnit A.diagPart) :
    (jacobi A h).toSplitting = Matrix.jacobiSplitting A h := rfl

@[simp]
theorem gaussSeidel_toSplitting (A : Matrix ι ι ℝ) (h : IsUnit A.diagPart) :
    (gaussSeidel A h).toSplitting = Matrix.gaussSeidelSplitting A h := rfl

@[simp]
theorem sor_toSplitting (A : Matrix ι ι ℝ) (h : IsUnit A.diagPart) {ω : ℝ} (hω : ω ≠ 0) :
    (sor A h hω).toSplitting = Matrix.sorSplitting A h hω := rfl

/-- Gauss–Seidel is SOR with `ω = 1` (§5.2.2). -/
theorem sor_one (A : Matrix ι ι ℝ) (h : IsUnit A.diagPart) :
    (sor A h one_ne_zero).N = (gaussSeidel A h).N := by
  change (1 : ℝ)⁻¹ • A.diagPart + A.strictLower = A.diagPart + A.strictLower
  rw [inv_one, one_smul]

end Classical

end Splittings

end AtkinsonHan.Ch05

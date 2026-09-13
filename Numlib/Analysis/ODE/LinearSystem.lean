import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Numlib.Analysis.ODE.Cauchy

/-!
# Linear systems with constant coefficients

The system `y' = A y` for a constant matrix `A : Matrix n n ℂ`, as used by the absolute-stability
and stiffness discussion of [quarteroni2000numerical] §11.9–11.10: the solution
`y t = exp (t A) y₀` (`linear_isSolutionOn_exp_smul`) and its uniqueness
(`linear_isSolutionOn_unique`), the expansion `y t = ∑ⱼ Cⱼ e^{λⱼ t} vⱼ` in an eigenvector basis
when `A = Q Λ Q⁻¹` is diagonalizable (`linear_solution_eq_sum_exp_smul`, the book's (11.82)), the
decay `‖y t‖ → 0` when every eigenvalue has negative real part
(`linear_tendsto_zero_of_re_lt_zero`, (11.83)–(11.84)), the diagonalizing change of variables
`z = Q⁻¹ y`, `z' = Λ z` (`linear_diagonalized_isSolutionOn`, (11.85)), which reduces the system to
`n` scalar test equations `zⱼ' = λⱼ zⱼ` (`isSolutionOn_diagonal_iff`), and the *stiffness quotient*
`r_s = σ / τ` of (11.86), `σ = min Re λⱼ`, `τ = max Re λⱼ` (`stiffnessQuotient`).

Mathlib has the matrix exponential (`NormedSpace.exp` on `Matrix n n ℂ`, with `Matrix.exp_conj`
and `Matrix.exp_diagonal`) and the derivative `hasDerivAt_exp_smul_const'`; the solution is one
composition with the linear map `M ↦ M *ᵥ y₀`, and uniqueness is
`ODE.isSolutionOn_unique_of_lipschitz` for the Lipschitz field `v ↦ A *ᵥ v`. Everything is over
`ℂ` on `n → ℂ`, because the eigenvalues of a real matrix are complex; a real system is read
through the complexified matrix `A.map ofReal`. Diagonalizability is the hypothesis
`A = Q * diagonal μ * Q⁻¹` with `IsUnit Q` — the columns of `Q` are the eigenvectors `vⱼ` and `μ`
the eigenvalues — rather than "`n` distinct eigenvalues", which implies it and is all the book
uses. The stiffness quotient is a definition on the spectrum; the book's "stiff iff `r_s ≫ 1`"
and its Definition 11.14 are informal and get no node.

## Conventions

The scalar `t • A` for `t : ℝ` is the real multiple of the complex matrix, `(t : ℂ) • A`. The
book's `e^{λⱼ t}` is `Complex.exp (μ j * t)`. Time starts at `t₀ = 0`; the initial datum is `y₀`.
-/

open Set Filter Topology Matrix NormedSpace

namespace ODE

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Derivatives of `mulVec` -/

omit [DecidableEq n] in
/-- The derivative of `t ↦ M *ᵥ y t` is `M *ᵥ y' t`: `mulVec` is linear. -/
theorem hasDerivWithinAt_mulVec {m : Type*} [Finite m] (M : Matrix m n ℂ) {y : ℝ → n → ℂ}
    {y' : n → ℂ} {I : Set ℝ} {t : ℝ} (hy : HasDerivWithinAt y y' I t) :
    HasDerivWithinAt (fun t => M *ᵥ y t) (M *ᵥ y') I t := by
  cases nonempty_fintype m
  exact ((LinearMap.toContinuousLinearMap
    M.mulVecLin).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t hy

/-- The map `M ↦ M *ᵥ v` on `Matrix n n ℂ`, as a continuous real-linear map. -/
noncomputable def mulVecRightCLM (v : n → ℂ) : Matrix n n ℂ →L[ℝ] (n → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M *ᵥ v
      map_add' := fun M N => Matrix.add_mulVec M N v
      map_smul' := fun c M => Matrix.smul_mulVec c M v }

omit [DecidableEq n] in
/-- The map `M ↦ M *ᵥ v`, applied. -/
@[simp] theorem mulVecRightCLM_apply (v : n → ℂ) (M : Matrix n n ℂ) :
    mulVecRightCLM v M = M *ᵥ v :=
  rfl

/-- The derivative of `t ↦ exp (t A) y₀` is `A (exp (t A) y₀)`, from `hasDerivAt_exp_smul_const'`
in the normed algebra `Matrix n n ℂ` under the `L^∞` operator norm. -/
theorem hasDerivAt_exp_smul_mulVec (A : Matrix n n ℂ) (y₀ : n → ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => exp (t • A) *ᵥ y₀) (A *ᵥ (exp (t • A) *ᵥ y₀)) t := by
  let _ : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  have h := (mulVecRightCLM y₀).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const' A t)
  exact h.congr_deriv (by simp only [Matrix.mulVec_mulVec]; rfl)

/-! ### The exponential solution -/

/-- **The exponential solution** of `y' = A y`, `y 0 = y₀`: `t ↦ exp (t A) y₀` solves the
system at every time ([quarteroni2000numerical] §11.9). -/
theorem linear_isSolutionOn_exp_smul (A : Matrix n n ℂ) (y₀ : n → ℂ) :
    IsSolutionOn (fun _ v => A *ᵥ v) 0 y₀ univ fun t : ℝ => exp (t • A) *ᵥ y₀ :=
  ⟨by simp, fun t _ => (hasDerivAt_exp_smul_mulVec A y₀ t).hasDerivWithinAt⟩

omit [DecidableEq n] in
/-- The linear field `v ↦ A *ᵥ v` is Lipschitz. -/
theorem exists_lipschitzWith_mulVec (A : Matrix n n ℂ) :
    ∃ L : NNReal, LipschitzWith L fun v : n → ℂ => A *ᵥ v :=
  ⟨_, (LinearMap.toContinuousLinearMap A.mulVecLin).lipschitzWith⟩

/-- **Uniqueness**: every solution of `y' = A y`, `y 0 = y₀` on `[0, T]` is `t ↦ exp (t A) y₀`
there. -/
theorem linear_isSolutionOn_unique {A : Matrix n n ℂ} {y₀ : n → ℂ} {T : ℝ} {y : ℝ → n → ℂ}
    (hy : IsSolutionOn (fun _ v => A *ᵥ v) 0 y₀ (Icc 0 T) y) :
    EqOn y (fun t : ℝ => exp (t • A) *ᵥ y₀) (Icc 0 T) := by
  obtain ⟨L, hL⟩ := exists_lipschitzWith_mulVec A
  have h := (linear_isSolutionOn_exp_smul A y₀).mono (subset_univ (Icc 0 T))
  have := isSolutionOn_unique_of_lipschitz (t₀ := 0) (T := T) (fun _ _ => hL) (by simpa using hy)
    (by simpa using h)
  simpa using this

/-! ### Diagonalizable systems -/

variable {A Q : Matrix n n ℂ} {μ : n → ℂ}

/-- The exponential of a diagonalized matrix: if `A = Q Λ Q⁻¹` with `Λ = diagonal μ` and `Q`
invertible, then `exp (t A) = Q diagonal (e^{t μⱼ}) Q⁻¹`. -/
theorem exp_smul_eq_of_eq_mul_diagonal (hA : A = Q * diagonal μ * Q⁻¹) (hQ : IsUnit Q) (t : ℝ) :
    exp (t • A) = Q * diagonal (fun j => Complex.exp (μ j * t)) * Q⁻¹ := by
  have e : t • A = Q * diagonal (fun j => μ j * t) * Q⁻¹ := by
    rw [hA, ← Matrix.smul_mul, ← Matrix.mul_smul, ← diagonal_smul]
    congr 3
    ext j
    simp [mul_comm]
  rw [e, Matrix.exp_conj _ _ hQ, Matrix.exp_diagonal, Pi.exp_def, Complex.exp_eq_exp_ℂ]

omit [DecidableEq n] in
/-- The column expansion of a matrix-vector product: `Q *ᵥ w = ∑ⱼ wⱼ • (column j of Q)`. -/
theorem mulVec_eq_sum_smul_col (Q : Matrix n n ℂ) (w : n → ℂ) :
    Q *ᵥ w = ∑ j, w j • fun i => Q i j := by
  ext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

/-- **The eigen-expansion of the solution** ([quarteroni2000numerical] (11.82)): if
`A = Q Λ Q⁻¹`, `Λ = diagonal μ`, `Q` invertible (its columns `vⱼ` an eigenvector basis, `μ j = λⱼ`),
then every solution of `y' = A y`, `y 0 = y₀` on `[0, T]` is
`y t = ∑ⱼ Cⱼ e^{λⱼ t} vⱼ` there, with the constants `C = Q⁻¹ y₀` fixed by the initial datum. -/
theorem linear_solution_eq_sum_exp_smul (hA : A = Q * diagonal μ * Q⁻¹) (hQ : IsUnit Q)
    {y₀ : n → ℂ} {T : ℝ} {y : ℝ → n → ℂ} (hy : IsSolutionOn (fun _ v => A *ᵥ v) 0 y₀ (Icc 0 T) y)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    y t = ∑ j, ((Q⁻¹ *ᵥ y₀) j * Complex.exp (μ j * t)) • fun i => Q i j := by
  rw [show y t = exp (t • A) *ᵥ y₀ from linear_isSolutionOn_unique hy ht,
    exp_smul_eq_of_eq_mul_diagonal hA hQ, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_eq_sum_smul_col]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mulVec_diagonal, mul_comm]

/-- **Decay of the solutions** ([quarteroni2000numerical] (11.83)–(11.84)): if `A = Q Λ Q⁻¹` is
diagonalizable and every eigenvalue has negative real part, every solution of `y' = A y` on
`[0, ∞)` tends to zero, because each `e^{λⱼ t} = e^{Re λⱼ t} (cos (Im λⱼ t) + i sin (Im λⱼ t))`
has norm `e^{Re λⱼ t} → 0`. -/
theorem linear_tendsto_zero_of_re_lt_zero (hA : A = Q * diagonal μ * Q⁻¹) (hQ : IsUnit Q)
    (hμ : ∀ j, (μ j).re < 0) {y₀ : n → ℂ} {y : ℝ → n → ℂ}
    (hy : IsSolutionOn (fun _ v => A *ᵥ v) 0 y₀ (Ici 0) y) :
    Tendsto (fun t => ‖y t‖) atTop (𝓝 0) := by
  rw [← tendsto_zero_iff_norm_tendsto_zero]
  have hterm : ∀ j, Tendsto (fun t : ℝ => ((Q⁻¹ *ᵥ y₀) j * Complex.exp (μ j * t)) • fun i => Q i j)
      atTop (𝓝 0) := by
    intro j
    have h1 : Tendsto (fun t : ℝ => Complex.exp (μ j * t)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        sub_zero]
      exact Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (hμ j))
    simpa using (h1.const_mul ((Q⁻¹ *ᵥ y₀) j)).smul_const (fun i => Q i j)
  have hsum := tendsto_finsetSum Finset.univ fun j _ => hterm j
  simp only [Finset.sum_const_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact (linear_solution_eq_sum_exp_smul hA hQ (hy.mono (Icc_subset_Ici_self : Icc 0 t ⊆ Ici 0))
    (right_mem_Icc.2 ht)).symm

/-- **The diagonalizing change of variables** ([quarteroni2000numerical] (11.85)): if
`A = Q Λ Q⁻¹` with `Q` invertible and `y` solves `y' = A y` on `I`, then `z = Q⁻¹ y` solves
`z' = Λ z` on `I`. -/
theorem linear_diagonalized_isSolutionOn (hA : A = Q * diagonal μ * Q⁻¹) (hQ : IsUnit Q)
    {t₀ : ℝ} {y₀ : n → ℂ} {I : Set ℝ} {y : ℝ → n → ℂ}
    (hy : IsSolutionOn (fun _ v => A *ᵥ v) t₀ y₀ I y) :
    IsSolutionOn (fun _ v => diagonal μ *ᵥ v) t₀ (Q⁻¹ *ᵥ y₀) I fun t => Q⁻¹ *ᵥ y t := by
  have hdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ
  refine ⟨by simp [hy.1], fun t ht => ?_⟩
  have h := hasDerivWithinAt_mulVec Q⁻¹ (hy.2 t ht)
  have e : diagonal μ *ᵥ (Q⁻¹ *ᵥ y t) = Q⁻¹ *ᵥ (A *ᵥ y t) := by
    rw [mulVec_mulVec, mulVec_mulVec, hA, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
  change HasDerivWithinAt _ (diagonal μ *ᵥ (Q⁻¹ *ᵥ y t)) I t
  rw [e]
  exact h

/-- The converse of the change of variables: if `z` solves `z' = Λ z` on `I`, then `y = Q z`
solves `y' = A y` on `I`. -/
theorem linear_isSolutionOn_of_diagonalized (hA : A = Q * diagonal μ * Q⁻¹) (hQ : IsUnit Q)
    {t₀ : ℝ} {z₀ : n → ℂ} {I : Set ℝ} {z : ℝ → n → ℂ}
    (hz : IsSolutionOn (fun _ v => diagonal μ *ᵥ v) t₀ z₀ I z) :
    IsSolutionOn (fun _ v => A *ᵥ v) t₀ (Q *ᵥ z₀) I fun t => Q *ᵥ z t := by
  have hdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ
  refine ⟨by simp [hz.1], fun t ht => ?_⟩
  have h := hasDerivWithinAt_mulVec Q (hz.2 t ht)
  have e : A *ᵥ (Q *ᵥ z t) = Q *ᵥ (diagonal μ *ᵥ z t) := by
    rw [mulVec_mulVec, mulVec_mulVec, hA, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet,
      Matrix.mul_one]
  change HasDerivWithinAt _ (A *ᵥ (Q *ᵥ z t)) I t
  rw [e]
  exact h

/-- **A diagonal system is `n` scalar test equations**: `z` solves `z' = diagonal μ *ᵥ z` on `I`
iff every component `zⱼ` solves the scalar equation `zⱼ' = μⱼ zⱼ` on `I`. -/
theorem isSolutionOn_diagonal_iff {t₀ : ℝ} {z₀ : n → ℂ} {I : Set ℝ} {z : ℝ → n → ℂ} :
    IsSolutionOn (fun _ v => diagonal μ *ᵥ v) t₀ z₀ I z ↔
      ∀ j, IsSolutionOn (fun _ w => μ j * w) t₀ (z₀ j) I fun t => z t j := by
  simp only [IsSolutionOn, funext_iff, forall_and, forall_comm (α := n)]
  refine and_congr Iff.rfl (forall_congr' fun t => forall_congr' fun _ => ?_)
  rw [hasDerivWithinAt_pi]
  simp only [mulVec_diagonal]

/-! ### The stiffness quotient -/

/-- **The stiffness quotient** ([quarteroni2000numerical] (11.86)): for a matrix whose
eigenvalues satisfy `σ ≤ Re λⱼ ≤ τ < 0`, `r_s = σ / τ` with `σ = min Re λⱼ` and `τ = max Re λⱼ`,
i.e. `sInf (re '' spectrum) / sSup (re '' spectrum)`. The book calls the system stiff when
`r_s ≫ 1`, which is not a definition. -/
noncomputable def stiffnessQuotient (A : Matrix n n ℂ) : ℝ :=
  sInf (Complex.re '' spectrum ℂ A) / sSup (Complex.re '' spectrum ℂ A)

/-- If the spectrum is nonempty and every eigenvalue has negative real part, the stiffness
quotient is at least `1`: `σ ≤ τ < 0` gives `σ / τ ≥ 1`. -/
theorem one_le_stiffnessQuotient (A : Matrix n n ℂ) (hne : (spectrum ℂ A).Nonempty)
    (hneg : ∀ μ ∈ spectrum ℂ A, μ.re < 0) : 1 ≤ stiffnessQuotient A := by
  have hfin : (Complex.re '' spectrum ℂ A).Finite := A.finite_spectrum.image _
  have hne' : (Complex.re '' spectrum ℂ A).Nonempty := hne.image _
  have hτ : sSup (Complex.re '' spectrum ℂ A) < 0 := by
    obtain ⟨μ, hμ, hμ'⟩ := hne'.csSup_mem hfin
    rw [← hμ']
    exact hneg μ hμ
  have hστ : sInf (Complex.re '' spectrum ℂ A) ≤ sSup (Complex.re '' spectrum ℂ A) :=
    csInf_le_csSup hne' hfin.bddBelow hfin.bddAbove
  rw [stiffnessQuotient, le_div_iff_of_neg hτ, one_mul]
  exact hστ

end ODE

import Numlib.Eigen.Pencil
import Numlib.Krylov.Convergence.CG
import Numlib.Krylov.Preconditioned
import Numlib.Krylov.ToEuclideanLin
import Numlib.Projection.ConjugateDirection
import Numlib.RingTheory.Polynomial.ChebyshevMinimax
import Numlib.Stationary.ADI
import Numlib.Stationary.Richardson
import NumlibSurface.QuarteroniSaccoSaleri.Chapter04.Section02

/-!
# Quarteroni–Sacco–Saleri §4.3: stationary and nonstationary iterative methods

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §4.3, over the backbone `Numlib/Stationary/Richardson` (the
preconditioned Richardson splitting, Theorems 4.8–4.9, Corollary 4.1, (4.29), the nonstationary
iteration and its residual update), `Numlib/Stationary/SPD` (the optimal parameter),
`Numlib/Eigen/Pencil` (the generalized eigenvalue problem of Remark 4.2),
`Numlib/Analysis/InnerProductSpace/Energy` (the energy functional and its gradient),
`Numlib/Projection/{OneDimensional,Optimality,ConjugateDirection}` (steepest descent, optimality
along a direction, conjugate directions), `Numlib/Krylov/CG` and `Numlib/Krylov/Convergence/CG`
(the conjugate gradient recurrence, its invariants and its Chebyshev bound),
`Numlib/RingTheory/Polynomial/ChebyshevMinimax` (Property 4.6), `Numlib/Krylov/Preconditioned`
(PCG) and `Numlib/Stationary/ADI` (the alternating-direction method).

## Conventions

Two pictures of `ℝⁿ` are used, as in the rest of the chapter. The Richardson methods of
§4.3.1–4.3.2 and the alternating-direction method of §4.3.6 are stationary iterations on
`Fin n → ℝ`, written with `A *ᵥ x` and `x ⬝ᵥ y` and identified with the splitting steps of §4.2
and the affine step `affineStep B f` of §4.1; their convergence is read through Theorem 4.1
(`theorem_4_1`) and the spectral radius `Matrix.complexSpectralRadius`. The gradient and conjugate
gradient methods of §4.3.3–4.3.5, whose subject is an inner product, live on
`EuclideanSpace ℝ (Fin n)`, where a matrix acts as `Matrix.toEuclideanLin A`, the book's `(x, y)`
is `inner ℝ x y` (the two orders agree over `ℝ`), and the energy norm `‖x‖_A = (x, A x)^{1/2}` of
(1.28) is `energyNorm (toEuclideanLin A) x`; the two pictures are related by `WithLp.toLp 2`.
Matrix norms are the spectral norm (Mathlib's scoped `Matrix.Norms.L2Operator`), so that
`K₂(A) = ‖A‖₂ ‖A⁻¹‖₂` is `NormedRing.condNumber A`, written `κ A`. "The eigenvalues of `P⁻¹ A`"
are `spectrum ℂ (complexify (P⁻¹ * A))`; "`P⁻¹ A` has real positive eigenvalues
`λ_1 ≥ … ≥ λ_n > 0`" is the hypothesis triple
`spectrum ℂ (complexify (P⁻¹ * A)) ⊆ Complex.ofReal '' Set.Icc lmin lmax`,
`lmin ∈ spectrum ℝ (P⁻¹ * A)`, `lmax ∈ spectrum ℝ (P⁻¹ * A)` with `0 < lmin` (`lmax = λ_1`,
`lmin = λ_n`); for a symmetric matrix the eigenvalues are Mathlib's
`Matrix.IsHermitian.eigenvalues`.

The conjugate gradient algorithm is written in the book's own letters (`cgStep`, `cg`), with the
book's direction update `p⁽ᵏ⁺¹⁾ = r⁽ᵏ⁺¹⁾ - β_k p⁽ᵏ⁾` of (4.41), whose `β_k` is the *negative* of the
backbone's `CG.beta`; `cg_eq_CG` identifies it with the backbone recurrence `CG.iterate`, and
every property of the method is read off that identification. The preconditioned method
(`pcgStep`, `pcg`) is treated the same way through `Krylov.PCG.iterate`.

## Contents

* `richardsonStep`, `richardsonStep_eq_affineStep`, `richardsonStep_eq`,
  `richardsonStep_jacobi_gaussSeidel`, `nonstationaryRichardson`, `equation_4_25`,
  `toLp_nonstationaryRichardson` — the Richardson methods (4.23)–(4.25).
* `theorem_4_8`, `theorem_4_9`, `theorem_4_9_optimal`, `richardson_monotone_of_posDef`,
  `equation_4_29`, `corollary_4_1`, `corollary_4_1_preconditioned` — §4.3.1.
* `remark_4_2`, `equation_4_33` — the generalized eigenvalue problem of §4.3.2.
* `energy`, `energy_eq_energyFunctional`, `equation_4_34`, `equation_4_35`, `gradientStep`,
  `gradientStep_eq`, `equation_4_37`, `theorem_4_10` — §4.3.3.
* `definition_4_4`, `IsOptimalWrtSubspace`, `definition_4_4_iff`,
  `optimal_preserved_iff_conjugate`, `cgStep`, `cg`, `cgX`, `cgR`, `cgP`, `cgAlpha`, `cgBeta`,
  `cg_eq_CG`, `equation_4_42`, `equation_4_44`, `equation_4_45`, `equation_4_46`, `theorem_4_11`,
  `theorem_4_12_terminates`, `theorem_4_12_orthogonal`, `theorem_4_12_bound`, `equation_4_49`,
  `property_4_6`, `property_4_6_unique`, `exercise_4_12` — §4.3.4.
* `pcgStep`, `pcg`, `pcg_eq_PCG`, `pcg_energyNorm_error_le` — §4.3.5.
* `adiStep`, `adiMatrix`, `adiConst`, `equation_4_50`, `adi_spectralRadius_le`, `adi_tendsto`,
  `adi_spectralRadius_le_sq` — §4.3.6.

The catalogue of preconditioners in §4.3.2 states no result and its Programs 17–18 are code;
Examples 4.4–4.7 are numerical experiments and Remark 4.3 is prose on rounding; none is a node.

## Readings and errata

* **Corollary 4.1.** "The non preconditioned stationary Richardson method is convergent" needs
  `0 < α < 2/λ_max(A)`, the range of Theorem 4.9, which the statement omits; (4.30) holds for every
  `α`. The preconditioned clause asks for `P`, `A` *and* `P⁻¹ A` symmetric positive definite; only
  `P` and `A` are needed, as the book's own closing sentence says (`corollary_4_1_preconditioned`).
* **The sentence after Theorem 4.9** ("if `P⁻¹ A` is symmetric positive definite the convergence
  is monotone with respect to `‖·‖₂` and `‖·‖_A`"): the `‖·‖₂` clause holds as stated, the `‖·‖_A`
  clause needs `P` symmetric (for `A = diag(1, 4)`, `P⁻¹ A = [[2, 1], [1, 2]]` and `α = 3/5`,
  `R_α` increases the `A`-norm of `(1, 0)`). It is stated with that hypothesis
  (`richardson_monotone_of_posDef`).
* **(4.45)** prints `β_k = ‖r⁽ᵏ⁺¹⁾‖²/‖r⁽ᵏ⁾‖²`; with the update (4.41) the sign is negative
  (`equation_4_45`). **(4.46)** prints `β_k/α_{k-1}` for the coefficient of `r⁽ᵏ⁻¹⁾`; it is
  `β_{k-1}/α_{k-1}` (`equation_4_46`). **Theorem 4.12** says the error is orthogonal to the
  directions; it is `A`-orthogonal (`theorem_4_12_orthogonal`). **Definition 4.4** calls the point
  `x⁽ᵏ⁾` a direction.
* **§4.3.6, the vector `f`.** The display after (4.50) prints
  `f = [α₁ (I - α₂ A₁)(I + α₁ A₁)⁻¹ + α₂ I] b`; composing the two half-steps gives
  `f = (I + α₂ A₂)⁻¹ [α₁ (I - α₂ A₁)(I + α₁ A₁)⁻¹ + α₂ I] b`, the leading inverse being the one
  that also opens `B` (`adiConst`, `equation_4_50`).
-/

open Filter Finset Matrix Stationary Topology WithLp
open scoped ENNReal NNReal Matrix.Norms.L2Operator NormedRing

namespace QuarteroniSaccoSaleri.Chapter04

variable {n : ℕ}

/-! ### The Richardson methods (4.23)–(4.25) -/

section Richardson

variable (A P : Matrix (Fin n) (Fin n) ℝ)

/-- The inverse of a nonzero scalar multiple of a square matrix, for Mathlib's junk-valued
inverse: `(c • M)⁻¹ = c⁻¹ • M⁻¹` for every `M` and every `c ≠ 0` (both sides vanish when `M` is
singular). -/
private theorem inv_smul_eq {𝕜 : Type*} [Field 𝕜] {c : 𝕜} (hc : c ≠ 0)
    (M : Matrix (Fin n) (Fin n) 𝕜) : (c • M)⁻¹ = c⁻¹ • M⁻¹ := by
  by_cases hM : IsUnit M.det
  · have h := inv_smul' M (Units.mk0 c hc) hM
    simpa [Units.smul_def] using h
  · have hcM : ¬ IsUnit (c • M).det := by
      rw [det_smul, isUnit_iff_ne_zero, not_not]
      rw [isUnit_iff_ne_zero, not_not] at hM
      simp [hM]
    rw [nonsing_inv_apply_not_isUnit _ hM, nonsing_inv_apply_not_isUnit _ hcM, smul_zero]

/-- **(4.23).** One step `x ↦ x + α P⁻¹ r` of the stationary preconditioned Richardson method with
acceleration parameter `α`, `r = b - A x` being the residual; the `k`-th iterate from `x⁽⁰⁾` is
`(richardsonStep A P α b)^[k] x⁽⁰⁾`. For `P` nonsingular and `α ≠ 0` it is the step of the
splitting `P/α - (P/α - A)` (`richardsonStep_eq`), with iteration matrix `R_α = I - α P⁻¹ A`
(`richardsonStep_eq_affineStep`); Jacobi and Gauss–Seidel are `α = 1` with `P = D` and `P = D - E`
(`richardsonStep_jacobi_gaussSeidel`). -/
noncomputable def richardsonStep (α : ℝ) (b x : Fin n → ℝ) : Fin n → ℝ :=
  x + α • (P⁻¹ *ᵥ (b - A *ᵥ x))

/-- **The iteration matrix `R_α = I - α P⁻¹ A`** of the stationary Richardson method (§4.3, the
display after (4.24)): the step (4.23) is the method (4.2) with `B = R_α` and `f = α P⁻¹ b`, for
every `α` and every `P` (Mathlib's `P⁻¹` is `0` for a singular `P`, and the identity is
algebraic). -/
theorem richardsonStep_eq_affineStep (α : ℝ) (b : Fin n → ℝ) :
    richardsonStep A P α b = affineStep (1 - α • (P⁻¹ * A)) (α • (P⁻¹ *ᵥ b)) := by
  funext x
  simp only [richardsonStep, affineStep, sub_mulVec, one_mulVec, smul_mulVec, mulVec_mulVec,
    mulVec_sub, smul_sub]
  abel

/-- For `P` nonsingular and `α ≠ 0`, the Richardson step (4.23) is the step of the splitting
`A = α⁻¹ P - (α⁻¹ P - A)` of §4.2 (backbone `Stationary.Splitting.preconditionedRichardson`), and
its iteration matrix is `R_α = I - α P⁻¹ A`
(`Stationary.Splitting.preconditionedRichardson_iterationOperator`). -/
theorem richardsonStep_eq {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsUnit P) {α : ℝ} (hα : α ≠ 0)
    (b : Fin n → ℝ) :
    richardsonStep A P α b = (Splitting.preconditionedRichardson A hP hα).mulVecStep b ∧
      (Splitting.preconditionedRichardson A hP hα).iterationOperator = 1 - α • (P⁻¹ * A) := by
  refine ⟨funext fun x => ?_, Splitting.preconditionedRichardson_iterationOperator A hP hα⟩
  rw [Splitting.mulVecStep_eq_add_inv_mulVec, richardsonStep,
    Splitting.preconditionedRichardson_m, inv_smul_eq (inv_ne_zero hα), inv_inv, smul_mulVec]

/-- **The sentence after (4.24).** The Jacobi and Gauss–Seidel methods are stationary Richardson
methods with `α = 1` and `P = D`, respectively `P = D - E` (§4.2.1). -/
theorem richardsonStep_jacobi_gaussSeidel (h : IsUnit (diagPart A)) (b : Fin n → ℝ) :
    richardsonStep A (D A) 1 b = jorSweep A 1 b ∧
      richardsonStep A (D A - E A) 1 b = sorSweep A 1 b := by
  constructor
  · rw [jorSweep_one_eq_mulVecStep A h b, D, (richardsonStep_eq A h one_ne_zero b).1,
      Splitting.preconditionedRichardson_diagPart, jorSplitting_one]
  · have hDE : IsUnit (D A - E A) := by
      rw [D_sub_E]
      exact (gaussSeidelSplitting A h).isUnit
    rw [sorSweep_one_eq_mulVecStep A h b, (richardsonStep_eq A hDE one_ne_zero b).1]
    funext x
    rw [Splitting.mulVecStep_eq_add_inv_mulVec, Splitting.mulVecStep_eq_add_inv_mulVec,
      Splitting.preconditionedRichardson_m, inv_one, one_smul, D_sub_E]
    rfl

/-- **(4.24).** The nonstationary Richardson (semi-iterative) method
`x⁽ᵏ⁺¹⁾ = x⁽ᵏ⁾ + α_k P⁻¹ r⁽ᵏ⁾`, with a parameter `α_k` depending on the step; under `WithLp.toLp 2`
it is the backbone's `Richardson.iterate` (`toLp_nonstationaryRichardson`). -/
noncomputable def nonstationaryRichardson (α : ℕ → ℝ) (b x₀ : Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0 => x₀
  | k + 1 => richardsonStep A P (α k) b (nonstationaryRichardson α b x₀ k)

/-- **(4.25).** With the preconditioned residual `z⁽ᵏ⁾ = P⁻¹ r⁽ᵏ⁾`, one step of (4.24) solves
`P z⁽ᵏ⁾ = r⁽ᵏ⁾`, updates the solution `x⁽ᵏ⁺¹⁾ = x⁽ᵏ⁾ + α_k z⁽ᵏ⁾` and updates the residual
`r⁽ᵏ⁺¹⁾ = r⁽ᵏ⁾ - α_k A z⁽ᵏ⁾` (backbone `Richardson.residual_iterate_succ`); the first clause needs
`P` nonsingular. -/
theorem equation_4_25 (hP : IsUnit P) (α : ℕ → ℝ) (b x₀ : Fin n → ℝ) (k : ℕ) :
    P *ᵥ (P⁻¹ *ᵥ (b - A *ᵥ nonstationaryRichardson A P α b x₀ k)) =
        b - A *ᵥ nonstationaryRichardson A P α b x₀ k ∧
      nonstationaryRichardson A P α b x₀ (k + 1) = nonstationaryRichardson A P α b x₀ k +
        α k • (P⁻¹ *ᵥ (b - A *ᵥ nonstationaryRichardson A P α b x₀ k)) ∧
      b - A *ᵥ nonstationaryRichardson A P α b x₀ (k + 1) =
        (b - A *ᵥ nonstationaryRichardson A P α b x₀ k) -
          α k • (A *ᵥ (P⁻¹ *ᵥ (b - A *ᵥ nonstationaryRichardson A P α b x₀ k))) := by
  refine ⟨mulVec_nonsing_inv_mulVec hP _, rfl, ?_⟩
  simp only [nonstationaryRichardson, richardsonStep, mulVec_add, mulVec_smul]
  abel

/-- Under `WithLp.toLp 2`, the nonstationary method (4.24) is the backbone's `Richardson.iterate`
of the operators `toEuclideanLin A` and `toEuclideanLin P⁻¹` on `EuclideanSpace ℝ (Fin n)`. -/
theorem toLp_nonstationaryRichardson (α : ℕ → ℝ) (b x₀ : Fin n → ℝ) (k : ℕ) :
    (toLp 2 (nonstationaryRichardson A P α b x₀ k) : EuclideanSpace ℝ (Fin n)) =
      Richardson.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) α (toLp 2 b) (toLp 2 x₀) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Richardson.iterate_succ, ← ih]
    rfl

end Richardson

/-! ### §4.3.1 Convergence analysis of the Richardson method -/

section Convergence

variable {A P : Matrix (Fin n) (Fin n) ℝ}

/-- For `P` nonsingular and any `α`, the stationary Richardson method converges to `A⁻¹ b` from
every `x⁽⁰⁾`, for every `b`, iff `ρ(R_α) < 1`: Theorem 4.1 for the method (4.23). For `α ≠ 0` this
is `Splitting.forall_tendsto_iff` of the splitting `richardsonStep_eq`; for `α = 0` the method is
the identity `x ↦ x`, consistent with every system, and Theorem 4.1 applies directly. -/
theorem forall_tendsto_richardsonStep_iff (hP : IsUnit P) (α : ℝ) :
    (∀ b x₀, Tendsto (fun k => (richardsonStep A P α b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b))) ↔
      complexSpectralRadius (1 - α • (P⁻¹ * A)) < 1 := by
  rcases eq_or_ne α 0 with rfl | hα
  · have hstep : ∀ b, richardsonStep A P 0 b = affineStep 1 0 := fun b => by
      rw [richardsonStep_eq_affineStep, zero_smul, sub_zero, zero_smul]
    have hc : ∀ b, definition_4_1 A b 1 0 := fun b => by
      rw [definition_4_1, one_mulVec, add_zero]
    simp only [hstep, zero_smul, sub_zero]
    exact ⟨fun h => (theorem_4_1 (hc 0)).1 (h 0), fun h b => (theorem_4_1 (hc b)).2 h⟩
  · simp only [(richardsonStep_eq A hP hα _).1]
    rw [Splitting.forall_tendsto_iff, Splitting.preconditionedRichardson_iterationOperator]

/-- **Theorem 4.8.** For any nonsingular matrix `P`, the stationary Richardson method (4.23) is
convergent (to the solution `A⁻¹ b`, from every `x⁽⁰⁾` and for every `b`) iff
`2 Re λ_i / (α |λ_i|²) > 1` for every eigenvalue `λ_i ∈ ℂ` of `P⁻¹ A` (4.26). Theorem 4.1 applied
to `R_α = I - α P⁻¹ A`, whose eigenvalues are `1 - α λ_i` (backbone
`Stationary.Splitting.complexSpectralRadius_one_sub_smul_lt_one_iff_forall`). At `α = 0` both
sides are false — the iteration is stationary and Lean's `x / 0 = 0` — as they are at an
eigenvalue `λ_i = 0`. -/
theorem theorem_4_8 [NeZero n] (hP : IsUnit P) (α : ℝ) :
    (∀ b x₀, Tendsto (fun k => (richardsonStep A P α b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b))) ↔
      ∀ μ ∈ spectrum ℂ (complexify (P⁻¹ * A)), 1 < 2 * μ.re / (α * ‖μ‖ ^ 2) := by
  rw [forall_tendsto_richardsonStep_iff hP]
  exact Splitting.complexSpectralRadius_one_sub_smul_lt_one_iff_forall _ α

/-- **Theorem 4.9, convergence.** Assume `P` is nonsingular and `P⁻¹ A` has positive real
eigenvalues, ordered as `λ_1 ≥ λ_2 ≥ … ≥ λ_n > 0` — that is, its complex spectrum lies in
`[λ_n, λ_1] ⊆ ℝ` with both endpoints attained and `λ_n > 0`. Then the stationary Richardson
method (4.23) is convergent iff `0 < α < 2/λ_1`: the eigenvalues of `R_α` are `1 - α λ_i`
(backbone `Stationary.Splitting.complexSpectralRadius_one_sub_smul_lt_one_iff`). -/
theorem theorem_4_9 (hP : IsUnit P) {lmin lmax : ℝ}
    (hsub : spectrum ℂ (complexify (P⁻¹ * A)) ⊆ Complex.ofReal '' Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ (P⁻¹ * A)) (hmax : lmax ∈ spectrum ℝ (P⁻¹ * A)) (hpos : 0 < lmin)
    (α : ℝ) :
    (∀ b x₀, Tendsto (fun k => (richardsonStep A P α b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b))) ↔
      0 < α ∧ α < 2 / lmax := by
  rw [forall_tendsto_richardsonStep_iff hP]
  exact Splitting.complexSpectralRadius_one_sub_smul_lt_one_iff hsub hmin hmax hpos α

/-- **Theorem 4.9, (4.27)–(4.28).** Under the hypotheses of `theorem_4_9`, the spectral radius of
`R_α = I - α P⁻¹ A` is minimum over `α > 0` at `α_opt = 2/(λ_1 + λ_n)`, with
`ρ_opt = ρ(R_{α_opt}) = (λ_1 - λ_n)/(λ_1 + λ_n)` (backbone
`Stationary.Splitting.isMinOn_complexSpectralRadius_one_sub_smul` and
`Stationary.Splitting.complexSpectralRadius_one_sub_smul_optimal_eq`). -/
theorem theorem_4_9_optimal {lmin lmax : ℝ}
    (hsub : spectrum ℂ (complexify (P⁻¹ * A)) ⊆ Complex.ofReal '' Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ (P⁻¹ * A)) (hmax : lmax ∈ spectrum ℝ (P⁻¹ * A)) (hpos : 0 < lmin) :
    IsMinOn (fun α : ℝ => complexSpectralRadius (1 - α • (P⁻¹ * A))) (Set.Ioi 0)
        (2 / (lmax + lmin)) ∧
      complexSpectralRadius (1 - (2 / (lmax + lmin)) • (P⁻¹ * A)) =
        ENNReal.ofReal ((lmax - lmin) / (lmax + lmin)) := by
  have h1 := Splitting.isMinOn_complexSpectralRadius_one_sub_smul hsub hmin hmax hpos
  have h2 := Splitting.complexSpectralRadius_one_sub_smul_optimal_eq hsub hmin hmax hpos
  rw [add_comm lmin lmax] at h1 h2
  exact ⟨h1, h2⟩

/-- A real symmetric matrix whose real spectrum lies in `[lmin, lmax]` with both endpoints
attained, read in the complex form that `theorem_4_9` takes. -/
theorem spectrum_complexify_subset_of_eigenvalues {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.IsHermitian) {lmin lmax : ℝ} (h : ∀ i, hM.eigenvalues i ∈ Set.Icc lmin lmax) :
    spectrum ℂ (complexify M) ⊆ Complex.ofReal '' Set.Icc lmin lmax := by
  refine hM.spectrum_complexify_subset ?_
  rw [hM.spectrum_real_eq_range_eigenvalues]
  rintro _ ⟨i, rfl⟩
  exact h i

/-- The real spectrum of a real symmetric matrix, recovered from the complex-spectrum hypothesis
of `theorem_4_9`: `spectrum ℂ (complexify M) ⊆ ℝ ∩ [lmin, lmax]` gives
`spectrum ℝ M ⊆ [lmin, lmax]`. -/
theorem spectrum_real_subset_of_spectrum_complexify_subset {M : Matrix (Fin n) (Fin n) ℝ}
    {lmin lmax : ℝ} (hsub : spectrum ℂ (complexify M) ⊆ Complex.ofReal '' Set.Icc lmin lmax) :
    spectrum ℝ M ⊆ Set.Icc lmin lmax := by
  intro μ hμ
  obtain ⟨t, ht, hte⟩ := hsub ((ofReal_mem_spectrum_complexify_iff M μ).mpr hμ)
  rwa [Complex.ofReal_inj.mp hte] at ht

/-- **The sentence after Theorem 4.9.** If `P⁻¹ A` is symmetric positive definite and
`0 < α < 2/λ_1`, `λ_1 = λ_max(P⁻¹ A)`, then `ρ(R_α) < 1` and the convergence of the Richardson
method is monotone with respect to `‖·‖₂`: `‖R_α e‖₂ ≤ ρ(R_α) ‖e‖₂` for every `e`, because `R_α`
is symmetric and `‖R_α‖₂ = ρ(R_α)` (backbone
`Matrix.l2_opNorm_eq_complexSpectralRadius_of_isHermitian`). It is monotone with respect to
`‖·‖_A` as well, `‖R_α e‖_A ≤ ρ(R_α) ‖e‖_A`, when moreover `A` is positive definite and `P` is
symmetric (backbone
`Stationary.Splitting.energyNorm_mulVec_iterationOperator_le_complexSpectralRadius`); the symmetry
of `P` is not implied by that of `P⁻¹ A` and cannot be dropped (see the module documentation). -/
theorem richardson_monotone_of_posDef (hP : IsUnit P) (hM : (P⁻¹ * A).PosDef) {lmin lmax : ℝ}
    (hsub : spectrum ℂ (complexify (P⁻¹ * A)) ⊆ Complex.ofReal '' Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ (P⁻¹ * A)) (hmax : lmax ∈ spectrum ℝ (P⁻¹ * A)) (hpos : 0 < lmin)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 2 / lmax) :
    complexSpectralRadius (1 - α • (P⁻¹ * A)) < 1 ∧
      (∀ e : Fin n → ℝ, ‖(toLp 2 ((1 - α • (P⁻¹ * A)) *ᵥ e) : EuclideanSpace ℝ (Fin n))‖ ≤
        (complexSpectralRadius (1 - α • (P⁻¹ * A))).toReal *
          ‖(toLp 2 e : EuclideanSpace ℝ (Fin n))‖) ∧
      (A.PosDef → P.IsSymm → ∀ e : Fin n → ℝ,
        (A *ᵥ ((1 - α • (P⁻¹ * A)) *ᵥ e)) ⬝ᵥ ((1 - α • (P⁻¹ * A)) *ᵥ e) ≤
          (complexSpectralRadius (1 - α • (P⁻¹ * A))).toReal ^ 2 * ((A *ᵥ e) ⬝ᵥ e)) := by
  refine ⟨(Splitting.complexSpectralRadius_one_sub_smul_lt_one_iff hsub hmin hmax hpos α).2
    ⟨hα0, hα1⟩, fun e => ?_, fun hA hPs e => ?_⟩
  · have hR : (1 - α • (P⁻¹ * A)).IsHermitian := by
      refine IsHermitian.sub ?_ (hM.1.smul (IsSelfAdjoint.all α))
      exact isHermitian_one
    rw [← l2_opNorm_eq_complexSpectralRadius_of_isHermitian hR, ← toEuclideanCLM_toLp,
      ← l2_opNorm_toEuclideanCLM]
    exact ContinuousLinearMap.le_opNorm _ _
  · have hm : (Splitting.preconditionedRichardson A hP hα0.ne').m.IsHermitian := by
      rw [Splitting.preconditionedRichardson_m, IsHermitian, conjTranspose_smul,
        conjTranspose_eq_transpose_of_trivial, hPs.eq]
      simp
    have h := Splitting.energyNorm_mulVec_iterationOperator_le_complexSpectralRadius
      (Splitting.preconditionedRichardson A hP hα0.ne') hA hm e
    rwa [Splitting.preconditionedRichardson_iterationOperator] at h

/-- **(4.29).** If `P⁻¹ A` is symmetric positive definite, with eigenvalues in `[λ_n, λ_1]`,
`0 < λ_n`, both attained, then in terms of `K₂(P⁻¹ A) = ‖P⁻¹ A‖₂ ‖A⁻¹ P‖₂` the optimal radius and
parameter of Theorem 4.9 are `ρ_opt = (K₂(P⁻¹ A) - 1)/(K₂(P⁻¹ A) + 1)` and
`α_opt = 2 ‖A⁻¹ P‖₂ / (K₂(P⁻¹ A) + 1)` (backbone
`Stationary.Splitting.complexSpectralRadius_one_sub_smul_optimal_eq_condNumber` and
`Stationary.Splitting.two_div_add_eq_mul_norm_inv_div_condNumber`, with `(P⁻¹ A)⁻¹ = A⁻¹ P`). -/
theorem equation_4_29 (hM : (P⁻¹ * A).PosDef) {lmin lmax : ℝ}
    (hsub : spectrum ℂ (complexify (P⁻¹ * A)) ⊆ Complex.ofReal '' Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ (P⁻¹ * A)) (hmax : lmax ∈ spectrum ℝ (P⁻¹ * A)) (hpos : 0 < lmin) :
    complexSpectralRadius (1 - (2 / (lmax + lmin)) • (P⁻¹ * A)) =
        ENNReal.ofReal ((κ (P⁻¹ * A) - 1) / (κ (P⁻¹ * A) + 1)) ∧
      2 / (lmax + lmin) = 2 * ‖A⁻¹ * P‖ / (κ (P⁻¹ * A) + 1) := by
  have hsub' := spectrum_real_subset_of_spectrum_complexify_subset hsub
  have hP : IsUnit P.det := by
    have h := isUnit_of_mul_isUnit_left hM.isUnit
    rwa [isUnit_nonsing_inv_iff, isUnit_iff_isUnit_det] at h
  have hinv : A⁻¹ * P = (P⁻¹ * A)⁻¹ := by
    rw [Matrix.mul_inv_rev, nonsing_inv_nonsing_inv P hP]
  rw [add_comm lmax lmin, hinv]
  exact ⟨Splitting.complexSpectralRadius_one_sub_smul_optimal_eq_condNumber hM.1 hsub' hmin hmax
    hpos, Splitting.two_div_add_eq_mul_norm_inv_div_condNumber hM.1 hsub' hmin hmax hpos⟩

-- TODO(backbone): `Matrix.PosDef.pos_of_mem_spectrum`, beside `Matrix.PosDef.eigenvalues_pos`.
/-- A real eigenvalue of a positive definite matrix is positive: it is one of the
`Matrix.IsHermitian.eigenvalues`, all of which are positive. -/
theorem posDef_pos_of_mem_spectrum (hA : A.PosDef) {μ : ℝ} (hμ : μ ∈ spectrum ℝ A) : 0 < μ := by
  rw [hA.1.spectrum_real_eq_range_eigenvalues] at hμ
  obtain ⟨i, rfl⟩ := hμ
  exact hA.eigenvalues_pos i

/-- **Corollary 4.1, the non preconditioned method.** Let `A` be symmetric positive definite, with
extreme eigenvalues `λ_min(A)`, `λ_max(A)`. Then the non preconditioned stationary Richardson method
(`P = I`) is convergent for `0 < α < 2/λ_max(A)` — the range Theorem 4.9 supplies and the
corollary omits (for `α = 3/λ_max(A)` the method diverges) — and, for every `α`,
`‖e⁽ᵏ⁺¹⁾‖_A ≤ ρ(R_α) ‖e⁽ᵏ⁾‖_A` (4.30): the error obeys `e⁽ᵏ⁺¹⁾ = R_α e⁽ᵏ⁾` with `R_α = I - α A`
(`equation_4_4`), and `‖R_α e‖_A² ≤ ρ(R_α)² ‖e‖_A²` for every `e` (backbone
`Stationary.Splitting.energyNorm_preconditionedRichardson_mulVec_le` at `P = I`). -/
theorem corollary_4_1 (hA : A.PosDef) {lmin lmax : ℝ} (hsub : spectrum ℝ A ⊆ Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ A) (hmax : lmax ∈ spectrum ℝ A) (α : ℝ) :
    (0 < α → α < 2 / lmax →
        ∀ b x₀, Tendsto (fun k => (richardsonStep A 1 α b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b))) ∧
      (richardsonStep A 1 α = fun b => affineStep (1 - α • A) (α • b)) ∧
      ∀ e : Fin n → ℝ, (A *ᵥ ((1 - α • A) *ᵥ e)) ⬝ᵥ ((1 - α • A) *ᵥ e) ≤
        (complexSpectralRadius (1 - α • A)).toReal ^ 2 * ((A *ᵥ e) ⬝ᵥ e) := by
  have hpos : 0 < lmin := posDef_pos_of_mem_spectrum hA hmin
  refine ⟨fun hα0 hα1 => ?_, ?_, fun e => ?_⟩
  · rw [forall_tendsto_richardsonStep_iff isUnit_one, inv_one, Matrix.one_mul]
    exact (Splitting.complexSpectralRadius_one_sub_smul_lt_one_iff
      (hA.1.spectrum_complexify_subset hsub) hmin hmax hpos α).2 ⟨hα0, hα1⟩
  · funext b
    rw [richardsonStep_eq_affineStep, inv_one, Matrix.one_mul, one_mulVec]
  · rcases eq_or_ne α 0 with rfl | hα
    · simp only [zero_smul, sub_zero, one_mulVec]
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        simp
      · have : NeZero n := ⟨hn.ne'⟩
        rw [(theorem_4_7_zero (A := A) hA.diagPart.isUnit).2, ENNReal.toReal_one, one_pow,
          one_mul]
    · have h := Splitting.energyNorm_preconditionedRichardson_mulVec_le hA Matrix.PosDef.one hα e
      rwa [inv_one, Matrix.one_mul] at h

/-- **Corollary 4.1, the preconditioned method**, in the generality of the book's closing remark:
if `P` and `A` are symmetric positive definite (no hypothesis on `P⁻¹ A`, which the corollary
also asks to be symmetric positive definite and which is symmetric only when `P` and `A`
commute), then for every `α ≠ 0` the inequality (4.30) holds for the preconditioned method,
`‖R_α e‖_A² ≤ ρ(R_α)² ‖e‖_A²` with `R_α = I - α P⁻¹ A` (backbone
`Stationary.Splitting.energyNorm_preconditionedRichardson_mulVec_le`: `R_α` is `A`-self-adjoint
because `A R_α = A - α A P⁻¹ A` is symmetric). -/
theorem corollary_4_1_preconditioned (hA : A.PosDef) (hP : P.PosDef) {α : ℝ} (hα : α ≠ 0)
    (e : Fin n → ℝ) :
    (A *ᵥ ((1 - α • (P⁻¹ * A)) *ᵥ e)) ⬝ᵥ ((1 - α • (P⁻¹ * A)) *ᵥ e) ≤
      (complexSpectralRadius (1 - α • (P⁻¹ * A))).toReal ^ 2 * ((A *ᵥ e) ⬝ᵥ e) :=
  Splitting.energyNorm_preconditionedRichardson_mulVec_le hA hP hα e

end Convergence

/-! ### §4.3.2 Preconditioning: Remark 4.2 and (4.33) -/

section Preconditioning

variable {A P : Matrix (Fin n) (Fin n) ℝ}

/-- **Remark 4.2, (4.32).** Let `A` and `P` be real symmetric matrices with `P` positive
definite. The eigenvalues `λ` of the preconditioned matrix `P⁻¹ A` are the solutions of the
generalized eigenvalue problem `A x = λ P x` with an eigenvector `x ≠ 0` (backbone
`Matrix.mem_spectrum_inv_mul_iff_exists_mulVec_eq_smul`); they are all real (backbone
`Matrix.pencilSpectrum_subset_range_ofReal_of_posDef`, Theorem 5.7); and each is the generalized
Rayleigh quotient `λ = (A x, x)/(P x, x)` of its eigenvector. -/
theorem remark_4_2 (hA : A.IsHermitian) (hP : P.PosDef) :
    (∀ μ : ℂ, μ ∈ spectrum ℂ (complexify (P⁻¹ * A)) ↔
        ∃ x : Fin n → ℂ, x ≠ 0 ∧ complexify A *ᵥ x = μ • (complexify P *ᵥ x)) ∧
      (∀ μ ∈ spectrum ℂ (complexify (P⁻¹ * A)), μ.im = 0) ∧
      ∀ (μ : ℝ) (x : Fin n → ℝ), x ≠ 0 → A *ᵥ x = μ • (P *ᵥ x) →
        μ = ((A *ᵥ x) ⬝ᵥ x) / ((P *ᵥ x) ⬝ᵥ x) := by
  refine ⟨fun μ => mem_spectrum_inv_mul_iff_exists_mulVec_eq_smul A hP.isUnit μ,
    fun μ hμ => ?_, fun μ x hx hμ => ?_⟩
  · rw [complexify_mul, complexify_inv,
      ← pencilSpectrum_eq_spectrum_of_isUnit _ ((isUnit_complexify_iff P).mpr hP.isUnit)] at hμ
    obtain ⟨t, ht⟩ := pencilSpectrum_subset_range_ofReal_of_posDef
      ((isHermitian_complexify_iff A).mpr hA) (posDef_complexify_iff.mpr hP) hμ
    rw [← ht]
    exact Complex.ofReal_im t
  · have hpos : 0 < (P *ᵥ x) ⬝ᵥ x := by
      have := hP.dotProduct_mulVec_pos hx
      rwa [star_trivial, dotProduct_comm] at this
    rw [hμ, smul_dotProduct, smul_eq_mul, mul_div_cancel_right₀ _ hpos.ne']

/-- **(4.33).** Let `A` and `P` be real symmetric with `P` positive definite, and let
`λ_min(A) ≤ λ_i(A) ≤ λ_max(A)` and `λ_min(P) ≤ λ_i(P) ≤ λ_max(P)` enclose their eigenvalues
(Mathlib's `Matrix.IsHermitian.eigenvalues`), with `0 ≤ λ_min(A)` — the sign the printed bound
presupposes, `A` being positive definite in the book's context — and `0 < λ_min(P)`. Then every
eigenvalue `λ` of `P⁻¹ A` is real and satisfies
`λ_min(A)/λ_max(P) ≤ λ ≤ λ_max(A)/λ_min(P)` (backbone `Matrix.spectrum_inv_mul_subset_Icc_div`,
proved from the generalized Rayleigh quotient rather than the Courant–Fischer theorem). -/
theorem equation_4_33 (hA : A.IsHermitian) (hP : P.PosDef) {a a' p p' : ℝ}
    (haA : ∀ i, hA.eigenvalues i ∈ Set.Icc a a') (hpP : ∀ i, hP.1.eigenvalues i ∈ Set.Icc p p')
    (ha : 0 ≤ a) (hp : 0 < p) :
    spectrum ℂ (complexify (P⁻¹ * A)) ⊆ Complex.ofReal '' Set.Icc (a / p') (a' / p) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [spectrum.of_subsingleton]
    exact Set.empty_subset _
  have hA' := hA.isSymmetricBoundedBy_toEuclideanLin haA
  have hP' := hP.1.isSymmetricBoundedBy_toEuclideanLin hpP
  have hinner : ∀ (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ),
      RCLike.re (inner ℝ (toEuclideanLin M (toLp 2 x)) (toLp 2 x)) = (M *ᵥ x) ⬝ᵥ x := by
    intro M x
    rw [RCLike.re_to_real, toEuclideanLin_toLp, EuclideanSpace.inner_toLp_toLp, star_trivial,
      dotProduct_comm]
  have hnorm : ∀ x : Fin n → ℝ, ‖(toLp 2 x : EuclideanSpace ℝ (Fin n))‖ ^ 2 = x ⬝ᵥ x := by
    intro x
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_toLp_toLp, star_trivial]
  have hp' : 0 < p' := by
    obtain ⟨h1, h2⟩ := hpP ⟨0, hn⟩
    exact hp.trans_le (h1.trans h2)
  refine spectrum_inv_mul_subset_Icc_div hA hP ha hp hp' (fun x => ?_) (fun x => ?_) (fun x => ?_)
    fun x => ?_
  · rw [← hinner, ← hnorm]; exact hA'.le_re_inner _
  · rw [← hinner, ← hnorm]; exact hA'.re_inner_le _
  · rw [← hinner, ← hnorm]; exact hP'.le_re_inner _
  · rw [← hinner, ← hnorm]; exact hP'.re_inner_le _

end Preconditioning

/-! ### §4.3.3 The gradient method -/

section Gradient

variable (A : Matrix (Fin n) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin n))

/-- **The energy of the system** `A x = b` (§4.3.3): the quadratic form
`Φ(y) = ½ yᵀ A y - yᵀ b` on `ℝⁿ`. It is the backbone's `energyFunctional (toEuclideanLin A) b`
(`energy_eq_energyFunctional`). -/
noncomputable def energy (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  1 / 2 * inner ℝ (toEuclideanLin A y) y - inner ℝ y b

/-- The book's energy `Φ` is the backbone's energy functional `½ ⟪A y, y⟫ - ⟪b, y⟫`. -/
theorem energy_eq_energyFunctional (y : EuclideanSpace ℝ (Fin n)) :
    energy A b y = energyFunctional (toEuclideanLin A) b y := by
  simp only [energy, energyFunctional, RCLike.re_to_real, real_inner_comm b y]
  ring

/-- The quadratic form of `A` is that of its symmetric part `½ (Aᵀ + A)`. -/
private theorem energy_eq_energy_symm (y : EuclideanSpace ℝ (Fin n)) :
    energy A b y = energy ((1 / 2 : ℝ) • (Aᵀ + A)) b y := by
  have h : inner ℝ (toEuclideanLin Aᵀ y) y = inner ℝ (toEuclideanLin A y) y := by
    rw [← conjTranspose_eq_transpose_of_trivial, toEuclideanLin_conjTranspose_inner_left,
      real_inner_comm]
  simp only [energy, map_smul, map_add, LinearMap.smul_apply, LinearMap.add_apply, inner_smul_left,
    inner_add_left, h, RCLike.conj_to_real]
  ring

/-- **(4.34).** The gradient of the energy is `∇Φ(y) = ½ (Aᵀ + A) y - b`, which is `A y - b` for
symmetric `A` (backbone `hasGradientAt_energyFunctional_of_finiteDimensional`); consequently a
critical point of `Φ`, `∇Φ(x) = 0`, solves the system `A x = b`. -/
theorem equation_4_34 (y : EuclideanSpace ℝ (Fin n)) :
    HasGradientAt (energy A b) (toEuclideanLin ((1 / 2 : ℝ) • (Aᵀ + A)) y - b) y ∧
      (A.IsSymm → HasGradientAt (energy A b) (toEuclideanLin A y - b) y) ∧
      ∀ x, toEuclideanLin A x - b = 0 → toEuclideanLin A x = b := by
  have hgrad : ∀ M : Matrix (Fin n) (Fin n) ℝ, M.IsSymm →
      HasGradientAt (energy M b) (toEuclideanLin M y - b) y := fun M hM => by
    rw [funext (energy_eq_energyFunctional M b)]
    exact hasGradientAt_energyFunctional_of_finiteDimensional hM.isSymmetric_toEuclideanLin b y
  refine ⟨?_, hgrad A, fun x hx => sub_eq_zero.mp hx⟩
  rw [funext (energy_eq_energy_symm A b)]
  refine hgrad _ ?_
  rw [IsSymm, transpose_smul, transpose_add, transpose_transpose, add_comm]

/-- **(4.35) and the display before it.** If `A` is symmetric positive definite and `x` solves
`A x = b`, then `Φ(y) = Φ(x) + ½ (y - x)ᵀ A (y - x)` for every `y`, that is
`½ ‖y - x‖_A² = Φ(y) - Φ(x)`; hence `Φ(y) > Φ(x)` for `y ≠ x` and `x` is the minimizer of the
energy (backbone `LinearMap.IsSymmetricCoercive.energyFunctional_sub_eq`). -/
theorem equation_4_35 (hA : A.PosDef) {x : EuclideanSpace ℝ (Fin n)} (hx : toEuclideanLin A x = b)
    (y : EuclideanSpace ℝ (Fin n)) :
    energy A b y = energy A b x + 1 / 2 * inner ℝ (toEuclideanLin A (y - x)) (y - x) ∧
      1 / 2 * energyNorm (toEuclideanLin A) (y - x) ^ 2 = energy A b y - energy A b x ∧
      (y ≠ x → energy A b x < energy A b y) := by
  have hA' := (posDef_iff_isSymmetricCoercive A).1 hA
  have h := hA'.energyFunctional_sub_eq hx y
  rw [← energy_eq_energyFunctional, ← energy_eq_energyFunctional] at h
  have hsq := hA'.energyNorm_sq (y - x)
  rw [RCLike.re_to_real] at hsq
  refine ⟨by rw [← hsq]; linarith, by linarith, fun hy => ?_⟩
  have := hA'.energyNorm_pos (sub_ne_zero.mpr hy)
  nlinarith

/-- **(4.36)–(4.37), the gradient (steepest descent) method.** From `x⁽ᵏ⁾`, with the residual
`r⁽ᵏ⁾ = b - A x⁽ᵏ⁾` as descent direction, `x⁽ᵏ⁺¹⁾ = x⁽ᵏ⁾ + α_k r⁽ᵏ⁾` with the dynamic parameter
`α_k = r⁽ᵏ⁾ᵀ r⁽ᵏ⁾ / r⁽ᵏ⁾ᵀ A r⁽ᵏ⁾` minimizing `Φ` along the line; the `k`-th iterate is
`(gradientStep A b)^[k] x⁽⁰⁾`. It is the backbone's `Projection.steepestDescentStep`
(`gradientStep_eq`). -/
noncomputable def gradientStep (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  x + (inner ℝ (b - toEuclideanLin A x) (b - toEuclideanLin A x) /
    inner ℝ (b - toEuclideanLin A x) (toEuclideanLin A (b - toEuclideanLin A x))) •
      (b - toEuclideanLin A x)

/-- The gradient step is the steepest-descent step `Projection.steepestDescentStep` of the
backbone. -/
theorem gradientStep_eq (x : EuclideanSpace ℝ (Fin n)) :
    gradientStep A b x = Projection.steepestDescentStep (toEuclideanLin A) b x := rfl

/-- **The sentence after (4.37).** The gradient method is the nonstationary Richardson method
(4.24) with `P = I` and the parameters `α_k` of (4.37) read along its own iterates: the
backbone's `Richardson.iterate` (`Richardson.iterate_gradient_eq_steepestDescentStep`), and on
coordinates `nonstationaryRichardson A 1` (`toLp_nonstationaryRichardson`). -/
theorem equation_4_37 (x₀ : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    (gradientStep A b)^[k] x₀ = Richardson.iterate (toEuclideanLin A) LinearMap.id
        (fun j => inner ℝ (b - toEuclideanLin A ((gradientStep A b)^[j] x₀))
            (b - toEuclideanLin A ((gradientStep A b)^[j] x₀)) /
          inner ℝ (b - toEuclideanLin A ((gradientStep A b)^[j] x₀))
            (toEuclideanLin A (b - toEuclideanLin A ((gradientStep A b)^[j] x₀)))) b x₀ k ∧
      (gradientStep A b)^[k] x₀ = toLp 2 (nonstationaryRichardson A 1
        (fun j => inner ℝ (b - toEuclideanLin A ((gradientStep A b)^[j] x₀))
            (b - toEuclideanLin A ((gradientStep A b)^[j] x₀)) /
          inner ℝ (b - toEuclideanLin A ((gradientStep A b)^[j] x₀))
            (toEuclideanLin A (b - toEuclideanLin A ((gradientStep A b)^[j] x₀))))
        (ofLp b) (ofLp x₀) k) := by
  have h := Richardson.iterate_gradient_eq_steepestDescentStep (toEuclideanLin A) b
    (fun k => (gradientStep A b)^[k] x₀) (fun k => Function.iterate_succ_apply' _ _ _) k
  simp only [Function.iterate_zero, id_eq] at h
  refine ⟨h, ?_⟩
  rw [toLp_nonstationaryRichardson, inv_one, toEuclideanLin_one, WithLp.toLp_ofLp,
    WithLp.toLp_ofLp]
  exact h

/-- The extreme eigenvalues of a real symmetric matrix of positive order: `lmin` and `lmax` with
`spectrum ℝ A ⊆ [lmin, lmax]`, both attained, and all of `Matrix.IsHermitian.eigenvalues` in
between. -/
theorem exists_extreme_eigenvalues [NeZero n] {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) :
    ∃ lmin lmax : ℝ, spectrum ℝ A ⊆ Set.Icc lmin lmax ∧ lmin ∈ spectrum ℝ A ∧
      lmax ∈ spectrum ℝ A ∧ ∀ i, hA.eigenvalues i ∈ Set.Icc lmin lmax := by
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image univ hA.eigenvalues univ_nonempty
  obtain ⟨i₁, -, hi₁⟩ := Finset.exists_max_image univ hA.eigenvalues univ_nonempty
  have hIcc : ∀ i, hA.eigenvalues i ∈ Set.Icc (hA.eigenvalues i₀) (hA.eigenvalues i₁) :=
    fun i => ⟨hi₀ i (mem_univ i), hi₁ i (mem_univ i)⟩
  refine ⟨hA.eigenvalues i₀, hA.eigenvalues i₁, ?_, ?_, ?_, hIcc⟩
  · rw [hA.spectrum_real_eq_range_eigenvalues]
    rintro _ ⟨i, rfl⟩
    exact hIcc i
  · rw [hA.spectrum_real_eq_range_eigenvalues]
    exact ⟨i₀, rfl⟩
  · rw [hA.spectrum_real_eq_range_eigenvalues]
    exact ⟨i₁, rfl⟩

/-- The spectral condition number of a symmetric positive definite matrix is the ratio of its
extreme eigenvalues, `K₂(A) = λ_max/λ_min` (the sentence after Theorem 4.10; backbone
`Stationary.Splitting.condNumber_eq_div_of_spectrum`). -/
theorem condNumber_eq_div_of_posDef {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) {lmin lmax : ℝ}
    (hsub : spectrum ℝ A ⊆ Set.Icc lmin lmax) (hmin : lmin ∈ spectrum ℝ A)
    (hmax : lmax ∈ spectrum ℝ A) : κ A = lmax / lmin :=
  Splitting.condNumber_eq_div_of_spectrum hA.1 hsub hmin hmax (posDef_pos_of_mem_spectrum hA hmin)

/-- **Theorem 4.10.** Let `A` be symmetric positive definite and `x` the solution of `A x = b`.
Then the gradient method converges for any initial datum `x⁽⁰⁾`, and (4.38)
`‖e⁽ᵏ⁺¹⁾‖_A ≤ (K₂(A) - 1)/(K₂(A) + 1) ‖e⁽ᵏ⁾‖_A`, `K₂(A) = λ_max/λ_min` being the spectral
condition number. The one-step estimate is the backbone's
`Projection.energyNorm_steepestDescentStep_le` (the book's argument: the gradient step beats the
optimal Richardson step of Corollary 4.1 in the `A`-norm), and the convergence follows from the
contraction (`Projection.tendsto_of_forall_norm_succ_le`). -/
theorem theorem_4_10 [NeZero n] (hA : A.PosDef) {x : EuclideanSpace ℝ (Fin n)}
    (hx : toEuclideanLin A x = b) :
    (∀ x₀, Tendsto (fun k => (gradientStep A b)^[k] x₀) atTop (𝓝 x)) ∧
      ∀ y, energyNorm (toEuclideanLin A) (x - gradientStep A b y) ≤
        (κ A - 1) / (κ A + 1) * energyNorm (toEuclideanLin A) (x - y) := by
  obtain ⟨lmin, lmax, hsub, hmin, hmax, hIcc⟩ := exists_extreme_eigenvalues hA.1
  have hpos : 0 < lmin := posDef_pos_of_mem_spectrum hA hmin
  have hle : lmin ≤ lmax := (hsub hmin).2
  have hB := hA.1.isSymmetricBoundedBy_toEuclideanLin hIcc
  have hκ : (κ A - 1) / (κ A + 1) = (lmax - lmin) / (lmax + lmin) := by
    rw [condNumber_eq_div_of_posDef hA hsub hmin hmax]
    field_simp
  have hrate : ∀ y, energyNorm (toEuclideanLin A) (x - gradientStep A b y) ≤
      (lmax - lmin) / (lmax + lmin) * energyNorm (toEuclideanLin A) (x - y) := fun y =>
    Projection.energyNorm_steepestDescentStep_le hpos hB hx y
  refine ⟨fun x₀ => ?_, fun y => hκ ▸ hrate y⟩
  have hρ0 : 0 ≤ (lmax - lmin) / (lmax + lmin) := div_nonneg (by linarith) (by linarith)
  have hρ1 : (lmax - lmin) / (lmax + lmin) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  refine Projection.tendsto_of_forall_norm_succ_le (N := energyNorm (toEuclideanLin A))
    (C := (Real.sqrt lmin)⁻¹) (fun v => ?_) (fun v => energyNorm_nonneg _ _) hρ0 hρ1 fun k => ?_
  · have h := hB.isCoerciveWith.norm_le_energyNorm hpos.le v
    have hs : 0 < Real.sqrt lmin := Real.sqrt_pos.mpr hpos
    rw [← div_eq_inv_mul, le_div_iff₀ hs, mul_comm]
    exact h
  · rw [Function.iterate_succ_apply']
    exact hrate _

end Gradient

/-! ### §4.3.4 The conjugate gradient method -/

section ConjugateGradient

variable (A : Matrix (Fin n) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin n))

/-- **Definition 4.4.** The point `x` (the book says "direction `x⁽ᵏ⁾`") is *optimal with respect
to the direction* `p` when `Φ(x) ≤ Φ(x + λ p)` for every `λ ∈ ℝ` (4.40); the book assumes
`p ≠ 0`, which nothing below needs. -/
def definition_4_4 (x p : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ t : ℝ, energy A b x ≤ energy A b (x + t • p)

/-- **Definition 4.4, second sentence.** `x` is *optimal with respect to a vector space* `V` when it
is optimal with respect to every direction in `V`. -/
def IsOptimalWrtSubspace (x : EuclideanSpace ℝ (Fin n))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ p ∈ V, definition_4_4 A b x p

variable {A b}

/-- **The displays after Definition 4.4.** For `A` symmetric positive definite, `x` is optimal
with respect to `p` iff `p ⟂ r`, `r = b - A x` the residual:
`∂Φ/∂λ (x + λ p) = pᵀ(A x - b) + λ pᵀ A p` vanishes at `λ = 0` iff `pᵀ r = 0` (backbone
`inner_residual_eq_zero_iff_forall_quadratic_add_smul_le`). Hence `x` is optimal with respect to
`V` iff `r ∈ Vᗮ`, and for `x ∈ x₀ + V` that is the Galerkin condition
`IsGalerkin (toEuclideanLin A) b x₀ V x` of the backbone, which is what the proof of Theorem 4.11
uses. -/
theorem definition_4_4_iff (hA : A.PosDef) (x p : EuclideanSpace ℝ (Fin n))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (x₀ : EuclideanSpace ℝ (Fin n)) :
    (definition_4_4 A b x p ↔ inner ℝ p (b - toEuclideanLin A x) = 0) ∧
      (IsOptimalWrtSubspace A b x V ↔ b - toEuclideanLin A x ∈ Vᗮ) ∧
      (x - x₀ ∈ V → (IsOptimalWrtSubspace A b x V ↔ IsGalerkin (toEuclideanLin A) b x₀ V x)) := by
  have hA' := (posDef_iff_isSymmetricCoercive A).1 hA
  have hdir : ∀ p, definition_4_4 A b x p ↔ inner ℝ p (b - toEuclideanLin A x) = 0 := by
    intro p
    rw [definition_4_4, real_inner_comm,
      inner_residual_eq_zero_iff_forall_quadratic_add_smul_le hA'.isSymmetric
        (hA'.isPositive.re_inner_nonneg_left p) b x]
    simp only [energy_eq_energyFunctional]
  have hsub : IsOptimalWrtSubspace A b x V ↔ b - toEuclideanLin A x ∈ Vᗮ := by
    rw [Submodule.mem_orthogonal]
    exact forall₂_congr fun p _ => hdir p
  exact ⟨hdir p, hsub, fun hmem => ⟨fun h => ⟨hmem, hsub.1 h⟩, fun h => hsub.2 h.orth⟩⟩

/-- **The display `0 = pᵀ r⁽ᵏ⁺¹⁾ = pᵀ (r⁽ᵏ⁾ - A q) = -pᵀ A q`.** If `x` is optimal with respect to
`p` and `x' = x + q`, then `x'` is still optimal with respect to `p` iff `pᵀ A q = 0`: to preserve
optimality the descent directions must be `A`-orthogonal, or `A`-conjugate. -/
theorem optimal_preserved_iff_conjugate (hA : A.PosDef) {x p : EuclideanSpace ℝ (Fin n)}
    (hx : definition_4_4 A b x p) (q : EuclideanSpace ℝ (Fin n)) :
    definition_4_4 A b (x + q) p ↔ inner ℝ p (toEuclideanLin A q) = 0 := by
  rw [(definition_4_4_iff hA x p ⊥ 0).1] at hx
  rw [(definition_4_4_iff hA (x + q) p ⊥ 0).1, map_add, sub_add_eq_sub_sub, inner_sub_right, hx,
    zero_sub, neg_eq_zero]

variable (A b)

/-- **(4.39).** The step length `α_k = p⁽ᵏ⁾ᵀ r⁽ᵏ⁾ / p⁽ᵏ⁾ᵀ A p⁽ᵏ⁾` minimizing `Φ(x⁽ᵏ⁾ + α p⁽ᵏ⁾)`,
computed on a state `(x, r, p)`. -/
noncomputable def cgAlphaStep (s : CG.State (EuclideanSpace ℝ (Fin n))) : ℝ :=
  inner ℝ s.p s.r / inner ℝ s.p (toEuclideanLin A s.p)

/-- **The conjugate gradient iteration of §4.3.4**, one step on the state `(x⁽ᵏ⁾, r⁽ᵏ⁾, p⁽ᵏ⁾)` in
the book's letters: `α_k = p⁽ᵏ⁾ᵀ r⁽ᵏ⁾ / p⁽ᵏ⁾ᵀ A p⁽ᵏ⁾` (4.39), `x⁽ᵏ⁺¹⁾ = x⁽ᵏ⁾ + α_k p⁽ᵏ⁾`,
`r⁽ᵏ⁺¹⁾ = r⁽ᵏ⁾ - α_k A p⁽ᵏ⁾`, `β_k = (A p⁽ᵏ⁾)ᵀ r⁽ᵏ⁺¹⁾ / (A p⁽ᵏ⁾)ᵀ p⁽ᵏ⁾` and
`p⁽ᵏ⁺¹⁾ = r⁽ᵏ⁺¹⁾ - β_k p⁽ᵏ⁾` (4.41) — with the book's *minus* sign, so that its `β_k` is the
negative of the backbone's `CG.beta`. The state type is the backbone's record `CG.State`; the step
is identified with `CG.step` along the iteration by `cg_eq_CG`. -/
noncomputable def cgStep (s : CG.State (EuclideanSpace ℝ (Fin n))) :
    CG.State (EuclideanSpace ℝ (Fin n)) :=
  let α := cgAlphaStep A s
  let r' := s.r - α • toEuclideanLin A s.p
  let β := inner ℝ (toEuclideanLin A s.p) r' / inner ℝ (toEuclideanLin A s.p) s.p
  { x := s.x + α • s.p, r := r', p := r' - β • s.p }

/-- The coefficient `β_k = (A p⁽ᵏ⁾)ᵀ r⁽ᵏ⁺¹⁾ / (A p⁽ᵏ⁾)ᵀ p⁽ᵏ⁾` of (4.41), computed on a state. -/
noncomputable def cgBetaStep (s : CG.State (EuclideanSpace ℝ (Fin n))) : ℝ :=
  inner ℝ (toEuclideanLin A s.p) (cgStep A s).r / inner ℝ (toEuclideanLin A s.p) s.p

/-- **The conjugate gradient method** started at `x⁽⁰⁾` with `r⁽⁰⁾ = b - A x⁽⁰⁾` and
`p⁽⁰⁾ = r⁽⁰⁾`: the state `(x⁽ᵏ⁾, r⁽ᵏ⁾, p⁽ᵏ⁾)` after `k` steps of `cgStep`. -/
noncomputable def cg (x₀ : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    CG.State (EuclideanSpace ℝ (Fin n)) :=
  (cgStep A)^[k] { x := x₀, r := b - toEuclideanLin A x₀, p := b - toEuclideanLin A x₀ }

variable (x₀ : EuclideanSpace ℝ (Fin n))

/-- The `k`-th conjugate gradient iterate `x⁽ᵏ⁾`. -/
noncomputable def cgX (k : ℕ) : EuclideanSpace ℝ (Fin n) := (cg A b x₀ k).x

/-- The `k`-th conjugate gradient residual `r⁽ᵏ⁾`. -/
noncomputable def cgR (k : ℕ) : EuclideanSpace ℝ (Fin n) := (cg A b x₀ k).r

/-- The `k`-th conjugate gradient descent direction `p⁽ᵏ⁾`. -/
noncomputable def cgP (k : ℕ) : EuclideanSpace ℝ (Fin n) := (cg A b x₀ k).p

/-- The step length `α_k` of (4.39) at step `k`. -/
noncomputable def cgAlpha (k : ℕ) : ℝ := cgAlphaStep A (cg A b x₀ k)

/-- The coefficient `β_k` of (4.41) at step `k`, with the book's sign. -/
noncomputable def cgBeta (k : ℕ) : ℝ := cgBetaStep A (cg A b x₀ k)

theorem cg_succ (k : ℕ) : cg A b x₀ (k + 1) = cgStep A (cg A b x₀ k) :=
  Function.iterate_succ_apply' _ _ _

@[simp] theorem cgX_zero : cgX A b x₀ 0 = x₀ := rfl

@[simp] theorem cgR_zero : cgR A b x₀ 0 = b - toEuclideanLin A x₀ := rfl

/-- `p⁽⁰⁾ = r⁽⁰⁾`. -/
@[simp] theorem cgP_zero : cgP A b x₀ 0 = cgR A b x₀ 0 := rfl

/-- (4.39): `α_k = p⁽ᵏ⁾ᵀ r⁽ᵏ⁾ / p⁽ᵏ⁾ᵀ A p⁽ᵏ⁾`. -/
theorem cgAlpha_eq (k : ℕ) : cgAlpha A b x₀ k =
    inner ℝ (cgP A b x₀ k) (cgR A b x₀ k) /
      inner ℝ (cgP A b x₀ k) (toEuclideanLin A (cgP A b x₀ k)) :=
  rfl

/-- `x⁽ᵏ⁺¹⁾ = x⁽ᵏ⁾ + α_k p⁽ᵏ⁾`. -/
theorem cgX_succ (k : ℕ) :
    cgX A b x₀ (k + 1) = cgX A b x₀ k + cgAlpha A b x₀ k • cgP A b x₀ k := by
  rw [cgX, cg_succ]
  rfl

/-- `r⁽ᵏ⁺¹⁾ = r⁽ᵏ⁾ - α_k A p⁽ᵏ⁾`. -/
theorem cgR_succ (k : ℕ) :
    cgR A b x₀ (k + 1) = cgR A b x₀ k - cgAlpha A b x₀ k • toEuclideanLin A (cgP A b x₀ k) := by
  rw [cgR, cg_succ]
  rfl

/-- `β_k = (A p⁽ᵏ⁾)ᵀ r⁽ᵏ⁺¹⁾ / (A p⁽ᵏ⁾)ᵀ p⁽ᵏ⁾`. -/
theorem cgBeta_eq (k : ℕ) : cgBeta A b x₀ k =
    inner ℝ (toEuclideanLin A (cgP A b x₀ k)) (cgR A b x₀ (k + 1)) /
      inner ℝ (toEuclideanLin A (cgP A b x₀ k)) (cgP A b x₀ k) := by
  rw [cgBeta, cgBetaStep, cgR, cg_succ]
  rfl

/-- (4.41): `p⁽ᵏ⁺¹⁾ = r⁽ᵏ⁺¹⁾ - β_k p⁽ᵏ⁾`. -/
theorem cgP_succ (k : ℕ) :
    cgP A b x₀ (k + 1) = cgR A b x₀ (k + 1) - cgBeta A b x₀ k • cgP A b x₀ k := by
  rw [cgP, cg_succ, cgBeta_eq, cgR, cg_succ]
  rfl

variable {A b x₀}

/-- A positive definite matrix acts as a symmetric coercive operator on `EuclideanSpace`. -/
theorem posDef_isSymmetricCoercive_toEuclideanLin (hA : A.PosDef) :
    (toEuclideanLin A).IsSymmetricCoercive :=
  (posDef_iff_isSymmetricCoercive A).1 hA

/-- On the backbone's iterates, the book's `α_k` of (4.39) is `CG.alpha`, because
`p⁽ᵏ⁾ᵀ r⁽ᵏ⁾ = ‖r⁽ᵏ⁾‖²` (`CG.inner_residual_direction_eq`). -/
private theorem cgAlphaStep_iterate (hA : A.PosDef) (k : ℕ) :
    cgAlphaStep A (CG.iterate (toEuclideanLin A) b x₀ k) =
      CG.alpha (toEuclideanLin A) (CG.iterate (toEuclideanLin A) b x₀ k) := by
  have h := CG.inner_residual_direction_eq b x₀ (posDef_isSymmetricCoercive_toEuclideanLin hA)
    (le_refl k)
  rw [RCLike.ofReal_real_eq_id, id_eq] at h
  rw [cgAlphaStep, CG.alpha, real_inner_comm (CG.iterate (toEuclideanLin A) b x₀ k).r, h,
    real_inner_self_eq_norm_sq,
    real_inner_comm (toEuclideanLin A (CG.iterate (toEuclideanLin A) b x₀ k).p)]

/-- On the backbone's iterates, the book's step produces the backbone's residual. -/
private theorem cgStep_r_iterate (hA : A.PosDef) (k : ℕ) :
    (cgStep A (CG.iterate (toEuclideanLin A) b x₀ k)).r =
      (CG.iterate (toEuclideanLin A) b x₀ (k + 1)).r := by
  rw [CG.iterate_succ_r, cgStep, cgAlphaStep_iterate hA]

/-- On the backbone's iterates, the book's `β_k` is the negative of `CG.beta`: from
`α_k A p⁽ᵏ⁾ = r⁽ᵏ⁾ - r⁽ᵏ⁺¹⁾`, `(A p⁽ᵏ⁾)ᵀ r⁽ᵏ⁺¹⁾ = -‖r⁽ᵏ⁺¹⁾‖²/α_k` and
`(A p⁽ᵏ⁾)ᵀ p⁽ᵏ⁾ = ‖r⁽ᵏ⁾‖²/α_k` (the solution of Exercise 13). -/
private theorem cgBetaStep_iterate (hA : A.PosDef) (k : ℕ) :
    cgBetaStep A (CG.iterate (toEuclideanLin A) b x₀ k) =
      -CG.beta (toEuclideanLin A) (CG.iterate (toEuclideanLin A) b x₀ k) := by
  have hA' := posDef_isSymmetricCoercive_toEuclideanLin hA
  rw [cgBetaStep, cgStep_r_iterate hA, CG.beta_iterate]
  rcases eq_or_ne (CG.iterate (toEuclideanLin A) b x₀ k).r 0 with hr | hr
  · have hp : (CG.iterate (toEuclideanLin A) b x₀ k).p = 0 :=
      CG.direction_eq_zero_of_residual_eq_zero _ b x₀ hr
    have hr' : (CG.iterate (toEuclideanLin A) b x₀ (k + 1)).r = 0 :=
      CG.residual_succ_eq_zero_of_eq_zero _ b x₀ hr
    rw [hp, hr, hr']
    simp
  · have hα := CG.alpha_smul_apply_direction (toEuclideanLin A) b x₀ k
    have hpos := CG.re_inner_apply_direction_pos b x₀ hA' hr
    rw [RCLike.re_to_real] at hpos
    have hrpos : 0 < inner ℝ (CG.iterate (toEuclideanLin A) b x₀ k).r
        (CG.iterate (toEuclideanLin A) b x₀ k).r := real_inner_self_pos.mpr hr
    have hαne : CG.alpha (toEuclideanLin A) (CG.iterate (toEuclideanLin A) b x₀ k) ≠ 0 := by
      rw [CG.alpha]
      exact div_ne_zero hrpos.ne' hpos.ne'
    have hAp : toEuclideanLin A (CG.iterate (toEuclideanLin A) b x₀ k).p =
        (CG.alpha (toEuclideanLin A) (CG.iterate (toEuclideanLin A) b x₀ k))⁻¹ •
          ((CG.iterate (toEuclideanLin A) b x₀ k).r -
            (CG.iterate (toEuclideanLin A) b x₀ (k + 1)).r) := by
      rw [← hα, smul_smul, inv_mul_cancel₀ hαne, one_smul]
    have h1 : inner ℝ (CG.iterate (toEuclideanLin A) b x₀ k).r
        (CG.iterate (toEuclideanLin A) b x₀ (k + 1)).r = 0 :=
      CG.inner_residual_eq_zero b x₀ hA' (Nat.ne_of_lt (Nat.lt_succ_self k))
    have h2 : inner ℝ (CG.iterate (toEuclideanLin A) b x₀ (k + 1)).r
        (CG.iterate (toEuclideanLin A) b x₀ k).p = 0 :=
      CG.inner_residual_direction_eq_zero b x₀ hA' (Nat.lt_succ_self k)
    have h3 : inner ℝ (CG.iterate (toEuclideanLin A) b x₀ k).r
        (CG.iterate (toEuclideanLin A) b x₀ k).p =
          ‖(CG.iterate (toEuclideanLin A) b x₀ k).r‖ ^ 2 := by
      have := CG.inner_residual_direction_eq b x₀ hA' (le_refl k)
      rwa [RCLike.ofReal_real_eq_id, id_eq] at this
    rw [hAp, inner_smul_left, inner_smul_left, inner_sub_left, inner_sub_left, h1, h2, h3,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, RCLike.conj_to_real]
    have hn : ‖(CG.iterate (toEuclideanLin A) b x₀ k).r‖ ≠ 0 := norm_ne_zero_iff.mpr hr
    field_simp
    ring

/-- On the backbone's iterates, the book's step is the backbone's step. -/
private theorem cgStep_iterate (hA : A.PosDef) (k : ℕ) :
    cgStep A (CG.iterate (toEuclideanLin A) b x₀ k) =
      CG.step (toEuclideanLin A) (CG.iterate (toEuclideanLin A) b x₀ k) := by
  have hβ := cgBetaStep_iterate hA (b := b) (x₀ := x₀) k
  have hr := cgStep_r_iterate hA (b := b) (x₀ := x₀) k
  rw [cgBetaStep] at hβ
  set s := CG.iterate (toEuclideanLin A) b x₀ k with hs
  refine CG.State.ext ?_ ?_ ?_
  · rw [CG.step_x, cgStep, cgAlphaStep_iterate hA]
  · rw [CG.step_r, cgStep, cgAlphaStep_iterate hA]
  · rw [CG.step_p, ← CG.iterate_succ, ← hr]
    change (cgStep A s).r - (inner ℝ (toEuclideanLin A s.p) (cgStep A s).r /
      inner ℝ (toEuclideanLin A s.p) s.p) • s.p = _
    rw [hβ, neg_smul, sub_neg_eq_add]

/-- **The bridge to the backbone.** For `A` symmetric positive definite, the conjugate gradient
method of §4.3.4 is the backbone recurrence `CG.iterate`: the states coincide, the book's `α_k` is
`CG.alpha` (because `p⁽ᵏ⁾ᵀ r⁽ᵏ⁾ = ‖r⁽ᵏ⁾‖²`, `CG.inner_residual_direction_eq`) and the book's
`β_k` is `-CG.beta` (Exercise 13, `equation_4_45`). Every property of the method below is read
off this identification. -/
theorem cg_eq_CG (hA : A.PosDef) (k : ℕ) :
    cg A b x₀ k = CG.iterate (toEuclideanLin A) b x₀ k ∧
      cgAlpha A b x₀ k = CG.alpha (toEuclideanLin A) (CG.iterate (toEuclideanLin A) b x₀ k) ∧
      cgBeta A b x₀ k = -CG.beta (toEuclideanLin A) (CG.iterate (toEuclideanLin A) b x₀ k) := by
  have hcg : cg A b x₀ k = CG.iterate (toEuclideanLin A) b x₀ k := by
    induction k with
    | zero => rfl
    | succ k ih => rw [cg_succ, ih, cgStep_iterate hA, CG.iterate_succ]
  exact ⟨hcg, by rw [cgAlpha, hcg, cgAlphaStep_iterate hA],
    by rw [cgBeta, hcg, cgBetaStep_iterate hA]⟩

/-- The book's iterate `x⁽ᵏ⁾` is the `x` component of the backbone's conjugate-gradient state,
by `cg_eq_CG`. -/
theorem cgX_eq_CG (hA : A.PosDef) (k : ℕ) :
    cgX A b x₀ k = (CG.iterate (toEuclideanLin A) b x₀ k).x := by
  rw [cgX, (cg_eq_CG hA k).1]

/-- The book's residual `r⁽ᵏ⁾` is the `r` component of the backbone's conjugate-gradient state,
by `cg_eq_CG`. -/
theorem cgR_eq_CG (hA : A.PosDef) (k : ℕ) :
    cgR A b x₀ k = (CG.iterate (toEuclideanLin A) b x₀ k).r := by
  rw [cgR, (cg_eq_CG hA k).1]

/-- The book's direction `p⁽ᵏ⁾` is the `p` component of the backbone's conjugate-gradient state,
by `cg_eq_CG`. -/
theorem cgP_eq_CG (hA : A.PosDef) (k : ℕ) :
    cgP A b x₀ k = (CG.iterate (toEuclideanLin A) b x₀ k).p := by
  rw [cgP, (cg_eq_CG hA k).1]

/-- The state's residual is the true residual `r⁽ᵏ⁾ = b - A x⁽ᵏ⁾`. -/
theorem cgR_eq_residual (hA : A.PosDef) (k : ℕ) :
    cgR A b x₀ k = b - toEuclideanLin A (cgX A b x₀ k) := by
  rw [cgR_eq_CG hA, cgX_eq_CG hA, CG.residual_eq]

/-- **(4.42).** The descent directions are `A`-conjugate: `(A p⁽ʲ⁾)ᵀ p⁽ᵏ⁺¹⁾ = 0` for
`j = 0, …, k`, and indeed `(A p⁽ⁱ⁾)ᵀ p⁽ʲ⁾ = 0` for all `i ≠ j` — the book's induction is the
backbone's `CG.inner_apply_direction_eq_zero`. -/
theorem equation_4_42 (hA : A.PosDef) :
    (∀ k, ∀ j ≤ k, inner ℝ (toEuclideanLin A (cgP A b x₀ j)) (cgP A b x₀ (k + 1)) = 0) ∧
      ∀ i j, i ≠ j → inner ℝ (toEuclideanLin A (cgP A b x₀ i)) (cgP A b x₀ j) = 0 := by
  have h : ∀ i j, i ≠ j → inner ℝ (toEuclideanLin A (cgP A b x₀ i)) (cgP A b x₀ j) = 0 := by
    intro i j hij
    rw [cgP_eq_CG hA, cgP_eq_CG hA]
    exact CG.inner_apply_direction_eq_zero b x₀ (posDef_isSymmetricCoercive_toEuclideanLin hA) hij
  exact ⟨fun k j hj => h j (k + 1) (by omega), h⟩

/-- **(4.43)–(4.44).** The residual `r⁽ᵏ⁾` is orthogonal to the earlier directions,
`p⁽ʲ⁾ᵀ r⁽ᵏ⁾ = 0` for `j < k` (backbone `CG.inner_residual_direction_eq_zero`), hence to the
space `V_k = span(p⁽⁰⁾, …, p⁽ᵏ⁻¹⁾)`, which is also `span(r⁽⁰⁾, …, r⁽ᵏ⁻¹⁾)` and is the Krylov
space `K_k(A; r⁽⁰⁾)` of §4.4 (`CG.span_direction_eq`, `CG.span_residual_eq`); moreover the
residuals are mutually orthogonal (`CG.inner_residual_eq_zero`). -/
theorem equation_4_44 (hA : A.PosDef) :
    (∀ k j, j < k → inner ℝ (cgP A b x₀ j) (cgR A b x₀ k) = 0) ∧
      (∀ k, Submodule.span ℝ (Set.range fun i : Fin k => cgP A b x₀ i) =
        Krylov.subspace (toEuclideanLin A) (b - toEuclideanLin A x₀) k) ∧
      (∀ k, Submodule.span ℝ (Set.range fun i : Fin k => cgR A b x₀ i) =
        Krylov.subspace (toEuclideanLin A) (b - toEuclideanLin A x₀) k) ∧
      ∀ i j, i ≠ j → inner ℝ (cgR A b x₀ i) (cgR A b x₀ j) = 0 := by
  have hA' := (posDef_isSymmetricCoercive_toEuclideanLin hA)
  simp only [cgP_eq_CG hA, cgR_eq_CG hA]
  exact ⟨fun k j hj => by
      rw [real_inner_comm]; exact CG.inner_residual_direction_eq_zero b x₀ hA' hj,
    CG.span_direction_eq b x₀ hA', CG.span_residual_eq b x₀ hA',
    fun i j hij => CG.inner_residual_eq_zero b x₀ hA' hij⟩

/-- **(4.45) and Exercise 13.** The two parameters may alternatively be expressed as
`α_k = ‖r⁽ᵏ⁾‖² / p⁽ᵏ⁾ᵀ A p⁽ᵏ⁾` and `β_k = -‖r⁽ᵏ⁺¹⁾‖² / ‖r⁽ᵏ⁾‖²`. The sign of `β_k` is negative,
not positive as printed: with the update `p⁽ᵏ⁺¹⁾ = r⁽ᵏ⁺¹⁾ - β_k p⁽ᵏ⁾` of (4.41),
`(A p⁽ᵏ⁾)ᵀ r⁽ᵏ⁺¹⁾ = -‖r⁽ᵏ⁺¹⁾‖²/α_k` and `α_k (A p⁽ᵏ⁾)ᵀ p⁽ᵏ⁾ = ‖r⁽ᵏ⁾‖²` (the solution of Exercise 13
prints a minus sign in the latter, which compensates). Both identities hold at every step, a
vanishing residual making both sides `0`. -/
theorem equation_4_45 (hA : A.PosDef) (k : ℕ) :
    cgAlpha A b x₀ k =
        ‖cgR A b x₀ k‖ ^ 2 / inner ℝ (cgP A b x₀ k) (toEuclideanLin A (cgP A b x₀ k)) ∧
      cgBeta A b x₀ k = -(‖cgR A b x₀ (k + 1)‖ ^ 2 / ‖cgR A b x₀ k‖ ^ 2) := by
  obtain ⟨-, hα, hβ⟩ := cg_eq_CG (b := b) (x₀ := x₀) hA k
  constructor
  · rw [hα, CG.alpha, cgR_eq_CG hA, cgP_eq_CG hA, real_inner_self_eq_norm_sq, real_inner_comm]
  · rw [hβ, CG.beta_iterate, cgR_eq_CG hA, cgR_eq_CG hA, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq]

/-- `α_k ≠ 0` while `r⁽ᵏ⁾ ≠ 0`: `α_k = ‖r⁽ᵏ⁾‖²/p⁽ᵏ⁾ᵀ A p⁽ᵏ⁾` with `p⁽ᵏ⁾ᵀ A p⁽ᵏ⁾ > 0`
(`CG.re_inner_apply_direction_pos`). -/
theorem cgAlpha_ne_zero (hA : A.PosDef) {k : ℕ} (hr : cgR A b x₀ k ≠ 0) :
    cgAlpha A b x₀ k ≠ 0 := by
  rw [(equation_4_45 hA k).1]
  have hpos := CG.re_inner_apply_direction_pos b x₀ (posDef_isSymmetricCoercive_toEuclideanLin hA)
    (cgR_eq_CG hA k ▸ hr)
  rw [RCLike.re_to_real, ← cgP_eq_CG hA, real_inner_comm] at hpos
  exact div_ne_zero (pow_ne_zero 2 (norm_ne_zero_iff.mpr hr)) hpos.ne'

/-- A vanishing residual stays zero: `r⁽ᵏ⁺¹⁾ = 0` as soon as `r⁽ᵏ⁾ = 0`
(`CG.residual_succ_eq_zero_of_eq_zero`). -/
theorem cgR_succ_eq_zero_of_eq_zero (hA : A.PosDef) {k : ℕ} (hr : cgR A b x₀ k = 0) :
    cgR A b x₀ (k + 1) = 0 := by
  rw [cgR_eq_CG hA] at hr ⊢
  exact CG.residual_succ_eq_zero_of_eq_zero _ b x₀ hr

/-- **(4.46) and Exercise 14, the three-term recurrence of the residuals.** Eliminating the
descent directions from `r⁽ᵏ⁺¹⁾ = r⁽ᵏ⁾ - α_k A p⁽ᵏ⁾` — through `A p⁽ᵏ⁾ = (r⁽ᵏ⁾ - r⁽ᵏ⁺¹⁾)/α_k`
and `p⁽ᵏ⁾ = r⁽ᵏ⁾ - β_{k-1} p⁽ᵏ⁻¹⁾`, as the solution of Exercise 14 does — gives, for `k ≥ 1`
(written `k + 1`) while `r⁽ᵏ⁾ ≠ 0`,
`A r⁽ᵏ⁾ = -(1/α_k) r⁽ᵏ⁺¹⁾ + (1/α_k - β_{k-1}/α_{k-1}) r⁽ᵏ⁾ + (β_{k-1}/α_{k-1}) r⁽ᵏ⁻¹⁾`. The last
coefficient is `β_{k-1}/α_{k-1}`, not the printed `β_k/α_{k-1}`. -/
theorem equation_4_46 (hA : A.PosDef) {k : ℕ} (hr : cgR A b x₀ (k + 1) ≠ 0) :
    toEuclideanLin A (cgR A b x₀ (k + 1)) =
      -(1 / cgAlpha A b x₀ (k + 1)) • cgR A b x₀ (k + 2) +
        (1 / cgAlpha A b x₀ (k + 1) - cgBeta A b x₀ k / cgAlpha A b x₀ k) • cgR A b x₀ (k + 1) +
        (cgBeta A b x₀ k / cgAlpha A b x₀ k) • cgR A b x₀ k := by
  have hr0 : cgR A b x₀ k ≠ 0 := fun h => hr (cgR_succ_eq_zero_of_eq_zero hA h)
  have hα0 := cgAlpha_ne_zero hA hr0
  have hα1 := cgAlpha_ne_zero hA hr
  have hAp : ∀ j, cgAlpha A b x₀ j ≠ 0 → toEuclideanLin A (cgP A b x₀ j) =
      (cgAlpha A b x₀ j)⁻¹ • (cgR A b x₀ j - cgR A b x₀ (j + 1)) := by
    intro j hj
    rw [cgR_succ, sub_sub_cancel, smul_smul, inv_mul_cancel₀ hj, one_smul]
  have hp : cgP A b x₀ (k + 1) = cgR A b x₀ (k + 1) - cgBeta A b x₀ k • cgP A b x₀ k :=
    cgP_succ A b x₀ k
  have hApk := hAp k hα0
  have hApk1 := hAp (k + 1) hα1
  rw [hp, map_sub, map_smul, hApk] at hApk1
  have h : toEuclideanLin A (cgR A b x₀ (k + 1)) =
      (cgAlpha A b x₀ (k + 1))⁻¹ • (cgR A b x₀ (k + 1) - cgR A b x₀ (k + 1 + 1)) +
        cgBeta A b x₀ k • ((cgAlpha A b x₀ k)⁻¹ • (cgR A b x₀ k - cgR A b x₀ (k + 1))) := by
    rw [← hApk1]
    abel
  rw [h]
  module

/-- **Theorem 4.11.** Let `A` be symmetric positive definite. Any method employing conjugate
directions — `x⁽ᵏ⁺¹⁾ = x⁽ᵏ⁾ + α_k p⁽ᵏ⁾` with the step (4.39) along mutually `A`-conjugate
directions `p⁽ᵏ⁾`, the backbone's `ConjugateDirection.iterate` — terminates after at most `n`
steps, yielding the exact solution. The book's proof is the expanding subspace theorem: `x⁽ᵏ⁾` is
optimal with respect to `p⁽⁰⁾, …, p⁽ᵏ⁻¹⁾`, i.e. the Galerkin iterate over their span
(`ConjugateDirection.isGalerkin_iterate`), so `r⁽ⁿ⁾ ⟂ ℝⁿ` and `x⁽ⁿ⁾ = x`
(`ConjugateDirection.iterate_eq_of_finrank_le`, with `dim ℝⁿ = n`). The directions used must be
nonzero. -/
theorem theorem_4_11 (hA : A.PosDef) {p : ℕ → EuclideanSpace ℝ (Fin n)}
    (hp : ConjugateDirection.IsConjugateFamily (toEuclideanLin A) p) (h0 : ∀ i < n, p i ≠ 0)
    {x : EuclideanSpace ℝ (Fin n)} (hx : toEuclideanLin A x = b) :
    (∀ k, IsGalerkin (toEuclideanLin A) b x₀ (Submodule.span ℝ (Set.range fun i : Fin k => p i))
        (ConjugateDirection.iterate (toEuclideanLin A) b p x₀ k)) ∧
      ∀ k, n ≤ k → ConjugateDirection.iterate (toEuclideanLin A) b p x₀ k = x := by
  have hA' := (posDef_isSymmetricCoercive_toEuclideanLin hA).isCoercive
  refine ⟨fun k => ConjugateDirection.isGalerkin_iterate b x₀ hA' hp k, fun k hk => ?_⟩
  refine ConjugateDirection.iterate_eq_of_finrank_le b x₀ hA' hp ?_ hx ?_
  · rwa [finrank_euclideanSpace_fin]
  · rwa [finrank_euclideanSpace_fin]

/-- **Theorem 4.12, finite termination.** For `A` symmetric positive definite the conjugate
gradient method converges after at most `n` steps: `r⁽ᵏ⁾ = 0` as soon as `k` reaches the grade of
`r⁽⁰⁾` (backbone `CG.residual_eq_zero_of_grade_le`), which is at most `n`
(`Krylov.grade_le_finrank`), and then `x⁽ᵏ⁾ = x`. The book derives it from Theorem 4.11, of
which CG is an instance (`CG.iterate_x_eq_conjugateDirection_iterate`). -/
theorem theorem_4_12_terminates (hA : A.PosDef) {x : EuclideanSpace ℝ (Fin n)}
    (hx : toEuclideanLin A x = b) :
    (∀ k, Krylov.grade (toEuclideanLin A) (b - toEuclideanLin A x₀) ≤ k → cgR A b x₀ k = 0) ∧
      Krylov.grade (toEuclideanLin A) (b - toEuclideanLin A x₀) ≤ n ∧
      ∀ k, n ≤ k → cgX A b x₀ k = x := by
  have hA' := (posDef_isSymmetricCoercive_toEuclideanLin hA)
  have hr : ∀ k, Krylov.grade (toEuclideanLin A) (b - toEuclideanLin A x₀) ≤ k →
      cgR A b x₀ k = 0 := fun k hk => by
    rw [cgR_eq_CG hA]
    exact CG.residual_eq_zero_of_grade_le b x₀ hA' hk
  have hgrade : Krylov.grade (toEuclideanLin A) (b - toEuclideanLin A x₀) ≤ n := by
    have := Krylov.grade_le_finrank (toEuclideanLin A) (b - toEuclideanLin A x₀)
    rwa [finrank_euclideanSpace_fin] at this
  refine ⟨hr, hgrade, fun k hk => ?_⟩
  have h := hr k (hgrade.trans hk)
  rw [cgR_eq_residual hA, sub_eq_zero] at h
  exact hA'.isCoercive.injective (h.symm.trans hx.symm)

/-- **Theorem 4.12, the orthogonality clause, read correctly.** The error `e⁽ᵏ⁾ = x⁽ᵏ⁾ - x` is
`A`-orthogonal — not, as printed, orthogonal — to `p⁽ʲ⁾` for `j < k`:
`(A e⁽ᵏ⁾)ᵀ p⁽ʲ⁾ = -r⁽ᵏ⁾ᵀ p⁽ʲ⁾ = 0` by (4.44). -/
theorem theorem_4_12_orthogonal (hA : A.PosDef) {x : EuclideanSpace ℝ (Fin n)}
    (hx : toEuclideanLin A x = b) {k j : ℕ} (hj : j < k) :
    inner ℝ (toEuclideanLin A (cgX A b x₀ k - x)) (cgP A b x₀ j) = 0 := by
  have h := (equation_4_44 (b := b) (x₀ := x₀) hA).1 k j hj
  rw [map_sub, hx, ← neg_sub, ← cgR_eq_residual hA, inner_neg_left, real_inner_comm, h, neg_zero]

/-- **Theorem 4.12, (4.47).** For `A` symmetric positive definite with `K₂(A) = λ_max/λ_min` and
`c = (√K₂(A) - 1)/(√K₂(A) + 1)`, the conjugate gradient error satisfies
`‖e⁽ᵏ⁾‖_A ≤ (2 cᵏ / (1 + c²ᵏ)) ‖e⁽⁰⁾‖_A` for every `k`. The `k`-th iterate is the Galerkin iterate
over the Krylov space (`CG.isGalerkinIterate`), which minimizes the `A`-norm of the error among
all `q(A) e⁽⁰⁾` with `q ∈ P_k^{0,1}` ((4.49), `equation_4_49`); Property 4.6 bounds that minimum
by `1/T_k((λ_1 + λ_n)/(λ_1 - λ_n))` (backbone
`Krylov.IsGalerkinIterate.energyNorm_error_le_div_eval_T`), and
`1/T_k((K₂ + 1)/(K₂ - 1)) = 2cᵏ/(1 + c²ᵏ)`
(`Polynomial.Chebyshev.one_div_eval_T_eq_two_mul_pow_div`). When `λ_min = λ_max` (`K₂(A) = 1`,
`c = 0`) the printed bound is `1` at `k = 0` and `0` for `k ≥ 1`, and holds because `A` is then a
multiple of the identity and the first step is exact
(`Krylov.IsGalerkinIterate.energyNorm_error_le`). -/
theorem theorem_4_12_bound [NeZero n] (hA : A.PosDef) {x : EuclideanSpace ℝ (Fin n)}
    (hx : toEuclideanLin A x = b) (k : ℕ) :
    energyNorm (toEuclideanLin A) (x - cgX A b x₀ k) ≤
      2 * ((√(κ A) - 1) / (√(κ A) + 1)) ^ k / (1 + ((√(κ A) - 1) / (√(κ A) + 1)) ^ (2 * k)) *
        energyNorm (toEuclideanLin A) (x - x₀) := by
  have hA' := (posDef_isSymmetricCoercive_toEuclideanLin hA)
  obtain ⟨lmin, lmax, hsub, hmin, hmax, hIcc⟩ := exists_extreme_eigenvalues hA.1
  have hpos : 0 < lmin := posDef_pos_of_mem_spectrum hA hmin
  have hle : lmin ≤ lmax := (hsub hmin).2
  have hB := hA.1.isSymmetricBoundedBy_toEuclideanLin hIcc
  have hκ : κ A = lmax / lmin := condNumber_eq_div_of_posDef hA hsub hmin hmax
  have hgal := CG.isGalerkinIterate b x₀ hA' k
  rw [cgX_eq_CG hA]
  rcases hle.lt_or_eq with hlt | heq
  · have hκ1 : 1 < κ A := by
      rw [hκ, lt_div_iff₀ hpos, one_mul]
      exact hlt
    have h := hgal.energyNorm_error_le_div_eval_T hpos hlt hB hx
    have hT := Polynomial.Chebyshev.one_div_eval_T_eq_two_mul_pow_div hκ1 k
    rw [show (κ A + 1) / (κ A - 1) = (lmax + lmin) / (lmax - lmin) by
      rw [hκ]; field_simp] at hT
    rw [div_eq_mul_one_div, hT, mul_comm] at h
    exact h
  · subst heq
    have hκ1 : κ A = 1 := by rw [hκ, div_self hpos.ne']
    rw [hκ1, Real.sqrt_one, sub_self, zero_div]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp only [pow_zero, mul_one, mul_zero, CG.iterate_zero, CG.init_x]
      norm_num
    · have h := hgal.energyNorm_error_le hpos le_rfl hB hx
      rw [div_self hpos.ne', Real.sqrt_one, sub_self, zero_div, zero_pow hk.ne', mul_zero,
        zero_mul] at h
      rw [zero_pow hk.ne', mul_zero, zero_div, zero_mul]
      exact h

/-- **(4.48)–(4.49).** For `A` symmetric positive definite and `x` the solution, the `A`-norm of
the error at step `k + 1` is the minimum of `‖q(A) e⁽⁰⁾‖_A` over the polynomials `q` of degree
`≤ k + 1` with `q(0) = 1` (the book takes `x⁽⁰⁾ = 0`, where `e⁽⁰⁾ = x`): the conjugate gradient
iterate is the Galerkin iterate over the Krylov space (`CG.isGalerkinIterate`) and
`Krylov.IsGalerkinIterate.energyNorm_error_eq_iInf` is the polynomial characterization. -/
theorem equation_4_49 (hA : A.PosDef) {x : EuclideanSpace ℝ (Fin n)}
    (hx : toEuclideanLin A x = b) (k : ℕ) :
    energyNorm (toEuclideanLin A) (x - cgX A b x₀ (k + 1)) =
      ⨅ q : {q : Polynomial ℝ // q.degree ≤ (k + 1 : ℕ) ∧ q.eval 0 = 1},
        energyNorm (toEuclideanLin A) (Polynomial.aeval (toEuclideanLin A) q.1 (x - x₀)) := by
  rw [cgX_eq_CG hA]
  exact (CG.isGalerkinIterate b x₀ (posDef_isSymmetricCoercive_toEuclideanLin hA)
    (k + 1)).energyNorm_error_eq_iInf (posDef_isSymmetricCoercive_toEuclideanLin hA) hx

end ConjugateGradient

/-! ### Property 4.6 and Exercise 12 -/

section Chebyshev

open Polynomial

/-- **Property 4.6, the value and the minimizer.** For `0 < λ_n < λ_1`, the problem of minimizing
`max_{λ_n ≤ z ≤ λ_1} |q(z)|` over `P_{k+1}^{0,1}` — the polynomials of degree `≤ k + 1` with
`q(0) = 1` — has value `1/C_{k+1}`, `C_{k+1} = T_{k+1}((λ_1 + λ_n)/(λ_1 - λ_n))`, and the value is
attained by `p_{k+1}(ξ) = T_{k+1}((λ_1 + λ_n - 2ξ)/(λ_1 - λ_n))/C_{k+1}` (backbone
`Polynomial.Chebyshev.shifted (k + 1) λ_n λ_1 0`, whose evaluation is that formula): backbone
`Polynomial.Chebyshev.one_div_eval_T_le_sSup_abs_eval_of_eval_zero` and
`Polynomial.Chebyshev.sSup_abs_eval_shifted`. -/
theorem property_4_6 {lmin lmax : ℝ} (hpos : 0 < lmin) (hlt : lmin < lmax) (k : ℕ) :
    (∀ q : ℝ[X], q.degree ≤ (k + 1 : ℕ) → q.eval 0 = 1 →
        1 / (Chebyshev.T ℝ (k + 1 : ℕ)).eval ((lmax + lmin) / (lmax - lmin)) ≤
          sSup ((fun t => |q.eval t|) '' Set.Icc lmin lmax)) ∧
      (Chebyshev.shifted (k + 1) lmin lmax 0).degree ≤ (k + 1 : ℕ) ∧
      (Chebyshev.shifted (k + 1) lmin lmax 0).eval 0 = 1 ∧
      (∀ ξ, (Chebyshev.shifted (k + 1) lmin lmax 0).eval ξ =
        (Chebyshev.T ℝ (k + 1 : ℕ)).eval ((lmax + lmin - 2 * ξ) / (lmax - lmin)) /
          (Chebyshev.T ℝ (k + 1 : ℕ)).eval ((lmax + lmin) / (lmax - lmin))) ∧
      sSup ((fun t => |(Chebyshev.shifted (k + 1) lmin lmax 0).eval t|) '' Set.Icc lmin lmax) =
        1 / (Chebyshev.T ℝ (k + 1 : ℕ)).eval ((lmax + lmin) / (lmax - lmin)) := by
  have hγ : (0 : ℝ) ∉ Set.Icc lmin lmax := fun h => absurd h.1 (not_le.mpr hpos)
  have hu : 1 ≤ (lmax + lmin) / (lmax - lmin) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  refine ⟨fun q hq hq0 =>
      Chebyshev.one_div_eval_T_le_sSup_abs_eval_of_eval_zero (k + 1) hpos hlt q hq hq0,
    Chebyshev.shifted_degree_le _ _ _ _, Chebyshev.shifted_eval_self _ hlt hγ, fun ξ => ?_, ?_⟩
  · have hne : lmax - lmin ≠ 0 := by linarith
    have harg : (lmax + lmin) / (lmax - lmin) - 2 / (lmax - lmin) * ξ =
        (lmax + lmin - 2 * ξ) / (lmax - lmin) := by
      field_simp
    simp only [Chebyshev.shifted, eval_mul, eval_C, eval_comp, eval_sub, eval_X, mul_zero,
      sub_zero, harg]
    ring
  · rw [Chebyshev.sSup_abs_eval_shifted _ hlt hγ, mul_zero, sub_zero,
      abs_of_nonneg (zero_le_one.trans (Chebyshev.one_le_eval_T hu _))]

/-- **Property 4.6, uniqueness.** The minimizer is unique: a polynomial of degree `≤ k + 1` with
`q(0) = 1` whose maximum modulus on `[λ_n, λ_1]` is `1/C_{k+1}` is `p_{k+1}` (backbone
`Polynomial.Chebyshev.eq_shifted_of_sSup_abs_eval_eq`; the book states the property without
proof). -/
theorem property_4_6_unique {lmin lmax : ℝ} (hpos : 0 < lmin) (hlt : lmin < lmax) (k : ℕ)
    {q : ℝ[X]} (hq : q.degree ≤ (k + 1 : ℕ)) (hq0 : q.eval 0 = 1)
    (hsup : sSup ((fun t => |q.eval t|) '' Set.Icc lmin lmax) =
      1 / (Chebyshev.T ℝ (k + 1 : ℕ)).eval ((lmax + lmin) / (lmax - lmin))) :
    q = Chebyshev.shifted (k + 1) lmin lmax 0 :=
  Chebyshev.eq_shifted_of_sSup_abs_eval_eq (by omega) hpos hlt (natDegree_le_iff_degree_le.mpr hq)
    hq0 hsup

end Chebyshev


/-! ### Exercise 12 -/

section Exercise

/-- The gradient step on coordinates: for `b, x : Fin n → ℝ`, with `r = b - A x`,
`gradientStep A (toLp 2 b) (toLp 2 x) = toLp 2 (x + (r ⬝ᵥ r / r ⬝ᵥ (A r)) • r)`. -/
theorem gradientStep_toLp (A : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) :
    gradientStep A (toLp 2 b) (toLp 2 x) =
      toLp 2 (x + ((b - A *ᵥ x) ⬝ᵥ (b - A *ᵥ x) / ((b - A *ᵥ x) ⬝ᵥ (A *ᵥ (b - A *ᵥ x)))) •
        (b - A *ᵥ x)) := by
  simp only [gradientStep, toEuclideanLin_toLp, ← toLp_sub, EuclideanSpace.inner_toLp_toLp,
    star_trivial, ← toLp_smul, ← toLp_add]
  rw [dotProduct_comm (A *ᵥ (b - A *ᵥ x))]

/-- The matrix `diag(1, 3)` of Exercise 12 is symmetric positive definite. -/
private theorem posDef_diag_one_three : (!![1, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  have h : (!![1, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℝ) = diagonal ![1, 3] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [h, posDef_diagonal_iff]
  intro i
  fin_cases i <;> norm_num

/-- **Exercise 12** (cited after Definition 4.4). The iterate `x⁽ᵏ⁺¹⁾` of the gradient method is
optimal with respect to `r⁽ᵏ⁾`, but `x⁽ᵏ⁺²⁾` in general is not: for `A = diag(1, 3)`, `b = 0` and
`x⁽⁰⁾ = (1, 1)`, one has `r⁽⁰⁾ = -(1, 3)`, `x⁽¹⁾ = (9/14, -1/14)`, `x⁽²⁾ = (3/28, 3/28)`,
`r⁽²⁾ = -(3/28, 9/28)` and `r⁽²⁾ᵀ r⁽⁰⁾ = 30/28 ≠ 0`, so `x⁽²⁾` is not optimal with respect to
`r⁽⁰⁾` (`definition_4_4_iff`), while `r⁽¹⁾ᵀ r⁽⁰⁾ = 0`. -/
theorem exercise_4_12 :
    definition_4_4 (!![1, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℝ) 0
        (gradientStep !![1, 0; 0, 3] 0 (toLp 2 ![1, 1]))
        (0 - toEuclideanLin !![1, 0; 0, 3] (toLp 2 ![1, 1])) ∧
      ¬ definition_4_4 (!![1, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℝ) 0
        ((gradientStep !![1, 0; 0, 3] 0)^[2] (toLp 2 ![1, 1]))
        (0 - toEuclideanLin !![1, 0; 0, 3] (toLp 2 ![1, 1])) := by
  have h0 : (0 : EuclideanSpace ℝ (Fin 2)) = toLp 2 0 := rfl
  have hx₁ : gradientStep (!![1, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℝ) (toLp 2 0) (toLp 2 ![1, 1]) =
      toLp 2 ![9 / 14, -1 / 14] := by
    rw [gradientStep_toLp]
    congr 1
    ext i
    fin_cases i <;>
    · simp [dotProduct, Fin.sum_univ_two]
      norm_num
  have hx₂ : gradientStep (!![1, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℝ) (toLp 2 0)
      (toLp 2 ![9 / 14, -1 / 14]) = toLp 2 ![3 / 28, 3 / 28] := by
    rw [gradientStep_toLp]
    congr 1
    ext i
    fin_cases i <;>
    · simp [dotProduct, Fin.sum_univ_two]
      norm_num
  have hiter : (gradientStep (!![1, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℝ) (toLp 2 0))^[2]
      (toLp 2 ![1, 1]) = toLp 2 ![3 / 28, 3 / 28] := by
    rw [Function.iterate_succ_apply', Function.iterate_one, hx₁, hx₂]
  rw [h0, hx₁, hiter, (definition_4_4_iff posDef_diag_one_three _ _ ⊥ 0).1,
    (definition_4_4_iff posDef_diag_one_three _ _ ⊥ 0).1]
  simp only [toEuclideanLin_toLp, ← toLp_sub, EuclideanSpace.inner_toLp_toLp, star_trivial]
  constructor
  · simp [dotProduct, Fin.sum_univ_two]
    norm_num
  · simp [dotProduct, Fin.sum_univ_two]
    norm_num

end Exercise

/-! ### §4.3.5 The preconditioned conjugate gradient method -/

section PCG

variable (A P : Matrix (Fin n) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin n))

/-- **The preconditioned conjugate gradient iteration of §4.3.5**, one step on the state
`(x⁽ᵏ⁾, r⁽ᵏ⁾, p⁽ᵏ⁾)` in the book's letters: `α_k = p⁽ᵏ⁾ᵀ r⁽ᵏ⁾ / p⁽ᵏ⁾ᵀ A p⁽ᵏ⁾`,
`x⁽ᵏ⁺¹⁾ = x⁽ᵏ⁾ + α_k p⁽ᵏ⁾`, `r⁽ᵏ⁺¹⁾ = r⁽ᵏ⁾ - α_k A p⁽ᵏ⁾`, `P z⁽ᵏ⁺¹⁾ = r⁽ᵏ⁺¹⁾`,
`β_k = (A p⁽ᵏ⁾)ᵀ z⁽ᵏ⁺¹⁾ / (A p⁽ᵏ⁾)ᵀ p⁽ᵏ⁾` and `p⁽ᵏ⁺¹⁾ = z⁽ᵏ⁺¹⁾ - β_k p⁽ᵏ⁾`, the book's `β_k` again
being the negative of the backbone's `Krylov.PCG.beta`. The state type is the backbone's record
`Krylov.PCG.State`; the identification is `pcg_eq_PCG`. -/
noncomputable def pcgStep (s : Krylov.PCG.State (EuclideanSpace ℝ (Fin n))) :
    Krylov.PCG.State (EuclideanSpace ℝ (Fin n)) :=
  let α := inner ℝ s.p s.r / inner ℝ s.p (toEuclideanLin A s.p)
  let r' := s.r - α • toEuclideanLin A s.p
  let z' := toEuclideanLin P⁻¹ r'
  let β := inner ℝ (toEuclideanLin A s.p) z' / inner ℝ (toEuclideanLin A s.p) s.p
  { x := s.x + α • s.p, r := r', p := z' - β • s.p }

/-- **The preconditioned conjugate gradient method** started at `x⁽⁰⁾` with `r⁽⁰⁾ = b - A x⁽⁰⁾`,
`z⁽⁰⁾ = P⁻¹ r⁽⁰⁾` and `p⁽⁰⁾ = z⁽⁰⁾`: the state after `k` steps of `pcgStep`. -/
noncomputable def pcg (x₀ : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    Krylov.PCG.State (EuclideanSpace ℝ (Fin n)) :=
  (pcgStep A P)^[k]
    { x := x₀, r := b - toEuclideanLin A x₀, p := toEuclideanLin P⁻¹ (b - toEuclideanLin A x₀) }

variable (x₀ : EuclideanSpace ℝ (Fin n))

/-- The step length `α_k = p⁽ᵏ⁾ᵀ r⁽ᵏ⁾ / p⁽ᵏ⁾ᵀ A p⁽ᵏ⁾` of the preconditioned method at step `k`. -/
noncomputable def pcgAlpha (k : ℕ) : ℝ :=
  inner ℝ (pcg A P b x₀ k).p (pcg A P b x₀ k).r /
    inner ℝ (pcg A P b x₀ k).p (toEuclideanLin A (pcg A P b x₀ k).p)

/-- The coefficient `β_k = (A p⁽ᵏ⁾)ᵀ z⁽ᵏ⁺¹⁾ / (A p⁽ᵏ⁾)ᵀ p⁽ᵏ⁾` of the preconditioned method at step
`k`, with `z⁽ᵏ⁺¹⁾ = P⁻¹ r⁽ᵏ⁺¹⁾`. -/
noncomputable def pcgBeta (k : ℕ) : ℝ :=
  inner ℝ (toEuclideanLin A (pcg A P b x₀ k).p) (toEuclideanLin P⁻¹ (pcg A P b x₀ (k + 1)).r) /
    inner ℝ (toEuclideanLin A (pcg A P b x₀ k).p) (pcg A P b x₀ k).p

theorem pcg_succ (k : ℕ) : pcg A P b x₀ (k + 1) = pcgStep A P (pcg A P b x₀ k) :=
  Function.iterate_succ_apply' _ _ _

/-- `x⁽ᵏ⁺¹⁾ = x⁽ᵏ⁾ + α_k p⁽ᵏ⁾`. -/
theorem pcg_succ_x (k : ℕ) :
    (pcg A P b x₀ (k + 1)).x = (pcg A P b x₀ k).x + pcgAlpha A P b x₀ k • (pcg A P b x₀ k).p := by
  rw [pcg_succ]
  rfl

/-- `r⁽ᵏ⁺¹⁾ = r⁽ᵏ⁾ - α_k A p⁽ᵏ⁾`. -/
theorem pcg_succ_r (k : ℕ) :
    (pcg A P b x₀ (k + 1)).r =
      (pcg A P b x₀ k).r - pcgAlpha A P b x₀ k • toEuclideanLin A (pcg A P b x₀ k).p := by
  rw [pcg_succ]
  rfl

/-- `p⁽ᵏ⁺¹⁾ = z⁽ᵏ⁺¹⁾ - β_k p⁽ᵏ⁾` with `z⁽ᵏ⁺¹⁾ = P⁻¹ r⁽ᵏ⁺¹⁾`. -/
theorem pcg_succ_p (k : ℕ) :
    (pcg A P b x₀ (k + 1)).p =
      toEuclideanLin P⁻¹ (pcg A P b x₀ (k + 1)).r - pcgBeta A P b x₀ k • (pcg A P b x₀ k).p := by
  rw [pcgBeta, pcg_succ]
  rfl

variable {A P b x₀}

/-- A symmetric positive definite `P` with its inverse `P⁻¹` is a preconditioner in the
backbone's sense. -/
theorem isPreconditioner_of_posDef (hP : P.PosDef) :
    Krylov.IsPreconditioner (toEuclideanLin P) (toEuclideanLin P⁻¹) :=
  ⟨posDef_isSymmetricCoercive_toEuclideanLin hP,
    fun x => toEuclideanLin_mul_nonsing_inv_apply hP.isUnit x⟩

/-- For `A` and `P` symmetric positive definite, the preconditioned operator `P⁻¹ A` is symmetric
coercive in the `P`-inner product: it is symmetric there because `A` is, and coercive because
`(P⁻¹ A x, x)_P = (A x, x) > 0` for `x ≠ 0` and the space is finite-dimensional
(`LinearMap.isCoercive_iff_forall_pos`). -/
theorem isSymmetricCoercive_energyEnd_of_posDef (hA : A.PosDef) (hP : P.PosDef) :
    ((isPreconditioner_of_posDef hP).energyEnd
      (toEuclideanLin P⁻¹ ∘ₗ toEuclideanLin A)).IsSymmetricCoercive := by
  have hM := isPreconditioner_of_posDef hP
  have hA' := posDef_isSymmetricCoercive_toEuclideanLin hA
  have : FiniteDimensional ℝ hM.EnergySpace := hM.toEnergy.finiteDimensional
  refine ⟨fun y y' => ?_, (LinearMap.isCoercive_iff_forall_pos _).2 fun y hy => ?_⟩
  · obtain ⟨x, rfl⟩ := hM.toEnergy.surjective y
    obtain ⟨x', rfl⟩ := hM.toEnergy.surjective y'
    rw [hM.inner_energyEnd_left, hM.inner_energyEnd_right]
    exact hA'.isSymmetric x x'
  · obtain ⟨x, rfl⟩ := hM.toEnergy.surjective y
    rw [hM.inner_energyEnd_left]
    exact hA'.isCoercive.inner_self_pos fun h => hy (by rw [h, map_zero])

/-- `(P⁻¹ r)ᵀ` against `P`-inner products: `(P⁻¹ u, w)_P = (u, w)`. -/
private theorem inner_toEnergy_inv_left (hP : P.PosDef) (u w : EuclideanSpace ℝ (Fin n)) :
    inner ℝ ((isPreconditioner_of_posDef hP).toEnergy (toEuclideanLin P⁻¹ u))
      ((isPreconditioner_of_posDef hP).toEnergy w) = inner ℝ u w := by
  rw [WithEnergy.inner_equiv, energyInner, (isPreconditioner_of_posDef hP).apply_inv]

/-- The residual of the backbone's PCG iteration after the book's step, and the identities
`p⁽ᵏ⁾ᵀ r⁽ᵏ⁾ = r⁽ᵏ⁾ᵀ P⁻¹ r⁽ᵏ⁾` behind the step length. -/
private theorem pcg_inner_direction_residual (hA : A.PosDef) (hP : P.PosDef) (k : ℕ) :
    inner ℝ (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k).p
        (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k).r =
      inner ℝ (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k).r
        (toEuclideanLin P⁻¹
          (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k).r) := by
  have hM := isPreconditioner_of_posDef hP
  have hB := isSymmetricCoercive_energyEnd_of_posDef hA hP
  obtain ⟨-, hr, hp, -⟩ := Krylov.PCG.iterate_eq_CG_iterate_withEnergy (toEuclideanLin A)
    (toEuclideanLin P⁻¹) b x₀ hM k
  have h := CG.inner_residual_direction_eq (hM.toEnergy (toEuclideanLin P⁻¹ b)) (hM.toEnergy x₀)
    hB (le_refl k)
  rw [RCLike.ofReal_real_eq_id, id_eq, ← hr, ← hp, inner_toEnergy_inv_left hP,
    ← real_inner_self_eq_norm_sq, inner_toEnergy_inv_left hP] at h
  rw [real_inner_comm, h, real_inner_comm]

/-- On the backbone's PCG iterates, the book's `α_k` is `Krylov.PCG.alpha`. -/
private theorem pcgAlpha_iterate (hA : A.PosDef) (hP : P.PosDef) (k : ℕ) :
    inner ℝ (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k).p
        (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k).r /
      inner ℝ (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k).p
        (toEuclideanLin A (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k).p) =
      Krylov.PCG.alpha (toEuclideanLin A) (toEuclideanLin P⁻¹)
        (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k) := by
  rw [Krylov.PCG.alpha, pcg_inner_direction_residual hA hP,
    real_inner_comm (toEuclideanLin A (Krylov.PCG.iterate _ _ b x₀ k).p)]

/-- On the backbone's PCG iterates, the book's step produces the backbone's residual. -/
private theorem pcgStep_r_iterate (hA : A.PosDef) (hP : P.PosDef) (k : ℕ) :
    (pcgStep A P (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k)).r =
      (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ (k + 1)).r := by
  rw [Krylov.PCG.iterate_succ, Krylov.PCG.step_r, pcgStep, pcgAlpha_iterate hA hP]

/-- On the backbone's PCG iterates, the book's `β_k` is the negative of `Krylov.PCG.beta`: from
`α_k A p⁽ᵏ⁾ = r⁽ᵏ⁾ - r⁽ᵏ⁺¹⁾` and the orthogonalities `r⁽ᵏ⁾ᵀ P⁻¹ r⁽ᵏ⁺¹⁾ = 0`, `r⁽ᵏ⁺¹⁾ᵀ p⁽ᵏ⁾ = 0`
of the conjugate gradient method in the `P`-inner product. -/
private theorem pcgBeta_iterate (hA : A.PosDef) (hP : P.PosDef) (k : ℕ) :
    inner ℝ
        (toEuclideanLin A (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k).p)
        (toEuclideanLin P⁻¹
          (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ (k + 1)).r) /
      inner ℝ
        (toEuclideanLin A (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k).p)
        (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k).p =
      -Krylov.PCG.beta (toEuclideanLin A) (toEuclideanLin P⁻¹)
        (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k) := by
  have hM := isPreconditioner_of_posDef hP
  have hB := isSymmetricCoercive_energyEnd_of_posDef hA hP
  set A' := toEuclideanLin A with hA'def
  set Minv := toEuclideanLin P⁻¹ with hMinv
  set S := Krylov.PCG.iterate A' Minv b x₀ with hS
  set T := CG.iterate (hM.energyEnd (Minv ∘ₗ A')) (hM.toEnergy (Minv b)) (hM.toEnergy x₀) with hT
  obtain ⟨-, hr, hp, -⟩ := Krylov.PCG.iterate_eq_CG_iterate_withEnergy A' Minv b x₀ hM k
  obtain ⟨-, hr1, -, -⟩ := Krylov.PCG.iterate_eq_CG_iterate_withEnergy A' Minv b x₀ hM (k + 1)
  have hstep : (S (k + 1)).r = (S k).r - Krylov.PCG.alpha A' Minv (S k) • A' (S k).p := by
    rw [hS, Krylov.PCG.iterate_succ, Krylov.PCG.step_r]
  rw [Krylov.PCG.beta, ← Krylov.PCG.iterate_succ]
  rcases eq_or_ne (S k).r 0 with hr0 | hr0
  · have hTr : (T k).r = 0 := by rw [← hr, hr0, map_zero, map_zero]
    have hTp : (T k).p = 0 := CG.direction_eq_zero_of_residual_eq_zero _ _ _ hTr
    have hp0 : (S k).p = 0 := by
      rw [← hp] at hTp
      exact hM.toEnergy.map_eq_zero_iff.mp hTp
    rw [hstep, hr0, hp0]
    simp
  · have hTr : (T k).r ≠ 0 := by
      rw [← hr]
      intro h
      have h' : Minv (S k).r = 0 := hM.toEnergy.map_eq_zero_iff.mp h
      exact hr0 (by rw [← hM.apply_inv (S k).r, h', map_zero])
    have hpos := CG.re_inner_apply_direction_pos (hM.toEnergy (Minv b)) (hM.toEnergy x₀) hB hTr
    rw [← hp, hM.inner_energyEnd_left, RCLike.re_to_real] at hpos
    have hrpos : 0 < inner ℝ (S k).r (Minv (S k).r) := by
      have h := real_inner_self_pos.mpr hTr
      rwa [← hr, inner_toEnergy_inv_left hP] at h
    have hαne : Krylov.PCG.alpha A' Minv (S k) ≠ 0 := by
      rw [Krylov.PCG.alpha]
      exact div_ne_zero hrpos.ne' hpos.ne'
    have hAp : A' (S k).p = (Krylov.PCG.alpha A' Minv (S k))⁻¹ • ((S k).r - (S (k + 1)).r) := by
      rw [hstep, sub_sub_cancel, smul_smul, inv_mul_cancel₀ hαne, one_smul]
    have h1 : inner ℝ (S k).r (Minv (S (k + 1)).r) = 0 := by
      have h := CG.inner_residual_eq_zero (hM.toEnergy (Minv b)) (hM.toEnergy x₀) hB
        (Nat.ne_of_lt (Nat.lt_succ_self k))
      rwa [← hr, ← hr1, inner_toEnergy_inv_left hP] at h
    have h2 : inner ℝ (S (k + 1)).r (S k).p = 0 := by
      have h := CG.inner_residual_direction_eq_zero (hM.toEnergy (Minv b)) (hM.toEnergy x₀) hB
        (Nat.lt_succ_self k)
      rwa [← hr1, ← hp, inner_toEnergy_inv_left hP] at h
    have h3 : inner ℝ (S k).r (S k).p = inner ℝ (S k).r (Minv (S k).r) := by
      rw [real_inner_comm]
      exact pcg_inner_direction_residual hA hP k
    have hN := hrpos.ne'
    rw [hAp, inner_smul_left, inner_smul_left, inner_sub_left, inner_sub_left, h1, h2, h3,
      RCLike.conj_to_real]
    simp only [← hS]
    field_simp
    ring

/-- Extensionality for the backbone's PCG state (a record of three vectors). -/
private theorem PCG.State.ext' {E : Type*} {s t : Krylov.PCG.State E} (hx : s.x = t.x)
    (hr : s.r = t.r) (hp : s.p = t.p) : s = t := by
  cases s
  cases t
  simp only at hx hr hp
  rw [hx, hr, hp]

/-- On the backbone's PCG iterates, the book's step is the backbone's step. -/
private theorem pcgStep_iterate (hA : A.PosDef) (hP : P.PosDef) (k : ℕ) :
    pcgStep A P (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k) =
      Krylov.PCG.step (toEuclideanLin A) (toEuclideanLin P⁻¹)
        (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k) := by
  have hβ := pcgBeta_iterate hA hP (b := b) (x₀ := x₀) k
  have hr := pcgStep_r_iterate hA hP (b := b) (x₀ := x₀) k
  set s := Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k with hs
  refine PCG.State.ext' ?_ ?_ ?_
  · rw [Krylov.PCG.step_x, pcgStep, pcgAlpha_iterate hA hP]
  · rw [Krylov.PCG.step_r, pcgStep, pcgAlpha_iterate hA hP]
  · rw [Krylov.PCG.step_p, ← Krylov.PCG.iterate_succ, ← hr]
    change toEuclideanLin P⁻¹ (pcgStep A P s).r -
      (inner ℝ (toEuclideanLin A s.p) (toEuclideanLin P⁻¹ (pcgStep A P s).r) /
        inner ℝ (toEuclideanLin A s.p) s.p) • s.p = _
    rw [hr, hβ, neg_smul, sub_neg_eq_add]

/-- **The bridge to the backbone for the preconditioned method.** For `A` and `P` symmetric
positive definite, the preconditioned conjugate gradient method of §4.3.5 is the backbone's
`Krylov.PCG.iterate`, the book's `α_k` is `Krylov.PCG.alpha` and its `β_k` is `-Krylov.PCG.beta`;
the identities `p⁽ᵏ⁾ᵀ r⁽ᵏ⁾ = r⁽ᵏ⁾ᵀ P⁻¹ r⁽ᵏ⁾` and `(A p⁽ᵏ⁾)ᵀ P⁻¹ r⁽ᵏ⁺¹⁾ = -(r⁽ᵏ⁺¹⁾ᵀ P⁻¹ r⁽ᵏ⁺¹⁾)/α_k`
behind them are those of the conjugate gradient method for `P⁻¹ A` in the `P`-inner product
(`Krylov.PCG.iterate_eq_CG_iterate_withEnergy`). -/
theorem pcg_eq_PCG (hA : A.PosDef) (hP : P.PosDef) (k : ℕ) :
    pcg A P b x₀ k = Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k ∧
      pcgAlpha A P b x₀ k = Krylov.PCG.alpha (toEuclideanLin A) (toEuclideanLin P⁻¹)
        (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k) ∧
      pcgBeta A P b x₀ k = -Krylov.PCG.beta (toEuclideanLin A) (toEuclideanLin P⁻¹)
        (Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k) := by
  have hpcg : ∀ k, pcg A P b x₀ k =
      Krylov.PCG.iterate (toEuclideanLin A) (toEuclideanLin P⁻¹) b x₀ k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [pcg_succ, ih, pcgStep_iterate hA hP, Krylov.PCG.iterate_succ]
  refine ⟨hpcg k, ?_, ?_⟩
  · rw [pcgAlpha, hpcg, pcgAlpha_iterate hA hP]
  · rw [pcgBeta, hpcg, hpcg, pcgBeta_iterate hA hP]

/-- **§4.3.5, the error estimate.** "The error estimate is the same as for the nonpreconditioned
method, provided to replace the matrix `A` by `P⁻¹ A`": for `A`, `P` symmetric positive definite,
`x` the solution, and the generalized eigenvalues of `A y = λ P y` enclosed in `[λ_n, λ_1]` —
`λ_n (P y, y) ≤ (A y, y) ≤ λ_1 (P y, y)` for all `y`, cf. Remark 4.2 — with `K = λ_1/λ_n`,
`‖e⁽ᵏ⁾‖_A ≤ 2 ((√K - 1)/(√K + 1))ᵏ ‖e⁽⁰⁾‖_A` (backbone `Krylov.PCG.energyNorm_error_le`
through `pcg_eq_PCG`). -/
theorem pcg_energyNorm_error_le (hA : A.PosDef) (hP : P.PosDef) {x : EuclideanSpace ℝ (Fin n)}
    (hx : toEuclideanLin A x = b) {lmin lmax : ℝ} (hpos : 0 < lmin) (hle : lmin ≤ lmax)
    (hlo : ∀ y, lmin * inner ℝ (toEuclideanLin P y) y ≤ inner ℝ (toEuclideanLin A y) y)
    (hhi : ∀ y, inner ℝ (toEuclideanLin A y) y ≤ lmax * inner ℝ (toEuclideanLin P y) y) (k : ℕ) :
    energyNorm (toEuclideanLin A) (x - (pcg A P b x₀ k).x) ≤
      2 * ((√(lmax / lmin) - 1) / (√(lmax / lmin) + 1)) ^ k *
        energyNorm (toEuclideanLin A) (x - x₀) := by
  rw [(pcg_eq_PCG hA hP k).1]
  exact Krylov.PCG.energyNorm_error_le (isPreconditioner_of_posDef hP)
    (posDef_isSymmetricCoercive_toEuclideanLin hA).isSymmetric hpos hle
    (fun y => by simpa using hlo y) (fun y => by simpa using hhi y) hx k

end PCG


/-! ### §4.3.6 The alternating-direction method -/

section ADI

variable (A₁ A₂ : Matrix (Fin n) (Fin n) ℝ) (α₁ α₂ : ℝ)

/-- **(4.50), the alternating-direction (Peaceman–Rachford) method** for `A = A₁ + A₂`, with two
real parameters `α₁`, `α₂`: one step solves `(I + α₁ A₁) x⁽ᵏ⁺¹ᐟ²⁾ = (I - α₁ A₂) x⁽ᵏ⁾ + α₁ b` for the
half step and then `(I + α₂ A₂) x⁽ᵏ⁺¹⁾ = (I - α₂ A₁) x⁽ᵏ⁺¹ᐟ²⁾ + α₂ b`. -/
noncomputable def adiStep (b x : Fin n → ℝ) : Fin n → ℝ :=
  (1 + α₂ • A₂)⁻¹ *ᵥ ((1 - α₂ • A₁) *ᵥ ((1 + α₁ • A₁)⁻¹ *ᵥ ((1 - α₁ • A₂) *ᵥ x + α₁ • b)) + α₂ • b)

/-- **The iteration matrix of the ADI method**,
`B = (I + α₂ A₂)⁻¹ (I - α₂ A₁) (I + α₁ A₁)⁻¹ (I - α₁ A₂)` (the display after (4.50)). -/
noncomputable def adiMatrix : Matrix (Fin n) (Fin n) ℝ :=
  (1 + α₂ • A₂)⁻¹ * (1 - α₂ • A₁) * (1 + α₁ • A₁)⁻¹ * (1 - α₁ • A₂)

/-- **The vector `f` of the ADI method**,
`f = (I + α₂ A₂)⁻¹ [α₁ (I - α₂ A₁)(I + α₁ A₁)⁻¹ + α₂ I] b`. The book's display omits the leading
factor `(I + α₂ A₂)⁻¹`, which composing the two half-steps produces (see the module
documentation). -/
noncomputable def adiConst (b : Fin n → ℝ) : Fin n → ℝ :=
  ((1 + α₂ • A₂)⁻¹ * (α₁ • ((1 - α₂ • A₁) * (1 + α₁ • A₁)⁻¹) + α₂ • 1)) *ᵥ b

/-- **The display after (4.50).** The ADI method is the linear iterative method (4.2) with matrix
`B = adiMatrix` and vector `f = adiConst`, for every choice of the parameters (an algebraic
identity, valid with Mathlib's junk-valued inverses). -/
theorem adiStep_eq_affineStep (b : Fin n → ℝ) :
    adiStep A₁ A₂ α₁ α₂ b = affineStep (adiMatrix A₁ A₂ α₁ α₂) (adiConst A₁ A₂ α₁ α₂ b) := by
  funext x
  simp only [adiStep, affineStep, adiMatrix, adiConst, mulVec_add, mulVec_smul, mulVec_mulVec,
    Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, add_mulVec, smul_mulVec, Matrix.mul_assoc]
  abel

/-- The ADI iteration matrix in the letters of the backbone, `r_i = 1/α_i`:
`B = (A₂ + r₂)⁻¹ (A₁ - r₂) (A₁ + r₁)⁻¹ (A₂ - r₁)`, over any field. -/
private theorem adiMatrix_eq_general {𝕜 : Type*} [Field 𝕜] (A₁ A₂ : Matrix (Fin n) (Fin n) 𝕜)
    {α₁ α₂ : 𝕜} (h₁ : α₁ ≠ 0) (h₂ : α₂ ≠ 0) :
    (1 + α₂ • A₂)⁻¹ * (1 - α₂ • A₁) * (1 + α₁ • A₁)⁻¹ * (1 - α₁ • A₂) =
      (A₂ + α₂⁻¹ • 1)⁻¹ * (A₁ - α₂⁻¹ • 1) * (A₁ + α₁⁻¹ • 1)⁻¹ * (A₂ - α₁⁻¹ • 1) := by
  have e1 : (1 : Matrix (Fin n) (Fin n) 𝕜) + α₂ • A₂ = α₂ • (A₂ + α₂⁻¹ • 1) := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ h₂, one_smul, add_comm]
  have e2 : (1 : Matrix (Fin n) (Fin n) 𝕜) - α₂ • A₁ = (-α₂) • (A₁ - α₂⁻¹ • 1) := by
    rw [smul_sub, smul_smul, neg_mul, mul_inv_cancel₀ h₂]
    module
  have e3 : (1 : Matrix (Fin n) (Fin n) 𝕜) + α₁ • A₁ = α₁ • (A₁ + α₁⁻¹ • 1) := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ h₁, one_smul, add_comm]
  have e4 : (1 : Matrix (Fin n) (Fin n) 𝕜) - α₁ • A₂ = (-α₁) • (A₂ - α₁⁻¹ • 1) := by
    rw [smul_sub, smul_smul, neg_mul, mul_inv_cancel₀ h₁]
    module
  rw [e1, e2, e3, e4, inv_smul_eq h₂, inv_smul_eq h₁]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [show -α₁ * (α₁⁻¹ * (-α₂ * α₂⁻¹)) = 1 by field_simp, one_smul]

/-- The matrix of the ADI vector `f` in the letters of the backbone:
`(I + α₂ A₂)⁻¹ [α₁ (I - α₂ A₁)(I + α₁ A₁)⁻¹ + α₂ I] = (A₂ + r₂)⁻¹ (I - (A₁ - r₂)(A₁ + r₁)⁻¹)`. -/
private theorem adiConst_eq_general {𝕜 : Type*} [Field 𝕜] (A₁ A₂ : Matrix (Fin n) (Fin n) 𝕜)
    {α₁ α₂ : 𝕜} (h₁ : α₁ ≠ 0) (h₂ : α₂ ≠ 0) :
    (1 + α₂ • A₂)⁻¹ * (α₁ • ((1 - α₂ • A₁) * (1 + α₁ • A₁)⁻¹) + α₂ • 1) =
      (A₂ + α₂⁻¹ • 1)⁻¹ * (1 - (A₁ - α₂⁻¹ • 1) * (A₁ + α₁⁻¹ • 1)⁻¹) := by
  have e1 : (1 : Matrix (Fin n) (Fin n) 𝕜) + α₂ • A₂ = α₂ • (A₂ + α₂⁻¹ • 1) := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ h₂, one_smul, add_comm]
  have e2 : (1 : Matrix (Fin n) (Fin n) 𝕜) - α₂ • A₁ = (-α₂) • (A₁ - α₂⁻¹ • 1) := by
    rw [smul_sub, smul_smul, neg_mul, mul_inv_cancel₀ h₂]
    module
  have e3 : (1 : Matrix (Fin n) (Fin n) 𝕜) + α₁ • A₁ = α₁ • (A₁ + α₁⁻¹ • 1) := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ h₁, one_smul, add_comm]
  rw [e1, e2, e3, inv_smul_eq h₂, inv_smul_eq h₁]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_add, Matrix.mul_sub,
    Matrix.mul_one]
  rw [show α₁ * (α₁⁻¹ * -α₂) * α₂⁻¹ = -1 by field_simp, show α₂ * α₂⁻¹ = 1 by field_simp]
  module

/-- The ADI iteration matrix as an operator, over `ℝ` or `ℂ`: with `α_i = 1/r_i` and the shifted
matrices `A_i + r_i I` nonsingular, `toEuclideanCLM B` is the backbone's
`Stationary.peacemanRachfordTwo (toEuclideanCLM A₁) (toEuclideanCLM A₂) r₁ r₂`. -/
private theorem toEuclideanCLM_adiMatrix_general {𝕜 : Type*} [RCLike 𝕜]
    (A₁ A₂ : Matrix (Fin n) (Fin n) 𝕜) {r₁ r₂ : ℝ} (h₁ : r₁ ≠ 0) (h₂ : r₂ ≠ 0)
    (hu₁ : IsUnit (A₁ + (r₁ : 𝕜) • (1 : Matrix (Fin n) (Fin n) 𝕜)))
    (hu₂ : IsUnit (A₂ + (r₂ : 𝕜) • (1 : Matrix (Fin n) (Fin n) 𝕜))) :
    toEuclideanCLM (n := Fin n) (𝕜 := 𝕜) ((1 + (r₂ : 𝕜)⁻¹ • A₂)⁻¹ * (1 - (r₂ : 𝕜)⁻¹ • A₁) *
        (1 + (r₁ : 𝕜)⁻¹ • A₁)⁻¹ * (1 - (r₁ : 𝕜)⁻¹ • A₂)) =
      peacemanRachfordTwo (toEuclideanCLM (n := Fin n) (𝕜 := 𝕜) A₁)
        (toEuclideanCLM (n := Fin n) (𝕜 := 𝕜) A₂) r₁ r₂ := by
  have h₁' : ((r₁ : 𝕜))⁻¹ ≠ 0 := inv_ne_zero (RCLike.ofReal_ne_zero.mpr h₁)
  have h₂' : ((r₂ : 𝕜))⁻¹ ≠ 0 := inv_ne_zero (RCLike.ofReal_ne_zero.mpr h₂)
  rw [adiMatrix_eq_general A₁ A₂ h₁' h₂', inv_inv, inv_inv, peacemanRachfordTwo, map_mul, map_mul,
    map_mul, toEuclideanCLM_nonsing_inv hu₂, toEuclideanCLM_nonsing_inv hu₁,
    toEuclideanCLM_add_smul_one, toEuclideanCLM_add_smul_one, toEuclideanCLM_sub_smul_one,
    toEuclideanCLM_sub_smul_one]

/-- The ADI vector `f` as an operator applied to `b`: `Stationary.peacemanRachfordTwoConst`. -/
private theorem toEuclideanCLM_adiConst_general {𝕜 : Type*} [RCLike 𝕜]
    (A₁ A₂ : Matrix (Fin n) (Fin n) 𝕜) {r₁ r₂ : ℝ} (h₁ : r₁ ≠ 0) (h₂ : r₂ ≠ 0)
    (hu₁ : IsUnit (A₁ + (r₁ : 𝕜) • (1 : Matrix (Fin n) (Fin n) 𝕜)))
    (hu₂ : IsUnit (A₂ + (r₂ : 𝕜) • (1 : Matrix (Fin n) (Fin n) 𝕜))) (b : Fin n → 𝕜) :
    toEuclideanCLM (n := Fin n) (𝕜 := 𝕜) ((1 + (r₂ : 𝕜)⁻¹ • A₂)⁻¹ *
        ((r₁ : 𝕜)⁻¹ • ((1 - (r₂ : 𝕜)⁻¹ • A₁) * (1 + (r₁ : 𝕜)⁻¹ • A₁)⁻¹) + (r₂ : 𝕜)⁻¹ • 1))
        (toLp 2 b) =
      peacemanRachfordTwoConst (toEuclideanCLM (n := Fin n) (𝕜 := 𝕜) A₁)
        (toEuclideanCLM (n := Fin n) (𝕜 := 𝕜) A₂) r₁ r₂ (toLp 2 b) := by
  have h₁' : ((r₁ : 𝕜))⁻¹ ≠ 0 := inv_ne_zero (RCLike.ofReal_ne_zero.mpr h₁)
  have h₂' : ((r₂ : 𝕜))⁻¹ ≠ 0 := inv_ne_zero (RCLike.ofReal_ne_zero.mpr h₂)
  rw [adiConst_eq_general A₁ A₂ h₁' h₂', inv_inv, inv_inv, peacemanRachfordTwoConst, map_mul,
    map_sub, map_mul, map_one, toEuclideanCLM_nonsing_inv hu₂, toEuclideanCLM_nonsing_inv hu₁,
    toEuclideanCLM_add_smul_one, toEuclideanCLM_add_smul_one, toEuclideanCLM_sub_smul_one,
    mul_apply_eq_comp]

/-- For a positive definite `A` and `r > 0`, the shift `A + r I` is nonsingular. -/
private theorem isUnit_add_smul_one_of_posDef {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {r : ℝ} (hr : 0 < r) : IsUnit (A + r • (1 : Matrix (Fin n) (Fin n) ℝ)) :=
  (hA.add (Matrix.PosDef.one.smul hr)).isUnit

/-- The complexified shift is nonsingular as well. -/
private theorem isUnit_complexify_add_smul_one_of_posDef {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) {r : ℝ} (hr : 0 < r) :
    IsUnit (complexify A + (r : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  rw [← complexify_one, ← complexify_smul, ← complexify_add, isUnit_complexify_iff]
  exact isUnit_add_smul_one_of_posDef hA hr

/-- **The display after (4.50), the identification with the backbone.** For `A₁`, `A₂` symmetric
positive definite and `α₁, α₂ > 0`, the matrix `B` of the ADI method acts on `EuclideanSpace` as
the two-parameter Peaceman–Rachford sweep operator `Stationary.peacemanRachfordTwo` with the
reciprocal parameters `r_i = 1/α_i`, and the vector `f` is its affine part
`Stationary.peacemanRachfordTwoConst`. -/
theorem equation_4_50 (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂)
    (b : Fin n → ℝ) :
    toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (adiMatrix A₁ A₂ α₁ α₂) =
        peacemanRachfordTwo (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A₁)
          (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A₂) (1 / α₁) (1 / α₂) ∧
      (toLp 2 (adiConst A₁ A₂ α₁ α₂ b) : EuclideanSpace ℝ (Fin n)) =
        peacemanRachfordTwoConst (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A₁)
          (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A₂) (1 / α₁) (1 / α₂) (toLp 2 b) := by
  have h₁ : (1 / α₁ : ℝ) ≠ 0 := one_div_ne_zero hα₁.ne'
  have h₂ : (1 / α₂ : ℝ) ≠ 0 := one_div_ne_zero hα₂.ne'
  have hu₁ := isUnit_add_smul_one_of_posDef hA₁ (one_div_pos.mpr hα₁)
  have hu₂ := isUnit_add_smul_one_of_posDef hA₂ (one_div_pos.mpr hα₂)
  have hinv : ∀ α : ℝ, ((1 / α : ℝ) : ℝ)⁻¹ = α := fun α => by rw [one_div, inv_inv]
  constructor
  · have h := toEuclideanCLM_adiMatrix_general A₁ A₂ h₁ h₂ hu₁ hu₂
    rw [RCLike.ofReal_real_eq_id, id_eq, id_eq, hinv, hinv] at h
    exact h
  · have h := toEuclideanCLM_adiConst_general A₁ A₂ h₁ h₂ hu₁ hu₂ b
    rw [RCLike.ofReal_real_eq_id, id_eq, id_eq, hinv, hinv] at h
    rw [adiConst, ← toEuclideanCLM_toLp]
    exact h

/-- The complexified ADI matrix acts on `EuclideanSpace ℂ (Fin n)` as the Peaceman–Rachford sweep
operator of the complexified `A₁`, `A₂`. -/
private theorem toEuclideanCLM_complexify_adiMatrix (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef)
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) :
    toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (complexify (adiMatrix A₁ A₂ α₁ α₂)) =
      peacemanRachfordTwo (toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (complexify A₁))
        (toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (complexify A₂)) (1 / α₁) (1 / α₂) := by
  have h₁ : (1 / α₁ : ℝ) ≠ 0 := one_div_ne_zero hα₁.ne'
  have h₂ : (1 / α₂ : ℝ) ≠ 0 := one_div_ne_zero hα₂.ne'
  have hu₁ := isUnit_complexify_add_smul_one_of_posDef hA₁ (one_div_pos.mpr hα₁)
  have hu₂ := isUnit_complexify_add_smul_one_of_posDef hA₂ (one_div_pos.mpr hα₂)
  have hc : ∀ α : ℝ, (α : ℂ) = (((1 / α : ℝ) : ℂ))⁻¹ := fun α => by
    rw [one_div, Complex.ofReal_inv, inv_inv]
  rw [adiMatrix, complexify_mul, complexify_mul, complexify_mul, complexify_inv, complexify_inv,
    complexify_add, complexify_add, complexify_sub, complexify_sub, complexify_smul,
    complexify_smul, complexify_smul, complexify_smul, complexify_one, hc α₁, hc α₂]
  exact toEuclideanCLM_adiMatrix_general _ _ h₁ h₂ hu₁ hu₂

/-- The real spectrum of the operator of a complexified real matrix is the real spectrum of the
matrix. -/
private theorem spectrum_real_toEuclideanCLM_complexify (A : Matrix (Fin n) (Fin n) ℝ) :
    spectrum ℝ (toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (complexify A)) = spectrum ℝ A := by
  ext t
  rw [← spectrum.algebraMap_mem_iff ℂ, AlgEquiv.spectrum_eq (toEuclideanCLM (n := Fin n) (𝕜 := ℂ)),
    Complex.coe_algebraMap, ofReal_mem_spectrum_complexify_iff]

/-- The operator of a complexified real symmetric matrix with real spectrum in `[lmin, lmax]` has
its quadratic form enclosed in `[lmin, lmax]`. -/
private theorem isSymmetricBoundedBy_toEuclideanCLM_complexify {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) {lmin lmax : ℝ} (hsub : spectrum ℝ A ⊆ Set.Icc lmin lmax) :
    ((toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (complexify A) :
      EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
        EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)).IsSymmetricBoundedBy
          lmin lmax := by
  rw [coe_toEuclideanCLM_eq_toEuclideanLin]
  refine (LinearMap.IsSymmetric.isSymmetricBoundedBy_iff_forall_hasEigenvalue
    (isSymmetric_toEuclideanLin_iff.mpr ((isHermitian_complexify_iff A).mpr hA)) lmin lmax).mpr
    fun μ hμ => ?_
  rw [hasEigenvalue_toEuclideanLin_iff] at hμ
  obtain ⟨t, ht, rfl⟩ := hA.spectrum_complexify_subset hsub hμ
  simpa using ht

/-- The complex spectral radius of the ADI matrix is the spectral radius of the sweep operator. -/
private theorem complexSpectralRadius_adiMatrix (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef)
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) :
    complexSpectralRadius (adiMatrix A₁ A₂ α₁ α₂) =
      spectralRadius ℂ (peacemanRachfordTwo (toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (complexify A₁))
        (toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (complexify A₂)) (1 / α₁) (1 / α₂)) := by
  rw [← toEuclideanCLM_complexify_adiMatrix A₁ A₂ α₁ α₂ hA₁ hA₂ hα₁ hα₂, complexSpectralRadius]
  simp only [spectralRadius]
  rw [AlgEquiv.spectrum_eq (toEuclideanCLM (n := Fin n) (𝕜 := ℂ))]

/-- The scalar identity behind the book's form of the ADI bound: for `t, α₁, α₂ > 0`,
`|t - 1/α₂| / (t + 1/α₁) = (α₁/α₂) |1 - α₂ t| / (1 + α₁ t)`. -/
private theorem abs_sub_div_add_eq {t : ℝ} (ht : 0 < t) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) :
    |t - 1 / α₂| / (t + 1 / α₁) = α₁ / α₂ * (|1 - α₂ * t| / (1 + α₁ * t)) := by
  have h1 : |t - 1 / α₂| * α₂ = |1 - α₂ * t| := by
    have h : |t - 1 / α₂| * α₂ = |(t - 1 / α₂) * α₂| := by
      rw [abs_mul, abs_of_pos hα₂]
    rw [h, abs_sub_comm 1 (α₂ * t)]
    congr 1
    field_simp
  have ht1 : t + 1 / α₁ ≠ 0 := by positivity
  have ht2 : 1 + α₁ * t ≠ 0 := by positivity
  rw [← h1]
  field_simp
  ring

/-- **§4.3.6, the estimate of `ρ(B)`.** For `A₁`, `A₂` symmetric positive definite with
eigenvalues `λ_i⁽¹⁾`, `λ_i⁽²⁾` (Mathlib's `Matrix.IsHermitian.eigenvalues`) and `α₁, α₂ > 0`,
`ρ(B) ≤ max_i |(1 - α₂ λ_i⁽¹⁾)/(1 + α₁ λ_i⁽¹⁾)| · max_i |(1 - α₁ λ_i⁽²⁾)/(1 + α₂ λ_i⁽²⁾)|`
(backbone `Stationary.spectralRadius_peacemanRachfordTwo_le`, which needs no commutativity of
`A₁` and `A₂`; the two factors are those of the backbone up to the constants `α₁/α₂` and `α₂/α₁`,
which cancel in the product). -/
theorem adi_spectralRadius_le [NeZero n] (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef) (hα₁ : 0 < α₁)
    (hα₂ : 0 < α₂) :
    complexSpectralRadius (adiMatrix A₁ A₂ α₁ α₂) ≤ ENNReal.ofReal
      (univ.sup' univ_nonempty
          (fun i => |1 - α₂ * hA₁.1.eigenvalues i| / (1 + α₁ * hA₁.1.eigenvalues i)) *
        univ.sup' univ_nonempty
          (fun i => |1 - α₁ * hA₂.1.eigenvalues i| / (1 + α₂ * hA₂.1.eigenvalues i))) := by
  set M₁ := univ.sup' univ_nonempty
    fun i => |1 - α₂ * hA₁.1.eigenvalues i| / (1 + α₁ * hA₁.1.eigenvalues i) with hM₁
  set M₂ := univ.sup' univ_nonempty
    fun i => |1 - α₁ * hA₂.1.eigenvalues i| / (1 + α₂ * hA₂.1.eigenvalues i) with hM₂
  have hM₁0 : 0 ≤ M₁ := by
    refine le_trans ?_ (Finset.le_sup'
      (fun i => |1 - α₂ * hA₁.1.eigenvalues i| / (1 + α₁ * hA₁.1.eigenvalues i))
      (mem_univ (0 : Fin n)))
    exact div_nonneg (abs_nonneg _) (by linarith [mul_pos hα₁ (hA₁.eigenvalues_pos 0)])
  have hM₂0 : 0 ≤ M₂ := by
    refine le_trans ?_ (Finset.le_sup'
      (fun i => |1 - α₁ * hA₂.1.eigenvalues i| / (1 + α₂ * hA₂.1.eigenvalues i))
      (mem_univ (0 : Fin n)))
    exact div_nonneg (abs_nonneg _) (by linarith [mul_pos hα₂ (hA₂.eigenvalues_pos 0)])
  have hbound : ∀ {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) {β γ : ℝ}, 0 < β → 0 < γ →
      ∀ t ∈ spectrum ℝ (toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (complexify A)),
        |t - 1 / γ| / (t + 1 / β) ≤ β / γ * univ.sup' univ_nonempty
          (fun i => |1 - γ * hA.1.eigenvalues i| / (1 + β * hA.1.eigenvalues i)) := by
    intro A hA β γ hβ hγ t ht
    rw [spectrum_real_toEuclideanCLM_complexify, hA.1.spectrum_real_eq_range_eigenvalues] at ht
    obtain ⟨i, rfl⟩ := ht
    rw [abs_sub_div_add_eq β γ (hA.eigenvalues_pos i) hβ hγ]
    exact mul_le_mul_of_nonneg_left (Finset.le_sup'
      (fun i => |1 - γ * hA.1.eigenvalues i| / (1 + β * hA.1.eigenvalues i)) (mem_univ i))
      (div_pos hβ hγ).le
  rw [complexSpectralRadius_adiMatrix A₁ A₂ α₁ α₂ hA₁ hA₂ hα₁ hα₂,
    show M₁ * M₂ = (α₁ / α₂ * M₁) * (α₂ / α₁ * M₂) by field_simp]
  exact spectralRadius_peacemanRachfordTwo_le hA₁.isSymmetricCoercive_toEuclideanCLM_complexify
    hA₂.isSymmetricCoercive_toEuclideanCLM_complexify (one_div_pos.mpr hα₁) (one_div_pos.mpr hα₂)
    (mul_nonneg (div_pos hα₁ hα₂).le hM₁0) (mul_nonneg (div_pos hα₂ hα₁).le hM₂0)
    (hbound hA₁ hα₁ hα₂) (hbound hA₂ hα₂ hα₁)

/-- **§4.3.6, convergence for equal parameters.** "The method converges if `ρ(B) < 1`, which is
always verified if `α₁ = α₂ = α > 0`": for `A₁`, `A₂` symmetric positive definite, `α > 0` and
`(A₁ + A₂) x = b`, the ADI iterates converge to `x` from every `x⁽⁰⁾` (backbone
`Stationary.tendsto_peacemanRachford` through `equation_4_50`; coercivity of `A₁`, `A₂` suffices,
neither symmetry nor commutativity is used). -/
theorem adi_tendsto (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef) {α : ℝ} (hα : 0 < α)
    {b x : Fin n → ℝ} (hx : (A₁ + A₂) *ᵥ x = b) (x₀ : Fin n → ℝ) :
    Tendsto (fun k => (adiStep A₁ A₂ α α b)^[k] x₀) atTop (𝓝 x) := by
  obtain ⟨hB, hf⟩ := equation_4_50 A₁ A₂ α α hA₁ hA₂ hα hα b
  rw [peacemanRachfordTwo_self] at hB
  rw [peacemanRachfordTwoConst_self] at hf
  have hH : ((toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A₁ :
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsCoercive := by
    rw [coe_toEuclideanCLM_eq_toEuclideanLin]
    exact (posDef_isSymmetricCoercive_toEuclideanLin hA₁).isCoercive
  have hV : ((toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A₂ :
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsCoercive := by
    rw [coe_toEuclideanCLM_eq_toEuclideanLin]
    exact (posDef_isSymmetricCoercive_toEuclideanLin hA₂).isCoercive
  have hx' : (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A₁ + toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A₂)
      (toLp 2 x) = toLp 2 b := by
    rw [← map_add, toEuclideanCLM_toLp, hx]
  have h := tendsto_peacemanRachford hH hV (one_div_pos.mpr hα) hx' (toLp 2 x₀)
  simp only [← hB, ← hf, ← toLp_affineStep_iterate, ← adiStep_eq_affineStep] at h
  have h' := (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin n => ℝ)).tendsto _ |>.comp h
  simpa [Function.comp_def] using h'

/-- **§4.3.6, the last display.** If the eigenvalues of `A₁` and `A₂` all lie in `[γ, δ]`,
`0 < γ ≤ δ`, then with `α₁ = α₂ = 1/√(δγ)` the ADI iteration matrix satisfies
`ρ(B) ≤ ((1 - √(γ/δ))/(1 + √(γ/δ)))²` (backbone
`Stationary.spectralRadius_peacemanRachford_le_of_spectrum_subset`). The book's proviso "provided
`γ/δ` tends to `0` as the size of `A` grows" is not a hypothesis of the inequality. -/
theorem adi_spectralRadius_le_sq (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef) {γ δ : ℝ} (hγ : 0 < γ)
    (hγδ : γ ≤ δ) (h₁ : ∀ i, hA₁.1.eigenvalues i ∈ Set.Icc γ δ)
    (h₂ : ∀ i, hA₂.1.eigenvalues i ∈ Set.Icc γ δ) :
    complexSpectralRadius (adiMatrix A₁ A₂ (1 / √(δ * γ)) (1 / √(δ * γ))) ≤
      ENNReal.ofReal (((1 - √(γ / δ)) / (1 + √(γ / δ))) ^ 2) := by
  have hr : 0 < 1 / √(δ * γ) := one_div_pos.mpr (Real.sqrt_pos.mpr (mul_pos (hγ.trans_le hγδ) hγ))
  have hsub : ∀ {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian),
      (∀ i, hA.eigenvalues i ∈ Set.Icc γ δ) → spectrum ℝ A ⊆ Set.Icc γ δ := by
    intro A hA h
    rw [hA.spectrum_real_eq_range_eigenvalues]
    rintro _ ⟨i, rfl⟩
    exact h i
  rw [complexSpectralRadius_adiMatrix A₁ A₂ _ _ hA₁ hA₂ hr hr, one_div_one_div,
    peacemanRachfordTwo_self, mul_comm δ γ]
  exact spectralRadius_peacemanRachford_le_of_spectrum_subset hγ hγδ
    (isSymmetricBoundedBy_toEuclideanCLM_complexify hA₁.1 (hsub hA₁.1 h₁))
    (isSymmetricBoundedBy_toEuclideanCLM_complexify hA₂.1 (hsub hA₂.1 h₂))

end ADI


end QuarteroniSaccoSaleri.Chapter04

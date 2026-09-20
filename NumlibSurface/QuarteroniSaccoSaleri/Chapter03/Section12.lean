import Numlib.LinearAlgebra.Matrix.Complexify
import NumlibSurface.QuarteroniSaccoSaleri.Chapter03.Section11

/-!
# Quarteroni–Sacco–Saleri §3.12: improving the accuracy of GEM

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §3.12, over the backbone `Numlib/Direct/Refinement` (scaling
`Matrix.scaled_mulVec_eq_iff`, iterative refinement `Refinement.step` as a stationary iteration
with its exactness and its error recursion), `Numlib/Conditioning/LinearSystem/Componentwise`
(the Skeel condition numbers `Matrix.skeelCond`, `Matrix.skeelCondAt` of Remark 3.7) and
`Numlib/LinearAlgebra/Matrix/Complexify` (`ρ(B) < 1 ↔ Bᵏ → 0` for a real matrix).

## Conventions

Scaling matrices are `diagonal d` for `d : Fin n → ℝ` with nonzero entries. The Skeel condition
numbers are the backbone's `Matrix.skeelCond A = ‖|A⁻¹| |A|‖_∞` and
`Matrix.skeelCondAt A x = ‖|A⁻¹| |A| |x|‖_∞ / ‖x‖_∞`, in the `∞`-norms of §3.1. One step of
iterative refinement with the approximate inverse `C` (in the book, the LU solve with the
computed factors, `C = (L̂ Û)⁻¹`) is `iterativeRefinementStep C A b x = x + C (b - A x)`, the
matrix form of the backbone's `Refinement.step`; the iterates `x⁽ⁱ⁾` are its `Function.iterate`
from `x⁽⁰⁾`. The spectral radius of a real matrix is `Matrix.complexSpectralRadius`, as in
chapter 1.

## Contents

* `scaledSystem` — `A x = b ↔ (D₁ A D₂) y = D₁ b` with `y = D₂⁻¹ x`, and row scaling.
* `remark_3_7`, `remark_3_7_iSup`, `remark_3_7_scaling` — the Skeel condition numbers.
* `iterativeRefinementStep`, `iterativeRefinementStep_eq`, `iterativeRefinement_exact`,
  `iterativeRefinement_convergence` — iterative refinement in exact arithmetic.
* `iterativeRefinement_fixedPrecision`, `iterativeRefinement_mixedPrecision` — the two
  finite-precision convergence statements of §3.12.2 (`ρ ≃ 2 n cond(A, x) u` for fixed-precision
  and `ρ ≃ u` for mixed-precision refinement), in the rigorous form of [higham2002accuracy]
  Theorems 12.2 and 12.1: the relative error obeys `e_{i+1} ≤ ρ e_i + φ` with explicit `ρ < 1`
  and floor `φ`, hence `e_k ≤ ρᵏ e_0 + φ / (1 - ρ)` and `limsup e_k ≤ φ / (1 - ρ)`, where the
  floor is `≈ 2 (n + 1) cond(A, x) u` in fixed precision and `≈ u` in mixed precision.

One step of iterative refinement in floating-point arithmetic — the exact error identity, its
`∞`-norm form and its instantiation in the relational rounding model — is a general fact with no
book-specific content and lives in the backbone as `Refinement.step_error`,
`Refinement.norm_step_error_le` and `Refinement.step_error_fp`; the computed steps of the two
convergence theorems are the backbone predicates `Refinement.RoundsStepLU` (residual in the
working precision) and `Refinement.RoundsStepLUMixed` (residual in a second, finer rounding model,
rounded once to the working precision), and the theorems are
`Refinement.norm_sub_le_of_forall_roundsStepLU` and
`Refinement.norm_sub_le_of_forall_roundsStepLUMixed`.

Example 3.10 (a numerical run), the heuristics `‖D₂⁻¹(x̂ - x)‖/‖D₂⁻¹ x‖ ≃ u K_∞(D₁ A D₂)` (which is
(3.69) for the scaled system) and `K_∞(A) ≃ β^{t(1 - 1/p)}`, and the stopping test of step 4 are
not nodes.

## Readings and errata

Remark 3.7 prints `cond(A, x) = ‖|A⁻¹| A |x| x‖_∞ / ‖x‖_∞`; it is read as
`‖|A⁻¹| |A| |x|‖_∞ / ‖x‖_∞`, the definition of [Ske79] and [higham2002accuracy] §7.2. The
convergence of iterative refinement in exact arithmetic is stated as "the iterates converge
from every `x⁽⁰⁾` to one and the same limit, for every `b`, iff `ρ(I - C A) < 1`"; the backbone's
`Refinement.forall_tendsto_iff_spectralRadius_lt_one` allows the limit to depend on the start and
needs `C` onto instead (`C = 0` is a counterexample otherwise). The two displays
`ρ ≃ 2 n cond(A, x) u` (FPR) and `ρ ≃ u` (MPR) of §3.12.2 are not propositions as printed (`≃`,
and "sufficiently small" without a quantifier); they are read as [higham2002accuracy] Theorems
12.2 and 12.1, the source the book cites, where the two quantities are the *limiting accuracy*
of the refined solution and the contraction factor is `η ≈ u ‖|A⁻¹| (|A| + 3n |L̂| |Û|)‖_∞`.
"sufficiently small" is the explicit hypothesis `2θ + γ_{n+1} cond(A) + 2u < 1` with
`θ = γ_{3n} ‖|A⁻¹| |L̂| |Û|‖_∞`, and `≃` is replaced by the explicit constants of the model.
-/

open Filter Finset Matrix Topology WithLp
open scoped ENNReal

namespace QuarteroniSaccoSaleri.Chapter03

variable {n : ℕ}

/-! ### §3.12.1: scaling, and Remark 3.7 -/

/-- **§3.12.1, scaling.** For nonsingular diagonal `D₁ = diag(d₁)` (scaling the equations) and
`D₂ = diag(d₂)` (scaling the unknowns), the system `A x = b` is equivalent to the scaled system
`(D₁ A D₂) y = D₁ b` with `y = D₂⁻¹ x`; row scaling alone is `D₁ A x = D₁ b` (backbone
`Matrix.scaled_mulVec_eq_iff`). -/
theorem scaledSystem {d₁ d₂ : Fin n → ℝ} (h₁ : ∀ i, d₁ i ≠ 0) (h₂ : ∀ i, d₂ i ≠ 0)
    (A : Matrix (Fin n) (Fin n) ℝ) (x b : Fin n → ℝ) :
    (A *ᵥ x = b ↔ (diagonal d₁ * A * diagonal d₂) *ᵥ ((diagonal d₂)⁻¹ *ᵥ x) = diagonal d₁ *ᵥ b) ∧
      (A *ᵥ x = b ↔ (diagonal d₁ * A) *ᵥ x = diagonal d₁ *ᵥ b) := by
  have hu : ∀ {d : Fin n → ℝ}, (∀ i, d i ≠ 0) → IsUnit (diagonal d) := fun hd => by
    rw [isUnit_iff_isUnit_det, det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    exact fun i _ => hd i
  have hu₁ := hu h₁
  have hu₂ := hu h₂
  refine ⟨scaled_mulVec_eq_iff hu₁ hu₂ A x b, ?_⟩
  have h := scaled_mulVec_eq_iff hu₁ isUnit_one A x b
  rwa [Matrix.mul_one, inv_one, one_mulVec] at h

open scoped Matrix.Norms.Operator in
/-- **Remark 3.7, the Skeel condition numbers.** `cond(A) = ‖|A⁻¹| |A|‖_∞` and, for `x ≠ 0`,
`cond(A, x) = ‖|A⁻¹| |A| |x|‖_∞ / ‖x‖_∞` (the book's display is read with the missing absolute
values restored): the backbone's `Matrix.skeelCond A` and `Matrix.skeelCondAt A x`. -/
theorem remark_3_7 (A : Matrix (Fin n) (Fin n) ℝ) :
    skeelCond A = ‖A⁻¹.abs * A.abs‖ ∧
      ∀ x : Fin n → ℝ, skeelCondAt A x = ‖A⁻¹.abs *ᵥ (A.abs *ᵥ |x|)‖ / ‖x‖ :=
  ⟨by rw [skeelCond], fun x => by rw [skeelCondAt]⟩

/-- **Remark 3.7, `cond(A) = sup_{x ≠ 0} cond(A, x)`** (backbone
`Matrix.skeelCond_eq_iSup_skeelCondAt`, whose supremum over all `x` is the same, the junk
value `cond(A, 0) = 0` changing nothing). -/
theorem remark_3_7_iSup [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) :
    skeelCond A = ⨆ x : {x : Fin n → ℝ // x ≠ 0}, skeelCondAt A x := by
  rw [skeelCond_eq_iSup_skeelCondAt]
  have hbdd : BddAbove (Set.range fun x : Fin n → ℝ => skeelCondAt A x) :=
    ⟨skeelCond A, by rintro _ ⟨x, rfl⟩; exact skeelCondAt_le_skeelCond x⟩
  have hbdd' : BddAbove (Set.range fun x : {x : Fin n → ℝ // x ≠ 0} => skeelCondAt A x) :=
    ⟨skeelCond A, by rintro _ ⟨x, rfl⟩; exact skeelCondAt_le_skeelCond x.1⟩
  have hne : Nonempty {x : Fin n → ℝ // x ≠ 0} := ⟨⟨Pi.single 0 1, by simp⟩⟩
  refine le_antisymm (ciSup_le fun x => ?_) (ciSup_le fun x => le_ciSup hbdd x.1)
  rcases eq_or_ne x 0 with rfl | hx
  · refine le_ciSup_of_le hbdd' hne.some ?_
    rw [skeelCondAt, norm_zero, div_zero]
    exact skeelCondAt_nonneg _
  · exact le_ciSup hbdd' ⟨x, hx⟩

/-- **Remark 3.7, invariance under row scaling.** Unlike `K(A)`, `cond(A, x)` is invariant under
`A ↦ D A` for a nonsingular diagonal `D` (backbone `Matrix.skeelCondAt_diagonal_mul`). -/
theorem remark_3_7_scaling {d : Fin n → ℝ} (hd : ∀ i, d i ≠ 0) (A : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) : skeelCondAt (diagonal d * A) x = skeelCondAt A x :=
  skeelCondAt_diagonal_mul hd x

/-! ### §3.12.2: iterative refinement -/

section Refinement

variable (C A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)

/-- **§3.12.2, one step of iterative refinement**, steps 1–3: from the current `x⁽ⁱ⁾`, compute
the residual `r⁽ⁱ⁾ = b - A x⁽ⁱ⁾`, solve `A z = r⁽ⁱ⁾` approximately, `z = C r⁽ⁱ⁾` — in the book by
the LU factorization of `A`, `C = (L̂ Û)⁻¹` — and set `x⁽ⁱ⁺¹⁾ = x⁽ⁱ⁾ + z`. This is the matrix form
of the backbone's `Refinement.step` (`iterativeRefinementStep_eq`). -/
noncomputable def iterativeRefinementStep (x : Fin n → ℝ) : Fin n → ℝ :=
  x + C *ᵥ (b - A *ᵥ x)

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The refinement step is the backbone's `Refinement.step` on `PiLp p (Fin n → ℝ)`, and it is
the stationary iteration `x ↦ (I - C A) x + C b` (backbone
`Refinement.step_eq_stationary_step`). -/
theorem iterativeRefinementStep_eq (x : Fin n → ℝ) :
    toLp p (iterativeRefinementStep C A b x) =
        Refinement.step (lpCLM p C) (lpCLM p A) (toLp p b) (toLp p x) ∧
      iterativeRefinementStep C A b x = (1 - C * A) *ᵥ x + C *ᵥ b := by
  constructor
  · rw [Refinement.step, lpCLM_apply, lpCLM_apply, ofLp_toLp, iterativeRefinementStep, toLp_add]
    rfl
  · rw [iterativeRefinementStep, sub_mulVec, one_mulVec, mulVec_sub, mulVec_mulVec]
    abel

/-- The iterates of the refinement step are those of the backbone's `Refinement.step`. -/
private theorem toLp_iterate (x₀ : Fin n → ℝ) (k : ℕ) :
    toLp p ((iterativeRefinementStep C A b)^[k] x₀) =
      (Refinement.step (lpCLM p C) (lpCLM p A) (toLp p b))^[k] (toLp p x₀) :=
  (Function.Semiconj.iterate_right (fun x => (iterativeRefinementStep_eq C A b p x).1) k) x₀

/-- `Matrix.lpCLM p` respects subtraction. -/
private theorem lpCLM_sub' (M N : Matrix (Fin n) (Fin n) ℝ) :
    lpCLM p (M - N) = lpCLM p M - lpCLM p N := by
  ext x i
  simp [sub_mulVec]

/-- `Matrix.lpCLM p` respects powers. -/
private theorem lpCLM_pow' (M : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    lpCLM p (M ^ k) = lpCLM p M ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, lpCLM_one]
  | succ k ih => rw [pow_succ, lpCLM_mul, ih, pow_succ]

variable {C A b}

/-- **§3.12.2, exactness.** "In absence of rounding errors, the process would stop at the first
step, yielding the exact solution": with the exact inverse `C = A⁻¹` — or the exact LU solve
`z = U⁻¹ (L⁻¹ r)` of Theorem 3.4's factorization with nonzero pivots — one step from any `x`
gives the solution `x*` of `A x = b` (backbone `Refinement.step_eq_of_eq_inverse`,
`Matrix.mulVec_luSolve`). -/
theorem iterativeRefinement_exact (hA : IsUnit A) {xs : Fin n → ℝ} (hxs : A *ᵥ xs = b)
    (x : Fin n → ℝ) :
    iterativeRefinementStep A⁻¹ A b x = xs ∧
      ∀ L U : Matrix (Fin n) (Fin n) ℝ, IsLU A L U → (∀ i, U i i ≠ 0) →
        x + luSolve L U (b - A *ᵥ x) = xs := by
  have hAd := (isUnit_iff_isUnit_det A).1 hA
  have h1 : iterativeRefinementStep A⁻¹ A b x = xs := by
    refine toLp_injective 2 ?_
    rw [(iterativeRefinementStep_eq A⁻¹ A b 2 x).1]
    refine Refinement.step_eq_of_eq_inverse ?_ (xs := toLp 2 xs) ?_ _
    · rw [← lpCLM_mul, nonsing_inv_mul _ hAd, lpCLM_one]
    · rw [lpCLM_apply, ofLp_toLp, hxs]
  refine ⟨h1, fun L U h hd => ?_⟩
  have hz : luSolve L U (b - A *ᵥ x) = A⁻¹ *ᵥ (b - A *ᵥ x) := by
    have := mulVec_luSolve (b - A *ᵥ x) h hd
    calc luSolve L U (b - A *ᵥ x) = A⁻¹ *ᵥ (A *ᵥ luSolve L U (b - A *ᵥ x)) :=
          (nonsing_inv_mulVec_mulVec hA _).symm
      _ = A⁻¹ *ᵥ (b - A *ᵥ x) := by rw [this]
  rw [hz]
  exact h1

/-- The error recursion of iterative refinement in exact arithmetic: with `x*` a solution of
`A x = b`, `x⁽ᵏ⁾ - x* = (I - C A)ᵏ (x⁽⁰⁾ - x*)` (backbone `Refinement.iterate_sub_eq`). -/
private theorem iterate_sub_eq' (C A : Matrix (Fin n) (Fin n) ℝ) {b xs : Fin n → ℝ}
    (hxs : A *ᵥ xs = b) (x₀ : Fin n → ℝ) (k : ℕ) :
    (iterativeRefinementStep C A b)^[k] x₀ - xs = ((1 - C * A) ^ k) *ᵥ (x₀ - xs) := by
  have h := Refinement.iterate_sub_eq (C := lpCLM 2 C) (A := lpCLM 2 A) (b := toLp 2 b)
    (xs := toLp 2 xs) (by rw [lpCLM_apply, ofLp_toLp, hxs]) (toLp 2 x₀) k
  rw [← toLp_iterate, ← toLp_sub, ← toLp_sub, ← lpCLM_mul, ← lpCLM_one, ← lpCLM_sub',
    ← lpCLM_pow', lpCLM_apply, ofLp_toLp] at h
  exact toLp_injective 2 h

/-- **§3.12.2, convergence in exact arithmetic.** Iterative refinement with the approximate
inverse `C` is the stationary iteration with matrix `I - C A`: for a solution `x*` of `A x = b`
the error obeys `x⁽ᵏ⁾ - x* = (I - C A)ᵏ (x⁽⁰⁾ - x*)`, so it is reduced by a factor
`‖I - C A‖_p` at each step (backbone `Refinement.iterate_sub_eq`,
`Refinement.norm_iterate_sub_le`); and the iterates converge from every start to one and the
same limit, for every right-hand side, iff `ρ(I - C A) < 1` (chapter 1's Theorem 1.5,
backbone `Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one`). -/
theorem iterativeRefinement_convergence (C A : Matrix (Fin n) (Fin n) ℝ) :
    (∀ (b xs : Fin n → ℝ), A *ᵥ xs = b → ∀ (x₀ : Fin n → ℝ) (k : ℕ),
      (iterativeRefinementStep C A b)^[k] x₀ - xs = ((1 - C * A) ^ k) *ᵥ (x₀ - xs) ∧
        ‖toLp p ((iterativeRefinementStep C A b)^[k] x₀ - xs)‖ ≤
          lpOpNorm p (1 - C * A) ^ k * ‖toLp p (x₀ - xs)‖) ∧
    ((∀ b : Fin n → ℝ, ∃ x, ∀ x₀,
        Tendsto (fun k => (iterativeRefinementStep C A b)^[k] x₀) atTop (𝓝 x)) ↔
      complexSpectralRadius (1 - C * A) < 1) := by
  refine ⟨fun b xs hxs x₀ k => ⟨iterate_sub_eq' C A hxs x₀ k, ?_⟩, ?_⟩
  · have h := Refinement.norm_iterate_sub_le (C := lpCLM p C) (A := lpCLM p A) (b := toLp p b)
      (xs := toLp p xs) (by rw [lpCLM_apply, ofLp_toLp, hxs]) (toLp p x₀) k
    rw [← toLp_iterate, ← toLp_sub, ← toLp_sub, ← lpCLM_mul, ← lpCLM_one, ← lpCLM_sub'] at h
    exact h
  · constructor
    · intro h
      obtain ⟨x, hx⟩ := h 0
      rw [← tendsto_pow_iff_complexSpectralRadius_lt_one,
        tendsto_zero_iff_forall_mulVec_tendsto_zero]
      intro v
      have hv := (hx v).sub (hx 0)
      rw [sub_self] at hv
      have key : ∀ k, (iterativeRefinementStep C A 0)^[k] v -
          (iterativeRefinementStep C A 0)^[k] 0 = ((1 - C * A) ^ k) *ᵥ v := by
        intro k
        have h1 := iterate_sub_eq' C A (xs := 0) (mulVec_zero A) v k
        have h2 := iterate_sub_eq' C A (xs := 0) (mulVec_zero A) 0 k
        rw [sub_zero, sub_zero] at h1
        rw [sub_zero, sub_zero, mulVec_zero] at h2
        rw [h1, h2, sub_zero]
      simpa only [key] using hv
    · intro h b
      have hu : IsUnit (C * A) := by
        have := isUnit_one_sub_of_complexSpectralRadius_lt_one h
        rwa [sub_sub_cancel] at this
      have hA : IsUnit A := (isUnit_iff_isUnit_det A).2
        (isUnit_of_mul_isUnit_right (by rw [← det_mul]; exact (isUnit_iff_isUnit_det _).1 hu))
      refine ⟨A⁻¹ *ᵥ b, fun x₀ => ?_⟩
      rw [← tendsto_sub_nhds_zero_iff]
      have hpow := (tendsto_pow_iff_complexSpectralRadius_lt_one _).2 h
      rw [tendsto_zero_iff_forall_mulVec_tendsto_zero] at hpow
      simpa only [iterate_sub_eq' C A (mulVec_nonsing_inv_mulVec hA b) x₀] using
        hpow (x₀ - A⁻¹ *ᵥ b)

end Refinement

/-! ### §3.12.2: iterative refinement in finite precision -/

section FinitePrecision

open FloatingPoint
open scoped Matrix.Norms.Operator

variable [NeZero n] {m : RoundingModel ℝ} {A L U : Matrix (Fin n) (Fin n) ℝ} {b x : Fin n → ℝ}

/-- Division of a recursion `a (k + 1) ≤ ρ a k + φ ‖x‖` by `‖x‖ > 0`. -/
private theorem div_recursion {a : ℕ → ℝ} {ρ φ c : ℝ} (hc : 0 < c)
    (h : ∀ k, a (k + 1) ≤ ρ * a k + φ * c) (k : ℕ) : a (k + 1) / c ≤ ρ * (a k / c) + φ :=
  (div_le_div_of_nonneg_right (h k) hc.le).trans_eq
    (by rw [add_div, mul_div_assoc, mul_div_assoc, div_self hc.ne', mul_one])

/-- **§3.12.2, fixed-precision iterative refinement (FPR)**, in the rigorous form of
[higham2002accuracy] Theorem 12.2, which the book's display summarizes. Let `A x = b` with `A`
nonsingular and `x ≠ 0`, let `L̂`, `Û` be the computed LU factors of `A` with nonzero pivots in a
floating-point arithmetic with roundoff unit `u`, `3 n u < 1`, and let `x⁽⁰⁾, x⁽¹⁾, …` be
iterates of the refinement algorithm (steps 1–3) computed in that arithmetic, the residual in the
working precision (`Refinement.RoundsStepLU` at every step). Put

`θ = γ_{3n} ‖|A⁻¹| |L̂| |Û|‖_∞`, `ρ = (θ + γ_{n+1} cond(A)) / (1 - 2u - θ)`,
`φ = (2 γ_{n+1} cond(A, x) + u (1 + θ)) / (1 - 2u - θ)`,

with `cond(A)`, `cond(A, x)` the Skeel condition numbers of Remark 3.7 and
`γ_k = k u / (1 - k u)`. If `‖|A⁻¹| |L̂| |Û|‖_∞` is sufficiently small — precisely, if
`2θ + γ_{n+1} cond(A) + 2u < 1` — then `ρ < 1` and at each step the relative error
`‖x - x⁽ⁱ⁾‖_∞ / ‖x‖_∞` is reduced by the factor `ρ` up to the floor `φ`:

`‖x - x⁽ⁱ⁺¹⁾‖_∞ / ‖x‖_∞ ≤ ρ ‖x - x⁽ⁱ⁾‖_∞ / ‖x‖_∞ + φ`,

hence `‖x - x⁽ᵏ⁾‖_∞ / ‖x‖_∞ ≤ ρᵏ ‖x - x⁽⁰⁾‖_∞ / ‖x‖_∞ + φ / (1 - ρ)`, and the limiting accuracy
is `limsup_k ‖x - x⁽ᵏ⁾‖_∞ / ‖x‖_∞ ≤ φ / (1 - ρ)`, where `φ ≈ 2 (n + 1) cond(A, x) u`. The book's
"`ρ ≃ 2 n cond(A, x) u`" is this floor (Higham's "until
`‖x - x̂_i‖_∞ / ‖x‖_∞ ≲ 2n cond(A, x) u`"); the contraction factor itself is
`ρ ≈ u ‖|A⁻¹| (3n |L̂| |Û| + (n + 1) |A|)‖_∞`, Higham's `η`. Backbone
`Refinement.norm_sub_le_of_forall_roundsStepLU`. -/
theorem iterativeRefinement_fixedPrecision (hcard : ((3 * n : ℕ) : ℝ) * m.u < 1) (hA : IsUnit A)
    (hx : A *ᵥ x = b) (hx0 : x ≠ 0) (hLU : RoundsLU m A L U) (hd : ∀ j, U j j ≠ 0)
    {xs : ℕ → Fin n → ℝ} (hstep : ∀ i, Refinement.RoundsStepLU m A L U b (xs i) (xs (i + 1)))
    {θ ρ φ : ℝ} (hθ : θ = gamma m.u (3 * n) * ‖A⁻¹.abs * (L.abs * U.abs)‖)
    (hρ : ρ = (θ + gamma m.u (n + 1) * skeelCond A) / (1 - 2 * m.u - θ))
    (hφ : φ = (2 * gamma m.u (n + 1) * skeelCondAt A x + m.u * (1 + θ)) / (1 - 2 * m.u - θ))
    (hsmall : 2 * θ + gamma m.u (n + 1) * skeelCond A + 2 * m.u < 1) :
    ρ < 1 ∧ (∀ i, ‖x - xs (i + 1)‖ / ‖x‖ ≤ ρ * (‖x - xs i‖ / ‖x‖) + φ) ∧
      (∀ k, ‖x - xs k‖ / ‖x‖ ≤ ρ ^ k * (‖x - xs 0‖ / ‖x‖) + φ / (1 - ρ)) ∧
      limsup (fun k => ‖x - xs k‖ / ‖x‖) atTop ≤ φ / (1 - ρ) := by
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hφx : φ * ‖x‖ = (2 * gamma m.u (n + 1) * ‖A⁻¹.abs *ᵥ (A.abs *ᵥ |x|)‖
      + m.u * (1 + θ) * ‖x‖) / (1 - 2 * m.u - θ) := by
    rw [hφ, skeelCondAt, div_mul_eq_mul_div]
    congr 1
    field_simp
  obtain ⟨hρ1, hrec, -, -⟩ := Refinement.norm_sub_le_of_forall_roundsStepLU (ρ := ρ)
    (φ := φ * ‖x‖) hcard hA hx hLU hd hstep hθ (by rw [hρ, skeelCond]) hφx
    (by rw [skeelCond] at hsmall; exact hsmall)
  have hθ0 : 0 ≤ θ := by
    rw [hθ]; exact mul_nonneg (gamma_nonneg m.u_nonneg hcard) (norm_nonneg _)
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  have hcard1 : ((n + 1 : ℕ) : ℝ) * m.u < 1 := by
    have h1 : ((n + 1 : ℕ) : ℝ) ≤ ((3 * n : ℕ) : ℝ) := by
      exact_mod_cast (by omega : n + 1 ≤ 3 * n)
    nlinarith [m.u_nonneg]
  have hγ1 := gamma_nonneg m.u_nonneg hcard1
  have hc0 : 0 ≤ skeelCond A := by rw [skeelCond]; exact norm_nonneg _
  have hcx0 := skeelCondAt_nonneg (A := A) x
  have hu0 := m.u_nonneg
  have hpos : 0 < 1 - 2 * m.u - θ := by linarith [mul_nonneg hγ1 hc0]
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hφ0 : 0 ≤ φ := by rw [hφ]; positivity
  have hrec' : ∀ i, ‖x - xs (i + 1)‖ / ‖x‖ ≤ ρ * (‖x - xs i‖ / ‖x‖) + φ :=
    div_recursion (a := fun k => ‖x - xs k‖) hxn hrec
  refine ⟨hρ1, hrec', fun k =>
    Refinement.le_pow_mul_add_div_of_forall_le_mul_add (a := fun k => ‖x - xs k‖ / ‖x‖) hρ0 hρ1
      hφ0 hrec' k, ?_⟩
  exact Refinement.limsup_le_div_of_forall_le_mul_add hρ0 hρ1 hφ0 (fun k => by positivity) hrec'

/-- **§3.12.2, mixed-precision iterative refinement (MPR)**, in the rigorous form of
[higham2002accuracy] Theorem 12.1. As `iterativeRefinement_fixedPrecision`, but the residual
`r⁽ⁱ⁾ = b - A x⁽ⁱ⁾` is computed in a second, finer floating-point arithmetic with roundoff unit
`ū` ("double precision"), `(n + 1) ū < 1`, and rounded once to the working precision
(`Refinement.RoundsStepLUMixed` at every step, a statement with two rounding models). Put

`θ = γ_{3n} ‖|A⁻¹| |L̂| |Û|‖_∞`, `ρ = (θ + (u + (1 + u) γ̄_{n+1}) cond(A)) / (1 - 2u - θ)`,
`φ = (2 (1 + u) γ̄_{n+1} cond(A, x) + u (1 + θ)) / (1 - 2u - θ)`,

with `γ̄_k = k ū / (1 - k ū)` the constant of the finer arithmetic. If
`2θ + (u + (1 + u) γ̄_{n+1}) cond(A) + 2u < 1` then `ρ < 1`, the relative error is reduced by the
factor `ρ` at each step up to the floor `φ`, `‖x - x⁽ᵏ⁾‖_∞ / ‖x‖_∞ ≤ ρᵏ ‖x - x⁽⁰⁾‖_∞ / ‖x‖_∞
+ φ / (1 - ρ)`, and `limsup_k ‖x - x⁽ᵏ⁾‖_∞ / ‖x‖_∞ ≤ φ / (1 - ρ)`. Moreover, in double the
working precision, `ū ≤ u²` with `2 (n + 1) ū ≤ 1`, the floor is

`φ ≤ u (1 + θ + 4 (1 + u) (n + 1) u cond(A, x)) / (1 - 2u - θ)`,

of the order of the roundoff unit `u` and independent of the condition number to first order in
`u`: this is the book's "`ρ ≃ u`, independent of the condition number of `A`" (Higham's "until
`‖x - x̂_i‖_∞ / ‖x‖_∞ ≈ u`"). Backbone `Refinement.norm_sub_le_of_forall_roundsStepLUMixed`. -/
theorem iterativeRefinement_mixedPrecision {m' : RoundingModel ℝ}
    (hcard : ((3 * n : ℕ) : ℝ) * m.u < 1) (hcard' : ((n + 1 : ℕ) : ℝ) * m'.u < 1) (hA : IsUnit A)
    (hx : A *ᵥ x = b) (hx0 : x ≠ 0) (hLU : RoundsLU m A L U) (hd : ∀ j, U j j ≠ 0)
    {xs : ℕ → Fin n → ℝ}
    (hstep : ∀ i, Refinement.RoundsStepLUMixed m m' A L U b (xs i) (xs (i + 1)))
    {θ ρ φ : ℝ} (hθ : θ = gamma m.u (3 * n) * ‖A⁻¹.abs * (L.abs * U.abs)‖)
    (hρ : ρ = (θ + (m.u + (1 + m.u) * gamma m'.u (n + 1)) * skeelCond A) / (1 - 2 * m.u - θ))
    (hφ : φ = (2 * (1 + m.u) * gamma m'.u (n + 1) * skeelCondAt A x + m.u * (1 + θ))
      / (1 - 2 * m.u - θ))
    (hsmall : 2 * θ + (m.u + (1 + m.u) * gamma m'.u (n + 1)) * skeelCond A + 2 * m.u < 1) :
    ρ < 1 ∧ (∀ i, ‖x - xs (i + 1)‖ / ‖x‖ ≤ ρ * (‖x - xs i‖ / ‖x‖) + φ) ∧
      (∀ k, ‖x - xs k‖ / ‖x‖ ≤ ρ ^ k * (‖x - xs 0‖ / ‖x‖) + φ / (1 - ρ)) ∧
      limsup (fun k => ‖x - xs k‖ / ‖x‖) atTop ≤ φ / (1 - ρ) ∧
      (m'.u ≤ m.u ^ 2 → 2 * ((n + 1 : ℕ) * m'.u) ≤ 1 →
        φ ≤ m.u * (1 + θ + 4 * (1 + m.u) * (n + 1) * m.u * skeelCondAt A x)
          / (1 - 2 * m.u - θ)) := by
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hφx : φ * ‖x‖ = (2 * (1 + m.u) * gamma m'.u (n + 1) * ‖A⁻¹.abs *ᵥ (A.abs *ᵥ |x|)‖
      + m.u * (1 + θ) * ‖x‖) / (1 - 2 * m.u - θ) := by
    rw [hφ, skeelCondAt, div_mul_eq_mul_div]
    congr 1
    field_simp
  obtain ⟨hρ1, hrec, -, -, hfloor⟩ := Refinement.norm_sub_le_of_forall_roundsStepLUMixed (ρ := ρ)
    (φ := φ * ‖x‖) hcard hcard' hA hx hLU hd hstep hθ (by rw [hρ, skeelCond]) hφx
    (by rw [skeelCond] at hsmall; exact hsmall)
  have hθ0 : 0 ≤ θ := by
    rw [hθ]; exact mul_nonneg (gamma_nonneg m.u_nonneg hcard) (norm_nonneg _)
  have hγ1 := gamma_nonneg m'.u_nonneg hcard'
  have hc0 : 0 ≤ skeelCond A := by rw [skeelCond]; exact norm_nonneg _
  have hcx0 := skeelCondAt_nonneg (A := A) x
  have hu0 := m.u_nonneg
  have hpos : 0 < 1 - 2 * m.u - θ := by
    have : 0 ≤ (m.u + (1 + m.u) * gamma m'.u (n + 1)) * skeelCond A := by positivity
    linarith
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hφ0 : 0 ≤ φ := by rw [hφ]; positivity
  have hrec' : ∀ i, ‖x - xs (i + 1)‖ / ‖x‖ ≤ ρ * (‖x - xs i‖ / ‖x‖) + φ :=
    div_recursion (a := fun k => ‖x - xs k‖) hxn hrec
  refine ⟨hρ1, hrec', fun k =>
    Refinement.le_pow_mul_add_div_of_forall_le_mul_add (a := fun k => ‖x - xs k‖ / ‖x‖) hρ0 hρ1
      hφ0 hrec' k,
    Refinement.limsup_le_div_of_forall_le_mul_add hρ0 hρ1 hφ0 (fun k => by positivity) hrec',
    fun hu2 hn2 => ?_⟩
  have h := hfloor hu2 hn2
  have hcx : ‖A⁻¹.abs *ᵥ (A.abs *ᵥ |x|)‖ = skeelCondAt A x * ‖x‖ := by
    rw [skeelCondAt, div_mul_cancel₀ _ hxn.ne']
  rw [hcx] at h
  have h' : φ * ‖x‖ ≤ (m.u * (1 + θ + 4 * (1 + m.u) * (n + 1) * m.u * skeelCondAt A x)
      / (1 - 2 * m.u - θ)) * ‖x‖ := by
    refine h.trans (le_of_eq ?_)
    rw [div_mul_eq_mul_div]
    congr 1
    ring
  exact le_of_mul_le_mul_right h' hxn

end FinitePrecision

end QuarteroniSaccoSaleri.Chapter03

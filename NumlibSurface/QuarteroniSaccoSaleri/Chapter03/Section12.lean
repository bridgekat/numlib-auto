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

One step of iterative refinement in floating-point arithmetic — the exact error identity, its
`∞`-norm form and its instantiation in the relational rounding model — is a general fact with no
book-specific content and lives in the backbone as `Refinement.step_error`,
`Refinement.norm_step_error_le` and `Refinement.step_error_fp`.

Example 3.10 (a numerical run), the heuristics `‖D₂⁻¹(x̂ - x)‖/‖D₂⁻¹ x‖ ≃ u K_∞(D₁ A D₂)` (which is
(3.69) for the scaled system) and `K_∞(A) ≃ β^{t(1 - 1/p)}`, and the stopping test of step 4 are
not nodes. The two finite-precision convergence factors of §3.12.2 (`ρ ≃ 2 n cond(A, x) u` for
fixed-precision and `ρ ≃ u` for mixed-precision refinement, [higham2002accuracy] Theorems
12.1–12.2) are asymptotic statements and are planned as not formalized; what is proved instead is
the rigorous one-step recursion they summarize, the backbone's `Refinement.step_error_fp`.

## Readings and errata

Remark 3.7 prints `cond(A, x) = ‖|A⁻¹| A |x| x‖_∞ / ‖x‖_∞`; it is read as
`‖|A⁻¹| |A| |x|‖_∞ / ‖x‖_∞`, the definition of [Ske79] and [higham2002accuracy] §7.2. The
convergence of iterative refinement in exact arithmetic is stated as "the iterates converge
from every `x⁽⁰⁾` to one and the same limit, for every `b`, iff `ρ(I - C A) < 1`"; the backbone's
`Refinement.forall_tendsto_iff_spectralRadius_lt_one` allows the limit to depend on the start and
needs `C` onto instead (`C = 0` is a counterexample otherwise).
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

end QuarteroniSaccoSaleri.Chapter03

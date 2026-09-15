import Numlib.FloatingPoint.LU
import Numlib.FloatingPoint.Stationary
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
* `refinementStep_error`, `norm_refinementStep_error_le`, `refinementStep_error_fp` — one step in
  floating-point arithmetic: the exact error identity, its `∞`-norm form, and the instantiation
  with the three rounding models.

Example 3.10 (a numerical run), the heuristics `‖D₂⁻¹(x̂ - x)‖/‖D₂⁻¹ x‖ ≃ u K_∞(D₁ A D₂)` (which is
(3.69) for the scaled system) and `K_∞(A) ≃ β^{t(1 - 1/p)}`, and the stopping test of step 4 are
not nodes. The two finite-precision convergence factors of §3.12.2 (`ρ ≃ 2 n cond(A, x) u` for
fixed-precision and `ρ ≃ u` for mixed-precision refinement, [higham2002accuracy] Theorems
12.1–12.2) are asymptotic statements and are planned as not formalized; what is proved here is the
rigorous one-step recursion they summarize (`refinementStep_error_fp`).

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

-- TODO(backbone): belongs in `Numlib/LinearAlgebra/Matrix/Complexify` beside
-- `Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one` (chapter 4's surface proves it too).
/-- A sequence of real matrices tends to `0` iff `M k *ᵥ v → 0` for every vector `v`. -/
private theorem tendsto_zero_iff_forall_mulVec_tendsto_zero {M : ℕ → Matrix (Fin n) (Fin n) ℝ} :
    Tendsto M atTop (𝓝 0) ↔ ∀ v, Tendsto (fun k => M k *ᵥ v) atTop (𝓝 0) := by
  constructor
  · intro h v
    have hc : Continuous fun D : Matrix (Fin n) (Fin n) ℝ => D *ᵥ v :=
      Continuous.matrix_mulVec continuous_id continuous_const
    simpa [Function.comp_def] using (hc.tendsto 0).comp h
  · intro h
    have key : Tendsto (fun k => (fun i j => M k i j : Fin n → Fin n → ℝ)) atTop
        (𝓝 (fun _ _ => (0 : ℝ))) := by
      refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
      have hsingle : ∀ k, (M k *ᵥ Pi.single j 1) i = M k i j := fun k => by simp
      simpa only [hsingle, Pi.zero_apply] using tendsto_pi_nhds.mp (h (Pi.single j 1)) i
    exact key

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

/-- **The error of one step of iterative refinement, exactly** (§3.12.2). Let `x` solve `A x = b`,
let `xhat` be the current iterate, let the computed residual be `rhat = b - A xhat + ξ`, let the
computed correction `zhat` solve the perturbed system `(A + ΔA) zhat = rhat` — which is what a
solve with the computed factors `L̂`, `Û` delivers, (3.64) — and let the computed update be
`yhat = xhat + zhat + η`. Then

`(A + ΔA) (x - yhat) = ΔA (x - xhat) - ξ - (A + ΔA) η`.

Every term on the right is small: `ΔA` is the backward error of the solve, `ξ` that of the residual
and `η` that of the update, so the new error is the old error multiplied by `(A + ΔA)⁻¹ ΔA` plus a
floor of the size of the rounding errors. This is the algebraic core of the convergence claim of
§3.12.2 and of [higham2002accuracy] Theorems 12.1–12.2.

Belongs in `Numlib/LinearSolve/Direct/Refinement.lean`; written here because this round's task did
not own that module. -/
theorem refinementStep_error {A ΔA : Matrix (Fin n) (Fin n) ℝ}
    {b x xhat zhat yhat rhat ξ η : Fin n → ℝ} (hx : A *ᵥ x = b)
    (hr : rhat = b - A *ᵥ xhat + ξ) (hz : (A + ΔA) *ᵥ zhat = rhat)
    (hy : yhat = xhat + zhat + η) :
    (A + ΔA) *ᵥ (x - yhat) = ΔA *ᵥ (x - xhat) - ξ - (A + ΔA) *ᵥ η := by
  have hr' : rhat = (A + ΔA) *ᵥ (x - xhat) - ΔA *ᵥ (x - xhat) + ξ := by
    rw [hr, ← hx, add_mulVec, mulVec_sub]
    abel
  rw [hr'] at hz
  rw [hy, show x - (xhat + zhat + η) = x - xhat - zhat - η by abel, mulVec_sub, mulVec_sub, hz]
  abel

open scoped Matrix.Norms.Operator in
/-- **The error recursion of iterative refinement, in the `∞`-norm.** With the data of
`refinementStep_error` and `A + ΔA` nonsingular,

`‖x - yhat‖_∞ ≤ ‖(A + ΔA)⁻¹ ΔA‖_∞ ‖x - xhat‖_∞ + ‖(A + ΔA)⁻¹‖_∞ ‖ξ‖_∞ + ‖η‖_∞`:

the error is reduced by the factor `‖(A + ΔA)⁻¹ ΔA‖_∞` down to a floor set by the residual and
update roundings. With `|ΔA| ≤ γ_{3n} |L̂| |Û|` from (3.64) the factor is at most
`γ_{3n} ‖ |(A + ΔA)⁻¹| |L̂| |Û| ‖_∞`, which is the quantity the book asks to be "sufficiently
small", with `(A + ΔA)⁻¹` in place of `A⁻¹`.

Belongs in `Numlib/LinearSolve/Direct/Refinement.lean`. -/
theorem norm_refinementStep_error_le {A ΔA : Matrix (Fin n) (Fin n) ℝ}
    {b x xhat zhat yhat rhat ξ η : Fin n → ℝ} (hinv : IsUnit (A + ΔA).det) (hx : A *ᵥ x = b)
    (hr : rhat = b - A *ᵥ xhat + ξ) (hz : (A + ΔA) *ᵥ zhat = rhat) (hy : yhat = xhat + zhat + η) :
    ‖x - yhat‖ ≤ ‖(A + ΔA)⁻¹ * ΔA‖ * ‖x - xhat‖ + ‖(A + ΔA)⁻¹‖ * ‖ξ‖ + ‖η‖ := by
  have hid := refinementStep_error hx hr hz hy
  have hsol : x - yhat = ((A + ΔA)⁻¹ * ΔA) *ᵥ (x - xhat) - (A + ΔA)⁻¹ *ᵥ ξ - η := by
    have h1 : (A + ΔA) *ᵥ (x - yhat + η) = ΔA *ᵥ (x - xhat) - ξ := by
      rw [mulVec_add, hid]; abel
    have h2 := congrArg (fun v => (A + ΔA)⁻¹ *ᵥ v) h1
    simp only [mulVec_mulVec, nonsing_inv_mul _ hinv, one_mulVec, mulVec_sub] at h2
    rw [show x - yhat = x - yhat + η - η by abel, h2, mulVec_sub]
  calc ‖x - yhat‖ = ‖((A + ΔA)⁻¹ * ΔA) *ᵥ (x - xhat) - (A + ΔA)⁻¹ *ᵥ ξ - η‖ := by rw [hsol]
    _ ≤ ‖((A + ΔA)⁻¹ * ΔA) *ᵥ (x - xhat) - (A + ΔA)⁻¹ *ᵥ ξ‖ + ‖η‖ := norm_sub_le _ _
    _ ≤ ‖((A + ΔA)⁻¹ * ΔA) *ᵥ (x - xhat)‖ + ‖(A + ΔA)⁻¹ *ᵥ ξ‖ + ‖η‖ := by
        gcongr
        exact norm_sub_le _ _
    _ ≤ ‖(A + ΔA)⁻¹ * ΔA‖ * ‖x - xhat‖ + ‖(A + ΔA)⁻¹‖ * ‖ξ‖ + ‖η‖ := by
        gcongr <;> exact linfty_opNorm_mulVec _ _


open FloatingPoint in
/-- **One step of iterative refinement in floating-point arithmetic** (§3.12.2, steps 1–3), with
the three backward errors named. The residual is computed as an affine step
(`FloatingPoint.RoundsAffineStep m (-A) b xhat rhat`), the correction by a solve with the computed
factors `L`, `U` of `A` (`FloatingPoint.RoundsLU` and the two substitutions), and the update
entrywise. Then there are `ΔA`, `ξ`, `η` with

`|ΔA| ≤ γ_{3n} |L| |U|`, `|ξ| ≤ γ_{n+1} (|A| |xhat| + |b|)`, `|η_i| ≤ u |xhat_i + zhat_i|`

satisfying the error identity of `refinementStep_error`. This is the rigorous content behind the
asymptotic convergence factors `ρ ≃ 2n cond(A, x) u` and `ρ ≃ u` that §3.12.2 quotes; see the plan
nodes `iterativeRefinement_fixedPrecision` and `iterativeRefinement_mixedPrecision` for what
separates it from them.

Belongs in `Numlib/LinearSolve/Direct/Refinement.lean` once that module may import
`Numlib/FloatingPoint/LU`. -/
theorem refinementStep_error_fp [NeZero n] {m : RoundingModel ℝ} (hu : m.u < 1)
    (hcard : ((3 * n : ℕ) : ℝ) * m.u < 1) {A L U : Matrix (Fin n) (Fin n) ℝ}
    {b x xhat rhat y zhat yhat : Fin n → ℝ} (hx : A *ᵥ x = b)
    (hres : RoundsAffineStep m (-A) b xhat rhat) (hLU : RoundsLU m A L U) (hd : ∀ j, U j j ≠ 0)
    (hfwd : RoundsForwardSubst m L rhat y) (hbck : RoundsBackSubst m U y zhat)
    (hupd : ∀ i, m.Rounds (xhat i + zhat i) (yhat i)) :
    ∃ ΔA : Matrix (Fin n) (Fin n) ℝ, ∃ ξ η : Fin n → ℝ,
      ΔA.abs ≤ₑ gamma m.u (3 * n) • (L.abs * U.abs) ∧
        |ξ| ≤ gamma m.u (n + 1) • (A.abs *ᵥ |xhat| + |b|) ∧
        (∀ i, |η i| ≤ m.u * |xhat i + zhat i|) ∧
        (A + ΔA) *ᵥ (x - yhat) = ΔA *ᵥ (x - xhat) - ξ - (A + ΔA) *ᵥ η := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  have hcard' : ((Fintype.card (Fin n) + 1 : ℕ) : ℝ) * m.u < 1 := by
    have h1 : ((Fintype.card (Fin n) + 1 : ℕ) : ℝ) ≤ ((3 * n : ℕ) : ℝ) := by
      simp only [Fintype.card_fin]
      push_cast
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    nlinarith [m.u_nonneg]
  have hcard3 : ((3 * Fintype.card (Fin n) : ℕ) : ℝ) * m.u < 1 := by
    simpa [Fintype.card_fin] using hcard
  obtain ⟨ξ, hξeq, hξle⟩ := exists_roundsAffineStep_eq_add hu hcard' hres
  obtain ⟨ΔA, hΔA, hsolve⟩ := exists_roundsLU_solve_eq hu hcard3 hLU hd hfwd hbck
  refine ⟨ΔA, ξ, yhat - (xhat + zhat), by simpa [Fintype.card_fin] using hΔA, ?_,
    fun i => by simpa using m.abs_sub_le (hupd i), ?_⟩
  · have habs : (-A).abs = A.abs := by ext i j; simp
    simpa [Fintype.card_fin, habs] using hξle
  · refine refinementStep_error hx ?_ hsolve (by ext i; simp)
    rw [hξeq, neg_mulVec]
    abel

end QuarteroniSaccoSaleri.Chapter03

import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.Analysis.Matrix.SpectralNorm
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.Stationary.Basic

/-!
# Quarteroni–Sacco–Saleri §4.1: on the convergence of iterative methods

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §4.1, over the backbone `Numlib/Stationary/Basic` (the affine
iteration `x ↦ G x + f` on a normed space, its error propagation, and the convergence factors and
rates), `Numlib/LinearAlgebra/Matrix/Complexify` (the spectral radius `Matrix.complexSpectralRadius`
of a real matrix and the equivalence `Bᵏ → 0 ⟺ ρ(B) < 1`) and `Numlib/Analysis/Matrix/SpectralNorm`
(the spectral norm of a symmetric matrix).

## Conventions

The book's linear iterative method (4.2), `x⁽ᵏ⁺¹⁾ = B x⁽ᵏ⁾ + f` on `ℝⁿ`, is `affineStep B f` on
`Fin n → ℝ`, and its `k`-th iterate from `x⁽⁰⁾` is `(affineStep B f)^[k] x⁽⁰⁾`. Under
`WithLp.toLp 2` it is the backbone's `Stationary.step` of the operator `Matrix.toEuclideanCLM B` on
`EuclideanSpace ℝ (Fin n)` (`toLp_affineStep`, `toLp_affineStep_iterate`), which is how every
backbone statement is transported. The solution of the system `A x = b` of (3.2) is written
`A⁻¹ *ᵥ b` with Mathlib's junk-valued inverse; the book's standing assumption that `A` is
nonsingular is therefore carried by the statements that need it and omitted from those that hold
as written without it. Matrix norms are the spectral norm `‖·‖₂` (Mathlib's scoped
`Matrix.Norms.L2Operator`), the book's "any matrix norm" of Definition 4.2 being fixed to the
Euclidean one; the spectral radius of a real matrix is `Matrix.complexSpectralRadius`,
`ℝ≥0∞`-valued, and its real value is `.toReal`.

## Contents

* `affineStep`, `toLp_affineStep`, `toLp_affineStep_iterate` — the method (4.2) and its transport.
* `definition_4_1`, `definition_4_1_iff`, `toLp_fixed_of_consistent` — consistency and its
  "equivalently".
* `example_4_1_consistent`, `example_4_1_iterate`, `example_4_1_not_tendsto`,
  `example_4_1_tendsto` — Example 4.1.
* `equation_4_4`, `affineStep_iterate_sub_iterate`,
  `complexSpectralRadius_lt_one_of_forall_tendsto`, `theorem_4_1`,
  `tendsto_of_algebraNorm_lt_one` — the error recursion, the convergence theorem and the
  sufficient condition `‖B‖ < 1`.
* `definition_4_2_factor`, `definition_4_2_averageFactor`, `definition_4_2_rate`,
  `definition_4_2_eq`, `asymptoticConvergenceRate`, `equation_4_5`, `equation_4_5_factor`,
  `equation_4_5_symm` — Definition 4.2 and the asymptotic rate (4.5).
* `exercise_4_1` — Exercise 1, cited after Definition 4.2 (the spectral radius of a matrix with a
  single real eigenvalue is `Matrix.complexSpectralRadius_eq_of_forall_mem_spectrum_iff`).

Remark 4.1 (order, stationarity and linearity of a general iteration) is a classification and
has no node.

## Readings

Theorem 4.1 and (4.4) are stated for a consistent method without assuming `A` nonsingular: with
Mathlib's `A⁻¹ = 0` for a singular `A`, consistency then reads `f = 0` and the statements remain
true. The book proves the converse of Theorem 4.1 through an eigenvector of modulus `> 1` and
leaves the case `ρ(B) = 1` unmentioned; both are subsumed by the equivalence `Bᵏ → 0 ⟺ ρ(B) < 1`
of Theorem 1.5. The symmetric case of (4.5) holds for every `m ≥ 1` with no condition on `ρ(B)`,
since `Real.log 0 = 0` makes both sides vanish for a nilpotent (hence zero) symmetric `B`.
-/

open Filter Finset Matrix Topology WithLp
open scoped ENNReal NNReal

namespace QuarteroniSaccoSaleri.Chapter04

variable {n : ℕ}

/-! ### The linear iterative method (4.2) -/

/-- **(4.2).** One step `x ↦ B x + f` of the linear iterative method `x⁽ᵏ⁺¹⁾ = B x⁽ᵏ⁾ + f`, for
the iteration matrix `B ∈ ℝ^{n×n}` and the vector `f` obtained from the right-hand side; the
`k`-th iterate from `x⁽⁰⁾` is `(affineStep B f)^[k] x⁽⁰⁾`. It is the backbone's `Stationary.step`
of the operator `Matrix.toEuclideanCLM B` read on plain functions (`toLp_affineStep`). -/
def affineStep (B : Matrix (Fin n) (Fin n) ℝ) (f x : Fin n → ℝ) : Fin n → ℝ := B *ᵥ x + f

/-- Under `WithLp.toLp 2`, the step (4.2) is `Stationary.step` of `Matrix.toEuclideanCLM B` on
`EuclideanSpace ℝ (Fin n)`: the transport through which the theory of `Numlib/Stationary/Basic`
applies to the book's iteration. -/
theorem toLp_affineStep (B : Matrix (Fin n) (Fin n) ℝ) (f x : Fin n → ℝ) :
    (toLp 2 (affineStep B f x) : EuclideanSpace ℝ (Fin n)) =
      Stationary.step (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B) (toLp 2 f) (toLp 2 x) := rfl

/-- The `k`-th iterate of (4.2) under `WithLp.toLp 2` is the `k`-th iterate of the backbone step. -/
theorem toLp_affineStep_iterate (B : Matrix (Fin n) (Fin n) ℝ) (f x₀ : Fin n → ℝ) (k : ℕ) :
    (toLp 2 ((affineStep B f)^[k] x₀) : EuclideanSpace ℝ (Fin n)) =
      (Stationary.step (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B) (toLp 2 f))^[k] (toLp 2 x₀) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]; rfl

/-! ### Definition 4.1 and Example 4.1 -/

/-- **Definition 4.1.** The iterative method (4.2) is *consistent* with the system `A x = b` when
`f` and `B` are such that `x = B x + f` for its solution `x = A⁻¹ b`: the solution is a fixed point
of the step `affineStep B f`. Meaningful for `A` nonsingular, the standing assumption of §3.2;
`definition_4_1_iff` is the "equivalently, `f = (I - B) A⁻¹ b`". -/
def definition_4_1 (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (f : Fin n → ℝ) : Prop :=
  A⁻¹ *ᵥ b = B *ᵥ (A⁻¹ *ᵥ b) + f

/-- **Definition 4.1, "equivalently"**: the method is consistent iff `f = (I - B) A⁻¹ b`. A
rearrangement, valid for every `A`. -/
theorem definition_4_1_iff (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → ℝ) :
    definition_4_1 A b B f ↔ f = (1 - B) *ᵥ (A⁻¹ *ᵥ b) := by
  rw [definition_4_1, sub_mulVec, one_mulVec]
  exact ⟨fun h => eq_sub_of_add_eq' h.symm, fun h => (add_eq_of_eq_sub' h).symm⟩

/-- The solution of a consistent method is a fixed point of the backbone step: Definition 4.1
under `WithLp.toLp 2`, in the form `hfix` that the lemmas of `Numlib/Stationary/Basic` take. -/
theorem toLp_fixed_of_consistent {A B : Matrix (Fin n) (Fin n) ℝ} {b f : Fin n → ℝ}
    (hc : definition_4_1 A b B f) :
    toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B (toLp 2 (A⁻¹ *ᵥ b)) + toLp 2 f =
      (toLp 2 (A⁻¹ *ᵥ b) : EuclideanSpace ℝ (Fin n)) := by
  rw [toEuclideanCLM_toLp, ← toLp_add, ← hc]

/-- `(2 I)⁻¹ b = b / 2`, the solution of the system of Example 4.1. -/
private theorem inv_two_smul_one_mulVec (b : Fin n → ℝ) :
    ((2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹ *ᵥ b = (1 / 2 : ℝ) • b := by
  have h : ((2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹ = (1 / 2 : ℝ) • 1 := by
    refine inv_eq_left_inv ?_
    rw [smul_mul_smul_comm, one_mul]
    norm_num
  rw [h, smul_mulVec, one_mulVec]

/-- **Example 4.1, consistency.** To solve `2 I x = b`, the method `x⁽ᵏ⁺¹⁾ = -x⁽ᵏ⁾ + b` (that is,
`B = -I`, `f = b`) is consistent: `b/2 = -(b/2) + b`. -/
theorem example_4_1_consistent (b : Fin n → ℝ) :
    definition_4_1 ((2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) b (-1) b := by
  rw [definition_4_1, inv_two_smul_one_mulVec, neg_mulVec, one_mulVec]
  module

/-- **Example 4.1, the iterates from `x⁽⁰⁾ = 0`.** The method generates `x⁽²ᵏ⁾ = 0` and
`x⁽²ᵏ⁺¹⁾ = b` for every `k`. -/
theorem example_4_1_iterate (b : Fin n → ℝ) (k : ℕ) :
    (affineStep (-1) b)^[2 * k] 0 = 0 ∧ (affineStep (-1) b)^[2 * k + 1] 0 = b := by
  have h1 : ∀ x, affineStep (-1 : Matrix (Fin n) (Fin n) ℝ) b x = -x + b := fun x => by
    rw [affineStep, neg_mulVec, one_mulVec]
  induction k with
  | zero => simp [h1]
  | succ k ih =>
    obtain ⟨ih0, ih1⟩ := ih
    have h2 : (affineStep (-1 : Matrix (Fin n) (Fin n) ℝ) b)^[2 * (k + 1)] 0 = 0 := by
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Function.iterate_succ_apply', ih1, h1]
      abel
    refine ⟨h2, ?_⟩
    rw [Function.iterate_succ_apply', h2, h1]
    abel

/-- **Example 4.1, non-convergence.** For `b ≠ 0` the sequence started at `x⁽⁰⁾ = 0` has no limit:
its even terms are `0` and its odd terms are `b`. Consistency alone does not give convergence. -/
theorem example_4_1_not_tendsto {b : Fin n → ℝ} (hb : b ≠ 0) :
    ¬ ∃ x, Tendsto (fun k => (affineStep (-1) b)^[k] 0) atTop (𝓝 x) := by
  rintro ⟨x, hx⟩
  have h2 : Tendsto (fun k : ℕ => 2 * k) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_mul_of_pos_left k two_pos) tendsto_id
  have h3 : Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_succ _) h2
  have heven : Tendsto (fun k => (affineStep (-1 : Matrix (Fin n) (Fin n) ℝ) b)^[2 * k] 0) atTop
      (𝓝 x) :=
    hx.comp h2
  have hodd : Tendsto (fun k => (affineStep (-1 : Matrix (Fin n) (Fin n) ℝ) b)^[2 * k + 1] 0) atTop
      (𝓝 x) :=
    hx.comp h3
  simp only [fun k => (example_4_1_iterate b k).1] at heven
  simp only [fun k => (example_4_1_iterate b k).2] at hodd
  exact hb ((tendsto_nhds_unique hodd tendsto_const_nhds).symm.trans
    (tendsto_nhds_unique heven tendsto_const_nhds))

/-- **Example 4.1, convergence from `x⁽⁰⁾ = b/2`.** Started at the solution the method is
stationary, `x⁽ᵏ⁾ = b/2` for all `k`, hence convergent. -/
theorem example_4_1_tendsto (b : Fin n → ℝ) :
    (∀ k, (affineStep (-1) b)^[k] ((1 / 2 : ℝ) • b) = (1 / 2 : ℝ) • b) ∧
      Tendsto (fun k => (affineStep (-1) b)^[k] ((1 / 2 : ℝ) • b)) atTop (𝓝 ((1 / 2 : ℝ) • b)) := by
  have hfix : affineStep (-1 : Matrix (Fin n) (Fin n) ℝ) b ((1 / 2 : ℝ) • b) = (1 / 2 : ℝ) • b := by
    rw [affineStep, neg_mulVec, one_mulVec]
    module
  have h : ∀ k, (affineStep (-1 : Matrix (Fin n) (Fin n) ℝ) b)^[k] ((1 / 2 : ℝ) • b)
      = (1 / 2 : ℝ) • b := fun k => Function.iterate_fixed hfix k
  refine ⟨h, ?_⟩
  simp only [h]
  exact tendsto_const_nhds

/-! ### Theorem 4.1 -/

/-- **(4.4).** For a consistent method, the error `e⁽ᵏ⁾ = x⁽ᵏ⁾ - x` obeys `e⁽ᵏ⁺¹⁾ = B e⁽ᵏ⁾`, hence
`e⁽ᵏ⁾ = Bᵏ e⁽⁰⁾` for all `k`; here `x = A⁻¹ b`. It is the backbone's `Stationary.step_iterate_sub`
transported along `toLp_affineStep_iterate`. -/
theorem equation_4_4 {A B : Matrix (Fin n) (Fin n) ℝ} {b f : Fin n → ℝ}
    (hc : definition_4_1 A b B f) (x₀ : Fin n → ℝ) (k : ℕ) :
    (affineStep B f)^[k] x₀ - A⁻¹ *ᵥ b = (B ^ k) *ᵥ (x₀ - A⁻¹ *ᵥ b) := by
  have h := Stationary.step_iterate_sub (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B) (toLp 2 f)
    (toLp_fixed_of_consistent hc) (toLp 2 x₀) k
  rw [← toLp_affineStep_iterate, ← map_pow, ← toLp_sub, ← toLp_sub, toEuclideanCLM_toLp] at h
  exact toLp_injective 2 h

/-- **Two iterations of (4.2) drift apart by `Bᵏ` applied to their initial difference**:
`x⁽ᵏ⁾ - y⁽ᵏ⁾ = Bᵏ (x⁽⁰⁾ - y⁽⁰⁾)`, no fixed point needed; the difference of two instances of the
closed form `Stationary.step_iterate_eq_pow_add_sum`. It is what makes "convergence for every
`x⁽⁰⁾`" force `Bᵏ → 0` whatever the limit is. -/
theorem affineStep_iterate_sub_iterate (B : Matrix (Fin n) (Fin n) ℝ) (f x₀ y₀ : Fin n → ℝ)
    (k : ℕ) :
    (affineStep B f)^[k] x₀ - (affineStep B f)^[k] y₀ = (B ^ k) *ᵥ (x₀ - y₀) := by
  have hx := Stationary.step_iterate_eq_pow_add_sum (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B)
    (toLp 2 f) (toLp 2 x₀) k
  have hy := Stationary.step_iterate_eq_pow_add_sum (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B)
    (toLp 2 f) (toLp 2 y₀) k
  rw [← toLp_affineStep_iterate] at hx hy
  have h := congrArg₂ (· - ·) hx hy
  simp only [add_sub_add_right_eq_sub, ← map_pow, ← toLp_sub, toEuclideanCLM_toLp, ← mulVec_sub]
    at h
  exact toLp_injective 2 h

/-- **Theorem 4.1, the necessity of `ρ(B) < 1`**, in the form the book's argument proves: if the
iteration (4.2) converges from every `x⁽⁰⁾` (to any limit `x`, the same for all starting vectors)
then `ρ(B) < 1`, because the differences `x⁽ᵏ⁾ - y⁽ᵏ⁾ = Bᵏ (x⁽⁰⁾ - y⁽⁰⁾)` tend to `0`, so `Bᵏ v → 0`
for every `v` (Theorem 1.5). No consistency is needed for this direction. -/
theorem complexSpectralRadius_lt_one_of_forall_tendsto {B : Matrix (Fin n) (Fin n) ℝ}
    {f x : Fin n → ℝ} (h : ∀ x₀, Tendsto (fun k => (affineStep B f)^[k] x₀) atTop (𝓝 x)) :
    complexSpectralRadius B < 1 := by
  rw [← tendsto_pow_iff_complexSpectralRadius_lt_one,
    tendsto_zero_iff_forall_mulVec_tendsto_zero]
  intro v
  have hv := (h v).sub (h 0)
  rw [sub_self] at hv
  simpa only [affineStep_iterate_sub_iterate, sub_zero] using hv

/-- **Theorem 4.1.** Let (4.2) be consistent with `A x = b`. Then the sequence `x⁽ᵏ⁾` converges to
the solution `x = A⁻¹ b` for every choice of `x⁽⁰⁾` iff `ρ(B) < 1`. By (4.4) the errors are
`Bᵏ e⁽⁰⁾`, and `Bᵏ v → 0` for every `v` iff `Bᵏ → 0` iff `ρ(B) < 1` (Theorem 1.5, backbone
`Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one`). The book's converse through an eigenvector
of modulus `> 1`, and the case `ρ(B) = 1` it leaves out, are subsumed by that equivalence
(`complexSpectralRadius_lt_one_of_forall_tendsto`). -/
theorem theorem_4_1 {A B : Matrix (Fin n) (Fin n) ℝ} {b f : Fin n → ℝ}
    (hc : definition_4_1 A b B f) :
    (∀ x₀, Tendsto (fun k => (affineStep B f)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b))) ↔
      complexSpectralRadius B < 1 := by
  refine ⟨complexSpectralRadius_lt_one_of_forall_tendsto, fun h x₀ => ?_⟩
  rw [← tendsto_pow_iff_complexSpectralRadius_lt_one,
    tendsto_zero_iff_forall_mulVec_tendsto_zero] at h
  rw [← tendsto_sub_nhds_zero_iff]
  simpa only [equation_4_4 hc] using h (x₀ - A⁻¹ *ᵥ b)

/-- **The remark after Theorem 4.1.** A sufficient condition for convergence is `‖B‖ < 1` for any
matrix norm — here any algebra norm `N` on `ℝ^{n×n}`, by (1.23) and Theorem 1.5: the powers of `B`
then tend to `0` (backbone `Matrix.tendsto_pow_of_algebraNorm_lt_one`), so `ρ(B) < 1` and
Theorem 4.1 applies. -/
theorem tendsto_of_algebraNorm_lt_one {A B : Matrix (Fin n) (Fin n) ℝ} {b f : Fin n → ℝ}
    (hc : definition_4_1 A b B f) (N : AlgebraNorm ℝ (Matrix (Fin n) (Fin n) ℝ)) (hN : N B < 1)
    (x₀ : Fin n → ℝ) :
    Tendsto (fun k => (affineStep B f)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b)) :=
  (theorem_4_1 hc).2
    ((tendsto_pow_iff_complexSpectralRadius_lt_one B).1 (tendsto_pow_of_algebraNorm_lt_one N hN))
    x₀

/-! ### Definition 4.2 and the asymptotic convergence rate (4.5) -/

section ConvergenceFactor

open scoped Matrix.Norms.L2Operator

/-- **Definition 4.2 (1).** The *convergence factor after `m` steps* of the iteration with matrix
`B` is `‖Bᵐ‖`, in the spectral norm. It bounds the error reduction over `m` steps, `‖e⁽ᵐ⁾‖ ≤
‖Bᵐ‖ ‖e⁽⁰⁾‖` (§4.6). -/
noncomputable def definition_4_2_factor (B : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) : ℝ := ‖B ^ m‖

/-- **Definition 4.2 (2).** The *average convergence factor after `m` steps* is `‖Bᵐ‖^{1/m}`. -/
noncomputable def definition_4_2_averageFactor (B : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) : ℝ :=
  ‖B ^ m‖ ^ (1 / m : ℝ)

/-- **Definition 4.2 (3).** The *average convergence rate after `m` steps* is
`R_m(B) = -(1/m) log ‖Bᵐ‖`. -/
noncomputable def definition_4_2_rate (B : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) : ℝ :=
  -(1 / m : ℝ) * Real.log ‖B ^ m‖

/-- The three quantities of Definition 4.2 are the backbone's `Stationary.convergenceFactor`,
`Stationary.averageConvergenceFactor` and `Stationary.averageConvergenceRate` of the operator
`Matrix.toEuclideanCLM B`, whose operator norm is the spectral norm of `B`
(`Matrix.l2_opNorm_toEuclideanCLM`). -/
theorem definition_4_2_eq (B : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) :
    definition_4_2_factor B m =
        Stationary.convergenceFactor (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B) m ∧
      definition_4_2_averageFactor B m =
        Stationary.averageConvergenceFactor (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B) m ∧
      definition_4_2_rate B m =
        Stationary.averageConvergenceRate (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B) m := by
  simp only [definition_4_2_factor, definition_4_2_averageFactor, definition_4_2_rate,
    Stationary.convergenceFactor, Stationary.averageConvergenceFactor,
    Stationary.averageConvergenceRate, ← map_pow, l2_opNorm_toEuclideanCLM]
  exact ⟨trivial, trivial, trivial⟩

/-- **The asymptotic convergence rate** `R(B) = -log ρ(B)` of (4.5), the limit of the average
convergence rates `R_k(B)` (`equation_4_5`). -/
noncomputable def asymptoticConvergenceRate (B : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  -Real.log (complexSpectralRadius B).toReal

/-- **(4.5).** `R(B) = lim_{k → ∞} R_k(B) = -log ρ(B)`, "where Property 1.13 has been accounted
for": Gelfand's formula `‖Bᵏ‖^{1/k} → ρ(B)` composed with the logarithm, for `ρ(B) ≠ 0` (backbone
`Matrix.tendsto_averageConvergenceRate`). For a nilpotent `B` the book's rate is `+∞` and the
formal `R_k(B)` are `0`. -/
theorem equation_4_5 {B : Matrix (Fin n) (Fin n) ℝ} (hρ : complexSpectralRadius B ≠ 0) :
    Tendsto (definition_4_2_rate B) atTop (𝓝 (asymptoticConvergenceRate B)) :=
  tendsto_averageConvergenceRate B hρ

/-- **(4.5), the closing remark**: `ρ(B)` is the *asymptotic convergence factor*, the limit of the
average convergence factors `‖Bᵐ‖^{1/m}` (Property 1.14, backbone
`Matrix.tendsto_pow_rpow_complexSpectralRadius`). -/
theorem equation_4_5_factor (B : Matrix (Fin n) (Fin n) ℝ) :
    Tendsto (definition_4_2_averageFactor B) atTop (𝓝 (complexSpectralRadius B).toReal) :=
  tendsto_pow_rpow_complexSpectralRadius B

/-- **(4.5), the symmetric case.** If `B` is symmetric then `R_m(B) = -(1/m) log ‖Bᵐ‖₂ = -log ρ(B)`
for every `m ≥ 1`, because `‖Bᵐ‖₂ = ‖B‖₂ᵐ = ρ(B)ᵐ` (backbone `Matrix.IsHermitian.l2_opNorm_pow`
and `Matrix.l2_opNorm_eq_complexSpectralRadius_of_isHermitian`). -/
theorem equation_4_5_symm {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsSymm) {m : ℕ} (hm : m ≠ 0) :
    definition_4_2_rate B m = asymptoticConvergenceRate B := by
  have hB' : B.IsHermitian := isHermitian_iff_isSymm.mpr hB
  rw [definition_4_2_rate, asymptoticConvergenceRate, hB'.l2_opNorm_pow hm,
    l2_opNorm_eq_complexSpectralRadius_of_isHermitian hB', Real.log_pow]
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  field_simp

/-- The spectrum of the complexification of a real `2 × 2` matrix, read off its characteristic
polynomial `λ² - tr(B) λ + det B`. -/
private theorem mem_spectrum_complexify_fin_two (B : Matrix (Fin 2) (Fin 2) ℝ) (μ : ℂ) :
    μ ∈ spectrum ℂ (complexify B) ↔ μ ^ 2 - B.trace * μ + B.det = 0 := by
  rw [mem_spectrum_complexify_iff, charpoly_fin_two, Polynomial.IsRoot.def]
  simp

/-- **Exercise 1** (cited after Definition 4.2 for the non-monotone convergence of `‖Bᵐ‖`). For
`B = [[a, 4], [0, a]]` with `0 < a < 1`, the spectral radius is `ρ(B) = a < 1` (the characteristic
polynomial is `(λ - a)²`), while the average convergence factor can exceed `1`: already for `m = 1`,
`‖B‖₂ ≥ |b₁₂| = 4 > 1`. -/
theorem exercise_4_1 {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    complexSpectralRadius (!![a, 4; 0, a] : Matrix (Fin 2) (Fin 2) ℝ) = ENNReal.ofReal a ∧
      complexSpectralRadius (!![a, 4; 0, a] : Matrix (Fin 2) (Fin 2) ℝ) < 1 ∧
      1 < definition_4_2_averageFactor (!![a, 4; 0, a] : Matrix (Fin 2) (Fin 2) ℝ) 1 := by
  set B : Matrix (Fin 2) (Fin 2) ℝ := !![a, 4; 0, a] with hB
  have hspec : ∀ μ : ℂ, μ ∈ spectrum ℂ (complexify B) ↔ μ = a := by
    intro μ
    rw [mem_spectrum_complexify_fin_two]
    simp only [hB, trace_fin_two_of, det_fin_two_of, mul_zero, sub_zero]
    push_cast
    constructor
    · intro h
      have h' : (μ - a) ^ 2 = 0 := by linear_combination h
      exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h')
    · rintro rfl
      ring
  have hρ : complexSpectralRadius B = ENNReal.ofReal a := by
    rw [complexSpectralRadius_eq_of_forall_mem_spectrum_iff hspec, abs_of_pos ha0]
  refine ⟨hρ, by rw [hρ]; exact ENNReal.ofReal_lt_one.mpr ha1, ?_⟩
  rw [definition_4_2_averageFactor, pow_one, Nat.cast_one, div_one, Real.rpow_one]
  have h4 : ‖B 0 1‖ ≤ ‖B‖ := norm_entry_le_l2_opNorm B 0 1
  have hB01 : ‖B 0 1‖ = 4 := by simp [hB]
  linarith

end ConvergenceFactor

end QuarteroniSaccoSaleri.Chapter04

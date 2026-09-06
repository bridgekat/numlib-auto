import Mathlib.Analysis.SpecificLimits.Basic
import Numlib.FloatingPoint.InnerProduct
import Numlib.LinearSolve.Stationary.Basic

/-!
# Stationary iterations in finite precision

A stationary iteration `x ↦ G x + c` run in floating-point arithmetic is the exact iteration
perturbed at every step, and its accuracy is limited by the size of that perturbation rather than by
the number of steps. This module separates the two halves of [higham2002accuracy] Theorem 17.1
[higham2002accuracy].

* `Stationary.norm_perturbed_iterate_sub_le` is the exact-arithmetic half, and knows nothing about
  rounding: a sequence obeying `x_{k+1} = G x_k + f + ξ_k` with `‖ξ_k‖ ≤ ε` and `‖G‖ < 1` stays
  within `‖G‖^k ‖x_0 - x'‖ + ε / (1 - ‖G‖)` of the fixed point `x'`. The first term dies and the
  second does not: `Stationary.limsup_norm_perturbed_iterate_sub_le` is the *limiting accuracy* `ε /
  (1 - ‖G‖)`, which is what the theorem is about.
* `FloatingPoint.exists_roundsAffineStep_eq_add` is the finite-precision half: one computed step,
  formed as a matrix–vector product followed by a rounded addition, is the exact step plus a
  perturbation bounded entrywise by `γ_{n+1} (|G| |x| + |c|)`, which is [higham2002accuracy]
  (17.5)–(17.6).

The two meet at `‖ξ_k‖ ≤ ε`, which needs a norm; the finite-precision half is stated over an
abstract ordered field, in the entrywise order of `Numlib/LinearAlgebra/Matrix/Order.lean`, and
`FloatingPoint.abs_sub_le_of_roundsMulVec_of_abs_le` of `Numlib/FloatingPoint/InnerProduct.lean` is
the row-sum form for a reader who wants the `∞`-norm shape without instantiating at `ℝ`.

The splitting form of the computed step — `M x_{k+1} = N x_k + b` with `M` triangular, solved by
substitution — is **not** covered, and the reason is that a model of substitution is missing:
`Numlib/FloatingPoint/InnerProduct.lean` has recursive summation, inner products and matrix
products, but no triangular solve, so there is nothing to bound the error of the solve with. The
affine form here covers every splitting whose iteration operator has already been formed, which is
the form the exact-arithmetic half consumes.
-/

open scoped Matrix

namespace Stationary

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **The error of a perturbed stationary iteration.** If `x_{k+1} = G x_k + f + ξ_k` with `‖ξ_k‖ ≤
ε`, if `‖G‖ < 1` and if `x'` is a fixed point of the unperturbed step, then

`‖x_k - x'‖ ≤ ‖G‖ ^ k ‖x_0 - x'‖ + ε / (1 - ‖G‖)`.

This is the exact-arithmetic core of [higham2002accuracy] Theorem 17.1: the transient decays
geometrically and the perturbation contributes the *limiting accuracy* `ε / (1 - ‖G‖)`
(`Stationary.limsup_norm_perturbed_iterate_sub_le`).

Reference: [higham2002accuracy], Theorem 17.1. -/
theorem norm_perturbed_iterate_sub_le {G : E →L[𝕜] E} {f : E} {x ξ : ℕ → E}
    (hstep : ∀ k, x (k + 1) = G (x k) + f + ξ k) {ε : ℝ} (hξ : ∀ k, ‖ξ k‖ ≤ ε) (hG : ‖G‖ < 1)
    {x' : E} (hfix : G x' + f = x') (k : ℕ) :
    ‖x k - x'‖ ≤ ‖G‖ ^ k * ‖x 0 - x'‖ + ε / (1 - ‖G‖) := by
  have hq0 : (0 : ℝ) ≤ ‖G‖ := norm_nonneg _
  have hpos : (0 : ℝ) < 1 - ‖G‖ := by linarith
  have hε : (0 : ℝ) ≤ ε := le_trans (norm_nonneg _) (hξ 0)
  have hrec : ∀ j, ‖x (j + 1) - x'‖ ≤ ‖G‖ * ‖x j - x'‖ + ε := by
    intro j
    have hsplit : x (j + 1) - x' = G (x j - x') + ξ j :=
      calc x (j + 1) - x' = G (x j) + f + ξ j - (G x' + f) := by rw [hstep j, hfix]
        _ = G (x j) - G x' + ξ j := by abel
        _ = G (x j - x') + ξ j := by rw [map_sub]
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add (G.le_opNorm _) (hξ j))
  induction k with
  | zero =>
    rw [pow_zero, one_mul]
    have : (0 : ℝ) ≤ ε / (1 - ‖G‖) := div_nonneg hε hpos.le
    linarith
  | succ k ih =>
    refine (hrec k).trans ?_
    have h1 : ‖G‖ * ‖x k - x'‖
        ≤ ‖G‖ * (‖G‖ ^ k * ‖x 0 - x'‖) + ‖G‖ * (ε / (1 - ‖G‖)) := by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left ih hq0
    have h2 : ‖G‖ * (ε / (1 - ‖G‖)) + ε = ε / (1 - ‖G‖) := by
      field_simp
      ring
    have h3 : ‖G‖ * (‖G‖ ^ k * ‖x 0 - x'‖) = ‖G‖ ^ (k + 1) * ‖x 0 - x'‖ := by ring
    linarith

/-- **The limiting accuracy of a perturbed stationary iteration**, [higham2002accuracy] Theorem
17.1: the error of a contracting iteration perturbed by at most `ε` at every step is asymptotically
at most `ε / (1 - ‖G‖)`, however many steps are taken.

Reference: [higham2002accuracy], Theorem 17.1. -/
theorem limsup_norm_perturbed_iterate_sub_le {G : E →L[𝕜] E} {f : E} {x ξ : ℕ → E}
    (hstep : ∀ k, x (k + 1) = G (x k) + f + ξ k) {ε : ℝ} (hξ : ∀ k, ‖ξ k‖ ≤ ε) (hG : ‖G‖ < 1)
    {x' : E} (hfix : G x' + f = x') :
    Filter.limsup (fun k => ‖x k - x'‖) Filter.atTop ≤ ε / (1 - ‖G‖) := by
  have hv : Filter.Tendsto (fun k : ℕ => ‖G‖ ^ k * ‖x 0 - x'‖ + ε / (1 - ‖G‖)) Filter.atTop
      (nhds (0 * ‖x 0 - x'‖ + ε / (1 - ‖G‖))) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hG).mul_const _).add_const _
  have hle : Filter.limsup (fun k => ‖x k - x'‖) Filter.atTop
      ≤ Filter.limsup (fun k : ℕ => ‖G‖ ^ k * ‖x 0 - x'‖ + ε / (1 - ‖G‖)) Filter.atTop :=
    Filter.limsup_le_limsup
      (Filter.Eventually.of_forall fun k => norm_perturbed_iterate_sub_le hstep hξ hG hfix k)
      (Filter.isCoboundedUnder_le_of_le _ fun k => norm_nonneg (x k - x'))
      hv.isBoundedUnder_le
  rw [hv.limsup_eq] at hle
  simpa using hle

end Stationary

namespace FloatingPoint

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {μ ν : Type*}

/-- `RoundsAffineStep m G c x y`: `y` is an admissible computed value of the affine step `G x + c`,
evaluated as the matrix–vector product `G x` — itself an inner product per row, as in
`FloatingPoint.RoundsMulVec` — followed by one rounded addition of `c` in each entry.

This is one step of a stationary iteration whose iteration operator `G` and constant `c` have
already been formed. -/
def RoundsAffineStep (m : RoundingModel K) (G : Matrix μ ν K) (c : μ → K) (x : ν → K)
    (y : μ → K) : Prop :=
  ∃ z : μ → K, RoundsMulVec m G x z ∧ ∀ i, m.Rounds (z i + c i) (y i)

variable [Fintype ν]

/-- **One computed step of a stationary iteration is the exact step plus a small perturbation**
([higham2002accuracy], (17.5)–(17.6)): a computed affine step satisfies `ŷ = G x + c + ξ` with `|ξ|
≤ γ_{n+1} (|G| |x| + |c|)` entrywise, `n` being the inner dimension.

Fed to `Stationary.norm_perturbed_iterate_sub_le`, this is the finite-precision half of
[higham2002accuracy] Theorem 17.1: the perturbation is proportional to the data of the step and not
to the number of steps taken, so the iteration has a limiting accuracy.

Reference: [higham2002accuracy], Theorems 17.1–17.2. -/
theorem exists_roundsAffineStep_eq_add {m : RoundingModel K} (hu : m.u < 1)
    (hcard : ((Fintype.card ν + 1 : ℕ) : K) * m.u < 1) {G : Matrix μ ν K} {c : μ → K}
    {x : ν → K} {y : μ → K} (h : RoundsAffineStep m G c x y) :
    ∃ ξ : μ → K, y = G *ᵥ x + c + ξ ∧
      |ξ| ≤ gamma m.u (Fintype.card ν + 1) • (G.abs *ᵥ |x| + |c|) := by
  obtain ⟨z, hz, hadd⟩ := h
  have hu0 : (0 : K) ≤ m.u := m.u_nonneg
  have hcard' : (Fintype.card ν : K) * m.u < 1 := by
    have hle : (Fintype.card ν : K) * m.u ≤ ((Fintype.card ν + 1 : ℕ) : K) * m.u := by
      push_cast
      nlinarith
    linarith
  refine ⟨y - (G *ᵥ x + c), by abel, Pi.le_def.2 fun i => ?_⟩
  -- the two error contributions, and the row sum they are measured against
  set n : ℕ := Fintype.card ν with hn
  set P : K := (G.abs *ᵥ |x|) i with hP
  have hPnonneg : 0 ≤ P := by
    rw [hP]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hmul : |(G *ᵥ x) i| ≤ P := Matrix.abs_mulVec_le G x i
  have hzi : |z i - (G *ᵥ x) i| ≤ gamma m.u n * P :=
    abs_sub_le_of_roundsMulVec hu hcard' hz i
  have hyi : |y i - (z i + c i)| ≤ m.u * |z i + c i| := m.abs_sub_le (hadd i)
  -- the size of the rounded quantity
  have hzc : |z i + c i| ≤ (1 + gamma m.u n) * P + |c i| := by
    have h1 : |z i| ≤ P + gamma m.u n * P := by
      have := abs_sub_abs_le_abs_sub (z i) ((G *ᵥ x) i)
      linarith [hzi, hmul]
    calc |z i + c i| ≤ |z i| + |c i| := abs_add_le _ _
      _ ≤ (P + gamma m.u n * P) + |c i| := by linarith
      _ = (1 + gamma m.u n) * P + |c i| := by ring
  -- collect
  have hstep : gamma m.u n * (1 + m.u) + m.u ≤ gamma m.u (n + 1) :=
    gamma_mul_one_add_add_le hu0 hu hcard
  have hun : m.u ≤ gamma m.u (n + 1) :=
    le_trans (le_gamma_one hu0 hu) (gamma_mono hu0 (Nat.le_add_left 1 n) hcard)
  have hgn : 0 ≤ gamma m.u n := gamma_nonneg hu0 hcard'
  have hci : 0 ≤ |c i| := abs_nonneg _
  have hbound : |(y - (G *ᵥ x + c)) i| ≤ m.u * ((1 + gamma m.u n) * P + |c i|)
      + gamma m.u n * P := by
    have hsplit : (y - (G *ᵥ x + c)) i = (y i - (z i + c i)) + (z i - (G *ᵥ x) i) := by
      simp only [Pi.sub_apply, Pi.add_apply]
      ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    have := mul_le_mul_of_nonneg_left hzc hu0
    linarith
  have htarget : (gamma m.u (n + 1) • (G.abs *ᵥ |x| + |c|)) i
      = gamma m.u (n + 1) * (P + |c i|) := by
    rw [hP]
    simp [Pi.smul_apply, smul_eq_mul]
  rw [htarget]
  refine hbound.trans ?_
  nlinarith [mul_le_mul_of_nonneg_right hstep hPnonneg,
    mul_le_mul_of_nonneg_right hun hci]

end FloatingPoint

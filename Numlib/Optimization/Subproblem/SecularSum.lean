import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Numlib.Analysis.Calculus.Taylor

/-!
# The spectral form of a secular function

For a finite family of poles `-μ i` and weights `w i`, this file studies the real function
`secularSum μ w x = ∑ i, w i / (x + μ i) ^ 2` on the half-line
`secularDomain μ = {x | ∀ i, 0 < x + μ i}` to the right of every pole. With `μ` the eigenvalues
of a symmetric operator `H` and `w i = ⟪bᵢ, g⟫²` the squared coordinates of a vector `g` in an
orthonormal eigenbasis, `secularSum μ w λ` is the secular function `π(λ) = ‖(H + λ)⁻¹ g‖²` of the
trust-region and regularization subproblems (Cartis–Gould–Toint, *Evaluation complexity of
algorithms for nonconvex optimization*, §8.2, (8.2.7)); nothing here mentions operators, so the
results apply equally to tridiagonal (Lanczos) and scaled problems.

## Main results

* `iteratedDeriv_secularSum`: the closed form of every derivative,
  `π⁽ʲ⁾(x) = (-1)ʲ (j + 1)! ∑ wᵢ / (x + μᵢ)^(j+2)` (book (B.8.8)), written with the moments
  `secularMoment μ w m x = ∑ wᵢ / (x + μᵢ)^m`.
* `secularSum_strictAntiOn` and companions: with nonnegative, not all zero weights, `secularSum`
  is positive, continuous, strictly decreasing and strictly convex on `secularDomain μ` and tends
  to `0` at `+∞`.
* `secularSum_taylor_bounds`, `secularSum_taylor_bounds_strict`: the signed Taylor bounds of every
  order (Theorem 8.2.2).
* `secularSum_curvature`, `secularSum_curvature_eq_iff`: the Cauchy–Schwarz inequality
  `(β - 1) p'² + p p'' ≥ 4 (β + 1/2) c²` behind Lemma 8.2.3, with its equality case
  `SinglePole μ w` (all positive weight sits at a single pole).
* `secularSum_rpow_deriv_sign`, `secularSum_rpow_shape`, `secularSum_rpow_tangent`: the
  transformed secular function `x ↦ secularSum μ w x ^ β` (Lemma 8.2.3, Corollary 8.2.4,
  Theorem 8.2.5).
* `newtonFactor`, `antitone_newtonFactor`: the factor `(1 - μ^β)/β` of the Newton step on the
  transformed secular equation is antitone in `β` (Lemma B.8.2).

## Corrections to the source

The book claims that the inequalities of Lemma 8.2.3 (ii), Corollary 8.2.4 (concavity) and
Theorem 8.2.5 are strict whenever `g ≠ 0`. This fails for `β = -1/2` when all the positive weight
sits at a single pole (`g` in one eigenspace of `H`): then `secularSum μ w x ^ (-1/2)` is affine on
`secularDomain μ` (for `n = 1`, `H = 0`, `g = 1`, it is `x ↦ x`), the second derivative vanishes
and the first-order Taylor estimate is exact. Here strictness is stated under `β ≠ -1/2 ∨
¬ SinglePole μ w`, and the exceptional case is proved to give equality. The strict Taylor
estimates also need `δ ≠ 0`, which the book omits in Theorem 8.2.5.
-/

open Set Filter Topology
open Finset (range)
open scoped Nat

namespace Subproblem

variable {ι : Type*} (μ w : ι → ℝ)

/-! ### Definitions -/

section Defs

variable [Fintype ι]

/-- The secular function in spectral form, `∑ i, w i / (x + μ i) ^ 2` (book (8.2.7)). -/
noncomputable def secularSum (x : ℝ) : ℝ := ∑ i, w i / (x + μ i) ^ 2

/-- The moments `∑ i, w i / (x + μ i) ^ m`; `secularSum` is the moment of order `2`, and the
derivatives of `secularSum` are multiples of the higher moments. -/
noncomputable def secularMoment (m : ℕ) (x : ℝ) : ℝ := ∑ i, w i / (x + μ i) ^ m

end Defs

/-- The half-line to the right of every pole, `{x | ∀ i, 0 < x + μ i}` (all of `ℝ` if `ι` is
empty). -/
def secularDomain : Set ℝ := {x | ∀ i, 0 < x + μ i}

/-- All the nonzero weights sit at a single pole: `μ i = μ j` whenever `w i ≠ 0` and `w j ≠ 0`.
This is the equality case of the curvature inequality `secularSum_curvature`. -/
def SinglePole : Prop := ∀ i j, w i ≠ 0 → w j ≠ 0 → μ i = μ j

variable {μ w}

/-! ### The domain -/

section Domain

@[simp]
theorem mem_secularDomain {x : ℝ} : x ∈ secularDomain μ ↔ ∀ i, 0 < x + μ i := Iff.rfl

theorem add_ne_zero_of_mem_secularDomain {x : ℝ} (hx : x ∈ secularDomain μ) (i : ι) :
    x + μ i ≠ 0 :=
  (hx i).ne'

theorem add_mem_secularDomain {x δ : ℝ} (hx : x ∈ secularDomain μ) (hδ : 0 ≤ δ) :
    x + δ ∈ secularDomain μ := fun i => by have := hx i; linarith

theorem secularDomain_eq_iInter : secularDomain μ = ⋂ i, Ioi (-μ i) := by
  ext x; simp [neg_lt_iff_pos_add]

theorem convex_secularDomain : Convex ℝ (secularDomain μ) := by
  rw [secularDomain_eq_iInter]
  exact convex_iInter fun _ => convex_Ioi _

/-- Weights are nonnegative and not all zero exactly when some weight is positive. -/
theorem exists_pos_of_ne_zero (hw : 0 ≤ w) (hw0 : w ≠ 0) : ∃ i, 0 < w i := by
  by_contra h
  push Not at h
  exact hw0 (funext fun i => le_antisymm (h i) (hw i))

variable [Finite ι]

theorem isOpen_secularDomain : IsOpen (secularDomain μ) := by
  rw [secularDomain_eq_iInter]
  exact isOpen_iInter_of_finite fun _ => isOpen_Ioi

theorem eventually_mem_secularDomain : ∀ᶠ x in atTop, x ∈ secularDomain μ := by
  simp only [mem_secularDomain]
  exact eventually_all.2 fun i => (eventually_gt_atTop (-μ i)).mono fun x hx => by linarith

theorem secularDomain_mem_nhds {x : ℝ} (hx : x ∈ secularDomain μ) : secularDomain μ ∈ 𝓝 x :=
  isOpen_secularDomain.mem_nhds hx

/-- The set where no pole is hit is open. -/
theorem isOpen_setOf_add_ne_zero : IsOpen {x : ℝ | ∀ i, x + μ i ≠ 0} := by
  have : {x : ℝ | ∀ i, x + μ i ≠ 0} = ⋂ i, {x | x + μ i ≠ 0} := by ext; simp
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_ne_fun (by fun_prop) continuous_const

end Domain

/-! ### Basic properties -/

variable [Fintype ι]

theorem secularSum_eq_secularMoment : secularSum μ w = secularMoment μ w 2 := rfl

theorem secularSum_apply (x : ℝ) : secularSum μ w x = ∑ i, w i / (x + μ i) ^ 2 := rfl

theorem secularMoment_apply (m : ℕ) (x : ℝ) :
    secularMoment μ w m x = ∑ i, w i / (x + μ i) ^ m := rfl

theorem secularMoment_nonneg (hw : 0 ≤ w) {x : ℝ} (hx : x ∈ secularDomain μ) (m : ℕ) :
    0 ≤ secularMoment μ w m x :=
  Finset.sum_nonneg fun i _ => div_nonneg (hw i) (pow_nonneg (hx i).le m)

theorem secularMoment_pos (hw : 0 ≤ w) (hw0 : w ≠ 0) {x : ℝ} (hx : x ∈ secularDomain μ)
    (m : ℕ) : 0 < secularMoment μ w m x := by
  obtain ⟨i, hi⟩ := exists_pos_of_ne_zero hw hw0
  exact Finset.sum_pos' (fun j _ => div_nonneg (hw j) (pow_nonneg (hx j).le m))
    ⟨i, Finset.mem_univ _, div_pos hi (pow_pos (hx i) m)⟩

theorem secularSum_nonneg (hw : 0 ≤ w) {x : ℝ} (hx : x ∈ secularDomain μ) :
    0 ≤ secularSum μ w x :=
  secularMoment_nonneg hw hx 2

theorem secularSum_pos (hw : 0 ≤ w) (hw0 : w ≠ 0) {x : ℝ} (hx : x ∈ secularDomain μ) :
    0 < secularSum μ w x :=
  secularMoment_pos hw hw0 hx 2

/-! ### Derivatives -/

/-- The derivative of one term `c / (x + a) ^ m`. -/
theorem hasDerivAt_div_add_pow (c a : ℝ) (m : ℕ) {x : ℝ} (hx : x + a ≠ 0) :
    HasDerivAt (fun y => c / (y + a) ^ m) (-(m * (c / (x + a) ^ (m + 1)))) x := by
  have h1 : HasDerivAt (fun y => (y + a) ^ m) (m * (x + a) ^ (m - 1)) x := by
    simpa using ((hasDerivAt_id x).add_const a).fun_pow m
  have h2 := (hasDerivAt_const x c).div h1 (pow_ne_zero m hx)
  convert h2 using 1
  rcases m with _ | m
  · simp
  · simp only [Nat.add_sub_cancel]
    field_simp
    push_cast
    ring

theorem hasDerivAt_secularMoment (m : ℕ) {x : ℝ} (hx : ∀ i, x + μ i ≠ 0) :
    HasDerivAt (secularMoment μ w m) (-(m * secularMoment μ w (m + 1) x)) x := by
  have := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    hasDerivAt_div_add_pow (w i) (μ i) m (hx i)
  convert this using 1
  · ext y; simp [secularMoment]
  · simp [secularMoment, Finset.mul_sum]

theorem contDiffAt_secularMoment (m : ℕ) {n : WithTop ℕ∞} {x : ℝ} (hx : ∀ i, x + μ i ≠ 0) :
    ContDiffAt ℝ n (secularMoment μ w m) x := by
  have : secularMoment μ w m = fun y => ∑ i, w i / (y + μ i) ^ m := rfl
  rw [this]
  exact ContDiffAt.sum fun i _ =>
    contDiffAt_const.div ((contDiffAt_id.add contDiffAt_const).pow m) (pow_ne_zero m (hx i))

theorem contDiffOn_secularSum {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (secularSum μ w) (secularDomain μ) := fun _ hx =>
  (contDiffAt_secularMoment 2 (add_ne_zero_of_mem_secularDomain hx)).contDiffWithinAt

theorem continuousOn_secularSum : ContinuousOn (secularSum μ w) (secularDomain μ) :=
  contDiffOn_secularSum (n := 0).continuousOn

/-- The derivatives of `secularSum` in closed form (book (B.8.8)): away from the poles,
`iteratedDeriv j (secularSum μ w) x = (-1) ^ j * (j + 1)! * ∑ i, w i / (x + μ i) ^ (j + 2)`. -/
theorem iteratedDeriv_secularSum (j : ℕ) {x : ℝ} (hx : ∀ i, x + μ i ≠ 0) :
    iteratedDeriv j (secularSum μ w) x = (-1) ^ j * (j + 1)! * secularMoment μ w (j + 2) x := by
  induction j generalizing x with
  | zero => simp [secularSum_eq_secularMoment]
  | succ j ih =>
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv j (secularSum μ w) =ᶠ[𝓝 x]
        fun y => (-1) ^ j * (j + 1)! * secularMoment μ w (j + 2) y :=
      Filter.eventually_of_mem (isOpen_setOf_add_ne_zero.mem_nhds hx) fun y hy => ih hy
    rw [hev.deriv_eq, ((hasDerivAt_secularMoment (j + 2) hx).const_mul _).deriv]
    push_cast [Nat.factorial_succ]
    ring

theorem deriv_secularSum {x : ℝ} (hx : ∀ i, x + μ i ≠ 0) :
    deriv (secularSum μ w) x = -2 * secularMoment μ w 3 x := by
  rw [← iteratedDeriv_one, iteratedDeriv_secularSum 1 hx]
  norm_num

theorem iteratedDeriv_two_secularSum {x : ℝ} (hx : ∀ i, x + μ i ≠ 0) :
    iteratedDeriv 2 (secularSum μ w) x = 6 * secularMoment μ w 4 x := by
  rw [iteratedDeriv_secularSum 2 hx]
  norm_num [Nat.factorial]

theorem hasDerivAt_secularSum {x : ℝ} (hx : ∀ i, x + μ i ≠ 0) :
    HasDerivAt (secularSum μ w) (-2 * secularMoment μ w 3 x) x := by
  simpa [secularSum_eq_secularMoment] using hasDerivAt_secularMoment (μ := μ) (w := w) 2 hx

/-! ### Shape -/

/-- `secularSum` is continuous, strictly decreasing and strictly convex on `secularDomain μ`
when the weights are nonnegative and not all zero; see also `secularSum_pos`,
`secularSum_strictConvexOn` and `tendsto_secularSum_atTop`. (With all weights zero it is
identically `0`.) -/
theorem secularSum_strictAntiOn (hw : 0 ≤ w) (hw0 : w ≠ 0) :
    StrictAntiOn (secularSum μ w) (secularDomain μ) := by
  refine strictAntiOn_of_deriv_neg convex_secularDomain continuousOn_secularSum fun x hx => ?_
  rw [isOpen_secularDomain.interior_eq] at hx
  rw [deriv_secularSum (add_ne_zero_of_mem_secularDomain hx)]
  have := secularMoment_pos hw hw0 hx 3
  linarith

theorem secularSum_strictConvexOn (hw : 0 ≤ w) (hw0 : w ≠ 0) :
    StrictConvexOn ℝ (secularDomain μ) (secularSum μ w) := by
  refine strictConvexOn_of_deriv2_pos convex_secularDomain continuousOn_secularSum fun x hx => ?_
  rw [isOpen_secularDomain.interior_eq] at hx
  rw [← iteratedDeriv_eq_iterate, iteratedDeriv_two_secularSum
    (add_ne_zero_of_mem_secularDomain hx)]
  have := secularMoment_pos hw hw0 hx 4
  linarith

theorem tendsto_secularSum_atTop : Tendsto (secularSum μ w) atTop (𝓝 0) := by
  have : Tendsto (fun x => ∑ i, w i / (x + μ i) ^ 2) atTop (𝓝 (∑ _i : ι, (0 : ℝ))) :=
    tendsto_finsetSum _ fun i _ => tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop two_ne_zero).comp (tendsto_atTop_add_const_right _ _ tendsto_id))
  rw [Finset.sum_const_zero] at this
  exact this

/-! ### Taylor expansions -/

/-- The Lagrange form of the Taylor remainder of `secularSum` (book (B.8.9)): for `x` and
`x + δ` in `secularDomain μ` there is `ξ ∈ secularDomain μ` with
`secularSum μ w (x + δ) = tₖ(δ) + (k + 2) M_{k+3}(ξ) (-δ) ^ (k + 1)`. -/
theorem secularSum_add_eq_sum_taylor_add {x δ : ℝ} (hx : x ∈ secularDomain μ)
    (hxδ : x + δ ∈ secularDomain μ) (k : ℕ) :
    ∃ ξ ∈ secularDomain μ, secularSum μ w (x + δ) =
      ∑ j ∈ range (k + 1), iteratedDeriv j (secularSum μ w) x / j ! * δ ^ j
        + (k + 2) * secularMoment μ w (k + 3) ξ * (-δ) ^ (k + 1) := by
  obtain ⟨ξ, hξ, h⟩ := exists_eq_sum_taylor_add isOpen_secularDomain convex_secularDomain
    (k := k) contDiffOn_secularSum hx hxδ
  refine ⟨ξ, hξ, ?_⟩
  rw [h, iteratedDeriv_secularSum (k + 1) (add_ne_zero_of_mem_secularDomain hξ), neg_pow δ]
  congr 1
  rw [show k + 1 + 2 = k + 3 by ring, Nat.factorial_succ (k + 1)]
  push_cast
  field_simp
  ring

/-- Consecutive Taylor polynomials of `secularSum` differ by
`tₖ₊₁(δ) - tₖ(δ) = (k + 2) M_{k+3}(x) (-δ) ^ (k + 1)`. -/
theorem sum_taylor_succ_secularSum {x : ℝ} (hx : ∀ i, x + μ i ≠ 0) (k : ℕ) (δ : ℝ) :
    ∑ j ∈ range (k + 2), iteratedDeriv j (secularSum μ w) x / j ! * δ ^ j =
      ∑ j ∈ range (k + 1), iteratedDeriv j (secularSum μ w) x / j ! * δ ^ j
        + (k + 2) * secularMoment μ w (k + 3) x * (-δ) ^ (k + 1) := by
  rw [Finset.sum_range_succ, iteratedDeriv_secularSum (k + 1) hx, neg_pow δ]
  congr 1
  rw [show k + 1 + 2 = k + 3 by ring, Nat.factorial_succ (k + 1)]
  push_cast
  field_simp
  ring

/-- The sign of `(-δ) ^ (k + 1)` for `δ > 0`: negative for even `k`. -/
private theorem neg_pow_succ_neg_of_even {δ : ℝ} (hδ : 0 < δ) {k : ℕ} (hk : Even k) :
    (-δ) ^ (k + 1) < 0 :=
  hk.add_one.pow_neg (by linarith)

/-- The sign of `(-δ) ^ (k + 1)` for `δ > 0`: positive for odd `k`. -/
private theorem neg_pow_succ_pos_of_odd {δ : ℝ} (hδ : 0 < δ) {k : ℕ} (hk : Odd k) :
    0 < (-δ) ^ (k + 1) :=
  hk.add_one.pow_pos (by linarith)

/-- **Signed Taylor bounds** (Cartis–Gould–Toint, Theorem 8.2.2, in spectral form). Let `w ≥ 0`,
`x ∈ secularDomain μ` and `tₖ(δ) = ∑ j ≤ k, π⁽ʲ⁾(x) / j! δʲ` the Taylor polynomials of
`π = secularSum μ w` at `x`. For `δ > 0`, `π(x + δ) ≤ tₖ(δ)` for even `k` and `π(x + δ) ≥ tₖ(δ)`
for odd `k`; for `δ < 0` with `x + δ ∈ secularDomain μ`, `tₖ(δ) ≤ tₖ₊₁(δ) ≤ π(x + δ)` for every
`k`. (The book states these for `k > 0`; they hold for `k = 0` as well.) The strict forms are
`secularSum_taylor_bounds_strict`. -/
theorem secularSum_taylor_bounds (hw : 0 ≤ w) {x : ℝ} (hx : x ∈ secularDomain μ) (k : ℕ) :
    (∀ δ, 0 < δ → (Even k → secularSum μ w (x + δ) ≤
        ∑ j ∈ range (k + 1), iteratedDeriv j (secularSum μ w) x / j ! * δ ^ j) ∧
      (Odd k → ∑ j ∈ range (k + 1), iteratedDeriv j (secularSum μ w) x / j ! * δ ^ j ≤
        secularSum μ w (x + δ))) ∧
    (∀ δ, δ < 0 → x + δ ∈ secularDomain μ →
      ∑ j ∈ range (k + 1), iteratedDeriv j (secularSum μ w) x / j ! * δ ^ j ≤
        ∑ j ∈ range (k + 2), iteratedDeriv j (secularSum μ w) x / j ! * δ ^ j ∧
      ∑ j ∈ range (k + 2), iteratedDeriv j (secularSum μ w) x / j ! * δ ^ j ≤
        secularSum μ w (x + δ)) := by
  refine ⟨fun δ hδ => ?_, fun δ hδ hxδ => ?_⟩
  · obtain ⟨ξ, hξ, h⟩ := secularSum_add_eq_sum_taylor_add (w := w) hx
      (add_mem_secularDomain hx hδ.le) k
    have hM := secularMoment_nonneg hw hξ (k + 3)
    have hk2 : (0 : ℝ) ≤ k + 2 := by positivity
    refine ⟨fun hk => ?_, fun hk => ?_⟩
    · have := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hk2 hM)
        (neg_pow_succ_neg_of_even hδ hk).le
      linarith
    · have := mul_nonneg (mul_nonneg hk2 hM) (neg_pow_succ_pos_of_odd hδ hk).le
      linarith
  · have hpow : 0 ≤ (-δ) ^ (k + 1) := pow_nonneg (by linarith) _
    have hpow' : 0 ≤ (-δ) ^ (k + 2) := pow_nonneg (by linarith) _
    have hk2 : (0 : ℝ) ≤ k + 2 := by positivity
    have hk3 : (0 : ℝ) ≤ (k + 1 : ℕ) + 2 := by positivity
    obtain ⟨ξ, hξ, h⟩ := secularSum_add_eq_sum_taylor_add (w := w) hx hxδ (k + 1)
    rw [show k + 1 + 1 = k + 2 from rfl] at h
    have hs := sum_taylor_succ_secularSum (w := w) (add_ne_zero_of_mem_secularDomain hx) k δ
    have h1 := mul_nonneg (mul_nonneg hk2 (secularMoment_nonneg hw hx (k + 3))) hpow
    have h2 := mul_nonneg (mul_nonneg hk3 (secularMoment_nonneg hw hξ (k + 1 + 3))) hpow'
    push_cast at h h2
    constructor <;> linarith

/-- **Strict signed Taylor bounds** (Theorem 8.2.2, strict part): when the weights are
nonnegative and not all zero, the inequalities of `secularSum_taylor_bounds` are strict. -/
theorem secularSum_taylor_bounds_strict (hw : 0 ≤ w) (hw0 : w ≠ 0) {x : ℝ}
    (hx : x ∈ secularDomain μ) (k : ℕ) :
    (∀ δ, 0 < δ → (Even k → secularSum μ w (x + δ) <
        ∑ j ∈ range (k + 1), iteratedDeriv j (secularSum μ w) x / j ! * δ ^ j) ∧
      (Odd k → ∑ j ∈ range (k + 1), iteratedDeriv j (secularSum μ w) x / j ! * δ ^ j <
        secularSum μ w (x + δ))) ∧
    (∀ δ, δ < 0 → x + δ ∈ secularDomain μ →
      ∑ j ∈ range (k + 1), iteratedDeriv j (secularSum μ w) x / j ! * δ ^ j <
        ∑ j ∈ range (k + 2), iteratedDeriv j (secularSum μ w) x / j ! * δ ^ j ∧
      ∑ j ∈ range (k + 2), iteratedDeriv j (secularSum μ w) x / j ! * δ ^ j <
        secularSum μ w (x + δ)) := by
  refine ⟨fun δ hδ => ?_, fun δ hδ hxδ => ?_⟩
  · obtain ⟨ξ, hξ, h⟩ := secularSum_add_eq_sum_taylor_add (w := w) hx
      (add_mem_secularDomain hx hδ.le) k
    have hM := secularMoment_pos hw hw0 hξ (k + 3)
    have hk2 : (0 : ℝ) < k + 2 := by positivity
    refine ⟨fun hk => ?_, fun hk => ?_⟩
    · have := mul_neg_of_pos_of_neg (mul_pos hk2 hM) (neg_pow_succ_neg_of_even hδ hk)
      linarith
    · have := mul_pos (mul_pos hk2 hM) (neg_pow_succ_pos_of_odd hδ hk)
      linarith
  · have hpow : 0 < (-δ) ^ (k + 1) := pow_pos (by linarith) _
    have hpow' : 0 < (-δ) ^ (k + 2) := pow_pos (by linarith) _
    have hk2 : (0 : ℝ) < k + 2 := by positivity
    have hk3 : (0 : ℝ) < (k + 1 : ℕ) + 2 := by positivity
    obtain ⟨ξ, hξ, h⟩ := secularSum_add_eq_sum_taylor_add (w := w) hx hxδ (k + 1)
    rw [show k + 1 + 1 = k + 2 from rfl] at h
    have hs := sum_taylor_succ_secularSum (w := w) (add_ne_zero_of_mem_secularDomain hx) k δ
    have h1 := mul_pos (mul_pos hk2 (secularMoment_pos hw hw0 hx (k + 3))) hpow
    have h2 := mul_pos (mul_pos hk3 (secularMoment_pos hw hw0 hξ (k + 1 + 3))) hpow'
    push_cast at h h2
    constructor <;> linarith

/-! ### The curvature inequality -/

/-- Lagrange's identity for the moments of orders `2`, `3`, `4`: with `uᵢ = (x + μ i)⁻¹`,
`2 (M₂ M₄ - M₃²) = ∑ᵢ ∑ⱼ wᵢ wⱼ (uᵢ uⱼ)² (uᵢ - uⱼ)²`. -/
theorem two_mul_secularMoment_sub_sq (x : ℝ) :
    2 * (secularMoment μ w 2 x * secularMoment μ w 4 x - secularMoment μ w 3 x ^ 2) =
      ∑ i, ∑ j, w i * w j * ((x + μ i)⁻¹ * (x + μ j)⁻¹) ^ 2 *
        ((x + μ i)⁻¹ - (x + μ j)⁻¹) ^ 2 := by
  set u : ι → ℝ := fun i => (x + μ i)⁻¹ with hu
  have hM : ∀ m, secularMoment μ w m x = ∑ i, w i * u i ^ m := fun m =>
    Finset.sum_congr rfl fun i _ => by simp [hu, div_eq_mul_inv, inv_pow]
  rw [hM, hM, hM, sq (∑ i, w i * u i ^ 3), Finset.sum_mul_sum, Finset.sum_mul_sum]
  have hcomm : ∑ i, ∑ j, w j * u j ^ 2 * (w i * u i ^ 4) =
      ∑ i, ∑ j, w i * u i ^ 2 * (w j * u j ^ 4) := Finset.sum_comm
  have hexp : ∑ i, ∑ j, w i * w j * (u i * u j) ^ 2 * (u i - u j) ^ 2 =
      ∑ i, ∑ j, w i * u i ^ 2 * (w j * u j ^ 4) + ∑ i, ∑ j, w j * u j ^ 2 * (w i * u i ^ 4) -
        2 * ∑ i, ∑ j, w i * u i ^ 3 * (w j * u j ^ 3) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hexp, hcomm]
  ring

/-- The Cauchy–Schwarz inequality `M₃² ≤ M₂ M₄` for nonnegative weights. -/
theorem secularMoment_three_sq_le (hw : 0 ≤ w) (x : ℝ) :
    secularMoment μ w 3 x ^ 2 ≤ secularMoment μ w 2 x * secularMoment μ w 4 x := by
  have := two_mul_secularMoment_sub_sq (μ := μ) (w := w) x
  have hnn : 0 ≤ ∑ i, ∑ j, w i * w j * ((x + μ i)⁻¹ * (x + μ j)⁻¹) ^ 2 *
      ((x + μ i)⁻¹ - (x + μ j)⁻¹) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (mul_nonneg (hw i) (hw j)) (sq_nonneg _)) (sq_nonneg _)
  linarith

/-- The equality case of `secularMoment_three_sq_le`: away from the poles, `M₃² = M₂ M₄` exactly
when all the nonzero weights sit at a single pole. -/
theorem secularMoment_three_sq_eq_iff (hw : 0 ≤ w) {x : ℝ} (hx : ∀ i, x + μ i ≠ 0) :
    secularMoment μ w 3 x ^ 2 = secularMoment μ w 2 x * secularMoment μ w 4 x ↔
      SinglePole μ w := by
  have hid := two_mul_secularMoment_sub_sq (μ := μ) (w := w) x
  have hterm : ∀ i j, 0 ≤ w i * w j * ((x + μ i)⁻¹ * (x + μ j)⁻¹) ^ 2 *
      ((x + μ i)⁻¹ - (x + μ j)⁻¹) ^ 2 := fun i j =>
    mul_nonneg (mul_nonneg (mul_nonneg (hw i) (hw j)) (sq_nonneg _)) (sq_nonneg _)
  have hsum : ∀ i, 0 ≤ ∑ j, w i * w j * ((x + μ i)⁻¹ * (x + μ j)⁻¹) ^ 2 *
      ((x + μ i)⁻¹ - (x + μ j)⁻¹) ^ 2 := fun i => Finset.sum_nonneg fun j _ => hterm i j
  constructor
  · intro heq i j hi hj
    have h0 : ∑ i, ∑ j, w i * w j * ((x + μ i)⁻¹ * (x + μ j)⁻¹) ^ 2 *
        ((x + μ i)⁻¹ - (x + μ j)⁻¹) ^ 2 = 0 := by rw [← hid, heq]; ring
    have hi0 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hsum i).1 h0 i (Finset.mem_univ _)
    have hij := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hterm i j).1 hi0 j
      (Finset.mem_univ _)
    have hui := inv_ne_zero (hx i)
    have huj := inv_ne_zero (hx j)
    simp only [mul_eq_zero, pow_eq_zero_iff two_ne_zero, hi, hj, hui, huj, false_or,
      sub_eq_zero, inv_inj] at hij
    linarith
  · intro hs
    have h0 : ∑ i, ∑ j, w i * w j * ((x + μ i)⁻¹ * (x + μ j)⁻¹) ^ 2 *
        ((x + μ i)⁻¹ - (x + μ j)⁻¹) ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      by_cases hi : w i = 0
      · simp [hi]
      by_cases hj : w j = 0
      · simp [hj]
      simp [hs i j hi hj]
    linarith

/-- **The curvature inequality** (proof of Cartis–Gould–Toint, Lemma 8.2.3). Let `w ≥ 0`, `p` the
function `secularSum μ w`, and `c = ∑ i, w i / (x + μ i) ^ 3` at a point `x` away from the poles.
Then for every real `β`, `(β - 1) p'(x)² + p(x) p''(x) ≥ 4 (β + 1/2) c²`. Equality is
characterized by `secularSum_curvature_eq_iff`. -/
theorem secularSum_curvature (hw : 0 ≤ w) {x : ℝ} (hx : ∀ i, x + μ i ≠ 0) (β : ℝ) :
    4 * (β + 1 / 2) * secularMoment μ w 3 x ^ 2 ≤
      (β - 1) * deriv (secularSum μ w) x ^ 2 +
        secularSum μ w x * iteratedDeriv 2 (secularSum μ w) x := by
  rw [deriv_secularSum hx, iteratedDeriv_two_secularSum hx, secularSum_eq_secularMoment]
  nlinarith [secularMoment_three_sq_le (μ := μ) hw x]

/-- The equality case of `secularSum_curvature`: it is independent of `β` and holds exactly when
all the nonzero weights sit at a single pole. -/
theorem secularSum_curvature_eq_iff (hw : 0 ≤ w) {x : ℝ} (hx : ∀ i, x + μ i ≠ 0) (β : ℝ) :
    (β - 1) * deriv (secularSum μ w) x ^ 2 +
        secularSum μ w x * iteratedDeriv 2 (secularSum μ w) x =
      4 * (β + 1 / 2) * secularMoment μ w 3 x ^ 2 ↔ SinglePole μ w := by
  rw [← secularMoment_three_sq_eq_iff hw hx, deriv_secularSum hx,
    iteratedDeriv_two_secularSum hx, secularSum_eq_secularMoment]
  constructor <;> intro h <;> linarith

/-! ### The transformed secular function -/

section Rpow

variable (hw : 0 ≤ w) (hw0 : w ≠ 0) (β : ℝ)
include hw hw0

/-- The first derivative of the transformed secular function `p ^ β`, `p = secularSum μ w`
(book (8.2.18)): `(p ^ β)' = β p ^ (β - 1) p'`. -/
theorem hasDerivAt_secularSum_rpow {x : ℝ} (hx : x ∈ secularDomain μ) :
    HasDerivAt (fun y => secularSum μ w y ^ β)
      (β * secularSum μ w x ^ (β - 1) * deriv (secularSum μ w) x) x := by
  have hp := hasDerivAt_secularSum (w := w) (add_ne_zero_of_mem_secularDomain hx)
  convert hp.rpow_const (p := β) (Or.inl (secularSum_pos hw hw0 hx).ne') using 1
  rw [hp.deriv]
  ring

theorem deriv_secularSum_rpow {x : ℝ} (hx : x ∈ secularDomain μ) :
    deriv (fun y => secularSum μ w y ^ β) x =
      β * secularSum μ w x ^ (β - 1) * deriv (secularSum μ w) x :=
  (hasDerivAt_secularSum_rpow hw hw0 β hx).deriv

/-- The derivative of `(p ^ β)'` (book (8.2.19)):
`(p ^ β)'' = β p ^ (β - 1) p'' + β (β - 1) p ^ (β - 2) p'²`. -/
theorem hasDerivAt_deriv_secularSum_rpow {x : ℝ} (hx : x ∈ secularDomain μ) :
    HasDerivAt (deriv fun y => secularSum μ w y ^ β)
      (β * secularSum μ w x ^ (β - 1) * iteratedDeriv 2 (secularSum μ w) x +
        β * (β - 1) * secularSum μ w x ^ (β - 2) * deriv (secularSum μ w) x ^ 2) x := by
  have hx' := add_ne_zero_of_mem_secularDomain hx
  have hev : (deriv fun y => secularSum μ w y ^ β) =ᶠ[𝓝 x]
      fun y => β * secularSum μ w y ^ (β - 1) * (-2 * secularMoment μ w 3 y) :=
    Filter.eventually_of_mem (secularDomain_mem_nhds hx) fun y hy => by
      rw [deriv_secularSum_rpow hw hw0 β hy, deriv_secularSum (add_ne_zero_of_mem_secularDomain hy)]
  have hp := hasDerivAt_secularSum (w := w) hx'
  have h1 := (hp.rpow_const (p := β - 1) (Or.inl (secularSum_pos hw hw0 hx).ne')).const_mul β
  have h2 := (hasDerivAt_secularMoment (μ := μ) (w := w) 3 hx').const_mul (-2)
  refine (HasDerivAt.congr_of_eventuallyEq (h1.mul h2) hev).congr_deriv ?_
  rw [iteratedDeriv_two_secularSum hx', deriv_secularSum hx', show β - 1 - 1 = β - 2 by ring]
  push_cast
  ring

theorem iteratedDeriv_two_secularSum_rpow {x : ℝ} (hx : x ∈ secularDomain μ) :
    iteratedDeriv 2 (fun y => secularSum μ w y ^ β) x =
      β * secularSum μ w x ^ (β - 1) * iteratedDeriv 2 (secularSum μ w) x +
        β * (β - 1) * secularSum μ w x ^ (β - 2) * deriv (secularSum μ w) x ^ 2 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  exact (hasDerivAt_deriv_secularSum_rpow hw hw0 β hx).deriv

/-- The second derivative of `p ^ β` factored through the curvature expression:
`(p ^ β)'' = β p ^ (β - 2) ((β - 1) p'² + p p'')`. -/
theorem iteratedDeriv_two_secularSum_rpow_eq_mul {x : ℝ} (hx : x ∈ secularDomain μ) :
    iteratedDeriv 2 (fun y => secularSum μ w y ^ β) x =
      β * secularSum μ w x ^ (β - 2) * ((β - 1) * deriv (secularSum μ w) x ^ 2 +
        secularSum μ w x * iteratedDeriv 2 (secularSum μ w) x) := by
  have hp := secularSum_pos hw hw0 hx
  have : secularSum μ w x ^ (β - 1) = secularSum μ w x ^ (β - 2) * secularSum μ w x := by
    rw [← Real.rpow_add_one hp.ne', show β - 2 + 1 = β - 1 by ring]
  rw [iteratedDeriv_two_secularSum_rpow hw hw0 β hx, this]
  ring

/-- **Derivatives of the transformed secular function** (Cartis–Gould–Toint, Lemma 8.2.3, in
spectral form). Let the weights be nonnegative and not all zero, `x ∈ secularDomain μ` and
`q = fun y => secularSum μ w y ^ β`. Then
(i) `q'(x) < 0` for `β > 0` and `q'(x) > 0` for `β < 0`;
(ii) `q''(x) > 0` for `β > 0`, and `q''(x) ≤ 0` for `β ∈ [-1/2, 0)`, strictly unless `β = -1/2`
and the nonzero weights sit at a single pole, in which case `q''(x) = 0`.
The book claims strictness in (ii) whenever `g ≠ 0`; the single-pole case at `β = -1/2` is a
counterexample. -/
theorem secularSum_rpow_deriv_sign {x : ℝ} (hx : x ∈ secularDomain μ) :
    (0 < β → deriv (fun y => secularSum μ w y ^ β) x < 0) ∧
    (β < 0 → 0 < deriv (fun y => secularSum μ w y ^ β) x) ∧
    (0 < β → 0 < iteratedDeriv 2 (fun y => secularSum μ w y ^ β) x) ∧
    (β ∈ Ico (-1 / 2) 0 → iteratedDeriv 2 (fun y => secularSum μ w y ^ β) x ≤ 0) ∧
    (β ∈ Ico (-1 / 2) 0 → (β ≠ -1 / 2 ∨ ¬ SinglePole μ w) →
      iteratedDeriv 2 (fun y => secularSum μ w y ^ β) x < 0) ∧
    (β = -1 / 2 → SinglePole μ w → iteratedDeriv 2 (fun y => secularSum μ w y ^ β) x = 0) := by
  have hx' := add_ne_zero_of_mem_secularDomain hx
  have hp := secularSum_pos hw hw0 hx
  have hM3 := secularMoment_pos hw hw0 hx 3
  have hd : deriv (secularSum μ w) x < 0 := by rw [deriv_secularSum hx']; linarith
  have hpow1 : 0 < secularSum μ w x ^ (β - 1) := Real.rpow_pos_of_pos hp _
  have hpow2 : 0 < secularSum μ w x ^ (β - 2) := Real.rpow_pos_of_pos hp _
  have hcurv := secularSum_curvature hw hx' β
  have hcurv_iff := secularSum_curvature_eq_iff hw hx' β
  have hc2 : 0 < secularMoment μ w 3 x ^ 2 := by positivity
  rw [deriv_secularSum_rpow hw hw0 β hx, iteratedDeriv_two_secularSum_rpow_eq_mul hw hw0 β hx]
  set K := (β - 1) * deriv (secularSum μ w) x ^ 2 +
    secularSum μ w x * iteratedDeriv 2 (secularSum μ w) x
  refine ⟨fun hβ => ?_, fun hβ => ?_, fun hβ => ?_, fun hβ => ?_, fun hβ hne => ?_,
    fun hβ hs => ?_⟩
  · exact mul_neg_of_pos_of_neg (mul_pos hβ hpow1) hd
  · exact mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hβ hpow1) hd
  · have hK : 0 < K := lt_of_lt_of_le (by have := hβ; positivity) hcurv
    exact mul_pos (mul_pos hβ hpow2) hK
  · have hK : 0 ≤ K := le_trans (mul_nonneg (by linarith [hβ.1]) hc2.le) hcurv
    exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hβ.2.le hpow2.le) hK
  · have hK : 0 < K := by
      rcases hne with hne | hne
      · have : 0 < β + 1 / 2 := by
          rcases hβ.1.lt_or_eq with h | h
          · linarith
          · exact absurd h.symm hne
        exact lt_of_lt_of_le (by positivity) hcurv
      · have hlt : 4 * (β + 1 / 2) * secularMoment μ w 3 x ^ 2 < K :=
          lt_of_le_of_ne hcurv fun h => hne (hcurv_iff.1 h.symm)
        exact lt_of_le_of_lt (mul_nonneg (by linarith [hβ.1]) hc2.le) hlt
    exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hβ.2 hpow2) hK
  · have hK : K = 0 := by rw [hcurv_iff.2 hs, hβ]; ring
    rw [hK, mul_zero]

theorem continuousOn_secularSum_rpow :
    ContinuousOn (fun y => secularSum μ w y ^ β) (secularDomain μ) :=
  continuousOn_secularSum.rpow_const fun _ hx => Or.inl (secularSum_pos hw hw0 hx).ne'

theorem contDiffOn_secularSum_rpow {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (fun y => secularSum μ w y ^ β) (secularDomain μ) := fun _ hx =>
  ((contDiffAt_secularMoment 2 (add_ne_zero_of_mem_secularDomain hx)).rpow_const_of_ne
    (secularSum_pos hw hw0 hx).ne').contDiffWithinAt

/-- The transformed secular function is strictly concave on `secularDomain μ` for
`β ∈ [-1/2, 0)`, except when `β = -1/2` and the nonzero weights sit at a single pole (then it is
affine, see `secularSum_rpow_tangent`). -/
theorem secularSum_rpow_strictConcaveOn (hβ : β ∈ Ico (-1 / 2) 0)
    (hne : β ≠ -1 / 2 ∨ ¬ SinglePole μ w) :
    StrictConcaveOn ℝ (secularDomain μ) (fun y => secularSum μ w y ^ β) := by
  refine strictConcaveOn_of_deriv2_neg convex_secularDomain
    (continuousOn_secularSum_rpow hw hw0 β) fun x hx => ?_
  rw [isOpen_secularDomain.interior_eq] at hx
  rw [← iteratedDeriv_eq_iterate]
  exact (secularSum_rpow_deriv_sign hw hw0 β hx).2.2.2.2.1 hβ hne

/-- **Monotonicity of the transformed secular function** (Cartis–Gould–Toint, Corollary 8.2.4,
in spectral form). Let the weights be nonnegative and not all zero. On `secularDomain μ`, the
function `q = fun y => secularSum μ w y ^ β` is, for `β > 0`, strictly decreasing and strictly
convex with limit `0` at `+∞`; for `β ∈ [-1/2, 0)` it is strictly increasing and concave with
limit `+∞` at `+∞`. Strict concavity holds except in the single-pole case at `β = -1/2`
(`secularSum_rpow_strictConcaveOn`). -/
theorem secularSum_rpow_shape :
    (0 < β → StrictAntiOn (fun y => secularSum μ w y ^ β) (secularDomain μ) ∧
      StrictConvexOn ℝ (secularDomain μ) (fun y => secularSum μ w y ^ β) ∧
      Tendsto (fun y => secularSum μ w y ^ β) atTop (𝓝 0)) ∧
    (β ∈ Ico (-1 / 2) 0 → StrictMonoOn (fun y => secularSum μ w y ^ β) (secularDomain μ) ∧
      ConcaveOn ℝ (secularDomain μ) (fun y => secularSum μ w y ^ β) ∧
      Tendsto (fun y => secularSum μ w y ^ β) atTop atTop) := by
  have hD := convex_secularDomain (μ := μ)
  have hc := continuousOn_secularSum_rpow (μ := μ) hw hw0 β
  have hint : interior (secularDomain μ) = secularDomain μ := isOpen_secularDomain.interior_eq
  have hsign := fun {x} (hx : x ∈ secularDomain μ) => secularSum_rpow_deriv_sign hw hw0 β hx
  refine ⟨fun hβ => ⟨?_, ?_, ?_⟩, fun hβ => ⟨?_, ?_, ?_⟩⟩
  · exact strictAntiOn_of_deriv_neg hD hc fun x hx => (hsign (hint ▸ hx)).1 hβ
  · refine strictConvexOn_of_deriv2_pos hD hc fun x hx => ?_
    rw [← iteratedDeriv_eq_iterate]
    exact (hsign (hint ▸ hx)).2.2.1 hβ
  · have := (Real.continuousAt_rpow_const 0 β (Or.inr hβ.le)).tendsto.comp
      (tendsto_secularSum_atTop (μ := μ) (w := w))
    rwa [Real.zero_rpow hβ.ne'] at this
  · exact strictMonoOn_of_deriv_pos hD hc fun x hx => (hsign (hint ▸ hx)).2.1 hβ.2
  · refine concaveOn_of_deriv2_nonpos hD hc (fun x hx => ?_) (fun x hx => ?_) fun x hx => ?_
    · exact (hasDerivAt_secularSum_rpow hw hw0 β (hint ▸ hx)).differentiableAt
        |>.differentiableWithinAt
    · exact (hasDerivAt_deriv_secularSum_rpow hw hw0 β (hint ▸ hx)).differentiableAt
        |>.differentiableWithinAt
    · rw [← iteratedDeriv_eq_iterate]
      exact (hsign (hint ▸ hx)).2.2.2.1 hβ
  · have hp : Tendsto (secularSum μ w) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_secularSum_atTop,
        eventually_mem_secularDomain.mono fun x hx => secularSum_pos hw hw0 hx⟩
    exact (tendsto_rpow_neg_nhdsGT_zero hβ.2).comp hp

/-- The first-order Taylor expansion of the transformed secular function with Lagrange
remainder: `q(x + δ) = q(x) + q'(x) δ + q''(ξ) δ² / 2` for some `ξ ∈ secularDomain μ`. -/
theorem secularSum_rpow_add_eq {x δ : ℝ} (hx : x ∈ secularDomain μ)
    (hxδ : x + δ ∈ secularDomain μ) :
    ∃ ξ ∈ secularDomain μ, secularSum μ w (x + δ) ^ β = secularSum μ w x ^ β +
      deriv (fun y => secularSum μ w y ^ β) x * δ +
        iteratedDeriv 2 (fun y => secularSum μ w y ^ β) ξ * δ ^ 2 / 2 := by
  obtain ⟨ξ, hξ, h⟩ := exists_eq_sum_taylor_add isOpen_secularDomain convex_secularDomain
    (k := 1) (contDiffOn_secularSum_rpow hw hw0 β) hx hxδ
  refine ⟨ξ, hξ, ?_⟩
  rw [h]
  simp [Finset.sum_range_succ]

/-- **First-order Taylor estimates of the transformed secular function** (Cartis–Gould–Toint,
Theorem 8.2.5, in spectral form). Let the weights be nonnegative and not all zero, `x` and
`x + δ` in `secularDomain μ`, `q = fun y => secularSum μ w y ^ β` and `t₁ = q x + q'(x) δ`.
For `β > 0`, `q (x + δ) ≥ t₁`; for `β ∈ [-1/2, 0)`, `q (x + δ) ≤ t₁`. Both are strict when
`δ ≠ 0`, except when `β = -1/2` and the nonzero weights sit at a single pole: then
`q (x + δ) = t₁` (`q` is affine). The book's strictness claim omits both `δ ≠ 0` and this
exception. -/
theorem secularSum_rpow_tangent {x δ : ℝ} (hx : x ∈ secularDomain μ)
    (hxδ : x + δ ∈ secularDomain μ) :
    (0 < β → secularSum μ w x ^ β + deriv (fun y => secularSum μ w y ^ β) x * δ ≤
      secularSum μ w (x + δ) ^ β) ∧
    (0 < β → δ ≠ 0 → secularSum μ w x ^ β + deriv (fun y => secularSum μ w y ^ β) x * δ <
      secularSum μ w (x + δ) ^ β) ∧
    (β ∈ Ico (-1 / 2) 0 → secularSum μ w (x + δ) ^ β ≤
      secularSum μ w x ^ β + deriv (fun y => secularSum μ w y ^ β) x * δ) ∧
    (β ∈ Ico (-1 / 2) 0 → δ ≠ 0 → (β ≠ -1 / 2 ∨ ¬ SinglePole μ w) →
      secularSum μ w (x + δ) ^ β <
        secularSum μ w x ^ β + deriv (fun y => secularSum μ w y ^ β) x * δ) ∧
    (β = -1 / 2 → SinglePole μ w → secularSum μ w (x + δ) ^ β =
      secularSum μ w x ^ β + deriv (fun y => secularSum μ w y ^ β) x * δ) := by
  obtain ⟨ξ, hξ, h⟩ := secularSum_rpow_add_eq hw hw0 β hx hxδ
  have hsign := secularSum_rpow_deriv_sign hw hw0 β hξ
  have hδ2 : 0 ≤ δ ^ 2 := sq_nonneg δ
  refine ⟨fun hβ => ?_, fun hβ hδ => ?_, fun hβ => ?_, fun hβ hδ hne => ?_, fun hβ hs => ?_⟩
  · have := mul_nonneg (hsign.2.2.1 hβ).le hδ2
    linarith
  · have := mul_pos (hsign.2.2.1 hβ) (pow_pos (abs_pos.2 hδ) 2 |>.trans_eq (sq_abs δ))
    linarith
  · have := mul_nonpos_of_nonpos_of_nonneg (hsign.2.2.2.1 hβ) hδ2
    linarith
  · have := mul_neg_of_neg_of_pos (hsign.2.2.2.2.1 hβ hne)
      (pow_pos (abs_pos.2 hδ) 2 |>.trans_eq (sq_abs δ))
    linarith
  · rw [h, hsign.2.2.2.2.2 hβ hs]
    ring

end Rpow

/-! ### The Newton factor -/

/-- The `β`-dependent factor `(1 - μ ^ β) / β` of the Newton step for the transformed secular
equation `π(λ) ^ β = Δ ^ (2 β)` (book (B.8.7), and (8.2.26) with `ω = 0`), extended to `β = 0` by
its limit `-log μ`. Here `μ = Δ² / π(λ)` is a positive real number. -/
noncomputable def newtonFactor (μ β : ℝ) : ℝ :=
  if β = 0 then -Real.log μ else (1 - μ ^ β) / β

theorem newtonFactor_zero (μ : ℝ) : newtonFactor μ 0 = -Real.log μ := by simp [newtonFactor]

theorem newtonFactor_of_ne_zero (μ : ℝ) {β : ℝ} (hβ : β ≠ 0) :
    newtonFactor μ β = (1 - μ ^ β) / β := by simp [newtonFactor, hβ]

/-- `newtonFactor μ β` is minus the slope of `b ↦ μ ^ b` between `0` and `β`. -/
private theorem newtonFactor_eq_neg_slope {m β : ℝ} (hβ : β ≠ 0) :
    newtonFactor m β = -slope (fun b => m ^ b) 0 β := by
  rw [newtonFactor_of_ne_zero m hβ, slope_def_field, Real.rpow_zero, sub_zero]
  ring

/-- **Monotonicity of the transformed secular Newton step** (Cartis–Gould–Toint, Lemma B.8.2):
for `μ > 0`, `β ↦ newtonFactor μ β = (1 - μ ^ β) / β` is antitone on `ℝ`. Hence the Newton
correction `-(π / π') (1 - μ^β)/β` for `π(λ) ^ β = Δ ^ (2 β)` from `λc` (with `π' < 0`) decreases
as `β` increases. (The book's hypothesis about the root `λ*` is not needed.) -/
theorem antitone_newtonFactor {μ : ℝ} (hμ : 0 < μ) : Antitone (newtonFactor μ) := by
  have hconv := convexOn_rpow_left hμ
  have hmono := hconv.slope_mono (Set.mem_univ 0)
  -- tangent inequality at `0`: `μ ^ b ≥ 1 + b log μ`
  have htan : ∀ b : ℝ, 1 + b * Real.log μ ≤ μ ^ b := fun b => by
    rw [Real.rpow_def_of_pos hμ]
    linarith [Real.add_one_le_exp (Real.log μ * b), mul_comm b (Real.log μ)]
  intro a b hab
  rcases hab.eq_or_lt with rfl | hab
  · exact le_rfl
  by_cases ha : a = 0
  · subst ha
    have hb : 0 < b := hab
    rw [newtonFactor_zero, newtonFactor_of_ne_zero μ hb.ne', div_le_iff₀ hb]
    nlinarith [htan b]
  by_cases hb : b = 0
  · subst hb
    rw [newtonFactor_zero, newtonFactor_of_ne_zero μ ha, le_div_iff_of_neg hab]
    nlinarith [htan a]
  rw [newtonFactor_eq_neg_slope ha, newtonFactor_eq_neg_slope hb, neg_le_neg_iff]
  exact hmono ⟨Set.mem_univ _, ha⟩ ⟨Set.mem_univ _, hb⟩ hab.le

end Subproblem

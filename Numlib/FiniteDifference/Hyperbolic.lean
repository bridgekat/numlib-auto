import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.InnerProductSpace.l2Space
import Numlib.Analysis.Calculus.PartialDeriv
import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Analysis.PDE.Transport
import Numlib.FiniteDifference.Derivative
import Numlib.FiniteDifference.VonNeumann

/-!
# Finite difference schemes for the linear transport equation

The schemes of [quarteroni2000numerical] §13.7 for `u_t + a u_x = 0` on the grid `x_j = j Δx`,
`t^n = n Δt` with `λ = Δt / Δx`, and their analysis (§13.8–13.9). Every explicit scheme is a
`FiniteDifference.Stencil`, so the whole theory — the numerical domain of dependence, the discrete
maximum principle, the `ℓ^p` bounds, the amplification factors — comes from
`Numlib.FiniteDifference.Stencil` and `Numlib.FiniteDifference.VonNeumann` rather than being
re-derived for each scheme.

## The schemes

`Hyperbolic.forwardEulerCentred`, `Hyperbolic.laxFriedrichs`, `Hyperbolic.laxWendroff` and
`Hyperbolic.upwind` are the four explicit three-point stencils (13.37), (13.39), (13.40), (13.41).
Each is a conservative scheme `Stencil.ofFlux` for its numerical flux (13.36), and each of the last
three is the forward Euler/centred scheme plus an artificial viscosity
(`Hyperbolic.artificialViscosity`, (13.42)) with the coefficient `k` of Table 13.1. The implicit
backward Euler/centred scheme (13.43) is the inverse of `1 + (λa/2) D₀` on `ℓ²(ℤ)`
(`Hyperbolic.backwardEulerCentred`): the centred difference `D₀` is skew-adjoint
(`Hyperbolic.inner_centredDiffCLM_left`), so `1 + (λa/2) D₀` is coercive with constant `1` and its
inverse is a contraction — the unconditional `‖·‖_{Δ,2}` stability of §13.8.2. The leap-frog and
Newmark schemes (13.44)–(13.45) for the wave equation are the predicates `Hyperbolic.IsLeapFrog`
and `Hyperbolic.IsNewmark`.

## Consistency

The exact solution of `u_t + a u_x = 0` is the travelling wave `u₀(x - a t)`
(`Transport.IsSolution.eq_comp_sub`), so the local truncation error at a grid point is a
combination of values of the *single-variable* function `u₀` near the foot `ξ = x_j - a t^n` of the
characteristic: `Hyperbolic.truncationError`, with `Hyperbolic.truncationError_eq_of_isSolution`
the bridge to the two-variable form of §13.8.1. Taylor's theorem with the Lagrange remainder
(`FiniteDifference.abs_sub_sum_taylor_le`) then gives the `τ` column of Table 13.1 with explicit
constants: `O(Δt + Δx²)` for forward Euler/centred, `O(Δx²/Δt + Δt + Δx²)` for Lax–Friedrichs,
`O(Δt² + Δx²)` for Lax–Wendroff, `O(Δt + Δx)` for upwind. `Hyperbolic.IsOfOrder` and
`Hyperbolic.IsConsistent` are the definitions of §13.8.1, and `Hyperbolic.IsConvergent` is
convergence at the grid points.

## Stability and the CFL condition

`Hyperbolic.CFL a lam` is `|a λ| ≤ 1`. It is **necessary**: with `|a| λ > 1` the numerical domain
of dependence at `(0, 1)` misses the foot `-a` of the characteristic
(`Stencil.iterate_apply_congr_of_eqOn`), so a bump datum concentrated there defeats every
three-point family (`Hyperbolic.not_isConvergent_of_one_lt_abs_mul`). It is **not sufficient**:
the forward Euler/centred amplification factors `1 - iλa sin φ` exceed `1` in modulus for every
mesh, and the family is unstable at every `λ`
(`Hyperbolic.forwardEulerCentred_not_isStableFamily`) — so the "necessary and sufficient" of
§13.8.3 is an erratum. Sufficiency is scheme by scheme: upwind and Lax–Friedrichs are *monotone*
stencils under the CFL condition (`Hyperbolic.upwind_isMonotone`,
`Hyperbolic.laxFriedrichs_isMonotone`), hence nonexpansive in every `ℓ^p` and subject to the
discrete maximum principle (13.53); for the `ℓ²` analysis the amplification factors of the four
schemes are computed here and their moduli characterized (`Hyperbolic.amplificationFactor_upwind`
and the companions, with `…_le_one_iff` giving exactly `λ|a| ≤ 1`), so that Theorem 13.1
(`FiniteDifference.norm_toEuclideanLin_periodicScheme_pow_le`) applies.

## Dissipation and dispersion

The exact solution multiplies the `k`-th harmonic by `Hyperbolic.exactAmplification a Δt k =
e^{-i a k Δt}` per step, of modulus `1`; the scheme multiplies it by `γ_k`. The ratio of moduli is
the amplification (dissipation) error `Hyperbolic.amplificationError` and the ratio of the phase
speeds is the dispersion error `Hyperbolic.dispersionError`, both as in §13.9. The *equivalent*
(modified) equation `v_t + a v_x = μ v_xx + ν v_xxx` of §13.9.1 is `Hyperbolic.IsModifiedSolution`;
that a scheme is second- or third-order consistent *with it* is the content of
`Hyperbolic.residual` and the estimates over it.

Consumers beyond this book: any text on hyperbolic difference schemes states exactly these results
for exactly these schemes.
-/

open Set Filter Topology Finset Function Complex Matrix
open scoped Real ENNReal Nat

namespace FiniteDifference

namespace Hyperbolic

/-! ### The schemes of §13.7 -/

/-- **The forward Euler/centred scheme** ([quarteroni2000numerical] (13.37)):
`u_j^{n+1} = u_j^n - (λa/2)(u_{j+1}^n - u_{j-1}^n)`. -/
noncomputable def forwardEulerCentred (a lam : ℝ) : Stencil :=
  Stencil.threePoint (lam * a / 2) 1 (-(lam * a / 2))

/-- **The Lax–Friedrichs scheme** ([quarteroni2000numerical] (13.39)):
`u_j^{n+1} = ½(u_{j+1}^n + u_{j-1}^n) - (λa/2)(u_{j+1}^n - u_{j-1}^n)`. -/
noncomputable def laxFriedrichs (a lam : ℝ) : Stencil :=
  Stencil.threePoint ((1 + lam * a) / 2) 0 ((1 - lam * a) / 2)

/-- **The Lax–Wendroff scheme** ([quarteroni2000numerical] (13.40)):
`u_j^{n+1} = u_j^n - (λa/2)(u_{j+1}^n - u_{j-1}^n) + (λ²a²/2)(u_{j+1}^n - 2u_j^n + u_{j-1}^n)`. -/
noncomputable def laxWendroff (a lam : ℝ) : Stencil :=
  Stencil.threePoint (lam * a / 2 * (1 + lam * a)) (1 - (lam * a) ^ 2)
    (lam * a / 2 * (lam * a - 1))

/-- **The upwind scheme** ([quarteroni2000numerical] (13.41)):
`u_j^{n+1} = u_j^n - (λa/2)(u_{j+1}^n - u_{j-1}^n) + (λ|a|/2)(u_{j+1}^n - 2u_j^n + u_{j-1}^n)`. -/
noncomputable def upwind (a lam : ℝ) : Stencil :=
  Stencil.threePoint (lam * max a 0) (1 - lam * |a|) (lam * max (-a) 0)

/-- **The forward Euler/centred scheme with an artificial viscosity `k`**
([quarteroni2000numerical] (13.42)): `u_j^{n+1} = u_j^n - (λa/2)(u_{j+1}^n - u_{j-1}^n) +
(k/2)(u_{j+1}^n - 2u_j^n + u_{j-1}^n)/Δx²`. -/
noncomputable def artificialViscosity (a lam Δx k : ℝ) : Stencil :=
  Stencil.threePoint (lam * a / 2 + k / (2 * Δx ^ 2)) (1 - k / Δx ^ 2)
    (-(lam * a / 2) + k / (2 * Δx ^ 2))

/-- Three-point stencils with equal weights agree. -/
theorem threePoint_congr {cm c0 cp cm' c0' cp' : ℝ} (hm : cm = cm') (h0 : c0 = c0')
    (hp : cp = cp') : Stencil.threePoint cm c0 cp = Stencil.threePoint cm' c0' cp' := by
  rw [hm, h0, hp]

/-- `max a 0` is the positive part `(a + |a|)/2`. -/
theorem max_zero_eq (a : ℝ) : max a 0 = (a + |a|) / 2 := by
  rcases le_total 0 a with h | h
  · rw [max_eq_left h, abs_of_nonneg h]; ring
  · rw [max_eq_right h, abs_of_nonpos h]; ring

/-- The negative part: `max (-a) 0 = (|a| - a)/2`. -/
theorem max_neg_zero_eq (a : ℝ) : max (-a) 0 = (|a| - a) / 2 := by
  rw [max_zero_eq, abs_neg]; ring

/-- **The upwind scheme for a right-moving wave** ([quarteroni2000numerical] (13.50)):
for `a > 0` it reads `u_j^{n+1} = u_j^n - λa (u_j^n - u_{j-1}^n)`. -/
theorem upwind_eq_of_pos {a : ℝ} (ha : 0 < a) (lam : ℝ) :
    upwind a lam = Stencil.threePoint (lam * a) (1 - lam * a) 0 :=
  threePoint_congr (by rw [max_eq_left ha.le]) (by rw [abs_of_pos ha])
    (by rw [max_eq_right (by linarith), mul_zero])

/-- **The upwind scheme for a left-moving wave**: for `a < 0` it reads
`u_j^{n+1} = u_j^n - λa (u_{j+1}^n - u_j^n)` ([quarteroni2000numerical] §13.7.1). -/
theorem upwind_eq_of_neg {a : ℝ} (ha : a < 0) (lam : ℝ) :
    upwind a lam = Stencil.threePoint 0 (1 + lam * a) (-(lam * a)) :=
  threePoint_congr (by rw [max_eq_right ha.le, mul_zero]) (by rw [abs_of_neg ha]; ring)
    (by rw [max_eq_left (by linarith)]; ring)

/-! ### Numerical fluxes and artificial viscosities (Table 13.1) -/

/-- **The numerical flux of the forward Euler/centred scheme** ([quarteroni2000numerical]
(13.38)): `h(u, v) = ½a(u + v)`. -/
theorem forwardEulerCentred_eq_ofFlux (a lam : ℝ) :
    forwardEulerCentred a lam = Stencil.ofFlux lam (a / 2) (a / 2) :=
  threePoint_congr (by ring) (by ring) (by ring)

/-- **The numerical flux of the Lax–Friedrichs scheme** ([quarteroni2000numerical] §13.7.1):
`h(u, v) = ½[a(u + v) - λ⁻¹(v - u)]`. -/
theorem laxFriedrichs_eq_ofFlux {lam : ℝ} (hlam : lam ≠ 0) (a : ℝ) :
    laxFriedrichs a lam = Stencil.ofFlux lam (a / 2 + 1 / (2 * lam)) (a / 2 - 1 / (2 * lam)) :=
  threePoint_congr (by field_simp; try ring) (by field_simp; try ring) (by field_simp; try ring)

/-- **The numerical flux of the Lax–Wendroff scheme** ([quarteroni2000numerical] §13.7.1):
`h(u, v) = ½[a(u + v) - λa²(v - u)]`. -/
theorem laxWendroff_eq_ofFlux (a lam : ℝ) :
    laxWendroff a lam
      = Stencil.ofFlux lam (a / 2 + lam * a ^ 2 / 2) (a / 2 - lam * a ^ 2 / 2) :=
  threePoint_congr (by ring) (by ring) (by ring)

/-- **The numerical flux of the upwind scheme** ([quarteroni2000numerical] §13.7.1):
`h(u, v) = ½[a(u + v) - |a|(v - u)]`. -/
theorem upwind_eq_ofFlux (a lam : ℝ) :
    upwind a lam = Stencil.ofFlux lam ((a + |a|) / 2) ((a - |a|) / 2) :=
  threePoint_congr (by rw [max_zero_eq]; try ring) (by ring)
    (by rw [max_neg_zero_eq]; try ring)

/-- **Lax–Friedrichs is forward Euler/centred with artificial viscosity `k = Δx²`**
([quarteroni2000numerical] Table 13.1). -/
theorem laxFriedrichs_eq_artificialViscosity {Δx : ℝ} (hΔx : Δx ≠ 0) (a lam : ℝ) :
    laxFriedrichs a lam = artificialViscosity a lam Δx (Δx ^ 2) :=
  threePoint_congr (by field_simp; try ring) (by field_simp; try ring) (by field_simp; try ring)

/-- **Lax–Wendroff is forward Euler/centred with artificial viscosity `k = a²Δt²`**
([quarteroni2000numerical] Table 13.1). -/
theorem laxWendroff_eq_artificialViscosity {Δt Δx lam : ℝ} (hΔx : Δx ≠ 0) (hlam : lam = Δt / Δx)
    (a : ℝ) : laxWendroff a lam = artificialViscosity a lam Δx (a ^ 2 * Δt ^ 2) := by
  subst hlam
  exact threePoint_congr (by field_simp; try ring) (by field_simp; try ring)
    (by field_simp; try ring)

/-- **Upwind is forward Euler/centred with artificial viscosity `k = |a| Δx Δt`**
([quarteroni2000numerical] Table 13.1). -/
theorem upwind_eq_artificialViscosity {Δt Δx lam : ℝ} (hΔx : Δx ≠ 0) (hlam : lam = Δt / Δx)
    (a : ℝ) : upwind a lam = artificialViscosity a lam Δx (|a| * Δx * Δt) := by
  subst hlam
  exact threePoint_congr (by rw [max_zero_eq]; field_simp; try ring) (by field_simp; try ring)
    (by rw [max_neg_zero_eq]; field_simp; try ring)

/-! ### Monotone schemes and the discrete maximum principle -/

/-- The coefficients of a three-point stencil, at an arbitrary grid offset.

TODO(backbone): this belongs beside `FiniteDifference.Stencil.threePoint`. -/
theorem threePoint_coe_apply (cm c0 cp : ℝ) (s : ℤ) :
    Stencil.threePoint cm c0 cp s
      = (if 1 = s then cm else 0) + (if 0 = s then c0 else 0) + (if -1 = s then cp else 0) := by
  simp [Stencil.threePoint, Finsupp.single_apply]

/-- **A three-point stencil with nonnegative weights summing to one is monotone**.

TODO(backbone): this belongs beside `FiniteDifference.Stencil.IsMonotone`. -/
theorem isMonotone_threePoint {cm c0 cp : ℝ} (hm : 0 ≤ cm) (h0 : 0 ≤ c0) (hp : 0 ≤ cp)
    (hsum : cm + c0 + cp = 1) : Stencil.IsMonotone (Stencil.threePoint cm c0 cp) := by
  refine ⟨fun s => ?_, by rw [Stencil.threePoint_sum]; exact hsum⟩
  rw [threePoint_coe_apply]
  split_ifs <;> linarith

/-- **The upwind scheme is monotone under the CFL condition**
([quarteroni2000numerical] §13.8.3): its weights are then nonnegative and sum to `1`, so it obeys
the discrete maximum principle (13.53) and is nonexpansive in every `ℓ^p`. -/
theorem upwind_isMonotone {a lam : ℝ} (h0 : 0 ≤ lam * |a|) (h1 : lam * |a| ≤ 1) :
    Stencil.IsMonotone (upwind a lam) := by
  have hsum : lam * max a 0 + (1 - lam * |a|) + lam * max (-a) 0 = 1 := by
    rw [max_zero_eq, max_neg_zero_eq]; ring
  rcases le_total a 0 with ha | ha
  · have e1 : max a 0 = 0 := max_eq_right ha
    have e2 : max (-a) 0 = |a| := by rw [max_neg_zero_eq, abs_of_nonpos ha]; ring
    exact isMonotone_threePoint (by rw [e1, mul_zero]) (by linarith) (by rw [e2]; exact h0) hsum
  · have e1 : max a 0 = a := max_eq_left ha
    have e2 : max (-a) 0 = 0 := max_eq_right (by linarith)
    have e3 : |a| = a := abs_of_nonneg ha
    exact isMonotone_threePoint (by rw [e1, ← e3]; exact h0) (by linarith)
      (by rw [e2, mul_zero]) hsum

/-- **The Lax–Friedrichs scheme is monotone under the CFL condition**
([quarteroni2000numerical] §13.8.3): the weights `(1 ± λa)/2` are nonnegative and sum to `1`. -/
theorem laxFriedrichs_isMonotone {a lam : ℝ} (h : |lam * a| ≤ 1) :
    Stencil.IsMonotone (laxFriedrichs a lam) := by
  rw [abs_le] at h
  exact isMonotone_threePoint (by linarith [h.1]) le_rfl (by linarith [h.2]) (by ring)

/-! ### Taylor expansions of the initial datum -/

/-- The triangle inequality for a difference. -/
private theorem abs_sub_le' (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  calc |x - y| = |x + -y| := by rw [sub_eq_add_neg]
    _ ≤ |x| + |-y| := abs_add_le _ _
    _ = |x| + |y| := by rw [abs_neg]

/-- **Taylor's theorem with a uniform remainder bound on the whole line**: for `g` of class
`C^{n+1}` with `|g^{(n+1)}| ≤ M` everywhere,
`|g (ξ + h) - ∑_{k ≤ n} h^k/k! g^{(k)}(ξ)| ≤ M |h|^{n+1}/(n+1)!`. -/
theorem abs_sub_sum_taylor_le_of_contDiff {g : ℝ → ℝ} {n : ℕ} {M : ℝ}
    (hg : ContDiff ℝ (n + 1) g) (hM : ∀ y, |iteratedDeriv (n + 1) g y| ≤ M) (ξ h : ℝ) :
    |g (ξ + h) - ∑ k ∈ Finset.range (n + 1), h ^ k / k ! * iteratedDeriv k g ξ|
      ≤ M * |h| ^ (n + 1) / (n + 1)! := by
  have hmem : ξ + h ∈ Metric.ball ξ (|h| + 1) := by
    have hd : dist (ξ + h) ξ = |h| := by rw [Real.dist_eq]; ring_nf
    rw [Metric.mem_ball, hd]
    linarith
  have h1 := FiniteDifference.abs_sub_sum_taylor_le (f := g) (x₀ := ξ) (n := n) (ε := |h| + 1)
    hg.contDiffOn (fun t _ => hM t) hmem
  simpa using h1

/-- **First-order Taylor**: `|g (ξ + h) - g ξ - h g'(ξ)| ≤ M h²/2` for `|g''| ≤ M`. -/
theorem abs_taylor_one {g : ℝ → ℝ} {M : ℝ} (hg : ContDiff ℝ 2 g)
    (hM : ∀ y, |iteratedDeriv 2 g y| ≤ M) (ξ h : ℝ) :
    |g (ξ + h) - g ξ - h * deriv g ξ| ≤ M * h ^ 2 / 2 := by
  have hg' : ContDiff ℝ ((1 : ℕ) + 1) g := by norm_num; exact hg
  have hM' : ∀ y, |iteratedDeriv ((1 : ℕ) + 1) g y| ≤ M := by norm_num; exact hM
  have h1 := abs_sub_sum_taylor_le_of_contDiff hg' hM' ξ h
  have hsum : ∑ k ∈ Finset.range ((1 : ℕ) + 1), h ^ k / k ! * iteratedDeriv k g ξ
      = g ξ + h * deriv g ξ := by
    rw [Finset.sum_range_succ, Finset.sum_range_one, iteratedDeriv_zero, iteratedDeriv_one]
    norm_num [Nat.factorial]
  rw [hsum, ← sub_sub] at h1
  calc |g (ξ + h) - g ξ - h * deriv g ξ| ≤ M * |h| ^ ((1 : ℕ) + 1) / ((1 : ℕ) + 1)! := h1
    _ = M * h ^ 2 / 2 := by norm_num [sq_abs]

/-- **Second-order Taylor**: `|g (ξ + h) - g ξ - h g' - h²/2 g''| ≤ M |h|³/6` for `|g'''| ≤ M`. -/
theorem abs_taylor_two {g : ℝ → ℝ} {M : ℝ} (hg : ContDiff ℝ 3 g)
    (hM : ∀ y, |iteratedDeriv 3 g y| ≤ M) (ξ h : ℝ) :
    |g (ξ + h) - g ξ - h * deriv g ξ - h ^ 2 / 2 * iteratedDeriv 2 g ξ| ≤ M * |h| ^ 3 / 6 := by
  have hg' : ContDiff ℝ ((2 : ℕ) + 1) g := by norm_num; exact hg
  have hM' : ∀ y, |iteratedDeriv ((2 : ℕ) + 1) g y| ≤ M := by norm_num; exact hM
  have h1 := abs_sub_sum_taylor_le_of_contDiff hg' hM' ξ h
  have hsum : ∑ k ∈ Finset.range ((2 : ℕ) + 1), h ^ k / k ! * iteratedDeriv k g ξ
      = g ξ + h * deriv g ξ + h ^ 2 / 2 * iteratedDeriv 2 g ξ := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, iteratedDeriv_zero,
      iteratedDeriv_one]
    norm_num [Nat.factorial]
  rw [hsum, ← sub_sub, ← sub_sub] at h1
  calc |g (ξ + h) - g ξ - h * deriv g ξ - h ^ 2 / 2 * iteratedDeriv 2 g ξ|
      ≤ M * |h| ^ ((2 : ℕ) + 1) / ((2 : ℕ) + 1)! := h1
    _ = M * |h| ^ 3 / 6 := by norm_num

/-- **Third-order Taylor**: `|g (ξ + h) - g ξ - h g' - h²/2 g'' - h³/6 g'''| ≤ M h⁴/24` for a
fourth derivative bounded by `M`. -/
theorem abs_taylor_three {g : ℝ → ℝ} {M : ℝ} (hg : ContDiff ℝ 4 g)
    (hM : ∀ y, |iteratedDeriv 4 g y| ≤ M) (ξ h : ℝ) :
    |g (ξ + h) - g ξ - h * deriv g ξ - h ^ 2 / 2 * iteratedDeriv 2 g ξ
      - h ^ 3 / 6 * iteratedDeriv 3 g ξ| ≤ M * h ^ 4 / 24 := by
  have hg' : ContDiff ℝ ((3 : ℕ) + 1) g := by norm_num; exact hg
  have hM' : ∀ y, |iteratedDeriv ((3 : ℕ) + 1) g y| ≤ M := by norm_num; exact hM
  have h1 := abs_sub_sum_taylor_le_of_contDiff hg' hM' ξ h
  have hsum : ∑ k ∈ Finset.range ((3 : ℕ) + 1), h ^ k / k ! * iteratedDeriv k g ξ
      = g ξ + h * deriv g ξ + h ^ 2 / 2 * iteratedDeriv 2 g ξ
        + h ^ 3 / 6 * iteratedDeriv 3 g ξ := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      iteratedDeriv_zero, iteratedDeriv_one]
    norm_num [Nat.factorial]
    try ring
  rw [hsum, ← sub_sub, ← sub_sub, ← sub_sub] at h1
  calc |g (ξ + h) - g ξ - h * deriv g ξ - h ^ 2 / 2 * iteratedDeriv 2 g ξ
        - h ^ 3 / 6 * iteratedDeriv 3 g ξ|
      ≤ M * |h| ^ ((3 : ℕ) + 1) / ((3 : ℕ) + 1)! := h1
    _ = M * h ^ 4 / 24 := by
        rw [show |h| ^ ((3 : ℕ) + 1) = h ^ 4 by
          rw [show (3 : ℕ) + 1 = 4 from rfl, ← abs_pow,
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ h ^ 4)]]
        norm_num

/-! ### The local truncation error -/

/-- **The local truncation error** of the scheme `c` for `u_t + a u_x = 0` on the exact solution
`u₀(x - a t)`, at the grid point whose characteristic foot is `ξ`
([quarteroni2000numerical] §13.8.1). -/
noncomputable def truncationError (c : Stencil) (a Δt Δx : ℝ) (u₀ : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  (u₀ (ξ - a * Δt) - Stencil.apply c (fun i : ℤ => u₀ (ξ + i * Δx)) 0) / Δt

/-- The truncation error of a three-point stencil, written out. -/
theorem truncationError_threePoint (cm c0 cp a Δt Δx : ℝ) (u₀ : ℝ → ℝ) (ξ : ℝ) :
    truncationError (Stencil.threePoint cm c0 cp) a Δt Δx u₀ ξ
      = (u₀ (ξ - a * Δt) - (cm * u₀ (ξ - Δx) + c0 * u₀ ξ + cp * u₀ (ξ + Δx))) / Δt := by
  rw [truncationError, Stencil.threePoint_apply]
  simp only [smul_eq_mul]
  push_cast
  ring_nf

/-- **The truncation error is the residual left by the exact solution**
([quarteroni2000numerical] §13.8.1): with `ξ = x_j - a t^n` the foot of the characteristic through
the grid point `(x_j, t^n)`, `τ = (u(x_j, t^{n+1}) - (c u(·, t^n))_j) / Δt` for the solution `u` of
`u_t + a u_x = 0`. -/
theorem truncationError_eq_of_isSolution {a : ℝ} {u₀ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hu : Transport.IsSolution (fun _ _ => a) 0 0 u₀ u) (c : Stencil) {Δt Δx : ℝ} (hΔt : 0 ≤ Δt)
    (j : ℤ) (n : ℕ) :
    truncationError c a Δt Δx u₀ ((j : ℝ) * Δx - a * (n * Δt))
      = (u ((j : ℝ) * Δx) (((n : ℝ) + 1) * Δt)
          - Stencil.apply c (fun i : ℤ => u ((i : ℝ) * Δx) (n * Δt)) j) / Δt := by
  have hn : (0 : ℝ) ≤ n * Δt := mul_nonneg (Nat.cast_nonneg n) hΔt
  have hn1 : (0 : ℝ) ≤ ((n : ℝ) + 1) * Δt := by positivity
  rw [truncationError, hu.eq_comp_sub _ hn1]
  congr 2
  · congr 1
    ring
  · rw [Stencil.apply_apply, Stencil.apply_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hu.eq_comp_sub _ hn]
    congr 2
    push_cast
    ring

/-! ### Consistency, order and convergence -/

/-- **The scheme family `c` is of order `p` in time and `q` in space** for the datum `u₀`
([quarteroni2000numerical] §13.8.1): the truncation error is `O(Δt^p + Δx^q)`, uniformly in the
grid point, for all small steps. -/
def IsOfOrder (c : ℝ → ℝ → Stencil) (a : ℝ) (u₀ : ℝ → ℝ) (p q : ℕ) : Prop :=
  ∃ C δ₀ : ℝ, 0 < δ₀ ∧ ∀ Δt Δx : ℝ, 0 < Δt → Δt ≤ δ₀ → 0 < Δx → Δx ≤ δ₀ → ∀ ξ : ℝ,
    |truncationError (c Δt Δx) a Δt Δx u₀ ξ| ≤ C * (Δt ^ p + Δx ^ q)

/-- **Consistency** ([quarteroni2000numerical] §13.8.1): the truncation error
`τ(Δt, Δx) = sup_ξ |τ_ξ|` tends to `0` as `Δt` and `Δx` tend to `0` independently. -/
def IsConsistent (c : ℝ → ℝ → Stencil) (a : ℝ) (u₀ : ℝ → ℝ) : Prop :=
  Tendsto (fun d : ℝ × ℝ => ⨆ ξ : ℝ, |truncationError (c d.1 d.2) a d.1 d.2 u₀ ξ|)
    (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0)

/-- **A scheme of positive order is consistent** ([quarteroni2000numerical] §13.8.1). -/
theorem IsOfOrder.isConsistent {c : ℝ → ℝ → Stencil} {a : ℝ} {u₀ : ℝ → ℝ} {p q : ℕ}
    (hp : p ≠ 0) (hq : q ≠ 0) (h : IsOfOrder c a u₀ p q) : IsConsistent c a u₀ := by
  obtain ⟨C, δ₀, hδ₀, hC⟩ := h
  have hpos : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), 0 < x := self_mem_nhdsWithin
  have hle : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), x ≤ δ₀ := by
    refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
    filter_upwards [Ioo_mem_nhds (by linarith : -δ₀ < (0 : ℝ)) hδ₀] with x hx using hx.2.le
  have hone : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), 0 < x ∧ x ≤ δ₀ := hpos.and hle
  refine squeeze_zero' (g := fun d : ℝ × ℝ => C * (d.1 ^ p + d.2 ^ q))
    (Filter.Eventually.of_forall fun d => Real.iSup_nonneg fun _ => abs_nonneg _) ?_ ?_
  · filter_upwards [hone.prod_mk hone] with d hd
    exact ciSup_le fun ξ => hC d.1 d.2 hd.1.1 hd.1.2 hd.2.1 hd.2.2 ξ
  · have h1 : Tendsto (fun d : ℝ × ℝ => d.1 ^ p) (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h := (continuous_pow p).continuousAt.tendsto.comp
        ((tendsto_fst (f := 𝓝[>] (0 : ℝ)) (g := 𝓝[>] (0 : ℝ))).mono_right nhdsWithin_le_nhds)
      simpa [Function.comp_def, zero_pow hp] using h
    have h2 : Tendsto (fun d : ℝ × ℝ => d.2 ^ q) (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h := (continuous_pow q).continuousAt.tendsto.comp
        ((tendsto_snd (f := 𝓝[>] (0 : ℝ)) (g := 𝓝[>] (0 : ℝ))).mono_right nhdsWithin_le_nhds)
      simpa [Function.comp_def, zero_pow hq] using h
    simpa using ((h1.add h2).const_mul C)

/-- **Convergence of a scheme family** at the grid points, over the horizon `T`
([quarteroni2000numerical] §13.8.1): the iterates started from the sampled datum approach the
exact solution `u₀(x - a t)` uniformly on the grid. -/
def IsConvergent (a : ℝ) (u₀ : ℝ → ℝ) (c : ℝ → ℝ → Stencil) (T : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ₀ > 0, ∀ Δt Δx : ℝ, 0 < Δt → Δt ≤ δ₀ → 0 < Δx → Δx ≤ δ₀ → ∀ (n : ℕ) (j : ℤ),
    (n : ℝ) * Δt ≤ T →
      |u₀ ((j : ℝ) * Δx - a * (n * Δt))
        - (Stencil.apply (c Δt Δx))^[n] (fun i : ℤ => u₀ ((i : ℝ) * Δx)) j| ≤ ε

/-! ### The truncation errors of the four schemes (Table 13.1) -/

section Truncation

variable {u₀ : ℝ → ℝ} {M₂ M₃ M₄ a Δt Δx lam ξ : ℝ}

/-- The remainder of the first-order expansion at the foot of the characteristic. -/
private theorem abs_timeRemainder_one_le (hu : ContDiff ℝ 2 u₀)
    (hM₂ : ∀ y, |iteratedDeriv 2 u₀ y| ≤ M₂) (b s z : ℝ) :
    |u₀ (z - b * s) - u₀ z + b * s * deriv u₀ z| ≤ M₂ * (b * s) ^ 2 / 2 := by
  have hb := abs_taylor_one hu hM₂ z (-(b * s))
  rw [show z + -(b * s) = z - b * s from by ring,
    show u₀ (z - b * s) - u₀ z - -(b * s) * deriv u₀ z
      = u₀ (z - b * s) - u₀ z + b * s * deriv u₀ z from by ring,
    show (-(b * s)) ^ 2 = (b * s) ^ 2 from by ring] at hb
  exact hb

/-- The remainder of the second-order expansion at `z - w`. -/
private theorem abs_spaceRemainder_two_left_le (hu : ContDiff ℝ 3 u₀)
    (hM₃ : ∀ y, |iteratedDeriv 3 u₀ y| ≤ M₃) {w : ℝ} (hw : 0 < w) (z : ℝ) :
    |u₀ (z - w) - u₀ z + w * deriv u₀ z - w ^ 2 / 2 * iteratedDeriv 2 u₀ z|
      ≤ M₃ * w ^ 3 / 6 := by
  have hb := abs_taylor_two hu hM₃ z (-w)
  rw [show z + -w = z - w from by ring,
    show u₀ (z - w) - u₀ z - -w * deriv u₀ z - (-w) ^ 2 / 2 * iteratedDeriv 2 u₀ z
      = u₀ (z - w) - u₀ z + w * deriv u₀ z - w ^ 2 / 2 * iteratedDeriv 2 u₀ z from by ring,
    abs_neg, abs_of_pos hw] at hb
  exact hb

/-- The remainder of the second-order expansion at `z + w`. -/
private theorem abs_spaceRemainder_two_right_le (hu : ContDiff ℝ 3 u₀)
    (hM₃ : ∀ y, |iteratedDeriv 3 u₀ y| ≤ M₃) {w : ℝ} (hw : 0 < w) (z : ℝ) :
    |u₀ (z + w) - u₀ z - w * deriv u₀ z - w ^ 2 / 2 * iteratedDeriv 2 u₀ z|
      ≤ M₃ * w ^ 3 / 6 := by
  have hb := abs_taylor_two hu hM₃ z w
  rwa [abs_of_pos hw] at hb

/-- **The truncation error of the forward Euler/centred scheme**
([quarteroni2000numerical] Table 13.1): it is `O(Δt + Δx²)`. -/
theorem abs_truncationError_forwardEulerCentred_le (hu : ContDiff ℝ 3 u₀)
    (hM₂ : ∀ y, |iteratedDeriv 2 u₀ y| ≤ M₂) (hM₃ : ∀ y, |iteratedDeriv 3 u₀ y| ≤ M₃)
    (hΔt : 0 < Δt) (hΔx : 0 < Δx) (hlam : lam = Δt / Δx) (ξ : ℝ) :
    |truncationError (forwardEulerCentred a lam) a Δt Δx u₀ ξ|
      ≤ a ^ 2 / 2 * M₂ * Δt + |a| / 6 * M₃ * Δx ^ 2 := by
  subst hlam
  have hu2 : ContDiff ℝ 2 u₀ := hu.of_le (by norm_num)
  have hΔt' : Δt ≠ 0 := ne_of_gt hΔt
  have hΔx' : Δx ≠ 0 := ne_of_gt hΔx
  have hM₃0 : 0 ≤ M₃ := (abs_nonneg _).trans (hM₃ 0)
  have hR := abs_timeRemainder_one_le hu2 hM₂ a Δt ξ
  have hQ := abs_spaceRemainder_two_left_le hu hM₃ hΔx ξ
  have hP := abs_spaceRemainder_two_right_le hu hM₃ hΔx ξ
  have hid : truncationError (forwardEulerCentred a (Δt / Δx)) a Δt Δx u₀ ξ * Δt
      = (u₀ (ξ - a * Δt) - u₀ ξ + a * Δt * deriv u₀ ξ)
        - Δt / Δx * a / 2
          * ((u₀ (ξ - Δx) - u₀ ξ + Δx * deriv u₀ ξ - Δx ^ 2 / 2 * iteratedDeriv 2 u₀ ξ)
            - (u₀ (ξ + Δx) - u₀ ξ - Δx * deriv u₀ ξ - Δx ^ 2 / 2 * iteratedDeriv 2 u₀ ξ)) := by
    rw [forwardEulerCentred, truncationError_threePoint]
    field_simp
    ring
  refine le_of_mul_le_mul_right ?_ hΔt
  calc |truncationError (forwardEulerCentred a (Δt / Δx)) a Δt Δx u₀ ξ| * Δt
      = |truncationError (forwardEulerCentred a (Δt / Δx)) a Δt Δx u₀ ξ * Δt| := by
        rw [abs_mul, abs_of_pos hΔt]
    _ ≤ M₂ * (a * Δt) ^ 2 / 2 + Δt / Δx * |a| / 2 * (M₃ * Δx ^ 3 / 6 + M₃ * Δx ^ 3 / 6) := by
        rw [hid]
        refine (abs_sub_le' _ _).trans ?_
        rw [abs_mul, show |Δt / Δx * a / 2| = Δt / Δx * |a| / 2 by
          rw [abs_div, abs_mul, abs_div, abs_of_pos hΔt, abs_of_pos hΔx]; norm_num]
        gcongr
        exact (abs_sub_le' _ _).trans (by gcongr)
    _ = (a ^ 2 / 2 * M₂ * Δt + |a| / 6 * M₃ * Δx ^ 2) * Δt := by field_simp; try ring

/-- **The truncation error of the Lax–Friedrichs scheme** ([quarteroni2000numerical] Table 13.1):
it is `O(Δx²/Δt + Δt + Δx²)`, and so is consistent only if `Δx²/Δt → 0`. -/
theorem abs_truncationError_laxFriedrichs_le (hu : ContDiff ℝ 3 u₀)
    (hM₂ : ∀ y, |iteratedDeriv 2 u₀ y| ≤ M₂) (hM₃ : ∀ y, |iteratedDeriv 3 u₀ y| ≤ M₃)
    (hΔt : 0 < Δt) (hΔx : 0 < Δx) (hlam : lam = Δt / Δx) (ξ : ℝ) :
    |truncationError (laxFriedrichs a lam) a Δt Δx u₀ ξ|
      ≤ M₂ / 2 * Δx ^ 2 / Δt + a ^ 2 / 2 * M₂ * Δt + |a| / 6 * M₃ * Δx ^ 2 := by
  subst hlam
  have hu2 : ContDiff ℝ 2 u₀ := hu.of_le (by norm_num)
  have hΔt' : Δt ≠ 0 := ne_of_gt hΔt
  have hΔx' : Δx ≠ 0 := ne_of_gt hΔx
  have hM₂0 : 0 ≤ M₂ := (abs_nonneg _).trans (hM₂ 0)
  have hM₃0 : 0 ≤ M₃ := (abs_nonneg _).trans (hM₃ 0)
  have hR := abs_timeRemainder_one_le hu2 hM₂ a Δt ξ
  have hQ := abs_spaceRemainder_two_left_le hu hM₃ hΔx ξ
  have hP := abs_spaceRemainder_two_right_le hu hM₃ hΔx ξ
  have hT : |u₀ (ξ - Δx) - u₀ ξ + Δx * deriv u₀ ξ| ≤ M₂ * Δx ^ 2 / 2 := by
    simpa using abs_timeRemainder_one_le hu2 hM₂ 1 Δx ξ
  have hS : |u₀ (ξ + Δx) - u₀ ξ - Δx * deriv u₀ ξ| ≤ M₂ * Δx ^ 2 / 2 :=
    abs_taylor_one hu2 hM₂ ξ Δx
  have hid : truncationError (laxFriedrichs a (Δt / Δx)) a Δt Δx u₀ ξ * Δt
      = (u₀ (ξ - a * Δt) - u₀ ξ + a * Δt * deriv u₀ ξ)
        - ((u₀ (ξ + Δx) - u₀ ξ - Δx * deriv u₀ ξ)
            + (u₀ (ξ - Δx) - u₀ ξ + Δx * deriv u₀ ξ)) / 2
        + Δt / Δx * a / 2
          * ((u₀ (ξ + Δx) - u₀ ξ - Δx * deriv u₀ ξ - Δx ^ 2 / 2 * iteratedDeriv 2 u₀ ξ)
            - (u₀ (ξ - Δx) - u₀ ξ + Δx * deriv u₀ ξ - Δx ^ 2 / 2 * iteratedDeriv 2 u₀ ξ)) := by
    rw [laxFriedrichs, truncationError_threePoint]
    field_simp
    ring
  refine le_of_mul_le_mul_right ?_ hΔt
  calc |truncationError (laxFriedrichs a (Δt / Δx)) a Δt Δx u₀ ξ| * Δt
      = |truncationError (laxFriedrichs a (Δt / Δx)) a Δt Δx u₀ ξ * Δt| := by
        rw [abs_mul, abs_of_pos hΔt]
    _ ≤ M₂ * (a * Δt) ^ 2 / 2 + (M₂ * Δx ^ 2 / 2 + M₂ * Δx ^ 2 / 2) / 2
        + Δt / Δx * |a| / 2 * (M₃ * Δx ^ 3 / 6 + M₃ * Δx ^ 3 / 6) := by
        rw [hid]
        refine (abs_add_le _ _).trans (add_le_add ((abs_sub_le' _ _).trans ?_) ?_)
        · refine add_le_add hR ?_
          rw [abs_div, show |(2 : ℝ)| = 2 from abs_of_pos two_pos]
          gcongr
          exact (abs_add_le _ _).trans (add_le_add hS hT)
        · rw [abs_mul, show |Δt / Δx * a / 2| = Δt / Δx * |a| / 2 by
            rw [abs_div, abs_mul, abs_div, abs_of_pos hΔt, abs_of_pos hΔx]; norm_num]
          gcongr
          exact (abs_sub_le' _ _).trans (by gcongr)
    _ = (M₂ / 2 * Δx ^ 2 / Δt + a ^ 2 / 2 * M₂ * Δt + |a| / 6 * M₃ * Δx ^ 2) * Δt := by
        field_simp; try ring

/-- **The truncation error of the upwind scheme** ([quarteroni2000numerical] Table 13.1): it is
`O(Δt + Δx)`. -/
theorem abs_truncationError_upwind_le (hu : ContDiff ℝ 2 u₀)
    (hM₂ : ∀ y, |iteratedDeriv 2 u₀ y| ≤ M₂) (hΔt : 0 < Δt) (hΔx : 0 < Δx)
    (hlam : lam = Δt / Δx) (ξ : ℝ) :
    |truncationError (upwind a lam) a Δt Δx u₀ ξ|
      ≤ a ^ 2 / 2 * M₂ * Δt + |a| / 2 * M₂ * Δx := by
  subst hlam
  have hΔt' : Δt ≠ 0 := ne_of_gt hΔt
  have hΔx' : Δx ≠ 0 := ne_of_gt hΔx
  have hM₂0 : 0 ≤ M₂ := (abs_nonneg _).trans (hM₂ 0)
  have hR := abs_timeRemainder_one_le hu hM₂ a Δt ξ
  have hT : |u₀ (ξ - Δx) - u₀ ξ + Δx * deriv u₀ ξ| ≤ M₂ * Δx ^ 2 / 2 := by
    simpa using abs_timeRemainder_one_le hu hM₂ 1 Δx ξ
  have hS : |u₀ (ξ + Δx) - u₀ ξ - Δx * deriv u₀ ξ| ≤ M₂ * Δx ^ 2 / 2 := abs_taylor_one hu hM₂ ξ Δx
  rcases lt_trichotomy a 0 with ha | ha | ha
  · have hid : truncationError (upwind a (Δt / Δx)) a Δt Δx u₀ ξ * Δt
        = (u₀ (ξ - a * Δt) - u₀ ξ + a * Δt * deriv u₀ ξ)
          + Δt / Δx * a * (u₀ (ξ + Δx) - u₀ ξ - Δx * deriv u₀ ξ) := by
      rw [upwind_eq_of_neg ha, truncationError_threePoint]
      field_simp
      ring
    refine le_of_mul_le_mul_right ?_ hΔt
    calc |truncationError (upwind a (Δt / Δx)) a Δt Δx u₀ ξ| * Δt
        = |truncationError (upwind a (Δt / Δx)) a Δt Δx u₀ ξ * Δt| := by
          rw [abs_mul, abs_of_pos hΔt]
      _ ≤ M₂ * (a * Δt) ^ 2 / 2 + Δt / Δx * |a| * (M₂ * Δx ^ 2 / 2) := by
          rw [hid]
          refine (abs_add_le _ _).trans (add_le_add hR ?_)
          rw [abs_mul, show |Δt / Δx * a| = Δt / Δx * |a| by
            rw [abs_mul, abs_div, abs_of_pos hΔt, abs_of_pos hΔx]]
          gcongr
      _ = (a ^ 2 / 2 * M₂ * Δt + |a| / 2 * M₂ * Δx) * Δt := by field_simp; try ring
  · subst ha
    have hid : truncationError (upwind 0 (Δt / Δx)) 0 Δt Δx u₀ ξ = 0 := by
      rw [upwind, truncationError_threePoint]
      norm_num
    rw [hid, abs_zero]
    positivity
  · have hid : truncationError (upwind a (Δt / Δx)) a Δt Δx u₀ ξ * Δt
        = (u₀ (ξ - a * Δt) - u₀ ξ + a * Δt * deriv u₀ ξ)
          - Δt / Δx * a * (u₀ (ξ - Δx) - u₀ ξ + Δx * deriv u₀ ξ) := by
      rw [upwind_eq_of_pos ha, truncationError_threePoint]
      field_simp
      ring
    refine le_of_mul_le_mul_right ?_ hΔt
    calc |truncationError (upwind a (Δt / Δx)) a Δt Δx u₀ ξ| * Δt
        = |truncationError (upwind a (Δt / Δx)) a Δt Δx u₀ ξ * Δt| := by
          rw [abs_mul, abs_of_pos hΔt]
      _ ≤ M₂ * (a * Δt) ^ 2 / 2 + Δt / Δx * |a| * (M₂ * Δx ^ 2 / 2) := by
          rw [hid]
          refine (abs_sub_le' _ _).trans (add_le_add hR ?_)
          rw [abs_mul, show |Δt / Δx * a| = Δt / Δx * |a| by
            rw [abs_mul, abs_div, abs_of_pos hΔt, abs_of_pos hΔx]]
          gcongr
      _ = (a ^ 2 / 2 * M₂ * Δt + |a| / 2 * M₂ * Δx) * Δt := by field_simp; try ring

/-- **The truncation error of the Lax–Wendroff scheme** ([quarteroni2000numerical] Table 13.1):
it is `O(Δt² + Δx²)`, the only second-order scheme of §13.7. -/
theorem abs_truncationError_laxWendroff_le (hu : ContDiff ℝ 4 u₀)
    (hM₃ : ∀ y, |iteratedDeriv 3 u₀ y| ≤ M₃) (hM₄ : ∀ y, |iteratedDeriv 4 u₀ y| ≤ M₄)
    (hΔt : 0 < Δt) (hΔt1 : Δt ≤ 1) (hΔx : 0 < Δx) (hΔx1 : Δx ≤ 1) (hlam : lam = Δt / Δx) (ξ : ℝ) :
    |truncationError (laxWendroff a lam) a Δt Δx u₀ ξ|
      ≤ |a| ^ 3 / 6 * M₃ * Δt ^ 2 + (|a| / 6 * M₃ + (|a| + a ^ 2) / 24 * M₄) * Δx ^ 2 := by
  subst hlam
  have hu3 : ContDiff ℝ 3 u₀ := hu.of_le (by norm_num)
  have hΔt' : Δt ≠ 0 := ne_of_gt hΔt
  have hΔx' : Δx ≠ 0 := ne_of_gt hΔx
  have hM₃0 : 0 ≤ M₃ := (abs_nonneg _).trans (hM₃ 0)
  have hM₄0 : 0 ≤ M₄ := (abs_nonneg _).trans (hM₄ 0)
  have hE : |u₀ (ξ - a * Δt) - u₀ ξ + a * Δt * deriv u₀ ξ
      - (a * Δt) ^ 2 / 2 * iteratedDeriv 2 u₀ ξ| ≤ M₃ * |a * Δt| ^ 3 / 6 := by
    have h := abs_taylor_two hu3 hM₃ ξ (-(a * Δt))
    rw [show ξ + -(a * Δt) = ξ - a * Δt from by ring,
      show u₀ (ξ - a * Δt) - u₀ ξ - -(a * Δt) * deriv u₀ ξ
          - (-(a * Δt)) ^ 2 / 2 * iteratedDeriv 2 u₀ ξ
        = u₀ (ξ - a * Δt) - u₀ ξ + a * Δt * deriv u₀ ξ
          - (a * Δt) ^ 2 / 2 * iteratedDeriv 2 u₀ ξ from by ring, abs_neg] at h
    exact h
  have hFp : |u₀ (ξ + Δx) - u₀ ξ - Δx * deriv u₀ ξ - Δx ^ 2 / 2 * iteratedDeriv 2 u₀ ξ
      - Δx ^ 3 / 6 * iteratedDeriv 3 u₀ ξ| ≤ M₄ * Δx ^ 4 / 24 := abs_taylor_three hu hM₄ ξ Δx
  have hFm : |u₀ (ξ - Δx) - u₀ ξ + Δx * deriv u₀ ξ - Δx ^ 2 / 2 * iteratedDeriv 2 u₀ ξ
      + Δx ^ 3 / 6 * iteratedDeriv 3 u₀ ξ| ≤ M₄ * Δx ^ 4 / 24 := by
    have h := abs_taylor_three hu hM₄ ξ (-Δx)
    rw [show ξ + -Δx = ξ - Δx from by ring,
      show u₀ (ξ - Δx) - u₀ ξ - -Δx * deriv u₀ ξ - (-Δx) ^ 2 / 2 * iteratedDeriv 2 u₀ ξ
          - (-Δx) ^ 3 / 6 * iteratedDeriv 3 u₀ ξ
        = u₀ (ξ - Δx) - u₀ ξ + Δx * deriv u₀ ξ - Δx ^ 2 / 2 * iteratedDeriv 2 u₀ ξ
          + Δx ^ 3 / 6 * iteratedDeriv 3 u₀ ξ from by ring,
      show (-Δx) ^ 4 = Δx ^ 4 from by ring] at h
    exact h
  have hd3 : |iteratedDeriv 3 u₀ ξ| ≤ M₃ := hM₃ ξ
  have hid : truncationError (laxWendroff a (Δt / Δx)) a Δt Δx u₀ ξ * Δt
      = (u₀ (ξ - a * Δt) - u₀ ξ + a * Δt * deriv u₀ ξ
          - (a * Δt) ^ 2 / 2 * iteratedDeriv 2 u₀ ξ)
        + Δt / Δx * a * Δx ^ 3 / 6 * iteratedDeriv 3 u₀ ξ
        + Δt / Δx * a / 2
          * ((u₀ (ξ + Δx) - u₀ ξ - Δx * deriv u₀ ξ - Δx ^ 2 / 2 * iteratedDeriv 2 u₀ ξ
              - Δx ^ 3 / 6 * iteratedDeriv 3 u₀ ξ)
            - (u₀ (ξ - Δx) - u₀ ξ + Δx * deriv u₀ ξ - Δx ^ 2 / 2 * iteratedDeriv 2 u₀ ξ
              + Δx ^ 3 / 6 * iteratedDeriv 3 u₀ ξ))
        - (Δt / Δx) ^ 2 * a ^ 2 / 2
          * ((u₀ (ξ + Δx) - u₀ ξ - Δx * deriv u₀ ξ - Δx ^ 2 / 2 * iteratedDeriv 2 u₀ ξ
              - Δx ^ 3 / 6 * iteratedDeriv 3 u₀ ξ)
            + (u₀ (ξ - Δx) - u₀ ξ + Δx * deriv u₀ ξ - Δx ^ 2 / 2 * iteratedDeriv 2 u₀ ξ
              + Δx ^ 3 / 6 * iteratedDeriv 3 u₀ ξ)) := by
    rw [laxWendroff, truncationError_threePoint]
    field_simp
    ring
  have habs1 : |Δt / Δx * a * Δx ^ 3 / 6| = Δt / Δx * |a| * Δx ^ 3 / 6 := by
    rw [abs_div, abs_mul, abs_mul, abs_div, abs_of_pos hΔt, abs_of_pos hΔx,
      abs_of_pos (by positivity : (0 : ℝ) < Δx ^ 3), abs_of_pos (by norm_num : (0 : ℝ) < 6)]
  have habs2 : |Δt / Δx * a / 2| = Δt / Δx * |a| / 2 := by
    rw [abs_div, abs_mul, abs_div, abs_of_pos hΔt, abs_of_pos hΔx]; norm_num
  have habs3 : |(Δt / Δx) ^ 2 * a ^ 2 / 2| = (Δt / Δx) ^ 2 * a ^ 2 / 2 :=
    abs_of_nonneg (by positivity)
  have hstep : |truncationError (laxWendroff a (Δt / Δx)) a Δt Δx u₀ ξ| * Δt
      ≤ M₃ * |a * Δt| ^ 3 / 6 + Δt / Δx * |a| * Δx ^ 3 / 6 * M₃
        + Δt / Δx * |a| / 2 * (M₄ * Δx ^ 4 / 24 + M₄ * Δx ^ 4 / 24)
        + (Δt / Δx) ^ 2 * a ^ 2 / 2 * (M₄ * Δx ^ 4 / 24 + M₄ * Δx ^ 4 / 24) := by
    calc |truncationError (laxWendroff a (Δt / Δx)) a Δt Δx u₀ ξ| * Δt
        = |truncationError (laxWendroff a (Δt / Δx)) a Δt Δx u₀ ξ * Δt| := by
          rw [abs_mul, abs_of_pos hΔt]
      _ ≤ _ := by
          rw [hid]
          refine (abs_sub_le' _ _).trans (add_le_add ((abs_add_le _ _).trans
            (add_le_add ((abs_add_le _ _).trans (add_le_add hE ?_)) ?_)) ?_)
          · rw [abs_mul, habs1]
            gcongr
          · rw [abs_mul, habs2]
            gcongr
            exact (abs_sub_le' _ _).trans (by gcongr)
          · rw [abs_mul, habs3]
            gcongr
            exact (abs_add_le _ _).trans (by gcongr)
  have hrw : M₃ * |a * Δt| ^ 3 / 6 + Δt / Δx * |a| * Δx ^ 3 / 6 * M₃
        + Δt / Δx * |a| / 2 * (M₄ * Δx ^ 4 / 24 + M₄ * Δx ^ 4 / 24)
        + (Δt / Δx) ^ 2 * a ^ 2 / 2 * (M₄ * Δx ^ 4 / 24 + M₄ * Δx ^ 4 / 24)
      = (|a| ^ 3 / 6 * M₃ * Δt ^ 2 + |a| / 6 * M₃ * Δx ^ 2 + |a| / 24 * M₄ * Δx ^ 3
          + a ^ 2 / 24 * M₄ * (Δt * Δx ^ 2)) * Δt := by
    rw [abs_mul, abs_of_pos hΔt, mul_pow]
    field_simp
    ring
  have e1 : Δx ^ 3 ≤ Δx ^ 2 := by nlinarith
  have e2 : Δt * Δx ^ 2 ≤ Δx ^ 2 := by nlinarith
  have g1 : |a| / 24 * M₄ * Δx ^ 3 ≤ |a| / 24 * M₄ * Δx ^ 2 :=
    mul_le_mul_of_nonneg_left e1 (mul_nonneg (by positivity) hM₄0)
  have g2 : a ^ 2 / 24 * M₄ * (Δt * Δx ^ 2) ≤ a ^ 2 / 24 * M₄ * Δx ^ 2 :=
    mul_le_mul_of_nonneg_left e2 (mul_nonneg (by positivity) hM₄0)
  refine le_of_mul_le_mul_right ?_ hΔt
  refine (hstep.trans (le_of_eq hrw)).trans (mul_le_mul_of_nonneg_right ?_ hΔt.le)
  nlinarith [g1, g2]

end Truncation

/-! ### The CFL condition -/

/-- **The Courant–Friedrichs–Lewy condition** ([quarteroni2000numerical] (13.48)): `|a λ| ≤ 1`
with `λ = Δt/Δx`. -/
def CFL (a lam : ℝ) : Prop := |a * lam| ≤ 1

/-- **The CFL condition for a variable speed field** ([quarteroni2000numerical] §13.8.3):
`Δt ≤ Δx / sup |a|`. -/
def CFLVariable (a : ℝ → ℝ → ℝ) (Δt Δx : ℝ) : Prop :=
  Δt * (⨆ q : ℝ × ℝ, |a q.1 q.2|) ≤ Δx

/-- **The CFL condition for a hyperbolic system** ([quarteroni2000numerical] §13.8.3):
`|λ_k Δt/Δx| ≤ 1` for every eigenvalue. -/
def CFLSystem {p : ℕ} (lam : Fin p → ℝ) (Δt Δx : ℝ) : Prop := ∀ k, |lam k * Δt / Δx| ≤ 1

/-! ### The CFL condition is necessary -/

/-- Iterating a stencil on the zero grid function gives zero. -/
private theorem iterate_apply_zero (c : Stencil) (n : ℕ) :
    (Stencil.apply c)^[n] (0 : ℤ → ℝ) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    exact map_zero (Stencil.applyₗ c)

/-- **The CFL condition is necessary for convergence** ([quarteroni2000numerical] §13.8.3): if
`|a| λ > 1`, then no three-point explicit scheme family converges for every datum. The numerical
domain of dependence at `(0, 1)` is contained in `|x| ≤ 1/λ`
(`FiniteDifference.Stencil.iterate_apply_congr_of_eqOn`), while the exact solution there reads the
datum at `-a`, which lies outside; a smooth bump concentrated at `-a` therefore defeats the
scheme. Since the book's §13.8.3 asserts the CFL condition to be *sufficient* as well, and the
forward Euler/centred scheme (`Hyperbolic.one_lt_norm_amplificationFactor_forwardEulerCentred`)
contradicts that, only this half is true. -/
theorem not_isConvergent_of_one_lt_abs_mul {a lam : ℝ} (hlam : 0 < lam) (hcfl : 1 < |a| * lam)
    (c : ℝ → ℝ → Stencil) (hc : ∀ Δt Δx : ℝ, ∀ s ∈ (c Δt Δx).support, |s| ≤ 1) :
    ∃ u₀ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u₀ ∧ ¬ IsConvergent a u₀ c 1 := by
  have hinv : 1 / lam < |a| := by rw [div_lt_iff₀ hlam]; linarith
  set r : ℝ := (|a| - 1 / lam) / 2 with hr
  have hrpos : 0 < r := by rw [hr]; linarith
  set f : ContDiffBump (-a) := ⟨r / 2, r, by positivity, by linarith⟩ with hf
  refine ⟨f, f.contDiff, ?_⟩
  intro hconv
  obtain ⟨δ₀, hδ₀, hbound⟩ := hconv (1 / 2) (by norm_num)
  obtain ⟨m, hm⟩ := exists_nat_gt (max (1 / δ₀) (1 / (lam * δ₀)))
  set n : ℕ := m + 1 with hn
  have hmax : 0 < max (1 / δ₀) (1 / (lam * δ₀)) := lt_max_of_lt_left (by positivity)
  have hnR : max (1 / δ₀) (1 / (lam * δ₀)) < (n : ℝ) := by
    rw [hn]
    push_cast
    linarith
  have hnpos : (0 : ℝ) < n := lt_trans hmax hnR
  set Δt : ℝ := 1 / n with hΔt
  set Δx : ℝ := 1 / (n * lam) with hΔx
  have hΔtpos : 0 < Δt := by rw [hΔt]; positivity
  have hΔxpos : 0 < Δx := by rw [hΔx]; positivity
  have hΔtle : Δt ≤ δ₀ := by
    rw [hΔt, div_le_iff₀ hnpos]
    have h1 : 1 / δ₀ < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hnR
    rw [div_lt_iff₀ hδ₀] at h1
    linarith
  have hΔxle : Δx ≤ δ₀ := by
    rw [hΔx, div_le_iff₀ (by positivity)]
    have h1 : 1 / (lam * δ₀) < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hnR
    rw [div_lt_iff₀ (by positivity)] at h1
    nlinarith
  have hnΔt : (n : ℝ) * Δt = 1 := by rw [hΔt]; field_simp
  have hnΔx : (n : ℝ) * Δx = 1 / lam := by rw [hΔx]; field_simp
  have hzero : ∀ i : ℤ, |i - 0| ≤ (n : ℤ) * 1 → f ((i : ℝ) * Δx) = 0 := by
    intro i hi
    have hiabs : |(i : ℝ)| ≤ (n : ℝ) := by
      rw [sub_zero, mul_one] at hi
      exact_mod_cast hi
    have hbd : |(i : ℝ) * Δx| ≤ 1 / lam := by
      rw [abs_mul, abs_of_pos hΔxpos, ← hnΔx]
      exact mul_le_mul_of_nonneg_right hiabs hΔxpos.le
    have hdist : r ≤ |(i : ℝ) * Δx - -a| := by
      have h1 : |a| - |(i : ℝ) * Δx| ≤ |(i : ℝ) * Δx + a| := by
        have h4 := abs_sub_le' ((i : ℝ) * Δx + a) ((i : ℝ) * Δx)
        rw [show (i : ℝ) * Δx + a - (i : ℝ) * Δx = a from by ring] at h4
        linarith
      have h3 : (i : ℝ) * Δx - -a = (i : ℝ) * Δx + a := by ring
      rw [h3]
      rw [hr]
      linarith
    refine f.zero_of_le_dist ?_
    rw [Real.dist_eq]
    exact hdist
  have hnum : (Stencil.apply (c Δt Δx))^[n] (fun i : ℤ => f ((i : ℝ) * Δx)) 0 = 0 := by
    rw [Stencil.iterate_apply_congr_of_eqOn (hc Δt Δx) n (v := (0 : ℤ → ℝ)) hzero,
      iterate_apply_zero]
    rfl
  have hexact : f ((0 : ℤ) * Δx - a * ((n : ℝ) * Δt)) = 1 := by
    rw [hnΔt]
    have h0 : ((0 : ℤ) : ℝ) * Δx - a * 1 = -a := by push_cast; ring
    rw [h0]
    exact f.one_of_mem_closedBall (Metric.mem_closedBall_self f.rIn_pos.le)
  have := hbound Δt Δx hΔtpos hΔtle hΔxpos hΔxle n 0 (by rw [hnΔt])
  rw [hnum, hexact] at this
  norm_num at this

/-! ### Multi-level schemes for the wave equation -/

/-- **The leap-frog scheme** for `u_tt = γ² u_xx` ([quarteroni2000numerical] (13.44)). -/
def IsLeapFrog (γ lam : ℝ) (u : ℕ → ℤ → ℝ) : Prop :=
  ∀ n j, u (n + 2) j - 2 * u (n + 1) j + u n j
    = (γ * lam) ^ 2 * (u (n + 1) (j + 1) - 2 * u (n + 1) j + u (n + 1) (j - 1))

/-- **The Newmark scheme** for `u_tt = γ² u_xx` ([quarteroni2000numerical] (13.45)), with the
parameters `β ∈ [0, ½]` and `θ ∈ [0, 1]` and the auxiliary velocity `v`. -/
def IsNewmark (γ lam Δt β θ : ℝ) (u v : ℕ → ℤ → ℝ) : Prop :=
  ∀ n j,
    u (n + 1) j - u n j = Δt * v n j
        + (γ * lam) ^ 2 * (β * (u (n + 1) (j + 1) - 2 * u (n + 1) j + u (n + 1) (j - 1))
          + (1 / 2 - β) * (u n (j + 1) - 2 * u n j + u n (j - 1))) ∧
      v (n + 1) j - v n j = (γ * lam) ^ 2 / Δt
        * (θ * (u (n + 1) (j + 1) - 2 * u (n + 1) j + u (n + 1) (j - 1))
          + (1 - θ) * (u n (j + 1) - 2 * u n j + u n (j - 1)))

/-! ### Amplification factors -/

section Amplification

variable {N : ℕ}

/-- **The phase angle of the `k`-th mode on the periodic grid** of `N` points, `φ_k = 2πk/N`
([quarteroni2000numerical] §13.9). -/
noncomputable def gridPhase (N : ℕ) (k : Fin N) : ℝ := 2 * π * k / N

/-- The grid phase, as a complex number. -/
private theorem ofReal_gridPhase (N : ℕ) (k : Fin N) :
    ((gridPhase N k : ℝ) : ℂ) = 2 * (Real.pi : ℂ) * ((k : ℕ) : ℂ) / (N : ℂ) := by
  rw [gridPhase]
  push_cast
  ring

/-- The complex exponential of a real phase. -/
private theorem exp_mul_I' (x : ℝ) :
    Complex.exp (I * x) = (Real.cos x : ℂ) + (Real.sin x : ℂ) * I := by
  rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- The complex exponential of a negated real phase. -/
private theorem exp_neg_mul_I' (x : ℝ) :
    Complex.exp (-(I * x)) = (Real.cos x : ℂ) - (Real.sin x : ℂ) * I := by
  rw [show -(I * (x : ℂ)) = I * ((-x : ℝ) : ℂ) by push_cast; ring, exp_mul_I', Real.cos_neg,
    Real.sin_neg]
  push_cast
  ring

/-- The squared modulus of `x + y i` for real `x`, `y`. -/
private theorem normSq_add_mul_I' (x y : ℝ) : ‖(x : ℂ) + (y : ℂ) * I‖ ^ 2 = x ^ 2 + y ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]

/-- A nonnegative real with square at most one is at most one. -/
private theorem le_one_of_sq_le_one {x : ℝ} (hx : 0 ≤ x) (h : x ^ 2 ≤ 1) : x ≤ 1 := by nlinarith

/-- A nonnegative real at most one has square at most one. -/
private theorem sq_le_one_of_le_one {x : ℝ} (hx : 0 ≤ x) (h : x ≤ 1) : x ^ 2 ≤ 1 := by nlinarith

/-- A nonnegative real with square at least one is at least one. -/
private theorem one_le_of_one_le_sq {x : ℝ} (hx : 0 ≤ x) (h : 1 ≤ x ^ 2) : 1 ≤ x := by nlinarith

variable [NeZero N]

/-- **The amplification factor of the forward Euler/centred scheme**
([quarteroni2000numerical] §13.8.4): `γ_k = 1 - i λ a sin φ_k`. -/
theorem amplificationFactor_forwardEulerCentred (a lam : ℝ) (k : Fin N) :
    amplificationFactor (Stencil.toPeriodic N (forwardEulerCentred a lam)) k
      = 1 - I * (lam * a) * (Real.sin (gridPhase N k) : ℂ) := by
  rw [forwardEulerCentred, Stencil.amplificationFactor_toPeriodic_threePoint,
    ← ofReal_gridPhase N k, exp_mul_I', exp_neg_mul_I']
  push_cast
  ring

/-- The squared modulus of the forward Euler/centred amplification factor:
`|γ_k|² = 1 + (λ a sin φ_k)²`, which exceeds `1` for every mesh
([quarteroni2000numerical] §13.8.4). -/
theorem norm_amplificationFactor_forwardEulerCentred_sq (a lam : ℝ) (k : Fin N) :
    ‖amplificationFactor (Stencil.toPeriodic N (forwardEulerCentred a lam)) k‖ ^ 2
      = 1 + (lam * a) ^ 2 * Real.sin (gridPhase N k) ^ 2 := by
  rw [amplificationFactor_forwardEulerCentred,
    show (1 : ℂ) - I * (lam * a) * (Real.sin (gridPhase N k) : ℂ)
      = ((1 : ℝ) : ℂ) + ((-(lam * a * Real.sin (gridPhase N k)) : ℝ) : ℂ) * I by push_cast; ring,
    normSq_add_mul_I']
  ring

/-- **The forward Euler/centred scheme amplifies every nonconstant mode**
([quarteroni2000numerical] §13.8.4): `1 < |γ_k|` whenever `λ a sin φ_k ≠ 0`. -/
theorem one_lt_norm_amplificationFactor_forwardEulerCentred {a lam : ℝ} {k : Fin N}
    (h : lam * a * Real.sin (gridPhase N k) ≠ 0) :
    1 < ‖amplificationFactor (Stencil.toPeriodic N (forwardEulerCentred a lam)) k‖ := by
  have hsq := norm_amplificationFactor_forwardEulerCentred_sq a lam k
  have hpos : 0 < (lam * a * Real.sin (gridPhase N k)) ^ 2 := by positivity
  nlinarith [norm_nonneg (amplificationFactor (Stencil.toPeriodic N (forwardEulerCentred a lam)) k)]

/-- **The amplification factor of the upwind scheme** ([quarteroni2000numerical] Exercise 13.6):
`γ_k = 1 - λ|a|(1 - cos φ_k) - i λ a sin φ_k`, a single formula covering both signs of `a`. -/
theorem amplificationFactor_upwind (a lam : ℝ) (k : Fin N) :
    amplificationFactor (Stencil.toPeriodic N (upwind a lam)) k
      = ((1 - lam * |a| * (1 - Real.cos (gridPhase N k)) : ℝ) : ℂ)
        - I * (lam * a) * (Real.sin (gridPhase N k) : ℂ) := by
  rw [upwind, Stencil.amplificationFactor_toPeriodic_threePoint,
    ← ofReal_gridPhase N k, exp_mul_I', exp_neg_mul_I',
    max_zero_eq, max_neg_zero_eq]
  push_cast
  ring

/-- The squared modulus of the upwind amplification factor:
`|γ_k|² = 1 - 2 λ|a| (1 - λ|a|)(1 - cos φ_k)` ([quarteroni2000numerical] Exercise 13.6). -/
theorem norm_amplificationFactor_upwind_sq (a lam : ℝ) (k : Fin N) :
    ‖amplificationFactor (Stencil.toPeriodic N (upwind a lam)) k‖ ^ 2
      = 1 - 2 * (lam * |a|) * (1 - lam * |a|) * (1 - Real.cos (gridPhase N k)) := by
  have hpy := Real.sin_sq_add_cos_sq (gridPhase N k)
  have habs : |a| ^ 2 = a ^ 2 := sq_abs a
  rw [amplificationFactor_upwind,
    show ((1 - lam * |a| * (1 - Real.cos (gridPhase N k)) : ℝ) : ℂ)
        - I * (lam * a) * (Real.sin (gridPhase N k) : ℂ)
      = ((1 - lam * |a| * (1 - Real.cos (gridPhase N k)) : ℝ) : ℂ)
        + ((-(lam * a * Real.sin (gridPhase N k)) : ℝ) : ℂ) * I by push_cast; ring,
    normSq_add_mul_I']
  linear_combination (lam ^ 2 * a ^ 2) * hpy
    + (lam ^ 2 * ((1 - Real.cos (gridPhase N k)) ^ 2 - 2 * (1 - Real.cos (gridPhase N k)))) * habs

/-- **The amplification factor of the Lax–Friedrichs scheme**: `γ_k = cos φ_k - i λ a sin φ_k`. -/
theorem amplificationFactor_laxFriedrichs (a lam : ℝ) (k : Fin N) :
    amplificationFactor (Stencil.toPeriodic N (laxFriedrichs a lam)) k
      = (Real.cos (gridPhase N k) : ℂ) - I * (lam * a) * (Real.sin (gridPhase N k) : ℂ) := by
  rw [laxFriedrichs, Stencil.amplificationFactor_toPeriodic_threePoint,
    ← ofReal_gridPhase N k, exp_mul_I', exp_neg_mul_I']
  push_cast
  ring

/-- The squared modulus of the Lax–Friedrichs amplification factor:
`|γ_k|² = cos² φ_k + (λ a)² sin² φ_k`. -/
theorem norm_amplificationFactor_laxFriedrichs_sq (a lam : ℝ) (k : Fin N) :
    ‖amplificationFactor (Stencil.toPeriodic N (laxFriedrichs a lam)) k‖ ^ 2
      = Real.cos (gridPhase N k) ^ 2 + (lam * a) ^ 2 * Real.sin (gridPhase N k) ^ 2 := by
  rw [amplificationFactor_laxFriedrichs,
    show (Real.cos (gridPhase N k) : ℂ) - I * (lam * a) * (Real.sin (gridPhase N k) : ℂ)
      = ((Real.cos (gridPhase N k) : ℝ) : ℂ)
        + ((-(lam * a * Real.sin (gridPhase N k)) : ℝ) : ℂ) * I by push_cast; ring,
    normSq_add_mul_I']
  ring

/-- **The amplification factor of the Lax–Wendroff scheme**:
`γ_k = 1 - (λ a)²(1 - cos φ_k) - i λ a sin φ_k`. -/
theorem amplificationFactor_laxWendroff (a lam : ℝ) (k : Fin N) :
    amplificationFactor (Stencil.toPeriodic N (laxWendroff a lam)) k
      = ((1 - (lam * a) ^ 2 * (1 - Real.cos (gridPhase N k)) : ℝ) : ℂ)
        - I * (lam * a) * (Real.sin (gridPhase N k) : ℂ) := by
  rw [laxWendroff, Stencil.amplificationFactor_toPeriodic_threePoint,
    ← ofReal_gridPhase N k, exp_mul_I', exp_neg_mul_I']
  push_cast
  ring

/-- The squared modulus of the Lax–Wendroff amplification factor:
`|γ_k|² = 1 - (λ a)²(1 - (λ a)²)(1 - cos φ_k)²`, which is
`1 - 4 (λ a)² (1 - (λ a)²) sin⁴(φ_k/2)`. -/
theorem norm_amplificationFactor_laxWendroff_sq (a lam : ℝ) (k : Fin N) :
    ‖amplificationFactor (Stencil.toPeriodic N (laxWendroff a lam)) k‖ ^ 2
      = 1 - (lam * a) ^ 2 * (1 - (lam * a) ^ 2) * (1 - Real.cos (gridPhase N k)) ^ 2 := by
  have hpy := Real.sin_sq_add_cos_sq (gridPhase N k)
  rw [amplificationFactor_laxWendroff,
    show ((1 - (lam * a) ^ 2 * (1 - Real.cos (gridPhase N k)) : ℝ) : ℂ)
        - I * (lam * a) * (Real.sin (gridPhase N k) : ℂ)
      = ((1 - (lam * a) ^ 2 * (1 - Real.cos (gridPhase N k)) : ℝ) : ℂ)
        + ((-(lam * a * Real.sin (gridPhase N k)) : ℝ) : ℂ) * I by push_cast; ring,
    normSq_add_mul_I']
  linear_combination ((lam * a) ^ 2) * hpy

/-! ### The stability conditions of Table 13.1 -/

omit [NeZero N] in
/-- The first mode of a grid of at least two points has `cos φ < 1`. -/
private theorem cos_gridPhase_lt_one (hN : 2 ≤ N) {k : Fin N} (hk : (k : ℕ) = 1) :
    Real.cos (gridPhase N k) < 1 := by
  have hN0 : (0 : ℝ) < N := by positivity
  have hval : gridPhase N k = 2 * π / N := by rw [gridPhase, hk]; push_cast; ring
  have hpos : 0 < gridPhase N k := by rw [hval]; positivity
  have hle : gridPhase N k ≤ π := by
    rw [hval, div_le_iff₀ hN0]
    have h2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith [Real.pi_pos]
  simpa using Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hle hpos

omit [NeZero N] in
/-- The first mode of a grid of at least three points has `sin φ > 0`. -/
private theorem sin_gridPhase_pos (hN : 3 ≤ N) {k : Fin N} (hk : (k : ℕ) = 1) :
    0 < Real.sin (gridPhase N k) := by
  have hN0 : (0 : ℝ) < N := by positivity
  have hval : gridPhase N k = 2 * π / N := by rw [gridPhase, hk]; push_cast; ring
  have hpos : 0 < gridPhase N k := by rw [hval]; positivity
  have hlt : gridPhase N k < π := by
    rw [hval, div_lt_iff₀ hN0]
    have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith [Real.pi_pos]
  exact Real.sin_pos_of_pos_of_lt_pi hpos hlt

/-- **The stability condition of the upwind scheme is the CFL condition**
([quarteroni2000numerical] Exercise 13.6): for `N ≥ 2` and `λ ≥ 0`, all the amplification factors
have modulus at most `1` exactly when `λ |a| ≤ 1`. -/
theorem norm_amplificationFactor_upwind_le_one_iff (hN : 2 ≤ N) {a lam : ℝ} (hlam : 0 ≤ lam) :
    (∀ k : Fin N, ‖amplificationFactor (Stencil.toPeriodic N (upwind a lam)) k‖ ≤ 1)
      ↔ lam * |a| ≤ 1 := by
  have hmul : 0 ≤ lam * |a| := mul_nonneg hlam (abs_nonneg a)
  constructor
  · intro h
    by_contra hcon
    rw [not_le] at hcon
    set k₁ : Fin N := ⟨1, by omega⟩ with hk₁def
    have hk₁ : (k₁ : ℕ) = 1 := rfl
    have hk := h k₁
    have hsq := norm_amplificationFactor_upwind_sq a lam k₁
    have hcos := cos_gridPhase_lt_one hN hk₁
    have hnn := norm_nonneg (amplificationFactor (Stencil.toPeriodic N (upwind a lam)) k₁)
    have hsq1 := sq_le_one_of_le_one hnn hk
    have h3 : 2 * (lam * |a|) * (1 - lam * |a|) * (1 - Real.cos (gridPhase N k₁)) < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by linarith) (by linarith)) (by linarith)
    linarith
  · intro h k
    have hsq := norm_amplificationFactor_upwind_sq a lam k
    have hcos : Real.cos (gridPhase N k) ≤ 1 := Real.cos_le_one _
    have hnn := norm_nonneg (amplificationFactor (Stencil.toPeriodic N (upwind a lam)) k)
    have h3 : 0 ≤ 2 * (lam * |a|) * (1 - lam * |a|) * (1 - Real.cos (gridPhase N k)) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    exact le_one_of_sq_le_one hnn (by linarith)

/-- **The stability condition of the Lax–Friedrichs scheme is the CFL condition**
([quarteroni2000numerical] §13.8.3): for `N ≥ 3`, all the amplification factors have modulus at
most `1` exactly when `|λ a| ≤ 1`. -/
theorem norm_amplificationFactor_laxFriedrichs_le_one_iff (hN : 3 ≤ N) (a lam : ℝ) :
    (∀ k : Fin N, ‖amplificationFactor (Stencil.toPeriodic N (laxFriedrichs a lam)) k‖ ≤ 1)
      ↔ |lam * a| ≤ 1 := by
  constructor
  · intro h
    by_contra hcon
    rw [not_le] at hcon
    set k₁ : Fin N := ⟨1, by omega⟩ with hk₁def
    have hk₁ : (k₁ : ℕ) = 1 := rfl
    have hk := h k₁
    have hsq := norm_amplificationFactor_laxFriedrichs_sq a lam k₁
    have hsin := sin_gridPhase_pos hN hk₁
    have hpy := Real.sin_sq_add_cos_sq (gridPhase N k₁)
    have habs : 1 < (lam * a) ^ 2 := by nlinarith [abs_nonneg (lam * a), sq_abs (lam * a)]
    have hnn := norm_nonneg (amplificationFactor (Stencil.toPeriodic N (laxFriedrichs a lam)) k₁)
    have hsq1 := sq_le_one_of_le_one hnn hk
    have hs2 : 0 < Real.sin (gridPhase N k₁) ^ 2 := by positivity
    have h3 : 0 < ((lam * a) ^ 2 - 1) * Real.sin (gridPhase N k₁) ^ 2 :=
      mul_pos (by linarith) hs2
    nlinarith
  · intro h k
    have hsq := norm_amplificationFactor_laxFriedrichs_sq a lam k
    have hpy := Real.sin_sq_add_cos_sq (gridPhase N k)
    have habs : (lam * a) ^ 2 ≤ 1 := by nlinarith [abs_nonneg (lam * a), sq_abs (lam * a)]
    have hnn := norm_nonneg (amplificationFactor (Stencil.toPeriodic N (laxFriedrichs a lam)) k)
    have h3 : 0 ≤ (1 - (lam * a) ^ 2) * Real.sin (gridPhase N k) ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    exact le_one_of_sq_le_one hnn (by nlinarith)

/-- **The stability condition of the Lax–Wendroff scheme is the CFL condition**
([quarteroni2000numerical] §13.8.3): for `N ≥ 2`, all the amplification factors have modulus at
most `1` exactly when `|λ a| ≤ 1`. -/
theorem norm_amplificationFactor_laxWendroff_le_one_iff (hN : 2 ≤ N) (a lam : ℝ) :
    (∀ k : Fin N, ‖amplificationFactor (Stencil.toPeriodic N (laxWendroff a lam)) k‖ ≤ 1)
      ↔ |lam * a| ≤ 1 := by
  constructor
  · intro h
    by_contra hcon
    rw [not_le] at hcon
    set k₁ : Fin N := ⟨1, by omega⟩ with hk₁def
    have hk₁ : (k₁ : ℕ) = 1 := rfl
    have hk := h k₁
    have hsq := norm_amplificationFactor_laxWendroff_sq a lam k₁
    have hcos := cos_gridPhase_lt_one hN hk₁
    have habs : 1 < (lam * a) ^ 2 := by nlinarith [abs_nonneg (lam * a), sq_abs (lam * a)]
    have hnn := norm_nonneg (amplificationFactor (Stencil.toPeriodic N (laxWendroff a lam)) k₁)
    have hsq1 := sq_le_one_of_le_one hnn hk
    have hc2 : 0 < (1 - Real.cos (gridPhase N k₁)) ^ 2 := by positivity
    have h3 : (lam * a) ^ 2 * (1 - (lam * a) ^ 2) * (1 - Real.cos (gridPhase N k₁)) ^ 2 < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by linarith) (by linarith)) hc2
    linarith
  · intro h k
    have hsq := norm_amplificationFactor_laxWendroff_sq a lam k
    have hcos : Real.cos (gridPhase N k) ≤ 1 := Real.cos_le_one _
    have habs : (lam * a) ^ 2 ≤ 1 := by nlinarith [abs_nonneg (lam * a), sq_abs (lam * a)]
    have hnn := norm_nonneg (amplificationFactor (Stencil.toPeriodic N (laxWendroff a lam)) k)
    have h3 : 0 ≤ (lam * a) ^ 2 * (1 - (lam * a) ^ 2) * (1 - Real.cos (gridPhase N k)) ^ 2 :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (sq_nonneg _)
    exact le_one_of_sq_le_one hnn (by linarith)

/-- **The amplification factor of the implicit backward Euler/centred scheme**
([quarteroni2000numerical] (13.43)): `γ_k = 1 / (1 + i λ a sin φ_k)`. -/
theorem amplificationFactor₂_backwardEulerCentred (a lam : ℝ) (k : Fin N) :
    amplificationFactor₂ (Stencil.toPeriodic N (Stencil.threePoint (-(lam * a / 2)) 1
        (lam * a / 2))) (Stencil.toPeriodic N (Stencil.threePoint 0 1 0)) k
      = 1 / (1 + I * (lam * a) * (Real.sin (gridPhase N k) : ℂ)) := by
  rw [amplificationFactor₂, Stencil.amplificationFactor_toPeriodic_threePoint,
    Stencil.amplificationFactor_toPeriodic_threePoint,
    ← ofReal_gridPhase N k, exp_mul_I', exp_neg_mul_I']
  push_cast
  ring_nf

/-- **The backward Euler/centred scheme is unconditionally `ℓ²`-stable**
([quarteroni2000numerical] §13.8.2): its amplification factors never exceed `1` in modulus. -/
theorem norm_amplificationFactor₂_backwardEulerCentred_le_one (a lam : ℝ) (k : Fin N) :
    ‖amplificationFactor₂ (Stencil.toPeriodic N (Stencil.threePoint (-(lam * a / 2)) 1
        (lam * a / 2))) (Stencil.toPeriodic N (Stencil.threePoint 0 1 0)) k‖ ≤ 1 := by
  rw [amplificationFactor₂_backwardEulerCentred, norm_div, norm_one]
  have hden : ‖(1 : ℂ) + I * (lam * a) * (Real.sin (gridPhase N k) : ℂ)‖ ^ 2
      = 1 + (lam * a) ^ 2 * Real.sin (gridPhase N k) ^ 2 := by
    rw [show (1 : ℂ) + I * (lam * a) * (Real.sin (gridPhase N k) : ℂ)
        = ((1 : ℝ) : ℂ) + ((lam * a * Real.sin (gridPhase N k) : ℝ) : ℂ) * I by push_cast; ring,
      normSq_add_mul_I']
    ring
  have h1 : 1 ≤ ‖(1 : ℂ) + I * (lam * a) * (Real.sin (gridPhase N k) : ℂ)‖ :=
    one_le_of_one_le_sq (norm_nonneg _) (by
      rw [hden]
      nlinarith [sq_nonneg (lam * a), sq_nonneg (Real.sin (gridPhase N k))])
  rw [div_le_one (by linarith)]
  exact h1

end Amplification

/-! ### The implicit backward Euler/centred scheme on `ℓ²(ℤ)` -/

section Implicit

/-- **The centred difference** `D₀ u j = u_{j+1} - u_{j-1}` as a bounded operator on `ℓ²(ℤ)`
([quarteroni2000numerical] (13.43)). -/
noncomputable def centredDiffCLM : lp (fun _ : ℤ => ℝ) 2 →L[ℝ] lp (fun _ : ℤ => ℝ) 2 :=
  Stencil.lpCLM (Stencil.threePoint (-1) 0 1) 2

/-- The centred difference acts by `u ↦ (j ↦ u_{j+1} - u_{j-1})`. -/
theorem centredDiffCLM_apply (u : lp (fun _ : ℤ => ℝ) 2) (j : ℤ) :
    centredDiffCLM u j = u (j + 1) - u (j - 1) := by
  rw [centredDiffCLM, Stencil.lpCLM_apply, Stencil.threePoint_apply]
  simp only [smul_eq_mul, neg_mul, one_mul, zero_mul]
  ring

/-- Composing two shifts adds the offsets. -/
private theorem shift_shift (s t : ℤ) (u : lp (fun _ : ℤ => ℝ) 2) :
    lp.shiftₗᵢ (E := ℝ) (𝕜 := ℝ) 2 s (lp.shiftₗᵢ (E := ℝ) (𝕜 := ℝ) 2 t u)
      = lp.shiftₗᵢ (E := ℝ) (𝕜 := ℝ) 2 (s + t) u := by
  refine lp.ext (funext fun j => ?_)
  simp only [lp.shiftₗᵢ_apply]
  rw [sub_sub]

/-- The zero shift is the identity. -/
private theorem shift_zero (u : lp (fun _ : ℤ => ℝ) 2) :
    lp.shiftₗᵢ (E := ℝ) (𝕜 := ℝ) 2 0 u = u := by
  refine lp.ext (funext fun j => ?_)
  simp

/-- **The shift is unitary**: `⟪S_s u, v⟫ = ⟪u, S_{-s} v⟫` on `ℓ²(ℤ)`. -/
theorem inner_shift_left (s : ℤ) (u v : lp (fun _ : ℤ => ℝ) 2) :
    inner ℝ (lp.shiftₗᵢ (E := ℝ) (𝕜 := ℝ) 2 s u) v
      = inner ℝ u (lp.shiftₗᵢ (E := ℝ) (𝕜 := ℝ) 2 (-s) v) := by
  have hv : lp.shiftₗᵢ (E := ℝ) (𝕜 := ℝ) 2 s (lp.shiftₗᵢ (E := ℝ) (𝕜 := ℝ) 2 (-s) v) = v := by
    rw [shift_shift, add_neg_cancel, shift_zero]
  conv_lhs => rw [← hv]
  exact (lp.shiftₗᵢ (E := ℝ) (𝕜 := ℝ) 2 s).inner_map_map u _

/-- The centred difference is the difference of the two unit shifts. -/
private theorem centredDiffCLM_eq_sub (u : lp (fun _ : ℤ => ℝ) 2) :
    centredDiffCLM u
      = lp.shiftₗᵢ (E := ℝ) (𝕜 := ℝ) 2 (-1) u - lp.shiftₗᵢ (E := ℝ) (𝕜 := ℝ) 2 1 u := by
  refine lp.ext (funext fun j => ?_)
  rw [lp.coeFn_sub]
  simp [centredDiffCLM_apply, sub_neg_eq_add]

/-- **The centred difference is skew-adjoint on `ℓ²(ℤ)`**: `⟪D₀ u, v⟫ = -⟪u, D₀ v⟫`
([quarteroni2000numerical] Exercise 13.7). -/
theorem inner_centredDiffCLM_left (u v : lp (fun _ : ℤ => ℝ) 2) :
    inner ℝ (centredDiffCLM u) v = -inner ℝ u (centredDiffCLM v) := by
  rw [centredDiffCLM_eq_sub u, centredDiffCLM_eq_sub v, inner_sub_left, inner_sub_right,
    inner_shift_left, inner_shift_left]
  norm_num

/-- **The centred difference has vanishing quadratic form**: `⟪D₀ u, u⟫ = 0`, the telescoping sum
of [quarteroni2000numerical] Exercise 13.7. -/
theorem inner_centredDiffCLM_self (u : lp (fun _ : ℤ => ℝ) 2) :
    inner ℝ (centredDiffCLM u) u = 0 := by
  have h := inner_centredDiffCLM_left u u
  have h2 : inner ℝ u (centredDiffCLM u) = inner ℝ (centredDiffCLM u) u := real_inner_comm _ _
  linarith

/-- **The operator of the implicit backward Euler/centred scheme** ([quarteroni2000numerical]
(13.43)): `B = 1 + (λa/2) D₀`, applied to the *new* time level. -/
noncomputable def backwardEulerCentredOp (a lam : ℝ) :
    lp (fun _ : ℤ => ℝ) 2 →L[ℝ] lp (fun _ : ℤ => ℝ) 2 :=
  ContinuousLinearMap.id ℝ _ + (lam * a / 2) • centredDiffCLM

/-- The scheme operator acts by `u_j + (λa/2)(u_{j+1} - u_{j-1})`. -/
theorem backwardEulerCentredOp_apply (a lam : ℝ) (u : lp (fun _ : ℤ => ℝ) 2) (j : ℤ) :
    backwardEulerCentredOp a lam u j = u j + lam * a / 2 * (u (j + 1) - u (j - 1)) := by
  have h : backwardEulerCentredOp a lam u = u + (lam * a / 2) • centredDiffCLM u := rfl
  rw [h, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    centredDiffCLM_apply]

/-- **The scheme operator is coercive with constant `1`**, because the centred difference is
skew-adjoint: `⟪B u, u⟫ = ‖u‖²` ([quarteroni2000numerical] Exercise 13.7). -/
theorem backwardEulerCentredOp_isCoerciveWith (a lam : ℝ) :
    ((backwardEulerCentredOp a lam : lp (fun _ : ℤ => ℝ) 2 →L[ℝ] lp (fun _ : ℤ => ℝ) 2) :
      lp (fun _ : ℤ => ℝ) 2 →ₗ[ℝ] lp (fun _ : ℤ => ℝ) 2).IsCoerciveWith 1 := by
  intro u
  have hB : (backwardEulerCentredOp a lam) u = u + (lam * a / 2) • centredDiffCLM u := rfl
  rw [ContinuousLinearMap.coe_coe, hB, inner_add_left, real_inner_smul_left,
    inner_centredDiffCLM_self]
  simp

/-- **The solution operator of the implicit backward Euler/centred scheme**: the inverse of
`1 + (λa/2) D₀`, which exists and is a contraction because that operator is coercive with constant
`1` ([quarteroni2000numerical] §13.8.2). -/
noncomputable def backwardEulerCentred (a lam : ℝ) :
    lp (fun _ : ℤ => ℝ) 2 →L[ℝ] lp (fun _ : ℤ => ℝ) 2 :=
  ((ContinuousLinearMap.exists_equiv_of_isCoerciveWith one_pos
    (backwardEulerCentredOp_isCoerciveWith a lam)).choose.symm :
      lp (fun _ : ℤ => ℝ) 2 →L[ℝ] lp (fun _ : ℤ => ℝ) 2)

/-- **The implicit scheme is solved by `backwardEulerCentred`**:
`u^{n+1}_j + (λa/2)(u^{n+1}_{j+1} - u^{n+1}_{j-1}) = u^n_j` ([quarteroni2000numerical] (13.43)). -/
theorem backwardEulerCentred_spec (a lam : ℝ) (u : lp (fun _ : ℤ => ℝ) 2) :
    backwardEulerCentredOp a lam (backwardEulerCentred a lam u) = u := by
  have hspec := (ContinuousLinearMap.exists_equiv_of_isCoerciveWith one_pos
    (backwardEulerCentredOp_isCoerciveWith a lam)).choose_spec
  have key : ∀ x, backwardEulerCentredOp a lam x
      = (ContinuousLinearMap.exists_equiv_of_isCoerciveWith one_pos
        (backwardEulerCentredOp_isCoerciveWith a lam)).choose x :=
    fun x => (congrFun (congrArg DFunLike.coe hspec.1) x).symm
  rw [key]
  exact ContinuousLinearEquiv.apply_symm_apply _ u

/-- **The implicit backward Euler/centred scheme is unconditionally stable in `‖·‖_{Δ,2}`**, with
constant `1`: `‖u^{n+1}‖ ≤ ‖u^n‖` for every `a` and every `λ`
([quarteroni2000numerical] §13.8.2 and Exercise 13.7). -/
theorem norm_backwardEulerCentred_apply_le (a lam : ℝ) (u : lp (fun _ : ℤ => ℝ) 2) :
    ‖backwardEulerCentred a lam u‖ ≤ ‖u‖ := by
  have hspec := (ContinuousLinearMap.exists_equiv_of_isCoerciveWith one_pos
    (backwardEulerCentredOp_isCoerciveWith a lam)).choose_spec
  have hn : ‖backwardEulerCentred a lam‖ ≤ 1 := hspec.2.trans (le_of_eq one_div_one)
  have h3 := (backwardEulerCentred a lam).le_of_opNorm_le hn u
  rwa [one_mul] at h3

end Implicit

/-! ### The unconditional instability of the forward Euler/centred scheme -/

section Instability

/-- Every periodic grid of at least eight points is nonempty. -/
instance neZero_add_eight (m : ℕ) : NeZero (m + 8) := ⟨by omega⟩

/-- **The forward Euler/centred family** on the periodic grids of `m + 8` points of `[0, 2π]`,
with `Δx = 2π/(m + 8)` and `Δt = λ Δx`, as real-linear operators on `EuclideanSpace ℂ`. -/
noncomputable def forwardEulerCentredFamily (a lam : ℝ) (m : ℕ) :
    EuclideanSpace ℂ (Fin (m + 8)) →L[ℝ] EuclideanSpace ℂ (Fin (m + 8)) :=
  (toEuclideanCLM (𝕜 := ℂ)
    (periodicScheme (Stencil.toPeriodic (m + 8) (forwardEulerCentred a lam)))).restrictScalars ℝ

/-- Restricting scalars commutes with powers. -/
private theorem restrictScalars_pow {N : ℕ}
    (A : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) (n : ℕ) :
    (A.restrictScalars ℝ) ^ n = (A ^ n).restrictScalars ℝ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, pow_succ, ih]; rfl

/-- On a grid of at least eight points the `⌊N/4⌋`-th phase lies in `(π/4, π/2]`, so its sine
squared exceeds `1/2`. -/
private theorem half_lt_sin_sq_gridPhase (m : ℕ) :
    1 / 2 < Real.sin (gridPhase (m + 8) ⟨(m + 8) / 4, by omega⟩) ^ 2 := by
  set N : ℕ := m + 8 with hN
  set q : ℕ := N / 4 with hq
  have hNpos : (0 : ℝ) < N := by rw [hN]; positivity
  have h4q : 4 * q ≤ N := by omega
  have hq4 : N < 4 * q + 4 := by omega
  have hN8 : 8 ≤ N := by omega
  have h4qR : 4 * (q : ℝ) ≤ (N : ℝ) := by exact_mod_cast h4q
  have hq4R : (N : ℝ) < 4 * (q : ℝ) + 4 := by exact_mod_cast hq4
  have hN8R : (8 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN8
  have hval : gridPhase N ⟨q, by omega⟩ = 2 * π * q / N := rfl
  have hpi := Real.pi_pos
  have hupper : gridPhase N ⟨q, by omega⟩ ≤ π / 2 := by
    rw [hval, div_le_iff₀ hNpos]
    nlinarith
  have hlower : π / 4 < gridPhase N ⟨q, by omega⟩ := by
    rw [hval, lt_div_iff₀ hNpos]
    nlinarith
  have hsin : Real.sin (π / 4) < Real.sin (gridPhase N ⟨q, by omega⟩) :=
    Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) hupper hlower
  rw [Real.sin_pi_div_four] at hsin
  have h2 : (0 : ℝ) < √2 / 2 := by positivity
  have hsq : (√2 / 2) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  nlinarith [hsin, h2, hsq]

/-- **The forward Euler/centred scheme is unconditionally unstable**
([quarteroni2000numerical] §13.8.4): for `a ≠ 0` and any `λ > 0` the family of periodic schemes
with `Δx = 2π/N`, `Δt = λ Δx` is not stable in the sense of (13.46), because the mode nearest to
`φ = π/2` has `|γ_k| ≥ √(1 + (λa)²/2) > 1` on every grid, so `‖Qⁿ‖₂ ≥ ρⁿ` grows past any `C_T` as
the mesh is refined at fixed `λ`. The CFL condition is therefore not sufficient. -/
theorem forwardEulerCentred_not_isStableFamily {a lam : ℝ} (ha : a ≠ 0) (hlam : 0 < lam) :
    ¬FiniteDifference.IsStableFamily (fun m : ℕ => lam * (2 * π / (m + 8)))
      (fun m : ℕ => 2 * π / (m + 8)) (forwardEulerCentredFamily a lam) := by
  intro hstab
  obtain ⟨C, δ₀, hδ₀, hC⟩ := hstab 1 one_pos
  have hpi := Real.pi_pos
  have hla : 0 < (lam * a) ^ 2 := by positivity
  set ρ : ℝ := √(1 + (lam * a) ^ 2 / 2) with hρdef
  have hρ1 : 1 < ρ := by
    rw [hρdef]
    exact (Real.lt_sqrt zero_le_one).2 (by nlinarith)
  have hρ0 : (0 : ℝ) ≤ ρ := by linarith
  obtain ⟨n₀, hn₀⟩ := pow_unbounded_of_one_lt C hρ1
  obtain ⟨m, hm⟩ := exists_nat_gt
    (max (2 * π * lam * (n₀ + 1)) (2 * π / δ₀ * (1 + lam)))
  set N : ℕ := m + 8 with hNdef
  have hNR : max (2 * π * lam * (n₀ + 1)) (2 * π / δ₀ * (1 + lam)) < (N : ℝ) := by
    rw [hNdef]
    push_cast
    linarith
  have h1 : 2 * π * lam * (n₀ + 1) < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hNR
  have h2 : 2 * π / δ₀ * (1 + lam) < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hNR
  have hNpos : (0 : ℝ) < N := by rw [hNdef]; positivity
  -- the two step sizes are below `δ₀`
  have hΔxpos : (0 : ℝ) < 2 * π / N := by positivity
  have hΔtpos : (0 : ℝ) < lam * (2 * π / N) := by positivity
  have hδ : 2 * π * (1 + lam) < δ₀ * N := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hδ₀] at h2
    linarith
  have hΔxle : 2 * π / N ≤ δ₀ := by
    rw [div_le_iff₀ hNpos]
    nlinarith
  have hΔtle : lam * (2 * π / N) ≤ δ₀ := by
    rw [mul_div_assoc', div_le_iff₀ hNpos]
    nlinarith
  -- the number of steps
  set n : ℕ := ⌊1 / (lam * (2 * π / N))⌋₊ with hndef
  have hxpos : (0 : ℝ) < 1 / (lam * (2 * π / N)) := by positivity
  have hnle : (n : ℝ) * (lam * (2 * π / N)) ≤ 1 := by
    have := Nat.floor_le hxpos.le
    rw [← hndef] at this
    calc (n : ℝ) * (lam * (2 * π / N)) ≤ (1 / (lam * (2 * π / N))) * (lam * (2 * π / N)) := by
          exact mul_le_mul_of_nonneg_right this hΔtpos.le
      _ = 1 := by field_simp
  have hnbig : n₀ ≤ n := by
    by_contra hcon
    rw [not_le] at hcon
    have hlt : (n : ℝ) + 1 ≤ n₀ := by exact_mod_cast hcon
    have hfl : 1 / (lam * (2 * π / N)) < (n : ℝ) + 1 := by
      have := Nat.lt_floor_add_one (1 / (lam * (2 * π / N)))
      rw [← hndef] at this
      exact this
    have hinv : (N : ℝ) / (2 * π * lam) = 1 / (lam * (2 * π / N)) := by field_simp
    rw [← hinv] at hfl
    rw [div_lt_iff₀ (by positivity)] at hfl
    nlinarith
  -- the mode nearest to `π/2`
  have hsin := half_lt_sin_sq_gridPhase m
  have hgam : ρ ≤ ‖FiniteDifference.amplificationFactor
      (Stencil.toPeriodic N (forwardEulerCentred a lam)) ⟨N / 4, by omega⟩‖ := by
    have hsq := norm_amplificationFactor_forwardEulerCentred_sq (N := N) a lam ⟨N / 4, by omega⟩
    have hge : ρ ^ 2 ≤ ‖FiniteDifference.amplificationFactor
        (Stencil.toPeriodic N (forwardEulerCentred a lam)) ⟨N / 4, by omega⟩‖ ^ 2 := by
      rw [hsq, hρdef, Real.sq_sqrt (by positivity)]
      nlinarith
    nlinarith [norm_nonneg (FiniteDifference.amplificationFactor
      (Stencil.toPeriodic N (forwardEulerCentred a lam)) (⟨N / 4, by omega⟩ : Fin N))]
  have hlow : ρ ^ n ≤ ‖forwardEulerCentredFamily a lam m ^ n‖ := by
    rw [forwardEulerCentredFamily, restrictScalars_pow, ContinuousLinearMap.norm_restrictScalars,
      ← map_pow]
    exact le_trans (pow_le_pow_left₀ hρ0 hgam n)
      (norm_amplificationFactor_pow_le _ ⟨N / 4, by omega⟩ n)
  have hcast : ((N : ℕ) : ℝ) = (m : ℝ) + 8 := by rw [hNdef]; push_cast; ring
  have hup := hC m (by simpa only [← hcast] using hΔtpos) (by simpa only [← hcast] using hΔtle)
    (by simpa only [← hcast] using hΔxpos) (by simpa only [← hcast] using hΔxle) n
    (by simpa only [← hcast] using hnle)
  have hmono : ρ ^ n₀ ≤ ρ ^ n := pow_le_pow_right₀ hρ1.le hnbig
  linarith

end Instability

/-! ### Dissipation and dispersion (§13.9) -/

/-- **The exact amplification factor** of the `k`-th harmonic
([quarteroni2000numerical] (13.54)): the exact solution of `u_t + a u_x = 0` multiplies `e^{ikx}`
by `g_k = e^{-i a k Δt}` per time step. -/
noncomputable def exactAmplification (a Δt : ℝ) (k : ℤ) : ℂ := Complex.exp (-(I * a * k * Δt))

/-- Iterating the exact amplification: `g_k^n = e^{-i a k (n Δt)}`. -/
theorem exactAmplification_pow (a Δt : ℝ) (k : ℤ) (n : ℕ) :
    exactAmplification a Δt k ^ n = Complex.exp (-(I * a * k * ((n : ℝ) * Δt))) := by
  rw [exactAmplification, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- **The phase angle of the `k`-th harmonic** on a grid of spacing `Δx`
([quarteroni2000numerical] §13.9): `φ_k = k Δx`. -/
noncomputable def phaseAngle (k : ℤ) (Δx : ℝ) : ℝ := k * Δx

/-- The exact amplification factor through the phase angle ([quarteroni2000numerical] (13.55)):
`g_k = e^{-i a λ φ_k}`. -/
theorem exactAmplification_eq_phaseAngle {Δt Δx lam : ℝ} (hΔx : Δx ≠ 0) (hlam : lam = Δt / Δx)
    (a : ℝ) (k : ℤ) :
    exactAmplification a Δt k = Complex.exp (-(I * ((a * lam * phaseAngle k Δx : ℝ) : ℂ))) := by
  subst hlam
  have hx : (a * (Δt / Δx) * ((k : ℝ) * Δx) : ℝ) = a * (k : ℝ) * Δt := by
    field_simp
    try ring
  rw [exactAmplification, phaseAngle, hx]
  congr 1
  push_cast
  ring

/-- **The exact solution neither amplifies nor damps any harmonic**: `|g_k| = 1`
([quarteroni2000numerical] §13.9). -/
theorem norm_exactAmplification (a Δt : ℝ) (k : ℤ) : ‖exactAmplification a Δt k‖ = 1 := by
  rw [exactAmplification, Complex.norm_exp]
  simp

/-- **The amplification (dissipation) error** of a numerical amplification factor
([quarteroni2000numerical] §13.9): `ε_a = |γ_k| / |g_k| = |γ_k|`. -/
noncomputable def amplificationError (γ : ℂ) : ℝ := ‖γ‖

/-- **The dispersion error** of a numerical amplification factor
([quarteroni2000numerical] §13.9): writing `γ_k = |γ_k| e^{-iωΔt}`, the ratio `ω/(k a)` of the
numerical phase speed to the exact speed is `-arg γ_k / (a λ φ_k)`. -/
noncomputable def dispersionError (a lam phi : ℝ) (γ : ℂ) : ℝ :=
  -Complex.arg γ / (a * lam * phi)

/-- The exact factor has amplification error `1`: no dissipation. -/
theorem amplificationError_exactAmplification (a Δt : ℝ) (k : ℤ) :
    amplificationError (exactAmplification a Δt k) = 1 := norm_exactAmplification a Δt k

/-- The exact factor has dispersion error `1`: no dispersion, as long as the phase is unambiguous
([quarteroni2000numerical] §13.9). -/
theorem dispersionError_exactAmplification {a lam Δt Δx : ℝ} {k : ℤ} (hΔx : Δx ≠ 0)
    (hlam : lam = Δt / Δx) (h0 : a * lam * phaseAngle k Δx ≠ 0)
    (hπ : |a * lam * phaseAngle k Δx| < π) :
    dispersionError a lam (phaseAngle k Δx) (exactAmplification a Δt k) = 1 := by
  rw [dispersionError, exactAmplification_eq_phaseAngle hΔx hlam]
  have harg : Complex.arg (Complex.exp (-(I * ((a * lam * phaseAngle k Δx : ℝ) : ℂ))))
      = -(a * lam * phaseAngle k Δx) := by
    rw [show -(I * ((a * lam * phaseAngle k Δx : ℝ) : ℂ))
        = ((-(a * lam * phaseAngle k Δx) : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I]
    refine Complex.arg_cos_add_sin_mul_I ?_
    rw [abs_lt] at hπ
    rw [Set.mem_Ioc]
    exact ⟨by linarith [hπ.2], by linarith [hπ.1]⟩
  rw [harg, neg_neg, div_self h0]

/-! ### Equivalent (modified) equations (§13.9.1) -/

/-- **The residual of a stencil on a smooth function of two variables**
([quarteroni2000numerical] §13.9.1): the amount by which `v` fails to satisfy the difference
equation, divided by `Δt`. On the travelling wave `u₀(x - a t)` it is the local truncation error
(`Hyperbolic.residual_comp_sub`). -/
noncomputable def residual (c : Stencil) (Δt Δx : ℝ) (v : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  (v x (t + Δt) - Stencil.apply c (fun i : ℤ => v (x + i * Δx) t) 0) / Δt

/-- The residual of a three-point stencil, written out. -/
theorem residual_threePoint (cm c0 cp Δt Δx : ℝ) (v : ℝ → ℝ → ℝ) (x t : ℝ) :
    residual (Stencil.threePoint cm c0 cp) Δt Δx v x t
      = (v x (t + Δt) - (cm * v (x - Δx) t + c0 * v x t + cp * v (x + Δx) t)) / Δt := by
  rw [residual, Stencil.threePoint_apply]
  simp only [smul_eq_mul]
  push_cast
  ring_nf

/-- **The residual on the exact travelling wave is the local truncation error**
([quarteroni2000numerical] §13.8.1 and §13.9.1). -/
theorem residual_comp_sub (c : Stencil) (a Δt Δx : ℝ) (u₀ : ℝ → ℝ) (x t : ℝ) :
    residual c Δt Δx (fun x t => u₀ (x - a * t)) x t
      = truncationError c a Δt Δx u₀ (x - a * t) := by
  rw [residual, truncationError]
  congr 2
  · congr 1
    ring
  · rw [Stencil.apply_apply, Stencil.apply_apply]
    exact Finset.sum_congr rfl fun s _ => by congr 2; ring

/-- **A classical solution of the equivalent (modified) equation**
`v_t + a v_x = μ v_xx + ν v_xxx` ([quarteroni2000numerical] (13.56)): `v` has partial derivatives
up to the third order in `x` on the whole plane and satisfies the equation everywhere. The
dissipative term is `μ v_xx` and the dispersive one `ν v_xxx`. -/
def IsModifiedSolution (a mu nu : ℝ) (v : ℝ → ℝ → ℝ) : Prop :=
  ∃ vx vt vxx vxt vxxx vxxt : ℝ → ℝ → ℝ,
    Transport.HasPartialsOn Set.univ v vx vt ∧ Transport.HasPartialsOn Set.univ vx vxx vxt ∧
      Transport.HasPartialsOn Set.univ vxx vxxx vxxt ∧
      ∀ x t : ℝ, vt x t + a * vx x t = mu * vxx x t + nu * vxxx x t

/-! ### Taylor expansion along the coordinate lines -/

section PartialTaylor

variable {v : ℝ → ℝ → ℝ} {D : ℕ → ℕ → ℝ → ℝ → ℝ} {M : ℝ} {i j : ℕ}

/-- A function differentiable on the whole plane has its first partial derivative as the
derivative of the restriction to a horizontal line.

TODO(backbone): this and its companion belong beside `Transport.HasPartialsOn`. -/
theorem hasPartialDerivFst_of_hasPartialsOn {u ux ut : ℝ → ℝ → ℝ}
    (h : Transport.HasPartialsOn Set.univ u ux ut) : HasPartialDerivFst u ux := by
  intro x t
  have h0 : HasFDerivAt (fun r : ℝ × ℝ => u r.1 r.2)
      (Transport.partialsCLM (ux x t) (ut x t)) (x, t) := by
    have h1 := h (x, t) (Set.mem_univ _)
    rwa [hasFDerivWithinAt_univ] at h1
  have hline : HasDerivAt (fun y : ℝ => (y, t)) (1, 0) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x t)
  have h2 := h0.comp_hasDerivAt x hline
  simp only [Transport.partialsCLM_apply, mul_one, mul_zero, add_zero, Function.comp_def] at h2
  exact h2

/-- A function differentiable on the whole plane has its second partial derivative as the
derivative of the restriction to a vertical line. -/
theorem hasPartialDerivSnd_of_hasPartialsOn {u ux ut : ℝ → ℝ → ℝ}
    (h : Transport.HasPartialsOn Set.univ u ux ut) : HasPartialDerivSnd u ut := by
  intro x t
  have h0 : HasFDerivAt (fun r : ℝ × ℝ => u r.1 r.2)
      (Transport.partialsCLM (ux x t) (ut x t)) (x, t) := by
    have h1 := h (x, t) (Set.mem_univ _)
    rwa [hasFDerivWithinAt_univ] at h1
  have hline : HasDerivAt (fun s : ℝ => (x, s)) (0, 1) t :=
    (hasDerivAt_const t x).prodMk (hasDerivAt_id t)
  have h2 := h0.comp_hasDerivAt t hline
  simp only [Transport.partialsCLM_apply, mul_one, mul_zero, zero_add, Function.comp_def] at h2
  exact h2

/-- **First-order Taylor expansion in space**: for a family of iterated partial derivatives with
`|∂_x^{i+2} ∂_t^j v| ≤ M`, `|D_{i,j}(x + h, t) - D_{i,j}(x, t) - h D_{i+1,j}(x, t)| ≤ M h²/2`. -/
theorem abs_taylor_fst_one (hD : HasPartialDerivs v D) (hM : ∀ y s, |D (i + 2) j y s| ≤ M)
    (x t h : ℝ) : |D i j (x + h) t - D i j x t - h * D (i + 1) j x t| ≤ M * h ^ 2 / 2 := by
  have hc : ContDiff ℝ 2 fun y => D i j y t := by exact_mod_cast hD.contDiff_fst 2 i j t
  have hb : ∀ y, |iteratedDeriv 2 (fun y => D i j y t) y| ≤ M := by
    rw [hD.iteratedDeriv_fst]
    exact fun y => hM y t
  simpa [hD.deriv_fst] using abs_taylor_one hc hb x h

/-- **Second-order Taylor expansion in space**. -/
theorem abs_taylor_fst_two (hD : HasPartialDerivs v D) (hM : ∀ y s, |D (i + 3) j y s| ≤ M)
    (x t h : ℝ) :
    |D i j (x + h) t - D i j x t - h * D (i + 1) j x t - h ^ 2 / 2 * D (i + 2) j x t|
      ≤ M * |h| ^ 3 / 6 := by
  have hc : ContDiff ℝ 3 fun y => D i j y t := by exact_mod_cast hD.contDiff_fst 3 i j t
  have hb : ∀ y, |iteratedDeriv 3 (fun y => D i j y t) y| ≤ M := by
    rw [hD.iteratedDeriv_fst]
    exact fun y => hM y t
  simpa [hD.deriv_fst, hD.iteratedDeriv_fst] using abs_taylor_two hc hb x h

/-- **Third-order Taylor expansion in space**. -/
theorem abs_taylor_fst_three (hD : HasPartialDerivs v D) (hM : ∀ y s, |D (i + 4) j y s| ≤ M)
    (x t h : ℝ) :
    |D i j (x + h) t - D i j x t - h * D (i + 1) j x t - h ^ 2 / 2 * D (i + 2) j x t
        - h ^ 3 / 6 * D (i + 3) j x t| ≤ M * h ^ 4 / 24 := by
  have hc : ContDiff ℝ 4 fun y => D i j y t := by exact_mod_cast hD.contDiff_fst 4 i j t
  have hb : ∀ y, |iteratedDeriv 4 (fun y => D i j y t) y| ≤ M := by
    rw [hD.iteratedDeriv_fst]
    exact fun y => hM y t
  simpa [hD.deriv_fst, hD.iteratedDeriv_fst] using abs_taylor_three hc hb x h

/-- **First-order Taylor expansion in time**. -/
theorem abs_taylor_snd_one (hD : HasPartialDerivs v D) (hM : ∀ y s, |D i (j + 2) y s| ≤ M)
    (x t h : ℝ) : |D i j x (t + h) - D i j x t - h * D i (j + 1) x t| ≤ M * h ^ 2 / 2 :=
  abs_taylor_fst_one hD.swap (fun y s => hM s y) t x h

/-- **Second-order Taylor expansion in time**. -/
theorem abs_taylor_snd_two (hD : HasPartialDerivs v D) (hM : ∀ y s, |D i (j + 3) y s| ≤ M)
    (x t h : ℝ) :
    |D i j x (t + h) - D i j x t - h * D i (j + 1) x t - h ^ 2 / 2 * D i (j + 2) x t|
      ≤ M * |h| ^ 3 / 6 :=
  abs_taylor_fst_two hD.swap (fun y s => hM s y) t x h

/-- **Third-order Taylor expansion in time**. -/
theorem abs_taylor_snd_three (hD : HasPartialDerivs v D) (hM : ∀ y s, |D i (j + 4) y s| ≤ M)
    (x t h : ℝ) :
    |D i j x (t + h) - D i j x t - h * D i (j + 1) x t - h ^ 2 / 2 * D i (j + 2) x t
        - h ^ 3 / 6 * D i (j + 3) x t| ≤ M * h ^ 4 / 24 :=
  abs_taylor_fst_three hD.swap (fun y s => hM s y) t x h

/-- **The second central difference in the first variable approximates the second partial
derivative**, with the constant `M h²/12` of the symmetric third-order expansion (the odd terms
cancel). -/
theorem abs_secondDiff_fst_sub_le (hD : HasPartialDerivs v D)
    (hM : ∀ y s, |D (i + 4) j y s| ≤ M) {h : ℝ} (hh : 0 < h) (x t : ℝ) :
    |(D i j (x + h) t - 2 * D i j x t + D i j (x - h) t) / h ^ 2 - D (i + 2) j x t|
      ≤ M * h ^ 2 / 12 := by
  have hh' : h ≠ 0 := ne_of_gt hh
  have hp := abs_taylor_fst_three hD hM x t h
  have hm := abs_taylor_fst_three hD hM x t (-h)
  rw [show x + -h = x - h from by ring, show M * (-h) ^ 4 / 24 = M * h ^ 4 / 24 from by ring] at hm
  have hid : ((D i j (x + h) t - 2 * D i j x t + D i j (x - h) t) / h ^ 2
        - D (i + 2) j x t) * h ^ 2
      = (D i j (x + h) t - D i j x t - h * D (i + 1) j x t - h ^ 2 / 2 * D (i + 2) j x t
          - h ^ 3 / 6 * D (i + 3) j x t)
        + (D i j (x - h) t - D i j x t - -h * D (i + 1) j x t - (-h) ^ 2 / 2 * D (i + 2) j x t
          - (-h) ^ 3 / 6 * D (i + 3) j x t) := by
    field_simp
    ring
  refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < h ^ 2)
  calc |(D i j (x + h) t - 2 * D i j x t + D i j (x - h) t) / h ^ 2 - D (i + 2) j x t| * h ^ 2
      = |((D i j (x + h) t - 2 * D i j x t + D i j (x - h) t) / h ^ 2
          - D (i + 2) j x t) * h ^ 2| := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < h ^ 2)]
    _ ≤ M * h ^ 4 / 24 + M * h ^ 4 / 24 := by
        rw [hid]
        exact (abs_add_le _ _).trans (add_le_add hp hm)
    _ = M * h ^ 2 / 12 * h ^ 2 := by ring

/-- **The second central difference in the second variable approximates the second partial
derivative**. -/
theorem abs_secondDiff_snd_sub_le (hD : HasPartialDerivs v D)
    (hM : ∀ y s, |D i (j + 4) y s| ≤ M) {h : ℝ} (hh : 0 < h) (x t : ℝ) :
    |(D i j x (t + h) - 2 * D i j x t + D i j x (t - h)) / h ^ 2 - D i (j + 2) x t|
      ≤ M * h ^ 2 / 12 :=
  abs_secondDiff_fst_sub_le hD.swap (fun y s => hM s y) hh t x

/-! ### The residual of a three-point scheme, expanded -/

/-- **The residual of a three-point scheme expanded to third order**
([quarteroni2000numerical] §13.9.1): Taylor's formula in `t` along the vertical line and in `x`
along the horizontal line through `(x, t)` turns

`τ = [v(x, t + Δt) - (cm v(x - Δx, t) + c0 v(x, t) + cp v(x + Δx, t))] / Δt`

into `v_t + (Δt/2) v_tt + (Δt²/6) v_ttt - Δt⁻¹ [(cm + c0 + cp - 1) v + Δx (cp - cm) v_x +
(Δx²/2)(cp + cm) v_xx + (Δx³/6)(cp - cm) v_xxx]` up to the two fourth-order remainders. Every
equivalent-equation computation of §13.9.1 is algebra over this identity. -/
theorem residual_threePoint_expansion (hD : HasPartialDerivs v D)
    (hM : ∀ i j, i + j = 4 → ∀ y s, |D i j y s| ≤ M) (cm c0 cp : ℝ) {Δt Δx : ℝ} (hΔt : 0 < Δt)
    (x t : ℝ) :
    |residual (Stencil.threePoint cm c0 cp) Δt Δx v x t
        - (D 0 1 x t + Δt / 2 * D 0 2 x t + Δt ^ 2 / 6 * D 0 3 x t
          - ((cm + c0 + cp - 1) * v x t + Δx * (cp - cm) * D 1 0 x t
            + Δx ^ 2 / 2 * (cp + cm) * D 2 0 x t + Δx ^ 3 / 6 * (cp - cm) * D 3 0 x t) / Δt)|
      ≤ M * (Δt ^ 3 / 24 + (|cm| + |cp|) * Δx ^ 4 / (24 * Δt)) := by
  have hΔt' : Δt ≠ 0 := ne_of_gt hΔt
  have hv : D 0 0 = v := hD.eq_zero_zero
  have hRt : |v x (t + Δt) - v x t - Δt * D 0 1 x t - Δt ^ 2 / 2 * D 0 2 x t
      - Δt ^ 3 / 6 * D 0 3 x t| ≤ M * Δt ^ 4 / 24 := by
    have h := abs_taylor_snd_three hD (hM 0 4 rfl) x t Δt
    rwa [hv] at h
  have hRp : |v (x + Δx) t - v x t - Δx * D 1 0 x t - Δx ^ 2 / 2 * D 2 0 x t
      - Δx ^ 3 / 6 * D 3 0 x t| ≤ M * Δx ^ 4 / 24 := by
    have h := abs_taylor_fst_three hD (hM 4 0 rfl) x t Δx
    rwa [hv] at h
  have hRm : |v (x - Δx) t - v x t + Δx * D 1 0 x t - Δx ^ 2 / 2 * D 2 0 x t
      + Δx ^ 3 / 6 * D 3 0 x t| ≤ M * Δx ^ 4 / 24 := by
    have h := abs_taylor_fst_three hD (hM 4 0 rfl) x t (-Δx)
    rw [hv, show x + -Δx = x - Δx from by ring,
      show v (x - Δx) t - v x t - -Δx * D 1 0 x t - (-Δx) ^ 2 / 2 * D 2 0 x t
          - (-Δx) ^ 3 / 6 * D 3 0 x t
        = v (x - Δx) t - v x t + Δx * D 1 0 x t - Δx ^ 2 / 2 * D 2 0 x t
          + Δx ^ 3 / 6 * D 3 0 x t from by ring,
      show M * (-Δx) ^ 4 / 24 = M * Δx ^ 4 / 24 from by ring] at h
    exact h
  have hid : (residual (Stencil.threePoint cm c0 cp) Δt Δx v x t
        - (D 0 1 x t + Δt / 2 * D 0 2 x t + Δt ^ 2 / 6 * D 0 3 x t
          - ((cm + c0 + cp - 1) * v x t + Δx * (cp - cm) * D 1 0 x t
            + Δx ^ 2 / 2 * (cp + cm) * D 2 0 x t + Δx ^ 3 / 6 * (cp - cm) * D 3 0 x t) / Δt)) * Δt
      = (v x (t + Δt) - v x t - Δt * D 0 1 x t - Δt ^ 2 / 2 * D 0 2 x t
          - Δt ^ 3 / 6 * D 0 3 x t)
        - cm * (v (x - Δx) t - v x t + Δx * D 1 0 x t - Δx ^ 2 / 2 * D 2 0 x t
            + Δx ^ 3 / 6 * D 3 0 x t)
        - cp * (v (x + Δx) t - v x t - Δx * D 1 0 x t - Δx ^ 2 / 2 * D 2 0 x t
            - Δx ^ 3 / 6 * D 3 0 x t) := by
    rw [residual_threePoint]
    field_simp
    ring
  refine le_of_mul_le_mul_right ?_ hΔt
  calc |residual (Stencil.threePoint cm c0 cp) Δt Δx v x t
        - (D 0 1 x t + Δt / 2 * D 0 2 x t + Δt ^ 2 / 6 * D 0 3 x t
          - ((cm + c0 + cp - 1) * v x t + Δx * (cp - cm) * D 1 0 x t
            + Δx ^ 2 / 2 * (cp + cm) * D 2 0 x t
            + Δx ^ 3 / 6 * (cp - cm) * D 3 0 x t) / Δt)| * Δt
      = |(residual (Stencil.threePoint cm c0 cp) Δt Δx v x t
          - (D 0 1 x t + Δt / 2 * D 0 2 x t + Δt ^ 2 / 6 * D 0 3 x t
            - ((cm + c0 + cp - 1) * v x t + Δx * (cp - cm) * D 1 0 x t
              + Δx ^ 2 / 2 * (cp + cm) * D 2 0 x t
              + Δx ^ 3 / 6 * (cp - cm) * D 3 0 x t) / Δt)) * Δt| := by
        rw [abs_mul, abs_of_pos hΔt]
    _ ≤ M * Δt ^ 4 / 24 + |cm| * (M * Δx ^ 4 / 24) + |cp| * (M * Δx ^ 4 / 24) := by
        rw [hid]
        refine (abs_sub_le' _ _).trans (add_le_add ((abs_sub_le' _ _).trans
          (add_le_add hRt ?_)) ?_)
        · rw [abs_mul]
          exact mul_le_mul_of_nonneg_left hRm (abs_nonneg cm)
        · rw [abs_mul]
          exact mul_le_mul_of_nonneg_left hRp (abs_nonneg cp)
    _ = M * (Δt ^ 3 / 24 + (|cm| + |cp|) * Δx ^ 4 / (24 * Δt)) * Δt := by
        field_simp
        ring

/-! ### The equivalent equation of the upwind scheme -/

/-- **The Taylor expansions of the upwind residual** ([quarteroni2000numerical] (13.57)–(13.58)):
for `a > 0` the residual of (13.41) on a smooth `v` is `v_t + a v_x` up to `O(Δt + Δx)`, and
`v_t + (Δt/2) v_tt + a v_x - (a Δx/2) v_xx` up to `O(Δt² + Δx²)`.

The book prints (13.58) with `a (v_x + (Δx/2) v_xx)`; the backward difference
`(v(x, t) - v(x - Δx, t))/Δx` is `v_x - (Δx/2) v_xx + O(Δx²)`, so the sign there is an erratum —
and the minus sign is what produces the `μ = a Δx/2 - a² Δt/2` of (13.59). -/
theorem abs_residual_upwind_sub_le (hD : HasPartialDerivs v D) {a Δt Δx lam : ℝ} (ha : 0 < a)
    (hΔt : 0 < Δt) (hΔx : 0 < Δx) (hlam : lam = Δt / Δx)
    (hM₂ : ∀ i j, i + j = 2 → ∀ y s, |D i j y s| ≤ M) (x t : ℝ) :
    |residual (upwind a lam) Δt Δx v x t - (D 0 1 x t + a * D 1 0 x t)|
      ≤ Δt / 2 * M + a * Δx / 2 * M := by
  subst hlam
  have hΔt' : Δt ≠ 0 := ne_of_gt hΔt
  have hΔx' : Δx ≠ 0 := ne_of_gt hΔx
  have hv : D 0 0 = v := hD.eq_zero_zero
  have hRt : |v x (t + Δt) - v x t - Δt * D 0 1 x t| ≤ M * Δt ^ 2 / 2 := by
    have h := abs_taylor_snd_one hD (hM₂ 0 2 rfl) x t Δt
    rwa [hv] at h
  have hRm : |v (x - Δx) t - v x t + Δx * D 1 0 x t| ≤ M * Δx ^ 2 / 2 := by
    have h := abs_taylor_fst_one hD (hM₂ 2 0 rfl) x t (-Δx)
    rw [hv, show x + -Δx = x - Δx from by ring,
      show v (x - Δx) t - v x t - -Δx * D 1 0 x t
        = v (x - Δx) t - v x t + Δx * D 1 0 x t from by ring,
      show M * (-Δx) ^ 2 / 2 = M * Δx ^ 2 / 2 from by ring] at h
    exact h
  have hid : (residual (upwind a (Δt / Δx)) Δt Δx v x t - (D 0 1 x t + a * D 1 0 x t)) * Δt
      = (v x (t + Δt) - v x t - Δt * D 0 1 x t)
        - Δt / Δx * a * (v (x - Δx) t - v x t + Δx * D 1 0 x t) := by
    rw [upwind_eq_of_pos ha, residual_threePoint]
    field_simp
    ring
  refine le_of_mul_le_mul_right ?_ hΔt
  calc |residual (upwind a (Δt / Δx)) Δt Δx v x t - (D 0 1 x t + a * D 1 0 x t)| * Δt
      = |(residual (upwind a (Δt / Δx)) Δt Δx v x t - (D 0 1 x t + a * D 1 0 x t)) * Δt| := by
        rw [abs_mul, abs_of_pos hΔt]
    _ ≤ M * Δt ^ 2 / 2 + Δt / Δx * a * (M * Δx ^ 2 / 2) := by
        rw [hid]
        refine (abs_sub_le' _ _).trans (add_le_add hRt ?_)
        rw [abs_mul, show |Δt / Δx * a| = Δt / Δx * a by
          rw [abs_of_nonneg (by positivity)]]
        exact mul_le_mul_of_nonneg_left hRm (by positivity)
    _ = (Δt / 2 * M + a * Δx / 2 * M) * Δt := by field_simp

/-- **The second Taylor expansion of the upwind residual** ([quarteroni2000numerical] (13.58)):
the residual is `v_t + (Δt/2) v_tt + a v_x - (a Δx/2) v_xx` up to `O(Δt² + Δx²)`. -/
theorem abs_residual_upwind_sub_le_two (hD : HasPartialDerivs v D) {a Δt Δx lam : ℝ} (ha : 0 < a)
    (hΔt : 0 < Δt) (hΔx : 0 < Δx) (hlam : lam = Δt / Δx)
    (hM₃ : ∀ i j, i + j = 3 → ∀ y s, |D i j y s| ≤ M) (x t : ℝ) :
    |residual (upwind a lam) Δt Δx v x t
        - (D 0 1 x t + Δt / 2 * D 0 2 x t + a * D 1 0 x t - a * Δx / 2 * D 2 0 x t)|
      ≤ Δt ^ 2 / 6 * M + a * Δx ^ 2 / 6 * M := by
  subst hlam
  have hΔt' : Δt ≠ 0 := ne_of_gt hΔt
  have hΔx' : Δx ≠ 0 := ne_of_gt hΔx
  have hv : D 0 0 = v := hD.eq_zero_zero
  have hRt : |v x (t + Δt) - v x t - Δt * D 0 1 x t - Δt ^ 2 / 2 * D 0 2 x t|
      ≤ M * Δt ^ 3 / 6 := by
    have h := abs_taylor_snd_two hD (hM₃ 0 3 rfl) x t Δt
    rw [hv, abs_of_pos hΔt] at h
    exact h
  have hRm : |v (x - Δx) t - v x t + Δx * D 1 0 x t - Δx ^ 2 / 2 * D 2 0 x t|
      ≤ M * Δx ^ 3 / 6 := by
    have h := abs_taylor_fst_two hD (hM₃ 3 0 rfl) x t (-Δx)
    rw [hv, show x + -Δx = x - Δx from by ring,
      show v (x - Δx) t - v x t - -Δx * D 1 0 x t - (-Δx) ^ 2 / 2 * D 2 0 x t
        = v (x - Δx) t - v x t + Δx * D 1 0 x t - Δx ^ 2 / 2 * D 2 0 x t from by ring,
      abs_neg, abs_of_pos hΔx] at h
    exact h
  have hid : (residual (upwind a (Δt / Δx)) Δt Δx v x t
        - (D 0 1 x t + Δt / 2 * D 0 2 x t + a * D 1 0 x t - a * Δx / 2 * D 2 0 x t)) * Δt
      = (v x (t + Δt) - v x t - Δt * D 0 1 x t - Δt ^ 2 / 2 * D 0 2 x t)
        - Δt / Δx * a * (v (x - Δx) t - v x t + Δx * D 1 0 x t - Δx ^ 2 / 2 * D 2 0 x t) := by
    rw [upwind_eq_of_pos ha, residual_threePoint]
    field_simp
    ring
  refine le_of_mul_le_mul_right ?_ hΔt
  calc |residual (upwind a (Δt / Δx)) Δt Δx v x t
        - (D 0 1 x t + Δt / 2 * D 0 2 x t + a * D 1 0 x t - a * Δx / 2 * D 2 0 x t)| * Δt
      = |(residual (upwind a (Δt / Δx)) Δt Δx v x t
          - (D 0 1 x t + Δt / 2 * D 0 2 x t + a * D 1 0 x t
            - a * Δx / 2 * D 2 0 x t)) * Δt| := by rw [abs_mul, abs_of_pos hΔt]
    _ ≤ M * Δt ^ 3 / 6 + Δt / Δx * a * (M * Δx ^ 3 / 6) := by
        rw [hid]
        refine (abs_sub_le' _ _).trans (add_le_add hRt ?_)
        rw [abs_mul, show |Δt / Δx * a| = Δt / Δx * a by
          rw [abs_of_nonneg (by positivity)]]
        exact mul_le_mul_of_nonneg_left hRm (by positivity)
    _ = (Δt ^ 2 / 6 * M + a * Δx ^ 2 / 6 * M) * Δt := by field_simp

/-- **A solution of the equivalent equation, read through a family of named partial derivatives**:
the relation (13.56) between the members of the family
(`FiniteDifference.Hyperbolic.IsModifiedSolution` quantifies its partial derivatives
existentially, and the derivative of a function is unique). -/
theorem IsModifiedSolution.eq_of_hasPartialDerivs {a mu nu : ℝ} (hv : IsModifiedSolution a mu nu v)
    (hD : HasPartialDerivs v D) (x t : ℝ) :
    D 0 1 x t + a * D 1 0 x t = mu * D 2 0 x t + nu * D 3 0 x t := by
  obtain ⟨vx, vt, vxx, vxt, vxxx, vxxt, h1, h2, h3, heq⟩ := hv
  have hv0 : HasPartialDerivFst v (D 1 0) := by
    rw [← hD.eq_zero_zero]
    exact hD.hasPartialDerivFst 0 0
  have hv1 : HasPartialDerivSnd v (D 0 1) := by
    rw [← hD.eq_zero_zero]
    exact hD.hasPartialDerivSnd 0 0
  have e1 : ∀ y s, vx y s = D 1 0 y s :=
    HasPartialDerivFst.congr (hasPartialDerivFst_of_hasPartialsOn h1) hv0 fun _ _ => rfl
  have e2 : ∀ y s, vt y s = D 0 1 y s :=
    HasPartialDerivSnd.congr (hasPartialDerivSnd_of_hasPartialsOn h1) hv1 fun _ _ => rfl
  have e3 : ∀ y s, vxx y s = D 2 0 y s :=
    HasPartialDerivFst.congr (hasPartialDerivFst_of_hasPartialsOn h2)
      (hD.hasPartialDerivFst 1 0) e1
  have e4 : ∀ y s, vxxx y s = D 3 0 y s :=
    HasPartialDerivFst.congr (hasPartialDerivFst_of_hasPartialsOn h3)
      (hD.hasPartialDerivFst 2 0) e3
  rw [← e1, ← e2, ← e3, ← e4]
  exact heq x t

/-- **The equivalent equation differentiated**: every iterated partial derivative of a solution of
`v_t + a v_x = μ v_xx + ν v_xxx` satisfies the same relation
(`∂_x^i ∂_t^j` of [quarteroni2000numerical] (13.56)). -/
theorem IsModifiedSolution.partial_eq {a mu nu : ℝ} (hv : IsModifiedSolution a mu nu v)
    (hD : HasPartialDerivs v D) (i j : ℕ) (x t : ℝ) :
    D i (j + 1) x t + a * D (i + 1) j x t = mu * D (i + 2) j x t + nu * D (i + 3) j x t := by
  have stepFst : ∀ i j : ℕ, (∀ y s : ℝ, D i (j + 1) y s + a * D (i + 1) j y s
        = mu * D (i + 2) j y s + nu * D (i + 3) j y s) →
      ∀ y s : ℝ, D (i + 1) (j + 1) y s + a * D (i + 2) j y s
        = mu * D (i + 3) j y s + nu * D (i + 4) j y s := fun i j h =>
    HasPartialDerivFst.congr
      ((hD.hasPartialDerivFst i (j + 1)).add ((hD.hasPartialDerivFst (i + 1) j).const_mul a))
      (((hD.hasPartialDerivFst (i + 2) j).const_mul mu).add
        ((hD.hasPartialDerivFst (i + 3) j).const_mul nu)) h
  have stepSnd : ∀ i j : ℕ, (∀ y s : ℝ, D i (j + 1) y s + a * D (i + 1) j y s
        = mu * D (i + 2) j y s + nu * D (i + 3) j y s) →
      ∀ y s : ℝ, D i (j + 2) y s + a * D (i + 1) (j + 1) y s
        = mu * D (i + 2) (j + 1) y s + nu * D (i + 3) (j + 1) y s := fun i j h =>
    HasPartialDerivSnd.congr
      ((hD.hasPartialDerivSnd i (j + 1)).add ((hD.hasPartialDerivSnd (i + 1) j).const_mul a))
      (((hD.hasPartialDerivSnd (i + 2) j).const_mul mu).add
        ((hD.hasPartialDerivSnd (i + 3) j).const_mul nu)) h
  have key : ∀ j i : ℕ, ∀ y s : ℝ, D i (j + 1) y s + a * D (i + 1) j y s
      = mu * D (i + 2) j y s + nu * D (i + 3) j y s := by
    intro j
    induction j with
    | zero =>
      intro i
      induction i with
      | zero => exact hv.eq_of_hasPartialDerivs hD
      | succ i ih => exact stepFst i 0 ih
    | succ j ihj => exact fun i => stepSnd i j (ihj i)
  exact key j i x t

/-- **The second-order equivalent equation of the upwind scheme**
([quarteroni2000numerical] (13.59)): for `a > 0` and `μ = a Δx/2 - a² Δt/2`, a solution of
`v_t + a v_x = μ v_xx` leaves the upwind scheme a residual `O(Δt² + Δt Δx + Δx²)` — one order
better than the `O(Δt + Δx)` left by a solution of the transport equation itself
(`FiniteDifference.Hyperbolic.abs_truncationError_upwind_le`).

The mechanism is that the equation is differentiated into `v_tt = a² v_xx + μ (v_xxt - a v_xxx)`
(`FiniteDifference.Hyperbolic.IsModifiedSolution.partial_eq`), which cancels the `(Δt/2) v_tt` of
(13.58) against the `-(a Δx/2) v_xx` exactly when `μ` has the stated value. -/
theorem abs_residual_upwind_le_of_isModifiedSolution (hD : HasPartialDerivs v D)
    {a mu Δt Δx lam : ℝ} (ha : 0 < a) (hΔt : 0 < Δt) (hΔx : 0 < Δx) (hlam : lam = Δt / Δx)
    (hmu : mu = a * Δx / 2 - a ^ 2 * Δt / 2) (hv : IsModifiedSolution a mu 0 v)
    (hM : ∀ i j, i + j = 3 → ∀ y s, |D i j y s| ≤ M) (x t : ℝ) :
    |residual (upwind a lam) Δt Δx v x t|
      ≤ M * (1 + a) ^ 3 * (Δt ^ 2 + Δt * Δx + Δx ^ 2) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 3 rfl 0 0)
  have hE := abs_residual_upwind_sub_le_two hD ha hΔt hΔx hlam hM x t
  -- the equation and its two derivatives
  have p00 : D 0 1 x t + a * D 1 0 x t = mu * D 2 0 x t + 0 * D 3 0 x t :=
    hv.eq_of_hasPartialDerivs hD x t
  have p01 : D 0 2 x t + a * D 1 1 x t = mu * D 2 1 x t + 0 * D 3 1 x t :=
    hv.partial_eq hD 0 1 x t
  have p10 : D 1 1 x t + a * D 2 0 x t = mu * D 3 0 x t + 0 * D 4 0 x t :=
    hv.partial_eq hD 1 0 x t
  have hkey : residual (upwind a lam) Δt Δx v x t
      = Δt * mu / 2 * (D 2 1 x t - a * D 3 0 x t)
        + (residual (upwind a lam) Δt Δx v x t
          - (D 0 1 x t + Δt / 2 * D 0 2 x t + a * D 1 0 x t - a * Δx / 2 * D 2 0 x t)) := by
    linear_combination p00 + (Δt / 2) * p01 - (a * Δt / 2) * p10 + D 2 0 x t * hmu
  have hmuabs : |mu| ≤ a * Δx / 2 + a ^ 2 * Δt / 2 := by
    rw [hmu]
    refine (abs_sub_le' _ _).trans ?_
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ a * Δx / 2),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ a ^ 2 * Δt / 2)]
  have hb1 : |D 2 1 x t - a * D 3 0 x t| ≤ M + a * M := by
    refine (abs_sub_le' _ _).trans (add_le_add (hM 2 1 rfl x t) ?_)
    rw [abs_mul, abs_of_pos ha]
    exact mul_le_mul_of_nonneg_left (hM 3 0 rfl x t) ha.le
  calc |residual (upwind a lam) Δt Δx v x t|
      ≤ |Δt * mu / 2 * (D 2 1 x t - a * D 3 0 x t)|
        + |residual (upwind a lam) Δt Δx v x t
          - (D 0 1 x t + Δt / 2 * D 0 2 x t + a * D 1 0 x t - a * Δx / 2 * D 2 0 x t)| := by
        conv_lhs => rw [hkey]
        exact abs_add_le _ _
    _ ≤ Δt * (a * Δx / 2 + a ^ 2 * Δt / 2) / 2 * (M + a * M)
        + (Δt ^ 2 / 6 * M + a * Δx ^ 2 / 6 * M) := by
        refine add_le_add ?_ hE
        rw [abs_mul, abs_div, abs_mul, abs_of_pos hΔt, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        refine mul_le_mul ?_ hb1 (abs_nonneg _) (by positivity)
        gcongr
    _ = M * ((1 + a) * a / 4 * (Δt * Δx) + ((1 + a) * a ^ 2 / 4 + 1 / 6) * Δt ^ 2
        + a / 6 * Δx ^ 2) := by ring
    _ ≤ M * ((1 + a) ^ 3 * (Δt * Δx) + (1 + a) ^ 3 * Δt ^ 2 + (1 + a) ^ 3 * Δx ^ 2) := by
        have h1 : (1 + a) * a / 4 ≤ (1 + a) ^ 3 := by nlinarith [ha.le, sq_nonneg a]
        have h2 : (1 + a) * a ^ 2 / 4 + 1 / 6 ≤ (1 + a) ^ 3 := by nlinarith [ha.le, sq_nonneg a]
        have h3 : a / 6 ≤ (1 + a) ^ 3 := by nlinarith [ha.le, sq_nonneg a]
        refine mul_le_mul_of_nonneg_left (add_le_add (add_le_add ?_ ?_) ?_) hM0
        · exact mul_le_mul_of_nonneg_right h1 (by positivity)
        · exact mul_le_mul_of_nonneg_right h2 (by positivity)
        · exact mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = M * (1 + a) ^ 3 * (Δt ^ 2 + Δt * Δx + Δx ^ 2) := by ring

/-! ### The third-order equivalent equation of a three-point scheme -/

/-- Bounding one term of an expansion by the bound on its derivative factor. -/
private theorem abs_mul_le_of_abs_le {c d N : ℝ} (h : |d| ≤ N) : |c * d| ≤ |c| * N := by
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg c)

/-- **The third-order equivalent equation of a conservative three-point scheme**
([quarteroni2000numerical] §13.9.1, Table 13.2): let `c = threePoint cm c0 cp` be consistent
(`cm + c0 + cp = 1`) with `cp - cm = -λ a`, and let `μ`, `ν` be the Warming–Hyett coefficients,
i.e. `(Δx²/2)(cp + cm) = Δt (μ + a² Δt/2)` and `ν + a Δx²/6 = a μ Δt + a³ Δt²/6`. Then a solution
of the equivalent equation `v_t + a v_x = μ v_xx + ν v_xxx` leaves the scheme a residual made
entirely of terms carrying a factor `μ²`, `μν`, `ν`, `Δt μ` or `Δt ν`: the `O(Δx)` term in `v_xx`
and the `O(Δx²)` term in `v_xxx` both cancel, which is exactly what fixes `μ` and `ν`.

The proof substitutes `∂_t = -a ∂_x + μ ∂_x² + ν ∂_x³` five times
(`FiniteDifference.Hyperbolic.IsModifiedSolution.partial_eq`) into the two time derivatives of
`Hyperbolic.residual_threePoint_expansion`, which is why partial derivatives up to order `5`
enter. With `Δt = λ Δx` and `λ` fixed, `μ = O(Δx)` and `ν = O(Δx²)`, so the bound is `O(Δx³)`,
one order better than the `O(Δx²)` of the second-order equivalent equation. -/
theorem abs_residual_threePoint_le_of_isModifiedSolution (hD : HasPartialDerivs v D)
    {a mu nu Δt Δx lam cm c0 cp : ℝ} (hΔt : 0 < Δt) (hΔx : 0 < Δx) (hlam : lam = Δt / Δx)
    (hsum : cm + c0 + cp = 1) (hdiff : cp - cm = -(lam * a))
    (hplus : Δx ^ 2 / 2 * (cp + cm) = Δt * (mu + a ^ 2 * Δt / 2))
    (hnu : nu + a * Δx ^ 2 / 6 = a * mu * Δt + a ^ 3 * Δt ^ 2 / 6)
    (hv : IsModifiedSolution a mu nu v) (hM : ∀ i j, i + j ≤ 5 → ∀ y s, |D i j y s| ≤ M)
    (x t : ℝ) :
    |residual (Stencil.threePoint cm c0 cp) Δt Δx v x t|
      ≤ M * (Δt * (mu ^ 2 + |a| * |nu| + |mu| * |nu| + |nu|) / 2
          + Δt ^ 2 * (a ^ 2 + |a| + 1) * (|mu| + |nu|) / 6
          + Δt ^ 3 / 24 + (|cm| + |cp|) * Δx ^ 4 / (24 * Δt)) := by
  subst hlam
  have hΔt' : Δt ≠ 0 := ne_of_gt hΔt
  have hΔx' : Δx ≠ 0 := ne_of_gt hΔx
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 0 (by omega) 0 0)
  have hexp := residual_threePoint_expansion (Δx := Δx) hD (fun i j h => hM i j (by omega))
    cm c0 cp hΔt x t
  have q00 : D 0 1 x t + a * D 1 0 x t = mu * D 2 0 x t + nu * D 3 0 x t :=
    hv.eq_of_hasPartialDerivs hD x t
  have q01 : D 0 2 x t + a * D 1 1 x t = mu * D 2 1 x t + nu * D 3 1 x t :=
    hv.partial_eq hD 0 1 x t
  have q10 : D 1 1 x t + a * D 2 0 x t = mu * D 3 0 x t + nu * D 4 0 x t :=
    hv.partial_eq hD 1 0 x t
  have q20 : D 2 1 x t + a * D 3 0 x t = mu * D 4 0 x t + nu * D 5 0 x t :=
    hv.partial_eq hD 2 0 x t
  have q02 : D 0 3 x t + a * D 1 2 x t = mu * D 2 2 x t + nu * D 3 2 x t :=
    hv.partial_eq hD 0 2 x t
  have q11 : D 1 2 x t + a * D 2 1 x t = mu * D 3 1 x t + nu * D 4 1 x t :=
    hv.partial_eq hD 1 1 x t
  have hE : D 0 1 x t + Δt / 2 * D 0 2 x t + Δt ^ 2 / 6 * D 0 3 x t
        - ((cm + c0 + cp - 1) * v x t + Δx * (cp - cm) * D 1 0 x t
          + Δx ^ 2 / 2 * (cp + cm) * D 2 0 x t + Δx ^ 3 / 6 * (cp - cm) * D 3 0 x t) / Δt
      = D 0 1 x t + a * D 1 0 x t + Δt / 2 * D 0 2 x t + Δt ^ 2 / 6 * D 0 3 x t
        - (mu + a ^ 2 * Δt / 2) * D 2 0 x t + a * Δx ^ 2 / 6 * D 3 0 x t := by
    rw [hsum, hdiff, hplus]
    field_simp
    ring
  have hE2 : D 0 1 x t + a * D 1 0 x t + Δt / 2 * D 0 2 x t + Δt ^ 2 / 6 * D 0 3 x t
        - (mu + a ^ 2 * Δt / 2) * D 2 0 x t + a * Δx ^ 2 / 6 * D 3 0 x t
      = (Δt * (mu ^ 2 - a * nu) / 2 + Δt ^ 2 * a ^ 2 * mu / 6) * D 4 0 x t
        + (Δt * mu * nu / 2 + Δt ^ 2 * a ^ 2 * nu / 6) * D 5 0 x t
        + (Δt * nu / 2 - Δt ^ 2 * a * mu / 6) * D 3 1 x t
        + -(Δt ^ 2 * a * nu / 6) * D 4 1 x t
        + Δt ^ 2 * mu / 6 * D 2 2 x t
        + Δt ^ 2 * nu / 6 * D 3 2 x t := by
    linear_combination q00 + (Δt / 2) * q01 - (a * Δt / 2) * q10
      + (mu * Δt / 2 + a ^ 2 * Δt ^ 2 / 6) * q20 + (Δt ^ 2 / 6) * q02 - (a * Δt ^ 2 / 6) * q11
      + D 3 0 x t * hnu
  have hkey : residual (Stencil.threePoint cm c0 cp) Δt Δx v x t
      = ((Δt * (mu ^ 2 - a * nu) / 2 + Δt ^ 2 * a ^ 2 * mu / 6) * D 4 0 x t
          + (Δt * mu * nu / 2 + Δt ^ 2 * a ^ 2 * nu / 6) * D 5 0 x t
          + (Δt * nu / 2 - Δt ^ 2 * a * mu / 6) * D 3 1 x t
          + -(Δt ^ 2 * a * nu / 6) * D 4 1 x t
          + Δt ^ 2 * mu / 6 * D 2 2 x t
          + Δt ^ 2 * nu / 6 * D 3 2 x t)
        + (residual (Stencil.threePoint cm c0 cp) Δt Δx v x t
          - (D 0 1 x t + Δt / 2 * D 0 2 x t + Δt ^ 2 / 6 * D 0 3 x t
            - ((cm + c0 + cp - 1) * v x t + Δx * (cp - cm) * D 1 0 x t
              + Δx ^ 2 / 2 * (cp + cm) * D 2 0 x t
              + Δx ^ 3 / 6 * (cp - cm) * D 3 0 x t) / Δt)) := by
    linear_combination hE.trans hE2
  have hT : |(Δt * (mu ^ 2 - a * nu) / 2 + Δt ^ 2 * a ^ 2 * mu / 6) * D 4 0 x t
        + (Δt * mu * nu / 2 + Δt ^ 2 * a ^ 2 * nu / 6) * D 5 0 x t
        + (Δt * nu / 2 - Δt ^ 2 * a * mu / 6) * D 3 1 x t
        + -(Δt ^ 2 * a * nu / 6) * D 4 1 x t
        + Δt ^ 2 * mu / 6 * D 2 2 x t
        + Δt ^ 2 * nu / 6 * D 3 2 x t|
      ≤ (|Δt * (mu ^ 2 - a * nu) / 2 + Δt ^ 2 * a ^ 2 * mu / 6|
          + |Δt * mu * nu / 2 + Δt ^ 2 * a ^ 2 * nu / 6|
          + |Δt * nu / 2 - Δt ^ 2 * a * mu / 6| + |-(Δt ^ 2 * a * nu / 6)|
          + |Δt ^ 2 * mu / 6| + |Δt ^ 2 * nu / 6|) * M := by
    have b1 := abs_mul_le_of_abs_le (c := Δt * (mu ^ 2 - a * nu) / 2 + Δt ^ 2 * a ^ 2 * mu / 6)
      (hM 4 0 (by omega) x t)
    have b2 := abs_mul_le_of_abs_le (c := Δt * mu * nu / 2 + Δt ^ 2 * a ^ 2 * nu / 6)
      (hM 5 0 (by omega) x t)
    have b3 := abs_mul_le_of_abs_le (c := Δt * nu / 2 - Δt ^ 2 * a * mu / 6)
      (hM 3 1 (by omega) x t)
    have b4 := abs_mul_le_of_abs_le (c := -(Δt ^ 2 * a * nu / 6)) (hM 4 1 (by omega) x t)
    have b5 := abs_mul_le_of_abs_le (c := Δt ^ 2 * mu / 6) (hM 2 2 (by omega) x t)
    have b6 := abs_mul_le_of_abs_le (c := Δt ^ 2 * nu / 6) (hM 3 2 (by omega) x t)
    calc |(Δt * (mu ^ 2 - a * nu) / 2 + Δt ^ 2 * a ^ 2 * mu / 6) * D 4 0 x t
          + (Δt * mu * nu / 2 + Δt ^ 2 * a ^ 2 * nu / 6) * D 5 0 x t
          + (Δt * nu / 2 - Δt ^ 2 * a * mu / 6) * D 3 1 x t
          + -(Δt ^ 2 * a * nu / 6) * D 4 1 x t
          + Δt ^ 2 * mu / 6 * D 2 2 x t
          + Δt ^ 2 * nu / 6 * D 3 2 x t|
        ≤ |Δt * (mu ^ 2 - a * nu) / 2 + Δt ^ 2 * a ^ 2 * mu / 6| * M
            + |Δt * mu * nu / 2 + Δt ^ 2 * a ^ 2 * nu / 6| * M
            + |Δt * nu / 2 - Δt ^ 2 * a * mu / 6| * M + |-(Δt ^ 2 * a * nu / 6)| * M
            + |Δt ^ 2 * mu / 6| * M + |Δt ^ 2 * nu / 6| * M :=
          (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
            ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
              ((abs_add_le _ _).trans (add_le_add b1 b2)) b3)) b4)) b5)) b6)
      _ = _ := by ring
  have hcoef : |Δt * (mu ^ 2 - a * nu) / 2 + Δt ^ 2 * a ^ 2 * mu / 6|
        + |Δt * mu * nu / 2 + Δt ^ 2 * a ^ 2 * nu / 6|
        + |Δt * nu / 2 - Δt ^ 2 * a * mu / 6| + |-(Δt ^ 2 * a * nu / 6)|
        + |Δt ^ 2 * mu / 6| + |Δt ^ 2 * nu / 6|
      ≤ Δt * (mu ^ 2 + |a| * |nu| + |mu| * |nu| + |nu|) / 2
        + Δt ^ 2 * (a ^ 2 + |a| + 1) * (|mu| + |nu|) / 6 := by
    have e1 : |Δt * (mu ^ 2 - a * nu) / 2 + Δt ^ 2 * a ^ 2 * mu / 6|
        ≤ Δt * (mu ^ 2 + |a| * |nu|) / 2 + Δt ^ 2 * a ^ 2 * |mu| / 6 := by
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_div, abs_mul, abs_of_pos hΔt, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        gcongr
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_of_nonneg (sq_nonneg mu)]
      · rw [abs_div, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Δt ^ 2),
          abs_of_nonneg (sq_nonneg a), abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    have e2 : |Δt * mu * nu / 2 + Δt ^ 2 * a ^ 2 * nu / 6|
        ≤ Δt * (|mu| * |nu|) / 2 + Δt ^ 2 * a ^ 2 * |nu| / 6 := by
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_div, abs_mul, abs_mul, abs_of_pos hΔt,
          abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        exact le_of_eq (by ring)
      · rw [abs_div, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Δt ^ 2),
          abs_of_nonneg (sq_nonneg a), abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    have e3 : |Δt * nu / 2 - Δt ^ 2 * a * mu / 6|
        ≤ Δt * |nu| / 2 + Δt ^ 2 * |a| * |mu| / 6 := by
      refine (abs_sub _ _).trans (add_le_add ?_ ?_)
      · rw [abs_div, abs_mul, abs_of_pos hΔt, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      · rw [abs_div, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Δt ^ 2),
          abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    have e4 : |-(Δt ^ 2 * a * nu / 6)| = Δt ^ 2 * |a| * |nu| / 6 := by
      rw [abs_neg, abs_div, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Δt ^ 2),
        abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    have e5 : |Δt ^ 2 * mu / 6| = Δt ^ 2 * |mu| / 6 := by
      rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Δt ^ 2),
        abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    have e6 : |Δt ^ 2 * nu / 6| = Δt ^ 2 * |nu| / 6 := by
      rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Δt ^ 2),
        abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    rw [e4, e5, e6]
    linarith [e1, e2, e3]
  calc |residual (Stencil.threePoint cm c0 cp) Δt Δx v x t|
      ≤ |(Δt * (mu ^ 2 - a * nu) / 2 + Δt ^ 2 * a ^ 2 * mu / 6) * D 4 0 x t
          + (Δt * mu * nu / 2 + Δt ^ 2 * a ^ 2 * nu / 6) * D 5 0 x t
          + (Δt * nu / 2 - Δt ^ 2 * a * mu / 6) * D 3 1 x t
          + -(Δt ^ 2 * a * nu / 6) * D 4 1 x t
          + Δt ^ 2 * mu / 6 * D 2 2 x t
          + Δt ^ 2 * nu / 6 * D 3 2 x t|
        + |residual (Stencil.threePoint cm c0 cp) Δt Δx v x t
          - (D 0 1 x t + Δt / 2 * D 0 2 x t + Δt ^ 2 / 6 * D 0 3 x t
            - ((cm + c0 + cp - 1) * v x t + Δx * (cp - cm) * D 1 0 x t
              + Δx ^ 2 / 2 * (cp + cm) * D 2 0 x t
              + Δx ^ 3 / 6 * (cp - cm) * D 3 0 x t) / Δt)| := by
        conv_lhs => rw [hkey]
        exact abs_add_le _ _
    _ ≤ (Δt * (mu ^ 2 + |a| * |nu| + |mu| * |nu| + |nu|) / 2
          + Δt ^ 2 * (a ^ 2 + |a| + 1) * (|mu| + |nu|) / 6) * M
        + M * (Δt ^ 3 / 24 + (|cm| + |cp|) * Δx ^ 4 / (24 * Δt)) :=
        add_le_add (hT.trans (mul_le_mul_of_nonneg_right hcoef hM0)) hexp
    _ = M * (Δt * (mu ^ 2 + |a| * |nu| + |mu| * |nu| + |nu|) / 2
          + Δt ^ 2 * (a ^ 2 + |a| + 1) * (|mu| + |nu|) / 6
          + Δt ^ 3 / 24 + (|cm| + |cp|) * Δx ^ 4 / (24 * Δt)) := by ring

/-- **The third-order equivalent equation of the upwind scheme** ([quarteroni2000numerical]
(13.60) and Table 13.2, upwind row): for `a > 0`, `μ = a Δx/2 - a² Δt/2` and the Warming–Hyett
`ν = -(a/6)(Δx² - 3 a Δx Δt + 2 a² Δt²)`, a solution of `v_t + a v_x = μ v_xx + ν v_xxx` leaves
the upwind scheme a residual made of terms carrying `μ²`, `μν`, `ν`, `Δt μ` or `Δt ν`. With
`λ = Δt/Δx` fixed this is `O(Δx³)`, one order better than (13.59).

Erratum: the text after (13.60) gives `ν = (a/6)(a² Δt² - Δx²)`, which disagrees with Table 13.2;
the table's value, used here, is the correct one — the text omits the `-2 a μ ∂_xxx` contribution
when it substitutes `v_tt`. -/
theorem abs_residual_upwind_le_of_isModifiedSolution_third (hD : HasPartialDerivs v D)
    {a mu nu Δt Δx lam : ℝ} (ha : 0 < a) (hΔt : 0 < Δt) (hΔx : 0 < Δx) (hlam : lam = Δt / Δx)
    (hmu : mu = a * Δx / 2 - a ^ 2 * Δt / 2)
    (hnu : nu = -(a / 6) * (Δx ^ 2 - 3 * a * Δx * Δt + 2 * a ^ 2 * Δt ^ 2))
    (hv : IsModifiedSolution a mu nu v) (hM : ∀ i j, i + j ≤ 5 → ∀ y s, |D i j y s| ≤ M)
    (x t : ℝ) :
    |residual (upwind a lam) Δt Δx v x t|
      ≤ M * (Δt * (mu ^ 2 + |a| * |nu| + |mu| * |nu| + |nu|) / 2
          + Δt ^ 2 * (a ^ 2 + |a| + 1) * (|mu| + |nu|) / 6
          + Δt ^ 3 / 24 + lam * a * Δx ^ 4 / (24 * Δt)) := by
  have hΔx' : Δx ≠ 0 := ne_of_gt hΔx
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 0 (by omega) 0 0)
  rw [upwind_eq_of_pos ha]
  refine (abs_residual_threePoint_le_of_isModifiedSolution hD hΔt hΔx hlam (by ring) (by ring)
    ?_ ?_ hv hM x t).trans ?_
  · rw [hmu, hlam]
    field_simp
    ring
  · rw [hnu, hmu]
    ring
  · have hcc : |lam * a| + |(0 : ℝ)| = lam * a := by
      rw [abs_of_pos (by positivity), abs_zero, add_zero]
    rw [hcc]

/-- **The third-order equivalent equation of the Lax–Friedrichs scheme**
([quarteroni2000numerical] Table 13.2 and Exercise 13.8): with `λ = Δt/Δx`,
`μ = (Δx²/(2Δt))(1 - (aλ)²)` and `ν = (a Δx²/3)(1 - (aλ)²)`, a solution of the equivalent equation
leaves the scheme a residual of the same shape, `O(Δx³)` at fixed `λ`. Here `μ = O(Δx²/Δt)`, which
is why Lax–Friedrichs is only consistent when `Δx²/Δt → 0`. -/
theorem abs_residual_laxFriedrichs_le_of_isModifiedSolution (hD : HasPartialDerivs v D)
    {a mu nu Δt Δx lam : ℝ} (hΔt : 0 < Δt) (hΔx : 0 < Δx) (hlam : lam = Δt / Δx)
    (hmu : mu = Δx ^ 2 / (2 * Δt) * (1 - (a * lam) ^ 2))
    (hnu : nu = a * Δx ^ 2 / 3 * (1 - (a * lam) ^ 2))
    (hv : IsModifiedSolution a mu nu v) (hM : ∀ i j, i + j ≤ 5 → ∀ y s, |D i j y s| ≤ M)
    (x t : ℝ) :
    |residual (laxFriedrichs a lam) Δt Δx v x t|
      ≤ M * (Δt * (mu ^ 2 + |a| * |nu| + |mu| * |nu| + |nu|) / 2
          + Δt ^ 2 * (a ^ 2 + |a| + 1) * (|mu| + |nu|) / 6
          + Δt ^ 3 / 24 + (1 + |lam * a|) * Δx ^ 4 / (24 * Δt)) := by
  have hΔt' : Δt ≠ 0 := ne_of_gt hΔt
  have hΔx' : Δx ≠ 0 := ne_of_gt hΔx
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 0 (by omega) 0 0)
  rw [laxFriedrichs]
  refine (abs_residual_threePoint_le_of_isModifiedSolution hD hΔt hΔx hlam (by ring) (by ring)
    ?_ ?_ hv hM x t).trans ?_
  · rw [hmu, hlam]
    field_simp
    ring
  · rw [hnu, hmu, hlam]
    field_simp
    ring
  · have hcc : |(1 + lam * a) / 2| + |(1 - lam * a) / 2| ≤ 1 + |lam * a| := by
      have h1 : |(1 + lam * a) / 2| ≤ (1 + |lam * a|) / 2 := by
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        gcongr
        exact (abs_add_le _ _).trans (by rw [abs_one])
      have h2 : |(1 - lam * a) / 2| ≤ (1 + |lam * a|) / 2 := by
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        gcongr
        exact (abs_sub _ _).trans (by rw [abs_one])
      linarith
    gcongr

/-- **The third-order equivalent equation of the Lax–Wendroff scheme**
([quarteroni2000numerical] Table 13.2 and Exercise 13.8): with `λ = Δt/Δx`, `μ = 0` — the scheme
is second order accurate, so it has no dissipative term — and `ν = (a Δx²/6)((aλ)² - 1)`, a
solution of the equivalent equation leaves the scheme a residual `O(Δx³)` at fixed `λ`. -/
theorem abs_residual_laxWendroff_le_of_isModifiedSolution (hD : HasPartialDerivs v D)
    {a nu Δt Δx lam : ℝ} (hΔt : 0 < Δt) (hΔx : 0 < Δx) (hlam : lam = Δt / Δx)
    (hnu : nu = a * Δx ^ 2 / 6 * ((a * lam) ^ 2 - 1))
    (hv : IsModifiedSolution a 0 nu v) (hM : ∀ i j, i + j ≤ 5 → ∀ y s, |D i j y s| ≤ M)
    (x t : ℝ) :
    |residual (laxWendroff a lam) Δt Δx v x t|
      ≤ M * (Δt * (|a| * |nu| + |nu|) / 2
          + Δt ^ 2 * (a ^ 2 + |a| + 1) * |nu| / 6
          + Δt ^ 3 / 24 + |lam * a| * (1 + |lam * a|) * Δx ^ 4 / (24 * Δt)) := by
  have hΔt' : Δt ≠ 0 := ne_of_gt hΔt
  have hΔx' : Δx ≠ 0 := ne_of_gt hΔx
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 0 (by omega) 0 0)
  rw [laxWendroff]
  refine (abs_residual_threePoint_le_of_isModifiedSolution hD hΔt hΔx hlam (by ring) (by ring)
    ?_ ?_ hv hM x t).trans ?_
  · rw [hlam]
    field_simp
    ring
  · rw [hnu, hlam]
    field_simp
    ring
  · have hb : |1 + lam * a| ≤ 1 + |lam * a| := by
      have h := abs_add_le (1 : ℝ) (lam * a)
      rw [abs_one] at h
      exact h
    have hb2 : |lam * a - 1| ≤ 1 + |lam * a| := by
      have h := abs_sub (lam * a) (1 : ℝ)
      rw [abs_one] at h
      linarith
    have hcc : |lam * a / 2 * (1 + lam * a)| + |lam * a / 2 * (lam * a - 1)|
        ≤ |lam * a| * (1 + |lam * a|) := by
      have h1 : |lam * a / 2 * (1 + lam * a)| ≤ |lam * a| / 2 * (1 + |lam * a|) := by
        rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        exact mul_le_mul_of_nonneg_left hb (by positivity)
      have h2 : |lam * a / 2 * (lam * a - 1)| ≤ |lam * a| / 2 * (1 + |lam * a|) := by
        rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        exact mul_le_mul_of_nonneg_left hb2 (by positivity)
      linarith
    simp only [abs_zero]
    refine mul_le_mul_of_nonneg_left ?_ hM0
    have hfac : (|lam * a / 2 * (1 + lam * a)| + |lam * a / 2 * (lam * a - 1)|) * Δx ^ 4
        / (24 * Δt) ≤ |lam * a| * (1 + |lam * a|) * Δx ^ 4 / (24 * Δt) := by
      gcongr
    linarith [hfac]

end PartialTaylor

/-! ### The energy of the second-order schemes for the wave equation

[quarteroni2000numerical] Remark 13.4 asserts that the leap-frog scheme (13.44) is stable under
the CFL restriction and that the Newmark scheme (13.45) is unconditionally stable for
`2β ≥ θ ≥ 1/2`. Neither claim is about the Euclidean norm of the state `(u^{n+1}, uⁿ)`: on the
constant mode the leap-frog amplification matrix is `!![2, -1; 1, 0] = I + N`, a Jordan block whose
powers grow linearly for *every* CFL number, and the `(u, Δt v)` state of Newmark has the Jordan
block `!![1, 1; 0, 1]` there. What both schemes control is the **energy** of the wave equation,
`‖u_t‖² + γ²‖u_x‖²`, and that is what is proved here.

Both are stated for an abstract symmetric positive semidefinite `A : E →ₗ[ℝ] E` on a real inner
product space, standing for the discretized `-γ² ∂ₓ²`: `IsLeapFrogOp A Δt u` is
`u^{n+2} - 2u^{n+1} + uⁿ = -Δt² A u^{n+1}` and `IsNewmarkOp A Δt β θ u v` is the Newmark pair.
`leapFrogEnergy` is conserved exactly (`leapFrogEnergy_succ`) and is equivalent to
`‖u^{n+1} - uⁿ‖² + Δt² ⟪A uⁿ, uⁿ⟫` with constants `1 ± κ` whenever `Δt² λmax ≤ 4κ²`
(`abs_leapFrogEnergy_sub_le`), whence the stability bound `leapFrog_stability`; for the discrete
Laplacian `λmax = 4γ²/Δx²` and `κ = |γ| Δt/Δx`, so the hypothesis is exactly the strict CFL
condition. `newmarkEnergy` is nonincreasing for `2β ≥ θ ≥ 1/2` with no restriction on `Δt`
(`newmarkEnergy_succ_le`), whence `newmark_stability`.

The concrete operator on `ℓ²(ℤ)` is `discreteWaveOp γ Δx = -(γ²/Δx²) δ²`, built from the second
difference `secondDiffCLM`; summation by parts (`inner_forwardDiffCLM`) turns its quadratic form
into `(γ²/Δx²)‖∇_h u‖²`, which is what makes it positive semidefinite and bounded by `4γ²/Δx²`.
-/

section SecondOrderEnergy

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {A : E →ₗ[ℝ] E} {lmax Δt β θ : ℝ} {u v : ℕ → E}

/-- **Cauchy–Schwarz for a positive semidefinite symmetric operator**, in the scaled form
`2 |t| |⟪A x, y⟫| ≤ t² ⟪A x, x⟫ + ⟪A y, y⟫`: expand `0 ≤ ⟪A (t x ∓ y), t x ∓ y⟫`. (A general fact
about `LinearMap.IsSymmetricBoundedBy A 0 lmax` over `ℝ`; it is kept here because this file is its
only consumer.) -/
theorem two_mul_abs_inner_le (hA : A.IsSymmetricBoundedBy 0 lmax) (t : ℝ) (x y : E) :
    2 * |t| * |⟪A x, y⟫| ≤ t ^ 2 * ⟪A x, x⟫ + ⟪A y, y⟫ := by
  have hpos : ∀ z : E, 0 ≤ ⟪A z, z⟫ := by
    intro z
    have h := hA.le_re_inner z
    simpa using h
  have hsymm : ∀ p q : E, ⟪A p, q⟫ = ⟪A q, p⟫ := by
    intro p q
    rw [hA.isSymmetric p q, real_inner_comm]
  have expand : ∀ s : ℝ, ⟪A (s • x - y), s • x - y⟫
      = s ^ 2 * ⟪A x, x⟫ - 2 * s * ⟪A x, y⟫ + ⟪A y, y⟫ := by
    intro s
    simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right]
    rw [hsymm y x]
    ring
  have h1 := hpos (t • x - y)
  have h2 := hpos ((-t) • x - y)
  rw [expand] at h1
  rw [expand] at h2
  have hkey : |2 * t * ⟪A x, y⟫| ≤ t ^ 2 * ⟪A x, x⟫ + ⟪A y, y⟫ := by
    rw [abs_le]
    constructor <;> nlinarith [h1, h2]
  calc 2 * |t| * |⟪A x, y⟫| = |2 * t * ⟪A x, y⟫| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ _ := hkey

/-! #### Leap-frog -/

/-- **The leap-frog scheme for the abstract wave equation** `u'' + A u = 0`:
`u^{n+2} - 2 u^{n+1} + uⁿ = -Δt² A u^{n+1}`. It is the operator form of
[quarteroni2000numerical] (13.44), which is the case `A = -γ² δ²/Δx²`. -/
def IsLeapFrogOp (A : E →ₗ[ℝ] E) (Δt : ℝ) (u : ℕ → E) : Prop :=
  ∀ n, u (n + 2) - (2 : ℝ) • u (n + 1) + u n = (-(Δt ^ 2)) • A (u (n + 1))

/-- **The discrete energy of the leap-frog scheme**,
`Eⁿ = ‖u^{n+1} - uⁿ‖² + Δt² ⟪A u^{n+1}, uⁿ⟫`. Divided by `Δt²` it is the discretization
`‖u_t‖² + ⟪A u, u⟫` of the energy of the wave equation, with the potential term evaluated at two
consecutive levels. -/
noncomputable def leapFrogEnergy (A : E →ₗ[ℝ] E) (Δt : ℝ) (u : ℕ → E) (n : ℕ) : ℝ :=
  ‖u (n + 1) - u n‖ ^ 2 + Δt ^ 2 * ⟪A (u (n + 1)), u n⟫

/-- **The leap-frog scheme conserves its energy exactly**, for symmetric `A` and every `Δt`. -/
theorem leapFrogEnergy_succ (hA : A.IsSymmetric) (h : IsLeapFrogOp A Δt u) (n : ℕ) :
    leapFrogEnergy A Δt u (n + 1) = leapFrogEnergy A Δt u n := by
  have hsymm : ∀ p q : E, ⟪A p, q⟫ = ⟪A q, p⟫ := fun p q => by
    rw [hA p q, real_inner_comm]
  have hstep : u (n + 2) - (2 : ℝ) • u (n + 1) + u n = (-(Δt ^ 2)) • A (u (n + 1)) := h n
  have hdiff : ‖u (n + 2) - u (n + 1)‖ ^ 2 - ‖u (n + 1) - u n‖ ^ 2
      = ⟪u (n + 2) - u n, u (n + 2) - (2 : ℝ) • u (n + 1) + u n⟫ := by
    simp only [inner_sub_left, inner_add_right, inner_sub_right, real_inner_smul_right,
      @norm_sub_sq_real]
    have e1 : ⟪u n, u (n + 2)⟫ = ⟪u (n + 2), u n⟫ := real_inner_comm _ _
    have e2 : ⟪u (n + 1), u n⟫ = ⟪u n, u (n + 1)⟫ := real_inner_comm _ _
    have e3 : ⟪u (n + 2), u (n + 2)⟫ = ‖u (n + 2)‖ ^ 2 := real_inner_self_eq_norm_sq _
    have e4 : ⟪u n, u n⟫ = ‖u n‖ ^ 2 := real_inner_self_eq_norm_sq _
    have e5 : ⟪u (n + 1), u (n + 2)⟫ = ⟪u (n + 2), u (n + 1)⟫ := real_inner_comm _ _
    linarith
  have hcross : ⟪u (n + 2) - u n, u (n + 2) - (2 : ℝ) • u (n + 1) + u n⟫
      = -(Δt ^ 2 * (⟪A (u (n + 1)), u (n + 2)⟫ - ⟪A (u (n + 1)), u n⟫)) := by
    rw [hstep, real_inner_smul_right, inner_sub_left, real_inner_comm (u (n + 2)),
      real_inner_comm (u n)]
    ring
  have hlast : ⟪A (u (n + 2)), u (n + 1)⟫ = ⟪A (u (n + 1)), u (n + 2)⟫ :=
    hsymm (u (n + 2)) (u (n + 1))
  change ‖u (n + 2) - u (n + 1)‖ ^ 2 + Δt ^ 2 * ⟪A (u (n + 2)), u (n + 1)⟫
    = ‖u (n + 1) - u n‖ ^ 2 + Δt ^ 2 * ⟪A (u (n + 1)), u n⟫
  rw [hcross] at hdiff
  rw [hlast]
  linarith

/-- The leap-frog energy of every level equals that of the initial pair. -/
theorem leapFrogEnergy_eq_zero (hA : A.IsSymmetric) (h : IsLeapFrogOp A Δt u) (n : ℕ) :
    leapFrogEnergy A Δt u n = leapFrogEnergy A Δt u 0 := by
  induction n with
  | zero => rfl
  | succ k ih => rw [leapFrogEnergy_succ hA h k, ih]

/-- **The leap-frog energy is equivalent to the norm of the state `(u^{n+1} - uⁿ, uⁿ)` measured in
velocity and potential energy**, with constants `1 ± κ`, whenever `Δt² λmax ≤ 4 κ²`. This is where
the CFL condition enters, and it is uniform over all modes, the constant one included. -/
theorem abs_leapFrogEnergy_sub_le (hA : A.IsSymmetricBoundedBy 0 lmax) {kap : ℝ} (hkap : 0 < kap)
    (hCFL : Δt ^ 2 * lmax ≤ 4 * kap ^ 2) (u : ℕ → E) (n : ℕ) :
    |leapFrogEnergy A Δt u n - (‖u (n + 1) - u n‖ ^ 2 + Δt ^ 2 * ⟪A (u n), u n⟫)|
      ≤ kap * (‖u (n + 1) - u n‖ ^ 2 + Δt ^ 2 * ⟪A (u n), u n⟫) := by
  set D := u (n + 1) - u n with hD
  have hexp : leapFrogEnergy A Δt u n - (‖D‖ ^ 2 + Δt ^ 2 * ⟪A (u n), u n⟫)
      = Δt ^ 2 * ⟪A D, u n⟫ := by
    have hsplit : A (u (n + 1)) = A D + A (u n) := by rw [hD, map_sub]; abel
    rw [leapFrogEnergy, hsplit, inner_add_left]
    ring
  have hcs := two_mul_abs_inner_le hA (1 / (2 * kap)) D (u n)
  have hbd : ⟪A D, D⟫ ≤ lmax * ‖D‖ ^ 2 := by simpa using hA.re_inner_le D
  have hsq : (0 : ℝ) ≤ ‖D‖ ^ 2 := sq_nonneg _
  have hDt : (0 : ℝ) ≤ Δt ^ 2 := sq_nonneg _
  have habs : (0 : ℝ) < 1 / (2 * kap) := by positivity
  rw [abs_of_pos habs] at hcs
  have hkey : Δt ^ 2 * |⟪A D, u n⟫| ≤ kap * (‖D‖ ^ 2 + Δt ^ 2 * ⟪A (u n), u n⟫) := by
    have h1 : |⟪A D, u n⟫| ≤ 1 / (4 * kap) * ⟪A D, D⟫ + kap * ⟪A (u n), u n⟫ := by
      have h2 : 2 * (1 / (2 * kap)) = 1 / kap := by field_simp
      rw [h2] at hcs
      have h3 : 1 / kap * |⟪A D, u n⟫| ≤ (1 / (2 * kap)) ^ 2 * ⟪A D, D⟫ + ⟪A (u n), u n⟫ := hcs
      have h4 : (1 / (2 * kap)) ^ 2 = 1 / (4 * kap ^ 2) := by field_simp; ring
      rw [h4] at h3
      have h5 := mul_le_mul_of_nonneg_left h3 hkap.le
      calc |⟪A D, u n⟫| = kap * (1 / kap * |⟪A D, u n⟫|) := by field_simp
        _ ≤ kap * (1 / (4 * kap ^ 2) * ⟪A D, D⟫ + ⟪A (u n), u n⟫) := h5
        _ = 1 / (4 * kap) * ⟪A D, D⟫ + kap * ⟪A (u n), u n⟫ := by field_simp
    have h5 : Δt ^ 2 * (1 / (4 * kap) * ⟪A D, D⟫) ≤ kap * ‖D‖ ^ 2 := by
      have h6 : Δt ^ 2 * ⟪A D, D⟫ ≤ Δt ^ 2 * (lmax * ‖D‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hbd hDt
      have h7 : Δt ^ 2 * (lmax * ‖D‖ ^ 2) ≤ 4 * kap ^ 2 * ‖D‖ ^ 2 := by nlinarith
      have h8 : Δt ^ 2 * (1 / (4 * kap) * ⟪A D, D⟫) = 1 / (4 * kap) * (Δt ^ 2 * ⟪A D, D⟫) := by
        ring
      have h9 : (0 : ℝ) < 1 / (4 * kap) := by positivity
      rw [h8]
      calc 1 / (4 * kap) * (Δt ^ 2 * ⟪A D, D⟫)
          ≤ 1 / (4 * kap) * (4 * kap ^ 2 * ‖D‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (h6.trans h7) h9.le
        _ = kap * ‖D‖ ^ 2 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h1 hDt]
  rw [hexp, abs_mul, abs_of_nonneg hDt]
  exact hkey

/-- **Energy stability of the leap-frog scheme**: under the strict CFL condition `Δt² λmax ≤ 4 κ²`
with `κ < 1`, the discrete energy `‖u^{n+1} - uⁿ‖² + Δt² ⟪A uⁿ, uⁿ⟫` stays bounded by
`(1 + κ)/(1 - κ)` times its initial value, for *all* `n` — no horizon is needed. -/
theorem leapFrog_stability (hA : A.IsSymmetricBoundedBy 0 lmax) {kap : ℝ} (hkap : 0 < kap)
    (hkap1 : kap < 1) (hCFL : Δt ^ 2 * lmax ≤ 4 * kap ^ 2) (h : IsLeapFrogOp A Δt u) (n : ℕ) :
    ‖u (n + 1) - u n‖ ^ 2 + Δt ^ 2 * ⟪A (u n), u n⟫
      ≤ (1 + kap) / (1 - kap) * (‖u 1 - u 0‖ ^ 2 + Δt ^ 2 * ⟪A (u 0), u 0⟫) := by
  have hn := abs_leapFrogEnergy_sub_le hA hkap hCFL u n
  have h0 := abs_leapFrogEnergy_sub_le hA hkap hCFL u 0
  have hE := leapFrogEnergy_eq_zero hA.isSymmetric h n
  rw [abs_le] at hn h0
  have hpos : (0 : ℝ) ≤ ‖u (0 + 1) - u 0‖ ^ 2 + Δt ^ 2 * ⟪A (u 0), u 0⟫ := by
    have hq := hA.le_re_inner (u 0)
    simp only [zero_mul, RCLike.re_to_real] at hq
    positivity
  have h1 : (0 : ℝ) < 1 - kap := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ h1]
  have e1 : u (0 + 1) = u 1 := rfl
  rw [e1] at h0 hpos
  nlinarith [hn.1, hn.2, h0.1, h0.2, hE, hpos]

/-! #### Newmark -/

/-- **The Newmark scheme for the abstract wave equation** `u'' + A u = 0` with the parameters `β`
and `θ` and the auxiliary velocity `v`. It is the operator form of [quarteroni2000numerical]
(13.45), which is the case `A = -γ² δ²/Δx²`. -/
def IsNewmarkOp (A : E →ₗ[ℝ] E) (Δt β θ : ℝ) (u v : ℕ → E) : Prop :=
  ∀ n, u (n + 1) - u n
        = Δt • v n - (Δt ^ 2) • (β • A (u (n + 1)) + (1 / 2 - β) • A (u n)) ∧
      v (n + 1) - v n = (-Δt) • (θ • A (u (n + 1)) + (1 - θ) • A (u n))

/-- **The discrete energy of the Newmark scheme**,
`Eⁿ = ‖vⁿ‖² + ⟪A uⁿ, uⁿ⟫ + (Δt²(2β - θ)/2) ‖A uⁿ‖²`: the kinetic and potential energies plus the
term the parameters of the method add. For `2β = θ = 1/2` it is exactly `‖v‖² + ⟪A u, u⟫`. -/
noncomputable def newmarkEnergy (A : E →ₗ[ℝ] E) (Δt β θ : ℝ) (u v : ℕ → E) (n : ℕ) : ℝ :=
  ‖v n‖ ^ 2 + ⟪A (u n), u n⟫ + Δt ^ 2 * (2 * β - θ) / 2 * ‖A (u n)‖ ^ 2

/-- **The energy identity of the Newmark scheme**: the energy decreases by exactly
`(2θ - 1) ⟪A D, D⟫ + Δt²(2β - θ)(θ - 1/2) ‖A D‖²` over one step, where `D = u^{n+1} - uⁿ`. Only
symmetry of `A` is used; no hypothesis on `Δt`, `β` or `θ`. -/
theorem newmarkEnergy_succ_sub (hA : A.IsSymmetric) (h : IsNewmarkOp A Δt β θ u v) (n : ℕ) :
    newmarkEnergy A Δt β θ u v (n + 1) - newmarkEnergy A Δt β θ u v n
      = -(2 * θ - 1) * ⟪A (u (n + 1) - u n), u (n + 1) - u n⟫
        - Δt ^ 2 * (2 * β - θ) * (θ - 1 / 2) * ‖A (u (n + 1) - u n)‖ ^ 2 := by
  obtain ⟨h1, h2⟩ := h n
  have hAD : A (u (n + 1) - u n) = A (u (n + 1)) - A (u n) := map_sub _ _ _
  have hw : θ • A (u (n + 1)) + (1 - θ) • A (u n) = A (θ • u (n + 1) + (1 - θ) • u n) := by
    simp [map_add, map_smul]
  have e2 : Δt • v n = (u (n + 1) - u n)
      + (Δt ^ 2) • (β • A (u (n + 1)) + (1 / 2 - β) • A (u n)) := by
    rw [h1]; abel
  have hsum : Δt • (v (n + 1) + v n) = (2 : ℝ) • (u (n + 1) - u n)
      + (Δt ^ 2 * (2 * β - θ)) • (A (u (n + 1)) - A (u n)) := by
    have e : v (n + 1) + v n = (v (n + 1) - v n) + (v n + v n) := by abel
    rw [e, smul_add, smul_add, h2, e2, smul_smul]
    module
  have hvel : ‖v (n + 1)‖ ^ 2 - ‖v n‖ ^ 2 = ⟪v (n + 1) - v n, v (n + 1) + v n⟫ := by
    simp only [inner_sub_left, inner_add_right]
    have f1 : ⟪v (n + 1), v (n + 1)⟫ = ‖v (n + 1)‖ ^ 2 := real_inner_self_eq_norm_sq _
    have f2 : ⟪v n, v n⟫ = ‖v n‖ ^ 2 := real_inner_self_eq_norm_sq _
    have f3 : ⟪v n, v (n + 1)⟫ = ⟪v (n + 1), v n⟫ := real_inner_comm _ _
    linarith
  have hA1 : ⟪A (θ • u (n + 1) + (1 - θ) • u n), Δt • (v (n + 1) + v n)⟫
      = 2 * ⟪A (θ • u (n + 1) + (1 - θ) • u n), u (n + 1) - u n⟫
        + Δt ^ 2 * (2 * β - θ)
          * ⟪A (θ • u (n + 1) + (1 - θ) • u n), A (u (n + 1)) - A (u n)⟫ := by
    rw [hsum, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  rw [real_inner_smul_right] at hA1
  have hkey : ‖v (n + 1)‖ ^ 2 - ‖v n‖ ^ 2
      = -(2 * ⟪A (θ • u (n + 1) + (1 - θ) • u n), u (n + 1) - u n⟫)
        - Δt ^ 2 * (2 * β - θ)
          * ⟪A (θ • u (n + 1) + (1 - θ) • u n), A (u (n + 1)) - A (u n)⟫ := by
    rw [hvel, h2, hw, real_inner_smul_left]
    linear_combination -hA1
  have hsq : ⟪A (u (n + 1)), u n⟫ = ⟪A (u n), u (n + 1)⟫ := by
    rw [hA (u (n + 1)) (u n), real_inner_comm]
  have hpq : ⟪A (u (n + 1)), A (u n)⟫ = ⟪A (u n), A (u (n + 1))⟫ := real_inner_comm _ _
  have e1 : ⟪A (θ • u (n + 1) + (1 - θ) • u n), u (n + 1) - u n⟫
      = θ * ⟪A (u (n + 1)), u (n + 1)⟫ - (2 * θ - 1) * ⟪A (u n), u (n + 1)⟫
        - (1 - θ) * ⟪A (u n), u n⟫ := by
    simp only [map_add, map_smul, inner_add_left, inner_sub_right, real_inner_smul_left]
    rw [hsq]
    ring
  have e5 : ⟪A (θ • u (n + 1) + (1 - θ) • u n), A (u (n + 1)) - A (u n)⟫
      = θ * ⟪A (u (n + 1)), A (u (n + 1))⟫ - (2 * θ - 1) * ⟪A (u n), A (u (n + 1))⟫
        - (1 - θ) * ⟪A (u n), A (u n)⟫ := by
    simp only [map_add, map_smul, inner_add_left, inner_sub_right, real_inner_smul_left]
    rw [hpq]
    ring
  have e3 : ⟪A (u (n + 1) - u n), u (n + 1) - u n⟫
      = ⟪A (u (n + 1)), u (n + 1)⟫ - 2 * ⟪A (u n), u (n + 1)⟫ + ⟪A (u n), u n⟫ := by
    rw [hAD, inner_sub_left, inner_sub_right, inner_sub_right, hsq]
    ring
  have e4 : ‖A (u (n + 1) - u n)‖ ^ 2 = ⟪A (u (n + 1)), A (u (n + 1))⟫
      - 2 * ⟪A (u n), A (u (n + 1))⟫ + ⟪A (u n), A (u n)⟫ := by
    rw [← real_inner_self_eq_norm_sq, hAD, inner_sub_left, inner_sub_right, inner_sub_right, hpq]
    ring
  have hnq : ‖A (u (n + 1))‖ ^ 2 = ⟪A (u (n + 1)), A (u (n + 1))⟫ :=
    (real_inner_self_eq_norm_sq _).symm
  have hnp : ‖A (u n)‖ ^ 2 = ⟪A (u n), A (u n)⟫ := (real_inner_self_eq_norm_sq _).symm
  rw [e1, e5] at hkey
  simp only [newmarkEnergy]
  rw [e3, e4, hnq, hnp]
  linear_combination hkey

/-- **The Newmark energy is nonincreasing when `2β ≥ θ ≥ 1/2`**, for every `Δt`: this is the
unconditional stability of [quarteroni2000numerical] Remark 13.4. -/
theorem newmarkEnergy_succ_le (hA : A.IsSymmetricBoundedBy 0 lmax) (hth : 1 / 2 ≤ θ)
    (hbt : θ ≤ 2 * β) (h : IsNewmarkOp A Δt β θ u v) (n : ℕ) :
    newmarkEnergy A Δt β θ u v (n + 1) ≤ newmarkEnergy A Δt β θ u v n := by
  have hid := newmarkEnergy_succ_sub hA.isSymmetric h n
  have hpos : 0 ≤ ⟪A (u (n + 1) - u n), u (n + 1) - u n⟫ := by
    simpa using hA.le_re_inner (u (n + 1) - u n)
  have h1 : 0 ≤ (2 * θ - 1) * ⟪A (u (n + 1) - u n), u (n + 1) - u n⟫ :=
    mul_nonneg (by linarith) hpos
  have h2 : 0 ≤ Δt ^ 2 * (2 * β - θ) * (θ - 1 / 2) * ‖A (u (n + 1) - u n)‖ ^ 2 := by
    have hc : (0 : ℝ) ≤ Δt ^ 2 * (2 * β - θ) * (θ - 1 / 2) :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (by linarith)
    positivity
  linarith

/-- The Newmark energy never exceeds its initial value when `2β ≥ θ ≥ 1/2`. -/
theorem newmarkEnergy_le (hA : A.IsSymmetricBoundedBy 0 lmax) (hth : 1 / 2 ≤ θ)
    (hbt : θ ≤ 2 * β) (h : IsNewmarkOp A Δt β θ u v) (n : ℕ) :
    newmarkEnergy A Δt β θ u v n ≤ newmarkEnergy A Δt β θ u v 0 := by
  induction n with
  | zero => exact le_refl _
  | succ k ih => exact (newmarkEnergy_succ_le hA hth hbt h k).trans ih

/-- **Unconditional stability of the Newmark scheme** for `2β ≥ θ ≥ 1/2`: the kinetic plus
potential energy `‖vⁿ‖² + ⟪A uⁿ, uⁿ⟫` never exceeds the initial Newmark energy, for every `Δt`. -/
theorem newmark_stability (hA : A.IsSymmetricBoundedBy 0 lmax) (hth : 1 / 2 ≤ θ)
    (hbt : θ ≤ 2 * β) (h : IsNewmarkOp A Δt β θ u v) (n : ℕ) :
    ‖v n‖ ^ 2 + ⟪A (u n), u n⟫
      ≤ ‖v 0‖ ^ 2 + ⟪A (u 0), u 0⟫ + Δt ^ 2 * (2 * β - θ) / 2 * ‖A (u 0)‖ ^ 2 := by
  have hmono := newmarkEnergy_le hA hth hbt h n
  have hextra : 0 ≤ Δt ^ 2 * (2 * β - θ) / 2 * ‖A (u n)‖ ^ 2 := by
    have hc : (0 : ℝ) ≤ Δt ^ 2 * (2 * β - θ) / 2 :=
      div_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (by norm_num)
    positivity
  simp only [newmarkEnergy] at hmono
  linarith

/-! #### The discrete wave operator on `ℓ²(ℤ)` -/

/-- **The forward difference** `∇_h u j = u_{j+1} - u_j` as a bounded operator on `ℓ²(ℤ)`. -/
noncomputable def forwardDiffCLM : lp (fun _ : ℤ => ℝ) 2 →L[ℝ] lp (fun _ : ℤ => ℝ) 2 :=
  Stencil.lpCLM (Stencil.threePoint 0 (-1) 1) 2

/-- The forward difference acts by `u ↦ (j ↦ u_{j+1} - u_j)`. -/
theorem forwardDiffCLM_apply (u : lp (fun _ : ℤ => ℝ) 2) (j : ℤ) :
    forwardDiffCLM u j = u (j + 1) - u j := by
  rw [forwardDiffCLM, Stencil.lpCLM_apply, Stencil.threePoint_apply]
  simp only [smul_eq_mul, neg_mul, one_mul, zero_mul]
  ring

/-- **The second difference** `δ² u j = u_{j+1} - 2 u_j + u_{j-1}` as a bounded operator on
`ℓ²(ℤ)`; it is the space operator of the leap-frog and Newmark schemes. -/
noncomputable def secondDiffCLM : lp (fun _ : ℤ => ℝ) 2 →L[ℝ] lp (fun _ : ℤ => ℝ) 2 :=
  Stencil.lpCLM (Stencil.threePoint 1 (-2) 1) 2

/-- The second difference acts by `u ↦ (j ↦ u_{j+1} - 2 u_j + u_{j-1})`. -/
theorem secondDiffCLM_apply (u : lp (fun _ : ℤ => ℝ) 2) (j : ℤ) :
    secondDiffCLM u j = u (j + 1) - 2 * u j + u (j - 1) := by
  rw [secondDiffCLM, Stencil.lpCLM_apply, Stencil.threePoint_apply]
  simp only [smul_eq_mul, neg_mul, one_mul]
  ring

/-- The forward difference is the difference of the shift by `-1` and the identity. -/
private theorem forwardDiffCLM_eq_sub (u : lp (fun _ : ℤ => ℝ) 2) :
    forwardDiffCLM u = lp.shiftₗᵢ (E := ℝ) (𝕜 := ℝ) 2 (-1) u - u := by
  refine lp.ext (funext fun j => ?_)
  rw [lp.coeFn_sub]
  simp [forwardDiffCLM_apply, sub_neg_eq_add]

/-- The second difference in terms of the two unit shifts. -/
private theorem secondDiffCLM_eq_sub (u : lp (fun _ : ℤ => ℝ) 2) :
    secondDiffCLM u
      = lp.shiftₗᵢ (E := ℝ) (𝕜 := ℝ) 2 (-1) u - (2 : ℝ) • u
        + lp.shiftₗᵢ (E := ℝ) (𝕜 := ℝ) 2 1 u := by
  refine lp.ext (funext fun j => ?_)
  rw [lp.coeFn_add, lp.coeFn_sub, lp.coeFn_smul]
  simp [secondDiffCLM_apply, sub_neg_eq_add]

/-- **Summation by parts on `ℓ²(ℤ)`**: `⟪∇_h u, ∇_h w⟫ = -⟪δ² u, w⟫`. -/
theorem inner_forwardDiffCLM (u w : lp (fun _ : ℤ => ℝ) 2) :
    ⟪forwardDiffCLM u, forwardDiffCLM w⟫ = -⟪secondDiffCLM u, w⟫ := by
  rw [forwardDiffCLM_eq_sub u, forwardDiffCLM_eq_sub w, secondDiffCLM_eq_sub u]
  rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_add_left, inner_sub_left,
    inner_shift_left, inner_shift_left, inner_shift_left, real_inner_smul_left]
  rw [shift_shift, show (- -1 + -1 : ℤ) = 0 by norm_num, shift_zero]
  ring

/-- **The discrete wave operator** `-γ² δ²/Δx²` on `ℓ²(ℤ)`: the space operator of the wave equation
`u_tt = γ² u_xx` discretized by centred differences ([quarteroni2000numerical] (13.44)–(13.45)). -/
noncomputable def discreteWaveOp (γ Δx : ℝ) :
    lp (fun _ : ℤ => ℝ) 2 →L[ℝ] lp (fun _ : ℤ => ℝ) 2 :=
  (-(γ ^ 2 / Δx ^ 2)) • secondDiffCLM

/-- The discrete wave operator acts by `-γ²/Δx² (u_{j+1} - 2 u_j + u_{j-1})`. -/
theorem discreteWaveOp_apply (γ Δx : ℝ) (u : lp (fun _ : ℤ => ℝ) 2) (j : ℤ) :
    discreteWaveOp γ Δx u j = -(γ ^ 2 / Δx ^ 2) * (u (j + 1) - 2 * u j + u (j - 1)) := by
  have h : discreteWaveOp γ Δx u = (-(γ ^ 2 / Δx ^ 2)) • secondDiffCLM u := rfl
  rw [h, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, secondDiffCLM_apply]

/-- The form of the discrete wave operator is the discrete Dirichlet form
`(γ²/Δx²) ⟪∇_h u, ∇_h w⟫`. -/
theorem inner_discreteWaveOp (γ Δx : ℝ) (u w : lp (fun _ : ℤ => ℝ) 2) :
    ⟪discreteWaveOp γ Δx u, w⟫ = γ ^ 2 / Δx ^ 2 * ⟪forwardDiffCLM u, forwardDiffCLM w⟫ := by
  have h : discreteWaveOp γ Δx u = (-(γ ^ 2 / Δx ^ 2)) • secondDiffCLM u := rfl
  rw [h, real_inner_smul_left, inner_forwardDiffCLM]
  ring

/-- The energy of the discrete wave operator is `(γ²/Δx²) ‖∇_h u‖²`, the discrete `γ² ∫ u_x²`. -/
theorem inner_discreteWaveOp_self (γ Δx : ℝ) (u : lp (fun _ : ℤ => ℝ) 2) :
    ⟪discreteWaveOp γ Δx u, u⟫ = γ ^ 2 / Δx ^ 2 * ‖forwardDiffCLM u‖ ^ 2 := by
  rw [inner_discreteWaveOp, real_inner_self_eq_norm_sq]

/-- The forward difference is bounded by `2` on `ℓ²(ℤ)`. -/
theorem norm_forwardDiffCLM_le (u : lp (fun _ : ℤ => ℝ) 2) :
    ‖forwardDiffCLM u‖ ≤ 2 * ‖u‖ := by
  rw [forwardDiffCLM_eq_sub]
  refine (norm_sub_le _ _).trans ?_
  rw [(lp.shiftₗᵢ (E := ℝ) (𝕜 := ℝ) 2 (-1)).norm_map]
  ring_nf
  exact le_refl _

/-- **The discrete wave operator is symmetric and positive semidefinite with quadratic form
bounded by `4γ²/Δx²`**: the discrete counterpart of `0 ≤ -γ² ∂ₓ² ≤ 4γ²/Δx²`, and the source of the
CFL constant. -/
theorem discreteWaveOp_isSymmetricBoundedBy (γ Δx : ℝ) :
    ((discreteWaveOp γ Δx : lp (fun _ : ℤ => ℝ) 2 →L[ℝ] lp (fun _ : ℤ => ℝ) 2) :
      lp (fun _ : ℤ => ℝ) 2 →ₗ[ℝ] lp (fun _ : ℤ => ℝ) 2).IsSymmetricBoundedBy 0
      (4 * γ ^ 2 / Δx ^ 2) := by
  have hc : (0 : ℝ) ≤ γ ^ 2 / Δx ^ 2 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    change ⟪discreteWaveOp γ Δx x, y⟫ = ⟪x, discreteWaveOp γ Δx y⟫
    have h1 : ⟪x, discreteWaveOp γ Δx y⟫ = ⟪discreteWaveOp γ Δx y, x⟫ := real_inner_comm _ _
    have h2 : ⟪forwardDiffCLM y, forwardDiffCLM x⟫ = ⟪forwardDiffCLM x, forwardDiffCLM y⟫ :=
      real_inner_comm _ _
    rw [h1, inner_discreteWaveOp, inner_discreteWaveOp, h2]
  · intro x
    change 0 * ‖x‖ ^ 2 ≤ RCLike.re (inner ℝ (discreteWaveOp γ Δx x) x)
    simp only [RCLike.re_to_real, zero_mul]
    rw [inner_discreteWaveOp_self]
    positivity
  · intro x
    change RCLike.re (inner ℝ (discreteWaveOp γ Δx x) x) ≤ _
    simp only [RCLike.re_to_real]
    rw [inner_discreteWaveOp_self]
    have h1 : ‖forwardDiffCLM x‖ ^ 2 ≤ (2 * ‖x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_forwardDiffCLM_le x) 2
    calc γ ^ 2 / Δx ^ 2 * ‖forwardDiffCLM x‖ ^ 2
        ≤ γ ^ 2 / Δx ^ 2 * (2 * ‖x‖) ^ 2 := mul_le_mul_of_nonneg_left h1 hc
      _ = 4 * γ ^ 2 / Δx ^ 2 * ‖x‖ ^ 2 := by ring

/-- **The leap-frog scheme (13.44) is the operator scheme of `discreteWaveOp`** when the levels
lie in `ℓ²(ℤ)` and `λ = Δt/Δx`. -/
theorem isLeapFrogOp_of_isLeapFrog {γ lam Δt Δx : ℝ} (hΔx : Δx ≠ 0) (hlam : lam = Δt / Δx)
    {u : ℕ → lp (fun _ : ℤ => ℝ) 2} (h : IsLeapFrog γ lam fun n => ⇑(u n)) :
    IsLeapFrogOp
      ((discreteWaveOp γ Δx : lp (fun _ : ℤ => ℝ) 2 →L[ℝ] lp (fun _ : ℤ => ℝ) 2) :
        lp (fun _ : ℤ => ℝ) 2 →ₗ[ℝ] lp (fun _ : ℤ => ℝ) 2) Δt u := by
  intro n
  refine lp.ext (funext fun j => ?_)
  have hstep := h n j
  simp only [lp.coeFn_add, lp.coeFn_sub, lp.coeFn_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, ContinuousLinearMap.coe_coe, discreteWaveOp_apply]
  rw [hstep, hlam]
  field_simp

/-- **The Newmark scheme (13.45) is the operator scheme of `discreteWaveOp`** when the levels lie
in `ℓ²(ℤ)` and `λ = Δt/Δx`. -/
theorem isNewmarkOp_of_isNewmark {γ lam Δt Δx β θ : ℝ} (hΔt : Δt ≠ 0) (hΔx : Δx ≠ 0)
    (hlam : lam = Δt / Δx) {u v : ℕ → lp (fun _ : ℤ => ℝ) 2}
    (h : IsNewmark γ lam Δt β θ (fun n => ⇑(u n)) fun n => ⇑(v n)) :
    IsNewmarkOp
      ((discreteWaveOp γ Δx : lp (fun _ : ℤ => ℝ) 2 →L[ℝ] lp (fun _ : ℤ => ℝ) 2) :
        lp (fun _ : ℤ => ℝ) 2 →ₗ[ℝ] lp (fun _ : ℤ => ℝ) 2) Δt β θ u v := by
  intro n
  constructor
  · refine lp.ext (funext fun j => ?_)
    have hstep := (h n j).1
    simp only [lp.coeFn_add, lp.coeFn_sub, lp.coeFn_smul, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.coe_coe, discreteWaveOp_apply]
    rw [hstep, hlam]
    field_simp
    ring
  · refine lp.ext (funext fun j => ?_)
    have hstep := (h n j).2
    simp only [lp.coeFn_add, lp.coeFn_sub, lp.coeFn_smul, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.coe_coe, discreteWaveOp_apply]
    rw [hstep, hlam]
    field_simp
    ring

end SecondOrderEnergy

end Hyperbolic

end FiniteDifference

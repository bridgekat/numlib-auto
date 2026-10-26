import Numlib.Optimization.Optimality.Unconstrained
import Numlib.Optimization.Descent
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# Optimality conditions on a convex set

Optimality conditions for minimizing a smooth `f : E → ℝ` over a convex set `C` of a real normed
space ([cartis2022evaluation], Theorem 1.1.2), with the feasible displacements
`C(x) = {d | x + d ∈ C}` of (1.1.7).

## Main results

* `Optimization.IsLocalMinOn.fderiv_apply_nonneg_of_convex`: the first-order condition (1.1.6),
  `∇f(x)[d] ≥ 0` for `d ∈ C(x)`;
* `Optimization.IsLocalMinOn.iteratedFDeriv_two_nonneg_of_convex`: the second-order condition
  (1.1.8);
* `Optimization.IsLocalMinOn.iteratedFDeriv_three_nonneg_of_convex`: the third-order condition
  (1.1.9);
* `Optimization.isStrictLocalMinOn_of_tangentCone`: the (corrected) second-order sufficient
  condition, over directions of the tangent cone;
* `Optimization.not_isLocalMinOn_parabola_counterexample`: the sufficient condition as printed in
  the book is false.

The necessary conditions follow from the ray lemma
`Optimization.iteratedFDeriv_apply_nonneg_of_ray` along the segment `t ↦ x + t d`, `t ∈ [0, 1]`,
which stays in `C` by convexity.

## The sufficient condition

The book's converse of Theorem 1.1.2 assumes (1.1.6) and `∇²f(x)[d]² > 0` for every nonzero
`d ∈ C(x)` with `∇f(x)[d] = 0`. This is false: for `C = {(u, v) | u² ≤ v}`,
`f(u, v) = v - 2u²` and `x = 0`, (1.1.6) holds, no nonzero `d ∈ C(0)` is orthogonal to
`∇f(0) = (0, 1)`, yet `f(u, u²) = -u² < 0` (`not_isLocalMinOn_parabola_counterexample`). Radial
directions do not see the curvature of the boundary. The correct condition quantifies over the
tangent cone `T_C(x) = tangentConeAt ℝ C x` (the closure of the cone of feasible directions); it
needs neither the convexity of `C` nor `x ∈ C`.
-/

open Filter Set Topology

namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If `x` minimizes `f` locally on a convex set `C` and `x + d ∈ C`, then `f x ≤ f (x + t d)` for
all small `t > 0`. -/
theorem IsLocalMinOn.eventually_le_add_smul_of_convex {f : E → ℝ} {C : Set E} {x d : E}
    (hC : Convex ℝ C) (hx : x ∈ C) (hmin : IsLocalMinOn f C x) (hd : x + d ∈ C) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), f x ≤ f (x + t • d) := by
  have ht : Tendsto (fun t : ℝ => x + t • d) (𝓝[>] 0) (𝓝[C] x) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun t : ℝ => x + t • d) (𝓝 0) (𝓝 (x + (0 : ℝ) • d)) :=
        (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
      rw [zero_smul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
      exact hC.add_smul_mem hx hd ⟨ht.1.le, ht.2.le⟩
  exact ht.eventually hmin

/-- **First-order necessary condition on a convex set** ([cartis2022evaluation], (1.1.6)): at a
local minimizer `x` of `f` on a convex set `C` at which `f` is differentiable,
`∇f(x)[d] ≥ 0` for every `d` with `x + d ∈ C`. -/
theorem IsLocalMinOn.fderiv_apply_nonneg_of_convex {f : E → ℝ} {C : Set E} {x d : E}
    (hC : Convex ℝ C) (hx : x ∈ C) (hmin : IsLocalMinOn f C x) (hf : DifferentiableAt ℝ f x)
    (hd : x + d ∈ C) : 0 ≤ fderiv ℝ f x d := by
  have := Descent.fderiv_apply_sub_nonneg_of_isLocalMinOn (f' := fun _ => fderiv ℝ f x) hC hx hmin
    hf.hasFDerivAt (x + d) hd
  simpa using this

/-- **Second-order necessary condition on a convex set** ([cartis2022evaluation], (1.1.8)): at a
local minimizer `x` of `f` on a convex set `C`, `f` `C²` at `x`, `∇²f(x)[d]² ≥ 0` for every `d`
with `x + d ∈ C` and `∇f(x)[d] = 0`. -/
theorem IsLocalMinOn.iteratedFDeriv_two_nonneg_of_convex {f : E → ℝ} {C : Set E} {x d : E}
    (hC : Convex ℝ C) (hx : x ∈ C) (hmin : IsLocalMinOn f C x) (hf : ContDiffAt ℝ 2 f x)
    (hd : x + d ∈ C) (hd1 : fderiv ℝ f x d = 0) : 0 ≤ iteratedFDeriv ℝ 2 f x (fun _ => d) := by
  refine iteratedFDeriv_apply_nonneg_of_ray two_ne_zero hf
    (IsLocalMinOn.eventually_le_add_smul_of_convex hC hx hmin hd) fun i hi hi2 => ?_
  obtain rfl : i = 1 := by omega
  rwa [iteratedFDeriv_one_apply]

/-- **Third-order necessary condition on a convex set** ([cartis2022evaluation], (1.1.9)): at a
local minimizer `x` of `f` on a convex set `C`, `f` `C³` at `x`, `∇³f(x)[d]³ ≥ 0` for every `d`
with `x + d ∈ C`, `∇f(x)[d] = 0` and `∇²f(x)[d]² = 0`. -/
theorem IsLocalMinOn.iteratedFDeriv_three_nonneg_of_convex {f : E → ℝ} {C : Set E} {x d : E}
    (hC : Convex ℝ C) (hx : x ∈ C) (hmin : IsLocalMinOn f C x) (hf : ContDiffAt ℝ 3 f x)
    (hd : x + d ∈ C) (hd1 : fderiv ℝ f x d = 0)
    (hd2 : iteratedFDeriv ℝ 2 f x (fun _ => d) = 0) :
    0 ≤ iteratedFDeriv ℝ 3 f x (fun _ => d) := by
  refine iteratedFDeriv_apply_nonneg_of_ray three_ne_zero hf
    (IsLocalMinOn.eventually_le_add_smul_of_convex hC hx hmin hd) fun i hi hi3 => ?_
  rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl
  · rwa [iteratedFDeriv_one_apply]
  · exact hd2

/-- **Second-order sufficient condition on a set** (corrected converse of [cartis2022evaluation],
Theorem 1.1.2). In finite dimension, let `f` be `C²` at `x`, satisfy the first-order condition
(1.1.6) `∇f(x)[y - x] ≥ 0` for `y ∈ C` near `x`, and `∇²f(x)[d]² > 0` for every nonzero `d` in
the tangent cone of `C` at `x` with `∇f(x)[d] = 0`. Then `x` is a strict local minimizer of `f`
on `C`.

The book quantifies over the radial directions `d ∈ C(x)` instead of the tangent cone; that
version is false (`not_isLocalMinOn_parabola_counterexample`). Convexity of `C` is not needed.
Proof: a violating sequence `y_k → x` in `C` has unit directions converging to some `d` in the
tangent cone; first-order expansions give `∇f(x)[d] = 0`, and the second-order expansion together
with `∇f(x)[y_k - x] ≥ 0` gives `∇²f(x)[d]² ≤ 0`. -/
theorem isStrictLocalMinOn_of_tangentCone [FiniteDimensional ℝ E] {f : E → ℝ} {C : Set E} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hfo : ∀ᶠ y in 𝓝[C] x, 0 ≤ fderiv ℝ f x (y - x))
    (hso : ∀ d ∈ tangentConeAt ℝ C x, d ≠ 0 → fderiv ℝ f x d = 0 →
      0 < iteratedFDeriv ℝ 2 f x (fun _ => d)) :
    IsStrictLocalMinOn f C x := by
  by_contra hcon
  obtain ⟨y, z, hy, hylim, hz, hyz⟩ := exists_seq_of_not_isStrictLocalMinOn hcon
  have hw : Tendsto (fun n => y n - x) atTop (𝓝 0) := by simpa using hylim.sub_const x
  have hr : ∀ᶠ n in atTop, 0 < ‖y n - x‖ :=
    Eventually.of_forall fun n => norm_pos_iff.2 (sub_ne_zero.2 (hy n).2.1)
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hfoN : ∀ᶠ n in atTop, 0 ≤ fderiv ℝ f x (y n - x) :=
    (tendsto_nhdsWithin_iff.2 ⟨hylim, Eventually.of_forall fun n => (hy n).1⟩).eventually hfo
  -- the limit direction is tangent
  have htan : z ∈ tangentConeAt ℝ C x :=
    mem_tangentConeAt_of_seq atTop (fun n => ‖y n - x‖⁻¹) (fun n => y n - x) hw
      (Eventually.of_forall fun n => by simpa using (hy n).1) hyz
  -- first order: `∇f(x)[z] = 0`
  have hfd : HasFDerivAt f (fderiv ℝ f x) x :=
    (hf.differentiableAt (by norm_num)).hasFDerivAt
  have h1 := tendsto_sub_div_of_hasFDerivAt hfd hr hw hyz
  simp only [add_sub_cancel] at h1
  have hle : fderiv ℝ f x z ≤ 0 :=
    le_of_tendsto' h1 fun n => div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 (hy n).2.2)
      (norm_nonneg _)
  have hge : 0 ≤ fderiv ℝ f x z := by
    refine ge_of_tendsto (((fderiv ℝ f x).continuous.tendsto z).comp hyz) ?_
    filter_upwards [hfoN] with n hn
    simp only [Function.comp_apply, map_smul, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.2 (norm_nonneg _)) hn
  have hz1 : fderiv ℝ f x z = 0 := le_antisymm hle hge
  -- second order: `∇²f(x)[z]² ≤ 0`
  have h2 := tendsto_sub_div_sq_of_contDiffAt hf hr hw hyz
  simp only [add_sub_cancel] at h2
  have hle2 : iteratedFDeriv ℝ 2 f x (fun _ => z) / 2 ≤ 0 := by
    refine le_of_tendsto h2 ?_
    filter_upwards [hfoN] with n hn
    refine div_nonpos_of_nonpos_of_nonneg ?_ (sq_nonneg _)
    linarith [(hy n).2.2]
  linarith [hso z htan hz0 hz1]

/-- **The printed converse of Theorem 1.1.2 is false** ([cartis2022evaluation], Theorem 1.1.2).
On `ℝ × ℝ`, `C = {p | p.1² ≤ p.2}` is closed and convex, and `f p = p.2 - 2 p.1²` satisfies at
`x = 0`: (i) the first-order condition (1.1.6); (ii) `∇f(0)[d] > 0` for every nonzero `d ∈ C(0)`,
so the book's radial second-order condition holds vacuously; yet (iii) `0` is not a local
minimizer of `f` on `C`, since `f(t, t²) = -t²`. -/
theorem not_isLocalMinOn_parabola_counterexample :
    Convex ℝ {p : ℝ × ℝ | p.1 ^ 2 ≤ p.2} ∧ IsClosed {p : ℝ × ℝ | p.1 ^ 2 ≤ p.2} ∧
      (∀ y ∈ {p : ℝ × ℝ | p.1 ^ 2 ≤ p.2},
        0 ≤ fderiv ℝ (fun p : ℝ × ℝ => p.2 - 2 * p.1 ^ 2) 0 (y - 0)) ∧
      (∀ d : ℝ × ℝ, d ≠ 0 → 0 + d ∈ {p : ℝ × ℝ | p.1 ^ 2 ≤ p.2} →
        0 < fderiv ℝ (fun p : ℝ × ℝ => p.2 - 2 * p.1 ^ 2) 0 d) ∧
      ¬ IsLocalMinOn (fun p : ℝ × ℝ => p.2 - 2 * p.1 ^ 2) {p : ℝ × ℝ | p.1 ^ 2 ≤ p.2} 0 := by
  set C : Set (ℝ × ℝ) := {p | p.1 ^ 2 ≤ p.2}
  set f : ℝ × ℝ → ℝ := fun p => p.2 - 2 * p.1 ^ 2
  have hfd : fderiv ℝ f 0 = ContinuousLinearMap.snd ℝ ℝ ℝ := by
    have h := (hasFDerivAt_snd (p := (0 : ℝ × ℝ))).sub
      (((hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : ℝ × ℝ))).pow 2).const_mul (2 : ℝ))
    refine h.fderiv.trans ?_
    ext <;> simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := (even_two.convexOn_pow (𝕜 := ℝ)).convex_epigraph
    simpa [C] using this
  · exact isClosed_le (continuous_fst.pow 2) continuous_snd
  · intro y hy
    rw [hfd, sub_zero, ContinuousLinearMap.coe_snd']
    exact (sq_nonneg _).trans hy
  · intro d hd hdC
    rw [zero_add] at hdC
    rw [hfd, ContinuousLinearMap.coe_snd']
    refine lt_of_le_of_ne ((sq_nonneg _).trans hdC) fun h => hd ?_
    have h1 : d.1 = 0 := pow_eq_zero_iff (n := 2) two_ne_zero |>.1
      (le_antisymm (h ▸ hdC) (sq_nonneg _))
    exact Prod.ext h1 h.symm
  · intro hmin
    have ht : Tendsto (fun t : ℝ => ((t, t ^ 2) : ℝ × ℝ)) (𝓝[≠] 0) (𝓝[C] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
        (Eventually.of_forall fun t => by simp [C])
      have : Tendsto (fun t : ℝ => ((t, t ^ 2) : ℝ × ℝ)) (𝓝 0) (𝓝 ((0, 0 ^ 2) : ℝ × ℝ)) :=
        (continuous_id.prodMk (continuous_id.pow 2)).tendsto 0
      rw [show ((0 : ℝ), (0 : ℝ) ^ 2) = (0 : ℝ × ℝ) by simp] at this
      exact this.mono_left nhdsWithin_le_nhds
    obtain ⟨t, htf, ht0⟩ := ((ht.eventually hmin).and self_mem_nhdsWithin).exists
    have ht0' : t ≠ 0 := ht0
    have : 0 < t ^ 2 := lt_of_le_of_ne (sq_nonneg t) (pow_ne_zero 2 ht0').symm
    simp only [f, Prod.fst_zero, Prod.snd_zero] at htf
    nlinarith

end Optimization

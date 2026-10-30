import Numlib.Nonlinear.MonotoneNewton
import NumlibSurface.CartisGouldToint.Chapter08.Section02

/-!
# Cartis–Gould–Toint, Appendix B: Appendix to Chapter 8

Surface file for [cartis2022evaluation], Appendix B, "Appendix to Chapter 8": Lemma B.8.1 (Newton
and secant iterations for convex monotone scalar equations) and Lemma B.8.2 (monotonicity in `β`
of the Newton step for the transformed secular equation). The appendix proofs of Lemma 8.2.1 and
Theorems 8.2.2–8.2.6 are the proofs of those Chapter 8 results.

## Corrections to the source

* Lemma B.8.1 needs `θ'(λ*) ≠ 0`: for `θ(x) = (1 - x)²` on `[0, 1]` and `λ₀ = 0` the Newton
  iterates are `1 - 2⁻ʲ`, only linearly convergent, and `γᴺ = 1`. In the concave (strictly
  increasing) case the starting condition must be `θ(λ₀) < 0` (and `θ(λ₁) < 0` for the secant
  method), as the reduction of the proof to `-θ` shows; the book prints `> 0` for both cases.
  The tangent inequality (B.8.3) is printed reversed; the proof uses `θ(x) ≥ θ'(λ*) (x - λ*)`.
  Iterates that reach `λ*` stay there, so the monotone increase is not strict in general.
  Continuous differentiability on `I` is formalized as a derivative within `I` at each point of
  `I` that is continuous on `I`.
* Lemma B.8.2: the hypothesis that `λ*` is the root of `π(λ) = Δ²` plays no role; `g ≠ 0` is
  needed for the Newton step to be defined.
-/

open Set Filter Topology
open scoped RealInnerProductSpace

namespace CartisGouldToint.AppendixB

open Subproblem CartisGouldToint.Chapter08

/-- **Lemma B.8.1 of [cartis2022evaluation] (Convergence rates of one-dimensional Newton-like
iteration)**, convex case, with the missing hypothesis `θ'(λ*) ≠ 0`. Let `θ` be convex, strictly
decreasing and continuously differentiable on `I = [λ_min, λ_max]` with a root `λ* ∈ I`,
`θ'(λ*) ≠ 0`, and `γᴺ = 1 - θ'(λ*)/θ'(λ₀)`.
(i) If `θ(λ₀) > 0` the Newton iterates (B.8.1) lie in `[λ₀, λ*]`, increase monotonically to `λ*`,
satisfy `λ* - λⱼ₊₁ ≤ γᴺ (λ* - λⱼ)` with `γᴺ < 1`, converge Q-superlinearly, and Q-quadratically
when `θ'` is Lipschitz continuous around `λ*`.
(ii) If `λ₀ < λ₁` in `I` with `θ(λ₀), θ(λ₁) > 0`, the secant iterates (B.8.2) (here
`Secant.iterate θ λ₀ λ₁ j = λⱼ₊₁`) lie in `[λ₀, λ*]`, increase monotonically to `λ*` with the same
factor `γᴺ` and converge Q-superlinearly. -/
theorem lemma_B_8_1 {θ θ' : ℝ → ℝ} {lmin lmax lamStar : ℝ}
    (hc : ConvexOn ℝ (Icc lmin lmax) θ) (hm : StrictAntiOn θ (Icc lmin lmax))
    (hd : ∀ x ∈ Icc lmin lmax, HasDerivWithinAt θ (θ' x) (Icc lmin lmax) x)
    (hd' : ContinuousOn θ' (Icc lmin lmax)) (hstar : lamStar ∈ Icc lmin lmax)
    (hroot : θ lamStar = 0) (hθ' : θ' lamStar ≠ 0) :
    (∀ lam₀ ∈ Icc lmin lmax, 0 < θ lam₀ →
      (∀ k, (Newton.scalarStep θ θ')^[k] lam₀ ∈ Icc lam₀ lamStar) ∧
      Monotone (fun k => (Newton.scalarStep θ θ')^[k] lam₀) ∧
      Tendsto (fun k => (Newton.scalarStep θ θ')^[k] lam₀) atTop (𝓝 lamStar) ∧
      1 - θ' lamStar / θ' lam₀ ∈ Ico 0 1 ∧
      (∀ k, lamStar - (Newton.scalarStep θ θ')^[k + 1] lam₀ ≤
        (1 - θ' lamStar / θ' lam₀) * (lamStar - (Newton.scalarStep θ θ')^[k] lam₀)) ∧
      ConvergesSuperlinearly (fun k => (Newton.scalarStep θ θ')^[k] lam₀) lamStar ∧
      ((∃ K, ∃ U ∈ 𝓝[Icc lmin lmax] lamStar, LipschitzOnWith K θ' U) →
        ConvergesWithOrder (fun k => (Newton.scalarStep θ θ')^[k] lam₀) lamStar 2)) ∧
    (∀ lam₀ ∈ Icc lmin lmax, ∀ lam₁ ∈ Icc lmin lmax, lam₀ < lam₁ → 0 < θ lam₀ → 0 < θ lam₁ →
      (∀ k, Secant.iterate θ lam₀ lam₁ k ∈ Icc lam₀ lamStar) ∧
      Monotone (Secant.iterate θ lam₀ lam₁) ∧
      Tendsto (Secant.iterate θ lam₀ lam₁) atTop (𝓝 lamStar) ∧
      1 - θ' lamStar / θ' lam₀ ∈ Ico 0 1 ∧
      (∀ k, lamStar - Secant.iterate θ lam₀ lam₁ (k + 1) ≤
        (1 - θ' lamStar / θ' lam₀) * (lamStar - Secant.iterate θ lam₀ lam₁ k)) ∧
      ConvergesSuperlinearly (Secant.iterate θ lam₀ lam₁) lamStar) := by
  have h : Newton.IsConvexAntiRoot θ θ' (Icc lmin lmax) lamStar :=
    ⟨hc, hm, hd, hstar, hroot, hθ'⟩
  have hcont : ContinuousWithinAt θ' (Icc lmin lmax) lamStar := hd' lamStar hstar
  refine ⟨fun lam₀ h₀ hθ₀ => ?_, fun lam₀ h₀ lam₁ h₁ h01 hθ₀ hθ₁ => ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := Newton.monotone_scalarStep_iterate_of_convexOn h h₀ hθ₀
    exact ⟨h1, h2, h3, h4, h5, h6 hcont, h7⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
      Newton.monotone_secant_iterate_of_convexOn h h₀ h₁ h01 hθ₀ hθ₁
    exact ⟨h1, h2, h3, h4, h5, h6 hcont⟩

/-- **Lemma B.8.1 of [cartis2022evaluation], concave case**, corrected: for `θ` concave, strictly
increasing and continuously differentiable on `I` with a root `λ* ∈ I` and `θ'(λ*) ≠ 0`, the same
conclusions hold from `θ(λ₀) < 0` (resp. `θ(λ₀), θ(λ₁) < 0`; the book prints `> 0`). -/
theorem lemma_B_8_1_concave {θ θ' : ℝ → ℝ} {lmin lmax lamStar : ℝ}
    (hc : ConcaveOn ℝ (Icc lmin lmax) θ) (hm : StrictMonoOn θ (Icc lmin lmax))
    (hd : ∀ x ∈ Icc lmin lmax, HasDerivWithinAt θ (θ' x) (Icc lmin lmax) x)
    (hd' : ContinuousOn θ' (Icc lmin lmax)) (hstar : lamStar ∈ Icc lmin lmax)
    (hroot : θ lamStar = 0) (hθ' : θ' lamStar ≠ 0) :
    (∀ lam₀ ∈ Icc lmin lmax, θ lam₀ < 0 →
      (∀ k, (Newton.scalarStep θ θ')^[k] lam₀ ∈ Icc lam₀ lamStar) ∧
      Monotone (fun k => (Newton.scalarStep θ θ')^[k] lam₀) ∧
      Tendsto (fun k => (Newton.scalarStep θ θ')^[k] lam₀) atTop (𝓝 lamStar) ∧
      1 - θ' lamStar / θ' lam₀ ∈ Ico 0 1 ∧
      (∀ k, lamStar - (Newton.scalarStep θ θ')^[k + 1] lam₀ ≤
        (1 - θ' lamStar / θ' lam₀) * (lamStar - (Newton.scalarStep θ θ')^[k] lam₀)) ∧
      ConvergesSuperlinearly (fun k => (Newton.scalarStep θ θ')^[k] lam₀) lamStar ∧
      ((∃ K, ∃ U ∈ 𝓝[Icc lmin lmax] lamStar, LipschitzOnWith K θ' U) →
        ConvergesWithOrder (fun k => (Newton.scalarStep θ θ')^[k] lam₀) lamStar 2)) ∧
    (∀ lam₀ ∈ Icc lmin lmax, ∀ lam₁ ∈ Icc lmin lmax, lam₀ < lam₁ → θ lam₀ < 0 → θ lam₁ < 0 →
      (∀ k, Secant.iterate θ lam₀ lam₁ k ∈ Icc lam₀ lamStar) ∧
      Monotone (Secant.iterate θ lam₀ lam₁) ∧
      Tendsto (Secant.iterate θ lam₀ lam₁) atTop (𝓝 lamStar) ∧
      1 - θ' lamStar / θ' lam₀ ∈ Ico 0 1 ∧
      (∀ k, lamStar - Secant.iterate θ lam₀ lam₁ (k + 1) ≤
        (1 - θ' lamStar / θ' lam₀) * (lamStar - Secant.iterate θ lam₀ lam₁ k)) ∧
      ConvergesSuperlinearly (Secant.iterate θ lam₀ lam₁) lamStar) := by
  have hcont : ContinuousWithinAt θ' (Icc lmin lmax) lamStar := hd' lamStar hstar
  refine ⟨fun lam₀ h₀ hθ₀ => ?_, fun lam₀ h₀ lam₁ h₁ h01 hθ₀ hθ₁ => ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
      Newton.monotone_scalarStep_iterate_of_concaveOn hc hm hd hstar hroot hθ' h₀ hθ₀
    exact ⟨h1, h2, h3, h4, h5, h6 hcont, h7⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
      Newton.monotone_secant_iterate_of_concaveOn hc hm hd hstar hroot hθ' h₀ h₁ h01 hθ₀ hθ₁
    exact ⟨h1, h2, h3, h4, h5, h6 hcont⟩

variable {n : ℕ} {g : EuclideanSpace ℝ (Fin n)} {H M : Matrix (Fin n) (Fin n) ℝ}

/-- **Lemma B.8.2 of [cartis2022evaluation] (Monotonicity of the transformed secular Newton
step).** Let `g ≠ 0`, `λc > λₛ`, `Δ > 0` and `Ψ_β(λ) = π(λ)^β - Δ^{2β}`. For `β ≠ 0` the Newton
step for `Ψ_β` from `λc` is `δ(β) = (-π(λc)/π⁽¹⁾(λc)) (1 - μ^β)/β` with `μ = Δ²/π(λc)` (B.8.7), and
`δ` decreases monotonically on `β ≠ 0`. -/
theorem lemma_B_8_2 (hH : H.IsHermitian) (hM : M.PosDef) (hg : g ≠ 0) {lamc Δ : ℝ}
    (hc : lambdaS hH hM < lamc) (hΔ : 0 < Δ) :
    (∀ β : ℝ, β ≠ 0 →
      -(secularFn g H M lamc ^ β - Δ ^ (2 * β)) /
          deriv (fun t => secularFn g H M t ^ β - Δ ^ (2 * β)) lamc =
        -secularFn g H M lamc / deriv (secularFn g H M) lamc *
          ((1 - (Δ ^ 2 / secularFn g H M lamc) ^ β) / β)) ∧
    AntitoneOn (fun β : ℝ => -secularFn g H M lamc / deriv (secularFn g H M) lamc *
      ((1 - (Δ ^ 2 / secularFn g H M lamc) ^ β) / β)) {β | β ≠ 0} := by
  have hc' := neg_leftmost_lt_of_lambdaS_lt hH hM hc
  have hg' := scaledGrad_ne_zero (hM := hM) hg
  rw [secularFn_eq_secular hM]
  have hpos := secular_pos (hH := isSymmetric_scaledOp hH) hg' hc'
  have hneg := deriv_secular_neg (hH := isSymmetric_scaledOp hH) hg' hc'
  refine ⟨fun β hβ => ?_, fun a ha b hb hab => ?_⟩
  · have := newtonCorrection_eq (hH := isSymmetric_scaledOp hH) hg' hc' hΔ hβ
    rwa [newtonFactor_of_ne_zero _ hβ] at this
  · have ha : a ≠ 0 := ha
    have hb : b ≠ 0 := hb
    have hanti := antitone_newtonFactor (div_pos (pow_pos hΔ 2) hpos) hab
    rw [newtonFactor_of_ne_zero _ ha, newtonFactor_of_ne_zero _ hb] at hanti
    exact mul_le_mul_of_nonneg_left hanti (div_nonneg_of_nonpos (neg_nonpos.2 hpos.le) hneg.le)

end CartisGouldToint.AppendixB

import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.Convex.Strong
import Numlib.Optimization.Constrained
import Numlib.Variational.Minimization
import NumlibSurface.QuarteroniSaccoSaleri.Chapter07.Section02

/-!
# Quarteroni–Sacco–Saleri §7.3: constrained optimization

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §7.3, constrained minimization in `ℝⁿ`: the optimality conditions on a
convex set (Property 7.9), strong convexity (7.49) and Property 7.10, equality constraints with
Definition 7.2, the Lagrangian and Property 7.11, inequality constraints with Definition 7.3 and
the Karush–Kuhn–Tucker conditions of Property 7.12, the nonlinear programming problem (7.52) with
the Kuhn–Tucker conditions of Properties 7.13–7.15, the penalty method (7.53) with Property 7.16,
the augmented Lagrangian (7.55) with Example 7.7, and Property 7.17. The backbone is
`Numlib/Optimization/{Constrained, Descent}`, `Numlib/Analysis/Convex/Gateaux` and
`Numlib/Variational/Minimization`; Mathlib's `IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt`
and `StrongConvexOn`.

## Conventions

Constraints are families `h : Fin m → ℝⁿ → ℝ` and `g : Fin r → ℝⁿ → ℝ`; the book's `J_h(x)`, whose
columns are the `∇h_i(x)`, is the family `fun i => gradient (h i) x`, and the backbone's derivative
data `h' i x = fderiv ℝ (h i) x = innerSL ℝ (∇h_i(x))` (`fderiv_eq_innerSL_gradient` of §7.2).
Local minimizers on a set are `IsLocalMinOn`.

## Readings and errata

* Property 7.10 needs `f` lower semicontinuous on `Ω` (`f x = (x - 1)²` on `[0, 1)`, `f 1 = 5` is
  strongly convex on `[0, 1]` and has no minimizer); the book's `ρ` of (7.49) is Mathlib's
  `m / 2` (`isStronglyConvexOn_iff`).
* Property 7.11, first part, needs `x*` regular (Definition 7.2, introduced just before but not
  invoked): `min x` subject to `x² = 0` has no multiplier.
* Property 7.16 asserts that the penalty minimizers converge to `x*`; what is true is that every
  cluster point is a constrained global minimizer, and convergence needs a unique constrained
  minimizer and a bounded sequence (`property_7_16`).
* Example 7.7's augmented Lagrangian `-x⁴ + λx + ½αx²` has no *global* minimizer; for `λ = 0`
  and `α > 0` the point `0` is a strict local one (`example_7_7_isLocalMin`).
* Property 7.17 (Bertsekas' uniform local analysis of the augmented Lagrangian) is not
  formalized.
-/

open Filter Matrix Metric Set Topology WithLp
open scoped InnerProductSpace

namespace QuarteroniSaccoSaleri.Chapter07

variable {n : ℕ}

/-! ### Property 7.9: optimality on a convex set -/

section Convex

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
  {xstar : EuclideanSpace ℝ (Fin n)}

/-- **Property 7.9 (1).** Let `Ω ⊆ ℝⁿ` be convex, `x* ∈ Ω`, and `f` differentiable at `x*` (the
book's `C¹` on a ball). If `x*` is a local minimizer of `f` on `Ω` then (7.48):
`∇f(x*)ᵀ (x - x*) ≥ 0` for all `x ∈ Ω`. `Descent.fderiv_apply_sub_nonneg_of_isLocalMinOn`. -/
theorem property_7_9_necessary (hΩ : Convex ℝ Ω) (hx : xstar ∈ Ω) (hf : DifferentiableAt ℝ f xstar)
    (hmin : IsLocalMinOn f Ω xstar) : ∀ x ∈ Ω, 0 ≤ ⟪gradient f xstar, x - xstar⟫_ℝ :=
    fun x hxΩ => by
  rw [inner_gradient_left]
  exact Descent.fderiv_apply_sub_nonneg_of_isLocalMinOn hΩ hx hmin hf.hasFDerivAt x hxΩ

/-- **Property 7.9 (2).** If moreover `f` is convex on `Ω` (7.21) and differentiable on `Ω`, then
(7.48) at `x* ∈ Ω` implies that `x*` is a global minimizer of `f` on `Ω`. The sufficiency half of
`isMinOn_iff_forall_lineDeriv_nonneg` (`Numlib/Analysis/Convex/Gateaux`). -/
theorem property_7_9_sufficient (hconv : ConvexOn ℝ Ω f) (hf : ∀ y ∈ Ω, DifferentiableAt ℝ f y)
    (hx : xstar ∈ Ω) (h48 : ∀ x ∈ Ω, 0 ≤ ⟪gradient f xstar, x - xstar⟫_ℝ) : IsMinOn f Ω xstar := by
  refine (isMinOn_iff_forall_lineDeriv_nonneg (f' := fderiv ℝ f) hconv
    (fun u hu v => (hf u hu).hasFDerivAt.hasLineDerivAt v) hx).2 fun v hv => ?_
  rw [← inner_gradient_left]
  exact h48 v hv

/-- **(7.49), strong convexity.** `f : Ω → ℝ` is strongly convex if for some `ρ > 0`,
`f(αx + (1 - α)y) ≤ α f(x) + (1 - α) f(y) - α(1 - α) ρ ‖x - y‖₂²` for all `x, y ∈ Ω` and
`α ∈ [0, 1]`. -/
def IsStronglyConvexOn (f : EuclideanSpace ℝ (Fin n) → ℝ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (ρ : ℝ) : Prop :=
  0 < ρ ∧ ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ α ∈ Icc (0 : ℝ) 1,
    f (α • x + (1 - α) • y) ≤ α * f x + (1 - α) * f y - α * (1 - α) * ρ * ‖x - y‖ ^ 2

/-- (7.49) is Mathlib's `StrongConvexOn Ω m f` with `m = 2ρ` (Mathlib's modulus is
`m / 2 · r²`), for a convex `Ω`. -/
theorem isStronglyConvexOn_iff (hΩ : Convex ℝ Ω) {ρ : ℝ} :
    IsStronglyConvexOn f Ω ρ ↔ 0 < ρ ∧ StrongConvexOn Ω (2 * ρ) f := by
  constructor
  · rintro ⟨hρ, h⟩
    refine ⟨hρ, hΩ, fun x hx y hy a b ha hb hab => ?_⟩
    have hb' : b = 1 - a := by linarith
    subst hb'
    have := h x hx y hy a ⟨ha, by linarith⟩
    simp only [smul_eq_mul]
    linarith
  · rintro ⟨hρ, -, h⟩
    refine ⟨hρ, fun x hx y hy α hα => ?_⟩
    have := h hx hy hα.1 (by linarith [hα.2] : (0 : ℝ) ≤ 1 - α) (by ring)
    simp only [smul_eq_mul] at this
    linarith

-- TODO(backbone): the planned `StrongConvexOn.isCoerciveFunctionalOn` of
-- `Numlib/Variational/Minimization` (open there); proved here in its planned generality so that
-- Property 7.10 delegates to it. Move it there.
/-- **A strongly convex function bounded below near a point of its domain is coercive.** If
`StrongConvexOn K m f` with `0 < m`, `x₀ ∈ K` and `c ≤ f` on `K ∩ B(x₀; r)` for some `r > 0`
(in particular if `f` is lower semicontinuous at `x₀`), then `f` is coercive on `K`: along the
segment from `x₀` to a far point `y ∈ K`, the point `z` at distance `r/2` from `x₀` satisfies
`c ≤ f z ≤ (1-t) f x₀ + t f y - (m/2) t (1-t) ‖y - x₀‖²` with `t = r / (2‖y - x₀‖)`, which
forces `f y ≥ (m/4) ‖y - x₀‖² - (2(|c| + |f x₀|)/r) ‖y - x₀‖`. -/
theorem strongConvexOn_isCoerciveFunctionalOn {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {K : Set V} {m : ℝ} {f : V → ℝ} (hf : StrongConvexOn K m f)
    (hm : 0 < m) {x₀ : V} (hx₀ : x₀ ∈ K) {r c : ℝ} (hr : 0 < r)
    (hc : ∀ y ∈ K, y ∈ ball x₀ r → c ≤ f y) : IsCoerciveFunctionalOn f K := by
  intro M
  set K₀ : ℝ := |c| + |f x₀| with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  set R₀ : ℝ := max (max r (16 * K₀ / (m * r))) (max 1 (8 * |M| / m)) with hR₀
  refine ⟨R₀ + ‖x₀‖, fun y hy hyn => ?_⟩
  set d : ℝ := ‖y - x₀‖ with hd
  have hdR : R₀ ≤ d := by
    have := norm_sub_norm_le y x₀
    linarith
  have hdr : r ≤ d := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hdR
  have hd1 : 1 ≤ d := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hdR
  have hdK : 16 * K₀ / (m * r) ≤ d :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hdR
  have hdM : 8 * |M| / m ≤ d := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hdR
  have hd0 : 0 < d := by linarith
  -- the intermediate point `z = (1 - t) x₀ + t y`
  set t : ℝ := r / (2 * d) with ht
  have ht0 : 0 < t := by positivity
  have htd : t * d = r / 2 := by rw [ht]; field_simp
  have ht1 : t ≤ 1 / 2 := by
    rw [ht, div_le_iff₀ (by positivity)]
    nlinarith
  have hz : (1 - t) • x₀ + t • y ∈ K := hf.1 hx₀ hy (by linarith) ht0.le (by ring)
  have hzball : (1 - t) • x₀ + t • y ∈ ball x₀ r := by
    rw [mem_ball, dist_eq_norm, show (1 - t) • x₀ + t • y - x₀ = t • (y - x₀) by module,
      norm_smul, Real.norm_eq_abs, abs_of_pos ht0, ← hd, htd]
    linarith
  have hfz : c ≤ f ((1 - t) • x₀ + t • y) := hc _ hz hzball
  have hsc := hf.2 hx₀ hy (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le (by ring)
  simp only [smul_eq_mul] at hsc
  rw [← norm_neg, neg_sub, ← hd] at hsc
  -- the key lower bound `t f y ≥ -K₀ + t (m/4) d²`
  have hfx₀ : (1 - t) * f x₀ ≤ |f x₀| := by
    have h1 : f x₀ ≤ |f x₀| := le_abs_self _
    have h2 : 0 ≤ |f x₀| := abs_nonneg _
    nlinarith
  have hcK : -|c| ≤ c := neg_abs_le c
  have hkey : t * (m / 4 * d ^ 2) - K₀ ≤ t * f y := by
    have h1 : t * (m / 4 * d ^ 2) ≤ (1 - t) * t * (m / 2 * d ^ 2) := by
      have : 0 ≤ t * (m / 2 * d ^ 2) := by positivity
      nlinarith
    linarith
  -- divide by `t` and conclude
  have hfy : m / 4 * d ^ 2 - 2 * K₀ / r * d ≤ f y := by
    have h1 : K₀ = t * (2 * K₀ / r * d) := by
      rw [ht]; field_simp
    have h2 : t * (m / 4 * d ^ 2 - 2 * K₀ / r * d) ≤ t * f y := by linarith
    exact le_of_mul_le_mul_left h2 ht0
  have h3 : 2 * K₀ / r * d ≤ m / 8 * d ^ 2 := by
    have : 2 * K₀ / r ≤ m / 8 * d := by
      rw [div_le_iff₀ (by positivity)] at hdK
      rw [div_le_iff₀ hr]
      nlinarith
    nlinarith
  have h4 : |M| ≤ m / 8 * d ^ 2 := by
    rw [div_le_iff₀ hm] at hdM
    have hmd : m * d ≤ m * d ^ 2 := by nlinarith [mul_pos hm hd0]
    nlinarith
  linarith [le_abs_self M]

-- TODO(backbone): the planned `existsUnique_isMinOn_of_strongConvexOn` of
-- `Numlib/Variational/Minimization` (open there); proved here for Property 7.10. Move it there.
/-- **Existence and uniqueness of the minimizer of a strongly convex function** on a nonempty
closed convex subset `K` of a finite-dimensional real inner product space, for `f` lower
semicontinuous on `K` and `StrongConvexOn K m f` with `0 < m`. Existence is
`exists_isMinOn_of_isClosed_of_finiteDimensional` with the coercivity
`strongConvexOn_isCoerciveFunctionalOn` (lower semicontinuity at a point of `K` gives the local
lower bound); uniqueness is `IsMinOn.eq_of_strictConvexOn`. -/
theorem existsUnique_isMinOn_of_strongConvexOn' {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {K : Set V} (hcl : IsClosed K)
    (hne : K.Nonempty) {f : V → ℝ} (hlsc : LowerSemicontinuousOn f K) {m : ℝ}
    (hf : StrongConvexOn K m f) (hm : 0 < m) : ∃! x, x ∈ K ∧ IsMinOn f K x := by
  obtain ⟨x₀, hx₀⟩ := hne
  -- a local lower bound at `x₀`, from lower semicontinuity
  have hlow : ∀ᶠ y in 𝓝[K] x₀, f x₀ - 1 < f y := hlsc x₀ hx₀ (f x₀ - 1) (by linarith)
  obtain ⟨r, hr, hrK⟩ := Metric.mem_nhdsWithin_iff.1 hlow
  have hcoer : IsCoerciveFunctionalOn f K :=
    strongConvexOn_isCoerciveFunctionalOn hf hm hx₀ hr fun y hy hyb => (hrK ⟨hyb, hy⟩).le
  obtain ⟨u, huK, humin⟩ := exists_isMinOn_of_isClosed_of_finiteDimensional (⊤ : Submodule ℝ V)
    (fun _ _ => Submodule.mem_top) hcl ⟨x₀, hx₀⟩ hlsc hcoer
  refine ⟨u, ⟨huK, humin⟩, fun v ⟨hvK, hvmin⟩ => ?_⟩
  exact IsMinOn.eq_of_strictConvexOn (hf.strictConvexOn hm) hvmin humin hvK huK

/-- **Property 7.10, with the hypothesis the book omits.** Let `Ω ⊆ ℝⁿ` be nonempty, closed and
convex, and `f` strongly convex (7.49) *and lower semicontinuous* on `Ω` (the book's examples are
continuous; without semicontinuity the statement is false). Then there is exactly one local
minimizer of `f` on `Ω`, and it is the global one: `∃! x*, x* ∈ Ω ∧ IsMinOn f Ω x*`, and every
local minimizer on `Ω` is a global one (Mathlib's `IsMinOn.of_isLocalMinOn_of_convexOn`). -/
theorem property_7_10 (hΩc : IsClosed Ω) (hΩ : Convex ℝ Ω) (hne : Ω.Nonempty) {ρ : ℝ}
    (hf : IsStronglyConvexOn f Ω ρ) (hlsc : LowerSemicontinuousOn f Ω) :
    (∃! xstar, xstar ∈ Ω ∧ IsMinOn f Ω xstar) ∧
      ∀ x ∈ Ω, IsLocalMinOn f Ω x → IsMinOn f Ω x := by
  obtain ⟨hρ, hsc⟩ := (isStronglyConvexOn_iff hΩ).1 hf
  refine ⟨existsUnique_isMinOn_of_strongConvexOn' hΩc hne hlsc hsc (by positivity),
    fun x hx hloc => IsMinOn.of_isLocalMinOn_of_convexOn hx hloc (hsc.convexOn fun r => ?_)⟩
  positivity

end Convex

/-! ### Equality constraints: Definition 7.2, the Lagrangian and Property 7.11 -/

section Equality

variable {m : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {h : Fin m → EuclideanSpace ℝ (Fin n) → ℝ}
  {xstar : EuclideanSpace ℝ (Fin n)}

/-- `innerSL ℝ` is injective (it is an isometry). -/
private theorem innerSL_injective :
    Function.Injective (innerSL ℝ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  fun a b hab => by
    have h2 : innerSL ℝ (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have h3 := congrArg norm h2
    rw [innerSL_apply_norm, norm_zero, norm_eq_zero] at h3
    exact sub_eq_zero.1 h3

/-- A real linear combination of `innerSL`'s is the `innerSL` of the combination. -/
private theorem sum_smul_innerSL {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (v : ι → EuclideanSpace ℝ (Fin n)) :
    ∑ i ∈ s, c i • innerSL ℝ (v i) = innerSL ℝ (∑ i ∈ s, c i • v i) := by
  simp [map_sum]

/-- `innerSL ℝ` is injective, so a family of gradients is linearly independent iff the family of
the derivatives `innerSL ℝ (∇h_i(x))` is. -/
private theorem linearIndependent_innerSL_iff {ι : Type*} (v : ι → EuclideanSpace ℝ (Fin n)) :
    LinearIndependent ℝ (fun i => innerSL ℝ (v i)) ↔ LinearIndependent ℝ v := by
  simp only [linearIndependent_iff']
  refine forall_congr' fun s => forall_congr' fun c => imp_congr_left ?_
  rw [sum_smul_innerSL, map_eq_zero_iff _ innerSL_injective]

/-- **Definition 7.2.** A point `x*` with `h(x*) = 0` is *regular* if the column vectors
`∇h_i(x*)` of the Jacobian matrix `J_h(x*)` are linearly independent (the `h_i` being `C¹` near
`x*`). -/
def definition_7_2 (h : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Prop :=
  (∀ i, h i x = 0) ∧ LinearIndependent ℝ fun i => gradient (h i) x

/-- Definition 7.2 is the backbone's `Constrained.IsRegularPoint` with the derivative data
`h' i x = fderiv ℝ (h i) x`. -/
theorem definition_7_2_iff (x : EuclideanSpace ℝ (Fin n)) :
    definition_7_2 h x ↔ Constrained.IsRegularPoint h (fun i y => fderiv ℝ (h i) y) x := by
  rw [definition_7_2, Constrained.IsRegularPoint, Constrained.mem_feasibleEq]
  refine and_congr Iff.rfl ?_
  simp only [fderiv_eq_innerSL_gradient]
  exact (linearIndependent_innerSL_iff _).symm

/-- **The Lagrangian** `ℒ(x, λ) = f(x) + λᵀ h(x)` of the equality-constrained problem (7.50):
the backbone's `Constrained.lagrangian`. -/
def lagrangian (f : EuclideanSpace ℝ (Fin n) → ℝ) (h : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (l : Fin m → ℝ) : ℝ :=
  Constrained.lagrangian f h x l

/-- The Lagrangian written out, `ℒ(x, λ) = f(x) + ∑ λ_i h_i(x)`. -/
theorem lagrangian_eq (x : EuclideanSpace ℝ (Fin n)) (l : Fin m → ℝ) :
    lagrangian f h x l = f x + ∑ i, l i * h i x :=
  rfl

/-- **The partial Jacobian `J_ℒ(x, λ)`** of the Lagrangian with respect to `x`, the gradient of
`ℒ(·, λ)`: `∇f(x) + ∑ λ_i ∇h_i(x)`, for `f`, `h_i` differentiable at `x`. -/
theorem gradient_lagrangian {x : EuclideanSpace ℝ (Fin n)} (hf : DifferentiableAt ℝ f x)
    (hh : ∀ i, DifferentiableAt ℝ (h i) x) (l : Fin m → ℝ) :
    gradient (fun y => lagrangian f h y l) x = gradient f x + ∑ i, l i • gradient (h i) x := by
  have hd := Constrained.lagrangian_hasFDerivAt (f' := fun y => fderiv ℝ f y)
    (h' := fun i y => fderiv ℝ (h i) y) hf.hasFDerivAt (fun i => (hh i).hasFDerivAt) l
  refine HasGradientAt.gradient (f' := gradient f x + ∑ i, l i • gradient (h i) x) ?_
  rw [hasGradientAt_iff_hasFDerivAt]
  refine hd.congr_fderiv ?_
  ext v
  simp only [fderiv_eq_innerSL_gradient, InnerProductSpace.toDual_apply_apply, inner_add_left,
    sum_inner, inner_smul_left, RCLike.conj_to_real, _root_.add_apply,
    _root_.sum_apply, _root_.smul_apply, innerSL_apply_apply, smul_eq_mul]

/-- **Property 7.11, first part, with the regularity the statement needs.** Let `x*` be a regular
point (Definition 7.2) and a local minimizer of `f` on `{x | h(x) = 0}`, with `f`, `h_i` of class
`C¹` near `x*`. Then there is a unique `λ* ∈ ℝᵐ` with `J_ℒ(x*, λ*) = 0`, that is,
`∇f(x*) + ∑ λ*_i ∇h_i(x*) = 0`. The book omits the regularity: for `min x` subject to `x² = 0`
no multiplier exists. `Constrained.existsUnique_multipliers_of_isLocalMinOn`. -/
theorem property_7_11 (hreg : definition_7_2 h xstar)
    (hmin : IsLocalMinOn f {x | ∀ i, h i x = 0} xstar) (hf : ContDiffAt ℝ 1 f xstar)
    (hh : ∀ i, ContDiffAt ℝ 1 (h i) xstar) :
    ∃! l : Fin m → ℝ, gradient f xstar + ∑ i, l i • gradient (h i) xstar = 0 := by
  have hex := Constrained.existsUnique_multipliers_of_isLocalMinOn (f' := fun y => fderiv ℝ f y)
    ((definition_7_2_iff xstar).1 hreg) hmin (hf.hasStrictFDerivAt one_ne_zero)
    fun i => (hh i).hasStrictFDerivAt one_ne_zero
  refine (existsUnique_congr fun l => ?_).1 hex
  simp only [fderiv_eq_innerSL_gradient]
  rw [sum_smul_innerSL, ← map_add, map_eq_zero_iff _ innerSL_injective]

/-- **Property 7.11, second part.** Let `x*` satisfy `h(x*) = 0`, with `f`, `h_i` of class `C²`
near `x*`, and let `H_ℒ` be the Hessian matrix of `ℒ(·, λ*)`. If some `λ* ∈ ℝᵐ` satisfies
`J_ℒ(x*, λ*) = 0` and `zᵀ H_ℒ(x*, λ*) z > 0` for every `z ≠ 0` with `∇h(x*)ᵀ z = 0`, then `x*` is a
strict local minimizer of (7.50). `Constrained.isLocalMin_of_lagrangian_second_order`. -/
theorem property_7_11_sufficient (hfeas : ∀ i, h i xstar = 0) (hf : ContDiffAt ℝ 2 f xstar)
    (hh : ∀ i, ContDiffAt ℝ 2 (h i) xstar) {l : Fin m → ℝ}
    (hstat : gradient f xstar + ∑ i, l i • gradient (h i) xstar = 0)
    (hpos : ∀ z, z ≠ 0 → (∀ i, ⟪gradient (h i) xstar, z⟫_ℝ = 0) →
      0 < ⟪toEuclideanLin (hessianMatrix (fun y => lagrangian f h y l) xstar) z, z⟫_ℝ) :
    ∃ δ > 0, ∀ y, (∀ i, h i y = 0) → dist y xstar < δ → y ≠ xstar → f xstar < f y := by
  -- the Lagrangian is `C²` at `x*`
  have hL : ContDiffAt ℝ 2 (fun y => lagrangian f h y l) xstar := by
    simp only [lagrangian_eq]
    exact hf.add (ContDiffAt.sum fun i _ => (hh i).const_smul (l i))
  have hd : DifferentiableAt ℝ (fderiv ℝ fun y => lagrangian f h y l) xstar :=
    (hL.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero
  -- the derivative of the Lagrangian near `x*` is `f' + ∑ λ_i h_i'`
  have hf1 : ∀ᶠ y in 𝓝 xstar, HasFDerivAt f (fderiv ℝ f y) y := by
    filter_upwards [hf.eventually (by simp)] with y hy
    exact (hy.differentiableAt (by simp)).hasFDerivAt
  have hh1 : ∀ i, ∀ᶠ y in 𝓝 xstar, HasFDerivAt (h i) (fderiv ℝ (h i) y) y := fun i => by
    filter_upwards [(hh i).eventually (by simp)] with y hy
    exact (hy.differentiableAt (by simp)).hasFDerivAt
  have hLderiv : (fun y => fderiv ℝ f y + ∑ i, l i • fderiv ℝ (h i) y)
      =ᶠ[𝓝 xstar] fderiv ℝ (fun y => lagrangian f h y l) := by
    filter_upwards [hf1, (Filter.eventually_all).2 hh1] with y hfy hhy
    exact (Constrained.lagrangian_hasFDerivAt hfy hhy l).fderiv.symm
  have hH : HasFDerivAt (fun y => fderiv ℝ f y + ∑ i, l i • fderiv ℝ (h i) y)
      (fderiv ℝ (fderiv ℝ fun y => lagrangian f h y l) xstar) xstar :=
    hd.hasFDerivAt.congr_of_eventuallyEq hLderiv
  refine Constrained.isLocalMin_of_lagrangian_second_order (h' := fun i y => fderiv ℝ (h i) y)
    hfeas hf1 hh1 hH ?_ fun z hz hz' => ?_
  · simp only [fderiv_eq_innerSL_gradient]
    rw [sum_smul_innerSL, ← map_add, hstat, map_zero]
  · rw [← inner_toEuclideanLin_hessianMatrix hd]
    refine hpos z hz fun i => ?_
    have := hz' i
    rwa [fderiv_eq_innerSL_gradient, innerSL_apply_apply] at this

end Equality

/-! ### Inequality constraints: Definition 7.3 and the Kuhn–Tucker conditions of Property 7.12 -/

section Inequality

variable {m r : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {h : Fin m → EuclideanSpace ℝ (Fin n) → ℝ}
  {g : Fin r → EuclideanSpace ℝ (Fin n) → ℝ} {xstar : EuclideanSpace ℝ (Fin n)}

/-- **Definition 7.3.** With `𝒥(x*) = {j | g_j(x*) = 0}` the active set
(`Constrained.activeSet`), a point `x*` with `h(x*) = 0` and `g(x*) ≤ 0` is *regular* if the
columns `∇h_i(x*)` of `J_h(x*)` together with the vectors `∇g_j(x*)`, `j ∈ 𝒥(x*)`, are linearly
independent. -/
def definition_7_3 (h : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin r → EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  (∀ i, h i x = 0) ∧ (∀ j, g j x ≤ 0) ∧
    LinearIndependent ℝ (Sum.elim (fun i => gradient (h i) x)
      fun j : Constrained.activeSet g x => gradient (g j) x)

/-- Definition 7.3 is the backbone's `Constrained.IsRegularPointIneq` with the derivative data. -/
theorem definition_7_3_iff (x : EuclideanSpace ℝ (Fin n)) :
    definition_7_3 h g x ↔ Constrained.IsRegularPointIneq h (fun i y => fderiv ℝ (h i) y) g
      (fun j y => fderiv ℝ (g j) y) x := by
  rw [definition_7_3, Constrained.IsRegularPointIneq]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  simp only [fderiv_eq_innerSL_gradient]
  have : (Sum.elim (fun i => innerSL ℝ (gradient (h i) x))
      fun j : Constrained.activeSet g x => innerSL ℝ (gradient (g j) x))
      = fun s => innerSL ℝ ((Sum.elim (fun i => gradient (h i) x)
        fun j : Constrained.activeSet g x => gradient (g j) x) s) := by
    funext s
    cases s <;> rfl
  rw [this, linearIndependent_innerSL_iff]

/-- **Property 7.12 (Karush–Kuhn–Tucker necessary conditions).** Let `x*` be a regular
(Definition 7.3) local minimizer of `f` on `{x | h(x) = 0 ∧ g(x) ≤ 0}`, with `f`, `h_i`, `g_j` of
class `C¹` near `x*`. Then there is exactly one pair `(λ*, μ*) ∈ ℝᵐ × ℝʳ` with
`J_ℳ(x*, λ*, μ*) = ∇f(x*) + ∑ λ*_i ∇h_i(x*) + ∑ μ*_j ∇g_j(x*) = 0`, `μ*_j ≥ 0` and
`μ*_j g_j(x*) = 0` for all `j`. Existence is `Constrained.exists_kkt_of_isLocalMinOn` (the implicit
function theorem and Farkas' lemma), uniqueness `Constrained.kkt_multipliers_unique`. -/
theorem property_7_12 (hreg : definition_7_3 h g xstar)
    (hmin : IsLocalMinOn f {x | (∀ i, h i x = 0) ∧ ∀ j, g j x ≤ 0} xstar)
    (hf : ContDiffAt ℝ 1 f xstar) (hh : ∀ i, ContDiffAt ℝ 1 (h i) xstar)
    (hg : ∀ j, ContDiffAt ℝ 1 (g j) xstar) :
    ∃! p : (Fin m → ℝ) × (Fin r → ℝ),
      gradient f xstar + ∑ i, p.1 i • gradient (h i) xstar + ∑ j, p.2 j • gradient (g j) xstar = 0
        ∧ (∀ j, 0 ≤ p.2 j) ∧ ∀ j, p.2 j * g j xstar = 0 := by
  have hreg' := (definition_7_3_iff xstar).1 hreg
  have hkkt : ∀ p : (Fin m → ℝ) × (Fin r → ℝ),
      Constrained.IsKKTPoint (fun y => fderiv ℝ f y) h (fun i y => fderiv ℝ (h i) y) g
          (fun j y => fderiv ℝ (g j) y) xstar p.1 p.2 ↔
        gradient f xstar + ∑ i, p.1 i • gradient (h i) xstar
          + ∑ j, p.2 j • gradient (g j) xstar = 0 ∧ (∀ j, 0 ≤ p.2 j) ∧
          ∀ j, p.2 j * g j xstar = 0 := by
    intro p
    have hst : fderiv ℝ f xstar + ∑ i, p.1 i • fderiv ℝ (h i) xstar
          + ∑ j, p.2 j • fderiv ℝ (g j) xstar = 0 ↔
        gradient f xstar + ∑ i, p.1 i • gradient (h i) xstar
          + ∑ j, p.2 j • gradient (g j) xstar = 0 := by
      simp only [fderiv_eq_innerSL_gradient]
      rw [sum_smul_innerSL, sum_smul_innerSL, ← map_add, ← map_add,
        map_eq_zero_iff _ innerSL_injective]
    constructor
    · rintro ⟨-, -, hs, hn, hc⟩
      exact ⟨hst.1 hs, hn, hc⟩
    · rintro ⟨hs, hn, hc⟩
      exact ⟨hreg.1, hreg.2.1, hst.2 hs, hn, hc⟩
  obtain ⟨l, μ, hlμ⟩ := Constrained.exists_kkt_of_isLocalMinOn hreg' hmin
    (hf.differentiableAt one_ne_zero).hasFDerivAt (fun i => (hh i).hasStrictFDerivAt one_ne_zero)
    fun j => (hg j).hasStrictFDerivAt one_ne_zero
  refine ⟨(l, μ), (hkkt (l, μ)).1 hlμ, fun p hp => ?_⟩
  obtain ⟨h1, h2⟩ := Constrained.kkt_multipliers_unique hreg' ((hkkt p).2 hp) hlμ
  exact Prod.ext h1 h2

end Inequality

/-! ### §7.3.1: the nonlinear programming problem and the Kuhn–Tucker conditions -/

section NonlinearProgramming

variable {m : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ}
  {b : Fin m → ℝ} {l k : ℕ} {xstar : EuclideanSpace ℝ (Fin n)}

/-- **(7.52), the feasible region.** The nonlinear programming problem of §7.3.1 is: maximize `f`
subject to `g_i x ≤ b_i` for `i = 1, …, l`, `g_i x ≥ b_i` for `i = l + 1, …, k`, `g_i x = b_i` for
`i = k + 1, …, m`, and `x ≥ 0`. A vector satisfying those constraints is a *feasible solution* and
`feasibleRegion g b l k` is the *feasible region*. The book's one-based index `i` is `i + 1` for
`i : Fin m`, so "`i ≤ l`" reads `(i : ℕ) < l`. The index sets of §7.3.1 are
`I_= = {i | g i x = b i}`, `I_≠` its complement, `J_= = {j | x j = 0}` and `J_> = {j | 0 < x j}`;
they are used only through those conditions and are written out where they occur. -/
def feasibleRegion (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (b : Fin m → ℝ) (l k : ℕ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | (∀ i : Fin m, (i : ℕ) < l → g i x ≤ b i) ∧
    (∀ i : Fin m, l ≤ (i : ℕ) → (i : ℕ) < k → b i ≤ g i x) ∧
    (∀ i : Fin m, k ≤ (i : ℕ) → g i x = b i) ∧ ∀ j, 0 ≤ x j}

/-- Membership in the feasible region of (7.52). -/
@[simp] theorem mem_feasibleRegion {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ feasibleRegion g b l k ↔ (∀ i : Fin m, (i : ℕ) < l → g i x ≤ b i) ∧
      (∀ i : Fin m, l ≤ (i : ℕ) → (i : ℕ) < k → b i ≤ g i x) ∧
      (∀ i : Fin m, k ≤ (i : ℕ) → g i x = b i) ∧ ∀ j, 0 ≤ x j := Iff.rfl

-- TODO(backbone): natural home `Mathlib/Analysis/InnerProductSpace/PiL2`, beside
-- `EuclideanSpace.inner_eq_star_dotProduct`, of which it is the real case written as a sum.
/-- The inner product of `ℝⁿ` in coordinates, `⟪v, w⟫ = ∑ j, v_j w_j`. -/
theorem real_inner_eq_sum (v w : EuclideanSpace ℝ (Fin n)) :
    ⟪v, w⟫_ℝ = ∑ j, v j * w j := by
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- A multiple of a coordinate is a convex function on any convex set. -/
private theorem convexOn_const_mul_coord {C : Set (EuclideanSpace ℝ (Fin n))} (hC : Convex ℝ C)
    (c : ℝ) (j : Fin n) : ConvexOn ℝ C fun y : EuclideanSpace ℝ (Fin n) => c * y j := by
  refine ⟨hC, fun x _ y _ a t _ _ _ => le_of_eq ?_⟩
  have h : (a • x + t • y) j = a * x j + t * y j := by simp
  simp only [smul_eq_mul, h]
  ring

/-- **The Lagrangian of (7.52)**, `ℒ(x, λ) = f(x) + ∑_{i ≤ m} λ_i (b_i - g_i x) - ∑_i λ_{m+i} x_i`.
The book's multiplier `λ ∈ ℝ^{m+n}` is carried as the pair `(λ₁, λ₂)` of its first `m` and last
`n` components, the second block read as a vector of `ℝⁿ`, so that the sign term is the inner
product `⟪λ₂, x⟫` (`nonlinearLagrangian_eq` writes it out in coordinates). -/
noncomputable def nonlinearLagrangian (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (b : Fin m → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (lam : (Fin m → ℝ) × EuclideanSpace ℝ (Fin n)) : ℝ :=
  f x + ∑ i, lam.1 i * (b i - g i x) - ⟪lam.2, x⟫_ℝ

/-- The Lagrangian of (7.52) with its sign term in coordinates. -/
theorem nonlinearLagrangian_eq (x : EuclideanSpace ℝ (Fin n))
    (lam : (Fin m → ℝ) × EuclideanSpace ℝ (Fin n)) :
    nonlinearLagrangian f g b x lam
      = f x + ∑ i, lam.1 i * (b i - g i x) - ∑ j, lam.2 j * x j := by
  rw [nonlinearLagrangian, real_inner_eq_sum]

-- TODO(backbone): natural home `Mathlib/Analysis/InnerProductSpace/PiL2`, beside
-- `EuclideanSpace.proj`; it is how a gradient is read off the coordinate derivatives.
/-- A real functional on `ℝⁿ` written through the coordinate projections:
`⟪v, ·⟫ = ∑ j, v j • proj j`. -/
theorem innerSL_eq_sum_smul_proj (v : EuclideanSpace ℝ (Fin n)) :
    innerSL ℝ v = ∑ j, v j • EuclideanSpace.proj (𝕜 := ℝ) j := by
  ext w
  rw [innerSL_apply_apply, real_inner_eq_sum]
  simp

/-- **The partial Jacobian `J_ℒ(x, λ) = ∇_x ℒ(x, λ)` of the Lagrangian of (7.52)**:
`∇_x ℒ(x, λ) = ∇f(x) - ∑ λ_i ∇g_i(x) - λ₂`, for `f` and the `g_i` differentiable at `x`. -/
theorem gradient_nonlinearLagrangian {x : EuclideanSpace ℝ (Fin n)} (hf : DifferentiableAt ℝ f x)
    (hg : ∀ i, DifferentiableAt ℝ (g i) x) (lam : (Fin m → ℝ) × EuclideanSpace ℝ (Fin n)) :
    gradient (fun y => nonlinearLagrangian f g b y lam) x
      = gradient f x - ∑ i, lam.1 i • gradient (g i) x - lam.2 := by
  have hd : HasFDerivAt (fun y => nonlinearLagrangian f g b y lam)
      (fderiv ℝ f x + ∑ i, lam.1 i • (-fderiv ℝ (g i) x) - innerSL ℝ lam.2) x := by
    simp only [nonlinearLagrangian]
    exact (hf.hasFDerivAt.add (HasFDerivAt.fun_sum (u := Finset.univ) fun i _ =>
      ((hg i).hasFDerivAt.const_sub (b i)).const_mul (lam.1 i))).sub
      (innerSL ℝ lam.2).hasFDerivAt
  refine HasGradientAt.gradient ?_
  rw [hasGradientAt_iff_hasFDerivAt]
  refine hd.congr_fderiv ?_
  ext v
  simp only [fderiv_eq_innerSL_gradient, InnerProductSpace.toDual_apply_apply, inner_sub_left,
    sum_inner, inner_smul_left, RCLike.conj_to_real, _root_.add_apply, _root_.sub_apply,
    _root_.sum_apply, _root_.smul_apply, _root_.neg_apply, innerSL_apply_apply, smul_eq_mul,
    mul_neg]
  rw [Finset.sum_neg_distrib]
  ring


/-- The partial Jacobian of the Lagrangian of (7.52) tested against a direction:
`⟪∇_x ℒ(x, λ), v⟫ = ∇f(x)ᵀv - ∑ λ_i ∇g_i(x)ᵀv - ⟪λ₂, v⟫`. -/
private theorem inner_gradient_nonlinearLagrangian {x : EuclideanSpace ℝ (Fin n)}
    (hf : DifferentiableAt ℝ f x) (hg : ∀ i, DifferentiableAt ℝ (g i) x)
    (lam : (Fin m → ℝ) × EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin n)) :
    ⟪gradient (fun y => nonlinearLagrangian f g b y lam) x, v⟫_ℝ
      = fderiv ℝ f x v - ∑ i, lam.1 i * fderiv ℝ (g i) x v - ⟪lam.2, v⟫_ℝ := by
  rw [gradient_nonlinearLagrangian hf hg, inner_sub_left, inner_sub_left, sum_inner]
  simp only [inner_smul_left, RCLike.conj_to_real, fderiv_eq_innerSL_gradient,
    innerSL_apply_apply]

/-! The translation of (7.52) into the standard form `min -f` subject to `h = 0`, `g̃ ≤ 0` of
Property 7.12: the equalities are indexed by `{i | k ≤ i}`, the inequalities by the `i < k`
together with the `n` sign constraints `-x_j ≤ 0`. -/

/-- The equality constraints of (7.52) in the standard form of Property 7.12: `g_i x - b_i = 0`
for `i = k + 1, …, m`. -/
def standardEq (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (b : Fin m → ℝ) (k : ℕ) :
    {i : Fin m // k ≤ (i : ℕ)} → EuclideanSpace ℝ (Fin n) → ℝ := fun i y => g i y - b i

/-- The derivative data of `standardEq`. -/
noncomputable def standardEqDeriv (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (k : ℕ) :
    {i : Fin m // k ≤ (i : ℕ)} → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := fun i y => fderiv ℝ (g i) y

/-- The sign with which the `i`-th constraint of (7.52) enters the standard form of Property
7.12: `+1` for the constraints `g_i x ≤ b_i` (`i = 1, …, l`) and `-1` for `g_i x ≥ b_i`
(`i = l + 1, …, k`). -/
def standardSign (l : ℕ) (i : Fin m) : ℝ := if (i : ℕ) < l then 1 else -1

/-- The sign attached to a `≤` constraint of (7.52) is `+1`. -/
theorem standardSign_of_lt {i : Fin m} (h : (i : ℕ) < l) : standardSign l i = 1 := by
  simp [standardSign, h]

/-- The sign attached to a `≥` constraint of (7.52) is `-1`. -/
theorem standardSign_of_le {i : Fin m} (h : l ≤ (i : ℕ)) : standardSign l i = -1 := by
  simp [standardSign, Nat.not_lt.2 h]

/-- The inequality constraints of (7.52) in the standard form of Property 7.12:
`σ_i (g_i x - b_i) ≤ 0` with `σ_i = standardSign l i` for `i = 1, …, k` — that is `g_i x ≤ b_i`
for `i ≤ l` and `g_i x ≥ b_i` for `l < i ≤ k` — together with the sign constraints `-x_j ≤ 0`. -/
def standardIneq (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (b : Fin m → ℝ) (l k : ℕ) :
    {i : Fin m // (i : ℕ) < k} ⊕ Fin n → EuclideanSpace ℝ (Fin n) → ℝ :=
  Sum.elim (fun i y => standardSign l (i : Fin m) * (g i y - b i)) fun j y => -y j

/-- The derivative data of `standardIneq`. -/
noncomputable def standardIneqDeriv (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (l k : ℕ) :
    {i : Fin m // (i : ℕ) < k} ⊕ Fin n → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  Sum.elim (fun i y => standardSign l (i : Fin m) • fderiv ℝ (g i) y)
    fun j _ => -EuclideanSpace.proj (𝕜 := ℝ) j

/-- **(7.52) in the standard form of Property 7.12.** The feasible region of (7.52) is the
feasible set of the equality constraints `standardEq` and the inequality constraints
`standardIneq`. The hypothesis `l ≤ k` is the one the index ranges of (7.52) presuppose and the
book does not write; it is carried by every statement below. -/
theorem nonlinearProgram_toStandard (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (b : Fin m → ℝ)
    {l k : ℕ} (hlk : l ≤ k) : feasibleRegion g b l k
      = Constrained.feasible (standardEq g b k) (standardIneq g b l k) := by
  ext x
  simp only [mem_feasibleRegion, Constrained.mem_feasible, standardEq, standardIneq,
    Subtype.forall, Sum.forall, Sum.elim_inl, Sum.elim_inr, sub_eq_zero, neg_nonpos]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h3, fun i hik => ?_, h4⟩
    rcases lt_or_ge (i : ℕ) l with hil | hil
    · rw [standardSign_of_lt hil]
      linarith [h1 i hil]
    · rw [standardSign_of_le hil]
      linarith [h2 i hil hik]
  · rintro ⟨h3, h12, h4⟩
    refine ⟨fun i hil => ?_, fun i hli hik => ?_, h3, h4⟩
    · have h := h12 i (hil.trans_le hlk)
      rw [standardSign_of_lt hil] at h
      linarith
    · have h := h12 i hik
      rw [standardSign_of_le hli] at h
      linarith

/-- **The constraint qualification for (7.52)**, which the book alludes to after Property 7.14
and does not state: `x` is a regular point (Definition 7.3) of the standard form
`nonlinearProgram_toStandard`, that is, the gradients `∇g_i(x)` for the equality constraints
`k < i ≤ m` and for the active inequality constraints, together with the vectors `-e_j` of the
active sign constraints `x_j = 0`, are linearly independent. -/
def IsRegularNLP (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (b : Fin m → ℝ) (l k : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  Constrained.IsRegularPointIneq (standardEq g b k) (standardEqDeriv g k) (standardIneq g b l k)
    (standardIneqDeriv g l k) x

/-! The Kuhn–Tucker conditions of Properties 7.13–7.15. -/

/-- The index set `Fin m` of (7.52) split at `k` into the inequality and the equality block. -/
private theorem sum_split_at {V : Type*} [AddCommMonoid V] (k : ℕ) (F : Fin m → V) :
    ∑ i : {i : Fin m // (i : ℕ) < k}, F i + ∑ i : {i : Fin m // k ≤ (i : ℕ)}, F i = ∑ i, F i := by
  have h1 : ∑ i : {i : Fin m // (i : ℕ) < k}, F i
      = ∑ i ∈ Finset.univ.filter fun i : Fin m => (i : ℕ) < k, F i :=
    (Finset.sum_subtype _ (fun x => by simp) F).symm
  have h2 : ∑ i : {i : Fin m // k ≤ (i : ℕ)}, F i
      = ∑ i ∈ Finset.univ.filter fun i : Fin m => ¬ ((i : ℕ) < k), F i :=
    (Finset.sum_subtype _ (fun x => by simp [not_lt]) F).symm
  rw [h1, h2, Finset.sum_filter_add_sum_filter_not]

/-- **The Kuhn–Tucker multipliers of (7.52).** Let `x*` be a constrained local maximizer of (7.52)
satisfying the constraint qualification `IsRegularNLP`, with `f` and the `g_i` of class `C¹`. Then
there is a multiplier `λ* ∈ ℝ^{m+n}` with `∇_x ℒ(x*, λ*) = 0`, whose components carry the signs
attached to the constraints (`λ*_i ≥ 0` for `g_i x ≤ b_i`, `λ*_i ≤ 0` for `g_i x ≥ b_i`,
`λ*_{m+j} ≤ 0` for `x_j ≥ 0`) and are complementary, `λ*_i (b_i - g_i x*) = 0` and
`λ*_{m+j} x*_j = 0`. Properties 7.13 and 7.14 are its consequences; the signs, which the book does
not list among the Kuhn–Tucker conditions, are what Property 7.15 needs.
`Constrained.exists_kkt_of_isLocalMinOn` applied to `min (-f)` in the standard form. -/
theorem exists_kuhnTucker (hlk : l ≤ k) (hreg : IsRegularNLP g b l k xstar)
    (hmax : IsLocalMaxOn f (feasibleRegion g b l k) xstar) (hf : ContDiff ℝ 1 f)
    (hg : ∀ i, ContDiff ℝ 1 (g i)) :
    ∃ lam : (Fin m → ℝ) × EuclideanSpace ℝ (Fin n),
      gradient (fun y => nonlinearLagrangian f g b y lam) xstar = 0 ∧
        (∀ i : Fin m, (i : ℕ) < l → 0 ≤ lam.1 i) ∧
        (∀ i : Fin m, l ≤ (i : ℕ) → (i : ℕ) < k → lam.1 i ≤ 0) ∧ (∀ j, lam.2 j ≤ 0) ∧
        (∀ i, lam.1 i * (b i - g i xstar) = 0) ∧ ∀ j, lam.2 j * xstar j = 0 := by
  have hdf : ∀ y, HasStrictFDerivAt f (fderiv ℝ f y) y := fun y =>
    hf.contDiffAt.hasStrictFDerivAt one_ne_zero
  have hdg : ∀ i, ∀ y, HasStrictFDerivAt (g i) (fderiv ℝ (g i) y) y := fun i y =>
    (hg i).contDiffAt.hasStrictFDerivAt one_ne_zero
  have hmin : IsLocalMinOn (fun y => -f y)
      (Constrained.feasible (standardEq g b k) (standardIneq g b l k)) xstar := by
    rw [← nonlinearProgram_toStandard g b hlk]
    exact hmax.neg
  obtain ⟨l0, mu, hkkt⟩ := Constrained.exists_kkt_of_isLocalMinOn
    (f' := fun y => -fderiv ℝ f y) (h' := standardEqDeriv g k) (g' := standardIneqDeriv g l k)
    hreg hmin ((hdf xstar).hasFDerivAt.neg) (fun i => (hdg i xstar).sub_const (b i))
    (fun s => by
      cases s with
      | inl i => exact ((hdg i xstar).sub_const (b i)).const_mul (standardSign l (i : Fin m))
      | inr j => exact (EuclideanSpace.proj (𝕜 := ℝ) j).hasStrictFDerivAt.neg)
  set lam1 : Fin m → ℝ := fun i => if hik : (i : ℕ) < k then
    standardSign l i * mu (Sum.inl ⟨i, hik⟩) else l0 ⟨i, not_lt.1 hik⟩ with hlam1
  set lam2 : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun j => -mu (Sum.inr j)) with hlam2
  have hlam2v : ∀ j, lam2 j = -mu (Sum.inr j) := fun j => by rw [hlam2]
  refine ⟨(lam1, lam2), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hdiff : DifferentiableAt ℝ f xstar := (hdf xstar).hasFDerivAt.differentiableAt
    have hdiffg : ∀ i, DifferentiableAt ℝ (g i) xstar := fun i =>
      (hdg i xstar).hasFDerivAt.differentiableAt
    rw [gradient_nonlinearLagrangian hdiff hdiffg]
    refine innerSL_injective ?_
    rw [map_zero, map_sub, map_sub, ← sum_smul_innerSL]
    simp only [← fderiv_eq_innerSL_gradient]
    have hstat : -fderiv ℝ f xstar + ∑ i, l0 i • standardEqDeriv g k i xstar
        + ∑ s, mu s • standardIneqDeriv g l k s xstar = 0 := hkkt.stationary
    have h1 : ∑ i, (lam1, lam2).1 i • fderiv ℝ (g i) xstar
        = ∑ i : {i : Fin m // (i : ℕ) < k},
            mu (Sum.inl i) • standardIneqDeriv g l k (Sum.inl i) xstar
          + ∑ i : {i : Fin m // k ≤ (i : ℕ)}, l0 i • standardEqDeriv g k i xstar := by
      rw [← sum_split_at k fun i => (lam1, lam2).1 i • fderiv ℝ (g i) xstar]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hlam1, dite_eq_left i.2, standardIneqDeriv, Sum.elim_inl, smul_smul, mul_comm]
      · refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hlam1, dite_eq_right (not_lt.2 i.2), standardEqDeriv]
    have h2 : innerSL ℝ (lam1, lam2).2
        = ∑ j, mu (Sum.inr j) • standardIneqDeriv g l k (Sum.inr j) xstar := by
      rw [innerSL_eq_sum_smul_proj]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [standardIneqDeriv, Sum.elim_inr, hlam2v, neg_smul, smul_neg]
    have h3 : fderiv ℝ f xstar - ∑ i, (lam1, lam2).1 i • fderiv ℝ (g i) xstar
          - innerSL ℝ (lam1, lam2).2
        = -(-fderiv ℝ f xstar + ∑ i, l0 i • standardEqDeriv g k i xstar
            + ∑ s, mu s • standardIneqDeriv g l k s xstar) := by
      rw [Fintype.sum_sum_type, h1, h2]
      abel
    rw [h3, hstat, neg_zero]
  · intro i hil
    simp only [hlam1, dite_eq_left (hil.trans_le hlk), standardSign_of_lt hil, one_mul]
    exact hkkt.nonneg _
  · intro i hli hik
    simp only [hlam1, dite_eq_left hik, standardSign_of_le hli, neg_one_mul, neg_nonpos]
    exact hkkt.nonneg _
  · intro j
    rw [hlam2v j, neg_nonpos]
    exact hkkt.nonneg _
  · intro i
    by_cases hik : (i : ℕ) < k
    · have hc := hkkt.complementary (Sum.inl ⟨i, hik⟩)
      simp only [standardIneq, Sum.elim_inl] at hc
      simp only [hlam1, dite_eq_left hik]
      linear_combination -hc
    · have he : g i xstar - b i = 0 := hkkt.feasible_eq ⟨i, not_lt.1 hik⟩
      simp only [hlam1, dite_eq_right hik]
      linear_combination -l0 ⟨i, not_lt.1 hik⟩ * he
  · intro j
    have hc := hkkt.complementary (Sum.inr j)
    simp only [standardIneq, Sum.elim_inr] at hc
    rw [hlam2v j]
    linear_combination hc

/-- **Property 7.13 (Kuhn–Tucker conditions I and II).** If `f` has a constrained local maximum at
`x*` for (7.52) and `f`, `g_i` are of class `C¹`, then — under the constraint qualification
`IsRegularNLP`, which the book mentions after Property 7.14 and does not state — there is a
multiplier `λ* ∈ ℝ^{m+n}` with `∇_x ℒ(x*, λ*) ≤ 0` componentwise, with equality in every component
`j ∈ J_>` (first condition), and `(∇_x ℒ(x*, λ*))ᵀ x* = 0` (second condition). In fact
`∇_x ℒ(x*, λ*) = 0` (`exists_kuhnTucker`), which is stronger than the book's first condition. -/
theorem property_7_13 (hlk : l ≤ k) (hreg : IsRegularNLP g b l k xstar)
    (hmax : IsLocalMaxOn f (feasibleRegion g b l k) xstar) (hf : ContDiff ℝ 1 f)
    (hg : ∀ i, ContDiff ℝ 1 (g i)) :
    ∃ lam : (Fin m → ℝ) × EuclideanSpace ℝ (Fin n),
      (∀ j, gradient (fun y => nonlinearLagrangian f g b y lam) xstar j ≤ 0) ∧
        (∀ j, 0 < xstar j → gradient (fun y => nonlinearLagrangian f g b y lam) xstar j = 0) ∧
        ⟪gradient (fun y => nonlinearLagrangian f g b y lam) xstar, xstar⟫_ℝ = 0 := by
  obtain ⟨lam, hgrad, -, -, -, -, -⟩ := exists_kuhnTucker hlk hreg hmax hf hg
  exact ⟨lam, fun j => by rw [hgrad]; simp, fun j _ => by rw [hgrad]; simp,
    by rw [hgrad, inner_zero_left]⟩

/-- **Property 7.14 (Kuhn–Tucker conditions III and IV).** Under the hypotheses of Property 7.13,
`∂ℒ/∂λ_i (x*, λ*) = b_i - g_i x*` is `≥ 0` for `i ≤ l`, `≤ 0` for `l < i ≤ k` and `= 0` for
`k < i ≤ m` (third condition, which is the feasibility of `x*`), and the multiplier of Property
7.13 also satisfies the complementary slackness `(∇_λ ℒ(x*, λ*))ᵀ λ* = 0` (fourth condition). The
book prints the fourth condition as `(∇_λ ℒ)ᵀ x* = 0`, which cannot be read as it stands: the
vectors `∇_λ ℒ ∈ ℝ^{m+n}` and `x* ∈ ℝⁿ` have different lengths, and the complementary slackness of
the Kuhn–Tucker conditions is `(∇_λ ℒ)ᵀ λ*`. -/
theorem property_7_14 (hlk : l ≤ k) (hreg : IsRegularNLP g b l k xstar)
    (hmax : IsLocalMaxOn f (feasibleRegion g b l k) xstar) (hf : ContDiff ℝ 1 f)
    (hg : ∀ i, ContDiff ℝ 1 (g i)) :
    ((∀ i : Fin m, (i : ℕ) < l → 0 ≤ b i - g i xstar) ∧
        (∀ i : Fin m, l ≤ (i : ℕ) → (i : ℕ) < k → b i - g i xstar ≤ 0) ∧
        ∀ i : Fin m, k ≤ (i : ℕ) → b i - g i xstar = 0) ∧
      ∃ lam : (Fin m → ℝ) × EuclideanSpace ℝ (Fin n),
        (∀ j, gradient (fun y => nonlinearLagrangian f g b y lam) xstar j ≤ 0) ∧
          (∀ j, 0 < xstar j → gradient (fun y => nonlinearLagrangian f g b y lam) xstar j = 0) ∧
          ⟪gradient (fun y => nonlinearLagrangian f g b y lam) xstar, xstar⟫_ℝ = 0 ∧
          ∑ i, lam.1 i * (b i - g i xstar) - ⟪lam.2, xstar⟫_ℝ = 0 := by
  have hfeas : xstar ∈ feasibleRegion g b l k := by
    rw [nonlinearProgram_toStandard g b hlk]
    exact Constrained.IsRegularPointIneq.mem_feasible hreg
  obtain ⟨hy1, hy2, hy3, hy4⟩ := hfeas
  obtain ⟨lam, hgrad, -, -, -, hc1, hc2⟩ := exists_kuhnTucker hlk hreg hmax hf hg
  refine ⟨⟨fun i hil => by linarith [hy1 i hil], fun i hli hik => by linarith [hy2 i hli hik],
    fun i hik => by rw [hy3 i hik]; ring⟩,
    lam, fun j => by rw [hgrad]; simp, fun j _ => by rw [hgrad]; simp,
    by rw [hgrad, inner_zero_left], ?_⟩
  rw [Finset.sum_eq_zero fun i _ => hc1 i, real_inner_eq_sum,
    Finset.sum_eq_zero fun j _ => hc2 j, sub_zero]

/-- **Property 7.15 (sufficiency of the Kuhn–Tucker conditions).** Let `f` be concave and each
`g_i` convex where `λ*_i > 0` and concave where `λ*_i < 0`, on a convex set `C` that contains the
feasible region and lies in the nonnegative orthant (the book says "in the feasible region", which
presupposes that the feasible region is convex; then `C` is it, and otherwise `C` is the orthant
`{x | x ≥ 0}` on which (7.52) is posed). Let `x*` be feasible and let `(x*, λ*)` satisfy the
Kuhn–Tucker conditions I, II and IV together with the signs of the multipliers that the book
leaves out of its list of conditions (`exists_kuhnTucker` supplies them). Then `x*` is a global
maximizer of `f` on the feasible region.
`Constrained.isMinOn_of_lagrangian_convexOn` applied to `-f`. -/
theorem property_7_15 {C : Set (EuclideanSpace ℝ (Fin n))}
    {lam : (Fin m → ℝ) × EuclideanSpace ℝ (Fin n)} (hsub : feasibleRegion g b l k ⊆ C)
    (hCnonneg : ∀ y ∈ C, ∀ j, 0 ≤ y j) (hfeas : xstar ∈ feasibleRegion g b l k)
    (hconc : ConcaveOn ℝ C f) (hgconv : ∀ i, 0 < lam.1 i → ConvexOn ℝ C (g i))
    (hgconc : ∀ i, lam.1 i < 0 → ConcaveOn ℝ C (g i)) (hfd : DifferentiableAt ℝ f xstar)
    (hgd : ∀ i, DifferentiableAt ℝ (g i) xstar)
    (hs1 : ∀ i : Fin m, (i : ℕ) < l → 0 ≤ lam.1 i)
    (hs2 : ∀ i : Fin m, l ≤ (i : ℕ) → (i : ℕ) < k → lam.1 i ≤ 0) (hs3 : ∀ j, lam.2 j ≤ 0)
    (hI : ∀ j, gradient (fun y => nonlinearLagrangian f g b y lam) xstar j ≤ 0)
    (hII : ⟪gradient (fun y => nonlinearLagrangian f g b y lam) xstar, xstar⟫_ℝ = 0)
    (hIV : ∑ i, lam.1 i * (b i - g i xstar) - ⟪lam.2, xstar⟫_ℝ = 0) :
    IsMaxOn f (feasibleRegion g b l k) xstar := by
  have hC : Convex ℝ C := hconc.1
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hfeas
  have hterm1 : ∀ i : Fin m, 0 ≤ lam.1 i * (b i - g i xstar) := by
    intro i
    rcases lt_or_ge (i : ℕ) k with hik | hik
    · rcases lt_or_ge (i : ℕ) l with hil | hil
      · nlinarith [hs1 i hil, hx1 i hil]
      · nlinarith [hs2 i hil hik, hx2 i hil hik]
    · rw [hx3 i hik]
      simp
  have hterm2 : ∀ j, lam.2 j * xstar j ≤ 0 := fun j => by nlinarith [hs3 j, hx4 j]
  have hzero : ∑ i, lam.1 i * (b i - g i xstar) = 0 ∧ ∑ j, lam.2 j * xstar j = 0 := by
    have hA : 0 ≤ ∑ i, lam.1 i * (b i - g i xstar) := Finset.sum_nonneg fun i _ => hterm1 i
    have hB : ∑ j, lam.2 j * xstar j ≤ 0 := Finset.sum_nonpos fun j _ => hterm2 j
    rw [real_inner_eq_sum] at hIV
    exact ⟨by linarith, by linarith⟩
  have hc1 : ∀ i, lam.1 i * (b i - g i xstar) = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hterm1 i).1 hzero.1 i (Finset.mem_univ i)
  have hc2 : ∀ j, lam.2 j * xstar j = 0 := fun j =>
    (Finset.sum_eq_zero_iff_of_nonpos fun j _ => hterm2 j).1 hzero.2 j (Finset.mem_univ j)
  have hnegf : ConvexOn ℝ C (fun y => -f y) := hconc.neg
  have hmin : IsMinOn (fun y => -f y) (feasibleRegion g b l k) xstar := by
    refine Constrained.isMinOn_of_lagrangian_convexOn (C := C)
      (f' := fun y => -fderiv ℝ f y)
      (g := Sum.elim (fun i (y : EuclideanSpace ℝ (Fin n)) => g i y - b i)
        fun j (y : EuclideanSpace ℝ (Fin n)) => -y j)
      (g' := Sum.elim (fun i (y : EuclideanSpace ℝ (Fin n)) => fderiv ℝ (g i) y)
        fun j (_ : EuclideanSpace ℝ (Fin n)) => -EuclideanSpace.proj (𝕜 := ℝ) j)
      (μ := Sum.elim (fun i => lam.1 i) fun j => -lam.2 j)
      hsub ⟨hx1, hx2, hx3, hx4⟩ hnegf ?_ hfd.hasFDerivAt.neg ?_ ?_ ?_ ?_
    · rintro (i | j)
      · simp only [Sum.elim_inl]
        rcases lt_trichotomy (lam.1 i) 0 with h | h | h
        · have he : (fun y => lam.1 i * (g i y - b i))
              = fun y => (-lam.1 i) • (-(fun y => g i y + -b i)) y := by
            funext y
            simp only [Pi.neg_apply, smul_eq_mul]
            ring
          rw [he]
          exact ((hgconc i h).add_const (-b i)).neg.smul (neg_nonneg.2 h.le)
        · have he : (fun y => lam.1 i * (g i y - b i)) = fun _ => (0 : ℝ) := by
            funext y
            rw [h]
            ring
          rw [he]
          exact convexOn_const 0 hC
        · have he : (fun y => lam.1 i * (g i y - b i)) = fun y => lam.1 i • (g i y + -b i) := by
            funext y
            simp only [smul_eq_mul]
            ring
          rw [he]
          exact ((hgconv i h).add_const (-b i)).smul h.le
      · simp only [Sum.elim_inr]
        have he : (fun y : EuclideanSpace ℝ (Fin n) => -lam.2 j * -y j)
            = fun y => lam.2 j * y j := by
          funext y
          ring
        rw [he]
        exact convexOn_const_mul_coord hC (lam.2 j) j
    · rintro (i | j)
      · exact (hgd i).hasFDerivAt.sub_const (b i)
      · exact (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.neg
    · rintro y ⟨hz1, hz2, hz3, hz4⟩ (i | j)
      · simp only [Sum.elim_inl]
        rcases lt_or_ge (i : ℕ) k with hik | hik
        · rcases lt_or_ge (i : ℕ) l with hil | hil
          · nlinarith [hs1 i hil, hz1 i hil]
          · nlinarith [hs2 i hil hik, hz2 i hil hik]
        · rw [hz3 i hik]
          simp
      · simp only [Sum.elim_inr]
        nlinarith [hs3 j, hz4 j]
    · rintro (i | j)
      · simp only [Sum.elim_inl]
        linear_combination -hc1 i
      · simp only [Sum.elim_inr]
        linear_combination hc2 j
    · intro y hyC
      have h2 := inner_gradient_nonlinearLagrangian (b := b) hfd hgd lam (y - xstar)
      have h3 : ⟪gradient (fun y => nonlinearLagrangian f g b y lam) xstar, y - xstar⟫_ℝ
          = ⟪gradient (fun y => nonlinearLagrangian f g b y lam) xstar, y⟫_ℝ := by
        rw [inner_sub_right, hII, sub_zero]
      have h4 : ⟪gradient (fun y => nonlinearLagrangian f g b y lam) xstar, y⟫_ℝ ≤ 0 := by
        rw [real_inner_eq_sum]
        exact Finset.sum_nonpos fun j _ => by nlinarith [hI j, hCnonneg y hyC j]
      have h5 : ∑ j : Fin n, -lam.2 j * -((y - xstar) j) = ⟪lam.2, y - xstar⟫_ℝ := by
        rw [real_inner_eq_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, _root_.neg_apply, EuclideanSpace.coe_proj]
      linarith [h2, h3, h4, h5]
  refine isMaxOn_iff.2 fun y hy => ?_
  have h := isMinOn_iff.1 hmin y hy
  linarith

end NonlinearProgramming

/-! ### The penalty method and the augmented Lagrangian -/

section Penalty

variable {m : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
  {h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}

/-- **(7.53).** The penalized Lagrangian `ℒ_α(x) = f(x) + ½ α ‖h(x)‖₂²` is the backbone's
`Constrained.penalized f h α`, and where the constraint is exactly satisfied it coincides with
`f`, so that "minimizing `f` would be equivalent to minimizing `ℒ_α`". -/
theorem equation_7_53 (α : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Constrained.penalized f h α x = f x + 1 / 2 * α * ‖h x‖ ^ 2 ∧
      (h x = 0 → Constrained.penalized f h α x = f x) :=
  ⟨rfl, fun hx => by simp [Constrained.penalized, hx]⟩

-- The book's `α_k` is "monotonically divergent"; the backbone's `Constrained.penalty_clusterPt`
-- needs only the divergence, so `hpos` and `hmono` are carried for fidelity.
set_option linter.unusedVariables false in
/-- **Property 7.16, in the form that is true.** Let `f : ℝⁿ → ℝ` and `h : ℝⁿ → ℝᵐ` be continuous
on a closed set `Ω`, let the penalty parameters `α_k > 0` be monotonically divergent, let `x*` be
a global minimizer of `f` on `{x ∈ Ω | h(x) = 0}`, and let `x*_k` be a global minimizer of
`ℒ_{α_k}` on `Ω` for each `k` (7.54). Then every cluster point of `x*_k` lies in `Ω`, satisfies
the constraint and is a global minimizer of `f` on `{x ∈ Ω | h(x) = 0}`
(`Constrained.penalty_clusterPt`); and if the constrained minimizer is unique and the sequence
is bounded (for instance `Ω` compact), then `x*_k → x*` (`Constrained.tendsto_penalty_of_unique`).
The book asserts the convergence to `x*` outright, which fails when the constrained problem has
several minimizers. -/
theorem property_7_16 {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsClosed Ω)
    (hf : ContinuousOn f Ω) (hh : ContinuousOn h Ω) {α : ℕ → ℝ} (hpos : ∀ k, 0 < α k)
    (hmono : Monotone α) (hdiv : Tendsto α atTop atTop) {xstar : EuclideanSpace ℝ (Fin n)}
    (hstar : xstar ∈ Ω ∧ h xstar = 0) (hmin : IsMinOn f {y | y ∈ Ω ∧ h y = 0} xstar)
    {xk : ℕ → EuclideanSpace ℝ (Fin n)} (hxk : ∀ k, xk k ∈ Ω)
    (hxmin : ∀ k, IsMinOn (Constrained.penalized f h (α k)) Ω (xk k)) :
    (∀ xbar, MapClusterPt xbar atTop xk →
        xbar ∈ Ω ∧ h xbar = 0 ∧ IsMinOn f {y | y ∈ Ω ∧ h y = 0} xbar) ∧
      ((∀ y ∈ Ω, h y = 0 → IsMinOn f {y | y ∈ Ω ∧ h y = 0} y → y = xstar) →
        Bornology.IsBounded (Set.range xk) → Tendsto xk atTop (𝓝 xstar)) :=
  ⟨fun xbar hcl => Constrained.penalty_clusterPt hΩ hf hh hdiv hstar hmin hxk hxmin hcl,
    fun huniq hbdd => Constrained.tendsto_penalty_of_unique hΩ hf hh hdiv hstar hmin huniq hxk
      hxmin hbdd⟩

/-- **(7.55).** The augmented Lagrangian `𝒢_α(x, λ) = f(x) + λᵀ h(x) + ½ α ‖h(x)‖₂²` is the
backbone's `Constrained.augmented f h α λ`; with `λ = 0` it is the penalized Lagrangian (7.53);
and a solution `x*` of the constrained problem (7.50) minimizes `𝒢_α(·, λ)` over the constraint set
`{x | h(x) = 0}` for every `α` and `λ`, where `𝒢_α(·, λ) = f`. -/
theorem equation_7_55 (α : ℝ) (l : EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin n)) :
    Constrained.augmented f h α l x = f x + ⟪l, h x⟫_ℝ + 1 / 2 * α * ‖h x‖ ^ 2 ∧
      Constrained.augmented f h α 0 = Constrained.penalized f h α ∧
      ∀ xstar, h xstar = 0 → IsMinOn f {y | h y = 0} xstar →
        IsMinOn (Constrained.augmented f h α l) {y | h y = 0} xstar := by
  refine ⟨rfl, Constrained.augmented_zero f h α, fun xstar hx hstar =>
    isMinOn_iff.2 fun y hy => ?_⟩
  have hy' : h y = 0 := hy
  simp only [Constrained.augmented, hx, hy', inner_zero_right, norm_zero, add_zero]
  simpa using isMinOn_iff.1 hstar y hy

/-- **The text after (7.56).** Property 7.16 also holds for the method of multipliers (7.56) when
the multiplier sequence `λ_k` is bounded: with the hypotheses of `property_7_16` and `x*_k` a
global minimizer of `𝒢_{α_k}(·, λ_k)` on `Ω`, every cluster point of `x*_k` is a constrained global
minimizer. `Constrained.augmented_clusterPt`. -/
theorem property_7_16_augmented {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsClosed Ω)
    (hf : ContinuousOn f Ω) (hh : ContinuousOn h Ω) {α : ℕ → ℝ} (hdiv : Tendsto α atTop atTop)
    {xstar : EuclideanSpace ℝ (Fin n)} (hstar : xstar ∈ Ω ∧ h xstar = 0)
    (hmin : IsMinOn f {y | y ∈ Ω ∧ h y = 0} xstar) {l : ℕ → EuclideanSpace ℝ (Fin m)} {Λ : ℝ}
    (hl : ∀ k, ‖l k‖ ≤ Λ) {xk : ℕ → EuclideanSpace ℝ (Fin n)} (hxk : ∀ k, xk k ∈ Ω)
    (hxmin : ∀ k, IsMinOn (Constrained.augmented f h (α k) (l k)) Ω (xk k))
    {xbar : EuclideanSpace ℝ (Fin n)} (hcl : MapClusterPt xbar atTop xk) :
    xbar ∈ Ω ∧ h xbar = 0 ∧ IsMinOn f {y | y ∈ Ω ∧ h y = 0} xbar :=
  Constrained.augmented_clusterPt hΩ hf hh hdiv hstar hmin hl hxk hxmin hcl

end Penalty

/-! ### Example 7.7 -/

section Example77

/-- **Example 7.7.** For `f(x) = -x⁴` on `ℝ` with the constraint `x = 0`, the constrained problem
has the solution `x* = 0`, but for every `α` and `λ` the augmented Lagrangian
`𝒢_α(x, λ) = -x⁴ + λx + ½αx²` has no global minimizer on `ℝ` (it tends to `-∞`), so problem
(7.56) has no solution. The book's "no longer admits a minimum at `x = 0` … for any `α_k ≠ 0`" is
to be read as this; see `example_7_7_isLocalMin`. -/
theorem example_7_7 (α l : ℝ) :
    IsMinOn (fun x : ℝ => -x ^ 4) {x | x = 0} 0 ∧
      (∀ x, Constrained.augmented (fun x : ℝ => -x ^ 4) (fun x : ℝ => x) α l x
        = -x ^ 4 + l * x + 1 / 2 * α * x ^ 2) ∧
      ¬ ∃ x₀, IsMinOn (Constrained.augmented (fun x : ℝ => -x ^ 4) (fun x : ℝ => x) α l) univ
        x₀ := by
  have hinner : ∀ a b : ℝ, ⟪a, b⟫_ℝ = a * b := fun a b => by simp [mul_comm]
  refine ⟨isMinOn_iff.2 fun x hx => by rw [show x = 0 from hx], fun x => ?_,
    fun ⟨x₀, hx₀⟩ => ?_⟩
  · simp only [Constrained.augmented, hinner, Real.norm_eq_abs, sq_abs]
  · -- a point far out is below `x₀`
    set S : ℝ := |x₀| + |l| + |α| + 1 with hS
    have hS1 : 1 ≤ S := by rw [hS]; linarith [abs_nonneg x₀, abs_nonneg l, abs_nonneg α]
    have hx₀S : |x₀| ≤ S := by rw [hS]; linarith [abs_nonneg l, abs_nonneg α]
    have hlS : |l| ≤ S := by rw [hS]; linarith [abs_nonneg x₀, abs_nonneg α]
    have hαS : |α| ≤ S := by rw [hS]; linarith [abs_nonneg x₀, abs_nonneg l]
    have hS2' : 1 ≤ S ^ 2 := by nlinarith
    have hS2 : S ^ 2 ≤ S ^ 4 := by
      calc S ^ 2 = S ^ 2 * 1 := by ring
        _ ≤ S ^ 2 * S ^ 2 := mul_le_mul_of_nonneg_left hS2' (sq_nonneg S)
        _ = S ^ 4 := by ring
    have hS3 : S ^ 3 ≤ S ^ 4 := by
      calc S ^ 3 = S ^ 3 * 1 := by ring
        _ ≤ S ^ 3 * S := mul_le_mul_of_nonneg_left hS1 (by positivity)
        _ = S ^ 4 := by ring
    have hT := isMinOn_iff.1 hx₀ (2 * S) (mem_univ _)
    simp only [Constrained.augmented, Real.norm_eq_abs, sq_abs, hinner] at hT
    -- `g(x₀) ≥ -3 S⁴` and `g(2S) ≤ -8 S⁴`
    have h1 : -x₀ ^ 4 + l * x₀ + 1 / 2 * α * x₀ ^ 2 ≥ -3 * S ^ 4 := by
      have ha : x₀ ^ 4 ≤ S ^ 4 := by
        have := pow_le_pow_left₀ (abs_nonneg x₀) hx₀S 4
        rwa [pow_abs, abs_of_nonneg (by positivity)] at this
      have hb : l * x₀ ≥ -(S * S) := by
        have := neg_abs_le (l * x₀)
        rw [abs_mul] at this
        nlinarith [abs_nonneg l, abs_nonneg x₀]
      have hc : 1 / 2 * α * x₀ ^ 2 ≥ -(S * S ^ 2) := by
        have h2 : x₀ ^ 2 ≤ S ^ 2 := by
          have := pow_le_pow_left₀ (abs_nonneg x₀) hx₀S 2
          rwa [pow_abs, abs_of_nonneg (by positivity)] at this
        have h3 := neg_abs_le α
        nlinarith [sq_nonneg x₀, abs_nonneg α]
      nlinarith
    have h2 : -(2 * S) ^ 4 + l * (2 * S) + 1 / 2 * α * (2 * S) ^ 2 ≤ -8 * S ^ 4 := by
      have hb : l * (2 * S) ≤ 2 * S * S := by nlinarith [le_abs_self l]
      have hc : 1 / 2 * α * (2 * S) ^ 2 ≤ 2 * S * S ^ 2 := by nlinarith [le_abs_self α]
      nlinarith
    nlinarith

/-- **Example 7.7, the local statement.** For `λ = 0` and `α > 0` the point `0` *is* a strict
local minimizer of `𝒢_α(·, 0) = -x⁴ + ½αx²`, since `𝒢''(0) = α > 0`: what fails at `0` is the
global minimality. -/
theorem example_7_7_isLocalMin {α : ℝ} (hα : 0 < α) :
    ∃ δ > 0, ∀ x : ℝ, |x| < δ → x ≠ 0 →
      Constrained.augmented (fun x : ℝ => -x ^ 4) (fun x : ℝ => x) α 0 0
        < Constrained.augmented (fun x : ℝ => -x ^ 4) (fun x : ℝ => x) α 0 x := by
  refine ⟨min 1 (α / 2), lt_min one_pos (by positivity), fun x hx hx0 => ?_⟩
  simp only [Constrained.augmented, Real.norm_eq_abs, sq_abs, inner_zero_left, add_zero]
  have hx1 : |x| < 1 := lt_of_lt_of_le hx (min_le_left _ _)
  have hxα : |x| < α / 2 := lt_of_lt_of_le hx (min_le_right _ _)
  have hxpos : 0 < |x| := abs_pos.2 hx0
  have hsq : x ^ 2 < α / 2 := by
    have : x ^ 2 = |x| * |x| := by rw [← sq_abs, sq]
    nlinarith
  have hx2 : 0 < x ^ 2 := by positivity
  nlinarith

end Example77

end QuarteroniSaccoSaleri.Chapter07

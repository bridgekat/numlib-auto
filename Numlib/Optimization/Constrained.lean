import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.LagrangeMultipliers
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Numlib.Analysis.Calculus.Taylor
import Numlib.Analysis.Convex.Gateaux
import Numlib.Analysis.Convex.LinearInequalities
import Numlib.Analysis.Convex.Extremum.Program

/-!
# Constrained optimization: Lagrange multipliers, Karush–Kuhn–Tucker, penalty methods

Constrained minimization on a real normed space ([quarteroni2000numerical] §7.3; Nocedal–Wright,
*Numerical Optimization*, Ch. 12; Bertsekas, *Constrained Optimization and Lagrange Multiplier
Methods*, Ch. 1, 2, 4): equality constraints `h i x = 0` indexed by a `Fintype ι`, inequality
constraints `g j x ≤ 0` indexed by a `Fintype κ`. Derivatives are data, `f' : E → E →L[ℝ] ℝ` and
`h' : ι → E → E →L[ℝ] ℝ`, as in `Numlib/Analysis/Convex/Gateaux`.

## Main definitions

* `Constrained.feasibleEq h`, `Constrained.feasible h g`: the feasible sets;
* `Constrained.IsRegularPoint h h' x`: a feasible point whose constraint gradients are linearly
  independent ([quarteroni2000numerical] Definition 7.2);
* `Constrained.lagrangian f h x l = f x + ∑ i, l i * h i x`;
* `Constrained.activeSet g x`, `Constrained.IsRegularPointIneq h h' g g' x`: the active
  inequality constraints and regularity in their presence, the linear independence constraint
  qualification (LICQ; [quarteroni2000numerical] Definition 7.3);
* `Constrained.IsKKTPoint f' h h' g g' x l μ`: the Karush–Kuhn–Tucker conditions;
* `Constrained.penalized f h α`, `Constrained.augmented f h α l`: the penalized and augmented
  Lagrangians ([quarteroni2000numerical] (7.53), (7.55)).

## Main statements

* `Constrained.existsUnique_multipliers_of_isLocalMinOn`: Lagrange multipliers exist and are
  unique at a regular local minimizer ([quarteroni2000numerical] Property 7.11, first part), from
  Mathlib's `IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt`, which produces a nontrivial
  `(Λ, Λ₀)`, and regularity, which normalizes `Λ₀ = 1`;
* `Constrained.isLocalMin_of_lagrangian_second_order`: the second-order sufficient condition
  ([quarteroni2000numerical] Property 7.11, second part);
* `Constrained.exists_kkt_of_isLocalMinOn`: the Kuhn–Tucker necessary conditions under LICQ
  ([quarteroni2000numerical] Property 7.12), through the linearizing lemma
  `Constrained.mem_posTangentConeAt_of_isRegularPointIneq` (the implicit function theorem) and
  Farkas' lemma `ConvexAnalysis.farkas`; `Constrained.kkt_multipliers_unique` is the uniqueness;
* `Constrained.isMinOn_of_lagrangian_convexOn`: sufficiency of the Kuhn–Tucker conditions for a
  convex program ([quarteroni2000numerical] Property 7.15);
* `Constrained.exists_kkt_of_convexOn_of_slater`: the Kuhn–Tucker conditions for a differentiable
  convex program under Slater's condition, restated from
  `ConvexAnalysis.exists_multipliers_of_slater_eq` of the convex library;
* `Constrained.penalty_clusterPt`, `Constrained.tendsto_penalty_of_unique`,
  `Constrained.augmented_clusterPt`: convergence of the penalty method and of the method of
  multipliers ([quarteroni2000numerical] Property 7.16, in its correct cluster-point form);
* `Constrained.exists_forall_pos_add_mul_sq_norm_of_pos_on_ker`: **Debreu's lemma** (Bertsekas
  Lemma 1.25), a bilinear form positive on the kernel of `A` becomes positive definite after
  adding `α ‖A ·‖²` for large `α`; `Constrained.fderiv_fderiv_augmented_apply`, the Hessian of
  the augmented Lagrangian at a feasible point, `H_{𝒢_α} = H_ℒ + α J_hᵀ J_h`; and
  `Constrained.exists_forall_pos_fderiv_fderiv_augmented`, condition 3 of Bertsekas'
  Proposition 2.4 ([quarteroni2000numerical] Property 7.17) from its condition 2.

## Design

The smooth theory of this module and the convex theory of `Numlib/Analysis/Convex/Extremum`
meet in two places: the sufficiency theorem, which is the tangent-functional inequality of
`Numlib/Analysis/Convex/Gateaux`, and the Slater theorem, restated from the convex library. The
Kuhn–Tucker theorem under LICQ is proved, not assumed: the tangent cone of the feasible set
contains the linearized cone (Mathlib's implicit function theorem applied to the active
constraints), the first-order condition holds on the tangent cone
(`IsLocalMinOn.hasFDerivWithinAt_nonneg`), and Farkas' lemma turns it into the multipliers.
Property 7.16 is stated for cluster points; the book's "the sequence converges" needs a unique
constrained minimizer and a bounded sequence (`tendsto_penalty_of_unique`).
-/

open Filter Set Topology

namespace Constrained

/-! ### Feasible sets, active constraints and the Lagrangian -/

section Defs

variable {E : Type*} {ι κ : Type*}

/-- The feasible set of the equality constraints `h i x = 0`
([quarteroni2000numerical] (7.50)). -/
def feasibleEq (h : ι → E → ℝ) : Set E := {x | ∀ i, h i x = 0}

/-- The feasible set of the mixed constraints `h i x = 0`, `g j x ≤ 0`
([quarteroni2000numerical] (7.51)). -/
def feasible (h : ι → E → ℝ) (g : κ → E → ℝ) : Set E := {x | (∀ i, h i x = 0) ∧ ∀ j, g j x ≤ 0}

/-- Membership in the feasible set of the equality constraints. -/
@[simp] theorem mem_feasibleEq {h : ι → E → ℝ} {x : E} : x ∈ feasibleEq h ↔ ∀ i, h i x = 0 :=
  Iff.rfl

/-- Membership in the feasible set of the mixed constraints. -/
@[simp] theorem mem_feasible {h : ι → E → ℝ} {g : κ → E → ℝ} {x : E} :
    x ∈ feasible h g ↔ (∀ i, h i x = 0) ∧ ∀ j, g j x ≤ 0 := Iff.rfl

/-- The active inequality constraints at `x`, `𝒥(x) = {j | g_j x = 0}`
([quarteroni2000numerical] Definition 7.3). -/
def activeSet (g : κ → E → ℝ) (x : E) : Set κ := {j | g j x = 0}

/-- A constraint is active at `x` when it holds with equality there. -/
@[simp] theorem mem_activeSet {g : κ → E → ℝ} {x : E} {j : κ} : j ∈ activeSet g x ↔ g j x = 0 :=
  Iff.rfl

variable [Fintype ι]

/-- The Lagrangian `ℒ(x, λ) = f x + ∑ λ_i h_i x` of the equality-constrained problem
([quarteroni2000numerical] §7.3). -/
def lagrangian (f : E → ℝ) (h : ι → E → ℝ) (x : E) (l : ι → ℝ) : ℝ := f x + ∑ i, l i * h i x

/-- On the feasible set the Lagrangian is the objective. -/
theorem lagrangian_eq_of_mem {f : E → ℝ} {h : ι → E → ℝ} {x : E} (hx : x ∈ feasibleEq h)
    (l : ι → ℝ) : lagrangian f h x l = f x := by
  simp [lagrangian, hx _]

end Defs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι κ : Type*} [Fintype ι] [Fintype κ]

/-! ### Regular points and Lagrange multipliers -/

omit [Fintype κ] in
/-- [quarteroni2000numerical] Definition 7.2: a *regular point* of the equality constraints is a
feasible point at which the constraint gradients are linearly independent (the linear independence
constraint qualification for equality constraints). -/
def IsRegularPoint (h : ι → E → ℝ) (h' : ι → E → E →L[ℝ] ℝ) (x : E) : Prop :=
  x ∈ feasibleEq h ∧ LinearIndependent ℝ fun i => h' i x

/-- The derivative of the Lagrangian in `x`: `ℒ' = f' + ∑ λ_i h_i'`. -/
theorem lagrangian_hasFDerivAt {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} {h : ι → E → ℝ}
    {h' : ι → E → E →L[ℝ] ℝ} {x : E} (hf : HasFDerivAt f (f' x) x)
    (hh : ∀ i, HasFDerivAt (h i) (h' i x) x) (l : ι → ℝ) :
    HasFDerivAt (fun y => lagrangian f h y l) (f' x + ∑ i, l i • h' i x) x :=
  hf.add (HasFDerivAt.fun_sum (u := Finset.univ) fun i _ => (hh i).const_mul (l i))

/-! ### Lagrange multipliers at a regular local minimizer -/

/-- A vanishing combination of linearly independent functionals has zero coefficients. -/
private theorem coeff_eq_zero_of_sum_smul_eq_zero {σ : Type*} [Fintype σ] {φ : σ → E →L[ℝ] ℝ}
    (hφ : LinearIndependent ℝ φ) {c : σ → ℝ} (hc : ∑ s, c s • φ s = 0) : ∀ s, c s = 0 :=
  Fintype.linearIndependent_iff.1 hφ c hc

/-- [quarteroni2000numerical] Property 7.11, first part, with the regularity hypothesis the book
omits (without it multipliers need not exist: `min x` subject to `x² = 0`): at a regular local
minimizer `x` of `f` on the equality constraints there is a unique multiplier vector `λ` with
`f' x + ∑ λ_i h_i' x = 0`, that is, the Lagrangian is stationary in `x` at `(x, λ)`. Existence up to
normalization is Mathlib's `IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt`, which needs the
strict differentiability and the completeness; regularity forces the multiplier of `f'` to be
nonzero and gives the uniqueness. -/
theorem existsUnique_multipliers_of_isLocalMinOn [CompleteSpace E] {f : E → ℝ}
    {f' : E → E →L[ℝ] ℝ} {h : ι → E → ℝ} {h' : ι → E → E →L[ℝ] ℝ} {x : E}
    (hx : IsRegularPoint h h' x) (hmin : IsLocalMinOn f (feasibleEq h) x)
    (hf : HasStrictFDerivAt f (f' x) x) (hh : ∀ i, HasStrictFDerivAt (h i) (h' i x) x) :
    ∃! l : ι → ℝ, f' x + ∑ i, l i • h' i x = 0 := by
  have hset : feasibleEq h = {y | ∀ i, h i y = h i x} := by
    ext y
    simp only [feasibleEq, Set.mem_ofPred_eq]
    exact forall_congr' fun i => by rw [hx.1 i]
  have hextr : IsLocalExtrOn f {y | ∀ i, h i y = h i x} x := by
    rw [← hset]; exact IsMinFilter.isExtrFilter hmin
  obtain ⟨Λ, Λ₀, hne, hsum⟩ := hextr.exists_multipliers_of_hasStrictFDerivAt hh hf
  have hΛ₀ : Λ₀ ≠ 0 := by
    rintro rfl
    rw [zero_smul, add_zero] at hsum
    exact hne (Prod.ext (funext fun i => coeff_eq_zero_of_sum_smul_eq_zero hx.2 hsum i) rfl)
  have hnorm : f' x + ∑ i, (Λ i / Λ₀) • h' i x = 0 := by
    have h1 : ∑ i, (Λ i / Λ₀) • h' i x = Λ₀⁻¹ • ∑ i, Λ i • h' i x := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, div_eq_inv_mul]
    have h2 : f' x = Λ₀⁻¹ • (Λ₀ • f' x) := by rw [smul_smul, inv_mul_cancel₀ hΛ₀, one_smul]
    rw [h1, h2, ← smul_add, add_comm, hsum, smul_zero]
  refine ⟨fun i => Λ i / Λ₀, hnorm, fun l hl => funext fun i => ?_⟩
  have h2 : ∑ j, (l j - Λ j / Λ₀) • h' j x = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, sub_eq_zero]
    exact add_left_cancel (hl.trans hnorm.symm)
  exact sub_eq_zero.1 (coeff_eq_zero_of_sum_smul_eq_zero hx.2 h2 i)

/-! ### The second-order sufficient condition -/

/-- [quarteroni2000numerical] Property 7.11, second part (the second-order sufficient condition;
Nocedal–Wright Theorem 12.6): let `x` satisfy the equality constraints, let `f` and the `h_i` be
differentiable near `x` with the derivative of the Lagrangian `y ↦ f' y + ∑ λ_i h_i' y`
differentiable at `x`, with derivative `H` (the Hessian of the Lagrangian at `(x, λ)`); if the
Lagrangian is stationary at `x` and `H` is positive definite on the tangent space of the
constraints, `0 < H z z` for `z ≠ 0` with `h_i' x z = 0`, then `x` is a strict local minimizer of
`f` on the constraint set. Neither regularity nor the implicit function theorem is needed: a
sequence of feasible `y_k → x`, `y_k ≠ x`, with `f y_k ≤ f x` has unit directions with a cluster
point `z` in the tangent space (`E` is finite-dimensional), and the second-order expansion of the
Lagrangian (`isLittleO_taylor_two`), which equals `f` on feasible points, forces `H z z ≤ 0`. -/
theorem isLocalMin_of_lagrangian_second_order [FiniteDimensional ℝ E] {f : E → ℝ}
    {f' : E → E →L[ℝ] ℝ} {h : ι → E → ℝ} {h' : ι → E → E →L[ℝ] ℝ} {x : E} {l : ι → ℝ}
    {H : E →L[ℝ] E →L[ℝ] ℝ} (hx : x ∈ feasibleEq h) (hf : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y)
    (hh : ∀ i, ∀ᶠ y in 𝓝 x, HasFDerivAt (h i) (h' i y) y)
    (hH : HasFDerivAt (fun y => f' y + ∑ i, l i • h' i y) H x)
    (hstat : f' x + ∑ i, l i • h' i x = 0)
    (hpos : ∀ z, z ≠ 0 → (∀ i, h' i x z = 0) → 0 < H z z) :
    ∃ δ > 0, ∀ y ∈ feasibleEq h, dist y x < δ → y ≠ x → f x < f y := by
  by_contra hcon
  push Not at hcon
  have hseq : ∀ n : ℕ, ∃ y, y ∈ feasibleEq h ∧ dist y x < 1 / ((n : ℝ) + 1) ∧ y ≠ x ∧
      f y ≤ f x := by
    intro n
    obtain ⟨y, hyS, hyd, hyne, hyf⟩ := hcon (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨y, hyS, hyd, hyne, hyf⟩
  choose y hyS hyd hyne hyf using hseq
  have hylim : Tendsto y atTop (𝓝 x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => (hyd n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hwne : ∀ n, y n - x ≠ 0 := fun n => sub_ne_zero.2 (hyne n)
  set u : ℕ → E := fun n => ‖y n - x‖⁻¹ • (y n - x) with hu
  have hunorm : ∀ n, ‖u n‖ = 1 := fun n => by
    rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 (hwne n))]
  obtain ⟨z, hz, φ, hφ, hulim⟩ := (isCompact_sphere (0 : E) 1).tendsto_subseq
    fun n => mem_sphere_zero_iff_norm.2 (hunorm n)
  have hz0 : z ≠ 0 := by
    intro h0
    rw [mem_sphere_zero_iff_norm, h0, norm_zero] at hz
    exact zero_ne_one hz
  have hyφ : Tendsto (y ∘ φ) atTop (𝓝 x) := hylim.comp hφ.tendsto_atTop
  -- the cluster direction lies in the tangent space of the constraints
  have htangent : ∀ i, h' i x z = 0 := by
    intro i
    have hd : HasFDerivAt (h i) (h' i x) x := (hh i).self_of_nhds
    have h1 := (hasFDerivAt_iff_tendsto.1 hd).comp hyφ
    have h2 : ∀ n, ‖y (φ n) - x‖⁻¹ * ‖h i (y (φ n)) - h i x - h' i x (y (φ n) - x)‖
        = ‖h' i x (u (φ n))‖ := by
      intro n
      rw [hyS (φ n) i, hx i, sub_self, zero_sub, norm_neg, hu, map_smul, norm_smul, norm_inv,
        norm_norm]
    have h3 : Tendsto (fun n => ‖h' i x (u (φ n))‖) atTop (𝓝 0) := by
      refine h1.congr fun n => ?_
      exact h2 n
    have h4 : Tendsto (fun n => ‖h' i x (u (φ n))‖) atTop (𝓝 ‖h' i x z‖) :=
      (((h' i x).continuous.tendsto z).comp hulim).norm
    exact norm_eq_zero.1 (tendsto_nhds_unique h4 h3)
  -- the second-order expansion of the Lagrangian along the sequence
  set L : E → ℝ := fun y => lagrangian f h y l with hLdef
  set L' : E → E →L[ℝ] ℝ := fun y => f' y + ∑ i, l i • h' i y with hL'def
  have hL : ∀ᶠ y in 𝓝 x, HasFDerivAt L (L' y) y := by
    filter_upwards [hf, eventually_all.2 hh] with y hfy hhy
    exact lagrangian_hasFDerivAt hfy hhy l
  have hpeano := isLittleO_taylor_two hL hH
  have hL'x : L' x = 0 := hstat
  have hr := (hpeano.tendsto_div_nhds_zero).comp hyφ
  have hkey : ∀ n, H (u (φ n)) (u (φ n)) / 2
      ≤ -((L (y (φ n)) - L x - L' x (y (φ n) - x) - H (y (φ n) - x) (y (φ n) - x) / 2)
          / ‖y (φ n) - x‖ ^ 2) := by
    intro n
    have hLy : L (y (φ n)) = f (y (φ n)) := lagrangian_eq_of_mem (hyS _) l
    have hLx : L x = f x := lagrangian_eq_of_mem hx l
    have hn : ‖y (φ n) - x‖ ≠ 0 := norm_ne_zero_iff.2 (hwne _)
    have hnpos : 0 < ‖y (φ n) - x‖ ^ 2 := pow_pos (norm_pos_iff.2 (hwne _)) 2
    have hHu : H (u (φ n)) (u (φ n)) = H (y (φ n) - x) (y (φ n) - x) / ‖y (φ n) - x‖ ^ 2 := by
      simp only [hu, map_smul, smul_apply, smul_eq_mul]
      field_simp
    rw [hHu, hLy, hLx, hL'x, zero_apply, sub_zero]
    have hd : (f (y (φ n)) - f x) / ‖y (φ n) - x‖ ^ 2 ≤ 0 :=
      div_nonpos_iff.2 (Or.inr ⟨by linarith [hyf (φ n)], hnpos.le⟩)
    have hsplit : -((f (y (φ n)) - f x - H (y (φ n) - x) (y (φ n) - x) / 2) / ‖y (φ n) - x‖ ^ 2)
        = H (y (φ n) - x) (y (φ n) - x) / ‖y (φ n) - x‖ ^ 2 / 2
          - (f (y (φ n)) - f x) / ‖y (φ n) - x‖ ^ 2 := by
      field_simp
      ring
    rw [hsplit]
    linarith
  have hlimL : Tendsto (fun n => H (u (φ n)) (u (φ n)) / 2) atTop (𝓝 (H z z / 2)) := by
    have hcont : Continuous fun v : E => H v v :=
      H.continuous₂.comp (continuous_id.prodMk continuous_id)
    exact ((hcont.tendsto z).comp hulim).div_const 2
  have hlimR : Tendsto (fun n => -((L (y (φ n)) - L x - L' x (y (φ n) - x)
      - H (y (φ n) - x) (y (φ n) - x) / 2) / ‖y (φ n) - x‖ ^ 2)) atTop (𝓝 (-0)) := by
    refine Tendsto.neg ?_
    refine hr.congr fun n => ?_
    simp only [Function.comp_apply]
  rw [neg_zero] at hlimR
  have hle := le_of_tendsto_of_tendsto' hlimL hlimR hkey
  have := hpos z hz0 htangent
  linarith

/-! ### Karush–Kuhn–Tucker points -/

/-- [quarteroni2000numerical] Definition 7.3: a *regular point* of the mixed constraints is a
feasible point at which the equality gradients together with the active inequality gradients are
linearly independent (the linear independence constraint qualification, LICQ). -/
def IsRegularPointIneq (h : ι → E → ℝ) (h' : ι → E → E →L[ℝ] ℝ) (g : κ → E → ℝ)
    (g' : κ → E → E →L[ℝ] ℝ) (x : E) : Prop :=
  (∀ i, h i x = 0) ∧ (∀ j, g j x ≤ 0) ∧
    LinearIndependent ℝ (Sum.elim (fun i => h' i x) fun j : activeSet g x => g' j x)

omit [Fintype ι] [Fintype κ] in
/-- A regular point of the mixed constraints is feasible. -/
theorem IsRegularPointIneq.mem_feasible {h : ι → E → ℝ} {h' : ι → E → E →L[ℝ] ℝ}
    {g : κ → E → ℝ} {g' : κ → E → E →L[ℝ] ℝ} {x : E} (hx : IsRegularPointIneq h h' g g' x) :
    x ∈ feasible h g :=
  ⟨hx.1, hx.2.1⟩

/-- The Karush–Kuhn–Tucker conditions for `min f` subject to `h = 0`, `g ≤ 0`
([quarteroni2000numerical] Property 7.12 and §7.3.1): feasibility, stationarity of the Lagrangian
`ℳ(x, λ, μ) = f + ∑ λ_i h_i + ∑ μ_j g_j` in `x`, nonnegativity of the inequality multipliers and
complementary slackness `μ_j g_j x = 0`. -/
structure IsKKTPoint (f' : E → E →L[ℝ] ℝ) (h : ι → E → ℝ) (h' : ι → E → E →L[ℝ] ℝ)
    (g : κ → E → ℝ) (g' : κ → E → E →L[ℝ] ℝ) (x : E) (l : ι → ℝ) (μ : κ → ℝ) : Prop where
  /-- The equality constraints hold at `x`. -/
  feasible_eq : ∀ i, h i x = 0
  /-- The inequality constraints hold at `x`. -/
  feasible_ineq : ∀ j, g j x ≤ 0
  /-- Stationarity of the Lagrangian in `x`. -/
  stationary : f' x + ∑ i, l i • h' i x + ∑ j, μ j • g' j x = 0
  /-- The inequality multipliers are nonnegative. -/
  nonneg : ∀ j, 0 ≤ μ j
  /-- Complementary slackness. -/
  complementary : ∀ j, μ j * g j x = 0

/-- A Karush–Kuhn–Tucker point is feasible. -/
theorem IsKKTPoint.mem_feasible {f' : E → E →L[ℝ] ℝ} {h : ι → E → ℝ} {h' : ι → E → E →L[ℝ] ℝ}
    {g : κ → E → ℝ} {g' : κ → E → E →L[ℝ] ℝ} {x : E} {l : ι → ℝ} {μ : κ → ℝ}
    (hx : IsKKTPoint f' h h' g g' x l μ) : x ∈ feasible h g :=
  ⟨hx.feasible_eq, hx.feasible_ineq⟩

/-- The multiplier of an inactive constraint vanishes. -/
theorem IsKKTPoint.eq_zero_of_notMem_activeSet {f' : E → E →L[ℝ] ℝ} {h : ι → E → ℝ}
    {h' : ι → E → E →L[ℝ] ℝ} {g : κ → E → ℝ} {g' : κ → E → E →L[ℝ] ℝ} {x : E} {l : ι → ℝ}
    {μ : κ → ℝ} (hx : IsKKTPoint f' h h' g g' x l μ) {j : κ} (hj : j ∉ activeSet g x) :
    μ j = 0 :=
  (mul_eq_zero.1 (hx.complementary j)).resolve_right hj

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι] in
/-- A sum over `κ` of terms that vanish off the active set is a sum over the active set. -/
theorem sum_eq_sum_activeSet {V : Type*} [AddCommMonoid V] {g : κ → E → ℝ} {x : E}
    [Fintype (activeSet g x)] {F : κ → V} (hF : ∀ j, j ∉ activeSet g x → F j = 0) :
    ∑ j, F j = ∑ j : activeSet g x, F j := by
  classical
  rw [← Finset.sum_filter_of_ne (p := fun j => j ∈ activeSet g x)
    (fun j _ hj => by_contra fun hj' => hj (hF j hj'))]
  exact Finset.sum_subtype _ (fun j => by simp) F

/-- Under LICQ the Karush–Kuhn–Tucker multipliers are unique ("only two vectors" in
[quarteroni2000numerical] Property 7.12): complementarity kills the inactive multipliers and the
difference of two stationarity equations is a vanishing combination of the linearly independent
active gradients. -/
theorem kkt_multipliers_unique {f' : E → E →L[ℝ] ℝ} {h : ι → E → ℝ} {h' : ι → E → E →L[ℝ] ℝ}
    {g : κ → E → ℝ} {g' : κ → E → E →L[ℝ] ℝ} {x : E} (hx : IsRegularPointIneq h h' g g' x)
    {l l' : ι → ℝ} {μ μ' : κ → ℝ} (h₁ : IsKKTPoint f' h h' g g' x l μ)
    (h₂ : IsKKTPoint f' h h' g g' x l' μ') : l = l' ∧ μ = μ' := by
  classical
  set c : ι ⊕ activeSet g x → ℝ := Sum.elim (fun i => l i - l' i) fun j => μ j - μ' j with hc
  have hsum : ∑ s, c s • Sum.elim (fun i => h' i x) (fun j : activeSet g x => g' j x) s = 0 := by
    rw [Fintype.sum_sum_type]
    simp only [hc, Sum.elim_inl, Sum.elim_inr]
    rw [← sum_eq_sum_activeSet (F := fun j => (μ j - μ' j) • g' j x)
      (fun j hj => by rw [h₁.eq_zero_of_notMem_activeSet hj, h₂.eq_zero_of_notMem_activeSet hj,
        sub_self, zero_smul])]
    have e := congrArg₂ (· - ·) h₁.stationary h₂.stationary
    simp only [sub_zero] at e
    rw [← e]
    simp only [sub_smul, Finset.sum_sub_distrib]
    abel
  have hzero := coeff_eq_zero_of_sum_smul_eq_zero hx.2.2 hsum
  refine ⟨funext fun i => sub_eq_zero.1 (hzero (Sum.inl i)), funext fun j => ?_⟩
  by_cases hj : j ∈ activeSet g x
  · exact sub_eq_zero.1 (hzero (Sum.inr ⟨j, hj⟩))
  · rw [h₁.eq_zero_of_notMem_activeSet hj, h₂.eq_zero_of_notMem_activeSet hj]

/-! ### The Kuhn–Tucker necessary conditions under LICQ

The route: (a) a family of linearly independent functionals is jointly surjective onto `ℝ^σ`;
(b) a map with surjective strict derivative has, in every direction `z`, a curve `γ` with
`γ 0 = a`, `γ' 0 = z` and `c (γ t) = c a + t c' z` — the implicit function theorem; (c) under
LICQ the linearized cone is contained in the positive tangent cone of the feasible set; (d) the
first-order condition of `IsLocalMinOn.hasFDerivWithinAt_nonneg` on that cone, turned into
multipliers by Farkas' lemma. -/

omit [Fintype ι] [Fintype κ] in
/-- Linearly independent functionals `φ_s`, `s : σ`, are jointly surjective: the map
`v ↦ (φ_s v)_s` has range `ℝ^σ`. This is the dual form of linear independence,
`span_flip_eq_top_iff_linearIndependent`. -/
theorem _root_.LinearIndependent.range_pi_eq_top {σ : Type*} [Finite σ] {φ : σ → E →L[ℝ] ℝ}
    (hφ : LinearIndependent ℝ φ) : (ContinuousLinearMap.pi φ).range = ⊤ := by
  cases nonempty_fintype σ
  have hφ' : LinearIndependent ℝ fun s => ⇑(φ s) := by
    rw [Fintype.linearIndependent_iff] at hφ ⊢
    intro g hg s
    refine hφ g ?_ s
    ext v
    have := congrFun hg v
    simpa [Finset.sum_apply] using this
  have hspan := span_flip_eq_top_iff_linearIndependent.2 hφ'
  have hrange : Set.range (flip fun s => ⇑(φ s))
      = ((ContinuousLinearMap.pi φ).range : Set (σ → ℝ)) := by
    ext w
    simp only [Set.mem_range, SetLike.mem_coe, LinearMap.mem_range]
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨v, by ext s; rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨v, by ext s; rfl⟩
  rw [hrange, Submodule.span_eq] at hspan
  exact hspan

omit [Fintype ι] [Fintype κ] in
/-- The linearizing lemma of the implicit function theorem: if `c : E → F` is strictly
differentiable at `a` with surjective derivative `c'`, `F` finite-dimensional, then for every
direction `z` there is a curve `γ` with `γ 0 = a`, `γ' 0 = z` and `c (γ t) = c a + t c' z` near
`t = 0`. The curve is `t ↦ ψ (c a + t c' z, t P z)` for the inverse `ψ` of `x ↦ (c x, P (x - a))`
provided by `ImplicitFunctionData`, `P` a projection onto `ker c'`; its derivative at `0` is
`(c', P)⁻¹ (c' z, P z) = z`. -/
theorem exists_hasDerivAt_of_hasStrictFDerivAt_of_range_eq_top [CompleteSpace E] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {c : E → F}
    {c' : E →L[ℝ] F} {a : E} (hc : HasStrictFDerivAt c c' a) (hc' : c'.range = ⊤) (z : E) :
    ∃ γ : ℝ → E, γ 0 = a ∧ HasDerivAt γ z 0 ∧ ∀ᶠ t in 𝓝 (0 : ℝ), c (γ t) = c a + t • c' z := by
  have := FiniteDimensional.complete ℝ F
  set φ : ImplicitFunctionData ℝ E F c'.ker :=
    HasStrictFDerivAt.implicitFunctionDataOfComplemented c c' hc hc'
      c'.ker_closedComplemented_of_finiteDimensional_range with hφ
  have hpt : φ.prodFun φ.pt = (c a, 0) := by
    simp [hφ, ImplicitFunctionData.prodFun, HasStrictFDerivAt.implicitFunctionDataOfComplemented]
  set P : E →L[ℝ] c'.ker := φ.rightDeriv with hP
  set ψ : F × c'.ker → E := fun q => φ.toOpenPartialHomeomorph.symm q with hψ
  set p : ℝ → F × c'.ker := fun t => (c a + t • c' z, t • P z) with hp
  have hp0 : p 0 = φ.prodFun φ.pt := by rw [hpt]; simp [hp]
  have hpderiv : HasDerivAt p (c' z, P z) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => c a + t • c' z) (c' z) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (c' z)).const_add (c a)
    have h2 : HasDerivAt (fun t : ℝ => t • P z) (P z) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const (P z)
    exact h1.prodMk h2
  have hψderiv : HasStrictFDerivAt ψ
      ((φ.leftDeriv.equivProdOfSurjectiveOfIsCompl φ.rightDeriv φ.range_leftDeriv
        φ.range_rightDeriv φ.isCompl_ker).symm : F × c'.ker →L[ℝ] E) (φ.prodFun φ.pt) :=
    φ.hasStrictFDerivAt.to_localInverse
  refine ⟨fun t => ψ (p t), ?_, ?_, ?_⟩
  · change ψ (p 0) = a
    rw [hp0]
    exact φ.toOpenPartialHomeomorph.left_inv φ.pt_mem_toOpenPartialHomeomorph_source
  · rw [← hp0] at hψderiv
    have h := hψderiv.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hpderiv
    have hz : (φ.leftDeriv.equivProdOfSurjectiveOfIsCompl φ.rightDeriv φ.range_leftDeriv
        φ.range_rightDeriv φ.isCompl_ker) z = (c' z, P z) := by
      rw [ContinuousLinearMap.equivProdOfSurjectiveOfIsCompl_apply]
      rfl
    rw [← hz, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] at h
    exact h
  · have hlim : Tendsto p (𝓝 0) (𝓝 (φ.prodFun φ.pt)) := by
      rw [← hp0]
      exact hpderiv.continuousAt.tendsto
    filter_upwards [hlim.eventually φ.leftFun_implicitFunction] with t ht
    rw [ImplicitFunctionData.implicitFunction_apply] at ht
    exact ht

omit [Fintype ι] [Fintype κ] in
/-- Under LICQ the linearized cone is contained in the positive tangent cone of the feasible set
(Nocedal–Wright Lemma 12.2): if `x` is a regular point of the mixed constraints, the `h_i` and
`g_j` are strictly differentiable at `x`, and `z` satisfies `h_i' x z = 0` for all `i` and
`g_j' x z ≤ 0` for the active `j`, then `z ∈ posTangentConeAt (feasible h g) x`. The curve of
`exists_hasDerivAt_of_hasStrictFDerivAt_of_range_eq_top` for the active constraints keeps
`h_i = 0`, makes the active `g_j` equal to `t g_j' x z ≤ 0`, and the inactive constraints stay
strict by continuity. -/
theorem mem_posTangentConeAt_of_isRegularPointIneq [FiniteDimensional ℝ E] [Finite ι] [Finite κ]
    {h : ι → E → ℝ}
    {h' : ι → E → E →L[ℝ] ℝ} {g : κ → E → ℝ} {g' : κ → E → E →L[ℝ] ℝ} {x : E}
    (hx : IsRegularPointIneq h h' g g' x) (hh : ∀ i, HasStrictFDerivAt (h i) (h' i x) x)
    (hg : ∀ j, HasStrictFDerivAt (g j) (g' j x) x) {z : E} (hz1 : ∀ i, h' i x z = 0)
    (hz2 : ∀ j ∈ activeSet g x, g' j x z ≤ 0) : z ∈ posTangentConeAt (feasible h g) x := by
  classical
  cases nonempty_fintype ι
  cases nonempty_fintype κ
  have := FiniteDimensional.complete ℝ E
  set cf : ι ⊕ activeSet g x → E → ℝ := Sum.elim h fun j => g j with hcf
  set cf' : ι ⊕ activeSet g x → E →L[ℝ] ℝ := Sum.elim (fun i => h' i x) fun j => g' j x
    with hcf'
  have hc : HasStrictFDerivAt (fun y s => cf s y) (ContinuousLinearMap.pi cf') x := by
    refine hasStrictFDerivAt_pi.2 fun s => ?_
    rcases s with i | j
    · exact hh i
    · exact hg j
  have hc' : (ContinuousLinearMap.pi cf').range = ⊤ := hx.2.2.range_pi_eq_top
  obtain ⟨γ, hγ0, hγ, hγc⟩ := exists_hasDerivAt_of_hasStrictFDerivAt_of_range_eq_top hc hc' z
  have hγcont : Tendsto γ (𝓝 0) (𝓝 x) := by
    have := hγ.continuousAt.tendsto
    rwa [hγ0] at this
  -- feasibility along the curve for small positive `t`
  have hfeas : ∀ᶠ t in 𝓝[>] (0 : ℝ), γ t ∈ feasible h g := by
    have hγc' : ∀ᶠ t in 𝓝[>] (0 : ℝ), (fun s => cf s (γ t))
        = (fun s => cf s x) + t • ContinuousLinearMap.pi cf' z :=
      hγc.filter_mono nhdsWithin_le_nhds
    have hinact : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, j ∉ activeSet g x → g j (γ t) < 0 := by
      refine eventually_all.2 fun j => ?_
      by_cases hj : j ∈ activeSet g x
      · exact Eventually.of_forall fun t hj' => absurd hj hj'
      · have hneg : g j x < 0 := lt_of_le_of_ne (hx.2.1 j) hj
        exact ((((hg j).continuousAt.tendsto.comp hγcont).eventually_lt_const hneg).filter_mono
          nhdsWithin_le_nhds).mono fun t ht _ => ht
    filter_upwards [hγc', hinact, self_mem_nhdsWithin] with t ht hin htpos
    have hval : ∀ s, cf s (γ t) = cf s x + t * cf' s z := fun s => by
      have := congrFun ht s
      simpa [ContinuousLinearMap.pi_apply] using this
    refine ⟨fun i => ?_, fun j => ?_⟩
    · have := hval (Sum.inl i)
      simp only [hcf, hcf', Sum.elim_inl] at this
      rw [this, hx.1 i, hz1 i, mul_zero, add_zero]
    · by_cases hj : j ∈ activeSet g x
      · have := hval (Sum.inr ⟨j, hj⟩)
        simp only [hcf, hcf', Sum.elim_inr] at this
        rw [this, mem_activeSet.1 hj, zero_add]
        exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt htpos) (hz2 j hj)
      · exact (hin j hj).le
  -- membership in the tangent cone through the curve
  have hd0 : Tendsto (fun t => γ t - x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := (hγcont.mono_left (nhdsWithin_le_nhds (s := Ioi 0))).sub_const x
    rwa [sub_self] at this
  refine mem_tangentConeAt_of_seq (𝓝[>] (0 : ℝ)) (fun t => Real.toNNReal t⁻¹) (fun t => γ t - x)
    hd0 (hfeas.mono fun t ht => by simpa using ht) ?_
  have hslope := hγ.tendsto_slope_zero_right
  simp only [zero_add, hγ0] at hslope
  refine hslope.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [NNReal.smul_def, Real.coe_toNNReal _ (inv_nonneg.2 (le_of_lt ht))]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι] in
/-- Multipliers on the active set extended by zero to all of `κ` (`Function.extend` along the
inclusion) sum against `v` as the multipliers themselves do over the active set. -/
theorem sum_extend_activeSet_smul {V : Type*} [AddCommMonoid V] [Module ℝ V] {g : κ → E → ℝ}
    {x : E} [Fintype (activeSet g x)] (c : activeSet g x → ℝ) (v : κ → V) :
    ∑ j, Function.extend Subtype.val c 0 j • v j = ∑ j : activeSet g x, c j • v j := by
  rw [sum_eq_sum_activeSet (F := fun j => Function.extend Subtype.val c 0 j • v j)
    (fun j hj => by
      rw [Function.extend_apply' _ _ _ (by rintro ⟨⟨j', hj'⟩, rfl⟩; exact hj hj'), Pi.zero_apply,
        zero_smul])]
  exact Finset.sum_congr rfl fun j _ => by rw [Subtype.val_injective.extend_apply]

/-- [quarteroni2000numerical] Property 7.12, the Karush–Kuhn–Tucker necessary conditions under
the linear independence constraint qualification (Nocedal–Wright Theorem 12.1): in finite
dimension, if `x` is a regular local minimizer of `f` on the mixed constraints, `f` differentiable
at `x`, the `h_i` and `g_j` strictly differentiable at `x` (as every `C¹` function is,
`ContDiffAt.hasStrictFDerivAt`), then there are multipliers `(λ, μ)` making `x` a
Karush–Kuhn–Tucker point; they are unique by `kkt_multipliers_unique`. Every `z` of the
linearized cone lies in the positive tangent cone of the feasible set
(`mem_posTangentConeAt_of_isRegularPointIneq`), so `f' x z ≥ 0` there
(`IsLocalMinOn.hasFDerivWithinAt_nonneg`); Farkas' lemma (`ConvexAnalysis.farkas`, for the
pairing of `E` with its dual, the coefficient vectors `h_i' x`, `-h_i' x` and the active
`g_j' x`) then writes `-f' x` as a nonnegative combination of them. -/
theorem exists_kkt_of_isLocalMinOn [FiniteDimensional ℝ E] {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {h : ι → E → ℝ} {h' : ι → E → E →L[ℝ] ℝ} {g : κ → E → ℝ} {g' : κ → E → E →L[ℝ] ℝ} {x : E}
    (hx : IsRegularPointIneq h h' g g' x) (hmin : IsLocalMinOn f (feasible h g) x)
    (hf : HasFDerivAt f (f' x) x) (hh : ∀ i, HasStrictFDerivAt (h i) (h' i x) x)
    (hg : ∀ j, HasStrictFDerivAt (g j) (g' j x) x) :
    ∃ (l : ι → ℝ) (μ : κ → ℝ), IsKKTPoint f' h h' g g' x l μ := by
  classical
  -- the first-order condition on the linearized cone
  have hfo : ∀ z, (∀ i, h' i x z = 0) → (∀ j ∈ activeSet g x, g' j x z ≤ 0) → 0 ≤ f' x z :=
    fun z hz1 hz2 => hmin.hasFDerivWithinAt_nonneg hf.hasFDerivWithinAt
      (mem_posTangentConeAt_of_isRegularPointIneq hx hh hg hz1 hz2)
  -- Farkas' lemma for the generators `h_i'`, `-h_i'`, active `g_j'`
  set A : (ι ⊕ ι) ⊕ activeSet g x → StrongDual ℝ E :=
    Sum.elim (Sum.elim (fun i => h' i x) fun i => -h' i x) fun j => g' j x with hA
  have hfarkas := (ConvexAnalysis.farkas (B := (topDualPairing ℝ E).flip) A (-f' x)).1 ?_
  swap
  · intro z hz
    simp only [LinearMap.flip_apply, topDualPairing_apply, hA, Sum.forall, Sum.elim_inl,
      Sum.elim_inr, neg_apply, neg_nonpos] at hz ⊢
    exact hfo z (fun i => le_antisymm (hz.1.1 i) (hz.1.2 i)) fun j hj => hz.2 ⟨j, hj⟩
  obtain ⟨lam, hlam, hsum⟩ := hfarkas
  refine ⟨fun i => lam (Sum.inl (Sum.inl i)) - lam (Sum.inl (Sum.inr i)),
    Function.extend Subtype.val (fun j => lam (Sum.inr j)) 0, hx.1, hx.2.1, ?_, ?_, ?_⟩
  · rw [sum_extend_activeSet_smul]
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at hsum
    simp only [hA, Sum.elim_inl, Sum.elim_inr, smul_neg] at hsum
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [Finset.sum_neg_distrib, ← sub_eq_add_neg] at hsum
    rw [add_assoc, hsum, add_neg_cancel]
  · intro j
    by_cases hj : j ∈ activeSet g x
    · have : j = Subtype.val (⟨j, hj⟩ : activeSet g x) := rfl
      rw [this, Subtype.val_injective.extend_apply]
      exact hlam _
    · rw [Function.extend_apply' _ _ _ (by rintro ⟨⟨j', hj'⟩, rfl⟩; exact hj hj')]
      rfl
  · intro j
    by_cases hj : j ∈ activeSet g x
    · rw [mem_activeSet.1 hj, mul_zero]
    · rw [Function.extend_apply' _ _ _ (by rintro ⟨⟨j', hj'⟩, rfl⟩; exact hj hj'), Pi.zero_apply,
        zero_mul]

/-! ### Sufficiency for convex programs -/

omit [Fintype ι] in
/-- A finite sum of functions convex on `C` is convex on `C`. -/
private theorem convexOn_sum {C : Set E} {φ : κ → E → ℝ} (hC : Convex ℝ C)
    (hφ : ∀ j, ConvexOn ℝ C (φ j)) : ConvexOn ℝ C fun y => ∑ j, φ j y := by
  have h : ConvexOn ℝ C (∑ j, φ j) :=
    Finset.sum_induction φ (ConvexOn ℝ C) (fun _ _ => ConvexOn.add) (convexOn_const 0 hC)
      fun j _ => hφ j
  convert h using 1
  funext y
  simp [Finset.sum_apply]

omit [Fintype ι] in
/-- Sufficiency of the Kuhn–Tucker conditions for a convex program, the engine behind
[quarteroni2000numerical] Property 7.15. Let `C` be convex, `S ⊆ C`, `x ∈ S`, `f` convex on `C`,
and let each `y ↦ μ_j g_j y` be convex on `C` (so `g_j` convex where `μ_j > 0`, concave where
`μ_j < 0`, arbitrary where `μ_j = 0`); suppose `f`, `g_j` differentiable at `x`, the multipliers
sign-compatible with feasibility on `S` (`μ_j g_j y ≤ 0` for `y ∈ S`) and complementary at `x`, and
the variational inequality `0 ≤ f' x (y - x) + ∑ μ_j g_j' x (y - x)` on `C`. Then `x` minimizes
`f` over `S`. The Lagrangian `Λ = f + ∑ μ_j g_j` is convex on `C`, lies above its tangent
functional at `x` (`ConvexOn.add_lineDeriv_le`), equals `f x` at `x` and is at most `f` on `S`.
Equality constraints are the pair `h ≤ 0`, `-h ≤ 0` with free multipliers, `≥`-constraints have
nonpositive multipliers, and stationarity `Λ' x = 0` is the case `C = univ`. -/
theorem isMinOn_of_lagrangian_convexOn {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} {g : κ → E → ℝ}
    {g' : κ → E → E →L[ℝ] ℝ} {μ : κ → ℝ} {C S : Set E} {x : E}
    (hSC : S ⊆ C) (hx : x ∈ S) (hf : ConvexOn ℝ C f) (hg : ∀ j, ConvexOn ℝ C fun y => μ j * g j y)
    (hf' : HasFDerivAt f (f' x) x) (hg' : ∀ j, HasFDerivAt (g j) (g' j x) x)
    (hsign : ∀ y ∈ S, ∀ j, μ j * g j y ≤ 0) (hcomp : ∀ j, μ j * g j x = 0)
    (hvi : ∀ y ∈ C, 0 ≤ f' x (y - x) + ∑ j, μ j * g' j x (y - x)) :
    IsMinOn f S x := by
  set Λ : E → ℝ := fun y => f y + ∑ j, μ j * g j y with hΛ
  have hΛconv : ConvexOn ℝ C Λ := hf.add (convexOn_sum hf.1 hg)
  have hΛ' : HasFDerivAt Λ (f' x + ∑ j, μ j • g' j x) x :=
    hf'.add (HasFDerivAt.fun_sum (u := Finset.univ) fun j _ => (hg' j).const_mul (μ j))
  have hΛx : Λ x = f x := by
    simp only [hΛ, hcomp, Finset.sum_const_zero, add_zero]
  intro y hy
  have htan := hΛconv.add_lineDeriv_le (hSC hx) (hSC hy) fun v => hΛ'.hasLineDerivAt v
  have hvi' := hvi y (hSC hy)
  simp only [add_apply, sum_apply, smul_apply, smul_eq_mul] at htan
  have hle : Λ y ≤ f y := by
    simp only [hΛ]
    have : ∑ j, μ j * g j y ≤ 0 := Finset.sum_nonpos fun j _ => hsign y hy j
    linarith
  simp only [Set.mem_ofPred_eq]
  linarith

/-! ### The convex case under Slater's condition -/

section Slater

variable [FiniteDimensional ℝ E]

omit [Fintype ι] [Fintype κ] in
/-- The derivative of an affine functional on a finite-dimensional space is its linear part. -/
theorem _root_.AffineMap.hasFDerivAt_of_finiteDimensional (a : E →ᵃ[ℝ] ℝ) (x : E) :
    HasFDerivAt a (LinearMap.toContinuousLinearMap a.linear) x := by
  have h := (LinearMap.toContinuousLinearMap a.linear).hasFDerivAt (x := x) |>.add_const (a 0)
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  have hy := congrFun (AffineMap.decomp a) y
  simp only [Pi.add_apply] at hy
  simpa using hy

/-- The Kuhn–Tucker conditions for a differentiable convex program under Slater's condition — the
constraint qualification [quarteroni2000numerical] allude to after Property 7.14, in the convex
case with Slater's condition in place of LICQ. In finite dimension let `f` and the inequality
constraints `g_j` be convex on the whole space and differentiable at `x`, the equality constraints
affine, `a i : E →ᵃ[ℝ] ℝ`; let Slater's condition hold, `∃ y, (∀ i, a i y = 0) ∧ ∀ j, g j y < 0`;
and let `x` minimize `f` on the feasible set (for a convex program a local minimizer is a global
one).
Then `x` is a Karush–Kuhn–Tucker point with the equality gradients `(a i).linear`. No regularity
of the constraint gradients is assumed, and the multipliers need not be unique. The multipliers
come from `ConvexAnalysis.exists_multipliers_of_slater_eq` ([rockafellar1970convex] Theorem 28.2),
with the objective and the constraints read in `EReal`: the infimum of the Lagrangian
`f + ∑ μ_j g_j + ∑ λ_i a_i` over `E` is `f x`, so `x` is an unconstrained minimizer of the
Lagrangian, whose derivative therefore vanishes at `x`, and complementary slackness follows from
`∑ μ_j g_j x = 0` with nonpositive terms. -/
theorem exists_kkt_of_convexOn_of_slater {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} {a : ι → E →ᵃ[ℝ] ℝ}
    {g : κ → E → ℝ} {g' : κ → E → E →L[ℝ] ℝ} {x : E} (hf : ConvexOn ℝ univ f)
    (hg : ∀ j, ConvexOn ℝ univ (g j)) (hf' : HasFDerivAt f (f' x) x)
    (hg' : ∀ j, HasFDerivAt (g j) (g' j x) x) (hslater : ∃ y, (∀ i, a i y = 0) ∧ ∀ j, g j y < 0)
    (hx : x ∈ feasible (fun i => a i) g) (hmin : IsMinOn f (feasible (fun i => a i) g) x) :
    ∃ (l : ι → ℝ) (μ : κ → ℝ),
      IsKKTPoint f' (fun i => a i) (fun i _ => LinearMap.toContinuousLinearMap (a i).linear) g g'
        x l μ := by
  classical
  set f₀ : E → EReal := fun y => (f y : EReal) with hf₀
  set G : κ → E → EReal := fun j y => (g j y : EReal) with hG
  set b : ι ⊕ ι → E →ᵃ[ℝ] ℝ := Sum.elim a fun k => -(a k) with hb
  have hfeas : ConvexAnalysis.feasibleSet G b = feasible (fun i => a i) g := by
    ext y
    simp only [ConvexAnalysis.mem_feasibleSet, mem_feasible, hG, hb, EReal.coe_nonpos,
      Sum.forall, Sum.elim_inl, Sum.elim_inr, AffineMap.coe_neg, Pi.neg_apply, neg_nonpos]
    constructor
    · rintro ⟨hg0, ha1, ha2⟩
      exact ⟨fun i => le_antisymm (ha1 i) (ha2 i), hg0⟩
    · rintro ⟨ha, hg0⟩
      exact ⟨hg0, fun i => (ha i).le, fun i => (ha i).ge⟩
  have hopt : ConvexAnalysis.optimalValue f₀ G b = (f x : EReal) := by
    rw [ConvexAnalysis.optimalValue, hfeas]
    exact le_antisymm (iInf₂_le x hx)
      (le_iInf₂ fun y hy => EReal.coe_le_coe_iff.2 (hmin hy))
  have hdom : ConvexAnalysis.dom f₀ = univ := by
    ext y; simp [hf₀]
  obtain ⟨z, hza, hzg⟩ := hslater
  obtain ⟨μ, l, hμ, hinf⟩ := ConvexAnalysis.exists_multipliers_of_slater_eq (f₀ := f₀) (f := G)
    (a := a) hf.convexFn_coe ⟨⟨x, by simp [hf₀]⟩, fun _ => EReal.coe_ne_bot _⟩
    (fun j => (hg j).convexFn_coe)
    (fun j => ⟨⟨x, by simp [hG]⟩, fun _ => EReal.coe_ne_bot _⟩)
    (fun j y _ => by simp [hG]) (by rw [hopt]; exact EReal.coe_ne_bot _)
    ⟨z, by rw [hdom, ConvexAnalysis.intrinsicInterior_univ]; trivial,
      fun j => EReal.coe_neg'.2 (hzg j), hza⟩
  -- the Lagrangian, as a real function
  set Λ : E → ℝ := fun y => f y + ∑ j, μ j * g j y + ∑ i, l i * a i y with hΛ
  have hΛcoe : ∀ y, f₀ y + (∑ j, (μ j : EReal) * G j y) + ((∑ i, l i * a i y : ℝ) : EReal)
      = (Λ y : EReal) := by
    intro y
    simp only [hΛ, hf₀, hG, EReal.coe_add, EReal.coe_sum, EReal.coe_mul]
  have hrhs : (⨅ y ∈ {y | (∀ j, G j y ≤ 0) ∧ ∀ i, a i y = 0}, f₀ y) = (f x : EReal) := by
    have hset : {y | (∀ j, G j y ≤ 0) ∧ ∀ i, a i y = 0} = feasible (fun i => a i) g := by
      ext y
      simp only [Set.mem_ofPred_eq, mem_feasible, hG, EReal.coe_nonpos]
      exact and_comm
    rw [hset]
    exact le_antisymm (iInf₂_le x hx) (le_iInf₂ fun y hy => EReal.coe_le_coe_iff.2 (hmin hy))
  rw [hrhs, iInf_congr hΛcoe] at hinf
  have hΛge : ∀ y, f x ≤ Λ y := fun y => EReal.coe_le_coe_iff.1 (hinf ▸ iInf_le _ y)
  have hax : ∀ i, a i x = 0 := hx.1
  have hgx : ∀ j, g j x ≤ 0 := hx.2
  have hsum_nonpos : ∑ j, μ j * g j x ≤ 0 :=
    Finset.sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (hμ j) (hgx j)
  have hΛx : Λ x = f x + ∑ j, μ j * g j x := by
    simp only [hΛ, hax, mul_zero, Finset.sum_const_zero, add_zero]
  have hsum_zero : ∑ j, μ j * g j x = 0 := by
    have := hΛge x
    rw [hΛx] at this
    linarith
  have hcomp : ∀ j, μ j * g j x = 0 := fun j =>
    (Finset.sum_eq_zero_iff_of_nonpos fun j _ =>
      mul_nonpos_of_nonneg_of_nonpos (hμ j) (hgx j)).1 hsum_zero j (Finset.mem_univ j)
  have hΛmin : IsLocalMin Λ x := by
    refine Filter.Eventually.of_forall fun y => ?_
    rw [hΛx, hsum_zero, add_zero]
    exact hΛge y
  have hΛ' : HasFDerivAt Λ (f' x + ∑ j, μ j • g' j x
      + ∑ i, l i • LinearMap.toContinuousLinearMap (a i).linear) x :=
    (hf'.add (HasFDerivAt.fun_sum (u := Finset.univ) fun j _ => (hg' j).const_mul (μ j))).add
      (HasFDerivAt.fun_sum (u := Finset.univ) fun i _ =>
        ((a i).hasFDerivAt_of_finiteDimensional x).const_mul (l i))
  have hstat := hΛmin.hasFDerivAt_eq_zero hΛ'
  refine ⟨l, μ, hax, hgx, ?_, hμ, hcomp⟩
  rw [← hstat]
  abel

end Slater

/-! ### The penalty method and the method of multipliers -/

section Penalty

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The penalized Lagrangian `ℒ_α(x) = f x + ½ α ‖h x‖²` ([quarteroni2000numerical] (7.53)). -/
noncomputable def penalized (f : E → ℝ) (h : E → F) (α : ℝ) (x : E) : ℝ :=
  f x + 1 / 2 * α * ‖h x‖ ^ 2

/-- The augmented Lagrangian `𝒢_α(x, λ) = f x + ⟪λ, h x⟫ + ½ α ‖h x‖²`
([quarteroni2000numerical] (7.55)). -/
noncomputable def augmented (f : E → ℝ) (h : E → F) (α : ℝ) (l : F) (x : E) : ℝ :=
  f x + inner ℝ l (h x) + 1 / 2 * α * ‖h x‖ ^ 2

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- With the zero multiplier the augmented Lagrangian is the penalized one. -/
@[simp] theorem augmented_zero (f : E → ℝ) (h : E → F) (α : ℝ) :
    augmented f h α 0 = penalized f h α := by
  funext x; simp [augmented, penalized]

omit [NormedSpace ℝ E] [InnerProductSpace ℝ F] [Fintype ι] [Fintype κ] in
/-- The common core of the convergence theorems for the penalty method and the method of
multipliers: if the iterates `x_k ∈ Ω` satisfy `f x_k + ½ α_k ‖h x_k‖² - Λ ‖h x_k‖ ≤ f x*` with
`α_k → ∞`, then every cluster point `x̄` of `x_k` lies in `Ω`, satisfies the constraint and has
`f x̄ ≤ f x*`. Along a subsequence converging to `x̄` the objective converges, so the penalty term
is bounded and forces `h x̄ = 0`. -/
theorem mem_and_eq_zero_and_le_of_clusterPt {f : E → ℝ} {h : E → F} {Ω : Set E}
    (hΩ : IsClosed Ω) (hf : ContinuousOn f Ω) (hh : ContinuousOn h Ω) {α : ℕ → ℝ}
    (hdiv : Tendsto α atTop atTop) {Λ : ℝ} (hΛ : 0 ≤ Λ) {fstar : ℝ} {xk : ℕ → E}
    (hxk : ∀ k, xk k ∈ Ω)
    (hle : ∀ k, f (xk k) + α k / 2 * ‖h (xk k)‖ ^ 2 - Λ * ‖h (xk k)‖ ≤ fstar) {xbar : E}
    (hcl : MapClusterPt xbar atTop xk) : xbar ∈ Ω ∧ h xbar = 0 ∧ f xbar ≤ fstar := by
  obtain ⟨φ, hφ, hlim⟩ := hcl.tendsto_subseq
  have hmem : xbar ∈ Ω := hΩ.mem_of_tendsto hlim (Eventually.of_forall fun n => hxk _)
  have hlimΩ : Tendsto (xk ∘ φ) atTop (𝓝[Ω] xbar) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n => hxk _⟩
  have hflim : Tendsto (fun n => f (xk (φ n))) atTop (𝓝 (f xbar)) :=
    (hf xbar hmem).tendsto.comp hlimΩ
  have hhlim : Tendsto (fun n => ‖h (xk (φ n))‖) atTop (𝓝 ‖h xbar‖) :=
    ((hh xbar hmem).tendsto.comp hlimΩ).norm
  have hαlim : Tendsto (fun n => α (φ n)) atTop atTop := hdiv.comp hφ.tendsto_atTop
  have hzero : h xbar = 0 := by
    by_contra hne
    have hc : 0 < ‖h xbar‖ := norm_pos_iff.2 hne
    have h1 : ∀ᶠ n in atTop, ‖h xbar‖ / 2 < ‖h (xk (φ n))‖ :=
      hhlim.eventually_const_lt (by linarith)
    have h2 : ∀ᶠ n in atTop, ‖h (xk (φ n))‖ < ‖h xbar‖ + 1 :=
      hhlim.eventually_lt_const (by linarith)
    have h3 : ∀ᶠ n in atTop, f xbar - 1 < f (xk (φ n)) :=
      hflim.eventually_const_lt (by linarith)
    have h4 : ∀ᶠ n in atTop,
        max 0 (fstar - (f xbar - 1) + Λ * (‖h xbar‖ + 1)) / ((‖h xbar‖ / 2) ^ 2 / 2) < α (φ n) :=
      hαlim.eventually_gt_atTop _
    obtain ⟨n, hn1, hn2, hn3, hn4⟩ := (h1.and (h2.and (h3.and h4))).exists
    have hq : (0 : ℝ) < (‖h xbar‖ / 2) ^ 2 / 2 := by positivity
    rw [div_lt_iff₀ hq] at hn4
    have hmax := le_max_right 0 (fstar - (f xbar - 1) + Λ * (‖h xbar‖ + 1))
    have hmax0 := le_max_left 0 (fstar - (f xbar - 1) + Λ * (‖h xbar‖ + 1))
    have h5 : (‖h xbar‖ / 2) ^ 2 ≤ ‖h (xk (φ n))‖ ^ 2 := by
      have : 0 ≤ ‖h xbar‖ / 2 := by positivity
      nlinarith
    have h6 : Λ * ‖h (xk (φ n))‖ ≤ Λ * (‖h xbar‖ + 1) :=
      mul_le_mul_of_nonneg_left hn2.le hΛ
    have h7 : α (φ n) / 2 * (‖h xbar‖ / 2) ^ 2 ≤ α (φ n) / 2 * ‖h (xk (φ n))‖ ^ 2 := by
      have hαpos : 0 ≤ α (φ n) := by nlinarith [hn4, hq]
      exact mul_le_mul_of_nonneg_left h5 (by linarith)
    have := hle (φ n)
    nlinarith
  refine ⟨hmem, hzero, ?_⟩
  have hbound : ∀ᶠ n in atTop, f (xk (φ n)) ≤ fstar + Λ * ‖h (xk (φ n))‖ := by
    refine (hαlim.eventually_ge_atTop 0).mono fun n hα => ?_
    have := hle (φ n)
    nlinarith [mul_nonneg hα (sq_nonneg ‖h (xk (φ n))‖)]
  have hlimr : Tendsto (fun n => fstar + Λ * ‖h (xk (φ n))‖) atTop (𝓝 (fstar + Λ * ‖h xbar‖)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul hhlim)
  rw [hzero, norm_zero, mul_zero, add_zero] at hlimr
  exact le_of_tendsto_of_tendsto hflim hlimr hbound

omit [NormedSpace ℝ E] [InnerProductSpace ℝ F] [Fintype ι] [Fintype κ] in
/-- [quarteroni2000numerical] Property 7.16, corrected to what is true (Luenberger–Ye,
*Linear and Nonlinear Programming*, Theorem 13.1; Bertsekas Proposition 4.2.1): every cluster
point of the sequence of global minimizers of the penalized problems is a global minimizer of the
constrained problem. Let `Ω` be closed, `f` and `h` continuous on `Ω`, `α_k → ∞`, `x*` a
constrained global minimizer, and `x_k ∈ Ω` a global minimizer of `ℒ_{α_k}` on `Ω`; then every
cluster point `x̄` of `x_k` lies in `Ω`, satisfies `h x̄ = 0` and minimizes `f` on the constraint
set. From `ℒ_{α_k}(x_k) ≤ ℒ_{α_k}(x*) = f x*`, along a subsequence converging to `x̄` the objective
converges, so `½ α_k ‖h x_k‖²` is bounded and `h x̄ = 0`, and `f x̄ ≤ f x*`. Neither the
monotonicity nor the positivity of the `α_k` the book assumes is needed, only the divergence. The
book's "the sequence converges to `x*`" needs a unique constrained minimizer and a bounded
sequence: `tendsto_penalty_of_unique`. -/
theorem penalty_clusterPt {f : E → ℝ} {h : E → F} {Ω : Set E} (hΩ : IsClosed Ω)
    (hf : ContinuousOn f Ω) (hh : ContinuousOn h Ω) {α : ℕ → ℝ} (hdiv : Tendsto α atTop atTop)
    {xstar : E} (hstar : xstar ∈ Ω ∧ h xstar = 0) (hmin : IsMinOn f {y ∈ Ω | h y = 0} xstar)
    {xk : ℕ → E} (hxk : ∀ k, xk k ∈ Ω) (hxmin : ∀ k, IsMinOn (penalized f h (α k)) Ω (xk k))
    {xbar : E} (hcl : MapClusterPt xbar atTop xk) :
    xbar ∈ Ω ∧ h xbar = 0 ∧ IsMinOn f {y ∈ Ω | h y = 0} xbar := by
  have hle : ∀ k, f (xk k) + α k / 2 * ‖h (xk k)‖ ^ 2 - 0 * ‖h (xk k)‖ ≤ f xstar := by
    intro k
    have := hxmin k hstar.1
    simp only [penalized, hstar.2, norm_zero, Set.mem_ofPred_eq] at this
    linarith
  obtain ⟨hmem, hzero, hfle⟩ :=
    mem_and_eq_zero_and_le_of_clusterPt hΩ hf hh hdiv le_rfl hxk hle hcl
  exact ⟨hmem, hzero, fun y hy => le_trans hfle (hmin hy)⟩

omit [NormedSpace ℝ E] [InnerProductSpace ℝ F] [Fintype ι] [Fintype κ] in
/-- The convergent form of [quarteroni2000numerical] Property 7.16: under the hypotheses of
`penalty_clusterPt`, in a proper space, if the sequence of penalty minimizers is bounded and the
constrained problem has the unique global minimizer `x*`, then `x_k → x*`. Every subsequence
outside a neighbourhood of `x*` would have a cluster point, which is a constrained minimizer
(`penalty_clusterPt`), hence `x*` itself. -/
theorem tendsto_penalty_of_unique [ProperSpace E] {f : E → ℝ} {h : E → F} {Ω : Set E}
    (hΩ : IsClosed Ω) (hf : ContinuousOn f Ω) (hh : ContinuousOn h Ω) {α : ℕ → ℝ}
    (hdiv : Tendsto α atTop atTop) {xstar : E} (hstar : xstar ∈ Ω ∧ h xstar = 0)
    (hmin : IsMinOn f {y ∈ Ω | h y = 0} xstar)
    (huniq : ∀ y ∈ Ω, h y = 0 → IsMinOn f {y ∈ Ω | h y = 0} y → y = xstar) {xk : ℕ → E}
    (hxk : ∀ k, xk k ∈ Ω) (hxmin : ∀ k, IsMinOn (penalized f h (α k)) Ω (xk k))
    (hbdd : Bornology.IsBounded (Set.range xk)) : Tendsto xk atTop (𝓝 xstar) := by
  rw [tendsto_nhds]
  by_contra hnot
  push Not at hnot
  obtain ⟨U, hU, hxU, hfreq⟩ := hnot
  have hfreq : ∃ᶠ k in atTop, xk k ∉ U := by
    rw [Filter.Frequently]
    exact fun h => hfreq (h.mono fun k hk => not_not.1 hk)
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hbdd
  have hK : IsCompact (Metric.closedBall (0 : E) R ∩ Uᶜ) :=
    (isCompact_closedBall 0 R).inter_right hU.isClosed_compl
  have hfreq' : ∃ᶠ k in atTop, xk k ∈ Metric.closedBall (0 : E) R ∩ Uᶜ :=
    hfreq.mono fun k hk => ⟨hR ⟨k, rfl⟩, hk⟩
  obtain ⟨a, ha, φ, hφ, hlim⟩ := hK.tendsto_subseq' hfreq'
  have hcl : MapClusterPt a atTop xk := MapClusterPt.of_comp hφ.tendsto_atTop hlim.mapClusterPt
  obtain ⟨hmem, hzero, hamin⟩ := penalty_clusterPt hΩ hf hh hdiv hstar hmin hxk hxmin hcl
  exact ha.2 (huniq a hmem hzero hamin ▸ hxU)

omit [NormedSpace ℝ E] [Fintype ι] [Fintype κ] in
/-- [quarteroni2000numerical] Property 7.16 for the method of multipliers ((7.56), as the book
asserts after (7.56)): with the hypotheses of `penalty_clusterPt`, a bounded multiplier sequence
`‖λ_k‖ ≤ Λ` and `x_k` a global minimizer of the augmented Lagrangian `𝒢_{α_k}(·, λ_k)` on `Ω`,
every cluster point of `x_k` is a constrained global minimizer. The inequality
`𝒢_{α_k}(x_k, λ_k) ≤ 𝒢_{α_k}(x*, λ_k) = f x*` and Cauchy–Schwarz give
`f x_k + ½ α_k ‖h x_k‖² - Λ ‖h x_k‖ ≤ f x*`, and the argument of `penalty_clusterPt` applies. -/
theorem augmented_clusterPt {f : E → ℝ} {h : E → F} {Ω : Set E} (hΩ : IsClosed Ω)
    (hf : ContinuousOn f Ω) (hh : ContinuousOn h Ω) {α : ℕ → ℝ} (hdiv : Tendsto α atTop atTop)
    {xstar : E} (hstar : xstar ∈ Ω ∧ h xstar = 0) (hmin : IsMinOn f {y ∈ Ω | h y = 0} xstar)
    {l : ℕ → F} {Λ : ℝ} (hl : ∀ k, ‖l k‖ ≤ Λ) {xk : ℕ → E} (hxk : ∀ k, xk k ∈ Ω)
    (hxmin : ∀ k, IsMinOn (augmented f h (α k) (l k)) Ω (xk k)) {xbar : E}
    (hcl : MapClusterPt xbar atTop xk) :
    xbar ∈ Ω ∧ h xbar = 0 ∧ IsMinOn f {y ∈ Ω | h y = 0} xbar := by
  have hΛ : 0 ≤ Λ := le_trans (norm_nonneg _) (hl 0)
  have hle : ∀ k, f (xk k) + α k / 2 * ‖h (xk k)‖ ^ 2 - Λ * ‖h (xk k)‖ ≤ f xstar := by
    intro k
    have h1 := hxmin k hstar.1
    simp only [augmented, hstar.2, norm_zero, inner_zero_right, Set.mem_ofPred_eq] at h1
    have h2 : -(‖l k‖ * ‖h (xk k)‖) ≤ inner ℝ (l k) (h (xk k)) :=
      neg_le_of_abs_le (abs_real_inner_le_norm _ _)
    have h3 : ‖l k‖ * ‖h (xk k)‖ ≤ Λ * ‖h (xk k)‖ :=
      mul_le_mul_of_nonneg_right (hl k) (norm_nonneg _)
    linarith
  obtain ⟨hmem, hzero, hfle⟩ :=
    mem_and_eq_zero_and_le_of_clusterPt hΩ hf hh hdiv hΛ hxk hle hcl
  exact ⟨hmem, hzero, fun y hy => le_trans hfle (hmin hy)⟩

end Penalty

/-! ### Debreu's lemma -/

section Debreu

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Debreu's lemma** (Bertsekas, *Constrained Optimization and Lagrange Multiplier Methods*,
Lemma 1.25; Finsler 1937, Debreu 1952): on a finite-dimensional space, if a continuous bilinear
form `H` is positive on the nonzero kernel vectors of a continuous linear map `A`, `H z z > 0`
for `z ≠ 0` with `A z = 0`, then `H + α ‖A ·‖²` is positive definite for every large `α`: there
is `α₀` with `H z z + α ‖A z‖² > 0` for all `α ≥ α₀` and `z ≠ 0`.

By compactness of the unit sphere: otherwise there are `α_k ≥ k` and unit vectors `u_k` with
`H u_k u_k + α_k ‖A u_k‖² ≤ 0`, so `‖A u_k‖² ≤ ‖H‖ / k → 0` and `H u_k u_k ≤ 0`; a cluster point
`w` of `u_k` is a unit vector with `A w = 0` and `H w w ≤ 0`. -/
theorem exists_forall_pos_add_mul_sq_norm_of_pos_on_ker [FiniteDimensional ℝ E]
    (H : E →L[ℝ] E →L[ℝ] ℝ) (A : E →L[ℝ] F) (hpos : ∀ z, z ≠ 0 → A z = 0 → 0 < H z z) :
    ∃ α₀ : ℝ, ∀ α, α₀ ≤ α → ∀ z, z ≠ 0 → 0 < H z z + α * ‖A z‖ ^ 2 := by
  by_contra hcon
  push Not at hcon
  choose α hα z hz0 hz using fun k : ℕ => hcon k
  -- normalize to the unit sphere
  set u : ℕ → E := fun k => ‖z k‖⁻¹ • z k with hu
  have hunorm : ∀ k, ‖u k‖ = 1 := fun k => by
    rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 (hz0 k))]
  have hineq : ∀ k, H (u k) (u k) + α k * ‖A (u k)‖ ^ 2 ≤ 0 := fun k => by
    have hzn : 0 < ‖z k‖ := norm_pos_iff.2 (hz0 k)
    have h1 : H (u k) (u k) = ‖z k‖⁻¹ ^ 2 * H (z k) (z k) := by
      simp only [hu, map_smul, smul_apply, smul_eq_mul]
      ring
    have h2 : ‖A (u k)‖ ^ 2 = ‖z k‖⁻¹ ^ 2 * ‖A (z k)‖ ^ 2 := by
      rw [hu, map_smul, norm_smul, norm_inv, norm_norm, mul_pow]
    rw [h1, h2]
    have := hz k
    have hc : 0 ≤ ‖z k‖⁻¹ ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this hc]
  have hαk : ∀ k : ℕ, (k : ℝ) ≤ α k := hα
  have hα0 : ∀ k : ℕ, 0 ≤ α k := fun k => (Nat.cast_nonneg k).trans (hαk k)
  have hHle : ∀ k : ℕ, H (u k) (u k) ≤ 0 := fun k => by
    have := hineq k
    have : 0 ≤ α k * ‖A (u k)‖ ^ 2 := mul_nonneg (hα0 k) (by positivity)
    linarith
  have hAle : ∀ k : ℕ, (k : ℝ) * ‖A (u k)‖ ^ 2 ≤ ‖H‖ := fun k => by
    have h1 : ‖H (u k) (u k)‖ ≤ ‖H‖ * ‖u k‖ * ‖u k‖ := H.le_opNorm₂ (u k) (u k)
    rw [hunorm, mul_one, mul_one, Real.norm_eq_abs] at h1
    have h2 : -H (u k) (u k) ≤ ‖H‖ := by linarith [neg_abs_le (H (u k) (u k))]
    have h3 : (k : ℝ) * ‖A (u k)‖ ^ 2 ≤ α k * ‖A (u k)‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (hαk k) (by positivity)
    linarith [hineq k]
  -- a cluster point of the unit vectors
  obtain ⟨w, hw, φ, hφ, hlim⟩ := (isCompact_sphere (0 : E) 1).tendsto_subseq
    fun k => mem_sphere_zero_iff_norm.2 (hunorm k)
  have hw0 : w ≠ 0 := by
    intro h0
    rw [mem_sphere_zero_iff_norm, h0, norm_zero] at hw
    exact zero_ne_one hw
  -- `A w = 0`
  have hAw : A w = 0 := by
    have h1 : Tendsto (fun k => ‖A (u (φ k))‖ ^ 2) atTop (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun k => by positivity) ?_
        ((tendsto_const_div_atTop_nhds_zero_nat ‖H‖).comp hφ.tendsto_atTop)
      filter_upwards [eventually_ge_atTop 1] with k hk
      have hφk : (1 : ℝ) ≤ φ k := by exact_mod_cast hk.trans (hφ.id_le k)
      rw [Function.comp_apply, le_div_iff₀ (by linarith)]
      linarith [hAle (φ k)]
    have h2 : Tendsto (fun k => ‖A (u (φ k))‖) atTop (𝓝 0) := by
      have := h1.sqrt
      rw [Real.sqrt_zero] at this
      exact this.congr fun k => Real.sqrt_sq (norm_nonneg _)
    have h3 : Tendsto (fun k => A (u (φ k))) atTop (𝓝 (A w)) :=
      (A.continuous.tendsto w).comp hlim
    exact tendsto_nhds_unique h3 (tendsto_zero_iff_norm_tendsto_zero.2 h2)
  -- `H w w ≤ 0`
  have hHw : H w w ≤ 0 := by
    have hcont : Continuous fun v : E => H v v :=
      H.continuous₂.comp (continuous_id.prodMk continuous_id)
    have h1 : Tendsto (fun k => H (u (φ k)) (u (φ k))) atTop (𝓝 (H w w)) :=
      (hcont.tendsto w).comp hlim
    exact le_of_tendsto' h1 fun k => hHle (φ k)
  exact absurd (hpos w hw0 hAw) (not_lt.2 hHw)

end Debreu

/-! ### The Hessian of the augmented Lagrangian at a feasible point -/

section AugmentedHessian

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The second derivative of `y ↦ ‖h y‖²` at a zero of `h`: for `h` of class `C²` at `x` with
`h x = 0`, `(‖h ·‖²)''(x) v v = 2 ‖h'(x) v‖²`. The first derivative is
`y ↦ 2 ⟪h y, h'(y) ·⟫`, whose derivative at `x` is `2 ⟪h'(x) ·, h'(x) ·⟫ + 2 ⟪h x, h''(x) · ·⟫`,
and the second term vanishes. -/
theorem fderiv_fderiv_norm_sq_apply {h : E → F} {x : E} (hx : h x = 0)
    (hh : ContDiffAt ℝ 2 h x) (v : E) :
    fderiv ℝ (fderiv ℝ fun y => ‖h y‖ ^ 2) x v v = 2 * ‖fderiv ℝ h x v‖ ^ 2 := by
  set g : E → ℝ := fun y => ‖h y‖ ^ 2 with hgdef
  have hg : ContDiffAt ℝ 2 g x := ContDiffAt.norm_sq ℝ hh
  have hgd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero
  -- reduce to the scalar function `y ↦ g'(y) v`
  have e1 : fderiv ℝ (fderiv ℝ g) x v v = fderiv ℝ (fun y => fderiv ℝ g y v) x v := by
    rw [fderiv_clm_apply hgd (differentiableAt_const v)]
    simp
  have hd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ h y := by
    filter_upwards [hh.eventually (by simp)] with y hy
    exact hy.differentiableAt (by simp)
  have e2 : (fun y => fderiv ℝ g y v) =ᶠ[𝓝 x] fun y => 2 * inner ℝ (h y) (fderiv ℝ h y v) := by
    filter_upwards [hd] with y hy
    rw [hgdef, (HasFDerivAt.norm_sq hy.hasFDerivAt).fderiv]
    simp
  rw [e1, e2.fderiv_eq]
  -- differentiate `y ↦ 2 ⟪h y, h'(y) v⟫` at `x`
  have hh' : HasFDerivAt (fderiv ℝ h) (fderiv ℝ (fderiv ℝ h) x) x :=
    ((hh.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero).hasFDerivAt
  have hhv := hh'.clm_apply (hasFDerivAt_const v x)
  have hin := (hd.self_of_nhds.hasFDerivAt.inner ℝ hhv).const_mul (2 : ℝ)
  rw [hin.fderiv]
  simp [fderivInnerCLM_apply, hx]

/-- **The Hessian of the augmented Lagrangian at a feasible point**: for `f`, `h` of class `C²`
at `x` with `h x = 0`, the second derivative of `𝒢_α(·, λ) = f + ⟪λ, h ·⟫ + ½ α ‖h ·‖²` is that
of the Lagrangian `𝒢_0(·, λ)` plus `α ‖h'(x) ·‖²`:

`𝒢_α''(x) v v = 𝒢_0''(x) v v + α ‖h'(x) v‖²`,

the matrix identity `H_{𝒢_α}(x, λ) = H_ℒ(x, λ) + α J_h(x)ᵀ J_h(x)` of Bertsekas, *Constrained
Optimization and Lagrange Multiplier Methods*, §2.2. -/
theorem fderiv_fderiv_augmented_apply {f : E → ℝ} {h : E → F} {x : E} (hx : h x = 0)
    (hf : ContDiffAt ℝ 2 f x) (hh : ContDiffAt ℝ 2 h x) (α : ℝ) (l : F) (v : E) :
    fderiv ℝ (fderiv ℝ (augmented f h α l)) x v v
      = fderiv ℝ (fderiv ℝ (augmented f h 0 l)) x v v + α * ‖fderiv ℝ h x v‖ ^ 2 := by
  have hsplit : augmented f h α l = augmented f h 0 l + (1 / 2 * α) • fun y => ‖h y‖ ^ 2 := by
    funext y
    simp only [augmented, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  -- `C²` of the pieces
  have hG : ContDiffAt ℝ 2 (augmented f h 0 l) x := by
    have : augmented f h 0 l = fun y => f y + inner ℝ l (h y) := by
      funext y; simp [augmented]
    rw [this]
    exact hf.add (ContDiffAt.inner ℝ contDiffAt_const hh)
  have hg : ContDiffAt ℝ 2 (fun y => ‖h y‖ ^ 2) x := ContDiffAt.norm_sq ℝ hh
  have hGd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (augmented f h 0 l) y := by
    filter_upwards [hG.eventually (by simp)] with y hy
    exact hy.differentiableAt (by simp)
  have hgd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (fun y => ‖h y‖ ^ 2) y := by
    filter_upwards [hg.eventually (by simp)] with y hy
    exact hy.differentiableAt (by simp)
  -- the first derivative near `x`
  have h1 : fderiv ℝ (augmented f h α l)
      =ᶠ[𝓝 x] fderiv ℝ (augmented f h 0 l) + (1 / 2 * α) • fderiv ℝ (fun y => ‖h y‖ ^ 2) := by
    filter_upwards [hGd, hgd] with y hGy hgy
    rw [Pi.add_apply, Pi.smul_apply, hsplit, fderiv_add hGy (hgy.const_smul _),
      fderiv_const_smul hgy]
  -- differentiate again
  have hG' : HasFDerivAt (fderiv ℝ (augmented f h 0 l))
      (fderiv ℝ (fderiv ℝ (augmented f h 0 l)) x) x :=
    ((hG.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero).hasFDerivAt
  have hg' : HasFDerivAt (fderiv ℝ (fun y => ‖h y‖ ^ 2))
      (fderiv ℝ (fderiv ℝ (fun y => ‖h y‖ ^ 2)) x) x :=
    ((hg.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero).hasFDerivAt
  have h2 := hG'.add (hg'.const_smul (1 / 2 * α))
  rw [h1.fderiv_eq, h2.fderiv]
  simp only [add_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [fderiv_fderiv_norm_sq_apply hx hh v]
  ring

/-- **Condition 3 of Bertsekas' Proposition 2.4 follows from condition 2** (Bertsekas,
*Constrained Optimization and Lagrange Multiplier Methods*, Lemma 1.25 applied to the augmented
Lagrangian; [quarteroni2000numerical] Property 7.17): at a feasible point `x`, `h x = 0`, with
`f`, `h` of class `C²`, if the Hessian of the Lagrangian `𝒢_0(·, λ)` is positive on the nonzero
directions `z` tangent to the constraints, `h'(x) z = 0`, then the Hessian of the augmented
Lagrangian `𝒢_α(·, λ)` at `x` is positive definite for every large `α`. -/
theorem exists_forall_pos_fderiv_fderiv_augmented [FiniteDimensional ℝ E] {f : E → ℝ} {h : E → F}
    {x : E} (hx : h x = 0) (hf : ContDiffAt ℝ 2 f x) (hh : ContDiffAt ℝ 2 h x) (l : F)
    (hpos : ∀ z, z ≠ 0 → fderiv ℝ h x z = 0 →
      0 < fderiv ℝ (fderiv ℝ (augmented f h 0 l)) x z z) :
    ∃ α₀ : ℝ, ∀ α, α₀ ≤ α → ∀ z, z ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ (augmented f h α l)) x z z := by
  obtain ⟨α₀, hα₀⟩ := exists_forall_pos_add_mul_sq_norm_of_pos_on_ker
    (fderiv ℝ (fderiv ℝ (augmented f h 0 l)) x) (fderiv ℝ h x) hpos
  refine ⟨α₀, fun α hα z hz => ?_⟩
  rw [fderiv_fderiv_augmented_apply hx hf hh α l z]
  exact hα₀ α hα z hz

end AugmentedHessian

end Constrained

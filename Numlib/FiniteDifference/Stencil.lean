import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Numlib.FiniteDifference.TwoLevel

/-!
# Constant-coefficient difference schemes on the integer grid

A **stencil** is a finitely supported family of real weights `c : ℤ →₀ ℝ`, acting on grid functions
`u : ℤ → M` (for any real module `M`) by the finite convolution

  `(c u) j = ∑_s c s • u (j - s)`,

so that `c s` is the weight of the neighbour `s` steps to the *left* (`FiniteDifference.Stencil`,
`FiniteDifference.Stencil.apply`). The three-point stencils `Stencil.threePoint cm c0 cp`, sending
`u` to `j ↦ cm u_{j-1} + c0 u_j + cp u_{j+1}`, cover every explicit scheme of
[quarteroni2000numerical] §13.7, and the conservative form `u_j - λ (h(u_j, u_{j+1}) - h(u_{j-1},
u_j))` of their (13.36) with a linear numerical flux `h(u, v) = α u + β v` is `Stencil.ofFlux λ α β`
(`FiniteDifference.IsConservativeForm`, `Stencil.isConservativeForm_iff`).

Three facts carry the theory.

* **Finite speed of propagation** (`Stencil.iterate_apply_congr_of_eqOn`): `(cⁿ u) j` depends only
  on `u` within `n r` of `j` when the stencil has radius `r`. This is the numerical domain of
  dependence, and the source of the Courant–Friedrichs–Lewy necessary condition of
  [quarteroni2000numerical] §13.8.3.
* **Monotone stencils** (`Stencil.IsMonotone`: `c ≥ 0`, `∑ c = 1`) are convex averages of
  neighbouring values, hence satisfy the discrete maximum principle
  (`Stencil.IsMonotone.apply_le_iSup`, `Stencil.IsMonotone.iInf_le_apply`, their iterates) and are
  nonexpansive in every `ℓ^p` (`Stencil.IsMonotone.norm_lpCLM_le_one`). The upwind and
  Lax–Friedrichs schemes are monotone exactly under the CFL condition.
* **The `ℓ^p` operator bound** `‖c‖_{ℓ^p → ℓ^p} ≤ ∑_s |c s|` (`Stencil.norm_lpCLM_le`), Young's
  inequality on `ℤ` for a finitely supported kernel: the stencil is the finite sum of the shift
  isometries `lp.shiftₗᵢ` weighted by its coefficients. The shifts are built from the general
  reindexing isometry `lp.compEquivₗᵢ` along a bijection of the index set, which Mathlib does not
  have. For `p = 2` the sharp bound is the supremum of the **symbol** `∑_s c s e^{-isφ}`
  (`Stencil.symbol`), the amplification factor of the mode `j ↦ e^{ijφ}`
  (`Stencil.apply_exp_eq_symbol_smul`); the `ℓ²` bound through the symbol is the whole-line
  counterpart of the periodic von Neumann analysis of `Numlib.FiniteDifference.VonNeumann`.

The **discrete norms** `‖v‖_{Δ,p} = Δx^{1/p} ‖v‖_p` of [quarteroni2000numerical] (13.47) are
`FiniteDifference.discreteNorm`, and **stability of a family of schemes** over every finite horizon
— `‖Qⁿ‖ ≤ C_T` for `n Δt ≤ T` and small steps, their (13.46) and Definition 6.3.1 of
[han2009theoretical] — is `FiniteDifference.IsStableFamily`, stated over a *dependent* family of
normed spaces so that periodic grids `Fin N` and the line `ℤ` are both instances; the error
accumulation theorem `FiniteDifference.norm_sub_le_of_stable` applies to each member of a stable
family (`IsStableFamily.exists_norm_sub_le`).
-/

open Set Filter Topology Finset Function
open scoped ENNReal

/-! ### Reindexing and shifting `ℓ^p` -/

namespace Memℓp

variable {α β E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}

/-- `Memℓp` is invariant under reindexing along a bijection: `f ∘ e ∈ ℓ^p` when `f ∈ ℓ^p`. -/
theorem comp_equiv {f : β → E} (hf : Memℓp f p) (e : α ≃ β) : Memℓp (f ∘ e) p := by
  rcases p.trichotomy with rfl | rfl | hp
  · exact memℓp_zero ((memℓp_zero_iff.1 hf).preimage e.injective.injOn)
  · refine memℓp_infty ?_
    have h := hf.bddAbove
    rwa [← e.surjective.range_comp fun i => ‖f i‖] at h
  · exact memℓp_gen ((e.summable_iff (f := fun i => ‖f i‖ ^ p.toReal)).2 (hf.summable hp))

end Memℓp

namespace lp

variable {α β E : Type*} [NormedAddCommGroup E] {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Reindexing `ℓ^p` along a bijection of the index set** is a linear isometry:
`(compEquivₗᵢ e f) a = f (e a)`. The `ℓ^p` norm is a sum or a supremum over the index set, and both
are invariant under bijections. -/
noncomputable def compEquivₗᵢ (e : α ≃ β) :
    lp (fun _ : β => E) p ≃ₗᵢ[𝕜] lp (fun _ : α => E) p where
  toFun f := ⟨(f : β → E) ∘ e, (lp.memℓp f).comp_equiv e⟩
  invFun g := ⟨(g : α → E) ∘ e.symm, (lp.memℓp g).comp_equiv e.symm⟩
  left_inv f := lp.ext (by ext b; simp)
  right_inv g := lp.ext (by ext a; simp)
  map_add' f g := rfl
  map_smul' c f := rfl
  norm_map' f := by
    rcases p.trichotomy with rfl | rfl | hp
    · exact absurd (Fact.out : (1 : ℝ≥0∞) ≤ 0) (by simp)
    · change ⨆ a, ‖f (e a)‖ = ⨆ b, ‖f b‖
      exact e.iSup_comp (g := fun b => ‖(f : β → E) b‖)
    · change ‖(⟨(f : β → E) ∘ e, (lp.memℓp f).comp_equiv e⟩ : lp (fun _ : α => E) p)‖ = ‖f‖
      rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
      congr 1
      exact e.tsum_eq fun b => ‖f b‖ ^ p.toReal

/-- The reindexing isometry acts by precomposition. -/
@[simp]
theorem compEquivₗᵢ_apply (e : α ≃ β) (f : lp (fun _ : β => E) p) (a : α) :
    compEquivₗᵢ (𝕜 := 𝕜) e f a = f (e a) := rfl

/-- **Translation on `ℓ^p(ℤ)`**: `(shiftₗᵢ p s u) j = u (j - s)`, a linear isometry. -/
noncomputable def shiftₗᵢ (p : ℝ≥0∞) [Fact (1 ≤ p)] (s : ℤ) :
    lp (fun _ : ℤ => E) p ≃ₗᵢ[𝕜] lp (fun _ : ℤ => E) p :=
  compEquivₗᵢ (Equiv.subRight s)

/-- The shift acts by translation: `(shiftₗᵢ p s u) j = u (j - s)`. -/
@[simp]
theorem shiftₗᵢ_apply (s : ℤ) (u : lp (fun _ : ℤ => E) p) (j : ℤ) :
    shiftₗᵢ (𝕜 := 𝕜) p s u j = u (j - s) := rfl

end lp

namespace FiniteDifference

/-! ### Stencils and their action -/

/-- A **stencil**: a finitely supported family of real weights on the integer grid. `c s` is the
weight of the neighbour `s` steps to the left in `Stencil.apply`. -/
abbrev Stencil := ℤ →₀ ℝ

namespace Stencil

variable {M : Type*} [AddCommMonoid M] [Module ℝ M]

/-- The action of a stencil on a grid function, `(c u) j = ∑_s c s • u (j - s)`: a finite
convolution on `ℤ`. -/
noncomputable def apply (c : Stencil) (u : ℤ → M) : ℤ → M :=
  fun j => c.sum fun s a => a • u (j - s)

/-- The action of a stencil, as a finite sum over its support. -/
theorem apply_apply (c : Stencil) (u : ℤ → M) (j : ℤ) :
    apply c u j = ∑ s ∈ c.support, c s • u (j - s) := rfl

/-- The action of a stencil is additive. -/
theorem apply_add (c : Stencil) (u v : ℤ → M) : apply c (u + v) = apply c u + apply c v := by
  ext j
  simp [apply_apply, smul_add, Finset.sum_add_distrib]

/-- The action of a stencil commutes with scalars. -/
theorem apply_smul (c : Stencil) (r : ℝ) (u : ℤ → M) : apply c (r • u) = r • apply c u := by
  ext j
  simp [apply_apply, Finset.smul_sum, smul_comm r]

/-- The action of a stencil as a linear map on grid functions. -/
noncomputable def applyₗ (c : Stencil) : (ℤ → M) →ₗ[ℝ] (ℤ → M) where
  toFun := apply c
  map_add' := apply_add c
  map_smul' := apply_smul c

/-- The linear map of a stencil acts by `Stencil.apply`. -/
@[simp]
theorem applyₗ_apply (c : Stencil) (u : ℤ → M) : applyₗ c u = apply c u := rfl

/-- The action of a stencil on a grid function reads it only within the support: two grid
functions agreeing on `{i | i - j ∈ c.support}` have the same image at `j`. -/
theorem apply_congr {c : Stencil} {u v : ℤ → M} {j : ℤ}
    (h : ∀ s ∈ c.support, u (j - s) = v (j - s)) : apply c u j = apply c v j :=
  Finset.sum_congr rfl fun s hs => by dsimp only; rw [h s hs]

/-- The three-point stencil `j ↦ cm u_{j-1} + c0 u_j + cp u_{j+1}`. -/
noncomputable def threePoint (cm c0 cp : ℝ) : Stencil :=
  Finsupp.single 1 cm + Finsupp.single 0 c0 + Finsupp.single (-1) cp

/-- The action of the three-point stencil:
`(c u) j = cm • u (j - 1) + c0 • u j + cp • u (j + 1)`. -/
theorem threePoint_apply (cm c0 cp : ℝ) (u : ℤ → M) (j : ℤ) :
    apply (threePoint cm c0 cp) u j = cm • u (j - 1) + c0 • u j + cp • u (j + 1) := by
  simp only [apply, threePoint]
  rw [Finsupp.sum_add_index' (h := fun s a => a • u (j - s)) (fun _ => zero_smul ℝ _)
      (fun _ _ _ => add_smul _ _ _),
    Finsupp.sum_add_index' (h := fun s a => a • u (j - s)) (fun _ => zero_smul ℝ _)
      (fun _ _ _ => add_smul _ _ _),
    Finsupp.sum_single_index (h := fun s a => a • u (j - s)) (zero_smul ℝ _),
    Finsupp.sum_single_index (h := fun s a => a • u (j - s)) (zero_smul ℝ _),
    Finsupp.sum_single_index (h := fun s a => a • u (j - s)) (zero_smul ℝ _), sub_zero,
    sub_neg_eq_add]

/-- The support of a three-point stencil lies in `{-1, 0, 1}`. -/
theorem support_threePoint_subset (cm c0 cp : ℝ) :
    (threePoint cm c0 cp).support ⊆ {1, 0, -1} := by
  refine (Finsupp.support_add.trans (union_subset_union Finsupp.support_add le_rfl)).trans ?_
  refine union_subset (union_subset ?_ ?_) ?_ <;>
    exact Finsupp.support_single_subset.trans (by simp)

/-- The sum of the weights of a three-point stencil. -/
theorem threePoint_sum (cm c0 cp : ℝ) :
    (threePoint cm c0 cp).sum (fun _ a => a) = cm + c0 + cp := by
  simp only [threePoint]
  rw [Finsupp.sum_add_index' (h := fun _ a => a) (fun _ => rfl) (fun _ _ _ => rfl),
    Finsupp.sum_add_index' (h := fun _ a => a) (fun _ => rfl) (fun _ _ _ => rfl),
    Finsupp.sum_single_index (h := fun _ a => a) rfl,
    Finsupp.sum_single_index (h := fun _ a => a) rfl,
    Finsupp.sum_single_index (h := fun _ a => a) rfl]

/-! ### Conservative form -/

/-- The **conservative form** of a linear numerical flux `h(u, v) = α u + β v`:
`Stencil.ofFlux lam α β` sends `u` to `j ↦ u_j - lam ((α u_j + β u_{j+1}) - (α u_{j-1} + β u_j))`
([quarteroni2000numerical] (13.36)). -/
noncomputable def ofFlux (lam α β : ℝ) : Stencil :=
  threePoint (lam * α) (1 - lam * (α - β)) (-(lam * β))

/-- The action of `Stencil.ofFlux`, in the conservative form of [quarteroni2000numerical]
(13.36). -/
theorem ofFlux_apply (lam α β : ℝ) (u : ℤ → ℝ) (j : ℤ) :
    apply (ofFlux lam α β) u j
      = u j - lam * ((α * u j + β * u (j + 1)) - (α * u (j - 1) + β * u j)) := by
  rw [ofFlux, threePoint_apply]
  simp only [smul_eq_mul]
  ring

end Stencil

/-- **A step in conservative form** ([quarteroni2000numerical] (13.36)): the scheme advances by
the difference of a numerical flux `h` across the two half-cells,
`(step u) j = u j - lam (h (u j) (u (j+1)) - h (u (j-1)) (u j))`. Every explicit scheme for a
conservation law `u_t + f(u)_x = 0` has this form. -/
def IsConservativeForm (lam : ℝ) (h : ℝ → ℝ → ℝ) (step : (ℤ → ℝ) → (ℤ → ℝ)) : Prop :=
  ∀ u j, step u j = u j - lam * (h (u j) (u (j + 1)) - h (u (j - 1)) (u j))

namespace Stencil

/-- A step is in conservative form with the linear flux `h(u, v) = α u + β v` if and only if it is
the action of `Stencil.ofFlux lam α β`. -/
theorem isConservativeForm_iff {lam α β : ℝ} {step : (ℤ → ℝ) → (ℤ → ℝ)} :
    IsConservativeForm lam (fun u v => α * u + β * v) step ↔ step = apply (ofFlux lam α β) := by
  constructor
  · intro h
    funext u j
    rw [ofFlux_apply, h u j]
  · rintro rfl u j
    exact ofFlux_apply lam α β u j

/-- `Stencil.ofFlux lam α β` is in conservative form with the flux `α u + β v`. -/
theorem isConservativeForm_ofFlux (lam α β : ℝ) :
    IsConservativeForm lam (fun u v => α * u + β * v) (apply (ofFlux lam α β)) :=
  isConservativeForm_iff.2 rfl

/-! ### Finite speed of propagation -/

variable {M : Type*} [AddCommMonoid M] [Module ℝ M]

/-- **Finite speed of propagation** (the numerical domain of dependence,
[quarteroni2000numerical] §13.8.3): if the stencil has radius `r`, `|s| ≤ r` on its support, and two
grid functions agree within `n r` of `j`, then their `n`-th iterates agree at `j`. -/
theorem iterate_apply_congr_of_eqOn {c : Stencil} {r : ℤ} (hr : ∀ s ∈ c.support, |s| ≤ r)
    (n : ℕ) {u v : ℤ → M} {j : ℤ} (huv : ∀ i, |i - j| ≤ n * r → u i = v i) :
    (apply c)^[n] u j = (apply c)^[n] v j := by
  induction n generalizing j with
  | zero => exact huv j (by simp)
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply']
    refine apply_congr fun s hs => ih fun i hi => huv i ?_
    have h1 := hr s hs
    have h2 : |i - j| ≤ |i - (j - s)| + |s| := by
      calc |i - j| = |(i - (j - s)) + (-s)| := by ring_nf
        _ ≤ |i - (j - s)| + |-s| := abs_add_le _ _
        _ = |i - (j - s)| + |s| := by rw [abs_neg]
    push_cast
    nlinarith

/-! ### Monotone stencils and the discrete maximum principle -/

/-- A **monotone stencil**: nonnegative weights summing to `1`, so that the scheme is a convex
average of neighbouring values. -/
def IsMonotone (c : Stencil) : Prop := (∀ s, 0 ≤ c s) ∧ c.sum (fun _ a => a) = 1

/-- The weights of a monotone stencil are nonnegative. -/
theorem IsMonotone.nonneg {c : Stencil} (hc : c.IsMonotone) (s : ℤ) : 0 ≤ c s := hc.1 s

/-- The weights of a monotone stencil sum to `1`. -/
theorem IsMonotone.sum_eq_one {c : Stencil} (hc : c.IsMonotone) : ∑ s ∈ c.support, c s = 1 := hc.2

/-- **The discrete maximum principle**, upper half: a monotone stencil does not exceed an upper
bound of its input. -/
theorem IsMonotone.apply_le {c : Stencil} (hc : c.IsMonotone) {u : ℤ → ℝ} {B : ℝ}
    (hu : ∀ i, u i ≤ B) (j : ℤ) : apply c u j ≤ B := by
  rw [apply_apply]
  calc ∑ s ∈ c.support, c s • u (j - s) ≤ ∑ s ∈ c.support, c s * B :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hu _) (hc.nonneg s)
    _ = B := by rw [← Finset.sum_mul, hc.sum_eq_one, one_mul]

/-- **The discrete maximum principle**, lower half: a monotone stencil does not go below a lower
bound of its input. -/
theorem IsMonotone.le_apply {c : Stencil} (hc : c.IsMonotone) {u : ℤ → ℝ} {B : ℝ}
    (hu : ∀ i, B ≤ u i) (j : ℤ) : B ≤ apply c u j := by
  rw [apply_apply]
  calc B = ∑ s ∈ c.support, c s * B := by rw [← Finset.sum_mul, hc.sum_eq_one, one_mul]
    _ ≤ ∑ s ∈ c.support, c s • u (j - s) :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hu _) (hc.nonneg s)

/-- Iterating a monotone stencil keeps an upper bound. -/
theorem IsMonotone.iterate_apply_le {c : Stencil} (hc : c.IsMonotone) {u : ℤ → ℝ} {B : ℝ}
    (hu : ∀ i, u i ≤ B) (n : ℕ) (j : ℤ) : (apply c)^[n] u j ≤ B := by
  induction n generalizing j with
  | zero => exact hu j
  | succ n ih => rw [iterate_succ_apply']; exact hc.apply_le ih j

/-- Iterating a monotone stencil keeps a lower bound. -/
theorem IsMonotone.le_iterate_apply {c : Stencil} (hc : c.IsMonotone) {u : ℤ → ℝ} {B : ℝ}
    (hu : ∀ i, B ≤ u i) (n : ℕ) (j : ℤ) : B ≤ (apply c)^[n] u j := by
  induction n generalizing j with
  | zero => exact hu j
  | succ n ih => rw [iterate_succ_apply']; exact hc.le_apply ih j

/-- **The discrete maximum principle** ([quarteroni2000numerical] (13.53)): for a monotone stencil
and a grid function bounded above, `(c u) j ≤ ⨆ i, u i`. -/
theorem IsMonotone.apply_le_iSup {c : Stencil} (hc : c.IsMonotone) {u : ℤ → ℝ}
    (hu : BddAbove (range u)) (j : ℤ) : apply c u j ≤ ⨆ i, u i :=
  hc.apply_le (fun i => le_ciSup hu i) j

/-- **The discrete maximum principle**, lower half: `⨅ i, u i ≤ (c u) j` for a grid function
bounded below. -/
theorem IsMonotone.iInf_le_apply {c : Stencil} (hc : c.IsMonotone) {u : ℤ → ℝ}
    (hu : BddBelow (range u)) (j : ℤ) : ⨅ i, u i ≤ apply c u j :=
  hc.le_apply (fun i => ciInf_le hu i) j

/-- The iterated discrete maximum principle: `(cⁿ u) j ≤ ⨆ i, u i`, so the supremum norm of the
solution of a monotone scheme never increases. -/
theorem IsMonotone.iterate_apply_le_iSup {c : Stencil} (hc : c.IsMonotone) {u : ℤ → ℝ}
    (hu : BddAbove (range u)) (n : ℕ) (j : ℤ) : (apply c)^[n] u j ≤ ⨆ i, u i :=
  hc.iterate_apply_le (fun i => le_ciSup hu i) n j

/-- The iterated discrete maximum principle, lower half: `⨅ i, u i ≤ (cⁿ u) j`. -/
theorem IsMonotone.iInf_le_iterate_apply {c : Stencil} (hc : c.IsMonotone) {u : ℤ → ℝ}
    (hu : BddBelow (range u)) (n : ℕ) (j : ℤ) : ⨅ i, u i ≤ (apply c)^[n] u j :=
  hc.le_iterate_apply (fun i => ciInf_le hu i) n j

/-! ### The stencil as a bounded operator on `ℓ^p(ℤ)` -/

section Lp

variable {p : ℝ≥0∞}

/-- The action of a stencil on a grid function, as the finite sum of the shifted grid functions
weighted by the coefficients. -/
theorem apply_eq_sum (c : Stencil) (u : ℤ → M) :
    apply c u = fun j => ∑ s ∈ c.support, (c s • (u ∘ Equiv.subRight s)) j := by
  ext j
  rw [apply_apply]
  rfl

/-- A stencil maps `ℓ^p` to `ℓ^p`, for every `p`: a finite linear combination of shifts. -/
theorem memℓp_apply (c : Stencil) {u : ℤ → ℝ} (hu : Memℓp u p) : Memℓp (apply c u) p := by
  rw [apply_eq_sum]
  exact Memℓp.finsetSum c.support (f := fun s => c s • (u ∘ Equiv.subRight s))
    fun s _ => (hu.comp_equiv (Equiv.subRight s)).const_smul (c s)

variable [Fact (1 ≤ p)]

/-- **The stencil as a bounded operator on `ℓ^p(ℤ)`**: `lpCLM c p = ∑_s c s • shiftₗᵢ p s`. -/
noncomputable def lpCLM (c : Stencil) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    lp (fun _ : ℤ => ℝ) p →L[ℝ] lp (fun _ : ℤ => ℝ) p :=
  ∑ s ∈ c.support, c s • (lp.shiftₗᵢ (E := ℝ) (𝕜 := ℝ) p s).toLinearIsometry.toContinuousLinearMap

/-- The bounded operator of a stencil acts by `Stencil.apply`. -/
theorem coeFn_lpCLM (c : Stencil) (u : lp (fun _ : ℤ => ℝ) p) : ⇑(lpCLM c p u) = apply c u := by
  ext j
  rw [lpCLM, _root_.sum_apply, lp.coeFn_sum, Finset.sum_apply, apply_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [smul_apply, lp.coeFn_smul, Pi.smul_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, lp.shiftₗᵢ_apply]

/-- The bounded operator of a stencil acts by `Stencil.apply`, pointwise. -/
theorem lpCLM_apply (c : Stencil) (u : lp (fun _ : ℤ => ℝ) p) (j : ℤ) :
    lpCLM c p u j = apply c u j := by
  rw [coeFn_lpCLM]

/-- **Young's inequality for a finitely supported kernel on `ℤ`**:
`‖lpCLM c p‖ ≤ ∑_s |c s|`, the triangle inequality plus the isometry of each shift. -/
theorem norm_lpCLM_le (c : Stencil) : ‖lpCLM c p‖ ≤ ∑ s ∈ c.support, |c s| := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _)
    (lp.shiftₗᵢ (E := ℝ) (𝕜 := ℝ) p s).toLinearIsometry.norm_toContinuousLinearMap_le

/-- **Monotone stencils are nonexpansive in every `ℓ^p`**: `‖lpCLM c p‖ ≤ 1`. This is the
`‖·‖_{Δ,1}` stability of the upwind and Lax–Friedrichs schemes under the CFL condition of
[quarteroni2000numerical] §13.8.3, with constant `1`. -/
theorem IsMonotone.norm_lpCLM_le_one {c : Stencil} (hc : c.IsMonotone) : ‖lpCLM c p‖ ≤ 1 := by
  refine (norm_lpCLM_le c).trans (le_of_eq ?_)
  rw [Finset.sum_congr rfl fun s _ => abs_of_nonneg (hc.nonneg s)]
  exact hc.sum_eq_one

/-- The bounded operator of a monotone stencil is nonexpansive: `‖lpCLM c p u‖ ≤ ‖u‖`. -/
theorem IsMonotone.norm_lpCLM_apply_le {c : Stencil} (hc : c.IsMonotone)
    (u : lp (fun _ : ℤ => ℝ) p) : ‖lpCLM c p u‖ ≤ ‖u‖ := by
  have := (lpCLM c p).le_of_opNorm_le hc.norm_lpCLM_le_one u
  rwa [one_mul] at this

end Lp

/-! ### The symbol -/

section Symbol

open Complex

/-- **The symbol of a stencil**, `σ(φ) = ∑_s c s e^{-isφ}`: the amplification factor of the Fourier
mode `j ↦ e^{ijφ}` under the stencil. -/
noncomputable def symbol (c : Stencil) (φ : ℝ) : ℂ :=
  ∑ s ∈ c.support, (c s : ℂ) * exp (-(I * s * φ))

/-- The Fourier modes are eigenvectors of every stencil, with eigenvalue the symbol:
`c (j ↦ e^{ijφ}) = σ(φ) • (j ↦ e^{ijφ})`. -/
theorem apply_exp_eq_symbol_smul (c : Stencil) (φ : ℝ) :
    apply c (fun j : ℤ => exp (I * j * φ)) = symbol c φ • fun j : ℤ => exp (I * j * φ) := by
  ext j
  rw [apply_apply, Pi.smul_apply, symbol, smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Complex.real_smul, mul_assoc (c s : ℂ), ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The symbol is `2π`-periodic. -/
theorem symbol_add_two_pi (c : Stencil) (φ : ℝ) : symbol c (φ + 2 * Real.pi) = symbol c φ := by
  unfold symbol
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  rw [show -(I * s * ((φ + 2 * Real.pi : ℝ) : ℂ)) = -(I * s * φ) + (-s : ℤ) * (2 * Real.pi * I) by
    push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The symbol of a three-point stencil: `σ(φ) = c0 + cm e^{-iφ} + cp e^{iφ}`. -/
theorem symbol_threePoint (cm c0 cp : ℝ) (φ : ℝ) :
    symbol (threePoint cm c0 cp) φ = c0 + cm * exp (-(I * φ)) + cp * exp (I * φ) := by
  have h := congrFun (apply_exp_eq_symbol_smul (threePoint cm c0 cp) φ) 0
  rw [threePoint_apply, Pi.smul_apply, smul_eq_mul] at h
  simp only [Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one, zero_sub, zero_add,
    Int.cast_neg, Int.cast_one, Complex.real_smul] at h
  rw [← h]
  ring_nf

end Symbol

/-! ### The `ℓ²` bound from the symbol

The operator norm of a stencil on `ℓ²(ℤ)` is at most the supremum of the modulus of its symbol —
the whole-line counterpart of the von Neumann analysis on a periodic grid. The proof is Parseval's
identity on `ℤ` for trigonometric polynomials, which needs nothing but the orthogonality of the
exponentials over one period (`∫_0^{2π} e^{ikφ} dφ = 2π δ_{k0}`, a finite computation), together
with the fact that the symbol of a convolution is the product of the symbols. The bound for a
finitely supported grid function extends to all of `ℓ²` by summing over larger and larger finite
sets of indices. -/

section SymbolLTwo

open Complex

/-- `conj (e^{-isφ}) = e^{isφ}` for an integer `s` and a real `φ`. -/
private theorem conj_exp_neg_int_mul (s : ℤ) (φ : ℝ) :
    (starRingEnd ℂ) (exp (-(I * s * φ))) = exp (I * s * φ) := by
  rw [← Complex.exp_conj]
  congr 1
  simp

/-- **Orthogonality of the exponentials over one period**: `∫_0^{2π} e^{ikφ} dφ` is `2π` when
`k = 0` and `0` otherwise. -/
private theorem integral_exp_int_mul (k : ℤ) :
    (∫ φ in (0 : ℝ)..(2 * Real.pi), exp (I * k * φ))
      = if k = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · rw [ite_eq_right hk]
    have hc : (I * (k : ℂ)) ≠ 0 := mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.2 hk)
    have h := integral_exp_mul_complex (a := (0 : ℝ)) (b := 2 * Real.pi) hc
    have htop : Complex.exp (I * (k : ℂ) * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      rw [show I * (k : ℂ) * ((2 * Real.pi : ℝ) : ℂ) = (k : ℂ) * (2 * Real.pi * I) by
        push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I k
    rw [h, htop]
    simp

/-- **Parseval's identity for a trigonometric polynomial**: for finitely many complex
coefficients, `∫_0^{2π} |∑_s v_s e^{-isφ}|² dφ = 2π ∑_s |v_s|²`. -/
private theorem integral_norm_sq_trigPoly (A : Finset ℤ) (v : ℤ → ℂ) :
    (∫ φ in (0 : ℝ)..(2 * Real.pi), ‖∑ s ∈ A, v s * exp (-(I * s * φ))‖ ^ 2)
      = 2 * Real.pi * ∑ s ∈ A, ‖v s‖ ^ 2 := by
  have hexpand : ∀ φ : ℝ,
      (∑ s ∈ A, v s * exp (-(I * s * φ))) * (starRingEnd ℂ) (∑ s ∈ A, v s * exp (-(I * s * φ)))
        = ∑ s ∈ A, ∑ t ∈ A, v s * (starRingEnd ℂ) (v t) * exp (I * ((t : ℂ) - (s : ℂ)) * φ) := by
    intro φ
    simp only [map_sum, map_mul, conj_exp_neg_int_mul]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
    rw [show v s * exp (-(I * s * φ)) * ((starRingEnd ℂ) (v t) * exp (I * t * φ))
        = v s * (starRingEnd ℂ) (v t) * (exp (-(I * s * φ)) * exp (I * t * φ)) by ring,
      ← Complex.exp_add]
    congr 2
    ring
  have hcint : ∀ s t : ℤ, IntervalIntegrable
      (fun φ : ℝ => v s * (starRingEnd ℂ) (v t) * exp (I * ((t : ℂ) - (s : ℂ)) * φ))
      MeasureTheory.volume 0 (2 * Real.pi) := by
    intro s t
    exact (by fun_prop : Continuous fun φ : ℝ =>
      v s * (starRingEnd ℂ) (v t) * exp (I * ((t : ℂ) - (s : ℂ)) * φ)).intervalIntegrable _ _
  have hsumint : ∀ s : ℤ, IntervalIntegrable
      (fun φ : ℝ => ∑ t ∈ A, v s * (starRingEnd ℂ) (v t) * exp (I * ((t : ℂ) - (s : ℂ)) * φ))
      MeasureTheory.volume 0 (2 * Real.pi) := fun s =>
    (by fun_prop : Continuous fun φ : ℝ =>
      ∑ t ∈ A, v s * (starRingEnd ℂ) (v t)
        * exp (I * ((t : ℂ) - (s : ℂ)) * φ)).intervalIntegrable _ _
  have hdiag : ∀ s t : ℤ,
      (∫ φ in (0 : ℝ)..(2 * Real.pi),
          v s * (starRingEnd ℂ) (v t) * exp (I * ((t : ℂ) - (s : ℂ)) * φ))
        = if t = s then ((2 * Real.pi : ℝ) : ℂ) * (v s * (starRingEnd ℂ) (v t)) else 0 := by
    intro s t
    rw [intervalIntegral.integral_const_mul]
    have hk : (fun φ : ℝ => exp (I * ((t : ℂ) - (s : ℂ)) * φ))
        = fun φ : ℝ => exp (I * ((t - s : ℤ) : ℂ) * φ) := by
      funext φ; push_cast; ring_nf
    rw [hk, integral_exp_int_mul (t - s)]
    rcases eq_or_ne t s with rfl | hts
    · simp [mul_comm]
    · rw [ite_eq_right (sub_ne_zero.2 hts), ite_eq_right hts, mul_zero]
  have hcomplex : (∫ φ in (0 : ℝ)..(2 * Real.pi),
      ((‖∑ s ∈ A, v s * exp (-(I * s * φ))‖ ^ 2 : ℝ) : ℂ))
      = ((2 * Real.pi * ∑ s ∈ A, ‖v s‖ ^ 2 : ℝ) : ℂ) := by
    have hpt : ∀ φ : ℝ, ((‖∑ s ∈ A, v s * exp (-(I * s * φ))‖ ^ 2 : ℝ) : ℂ)
        = (∑ s ∈ A, v s * exp (-(I * s * φ))) *
          (starRingEnd ℂ) (∑ s ∈ A, v s * exp (-(I * s * φ))) := by
      intro φ
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [intervalIntegral.integral_congr fun φ _ => (hpt φ).trans (hexpand φ),
      intervalIntegral.integral_finsetSum (f := fun s (φ : ℝ) =>
          ∑ t ∈ A, v s * (starRingEnd ℂ) (v t) * exp (I * ((t : ℂ) - (s : ℂ)) * φ))
        fun s _ => hsumint s]
    have hstep : ∀ s ∈ A, (∫ φ in (0 : ℝ)..(2 * Real.pi),
        ∑ t ∈ A, v s * (starRingEnd ℂ) (v t) * exp (I * ((t : ℂ) - (s : ℂ)) * φ))
          = ((2 * Real.pi : ℝ) : ℂ) * ((‖v s‖ : ℝ) : ℂ) ^ 2 := by
      intro s hs
      rw [intervalIntegral.integral_finsetSum (f := fun t (φ : ℝ) =>
            v s * (starRingEnd ℂ) (v t) * exp (I * ((t : ℂ) - (s : ℂ)) * φ))
          fun t _ => hcint s t,
        Finset.sum_congr rfl fun t _ => hdiag s t, Finset.sum_ite_eq' A s]
      rw [ite_eq_left hs, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
    push_cast
    ring
  rw [intervalIntegral.integral_ofReal] at hcomplex
  exact_mod_cast hcomplex

/-- Reindexing a sum of the shifted coefficients: `∑_{j ∈ A} w(j - s) e^{-ijφ}` equals
`∑_{t ∈ supp w} w(t) e^{-i(s+t)φ}` as soon as `A` contains `s + supp w`. -/
private theorem sum_shift_eq (s : ℤ) (A : Finset ℤ) (w : ℤ →₀ ℝ)
    (hA : ∀ t ∈ w.support, s + t ∈ A) (φ : ℝ) :
    (∑ j ∈ A, ((w (j - s) : ℝ) : ℂ) * exp (-(I * j * φ)))
      = ∑ t ∈ w.support, ((w t : ℝ) : ℂ) * exp (-(I * ((s : ℂ) + t) * φ)) := by
  classical
  have hmap : (∑ t ∈ w.support, ((w t : ℝ) : ℂ) * exp (-(I * ((s : ℂ) + t) * φ)))
      = ∑ j ∈ w.support.map ⟨(s + ·), add_right_injective s⟩,
          ((w (j - s) : ℝ) : ℂ) * exp (-(I * j * φ)) := by
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Function.Embedding.coeFn_mk, add_sub_cancel_left]
    push_cast
    ring_nf
  rw [hmap]
  refine (Finset.sum_subset (fun j hj => ?_) fun j hjA hj => ?_).symm
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_map.1 hj
    exact hA t ht
  · have hw : w (j - s) = 0 := by
      by_contra hne
      refine hj (Finset.mem_map.2 ⟨j - s, Finsupp.mem_support_iff.2 hne, ?_⟩)
      simp only [Function.Embedding.coeFn_mk]
      ring
    rw [hw]
    simp

/-- **The symbol of a convolution is the product of the symbols**, in the form needed below: the
trigonometric polynomial of `c ⋆ w` is `symbol c φ` times that of `w`. -/
private theorem sum_apply_mul_exp (c : Stencil) (w : ℤ →₀ ℝ) (A : Finset ℤ)
    (hA : ∀ s ∈ c.support, ∀ t ∈ w.support, s + t ∈ A) (φ : ℝ) :
    (∑ j ∈ A, ((apply c (w : ℤ → ℝ) j : ℝ) : ℂ) * exp (-(I * j * φ)))
      = symbol c φ * ∑ t ∈ w.support, ((w t : ℝ) : ℂ) * exp (-(I * t * φ)) := by
  have hlhs : (∑ j ∈ A, ((apply c (w : ℤ → ℝ) j : ℝ) : ℂ) * exp (-(I * j * φ)))
      = ∑ s ∈ c.support, ∑ j ∈ A,
          (c s : ℂ) * (((w (j - s) : ℝ) : ℂ) * exp (-(I * j * φ))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [apply_apply]
    push_cast [smul_eq_mul]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [hlhs, symbol, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [← Finset.mul_sum, sum_shift_eq s A w (fun t ht => hA s hs t ht) φ, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [show (-(I * ((s : ℂ) + t) * φ)) = -(I * s * φ) + -(I * t * φ) by ring, Complex.exp_add]
  ring

/-- **The `ℓ²` bound for a finitely supported grid function**: `∑_j |(c ⋆ w)_j|² ≤ ρ² ∑_t |w_t|²`
whenever the symbol is bounded by `ρ`, by Parseval on both sides. -/
private theorem sum_sq_apply_le (c : Stencil) {ρ : ℝ} (hρ : ∀ φ : ℝ, ‖symbol c φ‖ ≤ ρ)
    (w : ℤ →₀ ℝ) (A : Finset ℤ) (hA : ∀ s ∈ c.support, ∀ t ∈ w.support, s + t ∈ A) :
    (∑ j ∈ A, apply c (w : ℤ → ℝ) j ^ 2) ≤ ρ ^ 2 * ∑ t ∈ w.support, w t ^ 2 := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  set U : ℝ → ℂ := fun φ => ∑ t ∈ w.support, ((w t : ℝ) : ℂ) * exp (-(I * t * φ)) with hU
  have hleft := integral_norm_sq_trigPoly A fun j => ((apply c (w : ℤ → ℝ) j : ℝ) : ℂ)
  have hright := integral_norm_sq_trigPoly w.support fun t => ((w t : ℝ) : ℂ)
  have hmono : (∫ φ in (0 : ℝ)..(2 * Real.pi),
      ‖∑ j ∈ A, ((apply c (w : ℤ → ℝ) j : ℝ) : ℂ) * exp (-(I * j * φ))‖ ^ 2)
      ≤ ρ ^ 2 * ∫ φ in (0 : ℝ)..(2 * Real.pi), ‖U φ‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hpi.le
      ((by fun_prop : Continuous fun φ : ℝ =>
        ‖∑ j ∈ A, ((apply c (w : ℤ → ℝ) j : ℝ) : ℂ) * exp (-(I * j * φ))‖ ^ 2).intervalIntegrable
          _ _)
      ((by fun_prop : Continuous fun φ : ℝ => ρ ^ 2 * ‖U φ‖ ^ 2).intervalIntegrable _ _)
      fun φ _ => ?_
    rw [sum_apply_mul_exp c w A hA φ, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hρ φ) 2) (by positivity)
  rw [hleft, hright] at hmono
  have hcast : ∀ x : ℝ, ‖((x : ℝ) : ℂ)‖ ^ 2 = x ^ 2 := by
    intro x
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [hcast] at hmono
  nlinarith [hmono, Real.pi_pos]

/-- **The `ℓ²` operator norm of a stencil is bounded by the supremum of its symbol**: if
`‖symbol c φ‖ ≤ ρ` for every `φ`, then `‖lpCLM c 2‖ ≤ ρ`.

This is the sharp `ℓ²` bound, replacing the crude `∑_s |c s|` of `Stencil.norm_lpCLM_le`, and is
the whole-line counterpart of the periodic von Neumann criterion of
`Numlib.FiniteDifference.VonNeumann`. The proof is Parseval's identity for trigonometric
polynomials (`∫_0^{2π} |∑_s v_s e^{-isφ}|² = 2π ∑_s |v_s|²`, from the orthogonality of the
exponentials over one period), applied to a finitely supported truncation of the grid function and
to its image, followed by a passage to the limit over the finite sets of indices. -/
theorem norm_lpCLM_two_le_of_symbol_le (c : Stencil) {ρ : ℝ} (hρ : ∀ φ : ℝ, ‖symbol c φ‖ ≤ ρ) :
    ‖lpCLM c 2‖ ≤ ρ := by
  classical
  have hρ0 : 0 ≤ ρ := le_trans (norm_nonneg _) (hρ 0)
  refine ContinuousLinearMap.opNorm_le_bound _ hρ0 fun u => ?_
  have htoReal : ((2 : ℝ≥0∞)).toReal = 2 := by norm_num
  have hnorm_sq : ∀ v : lp (fun _ : ℤ => ℝ) 2, ‖v‖ ^ 2 = ∑' j : ℤ, (v j) ^ 2 := by
    intro v
    have h := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by rw [htoReal]; norm_num) v
    rw [htoReal] at h
    have hr : ∀ x : ℝ, x ^ (2 : ℝ) = x ^ 2 := fun x => by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    simp only [hr, Real.norm_eq_abs, sq_abs] at h
    exact h
  have hsummable : Summable fun j : ℤ => (lpCLM c 2 u j) ^ 2 := by
    have h := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by rw [htoReal]; norm_num) (lpCLM c 2 u)
    rw [htoReal] at h
    have hr : ∀ x : ℝ, x ^ (2 : ℝ) = x ^ 2 := fun x => by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    simp only [hr, Real.norm_eq_abs, sq_abs] at h
    exact h.summable
  have hkey : ∀ B : Finset ℤ, (∑ j ∈ B, (lpCLM c 2 u j) ^ 2) ≤ ρ ^ 2 * ‖u‖ ^ 2 := by
    intro B
    -- the finitely supported truncation of `u` that `(c ⋆ u)` sees on `B`
    set A : Finset ℤ := Finset.image₂ (fun j s => j - s) B c.support with hA
    set w : ℤ →₀ ℝ := Finsupp.onFinset A (fun t => if t ∈ A then (u : ℤ → ℝ) t else 0)
      (fun t ht => by by_contra hnot; rw [ite_eq_right hnot] at ht; exact ht rfl) with hw
    have hwA : ∀ t ∈ A, w t = (u : ℤ → ℝ) t := by
      intro t ht
      simp only [hw, Finsupp.onFinset_apply, ite_eq_left ht]
    have hwsupp : w.support ⊆ A := Finsupp.support_onFinset_subset
    have hagree : ∀ j ∈ B, apply c (w : ℤ → ℝ) j = apply c (u : ℤ → ℝ) j := by
      intro j hj
      rw [apply_apply, apply_apply]
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [hwA (j - s) (Finset.mem_image₂.2 ⟨j, hj, s, hs, rfl⟩)]
    set A₂ : Finset ℤ := B ∪ Finset.image₂ (fun s t => s + t) c.support w.support with hA₂
    have hAA : ∀ s ∈ c.support, ∀ t ∈ w.support, s + t ∈ A₂ := fun s hs t ht =>
      Finset.mem_union_right _ (Finset.mem_image₂.2 ⟨s, hs, t, ht, rfl⟩)
    have hsub : B ⊆ A₂ := Finset.subset_union_left
    calc (∑ j ∈ B, (lpCLM c 2 u j) ^ 2)
        = ∑ j ∈ B, apply c (w : ℤ → ℝ) j ^ 2 := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [lpCLM_apply, hagree j hj]
      _ ≤ ∑ j ∈ A₂, apply c (w : ℤ → ℝ) j ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => sq_nonneg _
      _ ≤ ρ ^ 2 * ∑ t ∈ w.support, w t ^ 2 := sum_sq_apply_le c hρ w A₂ hAA
      _ ≤ ρ ^ 2 * ‖u‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg ρ)
          rw [hnorm_sq u]
          have hsum : Summable fun j : ℤ => ((u : ℤ → ℝ) j) ^ 2 := by
            have h := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by rw [htoReal]; norm_num) u
            rw [htoReal] at h
            have hr : ∀ x : ℝ, x ^ (2 : ℝ) = x ^ 2 := fun x => by
              rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
            simp only [hr, Real.norm_eq_abs, sq_abs] at h
            exact h.summable
          refine le_trans (le_of_eq (Finset.sum_congr rfl fun t ht => ?_))
            (hsum.sum_le_tsum w.support fun j _ => sq_nonneg _)
          rw [hwA t (hwsupp ht)]
  have hle : ‖lpCLM c 2 u‖ ^ 2 ≤ (ρ * ‖u‖) ^ 2 := by
    rw [hnorm_sq (lpCLM c 2 u), mul_pow]
    exact hsummable.tsum_le_of_sum_le hkey
  nlinarith [norm_nonneg (lpCLM c 2 u), mul_nonneg hρ0 (norm_nonneg u), hle]

end SymbolLTwo

end Stencil

/-! ### Discrete norms and stable families -/

/-- **The discrete `L^p` norms** of [quarteroni2000numerical] (13.47):
`‖v‖_{Δ,p} = Δx^{1/p} ‖v‖_{ℓ^p}`, which is `(Δx ∑_j |v_j|^p)^{1/p}` for finite `p` and
`sup_j |v_j|` for `p = ∞`. -/
noncomputable def discreteNorm (p : ℝ≥0∞) (Δx : ℝ) (v : lp (fun _ : ℤ => ℝ) p) : ℝ :=
  Δx ^ (1 / p).toReal * ‖v‖

/-- The discrete maximum norm is the supremum norm. -/
theorem discreteNorm_top (Δx : ℝ) (v : lp (fun _ : ℤ => ℝ) ∞) : discreteNorm ∞ Δx v = ‖v‖ := by
  simp [discreteNorm]

/-- The discrete `L²` norm: `‖v‖_{Δ,2} = √(Δx ∑_j v_j²)`. -/
theorem discreteNorm_two_eq_sqrt {Δx : ℝ} (hΔx : 0 ≤ Δx) (v : lp (fun _ : ℤ => ℝ) 2) :
    discreteNorm 2 Δx v = √(Δx * ∑' j, v j ^ 2) := by
  have h2 : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have hsum : ∀ j, ‖v j‖ ^ (2 : ℝ) = v j ^ 2 := fun j => by
    rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [discreteNorm, lp.norm_eq_tsum_rpow h2, Real.sqrt_eq_rpow]
  simp only [ENNReal.toReal_ofNat, one_div, ENNReal.toReal_inv, hsum]
  rw [← Real.mul_rpow hΔx (tsum_nonneg fun j => sq_nonneg _)]

/-- The discrete `L¹` norm: `‖v‖_{Δ,1} = Δx ∑_j |v_j|`. -/
theorem discreteNorm_one (Δx : ℝ) (v : lp (fun _ : ℤ => ℝ) 1) :
    discreteNorm 1 Δx v = Δx * ∑' j, |v j| := by
  have h1 : (0 : ℝ) < (1 : ℝ≥0∞).toReal := by norm_num
  rw [discreteNorm, lp.norm_eq_tsum_rpow h1]
  simp [Real.norm_eq_abs]

/-- **Stability of a family of schemes** ([quarteroni2000numerical] (13.46); the fixed-space form
is Definition 6.3.1 of [han2009theoretical]): for every horizon `T > 0` there are `C` and `δ₀ > 0`
such that `‖Q i ^ n‖ ≤ C` whenever the steps `Δt i`, `Δx i` lie in `(0, δ₀]` and `n Δt i ≤ T`. The
family of spaces `E i` is dependent so that periodic grids and the whole line are both instances;
with `E i` a space of grid functions and the discrete norm a constant multiple of the `ℓ^p` norm,
`‖Q i ^ n‖ ≤ C` is `‖uⁿ‖_Δ ≤ C ‖u⁰‖_Δ`. -/
def IsStableFamily {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] (Δt Δx : ι → ℝ) (Q : ∀ i, E i →L[ℝ] E i) : Prop :=
  ∀ T : ℝ, 0 < T → ∃ C δ₀ : ℝ, 0 < δ₀ ∧ ∀ i, 0 < Δt i → Δt i ≤ δ₀ → 0 < Δx i → Δx i ≤ δ₀ →
    ∀ n : ℕ, (n : ℝ) * Δt i ≤ T → ‖Q i ^ n‖ ≤ C

namespace IsStableFamily

variable {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  {Δt Δx : ι → ℝ} {Q : ∀ i, E i →L[ℝ] E i}

/-- A stable family satisfies `‖(Q i ^ n) u‖ ≤ C ‖u‖` for `n Δt i ≤ T` and small steps. -/
theorem norm_le_of_isStableFamily (h : IsStableFamily Δt Δx Q) {T : ℝ} (hT : 0 < T) :
    ∃ C δ₀ : ℝ, 0 < δ₀ ∧ ∀ i, 0 < Δt i → Δt i ≤ δ₀ → 0 < Δx i → Δx i ≤ δ₀ →
      ∀ n : ℕ, (n : ℝ) * Δt i ≤ T → ∀ u : E i, ‖(Q i ^ n) u‖ ≤ C * ‖u‖ := by
  obtain ⟨C, δ₀, hδ₀, hC⟩ := h T hT
  exact ⟨C, δ₀, hδ₀, fun i h1 h2 h3 h4 n hn u =>
    (Q i ^ n).le_of_opNorm_le (hC i h1 h2 h3 h4 n hn) u⟩

/-- **Convergence of each member of a stable family**: the error accumulation theorem
`FiniteDifference.norm_sub_le_of_stable` applies to every scheme of a stable family with `M₀ = C`,
so a two-level recursion whose exact values carry local truncation errors of size `δ` has error at
most `C T δ` over the horizon `T`. -/
theorem exists_norm_sub_le (h : IsStableFamily Δt Δx Q) {T : ℝ} (hT : 0 < T) :
    ∃ C δ₀ : ℝ, 0 < δ₀ ∧ ∀ i, 0 < Δt i → Δt i ≤ δ₀ → 0 < Δx i → Δx i ≤ δ₀ →
      ∀ {u v g τ : ℕ → E i} {δ : ℝ} {N : ℕ}, 0 ≤ δ → (N : ℝ) * Δt i ≤ T →
        (∀ m < N, v (m + 1) = Q i (v m) + Δt i • g m) →
        (∀ m < N, u (m + 1) = Q i (u m) + Δt i • g m + Δt i • τ m) → u 0 = v 0 →
        (∀ m < N, ‖τ m‖ ≤ δ) → ∀ m ≤ N, ‖u m - v m‖ ≤ C * T * δ := by
  obtain ⟨C, δ₀, hδ₀, hC⟩ := h T hT
  refine ⟨C, δ₀, hδ₀, fun i h1 h2 h3 h4 u v g τ δ N hδ hN hv hu h0 hτ m hm => ?_⟩
  refine norm_sub_le_of_stable h1.le hδ hN hv hu h0 (fun k hk => hC i h1 h2 h3 h4 k ?_) hτ hm
  exact le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) h1.le) hN

end IsStableFamily

end FiniteDifference

import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
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

import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Nonlinear.FixedPoint

/-!
# Atkinson–Han §5.1: the Banach fixed-point theorem

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §5.1: contractive mappings, the Banach
fixed-point theorem with its three error bounds, the variant in which only an iterate contracts,
and the Zarantonello theorem for a strongly monotone Lipschitz operator on a Hilbert space.

Every proof specializes a declaration of `Numlib/Nonlinear/FixedPoint.lean` or of Mathlib; the
work of the file is the dictionary between the book's `‖T u - T v‖ ≤ α ‖u - v‖` and Mathlib's
`LipschitzOnWith`/`ContractingWith`, which is what `contractiveOn_iff`, `lipschitzOn_iff` and
`ContractiveOn.contractingWith_restrict` supply.

## Book-specific definitions

* `ContractiveOn`, `NonExpansiveOn`, `LipschitzOn` — Definition 5.1.2, in the book's normed
  form. `ContractiveOn.nonExpansiveOn`, `NonExpansiveOn.lipschitzOn` and
  `LipschitzOn.continuousOn` are the chain contractive ⇒ non-expansive ⇒ Lipschitz ⇒ continuous
  that the definition is stated for.
* `StronglyMonotoneWith` — (5.1.8); `stronglyMonotoneWith_iff_isCoerciveWith` says that for a
  bounded *linear* operator this is the backbone's `LinearMap.IsCoerciveWith`.

## Main results

* `example_5_1_1`, `example_5_1_1_tendsto_iff` — Example 5.1.1, the closed form of the affine
  iteration `x ↦ a x + b` on `ℝ` and its convergence exactly when `|a| < 1`.
* `theorem_5_1_3` — **Banach fixed-point theorem**, assembled from
  `theorem_5_1_3_existsUnique`, `theorem_5_1_3_tendsto` and the error bounds `equation_5_1_4`
  (a priori), `equation_5_1_5` (a posteriori) and `equation_5_1_6` (linear rate).
* `example_5_1_2` — a continuous map one of whose iterates is contractive still has a unique
  fixed point; this is what Theorem 5.2.3 uses for the Volterra equation.
* `theorem_5_1_4` — a strongly monotone Lipschitz operator on a real Hilbert space is a
  bijection, with the stability estimate (5.1.11).

## Implementation notes

The book states §5.1 in a Banach space and Theorem 5.1.4 in a Hilbert space, but several of the
arguments are purely metric and do not touch the vector space structure. The section variables
carrying it are kept, because they are part of the book's setting, and the unused-section-variable
linter is turned off for the file rather than the statements being weakened.
-/

open Filter Metric Set Topology

namespace AtkinsonHan.Chapter05

-- See the implementation notes above: the section variables carrying the vector space structure
-- are unused in the purely metric arguments, and are kept because the book's setting has them.
set_option linter.unusedSectionVars false

section Banach

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Definition 5.1.2: `T` is **contractive** on `K` with contractivity constant `α`, that is
`0 ≤ α < 1` and `‖T u - T v‖ ≤ α ‖u - v‖` for all `u, v ∈ K`. -/
def ContractiveOn (T : V → V) (K : Set V) (α : ℝ) : Prop :=
  0 ≤ α ∧ α < 1 ∧ ∀ u ∈ K, ∀ v ∈ K, ‖T u - T v‖ ≤ α * ‖u - v‖

/-- Definition 5.1.2: `T` is **non-expansive** on `K`, the borderline case `α = 1` of
contractivity. -/
def NonExpansiveOn (T : V → V) (K : Set V) : Prop :=
  ∀ u ∈ K, ∀ v ∈ K, ‖T u - T v‖ ≤ ‖u - v‖

/-- Definition 5.1.2: `T` is **Lipschitz** on `K`, that is `‖T u - T v‖ ≤ L ‖u - v‖` for some
Lipschitz constant `L ≥ 0`. -/
def LipschitzOn (T : V → V) (K : Set V) : Prop :=
  ∃ L : ℝ, 0 ≤ L ∧ ∀ u ∈ K, ∀ v ∈ K, ‖T u - T v‖ ≤ L * ‖u - v‖

variable {T : V → V} {K : Set V} {α : ℝ}

namespace ContractiveOn

/-- A contractivity constant is nonnegative. -/
theorem nonneg (h : ContractiveOn T K α) : 0 ≤ α := h.1

/-- A contractivity constant is smaller than `1`. -/
theorem lt_one (h : ContractiveOn T K α) : α < 1 := h.2.1

/-- The contraction estimate `‖T u - T v‖ ≤ α ‖u - v‖` of Definition 5.1.2. -/
theorem norm_sub_le (h : ContractiveOn T K α) {u v : V} (hu : u ∈ K) (hv : v ∈ K) :
    ‖T u - T v‖ ≤ α * ‖u - v‖ := h.2.2 u hu v hv

/-- The contractivity hypothesis in the metric form taken by the backbone
(`Numlib/Nonlinear/FixedPoint.lean`). -/
theorem dist_le (h : ContractiveOn T K α) :
    ∀ u ∈ K, ∀ v ∈ K, dist (T u) (T v) ≤ α * dist u v := fun _ hu _ hv => by
  simpa only [dist_eq_norm] using h.norm_sub_le hu hv

/-- Contractive maps are non-expansive (Definition 5.1.2). -/
theorem nonExpansiveOn (h : ContractiveOn T K α) : NonExpansiveOn T K := fun _ hu _ hv =>
  (h.norm_sub_le hu hv).trans (mul_le_of_le_one_left (norm_nonneg _) h.lt_one.le)

/-- Identification with Mathlib's `LipschitzOnWith`. -/
theorem contractingWith_restrict (h : ContractiveOn T K α) (hT : MapsTo T K K) :
    ContractingWith ⟨α, h.nonneg⟩ (hT.restrict T K K) := by
  refine ⟨?_, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  · exact_mod_cast h.lt_one
  · exact h.dist_le _ x.2 _ y.2

end ContractiveOn

/-- Identification of Definition 5.1.2 with Mathlib's `LipschitzOnWith`. -/
theorem contractiveOn_iff (hα : 0 ≤ α) :
    ContractiveOn T K α ↔ α < 1 ∧ LipschitzOnWith ⟨α, hα⟩ T K := by
  refine ⟨fun h => ⟨h.lt_one, lipschitzOnWith_iff_norm_sub_le.2 fun _ hx _ hy => ?_⟩,
    fun h => ⟨hα, h.1, fun _ hx _ hy => ?_⟩⟩
  · exact h.norm_sub_le hx hy
  · exact lipschitzOnWith_iff_norm_sub_le.1 h.2 hx hy

/-- Non-expansive maps are Lipschitz (Definition 5.1.2). -/
theorem NonExpansiveOn.lipschitzOn (h : NonExpansiveOn T K) : LipschitzOn T K :=
  ⟨1, zero_le_one, fun u hu v hv => by simpa using h u hu v hv⟩

/-- Identification of Definition 5.1.2 with Mathlib's `LipschitzOnWith`. -/
theorem lipschitzOn_iff : LipschitzOn T K ↔ ∃ L : NNReal, LipschitzOnWith L T K := by
  constructor
  · rintro ⟨L, hL, h⟩
    exact ⟨⟨L, hL⟩, lipschitzOnWith_iff_norm_sub_le.2 fun _ hx _ hy => h _ hx _ hy⟩
  · rintro ⟨L, h⟩
    exact ⟨L, L.coe_nonneg, fun _ hx _ hy => lipschitzOnWith_iff_norm_sub_le.1 h hx hy⟩

/-- Lipschitz maps are continuous (Definition 5.1.2). -/
theorem LipschitzOn.continuousOn (h : LipschitzOn T K) : ContinuousOn T K := by
  obtain ⟨L, hL⟩ := lipschitzOn_iff.1 h
  exact hL.continuousOn

section ScalarExample

/-- Example 5.1.1: the affine iteration `x ↦ a x + b` on `ℝ` has the closed form
`x_n = aⁿ x₀ + (1 - aⁿ)/(1 - a) b` when `a ≠ 1`. -/
theorem example_5_1_1 {a : ℝ} (ha : a ≠ 1) (b x₀ : ℝ) (n : ℕ) :
    (fun x => a * x + b)^[n] x₀ = a ^ n * x₀ + (1 - a ^ n) / (1 - a) * b := by
  have h1 : (1 : ℝ) - a ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    field_simp
    ring

/-- Example 5.1.1: for `a ≠ 1` the affine iteration converges from every starting point if and
only if `|a| < 1`. -/
theorem example_5_1_1_tendsto_iff {a : ℝ} (ha : a ≠ 1) (b : ℝ) :
    (∀ x₀ : ℝ, ∃ x, Tendsto (fun n => (fun x => a * x + b)^[n] x₀) atTop (𝓝 x)) ↔ |a| < 1 := by
  have h1 : (1 : ℝ) - a ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
  constructor
  · intro hconv
    obtain ⟨x, hx⟩ := hconv 1
    obtain ⟨y, hy⟩ := hconv 0
    have heq : (fun n : ℕ => (fun x => a * x + b)^[n] 1 - (fun x => a * x + b)^[n] 0)
        = fun n => a ^ n := by
      funext n
      rw [example_5_1_1 ha, example_5_1_1 ha]
      ring
    have hd : Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 (x - y)) := heq ▸ hx.sub hy
    have hs : Tendsto (fun n : ℕ => a ^ (n + 1)) atTop (𝓝 (x - y)) :=
      hd.comp (tendsto_add_atTop_nat 1)
    have hs' : Tendsto (fun n : ℕ => a ^ (n + 1)) atTop (𝓝 (a * (x - y))) := by
      simpa only [pow_succ, mul_comm] using hd.const_mul a
    have hfix : (1 - a) * (x - y) = 0 := by
      linear_combination tendsto_nhds_unique hs hs'
    have hxy : x - y = 0 := by
      rcases mul_eq_zero.1 hfix with h | h
      · exact absurd h h1
      · exact h
    rw [hxy] at hd
    exact tendsto_pow_atTop_nhds_zero_iff.1 hd
  · intro haa x₀
    refine ⟨b / (1 - a), ?_⟩
    have hz : Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_iff.2 haa
    have hlim := (hz.mul_const x₀).add
      (((tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).sub hz).div_const
        (1 - a) |>.mul_const b)
    have hgoal : b / (1 - a) = 0 * x₀ + (1 - 0) / (1 - a) * b := by ring
    rw [hgoal]
    simp only [example_5_1_1 ha]
    exact hlim

end ScalarExample

section Complete

variable [CompleteSpace V]

/-- Theorem 5.1.3(a): a contractive self-map of a nonempty closed subset of a Banach space has a
unique fixed point there. -/
theorem theorem_5_1_3_existsUnique (hK : IsClosed K) (hne : K.Nonempty) (hT : MapsTo T K K)
    (hα : ContractiveOn T K α) : ∃! u, u ∈ K ∧ T u = u :=
  exists_unique_fixedPoint_of_mapsTo hK hne hT hα.nonneg hα.lt_one hα.dist_le

/-- (5.1.4): the a priori bound `‖u_n - u‖ ≤ αⁿ/(1 - α) ‖u₀ - u₁‖`. -/
theorem equation_5_1_4 (hK : IsClosed K) (hT : MapsTo T K K) (hα : ContractiveOn T K α) {u : V}
    (hu : u ∈ K) (hfix : T u = u) {u₀ : V} (hu₀ : u₀ ∈ K) (n : ℕ) :
    ‖T^[n] u₀ - u‖ ≤ α ^ n / (1 - α) * ‖u₀ - T u₀‖ := by
  have h := dist_iterate_le_of_mapsTo hK hT hα.nonneg hα.lt_one hα.dist_le hu hfix hu₀ n
  rwa [dist_eq_norm, dist_eq_norm, norm_sub_rev (T u₀)] at h

/-- The one-step form of (5.1.5), stated for a point `a` of `K` with `T a ∈ K`. -/
private theorem norm_step_sub_fixed_le (hα : ContractiveOn T K α) {u : V} (hu : u ∈ K)
    (hfix : T u = u) {a : V} (ha : a ∈ K) (hTa : T a ∈ K) :
    ‖T a - u‖ ≤ α / (1 - α) * ‖a - T a‖ := by
  have h1 : ‖T a - u‖ ≤ ‖T a - T (T a)‖ + ‖T (T a) - u‖ := by
    simpa only [dist_eq_norm] using dist_triangle (T a) (T (T a)) u
  have h2 : ‖T a - T (T a)‖ ≤ α * ‖a - T a‖ := hα.norm_sub_le ha hTa
  have h3 : ‖T (T a) - u‖ ≤ α * ‖T a - u‖ := by
    have h := hα.norm_sub_le hTa hu
    rwa [hfix] at h
  have hlt : 0 < 1 - α := by linarith [hα.lt_one]
  rw [div_mul_eq_mul_div, le_div_iff₀ hlt]
  linarith

/-- (5.1.5): the a posteriori bound `‖u_{n+1} - u‖ ≤ α/(1 - α) ‖u_n - u_{n+1}‖`. -/
theorem equation_5_1_5 (hT : MapsTo T K K) (hα : ContractiveOn T K α) {u : V} (hu : u ∈ K)
    (hfix : T u = u) {u₀ : V} (hu₀ : u₀ ∈ K) (n : ℕ) :
    ‖T^[n + 1] u₀ - u‖ ≤ α / (1 - α) * ‖T^[n] u₀ - T^[n + 1] u₀‖ := by
  rw [Function.iterate_succ_apply']
  exact norm_step_sub_fixed_le hα hu hfix (hT.iterate n hu₀) (hT (hT.iterate n hu₀))

/-- (5.1.6): the linear rate `‖u_{n+1} - u‖ ≤ α ‖u_n - u‖`. -/
theorem equation_5_1_6 (hT : MapsTo T K K) (hα : ContractiveOn T K α) {u : V} (hu : u ∈ K)
    (hfix : T u = u) {u₀ : V} (hu₀ : u₀ ∈ K) (n : ℕ) :
    ‖T^[n + 1] u₀ - u‖ ≤ α * ‖T^[n] u₀ - u‖ := by
  have h := hα.norm_sub_le (hT.iterate n hu₀) hu
  rw [hfix] at h
  rwa [Function.iterate_succ_apply']

/-- Theorem 5.1.3(b): the fixed-point iteration converges to the fixed point from every starting
point of `K`. -/
theorem theorem_5_1_3_tendsto (hK : IsClosed K) (hT : MapsTo T K K) (hα : ContractiveOn T K α)
    {u : V} (hu : u ∈ K) (hfix : T u = u) {u₀ : V} (hu₀ : u₀ ∈ K) :
    Tendsto (fun n => T^[n] u₀) atTop (𝓝 u) := by
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => equation_5_1_4 hK hT hα hu hfix hu₀ n) ?_
  have h1 : Tendsto (fun n : ℕ => α ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hα.nonneg hα.lt_one
  simpa using (h1.div_const (1 - α)).mul_const ‖u₀ - T u₀‖

/-- **Theorem 5.1.3** (Banach fixed-point theorem).  Let `K` be a nonempty closed subset of a
Banach space `V` and let `T : K → K` be contractive with constant `α ∈ [0, 1)`.  Then `T` has a
unique fixed point in `K`, the iteration `u_{n+1} = T u_n` converges to it from every `u₀ ∈ K`,
and the errors obey (5.1.4), (5.1.5) and (5.1.6). -/
theorem theorem_5_1_3 (hK : IsClosed K) (hne : K.Nonempty) (hT : MapsTo T K K)
    (hα : ContractiveOn T K α) :
    (∃! u, u ∈ K ∧ T u = u) ∧
      ∀ u₀ ∈ K, ∃ u ∈ K, T u = u ∧ Tendsto (fun n => T^[n] u₀) atTop (𝓝 u) ∧
        (∀ n, ‖T^[n] u₀ - u‖ ≤ α ^ n / (1 - α) * ‖u₀ - T u₀‖) ∧
        (∀ n, ‖T^[n + 1] u₀ - u‖ ≤ α / (1 - α) * ‖T^[n] u₀ - T^[n + 1] u₀‖) ∧
        (∀ n, ‖T^[n + 1] u₀ - u‖ ≤ α * ‖T^[n] u₀ - u‖) := by
  obtain ⟨u, ⟨hu, hfix⟩, -⟩ := theorem_5_1_3_existsUnique hK hne hT hα
  exact ⟨theorem_5_1_3_existsUnique hK hne hT hα, fun u₀ hu₀ =>
    ⟨u, hu, hfix, theorem_5_1_3_tendsto hK hT hα hu hfix hu₀,
      fun n => equation_5_1_4 hK hT hα hu hfix hu₀ n, fun n => equation_5_1_5 hT hα hu hfix hu₀ n,
      fun n => equation_5_1_6 hT hα hu hfix hu₀ n⟩⟩

/-- **Example 5.1.2** (cited by Theorem 5.2.3): if `T : K → K` is continuous and some iterate
`T^[m]`, `m ≥ 1`, is contractive on `K`, then `T` still has a unique fixed point in `K` and
`u_{n+1} = T u_n` converges to it from every `u₀ ∈ K`. -/
theorem example_5_1_2 (hK : IsClosed K) (hne : K.Nonempty) (hT : MapsTo T K K)
    (hc : ContinuousOn T K) {m : ℕ} (hm : 0 < m) (hα : ContractiveOn T^[m] K α) :
    (∃! u, u ∈ K ∧ T u = u) ∧
      ∀ u₀ ∈ K, ∃ u ∈ K, T u = u ∧ Tendsto (fun n => T^[n] u₀) atTop (𝓝 u) := by
  have hcomplete : CompleteSpace K := hK.completeSpace_coe
  have hnonempty : Nonempty K := hne.to_subtype
  have hcont : Continuous (hT.restrict T K K) := hc.mapsToRestrict hT
  have hcw : ContractingWith ⟨α, hα.nonneg⟩ (hT.restrict T K K)^[m] := by
    rw [hT.iterate_restrict m]
    exact hα.contractingWith_restrict (hT.iterate m)
  have hkey : ∀ x : K, hT.restrict T K K x = x ↔ T (x : V) = (x : V) := fun x => by
    rw [Subtype.ext_iff, MapsTo.val_restrict_apply]
  constructor
  · obtain ⟨x, hx, hxu⟩ := exists_unique_fixedPoint_of_iterate_contractingWith hcont hm hcw
    refine ⟨(x : V), ⟨x.2, (hkey x).1 hx⟩, ?_⟩
    rintro y ⟨hy, hfy⟩
    exact congrArg Subtype.val (hxu ⟨y, hy⟩ ((hkey ⟨y, hy⟩).2 hfy))
  · intro u₀ hu₀
    obtain ⟨x, hx, htend⟩ :=
      tendsto_iterate_of_iterate_contractingWith hcont hm hcw ⟨u₀, hu₀⟩
    refine ⟨(x : V), x.2, (hkey x).1 hx, ?_⟩
    have h := (continuous_subtype_val.tendsto x).comp htend
    simpa only [Function.comp_def, MapsTo.coe_iterate_restrict] using h

end Complete

end Banach

section Hilbert

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- (5.1.8): `T` is **strongly monotone** with constant `c`, that is
`(T v₁ - T v₂, v₁ - v₂) ≥ c ‖v₁ - v₂‖²` on a real Hilbert space. -/
def StronglyMonotoneWith (T : V → V) (c : ℝ) : Prop :=
  ∀ v₁ v₂, c * ‖v₁ - v₂‖ ^ 2 ≤ inner ℝ (T v₁ - T v₂) (v₁ - v₂)

/-- Identification of (5.1.8) with the hypothesis of the backbone's `zarantonello`
(`Numlib/Nonlinear/FixedPoint.lean`). -/
theorem stronglyMonotoneWith_iff {T : V → V} {c : ℝ} :
    StronglyMonotoneWith T c ↔
      ∀ x y, c * ‖x - y‖ ^ 2 ≤ RCLike.re (inner ℝ (T x - T y) (x - y)) := by
  simp only [StronglyMonotoneWith, RCLike.re_to_real]

/-- For a bounded linear operator, strong monotonicity is coercivity
(`LinearMap.IsCoerciveWith`, `Numlib/Analysis/InnerProductSpace/Coercive.lean`). -/
theorem stronglyMonotoneWith_iff_isCoerciveWith (A : V →L[ℝ] V) (c : ℝ) :
    StronglyMonotoneWith (A : V → V) c ↔ (A : V →ₗ[ℝ] V).IsCoerciveWith c := by
  constructor
  · intro h x
    simpa [RCLike.re_to_real] using h x 0
  · intro h v₁ v₂
    have hv := h (v₁ - v₂)
    rw [RCLike.re_to_real] at hv
    simpa only [map_sub, ContinuousLinearMap.coe_coe] using hv

/-- Identification of (5.1.9) with Mathlib's `LipschitzWith`. -/
theorem lipschitzWith_toNNReal_iff {T : V → V} {c : ℝ} (hc : 0 ≤ c) :
    (∀ v₁ v₂, ‖T v₁ - T v₂‖ ≤ c * ‖v₁ - v₂‖) ↔ LipschitzWith (Real.toNNReal c) T := by
  rw [lipschitzWith_iff_norm_sub_le]
  simp [Real.coe_toNNReal _ hc]

/-- **Theorem 5.1.4**.  Let `V` be a real Hilbert space and `T : V → V` strongly monotone (5.1.8)
with constant `c₁ > 0` and Lipschitz (5.1.9) with constant `c₂ > 0`.  Then `T` is a bijection —
(5.1.10) `T u = b` has a unique solution for every `b` — and the solution depends Lipschitz
continuously on the data, (5.1.11) `‖u₁ - u₂‖ ≤ (1/c₁) ‖b₁ - b₂‖`. -/
theorem theorem_5_1_4 {T : V → V} {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hmono : StronglyMonotoneWith T c₁) (hlip : ∀ v₁ v₂, ‖T v₁ - T v₂‖ ≤ c₂ * ‖v₁ - v₂‖) :
    (∀ b, ∃! u, T u = b) ∧
      ∀ u₁ u₂ b₁ b₂, T u₁ = b₁ → T u₂ = b₂ → ‖u₁ - u₂‖ ≤ 1 / c₁ * ‖b₁ - b₂‖ := by
  have hm := stronglyMonotoneWith_iff.1 hmono
  refine ⟨fun b => zarantonello (𝕜 := ℝ) hc₁ hm ((lipschitzWith_toNNReal_iff hc₂.le).1 hlip) b,
    fun u₁ u₂ b₁ b₂ h₁ h₂ => ?_⟩
  have h := norm_sub_le_of_strongly_monotone (𝕜 := ℝ) hc₁ hm h₁ h₂
  rwa [one_div, inv_mul_eq_div]

end Hilbert

end AtkinsonHan.Chapter05

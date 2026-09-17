import Mathlib.Analysis.InnerProductSpace.l2Space
import Numlib.Analysis.Normed.Lp.Sequence
import NumlibSurface.Brezis.Chapter04.Section05

/-!
# Brezis §11.3: some classical spaces of sequences

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §11.3, over `ℝ`. The book's `ℓ^p`, `1 ≤ p ≤ ∞`, is
Mathlib's `lp (fun _ : ℕ ↦ ℝ) p` (indices from `0` rather than `1`, a relabelling that changes
nothing), with its norm, completeness (`lp.completeSpace`), Hölder's inequality and the Hilbert
structure of `ℓ²` (`lp.instInnerProductSpace`); `c` and `c₀` are the backbone's
`lp.convergent ℝ ℝ` and `lp.zeroAtInfty ℝ ℝ`, closed subspaces of `ℓ^∞`
(`Numlib/Analysis/Normed/Lp/Sequence`), and Propositions 11.15–11.21 are that module's theorems
read at `𝕜 = ℝ` and index type `ℕ`. Reflexivity of `ℓ^p` is proved there directly from the
duality of Proposition 11.18 (the book applies Theorem 4.10 to the counting measure), uniform
convexity by the book's own route, chapter 4's `L^p` result transported along
`lp.lpLIELpCount`. The closing table of the section is the content of 11.15–11.21; its last
entry, "`(ℓ^∞)^*` strictly bigger than `ℓ¹`", is not a numbered claim and has no node.

## Main results

* `lpNorm_eq`, `lp_completeSpace`, `mem_c_iff`, `c₀_le_c_isClosed`, `holder_lp`, `l2_inner`,
  `lp_subset_c₀`, `lp_subset_lq` — the definitions and elementary facts of the section.
* `proposition_11_15` — `ℓ^p` is reflexive and uniformly convex for `1 < p < ∞`.
* `proposition_11_16`, `proposition_11_17` — `c`, `c₀`, `ℓ^p` (`p < ∞`) are separable, `ℓ^∞` is
  not.
* `proposition_11_18`, `proposition_11_19`, `proposition_11_20` — the duals `(ℓ^p)^* = ℓ^{p'}`,
  `(c₀)^* = ℓ¹`, `c^* = ℓ¹ × ℝ`.
* `proposition_11_21` — `ℓ¹`, `ℓ^∞`, `c`, `c₀` are not reflexive.
-/

open Filter Topology
open scoped ENNReal InnerProductSpace

namespace Brezis.Chapter11

/-- The book's `ℓ^p`. -/
local notation "ℓ^" p => lp (fun _ : ℕ => ℝ) p

/-! ### The definitions -/

/-- **The definition of `ℓ^p` and `ℓ^∞`.** For `x : ℓ^p` with `1 ≤ p < ∞`,
`‖x‖_p = (∑ |x_k| ^ p) ^ (1 / p)`, and a sequence belongs to `ℓ^p` iff `∑ |x_k| ^ p < ∞`; for
`p = ∞`, `‖x‖_∞ = sup_k |x_k|`, and a sequence belongs to `ℓ^∞` iff it is bounded. -/
theorem lpNorm_eq {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    (∀ x : ℓ^p, ‖x‖ = (∑' k, |x k| ^ p.toReal) ^ (1 / p.toReal)) ∧
    (∀ x : ℕ → ℝ, Memℓp x p ↔ Summable fun k => |x k| ^ p.toReal) ∧
    (∀ x : ℓ^∞, ‖x‖ = ⨆ k, |x k|) ∧
    ∀ x : ℕ → ℝ, Memℓp x ∞ ↔ BddAbove (Set.range fun k => |x k|) := by
  have hP : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp
  exact ⟨fun x => by simpa only [Real.norm_eq_abs] using lp.norm_eq_tsum_rpow hP x,
    fun x => by simpa only [Real.norm_eq_abs] using memℓp_gen_iff (f := x) hP,
    fun x => by simpa only [Real.norm_eq_abs] using lp.norm_eq_ciSup x,
    fun x => by simpa only [Real.norm_eq_abs] using memℓp_infty_iff (f := x)⟩

/-- **"Which are Banach spaces for the `ℓ^p` (resp. `ℓ^∞`) norms."** `ℓ^p` is complete,
`1 ≤ p ≤ ∞` (Mathlib's `lp.completeSpace`, the "direct and quite easy" proof; the route through
Theorem 4.8 on the counting measure is the backbone's `lp.lpLIELpCount`). -/
theorem lp_completeSpace {p : ℝ≥0∞} [Fact (1 ≤ p)] : CompleteSpace (ℓ^p) := inferInstance

/-- **The spaces `c` and `c₀`.** `c = {x ; lim x_k exists}` and `c₀ = {x ; lim x_k = 0}`, both
subspaces of `ℓ^∞` with the `ℓ^∞` norm. -/
theorem mem_c_iff (x : ℓ^∞) :
    (x ∈ lp.convergent ℝ ℝ ↔ ∃ l : ℝ, Tendsto (fun k => x k) atTop (𝓝 l)) ∧
    (x ∈ lp.zeroAtInfty ℝ ℝ ↔ Tendsto (fun k => x k) atTop (𝓝 0)) :=
  ⟨lp.mem_convergent, lp.mem_zeroAtInfty⟩

/-- **"Clearly `c₀ ⊂ c ⊂ ℓ^∞` with `c₀` closed in `c`, and `c` closed in `ℓ^∞`."** -/
theorem c₀_le_c_isClosed :
    lp.zeroAtInfty ℝ ℝ ≤ lp.convergent ℝ ℝ ∧ IsClosed (lp.convergent ℝ ℝ : Set (ℓ^∞)) ∧
      IsClosed (lp.zeroAtInfty ℝ ℝ : Set (ℓ^∞)) :=
  ⟨lp.zeroAtInfty_le_convergent ℝ ℝ, lp.isClosed_convergent ℝ ℝ, lp.isClosed_zeroAtInfty ℝ ℝ⟩

/-- **Hölder's inequality in `ℓ^p`.** For conjugate exponents `p, p'` (`1 ≤ p ≤ ∞`), `x ∈ ℓ^p`
and `y ∈ ℓ^{p'}`, the series `∑ x_k y_k` converges and `|∑ x_k y_k| ≤ ‖x‖_p ‖y‖_{p'}`. -/
theorem holder_lp {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q] (x : ℓ^p)
    (y : ℓ^q) : (Summable fun k => x k * y k) ∧ |∑' k, x k * y k| ≤ ‖x‖ * ‖y‖ := by
  refine ⟨?_, ?_⟩
  · have h : Memℓp (fun k => ContinuousLinearMap.mul ℝ ℝ (x k) (y k)) 1 :=
      (lp.memℓp x).holder 1 (lp.memℓp y) (fun _ => ContinuousLinearMap.mul ℝ ℝ) (K := 1)
        fun _ => ContinuousLinearMap.opNorm_mul_le ℝ ℝ
    exact h.summable_of_one
  · have h := (lp.toDualCLM ℝ ℕ p q y).le_opNorm x
    rw [lp.toDualCLM_apply, lp.norm_toDualCLM_apply, Real.norm_eq_abs] at h
    rw [mul_comm ‖x‖]
    refine le_trans (le_of_eq ?_) h
    congr 1
    exact tsum_congr fun k => mul_comm _ _

/-- **"The space `ℓ²` is a Hilbert space equipped with the scalar product `(x, y) = ∑ x_k y_k`."**
-/
theorem l2_inner :
    (∀ x y : ℓ^2, ⟪x, y⟫_ℝ = ∑' k, x k * y k) ∧ CompleteSpace (ℓ^2) :=
  ⟨fun x y => by
    rw [lp.inner_eq_tsum]
    exact tsum_congr fun k => by simp [mul_comm], inferInstance⟩

/-- **"It is clear that `ℓ^p ⊂ c₀` with `‖x‖_∞ ≤ ‖x‖_p`, `1 ≤ p < ∞`."** The inclusion is
Mathlib's `lp.linearMapOfLE`; its image lies in `c₀` and it does not increase the norm. -/
theorem lp_subset_c₀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) (x : ℓ^p) :
    lp.linearMapOfLE ℝ (fun _ : ℕ => ℝ) le_top x ∈ lp.zeroAtInfty ℝ ℝ ∧
      ‖lp.linearMapOfLE ℝ (fun _ : ℕ => ℝ) le_top x‖ ≤ ‖x‖ ∧ ∀ k, |x k| ≤ ‖x‖ :=
  ⟨lp.linearMapOfLE_mem_zeroAtInfty ℝ hp x,
    lp.norm_linearMapOfLE_le ℝ (zero_lt_one.trans_le Fact.out).ne' le_top x,
    fun k => by simpa only [Real.norm_eq_abs] using
      lp.norm_apply_le_norm (zero_lt_one.trans_le Fact.out).ne' x k⟩

/-- **"`ℓ^p ⊂ ℓ^q` when `1 ≤ p ≤ q ≤ ∞`, with `‖x‖_q ≤ ‖x‖_p`."** -/
theorem lp_subset_lq {p q : ℝ≥0∞} [Fact (1 ≤ p)] (h : p ≤ q) (x : ℓ^p) :
    Memℓp (⇑x) q ∧ ‖lp.linearMapOfLE ℝ (fun _ : ℕ => ℝ) h x‖ ≤ ‖x‖ :=
  ⟨(lp.memℓp x).of_exponent_ge h,
    lp.norm_linearMapOfLE_le ℝ (zero_lt_one.trans_le Fact.out).ne' h x⟩

/-! ### Propositions 11.15–11.17 -/

/-- **Proposition 11.15, first clause.** `ℓ^p` is reflexive for `1 < p < ∞`. -/
theorem proposition_11_15_reflexive {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ∞) :
    NormedSpace.IsReflexive ℝ (ℓ^p) :=
  lp.isReflexive ℝ ℕ hp hp'

/-- **Proposition 11.15, second clause.** `ℓ^p` is uniformly convex for `1 < p < ∞`. -/
theorem proposition_11_15_uniformConvex {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ∞) :
    UniformConvexSpace (ℓ^p) := by
  have := Fact.mk hp
  have := Fact.mk hp'
  exact lp.uniformConvexSpace

/-- **Proposition 11.15.** `ℓ^p` is reflexive, and even uniformly convex, for `1 < p < ∞`. -/
theorem proposition_11_15 {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ∞) :
    NormedSpace.IsReflexive ℝ (ℓ^p) ∧ UniformConvexSpace (ℓ^p) :=
  ⟨proposition_11_15_reflexive hp hp', proposition_11_15_uniformConvex hp hp'⟩

/-- **Proposition 11.16.** The spaces `c`, `c₀` and `ℓ^p`, `1 ≤ p < ∞`, are separable. -/
theorem proposition_11_16 :
    TopologicalSpace.SeparableSpace (lp.convergent ℝ ℝ) ∧
    TopologicalSpace.SeparableSpace (lp.zeroAtInfty ℝ ℝ) ∧
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ → TopologicalSpace.SeparableSpace (ℓ^p) :=
  ⟨inferInstance, inferInstance, fun _ _ hp => lp.separableSpace (𝕜 := ℝ) hp⟩

/-- **Proposition 11.17.** `ℓ^∞` is not separable. -/
theorem proposition_11_17 : ¬ TopologicalSpace.SeparableSpace (ℓ^∞) :=
  lp.not_separableSpace_top

/-! ### Propositions 11.18–11.20: the duals -/

/-- **Proposition 11.18.** Let `1 ≤ p < ∞` with conjugate exponent `p'`. Every
`φ ∈ (ℓ^p)^*` is `x ↦ ∑ u_k x_k` for a unique `u ∈ ℓ^{p'}`, and `‖u‖_{p'} = ‖φ‖`. -/
theorem proposition_11_18 {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (hp : p ≠ ∞) (φ : StrongDual ℝ (ℓ^p)) :
    ∃! u : ℓ^q, (∀ x : ℓ^p, φ x = ∑' k, u k * x k) ∧ ‖u‖ = ‖φ‖ := by
  obtain ⟨u, hu⟩ := lp.toDual_surjective (𝕜 := ℝ) (α := ℕ) (p := p) (q := q) hp φ
  refine ⟨u, ⟨fun x => by rw [← hu, lp.toDual_apply], by rw [← hu, LinearIsometry.norm_map]⟩,
    fun v ⟨hv, _⟩ => (lp.toDual ℝ ℕ p q).injective ?_⟩
  rw [hu]
  ext x
  rw [lp.toDual_apply, hv x]

/-- **Proposition 11.19.** Every `φ ∈ (c₀)^*` is `x ↦ ∑ u_k x_k` for a unique `u ∈ ℓ¹`, and
`‖u‖_1 = ‖φ‖`. -/
theorem proposition_11_19 (φ : StrongDual ℝ (lp.zeroAtInfty ℝ ℝ)) :
    ∃! u : ℓ^1, (∀ x : lp.zeroAtInfty ℝ ℝ, φ x = ∑' k, u k * (x : ℓ^∞) k) ∧ ‖u‖ = ‖φ‖ := by
  obtain ⟨u, hu⟩ := lp.zeroAtInfty.toDual_surjective (𝕜 := ℝ) φ
  refine ⟨u, ⟨fun x => by rw [← hu, lp.zeroAtInfty.toDual_apply],
    by rw [← hu, LinearIsometry.norm_map]⟩, fun v ⟨hv, _⟩ => (lp.zeroAtInfty.toDual ℝ).injective ?_⟩
  rw [hu]
  ext x
  rw [lp.zeroAtInfty.toDual_apply, hv x]

/-- **Proposition 11.20.** Every `φ ∈ c^*` is `x ↦ ∑ u_k x_k + λ lim x_k` for a unique pair
`(u, λ) ∈ ℓ¹ × ℝ`, and `‖u‖_1 + |λ| = ‖φ‖`. -/
theorem proposition_11_20 (φ : StrongDual ℝ (lp.convergent ℝ ℝ)) :
    ∃! ul : (ℓ^1) × ℝ, (∀ x : lp.convergent ℝ ℝ,
      φ x = ∑' k, ul.1 k * (x : ℓ^∞) k + ul.2 * lp.convergent.limCLM ℝ ℝ x) ∧
      ‖ul.1‖ + |ul.2| = ‖φ‖ := by
  obtain ⟨w, hw⟩ := lp.convergent.toDual_surjective (𝕜 := ℝ) φ
  obtain ⟨⟨u, l⟩⟩ := w
  refine ⟨(u, l), ⟨fun x => by rw [← hw, lp.convergent.toDual_apply],
    by rw [← hw, LinearIsometry.norm_map, lp.norm_toLp_one_prod, Real.norm_eq_abs]⟩,
    fun ⟨v, m⟩ ⟨hv, _⟩ => ?_⟩
  have : WithLp.toLp 1 (v, m) = WithLp.toLp 1 (u, l) := by
    refine (lp.convergent.toDual ℝ).injective ?_
    rw [hw]
    ext x
    rw [lp.convergent.toDual_apply, hv x]
  exact congrArg WithLp.ofLp this

/-! ### Proposition 11.21 -/

/-- **Proposition 11.21, `c₀`.** `c₀` is not reflexive. -/
theorem proposition_11_21_c₀ : ¬ NormedSpace.IsReflexive ℝ (lp.zeroAtInfty ℝ ℝ) :=
  lp.zeroAtInfty.not_isReflexive ℝ

/-- **Proposition 11.21, `ℓ¹`.** `ℓ¹` is not reflexive. -/
theorem proposition_11_21_one : ¬ NormedSpace.IsReflexive ℝ (ℓ^1) :=
  lp.not_isReflexive_one ℝ

/-- **Proposition 11.21, `ℓ^∞`.** `ℓ^∞` is not reflexive. -/
theorem proposition_11_21_top : ¬ NormedSpace.IsReflexive ℝ (ℓ^∞) :=
  lp.not_isReflexive_top ℝ

/-- **Proposition 11.21, `c`.** `c` is not reflexive. -/
theorem proposition_11_21_c : ¬ NormedSpace.IsReflexive ℝ (lp.convergent ℝ ℝ) :=
  lp.convergent.not_isReflexive ℝ

/-- **Proposition 11.21.** The spaces `ℓ¹`, `ℓ^∞`, `c` and `c₀` are not reflexive. -/
theorem proposition_11_21 :
    ¬ NormedSpace.IsReflexive ℝ (ℓ^1) ∧ ¬ NormedSpace.IsReflexive ℝ (ℓ^∞) ∧
      ¬ NormedSpace.IsReflexive ℝ (lp.convergent ℝ ℝ) ∧
      ¬ NormedSpace.IsReflexive ℝ (lp.zeroAtInfty ℝ ℝ) :=
  ⟨proposition_11_21_one, proposition_11_21_top, proposition_11_21_c, proposition_11_21_c₀⟩

end Brezis.Chapter11

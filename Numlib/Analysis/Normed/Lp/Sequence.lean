/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Lp.lpSpace` / `Mathlib.Analysis.Normed.Lp.lpHolder` (the
subspaces `c`, `c₀` and the duality) and `Mathlib.MeasureTheory.Function.LpSpace.Basic` (the
counting-measure bridge).
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.MeasureTheory.Function.LpSeminorm.Count
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Numlib.Analysis.Convex.Uniform
import Numlib.Analysis.Normed.Module.Reflexive.Kakutani
import Numlib.MeasureTheory.Function.LpSpace.Clarkson

/-!
# The classical sequence spaces `ℓ^p`, `c` and `c₀`

The sequence spaces of [brezis2011functional] §11.3 beyond what Mathlib's
`Mathlib.Analysis.Normed.Lp.lpSpace` and `lpHolder` provide. Mathlib's `lp (fun _ : α ↦ E) p`
(`Memℓp`, `lp.completeSpace`, `lp.instNormedSpace`, Hölder's inequality `lp.tsum_mul_le_mul_norm`,
the pairing `lp.dualPairing`, `lp.norm_apply_le_norm`, `lp.hasSum_single`) is the space `ℓ^p`;
this module adds:

* **The subspaces `c` and `c₀` of `ℓ^∞(ℕ, E)`**: `lp.convergent 𝕜 E` (the sequences with a limit)
  and `lp.zeroAtInfty 𝕜 E` (the null sequences), as closed submodules of `lp (fun _ : ℕ ↦ E) ∞`,
  with `c₀ ≤ c`, the limit functional `lp.convergent.limCLM`, and the bridge
  `lp.zeroAtInftyLIE : c₀ ≃ₗᵢ[𝕜] C₀(ℕ, E)` to Mathlib's `ZeroAtInftyContinuousMap`. The book's
  statements compare `c₀`, `c` and `ℓ^p` *inside* `ℓ^∞`, which is why they are submodules and not
  standalone types.
* **The elementary inclusions**: `ℓ^p ⊆ c₀` (`lp.tendsto_cofinite_zero`,
  `lp.linearMapOfLE_mem_zeroAtInfty`) and `‖x‖_q ≤ ‖x‖_p` for `p ≤ q`
  (`lp.norm_linearMapOfLE_le`, with the bundled inclusion `lp.inclusionCLM`).
* **The right shift** `lp.shiftRightL 𝕜 : ℓ²(ℕ; 𝕜) →L[𝕜] ℓ²(ℕ; 𝕜)`, `u ↦ (0, u₀, u₁, …)`, an
  isometry (`lp.norm_shiftRightL_apply`): the operator of [brezis2011functional] chapter 6,
  Remark 6 and §11.4 (`0` in the spectrum but not an eigenvalue; over `ℂ`, no eigenvalue).
* **Duality**, Propositions 11.18–11.20 of [brezis2011functional], as isometric isomorphisms for
  scalar sequences over `RCLike 𝕜`: `(ℓ^p)* = ℓ^{p'}` for `1 ≤ p < ∞` (`lp.toDual`,
  `lp.dualEquiv`, any index type), `(c₀)* = ℓ¹` (`lp.zeroAtInfty.dualEquiv`) and
  `c* = ℓ¹ × 𝕜` with the norm `‖u‖₁ + ‖λ‖` (`lp.convergent.dualEquiv`, the product carrying the
  `ℓ¹` norm as `WithLp 1 (_ × 𝕜)`). The isometry `‖u‖_{p'} ≤ ‖φ_u‖` is the book's finite-section
  estimate with the test sequences `x_k = |u_k|^{p'-2} u_k`, packaged once as
  `lp.sum_norm_rpow_apply_single_le` and used for the isometry and for the surjectivity alike.
* **Reflexivity** of `ℓ^p` for `1 < p < ∞` (`lp.isReflexive`, `lp.instIsReflexive`), proved
  directly from the two duality isometries `(ℓ^p)** ≅ (ℓ^{p'})* ≅ ℓ^p`, and **non-reflexivity**
  of `c₀`, `ℓ^∞`, `c` and `ℓ¹` (Proposition 11.21): `c₀` by the book's bidual functional
  corresponding to `(1, 1, 1, …)`, `ℓ^∞` and `c` as spaces containing `c₀` as a closed subspace,
  `ℓ¹` because its dual `ℓ^∞` would be reflexive.
* **Uniform convexity** of `ℓ^p(α, ℝ)`, `1 < p < ∞`, countable `α` (`lp.uniformConvexSpace`),
  transported from `MeasureTheory.Lp.instUniformConvexSpace` along the isometry
  `lp.lpLIELpCount : lp (fun _ : α ↦ E) p ≃ₗᵢ[𝕜] Lp E p Measure.count` — the book's own route
  ("Theorem 4.10 and Exercise 4.12 with `Ω = ℕ`"), which also gives every `L^p` theorem an `ℓ^p`
  version for free.
* **Separability** of `ℓ^p` (`p < ∞`), `c₀` and `c` for a separable `E` (`lp.separableSpace`,
  `lp.zeroAtInfty.instSeparableSpace`, `lp.convergent.instSeparableSpace`: the finitely supported
  sequences, resp. those plus the constants, span a dense separable subspace) and
  **non-separability** of `ℓ^∞` over an infinite index type (`lp.not_separableSpace_top`: the
  indicator sequences are an uncountable `1`-separated family).

## References

Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
Universitext, Springer, 2011 [brezis2011functional], §11.3.
-/

open Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace lp

/-! ### The subspaces `c` and `c₀` of `ℓ^∞` -/

section Subspaces

variable (𝕜 E : Type*) [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The space `c` of [brezis2011functional] §11.3: the sequences in `E` that have a limit, as a
subspace of `ℓ^∞(ℕ, E)`. A convergent sequence is bounded, so the carrier lives in `ℓ^∞`. -/
def convergent : Submodule 𝕜 (lp (fun _ : ℕ => E) ∞) where
  carrier := {x | ∃ l : E, Tendsto (⇑x) atTop (𝓝 l)}
  add_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by rw [lp.coeFn_add]; exact ha.add hb⟩
  zero_mem' := ⟨0, by rw [lp.coeFn_zero]; exact tendsto_const_nhds⟩
  smul_mem' := by
    rintro c x ⟨a, ha⟩
    exact ⟨c • a, by rw [lp.coeFn_smul]; exact ha.const_smul c⟩

/-- The space `c₀` of [brezis2011functional] §11.3: the null sequences in `E`, as a subspace of
`ℓ^∞(ℕ, E)`. Named after Mathlib's `ZeroAtInftyContinuousMap` (`C₀(ℕ, E)`), to which it is
isometric (`lp.zeroAtInftyLIE`). -/
def zeroAtInfty : Submodule 𝕜 (lp (fun _ : ℕ => E) ∞) where
  carrier := {x | Tendsto (⇑x) atTop (𝓝 0)}
  add_mem' := by
    intro x y hx hy
    rw [Set.mem_ofPred_eq, lp.coeFn_add]
    have h := hx.add hy
    rw [add_zero] at h
    exact h
  zero_mem' := by rw [Set.mem_ofPred_eq, lp.coeFn_zero]; exact tendsto_const_nhds
  smul_mem' := by
    intro c x hx
    rw [Set.mem_ofPred_eq, lp.coeFn_smul]
    have h := hx.const_smul c
    rw [smul_zero] at h
    exact h

variable {𝕜 E}

/-- Membership in `c`: the sequence has a limit. -/
@[simp]
theorem mem_convergent {x : lp (fun _ : ℕ => E) ∞} :
    x ∈ convergent 𝕜 E ↔ ∃ l : E, Tendsto (⇑x) atTop (𝓝 l) :=
  Iff.rfl

/-- Membership in `c₀`: the sequence tends to `0`. -/
@[simp]
theorem mem_zeroAtInfty {x : lp (fun _ : ℕ => E) ∞} :
    x ∈ zeroAtInfty 𝕜 E ↔ Tendsto (⇑x) atTop (𝓝 0) :=
  Iff.rfl

variable (𝕜 E)

/-- `c₀ ⊆ c`: a null sequence has a limit. -/
theorem zeroAtInfty_le_convergent : zeroAtInfty 𝕜 E ≤ convergent 𝕜 E := fun _ hx => ⟨0, hx⟩

/-- `c₀` is closed in `ℓ^∞`: a uniform limit of null sequences is null. No completeness of `E`
is needed, the limit `0` being given. -/
theorem isClosed_zeroAtInfty : IsClosed (zeroAtInfty 𝕜 E : Set (lp (fun _ : ℕ => E) ∞)) := by
  refine isClosed_of_closure_subset fun x hx => ?_
  rw [SetLike.mem_coe, mem_zeroAtInfty, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx (ε / 2) (by positivity)
  rw [SetLike.mem_coe, mem_zeroAtInfty] at hy
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hy (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_zero_right]
  have h1 : ‖x n - y n‖ < ε / 2 := by
    refine (lp.norm_apply_le_norm ENNReal.top_ne_zero (x - y) n).trans_lt ?_
    rwa [← dist_eq_norm]
  have h2 : ‖y n‖ < ε / 2 := by simpa [dist_zero_right] using hN n hn
  calc ‖x n‖ = ‖(x n - y n) + y n‖ := by rw [sub_add_cancel]
    _ ≤ ‖x n - y n‖ + ‖y n‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add h1 h2
    _ = ε := add_halves ε

/-- `c` is closed in `ℓ^∞` when `E` is complete: a uniform limit of convergent sequences is
Cauchy, hence convergent. -/
theorem isClosed_convergent [CompleteSpace E] :
    IsClosed (convergent 𝕜 E : Set (lp (fun _ : ℕ => E) ∞)) := by
  refine isClosed_of_closure_subset fun x hx => ?_
  rw [SetLike.mem_coe, mem_convergent]
  refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.2 fun ε hε => ?_)
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx (ε / 3) (by positivity)
  rw [SetLike.mem_coe, mem_convergent] at hy
  obtain ⟨l, hl⟩ := hy
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hl.cauchySeq (ε / 3) (by positivity)
  have hxy' : ∀ k, dist (x k) (y k) < ε / 3 := fun k => by
    rw [dist_eq_norm]
    refine (lp.norm_apply_le_norm ENNReal.top_ne_zero (x - y) k).trans_lt ?_
    rwa [← dist_eq_norm]
  refine ⟨N, fun m hm n hn => ?_⟩
  calc dist (x m) (x n) ≤ dist (x m) (y m) + dist (y m) (y n) + dist (y n) (x n) :=
        dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · exact hxy' m
        · exact hN m hm n hn
        · rw [dist_comm]; exact hxy' n
    _ = ε := by ring

/-- `c` is a Banach space when `E` is. -/
instance convergent.instCompleteSpace [CompleteSpace E] : CompleteSpace (convergent 𝕜 E) :=
  (isClosed_convergent 𝕜 E).completeSpace_coe

/-- `c₀` is a Banach space when `E` is. -/
instance zeroAtInfty.instCompleteSpace [CompleteSpace E] : CompleteSpace (zeroAtInfty 𝕜 E) :=
  (isClosed_zeroAtInfty 𝕜 E).completeSpace_coe

/-- The sequences `(0, …, 0, a, 0, …)` are null sequences. -/
theorem single_mem_zeroAtInfty (k : ℕ) (a : E) : lp.single ∞ k a ∈ zeroAtInfty 𝕜 E := by
  rw [mem_zeroAtInfty, lp.coeFn_single]
  refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨k + 1, fun n hn => ?_⟩)
  exact (Pi.single_eq_of_ne (M := fun _ : ℕ => E) (show n ≠ k by omega) a).symm

end Subspaces

section Limit

variable (𝕜 E : Type*) [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The constant sequences, as elements of `ℓ^∞`. -/
def constL : E →L[𝕜] lp (fun _ : ℕ => E) ∞ :=
  LinearMap.mkContinuous
    { toFun := fun a => ⟨fun _ => a, memℓp_infty ⟨‖a‖, by rintro _ ⟨i, rfl⟩; exact le_rfl⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 fun a => by
      rw [one_mul]
      exact lp.norm_le_of_forall_le (norm_nonneg a) fun _ => le_rfl

/-- The terms of the constant sequence. -/
@[simp]
theorem constL_apply (a : E) (n : ℕ) : constL 𝕜 E a n = a := rfl

/-- The constant sequences have a limit. -/
theorem constL_mem_convergent (a : E) : constL 𝕜 E a ∈ convergent 𝕜 E :=
  ⟨a, tendsto_const_nhds⟩

/-! ### The limit functional on `c` -/

/-- The limit, as a bounded linear functional on `c` ([brezis2011functional] Proposition 11.20,
the `λ lim x_k` term): `x ↦ lim x`, of norm at most `1`. -/
def convergent.limCLM : convergent 𝕜 E →L[𝕜] E :=
  LinearMap.mkContinuous
    { toFun := fun x => limUnder atTop (⇑(x : lp (fun _ : ℕ => E) ∞))
      map_add' := fun x y => by
        obtain ⟨a, ha⟩ := x.2
        obtain ⟨b, hb⟩ := y.2
        have hab : Tendsto (⇑((x + y : convergent 𝕜 E) : lp (fun _ : ℕ => E) ∞)) atTop
            (𝓝 (a + b)) := by
          rw [Submodule.coe_add, lp.coeFn_add]
          exact ha.add hb
        rw [ha.limUnder_eq, hb.limUnder_eq, hab.limUnder_eq]
      map_smul' := fun c x => by
        obtain ⟨a, ha⟩ := x.2
        have hca : Tendsto (⇑((c • x : convergent 𝕜 E) : lp (fun _ : ℕ => E) ∞)) atTop
            (𝓝 (c • a)) := by
          rw [Submodule.coe_smul, lp.coeFn_smul]
          exact ha.const_smul c
        rw [RingHom.id_apply, ha.limUnder_eq, hca.limUnder_eq] }
    1 fun x => by
      obtain ⟨a, ha⟩ := x.2
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul, ha.limUnder_eq]
      exact le_of_tendsto' ha.norm fun n => lp.norm_apply_le_norm ENNReal.top_ne_zero _ n

variable {𝕜 E}

/-- The limit functional evaluates to the limit. -/
theorem convergent.tendsto_limCLM (x : convergent 𝕜 E) :
    Tendsto (⇑(x : lp (fun _ : ℕ => E) ∞)) atTop (𝓝 (convergent.limCLM 𝕜 E x)) := by
  obtain ⟨a, ha⟩ := x.2
  have : convergent.limCLM 𝕜 E x = a := ha.limUnder_eq
  rw [this]
  exact ha

/-- The limit functional is determined by the limit. -/
theorem convergent.limCLM_eq_of_tendsto {x : convergent 𝕜 E} {a : E}
    (hx : Tendsto (⇑(x : lp (fun _ : ℕ => E) ∞)) atTop (𝓝 a)) : convergent.limCLM 𝕜 E x = a :=
  tendsto_nhds_unique (convergent.tendsto_limCLM x) hx

/-- `‖lim x‖ ≤ ‖x‖_∞`. -/
theorem convergent.norm_limCLM_apply_le (x : convergent 𝕜 E) :
    ‖convergent.limCLM 𝕜 E x‖ ≤ ‖x‖ :=
  le_of_tendsto' (convergent.tendsto_limCLM x).norm fun n =>
    lp.norm_apply_le_norm ENNReal.top_ne_zero _ n

variable (𝕜 E) in
/-- The limit functional has norm at most `1`. -/
theorem convergent.norm_limCLM_le : ‖convergent.limCLM 𝕜 E‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- On a null sequence the limit functional vanishes. -/
theorem convergent.limCLM_eq_zero_of_mem_zeroAtInfty {x : convergent 𝕜 E}
    (hx : (x : lp (fun _ : ℕ => E) ∞) ∈ zeroAtInfty 𝕜 E) : convergent.limCLM 𝕜 E x = 0 :=
  convergent.limCLM_eq_of_tendsto hx

/-- The limit of a constant sequence. -/
@[simp]
theorem convergent.limCLM_constL (a : E) :
    convergent.limCLM 𝕜 E ⟨constL 𝕜 E a, constL_mem_convergent 𝕜 E a⟩ = a :=
  convergent.limCLM_eq_of_tendsto tendsto_const_nhds

/-- `x - (lim x) • (1, 1, …)` is a null sequence: the decomposition `c = c₀ ⊕ (constants)` of
[brezis2011functional] Proposition 11.20. -/
theorem convergent.sub_constL_limCLM_mem_zeroAtInfty (x : convergent 𝕜 E) :
    (x : lp (fun _ : ℕ => E) ∞) - constL 𝕜 E (convergent.limCLM 𝕜 E x) ∈ zeroAtInfty 𝕜 E := by
  rw [mem_zeroAtInfty, lp.coeFn_sub]
  have h := (convergent.tendsto_limCLM x).sub_const (convergent.limCLM 𝕜 E x)
  rw [sub_self] at h
  exact h

end Limit

/-! ### The inclusions `ℓ^p ⊆ c₀` and `ℓ^p ⊆ ℓ^q` -/

section Inclusions

variable {α : Type*} {E : α → Type*} [∀ i, NormedAddCommGroup (E i)] {p q : ℝ≥0∞}

/-- For `p ≠ ∞`, the norms of the terms of `f ∈ ℓ^p` tend to `0` along the cofinite filter:
`‖f i‖ ^ p` is summable. -/
theorem tendsto_norm_cofinite_zero (hp : p ≠ ∞) (f : lp E p) :
    Tendsto (fun i => ‖f i‖) cofinite (𝓝 0) := by
  rcases eq_or_ne p 0 with rfl | hp0
  · have hfin := (lp.memℓp f).finite_dsupport
    refine tendsto_const_nhds.congr' (hfin.eventually_cofinite_notMem.mono fun i hi => ?_)
    simp only [Set.mem_ofPred_eq, not_not] at hi
    simp [hi]
  · have hP : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
    have h := ((lp.memℓp f).summable hP).tendsto_cofinite_zero
    have hc :=
      ((Real.continuous_rpow_const (by positivity : (0 : ℝ) ≤ 1 / p.toReal)).tendsto 0).comp h
    rw [Real.zero_rpow (by positivity)] at hc
    refine hc.congr fun i => ?_
    simp only [Function.comp_apply]
    rw [← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel hP.ne', Real.rpow_one]

/-- "`ℓ^p ⊆ c₀`", [brezis2011functional] §11.3: for `p ≠ ∞` the terms of `f ∈ ℓ^p` tend to `0`
along the cofinite filter (on `ℕ`, along `atTop`). -/
theorem tendsto_cofinite_zero {E : Type*} [NormedAddCommGroup E] (hp : p ≠ ∞)
    (f : lp (fun _ : α => E) p) : Tendsto (fun i => f i) cofinite (𝓝 0) :=
  tendsto_zero_iff_norm_tendsto_zero.2 (tendsto_norm_cofinite_zero hp f)

/-- "`ℓ^p ⊆ c₀`" as an inclusion of subspaces of `ℓ^∞`: the image of `ℓ^p`, `p ≠ ∞`, under
Mathlib's inclusion `lp.linearMapOfLE` lies in `c₀`. -/
theorem linearMapOfLE_mem_zeroAtInfty (𝕜 : Type*) [NormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (hp : p ≠ ∞) (f : lp (fun _ : ℕ => E) p) :
    lp.linearMapOfLE 𝕜 (fun _ : ℕ => E) le_top f ∈ zeroAtInfty 𝕜 E := by
  rw [mem_zeroAtInfty, lp.coe_linearMapOfLE_apply, ← Nat.cofinite_eq_atTop]
  exact tendsto_cofinite_zero hp f

/-- "`ℓ^p ⊆ ℓ^q` for `p ≤ q` with `‖x‖_q ≤ ‖x‖_p`", [brezis2011functional] §11.3: Mathlib's
inclusion `lp.linearMapOfLE` does not increase the norm (for any `0 < p ≤ q ≤ ∞`). The proof
bounds `‖f i‖ ^ q = ‖f i‖ ^ p ‖f i‖ ^ (q - p) ≤ ‖f i‖ ^ p ‖f‖ ^ (q - p)` and sums. -/
theorem norm_linearMapOfLE_le (𝕜 : Type*) [NormedRing 𝕜] [∀ i, Module 𝕜 (E i)]
    [∀ i, IsBoundedSMul 𝕜 (E i)] (hp : p ≠ 0) (h : p ≤ q) (f : lp E p) :
    ‖lp.linearMapOfLE 𝕜 E h f‖ ≤ ‖f‖ := by
  have hfi : ∀ i, ‖f i‖ ≤ ‖f‖ := lp.norm_apply_le_norm hp f
  rcases eq_or_ne q ∞ with rfl | hq
  · exact lp.norm_le_of_forall_le (lp.norm_nonneg' f) fun i => by
      rw [lp.coe_linearMapOfLE_apply]; exact hfi i
  · have hp' : p ≠ ∞ := ne_top_of_le_ne_top hq h
    have hP : 0 < p.toReal := ENNReal.toReal_pos hp hp'
    have hPQ : p.toReal ≤ q.toReal := ENNReal.toReal_mono hq h
    have hQ : 0 < q.toReal := hP.trans_le hPQ
    have hQP : p.toReal + (q.toReal - p.toReal) ≠ 0 := by rw [add_sub_cancel]; exact hQ.ne'
    refine lp.norm_le_of_forall_sum_le hQ (lp.norm_nonneg' f) fun s => ?_
    simp only [lp.coe_linearMapOfLE_apply]
    calc ∑ i ∈ s, ‖f i‖ ^ q.toReal
        = ∑ i ∈ s, ‖f i‖ ^ p.toReal * ‖f i‖ ^ (q.toReal - p.toReal) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Real.rpow_add' (norm_nonneg _) hQP, add_sub_cancel]
      _ ≤ ∑ i ∈ s, ‖f i‖ ^ p.toReal * ‖f‖ ^ (q.toReal - p.toReal) := by
          gcongr with i hi
          exact hfi i
      _ = (∑ i ∈ s, ‖f i‖ ^ p.toReal) * ‖f‖ ^ (q.toReal - p.toReal) := by rw [Finset.sum_mul]
      _ ≤ ‖f‖ ^ p.toReal * ‖f‖ ^ (q.toReal - p.toReal) :=
          mul_le_mul_of_nonneg_right (lp.sum_rpow_le_norm_rpow hP f s)
            (Real.rpow_nonneg (lp.norm_nonneg' f) _)
      _ = ‖f‖ ^ q.toReal := by rw [← Real.rpow_add' (lp.norm_nonneg' f) hQP, add_sub_cancel]

end Inclusions

section InclusionCLM

variable {α : Type*} (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : α → Type*)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] {p q : ℝ≥0∞}

/-- The inclusion `ℓ^p → ℓ^q`, `1 ≤ p ≤ q ≤ ∞`, as a bounded linear map (of norm at most `1`,
`lp.norm_inclusionCLM_le`). -/
def inclusionCLM [Fact (1 ≤ p)] [Fact (1 ≤ q)] (h : p ≤ q) : lp E p →L[𝕜] lp E q :=
  (lp.linearMapOfLE 𝕜 E h).mkContinuous 1 fun f => by
    rw [one_mul]
    exact norm_linearMapOfLE_le 𝕜 (zero_lt_one.trans_le Fact.out).ne' h f

variable {E}

/-- The inclusion `ℓ^p → ℓ^q` does not change the underlying sequence. -/
@[simp]
theorem coe_inclusionCLM_apply [Fact (1 ≤ p)] [Fact (1 ≤ q)] (h : p ≤ q) (f : lp E p) :
    ⇑(inclusionCLM 𝕜 E h f) = f :=
  lp.coe_linearMapOfLE_apply h f

/-- The inclusion `ℓ^p → ℓ^q`, `p ≤ q`, has norm at most `1`. -/
theorem norm_inclusionCLM_le [Fact (1 ≤ p)] [Fact (1 ≤ q)] (h : p ≤ q) :
    ‖inclusionCLM 𝕜 E h‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end InclusionCLM

/-! ### The right shift on `ℓ²` -/

section Shift

variable (𝕜 : Type*) [NormedField 𝕜]

/-- The right-shifted sequence `(0, u₀, u₁, …)`. -/
private def shiftFun (u : ℕ → 𝕜) : ℕ → 𝕜
  | 0 => 0
  | n + 1 => u n

private theorem shiftFun_zero (u : ℕ → 𝕜) : shiftFun 𝕜 u 0 = 0 := rfl

private theorem shiftFun_succ (u : ℕ → 𝕜) (n : ℕ) : shiftFun 𝕜 u (n + 1) = u n := rfl

private theorem memℓp_shiftFun (u : lp (fun _ : ℕ => 𝕜) 2) : Memℓp (shiftFun 𝕜 u) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  exact (summable_nat_add_iff 1).1 ((memℓp_gen_iff (by norm_num)).1 u.2)

private theorem norm_shiftFun (u : lp (fun _ : ℕ => 𝕜) 2) :
    ‖(⟨shiftFun 𝕜 u, memℓp_shiftFun 𝕜 u⟩ : lp (fun _ : ℕ => 𝕜) 2)‖ = ‖u‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
  congr 1
  have hs := (memℓp_gen_iff (by norm_num)).1 (memℓp_shiftFun 𝕜 u)
  change ∑' i, ‖shiftFun 𝕜 u i‖ ^ (2 : ℝ≥0∞).toReal = _
  rw [hs.tsum_eq_zero_add]
  simp [shiftFun_zero, shiftFun_succ]

/-- **The right shift** `S_r u = (0, u₀, u₁, …)` on `ℓ²(ℕ; 𝕜)`: `(S_r u) 0 = 0` and
`(S_r u) (n + 1) = u n` (`shiftRightL_apply_zero`, `shiftRightL_apply_succ`). It is an isometry
(`norm_shiftRightL_apply`), hence injective, and not surjective — the standard example of an
operator with `0` in the spectrum but not an eigenvalue ([brezis2011functional] chapter 6,
Remark 6), and over `ℂ` of an operator without eigenvalues at all ([brezis2011functional]
§11.4). -/
def shiftRightL : lp (fun _ : ℕ => 𝕜) 2 →L[𝕜] lp (fun _ : ℕ => 𝕜) 2 :=
  LinearMap.mkContinuous
    { toFun := fun u => ⟨shiftFun 𝕜 u, memℓp_shiftFun 𝕜 u⟩
      map_add' := fun u v => lp.ext (funext fun n => by
        cases n with
        | zero => change (0 : 𝕜) = 0 + 0; rw [add_zero]
        | succ n => rfl)
      map_smul' := fun c u => lp.ext (funext fun n => by
        cases n with
        | zero => change (0 : 𝕜) = c • 0; rw [smul_zero]
        | succ n => rfl) }
    1 fun u => by
      rw [one_mul]
      exact (norm_shiftFun 𝕜 u).le

/-- `(S_r u) 0 = 0`. -/
@[simp]
theorem shiftRightL_apply_zero (u : lp (fun _ : ℕ => 𝕜) 2) : shiftRightL 𝕜 u 0 = 0 := rfl

/-- `(S_r u) (n + 1) = u n`. -/
@[simp]
theorem shiftRightL_apply_succ (u : lp (fun _ : ℕ => 𝕜) 2) (n : ℕ) :
    shiftRightL 𝕜 u (n + 1) = u n := rfl

/-- The right shift is an isometry: `‖S_r u‖ = ‖u‖`. -/
theorem norm_shiftRightL_apply (u : lp (fun _ : ℕ => 𝕜) 2) : ‖shiftRightL 𝕜 u‖ = ‖u‖ :=
  norm_shiftFun 𝕜 u

end Shift

/-! ### Finitely supported sequences in `c₀`, and the bridge to `C₀(ℕ, E)` -/

section ZeroAtInfty

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A null sequence is the sum of its coordinates `(0, …, 0, x k, 0, …)` in `ℓ^∞`: the analogue
of `lp.hasSum_single` at `p = ∞`, which holds exactly on `c₀`. -/
theorem zeroAtInfty.hasSum_single {x : lp (fun _ : ℕ => E) ∞} (hx : x ∈ zeroAtInfty 𝕜 E) :
    HasSum (fun k => lp.single ∞ k (x k)) x := by
  rw [HasSum, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hx (ε / 2) (by positivity)
  refine eventually_atTop.2 ⟨Finset.range N, fun s hs => ?_⟩
  rw [dist_eq_norm]
  refine (lp.norm_le_of_forall_le (C := ε / 2) (half_pos hε).le fun j => ?_).trans_lt
    (half_lt_self hε)
  rw [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.coeFn_single, Finset.sum_pi_single]
  split_ifs with hj
  · rw [sub_self, _root_.norm_zero]
    positivity
  · have hNj : N ≤ j := by
      by_contra h
      exact hj (hs (Finset.mem_range.2 (not_le.1 h)))
    rw [zero_sub, _root_.norm_neg]
    simpa [dist_zero_right] using (hN j hNj).le

/-- `lp.zeroAtInfty.hasSum_single` read inside the subtype `c₀`. -/
theorem zeroAtInfty.hasSum_single' (x : zeroAtInfty 𝕜 E) :
    HasSum (fun k => (⟨lp.single ∞ k ((x : lp (fun _ : ℕ => E) ∞) k),
      single_mem_zeroAtInfty 𝕜 E k _⟩ : zeroAtInfty 𝕜 E)) x := by
  have hind : Topology.IsInducing (zeroAtInfty 𝕜 E).subtype := Topology.IsInducing.subtypeVal
  exact (hind.hasSum_iff _ _).1 (zeroAtInfty.hasSum_single x.2)

variable (𝕜 E)

open scoped ZeroAtInfty in
/-- **The bridge to Mathlib**: `c₀` is isometrically isomorphic to `C₀(ℕ, E)`
(`ZeroAtInftyContinuousMap`), the identity on the underlying functions — on the discrete space
`ℕ` every function is continuous and `cocompact ℕ = atTop`, and both norms are the supremum
norm. -/
def zeroAtInftyLIE : zeroAtInfty 𝕜 E ≃ₗᵢ[𝕜] C₀(ℕ, E) where
  toFun x :=
    { toFun := ⇑(x : lp (fun _ : ℕ => E) ∞)
      continuous_toFun := continuous_of_discreteTopology
      zero_at_infty' := by rw [cocompact_eq_cofinite, Nat.cofinite_eq_atTop]; exact x.2 }
  invFun f :=
    ⟨⟨⇑f, memℓp_infty (by
      obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 f.isBounded_range
      exact ⟨C, by rintro _ ⟨i, rfl⟩; exact hC _ (Set.mem_range_self i)⟩)⟩, by
      rw [mem_zeroAtInfty, ← Nat.cofinite_eq_atTop, ← cocompact_eq_cofinite]
      exact zero_at_infty f⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' x := by
    change ‖(_ : C₀(ℕ, E)).toBCF‖ = ‖(x : lp (fun _ : ℕ => E) ∞)‖
    rw [BoundedContinuousFunction.norm_eq_iSup_norm, lp.norm_eq_ciSup]
    rfl

/-- The bridge `c₀ ≃ C₀(ℕ, E)` is the identity on the terms. -/
@[simp]
theorem zeroAtInftyLIE_apply (x : zeroAtInfty 𝕜 E) (n : ℕ) :
    zeroAtInftyLIE 𝕜 E x n = (x : lp (fun _ : ℕ => E) ∞) n :=
  rfl

end ZeroAtInfty

/-! ### The duality `(ℓ^p)* = ℓ^{p'}` -/

section Duality

variable {𝕜 : Type*} [RCLike 𝕜] {α : Type*} {p q : ℝ≥0∞}

/-- **The finite-section estimate** of [brezis2011functional] Proposition 11.18: for a
functional `φ` on `ℓ^p`, `1 ≤ p < ∞` with conjugate exponent `q < ∞`, and `u_k := φ (e_k)`,
`∑_{k ∈ s} ‖u_k‖ ^ q ≤ ‖φ‖ ^ q` for every finite set `s` of indices. This is the book's
display (6) before letting `N → ∞`, tested against `x_k = ‖u_k‖ ^ (q - 2) conj (u_k)` on `s`
(so that `u_k x_k = ‖u_k‖ ^ q`), and it serves both the isometry and the surjectivity. -/
theorem sum_norm_rpow_apply_single_le [DecidableEq α] [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [p.HolderConjugate q] (hq : q ≠ ∞) (φ : StrongDual 𝕜 (lp (fun _ : α => 𝕜) p))
    (s : Finset α) :
    ∑ k ∈ s, ‖φ (lp.single p k 1)‖ ^ q.toReal ≤ ‖φ‖ ^ q.toReal := by
  set Q := q.toReal with hQ
  have hQ1 : 1 ≤ Q := by
    rw [hQ, ← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hq Fact.out
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ1
  obtain ⟨v, hv⟩ : ∃ v : α → 𝕜, ∀ k, v k = φ (lp.single p k 1) := ⟨_, fun _ => rfl⟩
  simp only [← hv]
  set c : α → 𝕜 := fun k => ((‖v k‖ ^ (Q - 2) : ℝ) : 𝕜) * (starRingEnd 𝕜) (v k) with hc
  set x : lp (fun _ : α => 𝕜) p := ∑ k ∈ s, lp.single p k (c k) with hx
  set S := ∑ k ∈ s, ‖v k‖ ^ Q with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => Real.rpow_nonneg (norm_nonneg _) _
  -- `φ x = S`
  have hcv : ∀ k, c k * v k = ((‖v k‖ ^ Q : ℝ) : 𝕜) := fun k => by
    rw [hc, mul_assoc, RCLike.conj_mul, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul,
      ← Real.rpow_natCast, ← Real.rpow_add' (norm_nonneg _) (by norm_num; exact hQ0.ne')]
    norm_num
  have hφx : φ x = (S : 𝕜) := by
    rw [hx, map_sum, hS, RCLike.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 : (lp.single p k (c k) : lp (fun _ : α => 𝕜) p) = c k • lp.single p k 1 := by
      rw [← lp.single_smul, smul_eq_mul, mul_one]
    rw [h1, map_smul, smul_eq_mul, ← hv, hcv]
  have hφx' : S ≤ ‖φ‖ * ‖x‖ := by
    have : ‖φ x‖ = S := by rw [hφx, RCLike.norm_ofReal, abs_of_nonneg hS0]
    rw [← this]
    exact φ.le_opNorm x
  rcases eq_or_ne p ∞ with hp | hp
  · -- `p = ∞`, `q = 1`: the test vector has norm at most `1`
    have hq1 : q = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one p q).1 hp
    have hQ1' : Q = 1 := by rw [hQ, hq1, ENNReal.toReal_one]
    subst hp
    have hx1 : ‖x‖ ≤ 1 := by
      refine lp.norm_le_of_forall_le zero_le_one fun j => ?_
      rw [hx, lp.coeFn_sum, Finset.sum_apply]
      simp only [lp.coeFn_single, Finset.sum_pi_single]
      split_ifs with hj
      · rw [hc, norm_mul, RCLike.norm_ofReal, RCLike.norm_conj,
          abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), hQ1']
        rcases eq_or_ne (v j) 0 with h0 | h0
        · rw [h0, _root_.norm_zero, mul_zero]; exact zero_le_one
        · rw [show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one,
            inv_mul_cancel₀ (norm_ne_zero_iff.2 h0)]
      · rw [_root_.norm_zero]; exact zero_le_one
    rw [hQ1', Real.rpow_one]
    simp only [hQ1', Real.rpow_one] at hS
    rw [hS] at hφx' ⊢
    calc ∑ k ∈ s, ‖v k‖ ≤ ‖φ‖ * ‖x‖ := hφx'
      _ ≤ ‖φ‖ * 1 := by gcongr
      _ = ‖φ‖ := mul_one _
  · -- `1 < p < ∞`: `‖x‖ ^ p = S`
    have hPQ : p.toReal.HolderConjugate Q := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
    set P := p.toReal with hP
    have hP0 : 0 < P := hPQ.pos
    have hQ1'' : 1 < Q := hPQ.symm.lt
    have hxnorm : ‖x‖ ^ P = S := by
      rw [hx, lp.norm_sum_single hP0, hS]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hck : ‖c k‖ = ‖v k‖ ^ (Q - 1) := by
        rw [hc, norm_mul, RCLike.norm_ofReal, RCLike.norm_conj,
          abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), show Q - 1 = Q - 2 + 1 by ring,
          Real.rpow_add_one' (norm_nonneg _) (by intro h; linarith)]
      rw [hck, ← Real.rpow_mul (norm_nonneg _), hPQ.symm.sub_one_mul_conj]
    have hSle : S ≤ ‖φ‖ * S ^ (1 / P) := by
      have h2 : ‖x‖ = S ^ (1 / P) := by
        rw [← hxnorm, one_div, Real.rpow_rpow_inv (lp.norm_nonneg' x) hP0.ne']
      rwa [h2] at hφx'
    rcases hS0.eq_or_lt with hS0' | hSpos
    · rw [← hS0']
      exact Real.rpow_nonneg (norm_nonneg φ) _
    · have h3 : S ^ (1 / Q) ≤ ‖φ‖ := by
        have hsub : 1 / Q = 1 - 1 / P := by rw [one_div, one_div, hPQ.one_sub_inv]
        rw [hsub, Real.rpow_sub hSpos, Real.rpow_one, div_le_iff₀ (Real.rpow_pos_of_pos hSpos _)]
        exact hSle
      calc S = (S ^ (1 / Q)) ^ Q := by
            rw [← Real.rpow_mul hS0, one_div_mul_cancel hQ0.ne', Real.rpow_one]
        _ ≤ ‖φ‖ ^ Q := Real.rpow_le_rpow (Real.rpow_nonneg hS0 _) h3 hQ0.le

variable (𝕜 α p q) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- The map `u ↦ (x ↦ ∑' k, u k * x k)` from `ℓ^{p'}` to `(ℓ^p)*`, as a bounded linear map:
Mathlib's `lp.dualPairing` for the multiplication of `𝕜`. Its isometry property is
`lp.norm_toDualCLM_apply`, and `lp.toDual` is the bundled linear isometry. -/
def toDualCLM : lp (fun _ : α => 𝕜) q →L[𝕜] StrongDual 𝕜 (lp (fun _ : α => 𝕜) p) :=
  lp.dualPairing q p (fun _ => ContinuousLinearMap.mul 𝕜 𝕜) (K := 1) fun _ =>
    (ContinuousLinearMap.opNorm_mul_le 𝕜 𝕜).trans_eq NNReal.coe_one.symm

variable {𝕜 α p q}

/-- The pairing: `φ_u x = ∑' k, u k * x k`. -/
theorem toDualCLM_apply (u : lp (fun _ : α => 𝕜) q) (x : lp (fun _ : α => 𝕜) p) :
    toDualCLM 𝕜 α p q u x = ∑' k, u k * x k :=
  rfl

variable (𝕜 α p q) in
/-- Hölder's inequality: the pairing has norm at most `1`. -/
theorem norm_toDualCLM_le : ‖toDualCLM 𝕜 α p q‖ ≤ 1 :=
  (lp.norm_dualPairing (p := q) (q := p) (fun _ : α => ContinuousLinearMap.mul 𝕜 𝕜) (K := 1)
    fun _ => (ContinuousLinearMap.opNorm_mul_le 𝕜 𝕜).trans_eq NNReal.coe_one.symm).trans_eq
    NNReal.coe_one

/-- The pairing evaluated on a basis vector: `φ_u (e_k a) = u k * a`. -/
theorem toDualCLM_single [DecidableEq α] (u : lp (fun _ : α => 𝕜) q) (k : α) (a : 𝕜) :
    toDualCLM 𝕜 α p q u (lp.single p k a) = u k * a := by
  rw [toDualCLM_apply, tsum_eq_single k fun j hj => by
    rw [lp.single_apply, Pi.single_eq_of_ne hj, mul_zero]]
  rw [lp.single_apply, Pi.single_eq_same]

/-- **[brezis2011functional] Proposition 11.18, the norm identity** `‖φ_u‖ = ‖u‖_{p'}`: Hölder
gives `≤`, and the finite-section estimate `lp.sum_norm_rpow_apply_single_le` (for `p' = ∞`,
the test on the basis vectors) gives `≥`. -/
theorem norm_toDualCLM_apply (u : lp (fun _ : α => 𝕜) q) : ‖toDualCLM 𝕜 α p q u‖ = ‖u‖ := by
  classical
  refine le_antisymm ?_ ?_
  · have := (toDualCLM 𝕜 α p q).le_of_opNorm_le (norm_toDualCLM_le 𝕜 α p q) u
    rwa [one_mul] at this
  rcases eq_or_ne q ∞ with rfl | hq
  · refine lp.norm_le_of_forall_le (norm_nonneg _) fun k => ?_
    have := (toDualCLM 𝕜 α p ∞ u).le_opNorm (lp.single p k 1)
    rwa [toDualCLM_single, mul_one, lp.norm_single (zero_lt_one.trans_le Fact.out), norm_one,
      mul_one] at this
  · have hQ : 0 < q.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hq
    refine lp.norm_le_of_forall_sum_le hQ (norm_nonneg _) fun s => ?_
    have := sum_norm_rpow_apply_single_le hq (toDualCLM 𝕜 α p q u) s
    simpa only [toDualCLM_single, mul_one] using this

variable (𝕜 α p q)

/-- **[brezis2011functional] Proposition 11.18, the isometry**: for Hölder conjugate exponents
`p, p'` (including `(1, ∞)`), `u ↦ (x ↦ ∑' k, u k * x k)` is a linear isometry
`ℓ^{p'} → (ℓ^p)*`, for scalar sequences over `RCLike 𝕜` and any index type. -/
def toDual : lp (fun _ : α => 𝕜) q →ₗᵢ[𝕜] StrongDual 𝕜 (lp (fun _ : α => 𝕜) p) :=
  ⟨(toDualCLM 𝕜 α p q).toLinearMap, norm_toDualCLM_apply⟩

variable {𝕜 α p q}

/-- `lp.toDual` is `lp.toDualCLM` as a map. -/
@[simp]
theorem coe_toDual (u : lp (fun _ : α => 𝕜) q) : toDual 𝕜 α p q u = toDualCLM 𝕜 α p q u :=
  rfl

/-- The display of [brezis2011functional] Proposition 11.18: `⟨φ_u, x⟩ = ∑' k, u k * x k`. -/
theorem toDual_apply (u : lp (fun _ : α => 𝕜) q) (x : lp (fun _ : α => 𝕜) p) :
    toDual 𝕜 α p q u x = ∑' k, u k * x k :=
  rfl

/-- `φ_u (e_k a) = u k * a`. -/
theorem toDual_single [DecidableEq α] (u : lp (fun _ : α => 𝕜) q) (k : α) (a : 𝕜) :
    toDual 𝕜 α p q u (lp.single p k a) = u k * a :=
  toDualCLM_single u k a

/-- **[brezis2011functional] Proposition 11.18, existence**: for `p ≠ ∞`, every functional on
`ℓ^p` is `x ↦ ∑' k, u k * x k` for the sequence `u k := φ (e_k)`, which lies in `ℓ^{p'}` by the
finite-section estimate; `φ = φ_u` because both are continuous and agree on the basis vectors,
whose finite sums are dense (`lp.hasSum_single`). -/
theorem toDual_surjective (hp : p ≠ ∞) : Function.Surjective (toDual 𝕜 α p q) := by
  intro φ
  classical
  obtain ⟨v, hv⟩ : ∃ v : α → 𝕜, ∀ k, v k = φ (lp.single p k 1) := ⟨_, fun _ => rfl⟩
  have hv_mem : Memℓp v q := by
    rcases eq_or_ne q ∞ with rfl | hq
    · refine memℓp_infty ⟨‖φ‖, ?_⟩
      rintro _ ⟨k, rfl⟩
      have := φ.le_opNorm (lp.single p k 1)
      rwa [lp.norm_single (zero_lt_one.trans_le Fact.out), norm_one, mul_one, ← hv] at this
    · refine memℓp_gen' (C := ‖φ‖ ^ q.toReal) fun s => ?_
      simp only [hv]
      exact sum_norm_rpow_apply_single_le hq φ s
  refine ⟨⟨v, hv_mem⟩, ?_⟩
  refine lp.ext_continuousLinearMap hp fun k => ContinuousLinearMap.ext fun a => ?_
  simp only [ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply]
  rw [coe_toDual, toDualCLM_single]
  have h1 : (lp.single p k a : lp (fun _ : α => 𝕜) p) = a • lp.single p k 1 := by
    rw [← lp.single_smul, smul_eq_mul, mul_one]
  rw [h1, map_smul, smul_eq_mul, mul_comm]
  exact congrArg (fun t => a * t) (hv k)

variable (𝕜 α p q)

/-- **[brezis2011functional] Proposition 11.18 packaged**: for `1 ≤ p < ∞` with conjugate
`p'`, `ℓ^{p'} ≃ₗᵢ[𝕜] (ℓ^p)*` along `u ↦ (x ↦ ∑' k, u k * x k)` — "`(ℓ^p)* = ℓ^{p'}`" of the
book's table; at `p = 1` it reads `(ℓ¹)* = ℓ^∞`. -/
def dualEquiv (hp : p ≠ ∞) : lp (fun _ : α => 𝕜) q ≃ₗᵢ[𝕜] StrongDual 𝕜 (lp (fun _ : α => 𝕜) p) :=
  LinearIsometryEquiv.ofSurjective (toDual 𝕜 α p q) (toDual_surjective hp)

variable {𝕜 α p q}

/-- `dualEquiv` is the pairing `u ↦ (x ↦ ∑' k, u k * x k)`. -/
theorem dualEquiv_apply (hp : p ≠ ∞) (u : lp (fun _ : α => 𝕜) q) (x : lp (fun _ : α => 𝕜) p) :
    dualEquiv 𝕜 α p q hp u x = ∑' k, u k * x k :=
  rfl

/-- `lp.dualEquiv` is `lp.toDual` as a map. -/
@[simp]
theorem coe_dualEquiv (hp : p ≠ ∞) (u : lp (fun _ : α => 𝕜) q) :
    dualEquiv 𝕜 α p q hp u = toDual 𝕜 α p q u :=
  rfl

end Duality

/-! ### Reflexivity of `ℓ^p`, `1 < p < ∞` -/

section Reflexive

variable (𝕜 : Type*) [RCLike 𝕜] (α : Type*) {p : ℝ≥0∞}

/-- **[brezis2011functional] Proposition 11.15, reflexivity**: `ℓ^p` is reflexive for
`1 < p < ∞`, over `RCLike 𝕜` and any index type. Proved directly from the duality: with `p'`
the conjugate exponent and `e_p : ℓ^{p'} ≃ (ℓ^p)*`, `e_{p'} : ℓ^p ≃ (ℓ^{p'})*` the isometries of
Proposition 11.18, a functional `Φ` on `(ℓ^p)*` gives `Φ ∘ e_p = e_{p'} x` for some `x ∈ ℓ^p`,
and then `Φ (e_p u) = ∑' u k * x k = (e_p u) x`, so `Φ` is the evaluation at `x`. (The book
applies Theorem 4.10 to the counting measure instead.) -/
theorem isReflexive [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ∞) :
    NormedSpace.IsReflexive 𝕜 (lp (fun _ : α => 𝕜) p) := by
  set q := ENNReal.conjExponent p with hq
  have hpq : p.HolderConjugate q := ENNReal.HolderConjugate.conjExponent Fact.out
  have hq1 : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hq' : q ≠ ∞ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q p).2 hp.ne'
  set ep := dualEquiv 𝕜 α p q hp' with hep
  set eq := dualEquiv 𝕜 α q p hq' with heq
  refine ⟨fun Φ => ?_⟩
  obtain ⟨x, hx⟩ := eq.surjective (Φ.comp (ep.toContinuousLinearEquiv :
    lp (fun _ : α => 𝕜) q →L[𝕜] StrongDual 𝕜 (lp (fun _ : α => 𝕜) p)))
  refine ⟨x, ?_⟩
  ext f
  obtain ⟨u, rfl⟩ := ep.surjective f
  have h1 : eq x u = Φ (ep u) := by
    have := DFunLike.congr_fun hx u
    simpa using this
  rw [NormedSpace.dual_def, ← h1, heq, hep, dualEquiv_apply, dualEquiv_apply]
  exact tsum_congr fun k => mul_comm _ _

/-- `ℓ^p` is reflexive for `1 < p < ∞`, as an instance under `[Fact (1 < p)] [Fact (p ≠ ∞)]`
(the spelling of `MeasureTheory.Lp.instIsReflexive`). -/
instance instIsReflexive [Fact (1 < p)] [Fact (p ≠ ∞)] :
    NormedSpace.IsReflexive 𝕜 (lp (fun _ : α => 𝕜) p) :=
  isReflexive 𝕜 α Fact.out Fact.out

end Reflexive

/-! ### The dual of `c₀` -/

section ZeroAtInftyDual

variable {𝕜 : Type*} [RCLike 𝕜]

/-- `conj z / ‖z‖`: a scalar of norm at most `1` with `z * sgn z = ‖z‖` (and `sgn 0 = 0`), the
book's `sign (u_k)`. -/
private def sgn (z : 𝕜) : 𝕜 := (starRingEnd 𝕜) z / (‖z‖ : 𝕜)

private theorem mul_sgn (z : 𝕜) : z * sgn z = (‖z‖ : 𝕜) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [sgn]
  · rw [sgn, ← mul_div_assoc, RCLike.mul_conj, ← RCLike.ofReal_pow, ← RCLike.ofReal_div, pow_two,
      mul_div_assoc, div_self (norm_ne_zero_iff.2 hz), mul_one]

private theorem norm_sgn_le (z : 𝕜) : ‖sgn z‖ ≤ 1 := by
  rw [sgn, norm_div, RCLike.norm_conj, RCLike.norm_ofReal, abs_norm]
  exact div_self_le_one _

variable (𝕜)

/-- The basis vector `e_k` of `c₀`. -/
private def e₀ (k : ℕ) : zeroAtInfty 𝕜 𝕜 := ⟨lp.single ∞ k 1, single_mem_zeroAtInfty 𝕜 𝕜 k 1⟩

/-- The functional `x ↦ ∑' k, u k * x k` on `c₀` defined by `u ∈ ℓ¹`, as a bounded linear map
in `u`: the `(∞, 1)` case of `lp.toDualCLM` restricted to `c₀`. -/
def zeroAtInfty.toDualCLM : lp (fun _ : ℕ => 𝕜) 1 →L[𝕜] StrongDual 𝕜 (zeroAtInfty 𝕜 𝕜) :=
  ((ContinuousLinearMap.compL 𝕜 (zeroAtInfty 𝕜 𝕜) (lp (fun _ : ℕ => 𝕜) ∞) 𝕜).flip
    (zeroAtInfty 𝕜 𝕜).subtypeL).comp (lp.toDualCLM 𝕜 ℕ ∞ 1)

variable {𝕜}

/-- The pairing on `c₀`: `φ_u x = ∑' k, u k * x k`. -/
theorem zeroAtInfty.toDualCLM_apply (u : lp (fun _ : ℕ => 𝕜) 1) (x : zeroAtInfty 𝕜 𝕜) :
    zeroAtInfty.toDualCLM 𝕜 u x = ∑' k, u k * (x : lp (fun _ : ℕ => 𝕜) ∞) k :=
  rfl

/-- **The finite-section estimate for `c₀`** ([brezis2011functional] Proposition 11.19): for a
functional `φ` on `c₀` and `u_k := φ (e_k)`, `∑_{k ∈ s} ‖u_k‖ ≤ ‖φ‖` for every finite `s`,
tested against the finitely supported sequence `x_k = sign (u_k)` on `s`, of norm at most
`1`. -/
theorem zeroAtInfty.sum_norm_apply_single_le (φ : StrongDual 𝕜 (zeroAtInfty 𝕜 𝕜))
    (s : Finset ℕ) :
    ∑ k ∈ s, ‖φ ⟨lp.single ∞ k 1, single_mem_zeroAtInfty 𝕜 𝕜 k 1⟩‖ ≤ ‖φ‖ := by
  obtain ⟨v, hv⟩ : ∃ v : ℕ → 𝕜, ∀ k, v k = φ (e₀ 𝕜 k) := ⟨_, fun _ => rfl⟩
  change ∑ k ∈ s, ‖φ (e₀ 𝕜 k)‖ ≤ ‖φ‖
  simp only [← hv]
  set x : zeroAtInfty 𝕜 𝕜 := ⟨∑ k ∈ s, lp.single ∞ k (sgn (v k)),
    Submodule.sum_mem _ fun k _ => single_mem_zeroAtInfty 𝕜 𝕜 k _⟩ with hx
  have hx' : x = ∑ k ∈ s, sgn (v k) • e₀ 𝕜 k := by
    apply Subtype.ext
    rw [hx, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Submodule.coe_smul, e₀, ← lp.single_smul, smul_eq_mul, mul_one]
  have hφx : φ x = ((∑ k ∈ s, ‖v k‖ : ℝ) : 𝕜) := by
    have hms : φ (∑ k ∈ s, sgn (v k) • e₀ 𝕜 k) = ∑ k ∈ s, φ (sgn (v k) • e₀ 𝕜 k) :=
      map_sum φ _ _
    rw [hx', hms, RCLike.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_eq_mul, ← hv, mul_comm, mul_sgn]
  have hx1 : ‖x‖ ≤ 1 := by
    rw [← Submodule.norm_coe]
    refine lp.norm_le_of_forall_le zero_le_one fun j => ?_
    rw [hx]
    change ‖(∑ k ∈ s, lp.single ∞ k (sgn (v k)) : lp (fun _ : ℕ => 𝕜) ∞) j‖ ≤ 1
    rw [lp.coeFn_sum, Finset.sum_apply]
    simp only [lp.coeFn_single, Finset.sum_pi_single]
    split_ifs with hj
    · exact norm_sgn_le _
    · rw [_root_.norm_zero]
      exact zero_le_one
  calc ∑ k ∈ s, ‖v k‖ = ‖φ x‖ := by
        rw [hφx, RCLike.norm_ofReal, abs_of_nonneg (Finset.sum_nonneg fun k _ => norm_nonneg _)]
    _ ≤ ‖φ‖ * ‖x‖ := φ.le_opNorm x
    _ ≤ ‖φ‖ * 1 := by gcongr
    _ = ‖φ‖ := mul_one _

/-- `φ_u (e_k a) = u k * a` on `c₀`. -/
theorem zeroAtInfty.toDualCLM_single (u : lp (fun _ : ℕ => 𝕜) 1) (k : ℕ) (a : 𝕜) :
    zeroAtInfty.toDualCLM 𝕜 u ⟨lp.single ∞ k a, single_mem_zeroAtInfty 𝕜 𝕜 k a⟩ = u k * a :=
  lp.toDualCLM_single u k a

/-- **[brezis2011functional] Proposition 11.19, the norm identity** `‖φ_u‖_{(c₀)*} = ‖u‖₁`. -/
theorem zeroAtInfty.norm_toDualCLM_apply (u : lp (fun _ : ℕ => 𝕜) 1) :
    ‖zeroAtInfty.toDualCLM 𝕜 u‖ = ‖u‖ := by
  refine le_antisymm ?_ ?_
  · calc ‖zeroAtInfty.toDualCLM 𝕜 u‖
        = ‖(lp.toDualCLM 𝕜 ℕ ∞ 1 u).comp (zeroAtInfty 𝕜 𝕜).subtypeL‖ := rfl
      _ ≤ ‖lp.toDualCLM 𝕜 ℕ ∞ 1 u‖ * ‖(zeroAtInfty 𝕜 𝕜).subtypeL‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖u‖ * 1 := by
          gcongr
          · exact (lp.norm_toDualCLM_apply u).le
          · exact Submodule.norm_subtypeL_le _
      _ = ‖u‖ := mul_one _
  · have h1 : (0 : ℝ) < (1 : ℝ≥0∞).toReal := by simp
    refine lp.norm_le_of_forall_sum_le h1 (norm_nonneg _) fun s => ?_
    simp only [ENNReal.toReal_one, Real.rpow_one]
    have := zeroAtInfty.sum_norm_apply_single_le (zeroAtInfty.toDualCLM 𝕜 u) s
    simpa only [zeroAtInfty.toDualCLM_single, mul_one] using this

variable (𝕜)

/-- **[brezis2011functional] Proposition 11.19, the isometry**: `u ↦ (x ↦ ∑' k, u k * x k)` is a
linear isometry `ℓ¹ → (c₀)*`. -/
def zeroAtInfty.toDual : lp (fun _ : ℕ => 𝕜) 1 →ₗᵢ[𝕜] StrongDual 𝕜 (zeroAtInfty 𝕜 𝕜) :=
  ⟨(zeroAtInfty.toDualCLM 𝕜).toLinearMap, zeroAtInfty.norm_toDualCLM_apply⟩

variable {𝕜}

/-- `lp.zeroAtInfty.toDual` is `lp.zeroAtInfty.toDualCLM` as a map. -/
@[simp]
theorem zeroAtInfty.coe_toDual (u : lp (fun _ : ℕ => 𝕜) 1) :
    zeroAtInfty.toDual 𝕜 u = zeroAtInfty.toDualCLM 𝕜 u :=
  rfl

/-- The display of [brezis2011functional] Proposition 11.19. -/
theorem zeroAtInfty.toDual_apply (u : lp (fun _ : ℕ => 𝕜) 1) (x : zeroAtInfty 𝕜 𝕜) :
    zeroAtInfty.toDual 𝕜 u x = ∑' k, u k * (x : lp (fun _ : ℕ => 𝕜) ∞) k :=
  rfl

/-- **[brezis2011functional] Proposition 11.19, existence**: every functional on `c₀` is
`x ↦ ∑' k, u k * x k` for the sequence `u k := φ (e_k)`, in `ℓ¹` by the finite-section estimate;
the two functionals agree because every `x ∈ c₀` is the sum of its coordinates
(`lp.zeroAtInfty.hasSum_single'`, the density of the finitely supported sequences). -/
theorem zeroAtInfty.toDual_surjective : Function.Surjective (zeroAtInfty.toDual 𝕜) := by
  intro φ
  obtain ⟨v, hv⟩ : ∃ v : ℕ → 𝕜, ∀ k, v k = φ (e₀ 𝕜 k) := ⟨_, fun _ => rfl⟩
  have hv_mem : Memℓp v 1 := by
    refine memℓp_gen' (C := ‖φ‖) fun s => ?_
    simp only [ENNReal.toReal_one, Real.rpow_one, hv]
    exact zeroAtInfty.sum_norm_apply_single_le φ s
  refine ⟨⟨v, hv_mem⟩, ?_⟩
  ext x
  rw [← (zeroAtInfty.hasSum_single' x |>.mapL φ).tsum_eq, zeroAtInfty.coe_toDual,
    zeroAtInfty.toDualCLM_apply]
  refine tsum_congr fun k => ?_
  have h1 : (⟨lp.single ∞ k ((x : lp (fun _ : ℕ => 𝕜) ∞) k), single_mem_zeroAtInfty 𝕜 𝕜 k _⟩ :
      zeroAtInfty 𝕜 𝕜) = (x : lp (fun _ : ℕ => 𝕜) ∞) k • e₀ 𝕜 k := by
    apply Subtype.ext
    rw [Submodule.coe_smul, e₀, ← lp.single_smul, smul_eq_mul, mul_one]
  rw [h1, map_smul, smul_eq_mul, ← hv, mul_comm]

variable (𝕜)

/-- **[brezis2011functional] Proposition 11.19**: `(c₀)* = ℓ¹`, the isometric isomorphism
`ℓ¹ ≃ₗᵢ[𝕜] (c₀)*` along `u ↦ (x ↦ ∑' k, u k * x k)`. -/
def zeroAtInfty.dualEquiv : lp (fun _ : ℕ => 𝕜) 1 ≃ₗᵢ[𝕜] StrongDual 𝕜 (zeroAtInfty 𝕜 𝕜) :=
  LinearIsometryEquiv.ofSurjective (zeroAtInfty.toDual 𝕜) zeroAtInfty.toDual_surjective

variable {𝕜}

/-- `zeroAtInfty.dualEquiv` is the pairing `u ↦ (x ↦ ∑' k, u k * x k)`. -/
theorem zeroAtInfty.dualEquiv_apply (u : lp (fun _ : ℕ => 𝕜) 1) (x : zeroAtInfty 𝕜 𝕜) :
    zeroAtInfty.dualEquiv 𝕜 u x = ∑' k, u k * (x : lp (fun _ : ℕ => 𝕜) ∞) k :=
  rfl

/-- `lp.zeroAtInfty.dualEquiv` is `lp.zeroAtInfty.toDual` as a map. -/
@[simp]
theorem zeroAtInfty.coe_dualEquiv (u : lp (fun _ : ℕ => 𝕜) 1) :
    zeroAtInfty.dualEquiv 𝕜 u = zeroAtInfty.toDual 𝕜 u :=
  rfl

end ZeroAtInftyDual

/-! ### The dual of `c` -/

section ConvergentDual

variable (𝕜 : Type*) [RCLike 𝕜]

/-- The functional `x ↦ ∑' k, u k * x k + λ * lim x` on `c` defined by `(u, λ) ∈ ℓ¹ × 𝕜`, as a
bounded linear map in `(u, λ)`; the product carries the `ℓ¹` norm `‖u‖ + ‖λ‖` (`WithLp 1`). -/
def convergent.toDualCLM :
    WithLp 1 (lp (fun _ : ℕ => 𝕜) 1 × 𝕜) →L[𝕜] StrongDual 𝕜 (convergent 𝕜 𝕜) :=
  (((ContinuousLinearMap.compL 𝕜 (convergent 𝕜 𝕜) (lp (fun _ : ℕ => 𝕜) ∞) 𝕜).flip
      (convergent 𝕜 𝕜).subtypeL).comp (lp.toDualCLM 𝕜 ℕ ∞ 1)).comp
    (WithLp.fstL 1 𝕜 (lp (fun _ : ℕ => 𝕜) 1) 𝕜) +
    (WithLp.sndL 1 𝕜 (lp (fun _ : ℕ => 𝕜) 1) 𝕜).smulRight (convergent.limCLM 𝕜 𝕜)

variable {𝕜}

/-- The functional on `c` defined by `(u, λ)`: `x ↦ ∑' k, u k * x k + λ * lim x`. -/
theorem convergent.toDualCLM_apply (u : lp (fun _ : ℕ => 𝕜) 1) (l : 𝕜) (x : convergent 𝕜 𝕜) :
    convergent.toDualCLM 𝕜 (WithLp.toLp 1 (u, l)) x =
      ∑' k, u k * (x : lp (fun _ : ℕ => 𝕜) ∞) k + l * convergent.limCLM 𝕜 𝕜 x :=
  rfl

/-- The norm of `WithLp 1 (ℓ¹ × 𝕜)` is `‖u‖ + ‖λ‖`. -/
theorem norm_toLp_one_prod (u : lp (fun _ : ℕ => 𝕜) 1) (l : 𝕜) :
    ‖(WithLp.toLp 1 (u, l) : WithLp 1 (lp (fun _ : ℕ => 𝕜) 1 × 𝕜))‖ = ‖u‖ + ‖l‖ := by
  rw [WithLp.prod_norm_eq_add (by simp)]
  simp

/-- The terms `u k * x k`, `u ∈ ℓ¹`, `x ∈ ℓ^∞`, are summable. -/
theorem summable_mul_apply_of_one_of_top (u : lp (fun _ : ℕ => 𝕜) 1)
    (x : lp (fun _ : ℕ => 𝕜) ∞) : Summable fun k => u k * x k := by
  have hsum : Summable fun k => ‖u k‖ := by
    simpa using (lp.memℓp u).summable (p := 1) (by simp)
  refine Summable.of_norm_bounded (g := fun k => ‖u k‖ * ‖x‖) (hsum.mul_right _) fun k => ?_
  rw [norm_mul]
  gcongr
  exact lp.norm_apply_le_norm ENNReal.top_ne_zero x k

/-- `‖φ_{u,λ}‖ ≤ ‖u‖₁ + ‖λ‖`, the easy half of [brezis2011functional] Proposition 11.20. -/
theorem convergent.norm_toDualCLM_apply_le (u : lp (fun _ : ℕ => 𝕜) 1) (l : 𝕜) :
    ‖convergent.toDualCLM 𝕜 (WithLp.toLp 1 (u, l))‖ ≤ ‖u‖ + ‖l‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  rw [convergent.toDualCLM_apply, add_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · calc ‖∑' k, u k * (x : lp (fun _ : ℕ => 𝕜) ∞) k‖
        = ‖lp.toDualCLM 𝕜 ℕ ∞ 1 u (x : lp (fun _ : ℕ => 𝕜) ∞)‖ := rfl
      _ ≤ ‖lp.toDualCLM 𝕜 ℕ ∞ 1 u‖ * ‖(x : lp (fun _ : ℕ => 𝕜) ∞)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖u‖ * ‖x‖ := by rw [lp.norm_toDualCLM_apply, Submodule.norm_coe]
  · rw [norm_mul]
    gcongr
    exact convergent.norm_limCLM_apply_le x

/-- The test sequence of [brezis2011functional] Proposition 11.20: `sign (u_k)` for `k < N` and
`sign λ` beyond, as an element of `ℓ^∞`. -/
private def testFun (u : lp (fun _ : ℕ => 𝕜) 1) (l : 𝕜) (N : ℕ) : lp (fun _ : ℕ => 𝕜) ∞ :=
  ⟨fun k => if k < N then sgn (u k) else sgn l, memℓp_infty ⟨1, by
    rintro _ ⟨k, rfl⟩
    dsimp only
    split_ifs <;> exact norm_sgn_le _⟩⟩

private theorem tendsto_testFun (u : lp (fun _ : ℕ => 𝕜) 1) (l : 𝕜) (N : ℕ) :
    Tendsto (⇑(testFun u l N)) atTop (𝓝 (sgn l)) := by
  refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun k hk => ?_⟩)
  change sgn l = if k < N then sgn (u k) else sgn l
  rw [ite_eq_right (not_lt.2 hk)]

/-- The test sequence of [brezis2011functional] Proposition 11.20 as an element of `c`. -/
private def testSeq (u : lp (fun _ : ℕ => 𝕜) 1) (l : 𝕜) (N : ℕ) : convergent 𝕜 𝕜 :=
  ⟨testFun u l N, sgn l, tendsto_testFun u l N⟩

private theorem testSeq_apply (u : lp (fun _ : ℕ => 𝕜) 1) (l : 𝕜) (N k : ℕ) :
    ((testSeq u l N : convergent 𝕜 𝕜) : lp (fun _ : ℕ => 𝕜) ∞) k =
      if k < N then sgn (u k) else sgn l :=
  rfl

private theorem norm_testSeq_le (u : lp (fun _ : ℕ => 𝕜) 1) (l : 𝕜) (N : ℕ) :
    ‖testSeq u l N‖ ≤ 1 := by
  rw [← Submodule.norm_coe]
  refine lp.norm_le_of_forall_le zero_le_one fun k => ?_
  rw [testSeq_apply]
  split_ifs <;> exact norm_sgn_le _

private theorem limCLM_testSeq (u : lp (fun _ : ℕ => 𝕜) 1) (l : 𝕜) (N : ℕ) :
    convergent.limCLM 𝕜 𝕜 (testSeq u l N) = sgn l :=
  convergent.limCLM_eq_of_tendsto (tendsto_testFun u l N)

/-- **`‖u‖₁ + ‖λ‖ ≤ ‖φ_{u,λ}‖`**, the hard half of [brezis2011functional] Proposition 11.20:
testing on `x_N = (sign u_1, …, sign u_N, sign λ, sign λ, …)` gives
`∑_{k < N} ‖u_k‖ + ‖λ‖ - ∑_{k ≥ N} ‖u_k‖ ≤ ‖φ_{u,λ}‖`, and `N → ∞`. -/
theorem convergent.norm_add_norm_le_norm_toDualCLM_apply (u : lp (fun _ : ℕ => 𝕜) 1) (l : 𝕜) :
    ‖u‖ + ‖l‖ ≤ ‖convergent.toDualCLM 𝕜 (WithLp.toLp 1 (u, l))‖ := by
  set φ := convergent.toDualCLM 𝕜 (WithLp.toLp 1 (u, l)) with hφ
  have hsum : Summable fun k => ‖u k‖ := by
    simpa using (lp.memℓp u).summable (p := 1) (by simp)
  -- the estimate at a fixed `N`
  have key : ∀ N : ℕ, ∑ k ∈ Finset.range N, ‖u k‖ + ‖l‖ - ∑' k, ‖u (k + N)‖ ≤ ‖φ‖ := by
    intro N
    obtain ⟨x, hx⟩ : ∃ x, x = testSeq u l N := ⟨_, rfl⟩
    have hlim : convergent.limCLM 𝕜 𝕜 x = sgn l := by rw [hx]; exact limCLM_testSeq u l N
    have hx1 : ‖x‖ ≤ 1 := by rw [hx]; exact norm_testSeq_le u l N
    have hφx : φ x = ((∑ k ∈ Finset.range N, ‖u k‖ + ‖l‖ : ℝ) : 𝕜) +
        ∑' k, u (k + N) * (x : lp (fun _ : ℕ => 𝕜) ∞) (k + N) := by
      rw [hφ, convergent.toDualCLM_apply, hlim, mul_sgn,
        ← (summable_mul_apply_of_one_of_top u x).sum_add_tsum_nat_add N]
      have : ∑ k ∈ Finset.range N, u k * (x : lp (fun _ : ℕ => 𝕜) ∞) k =
          ((∑ k ∈ Finset.range N, ‖u k‖ : ℝ) : 𝕜) := by
        rw [RCLike.ofReal_sum]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [hx, testSeq_apply, ite_eq_left (Finset.mem_range.1 hk), mul_sgn]
      rw [this]
      push_cast
      ring
    have htail : ‖∑' k, u (k + N) * (x : lp (fun _ : ℕ => 𝕜) ∞) (k + N)‖ ≤ ∑' k, ‖u (k + N)‖ := by
      have hs1 : Summable fun k => ‖u (k + N)‖ := (summable_nat_add_iff N).2 hsum
      have hs2 : Summable fun k => u (k + N) * (x : lp (fun _ : ℕ => 𝕜) ∞) (k + N) :=
        (summable_nat_add_iff N).2 (summable_mul_apply_of_one_of_top u x)
      have hxk : ∀ k, ‖(x : lp (fun _ : ℕ => 𝕜) ∞) (k + N)‖ ≤ 1 := fun k => by
        rw [hx, testSeq_apply]
        split_ifs <;> exact norm_sgn_le _
      have hle : ∀ k, ‖u (k + N) * (x : lp (fun _ : ℕ => 𝕜) ∞) (k + N)‖ ≤ ‖u (k + N)‖ :=
        fun k => by
          rw [norm_mul]
          exact mul_le_of_le_one_right (norm_nonneg _) (hxk k)
      calc ‖∑' k, u (k + N) * (x : lp (fun _ : ℕ => 𝕜) ∞) (k + N)‖
          ≤ ∑' k, ‖u (k + N) * (x : lp (fun _ : ℕ => 𝕜) ∞) (k + N)‖ :=
            norm_tsum_le_tsum_norm hs2.norm
        _ ≤ ∑' k, ‖u (k + N)‖ := Summable.tsum_le_tsum hle hs2.norm hs1
    have hnn : 0 ≤ ∑ k ∈ Finset.range N, ‖u k‖ + ‖l‖ := by positivity
    calc ∑ k ∈ Finset.range N, ‖u k‖ + ‖l‖ - ∑' k, ‖u (k + N)‖
        ≤ ‖((∑ k ∈ Finset.range N, ‖u k‖ + ‖l‖ : ℝ) : 𝕜)‖ -
          ‖∑' k, u (k + N) * (x : lp (fun _ : ℕ => 𝕜) ∞) (k + N)‖ := by
          rw [RCLike.norm_ofReal, abs_of_nonneg hnn]
          exact sub_le_sub_left htail _
      _ ≤ ‖φ x‖ := by
          rw [hφx]
          exact sub_le_iff_le_add.2 (norm_le_add_norm_add _ _)
      _ ≤ ‖φ‖ * ‖x‖ := φ.le_opNorm x
      _ ≤ ‖φ‖ * 1 := mul_le_mul_of_nonneg_left hx1 (norm_nonneg _)
      _ = ‖φ‖ := mul_one _
  -- let `N → ∞`
  have h1 : Tendsto (fun N => ∑ k ∈ Finset.range N, ‖u k‖) atTop (𝓝 ‖u‖) := by
    have := (lp.hasSum_norm (p := 1) (by simp) u).tendsto_sum_nat
    simpa using this
  have h2 : Tendsto (fun N => ∑' k, ‖u (k + N)‖) atTop (𝓝 0) :=
    tendsto_sum_nat_add fun k => ‖u k‖
  have h3 : Tendsto (fun N => ∑ k ∈ Finset.range N, ‖u k‖ + ‖l‖ - ∑' k, ‖u (k + N)‖) atTop
      (𝓝 (‖u‖ + ‖l‖ - 0)) := (h1.add_const _).sub h2
  rw [sub_zero] at h3
  exact le_of_tendsto' h3 key

/-- **[brezis2011functional] Proposition 11.20, the norm identity** `‖φ_{u,λ}‖ = ‖u‖₁ + ‖λ‖`. -/
theorem convergent.norm_toDualCLM_apply (w : WithLp 1 (lp (fun _ : ℕ => 𝕜) 1 × 𝕜)) :
    ‖convergent.toDualCLM 𝕜 w‖ = ‖w‖ := by
  obtain ⟨⟨u, l⟩⟩ := w
  rw [norm_toLp_one_prod]
  exact le_antisymm (convergent.norm_toDualCLM_apply_le u l)
    (convergent.norm_add_norm_le_norm_toDualCLM_apply u l)

variable (𝕜)

/-- **[brezis2011functional] Proposition 11.20, the isometry**: `(u, λ) ↦ (x ↦ ∑' u k * x k +
λ lim x)` is a linear isometry `WithLp 1 (ℓ¹ × 𝕜) → c*`. -/
def convergent.toDual : WithLp 1 (lp (fun _ : ℕ => 𝕜) 1 × 𝕜) →ₗᵢ[𝕜] StrongDual 𝕜 (convergent 𝕜 𝕜) :=
  ⟨(convergent.toDualCLM 𝕜).toLinearMap, convergent.norm_toDualCLM_apply⟩

variable {𝕜}

/-- `lp.convergent.toDual` is `lp.convergent.toDualCLM` as a map. -/
@[simp]
theorem convergent.coe_toDual (w : WithLp 1 (lp (fun _ : ℕ => 𝕜) 1 × 𝕜)) :
    convergent.toDual 𝕜 w = convergent.toDualCLM 𝕜 w :=
  rfl

/-- The display of [brezis2011functional] Proposition 11.20. -/
theorem convergent.toDual_apply (u : lp (fun _ : ℕ => 𝕜) 1) (l : 𝕜) (x : convergent 𝕜 𝕜) :
    convergent.toDual 𝕜 (WithLp.toLp 1 (u, l)) x =
      ∑' k, u k * (x : lp (fun _ : ℕ => 𝕜) ∞) k + l * convergent.limCLM 𝕜 𝕜 x :=
  rfl

/-- The inclusion `c₀ → c`, as a bounded linear map. -/
private def incl : zeroAtInfty 𝕜 𝕜 →L[𝕜] convergent 𝕜 𝕜 :=
  (Submodule.inclusion (zeroAtInfty_le_convergent 𝕜 𝕜)).mkContinuous 1 fun x => by
    rw [one_mul, ← Submodule.norm_coe, ← Submodule.norm_coe (s := zeroAtInfty 𝕜 𝕜)]
    rfl

/-- **[brezis2011functional] Proposition 11.20, existence**: restricting `φ ∈ c*` to `c₀`
gives `u ∈ ℓ¹` with `φ y = ∑' u k * y k` on `c₀`; with `e = (1, 1, …)` and
`λ := φ e - ∑' u k`, every `x ∈ c` is `y + (lim x) e` with `y ∈ c₀`, so
`φ x = ∑' u k * x k + λ lim x`. -/
theorem convergent.toDual_surjective : Function.Surjective (convergent.toDual 𝕜) := by
  intro φ
  set u := (zeroAtInfty.dualEquiv 𝕜).symm (φ.comp incl) with hu
  have hu' : ∀ y : zeroAtInfty 𝕜 𝕜, φ (incl y) = ∑' k, u k * (y : lp (fun _ : ℕ => 𝕜) ∞) k := by
    intro y
    have := DFunLike.congr_fun ((zeroAtInfty.dualEquiv 𝕜).apply_symm_apply (φ.comp incl)) y
    rw [← hu, zeroAtInfty.dualEquiv_apply] at this
    rw [this]
    rfl
  set e : convergent 𝕜 𝕜 := ⟨constL 𝕜 𝕜 1, constL_mem_convergent 𝕜 𝕜 1⟩ with he
  refine ⟨WithLp.toLp 1 (u, φ e - ∑' k, u k), ?_⟩
  ext x
  rw [convergent.coe_toDual, convergent.toDualCLM_apply]
  set a := convergent.limCLM 𝕜 𝕜 x with ha
  -- `x = y + a • e` with `y ∈ c₀`
  set y : zeroAtInfty 𝕜 𝕜 := ⟨(x : lp (fun _ : ℕ => 𝕜) ∞) - constL 𝕜 𝕜 a,
    convergent.sub_constL_limCLM_mem_zeroAtInfty x⟩ with hy
  have hxy : x = incl y + a • e := by
    apply Subtype.ext
    rw [Submodule.coe_add, Submodule.coe_smul, he]
    change (x : lp (fun _ : ℕ => 𝕜) ∞) = ((x : lp (fun _ : ℕ => 𝕜) ∞) - constL 𝕜 𝕜 a) +
      a • constL 𝕜 𝕜 1
    rw [← map_smul, smul_eq_mul, mul_one, sub_add_cancel]
  have hsum : Summable fun k => u k * (x : lp (fun _ : ℕ => 𝕜) ∞) k :=
    summable_mul_apply_of_one_of_top u x
  have hsum' : Summable fun k => u k * a := by
    simpa using summable_mul_apply_of_one_of_top u (constL 𝕜 𝕜 a)
  symm
  calc φ x = φ (incl y) + a * φ e := by rw [hxy, map_add, map_smul, smul_eq_mul]
    _ = ∑' k, u k * ((x : lp (fun _ : ℕ => 𝕜) ∞) k - a) + a * φ e := by
        rw [hu' y]
        rfl
    _ = ∑' k, u k * (x : lp (fun _ : ℕ => 𝕜) ∞) k - a * ∑' k, u k + a * φ e := by
        simp_rw [mul_sub]
        rw [hsum.tsum_sub hsum', tsum_mul_right, mul_comm a, mul_comm _ a]
    _ = ∑' k, u k * (x : lp (fun _ : ℕ => 𝕜) ∞) k + (φ e - ∑' k, u k) * a := by ring

variable (𝕜)

/-- **[brezis2011functional] Proposition 11.20**: `c* = ℓ¹ × 𝕜` with the norm `‖u‖₁ + ‖λ‖`,
the isometric isomorphism `WithLp 1 (ℓ¹ × 𝕜) ≃ₗᵢ[𝕜] c*` along
`(u, λ) ↦ (x ↦ ∑' k, u k * x k + λ lim x)`. -/
def convergent.dualEquiv :
    WithLp 1 (lp (fun _ : ℕ => 𝕜) 1 × 𝕜) ≃ₗᵢ[𝕜] StrongDual 𝕜 (convergent 𝕜 𝕜) :=
  LinearIsometryEquiv.ofSurjective (convergent.toDual 𝕜) convergent.toDual_surjective

variable {𝕜}

/-- `convergent.dualEquiv` is the pairing `(u, λ) ↦ (x ↦ ∑' k, u k * x k + λ lim x)`. -/
theorem convergent.dualEquiv_apply (u : lp (fun _ : ℕ => 𝕜) 1) (l : 𝕜) (x : convergent 𝕜 𝕜) :
    convergent.dualEquiv 𝕜 (WithLp.toLp 1 (u, l)) x =
      ∑' k, u k * (x : lp (fun _ : ℕ => 𝕜) ∞) k + l * convergent.limCLM 𝕜 𝕜 x :=
  rfl

/-- `lp.convergent.dualEquiv` is `lp.convergent.toDual` as a map. -/
@[simp]
theorem convergent.coe_dualEquiv (w : WithLp 1 (lp (fun _ : ℕ => 𝕜) 1 × 𝕜)) :
    convergent.dualEquiv 𝕜 w = convergent.toDual 𝕜 w :=
  rfl

end ConvergentDual

/-! ### Non-reflexivity of `c₀`, `ℓ^∞`, `c` and `ℓ¹` -/

section NotReflexive

variable (𝕜 : Type*) [RCLike 𝕜]

variable {𝕜} in
/-- The functional of `(c₀)*` corresponding to `e_k ∈ ℓ¹` is the evaluation at `k`. -/
theorem zeroAtInfty.dualEquiv_single_apply (k : ℕ) (x : zeroAtInfty 𝕜 𝕜) :
    zeroAtInfty.dualEquiv 𝕜 (lp.single 1 k 1) x = (x : lp (fun _ : ℕ => 𝕜) ∞) k := by
  rw [zeroAtInfty.dualEquiv_apply, tsum_eq_single k fun j hj => by
    rw [lp.single_apply, Pi.single_eq_of_ne hj, zero_mul]]
  rw [lp.single_apply, Pi.single_eq_same, one_mul]

/-- **[brezis2011functional] Proposition 11.21, `c₀`**: `c₀` is not reflexive. Under
`(c₀)* = ℓ¹` and `(ℓ¹)* = ℓ^∞`, the canonical injection `c₀ → (c₀)**` is the inclusion
`c₀ → ℓ^∞`, which misses `(1, 1, 1, …)`: the functional `Φ := (u ↦ ∑' u k) ∘ ((c₀)* ≅ ℓ¹)` on
`(c₀)*` would be the evaluation at some `x ∈ c₀`, and testing on the functionals `e_k` gives
`x k = 1` for every `k`, contradicting `x k → 0`. -/
theorem zeroAtInfty.not_isReflexive : ¬ NormedSpace.IsReflexive 𝕜 (zeroAtInfty 𝕜 𝕜) := by
  intro h
  set e := zeroAtInfty.dualEquiv 𝕜 with he
  set Φ : StrongDual 𝕜 (StrongDual 𝕜 (zeroAtInfty 𝕜 𝕜)) :=
    (lp.tsumCLM 𝕜 ℕ 𝕜).comp (e.symm.toContinuousLinearEquiv :
      StrongDual 𝕜 (zeroAtInfty 𝕜 𝕜) →L[𝕜] lp (fun _ : ℕ => 𝕜) 1) with hΦ
  obtain ⟨x, hx⟩ :=
    NormedSpace.surjective_inclusionInDoubleDual (𝕜 := 𝕜) (V := zeroAtInfty 𝕜 𝕜) Φ
  have hk : ∀ k : ℕ, (x : lp (fun _ : ℕ => 𝕜) ∞) k = 1 := by
    intro k
    have := DFunLike.congr_fun hx (e (lp.single 1 k 1))
    rw [NormedSpace.dual_def, hΦ, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.symm_apply_apply,
      lp.tsumCLM_apply, he, zeroAtInfty.dualEquiv_single_apply,
      tsum_eq_single k fun j hj => by rw [lp.single_apply, Pi.single_eq_of_ne hj],
      lp.single_apply, Pi.single_eq_same] at this
    exact this
  have h0 : Tendsto (⇑(x : lp (fun _ : ℕ => 𝕜) ∞)) atTop (𝓝 0) := x.2
  rw [show ⇑(x : lp (fun _ : ℕ => 𝕜) ∞) = fun _ => (1 : 𝕜) from funext hk] at h0
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h0)

/-- **[brezis2011functional] Proposition 11.21, `ℓ^∞`**: `ℓ^∞` is not reflexive, since its closed
subspace `c₀` is not (Proposition 3.20). -/
theorem not_isReflexive_top : ¬ NormedSpace.IsReflexive 𝕜 (lp (fun _ : ℕ => 𝕜) ∞) := fun _ =>
  zeroAtInfty.not_isReflexive 𝕜
    (NormedSpace.isReflexive_of_isClosed (zeroAtInfty 𝕜 𝕜) (isClosed_zeroAtInfty 𝕜 𝕜))

/-- **[brezis2011functional] Proposition 11.21, `c`**: `c` is not reflexive, since its closed
subspace `c₀` is not (Proposition 3.20). -/
theorem convergent.not_isReflexive : ¬ NormedSpace.IsReflexive 𝕜 (convergent 𝕜 𝕜) := by
  intro h
  -- `c₀`, seen inside `c`
  set M : Submodule 𝕜 (convergent 𝕜 𝕜) := (zeroAtInfty 𝕜 𝕜).comap (convergent 𝕜 𝕜).subtype with hM
  have hMc : IsClosed (M : Set (convergent 𝕜 𝕜)) :=
    (isClosed_zeroAtInfty 𝕜 𝕜).preimage continuous_subtype_val
  have hMr : NormedSpace.IsReflexive 𝕜 M := NormedSpace.isReflexive_of_isClosed M hMc
  let e : M ≃ₗᵢ[𝕜] zeroAtInfty 𝕜 𝕜 :=
    { Submodule.comapSubtypeEquivOfLe (zeroAtInfty_le_convergent 𝕜 𝕜) with
      norm_map' := fun _ => rfl }
  exact zeroAtInfty.not_isReflexive 𝕜
    ((NormedSpace.isReflexive_congr e.toContinuousLinearEquiv).1 hMr)

/-- **[brezis2011functional] Proposition 11.21, `ℓ¹`**: `ℓ¹` is not reflexive: its dual
`ℓ^∞` (Proposition 11.18) would be reflexive too (Corollary 3.21). -/
theorem not_isReflexive_one : ¬ NormedSpace.IsReflexive 𝕜 (lp (fun _ : ℕ => 𝕜) 1) := by
  intro h
  have h1 : NormedSpace.IsReflexive 𝕜 (StrongDual 𝕜 (lp (fun _ : ℕ => 𝕜) 1)) := inferInstance
  exact not_isReflexive_top 𝕜
    ((NormedSpace.isReflexive_congr
      (dualEquiv 𝕜 ℕ 1 ∞ ENNReal.one_ne_top).toContinuousLinearEquiv).2 h1)

end NotReflexive

/-! ### Separability -/

section Separable

open TopologicalSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [SeparableSpace 𝕜]

/-- A normed space with a separable subset whose span is dense is separable. -/
theorem _root_.TopologicalSpace.separableSpace_of_isSeparable_of_dense_span {V : Type*}
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] {s : Set V} (hs : IsSeparable s)
    (hd : Dense (Submodule.span 𝕜 s : Set V)) : SeparableSpace V := by
  rw [← isSeparable_univ_iff, ← hd.closure_eq]
  exact hs.span.closure

/-- **[brezis2011functional] Proposition 11.16, `ℓ^p`**: for a countable index type, a separable
`E` (over a separable field) and `p < ∞`, `ℓ^p(α, E)` is separable: the finitely supported
sequences are dense (`lp.hasSum_single`) and are spanned by the separable set
`⋃ i, range (lp.single p i)`. -/
theorem separableSpace {α : Type*} [Countable α] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [SeparableSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    SeparableSpace (lp (fun _ : α => E) p) := by
  classical
  refine separableSpace_of_isSeparable_of_dense_span (𝕜 := 𝕜)
    (s := ⋃ i, Set.range (lp.single (E := fun _ : α => E) p i)) ?_ ?_
  · refine IsSeparable.iUnion fun i => ?_
    rw [← Set.image_univ]
    exact (IsSeparable.of_separableSpace _).image (lp.isometry_single i).continuous
  · refine dense_iff_closure_eq.2 (Set.eq_univ_of_forall fun f => ?_)
    refine mem_closure_of_tendsto (lp.hasSum_single hp f) (Eventually.of_forall fun s => ?_)
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.subset_span (Set.mem_iUnion.2 ⟨i, Set.mem_range_self _⟩)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **[brezis2011functional] Proposition 11.16, `c₀`**: for a separable `E`, `c₀` is separable —
the finitely supported sequences are dense in `c₀` (`lp.zeroAtInfty.hasSum_single'`). -/
instance zeroAtInfty.instSeparableSpace [SeparableSpace E] : SeparableSpace (zeroAtInfty 𝕜 E) := by
  refine separableSpace_of_isSeparable_of_dense_span (𝕜 := 𝕜) (s := ⋃ k, Set.range fun a : E =>
    (⟨lp.single ∞ k a, single_mem_zeroAtInfty 𝕜 E k a⟩ : zeroAtInfty 𝕜 E)) ?_ ?_
  · refine IsSeparable.iUnion fun k => ?_
    rw [← Set.image_univ]
    exact (IsSeparable.of_separableSpace _).image
      ((lp.isometry_single (E := fun _ : ℕ => E) (p := ∞) k).continuous.subtype_mk _)
  · refine dense_iff_closure_eq.2 (Set.eq_univ_of_forall fun x => ?_)
    refine mem_closure_of_tendsto (zeroAtInfty.hasSum_single' x) (Eventually.of_forall fun s => ?_)
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.subset_span (Set.mem_iUnion.2 ⟨k, Set.mem_range_self _⟩)

/-- **[brezis2011functional] Proposition 11.16, `c`**: for a separable `E`, `c` is separable —
every `x ∈ c` is `(x - (lim x) e) + (lim x) e` with `x - (lim x) e ∈ c₀` and `e = (1, 1, …)`,
so `c` is spanned by the finitely supported sequences and the constant sequences (the book's
`D + λ (1, 1, 1, …)`). -/
instance convergent.instSeparableSpace [SeparableSpace E] : SeparableSpace (convergent 𝕜 E) := by
  refine separableSpace_of_isSeparable_of_dense_span (𝕜 := 𝕜) (s := (⋃ k, Set.range fun a : E =>
    (⟨lp.single ∞ k a, zeroAtInfty_le_convergent 𝕜 E (single_mem_zeroAtInfty 𝕜 E k a)⟩ :
      convergent 𝕜 E)) ∪ Set.range fun a : E =>
    (⟨constL 𝕜 E a, constL_mem_convergent 𝕜 E a⟩ : convergent 𝕜 E)) ?_ ?_
  · refine IsSeparable.union (IsSeparable.iUnion fun k => ?_) ?_
    · rw [← Set.image_univ]
      exact (IsSeparable.of_separableSpace _).image
        ((lp.isometry_single (E := fun _ : ℕ => E) (p := ∞) k).continuous.subtype_mk _)
    · rw [← Set.image_univ]
      exact (IsSeparable.of_separableSpace _).image ((constL 𝕜 E).continuous.subtype_mk _)
  · refine dense_iff_closure_eq.2 (Set.eq_univ_of_forall fun x => ?_)
    set a := convergent.limCLM 𝕜 E x with ha
    set y : lp (fun _ : ℕ => E) ∞ := (x : lp (fun _ : ℕ => E) ∞) - constL 𝕜 E a with hy
    have hy0 : y ∈ zeroAtInfty 𝕜 E := convergent.sub_constL_limCLM_mem_zeroAtInfty x
    refine mem_closure_of_tendsto (b := atTop) (f := fun s : Finset ℕ => ∑ k ∈ s,
      (⟨lp.single ∞ k (y k), zeroAtInfty_le_convergent 𝕜 E (single_mem_zeroAtInfty 𝕜 E k _)⟩ :
        convergent 𝕜 E) + ⟨constL 𝕜 E a, constL_mem_convergent 𝕜 E a⟩) ?_
      (Eventually.of_forall fun s => ?_)
    · refine tendsto_subtype_rng.2 ?_
      have h := (zeroAtInfty.hasSum_single hy0).add_const (constL 𝕜 E a)
      have hyx : y + constL 𝕜 E a = x := by rw [hy, sub_add_cancel]
      rw [hyx] at h
      refine h.congr fun s => ?_
      simp only [Submodule.coe_add, Submodule.coe_sum]
    · refine Submodule.add_mem _ (Submodule.sum_mem _ fun k _ => Submodule.subset_span
        (Set.mem_union_left _ (Set.mem_iUnion.2 ⟨k, Set.mem_range_self _⟩))) ?_
      exact Submodule.subset_span (Set.mem_union_right _ (Set.mem_range_self _))

/-- **[brezis2011functional] Proposition 11.17**: `ℓ^∞` over an infinite index type is not
separable (for any nontrivial `E`): the indicator sequences `e · 1_A`, `A ⊆ α`, are pairwise at
distance `‖e‖`, so the balls of radius `‖e‖ / 2` around them are pairwise disjoint, nonempty and
open, and a separable space has only countably many such
(`Pairwise.countable_of_isOpen_disjoint`); but `Set α` is uncountable (Cantor). -/
theorem not_separableSpace_top {α : Type*} [Infinite α] {E : Type*} [NormedAddCommGroup E]
    [Nontrivial E] : ¬ SeparableSpace (lp (fun _ : α => E) ∞) := by
  intro h
  classical
  obtain ⟨e, he⟩ := exists_ne (0 : E)
  have he0 : 0 < ‖e‖ := norm_pos_iff.2 he
  -- the indicator sequences
  set ind : Set α → lp (fun _ : α => E) ∞ := fun A =>
    ⟨fun i => if i ∈ A then e else 0, memℓp_infty ⟨‖e‖, by
      rintro _ ⟨i, rfl⟩
      dsimp only
      split_ifs <;> simp⟩⟩ with hind
  have hdist : ∀ A B, A ≠ B → ‖e‖ ≤ dist (ind A) (ind B) := by
    intro A B hAB
    obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ A ↔ i ∈ B) := by
      by_contra h'
      refine hAB (Set.ext fun i => ?_)
      by_contra hi
      exact h' ⟨i, hi⟩
    rw [dist_eq_norm]
    refine le_trans ?_ (lp.norm_apply_le_norm ENNReal.top_ne_zero (ind A - ind B) i)
    rw [lp.coeFn_sub, Pi.sub_apply, hind]
    dsimp only
    by_cases hA : i ∈ A <;> by_cases hB : i ∈ B <;> simp [hA, hB] at hi ⊢
  have hdisj : Pairwise (Function.onFun Disjoint fun A => Metric.ball (ind A) (‖e‖ / 2)) :=
    fun A B hAB => Metric.ball_disjoint_ball (le_of_eq_of_le (add_halves _) (hdist A B hAB))
  have hcount : Countable (Set α) := hdisj.countable_of_isOpen_disjoint
    (fun _ => Metric.isOpen_ball) fun _ => Metric.nonempty_ball.2 (by positivity)
  obtain ⟨g, hg⟩ := Countable.exists_injective_nat (Set α)
  exact Function.cantor_injective ((Infinite.natEmbedding α) ∘ g)
    ((Infinite.natEmbedding α).injective.comp hg)

end Separable

/-! ### `ℓ^p` is `L^p` of the counting measure; uniform convexity -/

section Count

open MeasureTheory

variable {α : Type*} {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}

/-- The `tsum` of `‖f a‖ₑ ^ P` is the `ENNReal.ofReal` of the real `tsum` when the latter is
summable. -/
theorem tsum_enorm_rpow_eq_ofReal {P : ℝ} (hP : 0 ≤ P) {f : α → E}
    (hf : Summable fun a => ‖f a‖ ^ P) :
    ∑' a, ‖f a‖ₑ ^ P = ENNReal.ofReal (∑' a, ‖f a‖ ^ P) := by
  rw [ENNReal.ofReal_tsum_of_nonneg (fun a => Real.rpow_nonneg (norm_nonneg _) _) hf]
  refine tsum_congr fun a => ?_
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hP, ofReal_norm]

/-- Conversely, a finite `tsum` of `‖f a‖ₑ ^ P` gives a summable real family. -/
theorem summable_norm_rpow_of_tsum_enorm_rpow_ne_top {P : ℝ} {f : α → E}
    (hf : ∑' a, ‖f a‖ₑ ^ P ≠ ∞) : Summable fun a => ‖f a‖ ^ P := by
  have := ENNReal.summable_toReal hf
  refine this.congr fun a => ?_
  rw [← ENNReal.toReal_rpow, toReal_enorm]

/-- The supremum of `‖f a‖ₑ` is the `ENNReal.ofReal` of the supremum of `‖f a‖` when the latter
is bounded (and the index type is nonempty or the supremum is read as `0`). -/
theorem iSup_enorm_eq_ofReal_iSup {f : α → E} (hf : BddAbove (Set.range fun a => ‖f a‖)) :
    ⨆ a, ‖f a‖ₑ = ENNReal.ofReal (⨆ a, ‖f a‖) := by
  have hbdd : BddAbove (Set.range fun a => ‖f a‖₊) := by
    obtain ⟨C, hC⟩ := hf
    refine ⟨(max C 0).toNNReal, ?_⟩
    rintro _ ⟨a, rfl⟩
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (le_max_right _ _)]
    exact (hC ⟨a, rfl⟩).trans (le_max_left _ _)
  simp_rw [enorm_eq_nnnorm]
  rw [← ENNReal.coe_iSup hbdd,
    show (⨆ a, ‖f a‖) = ((⨆ a, ‖f a‖₊ : ℝ≥0) : ℝ) by rw [NNReal.coe_iSup]; simp_rw [coe_nnnorm],
    ENNReal.ofReal_coe_nnreal]

variable [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]

/-- Every function on a countable measurable space with measurable singletons is a.e. strongly
measurable for the counting measure. -/
theorem aestronglyMeasurable_count (f : α → E) :
    AEStronglyMeasurable f (Measure.count : Measure α) :=
  StronglyMeasurable.of_discrete.aestronglyMeasurable

/-- The `L^p` seminorm for the counting measure, `p ≠ 0, ∞`, as a `tsum`. -/
theorem eLpNorm_count_eq_tsum (hp0 : p ≠ 0) (hp : p ≠ ∞) (f : α → E) :
    eLpNorm f p (Measure.count : Measure α) = (∑' a, ‖f a‖ₑ ^ p.toReal) ^ (1 / p.toReal) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp (aestronglyMeasurable_count f),
    lintegral_count]

/-- `Memℓp f p ↔ MemLp f p count` for `1 ≤ p`: the finiteness of `∑ ‖f a‖ ^ p`, resp. of
`sup ‖f a‖`, read on either side. -/
theorem memℓp_iff_memLp_count [Fact (1 ≤ p)] (f : α → E) :
    Memℓp f p ↔ MemLp f p (Measure.count : Measure α) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  rw [memLp_iff]
  rcases eq_or_ne p ∞ with rfl | hp
  · rw [memℓp_infty_iff, eLpNorm_exponent_top (aestronglyMeasurable_count f), eLpNormEssSup_count]
    constructor
    · intro hf
      rw [iSup_enorm_eq_ofReal_iSup hf]
      exact ENNReal.ofReal_lt_top
    · intro hf
      refine ⟨(⨆ a, ‖f a‖ₑ).toReal, ?_⟩
      rintro _ ⟨a, rfl⟩
      dsimp only
      rw [← toReal_enorm]
      exact ENNReal.toReal_mono hf.ne (le_iSup (fun a => ‖f a‖ₑ) a)
  · have hP : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
    rw [memℓp_gen_iff hP, eLpNorm_count_eq_tsum hp0 hp,
      ENNReal.rpow_lt_top_iff_of_pos (by positivity)]
    constructor
    · intro hf
      rw [tsum_enorm_rpow_eq_ofReal hP.le hf]
      exact ENNReal.ofReal_lt_top
    · exact fun hf => summable_norm_rpow_of_tsum_enorm_rpow_ne_top hf.ne

/-- The `L^p` norm for the counting measure of an `ℓ^p` sequence is its `ℓ^p` norm. -/
theorem toReal_eLpNorm_count [Fact (1 ≤ p)] (f : lp (fun _ : α => E) p) :
    (eLpNorm f p (Measure.count : Measure α)).toReal = ‖f‖ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  rcases eq_or_ne p ∞ with rfl | hp
  · rw [eLpNorm_exponent_top (aestronglyMeasurable_count _), eLpNormEssSup_count,
      iSup_enorm_eq_ofReal_iSup (lp.memℓp f).bddAbove, lp.norm_eq_ciSup, ENNReal.toReal_ofReal]
    rcases isEmpty_or_nonempty α with hα | hα
    · simp
    · exact le_ciSup_of_le (lp.memℓp f).bddAbove (Classical.arbitrary α) (norm_nonneg _)
  · have hP : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
    rw [eLpNorm_count_eq_tsum hp0 hp, tsum_enorm_rpow_eq_ofReal hP.le ((lp.memℓp f).summable hP),
      ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (tsum_nonneg fun a => by positivity),
      lp.norm_eq_tsum_rpow hP]

end Count

section CountEquiv

open MeasureTheory

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] (α : Type*) [MeasurableSpace α]
  [MeasurableSingletonClass α] [Countable α] (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The isometric embedding `ℓ^p(α, E) → L^p(count)`, `f ↦ [f]`. -/
def lpToLpCount : lp (fun _ : α => E) p →ₗᵢ[𝕜] Lp E p (Measure.count : Measure α) where
  toFun f := ((memℓp_iff_memLp_count f).1 (lp.memℓp f)).toLp f
  map_add' f g := by
    change MemLp.toLp (⇑f + ⇑g) _ = _
    exact MemLp.toLp_add _ _
  map_smul' c f := by
    change MemLp.toLp (c • ⇑f) _ = _
    exact MemLp.toLp_const_smul _ _
  norm_map' f := by
    change ‖MemLp.toLp (⇑f) ((memℓp_iff_memLp_count f).1 (lp.memℓp f))‖ = _
    rw [Lp.norm_toLp]
    exact toReal_eLpNorm_count f

/-- On the counting measure the class `[f]` has `f` itself as its function. -/
@[simp]
theorem coeFn_lpToLpCount (f : lp (fun _ : α => E) p) : ⇑(lpToLpCount 𝕜 α E p f) = ⇑f := by
  funext a
  exact Measure.ae_count_iff.1
    (MemLp.coeFn_toLp ((memℓp_iff_memLp_count f).1 (lp.memℓp f))) a

/-- **`ℓ^p` is `L^p` of the counting measure** — the identification [brezis2011functional]
§11.3 uses to import chapter 4 ("Theorem 4.8 applied to `Ω = ℕ` equipped with the counting
measure"): for a countable index type with measurable singletons and `1 ≤ p`,
`ℓ^p(α, E) ≃ₗᵢ[𝕜] L^p(count)`, `f ↦ [f]`. On the counting measure a.e. equality is equality,
so the inverse is the representative itself. -/
def lpLIELpCount : lp (fun _ : α => E) p ≃ₗᵢ[𝕜] Lp E p (Measure.count : Measure α) :=
  LinearIsometryEquiv.ofSurjective (lpToLpCount 𝕜 α E p) fun g =>
    ⟨⟨(g : α → E), (memℓp_iff_memLp_count _).2 (Lp.memLp g)⟩, Lp.toLp_coeFn g (Lp.memLp g)⟩

/-- `lp.lpLIELpCount` is `lp.lpToLpCount` as a map. -/
@[simp]
theorem lpLIELpCount_apply (f : lp (fun _ : α => E) p) :
    lpLIELpCount 𝕜 α E p f = lpToLpCount 𝕜 α E p f :=
  rfl

/-- The class of `f ∈ ℓ^p` in `L^p(count)` has `f` itself as its function. -/
@[simp]
theorem coeFn_lpLIELpCount (f : lp (fun _ : α => E) p) : ⇑(lpLIELpCount 𝕜 α E p f) = ⇑f := by
  rw [lpLIELpCount_apply, coeFn_lpToLpCount]

/-- The `ℓ^p` sequence of a class in `L^p(count)` is its (unique) representative. -/
@[simp]
theorem coeFn_lpLIELpCount_symm (g : Lp E p (Measure.count : Measure α)) :
    ⇑((lpLIELpCount 𝕜 α E p).symm g) = ⇑g := by
  have h := coeFn_lpLIELpCount 𝕜 α E p ((lpLIELpCount 𝕜 α E p).symm g)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h.symm

end CountEquiv

section UniformConvex

/-- **[brezis2011functional] Proposition 11.15, uniform convexity**: `ℓ^p(α, ℝ)` is uniformly
convex for `1 < p < ∞` and a countable index type, transported from `L^p` of the counting measure
(`MeasureTheory.Lp.instUniformConvexSpace`, Clarkson's inequalities) along `lp.lpLIELpCount` —
the book's route, "Theorem 4.10 and Exercise 4.12 with `Ω = ℕ`". -/
theorem uniformConvexSpace {α : Type*} [Countable α] {p : ℝ≥0∞} [Fact (1 < p)] [Fact (p ≠ ∞)] :
    UniformConvexSpace (lp (fun _ : α => ℝ) p) := by
  let _ : MeasurableSpace α := ⊤
  have : MeasurableSingletonClass α := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  exact uniformConvexSpace_of_linearIsometryEquiv (lpLIELpCount ℝ α ℝ p)

/-- `ℓ^p(α, ℝ)` is uniformly convex for `1 < p < ∞`, as an instance. -/
instance instUniformConvexSpace {α : Type*} [Countable α] {p : ℝ≥0∞} [Fact (1 < p)]
    [Fact (p ≠ ∞)] : UniformConvexSpace (lp (fun _ : α => ℝ) p) :=
  uniformConvexSpace

end UniformConvex

end lp

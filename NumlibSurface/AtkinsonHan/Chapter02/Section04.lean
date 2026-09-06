import Numlib.Analysis.Normed.Ring.CondNumber
import Numlib.Approximation.Quadrature
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Atkinson–Han §2.4: more results on linear operators

Statements from Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework* (3rd ed.), §2.4.

The book's `cond(L) = ‖L⁻¹‖ ‖L‖` is defined here as `AtkinsonHan.Ch02.cond`, with
`cond_eq_condNumber` identifying it, for `V = W`, with the backbone's
`NormedRing.condNumber` (`Numlib.Analysis.Normed.Ring.CondNumber`).

## Main results

* `theorem_2_4_1` — the extension theorem, for the completion of a normed space.
* `theorem_2_4_3` — the bounded inverse theorem (a corollary of the open mapping theorem).
* `stability_of_isomorphism`, `equation_2_4_1`, `one_le_cond` — the conditioning bounds (2.4.1).
* `theorem_2_4_4` — the principle of uniform boundedness.
* `theorem_2_4_5` — the Banach–Steinhaus theorem on a dense subspace.
* `tendsto_of_tendsto_on_dense_of_bounded` — its ε/3 half, in the generality it is proved in.
* `equation_2_4_4`, `quadrature_convergence` — §2.4.4, the convergence of numerical quadrature.

## Not formalized here

Example 2.4.2 (extension of the derivative to `H¹`) is out of scope: Sobolev spaces are not
planned.
-/

open Filter Topology Bornology NNReal

namespace AtkinsonHan.Ch02

variable {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-! ### Theorem 2.4.1: the extension theorem -/

/-- **Extension theorem** (Theorem 2.4.1). A bounded linear operator `L ∈ 𝓛(V, W)` from a normed
space `V` into a Banach space `W` extends uniquely to a bounded linear operator on the completion
`V̂` of `V`, and the extension has the same norm. -/
theorem theorem_2_4_1 [CompleteSpace W] (L : V →L[𝕜] W) :
    ∃ Lhat : UniformSpace.Completion V →L[𝕜] W, (∀ v : V, Lhat ↑v = L v) ∧ ‖Lhat‖ = ‖L‖ ∧
      ∀ L' : UniformSpace.Completion V →L[𝕜] W, (∀ v : V, L' ↑v = L v) → L' = Lhat := by
  have hdense : DenseRange (UniformSpace.Completion.toComplL : V →L[𝕜] UniformSpace.Completion V) :=
    UniformSpace.Completion.denseRange_coe
  have hind :
      IsUniformInducing (UniformSpace.Completion.toComplL : V →L[𝕜] UniformSpace.Completion V) :=
    UniformSpace.Completion.isUniformInducing_coe V
  set Lhat := L.extend (UniformSpace.Completion.toComplL : V →L[𝕜] UniformSpace.Completion V)
    with hLhat
  have heq : ∀ v : V, Lhat ↑v = L v := fun v => L.extend_eq hdense hind v
  refine ⟨Lhat, heq, le_antisymm ?_ ?_, ?_⟩
  · have hbound : ∀ x : V, ‖x‖ ≤ (1 : ℝ≥0) *
        ‖(UniformSpace.Completion.toComplL : V →L[𝕜] UniformSpace.Completion V) x‖ := by
      intro x
      simp
    simpa using L.opNorm_extend_le hdense hbound
  · refine L.opNorm_le_bound (norm_nonneg _) fun v => ?_
    rw [← heq v]
    simpa [UniformSpace.Completion.norm_coe] using Lhat.le_opNorm (↑v : UniformSpace.Completion V)
  · intro L' hL'
    rw [hLhat]
    exact (ContinuousLinearMap.extend_unique L hdense hind L' (by ext v; exact hL' v)).symm

/-! ### Theorem 2.4.3: the bounded inverse theorem -/

/-- **Bounded inverse theorem** (Theorem 2.4.3). A bounded linear bijection between Banach spaces
has a bounded inverse; equivalently, it is a continuous linear equivalence. -/
theorem theorem_2_4_3 [CompleteSpace V] [CompleteSpace W] (L : V →L[𝕜] W)
    (hL : Function.Bijective L) : ∃ e : V ≃L[𝕜] W, (e : V →L[𝕜] W) = L := by
  refine ⟨ContinuousLinearEquiv.ofBijective L ?_ ?_, ContinuousLinearEquiv.coe_ofBijective _ _ _⟩
  · exact LinearMap.ker_eq_bot.2 hL.1
  · exact LinearMap.range_eq_top.2 hL.2

/-- Stability of a well-posed linear problem (the remark after Theorem 2.4.3): the solution of
`L v = w` depends Lipschitz-continuously on the data, with constant `‖L⁻¹‖`. -/
theorem stability_of_isomorphism (L : V ≃L[𝕜] W) (v vhat : V) :
    ‖v - vhat‖ ≤ ‖(L.symm : W →L[𝕜] V)‖ * ‖L v - L vhat‖ := by
  have hv : (L.symm : W →L[𝕜] V) (L v - L vhat) = v - vhat := by simp
  calc ‖v - vhat‖ = ‖(L.symm : W →L[𝕜] V) (L v - L vhat)‖ := by rw [hv]
    _ ≤ ‖(L.symm : W →L[𝕜] V)‖ * ‖L v - L vhat‖ := (L.symm : W →L[𝕜] V).le_opNorm _

/-! ### The condition number (2.4.1) -/

/-- The **condition number** `cond(L) = ‖L⁻¹‖ ‖L‖` of a bijection `L : V → W` with bounded
inverse (Atkinson–Han §2.4.2). -/
noncomputable def cond (L : V ≃L[𝕜] W) : ℝ :=
  ‖(L.symm : W →L[𝕜] V)‖ * ‖(L : V →L[𝕜] W)‖

/-- For an operator of a space into itself the book's `cond` is the backbone's
`NormedRing.condNumber` of the underlying element of the ring `V →L[𝕜] V`. -/
theorem cond_eq_condNumber (L : V ≃L[𝕜] V) :
    cond L = NormedRing.condNumber (L : V →L[𝕜] V) := by
  rw [cond, ContinuousLinearEquiv.condNumber_eq, mul_comm]

/-- `cond(L) ≥ 1`, because `L⁻¹L = I` has norm `1` (Atkinson–Han §2.4.2). -/
theorem one_le_cond [Nontrivial V] (L : V ≃L[𝕜] W) : 1 ≤ cond L := by
  rw [cond, mul_comm]
  exact L.one_le_norm_mul_norm_symm

/-- **Relative error bound (2.4.1).** The relative error in the solution is bounded by `cond(L)`
times the relative error in the data: with `w = L v` and `ŵ = L v̂`,
`‖v - v̂‖ / ‖v‖ ≤ cond(L) ‖w - ŵ‖ / ‖w‖`. -/
theorem equation_2_4_1 (L : V ≃L[𝕜] W) {v vhat : V} (hv : v ≠ 0) :
    ‖v - vhat‖ / ‖v‖ ≤ cond L * (‖L v - L vhat‖ / ‖L v‖) := by
  have ha : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hb : 0 < ‖L v‖ := norm_pos_iff.2 fun h => hv (by simpa using congrArg L.symm h)
  have hd : ‖v - vhat‖ ≤ ‖(L.symm : W →L[𝕜] V)‖ * ‖L v - L vhat‖
    := stability_of_isomorphism L v vhat
  have hq : ‖L v‖ ≤ ‖(L : V →L[𝕜] W)‖ * ‖v‖ := (L : V →L[𝕜] W).le_opNorm v
  rw [cond, mul_div_assoc', div_le_div_iff₀ ha hb]
  have hp : 0 ≤ ‖(L.symm : W →L[𝕜] V)‖ := norm_nonneg _
  have hr : 0 ≤ ‖L v - L vhat‖ := norm_nonneg _
  nlinarith [mul_nonneg hp hr]

/-! ### Theorems 2.4.4 and 2.4.5: uniform boundedness -/

/-- **Principle of uniform boundedness** (Theorem 2.4.4). A family of bounded operators from a
Banach space that is pointwise bounded is uniformly bounded in norm. -/
theorem theorem_2_4_4 [CompleteSpace V] (Ln : ℕ → V →L[𝕜] W) (h : ∀ v, ∃ C, ∀ n, ‖Ln n v‖ ≤ C) :
    ∃ C, ∀ n, ‖Ln n‖ ≤ C :=
  banach_steinhaus h

/-- A convergent sequence in a normed space is bounded. Used repeatedly to feed
`banach_steinhaus` the pointwise bounds it needs. -/
theorem exists_norm_le_of_tendsto {X : Type*} [NormedAddCommGroup X] {f : ℕ → X} {a : X}
    (h : Tendsto f atTop (𝓝 a)) : ∃ C : ℝ, ∀ n, ‖f n‖ ≤ C := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _ h)
  exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩

/-- The `⇐` half of Theorem 2.4.5, in the generality in which it is proved: pointwise convergence
on a dense *subset*, together with a uniform bound on the operator norms, gives pointwise
convergence everywhere. Neither completeness of `V` nor linearity of the dense set is used; only
the boundedness of the limit operator `L`, which the book also assumes. This is the ε/3 argument.

This general form is a candidate for the backbone; see `plans/atkinsonhan-ch2-3.md`,
Deferred backbone item 1. -/
theorem tendsto_of_tendsto_on_dense_of_bounded {s : Set V} (hs : Dense s) {L : V →L[𝕜] W}
    {Ln : ℕ → V →L[𝕜] W} {C : ℝ} (hC : ∀ n, ‖Ln n‖ ≤ C)
    (h : ∀ v ∈ s, Tendsto (fun n => Ln n v) atTop (𝓝 (L v))) (v : V) :
    Tendsto (fun n => Ln n v) atTop (𝓝 (L v)) := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hM : 0 < C + ‖L‖ + 1 := by positivity
  obtain ⟨u, hu, hdist⟩ := hs.exists_dist_lt v (ε := ε / (3 * (C + ‖L‖ + 1))) (by positivity)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 (h u hu)) (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hvu : ‖v - u‖ < ε / (3 * (C + ‖L‖ + 1)) := by rwa [← dist_eq_norm]
  have h1 : ‖Ln n v - Ln n u‖ ≤ C * ‖v - u‖ := by
    rw [← map_sub]
    exact ((Ln n).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _))
  have h2 : ‖L u - L v‖ ≤ ‖L‖ * ‖v - u‖ := by
    rw [← map_sub, ← norm_neg, ← map_neg, neg_sub]
    exact L.le_opNorm _
  have h3 : ‖Ln n u - L u‖ < ε / 3 := by rw [← dist_eq_norm]; exact hN n hn
  have hsum : (C + ‖L‖) * ‖v - u‖ < ε / 3 := by
    have := mul_lt_mul_of_pos_left hvu hM
    have hle : (C + ‖L‖) * ‖v - u‖ ≤ (C + ‖L‖ + 1) * ‖v - u‖ := by
      have := norm_nonneg (v - u)
      nlinarith
    have hval : (C + ‖L‖ + 1) * (ε / (3 * (C + ‖L‖ + 1))) = ε / 3 := by
      field_simp
    linarith [hval ▸ this]
  have hsplit : ‖Ln n v - L v‖ ≤ ‖Ln n v - Ln n u‖ + ‖Ln n u - L u‖ + ‖L u - L v‖ := by
    have : Ln n v - L v = (Ln n v - Ln n u) + (Ln n u - L u) + (L u - L v) := by abel
    rw [this]
    exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
  rw [dist_eq_norm]
  nlinarith

/-- **Banach–Steinhaus theorem** (Theorem 2.4.5). For bounded operators `L, Lₙ` from a Banach
space `V` and a dense subspace `V₀ ⊆ V`, one has `Lₙ v → L v` for every `v ∈ V` if and only if
(a) `Lₙ v → L v` for every `v ∈ V₀` and (b) the norms `‖Lₙ‖` are uniformly bounded. -/
theorem theorem_2_4_5 [CompleteSpace V] (L : V →L[𝕜] W) (Ln : ℕ → V →L[𝕜] W) (V₀ : Submodule 𝕜 V)
    (hV₀ : Dense (V₀ : Set V)) :
    (∀ v, Tendsto (fun n => Ln n v) atTop (𝓝 (L v))) ↔
      (∀ v ∈ V₀, Tendsto (fun n => Ln n v) atTop (𝓝 (L v))) ∧ ∃ C, ∀ n, ‖Ln n‖ ≤ C := by
  refine ⟨fun h => ⟨fun v _ => h v, banach_steinhaus fun v => exists_norm_le_of_tendsto (h v)⟩, ?_⟩
  rintro ⟨hdense, C, hC⟩
  exact tendsto_of_tendsto_on_dense_of_bounded hV₀ hC hdense

/-! ### §2.4.4: convergence of numerical quadrature

The book studies the quadrature functionals `Lₙ v = ∑_{i=0}^{n} wᵢ⁽ⁿ⁾ v(xᵢ⁽ⁿ⁾)` on `C[0,1]`,
approximating `L v = ∫₀¹ w v`. Both results are the backbone's, specialized to `[0, 1]`; the
quadrature functional is `Quadrature.functional` of `Numlib/Approximation/Quadrature`. -/

/-- **(2.4.4)** (Exercise 2.4.2). The norm of the quadrature functional
`Lₙ v = ∑ᵢ wᵢ v(xᵢ)` on `C[0, 1]` is the absolute sum of its weights, provided the nodes are
distinct. -/
theorem equation_2_4_4 {n : ℕ} (w : Fin n → ℝ) {x : Fin n → Set.Icc (0 : ℝ) 1}
    (hx : Function.Injective x) : ‖Quadrature.functional w x‖ = ∑ i, |w i| :=
  Quadrature.norm_functional w hx

/-- **§2.4.4** and **Exercise 2.4.3**, the convergence of numerical quadrature. Let the rules
`Lₖ v = ∑ᵢ wᵢ⁽ᵏ⁾ v(xᵢ⁽ᵏ⁾)` at distinct nodes of `[0, 1]` be exact for `L` on the polynomials of
degree at most `d k`, with `d k → ∞`. Then `Lₖ v → L v` for every `v ∈ C[0, 1]` if and only if the
absolute sums of the weights are bounded; and if the weights are nonnegative, convergence always
holds. -/
theorem quadrature_convergence {m d : ℕ → ℕ} {w : ∀ k, Fin (m k) → ℝ}
    {x : ∀ k, Fin (m k) → Set.Icc (0 : ℝ) 1} (hx : ∀ k, Function.Injective (x k))
    {L : C(Set.Icc (0 : ℝ) 1, ℝ) →L[ℝ] ℝ} (hd : Tendsto d atTop atTop)
    (hexact : ∀ k, Quadrature.IsExactOn L (w k) (x k) (d k)) :
    ((∀ v, Tendsto (fun k => Quadrature.functional (w k) (x k) v) atTop (𝓝 (L v))) ↔
        ∃ C, ∀ k, ∑ i, |w k i| ≤ C) ∧
      ((∀ k i, 0 ≤ w k i) →
        ∀ v, Tendsto (fun k => Quadrature.functional (w k) (x k) v) atTop (𝓝 (L v))) :=
  ⟨Quadrature.tendsto_iff_bddAbove_sum_abs hx hd hexact,
    fun hw => Quadrature.tendsto_of_nonneg hx hd hexact hw⟩

end AtkinsonHan.Ch02

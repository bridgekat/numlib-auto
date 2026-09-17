import Mathlib.Analysis.LocallyConvex.WeakSpace
import Numlib.Analysis.Normed.Module.WeakClosed
import Numlib.Analysis.Normed.Module.WeakDual
import Numlib.Analysis.Normed.Module.WeakStarMetrizable
import NumlibSurface.Brezis.Chapter03.Section01

/-!
# Brezis §3.2: definition and elementary properties of the weak topology `σ(E, E*)`

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §3.2, over a real Banach space `E`. The book's
definition is `weakTopology E := weakestTopology (fun f : StrongDual ℝ E => ⇑f)` (§3.1) and
`weakTopology_eq` identifies it with Mathlib's `WeakSpace ℝ E`, on which every later node is
stated: the book's "`x ∈ E` with the weak topology" is `toWeakSpace ℝ E x : WeakSpace ℝ E`, a
weakly closed/open set is `IsClosed (toWeakSpace ℝ E '' s)` / `IsOpen (…)`, and `xₙ ⇀ x` is
`WeakTendsto x u`, with the scoped notation `⇀`. Propositions 3.3–3.5 are Mathlib and the
backbone `Numlib/Analysis/Normed/Module/WeakDual`; Proposition 3.6, Remark 2 and Examples 1–2
are `Numlib/Analysis/Normed/Module/WeakClosed`; Remark 3 is
`Numlib/Analysis/Normed/Module/WeakStarMetrizable`. Remark 4 is stated in §3.2 but its node
`remark_3_4` sits in `Section06`, where Theorem 3.29 is.

The book assumes `E` Banach throughout; `[CompleteSpace E]` is carried on every theorem for
fidelity although nothing in this section uses it.

## Main results

* `weakTopology`, `weakTopology_eq`, `weakTopology_le` — the definition, its identification with
  `WeakSpace ℝ E`, and "the weak topology is weaker than the usual topology".
* `proposition_3_3`, `proposition_3_4` — Hausdorff; the neighbourhood basis `V(f₁, …, f_k; ε)`.
* `WeakTendsto`, `proposition_3_5`, `proposition_3_5_ii`, `proposition_3_5_iii_bounded`,
  `proposition_3_5_iii_liminf`, `proposition_3_5_iv` — the notation `xₙ ⇀ x` and Proposition 3.5.
* `proposition_3_6`, `proposition_3_6_tendsto` — in finite dimension weak = strong.
* `remark_3_2_isOpen`, `remark_3_2_isClosed`, `example_3_1`, `example_3_2`, `remark_3_3` —
  weakly open/closed sets are strongly open/closed; the sphere and the open ball in infinite
  dimension; the weak topology is not metrizable in infinite dimension.
-/

open Filter Metric Set Topology TopologicalSpace

namespace Brezis.Chapter03

/-! ### Basic neighbourhoods in a weak topology -/

section WeakBilin

variable {𝕜 E F : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F]
  [Module 𝕜 F]

/-- The sets `{x | ∀ y ∈ s, ‖B x y - B x₀ y‖ < ε}`, `s` finite and `ε > 0`, form a neighbourhood
basis of `x₀` in `WeakBilin B` — the common core of Propositions 3.4 and 3.12. -/
theorem WeakBilin.hasBasis_nhds (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (x₀ : WeakBilin B) :
    (𝓝 x₀).HasBasis (fun p : Finset F × ℝ => 0 < p.2)
      (fun p => {x : WeakBilin B | ∀ y ∈ p.1, ‖B x y - B x₀ y‖ < p.2}) := by
  refine Filter.hasBasis_iff.2 fun t => ⟨fun ht => ?_, ?_⟩
  · have hU : (x₀ + ·) ⁻¹' t ∈ 𝓝 (0 : WeakBilin B) := by
      rw [← map_add_left_nhds_zero x₀] at ht
      exact ht
    obtain ⟨s, ε, hε, hsub⟩ := WeakBilin.exists_finset_forall_norm_lt_subset_of_mem_nhds_zero hU
    refine ⟨(s, ε), hε, fun x hx => ?_⟩
    have hmem : x - x₀ ∈ {x : WeakBilin B | ∀ y ∈ s, ‖B x y‖ < ε} := fun y hy => by
      have e : B (x - x₀) y = B x y - B x₀ y :=
        (congrArg (fun g : F →ₗ[𝕜] 𝕜 => g y) (map_sub B (x : E) x₀)).trans
          (LinearMap.sub_apply _ _ _)
      rw [e]
      exact hx y hy
    have := hsub hmem
    simpa using this
  · rintro ⟨⟨s, ε⟩, hε, hsub⟩
    dsimp only at hε hsub
    refine Filter.mem_of_superset ?_ hsub
    have hopen : IsOpen {x : WeakBilin B | ∀ y ∈ s, ‖B x y - B x₀ y‖ < ε} := by
      have : {x : WeakBilin B | ∀ y ∈ s, ‖B x y - B x₀ y‖ < ε} =
          ⋂ y ∈ s, {x : WeakBilin B | ‖B x y - B x₀ y‖ < ε} := by
        ext x
        simp only [mem_ofPred_eq, mem_iInter]
      rw [this]
      exact isOpen_biInter_finset fun y _ =>
        isOpen_lt (((WeakBilin.eval_continuous B y).sub continuous_const).norm) continuous_const
    refine hopen.mem_nhds fun y _ => ?_
    rw [sub_self, norm_zero]
    exact hε

end WeakBilin

/-! ### The weak topology -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The Definition of §3.2.** The weak topology `σ(E, E*)` on `E` is the coarsest topology
making every `φ_f = ⟨f, ·⟩`, `f ∈ E*`, continuous (§3.1 with `X = E`, `Y_i = ℝ`, `I = E*`). -/
@[instance_reducible]
def weakTopology (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : TopologicalSpace E :=
  weakestTopology (fun f : StrongDual ℝ E => (f : E → ℝ))

/-- The book's weak topology is Mathlib's: `weakTopology E` is the topology of `WeakSpace ℝ E`
transported back to `E` along the identity `toWeakSpace ℝ E`. -/
theorem weakTopology_eq :
    weakTopology E = TopologicalSpace.induced (toWeakSpace ℝ E) inferInstance := by
  change _ = TopologicalSpace.induced (toWeakSpace ℝ E) (TopologicalSpace.induced
    (fun (x : WeakSpace ℝ E) (f : StrongDual ℝ E) => f x) Pi.topologicalSpace)
  rw [induced_compose, induced_to_pi]
  rfl

/-- "The weak topology is weaker than the usual topology": every weakly open set is open, i.e.
the norm topology is finer, `(norm topology) ≤ weakTopology E`. -/
theorem weakTopology_le : (inferInstance : TopologicalSpace E) ≤ weakTopology E := by
  rw [weakTopology_eq]
  exact continuous_iff_le_induced.1 (toWeakSpaceCLM ℝ E).continuous

/-- **Proposition 3.3.** The weak topology `σ(E, E*)` is Hausdorff. -/
theorem proposition_3_3 [CompleteSpace E] : T2Space (WeakSpace ℝ E) :=
  inferInstance

/-- **Proposition 3.4.** Let `x₀ ∈ E`; for `ε > 0` and a finite set `{f₁, …, f_k} ⊆ E*`, the
set `V(f₁, …, f_k; ε) = {x | |⟨fᵢ, x - x₀⟩| < ε ∀ i}` is a neighbourhood of `x₀` for
`σ(E, E*)`, and these sets form a basis of neighbourhoods of `x₀`. -/
theorem proposition_3_4 [CompleteSpace E] (x₀ : E) :
    (∀ (s : Finset (StrongDual ℝ E)) (ε : ℝ), 0 < ε →
      toWeakSpace ℝ E '' {x | ∀ f ∈ s, |f (x - x₀)| < ε} ∈ 𝓝 (toWeakSpace ℝ E x₀)) ∧
    (𝓝 (toWeakSpace ℝ E x₀)).HasBasis (fun p : Finset (StrongDual ℝ E) × ℝ => 0 < p.2)
      (fun p => toWeakSpace ℝ E '' {x | ∀ f ∈ p.1, |f (x - x₀)| < p.2}) := by
  have hb := WeakBilin.hasBasis_nhds (topDualPairing ℝ E).flip (toWeakSpace ℝ E x₀)
  have hset : ∀ (s : Finset (StrongDual ℝ E)) (ε : ℝ),
      toWeakSpace ℝ E '' {x | ∀ f ∈ s, |f (x - x₀)| < ε} =
        {x : WeakSpace ℝ E | ∀ f ∈ s, ‖(topDualPairing ℝ E).flip x f -
          (topDualPairing ℝ E).flip (toWeakSpace ℝ E x₀) f‖ < ε} := by
    intro s ε
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      intro f hf
      have := hx f hf
      rwa [map_sub] at this
    · intro hy
      refine ⟨(toWeakSpace ℝ E).symm y, fun f hf => ?_, (toWeakSpace ℝ E).apply_symm_apply y⟩
      rw [map_sub]
      exact hy f hf
  refine ⟨fun s ε hε => ?_, hb.congr (fun _ => Iff.rfl) fun p _ => (hset p.1 p.2).symm⟩
  rw [hset]
  exact hb.mem_of_mem (i := (s, ε)) hε

/-- **The notation `xₙ ⇀ x`** of §3.2: the sequence `x` converges to `u` in the weak topology
`σ(E, E*)`. Strong convergence `xₙ → x` is Mathlib's `Tendsto x atTop (𝓝 u)`. -/
def WeakTendsto (x : ℕ → E) (u : E) : Prop :=
  Tendsto (fun n => toWeakSpace ℝ E (x n)) atTop (𝓝 (toWeakSpace ℝ E u))

@[inherit_doc] scoped notation:50 x:51 " ⇀ " u:51 => WeakTendsto x u

/-- **Proposition 3.5 (i).** `xₙ ⇀ x` weakly in `σ(E, E*)` iff `⟨f, xₙ⟩ → ⟨f, x⟩` for every
`f ∈ E*`. -/
theorem proposition_3_5 [CompleteSpace E] (x : ℕ → E) (u : E) :
    x ⇀ u ↔ ∀ f : StrongDual ℝ E, Tendsto (fun n => f (x n)) atTop (𝓝 (f u)) :=
  tendsto_toWeakSpace_iff

/-- **Proposition 3.5 (ii).** If `xₙ → x` strongly then `xₙ ⇀ x` weakly. -/
theorem proposition_3_5_ii [CompleteSpace E] {x : ℕ → E} {u : E} (h : Tendsto x atTop (𝓝 u)) :
    x ⇀ u :=
  ((toWeakSpaceCLM ℝ E).continuous.tendsto u).comp h

/-- **Proposition 3.5 (iii), first half.** If `xₙ ⇀ x` weakly then `(‖xₙ‖)` is bounded. -/
theorem proposition_3_5_iii_bounded [CompleteSpace E] {x : ℕ → E} {u : E} (h : x ⇀ u) :
    ∃ C : ℝ, ∀ n, ‖x n‖ ≤ C :=
  exists_norm_le_of_tendsto_toWeakSpace h

/-- **Proposition 3.5 (iii), second half.** If `xₙ ⇀ x` weakly then `‖x‖ ≤ liminf ‖xₙ‖`. -/
theorem proposition_3_5_iii_liminf [CompleteSpace E] {x : ℕ → E} {u : E} (h : x ⇀ u) :
    ‖u‖ ≤ liminf (fun n => ‖x n‖) atTop :=
  norm_le_liminf_norm_of_weak_tendsto h

/-- **Proposition 3.5 (iv).** If `xₙ ⇀ x` weakly and `fₙ → f` strongly in `E*` then
`⟨fₙ, xₙ⟩ → ⟨f, x⟩`. -/
theorem proposition_3_5_iv [CompleteSpace E] {x : ℕ → E} {u : E} {f : ℕ → StrongDual ℝ E}
    {g : StrongDual ℝ E} (hx : x ⇀ u) (hf : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun n => f n (x n)) atTop (𝓝 (g u)) :=
  tendsto_apply_of_tendsto_toWeakSpace_of_tendsto hx hf

/-- **Proposition 3.6.** When `E` is finite-dimensional the weak topology `σ(E, E*)` and the
usual topology are the same. -/
theorem proposition_3_6 [CompleteSpace E] [FiniteDimensional ℝ E] :
    weakTopology E = (inferInstance : TopologicalSpace E) := by
  rw [weakTopology_eq]
  exact ((toWeakSpaceContinuousLinearEquiv ℝ E).toHomeomorph.isInducing.eq_induced).symm

/-- **Proposition 3.6, "in particular".** In finite dimension a sequence converges weakly iff it
converges strongly. -/
theorem proposition_3_6_tendsto [CompleteSpace E] [FiniteDimensional ℝ E] (x : ℕ → E) (u : E) :
    x ⇀ u ↔ Tendsto x atTop (𝓝 u) :=
  tendsto_toWeakSpace_iff_of_finiteDimensional

/-- **Remark 2, open sets.** Open sets in the weak topology are open in the strong topology. -/
theorem remark_3_2_isOpen [CompleteSpace E] {s : Set E} (h : IsOpen (toWeakSpace ℝ E '' s)) :
    IsOpen s :=
  WeakSpace.isOpen_of_isOpen s h

/-- **Remark 2, closed sets.** Closed sets in the weak topology are closed in the strong
topology. In infinite dimension the converse fails: Examples 1 and 2. -/
theorem remark_3_2_isClosed [CompleteSpace E] {s : Set E}
    (h : IsClosed (toWeakSpace ℝ E '' s)) : IsClosed s :=
  WeakSpace.isClosed_of_isClosed h

/-- **Example 1 of §3.2.** In an infinite-dimensional `E` the unit sphere
`S = {x | ‖x‖ = 1}` is never weakly closed; more precisely its weak closure is the closed unit
ball `B_E` (1), which is weakly closed. -/
theorem example_3_1 [CompleteSpace E] (h : ¬ FiniteDimensional ℝ E) :
    closure (toWeakSpace ℝ E '' sphere (0 : E) 1) = toWeakSpace ℝ E '' closedBall 0 1 ∧
      IsClosed (toWeakSpace ℝ E '' closedBall (0 : E) 1) ∧
      ¬ IsClosed (toWeakSpace ℝ E '' sphere (0 : E) 1) := by
  refine ⟨closure_image_toWeakSpace_sphere h, isClosed_image_toWeakSpace_closedBall 0 1,
    fun hc => ?_⟩
  have h0 : toWeakSpace ℝ E 0 ∈ toWeakSpace ℝ E '' sphere (0 : E) 1 := by
    rw [← hc.closure_eq, closure_image_toWeakSpace_sphere h]
    exact ⟨0, by simp, rfl⟩
  obtain ⟨z, hz, hz0⟩ := h0
  rw [(toWeakSpace ℝ E).injective.eq_iff] at hz0
  rw [hz0, mem_sphere_zero_iff_norm, norm_zero] at hz
  exact zero_ne_one hz

/-- **Example 2 of §3.2.** In an infinite-dimensional `E` the open unit ball
`U = {x | ‖x‖ < 1}` is never weakly open. -/
theorem example_3_2 [CompleteSpace E] (h : ¬ FiniteDimensional ℝ E) :
    ¬ IsOpen (toWeakSpace ℝ E '' ball (0 : E) 1) :=
  not_isOpen_image_toWeakSpace_ball h

/-- **Remark 3.** In an infinite-dimensional space the weak topology is never metrizable: no
metric on `E` induces `σ(E, E*)` (Exercise 3.8). The "however" — `B_E` is weakly metrizable
when `E*` is separable — is Theorem 3.29. -/
theorem remark_3_3 [CompleteSpace E] (h : ¬ FiniteDimensional ℝ E) :
    ¬ MetrizableSpace (WeakSpace ℝ E) :=
  not_metrizableSpace_weakSpace h

end Brezis.Chapter03

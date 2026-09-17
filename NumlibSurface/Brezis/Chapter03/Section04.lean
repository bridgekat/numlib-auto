import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.LinearAlgebra.Dual.Lemmas
import Numlib.Analysis.Normed.Module.Reflexive
import NumlibSurface.Brezis.Chapter02.Section02
import NumlibSurface.Brezis.Chapter03.Section03

/-!
# Brezis §3.4: the weak-∗ topology `σ(E*, E)`

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §3.4, on the dual `E* = StrongDual ℝ E` of a real
Banach space `E`. The book's definition is
`weakStarTopology E := weakestTopology (fun x : E => fun f : StrongDual ℝ E => f x)` and
`weakStarTopology_eq` identifies it with Mathlib's `WeakDual ℝ E`, on which every later node is
stated: `StrongDual.toWeakDual f : WeakDual ℝ E` is "`f` with the weak-∗ topology", and
`fₙ ⇀* f` is `WeakStarTendsto f g` with the scoped notation `⇀*`. Propositions 3.11–3.13 are
Mathlib and the backbone `Numlib/Analysis/Normed/Module/WeakDual`; Proposition 3.14 is Mathlib's
weak representation theorem `LinearMap.dualEmbedding_surjective` and Lemma 3.2 its algebraic
core `mem_span_of_iInf_ker_le_ker`; Corollary 3.15 and Remark 11 are proved here from them;
Theorem 3.16 is `WeakDual.isCompact_closedBall`; Remark 10 is the backbone's
`toWeakDualContinuousLinearEquiv` (`WeakClosed`). `[CompleteSpace E]` is carried on every
theorem; it is used in Proposition 3.13 (iii)–(iv) (uniform boundedness in `E`).

## Main results

* `weakStarTopology`, `weakStarTopology_eq` — the definition, its identification with
  `WeakDual ℝ E`, and "weak-∗ is coarser than weak, which is coarser than strong" on `E*`.
* `proposition_3_11`, `proposition_3_12` — Hausdorff; the neighbourhood basis `V(x₁, …, x_k; ε)`.
* `WeakStarTendsto`, `proposition_3_13`, `proposition_3_13_ii_weak`,
  `proposition_3_13_ii_weakStar`, `proposition_3_13_iii_bounded`, `proposition_3_13_iii_liminf`,
  `proposition_3_13_iv` — the notation `fₙ ⇀* f` and Proposition 3.13.
* `remark_3_9` — the `ℓ²` example: `fₙ ⇀* f` and `xₙ ⇀ x` do not give `⟨fₙ, xₙ⟩ → ⟨f, x⟩`.
* `remark_3_10` — in finite dimension the three topologies on `E*` coincide.
* `proposition_3_14`, `lemma_3_2`, `corollary_3_15`, `remark_3_11` — weak-∗ continuous
  functionals are evaluations; the algebraic lemma; weak-∗ closed hyperplanes; a weakly closed
  hyperplane that is not weak-∗ closed when `J` is not onto.
* `theorem_3_16` — Banach–Alaoglu–Bourbaki: `B_{E*}` is weak-∗ compact.

Remarks 8 and 12 are discussion.
-/

open Filter Metric Set Topology TopologicalSpace NormedSpace

namespace Brezis.Chapter03

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The weak-∗ topology -/

/-- **The Definition of §3.4.** The weak-∗ topology `σ(E*, E)` on `E*` is the coarsest topology
making every `φ_x = ⟨·, x⟩`, `x ∈ E`, continuous (§3.1 with `X = E*`, `Y_i = ℝ`, `I = E`). -/
@[instance_reducible]
def weakStarTopology (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    TopologicalSpace (StrongDual ℝ E) :=
  weakestTopology (fun x : E => fun f : StrongDual ℝ E => f x)

/-- The book's weak-∗ topology is Mathlib's: `weakStarTopology E` is the topology of
`WeakDual ℝ E` transported back to `E*` along the identity `StrongDual.toWeakDual`. Moreover
`σ(E*, E)` is coarser than `σ(E*, E**)`, which is coarser than the strong topology (in
Mathlib's order on topologies, `≤` is "finer"). -/
theorem weakStarTopology_eq :
    weakStarTopology E =
        TopologicalSpace.induced (StrongDual.toWeakDual : StrongDual ℝ E → WeakDual ℝ E)
          inferInstance ∧
      weakTopology (StrongDual ℝ E) ≤ weakStarTopology E ∧
      (inferInstance : TopologicalSpace (StrongDual ℝ E)) ≤ weakTopology (StrongDual ℝ E) := by
  have heq : weakStarTopology E =
      TopologicalSpace.induced (StrongDual.toWeakDual : StrongDual ℝ E → WeakDual ℝ E)
        inferInstance := by
    change _ = TopologicalSpace.induced (StrongDual.toWeakDual : StrongDual ℝ E → WeakDual ℝ E)
      (TopologicalSpace.induced (fun (f : WeakDual ℝ E) (x : E) => f x) Pi.topologicalSpace)
    rw [induced_compose, induced_to_pi]
    rfl
  refine ⟨heq, ?_, weakTopology_le⟩
  rw [heq, weakTopology_eq]
  have h := continuous_iff_le_induced.1 (WeakDual.continuous_weakSpace_toWeakDual (𝕜 := ℝ) (V := E))
  calc TopologicalSpace.induced (toWeakSpace ℝ (StrongDual ℝ E)) inferInstance
      ≤ TopologicalSpace.induced (toWeakSpace ℝ (StrongDual ℝ E))
        (TopologicalSpace.induced (fun f : WeakSpace ℝ (StrongDual ℝ E) =>
          StrongDual.toWeakDual ((toWeakSpace ℝ (StrongDual ℝ E)).symm f)) inferInstance) :=
        induced_mono h
    _ = TopologicalSpace.induced (StrongDual.toWeakDual : StrongDual ℝ E → WeakDual ℝ E)
        inferInstance := by
        rw [induced_compose]
        rfl

/-- **Proposition 3.11.** The weak-∗ topology is Hausdorff. -/
theorem proposition_3_11 [CompleteSpace E] : T2Space (WeakDual ℝ E) :=
  inferInstance

/-- **Proposition 3.12.** Let `f₀ ∈ E*`; for a finite set `{x₁, …, x_k} ⊆ E` and `ε > 0`, the
set `V(x₁, …, x_k; ε) = {f | |⟨f - f₀, xᵢ⟩| < ε ∀ i}` is a neighbourhood of `f₀` for
`σ(E*, E)`, and these sets form a basis of neighbourhoods of `f₀`. -/
theorem proposition_3_12 [CompleteSpace E] (f₀ : StrongDual ℝ E) :
    (∀ (s : Finset E) (ε : ℝ), 0 < ε →
      StrongDual.toWeakDual '' {f | ∀ x ∈ s, |(f - f₀) x| < ε} ∈
        𝓝 (StrongDual.toWeakDual f₀)) ∧
    (𝓝 (StrongDual.toWeakDual f₀)).HasBasis (fun p : Finset E × ℝ => 0 < p.2)
      (fun p => StrongDual.toWeakDual '' {f | ∀ x ∈ p.1, |(f - f₀) x| < p.2}) := by
  have hb := WeakBilin.hasBasis_nhds (topDualPairing ℝ E) (StrongDual.toWeakDual f₀)
  have hset : ∀ (s : Finset E) (ε : ℝ),
      StrongDual.toWeakDual '' {f | ∀ x ∈ s, |(f - f₀) x| < ε} =
        {f : WeakDual ℝ E | ∀ x ∈ s, ‖topDualPairing ℝ E f x -
          topDualPairing ℝ E (StrongDual.toWeakDual f₀) x‖ < ε} := by
    intro s ε
    ext g
    constructor
    · rintro ⟨f, hf, rfl⟩
      intro x hx
      have := hf x hx
      rwa [sub_apply] at this
    · intro hg
      refine ⟨StrongDual.toWeakDual.symm g, fun x hx => ?_,
        StrongDual.toWeakDual.apply_symm_apply g⟩
      rw [sub_apply]
      exact hg x hx
  refine ⟨fun s ε hε => ?_, hb.congr (fun _ => Iff.rfl) fun p _ => (hset p.1 p.2).symm⟩
  rw [hset]
  exact hb.mem_of_mem (i := (s, ε)) hε

/-- **The notation `fₙ ⇀* f`** of §3.4: the sequence `f` of `E*` converges to `g` in the weak-∗
topology `σ(E*, E)`. The book's "`fₙ ⇀ f` in `σ(E*, E**)`" is `WeakTendsto f g` on the Banach
space `E*`. -/
def WeakStarTendsto (f : ℕ → StrongDual ℝ E) (g : StrongDual ℝ E) : Prop :=
  Tendsto (fun n => StrongDual.toWeakDual (f n)) atTop (𝓝 (StrongDual.toWeakDual g))

@[inherit_doc] scoped notation:50 f:51 " ⇀* " g:51 => WeakStarTendsto f g

/-- **Proposition 3.13 (i).** `fₙ ⇀* f` in `σ(E*, E)` iff `⟨fₙ, x⟩ → ⟨f, x⟩` for every
`x ∈ E`. -/
theorem proposition_3_13 [CompleteSpace E] (f : ℕ → StrongDual ℝ E) (g : StrongDual ℝ E) :
    f ⇀* g ↔ ∀ x : E, Tendsto (fun n => f n x) atTop (𝓝 (g x)) :=
  tendsto_iff_forall_eval_tendsto_topDualPairing

/-- **Proposition 3.13 (ii), first sentence.** If `fₙ → f` strongly then `fₙ ⇀ f` in
`σ(E*, E**)`. -/
theorem proposition_3_13_ii_weak [CompleteSpace E] {f : ℕ → StrongDual ℝ E}
    {g : StrongDual ℝ E} (h : Tendsto f atTop (𝓝 g)) : f ⇀ g :=
  proposition_3_5_ii h

/-- **Proposition 3.13 (ii), second sentence.** If `fₙ ⇀ f` in `σ(E*, E**)` then `fₙ ⇀* f` in
`σ(E*, E)`. -/
theorem proposition_3_13_ii_weakStar [CompleteSpace E] {f : ℕ → StrongDual ℝ E}
    {g : StrongDual ℝ E} (h : f ⇀ g) : f ⇀* g :=
  tendsto_toWeakDual_of_tendsto_toWeakSpace h

/-- **Proposition 3.13 (iii), first half.** If `fₙ ⇀* f` then `(‖fₙ‖)` is bounded. -/
theorem proposition_3_13_iii_bounded [CompleteSpace E] {f : ℕ → StrongDual ℝ E}
    {g : StrongDual ℝ E} (h : f ⇀* g) : ∃ C : ℝ, ∀ n, ‖f n‖ ≤ C :=
  exists_norm_le_of_tendsto_toWeakDual h

/-- **Proposition 3.13 (iii), second half.** If `fₙ ⇀* f` then `‖f‖ ≤ liminf ‖fₙ‖`. -/
theorem proposition_3_13_iii_liminf [CompleteSpace E] {f : ℕ → StrongDual ℝ E}
    {g : StrongDual ℝ E} (h : f ⇀* g) : ‖g‖ ≤ liminf (fun n => ‖f n‖) atTop :=
  norm_le_liminf_norm_of_weakStar_tendsto h

/-- **Proposition 3.13 (iv).** If `fₙ ⇀* f` in `σ(E*, E)` and `xₙ → x` strongly in `E`, then
`⟨fₙ, xₙ⟩ → ⟨f, x⟩`. -/
theorem proposition_3_13_iv [CompleteSpace E] {f : ℕ → StrongDual ℝ E} {g : StrongDual ℝ E}
    {x : ℕ → E} {u : E} (hf : f ⇀* g) (hx : Tendsto x atTop (𝓝 u)) :
    Tendsto (fun n => f n (x n)) atTop (𝓝 (g u)) :=
  tendsto_apply_of_tendsto_toWeakDual_of_tendsto hf hx

/-! ### Remark 9: the example in `ℓ²` -/

/-- The standard unit vectors of `ℓ²` converge weakly to `0`. -/
private theorem weakTendsto_single_zero :
    (fun n => lp.single 2 n (1 : ℝ) : ℕ → lp (fun _ : ℕ => ℝ) 2) ⇀ 0 := by
  refine tendsto_toWeakSpace_iff.2 fun g => ?_
  obtain ⟨y, rfl⟩ := (InnerProductSpace.toDual ℝ (lp (fun _ : ℕ => ℝ) 2)).surjective g
  simp only [InnerProductSpace.toDual_apply_apply, inner_zero_right]
  refine (Brezis.Chapter02.tendsto_coord_zero y).congr fun n => ?_
  rw [lp.inner_single_right, RCLike.inner_apply, conj_trivial, one_mul]

/-- **Remark 9.** From `fₙ ⇀* f` (even `fₙ ⇀ f` in `σ(E*, E**)`) and `xₙ ⇀ x` one cannot
conclude `⟨fₙ, xₙ⟩ → ⟨f, x⟩`: in the Hilbert space `ℓ²`, the unit vectors `eₙ` and the
functionals `fₙ = ⟨eₙ, ·⟩` satisfy `eₙ ⇀ 0`, `fₙ ⇀ 0` weakly, `fₙ ⇀* 0`, and `⟨fₙ, eₙ⟩ = 1`
for every `n`. -/
theorem remark_3_9 :
    let e : ℕ → lp (fun _ : ℕ => ℝ) 2 := fun n => lp.single 2 n (1 : ℝ)
    let f : ℕ → StrongDual ℝ (lp (fun _ : ℕ => ℝ) 2) :=
      fun n => InnerProductSpace.toDual ℝ _ (e n)
    e ⇀ 0 ∧ f ⇀ 0 ∧ f ⇀* 0 ∧ (∀ n, f n (e n) = 1) ∧
      ¬ Tendsto (fun n => f n (e n)) atTop
        (𝓝 ((0 : StrongDual ℝ _) (0 : lp (fun _ : ℕ => ℝ) 2))) := by
  intro e f
  have he : e ⇀ 0 := weakTendsto_single_zero
  have hfe : ∀ n, f n (e n) = 1 := fun n => by
    simp only [f, e, InnerProductSpace.toDual_apply_apply, lp.inner_single_right,
      lp.single_apply_self, RCLike.inner_apply, conj_trivial, mul_one]
  have hf : f ⇀ 0 := by
    refine tendsto_toWeakSpace_iff.2 fun ξ => ?_
    -- `ℓ²` is reflexive, so `ξ = J y` for some `y ∈ ℓ²`
    obtain ⟨y, rfl⟩ := NormedSpace.surjective_inclusionInDoubleDual (𝕜 := ℝ)
      (V := lp (fun _ : ℕ => ℝ) 2) ξ
    simp only [f, e, dual_def, InnerProductSpace.toDual_apply_apply, map_zero]
    refine (Brezis.Chapter02.tendsto_coord_zero y).congr fun n => ?_
    rw [lp.inner_single_left, RCLike.inner_apply, conj_trivial, mul_one]
  refine ⟨he, hf, proposition_3_13_ii_weakStar hf, hfe, fun h => ?_⟩
  simp only [hfe, zero_apply] at h
  exact zero_ne_one (tendsto_nhds_unique h tendsto_const_nhds)

/-! ### Finite dimension, the weak representation theorem, and Banach–Alaoglu -/

/-- **Remark 10.** When `E` is finite-dimensional the three topologies (strong, weak, weak-∗)
on `E*` coincide: `σ(E*, E) = σ(E*, E**)` since `J` is onto, and `σ(E*, E**)` is the strong
topology by Proposition 3.6. -/
theorem remark_3_10 [CompleteSpace E] [FiniteDimensional ℝ E] :
    weakStarTopology E = weakTopology (StrongDual ℝ E) ∧
      weakTopology (StrongDual ℝ E) = (inferInstance : TopologicalSpace (StrongDual ℝ E)) := by
  refine ⟨?_, proposition_3_6⟩
  rw [weakStarTopology_eq.1, weakTopology_eq]
  have h₁ := (toWeakDualContinuousLinearEquiv ℝ E).toHomeomorph.isInducing.eq_induced
  have h₂ :=
    (toWeakSpaceContinuousLinearEquiv ℝ (StrongDual ℝ E)).toHomeomorph.isInducing.eq_induced
  exact h₁.symm.trans h₂

/-- **Proposition 3.14.** A linear functional `φ : E* → ℝ` continuous for the weak-∗ topology
is evaluation at some `x₀ ∈ E`: `φ f = ⟨f, x₀⟩` for all `f`. Stated both for `φ` a continuous
functional on `WeakDual ℝ E` and for a linear `φ` continuous for `weakStarTopology E`. -/
theorem proposition_3_14 [CompleteSpace E] :
    (∀ φ : StrongDual ℝ (WeakDual ℝ E), ∃ x₀ : E, ∀ f : StrongDual ℝ E,
      φ (StrongDual.toWeakDual f) = f x₀) ∧
    ∀ φ : StrongDual ℝ E →ₗ[ℝ] ℝ, Continuous[weakStarTopology E, _] φ →
      ∃ x₀ : E, ∀ f : StrongDual ℝ E, φ f = f x₀ := by
  have hrep : ∀ φ : StrongDual ℝ (WeakDual ℝ E), ∃ x₀ : E, ∀ f : StrongDual ℝ E,
      φ (StrongDual.toWeakDual f) = f x₀ := fun φ => by
    obtain ⟨x₀, hx₀⟩ := LinearMap.dualEmbedding_surjective (topDualPairing ℝ E) φ
    exact ⟨x₀, fun f => by rw [← hx₀]; rfl⟩
  refine ⟨hrep, fun φ hφ => ?_⟩
  rw [weakStarTopology_eq.1] at hφ
  have hsymm : Continuous[inferInstance,
      TopologicalSpace.induced (StrongDual.toWeakDual : StrongDual ℝ E → WeakDual ℝ E)
        inferInstance] (StrongDual.toWeakDual.symm : WeakDual ℝ E → StrongDual ℝ E) :=
    continuous_induced_rng.2 (continuous_id.congr fun _ => rfl)
  have hc : Continuous (fun g : WeakDual ℝ E => φ (StrongDual.toWeakDual.symm g)) :=
    @Continuous.comp (WeakDual ℝ E) (StrongDual ℝ E) ℝ _
      (TopologicalSpace.induced (StrongDual.toWeakDual : StrongDual ℝ E → WeakDual ℝ E)
        inferInstance) _ _ _ hφ hsymm
  obtain ⟨x₀, hx₀⟩ := hrep ⟨φ ∘ₗ StrongDual.toWeakDual.symm.toLinearMap, hc⟩
  exact ⟨x₀, fun f => by simpa using hx₀ f⟩

/-- **Lemma 3.2.** Let `X` be a vector space and `φ, φ₁, …, φ_k` linear functionals on `X` with
`[φᵢ v = 0 ∀ i] ⇒ [φ v = 0]`. Then `φ = ∑ λᵢ φᵢ` for some constants `λᵢ`. -/
theorem lemma_3_2 {X : Type*} [AddCommGroup X] [Module ℝ X] {k : ℕ} (φ : X →ₗ[ℝ] ℝ)
    (φ' : Fin k → (X →ₗ[ℝ] ℝ)) (h : ∀ v, (∀ i, φ' i v = 0) → φ v = 0) :
    ∃ lam : Fin k → ℝ, φ = ∑ i, lam i • φ' i := by
  have hmem : φ ∈ Submodule.span ℝ (Set.range φ') :=
    mem_span_of_iInf_ker_le_ker fun v hv => by
      rw [Submodule.mem_iInf] at hv
      exact h v fun i => hv i
  obtain ⟨lam, hlam⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hmem
  exact ⟨lam, hlam.symm⟩

/-- A translate of a hyperplane `{f | φ f = α}` of `WeakDual ℝ E` is the kernel of `φ`, so a
weak-∗ closed hyperplane has weak-∗ closed kernel and `φ` is weak-∗ continuous. -/
private theorem continuous_of_isClosed_level {φ : WeakDual ℝ E →ₗ[ℝ] ℝ} (hφ : φ ≠ 0)
    {α : ℝ} (hH : IsClosed {g : WeakDual ℝ E | φ g = α}) : Continuous φ := by
  obtain ⟨g, hg⟩ : ∃ g, φ g ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hφ (LinearMap.ext hcon)
  set g₁ : WeakDual ℝ E := (α / φ g) • g with hg₁
  have hφg₁ : φ g₁ = α := by rw [hg₁, map_smul, smul_eq_mul, div_mul_cancel₀ _ hg]
  have hker : (LinearMap.ker φ : Set (WeakDual ℝ E)) = (fun y => y + g₁) ⁻¹' {g | φ g = α} := by
    ext y
    simp [hφg₁]
  rw [LinearMap.continuous_iff_isClosed_ker, hker]
  exact hH.preimage (continuous_id.add continuous_const)

/-- **Corollary 3.15.** A hyperplane `H = {f ∈ E* | φ f = α}` (with `φ` linear, `φ ≢ 0`) that is
closed in `σ(E*, E)` has the form `H = {f | ⟨f, x₀⟩ = α}` for some `x₀ ∈ E`, `x₀ ≠ 0`. -/
theorem corollary_3_15 [CompleteSpace E] {φ : StrongDual ℝ E →ₗ[ℝ] ℝ} (hφ : φ ≠ 0) (α : ℝ)
    (hH : IsClosed (StrongDual.toWeakDual '' {f | φ f = α})) :
    ∃ (x₀ : E) (β : ℝ), x₀ ≠ 0 ∧ {f | φ f = α} = {f | f x₀ = β} := by
  set ψ : WeakDual ℝ E →ₗ[ℝ] ℝ := φ ∘ₗ StrongDual.toWeakDual.symm.toLinearMap with hψ
  have hψφ : ∀ f : StrongDual ℝ E, ψ (StrongDual.toWeakDual f) = φ f := fun f => by simp [hψ]
  have hψ0 : ψ ≠ 0 := by
    intro h
    refine hφ (LinearMap.ext fun f => ?_)
    have := hψφ f
    rw [h] at this
    simpa using this.symm
  have hset : StrongDual.toWeakDual '' {f | φ f = α} = {g : WeakDual ℝ E | ψ g = α} := by
    ext g
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact (hψφ f).trans hf
    · intro hg
      exact ⟨StrongDual.toWeakDual.symm g, by simpa [hψ] using hg,
        StrongDual.toWeakDual.apply_symm_apply g⟩
  rw [hset] at hH
  obtain ⟨x₀, hx₀⟩ := (proposition_3_14 (E := E)).1 ⟨ψ, continuous_of_isClosed_level hψ0 hH⟩
  have hφx : ∀ f : StrongDual ℝ E, φ f = f x₀ := fun f => (hψφ f).symm.trans (hx₀ f)
  refine ⟨x₀, α, fun h0 => hφ (LinearMap.ext fun f => ?_), Set.ext fun f => by rw [mem_ofPred_eq,
    mem_ofPred_eq, hφx]⟩
  rw [hφx, h0, map_zero, LinearMap.zero_apply]

/-- **Remark 11.** If `J : E → E**` is not surjective, `σ(E*, E)` is strictly coarser than
`σ(E*, E**)`: for `ξ ∈ E**` with `ξ ∉ J(E)`, the hyperplane `H = {f | ⟨ξ, f⟩ = 0}` is closed
in `σ(E*, E**)` but not in `σ(E*, E)`. So convex sets that are strongly closed need not be
weak-∗ closed. -/
theorem remark_3_11 [CompleteSpace E] {ξ : StrongDual ℝ (StrongDual ℝ E)}
    (hξ : ξ ∉ Set.range (inclusionInDoubleDual ℝ E)) :
    IsClosed (toWeakSpace ℝ (StrongDual ℝ E) '' {f | ξ f = 0}) ∧
      ¬ IsClosed (StrongDual.toWeakDual '' {f | ξ f = 0}) := by
  constructor
  · rw [LinearEquiv.image_eq_preimage_symm]
    exact isClosed_eq (WeakBilin.eval_continuous (topDualPairing ℝ (StrongDual ℝ E)).flip ξ)
      continuous_const
  · intro hH
    have hξ0 : (ξ : StrongDual ℝ E →ₗ[ℝ] ℝ) ≠ 0 := fun h => by
      refine hξ ⟨0, ?_⟩
      rw [map_zero]
      exact (ContinuousLinearMap.coe_injective
        (h.trans ContinuousLinearMap.toLinearMap_zero.symm)).symm
    obtain ⟨x₀, β, hx₀, hset⟩ := corollary_3_15 hξ0 0 hH
    have hβ : β = 0 := by
      have h0 : (0 : StrongDual ℝ E) ∈ {f | (ξ : StrongDual ℝ E →ₗ[ℝ] ℝ) f = 0} := by simp
      rw [hset] at h0
      simpa using h0.symm
    subst hβ
    obtain ⟨lam, hlam⟩ := lemma_3_2 (ξ : StrongDual ℝ E →ₗ[ℝ] ℝ)
      (fun _ : Fin 1 => (inclusionInDoubleDual ℝ E x₀ : StrongDual ℝ E →ₗ[ℝ] ℝ))
      fun f hf => by
        have : f ∈ {f : StrongDual ℝ E | f x₀ = 0} := by simpa using hf 0
        rw [← hset] at this
        exact this
    refine hξ ⟨lam 0 • x₀, ?_⟩
    rw [map_smul]
    refine ContinuousLinearMap.coe_injective ?_
    rw [hlam, Fin.sum_univ_one]
    rfl

/-- **Theorem 3.16 (Banach–Alaoglu–Bourbaki).** The closed unit ball `B_{E*} = {f | ‖f‖ ≤ 1}` is
compact in the weak-∗ topology `σ(E*, E)`. -/
theorem theorem_3_16 [CompleteSpace E] :
    IsCompact (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ E) 1) :=
  WeakDual.isCompact_closedBall 0 1

end Brezis.Chapter03

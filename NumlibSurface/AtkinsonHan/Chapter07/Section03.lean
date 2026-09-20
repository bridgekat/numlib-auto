import Numlib.Analysis.Normed.Operator.Embedding
import Numlib.Analysis.Sobolev.Density
import Numlib.Analysis.Sobolev.DenyLions
import Numlib.Analysis.Sobolev.ExtensionHigher
import Numlib.Analysis.Sobolev.HolderEmbedding
import NumlibSurface.AtkinsonHan.Chapter07.Section02

/-!
# Atkinson–Han §7.3: density of smooth functions, and continuous and compact embeddings

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §7.3.

Four of the section's results are here. **Theorem 7.3.1**, the Meyers–Serrin theorem `H = W`,
and **Theorem 7.3.4**, the density of `C_0^∞(ℝ^d)` in `W^{k,p}(ℝ^d)`, are both proved, for
`1 ≤ p < ∞`. The work is in `Numlib/Analysis/Sobolev/Density.lean`, on top of the mollification
theory of `Numlib/Analysis/Sobolev/Mollification.lean`: on the whole space a single mollification
serves every point at once and the passage to compact support is a truncation; on a general open
set the mollifier radius has to shrink towards the boundary, which is what the exhaustion and the
partition of unity of Theorem 7.3.1 arrange. In both the norm is `sobolevNorm`, the reading of
`‖·‖_{k,p}` attached to `definition_7_2_2`, as in Theorem 7.3.3.

Definition 7.3.6 is the vocabulary of §7.3.3, and lives in
`Numlib/Analysis/Normed/Operator/Embedding.lean`: `IsContinuousEmbedding ι` is `V ↪ W`, the
injective linear `ι : V → W` with `‖ι v‖_W ≤ c ‖v‖_V` (7.3.1), and `IsCompactEmbedding ι` is
`V ↪↪ W`, that together with the book's compactness — every bounded sequence of `V` has a
subsequence whose image converges in `W`. `definition_7_3_6` and `definition_7_3_6_compact` are the
two under the book's number, and `isCompactEmbedding_iff_isCompactOperator` identifies the second
with Mathlib's `IsCompactOperator` on the inclusion, which is what makes the compact-operator
theory available to it. Theorem 7.3.3, that every `v ∈ W_0^{k,p}(Ω)` is the `W^{k,p}(Ω)` limit of a
sequence in `C_0^∞(Ω)`, is here too: Definition 7.2.9 is formalized as the closure of the image of
`C_0^∞(Ω)` in `W^{k,p}(Ω)`, so the theorem is that closure read sequentially.

The rest of §7.3 is here under the hypothesis of the Brezis backbone — an *extension domain*
(`IsSobolevExtensionDomain`, `IsSobolevExtensionDomainAll` of
`Numlib/Analysis/Sobolev/{Cutoff,EmbeddingDomain}.lean`) where the book assumes a Lipschitz
domain; the `C¹` domains of Definition 7.2.1 are extension domains by Brezis's Theorem 9.7
(`isSobolevExtensionDomainAll_of_definition_7_2_1`), a Lipschitz domain would be one by Stein's
or Calderón's theorem, which is not formalized. The ambient dimension is written `d + 1` as in
Definition 7.2.1. Theorem 7.3.2 (density of `C^∞(Ω̄)`) and Theorem 7.3.5 (the extension
operator) are at order `k = 1` (`theorem_7_3_2`, `theorem_7_3_5`, from Brezis's Theorem 9.7) and at
every order `k ≥ 1` (`theorem_7_3_2_higher`, `theorem_7_3_5_order`, from the higher-order
reflection of Exercise 7.3.2 in the charts, `Numlib/Analysis/Sobolev/ExtensionHigher.lean`); the
universal operator of Stein, one for all `k` and `p`, is the open `theorem_7_3_5_universal`.
Theorem 7.3.7 (the Sobolev embeddings) is in its three clauses `theorem_7_3_7_a`, `_b`, `_c`, the
Hölder clause (c) read on continuous representatives (`ContDiffOnClosure`), the integer case
`theorem_7_3_7_c_integer` through the order-lowering map of
`Numlib/Analysis/Sobolev/ExtensionHigher.lean`; Theorem 7.3.8 (Rellich–Kondrachov) likewise,
with the clause (c) into `C(Ω̄)` and into the Hölder spaces `C^{j,β}(Ω̄)` of
`Numlib/Analysis/Calculus/HolderSpace.lean` (`theorem_7_3_8_c_holder`); Theorem 7.3.9 is
`W^{k,p}(Ω) ↪↪ W^{l,p}(Ω)` for `p < ∞` and, by
Arzelà–Ascoli on the Lipschitz representatives, at `p = ∞` (`theorem_7_3_9_top`). All of these
are the whole-space theorems of `Numlib/Analysis/Sobolev/Embedding.lean` carried to the domain by
the extension operator, in `Numlib/Analysis/Sobolev/{EmbeddingDomain,Compactness,DenyLions}.lean`
and `ExtensionHigher.lean`.

Theorems 7.3.12–7.3.14, the Deny–Lions norm equivalences, are here for both quantities (7.3.3)
and (7.3.4) (`equation_7_3_3`, `equation_7_3_4`), from `Numlib/Analysis/Sobolev/DenyLions.lean`:
the compactness argument of the book with `W^{k,p}(Ω) ↪↪ W^{k−1,p}(Ω)`, and the fact that
`|v|_{k,p,Ω} = 0` on a connected open set forces a polynomial of degree `< k`. Example 7.3.15 is
here in its `H_0^1` clause, the Poincaré–Friedrichs inequality (7.3.10), which needs no regularity
of the boundary (Poincaré's inequality of `Numlib/Analysis/Sobolev/Poincare.lean`); its boundary
clause, Example 7.3.16, and Theorems 7.3.10–7.3.11 need the trace on `∂Ω`, which exists nowhere
(`notes/frontier.md`, blocker 2). Theorem 7.3.17 and Corollary 7.3.18 (§7.3.6, the Sobolev
quotient space `W^{k+1,p}(Ω)/ℙ_k(Ω)`) are here, with `ℙ_k(Ω)` the backbone's
`SobolevEuclidean.polynomialSubmodule` and the quotient norm written as the infimum over it:
the book's Hahn–Banach proof through Theorem 7.3.12.
-/

open Filter MeasureTheory Set TopologicalSpace

open scoped ContDiff Distributions ENNReal NNReal Topology

namespace AtkinsonHan.Chapter07

/-! ### Definition 7.3.6: continuous and compact embeddings -/

section Embedding

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {V W : Type*} [NormedAddCommGroup V]
  [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- **Definition 7.3.6**, the continuous embedding: for spaces `V ⊆ W`, one writes `V ↪ W` and
says `V` is continuously embedded in `W` when `‖v‖_W ≤ c ‖v‖_V` holds on `V` for some constant `c`
(7.3.1).

The inclusion `V ⊆ W` is carried by an injective linear map, because the two spaces have different
norms and the embeddings of §7.3.3 are between different types. The book's standing hypothesis that
`V` and `W` are Banach is not needed and is not imposed. -/
def definition_7_3_6 (ι : V →ₗ[𝕜] W) : Prop := IsContinuousEmbedding ι

/-- **Definition 7.3.6**, the compact embedding: for spaces `V ⊆ W`, one writes `V ↪↪ W` and says
`V` is compactly embedded in `W` when `V ↪ W` and, in addition, every bounded sequence of `V` has
a subsequence converging in `W`.

`isCompactEmbedding_iff_isCompactOperator` identifies this with an injective `IsCompactOperator`,
so the compact-operator theory applies to it. -/
def definition_7_3_6_compact (ι : V →ₗ[𝕜] W) : Prop := IsCompactEmbedding ι

/-- A compact embedding is a continuous embedding: Definition 7.3.6 asks for the bound (7.3.1)
before the compactness. -/
theorem definition_7_3_6_of_compact {ι : V →ₗ[𝕜] W} (h : definition_7_3_6_compact ι) :
    definition_7_3_6 ι :=
  h.toIsContinuousEmbedding

end Embedding

/-! ### Theorem 7.3.1: `C^∞(Ω) ∩ W^{k,p}(Ω)` is dense in `W^{k,p}(Ω)` -/

section Interior

variable {d : ℕ}

/-- **Theorem 7.3.1** (Meyers–Serrin, `H = W`): for `v ∈ W^{k,p}(Ω)` with `1 ≤ p < ∞` there is a
sequence `{v_n} ⊆ C^∞(Ω) ∩ W^{k,p}(Ω)` with `‖v_n - v‖_{k,p,Ω} → 0`.

The approximating functions are smooth in the *interior* of `Ω` only, which is what the book
emphasizes after the statement; no regularity of `∂Ω` is assumed anywhere, and Theorem 7.3.2 is
the sharpening that needs it. The norm is `sobolevNorm`, which is `‖·‖_{k,p,Ω}` in the bundled
reading of Definition 7.2.2; see the note there on the two readings.

The proof is in `Numlib/Analysis/Sobolev/Density.lean`: an exhaustion of `Ω` by relatively
compact open sets, a telescoping smooth partition of unity subordinate to it, and one mollifier
radius per piece. -/
theorem theorem_7_3_1 {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    {Ω : Opens (EuclideanSpace ℝ (Fin d))} {v : EuclideanSpace ℝ (Fin d) → ℝ}
    (hv : definition_7_2_2 k p Ω v) :
    ∃ w : ℕ → EuclideanSpace ℝ (Fin d) → ℝ,
      (∀ n, ContDiffOn ℝ ∞ (w n) (Ω : Set (EuclideanSpace ℝ (Fin d)))) ∧
        (∀ n, definition_7_2_2 k p Ω (w n)) ∧
        Tendsto (fun n ↦ sobolevNorm (w n - v) k p Ω volume) atTop (𝓝 0) :=
  hv.exists_seq_contDiffOn_tendsto_sobolevNorm hp hp'

end Interior

/-! ### Theorem 7.3.4: `C_0^∞(ℝ^d)` is dense in `W^{k,p}(ℝ^d)` -/

section WholeSpace

variable {d : ℕ}

/-- **Theorem 7.3.4**: for `k ≥ 0` and `p ∈ [1, ∞)` the space `C_0^∞(ℝ^d)` is dense in
`W^{k,p}(ℝ^d)`; that is, every `v ∈ W^{k,p}(ℝ^d)` is the limit of a sequence of test functions on
`ℝ^d` in the norm `‖·‖_{k,p}`.

The whole space is `⊤ : Opens (EuclideanSpace ℝ (Fin d))`, and `C_0^∞(ℝ^d)` is `𝓓(⊤, ℝ)`, the
smooth compactly supported functions — the support condition of a test function on `⊤` is vacuous.
Each `φ n` lies in `W^{k,p}(ℝ^d)` by `TestFunction.memSobolev`, so the sequence really is a
sequence of the space. The norm is `sobolevNorm`, which is `‖·‖_{k,p}` in the bundled reading of
Definition 7.2.2; see the note there on the two readings.

Unlike Theorems 7.3.1 and 7.3.2 this one needs neither an exhaustion nor a partition of unity: on
the whole space no point is near a boundary, so a single mollification approximates `v` and all
its weak derivatives at once, and multiplying by a cut-off `η(x/R)` makes the support compact at a
cost controlled by the Leibniz bound. -/
theorem theorem_7_3_4 {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    {v : EuclideanSpace ℝ (Fin d) → ℝ} (hv : definition_7_2_2 k p ⊤ v) :
    ∃ φ : ℕ → 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin d))), ℝ),
      Tendsto (fun n ↦ sobolevNorm ((φ n : EuclideanSpace ℝ (Fin d) → ℝ) - v) k p ⊤ volume)
        atTop (𝓝 0) := by
  obtain ⟨w, hw1, hw2, hw3⟩ :=
    MemSobolev.exists_seq_hasCompactSupport_tendsto_sobolevNorm hp hp' hv
  exact ⟨fun n ↦ ⟨w n, hw1 n, hw2 n, by simp⟩, hw3⟩

end WholeSpace

/-! ### Theorem 7.3.3: `W_0^{k,p}(Ω)` is the closure of `C_0^∞(Ω)` -/

variable {d : ℕ}

/-- **Theorem 7.3.3**: for `v ∈ W_0^{k,p}(Ω)` there is a sequence `{v_n} ⊆ C_0^∞(Ω)` with
`‖v_n - v‖_{k,p,Ω} → 0`; that is, every element of `W_0^{k,p}(Ω)` is a `W^{k,p}(Ω)` limit of test
functions.

Definition 7.2.9 is formalized as the closure, in the Banach space `Sobolev ℝ k p Ω volume` of
Theorem 7.2.3, of the submodule of the elements whose function agrees off a null set with a test
function on `Ω`; so this theorem is that closure read sequentially, a normed space being
metrizable. The sequence is produced as elements `u n` of `W^{k,p}(Ω)` together with the test
functions `φ n` they carry, because an element of the space is a tuple of derivatives and not a
function: `Sobolev.fn (u n) =ᵐ φ n` is what "`v_n ∈ C_0^∞(Ω)`" means here, and the derivatives of
`u n` are then the classical derivatives of `φ n`, by `TestFunction.memSobolev`. -/
theorem theorem_7_3_3 {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {Ω : Opens (EuclideanSpace ℝ (Fin d))} {v : Sobolev ℝ k p Ω volume}
    (hv : v ∈ definition_7_2_9 k p Ω) :
    ∃ (φ : ℕ → 𝓓(Ω, ℝ)) (u : ℕ → Sobolev ℝ k p Ω volume),
      (∀ n, Sobolev.fn (u n) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin d)))] φ n) ∧
        Tendsto (fun n ↦ ‖u n - v‖) atTop (𝓝 0) := by
  rw [definition_7_2_9, SobolevZero, ← SetLike.mem_coe,
    Submodule.topologicalClosure_coe] at hv
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hv
  choose φ hφ using fun n ↦ hu n
  exact ⟨φ, u, hφ, tendsto_iff_norm_sub_tendsto_zero.1 hlim⟩

/-! ### The domain hypothesis of §7.3 -/

section DomainHypothesis

/-- **The `C¹` domains of Definition 7.2.1 are extension domains for every exponent**: a bounded
open `Ω ⊆ ℝ^{d+1}` whose boundary is of class `C¹` in the sense of Definition 7.2.1 satisfies the
hypothesis `IsSobolevExtensionDomainAll (d + 1) Ω` under which the results of §7.3 are stated
here. This is Theorem 9.7 of Brezis (`IsSobolevExtensionDomainAll.of_isContDiffChartDomain`)
through the bridge `definition_7_2_1_contDiffDomain` between Definition 7.2.1 and the backbone's
graph domains. The book states §7.3 for Lipschitz domains; the formalization's hypothesis is the
extension property, which the `C¹` domains have (`notes/fem-roadmap.md`, Decision B) and which
a Lipschitz domain would have through Stein's or Calderón's theorem, not formalized. -/
theorem isSobolevExtensionDomainAll_of_definition_7_2_1
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} (hΩ : definition_7_2_1 {g | ContDiff ℝ 1 g} Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    IsSobolevExtensionDomainAll (d + 1) Ω :=
  IsSobolevExtensionDomainAll.of_isContDiffChartDomain
    ((definition_7_2_1_contDiffDomain 1 Ω).2 hΩ).isContDiffChartDomain
    (hb.closure.subset frontier_subset_closure)

end DomainHypothesis

/-! ### Theorem 7.3.2: density of `C^∞(Ω̄)` -/

section Density

/-- **Theorem 7.3.2** at order `k = 1`: for `v ∈ W^{1,p}(Ω)` with `1 ≤ p < ∞` on an extension
domain `Ω` there is a sequence `{v_n} ⊆ C^∞(Ω̄)` with `‖v_n − v‖_{1,p} → 0`. The approximants
`φ n` are even restrictions to `Ω` of `C_c^∞(ℝ^d)` functions, and `u n` is the element of
`W^{1,p}(Ω)` they define.

The book states the theorem for every order `k` on a Lipschitz domain; the formalization has
the extension domains of the `C¹` route (Brezis, Corollary 9.8, through
`SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_hasSobolevExtensionOn`) and
only the order `k = 1`, which is the order of the backbone's extension operator; the higher
orders are the open `theorem_7_3_2_higher`. `IsSobolevExtensionDomain` is supplied for the `C¹`
domains of Definition 7.2.1 by `isSobolevExtensionDomainAll_of_definition_7_2_1`. -/
theorem theorem_7_3_2 {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp' : p ≠ ⊤)
    {Ω : Opens (EuclideanSpace ℝ (Fin d))} (hΩ : IsSobolevExtensionDomain d p Ω)
    (v : SobolevMultiIndex ℝ (stdBasis d) 1 p Ω volume) :
    ∃ (φ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
      (u : ℕ → SobolevMultiIndex ℝ (stdBasis d) 1 p Ω volume),
      (∀ n, ContDiff ℝ ∞ (φ n)) ∧ (∀ n, HasCompactSupport (φ n)) ∧
      (∀ n, SobolevMultiIndex.fn (u n) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin d)))]
        φ n) ∧
      Tendsto (fun n ↦ ‖u n - v‖) atTop (𝓝 0) := by
  obtain ⟨φ, hφ, hφc, u, hu, hlim⟩ :=
    SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_hasSobolevExtensionOn hp' hΩ
      ⟨v, Submodule.mem_top⟩
  exact ⟨φ, u, hφ, hφc, hu, tendsto_iff_norm_sub_tendsto_zero.1 hlim⟩

/-- **The `C^k` domains of Definition 7.2.1 are `W^{k,p}`-extension domains**, `k ≥ 1`: a bounded
open `Ω ⊆ ℝ^{d+1}` whose boundary is of class `C^k` in the sense of Definition 7.2.1 has a bounded
linear extension operator `W^{k,p}(Ω) → W^{k,p}(ℝ^{d+1})` for every `p ∈ [1, ∞]`
(`IsSobolevExtensionDomainOfOrder.of_isContDiffChartDomain`, the higher-order reflection of
Exercise 7.3.2 in the charts of Brezis's Theorem 9.7), through the bridge
`definition_7_2_1_contDiffDomain`. The book states §7.3 for Lipschitz domains; the
formalization's hypothesis is the extension property at order `k`, which the `C^k` domains have
and which a Lipschitz domain would have through Stein's universal extension theorem, not
formalized. -/
theorem isSobolevExtensionDomainOfOrder_of_definition_7_2_1 {k : ℕ} (hk : 1 ≤ k) {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : definition_7_2_1 {g | ContDiff ℝ k g} Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    IsSobolevExtensionDomainOfOrder (d + 1) k p Ω :=
  IsSobolevExtensionDomainOfOrder.of_isContDiffChartDomain hk
    ((definition_7_2_1_contDiffDomain k Ω).2 hΩ).isContDiffChartDomain
    (hb.closure.subset frontier_subset_closure)

/-- **Theorem 7.3.2** at every order: for `v ∈ W^{k,p}(Ω)` with `1 ≤ p < ∞` on a
`W^{k,p}`-extension domain `Ω` there is a sequence `{v_n} ⊆ C^∞(Ω̄)` with `‖v_n − v‖_{k,p} → 0`.
The approximants `φ n` are restrictions to `Ω` of `C_c^∞(ℝ^d)` functions, and `u n` is the element
of `W^{k,p}(Ω)` they define.

The book states the theorem for a Lipschitz domain; the formalization has the
`W^{k,p}`-extension domains (`IsSobolevExtensionDomainOfOrder`), which the `C^k` domains of
Definition 7.2.1 are by `isSobolevExtensionDomainOfOrder_of_definition_7_2_1` (Brezis's
Corollary 9.8 at every order, through the higher-order extension operator of
`Numlib/Analysis/Sobolev/ExtensionHigher.lean`; a Lipschitz domain would enter through Stein's
theorem, not formalized). The order `k = 1` is `theorem_7_3_2`. -/
theorem theorem_7_3_2_higher {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp' : p ≠ ⊤)
    {Ω : Opens (EuclideanSpace ℝ (Fin d))} (hΩ : IsSobolevExtensionDomainOfOrder d k p Ω)
    (v : SobolevMultiIndex ℝ (stdBasis d) k p Ω volume) :
    ∃ (φ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
      (u : ℕ → SobolevMultiIndex ℝ (stdBasis d) k p Ω volume),
      (∀ n, ContDiff ℝ ∞ (φ n)) ∧ (∀ n, HasCompactSupport (φ n)) ∧
      (∀ n, SobolevMultiIndex.fn (u n) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin d)))]
        φ n) ∧
      Tendsto (fun n ↦ ‖u n - v‖) atTop (𝓝 0) := by
  obtain ⟨φ, hφ, hφc, u, hu, hlim⟩ :=
    SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_order hp' hΩ v
  exact ⟨φ, u, hφ, hφc, hu, tendsto_iff_norm_sub_tendsto_zero.1 hlim⟩


end Density

/-! ### Theorem 7.3.5: the extension operator -/

section Extension

/-- **Theorem 7.3.5** at order `k = 1`: for a bounded `C¹` domain `Ω ⊆ ℝ^{d+1}` (Definition
7.2.1) and `p ∈ [1, ∞]`, there is a linear continuous extension operator
`E : W^{1,p}(Ω) → W^{1,p}(ℝ^{d+1})`, `Ev = v` in `Ω`, with
`‖Ev‖_{W^{1,p}(ℝ^{d+1})} ≤ c ‖v‖_{W^{1,p}(Ω)}` for a constant `c` independent of `v`.

The book's theorem is Stein's *universal* extension theorem: one operator `E`, for a Lipschitz
domain or a half-space, continuous `W^{k,p}(Ω) → W^{k,p}(ℝ^d)` for *every* `k ≥ 0` and
`p ∈ [1, ∞]`, with `Ev` smooth off `closure Ω`. The formalization is Brezis's Theorem 9.7
(`SobolevEuclidean.exists_extensionL`, reflection across `C¹` charts): one operator per `p`, at
order `k = 1` only, with no smoothness of `Ev` off `closure Ω` — the reflected pieces are not
smooth there. The universal statement is the open `theorem_7_3_5_universal`. -/
theorem theorem_7_3_5 {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : definition_7_2_1 {g | ContDiff ℝ 1 g} Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    ∃ E : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 p Ω volume →L[ℝ]
        SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 p ⊤ volume,
      (∀ v, SobolevMultiIndex.fn (E v)
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] SobolevMultiIndex.fn v) ∧
      ∃ c : ℝ, ∀ v, ‖E v‖ ≤ c * ‖v‖ := by
  have h1 : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) :=
    ((definition_7_2_1_contDiffDomain 1 Ω).2 hΩ).isContDiffChartDomain
  have h2 : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    hb.closure.subset frontier_subset_closure
  have h3 := SobolevEuclidean.exists_extensionL (p := p) h1 h2
  obtain ⟨E, c, hE⟩ := h3
  exact ⟨E, fun v ↦ (hE v).1, c, fun v ↦ (hE v).2.2⟩

/-- **Theorem 7.3.5** at order `k ≥ 1`: for a bounded `C^k` domain `Ω ⊆ ℝ^{d+1}` (Definition
7.2.1) and `p ∈ [1, ∞]`, there is a linear continuous extension operator
`E : W^{k,p}(Ω) → W^{k,p}(ℝ^{d+1})`, `Ev = v` in `Ω`, with
`‖Ev‖_{W^{k,p}(ℝ^{d+1})} ≤ c ‖v‖_{W^{k,p}(Ω)}` for a constant `c` independent of `v`.

The book's theorem is Stein's *universal* extension theorem: one operator `E`, for a Lipschitz
domain or a half-space, continuous `W^{k,p}(Ω) → W^{k,p}(ℝ^d)` for *every* `k ≥ 0` and
`p ∈ [1, ∞]`, with `Ev` smooth off `closure Ω`. The formalization is the higher-order reflection
of Exercise 7.3.2 carried into the charts of Brezis's Theorem 9.7
(`SobolevEuclidean.exists_extensionL_of_order`, `Numlib/Analysis/Sobolev/ExtensionHigher.lean`):
one operator per `k` and `p`, on a `C^k` domain, with no smoothness of `Ev` off `closure Ω` —
the reflected pieces are not smooth there. The order `k = 1` on a `C¹` domain is
`theorem_7_3_5`; the universal statement is the open `theorem_7_3_5_universal`. -/
theorem theorem_7_3_5_order {k : ℕ} (hk : 1 ≤ k) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} (hΩ : definition_7_2_1 {g | ContDiff ℝ k g} Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    ∃ E : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume →L[ℝ]
        SobolevMultiIndex ℝ (stdBasis (d + 1)) k p ⊤ volume,
      (∀ v, SobolevMultiIndex.fn (E v)
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] SobolevMultiIndex.fn v) ∧
      ∃ c : ℝ, ∀ v, ‖E v‖ ≤ c * ‖v‖ := by
  have h1 : IsContDiffChartDomain k (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) :=
    ((definition_7_2_1_contDiffDomain k Ω).2 hΩ).isContDiffChartDomain
  have h2 : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    hb.closure.subset frontier_subset_closure
  have h3 := SobolevEuclidean.exists_extensionL_of_order (p := p) hk h1 h2
  obtain ⟨E, c, hE⟩ := h3
  exact ⟨E, fun v ↦ (hE v).1, c, fun v ↦ (hE v).2⟩


end Extension

/-! ### Theorems 7.3.7–7.3.9: the Sobolev embeddings -/

section Embeddings

variable {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **Theorem 7.3.7 (a)**: on a bounded extension domain `Ω ⊆ ℝ^{d+1}` (the book's Lipschitz
domain), if `k < (d+1)/p` then `W^{k,p}(Ω) ↪ L^q(Ω)` for every `q ≤ p^*`, where
`1/p^* = 1/p − k/(d+1)`; the embedding is the inclusion `SobolevMultiIndex.toLpₗ`, and
`definition_7_3_6` is the reading of `↪`. For `q ≤ p` this is Hölder's inequality on the bounded
`Ω`; for `p < q ≤ p^*` it is Brezis's Corollary 9.15 on the domain
(`SobolevEuclidean.isContinuousEmbedding_toLp_of_order_of_hasSobolevExtension`). -/
theorem theorem_7_3_7_a {k : ℕ} {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))]
    (hΩ : IsSobolevExtensionDomainAll (d + 1) Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hk : (k : ℝ) < (d + 1 : ℕ) / p) {p' : ℝ≥0}
    (hp' : (p' : ℝ)⁻¹ = (p : ℝ)⁻¹ - k / (d + 1 : ℕ)) (hq : q ≤ p') :
    ∃ h : ∀ u : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume,
        MemLp (SobolevMultiIndex.fn u) q
          (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      definition_7_3_6 (SobolevMultiIndex.toLpₗ ℝ (stdBasis (d + 1)) k p Ω volume h) := by
  have hμ := (hb.measure_lt_top (μ := volume)).ne
  have hp1 : (1 : ℝ≥0) ≤ p := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p)
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le (by exact_mod_cast hp1)
  have hN0 : (0 : ℝ) < (d + 1 : ℕ) := by positivity
  rcases le_or_gt q p with hqp | hpq
  · have : IsFiniteMeasure (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
      isFiniteMeasure_restrict.2 hμ
    have hqp' : (q : ℝ≥0∞) ≤ p := by exact_mod_cast hqp
    exact ⟨fun u ↦ (SobolevMultiIndex.memLp u).mono_exponent hqp',
      SobolevMultiIndex.isContinuousEmbedding_toLpₗ_of_le hμ hqp' _⟩
  · have hq0 : (0 : ℝ) < q := hp0.trans (by exact_mod_cast hpq)
    have hp'0 : (0 : ℝ) < p' := hq0.trans_le (by exact_mod_cast hq)
    have hq' : (p : ℝ)⁻¹ - k / (d + 1 : ℕ) ≤ (q : ℝ)⁻¹ := by
      rw [← hp']
      exact inv_anti₀ hq0 (by exact_mod_cast hq)
    -- `p < q ≤ p*` forces `k ≥ 1`, hence `d + 1 > p ≥ 1`
    have hN : 2 ≤ d + 1 ∨ 1 < p := by
      left
      have hpp' : (p : ℝ) < p' := hpq.trans_le (by exact_mod_cast hq)
      have hk1 : (0 : ℝ) < k := by
        by_contra hk0
        push Not at hk0
        have hk0' : (k : ℝ) = 0 := le_antisymm hk0 (Nat.cast_nonneg k)
        rw [hk0', zero_div, sub_zero] at hp'
        exact absurd (inv_inj.1 hp') hpp'.ne'
      have h1 : (1 : ℝ) < (d + 1 : ℕ) / p := lt_of_le_of_lt (by exact_mod_cast hk1) hk
      have h2 : (p : ℝ) < (d + 1 : ℕ) := by rwa [lt_div_iff₀ hp0, one_mul] at h1
      have h3 : (1 : ℝ) < (d + 1 : ℕ) := lt_of_le_of_lt (by exact_mod_cast hp1) h2
      exact_mod_cast h3
    exact ⟨_, SobolevEuclidean.isContinuousEmbedding_toLp_of_order_of_hasSobolevExtension hΩ hN
      hpq.le hq'⟩

/-- **Theorem 7.3.7 (b)**: on a bounded extension domain `Ω ⊆ ℝ^{d+1}`, if `k = (d+1)/p` then
`W^{k,p}(Ω) ↪ L^q(Ω)` for every `q < ∞`. The hypothesis `d ≥ 1 ∨ p > 1` excludes the case
`d + 1 = 1 = p` (an interval and `W^{1,1}`), for which the backbone's Corollary 9.15 is not
available; see Brezis's Corollary 9.11. -/
theorem theorem_7_3_7_b {k : ℕ} {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))]
    (hΩ : IsSobolevExtensionDomainAll (d + 1) Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (hN : 1 ≤ d ∨ 1 < p)
    (hk : (k : ℝ) = (d + 1 : ℕ) / p) :
    ∃ h : ∀ u : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume,
        MemLp (SobolevMultiIndex.fn u) q
          (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      definition_7_3_6 (SobolevMultiIndex.toLpₗ ℝ (stdBasis (d + 1)) k p Ω volume h) := by
  have hμ := (hb.measure_lt_top (μ := volume)).ne
  have hp1 : (1 : ℝ≥0) ≤ p := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p)
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le (by exact_mod_cast hp1)
  have hN0 : (0 : ℝ) < (d + 1 : ℕ) := by positivity
  rcases le_or_gt q p with hqp | hpq
  · have : IsFiniteMeasure (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
      isFiniteMeasure_restrict.2 hμ
    have hqp' : (q : ℝ≥0∞) ≤ p := by exact_mod_cast hqp
    exact ⟨fun u ↦ (SobolevMultiIndex.memLp u).mono_exponent hqp',
      SobolevMultiIndex.isContinuousEmbedding_toLpₗ_of_le hμ hqp' _⟩
  · have hq' : (p : ℝ)⁻¹ - k / (d + 1 : ℕ) ≤ (q : ℝ)⁻¹ := by
      rw [hk, div_div, mul_comm, ← div_div, div_self hN0.ne', one_div, sub_self]
      positivity
    have hN' : 2 ≤ d + 1 ∨ 1 < p := hN.imp (fun h ↦ by omega) id
    exact ⟨_, SobolevEuclidean.isContinuousEmbedding_toLp_of_order_of_hasSobolevExtension hΩ hN'
      hpq.le hq'⟩

/-- **Theorem 7.3.7 (c)**, the case `(d+1)/p` not an integer: on a bounded extension domain
`Ω ⊆ ℝ^{d+1}`, if `k > (d+1)/p` then `W^{k,p}(Ω) ↪ C^{k−[(d+1)/p]−1,β}(Ω̄)` with
`β = [(d+1)/p] + 1 − (d+1)/p`. With `j = k − [(d+1)/p] − 1`, every `v ∈ W^{k,p}(Ω)` has a
representative `v' ∈ C^j(Ω̄)` (`ContDiffOnClosure`, the derivatives up to order `j` extending
continuously to `Ω̄`) whose derivatives of order `≤ j` are bounded by `C ‖v‖_{k,p}` and whose
derivative of order `j` is `β`-Hölder with constant `C ‖v‖_{k,p}` — the bound
`‖v'‖_{C^{j,β}} ≤ C ‖v‖_{k,p}` of the embedding, read on the representative. Brezis's
Corollary 9.15 (`SobolevEuclidean.exists_contDiffOn_closure_ae_eq_of_order`); the hypothesis
`d ≥ 1 ∨ p > 1` is the backbone's. The case `(d+1)/p` an integer, where the book allows any
`β < 1`, is `theorem_7_3_7_c_integer`. -/
theorem theorem_7_3_7_c {k : ℕ} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hΩ : IsSobolevExtensionDomainAll (d + 1) Ω) (hN : 1 ≤ d ∨ 1 < p)
    (hk : ((d + 1 : ℕ) : ℝ) / p < k) (hint : ∀ j : ℕ, ((d + 1 : ℕ) : ℝ) / p ≠ j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume,
      ∃ v' : EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
        ContDiffOnClosure ℝ ((k - ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ - 1 : ℕ) : WithTop ℕ∞) v' Ω ∧
        SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] v' ∧
        (∀ i ≤ k - ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ - 1, ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
          ‖iteratedFDeriv ℝ i v' x‖ ≤ C * ‖v‖) ∧
        ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
          ∀ y ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
          ‖iteratedFDeriv ℝ (k - ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ - 1) v' x
              - iteratedFDeriv ℝ (k - ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ - 1) v' y‖
            ≤ C * ‖v‖ * ‖x - y‖ ^ (⌊((d + 1 : ℕ) : ℝ) / p⌋₊ + 1 - ((d + 1 : ℕ) : ℝ) / p) := by
  have hN' : 2 ≤ d + 1 ∨ 1 < p := hN.imp (fun h ↦ by omega) id
  have hs0 : (0 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) / p := by positivity
  obtain ⟨j, hj⟩ : ∃ j : ℕ, j = k - ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ - 1 := ⟨_, rfl⟩
  have hfloor : ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ < k := Nat.floor_lt hs0 |>.2 hk
  have hjcast : (j : ℝ) = k - ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ - 1 := by
    have hk' : k = j + ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ + 1 := by omega
    rw [hk']
    push_cast
    ring
  have hθ : (k : ℝ) - (d + 1 : ℕ) / p - j
      = ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ + 1 - ((d + 1 : ℕ) : ℝ) / p := by
    rw [hjcast]
    ring
  have hθ0 : 0 < (k : ℝ) - (d + 1 : ℕ) / p - j := by
    rw [hθ, sub_pos]
    exact Nat.lt_floor_add_one _
  have hθ1 : (k : ℝ) - (d + 1 : ℕ) / p - j < 1 := by
    have hlt : (⌊((d + 1 : ℕ) : ℝ) / p⌋₊ : ℝ) < ((d + 1 : ℕ) : ℝ) / p :=
      lt_of_le_of_ne (Nat.floor_le hs0) (Ne.symm (hint _))
    rw [hθ]
    linarith
  obtain ⟨C, hC0, hC⟩ := SobolevEuclidean.exists_contDiffOn_closure_ae_eq_of_order
    (N := d + 1) (m := k) (k := j) hΩ hN' hθ0 hθ1
  rw [← hθ, ← hj]
  refine ⟨C, hC0, fun v ↦ ?_⟩
  obtain ⟨v', -, hv', hae, hG, G, hGc, hGeq, hGh⟩ := hC v
  refine ⟨v', ⟨hv', fun i hi ↦ ?_⟩, hae, fun i hi x hx ↦ ?_, fun x hx y hy ↦ ?_⟩
  · obtain ⟨G', hG'c, hG'eq, -⟩ := hG i (by exact_mod_cast hi)
    exact ⟨G', hG'c.continuousOn, hG'eq.symm⟩
  · obtain ⟨G', -, hG'eq, hG'b⟩ := hG i hi
    rw [hG'eq hx]
    exact hG'b x
  · rw [hGeq hx, hGeq hy]
    exact hGh x y

set_option maxHeartbeats 800000 in
-- the seven destructurings of existentials (`j`, `q`, the Morrey data at exponent `q`, the
-- order-lowering operator `T`, the representative `v'`) in the typed Sobolev context at two
-- exponents cost 0.5–1 s each, 8 s in all (profiled), and the default budget of 200 000 is
-- exhausted at about 4 s; see `notes/lessons.md`, "heartbeats are per declaration".
/-- **Theorem 7.3.7 (c)**, the case `(d+1)/p = ℓ` an integer: on a bounded extension domain
`Ω ⊆ ℝ^{d+1}`, if `k > ℓ` then `W^{k,p}(Ω) ↪ C^{k−ℓ−1,β}(Ω̄)` for every `0 < β < 1`. With
`j = k − ℓ − 1`, every `v ∈ W^{k,p}(Ω)` has a representative `v' ∈ C^j(Ω̄)` whose derivatives of
order `≤ j` are bounded by `C ‖v‖_{k,p}` and whose derivative of order `j` is `β`-Hölder with
constant `C ‖v‖_{k,p}`, read on the representative as in `theorem_7_3_7_c`.

Proof: `W^{k,p}(Ω) ⊆ W^{j+1,q}(Ω)` for every `q < ∞` (the critical case of Brezis's
Corollary 9.15, as a bounded operator through the closed graph theorem,
`SobolevEuclidean.exists_continuousLinearMap_lower_of_order`), and for
`q = (d+1)/(1 − β) > d + 1` Morrey's theorem gives `W^{j+1,q}(Ω) ↪ C^{j,β}(Ω̄)`
(`SobolevEuclidean.exists_contDiffOn_closure_ae_eq_of_order`). The hypothesis `d ≥ 1 ∨ p > 1`
is the backbone's; the non-integer case is `theorem_7_3_7_c`. -/
theorem theorem_7_3_7_c_integer {k ℓ : ℕ} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hΩ : IsSobolevExtensionDomainAll (d + 1) Ω) (hN : 1 ≤ d ∨ 1 < p)
    (hℓ : ((d + 1 : ℕ) : ℝ) / p = ℓ) (hk : ℓ < k) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume,
      ∃ v' : EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
        ContDiffOnClosure ℝ ((k - ℓ - 1 : ℕ) : WithTop ℕ∞) v' Ω ∧
        SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] v' ∧
        (∀ i ≤ k - ℓ - 1, ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
          ‖iteratedFDeriv ℝ i v' x‖ ≤ C * ‖v‖) ∧
        ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
          ∀ y ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
          ‖iteratedFDeriv ℝ (k - ℓ - 1) v' x - iteratedFDeriv ℝ (k - ℓ - 1) v' y‖
            ≤ C * ‖v‖ * ‖x - y‖ ^ β := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = ℓ + 1 + j := ⟨k - ℓ - 1, by omega⟩
  have hj' : ℓ + 1 + j - ℓ - 1 = j := by omega
  rw [hj']
  have hN' : 2 ≤ d + 1 ∨ 1 < p := hN.imp (fun h ↦ by omega) id
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le (by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p))
  have hd1 : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
  have hℓ0 : (0 : ℝ) < ℓ := by rw [← hℓ]; positivity
  -- the exponent `q = (d+1)/(1 − β) > d + 1`
  obtain ⟨q, hq⟩ : ∃ q : ℝ≥0, (q : ℝ) = ((d + 1 : ℕ) : ℝ) / (1 - β) :=
    ⟨Real.toNNReal (((d + 1 : ℕ) : ℝ) / (1 - β)),
      Real.coe_toNNReal _ (div_nonneg hd1.le (by linarith))⟩
  have hqd : ((d + 1 : ℕ) : ℝ) < q := by
    rw [hq, lt_div_iff₀ (by linarith)]
    nlinarith
  have hq1 : (1 : ℝ) ≤ q := by
    have : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le d)
    linarith
  have : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨by exact_mod_cast hq1⟩
  have hpq : p ≤ q := by
    have hp : (p : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by
      have h1 : ((d + 1 : ℕ) : ℝ) = ℓ * p := by rw [← hℓ]; field_simp
      have h2 : (1 : ℝ) ≤ ℓ := by exact_mod_cast (Nat.one_le_iff_ne_zero.2 (by
        rintro rfl; simp at hℓ0))
      nlinarith
    exact_mod_cast hp.trans hqd.le
  have hr : (p : ℝ)⁻¹ - ℓ / (d + 1 : ℕ) ≤ (q : ℝ)⁻¹ := by
    have h1 : (p : ℝ)⁻¹ = ℓ / (d + 1 : ℕ) := by
      rw [← hℓ]; field_simp
    rw [h1, sub_self]
    positivity
  -- the order-lowering map and Morrey's theorem at exponent `q`
  have hθ : ((j + 1 : ℕ) : ℝ) - (d + 1 : ℕ) / q - j = β := by
    rw [hq]
    push_cast
    field_simp
    ring
  have hq1' : (1 : ℝ≥0) < q := by
    have : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le d)
    exact_mod_cast this.trans_lt hqd
  obtain ⟨C, hC0, hC⟩ := SobolevEuclidean.exists_contDiffOn_closure_ae_eq_of_order
    (N := d + 1) (m := j + 1) (k := j) (p := q) hΩ (Or.inr hq1') (by rw [hθ]; exact hβ0)
    (by rw [hθ]; exact hβ1)
  obtain ⟨T, hT⟩ := SobolevEuclidean.exists_continuousLinearMap_lower_of_order (N := d + 1) ℓ j
    (p := p) (r := q) hΩ hN' hpq hr
  refine ⟨C * ‖T‖, mul_nonneg hC0 (norm_nonneg _), fun v ↦ ?_⟩
  obtain ⟨v', -, hv', hae, hG, G, hGc, hGeq, hGh⟩ := hC (T v)
  have hTv : ‖T v‖ ≤ ‖T‖ * ‖v‖ := T.le_opNorm v
  have hCT : C * ‖T v‖ ≤ C * ‖T‖ * ‖v‖ := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hTv hC0
  refine ⟨v', ⟨hv', fun i hi ↦ ?_⟩, (hT v).symm.trans hae, fun i hi x hx ↦ ?_, fun x hx y hy ↦ ?_⟩
  · obtain ⟨G', hG'c, hG'eq, -⟩ := hG i (by exact_mod_cast hi)
    exact ⟨G', hG'c.continuousOn, hG'eq.symm⟩
  · obtain ⟨G', -, hG'eq, hG'b⟩ := hG i hi
    rw [hG'eq hx]
    exact (hG'b x).trans hCT
  · rw [hGeq hx, hGeq hy, ← hθ]
    refine (hGh x y).trans ?_
    gcongr


/-- **Theorem 7.3.7 (Sobolev embedding theorem)**, on a bounded extension domain `Ω ⊆ ℝ^{d+1}`
(the book's Lipschitz domain, see `isSobolevExtensionDomainAll_of_definition_7_2_1`): (a) if
`k < (d+1)/p` then `W^{k,p}(Ω) ↪ L^q(Ω)` for every `q ≤ p^*`, `1/p^* = 1/p − k/(d+1)`
(`theorem_7_3_7_a`); (b) if `k = (d+1)/p` then `W^{k,p}(Ω) ↪ L^q(Ω)` for every `q < ∞`
(`theorem_7_3_7_b`); (c) if `k > (d+1)/p` and `(d+1)/p` is not an integer then
`W^{k,p}(Ω) ↪ C^{k−[(d+1)/p]−1,β}(Ω̄)` with `β = [(d+1)/p] + 1 − (d+1)/p`, read on continuous
representatives (`theorem_7_3_7_c`). The clauses (b) and (c) carry the backbone's hypothesis
`d ≥ 1 ∨ p > 1`; the integer case of (c), with every `β < 1`, is `theorem_7_3_7_c_integer`. -/
theorem theorem_7_3_7 {k : ℕ} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hΩ : IsSobolevExtensionDomainAll (d + 1) Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    (∀ (q p' : ℝ≥0) [Fact (1 ≤ (q : ℝ≥0∞))], (k : ℝ) < (d + 1 : ℕ) / p →
      (p' : ℝ)⁻¹ = (p : ℝ)⁻¹ - k / (d + 1 : ℕ) → q ≤ p' →
      ∃ h : ∀ u : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume,
          MemLp (SobolevMultiIndex.fn u) q
            (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
        definition_7_3_6 (SobolevMultiIndex.toLpₗ ℝ (stdBasis (d + 1)) k p Ω volume h)) ∧
    (1 ≤ d ∨ 1 < p → (k : ℝ) = (d + 1 : ℕ) / p → ∀ (q : ℝ≥0) [Fact (1 ≤ (q : ℝ≥0∞))],
      ∃ h : ∀ u : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume,
          MemLp (SobolevMultiIndex.fn u) q
            (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
        definition_7_3_6 (SobolevMultiIndex.toLpₗ ℝ (stdBasis (d + 1)) k p Ω volume h)) ∧
    (1 ≤ d ∨ 1 < p → ((d + 1 : ℕ) : ℝ) / p < k → (∀ j : ℕ, ((d + 1 : ℕ) : ℝ) / p ≠ j) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume,
        ∃ v' : EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
          ContDiffOnClosure ℝ ((k - ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ - 1 : ℕ) : WithTop ℕ∞) v' Ω ∧
          SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
            v' ∧
          (∀ i ≤ k - ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ - 1,
            ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
            ‖iteratedFDeriv ℝ i v' x‖ ≤ C * ‖v‖) ∧
          ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
            ∀ y ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
            ‖iteratedFDeriv ℝ (k - ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ - 1) v' x
                - iteratedFDeriv ℝ (k - ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ - 1) v' y‖
              ≤ C * ‖v‖ * ‖x - y‖ ^ (⌊((d + 1 : ℕ) : ℝ) / p⌋₊ + 1 - ((d + 1 : ℕ) : ℝ) / p)) :=
  ⟨fun _ _ _ hk hp' hq ↦ theorem_7_3_7_a hΩ hb hk hp' hq,
    fun hN hk _ _ ↦ theorem_7_3_7_b hΩ hb hN hk, fun hN hk hint ↦ theorem_7_3_7_c hΩ hN hk hint⟩

/-- **Theorem 7.3.8 (a)** (Rellich–Kondrachov): on a bounded extension domain `Ω ⊆ ℝ^{d+1}`, if
`1 ≤ k < (d+1)/p` then `W^{k,p}(Ω) ↪↪ L^q(Ω)` for every `q < p^*`, `1/p^* = 1/p − k/(d+1)`.
The book writes `k < d/p` with `k ≥ 1` understood — at `k = 0` the statement would say
`L^p(Ω) ↪↪ L^q(Ω)` for `q < p`, which is false. The backbone's
`SobolevEuclidean.isCompactEmbedding_toLpₗ_of_order_of_lt`: `W^{k,p}(Ω) ↪ W^{1,r}(Ω)` and the
Rellich–Kondrachov theorem for `W^{1,r}(Ω)` (Brezis, Theorem 9.16). -/
theorem theorem_7_3_8_a {k : ℕ} {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))]
    (hΩ : IsSobolevExtensionDomainAll (d + 1) Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (hk1 : 1 ≤ k)
    (hk : (k : ℝ) < (d + 1 : ℕ) / p) {p' : ℝ≥0}
    (hp' : (p' : ℝ)⁻¹ = (p : ℝ)⁻¹ - k / (d + 1 : ℕ)) (hq : q < p') :
    ∃ h : ∀ u : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume,
        MemLp (SobolevMultiIndex.fn u) q
          (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      definition_7_3_6_compact
        (SobolevMultiIndex.toLpₗ ℝ (stdBasis (d + 1)) k p Ω volume h) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact SobolevEuclidean.isCompactEmbedding_toLpₗ_of_order_of_lt k hΩ
    (hb.measure_lt_top (μ := volume)).ne hk hp' hq

/-- **Theorem 7.3.8 (b)**, as printed: if `k = (d+1)/p` then `W^{k,p}(Ω) ↪ L^q(Ω)` for every
`q < ∞` — the book's clause (b) states a continuous embedding, the same as Theorem 7.3.7 (b);
the compact embedding it presumably intends is `theorem_7_3_8_b_compact`. -/
theorem theorem_7_3_8_b {k : ℕ} {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))]
    (hΩ : IsSobolevExtensionDomainAll (d + 1) Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (hN : 1 ≤ d ∨ 1 < p)
    (hk : (k : ℝ) = (d + 1 : ℕ) / p) :
    ∃ h : ∀ u : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume,
        MemLp (SobolevMultiIndex.fn u) q
          (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      definition_7_3_6 (SobolevMultiIndex.toLpₗ ℝ (stdBasis (d + 1)) k p Ω volume h) :=
  theorem_7_3_7_b hΩ hb hN hk

/-- **Theorem 7.3.8 (b), the compact form**: on a bounded extension domain `Ω ⊆ ℝ^{d+1}` with
`d ≥ 1`, if `k = (d+1)/p` (so `k ≥ 1`) then `W^{k,p}(Ω) ↪↪ L^q(Ω)` for every `q < ∞`. The
backbone's `SobolevEuclidean.isCompactEmbedding_toLpₗ_of_order_of_eq`:
`W^{k,p}(Ω) ↪ W^{1,d+1}(Ω) ↪↪ L^q(Ω)`. -/
theorem theorem_7_3_8_b_compact {k : ℕ} {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    [Fact (1 ≤ (q : ℝ≥0∞))] (hΩ : IsSobolevExtensionDomainAll (d + 1) Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (hd : 1 ≤ d)
    (hk : (k : ℝ) = (d + 1 : ℕ) / p) :
    ∃ h : ∀ u : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume,
        MemLp (SobolevMultiIndex.fn u) q
          (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      definition_7_3_6_compact
        (SobolevMultiIndex.toLpₗ ℝ (stdBasis (d + 1)) k p Ω volume h) := by
  have hp1 : (1 : ℝ≥0) ≤ p := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p)
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le (by exact_mod_cast hp1)
  have hk1 : 1 ≤ k := by
    have h1 : (0 : ℝ) < (d + 1 : ℕ) / p := div_pos (by positivity) hp0
    rw [← hk] at h1
    exact_mod_cast h1
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact SobolevEuclidean.isCompactEmbedding_toLpₗ_of_order_of_eq k hΩ
    (hb.measure_lt_top (μ := volume)).ne (by omega) hk

/-- **Theorem 7.3.8 (c)**, the case `β = 0` and `k − [(d+1)/p] − 1` replaced by `0`: on a bounded
extension domain `Ω ⊆ ℝ^{d+1}`, if `k > (d+1)/p` then `W^{k,p}(Ω) ↪↪ C(Ω̄)`: there is a bounded
linear `ι : W^{k,p}(Ω) → C(Ω̄)` sending `v` to the restriction of a continuous representative
of `v`, and `ι` is a compact embedding. The backbone's
`SobolevEuclidean.exists_isCompactEmbedding_toContinuousMap_of_order` (`W^{k,p}(Ω) ↪ W^{1,r}(Ω)`
for an `r > d + 1` and Arzelà–Ascoli); the hypothesis `d ≥ 1 ∨ p > 1` is the backbone's. The
Hölder clause `W^{k,p}(Ω) ↪↪ C^{k−[(d+1)/p]−1,β}(Ω̄)` for `β < [(d+1)/p] + 1 − (d+1)/p` is
`theorem_7_3_8_c_holder`. -/
theorem theorem_7_3_8_c {k : ℕ} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hΩ : IsSobolevExtensionDomainAll (d + 1) Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (hN : 1 ≤ d ∨ 1 < p)
    (hk : ((d + 1 : ℕ) : ℝ) / p < k) :
    haveI : CompactSpace (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
      isCompact_iff_compactSpace.1 hb.isCompact_closure
    ∃ ι : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume →L[ℝ]
        C(closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), ℝ),
      (∀ v, ∃ v' : EuclideanSpace ℝ (Fin (d + 1)) → ℝ, Continuous v' ∧
        SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] v' ∧
        ∀ x, ι v x = v' x) ∧
      definition_7_3_6_compact ι.toLinearMap := by
  have : CompactSpace (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    isCompact_iff_compactSpace.1 hb.isCompact_closure
  have hN' : 2 ≤ d + 1 ∨ 1 < p := hN.imp (fun h ↦ by omega) id
  have hp1 : (1 : ℝ≥0) ≤ p := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p)
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le (by exact_mod_cast hp1)
  have hk1 : 1 ≤ k := by
    have h1 : (0 : ℝ) < (d + 1 : ℕ) / p := div_pos (by positivity) hp0
    exact_mod_cast h1.trans hk
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact SobolevEuclidean.exists_isCompactEmbedding_toContinuousMap_of_order k hΩ hN' hk
    subset_closure

/-- **Theorem 7.3.8 (c), the Hölder target**: on a bounded extension domain `Ω ⊆ ℝ^{d+1}`, if
`k > (d+1)/p` then `W^{k,p}(Ω) ↪↪ C^{k−[(d+1)/p]−1,β}(Ω̄)` for every
`0 < β < [(d+1)/p] + 1 − (d+1)/p`: a bounded linear injection into the Hölder space
`HolderSpace` of `Numlib/Analysis/Calculus/HolderSpace.lean`, sending `v` to its continuous
representative, which is a compact embedding. The backbone's
`SobolevEuclidean.exists_isCompactEmbedding_toHolderSpace_of_lt`: Arzelà–Ascoli with Hölder
interpolation in `C^{j,·}(Ω̄)`, the sharp exponent of Corollary 9.15 in the non-integer case and
the order lowering `W^{k,p}(Ω) → W^{j+1,q}(Ω)` with Morrey at exponent `q` when `(d+1)/p` is an
integer (where the bound on `β` reads `β < 1`); the hypothesis `d ≥ 1 ∨ p > 1` is the backbone's.
The case `β = 0` with the target `C(Ω̄)` is `theorem_7_3_8_c`. -/
theorem theorem_7_3_8_c_holder {k : ℕ} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hΩ : IsSobolevExtensionDomainAll (d + 1) Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (hN : 1 ≤ d ∨ 1 < p)
    (hk : ((d + 1 : ℕ) : ℝ) / p < k) {β : ℝ≥0} (hβ0 : 0 < β)
    (hβ : (β : ℝ) < ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ + 1 - ((d + 1 : ℕ) : ℝ) / p) :
    ∃ ι : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume →L[ℝ]
        HolderSpace Ω ℝ (k - ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ - 1) β,
      (∀ v, ∃ v' : EuclideanSpace ℝ (Fin (d + 1)) → ℝ, Continuous v' ∧
        SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] v' ∧
        ∀ x, ι v x = v' x) ∧
      definition_7_3_6_compact ι.toLinearMap := by
  have hN' : 2 ≤ d + 1 ∨ 1 < p := hN.imp (fun h ↦ by omega) id
  have hs0 : (0 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) / p := by positivity
  have hfloor : ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ < k := Nat.floor_lt hs0 |>.2 hk
  have hjcast : ((k - ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ - 1 : ℕ) : ℝ)
      = k - ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  have hlt := Nat.lt_floor_add_one (((d + 1 : ℕ) : ℝ) / p)
  have hfl := Nat.floor_le hs0
  have hm : ((k - ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ - 1 : ℕ) : ℝ) + (d + 1 : ℕ) / p < k := by
    rw [hjcast]
    linarith
  have hle : (k : ℝ) - (d + 1 : ℕ) / p - ((k - ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ - 1 : ℕ) : ℝ) ≤ 1 := by
    rw [hjcast]
    linarith
  have hβ' : (β : ℝ) < k - (d + 1 : ℕ) / p - ((k - ⌊((d + 1 : ℕ) : ℝ) / p⌋₊ - 1 : ℕ) : ℝ) := by
    rw [hjcast]
    linarith
  exact SobolevEuclidean.exists_isCompactEmbedding_toHolderSpace_of_lt (N := d + 1) _ hΩ hb
    (by omega) hN' hm hle hβ0 hβ'

/-- **Theorem 7.3.8 (compact Sobolev embedding theorem, Rellich–Kondrachov)**, on a bounded
extension domain `Ω ⊆ ℝ^{d+1}`: (a) if `1 ≤ k < (d+1)/p` then `W^{k,p}(Ω) ↪↪ L^q(Ω)` for every
`q < p^*` (`theorem_7_3_8_a`); (b) if `k = (d+1)/p` then `W^{k,p}(Ω) ↪ L^q(Ω)` for every `q < ∞`
(`theorem_7_3_8_b`, as printed; the compact form is `theorem_7_3_8_b_compact`); (c) if
`k > (d+1)/p` then `W^{k,p}(Ω) ↪↪ C(Ω̄)` (`theorem_7_3_8_c`, the case `β = 0` of the book's
`C^{k−[(d+1)/p]−1,β}(Ω̄)`; the Hölder clause is `theorem_7_3_8_c_holder`). -/
theorem theorem_7_3_8 {k : ℕ} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hΩ : IsSobolevExtensionDomainAll (d + 1) Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    haveI : CompactSpace (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
      isCompact_iff_compactSpace.1 hb.isCompact_closure
    (∀ (q p' : ℝ≥0) [Fact (1 ≤ (q : ℝ≥0∞))], 1 ≤ k → (k : ℝ) < (d + 1 : ℕ) / p →
      (p' : ℝ)⁻¹ = (p : ℝ)⁻¹ - k / (d + 1 : ℕ) → q < p' →
      ∃ h : ∀ u : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume,
          MemLp (SobolevMultiIndex.fn u) q
            (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
        definition_7_3_6_compact
          (SobolevMultiIndex.toLpₗ ℝ (stdBasis (d + 1)) k p Ω volume h)) ∧
    (1 ≤ d ∨ 1 < p → (k : ℝ) = (d + 1 : ℕ) / p → ∀ (q : ℝ≥0) [Fact (1 ≤ (q : ℝ≥0∞))],
      ∃ h : ∀ u : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume,
          MemLp (SobolevMultiIndex.fn u) q
            (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
        definition_7_3_6 (SobolevMultiIndex.toLpₗ ℝ (stdBasis (d + 1)) k p Ω volume h)) ∧
    (1 ≤ d ∨ 1 < p → ((d + 1 : ℕ) : ℝ) / p < k →
      ∃ ι : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume →L[ℝ]
          C(closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), ℝ),
        (∀ v, ∃ v' : EuclideanSpace ℝ (Fin (d + 1)) → ℝ, Continuous v' ∧
          SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
            v' ∧
          ∀ x, ι v x = v' x) ∧
        definition_7_3_6_compact ι.toLinearMap) :=
  ⟨fun _ _ _ hk1 hk hp' hq ↦ theorem_7_3_8_a hΩ hb hk1 hk hp' hq,
    fun hN hk _ _ ↦ theorem_7_3_8_b hΩ hb hN hk, fun hN hk ↦ theorem_7_3_8_c hΩ hb hN hk⟩

/-- **Theorem 7.3.9**: for integers `k > l ≥ 0`, `p ∈ [1, ∞)` and a bounded extension domain
`Ω ⊆ ℝ^{d+1}` (the book's nonempty open bounded Lipschitz domain), `W^{k,p}(Ω) ↪↪ W^{l,p}(Ω)`
along the inclusion `SobolevMultiIndex.toLowerOrderL`. The backbone's
`SobolevEuclidean.isCompactEmbedding_toLowerOrderL_of_lt` (Brezis's Theorem 9.16 iterated); the
book's `p = ∞` is `theorem_7_3_9_top`. -/
theorem theorem_7_3_9 {k l : ℕ} (hlk : l < k) {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hΩ : IsSobolevExtensionDomain (d + 1) p Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    definition_7_3_6_compact
      (SobolevMultiIndex.toLowerOrderL ℝ (stdBasis (d + 1)) p Ω volume hlk.le).toLinearMap :=
  SobolevEuclidean.isCompactEmbedding_toLowerOrderL_of_lt hΩ (hb.measure_lt_top (μ := volume)).ne
    hlk

/-- **Theorem 7.3.9 at `p = ∞`**: for integers `k > l ≥ 0` and a bounded `W^{1,∞}`-extension
domain `Ω ⊆ ℝ^{d+1}` (the book's nonempty open bounded Lipschitz domain, which is one through
Stein's theorem, not formalized; the bounded `C¹` domains of Definition 7.2.1 are, by
`theorem_7_3_5`), `W^{k,∞}(Ω) ↪↪ W^{l,∞}(Ω)` along the inclusion
`SobolevMultiIndex.toLowerOrderL`. The backbone's
`SobolevEuclidean.isCompactEmbedding_toLowerOrderL_top_of_lt`
(`Numlib/Analysis/Sobolev/ExtensionHigher.lean`): `W^{1,∞}(Ω) ⊂⊂ L^∞(Ω)` is the Arzelà–Ascoli
theorem on the Lipschitz representatives of the extensions, iterated as for `p < ∞`. The case
`1 ≤ p < ∞` is `theorem_7_3_9`. -/
theorem theorem_7_3_9_top {k l : ℕ} (hlk : l < k) (hΩ : IsSobolevExtensionDomain (d + 1) ⊤ Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    definition_7_3_6_compact
      (SobolevMultiIndex.toLowerOrderL ℝ (stdBasis (d + 1)) ⊤ Ω volume hlk.le).toLinearMap :=
  SobolevEuclidean.isCompactEmbedding_toLowerOrderL_top_of_lt hΩ hb hlk

end Embeddings

/-! ### §7.3.5: equivalent norms (Deny–Lions) -/

section DenyLions

variable {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The quantity (7.3.3)**, `‖v‖ = |v|_{k,p,Ω} + ∑_{j=1}^J f_j(v)`, for seminorms `f_j` on
`W^{k,p}(Ω)`, where `|v|_{k,p,Ω} = (∫_Ω ∑_{|α| = k} |∂^α v|^p)^{1/p}` is the seminorm of §7.3.5,
the backbone's `SobolevMultiIndex.topSeminorm` (whose formula is
`SobolevMultiIndex.topSeminorm_eq_sum`; at `k = 1` it is the gradient norm,
`SobolevMultiIndex.topSeminorm_one_eq_gradNorm`). -/
noncomputable def equation_7_3_3 {J : Type*} [Fintype J]
    (f : J → Seminorm ℝ (SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume))
    (v : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume) : ℝ :=
  SobolevMultiIndex.topSeminorm ℝ (stdBasis (d + 1)) k p Ω volume v + ∑ j, f j v

/-- **The quantity (7.3.4)**, `‖v‖ = [|v|_{k,p,Ω}^p + ∑_{j=1}^J f_j(v)^p]^{1/p}`, for seminorms
`f_j` on `W^{k,p}(Ω)` and `p < ∞`. -/
noncomputable def equation_7_3_4 {J : Type*} [Fintype J]
    (f : J → Seminorm ℝ (SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume))
    (v : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume) : ℝ :=
  (SobolevMultiIndex.topSeminorm ℝ (stdBasis (d + 1)) k p Ω volume v ^ p.toReal
    + ∑ j, f j v ^ p.toReal) ^ (1 / p.toReal)

/-- **Theorem 7.3.12 (Deny–Lions norm equivalence)**: let `Ω ⊆ ℝ^{d+1}` be a connected bounded
extension domain (the book's Lipschitz domain), `k ≥ 1` (written `k + 1`), `1 ≤ p < ∞`, and let
`f_j : W^{k+1,p}(Ω) → ℝ`, `j ∈ J` finite, be seminorms with (H1) `0 ≤ f_j(v) ≤ c ‖v‖_{k+1,p,Ω}`
and (H2) "`v ∈ ℙ_k(Ω)` and `f_j(v) = 0` for all `j` imply `v = 0`". Then the quantities (7.3.3),
`|v|_{k+1,p,Ω} + ∑_j f_j(v)`, and (7.3.4), `[|v|_{k+1,p,Ω}^p + ∑_j f_j(v)^p]^{1/p}`, define norms
on `W^{k+1,p}(Ω)` equivalent to `‖v‖_{k+1,p,Ω}`: each vanishes only at `0` and is bounded above
and below by positive multiples of `‖v‖_{k+1,p,Ω}`.

`ℙ_k(Ω)` is read as the restrictions to `Ω` of the polynomials
`MvPolynomial.restrictTotalDegree (Fin (d + 1)) ℝ k` of total degree at most `k`, `v ∈ ℙ_k(Ω)`
meaning that the function of `v` agrees almost everywhere on `Ω` with one. The backbone's
`SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_of_isPreconnected`: the book's compactness
argument through `W^{k+1,p}(Ω) ↪↪ W^{k,p}(Ω)` (Theorem 7.3.9), and the fact that
`|v|_{k+1,p,Ω} = 0` on a connected `Ω` forces `v ∈ ℙ_k(Ω)`
(`SobolevMultiIndex.exists_mvPolynomial_ae_eq_of_forall_weakDeriv_eq_zero`). The book's Lipschitz
hypothesis is replaced by the extension property, which the `C¹` domains have
(`isSobolevExtensionDomainAll_of_definition_7_2_1`). -/
theorem theorem_7_3_12 {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hΩ : IsSobolevExtensionDomain (d + 1) p Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hc : IsPreconnected (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) {J : Type*} [Fintype J]
    (f : J → Seminorm ℝ (SobolevMultiIndex ℝ (stdBasis (d + 1)) (k + 1) p Ω volume))
    (h1 : ∃ c : ℝ, ∀ j v, f j v ≤ c * ‖v‖)
    (h2 : ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) (k + 1) p Ω volume,
      (∃ q ∈ MvPolynomial.restrictTotalDegree (Fin (d + 1)) ℝ k, SobolevMultiIndex.fn v
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
          fun x ↦ MvPolynomial.eval (fun i ↦ x i) q) →
      (∀ j, f j v = 0) → v = 0) :
    ((∀ v, equation_7_3_3 f v = 0 → v = 0) ∧
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
        ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) (k + 1) p Ω volume,
          c₁ * ‖v‖ ≤ equation_7_3_3 f v ∧ equation_7_3_3 f v ≤ c₂ * ‖v‖) ∧
    ((∀ v, equation_7_3_4 f v = 0 → v = 0) ∧
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
        ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) (k + 1) p Ω volume,
          c₁ * ‖v‖ ≤ equation_7_3_4 f v ∧ equation_7_3_4 f v ≤ c₂ * ‖v‖) := by
  obtain ⟨c, hf⟩ := h1
  exact SobolevMultiIndex.norm_equiv_of_exists_norm_le_topSeminorm_add_sum (by simp) hf
    (SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_of_isPreconnected hΩ
      (hb.measure_lt_top (μ := volume)).ne hc f hf h2)

/-- **Theorem 7.3.13**: the conclusion of Theorem 7.3.12 on a bounded extension domain
`Ω ⊆ ℝ^{d+1}` (the book's open bounded set with Lipschitz boundary), without connectedness, under
(H1) and the stronger (H2)′ "`|v|_{k+1,p,Ω} = 0` and `f_j(v) = 0` for all `j` imply `v = 0`":
both (7.3.3) and (7.3.4) are norms on `W^{k+1,p}(Ω)` equivalent to `‖v‖_{k+1,p,Ω}`. This is the
form that yields the Poincaré–Friedrichs inequality of Example 7.3.15. The backbone's
`SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_of_forall_eq_zero`. -/
theorem theorem_7_3_13 {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hΩ : IsSobolevExtensionDomain (d + 1) p Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) {J : Type*} [Fintype J]
    (f : J → Seminorm ℝ (SobolevMultiIndex ℝ (stdBasis (d + 1)) (k + 1) p Ω volume))
    (h1 : ∃ c : ℝ, ∀ j v, f j v ≤ c * ‖v‖)
    (h2 : ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) (k + 1) p Ω volume,
      SobolevMultiIndex.topSeminorm ℝ (stdBasis (d + 1)) (k + 1) p Ω volume v = 0 →
      (∀ j, f j v = 0) → v = 0) :
    ((∀ v, equation_7_3_3 f v = 0 → v = 0) ∧
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
        ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) (k + 1) p Ω volume,
          c₁ * ‖v‖ ≤ equation_7_3_3 f v ∧ equation_7_3_3 f v ≤ c₂ * ‖v‖) ∧
    ((∀ v, equation_7_3_4 f v = 0 → v = 0) ∧
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
        ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) (k + 1) p Ω volume,
          c₁ * ‖v‖ ≤ equation_7_3_4 f v ∧ equation_7_3_4 f v ≤ c₂ * ‖v‖) := by
  obtain ⟨c, hf⟩ := h1
  exact SobolevMultiIndex.norm_equiv_of_exists_norm_le_topSeminorm_add_sum (by simp) hf
    (SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_of_forall_eq_zero hΩ
      (hb.measure_lt_top (μ := volume)).ne f hf h2)

/-- **Theorem 7.3.14**: the conclusion of Theorem 7.3.12 for `Ω = ⋃_{λ ∈ Λ} Ω_λ` a bounded
extension domain of `ℝ^{d+1}` which is the union of connected open sets `Ω_λ` (the book's
disjoint union of sets with Lipschitz boundaries — disjointness plays no role in the proof and is
not assumed), under (H1) and (H2) "`v|_{Ω_λ} ∈ ℙ_k(Ω_λ)` for every `λ` and `f_j(v) = 0` for all
`j` imply `v = 0`": both (7.3.3) and (7.3.4) are norms on `W^{k+1,p}(Ω)` equivalent to
`‖v‖_{k+1,p,Ω}`. The backbone's `SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_of_iSup`. -/
theorem theorem_7_3_14 {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hΩ : IsSobolevExtensionDomain (d + 1) p Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    {Λ : Type*} {Ω' : Λ → Opens (EuclideanSpace ℝ (Fin (d + 1)))} (hΩ' : Ω = ⨆ l, Ω' l)
    (hc : ∀ l, IsPreconnected (Ω' l : Set (EuclideanSpace ℝ (Fin (d + 1))))) {J : Type*}
    [Fintype J] (f : J → Seminorm ℝ (SobolevMultiIndex ℝ (stdBasis (d + 1)) (k + 1) p Ω volume))
    (h1 : ∃ c : ℝ, ∀ j v, f j v ≤ c * ‖v‖)
    (h2 : ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) (k + 1) p Ω volume,
      (∀ l, ∃ q ∈ MvPolynomial.restrictTotalDegree (Fin (d + 1)) ℝ k, SobolevMultiIndex.fn v
        =ᵐ[volume.restrict (Ω' l : Set (EuclideanSpace ℝ (Fin (d + 1))))]
          fun x ↦ MvPolynomial.eval (fun i ↦ x i) q) →
      (∀ j, f j v = 0) → v = 0) :
    ((∀ v, equation_7_3_3 f v = 0 → v = 0) ∧
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
        ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) (k + 1) p Ω volume,
          c₁ * ‖v‖ ≤ equation_7_3_3 f v ∧ equation_7_3_3 f v ≤ c₂ * ‖v‖) ∧
    ((∀ v, equation_7_3_4 f v = 0 → v = 0) ∧
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
        ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) (k + 1) p Ω volume,
          c₁ * ‖v‖ ≤ equation_7_3_4 f v ∧ equation_7_3_4 f v ≤ c₂ * ‖v‖) := by
  obtain ⟨c, hf⟩ := h1
  exact SobolevMultiIndex.norm_equiv_of_exists_norm_le_topSeminorm_add_sum (by simp) hf
    (SobolevEuclidean.exists_norm_le_topSeminorm_add_sum_of_iSup hΩ
      (hb.measure_lt_top (μ := volume)).ne hΩ' hc f hf h2)

/-- **Example 7.3.15, the Poincaré–Friedrichs inequality (7.3.10)**: for a bounded open
`Ω ⊆ ℝ^{d+1}`, `‖v‖_{1,Ω} ≤ c |v|_{1,Ω}` for all `v ∈ H_0^1(Ω)`, so the seminorm `|·|_{1,Ω}` is
a norm on `H_0^1(Ω)` equivalent to the `H^1(Ω)`-norm (the other inequality being
`SobolevMultiIndex.topSeminorm_le_norm`).

The book derives it from Theorem 7.3.13 with `f_1(v) = ∫_Γ |v| ds` (`example_7_3_15_boundary`,
open: no trace). Here it is Poincaré's inequality on `W_0^{1,p}(Ω)`
(`SobolevEuclideanZero.norm_le_gradNorm`, Brezis's Corollary 9.19), which needs no regularity of
`∂Ω` and no compactness, with `c = (1 + 4R²)^{1/2}` for `Ω ⊆ B(0, R)`. `H_0^1(Ω)` is the
backbone's `SobolevEuclideanZero (d + 1) 1 2 Ω`, the closure of `C_0^∞(Ω)` in the space of
Definition 7.2.2 in the book's own indexing; `definition_7_2_9` is the same closure taken in the
bundled reading `Sobolev ℝ 1 2 Ω volume`, and the two are not identified. -/
theorem example_7_3_15 (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    ∃ c : ℝ, ∀ v : SobolevEuclideanZero (d + 1) 1 2 Ω,
      ‖(v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 2 Ω volume)‖
        ≤ c * SobolevMultiIndex.topSeminorm ℝ (stdBasis (d + 1)) 1 2 Ω volume
          (v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 2 Ω volume) := by
  obtain ⟨R, hR0, hR⟩ := hb.subset_ball_lt 0 0
  refine ⟨(1 + (2 * R) ^ (2 : ℝ≥0∞).toReal) ^ (1 / (2 : ℝ≥0∞).toReal), fun v ↦ ?_⟩
  rw [SobolevMultiIndex.topSeminorm_one_eq_gradNorm]
  exact SobolevEuclideanZero.norm_le_gradNorm (by simp) hR0.le hR v


/-! ### §7.3.6: the Sobolev quotient space -/

section Quotient

/-- `1 ≤ 2` for the exponent `p = 2` written in the backbone's form `((2 : ℝ≥0) : ℝ≥0∞)`, the
form in which the Euclidean theorems of `Numlib/Analysis/Sobolev/DenyLions.lean` (which take
`p : ℝ≥0`) return statements at `p = 2`. -/
instance fact_one_le_two_coe : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- **Theorem 7.3.17**: let `Ω ⊆ ℝ^{d+1}` be a connected bounded extension domain (the book's
Lipschitz domain), `1 ≤ p < ∞` and `k ≥ 0`, and let `V = W^{k+1,p}(Ω)/ℙ_k(Ω)` be the quotient
space with its quotient norm `‖[v]‖_V = inf_{q ∈ ℙ_k(Ω)} ‖v + q‖_{k+1,p,Ω}`. Then the quantity
`|v|_{k+1,p,Ω}`, `v ∈ [v]`, is a norm on `V` equivalent to `‖[v]‖_V`: it does not depend on the
representative, it vanishes exactly on the class of `0`, and
`c₁ |v|_{k+1,p,Ω} ≤ ‖[v]‖_V ≤ c₂ |v|_{k+1,p,Ω}` for all `v`, with `c₁ = 1` — the inequality
(7.3.13) being the second.

`ℙ_k(Ω)` is the backbone's `SobolevEuclidean.polynomialSubmodule`, the subspace of
`W^{k+1,p}(Ω)` of the elements whose function agrees almost everywhere on `Ω` with a polynomial
of total degree at most `k` (`SobolevEuclidean.mem_polynomialSubmodule_iff`), and the quotient
norm is written on representatives as the infimum over that subspace. The proof is the book's
first: the coordinate functionals of a basis of `ℙ_k(Ω)` extend by the Hahn–Banach theorem to
bounded functionals `f_i` on `W^{k+1,p}(Ω)`, the seminorms `|f_i|` satisfy the hypotheses of
Theorem 7.3.12, and the representative `v + q` with all `f_i(v + q) = 0` gives (7.3.13)
(`SobolevEuclidean.exists_ciInf_norm_add_le_mul_topSeminorm`); `|v|_{k+1,p,Ω} ≤ ‖[v]‖_V` because
`|·|_{k+1,p,Ω}` vanishes on `ℙ_k(Ω)` and is bounded by the norm. -/
theorem theorem_7_3_17 {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hΩ : IsSobolevExtensionDomain (d + 1) p Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hc : IsPreconnected (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    (∀ (v : SobolevMultiIndex ℝ (stdBasis (d + 1)) (k + 1) p Ω volume)
        (q : SobolevMultiIndex ℝ (stdBasis (d + 1)) (k + 1) p Ω volume),
        q ∈ SobolevEuclidean.polynomialSubmodule (k := k) (p := p) hb →
        SobolevMultiIndex.topSeminorm ℝ (stdBasis (d + 1)) (k + 1) p Ω volume (v + q)
          = SobolevMultiIndex.topSeminorm ℝ (stdBasis (d + 1)) (k + 1) p Ω volume v) ∧
    (∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) (k + 1) p Ω volume,
        SobolevMultiIndex.topSeminorm ℝ (stdBasis (d + 1)) (k + 1) p Ω volume v = 0 ↔
          v ∈ SobolevEuclidean.polynomialSubmodule (k := k) (p := p) hb) ∧
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) (k + 1) p Ω volume,
        c₁ * SobolevMultiIndex.topSeminorm ℝ (stdBasis (d + 1)) (k + 1) p Ω volume v
          ≤ ⨅ q : SobolevEuclidean.polynomialSubmodule (k := k) (p := p) hb, ‖v + q‖ ∧
        ⨅ q : SobolevEuclidean.polynomialSubmodule (k := k) (p := p) hb, ‖v + q‖
          ≤ c₂ * SobolevMultiIndex.topSeminorm ℝ (stdBasis (d + 1)) (k + 1) p Ω volume v := by
  have h := SobolevEuclidean.exists_ciInf_norm_add_le_mul_topSeminorm (k := k) hΩ hb hc
  obtain ⟨C, hC, hle⟩ := h
  refine ⟨fun v q hq ↦ ?_, fun v ↦ ?_, 1, C, one_pos, hC, fun v ↦ ⟨?_, hle v⟩⟩
  · exact SobolevEuclidean.topSeminorm_add_of_mem_polynomialSubmodule hb v hq
  · exact SobolevEuclidean.topSeminorm_eq_zero_iff_mem_polynomialSubmodule hb hc
  · exact (one_mul _).trans_le (SobolevEuclidean.topSeminorm_le_ciInf_norm_add hb v)

/-- **Corollary 7.3.18**, the inequality (7.3.16): for a connected bounded extension domain
`Ω ⊆ ℝ^{d+1}` (the book's Lipschitz domain) there is a constant `c` depending only on `Ω` (and
`k`) with `inf_{q ∈ ℙ_k(Ω)} ‖v + q‖_{k+1,Ω} ≤ c |v|_{k+1,Ω}` for all `v ∈ H^{k+1}(Ω)` — Theorem
7.3.17 at `p = 2`, the form Chapter 10 quotes for the finite element interpolation error. The
exponent is written `((2 : ℝ≥0) : ℝ≥0∞)`, the backbone's form of `p = 2`; `H^{k+1}(Ω)` is
`SobolevMultiIndex ℝ (stdBasis (d + 1)) (k + 1) 2 Ω volume`, definitionally. -/
theorem corollary_7_3_18 (hΩ : IsSobolevExtensionDomain (d + 1) ((2 : ℝ≥0) : ℝ≥0∞) Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hc : IsPreconnected (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    ∃ c : ℝ, ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) (k + 1) ((2 : ℝ≥0) : ℝ≥0∞) Ω volume,
      ⨅ q : SobolevEuclidean.polynomialSubmodule (k := k) (p := ((2 : ℝ≥0) : ℝ≥0∞)) hb, ‖v + q‖
        ≤ c * SobolevMultiIndex.topSeminorm ℝ (stdBasis (d + 1)) (k + 1) ((2 : ℝ≥0) : ℝ≥0∞) Ω
          volume v := by
  have h := SobolevEuclidean.exists_ciInf_norm_add_le_mul_topSeminorm (k := k) (p := 2) hΩ hb hc
  obtain ⟨C, -, hle⟩ := h
  exact ⟨C, hle⟩

end Quotient

end DenyLions

end AtkinsonHan.Chapter07

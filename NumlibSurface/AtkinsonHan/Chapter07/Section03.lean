import Numlib.Analysis.Normed.Operator.Embedding
import Numlib.Analysis.Sobolev.Boundary.ContDiffDomain
import Numlib.Analysis.Sobolev.Boundary.Kernel
import Numlib.Analysis.Sobolev.Boundary.PolygonTrace
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
reflection of Exercise 7.3.2 in the charts, `Numlib/Analysis/Sobolev/ExtensionHigher.lean`), and
at order `k` with the `L^p` bound of the extension as well (`theorem_7_3_5_order_lp`: one operator
bounded at the orders `0` and `k` at once, which is what Example 7.4.3 of §7.4 needs) and, at a
fixed `k`, as one operator for *every* exponent (`theorem_7_3_5_order_uniform`). Stein’s
universal operator, one for all `k` *and* `p` on a Lipschitz domain, is not formalized; the
`## Not formalized here` section below says what it would need.
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
of the boundary (Poincaré's inequality of `Numlib/Analysis/Sobolev/Poincare.lean`), and in its
boundary clause (`example_7_3_15_boundary`), with Example 7.3.16, the Poincaré–Friedrichs
inequality under a mixed boundary condition: both through the trace. Theorem 7.3.17 and
Corollary 7.3.18 (§7.3.6, the Sobolev quotient space `W^{k+1,p}(Ω)/ℙ_k(Ω)`) are here, with
`ℙ_k(Ω)` the backbone's `SobolevEuclidean.polynomialSubmodule` and the quotient norm written as the
infimum over it: the book's Hahn–Banach proof through Theorem 7.3.12.

§7.3.4, the traces, is here on the bounded `C¹` domains of Definition 7.2.1, where the book has
Lipschitz domains (out of scope, as everywhere in this chapter), and on the triangulated plane
domains — polygons — of the finite element chapters: the surface measure
`IsContDiffDomain.boundaryMeasure` on `∂Ω` and the trace operator `IsContDiffDomain.traceL`
of `Numlib/Analysis/Sobolev/Boundary/` — Nečas's construction from the divergence theorem with a
transversal vector field, extended by the density of `C^∞(Ω̄)` — give Theorem 7.3.10 in its
clauses (a)–(b) (`theorem_7_3_10`) and (c) (`theorem_7_3_10_compact`, for `1 < p`: the book's
`1 ≤ p` is an erratum, the trace `W^{1,1} → L¹(Γ)` being onto); on a polygon the trace is glued
along the boundary edges from the traces on the triangles (`Triangulation.traceL` of
`Numlib/Analysis/Sobolev/Boundary/PolygonTrace.lean`; `theorem_7_3_10_polygon`,
`theorem_7_3_10_polygon_compact`). The kernel of the trace is `W_0^{1,p}(Ω)`
(`theorem_7_3_10_kernel`, from `Numlib/Analysis/Sobolev/Boundary/Kernel.lean`), the meaning the
book promises for Definition 7.2.9 "after the trace theorems are presented". Theorem 7.3.11 is
here in its `L^p` clause at `s = 2`: the trace `γ₀ v = v|_Γ` and the normal-derivative trace
`γ₁ v = (∂v/∂ν)|_Γ = ∑ᵢ νᵢ γ(∂ᵢ v)` on `W^{2,p}(Ω)` (`theorem_7_3_11_trace₀`,
`theorem_7_3_11_trace₁`, with their values on smooth representatives), which are the unique such
operators on a bounded `C²` domain (`theorem_7_3_11`; the book's boundary is `C^{1,1}`, and the
density of smooth functions in `W^{2,p}(Ω)` that the uniqueness rests on is available through the
order-two extension operator of `C²` domains). The range clause `γ(W^{1,p}(Ω)) = W^{1−1/p,p}(Γ)`
and the fractional targets of Theorem 7.3.11 are not formalized: the boundary spaces `W^{σ,p}(Γ)`
of Definition 7.2.13 are defined relative to a patch system only, and nothing identifies the
spaces of two patch systems. The `## Not formalized here` section below is the record.

## Not formalized here

Three of §7.3's printed statements are out of scope: Stein's universal extension theorem, and the
two clauses whose targets are Sobolev spaces of fractional order on the boundary. Their plan nodes
were removed in the closing round of 2026-09-23 and this section is the permanent record.

**One obstruction is shared by the two fractional items** — and by Definition 7.2.13's
independence of the patch system, recorded in the `## Not formalized here` section of
`NumlibSurface/AtkinsonHan/Chapter07/Section02.lean`. The project has no *Sobolev space of
fractional order on a boundary* that it can compute with. `definition_7_2_13` does define
`W^{s,p}(∂Ω)`, as a submodule of `L^p(∂Ω)` cut out patch by patch through the Slobodeckij spaces
`SobolevSlobodeckij` of `Numlib/Analysis/Sobolev/Slobodeckij.lean` — but only *relative to a chosen
graph atlas*, and nothing identifies the spaces of two atlases. What is missing is a single theorem:
the invariance of the Slobodeckij seminorm `∬ |v(x) − v(y)|^p / |x − y|^{d−1+sp}` under a
bi-Lipschitz change of variables, applied to the `C¹` chart transitions
`EuclideanSpace.graphTransition` and localized to the overlaps of two patches. That is about 400
lines on top of `Slobodeckij.lean`, which carries the spaces and their norms but no change of
variables at all; the Jacobian bounds it would use are
`EuclideanSpace.graphDensity_graphTransition` of
`Numlib/Analysis/Sobolev/Boundary/GraphMeasure.lean`. Until it exists, a statement whose *target* is
`W^{σ,p}(Γ)` for non-integer `σ` is a statement about an atlas rather than about `Γ`, and is not
worth proving. The surface measure itself is atlas-independent (`GraphAtlas.measure_eq`), so at
`σ = 0` — the `L^p(Γ)` targets — nothing is missing, and that is exactly the range in which
`theorem_7_3_10` and `theorem_7_3_11` are proved.

* **Theorem 7.3.5, Stein's universal extension theorem.** For `Ω` a half-space or a Lipschitz
  domain there is *one* linear operator `E`, continuous `W^{k,p}(Ω) → W^{k,p}(ℝ^d)` for every
  `k ≥ 0` and every `p ∈ [1, ∞]`, with `Ev = v` on `Ω`, `Ev` smooth off `closure Ω`, and
  `‖Ev‖_{W^{k,p}(ℝ^d)} ≤ c ‖v‖_{W^{k,p}(Ω)}`. What is here instead is the reflection construction
  of Brezis's Theorem 9.7 and Exercise 7.3.2, in four forms: one operator per `p` at order one on a
  bounded `C¹` domain (`theorem_7_3_5`), one per `k` and `p` at order `k` on a bounded `C^k` domain
  (`theorem_7_3_5_order`), and the two clauses of the universal theorem that the reflection does
  give — a single operator bounded at the orders `0` and `k` *at once* (`theorem_7_3_5_order_lp`),
  which is what Example 7.4.3 of §7.4 needs, and, at a fixed `k`, a single operator *for every
  exponent* `p` (`theorem_7_3_5_order_uniform`), exhibited as the map
  `E f = 1_Ω · θ₀ f + ∑_i 1_{U_i} · θ_i · (higherReflection a l (f ∘ H_i) ∘ H_i⁻¹)` on functions.
  Two things stay out. (i) Lipschitz domains: the charts of `Numlib/Analysis/Sobolev/Chart.lean`
  are `C^n` graphs. (ii) One operator for all `k`, with `Ev` smooth off `closure Ω`: the reflection
  `∑_j a_j v(x', l_j x_N)` has coefficients solving a Vandermonde system of order `k`
  (`exists_vandermonde_coeffs_scales`), so it changes with `k`, and `Ev` is smooth off `closure Ω`
  for no `k`. Stein's operator is instead a Calderón-kernel regularization of the reflection
  (Stein, *Singular Integrals*, VI.3), research-scale here.

* **Theorem 7.3.10, the range clause.** The trace `γ` of `theorem_7_3_10` maps `W^{1,p}(Ω)` *onto*
  `W^{1−1/p,p}(Γ)`, so that `H^{1/2}(Γ) = γ(H^1(Ω))` and the quotient norm (7.3.2) is equivalent to
  the norm of Definition 7.2.13. This is Gagliardo's theorem, and on top of the shared obstruction
  above it is two projects: the fractional boundedness
  `‖γ v‖_{W^{1−1/p,p}(Γ)} ≤ C ‖v‖_{W^{1,p}(Ω)}` (~600 lines on `Slobodeckij.lean`, with the chart
  transport) and the right inverse, Gagliardo's extension of a `W^{1−1/p,p}` boundary function by
  averaging over balls (1000+ lines). The trace itself is proved, and no consumer in the corpus
  needs its range: `theorem_11_4_5` is stated through the density of traces in `L¹(Γ)` rather than
  through `H^{1/2}(Γ)`.

* **Theorem 7.3.11 as printed.** On a bounded open set with `C^{k,1}` boundary, for `1 ≤ p ≤ ∞` and
  `s − 1/p > 1` not an integer with `k ≥ s − 1`, the maps `γ₀ : W^{s,p}(Ω) → W^{s−1/p,p}(Γ)` and
  `γ₁ : W^{s,p}(Ω) → W^{s−1−1/p,p}(Γ)` are bounded, linear and *surjective*. What is proved is the
  `L^p(Γ)` clause at `s = 2`: `theorem_7_3_11`, over `theorem_7_3_11_trace₀` and
  `theorem_7_3_11_trace₁` with their values on smooth representatives, and uniqueness on a bounded
  `C²` domain. Everything fractional remains — the targets `W^{σ,p}(Γ)` (the shared obstruction),
  the domain spaces `W^{s,p}(Ω)` of non-integer `s`, the surjectivity (a Gagliardo-type theorem
  after the range clause above, 1000+ lines) and `C^{k,1}` boundaries, the library having `C^n`
  graphs only. The book itself quotes the statement from [98] without proof.
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
smooth there. The universal statement is not formalized; the module doc’s
`## Not formalized here` section says what it would need. -/
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
`theorem_7_3_5`; `theorem_7_3_5_order_lp` adds the `L^p` bound of the extension to this
statement and `theorem_7_3_5_order_uniform` makes the operator one and the same for every
exponent; the universal statement of the book is not formalized (the module doc’s
`## Not formalized here`). -/
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

/-! #### The order-`k` extension operator with its `L^p` bound

`SobolevEuclidean.exists_extensionL_of_order` of `Numlib/Analysis/Sobolev/ExtensionHigher.lean`
states only `‖Ev‖_{W^{k,p}(ℝ^{d+1})} ≤ c ‖v‖_{W^{k,p}(Ω)}`, where the order-one operator
`SobolevEuclidean.exists_extensionL` of `Numlib/Analysis/Sobolev/Extension.lean` carries in
addition `‖Ev‖_{L^p(ℝ^{d+1})} ≤ c ‖v‖_{L^p(Ω)}`. The three lemmas below re-run the order-`k`
assembly keeping that second bound: each piece of the operator has one
(`SobolevMultiIndex.eLpNorm_fn_extendZeroMulL_le` for the zero extensions,
`SobolevMultiIndex.exists_eLpNorm_fn_compDiffeoL_le` for the two chart transports,
`SobolevMultiIndex.exists_eLpNorm_fn_higherReflectionL_le` for the higher-order reflection — a
finite sum of dilations), and the closed graph theorem
`SobolevMultiIndex.exists_continuousLinearMap_of_order` ties the function of the order-`k`
operator to the function of the order-one one, so the bound survives the passage to order `k`.
They belong in `ExtensionHigher.lean` and are here only because it is read-only for this round. -/

/-- **The `L^p` bound of a restrict–transfer–reflect–retransfer composite**, with the operators
and all three constants as variables: `SobolevEuclidean.eLpNorm_chartExtend_of_ops` of
`Numlib/Analysis/Sobolev/Extension.lean` with the reflection's constant `2` — which is the even
reflection's — replaced by a variable, as the higher-order reflection needs. -/
private theorem eLpNorm_chartExtend_of_ops' {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {Ω Ωc Qp Q U : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (R : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p Ωc)
    (T₁ : SobolevEuclidean (d + 1) 1 p Ωc →L[ℝ] SobolevEuclidean (d + 1) 1 p Qp)
    (S : SobolevEuclidean (d + 1) 1 p Qp →L[ℝ] SobolevEuclidean (d + 1) 1 p Q)
    (T₂ : SobolevEuclidean (d + 1) 1 p Q →L[ℝ] SobolevEuclidean (d + 1) 1 p U)
    (hRfn : ∀ u, SobolevMultiIndex.fn (R u)
      =ᵐ[volume.restrict (Ωc : Set (EuclideanSpace ℝ (Fin (d + 1))))] SobolevMultiIndex.fn u)
    {C₁ C₂ C₃ : ℝ≥0∞}
    (hT₁ : ∀ v, eLpNorm (SobolevMultiIndex.fn (T₁ v)) p
        (volume.restrict (Qp : Set (EuclideanSpace ℝ (Fin (d + 1)))))
      ≤ C₁ * eLpNorm (SobolevMultiIndex.fn v) p
        (volume.restrict (Ωc : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (hS : ∀ w, eLpNorm (SobolevMultiIndex.fn (S w)) p
        (volume.restrict (Q : Set (EuclideanSpace ℝ (Fin (d + 1)))))
      ≤ C₂ * eLpNorm (SobolevMultiIndex.fn w) p
        (volume.restrict (Qp : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (hT₂ : ∀ w, eLpNorm (SobolevMultiIndex.fn (T₂ w)) p
        (volume.restrict (U : Set (EuclideanSpace ℝ (Fin (d + 1)))))
      ≤ C₃ * eLpNorm (SobolevMultiIndex.fn w) p
        (volume.restrict (Q : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (u : SobolevEuclidean (d + 1) 1 p Ω) :
    eLpNorm (SobolevMultiIndex.fn (T₂ (S (T₁ (R u))))) p
        (volume.restrict (U : Set (EuclideanSpace ℝ (Fin (d + 1)))))
      ≤ C₃ * (C₂ * C₁) * eLpNorm (SobolevMultiIndex.fn u) p
        (volume.restrict (Ωc : Set (EuclideanSpace ℝ (Fin (d + 1))))) := by
  calc eLpNorm (SobolevMultiIndex.fn (T₂ (S (T₁ (R u))))) p
          (volume.restrict (U : Set (EuclideanSpace ℝ (Fin (d + 1)))))
      ≤ C₃ * eLpNorm (SobolevMultiIndex.fn (S (T₁ (R u)))) p
          (volume.restrict (Q : Set (EuclideanSpace ℝ (Fin (d + 1))))) := hT₂ _
    _ ≤ C₃ * (C₂ * eLpNorm (SobolevMultiIndex.fn (T₁ (R u))) p
          (volume.restrict (Qp : Set (EuclideanSpace ℝ (Fin (d + 1)))))) := by
        gcongr; exact hS _
    _ ≤ C₃ * (C₂ * (C₁ * eLpNorm (SobolevMultiIndex.fn (R u)) p
          (volume.restrict (Ωc : Set (EuclideanSpace ℝ (Fin (d + 1))))))) := by
        gcongr; exact hT₁ _
    _ = C₃ * (C₂ * C₁) * eLpNorm (SobolevMultiIndex.fn u) p
          (volume.restrict (Ωc : Set (EuclideanSpace ℝ (Fin (d + 1))))) := by
        rw [eLpNorm_congr_ae (hRfn u)]; ring

/-- **The `L^p` bound of the higher-order chart-local extension**
`SobolevEuclidean.chartExtendLr`: `‖w_i‖_{L^p(U_r)} ≤ C ‖u‖_{L^p(U_r ∩ Ω)}`. The order-one
`SobolevEuclidean.chartExtendL` has it as `SobolevEuclidean.exists_eLpNorm_fn_chartExtendL_le`;
the higher-order variant does not, and its three mass-moving steps are the transport to `Q_{r,+}`
along the chart, the reflection to `Q_r` and the transport back to `U_r`. -/
private theorem exists_eLpNorm_fn_chartExtendLr_le {n : WithTop ℕ∞} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} {m : ℕ} {a l : Fin m → ℝ}
    (c : ContDiffChart n (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (hn : 1 ≤ n) {r : ℝ}
    (hr : r < 1) (ha : ∑ j, a j = 1) (hl : ∀ j, l j < 0) (hl1 : ∀ j, -1 ≤ l j) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ u : SobolevEuclidean (d + 1) 1 p Ω,
      eLpNorm (SobolevMultiIndex.fn (SobolevEuclidean.chartExtendLr p c hn hr ha hl hl1 u)) p
          (volume.restrict (c.opensUr hr : Set (EuclideanSpace ℝ (Fin (d + 1)))))
        ≤ C * eLpNorm (SobolevMultiIndex.fn u) p
          (volume.restrict (c.opensInterr hr : Set (EuclideanSpace ℝ (Fin (d + 1))))) := by
  obtain ⟨C₁, hC₁, h₁⟩ := SobolevMultiIndex.exists_eLpNorm_fn_compDiffeoL_le (F := ℝ)
    (b := stdBasis (d + 1)) (p := p) (μ := volume)
    (c.exists_isDiffeoOnWithBoundedJacobian_posHalf_cylinder hr hn).choose_spec
  obtain ⟨C₂, hC₂, h₂⟩ := SobolevMultiIndex.exists_eLpNorm_fn_higherReflectionL_le (F := ℝ)
    (b := stdBasis (d + 1)) (p := p) (r := r) ha hl hl1
  obtain ⟨C₃, hC₃, h₃⟩ := SobolevMultiIndex.exists_eLpNorm_fn_compDiffeoL_le (F := ℝ)
    (b := stdBasis (d + 1)) (p := p) (μ := volume)
    (c.exists_isDiffeoOnWithBoundedJacobian_cylinder hr hn).choose_spec.symm
  refine ⟨C₃ * (C₂ * C₁), ENNReal.mul_ne_top hC₃ (ENNReal.mul_ne_top hC₂ hC₁), fun u ↦ ?_⟩
  exact eLpNorm_chartExtend_of_ops' (SobolevEuclidean.chartRestrictLr p c hr)
    (SobolevEuclidean.chartTransferLr p c hn hr) (SobolevEuclidean.cubeReflectLr p ha hl hl1)
    (SobolevEuclidean.chartRetransferLr p c hn hr) (SobolevEuclidean.fn_chartRestrictLr p c hr)
    h₁ h₂ h₃ u

/-- **From an order-one operator with an `L^p` bound to the operator at order `k`**:
`SobolevEuclidean.exists_extensionL_of_order_of_ops` with the `L^p` bound carried over. The
closed graph theorem `SobolevMultiIndex.exists_continuousLinearMap_of_order` gives an operator
whose function is the function of `P₁`, so the `L^p` bound of `P₁` is the `L^p` bound of it. -/
private theorem exists_extensionL_of_order_lp_of_ops {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} {k : ℕ} (hk : 1 ≤ k)
    (P₁ : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤)
    (hid : ∀ u, SobolevMultiIndex.fn (P₁ u)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] SobolevMultiIndex.fn u)
    (hmem : ∀ u : SobolevEuclidean (d + 1) 1 p Ω,
      MemSobolevMultiIndex (stdBasis (d + 1)) (SobolevMultiIndex.fn u) k p Ω volume →
      MemSobolevMultiIndex (stdBasis (d + 1)) (SobolevMultiIndex.fn (P₁ u)) k p ⊤ volume)
    {K : ℝ≥0∞} (hKt : K ≠ ⊤)
    (hlp : ∀ u, eLpNorm (SobolevMultiIndex.fn (P₁ u)) p volume
      ≤ K * eLpNorm (SobolevMultiIndex.fn u) p
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    ∃ (P : SobolevEuclidean (d + 1) k p Ω →L[ℝ] SobolevEuclidean (d + 1) k p ⊤) (C : ℝ),
      ∀ u : SobolevEuclidean (d + 1) k p Ω,
        SobolevMultiIndex.fn (P u)
            =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
            SobolevMultiIndex.fn u ∧
        ‖P u‖ ≤ C * ‖u‖ ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume ≤ ENNReal.ofReal C
          * eLpNorm (SobolevMultiIndex.fn u) p
            (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) := by
  obtain ⟨Pk, hPk⟩ := SobolevMultiIndex.exists_continuousLinearMap_of_order hk P₁ fun u ↦
    hmem (SobolevMultiIndex.toLowerOrderL ℝ (stdBasis (d + 1)) p Ω volume hk u)
      (SobolevMultiIndex.memSobolevMultiIndex u)
  refine ⟨Pk, max K.toReal ‖Pk‖,
    fun u ↦ ⟨Filter.EventuallyEq.trans
        (ae_restrict_of_ae_restrict_of_subset (subset_univ _) (hPk u)) (hid _),
      (Pk.le_opNorm u).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)), ?_⟩⟩
  have h1 : SobolevMultiIndex.fn (Pk u) =ᵐ[volume] SobolevMultiIndex.fn
      (P₁ (SobolevMultiIndex.toLowerOrderL ℝ (stdBasis (d + 1)) p Ω volume hk u)) :=
    eventuallyEq_restrict_coe_top_iff.1 (hPk u)
  have h2 : SobolevMultiIndex.fn
      (SobolevMultiIndex.toLowerOrderL ℝ (stdBasis (d + 1)) p Ω volume hk u)
      = SobolevMultiIndex.fn u := rfl
  rw [eLpNorm_congr_ae h1]
  refine (hlp _).trans ?_
  rw [h2]
  gcongr
  calc K = ENNReal.ofReal K.toReal := (ENNReal.ofReal_toReal hKt).symm
    _ ≤ ENNReal.ofReal (max K.toReal ‖Pk‖) := ENNReal.ofReal_le_ofReal (le_max_left _ _)

/-- **The order-`k` extension operator with its `L^p` bound, over an explicit atlas**: the
assembly of `SobolevEuclidean.exists_extensionL_of_order_of_atlas` with the `L^p(ℝ^{d+1})` bound
of the order-one operator carried through the closed graph theorem. -/
private theorem exists_extensionL_of_order_lp_of_atlas {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} {k n : ℕ} (hk : 1 ≤ k)
    (c : Fin n → ContDiffChart k (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    {θ₀ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} {θ : Fin n → EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hθ₀ : ContDiff ℝ ∞ θ₀) (hθ₀κ : ∃ κ : ℝ, HasCompactSupport fun x ↦ θ₀ x - κ)
    (hθ₀Γ : Disjoint (tsupport θ₀) (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (hθ : ∀ i, ContDiff ℝ ∞ (θ i)) (hθc : ∀ i, HasCompactSupport (θ i))
    (hsum : ∀ x, θ₀ x + ∑ i, θ i x = 1) {r : Fin n → ℝ} (hr : ∀ i, r i < 1)
    (hθr : ∀ i, tsupport (θ i) ⊆ (c i).opensUr (hr i)) {m : ℕ} {a l : Fin m → ℝ}
    (ha0 : ∑ j, a j = 1) (hl0 : ∀ j, l j < 0) (hl1 : ∀ j, -1 ≤ l j)
    (hak : ∀ i < k, ∑ j, a j * l j ^ i = 1) :
    ∃ (P : SobolevEuclidean (d + 1) k p Ω →L[ℝ] SobolevEuclidean (d + 1) k p ⊤) (C : ℝ),
      ∀ u : SobolevEuclidean (d + 1) k p Ω,
        SobolevMultiIndex.fn (P u)
            =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
            SobolevMultiIndex.fn u ∧
        ‖P u‖ ≤ C * ‖u‖ ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume ≤ ENNReal.ofReal C
          * eLpNorm (SobolevMultiIndex.fn u) p
            (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) := by
  have hn : (1 : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by exact_mod_cast hk
  have hα₀ : IsSobolevCutoff Ω θ₀ :=
    IsSobolevCutoff.of_hasCompactSupport_sub hθ₀ hθ₀κ.choose_spec hθ₀Γ
  have hα : ∀ i, IsSobolevCutoff ((c i).opensUr (hr i)) (θ i) := fun i ↦
    IsSobolevCutoff.of_hasCompactSupport (hθ i) (hθc i) (hθr i)
  obtain ⟨M₀, -, hM₀⟩ := hα₀.exists_nonneg_bound
  choose M hM0 hM using fun i ↦ (hα i).exists_nonneg_bound
  choose B hB hBu using fun i ↦
    exists_eLpNorm_fn_chartExtendLr_le (p := p) (c i) hn (hr i) ha0 hl0 hl1
  obtain ⟨P₁, hP₁⟩ :
      ∃ P₁ : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤,
        ∀ u, P₁ u = SobolevMultiIndex.extendZeroMulL ℝ (stdBasis (d + 1)) p volume hα₀ u
          + ∑ i, SobolevMultiIndex.extendZeroMulL ℝ (stdBasis (d + 1)) p volume (hα i)
              (SobolevEuclidean.chartExtendLr p (c i) hn (hr i) ha0 hl0 hl1 u) :=
    ⟨SobolevMultiIndex.extendZeroMulL ℝ (stdBasis (d + 1)) p volume hα₀
        + ∑ i, (SobolevMultiIndex.extendZeroMulL ℝ (stdBasis (d + 1)) p volume (hα i)).comp
          (SobolevEuclidean.chartExtendLr p (c i) hn (hr i) ha0 hl0 hl1),
      fun u ↦ by
        simp only [_root_.add_apply, _root_.sum_apply, ContinuousLinearMap.comp_apply]⟩
  have hid : ∀ u, SobolevMultiIndex.fn (P₁ u)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      SobolevMultiIndex.fn u := fun u ↦
    SobolevEuclidean.fn_extension_ae_eq_of_ops (Ωc := fun i ↦ (c i).opensInterr (hr i))
      (fun _ ↦ rfl) (χ := fun _ ↦ 1) (fun x _ ↦ hsum x)
      (fun i x hx ↦ image_eq_zero_of_notMem_tsupport fun h ↦ hx (hθr i h))
      (fun u ↦ SobolevMultiIndex.fn_extendZeroMulL hα₀ u)
      (fun i w ↦ SobolevMultiIndex.fn_extendZeroMulL (hα i) w)
      (fun i u ↦ SobolevEuclidean.chartExtendLr_fn_ae_eq p (c i) hn (hr i) ha0 hl0 hl1 u)
      hP₁ u (Eventually.of_forall fun x ↦ (one_mul _).symm)
  have hmem : ∀ u : SobolevEuclidean (d + 1) 1 p Ω,
      MemSobolevMultiIndex (stdBasis (d + 1)) (SobolevMultiIndex.fn u) k p Ω volume →
      MemSobolevMultiIndex (stdBasis (d + 1)) (SobolevMultiIndex.fn (P₁ u)) k p ⊤ volume :=
    fun u hu ↦ SobolevEuclidean.extension_mem_of_ops
      (fun u ↦ SobolevMultiIndex.fn_extendZeroMulL hα₀ u)
      (fun i w ↦ SobolevMultiIndex.fn_extendZeroMulL (hα i) w) hP₁ hθ₀ hθ₀κ hθ₀Γ hθ hθc hθr
      (fun i u hu ↦ SobolevEuclidean.chartExtendLr_mem_of_order p (c i) hn (hr i) ha0 hl0 hl1
        le_rfl hak u hu) u hu
  have hlp : ∀ u : SobolevEuclidean (d + 1) 1 p Ω,
      eLpNorm (SobolevMultiIndex.fn (P₁ u)) p volume
        ≤ (ENNReal.ofReal M₀ + ∑ i, ENNReal.ofReal (M i) * B i)
          * eLpNorm (SobolevMultiIndex.fn u) p
            (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) := fun u ↦
    SobolevEuclidean.eLpNorm_fn_extension_le_of_ops (Ωc := fun i ↦ (c i).opensInterr (hr i))
      (fun _ ↦ rfl)
      (fun u ↦ SobolevMultiIndex.eLpNorm_fn_extendZeroMulL_le hα₀ (fun x ↦ (hM₀ x).1) u)
      (fun i w ↦ SobolevMultiIndex.eLpNorm_fn_extendZeroMulL_le (hα i) (fun x ↦ (hM i x).1) w)
      (fun i u ↦ hBu i u) hP₁ u
  have hKt : ENNReal.ofReal M₀ + ∑ i, ENNReal.ofReal (M i) * B i ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top,
      ENNReal.sum_ne_top.2 fun i _ ↦ ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hB i)⟩
  exact exists_extensionL_of_order_lp_of_ops hk P₁ hid hmem hKt hlp

set_option maxHeartbeats 400000 in
-- The heartbeat budget is raised because this proof assembles, in one declaration, the finite
-- atlas, the partition of unity of Brezis's Lemma 9.3, the radii `r_i` and the Vandermonde
-- coefficients, and every step unifies the surface spelling `SobolevMultiIndex ℝ (stdBasis _)`
-- of the Sobolev space with the backbone's `SobolevEuclidean`; the backbone's own
-- `SobolevEuclidean.exists_extensionL_of_order` does the same work inside `ExtensionHigher.lean`,
-- where these lemmas belong and where the unification is cheaper.
/-- **The order-`k` extension operator with its `L^p` bound on a `C^k` chart domain**:
`SobolevEuclidean.exists_extensionL_of_order` with the `L^p(ℝ^{d+1})` bound kept — the same
finite atlas, partition of unity, radii and Vandermonde coefficients. -/
private theorem exists_extensionL_of_order_lp {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} {k : ℕ} (hk : 1 ≤ k)
    (h1 : IsContDiffChartDomain k (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    ∃ (P : SobolevEuclidean (d + 1) k p Ω →L[ℝ] SobolevEuclidean (d + 1) k p ⊤) (C : ℝ),
      ∀ u : SobolevEuclidean (d + 1) k p Ω,
        SobolevMultiIndex.fn (P u)
            =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
            SobolevMultiIndex.fn u ∧
        ‖P u‖ ≤ C * ‖u‖ ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume ≤ ENNReal.ofReal C
          * eLpNorm (SobolevMultiIndex.fn u) p
            (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) := by
  obtain ⟨n, c, hc⟩ := h1.exists_finite_atlas hΓ
  have hKc : IsCompact (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_frontier hΓ
  obtain ⟨θ₀, θ, hθ₀, hθ, -, -, hsum, hθc, hθU, hθ₀K⟩ :=
    hKc.exists_contDiff_partitionOfUnity (fun i ↦ (c i).isOpen_U) hc
  choose r hr hθr using fun i ↦ (c i).exists_lt_one_subset_opensUr (hθc i) (hθU i)
  obtain ⟨a, l, hl0, hl1, ha0, hak⟩ := exists_vandermonde_coeffs_scales k hk
  have hθ₀κ : HasCompactSupport fun x ↦ θ₀ x - 1 := by
    have e : (fun x ↦ θ₀ x - 1) = -(∑ i, θ i) := by
      funext x
      rw [Pi.neg_apply, Finset.sum_apply]
      linarith [hsum x]
    rw [e]
    exact (HasCompactSupport.finset_sum fun i _ ↦ hθc i).neg
  have h := exists_extensionL_of_order_lp_of_atlas (p := p) hk c hθ₀ ⟨1, hθ₀κ⟩ hθ₀K hθ
    hθc hsum hr hθr ha0 hl0 hl1 hak
  exact h

/-- **Theorem 7.3.5** at order `k ≥ 1`, with the `L^p` bound of the extension: for a bounded
`C^k` domain `Ω ⊆ ℝ^{d+1}` (Definition 7.2.1) and `p ∈ [1, ∞]` there is a linear continuous
`E : W^{k,p}(Ω) → W^{k,p}(ℝ^{d+1})`, `Ev = v` in `Ω`, with both
`‖Ev‖_{W^{k,p}(ℝ^{d+1})} ≤ c ‖v‖_{W^{k,p}(Ω)}` and `‖Ev‖_{L^p(ℝ^{d+1})} ≤ c ‖v‖_{L^p(Ω)}`.

This is `theorem_7_3_5_order` with the second bound added, and it is the one clause of Stein's
universal extension theorem that the reflection construction does give beyond a single order: the
*same* operator is bounded at the orders `0` and `k` at once, because every piece of it — the zero
extensions with the cut-offs of the partition of unity, the two chart transports and the
higher-order reflection, a finite sum of dilations — is bounded on `L^p`, and the closed graph
theorem that lifts the order-one operator to order `k` does not change its function. What the
construction does *not* give is one operator for all `k` at once (the reflection coefficients
solve a Vandermonde system of order `k`) nor, as the backbone states it, one operator for all `p`
at once; see the `## Not formalized here` section of this module. Example 7.4.3 on a domain
(`example_7_4_3` of §7.4) is the consumer: it needs `‖Ev‖_{H^{d+1}}` and `‖Ev‖_{L²}` controlled
by `‖v‖_{H^{d+1}(Ω)}` and `‖v‖_{L²(Ω)}` simultaneously. -/
theorem theorem_7_3_5_order_lp {k : ℕ} (hk : 1 ≤ k) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} (hΩ : definition_7_2_1 {g | ContDiff ℝ k g} Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    ∃ E : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume →L[ℝ]
        SobolevMultiIndex ℝ (stdBasis (d + 1)) k p ⊤ volume,
      (∀ v, SobolevMultiIndex.fn (E v)
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] SobolevMultiIndex.fn v) ∧
      ∃ c : ℝ, (∀ v, ‖E v‖ ≤ c * ‖v‖) ∧
        ∀ v, eLpNorm (SobolevMultiIndex.fn (E v)) p volume ≤ ENNReal.ofReal c
          * eLpNorm (SobolevMultiIndex.fn v) p
            (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) := by
  have h1 : IsContDiffChartDomain k (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) :=
    ((definition_7_2_1_contDiffDomain k Ω).2 hΩ).isContDiffChartDomain
  have hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    hb.closure.subset frontier_subset_closure
  have h3 := exists_extensionL_of_order_lp (p := p) hk h1 hΓ
  obtain ⟨E, C, hE⟩ := h3
  exact ⟨E, fun v ↦ (hE v).1, C, fun v ↦ (hE v).2.1, fun v ↦ (hE v).2.2⟩


/-! #### The same operator at every exponent

The construction of `theorem_7_3_5_order` never mentions `p`: the finite atlas, the partition of
unity, the radii `r_i` and the Vandermonde coefficients `a, l` are chosen before any exponent is,
and every piece of the order-one operator — `SobolevMultiIndex.extendZeroMulL`,
`SobolevEuclidean.chartExtendLr` — is a *definition* parameterized by `p`, not an existential. What
the backbone's statements do not say is that the resulting operators, for two exponents, are the
same map on functions. Saying it needs a formula for the function of `chartExtendLr` on all of
`U_r`, not only on `U_r ∩ Ω` where `SobolevEuclidean.chartExtendLr_fn_ae_eq` leaves it; that is
`chartExtendLr_fn_formula` below, and it rests on `higherReflection_congr_ae`, the congruence of
the higher-order reflection under an almost-everywhere equality of its argument on `Q_{r,+}` — the
dilations `scaleLast (l j)` pull null sets of `Q_{r,+}` back to null sets of `Q_{r,−}`, which is
the third clause of `IsReflectionSet.exists_facts`. Both belong to
`Numlib/Analysis/Sobolev/ExtensionHigher.lean`. -/

/-- **The higher-order reflection is a congruence for almost-everywhere equality on `Q_{r,+}`**:
if `w = w'` almost everywhere on the positive half of the cylinder `Q_r`, then `P w = P w'`
almost everywhere on `Q_r`. On `{x_N > 0}` this is the hypothesis; on `{x_N < 0}` it is the
hypothesis transported along the dilations `scaleLast (l j)`
(`IsReflectionSet.exists_facts`, third clause), which map `Q_{r,−}` into `Q_{r,+}`; the hyperplane
`{x_N = 0}` is null (`ae_apply_last_ne_zero`). -/
private theorem higherReflection_congr_ae {m : ℕ} {a l : Fin m → ℝ} (hl : ∀ j, l j < 0)
    (hl1 : ∀ j, -1 ≤ l j) (r : ℝ) {w w' : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (h : w =ᵐ[volume.restrict (posHalf (EuclideanSpace.single (Fin.last d) (1 : ℝ))
      (cylinder d r) : Set (EuclideanSpace ℝ (Fin (d + 1))))] w') :
    higherReflection a l w
      =ᵐ[volume.restrict (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      higherReflection a l w' := by
  have : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩
  obtain ⟨-, -, -, -, htrans⟩ :=
    (isReflectionSet_cylinder hl hl1 r).exists_facts (F := ℝ) a 1
  have hneg : ∀ᵐ x ∂volume, x ∈ negHalf (cylinder d r) →
      ∀ j, w (scaleLast (l j) x) = w' (scaleLast (l j) x) :=
    (ae_restrict_iff' isOpen_negHalf'.measurableSet).1 (htrans h)
  have hpos : ∀ᵐ x ∂volume, x ∈ (posHalf (EuclideanSpace.single (Fin.last d) (1 : ℝ))
      (cylinder d r) : Set (EuclideanSpace ℝ (Fin (d + 1)))) → w x = w' x :=
    (ae_restrict_iff' (posHalf (EuclideanSpace.single (Fin.last d) (1 : ℝ))
      (cylinder d r)).isOpen.measurableSet).1 h
  filter_upwards [ae_restrict_of_ae hneg, ae_restrict_of_ae hpos,
    ae_restrict_of_ae (ae_apply_last_ne_zero (d := d)),
    ae_restrict_mem (cylinder d r).isOpen.measurableSet] with x hx1 hx2 hx0 hxc
  rcases lt_or_gt_of_ne hx0 with hlt | hgt
  · rw [higherReflection_of_neg a l hlt, higherReflection_of_neg a l hlt]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [hx1 ⟨hxc, hlt⟩ j]
  · rw [higherReflection_of_nonneg a l hgt.le, higherReflection_of_nonneg a l hgt.le]
    exact hx2 (mem_posHalf_last_iff.2 ⟨hxc, hgt⟩)

/-- **The function of the higher-order chart-local extension**, on all of `U_r`:
`w_i = P(u ∘ H) ∘ H⁻¹` for the higher-order reflection `P`.
`SobolevEuclidean.chartExtendLr_fn_ae_eq` gives only its restriction to `U_r ∩ Ω`, where it is
`u`; this is the formula that makes the operator visible at the level of functions, and hence
independent of the exponent. -/
private theorem chartExtendLr_fn_formula {n : WithTop ℕ∞} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} {m : ℕ} {a l : Fin m → ℝ}
    (c : ContDiffChart n (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (hn : 1 ≤ n) {r : ℝ}
    (hr : r < 1) (ha : ∑ j, a j = 1) (hl : ∀ j, l j < 0) (hl1 : ∀ j, -1 ≤ l j)
    (u : SobolevEuclidean (d + 1) 1 p Ω) :
    SobolevMultiIndex.fn (SobolevEuclidean.chartExtendLr p c hn hr ha hl hl1 u)
      =ᵐ[volume.restrict (c.opensUr hr : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      fun x ↦ higherReflection a l
        (fun y ↦ SobolevMultiIndex.fn u (c.toFun y)) (c.invFun x) := by
  have h6 : SobolevMultiIndex.fn (SobolevEuclidean.chartTransferLr p c hn hr
      (SobolevEuclidean.chartRestrictLr p c hr u))
      =ᵐ[volume.restrict (posHalf (EuclideanSpace.single (Fin.last d) (1 : ℝ))
        (cylinder d r) : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      fun y ↦ SobolevMultiIndex.fn u (c.toFun y) :=
    (SobolevEuclidean.fn_chartTransferLr p c hn hr _).trans
      ((c.exists_isDiffeoOnWithBoundedJacobian_posHalf_cylinder hr
        hn).choose_spec.ae_comp_restrict (SobolevEuclidean.fn_chartRestrictLr p c hr u))
  have hQ : SobolevMultiIndex.fn (SobolevEuclidean.cubeReflectLr p ha hl hl1
      (SobolevEuclidean.chartTransferLr p c hn hr (SobolevEuclidean.chartRestrictLr p c hr u)))
      =ᵐ[volume.restrict (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      higherReflection a l (fun y ↦ SobolevMultiIndex.fn u (c.toFun y)) :=
    (SobolevEuclidean.fn_cubeReflectLr p ha hl hl1 _).trans
      (higherReflection_congr_ae hl hl1 r h6)
  rw [SobolevEuclidean.chartExtendLr_apply]
  exact (SobolevEuclidean.fn_chartRetransferLr p c hn hr _).trans
    ((c.exists_isDiffeoOnWithBoundedJacobian_cylinder hr hn).choose_spec.symm.ae_comp_restrict hQ)

/-- **The function of one summand of the extension operator**: the zero extension of
`θ_i w_i` is `1_{U_{r_i}} · θ_i · (P(u ∘ H_i) ∘ H_i⁻¹)`, everywhere up to a null set of
`ℝ^{d+1}`. -/
private theorem fn_extendZeroMul_chartExtendLr {n : WithTop ℕ∞} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} {m : ℕ} {a l : Fin m → ℝ}
    (c : ContDiffChart n (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (hn : 1 ≤ n) {r : ℝ}
    (hr : r < 1) (ha : ∑ j, a j = 1) (hl : ∀ j, l j < 0) (hl1 : ∀ j, -1 ≤ l j)
    {θ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} (hθ : IsSobolevCutoff (c.opensUr hr) θ)
    (u : SobolevEuclidean (d + 1) 1 p Ω) :
    SobolevMultiIndex.fn (SobolevMultiIndex.extendZeroMulL ℝ (stdBasis (d + 1)) p volume hθ
        (SobolevEuclidean.chartExtendLr p c hn hr ha hl hl1 u))
      =ᵐ[volume] (c.opensUr hr : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator
        (fun y ↦ θ y • higherReflection a l (fun z ↦ SobolevMultiIndex.fn u (c.toFun z))
          (c.invFun y)) := by
  filter_upwards [SobolevMultiIndex.fn_extendZeroMulL hθ
      (SobolevEuclidean.chartExtendLr p c hn hr ha hl hl1 u),
    (ae_restrict_iff' (c.opensUr hr).isOpen.measurableSet).1
      (chartExtendLr_fn_formula c hn hr ha hl hl1 u)] with x hx1 hx2
  rw [hx1]
  by_cases hx : x ∈ (c.opensUr hr : Set (EuclideanSpace ℝ (Fin (d + 1))))
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, hx2 hx]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]

/-- **From an order-one operator with a function-level formula to the operator at order `k`**:
`SobolevEuclidean.exists_extensionL_of_order_of_ops` with the formula carried over, the closed
graph theorem not changing the function of the operator. -/
private theorem exists_extensionL_of_order_fn_of_ops {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} {k : ℕ} (hk : 1 ≤ k)
    (P₁ : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤)
    (hid : ∀ u, SobolevMultiIndex.fn (P₁ u)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] SobolevMultiIndex.fn u)
    (hmem : ∀ u : SobolevEuclidean (d + 1) 1 p Ω,
      MemSobolevMultiIndex (stdBasis (d + 1)) (SobolevMultiIndex.fn u) k p Ω volume →
      MemSobolevMultiIndex (stdBasis (d + 1)) (SobolevMultiIndex.fn (P₁ u)) k p ⊤ volume)
    {E : (EuclideanSpace ℝ (Fin (d + 1)) → ℝ) → EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hfn : ∀ u, SobolevMultiIndex.fn (P₁ u) =ᵐ[volume] E (SobolevMultiIndex.fn u)) :
    ∃ (P : SobolevEuclidean (d + 1) k p Ω →L[ℝ] SobolevEuclidean (d + 1) k p ⊤) (C : ℝ),
      ∀ u : SobolevEuclidean (d + 1) k p Ω,
        SobolevMultiIndex.fn (P u) =ᵐ[volume] E (SobolevMultiIndex.fn u) ∧
        SobolevMultiIndex.fn (P u)
          =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
          SobolevMultiIndex.fn u ∧
        ‖P u‖ ≤ C * ‖u‖ := by
  obtain ⟨Pk, hPk⟩ := SobolevMultiIndex.exists_continuousLinearMap_of_order hk P₁ fun u ↦
    hmem (SobolevMultiIndex.toLowerOrderL ℝ (stdBasis (d + 1)) p Ω volume hk u)
      (SobolevMultiIndex.memSobolevMultiIndex u)
  refine ⟨Pk, ‖Pk‖, fun u ↦ ⟨?_, Filter.EventuallyEq.trans
    (ae_restrict_of_ae_restrict_of_subset (subset_univ _) (hPk u)) (hid _), Pk.le_opNorm u⟩⟩
  have h4 : SobolevMultiIndex.fn
      (SobolevMultiIndex.toLowerOrderL ℝ (stdBasis (d + 1)) p Ω volume hk u)
      = SobolevMultiIndex.fn u := rfl
  refine (eventuallyEq_restrict_coe_top_iff.1 (hPk u)).trans ?_
  rw [← h4]
  exact hfn _

/-- **One extension operator for every exponent, over an explicit atlas**: the function-level
map
`E f = 1_Ω θ₀ f + ∑_i 1_{U_{r_i}} θ_i · (P(f ∘ H_i) ∘ H_i⁻¹)`
is built from the atlas, the partition of unity, the radii and the reflection coefficients alone,
and for every `p ∈ [1, ∞]` the order-`k` extension operator of `theorem_7_3_5_order` built from
that same data has `E` as its function. -/
private theorem exists_extensionL_of_order_uniform_of_atlas
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} {k n : ℕ} (hk : 1 ≤ k)
    (c : Fin n → ContDiffChart k (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    {θ₀ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} {θ : Fin n → EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hθ₀ : ContDiff ℝ ∞ θ₀) (hθ₀κ : ∃ κ : ℝ, HasCompactSupport fun x ↦ θ₀ x - κ)
    (hθ₀Γ : Disjoint (tsupport θ₀) (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (hθ : ∀ i, ContDiff ℝ ∞ (θ i)) (hθc : ∀ i, HasCompactSupport (θ i))
    (hsum : ∀ x, θ₀ x + ∑ i, θ i x = 1) {r : Fin n → ℝ} (hr : ∀ i, r i < 1)
    (hθr : ∀ i, tsupport (θ i) ⊆ (c i).opensUr (hr i)) {m : ℕ} {a l : Fin m → ℝ}
    (ha0 : ∑ j, a j = 1) (hl0 : ∀ j, l j < 0) (hl1 : ∀ j, -1 ≤ l j)
    (hak : ∀ i < k, ∑ j, a j * l j ^ i = 1) :
    ∃ E : (EuclideanSpace ℝ (Fin (d + 1)) → ℝ) → EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
      ∀ (p : ℝ≥0∞) (_ : Fact (1 ≤ p)),
        ∃ (P : SobolevEuclidean (d + 1) k p Ω →L[ℝ] SobolevEuclidean (d + 1) k p ⊤) (C : ℝ),
          ∀ u : SobolevEuclidean (d + 1) k p Ω,
            SobolevMultiIndex.fn (P u) =ᵐ[volume] E (SobolevMultiIndex.fn u) ∧
            SobolevMultiIndex.fn (P u)
              =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
              SobolevMultiIndex.fn u ∧
            ‖P u‖ ≤ C * ‖u‖ := by
  have hn : (1 : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by exact_mod_cast hk
  have hα₀ : IsSobolevCutoff Ω θ₀ :=
    IsSobolevCutoff.of_hasCompactSupport_sub hθ₀ hθ₀κ.choose_spec hθ₀Γ
  have hα : ∀ i, IsSobolevCutoff ((c i).opensUr (hr i)) (θ i) := fun i ↦
    IsSobolevCutoff.of_hasCompactSupport (hθ i) (hθc i) (hθr i)
  obtain ⟨E, hE⟩ :
      ∃ E : (EuclideanSpace ℝ (Fin (d + 1)) → ℝ) → EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
        E = fun f x ↦ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator
            (fun y ↦ θ₀ y • f y) x
          + ∑ i, ((c i).opensUr (hr i) : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator
              (fun y ↦ θ i y • higherReflection a l (fun z ↦ f ((c i).toFun z))
                ((c i).invFun y)) x := ⟨_, rfl⟩
  refine ⟨E, fun p hp ↦ ?_⟩
  obtain ⟨P₁, hP₁⟩ :
      ∃ P₁ : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤,
        ∀ u, P₁ u = SobolevMultiIndex.extendZeroMulL ℝ (stdBasis (d + 1)) p volume hα₀ u
          + ∑ i, SobolevMultiIndex.extendZeroMulL ℝ (stdBasis (d + 1)) p volume (hα i)
              (SobolevEuclidean.chartExtendLr p (c i) hn (hr i) ha0 hl0 hl1 u) :=
    ⟨SobolevMultiIndex.extendZeroMulL ℝ (stdBasis (d + 1)) p volume hα₀
        + ∑ i, (SobolevMultiIndex.extendZeroMulL ℝ (stdBasis (d + 1)) p volume (hα i)).comp
          (SobolevEuclidean.chartExtendLr p (c i) hn (hr i) ha0 hl0 hl1),
      fun u ↦ by
        simp only [_root_.add_apply, _root_.sum_apply, ContinuousLinearMap.comp_apply]⟩
  have hid : ∀ u, SobolevMultiIndex.fn (P₁ u)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      SobolevMultiIndex.fn u := fun u ↦
    SobolevEuclidean.fn_extension_ae_eq_of_ops (Ωc := fun i ↦ (c i).opensInterr (hr i))
      (fun _ ↦ rfl) (χ := fun _ ↦ 1) (fun x _ ↦ hsum x)
      (fun i x hx ↦ image_eq_zero_of_notMem_tsupport fun h ↦ hx (hθr i h))
      (fun u ↦ SobolevMultiIndex.fn_extendZeroMulL hα₀ u)
      (fun i w ↦ SobolevMultiIndex.fn_extendZeroMulL (hα i) w)
      (fun i u ↦ SobolevEuclidean.chartExtendLr_fn_ae_eq p (c i) hn (hr i) ha0 hl0 hl1 u)
      hP₁ u (Eventually.of_forall fun x ↦ (one_mul _).symm)
  have hmem : ∀ u : SobolevEuclidean (d + 1) 1 p Ω,
      MemSobolevMultiIndex (stdBasis (d + 1)) (SobolevMultiIndex.fn u) k p Ω volume →
      MemSobolevMultiIndex (stdBasis (d + 1)) (SobolevMultiIndex.fn (P₁ u)) k p ⊤ volume :=
    fun u hu ↦ SobolevEuclidean.extension_mem_of_ops
      (fun u ↦ SobolevMultiIndex.fn_extendZeroMulL hα₀ u)
      (fun i w ↦ SobolevMultiIndex.fn_extendZeroMulL (hα i) w) hP₁ hθ₀ hθ₀κ hθ₀Γ hθ hθc hθr
      (fun i u hu ↦ SobolevEuclidean.chartExtendLr_mem_of_order p (c i) hn (hr i) ha0 hl0 hl1
        le_rfl hak u hu) u hu
  have hfn : ∀ u, SobolevMultiIndex.fn (P₁ u) =ᵐ[volume] E (SobolevMultiIndex.fn u) := by
    intro u
    filter_upwards [SobolevEuclidean.fn_extension_of_ops hP₁ u,
      SobolevMultiIndex.fn_extendZeroMulL hα₀ u,
      ae_all_iff.2 fun i ↦ fn_extendZeroMul_chartExtendLr (c i) hn (hr i) ha0 hl0 hl1 (hα i) u]
      with x hx0 hx1 hx2
    rw [hE, hx0]
    simp only [Pi.add_apply, Finset.sum_apply, hx1]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ hx2 i
  exact exists_extensionL_of_order_fn_of_ops hk P₁ hid hmem hfn

set_option maxHeartbeats 400000 in
-- The heartbeat budget is raised for the same reason as in
-- `exists_extensionL_of_order_lp`: the finite atlas, the partition of unity, the radii and the
-- Vandermonde coefficients are assembled in one declaration, and every step unifies the surface
-- spelling of the Sobolev space with the backbone's.
/-- **One extension operator for every exponent, on a `C^k` chart domain**: the atlas and the
partition of unity of `SobolevEuclidean.exists_extensionL_of_order`, with the function-level
operator kept. -/
private theorem exists_extensionL_of_order_uniform
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} {k : ℕ} (hk : 1 ≤ k)
    (h1 : IsContDiffChartDomain k (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    ∃ E : (EuclideanSpace ℝ (Fin (d + 1)) → ℝ) → EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
      ∀ (p : ℝ≥0∞) (_ : Fact (1 ≤ p)),
        ∃ (P : SobolevEuclidean (d + 1) k p Ω →L[ℝ] SobolevEuclidean (d + 1) k p ⊤) (C : ℝ),
          ∀ u : SobolevEuclidean (d + 1) k p Ω,
            SobolevMultiIndex.fn (P u) =ᵐ[volume] E (SobolevMultiIndex.fn u) ∧
            SobolevMultiIndex.fn (P u)
              =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
              SobolevMultiIndex.fn u ∧
            ‖P u‖ ≤ C * ‖u‖ := by
  obtain ⟨n, c, hc⟩ := h1.exists_finite_atlas hΓ
  have hKc : IsCompact (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_frontier hΓ
  obtain ⟨θ₀, θ, hθ₀, hθ, -, -, hsum, hθc, hθU, hθ₀K⟩ :=
    hKc.exists_contDiff_partitionOfUnity (fun i ↦ (c i).isOpen_U) hc
  choose r hr hθr using fun i ↦ (c i).exists_lt_one_subset_opensUr (hθc i) (hθU i)
  obtain ⟨a, l, hl0, hl1, ha0, hak⟩ := exists_vandermonde_coeffs_scales k hk
  have hθ₀κ : HasCompactSupport fun x ↦ θ₀ x - 1 := by
    have e : (fun x ↦ θ₀ x - 1) = -(∑ i, θ i) := by
      funext x
      rw [Pi.neg_apply, Finset.sum_apply]
      linarith [hsum x]
    rw [e]
    exact (HasCompactSupport.finset_sum fun i _ ↦ hθc i).neg
  have h := exists_extensionL_of_order_uniform_of_atlas hk c hθ₀ ⟨1, hθ₀κ⟩ hθ₀K hθ
    hθc hsum hr hθr ha0 hl0 hl1 hak
  exact h

/-- **Theorem 7.3.5 at order `k`, one operator for every `p`** (the weakened form of the
universal extension theorem in the exponent): for a bounded `C^k` domain `Ω ⊆ ℝ^{d+1}`
(Definition 7.2.1) and `k ≥ 1` there is a *single* map `E` on functions such that, for every
`p ∈ [1, ∞]`, there is a bounded linear `E_p : W^{k,p}(Ω) → W^{k,p}(ℝ^{d+1})` whose function is
`E` applied to the function of its argument, with `E_p v = v` on `Ω` and
`‖E_p v‖ ≤ c ‖v‖`. In particular the operators of two exponents agree on the functions they share:
`E` is one operator, restricting to a bounded operator on each `W^{k,p}(Ω)`.

This is the clause of Stein's universal extension theorem that concerns the exponent;
`theorem_7_3_5_order_lp` is the clause that concerns the order (one operator bounded at the orders
`0` and `k` at once). What stays out of reach is one operator for every *order* `k` — the
reflection `∑_j a_j v(x', l_j x_N)` has coefficients solving a Vandermonde system of order `k` —
together with the smoothness of `Ev` off `closure Ω` and Lipschitz domains; the
`## Not formalized here` section of this module is the record.

`E` is the explicit map
`E f = 1_Ω θ₀ f + ∑_i 1_{U_{r_i}} θ_i · (P(f ∘ H_i) ∘ H_i⁻¹)`
of the proof of Theorem 9.7 with the higher-order reflection `P`, read at the level of functions;
the existential hides it only because the atlas and the partition of unity are themselves
existential. -/
theorem theorem_7_3_5_order_uniform {k : ℕ} (hk : 1 ≤ k)
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} (hΩ : definition_7_2_1 {g | ContDiff ℝ k g} Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    ∃ E : (EuclideanSpace ℝ (Fin (d + 1)) → ℝ) → EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
      ∀ (p : ℝ≥0∞) (_ : Fact (1 ≤ p)),
        ∃ (Ep : SobolevMultiIndex ℝ (stdBasis (d + 1)) k p Ω volume →L[ℝ]
            SobolevMultiIndex ℝ (stdBasis (d + 1)) k p ⊤ volume) (c : ℝ),
          ∀ v, SobolevMultiIndex.fn (Ep v) =ᵐ[volume] E (SobolevMultiIndex.fn v) ∧
            SobolevMultiIndex.fn (Ep v)
              =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
              SobolevMultiIndex.fn v ∧
            ‖Ep v‖ ≤ c * ‖v‖ := by
  have h1 : IsContDiffChartDomain k (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) :=
    ((definition_7_2_1_contDiffDomain k Ω).2 hΩ).isContDiffChartDomain
  have hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    hb.closure.subset frontier_subset_closure
  have h3 := exists_extensionL_of_order_uniform hk h1 hΓ
  exact h3

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

/-! ### Theorem 7.3.10: the trace operator -/

section Trace

variable {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **Theorem 7.3.10 (a), (b)** (the trace theorem) on a bounded `C¹` domain `Ω ⊆ ℝ^{d+1}`, for
`1 ≤ p < ∞`: the trace operator `γ : W^{1,p}(Ω) →L[ℝ] L^p(Γ)` — the backbone's
`IsContDiffDomain.traceL hΩ hb p hp`, continuous and linear by its type — satisfies
(a) `γ v = v|_Γ` whenever `v ∈ W^{1,p}(Ω) ∩ C(Ω̄)`, that is `γ v = ṽ` `σ`-almost everywhere on
`Γ` for every representative `ṽ` of `v` continuous on `closure Ω`, and
(b) `‖γ v‖_{L^p(Γ)} ≤ c ‖v‖_{W^{1,p}(Ω)}` for a constant `c > 0`. Clause (c), the compactness of
`γ`, is `theorem_7_3_10_compact`; the range `γ(W^{1,p}(Ω)) = W^{1−1/p,p}(Γ)` and the space
`H^{1/2}(Γ)` with the norm (7.3.2) are not formalized — Gagliardo’s theorem, on top of
boundary Sobolev spaces that do not depend on the patch system; the module doc’s
`## Not formalized here` section is the record.

The book states the theorem, without proof, for a Lipschitz domain; the formalization has the
bounded `C¹` domains of Definition 7.2.1 (`hΩ : IsContDiffDomain 1 Ω`, through
`definition_7_2_1_contDiffDomain`), on which the surface measure `σ = hΩ.boundaryMeasure hb` on
`Γ = ∂Ω` and the trace exist (`Numlib/Analysis/Sobolev/Boundary/`); `L^p(Γ)` is `Lp ℝ p σ`, `σ`
being a measure on the ambient space carried by `Γ`. The trace is Nečas's:
`∫_Γ |v|^p dσ ≤ C ‖v‖_{W^{1,p}}^p` for `v ∈ C¹(Ω̄)`, from the divergence theorem applied to
`|v|^p w` with a vector field `w` transversal to `Γ`, then extension by the density of `C^∞(Ω̄)`
(Theorem 7.3.2); (a) uses the uniform approximation of a function continuous up to the
boundary. -/
theorem theorem_7_3_10 {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (hΩ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    (∀ (v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 p Ω volume)
        (v' : EuclideanSpace ℝ (Fin (d + 1)) → ℝ),
        SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] v' →
        ContinuousOn v' (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) →
        (hΩ.traceL hb p hp v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) =ᵐ[hΩ.boundaryMeasure hb] v') ∧
      ∃ c : ℝ, 0 < c ∧ ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 p Ω volume,
        ‖hΩ.traceL hb p hp v‖ ≤ c * ‖v‖ :=
  ⟨fun v _ hv hc ↦ hΩ.traceL_ae_eq_of_continuousOn hb p hp v hv hc, (hΩ.traceL hb p hp).bound⟩

/-- **The meaning of Definition 7.2.9 through the trace, at `k = 1`** (the remark after
Definition 7.2.9: `W_0^{k,p}(Ω)` is "the space of all the functions `v` in `W^{k,p}(Ω)` with the
property that `∂^α v = 0` on `∂Ω` for `|α| ≤ k − 1`, the meaning of this statement being made
clear later after the trace theorems are presented"): on a bounded `C¹` domain `Ω ⊆ ℝ^{d+1}`, for
`1 ≤ p < ∞`, `W_0^{1,p}(Ω)` is the kernel of the trace `γ` of Theorem 7.3.10 —
`γ v = 0 ↔ v ∈ W_0^{1,p}(Ω)`.

Here `W_0^{1,p}(Ω)` is `SobolevEuclideanZero (d + 1) 1 p Ω`, the closure of the test functions in
the multi-index reading `SobolevEuclidean` of `W^{1,p}(Ω)`, on which the trace lives; the
identification with `definition_7_2_9 1 p Ω` (the closure in the bundled reading `Sobolev`) is
the unformalized comparison of the two readings already noted at `definition_7_2_9`. The backbone
is `IsContDiffDomain.traceL_eq_zero_iff_mem_zero` (`Numlib/Analysis/Sobolev/Boundary/Kernel.lean`):
`W_0^{1,p}(Ω) ⊆ ker γ` because test functions vanish on `∂Ω` and `γ` is continuous, and
`ker γ ⊆ W_0^{1,p}(Ω)` because, by Green's formula against a test function of `ℝ^{d+1}`
(`IsContDiffDomain.green_contDiff`), the extension of `v` by zero has the extensions by zero of
`∂ᵢ v` as weak derivatives, so lies in `W^{1,p}(ℝ^{d+1})`, which characterizes `W_0^{1,p}(Ω)` on a
`C¹` domain (Brezis, Proposition 9.18). The book's Lipschitz domain is out of scope and restated
as `C¹` (see `theorem_7_3_10`). -/
theorem theorem_7_3_10_kernel {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (hΩ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 p Ω volume) :
    hΩ.traceL hb p hp v = 0 ↔ v ∈ SobolevEuclideanZero (d + 1) 1 p Ω :=
  hΩ.traceL_eq_zero_iff_mem_zero hb p hp v

/-- **Theorem 7.3.10 (c)**: the trace operator `γ : W^{1,p}(Ω) → L^p(Γ)` of `theorem_7_3_10` is
compact — `IsCompactOperator` in Mathlib's sense, and in the book's sequential form: for every
bounded sequence `{v_n}` in `W^{1,p}(Ω)` there is a subsequence `{v_{n'}}` with `{γ v_{n'}}`
convergent in `L^p(Γ)`.

The hypothesis is `1 < p < ∞` where the book has `1 ≤ p < ∞`: at `p = 1` the statement is false,
the trace `W^{1,1}(Ω) → L¹(Γ)` being onto (Gagliardo), so not compact — an erratum of the book.
The domain is a bounded `C¹` domain, the book's Lipschitz domain being out of scope (see
`theorem_7_3_10`). The proof (`IsContDiffDomain.isCompactOperator_traceL`) is Nečas's inequality
in its sharp form `∫_Γ |γ v|^p ≤ C (‖v‖_{L^p}^p + ‖v‖_{L^p}^{p−1} ‖∇v‖_{L^p})`, applied to the
differences of a bounded sequence whose `L^p(Ω)` parts converge by the Rellich–Kondrachov theorem
(Theorem 7.3.8), so that the traces are Cauchy in `L^p(Γ)`; the sequential form is
`IsCompactOperator.isCompact_closure_image_closedBall` with `IsCompact.tendsto_subseq`. -/
theorem theorem_7_3_10_compact {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hΩ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    IsCompactOperator (hΩ.traceL hb p hp) ∧
      ∀ v : ℕ → SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 p Ω volume, (∃ M : ℝ, ∀ n, ‖v n‖ ≤ M) →
        ∃ (φ : ℕ → ℕ) (w : Lp ℝ p (hΩ.boundaryMeasure hb)), StrictMono φ ∧
          Tendsto (fun n ↦ hΩ.traceL hb p hp (v (φ n))) atTop (𝓝 w) := by
  have hK := hΩ.isCompactOperator_traceL hb p hp hp1
  refine ⟨hK, fun v ⟨M, hM⟩ ↦ ?_⟩
  obtain ⟨w, -, φ, hφ, hwφ⟩ :=
    (hK.isCompact_closure_image_closedBall M).tendsto_subseq
      (x := fun n ↦ hΩ.traceL hb p hp (v n))
      fun n ↦ subset_closure ⟨v n, mem_closedBall_zero_iff.2 (hM n), rfl⟩
  exact ⟨φ, w, hφ, hwφ⟩

/-! #### Theorem 7.3.10 on a triangulated polygon

The finite element chapters apply the trace theorem to polygonal domains, which are Lipschitz
but not `C¹`. The formalization's second reading of the book's Lipschitz domain is a plane domain
`Ω ⊆ ℝ²` with a triangulation `𝒯 : Triangulation Ω` (`Numlib/Geometry/Triangulation.lean`); the
boundary `Γ` then carries the arclength measure `σ = 𝒯.boundaryMeasure` of its boundary edges
and the outward normal `ν = 𝒯.outwardNormal` (`Numlib/Analysis/Sobolev/Boundary/Polygon.lean`),
and the trace `𝒯.traceL p hp : W^{1,p}(Ω) →L L^p(Γ)` is glued along the boundary edges from the
traces of Theorem 7.3.10 on the open triangles, each a bounded convex set with a transversal
field (`Numlib/Analysis/Sobolev/Boundary/PolygonTrace.lean`). -/

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

/-- **Theorem 7.3.10 (a), (b) on a triangulated polygon**: for a plane domain `Ω ⊆ ℝ²`
triangulated by `𝒯 : Triangulation Ω` and `1 ≤ p < ∞`, the trace operator
`γ = 𝒯.traceL p hp : W^{1,p}(Ω) →L[ℝ] L^p(Γ)` — continuous and linear by its type, with `L^p(Γ)`
the space `Lp ℝ p σ` of the arclength measure `σ = 𝒯.boundaryMeasure` on the boundary edges —
satisfies (a) `γ v = v|_Γ`, that is `γ v = ṽ` `σ`-almost everywhere, for every representative
`ṽ` of `v ∈ W^{1,p}(Ω)` continuous on `closure Ω`, and (b) `‖γ v‖_{L^p(Γ)} ≤ c ‖v‖_{W^{1,p}(Ω)}`
for a constant `c > 0`. Clause (c) is `theorem_7_3_10_polygon_compact`. The book's Lipschitz
domain is out of scope; a triangulated polygon is the finite element chapters' instance of it
(`theorem_7_3_10` is the `C¹` instance).

The operator is the sum over the boundary edges of the triangle's trace on the owning element,
extended by zero off the edge (`Triangulation.traceL`), and (a) is
`Triangulation.traceL_ae_eq_of_continuousOn`: on each boundary edge, Theorem 7.3.10 (a) on the
triangle. It is the trace of the trace family `𝒯.traceFamily hI` of a polygon without slits —
`hI : 𝒯.InteriorEdgesSubset`, the relative interior of every interior edge lying in `Ω` —
definitionally (`Triangulation.traceFamily_traceL`), the object the polygon consumers of §7.6,
§11 and §13 take; the no-slit hypothesis is what Green's formula needs
(`proposition_7_6_1_polygon`), while the clauses (a)–(c) hold for every triangulation. -/
theorem theorem_7_3_10_polygon {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    (∀ (v : SobolevMultiIndex ℝ (stdBasis 2) 1 p Ω volume) (v' : 𝔼₂ → ℝ),
        SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼₂)] v' →
        ContinuousOn v' (closure (Ω : Set 𝔼₂)) →
        (𝒯.traceL p hp v : 𝔼₂ → ℝ) =ᵐ[𝒯.boundaryMeasure] v') ∧
      ∃ c : ℝ, 0 < c ∧ ∀ v : SobolevMultiIndex ℝ (stdBasis 2) 1 p Ω volume,
        ‖𝒯.traceL p hp v‖ ≤ c * ‖v‖ :=
  ⟨fun v _ hv hc ↦ Triangulation.traceL_ae_eq_of_continuousOn hp v hv hc, (𝒯.traceL p hp).bound⟩

/-- **Theorem 7.3.10 (c) on a triangulated polygon**: the trace `γ = 𝒯.traceL p hp` of
`theorem_7_3_10_polygon` is compact for `1 < p < ∞` — `IsCompactOperator`, and in the book's
sequential form: every bounded sequence `{v_n}` of `W^{1,p}(Ω)` has a subsequence `{v_{n'}}` with
`{γ v_{n'}}` convergent in `L^p(Γ)`. As in `theorem_7_3_10_compact`, `1 < p` where the book has
`1 ≤ p` (an erratum: at `p = 1` the trace is onto `L¹(Γ)`). Each boundary edge's contribution is
compact because the triangle's trace is (`EuclideanSpace.isCompactOperator_triangleTraceL`,
Nečas's inequality with Rellich–Kondrachov on the triangle), and a finite sum of compact operators
is compact (`Triangulation.isCompactOperator_traceL`). -/
theorem theorem_7_3_10_polygon_compact {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) :
    IsCompactOperator (𝒯.traceL p hp) ∧
      ∀ v : ℕ → SobolevMultiIndex ℝ (stdBasis 2) 1 p Ω volume, (∃ M : ℝ, ∀ n, ‖v n‖ ≤ M) →
        ∃ (φ : ℕ → ℕ) (w : Lp ℝ p 𝒯.boundaryMeasure), StrictMono φ ∧
          Tendsto (fun n ↦ 𝒯.traceL p hp (v (φ n))) atTop (𝓝 w) := by
  have hK := 𝒯.isCompactOperator_traceL hp hp1
  refine ⟨hK, fun v ⟨M, hM⟩ ↦ ?_⟩
  obtain ⟨w, -, φ, hφ, hwφ⟩ :=
    (hK.isCompact_closure_image_closedBall M).tendsto_subseq
      (x := fun n ↦ 𝒯.traceL p hp (v n))
      fun n ↦ subset_closure ⟨v n, mem_closedBall_zero_iff.2 (hM n), rfl⟩
  exact ⟨φ, w, hφ, hwφ⟩

end Trace

/-! ### Theorem 7.3.11: the traces of `W^{2,p}(Ω)` and the normal derivative -/

section NormalTrace

open SobolevMultiIndex

variable {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **The trace `γ₀` of Theorem 7.3.11 at `s = 2`**, `γ₀ : W^{2,p}(Ω) →L[ℝ] L^p(Γ)` on a bounded
`C¹` domain, `1 ≤ p < ∞`: the trace `γ` of Theorem 7.3.10 applied after forgetting the
second-order derivatives (`SobolevMultiIndex.toLowerOrderL`), so that `γ₀ v = v|_Γ` for `v` with
a representative continuous on `closure Ω` (`theorem_7_3_11_trace₀_ae_eq`). Its target is
`L^p(Γ)` where the book has `W^{s−1/p,p}(Γ)` (`theorem_7_3_11`). -/
noncomputable def theorem_7_3_11_trace₀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (hΩ₁ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    SobolevMultiIndex ℝ (stdBasis (d + 1)) 2 p Ω volume →L[ℝ] Lp ℝ p (hΩ₁.boundaryMeasure hb) :=
  hΩ₁.traceL hb p hp ∘L toLowerOrderL ℝ (stdBasis (d + 1)) p Ω volume one_le_two

/-- The partial derivative `∂ᵢ : W^{2,p}(Ω) →L[ℝ] W^{1,p}(Ω)` of Theorem 7.3.11's normal
derivative, with its orders written `2` and `1`: `SobolevMultiIndex.partialDerivL` writes them
`k + 1` and `k`, and a sum of operators whose types agree only up to that arithmetic cannot be
rewritten with `ContinuousLinearMap.sum_apply`. -/
noncomputable def theorem_7_3_11_partialDerivL (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))) (i : Fin (d + 1)) :
    SobolevMultiIndex ℝ (stdBasis (d + 1)) 2 p Ω volume →L[ℝ]
      SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 p Ω volume :=
  partialDerivL ℝ (stdBasis (d + 1)) p Ω volume i

/-- Multiplication by the component `νᵢ` of the outward unit normal on `L^p(Γ)`, the operator
`BoundaryData.mulNormalL` of the boundary data of a bounded `C¹` domain, with the surface measure
written `hΩ₁.boundaryMeasure hb` (the backbone writes it `(hΩ₁.boundaryData hb).σ`, the same
measure by `IsContDiffDomain.boundaryData_σ`). -/
noncomputable def theorem_7_3_11_mulNormalL (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hΩ₁ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (i : Fin (d + 1)) :
    Lp ℝ p (hΩ₁.boundaryMeasure hb) →L[ℝ] Lp ℝ p (hΩ₁.boundaryMeasure hb) :=
  (hΩ₁.boundaryData hb).mulNormalL p i

/-- **The normal-derivative trace `γ₁` of Theorem 7.3.11 at `s = 2`**,
`γ₁ : W^{2,p}(Ω) →L[ℝ] L^p(Γ)` on a bounded `C¹` domain, `1 ≤ p < ∞`: the book's
`∂v/∂ν = ∑ᵢ (∂v/∂xᵢ) νᵢ` read through the trace of Theorem 7.3.10 on each first derivative,
`γ₁ v = ∑ᵢ νᵢ · γ(∂ᵢ v)` (`theorem_7_3_11_partialDerivL`, `theorem_7_3_11_mulNormalL`), so that
`γ₁ v = (∂v/∂ν)|_Γ` for `v` with a `C¹` representative (`theorem_7_3_11_trace₁_ae_eq`). At
`p = 2` it is the backbone's `BoundaryData.TraceFamily.normalTrace`
(`Numlib/Analysis/Sobolev/Boundary/Data.lean`), the same formula. Its target is `L^p(Γ)` where
the book has `W^{s−1−1/p,p}(Γ)` (`theorem_7_3_11`). -/
noncomputable def theorem_7_3_11_trace₁ {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (hΩ₁ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    SobolevMultiIndex ℝ (stdBasis (d + 1)) 2 p Ω volume →L[ℝ] Lp ℝ p (hΩ₁.boundaryMeasure hb) :=
  ∑ i, theorem_7_3_11_mulNormalL p hΩ₁ hb i ∘L hΩ₁.traceL hb p hp ∘L
    theorem_7_3_11_partialDerivL p Ω i

/-- **`γ₀ v = v|_Γ`** (Theorem 7.3.11, the defining property of `γ₀`): on a bounded `C¹` domain,
for `v ∈ W^{2,p}(Ω)` with a representative `ṽ` continuous on `closure Ω`, `γ₀ v = ṽ`
`σ`-almost everywhere on `Γ` — Theorem 7.3.10 (a) for the underlying `W^{1,p}` element. The
book asks `v ∈ C¹(Ω̄)`; continuity up to the boundary is what the trace sees. -/
theorem theorem_7_3_11_trace₀_ae_eq {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (hΩ₁ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 2 p Ω volume)
    {v' : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hv : fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] v')
    (hc : ContinuousOn v' (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    (theorem_7_3_11_trace₀ hp hΩ₁ hb v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
      =ᵐ[hΩ₁.boundaryMeasure hb] v' :=
  hΩ₁.traceL_ae_eq_of_continuousOn hb p hp _ hv hc

/-- **The trace of a first derivative**: on a bounded `C¹` domain, for `v ∈ W^{2,p}(Ω)` with a
`C¹` representative `ṽ` of the plane, the trace of `∂ᵢ v ∈ W^{1,p}(Ω)` is `∂ᵢ ṽ` on `Γ` —
Theorem 7.3.10 (a) for `∂ᵢ v`, whose continuous representative is `∂ᵢ ṽ`
(`SobolevEuclidean.weakDeriv_singleLE_ae_eq_fderiv`). -/
theorem theorem_7_3_11_traceL_partialDerivL_ae_eq {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (hΩ₁ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 2 p Ω volume)
    {v' : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hv : fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] v')
    (hv' : ContDiff ℝ 1 v') (i : Fin (d + 1)) :
    (hΩ₁.traceL hb p hp (theorem_7_3_11_partialDerivL p Ω i v) :
        EuclideanSpace ℝ (Fin (d + 1)) → ℝ) =ᵐ[hΩ₁.boundaryMeasure hb]
      fun x ↦ fderiv ℝ v' x (EuclideanSpace.single i 1) := by
  refine hΩ₁.traceL_ae_eq_of_continuousOn hb p hp _ ?_
    ((hv'.continuous_fderiv one_ne_zero).clm_apply continuous_const).continuousOn
  rw [theorem_7_3_11_partialDerivL, partialDerivL_apply, fn_partialDeriv]
  exact SobolevEuclidean.weakDeriv_singleLE_ae_eq_fderiv v hv hv' i

/-- **`γ₁ v = (∂v/∂ν)|_Γ`** (Theorem 7.3.11, the defining property of `γ₁`): on a bounded `C¹`
domain, for `v ∈ W^{2,p}(Ω)` with a `C¹` representative `ṽ` of the plane,
`γ₁ v = ∑ᵢ νᵢ ∂ᵢ ṽ` `σ`-almost everywhere on `Γ`, the classical normal derivative
`∂ṽ/∂ν = ∑ᵢ (∂ṽ/∂xᵢ) νᵢ` displayed before the theorem — termwise, the trace of `∂ᵢ v` is
`∂ᵢ ṽ` (`theorem_7_3_11_traceL_partialDerivL_ae_eq`) and multiplication by `νᵢ` acts pointwise
(`BoundaryData.coeFn_mulNormalL`). The book's `v ∈ W^{s,p}(Ω) ∩ C¹(Ω̄)` is read as a
representative `C¹` on `ℝ^{d+1}`, whose derivative is then continuous up to the boundary. -/
theorem theorem_7_3_11_trace₁_ae_eq {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (hΩ₁ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 2 p Ω volume)
    {v' : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hv : fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] v')
    (hv' : ContDiff ℝ 1 v') :
    (theorem_7_3_11_trace₁ hp hΩ₁ hb v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
      =ᵐ[hΩ₁.boundaryMeasure hb]
        fun x ↦ ∑ i, hΩ₁.outwardNormal hb x i * fderiv ℝ v' x (EuclideanSpace.single i 1) := by
  rw [theorem_7_3_11_trace₁, sum_apply]
  have h2 := Lp.coeFn_finsetSum (μ := hΩ₁.boundaryMeasure hb) Finset.univ fun i ↦
    (theorem_7_3_11_mulNormalL p hΩ₁ hb i ∘L hΩ₁.traceL hb p hp ∘L
      theorem_7_3_11_partialDerivL p Ω i) v
  have h3 : ∀ i : Fin (d + 1), (theorem_7_3_11_mulNormalL p hΩ₁ hb i
      (hΩ₁.traceL hb p hp (theorem_7_3_11_partialDerivL p Ω i v)) :
        EuclideanSpace ℝ (Fin (d + 1)) → ℝ) =ᵐ[hΩ₁.boundaryMeasure hb]
      fun x ↦ hΩ₁.outwardNormal hb x i * (hΩ₁.traceL hb p hp
        (theorem_7_3_11_partialDerivL p Ω i v) : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) x :=
    fun i ↦ (hΩ₁.boundaryData hb).coeFn_mulNormalL p i
      (hΩ₁.traceL hb p hp (theorem_7_3_11_partialDerivL p Ω i v))
  have hi := ae_all_iff.2 fun i ↦ theorem_7_3_11_traceL_partialDerivL_ae_eq hp hΩ₁ hb v hv hv' i
  filter_upwards [h2, ae_all_iff.2 h3, hi] with x hx2 hx3 hxi
  rw [hx2, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ ↦ by
    change (theorem_7_3_11_mulNormalL p hΩ₁ hb i (hΩ₁.traceL hb p hp
      (theorem_7_3_11_partialDerivL p Ω i v)) : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) x = _
    rw [hx3 i, hxi i]

/-- **Theorem 7.3.11, the `L^p` clause at `s = 2`**: on a bounded `C²` domain `Ω ⊆ ℝ^{d+1}` with
boundary `Γ`, for `1 ≤ p < ∞`, there are unique bounded linear maps
`γ₀ : W^{2,p}(Ω) →L[ℝ] L^p(Γ)` and `γ₁ : W^{2,p}(Ω) →L[ℝ] L^p(Γ)` such that `γ₀ v = v|_Γ` for
every `v` with a representative continuous on `closure Ω`, and `γ₁ v = (∂v/∂ν)|_Γ = ∑ᵢ νᵢ ∂ᵢ v`
for every `v` with a `C¹` representative — the book's `v ∈ W^{s,p}(Ω) ∩ C¹(Ω̄)`. The operators
are `theorem_7_3_11_trace₀` and `theorem_7_3_11_trace₁`; the four clauses are their two defining
properties (`theorem_7_3_11_trace₀_ae_eq`, `theorem_7_3_11_trace₁_ae_eq`) and the uniqueness of
each.

The hypotheses of the book are a bounded open set with a `C^{k,1}` boundary, `k ≥ s − 1 = 1`,
i.e. `C^{1,1}`, and targets `W^{s−1/p,p}(Γ)`, `W^{s−1−1/p,p}(Γ)` onto which `γ₀`, `γ₁` are
surjective; the formalization has the `L^p(Γ)` targets (the fractional spaces on `Γ`, the
surjectivity and the general `s`, `k` are not formalized — the module doc’s
`## Not formalized here`) and a `C²`
boundary. The existence and the two formulas hold on a bounded `C¹` domain (`hΩ₁`, on which the
surface measure `σ = hΩ₁.boundaryMeasure hb`, the normal `ν` and the trace of Theorem 7.3.10
live); the `C²` structure `hΩ : IsContDiffDomain 2 Ω` enters the uniqueness only, which rests on
the density in `W^{2,p}(Ω)` of the restrictions of `C_c^∞(ℝ^{d+1})` (Theorem 7.3.2 at order 2,
`theorem_7_3_2_higher`), available through the order-two extension operator of `C²` chart domains
(`IsSobolevExtensionDomainOfOrder.of_isContDiffChartDomain`); on such a `v` both `γ₀` and `γ₁`
are prescribed, and two continuous linear maps agreeing on a dense subspace agree. The `C¹`
structure is a separate hypothesis (it follows from the `C²` one, `IsContDiffDomain n Ω` being
monotone in `n`) so that the surface measure is stated on it. -/
theorem theorem_7_3_11 {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (hΩ₁ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΩ : IsContDiffDomain 2 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    ∃ γ₀ γ₁ : SobolevMultiIndex ℝ (stdBasis (d + 1)) 2 p Ω volume →L[ℝ]
        Lp ℝ p (hΩ₁.boundaryMeasure hb),
      (∀ (v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 2 p Ω volume)
          (v' : EuclideanSpace ℝ (Fin (d + 1)) → ℝ),
        fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] v' →
        ContinuousOn v' (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) →
        (γ₀ v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) =ᵐ[hΩ₁.boundaryMeasure hb] v')
      ∧ (∀ (v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 2 p Ω volume)
          (v' : EuclideanSpace ℝ (Fin (d + 1)) → ℝ),
        fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] v' →
        ContDiff ℝ 1 v' →
        (γ₁ v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) =ᵐ[hΩ₁.boundaryMeasure hb]
          fun x ↦ ∑ i, hΩ₁.outwardNormal hb x i * fderiv ℝ v' x (EuclideanSpace.single i 1))
      ∧ (∀ γ₀' : SobolevMultiIndex ℝ (stdBasis (d + 1)) 2 p Ω volume →L[ℝ]
            Lp ℝ p (hΩ₁.boundaryMeasure hb),
        (∀ (v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 2 p Ω volume)
            (v' : EuclideanSpace ℝ (Fin (d + 1)) → ℝ),
          fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] v' →
          ContinuousOn v' (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) →
          (γ₀' v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) =ᵐ[hΩ₁.boundaryMeasure hb] v') →
        γ₀' = γ₀)
      ∧ (∀ γ₁' : SobolevMultiIndex ℝ (stdBasis (d + 1)) 2 p Ω volume →L[ℝ]
            Lp ℝ p (hΩ₁.boundaryMeasure hb),
        (∀ (v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 2 p Ω volume)
            (v' : EuclideanSpace ℝ (Fin (d + 1)) → ℝ),
          fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] v' →
          ContDiff ℝ 1 v' →
          (γ₁' v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) =ᵐ[hΩ₁.boundaryMeasure hb]
            fun x ↦ ∑ i, hΩ₁.outwardNormal hb x i * fderiv ℝ v' x (EuclideanSpace.single i 1)) →
        γ₁' = γ₁) := by
  -- density of the elements with a smooth compactly supported representative in `W^{2,p}(Ω)`
  have hext : IsSobolevExtensionDomainOfOrder (d + 1) 2 p Ω :=
    IsSobolevExtensionDomainOfOrder.of_isContDiffChartDomain one_le_two hΩ.isContDiffChartDomain
      (hb.closure.subset frontier_subset_closure)
  have hdense : Dense {v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 2 p Ω volume |
      ∃ v' : EuclideanSpace ℝ (Fin (d + 1)) → ℝ, ContDiff ℝ ∞ v' ∧ HasCompactSupport v' ∧
        fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] v'} := by
    intro v
    have h := SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_order hp hext v
    obtain ⟨φ, hφ, hφc, w, hw, hwv⟩ := h
    exact mem_closure_iff_seq_limit.2 ⟨w, fun n ↦ ⟨φ n, hφ n, hφc n, hw n⟩, hwv⟩
  have hspan := hdense.mono (Submodule.subset_span (R := ℝ))
  refine ⟨theorem_7_3_11_trace₀ hp hΩ₁ hb, theorem_7_3_11_trace₁ hp hΩ₁ hb,
    fun v v' hv hc ↦ theorem_7_3_11_trace₀_ae_eq hp hΩ₁ hb v hv hc,
    fun v v' hv hv' ↦ theorem_7_3_11_trace₁_ae_eq hp hΩ₁ hb v hv hv', fun γ₀' h ↦ ?_,
    fun γ₁' h ↦ ?_⟩
  · refine ContinuousLinearMap.ext_on hspan ?_
    rintro v ⟨v', hv', -, hv⟩
    exact Lp.ext ((h v v' hv hv'.continuous.continuousOn).trans
      (theorem_7_3_11_trace₀_ae_eq hp hΩ₁ hb v hv hv'.continuous.continuousOn).symm)
  · refine ContinuousLinearMap.ext_on hspan ?_
    rintro v ⟨v', hv', -, hv⟩
    exact Lp.ext ((h v v' hv (hv'.of_le (by simp))).trans
      (theorem_7_3_11_trace₁_ae_eq hp hΩ₁ hb v hv (hv'.of_le (by simp))).symm)

end NormalTrace

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
through the trace). Here it is Poincaré's inequality on `W_0^{1,p}(Ω)`
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

/-! ### Examples 7.3.15 (boundary clause) and 7.3.16: Poincaré–Friedrichs through the trace -/

section PoincareFriedrichs

/-- `1 ≤ 2` for the exponent `p = 2` written in the backbone's form `((2 : ℝ≥0) : ℝ≥0∞)`, the
form in which the Euclidean theorems of `Numlib/Analysis/Sobolev/DenyLions.lean` (which take
`p : ℝ≥0`) return statements at `p = 2`. -/
instance fact_one_le_two_coe : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

local notation "𝟚" => ((2 : ℝ≥0) : ℝ≥0∞)

/-- An element of `H¹(Ω)` which is almost everywhere a polynomial of degree `≤ 0` is almost
everywhere a constant. -/
private theorem fn_ae_eq_const_of_degree_zero
    {v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume}
    (hv : ∃ q ∈ MvPolynomial.restrictTotalDegree (Fin (d + 1)) ℝ 0, SobolevMultiIndex.fn v
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        fun x ↦ MvPolynomial.eval (fun i ↦ x i) q) :
    ∃ c : ℝ, SobolevMultiIndex.fn v
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] fun _ ↦ c := by
  obtain ⟨q, hq, hvq⟩ := hv
  rw [MvPolynomial.mem_restrictTotalDegree, Nat.le_zero,
    MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hq
  refine ⟨q.coeff 0, hvq.trans (Eventually.of_forall fun x ↦ ?_)⟩
  change MvPolynomial.eval (fun i ↦ x i) q = q.coeff 0
  conv_lhs => rw [hq]
  rw [MvPolynomial.eval_C]

/-- **(H2)′ of Theorem 7.3.13 for the seminorm `∫_Γ |γ v| dσ`, without connectedness**: an
element of `H¹(Ω)` with `|v|_{1,Ω} = 0` and `∫_Γ |γ v| dσ = 0` is zero — its trace vanishes
(`IsContDiffDomain.traceL_ae_eq_zero_of_integral_abs_eq_zero`), so it lies in `H_0^1(Ω)` by the
kernel theorem and Poincaré's inequality applies
(`IsContDiffDomain.eq_zero_of_gradNorm_eq_zero_of_traceL_eq_zero`). -/
private theorem eq_zero_of_topSeminorm_eq_zero_of_integral_abs_traceL_eq_zero
    (hΩ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    {v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume}
    (hv : SobolevMultiIndex.topSeminorm ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume v = 0)
    (h0 : ∫ x, |(hΩ.traceL hb 𝟚 ENNReal.coe_ne_top v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) x|
      ∂(hΩ.boundaryMeasure hb) = 0) : v = 0 := by
  have hγ : hΩ.traceL hb 𝟚 ENNReal.coe_ne_top v = 0 :=
    Lp.ext ((hΩ.traceL_ae_eq_zero_of_integral_abs_eq_zero hb 𝟚 ENNReal.coe_ne_top h0).trans
      (Lp.coeFn_zero _ _ _).symm)
  refine hΩ.eq_zero_of_gradNorm_eq_zero_of_traceL_eq_zero hb 𝟚 ENNReal.coe_ne_top ?_ hγ
  rwa [← SobolevMultiIndex.topSeminorm_one_eq_gradNorm]

/-- **(H2) of Theorem 7.3.12 for the seminorm `f_1(v) = ∫_U |γ v| dσ`** on a boundary piece `U` of
positive surface measure: an element of `H¹(Ω)` which is almost everywhere a polynomial of degree
`≤ 0` and has `f_1(v) = 0` is zero. -/
private theorem eq_zero_of_degree_zero_of_setIntegral_abs_traceL_eq_zero
    (hΩ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    {U : Set (EuclideanSpace ℝ (Fin (d + 1)))} (hU : 0 < hΩ.boundaryMeasure hb U)
    {f : Seminorm ℝ (SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume)}
    (hf : ∀ v, f v = ∫ x in U, |(hΩ.traceL hb 𝟚 ENNReal.coe_ne_top v :
        EuclideanSpace ℝ (Fin (d + 1)) → ℝ) x| ∂(hΩ.boundaryMeasure hb))
    (v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume)
    (hv : ∃ q ∈ MvPolynomial.restrictTotalDegree (Fin (d + 1)) ℝ 0, SobolevMultiIndex.fn v
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
          fun x ↦ MvPolynomial.eval (fun i ↦ x i) q)
    (hfv : ∀ _ : Unit, f v = 0) : v = 0 := by
  obtain ⟨c, hvc⟩ := fn_ae_eq_const_of_degree_zero hv
  refine hΩ.eq_zero_of_traceL_integral_abs_eq_zero hb 𝟚 ENNReal.coe_ne_top hU hvc ?_
  rw [← hf]
  exact hfv ()

/-- **Example 7.3.15, the boundary clause**, on a bounded `C¹` domain `Ω ⊆ ℝ^{d+1}`: with
`Γ = ∂Ω`, its surface measure `σ` and the trace `γ : H¹(Ω) → L²(Γ)` of Theorem 7.3.10, there is
a constant `c > 0`, depending only on `Ω`, such that
`‖v‖_{1,Ω} ≤ c (|v|_{1,Ω} + ‖v‖_{L¹(Γ)})` for all `v ∈ H¹(Ω)`, where `‖v‖_{L¹(Γ)} = ∫_Γ |γ v| dσ`.
This is Theorem 7.3.13 with `k = 1`, `p = 2`, `J = 1` and `f_1(v) = ∫_Γ |v| ds`: (H1) is the
boundedness of the trace, and (H2)′ — `|v|_{1,Ω} = 0` and `∫_Γ |γ v| dσ = 0` force `v = 0` —
holds without any connectedness of `Ω`: a vanishing `∫_Γ |γ v| dσ` means `γ v = 0`, so
`v ∈ H_0^1(Ω)` by the kernel theorem (`theorem_7_3_10_kernel`,
`IsContDiffDomain.mem_zero_of_traceL_eq_zero`), and Poincaré's inequality on `H_0^1(Ω)`
(`SobolevEuclideanZero.norm_le_gradNorm`, the inequality (7.3.10) of `example_7_3_15`) with
`|v|_{1,Ω} = 0` gives `v = 0`. The `H_0^1` clause (7.3.10), the Poincaré–Friedrichs inequality
itself, is `example_7_3_15`, proved directly.

The book's hypothesis is a bounded Lipschitz domain, which is out of scope; the formalization has
the bounded `C¹` domains of Definition 7.2.1, on which the trace exists. -/
theorem example_7_3_15_boundary
    (hΩ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume,
      ‖v‖ ≤ c * (SobolevMultiIndex.topSeminorm ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume v
        + ∫ x, |(hΩ.traceL hb 𝟚 ENNReal.coe_ne_top v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) x|
          ∂(hΩ.boundaryMeasure hb)) := by
  have hΩ' : IsSobolevExtensionDomain (d + 1) 𝟚 Ω :=
    IsSobolevExtensionDomain.of_isContDiffDomain hΩ (hb.closure.subset frontier_subset_closure)
  -- the seminorm `f_1(v) = ∫_Γ |γ v| dσ` and (H1)
  obtain ⟨f, hf, h1⟩ : ∃ f : Seminorm ℝ (SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume),
      (∀ v, f v = ∫ x in univ, |(hΩ.traceL hb 𝟚 ENNReal.coe_ne_top v :
        EuclideanSpace ℝ (Fin (d + 1)) → ℝ) x| ∂(hΩ.boundaryMeasure hb)) ∧
      ∃ c : ℝ, ∀ v, f v ≤ c * ‖v‖ :=
    ⟨absIntegralSeminorm (hΩ.traceL hb 𝟚 ENNReal.coe_ne_top) univ,
      fun v ↦ absIntegralSeminorm_apply _ _ v,
      exists_absIntegralSeminorm_le (hΩ.traceL hb 𝟚 ENNReal.coe_ne_top) univ⟩
  obtain ⟨c, hc1⟩ := h1
  -- (H2)′, through Green's formula on the zero extension
  have h2 : ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume,
      SobolevMultiIndex.topSeminorm ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume v = 0 →
        (∀ _ : Unit, f v = 0) → v = 0 := by
    intro v hv hfv
    have h0 := hfv ()
    simp only [hf, Measure.restrict_univ] at h0
    exact eq_zero_of_topSeminorm_eq_zero_of_integral_abs_traceL_eq_zero hΩ hb hv h0
  have h := theorem_7_3_13 (k := 0) hΩ' hb (fun _ : Unit ↦ f) ⟨c, fun _ v ↦ hc1 v⟩ h2
  obtain ⟨⟨-, c₁, c₂, hc₁, -, hle⟩, -⟩ := h
  refine ⟨c₁⁻¹, inv_pos.2 hc₁, fun v ↦ ?_⟩
  have key := (hle v).1
  simp only [equation_7_3_3, Fintype.sum_unique, hf, Measure.restrict_univ] at key
  rw [← div_eq_inv_mul, le_div_iff₀' hc₁]
  exact key

/-- **The inequality of Example 7.3.16**: on a bounded connected `C¹` domain, for an open `U`
meeting `∂Ω` and `f_1(v) = ∫_U |γ v| dσ`, Theorem 7.3.12 with `k = 1`, `p = 2`, `J = 1` gives
`‖v‖_{1,Ω} ≤ c (|v|_{1,Ω} + f_1(v))` on `H¹(Ω)`. -/
private theorem exists_norm_le_topSeminorm_add_setIntegral_abs_traceL
    (hΩ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hc : IsPreconnected (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    {U : Set (EuclideanSpace ℝ (Fin (d + 1)))} (hU : IsOpen U)
    (hne : (U ∩ frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))).Nonempty) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume,
      ‖v‖ ≤ c * (SobolevMultiIndex.topSeminorm ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume v
        + ∫ x in U, |(hΩ.traceL hb 𝟚 ENNReal.coe_ne_top v :
          EuclideanSpace ℝ (Fin (d + 1)) → ℝ) x| ∂(hΩ.boundaryMeasure hb)) := by
  have hΩ' : IsSobolevExtensionDomain (d + 1) 𝟚 Ω :=
    IsSobolevExtensionDomain.of_isContDiffDomain hΩ (hb.closure.subset frontier_subset_closure)
  obtain ⟨f, hf, h1⟩ : ∃ f : Seminorm ℝ (SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume),
      (∀ v, f v = ∫ x in U, |(hΩ.traceL hb 𝟚 ENNReal.coe_ne_top v :
        EuclideanSpace ℝ (Fin (d + 1)) → ℝ) x| ∂(hΩ.boundaryMeasure hb)) ∧
      ∃ c : ℝ, ∀ v, f v ≤ c * ‖v‖ :=
    ⟨absIntegralSeminorm (hΩ.traceL hb 𝟚 ENNReal.coe_ne_top) U,
      fun v ↦ absIntegralSeminorm_apply _ _ v,
      exists_absIntegralSeminorm_le (hΩ.traceL hb 𝟚 ENNReal.coe_ne_top) U⟩
  obtain ⟨c, hc1⟩ := h1
  have h := theorem_7_3_12 (k := 0) hΩ' hb hc (fun _ : Unit ↦ f) ⟨c, fun _ v ↦ hc1 v⟩
    (eq_zero_of_degree_zero_of_setIntegral_abs_traceL_eq_zero hΩ hb
      (hΩ.boundaryMeasure_pos_of_isOpen hb hU hne) hf)
  obtain ⟨⟨-, c₁, c₂, hc₁, -, hle⟩, -⟩ := h
  refine ⟨c₁⁻¹, inv_pos.2 hc₁, fun v ↦ ?_⟩
  have key := (hle v).1
  simp only [equation_7_3_3, Fintype.sum_unique, hf] at key
  rw [← div_eq_inv_mul, le_div_iff₀' hc₁]
  exact key

/-- **Example 7.3.16**, on a bounded connected `C¹` domain `Ω ⊆ ℝ^{d+1}` (the book's Lipschitz
domain, out of scope, restated as `C¹`; see `theorem_7_3_10`): let `Γ_0` be an open non-empty
subset of the boundary `Γ` — here `Γ_0 = U ∩ Γ` for an open `U ⊆ ℝ^{d+1}` meeting `Γ`, every
relatively open subset of `Γ` being of this form — with the surface measure `σ` and the trace
`γ : H¹(Ω) → L²(Γ)` of Theorem 7.3.10. Then there is a constant `c > 0`, depending only on `Ω`
(and `Γ_0`), such that `‖v‖_{1,Ω} ≤ c (|v|_{1,Ω} + ‖v‖_{L¹(Γ_0)})` for all `v ∈ H¹(Ω)`, where
`‖v‖_{L¹(Γ_0)} = ∫_U |γ v| dσ`; therefore `‖v‖_{1,Ω} ≤ c |v|_{1,Ω}` for all
`v ∈ H^1_{Γ_0}(Ω) = {v ∈ H¹(Ω) : v = 0 a.e. on Γ_0}`, "`v = 0` a.e. on `Γ_0`" being
`γ v = 0` `σ`-almost everywhere on `U` — the Poincaré–Friedrichs inequality under a mixed
boundary condition.

The inequality is Theorem 7.3.12 with `k = 1`, `p = 2`, `J = 1` and `f_1(v) = ∫_{Γ_0} |v| ds`:
(H1) is the boundedness of the trace, and (H2) — a constant `v` with `f_1(v) = 0` is zero —
holds because the trace of a constant is that constant (Theorem 7.3.10 (a)) and
`σ(Γ_0) > 0` (`IsContDiffDomain.boundaryMeasure_pos_of_isOpen`). -/
theorem example_7_3_16
    (hΩ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hc : IsPreconnected (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    {U : Set (EuclideanSpace ℝ (Fin (d + 1)))} (hU : IsOpen U)
    (hne : (U ∩ frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))).Nonempty) :
    ∃ c : ℝ, 0 < c ∧
      (∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume,
        ‖v‖ ≤ c * (SobolevMultiIndex.topSeminorm ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume v
          + ∫ x in U, |(hΩ.traceL hb 𝟚 ENNReal.coe_ne_top v :
            EuclideanSpace ℝ (Fin (d + 1)) → ℝ) x| ∂(hΩ.boundaryMeasure hb))) ∧
      ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume,
        (hΩ.traceL hb 𝟚 ENNReal.coe_ne_top v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
          =ᵐ[(hΩ.boundaryMeasure hb).restrict U] 0 →
        ‖v‖ ≤ c * SobolevMultiIndex.topSeminorm ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume v := by
  obtain ⟨c, hc0, key⟩ :=
    exists_norm_le_topSeminorm_add_setIntegral_abs_traceL hΩ hb hc hU hne
  refine ⟨c, hc0, key, fun v hv ↦ ?_⟩
  have h0 : ∫ x in U, |(hΩ.traceL hb 𝟚 ENNReal.coe_ne_top v :
      EuclideanSpace ℝ (Fin (d + 1)) → ℝ) x| ∂(hΩ.boundaryMeasure hb) = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hv] with x hx
    rw [hx, Pi.zero_apply, abs_zero]
  have hv' := key v
  simp only [h0, add_zero] at hv'
  exact hv'

end PoincareFriedrichs


/-! ### §7.3.6: the Sobolev quotient space -/

section Quotient

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

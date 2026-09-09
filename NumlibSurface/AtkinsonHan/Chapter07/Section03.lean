import Numlib.Analysis.Normed.Operator.Embedding
import NumlibSurface.AtkinsonHan.Chapter07.Section02

/-!
# Atkinson–Han §7.3: continuous and compact embeddings, and the density of `C_0^∞(Ω)`

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §7.3.

Two of the section's results are here. Definition 7.3.6 is the vocabulary of §7.3.3, and lives in
`Numlib/Analysis/Normed/Operator/Embedding.lean`: `IsContinuousEmbedding ι` is `V ↪ W`, the
injective linear `ι : V → W` with `‖ι v‖_W ≤ c ‖v‖_V` (7.3.1), and `IsCompactEmbedding ι` is
`V ↪↪ W`, that together with the book's compactness — every bounded sequence of `V` has a
subsequence whose image converges in `W`. `definition_7_3_6` and `definition_7_3_6_compact` are the
two under the book's number, and `isCompactEmbedding_iff_isCompactOperator` identifies the second
with Mathlib's `IsCompactOperator` on the inclusion, which is what makes the compact-operator
theory available to it. Theorem 7.3.3, that every `v ∈ W_0^{k,p}(Ω)` is the `W^{k,p}(Ω)` limit of a
sequence in `C_0^∞(Ω)`, is here too: Definition 7.2.9 is formalized as the closure of the image of
`C_0^∞(Ω)` in `W^{k,p}(Ω)`, so the theorem is that closure read sequentially.

Everything else in §7.3 is out of reach, and this is the section that blocks the rest of the book.
Theorems 7.3.1 (Meyers–Serrin) and 7.3.2 (Calderón–Stein) are the density of `C^∞(Ω)` and of
`C^∞(closure Ω)`; Theorem 7.3.4 is the whole-space case of the first; Theorem 7.3.5 is Stein's
extension operator; Theorems 7.3.7–7.3.9 are the Sobolev embeddings and Rellich–Kondrachov;
Theorems 7.3.10 and 7.3.11 are the trace and the generalized normal derivative; and
Theorems 7.3.12–7.3.14, Examples 7.3.15–7.3.16, Theorem 7.3.17 and Corollary 7.3.18 are the
Deny–Lions norm equivalences, Poincaré–Friedrichs and Bramble–Hilbert, each proved in the book by a
compactness contradiction that uses the compact embedding of Theorem 7.3.9. Mathlib has none of
this: no density theory for a Sobolev space on an open set, no extension operator, no
Gagliardo–Nirenberg–Sobolev on a domain (`Mathlib/Analysis/Calculus/SobolevInequality.lean` covers
only compactly supported `C^1` functions on the whole space), no Rellich–Kondrachov, and no surface
measure on a Lipschitz boundary, so `L^p(Γ)` and the trace are not even statable. The book itself
states almost all of §7.3.1–§7.3.4 without proof.
-/

open Filter MeasureTheory Set TopologicalSpace

open scoped Distributions ENNReal Topology

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

end AtkinsonHan.Chapter07

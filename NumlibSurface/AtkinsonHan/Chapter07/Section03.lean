import Numlib.Analysis.Normed.Operator.Embedding
import Numlib.Analysis.Sobolev.Density
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

Everything else in §7.3 is out of reach, and this is the section that blocks the rest of the book.
Theorem 7.3.2 (Calderón–Stein) is the density of `C^∞(closure Ω)` on a Lipschitz domain, which is
smoothness up to the boundary and needs boundary charts; Theorem 7.3.5 is Stein's extension
operator; Theorems 7.3.7–7.3.9 are the Sobolev embeddings and Rellich–Kondrachov;
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

open scoped ContDiff Distributions ENNReal Topology

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

end AtkinsonHan.Chapter07

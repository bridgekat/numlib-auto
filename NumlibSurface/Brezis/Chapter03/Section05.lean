import Mathlib.Topology.Sequences
import Numlib.Analysis.Normed.Module.Reflexive.EberleinSmulian
import Numlib.Analysis.Normed.Module.Reflexive.Kakutani
import Numlib.Analysis.Normed.Operator.Unbounded.Reflexive
import NumlibSurface.Brezis.Chapter01.Section03
import NumlibSurface.Brezis.Chapter03.Section04

/-!
# Brezis §3.5: reflexive spaces

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §3.5, over a real Banach space `E`. Reflexivity is the
book's Definition `IsReflexive E` (the canonical injection `J = inclusionInDoubleDual ℝ E` of
§1.3 is onto), identified with the backbone's class `NormedSpace.IsReflexive ℝ E` by
`isReflexive_iff`; "compact in `σ(E, E*)`" is `IsCompact (toWeakSpace ℝ E '' s)`. Theorem 3.17
(Kakutani), Lemmas 3.3–3.4, Remark 15 and Corollaries 3.21–3.22 are the backbone
`Numlib/Analysis/Normed/Module/Reflexive/Kakutani`; Theorem 3.18 and Proposition 3.20 are
`Numlib/Analysis/Normed/Module/Reflexive`; Theorem 3.19 (Eberlein–Šmulian, Problem 10) is
`Reflexive/EberleinSmulian`; Theorem 3.24 is `Numlib/Analysis/Normed/Operator/Unbounded/Reflexive`
over chapter 2's Banach adjoint `LinearPMap.strongDualAdjoint`; Corollary 3.23 is proved here
from Corollaries 3.22 and 3.9 by the book's argument, with `φ : E → EReal` as in chapter 1.

The book's Definition is made for a Banach space; the surface definition `IsReflexive E` asks
no completeness (a reflexive normed space is complete, `NormedSpace.completeSpace_of_isReflexive`),
so that Proposition 3.20 can be stated for a closed subspace `M` without supplying its
completeness by hand. The theorems carry the book's `[CompleteSpace E]`.

## Main results

* `IsReflexive`, `isReflexive_iff` — the Definition and the bridge to the backbone class.
* `remark_3_13_finiteDimensional`, `remark_3_13_hilbert` — finite-dimensional spaces and
  Hilbert spaces are reflexive.
* `theorem_3_17_mp`, `theorem_3_17_mpr`, `theorem_3_17` — Kakutani: reflexive iff `B_E` is
  weakly compact; `lemma_3_3` (Helly), `lemma_3_4`, `lemma_3_4_dense` (Goldstine),
  `remark_3_15`.
* `theorem_3_18`, `theorem_3_19` — bounded sequences have weakly convergent subsequences iff
  reflexive (Eberlein–Šmulian for the converse); `remark_3_17`.
* `proposition_3_20`, `corollary_3_21`, `corollary_3_22`, `corollary_3_23` — closed subspaces,
  the dual, bounded closed convex sets, and the existence of a minimizer.
* `theorem_3_24_a`, `theorem_3_24_b` — `D(A*)` is dense and `A** = A` between reflexive spaces.

Remarks 14, 16, 18 are discussion; Remark 13's `L^p`, `ℓ^p`, `L¹`, `L^∞`, `C(K)` clauses are
chapters 4 and 11; Remark 17 (ii)–(iii) are not stated.
-/

open Bornology Filter Metric Set Topology NormedSpace

namespace Brezis.Chapter03

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-! ### The Definition -/

/-- **The Definition of §3.5.** `E` is reflexive if the canonical injection `J : E → E**` of
§1.3 is surjective, `J(E) = E**`. -/
def IsReflexive (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  Function.Surjective (inclusionInDoubleDual ℝ E)

/-- The book's Definition is the backbone's class `NormedSpace.IsReflexive ℝ E`. -/
theorem isReflexive_iff : IsReflexive E ↔ NormedSpace.IsReflexive ℝ E :=
  ⟨fun h => ⟨h⟩, fun _ => NormedSpace.surjective_inclusionInDoubleDual⟩

/-- **Remark 13, first claim.** Finite-dimensional spaces are reflexive
(`dim E = dim E* = dim E**`). -/
theorem remark_3_13_finiteDimensional [CompleteSpace E] [FiniteDimensional ℝ E] :
    IsReflexive E :=
  isReflexive_iff.2 inferInstance

/-- **Remark 13, "in Chapter 5 we shall see that Hilbert spaces are reflexive".** -/
theorem remark_3_13_hilbert {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] : IsReflexive H :=
  isReflexive_iff.2 inferInstance

/-! ### Kakutani's theorem -/

/-- **Theorem 3.17 (Kakutani), "only if".** If `E` is reflexive then `B_E = {x | ‖x‖ ≤ 1}` is
compact in the weak topology `σ(E, E*)`. -/
theorem theorem_3_17_mp [CompleteSpace E] (h : IsReflexive E) :
    IsCompact (toWeakSpace ℝ E '' closedBall (0 : E) 1) := by
  have := isReflexive_iff.1 h
  exact NormedSpace.isCompact_image_toWeakSpace_closedBall 1

/-- **Theorem 3.17 (Kakutani), "if".** If `B_E` is compact in `σ(E, E*)` then `E` is
reflexive. -/
theorem theorem_3_17_mpr [CompleteSpace E]
    (h : IsCompact (toWeakSpace ℝ E '' closedBall (0 : E) 1)) : IsReflexive E :=
  isReflexive_iff.2 (NormedSpace.isReflexive_of_isCompact_image_toWeakSpace_closedBall h)

/-- **Theorem 3.17 (Kakutani).** A Banach space `E` is reflexive iff `B_E` is compact in the
weak topology `σ(E, E*)`. -/
theorem theorem_3_17 [CompleteSpace E] :
    IsReflexive E ↔ IsCompact (toWeakSpace ℝ E '' closedBall (0 : E) 1) :=
  ⟨theorem_3_17_mp, theorem_3_17_mpr⟩

/-- **Lemma 3.3 (Helly).** Let `f₁, …, f_k ∈ E*` and `γ₁, …, γ_k ∈ ℝ`. The following are
equivalent: (i) for every `ε > 0` there is `x_ε ∈ E` with `‖x_ε‖ ≤ 1` and
`|⟨fᵢ, x_ε⟩ - γᵢ| < ε` for all `i`; (ii) `|∑ βᵢ γᵢ| ≤ ‖∑ βᵢ fᵢ‖` for all `β₁, …, β_k ∈ ℝ`. -/
theorem lemma_3_3 [CompleteSpace E] {k : ℕ} (f : Fin k → StrongDual ℝ E) (γ : Fin k → ℝ) :
    (∀ ε > 0, ∃ x : E, ‖x‖ ≤ 1 ∧ ∀ i, |f i x - γ i| < ε) ↔
      ∀ β : Fin k → ℝ, |∑ i, β i * γ i| ≤ ‖∑ i, β i • f i‖ :=
  NormedSpace.helly_iff f γ

/-- **Lemma 3.4 (Goldstine).** `J(B_E)` is dense in `B_{E**}` for the topology
`σ(E**, E*)`. -/
theorem lemma_3_4 [CompleteSpace E] :
    closure ((StrongDual.toWeakDual ∘ inclusionInDoubleDual ℝ E) '' closedBall (0 : E) 1) =
      WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ (StrongDual ℝ E)) 1 :=
  NormedSpace.goldstine

/-- **Lemma 3.4 (Goldstine), "consequently".** `J(E)` is dense in `E**` for the topology
`σ(E**, E*)`. -/
theorem lemma_3_4_dense [CompleteSpace E] :
    DenseRange (StrongDual.toWeakDual ∘ inclusionInDoubleDual ℝ E) :=
  NormedSpace.denseRange_toWeakDual_inclusionInDoubleDual

/-- **Remark 15.** `J(B_E)` is closed in `E**` for the strong topology; consequently it is not
strongly dense in `B_{E**}` unless `J(B_E) = B_{E**}`, i.e. `E` is reflexive. -/
theorem remark_3_15 [CompleteSpace E] :
    IsClosed (inclusionInDoubleDual ℝ E '' closedBall (0 : E) 1) ∧
      (closure (inclusionInDoubleDual ℝ E '' closedBall (0 : E) 1) =
        closedBall (0 : StrongDual ℝ (StrongDual ℝ E)) 1 → IsReflexive E) := by
  refine ⟨NormedSpace.isClosed_image_inclusionInDoubleDual_closedBall 1, fun hdense ξ => ?_⟩
  rw [(NormedSpace.isClosed_image_inclusionInDoubleDual_closedBall 1).closure_eq] at hdense
  rcases eq_or_ne ξ 0 with rfl | hξ
  · exact ⟨0, map_zero _⟩
  have hξ0 : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have hmem : ‖ξ‖⁻¹ • ξ ∈ closedBall (0 : StrongDual ℝ (StrongDual ℝ E)) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hξ0.ne']
  rw [← hdense] at hmem
  obtain ⟨x, -, hx⟩ := hmem
  refine ⟨‖ξ‖ • x, ?_⟩
  rw [map_smul, hx, smul_smul, mul_inv_cancel₀ hξ0.ne', one_smul]

/-! ### Weak sequential compactness -/

/-- **Theorem 3.18.** If `E` is reflexive and `(xₙ)` is a bounded sequence in `E`, there is a
subsequence `(x_{n_k})` converging in the weak topology `σ(E, E*)`. -/
theorem theorem_3_18 [CompleteSpace E] (hE : IsReflexive E) {x : ℕ → E} {C : ℝ}
    (hx : ∀ n, ‖x n‖ ≤ C) : ∃ (u : E) (φ : ℕ → ℕ), StrictMono φ ∧ (x ∘ φ) ⇀ u := by
  have := isReflexive_iff.1 hE
  obtain ⟨u, φ, hφ, hlim⟩ := NormedSpace.exists_subseq_forall_dual_tendsto (𝕜 := ℝ) hx
  exact ⟨u, φ, hφ, (proposition_3_5 _ _).2 hlim⟩

/-- **Theorem 3.19 (Eberlein–Šmulian).** If every bounded sequence in the Banach space `E`
admits a weakly convergent subsequence (in `σ(E, E*)`), then `E` is reflexive. -/
theorem theorem_3_19 [CompleteSpace E]
    (h : ∀ (x : ℕ → E) (C : ℝ), (∀ n, ‖x n‖ ≤ C) →
      ∃ (u : E) (φ : ℕ → ℕ), StrictMono φ ∧ (x ∘ φ) ⇀ u) : IsReflexive E :=
  isReflexive_iff.2 <| NormedSpace.isReflexive_of_forall_exists_subseq_forall_dual_tendsto
    fun x C hx => by
      obtain ⟨u, φ, hφ, hlim⟩ := h x C hx
      exact ⟨u, φ, hφ, (proposition_3_5 _ _).1 hlim⟩

/-- **Remark 17 (i).** In a metric space `X`, a set is compact iff every sequence in it admits a
convergent subsequence. -/
theorem remark_3_17 {X : Type*} [MetricSpace X] (s : Set X) : IsCompact s ↔ IsSeqCompact s :=
  isCompact_iff_isSeqCompact

/-! ### Further properties of reflexive spaces -/

/-- **Proposition 3.20.** A closed linear subspace `M` of a reflexive Banach space `E` is
reflexive. -/
theorem proposition_3_20 [CompleteSpace E] (hE : IsReflexive E) (M : Submodule ℝ E)
    (hM : IsClosed (M : Set E)) : IsReflexive M := by
  have := isReflexive_iff.1 hE
  exact isReflexive_iff.2 (NormedSpace.isReflexive_of_isClosed M hM)

/-- **Corollary 3.21.** A Banach space `E` is reflexive iff its dual `E*` is reflexive. -/
theorem corollary_3_21 [CompleteSpace E] : IsReflexive E ↔ IsReflexive (StrongDual ℝ E) := by
  rw [isReflexive_iff, isReflexive_iff]
  exact NormedSpace.isReflexive_strongDual_iff.symm

/-- **Corollary 3.22.** Let `E` be a reflexive Banach space and `K ⊆ E` bounded, closed and
convex. Then `K` is compact in the weak topology `σ(E, E*)`. -/
theorem corollary_3_22 [CompleteSpace E] (hE : IsReflexive E) {K : Set E} (hb : IsBounded K)
    (hc : IsClosed K) (hK : Convex ℝ K) : IsCompact (toWeakSpace ℝ E '' K) := by
  have := isReflexive_iff.1 hE
  exact hK.isCompact_image_toWeakSpace_of_isBounded_of_isClosed hb hc

/-- **Corollary 3.23.** Let `E` be a reflexive Banach space, `A ⊆ E` nonempty, closed and
convex, and `φ : A → (−∞, +∞]` convex, l.s.c., `φ ≢ +∞`, and coercive on `A` — `φ x → +∞` as
`‖x‖ → ∞`, `x ∈ A` (no assumption if `A` is bounded). Then `φ` achieves its minimum on `A`.
The function on `A` is given as `φ : E → EReal` with the convexity and semicontinuity
hypotheses on its restriction `ψ = convexRestrict A φ` (which is `φ` on `A` and `+∞` off it);
the book's closedness and convexity of `A` are carried but not used (the sublevel sets of `ψ`
are closed and convex by themselves), and neither is its requirement that `φ` never take the
value `−∞`. -/
theorem corollary_3_23 [CompleteSpace E] (hE : IsReflexive E) {A : Set E} (_hAc : IsClosed A)
    (_hAconv : Convex ℝ A) {φ : E → EReal}
    (hconv : ConvexAnalysis.ConvexFn (ConvexAnalysis.convexRestrict A φ))
    (hlsc : LowerSemicontinuous (ConvexAnalysis.convexRestrict A φ)) (hne : ∃ a ∈ A, φ a < ⊤)
    (hcoer : IsBounded A ∨ ∀ M : ℝ, ∃ R : ℝ, ∀ x ∈ A, R < ‖x‖ → (M : EReal) < φ x) :
    ∃ x₀ ∈ A, ∀ x ∈ A, φ x₀ ≤ φ x := by
  obtain ⟨a, haA, ha⟩ := hne
  set ψ := ConvexAnalysis.convexRestrict A φ with hψ
  -- the sublevel set `Ã = {x ∈ A | φ x ≤ φ a}`, which is `{x | ψ x ≤ φ a}`
  set S : Set E := {x | ψ x ≤ φ a} with hS
  have hSA : S ⊆ A := fun x hx => by
    by_contra hxA
    have : ψ x = ⊤ := ConvexAnalysis.convexRestrict_of_notMem hxA
    rw [hS, mem_ofPred_eq, this, top_le_iff] at hx
    exact ha.ne hx
  have hSmem : ∀ x ∈ A, x ∈ S ↔ φ x ≤ φ a := fun x hx => by
    rw [hS, mem_ofPred_eq, hψ, ConvexAnalysis.convexRestrict_of_mem hx]
  have haS : a ∈ S := (hSmem a haA).2 le_rfl
  have hSc : IsClosed S := hlsc.isClosed_preimage (φ a)
  have hSconv : Convex ℝ S := hconv.convex_le (φ a)
  have hSb : IsBounded S := by
    rcases hcoer with hb | hcoer
    · exact hb.subset hSA
    · obtain ⟨M, hM⟩ : ∃ M : ℝ, φ a < M := by
        rcases eq_or_ne (φ a) ⊥ with h | h
        · exact ⟨0, h ▸ EReal.bot_lt_coe 0⟩
        · obtain ⟨M, hM, -⟩ := EReal.lt_iff_exists_real_btwn.1 ha
          exact ⟨M, hM⟩
      obtain ⟨R, hR⟩ := hcoer M
      refine (isBounded_closedBall (x := (0 : E)) (r := R)).subset fun x hx => ?_
      rw [mem_closedBall_zero_iff]
      by_contra hRx
      have h1 := hR x (hSA hx) (lt_of_not_ge hRx)
      have h2 := (hSmem x (hSA hx)).1 hx
      exact (h1.trans_le h2).not_gt hM
  -- `Ã` is weakly compact and `ψ` is weakly l.s.c., so `ψ` attains its minimum on `Ã`
  have hcpt := corollary_3_22 hE hSb hSc hSconv
  have hwlsc := corollary_3_9 hconv hlsc
  have hSne : (toWeakSpace ℝ E '' S).Nonempty := ⟨toWeakSpace ℝ E a, a, haS, rfl⟩
  obtain ⟨y₀, hy₀, hmin⟩ := (hwlsc.lowerSemicontinuousOn _).exists_isMinOn hSne hcpt
  obtain ⟨x₀, hx₀S, rfl⟩ := hy₀
  refine ⟨x₀, hSA hx₀S, fun x hx => ?_⟩
  have hx₀a : φ x₀ ≤ φ a := (hSmem x₀ (hSA hx₀S)).1 hx₀S
  by_cases hxS : x ∈ S
  · have := hmin ⟨x, hxS, rfl⟩
    simpa [hψ, ConvexAnalysis.convexRestrict_of_mem hx,
        ConvexAnalysis.convexRestrict_of_mem (hSA hx₀S)]
      using this
  · have : φ a < φ x := lt_of_not_ge fun h => hxS ((hSmem x hx).2 h)
    exact hx₀a.trans this.le

/-! ### Theorem 3.24: the double adjoint -/

/-- **Theorem 3.24, first clause.** Let `E`, `F` be reflexive Banach spaces and
`A : D(A) ⊆ E → F` an unbounded operator, densely defined and closed. Then `D(A*)` is dense in
`F*` (so that `A**` is well defined). -/
theorem theorem_3_24_a [CompleteSpace E] [CompleteSpace F] (_hE : IsReflexive E)
    (hF : IsReflexive F) {A : E →ₗ.[ℝ] F} (hd : Dense (A.domain : Set E)) (hc : A.IsClosed) :
    Dense (A.strongDualAdjoint.domain : Set (StrongDual ℝ F)) := by
  have := isReflexive_iff.1 hF
  exact LinearPMap.dense_domain_strongDualAdjoint hc hd

/-- **Theorem 3.24, second clause: `A** = A`.** Under the same hypotheses the double adjoint,
viewed as an unbounded operator from `E` into `F` through `J_E` and `J_F`, is `A`: its graph is
the image of `G(A)` under `J_E × J_F`. -/
theorem theorem_3_24_b [CompleteSpace E] [CompleteSpace F] (hE : IsReflexive E)
    (hF : IsReflexive F) {A : E →ₗ.[ℝ] F} (hd : Dense (A.domain : Set E)) (hc : A.IsClosed) :
    A.strongDualAdjoint.strongDualAdjoint.graph =
      A.graph.map ((inclusionInDoubleDual ℝ E : E →ₗ[ℝ] StrongDual ℝ (StrongDual ℝ E)).prodMap
        (inclusionInDoubleDual ℝ F : F →ₗ[ℝ] StrongDual ℝ (StrongDual ℝ F))) := by
  have := isReflexive_iff.1 hE
  have := isReflexive_iff.1 hF
  exact LinearPMap.graph_strongDualAdjoint_strongDualAdjoint hc hd

end Brezis.Chapter03

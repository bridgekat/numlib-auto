/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Operations.Basic
import Numlib.Analysis.Convex.Operations.Image
import Numlib.Analysis.Convex.Operations.InfConv
import Numlib.Analysis.Convex.RelativeInterior
import Numlib.Analysis.Convex.Recession.Function

/-!
# Closedness of linear images of convex sets and functions

Let $E$ be a finite-dimensional real normed space, $G$ a real normed space, $C \subseteq E$ a
nonempty convex set and $A : E \to G$ a linear map. The image $AC$ need not be closed. Suppose that
$$0^+(\operatorname{cl} C) \cap \ker A \subseteq \operatorname{lin}(\operatorname{cl} C),$$
that is, every direction of recession of $\operatorname{cl} C$ that $A$ maps to $0$ is also a
direction of recession in the opposite sense. Then $\operatorname{cl}(AC) = A(\operatorname{cl} C)$
and $0^+(A(\operatorname{cl} C)) = A(0^+(\operatorname{cl} C))$. This is Theorem 9.1 of
[rockafellar1970convex], and the module follows §9 of that book.

From this theorem the module derives closedness results for sums $C + D$ of convex sets, for the
image $Af$ of a closed proper convex function $f$, and for the infimal convolution
$f \mathbin{\square} g$, together with the attainment of the infima that define $Af$ and
$f \mathbin{\square} g$. It also gives rules for the recession function $f0^+$ and the closure
$\operatorname{cl} f$ of sums, pointwise suprema and compositions $gA$ of convex functions.

## Main results

* `ConvexAnalysis.image_recessionCone_subset`: $A(0^+C) \subseteq 0^+(AC)$ for every set $C$ and
  every linear map $A$.
* `ConvexAnalysis.isClosed_image_of_recessionCone_inter_ker`,
  `ConvexAnalysis.recessionCone_image_of_recessionCone_inter_ker`: if $C$ is closed and convex and
  $0^+C \cap \ker A \subseteq \{0\}$, then $AC$ is closed, and $0^+(AC) = A(0^+C)$ if $C$ is also
  nonempty.
* `Convex.closure_image_eq_and_recessionCone`: Theorem 9.1 of [rockafellar1970convex], as stated
  above. Its parts are `Convex.isClosed_image_closure`, `Convex.closure_image_eq` and
  `Convex.recessionCone_image_closure`.
* `Convex.isClosed_add`, `Convex.closure_add_eq`, `Convex.recessionCone_add`: the same three
  conclusions for a sum $C + D$, when a direction of recession of $C$ and one of $D$ can cancel only
  inside the lineality spaces. The cases of no cancellation, of a bounded summand and of two cones
  follow.
* `ConvexAnalysis.closedProperConvexFn_mapLin`: a linear image $Af$ of a closed proper convex
  function is closed proper convex, the infimum that defines it is attained, and
  $(Af)0^+ = A(f0^+)$.
* `ConvexAnalysis.closedProperConvexFn_infConv_of_recessionFn_symm`,
  `ConvexAnalysis.closedProperConvexFn_infConv`: the same for the infimal convolution
  $f \mathbin{\square} g$, under a symmetry hypothesis and under a positivity hypothesis on $f0^+$
  and $g0^+$.
* `ConvexAnalysis.ClosedProperConvexFn.add`, `ConvexAnalysis.closedProperConvexFn_finsetSum`,
  `ConvexAnalysis.recessionFn_add`, `ConvexAnalysis.convexCl_add`: a sum of closed proper convex
  functions whose effective domains have a common point is closed proper convex, and its recession
  function is the sum of the recession functions; $\operatorname{cl}(f + g) = \operatorname{cl} f +
  \operatorname{cl} g$ when the relative interiors of the effective domains meet.
* `ConvexAnalysis.isClosed_epi_iSup`, `ConvexAnalysis.recessionFn_iSup`,
  `ConvexAnalysis.lscHull_iSup`: the rules for pointwise suprema.
* `ConvexAnalysis.isClosed_epi_compLin`, `ConvexAnalysis.recessionFn_compLin`,
  `ConvexAnalysis.convexCl_compLin`: the rules for the composition $gA$ with a linear map.

## Proof outline

Both conclusions of Theorem 9.1 come from one compactness argument: a decreasing sequence of
nonempty closed convex sets, each with recession cone $\{0\}$, is a sequence of compact sets, so its
intersection is nonempty. The hypothesis says that $N = 0^+(\operatorname{cl} C) \cap \ker A$ is a
subspace. Splitting $\operatorname{cl} C = N + (\operatorname{cl} C \cap M)$ along a complement $M$
of $N$ does not change the image, and it reduces the recession cone to one that meets $\ker A$ only
at $0$. The results on functions apply the results on sets to epigraphs.

## Implementation notes

* Finite dimension is needed only for $E$, to get the compactness. The target space $G$ is any real
  normed space.
* Functions take values in `EReal`. The epigraph is $\operatorname{epi} f = \{(x, \mu) \in E \times
  \mathbb{R} \mid f(x) \le \mu\}$ (`ConvexAnalysis.epi`), the effective domain is
  $\operatorname{dom} f = \{x \mid f(x) < +\infty\}$ (`ConvexAnalysis.convexDom`), and the recession
  function $f0^+$ is `ConvexAnalysis.recessionFn`, with $\operatorname{epi}(f0^+) =
  0^+(\operatorname{epi} f)$.
* The image $(Af)(y) = \inf\{f(x) \mid Ax = y\}$ is `ConvexAnalysis.mapLin`, the composition $gA$ is
  `ConvexAnalysis.compLin`, and the infimal convolution is `ConvexAnalysis.infConv`. A closed proper
  convex function is `ConvexAnalysis.ClosedProperConvexFn`.
* Two closures of a function occur: the lower semicontinuous hull, whose epigraph is
  $\operatorname{cl}(\operatorname{epi} f)$ (`ConvexAnalysis.lscHull`), and the closure
  $\operatorname{cl} f$ of a convex function (`ConvexAnalysis.convexCl`).
-/

open Filter Metric Pointwise Set Topology

namespace ConvexAnalysis

/-! ### Rays in a convex set -/

section Ray

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {C : Set E}

/-- Let $C$ be convex, and let $x_0 \in C$ and $x_0 + cz \in C$. Then $x_0 + bz \in C$ for every $b$
with $0 \le b \le c$.

Mathlib's `Convex.add_smul_mem` is the same statement with $b/c$ in place of $b$. The form here
is convenient when the endpoints are indexed by natural numbers. -/
theorem _root_.Convex.add_smul_mem_of_le (hC : Convex ℝ C) {x₀ z : E} (hx₀ : x₀ ∈ C) {b c : ℝ}
    (hb : 0 ≤ b) (hbc : b ≤ c) (h : x₀ + c • z ∈ C) : x₀ + b • z ∈ C := by
  rcases eq_or_lt_of_le (hb.trans hbc) with hc | hc
  · have hb0 : b = 0 := le_antisymm (hbc.trans hc.symm.le) hb
    rw [hb0, zero_smul, add_zero]
    exact hx₀
  · have hmem := hC.add_smul_mem hx₀ h ⟨by positivity, (div_le_one hc).2 hbc⟩
    rwa [smul_smul, div_mul_cancel₀ _ hc.ne'] at hmem

end Ray

/-! ### The unconditional inclusion -/

section Unconditional

variable {E G : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup G] [Module ℝ G]

/-- Let $A : E \to G$ be a linear map between real vector spaces and $C \subseteq E$ any set. Then
$$A(0^+C) \subseteq 0^+(AC).$$

No convexity, no closedness and no hypothesis on $A$ are needed. -/
theorem image_recessionCone_subset (A : E →ₗ[ℝ] G) (C : Set E) :
    A '' recessionCone C ⊆ recessionCone (A '' C) := by
  rintro _ ⟨y, hy, rfl⟩ _ ⟨x, hx, rfl⟩ a ha
  exact ⟨x + a • y, hy x hx a ha, by rw [map_add, map_smul]⟩

end Unconditional

/-! ### Images under the reduced hypothesis -/

section Reduced

variable {E G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {C : Set E} {A : E →ₗ[ℝ] G}

/-- Let $E$ be a finite-dimensional real normed space, $G$ a real normed space, $A : E \to G$ a
linear map, and $C \subseteq E$ a closed convex set with
$$0^+C \cap \ker A \subseteq \{0\}.$$
Then $AC$ is closed.

This is the case of `Convex.closure_image_eq_and_recessionCone` in which no nonzero direction of
recession is mapped to $0$, and it is the main step of the proof of that theorem. Nonemptiness
of $C$ is not needed. -/
theorem isClosed_image_of_recessionCone_inter_ker (A : E →ₗ[ℝ] G) (hC : Convex ℝ C)
    (hC' : IsClosed C) (h : recessionCone C ∩ (LinearMap.ker A : Set E) ⊆ {0}) :
    IsClosed (A '' C) := by
  rcases Set.eq_empty_or_nonempty C with rfl | -
  · simp
  have hA : Continuous A := A.continuous_of_finiteDimensional
  rw [← closure_eq_iff_isClosed]
  refine Set.Subset.antisymm (fun y hy => ?_) subset_closure
  set t : ℕ → Set E := fun n => C ∩ A ⁻¹' closedBall y ((n : ℝ) + 1)⁻¹ with ht
  have hpos : ∀ n : ℕ, (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := fun n => by positivity
  have htn : ∀ n, (t n).Nonempty := by
    intro n
    obtain ⟨_, ⟨x, hx, rfl⟩, hd⟩ := Metric.mem_closure_iff.1 hy _ (hpos n)
    exact ⟨x, hx, by simpa [mem_closedBall, dist_comm] using hd.le⟩
  have htconv : ∀ n, Convex ℝ (t n) := fun n =>
    hC.inter ((convex_closedBall y _).linear_preimage A)
  have htcl : ∀ n, IsClosed (t n) := fun n => hC'.inter (isClosed_closedBall.preimage hA)
  have htd : ∀ n, t (n + 1) ⊆ t n := by
    intro n
    simp only [ht]
    refine Set.inter_subset_inter_right _ (Set.preimage_mono (closedBall_subset_closedBall ?_))
    rw [inv_le_inv₀ (by positivity) (by positivity)]
    push_cast
    linarith
  have htrec : ∀ n, recessionCone (t n) = {0} := by
    intro n
    have hpre : (A ⁻¹' closedBall y ((n : ℝ) + 1)⁻¹).Nonempty := (htn n).mono inter_subset_right
    simp only [ht]
    rw [recessionCone_inter hC hC' ((convex_closedBall y _).linear_preimage A)
      (isClosed_closedBall.preimage hA) (htn n),
      recessionCone_preimage_closedBall A y (hpos n).le hpre]
    exact Set.Subset.antisymm h (by simp)
  have ht0 : IsCompact (t 0) :=
    (isCompact_iff_recessionCone_eq_zero (htconv 0) (htcl 0) (htn 0)).2 (htrec 0)
  obtain ⟨x, hx⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t htd htn ht0 htcl
  refine ⟨x, (Set.mem_iInter.1 hx 0).1, ?_⟩
  have hd : ∀ n : ℕ, dist (A x) y ≤ ((n : ℝ) + 1)⁻¹ := fun n => (Set.mem_iInter.1 hx n).2
  exact dist_le_zero.1 (ge_of_tendsto tendsto_inv_nat_add_one_atTop_nhds_zero (.of_forall hd))

/-- Let $E$ be a finite-dimensional real normed space, $G$ a real normed space, $A : E \to G$ a
linear map, and $C \subseteq E$ a nonempty closed convex set with
$0^+C \cap \ker A \subseteq \{0\}$. Then
$$0^+(AC) = A(0^+C).$$
-/
theorem recessionCone_image_of_recessionCone_inter_ker (A : E →ₗ[ℝ] G) (hC : Convex ℝ C)
    (hC' : IsClosed C) (hne : C.Nonempty)
    (h : recessionCone C ∩ (LinearMap.ker A : Set E) ⊆ {0}) :
    recessionCone (A '' C) = A '' recessionCone C := by
  refine Set.Subset.antisymm (fun v hv => ?_) (image_recessionCone_subset A C)
  obtain ⟨x₀, hx₀⟩ := hne
  have hA : Continuous A := A.continuous_of_finiteDimensional
  have hpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  set t : ℕ → Set E := fun n => {z | x₀ + ((n : ℝ) + 1) • z ∈ C} ∩ A ⁻¹' {v} with ht
  have hsconv : ∀ n : ℕ, Convex ℝ {z | x₀ + ((n : ℝ) + 1) • z ∈ C} := fun n =>
    convex_preimage_affine_smul hC x₀ _
  have hscl : ∀ n : ℕ, IsClosed {z | x₀ + ((n : ℝ) + 1) • z ∈ C} := fun n =>
    hC'.preimage ((continuous_const_smul _).const_add x₀)
  have htconv : ∀ n, Convex ℝ (t n) := fun n =>
    (hsconv n).inter ((convex_singleton v).linear_preimage A)
  have htcl : ∀ n, IsClosed (t n) := fun n => (hscl n).inter (isClosed_singleton.preimage hA)
  have htn : ∀ n, (t n).Nonempty := by
    intro n
    obtain ⟨d, hdC, hdA⟩ : A x₀ + ((n : ℝ) + 1) • v ∈ A '' C :=
      hv (A x₀) ⟨x₀, hx₀, rfl⟩ _ (hpos n).le
    refine ⟨((n : ℝ) + 1)⁻¹ • (d - x₀), ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq]
      rw [smul_inv_smul₀ (hpos n).ne']
      have hcancel : x₀ + (d - x₀) = d := by abel
      rw [hcancel]
      exact hdC
    · have : A (((n : ℝ) + 1)⁻¹ • (d - x₀)) = v := by
        rw [map_smul, map_sub, hdA, add_sub_cancel_left, smul_smul,
          inv_mul_cancel₀ (hpos n).ne', one_smul]
      simpa using this
  have htd : ∀ n, t (n + 1) ⊆ t n := by
    intro n z hz
    refine ⟨?_, hz.2⟩
    refine hC.add_smul_mem_of_le hx₀ (by positivity) ?_ hz.1
    push_cast
    linarith
  have htrec : ∀ n, recessionCone (t n) = {0} := by
    intro n
    have hpre : (A ⁻¹' ({v} : Set G)).Nonempty := (htn n).mono inter_subset_right
    have hker : A ⁻¹' ({0} : Set G) = (LinearMap.ker A : Set E) := by
      ext z; simp [LinearMap.mem_ker]
    simp only [ht]
    rw [recessionCone_inter (hsconv n) (hscl n) ((convex_singleton v).linear_preimage A)
      (isClosed_singleton.preimage hA) (htn n),
      recessionCone_preimage_affine (hpos n) x₀ C,
      recessionCone_preimage A (convex_singleton v) isClosed_singleton hpre,
      recessionCone_singleton v, hker]
    exact Set.Subset.antisymm h (by simp)
  have ht0 : IsCompact (t 0) :=
    (isCompact_iff_recessionCone_eq_zero (htconv 0) (htcl 0) (htn 0)).2 (htrec 0)
  obtain ⟨z, hz⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t htd htn ht0 htcl
  refine ⟨z, mem_recessionCone_of_exists_ray hC hC' ⟨x₀, fun a ha => ?_⟩, ?_⟩
  · obtain ⟨n, hn⟩ := exists_nat_ge a
    exact hC.add_smul_mem_of_le hx₀ ha (hn.trans (by linarith)) (Set.mem_iInter.1 hz n).1
  · simpa using (Set.mem_iInter.1 hz 0).2

end Reduced

/-! ### Closedness of a linear image -/

section Main

variable {E G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {C : Set E} {A : E →ₗ[ℝ] G}

/-- Let $C \subseteq E$ be a nonempty convex set and $A : E \to G$ a linear map, and suppose that
every $z \in 0^+(\operatorname{cl} C)$ with $Az = 0$ lies in
$\operatorname{lin}(\operatorname{cl} C)$. Then there is a nonempty closed convex set
$D \subseteq E$ with $AD = A(\operatorname{cl} C)$, $A(0^+D) = A(0^+(\operatorname{cl} C))$ and
$0^+D \cap \ker A \subseteq \{0\}$.

The hypothesis says that $N = 0^+(\operatorname{cl} C) \cap \ker A$ lies in the lineality space,
so $N$ is a subspace. The set $D$ is $\operatorname{cl} C \cap M$ for a complement $M$ of $N$.
The result is an existence statement so that the proofs of closedness and of the formula for the
recession cone can both use it. -/
theorem exists_reduction_of_recessionCone_inter_ker (hC : Convex ℝ C) (hne : C.Nonempty)
    (A : E →ₗ[ℝ] G)
    (h : ∀ z ∈ recessionCone (closure C), A z = 0 → z ∈ linealitySpace (closure C)) :
    ∃ D : Set E, Convex ℝ D ∧ IsClosed D ∧ D.Nonempty ∧
      A '' D = A '' closure C ∧ A '' recessionCone D = A '' recessionCone (closure C) ∧
      recessionCone D ∩ (LinearMap.ker A : Set E) ⊆ {0} := by
  have hD : Convex ℝ (closure C) := hC.closure
  have hD' : IsClosed (closure C) := isClosed_closure
  set N : Submodule ℝ E := linealitySubmodule (closure C) ⊓ LinearMap.ker A with hN
  have hNlin : (N : Set E) ⊆ linealitySpace (closure C) := fun z hz =>
    mem_linealitySubmodule.1 (Submodule.mem_inf.1 hz).1
  have hNker : ∀ z ∈ (N : Set E), A z = 0 := fun z hz =>
    LinearMap.mem_ker.1 (Submodule.mem_inf.1 hz).2
  obtain ⟨M, hM⟩ := Submodule.exists_isCompl N
  have hMcl : IsClosed (M : Set E) := M.closed_of_finiteDimensional
  have hsplit : closure C = (N : Set E) + (closure C ∩ (M : Set E)) :=
    eq_add_inter_of_isCompl_of_le hNlin hM
  have hDMne : (closure C ∩ (M : Set E)).Nonempty := by
    obtain ⟨x, hx⟩ := hne.closure
    rw [hsplit] at hx
    obtain ⟨-, -, q, hq, -⟩ := hx
    exact ⟨q, hq⟩
  refine ⟨closure C ∩ (M : Set E), hD.inter M.convex, hD'.inter hMcl, hDMne, ?_, ?_, ?_⟩
  · refine Set.Subset.antisymm (Set.image_mono inter_subset_left) ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [hsplit] at hx
    obtain ⟨p, hp, q, hq, rfl⟩ := hx
    exact ⟨q, hq, by rw [map_add, hNker p hp, zero_add]⟩
  · rw [recessionCone_inter hD hD' M.convex hMcl hDMne, recessionCone_coe_submodule]
    refine Set.Subset.antisymm (Set.image_mono inter_subset_left) ?_
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨p, hp, q, hq, rfl⟩ :=
      Submodule.mem_sup.1 (show z ∈ N ⊔ M by rw [hM.sup_eq_top]; trivial)
    refine ⟨q, ⟨?_, hq⟩, by rw [map_add, hNker p hp, zero_add]⟩
    have hpneg : -p ∈ recessionCone (closure C) := (mem_linealitySpace.1 (hNlin hp)).2
    have hsum := add_mem_recessionCone hz hpneg
    simpa [add_comm, add_assoc] using hsum
  · rw [recessionCone_inter hD hD' M.convex hMcl hDMne, recessionCone_coe_submodule]
    rintro z ⟨⟨hz₁, hz₂⟩, hz₃⟩
    have hzN : z ∈ N :=
      Submodule.mem_inf.2 ⟨mem_linealitySubmodule.2 (h z hz₁ (LinearMap.mem_ker.1 hz₃)), hz₃⟩
    have hbot : z ∈ N ⊓ M := ⟨hzN, hz₂⟩
    rw [hM.inf_eq_bot] at hbot
    simpa using hbot

/-- Let $C \subseteq E$ be convex and $A : E \to G$ a linear map, and suppose that every
$z \in 0^+(\operatorname{cl} C)$ with $Az = 0$ lies in
$\operatorname{lin}(\operatorname{cl} C)$. Then $A(\operatorname{cl} C)$ is closed. -/
theorem _root_.Convex.isClosed_image_closure (hC : Convex ℝ C) (A : E →ₗ[ℝ] G)
    (h : ∀ z ∈ recessionCone (closure C), A z = 0 → z ∈ linealitySpace (closure C)) :
    IsClosed (A '' closure C) := by
  rcases Set.eq_empty_or_nonempty C with rfl | hne
  · simp
  obtain ⟨D, hDconv, hDcl, -, himg, -, hred⟩ :=
    exists_reduction_of_recessionCone_inter_ker hC hne A h
  rw [← himg]
  exact isClosed_image_of_recessionCone_inter_ker A hDconv hDcl hred

/-- Let $C \subseteq E$ be convex and $A : E \to G$ a linear map, and suppose that every
$z \in 0^+(\operatorname{cl} C)$ with $Az = 0$ lies in
$\operatorname{lin}(\operatorname{cl} C)$. Then
$\operatorname{cl}(AC) = A(\operatorname{cl} C)$. -/
theorem _root_.Convex.closure_image_eq (hC : Convex ℝ C) (A : E →ₗ[ℝ] G)
    (h : ∀ z ∈ recessionCone (closure C), A z = 0 → z ∈ linealitySpace (closure C)) :
    closure (A '' C) = A '' closure C := by
  refine Set.Subset.antisymm ?_
    (image_closure_subset_closure_image A.continuous_of_finiteDimensional)
  rw [← (Convex.isClosed_image_closure hC A h).closure_eq]
  exact closure_mono (Set.image_mono subset_closure)

/-- Let $C \subseteq E$ be nonempty and convex and $A : E \to G$ a linear map, and suppose that
every $z \in 0^+(\operatorname{cl} C)$ with $Az = 0$ lies in
$\operatorname{lin}(\operatorname{cl} C)$. Then $0^+(A(\operatorname{cl} C)) =
A(0^+(\operatorname{cl} C))$. -/
theorem _root_.Convex.recessionCone_image_closure (hC : Convex ℝ C) (hne : C.Nonempty)
    (A : E →ₗ[ℝ] G)
    (h : ∀ z ∈ recessionCone (closure C), A z = 0 → z ∈ linealitySpace (closure C)) :
    recessionCone (A '' closure C) = A '' recessionCone (closure C) := by
  obtain ⟨D, hDconv, hDcl, hDne, himg, hrec, hred⟩ :=
    exists_reduction_of_recessionCone_inter_ker hC hne A h
  rw [← himg, ← hrec]
  exact recessionCone_image_of_recessionCone_inter_ker A hDconv hDcl hDne hred

/-- Let $E$ be a finite-dimensional real normed space, $G$ a real normed space, $C \subseteq E$ a
nonempty convex set and $A : E \to G$ a linear map. Suppose that every
$z \in 0^+(\operatorname{cl} C)$ with $Az = 0$ lies in
$\operatorname{lin}(\operatorname{cl} C)$. Then
$$\operatorname{cl}(AC) = A(\operatorname{cl} C) \quad\text{and}\quad 0^+(A(\operatorname{cl}
  C)) = A(0^+(\operatorname{cl} C)).$$
This is Theorem 9.1 of [rockafellar1970convex].

The target space $G$ need not be finite-dimensional. The two conclusions are
`Convex.closure_image_eq` and `Convex.recessionCone_image_closure`, and
`Convex.isClosed_image_closure` states that $A(\operatorname{cl} C)$ is closed. -/
theorem _root_.Convex.closure_image_eq_and_recessionCone (hC : Convex ℝ C) (hne : C.Nonempty)
    (A : E →ₗ[ℝ] G)
    (h : ∀ z ∈ recessionCone (closure C), A z = 0 → z ∈ linealitySpace (closure C)) :
    closure (A '' C) = A '' closure C ∧
      recessionCone (A '' closure C) = A '' recessionCone (closure C) :=
  ⟨Convex.closure_image_eq hC A h, Convex.recessionCone_image_closure hC hne A h⟩

end Main

/-! ### Sums of sets -/

section Sum

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {C D : Set E}

omit [FiniteDimensional ℝ E] in
/-- For sets $C, D \subseteq E$, the sum $C + D$ is the image of $C \times D$ under the linear map
$(x, y) \mapsto x + y$. This turns a question about a sum into a question about a linear image. -/
theorem image_coprod_id_prod (C D : Set E) :
    (LinearMap.id.coprod LinearMap.id : E × E →ₗ[ℝ] E) '' C ×ˢ D = C + D :=
  Set.add_image_prod

omit [FiniteDimensional ℝ E] in
/-- Let $C$ and $D$ be nonempty, and suppose that $z \in \operatorname{lin}(\operatorname{cl} C)$
and $w \in \operatorname{lin}(\operatorname{cl} D)$ whenever $z \in 0^+(\operatorname{cl} C)$,
$w \in 0^+(\operatorname{cl} D)$ and $z + w = 0$. Then every
$p \in 0^+(\operatorname{cl}(C \times D))$ with $p_1 + p_2 = 0$ lies in
$\operatorname{lin}(\operatorname{cl}(C \times D))$. This is the hypothesis of
`Convex.closure_image_eq_and_recessionCone` for the set $C \times D$ and the map
$(x, y) \mapsto x + y$. -/
theorem forall_mem_linealitySpace_prod (hCne : C.Nonempty) (hDne : D.Nonempty)
    (h : ∀ z ∈ recessionCone (closure C), ∀ w ∈ recessionCone (closure D), z + w = 0 →
      z ∈ linealitySpace (closure C) ∧ w ∈ linealitySpace (closure D)) :
    ∀ p ∈ recessionCone (closure (C ×ˢ D)),
      (LinearMap.id.coprod LinearMap.id : E × E →ₗ[ℝ] E) p = 0 →
        p ∈ linealitySpace (closure (C ×ˢ D)) := by
  rintro ⟨z, w⟩ hp hzero
  rw [closure_prod_eq, recessionCone_prod hCne.closure hDne.closure] at hp
  rw [closure_prod_eq, linealitySpace_prod hCne.closure hDne.closure]
  exact h z hp.1 w hp.2 hzero

/-- Let $E$ be a finite-dimensional real normed space, and let $C, D \subseteq E$ be nonempty closed
convex sets. Suppose that $z \in \operatorname{lin} C$ and $w \in \operatorname{lin} D$ whenever
$z \in 0^+C$, $w \in 0^+D$ and $z + w = 0$. Then $C + D$ is closed.

The hypothesis says that a direction of recession of $C$ and a direction of recession of $D$ can
cancel only inside the two lineality spaces. The proof applies
`Convex.closure_image_eq_and_recessionCone` to $C \times D$ and the map $(x, y) \mapsto x + y$. -/
theorem _root_.Convex.isClosed_add (hC : Convex ℝ C) (hCc : IsClosed C) (hCne : C.Nonempty)
    (hD : Convex ℝ D) (hDc : IsClosed D) (hDne : D.Nonempty)
    (h : ∀ z ∈ recessionCone C, ∀ w ∈ recessionCone D, z + w = 0 →
      z ∈ linealitySpace C ∧ w ∈ linealitySpace D) :
    IsClosed (C + D) := by
  have hCcl : closure C = C := hCc.closure_eq
  have hDcl : closure D = D := hDc.closure_eq
  have hkey := forall_mem_linealitySpace_prod hCne hDne (by rw [hCcl, hDcl]; exact h)
  have := Convex.isClosed_image_closure (hC.prod hD) (LinearMap.id.coprod LinearMap.id) hkey
  rwa [closure_prod_eq, hCcl, hDcl, image_coprod_id_prod] at this

/-- Let $E$ be a finite-dimensional real normed space, and let $C, D \subseteq E$ be nonempty convex
sets. Suppose that $z \in \operatorname{lin}(\operatorname{cl} C)$ and
$w \in \operatorname{lin}(\operatorname{cl} D)$ whenever $z \in 0^+(\operatorname{cl} C)$,
$w \in 0^+(\operatorname{cl} D)$ and $z + w = 0$. Then
$$\operatorname{cl}(C + D) = \operatorname{cl} C + \operatorname{cl} D.$$
-/
theorem _root_.Convex.closure_add_eq (hC : Convex ℝ C) (hCne : C.Nonempty) (hD : Convex ℝ D)
    (hDne : D.Nonempty)
    (h : ∀ z ∈ recessionCone (closure C), ∀ w ∈ recessionCone (closure D), z + w = 0 →
      z ∈ linealitySpace (closure C) ∧ w ∈ linealitySpace (closure D)) :
    closure (C + D) = closure C + closure D := by
  have := Convex.closure_image_eq (hC.prod hD) (LinearMap.id.coprod LinearMap.id)
    (forall_mem_linealitySpace_prod hCne hDne h)
  rwa [image_coprod_id_prod, closure_prod_eq, image_coprod_id_prod] at this

/-- Let $E$ be a finite-dimensional real normed space, and let $C, D \subseteq E$ be nonempty convex
sets. Suppose that $z \in \operatorname{lin}(\operatorname{cl} C)$ and
$w \in \operatorname{lin}(\operatorname{cl} D)$ whenever $z \in 0^+(\operatorname{cl} C)$,
$w \in 0^+(\operatorname{cl} D)$ and $z + w = 0$. Then
$$0^+(\operatorname{cl} C + \operatorname{cl} D) = 0^+(\operatorname{cl} C) +
  0^+(\operatorname{cl} D).$$
-/
theorem _root_.Convex.recessionCone_add (hC : Convex ℝ C) (hCne : C.Nonempty) (hD : Convex ℝ D)
    (hDne : D.Nonempty)
    (h : ∀ z ∈ recessionCone (closure C), ∀ w ∈ recessionCone (closure D), z + w = 0 →
      z ∈ linealitySpace (closure C) ∧ w ∈ linealitySpace (closure D)) :
    recessionCone (closure C + closure D) =
      recessionCone (closure C) + recessionCone (closure D) := by
  have := Convex.recessionCone_image_closure (hC.prod hD)
    (hCne.prod hDne) (LinearMap.id.coprod LinearMap.id)
    (forall_mem_linealitySpace_prod hCne hDne h)
  rwa [closure_prod_eq, image_coprod_id_prod,
    recessionCone_prod hCne.closure hDne.closure, image_coprod_id_prod] at this

/-! ### Sums under a no-cancellation hypothesis -/

omit [FiniteDimensional ℝ E] in
/-- Suppose that $z \in 0^+C$ and $-z \in 0^+D$ imply $z = 0$. Then $z \in \operatorname{lin} C$ and
$w \in \operatorname{lin} D$ whenever $z \in 0^+C$, $w \in 0^+D$ and $z + w = 0$: the only such
pair is $(0, 0)$, which lies in both lineality spaces. -/
theorem forall_mem_linealitySpace_of_neg_notMem
    (h : ∀ z ∈ recessionCone C, -z ∈ recessionCone D → z = 0) :
    ∀ z ∈ recessionCone C, ∀ w ∈ recessionCone D, z + w = 0 →
      z ∈ linealitySpace C ∧ w ∈ linealitySpace D := by
  intro z hz w hw hzw
  have hw' : w = -z := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hzw
  subst hw'
  have hz0 : z = 0 := h z hz hw
  subst hz0
  refine ⟨zero_mem_linealitySpace C, ?_⟩
  rw [neg_zero]
  exact zero_mem_linealitySpace D

/-- Let $C$ and $D$ be nonempty closed convex subsets of a finite-dimensional real normed space. If
$z \in 0^+C$ and $-z \in 0^+D$ imply $z = 0$, then $C + D$ is closed. -/
theorem _root_.Convex.isClosed_add_of_neg_notMem_recessionCone (hC : Convex ℝ C) (hCc : IsClosed C)
    (hCne : C.Nonempty) (hD : Convex ℝ D) (hDc : IsClosed D) (hDne : D.Nonempty)
    (h : ∀ z ∈ recessionCone C, -z ∈ recessionCone D → z = 0) : IsClosed (C + D) :=
  Convex.isClosed_add hC hCc hCne hD hDc hDne (forall_mem_linealitySpace_of_neg_notMem h)

/-- Let $C$ and $D$ be nonempty closed convex subsets of a finite-dimensional real normed space. If
$z \in 0^+C$ and $-z \in 0^+D$ imply $z = 0$, then $0^+(C + D) = 0^+C + 0^+D$. -/
theorem _root_.Convex.recessionCone_add_of_neg_notMem_recessionCone (hC : Convex ℝ C)
    (hCc : IsClosed C) (hCne : C.Nonempty) (hD : Convex ℝ D) (hDc : IsClosed D) (hDne : D.Nonempty)
    (h : ∀ z ∈ recessionCone C, -z ∈ recessionCone D → z = 0) :
    recessionCone (C + D) = recessionCone C + recessionCone D := by
  have key := Convex.recessionCone_add hC hCne hD hDne
    (by rw [hCc.closure_eq, hDc.closure_eq]; exact forall_mem_linealitySpace_of_neg_notMem h)
  rwa [hCc.closure_eq, hDc.closure_eq] at key

/-- Let $C$ be a nonempty bounded closed convex set and $D$ a nonempty closed convex set in a
finite-dimensional real normed space. Then $C + D$ is closed. A bounded set has $0^+C = \{0\}$,
so the hypothesis of `Convex.isClosed_add` holds. -/
theorem _root_.Convex.isClosed_add_of_isBounded (hC : Convex ℝ C) (hCc : IsClosed C)
    (hCne : C.Nonempty) (hCb : Bornology.IsBounded C) (hD : Convex ℝ D) (hDc : IsClosed D)
    (hDne : D.Nonempty) :
    IsClosed (C + D) := by
  refine Convex.isClosed_add_of_neg_notMem_recessionCone hC hCc hCne hD hDc hDne fun z hz _ => ?_
  rw [recessionCone_eq_zero_of_isBounded hCne hCb] at hz
  exact hz

/-- Let $K$ and $L$ be pointed convex cones in a finite-dimensional real normed space. Suppose that
$z \in \operatorname{lin}(\operatorname{cl} K)$ and
$w \in \operatorname{lin}(\operatorname{cl} L)$ whenever $z \in \operatorname{cl} K$,
$w \in \operatorname{cl} L$ and $z + w = 0$. Then $\operatorname{cl}(K + L) = \operatorname{cl}
K + \operatorname{cl} L$.

The closure of a cone is its own recession cone, so the hypothesis of `Convex.closure_add_eq` is
a condition on the closures themselves. -/
theorem closure_add_coe_pointedCone (K L : PointedCone ℝ E)
    (h : ∀ z ∈ closure (K : Set E), ∀ w ∈ closure (L : Set E), z + w = 0 →
      z ∈ linealitySpace (closure (K : Set E)) ∧ w ∈ linealitySpace (closure (L : Set E))) :
    closure ((K : Set E) + (L : Set E)) = closure (K : Set E) + closure (L : Set E) := by
  refine Convex.closure_add_eq (K : ConvexCone ℝ E).convex ⟨0, K.zero_mem⟩
    (L : ConvexCone ℝ E).convex ⟨0, L.zero_mem⟩ ?_
  rwa [recessionCone_closure_coe_pointedCone, recessionCone_closure_coe_pointedCone]

end Sum

/-! ### Images of functions -/

section FnAlg

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {f : E → EReal} {z : E}

/-- Let $f$ be proper. Then $(z, 0) \in \operatorname{lin}(\operatorname{epi} f)$ if and only if $z$
lies in the constancy space of $f$, that is, $(f0^+)(z) \le 0$ and $(f0^+)(-z) \le 0$.

So $(z, 0)$ lies in the lineality space of $\operatorname{epi} f$ exactly when $f$ is constant
along $z$. By definition, $(z, 0) \in 0^+(\operatorname{epi} f)$ exactly when $f$ recedes in the
direction $z$. -/
theorem mk_zero_mem_linealitySpace_epi_iff (hp : ProperConvex f) :
    ((z, (0 : ℝ)) : E × ℝ) ∈ linealitySpace (epi f) ↔ z ∈ constancySpace f := by
  rw [mk_mem_linealitySpace_epi_iff hp, mem_constancySpace]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨by rw [h₁]; norm_num, by rw [h₂]; norm_num⟩
  · rintro ⟨h₁, h₂⟩
    have hc₁ : recessionFn f z ≤ ((0 : ℝ) : EReal) := by simpa using h₁
    have hc₂ : recessionFn f (-z) ≤ ((0 : ℝ) : EReal) := by simpa using h₂
    have hb₁ : ((0 : ℝ) : EReal) ≤ recessionFn f z :=
      le_recessionFn_of_neg_le hp (ν := 0) (by simpa using hc₂)
    have hb₂ : ((0 : ℝ) : EReal) ≤ recessionFn f (-z) := by
      refine le_recessionFn_of_neg_le hp (ν := 0) ?_
      simpa using hc₁
    exact ⟨le_antisymm hc₁ hb₁, by simpa using le_antisymm hc₂ hb₂⟩

end FnAlg

section Fn

variable {E G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {f : E → EReal} {A : E →ₗ[ℝ] G}

/-- Let $E$ be a finite-dimensional real normed space, $G$ a real normed space, $f$ a closed proper
convex function on $E$ and $A : E \to G$ a linear map. Let $Af$ be the image of $f$ under $A$,
$(Af)(y) = \inf\{f(x) \mid Ax = y\}$. Suppose that every $z$ with $(f0^+)(z) \le 0$ and $Az = 0$
lies in the constancy space of $f$. Then
$$\operatorname{epi}(Af) = \{(Ax, \mu) \mid (x, \mu) \in \operatorname{epi} f\},$$
$Af$ is a closed proper convex function, and $(Af)0^+ = A(f0^+)$.

The hypothesis says that $f$ is constant along every direction of recession of $f$ that $A$ maps
to $0$. The epigraph identity says that the infimum defining $(Af)(y)$ is attained whenever it
is finite. The three conclusions come from one application of the theorem on linear images to
$\operatorname{epi} f$ and the map $(x, \mu) \mapsto (Ax, \mu)$: closedness, properness and the
recession function are read off the epigraph identity. The companion result for infimal
convolution is `ConvexAnalysis.closedProperConvexFn_infConv`. -/
theorem closedProperConvexFn_mapLin (hf : ClosedProperConvexFn f) (A : E →ₗ[ℝ] G)
    (h : ∀ z, recessionFn f z ≤ 0 → A z = 0 → z ∈ constancySpace f) :
    epi (mapLin A f) = A.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ) '' epi f ∧
      ClosedProperConvexFn (mapLin A f) ∧
      recessionFn (mapLin A f) = mapLin A (recessionFn f) := by
  set Aid : E × ℝ →ₗ[ℝ] G × ℝ := A.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ) with hAid
  have hp : ProperConvex f := hf.proper
  have hconv : Convex ℝ (epi f) := hf.convex.convex_epi
  have hclosure : closure (epi f) = epi f := hf.isClosed_epi.closure_eq
  have hne : (epi f).Nonempty := by
    obtain ⟨x, hx⟩ := hp.convexDom_nonempty
    obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x) hx
    exact ⟨(x, r), mk_mem_epi.2 hr.le⟩
  -- the hypothesis, transported to the epigraph
  have hkey : ∀ q ∈ recessionCone (closure (epi f)), Aid q = 0 →
      q ∈ linealitySpace (closure (epi f)) := by
    rintro ⟨w, ν⟩ hq hzero
    rw [hclosure] at hq ⊢
    have hν : ν = 0 := congrArg Prod.snd hzero
    have hw : A w = 0 := congrArg Prod.fst hzero
    subst hν
    exact (mk_zero_mem_linealitySpace_epi_iff hp).2
      (h w (by simpa using recessionFn_le_coe_iff.2 hq) hw)
  have hclosed : IsClosed (Aid '' epi f) := by
    have := Convex.isClosed_image_closure hconv Aid hkey
    rwa [hclosure] at this
  have hrec : recessionCone (Aid '' epi f) = Aid '' recessionCone (epi f) := by
    have := Convex.recessionCone_image_closure hconv hne Aid hkey
    rwa [hclosure] at this
  -- the image of an epigraph is upward closed, hence (being closed) an epigraph
  have hmono : ∀ (y : G) (μ ν : ℝ), (y, μ) ∈ Aid '' epi f → μ ≤ ν → (y, ν) ∈ Aid '' epi f := by
    rintro y μ ν ⟨⟨x, ρ⟩, hxρ, hxy⟩ hμν
    have h₁ : A x = y := congrArg Prod.fst hxy
    have h₂ : ρ = μ := congrArg Prod.snd hxy
    refine ⟨(x, ν), mk_mem_epi.2 ((mk_mem_epi.1 hxρ).trans ?_), ?_⟩
    · exact_mod_cast h₂ ▸ hμν
    · rw [hAid, LinearMap.prodMap_apply, h₁]
      rfl
  have hepi : epi (mapLin A f) = Aid '' epi f :=
    epi_mapLin (IsEpiLike.of_isClosed hmono hclosed)
  -- properness: a vertical line in the image would be a direction of recession `A` kills
  have hnebot : ∀ y : G, mapLin A f y ≠ ⊥ := by
    intro y hbot
    have hline : ∀ μ : ℝ, ((y, μ) : G × ℝ) ∈ Aid '' epi f := fun μ => by
      rw [← hepi]
      exact mk_mem_epi.2 (hbot ▸ bot_le)
    have hray : ((0 : G), (-1 : ℝ)) ∈ recessionCone (Aid '' epi f) := by
      refine mem_recessionCone_of_exists_ray (hconv.linear_image Aid) hclosed
        ⟨(y, 0), fun a ha => ?_⟩
      have : ((y, (0 : ℝ)) : G × ℝ) + a • ((0 : G), (-1 : ℝ)) = (y, -a) := by
        simp [Prod.smul_mk, Prod.mk_add_mk]
      rw [this]
      exact hline (-a)
    rw [hrec] at hray
    obtain ⟨⟨w, ν⟩, hw, hwy⟩ := hray
    have h₁ : A w = 0 := congrArg Prod.fst hwy
    have h₂ : ν = -1 := congrArg Prod.snd hwy
    subst h₂
    have hle : recessionFn f w ≤ ((-1 : ℝ) : EReal) := recessionFn_le_coe_iff.2 hw
    have hconst := h w (hle.trans (by norm_num)) h₁
    have hzero : recessionFn f w = ((0 : ℝ) : EReal) :=
      ((mk_mem_linealitySpace_epi_iff hp).1 ((mk_zero_mem_linealitySpace_epi_iff hp).2 hconst)).1
    rw [hzero, EReal.coe_le_coe_iff] at hle
    linarith
  have hdomne : (convexDom (mapLin A f)).Nonempty := by
    rw [convexDom_mapLin]
    exact hp.convexDom_nonempty.image A
  refine ⟨hepi, ClosedProperConvexFn.of_isClosed_epi (convexFn_mapLin A hf.convex)
    (by rw [hepi]; exact hclosed) ⟨hdomne, hnebot⟩, ?_⟩
  -- the recession function of an image
  have hepilike : IsEpiLike (Aid '' epi (recessionFn f)) := by
    rw [epi_recessionFn, ← hrec, ← hepi]
    exact isEpiLike_recessionCone_epi _
  refine epi_injective ?_
  rw [epi_recessionFn, hepi, hrec, epi_mapLin hepilike, epi_recessionFn]

/-- Under the hypotheses of `ConvexAnalysis.closedProperConvexFn_mapLin`, let $y \in G$ and
$\mu \in \mathbb{R}$ with $(Af)(y) \le \mu$. Then there is $x \in E$ with $Ax = y$ and
$f(x) \le \mu$. In particular, the infimum defining $(Af)(y)$ is attained when it is finite. -/
theorem exists_mapLin_eq (hf : ClosedProperConvexFn f) (A : E →ₗ[ℝ] G)
    (h : ∀ z, recessionFn f z ≤ 0 → A z = 0 → z ∈ constancySpace f)
    {y : G} {μ : ℝ} (hμ : mapLin A f y ≤ (μ : EReal)) :
    ∃ x : E, A x = y ∧ f x ≤ (μ : EReal) := by
  obtain ⟨hepi, -, -⟩ := closedProperConvexFn_mapLin hf A h
  obtain ⟨⟨x, ρ⟩, hxρ, hxy⟩ : ((y, μ) : G × ℝ) ∈ _ := hepi ▸ mk_mem_epi.2 hμ
  refine ⟨x, congrArg Prod.fst hxy, ?_⟩
  have h₂ : ρ = μ := congrArg Prod.snd hxy
  exact h₂ ▸ mk_mem_epi.1 hxρ

end Fn

/-! ### Infimal convolution -/

section InfConvFn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f g : E → EReal}

omit [FiniteDimensional ℝ E] in
/-- Let $f$ and $g$ be proper, and suppose that $(f0^+)(z) + (g0^+)(-z) > 0$ for every $z \neq 0$.
If $q \in 0^+(\operatorname{epi} f)$ and $-q \in 0^+(\operatorname{epi} g)$, then $q = 0$.

The hypothesis says nothing at $z = 0$. Properness gives $(f0^+)(0) = (g0^+)(0) = 0$, and this
forces the second coordinate of $q$ to be $0$. -/
theorem forall_eq_zero_of_recessionFn_add_pos (hpf : ProperConvex f) (hpg : ProperConvex g)
    (h : ∀ z : E, z ≠ 0 → 0 < recessionFn f z + recessionFn g (-z)) :
    ∀ q ∈ recessionCone (epi f), -q ∈ recessionCone (epi g) → q = 0 := by
  rintro ⟨z, ν⟩ hq hnq
  have hnq' : ((-z, -ν) : E × ℝ) ∈ recessionCone (epi g) := hnq
  have h₁ : recessionFn f z ≤ (ν : EReal) := recessionFn_le_coe_iff.2 hq
  have h₂ : recessionFn g (-z) ≤ ((-ν : ℝ) : EReal) := recessionFn_le_coe_iff.2 hnq'
  rcases eq_or_ne z 0 with rfl | hz
  · rw [recessionFn_apply_zero hpf] at h₁
    rw [neg_zero, recessionFn_apply_zero hpg] at h₂
    have e₁' : (0 : ℝ) ≤ ν := by exact_mod_cast h₁
    have e₂' : (0 : ℝ) ≤ -ν := by exact_mod_cast h₂
    have hν0 : ν = 0 := le_antisymm (by linarith) e₁'
    rw [hν0]
    exact Prod.mk_zero_zero
  · exfalso
    have hsum : recessionFn f z + recessionFn g (-z) ≤ (ν : EReal) + ((-ν : ℝ) : EReal) :=
      add_le_add h₁ h₂
    rw [← EReal.coe_add, add_neg_cancel, EReal.coe_zero] at hsum
    exact absurd hsum (not_le.2 (h z hz))

omit [FiniteDimensional ℝ E] in
/-- Call $z \in E$ a direction of **joint recession** of $f$ and $g$ if
$(f0^+)(z) + (g0^+)(-z) \le 0$; these are the directions in which $f \mathbin{\square} g$ does
not increase. Let $f$ and $g$ be proper, and suppose that $-z$ is a direction of joint recession
whenever $z$ is. If $q \in 0^+(\operatorname{epi} f)$, $r \in 0^+(\operatorname{epi} g)$ and
$q + r = 0$, then $q \in \operatorname{lin}(\operatorname{epi} f)$ and
$r \in \operatorname{lin}(\operatorname{epi} g)$. This is the hypothesis of
`Convex.isClosed_add` for $\operatorname{epi} f$ and $\operatorname{epi} g$.

The hypothesis is about directions in $E$ only. Properness, through
`ConvexAnalysis.le_recessionFn_of_neg_le`, relates the two second coordinates. -/
theorem forall_mem_linealitySpace_epi_of_recessionFn_symm (hpf : ProperConvex f)
    (hpg : ProperConvex g)
    (h : ∀ z : E, recessionFn f z + recessionFn g (-z) ≤ 0 →
      recessionFn f (-z) + recessionFn g z ≤ 0) :
    ∀ q ∈ recessionCone (epi f), ∀ r ∈ recessionCone (epi g), q + r = 0 →
      q ∈ linealitySpace (epi f) ∧ r ∈ linealitySpace (epi g) := by
  rintro ⟨z, ν⟩ hq ⟨w, ρ⟩ hr hqr
  have hqr' : ((z, ν) : E × ℝ) + ((w, ρ) : E × ℝ) = 0 := hqr
  have hzw : z + w = (0 : E) := congrArg Prod.fst hqr'
  have hνρ : ν + ρ = (0 : ℝ) := congrArg Prod.snd hqr'
  have hw : w = -z := eq_neg_of_add_eq_zero_right hzw
  have hρ : ρ = -ν := by linarith
  subst hw
  subst hρ
  have h₁ : recessionFn f z ≤ (ν : EReal) := recessionFn_le_coe_iff.2 hq
  have h₂ : recessionFn g (-z) ≤ ((-ν : ℝ) : EReal) := recessionFn_le_coe_iff.2 hr
  have hsum : recessionFn f z + recessionFn g (-z) ≤ 0 := by
    have hadd := add_le_add h₁ h₂
    rwa [← EReal.coe_add, add_neg_cancel, EReal.coe_zero] at hadd
  have hsym := h z hsum
  have hA : ((-ν : ℝ) : EReal) ≤ recessionFn f (-z) :=
    le_recessionFn_of_neg_le hpf (by simp only [neg_neg]; exact h₁)
  have hB : (ν : EReal) ≤ recessionFn g z := le_recessionFn_of_neg_le hpg h₂
  have hfz : recessionFn f (-z) ≤ ((-ν : ℝ) : EReal) := by
    refine EReal.le_coe_of_add_le_coe_add hA hB ?_
    rwa [neg_add_cancel, EReal.coe_zero]
  have hgz : recessionFn g z ≤ (ν : EReal) := by
    refine EReal.le_coe_of_add_le_coe_add hB hA ?_
    rw [add_neg_cancel, EReal.coe_zero, add_comm]
    exact hsym
  refine ⟨mem_linealitySpace.2 ⟨hq, recessionFn_le_coe_iff.1 hfz⟩,
    mem_linealitySpace.2 ⟨hr, ?_⟩⟩
  have hneg : -((-z, -ν) : E × ℝ) = ((z, ν) : E × ℝ) := by simp
  rw [hneg]
  exact recessionFn_le_coe_iff.1 hgz

/-- Let $E$ be a finite-dimensional real normed space and $f$, $g$ closed proper convex functions on
$E$. Suppose that the set of directions of joint recession,
$\{z \mid (f0^+)(z) + (g0^+)(-z) \le 0\}$, is symmetric: $(f0^+)(-z) + (g0^+)(z) \le 0$ whenever
$(f0^+)(z) + (g0^+)(-z) \le 0$. Then
$$\operatorname{epi}(f \mathbin{\square} g) = \operatorname{epi} f + \operatorname{epi} g,$$
$f \mathbin{\square} g$ is a closed proper convex function, and $(f \mathbin{\square} g)0^+ =
f0^+ \mathbin{\square} g0^+$.

The epigraph identity says that the infimum defining $(f \mathbin{\square} g)(x)$ is attained.
The hypothesis is weaker than that of `ConvexAnalysis.closedProperConvexFn_infConv`, which asks
the set of directions of joint recession to be $\{0\}$. Symmetry allows a whole subspace of
directions along which $f$ and $g$ are affine with opposite slopes; $f = g = 0$ is such a pair,
and the conclusions hold for it.

Properness of $f \mathbin{\square} g$ is where symmetry is used. A vertical line in
$\operatorname{epi} f + \operatorname{epi} g$ gives a direction $z$ with
$(f0^+)(z) + (g0^+)(-z) \le -1$. Symmetry then makes the reversed sum at most $0$, while
`ConvexAnalysis.le_recessionFn_of_neg_le` gives $(f0^+)(-z) + (g0^+)(z) \ge 1$. -/
theorem closedProperConvexFn_infConv_of_recessionFn_symm (hf : ClosedProperConvexFn f)
    (hg : ClosedProperConvexFn g)
    (h : ∀ z : E, recessionFn f z + recessionFn g (-z) ≤ 0 →
      recessionFn f (-z) + recessionFn g z ≤ 0) :
    epi (infConv f g) = epi f + epi g ∧ ClosedProperConvexFn (infConv f g) ∧
      recessionFn (infConv f g) = infConv (recessionFn f) (recessionFn g) := by
  have hfne : (epi f).Nonempty := (epi_nonempty_iff f).2 hf.proper.convexDom_nonempty
  have hgne : (epi g).Nonempty := (epi_nonempty_iff g).2 hg.proper.convexDom_nonempty
  have hfcl : closure (epi f) = epi f := hf.isClosed_epi.closure_eq
  have hgcl : closure (epi g) = epi g := hg.isClosed_epi.closure_eq
  have hkey := forall_mem_linealitySpace_epi_of_recessionFn_symm hf.proper hg.proper h
  have hclosed : IsClosed (epi f + epi g) :=
    Convex.isClosed_add hf.convex.convex_epi hf.isClosed_epi hfne hg.convex.convex_epi
      hg.isClosed_epi hgne hkey
  have hrecset : recessionCone (epi f + epi g)
      = recessionCone (epi f) + recessionCone (epi g) := by
    have hres := Convex.recessionCone_add hf.convex.convex_epi hfne hg.convex.convex_epi hgne
      (by rw [hfcl, hgcl]; exact hkey)
    rwa [hfcl, hgcl] at hres
  have hepi : epi (infConv f g) = epi f + epi g :=
    epi_infConv (IsEpiLike.of_isClosed (fun _ _ _ hμ hμν => mem_epi_add_epi_of_le hμ hμν) hclosed)
  -- properness: a vertical line in `epi f + epi g` violates the symmetry
  have hnebot : ∀ x : E, infConv f g x ≠ ⊥ := by
    intro x hbot
    have hline : ∀ μ : ℝ, ((x, μ) : E × ℝ) ∈ epi f + epi g := by
      intro μ
      rw [← hepi]
      exact mk_mem_epi.2 (le_of_eq_of_le hbot bot_le)
    have hray : (((0 : E), (-1 : ℝ)) : E × ℝ) ∈ recessionCone (epi f + epi g) := by
      refine mem_recessionCone_of_exists_ray (hf.convex.convex_epi.add hg.convex.convex_epi)
        hclosed ⟨((x, (0 : ℝ)) : E × ℝ), fun a ha => ?_⟩
      have hshift : ((x, (0 : ℝ)) : E × ℝ) + a • (((0 : E), (-1 : ℝ)) : E × ℝ)
          = ((x, -a) : E × ℝ) := by simp [Prod.smul_mk, Prod.mk_add_mk]
      rw [hshift]
      exact hline (-a)
    rw [hrecset] at hray
    obtain ⟨q, hq, r, hr, hqr⟩ := hray
    have hqr' : q + r = (((0 : E), (-1 : ℝ)) : E × ℝ) := hqr
    have hz : q.1 + r.1 = (0 : E) := congrArg Prod.fst hqr'
    have hν : q.2 + r.2 = (-1 : ℝ) := congrArg Prod.snd hqr'
    have hrq : r = ((-q.1, r.2) : E × ℝ) :=
      Prod.ext (eq_neg_of_add_eq_zero_right hz) rfl
    have h₁ : recessionFn f q.1 ≤ ((q.2 : ℝ) : EReal) := recessionFn_le_coe_iff.2 hq
    have h₂ : recessionFn g (-q.1) ≤ ((r.2 : ℝ) : EReal) := by
      refine recessionFn_le_coe_iff.2 ?_
      rwa [hrq] at hr
    have hsum : recessionFn f q.1 + recessionFn g (-q.1) ≤ 0 := by
      have hadd := add_le_add h₁ h₂
      rw [← EReal.coe_add, hν] at hadd
      refine hadd.trans ?_
      rw [← EReal.coe_zero, EReal.coe_le_coe_iff]
      norm_num
    have hsym := h q.1 hsum
    have hA : ((-q.2 : ℝ) : EReal) ≤ recessionFn f (-q.1) :=
      le_recessionFn_of_neg_le hf.proper (by simp only [neg_neg]; exact h₁)
    have hB : ((-r.2 : ℝ) : EReal) ≤ recessionFn g q.1 :=
      le_recessionFn_of_neg_le hg.proper (by simp only [neg_neg]; exact h₂)
    have hcontra : (((-q.2 + -r.2 : ℝ)) : EReal) ≤ 0 := by
      refine le_trans ?_ hsym
      rw [EReal.coe_add]
      exact add_le_add hA hB
    have hval : -q.2 + -r.2 = (1 : ℝ) := by rw [← neg_add, hν]; norm_num
    rw [hval, ← EReal.coe_zero, EReal.coe_le_coe_iff] at hcontra
    linarith
  have hproper : ProperConvex (infConv f g) := by
    refine ⟨?_, hnebot⟩
    rw [convexDom_infConv]
    exact hf.proper.convexDom_nonempty.add hg.proper.convexDom_nonempty
  refine ⟨hepi, ClosedProperConvexFn.of_isClosed_epi (convexFn_infConv hf.convex hg.convex)
    (by rw [hepi]; exact hclosed) hproper, ?_⟩
  -- the recession function of an infimal convolute
  have hepilike₂ : IsEpiLike (epi (recessionFn f) + epi (recessionFn g)) := by
    rw [epi_recessionFn, epi_recessionFn, ← hrecset, ← hepi]
    exact isEpiLike_recessionCone_epi _
  refine epi_injective ?_
  have hL : epi (recessionFn (infConv f g)) = recessionCone (epi f) + recessionCone (epi g) := by
    rw [epi_recessionFn, hepi, hrecset]
  have hR : epi (infConv (recessionFn f) (recessionFn g))
      = recessionCone (epi f) + recessionCone (epi g) := by
    rw [epi_infConv hepilike₂, epi_recessionFn, epi_recessionFn]
  rw [hL, hR]

omit [FiniteDimensional ℝ E] in
/-- Let $f$ and $g$ be proper. If $(f0^+)(z) + (g0^+)(-z) > 0$ for every $z \neq 0$, then the set of
directions of joint recession is symmetric: $(f0^+)(-z) + (g0^+)(z) \le 0$ whenever
$(f0^+)(z) + (g0^+)(-z) \le 0$, because the set is then $\{0\}$. -/
theorem recessionFn_symm_of_recessionFn_add_pos (hpf : ProperConvex f) (hpg : ProperConvex g)
    (h : ∀ z : E, z ≠ 0 → 0 < recessionFn f z + recessionFn g (-z)) :
    ∀ z : E, recessionFn f z + recessionFn g (-z) ≤ 0 →
      recessionFn f (-z) + recessionFn g z ≤ 0 := by
  intro z hz
  rcases eq_or_ne z 0 with rfl | hne
  · refine le_of_eq ?_
    rw [neg_zero, recessionFn_apply_zero hpf, recessionFn_apply_zero hpg, add_zero]
  · exact absurd hz (not_le.2 (h z hne))

/-- Let $E$ be a finite-dimensional real normed space and $f$, $g$ closed proper convex functions on
$E$ with
$$(f0^+)(z) + (g0^+)(-z) > 0 \quad \text{for every } z \neq 0.$$
Then $\operatorname{epi}(f \mathbin{\square} g) = \operatorname{epi} f + \operatorname{epi} g$,
$f \mathbin{\square} g$ is a closed proper convex function, and $(f \mathbin{\square} g)0^+ =
f0^+ \mathbin{\square} g0^+$.

The epigraph identity is the statement that the infimum is attained: a sum of epigraphs is an
epigraph exactly when every infimum defining $f \mathbin{\square} g$ is attained. The hypothesis
is stronger than needed: it suffices that the set of directions of joint recession is symmetric,
not that it is $\{0\}$. This result is a special case of
`ConvexAnalysis.closedProperConvexFn_infConv_of_recessionFn_symm`, through
`ConvexAnalysis.recessionFn_symm_of_recessionFn_add_pos`. -/
theorem closedProperConvexFn_infConv (hf : ClosedProperConvexFn f) (hg : ClosedProperConvexFn g)
    (h : ∀ z : E, z ≠ 0 → 0 < recessionFn f z + recessionFn g (-z)) :
    epi (infConv f g) = epi f + epi g ∧ ClosedProperConvexFn (infConv f g) ∧
      recessionFn (infConv f g) = infConv (recessionFn f) (recessionFn g) :=
  closedProperConvexFn_infConv_of_recessionFn_symm hf hg
    (recessionFn_symm_of_recessionFn_add_pos hf.proper hg.proper h)

/-- Under the hypotheses of `ConvexAnalysis.closedProperConvexFn_infConv_of_recessionFn_symm`, let
$x \in E$ and $\mu \in \mathbb{R}$ with $(f \mathbin{\square} g)(x) \le \mu$. Then there are
$y \in E$ and real numbers $\nu$, $\rho$ with $\nu + \rho = \mu$, $f(y) \le \nu$ and
$g(x - y) \le \rho$.

The statement also contains the equation $y + (x - y) = x$, which always holds. -/
theorem exists_add_eq_of_infConv_le_of_recessionFn_symm (hf : ClosedProperConvexFn f)
    (hg : ClosedProperConvexFn g)
    (h : ∀ z : E, recessionFn f z + recessionFn g (-z) ≤ 0 →
      recessionFn f (-z) + recessionFn g z ≤ 0) {x : E} {μ : ℝ}
    (hμ : infConv f g x ≤ (μ : EReal)) :
    ∃ (y : E) (ν ρ : ℝ), y + (x - y) = x ∧ ν + ρ = μ ∧ f y ≤ (ν : EReal) ∧
      g (x - y) ≤ (ρ : EReal) := by
  obtain ⟨hepi, -, -⟩ := closedProperConvexFn_infConv_of_recessionFn_symm hf hg h
  have hmem : ((x, μ) : E × ℝ) ∈ epi f + epi g := hepi ▸ mk_mem_epi.2 hμ
  obtain ⟨q, hq, r, hr, hqr⟩ := hmem
  have hqr' : q + r = ((x, μ) : E × ℝ) := hqr
  have hx : q.1 + r.1 = x := congrArg Prod.fst hqr'
  have hν : q.2 + r.2 = μ := congrArg Prod.snd hqr'
  refine ⟨q.1, q.2, r.2, by rw [← hx]; abel, hν, hq, ?_⟩
  have hr1 : x - q.1 = r.1 := by rw [← hx]; abel
  rw [hr1]
  exact hr

/-- Under the hypotheses of `ConvexAnalysis.closedProperConvexFn_infConv`, let $x \in E$ and
$\mu \in \mathbb{R}$ with $(f \mathbin{\square} g)(x) \le \mu$. Then there are $y \in E$ and
real numbers $\nu$, $\rho$ with $\nu + \rho = \mu$, $f(y) \le \nu$ and $g(x - y) \le \rho$.

The statement also contains the equation $y + (x - y) = x$, which always holds. -/
theorem exists_add_eq_of_infConv_le (hf : ClosedProperConvexFn f) (hg : ClosedProperConvexFn g)
    (h : ∀ z : E, z ≠ 0 → 0 < recessionFn f z + recessionFn g (-z)) {x : E} {μ : ℝ}
    (hμ : infConv f g x ≤ (μ : EReal)) :
    ∃ (y : E) (ν ρ : ℝ), y + (x - y) = x ∧ ν + ρ = μ ∧ f y ≤ (ν : EReal) ∧
      g (x - y) ≤ (ρ : EReal) :=
  exists_add_eq_of_infConv_le_of_recessionFn_symm hf hg
    (recessionFn_symm_of_recessionFn_add_pos hf.proper hg.proper h) hμ

end InfConvFn

/-! ### Sums of functions -/

section AddFn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f g : E → EReal}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- If $f$ and $g$ never take the value $-\infty$, then $f + g$ never takes the value $-\infty$. -/
theorem add_ne_bot (hf : ∀ x, f x ≠ ⊥) (hg : ∀ x, g x ≠ ⊥) (x : E) : (f + g) x ≠ ⊥ := by
  rw [Pi.add_apply]
  exact EReal.add_ne_bot_iff.2 ⟨hf x, hg x⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- If $f$ and $g$ are proper and $\operatorname{dom}(f + g)$ is nonempty, then $f + g$ is proper.
-/
theorem ProperConvex.add (hf : ProperConvex f) (hg : ProperConvex g)
    (hne : (convexDom (f + g)).Nonempty) :
    ProperConvex (f + g) := ⟨hne, add_ne_bot hf.ne_bot hg.ne_bot⟩

omit [FiniteDimensional ℝ E] in
/-- Let $E$ be a real normed space and $f$, $g$ closed proper convex functions on $E$ such that
$f + g$ is not identically $+\infty$, that is, $\operatorname{dom} f \cap \operatorname{dom} g$
is nonempty. Then $f + g$ is a closed proper convex function.

The hypothesis is the nonemptiness of `convexDom (f + g)`. Lower semicontinuity of the sum is
Mathlib's `LowerSemicontinuous.add'`. Its hypothesis of continuity of addition holds because
neither summand takes the value $-\infty$, so addition in `EReal` is continuous at every pair of
values that occurs. -/
theorem ClosedProperConvexFn.add (hf : ClosedProperConvexFn f) (hg : ClosedProperConvexFn g)
    (hne : (convexDom (f + g)).Nonempty) : ClosedProperConvexFn (f + g) := by
  have hbot : ∀ x, (f + g) x ≠ ⊥ := add_ne_bot hf.proper.ne_bot hg.proper.ne_bot
  refine ⟨hf.convex.add hg.convex hf.proper.ne_bot hg.proper.ne_bot, ?_, ⟨hne, hbot⟩⟩
  rw [closedConvex_iff_lowerSemicontinuous hbot]
  exact LowerSemicontinuous.add' hf.lowerSemicontinuous hg.lowerSemicontinuous fun x =>
    EReal.continuousAt_add (Or.inr (hg.proper.ne_bot x)) (Or.inl (hf.proper.ne_bot x))

omit [FiniteDimensional ℝ E] in
/-- Let $E$ be a real normed space and $g_i$, $i \in s$, finitely many closed proper convex
functions on $E$ whose effective domains have a common point $x_0$. Then $\sum_{i \in s} g_i$ is
a closed proper convex function.

The binary rule needs a point of the effective domain at each step. So the induction proves the
conclusion together with $x_0 \in \operatorname{dom} \sum_{i \in s} g_i$. -/
theorem closedProperConvexFn_finsetSum {ι : Type*} {s : Finset ι} {g : ι → E → EReal}
    (hg : ∀ i ∈ s, ClosedProperConvexFn (g i)) {x₀ : E} (hx₀ : ∀ i ∈ s, x₀ ∈ convexDom (g i)) :
    ClosedProperConvexFn (∑ i ∈ s, g i) := by
  have key : ∀ t : Finset ι,
      (∀ i ∈ t, ClosedProperConvexFn (g i)) → (∀ i ∈ t, x₀ ∈ convexDom (g i)) →
      ClosedProperConvexFn (∑ i ∈ t, g i) ∧ x₀ ∈ convexDom (∑ i ∈ t, g i) := by
    intro t
    induction t using Finset.cons_induction with
    | empty =>
      intro _ _
      have h0 : (∑ _i ∈ (∅ : Finset ι), g _i) = fun _ : E => (0 : EReal) := by
        funext x; simp
      rw [h0]
      refine ⟨⟨convexFn_const 0, ?_, ⟨⟨0, ?_⟩, fun _ => by simp⟩⟩, ?_⟩
      · exact (closedConvex_iff_lowerSemicontinuous (f := fun _ : E => (0 : EReal))
          fun _ => by simp).2 lowerSemicontinuous_const
      · rw [mem_convexDom]; exact lt_of_le_of_ne le_top (by simp)
      · rw [mem_convexDom]; exact lt_of_le_of_ne le_top (by simp)
    | cons i t hi ih =>
      intro hc hd
      obtain ⟨hall, hdomt⟩ := ih (fun j hj => hc j (Finset.mem_cons_of_mem hj))
        (fun j hj => hd j (Finset.mem_cons_of_mem hj))
      have hi₀ : x₀ ∈ convexDom (g i) := hd i (Finset.mem_cons_self i t)
      have hmem : x₀ ∈ convexDom (g i + ∑ j ∈ t, g j) := by
        rw [mem_convexDom, Pi.add_apply]
        exact EReal.add_lt_top (mem_convexDom.1 hi₀).ne (mem_convexDom.1 hdomt).ne
      rw [Finset.sum_cons]
      exact ⟨ClosedProperConvexFn.add (hc i (Finset.mem_cons_self i t)) hall ⟨x₀, hmem⟩, hmem⟩
  exact (key s hg hx₀).1

omit [FiniteDimensional ℝ E] in
/-- Let $E$ be a real normed space and $f$, $g$ closed proper convex functions on $E$ such that
$\operatorname{dom} f \cap \operatorname{dom} g$ is nonempty. Then
$$(f + g)0^+ = f0^+ + g0^+.$$

Both sides are limits of difference quotients based at one common point of
$\operatorname{dom} f \cap \operatorname{dom} g$, and the difference quotients add up
(`EReal.coe_mul_sub_add_coe_mul_sub`). Closedness is what makes a single base point enough. -/
theorem recessionFn_add (hf : ClosedProperConvexFn f) (hg : ClosedProperConvexFn g)
    (hne : (convexDom (f + g)).Nonempty) :
    recessionFn (f + g) = recessionFn f + recessionFn g := by
  obtain ⟨x, hx⟩ := hne
  have hsum : ClosedProperConvexFn (f + g) := hf.add hg ⟨x, hx⟩
  have hdom : convexDom (f + g) = convexDom f ∩ convexDom g :=
      convexDom_add hf.proper.ne_bot hg.proper.ne_bot
  have hxfg : x ∈ convexDom f ∩ convexDom g := hdom ▸ hx
  obtain ⟨p, hp⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hf.proper.ne_bot x) hxfg.1
  obtain ⟨q, hq⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hg.proper.ne_bot x) hxfg.2
  funext y
  have h1 := tendsto_coe_inv_mul_sub_atTop hf.convex hf.isClosed_epi hf.proper.ne_bot hxfg.1 y
  have h2 := tendsto_coe_inv_mul_sub_atTop hg.convex hg.isClosed_epi hg.proper.ne_bot hxfg.2 y
  have h3 := tendsto_coe_inv_mul_sub_atTop hsum.convex hsum.isClosed_epi hsum.proper.ne_bot hx y
  have hcont : ContinuousAt (fun r : EReal × EReal => r.1 + r.2)
      (recessionFn f y, recessionFn g y) :=
    EReal.continuousAt_add (Or.inr (recessionFn_ne_bot hg.proper y))
      (Or.inl (recessionFn_ne_bot hf.proper y))
  have hadd : Tendsto (fun a : ℝ => ((a⁻¹ : ℝ) : EReal) * (f (x + a • y) - f x)
      + ((a⁻¹ : ℝ) : EReal) * (g (x + a • y) - g x)) atTop
      (𝓝 (recessionFn f y + recessionFn g y)) := hcont.tendsto.comp (h1.prodMk_nhds h2)
  have heq : (fun a : ℝ => ((a⁻¹ : ℝ) : EReal) * (f (x + a • y) - f x)
      + ((a⁻¹ : ℝ) : EReal) * (g (x + a • y) - g x))
      =ᶠ[atTop] fun a : ℝ => ((a⁻¹ : ℝ) : EReal) * ((f + g) (x + a • y) - (f + g) x) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    have hx0 : (f + g) x = ((p + q : ℝ) : EReal) := by
      rw [Pi.add_apply, hp, hq, EReal.coe_add]
    rw [Pi.add_apply f g (x + a • y), hx0, hp, hq]
    exact EReal.coe_mul_sub_add_coe_mul_sub (by positivity) (hf.proper.ne_bot _)
      (hg.proper.ne_bot _) p q
  exact tendsto_nhds_unique h3 (Filter.Tendsto.congr' heq hadd)

/-- Let $E$ be a finite-dimensional real normed space and $f$, $g$ proper convex functions on $E$
such that some $x$ lies in $\operatorname{ri}(\operatorname{dom} f) \cap
\operatorname{ri}(\operatorname{dom} g)$. Then the lower semicontinuous hull of $f + g$ is the
sum of the lower semicontinuous hulls of $f$ and $g$.

Each of the three hulls at a point is a limit along the same segment from $x$. The point $x$
lies in $\operatorname{ri}(\operatorname{dom}(f + g))$, because the relative interior of an
intersection of convex sets with a common relative interior point is the intersection of the
relative interiors. -/
theorem lscHull_add (hf : ConvexFn f) (hpf : ProperConvex f) (hg : ConvexFn g)
    (hpg : ProperConvex g)
    {x : E} (hxf : x ∈ ri (convexDom f)) (hxg : x ∈ ri (convexDom g)) :
    lscHull (f + g) = lscHull f + lscHull g := by
  have hsum : ConvexFn (f + g) := hf.add hg hpf.ne_bot hpg.ne_bot
  have hx : x ∈ ri (convexDom (f + g)) := by
    rw [convexDom_add hpf.ne_bot hpg.ne_bot,
      Convex.relint_inter hf.convex_convexDom hg.convex_convexDom ⟨x, hxf, hxg⟩]
    exact ⟨hxf, hxg⟩
  funext y
  have h1 := hf.tendsto_lscHull_along_segment_relint hxf y
  have h2 := hg.tendsto_lscHull_along_segment_relint hxg y
  have h3 := hsum.tendsto_lscHull_along_segment_relint hx y
  have hcont : ContinuousAt (fun r : EReal × EReal => r.1 + r.2) (lscHull f y, lscHull g y) :=
    EReal.continuousAt_add (Or.inr (hg.lscHull_ne_bot hpg y))
      (Or.inl (hf.lscHull_ne_bot hpf y))
  exact tendsto_nhds_unique h3 (hcont.tendsto.comp (h1.prodMk_nhds h2))

/-- Let $E$ be a finite-dimensional real normed space and $f$, $g$ proper convex functions on $E$
such that some $x$ lies in $\operatorname{ri}(\operatorname{dom} f) \cap
\operatorname{ri}(\operatorname{dom} g)$. Then
$$\operatorname{cl}(f + g) = \operatorname{cl} f + \operatorname{cl} g.$$

Here $\operatorname{cl}$ is the closure of a convex function, `ConvexAnalysis.convexCl`. -/
theorem convexCl_add (hf : ConvexFn f) (hpf : ProperConvex f) (hg : ConvexFn g)
    (hpg : ProperConvex g)
    {x : E} (hxf : x ∈ ri (convexDom f)) (hxg : x ∈ ri (convexDom g)) :
    convexCl (f + g) = convexCl f + convexCl g := by
  have hxfd : x ∈ convexDom f := intrinsicInterior_subset hxf
  have hxgd : x ∈ convexDom g := intrinsicInterior_subset hxg
  have hne : (convexDom (f + g)).Nonempty := by
    refine ⟨x, ?_⟩
    rw [convexDom_add hpf.ne_bot hpg.ne_bot]
    exact ⟨hxfd, hxgd⟩
  have hsum : ConvexFn (f + g) := hf.add hg hpf.ne_bot hpg.ne_bot
  rw [hsum.convexCl_eq_lscHull (ProperConvex.add hpf hpg hne), hf.convexCl_eq_lscHull hpf,
    hg.convexCl_eq_lscHull hpg]
  exact lscHull_add hf hpf hg hpg hxf hxg

end AddFn

/-! ### Pointwise suprema -/

section SupFn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} {f : ι → E → EReal}

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Let $(f_i)_{i \in I}$ be functions on a normed additive group whose epigraphs are closed. Then
the pointwise supremum $\sup_i f_i$ has a closed epigraph, because its epigraph is the
intersection of the epigraphs of the $f_i$. No other hypothesis is needed. -/
theorem isClosed_epi_iSup (hc : ∀ i, IsClosed (epi (f i))) :
    IsClosed (epi fun z => ⨆ i, f i z) := by
  rw [epi_iSup]
  exact isClosed_iInter hc

omit [FiniteDimensional ℝ E] in
/-- Let $E$ be a real normed space and $(f_i)_{i \in I}$ convex functions on $E$ with closed
epigraphs, and suppose that the epigraph of $\sup_i f_i$ is nonempty. Then
$$\Bigl(\sup_i f_i\Bigr)0^+ = \sup_i\, (f_i 0^+).$$

The epigraph of a recession function is the recession cone of the epigraph
(`ConvexAnalysis.epi_recessionFn`), so this is the rule for the recession cone of an
intersection. -/
theorem recessionFn_iSup (hconv : ∀ i, ConvexFn (f i)) (hc : ∀ i, IsClosed (epi (f i)))
    (hne : (epi fun z => ⨆ i, f i z).Nonempty) :
    recessionFn (fun z => ⨆ i, f i z) = fun z => ⨆ i, recessionFn (f i) z := by
  rw [epi_iSup] at hne
  refine epi_injective ?_
  rw [epi_recessionFn, epi_iSup, epi_iSup,
    recessionCone_iInter (fun i => (hconv i).convex_epi) hc hne]
  exact iInter_congr fun i => (epi_recessionFn (f i)).symm

/-- Let $E$ be a finite-dimensional real normed space and $(f_i)_{i \in I}$ convex functions on $E$.
Let $x$ be a point of $\operatorname{ri}(\operatorname{dom} f_i)$ for every $i$, with
$\sup_i f_i(x) < +\infty$. Then the lower semicontinuous hull of $\sup_i f_i$ is the pointwise
supremum of the lower semicontinuous hulls of the $f_i$.

For every real $\mu > \sup_i f_i(x)$, the point $(x, \mu)$ lies in
$\operatorname{ri}(\operatorname{epi} f_i)$ for every $i$. This common relative interior point
of the epigraphs lets the closure pass inside the intersection. -/
theorem lscHull_iSup (hconv : ∀ i, ConvexFn (f i)) {x : E} (hx : ∀ i, x ∈ ri (convexDom (f i)))
    (hfin : (⨆ i, f i x) < ⊤) :
    lscHull (fun z => ⨆ i, f i z) = fun z => ⨆ i, lscHull (f i) z := by
  obtain ⟨μ, hμ, -⟩ := EReal.lt_iff_exists_real_btwn.1 hfin
  refine epi_injective ?_
  rw [epi_lscHull, epi_iSup, epi_iSup,
    Convex.closure_iInter (fun i => (hconv i).convex_epi)
      ⟨(x, μ), mem_iInter.2 fun i => by
        rw [(hconv i).relint_epi]
        exact ⟨hx i, lt_of_le_of_lt (le_iSup (fun j => f j x) i) hμ⟩⟩]
  exact iInter_congr fun i => (epi_lscHull (f i)).symm

end SupFn

/-! ### Composition with a linear map -/

section CompLinFn

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] {g : G → EReal}

omit [FiniteDimensional ℝ G] in
/-- Let $E$ be a finite-dimensional real normed space, $G$ a real normed space, $g$ a function on
$G$ with closed epigraph, and $A : E \to G$ a linear map. Then $gA = g \circ A$ has a closed
epigraph.

No relative interior hypothesis is needed: $\operatorname{epi}(gA)$ is the preimage of
$\operatorname{epi} g$ under the map $(x, \mu) \mapsto (Ax, \mu)$, which is continuous because
$E$ is finite-dimensional. -/
theorem isClosed_epi_compLin (hc : IsClosed (epi g)) (A : E →ₗ[ℝ] G) :
    IsClosed (epi (compLin g A)) := by
  rw [epi_compLin]
  exact hc.preimage (prodMapId A).continuous_of_finiteDimensional

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ G] in
/-- Let $E$ and $G$ be real normed spaces, $g$ a convex function on $G$ with closed epigraph, and
$A : E \to G$ a linear map, and suppose that $\operatorname{dom}(gA)$ is nonempty. Then
$$(gA)0^+ = (g0^+)A.$$

The epigraph of $(gA)0^+$ is the recession cone of a preimage of $\operatorname{epi} g$, so this
is `ConvexAnalysis.recessionCone_preimage` read through `ConvexAnalysis.epi_recessionFn`. -/
theorem recessionFn_compLin (hg : ConvexFn g) (hc : IsClosed (epi g)) (A : E →ₗ[ℝ] G)
    (hne : (convexDom (compLin g A)).Nonempty) :
    recessionFn (compLin g A) = compLin (recessionFn g) A := by
  refine epi_injective ?_
  rw [epi_recessionFn, epi_compLin, epi_compLin, epi_recessionFn]
  refine recessionCone_preimage (prodMapId A) hg.convex_epi hc ?_
  obtain ⟨x, hx⟩ := hne
  obtain ⟨μ, hμ, -⟩ := EReal.lt_iff_exists_real_btwn.1 (mem_convexDom.1 hx)
  exact ⟨(x, μ), mk_mem_epi.2 hμ.le⟩

omit [FiniteDimensional ℝ E] in
/-- Let $G$ be a finite-dimensional real normed space, $g$ a convex function on $G$, and
$A : E \to G$ a linear map with $Ax \in \operatorname{ri}(\operatorname{dom} g)$. Then some
$(x', \mu)$ is mapped by $(x', \mu) \mapsto (Ax', \mu)$ into
$\operatorname{ri}(\operatorname{epi} g)$. -/
theorem preimage_relint_epi_nonempty (hg : ConvexFn g) (A : E →ₗ[ℝ] G) {x : E}
    (hx : A x ∈ ri (convexDom g)) : ((prodMapId A) ⁻¹' ri (epi g)).Nonempty := by
  obtain ⟨μ, hμ, -⟩ :=
    EReal.lt_iff_exists_real_btwn.1 (mem_convexDom.1 (intrinsicInterior_subset hx))
  refine ⟨(x, μ), ?_⟩
  rw [Set.mem_preimage, hg.relint_epi]
  exact ⟨hx, hμ⟩

/-- Let $E$ and $G$ be finite-dimensional real normed spaces, $g$ a convex function on $G$, and
$A : E \to G$ a linear map with $Ax \in \operatorname{ri}(\operatorname{dom} g)$ for some $x$.
Then the lower semicontinuous hull of $gA$ is the composition of the lower semicontinuous hull
of $g$ with $A$.

This is the rule for the closure of a preimage, applied to $\operatorname{epi} g$. -/
theorem lscHull_compLin (hg : ConvexFn g) (A : E →ₗ[ℝ] G) {x : E} (hx : A x ∈ ri (convexDom g)) :
    lscHull (compLin g A) = compLin (lscHull g) A := by
  refine epi_injective ?_
  rw [epi_lscHull, epi_compLin, epi_compLin, epi_lscHull]
  exact Convex.closure_preimage hg.convex_epi (prodMapId A)
    (preimage_relint_epi_nonempty hg A hx)

/-- Let $E$ and $G$ be finite-dimensional real normed spaces, $g$ a proper convex function on $G$,
and $A : E \to G$ a linear map with $Ax \in \operatorname{ri}(\operatorname{dom} g)$ for some
$x$. Then
$$\operatorname{cl}(gA) = (\operatorname{cl} g)A.$$

Here $\operatorname{cl}$ is the closure of a convex function, `ConvexAnalysis.convexCl`. -/
theorem convexCl_compLin (hg : ConvexFn g) (hp : ProperConvex g) (A : E →ₗ[ℝ] G) {x : E}
    (hx : A x ∈ ri (convexDom g)) : convexCl (compLin g A) = compLin (convexCl g) A := by
  have hcomp : ConvexFn (compLin g A) := convexFn_compLin A hg
  have hpc : ProperConvex (compLin g A) :=
    ⟨⟨x, by rw [convexDom_compLin, Set.mem_preimage]; exact intrinsicInterior_subset hx⟩,
      fun z => by rw [compLin_apply]; exact hp.ne_bot _⟩
  rw [hcomp.convexCl_eq_lscHull hpc, hg.convexCl_eq_lscHull hp]
  exact lscHull_compLin hg A hx

end CompLinFn

end ConvexAnalysis

/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Module.Dual`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Normed.Module.Annihilator
import Numlib.Analysis.Normed.Module.Complemented
import Numlib.Analysis.Normed.Module.DualSeparable

/-!
# When is the sum of two closed subspaces closed?

Let $G$ and $L$ be closed subspaces of a Banach space $E$ over $\mathbb{R}$ or $\mathbb{C}$. Write
$M^\perp \subseteq E^*$ for the annihilator of a subspace $M \subseteq E$, and $N^\perp \subseteq E$
for the coannihilator of a subspace $N \subseteq E^*$, as in
`Numlib.Analysis.Normed.Module.Annihilator`. Theorem 2.16 of [brezis2011functional] says that the
following four conditions are equivalent:

* (a) $G + L$ is closed in $E$;
* (b) $G^\perp + L^\perp$ is closed in $E^*$;
* (c) $G + L = (G^\perp \cap L^\perp)^\perp$;
* (d) $G^\perp + L^\perp = (G \cap L)^\perp$.

This module proves the theorem.

## Main results

* `Submodule.strongDualAnnihilator_inf_of_isClosed_sup`: (a) implies (d).
* `Submodule.closedBall_inter_topologicalClosure_sup_subset_closure_add`: the separation step of the
  proof that (b) implies (a). If $\|f|_{\overline{G + L}}\| \le C (\|f|_G\| + \|f|_L\|)$ for every
  functional $f$, then the ball of radius $1/C$ of $\overline{G + L}$ lies in the closure of
  $B_G + B_L$, where $B_G$ and $B_L$ are the closed unit balls of $G$ and $L$.
* `Submodule.isClosed_sup_of_isClosed_sup_strongDualAnnihilator`: (b) implies (a).
* `Submodule.tfae_isClosed_sup`: the four conditions are equivalent.

## Proof outline

For (a) ⇒ (d), a functional $f \in (G \cap L)^\perp$ gives the functional $a + b \mapsto f(a)$ on
$G + L$. It is bounded because a closed sum has a bounded decomposition, and its extension to $E$
splits $f$ into a part in $G^\perp$ and a part in $L^\perp$. For (b) ⇒ (a), the distance inequality
for closed sums, applied in $E^*$ to $G^\perp$ and $L^\perp$, and the formula
$\operatorname{dist}(f, M^\perp) = \|f|_M\|$ give the hypothesis of the separation step. An
open-mapping argument then shows that $(x, y) \mapsto x + y$ maps $G \times L$ onto
$\overline{G + L}$. The other implications follow from the formulas of Corollary 2.15 of
[brezis2011functional].

## Implementation notes

* This is a separate module from `Numlib.Analysis.Normed.Module.Annihilator` because the proof uses
  the open mapping theorem, in the form of `Submodule.exists_add_eq_norm_le_of_isClosed_sup` and
  `Submodule.exists_infDist_inf_le_of_isClosed_sup` (`Numlib.Analysis.Normed.Module.Complemented`)
  and of `ContinuousLinearMap.exists_preimage_norm_le_of_approx`
  (`Numlib.Analysis.Normed.Operator.Unbounded.Basic`). The parent module and its many users should
  not have to import these.
-/

open Metric

open scoped Pointwise

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Let $E$ be a Banach space over $\mathbb{R}$ or $\mathbb{C}$, and let $G$ and $L$ be closed
subspaces of $E$ such that $G + L$ is closed. Then
$$(G \cap L)^\perp = G^\perp + L^\perp.$$
This is the implication (a) ⇒ (d) of Theorem 2.16 of [brezis2011functional].

Given $f \in (G \cap L)^\perp$, the functional $a + b \mapsto f(a)$ on $G + L$ is well defined,
because two decompositions differ by an element of $G \cap L$. It is bounded by the bounded
decomposition `Submodule.exists_add_eq_norm_le_of_isClosed_sup`. A norm-preserving extension
$\psi$ of it to $E$ satisfies $f - \psi \in G^\perp$ and $\psi \in L^\perp$. -/
theorem strongDualAnnihilator_inf_of_isClosed_sup [CompleteSpace E] {G L : Submodule 𝕜 E}
    (hG : IsClosed (G : Set E)) (hL : IsClosed (L : Set E))
    (hGL : IsClosed ((G ⊔ L : Submodule 𝕜 E) : Set E)) :
    (G ⊓ L).strongDualAnnihilator = G.strongDualAnnihilator ⊔ L.strongDualAnnihilator := by
  refine le_antisymm (fun f hf => ?_)
    (sup_le (strongDualAnnihilator_anti inf_le_left) (strongDualAnnihilator_anti inf_le_right))
  obtain ⟨C, hC0, hC⟩ := exists_add_eq_norm_le_of_isClosed_sup G L hG hL hGL
  -- `f a` depends only on `a + b`, since `f` vanishes on `G ∩ L`
  have hwd : ∀ a ∈ G, ∀ b ∈ L, ∀ a' ∈ G, ∀ b' ∈ L, a + b = a' + b' → f a = f a' := by
    intro a ha b hb a' ha' b' hb' h
    have hmem : a - a' ∈ G ⊓ L := by
      refine ⟨G.sub_mem ha ha', ?_⟩
      have : a - a' = b' - b := by
        rw [sub_eq_sub_iff_add_eq_add, h, add_comm]
      rw [this]
      exact L.sub_mem hb' hb
    have := mem_strongDualAnnihilator.1 hf _ hmem
    rwa [map_sub, sub_eq_zero] at this
  -- a choice of decomposition for every element of `G + L`
  have hdec : ∀ z : ↥(G ⊔ L), ∃ a ∈ G, ∃ b ∈ L, (z : E) = a + b := fun z => by
    obtain ⟨a, ha, b, hb, h⟩ := mem_sup.1 z.2
    exact ⟨a, ha, b, hb, h.symm⟩
  choose a ha b hb hab using hdec
  let φ : ↥(G ⊔ L) →ₗ[𝕜] 𝕜 :=
    { toFun := fun z => f (a z)
      map_add' := fun z₁ z₂ => by
        have := hwd (a (z₁ + z₂)) (ha _) (b (z₁ + z₂)) (hb _) (a z₁ + a z₂)
          (G.add_mem (ha _) (ha _)) (b z₁ + b z₂) (L.add_mem (hb _) (hb _)) (by
            rw [← hab (z₁ + z₂), coe_add, hab z₁, hab z₂]
            abel)
        rw [this, map_add]
      map_smul' := fun c z => by
        have := hwd (a (c • z)) (ha _) (b (c • z)) (hb _) (c • a z) (G.smul_mem c (ha _))
          (c • b z) (L.smul_mem c (hb _)) (by rw [← hab (c • z), coe_smul, hab z, smul_add])
        simp only [RingHom.id_apply]
        rw [this, map_smul, smul_eq_mul] }
  -- `φ` is bounded, by the bounded decomposition
  have hφ : ∀ z : ↥(G ⊔ L), ‖φ z‖ ≤ C * ‖f‖ * ‖z‖ := fun z => by
    obtain ⟨a', ha', b', hb', hz, ha'n, -⟩ := hC z z.2
    have : φ z = f a' := hwd _ (ha z) _ (hb z) a' ha' b' hb' (by rw [← hab z, ← hz])
    rw [this]
    calc ‖f a'‖ ≤ ‖f‖ * ‖a'‖ := f.le_opNorm _
      _ ≤ ‖f‖ * (C * ‖(z : E)‖) := by gcongr
      _ = C * ‖f‖ * ‖z‖ := by rw [norm_coe]; ring
  obtain ⟨ψ, hψ, -⟩ := exists_extension_norm_eq (G ⊔ L) (φ.mkContinuous (C * ‖f‖) hφ)
  have hψ' : ∀ z : ↥(G ⊔ L), ψ z = f (a z) := hψ
  have hψG : ∀ x ∈ G, ψ x = f x := fun x hx => by
    rw [hψ' ⟨x, mem_sup_left hx⟩]
    exact hwd _ (ha _) _ (hb _) x hx 0 L.zero_mem (by rw [← hab, add_zero])
  have hψL : ∀ y ∈ L, ψ y = 0 := fun y hy => by
    rw [hψ' ⟨y, mem_sup_right hy⟩,
      hwd _ (ha _) _ (hb _) 0 G.zero_mem y hy (by rw [← hab, zero_add]), map_zero]
  have h1 : f - ψ ∈ G.strongDualAnnihilator :=
    mem_strongDualAnnihilator.2 fun x hx => by rw [sub_apply, hψG x hx, sub_self]
  have h2 : ψ ∈ L.strongDualAnnihilator := mem_strongDualAnnihilator.2 hψL
  rw [← sub_add_cancel f ψ]
  exact add_mem_sup h1 h2

open scoped ComplexOrder in
/-- The separation step of Theorem 2.16 of [brezis2011functional], formula (25). Let $G$ and $L$ be
subspaces of a normed space $E$ over $\mathbb{R}$ or $\mathbb{C}$, let $Y = \overline{G + L}$,
and let $C > 0$. Suppose that every $f \in E^*$ satisfies
$$\|f|_Y\| \le C (\|f|_G\| + \|f|_L\|).$$
Then every $x \in Y$ with $\|x\| \le 1/C$ lies in the closure of $B_G + B_L$, where $B_G$ and
$B_L$ are the closed unit balls of $G$ and $L$.

If not, `AbsConvex.exists_norm_apply_le_one_of_isClosed_of_notMem` separates $x$ from this
closed absolutely convex set by a functional $f_0$ with $|f_0| \le 1$ on the set and
$|f_0(x)| > 1$. Rotating $a \in B_G$ and $b \in B_L$ by scalars of modulus $1$ gives
$|f_0(a)| + |f_0(b)| = |f_0(a' + b')| \le 1$. Hence $\|f_0|_G\| + \|f_0|_L\| \le 1$ and
$|f_0(x)| \le \|f_0|_Y\| \, \|x\| \le C \cdot (1/C) = 1$, a contradiction. -/
theorem closedBall_inter_topologicalClosure_sup_subset_closure_add (G L : Submodule 𝕜 E) {C : ℝ}
    (hC : 0 < C)
    (h : ∀ f : StrongDual 𝕜 E, ‖f.comp (G ⊔ L).topologicalClosure.subtypeL‖ ≤
      C * (‖f.comp G.subtypeL‖ + ‖f.comp L.subtypeL‖)) :
    closedBall (0 : E) C⁻¹ ∩ (G ⊔ L).topologicalClosure ⊆
      closure ((G : Set E) ∩ closedBall 0 1 + (L : Set E) ∩ closedBall 0 1) := by
  -- the real structure of `E`, for the convexity of balls
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have : IsScalarTower ℝ 𝕜 E := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  set S : Set E := (G : Set E) ∩ closedBall 0 1 + (L : Set E) ∩ closedBall 0 1 with hS
  rintro x₀ ⟨hx₀n, hx₀Y⟩
  by_contra hx₀
  rw [mem_closedBall_zero_iff] at hx₀n
  have h0G : (0 : E) ∈ (G : Set E) ∩ closedBall 0 1 := ⟨G.zero_mem, mem_closedBall_self zero_le_one⟩
  have h0L : (0 : E) ∈ (L : Set E) ∩ closedBall 0 1 := ⟨L.zero_mem, mem_closedBall_self zero_le_one⟩
  -- `closure S` is nonempty, closed and absolutely convex
  have hGb : Balanced 𝕜 (G : Set E) := fun c _ => by
    rintro _ ⟨y, hy, rfl⟩
    exact G.smul_mem c hy
  have hLb : Balanced 𝕜 (L : Set E) := fun c _ => by
    rintro _ ⟨y, hy, rfl⟩
    exact L.smul_mem c hy
  have hGc : Convex ℝ (G : Set E) := fun x hx y hy r s _ _ _ => by
    rw [← algebraMap_smul 𝕜 r x, ← algebraMap_smul 𝕜 s y]
    exact G.add_mem (G.smul_mem _ hx) (G.smul_mem _ hy)
  have hLc : Convex ℝ (L : Set E) := fun x hx y hy r s _ _ _ => by
    rw [← algebraMap_smul 𝕜 r x, ← algebraMap_smul 𝕜 s y]
    exact L.add_mem (L.smul_mem _ hx) (L.smul_mem _ hy)
  have hK : AbsConvex 𝕜 (closure S) :=
    ⟨((hGb.inter balanced_closedBall_zero).add (hLb.inter balanced_closedBall_zero)).closure,
      convex_RCLike_iff_convex_real.2
        (((hGc.inter (convex_closedBall 0 1)).add (hLc.inter (convex_closedBall 0 1))).closure)⟩
  have hKne : (closure S).Nonempty := ⟨0, subset_closure ⟨0, h0G, 0, h0L, add_zero 0⟩⟩
  obtain ⟨f₀, hf₀K, hf₀x⟩ :=
    hK.exists_norm_apply_le_one_of_isClosed_of_notMem hKne isClosed_closure hx₀
  -- the rotation: `‖f₀ a‖ + ‖f₀ b‖ ≤ 1` on `B_G × B_L`
  have hsum : ∀ a ∈ (G : Set E) ∩ closedBall 0 1, ∀ b ∈ (L : Set E) ∩ closedBall 0 1,
      ‖f₀ a‖ + ‖f₀ b‖ ≤ 1 := by
    intro a ha b hb
    obtain ⟨c, hc1, hc⟩ := RCLike.exists_norm_eq_mul_self (f₀ a)
    obtain ⟨d, hd1, hd⟩ := RCLike.exists_norm_eq_mul_self (f₀ b)
    have hca : c • a ∈ (G : Set E) ∩ closedBall 0 1 := by
      refine ⟨G.smul_mem c ha.1, ?_⟩
      rw [mem_closedBall_zero_iff, norm_smul, hc1, one_mul]
      exact mem_closedBall_zero_iff.1 ha.2
    have hdb : d • b ∈ (L : Set E) ∩ closedBall 0 1 := by
      refine ⟨L.smul_mem d hb.1, ?_⟩
      rw [mem_closedBall_zero_iff, norm_smul, hd1, one_mul]
      exact mem_closedBall_zero_iff.1 hb.2
    have := hf₀K _ (subset_closure ⟨c • a, hca, d • b, hdb, rfl⟩)
    rwa [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← hc, ← hd, ← RCLike.ofReal_add,
      RCLike.norm_ofReal, abs_of_nonneg (by positivity)] at this
  -- hence `‖f₀|_G‖ + ‖f₀|_L‖ ≤ 1`
  have hL' : ∀ a ∈ (G : Set E) ∩ closedBall 0 1, ‖f₀.comp L.subtypeL‖ ≤ 1 - ‖f₀ a‖ := by
    intro a ha
    have h0 := hsum a ha 0 h0L
    rw [map_zero, norm_zero, add_zero] at h0
    refine ContinuousLinearMap.opNorm_le_of_unit_norm (by linarith) fun b hb => ?_
    have := hsum a ha b ⟨b.2, by rw [mem_closedBall_zero_iff, norm_coe, hb]⟩
    rw [ContinuousLinearMap.comp_apply, subtypeL_apply]
    linarith
  have hG' : ‖f₀.comp G.subtypeL‖ ≤ 1 - ‖f₀.comp L.subtypeL‖ := by
    have h0 := hL' 0 h0G
    rw [map_zero, norm_zero, sub_zero] at h0
    refine ContinuousLinearMap.opNorm_le_of_unit_norm (by linarith) fun a ha => ?_
    have := hL' a ⟨a.2, by rw [mem_closedBall_zero_iff, norm_coe, ha]⟩
    rw [ContinuousLinearMap.comp_apply, subtypeL_apply]
    linarith
  -- contradiction with the hypothesis at `f₀` and `x₀`
  have hx₀' : ‖f₀ x₀‖ ≤ ‖f₀.comp (G ⊔ L).topologicalClosure.subtypeL‖ * ‖x₀‖ := by
    have := (f₀.comp (G ⊔ L).topologicalClosure.subtypeL).le_opNorm ⟨x₀, hx₀Y⟩
    rwa [ContinuousLinearMap.comp_apply, subtypeL_apply] at this
  have hle : ‖f₀ x₀‖ ≤ 1 := by
    calc ‖f₀ x₀‖ ≤ ‖f₀.comp (G ⊔ L).topologicalClosure.subtypeL‖ * ‖x₀‖ := hx₀'
      _ ≤ (C * (‖f₀.comp G.subtypeL‖ + ‖f₀.comp L.subtypeL‖)) * C⁻¹ := by
          gcongr
          exact h f₀
      _ ≤ (C * 1) * C⁻¹ := by gcongr; linarith
      _ = 1 := by field_simp
  linarith

/-- Let $E$ be a Banach space over $\mathbb{R}$ or $\mathbb{C}$, and let $G$ and $L$ be closed
subspaces of $E$ such that $G^\perp + L^\perp$ is closed in $E^*$. Then $G + L$ is closed in
$E$. This is the implication (b) ⇒ (a) of Theorem 2.16 of [brezis2011functional].

Let $Y = \overline{G + L}$. The distance inequality
`Submodule.exists_infDist_inf_le_of_isClosed_sup` in the Banach space $E^*$ for $G^\perp$ and
$L^\perp$, read through $\operatorname{dist}(f, M^\perp) = \|f|_M\|$, gives
$\|f|_Y\| \le C (\|f|_G\| + \|f|_L\|)$. The separation step
`Submodule.closedBall_inter_topologicalClosure_sup_subset_closure_add` then puts the ball of
radius $1/C$ of $Y$ inside the closure of $B_G + B_L$. This is the approximation hypothesis of
the open-mapping step `ContinuousLinearMap.exists_preimage_norm_le_of_approx` for the map
$G \times L \to Y$, $(x, y) \mapsto x + y$. So this map is onto $Y$, that is,
$G + L = \overline{G + L}$. -/
theorem isClosed_sup_of_isClosed_sup_strongDualAnnihilator [CompleteSpace E]
    {G L : Submodule 𝕜 E} (hG : IsClosed (G : Set E)) (hL : IsClosed (L : Set E))
    (h : IsClosed ((G.strongDualAnnihilator ⊔ L.strongDualAnnihilator :
      Submodule 𝕜 (StrongDual 𝕜 E)) : Set (StrongDual 𝕜 E))) :
    IsClosed ((G ⊔ L : Submodule 𝕜 E) : Set E) := by
  set Y := (G ⊔ L).topologicalClosure with hYdef
  -- Steps 1–2: `‖f|_Y‖ ≤ C (‖f|_G‖ + ‖f|_L‖)`
  obtain ⟨C₀, hC₀⟩ := exists_infDist_inf_le_of_isClosed_sup G.strongDualAnnihilator
    L.strongDualAnnihilator (isClosed_strongDualAnnihilator G) (isClosed_strongDualAnnihilator L) h
  set C := max C₀ 1 with hCdef
  have hC : 0 < C := lt_of_lt_of_le one_pos (le_max_right _ _)
  have h24 : ∀ f : StrongDual 𝕜 E, ‖f.comp Y.subtypeL‖ ≤
      C * (‖f.comp G.subtypeL‖ + ‖f.comp L.subtypeL‖) := by
    intro f
    have := hC₀ f
    rw [← strongDualAnnihilator_sup, ← strongDualAnnihilator_topologicalClosure (G ⊔ L),
      infDist_strongDualAnnihilator, infDist_strongDualAnnihilator,
      infDist_strongDualAnnihilator] at this
    calc ‖f.comp Y.subtypeL‖ ≤ C₀ * (‖f.comp G.subtypeL‖ + ‖f.comp L.subtypeL‖) := this
      _ ≤ C * (‖f.comp G.subtypeL‖ + ‖f.comp L.subtypeL‖) := by
          gcongr
          exact le_max_left _ _
  -- Step 3: the separation step
  have h25 := closedBall_inter_topologicalClosure_sup_subset_closure_add G L hC h24
  -- Step 4: the addition map `G × L → Y` is onto
  have hGY : G ⊔ L ≤ Y := le_topologicalClosure _
  have := hG.completeSpace_coe
  have := hL.completeSpace_coe
  let T : G × L →L[𝕜] Y := (G.subtypeL.coprod L.subtypeL).codRestrict Y fun p =>
    hGY (add_mem_sup p.1.2 p.2.2)
  have hT : ∀ p : G × L, (T p : E) = p.1 + p.2 := fun p => rfl
  have happrox : ∀ y : Y, ∃ u : G × L, dist (T u) y ≤ 1 / 2 * ‖y‖ ∧ ‖u‖ ≤ C * ‖y‖ := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · exact ⟨0, by simp, by simp⟩
    have hy' : 0 < ‖y‖ := norm_pos_iff.2 hy
    set t : ℝ := C * ‖y‖ with ht
    have ht0 : 0 < t := by positivity
    -- `t⁻¹ • y` lies in the ball of radius `1/C` of `Y`, hence in `closure (B_G + B_L)`
    have hmem : ((t⁻¹ : ℝ) : 𝕜) • (y : E) ∈ closedBall (0 : E) C⁻¹ ∩ Y := by
      refine ⟨?_, Y.smul_mem _ y.2⟩
      rw [mem_closedBall_zero_iff, norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.2 ht0),
        norm_coe, ht, mul_inv, mul_assoc, inv_mul_cancel₀ hy'.ne', mul_one]
    obtain ⟨z, ⟨a, ha, b, hb, rfl⟩, hz⟩ :=
      Metric.mem_closure_iff.1 (h25 hmem) (1 / (2 * C)) (by positivity)
    refine ⟨((t : ℝ) : 𝕜) • (⟨a, ha.1⟩, ⟨b, hb.1⟩), ?_, ?_⟩
    · rw [Subtype.dist_eq, hT, dist_eq_norm]
      have hrw : (((t : ℝ) : 𝕜) • (⟨a, ha.1⟩, ⟨b, hb.1⟩) : G × L).1 +
          ((((t : ℝ) : 𝕜) • (⟨a, ha.1⟩, ⟨b, hb.1⟩) : G × L).2 : E) - y =
          ((t : ℝ) : 𝕜) • ((a + b) - ((t⁻¹ : ℝ) : 𝕜) • (y : E)) := by
        simp only [Prod.smul_fst, Prod.smul_snd, coe_smul, smul_sub, smul_add, smul_smul,
          ← RCLike.ofReal_mul, mul_inv_cancel₀ ht0.ne', RCLike.ofReal_one, one_smul]
      rw [hrw, norm_smul, RCLike.norm_ofReal, abs_of_pos ht0, ← dist_eq_norm, dist_comm]
      calc t * dist (((t⁻¹ : ℝ) : 𝕜) • (y : E)) (a + b) ≤ t * (1 / (2 * C)) := by gcongr
        _ = 1 / 2 * ‖y‖ := by rw [ht]; field_simp
    · rw [norm_smul, RCLike.norm_ofReal, abs_of_pos ht0, ht, Prod.norm_def]
      have ha1 : ‖(⟨a, ha.1⟩ : G)‖ ≤ 1 := by rw [← norm_coe]; exact mem_closedBall_zero_iff.1 ha.2
      have hb1 : ‖(⟨b, hb.1⟩ : L)‖ ≤ 1 := by rw [← norm_coe]; exact mem_closedBall_zero_iff.1 hb.2
      calc C * ‖y‖ * max ‖(⟨a, ha.1⟩ : G)‖ ‖(⟨b, hb.1⟩ : L)‖ ≤ C * ‖y‖ * 1 := by
            gcongr
            exact max_le ha1 hb1
        _ = C * ‖y‖ := mul_one _
  have hYle : Y ≤ G ⊔ L := fun y hy => by
    obtain ⟨u, hu, -⟩ := T.exists_preimage_norm_le_of_approx happrox ⟨y, hy⟩
    have : y = u.1 + u.2 := by rw [← hT, hu]
    rw [this]
    exact add_mem_sup u.1.2 u.2.2
  rw [le_antisymm hGY hYle]
  exact isClosed_topologicalClosure _

/-- Closed sums and annihilators. Let $E$ be a Banach space over $\mathbb{R}$ or $\mathbb{C}$, and
let $G$ and $L$ be closed subspaces of $E$. The following conditions are equivalent: (a) $G + L$
is closed; (b) $G^\perp + L^\perp$ is closed in $E^*$; (c)
$G + L = (G^\perp \cap L^\perp)^\perp$; (d) $G^\perp + L^\perp = (G \cap L)^\perp$. This is
Theorem 2.16 of [brezis2011functional]. -/
theorem tfae_isClosed_sup [CompleteSpace E] {G L : Submodule 𝕜 E} (hG : IsClosed (G : Set E))
    (hL : IsClosed (L : Set E)) :
    [IsClosed ((G ⊔ L : Submodule 𝕜 E) : Set E),
      IsClosed ((G.strongDualAnnihilator ⊔ L.strongDualAnnihilator :
        Submodule 𝕜 (StrongDual 𝕜 E)) : Set (StrongDual 𝕜 E)),
      G ⊔ L = (G.strongDualAnnihilator ⊓ L.strongDualAnnihilator).strongDualCoannihilator,
      G.strongDualAnnihilator ⊔ L.strongDualAnnihilator = (G ⊓ L).strongDualAnnihilator].TFAE := by
  tfae_have 1 → 4 := fun h => (strongDualAnnihilator_inf_of_isClosed_sup hG hL h).symm
  tfae_have 4 → 2 := fun h => by
    rw [h]
    exact isClosed_strongDualAnnihilator _
  tfae_have 2 → 1 := isClosed_sup_of_isClosed_sup_strongDualAnnihilator hG hL
  tfae_have 1 ↔ 3 := by
    rw [strongDualCoannihilator_inf_strongDualAnnihilator]
    refine ⟨fun h => h.submodule_topologicalClosure_eq.symm, fun h => ?_⟩
    rw [h]
    exact isClosed_topologicalClosure _
  tfae_finish

end Submodule

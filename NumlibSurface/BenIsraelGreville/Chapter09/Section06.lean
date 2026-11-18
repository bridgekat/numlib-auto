/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter09.Section05
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Minimal properties of generalized inverses

Section 9.6 of [benIsrael2003generalized] considers least-residual and
least-norm solutions for partial operators on Hilbert spaces. The extremal
inverse inverts the image of the carrier and vanishes perpendicular to
the full range.

## Deviations from the source

* **Equation (74)** gives the norm of the residual perpendicular to the
  range, since the infimum is a scalar.
* The necessity in **Theorem 6** follows by varying the candidate by
  vectors in the kernel, including when the kernel is nonclosed.
* **Exercise 44** uses $TT^*$ as the right Gram operator.
* **Exercise 48** uses the domain shift x₁ in the formula for the minimizer,
  consistently with the multiplier equation. The shift y₁ belongs to the
  codomain of the weighting operator S.
-/

namespace BenIsraelGreville.Chapter09

open LinearPMap
open scoped InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **Definition 4**, Equations (70)–(71) of [benIsrael2003generalized].
An extremal solution is a point in the operator's domain whose residual
norm is minimal among all domain points. -/
abbrev IsExtremalSolution (T : E →ₗ.[𝕜] F) (y : F) (x : T.domain) : Prop :=
  IsOperatorLeastSquaresSolution T y x

/-- **Definition 4** of [benIsrael2003generalized].
A least extremal solution has smaller norm than every distinct
extremal solution. -/
def IsLeastExtremalSolution (T : E →ₗ.[𝕜] F) (y : F) (x : T.domain) : Prop :=
  IsExtremalSolution T y x ∧
    ∀ z : T.domain, IsExtremalSolution T y z → z ≠ x → ‖(x : E)‖ < ‖(z : E)‖

/-- The extremal solution criterion in terms of the residual. -/
theorem isExtremalSolution_iff_residual_mem_orthogonal
    (T : E →ₗ.[𝕜] F) {y : F} {x : T.domain} :
    IsExtremalSolution T y x ↔ y - T x ∈ T.toFun.rangeᗮ :=
  isOperatorLeastSquaresSolution_iff T

private theorem starProjection_closure_eq_of_residual {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H] (S : Submodule 𝕜 H) {x z : H}
    (hz : z ∈ S) (hres : x - z ∈ Sᗮ) : S.topologicalClosure.starProjection x = z := by
  apply Submodule.eq_starProjection_of_mem_orthogonal (S.le_topologicalClosure hz)
  rwa [Submodule.orthogonal_closure]

private theorem sub_starProjection_closure_eq {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H] (S : Submodule 𝕜 H) (x : H) :
    x - S.topologicalClosure.starProjection x = Sᗮ.starProjection x := by
  symm
  apply Submodule.eq_starProjection_of_mem_orthogonal ?_ ?_
  · rw [← S.orthogonal_closure]
    exact S.topologicalClosure.sub_starProjection_mem_orthogonal x
  · rw [sub_sub_cancel, S.orthogonal_orthogonal_eq_closure]
    exact S.topologicalClosure.starProjection_apply_mem x

/-- **Equation (73)** of [benIsrael2003generalized].
A domain point is an extremal solution exactly when its image is the
orthogonal projection of the datum onto the closure of the range. -/
theorem isExtremalSolution_iff_apply_eq_projection [CompleteSpace F]
    (T : E →ₗ.[𝕜] F) {y : F} {x : T.domain} :
    IsExtremalSolution T y x ↔ T x = T.toFun.range.topologicalClosure.starProjection y := by
  rw [isExtremalSolution_iff_residual_mem_orthogonal]
  refine ⟨fun h => (starProjection_closure_eq_of_residual T.toFun.range ⟨x, rfl⟩ h).symm, ?_⟩
  intro he
  rw [he, sub_starProjection_closure_eq]
  exact T.toFun.rangeᗮ.starProjection_apply_mem y

private theorem iInf_residual_eq_infDist_range (T : E →ₗ.[𝕜] F) (y : F) :
    (⨅ x : T.domain, ‖T x - y‖) = Metric.infDist y (T.toFun.range : Set F) := by
  rw [Metric.infDist_eq_iInf]
  have h₁ : BddBelow (Set.range fun x : T.domain => ‖T x - y‖) :=
    ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩
  have h₂ : BddBelow (Set.range fun z : T.toFun.range => dist y (z : F)) :=
    ⟨0, Set.forall_mem_range.mpr fun _ => dist_nonneg⟩
  refine le_antisymm (le_ciInf fun z => ?_) (le_ciInf fun x => ?_)
  · obtain ⟨x, hx⟩ := z.2
    have he : ‖T x - y‖ = dist y (z : F) := by rw [dist_comm, dist_eq_norm, ← hx]; rfl
    exact ciInf_le_of_le h₁ x he.le
  · refine ciInf_le_of_le h₂ (⟨T x, x, rfl⟩ : T.toFun.range) ?_
    rw [dist_comm, dist_eq_norm]

/-- **Theorem 5**, Equations (72)–(74) of [benIsrael2003generalized].
Extremal solutions exist exactly when the fitted value lies in the
range. The infimum of the residual norms is the norm of the orthogonal
residual. -/
theorem theorem_5 [CompleteSpace F] (T : E →ₗ.[𝕜] F) (y : F) :
    ((∃ x : T.domain, IsExtremalSolution T y x) ↔
      T.toFun.range.topologicalClosure.starProjection y ∈ T.toFun.range) ∧
    (⨅ x : T.domain, ‖T x - y‖) = ‖T.toFun.rangeᗮ.starProjection y‖ := by
  constructor
  · constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, (isExtremalSolution_iff_apply_eq_projection T).mp hx⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, (isExtremalSolution_iff_apply_eq_projection T).mpr hx⟩
  · rw [iInf_residual_eq_infDist_range]
    rw [← Metric.infDist_closure]
    have h := (isBestApprox_starProjection T.toFun.range.topologicalClosure y).norm_sub_eq_infDist
    rw [sub_starProjection_closure_eq] at h
    exact h.symm

/-- Two extremal solutions of the same equation have equal fitted values,
so their difference is in the kernel. -/
theorem extremalSolutions_sub_mem_ker [CompleteSpace F] {T : E →ₗ.[𝕜] F}
    {y : F} {x z : T.domain} (hx : IsExtremalSolution T y x)
    (hz : IsExtremalSolution T y z) : (x : E) - (z : E) ∈ T.ker := by
  exact T.sub_mem_ker_iff.mpr (((isExtremalSolution_iff_apply_eq_projection T).mp hx).trans
    ((isExtremalSolution_iff_apply_eq_projection T).mp hz).symm)

/-- **Lemma 4**, Equation (75) of [benIsrael2003generalized].
Extremal solutions have the same orthogonal complement component.
Their projections onto the kernel closure belong to the kernel
simultaneously. -/
theorem lemma_4 [CompleteSpace E] [CompleteSpace F] {T : E →ₗ.[𝕜] F} {y : F}
    {x z : T.domain} (hx : IsExtremalSolution T y x) (hz : IsExtremalSolution T y z) :
    T.kerᗮ.starProjection x = T.kerᗮ.starProjection z ∧
      (T.ker.topologicalClosure.starProjection x ∈ T.ker ↔
        T.ker.topologicalClosure.starProjection z ∈ T.ker) := by
  have hk := extremalSolutions_sub_mem_ker hx hz
  have hc : (x : E) - (z : E) ∈ T.ker.topologicalClosure := T.ker.le_topologicalClosure hk
  have hq : (x : E) - (z : E) ∈ (T.kerᗮ)ᗮ := by
    rwa [T.ker.orthogonal_orthogonal_eq_closure]
  constructor
  · have he := (T.kerᗮ.starProjection_apply_eq_zero_iff).mpr hq
    rwa [_root_.map_sub, sub_eq_zero] at he
  · have he := (T.ker.topologicalClosure.starProjection_eq_self_iff).mpr hc
    rw [_root_.map_sub] at he
    constructor
    · intro h
      have h' : T.ker.topologicalClosure.starProjection z =
          T.ker.topologicalClosure.starProjection x - ((x : E) - (z : E)) := by rw [← he]; abel
      rw [h']
      exact T.ker.sub_mem h hk
    · intro h
      have h' : T.ker.topologicalClosure.starProjection x =
          T.ker.topologicalClosure.starProjection z + ((x : E) - (z : E)) := by rw [← he]; abel
      rw [h']
      exact T.ker.add_mem h hk

/-- **Definition 4**, least-norm characterization.
An extremal solution is least precisely when it is perpendicular to
the original kernel. -/
theorem isLeastExtremalSolution_iff {T : E →ₗ.[𝕜] F} {y : F} {x : T.domain} :
    IsLeastExtremalSolution T y x ↔ IsExtremalSolution T y x ∧ (x : E) ∈ T.kerᗮ := by
  constructor
  · rintro ⟨hx, hmin⟩
    refine ⟨hx, ?_⟩
    have h : IsBestApprox (T.ker : Set E) (x : E) (0 : E) := by
      refine ⟨T.ker.zero_mem, fun k hk => ?_⟩
      let k' : T.domain := ⟨k, T.ker_le_domain hk⟩
      have hT : T k' = 0 := T.coe_mem_ker_iff.mp hk
      have he : T (x - k') = T x := by rw [T.map_sub, hT, sub_zero]
      have hx' : IsExtremalSolution T y (x - k') := by
        rw [isExtremalSolution_iff_residual_mem_orthogonal, he]
        exact (isExtremalSolution_iff_residual_mem_orthogonal T).mp hx
      by_cases hEq : x - k' = x
      · have he' : (x : E) - k = (x : E) := congrArg Subtype.val hEq
        rw [he', sub_zero]
      · simpa only [sub_zero, Submodule.coe_sub] using (hmin _ hx' hEq).le
    simpa only [sub_zero] using (isBestApprox_iff_mem_orthogonal T.ker T.ker.zero_mem).mp h
  · rintro ⟨hx, hk⟩
    refine ⟨hx, fun z hz hne => ?_⟩
    have hzero := (isExtremalSolution_iff_residual_mem_orthogonal T).mp hx
    have hzero' := (isExtremalSolution_iff_residual_mem_orthogonal T).mp hz
    have he : T z - T x = (y - T x) - (y - T z) := by abel
    have hzrx : T z - T x ∈ T.toFun.rangeᗮ := by
      rw [he]
      exact T.toFun.rangeᗮ.sub_mem hzero hzero'
    have hzrx' : T z - T x ∈ T.toFun.range := T.toFun.range.sub_mem ⟨z, rfl⟩ ⟨x, rfl⟩
    have hh : T z - T x = 0 :=
      (Submodule.disjoint_def.mp T.toFun.range.orthogonal_disjoint) _ hzrx' hzrx
    have hd : (z : E) - (x : E) ∈ T.ker := T.sub_mem_ker_iff.mpr (sub_eq_zero.mp hh)
    have hi := T.ker.inner_left_of_mem_orthogonal hd hk
    have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (x : E) ((z : E) - (x : E)) hi
    have hp' : ‖(z : E)‖ ^ 2 = ‖(x : E)‖ ^ 2 + ‖(z : E) - (x : E)‖ ^ 2 := by
      simpa only [add_sub_cancel, pow_two] using hp
    have hn : (z : E) - (x : E) ≠ 0 := fun h => hne (Subtype.ext (sub_eq_zero.mp h))
    nlinarith [norm_nonneg (z : E), norm_nonneg (x : E), sq_pos_of_pos (norm_pos_iff.mpr hn)]

/-- **Theorem 6**, Equations (76)–(78) of [benIsrael2003generalized].
Given an extremal solution, subtracting its kernel-closure projection
gives the least extremal solution precisely when that projection lies
in the kernel. -/
theorem theorem_6 [CompleteSpace E] [CompleteSpace F] {T : E →ₗ.[𝕜] F}
    {y : F} {x : T.domain} (hx : IsExtremalSolution T y x) :
    ((∃ z : T.domain, IsLeastExtremalSolution T y z) ↔
      T.ker.topologicalClosure.starProjection x ∈ T.ker) ∧
    ∀ z : T.domain, IsLeastExtremalSolution T y z →
      (z : E) = T.kerᗮ.starProjection x := by
  have hproj (z : T.domain) (hz : IsLeastExtremalSolution T y z) :
      (z : E) = T.kerᗮ.starProjection x := by
    obtain ⟨hze, hzK⟩ := isLeastExtremalSolution_iff.mp hz
    rw [(lemma_4 hx hze).1]
    exact (T.kerᗮ.starProjection_eq_self_iff.mpr hzK).symm
  refine ⟨⟨?_, ?_⟩, hproj⟩
  · rintro ⟨z, hz⟩
    have hk := extremalSolutions_sub_mem_ker hx (isLeastExtremalSolution_iff.mp hz).1
    rw [hproj z hz, ← sub_starProjection_closure_eq] at hk
    rwa [sub_sub_cancel] at hk
  · intro hp
    let p : T.domain := ⟨_, T.ker_le_domain hp⟩
    let z := x - p
    have hp0 : T p = 0 := T.coe_mem_ker_iff.mp hp
    have he : T z = T x := by rw [T.map_sub, hp0, sub_zero]
    refine ⟨z, isLeastExtremalSolution_iff.mpr ⟨?_, ?_⟩⟩
    · rw [isExtremalSolution_iff_apply_eq_projection, he]
      exact (isExtremalSolution_iff_apply_eq_projection T).mp hx
    · change (x : E) - T.ker.topologicalClosure.starProjection x ∈ T.kerᗮ
      rw [sub_starProjection_closure_eq]
      exact T.kerᗮ.starProjection_apply_mem x


/-- **Definition 5**, Equation (79) of [benIsrael2003generalized].
The kernel-closure part of the domain is its intersection with the
topological closure of the kernel. -/
def extremalKernelPart (T : E →ₗ.[𝕜] F) : Submodule 𝕜 E :=
  T.domain ⊓ T.ker.topologicalClosure

/-- **Equation (80)** of [benIsrael2003generalized].
The kernel-closure part and the carrier are orthogonal. Their sum
has an algebraic complement within the original domain. -/
theorem exists_extremalDomainComplement [CompleteSpace E] (T : E →ₗ.[𝕜] F) :
    (extremalKernelPart T).IsOrtho (carrier T) ∧
      ∃ A : Submodule 𝕜 E, A ≤ T.domain ∧ Disjoint A (extremalKernelPart T ⊔ carrier T) ∧
        T.domain = A ⊔ (extremalKernelPart T ⊔ carrier T) := by
  constructor
  · apply Submodule.isOrtho_iff_le.mpr
    apply le_trans (show extremalKernelPart T ≤ T.ker.topologicalClosure from inf_le_right)
    rw [← T.ker.orthogonal_orthogonal_eq_closure]
    exact Submodule.orthogonal_le (show carrier T ≤ T.kerᗮ from inf_le_right)
  · let V := extremalKernelPart T ⊔ carrier T
    have hV : V ≤ T.domain := sup_le inf_le_left inf_le_left
    let V₀ := V.comap T.domain.subtype
    obtain ⟨A₀, hA₀⟩ := V₀.exists_isCompl
    let A := A₀.map T.domain.subtype
    have hm : V₀.map T.domain.subtype = V := by
      apply Submodule.map_comap_eq_self
      simpa only [Submodule.range_subtype] using hV
    refine ⟨A, ?_, ?_, ?_⟩
    · rintro _ ⟨x, _, rfl⟩
      exact x.2
    · change Disjoint A V
      rw [← hm, disjoint_iff, ← Submodule.map_inf _ T.domain.injective_subtype,
        hA₀.symm.inf_eq_bot, Submodule.map_bot]
    · have h := congrArg (Submodule.map T.domain.subtype) hA₀.symm.sup_eq_top
      simpa only [Submodule.map_sup, hm, Submodule.map_top, Submodule.range_subtype] using h.symm

/-- **Definition 5** of [benIsrael2003generalized].
The extremal inverse applies the inverse on the carrier and is zero
perpendicular to the range of the original operator. The construction
is a partial linear map even for a domain which does not split along
the kernel. -/
noncomputable def extremalInverse (T : E →ₗ.[𝕜] F) : F →ₗ.[𝕜] E :=
  tsengInverseOn T T.toFun.rangeᗮ le_rfl

/-- **Definition 5** of [benIsrael2003generalized], inverse graph.
An input-output pair is a carrier point whose image differs from the
input by a vector orthogonal to the original range. -/
theorem mem_graph_extremalInverse_iff (T : E →ₗ.[𝕜] F) {x : E} {y : F} :
    (y, x) ∈ (extremalInverse T).graph ↔
      ∃ a : T.domain, (a : E) ∈ T.kerᗮ ∧ (a : E) = x ∧ y - T a ∈ T.toFun.rangeᗮ :=
  mem_graph_tsengInverseOn_iff T _ le_rfl

private theorem mem_range_restrictCarrier_iff (T : E →ₗ.[𝕜] F) {y : F} :
    y ∈ (restrictCarrier T).toFun.range ↔ ∃ a : T.domain, (a : E) ∈ T.kerᗮ ∧ T a = y := by
  constructor
  · rintro ⟨a, rfl⟩
    have ha : (a : E) ∈ carrier T := restrictCarrier_domain T ▸ a.2
    exact ⟨⟨a, ha.1⟩, ha.2, ((restrictCarrier_le T).2 (x := a) (y := ⟨a, ha.1⟩) rfl).symm⟩
  · rintro ⟨a, ha, rfl⟩
    have hD : (a : E) ∈ (restrictCarrier T).domain := by
      rw [restrictCarrier_domain]
      exact ⟨a.2, ha⟩
    exact ⟨⟨a, hD⟩, (restrictCarrier_le T).2 (x := ⟨a, hD⟩) (y := a) rfl⟩

/-- **Theorem 7(a)** of [benIsrael2003generalized].
The extremal inverse domain is the orthogonal sum of the carrier
image and the perpendicular complement of the original range. -/
theorem extremalInverse_domain (T : E →ₗ.[𝕜] F) :
    (extremalInverse T).domain = (restrictCarrier T).toFun.range ⊔ T.toFun.rangeᗮ := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := LinearPMap.mem_domain_iff.mp hy
    obtain ⟨a, ha, _, he⟩ := (mem_graph_extremalInverse_iff T).mp hx
    exact Submodule.mem_sup.mpr ⟨T a, (mem_range_restrictCarrier_iff T).mpr ⟨a, ha, rfl⟩,
      y - T a, he, add_sub_cancel _ _⟩
  · intro hy
    obtain ⟨b, hb, z, hz, hsum⟩ := Submodule.mem_sup.mp hy
    obtain ⟨a, ha, rfl⟩ := (mem_range_restrictCarrier_iff T).mp hb
    refine LinearPMap.mem_domain_iff.mpr ⟨a, (mem_graph_extremalInverse_iff T).mpr ⟨a, ha, rfl, ?_⟩⟩
    rwa [← hsum, add_sub_cancel_left]

/-- **Theorem 7(b)** of [benIsrael2003generalized]. -/
theorem extremalInverse_range (T : E →ₗ.[𝕜] F) :
    (extremalInverse T).toFun.range = carrier T :=
  tsengInverseOn_range T _ le_rfl

/-- **Theorem 7(c)** of [benIsrael2003generalized]. -/
theorem extremalInverse_ker (T : E →ₗ.[𝕜] F) :
    (extremalInverse T).ker = T.toFun.rangeᗮ :=
  tsengInverseOn_ker T _ le_rfl

/-- The inverse range is contained in the original domain. -/
theorem extremalInverse_range_le_domain (T : E →ₗ.[𝕜] F) :
    (extremalInverse T).toFun.range ≤ T.domain := by
  rw [extremalInverse_range]
  exact inf_le_left

/-- **Theorem 7(d)** of [benIsrael2003generalized].
Applying the operator after the extremal inverse fits the orthogonal
projection onto the closed range. -/
theorem extremalInverse_apply_projection [CompleteSpace F] (T : E →ₗ.[𝕜] F)
    (y : (extremalInverse T).domain) :
    T ⟨extremalInverse T y, extremalInverse_range_le_domain T ⟨y, rfl⟩⟩ =
      T.toFun.range.topologicalClosure.starProjection y := by
  obtain ⟨a, _, ha, hres⟩ :=
    (mem_graph_extremalInverse_iff T).mp ((extremalInverse T).mem_graph y)
  have he : (⟨extremalInverse T y, extremalInverse_range_le_domain T ⟨y, rfl⟩⟩ : T.domain) = a :=
    Subtype.ext ha.symm
  rw [he]
  exact (starProjection_closure_eq_of_residual T.toFun.range ⟨a, rfl⟩ hres).symm

/-- **Theorem 7(e)** of [benIsrael2003generalized].
On the sum of the original kernel and carrier, applying the extremal
inverse after the operator projects onto the closure of the carrier. -/
theorem extremalInverse_projection_apply [CompleteSpace E] (T : E →ₗ.[𝕜] F)
    (x : T.domain) (hx : (x : E) ∈ T.ker ⊔ carrier T) :
    ∃ hy : T x ∈ (extremalInverse T).domain,
      extremalInverse T ⟨T x, hy⟩ = (carrier T).topologicalClosure.starProjection x := by
  obtain ⟨k, hk, a, ha, hsum⟩ := Submodule.mem_sup.mp hx
  let u : T.domain := ⟨k, T.ker_le_domain hk⟩
  let v : T.domain := ⟨a, ha.1⟩
  have hTu : T u = 0 := T.coe_mem_ker_iff.mp hk
  have he : T x = T v := by
    rw [show x = u + v from Subtype.ext hsum.symm, T.map_add, hTu, zero_add]
  have hg : (T x, a) ∈ (extremalInverse T).graph := (mem_graph_extremalInverse_iff T).mpr
    ⟨v, ha.2, rfl, by rw [he, sub_self]; exact Submodule.zero_mem _⟩
  have hy := LinearPMap.mem_domain_of_mem_graph hg
  refine ⟨hy, ((LinearPMap.image_iff hy).mpr hg).symm.trans ?_⟩
  symm
  apply starProjection_closure_eq_of_residual (carrier T) ha
  have hko : k ∈ (carrier T)ᗮ :=
    (Submodule.orthogonal_le (show carrier T ≤ T.kerᗮ from inf_le_right))
      (T.ker.le_orthogonal_orthogonal hk)
  rwa [← hsum, add_sub_cancel_right]

/-- **Theorem 7(a)–(e)** of [benIsrael2003generalized].
The partial domain, range, kernel, and both projection formulas for
the extremal inverse. -/
theorem theorem_7 [CompleteSpace E] [CompleteSpace F] (T : E →ₗ.[𝕜] F) :
    let S := extremalInverse T
    S.domain = (restrictCarrier T).toFun.range ⊔ T.toFun.rangeᗮ ∧
    S.toFun.range = carrier T ∧ S.ker = T.toFun.rangeᗮ ∧
    (∀ y : S.domain, T ⟨S y, extremalInverse_range_le_domain T ⟨y, rfl⟩⟩ =
      T.toFun.range.topologicalClosure.starProjection y) ∧
    ∀ x : T.domain, (x : E) ∈ T.ker ⊔ carrier T →
      ∃ hy : T x ∈ S.domain, S ⟨T x, hy⟩ = (carrier T).topologicalClosure.starProjection x :=
  ⟨extremalInverse_domain T, extremalInverse_range T, extremalInverse_ker T,
    extremalInverse_apply_projection T, extremalInverse_projection_apply T⟩

/-- **Theorem 8**, Equations (81)–(82) of [benIsrael2003generalized].
A point is the least extremal solution exactly when it is the value
of the extremal inverse on the datum, including the required domain
membership. -/
theorem isLeastExtremalSolution_iff_extremalInverse_graph (T : E →ₗ.[𝕜] F)
    {y : F} {x : T.domain} :
    IsLeastExtremalSolution T y x ↔ (y, (x : E)) ∈ (extremalInverse T).graph := by
  rw [isLeastExtremalSolution_iff, isExtremalSolution_iff_residual_mem_orthogonal,
    mem_graph_extremalInverse_iff]
  constructor
  · rintro ⟨h, ho⟩
    exact ⟨x, ho, rfl, h⟩
  · rintro ⟨a, ha, he, hres⟩
    have hax : a = x := Subtype.ext he
    exact ⟨hax ▸ hres, he ▸ ha⟩

/-- **Theorem 8** of [benIsrael2003generalized].
Existence of a least extremal solution is equivalent to membership in
the extremal inverse domain. The inverse provides that solution. -/
theorem theorem_8 (T : E →ₗ.[𝕜] F) (y : F) :
    ((∃ x : T.domain, IsLeastExtremalSolution T y x) ↔ y ∈ (extremalInverse T).domain) ∧
    ∀ hy : y ∈ (extremalInverse T).domain, ∀ x : T.domain,
      IsLeastExtremalSolution T y x ↔ (x : E) = extremalInverse T ⟨y, hy⟩ := by
  constructor
  · constructor
    · rintro ⟨a, ha⟩
      exact LinearPMap.mem_domain_of_mem_graph
        ((isLeastExtremalSolution_iff_extremalInverse_graph T).mp ha)
    · intro hy
      let S := extremalInverse T
      let b : S.domain := ⟨y, hy⟩
      let x : T.domain := ⟨S b, extremalInverse_range_le_domain T ⟨b, rfl⟩⟩
      exact ⟨x, (isLeastExtremalSolution_iff_extremalInverse_graph T).mpr (S.mem_graph b)⟩
  · intro hy x
    rw [isLeastExtremalSolution_iff_extremalInverse_graph]
    exact (LinearPMap.image_iff hy).symm

/-- With a closed kernel the extremal inverse is the maximal Tseng
inverse, as in the closed-kernel case of **Theorem 8**. The predicate
`IsTsengInverse` includes decomposability with respect to the kernel. -/
theorem extremalInverse_eq_maximalTsengInverse_of_isClosed_ker [CompleteSpace E]
    (T : E →ₗ.[𝕜] F) (hK : IsClosed (T.ker : Set E)) :
    IsTsengInverse T (extremalInverse T) ∧ extremalInverse T = maximalTsengInverse T := by
  refine ⟨isTsengInverse_maximalTsengInverse T ?_, rfl⟩
  exact (isDecomposable_of_isClosed T.ker_le_domain hK).2


section Examples

/-- **Exercise 37** of [benIsrael2003generalized].
A datum in the closure of the range but outside the range admits no
extremal solution. This applies to the diagonal operator of Exercise 7. -/
theorem exercise_9_37 [CompleteSpace F] (T : E →ₗ.[𝕜] F) {y : F}
    (hy : y ∈ T.toFun.range.topologicalClosure) (hn : y ∉ T.toFun.range) :
    ¬ ∃ x : T.domain, IsExtremalSolution T y x := by
  rw [(theorem_5 T y).1, Submodule.starProjection_eq_self_iff.mpr hy]
  exact hn

/-- A bounded operator with nonclosed range admits a datum without an
extremal solution. -/
theorem exists_no_extremalSolution_of_nonclosed_range [CompleteSpace F]
    (T : E →ₗ.[𝕜] F) (hT : ¬ IsClosed (T.toFun.range : Set F)) :
    ∃ y : F, ¬ ∃ x : T.domain, IsExtremalSolution T y x := by
  have hlt : T.toFun.range < T.toFun.range.topologicalClosure :=
    lt_of_le_of_ne T.toFun.range.le_topologicalClosure fun he =>
      hT (he.symm ▸ T.toFun.range.isClosed_topologicalClosure)
  obtain ⟨y, hy, hn⟩ := IsConcreteLE.exists_of_lt hlt
  exact ⟨y, exercise_9_37 T hy hn⟩

/-- An extremal inverse extends to the corresponding Erdélyi inverse,
which permits the whole perpendicular complement of the carrier image
in its domain. -/
theorem extremalInverse_le_erdelyiInverse (T : E →ₗ.[𝕜] F) :
    extremalInverse T ≤ erdelyiInverse T := by
  apply LinearPMap.le_of_le_graph
  rintro ⟨y, x⟩ h
  obtain ⟨a, ha, he, hres⟩ := (mem_graph_extremalInverse_iff T).mp h
  refine (mem_graph_erdelyiInverse_iff T).mpr ⟨a, ha, he, Submodule.orthogonal_le ?_ hres⟩
  rintro _ ⟨b, rfl⟩
  exact ⟨⟨b, b.2.2⟩, rfl⟩

/-- **Theorem 7(a)** of [benIsrael2003generalized], noncontainment example.
The noncontainment example for the Erdélyi inverse also works for the
extremal inverse. -/
theorem theorem_7_range_not_le_domain_example [CompleteSpace E]
    (A : E →L[𝕜] E) (hA : Function.Injective A)
    (hD : Dense (A.range : Set E)) (hR : ¬ IsClosed (A.range : Set E)) :
    ∃ T : WithLp 2 (E × E) →ₗ.[𝕜] E, ¬ T.toFun.range ≤ (extremalInverse T).domain := by
  obtain ⟨T, h⟩ := theorem_4b_range_not_le_domain_example A hA hD hR
  exact ⟨T, fun he => h (he.trans (extremalInverse_le_erdelyiInverse T).1)⟩

/-- **Exercise 39** of [benIsrael2003generalized], abstract form.
A nonzero datum for an everywhere-defined discontinuous linear
functional has exact solutions but no least extremal solution. -/
theorem exercise_9_39_unbounded_functional [CompleteSpace E] (f : E →ₗ[𝕜] 𝕜)
    (hf : ¬ Continuous f) {y : 𝕜} (hy : y ≠ 0) :
    let T := f.toPMap ⊤
    (∃ x : T.domain, T x = y) ∧ ¬ ∃ x : T.domain, IsLeastExtremalSolution T y x := by
  let T := f.toPMap ⊤
  have hn : ∃ x, f x ≠ 0 := by
    by_contra! h
    apply hf
    rw [show f = 0 from LinearMap.ext h]
    exact continuous_zero
  obtain ⟨x, hx⟩ := hn
  let u : T.domain := ⟨(y / f x) • x, trivial⟩
  have hu : T u = y := by
    change f ((y / f x) • x) = y
    rw [_root_.map_smul, smul_eq_mul, div_mul_cancel₀ _ hx]
  refine ⟨⟨u, hu⟩, ?_⟩
  rintro ⟨z, hz⟩
  obtain ⟨he, ho⟩ := isLeastExtremalSolution_iff.mp hz
  have ho' := (exercise_9_2 f hf).2.1
  have hz0 : (z : E) = 0 := by
    rw [ho'] at ho
    simpa only [Submodule.mem_bot] using ho
  have heq := he u
  rw [show z = 0 from Subtype.ext hz0, T.map_zero, hu, sub_self, norm_zero, sub_zero] at heq
  exact hy (norm_eq_zero.mp (le_antisymm heq (norm_nonneg _)))

end Examples

section Iterated

private theorem range_restrictCarrier_le (T : E →ₗ.[𝕜] F) :
    (restrictCarrier T).toFun.range ≤ T.toFun.range := by
  rintro _ ⟨x, rfl⟩
  have h := restrictCarrier_le T
  exact ⟨⟨x, h.1 x.2⟩, (h.2 (x := x) (y := ⟨x, h.1 x.2⟩) rfl).symm⟩

/-- The extremal inverse has a domain decomposable along its kernel.
Its carrier is the image of the original carrier. -/
theorem extremalInverse_decomposable (T : E →ₗ.[𝕜] F) :
    IsDecomposable (extremalInverse T).domain (extremalInverse T).ker ∧
      carrier (extremalInverse T) = (restrictCarrier T).toFun.range := by
  let U := (restrictCarrier T).toFun.range
  have hr : U ≤ T.toFun.rangeᗮᗮ :=
    (range_restrictCarrier_le T).trans T.toFun.range.le_orthogonal_orthogonal
  have he : carrier (extremalInverse T) = U := by
    unfold carrier
    rw [extremalInverse_domain, extremalInverse_ker]
    refine le_antisymm (fun y hy => ?_) (le_inf le_sup_left hr)
    obtain ⟨u, hu, z, hz, he⟩ := Submodule.mem_sup.mp hy.1
    have hzo : z ∈ T.toFun.rangeᗮᗮ := by
      have hz' : z = y - u := eq_sub_of_add_eq' he
      rw [hz']
      exact T.toFun.rangeᗮᗮ.sub_mem hy.2 (hr hu)
    have hz0 : z = 0 := (Submodule.disjoint_def.mp T.toFun.rangeᗮ.orthogonal_disjoint) z hz hzo
    simpa only [← he, hz0, add_zero] using hu
  refine ⟨⟨(extremalInverse T).ker_le_domain, ?_⟩, he⟩
  change (extremalInverse T).domain = (extremalInverse T).ker ⊔ carrier (extremalInverse T)
  rw [he, extremalInverse_domain, extremalInverse_ker, sup_comm]

/-- The maximal Tseng inverse of the extremal inverse, as in Exercise 40. -/
noncomputable def iteratedExtremalInverse (T : E →ₗ.[𝕜] F) : E →ₗ.[𝕜] F :=
  maximalTsengInverse (extremalInverse T)

/-- **Exercise 40(a)** of [benIsrael2003generalized].
The graph of the iterated inverse extends the carrier graph by zero
in the input direction perpendicular to the carrier. -/
theorem mem_graph_iteratedExtremalInverse_iff (T : E →ₗ.[𝕜] F) {x : E} {y : F} :
    (x, y) ∈ (iteratedExtremalInverse T).graph ↔
      ∃ a : T.domain, (a : E) ∈ T.kerᗮ ∧ T a = y ∧ x - (a : E) ∈ (carrier T)ᗮ := by
  let S := extremalInverse T
  rw [iteratedExtremalInverse, maximalTsengInverse, mem_graph_tsengInverseOn_iff,
    extremalInverse_range,
    extremalInverse_ker]
  constructor
  · rintro ⟨b, hbo, hby, hres⟩
    obtain ⟨a, hao, hab, hba⟩ := (mem_graph_extremalInverse_iff T).mp (S.mem_graph b)
    have hTbo : T a ∈ T.toFun.rangeᗮᗮ := T.toFun.range.le_orthogonal_orthogonal ⟨a, rfl⟩
    have hb0 := (Submodule.disjoint_def.mp T.toFun.rangeᗮ.orthogonal_disjoint) _ hba
      (T.toFun.rangeᗮᗮ.sub_mem hbo hTbo)
    exact ⟨a, hao, (sub_eq_zero.mp hb0).symm.trans hby, hab.symm ▸ hres⟩
  · rintro ⟨a, hao, hay, hres⟩
    have hg : (T a, (a : E)) ∈ S.graph :=
      (mem_graph_extremalInverse_iff T).mpr
        ⟨a, hao, rfl, by simpa only [sub_self] using Submodule.zero_mem _⟩
    have hb := LinearPMap.mem_domain_of_mem_graph hg
    have he := (LinearPMap.image_iff hb).mpr hg
    exact ⟨⟨T a, hb⟩, T.toFun.range.le_orthogonal_orthogonal ⟨a, rfl⟩, hay, he ▸ hres⟩

/-- **Exercise 40(b)–(d)** of [benIsrael2003generalized].
The iterated inverse is defined on the carrier plus its perpendicular
complement, with range the original carrier image and kernel the
carrier's perpendicular complement. -/
theorem exercise_9_40 (T : E →ₗ.[𝕜] F) :
    (iteratedExtremalInverse T).domain = carrier T ⊔ (carrier T)ᗮ ∧
    (iteratedExtremalInverse T).toFun.range = (restrictCarrier T).toFun.range ∧
    (iteratedExtremalInverse T).ker = (carrier T)ᗮ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [iteratedExtremalInverse, maximalTsengInverse_domain _ (extremalInverse_decomposable T).1.2,
      extremalInverse_range]
  · rw [iteratedExtremalInverse, maximalTsengInverse_range, (extremalInverse_decomposable T).2]
  · rw [iteratedExtremalInverse, maximalTsengInverse_ker, extremalInverse_range]

/-- The orthogonal sum of the original kernel and carrier in Exercise 41. -/
def extremalCoreDomain (T : E →ₗ.[𝕜] F) : Submodule 𝕜 E :=
  T.ker ⊔ carrier T

/-- **Exercise 41(a)** of [benIsrael2003generalized].
The iterated inverse domain splits further into the carrier, the
closure of the kernel, and the perpendicular complement of the core. -/
theorem exercise_9_41a [CompleteSpace E] (T : E →ₗ.[𝕜] F) :
    (iteratedExtremalInverse T).domain =
      carrier T ⊔ (T.ker.topologicalClosure ⊔ (extremalCoreDomain T)ᗮ) := by
  have hle : T.ker.topologicalClosure ≤ (carrier T)ᗮ := by
    rw [← T.ker.orthogonal_orthogonal_eq_closure]
    exact Submodule.orthogonal_le (show carrier T ≤ T.kerᗮ from inf_le_right)
  have hs := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hle
  rw [Submodule.orthogonal_closure, Submodule.inf_orthogonal] at hs
  rw [(exercise_9_40 T).1, ← hs]
  rfl

/-- **Exercise 41(b)** of [benIsrael2003generalized].
The original operator and the iterated inverse agree on the
orthogonal sum of the kernel and carrier. -/
theorem exercise_9_41b (T : E →ₗ.[𝕜] F) :
    let U := T.domRestrict (extremalCoreDomain T)
    U ≤ iteratedExtremalInverse T ∧ U.domain = extremalCoreDomain T := by
  intro U
  have hd : U.domain = extremalCoreDomain T :=
    inf_eq_left.mpr (sup_le T.ker_le_domain inf_le_left)
  refine ⟨LinearPMap.le_of_le_graph ?_, hd⟩
  rintro ⟨x, y⟩ h
  obtain ⟨a, ha, hay⟩ := U.mem_graph_iff.mp h
  have hau : (a : E) ∈ extremalCoreDomain T := a.2.1
  obtain ⟨k, hk, c, hc, he⟩ := Submodule.mem_sup.mp hau
  let k' : T.domain := ⟨k, T.ker_le_domain hk⟩
  let c' : T.domain := ⟨c, hc.1⟩
  have he' : (⟨a, a.2.2⟩ : T.domain) = k' + c' := Subtype.ext he.symm
  have hk0 : T k' = 0 := T.coe_mem_ker_iff.mp hk
  have hT : T ⟨a, a.2.2⟩ = y := hay
  rw [he', T.map_add, hk0, zero_add] at hT
  refine (mem_graph_iteratedExtremalInverse_iff T).mpr ⟨c', hc.2, hT, ?_⟩
  have hko := (Submodule.orthogonal_le (show carrier T ≤ T.kerᗮ from inf_le_right))
    (T.ker.le_orthogonal_orthogonal hk)
  change x - c ∈ (carrier T)ᗮ
  change (a : E) = x at ha
  have hxc : x - c = k := by rw [← ha, ← he, add_sub_cancel_right]
  rwa [hxc]

/-- **Exercise 41(c)** of [benIsrael2003generalized].
The iterated inverse extends the original operator exactly when the
original domain decomposes orthogonally along its kernel. In that
case the added perpendicular directions are in its kernel. -/
theorem exercise_9_41c [CompleteSpace E] (T : E →ₗ.[𝕜] F) :
    (T ≤ iteratedExtremalInverse T ↔ IsDecomposable T.domain T.ker) ∧
    (IsDecomposable T.domain T.ker →
      (iteratedExtremalInverse T).ker = T.ker.topologicalClosure ⊔ T.domainᗮ) := by
  constructor
  · constructor
    · intro h
      refine ⟨T.ker_le_domain, le_antisymm (fun x hx => ?_) (sup_le T.ker_le_domain inf_le_left)⟩
      let a : T.domain := ⟨x, hx⟩
      have ha := LinearPMap.le_graph_of_le h (T.mem_graph a)
      obtain ⟨b, hbo, hba, _⟩ := (mem_graph_iteratedExtremalInverse_iff T).mp ha
      have hK : x - (b : E) ∈ T.ker := T.sub_mem_ker_iff.mpr hba.symm
      exact Submodule.mem_sup.mpr ⟨x - (b : E), hK, b, ⟨b.2, hbo⟩, sub_add_cancel _ _⟩
    · intro h
      have hu := exercise_9_41b T
      have hEq : T.domRestrict (extremalCoreDomain T) = T :=
        LinearPMap.eq_of_le_of_domain_eq LinearPMap.domRestrict_le (hu.2.trans h.2.symm)
      exact hEq.symm.le.trans hu.1
  · intro h
    have hle : T.ker.topologicalClosure ≤ (carrier T)ᗮ := by
      rw [← T.ker.orthogonal_orthogonal_eq_closure]
      exact Submodule.orthogonal_le (show carrier T ≤ T.kerᗮ from inf_le_right)
    have hs := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hle
    have hdom : T.domain = T.ker ⊔ carrier T := h.2
    rw [Submodule.orthogonal_closure, Submodule.inf_orthogonal, ← hdom] at hs
    exact (exercise_9_40 T).2.2.trans hs.symm

end Iterated


section Restricted

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]

/-- The restriction of a bounded operator to the kernel of the constraint. -/
def kernelRestrictedOperator (T : E →L[𝕜] F) (S : E →L[𝕜] G) : S.ker →L[𝕜] F :=
  T.comp S.ker.subtypeL

/-- **Exercise 45** of [benIsrael2003generalized].
The kernel-restricted pseudoinverse takes its values in the ambient
space by composing the restricted inverse with the kernel inclusion. -/
noncomputable def kernelRestrictedPseudoinverse (T : E →L[𝕜] F) (S : E →L[𝕜] G)
    (hR : IsClosed ((kernelRestrictedOperator T S).range : Set F)) : F →L[𝕜] E :=
  let _ : CompleteSpace S.ker := S.isClosed_ker.completeSpace_coe
  S.ker.subtypeL.comp (boundedMoorePenroseInverse (kernelRestrictedOperator T S) hR)

/-- **Exercise 45** of [benIsrael2003generalized].
The five equations for the kernel-restricted pseudoinverse, with the
last two evaluated on the kernel of the constraint. -/
def IsKernelRestrictedPseudoinverse (T : E →L[𝕜] F) (S : E →L[𝕜] G) (X : F →L[𝕜] E) : Prop :=
  let _ : CompleteSpace S.ker := S.isClosed_ker.completeSpace_coe
  S.comp X = 0 ∧ (X.comp T).comp X = X ∧ (T.comp X).adjoint = T.comp X ∧
  (∀ x : S.ker, T (X (T x)) = T x) ∧
  ∀ x : S.ker, S.ker.starProjection ((X.comp T).adjoint x) = X (T x)

omit [CompleteSpace G] in
private theorem kernelRestrictedPseudoinverse_lift_iff (T : E →L[𝕜] F)
    (S : E →L[𝕜] G) (Y : F →L[𝕜] S.ker) :
    let _ : CompleteSpace S.ker := S.isClosed_ker.completeSpace_coe
    let A := kernelRestrictedOperator T S
    IsKernelRestrictedPseudoinverse T S (S.ker.subtypeL.comp Y) ↔
      (A.comp Y).comp A = A ∧ (Y.comp A).comp Y = Y ∧
      (A.comp Y).adjoint = A.comp Y ∧ (Y.comp A).adjoint = Y.comp A := by
  let : CompleteSpace S.ker := S.isClosed_ker.completeSpace_coe
  let I := S.ker.subtypeL
  let A := kernelRestrictedOperator T S
  let X := I.comp Y
  have hS : S.comp X = 0 := by
    ext y
    exact (Y y).2
  have hTX : T.comp X = A.comp Y := rfl
  have hAdj (x : S.ker) :
      (↑((Y.comp A).adjoint x) : E) = S.ker.starProjection ((X.comp T).adjoint x) := by
    change (↑((Y.comp (T.comp I)).adjoint x) : E) =
      S.ker.starProjection (((I.comp Y).comp T).adjoint (I x))
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      Submodule.adjoint_subtypeL]
    change (↑(S.ker.orthogonalProjectionOnto (T.adjoint (Y.adjoint x))) : E) =
      S.ker.starProjection (T.adjoint (Y.adjoint (S.ker.orthogonalProjectionOnto (I x))))
    have hI : S.ker.orthogonalProjectionOnto (I x) = x :=
      S.ker.orthogonalProjectionOnto_mem_subspace_eq_self x
    rw [hI]
    rfl
  change (S.comp X = 0 ∧ (X.comp T).comp X = X ∧ (T.comp X).adjoint = T.comp X ∧
    (∀ x : S.ker, T (X (T x)) = T x) ∧
    ∀ x : S.ker, S.ker.starProjection ((X.comp T).adjoint x) = X (T x)) ↔
    (A.comp Y).comp A = A ∧ (Y.comp A).comp Y = Y ∧
    (A.comp Y).adjoint = A.comp Y ∧ (Y.comp A).adjoint = Y.comp A
  constructor
  · rintro ⟨_, hOut, hRight, hIn, hLeft⟩
    refine ⟨ContinuousLinearMap.ext hIn, ?_, by simpa only [hTX] using hRight, ?_⟩
    · ext y
      exact DFunLike.congr_fun hOut y
    · ext x
      exact (hAdj x).trans (hLeft x)
  · rintro ⟨hIn, hOut, hRight, hLeft⟩
    refine ⟨hS, ?_, by simpa only [hTX] using hRight, DFunLike.congr_fun hIn, fun x => ?_⟩
    · ext y
      exact congrArg Subtype.val (DFunLike.congr_fun hOut y)
    · rw [← hAdj]
      exact congrArg Subtype.val (DFunLike.congr_fun hLeft x)

omit [CompleteSpace G] in
/-- **Exercise 45** of [benIsrael2003generalized].
For closed range on the constraint kernel, the five equations have the
kernel-restricted pseudoinverse as their unique solution. -/
theorem exercise_9_45 (T : E →L[𝕜] F) (S : E →L[𝕜] G)
    (hR : IsClosed ((kernelRestrictedOperator T S).range : Set F)) (X : F →L[𝕜] E) :
    IsKernelRestrictedPseudoinverse T S X ↔ X = kernelRestrictedPseudoinverse T S hR := by
  let : CompleteSpace S.ker := S.isClosed_ker.completeSpace_coe
  let A := kernelRestrictedOperator T S
  constructor
  · intro h
    have hSX : S.comp X = 0 := h.1
    let Y := X.codRestrict S.ker (fun y => DFunLike.congr_fun hSX y)
    have hXY : X = S.ker.subtypeL.comp Y := rfl
    rw [hXY] at h ⊢
    have he := (theorem_3a A hR Y).mp ((kernelRestrictedPseudoinverse_lift_iff T S Y).mp h)
    rw [he]
    rfl
  · rintro rfl
    exact (kernelRestrictedPseudoinverse_lift_iff T S _).mpr
      (boundedMoorePenroseInverse_penrose A hR)

omit [CompleteSpace G] in
private theorem boundedMoorePenroseInverse_leastExtremal (A : E →L[𝕜] F)
    (hR : IsClosed (A.range : Set F)) (y : F) :
    let T := A.toLinearMap.toPMap ⊤
    IsLeastExtremalSolution T y ⟨boundedMoorePenroseInverse A hR y, trivial⟩ := by
  let B := boundedMoorePenroseInverse A hR
  apply (isLeastExtremalSolution_iff_extremalInverse_graph _).mpr
  have he := boundedMoorePenroseInverse_asPartial A hR
  change B.toLinearMap.toPMap ⊤ = extremalInverse (A.toLinearMap.toPMap ⊤) at he
  exact he ▸ (B.toLinearMap.toPMap ⊤).mem_graph ⟨y, trivial⟩

/-- Being the least extremal solution on an affine constraint fiber. -/
def IsLeastConstrainedExtremalSolution (T : E →L[𝕜] F) (S : E →L[𝕜] G)
    (y : F) (z : G) (x : E) : Prop :=
  S x = z ∧
    (∀ w, S w = z → ‖y - T x‖ ≤ ‖y - T w‖) ∧
    ∀ w, S w = z → ‖y - T w‖ = ‖y - T x‖ → w ≠ x → ‖x‖ < ‖w‖

/-- **Exercise 46** of [benIsrael2003generalized].
The least extremal solution with a feasible kernel constraint is the
sum of its minimum-norm particular solution and the kernel-restricted
least extremal correction. -/
theorem exercise_9_46 (T : E →L[𝕜] F) (S : E →L[𝕜] G)
    (hR : IsClosed ((kernelRestrictedOperator T S).range : Set F))
    (hS : IsClosed (S.range : Set G)) (y : F) {z : G} (hz : z ∈ S.range) :
    let c := boundedMoorePenroseInverse S hS z
    let x := kernelRestrictedPseudoinverse T S hR (y - T c) + c
    IsLeastConstrainedExtremalSolution T S y z x ∧
      ∀ w, IsLeastConstrainedExtremalSolution T S y z w → w = x := by
  let : CompleteSpace S.ker := S.isClosed_ker.completeSpace_coe
  let A := kernelRestrictedOperator T S
  let c := boundedMoorePenroseInverse S hS z
  let p := boundedMoorePenroseInverse A hR (y - T c)
  have hc : S c = z := by
    change (S.comp (boundedMoorePenroseInverse S hS)) z = z
    rw [(boundedMoorePenroseInverse_projections S hS).1]
    exact Submodule.starProjection_eq_self_iff.mpr (S.range.le_topologicalClosure hz)
  have hco : c ∈ S.kerᗮ := (boundedMoorePenroseInverse_range_ker S hS).1 ▸ ⟨z, rfl⟩
  have hp := boundedMoorePenroseInverse_leastExtremal A hR (y - T c)
  have hpmin (u : S.ker) : ‖(y - T c) - A p‖ ≤ ‖(y - T c) - A u‖ :=
    hp.1 ⟨u, trivial⟩
  have hTie (u : S.ker) (hu : ‖(y - T c) - A u‖ = ‖(y - T c) - A p‖) (hne : u ≠ p) :
      ‖p‖ < ‖u‖ := by
    have he : IsExtremalSolution (A.toLinearMap.toPMap ⊤) (y - T c) ⟨u, trivial⟩ := by
      intro w
      change ‖(y - T c) - A u‖ ≤ ‖(y - T c) - A (w : S.ker)‖
      rw [hu]
      exact hpmin w
    exact hp.2 ⟨u, trivial⟩ he (fun h => hne (congrArg Subtype.val h))
  have hsq (u : S.ker) : ‖(u : E) + c‖ ^ 2 = ‖(u : E)‖ ^ 2 + ‖c‖ ^ 2 := by
    simpa only [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (u : E) c (S.ker.inner_right_of_mem_orthogonal u.2 hco)
  change IsLeastConstrainedExtremalSolution T S y z ((p : E) + c) ∧
    ∀ w, IsLeastConstrainedExtremalSolution T S y z w → w = (p : E) + c
  have hsol : IsLeastConstrainedExtremalSolution T S y z ((p : E) + c) := by
    refine ⟨?_, ?_, ?_⟩
    · have hSp : S (p : E) = 0 := p.2
      rw [_root_.map_add, hSp, hc, zero_add]
    · intro w hw
      have hmem : w - c ∈ S.ker := by
        change S (w - c) = 0
        rw [_root_.map_sub, hw, hc, sub_self]
      let u : S.ker := ⟨w - c, hmem⟩
      have he : w = (u : E) + c := by change w = w - c + c; rw [sub_add_cancel]
      rw [he, _root_.map_add, _root_.map_add]
      have h := hpmin u
      change ‖(y - T c) - T p‖ ≤ ‖(y - T c) - T u‖ at h
      simpa only [sub_add_eq_sub_sub, sub_right_comm y] using h
    · intro w hw hTie' hne
      have hmem : w - c ∈ S.ker := by
        change S (w - c) = 0
        rw [_root_.map_sub, hw, hc, sub_self]
      let u : S.ker := ⟨w - c, hmem⟩
      have he : w = (u : E) + c := by change w = w - c + c; rw [sub_add_cancel]
      have hune : u ≠ p := fun h => hne (he.trans (congrArg (fun a : S.ker => (a : E) + c) h))
      rw [he, _root_.map_add, _root_.map_add] at hTie'
      have hpNorm := hTie u (by
        change ‖(y - T c) - T u‖ = ‖(y - T c) - T p‖
        simpa only [sub_add_eq_sub_sub, sub_right_comm y] using hTie') hune
      change ‖(p : E)‖ < ‖(u : E)‖ at hpNorm
      rw [he]
      nlinarith [hsq p, hsq u, norm_nonneg ((p : E) + c), norm_nonneg ((u : E) + c),
        norm_nonneg (p : E)]
  refine ⟨hsol, fun w hw => ?_⟩
  by_contra hne
  have h₁ := hsol.2.1 w hw.1
  have h₂ := hw.2.1 ((p : E) + c) hsol.1
  have hEq := le_antisymm h₂ h₁
  exact (hsol.2.2 w hw.1 hEq hne).not_gt (hw.2.2 _ hsol.1 hEq.symm (Ne.symm hne))

end Restricted


section AdjointCriterion

variable [CompleteSpace E] [CompleteSpace F]

private theorem ker_adjointComp_eq (T : E →L[𝕜] F) :
    (T.comp T.adjoint).ker = T.adjoint.ker :=
  T.ker_self_comp_adjoint

private theorem exists_extremalSolution_iff_adjoint_bound (T : E →L[𝕜] F) (y : F) :
    (∃ x : (T.toLinearMap.toPMap ⊤).domain, IsExtremalSolution (T.toLinearMap.toPMap ⊤) y x) ↔
      ∃ β : ℝ, 0 < β ∧ ∀ z ∈ (T.adjoint.ker)ᗮ,
        ‖inner 𝕜 y z‖ ^ 2 ≤ β * ‖T.adjoint z‖ ^ 2 := by
  let A := T.toLinearMap.toPMap ⊤
  have hR : A.toFun.range = T.range := LinearMap.range_toPMap_top _
  constructor
  · rintro ⟨x, hx⟩
    have hres := (isExtremalSolution_iff_residual_mem_orthogonal A).mp hx
    change y - T (x : E) ∈ A.toFun.rangeᗮ at hres
    rw [hR, T.orthogonal_range] at hres
    refine ⟨‖(x : E)‖ ^ 2 + 1, by positivity, fun z hz => ?_⟩
    have hz0 := (T.adjoint.ker).inner_right_of_mem_orthogonal hres hz
    have hInner : inner 𝕜 y z = inner 𝕜 (x : E) (T.adjoint z) := by
      rw [inner_sub_left] at hz0
      rw [sub_eq_zero.mp hz0, T.adjoint_inner_right]
    rw [hInner]
    have hi := norm_inner_le_norm (𝕜 := 𝕜) (x : E) (T.adjoint z)
    calc
      _ ≤ (‖(x : E)‖ * ‖T.adjoint z‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hi
      _ ≤ _ := by rw [mul_pow]; exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  · rintro ⟨β, hβ, hb⟩
    let U := (T.adjoint.ker)ᗮ
    let B := T.adjoint.comp U.subtypeL
    have hInj : Function.Injective B.toLinearMap := by
      apply LinearMap.ker_eq_bot.mp
      rw [Submodule.eq_bot_iff]
      intro z hz
      apply Subtype.ext
      exact (Submodule.disjoint_def.mp T.adjoint.ker.orthogonal_disjoint) (z : F) hz z.2
    let e := LinearEquiv.ofInjective B.toLinearMap hInj
    let f : B.range →ₗ[𝕜] 𝕜 := ((innerSL 𝕜 y).toLinearMap.comp U.subtype).comp e.symm.toLinearMap
    let P : E →ₗ.[𝕜] 𝕜 := ⟨B.range, f⟩
    have hBound : IsBoundedOperator P := by
      refine ⟨Real.sqrt β, fun w => ?_⟩
      let u := e.symm w
      have hw : T.adjoint (u : F) = (w : E) := congrArg Subtype.val (e.apply_symm_apply w)
      have h := hb (u : F) u.2
      change ‖inner 𝕜 y (u : F)‖ ≤ Real.sqrt β * ‖(w : E)‖
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
      rw [mul_pow, Real.sq_sqrt hβ.le, ← hw]
      exact h
    obtain ⟨g, hg⟩ := exists_bounded_extension P hBound
    obtain ⟨x, hx⟩ := (InnerProductSpace.toDual 𝕜 E).surjective g
    refine ⟨⟨x, trivial⟩, (isExtremalSolution_iff_residual_mem_orthogonal A).mpr ?_⟩
    change y - T x ∈ A.toFun.rangeᗮ
    rw [hR, Submodule.mem_orthogonal']
    intro z hz
    have ho : z ∈ U := by
      change z ∈ (T.adjoint.ker)ᗮ
      rw [← T.orthogonal_range]
      exact T.range.le_orthogonal_orthogonal hz
    let u : U := ⟨z, ho⟩
    have h := hg (e u)
    change g (T.adjoint z) = inner 𝕜 y (e.symm (e u) : F) at h
    rw [LinearEquiv.symm_apply_apply] at h
    rw [← hx] at h
    change inner 𝕜 x (T.adjoint z) = inner 𝕜 y z at h
    rw [inner_sub_left, ← T.adjoint_inner_right, h, sub_self]

/-- **Exercise 44** of [benIsrael2003generalized].
For a bounded operator an extremal solution exists precisely when
the datum's pairing is bounded by the quadratic form of the right Gram
operator on the perpendicular complement of its kernel. -/
theorem exercise_9_44 (T : E →L[𝕜] F) (y : F) :
    (∃ x : (T.toLinearMap.toPMap ⊤).domain, IsExtremalSolution (T.toLinearMap.toPMap ⊤) y x) ↔
      ∃ β : ℝ, 0 < β ∧ ∀ z ∈ (T.comp T.adjoint).kerᗮ,
        ‖inner 𝕜 y z‖ ^ 2 ≤ β * RCLike.re (inner 𝕜 z (T (T.adjoint z))) := by
  rw [exists_extremalSolution_iff_adjoint_bound, ker_adjointComp_eq]
  simp only [T.adjoint.apply_norm_sq_eq_inner_adjoint_right,
    ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_apply]

end AdjointCriterion


section Weighted

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]

/-- The normal operator for the weighted least-norm functional in
Exercises 47–48. -/
noncomputable def weightedNormalOperator (S : E →L[𝕜] G) : E →L[𝕜] E :=
  ContinuousLinearMap.id 𝕜 E + S.adjoint.comp S

private theorem weightedNormalOperator_lower (S : E →L[𝕜] G) (x : E) :
    ‖x‖ ≤ ‖weightedNormalOperator S x‖ := by
  let B := weightedNormalOperator S
  change ‖x‖ ≤ ‖B x‖
  by_cases hx : x = 0
  · simp [hx]
  · have h : ‖x‖ ^ 2 + ‖S x‖ ^ 2 = RCLike.re (inner 𝕜 x (B x)) := by
      change _ = RCLike.re (inner 𝕜 x (x + S.adjoint (S x)))
      rw [inner_add_right, _root_.map_add, inner_self_eq_norm_sq,
        S.apply_norm_sq_eq_inner_adjoint_right]
      rfl
    apply (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hx)).mp
    have hb := re_inner_le_norm (𝕜 := 𝕜) x (B x)
    nlinarith [sq_nonneg ‖S x‖]

/-- The normal operator is an invertible bounded linear operator. -/
noncomputable def weightedNormalEquiv (S : E →L[𝕜] G) : E ≃L[𝕜] E := by
  let B := weightedNormalOperator S
  have hk : B.ker = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have h := weightedNormalOperator_lower S x
    change ‖x‖ ≤ ‖B x‖ at h
    have hz : B x = 0 := hx
    rw [hz, norm_zero] at h
    exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
  have hB : (B.toLinearMap.toPMap ⊤).IsClosed := by
    have hD : IsClosed (((⊤ : Submodule 𝕜 E) : Set E)) := by
      rw [Submodule.top_coe]
      exact isClosed_univ
    exact B.isClosed_toPMap hD
  have hR : IsClosed (B.range : Set E) := by
    rw [← LinearMap.range_toPMap_top B.toLinearMap]
    apply hB.isClosed_range_of_norm_le (C := 1)
    intro u
    change ‖(u : E)‖ ≤ 1 * ‖B (u : E)‖
    rw [one_mul]
    exact weightedNormalOperator_lower S u
  have hAdj : B.adjoint = B := by
    change (ContinuousLinearMap.id 𝕜 E + S.adjoint.comp S).adjoint =
      ContinuousLinearMap.id 𝕜 E + S.adjoint.comp S
    rw [_root_.map_add, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint]
  have hc : B.range = ⊤ := by
    have := hR.completeSpace_coe
    apply B.range.orthogonal_eq_bot_iff.mp
    rw [B.orthogonal_range, hAdj, hk]
  exact ContinuousLinearEquiv.ofBijective B hk hc

/-- The bounded equivalence acts as the normal operator. -/
theorem weightedNormalEquiv_apply (S : E →L[𝕜] G) (x : E) :
    weightedNormalEquiv S x = weightedNormalOperator S x := rfl

/-- The weighted square objective with one shift in the domain
and a second shift in the codomain of the weighting operator. -/
def weightedExtremalCost (S : E →L[𝕜] G) (x₁ : E) (y₁ : G) (x : E) : ℝ :=
  ‖S x - y₁‖ ^ 2 + ‖x - x₁‖ ^ 2

/-- The weighted objective is minimized among exact solutions of the
original equation. -/
def IsWeightedExtremalSolution (T : E →L[𝕜] F) (S : E →L[𝕜] G)
    (y : F) (x₁ : E) (y₁ : G) (x : E) : Prop :=
  T x = y ∧ ∀ z, T z = y → weightedExtremalCost S x₁ y₁ x ≤ weightedExtremalCost S x₁ y₁ z

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace G] [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 F] in
private theorem norm_add_sq_expand {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (a b : H) : ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 + 2 * RCLike.re (inner 𝕜 a b) := by
  have h := re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (𝕜 := 𝕜) a b
  linarith only [h]

omit [CompleteSpace F] in
private theorem cost_add_sq_of_normal_equation (T : E →L[𝕜] F) (S : E →L[𝕜] G)
    (x₁ : E) (y₁ : G) {x z : E} (hz : T z = T x)
    (hK : weightedNormalOperator S x - (x₁ + S.adjoint y₁) ∈ T.kerᗮ) :
    weightedExtremalCost S x₁ y₁ z =
      weightedExtremalCost S x₁ y₁ x + (‖S (z - x)‖ ^ 2 + ‖z - x‖ ^ 2) := by
  let d := z - x
  have hd : d ∈ T.ker := by
    change T (z - x) = 0
    rw [_root_.map_sub, hz, sub_self]
  have h := T.ker.inner_left_of_mem_orthogonal hd hK
  have hn : weightedNormalOperator S x - (x₁ + S.adjoint y₁) =
      (x - x₁) + S.adjoint (S x - y₁) := by
    change (x + S.adjoint (S x)) - (x₁ + S.adjoint y₁) = _
    rw [_root_.map_sub]
    abel
  rw [hn, inner_add_left, S.adjoint_inner_left] at h
  have he := congrArg RCLike.re h
  rw [_root_.map_add, RCLike.zero_re] at he
  have h₁ : S z - y₁ = (S x - y₁) + S d := by
    rw [show S d = S z - S x from _root_.map_sub S z x]
    abel
  have h₂ : z - x₁ = (x - x₁) + d := by dsimp [d]; abel
  unfold weightedExtremalCost
  rw [h₁, h₂, norm_add_sq_expand (𝕜 := 𝕜), norm_add_sq_expand (𝕜 := 𝕜)]
  linarith

omit [CompleteSpace F] in
private theorem normal_equation_isWeightedExtremalSolution (T : E →L[𝕜] F) (S : E →L[𝕜] G)
    (y : F) (x₁ : E) (y₁ : G) {x : E} (hx : T x = y)
    (hK : weightedNormalOperator S x - (x₁ + S.adjoint y₁) ∈ T.kerᗮ) :
    IsWeightedExtremalSolution T S y x₁ y₁ x ∧
      ∀ z, IsWeightedExtremalSolution T S y x₁ y₁ z → z = x := by
  have hcost (z : E) (hz : T z = y) :=
    cost_add_sq_of_normal_equation T S x₁ y₁ (hz.trans hx.symm) hK
  constructor
  · refine ⟨hx, fun z hz => ?_⟩
    rw [hcost z hz]
    exact le_add_of_nonneg_right (add_nonneg (sq_nonneg _) (sq_nonneg _))
  · intro z hz
    by_contra hne
    have hs := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
    have hle := hz.2 x hx
    rw [hcost z hz.1] at hle
    linarith [sq_nonneg ‖S (z - x)‖]

omit [CompleteSpace E] [CompleteSpace F] in
private theorem isClosed_range_of_range_eq_top (T : E →L[𝕜] F)
    (hTop : T.range = ⊤) : IsClosed (T.range : Set F) := by
  rw [hTop, Submodule.top_coe]
  exact isClosed_univ

/-- **Exercise 48** of [benIsrael2003generalized].
For a surjective operator there is a unique weighted minimizer on each
fiber. The unique multiplier is determined by the displayed equation.
The domain shift is the given vector x₁. -/
theorem exercise_9_48 (T : E →L[𝕜] F) (S : E →L[𝕜] G)
    (hTop : T.range = ⊤) (y : F) (x₁ : E) (y₁ : G) :
    let B := boundedMoorePenroseInverse T (isClosed_range_of_range_eq_top T hTop)
    let e := weightedNormalEquiv S
    let c := x₁ + S.adjoint y₁
    let x := fun w : F => e.symm (B w + c)
    (∃! w : F, T (x w) = y) ∧
    (∃! z : E, IsWeightedExtremalSolution T S y x₁ y₁ z) ∧
    ∀ w, T (x w) = y → IsWeightedExtremalSolution T S y x₁ y₁ (x w) := by
  intro B e c x
  let hR := isClosed_range_of_range_eq_top T hTop
  let K := T.ker
  let : CompleteSpace K := T.isClosed_ker.completeSpace_coe
  let I := K.subtypeL
  let U := S.comp I
  let p := B y
  have hp : T p = y := by
    have h := (boundedMoorePenroseInverse_projections T hR).1
    change (T.comp B) y = y
    rw [h]
    apply Submodule.starProjection_eq_self_iff.mpr
    apply T.range.le_topologicalClosure
    rw [hTop]
    trivial
  let P := K.orthogonalProjectionOnto
  let u := (weightedNormalEquiv U).symm (P (c - weightedNormalOperator S p))
  let z : E := p + I u
  have hz : T z = y := by
    change T (p + (u : E)) = y
    rw [_root_.map_add, hp, show T (u : E) = 0 from u.2, add_zero]
  have hU (k : K) : P (weightedNormalOperator S k) = weightedNormalOperator U k := by
    change P ((k : E) + S.adjoint (S k)) = k + (S.comp I).adjoint (S k)
    rw [_root_.map_add, ContinuousLinearMap.adjoint_comp, Submodule.adjoint_subtypeL]
    rw [show P (k : E) = k from K.orthogonalProjectionOnto_mem_subspace_eq_self k]
    rfl
  have hzK : weightedNormalOperator S z - c ∈ Kᗮ := by
    rw [← K.ker_orthogonalProjectionOnto]
    change P (weightedNormalOperator S (p + (u : E)) - c) = 0
    rw [_root_.map_sub, _root_.map_add, _root_.map_add, hU]
    have hu : weightedNormalOperator U u = P (c - weightedNormalOperator S p) := by
      rw [← weightedNormalEquiv_apply]
      exact (weightedNormalEquiv U).apply_symm_apply _
    rw [hu, _root_.map_sub]
    abel
  have hBr := (boundedMoorePenroseInverse_range_ker T hR).1
  have hrange : weightedNormalOperator S z - c ∈ B.range := hBr.symm ▸ hzK
  obtain ⟨w₀, hw₀⟩ := hrange
  have hEx : x w₀ = z := by
    apply e.injective
    change e (e.symm (B w₀ + c)) = e z
    rw [e.apply_symm_apply, show B w₀ = weightedNormalOperator S z - c from hw₀,
      sub_add_cancel, show e z = weightedNormalOperator S z from weightedNormalEquiv_apply S z]
  have hBinj : Function.Injective B := by
    apply LinearMap.ker_eq_bot.mp
    change B.ker = ⊥
    rw [(boundedMoorePenroseInverse_range_ker T hR).2, hTop, Submodule.top_orthogonal_eq_bot]
  have hnormal (w : F) : weightedNormalOperator S (x w) - c ∈ Kᗮ := by
    have h : weightedNormalOperator S (x w) = B w + c := by
      rw [← weightedNormalEquiv_apply]
      exact e.apply_symm_apply _
    rw [h, add_sub_cancel_right, ← hBr]
    exact ⟨w, rfl⟩
  have hx (w : F) (hw : T (x w) = y) :=
    normal_equation_isWeightedExtremalSolution T S y x₁ y₁ hw (hnormal w)
  have hmin := normal_equation_isWeightedExtremalSolution T S y x₁ y₁ hz hzK
  refine ⟨⟨w₀, (congrArg T hEx).trans hz, ?_⟩, ⟨z, hmin.1, hmin.2⟩, fun w hw => (hx w hw).1⟩
  intro w hw
  apply hBinj
  have he : x w = x w₀ := (hmin.2 _ (hx w hw).1).trans hEx.symm
  exact add_right_cancel (e.symm.injective he)

/-- **Exercise 47** of [benIsrael2003generalized].
The unshifted weighted least-norm problem is the zero-shift case of
the multiplier formula. -/
theorem exercise_9_47 (T : E →L[𝕜] F) (S : E →L[𝕜] G)
    (hTop : T.range = ⊤) (y : F) :
    let x := fun w : F => (weightedNormalEquiv S).symm
      (boundedMoorePenroseInverse T (isClosed_range_of_range_eq_top T hTop) w)
    (∃! w : F, T (x w) = y) ∧
    (∃! z : E, T z = y ∧ ∀ v, T v = y → ‖S z‖ ^ 2 + ‖z‖ ^ 2 ≤ ‖S v‖ ^ 2 + ‖v‖ ^ 2) ∧
    ∀ w, T (x w) = y → IsWeightedExtremalSolution T S y 0 0 (x w) := by
  simpa only [IsWeightedExtremalSolution, weightedExtremalCost, _root_.map_zero,
    sub_zero, zero_add, add_zero] using exercise_9_48 T S hTop y (0 : E) (0 : G)

end Weighted


section DomainExamples

private theorem extremalKernelPart_eq_ker_of_isClosable {T : E →ₗ.[𝕜] F}
    (hT : T.IsClosable) : extremalKernelPart T = T.ker := by
  have hle := T.le_closure
  have hk : T.ker ≤ T.closure.ker := by
    intro x hx
    obtain ⟨u, rfl, hu⟩ := LinearPMap.mem_ker_iff.mp hx
    let v : T.closure.domain := ⟨u, hle.1 u.2⟩
    exact LinearPMap.mem_ker_iff.mpr ⟨v, rfl, (hle.2 (x := u) (y := v) rfl).symm.trans hu⟩
  have hkc := T.ker.topologicalClosure_minimal hk
    (isClosed_kernel_of_isClosed _ hT.closure_isClosed)
  refine le_antisymm (fun x hx => ?_) (le_inf T.ker_le_domain T.ker.le_topologicalClosure)
  let u : T.domain := ⟨x, hx.1⟩
  let v : T.closure.domain := ⟨x, hle.1 hx.1⟩
  have hv : T.closure v = 0 := T.closure.coe_mem_ker_iff.mp (hkc hx.2)
  exact T.coe_mem_ker_iff.mpr ((hle.2 (x := u) (y := v) rfl).trans hv)

/-- **Exercise 42** of [benIsrael2003generalized].
The rank-one operator of Exercise 4 has nonzero range complementary to
the specified kernel. Its carrier is zero, its extremal inverse is zero
on the perpendicular complement of the range, and its iterated inverse
is zero everywhere. -/
theorem exercise_9_42 [CompleteSpace E] (D : Submodule 𝕜 E) (hD : Dense (D : Set E))
    (v : E) (hv : v ∉ D) :
    ∃ (T : E →ₗ.[𝕜] E) (A : Submodule 𝕜 E),
      T.domain = D ∧ T.ker = D ⊓ (𝕜 ∙ v)ᗮ ∧ carrier T = ⊥ ∧
      A = T.toFun.range ∧ A ≠ ⊥ ∧ Disjoint A T.ker ∧ T.domain = A ⊔ T.ker ∧
      extremalKernelPart T = T.ker ∧ (extremalInverse T).domain = Aᗮ ∧
      (extremalInverse T).ker = Aᗮ ∧ iteratedExtremalInverse T = 0 := by
  obtain ⟨T, hdom, _, hTClo, hA, hTC, hk, hfix⟩ := exercise_9_4_rankOne D hD v hv
  let A := T.toFun.range
  have hAK : A ≤ T.domain := by
    rintro _ ⟨u, rfl⟩
    exact LinearPMap.mem_domain_of_mem_graph (hfix u)
  have hRdom : T.domain = A ⊔ T.ker := by
    refine le_antisymm (fun x hx => ?_) (sup_le hAK T.ker_le_domain)
    let u : T.domain := ⟨x, hx⟩
    obtain ⟨a, hua, ha⟩ := T.mem_graph_iff.mp (hfix u)
    have hka : (↑(u - a) : E) ∈ T.ker := T.coe_mem_ker_iff.mpr
      (by rw [LinearPMap.map_sub, ha, sub_self])
    change (↑a : E) = T u at hua
    refine Submodule.mem_sup.mpr ⟨T u, ⟨u, rfl⟩, ↑(u - a), hka, ?_⟩
    change T u + (x - (a : E)) = x
    rw [hua]
    abel
  have hDisj : Disjoint A T.ker := by
    rw [Submodule.disjoint_def]
    rintro _ ⟨u, rfl⟩ hu
    obtain ⟨a, hua, ha⟩ := T.mem_graph_iff.mp (hfix u)
    exact ha.symm.trans (T.coe_mem_ker_iff.mp (hua ▸ hu))
  have hImage : (restrictCarrier T).toFun.range = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro _ ⟨a, rfl⟩
    have hp : (a : E) ∈ carrier T := restrictCarrier_domain T ▸ a.2
    rw [hTC] at hp
    have h0 : (a : E) = 0 := by simpa only [Submodule.mem_bot] using hp
    rw [show a = 0 from Subtype.ext h0, LinearMap.map_zero]
  refine ⟨T, A, hdom, hk, hTC, rfl, hA, hDisj, hRdom,
    extremalKernelPart_eq_ker_of_isClosable hTClo, ?_, extremalInverse_ker T, ?_⟩
  · rw [extremalInverse_domain, hImage, bot_sup_eq]
  · rw [← LinearPMap.ker_eq_top, (exercise_9_40 T).2.2, hTC, Submodule.bot_orthogonal_eq_top]

private theorem eq_zero_of_add_smul_eq_zero_of_not_mem {H : Type*} [AddCommGroup H] [Module 𝕜 H]
    {L : Submodule 𝕜 H} {x y : H} (hx : x ∈ L) (hy : y ∉ L)
    {c : 𝕜} (h : x + c • y = 0) : c = 0 ∧ x = 0 := by
  suffices h₀ : c = 0 from ⟨h₀, by simpa only [h₀, zero_smul, add_zero] using h⟩
  by_contra hc
  apply hy
  have he : c • y = -x := eq_neg_of_add_eq_zero_right h
  have hy' := L.smul_mem c⁻¹ (he.symm ▸ L.neg_mem hx)
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hy'

set_option maxHeartbeats 700000 in
-- The construction uses several elaborations of partial maps on a three-summand domain.
/-- **Exercise 43** of [benIsrael2003generalized].
The specified nonclosed subspaces give an operator whose nonzero
complement line is disjoint from the iterated inverse domain. -/
theorem exercise_9_43 [CompleteSpace E] (M N : Submodule 𝕜 E) (hN : N ≤ Mᗮ)
    {y z : E} (hy : y ∈ M.topologicalClosure) (hy' : y ∉ M)
    (hz : z ∈ Mᗮ) (hz' : z ∉ N ⊔ (Nᗮ ⊓ Mᗮ)) :
    let x := y + z
    let A : Submodule 𝕜 E := 𝕜 ∙ x
    ∃ T : E →ₗ.[𝕜] E, T.domain = M ⊔ (N ⊔ A) ∧ T.ker = M ∧ carrier T = N ∧
      extremalKernelPart T = M ∧ A ≠ ⊥ ∧ Disjoint A (M ⊔ N) ∧
      Disjoint A (iteratedExtremalInverse T).domain ∧
      ∀ a ∈ M, ∀ b ∈ N, ∀ t : 𝕜, (a + (b + t • x), b + t • x) ∈ T.graph := by
  intro x A
  let P := Mᗮ.starProjection
  let Q := M.topologicalClosure.starProjection
  have hQorth : M.topologicalClosureᗮ = Mᗮ := M.orthogonal_closure
  have hPzero {u : E} (hu : u ∈ M.topologicalClosure) : P u = 0 := by
    apply (Mᗮ.starProjection_apply_eq_zero_iff).mpr
    rw [M.orthogonal_orthogonal_eq_closure]
    exact hu
  have hPfix {u : E} (hu : u ∈ Mᗮ) : P u = u :=
    Submodule.starProjection_eq_self_iff.mpr hu
  have hQzero {u : E} (hu : u ∈ Mᗮ) : Q u = 0 := by
    apply (M.topologicalClosure.starProjection_apply_eq_zero_iff).mpr
    rwa [hQorth]
  have hQfix {u : E} (hu : u ∈ M.topologicalClosure) : Q u = u :=
    Submodule.starProjection_eq_self_iff.mpr hu
  have hPx : P x = z := by change P (y + z) = z; rw [_root_.map_add, hPzero hy, hPfix hz, zero_add]
  have hQx : Q x = y := by change Q (y + z) = y; rw [_root_.map_add, hQfix hy, hQzero hz, add_zero]
  have hzN : z ∉ N := fun h => hz' ((le_sup_left : N ≤ N ⊔ (Nᗮ ⊓ Mᗮ)) h)
  have hsum {b : E} (hb : b ∈ N) {t : 𝕜} (hs : b + t • x ∈ M.topologicalClosure) :
      t = 0 ∧ b = 0 := by
    have h := hPzero hs
    rw [_root_.map_add, _root_.map_smul, hPfix (hN hb), hPx] at h
    exact eq_zero_of_add_smul_eq_zero_of_not_mem hb hzN h
  let W := N ⊔ A
  have hMW : Disjoint M W := by
    rw [Submodule.disjoint_def]
    intro u hu huw
    obtain ⟨b, hb, c, hc, he⟩ := Submodule.mem_sup.mp huw
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hc
    have h := hsum hb (he.symm ▸ M.le_topologicalClosure hu)
    rw [h.1, h.2, zero_smul, zero_add] at he
    exact he.symm
  let Z : E →ₗ.[𝕜] E := (0 : E →ₗ[𝕜] E).toPMap M
  let I : E →ₗ.[𝕜] E := (LinearMap.id : E →ₗ[𝕜] E).toPMap W
  let hI := LinearPMap.sup_h_of_disjoint Z I hMW
  let T := Z.sup I hI
  have hTdom : T.domain = M ⊔ W := rfl
  have hApply (a : E) (ha : a ∈ M) (b : E) (hb : b ∈ W) :
      (a + b, b) ∈ T.graph := by
    have hu : a + b ∈ T.domain := Submodule.mem_sup.mpr ⟨a, ha, b, hb, rfl⟩
    have hval : T ⟨a + b, hu⟩ = b := by
      have h := LinearPMap.sup_apply hI (⟨a, ha⟩ : Z.domain) (⟨b, hb⟩ : I.domain) ⟨a + b, hu⟩ rfl
      exact h.trans (zero_add _)
    exact (LinearPMap.image_iff hu).mp hval.symm
  have hker : T.ker = M := by
    ext u
    constructor
    · intro hu
      obtain ⟨v', rfl, hv'⟩ := LinearPMap.mem_ker_iff.mp hu
      have hd : (v' : E) ∈ M ⊔ W := v'.2
      obtain ⟨a, ha, b, hb, he⟩ := Submodule.mem_sup.mp hd
      have hg : ((v' : E), b) ∈ T.graph := he ▸ hApply a ha b hb
      have hval : b = T v' := (LinearPMap.image_iff v'.2).mpr hg
      rw [hv'] at hval
      rw [← he, hval, add_zero]
      exact ha
    · intro hu
      have hg := hApply u hu 0 W.zero_mem
      rw [add_zero] at hg
      obtain ⟨v', hv', hv'0⟩ := T.mem_graph_iff.mp hg
      exact LinearPMap.mem_ker_iff.mpr ⟨v', hv'.symm, hv'0⟩
  have hD (u : E) (hu : u ∈ T.domain) :
      ∃ a ∈ M, ∃ b ∈ N, ∃ t : 𝕜, a + (b + t • x) = u := by
    obtain ⟨a, ha, w, hw, he⟩ := Submodule.mem_sup.mp (show u ∈ M ⊔ W from hu)
    obtain ⟨b, hb, c, hc, hc'⟩ := Submodule.mem_sup.mp hw
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hc
    exact ⟨a, ha, b, hb, t, by rw [hc', he]⟩
  have hC : carrier T = N := by
    unfold carrier
    rw [hker]
    have hND : N ≤ T.domain := by
      rw [hTdom]
      exact (le_sup_left : N ≤ N ⊔ A).trans le_sup_right
    refine le_antisymm (fun u hu => ?_) (le_inf hND hN)
    obtain ⟨a, ha, b, hb, t, he⟩ := hD u hu.1
    have h := hQzero hu.2
    rw [← he, _root_.map_add, _root_.map_add, _root_.map_smul,
      hQfix (M.le_topologicalClosure ha), hQzero (hN hb), hQx, zero_add] at h
    obtain ⟨ht, ha0⟩ := eq_zero_of_add_smul_eq_zero_of_not_mem ha hy' h
    simpa only [← he, ht, ha0, zero_smul, add_zero, zero_add] using hb
  have hB : extremalKernelPart T = M := by
    unfold extremalKernelPart
    rw [hker]
    have hMD : M ≤ T.domain := by rw [hTdom]; exact le_sup_left
    refine le_antisymm (fun u hu => ?_) (le_inf hMD M.le_topologicalClosure)
    obtain ⟨a, ha, b, hb, t, he⟩ := hD u hu.1
    have h : b + t • x ∈ M.topologicalClosure := by
      have ht := M.topologicalClosure.sub_mem hu.2 (M.le_topologicalClosure ha)
      rw [← he, add_sub_cancel_left] at ht
      exact ht
    obtain ⟨ht, hb0⟩ := hsum hb h
    simpa only [← he, ht, hb0, zero_smul, add_zero] using ha
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, _root_.map_zero] at hPx
    exact hzN (hPx ▸ N.zero_mem)
  have hxD : x ∉ (iteratedExtremalInverse T).domain := by
    rw [(exercise_9_40 T).1, hC]
    intro h
    obtain ⟨b, hb, u, hu, he⟩ := Submodule.mem_sup.mp h
    have hPu : P u ∈ Nᗮ := by
      apply (Submodule.mem_orthogonal _ _).mpr
      intro a ha
      change inner 𝕜 a (Mᗮ.starProjection u) = 0
      rw [← Mᗮ.inner_starProjection_left_eq_right]
      have h := hPfix (hN ha)
      change Mᗮ.starProjection a = a at h
      rw [h]
      exact N.inner_right_of_mem_orthogonal ha hu
    have hsum' := congrArg P he
    rw [_root_.map_add, hPfix (hN hb), hPx] at hsum'
    exact hz' (Submodule.mem_sup.mpr ⟨b, hb, P u, ⟨hPu, Mᗮ.starProjection_apply_mem u⟩, hsum'⟩)
  refine ⟨T, hTdom, hker, hC, hB, ?_, ?_, ?_, ?_⟩
  · intro h
    have hx : x ∈ A := Submodule.subset_span (by simp)
    rw [h] at hx
    exact hx0 (by simpa only [Submodule.mem_bot] using hx)
  · rw [Submodule.disjoint_def]
    intro u hu hw
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hu
    obtain ⟨a, ha, b, hb, he⟩ := Submodule.mem_sup.mp hw
    have h := congrArg Q he
    rw [_root_.map_add, _root_.map_smul, hQfix (M.le_topologicalClosure ha), hQzero (hN hb), hQx,
      add_zero] at h
    have h₀ : t = 0 := by
      by_contra ht
      have hh : t • y ∈ M := h ▸ ha
      have hm := M.smul_mem t⁻¹ hh
      apply hy'
      simpa only [smul_smul, inv_mul_cancel₀ ht, one_smul] using hm
    rw [h₀, zero_smul]
  · rw [Submodule.disjoint_def]
    intro u hu h
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hu
    by_cases ht : t = 0
    · rw [ht, zero_smul]
    · exfalso
      apply hxD
      simpa only [smul_smul, inv_mul_cancel₀ ht, one_smul] using
        (iteratedExtremalInverse T).domain.smul_mem t⁻¹ h
  · intro a ha b hb t
    have hc : t • x ∈ A := Submodule.mem_span_singleton.mpr ⟨t, rfl⟩
    exact hApply a ha _ (Submodule.mem_sup.mpr ⟨b, hb, t • x, hc, rfl⟩)

end DomainExamples


section FurtherExamples

open Filter
open scoped Topology ENNReal

/-- **Exercise 37** of [benIsrael2003generalized].
The harmonic-coordinate datum for the diagonal operator from Exercise 7
has no extremal solution. -/
theorem exercise_9_37_diagonal (k : ℝ) (h₀ : 0 < k) (h₁ : k < 1) :
    let H := lp (fun _ : ℕ => ℝ) 2
    ∃ (T : H →L[ℝ] H) (y : H), (∀ x n, T x n = k ^ n * x n) ∧
      (∀ n : ℕ, y n = ((n : ℝ) + 1)⁻¹) ∧
      let P : H →ₗ.[ℝ] H := T.toLinearMap.toPMap ⊤
      ¬ ∃ x : P.domain, IsExtremalSolution P y x := by
  obtain ⟨T, hT, _, hD, _⟩ := exercise_9_7 k h₀ h₁
  let H := lp (fun _ : ℕ => ℝ) 2
  let w (n : ℕ) := ((n : ℝ) + 1)⁻¹
  have hw : Memℓp w 2 := by
    apply memℓp_gen
    have hs := Real.summable_nat_pow_inv.mpr (by decide : 1 < (2 : ℕ))
    have hshift := (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) 1).mpr hs
    refine hshift.congr fun n => ?_
    have hw₀ : 0 ≤ w n := inv_nonneg.mpr (by positivity : 0 ≤ (n : ℝ) + 1)
    rw [Real.norm_eq_abs, abs_of_nonneg hw₀]
    change (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ = (w n) ^ ((2 : ℝ≥0∞).toReal)
    rw [Nat.cast_add, Nat.cast_one]
    norm_num [w, ← inv_pow]
  let y : H := ⟨w, hw⟩
  let P : H →ₗ.[ℝ] H := T.toLinearMap.toPMap ⊤
  refine ⟨T, y, hT, fun _ => rfl, exercise_9_37 P ?_ ?_⟩
  · rw [LinearMap.range_toPMap_top]
    change y ∈ closure (Set.range T)
    exact hD y
  · rw [LinearMap.range_toPMap_top]
    rintro ⟨x, hx⟩
    have hk : ‖k‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_pos h₀]
    have hs : Summable (fun n : ℕ => ((n : ℝ) + 1) * k ^ n) := by
      have h := (summable_pow_mul_geometric_of_norm_lt_one 1 hk).add
        (summable_pow_mul_geometric_of_norm_lt_one 0 hk)
      exact h.congr fun n => by simp only [pow_one, pow_zero, one_mul]; ring
    have hl : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * k ^ n * ‖x‖) atTop (𝓝 0) := by
      simpa only [zero_mul] using hs.tendsto_atTop_zero.mul_const ‖x‖
    have hsmall := hl.eventually_lt_const (show (0 : ℝ) < 1 from zero_lt_one)
    obtain ⟨n, hn⟩ := hsmall.exists
    have hc := congrArg (fun a : H => a n) hx
    change T x n = ((n : ℝ) + 1)⁻¹ at hc
    rw [hT] at hc
    have he : ((n : ℝ) + 1) * k ^ n * x n = 1 := by
      rw [mul_assoc, hc, mul_inv_cancel₀ (by positivity : (n : ℝ) + 1 ≠ 0)]
    have hb : x n ≤ ‖x‖ := (Real.le_norm_self _).trans (lp.norm_apply_le_norm (by norm_num) x n)
    have hbb := mul_le_mul_of_nonneg_left hb
      (by positivity : 0 ≤ ((n : ℝ) + 1) * k ^ n)
    rw [he] at hbb
    exact (not_lt_of_ge hbb) hn

/-- The compact-operator obstruction behind **Exercise 38** of
[benIsrael2003generalized]. A compact operator with infinite-dimensional
range always admits a datum without an extremal solution. -/
theorem exists_no_extremalSolution_of_compact_infinite_range [CompleteSpace E] [CompleteSpace F]
    (T : E →L[𝕜] F) (hT : IsCompactOperator T) (hInfinite : ¬ FiniteDimensional 𝕜 T.range) :
    ∃ y : F, ¬ ∃ x : (T.toLinearMap.toPMap ⊤).domain,
      IsExtremalSolution (T.toLinearMap.toPMap ⊤) y x := by
  apply exists_no_extremalSolution_of_nonclosed_range
  rw [LinearMap.range_toPMap_top, exercise_9_8b T hT]
  exact hInfinite

/-- **Exercise 38** of [benIsrael2003generalized].
The integral operator with the Dirichlet Green kernel for the negative
second derivative on the unit interval has a datum without an
extremal solution. -/
theorem exercise_9_38 :
    let T := (intervalDirichletGreenOperator (0 : ℝ) 1).toLinearMap.toPMap ⊤
    ∃ y : IntervalL2 0 1, ¬ ∃ x : T.domain, IsExtremalSolution T y x := by
  intro T
  apply exists_no_extremalSolution_of_nonclosed_range T
  change ¬ IsClosed (((intervalDirichletGreenOperator (0 : ℝ) 1).toLinearMap.toPMap ⊤).toFun.range :
    Set (IntervalL2 0 1))
  rw [LinearMap.range_toPMap_top]
  exact intervalDirichletGreenOperator_range_not_closed (by norm_num)

end FurtherExamples


section MomentExample

open MeasureTheory Set Filter
open scoped ENNReal

/-- Lebesgue measure restricted to the positive half-line. -/
noncomputable abbrev halfLineVolume : Measure ℝ :=
  volume.restrict (Ici (0 : ℝ))

/-- The space of square-integrable functions on the positive half-line. -/
noncomputable abbrev HalfLineL2 := Lp ℝ 2 halfLineVolume

/-- The domain on which the first moment is absolutely integrable. -/
def halfLineMomentDomain : Submodule ℝ HalfLineL2 where
  carrier := {f | Integrable (fun t => t * f t) halfLineVolume}
  zero_mem' := by
    have h : Integrable (fun _ : ℝ => (0 : ℝ)) halfLineVolume := integrable_zero ℝ ℝ halfLineVolume
    apply h.congr
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := (2 : ℝ≥0∞)) (μ := halfLineVolume)] with t ht
    change 0 = t * (0 : HalfLineL2) t
    rw [ht, Pi.zero_apply, mul_zero]
  add_mem' {f g} hf hg := by
    have h := hf.add hg
    apply h.congr
    filter_upwards [Lp.coeFn_add f g] with t ht
    change t * f t + t * g t = t * (f + g) t
    rw [ht, Pi.add_apply, mul_add]
  smul_mem' c f hf := by
    apply (hf.const_mul c).congr
    filter_upwards [Lp.coeFn_smul c f] with t ht
    change c * (t * f t) = t * (c • f) t
    rw [ht, Pi.smul_apply, smul_eq_mul]
    ring

/-- **Exercise 39** of [benIsrael2003generalized].
The absolutely integrable first moment defines a partial linear
functional on the half-line L² space. -/
noncomputable def halfLineMoment : HalfLineL2 →ₗ.[ℝ] ℝ where
  domain := halfLineMomentDomain
  toFun :=
    { toFun := fun f => ∫ t, t * f.val t ∂halfLineVolume
      map_add' := by
        intro f g
        change (∫ t, t * (f.val + g.val) t ∂halfLineVolume) = _
        calc
          _ = (∫ t, t * f.val t + t * g.val t ∂halfLineVolume) := by
            apply integral_congr_ae
            filter_upwards [Lp.coeFn_add f.val g.val] with t ht
            rw [ht, Pi.add_apply, mul_add]
          _ = _ := integral_add f.2 g.2
      map_smul' := by
        intro c f
        change (∫ t, t * (c • f.val) t ∂halfLineVolume) = c * (∫ t, t * f.val t ∂halfLineVolume)
        calc
          _ = (∫ t, c * (t * f.val t) ∂halfLineVolume) := by
            apply integral_congr_ae
            filter_upwards [Lp.coeFn_smul c f.val] with t ht
            rw [ht, Pi.smul_apply, smul_eq_mul]
            ring
          _ = _ := integral_const_mul c _ }

private abbrev momentWindow (a : ℝ) := Icc (1 : ℝ) (a + 1)

private theorem measure_momentWindow (a : ℝ) :
    halfLineVolume.restrict (momentWindow a) = (volume : Measure ℝ).restrict (momentWindow a) := by
  rw [halfLineVolume, Measure.restrict_restrict measurableSet_Icc, inter_eq_left.mpr]
  intro t ht
  exact (by norm_num : (0 : ℝ) ≤ 1).trans ht.1

private noncomputable abbrev momentTrial (a : ℝ) : ℝ → ℝ :=
  (momentWindow a).indicator (fun t => (a * t)⁻¹)

private theorem memLp_momentTrial {a : ℝ} (ha : 0 < a) :
    MemLp (momentTrial a) 2 halfLineVolume := by
  rw [momentTrial, memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet,
    measure_momentWindow]
  have : IsFiniteMeasure ((volume : Measure ℝ).restrict (momentWindow a)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hm : Measurable fun t : ℝ => (a * t)⁻¹ := by fun_prop
  apply MemLp.of_bound hm.aestronglyMeasurable a⁻¹
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc] with t ht
  have ht₁ : (1 : ℝ) ≤ t := ht.1
  have ht₀ : 0 < t := zero_lt_one.trans_le ht₁
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (mul_pos ha ht₀))]
  exact (inv_le_inv₀ (mul_pos ha ht₀) ha).mpr (by nlinarith [mul_nonneg ha.le (sub_nonneg.mpr ht₁)])

private theorem momentTrial_weighted {a : ℝ} (ha : 0 < a) (t : ℝ) :
    t * momentTrial a t = (momentWindow a).indicator (fun _ => a⁻¹) t := by
  by_cases h : t ∈ momentWindow a
  · rw [momentTrial, indicator_of_mem h, indicator_of_mem h]
    have ht : 0 < t := zero_lt_one.trans_le h.1
    field_simp
  · rw [momentTrial, indicator_of_notMem h, indicator_of_notMem h, mul_zero]

private theorem integrable_momentTrial_weighted {a : ℝ} (ha : 0 < a) :
    Integrable (fun t => t * momentTrial a t) halfLineVolume := by
  simp_rw [momentTrial_weighted ha]
  rw [integrable_indicator_iff measurableSet_Icc, IntegrableOn, measure_momentWindow]
  have : IsFiniteMeasure ((volume : Measure ℝ).restrict (momentWindow a)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  exact integrable_const _

private theorem integral_inv_sq_momentWindow {a : ℝ} (ha : 0 < a) :
    (∫ t in momentWindow a, t⁻¹ ^ 2) = 1 - (a + 1)⁻¹ := by
  have hle : (1 : ℝ) ≤ a + 1 := by linarith
  rw [momentWindow, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
  have hcond : (0 : ℝ) ∉ uIcc (1 : ℝ) (a + 1) := by
    rw [uIcc_of_le hle]
    norm_num
  have he : (∫ t in (1 : ℝ)..a + 1, t⁻¹ ^ 2) = ∫ t in (1 : ℝ)..a + 1, t ^ (-2 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht0 : 0 ≤ t := (by norm_num : (0 : ℝ) ≤ 1).trans (by rw [uIcc_of_le hle] at ht; exact ht.1)
    change t⁻¹ ^ 2 = t ^ (-(2 : ℝ))
    rw [Real.rpow_neg ht0, Real.rpow_two, inv_pow]
  rw [he, integral_rpow (Or.inr ⟨by norm_num, hcond⟩)]
  norm_num [Real.rpow_neg (show 0 ≤ a + 1 by linarith)]
  ring

/-- The explicit trial vector of **Exercise 39** has first moment one
and the stated squared norm. The parameter may be any positive real
number, so this in particular covers the printed sequence. -/
theorem halfLineMoment_trial (a : ℝ) (ha : 0 < a) :
    ∃ f : halfLineMoment.domain,
      ((f : HalfLineL2) : ℝ → ℝ) =ᵐ[halfLineVolume]
        (Icc (1 : ℝ) (a + 1)).indicator (fun t => (a * t)⁻¹) ∧
      halfLineMoment f = 1 ∧ ‖(f : HalfLineL2)‖ ^ 2 = (a * (a + 1))⁻¹ := by
  let f := (memLp_momentTrial ha).toLp (momentTrial a)
  have hf : (f : ℝ → ℝ) =ᵐ[halfLineVolume] momentTrial a := (memLp_momentTrial ha).coeFn_toLp
  have hfi : Integrable (fun t => t * f t) halfLineVolume :=
    (integrable_momentTrial_weighted ha).congr
      (hf.symm.mono fun t ht => congrArg (fun v => t * v) ht)
  let f' : halfLineMoment.domain := ⟨f, hfi⟩
  refine ⟨f', hf, ?_, ?_⟩
  · change (∫ t, t * f t ∂halfLineVolume) = 1
    have he : (∫ t, t * f t ∂halfLineVolume) =
        ∫ t, (momentWindow a).indicator (fun _ => a⁻¹) t ∂halfLineVolume :=
      integral_congr_ae (hf.mono fun t ht => by
        change t * f t = _
        rw [ht, momentTrial_weighted ha])
    rw [he, integral_indicator measurableSet_Icc, measure_momentWindow, integral_const,
      measureReal_def, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith : 0 ≤ a + 1 - 1), add_sub_cancel_right, smul_eq_mul,
      mul_inv_cancel₀ ha.ne']
  · change ‖f‖ ^ 2 = _
    have hL2 : ‖f‖ ^ 2 = ∫ t, momentTrial a t ^ 2 ∂halfLineVolume := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hf] with t ht
      rw [ht, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    have he : (fun t => momentTrial a t ^ 2) =
        (momentWindow a).indicator (fun t => a⁻¹ ^ 2 * t⁻¹ ^ 2) := by
      funext t
      by_cases ht : t ∈ momentWindow a
      · rw [momentTrial, indicator_of_mem ht, indicator_of_mem ht, mul_inv_rev, mul_pow, mul_comm]
      · simp only [momentTrial, indicator_of_notMem ht, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    rw [hL2, he, integral_indicator measurableSet_Icc, measure_momentWindow,
      integral_const_mul, integral_inv_sq_momentWindow ha]
    field_simp [ha.ne', show a + 1 ≠ 0 by positivity]
    ring

/-- **Exercise 39** of [benIsrael2003generalized].
The first-moment equation with datum one is consistent, but has no least
extremal solution. Its exact solutions contain vectors of arbitrarily
small norm. -/
theorem exercise_9_39 :
    (∃ f : halfLineMoment.domain, halfLineMoment f = 1) ∧
      ¬ ∃ f : halfLineMoment.domain, IsLeastExtremalSolution halfLineMoment 1 f := by
  obtain ⟨g, _, hg, _⟩ := halfLineMoment_trial 1 zero_lt_one
  refine ⟨⟨g, hg⟩, ?_⟩
  rintro ⟨f, hf⟩
  have he := hf.1 g
  rw [hg, sub_self, norm_zero] at he
  have hTf : halfLineMoment f = 1 :=
    (sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm he (norm_nonneg _)))).symm
  have hf₀ : (f : HalfLineL2) ≠ 0 := by
    intro h
    have h' : f = 0 := Subtype.ext h
    rw [h', LinearPMap.map_zero] at hTf
    exact zero_ne_one hTf
  have hn := norm_pos_iff.mpr hf₀
  let a := (‖(f : HalfLineL2)‖ ^ 2)⁻¹ + 1
  have ha : 0 < a := by positivity
  obtain ⟨u, _, hu, hu2⟩ := halfLineMoment_trial a ha
  have hsmall : ‖(u : HalfLineL2)‖ < ‖(f : HalfLineL2)‖ := by
    apply (sq_lt_sq₀ (norm_nonneg _) hn.le).mp
    rw [hu2, ← one_div]
    apply (div_lt_iff₀ (mul_pos ha (by positivity))).mpr
    have heq : ‖(f : HalfLineL2)‖ ^ 2 * a = 1 + ‖(f : HalfLineL2)‖ ^ 2 := by
      dsimp [a]
      rw [mul_add, mul_inv_cancel₀ (pow_ne_zero 2 hn.ne'), mul_one]
    rw [← mul_assoc, heq]
    nlinarith [sq_pos_of_pos hn, mul_pos (sq_pos_of_pos hn) ha]
  have hExt : IsExtremalSolution halfLineMoment 1 u := by
    intro w
    rw [hu, sub_self, norm_zero]
    exact norm_nonneg _
  have hne : u ≠ f := by intro h; rw [h] at hsmall; exact (lt_irrefl _) hsmall
  exact hsmall.not_gt (hf.2 u hExt hne)

end MomentExample

end BenIsraelGreville.Chapter09

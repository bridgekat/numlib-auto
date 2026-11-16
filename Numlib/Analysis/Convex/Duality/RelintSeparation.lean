/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Duality.Relint

/-!
# When a subspace meets a relative interior

The constraint qualifications of the exactness theory, "the range of $A$ meets
$\operatorname{ri}(\operatorname{dom} g)$" and "the effective domains have a common relative
interior point", are primal conditions. This module turns them into dual conditions: statements
about the directions $y$ of the pairing in which the sets are bounded. The presentation follows §11,
§13 and §16 of [rockafellar1970convex].

The main tool is proper separation. Two nonempty convex sets have disjoint relative interiors
exactly when some hyperplane separates them properly. Over a compatible pairing the separating
functional is $\langle \cdot, y \rangle$ for some $y$ in the second space, and the two conditions of
proper separation become two inequalities between values of the pairing. When one of the two sets is
a subspace $L$, a direction in which the pairing is bounded on $L$ is one in which it vanishes on
$L$. Then both extrema over $L$ are $0$, and the condition becomes a statement about one set
together with the annihilator of $L$.

## Main results

* `ConvexAnalysis.exists_pairing_le_iff_disjoint_relint`: proper separation over a pairing. The sets
  $\operatorname{ri} C_1$ and $\operatorname{ri} C_2$ are disjoint exactly when, for some $y$, the
  pairing with $y$ is nowhere larger on $C_1$ than on $C_2$ and is strictly smaller at one pair of
  points.
* `ConvexAnalysis.submodule_inter_relint_nonempty_iff`,
  `ConvexAnalysis.submodule_inter_relint_nonempty_iff_supportFn`: the case of a subspace, stated
  pointwise and through the support function.
* `ConvexAnalysis.submodule_inter_relint_convexDom_nonempty_iff`: the case of an effective domain,
  with the support function of $\operatorname{dom} f$ written as the recession function of $f^*$
  (Lemma 16.2 of [rockafellar1970convex]).
* `ConvexAnalysis.exists_apply_mem_relint_convexDom_iff`: the same for the range of a linear map,
  whose annihilator on the other side of the pairing is the kernel of the adjoint (Corollary 16.2.1
  of [rockafellar1970convex]).

## Implementation notes

* The general statement uses the pointwise inequalities $\langle x_1, y \rangle \le \langle x_2, y
  \rangle$, which mention no extended reals. The support function appears only when one of the two
  sets is a subspace, where two of the four extrema of the proper-separation criterion become $0$.
* Only $E$ carries a topology. Proper separation happens there and needs finite dimension, while $F$
  enters only through `ConvexAnalysis.IsCompatiblePairing` and is a plain module.
* Properness of $f^*$ is a hypothesis rather than a conclusion, as in
  `ConvexAnalysis.recessionFn_convexConj`. In finite dimensions a caller discharges it with
  `ConvexAnalysis.properConvex_convexConj_of_properConvex`.
-/

open Set

namespace ConvexAnalysis

/-! ### Boundedness on a subspace -/

section Support

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {y : F}

/-- **A linear function that is bounded above on a subspace vanishes on it.** Let $L$ be a subspace
of $E$, $y \in F$ and $c \in \mathbb{R}$. If $\langle x, y \rangle \le c$ for every $x \in L$,
then $\langle x, y \rangle = 0$ for every $x \in L$.

A subspace is closed under multiplication by every real scalar, so one nonzero value would make
the pairing unbounded on $L$. -/
theorem forall_pairing_eq_zero_of_forall_le {L : Submodule ℝ E} {c : ℝ}
    (h : ∀ x ∈ L, B x y ≤ c) : ∀ x ∈ L, B x y = 0 := by
  intro x hx
  by_contra hne
  have hmem : ((c + 1) / B x y) • x ∈ L := L.smul_mem _ hx
  have hbound := h _ hmem
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hne] at hbound
  linarith

end Support

/-! ### A subspace is relatively open -/

section Relint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- In a real normed space $E$, the relative interior of a subspace $L$ is $L$ itself:
$\operatorname{ri} L = L$. -/
theorem intrinsicInterior_coe_submodule (L : Submodule ℝ E) : ri (L : Set E) = (L : Set E) :=
  AffineSubspace.intrinsicInterior_coe (L : AffineSubspace ℝ E)

end Relint

/-! ### Proper separation, read through the pairing -/

section Separation

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {C C₁ C₂ : Set E}

/-- **Proper separation over a pairing.** Let $E$ be a finite-dimensional normed space, and let the
pairing be compatible with its topology. Let $C_1, C_2 \subseteq E$ be nonempty and convex. Then
$\operatorname{ri} C_1 \cap \operatorname{ri} C_2 = \emptyset$ if and only if there is $y \in F$
with
$$\langle x_1, y \rangle \le \langle x_2, y \rangle \quad\text{for all } x_1 \in C_1,\ x_2 \in
  C_2,$$
and $\langle x_1, y \rangle < \langle x_2, y \rangle$ for some $x_1 \in C_1$ and $x_2 \in C_2$. -/
theorem exists_pairing_le_iff_disjoint_relint (h₁ : Convex ℝ C₁) (h₂ : Convex ℝ C₂)
    (hne₁ : C₁.Nonempty) (hne₂ : C₂.Nonempty) :
    (∃ y : F, (∀ x₁ ∈ C₁, ∀ x₂ ∈ C₂, B x₁ y ≤ B x₂ y) ∧
        ∃ x₁ ∈ C₁, ∃ x₂ ∈ C₂, B x₁ y < B x₂ y) ↔ Disjoint (ri C₁) (ri C₂) := by
  rw [← exists_separatesProperly_iff_disjoint_relint h₁ h₂ hne₁ hne₂]
  constructor
  · rintro ⟨y, hle, x₁, hx₁, x₂, hx₂, hlt⟩
    refine ⟨evalCLM B y, ?_⟩
    rw [exists_separatesProperly_iff_iSup_le_iInf hne₁ hne₂]
    constructor
    · refine iSup₂_le fun a ha => le_iInf₂ fun b hb => ?_
      have hab : evalCLM B y a ≤ evalCLM B y b := hle a ha b hb
      exact_mod_cast hab
    · have hlt' : evalCLM B y x₁ < evalCLM B y x₂ := hlt
      calc (⨅ x ∈ C₁, ((evalCLM B y x : ℝ) : EReal))
          ≤ ((evalCLM B y x₁ : ℝ) : EReal) := iInf₂_le_coe_apply hx₁
        _ < ((evalCLM B y x₂ : ℝ) : EReal) := by exact_mod_cast hlt'
        _ ≤ ⨆ x ∈ C₂, ((evalCLM B y x : ℝ) : EReal) := coe_apply_le_iSup₂ hx₂
  · rintro ⟨g, c, hsep⟩
    obtain ⟨y, hy⟩ := exists_pairing_eq B g
    have hle : ∀ x₁ ∈ C₁, ∀ x₂ ∈ C₂, B x₁ y ≤ B x₂ y := by
      intro x₁ hx₁ x₂ hx₂
      have h₁ : g x₁ ≤ c := hsep.le_of_mem_left hx₁
      have h₂ : c ≤ g x₂ := hsep.le_of_mem_right hx₂
      rw [hy x₁] at h₁
      rw [hy x₂] at h₂
      linarith
    obtain ⟨q, hq, hqc⟩ : ∃ q, q ∈ C₁ ∪ C₂ ∧ g q ≠ c := by
      by_contra hcon
      push Not at hcon
      exact hsep.not_subset fun q hq => hcon q hq
    refine ⟨y, hle, ?_⟩
    rcases hq with hq | hq
    · obtain ⟨x₂, hx₂⟩ := hne₂
      refine ⟨q, hq, x₂, hx₂, ?_⟩
      have h₁ : g q < c := lt_of_le_of_ne (hsep.le_of_mem_left hq) hqc
      have h₂ : c ≤ g x₂ := hsep.le_of_mem_right hx₂
      rw [hy q] at h₁
      rw [hy x₂] at h₂
      linarith
    · obtain ⟨x₁, hx₁⟩ := hne₁
      refine ⟨x₁, hx₁, q, hq, ?_⟩
      have h₁ : g x₁ ≤ c := hsep.le_of_mem_left hx₁
      have h₂ : c < g q := lt_of_le_of_ne (hsep.le_of_mem_right hq) (Ne.symm hqc)
      rw [hy x₁] at h₁
      rw [hy q] at h₂
      linarith

/-- **A subspace meets the relative interior of a convex set** exactly when no direction of the
pairing annihilates the subspace, is nowhere positive on the set and is negative somewhere on
it. Let $E$ be a finite-dimensional normed space, and let the pairing be compatible with its
topology. Let $L$ be a subspace of $E$ and $C \subseteq E$ nonempty and convex. Then
$L \cap \operatorname{ri} C \neq \emptyset$ if and only if there is no $y \in F$ such that
* $\langle x, y \rangle = 0$ for every $x \in L$,
* $\langle x, y \rangle \le 0$ for every $x \in C$, and
* $\langle x, y \rangle < 0$ for some $x \in C$.

In the proof, the separating direction is not assumed to vanish on $L$. It vanishes on $L$
because the pairing with it is bounded below on $L$
(`ConvexAnalysis.forall_pairing_eq_zero_of_forall_le`). -/
theorem submodule_inter_relint_nonempty_iff (L : Submodule ℝ E) (hC : Convex ℝ C)
    (hne : C.Nonempty) :
    ((L : Set E) ∩ ri C).Nonempty ↔
      ¬ ∃ y : F, (∀ x ∈ L, B x y = 0) ∧ (∀ x ∈ C, B x y ≤ 0) ∧ ∃ x ∈ C, B x y < 0 := by
  have hzeroL : (0 : E) ∈ (L : Set E) := L.zero_mem
  have hkey : (∃ y : F, (∀ x ∈ L, B x y = 0) ∧ (∀ x ∈ C, B x y ≤ 0) ∧ ∃ x ∈ C, B x y < 0) ↔
      Disjoint (ri C) (ri (L : Set E)) := by
    rw [← exists_pairing_le_iff_disjoint_relint (B := B) hC L.convex hne ⟨0, hzeroL⟩]
    constructor
    · rintro ⟨y, hzero, hnonpos, x, hx, hlt⟩
      refine ⟨y, fun x₁ hx₁ x₂ hx₂ => ?_, x, hx, 0, hzeroL, ?_⟩
      · rw [hzero x₂ hx₂]
        exact hnonpos x₁ hx₁
      · rwa [hzero 0 L.zero_mem]
    · rintro ⟨y, hle, x₁, hx₁, x₂, hx₂, hlt⟩
      have hzero : ∀ x ∈ L, B x y = 0 := by
        have hneg : ∀ x ∈ L, B x (-y) ≤ -B x₁ y := by
          intro x hx
          rw [map_neg (B x) y]
          linarith [hle x₁ hx₁ x hx]
        intro x hx
        have h := forall_pairing_eq_zero_of_forall_le hneg x hx
        rw [map_neg (B x) y, neg_eq_zero] at h
        exact h
      refine ⟨y, hzero, fun x hx => ?_, x₁, hx₁, ?_⟩
      · rw [← hzero 0 L.zero_mem]
        exact hle x hx 0 hzeroL
      · rwa [← hzero x₂ hx₂]
  rw [hkey, intrinsicInterior_coe_submodule]
  constructor
  · rintro ⟨x, hxL, hxC⟩
    exact Set.not_disjoint_iff_nonempty_inter.2 ⟨x, hxC, hxL⟩
  · intro h
    obtain ⟨x, hxC, hxL⟩ := Set.not_disjoint_iff_nonempty_inter.1 h
    exact ⟨x, hxL, hxC⟩

/-- **A subspace meets the relative interior of a convex set**, with the two conditions on the set
written through its support function. Let $E$ be a finite-dimensional normed space, and let the
pairing be compatible with its topology. Let $L$ be a subspace of $E$ and $C \subseteq E$
nonempty and convex. Then $L \cap \operatorname{ri} C \neq \emptyset$ if and only if there is no
$y \in F$ such that $\langle x, y \rangle = 0$ for every $x \in L$ and
$$\delta^*(y \mid C) \le 0 < \delta^*(-y \mid C).$$
-/
theorem submodule_inter_relint_nonempty_iff_supportFn (L : Submodule ℝ E) (hC : Convex ℝ C)
    (hne : C.Nonempty) :
    ((L : Set E) ∩ ri C).Nonempty ↔
      ¬ ∃ y : F, (∀ x ∈ L, B x y = 0) ∧ supportFn B C y ≤ 0 ∧ 0 < supportFn B C (-y) := by
  rw [submodule_inter_relint_nonempty_iff (B := B) L hC hne]
  refine not_congr (exists_congr fun y => and_congr_right fun _ => ?_)
  rw [supportFn_le_zero_iff, zero_lt_supportFn_iff]
  refine and_congr_right fun _ => exists_congr fun x => and_congr_right fun _ => ?_
  rw [map_neg (B x) y, neg_pos]

end Separation

/-! ### The effective domain of a convex function -/

section Function

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {f : E → EReal}

/-- **A subspace meets the relative interior of an effective domain.** Let $E$ be a
finite-dimensional normed space, and let the pairing be compatible with its topology. Let $L$ be
a subspace of $E$, and let $f$ be a proper convex function on $E$ whose conjugate $f^*$ is
proper. Then $L \cap \operatorname{ri}(\operatorname{dom} f) \neq \emptyset$ if and only if
there is no $y \in F$ such that $\langle x, y \rangle = 0$ for every $x \in L$ and
$$(f^* 0^+)(y) \le 0 < (f^* 0^+)(-y),$$
where $f^* 0^+$ is the recession function of $f^*$. This is Lemma 16.2 of
[rockafellar1970convex].

The recession function of $f^*$ is the support function of $\operatorname{dom} f$
(`ConvexAnalysis.recessionFn_convexConj`), so this is
`ConvexAnalysis.submodule_inter_relint_nonempty_iff_supportFn` at $C = \operatorname{dom} f$. -/
theorem submodule_inter_relint_convexDom_nonempty_iff (L : Submodule ℝ E) (hf : ConvexFn f)
    (hp : ProperConvex f) (hc : ProperConvex (convexConj B f)) :
    ((L : Set E) ∩ ri (convexDom f)).Nonempty ↔
      ¬ ∃ y : F, (∀ x ∈ L, B x y = 0) ∧ recessionFn (convexConj B f) y ≤ 0 ∧
        0 < recessionFn (convexConj B f) (-y) := by
  rw [recessionFn_convexConj hp hc]
  exact submodule_inter_relint_nonempty_iff_supportFn L hf.convex_convexDom hp.convexDom_nonempty

end Function

/-! ### The range of a linear transformation -/

section Image

variable {E F G H : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [AddCommGroup H] [Module ℝ H]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ} [IsCompatiblePairing B']
  {A : E →ₗ[ℝ] G} {A' : H →ₗ[ℝ] F} {g : G → EReal}

omit [FiniteDimensional ℝ G] [IsCompatiblePairing B'] in
/-- **The annihilator of the range of $A$ is the kernel of its adjoint.** Let the pairing $B$ of $E$
and $F$ separate the points of $F$: if $\langle x, y \rangle = 0$ for every $x$, then $y = 0$.
Let $A : E \to G$ and $A' : H \to F$ be adjoint: $\langle Ax, z \rangle' = \langle x, A'z
\rangle$. Then for every $y \in H$, $\langle z, y \rangle' = 0$ for every $z$ in the range of
$A$ if and only if $A'y = 0$. -/
theorem forall_mem_range_eq_zero_iff (hB : B.SeparatingRight) (hA : IsAdjointPair B B' A A')
    (y : H) : (∀ z ∈ LinearMap.range A, B' z y = 0) ↔ A' y = 0 := by
  constructor
  · intro h
    refine hB _ fun x => ?_
    rw [← hA x y]
    exact h (A x) (LinearMap.mem_range_self A x)
  · intro h z hz
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.1 hz
    rw [hA x y, h, map_zero]

/-- Let $B$ pair $E$ with $F$ and separate the points of $F$, and let $B'$ pair a finite-dimensional
normed space $G$ with $H$, compatibly with the topology of $G$. Let $A : E \to G$ and
$A' : H \to F$ be adjoint: $\langle Ax, z \rangle' = \langle x, A'z \rangle$. Let $g$ be a
proper convex function on $G$ whose conjugate $g^*$ is proper. Then
$Ax \in \operatorname{ri}(\operatorname{dom} g)$ for some $x \in E$ if and only if there is no
$y \in H$ such that $A'y = 0$ and
$$(g^* 0^+)(y) \le 0 < (g^* 0^+)(-y).$$
This is Corollary 16.2.1 of [rockafellar1970convex].

The proof applies `ConvexAnalysis.submodule_inter_relint_convexDom_nonempty_iff` to the range of
$A$, whose annihilator is the kernel of $A'$ by `ConvexAnalysis.forall_mem_range_eq_zero_iff`. -/
theorem exists_apply_mem_relint_convexDom_iff (hB : B.SeparatingRight)
    (hA : IsAdjointPair B B' A A')
    (hg : ConvexFn g) (hp : ProperConvex g) (hc : ProperConvex (convexConj B' g)) :
    (∃ x, A x ∈ ri (convexDom g)) ↔
      ¬ ∃ y : H,
          A' y = 0 ∧ recessionFn (convexConj B' g) y ≤ 0 ∧ 0
              < recessionFn (convexConj B' g) (-y) := by
  have hmem : (∃ x, A x ∈ ri (convexDom g)) ↔
      ((LinearMap.range A : Set G) ∩ ri (convexDom g)).Nonempty := by
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨A x, LinearMap.mem_range_self A x, hx⟩
    · rintro ⟨z, hzL, hz⟩
      obtain ⟨x, rfl⟩ := LinearMap.mem_range.1 hzL
      exact ⟨x, hz⟩
  rw [hmem, submodule_inter_relint_convexDom_nonempty_iff (LinearMap.range A) hg hp hc]
  exact not_congr (exists_congr fun y =>
    and_congr (forall_mem_range_eq_zero_iff hB hA y) Iff.rfl)

end Image

end ConvexAnalysis

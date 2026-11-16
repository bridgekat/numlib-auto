/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Duality.Support
import Numlib.Analysis.Convex.RelativeInterior

/-!
# Relative interiors, interiors and affine hulls from the support function

Let $B$ be a bilinear pairing of real vector spaces $E$ and $F$, written
$\langle x, y \rangle = B(x, y)$, and let $\delta^*(y \mid s) = \sup_{x \in s} \langle x, y \rangle$
be the support function of a set $s \subseteq E$. The support function records the closed
half-spaces that contain $s$, and therefore it determines the closed convex hull:
$x \in \operatorname{cl}(\operatorname{conv} s)$ if and only if
$\langle x, y \rangle \le \delta^*(y \mid s)$ for every $y$. In finite dimensions it determines
more. The relative interior, the interior and the affine hull of a convex set are all determined by
which of these inequalities are strict. The presentation follows §1 and §13 of
[rockafellar1970convex].

The dividing line is the set of directions $y$ in which the support function is **additively
reversible**, $-\delta^*(-y \mid C) = \delta^*(y \mid C)$. These are exactly the directions in which
$\langle \cdot, y \rangle$ is constant on $C$, that is, in which $C$ lies in a hyperplane; no
inequality can be strict there. The relative interior asks for strictness in every other direction.
The interior asks for strictness in every direction except $0$, so no reversible directions other
than $0$ can exist. The affine hull asks for equality in the reversible directions and for nothing
in the other directions.

## Main results

* `ConvexAnalysis.supportFn_neg_eq_neg_iff`, `ConvexAnalysis.neg_supportFn_neg_eq_iff`: the
  reversible directions of a support function are its directions of constancy.
* `ConvexAnalysis.mem_relint_iff_lt_supportFn`, `ConvexAnalysis.mem_interior_iff_lt_supportFn`: the
  descriptions of $\operatorname{ri} C$ and $\operatorname{int} C$ (Theorem 13.1 of
  [rockafellar1970convex]).
* `ConvexAnalysis.mem_affineSpan_iff_eq_supportFn`: the description of $\operatorname{aff} C$. The
  affine hull of a set is the intersection of the hyperplanes that contain it. No convexity is
  needed.
* `ConvexAnalysis.isBounded_iff_forall_bddAbove`: a set is bounded in the norm exactly when its
  support function is finite everywhere.

The description of the closure is `ConvexAnalysis.mem_closure_convexHull_iff_le_supportFn` in
`Numlib.Analysis.Convex.Duality.Support`. It is the only one of the four descriptions that holds in
every locally convex space.

## Implementation notes

* All three descriptions in this module need finite dimension. Let $\varphi$ be a discontinuous
  linear functional and $C = \ker \varphi$, a dense proper subspace. Then
  $\operatorname{aff} C = \operatorname{ri} C = C$, while $\operatorname{int} C = \emptyset$. A
  continuous functional that is constant on a dense set vanishes, so the reversible directions of
  $\delta^*(\cdot \mid C)$ are exactly the $y$ with $\langle \cdot, y \rangle = 0$, and
  $\delta^*(y \mid C) = +\infty$ for all other $y$. Then every point of the space satisfies all
  three conditions.
* The description of the interior has two hypotheses that the classical statement does not write.
  The first is that $B$ separates the points of $F$. Over $\mathbb{R}^n$ paired with itself,
  $y \neq 0$ and $\langle \cdot, y \rangle \neq 0$ are the same condition. Over a general pairing, a
  $y \neq 0$ that pairs trivially with $E$ would demand $\langle x, y \rangle = 0 < \delta^*(y \mid
  C) = 0$. The second is that $C$ is nonempty. For $C = \emptyset$ the condition is false as soon as
  some $y \neq 0$ exists, and it is vacuously true over the zero space, where
  $\operatorname{int} \emptyset = \emptyset$.
-/

namespace ConvexAnalysis

/-! ### Directions of constancy -/

section Constancy

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {s : Set E} {y : F}

/-- **The support function in a direction of constancy is that constant.** Let $s \subseteq E$ be
nonempty, $y \in F$ and $c \in \mathbb{R}$. If $\langle x, y \rangle = c$ for every $x \in s$,
then $\delta^*(y \mid s) = c$. -/
theorem supportFn_eq_coe_of_forall_eq (hs : s.Nonempty) {c : ℝ} (h : ∀ x ∈ s, B x y = c) :
    supportFn B s y = ((c : ℝ) : EReal) := by
  obtain ⟨x₀, hx₀⟩ := hs
  refine le_antisymm (supportFn_le_coe_iff.2 fun x hx => (h x hx).le) ?_
  rw [← h x₀ hx₀]
  exact le_supportFn hx₀ y

/-- **A support function is additively reversible in a direction exactly when the pairing is
constant on the set.** Let $s \subseteq E$ be nonempty and $y \in F$. Then
$$\delta^*(-y \mid s) = -\delta^*(y \mid s) \iff \langle \cdot, y \rangle \text{ is constant on
  } s.$$

The left side says that the supremum and the infimum of $\langle \cdot, y \rangle$ over $s$
agree. Nonemptiness is necessary: for $s = \emptyset$ both $\delta^*(-y \mid s)$ and
$\delta^*(y \mid s)$ are $-\infty$, and $-(-\infty) = +\infty$. -/
theorem supportFn_neg_eq_neg_iff (hs : s.Nonempty) (y : F) :
    supportFn B s (-y) = -supportFn B s y ↔ ∃ c : ℝ, ∀ x ∈ s, B x y = c := by
  obtain ⟨x₀, hx₀⟩ := hs
  constructor
  · intro h
    have hbot : supportFn B s y ≠ ⊥ := supportFn_ne_bot ⟨x₀, hx₀⟩ y
    have hbot' : supportFn B s (-y) ≠ ⊥ := supportFn_ne_bot ⟨x₀, hx₀⟩ (-y)
    have htop : supportFn B s y ≠ ⊤ := by
      intro ht
      rw [ht, EReal.neg_top] at h
      exact hbot' h
    obtain ⟨c, hc⟩ :=
      EReal.exists_coe_of_ne_bot_of_lt_top hbot (lt_top_iff_ne_top.2 htop)
    refine ⟨c, fun x hx => ?_⟩
    have h1 : B x y ≤ c := supportFn_le_coe_iff.1 hc.le x hx
    have h2 : B x (-y) ≤ -c := by
      refine supportFn_le_coe_iff.1 ?_ x hx
      rw [h, hc, ← EReal.coe_neg]
    rw [map_neg] at h2
    linarith
  · rintro ⟨c, hc⟩
    have hy : supportFn B s y = ((c : ℝ) : EReal) :=
      supportFn_eq_coe_of_forall_eq ⟨x₀, hx₀⟩ hc
    have hy' : supportFn B s (-y) = ((-c : ℝ) : EReal) :=
      supportFn_eq_coe_of_forall_eq ⟨x₀, hx₀⟩ fun x hx => by rw [map_neg, hc x hx]
    rw [hy, hy', EReal.coe_neg]

/-- **Reversible directions are directions of constancy**, in the orientation that the descriptions
below use. Let $s \subseteq E$ be nonempty and $y \in F$. Then
$$-\delta^*(-y \mid s) = \delta^*(y \mid s) \iff \langle \cdot, y \rangle \text{ is constant on
  } s.$$

This is `ConvexAnalysis.supportFn_neg_eq_neg_iff` with the two sides of the equation exchanged. -/
theorem neg_supportFn_neg_eq_iff (hs : s.Nonempty) (y : F) :
    -supportFn B s (-y) = supportFn B s y ↔ ∃ c : ℝ, ∀ x ∈ s, B x y = c := by
  rw [neg_eq_iff_eq_neg]
  exact supportFn_neg_eq_neg_iff hs y

end Constancy

/-! ### The relative interior, the interior and the affine hull -/

section FiniteDim

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {C : Set E}

/-- **A point outside the affine hull is cut away from it by a direction of constancy.** Let $E$ be
a finite-dimensional normed space, and let the pairing be compatible with its topology. Let
$C \subseteq E$ be nonempty and $x \notin \operatorname{aff} C$. Then there are $y \in F$ and
$c \in \mathbb{R}$ with $\langle z, y \rangle = c$ for every $z \in C$ and
$\langle x, y \rangle \neq c$.

The affine hull is closed because the dimension is finite, so a point outside it is strongly
separated from it, and a linear functional that is bounded below on an affine set is constant on
it. -/
theorem exists_forall_eq_of_notMem_affineSpan (hne : C.Nonempty) {x : E}
    (hx : x ∉ affineSpan ℝ C) :
    ∃ (y : F) (c : ℝ), (∀ z ∈ C, B z y = c) ∧ B x y ≠ c := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨g, u, v, hgx, huv, hgA⟩ := geometric_hahn_banach_compact_closed
    (convex_singleton x) isCompact_singleton (affineSpan ℝ C).convex
    (affineSpan ℝ C).closed_of_finiteDimensional (Set.disjoint_singleton_left.2 hx)
  obtain ⟨y, hy⟩ := exists_pairing_eq B g
  refine ⟨y, g p, fun z hz => ?_, ?_⟩
  · rw [← hy z]
    exact eq_of_le_on_affineSubspace (fun w hw => (hgA w hw).le)
      (subset_affineSpan ℝ C hz) (subset_affineSpan ℝ C hp)
  · rw [← hy x]
    have h₁ : g x < u := hgx x rfl
    have h₂ : v < g p := hgA p (subset_affineSpan ℝ C hp)
    exact ne_of_lt (by linarith)

/-- **The relative interior from the support function.** Let $E$ be a finite-dimensional normed
space, and let the pairing be compatible with its topology: every functional
$\langle \cdot, y \rangle$ is continuous, and every continuous linear functional on $E$ has this
form. Let $C \subseteq E$ be convex and $x \in E$. Then $x \in \operatorname{ri} C$ if and only
if
* $\langle x, y \rangle \le \delta^*(y \mid C)$ for every $y \in F$, and
* $\langle x, y \rangle < \delta^*(y \mid C)$ for every $y \in F$ with
  $-\delta^*(-y \mid C) \neq \delta^*(y \mid C)$.

This is the description of the relative interior in Theorem 13.1 of [rockafellar1970convex]. In
terms of the pairing, $\langle x, y \rangle = \delta^*(y \mid C)$ holds exactly when
$\langle \cdot, y \rangle$ attains its maximum over $C$ at $x$, and this is compatible with
$x \in \operatorname{ri} C$ only when $\langle \cdot, y \rangle$ is constant on $C$. -/
theorem mem_relint_iff_lt_supportFn (hC : Convex ℝ C) (x : E) :
    x ∈ ri C ↔ (∀ y : F, ((B x y : ℝ) : EReal) ≤ supportFn B C y) ∧
      ∀ y : F, -supportFn B C (-y) ≠ supportFn B C y →
        ((B x y : ℝ) : EReal) < supportFn B C y := by
  constructor
  · intro hx
    have hxC : x ∈ C := intrinsicInterior_subset hx
    refine ⟨fun y => le_supportFn hxC y, fun y hy => ?_⟩
    rcases lt_or_eq_of_le (le_supportFn (B := B) hxC y) with hlt | heq
    · exact hlt
    · exfalso
      have hmax : ∀ z ∈ C, evalCLM B y z ≤ evalCLM B y x := fun z hz => by
        simpa using supportFn_le_coe_iff.1 (le_of_eq heq.symm) z hz
      have hnc : ¬∃ c : ℝ, ∀ z ∈ C, B z y = c :=
        fun h => hy ((neg_supportFn_neg_eq_iff (B := B) ⟨x, hxC⟩ y).2 h)
      obtain ⟨z, hz, hzne⟩ : ∃ z ∈ C, B z y ≠ B x y := by
        by_contra hcon
        push Not at hcon
        exact hnc ⟨B x y, hcon⟩
      exact (notMem_relint_iff_exists_isMaxOn hC hxC).2
        ⟨evalCLM B y, hmax, z, hz, by simpa using hzne⟩ hx
  · rintro ⟨hle, hlt⟩
    have hxcl : x ∈ closure C := by
      have h := (mem_closure_convexHull_iff_le_supportFn (B := B) C x).2 hle
      rwa [hC.convexHull_eq] at h
    have hne : C.Nonempty := closure_nonempty_iff.1 ⟨x, hxcl⟩
    rw [← Convex.relint_closure hC]
    by_contra hnot
    obtain ⟨g, hmax, z, hz, hzne⟩ := (notMem_relint_iff_exists_isMaxOn hC.closure hxcl).1 hnot
    obtain ⟨y, hy⟩ := exists_pairing_eq B g
    have hsupp : supportFn B C y = ((g x : ℝ) : EReal) := by
      rw [← supportFn_closure (B := B) C]
      refine le_antisymm (supportFn_le_coe_iff.2 fun w hw => ?_) ?_
      · rw [← hy w]; exact hmax w hw
      · rw [hy x]; exact le_supportFn hxcl y
    obtain ⟨c, hc⟩ : ∃ c : ℝ, ∀ w ∈ C, B w y = c := by
      refine (neg_supportFn_neg_eq_iff (B := B) hne y).1 ?_
      by_contra hcon
      have hstrict := hlt y hcon
      rw [hsupp, ← hy x] at hstrict
      exact absurd hstrict (lt_irrefl _)
    have hclc : closure C ⊆ {w : E | B w y = c} :=
      closure_minimal (fun w hw => hc w hw)
        (isClosed_eq (continuous_pairing B y) continuous_const)
    have hz' : B z y = c := hclc hz
    have hx' : B x y = c := hclc hxcl
    exact hzne (by rw [hy z, hy x, hz', hx'])

/-- **The interior from the support function.** Let $E$ be a finite-dimensional normed space, and
let the pairing be compatible with its topology. Let the pairing separate the points of $F$: if
$\langle x, y \rangle = 0$ for every $x$, then $y = 0$. Let $C \subseteq E$ be nonempty and
convex, and $x \in E$. Then
$$x \in \operatorname{int} C \iff \langle x, y \rangle < \delta^*(y \mid C) \text{ for every } y
  \in F \text{ with } y \neq 0.$$
This is the description of the interior in Theorem 13.1 of [rockafellar1970convex].

The relative interior is the interior exactly when $0$ is the only reversible direction, and
strictness in every nonzero direction asks for both conditions at once. The hypotheses on the
pairing and on nonemptiness are not in the classical statement; the module documentation
explains why they are needed. -/
theorem mem_interior_iff_lt_supportFn (hC : Convex ℝ C) (hne : C.Nonempty)
    (hB : B.SeparatingRight) (x : E) :
    x ∈ interior C ↔ ∀ y : F, y ≠ 0 → ((B x y : ℝ) : EReal) < supportFn B C y := by
  constructor
  · intro hx
    have htop : affineSpan ℝ C = ⊤ := hC.interior_nonempty_iff_affineSpan_eq_top.1 ⟨x, hx⟩
    have hri : x ∈ ri C := by rwa [intrinsicInterior_eq_interior htop]
    intro y hy
    refine ((mem_relint_iff_lt_supportFn (B := B) hC x).1 hri).2 y ?_
    intro hrev
    obtain ⟨c, hc⟩ := (neg_supportFn_neg_eq_iff (B := B) hne y).1 hrev
    have hmem : ∀ w : E, w ∈ affineSpan ℝ C := by
      intro w
      rw [htop]
      exact AffineSubspace.mem_top ℝ E w
    have hEqOn : Set.EqOn (B.flip y).toAffineMap (AffineMap.const ℝ E c) C := fun w hw => hc w hw
    have hall : ∀ w : E, B w y = c := fun w => by
      simpa using AffineMap.eqOn_affineSpan hEqOn (hmem w)
    have hc0 : c = 0 := by simpa using (hall 0).symm
    exact hy (hB y fun z => by rw [hall z, hc0])
  · intro h
    have htop : affineSpan ℝ C = ⊤ := by
      by_contra hcon
      obtain ⟨p, hp⟩ : ∃ p : E, p ∉ affineSpan ℝ C := by
        by_contra hall
        push Not at hall
        exact hcon (eq_top_iff.2 fun q _ => hall q)
      obtain ⟨y, c, hc, hpc⟩ := exists_forall_eq_of_notMem_affineSpan (B := B) hne hp
      obtain ⟨w, hw⟩ := hne
      have hy0 : y ≠ 0 := by
        rintro rfl
        have hc0 : c = 0 := by simpa using (hc w hw).symm
        exact hpc (by simp [hc0])
      have h₁ : B x y < c := by
        have hlt := h y hy0
        rw [supportFn_eq_coe_of_forall_eq (B := B) ⟨w, hw⟩ hc] at hlt
        exact_mod_cast hlt
      have h₂ : B x (-y) < -c := by
        have hlt := h (-y) (neg_ne_zero.2 hy0)
        rw [supportFn_eq_coe_of_forall_eq (B := B) ⟨w, hw⟩
          fun z hz => by rw [map_neg, hc z hz]] at hlt
        exact_mod_cast hlt
      rw [map_neg] at h₂
      linarith
    rw [← intrinsicInterior_eq_interior htop, mem_relint_iff_lt_supportFn (B := B) hC x]
    refine ⟨fun y => ?_, fun y hrev => ?_⟩
    · by_cases hy : y = 0
      · subst hy
        simp [supportFn_zero hne]
      · exact (h y hy).le
    · refine h y fun hy => ?_
      subst hy
      exact hrev (by simp [supportFn_zero hne])

/-- **The affine hull from the support function.** Let $E$ be a finite-dimensional normed space, and
let the pairing be compatible with its topology. Let $C \subseteq E$ be nonempty and $x \in E$.
Then $x \in \operatorname{aff} C$ if and only if
$$\langle x, y \rangle = \delta^*(y \mid C) \quad\text{for every } y \in F \text{ with }
  -\delta^*(-y \mid C) = \delta^*(y \mid C).$$

Convexity of $C$ is not needed. -/
theorem mem_affineSpan_iff_eq_supportFn (hne : C.Nonempty) (x : E) :
    x ∈ affineSpan ℝ C ↔ ∀ y : F, -supportFn B C (-y) = supportFn B C y →
      ((B x y : ℝ) : EReal) = supportFn B C y := by
  constructor
  · intro hx y hrev
    obtain ⟨c, hc⟩ := (neg_supportFn_neg_eq_iff (B := B) hne y).1 hrev
    have hEqOn : Set.EqOn (B.flip y).toAffineMap (AffineMap.const ℝ E c) C := fun w hw => hc w hw
    have hxc : B x y = c := by simpa using AffineMap.eqOn_affineSpan hEqOn hx
    rw [hxc, supportFn_eq_coe_of_forall_eq (B := B) hne hc]
  · intro h
    by_contra hx
    obtain ⟨y, c, hc, hxc⟩ := exists_forall_eq_of_notMem_affineSpan (B := B) hne hx
    have hsupp : supportFn B C y = ((c : ℝ) : EReal) :=
      supportFn_eq_coe_of_forall_eq (B := B) hne hc
    have hrev : -supportFn B C (-y) = supportFn B C y :=
      (neg_supportFn_neg_eq_iff (B := B) hne y).2 ⟨c, hc⟩
    have heq := h y hrev
    rw [hsupp] at heq
    exact hxc (by exact_mod_cast heq)

/-! ### Boundedness in the norm -/

/-- **Boundedness in the norm.** Let $E$ be a finite-dimensional normed space, and let the pairing
be compatible with its topology. A set $C \subseteq E$ is bounded in the norm if and only if for
every $y \in F$ the functional $\langle \cdot, y \rangle$ is bounded above on $C$, that is, if
and only if $\delta^*(\cdot \mid C) < +\infty$ everywhere.

`ConvexAnalysis.exists_supportFn_finite_iff` uses boundedness in the sense of the pairing and
holds in every locally convex space. The step that needs finite dimension is the passage to
`Bornology.IsBounded`, a coordinate estimate against a finite basis. -/
theorem isBounded_iff_forall_bddAbove :
    Bornology.IsBounded C ↔ ∀ y : F, ∃ c : ℝ, ∀ x ∈ C, B x y ≤ c := by
  constructor
  · intro hb y
    obtain ⟨r, hr⟩ := isBounded_iff_forall_norm_le.1 hb
    set φ : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (B.flip y)
    refine ⟨‖φ‖ * r, fun x hx => ?_⟩
    calc (B x y : ℝ) = φ x := rfl
      _ ≤ ‖φ x‖ := Real.le_norm_self _
      _ ≤ ‖φ‖ * ‖x‖ := φ.le_opNorm x
      _ ≤ ‖φ‖ * r := by
          exact mul_le_mul_of_nonneg_left (hr x hx) (norm_nonneg φ)
  · intro h
    rw [isBounded_iff_forall_norm_le]
    set b := Module.finBasis ℝ E
    have hco : ∀ i, ∃ y : F, ∀ x : E, b.coord i x = B x y := fun i =>
      exists_pairing_eq B ⟨b.coord i, LinearMap.continuous_of_finiteDimensional _⟩
    choose y hy using hco
    have hbd : ∀ i, ∃ c : ℝ, ∀ x ∈ C, |b.coord i x| ≤ c := by
      intro i
      obtain ⟨c₁, hc₁⟩ := h (y i)
      obtain ⟨c₂, hc₂⟩ := h (-(y i))
      refine ⟨max c₁ c₂, fun x hx => ?_⟩
      have h₁ : b.coord i x ≤ c₁ := by rw [hy i x]; exact hc₁ x hx
      have h₂ : -(b.coord i x) ≤ c₂ := by
        rw [hy i x, ← map_neg (B x) (y i)]
        exact hc₂ x hx
      rw [abs_le]
      exact ⟨by linarith [le_max_right c₁ c₂], by linarith [le_max_left c₁ c₂]⟩
    choose c hc using hbd
    refine ⟨∑ i, c i * ‖b i‖, fun x hx => ?_⟩
    calc ‖x‖ = ‖∑ i, b.repr x i • b i‖ := by rw [b.sum_repr]
      _ ≤ ∑ i, ‖b.repr x i • b i‖ := norm_sum_le _ _
      _ ≤ ∑ i, c i * ‖b i‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_smul, Real.norm_eq_abs, ← b.coord_apply]
          exact mul_le_mul_of_nonneg_right (hc i x hx) (norm_nonneg _)

end FiniteDim

end ConvexAnalysis

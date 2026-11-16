/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Dual
import Numlib.Analysis.Convex.Recession.Closedness
import Numlib.Analysis.Convex.Separation
import NumlibSurface.Rockafellar.Chapter02.Section06

/-!
# Rockafellar, Section 11: Separation theorems

This module formalizes §11 of [rockafellar1970convex]: the notions of separation of two sets by a
hyperplane, the fundamental separation construction, and supporting hyperplanes. A hyperplane is
$H = \{x \mid \langle x, b \rangle = \beta\}$ with $b \neq 0$. It separates $C_1$ and $C_2$ if $C_1$
lies in the closed half-space $\{x \mid \langle x, b \rangle \ge \beta\}$ and $C_2$ in the opposite
one; it separates them properly if moreover $C_1$ and $C_2$ are not both contained in $H$; and it
separates them strongly if, for some $\varepsilon > 0$, $C_1 + \varepsilon B$ and
$C_2 + \varepsilon B$ lie in the opposite open half-spaces, where $B$ is the closed Euclidean unit
ball. The main theorems say that two nonempty convex sets can be separated properly if and only if
their relative interiors are disjoint, and strongly if and only if
$0 \notin \operatorname{cl}(C_1 - C_2)$; that a closed convex set is the intersection of the closed
half-spaces that contain it; and that a closed convex cone is the intersection of the homogeneous
closed half-spaces that contain it. The proofs specialize `Numlib.Analysis.Convex.Separation`.

All 16 numbered results of §11 are formalized, in the vocabulary of the book.

## Main definitions

* Section 11, `Rockafellar.SeparatesRn`, `Rockafellar.SeparatesProperlyRn`,
  `Rockafellar.SeparatesStrictlyRn` and `Rockafellar.SeparatesStronglyRn`: the hyperplane
  $\{x \mid \langle x, b \rangle = \beta\}$ separates $C_1$ and $C_2$, properly, strictly, or
  strongly; each definition contains $b \neq 0$, so that the set is a hyperplane (Theorem 1.3).
* Section 11, `Rockafellar.SeparableProperly` and `Rockafellar.SeparableStrongly`: some hyperplane
  separates $C_1$ and $C_2$ properly, or strongly.
* Section 11, `Rockafellar.IsSupportingHalfSpace`: $\{x \mid \langle x, b \rangle \le \beta\}$ with
  $b \neq 0$ is a supporting half-space to $C$.

## Main results

* Theorem 11.1, `Rockafellar.theorem_11_1_ab` and `Rockafellar.theorem_11_1_c`: proper separation is
  the existence of $b$ with $\inf_{C_1} \langle \cdot, b \rangle \ge \sup_{C_2} \langle \cdot, b
  \rangle$ and $\sup_{C_1} \langle \cdot, b \rangle > \inf_{C_2} \langle \cdot, b \rangle$, and
  strong separation is the existence of $b$ with $\inf_{C_1} \langle \cdot, b \rangle > \sup_{C_2}
  \langle \cdot, b \rangle$.
* Theorem 11.2, `Rockafellar.theorem_11_2`: a nonempty relatively open convex set disjoint from a
  nonempty affine set $M$ lies in an open half-space whose boundary hyperplane contains $M$.
* Theorem 11.3, `Rockafellar.theorem_11_3`: two nonempty convex sets can be separated properly if
  and only if their relative interiors are disjoint.
* Theorem 11.4, `Rockafellar.theorem_11_4` and `Rockafellar.theorem_11_4_closure`: two nonempty
  convex sets can be separated strongly if and only if $\inf\{|x_1 - x_2| \mid x_1 \in C_1, x_2 \in
  C_2\} > 0$, that is, $0 \notin \operatorname{cl}(C_1 - C_2)$.
* Corollary 11.4.1, `Rockafellar.corollary_11_4_1`: disjoint nonempty closed convex sets with no
  common direction of recession can be separated strongly.
* Corollary 11.4.2, `Rockafellar.corollary_11_4_2`: nonempty convex sets with disjoint closures, one
  of them bounded, can be separated strongly.
* Theorem 11.5, `Rockafellar.theorem_11_5`: a closed convex set is the intersection of the closed
  half-spaces that contain it.
* Corollary 11.5.1, `Rockafellar.corollary_11_5_1`: $\operatorname{cl}(\operatorname{conv} S)$ is
  the intersection of the closed half-spaces that contain $S$.
* Corollary 11.5.2, `Rockafellar.corollary_11_5_2`: a nonempty convex set other than $\mathbb{R}^n$
  lies in a closed half-space.
* Theorem 11.6, `Rockafellar.theorem_11_6`: a nonempty convex subset $D$ of a convex set $C$ lies in
  a nontrivial supporting hyperplane to $C$ if and only if $D$ is disjoint from
  $\operatorname{ri} C$.
* Corollary 11.6.1, `Rockafellar.corollary_11_6_1`: a convex set has a nonzero normal at each of its
  boundary points.
* Corollary 11.6.2, `Rockafellar.corollary_11_6_2`: $x \in C$ is a relative boundary point of $C$ if
  and only if some linear function that is not constant on $C$ attains its maximum over $C$ at $x$.
* Theorem 11.7, `Rockafellar.theorem_11_7` and `Rockafellar.theorem_11_7'`: if one of two properly
  separable nonempty sets is a cone, a properly separating hyperplane can be taken through the
  origin.
* Corollary 11.7.1, `Rockafellar.corollary_11_7_1`: a nonempty closed convex cone is the
  intersection of the homogeneous closed half-spaces that contain it.
* Corollary 11.7.2, `Rockafellar.corollary_11_7_2`: the closure of the convex cone generated by $S$
  is the intersection of the homogeneous closed half-spaces that contain $S$.
* Corollary 11.7.3, `Rockafellar.corollary_11_7_3`: a nonempty convex cone other than $\mathbb{R}^n$
  lies in a homogeneous closed half-space.

## Implementation notes

* The book quantifies over vectors $b$, where the backbone quantifies over continuous linear
  functionals. In $\mathbb{R}^n$ these are the same quantification (`Rockafellar.exists_linFn`), and
  every statement of this module is over vectors. The vector $b$ is read as the linear function
  $\langle \cdot, b \rangle$, `Rockafellar.linFn b`, and $\langle x, b \rangle$ is
  `Rockafellar.pairing n x b`.
* Theorem 11.1 of the book puts $C_1$ in the upper half-space and $C_2$ in the lower one, while the
  backbone's `ConvexAnalysis.Separates f c s t` puts $s$ below and $t$ above. The definitions of
  this module therefore use `ConvexAnalysis.Separates (Rockafellar.linFn b) β C₂ C₁`, so that the
  inequalities in every statement are those of the book.
* `Rockafellar.separatesStronglyRn_iff` identifies the definition of strong separation of the book,
  with the ball $\varepsilon B$, with the backbone's definition by a gap between a supremum and an
  infimum, `ConvexAnalysis.SeparatesStrongly`. This is the content of Theorem 11.1(c).
* Infima and suprema of $\langle \cdot, b \rangle$ over a set are taken in `EReal`, so that no
  boundedness side conditions are needed.

## Deviations from the source

* **Corollary 11.5.2** (correction). The book assumes only $C \neq \mathbb{R}^n$; the statement also
  needs $C \neq \emptyset$, since for $n = 0$ the empty set is a convex set other than
  $\mathbb{R}^0$ and there is no $b \neq 0$. See `Rockafellar.corollary_11_5_2`.
* **Corollary 11.7.3** (correction). The book assumes only $K \neq \mathbb{R}^n$; the statement also
  needs $K \neq \emptyset$, for the same reason as in Corollary 11.5.2. See
  `Rockafellar.corollary_11_7_3`.
-/

open Set Pointwise

namespace Rockafellar

open ConvexAnalysis

variable {n : ℕ}

/-!
### Vectors as linear functions

A vector $b$ is read as the linear function $\langle \cdot, b \rangle$, which is
`Rockafellar.linFn b`. This definition and `Rockafellar.exists_linFn` are in
`NumlibSurface.Rockafellar.Common.Euclidean`, because §§13, 14 and 18 use them too.
-/

/-!
### The four notions of separation

The book defines them on page 95.
-/

/-- **Section 11** of [rockafellar1970convex], separation (page 95 of the book). Let
$b \in \mathbb{R}^n$, $\beta \in \mathbb{R}$ and $C_1, C_2 \subseteq \mathbb{R}^n$. The
hyperplane $H = \{x \mid \langle x, b \rangle = \beta\}$ **separates** $C_1$ and $C_2$ if
$b \neq 0$, $C_1$ is contained in the closed half-space
$\{x \mid \langle x, b \rangle \ge \beta\}$, and $C_2$ is contained in the opposite closed
half-space $\{x \mid \langle x, b \rangle \le \beta\}$.

The definition uses the backbone's `ConvexAnalysis.Separates`, whose two sets are in the other
order. -/
def SeparatesRn (b : Rn n) (β : ℝ) (C₁ C₂ : Set (Rn n)) : Prop :=
  b ≠ 0 ∧ Separates (linFn b) β C₂ C₁

/-- **Section 11** of [rockafellar1970convex], proper separation (page 95 of the book). The
hyperplane $H = \{x \mid \langle x, b \rangle = \beta\}$ separates $C_1$ and $C_2$ **properly**
if $b \neq 0$, $H$ separates $C_1$ and $C_2$, and $C_1$ and $C_2$ are not both contained in $H$. -/
def SeparatesProperlyRn (b : Rn n) (β : ℝ) (C₁ C₂ : Set (Rn n)) : Prop :=
  b ≠ 0 ∧ SeparatesProperly (linFn b) β C₂ C₁

/-- **Section 11** of [rockafellar1970convex], strict separation (page 95 of the book). The
hyperplane $H = \{x \mid \langle x, b \rangle = \beta\}$ separates $C_1$ and $C_2$ **strictly**
if $b \neq 0$ and $C_1$ and $C_2$ belong to opposing open half-spaces:
$$\langle x, b \rangle > \beta \text{ for every } x \in C_1, \qquad \langle x, b \rangle < \beta
  \text{ for every } x \in C_2.$$

The book defines this notion but numbers no result about it. -/
def SeparatesStrictlyRn (b : Rn n) (β : ℝ) (C₁ C₂ : Set (Rn n)) : Prop :=
  b ≠ 0 ∧ (∀ x ∈ C₂, pairing n x b < β) ∧ ∀ x ∈ C₁, β < pairing n x b

/-- **Section 11** of [rockafellar1970convex], strong separation (page 95 of the book). The
hyperplane $H = \{x \mid \langle x, b \rangle = \beta\}$ separates $C_1$ and $C_2$ **strongly**
if $b \neq 0$ and there is $\varepsilon > 0$ such that $C_1 + \varepsilon B$ is contained in the
open half-space $\{x \mid \langle x, b \rangle > \beta\}$ and $C_2 + \varepsilon B$ in the
opposite open half-space $\{x \mid \langle x, b \rangle < \beta\}$, where $B$ is the closed
Euclidean unit ball.

This is the definition of the book. `Rockafellar.separatesStronglyRn_iff` identifies it with the
backbone's definition by a gap, which is condition (c) of Theorem 11.1. -/
def SeparatesStronglyRn (b : Rn n) (β : ℝ) (C₁ C₂ : Set (Rn n)) : Prop :=
  b ≠ 0 ∧ ∃ ε > 0, (∀ x ∈ C₂ + Metric.closedBall (0 : Rn n) ε, pairing n x b < β) ∧
    ∀ x ∈ C₁ + Metric.closedBall (0 : Rn n) ε, β < pairing n x b

/-- Let $b \in \mathbb{R}^n$, $\beta \in \mathbb{R}$ and $C_1, C_2 \subseteq \mathbb{R}^n$. Then
$\{x \mid \langle x, b \rangle = \beta\}$ separates $C_1$ and $C_2$ strongly if and only if
$b \neq 0$ and
$$\sup_{x \in C_2} \langle x, b \rangle < \beta < \inf_{x \in C_1} \langle x, b \rangle,$$
with the supremum and the infimum taken in $[-\infty, +\infty]$.

The right side is `ConvexAnalysis.SeparatesStrongly (Rockafellar.linFn b) β C₂ C₁`. The proof
specializes `ConvexAnalysis.separatesStrongly_iff_exists_closedBall`. -/
theorem separatesStronglyRn_iff {b : Rn n} {β : ℝ} {C₁ C₂ : Set (Rn n)} :
    SeparatesStronglyRn b β C₁ C₂ ↔ b ≠ 0 ∧ SeparatesStrongly (linFn b) β C₂ C₁ := by
  simp only [SeparatesStronglyRn, separatesStrongly_iff_exists_closedBall, linFn_apply]

/-- **Section 11** of [rockafellar1970convex]. The sets $C_1, C_2 \subseteq \mathbb{R}^n$ **can be
separated properly** if some hyperplane separates them properly. -/
def SeparableProperly (C₁ C₂ : Set (Rn n)) : Prop :=
  ∃ (b : Rn n) (β : ℝ), SeparatesProperlyRn b β C₁ C₂

/-- **Section 11** of [rockafellar1970convex]. The sets $C_1, C_2 \subseteq \mathbb{R}^n$ **can be
separated strongly** if some hyperplane separates them strongly. -/
def SeparableStrongly (C₁ C₂ : Set (Rn n)) : Prop :=
  ∃ (b : Rn n) (β : ℝ), SeparatesStronglyRn b β C₁ C₂

/-- Let $C_1$ and $C_2$ be nonempty subsets of $\mathbb{R}^n$. Then $C_1$ and $C_2$ can be separated
properly if and only if there are a continuous linear functional $f$ and a real $c$ with
`ConvexAnalysis.SeparatesProperly f c C₁ C₂`.

The change of sides is `ConvexAnalysis.SeparatesProperly.symm`, and $f \neq 0$ is
`ConvexAnalysis.SeparatesProperly.ne_zero`. -/
theorem separableProperly_iff_exists {C₁ C₂ : Set (Rn n)} (h₁ : C₁.Nonempty) (h₂ : C₂.Nonempty) :
    SeparableProperly C₁ C₂ ↔ ∃ (f : Rn n →L[ℝ] ℝ) (c : ℝ), SeparatesProperly f c C₁ C₂ := by
  constructor
  · rintro ⟨b, β, -, hsep⟩
    exact ⟨-linFn b, -β, hsep.symm⟩
  · rintro ⟨f, c, hsep⟩
    obtain ⟨b, hb⟩ := exists_linFn (-f)
    have hb0 : b ≠ 0 := by
      intro hzero
      have hz : linFn b = 0 := linFn_eq_zero_iff.2 hzero
      rw [hb, neg_eq_zero] at hz
      exact hsep.ne_zero h₁ h₂ hz
    exact ⟨b, -c, hb0, by rw [hb]; exact hsep.symm⟩

/-- Let $C_1$ and $C_2$ be nonempty subsets of $\mathbb{R}^n$. Then $C_1$ and $C_2$ can be separated
strongly if and only if there are a continuous linear functional $f$ and a real $c$ with
`ConvexAnalysis.SeparatesStrongly f c C₁ C₂`. -/
theorem separableStrongly_iff_exists {C₁ C₂ : Set (Rn n)} (h₁ : C₁.Nonempty) (h₂ : C₂.Nonempty) :
    SeparableStrongly C₁ C₂ ↔ ∃ (f : Rn n →L[ℝ] ℝ) (c : ℝ), SeparatesStrongly f c C₁ C₂ := by
  constructor
  · rintro ⟨b, β, hsep⟩
    rw [separatesStronglyRn_iff] at hsep
    exact ⟨-linFn b, -β, hsep.2.symm⟩
  · rintro ⟨f, c, hsep⟩
    obtain ⟨b, hb⟩ := exists_linFn (-f)
    have hb0 : b ≠ 0 := by
      intro hzero
      have hz : linFn b = 0 := linFn_eq_zero_iff.2 hzero
      rw [hb, neg_eq_zero] at hz
      exact hsep.ne_zero h₁ h₂ hz
    exact ⟨b, -c, separatesStronglyRn_iff.2 ⟨hb0, by rw [hb]; exact hsep.symm⟩⟩

/-! ### Theorem 11.1 -/

/-- **Theorem 11.1** of [rockafellar1970convex], conditions (a) and (b). Let $C_1$ and $C_2$ be
nonempty sets in $\mathbb{R}^n$. There exists a hyperplane separating $C_1$ and $C_2$ properly
if and only if there exists a vector $b$ such that

(a) $\inf\{\langle x, b \rangle \mid x \in C_1\} \ge \sup\{\langle x, b \rangle \mid x \in
C_2\}$, and

(b) $\sup\{\langle x, b \rangle \mid x \in C_1\} > \inf\{\langle x, b \rangle \mid x \in C_2\}$.

The infima and suprema are taken in $[-\infty, +\infty]$, which removes the boundedness side
conditions that the book leaves implicit. -/
theorem theorem_11_1_ab {C₁ C₂ : Set (Rn n)} (h₁ : C₁.Nonempty) (h₂ : C₂.Nonempty) :
    SeparableProperly C₁ C₂ ↔ ∃ b : Rn n,
      (⨆ x ∈ C₂, ((pairing n x b : ℝ) : EReal)) ≤ ⨅ x ∈ C₁, ((pairing n x b : ℝ) : EReal) ∧
        (⨅ x ∈ C₂, ((pairing n x b : ℝ) : EReal)) < ⨆ x ∈ C₁, ((pairing n x b : ℝ) : EReal) := by
  constructor
  · rintro ⟨b, β, -, hsep⟩
    exact ⟨b, by
      simpa only [linFn_apply] using (exists_separatesProperly_iff_iSup_le_iInf h₂ h₁).1 ⟨β, hsep⟩⟩
  · rintro ⟨b, hb⟩
    obtain ⟨β, hβ⟩ := (exists_separatesProperly_iff_iSup_le_iInf (f := linFn b) h₂ h₁).2
      (by simpa only [linFn_apply] using hb)
    exact ⟨b, β, linFn_eq_zero_iff.not.1 (hβ.ne_zero h₂ h₁), hβ⟩

/-- **Theorem 11.1** of [rockafellar1970convex], condition (c). Let $C_1$ and $C_2$ be nonempty sets
in $\mathbb{R}^n$. There exists a hyperplane separating $C_1$ and $C_2$ strongly if and only if
there exists a vector $b$ such that

(c) $\inf\{\langle x, b \rangle \mid x \in C_1\} > \sup\{\langle x, b \rangle \mid x \in C_2\}$.

The infimum and the supremum are taken in $[-\infty, +\infty]$. The passage from the definition
with $\varepsilon B$ to this gap is `Rockafellar.separatesStronglyRn_iff`, which is the content
of the proof of the book. -/
theorem theorem_11_1_c {C₁ C₂ : Set (Rn n)} (h₁ : C₁.Nonempty) (h₂ : C₂.Nonempty) :
    SeparableStrongly C₁ C₂ ↔ ∃ b : Rn n,
      (⨆ x ∈ C₂, ((pairing n x b : ℝ) : EReal)) < ⨅ x ∈ C₁, ((pairing n x b : ℝ) : EReal) := by
  constructor
  · rintro ⟨b, β, hsep⟩
    rw [separatesStronglyRn_iff] at hsep
    exact ⟨b, by
      simpa only [linFn_apply] using exists_separatesStrongly_iff_iSup_lt_iInf.1 ⟨β, hsep.2⟩⟩
  · rintro ⟨b, hb⟩
    obtain ⟨β, hβ⟩ := (exists_separatesStrongly_iff_iSup_lt_iInf (f := linFn b) (s := C₂)
      (t := C₁)).2 (by simpa only [linFn_apply] using hb)
    exact ⟨b, β, separatesStronglyRn_iff.2 ⟨linFn_eq_zero_iff.not.1 (hβ.ne_zero h₂ h₁), hβ⟩⟩

/-! ### Theorem 11.2, the fundamental construction -/

/-- **Theorem 11.2** of [rockafellar1970convex]. Let $C$ be a nonempty relatively open convex set in
$\mathbb{R}^n$, and let $M$ be a nonempty affine set in $\mathbb{R}^n$ not meeting $C$. Then
there exists a hyperplane $H$ containing $M$ such that one of the open half-spaces associated
with $H$ contains $C$: there are $b \neq 0$ and $\beta$ with $\langle x, b \rangle = \beta$ for
every $x \in M$ and $\langle x, b \rangle < \beta$ for every $x \in C$.

The backbone has the case of an open $C$ and the case of a single point $M$; this statement is
for relatively open $C$ and a general affine set $M$. Relatively open is
`Rockafellar.IsRelativelyOpen`, and affine is `Rockafellar.IsAffineSet`. -/
theorem theorem_11_2 {C M : Set (Rn n)} (hC : Convex ℝ C) (hCne : C.Nonempty)
    (hCo : IsRelativelyOpen C) (hM : IsAffineSet M) (hMne : M.Nonempty)
    (hdisj : Disjoint C M) :
    ∃ (b : Rn n) (β : ℝ), b ≠ 0 ∧ (∀ x ∈ M, pairing n x b = β) ∧ ∀ x ∈ C, pairing n x b < β := by
  obtain ⟨p, hp⟩ := hMne
  obtain ⟨c₀, hc₀⟩ := hCne
  set A := hM.toAffineSubspace with hA
  set W := A.direction with hW
  have hpA : p ∈ A := hp
  set D : Set (Rn n) := C + (W : Set (Rn n)) with hD
  have hCD : C ⊆ D := fun x hx => Set.mem_add.2 ⟨x, hx, 0, W.zero_mem, add_zero x⟩
  have hDconv : Convex ℝ D := hC.add W.convex
  have hpD : p ∉ D := by
    intro hmem
    obtain ⟨c, hc, w, hw, hcw⟩ := Set.mem_add.1 hmem
    have hcM : c ∈ M := by
      have hmem' : (-w) +ᵥ p ∈ A := AffineSubspace.vadd_mem_of_mem_direction (W.neg_mem hw) hpA
      have hce : (-w) +ᵥ p = c := by rw [vadd_eq_add, ← hcw]; abel
      rwa [hce] at hmem'
    exact Set.disjoint_left.1 hdisj hc hcM
  obtain ⟨g, hgle, x₁, hx₁, hglt⟩ :=
    exists_lt_of_notMem_relint hDconv ⟨c₀, hCD hc₀⟩ fun hmem => hpD (intrinsicInterior_subset hmem)
  have hgW : ∀ w ∈ W, g w = 0 := by
    intro w hw
    have hsub : ∀ y ∈ AffineSubspace.mk' c₀ W, -(g p) ≤ (-g) y := by
      intro y hy
      have hyW : y -ᵥ c₀ ∈ W := by
        simpa [AffineSubspace.direction_mk'] using
          AffineSubspace.vsub_mem_direction hy (AffineSubspace.self_mem_mk' c₀ W)
      have hyD : y ∈ D := Set.mem_add.2 ⟨c₀, hc₀, y - c₀, by simpa using hyW, by abel⟩
      simpa using neg_le_neg (hgle y hyD)
    have hw' : w +ᵥ c₀ ∈ AffineSubspace.mk' c₀ W :=
      AffineSubspace.vadd_mem_of_mem_direction
        (by simpa [AffineSubspace.direction_mk'] using hw) (AffineSubspace.self_mem_mk' c₀ W)
    have heq := eq_of_le_on_affineSubspace (f := -g) hsub hw' (AffineSubspace.self_mem_mk' c₀ W)
    simp only [neg_apply, vadd_eq_add, map_add] at heq
    linarith
  have hgC : ∀ x ∈ C, g x ≤ g p := fun x hx => hgle x (hCD hx)
  obtain ⟨c₁, hc₁, hc₁lt⟩ : ∃ c ∈ C, g c < g p := by
    obtain ⟨c, hc, w, hw, hcw⟩ := Set.mem_add.1 hx₁
    refine ⟨c, hc, ?_⟩
    have hsum : g c + g w = g x₁ := by rw [← map_add, hcw]
    rw [hgW w hw, add_zero] at hsum
    rw [hsum]
    exact hglt
  have hgstrict : ∀ x ∈ C, g x < g p := by
    intro x hx
    rcases lt_or_eq_of_le (hgC x hx) with h | h
    · exact h
    · exfalso
      have hnot : x ∉ ri C := (notMem_relint_iff_exists_isMaxOn hC hx).2
        ⟨g, fun y hy => by rw [h]; exact hgC y hy, c₁, hc₁, by rw [h]; exact hc₁lt.ne⟩
      rw [hCo] at hnot
      exact hnot hx
  obtain ⟨b, hb⟩ := exists_linFn g
  refine ⟨b, g p, ?_, ?_, ?_⟩
  · intro hb0
    subst hb0
    have hg0 : g = 0 := by rw [← hb]; exact linFn_eq_zero_iff.2 rfl
    rw [hg0] at hc₁lt
    simp at hc₁lt
  · intro x hx
    have hxW : x -ᵥ p ∈ W := AffineSubspace.vsub_mem_direction hx hpA
    have hgx : g (x - p) = 0 := hgW _ (by simpa using hxW)
    rw [map_sub, sub_eq_zero] at hgx
    rw [← linFn_apply b x, hb]
    exact hgx
  · intro x hx
    rw [← linFn_apply b x, hb]
    exact hgstrict x hx

/-! ### Theorem 11.3, the main separation theorem -/

/-- **Theorem 11.3** of [rockafellar1970convex]. Let $C_1$ and $C_2$ be nonempty convex sets in
$\mathbb{R}^n$. In order that there exist a hyperplane separating $C_1$ and $C_2$ properly, it
is necessary and sufficient that $\operatorname{ri} C_1$ and $\operatorname{ri} C_2$ have no
point in common. -/
theorem theorem_11_3 {C₁ C₂ : Set (Rn n)} (h₁ : Convex ℝ C₁) (h₂ : Convex ℝ C₂)
    (hne₁ : C₁.Nonempty) (hne₂ : C₂.Nonempty) :
    SeparableProperly C₁ C₂ ↔ ri C₁ ∩ ri C₂ = ∅ := by
  rw [separableProperly_iff_exists hne₁ hne₂,
    exists_separatesProperly_iff_disjoint_relint h₁ h₂ hne₁ hne₂, Set.disjoint_iff_inter_eq_empty]

/-! ### Theorem 11.4 and its corollaries -/

/-- **Theorem 11.4** of [rockafellar1970convex], second form. Let $C_1$ and $C_2$ be nonempty convex
sets in $\mathbb{R}^n$. Then there exists a hyperplane separating $C_1$ and $C_2$ strongly if
and only if
$$0 \notin \operatorname{cl}(C_1 - C_2).$$
-/
theorem theorem_11_4_closure {C₁ C₂ : Set (Rn n)} (h₁ : Convex ℝ C₁) (h₂ : Convex ℝ C₂)
    (hne₁ : C₁.Nonempty) (hne₂ : C₂.Nonempty) :
    SeparableStrongly C₁ C₂ ↔ (0 : Rn n) ∉ closure (C₁ - C₂) := by
  rw [separableStrongly_iff_exists hne₁ hne₂,
    separatesStrongly_iff_zero_notMem_closure_sub h₁ h₂]

/-- **Theorem 11.4** of [rockafellar1970convex]. Let $C_1$ and $C_2$ be nonempty convex sets in
$\mathbb{R}^n$. In order that there exist a hyperplane separating $C_1$ and $C_2$ strongly, it
is necessary and sufficient that
$$\inf\{|x_1 - x_2| \mid x_1 \in C_1, x_2 \in C_2\} > 0.$$

The condition is stated as: there is $\varepsilon > 0$ with $\varepsilon \le \|x_1 - x_2\|$ for
all $x_1 \in C_1$ and $x_2 \in C_2$. `Rockafellar.theorem_11_4_closure` is the same statement in
the form $0 \notin \operatorname{cl}(C_1 - C_2)$, which is the form that the backbone proves: a
positive infimum of $|x_1 - x_2|$ is a ball around the origin that misses $C_1 - C_2$. -/
theorem theorem_11_4 {C₁ C₂ : Set (Rn n)} (h₁ : Convex ℝ C₁) (h₂ : Convex ℝ C₂)
    (hne₁ : C₁.Nonempty) (hne₂ : C₂.Nonempty) :
    SeparableStrongly C₁ C₂ ↔ ∃ ε > 0, ∀ x₁ ∈ C₁, ∀ x₂ ∈ C₂, ε ≤ ‖x₁ - x₂‖ := by
  rw [theorem_11_4_closure h₁ h₂ hne₁ hne₂]
  constructor
  · intro h
    rw [Metric.mem_closure_iff] at h
    push Not at h
    obtain ⟨ε, hε, hball⟩ := h
    refine ⟨ε, hε, fun x₁ hx₁ x₂ hx₂ => ?_⟩
    have hd := hball _ (Set.sub_mem_sub hx₁ hx₂)
    rwa [dist_zero_left] at hd
  · rintro ⟨ε, hε, hsep⟩ hmem
    rw [Metric.mem_closure_iff] at hmem
    obtain ⟨y, hy, hylt⟩ := hmem ε hε
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Set.mem_sub.1 hy
    rw [dist_zero_left] at hylt
    exact absurd (hsep x₁ hx₁ x₂ hx₂) (not_le.2 hylt)

/-- **Corollary 11.4.1** of [rockafellar1970convex]. Let $C_1$ and $C_2$ be nonempty disjoint closed
convex sets in $\mathbb{R}^n$ having no common directions of recession, that is,
$0^+ C_1 \cap 0^+ C_2 \subseteq \{0\}$. Then there exists a hyperplane separating $C_1$ and
$C_2$ strongly. -/
theorem corollary_11_4_1 {C₁ C₂ : Set (Rn n)} (h₁ : Convex ℝ C₁) (hc₁ : IsClosed C₁)
    (hne₁ : C₁.Nonempty) (h₂ : Convex ℝ C₂) (hc₂ : IsClosed C₂) (hne₂ : C₂.Nonempty)
    (hdisj : Disjoint C₁ C₂) (hrec : recessionCone C₁ ∩ recessionCone C₂ ⊆ {0}) :
    SeparableStrongly C₁ C₂ := by
  have hkey : ∀ z ∈ recessionCone C₁, -z ∈ recessionCone (-C₂) → z = 0 := by
    intro z hz hnz
    rw [recessionCone_neg, Set.mem_neg, neg_neg] at hnz
    exact hrec ⟨hz, hnz⟩
  have hclosed : IsClosed (C₁ + -C₂) :=
    Convex.isClosed_add_of_neg_notMem_recessionCone h₁ hc₁ hne₁ h₂.neg hc₂.neg hne₂.neg hkey
  rw [← sub_eq_add_neg] at hclosed
  rw [theorem_11_4_closure h₁ h₂ hne₁ hne₂, hclosed.closure_eq]
  intro hmem
  obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_sub.1 hmem
  rw [sub_eq_zero] at hxy
  exact Set.disjoint_left.1 hdisj hx (hxy ▸ hy)

/-- **Corollary 11.4.2** of [rockafellar1970convex]. Let $C_1$ and $C_2$ be nonempty convex sets in
$\mathbb{R}^n$ whose closures are disjoint. If either set is bounded, there exists a hyperplane
separating $C_1$ and $C_2$ strongly.

The proof uses that a closed bounded set in $\mathbb{R}^n$ is compact; the book instead deduces
the corollary from Corollary 11.4.1. -/
theorem corollary_11_4_2 {C₁ C₂ : Set (Rn n)} (h₁ : Convex ℝ C₁) (h₂ : Convex ℝ C₂)
    (hne₁ : C₁.Nonempty) (hne₂ : C₂.Nonempty) (hdisj : Disjoint (closure C₁) (closure C₂))
    (hbdd : Bornology.IsBounded C₁ ∨ Bornology.IsBounded C₂) :
    SeparableStrongly C₁ C₂ := by
  rw [separableStrongly_iff_exists hne₁ hne₂]
  obtain ⟨f, c, hsep⟩ : ∃ (f : Rn n →L[ℝ] ℝ) (c : ℝ),
      SeparatesStrongly f c (closure C₁) (closure C₂) := by
    rcases hbdd with hb | hb
    · exact separatesStrongly_of_disjoint_isCompact_isClosed h₁.closure
        (Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure)
        h₂.closure isClosed_closure hdisj
    · exact separatesStrongly_of_disjoint_isClosed_isCompact h₁.closure isClosed_closure
        h₂.closure (Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure) hdisj
  exact ⟨f, c, hsep.mono subset_closure subset_closure⟩

/-! ### Theorem 11.5 and its corollaries -/

/-- **Theorem 11.5** of [rockafellar1970convex]. A closed convex set $C$ in $\mathbb{R}^n$ is the
intersection of the closed half-spaces which contain it:
$$C = \bigcap\{\{x \mid \langle x, b \rangle \le \beta\} \mid b \in \mathbb{R}^n, \beta \in
  \mathbb{R}, \langle y, b \rangle \le \beta \text{ for all } y \in C\}.$$

The intersection runs over all vectors $b$, including $b = 0$. This is harmless:
$\{x \mid \langle x, 0 \rangle \le \beta\}$ is $\mathbb{R}^n$ when $\beta \ge 0$, which is the
only case in which it contains a nonempty $C$. -/
theorem theorem_11_5 {C : Set (Rn n)} (hC : Convex ℝ C) (hCc : IsClosed C) :
    ⋂ (b : Rn n) (β : ℝ) (_ : ∀ y ∈ C, pairing n y b ≤ β),
      {x : Rn n | pairing n x b ≤ β} = C := by
  ext x
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  rw [mem_iff_forall_le_halfSpace hC hCc]
  constructor
  · intro h f c hf
    obtain ⟨b, rfl⟩ := exists_linFn f
    simp only [linFn_apply] at hf ⊢
    exact h b c hf
  · intro h b c hb
    simpa only [linFn_apply] using h (linFn b) c (by simpa only [linFn_apply] using hb)

/-- **Corollary 11.5.1** of [rockafellar1970convex]. Let $S$ be any subset of $\mathbb{R}^n$. Then
$\operatorname{cl}(\operatorname{conv} S)$ is the intersection of all the closed half-spaces
containing $S$.

As in `Rockafellar.theorem_11_5`, the intersection runs over all vectors $b$, including $b = 0$. -/
theorem corollary_11_5_1 (S : Set (Rn n)) :
    ⋂ (b : Rn n) (β : ℝ) (_ : ∀ y ∈ S, pairing n y b ≤ β), {x : Rn n | pairing n x b ≤ β} =
      closure (convexHull ℝ S) := by
  rw [← closure_convexHull_eq_iInter_halfspaces S]
  ext x
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · intro h f c hf
    obtain ⟨b, rfl⟩ := exists_linFn f
    simp only [linFn_apply] at hf ⊢
    exact h b c hf
  · intro h b c hb
    simpa only [linFn_apply] using h (linFn b) c (by simpa only [linFn_apply] using hb)

/-- **Corollary 11.5.2** of [rockafellar1970convex]. Let $C$ be a nonempty convex subset of
$\mathbb{R}^n$ other than $\mathbb{R}^n$ itself. Then there exists a closed half-space
containing $C$; in other words, there exists some $b \in \mathbb{R}^n$, $b \neq 0$, such that
the linear function $\langle \cdot, b \rangle$ is bounded above on $C$.

**Correction.** The book assumes only that $C$ is convex and $C \neq \mathbb{R}^n$. The
statement is false for $n = 0$ and $C = \emptyset$: the empty set is a convex set other than
$\mathbb{R}^0$, and there is no $b \neq 0$ in $\mathbb{R}^0$. The hypothesis $C \neq \emptyset$
is therefore added. -/
theorem corollary_11_5_2 {C : Set (Rn n)} (hC : Convex ℝ C) (hne : C.Nonempty)
    (h : C ≠ Set.univ) : ∃ (b : Rn n) (β : ℝ), b ≠ 0 ∧ ∀ x ∈ C, pairing n x b ≤ β := by
  have hcl : closure C ≠ Set.univ := by
    intro hcl
    refine h (Set.eq_univ_of_univ_subset ?_)
    have hri : ri C = Set.univ := by rw [← Convex.relint_closure hC, hcl, intrinsicInterior_univ]
    rw [← hri]
    exact intrinsicInterior_subset
  obtain ⟨f, c, hf0, hf⟩ := exists_ne_zero_forall_le_of_closure_ne_univ hC hne hcl
  obtain ⟨b, rfl⟩ := exists_linFn f
  exact ⟨b, c, linFn_eq_zero_iff.not.1 hf0, by simpa only [linFn_apply] using hf⟩

/-! ### Theorem 11.6, supporting hyperplanes -/

/-- **Section 11** of [rockafellar1970convex], supporting half-spaces (page 99 of the book). Let
$b \in \mathbb{R}^n$, $\beta \in \mathbb{R}$ and $C \subseteq \mathbb{R}^n$. The closed
half-space $\{x \mid \langle x, b \rangle \le \beta\}$ is a **supporting half-space** to $C$ if
$b \neq 0$, it contains $C$, and it has a point of $C$ in its boundary:
$\langle x, b \rangle = \beta$ for some $x \in C$. The boundary
$\{x \mid \langle x, b \rangle = \beta\}$ is then a **supporting hyperplane** to $C$. -/
def IsSupportingHalfSpace (b : Rn n) (β : ℝ) (C : Set (Rn n)) : Prop :=
  b ≠ 0 ∧ (∀ x ∈ C, pairing n x b ≤ β) ∧ ∃ x ∈ C, pairing n x b = β

/-- Let $b \in \mathbb{R}^n$, $\beta \in \mathbb{R}$ and $C \subseteq \mathbb{R}^n$. Then
$\{x \mid \langle x, b \rangle \le \beta\}$ is a supporting half-space to $C$ if and only if
`ConvexAnalysis.IsSupporting (Rockafellar.linFn b) β C` holds for the linear function
$\langle \cdot, b \rangle$. -/
theorem isSupportingHalfSpace_iff {b : Rn n} {β : ℝ} {C : Set (Rn n)} :
    IsSupportingHalfSpace b β C ↔ IsSupporting (linFn b) β C := by
  constructor
  · rintro ⟨hb, hle, hex⟩
    exact ⟨linFn_eq_zero_iff.not.2 hb, fun x hx => by simpa only [linFn_apply] using hle x hx,
      by simpa only [linFn_apply] using hex⟩
  · rintro ⟨hb, hle, hex⟩
    exact ⟨linFn_eq_zero_iff.not.1 hb, fun x hx => by simpa only [linFn_apply] using hle hx,
      by simpa only [linFn_apply] using hex⟩

/-- **Theorem 11.6** of [rockafellar1970convex]. Let $C$ be a convex set in $\mathbb{R}^n$, and let
$D$ be a nonempty convex subset of $C$. In order that there exist a nontrivial supporting
hyperplane to $C$ containing $D$, it is necessary and sufficient that $D$ be disjoint from
$\operatorname{ri} C$.

A supporting hyperplane $\{x \mid \langle x, b \rangle = \beta\}$ is nontrivial if it does not
contain $C$: $\langle x, b \rangle \neq \beta$ for some $x \in C$. The backbone has the version
with the interior; this statement uses $\operatorname{ri} C$. A nontrivial supporting hyperplane
to $C$ through $D$ is the same as a proper separation of $D$ and $C$. -/
theorem theorem_11_6 {C D : Set (Rn n)} (hC : Convex ℝ C) (hD : Convex ℝ D) (hDC : D ⊆ C)
    (hDne : D.Nonempty) :
    (∃ (b : Rn n) (β : ℝ), IsSupportingHalfSpace b β C ∧ (∀ x ∈ D, pairing n x b = β) ∧
      ∃ x ∈ C, pairing n x b ≠ β) ↔ D ∩ ri C = ∅ := by
  obtain ⟨d₀, hd₀⟩ := hDne
  constructor
  · rintro ⟨b, β, ⟨-, hle, -⟩, hDβ, y, hy, hyne⟩
    refine Set.eq_empty_of_forall_notMem fun x hx => ?_
    have hxC : x ∈ C := hDC hx.1
    refine (notMem_relint_iff_exists_isMaxOn hC hxC).2 ⟨linFn b, fun z hz => ?_, y, hy, ?_⟩ hx.2
    · simp only [linFn_apply, hDβ x hx.1]
      exact hle z hz
    · simpa only [linFn_apply, hDβ x hx.1] using hyne
  · intro hdisj
    have hri : ri D ∩ ri C = ∅ :=
      Set.eq_empty_of_forall_notMem fun x hx =>
        Set.eq_empty_iff_forall_notMem.1 hdisj x ⟨intrinsicInterior_subset hx.1, hx.2⟩
    obtain ⟨b, β, hb, hsep⟩ := (theorem_11_3 hD hC ⟨d₀, hd₀⟩ ⟨d₀, hDC hd₀⟩).2 hri
    have hCle : ∀ x ∈ C, pairing n x b ≤ β := fun x hx => by
      simpa only [linFn_apply] using hsep.le_of_mem_left hx
    have hDeq : ∀ x ∈ D, pairing n x b = β := fun x hx =>
      le_antisymm (hCle x (hDC hx)) (by simpa only [linFn_apply] using hsep.le_of_mem_right hx)
    obtain ⟨y, hy, hyne⟩ : ∃ y ∈ C, pairing n y b ≠ β := by
      by_contra hcon
      push Not at hcon
      refine hsep.not_subset fun z hz => ?_
      rcases hz with hz | hz
      · simpa only [Set.mem_ofPred_eq, linFn_apply] using hcon z hz
      · simpa only [Set.mem_ofPred_eq, linFn_apply] using hDeq z hz
    exact ⟨b, β, ⟨hb, hCle, d₀, hDC hd₀, hDeq d₀ hd₀⟩, hDeq, y, hy, hyne⟩

/-- **Corollary 11.6.1** of [rockafellar1970convex]. A convex set has a nonzero normal at each of
its boundary points: if $C \subseteq \mathbb{R}^n$ is convex and $x \in C$ is a boundary point
of $C$, then there is $b \neq 0$ with $\langle z - x, b \rangle \le 0$ for every $z \in C$.

The normals to $C$ at $x$ form `ConvexAnalysis.normalCone (Rockafellar.pairing n) C x`. The
proof specializes `ConvexAnalysis.exists_ne_zero_isMaxOn_of_mem_frontier`. -/
theorem corollary_11_6_1 {C : Set (Rn n)} (hC : Convex ℝ C) {x : Rn n} (hx : x ∈ C)
    (hfr : x ∈ frontier C) : ∃ b ∈ normalCone (pairing n) C x, b ≠ 0 := by
  obtain ⟨g, hg0, hg⟩ := exists_ne_zero_isMaxOn_of_mem_frontier hC hx hfr
  obtain ⟨b, rfl⟩ := exists_linFn g
  refine ⟨b, fun z hz => ?_, linFn_eq_zero_iff.not.1 hg0⟩
  have hzx := hg z hz
  simp only [linFn_apply] at hzx
  simp only [map_sub, LinearMap.sub_apply, sub_nonpos]
  exact hzx

/-- **Corollary 11.6.2** of [rockafellar1970convex]. Let $C$ be a convex set in $\mathbb{R}^n$, and
let $x \in C$. Then $x$ is a relative boundary point of $C$ if and only if there exists a linear
function $h$ not constant on $C$ such that $h$ achieves its maximum over $C$ at $x$.

The linear function $h$ is $\langle \cdot, b \rangle$ for a vector $b$. The relative boundary is
`Rockafellar.relbd` of §6. -/
theorem corollary_11_6_2 {C : Set (Rn n)} (hC : Convex ℝ C) {x : Rn n} (hx : x ∈ C) :
    x ∈ relbd C ↔ ∃ b : Rn n, (∀ y ∈ C, pairing n y b ≤ pairing n x b) ∧
      ∃ y ∈ C, pairing n y b ≠ pairing n x b := by
  rw [mem_relbd_iff, notMem_relint_iff_exists_isMaxOn hC hx]
  simp only [subset_closure hx, true_and]
  constructor
  · rintro ⟨g, hle, y, hy, hne⟩
    obtain ⟨b, rfl⟩ := exists_linFn g
    exact ⟨b, by simpa only [linFn_apply] using hle, y, hy, by simpa only [linFn_apply] using hne⟩
  · rintro ⟨b, hle, y, hy, hne⟩
    exact ⟨linFn b, by simpa only [linFn_apply] using hle, y, hy,
      by simpa only [linFn_apply] using hne⟩

/-! ### Theorem 11.7, cones and homogeneous half-spaces -/

/-- **Theorem 11.7** of [rockafellar1970convex]. Let $C_1$ and $C_2$ be nonempty subsets of
$\mathbb{R}^n$, and let $C_2$ be a cone. If there exists a hyperplane which separates $C_1$ and
$C_2$ properly, then there exists a hyperplane which separates $C_1$ and $C_2$ properly and
passes through the origin.

The book lets either set be the cone. This declaration has the cone on the side of $C_2$, and
`Rockafellar.theorem_11_7'` has it on the side of $C_1$. The conclusion
`Rockafellar.SeparatesProperlyRn b 0 C₁ C₂` says that the hyperplane
$\{x \mid \langle x, b \rangle = 0\}$ separates properly; it contains the origin. A cone is
`Rockafellar.IsCone`. -/
theorem theorem_11_7 {C₁ C₂ : Set (Rn n)} (hne₁ : C₁.Nonempty) (hne₂ : C₂.Nonempty)
    (hcone : IsCone C₂) (h : SeparableProperly C₁ C₂) :
    ∃ b : Rn n, SeparatesProperlyRn b 0 C₁ C₂ := by
  obtain ⟨b, β, hb, hsep⟩ := h
  exact ⟨b, hb, hsep.zero_of_isCone_left (fun _ ha _ hx => hcone _ ha _ hx) hne₂ hne₁⟩

/-- **Theorem 11.7** of [rockafellar1970convex], with the cone on the other side. Let $C_1$ and
$C_2$ be nonempty subsets of $\mathbb{R}^n$, and let $C_1$ be a cone. If there exists a
hyperplane which separates $C_1$ and $C_2$ properly, then there exists a hyperplane which
separates $C_1$ and $C_2$ properly and passes through the origin. -/
theorem theorem_11_7' {C₁ C₂ : Set (Rn n)} (hne₁ : C₁.Nonempty) (hne₂ : C₂.Nonempty)
    (hcone : IsCone C₁) (h : SeparableProperly C₁ C₂) :
    ∃ b : Rn n, SeparatesProperlyRn b 0 C₁ C₂ := by
  obtain ⟨b, β, hb, hsep⟩ := h
  exact ⟨b, hb, hsep.zero_of_isCone_right (fun _ ha _ hx => hcone _ ha _ hx) hne₂ hne₁⟩

/-- **Corollary 11.7.1** of [rockafellar1970convex]. A nonempty closed convex cone $K$ in
$\mathbb{R}^n$ is the intersection of the homogeneous closed half-spaces which contain it, a
homogeneous half-space being one with the origin on its boundary:
$$K = \bigcap\{\{x \mid \langle x, b \rangle \le 0\} \mid b \in \mathbb{R}^n, \langle y, b
  \rangle \le 0 \text{ for all } y \in K\}.$$
-/
theorem corollary_11_7_1 {K : Set (Rn n)} (hconv : Convex ℝ K) (hcone : IsCone K)
    (hcl : IsClosed K) (hne : K.Nonempty) :
    ⋂ (b : Rn n) (_ : ∀ y ∈ K, pairing n y b ≤ 0), {x : Rn n | pairing n x b ≤ 0} = K := by
  refine Eq.trans ?_ (isClosed_convex_isCone_eq_iInter_halfSpaceCone hconv
    (fun _ ha _ hx => hcone _ ha _ hx) hcl hne)
  ext x
  simp only [Set.mem_iInter, coe_halfSpaceCone, Set.mem_ofPred_eq]
  constructor
  · intro h f hf
    obtain ⟨b, rfl⟩ := exists_linFn f
    simp only [linFn_apply] at hf ⊢
    exact h b hf
  · intro h b hb
    simpa only [linFn_apply] using h (linFn b) (by simpa only [linFn_apply] using hb)

/-- **Corollary 11.7.2** of [rockafellar1970convex]. Let $S$ be any subset of $\mathbb{R}^n$, and
let $K$ be the closure of the convex cone generated by $S$. Then $K$ is the intersection of all
the homogeneous closed half-spaces containing $S$.

The cone generated by $S$ is `PointedCone.hull ℝ S`, which contains the origin. The proof of the
book needs this, so no generality is lost. -/
theorem corollary_11_7_2 (S : Set (Rn n)) :
    ⋂ (b : Rn n) (_ : ∀ y ∈ S, pairing n y b ≤ 0), {x : Rn n | pairing n x b ≤ 0} =
      closure (PointedCone.hull ℝ S : Set (Rn n)) := by
  rw [← closure_hull_eq_iInter_halfSpaceCone S]
  ext x
  simp only [Set.mem_iInter, coe_halfSpaceCone, Set.mem_ofPred_eq]
  constructor
  · intro h f hf
    obtain ⟨b, rfl⟩ := exists_linFn f
    simp only [linFn_apply] at hf ⊢
    exact h b hf
  · intro h b hb
    simpa only [linFn_apply] using h (linFn b) (by simpa only [linFn_apply] using hb)

/-- **Corollary 11.7.3** of [rockafellar1970convex]. Let $K$ be a nonempty convex cone in
$\mathbb{R}^n$ other than $\mathbb{R}^n$ itself. Then $K$ is contained in some homogeneous
closed half-space of $\mathbb{R}^n$; in other words, there exists some vector $b \neq 0$ such
that $\langle x, b \rangle \le 0$ for every $x \in K$.

**Correction.** The book assumes only that $K$ is a convex cone and $K \neq \mathbb{R}^n$. As in
Corollary 11.5.2, the statement is false for $n = 0$ and $K = \emptyset$, so the hypothesis
$K \neq \emptyset$ is added. -/
theorem corollary_11_7_3 {K : Set (Rn n)} (hconv : Convex ℝ K) (hcone : IsCone K)
    (hne : K.Nonempty) (h : K ≠ Set.univ) :
    ∃ b : Rn n, b ≠ 0 ∧ ∀ x ∈ K, pairing n x b ≤ 0 := by
  have hcl : closure K ≠ Set.univ := by
    intro hcl
    refine h (Set.eq_univ_of_univ_subset ?_)
    have hri : ri K = Set.univ := by
      rw [← Convex.relint_closure hconv, hcl, intrinsicInterior_univ]
    rw [← hri]
    exact intrinsicInterior_subset
  obtain ⟨f, hf0, hf⟩ := exists_ne_zero_forall_le_zero_of_closure_ne_univ hconv
    (fun _ ha _ hx => hcone _ ha _ hx) hne hcl
  obtain ⟨b, rfl⟩ := exists_linFn f
  exact ⟨b, linFn_eq_zero_iff.not.1 hf0, by simpa only [linFn_apply] using hf⟩

end Rockafellar

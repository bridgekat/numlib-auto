/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import NumlibSurface.Rockafellar.Common.Euclidean

/-!
# Rockafellar, Section 1: Affine sets

This module formalizes Section 1 of [rockafellar1970convex]. A set $M \subseteq \mathbb{R}^n$ is
affine if $(1 - \lambda) x + \lambda y \in M$ for all $x, y \in M$ and all $\lambda \in \mathbb{R}$.
The section shows that the subspaces are the affine sets that contain the origin, that a non-empty
affine set is a translate $L + a$ of a unique subspace $L$, and it defines the dimension of an
affine set as the dimension of $L$, with $\dim \emptyset = -1$. It then describes hyperplanes as the
level sets $\{x \mid \langle x, b \rangle = \beta\}$ with $b \neq 0$, describes affine sets as the
solution sets of systems of linear equations $Bx = b$, and describes affine transformations as the
maps $x \mapsto Ax + a$ with $A$ linear.

All 8 numbered results of Section 1 are formalized. The content is linear algebra, so the proofs use
the affine-space and inner-product API of Mathlib and almost nothing from the backbone.

## Main definitions

* Definition of affine set, `Rockafellar.IsAffineSet`: $(1 - \lambda) x + \lambda y \in M$ for all
  $x, y \in M$ and $\lambda \in \mathbb{R}$.
* Definition of dimension, `Rockafellar.dim`: the dimension of the subspace parallel to the affine
  hull, with $\dim \emptyset = -1$.
* Definition of hyperplane, `Rockafellar.IsHyperplane`: an affine set of dimension $n - 1$.
* Definition of affine transformation, `Rockafellar.IsAffineMap`: a map $T$ with $T((1 - \lambda)
  x + \lambda y) = (1 - \lambda) Tx + \lambda Ty$.

## Main results

* Theorem 1.1, `Rockafellar.theorem_1_1`: the subspaces of $\mathbb{R}^n$ are the affine sets that
  contain the origin.
* Theorem 1.2, `Rockafellar.theorem_1_2`, `Rockafellar.theorem_1_2_sub`: a non-empty affine set $M$
  is parallel to a unique subspace $L$, and $L = M - M$.
* Theorem 1.3, `Rockafellar.theorem_1_3`, `Rockafellar.theorem_1_3_exists`,
  `Rockafellar.theorem_1_3_unique`: the hyperplanes are the sets
  $\{x \mid \langle x, b \rangle = \beta\}$ with $b \neq 0$, and $(b, \beta)$ is unique up to a
  common non-zero multiple.
* Theorem 1.4, `Rockafellar.theorem_1_4`, `Rockafellar.theorem_1_4_exists`: the affine sets are the
  solution sets $\{x \mid Bx = b\}$ of systems of linear equations.
* Corollary 1.4.1, `Rockafellar.corollary_1_4_1`: every affine set is the intersection of finitely
  many hyperplanes.
* Theorem 1.5, `Rockafellar.theorem_1_5`: the affine transformations $\mathbb{R}^n \to \mathbb{R}^m$
  are the maps $x \mapsto Ax + a$ with $A$ linear.
* Theorem 1.6, `Rockafellar.theorem_1_6`, `Rockafellar.theorem_1_6_unique`: two affinely independent
  sets of $m + 1$ points are carried onto each other by a bijective affine transformation of
  $\mathbb{R}^n$, uniquely when $m = n$.
* Corollary 1.6.1, `Rockafellar.corollary_1_6_1`: two affine sets of the same dimension are carried
  onto each other by a bijective affine transformation of $\mathbb{R}^n$.
* Unnumbered result, `Rockafellar.orthogonal_graph_eq_graph_neg_adjoint`: the orthogonal complement
  of the graph of a linear map $A$ is the graph of $-A^*$. Section 22 uses this fact.

## Implementation notes

* `Rockafellar.isAffineSet_iff_coe_affineSpan` identifies affine sets with sets that equal their
  Mathlib `affineSpan`. `Rockafellar.IsAffineSet.toAffineSubspace` and
  `Rockafellar.IsAffineSet.toSubmodule` (for a set that contains the origin) turn an affine set into
  Mathlib structures. Later sections rewrite along these bridges.
* `Rockafellar.dim` is integer-valued because of the convention $\dim \emptyset = -1$.
  `Rockafellar.dim_eq_finrank_direction` identifies it with the `Module.finrank` of the direction of
  the affine hull for a non-empty set. Later sections use this definition of dimension.
* In Theorem 1.4 the book writes $B$ as a real $m \times n$ matrix. Here $B$ is a linear map
  `Rn n →ₗ[ℝ] Rn m`, which is the same data. Corollary 1.4.1 makes the row decomposition of $B$
  explicit through a basis of $L^\perp$.

## Deviations from the source

* **Theorem 1.3** (correction). The book states that every hyperplane is a level set
  $\{x \mid \langle x, b \rangle = \beta\}$ with $b \neq 0$. This fails in $\mathbb{R}^0$, where the
  empty set is a hyperplane and no $b \neq 0$ exists. The statement adds $n > 0$. See
  `Rockafellar.theorem_1_3_exists`.
-/

namespace Rockafellar

open ConvexAnalysis

open scoped Pointwise

variable {m n : ℕ} {M : Set (Rn n)}

/-! ### Affine sets -/

/-- **Section 1** of [rockafellar1970convex], definition of affine set. A set
$M \subseteq \mathbb{R}^n$ is an **affine set** if $(1 - \lambda) x + \lambda y \in M$ for all
$x \in M$, $y \in M$ and $\lambda \in \mathbb{R}$. -/
def IsAffineSet (M : Set (Rn n)) : Prop :=
  ∀ ⦃x : Rn n⦄, x ∈ M → ∀ ⦃y : Rn n⦄, y ∈ M → ∀ l : ℝ, (1 - l) • x + l • y ∈ M

/-- The underlying set of a Mathlib `AffineSubspace` of $\mathbb{R}^n$ is an affine set. -/
theorem isAffineSet_coe (M : AffineSubspace ℝ (Rn n)) : IsAffineSet (M : Set (Rn n)) := by
  intro x hx y hy l
  have h := M.smul_vsub_vadd_mem l hy hx hx
  have he : l • (y -ᵥ x) +ᵥ x = (1 - l) • x + l • y := by
    simp only [vsub_eq_sub, vadd_eq_add, smul_sub, sub_smul, one_smul]
    abel
  rwa [he] at h

/-- For $s \subseteq \mathbb{R}^n$ and $a, z \in \mathbb{R}^n$, $z \in s + \{a\}$ if and only if
$z - a \in s$. -/
theorem mem_add_singleton {s : Set (Rn n)} {a z : Rn n} : z ∈ s + {a} ↔ z - a ∈ s := by
  rw [Set.add_singleton, Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨z - a, h, by abel⟩

/-- If $M$ is an affine set and $a \in \mathbb{R}^n$, then the translate $M + a$ is an affine set.
-/
theorem IsAffineSet.add_singleton (h : IsAffineSet M) (a : Rn n) : IsAffineSet (M + {a}) := by
  intro x hx y hy l
  rw [mem_add_singleton] at hx hy ⊢
  have := h hx hy l
  have he : (1 - l) • (x - a) + l • (y - a) = (1 - l) • x + l • y - a := by
    simp only [smul_sub, sub_smul, one_smul]
    abel
  rwa [he] at this

/-- The subspace of $\mathbb{R}^n$ whose underlying set is an affine set $M$ that contains the
origin. This is the construction in the proof of Theorem 1.1 of [rockafellar1970convex]: $M$ is
closed under scalar multiples because $\lambda x = (1 - \lambda) 0 + \lambda x$, and under sums
because $x + y = 2 \bigl(\tfrac12 x + \tfrac12 y\bigr)$. -/
def IsAffineSet.toSubmodule (h : IsAffineSet M) (h0 : (0 : Rn n) ∈ M) : Submodule ℝ (Rn n) where
  carrier := M
  zero_mem' := h0
  smul_mem' l x hx := by
    have := h h0 hx l
    rwa [smul_zero, zero_add] at this
  add_mem' {x y} hx hy := by
    have hmid : (1 - (1 / 2 : ℝ)) • x + (1 / 2 : ℝ) • y ∈ M := h hx hy _
    have h2 : (1 - (2 : ℝ)) • (0 : Rn n) + (2 : ℝ) • ((1 - (1 / 2 : ℝ)) • x + (1 / 2 : ℝ) • y)
        ∈ M := h h0 hmid 2
    have he : (1 - (2 : ℝ)) • (0 : Rn n)
        + (2 : ℝ) • ((1 - (1 / 2 : ℝ)) • x + (1 / 2 : ℝ) • y) = x + y := by
      simp only [smul_zero, zero_add, smul_add, smul_smul]
      norm_num
    rwa [he] at h2

/-- The underlying set of `Rockafellar.IsAffineSet.toSubmodule` is the affine set it comes from. -/
@[simp] theorem IsAffineSet.coe_toSubmodule (h : IsAffineSet M) (h0 : (0 : Rn n) ∈ M) :
    (h.toSubmodule h0 : Set (Rn n)) = M := rfl

/-- **Theorem 1.1** of [rockafellar1970convex]. The subspaces of $\mathbb{R}^n$ are the affine sets
which contain the origin: a set $M \subseteq \mathbb{R}^n$ is the underlying set of a subspace
if and only if $M$ is affine and $0 \in M$. -/
theorem theorem_1_1 (M : Set (Rn n)) :
    (∃ L : Submodule ℝ (Rn n), (L : Set (Rn n)) = M) ↔ IsAffineSet M ∧ (0 : Rn n) ∈ M := by
  constructor
  · rintro ⟨L, rfl⟩
    refine ⟨fun x hx y hy l => ?_, L.zero_mem⟩
    exact L.add_mem (L.smul_mem _ hx) (L.smul_mem _ hy)
  · rintro ⟨h, h0⟩
    exact ⟨h.toSubmodule h0, rfl⟩

/-- The Mathlib `AffineSubspace` of $\mathbb{R}^n$ whose underlying set is an affine set $M$. It
supports `Rockafellar.isAffineSet_iff_coe_affineSpan`, which relates the affine sets of
[rockafellar1970convex] to Mathlib. -/
def IsAffineSet.toAffineSubspace (h : IsAffineSet M) : AffineSubspace ℝ (Rn n) where
  carrier := M
  smul_vsub_vadd_mem' c {p₁ p₂ p₃} h₁ h₂ h₃ := by
    have hT : IsAffineSet (M + {-p₂}) := h.add_singleton (-p₂)
    have h0 : (0 : Rn n) ∈ M + {-p₂} := mem_add_singleton.2 (by simpa using h₂)
    set L := hT.toSubmodule h0 with hL
    have hp₁ : p₁ - p₂ ∈ L := mem_add_singleton.2 (by simpa using h₁)
    have hp₃ : p₃ - p₂ ∈ L := mem_add_singleton.2 (by simpa using h₃)
    have hmem : c • (p₁ - p₂) + (p₃ - p₂) ∈ L := L.add_mem (L.smul_mem c hp₁) hp₃
    have hmem' : c • (p₁ - p₂) + (p₃ - p₂) ∈ M + {-p₂} := hmem
    rw [mem_add_singleton] at hmem'
    have he : c • (p₁ - p₂) + (p₃ - p₂) - -p₂ = c • (p₁ -ᵥ p₂) +ᵥ p₃ := by
      simp only [vsub_eq_sub, vadd_eq_add]
      abel
    rwa [he] at hmem'

/-- The underlying set of `Rockafellar.IsAffineSet.toAffineSubspace` is the affine set it comes
from. -/
@[simp] theorem IsAffineSet.coe_toAffineSubspace (h : IsAffineSet M) :
    (h.toAffineSubspace : Set (Rn n)) = M := rfl

/-- A set $M \subseteq \mathbb{R}^n$ is an affine set if and only if it equals its affine hull, that
is, the underlying set of the Mathlib `affineSpan` of $M$ is $M$.

This is the bridge between the affine sets of Section 1 of [rockafellar1970convex] and the
affine subspaces of Mathlib, along which the later sections rewrite. -/
theorem isAffineSet_iff_coe_affineSpan (M : Set (Rn n)) :
    IsAffineSet M ↔ (affineSpan ℝ M : Set (Rn n)) = M := by
  constructor
  · intro h
    refine subset_antisymm ?_ (subset_affineSpan ℝ M)
    have : affineSpan ℝ M ≤ h.toAffineSubspace := affineSpan_le.2 (by simp)
    exact this
  · intro h
    rw [← h]
    exact isAffineSet_coe _

/-! ### Translates of subspaces, and Theorem 1.2 -/

/-- For a subspace $L$ of $\mathbb{R}^n$ and $a \in \mathbb{R}^n$, the affine subspace through $a$
with direction $L$ has the underlying set $L + a$. -/
theorem coe_mk'_eq (L : Submodule ℝ (Rn n)) (a : Rn n) :
    (AffineSubspace.mk' a L : Set (Rn n)) = (L : Set (Rn n)) + {a} := by
  ext z
  rw [mem_add_singleton, SetLike.mem_coe, SetLike.mem_coe,
    ← AffineSubspace.vsub_right_mem_direction_iff_mem (AffineSubspace.self_mem_mk' a L) z,
    AffineSubspace.direction_mk']
  rfl

/-- For a subspace $L$ of $\mathbb{R}^n$ and $a \in \mathbb{R}^n$, the translate $L + a$ is an
affine set. -/
theorem isAffineSet_coe_add_singleton (L : Submodule ℝ (Rn n)) (a : Rn n) :
    IsAffineSet ((L : Set (Rn n)) + {a}) := by
  rw [← coe_mk'_eq]
  exact isAffineSet_coe _

/-- For a subspace $L$ of $\mathbb{R}^n$ and $a \in \mathbb{R}^n$, the linear span of the
differences of points of $L + a$ (the Mathlib `vectorSpan`) is $L$. -/
theorem vectorSpan_coe_add_singleton (L : Submodule ℝ (Rn n)) (a : Rn n) :
    vectorSpan ℝ ((L : Set (Rn n)) + {a}) = L := by
  rw [← coe_mk'_eq, ← direction_affineSpan, AffineSubspace.affineSpan_coe,
    AffineSubspace.direction_mk']

/-- Let $M$ be an affine set and $a \in M$. Then $M = V + a$, where $V$ is the linear span of the
differences of points of $M$ (the Mathlib `vectorSpan`). This is the existence part of Theorem
1.2 of [rockafellar1970convex]. -/
theorem eq_vectorSpan_add_singleton (h : IsAffineSet M) {a : Rn n} (ha : a ∈ M) :
    M = (vectorSpan ℝ M : Set (Rn n)) + {a} := by
  have hspan : (affineSpan ℝ M : Set (Rn n)) = M := (isAffineSet_iff_coe_affineSpan M).1 h
  have ha' : a ∈ affineSpan ℝ M := by rw [← SetLike.mem_coe, hspan]; exact ha
  ext z
  rw [mem_add_singleton, SetLike.mem_coe, ← direction_affineSpan,
    show (z - a : Rn n) = z -ᵥ a from rfl,
    AffineSubspace.vsub_right_mem_direction_iff_mem ha' z, ← SetLike.mem_coe, hspan]

/-- **Theorem 1.2** of [rockafellar1970convex]. Each non-empty affine set $M \subseteq \mathbb{R}^n$
is parallel to a unique subspace $L$: there is exactly one subspace $L$ such that $M = L + a$
for some $a \in \mathbb{R}^n$.

The proof takes $L$ to be the Mathlib `vectorSpan` of $M$. `Rockafellar.theorem_1_2_sub`
identifies $L$ with $M - M$. -/
theorem theorem_1_2 (h : IsAffineSet M) (hne : M.Nonempty) :
    ∃! L : Submodule ℝ (Rn n), ∃ a : Rn n, M = (L : Set (Rn n)) + {a} := by
  obtain ⟨a, ha⟩ := hne
  refine ⟨vectorSpan ℝ M, ⟨a, eq_vectorSpan_add_singleton h ha⟩, ?_⟩
  rintro L ⟨c, hc⟩
  rw [hc, vectorSpan_coe_add_singleton]

/-- **Theorem 1.2** of [rockafellar1970convex], the parallel subspace as a difference set. Let $L$
be a subspace of $\mathbb{R}^n$ and $a \in \mathbb{R}^n$. If $M = L + a$, then $L = M - M$. -/
theorem theorem_1_2_sub {L : Submodule ℝ (Rn n)} {a : Rn n} (hL : M = (L : Set (Rn n)) + {a}) :
    (L : Set (Rn n)) = M - M := by
  ext z
  constructor
  · intro hz
    refine ⟨z + a, ?_, a, ?_, by simp⟩
    · rw [hL, mem_add_singleton]
      simpa using hz
    · rw [hL, mem_add_singleton]
      simp
  · rintro ⟨u, hu, v, hv, rfl⟩
    rw [hL, mem_add_singleton] at hu hv
    have := L.sub_mem hu hv
    simpa using this

/-! ### Dimension -/

open scoped Classical in
/-- **Section 1** of [rockafellar1970convex], definition of dimension. The **dimension** of a set
$S \subseteq \mathbb{R}^n$ is the dimension of the subspace parallel to its affine hull, with
the convention $\dim \emptyset = -1$:
$$\dim S = \dim \operatorname{span} \{x - y \mid x, y \in S\} - \begin{cases} 1 & S = \emptyset,
  \\ 0 & S \neq \emptyset. \end{cases}$$

The value is an integer because of the convention for the empty set. The book defines the
dimension for affine sets, as the dimension of the parallel subspace of Theorem 1.2, and for
convex sets $C$, as $\dim \operatorname{aff} C$ (Section 2). The definition here applies to
every set and agrees with both. -/
noncomputable def dim (S : Set (Rn n)) : ℤ :=
  (Module.finrank ℝ (vectorSpan ℝ S) : ℤ) - if S = ∅ then 1 else 0

/-- The empty set has dimension $-1$. -/
@[simp] theorem dim_empty : dim (∅ : Set (Rn n)) = -1 := by
  simp [dim]

/-- For a non-empty set $S \subseteq \mathbb{R}^n$, $\dim S$ is the dimension of the linear span of
the differences of points of $S$ (the Mathlib `vectorSpan`). -/
theorem dim_of_nonempty {S : Set (Rn n)} (h : S.Nonempty) :
    dim S = (Module.finrank ℝ (vectorSpan ℝ S) : ℤ) := by
  simp [dim, h.ne_empty]

/-- For a non-empty set $S \subseteq \mathbb{R}^n$, $\dim S$ is the dimension of the direction of
the affine hull of $S$:
$$\dim S = \dim (\operatorname{aff} S - \operatorname{aff} S).$$

This identifies `Rockafellar.dim` with the `Module.finrank` of the direction of the Mathlib
`affineSpan`. -/
theorem dim_eq_finrank_direction {S : Set (Rn n)} (h : S.Nonempty) :
    dim S = (Module.finrank ℝ (affineSpan ℝ S).direction : ℤ) := by
  rw [dim_of_nonempty h, direction_affineSpan]

/-- For a subspace $L$ of $\mathbb{R}^n$, the linear span of the differences of points of $L$ (the
Mathlib `vectorSpan`) is $L$. This is Theorem 1.1 of [rockafellar1970convex] in the form that
`Rockafellar.dim` uses. -/
theorem vectorSpan_coe_submodule (L : Submodule ℝ (Rn n)) :
    vectorSpan ℝ (L : Set (Rn n)) = L := by
  rw [vectorSpan_eq_span_vsub_set_right ℝ L.zero_mem]
  have himg : (fun x : Rn n => x -ᵥ (0 : Rn n)) '' (L : Set (Rn n)) = (L : Set (Rn n)) := by
    ext z
    simp
  rw [himg, Submodule.span_eq]

/-- The dimension of a subspace $L$ of $\mathbb{R}^n$ is its dimension as a vector space. -/
@[simp] theorem dim_coe_submodule (L : Submodule ℝ (Rn n)) :
    dim (L : Set (Rn n)) = (Module.finrank ℝ L : ℤ) := by
  rw [dim_of_nonempty ⟨0, L.zero_mem⟩, vectorSpan_coe_submodule]

/-- For a subspace $L$ of $\mathbb{R}^n$ and $a \in \mathbb{R}^n$, $\dim(L + a)$ is the dimension of
$L$ as a vector space. -/
@[simp] theorem dim_coe_add_singleton (L : Submodule ℝ (Rn n)) (a : Rn n) :
    dim ((L : Set (Rn n)) + {a}) = (Module.finrank ℝ L : ℤ) := by
  have ha : a ∈ (L : Set (Rn n)) + {a} := by
    rw [mem_add_singleton]
    simp
  rw [dim_of_nonempty ⟨a, ha⟩, vectorSpan_coe_add_singleton]

/-- If $S \subseteq T \subseteq \mathbb{R}^n$ and $S$ is non-empty, then $\dim S \le \dim T$. -/
theorem dim_le_dim_of_subset {S T : Set (Rn n)} (hne : S.Nonempty) (hST : S ⊆ T) :
    dim S ≤ dim T := by
  rw [dim_of_nonempty hne, dim_of_nonempty (hne.mono hST)]
  exact_mod_cast Submodule.finrank_mono (vectorSpan_mono ℝ hST)

/-- The dimension of $\mathbb{R}^n$ is $n$. -/
@[simp] theorem dim_univ : dim (Set.univ : Set (Rn n)) = (n : ℤ) := by
  have huniv : (Set.univ : Set (Rn n)) = ((⊤ : Submodule ℝ (Rn n)) : Set (Rn n)) := by
    ext z
    simp
  rw [huniv, dim_coe_submodule]
  simp

/-- For a set $S \subseteq \mathbb{R}^n$ that contains the origin, the linear span of the
differences of points of $S$ (the Mathlib `vectorSpan`) is the linear span of $S$. This is
Theorem 1.1 of [rockafellar1970convex] in the form that Theorem 2.7 uses. -/
theorem vectorSpan_eq_span_of_zero_mem {S : Set (Rn n)} (h0 : (0 : Rn n) ∈ S) :
    vectorSpan ℝ S = Submodule.span ℝ S :=
  _root_.vectorSpan_eq_span_of_zero_mem h0

/-- For a set $S \subseteq \mathbb{R}^n$ that contains the origin, the affine hull of $S$ is the
linear span of $S$. This is a consequence of Theorem 1.1 of [rockafellar1970convex]. -/
theorem coe_affineSpan_of_zero_mem {S : Set (Rn n)} (h0 : (0 : Rn n) ∈ S) :
    (affineSpan ℝ S : Set (Rn n)) = (Submodule.span ℝ S : Set (Rn n)) := by
  have h0' : (0 : Rn n) ∈ affineSpan ℝ S := subset_affineSpan ℝ S h0
  have hmk : AffineSubspace.mk' (0 : Rn n) (affineSpan ℝ S).direction = affineSpan ℝ S :=
    AffineSubspace.mk'_eq h0'
  rw [← hmk, coe_mk'_eq, direction_affineSpan, vectorSpan_eq_span_of_zero_mem h0]
  ext z
  rw [mem_add_singleton]
  simp

/-! ### Hyperplanes: Theorem 1.3 -/

/-- **Section 1** of [rockafellar1970convex], definition of hyperplane. A **hyperplane** in
$\mathbb{R}^n$ is an affine set $H$ of dimension $n - 1$.

The dimension is `Rockafellar.dim`, so for $n = 0$ the empty set, of dimension $-1$, is a
hyperplane in $\mathbb{R}^0$. -/
def IsHyperplane (H : Set (Rn n)) : Prop :=
  IsAffineSet H ∧ dim H = (n : ℤ) - 1

/-- For $a, b, x \in \mathbb{R}^n$, $x - a$ is orthogonal to $b$ if and only if
$\langle x, b \rangle = \langle a, b \rangle$. -/
theorem sub_mem_orthogonal_span_singleton_iff (b x a : Rn n) :
    x - a ∈ ((ℝ ∙ b)ᗮ : Submodule ℝ (Rn n)) ↔ pairing n x b = pairing n a b := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right, sub_eq_zero]
  simp only [pairing_apply]
  rw [real_inner_comm x b, real_inner_comm a b]

/-- Let $b \in \mathbb{R}^n$ with $b \neq 0$, and let $\beta \in \mathbb{R}$. The level set
$\{x \mid \langle x, b \rangle = \beta\}$ is the translate of the orthogonal complement of
$\mathbb{R} b$ through the point $(\beta / \|b\|^2) b$. -/
theorem setOf_pairing_eq (b : Rn n) (hb : b ≠ 0) (β : ℝ) :
    {x : Rn n | pairing n x b = β}
      = (((ℝ ∙ b)ᗮ : Submodule ℝ (Rn n)) : Set (Rn n)) + {(β / ‖b‖ ^ 2) • b} := by
  have hnorm : ‖b‖ ≠ 0 := norm_ne_zero_iff.2 hb
  have ha : pairing n ((β / ‖b‖ ^ 2) • b) b = β := by
    rw [pairing_apply, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  ext x
  rw [mem_add_singleton, SetLike.mem_coe, sub_mem_orthogonal_span_singleton_iff, ha]
  exact Iff.rfl

/-- For $b \in \mathbb{R}^n$ with $b \neq 0$, the orthogonal complement of $\mathbb{R} b$ has
dimension $n - 1$, stated as $\dim (\mathbb{R} b)^\perp + 1 = n$. -/
theorem finrank_orthogonal_span_singleton_add_one (b : Rn n) (hb : b ≠ 0) :
    Module.finrank ℝ ((ℝ ∙ b)ᗮ : Submodule ℝ (Rn n)) + 1 = n := by
  have h := Submodule.finrank_add_finrank_orthogonal (K := (ℝ ∙ b : Submodule ℝ (Rn n)))
  rw [finrank_span_singleton hb, finrank_euclideanSpace_fin] at h
  omega

/-- **Theorem 1.3** of [rockafellar1970convex], the level sets are hyperplanes. Given
$\beta \in \mathbb{R}$ and a non-zero $b \in \mathbb{R}^n$, the set
$$H = \{x \mid \langle x, b \rangle = \beta\}$$
is a hyperplane in $\mathbb{R}^n$. -/
theorem theorem_1_3 (b : Rn n) (hb : b ≠ 0) (β : ℝ) :
    IsHyperplane {x : Rn n | pairing n x b = β} := by
  have hrank := finrank_orthogonal_span_singleton_add_one b hb
  rw [setOf_pairing_eq b hb β]
  refine ⟨isAffineSet_coe_add_singleton _ _, ?_⟩
  rw [dim_coe_add_singleton]
  omega

/-- **Theorem 1.3** of [rockafellar1970convex], every hyperplane is a level set. Let $n > 0$. Every
hyperplane $H$ in $\mathbb{R}^n$ has the form $H = \{x \mid \langle x, b \rangle = \beta\}$ for
some $b \in \mathbb{R}^n$ with $b \neq 0$ and some $\beta \in \mathbb{R}$.

**Correction.** The book does not assume $n > 0$, and the statement is false without it. In
$\mathbb{R}^0$ the empty set has dimension $-1 = n - 1$, so it is a hyperplane, but there is no
non-zero $b \in \mathbb{R}^0$. For $n \ge 1$ every hyperplane is non-empty, and the hypothesis
has no effect. -/
theorem theorem_1_3_exists (hn : 0 < n) {H : Set (Rn n)} (h : IsHyperplane H) :
    ∃ (b : Rn n) (β : ℝ), b ≠ 0 ∧ H = {x : Rn n | pairing n x b = β} := by
  obtain ⟨haff, hdim⟩ := h
  have hne : H.Nonempty := by
    rcases Set.eq_empty_or_nonempty H with rfl | hne
    · rw [dim_empty] at hdim
      omega
    · exact hne
  obtain ⟨a, ha⟩ := hne
  have hL : (Module.finrank ℝ (vectorSpan ℝ H) : ℤ) = (n : ℤ) - 1 := by
    rw [← dim_of_nonempty ⟨a, ha⟩]
    exact hdim
  have hperp : Module.finrank ℝ ((vectorSpan ℝ H)ᗮ : Submodule ℝ (Rn n)) = 1 := by
    have h2 := Submodule.finrank_add_finrank_orthogonal (K := vectorSpan ℝ H)
    rw [finrank_euclideanSpace_fin] at h2
    omega
  obtain ⟨b, hbmem, hbne⟩ : ∃ b : Rn n, b ∈ (vectorSpan ℝ H)ᗮ ∧ b ≠ 0 := by
    refine Submodule.exists_mem_ne_zero_of_ne_bot ?_
    intro hbot
    rw [hbot] at hperp
    simp at hperp
  have hspan : (ℝ ∙ b) = ((vectorSpan ℝ H)ᗮ : Submodule ℝ (Rn n)) := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rwa [Submodule.span_singleton_le_iff_mem]
    · rw [finrank_span_singleton hbne, hperp]
  have hLeq : vectorSpan ℝ H = ((ℝ ∙ b)ᗮ : Submodule ℝ (Rn n)) := by
    rw [hspan, Submodule.orthogonal_orthogonal]
  refine ⟨b, pairing n a b, hbne, ?_⟩
  have hH : H = ((vectorSpan ℝ H : Submodule ℝ (Rn n)) : Set (Rn n)) + {a} :=
    eq_vectorSpan_add_singleton haff ha
  ext x
  rw [hH, mem_add_singleton, SetLike.mem_coe, hLeq, sub_mem_orthogonal_span_singleton_iff]
  exact Iff.rfl

/-- **Theorem 1.3** of [rockafellar1970convex], uniqueness. Let $b, b' \in \mathbb{R}^n$ be non-zero
and $\beta, \beta' \in \mathbb{R}$. If $\{x \mid \langle x, b \rangle = \beta\} = \{x \mid
\langle x, b' \rangle = \beta'\}$, then there is $\lambda \neq 0$ with $b' = \lambda b$ and
$\beta' = \lambda \beta$. -/
theorem theorem_1_3_unique {b b' : Rn n} {β β' : ℝ} (hb : b ≠ 0) (hb' : b' ≠ 0)
    (h : {x : Rn n | pairing n x b = β} = {x : Rn n | pairing n x b' = β'}) :
    ∃ l : ℝ, l ≠ 0 ∧ b' = l • b ∧ β' = l * β := by
  have hvs : ((ℝ ∙ b)ᗮ : Submodule ℝ (Rn n)) = ((ℝ ∙ b')ᗮ : Submodule ℝ (Rn n)) := by
    have h1 := congrArg (vectorSpan ℝ) h
    rwa [setOf_pairing_eq b hb β, setOf_pairing_eq b' hb' β', vectorSpan_coe_add_singleton,
      vectorSpan_coe_add_singleton] at h1
  have hsp : (ℝ ∙ b) = (ℝ ∙ b') := by
    have := congrArg (fun K : Submodule ℝ (Rn n) => Kᗮ) hvs
    rwa [Submodule.orthogonal_orthogonal, Submodule.orthogonal_orthogonal] at this
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l • b = b' := by
    have : b' ∈ (ℝ ∙ b) := by rw [hsp]; exact Submodule.mem_span_singleton_self b'
    rwa [Submodule.mem_span_singleton] at this
  have hlne : l ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hl
    exact hb' hl.symm
  refine ⟨l, hlne, hl.symm, ?_⟩
  have hnorm : ‖b‖ ≠ 0 := norm_ne_zero_iff.2 hb
  set a : Rn n := (β / ‖b‖ ^ 2) • b with hadef
  have ha : pairing n a b = β := by
    rw [hadef, pairing_apply, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  have hamem : a ∈ {x : Rn n | pairing n x b' = β'} := by
    rw [← h]
    exact ha
  have hamem' : pairing n a b' = β' := hamem
  rw [← hl, map_smul, smul_eq_mul, ha] at hamem'
  exact hamem'.symm

/-! ### Linear systems: Theorem 1.4 and Corollary 1.4.1 -/

/-- **Theorem 1.4** of [rockafellar1970convex], solution sets are affine. Given $b \in \mathbb{R}^m$
and a linear map $B : \mathbb{R}^n \to \mathbb{R}^m$, the set
$\{x \in \mathbb{R}^n \mid Bx = b\}$ is an affine set in $\mathbb{R}^n$.

The book writes $B$ as a real $m \times n$ matrix. A linear map `Rn n →ₗ[ℝ] Rn m` is the same
data. -/
theorem theorem_1_4 (B : Rn n →ₗ[ℝ] Rn m) (b : Rn m) : IsAffineSet {x : Rn n | B x = b} := by
  intro x hx y hy l
  have hx' : B x = b := hx
  have hy' : B y = b := hy
  change B ((1 - l) • x + l • y) = b
  rw [map_add, map_smul, map_smul, hx', hy', ← add_smul]
  simp

/-- **Theorem 1.4** of [rockafellar1970convex], every affine set is a solution set. For every affine
set $M \subseteq \mathbb{R}^n$ there are $k \in \mathbb{N}$, a linear map
$B : \mathbb{R}^n \to \mathbb{R}^k$ and $b \in \mathbb{R}^k$ such that $M = \{x \mid Bx = b\}$.

The statement includes the empty set and $\mathbb{R}^n$, which are solution sets for degenerate
choices of $B$ and $b$. -/
theorem theorem_1_4_exists (h : IsAffineSet M) :
    ∃ (k : ℕ) (B : Rn n →ₗ[ℝ] Rn k) (b : Rn k), M = {x : Rn n | B x = b} := by
  rcases Set.eq_empty_or_nonempty M with rfl | ⟨a, ha⟩
  · have hnt : Nontrivial (Rn 1) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp)
    obtain ⟨c, hc⟩ := exists_ne (0 : Rn 1)
    refine ⟨1, 0, c, ?_⟩
    ext x
    simp only [Set.mem_empty_iff_false, false_iff]
    intro hx
    have hx' : (0 : Rn 1) = c := hx
    exact hc hx'.symm
  · set L := vectorSpan ℝ M with hLdef
    refine ⟨n, (Lᗮ : Submodule ℝ (Rn n)).starProjection.toLinearMap,
      (Lᗮ : Submodule ℝ (Rn n)).starProjection a, ?_⟩
    have hM : M = (L : Set (Rn n)) + {a} := eq_vectorSpan_add_singleton h ha
    have key : ∀ z : Rn n, z ∈ L ↔ (Lᗮ : Submodule ℝ (Rn n)).starProjection z = 0 := by
      intro z
      rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal]
    ext x
    rw [hM, mem_add_singleton, SetLike.mem_coe, key, map_sub, sub_eq_zero]
    exact Iff.rfl

/-- For $u, x, a \in \mathbb{R}^n$, $\langle u, x - a \rangle = 0$ if and only if
$\langle x, u \rangle = \langle a, u \rangle$. -/
theorem pairing_sub_eq_zero_iff (u x a : Rn n) :
    pairing n u (x - a) = 0 ↔ pairing n x u = pairing n a u := by
  simp only [pairing_apply]
  rw [inner_sub_right, sub_eq_zero, real_inner_comm x u, real_inner_comm a u]

/-- For $S \subseteq \mathbb{R}^n$ and $v \in \mathbb{R}^n$, $v$ is orthogonal to the linear span of
$S$ if and only if $\langle u, v \rangle = 0$ for all $u \in S$. -/
theorem mem_orthogonal_span_iff {S : Set (Rn n)} {v : Rn n} :
    v ∈ ((Submodule.span ℝ S)ᗮ : Submodule ℝ (Rn n)) ↔ ∀ u ∈ S, pairing n u v = 0 := by
  simp only [pairing_apply]
  rw [Submodule.mem_orthogonal]
  refine ⟨fun h u hu => h u (Submodule.subset_span hu), fun h u hu => ?_⟩
  have hle : Submodule.span ℝ S ≤ ((ℝ ∙ v)ᗮ : Submodule ℝ (Rn n)) := by
    rw [Submodule.span_le]
    exact fun z hz => Submodule.mem_orthogonal_singleton_iff_inner_left.2 (h z hz)
  exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 (hle hu)

/-- **Corollary 1.4.1** of [rockafellar1970convex]. Every affine subset $M$ of $\mathbb{R}^n$ is the
intersection of a finite collection of hyperplanes: there are $k \in \mathbb{N}$ and hyperplanes
$H_1, \dots, H_k$ in $\mathbb{R}^n$ with $M = H_1 \cap \dots \cap H_k$.

The degenerate cases are included. $\mathbb{R}^n$ is the intersection of the empty collection
($k = 0$). For $n \ge 1$ the empty set is the intersection of two parallel hyperplanes, and for
$n = 0$ it is itself the only hyperplane of $\mathbb{R}^0$. -/
theorem corollary_1_4_1 (h : IsAffineSet M) :
    ∃ (k : ℕ) (H : Fin k → Set (Rn n)), (∀ i, IsHyperplane (H i)) ∧ M = ⋂ i, H i := by
  rcases Set.eq_empty_or_nonempty M with rfl | ⟨a, ha⟩
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · refine ⟨1, fun _ => (∅ : Set (Rn 0)), fun _ => ⟨?_, by simp⟩, ?_⟩
      · intro x hx
        exact absurd hx (Set.notMem_empty x)
      · exact Set.Subset.antisymm (Set.empty_subset _) fun x hx => Set.mem_iInter.1 hx 0
    · have hnt : Nontrivial (Rn n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa)
      obtain ⟨b, hb⟩ := exists_ne (0 : Rn n)
      refine ⟨2, fun i => {x : Rn n | pairing n x b = if i = 0 then 0 else 1},
        fun i => theorem_1_3 b hb _, ?_⟩
      ext x
      simp only [Set.mem_empty_iff_false, Set.mem_iInter, false_iff]
      intro hx
      have h0 : pairing n x b = 0 := by simpa using hx 0
      have h1 : pairing n x b = 1 := by simpa using hx 1
      rw [h0] at h1
      exact zero_ne_one h1
  · set L := vectorSpan ℝ M with hLdef
    set v := Module.finBasis ℝ ((Lᗮ : Submodule ℝ (Rn n))) with hvdef
    have hspan : Submodule.span ℝ (Set.range fun i => ((v i : Rn n)))
        = (Lᗮ : Submodule ℝ (Rn n)) := by
      have h1 := congrArg (Submodule.map (Lᗮ : Submodule ℝ (Rn n)).subtype) v.span_eq
      rwa [Submodule.map_span, ← Set.range_comp, Submodule.map_subtype_top] at h1
    refine ⟨Module.finrank ℝ ((Lᗮ : Submodule ℝ (Rn n))),
      fun i => {x : Rn n | pairing n x (v i : Rn n) = pairing n a (v i : Rn n)}, fun i => ?_, ?_⟩
    · refine theorem_1_3 _ ?_ _
      simpa using v.ne_zero i
    · have hM : M = (L : Set (Rn n)) + {a} := eq_vectorSpan_add_singleton h ha
      ext x
      have key : x - a ∈ L ↔ ∀ u ∈ Set.range (fun i => ((v i : Rn n))),
          pairing n u (x - a) = 0 := by
        rw [← mem_orthogonal_span_iff, hspan, Submodule.orthogonal_orthogonal]
      rw [hM, mem_add_singleton, SetLike.mem_coe, key, Set.mem_iInter]
      constructor
      · intro hx i
        exact (pairing_sub_eq_zero_iff _ x a).1 (hx _ ⟨i, rfl⟩)
      · rintro hx u ⟨i, rfl⟩
        exact (pairing_sub_eq_zero_iff _ x a).2 (hx i)

/-! ### Affine transformations: Theorems 1.5 and 1.6 -/

/-- **Section 1** of [rockafellar1970convex], definition of affine transformation. A map
$T : \mathbb{R}^n \to \mathbb{R}^m$ is an **affine transformation** if
$$T((1 - \lambda) x + \lambda y) = (1 - \lambda) Tx + \lambda Ty$$
for all $x, y \in \mathbb{R}^n$ and $\lambda \in \mathbb{R}$. -/
def IsAffineMap (T : Rn n → Rn m) : Prop :=
  ∀ (x y : Rn n) (l : ℝ), T ((1 - l) • x + l • y) = (1 - l) • T x + l • T y

/-- **Theorem 1.5** of [rockafellar1970convex]. The affine transformations from $\mathbb{R}^n$ to
$\mathbb{R}^m$ are the mappings $T$ of the form $Tx = Ax + a$, where $A$ is a linear
transformation and $a \in \mathbb{R}^m$: a map $T$ is affine if and only if there are a linear
map $A$ and $a \in \mathbb{R}^m$ with $Tx = Ax + a$ for all $x$. -/
theorem theorem_1_5 (T : Rn n → Rn m) :
    IsAffineMap T ↔ ∃ (A : Rn n →ₗ[ℝ] Rn m) (a : Rn m), ∀ x, T x = A x + a := by
  constructor
  · intro h
    have hsmul : ∀ (l : ℝ) (x : Rn n), T (l • x) - T 0 = l • (T x - T 0) := by
      intro l x
      have hx := h 0 x l
      rw [smul_zero, zero_add] at hx
      rw [hx]
      module
    have hadd : ∀ x y : Rn n, T (x + y) - T 0 = (T x - T 0) + (T y - T 0) := by
      intro x y
      have h1 := h x y (1 / 2 : ℝ)
      have h2 := hsmul (2 : ℝ) ((1 / 2 : ℝ) • (x + y))
      have harg : (1 - (1 / 2 : ℝ)) • x + (1 / 2 : ℝ) • y = (1 / 2 : ℝ) • (x + y) := by module
      have harg2 : (2 : ℝ) • ((1 / 2 : ℝ) • (x + y)) = x + y := by module
      rw [harg] at h1
      rw [harg2, h1] at h2
      rw [h2]
      module
    exact ⟨{ toFun := fun x => T x - T 0, map_add' := hadd, map_smul' := hsmul }, T 0,
      fun x => by simp⟩
  · rintro ⟨A, a, hT⟩ x y l
    rw [hT, hT, hT, map_add, map_smul, map_smul]
    module

/-- For a linear isomorphism $A : \mathbb{R}^n \to \mathbb{R}^m$ and $c \in \mathbb{R}^n$,
$d \in \mathbb{R}^m$, the map $x \mapsto A(x - c) + d$ is an affine transformation. -/
theorem isAffineMap_linear_translate (A : Rn n ≃ₗ[ℝ] Rn m) (c : Rn n) (d : Rn m) :
    IsAffineMap (fun x => A (x - c) + d) := by
  intro x y l
  have harg : (1 - l) • x + l • y - c = (1 - l) • (x - c) + l • (y - c) := by module
  simp only [harg, map_add, map_smul]
  module

/-- For a linear isomorphism $A : \mathbb{R}^n \to \mathbb{R}^m$ and $c \in \mathbb{R}^n$,
$d \in \mathbb{R}^m$, the map $x \mapsto A(x - c) + d$ is a bijection. -/
theorem bijective_linear_translate (A : Rn n ≃ₗ[ℝ] Rn m) (c : Rn n) (d : Rn m) :
    Function.Bijective (fun x => A (x - c) + d) := by
  constructor
  · intro x y hxy
    have h1 : A (x - c) = A (y - c) := by
      have := hxy
      simpa using this
    have h2 : x - c = y - c := A.injective h1
    have := sub_left_injective h2
    exact this
  · intro z
    refine ⟨A.symm (z - d) + c, ?_⟩
    simp

/-- Let $(v_i)_{i \in \iota}$ and $(v'_i)_{i \in \iota}$ be two linearly independent families in
$\mathbb{R}^n$ with the same index set. Then there is a linear isomorphism $A$ of $\mathbb{R}^n$
onto itself with $A v_i = v'_i$ for all $i$. -/
theorem exists_linearEquiv_apply_eq {ι : Type} {v v' : ι → Rn n}
    (hv : LinearIndependent ℝ v) (hv' : LinearIndependent ℝ v') :
    ∃ A : Rn n ≃ₗ[ℝ] Rn n, ∀ i, A (v i) = v' i := by
  obtain ⟨A, hA⟩ := Submodule.exists_linearEquiv_restrict_eq
    ((Module.Basis.span hv).equiv (Module.Basis.span hv') (Equiv.refl ι))
  refine ⟨A, fun i => ?_⟩
  have h1 := (hA (Module.Basis.span hv i)).symm
  rwa [Module.Basis.coe_span_apply, Module.Basis.equiv_apply, Equiv.refl_apply,
    Module.Basis.coe_span_apply] at h1

/-- **Theorem 1.6** of [rockafellar1970convex]. Let $\{b_0, b_1, \dots, b_m\}$ and
$\{b'_0, b'_1, \dots, b'_m\}$ be affinely independent sets in $\mathbb{R}^n$. Then there is a
one-to-one affine transformation $T$ of $\mathbb{R}^n$ onto itself with $T b_i = b'_i$ for
$i = 0, \dots, m$.

The two sets are affinely independent families `b b' : Fin (k + 1) → Rn n`, so the points are
listed in order and the number $m$ is `k`. -/
theorem theorem_1_6 {k : ℕ} {b b' : Fin (k + 1) → Rn n}
    (hb : AffineIndependent ℝ b) (hb' : AffineIndependent ℝ b') :
    ∃ T : Rn n → Rn n, IsAffineMap T ∧ Function.Bijective T ∧ ∀ i, T (b i) = b' i := by
  have hv : LinearIndependent ℝ fun i : {x : Fin (k + 1) // x ≠ 0} => b (i : Fin (k + 1)) - b 0 :=
    (affineIndependent_iff_linearIndependent_vsub ℝ b 0).1 hb
  have hv' : LinearIndependent ℝ
      fun i : {x : Fin (k + 1) // x ≠ 0} => b' (i : Fin (k + 1)) - b' 0 :=
    (affineIndependent_iff_linearIndependent_vsub ℝ b' 0).1 hb'
  obtain ⟨A, hA⟩ := exists_linearEquiv_apply_eq hv hv'
  refine ⟨fun x => A (x - b 0) + b' 0, isAffineMap_linear_translate _ _ _,
    bijective_linear_translate _ _ _, fun i => ?_⟩
  by_cases hi : i = 0
  · subst hi
    simp
  · have h1 : A (b i - b 0) = b' i - b' 0 := hA ⟨i, hi⟩
    simp [h1]

/-- **Theorem 1.6** of [rockafellar1970convex], uniqueness when $m = n$. Let $\{b_0, \dots, b_n\}$
be an affinely independent set of $n + 1$ points in $\mathbb{R}^n$. If two affine
transformations $T_1, T_2$ of $\mathbb{R}^n$ into itself agree at every $b_i$, then $T_1 = T_2$.

So the transformation of `Rockafellar.theorem_1_6` is unique when $m = n$. The statement does
not need $T_1$ and $T_2$ to be bijective. -/
theorem theorem_1_6_unique {b : Fin (n + 1) → Rn n} (hb : AffineIndependent ℝ b)
    {T₁ T₂ : Rn n → Rn n} (h₁ : IsAffineMap T₁) (h₂ : IsAffineMap T₂)
    (hT : ∀ i, T₁ (b i) = T₂ (b i)) : T₁ = T₂ := by
  obtain ⟨A₁, a₁, hA₁⟩ := (theorem_1_5 T₁).1 h₁
  obtain ⟨A₂, a₂, hA₂⟩ := (theorem_1_5 T₂).1 h₂
  have hDb : ∀ i, (A₁ - A₂) (b i) = a₂ - a₁ := by
    intro i
    have h := hT i
    rw [hA₁, hA₂] at h
    simp only [LinearMap.sub_apply]
    have : A₁ (b i) - A₂ (b i) = a₂ - a₁ := by
      rw [sub_eq_sub_iff_add_eq_add, add_comm a₂ (A₂ (b i))]
      exact h
    exact this
  have hspan : vectorSpan ℝ (Set.range b) = ⊤ :=
    AffineIndependent.vectorSpan_eq_top_of_card_eq_finrank_add_one hb (by simp)
  have hle : vectorSpan ℝ (Set.range b) ≤ LinearMap.ker (A₁ - A₂) := by
    rw [vectorSpan_eq_span_vsub_set_right ℝ (Set.mem_range_self 0), Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    have hi := hDb i
    have h0 := hDb 0
    simp only [SetLike.mem_coe, LinearMap.mem_ker, vsub_eq_sub, map_sub, hi, h0, sub_self]
  have hD : ∀ x : Rn n, A₁ x = A₂ x := by
    intro x
    have hx : x ∈ vectorSpan ℝ (Set.range b) := by
      rw [hspan]
      trivial
    have := hle hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
    exact this
  have ha : a₁ = a₂ := by
    have h0 := hDb 0
    rw [LinearMap.sub_apply, hD (b 0), sub_self] at h0
    exact (sub_eq_zero.1 h0.symm).symm
  funext x
  rw [hA₁, hA₂, hD x, ha]

/-- For a linear isomorphism $A : \mathbb{R}^n \to \mathbb{R}^m$, a set $S \subseteq \mathbb{R}^n$
and $c \in \mathbb{R}^n$, $d \in \mathbb{R}^m$, the map $x \mapsto A(x - c) + d$ carries $S + c$
onto $A S + d$. -/
theorem image_linear_translate (A : Rn n ≃ₗ[ℝ] Rn m) (S : Set (Rn n)) (c : Rn n) (d : Rn m) :
    (fun x => A (x - c) + d) '' (S + {c}) = ((fun x => A x) '' S) + {d} := by
  ext z
  rw [mem_add_singleton]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_add_singleton] at hx
    simp only [add_sub_cancel_right]
    exact ⟨x - c, hx, rfl⟩
  · rintro ⟨u, hu, hue⟩
    refine ⟨u + c, ?_, ?_⟩
    · rw [mem_add_singleton, add_sub_cancel_right]
      exact hu
    · simp [hue]

/-- **Corollary 1.6.1** of [rockafellar1970convex]. Let $M_1$ and $M_2$ be affine sets in
$\mathbb{R}^n$ with $\dim M_1 = \dim M_2$. Then there is a one-to-one affine transformation $T$
of $\mathbb{R}^n$ onto itself with $T M_1 = M_2$.

The dimension is `Rockafellar.dim`, so the statement includes the case $M_1 = M_2 = \emptyset$. -/
theorem corollary_1_6_1 {M₁ M₂ : Set (Rn n)} (h₁ : IsAffineSet M₁) (h₂ : IsAffineSet M₂)
    (hdim : dim M₁ = dim M₂) :
    ∃ T : Rn n → Rn n, IsAffineMap T ∧ Function.Bijective T ∧ T '' M₁ = M₂ := by
  rcases Set.eq_empty_or_nonempty M₁ with rfl | ⟨a₁, ha₁⟩
  · have hM₂ : M₂ = ∅ := by
      rcases Set.eq_empty_or_nonempty M₂ with h | ⟨a₂, ha₂⟩
      · exact h
      · rw [dim_empty, dim_of_nonempty ⟨a₂, ha₂⟩] at hdim
        omega
    subst hM₂
    exact ⟨id, fun _ _ _ => rfl, Function.bijective_id, by simp⟩
  · have hM₂ne : M₂.Nonempty := by
      rcases Set.eq_empty_or_nonempty M₂ with rfl | h
      · rw [dim_empty, dim_of_nonempty ⟨a₁, ha₁⟩] at hdim
        omega
      · exact h
    obtain ⟨a₂, ha₂⟩ := hM₂ne
    have hrank : Module.finrank ℝ (vectorSpan ℝ M₁) = Module.finrank ℝ (vectorSpan ℝ M₂) := by
      rw [dim_of_nonempty ⟨a₁, ha₁⟩, dim_of_nonempty ⟨a₂, ha₂⟩] at hdim
      omega
    obtain ⟨e⟩ : Nonempty ((vectorSpan ℝ M₁) ≃ₗ[ℝ] (vectorSpan ℝ M₂)) :=
      ⟨LinearEquiv.ofFinrankEq _ _ hrank⟩
    obtain ⟨A, hA⟩ := Submodule.exists_linearEquiv_restrict_eq e
    have hM₁ : M₁ = ((vectorSpan ℝ M₁ : Submodule ℝ (Rn n)) : Set (Rn n)) + {a₁} :=
      eq_vectorSpan_add_singleton h₁ ha₁
    have hM₂ : M₂ = ((vectorSpan ℝ M₂ : Submodule ℝ (Rn n)) : Set (Rn n)) + {a₂} :=
      eq_vectorSpan_add_singleton h₂ ha₂
    have hmap : (fun x => A x) '' ((vectorSpan ℝ M₁ : Submodule ℝ (Rn n)) : Set (Rn n))
        = ((vectorSpan ℝ M₂ : Submodule ℝ (Rn n)) : Set (Rn n)) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hx' := (hA ⟨x, hx⟩).symm
        simp only [hx']
        exact (e ⟨x, hx⟩).2
      · intro hy
        refine ⟨(e.symm ⟨y, hy⟩ : Rn n), (e.symm ⟨y, hy⟩).2, ?_⟩
        have hy' := (hA (e.symm ⟨y, hy⟩)).symm
        simpa using hy'
    refine ⟨fun x => A (x - a₁) + a₂, isAffineMap_linear_translate _ _ _,
      bijective_linear_translate _ _ _, ?_⟩
    rw [hM₁, image_linear_translate, hmap]
    exact hM₂.symm


/-! ### The orthogonal complement of a graph -/

/-- **Section 1** of [rockafellar1970convex], orthogonal complement of a graph. Let
$A : \mathbb{R}^n \to \mathbb{R}^m$ be linear. The graph
$L = \{(x, Ax) \mid x \in \mathbb{R}^n\}$ of $A$ is a subspace, and its orthogonal complement is
the graph of $-A^*$:
$$L^\perp = \{(x^*, y^*) \mid x^* = -A^* y^*\}.$$

The book works in $\mathbb{R}^{n+m}$. Here the ambient space is the product
$\mathbb{R}^n \times \mathbb{R}^m$ with the pairing `Rockafellar.pairingProd`, $\langle (x, y),
(x^*, y^*) \rangle = \langle x, x^* \rangle + \langle y, y^* \rangle$, which is the same
bilinear form after the identification of $\mathbb{R}^n \times \mathbb{R}^m$ with
$\mathbb{R}^{n+m}$. The adjoint $A^*$ is `LinearMap.adjoint A`. The book does not number this
fact, but Section 22 uses it. -/
theorem orthogonal_graph_eq_graph_neg_adjoint (A : Rn n →ₗ[ℝ] Rn m) :
    {z : Rn n × Rn m | ∀ w : Rn n × Rn m, w.2 = A w.1 → pairingProd n m w z = 0}
      = {z : Rn n × Rn m | z.1 = -(LinearMap.adjoint A) z.2} := by
  ext z
  constructor
  · intro hz
    have key : ∀ x : Rn n, (inner ℝ x (z.1 + LinearMap.adjoint A z.2) : ℝ) = 0 := by
      intro x
      have hx := hz (x, A x) rfl
      rw [prodPairing_apply] at hx
      simp only [pairing_apply] at hx
      rw [inner_add_right, LinearMap.adjoint_inner_right]
      exact hx
    have h0 := key (z.1 + LinearMap.adjoint A z.2)
    rw [inner_self_eq_zero] at h0
    exact eq_neg_of_add_eq_zero_left h0
  · intro hz
    have hz' : z.1 = -(LinearMap.adjoint A) z.2 := hz
    intro w hw
    rw [prodPairing_apply, hw]
    simp only [pairing_apply]
    rw [hz', ← LinearMap.adjoint_inner_right, inner_neg_right]
    ring

end Rockafellar

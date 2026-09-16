import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import NumlibSurface.Rockafellar.Common.Euclidean

/-!
# Rockafellar §1: affine sets

Surface file for R. Tyrrell Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §1:
affine sets in `ℝⁿ`, the unique subspace each is parallel to, dimension, hyperplanes and the
linear systems whose solution sets affine sets are, and affine transformations.

All 8 numbered results of §1 are formalized. The content is linear algebra, so §1 specialises
almost nothing from the backbone and is closed by Mathlib's affine-space and inner-product API.

The converse half of `theorem_1_3` carries `0 < n`, which the book does not: in `ℝ⁰` the empty set
has dimension `-1 = n - 1` and so is a hyperplane, yet there is no non-zero `b ∈ ℝ⁰` to represent
it with. For `n ≥ 1` the hypothesis is vacuous, and `corollary_1_4_1` needs none. Theorem 1.4's
`B` is a linear map `ℝⁿ →ₗ[ℝ] ℝᵐ` rather than an `m × n` matrix; the row decomposition the book
writes is what `corollary_1_4_1` makes explicit, through a basis of `L⊥`.

## Main definitions

* `IsAffineSet M` — `(1-λ)x + λy ∈ M` for all `x, y ∈ M` and all `λ ∈ ℝ`. Bridged to Mathlib by
  `isAffineSet_iff_coe_affineSpan` and `IsAffineSet.toAffineSubspace`, and to `Submodule` by
  `IsAffineSet.toSubmodule` when `M` contains the origin.
* `dim S` — the dimension of the subspace parallel to `aff S`. It is `ℤ`-valued because
  Rockafellar's convention is `dim ∅ = -1`; `dim_eq_finrank_direction` identifies it with the
  `finrank` of the direction otherwise. Later sections use this definition.
* `IsHyperplane` — an affine set of dimension `n - 1`.
* `IsAffineMap` — the book's *affine transformation*.

## Main results

* `theorem_1_1` — the subspaces of `ℝⁿ` are exactly the affine sets containing the origin.
* `theorem_1_2`, `theorem_1_2_sub` — a non-empty affine set is parallel to a unique subspace,
  namely `M - M`.
* `theorem_1_3`, `theorem_1_3_exists`, `theorem_1_3_unique` — the hyperplanes of `ℝⁿ` are the
  level sets `{x | ⟨x, b⟩ = β}` of a non-zero `b`, and `(b, β)` is determined up to a common
  non-zero multiple.
* `theorem_1_4`, `theorem_1_4_exists` — the affine sets are exactly the solution sets `{x | Bx = b}`
  of systems of linear equations.
* `corollary_1_4_1` — every affine set is an intersection of finitely many hyperplanes.
* `theorem_1_5` — the affine transformations `ℝⁿ → ℝᵐ` are the maps `x ↦ Ax + a` with `A` linear.
* `theorem_1_6`, `theorem_1_6_unique` — two affinely independent sets of `m + 1` points are
  carried onto each other by a bijective affine transformation of `ℝⁿ`, uniquely when `m = n`.
* `corollary_1_6_1` — any two affine sets of the same dimension are carried onto each other by a
  bijective affine transformation of `ℝⁿ`.
* `isAffineSet_iff_coe_affineSpan`, `dim_eq_finrank_direction` — the bridges to Mathlib's
  `affineSpan` and `finrank` that the rest of the surface rewrites along.
* `orthogonal_graph_eq_graph_neg_adjoint` — the unnumbered fact of §1 that §22 depends on: the
  orthogonal complement of the graph of a linear `A` is the graph of `-A*`.
-/

namespace Rockafellar

open ConvexAnalysis

open scoped Pointwise

variable {m n : ℕ} {M : Set (Rn n)}

/-! ### Affine sets -/

/-- Rockafellar's **affine set**: `M ⊆ ℝⁿ` such that `(1 - λ)x + λy ∈ M` whenever `x ∈ M`,
`y ∈ M` and `λ ∈ ℝ`. -/
def IsAffineSet (M : Set (Rn n)) : Prop :=
  ∀ ⦃x : Rn n⦄, x ∈ M → ∀ ⦃y : Rn n⦄, y ∈ M → ∀ l : ℝ, (1 - l) • x + l • y ∈ M

/-- The underlying set of an `AffineSubspace` is an affine set. -/
theorem isAffineSet_coe (M : AffineSubspace ℝ (Rn n)) : IsAffineSet (M : Set (Rn n)) := by
  intro x hx y hy l
  have h := M.smul_vsub_vadd_mem l hy hx hx
  have he : l • (y -ᵥ x) +ᵥ x = (1 - l) • x + l • y := by
    simp only [vsub_eq_sub, vadd_eq_add, smul_sub, sub_smul, one_smul]
    abel
  rwa [he] at h

/-- Membership in a translate, unfolded. -/
theorem mem_add_singleton {s : Set (Rn n)} {a z : Rn n} : z ∈ s + {a} ↔ z - a ∈ s := by
  rw [Set.add_singleton, Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨z - a, h, by abel⟩

/-- A translate of an affine set is affine. -/
theorem IsAffineSet.add_singleton (h : IsAffineSet M) (a : Rn n) : IsAffineSet (M + {a}) := by
  intro x hx y hy l
  rw [mem_add_singleton] at hx hy ⊢
  have := h hx hy l
  have he : (1 - l) • (x - a) + l • (y - a) = (1 - l) • x + l • y - a := by
    simp only [smul_sub, sub_smul, one_smul]
    abel
  rwa [he] at this

/-- Rockafellar's proof of Theorem 1.1: an affine set containing the origin is a subspace. This
packages it as a `Submodule`. -/
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

/-- The carrier of `IsAffineSet.toSubmodule` is the set it came from. -/
@[simp] theorem IsAffineSet.coe_toSubmodule (h : IsAffineSet M) (h0 : (0 : Rn n) ∈ M) :
    (h.toSubmodule h0 : Set (Rn n)) = M := rfl

/-- **Theorem 1.1.** The subspaces of `ℝⁿ` are the affine sets which contain the
origin. -/
theorem theorem_1_1 (M : Set (Rn n)) :
    (∃ L : Submodule ℝ (Rn n), (L : Set (Rn n)) = M) ↔ IsAffineSet M ∧ (0 : Rn n) ∈ M := by
  constructor
  · rintro ⟨L, rfl⟩
    refine ⟨fun x hx y hy l => ?_, L.zero_mem⟩
    exact L.add_mem (L.smul_mem _ hx) (L.smul_mem _ hy)
  · rintro ⟨h, h0⟩
    exact ⟨h.toSubmodule h0, rfl⟩

/-- An affine set is the underlying set of an `AffineSubspace`. -/
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

/-- The carrier of `IsAffineSet.toAffineSubspace` is the set it came from. -/
@[simp] theorem IsAffineSet.coe_toAffineSubspace (h : IsAffineSet M) :
    (h.toAffineSubspace : Set (Rn n)) = M := rfl

/-- **The bridge to Mathlib.** A subset of `ℝⁿ` is affine in Rockafellar's sense exactly when it
is its own affine hull. -/
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

/-- A translate of a subspace is the affine subspace through `a` in that direction. -/
theorem coe_mk'_eq (L : Submodule ℝ (Rn n)) (a : Rn n) :
    (AffineSubspace.mk' a L : Set (Rn n)) = (L : Set (Rn n)) + {a} := by
  ext z
  rw [mem_add_singleton, SetLike.mem_coe, SetLike.mem_coe,
    ← AffineSubspace.vsub_right_mem_direction_iff_mem (AffineSubspace.self_mem_mk' a L) z,
    AffineSubspace.direction_mk']
  rfl

/-- A translate of a subspace is an affine set. -/
theorem isAffineSet_coe_add_singleton (L : Submodule ℝ (Rn n)) (a : Rn n) :
    IsAffineSet ((L : Set (Rn n)) + {a}) := by
  rw [← coe_mk'_eq]
  exact isAffineSet_coe _

/-- The direction of a translate of a subspace is that subspace. -/
theorem vectorSpan_coe_add_singleton (L : Submodule ℝ (Rn n)) (a : Rn n) :
    vectorSpan ℝ ((L : Set (Rn n)) + {a}) = L := by
  rw [← coe_mk'_eq, ← direction_affineSpan, AffineSubspace.affineSpan_coe,
    AffineSubspace.direction_mk']

/-- A non-empty affine set is the translate of its direction by any one of its points. This is
the existence half of Theorem 1.2, phrased through Mathlib's `vectorSpan`. -/
theorem eq_vectorSpan_add_singleton (h : IsAffineSet M) {a : Rn n} (ha : a ∈ M) :
    M = (vectorSpan ℝ M : Set (Rn n)) + {a} := by
  have hspan : (affineSpan ℝ M : Set (Rn n)) = M := (isAffineSet_iff_coe_affineSpan M).1 h
  have ha' : a ∈ affineSpan ℝ M := by rw [← SetLike.mem_coe, hspan]; exact ha
  ext z
  rw [mem_add_singleton, SetLike.mem_coe, ← direction_affineSpan,
    show (z - a : Rn n) = z -ᵥ a from rfl,
    AffineSubspace.vsub_right_mem_direction_iff_mem ha' z, ← SetLike.mem_coe, hspan]

/-- **Theorem 1.2.** Each non-empty affine set `M` is parallel to a unique subspace `L`, that is,
`M = L + a` for some `a`. The witness is `vectorSpan ℝ M`; `theorem_1_2_sub` identifies it with
`M - M`. -/
theorem theorem_1_2 (h : IsAffineSet M) (hne : M.Nonempty) :
    ∃! L : Submodule ℝ (Rn n), ∃ a : Rn n, M = (L : Set (Rn n)) + {a} := by
  obtain ⟨a, ha⟩ := hne
  refine ⟨vectorSpan ℝ M, ⟨a, eq_vectorSpan_add_singleton h ha⟩, ?_⟩
  rintro L ⟨c, hc⟩
  rw [hc, vectorSpan_coe_add_singleton]

/-- **Theorem 1.2**, second sentence: a subspace parallel to `M` is `M - M`. -/
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
/-- Rockafellar's **dimension** of a subset of `ℝⁿ`: the dimension of the subspace parallel to
its affine hull, with the convention `dim ∅ = -1`. It is therefore `ℤ`-valued.

For an affine set this is the dimension of the parallel subspace of Theorem 1.2, and for a convex
set it is the dimension of `aff C` (§2). -/
noncomputable def dim (S : Set (Rn n)) : ℤ :=
  (Module.finrank ℝ (vectorSpan ℝ S) : ℤ) - if S = ∅ then 1 else 0

/-- Rockafellar's convention: the empty set has dimension `-1`. -/
@[simp] theorem dim_empty : dim (∅ : Set (Rn n)) = -1 := by
  simp [dim]

/-- On a non-empty set `dim` is the `finrank` of the direction. -/
theorem dim_of_nonempty {S : Set (Rn n)} (h : S.Nonempty) :
    dim S = (Module.finrank ℝ (vectorSpan ℝ S) : ℤ) := by
  simp [dim, h.ne_empty]

/-- On a non-empty set `dim` is the `finrank` of the direction of the affine hull. -/
theorem dim_eq_finrank_direction {S : Set (Rn n)} (h : S.Nonempty) :
    dim S = (Module.finrank ℝ (affineSpan ℝ S).direction : ℤ) := by
  rw [dim_of_nonempty h, direction_affineSpan]

/-- The direction of a subspace, as a set, is the subspace itself — **Theorem 1.1** in the form
`dim` needs it. -/
theorem vectorSpan_coe_submodule (L : Submodule ℝ (Rn n)) :
    vectorSpan ℝ (L : Set (Rn n)) = L := by
  rw [vectorSpan_eq_span_vsub_set_right ℝ L.zero_mem]
  have himg : (fun x : Rn n => x -ᵥ (0 : Rn n)) '' (L : Set (Rn n)) = (L : Set (Rn n)) := by
    ext z
    simp
  rw [himg, Submodule.span_eq]

/-- The dimension of a subspace is its `finrank`. -/
@[simp] theorem dim_coe_submodule (L : Submodule ℝ (Rn n)) :
    dim (L : Set (Rn n)) = (Module.finrank ℝ L : ℤ) := by
  rw [dim_of_nonempty ⟨0, L.zero_mem⟩, vectorSpan_coe_submodule]

/-- The dimension of a translate of a subspace is the `finrank` of that subspace. -/
@[simp] theorem dim_coe_add_singleton (L : Submodule ℝ (Rn n)) (a : Rn n) :
    dim ((L : Set (Rn n)) + {a}) = (Module.finrank ℝ L : ℤ) := by
  have ha : a ∈ (L : Set (Rn n)) + {a} := by
    rw [mem_add_singleton]
    simp
  rw [dim_of_nonempty ⟨a, ha⟩, vectorSpan_coe_add_singleton]

/-- `dim` is monotone. -/
theorem dim_le_dim_of_subset {S T : Set (Rn n)} (hne : S.Nonempty) (hST : S ⊆ T) :
    dim S ≤ dim T := by
  rw [dim_of_nonempty hne, dim_of_nonempty (hne.mono hST)]
  exact_mod_cast Submodule.finrank_mono (vectorSpan_mono ℝ hST)

/-- `dim ℝⁿ = n`. -/
@[simp] theorem dim_univ : dim (Set.univ : Set (Rn n)) = (n : ℤ) := by
  have huniv : (Set.univ : Set (Rn n)) = ((⊤ : Submodule ℝ (Rn n)) : Set (Rn n)) := by
    ext z
    simp
  rw [huniv, dim_coe_submodule]
  simp

/-- **Theorem 1.1** in the form §2's Theorem 2.7 needs it: for a set containing the origin, the
direction of the affine hull is the linear span. -/
theorem vectorSpan_eq_span_of_zero_mem {S : Set (Rn n)} (h0 : (0 : Rn n) ∈ S) :
    vectorSpan ℝ S = Submodule.span ℝ S :=
  _root_.vectorSpan_eq_span_of_zero_mem h0

/-- **Theorem 1.1**: for a set containing the origin, the affine hull *is* the linear span. -/
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

/-- Rockafellar's **hyperplane**: an `(n-1)`-dimensional affine set in `ℝⁿ`. -/
def IsHyperplane (H : Set (Rn n)) : Prop :=
  IsAffineSet H ∧ dim H = (n : ℤ) - 1

/-- `x - a ⊥ b` says exactly that `x` and `a` have the same pairing against `b`. -/
theorem sub_mem_orthogonal_span_singleton_iff (b x a : Rn n) :
    x - a ∈ ((ℝ ∙ b)ᗮ : Submodule ℝ (Rn n)) ↔ pairing n x b = pairing n a b := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right, sub_eq_zero]
  simp only [pairing_apply]
  rw [real_inner_comm x b, real_inner_comm a b]

/-- The level set `⟨·, b⟩ = β` is the translate of `(ℝb)ᗮ` through `(β/‖b‖²)b`. -/
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

/-- The orthogonal complement of a line has dimension `n - 1`. -/
theorem finrank_orthogonal_span_singleton_add_one (b : Rn n) (hb : b ≠ 0) :
    Module.finrank ℝ ((ℝ ∙ b)ᗮ : Submodule ℝ (Rn n)) + 1 = n := by
  have h := Submodule.finrank_add_finrank_orthogonal (K := (ℝ ∙ b : Submodule ℝ (Rn n)))
  rw [finrank_span_singleton hb, finrank_euclideanSpace_fin] at h
  omega

/-- **Theorem 1.3**, first sentence. Given `β ∈ ℝ` and a non-zero `b ∈ ℝⁿ`, the set
`H = {x | ⟨x, b⟩ = β}` is a hyperplane in `ℝⁿ`. -/
theorem theorem_1_3 (b : Rn n) (hb : b ≠ 0) (β : ℝ) :
    IsHyperplane {x : Rn n | pairing n x b = β} := by
  have hrank := finrank_orthogonal_span_singleton_add_one b hb
  rw [setOf_pairing_eq b hb β]
  refine ⟨isAffineSet_coe_add_singleton _ _, ?_⟩
  rw [dim_coe_add_singleton]
  omega

/-- **Theorem 1.3**, second sentence: every hyperplane is of that form.

The hypothesis `0 < n` is not in the book, and is genuinely needed: in `ℝ⁰` the empty set has
dimension `-1 = n - 1`, so it is a hyperplane in Rockafellar's sense, yet there is no non-zero
`b ∈ ℝ⁰`. For `n ≥ 1` a hyperplane is automatically non-empty. -/
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

/-- **Theorem 1.3**, third sentence: `b` and `β` are unique up to a common non-zero
multiple. -/
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

/-- **Theorem 1.4**, first sentence. Given `b ∈ ℝᵐ` and a linear `B : ℝⁿ → ℝᵐ`, the solution set
`{x | Bx = b}` is an affine set in `ℝⁿ`. The book writes `B` as an `m × n` matrix; a linear map is
the same data. -/
theorem theorem_1_4 (B : Rn n →ₗ[ℝ] Rn m) (b : Rn m) : IsAffineSet {x : Rn n | B x = b} := by
  intro x hx y hy l
  have hx' : B x = b := hx
  have hy' : B y = b := hy
  change B ((1 - l) • x + l • y) = b
  rw [map_add, map_smul, map_smul, hx', hy', ← add_smul]
  simp

/-- **Theorem 1.4**, second sentence: every affine set is such a solution set. The
empty set and `ℝⁿ` are covered, by degenerate choices of `B`. -/
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

/-- `u ⊥ (x - a)` says exactly that `x` and `a` have the same pairing against `u`. -/
theorem pairing_sub_eq_zero_iff (u x a : Rn n) :
    pairing n u (x - a) = 0 ↔ pairing n x u = pairing n a u := by
  simp only [pairing_apply]
  rw [inner_sub_right, sub_eq_zero, real_inner_comm x u, real_inner_comm a u]

/-- Orthogonality to a spanning set is orthogonality to the span. -/
theorem mem_orthogonal_span_iff {S : Set (Rn n)} {v : Rn n} :
    v ∈ ((Submodule.span ℝ S)ᗮ : Submodule ℝ (Rn n)) ↔ ∀ u ∈ S, pairing n u v = 0 := by
  simp only [pairing_apply]
  rw [Submodule.mem_orthogonal]
  refine ⟨fun h u hu => h u (Submodule.subset_span hu), fun h u hu => ?_⟩
  have hle : Submodule.span ℝ S ≤ ((ℝ ∙ v)ᗮ : Submodule ℝ (Rn n)) := by
    rw [Submodule.span_le]
    exact fun z hz => Submodule.mem_orthogonal_singleton_iff_inner_left.2 (h z hz)
  exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 (hle hu)

/-- **Corollary 1.4.1.** Every affine subset of `ℝⁿ` is an intersection of a finite
collection of hyperplanes.

`ℝⁿ` itself is the intersection of the empty collection; `∅` is the intersection of two parallel
hyperplanes when `n ≥ 1`, and is itself the unique hyperplane of `ℝ⁰`. -/
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

/-- Rockafellar's **affine transformation**: a map `T : ℝⁿ → ℝᵐ` with
`T((1-λ)x + λy) = (1-λ)Tx + λTy` for all `x`, `y` and `λ ∈ ℝ`. -/
def IsAffineMap (T : Rn n → Rn m) : Prop :=
  ∀ (x y : Rn n) (l : ℝ), T ((1 - l) • x + l • y) = (1 - l) • T x + l • T y

/-- **Theorem 1.5.** The affine transformations from `ℝⁿ` to `ℝᵐ` are the mappings
`T` of the form `Tx = Ax + a` with `A` linear and `a ∈ ℝᵐ`. -/
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

/-- `x ↦ A(x - c) + d` is an affine transformation. -/
theorem isAffineMap_linear_translate (A : Rn n ≃ₗ[ℝ] Rn m) (c : Rn n) (d : Rn m) :
    IsAffineMap (fun x => A (x - c) + d) := by
  intro x y l
  have harg : (1 - l) • x + l • y - c = (1 - l) • (x - c) + l • (y - c) := by module
  simp only [harg, map_add, map_smul]
  module

/-- `x ↦ A(x - c) + d` is a bijection when `A` is. -/
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

/-- Two linearly independent families with the same index set are carried onto each other by a
linear automorphism of `ℝⁿ`. -/
theorem exists_linearEquiv_apply_eq {ι : Type} {v v' : ι → Rn n}
    (hv : LinearIndependent ℝ v) (hv' : LinearIndependent ℝ v') :
    ∃ A : Rn n ≃ₗ[ℝ] Rn n, ∀ i, A (v i) = v' i := by
  obtain ⟨A, hA⟩ := Submodule.exists_linearEquiv_restrict_eq
    ((Module.Basis.span hv).equiv (Module.Basis.span hv') (Equiv.refl ι))
  refine ⟨A, fun i => ?_⟩
  have h1 := (hA (Module.Basis.span hv i)).symm
  rwa [Module.Basis.coe_span_apply, Module.Basis.equiv_apply, Equiv.refl_apply,
    Module.Basis.coe_span_apply] at h1

/-- **Theorem 1.6.** Two affinely independent sets of `m + 1` points of `ℝⁿ` are
carried onto each other, in order, by a one-to-one affine transformation of `ℝⁿ` onto itself. -/
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

/-- **Theorem 1.6**, last sentence: when the affinely independent set has `n + 1`
points, the transformation is unique. -/
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

/-- The image of a translate under `x ↦ A(x - c) + d`. -/
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

/-- **Corollary 1.6.1.** Any two affine sets of `ℝⁿ` of the same dimension are
carried onto each other by a one-to-one affine transformation of `ℝⁿ` onto itself. -/
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

/-- **Rockafellar, §1, unnumbered**. The graph of a linear transformation
`A : ℝⁿ → ℝᵐ` is a subspace `L` of `ℝⁿ⁺ᵐ`, and its orthogonal complement `L⊥` is the graph of
`-A*`.

The book works in `ℝⁿ⁺ᵐ`; here the ambient space is the product `ℝⁿ × ℝᵐ` with the product pairing
`pairingProd`, which is the same bilinear form under the obvious identification. This identity is
not numbered in the book, but §22 depends on it. -/
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

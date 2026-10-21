import Mathlib.Data.Set.Image

/-!
# Images and zero fibers

The image and kernel conventions of Appendix A.7 are set image and the zero fiber
restricted to a domain. The latter applies to nonlinear maps and is not a linear-map kernel.
-/

namespace CartisGouldToint.AppendixA.Section07

/-- The image `Im(c, D)` of a function over its specified domain. -/
abbrev imageOn {E F : Type*} (c : E → F) (D : Set E) : Set F := c '' D

/-- Membership in the image means having a preimage in the specified domain. -/
@[simp] theorem mem_imageOn {E F : Type*} (c : E → F) (D : Set E) (y : F) :
    y ∈ imageOn c D ↔ ∃ x ∈ D, c x = y := Iff.rfl

/-- The textbook's `Ker(c, D)`: the zero fiber inside `D`, also for nonlinear maps. -/
abbrev zeroFiberOn {E F : Type*} [Zero F] (c : E → F) (D : Set E) : Set E :=
  D ∩ c ⁻¹' {0}

/-- A point of the zero fiber lies in the domain and maps to zero. -/
@[simp] theorem mem_zeroFiberOn {E F : Type*} [Zero F] (c : E → F) (D : Set E) (x : E) :
    x ∈ zeroFiberOn c D ↔ x ∈ D ∧ c x = 0 := Iff.rfl

/-- The restricted zero fiber is contained in its domain. -/
theorem zeroFiberOn_subset {E F : Type*} [Zero F] (c : E → F) (D : Set E) :
    zeroFiberOn c D ⊆ D := Set.inter_subset_left

/-- The zero fiber is nonempty exactly when zero belongs to the image. -/
theorem zero_mem_imageOn_iff {E F : Type*} [Zero F] (c : E → F) (D : Set E) :
    0 ∈ imageOn c D ↔ (zeroFiberOn c D).Nonempty := by
  simp only [mem_imageOn, Set.nonempty_def, mem_zeroFiberOn]

end CartisGouldToint.AppendixA.Section07

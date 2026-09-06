/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Assembly`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul

/-!
# Connectivity matrices and the assembly of a matrix from local blocks

A *local-to-global map* `ι : κ → n` names, inside a global index set `n`, the `κ` indices that one
local piece of a problem owns; the finite element method calls `κ` the local degrees of freedom of
an element and `ι` its connectivity list. The Boolean matrix `Matrix.connectivity ι` of shape
`n × κ` — a `1` in position `(ι p, p)` and zeros elsewhere — is the *scatter* operator of that map,
and its transpose is the *gather* operator `x ↦ x ∘ ι`.

The one theorem here is `Matrix.connectivity_mul_submatrix_mul_transpose`: a matrix supported on
the block `range ι × range ι` is recovered from that block by scattering, `P (Mᵢᵢ) Pᵀ = M`. Summed
over a family of local maps it gives `Matrix.eq_sum_connectivity_mul_submatrix_mul_transpose`, the
statement that a matrix which splits as a sum of locally supported contributions is the sum of the
scattered local blocks, and `Matrix.mulVec_eq_sum_connectivity`, the *unassembled* matrix–vector
product: gather, apply the local block, scatter, add up. Both are the algebraic content of finite
element assembly, and neither mentions any geometry.

## Main definitions

* `Matrix.connectivity ι`: the Boolean scatter matrix of `ι : κ → n`.

## Main results

* `Matrix.transpose_connectivity_mulVec`: gathering is restriction, `Pᵀ *ᵥ x = x ∘ ι`.
* `Matrix.connectivity_mul_submatrix_mul_transpose`: `P (M.submatrix ι ι) Pᵀ = M` for an injective
  `ι` and an `M` supported on `range ι × range ι`.
* `Matrix.eq_sum_connectivity_mul_submatrix_mul_transpose` and `Matrix.mulVec_eq_sum_connectivity`:
  the assembled matrix and the assembled matrix–vector product as sums over the local pieces.
-/

namespace Matrix

variable {n κ E R : Type*}

section Def

variable [DecidableEq n] [Zero R] [One R]

/-- The Boolean *connectivity* (or *scatter*) matrix of a local-to-global index map `ι : κ → n`:
the `n × κ` matrix whose `(i, p)` entry is `1` when `i = ι p` and `0` otherwise. It is the
submatrix of the identity that keeps all rows and selects the columns named by `ι`, so multiplying
by it on the left scatters a local vector into the global index set, and multiplying by its
transpose gathers a global vector down to the local one. -/
def connectivity (ι : κ → n) : Matrix n κ R := Matrix.of fun i p => if i = ι p then 1 else 0

/-- The entries of the connectivity matrix: `1` where the global index `i` is the image of the
local index `p`, and `0` elsewhere. -/
@[simp]
theorem connectivity_apply (ι : κ → n) (i : n) (p : κ) :
    (connectivity ι : Matrix n κ R) i p = if i = ι p then 1 else 0 := rfl

/-- The connectivity matrix is a submatrix of the identity: `P_ι = I_{*, ι}`. -/
theorem connectivity_eq_submatrix_one (ι : κ → n) :
    (connectivity ι : Matrix n κ R) = (1 : Matrix n n R).submatrix id ι := by
  ext i p
  simp [Matrix.one_apply]

/-- The rows of the connectivity matrix at an index of the form `ι p₀` are read by injectivity:
`P (ι p₀) p = δ_{p₀ p}`. -/
theorem connectivity_apply_of_injective [DecidableEq κ] {ι : κ → n} (hι : Function.Injective ι)
    (p₀ p : κ) : (connectivity ι : Matrix n κ R) (ι p₀) p = if p₀ = p then 1 else 0 := by
  simp only [connectivity_apply]
  exact if_congr hι.eq_iff rfl rfl

end Def

section Vec

variable [DecidableEq n] [Fintype n] [NonAssocSemiring R]

/-- Gathering: the transpose of the connectivity matrix restricts a global vector to the local
indices, `Pᵀ *ᵥ x = x ∘ ι`. -/
theorem transpose_connectivity_mulVec (ι : κ → n) (x : n → R) :
    (connectivity ι : Matrix n κ R)ᵀ *ᵥ x = fun p => x (ι p) := by
  funext p
  simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]

end Vec

section Reconstruct

variable [DecidableEq n] [Fintype κ] [Semiring R]

/-- The scatter–gather sandwich reconstructs a locally supported matrix from its local block: if
`ι` is injective and `M` vanishes whenever either index falls outside `range ι`, then
`P (M.submatrix ι ι) Pᵀ = M`.

This is the identity behind finite element assembly. Injectivity says that an element does not
name the same global node twice; the support hypothesis is the one the textbooks leave implicit,
and without it the scatter loses exactly the entries that lie outside the element. -/
theorem connectivity_mul_submatrix_mul_transpose {ι : κ → n} (hι : Function.Injective ι)
    {M : Matrix n n R} (hM : ∀ i j, (i ∉ Set.range ι ∨ j ∉ Set.range ι) → M i j = 0) :
    (connectivity ι : Matrix n κ R) * M.submatrix ι ι * (connectivity ι : Matrix n κ R)ᵀ = M := by
  classical
  ext i j
  have hexp : ((connectivity ι : Matrix n κ R) * M.submatrix ι ι *
      (connectivity ι : Matrix n κ R)ᵀ) i j
      = ∑ q : κ, ∑ p : κ, (connectivity ι : Matrix n κ R) i p * M (ι p) (ι q) *
        (connectivity ι : Matrix n κ R) j q := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, Finset.sum_mul]
  rw [hexp]
  rcases em (∃ p, ι p = i) with ⟨p₀, rfl⟩ | hi
  · rcases em (∃ q, ι q = j) with ⟨q₀, rfl⟩ | hj
    · have hinner : ∀ q : κ, (∑ p : κ, (connectivity ι : Matrix n κ R) (ι p₀) p *
          M (ι p) (ι q) * (connectivity ι : Matrix n κ R) (ι q₀) q)
          = M (ι p₀) (ι q) * (connectivity ι : Matrix n κ R) (ι q₀) q := by
        intro q
        refine Finset.sum_eq_single_of_mem p₀ (Finset.mem_univ _) ?_ |>.trans ?_
        · intro b _ hb
          rw [connectivity_apply_of_injective hι, ite_eq_right (Ne.symm hb), zero_mul, zero_mul]
        · rw [connectivity_apply_of_injective hι, ite_eq_left rfl, one_mul]
      simp only [hinner]
      refine Finset.sum_eq_single_of_mem q₀ (Finset.mem_univ _) ?_ |>.trans ?_
      · intro b _ hb
        rw [connectivity_apply_of_injective hι, ite_eq_right (Ne.symm hb), mul_zero]
      · rw [connectivity_apply_of_injective hι, ite_eq_left rfl, mul_one]
    · rw [hM _ _ (Or.inr (by simpa using hj))]
      refine Finset.sum_eq_zero fun q _ => Finset.sum_eq_zero fun p _ => ?_
      have hne : j ≠ ι q := fun h => hj ⟨q, h.symm⟩
      simp [hne]
  · rw [hM _ _ (Or.inl (by simpa using hi))]
    refine Finset.sum_eq_zero fun q _ => Finset.sum_eq_zero fun p _ => ?_
    have hne : i ≠ ι p := fun h => hi ⟨p, h.symm⟩
    simp [hne]

variable [Fintype E]

/-- **Assembly.** A matrix that splits as a sum of locally supported contributions, one per element
of a finite family with local-to-global maps `ι e`, is the sum of the scattered local blocks:
`A = ∑ₑ Pₑ Aₑ Pₑᵀ` with `Aₑ` the local block `(A e).submatrix (ι e) (ι e)`. -/
theorem eq_sum_connectivity_mul_submatrix_mul_transpose {ι : E → κ → n}
    (hι : ∀ e, Function.Injective (ι e)) {A : Matrix n n R} {Aloc : E → Matrix n n R}
    (hsupp : ∀ e i j, (i ∉ Set.range (ι e) ∨ j ∉ Set.range (ι e)) → Aloc e i j = 0)
    (hA : A = ∑ e, Aloc e) :
    A = ∑ e, (connectivity (ι e) : Matrix n κ R) * (Aloc e).submatrix (ι e) (ι e) *
      (connectivity (ι e) : Matrix n κ R)ᵀ := by
  classical
  rw [hA]
  exact Finset.sum_congr rfl fun e _ =>
    (connectivity_mul_submatrix_mul_transpose (hι e) (hsupp e)).symm

variable [Fintype n]

/-- **The unassembled matrix–vector product.** With the hypotheses of
`Matrix.eq_sum_connectivity_mul_submatrix_mul_transpose`, applying `A` to a vector is: gather onto
each element, apply the local block there, scatter back, and add up. The global matrix `A` never
has to be formed. -/
theorem mulVec_eq_sum_connectivity {ι : E → κ → n} (hι : ∀ e, Function.Injective (ι e))
    {A : Matrix n n R} {Aloc : E → Matrix n n R}
    (hsupp : ∀ e i j, (i ∉ Set.range (ι e) ∨ j ∉ Set.range (ι e)) → Aloc e i j = 0)
    (hA : A = ∑ e, Aloc e) (x : n → R) :
    A *ᵥ x = ∑ e, (connectivity (ι e) : Matrix n κ R) *ᵥ
      ((Aloc e).submatrix (ι e) (ι e) *ᵥ fun p => x (ι e p)) := by
  classical
  conv_lhs => rw [eq_sum_connectivity_mul_submatrix_mul_transpose hι hsupp hA]
  rw [Matrix.sum_mulVec]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← transpose_connectivity_mulVec (ι e) x, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

end Reconstruct

end Matrix

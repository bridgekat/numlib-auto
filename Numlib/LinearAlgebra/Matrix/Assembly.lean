/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

A **local-to-global map** $\iota \colon \kappa \to n$ names, inside a global index set $n$, the
indices that one local piece of a problem owns. The finite element method calls $\kappa$ the local
degrees of freedom of an element and $\iota$ its connectivity list. The **connectivity matrix**
$P_\iota$ of $\iota$ is the $n \times \kappa$ matrix with entry $1$ in position $(\iota(p), p)$ and
$0$ elsewhere. Multiplication by $P_\iota$ scatters a local vector into the global index set, and
multiplication by $P_\iota^T$ gathers a global vector $x$ to the local vector $x \circ \iota$.

The main identity is $P_\iota M_{\iota\iota} P_\iota^T = M$ for an injective $\iota$ and a matrix
$M$ that vanishes outside the block $\operatorname{range} \iota \times \operatorname{range} \iota$,
where $M_{\iota\iota}$ is the local block $(M_{\iota(p) \iota(q)})_{p, q}$. Summed over a family of
local maps, it shows that a matrix which is a sum of locally supported contributions is the sum of
the scattered local blocks. It also gives the unassembled matrix–vector product: gather, apply the
local block, scatter, and add up. These results are the algebraic content of finite element
assembly, and they use no geometry.

## Main definitions

* `Matrix.connectivity`: the connectivity matrix $P_\iota$ of a map $\iota \colon \kappa \to n$.

## Main results

* `Matrix.transpose_connectivity_mulVec`: gathering is restriction, $P_\iota^T x = x \circ \iota$.
* `Matrix.connectivity_mul_submatrix_mul_transpose`: $P_\iota M_{\iota\iota} P_\iota^T = M$ for an
  injective $\iota$ and a matrix $M$ supported on $\operatorname{range} \iota \times
  \operatorname{range} \iota$.
* `Matrix.eq_sum_connectivity_mul_submatrix_mul_transpose`: if $A = \sum_e A_e$ with each $A_e$
  supported on the indices of the element $e$, then $A = \sum_e P_e (A_e)_{\iota_e \iota_e} P_e^T$.
* `Matrix.mulVec_eq_sum_connectivity`: under the same hypotheses, $Ax = \sum_e P_e (A_e)_{\iota_e
  \iota_e} (x \circ \iota_e)$.

## Implementation notes

* The local block $M_{\iota\iota}$ is `M.submatrix ι ι`.
-/

namespace Matrix

variable {n κ E R : Type*}

section Def

variable [DecidableEq n] [Zero R] [One R]

/-- The **connectivity matrix**, or scatter matrix, of a local-to-global index map
$\iota \colon \kappa \to n$ is the $n \times \kappa$ matrix $P_\iota$ with entries
$$(P_\iota)_{ip} = \begin{cases} 1 & \text{if } i = \iota(p), \\ 0 & \text{otherwise.}
  \end{cases}$$
It is the submatrix of the identity that keeps all rows and selects the columns named by
$\iota$. Multiplication by $P_\iota$ on the left scatters a local vector into the global index
set, and multiplication by $P_\iota^T$ gathers a global vector to the local one. -/
def connectivity (ι : κ → n) : Matrix n κ R := Matrix.of fun i p => if i = ι p then 1 else 0

/-- The entries of the connectivity matrix: $(P_\iota)_{ip}$ is $1$ if $i = \iota(p)$ and $0$
otherwise. -/
@[simp]
theorem connectivity_apply (ι : κ → n) (i : n) (p : κ) :
    (connectivity ι : Matrix n κ R) i p = if i = ι p then 1 else 0 := rfl

/-- The connectivity matrix is a submatrix of the identity: $P_\iota$ consists of the columns
$\iota(p)$, $p \in \kappa$, of the identity matrix of order $n$. -/
theorem connectivity_eq_submatrix_one (ι : κ → n) :
    (connectivity ι : Matrix n κ R) = (1 : Matrix n n R).submatrix id ι := by
  ext i p
  simp [Matrix.one_apply]

/-- Let $\iota \colon \kappa \to n$ be injective. Then for $p_0, p \in \kappa$, the entry
$(P_\iota)_{\iota(p_0), p}$ is $1$ if $p_0 = p$ and $0$ otherwise. -/
theorem connectivity_apply_of_injective [DecidableEq κ] {ι : κ → n} (hι : Function.Injective ι)
    (p₀ p : κ) : (connectivity ι : Matrix n κ R) (ι p₀) p = if p₀ = p then 1 else 0 := by
  simp only [connectivity_apply]
  exact if_congr hι.eq_iff rfl rfl

end Def

section Vec

variable [DecidableEq n] [Fintype n] [NonAssocSemiring R]

/-- Gathering is restriction: for a vector $x$ indexed by $n$, $P_\iota^T x = x \circ \iota$, that
is, $(P_\iota^T x)_p = x_{\iota(p)}$. -/
theorem transpose_connectivity_mulVec (ι : κ → n) (x : n → R) :
    (connectivity ι : Matrix n κ R)ᵀ *ᵥ x = fun p => x (ι p) := by
  funext p
  simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]

end Vec

section Reconstruct

variable [DecidableEq n] [Fintype κ] [Semiring R]

/-- Let $\iota \colon \kappa \to n$ be injective, with $\kappa$ finite, and let $M$ be an
$n \times n$ matrix over a semiring with $M_{ij} = 0$ whenever
$i \notin \operatorname{range} \iota$ or $j \notin \operatorname{range} \iota$. Then the scatter
of the local block reconstructs $M$:
$$P_\iota M_{\iota\iota} P_\iota^T = M,$$
where $M_{\iota\iota} = (M_{\iota(p) \iota(q)})_{p, q \in \kappa}$.

This is the identity behind finite element assembly. Injectivity says that an element does not
name the same global node twice. The support hypothesis is the one that textbooks leave
implicit; without it, the scatter loses exactly the entries outside the element. The local block
$M_{\iota\iota}$ is `M.submatrix ι ι`. -/
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

/-- **Assembly.** Let $E$ be a finite set of elements, and for each $e \in E$ let
$\iota_e \colon \kappa \to n$ be an injective local-to-global map and let $A_e$ be an
$n \times n$ matrix over a semiring with $(A_e)_{ij} = 0$ whenever
$i \notin \operatorname{range} \iota_e$ or $j \notin \operatorname{range} \iota_e$. If
$A = \sum_{e \in E} A_e$, then $A$ is the sum of the scattered local blocks:
$$A = \sum_{e \in E} P_{\iota_e} (A_e)_{\iota_e \iota_e} P_{\iota_e}^T.$$

The local block $(A_e)_{\iota_e \iota_e}$ is `(Aloc e).submatrix (ι e) (ι e)`. -/
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

/-- **The unassembled matrix–vector product.** Under the hypotheses of
`Matrix.eq_sum_connectivity_mul_submatrix_mul_transpose`, with $n$ finite, every vector $x$
satisfies
$$Ax = \sum_{e \in E} P_{\iota_e} \bigl((A_e)_{\iota_e \iota_e} (x \circ \iota_e)\bigr).$$
Thus $Ax$ is computed by gathering $x$ onto each element, applying the local block, scattering
back, and adding up. The global matrix $A$ is never formed. -/
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

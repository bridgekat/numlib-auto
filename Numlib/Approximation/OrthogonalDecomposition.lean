import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Order.Interval.Finset.SuccPred

/-!
# The orthogonal grading of an increasing chain of subspaces

Let `S : ℕ → Submodule 𝕜 E` be an increasing chain of finite-dimensional subspaces of an inner
product space. Each level adds to the previous one exactly the part of it orthogonal to that
previous level, and this module names that part and records what it satisfies: the levels are
recovered as sups of the components, distinct components are orthogonal, and the dimensions add.

The motivating instance is the chain of spaces of polynomials of total degree at most `n` inside
`L²` of a domain, where the components are the spaces of "orthogonal polynomials of exact degree
`n`" of multivariable approximation theory; nothing in the development is special to that case.

## Main definitions

* `Approximation.orthogonalComponent S n` is `(S (n - 1))ᗮ ⊓ S n`, with `S 0` itself at `n = 0`.

## Main results

* `Approximation.orthogonalComponent_isOrtho`: distinct components are orthogonal, so the family is
  an `OrthogonalFamily` (`Approximation.orthogonalFamily_orthogonalComponent`) and in particular
  `iSupIndep` (`Approximation.iSupIndep_orthogonalComponent`).
* `Approximation.finsetSup_orthogonalComponent`: `S n` is the sup of the components of index at
  most `n`. Together with the previous item this is the orthogonal direct sum decomposition
  `S n = V 0 ⊕ ⋯ ⊕ V n`.
* `Approximation.finrank_orthogonalComponent_add`: the dimension of the `n + 1`-st component is
  what the `n + 1`-st level adds to the `n`-th.
* `Approximation.starProjection_eq_sum_orthogonalComponent`: the orthogonal projection onto `S n` is
  the sum of the projections onto the components, which is a generalized Fourier expansion written
  without choosing a basis.
* `Approximation.orthogonal_inf_eq_finsetSup`: `(S k)ᗮ ⊓ S n` is the sup of the components of index
  in `Set.Ioc k n`, with `Approximation.mem_finsetSup_Icc_of_mem` its membership form. This is what
  a three-term recursion needs: an element of `S n` orthogonal to `S k` has components only in
  degrees `k + 1, …, n`.
-/

open Module

namespace Approximation

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {S : ℕ → Submodule 𝕜 E}

/-- The `n`-th **orthogonal component** of a chain `S` of subspaces: the part of `S n` orthogonal to
`S (n - 1)`, and `S 0` itself at `n = 0`. For an increasing chain it is what the `n`-th level adds
to the `n - 1`-st one. -/
def orthogonalComponent (S : ℕ → Submodule 𝕜 E) : ℕ → Submodule 𝕜 E
  | 0 => S 0
  | n + 1 => (S n)ᗮ ⊓ S (n + 1)

@[simp]
theorem orthogonalComponent_zero (S : ℕ → Submodule 𝕜 E) : orthogonalComponent S 0 = S 0 := rfl

@[simp]
theorem orthogonalComponent_succ (S : ℕ → Submodule 𝕜 E) (n : ℕ) :
    orthogonalComponent S (n + 1) = (S n)ᗮ ⊓ S (n + 1) := rfl

/-- A component is contained in the level of the same index. -/
theorem orthogonalComponent_le (S : ℕ → Submodule 𝕜 E) (n : ℕ) :
    orthogonalComponent S n ≤ S n := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact inf_le_right

/-- A component of index `> k` is orthogonal to the `k`-th level. -/
theorem orthogonalComponent_le_orthogonal (hS : Monotone S) {k n : ℕ} (h : k < n) :
    orthogonalComponent S n ≤ (S k)ᗮ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact inf_le_left.trans (Submodule.orthogonal_le (hS (by omega)))

/-- Distinct components are orthogonal. -/
theorem orthogonalComponent_isOrtho (hS : Monotone S) {m n : ℕ} (h : m ≠ n) :
    orthogonalComponent S m ⟂ orthogonalComponent S n := by
  wlog hmn : m < n generalizing m n
  · exact (this h.symm (by omega)).symm
  exact Submodule.isOrtho_iff_le.2 <| (orthogonalComponent_le S m).trans <|
    (Submodule.le_orthogonal_orthogonal (S m)).trans
      (Submodule.orthogonal_le (orthogonalComponent_le_orthogonal hS hmn))

/-- The components form an orthogonal family of subspaces. -/
theorem orthogonalFamily_orthogonalComponent (hS : Monotone S) :
    OrthogonalFamily 𝕜 (fun n => orthogonalComponent S n)
      fun n => (orthogonalComponent S n).subtypeₗᵢ :=
  OrthogonalFamily.of_pairwise fun _ _ h => orthogonalComponent_isOrtho hS h

/-- The components are independent: a family of vectors taken from distinct components is linearly
independent. -/
theorem iSupIndep_orthogonalComponent (hS : Monotone S) : iSupIndep (orthogonalComponent S) :=
  (orthogonalFamily_orthogonalComponent hS).independent

/-- The orthogonal projection onto a subspace split as a sup of two orthogonal pieces is the sum of
the projections onto the pieces. The splitting is given as an equation rather than by writing the
sup, so that the statement never has to transport the `Submodule.HasOrthogonalProjection`
instance. -/
theorem starProjection_eq_add_of_isOrtho {K K₁ K₂ : Submodule 𝕜 E} [K.HasOrthogonalProjection]
    [K₁.HasOrthogonalProjection] [K₂.HasOrthogonalProjection] (hK : K₁ ⊔ K₂ = K) (h : K₁ ⟂ K₂)
    (v : E) : K.starProjection v = K₁.starProjection v + K₂.starProjection v := by
  refine Submodule.eq_starProjection_of_mem_orthogonal (K := K) ?_ ?_
  · rw [← hK]
    exact Submodule.add_mem_sup (K₁.starProjection_apply_mem v)
      (K₂.starProjection_apply_mem v)
  · rw [← hK, ← Submodule.inf_orthogonal]
    refine ⟨?_, ?_⟩
    · have hv : v - (K₁.starProjection v + K₂.starProjection v)
          = (v - K₁.starProjection v) - K₂.starProjection v := by abel
      exact hv ▸ Submodule.sub_mem _ (K₁.sub_starProjection_mem_orthogonal v)
        (Submodule.isOrtho_iff_le.1 h.symm (K₂.starProjection_apply_mem v))
    · have hv : v - (K₁.starProjection v + K₂.starProjection v)
          = (v - K₂.starProjection v) - K₁.starProjection v := by abel
      exact hv ▸ Submodule.sub_mem _ (K₂.sub_starProjection_mem_orthogonal v)
        (Submodule.isOrtho_iff_le.1 h (K₁.starProjection_apply_mem v))

section FiniteDimensional

variable (hS : Monotone S) (hfd : ∀ n, FiniteDimensional 𝕜 (S n))
include hS hfd

/-- One level and the next component span the next level. -/
theorem sup_orthogonalComponent_succ (n : ℕ) :
    S n ⊔ orthogonalComponent S (n + 1) = S (n + 1) := by
  have := hfd n
  exact Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection (hS (Nat.le_succ n))

/-- A level is the sup of the components of index at most it. With
`Approximation.orthogonalComponent_isOrtho` this is the orthogonal decomposition
`S n = V 0 ⊕ ⋯ ⊕ V n`. -/
theorem finsetSup_orthogonalComponent (n : ℕ) :
    (Finset.range (n + 1)).sup (orthogonalComponent S) = S n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.range_add_one, Finset.sup_insert, sup_comm, ih,
      sup_orthogonalComponent_succ hS hfd]

/-- `(S k)ᗮ ⊓ S n` is the sup of the components of index in `Set.Ioc k n`. -/
theorem orthogonal_inf_eq_finsetSup (k n : ℕ) :
    (S k)ᗮ ⊓ S n = (Finset.Ioc k n).sup (orthogonalComponent S) := by
  have hbot : ∀ j : ℕ, (S j)ᗮ ⊓ S j = ⊥ := fun j =>
    (inf_comm _ _).trans (Submodule.inf_orthogonal_eq_bot (S j))
  induction n with
  | zero =>
    rw [Finset.Ioc_eq_empty (by omega), Finset.sup_empty, eq_bot_iff]
    exact le_trans (inf_le_inf_left _ (hS (Nat.zero_le k))) (le_of_eq (hbot k))
  | succ n ih =>
    rcases le_or_gt (n + 1) k with hk | hk
    · rw [Finset.Ioc_eq_empty (by omega), Finset.sup_empty, eq_bot_iff]
      exact le_trans (inf_le_inf_left _ (hS hk)) (le_of_eq (hbot k))
    · have hkn : k ≤ n := by omega
      have hsub : orthogonalComponent S (n + 1) ≤ (S k)ᗮ :=
        orthogonalComponent_le_orthogonal hS (by omega)
      rw [← sup_orthogonalComponent_succ hS hfd n, inf_comm, sup_comm (S n),
        sup_inf_assoc_of_le _ hsub, inf_comm (S n) (S k)ᗮ, ih, ← Order.succ_eq_add_one,
        ← Finset.insert_Ioc_right_eq_Ioc_succ hkn, Finset.sup_insert, Order.succ_eq_add_one]

/-- An element of `S n` orthogonal to `S k` lies in the sup of the components of index in
`Set.Ioc k n`. This is the abstract three-term recursion: if multiplication by a coordinate is
symmetric and raises the level by at most one, it moves a component into the three neighbouring
ones. -/
theorem mem_finsetSup_of_mem_of_inner_eq_zero {v : E} {k n : ℕ} (hv : v ∈ S n)
    (h : ∀ w ∈ S k, inner 𝕜 w v = 0) :
    v ∈ (Finset.Ioc k n).sup (orthogonalComponent S) :=
  orthogonal_inf_eq_finsetSup hS hfd k n ▸ ⟨(Submodule.mem_orthogonal _ _).2 h, hv⟩

/-- The form of the previous lemma that survives at `a = 0`: an element of `S n` orthogonal to
every level below `a` lies in the sup of the components of index in `Set.Icc a n`. For `a = 0` the
hypothesis is vacuous and the conclusion is `v ∈ S n`. -/
theorem mem_finsetSup_Icc_of_mem {v : E} {a n : ℕ} (hv : v ∈ S n)
    (h : ∀ k, k + 1 ≤ a → ∀ w ∈ S k, inner 𝕜 w v = 0) :
    v ∈ (Finset.Icc a n).sup (orthogonalComponent S) := by
  cases a with
  | zero =>
    rw [show Finset.Icc 0 n = Finset.range (n + 1) by ext x; simp,
      finsetSup_orthogonalComponent hS hfd]
    exact hv
  | succ b =>
    rw [show Finset.Icc (b + 1) n = Finset.Ioc b n by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega]
    exact mem_finsetSup_of_mem_of_inner_eq_zero hS hfd hv (h b le_rfl)

/-- The dimension of the `n + 1`-st component is what the `n + 1`-st level adds to the `n`-th. -/
theorem finrank_orthogonalComponent_add (n : ℕ) :
    finrank 𝕜 (orthogonalComponent S (n + 1)) + finrank 𝕜 (S n) = finrank 𝕜 (S (n + 1)) := by
  have := hfd n
  have := hfd (n + 1)
  have : FiniteDimensional 𝕜 (orthogonalComponent S (n + 1)) :=
    Submodule.finiteDimensional_of_le (orthogonalComponent_le S (n + 1))
  have hinf : S n ⊓ orthogonalComponent S (n + 1) = ⊥ := by
    rw [eq_bot_iff]
    exact le_trans (inf_le_inf_left _ inf_le_left)
      (le_of_eq (Submodule.inf_orthogonal_eq_bot (S n)))
  have := Submodule.finrank_sup_add_finrank_inf_eq (S n) (orthogonalComponent S (n + 1))
  rw [sup_orthogonalComponent_succ hS hfd n, hinf] at this
  simpa [Nat.add_comm] using this.symm

end FiniteDimensional

section Projection

variable [∀ n, FiniteDimensional 𝕜 (S n)]

instance finiteDimensional_orthogonalComponent (n : ℕ) :
    FiniteDimensional 𝕜 (orthogonalComponent S n) :=
  Submodule.finiteDimensional_of_le (orthogonalComponent_le S n)

/-- The orthogonal projection onto the `n`-th level is the sum of the projections onto the
components of index at most `n`. With `Approximation.finsetSup_orthogonalComponent` this is the
abstract generalized Fourier expansion: choosing an orthonormal basis `{φ_{m,ℓ}}_ℓ` of each
component turns the `m`-th summand into `∑_ℓ ⟪φ_{m,ℓ}, v⟫ φ_{m,ℓ}`, so no basis has to be chosen in
order to state it. -/
theorem starProjection_eq_sum_orthogonalComponent (hS : Monotone S) (n : ℕ) (v : E) :
    (S n).starProjection v =
      ∑ m ∈ Finset.range (n + 1), (orthogonalComponent S m).starProjection v := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hortho : S n ⟂ orthogonalComponent S (n + 1) :=
      (Submodule.isOrtho_iff_le.2 (orthogonalComponent_le_orthogonal hS n.lt_succ_self)).symm
    rw [Finset.sum_range_succ, ← ih, starProjection_eq_add_of_isOrtho
      (sup_orthogonalComponent_succ hS (fun _ => inferInstance) n) hortho v]

end Projection

end Approximation

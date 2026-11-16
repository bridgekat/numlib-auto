/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Order.Interval.Finset.SuccPred

/-!
# The orthogonal grading of an increasing chain of subspaces

Let $S_0 \le S_1 \le S_2 \le \cdots$ be an increasing chain of finite-dimensional subspaces of an
inner product space $E$ over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. The $n$-th **orthogonal
component** $V_n$ is the part of $S_n$ that is orthogonal to $S_{n-1}$, with $V_0 = S_0$. This
module proves that distinct components are orthogonal, that each level is the orthogonal direct sum
$S_n = V_0 \oplus \cdots \oplus V_n$, that the dimensions add, and that the orthogonal projection
onto $S_n$ is the sum of the projections onto $V_0, \dots, V_n$.

The motivating instance is the chain of spaces of polynomials of total degree at most $n$ in $L^2$
of a domain. There $V_n$ is the space of orthogonal polynomials of exact degree $n$ of multivariable
approximation theory. Nothing in the module is special to that case.

## Main definitions

* `Approximation.orthogonalComponent`: $V_0 = S_0$ and $V_{n+1} = S_n^\perp \cap S_{n+1}$.

## Main results

* `Approximation.orthogonalComponent_isOrtho`: distinct components are orthogonal. Hence the
  components form an orthogonal family (`Approximation.orthogonalFamily_orthogonalComponent`) and
  are independent (`Approximation.iSupIndep_orthogonalComponent`).
* `Approximation.finsetSup_orthogonalComponent`: $S_n = V_0 + \cdots + V_n$. With the previous item,
  this is the orthogonal direct sum decomposition $S_n = V_0 \oplus \cdots \oplus V_n$.
* `Approximation.finrank_orthogonalComponent_add`: $\dim V_{n+1} + \dim S_n = \dim S_{n+1}$.
* `Approximation.starProjection_eq_sum_orthogonalComponent`: the orthogonal projection onto $S_n$ is
  the sum of the orthogonal projections onto $V_0, \dots, V_n$, a generalized Fourier expansion that
  needs no choice of basis.
* `Approximation.orthogonal_inf_eq_finsetSup`: $S_k^\perp \cap S_n = V_{k+1} + \cdots + V_n$. Its
  membership form `Approximation.mem_finsetSup_of_mem_of_inner_eq_zero` is what a three-term
  recurrence needs: an element of $S_n$ orthogonal to $S_k$ has components only in the degrees
  $k + 1, \dots, n$.

## Implementation notes

* The chain is a sequence `S : ℕ → Submodule 𝕜 E`. Monotonicity of the chain and finite
  dimensionality of each level are hypotheses of the individual results, not part of the definition.
* A sum of subspaces is the supremum `Finset.sup` in the lattice of submodules.
-/

open Module

namespace Approximation

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {S : ℕ → Submodule 𝕜 E}

/-- The $n$-th **orthogonal component** $V_n$ of a sequence $(S_k)$ of subspaces: $V_0 = S_0$, and
$$V_{n+1} = S_n^\perp \cap S_{n+1}.$$
For an increasing chain, $V_n$ is what the $n$-th level adds to the $(n-1)$-st one. -/
def orthogonalComponent (S : ℕ → Submodule 𝕜 E) : ℕ → Submodule 𝕜 E
  | 0 => S 0
  | n + 1 => (S n)ᗮ ⊓ S (n + 1)

/-- The zeroth orthogonal component is $V_0 = S_0$. -/
@[simp]
theorem orthogonalComponent_zero (S : ℕ → Submodule 𝕜 E) : orthogonalComponent S 0 = S 0 := rfl

/-- The orthogonal component of index $n + 1$ is $V_{n+1} = S_n^\perp \cap S_{n+1}$. -/
@[simp]
theorem orthogonalComponent_succ (S : ℕ → Submodule 𝕜 E) (n : ℕ) :
    orthogonalComponent S (n + 1) = (S n)ᗮ ⊓ S (n + 1) := rfl

/-- For every sequence $(S_k)$ of subspaces and every $n$, the orthogonal component $V_n$ is
contained in $S_n$. -/
theorem orthogonalComponent_le (S : ℕ → Submodule 𝕜 E) (n : ℕ) :
    orthogonalComponent S n ≤ S n := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact inf_le_right

/-- Let $(S_k)$ be an increasing sequence of subspaces, and let $k < n$. Then the orthogonal
component $V_n$ is orthogonal to $S_k$:
$$V_n \le S_k^\perp.$$
-/
theorem orthogonalComponent_le_orthogonal (hS : Monotone S) {k n : ℕ} (h : k < n) :
    orthogonalComponent S n ≤ (S k)ᗮ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact inf_le_left.trans (Submodule.orthogonal_le (hS (by omega)))

/-- Let $(S_k)$ be an increasing sequence of subspaces, and let $m \neq n$. Then the orthogonal
components $V_m$ and $V_n$ are orthogonal. -/
theorem orthogonalComponent_isOrtho (hS : Monotone S) {m n : ℕ} (h : m ≠ n) :
    orthogonalComponent S m ⟂ orthogonalComponent S n := by
  wlog hmn : m < n generalizing m n
  · exact (this h.symm (by omega)).symm
  exact Submodule.isOrtho_iff_le.2 <| (orthogonalComponent_le S m).trans <|
    (Submodule.le_orthogonal_orthogonal (S m)).trans
      (Submodule.orthogonal_le (orthogonalComponent_le_orthogonal hS hmn))

/-- Let $(S_k)$ be an increasing sequence of subspaces. Then the orthogonal components
$(V_n)_{n \in \mathbb{N}}$, each with its inclusion into $E$, form an orthogonal family of
subspaces in the sense of `OrthogonalFamily`. -/
theorem orthogonalFamily_orthogonalComponent (hS : Monotone S) :
    OrthogonalFamily 𝕜 (fun n => orthogonalComponent S n)
      fun n => (orthogonalComponent S n).subtypeₗᵢ :=
  OrthogonalFamily.of_pairwise fun _ _ h => orthogonalComponent_isOrtho hS h

/-- Let $(S_k)$ be an increasing sequence of subspaces. Then the orthogonal components $(V_n)$ are
independent in the sense of `iSupIndep`: each $V_n$ meets the sum of the other components only
in $0$. Equivalently, nonzero vectors taken from distinct components are linearly independent. -/
theorem iSupIndep_orthogonalComponent (hS : Monotone S) : iSupIndep (orthogonalComponent S) :=
  (orthogonalFamily_orthogonalComponent hS).independent

/-- Let $K$, $K_1$ and $K_2$ be subspaces of $E$ that admit orthogonal projections, with
$K_1 + K_2 = K$ and $K_1 \perp K_2$. Then for every $v \in E$,
$$P_K v = P_{K_1} v + P_{K_2} v,$$
where $P_L$ is the orthogonal projection onto $L$.

The splitting is a hypothesis $K_1 \sqcup K_2 = K$ rather than a statement about
$K_1 \sqcup K_2$ itself, so that the statement need not transport the
`Submodule.HasOrthogonalProjection` instance. The projections are `Submodule.starProjection`. -/
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

/-- Let $(S_k)$ be an increasing sequence of finite-dimensional subspaces. Then for every $n$,
$$S_n + V_{n+1} = S_{n+1}.$$
-/
theorem sup_orthogonalComponent_succ (n : ℕ) :
    S n ⊔ orthogonalComponent S (n + 1) = S (n + 1) := by
  have := hfd n
  exact Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection (hS (Nat.le_succ n))

/-- Let $(S_k)$ be an increasing sequence of finite-dimensional subspaces. Then for every $n$, the
level $S_n$ is the sum of the orthogonal components of index at most $n$:
$$V_0 + V_1 + \cdots + V_n = S_n.$$
With `Approximation.orthogonalComponent_isOrtho`, this is the orthogonal direct sum
decomposition $S_n = V_0 \oplus \cdots \oplus V_n$. -/
theorem finsetSup_orthogonalComponent (n : ℕ) :
    (Finset.range (n + 1)).sup (orthogonalComponent S) = S n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.range_add_one, Finset.sup_insert, sup_comm, ih,
      sup_orthogonalComponent_succ hS hfd]

/-- Let $(S_k)$ be an increasing sequence of finite-dimensional subspaces. Then for all $k$ and $n$,
$$S_k^\perp \cap S_n = \sum_{k < m \le n} V_m.$$
For $k \ge n$ both sides are the zero subspace. -/
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

/-- Let $(S_k)$ be an increasing sequence of finite-dimensional subspaces, and let $v \in S_n$
satisfy $\langle w, v \rangle = 0$ for every $w \in S_k$. Then
$$v \in \sum_{k < m \le n} V_m.$$

This is the abstract form of the three-term recurrence: if multiplication by a coordinate is
symmetric and raises the level by at most one, it moves a component into the three neighbouring
ones. -/
theorem mem_finsetSup_of_mem_of_inner_eq_zero {v : E} {k n : ℕ} (hv : v ∈ S n)
    (h : ∀ w ∈ S k, inner 𝕜 w v = 0) :
    v ∈ (Finset.Ioc k n).sup (orthogonalComponent S) :=
  orthogonal_inf_eq_finsetSup hS hfd k n ▸ ⟨(Submodule.mem_orthogonal _ _).2 h, hv⟩

/-- Let $(S_k)$ be an increasing sequence of finite-dimensional subspaces, and let $v \in S_n$
satisfy $\langle w, v \rangle = 0$ for every $w \in S_k$ and every $k < a$. Then
$$v \in \sum_{a \le m \le n} V_m.$$

This form of `Approximation.mem_finsetSup_of_mem_of_inner_eq_zero` also covers $a = 0$, where
the hypothesis is vacuous and the conclusion is $v \in S_n$. -/
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

/-- Let $(S_k)$ be an increasing sequence of finite-dimensional subspaces. Then for every $n$,
$$\dim V_{n+1} + \dim S_n = \dim S_{n+1}.$$
-/
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

/-- Let $(S_k)$ be an increasing sequence of finite-dimensional subspaces. Then for every $n$ and
every $v \in E$, the orthogonal projection of $v$ onto $S_n$ is the sum of its orthogonal
projections onto the components $V_0, \dots, V_n$:
$$P_{S_n} v = \sum_{m=0}^{n} P_{V_m} v.$$

With `Approximation.finsetSup_orthogonalComponent`, this is the generalized Fourier expansion
without a choice of basis: an orthonormal basis $(\varphi_{m,\ell})_\ell$ of each component
$V_m$ turns the $m$-th summand into $\sum_\ell \langle \varphi_{m,\ell}, v \rangle
\varphi_{m,\ell}$. The projections are `Submodule.starProjection`. -/
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

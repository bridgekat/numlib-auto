/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.Brezis.Chapter07.Section02

/-!
# Brezis, Section 7.3: Regularity

This module formalizes Section 7.3 of [brezis2011functional] for a maximal monotone operator $A$ on
a real Hilbert space $H$. The spaces $D(A^k)$ are defined by induction: $D(A^1) = D(A)$ and, for
$k \ge 2$,
$$D(A^k) = \{v \in D(A^{k-1}) : Av \in D(A^{k-1})\}.$$
With the scalar product $(u, v)_{D(A^k)} = \sum_{j=0}^k (A^j u, A^j v)$, the space $D(A^k)$ is a
Hilbert space. Theorem 7.5 says that more regular data give more regular solutions: if
$u_0 \in D(A^k)$, then the solution $u$ of problem (6) of Section 7.2 satisfies
$u \in C^{k-j}([0, +\infty); D(A^j))$ for every $j = 0, 1, \dots, k$.

The results specialize the backbone modules `Numlib.Analysis.InnerProductSpace.MaximalMonotone` and
`Numlib.Analysis.ODE.HilleYosida`.

## Main definitions

* Section 7.3, definition of the spaces $D(A^k)$, `Brezis.Chapter07.domainPow`: the recursive
  subspace $D(A^k)$ of $H$.

## Main results

* `Brezis.Chapter07.domainPow_zero`, `Brezis.Chapter07.domainPow_one` and
  `Brezis.Chapter07.mem_domainPow_succ_iff`: the recursion that defines $D(A^k)$.
* `Brezis.Chapter07.mem_domainPow_iff`: $D(A^k)$ is the set of first coordinates of the tuples
  $(v, Av, \dots, A^k v)$ of the backbone's space `LinearPMap.PowDomain A k`.
* Section 7.3, `Brezis.Chapter07.domainPow_hilbert`: $D(A^k)$ is a Hilbert space for the scalar
  product $\sum_{j \le k} (A^j u, A^j v)$.
* Theorem 7.5, `Brezis.Chapter07.theorem_7_5`: if $u_0 \in D(A^k)$, then
  $u \in C^{k-j}([0, +\infty); D(A^j))$ for every $j \le k$.

## Proof outline

The proof of the source applies Theorem 7.4 to the part $A_1$ of $A$ in the Hilbert space
$H_1 = D(A)$, and then argues by induction on $k$ with $v = du/dt$. The backbone carries out this
induction over the parts `LinearPMap.powPart A j` in
`LinearPMap.IsMaximalMonotone.contDiffOn_semigroup_powPart`, and packages it as
`LinearPMap.IsMaximalMonotone.contDiffOnPowDomain_semigroup` for the semigroup solution. The
uniqueness of Theorem 7.4 transfers the result to every solution $u$.

## Implementation notes

* The space $D(A^k)$ as a Hilbert space is the backbone's `LinearPMap.PowDomain A k`: the tuples
  $(u, Au, \dots, A^k u)$ in `PiLp 2 (Fin (k + 1) → H)`. Its inner product is the scalar product of
  the source, and $A^j u$ is the coordinate `LinearPMap.PowDomain.applyL A k j`.
* The condition $u \in C^n([0, +\infty); D(A^j))$ is the backbone's `LinearPMap.ContDiffOnPowDomain
  A n j u (Set.Ici 0)`: $u$ lifts to a $C^n$ map into `LinearPMap.PowDomain A j`.

## Deviations from the source

* **Theorem 7.5** (generalization). The source states the theorem for $k \ge 2$. It holds for every
  $k$. See `Brezis.Chapter07.theorem_7_5`.
-/

open Filter Topology Set LinearPMap.PowDomain
open scoped InnerProductSpace

noncomputable section

namespace Brezis.Chapter07

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ### The spaces $D(A^k)$ -/

/-- **Section 7.3** of [brezis2011functional], definition of the spaces $D(A^k)$. Let $A$ be a
linear unbounded operator on $H$. The subspaces $D(A^k)$ of $H$ are defined by induction:
$$D(A^0) = H, \qquad D(A^{k+1}) = \{v \in D(A^k) : v \in D(A) \text{ and } Av \in D(A^k)\}.$$
In particular $D(A^1) = D(A)$, and for $k \ge 2$ this is the source's definition $D(A^k) = \{v
\in D(A^{k-1}) : Av \in D(A^{k-1})\}$.

As a submodule of $H$, the second condition is the image under the inclusion $D(A) \subseteq H$
of the preimage of $D(A^k)$ under $A$. -/
def domainPow (A : H →ₗ.[ℝ] H) : ℕ → Submodule ℝ H
  | 0 => ⊤
  | k + 1 => domainPow A k ⊓ (Submodule.comap A.toFun (domainPow A k)).map A.domain.subtype

variable {A : H →ₗ.[ℝ] H}

/-- The space $D(A^0)$ is all of $H$. -/
@[simp]
theorem domainPow_zero : domainPow A 0 = ⊤ :=
  rfl

/-- A vector $v$ lies in $D(A^{k+1})$ if and only if $v \in D(A^k)$, $v \in D(A)$ and
$Av \in D(A^k)$. -/
theorem mem_domainPow_succ_iff {k : ℕ} {v : H} :
    v ∈ domainPow A (k + 1) ↔
      v ∈ domainPow A k ∧ ∃ h : v ∈ A.domain, A ⟨v, h⟩ ∈ domainPow A k := by
  simp only [domainPow, Submodule.mem_inf, Submodule.mem_map, Submodule.mem_comap]
  refine and_congr_right fun _ => ⟨fun ⟨y, hy, hyv⟩ => ?_, fun ⟨h, hv⟩ => ⟨⟨v, h⟩, hv, rfl⟩⟩
  obtain ⟨y, hy'⟩ := y
  change y = v at hyv
  subst hyv
  exact ⟨hy', hy⟩

/-- The space $D(A^1)$ is $D(A)$. -/
@[simp]
theorem domainPow_one : domainPow A 1 = A.domain := by
  ext v
  rw [mem_domainPow_succ_iff, domainPow_zero]
  simp

/-- A vector $v$ lies in $D(A^k)$ if and only if $v$ is the first coordinate of some tuple
$(v, Av, \dots, A^k v)$ of the backbone's space `LinearPMap.PowDomain A k`. -/
theorem mem_domainPow_iff {k : ℕ} {v : H} :
    v ∈ domainPow A k ↔ ∃ x : A.PowDomain k, applyL A k 0 x = v := by
  induction k generalizing v with
  | zero =>
    refine ⟨fun _ => ⟨LinearPMap.PowDomain.mk A (fun _ => v) fun i => i.elim0, rfl⟩,
      fun _ => Submodule.mem_top⟩
  | succ k ih =>
    rw [mem_domainPow_succ_iff]
    constructor
    · rintro ⟨-, h, hAv⟩
      obtain ⟨y, hy⟩ := ih.1 hAv
      -- the tuple `(v, A v, …, A^{k+1} v)` is `v` followed by the tuple of `A v`
      refine ⟨LinearPMap.PowDomain.mk A (Fin.cons v fun i => applyL A k i y) fun i => ?_, ?_⟩
      · induction i using Fin.cases with
        | zero =>
          simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ]
          exact ⟨h, hy.symm⟩
        | succ j =>
          rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
          exact ⟨applyL_mem_domain y j, apply_applyL y j⟩
      · simp
    · rintro ⟨x, rfl⟩
      exact ⟨ih.2 ⟨castL A k x, by simp⟩, applyL_mem_domain x 0,
        ih.2 ⟨shiftL A k x, applyL_zero_shiftL x⟩⟩

/-- **Section 7.3** of [brezis2011functional], the Hilbert structure of $D(A^k)$. Let $H$ be a
Hilbert space, let $A$ be maximal monotone, and let $k \in \mathbb{N}$. Then the space $D(A^k)$
is complete for the scalar product and the norm
$$(u, v)_{D(A^k)} = \sum_{j=0}^k (A^j u, A^j v), \qquad |u|_{D(A^k)} = \Big(\sum_{j=0}^k |A^j
  u|^2\Big)^{1/2}.$$

The source says "it is easily seen" that $D(A^k)$ is a Hilbert space. The space is the
backbone's `LinearPMap.PowDomain A k` of tuples $(u, Au, \dots, A^k u)$, whose first coordinates
form $D(A^k)$ by `Brezis.Chapter07.mem_domainPow_iff`; $A^j u$ is the coordinate
`LinearPMap.PowDomain.applyL A k j`. The completeness holds for every closed operator $A$. -/
theorem domainPow_hilbert [CompleteSpace H] (hA : IsMaximalMonotone A) (k : ℕ) :
    CompleteSpace (A.PowDomain k) ∧
      (∀ x y : A.PowDomain k, ⟪x, y⟫_ℝ = ∑ j, ⟪applyL A k j x, applyL A k j y⟫_ℝ) ∧
      ∀ x : A.PowDomain k, ‖x‖ = Real.sqrt (∑ j, ‖applyL A k j x‖ ^ 2) :=
  ⟨(proposition_7_1_b hA).completeSpace_powDomain k, fun x y => inner_def x y, fun x => by
    rw [← norm_sq_eq, Real.sqrt_sq (norm_nonneg _)]⟩

/-! ### Theorem 7.5 -/

/-- **Theorem 7.5** of [brezis2011functional]. Let $H$ be a Hilbert space, let $A$ be maximal
monotone, let $k \in \mathbb{N}$, and let $u_0 \in D(A^k)$. Let $u$ be the solution of problem
(6) given by Theorem 7.4, in the sense of `Brezis.Chapter07.IsSolution`. Then
$$u \in C^{k-j}([0, +\infty); D(A^j)) \quad \text{for every } j = 0, 1, \dots, k.$$

**Generalization.** The source states the theorem for $k \ge 2$. The statement holds for every
$k$.

The condition $u \in C^{k-j}([0, +\infty); D(A^j))$ is `LinearPMap.ContDiffOnPowDomain A (k - j)
j u (Set.Ici 0)`. -/
theorem theorem_7_5 [CompleteSpace H] (hA : IsMaximalMonotone A) {k : ℕ} {u₀ : H}
    (hu₀ : u₀ ∈ domainPow A k) {u : ℝ → H} (hu : IsSolution A u₀ u) :
    ∀ j ≤ k, A.ContDiffOnPowDomain (k - j : ℕ) j u (Ici 0) := by
  intro j hj
  obtain ⟨x, hx⟩ := mem_domainPow_iff.1 hu₀
  have hmem : u₀ ∈ A.domain := hu.1.apply_zero ▸ hu.1.mem_domain 0 self_mem_Ici
  have hu' : A.IsSolutionOn ((⟨u₀, hmem⟩ : A.domain) : H) (Ici 0) u := hu.1
  refine contDiffOnPowDomain_congr (hA.isMaximalMonotone.contDiffOnPowDomain_semigroup x hj)
    fun t ht => ?_
  rw [hx, (hu'.eq_semigroup hA.isMaximalMonotone ht)]

end Brezis.Chapter07

end

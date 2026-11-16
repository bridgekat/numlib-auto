/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Instances.Matrix

/-!
# Continuity of polynomial coefficients, and the root count in a compact set

Let $R$ be a commutative topological ring. A family of polynomials $p : T \to R[X]$, indexed by a
topological space $T$, depends continuously on its parameter if every coefficient
$t \mapsto [X^j]\, p(t)$ is continuous. This condition is stable under products. So it holds for
$\prod_i (X - \alpha_i)$ as a function of the roots $\alpha$, and for the characteristic polynomial
as a function of the entries of the matrix.

For an integral domain $R$ and a set $S \subseteq R$, let $N_S(p)$ be the number of roots of $p$ in
$S$, counted with multiplicity. The main result is that $N_S(p(t))$ does not depend on $t$, for a
connected parameter space $T$ and a continuous family of monic polynomials of degree $n$ that split
with all roots in $S \cup S'$, where $S$ and $S'$ are disjoint compact sets. Nothing here is
complex-analytic, and $S$ can be any compact set, not only a disc or a set with a tractable
boundary. This matters for the intended application, the Gershgorin disc counting theorem (Theorem
3.12 of [saad2011numerical]), where $S$ is a union of discs that can overlap.

## Main definitions

* `Polynomial.countRootsIn`: the number $N_S(p)$ of roots of $p$ in $S$, counted with multiplicity.

## Main results

* `Polynomial.countRootsIn_le_card_roots`: $N_S(p)$ is at most the number of roots of $p$.
* `Polynomial.roots_prod_univ_X_sub_C`: the multiset of roots of $\prod_i (X - \alpha_i)$ is the
  multiset of the values $\alpha_i$.
* `Polynomial.countRootsIn_prod_univ_X_sub_C`: $N_S(\prod_i (X - \alpha_i))$ is the number of
  indices $i$ with $\alpha_i \in S$.
* `Polynomial.exists_eq_prod_X_sub_C`: a monic polynomial of degree $n$ with $n$ roots is
  $\prod_{i < n} (X - \alpha_i)$ for a tuple $\alpha$ that lists its roots.
* `Polynomial.continuous_coeff_mul`: coefficientwise continuity is stable under multiplication.
* `Polynomial.continuous_coeff_prod`: coefficientwise continuity is stable under finite products.
* `Polynomial.continuous_coeff_X_sub_C`: the coefficients of $X - \alpha(t)$ are continuous in $t$
  when $\alpha$ is continuous.
* `Polynomial.continuous_coeff_prod_X_sub_C`: the coefficients of $\prod_i (X - \alpha_i)$ depend
  continuously on $\alpha$.
* `Matrix.continuous_coeff_charpoly`: the coefficients of the characteristic polynomial depend
  continuously on the matrix.
* `Polynomial.countRootsIn_eq_of_preconnected`: the number of roots in a compact set $S$ is constant
  along a connected family whose roots stay in $S \cup S'$.

## Proof outline

Fix disjoint compact sets $S$ and $S'$, and consider the monic polynomials of degree $n$ that split
with all roots in $S \cup S'$. Each such polynomial is $\prod_i (X - \alpha_i)$ for a tuple
$\alpha \in R^n$. For $J \subseteq \{0, \dots, n-1\}$, the tuples with $\alpha_i \in S$ exactly for
$i \in J$ form the compact box $\prod_i K_i$, where $K_i = S$ for $i \in J$ and $K_i = S'$
otherwise. Its image under the continuous coefficient map is compact, hence closed. A polynomial
determines its multiset of roots, so a polynomial in this image has $N_S = |J|$. Hence each level
set $\{t : N_S(p(t)) = k\}$ is closed. At most $n + 1$ of them are nonempty, and finitely many
disjoint closed sets that cover a space are all open. Connectedness of $T$ finishes the argument.
This compactness argument replaces the usual complex-analytic route through Rouché's theorem or the
argument principle on a contour around $S$.

## Implementation notes

* A polynomial has no topology of its own in Mathlib. Continuity of a family of polynomials is
  therefore stated coefficientwise, as `∀ j, Continuous fun t => (p t).coeff j`.
* `Matrix.continuous_coeff_charpoly` is in this file, not beside the other matrix topology, because
  it is an instance of the same fact: the coefficients of a polynomial built from data depend
  continuously on the data. Its proof applies `Polynomial.continuous_coeff_prod` to the Leibniz
  expansion of the determinant.
-/

open Finset Polynomial

namespace Polynomial

section CountRootsIn

variable {R : Type*} [CommRing R] [IsDomain R]

open scoped Classical in
/-- Let $R$ be an integral domain, let $S \subseteq R$ and let $p \in R[X]$. The **number of roots
of $p$ in $S$**, $N_S(p)$, is the number of roots of $p$ that lie in $S$, counted with
multiplicity.

For the characteristic polynomial of a matrix, this is the number of eigenvalues in $S$, counted
with algebraic multiplicity. The value is the cardinality of `p.roots` filtered by membership in
$S$. Since Mathlib gives the zero polynomial the empty multiset of roots, $N_S(0) = 0$. -/
noncomputable def countRootsIn (S : Set R) (p : R[X]) : ℕ :=
  Multiset.card (p.roots.filter (· ∈ S))

/-- Let $R$ be an integral domain, let $S \subseteq R$ and let $p \in R[X]$. Then $N_S(p)$ is at
most the number of roots of $p$ counted with multiplicity. -/
theorem countRootsIn_le_card_roots (S : Set R) (p : R[X]) :
    p.countRootsIn S ≤ Multiset.card p.roots := by
  classical exact Multiset.card_le_card (Multiset.filter_le _ _)

/-- Let $R$ be an integral domain and let $(\alpha_i)_{i \in \iota}$ be a finite family in $R$. Then
the multiset of roots of $\prod_{i \in \iota} (X - \alpha_i)$ is the multiset of the values
$\alpha_i$, $i \in \iota$. -/
theorem roots_prod_univ_X_sub_C {ι : Type*} [Fintype ι] (α : ι → R) :
    (∏ i, (X - C (α i))).roots = Multiset.map α Finset.univ.val := by
  rw [Finset.prod_eq_multiset_prod,
    show (Multiset.map (fun i => X - C (α i)) Finset.univ.val)
      = Multiset.map (fun a => X - C a) (Multiset.map α Finset.univ.val) by
        rw [Multiset.map_map]; rfl]
  exact roots_multiset_prod_X_sub_C _

open scoped Classical in
/-- Let $R$ be an integral domain, let $S \subseteq R$, and let $(\alpha_i)_{i \in \iota}$ be a
finite family in $R$. Then
$$N_S\Bigl(\prod_{i \in \iota} (X - \alpha_i)\Bigr) = \#\{i \in \iota : \alpha_i \in S\}.$$
-/
theorem countRootsIn_prod_univ_X_sub_C {ι : Type*} [Fintype ι] (S : Set R) (α : ι → R) :
    (∏ i, (X - C (α i))).countRootsIn S = (Finset.univ.filter fun i => α i ∈ S).card := by
  rw [countRootsIn, roots_prod_univ_X_sub_C, Multiset.filter_map, Multiset.card_map]
  rfl

/-- Let $R$ be an integral domain, and let $p \in R[X]$ be monic of degree $n$, with $n$ roots
counted with multiplicity. Then there is a tuple $\alpha = (\alpha_0, \dots, \alpha_{n-1}) \in
R^n$ such that
$$p = \prod_{i=0}^{n-1} (X - \alpha_i),$$
and the multiset of the values $\alpha_i$ is the multiset of roots of $p$.

This is the tuple form of `Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq`. It makes
the roots of such a polynomial available as a point of a compact box in $R^n$. -/
theorem exists_eq_prod_X_sub_C {p : R[X]} {n : ℕ} (hm : p.Monic) (hd : p.natDegree = n)
    (hc : Multiset.card p.roots = n) :
    ∃ α : Fin n → R, p = ∏ i, (X - C (α i)) ∧ Multiset.map α Finset.univ.val = p.roots := by
  obtain ⟨α, hα⟩ : ∃ f : Fin n → R, Multiset.map f Finset.univ.val = p.roots := by
    have hl : p.roots.toList.length = n := by simp [hc]
    subst hl
    exact ⟨p.roots.toList.get, by
      rw [show Multiset.map p.roots.toList.get Finset.univ.val = ↑(List.ofFn p.roots.toList.get) by
        simp [List.ofFn_eq_map], List.ofFn_get, Multiset.coe_toList]⟩
  refine ⟨α, .symm ?_, hα⟩
  calc ∏ i, (X - C (α i)) = (Multiset.map (fun a => X - C a) p.roots).prod := by
        rw [Finset.prod_eq_multiset_prod, ← hα, Multiset.map_map]; rfl
    _ = p := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm (hc.trans hd.symm)

end CountRootsIn

section Continuity

variable {R T ι : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [TopologicalSpace T]

/-- Let $R$ be a commutative topological ring and let $T$ be a topological space. If
$p, q : T \to R[X]$ have continuous coefficients, then for each $j$ the coefficient
$t \mapsto [X^j]\,(p(t) q(t))$ is continuous. Each coefficient of a product is a finite sum of
products of coefficients. -/
theorem continuous_coeff_mul {p q : T → R[X]}
    (hp : ∀ j, Continuous fun t => (p t).coeff j) (hq : ∀ j, Continuous fun t => (q t).coeff j)
    (j : ℕ) : Continuous fun t => (p t * q t).coeff j := by
  simp only [Polynomial.coeff_mul]
  exact continuous_finsetSum _ fun x _ => (hp x.1).mul (hq x.2)

/-- Let $R$ be a commutative topological ring, let $T$ be a topological space, and let $s$ be a
finite set of indices. If each $f_i : T \to R[X]$ has continuous coefficients, then for each $j$
the coefficient $t \mapsto [X^j] \prod_{i \in s} f_i(t)$ is continuous. -/
theorem continuous_coeff_prod (s : Finset ι) {f : ι → T → R[X]}
    (hf : ∀ i, ∀ j, Continuous fun t => (f i t).coeff j) :
    ∀ j, Continuous fun t => (∏ i ∈ s, f i t).coeff j := by
  classical
  induction s using Finset.induction with
  | empty => intro j; simp only [Finset.prod_empty]; exact continuous_const
  | insert a s ha ih =>
      intro j; simp only [Finset.prod_insert ha]; exact continuous_coeff_mul (hf a) ih j

/-- Let $R$ be a commutative topological ring, let $T$ be a topological space, and let
$\alpha : T \to R$ be continuous. Then for each $j$ the coefficient
$t \mapsto [X^j]\,(X - \alpha(t))$ is continuous. -/
theorem continuous_coeff_X_sub_C {α : T → R} (hα : Continuous α) (j : ℕ) :
    Continuous fun t => ((X : R[X]) - C (α t)).coeff j := by
  simp only [coeff_sub, coeff_C]
  split_ifs with h
  · exact continuous_const.sub hα
  · exact continuous_const.sub continuous_const

/-- Let $R$ be a commutative topological ring and let $\iota$ be finite. Then for each $j$ the
coefficient $\alpha \mapsto [X^j] \prod_{i \in \iota} (X - \alpha_i)$ is a continuous function
on $R^\iota$: the coefficients of the monic polynomial with prescribed roots depend continuously
on the roots. -/
theorem continuous_coeff_prod_X_sub_C [Fintype ι] (j : ℕ) :
    Continuous fun α : ι → R => (∏ i, (X - C (α i))).coeff j :=
  continuous_coeff_prod _ (fun i => continuous_coeff_X_sub_C (continuous_apply i)) j

end Continuity

end Polynomial

/-- Let $R$ be a commutative topological ring, let $T$ be a topological space, and let
$M : T \to R^{\iota \times \iota}$ be continuous, with $\iota$ finite. Then for each $j$ the
coefficient $t \mapsto [X^j] \chi_{M(t)}$ of the characteristic polynomial is continuous.

The coefficients are polynomials in the entries of the matrix, by the Leibniz expansion of the
determinant of `Matrix.charmatrix`. -/
theorem Matrix.continuous_coeff_charpoly {R T ι : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [TopologicalSpace T] [Fintype ι] [DecidableEq ι]
    {M : T → Matrix ι ι R} (hM : Continuous M) (j : ℕ) :
    Continuous fun t => (M t).charpoly.coeff j := by
  have hentry : ∀ (a b : ι) (k : ℕ), Continuous fun t => (charmatrix (M t) a b).coeff k := by
    intro a b k
    by_cases h : a = b
    · subst h
      simpa only [Matrix.charmatrix_apply_eq] using
        Polynomial.continuous_coeff_X_sub_C (hM.matrix_elem a a) k
    · simp only [Matrix.charmatrix_apply_ne _ _ _ h, Polynomial.coeff_neg, Polynomial.coeff_C]
      split_ifs
      · exact (hM.matrix_elem a b).neg
      · exact continuous_const
  simp only [Matrix.charpoly, Matrix.det_apply', Polynomial.finsetSum_coeff]
  refine continuous_finsetSum _ fun σ _ => ?_
  exact Polynomial.continuous_coeff_mul (fun _ => continuous_const)
    (Polynomial.continuous_coeff_prod Finset.univ fun i k => hentry (σ i) i k) j

namespace Polynomial

variable {R T : Type*} [CommRing R] [IsDomain R] [TopologicalSpace R] [IsTopologicalRing R]
  [T2Space R] [TopologicalSpace T]

/-- **The number of roots in a compact set is constant along a connected family.** Let $R$ be an
integral domain with a Hausdorff ring topology, and let $T$ be a preconnected topological space.
Let $S, S' \subseteq R$ be compact and disjoint. Let $p : T \to R[X]$ be a family of polynomials
with continuous coefficients $t \mapsto [X^j]\, p(t)$. Assume that for every $t \in T$ the
polynomial $p(t)$ is monic of degree $n$, has $n$ roots counted with multiplicity, and has all
its roots in $S \cup S'$. Then for all $t_0, t_1 \in T$,
$$N_S(p(t_0)) = N_S(p(t_1)).$$

No hypothesis separates the roots from each other or requires them to be simple. Multiple roots
can split up and merge as $t$ varies; only their total multiplicity in $S$ is constant. The
proof is the compactness argument of the module documentation. It uses no complex analysis, and
$S$ can be any compact set. -/
theorem countRootsIn_eq_of_preconnected [PreconnectedSpace T]
    {S S' : Set R} (hS : IsCompact S) (hS' : IsCompact S') (hSS' : Disjoint S S')
    {n : ℕ} {p : T → R[X]} (hm : ∀ t, (p t).Monic) (hd : ∀ t, (p t).natDegree = n)
    (hcard : ∀ t, Multiset.card (p t).roots = n)
    (hsub : ∀ t, ∀ z ∈ (p t).roots, z ∈ S ∪ S')
    (hcont : ∀ j, Continuous fun t => (p t).coeff j) (t₀ t₁ : T) :
    (p t₀).countRootsIn S = (p t₁).countRootsIn S := by
  classical
  set c : T → ℕ → R := fun t j => (p t).coeff j with hc
  have hcc : Continuous c := continuous_pi hcont
  set Φ : (Fin n → R) → ℕ → R := fun α j => (∏ i, (X - C (α i))).coeff j with hΦ
  have hΦc : Continuous Φ := continuous_pi fun j => continuous_coeff_prod_X_sub_C j
  -- the tuples with `α i ∈ S` exactly for `i ∈ J` form a compact box, so its image is closed
  have hPclosed : ∀ J : Finset (Fin n),
      IsClosed (Φ '' (Set.univ.pi fun i => if i ∈ J then S else S')) := fun J =>
    (IsCompact.image (isCompact_univ_pi fun i => by split_ifs; exacts [hS, hS']) hΦc).isClosed
  -- a coefficient sequence in that image has exactly `J.card` roots in `S`
  have hmem : ∀ (t : T) (J : Finset (Fin n)),
      c t ∈ Φ '' (Set.univ.pi fun i => if i ∈ J then S else S') →
      (p t).countRootsIn S = J.card := by
    rintro t J ⟨α, hα, hΦα⟩
    have hpe : p t = ∏ i, (X - C (α i)) := Polynomial.ext fun j => congrFun hΦα.symm j
    have hJ : (Finset.univ.filter fun i => α i ∈ S) = J := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hi := hα i (Set.mem_univ i)
      refine ⟨fun hiS => by_contra fun hiJ => ?_, fun hiJ => by simpa [hiJ] using hi⟩
      simp only [hiJ, ite_false] at hi
      exact Set.disjoint_left.mp hSS' hiS hi
    rw [hpe, countRootsIn_prod_univ_X_sub_C, hJ]
  -- and conversely every member of the family lies in one such image
  have hmem' : ∀ t : T, ∃ J : Finset (Fin n), J.card = (p t).countRootsIn S ∧
      c t ∈ Φ '' (Set.univ.pi fun i => if i ∈ J then S else S') := by
    intro t
    obtain ⟨α, hpe, hαroots⟩ := exists_eq_prod_X_sub_C (hm t) (hd t) (hcard t)
    refine ⟨Finset.univ.filter fun i => α i ∈ S, by rw [hpe, countRootsIn_prod_univ_X_sub_C],
      α, fun i _ => ?_, ?_⟩
    · by_cases hi : α i ∈ S
      · simp [hi]
      · have hmem2 : α i ∈ S ∪ S' := hsub t (α i) (by
          rw [← hαroots]; exact Multiset.mem_map_of_mem _ (Finset.mem_val.mpr (Finset.mem_univ i)))
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hi, ite_false]
        exact hmem2.resolve_left hi
    · funext j; simp only [hc, hΦ, hpe]
  -- hence every level set of the root count is closed
  have hclosed : ∀ k, IsClosed {t | (p t).countRootsIn S = k} := by
    intro k
    have heq : {t | (p t).countRootsIn S = k}
        = ⋃ J ∈ {J : Finset (Fin n) | J.card = k},
            c ⁻¹' (Φ '' (Set.univ.pi fun i => if i ∈ J then S else S')) := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage, exists_prop]
      refine ⟨fun h => ?_, fun ⟨J, hJ, hJm⟩ => by rw [hmem t J hJm, hJ]⟩
      obtain ⟨J, hJ, hJm⟩ := hmem' t
      exact ⟨J, hJ.trans h, hJm⟩
    rw [heq]
    exact Set.Finite.isClosed_biUnion (Set.toFinite _) fun J _ => (hPclosed J).preimage hcc
  have hle : ∀ t, (p t).countRootsIn S ≤ n := fun t =>
    (countRootsIn_le_card_roots S (p t)).trans_eq (hcard t)
  -- there are at most `n + 1` level sets, so each of them is open as well
  have hclopen : IsClopen {t | (p t).countRootsIn S = (p t₀).countRootsIn S} := by
    refine ⟨hclosed _, ?_⟩
    rw [← isClosed_compl_iff]
    have heq : {t | (p t).countRootsIn S = (p t₀).countRootsIn S}ᶜ
        = ⋃ k ∈ {k : ℕ | k ≤ n ∧ k ≠ (p t₀).countRootsIn S}, {t | (p t).countRootsIn S = k} := by
      ext t
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
      exact ⟨fun h => ⟨_, ⟨hle t, h⟩, rfl⟩, fun ⟨k, hk, hkt⟩ => hkt ▸ hk.2⟩
    rw [heq]
    exact Set.Finite.isClosed_biUnion
      ((Set.finite_le_nat n).subset fun k hk => hk.1) fun k _ => hclosed k
  have huniv := hclopen.eq_univ ⟨t₀, rfl⟩
  have ht₁ : t₁ ∈ {t | (p t).countRootsIn S = (p t₀).countRootsIn S} := by rw [huniv]; trivial
  exact ht₁.symm

end Polynomial

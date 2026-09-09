import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Instances.Matrix

/-!
# Continuity of polynomial coefficients, and the root count in a compact set

A polynomial has no topology of its own in Mathlib, but a *family* of polynomials
`p : T → R[X]` can still be asked to depend continuously on its parameter: the right condition is
that every coefficient `t ↦ (p t).coeff j` be continuous.  This file develops that condition —
it is stable under products, so it holds for `∏ i, (X - C (α i))` in the roots `α` and for the
characteristic polynomial in the entries of the matrix — and uses it to prove the main result:

`Polynomial.countRootsIn_eq_of_preconnected`, **the number of roots in a compact set is constant
along a connected family**, provided the roots never leave the union of two disjoint compact sets.

## The counting argument

`Polynomial.countRootsIn S p` is the number of roots of `p` lying in `S`, counted with
multiplicity.  Fix two disjoint compact sets `S`, `S'` and let `p` run over the monic degree-`n`
polynomials that split with all their roots in `S ∪ S'`.  Every such polynomial is
`∏ i, (X - C (α i))` for a tuple `α : Fin n → R`, and for `J ⊆ Fin n` the tuples with `α i ∈ S`
exactly for `i ∈ J` form the compact box `Set.univ.pi fun i => if i ∈ J then S else S'`.  Its
image under the (continuous) coefficient map is therefore compact, hence closed; and since a
polynomial determines its multiset of roots, membership in that image pins the root count down to
`J.card`.  So each level set `{t | countRootsIn S (p t) = k}` is closed; there are at most `n + 1`
nonempty ones, and finitely many disjoint closed sets covering a space are all open.
Connectedness of the parameter space finishes the argument.

`Matrix.continuous_coeff_charpoly` is here rather than beside the other matrix topology because it
is a member of the same family — the coefficients of a polynomial assembled from data depend
continuously on the data — and its proof is one application of `Polynomial.continuous_coeff_prod`
to the Leibniz expansion.

This replaces the usual complex-analytic route (Rouché's theorem, or the argument principle applied
to a contour around `S`).  Nothing here is complex-analytic — `R` is any topological integral
domain — and, unlike a contour argument, nothing asks `S` to be a disc or to have a tractable
boundary.  That matters for the intended application, the Gershgorin disc counting theorem (Saad,
*Numerical Methods for Large Eigenvalue Problems*, 2nd edition, Theorem 3.12), where `S` is a union
of possibly overlapping discs.
-/

open Finset Polynomial

namespace Polynomial

section CountRootsIn

variable {R : Type*} [CommRing R] [IsDomain R]

open scoped Classical in
/-- The number of roots of `p` lying in the set `S`, counted with multiplicity.

For the characteristic polynomial of a matrix this is the number of eigenvalues in `S` counted with
algebraic multiplicity. -/
noncomputable def countRootsIn (S : Set R) (p : R[X]) : ℕ :=
  Multiset.card (p.roots.filter (· ∈ S))

/-- The roots in `S` are among all the roots, so there are at most as many of them. -/
theorem countRootsIn_le_card_roots (S : Set R) (p : R[X]) :
    p.countRootsIn S ≤ Multiset.card p.roots := by
  classical exact Multiset.card_le_card (Multiset.filter_le _ _)

/-- The roots of `∏ i, (X - C (α i))`, as a multiset, are the values of the tuple `α`. -/
theorem roots_prod_univ_X_sub_C {ι : Type*} [Fintype ι] (α : ι → R) :
    (∏ i, (X - C (α i))).roots = Multiset.map α Finset.univ.val := by
  rw [Finset.prod_eq_multiset_prod,
    show (Multiset.map (fun i => X - C (α i)) Finset.univ.val)
      = Multiset.map (fun a => X - C a) (Multiset.map α Finset.univ.val) by
        rw [Multiset.map_map]; rfl]
  exact roots_multiset_prod_X_sub_C _

open scoped Classical in
/-- The roots of `∏ i, (X - C (α i))` in `S` are counted by the indices `i` with `α i ∈ S`. -/
theorem countRootsIn_prod_univ_X_sub_C {ι : Type*} [Fintype ι] (S : Set R) (α : ι → R) :
    (∏ i, (X - C (α i))).countRootsIn S = (Finset.univ.filter fun i => α i ∈ S).card := by
  rw [countRootsIn, roots_prod_univ_X_sub_C, Multiset.filter_map, Multiset.card_map]
  rfl

/-- A monic polynomial of degree `n` with `n` roots is `∏ i, (X - C (α i))` for a tuple
`α : Fin n → R` enumerating its roots.  This is the tuple form of
`Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq`, and it is what makes the roots of
such a polynomial available as a *point* of a compact box. -/
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

/-- Coefficientwise continuity is stable under multiplication: each coefficient of a product is a
finite sum of products of coefficients. -/
theorem continuous_coeff_mul {p q : T → R[X]}
    (hp : ∀ j, Continuous fun t => (p t).coeff j) (hq : ∀ j, Continuous fun t => (q t).coeff j)
    (j : ℕ) : Continuous fun t => (p t * q t).coeff j := by
  simp only [Polynomial.coeff_mul]
  exact continuous_finsetSum _ fun x _ => (hp x.1).mul (hq x.2)

/-- Coefficientwise continuity is stable under finite products. -/
theorem continuous_coeff_prod (s : Finset ι) {f : ι → T → R[X]}
    (hf : ∀ i, ∀ j, Continuous fun t => (f i t).coeff j) :
    ∀ j, Continuous fun t => (∏ i ∈ s, f i t).coeff j := by
  classical
  induction s using Finset.induction with
  | empty => intro j; simp only [Finset.prod_empty]; exact continuous_const
  | insert a s ha ih =>
      intro j; simp only [Finset.prod_insert ha]; exact continuous_coeff_mul (hf a) ih j

/-- The coefficients of `X - C α` depend continuously on `α`. -/
theorem continuous_coeff_X_sub_C {α : T → R} (hα : Continuous α) (j : ℕ) :
    Continuous fun t => ((X : R[X]) - C (α t)).coeff j := by
  simp only [coeff_sub, coeff_C]
  split_ifs with h
  · exact continuous_const.sub hα
  · exact continuous_const.sub continuous_const

/-- The coefficients of the monic polynomial with prescribed roots depend continuously on the
roots. -/
theorem continuous_coeff_prod_X_sub_C [Fintype ι] (j : ℕ) :
    Continuous fun α : ι → R => (∏ i, (X - C (α i))).coeff j :=
  continuous_coeff_prod _ (fun i => continuous_coeff_X_sub_C (continuous_apply i)) j

end Continuity

end Polynomial

/-- The coefficients of the characteristic polynomial depend continuously on the matrix: they are
polynomials in its entries, by the Leibniz expansion of the determinant of `charmatrix`. -/
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

/-- **The number of roots in a compact set is constant along a connected family.**

Let `S` and `S'` be disjoint compact sets and let `p t` be a family of monic polynomials of degree
`n`, depending continuously on `t` in the sense that every coefficient does, each of which splits
with all `n` of its roots in `S ∪ S'`.  Then the number of roots in `S`, counted with multiplicity,
is the same for all `t`.

No hypothesis separates the roots from one another or asks them to be simple: multiple roots may
split up and merge as `t` varies, and only their total multiplicity inside `S` is claimed to be
constant.  The proof is the compactness argument described in the module documentation; it uses no
complex analysis, and `S` may be any compact set. -/
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

import Mathlib.Analysis.Calculus.Deriv.Inv
import Numlib.Approximation.DividedDifference
import Numlib.Approximation.Hermite

/-!
# The Newton form of the interpolating polynomial

The Newton divided difference `f[x₀, …, x_m]` is `DividedDifference.newton` of
`Numlib/Approximation/DividedDifference`, in its explicit symmetric form
`∑ᵢ f(xᵢ) / ∏_{j ≠ i} (xᵢ - xⱼ)`, together with `newton_eq_coeff` (it is the coefficient of `X^m`
in the interpolant) and the divided-difference error form `sub_eval_interpolate_eq_newton`. This
module is the rest of the classical theory of that object, [quarteroni2000numerical] §8.2 and
[kress1998numerical] §8.2: the Newton form of the interpolant, the recursion in the nodes, the
algebraic rules (symmetry, linearity, Leibniz), the mean-value form `f[x₀, …, x_m] = f^{(m)}(ξ)/m!`,
the divided differences of `t ↦ 1/(z - t)` (the engine of Runge-type divergence arguments), the
derivative of a divided difference in its last argument, and confluent divided differences at
repeated nodes, which B-splines with coincident knots need.

## The divided difference over a finite index set

The classical statements are indexed by `Fin (m + 1)`, but the arguments behind them — adding a
node, deleting one, splitting the node set into a prefix and a suffix — are cleaner on an
arbitrary finite set of indices, where they need no dependent types. So the module first develops
`DividedDifference.newtonOn s v f`, the divided difference of `f` at the nodes `v i`, `i ∈ s`, over
any field, in the setting of Mathlib's `Lagrange.interpolate s v`; `newton f v` is
`newtonOn Finset.univ v f` by definition. The Newton form over a linearly ordered index set
(`interpolate_eq_sum_newtonOn_mul_nodal`), the recursion in two arbitrary nodes
(`newtonOn_eq_sub_div`) and the Leibniz formula (`newtonOn_mul`) are proved there, and the
`Fin`-indexed statements are read off through the reindexing lemma `newtonOn_map`.

## Conventions

Nodes are `v : Fin (m + 1) → ℝ`; `Fin.init v`, `Fin.tail v` and `Fin.snoc v t` drop the last, drop
the first and append a node, so that the recursion reads
`newton f v = (newton f (Fin.tail v) - newton f (Fin.init v)) / (v (Fin.last _) - v 0)`. The
truncations `prefixNodes v k = (x₀, …, x_k)` and `suffixNodes v k = (x_k, …, x_m)` carry the Newton
sum and the Leibniz formula, and `prefixNodal v k = ∏_{j < k} (X - x_j)` is the nodal polynomial
`ω_k` of the first `k` nodes. The interpolant is Mathlib's
`Lagrange.interpolate Finset.univ v (f ∘ v)` and the nodal polynomial is
`Lagrange.nodal Finset.univ v`, as in `DividedDifference`.

## Main results

* `interpolate_snoc_eq` and `eval_interpolate_snoc_sub` — adding a node adds
  `f[x₀, …, x_m, t] ω_{m+1}` to the interpolant, and the new coefficient is the book's definition
  `(f(t) - Π_m f(t)) / ω_{m+1}(t)` of the divided difference.
* `interpolate_eq_sum_newton_mul_prefixNodal` — the **Newton divided difference formula**
  `Π_m f = ∑_k f[x₀, …, x_k] ω_k`.
* `newton_succ` — the recursion `f[x₀, …, x_m] = (f[x₁, …, x_m] - f[x₀, …, x_{m-1}]) / (x_m - x₀)`.
* `newton_comp_perm`, `newton_add`, `newton_smul`, `newton_mul` — symmetry, linearity and the
  **Leibniz formula** `(gh)[x₀, …, x_m] = ∑_j g[x₀, …, x_j] h[x_j, …, x_m]`.
* `newton_eval_eq_coeff` and `newton_eq_zero_of_degree_lt` — on a polynomial of degree `≤ m` the
  divided difference reads off the coefficient of `X^m`, and it vanishes on `𝒫_{m-1}`.
* `exists_newton_eq_iteratedDeriv_div` and `abs_newton_le` — the **mean-value form**
  `f[x₀, …, x_m] = f^{(m)}(ξ)/m!` and the bound it gives.
* `newton_inv_sub` — `f[x₀, …, x_m] = 1/∏ᵢ (z - xᵢ)` for `f(t) = 1/(z - t)`.
* `hasDerivAt_newton_snoc` — the derivative of `x ↦ f[x₀, …, x_n, x]` is the confluent divided
  difference `f[x₀, …, x_n, x, x]`, the top coefficient of the Hermite interpolant with a double
  node at `x`.
* `confluent`, `confluent_eq_newton`, `confluent_const` — confluent divided differences at
  repeated nodes.

## References

[quarteroni2000numerical] §8.2 and Remark 8.3; [kress1998numerical] §8.2; the Leibniz formula is
Steffensen's, *Interpolation*, §19. The book prints the value of the `n`-th divided difference at
`n + 1` coincident nodes as `f^{(n+1)}(x₀)/(n+1)!`; the correct value `f^{(n)}(x₀)/n!` is used.
-/

open Polynomial Finset

/-- The top iterated derivative of a polynomial of degree at most `k` is the constant
`k! · (coefficient of X^k)`. -/
theorem Polynomial.iterate_derivative_eq_C_of_natDegree_le {R : Type*} [CommSemiring R] {p : R[X]}
    {k : ℕ} (hp : p.natDegree ≤ k) :
    derivative^[k] p = C ((k.factorial : R) * p.coeff k) := by
  have h0 : (derivative^[k] p).natDegree = 0 :=
    Nat.le_zero.mp ((natDegree_iterate_derivative p k).trans (by omega))
  rw [eq_C_of_natDegree_eq_zero h0, coeff_iterate_derivative, zero_add, Nat.descFactorial_self,
    nsmul_eq_mul]

/-- Reindexing a Lagrange interpolant along an embedding of the index set. -/
theorem Lagrange.interpolate_map {F : Type*} [Field F] {ι κ : Type*} [DecidableEq ι]
    [DecidableEq κ] (e : κ ↪ ι) (t : Finset κ) (v r : ι → F) :
    Lagrange.interpolate (t.map e) v r = Lagrange.interpolate t (v ∘ e) (r ∘ e) := by
  simp only [Lagrange.interpolate_apply, Finset.sum_map, Function.comp_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  simp only [Lagrange.basis, ← Finset.map_erase, Finset.prod_map]
  rfl

/-- Reindexing a nodal polynomial along an embedding of the index set. -/
theorem Lagrange.nodal_map {R : Type*} [CommRing R] {ι κ : Type*} (e : κ ↪ ι) (t : Finset κ)
    (v : ι → R) : Lagrange.nodal (t.map e) v = Lagrange.nodal t (v ∘ e) := by
  simp only [Lagrange.nodal, Finset.prod_map]
  rfl

/-- **Adding a node to a Lagrange interpolant**: the interpolant at `insert a t` is the interpolant
at `t` plus its own coefficient of `X^{#t}` times the nodal polynomial of `t`. The difference of the
two interpolants vanishes at the nodes of `t` and has degree at most `#t`, so it is that multiple
of the nodal polynomial. -/
theorem Lagrange.interpolate_insert_eq {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]
    {v : ι → F} {a : ι} {t : Finset ι} (hvs : Set.InjOn v ((insert a t : Finset ι) : Set ι))
    (ha : a ∉ t) (r : ι → F) :
    Lagrange.interpolate (insert a t) v r = Lagrange.interpolate t v r
      + C ((Lagrange.interpolate (insert a t) v r).coeff t.card) * Lagrange.nodal t v := by
  set P := Lagrange.interpolate (insert a t) v r with hP
  set c := P.coeff t.card with hc
  have hvt : Set.InjOn v t := hvs.mono (Finset.coe_subset.mpr (subset_insert a t))
  have hcard : (insert a t).card = t.card + 1 := Finset.card_insert_of_notMem ha
  have hPdeg : P.degree < ((t.card + 1 : ℕ) : WithBot ℕ) := by
    have := Lagrange.degree_interpolate_lt r hvs
    rwa [hcard] at this
  have hωdeg : (Lagrange.nodal t v).degree = (t.card : WithBot ℕ) := Lagrange.degree_nodal
  have hωtop : (Lagrange.nodal t v).coeff t.card = 1 := by
    have h := (Lagrange.nodal_monic (s := t) (v := v)).coeff_natDegree
    rwa [Lagrange.natDegree_nodal] at h
  -- subtracting `c ω` drops the degree below `#t`
  have hdeg : (P - C c * Lagrange.nodal t v).degree < (t.card : WithBot ℕ) := by
    refine (Polynomial.degree_lt_iff_coeff_zero _ _).2 fun k hk => ?_
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    rcases eq_or_lt_of_le hk with rfl | hlt
    · rw [hωtop, mul_one, sub_self]
    · rw [Polynomial.coeff_eq_zero_of_degree_lt (hPdeg.trans_le (by exact_mod_cast hlt)),
        Polynomial.coeff_eq_zero_of_degree_lt (hωdeg ▸ (by exact_mod_cast hlt)), mul_zero,
        sub_zero]
  have hval : ∀ i ∈ t, (P - C c * Lagrange.nodal t v).eval (v i) = r i := by
    intro i hi
    rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Lagrange.eval_nodal_at_node hi, mul_zero, sub_zero, hP,
      Lagrange.eval_interpolate_at_node _ hvs (mem_insert_of_mem hi)]
  have := Lagrange.eq_interpolate_of_eval_eq r hvt hdeg hval
  linear_combination this

namespace DividedDifference

/-! ### The divided difference over a finite index set -/

section Finset

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → F}

/-- **The Newton divided difference over a finite index set**: `f[v i : i ∈ s]`, in the explicit
form `∑_{i ∈ s} f(v i) / ∏_{j ∈ s, j ≠ i} (v i - v j)`. For injective nodes it is the coefficient of
`X^{#s - 1}` in `Lagrange.interpolate s v (f ∘ v)` (`DividedDifference.newtonOn_eq_coeff`);
`DividedDifference.newton f v` is the case `s = Finset.univ` of a `Fin`-indexed family. -/
noncomputable def newtonOn (s : Finset ι) (v : ι → F) (f : F → F) : F :=
  ∑ i ∈ s, f (v i) / ∏ j ∈ s.erase i, (v i - v j)

/-- The `Fin`-indexed divided difference is the one over the full index set. -/
theorem newton_eq_newtonOn {m : ℕ} (f : ℝ → ℝ) (v : Fin (m + 1) → ℝ) :
    newton f v = newtonOn univ v f := rfl

@[simp]
theorem newtonOn_empty (v : ι → F) (f : F → F) : newtonOn ∅ v f = 0 := by
  simp [newtonOn]

/-- The divided difference at a single node is the value of the function there. -/
@[simp]
theorem newtonOn_singleton (v : ι → F) (f : F → F) (i : ι) : newtonOn {i} v f = f (v i) := by
  simp [newtonOn]

/-- Reindexing the nodes along an embedding of the index set. -/
theorem newtonOn_map {κ : Type*} [DecidableEq κ] (e : κ ↪ ι) (t : Finset κ) (v : ι → F)
    (f : F → F) : newtonOn (t.map e) v f = newtonOn t (v ∘ e) f := by
  simp only [newtonOn, Finset.sum_map, Function.comp_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.map_erase, Finset.prod_map]

/-- **The divided difference is the top coefficient of the interpolant**: for injective nodes,
`newtonOn s v f` is the coefficient of `X^{#s - 1}` in `Lagrange.interpolate s v (f ∘ v)`. This is
`Lagrange.coeff_eq_sum` read backwards. -/
theorem newtonOn_eq_coeff (hvs : Set.InjOn v s) (f : F → F) :
    newtonOn s v f = (Lagrange.interpolate s v fun i => f (v i)).coeff (s.card - 1) := by
  rw [Lagrange.coeff_eq_sum hvs (Lagrange.degree_interpolate_lt _ hvs)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Lagrange.eval_interpolate_at_node _ hvs hi]

/-- On a polynomial of degree `< #s` the divided difference reads off the coefficient of
`X^{#s - 1}`. -/
theorem newtonOn_eval_eq_coeff (hvs : Set.InjOn v s) {p : F[X]} (hp : p.degree < s.card) :
    newtonOn s v (fun t => p.eval t) = p.coeff (s.card - 1) := by
  rw [newtonOn_eq_coeff hvs, ← Lagrange.eq_interpolate hvs hp]

/-- Divided differences are additive in the function. -/
theorem newtonOn_add (s : Finset ι) (v : ι → F) (f g : F → F) :
    newtonOn s v (fun t => f t + g t) = newtonOn s v f + newtonOn s v g := by
  simp only [newtonOn, add_div, Finset.sum_add_distrib]

/-- Divided differences are homogeneous in the function. -/
theorem newtonOn_smul (s : Finset ι) (v : ι → F) (c : F) (f : F → F) :
    newtonOn s v (fun t => c * f t) = c * newtonOn s v f := by
  simp only [newtonOn, Finset.mul_sum, mul_div_assoc]

/-- **The recursion in two nodes**: deleting either of two distinct nodes `v i`, `v j`,
`f[S] = (f[S ∖ {v j}] - f[S ∖ {v i}]) / (v i - v j)`. It is the coefficient of `X^{#s - 1}` in
Mathlib's `Lagrange.interpolate_eq_add_interpolate_erase`. -/
theorem newtonOn_eq_sub_div (hvs : Set.InjOn v s) (f : F → F) {i j : ι} (hi : i ∈ s)
    (hj : j ∈ s) (hij : i ≠ j) :
    newtonOn s v f = (newtonOn (s.erase j) v f - newtonOn (s.erase i) v f) / (v i - v j) := by
  have hcard : 2 ≤ s.card := Finset.one_lt_card.mpr ⟨i, hi, j, hj, hij⟩
  obtain ⟨d, hd⟩ : ∃ d, s.card = d + 1 + 1 := ⟨s.card - 2, by omega⟩
  have hvij : v i - v j ≠ 0 := sub_ne_zero.mpr fun h => hij (hvs hi hj h)
  have hvji : v j - v i ≠ 0 := sub_ne_zero.mpr fun h => hij (hvs hi hj h.symm)
  -- the coefficient of `X^{d+1}` in the product of an interpolant with a linear factor
  have key : ∀ (k a b : ι), k ∈ s → v a - v b ≠ 0 →
      ((Lagrange.interpolate (s.erase k) v fun l => f (v l)) *
        Lagrange.basisDivisor (v a) (v b)).coeff (d + 1)
        = (v a - v b)⁻¹ * newtonOn (s.erase k) v f := by
    intro k a b hk _
    have hvsk : Set.InjOn v (s.erase k) := hvs.mono (Finset.coe_subset.mpr (erase_subset k s))
    have hcardk : (s.erase k).card = d + 1 := by
      rw [Finset.card_erase_of_mem hk, hd, Nat.add_sub_cancel]
    have hdeg : (Lagrange.interpolate (s.erase k) v fun l => f (v l)).degree
        < ((d + 1 : ℕ) : WithBot ℕ) := by
      have := Lagrange.degree_interpolate_lt (fun l => f (v l)) hvsk
      rwa [hcardk] at this
    rw [Lagrange.basisDivisor, mul_left_comm, Polynomial.coeff_C_mul,
      Polynomial.coeff_mul_X_sub_C, Polynomial.coeff_eq_zero_of_degree_lt hdeg, zero_mul,
      sub_zero, newtonOn_eq_coeff hvsk, hcardk, Nat.add_sub_cancel]
  have h := congrArg (fun p : F[X] => p.coeff (d + 1))
    (Lagrange.interpolate_eq_add_interpolate_erase (fun l => f (v l)) hvs hi hj hij)
  simp only [Polynomial.coeff_add] at h
  rw [key j i j hj hvij, key i j i hi hvji] at h
  rw [newtonOn_eq_coeff hvs, hd, Nat.add_sub_cancel, h]
  field_simp
  ring

/-- **Adding a node** (the Newton step): for `a ∉ t` and injective nodes,
`Π_{insert a t} f = Π_t f + f[v i : i ∈ insert a t] · nodal t`. -/
theorem interpolate_insert_eq_newtonOn {a : ι} {t : Finset ι}
    (hvs : Set.InjOn v ((insert a t : Finset ι) : Set ι)) (ha : a ∉ t) (f : F → F) :
    (Lagrange.interpolate (insert a t) v fun i => f (v i))
      = (Lagrange.interpolate t v fun i => f (v i))
        + C (newtonOn (insert a t) v f) * Lagrange.nodal t v := by
  rw [newtonOn_eq_coeff hvs, Finset.card_insert_of_notMem ha, Nat.add_sub_cancel]
  exact Lagrange.interpolate_insert_eq hvs ha _

/-- **The Newton divided difference formula over a linearly ordered index set**: for injective
nodes, `Π_s f = ∑_{j ∈ s} f[v i : i ∈ s, i ≤ j] · ∏_{i ∈ s, i < j} (X - v i)`. -/
theorem interpolate_eq_sum_newtonOn_mul_nodal [LinearOrder ι] (hvs : Set.InjOn v s)
    (f : F → F) :
    (Lagrange.interpolate s v fun i => f (v i))
      = ∑ j ∈ s, C (newtonOn (s.filter (· ≤ j)) v f) * Lagrange.nodal (s.filter (· < j)) v := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a t hlt ih =>
    have ha : a ∉ t := fun h => lt_irrefl a (hlt a h)
    have hvt : Set.InjOn v t := hvs.mono (Finset.coe_subset.mpr (subset_insert a t))
    rw [interpolate_insert_eq_newtonOn hvs ha, ih hvt, Finset.sum_insert ha, add_comm]
    congr 1
    · rw [Finset.filter_insert, ite_eq_left le_rfl, Finset.filter_insert,
        ite_eq_right (lt_irrefl a), Finset.filter_true_of_mem fun x hx => (hlt x hx).le,
        Finset.filter_true_of_mem fun x hx => hlt x hx]
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.filter_insert, ite_eq_right (not_le.mpr (hlt j hj)), Finset.filter_insert,
        ite_eq_right (not_lt.mpr (hlt j hj).le)]

/-- **The reversed Newton formula**: the same expansion built from the largest node down,
`Π_s f = ∑_{j ∈ s} f[v i : i ∈ s, j ≤ i] · ∏_{i ∈ s, j < i} (X - v i)`. -/
theorem interpolate_eq_sum_newtonOn_mul_nodal' [LinearOrder ι] (hvs : Set.InjOn v s)
    (f : F → F) :
    (Lagrange.interpolate s v fun i => f (v i))
      = ∑ j ∈ s, C (newtonOn (s.filter (j ≤ ·)) v f) * Lagrange.nodal (s.filter (j < ·)) v := by
  induction s using Finset.induction_on_min with
  | empty => simp
  | insert a t hlt ih =>
    have ha : a ∉ t := fun h => lt_irrefl a (hlt a h)
    have hvt : Set.InjOn v t := hvs.mono (Finset.coe_subset.mpr (subset_insert a t))
    rw [interpolate_insert_eq_newtonOn hvs ha, ih hvt, Finset.sum_insert ha, add_comm]
    congr 1
    · rw [Finset.filter_insert, ite_eq_left le_rfl, Finset.filter_insert,
        ite_eq_right (lt_irrefl a), Finset.filter_true_of_mem fun x hx => (hlt x hx).le,
        Finset.filter_true_of_mem fun x hx => hlt x hx]
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.filter_insert, ite_eq_right (not_le.mpr (hlt j hj)), Finset.filter_insert,
        ite_eq_right (not_lt.mpr (hlt j hj).le)]

/-- The nodes below `j` and the nodes above `l ≥ j` all differ from `j`. -/
private theorem filter_lt_union_filter_lt_subset [LinearOrder ι] {j l : ι} (hjl : j ≤ l) :
    s.filter (· < j) ∪ s.filter (l < ·) ⊆ s.erase j := by
  intro i hi
  rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at hi
  rw [Finset.mem_erase]
  rcases hi with ⟨his, hij⟩ | ⟨his, hli⟩
  · exact ⟨hij.ne, his⟩
  · exact ⟨(hjl.trans_lt hli).ne', his⟩

omit [DecidableEq ι] in
private theorem disjoint_filter_lt_filter_lt [LinearOrder ι] {j l : ι} (hjl : j ≤ l) :
    Disjoint (s.filter (· < j)) (s.filter (l < ·)) := by
  rw [Finset.disjoint_filter]
  intro i _ hij hli
  exact absurd (hjl.trans_lt hli) (not_lt.mpr hij.le)

/-- **The Leibniz formula over a linearly ordered index set**: for injective nodes,
`(gh)[v i : i ∈ s] = ∑_{j ∈ s} g[v i : i ≤ j] · h[v i : j ≤ i]`.

Steffensen's proof: multiplying the Newton form of `Π_s g` by the reversed Newton form of `Π_s h`
gives a double sum of terms `g[…, v j] h[v l, …] ω_j ω'_l`; the terms with `j > l` vanish at every
node, and the rest form a polynomial of degree `< #s` taking the values `g h` at the nodes, hence
`Π_s (gh)`, whose top coefficient comes from the terms `j = l` alone. -/
theorem newtonOn_mul [LinearOrder ι] (hvs : Set.InjOn v s) (g h : F → F) :
    newtonOn s v (fun t => g t * h t)
      = ∑ j ∈ s, newtonOn (s.filter (· ≤ j)) v g * newtonOn (s.filter (j ≤ ·)) v h := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨d, hd⟩ : ∃ d, s.card = d + 1 := ⟨s.card - 1, by have := hne.card_pos; omega⟩
  set G : ι → F := fun j => newtonOn (s.filter (· ≤ j)) v g with hG
  set H : ι → F := fun l => newtonOn (s.filter (l ≤ ·)) v h with hH
  set ω : ι → F[X] := fun j => Lagrange.nodal (s.filter (· < j)) v with hω
  set ω' : ι → F[X] := fun l => Lagrange.nodal (s.filter (l < ·)) v with hω'
  -- the natural degrees of the products `ω j * ω' l`
  have hmonic : ∀ j l, (ω j * ω' l).Monic := fun j l =>
    Lagrange.nodal_monic.mul Lagrange.nodal_monic
  have hnat : ∀ j l, (ω j * ω' l).natDegree
      = (s.filter (· < j)).card + (s.filter (l < ·)).card := fun j l => by
    rw [Lagrange.nodal_monic.natDegree_mul Lagrange.nodal_monic, Lagrange.natDegree_nodal,
      Lagrange.natDegree_nodal]
  have herase : ∀ j ∈ s, (s.erase j).card = d := fun j hj => by
    rw [Finset.card_erase_of_mem hj, hd, Nat.add_sub_cancel]
  have hnat_le : ∀ j ∈ s, ∀ l, j ≤ l → (ω j * ω' l).natDegree ≤ d := by
    intro j hj l hjl
    rw [hnat, ← Finset.card_union_of_disjoint (disjoint_filter_lt_filter_lt hjl), ← herase j hj]
    exact Finset.card_le_card (filter_lt_union_filter_lt_subset hjl)
  have hnat_lt : ∀ j ∈ s, ∀ l ∈ s, j < l → (ω j * ω' l).natDegree < d := by
    intro j hj l hl hjl
    rw [hnat, ← Finset.card_union_of_disjoint (disjoint_filter_lt_filter_lt hjl.le), ← herase j hj]
    have hl' : l ∈ s.erase j := Finset.mem_erase.mpr ⟨hjl.ne', hl⟩
    have hsub : s.filter (· < j) ∪ s.filter (l < ·) ⊆ (s.erase j).erase l := by
      intro i hi
      rw [Finset.mem_erase]
      refine ⟨?_, filter_lt_union_filter_lt_subset hjl.le hi⟩
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at hi
      rcases hi with ⟨_, hij⟩ | ⟨_, hli⟩
      · exact (hij.trans hjl).ne
      · exact hli.ne'
    exact (Finset.card_le_card hsub).trans_lt (Finset.card_erase_lt_of_mem hl')
  have hnat_eq : ∀ j ∈ s, (ω j * ω' j).natDegree = d := by
    intro j hj
    rw [hnat, ← Finset.card_union_of_disjoint (disjoint_filter_lt_filter_lt le_rfl), ← herase j hj]
    congr 1
    refine le_antisymm (filter_lt_union_filter_lt_subset le_rfl) fun i hi => ?_
    rw [Finset.mem_erase] at hi
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases lt_or_gt_of_ne hi.1 with hlt | hlt
    · exact Or.inl ⟨hi.2, hlt⟩
    · exact Or.inr ⟨hi.2, hlt⟩
  -- the polynomial made of the terms `j ≤ l`
  set r : F[X] := ∑ j ∈ s, ∑ l ∈ s.filter (j ≤ ·), C (G j * H l) * (ω j * ω' l) with hr
  have hrdeg : r.degree < (s.card : WithBot ℕ) := by
    have hle : r.natDegree ≤ d := by
      refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
      refine natDegree_sum_le_of_forall_le _ _ fun l hl => ?_
      exact (natDegree_C_mul_le _ _).trans (hnat_le j hj l (Finset.mem_filter.mp hl).2)
    calc r.degree ≤ (d : WithBot ℕ) := degree_le_of_natDegree_le hle
      _ < ((d + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self d
      _ = _ := by rw [hd]
  -- the two Newton forms, and the values of `r` at the nodes
  have hp : (Lagrange.interpolate s v fun i => g (v i)) = ∑ j ∈ s, C (G j) * ω j :=
    interpolate_eq_sum_newtonOn_mul_nodal hvs g
  have hq : (Lagrange.interpolate s v fun i => h (v i)) = ∑ l ∈ s, C (H l) * ω' l :=
    interpolate_eq_sum_newtonOn_mul_nodal' hvs h
  have hrval : ∀ i ∈ s, r.eval (v i) = g (v i) * h (v i) := by
    intro i hi
    have hpi : (∑ j ∈ s, C (G j) * ω j).eval (v i) = g (v i) := by
      rw [← hp, Lagrange.eval_interpolate_at_node _ hvs hi]
    have hqi : (∑ l ∈ s, C (H l) * ω' l).eval (v i) = h (v i) := by
      rw [← hq, Lagrange.eval_interpolate_at_node _ hvs hi]
    rw [← hpi, ← hqi, hr, eval_finsetSum, eval_finsetSum, eval_finsetSum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [eval_finsetSum, Finset.sum_filter_of_ne]
    · refine Finset.sum_congr rfl fun l _ => ?_
      simp only [eval_mul, eval_C]
      ring
    · intro l _ hne
      by_contra hjl
      rw [not_le] at hjl
      apply hne
      simp only [eval_mul, eval_C, hω, hω']
      rcases lt_or_ge i j with hij | hji
      · rw [Lagrange.eval_nodal_at_node (Finset.mem_filter.mpr ⟨hi, hij⟩)]
        ring
      · rw [Lagrange.eval_nodal_at_node (Finset.mem_filter.mpr ⟨hi, hjl.trans_le hji⟩)]
        ring
  have hreq : r = Lagrange.interpolate s v fun i => g (v i) * h (v i) :=
    Lagrange.eq_interpolate_of_eval_eq _ hvs hrdeg hrval
  -- the top coefficient of `r` comes from the diagonal terms
  rw [newtonOn_eq_coeff hvs, ← hreq, hd, Nat.add_sub_cancel, hr, finsetSum_coeff]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [finsetSum_coeff, Finset.sum_eq_single_of_mem j (Finset.mem_filter.mpr ⟨hj, le_rfl⟩)]
  · rw [coeff_C_mul, ← hnat_eq j hj, (hmonic j j).coeff_natDegree, mul_one]
  · intro l hl hlj
    rw [Finset.mem_filter] at hl
    rw [coeff_C_mul,
      coeff_eq_zero_of_natDegree_lt (hnat_lt j hj l hl.1 (lt_of_le_of_ne hl.2 (Ne.symm hlj))),
      mul_zero]

/-- **Divided differences of a Cauchy kernel**: for `z` distinct from every node,
`f[v i : i ∈ s] = 1 / ∏_{i ∈ s} (z - v i)` for `f(t) = 1/(z - t)`. Induction on the node set with
the recursion `newtonOn_eq_sub_div`. -/
theorem newtonOn_inv_sub (hvs : Set.InjOn v s) (hne : s.Nonempty) {z : F}
    (hz : ∀ i ∈ s, z ≠ v i) :
    newtonOn s v (fun t => 1 / (z - t)) = 1 / ∏ i ∈ s, (z - v i) := by
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases hcard : s.card = 1
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard
      simp
    · obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp
        (lt_of_le_of_ne hne.card_pos (Ne.symm hcard))
      have hzi : z - v i ≠ 0 := sub_ne_zero.mpr (hz i hi)
      have hzj : z - v j ≠ 0 := sub_ne_zero.mpr (hz j hj)
      have hvij : v i - v j ≠ 0 := sub_ne_zero.mpr fun h => hij (hvs hi hj h)
      have hPi : ∏ k ∈ s.erase i, (z - v k) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun k hk => sub_ne_zero.mpr (hz k (mem_of_mem_erase hk))
      have hPj : ∏ k ∈ s.erase j, (z - v k) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun k hk => sub_ne_zero.mpr (hz k (mem_of_mem_erase hk))
      have hprod : (z - v i) * ∏ k ∈ s.erase i, (z - v k)
          = (z - v j) * ∏ k ∈ s.erase j, (z - v k) := by
        rw [Finset.mul_prod_erase s (fun k => z - v k) hi,
          Finset.mul_prod_erase s (fun k => z - v k) hj]
      rw [newtonOn_eq_sub_div hvs _ hi hj hij,
        ih (s.erase j) (Finset.erase_ssubset hj)
          (hvs.mono (Finset.coe_subset.mpr (erase_subset j s)))
          ⟨i, Finset.mem_erase.mpr ⟨hij, hi⟩⟩ (fun k hk => hz k (mem_of_mem_erase hk)),
        ih (s.erase i) (Finset.erase_ssubset hi)
          (hvs.mono (Finset.coe_subset.mpr (erase_subset i s)))
          ⟨j, Finset.mem_erase.mpr ⟨hij.symm, hj⟩⟩ (fun k hk => hz k (mem_of_mem_erase hk)),
        ← Finset.mul_prod_erase s (fun k => z - v k) hi]
      field_simp
      linear_combination hprod

end Finset

/-! ### The `Fin`-indexed statements -/

section Fin

variable {m : ℕ}

/-- The first `k + 1` nodes `x₀, …, x_k` of `x₀, …, x_m`. -/
def prefixNodes (v : Fin (m + 1) → ℝ) (k : Fin (m + 1)) : Fin ((k : ℕ) + 1) → ℝ :=
  fun i => v (Fin.castLE k.isLt i)

/-- The last nodes `x_k, …, x_m` of `x₀, …, x_m`. -/
def suffixNodes (v : Fin (m + 1) → ℝ) (k : Fin (m + 1)) : Fin (m - k + 1) → ℝ :=
  fun i => v ⟨k + i, by have := k.isLt; have := i.isLt; omega⟩

/-- The nodal polynomial `ω_k = ∏_{j < k} (X - x_j)` of the first `k` nodes; `ω_0 = 1`. -/
noncomputable def prefixNodal (v : Fin (m + 1) → ℝ) (k : Fin (m + 1)) : ℝ[X] :=
  ∏ j : Fin (k : ℕ), (X - C (v (Fin.castLE k.isLt.le j)))

/-- The embedding `i ↦ k + i` of the indices of the suffix `x_k, …, x_m`. -/
def suffixEmb (m : ℕ) (k : Fin (m + 1)) : Fin (m - k + 1) ↪ Fin (m + 1) :=
  ⟨fun i => ⟨k + i, by have := k.isLt; have := i.isLt; omega⟩, fun i j hij => by
    have := congrArg Fin.val hij
    simp only at this
    exact Fin.ext (by omega)⟩

/-- The prefix indices `0, …, k` are the indices `≤ k`. -/
theorem map_castLEEmb_univ_eq_filter (k : Fin (m + 1)) :
    (univ : Finset (Fin ((k : ℕ) + 1))).map (Fin.castLEEmb k.isLt) = univ.filter (· ≤ k) := by
  ext i
  simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_filter, Fin.castLEEmb_apply,
    Fin.le_def]
  constructor
  · rintro ⟨j, rfl⟩
    simp only [Fin.val_castLE]
    omega
  · intro hi
    exact ⟨⟨i, by omega⟩, Fin.ext rfl⟩

/-- The suffix indices `k, …, m` are the indices `≥ k`. -/
theorem map_suffixEmb_univ_eq_filter (k : Fin (m + 1)) :
    (univ : Finset (Fin (m - k + 1))).map (suffixEmb m k) = univ.filter (k ≤ ·) := by
  ext i
  simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_filter]
  constructor
  · rintro ⟨j, rfl⟩
    change (k : ℕ) ≤ (k : ℕ) + (j : ℕ)
    exact Nat.le_add_right _ _
  · intro hi
    rw [Fin.le_def] at hi
    refine ⟨⟨i - k, by have := k.isLt; have := i.isLt; omega⟩, Fin.ext ?_⟩
    change (k : ℕ) + ((i : ℕ) - k) = i
    omega

/-- The indices `< k` are the image of `Fin k`. -/
theorem map_castLEEmb_univ_eq_filter_lt (k : Fin (m + 1)) :
    (univ : Finset (Fin (k : ℕ))).map (Fin.castLEEmb k.isLt.le) = univ.filter (· < k) := by
  ext i
  simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_filter, Fin.castLEEmb_apply,
    Fin.lt_def]
  constructor
  · rintro ⟨j, rfl⟩
    simp
  · intro hi
    exact ⟨⟨i, hi⟩, Fin.ext rfl⟩

/-- The divided difference at the first `k + 1` nodes, over the index set `{i | i ≤ k}`. -/
theorem newton_prefixNodes (f : ℝ → ℝ) (v : Fin (m + 1) → ℝ) (k : Fin (m + 1)) :
    newton f (prefixNodes v k) = newtonOn (univ.filter (· ≤ k)) v f := by
  rw [← map_castLEEmb_univ_eq_filter, newtonOn_map]
  rfl

/-- The divided difference at the last nodes, over the index set `{i | k ≤ i}`. -/
theorem newton_suffixNodes (f : ℝ → ℝ) (v : Fin (m + 1) → ℝ) (k : Fin (m + 1)) :
    newton f (suffixNodes v k) = newtonOn (univ.filter (k ≤ ·)) v f := by
  rw [← map_suffixEmb_univ_eq_filter, newtonOn_map]
  rfl

/-- The nodal polynomial of the first `k` nodes is Mathlib's nodal polynomial over the indices
`< k`. -/
theorem prefixNodal_eq_nodal (v : Fin (m + 1) → ℝ) (k : Fin (m + 1)) :
    prefixNodal v k = Lagrange.nodal (univ.filter (· < k)) v := by
  rw [← map_castLEEmb_univ_eq_filter_lt, Lagrange.nodal_map]
  rfl

/-- The nodal polynomial of all `m + 1` nodes factors as `ω_m · (X - x_m)`. -/
theorem prefixNodal_last_mul (v : Fin (m + 1) → ℝ) :
    prefixNodal v (Fin.last m) * (X - C (v (Fin.last m))) = Lagrange.nodal univ v := by
  rw [Lagrange.nodal_eq, Fin.prod_univ_castSucc]
  rfl

/-- The divided difference at a single node is the value of the function there. -/
@[simp]
theorem newton_zero (f : ℝ → ℝ) (v : Fin 1 → ℝ) : newton f v = f (v 0) := by
  have : (univ : Finset (Fin (0 + 1))) = {0} := by
    ext i
    simp [Fin.fin_one_eq_zero i]
  rw [newton_eq_newtonOn, this, newtonOn_singleton]

/-- The divided difference at the nodes `x₁, …, x_m`, over the index set `{i | i ≠ 0}`. -/
theorem newton_tail (f : ℝ → ℝ) (v : Fin (m + 2) → ℝ) :
    newton f (Fin.tail v) = newtonOn (univ.erase 0) v f := by
  have : (univ : Finset (Fin (m + 2))).erase 0 = univ.map (Fin.succEmb (m + 1)) := by
    ext i
    simp [Fin.exists_succ_eq]
  rw [this, newtonOn_map]
  rfl

/-- The divided difference at the nodes `x₀, …, x_{m-1}`, over the index set `{i | i ≠ m}`. -/
theorem newton_init (f : ℝ → ℝ) (v : Fin (m + 2) → ℝ) :
    newton f (Fin.init v) = newtonOn (univ.erase (Fin.last (m + 1))) v f := by
  have : (univ : Finset (Fin (m + 2))).erase (Fin.last (m + 1))
      = univ.map (Fin.castSuccEmb (n := m + 1)) := by
    ext i
    simp [Fin.exists_castSucc_eq]
  rw [this, newtonOn_map]
  rfl

/-- **Adding a node** ([quarteroni2000numerical] (8.16)): for nodes `x₀, …, x_m` and a new node
`t` distinct from them, the interpolant at `x₀, …, x_m, t` is the interpolant at `x₀, …, x_m`
plus `f[x₀, …, x_m, t] ω_{m+1}`. -/
theorem interpolate_snoc_eq (f : ℝ → ℝ) {v : Fin (m + 1) → ℝ} {t : ℝ}
    (hv : Function.Injective (Fin.snoc v t : Fin (m + 2) → ℝ)) :
    (Lagrange.interpolate univ (Fin.snoc v t : Fin (m + 2) → ℝ)
        fun i => f ((Fin.snoc v t : Fin (m + 2) → ℝ) i))
      = (Lagrange.interpolate univ v fun i => f (v i))
        + C (newton f (Fin.snoc v t)) * Lagrange.nodal univ v := by
  have hcons : (univ : Finset (Fin (m + 2)))
      = insert (Fin.last (m + 1)) (univ.map (Fin.castSuccEmb (n := m + 1))) := by
    ext i
    simp [Fin.exists_castSucc_eq, eq_or_ne]
  have hlast : Fin.last (m + 1) ∉ (univ : Finset (Fin (m + 1))).map Fin.castSuccEmb := by
    simp
  rw [newton_eq_newtonOn, hcons, interpolate_insert_eq_newtonOn hv.injOn hlast,
    Lagrange.interpolate_map, Lagrange.nodal_map, ← hcons]
  simp only [Function.comp_def, Fin.coe_castSuccEmb, Fin.snoc_castSucc]

/-- **The book's definition of the divided difference** ([quarteroni2000numerical] (8.14)):
`f[x₀, …, x_m, t] = (f(t) - Π_m f(t)) / ω_{m+1}(t)` for a new node `t`. -/
theorem eval_interpolate_snoc_sub (f : ℝ → ℝ) {v : Fin (m + 1) → ℝ} {t : ℝ}
    (hv : Function.Injective (Fin.snoc v t : Fin (m + 2) → ℝ)) :
    newton f (Fin.snoc v t)
      = (f t - (Lagrange.interpolate univ v fun i => f (v i)).eval t) / ∏ i, (t - v i) := by
  obtain ⟨hv', ht⟩ := Fin.snoc_injective_iff.mp hv
  have ht' : ∀ i, v i ≠ t := fun i h => ht ⟨i, h⟩
  have hprod : ∏ i, (t - v i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr (ht' i).symm
  rw [sub_eval_interpolate_eq_newton f hv' ht', mul_div_cancel_left₀ _ hprod]

/-- **The Newton divided difference formula** ([quarteroni2000numerical] (8.17)):
`Π_m f = ∑_{k=0}^m f[x₀, …, x_k] ω_k`. -/
theorem interpolate_eq_sum_newton_mul_prefixNodal (f : ℝ → ℝ) {v : Fin (m + 1) → ℝ}
    (hv : Function.Injective v) :
    (Lagrange.interpolate univ v fun i => f (v i))
      = ∑ k : Fin (m + 1), C (newton f (prefixNodes v k)) * prefixNodal v k := by
  rw [interpolate_eq_sum_newtonOn_mul_nodal hv.injOn]
  exact Finset.sum_congr rfl fun k _ => by rw [newton_prefixNodes, prefixNodal_eq_nodal]

/-- **The recursion** ([quarteroni2000numerical] (8.19), Exercise 8.7):
`f[x₀, …, x_m] = (f[x₁, …, x_m] - f[x₀, …, x_{m-1}]) / (x_m - x₀)`. -/
theorem newton_succ (f : ℝ → ℝ) {v : Fin (m + 2) → ℝ} (hv : Function.Injective v) :
    newton f v
      = (newton f (Fin.tail v) - newton f (Fin.init v)) / (v (Fin.last (m + 1)) - v 0) := by
  rw [newton_tail, newton_init, newton_eq_newtonOn]
  exact newtonOn_eq_sub_div hv.injOn f (mem_univ _) (mem_univ _) (Fin.last_pos).ne'

/-- **Symmetry** ([quarteroni2000numerical] §8.2.1, property 1): a divided difference does not
depend on the order of its nodes. -/
theorem newton_comp_perm (f : ℝ → ℝ) (v : Fin (m + 1) → ℝ) (σ : Equiv.Perm (Fin (m + 1))) :
    newton f (v ∘ σ) = newton f v := by
  have h := newtonOn_map σ.toEmbedding univ v f
  rw [Finset.map_univ_equiv] at h
  rw [newton_eq_newtonOn, newton_eq_newtonOn, h]
  rfl

/-- **Linearity** ([quarteroni2000numerical] §8.2.1, property 2), additivity. -/
theorem newton_add (f g : ℝ → ℝ) (v : Fin (m + 1) → ℝ) :
    newton (f + g) v = newton f v + newton g v :=
  newtonOn_add univ v f g

/-- **Linearity** ([quarteroni2000numerical] §8.2.1, property 2), homogeneity. -/
theorem newton_smul (c : ℝ) (f : ℝ → ℝ) (v : Fin (m + 1) → ℝ) :
    newton (fun t => c * f t) v = c * newton f v :=
  newtonOn_smul univ v c f

/-- **The Leibniz formula** ([quarteroni2000numerical] §8.2.1, property 3):
`(gh)[x₀, …, x_m] = ∑_{j=0}^m g[x₀, …, x_j] h[x_j, …, x_m]`. -/
theorem newton_mul (g h : ℝ → ℝ) {v : Fin (m + 1) → ℝ} (hv : Function.Injective v) :
    newton (fun t => g t * h t) v
      = ∑ j : Fin (m + 1), newton g (prefixNodes v j) * newton h (suffixNodes v j) := by
  rw [newton_eq_newtonOn, newtonOn_mul hv.injOn]
  exact Finset.sum_congr rfl fun j _ => by rw [newton_prefixNodes, newton_suffixNodes]

/-- On a polynomial of degree at most `m`, the divided difference at `m + 1` nodes is the
coefficient of `X^m`. -/
theorem newton_eval_eq_coeff {p : ℝ[X]} (hp : p.degree ≤ m) {v : Fin (m + 1) → ℝ}
    (hv : Function.Injective v) : newton (fun t => p.eval t) v = p.coeff m := by
  have hcard : (univ : Finset (Fin (m + 1))).card = m + 1 := by simp
  rw [newton_eq_newtonOn, newtonOn_eval_eq_coeff hv.injOn (by
    rw [hcard]; exact lt_of_le_of_lt hp (by exact_mod_cast Nat.lt_succ_self m)), hcard,
    Nat.add_sub_cancel]

/-- A divided difference of order `m` of a polynomial of degree `< m` vanishes
([quarteroni2000numerical] §8.2.1, the remark after Example 8.3). -/
theorem newton_eq_zero_of_degree_lt {p : ℝ[X]} (hp : p.degree < m) {v : Fin (m + 1) → ℝ}
    (hv : Function.Injective v) : newton (fun t => p.eval t) v = 0 := by
  rw [newton_eval_eq_coeff hp.le hv]
  exact coeff_eq_zero_of_degree_lt hp

/-- A divided difference of order `m` of a polynomial of degree `m` is its leading coefficient. -/
theorem newton_eval_eq_leadingCoeff {p : ℝ[X]} (hp : p.degree = m) {v : Fin (m + 1) → ℝ}
    (hv : Function.Injective v) : newton (fun t => p.eval t) v = p.leadingCoeff := by
  rw [newton_eval_eq_coeff hp.le hv, leadingCoeff, natDegree_eq_of_degree_eq_some hp]

/-! ### The mean-value form -/

/-- **The mean-value form of a divided difference, for a function smooth only near the interval**
([quarteroni2000numerical] (8.21), [kress1998numerical] Theorem 8.9): for `f` of class `C^{m+1}`
on an open set containing `[a, b]` and `m + 2` distinct nodes in `[a, b]`,
`f[x₀, …, x_{m+1}] = f^{(m+1)}(ξ)/(m+1)!` for some `ξ` strictly inside `[a, b]`.

The function `f - Π_{m+1} f` vanishes at the `m + 2` nodes, so by the generalized Rolle theorem its
`(m+1)`-st derivative vanishes somewhere, and that derivative is `f^{(m+1)} - (m+1)! · f[x₀, …]`. -/
theorem exists_newton_eq_iteratedDeriv_div_of_contDiffOn {a b : ℝ} {f : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hUsub : Set.Icc a b ⊆ U) (hf : ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) f U)
    {v : Fin (m + 2) → ℝ} (hv : Function.Injective v) (hmem : ∀ i, v i ∈ Set.Icc a b) :
    ∃ ξ ∈ Set.Ioo a b, newton f v = iteratedDeriv (m + 1) f ξ / (m + 1).factorial := by
  classical
  set P : ℝ[X] := Lagrange.interpolate univ v fun i => f (v i) with hP
  have hPdeg : P.natDegree ≤ m + 1 := by
    have := Lagrange.degree_interpolate_le (s := univ) (fun i => f (v i)) hv.injOn
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact natDegree_le_of_degree_le (this.trans (by exact_mod_cast (by omega : m + 2 - 1 ≤ m + 1)))
  have hPcd : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) fun t => P.eval t := by
    simpa [Polynomial.coe_aeval_eq_eval] using P.contDiff_aeval (𝕜 := ℝ) ((m + 1 : ℕ) : WithTop ℕ∞)
  set s : Finset ℝ := univ.image v with hs
  have hscard : m + 2 ≤ s.card := by
    rw [hs, Finset.card_image_of_injective _ hv, Finset.card_univ, Fintype.card_fin]
  have hssub : ∀ t ∈ s, t ∈ Set.Icc a b := by
    intro t ht
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
    exact hmem i
  have hzero : ∀ t ∈ s, f t - P.eval t = 0 := by
    intro t ht
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
    rw [hP, Lagrange.eval_interpolate_at_node _ hv.injOn (mem_univ i), sub_self]
  obtain ⟨ξ, hξ, hξ0⟩ := exists_iteratedDeriv_eq_zero_of_forall_eq_zero_of_contDiffOn hU hUsub
    (hf.sub hPcd.contDiffOn) hscard hssub hzero
  refine ⟨ξ, hξ, ?_⟩
  have hsub : iteratedDeriv (m + 1) (fun u => f u - P.eval u) ξ
      = iteratedDeriv (m + 1) f ξ - iteratedDeriv (m + 1) (fun u => P.eval u) ξ :=
    iteratedDeriv_fun_sub (hf.contDiffAt (hU.mem_nhds (hUsub ⟨hξ.1.le, hξ.2.le⟩)))
      hPcd.contDiffAt
  have hPder : iteratedDeriv (m + 1) (fun u => P.eval u) ξ
      = (m + 1).factorial * newton f v := by
    rw [congrFun (Polynomial.iteratedDeriv_eval P (m + 1)) ξ,
      Polynomial.iterate_derivative_eq_C_of_natDegree_le hPdeg, eval_C, newton_eq_coeff f hv]
  rw [hsub, hPder] at hξ0
  have hfact : ((m + 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp
  linarith

/-- **The mean-value form of a divided difference** ([quarteroni2000numerical] (8.21),
[kress1998numerical] Theorem 8.9): for `f` of class `C^m` on an open set containing `[a, b]` and
`m + 1` distinct nodes in `[a, b]`, `f[x₀, …, x_m] = f^{(m)}(ξ)/m!` for some `ξ ∈ [a, b]`. For
`m = 0` the divided difference is `f(x₀)`; otherwise `ξ` may be taken strictly inside `[a, b]`
(`exists_newton_eq_iteratedDeriv_div_of_contDiffOn`). -/
theorem exists_newton_eq_iteratedDeriv_div {a b : ℝ} {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hUsub : Set.Icc a b ⊆ U) (hf : ContDiffOn ℝ (m : WithTop ℕ∞) f U) {v : Fin (m + 1) → ℝ}
    (hv : Function.Injective v) (hmem : ∀ i, v i ∈ Set.Icc a b) :
    ∃ ξ ∈ Set.Icc a b, newton f v = iteratedDeriv m f ξ / m.factorial := by
  cases m with
  | zero => exact ⟨v 0, hmem 0, by simp⟩
  | succ m =>
    obtain ⟨ξ, hξ, h⟩ :=
      exists_newton_eq_iteratedDeriv_div_of_contDiffOn hU hUsub hf hv hmem
    exact ⟨ξ, Set.Ioo_subset_Icc_self hξ, h⟩

/-- **The mean-value form of a divided difference, for a globally smooth function.** -/
theorem exists_newton_eq_iteratedDeriv_div_of_contDiff {a b : ℝ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ (m : WithTop ℕ∞) f) {v : Fin (m + 1) → ℝ} (hv : Function.Injective v)
    (hmem : ∀ i, v i ∈ Set.Icc a b) :
    ∃ ξ ∈ Set.Icc a b, newton f v = iteratedDeriv m f ξ / m.factorial :=
  exists_newton_eq_iteratedDeriv_div isOpen_univ (Set.subset_univ _) hf.contDiffOn hv hmem

/-- **The bound on a divided difference**: if `|f^{(m)}| ≤ M` on `[a, b]`, then
`|f[x₀, …, x_m]| ≤ M / m!` for any `m + 1` distinct nodes in `[a, b]`. -/
theorem abs_newton_le {a b : ℝ} {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hUsub : Set.Icc a b ⊆ U)
    (hf : ContDiffOn ℝ (m : WithTop ℕ∞) f U) {v : Fin (m + 1) → ℝ} (hv : Function.Injective v)
    (hmem : ∀ i, v i ∈ Set.Icc a b) {M : ℝ}
    (hM : ∀ t ∈ Set.Icc a b, |iteratedDeriv m f t| ≤ M) : |newton f v| ≤ M / m.factorial := by
  obtain ⟨ξ, hξ, h⟩ := exists_newton_eq_iteratedDeriv_div hU hUsub hf hv hmem
  rw [h, abs_div, abs_of_pos (by positivity : (0 : ℝ) < m.factorial)]
  exact div_le_div_of_nonneg_right (hM ξ hξ) (by positivity)

/-- **Divided differences of a Cauchy kernel** ([quarteroni2000numerical] Example 8.1, the
real-variable route to Runge's phenomenon): for `z` distinct from every node,
`f[x₀, …, x_m] = 1 / ∏ᵢ (z - xᵢ)` for `f(t) = 1/(z - t)`. The same identity over any field is
`newtonOn_inv_sub`. -/
theorem newton_inv_sub {v : Fin (m + 1) → ℝ} (hv : Function.Injective v) {z : ℝ}
    (hz : ∀ i, z ≠ v i) : newton (fun t => 1 / (z - t)) v = 1 / ∏ i, (z - v i) :=
  newtonOn_inv_sub hv.injOn univ_nonempty fun i _ => hz i

/-! ### The derivative in the last node -/

/-- **The derivative of a divided difference in its last argument** ([quarteroni2000numerical]
(9.22), Exercise 9.4): for distinct nodes `x₀, …, x_n`, a point `x` distinct from them and `f`
differentiable at `x`, the derivative of `x ↦ f[x₀, …, x_n, x]` at `x` is the *confluent* divided
difference `f[x₀, …, x_n, x, x]`: the coefficient of `X^{n+2}` in the Hermite interpolant of `f`
at the simple nodes `x₀, …, x_n` and the double node `x`.

Near `x` the function is `(f - Π_n f)/ω_{n+1}` (`eval_interpolate_snoc_sub`), whose derivative is
computed by the quotient rule; the Hermite interpolant `H` is the Lagrange interpolant at
`x₀, …, x_n, x` plus `c (X - x) ω_{n+1}` with `c` its top coefficient, and differentiating this
identity at `x`, where `H' = f'`, identifies `c` with that derivative. -/
theorem hasDerivAt_newton_snoc {n : ℕ} {f : ℝ → ℝ} {v : Fin (n + 1) → ℝ}
    (hv : Function.Injective v) {x : ℝ} (hx : x ∉ Set.range v) (hf : DifferentiableAt ℝ f x) :
    HasDerivAt (fun y => newton f (Fin.snoc v y))
      ((Hermite.interpolate (Fin.snoc v x) (Fin.snoc (fun _ => 0) 1) f).coeff (n + 2)) x := by
  classical
  set w : Fin (n + 2) → ℝ := Fin.snoc v x with hw
  set μ : Fin (n + 2) → ℕ := Fin.snoc (fun _ => 0) 1 with hμ
  set H : ℝ[X] := Hermite.interpolate w μ f with hH
  set c : ℝ := H.coeff (n + 2) with hc
  set ω : ℝ[X] := Lagrange.nodal univ v with hω
  set P₀ : ℝ[X] := Lagrange.interpolate univ v fun i => f (v i) with hP₀
  have hwinj : Function.Injective w := Fin.snoc_injective_iff.mpr ⟨hv, hx⟩
  have hxv : ∀ i, v i ≠ x := fun i h => hx ⟨i, h⟩
  have hωx : ω.eval x ≠ 0 := by
    rw [hω, Lagrange.eval_nodal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr (hxv i).symm
  have hωv : ∀ i, ω.eval (v i) = 0 := fun i => Lagrange.eval_nodal_at_node (mem_univ i)
  -- the Hermite interpolant: degree, values, derivative at `x`
  have hμsum : ∑ i, (μ i + 1) = n + 3 := by
    rw [Fin.sum_univ_castSucc]
    simp [hμ, Fin.snoc_castSucc, Fin.snoc_last]
  have hHdeg : H.degree < ((n + 3 : ℕ) : WithBot ℕ) := by
    have := Hermite.degree_interpolate_lt hwinj μ f
    rwa [hμsum] at this
  have hHval : ∀ i, H.eval (w i) = f (w i) := fun i => by
    simpa using
      Hermite.eval_iterate_derivative_interpolate (f := f) hwinj i (j := 0) (Nat.zero_le _)
  have hHder : (derivative H).eval x = deriv f x := by
    have h1 : 1 ≤ μ (Fin.last (n + 1)) := by simp [hμ]
    have := Hermite.eval_iterate_derivative_interpolate (f := f) hwinj (Fin.last (n + 1)) h1
    simpa [hw, Fin.snoc_last, iteratedDeriv_one] using this
  -- `H` is the Lagrange interpolant at `w` plus `c (X - x) ω`
  set Q : ℝ[X] := (X - C x) * ω with hQ
  have hQmonic : Q.Monic := (monic_X_sub_C x).mul Lagrange.nodal_monic
  have hQnat : Q.natDegree = n + 2 := by
    rw [hQ, (monic_X_sub_C x).natDegree_mul Lagrange.nodal_monic, natDegree_X_sub_C,
      Lagrange.natDegree_nodal, Finset.card_univ, Fintype.card_fin]
    ring
  have hQval : ∀ i, Q.eval (w i) = 0 := by
    intro i
    induction i using Fin.lastCases with
    | last => simp [hQ, hw, Fin.snoc_last]
    | cast i => simp [hQ, hw, Fin.snoc_castSucc, hωv]
  have hH₁ : H = (Lagrange.interpolate univ w fun i => f (w i)) + C c * Q := by
    have hdeg : (H - C c * Q).degree < ((n + 2 : ℕ) : WithBot ℕ) := by
      refine (degree_lt_iff_coeff_zero _ _).2 fun k hk => ?_
      rw [coeff_sub, coeff_C_mul]
      rcases eq_or_lt_of_le hk with hk | hlt
      · rw [← hk, ← hQnat, hQmonic.coeff_natDegree, mul_one, hQnat, hc, sub_self]
      · rw [coeff_eq_zero_of_degree_lt (hHdeg.trans_le (by exact_mod_cast hlt)),
          coeff_eq_zero_of_natDegree_lt (hQnat ▸ hlt), mul_zero, sub_zero]
    have hval : ∀ i ∈ (univ : Finset (Fin (n + 2))), (H - C c * Q).eval (w i) = f (w i) :=
      fun i _ => by rw [eval_sub, eval_mul, eval_C, hQval, mul_zero, sub_zero, hHval]
    have := Lagrange.eq_interpolate_of_eval_eq _ hwinj.injOn
      (by rw [Finset.card_univ, Fintype.card_fin]; exact hdeg) hval
    rw [← this]
    ring
  -- the Lagrange interpolant at `w` is the one at `v` plus `f[v, x] ω`
  have hP₁₀ : (Lagrange.interpolate univ w fun i => f (w i))
      = P₀ + C (newton f w) * ω := interpolate_snoc_eq f hwinj
  have hFx : newton f w = (f x - P₀.eval x) / ω.eval x := by
    rw [eval_interpolate_snoc_sub f hwinj, hω, Lagrange.eval_nodal]
  -- differentiate the identity at `x`
  have hkey : deriv f x
      = (derivative P₀).eval x + newton f w * (derivative ω).eval x + c * ω.eval x := by
    have := congrArg (fun p : ℝ[X] => (derivative p).eval x) hH₁
    simp only [hP₁₀, hQ, derivative_add, derivative_mul, derivative_C, derivative_sub,
      derivative_X, eval_add, eval_mul, eval_C, eval_sub, eval_X, sub_self, zero_mul, zero_add,
      one_mul, add_zero, sub_zero] at this
    rw [hHder] at this
    linarith [this]
  -- the function agrees with `(f - Π_n f)/ω` near `x`
  have hev : (fun y => newton f (Fin.snoc v y)) =ᶠ[nhds x]
      fun y => (f y - P₀.eval y) / ω.eval y := by
    have hopen : IsOpen (Set.range v)ᶜ := (Set.finite_range v).isClosed.isOpen_compl
    filter_upwards [hopen.mem_nhds hx] with y hy
    have hinj : Function.Injective (Fin.snoc v y : Fin (n + 2) → ℝ) :=
      Fin.snoc_injective_iff.mpr ⟨hv, hy⟩
    rw [eval_interpolate_snoc_sub f hinj, hω, Lagrange.eval_nodal]
  have hd : HasDerivAt (fun y => (f y - P₀.eval y) / ω.eval y)
      (((deriv f x - (derivative P₀).eval x) * ω.eval x
        - (f x - P₀.eval x) * (derivative ω).eval x) / (ω.eval x) ^ 2) x :=
    HasDerivAt.div (hf.hasDerivAt.sub (P₀.hasDerivAt x)) (ω.hasDerivAt x) hωx
  refine (hd.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [hkey, hFx]
  field_simp
  ring

/-! ### Confluent divided differences -/

/-- **Confluent divided differences** ([quarteroni2000numerical] Remark 8.3, with the corrected
diagonal value): by recursion on the number of nodes, `f[x₀] = f(x₀)`, and for `m + 2` nodes
`f[x₀, …, x_{m+1}] = f^{(m+1)}(x₀)/(m+1)!` when `x₀ = x_{m+1}` (so, for a nondecreasing family,
when all the nodes coincide) and `(f[x₁, …, x_{m+1}] - f[x₀, …, x_m]) / (x_{m+1} - x₀)` otherwise.

The book prints `f^{(n+1)}(x₀)/(n+1)!` for `n + 1` coincident nodes `x₀ = ⋯ = x_n`; the `n`-th
divided difference at those nodes is `f^{(n)}(x₀)/n!` (for instance `f[x₀, x₀] = f'(x₀)`), which
is the value used here. -/
noncomputable def confluent (f : ℝ → ℝ) : {m : ℕ} → (Fin (m + 1) → ℝ) → ℝ
  | 0, v => f (v 0)
  | m + 1, v =>
    if v 0 = v (Fin.last (m + 1)) then iteratedDeriv (m + 1) f (v 0) / (m + 1).factorial
    else (confluent f (Fin.tail v) - confluent f (Fin.init v)) / (v (Fin.last (m + 1)) - v 0)

@[simp]
theorem confluent_zero (f : ℝ → ℝ) (v : Fin 1 → ℝ) : confluent f v = f (v 0) := rfl

theorem confluent_succ (f : ℝ → ℝ) (v : Fin (m + 2) → ℝ) :
    confluent f v = if v 0 = v (Fin.last (m + 1))
      then iteratedDeriv (m + 1) f (v 0) / (m + 1).factorial
      else (confluent f (Fin.tail v) - confluent f (Fin.init v)) / (v (Fin.last (m + 1)) - v 0) :=
  rfl

/-- At distinct nodes the confluent divided difference is the classical one. -/
theorem confluent_eq_newton (f : ℝ → ℝ) {v : Fin (m + 1) → ℝ} (hv : Function.Injective v) :
    confluent f v = newton f v := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h0 : v 0 ≠ v (Fin.last (m + 1)) := fun h => absurd (hv h) (Fin.last_pos).ne
    rw [confluent_succ, ite_eq_right h0, ih (v := Fin.tail v) (hv.comp (Fin.succ_injective _)),
      ih (v := Fin.init v) (hv.comp (Fin.castSucc_injective _)), newton_succ f hv]

/-- At `m + 1` copies of one node `x`, the confluent divided difference is `f^{(m)}(x)/m!`. -/
theorem confluent_const (f : ℝ → ℝ) (x : ℝ) :
    confluent f (fun _ : Fin (m + 1) => x) = iteratedDeriv m f x / m.factorial := by
  cases m with
  | zero => simp
  | succ m => rw [confluent_succ, ite_eq_left rfl]

end Fin

end DividedDifference

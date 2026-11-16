/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Deriv.Inv
import Numlib.Approximation.DividedDifference
import Numlib.Approximation.Hermite

/-!
# The Newton form of the interpolating polynomial

Let $x_0, \dots, x_m$ be distinct real nodes. The Newton divided difference
$$f[x_0, \dots, x_m] = \sum_{i=0}^m \frac{f(x_i)}{\prod_{j \neq i} (x_i - x_j)}$$
is `DividedDifference.newton` of `Numlib.Approximation.DividedDifference`. That module also proves
that it is the coefficient of $X^m$ in the interpolant (`DividedDifference.newton_eq_coeff`) and the
divided-difference form of the interpolation error
(`DividedDifference.sub_eval_interpolate_eq_newton`). This module develops the rest of the classical
theory of divided differences, following [quarteroni2000numerical], §8.2 and Remark 8.3, and
[kress1998numerical], §8.2: the Newton form of the interpolant, the recursion in the nodes, the
algebraic rules (symmetry, linearity and the Leibniz formula), the mean value form
$f[x_0, \dots, x_m] = f^{(m)}(\xi)/m!$, the divided differences of $t \mapsto 1/(z - t)$ (the engine
of divergence arguments of Runge type), the derivative of a divided difference in its last argument,
and confluent divided differences at repeated nodes, which B-splines with coincident knots need.

Write $\Pi_m f$ for the interpolant of $f$ at $x_0, \dots, x_m$ and
$\omega_k = \prod_{j < k} (X - x_j)$ for the nodal polynomial of the first $k$ nodes, with
$\omega_0 = 1$.

## Main definitions

* `DividedDifference.newtonOn`: the divided difference $f[v_i : i \in s]$ at the nodes indexed by a
  finite set $s$, over any field.
* `DividedDifference.prefixNodes`, `DividedDifference.suffixNodes`: the truncations
  $(x_0, \dots, x_k)$ and $(x_k, \dots, x_m)$ of the nodes.
* `DividedDifference.prefixNodal`: the nodal polynomial $\omega_k$ of the first $k$ nodes.
* `DividedDifference.confluent`: the confluent divided difference at possibly repeated nodes.

## Main results

* `DividedDifference.interpolate_snoc_eq`: adding a node $t$ adds
  $f[x_0, \dots, x_m, t] \, \omega_{m+1}$ to the interpolant.
* `DividedDifference.eval_interpolate_snoc_sub`: $f[x_0, \dots, x_m, t] = (f(t) - \Pi_m
  f(t))/\omega_{m+1}(t)$, the definition of the divided difference in [quarteroni2000numerical].
* `DividedDifference.interpolate_eq_sum_newton_mul_prefixNodal`: the **Newton divided difference
  formula** $\Pi_m f = \sum_{k=0}^m f[x_0, \dots, x_k] \, \omega_k$.
* `DividedDifference.newton_succ`: the recursion $f[x_0, \dots, x_m] = (f[x_1, \dots, x_m] - f[x_0,
  \dots, x_{m-1}])/(x_m - x_0)$.
* `DividedDifference.newton_comp_perm`: a divided difference does not depend on the order of the
  nodes.
* `DividedDifference.newton_add`, `DividedDifference.newton_smul`: a divided difference is linear in
  the function.
* `DividedDifference.newton_mul`: the **Leibniz formula** $(gh)[x_0, \dots, x_m] = \sum_{j=0}^m
  g[x_0, \dots, x_j] \, h[x_j, \dots, x_m]$.
* `DividedDifference.newton_eval_eq_coeff`: on a polynomial of degree at most $m$, the divided
  difference is the coefficient of $X^m$.
* `DividedDifference.newton_eq_zero_of_degree_lt`: the divided difference of a polynomial of degree
  less than $m$ vanishes.
* `DividedDifference.exists_newton_eq_iteratedDeriv_div`: the **mean value form**
  $f[x_0, \dots, x_m] = f^{(m)}(\xi)/m!$.
* `DividedDifference.abs_newton_le`: $|f[x_0, \dots, x_m]| \le M/m!$ if $|f^{(m)}| \le M$.
* `DividedDifference.newton_inv_sub`: for $f(t) = 1/(z - t)$,
  $f[x_0, \dots, x_m] = 1/\prod_i (z - x_i)$.
* `DividedDifference.hasDerivAt_newton_snoc`: the derivative of $x \mapsto f[x_0, \dots, x_n, x]$ is
  the confluent divided difference $f[x_0, \dots, x_n, x, x]$, the top coefficient of the Hermite
  interpolant with a double node at $x$.
* `DividedDifference.confluent_eq_newton`, `DividedDifference.confluent_const`: the confluent
  divided difference is the classical one at distinct nodes, and $f^{(m)}(x)/m!$ at $m + 1$ copies
  of $x$.
* `DividedDifference.continuous_confluent`: for $f$ of class $C^m$, the confluent divided difference
  is continuous on the nondecreasing tuples of nodes.
* `DividedDifference.exists_confluent_eq_iteratedDeriv_div`: the mean value form of the confluent
  divided difference, with $\xi$ between the extreme nodes.
* `DividedDifference.newtonOn_eq_divDiff`, `DividedDifference.confluent_eq_divDiff`: both divided
  differences are instances of the divided difference `Hermite.divDiff` at a multiset of possibly
  repeated nodes (`Numlib.Analysis.Calculus.HermiteInterpolation`), the leading coefficient of the
  Hermite interpolant: at distinct nodes, and at a nondecreasing tuple of nodes.

## Implementation notes

* The classical statements are indexed by `Fin (m + 1)`. The arguments behind them (adding a node,
  deleting a node, splitting the nodes into a prefix and a suffix) are simpler on an arbitrary
  finite set of indices, where they need no dependent types. So the module first develops
  `DividedDifference.newtonOn s v f`, the divided difference of $f$ at the nodes $v_i$, $i \in s$,
  over any field, in the setting of Mathlib's `Lagrange.interpolate s v`. By definition,
  `DividedDifference.newton f v` is `DividedDifference.newtonOn Finset.univ v f`. The Newton form
  over a linearly ordered index set (`DividedDifference.interpolate_eq_sum_newtonOn_mul_nodal`), the
  recursion in two arbitrary nodes (`DividedDifference.newtonOn_eq_sub_div`) and the Leibniz formula
  (`DividedDifference.newtonOn_mul`) are proved for `DividedDifference.newtonOn`, and the
  `Fin`-indexed statements follow through the reindexing lemma `DividedDifference.newtonOn_map`.
* The nodes are `v : Fin (m + 1) → ℝ`. `Fin.init v`, `Fin.tail v` and `Fin.snoc v t` drop the last
  node, drop the first node, and append the node $t$, so the recursion reads `newton f v = (newton f
  (Fin.tail v) - newton f (Fin.init v)) / (v (Fin.last _) - v 0)`. The truncations
  `DividedDifference.prefixNodes v k` and `DividedDifference.suffixNodes v k` carry the Newton sum
  and the Leibniz formula. The interpolant is Mathlib's `Lagrange.interpolate Finset.univ v (f ∘ v)`
  and the nodal polynomial is `Lagrange.nodal Finset.univ v`, as in
  `Numlib.Approximation.DividedDifference`.
* The Leibniz formula has Steffensen's proof (*Interpolation*, §19).
* Remark 8.3 of [quarteroni2000numerical] gives the value $f^{(n+1)}(x_0)/(n + 1)!$ for the divided
  difference at $n + 1$ coincident nodes $x_0 = \dots = x_n$. The correct value is
  $f^{(n)}(x_0)/n!$, and `DividedDifference.confluent` uses it.
-/

open Polynomial Finset

/-- Reindexing a Lagrange interpolant along an embedding $e : \kappa \hookrightarrow \iota$ of index
sets: the interpolant of the values $r$ at the nodes $v$ over the image $e(t)$ of a finite set
$t$ is the interpolant of the values $r \circ e$ at the nodes $v \circ e$ over $t$. -/
theorem Lagrange.interpolate_map {F : Type*} [Field F] {ι κ : Type*} [DecidableEq ι]
    [DecidableEq κ] (e : κ ↪ ι) (t : Finset κ) (v r : ι → F) :
    Lagrange.interpolate (t.map e) v r = Lagrange.interpolate t (v ∘ e) (r ∘ e) := by
  simp only [Lagrange.interpolate_apply, Finset.sum_map, Function.comp_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  simp only [Lagrange.basis, ← Finset.map_erase, Finset.prod_map]
  rfl

/-- Reindexing a nodal polynomial along an embedding $e : \kappa \hookrightarrow \iota$ of index
sets: the nodal polynomial of the nodes $v$ over $e(t)$ is the nodal polynomial of the nodes
$v \circ e$ over $t$. -/
theorem Lagrange.nodal_map {R : Type*} [CommRing R] {ι κ : Type*} (e : κ ↪ ι) (t : Finset κ)
    (v : ι → R) : Lagrange.nodal (t.map e) v = Lagrange.nodal t (v ∘ e) := by
  simp only [Lagrange.nodal, Finset.prod_map]
  rfl

/-- **Adding a node to a Lagrange interpolant.** Let $F$ be a field, let $t$ be a finite index set
and $a \notin t$, and let the nodes $v_i$, $i \in t \cup \{a\}$, be distinct. Then for all
values $r$,
$$\Pi_{t \cup \{a\}} = \Pi_t + c \, \omega_t,$$
where $\Pi_s$ is the Lagrange interpolant of $r$ at the nodes indexed by $s$,
$\omega_t = \prod_{i \in t} (X - v_i)$ is the nodal polynomial of $t$, and $c$ is the
coefficient of $X^{\# t}$ in $\Pi_{t \cup \{a\}}$.

The difference of the two interpolants vanishes at the nodes of $t$ and has degree at most
$\# t$, so it is a multiple of $\omega_t$. -/
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

/-- The **Newton divided difference over a finite index set**: for a finite set $s$ of indices,
nodes $v_i$ in a field $F$ and $f : F \to F$,
$$f[v_i : i \in s] = \sum_{i \in s} \frac{f(v_i)}{\prod_{j \in s, \, j \neq i} (v_i - v_j)}.$$

For injective nodes it is the coefficient of $X^{\# s - 1}$ in the interpolant
`Lagrange.interpolate s v (f ∘ v)` (`DividedDifference.newtonOn_eq_coeff`). The divided
difference `DividedDifference.newton f v` of a `Fin`-indexed family is the case
`s = Finset.univ`. -/
noncomputable def newtonOn (s : Finset ι) (v : ι → F) (f : F → F) : F :=
  ∑ i ∈ s, f (v i) / ∏ j ∈ s.erase i, (v i - v j)

/-- The divided difference $f[x_0, \dots, x_m]$ of a `Fin`-indexed family of real nodes is the
divided difference over the full index set. -/
theorem newton_eq_newtonOn {m : ℕ} (f : ℝ → ℝ) (v : Fin (m + 1) → ℝ) :
    newton f v = newtonOn univ v f := rfl

/-- The divided difference over the empty index set is $0$. -/
@[simp]
theorem newtonOn_empty (v : ι → F) (f : F → F) : newtonOn ∅ v f = 0 := by
  simp [newtonOn]

/-- The divided difference at a single node $v_i$ is the value $f(v_i)$. -/
@[simp]
theorem newtonOn_singleton (v : ι → F) (f : F → F) (i : ι) : newtonOn {i} v f = f (v i) := by
  simp [newtonOn]

/-- Reindexing the nodes along an embedding $e : \kappa \hookrightarrow \iota$:
$f[v_i : i \in e(t)] = f[v_{e(j)} : j \in t]$. -/
theorem newtonOn_map {κ : Type*} [DecidableEq κ] (e : κ ↪ ι) (t : Finset κ) (v : ι → F)
    (f : F → F) : newtonOn (t.map e) v f = newtonOn t (v ∘ e) f := by
  simp only [newtonOn, Finset.sum_map, Function.comp_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.map_erase, Finset.prod_map]

/-- The divided difference depends on the nodes only through their values on the index set: if
$v_i = w_i$ for every $i \in s$, then $f[v_i : i \in s] = f[w_i : i \in s]$. -/
theorem newtonOn_congr {w : ι → F} (h : ∀ i ∈ s, v i = w i) (f : F → F) :
    newtonOn s v f = newtonOn s w f := by
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [h i hi]
  congr 1
  exact Finset.prod_congr rfl fun l hl => by rw [h l (Finset.mem_of_mem_erase hl)]

/-- **Deleting one node, written as a sum over the whole index set.** Let the nodes $v_i$,
$i \in s$, be distinct and let $a \in s$. Then
$$f[v_i : i \in s \setminus \{a\}] = \sum_{w \in s} \frac{f(v_w)(v_w - v_a)}{\prod_{j \in s, \,
  j \neq w} (v_w - v_j)}.$$

The term of the deleted node carries the factor $v_a - v_a = 0$, so it may be added to the sum. -/
theorem newtonOn_erase_eq_sum (hvs : Set.InjOn v s) (f : F → F) {a : ι} (ha : a ∈ s) :
    newtonOn (s.erase a) v f
      = ∑ w ∈ s, f (v w) * (v w - v a) / ∏ j ∈ s.erase w, (v w - v j) := by
  rw [newtonOn, ← Finset.sum_erase _ (f := fun w => f (v w) * (v w - v a)
    / ∏ j ∈ s.erase w, (v w - v j)) (a := a) (by simp)]
  refine Finset.sum_congr rfl fun w hw => ?_
  obtain ⟨hwa, hws⟩ := Finset.mem_erase.1 hw
  have hne : v w - v a ≠ 0 := sub_ne_zero.2 fun h => hwa (hvs hws ha h)
  have hsplit : ∏ j ∈ s.erase w, (v w - v j)
      = (v w - v a) * ∏ j ∈ (s.erase w).erase a, (v w - v j) :=
    (Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨Ne.symm hwa, ha⟩)).symm
  rw [hsplit, Finset.erase_right_comm]
  field_simp

/-- **A three-term identity for divided differences.** Let the nodes $v_i$, $i \in s$, be distinct,
let $p, q, r \in s$, and let $v_p = b v_q + (1 - b) v_r$ for some $b \in F$. Then
$$f[v_i : i \in s \setminus \{p\}] = b \, f[v_i : i \in s \setminus \{q\}] + (1 - b) \, f[v_i :
  i \in s \setminus \{r\}].$$

In the form of `DividedDifference.newtonOn_erase_eq_sum`, this is the pointwise identity
$v_w - v_p = b (v_w - v_q) + (1 - b)(v_w - v_r)$. It is the engine of Boehm's knot insertion for
B-splines. -/
theorem newtonOn_erase_eq_affine_comb (hvs : Set.InjOn v s) {p q r : ι} (hp : p ∈ s) (hq : q ∈ s)
    (hr : r ∈ s) {b : F} (hb : v p = b * v q + (1 - b) * v r) (f : F → F) :
    newtonOn (s.erase p) v f
      = b * newtonOn (s.erase q) v f + (1 - b) * newtonOn (s.erase r) v f := by
  rw [newtonOn_erase_eq_sum hvs f hp, newtonOn_erase_eq_sum hvs f hq,
    newtonOn_erase_eq_sum hvs f hr, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [hb]
  field_simp
  ring

/-- For a sequence $v_0, v_1, \dots$ of real nodes, a function $g$ and $m, i \in \mathbb{N}$, the
divided difference $g[v_i, \dots, v_{i+m}]$ at $m + 1$ consecutive nodes equals the divided
difference over the index interval $\{i, \dots, i + m\}$. -/
theorem newton_shift_eq_newtonOn (v : ℕ → ℝ) (g : ℝ → ℝ) (m i : ℕ) :
    newton g (fun r : Fin (m + 1) => v (i + r)) = newtonOn (Finset.Icc i (i + m)) v g := by
  have hinj : Function.Injective (fun r : Fin (m + 1) => i + (r : ℕ)) :=
    fun a b h => Fin.ext (by simpa using h)
  have hmap : (Finset.univ : Finset (Fin (m + 1))).map ⟨_, hinj⟩ = Finset.Icc i (i + m) := by
    ext c
    simp only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and,
      Finset.mem_Icc]
    constructor
    · rintro ⟨r, rfl⟩
      have := r.isLt
      omega
    · rintro ⟨h1, h2⟩
      refine ⟨⟨c - i, by omega⟩, ?_⟩
      change i + (c - i) = c
      omega
  rw [← hmap, newtonOn_map, newton_eq_newtonOn]
  rfl

/-- **The divided difference is the top coefficient of the interpolant.** If the nodes $v_i$,
$i \in s$, are distinct, then $f[v_i : i \in s]$ is the coefficient of $X^{\# s - 1}$ in the
Lagrange interpolant of $f$ at these nodes.

This is Mathlib's `Lagrange.coeff_eq_sum` read backwards. -/
theorem newtonOn_eq_coeff (hvs : Set.InjOn v s) (f : F → F) :
    newtonOn s v f = (Lagrange.interpolate s v fun i => f (v i)).coeff (s.card - 1) := by
  rw [Lagrange.coeff_eq_sum hvs (Lagrange.degree_interpolate_lt _ hvs)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Lagrange.eval_interpolate_at_node _ hvs hi]

/-- Let the nodes $v_i$, $i \in s$, be distinct, and let $p$ be a polynomial of degree less than
$\# s$. Then $p[v_i : i \in s]$ is the coefficient of $X^{\# s - 1}$ in $p$. -/
theorem newtonOn_eval_eq_coeff (hvs : Set.InjOn v s) {p : F[X]} (hp : p.degree < s.card) :
    newtonOn s v (fun t => p.eval t) = p.coeff (s.card - 1) := by
  rw [newtonOn_eq_coeff hvs, ← Lagrange.eq_interpolate hvs hp]

/-- Divided differences are additive in the function: $(f + g)[v_i : i \in s] = f[v_i : i \in s] +
g[v_i : i \in s]$. -/
theorem newtonOn_add (s : Finset ι) (v : ι → F) (f g : F → F) :
    newtonOn s v (fun t => f t + g t) = newtonOn s v f + newtonOn s v g := by
  simp only [newtonOn, add_div, Finset.sum_add_distrib]

/-- Divided differences are homogeneous in the function:
$(cf)[v_i : i \in s] = c \, f[v_i : i \in s]$. -/
theorem newtonOn_smul (s : Finset ι) (v : ι → F) (c : F) (f : F → F) :
    newtonOn s v (fun t => c * f t) = c * newtonOn s v f := by
  simp only [newtonOn, Finset.mul_sum, mul_div_assoc]

/-- **The recursion in two nodes.** Let the nodes $v_k$, $k \in s$, be distinct, and let
$i, j \in s$ with $i \neq j$. Then
$$f[v_k : k \in s] = \frac{f[v_k : k \in s \setminus \{j\}] - f[v_k : k \in s \setminus
  \{i\}]}{v_i - v_j}.$$

This is the coefficient of $X^{\# s - 1}$ in Mathlib's
`Lagrange.interpolate_eq_add_interpolate_erase`. -/
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

/-- **Adding a node (the Newton step).** Let $a \notin t$ and let the nodes $v_i$,
$i \in t \cup \{a\}$, be distinct. Then
$$\Pi_{t \cup \{a\}} f = \Pi_t f + f[v_i : i \in t \cup \{a\}] \, \omega_t,$$
where $\Pi_s f$ is the Lagrange interpolant of $f$ at the nodes indexed by $s$ and $\omega_t$ is
the nodal polynomial of $t$. -/
theorem interpolate_insert_eq_newtonOn {a : ι} {t : Finset ι}
    (hvs : Set.InjOn v ((insert a t : Finset ι) : Set ι)) (ha : a ∉ t) (f : F → F) :
    (Lagrange.interpolate (insert a t) v fun i => f (v i))
      = (Lagrange.interpolate t v fun i => f (v i))
        + C (newtonOn (insert a t) v f) * Lagrange.nodal t v := by
  rw [newtonOn_eq_coeff hvs, Finset.card_insert_of_notMem ha, Nat.add_sub_cancel]
  exact Lagrange.interpolate_insert_eq hvs ha _

/-- **The Newton divided difference formula over a linearly ordered index set.** Let the index set
be linearly ordered and let the nodes $v_i$, $i \in s$, be distinct. Then
$$\Pi_s f = \sum_{j \in s} f[v_i : i \in s, \, i \le j] \prod_{i \in s, \, i < j} (X - v_i).$$
-/
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

/-- **The reversed Newton formula.** Let the index set be linearly ordered and let the nodes $v_i$,
$i \in s$, be distinct. Then
$$\Pi_s f = \sum_{j \in s} f[v_i : i \in s, \, j \le i] \prod_{i \in s, \, j < i} (X - v_i).$$
This is the expansion built from the largest node down.

It is `DividedDifference.interpolate_eq_sum_newtonOn_mul_nodal` for the reversed order. -/
theorem interpolate_eq_sum_newtonOn_mul_nodal' [LinearOrder ι] (hvs : Set.InjOn v s)
    (f : F → F) :
    (Lagrange.interpolate s v fun i => f (v i))
      = ∑ j ∈ s, C (newtonOn (s.filter (j ≤ ·)) v f) * Lagrange.nodal (s.filter (j < ·)) v := by
  exact interpolate_eq_sum_newtonOn_mul_nodal (ι := ιᵒᵈ) hvs f

/-- For $j \le l$, the indices in $s$ below $j$ and the indices in $s$ above $l$ all differ from
$j$. -/
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

/-- **The Leibniz formula over a linearly ordered index set.** Let the index set be linearly ordered
and let the nodes $v_i$, $i \in s$, be distinct. Then
$$(gh)[v_i : i \in s] = \sum_{j \in s} g[v_i : i \in s, \, i \le j] \, h[v_i : i \in s, \, j \le
  i].$$

The proof is Steffensen's. The product of the Newton form of $\Pi_s g$ and the reversed Newton
form of $\Pi_s h$ is a double sum of terms $g[\dots, v_j] \, h[v_l, \dots] \, \omega_j
\omega'_l$. The terms with $j > l$ vanish at every node. The other terms form a polynomial of
degree less than $\# s$ that takes the values $gh$ at the nodes, so this polynomial is
$\Pi_s (gh)$, and its top coefficient comes from the terms with $j = l$ alone. -/
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

/-- **Divided differences of a Cauchy kernel.** Let the nodes $v_i$, $i \in s$, be distinct, let $s$
be nonempty, and let $z \neq v_i$ for every $i \in s$. Then for $f(t) = 1/(z - t)$,
$$f[v_i : i \in s] = \frac{1}{\prod_{i \in s} (z - v_i)}.$$

The proof is an induction on the index set with the recursion
`DividedDifference.newtonOn_eq_sub_div`. -/
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

/-! ### The divided difference at a multiset of nodes -/

section Multiset

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [DecidableEq 𝕜] {ι : Type*} [DecidableEq ι]

/-- **At distinct nodes, the multiset divided difference is the classical one.** Let $\mathbb{K}$ be
a nontrivially normed field and let the nodes $v_i \in \mathbb{K}$, $i \in s$, be distinct. Then
$f[v_i : i \in s]$ is `Hermite.divDiff f` at the multiset of the nodes $v_i$, $i \in s$.

Both are the coefficient of $X^{\# s - 1}$ of the interpolant of degree less than $\# s$, and at
simple nodes jet interpolation is Lagrange interpolation. -/
theorem newtonOn_eq_divDiff {s : Finset ι} {v : ι → 𝕜} (hvs : Set.InjOn v s) (f : 𝕜 → 𝕜) :
    newtonOn s v f = Hermite.divDiff f (s.val.map v) := by
  have hnd : (s.val.map v).Nodup := s.nodup.map_on fun i hi j hj h => hvs hi hj h
  have hcard : Multiset.card (s.val.map v) = s.card := by simp
  have hP : Lagrange.interpolate s v (fun i => f (v i))
      = Hermite.interpolateJet (s.val.map v) (Hermite.taylorJet f) := by
    refine Hermite.eq_interpolateJet (by rw [hcard]; exact Lagrange.degree_interpolate_lt _ hvs)
      (Hermite.isJetInterpolant_iff_coeff_taylor.mpr fun z hz j hj => ?_)
    rw [Multiset.count_eq_one_of_mem hnd hz, Nat.lt_one_iff] at hj
    subst hj
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hz
    rw [taylor_coeff_zero, Hermite.taylorJet_zero,
      Lagrange.eval_interpolate_at_node _ hvs (Finset.mem_def.mpr hi)]
  rw [newtonOn_eq_coeff hvs, hP, Hermite.divDiff, hcard]

end Multiset

/-! ### The `Fin`-indexed statements -/

section Fin

variable {m : ℕ}

/-- The first $k + 1$ nodes $x_0, \dots, x_k$ of the nodes $x_0, \dots, x_m$. -/
def prefixNodes (v : Fin (m + 1) → ℝ) (k : Fin (m + 1)) : Fin ((k : ℕ) + 1) → ℝ :=
  fun i => v (Fin.castLE k.isLt i)

/-- The last $m - k + 1$ nodes $x_k, \dots, x_m$ of the nodes $x_0, \dots, x_m$. -/
def suffixNodes (v : Fin (m + 1) → ℝ) (k : Fin (m + 1)) : Fin (m - k + 1) → ℝ :=
  fun i => v ⟨k + i, by have := k.isLt; have := i.isLt; omega⟩

/-- The nodal polynomial $\omega_k = \prod_{j < k} (X - x_j)$ of the first $k$ nodes, with
$\omega_0 = 1$. -/
noncomputable def prefixNodal (v : Fin (m + 1) → ℝ) (k : Fin (m + 1)) : ℝ[X] :=
  ∏ j : Fin (k : ℕ), (X - C (v (Fin.castLE k.isLt.le j)))

/-- The embedding $i \mapsto k + i$ of the indices $0, \dots, m - k$ of the suffix $x_k, \dots, x_m$
into the indices $0, \dots, m$. -/
def suffixEmb (m : ℕ) (k : Fin (m + 1)) : Fin (m - k + 1) ↪ Fin (m + 1) :=
  ⟨fun i => ⟨k + i, by have := k.isLt; have := i.isLt; omega⟩, fun i j hij => by
    have := congrArg Fin.val hij
    simp only at this
    exact Fin.ext (by omega)⟩

/-- The image of the prefix indices $0, \dots, k$ in the indices $0, \dots, m$ is the set of indices
$i \le k$. -/
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

/-- The image of the suffix indices under $i \mapsto k + i$ is the set of indices $i \ge k$. -/
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
    refine ⟨⟨i - k, by omega⟩, Fin.ext ?_⟩
    change (k : ℕ) + ((i : ℕ) - k) = i
    omega

/-- The image of the indices $0, \dots, k - 1$ in the indices $0, \dots, m$ is the set of indices
$i < k$. -/
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

/-- The divided difference $f[x_0, \dots, x_k]$ at the first $k + 1$ nodes is the divided difference
over the index set $\{i : i \le k\}$. -/
theorem newton_prefixNodes (f : ℝ → ℝ) (v : Fin (m + 1) → ℝ) (k : Fin (m + 1)) :
    newton f (prefixNodes v k) = newtonOn (univ.filter (· ≤ k)) v f := by
  rw [← map_castLEEmb_univ_eq_filter, newtonOn_map]
  rfl

/-- The divided difference $f[x_k, \dots, x_m]$ at the last nodes is the divided difference over the
index set $\{i : i \ge k\}$. -/
theorem newton_suffixNodes (f : ℝ → ℝ) (v : Fin (m + 1) → ℝ) (k : Fin (m + 1)) :
    newton f (suffixNodes v k) = newtonOn (univ.filter (k ≤ ·)) v f := by
  rw [← map_suffixEmb_univ_eq_filter, newtonOn_map]
  rfl

/-- The nodal polynomial $\omega_k$ of the first $k$ nodes is Mathlib's nodal polynomial over the
indices $i < k$. -/
theorem prefixNodal_eq_nodal (v : Fin (m + 1) → ℝ) (k : Fin (m + 1)) :
    prefixNodal v k = Lagrange.nodal (univ.filter (· < k)) v := by
  rw [← map_castLEEmb_univ_eq_filter_lt, Lagrange.nodal_map]
  rfl

/-- The nodal polynomial of all $m + 1$ nodes factors as $\omega_m (X - x_m)$. -/
theorem prefixNodal_last_mul (v : Fin (m + 1) → ℝ) :
    prefixNodal v (Fin.last m) * (X - C (v (Fin.last m))) = Lagrange.nodal univ v := by
  rw [Lagrange.nodal_eq, Fin.prod_univ_castSucc]
  rfl

/-- The divided difference $f[x_0]$ at a single node is $f(x_0)$. -/
@[simp]
theorem newton_zero (f : ℝ → ℝ) (v : Fin 1 → ℝ) : newton f v = f (v 0) := by
  have : (univ : Finset (Fin (0 + 1))) = {0} := by
    ext i
    simp [Fin.fin_one_eq_zero i]
  rw [newton_eq_newtonOn, this, newtonOn_singleton]

/-- The divided difference $f[x_1, \dots, x_{m+1}]$ at the nodes without the first one is the
divided difference over the index set $\{i : i \neq 0\}$. -/
theorem newton_tail (f : ℝ → ℝ) (v : Fin (m + 2) → ℝ) :
    newton f (Fin.tail v) = newtonOn (univ.erase 0) v f := by
  have : (univ : Finset (Fin (m + 2))).erase 0 = univ.map (Fin.succEmb (m + 1)) := by
    ext i
    simp [Fin.exists_succ_eq]
  rw [this, newtonOn_map]
  rfl

/-- The divided difference $f[x_0, \dots, x_m]$ at the nodes $x_0, \dots, x_{m+1}$ without the last
one is the divided difference over the index set $\{i : i \neq m + 1\}$. -/
theorem newton_init (f : ℝ → ℝ) (v : Fin (m + 2) → ℝ) :
    newton f (Fin.init v) = newtonOn (univ.erase (Fin.last (m + 1))) v f := by
  have : (univ : Finset (Fin (m + 2))).erase (Fin.last (m + 1))
      = univ.map (Fin.castSuccEmb (n := m + 1)) := by
    ext i
    simp [Fin.exists_castSucc_eq]
  rw [this, newtonOn_map]
  rfl

/-- **Adding a node.** Let $x_0, \dots, x_m, t$ be distinct real nodes. Then
$$\Pi_{m+1} f = \Pi_m f + f[x_0, \dots, x_m, t] \, \omega_{m+1},$$
where $\Pi_{m+1} f$ is the interpolant of $f$ at $x_0, \dots, x_m, t$, $\Pi_m f$ the interpolant
at $x_0, \dots, x_m$, and $\omega_{m+1} = \prod_{i=0}^m (X - x_i)$. This is (8.16) of
[quarteroni2000numerical]. -/
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

/-- **The divided difference as the coefficient of the new node.** Let $x_0, \dots, x_m, t$ be
distinct real nodes. Then
$$f[x_0, \dots, x_m, t] = \frac{f(t) - \Pi_m f(t)}{\prod_{i=0}^m (t - x_i)},$$
where $\Pi_m f$ is the interpolant of $f$ at $x_0, \dots, x_m$. This is the definition (8.14) of
the divided difference in [quarteroni2000numerical]. -/
theorem eval_interpolate_snoc_sub (f : ℝ → ℝ) {v : Fin (m + 1) → ℝ} {t : ℝ}
    (hv : Function.Injective (Fin.snoc v t : Fin (m + 2) → ℝ)) :
    newton f (Fin.snoc v t)
      = (f t - (Lagrange.interpolate univ v fun i => f (v i)).eval t) / ∏ i, (t - v i) := by
  obtain ⟨hv', ht⟩ := Fin.snoc_injective_iff.mp hv
  have ht' : ∀ i, v i ≠ t := fun i h => ht ⟨i, h⟩
  have hprod : ∏ i, (t - v i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr (ht' i).symm
  rw [sub_eval_interpolate_eq_newton f hv' ht', mul_div_cancel_left₀ _ hprod]

/-- **The Newton divided difference formula.** Let $x_0, \dots, x_m$ be distinct real nodes. Then
$$\Pi_m f = \sum_{k=0}^m f[x_0, \dots, x_k] \, \omega_k.$$
This is (8.17) of [quarteroni2000numerical]. -/
theorem interpolate_eq_sum_newton_mul_prefixNodal (f : ℝ → ℝ) {v : Fin (m + 1) → ℝ}
    (hv : Function.Injective v) :
    (Lagrange.interpolate univ v fun i => f (v i))
      = ∑ k : Fin (m + 1), C (newton f (prefixNodes v k)) * prefixNodal v k := by
  rw [interpolate_eq_sum_newtonOn_mul_nodal hv.injOn]
  exact Finset.sum_congr rfl fun k _ => by rw [newton_prefixNodes, prefixNodal_eq_nodal]

/-- **The recursion of divided differences.** Let $x_0, \dots, x_{m+1}$ be distinct real nodes. Then
$$f[x_0, \dots, x_{m+1}] = \frac{f[x_1, \dots, x_{m+1}] - f[x_0, \dots, x_m]}{x_{m+1} - x_0}.$$
This is (8.19) and Exercise 8.7 of [quarteroni2000numerical]. -/
theorem newton_succ (f : ℝ → ℝ) {v : Fin (m + 2) → ℝ} (hv : Function.Injective v) :
    newton f v
      = (newton f (Fin.tail v) - newton f (Fin.init v)) / (v (Fin.last (m + 1)) - v 0) := by
  rw [newton_tail, newton_init, newton_eq_newtonOn]
  exact newtonOn_eq_sub_div hv.injOn f (mem_univ _) (mem_univ _) (Fin.last_pos).ne'

/-- **Symmetry of divided differences.** For all real nodes $x_0, \dots, x_m$ and every permutation
$\sigma$ of the indices, $f[x_{\sigma(0)}, \dots, x_{\sigma(m)}] = f[x_0, \dots, x_m]$. This is
property 1 of §8.2.1 of [quarteroni2000numerical]. -/
theorem newton_comp_perm (f : ℝ → ℝ) (v : Fin (m + 1) → ℝ) (σ : Equiv.Perm (Fin (m + 1))) :
    newton f (v ∘ σ) = newton f v := by
  have h := newtonOn_map σ.toEmbedding univ v f
  rw [Finset.map_univ_equiv] at h
  rw [newton_eq_newtonOn, newton_eq_newtonOn, h]
  rfl

/-- **Linearity of divided differences, additivity.** For all real nodes $x_0, \dots, x_m$, $(f +
g)[x_0, \dots, x_m] = f[x_0, \dots, x_m] + g[x_0, \dots, x_m]$. This is property 2 of §8.2.1 of
[quarteroni2000numerical]. -/
theorem newton_add (f g : ℝ → ℝ) (v : Fin (m + 1) → ℝ) :
    newton (f + g) v = newton f v + newton g v :=
  newtonOn_add univ v f g

/-- **Linearity of divided differences, homogeneity.** For all real nodes $x_0, \dots, x_m$ and
$c \in \mathbb{R}$, $(cf)[x_0, \dots, x_m] = c \, f[x_0, \dots, x_m]$. This is property 2 of
§8.2.1 of [quarteroni2000numerical]. -/
theorem newton_smul (c : ℝ) (f : ℝ → ℝ) (v : Fin (m + 1) → ℝ) :
    newton (fun t => c * f t) v = c * newton f v :=
  newtonOn_smul univ v c f

/-- **The Leibniz formula.** Let $x_0, \dots, x_m$ be distinct real nodes. Then
$$(gh)[x_0, \dots, x_m] = \sum_{j=0}^m g[x_0, \dots, x_j] \, h[x_j, \dots, x_m].$$
This is property 3 of §8.2.1 of [quarteroni2000numerical]. -/
theorem newton_mul (g h : ℝ → ℝ) {v : Fin (m + 1) → ℝ} (hv : Function.Injective v) :
    newton (fun t => g t * h t) v
      = ∑ j : Fin (m + 1), newton g (prefixNodes v j) * newton h (suffixNodes v j) := by
  rw [newton_eq_newtonOn, newtonOn_mul hv.injOn]
  exact Finset.sum_congr rfl fun j _ => by rw [newton_prefixNodes, newton_suffixNodes]

/-- Let $x_0, \dots, x_m$ be distinct real nodes and let $p$ be a polynomial of degree at most $m$.
Then $p[x_0, \dots, x_m]$ is the coefficient of $X^m$ in $p$. -/
theorem newton_eval_eq_coeff {p : ℝ[X]} (hp : p.degree ≤ m) {v : Fin (m + 1) → ℝ}
    (hv : Function.Injective v) : newton (fun t => p.eval t) v = p.coeff m := by
  have hcard : (univ : Finset (Fin (m + 1))).card = m + 1 := by simp
  rw [newton_eq_newtonOn, newtonOn_eval_eq_coeff hv.injOn (by
    rw [hcard]; exact lt_of_le_of_lt hp (by exact_mod_cast Nat.lt_succ_self m)), hcard,
    Nat.add_sub_cancel]

/-- Let $x_0, \dots, x_m$ be distinct real nodes and let $p$ be a polynomial of degree less than
$m$. Then $p[x_0, \dots, x_m] = 0$. This is the remark after Example 8.3 in §8.2.1 of
[quarteroni2000numerical]. -/
theorem newton_eq_zero_of_degree_lt {p : ℝ[X]} (hp : p.degree < m) {v : Fin (m + 1) → ℝ}
    (hv : Function.Injective v) : newton (fun t => p.eval t) v = 0 := by
  rw [newton_eval_eq_coeff hp.le hv]
  exact coeff_eq_zero_of_degree_lt hp

/-- Let $x_0, \dots, x_m$ be distinct real nodes and let $p$ be a polynomial of degree $m$. Then
$p[x_0, \dots, x_m]$ is the leading coefficient of $p$. -/
theorem newton_eval_eq_leadingCoeff {p : ℝ[X]} (hp : p.degree = m) {v : Fin (m + 1) → ℝ}
    (hv : Function.Injective v) : newton (fun t => p.eval t) v = p.leadingCoeff := by
  rw [newton_eval_eq_coeff hp.le hv, leadingCoeff, natDegree_eq_of_degree_eq_some hp]

/-! ### The mean-value form -/

/-- **The mean value form of a divided difference, with an interior point.** Let $f$ be of class
$C^{m+1}$ on an open set $U \supseteq [a, b]$, and let $x_0, \dots, x_{m+1}$ be distinct nodes
in $[a, b]$. Then there is $\xi \in (a, b)$ with
$$f[x_0, \dots, x_{m+1}] = \frac{f^{(m+1)}(\xi)}{(m + 1)!}.$$
This is (8.21) of [quarteroni2000numerical] and Theorem 8.9 of [kress1998numerical].

The function $f - \Pi_{m+1} f$ vanishes at the $m + 2$ nodes, so by the generalized Rolle
theorem its derivative of order $m + 1$ vanishes somewhere, and this derivative is
$f^{(m+1)} - (m + 1)! \, f[x_0, \dots, x_{m+1}]$. -/
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

/-- **The mean value form of a divided difference.** Let $f$ be of class $C^m$ on an open set
$U \supseteq [a, b]$, and let $x_0, \dots, x_m$ be distinct nodes in $[a, b]$. Then there is
$\xi \in [a, b]$ with
$$f[x_0, \dots, x_m] = \frac{f^{(m)}(\xi)}{m!}.$$
This is (8.21) of [quarteroni2000numerical] and Theorem 8.9 of [kress1998numerical].

For $m = 0$ the divided difference is $f(x_0)$. For $m \ge 1$ the point $\xi$ can be taken in
$(a, b)$ (`DividedDifference.exists_newton_eq_iteratedDeriv_div_of_contDiffOn`). -/
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

/-- **The mean value form of a divided difference, for a globally smooth function.** Let
$f \in C^m(\mathbb{R})$ and let $x_0, \dots, x_m$ be distinct nodes in $[a, b]$. Then there is
$\xi \in [a, b]$ with $f[x_0, \dots, x_m] = f^{(m)}(\xi)/m!$. -/
theorem exists_newton_eq_iteratedDeriv_div_of_contDiff {a b : ℝ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ (m : WithTop ℕ∞) f) {v : Fin (m + 1) → ℝ} (hv : Function.Injective v)
    (hmem : ∀ i, v i ∈ Set.Icc a b) :
    ∃ ξ ∈ Set.Icc a b, newton f v = iteratedDeriv m f ξ / m.factorial :=
  exists_newton_eq_iteratedDeriv_div isOpen_univ (Set.subset_univ _) hf.contDiffOn hv hmem

/-- **A bound on a divided difference.** Let $f$ be of class $C^m$ on an open set
$U \supseteq [a, b]$, let $|f^{(m)}| \le M$ on $[a, b]$, and let $x_0, \dots, x_m$ be distinct
nodes in $[a, b]$. Then $|f[x_0, \dots, x_m]| \le M/m!$. -/
theorem abs_newton_le {a b : ℝ} {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hUsub : Set.Icc a b ⊆ U)
    (hf : ContDiffOn ℝ (m : WithTop ℕ∞) f U) {v : Fin (m + 1) → ℝ} (hv : Function.Injective v)
    (hmem : ∀ i, v i ∈ Set.Icc a b) {M : ℝ}
    (hM : ∀ t ∈ Set.Icc a b, |iteratedDeriv m f t| ≤ M) : |newton f v| ≤ M / m.factorial := by
  obtain ⟨ξ, hξ, h⟩ := exists_newton_eq_iteratedDeriv_div hU hUsub hf hv hmem
  rw [h, abs_div, abs_of_pos (by positivity : (0 : ℝ) < m.factorial)]
  exact div_le_div_of_nonneg_right (hM ξ hξ) (by positivity)

/-- **Divided differences of a Cauchy kernel.** Let $x_0, \dots, x_m$ be distinct real nodes and let
$z \in \mathbb{R}$ differ from every node. Then for $f(t) = 1/(z - t)$,
$$f[x_0, \dots, x_m] = \frac{1}{\prod_{i=0}^m (z - x_i)}.$$
This is the real-variable route to Runge's phenomenon of Example 8.1 of
[quarteroni2000numerical].

The same identity over any field is `DividedDifference.newtonOn_inv_sub`. -/
theorem newton_inv_sub {v : Fin (m + 1) → ℝ} (hv : Function.Injective v) {z : ℝ}
    (hz : ∀ i, z ≠ v i) : newton (fun t => 1 / (z - t)) v = 1 / ∏ i, (z - v i) :=
  newtonOn_inv_sub hv.injOn univ_nonempty fun i _ => hz i

/-! ### The derivative in the last node -/

/-- **The derivative of a divided difference in its last argument.** Let $x_0, \dots, x_n$ be
distinct real nodes, let $x$ differ from every node, and let $f$ be differentiable at $x$. Then
the function $y \mapsto f[x_0, \dots, x_n, y]$ has at $x$ the derivative
$$f[x_0, \dots, x_n, x, x],$$
the confluent divided difference: the coefficient of $X^{n+2}$ in the Hermite interpolant of $f$
at the simple nodes $x_0, \dots, x_n$ and the double node $x$. This is (9.22) and Exercise 9.4
of [quarteroni2000numerical].

The Hermite interpolant is `Hermite.interpolate` with the multiplicity $0$ at $x_0, \dots, x_n$
and $1$ at $x$. Near $x$ the function is $(f - \Pi_n f)/\omega_{n+1}$
(`DividedDifference.eval_interpolate_snoc_sub`), whose derivative follows from the quotient
rule. The Hermite interpolant $H$ is the Lagrange interpolant at $x_0, \dots, x_n, x$ plus
$c (X - x) \omega_{n+1}$, where $c$ is its top coefficient. The derivative of this identity at
$x$, where $H' = f'$, identifies $c$ with the derivative. -/
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

/-- The **confluent divided difference** at possibly repeated nodes, by recursion on the number of
nodes: $f[x_0] = f(x_0)$, and for $m + 2$ nodes
$$f[x_0, \dots, x_{m+1}] = \begin{cases} f^{(m+1)}(x_0)/(m + 1)! & \text{if } x_0 = x_{m+1}, \\
  \dfrac{f[x_1, \dots, x_{m+1}] - f[x_0, \dots, x_m]}{x_{m+1} - x_0} & \text{otherwise.}
  \end{cases}$$
For a nondecreasing family of nodes, the condition $x_0 = x_{m+1}$ says that all the nodes
coincide. This is Remark 8.3 of [quarteroni2000numerical], with a corrected value at coincident
nodes.

Remark 8.3 of [quarteroni2000numerical] gives the value $f^{(n+1)}(x_0)/(n + 1)!$ at $n + 1$
coincident nodes $x_0 = \dots = x_n$. The divided difference at these nodes is $f^{(n)}(x_0)/n!$
(for example, $f[x_0, x_0] = f'(x_0)$), and this is the value used here. -/
noncomputable def confluent (f : ℝ → ℝ) : {m : ℕ} → (Fin (m + 1) → ℝ) → ℝ
  | 0, v => f (v 0)
  | m + 1, v =>
    if v 0 = v (Fin.last (m + 1)) then iteratedDeriv (m + 1) f (v 0) / (m + 1).factorial
    else (confluent f (Fin.tail v) - confluent f (Fin.init v)) / (v (Fin.last (m + 1)) - v 0)

/-- The confluent divided difference at a single node $x_0$ is $f(x_0)$. -/
@[simp]
theorem confluent_zero (f : ℝ → ℝ) (v : Fin 1 → ℝ) : confluent f v = f (v 0) := rfl

/-- The recursion of the confluent divided difference at $m + 2$ nodes: the value is
$f^{(m+1)}(x_0)/(m + 1)!$ if $x_0 = x_{m+1}$, and $(f[x_1, \dots, x_{m+1}] - f[x_0, \dots,
x_m])/(x_{m+1} - x_0)$ otherwise. -/
theorem confluent_succ (f : ℝ → ℝ) (v : Fin (m + 2) → ℝ) :
    confluent f v = if v 0 = v (Fin.last (m + 1))
      then iteratedDeriv (m + 1) f (v 0) / (m + 1).factorial
      else (confluent f (Fin.tail v) - confluent f (Fin.init v)) / (v (Fin.last (m + 1)) - v 0) :=
  rfl

/-- At distinct real nodes, the confluent divided difference is the classical divided difference
`DividedDifference.newton`. -/
theorem confluent_eq_newton (f : ℝ → ℝ) {v : Fin (m + 1) → ℝ} (hv : Function.Injective v) :
    confluent f v = newton f v := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h0 : v 0 ≠ v (Fin.last (m + 1)) := fun h => absurd (hv h) (Fin.last_pos).ne
    rw [confluent_succ, ite_eq_right h0, ih (v := Fin.tail v) (hv.comp (Fin.succ_injective _)),
      ih (v := Fin.init v) (hv.comp (Fin.castSucc_injective _)), newton_succ f hv]

/-- At $m + 1$ copies of one node $x$, the confluent divided difference is $f^{(m)}(x)/m!$. -/
theorem confluent_const (f : ℝ → ℝ) (x : ℝ) :
    confluent f (fun _ : Fin (m + 1) => x) = iteratedDeriv m f x / m.factorial := by
  cases m with
  | zero => simp
  | succ m => rw [confluent_succ, ite_eq_left rfl]

/-- The multiset of the last $m + 1$ of $m + 2$ nodes is $x_{m+1}$ added to the multiset of
$x_1, \dots, x_m$. -/
private theorem univ_val_map_tail (v : Fin (m + 2) → ℝ) :
    (Finset.univ : Finset (Fin (m + 1))).val.map (Fin.tail v)
      = v (Fin.last _) ::ₘ (List.ofFn fun i : Fin m => v i.succ.castSucc : Multiset ℝ) := by
  rw [Fin.univ_val_map, List.ofFn_succ', List.concat_eq_append,
    Multiset.coe_eq_coe.mpr (List.perm_append_singleton _ _), ← Multiset.cons_coe]
  simp only [Fin.tail, Fin.succ_last, Fin.succ_castSucc]

/-- The multiset of the first $m + 1$ of $m + 2$ nodes is $x_0$ added to the multiset of
$x_1, \dots, x_m$. -/
private theorem univ_val_map_init (v : Fin (m + 2) → ℝ) :
    (Finset.univ : Finset (Fin (m + 1))).val.map (Fin.init v)
      = v 0 ::ₘ (List.ofFn fun i : Fin m => v i.succ.castSucc : Multiset ℝ) := by
  rw [Fin.univ_val_map, List.ofFn_succ]
  simp only [Fin.init, Fin.castSucc_zero]
  rfl

/-- **Confluent divided differences are multiset divided differences.** For every $f$ and every
nondecreasing tuple of real nodes $x_0 \le \dots \le x_m$, the confluent divided difference
$f[x_0, \dots, x_m]$ is `Hermite.divDiff f` at the multiset of the nodes.

No smoothness of $f$ is needed, since both sides read only the jets of $f$ at the nodes. The two
recursions are `Hermite.divDiff_replicate` and `Hermite.divDiff_cons_cons`. -/
theorem confluent_eq_divDiff (f : ℝ → ℝ) {v : Fin (m + 1) → ℝ} (hv : Monotone v) :
    confluent f v = Hermite.divDiff f ((Finset.univ : Finset (Fin (m + 1))).val.map v) := by
  induction m with
  | zero =>
    rw [confluent_zero, Fin.univ_val_map, List.ofFn_succ, List.ofFn_zero]
    exact (Hermite.divDiff_singleton f (v 0)).symm
  | succ m ih =>
    have hmap : (Finset.univ : Finset (Fin (m + 2))).val.map v
        = v (Fin.last _) ::ₘ v 0 ::ₘ
          (List.ofFn fun i : Fin m => v i.succ.castSucc : Multiset ℝ) := by
      rw [Fin.univ_val_map, List.ofFn_succ, ← Multiset.cons_coe]
      change v 0 ::ₘ (List.ofFn (Fin.tail v) : Multiset ℝ) = _
      rw [← Fin.univ_val_map, univ_val_map_tail, Multiset.cons_swap]
    rw [confluent_succ]
    split_ifs with h
    · have hc : ∀ i, v i = v 0 := fun i =>
        le_antisymm (h ▸ hv (Fin.le_last i)) (hv (Fin.zero_le i))
      have hrep : (Finset.univ : Finset (Fin (m + 2))).val.map v
          = Multiset.replicate (m + 2) (v 0) := by
        refine Multiset.eq_replicate.mpr ⟨by simp, fun b hb => ?_⟩
        obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hb
        exact hc i
      rw [hrep, Hermite.divDiff_replicate, Hermite.taylorJet]
    · rw [ih (v := Fin.tail v) (hv.comp Fin.strictMono_succ.monotone),
        ih (v := Fin.init v) (hv.comp Fin.strictMono_castSucc.monotone), univ_val_map_tail,
        univ_val_map_init, hmap, Hermite.divDiff_cons_cons f (Ne.symm h)]

/-- If the confluent divided difference over $m + 1$ nodes is continuous on the nondecreasing
tuples, then the one over $m + 2$ nodes is continuous, within the nondecreasing tuples, at every
nondecreasing tuple whose extreme nodes differ, because there it is a difference quotient with a
nonzero denominator on a whole neighbourhood. -/
private lemma continuousWithinAt_confluent_of_ne {f : ℝ → ℝ}
    (hC : ContinuousOn (fun w : Fin (m + 1) → ℝ => confluent f w) {w | Monotone w})
    {v : Fin (m + 2) → ℝ} (hv : Monotone v) (hne : v 0 ≠ v (Fin.last (m + 1))) :
    ContinuousWithinAt (fun u : Fin (m + 2) → ℝ => confluent f u) {u | Monotone u} v := by
  set S : Set (Fin (m + 2) → ℝ) := {u | Monotone u} with hS
  set T : Set (Fin (m + 1) → ℝ) := {w | Monotone w} with hT
  have htailc : Continuous fun u : Fin (m + 2) → ℝ => Fin.tail u :=
    continuous_pi fun i => continuous_apply _
  have hinitc : Continuous fun u : Fin (m + 2) → ℝ => Fin.init u :=
    continuous_pi fun i => continuous_apply _
  have htailm : Set.MapsTo (fun u : Fin (m + 2) → ℝ => Fin.tail u) S T :=
    fun u hu i j hij => hu (Fin.succ_le_succ_iff.mpr hij)
  have hinitm : Set.MapsTo (fun u : Fin (m + 2) → ℝ => Fin.init u) S T :=
    fun u hu i j hij => hu (Fin.castSucc_le_castSucc_iff.mpr hij)
  have h1 : ContinuousWithinAt (fun u : Fin (m + 2) → ℝ => confluent f (Fin.tail u)) S v :=
    ContinuousWithinAt.comp (hC _ (htailm hv)) htailc.continuousWithinAt htailm
  have h2 : ContinuousWithinAt (fun u : Fin (m + 2) → ℝ => confluent f (Fin.init u)) S v :=
    ContinuousWithinAt.comp (hC _ (hinitm hv)) hinitc.continuousWithinAt hinitm
  have h3 : ContinuousWithinAt (fun u : Fin (m + 2) → ℝ => u (Fin.last (m + 1)) - u 0) S v := by
    fun_prop
  have hden : v (Fin.last (m + 1)) - v 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hg : ContinuousWithinAt (fun u : Fin (m + 2) → ℝ =>
      (confluent f (Fin.tail u) - confluent f (Fin.init u)) / (u (Fin.last (m + 1)) - u 0)) S v :=
    (h1.sub h2).div h3 hden
  refine hg.congr_of_eventuallyEq ?_ ?_
  · have hO : IsOpen {u : Fin (m + 2) → ℝ | u 0 ≠ u (Fin.last (m + 1))} :=
      isOpen_ne_fun (continuous_apply _) (continuous_apply _)
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hO.mem_nhds hne)] with u hu
    rw [confluent_succ, ite_eq_right hu]
  · rw [confluent_succ, ite_eq_right hne]

/-- If $f$ is of class $C^{m+1}$ and the confluent divided difference over $m + 1$ nodes is
continuous on the nondecreasing tuples, then for every nondecreasing tuple
$x_0 \le \dots \le x_{m+1}$ there is $\xi \in [x_0, x_{m+1}]$ with $f[x_0, \dots, x_{m+1}] =
f^{(m+1)}(\xi)/(m + 1)!$; the proof approximates the tuple by strictly increasing tuples inside
$[x_0, x_{m+1}]$ and passes to the limit. -/
private lemma exists_confluent_eq_of_continuousOn {f : ℝ → ℝ}
    (hf : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) f)
    (hC : ContinuousOn (fun w : Fin (m + 1) → ℝ => confluent f w) {w | Monotone w})
    {v : Fin (m + 2) → ℝ} (hv : Monotone v) :
    ∃ ξ ∈ Set.Icc (v 0) (v (Fin.last (m + 1))),
      confluent f v = iteratedDeriv (m + 1) f ξ / (m + 1).factorial := by
  have hle : v 0 ≤ v (Fin.last (m + 1)) := hv (Fin.zero_le _)
  by_cases h0 : v 0 = v (Fin.last (m + 1))
  · exact ⟨v 0, ⟨le_rfl, hle⟩, by rw [confluent_succ, ite_eq_left h0]⟩
  have hab : v 0 < v (Fin.last (m + 1)) := lt_of_le_of_ne hle h0
  have hm3 : (0 : ℝ) < (m : ℝ) + 3 := by positivity
  -- a strictly increasing grid inside `[v 0, v (last)]`
  set g : Fin (m + 2) → ℝ :=
    fun i => v 0 + (v (Fin.last (m + 1)) - v 0) * ((i : ℝ) + 1) / ((m : ℝ) + 3) with hgdef
  have hgmono : StrictMono g := by
    intro i j hij
    have hij' : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast (hij : (i : ℕ) < (j : ℕ))
    simp only [hgdef]
    gcongr
  have hgmem : ∀ i, g i ∈ Set.Icc (v 0) (v (Fin.last (m + 1))) := by
    intro i
    have hi : ((i : ℕ) : ℝ) ≤ (m : ℝ) + 1 := by
      have := i.isLt
      have : (i : ℕ) ≤ m + 1 := by omega
      exact_mod_cast this
    constructor
    · simp only [hgdef]
      have : (0 : ℝ) ≤ (v (Fin.last (m + 1)) - v 0) * ((i : ℝ) + 1) / ((m : ℝ) + 3) := by
        positivity
      linarith
    · simp only [hgdef]
      have h1 : (v (Fin.last (m + 1)) - v 0) * ((i : ℝ) + 1) / ((m : ℝ) + 3)
          ≤ v (Fin.last (m + 1)) - v 0 := by
        rw [div_le_iff₀ hm3]
        nlinarith
      linarith
  have hvmem : ∀ i, v i ∈ Set.Icc (v 0) (v (Fin.last (m + 1))) :=
    fun i => ⟨hv (Fin.zero_le _), hv (Fin.le_last _)⟩
  -- the perturbed nodes: strictly increasing, and still inside `[v 0, v (last)]`
  set w : ℕ → Fin (m + 2) → ℝ :=
    fun n i => (1 - ((n : ℝ) + 1)⁻¹) * v i + ((n : ℝ) + 1)⁻¹ * g i with hwdef
  have heps : ∀ n : ℕ, 0 < ((n : ℝ) + 1)⁻¹ ∧ ((n : ℝ) + 1)⁻¹ ≤ 1 := by
    intro n
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact ⟨by positivity, by rw [inv_le_one₀ hn]; linarith [Nat.cast_nonneg (α := ℝ) n]⟩
  have hwmono : ∀ n, StrictMono (w n) := by
    intro n i j hij
    have hn := heps n
    have h1 : v i ≤ v j := hv hij.le
    have h2 : g i < g j := hgmono hij
    simp only [hwdef]
    nlinarith [hn.1, hn.2]
  have hwmem : ∀ n i, w n i ∈ Set.Icc (v 0) (v (Fin.last (m + 1))) := by
    intro n i
    have he := heps n
    have h1 := hvmem i
    have h2 := hgmem i
    constructor <;> simp only [hwdef] <;> nlinarith [he.1, he.2, h1.1, h1.2, h2.1, h2.2]
  have hwtend : Filter.Tendsto w Filter.atTop (nhds v) := by
    rw [tendsto_pi_nhds]
    intro i
    have h0 : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) Filter.atTop (nhds 0) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h1 : Filter.Tendsto (fun n : ℕ => (1 - ((n : ℝ) + 1)⁻¹) * v i + ((n : ℝ) + 1)⁻¹ * g i)
        Filter.atTop (nhds ((1 - 0) * v i + 0 * g i)) :=
      ((tendsto_const_nhds.sub h0).mul tendsto_const_nhds).add (h0.mul tendsto_const_nhds)
    simp only [hwdef]
    simpa using h1
  have hxi : ∀ n, ∃ ξ ∈ Set.Icc (v 0) (v (Fin.last (m + 1))),
      iteratedDeriv (m + 1) f ξ = ((m + 1).factorial : ℝ) * confluent f (w n) := by
    intro n
    obtain ⟨ξ, hξ, hval⟩ :=
      exists_newton_eq_iteratedDeriv_div_of_contDiff hf (hwmono n).injective (hwmem n)
    refine ⟨ξ, hξ, ?_⟩
    rw [confluent_eq_newton f (hwmono n).injective, hval]
    field_simp
  choose ξ hξmem hξval using hxi
  have hcont : Continuous (iteratedDeriv (m + 1) f) := hf.continuous_iteratedDeriv (m + 1) le_rfl
  have hlim : Filter.Tendsto (fun n => iteratedDeriv (m + 1) f (ξ n)) Filter.atTop
      (nhds (((m + 1).factorial : ℝ) * confluent f v)) := by
    simp only [hξval]
    refine Filter.Tendsto.const_mul _ ?_
    exact (continuousWithinAt_confluent_of_ne hC hv h0).tendsto.comp
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hwtend
        (Filter.Eventually.of_forall fun n => (hwmono n).monotone))
  have hclosed : IsClosed (iteratedDeriv (m + 1) f '' Set.Icc (v 0) (v (Fin.last (m + 1)))) :=
    (isCompact_Icc.image hcont).isClosed
  obtain ⟨ξ₀, hξ₀mem, hξ₀⟩ :=
    hclosed.mem_of_tendsto hlim (Filter.Eventually.of_forall fun n => ⟨ξ n, hξmem n, rfl⟩)
  refine ⟨ξ₀, hξ₀mem, ?_⟩
  rw [hξ₀]
  field_simp

/-- **Continuity of the confluent divided difference.** Let $f \in C^m(\mathbb{R})$. Then the map
$(x_0, \dots, x_m) \mapsto f[x_0, \dots, x_m]$ of `DividedDifference.confluent` is continuous on
the set of nondecreasing tuples. This is the continuity stated in Remark 8.3 of
[quarteroni2000numerical].

This makes `DividedDifference.confluent` the right extension of `DividedDifference.newton` to
coincident nodes: the nondecreasing tuples with distinct entries are dense in the nondecreasing
tuples, so `DividedDifference.confluent f` is the unique continuous extension of
`DividedDifference.newton f` from them. The proof is an induction on $m$. Where $x_0 \neq x_m$,
an open condition that covers every partially coincident tuple, the value is a difference
quotient of confluent divided differences over $m$ nodes, which are continuous by the induction
hypothesis. The induction hypothesis also gives the mean value form
$f[x_0, \dots, x_m] = f^{(m)}(\xi)/m!$ with $\xi \in [x_0, x_m]$. At a tuple $(c, \dots, c)$
with all nodes equal, where the value is $f^{(m)}(c)/m!$, this mean value form and the
continuity of $f^{(m)}$ give the continuity. -/
theorem continuous_confluent {f : ℝ → ℝ} (hf : ContDiff ℝ (m : WithTop ℕ∞) f) :
    ContinuousOn (fun v : Fin (m + 1) → ℝ => confluent f v) {v | Monotone v} := by
  induction m with
  | zero =>
    intro v _
    simp only [confluent_zero]
    exact (hf.continuous.comp (continuous_apply (0 : Fin 1))).continuousWithinAt
  | succ m ih =>
    have hC := ih (hf.of_le (by exact_mod_cast Nat.le_succ m))
    intro v hv
    by_cases h0 : v 0 = v (Fin.last (m + 1))
    · have hval : confluent f v = iteratedDeriv (m + 1) f (v 0) / (m + 1).factorial := by
        rw [confluent_succ, ite_eq_left h0]
      have hcont : Continuous (iteratedDeriv (m + 1) f) :=
        hf.continuous_iteratedDeriv (m + 1) le_rfl
      have hfac : (0 : ℝ) < ((m + 1).factorial : ℝ) := by positivity
      rw [ContinuousWithinAt, hval, Metric.tendsto_nhdsWithin_nhds]
      intro ε hε
      obtain ⟨δ, hδ, hδ'⟩ :=
        Metric.continuous_iff.mp hcont (v 0) (ε * ((m + 1).factorial : ℝ)) (by positivity)
      refine ⟨δ, hδ, fun u hu hud => ?_⟩
      obtain ⟨ξ, hξ, hξval⟩ := exists_confluent_eq_of_continuousOn hf hC hu
      have h1 : |u 0 - v 0| < δ := by
        have := dist_le_pi_dist u v 0
        rw [Real.dist_eq] at this
        linarith [this, hud]
      have h2 : |u (Fin.last (m + 1)) - v 0| < δ := by
        have := dist_le_pi_dist u v (Fin.last (m + 1))
        rw [Real.dist_eq, ← h0] at this
        linarith [this, hud]
      have h3 : dist ξ (v 0) < δ := by
        rw [Real.dist_eq, abs_lt]
        rw [abs_lt] at h1 h2
        exact ⟨by linarith [hξ.1], by linarith [hξ.2]⟩
      have h4 := hδ' ξ h3
      rw [Real.dist_eq] at h4 ⊢
      rw [hξval, div_sub_div_same, abs_div, abs_of_pos hfac, div_lt_iff₀ hfac]
      exact h4
    · exact continuousWithinAt_confluent_of_ne hC hv h0

/-- **The mean value form of a confluent divided difference.** Let $f \in C^m(\mathbb{R})$ and let
$x_0 \le \dots \le x_m$ be real nodes. Then there is $\xi \in [x_0, x_m]$ with
$$f[x_0, \dots, x_m] = \frac{f^{(m)}(\xi)}{m!}.$$
This is (8.21) together with Remark 8.3 of [quarteroni2000numerical].

At distinct nodes this is `DividedDifference.exists_newton_eq_iteratedDeriv_div`, and at
coincident nodes it is `DividedDifference.confluent_const`. The content of the theorem is that
the two cases fit together. -/
theorem exists_confluent_eq_iteratedDeriv_div {f : ℝ → ℝ} (hf : ContDiff ℝ (m : WithTop ℕ∞) f)
    {v : Fin (m + 1) → ℝ} (hv : Monotone v) :
    ∃ ξ ∈ Set.Icc (v 0) (v (Fin.last m)), confluent f v = iteratedDeriv m f ξ / m.factorial := by
  cases m with
  | zero => exact ⟨v 0, ⟨le_rfl, hv (Fin.zero_le _)⟩, by simp⟩
  | succ m =>
    exact exists_confluent_eq_of_continuousOn hf
      (continuous_confluent (hf.of_le (by exact_mod_cast Nat.le_succ m))) hv

end Fin


end DividedDifference

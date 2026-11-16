/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Lagrange`, or a sibling file (Mathlib's `Polynomial.hermite` is
the unrelated probabilists' Hermite polynomial, so the namespace would need renaming there).
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Hermite interpolation on a multiset of nodes

This module gives the algebraic half of Hermite interpolation, over a commutative ring and, for
existence and uniqueness, over a field. The nodes form a multiset $s$, and $\mu_s(x)$ denotes the
multiplicity of a node $x$ in $s$. A **jet** at $x$ is a sequence $y = (y_0, y_1, \dots)$ of
prescribed Taylor coefficients, and its truncated Taylor polynomial is
$T_m(y, x) = \sum_{j < m} y_j (X - x)^j$. A polynomial $p$ **interpolates** the jets $y(x)$ at the
nodes of $s$ if its first $\mu_s(x)$ Taylor coefficients at each node $x$ are
$y(x)_0, \dots, y(x)_{\mu_s(x) - 1}$, that is, if $(X - x)^{\mu_s(x)}$ divides
$p - T_{\mu_s(x)}(y(x), x)$. The **nodal polynomial** is $\omega_s = \prod_{x \in s} (X - x)$, monic
of degree $|s|$.

Over a field, exactly one polynomial of degree less than $|s|$ interpolates given jets at the nodes
of $s$. This is the companion of Mathlib's Lagrange interpolation in
`Mathlib.LinearAlgebra.Lagrange`, which is the case of a multiset without repetitions.

## Main definitions

* `Hermite.jetPoly`: the truncated Taylor polynomial $T_m(y, x) = \sum_{j < m} y_j (X - x)^j$ of a
  jet $y$ at $x$.
* `Hermite.nodalMultiset`: the nodal polynomial $\omega_s = \prod_{x \in s} (X - x)$ of a multiset
  $s$.
* `Hermite.IsJetInterpolant`: $p$ interpolates the jets $y(x)$ at the nodes of $s$, to the
  multiplicity of each node.
* `Hermite.interpolateJet`: the unique interpolant of degree less than $|s|$.

## Main results

* `Hermite.isJetInterpolant_iff_coeff_taylor`: $p$ interpolates the jets if and only if its first
  $\mu_s(x)$ Taylor coefficients at each node $x$ are the prescribed ones.
* `Hermite.existsUnique_isJetInterpolant`: unisolvence, exactly one polynomial of degree less than
  $|s|$ interpolates given jets.
* `Hermite.IsJetInterpolant.nodalMultiset_dvd_sub`: two interpolants of the same jets differ by a
  multiple of $\omega_s$.
* `Hermite.IsJetInterpolant.of_le`: an interpolant on $t$ is an interpolant on every sub-multiset of
  $t$.
* `Hermite.interpolateJet_congr`, `Hermite.interpolateJet_add`, `Hermite.interpolateJet_smul`: the
  interpolant depends only on the jet entries it uses, and it depends linearly on the jets.
* `Hermite.interpolateJet_cons_sub`: the Newton step, adding a node adds to the interpolant a
  multiple of the old nodal polynomial, and the multiple is the new leading coefficient.

## Proof outline

Existence is the Chinese remainder theorem in the Dedekind domain $K[X]$, for the pairwise distinct
prime ideals $(X - x)$ raised to the multiplicities, followed by reduction modulo $\omega_s$.
Uniqueness holds because the difference of two interpolants is divisible by $\omega_s$, which has
degree $|s|$.

## Implementation notes

* The interpolation condition is stated as a divisibility, so that it needs no assumption on the
  characteristic. The Taylor coefficients of $p$ at $x$ are the coefficients of
  `Polynomial.taylor x p`, which is $p(X + x)$.
* The jets and divided differences of functions in `Numlib.Analysis.Calculus.HermiteInterpolation`
  (`Hermite.taylorJet`, `Hermite.divDiff`), the primary functional calculus in
  `Numlib.Analysis.Normed.Algebra.PrimaryFunctionalCalculus.Basic`, and the real Hermite
  interpolation in `Numlib.Approximation.Hermite` use this module.
-/

open Polynomial

namespace Hermite

section CommRing

variable {R : Type*} [CommRing R]

/-! ### Jets and their Taylor polynomials -/

/-- The **truncated Taylor polynomial** of a jet $y = (y_0, y_1, \dots)$ at $x$, of order $m$:
$$T_m(y, x) = \sum_{j < m} y_j (X - x)^j.$$
-/
noncomputable def jetPoly (y : ℕ → R) (x : R) (m : ℕ) : R[X] :=
  ∑ j ∈ Finset.range m, C (y j) * (X - C x) ^ j

/-- The truncated Taylor polynomial of order $0$ is $0$. -/
@[simp]
theorem jetPoly_zero (y : ℕ → R) (x : R) : jetPoly y x 0 = 0 := by
  simp [jetPoly]

/-- The truncated Taylor polynomial of order $m + 1$ is $T_{m+1}(y, x) = T_m(y, x) + y_m (X - x)^m$.
-/
theorem jetPoly_succ (y : ℕ → R) (x : R) (m : ℕ) :
    jetPoly y x (m + 1) = jetPoly y x m + C (y m) * (X - C x) ^ m :=
  Finset.sum_range_succ _ _

/-- Seen from $x$, the truncated Taylor polynomial of a jet has the jet as its coefficients:
`Polynomial.taylor x` maps $T_m(y, x)$ to $\sum_{j < m} y_j X^j$. -/
theorem taylor_jetPoly (y : ℕ → R) (x : R) (m : ℕ) :
    taylor x (jetPoly y x m) = ∑ j ∈ Finset.range m, C (y j) * X ^ j := by
  simp [jetPoly, map_sum, taylor_mul, taylor_pow, taylor_X, taylor_C]

/-- The Taylor coefficient of order $j$ of $T_m(y, x)$ at $x$ is $y_j$ for $j < m$ and $0$ for
$j \ge m$. -/
theorem coeff_taylor_jetPoly (y : ℕ → R) (x : R) (m j : ℕ) :
    (taylor x (jetPoly y x m)).coeff j = if j < m then y j else 0 := by
  rw [taylor_jetPoly, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  simp [Finset.sum_ite_eq, Finset.mem_range]

/-- The truncated Taylor polynomial $T_m(y, x)$ depends only on the entries $y_0, \dots, y_{m-1}$ of
the jet. -/
theorem jetPoly_congr {y y' : ℕ → R} {x : R} {m : ℕ} (h : ∀ j < m, y j = y' j) :
    jetPoly y x m = jetPoly y' x m :=
  Finset.sum_congr rfl fun j hj => by rw [h j (Finset.mem_range.mp hj)]

/-- The truncated Taylor polynomial is additive in the jet:
$T_m(y + y', x) = T_m(y, x) + T_m(y', x)$. -/
theorem jetPoly_add (y y' : ℕ → R) (x : R) (m : ℕ) :
    jetPoly (y + y') x m = jetPoly y x m + jetPoly y' x m := by
  simp [jetPoly, add_mul, Finset.sum_add_distrib]

/-- The truncated Taylor polynomial is homogeneous in the jet: $T_m(c y, x) = c\, T_m(y, x)$. -/
theorem jetPoly_smul (c : R) (y : ℕ → R) (x : R) (m : ℕ) :
    jetPoly (c • y) x m = c • jetPoly y x m := by
  simp [jetPoly, Finset.smul_sum, smul_eq_C_mul, mul_assoc]

/-- For $m \le n$, the truncations of one jet at the orders $m$ and $n$ agree to order $m$:
$(X - x)^m$ divides $T_n(y, x) - T_m(y, x)$. -/
theorem pow_dvd_jetPoly_sub_jetPoly (y : ℕ → R) (x : R) {m n : ℕ} (h : m ≤ n) :
    (X - C x) ^ m ∣ jetPoly y x n - jetPoly y x m := by
  rw [jetPoly, jetPoly, ← Finset.sum_range_add_sum_Ico _ h, add_sub_cancel_left]
  exact Finset.dvd_sum fun j hj =>
    (pow_dvd_pow _ (Finset.mem_Ico.mp hj).1).mul_left _

/-- $(X - x)^m$ divides $q$ if and only if the first $m$ Taylor coefficients of $q$ at $x$ vanish,
that is, the coefficient of $X^j$ in `Polynomial.taylor x q` is $0$ for every $j < m$. -/
theorem pow_X_sub_C_dvd_iff {x : R} {m : ℕ} {q : R[X]} :
    (X - C x) ^ m ∣ q ↔ ∀ j < m, (taylor x q).coeff j = 0 := by
  have h : taylor x ((X - C x) ^ m) = X ^ m := by simp [taylor_pow, taylor_X]
  rw [← map_dvd_iff (taylorEquiv x)]
  change taylor x _ ∣ taylor x q ↔ _
  rw [h, X_pow_dvd_iff]

/-- The truncated Taylor polynomial $T_m(y, x)$ has degree less than $m$. For $m = 0$, it is the
zero polynomial, whose degree is $\bot$. -/
theorem degree_jetPoly_lt (y : ℕ → R) (x : R) (m : ℕ) : (jetPoly y x m).degree < m := by
  rw [← degree_taylor _ x, taylor_jetPoly, ← mem_degreeLT]
  exact Submodule.sum_mem _ fun j hj => mem_degreeLT.mpr
    ((degree_C_mul_X_pow_le j _).trans_lt (by exact_mod_cast Finset.mem_range.mp hj))

/-- Over a nontrivial ring, the coefficient of $X^m$ in $T_{m+1}(y, x)$ is $y_m$, the last entry of
the jet that is used. -/
theorem coeff_jetPoly_succ_self [Nontrivial R] (y : ℕ → R) (x : R) (m : ℕ) :
    (jetPoly y x (m + 1)).coeff m = y m := by
  have h1 : (jetPoly y x m).coeff m = 0 := coeff_eq_zero_of_degree_lt (degree_jetPoly_lt y x m)
  have hd : ((X - C x) ^ m).natDegree = m := by
    rw [(monic_X_sub_C x).natDegree_pow, natDegree_X_sub_C, mul_one]
  have h2 : ((X - C x) ^ m).coeff m = 1 := by
    have := ((monic_X_sub_C x).pow m).coeff_natDegree
    rwa [hd] at this
  rw [jetPoly_succ, coeff_add, h1, coeff_C_mul, h2, zero_add, mul_one]

/-! ### The nodal polynomial of a multiset -/

/-- The **nodal polynomial** of a multiset $s$ of nodes, each node counted with its multiplicity:
$$\omega_s = \prod_{x \in s} (X - x).$$
-/
noncomputable def nodalMultiset (s : Multiset R) : R[X] :=
  (s.map fun x => X - C x).prod

/-- The nodal polynomial of the empty multiset is $1$. -/
@[simp]
theorem nodalMultiset_zero : nodalMultiset (0 : Multiset R) = 1 := by
  simp [nodalMultiset]

/-- Adding a node $x$ to $s$ multiplies the nodal polynomial by $X - x$:
$\omega_{\{x\} + s} = (X - x)\, \omega_s$. -/
@[simp]
theorem nodalMultiset_cons (x : R) (s : Multiset R) :
    nodalMultiset (x ::ₘ s) = (X - C x) * nodalMultiset s := by
  simp [nodalMultiset]

/-- The nodal polynomial of a sum of multisets is the product:
$\omega_{s + t} = \omega_s\, \omega_t$. -/
theorem nodalMultiset_add (s t : Multiset R) :
    nodalMultiset (s + t) = nodalMultiset s * nodalMultiset t := by
  simp [nodalMultiset]

/-- The nodal polynomial of the single node $x$ is $X - x$. -/
@[simp]
theorem nodalMultiset_singleton (x : R) : nodalMultiset {x} = X - C x := by
  simp [nodalMultiset]

/-- The nodal polynomial of $k$ copies of $s$ is $\omega_s^k$. -/
theorem nodalMultiset_nsmul (k : ℕ) (s : Multiset R) :
    nodalMultiset (k • s) = nodalMultiset s ^ k := by
  simp [nodalMultiset, Multiset.map_nsmul, Multiset.prod_nsmul]

/-- The nodal polynomial of a finite sum of multisets $\sum_{i \in t} s_i$ is
$\prod_{i \in t} \omega_{s_i}$. -/
theorem nodalMultiset_sum {ι : Type*} (t : Finset ι) (s : ι → Multiset R) :
    nodalMultiset (∑ i ∈ t, s i) = ∏ i ∈ t, nodalMultiset (s i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, nodalMultiset_add, ih]

/-- The nodal polynomial is monic. -/
theorem monic_nodalMultiset (s : Multiset R) : (nodalMultiset s).Monic :=
  monic_multiset_prod_of_monic _ _ fun x _ => monic_X_sub_C x

/-- Over a nontrivial ring, the nodal polynomial $\omega_s$ has degree $|s|$, the number of nodes
counted with multiplicity (`Polynomial.natDegree` form). -/
@[simp]
theorem natDegree_nodalMultiset [Nontrivial R] (s : Multiset R) :
    (nodalMultiset s).natDegree = Multiset.card s :=
  natDegree_multiset_prod_X_sub_C_eq_card s

/-- Over a nontrivial ring, the nodal polynomial $\omega_s$ has degree $|s|$ (`Polynomial.degree`
form). -/
theorem degree_nodalMultiset [Nontrivial R] (s : Multiset R) :
    (nodalMultiset s).degree = Multiset.card s := by
  rw [degree_eq_natDegree (monic_nodalMultiset s).ne_zero, natDegree_nodalMultiset]

/-- The value of the nodal polynomial at $t$ is $\omega_s(t) = \prod_{x \in s} (t - x)$. -/
theorem eval_nodalMultiset (s : Multiset R) (t : R) :
    (nodalMultiset s).eval t = (s.map fun x => t - x).prod := by
  simp [nodalMultiset, eval_multiset_prod, Multiset.map_map]

/-- If $s \le t$ as multisets, then $\omega_s$ divides $\omega_t$. -/
theorem nodalMultiset_dvd_nodalMultiset {s t : Multiset R} (h : s ≤ t) :
    nodalMultiset s ∣ nodalMultiset t := by
  obtain ⟨u, rfl⟩ := Multiset.le_iff_exists_add.mp h
  rw [nodalMultiset_add]
  exact dvd_mul_right _ _

/-- The nodal polynomial grouped by distinct nodes: $\omega_s = \prod_x (X - x)^{\mu_s(x)}$, the
product over the distinct nodes $x$ of $s$. -/
theorem nodalMultiset_eq_prod_count [DecidableEq R] (s : Multiset R) :
    nodalMultiset s = ∏ x ∈ s.toFinset, (X - C x) ^ s.count x :=
  Finset.prod_multiset_map_count s _

/-- For every $x$, the power $(X - x)^{\mu_s(x)}$ divides the nodal polynomial $\omega_s$. -/
theorem pow_count_dvd_nodalMultiset [DecidableEq R] (s : Multiset R) (x : R) :
    (X - C x) ^ s.count x ∣ nodalMultiset s := by
  by_cases hx : x ∈ s
  · rw [nodalMultiset_eq_prod_count]
    exact Finset.dvd_prod_of_mem _ (Multiset.mem_toFinset.mpr hx)
  · rw [Multiset.count_eq_zero_of_notMem hx, pow_zero]
    exact one_dvd _

/-! ### Jet interpolation -/

variable [DecidableEq R]

/-- A polynomial $p$ **interpolates the jets** $y(x)$ at the nodes of a multiset $s$ if, for every
node $x$ of $s$,
$$(X - x)^{\mu_s(x)} \mid p - T_{\mu_s(x)}(y(x), x),$$
where $\mu_s(x)$ is the multiplicity of $x$ in $s$.

By `Hermite.isJetInterpolant_iff_coeff_taylor`, this says that the first $\mu_s(x)$ Taylor
coefficients of $p$ at $x$ are $y(x)_0, \dots, y(x)_{\mu_s(x)-1}$. For a multiset without
repetitions, it is Lagrange interpolation of the values $y(x)_0$. The jets are a function
`y : R → ℕ → R`, and $T_m(y(x), x)$ is `Hermite.jetPoly (y x) x m`. -/
def IsJetInterpolant (s : Multiset R) (y : R → ℕ → R) (p : R[X]) : Prop :=
  ∀ x ∈ s, (X - C x) ^ s.count x ∣ p - jetPoly (y x) x (s.count x)

/-- A polynomial $p$ interpolates the jets $y(x)$ at the nodes of $s$ if and only if, for every node
$x$ of $s$ and every $j < \mu_s(x)$, the Taylor coefficient of order $j$ of $p$ at $x$ is
$y(x)_j$. -/
theorem isJetInterpolant_iff_coeff_taylor {s : Multiset R} {y : R → ℕ → R} {p : R[X]} :
    IsJetInterpolant s y p ↔ ∀ x ∈ s, ∀ j < s.count x, (taylor x p).coeff j = y x j := by
  refine forall₂_congr fun x _ => ?_
  rw [pow_X_sub_C_dvd_iff]
  refine forall₂_congr fun j hj => ?_
  rw [map_sub, coeff_sub, coeff_taylor_jetPoly, ite_eq_left hj, sub_eq_zero]

/-- Every polynomial $p$ interpolates its own Taylor coefficients at the nodes of every multiset. -/
theorem isJetInterpolant_coeff_taylor (s : Multiset R) (p : R[X]) :
    IsJetInterpolant s (fun x j => (taylor x p).coeff j) p :=
  isJetInterpolant_iff_coeff_taylor.mpr fun _ _ _ _ => rfl

/-- Interpolation uses only the jet entries below the multiplicities: if $y(x)_j = y'(x)_j$ for
every node $x$ of $s$ and every $j < \mu_s(x)$, then $p$ interpolates $y$ if and only if it
interpolates $y'$. -/
theorem isJetInterpolant_congr {s : Multiset R} {y y' : R → ℕ → R}
    (h : ∀ x ∈ s, ∀ j < s.count x, y x j = y' x j) {p : R[X]} :
    IsJetInterpolant s y p ↔ IsJetInterpolant s y' p := by
  refine forall₂_congr fun x hx => ?_
  rw [jetPoly_congr (h x hx)]

/-- If $p$ interpolates the jets $y$ and $p'$ interpolates the jets $y'$ at the nodes of $s$, then
$p + p'$ interpolates $y + y'$. -/
theorem IsJetInterpolant.add {s : Multiset R} {y y' : R → ℕ → R} {p p' : R[X]}
    (hp : IsJetInterpolant s y p) (hp' : IsJetInterpolant s y' p') :
    IsJetInterpolant s (y + y') (p + p') := by
  intro x hx
  have h : p + p' - jetPoly ((y + y') x) x (s.count x)
      = (p - jetPoly (y x) x (s.count x)) + (p' - jetPoly (y' x) x (s.count x)) := by
    rw [Pi.add_apply, jetPoly_add]
    ring
  rw [h]
  exact dvd_add (hp x hx) (hp' x hx)

/-- If $p$ interpolates the jets $y$ at the nodes of $s$, then $c p$ interpolates $c y$ for every
scalar $c$. -/
theorem IsJetInterpolant.smul {s : Multiset R} {y : R → ℕ → R} {p : R[X]}
    (hp : IsJetInterpolant s y p) (c : R) : IsJetInterpolant s (c • y) (c • p) := by
  intro x hx
  rw [Pi.smul_apply, jetPoly_smul, ← smul_sub, smul_eq_C_mul]
  exact (hp x hx).mul_left _

/-- The zero polynomial interpolates the zero jets. -/
theorem isJetInterpolant_zero (s : Multiset R) : IsJetInterpolant s 0 0 := by
  intro x _
  simp [jetPoly]

/-- **Products of interpolants** interpolate the Cauchy products of the jets: if $p$ interpolates
$y$ and $q$ interpolates $z$ at the nodes of $s$, then $p q$ interpolates the jets $x \mapsto
\bigl(\sum_{i=0}^{n} y(x)_i\, z(x)_{n-i}\bigr)_n$. -/
theorem IsJetInterpolant.mul {s : Multiset R} {y z : R → ℕ → R} {p q : R[X]}
    (hp : IsJetInterpolant s y p) (hq : IsJetInterpolant s z q) :
    IsJetInterpolant s (fun x n => ∑ i ∈ Finset.range (n + 1), y x i * z x (n - i)) (p * q) := by
  rw [isJetInterpolant_iff_coeff_taylor] at hp hq ⊢
  intro x hx n hn
  rw [taylor_mul, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (taylor x p).coeff i * (taylor x q).coeff j)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  rw [hp x hx i (by omega), hq x hx (n - i) (by omega)]

/-- Finite sums of interpolants interpolate the sums of the jets: if $p_i$ interpolates $y_i$ at the
nodes of $s$ for every $i \in t$, then $\sum_{i \in t} p_i$ interpolates $\sum_{i \in t} y_i$. -/
theorem IsJetInterpolant.sum {ι : Type*} {s : Multiset R} (t : Finset ι) {y : ι → R → ℕ → R}
    {p : ι → R[X]} (h : ∀ i ∈ t, IsJetInterpolant s (y i) (p i)) :
    IsJetInterpolant s (∑ i ∈ t, y i) (∑ i ∈ t, p i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using isJetInterpolant_zero s
  | insert i t hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i t)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- **Restriction of an interpolant.** Let $s \le t$ be multisets of nodes. If $p$ interpolates the
jets $y$ at the nodes of $t$, then $p$ interpolates $y$ at the nodes of $s$. -/
theorem IsJetInterpolant.of_le {s t : Multiset R} {y : R → ℕ → R} {p : R[X]}
    (hp : IsJetInterpolant t y p) (hst : s ≤ t) : IsJetInterpolant s y p := by
  intro x hx
  have hc : s.count x ≤ t.count x := Multiset.count_le_of_le x hst
  have h : p - jetPoly (y x) x (s.count x)
      = (p - jetPoly (y x) x (t.count x))
        + (jetPoly (y x) x (t.count x) - jetPoly (y x) x (s.count x)) := by ring
  rw [h]
  exact dvd_add ((pow_dvd_pow _ hc).trans (hp x (Multiset.mem_of_le hst hx)))
    (pow_dvd_jetPoly_sub_jetPoly _ _ hc)

end CommRing

section Field

variable {K : Type*} [Field K]

/-- Over a field, the nodal polynomial $\omega_s$ splits. -/
theorem splits_nodalMultiset (s : Multiset K) : (nodalMultiset s).Splits :=
  Splits.multisetProd fun _ hf => by
    obtain ⟨x, -, rfl⟩ := Multiset.mem_map.mp hf
    exact Splits.X_sub_C x

/-- Over a field, the multiset of roots of the nodal polynomial $\omega_s$ is $s$. -/
@[simp]
theorem roots_nodalMultiset (s : Multiset K) : (nodalMultiset s).roots = s :=
  roots_multiset_prod_X_sub_C s

/-- Over a field, a monic polynomial that splits is the nodal polynomial of its multiset of roots.
-/
theorem eq_nodalMultiset_roots {p : K[X]} (hp : p.Monic) (hs : p.Splits) :
    p = nodalMultiset p.roots :=
  hs.eq_prod_roots_of_monic hp

variable [DecidableEq K]

/-- Over a field, $\omega_s$ divides $p$ if and only if $(X - x)^{\mu_s(x)}$ divides $p$ for every
node $x$ of $s$. -/
theorem nodalMultiset_dvd_iff {s : Multiset K} {p : K[X]} :
    nodalMultiset s ∣ p ↔ ∀ x ∈ s, (X - C x) ^ s.count x ∣ p := by
  refine ⟨fun h x _ => (pow_count_dvd_nodalMultiset s x).trans h, fun h => ?_⟩
  rw [nodalMultiset_eq_prod_count]
  refine Finset.prod_dvd_of_coprime (fun x _ x' _ hxx' => ?_)
    fun x hx => h x (Multiset.mem_toFinset.mp hx)
  exact (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hxx').isUnit).pow

/-- **Two interpolants of the same jets differ by a multiple of the nodal polynomial.** Let $K$ be a
field and $s$ a multiset of nodes in $K$. If $p$ and $q$ both interpolate the jets $y$ at the
nodes of $s$, then $\omega_s$ divides $p - q$. -/
theorem IsJetInterpolant.nodalMultiset_dvd_sub {s : Multiset K} {y : K → ℕ → K} {p q : K[X]}
    (hp : IsJetInterpolant s y p) (hq : IsJetInterpolant s y q) : nodalMultiset s ∣ p - q := by
  refine nodalMultiset_dvd_iff.mpr fun x hx => ?_
  have h : p - q = (p - jetPoly (y x) x (s.count x)) - (q - jetPoly (y x) x (s.count x)) := by
    ring
  rw [h]
  exact dvd_sub (hp x hx) (hq x hx)

/-- Over a field, a polynomial $p$ interpolates the zero jets at the nodes of $s$ if and only if
$\omega_s$ divides $p$. -/
theorem isJetInterpolant_zero_iff {s : Multiset K} {p : K[X]} :
    IsJetInterpolant s 0 p ↔ nodalMultiset s ∣ p := by
  refine ⟨fun h => by simpa using h.nodalMultiset_dvd_sub (isJetInterpolant_zero s), fun h => ?_⟩
  intro x hx
  simpa [jetPoly] using (pow_count_dvd_nodalMultiset s x).trans h

/-- Over a field, if $p$ interpolates the jets $y$ at the nodes of $s$ and $\omega_s$ divides
$p - q$, then $q$ also interpolates $y$. -/
theorem IsJetInterpolant.of_nodalMultiset_dvd_sub {s : Multiset K} {y : K → ℕ → K} {p q : K[X]}
    (hp : IsJetInterpolant s y p) (h : nodalMultiset s ∣ p - q) : IsJetInterpolant s y q := by
  intro x hx
  have e : q - jetPoly (y x) x (s.count x) = (p - jetPoly (y x) x (s.count x)) - (p - q) := by
    ring
  rw [e]
  exact dvd_sub (hp x hx) ((pow_count_dvd_nodalMultiset s x).trans h)

/-- Over a field, two polynomials that interpolate the same jets at the nodes of $s$ have the same
remainder modulo $\omega_s$. -/
theorem IsJetInterpolant.modByMonic_eq {s : Multiset K} {y : K → ℕ → K} {p q : K[X]}
    (hp : IsJetInterpolant s y p) (hq : IsJetInterpolant s y q) :
    p %ₘ nodalMultiset s = q %ₘ nodalMultiset s :=
  modByMonic_eq_of_dvd_sub (monic_nodalMultiset s) (hp.nodalMultiset_dvd_sub hq)

/-- Over a field, if $p$ interpolates the jets $y$ at the nodes of $s$, then so does the remainder
of $p$ modulo $\omega_s$. -/
theorem IsJetInterpolant.modByMonic {s : Multiset K} {y : K → ℕ → K} {p : K[X]}
    (hp : IsJetInterpolant s y p) : IsJetInterpolant s y (p %ₘ nodalMultiset s) :=
  hp.of_nodalMultiset_dvd_sub (by
    rw [← dvd_neg, neg_sub]
    exact dvd_modByMonic_sub p _)

/-- **Existence of an interpolant.** Over a field $K$, for every multiset $s$ of nodes and all jets
$y$, some polynomial interpolates $y$ at the nodes of $s$.

The proof applies the Chinese remainder theorem in the Dedekind domain $K[X]$ to the pairwise
distinct prime ideals $(X - x)$, raised to the multiplicities. -/
theorem exists_isJetInterpolant (s : Multiset K) (y : K → ℕ → K) :
    ∃ p : K[X], IsJetInterpolant s y p := by
  obtain ⟨p, hp⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal
    (s := s.toFinset) (fun x => Ideal.span {X - C x}) s.count
    (fun x _ => Ideal.prime_span_singleton_iff.mpr (prime_X_sub_C x))
    (fun x _ x' _ hxx' h => hxx' (by
      have := eq_of_monic_of_associated (monic_X_sub_C x) (monic_X_sub_C x')
        (Ideal.span_singleton_eq_span_singleton.mp h)
      simpa using congrArg (eval 0) this))
    (fun x => jetPoly (y x.1) x.1 (s.count x.1))
  refine ⟨p, fun x hx => ?_⟩
  have := hp x (Multiset.mem_toFinset.mpr hx)
  rwa [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at this

/-- **Unisolvence of Hermite interpolation on a multiset.** Let $K$ be a field, let $s$ be a
multiset of nodes in $K$, and let $y$ assign a jet $y(x)$ to each $x \in K$. Then exactly one
polynomial $p \in K[X]$ with $\deg p < |s|$ interpolates the jets $y(x)$ at the nodes of $s$.

Here $|s|$ is `Multiset.card s`, the number of nodes counted with multiplicity. Existence is
`Hermite.exists_isJetInterpolant` followed by reduction modulo $\omega_s$, and uniqueness is
`Hermite.IsJetInterpolant.nodalMultiset_dvd_sub`. -/
theorem existsUnique_isJetInterpolant (s : Multiset K) (y : K → ℕ → K) :
    ∃! p : K[X], p.degree < Multiset.card s ∧ IsJetInterpolant s y p := by
  obtain ⟨p, hp⟩ := exists_isJetInterpolant s y
  refine ⟨p %ₘ nodalMultiset s, ⟨?_, hp.modByMonic⟩, fun q ⟨hqdeg, hq⟩ => ?_⟩
  · rw [← degree_nodalMultiset]
    exact degree_modByMonic_lt _ (monic_nodalMultiset s)
  · rw [hq.modByMonic_eq hp |>.symm, (modByMonic_eq_self_iff (monic_nodalMultiset s)).mpr]
    rwa [degree_nodalMultiset]

/-- The **Hermite interpolant** of the jets $y$ on the multiset of nodes $s$: the unique polynomial
of degree less than $|s|$ that interpolates the jets $y(x)$ at the nodes of $s$
(`Hermite.existsUnique_isJetInterpolant`). -/
noncomputable def interpolateJet (s : Multiset K) (y : K → ℕ → K) : K[X] :=
  (existsUnique_isJetInterpolant s y).exists.choose

/-- The Hermite interpolant on $s$ has degree less than $|s|$. -/
theorem degree_interpolateJet_lt (s : Multiset K) (y : K → ℕ → K) :
    (interpolateJet s y).degree < Multiset.card s :=
  (existsUnique_isJetInterpolant s y).exists.choose_spec.1

/-- The Hermite interpolant of the jets $y$ on $s$ interpolates $y$ at the nodes of $s$. -/
theorem isJetInterpolant_interpolateJet (s : Multiset K) (y : K → ℕ → K) :
    IsJetInterpolant s y (interpolateJet s y) :=
  (existsUnique_isJetInterpolant s y).exists.choose_spec.2

/-- **Uniqueness of the Hermite interpolant.** Over a field, every polynomial $p$ with
$\deg p < |s|$ that interpolates the jets $y$ at the nodes of $s$ is the Hermite interpolant of
$y$ on $s$. -/
theorem eq_interpolateJet {s : Multiset K} {y : K → ℕ → K} {p : K[X]}
    (hdeg : p.degree < Multiset.card s) (hp : IsJetInterpolant s y p) :
    p = interpolateJet s y :=
  (existsUnique_isJetInterpolant s y).unique ⟨hdeg, hp⟩
    ⟨degree_interpolateJet_lt s y, isJetInterpolant_interpolateJet s y⟩

/-- Over a field, the remainder modulo $\omega_s$ of any interpolant of the jets $y$ at the nodes of
$s$ is the Hermite interpolant of $y$ on $s$. -/
theorem IsJetInterpolant.modByMonic_eq_interpolateJet {s : Multiset K} {y : K → ℕ → K}
    {p : K[X]} (hp : IsJetInterpolant s y p) : p %ₘ nodalMultiset s = interpolateJet s y := by
  refine eq_interpolateJet ?_ hp.modByMonic
  rw [← degree_nodalMultiset]
  exact degree_modByMonic_lt _ (monic_nodalMultiset s)

/-- Over a field, the Hermite interpolant of the Taylor coefficients of a polynomial $p$ on $s$ is
the remainder of $p$ modulo $\omega_s$. -/
theorem interpolateJet_coeff_taylor (s : Multiset K) (p : K[X]) :
    interpolateJet s (fun x j => (taylor x p).coeff j) = p %ₘ nodalMultiset s :=
  (isJetInterpolant_coeff_taylor s p).modByMonic_eq_interpolateJet.symm

/-- The **Hermite interpolant depends only on the jet entries it uses**. Over a field, if
$y(x)_j = y'(x)_j$ for every node $x$ of $s$ and every $j < \mu_s(x)$, then the Hermite
interpolants of $y$ and $y'$ on $s$ are equal. -/
theorem interpolateJet_congr {s : Multiset K} {y y' : K → ℕ → K}
    (h : ∀ x ∈ s, ∀ j < s.count x, y x j = y' x j) :
    interpolateJet s y = interpolateJet s y' :=
  eq_interpolateJet (degree_interpolateJet_lt s y)
    ((isJetInterpolant_congr h).mp (isJetInterpolant_interpolateJet s y))

/-- The Hermite interpolant is additive in the jets. -/
theorem interpolateJet_add (s : Multiset K) (y y' : K → ℕ → K) :
    interpolateJet s (y + y') = interpolateJet s y + interpolateJet s y' :=
  (eq_interpolateJet ((degree_add_le _ _).trans_lt
      (max_lt (degree_interpolateJet_lt s y) (degree_interpolateJet_lt s y')))
    ((isJetInterpolant_interpolateJet s y).add (isJetInterpolant_interpolateJet s y'))).symm

/-- The Hermite interpolant is homogeneous in the jets: the interpolant of $c y$ is $c$ times the
interpolant of $y$. -/
theorem interpolateJet_smul (s : Multiset K) (c : K) (y : K → ℕ → K) :
    interpolateJet s (c • y) = c • interpolateJet s y :=
  (eq_interpolateJet ((degree_smul_le _ _).trans_lt (degree_interpolateJet_lt s y))
    ((isJetInterpolant_interpolateJet s y).smul c)).symm

/-- The Hermite interpolant on the empty multiset of nodes is $0$. -/
@[simp]
theorem interpolateJet_zero (y : K → ℕ → K) : interpolateJet 0 y = 0 := by
  have h := degree_interpolateJet_lt 0 y
  rw [Multiset.card_zero, Nat.cast_zero, Nat.WithBot.lt_zero_iff, degree_eq_bot] at h
  exact h

/-- **The Newton step of Hermite interpolation.** Let $K$ be a field, let $s$ be a multiset of nodes
in $K$, let $x \in K$, and let $y$ be jets. Let $p_s$ and $p_{\{x\} + s}$ be the Hermite
interpolants of $y$ on $s$ and on $s$ with one more copy of $x$. Then
$$p_{\{x\} + s} - p_s = c\, \omega_s,$$
where $c$ is the coefficient of $X^{|s|}$ in $p_{\{x\} + s}$. -/
theorem interpolateJet_cons_sub (x : K) (s : Multiset K) (y : K → ℕ → K) :
    interpolateJet (x ::ₘ s) y - interpolateJet s y
      = C ((interpolateJet (x ::ₘ s) y).coeff (Multiset.card s)) * nodalMultiset s := by
  set P := interpolateJet (x ::ₘ s) y
  set I := interpolateJet s y
  obtain ⟨q, hq⟩ : nodalMultiset s ∣ P - I :=
    ((isJetInterpolant_interpolateJet _ y).of_le (Multiset.le_cons_self s x)).nodalMultiset_dvd_sub
      (isJetInterpolant_interpolateJet s y)
  have hIdeg : I.degree < Multiset.card s := degree_interpolateJet_lt s y
  have hPdeg : P.natDegree ≤ Multiset.card s := by
    have := degree_interpolateJet_lt (x ::ₘ s) y
    rw [Multiset.card_cons] at this
    exact natDegree_le_iff_coeff_eq_zero.mpr fun N hN =>
      (degree_lt_iff_coeff_zero _ _).mp this N (by omega)
  have hIcoeff : I.coeff (Multiset.card s) = 0 := coeff_eq_zero_of_degree_lt hIdeg
  have hqC : q = C (q.coeff 0) := by
    by_cases hq0 : q = 0
    · simp [hq0]
    refine eq_C_of_natDegree_eq_zero ?_
    have h1 : (P - I).natDegree ≤ Multiset.card s :=
      (natDegree_sub_le _ _).trans (max_le hPdeg (natDegree_le_of_degree_le hIdeg.le))
    rw [hq, (monic_nodalMultiset s).natDegree_mul' hq0, natDegree_nodalMultiset] at h1
    omega
  have hc : P.coeff (Multiset.card s) = q.coeff 0 := by
    have h := congrArg (coeff · (Multiset.card s)) hq
    simp only [coeff_sub, hIcoeff, sub_zero] at h
    rw [h, hqC, coeff_mul_C, coeff_C_zero, ← natDegree_nodalMultiset s,
      (monic_nodalMultiset s).coeff_natDegree, one_mul]
  rw [hq, hc, ← hqC, mul_comm]

end Field

end Hermite

/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Algebra.Polynomial.Derivative
import Numlib.Analysis.Calculus.HermiteInterpolation
import Numlib.Approximation.Interpolation

/-!
# Hermite interpolation

Hermite interpolation matches a function and some of its derivatives at finitely many nodes. Let
$x_1, \dots, x_n \in \mathbb{R}$ be distinct nodes and let $m_1, \dots, m_n \in \mathbb{N}$. The
Hermite interpolant of $f$ is the unique polynomial $p$ of degree less than $M = \sum_i (m_i + 1)$
with $p^{(j)}(x_i) = f^{(j)}(x_i)$ for all $i$ and all $j \le m_i$. Its error is carried by the
nodal polynomial $\prod_i (x - x_i)^{m_i + 1}$: for $f$ of class $C^{N+1}$ with $M = N + 1$,
$$f(t) - p(t) = \frac{f^{(N+1)}(\xi)}{(N + 1)!} \prod_i (t - x_i)^{m_i + 1}$$ for some $\xi$ in an
interval that contains the nodes and $t$. The material is [han2009theoretical], §3.2.2, and
[kress1998numerical], §8.1.

The main tool is Rolle's theorem with multiplicities. The module also identifies its real
interpolant with the multiset Hermite interpolation of
`Numlib.RingTheory.Polynomial.HermiteInterpolation`, which works over any field.

## Main definitions

* `Hermite.nodal`: the nodal polynomial $\prod_i (x - x_i)^{m_i + 1}$.
* `Hermite.nodeMultiset`: the multiset $\sum_i (m_i + 1) \cdot \{x_i\}$ of the nodes.
* `Hermite.interpolate`: the Hermite interpolant of $f$.

## Main results

* `Hermite.exists_iteratedDeriv_eq_zero`: **Rolle's theorem with multiplicities**. If a function of
  class $C^{N+1}$ has zeros in $[a, b]$ whose multiplicities sum to $N + 2$, then its derivative of
  order $N + 1$ vanishes somewhere in $[a, b]$.
* `Hermite.isUnisolvent`: the Hermite interpolation problem has exactly one solution of degree less
  than $M$.
* `Hermite.interpolate_eq_interpolateJet` and `Hermite.nodal_eq_nodalMultiset`: the real interpolant
  and the nodal polynomial are instances of the multiset constructions.
* `Hermite.degree_interpolate_lt`, `Hermite.eval_iterate_derivative_interpolate` and
  `Hermite.eq_interpolate`: the defining properties of the interpolant.
* `Hermite.interpolate_zero_eq_lagrange`: at simple nodes the Hermite interpolant is the Lagrange
  interpolant.
* `Hermite.exists_sub_interpolate_eq`: the error formula.
* `Hermite.eq_of_twoPoint_jets`: two polynomials of degree at most $2p + 1$ with the same
  derivatives of order at most $p$ at $0$ and at a point $s \neq 0$ are equal.

## Proof outline

Rolle's theorem with multiplicities is proved by induction on the order of the derivative: a zero of
multiplicity $k$ of $g$ is a zero of multiplicity $k - 1$ of $g'$, and each gap between two
consecutive distinct zeros contributes one more zero of $g'$ by Rolle's theorem. The error formula
then follows from it in the same way as the Lagrange error formula follows from the simple Rolle
theorem. Unique solvability is the Chinese remainder theorem in $\mathbb{R}[X]$, in the form
`Hermite.existsUnique_isJetInterpolant`.

## Implementation notes

* The nodes and the orders are `Fin n`-indexed functions `x` and `m`. The number $m_i$ is the
  highest order of a derivative that is matched at $x_i$, so $x_i$ has multiplicity $m_i + 1$.
* The multiset Hermite interpolation `Hermite.interpolateJet` of
  `Numlib.RingTheory.Polynomial.HermiteInterpolation`, and the jets `Hermite.taylorJet` and
  confluent divided differences `Hermite.divDiff` of
  `Numlib.Analysis.Calculus.HermiteInterpolation`, generalize the real interpolant of this module.
* The divided-difference form of the error and the Newton form of the interpolant are not developed
  here. The divided difference at distinct nodes is `DividedDifference.newtonOn` in
  `Numlib.Approximation.NewtonForm`, and at repeated nodes it is `Hermite.divDiff`.
-/

open scoped Polynomial

namespace Hermite

/-! ### Rolle's theorem with multiplicities -/

/-- The induction behind Rolle's theorem with multiplicities: if $F_{j+1}$ is the derivative of
$F_j$ for $j < k$, and $F_0$ vanishes to order $Z(t) \ge 1$ at each point $t$ of a finite set
$s \subseteq [a, b]$ with $\sum_{t \in s} Z(t) = k + 1$, then $F_k$ vanishes somewhere in
$[a, b]$. -/
private theorem exists_eq_zero_mult_aux {a b : ℝ} :
    ∀ (k : ℕ) (F : ℕ → ℝ → ℝ),
      (∀ j < k, ∀ t : ℝ, HasDerivAt (F j) (F (j + 1) t) t) →
      ∀ (s : Finset ℝ) (Z : ℝ → ℕ), (∀ t ∈ s, 1 ≤ Z t) → (∀ t ∈ s, t ∈ Set.Icc a b) →
        (∀ t ∈ s, ∀ j < Z t, F j t = 0) → ∑ t ∈ s, Z t = k + 1 →
        ∃ ξ ∈ Set.Icc a b, F k ξ = 0 := by
  intro k
  induction k with
  | zero =>
    intro F _ s Z hpos hsub hzero hsum
    obtain ⟨t, ht⟩ : s.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      simp at hsum
    exact ⟨t, hsub t ht, hzero t ht 0 (hpos t ht)⟩
  | succ k ih =>
    intro F hF s Z hpos hsub hzero hsum
    classical
    -- the nodes, in increasing order
    obtain ⟨p, hcard⟩ : ∃ p, s.card = p + 1 := by
      refine ⟨s.card - 1, ?_⟩
      have : s.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        rintro rfl
        simp at hsum
      have := Finset.card_pos.mpr this
      omega
    set y : Fin (p + 1) → ℝ := ⇑(s.orderEmbOfFin hcard) with hy
    have hymono : StrictMono y := (s.orderEmbOfFin hcard).strictMono
    have hymem : ∀ i, y i ∈ s := fun i => Finset.orderEmbOfFin_mem s hcard i
    have hyrange : ∀ t ∈ s, ∃ i, y i = t := by
      intro t ht
      have : t ∈ Set.range y := by
        rw [hy, Finset.range_orderEmbOfFin]
        exact ht
      exact this
    have hdiff0 : Differentiable ℝ (F 0) := fun t => (hF 0 (Nat.succ_pos k) t).differentiableAt
    have hcont : Continuous (F 0) := hdiff0.continuous
    -- one Rolle step in each gap
    have hrolle : ∀ i : Fin p, ∃ c ∈ Set.Ioo (y i.castSucc) (y i.succ), F 1 c = 0 := by
      intro i
      refine exists_hasDerivAt_eq_zero (f := F 0) (hymono (Fin.castSucc_lt_succ (i := i)))
        hcont.continuousOn ?_ fun t _ => hF 0 (Nat.succ_pos k) t
      rw [hzero _ (hymem _) 0 (hpos _ (hymem _)), hzero _ (hymem _) 0 (hpos _ (hymem _))]
    choose c hc hc0 using hrolle
    have hcmono : StrictMono c := by
      intro i j hij
      calc c i < y i.succ := (hc i).2
        _ ≤ y j.castSucc := hymono.monotone (by
            simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
            omega)
        _ < c j := (hc j).1
    have hcnots : ∀ i, c i ∉ s := by
      intro i hci
      obtain ⟨j, hj⟩ := hyrange _ hci
      have h1 : i.castSucc < j := hymono.lt_iff_lt.mp (hj ▸ (hc i).1)
      have h2 : j < i.succ := hymono.lt_iff_lt.mp (hj ▸ (hc i).2)
      simp only [Fin.lt_def, Fin.val_succ, Fin.val_castSucc] at h1 h2
      omega
    -- the nodes of `F 1`, with their multiplicities
    set G : Finset ℝ := Finset.image c Finset.univ with hG
    set s' : Finset ℝ := s.filter (fun t => 2 ≤ Z t) ∪ G with hs'
    set Z' : ℝ → ℕ := fun t => if t ∈ s then Z t - 1 else 1 with hZ'
    have hZ's : ∀ t ∈ s, Z' t = Z t - 1 := fun t ht => ite_eq_left ht
    have hZ'n : ∀ t ∉ s, Z' t = 1 := fun t ht => ite_eq_right ht
    have hGcard : G.card = p := by
      rw [hG, Finset.card_image_of_injective _ hcmono.injective, Finset.card_univ,
        Fintype.card_fin]
    have hGnots : ∀ t ∈ G, t ∉ s := by
      intro t ht
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
      exact hcnots i
    have hdisj : Disjoint (s.filter (fun t => 2 ≤ Z t)) G := by
      rw [Finset.disjoint_right]
      exact fun t ht htf => hGnots t ht (Finset.mem_filter.mp htf).1
    -- the orders available to `F 1` sum to `k + 1`
    have hsum' : ∑ t ∈ s', Z' t = k + 1 := by
      have hsplit : ∑ t ∈ s', Z' t
          = (∑ t ∈ s.filter (fun t => 2 ≤ Z t), Z' t) + ∑ t ∈ G, Z' t := by
        rw [hs', Finset.sum_union hdisj]
      have hG' : ∑ t ∈ G, Z' t = p := by
        rw [← hGcard, Finset.card_eq_sum_ones]
        exact Finset.sum_congr rfl fun t ht => hZ'n t (hGnots t ht)
      have hfil : ∑ t ∈ s.filter (fun t => 2 ≤ Z t), Z' t = ∑ t ∈ s, (Z t - 1) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [hZ's t ht]
        by_cases h2 : 2 ≤ Z t
        · rw [ite_eq_left h2]
        · rw [ite_eq_right h2]
          have := hpos t ht
          omega
      have hZsum : ∑ t ∈ s, (Z t - 1) + s.card = k + 2 := by
        rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib, ← hsum]
        refine Finset.sum_congr rfl fun t ht => ?_
        have := hpos t ht
        omega
      rw [hsplit, hfil, hG']
      omega
    have hpos' : ∀ t ∈ s', 1 ≤ Z' t := by
      intro t ht
      rcases Finset.mem_union.mp ht with ht | ht
      · obtain ⟨hts, h2⟩ := Finset.mem_filter.mp ht
        rw [hZ's t hts]
        omega
      · rw [hZ'n t (hGnots t ht)]
    have hsub' : ∀ t ∈ s', t ∈ Set.Icc a b := by
      intro t ht
      rcases Finset.mem_union.mp ht with ht | ht
      · exact hsub t (Finset.mem_filter.mp ht).1
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
        exact ⟨le_trans (hsub _ (hymem i.castSucc)).1 (hc i).1.le,
          le_trans (hc i).2.le (hsub _ (hymem i.succ)).2⟩
    have hzero' : ∀ t ∈ s', ∀ j < Z' t, F (j + 1) t = 0 := by
      intro t ht j hj
      rcases Finset.mem_union.mp ht with ht | ht
      · obtain ⟨hts, -⟩ := Finset.mem_filter.mp ht
        rw [hZ's t hts] at hj
        exact hzero t hts (j + 1) (by omega)
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
        rw [hZ'n _ (hcnots i)] at hj
        interval_cases j
        exact hc0 i
    obtain ⟨ξ, hξ, hξ0⟩ := ih (fun j => F (j + 1))
      (fun j hj t => hF (j + 1) (by omega) t) s' Z' hpos' hsub' hzero' hsum'
    exact ⟨ξ, hξ, hξ0⟩

/-- **Rolle's theorem with multiplicities.** Let $g : \mathbb{R} \to \mathbb{R}$ be of class
$C^{N+1}$. Let $x_1, \dots, x_n$ be distinct points of $[a, b]$ and let
$m_1, \dots, m_n \in \mathbb{N}$ with $\sum_i (m_i + 1) = N + 2$. If $g^{(j)}(x_i) = 0$ for all
$i$ and all $j \le m_i$, then there is $\xi \in [a, b]$ with $$g^{(N+1)}(\xi) = 0.$$ See
[kress1998numerical], §8.1, and [han2009theoretical], §3.2.2.

For $m = 0$ and $n = N + 2$ this is `exists_iteratedDeriv_eq_zero_of_forall_eq_zero`, whose
conclusion gives the sharper $\xi \in (a, b)$. With multiplicities the open interval is not
possible, since a single node of multiplicity $N + 2$ can be an endpoint. The derivatives are
`iteratedDeriv`. -/
theorem exists_iteratedDeriv_eq_zero {N n : ℕ} {a b : ℝ} {g : ℝ → ℝ}
    (hg : ContDiff ℝ ((N + 1 : ℕ) : WithTop ℕ∞) g) {x : Fin n → ℝ}
    (hx : Function.Injective x) (hmem : ∀ i, x i ∈ Set.Icc a b) {m : Fin n → ℕ}
    (hsum : ∑ i, (m i + 1) = N + 2)
    (hzero : ∀ i, ∀ j ≤ m i, iteratedDeriv j g (x i) = 0) :
    ∃ ξ ∈ Set.Icc a b, iteratedDeriv (N + 1) g ξ = 0 := by
  classical
  -- the successive derivatives of `g`
  have hdiff : ∀ j < N + 1, Differentiable ℝ (iteratedDeriv j g) := fun j hj =>
    hg.differentiable_iteratedDeriv j (by exact_mod_cast hj)
  have hstep : ∀ j < N + 1, ∀ t : ℝ,
      HasDerivAt (iteratedDeriv j g) (iteratedDeriv (j + 1) g t) t := by
    intro j hj t
    have h := ((hdiff j hj) t).hasDerivAt
    rwa [← iteratedDeriv_succ] at h
  -- the multiplicity function of the nodes
  set s : Finset ℝ := Finset.image x Finset.univ with hs
  set Z : ℝ → ℕ := fun t => ∑ i, if x i = t then m i + 1 else 0 with hZ
  have hZx : ∀ i, Z (x i) = m i + 1 := by
    intro i
    rw [hZ]
    simp only
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [ite_eq_right fun h => hj (hx h)]
    · simp
  refine exists_eq_zero_mult_aux (N + 1) (fun j => iteratedDeriv j g) hstep s Z ?_ ?_ ?_ ?_
  · rintro t ht
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
    rw [hZx]
    omega
  · rintro t ht
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
    exact hmem i
  · rintro t ht j hj
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
    rw [hZx] at hj
    exact hzero i j (by omega)
  · rw [hs, Finset.sum_image fun i _ j _ h => hx h]
    simpa only [hZx] using hsum

/-! ### The nodal polynomial -/

section Nodal

variable {n : ℕ}

/-- The **nodal polynomial** of distinct nodes $x_1, \dots, x_n$ with orders $m_1, \dots, m_n$ is
the monic polynomial $$\prod_i (x - x_i)^{m_i + 1}$$ of degree $\sum_i (m_i + 1)$. It vanishes
at $x_i$ together with its derivatives of order at most $m_i$, and it carries the error of
Hermite interpolation. -/
noncomputable def nodal (x : Fin n → ℝ) (m : Fin n → ℕ) : ℝ[X] :=
  ∏ i, (Polynomial.X - Polynomial.C (x i)) ^ (m i + 1)

/-- The nodal polynomial $\prod_i (x - x_i)^{m_i + 1}$ is monic. -/
theorem monic_nodal (x : Fin n → ℝ) (m : Fin n → ℕ) : (nodal x m).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun i _ => (Polynomial.monic_X_sub_C (x i)).pow _

/-- The nodal polynomial $\prod_i (x - x_i)^{m_i + 1}$ has degree $\sum_i (m_i + 1)$, the total
number of interpolation conditions. -/
theorem natDegree_nodal (x : Fin n → ℝ) (m : Fin n → ℕ) :
    (nodal x m).natDegree = ∑ i, (m i + 1) := by
  rw [nodal, Polynomial.natDegree_prod _ _ fun i _ =>
    ((Polynomial.monic_X_sub_C (x i)).pow _).ne_zero]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]

/-- The value of the nodal polynomial at $t$ is $\prod_i (t - x_i)^{m_i + 1}$. -/
@[simp]
theorem eval_nodal (x : Fin n → ℝ) (m : Fin n → ℕ) (t : ℝ) :
    (nodal x m).eval t = ∏ i, (t - x i) ^ (m i + 1) := by
  simp [nodal, Polynomial.eval_prod]

/-- For each node $x_i$, the factor $(x - x_i)^{m_i + 1}$ divides the nodal polynomial. -/
theorem pow_dvd_nodal (x : Fin n → ℝ) (m : Fin n → ℕ) (i : Fin n) :
    (Polynomial.X - Polynomial.C (x i)) ^ (m i + 1) ∣ nodal x m :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

/-- For each node $x_i$ and each $j \le m_i$, the derivative of order $j$ of the nodal polynomial
vanishes at $x_i$. -/
theorem eval_iterate_derivative_nodal {x : Fin n → ℝ} {m : Fin n → ℕ} (i : Fin n) {j : ℕ}
    (hj : j ≤ m i) : (Polynomial.derivative^[j] (nodal x m)).eval (x i) = 0 := by
  have hdvd : (Polynomial.X - Polynomial.C (x i)) ^ (m i + 1 - j) ∣
      Polynomial.derivative^[j] (nodal x m) :=
    Polynomial.pow_sub_dvd_iterate_derivative_of_pow_dvd j (pow_dvd_nodal x m i)
  have hone : (Polynomial.X - Polynomial.C (x i)) ∣ Polynomial.derivative^[j] (nodal x m) :=
    (dvd_pow_self _ (by omega)).trans hdvd
  exact Polynomial.dvd_iff_isRoot.mp hone

/-- If $\sum_i (m_i + 1) = M$, the derivative of order $M$ of the nodal polynomial is the constant
$M!$. -/
theorem iterate_derivative_nodal (x : Fin n → ℝ) (m : Fin n → ℕ) {M : ℕ}
    (hM : ∑ i, (m i + 1) = M) :
    Polynomial.derivative^[M] (nodal x m) = Polynomial.C ((M.factorial : ℝ)) := by
  have hdeg : (nodal x m).natDegree = M := (natDegree_nodal x m).trans hM
  rw [Polynomial.iterate_derivative_eq_C_of_natDegree_eq hdeg, (monic_nodal x m).leadingCoeff,
    mul_one]

end Nodal

/-! ### Unique solvability of the Hermite problem -/

section Unisolvent

variable {n : ℕ}

/-- The multiset of the nodes $x_i$ with the multiplicities $m_i + 1$:
$\sum_i (m_i + 1) \cdot \{x_i\}$. It connects the `Fin`-indexed data of this module to the
multiset Hermite interpolation of `Numlib.RingTheory.Polynomial.HermiteInterpolation`. -/
noncomputable def nodeMultiset (x : Fin n → ℝ) (m : Fin n → ℕ) : Multiset ℝ :=
  ∑ i, (m i + 1) • {x i}

/-- The multiset of the nodes has $\sum_i (m_i + 1)$ elements. -/
@[simp]
theorem card_nodeMultiset (x : Fin n → ℝ) (m : Fin n → ℕ) :
    Multiset.card (nodeMultiset x m) = ∑ i, (m i + 1) := by
  simp [nodeMultiset, Multiset.card_sum]

/-- A real number $t$ is in the multiset of the nodes if and only if $t = x_i$ for some $i$. -/
theorem mem_nodeMultiset {x : Fin n → ℝ} {m : Fin n → ℕ} {t : ℝ} :
    t ∈ nodeMultiset x m ↔ ∃ i, x i = t := by
  simp [nodeMultiset, Multiset.mem_sum, Multiset.mem_nsmul, eq_comm]

/-- If the nodes are distinct, the node $x_i$ occurs $m_i + 1$ times in the multiset of the nodes.
-/
theorem count_nodeMultiset {x : Fin n → ℝ} (hx : Function.Injective x) (m : Fin n → ℕ)
    (i : Fin n) : (nodeMultiset x m).count (x i) = m i + 1 := by
  classical
  rw [nodeMultiset, Multiset.count_sum', Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    rw [Multiset.count_nsmul, Multiset.count_singleton, ite_eq_right (fun h => hk (hx h).symm),
      mul_zero]
  · simp

/-- The nodal polynomial $\prod_i (x - x_i)^{m_i + 1}$ is the nodal polynomial
`Hermite.nodalMultiset` of the multiset of the nodes. -/
theorem nodal_eq_nodalMultiset (x : Fin n → ℝ) (m : Fin n → ℕ) :
    nodal x m = Hermite.nodalMultiset (nodeMultiset x m) := by
  simp [nodal, nodeMultiset, nodalMultiset_sum, nodalMultiset_nsmul]

/-- Let the nodes $x_i$ be distinct. A polynomial $p$ interpolates the jets $y$ on the multiset of
the nodes if and only if, for all $i$ and all $j \le m_i$, the Taylor coefficient of order $j$
of $p$ at $x_i$ is $y(x_i, j)$. -/
theorem isJetInterpolant_nodeMultiset_iff {x : Fin n → ℝ} (hx : Function.Injective x)
    {m : Fin n → ℕ} {y : ℝ → ℕ → ℝ} {p : ℝ[X]} :
    IsJetInterpolant (nodeMultiset x m) y p ↔
      ∀ i, ∀ j ≤ m i, (Polynomial.taylor (x i) p).coeff j = y (x i) j := by
  classical
  rw [isJetInterpolant_iff_coeff_taylor]
  constructor
  · intro h i j hj
    exact h (x i) (mem_nodeMultiset.mpr ⟨i, rfl⟩) j (by rw [count_nodeMultiset hx]; omega)
  · intro h t ht j hj
    obtain ⟨i, rfl⟩ := mem_nodeMultiset.mp ht
    rw [count_nodeMultiset hx] at hj
    exact h i j (by omega)

/-- **Unisolvence of the Hermite interpolation problem.** Let $x_1, \dots, x_n$ be distinct real
nodes, let $m_1, \dots, m_n \in \mathbb{N}$ with $\sum_i (m_i + 1) = M$, and let
$y_{ij} \in \mathbb{R}$. Then there is exactly one polynomial $p$ of degree less than $M$ with
$$p^{(j)}(x_i) = y_{ij} \qquad \text{for all } i \text{ and all } j \le m_i.$$ See
[han2009theoretical], §3.2.2 and (3.2.6).

This is the instance of `Hermite.existsUnique_isJetInterpolant` for the multiset
`Hermite.nodeMultiset x m` and the jets $y_{ij}/j!$. -/
theorem isUnisolvent {M : ℕ} {x : Fin n → ℝ} (hx : Function.Injective x) {m : Fin n → ℕ}
    (hM : ∑ i, (m i + 1) = M) (y : Fin n → ℕ → ℝ) :
    ∃! p : ℝ[X], p.degree < (M : WithBot ℕ) ∧
      ∀ i, ∀ j ≤ m i, (Polynomial.derivative^[j] p).eval (x i) = y i j := by
  classical
  set yJ : ℝ → ℕ → ℝ := fun t j =>
    if h : ∃ i, x i = t then y h.choose j / j.factorial else 0
  have hyJ : ∀ i j, yJ (x i) j = y i j / j.factorial := fun i j => by
    have h : ∃ k, x k = x i := ⟨i, rfl⟩
    simp only [yJ, h, ↓reduceDIte, hx h.choose_spec]
  have hiff : ∀ p : ℝ[X], IsJetInterpolant (nodeMultiset x m) yJ p ↔
      ∀ i, ∀ j ≤ m i, (Polynomial.derivative^[j] p).eval (x i) = y i j := fun p => by
    rw [isJetInterpolant_nodeMultiset_iff hx]
    refine forall_congr' fun i => forall₂_congr fun j _ => ?_
    have hj : (j.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
    rw [coeff_taylor_eq_eval_iterate_derivative_div, hyJ, div_left_inj' hj]
  obtain ⟨p, ⟨hpdeg, hp⟩, huniq⟩ := existsUnique_isJetInterpolant (nodeMultiset x m) yJ
  rw [card_nodeMultiset, hM] at hpdeg
  refine ⟨p, ⟨hpdeg, (hiff p).mp hp⟩, fun q ⟨hqdeg, hq⟩ => huniq q ⟨?_, (hiff q).mpr hq⟩⟩
  rwa [card_nodeMultiset, hM]

/-- Let $x_1, \dots, x_n$ be distinct real nodes and let $m_1, \dots, m_n \in \mathbb{N}$ with
$\sum_i (m_i + 1) = M$. If a polynomial $p$ of degree less than $M$ satisfies $p^{(j)}(x_i) = 0$
for all $i$ and all $j \le m_i$, then $p = 0$. This is the uniqueness half of
`Hermite.isUnisolvent`. -/
theorem eq_zero_of_forall_eval_iterate_derivative_eq_zero {M : ℕ} {x : Fin n → ℝ}
    (hx : Function.Injective x) {m : Fin n → ℕ} (hM : ∑ i, (m i + 1) = M) {p : ℝ[X]}
    (hdeg : p.degree < (M : WithBot ℕ))
    (hzero : ∀ i, ∀ j ≤ m i, (Polynomial.derivative^[j] p).eval (x i) = 0) : p = 0 :=
  (isUnisolvent hx hM fun _ _ => 0).unique ⟨hdeg, hzero⟩
    ⟨by simp, fun i j _ => by simp⟩

end Unisolvent

/-! ### The Hermite interpolant -/

section Interpolate

variable {n : ℕ} {x : Fin n → ℝ} {m : Fin n → ℕ} {f : ℝ → ℝ}

open scoped Classical in
/-- **The Hermite interpolant** of $f : \mathbb{R} \to \mathbb{R}$ at distinct nodes
$x_1, \dots, x_n$ with orders $m_1, \dots, m_n$: the unique polynomial $p$ of degree less than
$\sum_i (m_i + 1)$ with $p^{(j)}(x_i) = f^{(j)}(x_i)$ for all $i$ and all $j \le m_i$. See
[han2009theoretical], §3.2.2.

The definition is the multiset interpolant `Hermite.interpolateJet` of the Taylor jets of $f$ on
the multiset of the nodes (`Hermite.interpolate_eq_interpolateJet`). For $m = 0$ it is
`Lagrange.interpolate` (`Hermite.interpolate_zero_eq_lagrange`). If the nodes are not distinct,
the Lean value is $0$; the interpolation problem then has no solution in general. -/
noncomputable def interpolate (x : Fin n → ℝ) (m : Fin n → ℕ) (f : ℝ → ℝ) : ℝ[X] :=
  if Function.Injective x then interpolateJet (nodeMultiset x m) (taylorJet f) else 0

/-- **The real Hermite interpolant is the multiset interpolant.** If the nodes $x_i$ are distinct,
the Hermite interpolant of $f$ is `Hermite.interpolateJet` of the Taylor jets of $f$ on the
multiset $\sum_i (m_i + 1) \cdot \{x_i\}$. -/
theorem interpolate_eq_interpolateJet (hx : Function.Injective x) (m : Fin n → ℕ) (f : ℝ → ℝ) :
    interpolate x m f = interpolateJet (nodeMultiset x m) (taylorJet f) := by
  classical
  rw [interpolate, ite_eq_left_iff.mpr fun h => absurd hx h]

/-- If the nodes are distinct, the Hermite interpolant has degree less than $\sum_i (m_i + 1)$, the
number of interpolation conditions. -/
theorem degree_interpolate_lt (hx : Function.Injective x) (m : Fin n → ℕ) (f : ℝ → ℝ) :
    (interpolate x m f).degree < ((∑ i, (m i + 1) : ℕ) : WithBot ℕ) := by
  rw [interpolate_eq_interpolateJet hx, ← card_nodeMultiset]
  exact degree_interpolateJet_lt _ _

/-- If the nodes are distinct, the Hermite interpolant $p$ of $f$ satisfies
$p^{(j)}(x_i) = f^{(j)}(x_i)$ for each node $x_i$ and each $j \le m_i$. -/
theorem eval_iterate_derivative_interpolate (hx : Function.Injective x) (i : Fin n) {j : ℕ}
    (hj : j ≤ m i) :
    (Polynomial.derivative^[j] (interpolate x m f)).eval (x i) = iteratedDeriv j f (x i) := by
  rw [interpolate_eq_interpolateJet hx]
  exact isJetInterpolant_taylorJet_iff.mp (isJetInterpolant_interpolateJet _ _) (x i)
    (mem_nodeMultiset.mpr ⟨i, rfl⟩) j (by rw [count_nodeMultiset hx]; omega)

/-- Let the nodes be distinct. If a polynomial $p$ of degree less than $\sum_i (m_i + 1)$ satisfies
$p^{(j)}(x_i) = f^{(j)}(x_i)$ for all $i$ and all $j \le m_i$, then $p$ is the Hermite
interpolant of $f$. -/
theorem eq_interpolate (hx : Function.Injective x) {p : ℝ[X]}
    (hdeg : p.degree < ((∑ i, (m i + 1) : ℕ) : WithBot ℕ))
    (hval : ∀ i, ∀ j ≤ m i,
      (Polynomial.derivative^[j] p).eval (x i) = iteratedDeriv j f (x i)) :
    p = interpolate x m f :=
  (isUnisolvent hx (M := ∑ i, (m i + 1)) rfl fun i j => iteratedDeriv j f (x i)).unique
    ⟨hdeg, hval⟩
    ⟨degree_interpolate_lt hx m f, fun _ _ hj => eval_iterate_derivative_interpolate hx _ hj⟩

/-- **At simple nodes the Hermite interpolant is the Lagrange interpolant.** If the nodes $x_i$ are
distinct and all $m_i = 0$, the Hermite interpolant of $f$ is the Lagrange interpolant of $f$ at
the nodes. -/
theorem interpolate_zero_eq_lagrange (hx : Function.Injective x) (f : ℝ → ℝ) :
    interpolate x (fun _ => 0) f = Lagrange.interpolate Finset.univ x fun i => f (x i) := by
  classical
  refine (eq_interpolate hx ?_ ?_).symm
  · have hdeg : (Lagrange.interpolate Finset.univ x fun i => f (x i)).degree
        < (((Finset.univ : Finset (Fin n)).card : ℕ) : WithBot ℕ) :=
      Lagrange.degree_interpolate_lt (s := (Finset.univ : Finset (Fin n)))
        (r := fun i => f (x i)) hx.injOn
    simpa using hdeg
  · intro i j hj
    have hj0 : j = 0 := Nat.le_zero.mp hj
    subst hj0
    simpa using Lagrange.eval_interpolate_at_node _ hx.injOn (Finset.mem_univ i)

end Interpolate

/-! ### The interpolation error -/

/-- **The Hermite interpolation error formula.** Let $f : \mathbb{R} \to \mathbb{R}$ be of class
$C^{N+1}$. Let $x_1, \dots, x_n$ be distinct points of $[a, b]$ and let
$m_1, \dots, m_n \in \mathbb{N}$ with $\sum_i (m_i + 1) = N + 1$. Let $p$ be the Hermite
interpolant of $f$. Then for every $t \in [a, b]$ there is $\xi \in [a, b]$ with $$f(t) - p(t) =
\frac{f^{(N+1)}(\xi)}{(N + 1)!} \prod_i (t - x_i)^{m_i + 1}.$$ See [han2009theoretical], §3.2.2,
and [kress1998numerical], §8.1.

As in the Lagrange case, the proof subtracts from $f - p$ a multiple of the nodal polynomial,
chosen so that the difference also vanishes at $t$. Its zeros then have multiplicities that sum
to $N + 2$, and `Hermite.exists_iteratedDeriv_eq_zero` applies. The hypothesis is `ContDiff` on
all of $\mathbb{R}$. -/
theorem exists_sub_interpolate_eq {N n : ℕ} {a b : ℝ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ ((N + 1 : ℕ) : WithTop ℕ∞) f) {x : Fin n → ℝ}
    (hx : Function.Injective x) (hxmem : ∀ i, x i ∈ Set.Icc a b) {m : Fin n → ℕ}
    (hsum : ∑ i, (m i + 1) = N + 1) {t : ℝ} (ht : t ∈ Set.Icc a b) :
    ∃ ξ ∈ Set.Icc a b, f t - (interpolate x m f).eval t
      = iteratedDeriv (N + 1) f ξ / (N + 1).factorial * ∏ i, (t - x i) ^ (m i + 1) := by
  classical
  set p : ℝ[X] := interpolate x m f with hp
  by_cases hcase : ∃ i, t = x i
  · -- at a node both sides vanish
    obtain ⟨i, rfl⟩ := hcase
    refine ⟨x i, hxmem i, ?_⟩
    have h0 := eval_iterate_derivative_interpolate (f := f) hx i (Nat.zero_le (m i))
    simp only [Function.iterate_zero, id_eq, iteratedDeriv_zero] at h0
    rw [hp, h0, sub_self,
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [sub_self]; exact zero_pow (by omega)),
      mul_zero]
  · push Not at hcase
    set W : ℝ[X] := nodal x m with hW
    have hWt : W.eval t ≠ 0 := by
      rw [hW, eval_nodal]
      exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (sub_ne_zero.mpr (hcase i))
    set c : ℝ := (f t - p.eval t) / W.eval t with hc
    set Q : ℝ[X] := p + Polynomial.C c * W with hQ
    have hQder : ∀ j : ℕ, Polynomial.derivative^[j] Q
        = Polynomial.derivative^[j] p + Polynomial.C c * Polynomial.derivative^[j] W := fun j => by
      rw [hQ, Polynomial.iterate_derivative_add, Polynomial.iterate_derivative_C_mul]
    -- the auxiliary function and its zeros, counted with multiplicity
    have hQdiff : ContDiff ℝ ((N + 1 : ℕ) : WithTop ℕ∞) fun u => Q.eval u := by
      simpa [Polynomial.coe_aeval_eq_eval] using
        Q.contDiff_aeval (𝕜 := ℝ) ((N + 1 : ℕ) : WithTop ℕ∞)
    have hgdiff : ContDiff ℝ ((N + 1 : ℕ) : WithTop ℕ∞) fun u => f u - Q.eval u := hf.sub hQdiff
    have hgder : ∀ j ≤ N + 1, ∀ u : ℝ, iteratedDeriv j (fun u => f u - Q.eval u) u
        = iteratedDeriv j f u - (Polynomial.derivative^[j] Q).eval u := by
      intro j hj u
      have hjle : ((j : ℕ) : WithTop ℕ∞) ≤ ((N + 1 : ℕ) : WithTop ℕ∞) := by exact_mod_cast hj
      rw [iteratedDeriv_fun_sub (hf.of_le hjle).contDiffAt (hQdiff.of_le hjle).contDiffAt,
        Polynomial.iteratedDeriv_eval]
    have hmle : ∀ i, m i ≤ N := by
      intro i
      have := Finset.single_le_sum (f := fun i => m i + 1) (fun i _ => Nat.zero_le _)
        (Finset.mem_univ i)
      omega
    have hzeronode : ∀ i, ∀ j ≤ m i, iteratedDeriv j (fun u => f u - Q.eval u) (x i) = 0 := by
      intro i j hj
      rw [hgder j (by have := hmle i; omega), hQder, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, eval_iterate_derivative_interpolate hx i hj, hW,
        eval_iterate_derivative_nodal i hj]
      ring
    have hzerot : (fun u => f u - Q.eval u) t = 0 := by
      simp only [hQ, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, hc]
      field_simp
      ring
    -- Rolle with multiplicities on the nodes together with `t`
    have hxc : Function.Injective (Fin.cons t x : Fin (n + 1) → ℝ) :=
      Fin.cons_injective_iff.mpr ⟨by rintro ⟨i, hi⟩; exact hcase i hi.symm, hx⟩
    have hsum' : ∑ i, ((Fin.cons 0 m : Fin (n + 1) → ℕ) i + 1) = N + 2 := by
      have : ∀ i : Fin (n + 1), (Fin.cons 0 m : Fin (n + 1) → ℕ) i + 1
          = (Fin.cons 1 (fun i => m i + 1) : Fin (n + 1) → ℕ) i := by
        refine Fin.cases ?_ ?_ <;> simp
      rw [Finset.sum_congr rfl fun i _ => this i, Fin.sum_cons, hsum]
      omega
    have hmem' : ∀ i : Fin (n + 1), (Fin.cons t x : Fin (n + 1) → ℝ) i ∈ Set.Icc a b := by
      refine Fin.cases ?_ fun i => ?_
      · simpa using ht
      · simpa using hxmem i
    have hzero' : ∀ i : Fin (n + 1), ∀ j ≤ (Fin.cons 0 m : Fin (n + 1) → ℕ) i,
        iteratedDeriv j (fun u => f u - Q.eval u) ((Fin.cons t x : Fin (n + 1) → ℝ) i) = 0 := by
      refine Fin.cases ?_ fun i j hj => ?_
      · intro j hj
        have hj0 : j = 0 := Nat.le_zero.mp (by simpa using hj)
        subst hj0
        simpa using hzerot
      · simpa using hzeronode i j (by simpa using hj)
    obtain ⟨ξ, hξ, hξ0⟩ := exists_iteratedDeriv_eq_zero (N := N) hgdiff hxc hmem' hsum' hzero'
    -- compute the top derivative of the auxiliary function
    refine ⟨ξ, hξ, ?_⟩
    have hpder : Polynomial.derivative^[N + 1] p = 0 :=
      Polynomial.iterate_derivative_eq_zero_of_degree_lt
        (by simpa [hsum] using degree_interpolate_lt hx m f)
    have hWder : Polynomial.derivative^[N + 1] W = Polynomial.C (((N + 1).factorial : ℝ)) :=
      iterate_derivative_nodal x m hsum
    rw [hgder (N + 1) le_rfl, hQder, hpder, hWder] at hξ0
    simp only [Polynomial.eval_mul, Polynomial.eval_C, zero_add] at hξ0
    have hfact : (((N + 1).factorial : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hceq : c = iteratedDeriv (N + 1) f ξ / (N + 1).factorial := by
      field_simp
      linarith [hξ0]
    have hres : f t - p.eval t = c * W.eval t := by
      rw [hc]
      field_simp
    rw [hres, hceq, hW, eval_nodal]

/-! ### Two-point Hermite interpolation -/

/-- **Uniqueness of two-point Hermite interpolation.** Let $s \neq 0$ and let $\pi, \pi'$ be real
polynomials of degree at most $2p + 1$. If $\pi^{(j)}(0) = \pi'^{(j)}(0)$ and
$\pi^{(j)}(s) = \pi'^{(j)}(s)$ for all $j \le p$, then $\pi = \pi'$. -/
theorem eq_of_twoPoint_jets {p : ℕ} {s : ℝ} (hs : s ≠ 0) {π π' : ℝ[X]}
    (hπ : π.natDegree ≤ 2 * p + 1) (hπ' : π'.natDegree ≤ 2 * p + 1)
    (h0 : ∀ j ≤ p, (Polynomial.derivative^[j] π).eval 0 = (Polynomial.derivative^[j] π').eval 0)
    (h1 : ∀ j ≤ p, (Polynomial.derivative^[j] π).eval s = (Polynomial.derivative^[j] π').eval s) :
    π = π' := by
  have hx : Function.Injective (![0, s] : Fin 2 → ℝ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have hM : ∑ i : Fin 2, ((![p, p] : Fin 2 → ℕ) i + 1) = 2 * p + 2 := by
    simp [Fin.sum_univ_two]; ring
  have hdeg : ∀ q : ℝ[X], q.natDegree ≤ 2 * p + 1 → q.degree < ((2 * p + 2 : ℕ) : WithBot ℕ) :=
    fun q hq => (Polynomial.degree_le_of_natDegree_le hq).trans_lt
      (by exact_mod_cast Nat.lt_succ_self _)
  refine (isUnisolvent hx hM (fun i j => (Polynomial.derivative^[j] π').eval (![0, s] i))).unique
    ⟨hdeg π hπ, fun i j hj => ?_⟩ ⟨hdeg π' hπ', fun i j _ => rfl⟩
  fin_cases i
  · exact h0 j hj
  · exact h1 j hj

end Hermite

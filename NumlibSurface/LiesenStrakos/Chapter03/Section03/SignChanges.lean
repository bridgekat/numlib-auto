/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Module
import Numlib.Approximation.Jackson
import NumlibSurface.LiesenStrakos.Chapter03.Section01

/-!
# Sign changes of consecutive Gauss distributions

Moment matching forces the cumulative difference to alternate sign between its successive
nodes. If a sign pattern had fewer changes, its switches would define a polynomial of
too low a degree whose antiderivative gives a contradiction by summation by parts.
-/

open Polynomial

namespace LiesenStrakos.Chapter03

private theorem prod_adjacent_signs (s : ℕ → ℝ) (hs : ∀ i, s i * s i = 1) :
    ∀ a b, a ≤ b → ∏ k ∈ Finset.Ico a b, (s k * s (k + 1)) = s a * s b := by
  intro a b h
  induction b, h using Nat.le_induction with
  | base => simp [hs]
  | succ b hab ih =>
    rw [Finset.prod_Ico_succ_top hab, ih]
    calc (s a * s b) * (s b * s (b + 1)) = s a * (s b * s b) * s (b + 1) := by ring
      _ = _ := by rw [hs, mul_one]

private theorem prod_signs_pos {m : ℕ} (t s : ℕ → ℝ)
    (ht : ∀ i j, i < j → j ≤ m → t i < t j)
    (hs : ∀ i, s i = 1 ∨ s i = -1) {i : ℕ} (hi : i < m) {x : ℝ}
    (hx₀ : t i < x) (hx₁ : x < t (i + 1)) :
    0 < s i * (s (m - 1) * ∏ k ∈ (Finset.range (m - 1)).filter (fun k => s k ≠ s (k + 1)),
      (x - t (k + 1))) := by
  have hsq (j : ℕ) : s j * s j = 1 := by rcases hs j with h | h <;> norm_num [h]
  have hdiff {j : ℕ} (h : s j ≠ s (j + 1)) : s j * s (j + 1) = -1 := by
    rcases hs j with ha | ha <;> rcases hs (j + 1) with hb | hb <;> simp_all
  rw [← mul_assoc, ← prod_adjacent_signs s hsq i (m - 1) (by omega)]
  have heq : Finset.Ico i (m - 1) = (Finset.range (m - 1)).filter (fun k => i ≤ k) := by
    ext k
    simp [and_comm]
  rw [heq, Finset.prod_filter, Finset.prod_filter, ← Finset.prod_mul_distrib]
  apply Finset.prod_pos
  intro k hk
  have hkm : k + 1 ≤ m := by have := Finset.mem_range.1 hk; omega
  split_ifs with hik hne hne
  · rw [hdiff hne]
    have hlt : x < t (k + 1) := hx₁.trans_le (by
      rcases hik.eq_or_lt with he | hlt
      · rw [he]
      · exact (ht _ _ (by omega) hkm).le)
    linarith
  · rw [← not_ne_iff.mp hne, hsq, mul_one]
    norm_num
  · rw [one_mul]
    have hlt : t (k + 1) ≤ t i := by
      have hki : k + 1 ≤ i := by omega
      rcases hki.eq_or_lt with he | hlt
      · rw [he]
      · exact (ht _ _ hlt hi.le).le
    linarith
  · norm_num

private theorem adjacent_sign_ne_of_zero_moments {m : ℕ} (hm : 1 < m) (t d s : ℕ → ℝ)
    (ht : ∀ i j, i < j → j ≤ m → t i < t j)
    (hzero : ∀ p : ℝ[X], p.degree < m →
      ∑ j ∈ Finset.range (m + 1), d j * p.eval (t j) = 0)
    (hfirst : d 0 ≠ 0) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (hcomp : ∀ i < m, 0 ≤ s i * ∑ j ∈ Finset.range (i + 1), d j) :
    ∀ i < m - 1, s i ≠ s (i + 1) := by
  intro i hi hsame
  let changes := (Finset.range (m - 1)).filter (fun k => s k ≠ s (k + 1))
  have hcard : changes.card < m - 1 := by
    rw [← Finset.card_range (m - 1)]
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.filter_subset _ _, fun he => ?_⟩
    have : i ∈ changes := he.symm ▸ Finset.mem_range.2 hi
    exact (Finset.mem_filter.1 this).2 hsame
  let Q : ℝ[X] := C (s (m - 1)) * Lagrange.nodal changes (fun k => t (k + 1))
  have hdegree : Q.degree ≤ ↑(m - 2) := by
    change (C (s (m - 1)) * Lagrange.nodal changes (fun k => t (k + 1))).degree ≤ _
    apply (degree_mul_le_of_le degree_C_le le_rfl).trans
    rw [zero_add, Lagrange.degree_nodal]
    exact_mod_cast (show changes.card ≤ m - 2 by omega)
  obtain ⟨P, hP, hder⟩ := Jackson.exists_derivative_eq hdegree
  have hP' : P.degree < m := hP.trans_lt (by exact_mod_cast (by omega : m - 2 + 1 < m))
  have hsign (k : ℕ) (hk : k < m) :
      0 < s k * (P.eval (t (k + 1)) - P.eval (t k)) := by
    have ht' : t k < t (k + 1) := ht _ _ (by omega) (by omega)
    let f : ℝ → ℝ := fun x => (C (s k) * P).eval x
    have hcont : ContinuousOn f (Set.Icc (t k) (t (k + 1))) :=
      (C (s k) * P).continuous.continuousOn
    have hmon := strictMonoOn_of_deriv_pos (convex_Icc (t k) (t (k + 1))) hcont
      (fun x hx => by
        rw [interior_Icc] at hx
        have h := (C (s k) * P).hasDerivAt x
        rw [h.deriv, derivative_C_mul, hder, eval_mul, eval_C]
        change 0 < s k * (C (s (m - 1)) * Lagrange.nodal changes (fun j => t (j + 1))).eval x
        rw [eval_mul, eval_C, Lagrange.eval_nodal]
        exact prod_signs_pos t s ht hs hk hx.1 hx.2)
    have hlt := hmon ⟨le_rfl, ht'.le⟩ ⟨ht'.le, le_rfl⟩ ht'
    change (C (s k) * P).eval (t k) < (C (s k) * P).eval (t (k + 1)) at hlt
    rw [eval_mul, eval_C, eval_mul, eval_C] at hlt
    rwa [mul_sub, sub_pos]
  have hmass : ∑ j ∈ Finset.range (m + 1), d j = 0 := by
    simpa using hzero 1 (by rw [degree_one]; exact_mod_cast (by omega : 0 < m))
  have hdtotal := hzero P hP'
  rw [show (∑ j ∈ Finset.range (m + 1), d j * P.eval (t j)) =
      ∑ j ∈ Finset.range (m + 1), d j • P.eval (t j) by rfl,
    Finset.sum_range_by_parts', hmass, zero_smul, zero_sub, neg_eq_zero,
    Nat.add_sub_cancel] at hdtotal
  let cum (k : ℕ) := ∑ j ∈ Finset.range (k + 1), d j
  have hfactor (k : ℕ) :
      cum k * (P.eval (t (k + 1)) - P.eval (t k)) =
      (s k * cum k) * (s k * (P.eval (t (k + 1)) - P.eval (t k))) := by
    rcases hs k with h | h <;> rw [h] <;> ring
  have hpos : 0 < ∑ k ∈ Finset.range m, cum k * (P.eval (t (k + 1)) - P.eval (t k)) := by
    apply Finset.sum_pos'
    · intro k hk
      rw [hfactor]
      exact mul_nonneg (hcomp k (Finset.mem_range.1 hk)) (hsign k (Finset.mem_range.1 hk)).le
    · refine ⟨0, Finset.mem_range.2 (by omega), ?_⟩
      rw [hfactor]
      have hmass₀ : s 0 * cum 0 ≠ 0 := by
        have hs₀ : s 0 ≠ 0 := by rcases hs 0 with hh | hh <;> norm_num [hh]
        simpa [cum, hfirst] using mul_ne_zero hs₀ hfirst
      exact mul_pos (lt_of_le_of_ne (hcomp 0 (by omega)) hmass₀.symm) (hsign 0 (by omega))
  exact hpos.ne' hdtotal


private theorem cumulative_mul_lt_zero_of_zero_moments {m : ℕ} (hm : 1 < m) (t d : ℕ → ℝ)
    (ht : ∀ i j, i < j → j ≤ m → t i < t j)
    (hzero : ∀ p : ℝ[X], p.degree < m →
      ∑ j ∈ Finset.range (m + 1), d j * p.eval (t j) = 0)
    (hfirst : d 0 ≠ 0) :
    ∀ i < m - 1, (∑ j ∈ Finset.range (i + 1), d j) *
      (∑ j ∈ Finset.range (i + 2), d j) < 0 := by
  let c (i : ℕ) := ∑ j ∈ Finset.range (i + 1), d j
  let s (i : ℕ) := if 0 ≤ c i then (1 : ℝ) else -1
  let q (i : ℕ) := if 0 < c i then (1 : ℝ) else -1
  have hs (i : ℕ) : s i = 1 ∨ s i = -1 := by
    dsimp only [s]
    split <;> simp
  have hq (i : ℕ) : q i = 1 ∨ q i = -1 := by
    dsimp only [q]
    split <;> simp
  have hs' (i : ℕ) : 0 ≤ s i * c i := by
    dsimp [s]
    split <;> simp_all
    all_goals linarith
  have hq' (i : ℕ) : 0 ≤ q i * c i := by
    dsimp [q]
    split <;> simp_all
    all_goals linarith
  have hsne := adjacent_sign_ne_of_zero_moments hm t d s ht hzero hfirst hs (fun i _ => hs' i)
  have hqne := adjacent_sign_ne_of_zero_moments hm t d q ht hzero hfirst hq (fun i _ => hq' i)
  have heq (i : ℕ) (hi : i < m) : s i = q i := by
    induction i with
    | zero =>
      have hc : c 0 ≠ 0 := by simpa [c] using hfirst
      simp only [s, q, le_iff_lt_or_eq, hc.symm, or_false]
    | succ i ih =>
      have hi' : i < m - 1 := by omega
      have hsame := ih (by omega)
      have hsai := hsne i hi'
      have hqai := hqne i hi'
      rw [← hsame] at hqai
      rcases hs i with hh | hh <;> rcases hs (i + 1) with hh₁ | hh₁ <;>
        rcases hq (i + 1) with hh₂ | hh₂ <;> simp_all
  have hnz (i : ℕ) (hi : i < m) : c i ≠ 0 := by
    intro h
    have hsame := heq i hi
    norm_num [s, q, h] at hsame
  intro i hi
  change c i * c (i + 1) < 0
  have hsign := hsne i hi
  rcases lt_or_gt_of_ne (hnz i (by omega)) with ha | ha <;>
    rcases lt_or_gt_of_ne (hnz (i + 1) (by omega)) with hb | hb
  · simp [s, ha.not_ge, hb.not_ge] at hsign
  · exact mul_neg_of_neg_of_pos ha hb
  · exact mul_neg_of_pos_of_neg ha hb
  · simp [s, ha.le, hb.le] at hsign

/-- **Theorem 3.3.4** of [liesen2013krylov]. For consecutive positive Gauss rules with disjoint
nodes, their cumulative distribution difference changes sign at each of the $2n-1$ interior
boundaries between its $2n$ bounded gaps. The CDF value at the left endpoint of a gap is its
constant value there. The cumulative difference is zero at the last node. -/
theorem theorem_3_3_4 {μ : MeasureTheory.Measure ℝ} {n : ℕ} (hn : 0 < n)
    {x w : Fin n → ℝ} {y v : Fin (n + 1) → ℝ}
    (hx : Function.Injective x) (hy : Function.Injective y) (hxy : ∀ i j, x i ≠ y j)
    (hw : ∀ i, 0 < w i) (hv : ∀ j, 0 < v j)
    (hex : Quadrature.IsExactOnMeasure μ w x (2 * n - 1))
    (hey : Quadrature.IsExactOnMeasure μ v y (2 * n - 1)) :
    let Δ (t : ℝ) := atomicDistribution y v t - atomicDistribution x w t
    ∃ t : Fin (2 * n + 1) → ℝ, StrictMono t ∧ Set.range t = Set.range x ∪ Set.range y ∧
      Δ (t (Fin.last (2 * n))) = 0 ∧
      ∀ i (hi : i < 2 * n - 1),
        Δ (t ⟨i, by omega⟩) * Δ (t ⟨i + 1, by omega⟩) < 0 := by
  classical
  let m := 2 * n
  let nodes : Fin n ⊕ Fin (n + 1) → ℝ := Sum.elim x y
  let masses : Fin n ⊕ Fin (n + 1) → ℝ := Sum.elim (fun i => -w i) v
  let s := Finset.univ.image nodes
  have hnodes : Function.Injective nodes := by
    intro a b h
    rcases a with a | a <;> rcases b with b | b
    · exact congrArg Sum.inl (hx h)
    · exact False.elim (hxy a b h)
    · exact False.elim (hxy b a h.symm)
    · exact congrArg Sum.inr (hy h)
  have hcard : s.card = m + 1 := by
    rw [Finset.card_image_of_injective _ hnodes, Finset.card_univ, Fintype.card_sum]
    simp only [Fintype.card_fin, m]
    omega
  let t := s.orderEmbOfFin hcard
  have htrange : Set.range t = Set.range nodes := by
    rw [Finset.range_orderEmbOfFin, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hlift (j : Fin (m + 1)) : ∃ a, nodes a = t j := by
    have hm : t j ∈ Set.range nodes := htrange ▸ Set.mem_range_self j
    exact hm
  choose a ha using hlift
  have haInj : Function.Injective a := fun i j hij =>
    t.injective (by rw [← ha, ← ha, hij])
  have haSurj : Function.Surjective a := by
    intro i
    have hm : nodes i ∈ Set.range t := htrange.symm ▸ Set.mem_range_self i
    obtain ⟨j, hj⟩ := hm
    exact ⟨j, hnodes ((ha j).trans hj)⟩
  let e := Equiv.ofBijective a ⟨haInj, haSurj⟩
  let T (i : ℕ) : ℝ := if hi : i < m + 1 then t ⟨i, hi⟩ else 0
  let d (i : ℕ) : ℝ := if hi : i < m + 1 then masses (e ⟨i, hi⟩) else 0
  have hT (i : ℕ) (hi : i < m + 1) : T i = t ⟨i, hi⟩ := dite_eq_left hi
  have hd (i : ℕ) (hi : i < m + 1) : d i = masses (e ⟨i, hi⟩) := dite_eq_left hi
  have hTmono (i j : ℕ) (hij : i < j) (hj : j ≤ m) : T i < T j := by
    rw [hT _ (by omega), hT _ (by omega)]
    exact t.strictMono hij
  have hfirst : d 0 ≠ 0 := by
    rw [hd _ (by omega)]
    cases he : e ⟨0, by omega⟩ with
    | inl i => exact neg_ne_zero.2 (hw i).ne'
    | inr j => exact (hv j).ne'
  have hzero (p : ℝ[X]) (hp : p.degree < m) :
      ∑ j ∈ Finset.range (m + 1), d j * p.eval (T j) = 0 := by
    have hpd : p.degree ≤ ↑(2 * n - 1) := by
      rw [show m = 2 * n - 1 + 1 by dsimp [m]; omega] at hp
      rcases eq_or_ne p 0 with rfl | hp0
      · simp
      rw [degree_eq_natDegree hp0] at hp ⊢
      exact_mod_cast (Nat.lt_succ_iff.1 (by exact_mod_cast hp))
    have hs := Fintype.sum_equiv e (fun j => masses (e j) * p.eval (t j))
      (fun a => masses a * p.eval (nodes a)) (fun j => by rw [show nodes (e j) = t j from ha j])
    rw [← Fin.sum_univ_eq_sum_range (fun j => d j * p.eval (T j))]
    simp only [hd _ (Fin.isLt _), hT _ (Fin.isLt _)]
    rw [hs, Fintype.sum_sum_type]
    simp only [masses, nodes, Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib,
      hex p hpd, hey p hpd, neg_add_cancel]
  let Δ (z : ℝ) := atomicDistribution y v z - atomicDistribution x w z
  have hval (z : ℝ) : Δ z =
      ∑ j : Fin (m + 1), if t j ≤ z then masses (e j) else 0 := by
    have hs := Fintype.sum_equiv e (fun j => if t j ≤ z then masses (e j) else 0)
      (fun a => if nodes a ≤ z then masses a else 0) (fun j => by
        rw [show nodes (e j) = t j from ha j])
    rw [hs, Fintype.sum_sum_type]
    have hxsum : ∑ i, (if x i ≤ z then -w i else 0) =
        -(∑ i, if x i ≤ z then w i else 0) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      split <;> simp_all
    change (∑ j, if y j ≤ z then v j else 0) - (∑ i, if x i ≤ z then w i else 0) =
      (∑ i, if x i ≤ z then -w i else 0) + ∑ j, if y j ≤ z then v j else 0
    rw [hxsum]
    ring
  have hcum {i : ℕ} (hi : i ≤ m) :
      Δ (T i) = ∑ j ∈ Finset.range (i + 1), d j := by
    rw [hval, ← Finset.sum_filter]
    have hle (j : Fin (m + 1)) : t j ≤ T i ↔ (j : ℕ) ≤ i := by
      rw [hT _ (by omega)]
      exact t.le_iff_le
    simp only [hle]
    rw [Finset.sum_filter]
    have heq : (∑ j : Fin (m + 1), if (j : ℕ) ≤ i then masses (e j) else 0) =
        ∑ j ∈ Finset.range (m + 1), if j ≤ i then d j else 0 := by
      rw [← Fin.sum_univ_eq_sum_range (fun j => if j ≤ i then d j else 0)]
      simp only [hd _ (Fin.isLt _)]
    rw [heq, ← Finset.sum_filter]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hterminal : ∑ j ∈ Finset.range (m + 1), d j = 0 := by
    simpa using hzero 1 (by rw [degree_one]; exact_mod_cast (by dsimp [m]; omega : 0 < m))
  refine ⟨t, t.strictMono, htrange.trans ?_, ?_, ?_⟩
  · ext z
    constructor
    · rintro ⟨a, rfl⟩
      cases a with
      | inl i => exact Or.inl (Set.mem_range_self i)
      | inr j => exact Or.inr (Set.mem_range_self j)
    · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
      · exact ⟨Sum.inl i, rfl⟩
      · exact ⟨Sum.inr j, rfl⟩
  · change Δ (t ⟨m, by omega⟩) = 0
    rw [← hT m (by omega), hcum le_rfl, hterminal]
  · intro i hi
    change Δ (t ⟨i, _⟩) * Δ (t ⟨i + 1, _⟩) < 0
    rw [← hT i (by omega), ← hT (i + 1) (by omega), hcum (by omega), hcum (by omega)]
    exact cumulative_mul_lt_zero_of_zero_moments (by dsimp [m]; omega) T d hTmono hzero hfirst i hi
end LiesenStrakos.Chapter03

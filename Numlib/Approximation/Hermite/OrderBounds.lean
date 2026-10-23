import Numlib.Approximation.Hermite.Global

/-!
# Separate bounds for derivative orders of global Hermite interpolants

Bounds on positive-order derivatives are independent of absolute function values.
The gluing interface permits a distinct bound for every derivative order, so a
large value range does not inflate the derivative estimates.
-/

open Polynomial Set
namespace Hermite

/-- A finite polynomial chain with a separate bound for every derivative order. -/
structure OrderBoundedChain (p n : ℕ) (x : ℕ → ℝ) (jets : ℕ → ℕ → ℝ)
    (Q : ℕ → ℝ[X]) (L : NNReal) (B : ℕ → ℝ) : Prop where
  increasing : ∀ i j, i < j → j ≤ n → x i < x j
  left_jet : ∀ k < n, ∀ j ≤ p, iteratedDeriv j (fun t => (Q k).eval t) 0 = jets k j
  right_jet : ∀ k < n, ∀ j ≤ p,
    iteratedDeriv j (fun t => (Q k).eval t) (x (k + 1) - x k) = jets (k + 1) j
  lipschitz : ∀ k < n, LipschitzOnWith L (iteratedDeriv p (fun t => (Q k).eval t))
    (Icc 0 (x (k + 1) - x k))
  bound : ∀ k < n, ∀ j ≤ p, ∀ t ∈ Icc 0 (x (k + 1) - x k),
    |iteratedDeriv j (fun z => (Q k).eval z) t| ≤ B j

/-- Starting from a matching seed, glue every interval in a finite chain. The result
retains the prescribed jets, the prefix bounds, and the terminal Taylor tail. -/
theorem OrderBoundedChain.exists_prefix {p n : ℕ} {x : ℕ → ℝ} {jets : ℕ → ℕ → ℝ}
    {Q : ℕ → ℝ[X]} {L : NNReal} {B : ℕ → ℝ}
    (h : OrderBoundedChain p n x jets Q L B) (seed : ℝ → ℝ)
    (hseed : ContDiff ℝ p seed) (hLseed : LipschitzWith L (iteratedDeriv p seed))
    (hseedj : ∀ j ≤ p, iteratedDeriv j seed (x 0) = jets 0 j)
    (hseedb : ∀ j ≤ p, ∀ t ≤ x 0, |iteratedDeriv j seed t| ≤ B j)
    (hseedt : ∀ j ≤ p, ∀ t, x 0 ≤ t → iteratedDeriv j seed t =
      iteratedDeriv j (taylorTail p (jets 0) (x 0)) t) :
    ∃ f : ℝ → ℝ, ContDiff ℝ p f ∧ LipschitzWith L (iteratedDeriv p f) ∧
      (∀ k ≤ n, ∀ j ≤ p, iteratedDeriv j f (x k) = jets k j) ∧
      (∀ j ≤ p, ∀ t ≤ x n, |iteratedDeriv j f t| ≤ B j) ∧
      (∀ j ≤ p, ∀ t, x n ≤ t → iteratedDeriv j f t =
        iteratedDeriv j (taylorTail p (jets n) (x n)) t) := by
  induction n with
  | zero =>
    refine ⟨seed, hseed, hLseed, ?_, hseedb, hseedt⟩
    intro k hk j hj
    have hk0 : k = 0 := by omega
    subst k
    exact hseedj j hj
  | succ n ih =>
    have hsmall : OrderBoundedChain p n x jets Q L B := {
      increasing := fun i j hij hj => h.increasing i j hij (by omega)
      left_jet := fun k hk => h.left_jet k (by omega)
      right_jet := fun k hk => h.right_jet k (by omega)
      lipschitz := fun k hk => h.lipschitz k (by omega)
      bound := fun k hk => h.bound k (by omega) }
    obtain ⟨f,hf,hLf,hfj,hfb,_hft⟩ := ih hsmall
    have hab : x n < x (n + 1) := h.increasing n (n + 1) (by omega) le_rfl
    have hmatch : ∀ j ≤ p, iteratedDeriv j f (x n) =
        iteratedDeriv j (fun t => (Q n).eval t) 0 := by
      intro j hj
      exact (hfj n le_rfl j hj).trans (h.left_jet n (by omega) j hj).symm
    refine ⟨extendRight p f (Q n) (x n) (x (n + 1)),
      extendRight_contDiff hf hab.le hmatch,
      extendRight_lipschitz_top hf hab.le hmatch hLf (h.lipschitz n (by omega)), ?_, ?_, ?_⟩
    · intro k hk j hj
      by_cases hkn : k ≤ n
      · have hx : x k ≤ x n := by
          rcases lt_or_eq_of_le hkn with hlt | rfl
          · exact (h.increasing k n hlt (by omega)).le
          · exact le_rfl
        rw [extendRight_left hf hab.le hmatch hj hx]
        exact hfj k hkn j hj
      · have heq : k = n + 1 := by omega
        subst k
        rw [extendRight_interval hf hab.le hmatch hj ⟨hab.le,le_rfl⟩]
        exact h.right_jet n (by omega) j hj
    · intro j hj t ht
      by_cases hta : t ≤ x n
      · rw [extendRight_left hf hab.le hmatch hj hta]
        exact hfb j hj t hta
      · rw [extendRight_interval hf hab.le hmatch hj ⟨(lt_of_not_ge hta).le,ht⟩]
        exact h.bound n (by omega) j hj (t - x n)
          ⟨sub_nonneg.mpr (lt_of_not_ge hta).le, sub_le_sub_right ht (x n)⟩
    · intro j hj t ht
      rw [extendRight_tail hf hab hmatch hj ht,
        taylorTail_congr (h.right_jet n (by omega)) (x (n + 1))]

/-- Uniform bounds on a prefix and an appended interval give a bound on the enlarged prefix. -/
theorem extendRight_orderBounds {p : ℕ} {f : ℝ → ℝ} {Q : ℝ[X]} {a b : ℝ}
    (hf : ContDiff ℝ p f) (hab : a ≤ b)
    (hjet : ∀ j ≤ p, iteratedDeriv j f a = iteratedDeriv j (fun t => Q.eval t) 0)
    {B : ℕ → ℝ} (hfB : ∀ j ≤ p, ∀ t ≤ a, |iteratedDeriv j f t| ≤ B j)
    (hQB : ∀ j ≤ p, ∀ t ∈ Icc 0 (b - a), |iteratedDeriv j (fun z => Q.eval z) t| ≤ B j) :
    ∀ j ≤ p, ∀ t ≤ b, |iteratedDeriv j (extendRight p f Q a b) t| ≤ B j := by
  intro j hj t ht
  by_cases hta : t ≤ a
  · rw [extendRight_left hf hab hjet hj hta]
    exact hfB j hj t hta
  · rw [extendRight_interval hf hab hjet hj ⟨(lt_of_not_ge hta).le,ht⟩]
    exact hQB j hj (t-a) ⟨sub_nonneg.mpr (lt_of_not_ge hta).le, sub_le_sub_right ht a⟩

/-- Two exterior polynomial transitions with flat outer jets turn a finite chain
into a globally bounded `C^p` interpolant with the same highest derivative Lipschitz constant. -/
theorem OrderBoundedChain.exists_global {p n : ℕ} {x : ℕ → ℝ}
    {jets : ℕ → ℕ → ℝ} {Q : ℕ → ℝ[X]} {L : NNReal} {B : ℕ → ℝ} {W : ℝ}
    (hB : ∀ j ≤ p, 0 ≤ B j) (hW : 0 < W) (h : OrderBoundedChain p n x jets Q L B)
    (P R : ℝ[X])
    (hP0 : ∀ j ≤ p, iteratedDeriv j (fun t => P.eval t) 0 =
      if j = 0 then jets 0 0 else 0)
    (hP1 : ∀ j ≤ p, iteratedDeriv j (fun t => P.eval t) W = jets 0 j)
    (hR0 : ∀ j ≤ p, iteratedDeriv j (fun t => R.eval t) 0 = jets n j)
    (hR1 : ∀ j ≤ p, iteratedDeriv j (fun t => R.eval t) W =
      if j = 0 then jets n 0 else 0)
    (hPL : LipschitzOnWith L (iteratedDeriv p (fun t => P.eval t)) (Icc 0 W))
    (hRL : LipschitzOnWith L (iteratedDeriv p (fun t => R.eval t)) (Icc 0 W))
    (hPB : ∀ j ≤ p, ∀ t ∈ Icc 0 W, |iteratedDeriv j (fun z => P.eval z) t| ≤ B j)
    (hRB : ∀ j ≤ p, ∀ t ∈ Icc 0 W, |iteratedDeriv j (fun z => R.eval z) t| ≤ B j) :
    ∃ f : ℝ → ℝ, ContDiff ℝ p f ∧ LipschitzWith L (iteratedDeriv p f) ∧
      (∀ k ≤ n, ∀ j ≤ p, iteratedDeriv j f (x k) = jets k j) ∧
      (∀ j ≤ p, ∀ t, |iteratedDeriv j f t| ≤ B j) := by
  let seed := extendRight p (fun _ => jets 0 0) P (x 0-W) (x 0)
  have ha : x 0-W < x 0 := by linarith
  have hm : ∀ j ≤ p, iteratedDeriv j (fun _ : ℝ => jets 0 0) (x 0-W) =
      iteratedDeriv j (fun t => P.eval t) 0 := by
    intro j hj
    simpa only [iteratedDeriv_const] using (hP0 j hj).symm
  have hs : ContDiff ℝ p seed := extendRight_contDiff contDiff_const ha.le hm
  have hsL : LipschitzWith L (iteratedDeriv p seed) := by
    apply extendRight_lipschitz_top contDiff_const ha.le hm
    · apply lipschitzWith_iff_norm_sub_le.mpr
      intro u v
      simp only [iteratedDeriv_const, sub_self, norm_zero]
      positivity
    · simpa only [sub_sub_cancel] using hPL
  have hsj : ∀ j ≤ p, iteratedDeriv j seed (x 0) = jets 0 j := by
    intro j hj
    rw [extendRight_interval contDiff_const ha.le hm hj ⟨ha.le,le_rfl⟩]
    simpa only [sub_sub_cancel] using hP1 j hj
  have hsb : ∀ j ≤ p, ∀ t ≤ x 0, |iteratedDeriv j seed t| ≤ B j := by
    apply extendRight_orderBounds contDiff_const ha.le hm
    · intro j hj t _ht
      by_cases hj0 : j = 0
      · subst j
        have hh := hPB 0 (by omega) 0 ⟨by simp,hW.le⟩
        simpa only [iteratedDeriv_zero, hP0 0 (by omega), ite_true] using hh
      · simpa only [iteratedDeriv_const, ite_eq_right hj0, abs_zero] using hB j hj
    · simpa only [sub_sub_cancel] using hPB
  have hst : ∀ j ≤ p, ∀ t, x 0 ≤ t → iteratedDeriv j seed t =
      iteratedDeriv j (taylorTail p (jets 0) (x 0)) t := by
    intro j hj t ht
    rw [extendRight_tail contDiff_const ha hm hj ht]
    have hh : ∀ i ≤ p, iteratedDeriv i (fun z => P.eval z) (x 0-(x 0-W)) = jets 0 i := by
      simpa only [sub_sub_cancel] using hP1
    rw [taylorTail_congr hh]
  obtain ⟨f,hf,hLf,hfj,hfb,_hft⟩ := h.exists_prefix seed hs hsL hsj hsb hst
  have hb : x n < x n+W := by linarith
  have hmatch : ∀ j ≤ p, iteratedDeriv j f (x n) = iteratedDeriv j (fun t => R.eval t) 0 := by
    intro j hj
    exact (hfj n le_rfl j hj).trans (hR0 j hj).symm
  refine ⟨extendRight p f R (x n) (x n+W), extendRight_contDiff hf hb.le hmatch,
    extendRight_lipschitz_top hf hb.le hmatch hLf (by simpa using hRL), ?_, ?_⟩
  · intro k hk j hj
    have hx : x k ≤ x n := by
      rcases lt_or_eq_of_le hk with hkn | rfl
      · exact (h.increasing k n hkn le_rfl).le
      · exact le_rfl
    rw [extendRight_left hf hb.le hmatch hj hx]
    exact hfj k hk j hj
  · intro j hj t
    by_cases ht : t ≤ x n+W
    · apply extendRight_orderBounds hf hb.le hmatch hfb (by simpa using hRB) j hj t ht
    · rw [extendRight_tail hf hb hmatch hj (lt_of_not_ge ht).le]
      have hflat : ∀ i, 1 ≤ i → i ≤ p →
          iteratedDeriv i (fun z => R.eval z) (x n+W-x n) = 0 := by
        intro i hi hip
        simpa only [add_sub_cancel_left, ite_eq_right (by omega : i ≠ 0)] using hR1 i hip
      rw [taylorTail_of_flat hflat]
      by_cases hj0 : j = 0
      · subst j
        have hh := hRB 0 (by omega) W ⟨hW.le,le_rfl⟩
        simpa only [iteratedDeriv_zero, add_sub_cancel_left] using hh
      · simpa only [iteratedDeriv_const, ite_eq_right hj0, abs_zero] using hB j hj

/-- Add a constant only to the value entry of a derivative jet. -/
def shiftJet (c : ℝ) (a : ℕ → ℝ) (j : ℕ) : ℝ := a j + if j = 0 then c else 0

/-- Initial Taylor interpolation commutes with adding a constant. -/
theorem initialPolynomial_shiftJet (p : ℕ) (a : ℕ → ℝ) (c : ℝ) :
    initialPolynomial p (shiftJet c a) = initialPolynomial p a + C c := by
  have hh : (fun j => shiftJet c a j / (j.factorial : ℝ)) =
      (fun j => a j / (j.factorial : ℝ)) +
      (fun j => flatJet c j / (j.factorial : ℝ)) := by
    funext j
    simp only [shiftJet, flatJet, Pi.add_apply, add_div]
  unfold initialPolynomial
  rw [hh, jetPoly_add]
  change initialPolynomial p a + initialPolynomial p (flatJet c) = _
  rw [initialPolynomial_flatJet]
  rfl

/-- Adding a constant changes only the zeroth polynomial derivative. -/
theorem iterate_derivative_add_const (Q : ℝ[X]) (c : ℝ) (j : ℕ) :
    derivative^[j] (Q + C c) = derivative^[j] Q + if j = 0 then C c else 0 := by
  have hh : derivative^[j] (Q+C c) = derivative^[j] Q + derivative^[j] (C c) := by
    simp_rw [← Module.End.pow_apply, map_add]
  rw [hh]
  by_cases hj : j = 0
  · subst j; simp
  · rw [iterate_derivative_C (by omega), ite_eq_right hj]

/-- Two-endpoint interpolation commutes with adding a common constant to both values. -/
theorem endpointPolynomial_shiftJet {p : ℕ} {s : ℝ} (hs : s ≠ 0)
    (a b : ℕ → ℝ) (c : ℝ) :
    endpointPolynomial p s (shiftJet c a) (shiftJet c b) = endpointPolynomial p s a b+C c := by
  symm
  apply endpointPolynomial_eq_of_jets hs
  · have hn : (endpointPolynomial p s a b+C c).natDegree ≤ 2*p+1 :=
      (natDegree_add_le _ _).trans (max_le (endpointPolynomial_natDegree_le p s a b)
        (by simp))
    exact (natDegree_le_iff_degree_le.mp hn).trans_lt
      (by exact_mod_cast (show 2*p+1<2*p+2 by omega))
  · intro j hj
    rw [iterate_derivative_add_const]
    simp only [eval_add, endpointPolynomial_zero hs a b hj, shiftJet]
    split_ifs <;> simp
  · intro j hj
    rw [iterate_derivative_add_const]
    simp only [eval_add, endpointPolynomial_right hs a b hj, shiftJet]
    split_ifs <;> simp

/-- The full derivative jet of a shifted interpolant changes only at order zero. -/
theorem iteratedDeriv_endpointPolynomial_shiftJet {p : ℕ} {s : ℝ} (hs : s ≠ 0)
    (a b : ℕ → ℝ) (c : ℝ) (j : ℕ) (t : ℝ) :
    iteratedDeriv j (endpointPolynomial p s (shiftJet c a) (shiftJet c b)).eval t =
      iteratedDeriv j (endpointPolynomial p s a b).eval t + if j = 0 then c else 0 := by
  simp only [Polynomial.iteratedDeriv_eval]
  rw [endpointPolynomial_shiftJet hs, iterate_derivative_add_const]
  simp only [eval_add]
  split_ifs <;> simp

/-- Endpoint derivative bounds measured relative to the initial value are independent
of the magnitude of that value. All positive-order bounds are absolute. -/
theorem endpointPolynomial_uniform_centered_bounds (p : ℕ) (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ L > 0, ∃ B > 0, ∀ s : ℝ, 0 < s → s ≤ κ → ∀ a b : ℕ → ℝ,
      (∀ j, 1 ≤ j → j ≤ p → |a j| ≤ κ) →
      (∀ j ≤ p, |b j-(derivative^[j] (initialPolynomial p a)).eval s| ≤
        κ*s^(p-j+1)) →
      (∀ u ∈ Icc 0 s, ∀ v ∈ Icc 0 s,
        |iteratedDeriv p (endpointPolynomial p s a b).eval u -
          iteratedDeriv p (endpointPolynomial p s a b).eval v| ≤ L*|u-v|) ∧
      ∀ j ≤ p, ∀ t ∈ Icc 0 s,
        |iteratedDeriv j (endpointPolynomial p s a b).eval t -
          (if j=0 then a 0 else 0)| ≤ B := by
  obtain ⟨L,hL,B,hB,H⟩ := endpointPolynomial_uniform_bounds p κ hκ
  refine ⟨L,hL,B,hB,?_⟩
  intro s hs hsκ a b ha hres
  refine ⟨(H s hs a b hres).1,?_⟩
  have hnorm : ∀ j ≤ p, |shiftJet (-a 0) (a) j| ≤ κ := by
    intro j hj
    by_cases hj0 : j=0
    · subst j
      simpa only [shiftJet, ite_true, add_neg_cancel, abs_zero] using hκ
    · simpa only [shiftJet, ite_eq_right hj0, add_zero] using ha j (by omega) hj
  have hr : ∀ j ≤ p,
      |shiftJet (-a 0) b j -
        (derivative^[j] (initialPolynomial p (shiftJet (-a 0) a))).eval s| ≤
      κ*s^(p-j+1) := by
    intro j hj
    have he : shiftJet (-a 0) b j -
        (derivative^[j] (initialPolynomial p (shiftJet (-a 0) a))).eval s =
        b j-(derivative^[j] (initialPolynomial p a)).eval s := by
      rw [initialPolynomial_shiftJet, iterate_derivative_add_const, eval_add]
      unfold shiftJet
      by_cases hj0 : j=0 <;> simp [hj0]
    rw [he]
    exact hres j hj
  have hb := (H s hs (shiftJet (-a 0) a) (shiftJet (-a 0) b) hr).2 hnorm hsκ
  intro j hj t ht
  have hh := hb j hj t ht
  rw [iteratedDeriv_endpointPolynomial_shiftJet hs.ne'] at hh
  by_cases hj0 : j=0
  · simpa only [hj0, ite_true, sub_eq_add_neg] using hh
  · simpa only [ite_eq_right hj0, add_zero, sub_zero] using hh

/-- Only positive-order endpoint entries are needed for a flat-to-jet residual bound. -/
theorem flatJet_residual_positive {p : ℕ} {a : ℕ → ℝ} {κ : ℝ} (hκ : 0 ≤ κ)
    (ha : ∀ j, 1 ≤ j → j ≤ p → |a j| ≤ κ) :
    ∀ j ≤ p, |a j-(derivative^[j] (initialPolynomial p (flatJet (a 0)))).eval 1| ≤
      κ*(1:ℝ)^(p-j+1) := by
  intro j hj
  rw [initialPolynomial_flatJet]
  by_cases hj0 : j=0
  · subst j
    simpa only [Function.iterate_zero, id_eq, eval_C, sub_self, abs_zero, one_pow,
      mul_one] using hκ
  · rw [iterate_derivative_C (by omega), eval_zero, sub_zero]
    simpa only [one_pow, mul_one] using ha j (by omega) hj

/-- A centered derivative bound and a bound on the initial value give separate
zeroth- and positive-order estimates. -/
theorem abs_le_orderBound {Q : ℝ[X]} {p : ℕ} {S : Set ℝ} {c M B : ℝ}
    (hc : |c| ≤ M)
    (hQ : ∀ j ≤ p, ∀ t ∈ S,
      |iteratedDeriv j Q.eval t-(if j=0 then c else 0)| ≤ B) :
    ∀ j ≤ p, ∀ t ∈ S,
      |iteratedDeriv j Q.eval t| ≤ if j = 0 then M + B else B := by
  intro j hj t ht
  have hh := hQ j hj t ht
  by_cases hj0 : j=0
  · subst j
    simp only [ite_true] at hh ⊢
    have htri : |iteratedDeriv 0 Q.eval t| ≤ |iteratedDeriv 0 Q.eval t-c|+|c| := by
      simpa only [sub_add_cancel] using abs_add_le (iteratedDeriv 0 Q.eval t-c) c
    linarith
  · simpa only [ite_eq_right hj0, sub_zero] using hh

/-- Globally bounded positive derivatives can be interpolated independently of
absolute function values. The value bound is additive in the given value range. -/
theorem exists_uniform_interpolant_positive (p : ℕ) (κ : ℝ) (hκ : 1 ≤ κ) :
    ∃ (L : ℝ) (hL : 0 < L), ∃ B > 0, ∀ n : ℕ,
      ∀ x : ℕ → ℝ, ∀ a : ℕ → ℕ → ℝ,
      (∀ i j, i < j → j ≤ n → x i < x j) →
      (∀ k ≤ n, ∀ j, 1 ≤ j → j ≤ p → |a k j| ≤ κ) →
      (∀ k < n, x (k+1)-x k ≤ κ) →
      (∀ k < n, ∀ j ≤ p,
        |a (k+1) j-(derivative^[j] (initialPolynomial p (a k))).eval (x (k+1)-x k)| ≤
          κ*(x (k+1)-x k)^(p-j+1)) →
      ∀ M : ℝ, 0 ≤ M → (∀ k ≤ n, |a k 0| ≤ M) →
      ∃ f : ℝ → ℝ, ContDiff ℝ p f ∧ LipschitzWith ⟨L,hL.le⟩ (iteratedDeriv p f) ∧
        (∀ k ≤ n, ∀ j ≤ p, iteratedDeriv j f (x k) = a k j) ∧
        (∀ t, |f t| ≤ M+B) ∧
        ∀ j, 1 ≤ j → j ≤ p → ∀ t, |iteratedDeriv j f t| ≤ B := by
  classical
  obtain ⟨L,hL,B,hB,H⟩ := endpointPolynomial_uniform_centered_bounds p κ (by linarith)
  refine ⟨L,hL,B,hB,?_⟩
  intro n x a hx ha hstep hres M hM hval
  have hs : ∀ k < n, 0 < x (k+1)-x k := by
    intro k hk
    exact sub_pos.mpr (hx k (k+1) (by omega) (by omega))
  let P := endpointPolynomial p 1 (flatJet (a 0 0)) (a 0)
  let Q : ℕ → ℝ[X] := fun k => endpointPolynomial p (x (k+1)-x k) (a k) (a (k+1))
  let V := endpointPolynomial p 1 (flatJet (a n 0)) (fun j => (-1:ℝ)^j*a n j)
  let R := reflectPolynomial V 1
  let L' : NNReal := ⟨L,hL.le⟩
  let Bs : ℕ → ℝ := fun j => if j = 0 then M + B else B
  have hflat (c : ℝ) : ∀ j, 1 ≤ j → j ≤ p → |flatJet c j| ≤ κ := by
    intro j hj _hjp
    simpa only [flatJet, ite_eq_right (by omega : j ≠ 0), abs_zero] using
      (show 0 ≤ κ by linarith)
  have hPest := H 1 (by norm_num) hκ (flatJet (a 0 0)) (a 0) (hflat _)
    (flatJet_residual_positive (by linarith) (ha 0 (by omega)))
  have hVest := H 1 (by norm_num) hκ (flatJet (a n 0)) (fun j => (-1:ℝ)^j*a n j)
    (hflat _) (by
      have hv : ∀ j, 1 ≤ j → j ≤ p → |(-1:ℝ)^j*a n j| ≤ κ := by
        intro j hj hjp
        simpa using ha n le_rfl j hj hjp
      simpa only [pow_zero, one_mul] using flatJet_residual_positive (by linarith) hv)
  have hQest (k : ℕ) (hk : k < n) := H _ (hs k hk) (hstep k hk) (a k) (a (k+1))
    (ha k hk.le) (hres k hk)
  have hP0 : ∀ j ≤ p, iteratedDeriv j P.eval 0 = if j=0 then a 0 0 else 0 := by
    intro j hj
    simpa only [P, flatJet, Polynomial.iteratedDeriv_eval] using
      endpointPolynomial_zero (by norm_num : (1:ℝ) ≠ 0) (flatJet (a 0 0)) (a 0) hj
  have hP1 : ∀ j ≤ p, iteratedDeriv j P.eval 1 = a 0 j := by
    intro j hj
    simpa only [P, Polynomial.iteratedDeriv_eval] using
      endpointPolynomial_right (by norm_num : (1:ℝ) ≠ 0) (flatJet (a 0 0)) (a 0) hj
  have hV0 : ∀ j ≤ p, iteratedDeriv j V.eval 0 = if j=0 then a n 0 else 0 := by
    intro j hj
    simpa only [V, flatJet, Polynomial.iteratedDeriv_eval] using
      endpointPolynomial_zero (by norm_num : (1:ℝ) ≠ 0) (flatJet (a n 0))
        (fun j => (-1:ℝ)^j*a n j) hj
  have hV1 : ∀ j ≤ p, iteratedDeriv j V.eval 1 = (-1:ℝ)^j*a n j := by
    intro j hj
    simpa only [V, Polynomial.iteratedDeriv_eval] using
      endpointPolynomial_right (by norm_num : (1:ℝ) ≠ 0) (flatJet (a n 0))
        (fun j => (-1:ℝ)^j*a n j) hj
  have hRjets := reflectPolynomial_endpoint_jets hV0 hV1
  have hPL : LipschitzOnWith L' (iteratedDeriv p P.eval) (Icc 0 1) := by
    rw [lipschitzOnWith_iff_norm_sub_le]
    intro u hu v hv
    change ‖iteratedDeriv p P.eval u-iteratedDeriv p P.eval v‖ ≤ L*‖u-v‖
    simpa only [Real.norm_eq_abs] using hPest.1 u hu v hv
  have hVL : LipschitzOnWith L' (iteratedDeriv p V.eval) (Icc 0 1) := by
    rw [lipschitzOnWith_iff_norm_sub_le]
    intro u hu v hv
    change ‖iteratedDeriv p V.eval u-iteratedDeriv p V.eval v‖ ≤ L*‖u-v‖
    simpa only [Real.norm_eq_abs] using hVest.1 u hu v hv
  have hPB : ∀ j ≤ p, ∀ t ∈ Icc 0 1, |iteratedDeriv j P.eval t| ≤ Bs j := by
    apply abs_le_orderBound (hval 0 (by omega))
    simpa only [flatJet, ite_true] using hPest.2
  have hVB : ∀ j ≤ p, ∀ t ∈ Icc 0 1, |iteratedDeriv j V.eval t| ≤ Bs j := by
    apply abs_le_orderBound (hval n le_rfl)
    simpa only [flatJet, ite_true] using hVest.2
  have hc : OrderBoundedChain p n x a Q L' Bs := {
    increasing := hx
    left_jet := by
      intro k hk j hj
      simpa only [Q, Polynomial.iteratedDeriv_eval] using
        endpointPolynomial_zero (hs k hk).ne' (a k) (a (k+1)) hj
    right_jet := by
      intro k hk j hj
      simpa only [Q, Polynomial.iteratedDeriv_eval] using
        endpointPolynomial_right (hs k hk).ne' (a k) (a (k+1)) hj
    lipschitz := by
      intro k hk
      rw [lipschitzOnWith_iff_norm_sub_le]
      intro u hu v hv
      change ‖iteratedDeriv p (Q k).eval u-iteratedDeriv p (Q k).eval v‖ ≤ L*‖u-v‖
      simpa only [Real.norm_eq_abs] using (hQest k hk).1 u hu v hv
    bound := fun k hk => abs_le_orderBound (hval k hk.le) (hQest k hk).2 }
  obtain ⟨f,hf,hLf,hfj,hfb⟩ := hc.exists_global
    (by intro j hj; dsimp [Bs]; split_ifs <;> positivity)
    (by norm_num : (0:ℝ) < 1) P R hP0 hP1 hRjets.1 hRjets.2 hPL
    (iteratedDeriv_reflectPolynomial_lipschitzOnWith hVL) hPB
    (fun j hj => abs_iteratedDeriv_reflectPolynomial_le (hVB j hj))
  refine ⟨f,hf,hLf,hfj,?_,?_⟩
  · intro t
    simpa only [Bs, ite_true, iteratedDeriv_zero] using hfb 0 (by omega) t
  · intro j hj hjp t
    simpa only [Bs, ite_eq_right (by omega : j ≠ 0)] using hfb j hjp t

end Hermite

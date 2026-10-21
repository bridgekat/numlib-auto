import Numlib.Analysis.Calculus.HermiteInterpolationBounds
import Numlib.Analysis.Calculus.PiecewiseDerivatives
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-!
# Hermite interpolation on finitely many real intervals

The interval interpolants are joined with their full jets. A single Lipschitz constant
controls the highest derivative independently of the number or separation of knots.
When the initial jets and spacings are bounded, two unit transition intervals lead to constant
exterior tails. Their compatibility bound depends only on the original order and data bound.
-/

open Polynomial Set
open scoped NNReal

namespace Hermite

/-- A real polynomial evaluated relative to an interval's left endpoint. -/
noncomputable def shiftedPolynomial (q : ℝ[X]) (a : ℝ) : ℝ → ℝ := fun t => q.eval (t - a)

/-- Translating a polynomial translates each of its iterated derivatives. -/
theorem iteratedDeriv_shiftedPolynomial (q : ℝ[X]) (a : ℝ) (j : ℕ) :
    iteratedDeriv j (shiftedPolynomial q a) =
      fun t => (derivative^[j] q).eval (t - a) := by
  unfold shiftedPolynomial
  rw [iteratedDeriv_comp_sub_const j (fun z => q.eval z) a, Polynomial.iteratedDeriv_eval]

/-- A translated polynomial is smooth to every order. -/
theorem contDiff_shiftedPolynomial (q : ℝ[X]) (a : ℝ) (p : ℕ) :
    ContDiff ℝ p (shiftedPolynomial q a) := by
  unfold shiftedPolynomial
  have ht : ContDiff ℝ p (fun t : ℝ => t - a) := contDiff_id.sub contDiff_const
  simpa only [Function.comp_def, aeval_def, Algebra.algebraMap_self, eval₂_id] using
    (q.contDiff_aeval (p : WithTop ℕ∞)).comp ht

/-- A translation preserves an interval Lipschitz estimate. -/
theorem lipschitzOnWith_shiftedPolynomial {q : ℝ[X]} {a s : ℝ} {j : ℕ} {L : ℝ≥0}
    (h : LipschitzOnWith L (iteratedDeriv j (fun t => q.eval t)) (Icc 0 s)) :
    LipschitzOnWith L (iteratedDeriv j (shiftedPolynomial q a)) (Icc a (a + s)) := by
  rw [iteratedDeriv_shiftedPolynomial]
  rw [Polynomial.iteratedDeriv_eval] at h
  apply LipschitzOnWith.of_dist_le_mul
  intro t ht u hu
  have hh := h.dist_le_mul (t - a) ⟨by linarith [ht.1], by linarith [ht.2]⟩
    (u - a) ⟨by linarith [hu.1], by linarith [hu.2]⟩
  simpa only [Real.dist_eq, sub_sub_sub_cancel_right] using hh

/-- The highest derivative of a degree-at-most-`p` polynomial is globally constant. -/
theorem lipschitzWith_iteratedDeriv_polynomial_of_natDegree_le {q : ℝ[X]} {p : ℕ}
    (hq : q.natDegree ≤ p) : LipschitzWith 0 (iteratedDeriv p (fun t => q.eval t)) := by
  rw [Polynomial.iteratedDeriv_eval]
  apply lipschitzWith_of_nnnorm_deriv_le (derivative^[p] q).differentiable
  intro t
  have hzero : derivative^[p + 1] q = 0 := iterate_derivative_eq_zero (by omega)
  rw [Function.iterate_succ_apply'] at hzero
  rw [Polynomial.deriv, hzero, eval_zero]
  simp

/-- A translated Taylor polynomial has a globally constant highest derivative. -/
theorem lipschitzWith_shifted_endpointTaylor (p : ℕ) (a : ℕ → ℝ) (c : ℝ) :
    LipschitzWith 0 (iteratedDeriv p (shiftedPolynomial (endpointTaylor p a) c)) := by
  unfold shiftedPolynomial
  rw [iteratedDeriv_comp_sub_const p (fun z => (endpointTaylor p a).eval z) c]
  have h := lipschitzWith_iteratedDeriv_polynomial_of_natDegree_le
    (natDegree_endpointTaylor_le p a)
  apply LipschitzWith.of_dist_le_mul
  intro t u
  simpa only [NNReal.coe_zero, zero_mul] using h.dist_le_mul (t - c) (u - c)

/-- Finite compatible jets admit a globally smooth interpolant with a uniform Lipschitz
highest derivative. The exterior pieces are the endpoint Taylor polynomials. Lower derivatives
are uniformly bounded on the knot span when the initial jets and spacings are bounded. -/
theorem finite_hermite_interpolation_with_taylor_tails (p : ℕ) (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ L B : ℝ≥0, ∀ (N : ℕ), 0 < N → ∀ (x : ℕ → ℝ) (a : ℕ → ℕ → ℝ),
      (∀ i < N, x i < x (i + 1)) →
      (∀ i < N, ∀ j ≤ p,
        |a (i + 1) j - (derivative^[j] (endpointTaylor p (a i))).eval (x (i + 1) - x i)| ≤
          κ * (x (i + 1) - x i) ^ (p + 1 - j)) →
      ∃ f : ℝ → ℝ, ContDiff ℝ p f ∧ LipschitzWith L (iteratedDeriv p f) ∧
        (∀ i ≤ N, ∀ j ≤ p, iteratedDeriv j f (x i) = a i j) ∧
        (∀ j ≤ p, ∀ t ≤ x 0, iteratedDeriv j f t =
          (derivative^[j] (endpointTaylor p (a 0))).eval (t - x 0)) ∧
        (∀ j ≤ p, ∀ t ≥ x N, iteratedDeriv j f t =
          (derivative^[j] (endpointTaylor p (a N))).eval (t - x N)) ∧
        ((∀ i < N, ∀ j ≤ p, |a i j| ≤ κ) →
          (∀ i < N, x (i + 1) - x i ≤ κ) →
          ∀ j ≤ p, ∀ t ∈ Icc (x 0) (x N), |iteratedDeriv j f t| ≤ B) := by
  classical
  obtain ⟨L, B, hinterval⟩ := interval_hermite_derivative_bounds p κ hκ
  refine ⟨L, B, ?_⟩
  intro N hN x a hx ha
  have hp : ∀ i, ∃ P : ℝ[X], i < N →
      (∀ j ≤ p, iteratedDeriv j (fun t => P.eval t) 0 = a i j ∧
        iteratedDeriv j (fun t => P.eval t) (x (i + 1) - x i) = a (i + 1) j) ∧
      LipschitzOnWith L (iteratedDeriv p (fun t => P.eval t))
        (Icc 0 (x (i + 1) - x i)) ∧
      ((∀ j ≤ p, |a i j| ≤ κ) → x (i + 1) - x i ≤ κ →
        ∀ j ≤ p, ∀ t ∈ Icc 0 (x (i + 1) - x i), |iteratedDeriv j (fun t => P.eval t) t| ≤ B) := by
    intro i
    by_cases hi : i < N
    · obtain ⟨P, _, hjet, hlip, hb⟩ := hinterval (x (i + 1) - x i) (a i) (a (i + 1))
        (sub_pos.mpr (hx i hi)) (ha i hi)
      exact ⟨P, fun _ => ⟨hjet, hlip, hb⟩⟩
    · exact ⟨0, fun hi' => (hi hi').elim⟩
  choose P hP using hp
  let F : ℕ → ℝ → ℝ := fun i => if i = 0 then
    shiftedPolynomial (endpointTaylor p (a 0)) (x 0) else if i ≤ N then
    shiftedPolynomial (P (i - 1)) (x (i - 1)) else
    shiftedPolynomial (endpointTaylor p (a N)) (x N)
  have hF0 : F 0 = shiftedPolynomial (endpointTaylor p (a 0)) (x 0) := by simp [F]
  have hFi (i : ℕ) (hi : i < N) : F (i + 1) = shiftedPolynomial (P i) (x i) := by
    simp [F, Nat.succ_le_iff.mpr hi]
  have hFN : F (N + 1) = shiftedPolynomial (endpointTaylor p (a N)) (x N) := by
    simp [F]
  have hs : ∀ i ≤ N + 1, ContDiff ℝ p (F i) := by
    intro i _
    dsimp [F]
    split_ifs <;> exact contDiff_shiftedPolynomial _ _ p
  have hleft (i : ℕ) (hi : i ≤ N) (j : ℕ) (hj : j ≤ p) :
      iteratedDeriv j (F i) (x i) = a i j := by
    by_cases hi0 : i = 0
    · subst i
      simp only [hF0, iteratedDeriv_shiftedPolynomial, sub_self]
      exact eval_iterate_derivative_endpointTaylor p j (a 0) hj
    · have him : i - 1 < N := by omega
      have hieq : i - 1 + 1 = i := Nat.sub_add_cancel (by omega)
      rw [← hieq, hFi _ him, iteratedDeriv_shiftedPolynomial]
      have hh := ((hP (i - 1) him).1 j hj).2
      rw [Polynomial.iteratedDeriv_eval] at hh
      simpa only [hieq] using hh
  have hright (i : ℕ) (hi : i ≤ N) (j : ℕ) (hj : j ≤ p) :
      iteratedDeriv j (F (i + 1)) (x i) = a i j := by
    rcases hi.eq_or_lt with rfl | hi
    · simp only [hFN, iteratedDeriv_shiftedPolynomial, sub_self]
      exact eval_iterate_derivative_endpointTaylor p j (a i) hj
    · simp only [hFi i hi, iteratedDeriv_shiftedPolynomial, sub_self]
      have hh := ((hP i hi).1 j hj).1
      simpa only [Polynomial.iteratedDeriv_eval] using hh
  have hm : ∀ i ≤ N, ∀ j ≤ p,
      iteratedDeriv j (F i) (x i) = iteratedDeriv j (F (i + 1)) (x i) :=
    fun i hi j hj => (hleft i hi j hj).trans (hright i hi j hj).symm
  have hlip (i : ℕ) (hi : i < N) :
      LipschitzOnWith L (iteratedDeriv p (F (i + 1))) (Icc (x i) (x (i + 1))) := by
    rw [hFi i hi]
    have hh := lipschitzOnWith_shiftedPolynomial (a := x i) (hP i hi).2.1
    have he : x i + (x (i + 1) - x i) = x (i + 1) := by ring
    rwa [he] at hh
  have hfl : LipschitzOnWith L (iteratedDeriv p (F 0)) (Iic (x 0)) := by
    rw [hF0]
    exact ((lipschitzWith_shifted_endpointTaylor p (a 0) (x 0)).weaken
      (by exact zero_le)).lipschitzOnWith
  have hfr : LipschitzOnWith L (iteratedDeriv p (F (N + 1))) (Ici (x N)) := by
    rw [hFN]
    exact ((lipschitzWith_shifted_endpointTaylor p (a N) (x N)).weaken
      (by exact zero_le)).lipschitzOnWith
  have hglobal := contDiff_lipschitz_joinFin hx hs hm hfl hlip hfr
  have hprefix := contDiff_joinFin_of_matching_jets hx
    (fun i hi => hs i (Nat.le_succ_of_le hi)) (fun i hi => hm i hi.le)
  have hderiv (j : ℕ) (hj : j ≤ p) :
      iteratedDeriv j (joinFin x F (N + 1)) =
        joinAt (x N) (joinFin x (fun i => iteratedDeriv j (F i)) N)
          (iteratedDeriv j (F (N + 1))) := by
    have hh := contDiff_joinAt_of_matching_jets hprefix.1 (hs _ le_rfl)
      (fun k hk => by rw [hprefix.2 k hk, joinFin_eq_last x _ N hx le_rfl]; exact hm N le_rfl k hk)
    simpa only [joinFin, hprefix.2 j hj] using hh.2 j hj
  refine ⟨joinFin x F (N + 1), hglobal.1, hglobal.2, ?_, ?_, ?_, ?_⟩
  · intro i hi j hj
    rw [hderiv j hj, joinAt_of_le _ _ (le_of_adjacent_le (fun k hk => (hx k hk).le) hi le_rfl),
      joinFin_at_knot hx hi]
    exact hleft i hi j hj
  · intro j hj t ht
    rw [hderiv j hj, joinAt_of_le _ _ (ht.trans
      (le_of_adjacent_le (fun k hk => (hx k hk).le) (Nat.zero_le N) le_rfl)),
      joinFin_eq_first (fun i hi => le_of_adjacent_le (fun k hk => (hx k hk).le)
        (Nat.zero_le i) hi.le) ht, hF0, iteratedDeriv_shiftedPolynomial]
  · intro j hj t ht
    rw [hderiv j hj, joinAt_of_ge (by
      rw [joinFin_eq_last x _ N hx le_rfl]; exact hm N le_rfl j hj) ht,
      hFN, iteratedDeriv_shiftedPolynomial]
  · intro hab hsκ j hj t ht
    rw [hderiv j hj, joinAt_of_le _ _ ht.2]
    have hb0 : ‖iteratedDeriv j (F 0) (x 0)‖ ≤ B := by
      rw [Real.norm_eq_abs, hleft 0 (Nat.zero_le N) j hj]
      have hh := (hP 0 hN).2.2 (hab 0 hN) (hsκ 0 hN) j hj 0
        ⟨le_rfl, (sub_pos.mpr (hx 0 hN)).le⟩
      rwa [((hP 0 hN).1 j hj).1] at hh
    exact norm_joinFin_le_on_Icc (f := fun i => iteratedDeriv j (F i)) hb0 (fun i hi u hu => by
      rw [hFi i hi, iteratedDeriv_shiftedPolynomial, Real.norm_eq_abs]
      have hh := (hP i hi).2.2 (hab i hi) (hsκ i hi) j hj (u - x i)
        ⟨sub_nonneg.mpr hu.1, sub_le_sub_right hu.2 (x i)⟩
      simpa only [Polynomial.iteratedDeriv_eval] using hh) t ht

/-- The endpoint Taylor polynomial has a uniform linear bound in the jet amplitude on `[0,1]`. -/
theorem exists_endpointTaylor_unit_bound (p : ℕ) : ∃ C > 0,
    ∀ (a : ℕ → ℝ) (A : ℝ), 0 ≤ A → (∀ j ≤ p, |a j| ≤ A) →
      ∀ j ≤ p, |(derivative^[j] (endpointTaylor p a)).eval 1| ≤ A * C := by
  obtain ⟨C, hC, hb⟩ := exists_sum_smul_polynomial_derivative_bound
    (fun i => (X : ℝ[X]) ^ i) p p 0 1
  refine ⟨C, hC, ?_⟩
  intro a A hA ha j hj
  have hd (i : ℕ) (hi : i ≤ p) : |a i / (i.factorial : ℝ)| ≤ A := by
    rw [abs_div, abs_of_pos (show (0 : ℝ) < i.factorial from Nat.cast_pos.mpr i.factorial_pos)]
    apply (div_le_iff₀ (Nat.cast_pos.mpr i.factorial_pos)).mpr
    have hf : (1 : ℝ) ≤ i.factorial := by exact_mod_cast i.factorial_pos
    exact (ha i hi).trans (by nlinarith)
  simpa only [endpointTaylor, jetPoly, C_0, sub_zero, smul_eq_C_mul] using
    hb (fun i => a i / (i.factorial : ℝ)) A hA hd j hj 1 ⟨zero_le_one, le_rfl⟩

/-- The jet of a constant function. -/
def constantJet (v : ℝ) (j : ℕ) : ℝ := if j = 0 then v else 0

/-- The Taylor polynomial of constant data is the same constant polynomial. -/
@[simp] theorem endpointTaylor_constantJet (p : ℕ) (v : ℝ) :
    endpointTaylor p (constantJet v) = C v := by
  classical
  simp only [endpointTaylor, jetPoly, C_0, sub_zero]
  rw [Finset.sum_eq_single 0]
  · simp [constantJet]
  · intro i _ hi; simp [constantJet, hi]
  · simp

/-- Every derivative of a constant polynomial is its constant jet. -/
theorem eval_iterate_derivative_C (v t : ℝ) (j : ℕ) :
    (derivative^[j] (C v)).eval t = constantJet v j := by
  by_cases hj : j = 0
  · simp [hj, constantJet]
  · simp [iterate_derivative_C (Nat.pos_of_ne_zero hj), constantJet, hj]

/-- For finite compatible jets, the interpolant can have globally bounded lower derivatives
when the initial jets and spacings are uniformly bounded. Both constants are independent of
the knot count and minimum spacing. Constant exterior jets are connected by two unit intervals. -/
theorem exists_contDiff_lipschitz_iteratedDeriv_of_finite_jets
    (p : ℕ) (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ L B : ℝ≥0, ∀ (N : ℕ), 0 < N → ∀ (x : ℕ → ℝ) (a : ℕ → ℕ → ℝ),
      (∀ i < N, x i < x (i + 1)) →
      (∀ i < N, ∀ j ≤ p,
        |a (i + 1) j - (derivative^[j] (endpointTaylor p (a i))).eval (x (i + 1) - x i)| ≤
          κ * (x (i + 1) - x i) ^ (p + 1 - j)) →
      ∃ f : ℝ → ℝ, ContDiff ℝ p f ∧ LipschitzWith L (iteratedDeriv p f) ∧
        (∀ i ≤ N, ∀ j ≤ p, iteratedDeriv j f (x i) = a i j) ∧
        ((∀ i < N, ∀ j ≤ p, |a i j| ≤ κ) →
          (∀ i < N, x (i + 1) - x i ≤ κ) →
          ∀ j ≤ p, ∀ t, |iteratedDeriv j f t| ≤ B) := by
  classical
  obtain ⟨L₀, B₀, hbase⟩ := finite_hermite_interpolation_with_taylor_tails p κ hκ
  obtain ⟨C, hC, hunit⟩ := exists_endpointTaylor_unit_bound p
  let A : ℝ := κ + B₀ + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hκA : κ ≤ A := by dsimp [A]; nlinarith [B₀.coe_nonneg]
  have hBA : (B₀ : ℝ) ≤ A := by dsimp [A]; linarith
  let Γ : ℝ := A * (C + 2) + 1
  have hΓ : 0 < Γ := by dsimp [Γ]; positivity
  have hAΓ : A ≤ Γ := by dsimp [Γ]; nlinarith
  have hκΓ : κ ≤ Γ := hκA.trans hAΓ
  have h1Γ : 1 ≤ Γ := by dsimp [Γ]; nlinarith
  have hACΓ : A + A * C ≤ Γ := by dsimp [Γ]; nlinarith
  obtain ⟨L₁, B₁, hext⟩ := finite_hermite_interpolation_with_taylor_tails p Γ hΓ.le
  refine ⟨max L₀ L₁, max B₁ ⟨A, hA.le⟩, ?_⟩
  intro N hN x a hx ha
  obtain ⟨f₀, hf₀, hLip₀, hjet₀, _, _, hbound₀⟩ := hbase N hN x a hx ha
  by_cases hbounded : (∀ i < N, ∀ j ≤ p, |a i j| ≤ κ) ∧
      (∀ i < N, x (i + 1) - x i ≤ κ)
  swap
  · refine ⟨f₀, hf₀, hLip₀.weaken (le_max_left _ _), hjet₀, ?_⟩
    intro hba hbs
    exact (hbounded ⟨hba, hbs⟩).elim
  have hab : ∀ i ≤ N, ∀ j ≤ p, |a i j| ≤ A := by
    intro i hi j hj
    rcases hi.eq_or_lt with rfl | hi
    · rw [← hjet₀ i le_rfl j hj]
      exact (hbound₀ hbounded.1 hbounded.2 j hj (x i)
        ⟨le_of_adjacent_le (fun k hk => (hx k hk).le) (Nat.zero_le i) le_rfl, le_rfl⟩).trans hBA
    · exact (hbounded.1 i hi j hj).trans hκA
  let y : ℕ → ℝ := fun i => if i = 0 then x 0 - 1 else if i ≤ N + 1 then x (i - 1) else x N + 1
  let b : ℕ → ℕ → ℝ := fun i => if i = 0 then constantJet (a 0 0) else
    if i ≤ N + 1 then a (i - 1) else constantJet (a N 0)
  have hy0 : y 0 = x 0 - 1 := by simp [y]
  have hyi (i : ℕ) (hi : i ≤ N) : y (i + 1) = x i := by simp [y, Nat.add_le_add_right hi 1]
  have hyend : y (N + 2) = x N + 1 := by simp [y]
  have hb0 : b 0 = constantJet (a 0 0) := by simp [b]
  have hbi (i : ℕ) (hi : i ≤ N) : b (i + 1) = a i := by simp [b, Nat.add_le_add_right hi 1]
  have hbend : b (N + 2) = constantJet (a N 0) := by simp [b]
  have hy : ∀ i < N + 2, y i < y (i + 1) := by
    intro i hi
    by_cases hi0 : i = 0
    · subst i; rw [hy0, hyi 0 (Nat.zero_le N)]; linarith
    · have hie : i - 1 + 1 = i := Nat.sub_add_cancel (by omega)
      rcases (show i ≤ N + 1 by omega).eq_or_lt with rfl | hi'
      · rw [hyi N le_rfl, show N + 1 + 1 = N + 2 by omega, hyend]; linarith
      · rw [← hie, hyi (i - 1) (by omega), hie, hyi i (by omega)]
        simpa only [hie] using hx (i - 1) (by omega)
  have hb : ∀ i < N + 2, ∀ j ≤ p, |b i j| ≤ Γ := by
    intro i hi j hj
    by_cases hi0 : i = 0
    · subst i
      rw [hb0]
      by_cases hj0 : j = 0
      · simpa [constantJet, hj0] using (hab 0 (Nat.zero_le N) 0 (Nat.zero_le p)).trans hAΓ
      · simpa [constantJet, hj0] using hΓ.le
    · have hie : i - 1 + 1 = i := Nat.sub_add_cancel (by omega)
      rw [← hie, hbi (i - 1) (by omega)]
      exact (hab (i - 1) (by omega) j hj).trans hAΓ
  have hspacing : ∀ i < N + 2, y (i + 1) - y i ≤ Γ := by
    intro i hi
    by_cases hi0 : i = 0
    · subst i; rw [hy0, hyi 0 (Nat.zero_le N)]; simpa only [sub_sub_cancel] using h1Γ
    · have hie : i - 1 + 1 = i := Nat.sub_add_cancel (by omega)
      rcases (show i ≤ N + 1 by omega).eq_or_lt with rfl | hi'
      · rw [hyi N le_rfl, show N + 1 + 1 = N + 2 by omega, hyend]
        simpa only [add_sub_cancel_left] using h1Γ
      · rw [← hie, hyi (i - 1) (by omega), hie, hyi i (by omega)]
        have hh := (hbounded.2 (i - 1) (by omega)).trans hκΓ
        simpa only [hie] using hh
  have hcompat : ∀ i < N + 2, ∀ j ≤ p,
      |b (i + 1) j - (derivative^[j] (endpointTaylor p (b i))).eval (y (i + 1) - y i)| ≤
        Γ * (y (i + 1) - y i) ^ (p + 1 - j) := by
    intro i hi j hj
    by_cases hi0 : i = 0
    · subst i
      rw [hy0, hyi 0 (Nat.zero_le N), hb0, hbi 0 (Nat.zero_le N), endpointTaylor_constantJet,
        eval_iterate_derivative_C]
      simp only [sub_sub_cancel, one_pow, mul_one]
      by_cases hj0 : j = 0
      · simp [constantJet, hj0, hΓ.le]
      · simpa [constantJet, hj0] using (hab 0 (Nat.zero_le N) j hj).trans hAΓ
    · have hie : i - 1 + 1 = i := Nat.sub_add_cancel (by omega)
      rcases (show i ≤ N + 1 by omega).eq_or_lt with rfl | hi'
      · rw [hyi N le_rfl, hbi N le_rfl, show N + 1 + 1 = N + 2 by omega, hyend, hbend]
        simp only [add_sub_cancel_left, one_pow, mul_one]
        have hcj : |constantJet (a N 0) j| ≤ A := by
          by_cases hj0 : j = 0
          · simpa [constantJet, hj0] using hab N le_rfl 0 (Nat.zero_le p)
          · simp [constantJet, hj0, hA.le]
        exact (abs_sub _ _).trans ((add_le_add hcj
          (hunit (a N) A hA.le (hab N le_rfl) j hj)).trans hACΓ)
      · rw [← hie, hyi (i - 1) (by omega), hbi (i - 1) (by omega), hie,
          hyi i (by omega), hbi i (by omega)]
        have hh := (ha (i - 1) (by omega) j hj).trans
          (mul_le_mul_of_nonneg_right hκΓ (pow_nonneg (sub_pos.mpr (hx (i - 1) (by omega))).le _))
        simpa only [hie] using hh
  obtain ⟨f, hf, hLip, hjet, hleft, hright, hbound⟩ := hext (N + 2) (by omega) y b hy hcompat
  refine ⟨f, hf, hLip.weaken (le_max_right _ _), ?_, ?_⟩
  · intro i hi j hj
    have hh := hjet (i + 1) (by omega) j hj
    simpa only [hyi i hi, hbi i hi] using hh
  · intro _ _ j hj t
    rcases le_total t (y 0) with ht | ht
    · rw [hleft j hj t ht, hb0, endpointTaylor_constantJet, eval_iterate_derivative_C]
      apply le_trans _ (le_max_right (B₁ : ℝ) A)
      by_cases hj0 : j = 0
      · simpa [constantJet, hj0] using hab 0 (Nat.zero_le N) 0 (Nat.zero_le p)
      · simp [constantJet, hj0, hA.le]
    · rcases le_total t (y (N + 2)) with ht' | ht'
      · exact (hbound hb hspacing j hj t ⟨ht, ht'⟩).trans (le_max_left _ _)
      · rw [hright j hj t ht', hbend, endpointTaylor_constantJet, eval_iterate_derivative_C]
        apply le_trans _ (le_max_right (B₁ : ℝ) A)
        by_cases hj0 : j = 0
        · simpa [constantJet, hj0] using hab N le_rfl 0 (Nat.zero_le p)
        · simp [constantJet, hj0, hA.le]

end Hermite

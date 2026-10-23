import Numlib.Approximation.Hermite.Global
import Numlib.Analysis.Calculus.TaylorModel.Scalar
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Uniform monomial Hermite data for regularization lower bounds

A single nonzero derivative order gives a genuine constant-plus-monomial initial
polynomial. Every endpoint residual has the exact Hermite scaling, including
the nonzero final change in that derivative. Fixed data budgets yield actual
globally bounded C^p objectives with uniform Lipschitz highest derivatives.
-/

open Polynomial Set
namespace HighOrderRegularization.Sharpness

/-- The exponent balancing an order-`r` monomial with the order-`p+1` penalty. -/
def balance (p r : ℕ) : ℕ := p - r + 1

/-- Equally spaced real interpolation nodes. -/
def point (t : ℝ) (k : ℕ) : ℝ := k * t

/-- The nonterminal trial count at grid spacing `t`. -/
noncomputable def horizon (p : ℕ) (t : ℝ) : ℕ := ⌈1 / t ^ (p + 1)⌉₊

/-- A constant predicted objective drop at every nonterminal trial. -/
noncomputable def drop (p r : ℕ) (A t : ℝ) : ℝ := A / r.factorial * t ^ (p + 1)

/-- Values and a single nonzero positive-order derivative, halved at the last node. -/
noncomputable def jet (p r N : ℕ) (A t : ℝ) (k j : ℕ) : ℝ :=
  if j = 0 then (N - k : ℕ) * drop p r A t else
    if j = r then -(if k < N then A else A / 2) * t ^ balance p r else 0

/-- A genuine prescribed finite jet uses actual iterated derivatives. -/
def MatchesJets (f : ℝ → ℝ) (p r N : ℕ) (A t : ℝ) : Prop :=
  ∀ k ≤ N, ∀ j ≤ p, iteratedDeriv j f (point t k) = jet p r N A t k j

/-- Jet matching is the corresponding family of actual derivative equalities. -/
theorem matchesJets_iff {f : ℝ → ℝ} {p r N : ℕ} {A t : ℝ} :
    MatchesJets f p r N A t ↔
      ∀ k ≤ N, ∀ j ≤ p, iteratedDeriv j f (point t k) = jet p r N A t k j := Iff.rfl

@[simp] theorem point_zero (t : ℝ) : point t 0 = 0 := by simp [point]

/-- Each step has the stated grid spacing. -/
theorem point_succ (t : ℝ) (k : ℕ) : point t (k + 1) = point t k + t := by
  simp [point, Nat.cast_add, add_mul]

/-- Positive grid spacing gives strictly increasing nodes. -/
theorem point_strictMono {t : ℝ} (ht : 0 < t) : StrictMono (point t) := by
  intro i j hij
  exact mul_lt_mul_of_pos_right (by exact_mod_cast hij) ht

/-- The trial count is positive at every positive grid spacing. -/
theorem horizon_pos (p : ℕ) {t : ℝ} (ht : 0 < t) : 0 < horizon p t := by
  rw [horizon, Nat.pos_iff_ne_zero, ne_eq, Nat.ceil_eq_zero]
  exact not_le_of_gt (by positivity)

/-- The ceiling count times the objective power is uniformly below two. -/
theorem horizon_mul_power_lt_two (p : ℕ) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (horizon p t : ℝ) * t ^ (p + 1) < 2 := by
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 1 / t ^ (p + 1) by positivity)
  have hm := mul_lt_mul_of_pos_right hc (show 0 < t ^ (p + 1) by positivity)
  have hp : t ^ (p + 1) ≤ 1 := pow_le_one₀ ht.le ht1
  dsimp [horizon]
  calc
    _ < (1 / t ^ (p + 1) + 1) * t ^ (p + 1) := hm
    _ = 1 + t ^ (p + 1) := by field_simp
    _ ≤ 2 := by linarith

/-- Nonterminal jets give a constant plus a single monomial initial polynomial. -/
theorem initialPolynomial_eq {p r N k : ℕ} (hr : 0 < r) (hrp : r ≤ p)
    (hk : k < N) (A t : ℝ) :
    Hermite.initialPolynomial p (jet p r N A t k) =
      C (jet p r N A t k 0) - C (A * t ^ balance p r / r.factorial) * X ^ r := by
  change ∑ i ∈ Finset.range (p + 1),
    C (jet p r N A t k i / i.factorial) * (X - C 0) ^ i = _
  have heq (i : ℕ) : C (jet p r N A t k i / i.factorial) * (X - C 0) ^ i =
      (if i = 0 then C (jet p r N A t k 0) else 0) +
        (if i = r then -(C (A * t ^ balance p r / r.factorial) * X ^ r) else 0) := by
    by_cases hi0 : i = 0
    · subst i
      simp [Ne.symm (Nat.ne_of_gt hr)]
    · by_cases hir : i = r
      · subst i
        simp [jet, Nat.ne_of_gt hr, hk, sub_eq_add_neg, neg_div]
      · simp [jet, hi0, hir]
  simp_rw [heq, Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq', show 0 ∈ Finset.range (p + 1) by simp,
    show r ∈ Finset.range (p + 1) by simp; omega, sub_eq_add_neg]

/-- Actual positive derivatives of the initial polynomial have descending-factorial coefficients. -/
theorem initialPolynomial_derivative {p r N k j : ℕ} (hr : 0 < r) (hrp : r ≤ p)
    (hk : k < N) (hj : 0 < j) (A t u : ℝ) :
    (derivative^[j] (Hermite.initialPolynomial p (jet p r N A t k))).eval u =
      -(r.descFactorial j : ℝ) * (A * t ^ balance p r / r.factorial) * u ^ (r - j) := by
  rw [initialPolynomial_eq hr hrp hk]
  simp only [iterate_derivative_sub, iterate_derivative_C hj,
    iterate_derivative_C_mul, iterate_derivative_X_pow_eq_C_mul,
    eval_sub, eval_zero, eval_mul, eval_C, eval_pow, eval_X]
  ring

/-- Adjacent objective values equal the actual monomial prediction at the step. -/
theorem objective_residual_zero {p r N k : ℕ} (hr : 0 < r) (hrp : r ≤ p)
    (hk : k < N) (A t : ℝ) :
    jet p r N A t (k + 1) 0 - (Hermite.initialPolynomial p (jet p r N A t k)).eval t = 0 := by
  have hn : ((N - k : ℕ) : ℝ) = ((N - (k + 1) : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show N - k = N - (k + 1) + 1 by omega)
  have hp : balance p r + r = p + 1 := by dsimp [balance]; omega
  rw [initialPolynomial_eq hr hrp hk]
  simp only [jet, ite_true, eval_sub, eval_C, eval_mul, eval_pow, eval_X]
  rw [hn]
  dsimp [drop]
  have hpw : t ^ balance p r * t ^ r = t ^ (p + 1) := by rw [← pow_add, hp]
  rw [← hpw]
  ring

/-- Every true endpoint residual has the uniform monomial scaling. -/
theorem endpoint_residual_bound {p r N k j : ℕ} (hr : 0 < r) (hrp : r ≤ p)
    (hk : k < N) (hj : j ≤ p) {A t : ℝ} (hA : 0 ≤ A) (ht : 0 < t) :
    |jet p r N A t (k + 1) j -
      (derivative^[j] (Hermite.initialPolynomial p (jet p r N A t k))).eval t| ≤
        A * t ^ (p - j + 1) := by
  by_cases hj0 : j = 0
  · subst j
    rw [Function.iterate_zero_apply, objective_residual_zero hr hrp hk]
    simp only [abs_zero]
    positivity
  have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
  rw [initialPolynomial_derivative hr hrp hk hjpos]
  by_cases hjr : j = r
  · subst j
    rw [Nat.descFactorial_self, Nat.sub_self, pow_zero, mul_one]
    have heq : -(r.factorial : ℝ) * (A * t ^ balance p r / r.factorial) =
        -A * t ^ balance p r := by field_simp
    rw [heq]
    by_cases hk1 : k + 1 < N
    · simpa [jet, Nat.ne_of_gt hr, hk1] using
        (show 0 ≤ A * t ^ (p - r + 1) by positivity)
    · simp only [jet, ite_eq_right (Nat.ne_of_gt hr), ite_true, ite_eq_right hk1]
      have he : -(A / 2) * t ^ balance p r - -A * t ^ balance p r =
          A / 2 * t ^ balance p r := by ring
      rw [he, abs_of_nonneg (by positivity)]
      dsimp [balance]
      nlinarith [show 0 ≤ A * t ^ (p - r + 1) by positivity]
  · rw [show jet p r N A t (k + 1) j = 0 by simp [jet, hj0, hjr]]
    by_cases hjle : j ≤ r
    · have hd : (r.descFactorial j : ℝ) / r.factorial ≤ 1 := by
        apply (div_le_one (by positivity : (0 : ℝ) < r.factorial)).2
        exact_mod_cast (show r.descFactorial j ≤ r.factorial by
          have hh := Nat.factorial_mul_descFactorial hjle
          have hf := Nat.factorial_pos (r - j)
          nlinarith)
      have hp : balance p r + (r - j) = p - j + 1 := by dsimp [balance]; omega
      have heq : -(r.descFactorial j : ℝ) * (A * t ^ balance p r / r.factorial) *
          t ^ (r - j) = -((r.descFactorial j : ℝ) / r.factorial *
            A * t ^ (p - j + 1)) := by
        rw [← hp, pow_add]
        ring
      rw [heq, zero_sub, neg_neg, abs_of_nonneg (by positivity)]
      calc
        (r.descFactorial j : ℝ) / r.factorial * A * t ^ (p - j + 1) ≤
            1 * A * t ^ (p - j + 1) := by gcongr
        _ = _ := by ring
    · rw [Nat.descFactorial_of_lt (by omega : r < j)]
      simp only [Nat.cast_zero, neg_zero, zero_mul, sub_zero, abs_zero]
      positivity

/-- A fixed bound for values, positive jets, grid steps and normalized residuals. -/
noncomputable def dataBound (p : ℕ) (A T C : ℝ) : ℝ :=
  max T (max A (max (A * C) (A * T ^ (p + 1))))

/-- Fixed data budgets precede both the number of nodes and the grid spacing. -/
theorem uniform_data {p r N : ℕ} (hr : 0 < r) (hrp : r ≤ p)
    {A T C t : ℝ} (hA : 0 ≤ A) (hT : 1 ≤ T)
    (ht : 0 < t) (htT : t ≤ T) (hcount : (N : ℝ) * t ^ (p + 1) ≤ C) :
    (∀ k ≤ N, ∀ j ≤ p, |jet p r N A t k j| ≤ dataBound p A T C) ∧
    (∀ k < N, point t (k + 1) - point t k ≤ dataBound p A T C) ∧
    (∀ k < N, ∀ j ≤ p,
      |jet p r N A t (k + 1) j -
        (derivative^[j] (Hermite.initialPolynomial p (jet p r N A t k))).eval
          (point t (k + 1) - point t k)| ≤
      dataBound p A T C * (point t (k + 1) - point t k) ^ (p - j + 1)) := by
  have hAT : A * T ^ (p + 1) ≤ dataBound p A T C :=
    (le_max_right (A * C) _).trans ((le_max_right A _).trans (le_max_right T _))
  have hAC : A * C ≤ dataBound p A T C :=
    (le_max_left _ _).trans ((le_max_right A _).trans (le_max_right T _))
  have hAK : A ≤ dataBound p A T C := (le_max_left _ _).trans (le_max_right T _)
  have hTK : T ≤ dataBound p A T C := le_max_left _ _
  have htp : t ^ balance p r ≤ T ^ (p + 1) :=
    (pow_le_pow_left₀ ht.le htT _).trans
      (pow_le_pow_right₀ hT (by dsimp [balance]; omega))
  have hstep (k : ℕ) : point t (k + 1) - point t k = t := by rw [point_succ]; ring
  refine ⟨?_, ?_, ?_⟩
  · intro k hk j hj
    by_cases hj0 : j = 0
    · subst j
      simp only [jet, ite_true, drop]
      rw [abs_of_nonneg (by positivity)]
      have hn : ((N - k : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N k
      have hf : (1 : ℝ) ≤ r.factorial := by exact_mod_cast Nat.factorial_pos r
      have hh : A / r.factorial ≤ A := div_le_self hA hf
      calc
        ((N - k : ℕ) : ℝ) * (A / r.factorial * t ^ (p + 1)) ≤
            (N : ℝ) * (A * t ^ (p + 1)) := by gcongr
        _ = A * ((N : ℝ) * t ^ (p + 1)) := by ring
        _ ≤ A * C := mul_le_mul_of_nonneg_left hcount hA
        _ ≤ _ := hAC
    · by_cases hjr : j = r
      · subst j
        simp only [jet, ite_eq_right hj0, ite_true]
        by_cases hkN : k < N
        · rw [ite_eq_left hkN, abs_mul, abs_neg, abs_of_nonneg hA,
            abs_of_nonneg (by positivity)]
          exact (mul_le_mul_of_nonneg_left htp hA).trans hAT
        · rw [ite_eq_right hkN, abs_mul, abs_neg,
            abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
          have hh : A / 2 * t ^ balance p r ≤ A * T ^ (p + 1) := by
            calc _ ≤ A * t ^ balance p r := by
                   nlinarith [show 0 ≤ A * t ^ balance p r by positivity]
                 _ ≤ _ := mul_le_mul_of_nonneg_left htp hA
          exact hh.trans hAT
      · simp only [jet, ite_eq_right hj0, ite_eq_right hjr, abs_zero]
        exact hA.trans hAK
  · intro k hk
    rw [hstep]
    exact htT.trans hTK
  · intro k hk j hj
    rw [hstep]
    exact (endpoint_residual_bound hr hrp hk hj hA ht).trans
      (mul_le_mul_of_nonneg_right hAK (by positivity))

/-- Uniformly bounded monomial data are realized by globally smooth actual
objectives, with the highest derivative Lipschitz and every prescribed jet attained.
The constants are chosen before the count and spacing. -/
theorem exists_uniform_objectives {p r : ℕ} (hr : 0 < r) (hrp : r ≤ p)
    {A T C : ℝ} (hA : 0 ≤ A) (hT : 1 ≤ T) :
    ∃ (L : ℝ) (hL : 0 < L), ∃ B > 0,
      ∀ N : ℕ, 0 < N → ∀ t : ℝ, 0 < t → t ≤ T →
        (N : ℝ) * t ^ (p + 1) ≤ C →
        ∃ f : ℝ → ℝ, ContDiff ℝ p f ∧
          LipschitzWith ⟨L, hL.le⟩ (iteratedDeriv p f) ∧
          MatchesJets f p r N A t ∧ ∀ j ≤ p, ∀ x, |iteratedDeriv j f x| ≤ B := by
  have hκ : 0 ≤ dataBound p A T C := (zero_le_one.trans hT).trans (le_max_left _ _)
  obtain ⟨L, hL, B, hB, hex⟩ := Hermite.exists_uniform_interpolant p (dataBound p A T C) hκ
  refine ⟨L, hL, B, hB, ?_⟩
  intro N hN t ht htT hcount
  have hd := uniform_data hr hrp hA hT ht htT hcount
  obtain ⟨f, hf, hLip, hjet, hb⟩ := hex N hN (point t) (jet p r N A t)
    (fun i j hij _ => point_strictMono ht hij) hd.2.2
  exact ⟨f, hf, hLip, hjet, hb ⟨fun k hk => hd.1 k hk.le, hd.2.1⟩⟩

end HighOrderRegularization.Sharpness

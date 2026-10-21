import Numlib.Optimization.TaylorOptimality
import Numlib.Analysis.SpecialFunctions.FactorialSeries
import Mathlib.Tactic.Ring

/-!
# Inexact finite Taylor models

Arbitrary continuous multilinear coefficients form polynomial models. Certified coefficient
errors control their decrements and compact gaps. The constant coefficient is independent of
the positive-degree coefficients, and cancels from every decrement. No surrogate objective
whose derivatives produce the approximate coefficients is required.
-/

noncomputable section
open scoped Nat
namespace Optimization.InexactTaylorModels

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A coefficient family with certified errors against the true positive-order derivatives.
Only orders up to `q` are used; the scalar constant may itself be inexact. -/
structure ApproximateJet (f : E → ℝ) (x : E) (q : ℕ) where
  constant : ℝ
  coefficient : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ
  error : ℕ → ℝ
  error_le : ∀ i ∈ Finset.Icc 1 q, ‖coefficient i - iteratedFDeriv ℝ i f x‖ ≤ error i

/-- Requested positive accuracies and fixed nonnegative error multipliers. The contract is
mathematical data; an algorithm need not know the multipliers. -/
structure RequestedAccuracy {f : E → ℝ} {x : E} {q : ℕ} (J : ApproximateJet f x q) where
  request : ℕ → ℝ
  multiplier : ℕ → ℝ
  request_pos : ∀ i ∈ Finset.Icc 1 q, 0 < request i
  multiplier_nonneg : ∀ i ∈ Finset.Icc 1 q, 0 ≤ multiplier i
  error_le : ∀ i ∈ Finset.Icc 1 q, J.error i ≤ multiplier i * request i

/-- A factorial-normalized finite polynomial with a separate constant coefficient. -/
def polynomial (c : ℝ)
    (A : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ)
    (q : ℕ) (s : E) : ℝ :=
  c + ∑ i ∈ Finset.Icc 1 q, A i (fun _ => s) / (i ! : ℝ)

/-- The constant-free decrement of a finite polynomial. -/
def decrement (A : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ)
    (q : ℕ) (s : E) : ℝ :=
  -(∑ i ∈ Finset.Icc 1 q, A i (fun _ => s) / (i ! : ℝ))

/-- Positive homogeneous terms vanish at zero. -/
@[simp] theorem polynomial_zero (c : ℝ)
    (A : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ) (q : ℕ) :
    polynomial c A q 0 = c := by
  unfold polynomial
  have h : ∀ i ∈ Finset.Icc 1 q, A i (fun _ => (0 : E)) / (i ! : ℝ) = 0 := by
    intro i hi
    have hi' : 0 < i := (Finset.mem_Icc.mp hi).1
    rw [(A i).map_coord_zero (⟨0, hi'⟩ : Fin i) rfl]
    simp
  rw [Finset.sum_eq_zero h, add_zero]

/-- The scalar constant cancels exactly, even when it is an inexact function value. -/
theorem decrement_eq (c : ℝ)
    (A : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ)
    (q : ℕ) (s : E) :
    decrement A q s = polynomial c A q 0 - polynomial c A q s := by
  rw [polynomial_zero]
  simp [decrement, polynomial]

/-- Every finite coefficient decrement is continuous. -/
theorem continuous_decrement
    (A : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ) (q : ℕ) :
    Continuous (decrement A q) := by
  apply Continuous.neg
  apply continuous_finsetSum
  intro i _
  exact ((A i).cont.comp (continuous_pi fun _ => continuous_id)).div_const _

/-- Coefficient subtraction gives the actual finite expansion of decrement differences. -/
theorem decrement_sub
    (A B : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ)
    (q : ℕ) (s : E) :
    decrement A q s - decrement B q s =
      -(∑ i ∈ Finset.Icc 1 q, (A i - B i) (fun _ => s) / (i ! : ℝ)) := by
  simp only [decrement, sub_apply, sub_div, Finset.sum_sub_distrib]
  ring

/-- Exact derivative coefficients recover the existing Taylor decrement. -/
theorem decrement_iteratedFDeriv (f : E → ℝ) (x : E) (q : ℕ) (s : E) :
    decrement (fun i => iteratedFDeriv ℝ i f x) q s =
      TaylorCriticality.taylorDecrement f q x s := by
  induction q with
  | zero => simp [decrement]
  | succ q ih =>
    rw [TaylorCriticality.taylorDecrement_succ, ← ih]
    unfold decrement
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ q + 1)]
    simp only [div_eq_mul_inv]
    ring

/-- Absolute decrement error is bounded by the factorial-weighted coefficient errors. -/
theorem decrement_error_le
    (A B : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ)
    (e : ℕ → ℝ) (q : ℕ) (s : E)
    (hcoeff : ∀ i ∈ Finset.Icc 1 q, ‖A i - B i‖ ≤ e i) :
    |decrement A q s - decrement B q s| ≤
      ∑ i ∈ Finset.Icc 1 q, e i * ‖s‖ ^ i / (i ! : ℝ) := by
  rw [decrement_sub, abs_neg, ← Real.norm_eq_abs]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  have h := (A i - B i).le_opNorm (fun _ => s)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  have hh := h.trans (mul_le_mul_of_nonneg_right (hcoeff i hi) (pow_nonneg (norm_nonneg s) i))
  simpa only [norm_div, Real.norm_natCast] using
    div_le_div_of_nonneg_right hh (Nat.cast_nonneg i.factorial)

/-- The positive reciprocal-factorial sum is uniformly at most two. -/
theorem sum_inv_factorial_le_two (q : ℕ) :
    ∑ i ∈ Finset.Icc 1 q, (1 / (i ! : ℝ)) ≤ 2 := by
  have hset : Finset.Icc 1 q = (Finset.range (q + 1)).filter (1 ≤ ·) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_range]
    omega
  rw [hset]
  simpa using Real.sum_pos_pow_div_factorial_le (δ := 1) (by norm_num) (q + 1)

/-- Uniform coefficient error bounds give a uniform compact-radius error bound. -/
theorem error_sum_le {e : ℕ → ℝ} {q : ℕ} {δ K : ℝ}
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (hK : 0 ≤ K)
    (he : ∀ i ∈ Finset.Icc 1 q, e i ≤ K) :
    ∑ i ∈ Finset.Icc 1 q, e i * δ ^ i / (i ! : ℝ) ≤ 2 * K := by
  calc
    _ ≤ ∑ i ∈ Finset.Icc 1 q, K / (i ! : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact div_le_div_of_nonneg_right
        ((mul_le_mul_of_nonneg_right (he i hi) (pow_nonneg hδ.1 i)).trans
          (mul_le_of_le_one_right hK (pow_le_one₀ hδ.1 hδ.2))) (by positivity)
    _ = K * ∑ i ∈ Finset.Icc 1 q, (1 / (i ! : ℝ)) := by rw [Finset.mul_sum]; congr 1; funext i; ring
    _ ≤ 2 * K := by nlinarith [mul_le_mul_of_nonneg_left (sum_inv_factorial_le_two q) hK]

/-- Step-dependent coefficient errors give an order-`p+1` error without division by the step
norm or by error constants. In particular, zero steps and zero constants are included. -/
theorem decrement_error_le_step_power
    (A B : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ)
    {q p : ℕ} (s : E) {K κ : ℝ} (hqp : q ≤ p) (hK : 0 ≤ K) (hκ : 0 ≤ κ)
    (hcoeff : ∀ i ∈ Finset.Icc 1 q,
      ‖A i - B i‖ ≤ K * κ * ‖s‖ ^ (p - i + 1)) :
    |decrement A q s - decrement B q s| ≤ 2 * K * κ * ‖s‖ ^ (p + 1) := by
  apply (decrement_error_le A B (fun i => K * κ * ‖s‖ ^ (p - i + 1)) q s hcoeff).trans
  have heq : ∀ i ∈ Finset.Icc 1 q,
      K * κ * ‖s‖ ^ (p - i + 1) * ‖s‖ ^ i / (i ! : ℝ) =
        (K * κ * ‖s‖ ^ (p + 1)) * (1 / (i ! : ℝ)) := by
    intro i hi
    have hi' : i ≤ p := (Finset.mem_Icc.mp hi).2.trans hqp
    rw [mul_assoc, ← pow_add, show p - i + 1 + i = p + 1 by omega]
    ring
  rw [Finset.sum_congr rfl heq, ← Finset.mul_sum]
  have h := mul_le_mul_of_nonneg_left (sum_inv_factorial_le_two q)
    (mul_nonneg (mul_nonneg hK hκ) (pow_nonneg (norm_nonneg s) (p + 1)))
  nlinarith only [h]

/-- An approximate compact gap and an independent half-tolerance error budget certify the
true compact gap. The displacement set is retained rather than replaced by a formal scalar. -/
theorem approximate_gap_certifies
    (A B : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ)
    (e : ℕ → ℝ) {D : Set E} {δ ε : ℝ} {q : ℕ}
    (hD : IsCompact D) (hne : D.Nonempty) (hδ : 0 ≤ δ)
    (hball : D ⊆ Metric.closedBall 0 δ)
    (hcoeff : ∀ i ∈ Finset.Icc 1 q, ‖A i - B i‖ ≤ e i)
    (hgap : TaylorCriticality.gapOn (decrement A q) D ≤ ε * δ ^ q / (2 * (q ! : ℝ)))
    (herr : ∑ i ∈ Finset.Icc 1 q, e i * δ ^ i / (i ! : ℝ) ≤
      ε * δ ^ q / (2 * (q ! : ℝ))) :
    TaylorCriticality.gapOn (decrement B q) D ≤ ε * δ ^ q / (q ! : ℝ) := by
  have h := TaylorCriticality.gapOn_perturb_le A B e hD hne
    (continuous_decrement A q).continuousOn (continuous_decrement B q).continuousOn
    hδ hball hcoeff (fun d _ => decrement_sub A B q d)
  have := (abs_le.mp h).1
  have heq : ε * δ ^ q / (q ! : ℝ) =
      2 * (ε * δ ^ q / (2 * (q ! : ℝ))) := by ring
  rw [heq]
  linarith

/-- Acceptance using two inexact objective values transfers to genuine objective decrease
when their common error budget is small enough relative to the positive predicted decrement. -/
theorem true_decrease_of_inexact_acceptance {X : Type*} (f : X → ℝ) (x y : X)
    {fx fy h η D : ℝ} (hD : 0 < D)
    (hx : |fx - f x| ≤ h) (hy : |fy - f y| ≤ h)
    (haccept : η ≤ (fx - fy) / D) (hbudget : 2 * h ≤ η * D / 2) :
    η * D / 2 ≤ f x - f y := by
  have ha := (le_div_iff₀ hD).mp haccept
  have hx' := (abs_le.mp hx).2
  have hy' := (abs_le.mp hy).1
  linarith

/-- Exact derivative coefficients and the true constant give the original Taylor model. -/
theorem polynomial_iteratedFDeriv (f : E → ℝ) (x : E) (q : ℕ) (s : E) :
    polynomial (f x) (fun i => iteratedFDeriv ℝ i f x) q s =
      RegularizedTaylorModel.taylorModel f q x s := by
  have h := decrement_iteratedFDeriv f x q s
  rw [decrement_eq (f x), polynomial_zero, TaylorCriticality.taylorDecrement_eq] at h
  linarith

/-- A possibly inexact constant adds its own error to the constant-free decrement error. -/
theorem polynomial_error_le (f : E → ℝ) (x : E) (c : ℝ)
    (A : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ)
    (q : ℕ) (s : E) :
    |polynomial c A q s - RegularizedTaylorModel.taylorModel f q x s| ≤
      |c - f x| + |decrement A q s - TaylorCriticality.taylorDecrement f q x s| := by
  have heq : polynomial c A q s - RegularizedTaylorModel.taylorModel f q x s =
      (c - f x) - (decrement A q s - TaylorCriticality.taylorDecrement f q x s) := by
    rw [decrement_eq c, polynomial_zero, TaylorCriticality.taylorDecrement_eq]
    ring
  rw [heq]
  simpa only [Real.norm_eq_abs] using norm_sub_le (c - f x)
    (decrement A q s - TaylorCriticality.taylorDecrement f q x s)

/-- Exact function values identify model-value error with decrement error. -/
theorem polynomial_error_eq (f : E → ℝ) (x : E)
    (A : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ)
    (q : ℕ) (s : E) :
    |polynomial (f x) A q s - RegularizedTaylorModel.taylorModel f q x s| =
      |decrement A q s - TaylorCriticality.taylorDecrement f q x s| := by
  rw [decrement_eq (f x), polynomial_zero, TaylorCriticality.taylorDecrement_eq]
  have heq : f x - polynomial (f x) A q s -
      (f x - RegularizedTaylorModel.taylorModel f q x s) =
      -(polynomial (f x) A q s - RegularizedTaylorModel.taylorModel f q x s) := by ring
  rw [heq, abs_neg]

/-- Compact gap perturbation for actual coefficient polynomials. -/
theorem gap_error_le
    (A B : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ)
    (e : ℕ → ℝ) {q : ℕ} {D : Set E} {δ : ℝ}
    (hD : IsCompact D) (hne : D.Nonempty) (hδ : 0 ≤ δ)
    (hball : D ⊆ Metric.closedBall 0 δ)
    (hcoeff : ∀ i ∈ Finset.Icc 1 q, ‖A i - B i‖ ≤ e i) :
    |TaylorCriticality.gapOn (decrement A q) D -
      TaylorCriticality.gapOn (decrement B q) D| ≤
      ∑ i ∈ Finset.Icc 1 q, e i * δ ^ i / (i ! : ℝ) :=
  TaylorCriticality.gapOn_perturb_le A B e hD hne
    (continuous_decrement A q).continuousOn (continuous_decrement B q).continuousOn
    hδ hball hcoeff (fun d _ => decrement_sub A B q d)

/-- A finite coefficient polynomial with factorial-normalized radial regularization. -/
def regularizedPolynomial (c : ℝ)
    (A : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ)
    (p : ℕ) (σ : ℝ) (s : E) : ℝ :=
  polynomial c A p s + σ * ‖s‖ ^ (p + 1) / ((p + 1)! : ℝ)

/-- Splitting the polynomial at a lower truncation order isolates its actual higher terms. -/
theorem polynomial_eq_truncation_add (c : ℝ)
    (A : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ)
    {j p : ℕ} (hjp : j ≤ p) (s : E) :
    polynomial c A p s = polynomial c A j s +
      ∑ i ∈ Finset.Icc (j + 1) p, A i (fun _ => s) / (i ! : ℝ) := by
  have hdisj : Disjoint (Finset.Icc 1 j) (Finset.Icc (j + 1) p) := by
    apply Finset.disjoint_left.mpr
    intro i hi hi'
    have := (Finset.mem_Icc.mp hi).2
    have := (Finset.mem_Icc.mp hi').1
    omega
  have hunion : Finset.Icc 1 j ∪ Finset.Icc (j + 1) p = Finset.Icc 1 p := by
    ext i
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  unfold polynomial
  rw [← hunion, Finset.sum_union hdisj]
  ring

/-- A regularized finite polynomial differs from its lower-order decrement by a factorial
tail controlled by its supplied coefficient norms. This uses the approximate coefficients
themselves and needs no derivatives of a surrogate function. -/
theorem regularized_decrease_ge_truncation (c : ℝ)
    (A : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ)
    {j p : ℕ} (hjp : j ≤ p) {L σ δ : ℝ} (hL : 0 ≤ L)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (d : E) (hd : ‖d‖ ≤ δ)
    (hA : ∀ i ∈ Finset.Icc (j + 1) p, ‖A i‖ ≤ L) :
    decrement A j d - 2 * max L σ * δ ^ (j + 1) / (j ! : ℝ) ≤
      c - regularizedPolynomial c A p σ d := by
  let M := max L σ
  have hM : 0 ≤ M := hL.trans (le_max_left _ _)
  have hterm : ∀ i ∈ Finset.Icc (j + 1) p,
      A i (fun _ => d) / (i ! : ℝ) ≤ M * δ ^ i / (i ! : ℝ) := by
    intro i hi
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc
      _ ≤ ‖A i (fun _ => d)‖ := le_abs_self _
      _ ≤ ‖A i‖ * ‖d‖ ^ i := by simpa using (A i).le_opNorm (fun _ => d)
      _ ≤ M * δ ^ i := mul_le_mul ((hA i hi).trans (le_max_left _ _))
        (pow_le_pow_left₀ (norm_nonneg d) hd i) (pow_nonneg (norm_nonneg d) i) hM
  have hreg : σ * ‖d‖ ^ (p + 1) / ((p + 1)! : ℝ) ≤
      M * δ ^ (p + 1) / ((p + 1)! : ℝ) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul (le_max_right _ _) (pow_le_pow_left₀ (norm_nonneg d) hd _)
      (pow_nonneg (norm_nonneg d) _) hM
  have htail : (∑ i ∈ Finset.Icc (j + 1) p, A i (fun _ => d) / (i ! : ℝ)) +
      σ * ‖d‖ ^ (p + 1) / ((p + 1)! : ℝ) ≤
      2 * M * δ ^ (j + 1) / (j ! : ℝ) := by
    calc
      _ ≤ (∑ i ∈ Finset.Icc (j + 1) p, M * δ ^ i / (i ! : ℝ)) +
          M * δ ^ (p + 1) / ((p + 1)! : ℝ) :=
        add_le_add (Finset.sum_le_sum hterm) hreg
      _ = M * ∑ i ∈ Finset.Icc (j + 1) (p + 1), δ ^ i / (i ! : ℝ) := by
        rw [Finset.sum_Icc_succ_top (by omega : j + 1 ≤ p + 1), mul_add,
          Finset.mul_sum]
        simp only [mul_div_assoc]
      _ ≤ M * (2 * δ ^ (j + 1) / (j ! : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hM
        have hset : Finset.Icc (j + 1) (p + 1) =
            (Finset.range (p + 2)).filter (j + 1 ≤ ·) := by
          ext i
          simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_range]
          omega
        rw [hset]
        exact Real.sum_tail_pow_div_factorial_le hδ j (p + 2)
      _ = _ := by ring
  have heq := decrement_eq c A j d
  rw [polynomial_zero] at heq
  rw [regularizedPolynomial, polynomial_eq_truncation_add c A hjp]
  dsimp [M] at htail
  linarith

/-- A small enough radius transfers a positive truncated decrement to at least half as
much regularized model decrease. The radius condition is written without division, so it
also handles vanishing coefficient and regularization bounds. -/
theorem half_decrease_of_small_radius (c : ℝ)
    (A : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ)
    {j p : ℕ} (hjp : j ≤ p) {L σ δ α : ℝ} (hL : 0 ≤ L)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (d : E) (hd : ‖d‖ ≤ δ)
    (hA : ∀ i ∈ Finset.Icc (j + 1) p, ‖A i‖ ≤ L)
    (hsmall : 4 * max L σ * δ ≤ α)
    (hdec : α * δ ^ j / (j ! : ℝ) ≤ decrement A j d) :
    α * δ ^ j / (2 * (j ! : ℝ)) ≤ c - regularizedPolynomial c A p σ d := by
  have h := regularized_decrease_ge_truncation c A hjp (σ := σ) hL hδ d hd hA
  have hmul := mul_le_mul_of_nonneg_right hsmall
    (div_nonneg (pow_nonneg hδ.1 j) (Nat.cast_nonneg j.factorial))
  rw [pow_succ] at h
  have heq : α * δ ^ j / (2 * (j ! : ℝ)) = (α * δ ^ j / (j ! : ℝ)) / 2 := by ring
  rw [heq]
  ring_nf at h hmul hdec ⊢
  linarith only [h, hmul, hdec]

/-- Retaining a strictly decreasing model witness makes the predicted decrement positive
and pays for its regularizer. The witness and comparison are actual model-value premises. -/
theorem decrement_pos_of_retained_model_decrease (c : ℝ)
    (A : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ)
    (p : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) {d s : E}
    (hd : regularizedPolynomial c A p σ d < c)
    (hs : regularizedPolynomial c A p σ s ≤ regularizedPolynomial c A p σ d) :
    σ * ‖s‖ ^ (p + 1) / ((p + 1)! : ℝ) ≤ decrement A p s ∧
      0 < decrement A p s ∧ s ≠ 0 := by
  have hh : regularizedPolynomial c A p σ s < c := hs.trans_lt hd
  have he := decrement_eq c A p s
  rw [polynomial_zero] at he
  unfold regularizedPolynomial at hh
  have hr : 0 ≤ σ * ‖s‖ ^ (p + 1) / ((p + 1)! : ℝ) := by positivity
  have hp : 0 < decrement A p s := by linarith
  refine ⟨by linarith, hp, ?_⟩
  intro hz
  rw [hz, decrement_eq c, polynomial_zero, sub_self] at hp
  exact (lt_irrefl 0 hp)

end Optimization.InexactTaylorModels

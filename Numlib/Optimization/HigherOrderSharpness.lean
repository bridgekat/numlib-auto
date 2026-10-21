import Numlib.Optimization.FlatJetChain
import Numlib.Optimization.HigherOrderRegularizationRun
import Numlib.Optimization.CubicSharpTrace

/-!
# Sharp higher-order regularization runs

A single negative derivative of a chosen order gives sparse Taylor data. Uniform Hermite
extension supplies bounded objectives and Lipschitz highest derivatives independently of the
tolerances and execution length. Normalizing the active derivative by `(q-1)!/p!` makes the
chosen steps solve the actual unit-regularization model equation. Its Hessian and cubic
residual bounds hold on every unit direction. Complete executions first stop at the last
knot and also first satisfy the full objective quality test there. Each criticality branch
attains its exact ceiling lower bound; choosing the hardest branch gives their maximum.
-/
noncomputable section
open scoped NNReal Topology
namespace Optimization.HigherOrderSharpness
open Polynomial

/-- Constant negative derivative of order `q`, switched off at the last knot, and objective
values decreasing by its Taylor prediction. -/
def sparseJet (N q : ℕ) (G h : ℝ) (k j : ℕ) : ℝ :=
  if j = 0 then -(k : ℝ) * G * h ^ q / q.factorial else
  if j = q then if k < N then -G else 0 else 0

/-- The active Taylor polynomial has only its constant and order-`q` coefficients. -/
theorem endpointTaylor_sparseJet {N p q k : ℕ} {G h : ℝ}
    (hq : 1 ≤ q) (hqp : q ≤ p) (hk : k < N) :
    Hermite.endpointTaylor p (sparseJet N q G h k) =
      C (-(k : ℝ) * G * h ^ q / q.factorial) + C (-G / q.factorial) * X ^ q := by
  classical
  unfold Hermite.endpointTaylor Hermite.jetPoly
  simp only [C_0, sub_zero]
  rw [Finset.sum_range_succ']
  have he : ∑ x ∈ Finset.range p,
      C (sparseJet N q G h k (x + 1) / ((x + 1).factorial : ℝ)) * X ^ (x + 1) =
      C (-G / q.factorial) * X ^ q := by
    rw [Finset.sum_eq_single (q - 1)]
    · simp [sparseJet, hk, Nat.sub_add_cancel hq, show q ≠ 0 by omega]
    · intro i hi hiq
      have hin : i + 1 ≠ q := by omega
      simp [sparseJet, hin]
    · intro hz
      exact (hz (by simp; omega)).elim
  rw [he]
  simp [sparseJet, add_comm]

/-- Positive-order derivatives of the sparse polynomial are explicit falling-factorial terms. -/
theorem eval_iterate_derivative_sparse {q j : ℕ} {a G h : ℝ} (hj : 0 < j) :
    (derivative^[j] (C a + C (-G / q.factorial) * X ^ q)).eval h =
      (-G / q.factorial) * (q.descFactorial j : ℝ) * h ^ (q - j) := by
  rw [← Module.End.pow_apply, map_add, eval_add, Module.End.pow_apply, Module.End.pow_apply,
    iterate_derivative_C hj, eval_zero, zero_add, iterate_derivative_C_mul,
    iterate_derivative_X_pow_eq_C_mul]
  simp [mul_assoc]

private theorem descFactorial_div_factorial_le_one {q j : ℕ} (hj : j ≤ q) :
    (q.descFactorial j : ℝ) / q.factorial ≤ 1 := by
  have he : ((q - j).factorial : ℝ) * (q.descFactorial j : ℝ) = q.factorial := by
    exact_mod_cast Nat.factorial_mul_descFactorial hj
  have hfac : (1 : ℝ) ≤ (q - j).factorial := by exact_mod_cast Nat.factorial_pos (q - j)
  rw [div_le_one (by positivity)]
  nlinarith [(show (0 : ℝ) ≤ (q.descFactorial j : ℝ) by positivity)]

/-- The sparse chain has uniform scaled Taylor discrepancies at every derivative order. -/
theorem sparseJet_compatible {N p q : ℕ} {G h κ : ℝ} (hq : 1 ≤ q) (hqp : q ≤ p)
    (hG : 0 ≤ G) (hh : 0 < h) (hκ : 0 ≤ κ) (hscale : G ≤ κ * h ^ (p - q + 1)) :
    ∀ k < N, ∀ j ≤ p,
      |sparseJet N q G h (k + 1) j -
        (derivative^[j] (Hermite.endpointTaylor p (sparseJet N q G h k))).eval h| ≤
        κ * h ^ (p + 1 - j) := by
  intro k hk j hj
  rw [endpointTaylor_sparseJet hq hqp hk]
  by_cases hj0 : j = 0
  · subst j
    simp only [Function.iterate_zero_apply, eval_add, eval_C, eval_mul, eval_pow, eval_X,
      sparseJet, ↓reduceIte, Nat.cast_add, Nat.cast_one]
    have he : -((k : ℝ) + 1) * G * h ^ q / q.factorial -
        (-(k : ℝ) * G * h ^ q / q.factorial + -G / q.factorial * h ^ q) = 0 := by ring
    rw [he, abs_zero]
    positivity
  rw [eval_iterate_derivative_sparse (by omega)]
  by_cases hjq : j ≤ q
  · have hprod : (p - q + 1) + (q - j) = p + 1 - j := by omega
    have hbound : G / q.factorial * (q.descFactorial j : ℝ) * h ^ (q - j) ≤
        κ * h ^ (p + 1 - j) := by
      calc
        _ = G * h ^ (q - j) * ((q.descFactorial j : ℝ) / q.factorial) := by ring
        _ ≤ G * h ^ (q - j) * 1 :=
          mul_le_mul_of_nonneg_left (descFactorial_div_factorial_le_one hjq) (by positivity)
        _ ≤ (κ * h ^ (p - q + 1)) * h ^ (q - j) := by
          simpa using mul_le_mul_of_nonneg_right hscale (pow_nonneg hh.le (q - j))
        _ = _ := by rw [mul_assoc, ← pow_add, hprod]
    by_cases heq : j = q
    · subst j
      simp only [sparseJet, ite_eq_right hj0, ↓reduceIte, Nat.sub_self, pow_zero, mul_one,
        Nat.descFactorial_self]
      have hc : -G / (q.factorial : ℝ) * q.factorial = -G := by field_simp
      rw [hc]
      split_ifs
      · simp only [sub_self, abs_zero]; positivity
      · simpa [abs_of_nonneg hG, show p + 1 - q = p - q + 1 by omega] using hscale
    · simp only [sparseJet, ite_eq_right hj0, ite_eq_right heq, zero_sub, neg_mul, neg_div,
        abs_neg, abs_of_nonneg (by positivity : 0 ≤ G / (q.factorial : ℝ) *
          (q.descFactorial j : ℝ) * h ^ (q - j))]
      exact hbound
  · simp only [sparseJet, ite_eq_right hj0, ite_eq_right (by omega : j ≠ q),
      Nat.descFactorial_of_lt (by omega : q < j), Nat.cast_zero, mul_zero, zero_mul,
      sub_self, abs_zero]
    positivity

/-- Initial sparse jets are uniformly bounded by their total value drop and active derivative. -/
theorem abs_sparseJet_le {N q : ℕ} {G h κ : ℝ} (hG : 0 ≤ G) (hh : 0 ≤ h)
    (hκ : 0 ≤ κ) (hdrop : (N : ℝ) * G * h ^ q ≤ κ) (hslope : G ≤ κ) :
    ∀ k < N, ∀ j : ℕ, |sparseJet N q G h k j| ≤ κ := by
  intro k hk j
  by_cases hj0 : j = 0
  · subst j
    simp only [sparseJet, ↓reduceIte]
    rw [show -(k : ℝ) * G * h ^ q / q.factorial =
      -((k : ℝ) * G * h ^ q / q.factorial) by ring, abs_neg, abs_of_nonneg (by positivity)]
    have hkn : (k : ℝ) ≤ N := by exact_mod_cast hk.le
    have hfac : (1 : ℝ) ≤ q.factorial := by exact_mod_cast Nat.factorial_pos q
    calc
      _ ≤ (k : ℝ) * G * h ^ q := div_le_self (by positivity) hfac
      _ ≤ (N : ℝ) * G * h ^ q :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hkn hG) (by positivity)
      _ ≤ κ := hdrop
  · by_cases hjq : j = q
    · have hq0 : q ≠ 0 := by omega
      simpa [sparseJet, hjq, hk, hq0, abs_of_nonneg hG] using hslope
    · simpa [sparseJet, hj0, hjq] using hκ

/-- Uniform bounded extensions of sparse chains, for arbitrary derivative and model orders.
The regularity and boundedness constants are chosen before the chain length and spacing. -/
theorem exists_sparseJet_chain (p q : ℕ) (hq : 1 ≤ q) (hqp : q ≤ p)
    (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ L B : ℝ≥0, ∀ N : ℕ, 0 < N → ∀ G h : ℝ, 0 ≤ G → 0 < h →
      G ≤ κ * h ^ (p - q + 1) → (N : ℝ) * G * h ^ q ≤ κ → G ≤ κ → h ≤ κ →
      ∃ f : ℝ → ℝ, ContDiff ℝ p f ∧ LipschitzWith L (iteratedDeriv p f) ∧
        (∀ k ≤ N, ∀ j ≤ p, iteratedDeriv j f ((k : ℝ) * h) = sparseJet N q G h k j) ∧
        (∀ j ≤ p, ∀ t : ℝ, |iteratedDeriv j f t| ≤ B) := by
  obtain ⟨L, B, hjet⟩ := Hermite.exists_contDiff_lipschitz_iteratedDeriv_of_finite_jets p κ hκ
  refine ⟨L, B, ?_⟩
  intro N hN G h hG hh hscale hdrop hslope hspacing
  have hdiff (k : ℕ) : ((k + 1 : ℕ) : ℝ) * h - (k : ℝ) * h = h := by push_cast; ring
  obtain ⟨f, hf, hLip, he, hb⟩ := hjet N hN (fun k => (k : ℝ) * h) (sparseJet N q G h)
    (fun k _ => by push_cast; nlinarith)
    (fun k hk j hj => by rw [hdiff]; exact sparseJet_compatible hq hqp hG hh hκ hscale k hk j hj)
  exact ⟨f, hf, hLip, he, hb (fun k hk j _ => abs_sparseJet_le hG hh.le hκ hdrop hslope k hk j)
    (fun k _ => by simpa only [hdiff] using hspacing)⟩

open HigherOrderRegularization RegularizedTaylorModel

/-- Scalar Taylor models equal the polynomial obtained directly from their derivative jet. -/
theorem taylorModel_eq_endpointTaylor (f : ℝ → ℝ) (p : ℕ) (x s : ℝ) :
    taylorModel f p x s = (Hermite.endpointTaylor p (fun j => iteratedDeriv j f x)).eval s := by
  rw [taylorModel_real]
  simp only [Hermite.endpointTaylor, Hermite.jetPoly, C_0, sub_zero, eval_finsetSum,
    eval_mul, eval_C, eval_pow, eval_X, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- A sparse objective jet determines the actual factorial-normalized regularized model. -/
theorem model_of_sparseJet {N p q k : ℕ} {f : ℝ → ℝ} {G h σ s : ℝ}
    (hq : 1 ≤ q) (hqp : q ≤ p) (hk : k < N)
    (hjet : ∀ j ≤ p, iteratedDeriv j f ((k : ℝ) * h) = sparseJet N q G h k j) :
    model f p ((k : ℝ) * h) σ s =
      -(k : ℝ) * G * h ^ q / q.factorial + (-G / q.factorial) * s ^ q +
        σ / ((p + 1).factorial : ℝ) * |s| ^ (p + 1) := by
  rw [model, taylorModel_eq_endpointTaylor]
  have he : Hermite.endpointTaylor p (fun j => iteratedDeriv j f ((k : ℝ) * h)) =
      Hermite.endpointTaylor p (sparseJet N q G h k) := by
    unfold Hermite.endpointTaylor Hermite.jetPoly
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only
    rw [hjet j (by simpa using hj)]
  rw [he, endpointTaylor_sparseJet hq hqp hk]
  simp

/-- On a positive step, every positive-order actual model derivative is an explicit sum of
falling-factorial terms. The norm regularization is handled by local equality on the positive
half-line, so the formula applies equally to even and odd model degrees. -/
theorem iteratedDeriv_model_of_sparseJet {N p q k j : ℕ} {f : ℝ → ℝ} {G h σ s : ℝ}
    (hq : 1 ≤ q) (hqp : q ≤ p) (hk : k < N) (hj : 0 < j) (hs : 0 < s)
    (hjet : ∀ i ≤ p, iteratedDeriv i f ((k : ℝ) * h) = sparseJet N q G h k i) :
    iteratedDeriv j (model f p ((k : ℝ) * h) σ) s =
      (-G / q.factorial) * (q.descFactorial j : ℝ) * s ^ (q - j) +
        (σ / ((p + 1).factorial : ℝ)) * ((p + 1).descFactorial j : ℝ) * s ^ (p + 1 - j) := by
  let a := -(k : ℝ) * G * h ^ q / q.factorial
  have he : model f p ((k : ℝ) * h) σ =ᶠ[𝓝 s]
      (fun t : ℝ => a + (-G / q.factorial) * t ^ q +
        σ / ((p + 1).factorial : ℝ) * t ^ (p + 1)) := by
    filter_upwards [eventually_gt_nhds hs] with t ht
    rw [model_of_sparseJet hq hqp hk hjet, abs_of_pos ht]
  rw [he.iteratedDeriv_eq j]
  have hfun : (fun t : ℝ => a + (-G / q.factorial) * t ^ q +
      σ / ((p + 1).factorial : ℝ) * t ^ (p + 1)) =
      (fun t : ℝ => a + ((-G / q.factorial) * t ^ q +
        σ / ((p + 1).factorial : ℝ) * t ^ (p + 1))) := by ext; ring
  rw [hfun, iteratedDeriv_const_add hj,
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field,
    iteratedDeriv_pow, iteratedDeriv_pow]
  ring

/-- The magnitude that makes a positive step solve the actual unit-regularization model
first-order equation. -/
def normalizedMagnitude (p q : ℕ) (h : ℝ) : ℝ :=
  ((q - 1).factorial : ℝ) / p.factorial * h ^ (p - q + 1)

/-- The actual model gradient vanishes at the chosen step, for all three criticality orders. -/
theorem model_deriv_zero {N p q k : ℕ} {f : ℝ → ℝ} {h : ℝ}
    (hq : 1 ≤ q) (hq3 : q ≤ 3) (hqp : q ≤ p) (hk : k < N) (hh : 0 < h)
    (hjet : ∀ i ≤ p, iteratedDeriv i f ((k : ℝ) * h) =
      sparseJet N q (normalizedMagnitude p q h) h k i) :
    deriv (model f p ((k : ℝ) * h) 1) h = 0 := by
  have he := iteratedDeriv_model_of_sparseJet hq hqp hk (j := 1) (σ := 1) (by decide) hh hjet
  rw [iteratedDeriv_one] at he
  rw [he]
  simp only [Nat.descFactorial_one, Nat.add_sub_cancel]
  have hfac : (p.factorial : ℝ) ≠ 0 := by positivity
  have hp : (p + 1 : ℝ) ≠ 0 := by positivity
  have hpow1 : h ^ (p - 1 + 1) = h ^ p := by rw [Nat.sub_add_cancel (by omega : 1 ≤ p)]
  interval_cases q
  · simp only [normalizedMagnitude, Nat.factorial_zero, Nat.factorial_one,
      Nat.cast_one, Nat.sub_self, pow_zero, mul_one]
    rw [hpow1, Nat.factorial_succ]
    push_cast
    field_simp
    ring
  · have hpow2 : h ^ (p - 2 + 1) * h = h ^ p := by
      rw [← pow_succ, show p - 2 + 1 + 1 = p by omega]
    norm_num only [normalizedMagnitude, Nat.reduceSub, Nat.factorial_one, Nat.factorial_two,
      Nat.cast_one, Nat.cast_ofNat, pow_one]
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    nlinarith [hpow2]
  · have hpow3 : h ^ (p - 3 + 1) * h ^ 2 = h ^ p := by
      rw [← pow_add, show p - 3 + 1 + 2 = p by omega]
    norm_num only [normalizedMagnitude, Nat.reduceSub, Nat.factorial_two, Nat.factorial_succ,
      Nat.cast_one, Nat.cast_ofNat]
    rw [Nat.cast_mul]
    push_cast
    field_simp
    nlinarith [hpow3]

/-- The actual model Hessian at the selected positive step, in scalar form. -/
theorem model_second_deriv {N p q k : ℕ} {f : ℝ → ℝ} {h : ℝ}
    (hp : 2 ≤ p) (hq : 1 ≤ q) (hq3 : q ≤ 3) (hqp : q ≤ p) (hk : k < N) (hh : 0 < h)
    (hjet : ∀ i ≤ p, iteratedDeriv i f ((k : ℝ) * h) =
      sparseJet N q (normalizedMagnitude p q h) h k i) :
    iteratedDeriv 2 (model f p ((k : ℝ) * h) 1) h =
      ((p : ℝ) + 1 - q) / p.factorial * h ^ (p - 1) := by
  rw [iteratedDeriv_model_of_sparseJet hq hqp hk (by decide) hh hjet]
  have hfac : (p.factorial : ℝ) ≠ 0 := by positivity
  have hpn : (p + 1 : ℝ) ≠ 0 := by positivity
  have hp2 : p + 1 - 2 = p - 1 := by omega
  interval_cases q
  · norm_num only [normalizedMagnitude, Nat.reduceSub, Nat.factorial_zero, Nat.factorial_one,
      Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.cast_zero, Nat.cast_one, zero_mul,
      mul_zero, zero_add, one_mul]
    rw [Nat.factorial_succ, hp2]
    push_cast
    field_simp
    ring
  · norm_num only [normalizedMagnitude, Nat.reduceSub, Nat.factorial_one, Nat.factorial_two,
      Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, pow_zero, mul_one]
    rw [Nat.factorial_succ, hp2, show p - 2 + 1 = p - 1 by omega]
    push_cast
    field_simp
    ring
  · have hpow : h ^ (p - 3 + 1) * h = h ^ (p - 1) := by
      rw [← pow_succ, show p - 3 + 1 + 1 = p - 1 by omega]
    norm_num only [normalizedMagnitude, Nat.reduceSub, Nat.factorial_two,
      Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, pow_one, mul_one]
    rw [Nat.factorial_succ, hp2]
    push_cast
    field_simp
    nlinarith [hpow]

/-- The actual third model derivative at the selected step. -/
theorem model_third_deriv {N p q k : ℕ} {f : ℝ → ℝ} {h : ℝ}
    (hp : 3 ≤ p) (hq : 1 ≤ q) (hq3 : q ≤ 3) (hqp : q ≤ p) (hk : k < N) (hh : 0 < h)
    (hjet : ∀ i ≤ p, iteratedDeriv i f ((k : ℝ) * h) =
      sparseJet N q (normalizedMagnitude p q h) h k i) :
    iteratedDeriv 3 (model f p ((k : ℝ) * h) 1) h =
      ((p : ℝ) * (p - 1) - (q - 1) * (q - 2)) / p.factorial * h ^ (p - 2) := by
  rw [iteratedDeriv_model_of_sparseJet hq hqp hk (by decide) hh hjet]
  have hfac : (p.factorial : ℝ) ≠ 0 := by positivity
  have hpn : (p + 1 : ℝ) ≠ 0 := by positivity
  have hp2 : p + 1 - 2 = p - 1 := by omega
  have hp3 : p + 1 - 3 = p - 2 := by omega
  have hpcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
  interval_cases q <;>
    norm_num only [normalizedMagnitude, Nat.reduceSub, Nat.factorial_zero, Nat.factorial_one,
      Nat.factorial_two, Nat.factorial_succ, Nat.descFactorial_succ, Nat.descFactorial_zero,
      Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, zero_mul, mul_zero, zero_add,
      one_mul, mul_one, pow_zero] <;>
    rw [hp2, hp3] <;> push_cast <;>
    rw [hpcast] <;>
    (try rw [show p - 3 + 1 = p - 2 by omega]) <;>
    field_simp <;> ring

/-- Normalized magnitudes are positive at positive spacing. -/
theorem normalizedMagnitude_pos (p q : ℕ) {h : ℝ} (hh : 0 < h) :
    0 < normalizedMagnitude p q h := by unfold normalizedMagnitude; positivity

/-- The normalized magnitude obeys the uniform compatibility scale. -/
theorem normalizedMagnitude_le {p q : ℕ} {h : ℝ} (hq : 1 ≤ q) (hqp : q ≤ p) (hh : 0 ≤ h) :
    normalizedMagnitude p q h ≤ h ^ (p - q + 1) := by
  have hf : ((q - 1).factorial : ℝ) ≤ p.factorial := by
    exact_mod_cast Nat.factorial_le (show q - 1 ≤ p by omega)
  have hratio : ((q - 1).factorial : ℝ) / p.factorial ≤ 1 :=
    (div_le_one (by positivity)).mpr hf
  simpa [normalizedMagnitude] using
    mul_le_mul_of_nonneg_right hratio (pow_nonneg hh _)

/-- The scalar model Hessian lies between zero and the direction-test threshold. -/
theorem model_second_deriv_bounds {N p q k : ℕ} {f : ℝ → ℝ} {h : ℝ}
    (hp : 2 ≤ p) (hq : 1 ≤ q) (hq3 : q ≤ 3) (hqp : q ≤ p) (hk : k < N) (hh : 0 < h)
    (hjet : ∀ i ≤ p, iteratedDeriv i f ((k : ℝ) * h) =
      sparseJet N q (normalizedMagnitude p q h) h k i) :
    0 ≤ iteratedDeriv 2 (model f p ((k : ℝ) * h) 1) h ∧
      iteratedDeriv 2 (model f p ((k : ℝ) * h) 1) h ≤ h ^ (p - 1) := by
  rw [model_second_deriv hp hq hq3 hqp hk hh hjet]
  have hqr : (q : ℝ) ≤ p := by exact_mod_cast hqp
  have hqr1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hpf : (p : ℝ) ≤ p.factorial := by exact_mod_cast Nat.self_le_factorial p
  have hn : 0 ≤ ((p : ℝ) + 1 - q) / p.factorial :=
    div_nonneg (by linarith) (by positivity)
  constructor
  · positivity
  · have hc : ((p : ℝ) + 1 - q) / p.factorial ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    simpa using mul_le_mul_of_nonneg_right hc (pow_nonneg hh.le (p - 1))

/-- The actual scalar third derivative obeys the unit residual bound. -/
theorem model_third_deriv_bounds {N p q k : ℕ} {f : ℝ → ℝ} {h : ℝ}
    (hp : 3 ≤ p) (hq : 1 ≤ q) (hq3 : q ≤ 3) (hqp : q ≤ p) (hk : k < N) (hh : 0 < h)
    (hjet : ∀ i ≤ p, iteratedDeriv i f ((k : ℝ) * h) =
      sparseJet N q (normalizedMagnitude p q h) h k i) :
    |iteratedDeriv 3 (model f p ((k : ℝ) * h) 1) h| ≤ h ^ (p - 2) := by
  rw [model_third_deriv hp hq hq3 hqp hk hh hjet]
  have hpr : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hdesc := descFactorial_div_factorial_le_one (show 2 ≤ p by omega)
  have hpcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
  norm_num only [Nat.descFactorial_succ, Nat.descFactorial_zero, mul_one, Nat.sub_zero,
    Nat.cast_mul] at hdesc
  rw [hpcast] at hdesc
  have hc : 0 ≤ ((p : ℝ) * (p - 1) - (q - 1) * (q - 2)) / p.factorial ∧
      ((p : ℝ) * (p - 1) - (q - 1) * (q - 2)) / p.factorial ≤ 1 := by
    interval_cases q <;> norm_num only [Nat.cast_ofNat] <;> constructor
    all_goals first
      | apply div_nonneg <;> (first | positivity | nlinarith)
      | rw [div_le_one (by positivity)]; have hd := (div_le_one (by positivity)).mp hdesc; nlinarith
  rw [abs_of_nonneg (mul_nonneg hc.1 (pow_nonneg hh.le _))]
  simpa using mul_le_mul_of_nonneg_right hc.2 (pow_nonneg hh.le (p - 2))

/-- The model Hessian is the scalar second derivative in every direction. -/
theorem model_curvature {N p q k : ℕ} {f : ℝ → ℝ} {h : ℝ}
    (hp : 2 ≤ p) (hq : 1 ≤ q) (hq3 : q ≤ 3) (hqp : q ≤ p) (hk : k < N) (hh : 0 < h)
    (hjet : ∀ i ≤ p, iteratedDeriv i f ((k : ℝ) * h) =
      sparseJet N q (normalizedMagnitude p q h) h k i) :
    leastCurvature (fderiv ℝ (fderiv ℝ (model f p ((k : ℝ) * h) 1)) h) =
      ((p : ℝ) + 1 - q) / p.factorial * h ^ (p - 1) := by
  apply leastCurvature_eq_of_scalar
  intro u
  have he := iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod (𝕜 := ℝ)
    (f := model f p ((k : ℝ) * h) 1) (x := h) (m := fun _ : Fin 2 => u)
  rw [iteratedFDeriv_two_apply, model_second_deriv hp hq hq3 hqp hk hh hjet] at he
  simpa [Fin.prod_univ_two, Real.norm_eq_abs, sq_abs, smul_eq_mul, mul_assoc,
    mul_comm, mul_left_comm, pow_two] using he

/-- All unit directions pass the actual model's small-curvature test. -/
theorem model_smallCurvatureDirections {N p q k : ℕ} {f : ℝ → ℝ} {h : ℝ}
    (hp : 2 ≤ p) (hq : 1 ≤ q) (hq3 : q ≤ 3) (hqp : q ≤ p) (hk : k < N) (hh : 0 < h)
    (hjet : ∀ i ≤ p, iteratedDeriv i f ((k : ℝ) * h) =
      sparseJet N q (normalizedMagnitude p q h) h k i) :
    smallCurvatureDirections (model f p ((k : ℝ) * h) 1) h (h ^ (p - 1)) =
      {d : ℝ | ‖d‖ = 1} := by
  ext d
  constructor
  · exact fun hd => hd.1
  · intro hd
    refine ⟨hd, ?_⟩
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
    have hdabs : |d| = 1 := hd
    have hb := model_second_deriv_bounds hp hq hq3 hqp hk hh hjet
    simpa [Finset.prod_const, Fintype.card_fin, smul_eq_mul, abs_mul, abs_pow, hdabs,
      abs_of_nonneg hb.1] using hb.2

/-- The chosen step satisfies every activated actual model residual, including cubic tests
on its nonempty direction set. -/
theorem modelResiduals {N p q r k : ℕ} {f : ℝ → ℝ} {h : ℝ}
    (hrp : r ≤ p) (hq : 1 ≤ q) (hq3 : q ≤ 3) (hqp : q ≤ p) (hk : k < N) (hh : 0 < h)
    (hjet : ∀ i ≤ p, iteratedDeriv i f ((k : ℝ) * h) =
      sparseJet N q (normalizedMagnitude p q h) h k i) :
    ModelResiduals r p (fun _ => 1) f ((k : ℝ) * h) 1 h := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← norm_deriv_eq_norm_fderiv, model_deriv_zero hq hq3 hqp hk hh hjet]
    simp
  · intro hr
    rw [model_curvature (by omega) hq hq3 hqp hk hh hjet]
    have hb := (model_second_deriv_bounds (by omega) hq hq3 hqp hk hh hjet).1
    rw [model_second_deriv (by omega) hq hq3 hqp hk hh hjet] at hb
    exact (neg_nonpos.mpr (by positivity)).trans hb
  · intro hr d hd
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
    have hdabs : |d| = 1 := hd.1
    have hb := model_third_deriv_bounds (by omega) hq hq3 hqp hk hh hjet
    simpa [Finset.prod_const, Fintype.card_fin, smul_eq_mul, abs_mul, abs_pow, hdabs,
      Real.norm_eq_abs, abs_of_pos hh] using hb

/-- The negative Taylor term at the selected step is an explicit positive scalar. -/
theorem normalizedMagnitude_taylor_drop {p q : ℕ} {h : ℝ} (hq : 1 ≤ q) (hqp : q ≤ p) :
    normalizedMagnitude p q h / q.factorial * h ^ q =
      h ^ (p + 1) / ((q : ℝ) * p.factorial) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hfac : ((q - 1).factorial : ℝ) ≠ 0 := by positivity
  have hfacp : (p.factorial : ℝ) ≠ 0 := by positivity
  have hf : (q.factorial : ℝ) = (q : ℝ) * (q - 1).factorial := by
    exact_mod_cast (Nat.mul_factorial_pred (by omega : q ≠ 0)).symm
  unfold normalizedMagnitude
  rw [hf]
  field_simp
  rw [← pow_add, show p - q + 1 + q = p + 1 by omega]

/-- Every active selected step strictly decreases the actual regularized model. -/
theorem model_decrease {N p q k : ℕ} {f : ℝ → ℝ} {h : ℝ}
    (hq : 1 ≤ q) (hqp : q ≤ p) (hk : k < N) (hh : 0 < h)
    (hjet : ∀ i ≤ p, iteratedDeriv i f ((k : ℝ) * h) =
      sparseJet N q (normalizedMagnitude p q h) h k i) :
    model f p ((k : ℝ) * h) 1 h < model f p ((k : ℝ) * h) 1 0 := by
  have hf := hjet 0 (by omega)
  simp only [iteratedDeriv_zero, sparseJet, ↓reduceIte] at hf
  rw [model_zero, hf, model_of_sparseJet hq hqp hk hjet, abs_of_pos hh]
  have hd := normalizedMagnitude_taylor_drop (h := h) hq hqp
  have hineq : h ^ (p + 1) / ((p + 1).factorial : ℝ) <
      h ^ (p + 1) / ((q : ℝ) * p.factorial) := by
    apply div_lt_div_of_pos_left (pow_pos hh _)
    · exact mul_pos (by exact_mod_cast (by omega : 0 < q)) (by positivity)
    · rw [Nat.factorial_succ, Nat.cast_mul]
      exact mul_lt_mul_of_pos_right (by exact_mod_cast (by omega : q < p + 1)) (by positivity)
  simp only [neg_div, neg_mul]
  rw [hd]
  rw [show 1 / ((p + 1).factorial : ℝ) * h ^ (p + 1) =
    h ^ (p + 1) / ((p + 1).factorial : ℝ) by ring]
  linarith

/-- The prescribed successor values make the actual acceptance ratio exactly one. -/
theorem ratio_one {N p q k : ℕ} {f : ℝ → ℝ} {h : ℝ}
    (hq : 1 ≤ q) (hqp : q ≤ p) (hk : k < N) (hh : 0 < h)
    (hjet : ∀ i ≤ N, ∀ j ≤ p, iteratedDeriv j f ((i : ℝ) * h) =
      sparseJet N q (normalizedMagnitude p q h) h i j) :
    ratio f p ((k : ℝ) * h) h = 1 := by
  have ht : taylorModel f p ((k : ℝ) * h) h = f (((k + 1 : ℕ) : ℝ) * h) := by
    have hm := model_of_sparseJet hq hqp hk (hjet k hk.le) (σ := 0) (s := h)
    simp only [model, zero_div, zero_mul, add_zero] at hm
    rw [hm]
    have hv := hjet (k + 1) hk 0 (by omega)
    simp only [iteratedDeriv_zero, sparseJet, ↓reduceIte, Nat.cast_add, Nat.cast_one] at hv
    push_cast
    rw [hv]
    ring
  have hv := hjet k hk.le 0 (by omega)
  have hv' := hjet (k + 1) hk 0 (by omega)
  simp only [iteratedDeriv_zero, sparseJet, ↓reduceIte] at hv hv'
  rw [ratio, ite_eq_right hh.ne', taylorModel_zero, ht,
    show (k : ℝ) * h + h = ((k + 1 : ℕ) : ℝ) * h by push_cast; ring]
  apply div_self
  rw [hv, hv']
  have hG := normalizedMagnitude_pos p q hh
  have he : -(k : ℝ) * normalizedMagnitude p q h * h ^ q / q.factorial -
      -((k + 1 : ℕ) : ℝ) * normalizedMagnitude p q h * h ^ q / q.factorial =
      normalizedMagnitude p q h * h ^ q / q.factorial := by push_cast; ring
  rw [he]
  positivity

/-- The actual objective Hessian at a sparse knot is exactly its prescribed scalar. -/
theorem objective_curvature {N p q k : ℕ} {f : ℝ → ℝ} {G h : ℝ}
    (hp : 2 ≤ p)
    (hjet : ∀ i ≤ p, iteratedDeriv i f ((k : ℝ) * h) = sparseJet N q G h k i) :
    leastCurvature (fderiv ℝ (fderiv ℝ f) ((k : ℝ) * h)) =
      if q = 2 then if k < N then -G else 0 else 0 := by
  apply leastCurvature_eq_of_scalar
  intro u
  have he := iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod (𝕜 := ℝ)
    (f := f) (x := (k : ℝ) * h) (m := fun _ : Fin 2 => u)
  rw [iteratedFDeriv_two_apply, hjet 2 hp] at he
  simpa [sparseJet, eq_comm, Fin.prod_univ_two, Real.norm_eq_abs, sq_abs,
    smul_eq_mul, mul_assoc, mul_comm, mul_left_comm, pow_two] using he

/-- No active sparse knot passes the algorithm's stopping test when its corresponding
criticality tolerance is strictly smaller than the prescribed derivative magnitude. -/
theorem not_stationary {N p q r k : ℕ} {f : ℝ → ℝ} {G h : ℝ}
    {epsilon : Fin 3 → ℝ} {D : Set ℝ}
    (hq : 1 ≤ q) (hq3 : q ≤ 3) (hqr : q ≤ r) (hrp : r ≤ p) (hk : k < N)
    (hG : 0 < G) (heps : ∀ i, 0 < epsilon i)
    (hthreshold : epsilon ⟨q - 1, by omega⟩ < G)
    (hjet : ∀ i ≤ p, iteratedDeriv i f ((k : ℝ) * h) = sparseJet N q G h k i)
    (hunit : ∀ d ∈ D, ‖d‖ = 1) :
    ¬Stationary r epsilon f ((k : ℝ) * h) D := by
  intro hstop
  interval_cases q
  · have hg := hstop.first
    rw [← norm_deriv_eq_norm_fderiv, ← iteratedDeriv_one, hjet 1 (by omega)] at hg
    norm_num [sparseJet, hk, Real.norm_eq_abs, abs_of_pos hG] at hg
    exact (not_le_of_gt hthreshold) hg
  · have hH := hstop.second (by omega) (heps 1).le
    rw [objective_curvature (by omega) hjet] at hH
    norm_num [hk] at hH
    exact (not_le_of_gt hthreshold) (by simpa using hH)
  · have hh := hstop.third (by omega) (by
      rw [objective_curvature (by omega) hjet]
      norm_num
      exact (heps 1).le)
    obtain ⟨d, hd⟩ := hh.1
    have ht := (hh.2 d hd).1
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, hjet 3 (by omega)] at ht
    have hdabs : |d| = 1 := hunit d hd
    norm_num [sparseJet, hk, Finset.prod_const, Fintype.card_fin, smul_eq_mul,
      abs_mul, abs_pow, hdabs, abs_of_pos hG] at ht
    exact (not_le_of_gt hthreshold) ht

/-- Full objective quality tests use every nearly flat objective direction. -/
def ObjectiveQuality (r : ℕ) (epsilon : Fin 3 → ℝ) (f : ℝ → ℝ) (z : ℝ) : Prop :=
  ‖fderiv ℝ f z‖ ≤ epsilon 0 ∧
    (2 ≤ r → -epsilon 1 ≤ leastCurvature (fderiv ℝ (fderiv ℝ f) z)) ∧
    (3 ≤ r → ∀ d ∈ smallCurvatureDirections f z (epsilon 1),
      |iteratedFDeriv ℝ 3 f z (fun _ => d)| ≤ epsilon 2)

/-- Every active sparse knot fails the full objective quality test, including the full
objective-defined direction set in the third-order case. -/
theorem not_objectiveQuality {N p q r k : ℕ} {f : ℝ → ℝ} {G h : ℝ}
    {epsilon : Fin 3 → ℝ}
    (hq : 1 ≤ q) (hq3 : q ≤ 3) (hqr : q ≤ r) (hrp : r ≤ p) (hk : k < N)
    (hG : 0 < G) (heps : ∀ i, 0 < epsilon i)
    (hthreshold : epsilon ⟨q - 1, by omega⟩ < G)
    (hjet : ∀ i ≤ p, iteratedDeriv i f ((k : ℝ) * h) = sparseJet N q G h k i) :
    ¬ObjectiveQuality r epsilon f ((k : ℝ) * h) := by
  intro hstop
  interval_cases q
  · have hg := hstop.1
    rw [← norm_deriv_eq_norm_fderiv, ← iteratedDeriv_one, hjet 1 (by omega)] at hg
    norm_num [sparseJet, hk, Real.norm_eq_abs, abs_of_pos hG] at hg
    exact (not_le_of_gt hthreshold) hg
  · have hH := hstop.2.1 (by omega)
    rw [objective_curvature (by omega) hjet] at hH
    norm_num [hk] at hH
    exact (not_le_of_gt hthreshold) (by simpa using hH)
  · have hmem : (1 : ℝ) ∈ smallCurvatureDirections f ((k : ℝ) * h) (epsilon 1) := by
      constructor
      · norm_num
      · rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, hjet 2 (by omega)]
        norm_num [sparseJet]
        exact (heps 1).le
    have ht := hstop.2.2 (by omega) 1 hmem
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, hjet 3 (by omega)] at ht
    norm_num [sparseJet, hk, abs_of_pos hG] at ht
    exact (not_le_of_gt hthreshold) ht

/-- A completely stationary last sparse jet satisfies the exact algorithm stop, as soon as
its activated third-order direction set is nonempty. -/
theorem stationary_terminal {N p q r : ℕ} {f : ℝ → ℝ} {G h : ℝ}
    {epsilon : Fin 3 → ℝ} {D : Set ℝ} (hr : 1 ≤ r) (hrp : r ≤ p)
    (heps : ∀ i, 0 < epsilon i) (hD : 3 ≤ r → D.Nonempty)
    (hjet : ∀ i ≤ p, iteratedDeriv i f ((N : ℝ) * h) = sparseJet N q G h N i) :
    Stationary r epsilon f ((N : ℝ) * h) D := by
  refine ⟨?_, fun hr2 => Or.inr ⟨?_, fun hr3 => ⟨hD hr3, fun d hd => ?_⟩⟩⟩
  · rw [← norm_deriv_eq_norm_fderiv, ← iteratedDeriv_one, hjet 1 (by omega)]
    simpa [sparseJet] using (heps 0).le
  · rw [objective_curvature (by omega) hjet]
    simp only [lt_self_iff_false, ite_false, ite_self]
    exact neg_nonpos.mpr (heps 1).le
  · rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
      iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
      hjet 3 (by omega), hjet 2 (by omega)]
    simpa [sparseJet] using And.intro (heps 2).le (heps 1).le

/-- The complete finite chain obeys all actual ARp laws and stops for the first time at its
last knot. The other tolerances may be arbitrary positive numbers. -/
theorem isRun_of_sparseJet {N p q r : ℕ} {f : ℝ → ℝ} {h : ℝ}
    {epsilon : Fin 3 → ℝ} (hN : 0 < N) (hr : 1 ≤ r) (hr3 : r ≤ 3) (hqr : q ≤ r)
    (hq : 1 ≤ q) (hrp : r ≤ p) (hh : 0 < h) (heps : ∀ i, 0 < epsilon i)
    (hthreshold : epsilon ⟨q - 1, by omega⟩ < normalizedMagnitude p q h)
    (hjet : ∀ k ≤ N, ∀ j ≤ p, iteratedDeriv j f ((k : ℝ) * h) =
      sparseJet N q (normalizedMagnitude p q h) h k j) :
    IsRun CubicRegularization.sharpParameters r p (fun _ => 1) epsilon f
      (fun k => (k : ℝ) * h) (fun _ => h) (fun _ => 1) N := by
  have hqp := hqr.trans hrp
  have hq3 := hqr.trans hr3
  have hratio (k : ℕ) (hk : k < N) : ratio f p ((k : ℝ) * h) h = 1 :=
    ratio_one hq hqp hk hh hjet
  refine
    { initial_lower := by norm_num [CubicRegularization.sharpParameters]
      update := ?_
      decrease := ?_
      iterate := ?_
      order_pos := hr
      order_le_three := hr3
      degree_ge_order := hrp
      theta_pos := by intro i; norm_num
      theta_le_one := by intro i; norm_num
      epsilon_pos := by intro i hi; exact heps i
      residuals := ?_
      terminal := ?_
      first := ?_ }
  · intro k hk
    norm_num [hratio k hk, CubicRegularization.sharpParameters]
  · intro k hk
    exact model_decrease hq hqp hk hh (hjet k hk.le)
  · intro k hk
    rw [hratio k hk]
    norm_num [CubicRegularization.sharpParameters]
    ring
  · intro k hk
    exact modelResiduals hrp hq hq3 hqp hk hh (hjet k hk.le)
  · apply stationary_terminal hr hrp heps _ (hjet N le_rfl)
    intro hrthird
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
    rw [directionSequence_succ]
    simp only [one_mul, Real.norm_eq_abs, abs_of_pos hh]
    rw [model_smallCurvatureDirections (by omega) hq hq3 hqp (by omega) hh
      (hjet m (by omega))]
    exact ⟨1, by norm_num⟩
  · intro k hk
    apply not_stationary hq hq3 hqr hrp hk (normalizedMagnitude_pos p q hh) heps hthreshold
      (hjet k hk.le)
    intro d hd
    cases k <;> exact hd.1

/-- The endpoint satisfies the full objective quality conditions, with the entire
objective-defined nearly-flat direction set. -/
theorem objectiveQuality_terminal {N p q r : ℕ} {f : ℝ → ℝ} {G h : ℝ}
    {epsilon : Fin 3 → ℝ} (hr : 1 ≤ r) (hrp : r ≤ p)
    (heps : ∀ i, 0 < epsilon i)
    (hjet : ∀ i ≤ p, iteratedDeriv i f ((N : ℝ) * h) = sparseJet N q G h N i) :
    ObjectiveQuality r epsilon f ((N : ℝ) * h) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← norm_deriv_eq_norm_fderiv, ← iteratedDeriv_one, hjet 1 (by omega)]
    simpa [sparseJet] using (heps 0).le
  · intro hr2
    rw [objective_curvature (by omega) hjet]
    simp only [lt_self_iff_false, ite_false, ite_self]
    exact neg_nonpos.mpr (heps 1).le
  · intro hr3 d hd
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, hjet 3 (by omega)]
    simpa [sparseJet] using (heps 2).le

/-- Scalar derivative Lipschitz bounds are the operator-norm bounds on the actual tensors. -/
theorem iteratedFDeriv_lipschitz {f : ℝ → ℝ} {p : ℕ} {L : ℝ≥0}
    (hL : LipschitzWith L (iteratedDeriv p f)) : LipschitzWith L (iteratedFDeriv ℝ p f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  simp only [iteratedFDeriv_eq_equiv_comp, Function.comp_apply, ← map_sub,
    LinearIsometryEquiv.norm_map]
  simpa only [dist_eq_norm] using hL.dist_le_mul x y

/-- Every derivative order uses precisely the successful-step cache cost on this chain. -/
theorem derivativeEvaluations_eq {N p q : ℕ} {f : ℝ → ℝ} {h : ℝ}
    (hq : 1 ≤ q) (hqp : q ≤ p) (hh : 0 < h)
    (hjet : ∀ k ≤ N, ∀ j ≤ p, iteratedDeriv j f ((k : ℝ) * h) =
      sparseJet N q (normalizedMagnitude p q h) h k j) :
    derivativeEvaluations CubicRegularization.sharpParameters p f
      (fun k => (k : ℝ) * h) (fun _ => h) N = N + 1 := by
  classical
  unfold derivativeEvaluations ParameterUpdates.successCount
  rw [Finset.filter_eq_self.mpr]
  · simp
  · intro k hk
    rw [ratio_one hq hqp (Finset.mem_range.mp hk) hh hjet]
    norm_num [CubicRegularization.sharpParameters]

/-- The sharp evaluation exponent for model degree `p` and criticality order `q`. -/
def sharpExponent (p q : ℕ) : ℝ := ((p + 1 : ℕ) : ℝ) / ((p - q + 1 : ℕ) : ℝ)

/-- Tolerances below this positive scale give unit-bounded spacings for the normalized model. -/
def toleranceScale (p q : ℕ) : ℝ := ((q - 1).factorial : ℝ) / p.factorial / 2

/-- Uniform hard families for every separate criticality branch of actual ARp. Constants
precede all tolerances; all trials are accepted, every actual activated model residual holds,
the first algorithm stop is the endpoint, and every earlier point fails the full objective
quality test. The lower bound has the exact real-power exponent and ceiling rounding. -/
theorem exists_hard_family (p r q : ℕ) (hr : 1 ≤ r) (hr3 : r ≤ 3)
    (hq : 1 ≤ q) (hqr : q ≤ r) (hrp : r ≤ p) :
    ∃ L B : ℝ≥0, ∀ epsilon : Fin 3 → ℝ, (∀ i, 0 < epsilon i) →
      epsilon ⟨q - 1, by omega⟩ ≤ toleranceScale p q →
      ∃ (f : ℝ → ℝ) (N : ℕ) (h : ℝ),
        0 < h ∧ h ≤ 1 ∧ ContDiff ℝ p f ∧ LipschitzWith L (iteratedFDeriv ℝ p f) ∧
        (∀ x, |f x| ≤ B) ∧ f 0 = 0 ∧
        IsRun CubicRegularization.sharpParameters r p (fun _ => 1) epsilon f
          (fun k => (k : ℝ) * h) (fun _ => h) (fun _ => 1) N ∧
        (∀ k < N, ¬ObjectiveQuality r epsilon f ((k : ℝ) * h)) ∧
        ObjectiveQuality r epsilon f ((N : ℝ) * h) ∧
        functionEvaluations N = N + 1 ∧
        derivativeEvaluations CubicRegularization.sharpParameters p f
          (fun k => (k : ℝ) * h) (fun _ => h) N = N + 1 ∧
        N = ⌈1 / (epsilon ⟨q - 1, by omega⟩) ^ sharpExponent p q⌉₊ ∧
        1 / (epsilon ⟨q - 1, by omega⟩) ^ sharpExponent p q ≤ (N : ℝ) := by
  let a : ℝ := ((q - 1).factorial : ℝ) / p.factorial
  let t := sharpExponent p q
  let C : ℝ := (2 / a) ^ t
  let κ := 2 * C + 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hC : 0 < C := Real.rpow_pos_of_pos (by positivity) _
  have hκ : 0 ≤ κ := by dsimp [κ]; positivity
  have hκ2 : 2 ≤ κ := by dsimp [κ]; linarith
  have hqp : q ≤ p := hqr.trans hrp
  obtain ⟨L, B, hc⟩ := exists_sparseJet_chain p q hq hqp κ hκ
  refine ⟨L, B, ?_⟩
  intro epsilon heps hsmall
  let e := epsilon ⟨q - 1, by omega⟩
  have he : 0 < e := heps _
  have hesmall : e ≤ a / 2 := hsmall
  let h := (2 * e / a) ^ ((p - q + 1 : ℕ) : ℝ)⁻¹
  have hb : 0 < 2 * e / a := by positivity
  have hb1 : 2 * e / a ≤ 1 := (div_le_one ha).mpr (by linarith)
  have hh : 0 < h := Real.rpow_pos_of_pos hb _
  have hh1 : h ≤ 1 := Real.rpow_le_one hb.le hb1 (by positivity)
  have hr0 : p - q + 1 ≠ 0 := by omega
  have hpower : h ^ (p - q + 1) = 2 * e / a := Real.rpow_inv_natCast_pow hb.le hr0
  have hmag : normalizedMagnitude p q h = 2 * e := by
    unfold normalizedMagnitude
    change a * h ^ (p - q + 1) = _
    rw [hpower]
    field_simp
  have hp1 : h ^ (p + 1) = C * e ^ t := by
    dsimp [h, C, t, sharpExponent]
    rw [← Real.rpow_mul_natCast hb.le]
    have hexp : (((p - q + 1 : ℕ) : ℝ)⁻¹ * ((p + 1 : ℕ) : ℝ)) =
        ((p + 1 : ℕ) : ℝ) / ((p - q + 1 : ℕ) : ℝ) := by ring
    rw [hexp, show 2 * e / a = (2 / a) * e by ring, Real.mul_rpow (by positivity) he.le]
  let N : ℕ := ⌈1 / e ^ t⌉₊
  have hN : 0 < N := Nat.ceil_pos.mpr (by positivity)
  have hupper : (N : ℝ) < 1 / e ^ t + 1 := Nat.ceil_lt_add_one (by positivity)
  have hdrop : (N : ℝ) * normalizedMagnitude p q h * h ^ q ≤ κ := by
    have hn : (N : ℝ) * h ^ (p + 1) ≤ C + 1 := by
      have hm := mul_le_mul_of_nonneg_right hupper.le (pow_nonneg hh.le (p + 1))
      have hcancel : (1 / e ^ t + 1) * h ^ (p + 1) = C + h ^ (p + 1) := by
        rw [hp1]
        field_simp
      rw [hcancel] at hm
      exact hm.trans (by linarith [pow_le_one₀ hh.le hh1 (n := p + 1)])
    have hmagle := normalizedMagnitude_le hq hqp hh.le
    calc
      _ ≤ (N : ℝ) * h ^ (p - q + 1) * h ^ q :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hmagle (by positivity)) (by positivity)
      _ = (N : ℝ) * h ^ (p + 1) := by
        rw [mul_assoc, ← pow_add, show p - q + 1 + q = p + 1 by omega]
      _ ≤ C + 1 := hn
      _ ≤ κ := by dsimp [κ]; linarith
  obtain ⟨f, hf, hLip, hjet, hbnd⟩ := hc N hN (normalizedMagnitude p q h) h
    (normalizedMagnitude_pos p q hh).le hh
    ((normalizedMagnitude_le hq hqp hh.le).trans (by
      nlinarith [pow_nonneg hh.le (p - q + 1)])) hdrop
    ((normalizedMagnitude_le hq hqp hh.le).trans
      ((pow_le_one₀ hh.le hh1).trans (by linarith))) (by linarith)
  refine ⟨f, N, h, hh, hh1, hf, iteratedFDeriv_lipschitz hLip, ?_, ?_, ?_, ?_, ?_, rfl,
    derivativeEvaluations_eq hq hqp hh hjet, rfl, Nat.le_ceil _⟩
  · intro x
    simpa using hbnd 0 (by omega) x
  · simpa [sparseJet] using hjet 0 (by omega) 0 (by omega)
  · apply isRun_of_sparseJet hN hr hr3 hqr hq hrp hh heps _ hjet
    change e < normalizedMagnitude p q h
    rw [hmag]
    linarith
  · intro k hk
    apply not_objectiveQuality hq (hqr.trans hr3) hqr hrp hk
      (normalizedMagnitude_pos p q hh) heps _ (hjet k hk.le)
    change e < normalizedMagnitude p q h
    rw [hmag]
    linarith
  · exact objectiveQuality_terminal hr hrp heps (hjet N le_rfl)

/-- The maximum sharp lower bound over activated first-, second-, and third-order tests. -/
def evaluationLowerBound (p r : ℕ) (epsilon : Fin 3 → ℝ) : ℝ :=
  max (1 / (epsilon 0) ^ sharpExponent p 1)
    (max (if 2 ≤ r then 1 / (epsilon 1) ^ sharpExponent p 2 else 0)
      (if 3 ≤ r then 1 / (epsilon 2) ^ sharpExponent p 3 else 0))

/-- The first-order maximum is its single gradient power. -/
theorem evaluationLowerBound_one (p : ℕ) (epsilon : Fin 3 → ℝ)
    (heps : ∀ i, 0 < epsilon i) :
    evaluationLowerBound p 1 epsilon = 1 / (epsilon 0) ^ sharpExponent p 1 := by
  simp only [evaluationLowerBound, show ¬2 ≤ 1 by omega, show ¬3 ≤ 1 by omega,
    ite_false, max_self]
  exact max_eq_left (div_nonneg zero_le_one (Real.rpow_nonneg (heps 0).le _))

/-- The second-order maximum is exactly the gradient and curvature maximum. -/
theorem evaluationLowerBound_two (p : ℕ) (epsilon : Fin 3 → ℝ)
    (heps : ∀ i, 0 < epsilon i) :
    evaluationLowerBound p 2 epsilon =
      max (1 / (epsilon 0) ^ sharpExponent p 1) (1 / (epsilon 1) ^ sharpExponent p 2) := by
  simp only [evaluationLowerBound, show 2 ≤ 2 by omega, show ¬3 ≤ 2 by omega,
    ite_true, ite_false]
  rw [max_eq_left (div_nonneg zero_le_one (Real.rpow_nonneg (heps 1).le _))]

/-- The third-order maximum includes all three printed criticality powers. -/
theorem evaluationLowerBound_three (p : ℕ) (epsilon : Fin 3 → ℝ) :
    evaluationLowerBound p 3 epsilon = max (1 / (epsilon 0) ^ sharpExponent p 1)
      (max (1 / (epsilon 1) ^ sharpExponent p 2) (1 / (epsilon 2) ^ sharpExponent p 3)) := by
  simp only [evaluationLowerBound, show 2 ≤ 3 by omega, show 3 ≤ 3 by omega, ite_true]

/-- Every model degree and criticality order has a nontrivial admissible tolerance range. -/
theorem toleranceScale_pos (p q : ℕ) : 0 < toleranceScale p q := by
  unfold toleranceScale
  positivity

/-- A single family attains the maximum of all activated lower bounds. Choosing the hardest
branch after the tolerances does not change the uniform objective or Lipschitz constants. -/
theorem exists_max_hard_family (p r : ℕ) (hr : 1 ≤ r) (hr3 : r ≤ 3) (hrp : r ≤ p) :
    ∃ L B : ℝ≥0, ∀ epsilon : Fin 3 → ℝ, (∀ i, 0 < epsilon i) →
      (∀ i : Fin r, epsilon ⟨i.val, by omega⟩ ≤ toleranceScale p (i.val + 1)) →
      ∃ (f : ℝ → ℝ) (N : ℕ) (h : ℝ),
        0 < h ∧ h ≤ 1 ∧ ContDiff ℝ p f ∧ LipschitzWith L (iteratedFDeriv ℝ p f) ∧
        (∀ x, |f x| ≤ B) ∧ f 0 = 0 ∧
        IsRun CubicRegularization.sharpParameters r p (fun _ => 1) epsilon f
          (fun k => (k : ℝ) * h) (fun _ => h) (fun _ => 1) N ∧
        (∀ k < N, ¬ObjectiveQuality r epsilon f ((k : ℝ) * h)) ∧
        ObjectiveQuality r epsilon f ((N : ℝ) * h) ∧
        functionEvaluations N = N + 1 ∧
        derivativeEvaluations CubicRegularization.sharpParameters p f
          (fun k => (k : ℝ) * h) (fun _ => h) N = N + 1 ∧
        evaluationLowerBound p r epsilon ≤ (N : ℝ) := by
  classical
  let _ : NeZero r := ⟨by omega⟩
  choose Ls Bs hfamily using fun i : Fin r =>
    exists_hard_family p r (i.val + 1) hr hr3 (by omega) (by omega) hrp
  let L := Finset.univ.sup Ls
  let B := Finset.univ.sup Bs
  refine ⟨L, B, ?_⟩
  intro epsilon heps hsmall
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin r => 1 / (epsilon ⟨i.val, by omega⟩) ^ sharpExponent p (i.val + 1))
    Finset.univ_nonempty
  obtain ⟨f, N, h, hh, hh1, hf, hLip, hb, hf0, hrun, hnot, hterminal, hfe, hde, hN, hNL⟩ :=
    hfamily i epsilon heps (by simpa using hsmall i)
  refine ⟨f, N, h, hh, hh1, hf, ?_, ?_, hf0, hrun, hnot, hterminal, hfe, hde, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    exact (hLip.dist_le_mul x y).trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast (Finset.le_sup (f := Ls) (Finset.mem_univ i))) dist_nonneg)
  · intro x
    exact (hb x).trans (by exact_mod_cast (Finset.le_sup (f := Bs) (Finset.mem_univ i)))
  · have hbound (j : Fin r) :
        1 / (epsilon ⟨j.val, by omega⟩) ^ sharpExponent p (j.val + 1) ≤ (N : ℝ) :=
      (hmax j (Finset.mem_univ j)).trans (by simpa using hNL)
    apply max_le (hbound ⟨0, by omega⟩)
    apply max_le
    · split_ifs with hr2
      · exact hbound ⟨1, by omega⟩
      · positivity
    · split_ifs with hrthird
      · exact hbound ⟨2, by omega⟩
      · positivity

end Optimization.HigherOrderSharpness

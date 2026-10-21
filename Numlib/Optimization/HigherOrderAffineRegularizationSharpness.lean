import Numlib.Optimization.HigherOrderApproximateRegularizationSharpness

/-!
# Sharp affine regularization models

At a sufficiently small fixed regularization parameter, the actual high-order model Taylor
gaps meet all requested criteria on the accuracy radius. The estimate uses the vanishing
model gradient and the exact higher derivatives of the norm regularizer.
-/
noncomputable section
open scoped Nat NNReal
namespace Optimization.HigherOrderAffineRegularizationSharpness
open HigherOrderApproximateRegularization HigherOrderSharpness TaylorCriticality
open HigherOrderApproximateRegularizationSharpness Metric Set

/-- Falling-factorial coefficients normalized by the full factorial are at most one. -/
theorem descFactorial_div_le_one {n j : ℕ} (hj : j ≤ n) :
    (n.descFactorial j : ℝ) / n.factorial ≤ 1 := by
  have he : ((n - j).factorial : ℝ) * n.descFactorial j = n.factorial := by
    exact_mod_cast Nat.factorial_mul_descFactorial hj
  have hfac : (1 : ℝ) ≤ (n - j).factorial := by exact_mod_cast Nat.factorial_pos (n - j)
  apply (div_le_one (by positivity)).mpr
  nlinarith [(show (0 : ℝ) ≤ n.descFactorial j by positivity)]

/-- All high-order regularizer terms, after the first-order cancellation, have a common
quadratic bound on a radius smaller than the selected positive step. -/
theorem model_term_affine {N p k j : ℕ} {f : ℝ → ℝ} {G h σ ε d : ℝ}
    (hp : 1 ≤ p) (hk : k < N) (hj : 2 ≤ j) (hjp : j ≤ p)
    (hh : 0 < h) (hσ : 0 ≤ σ) (hε : 0 ≤ ε) (hεh : ε ≤ h) (hd : |d| ≤ ε)
    (hjet : ∀ i ≤ p, iteratedDeriv i f ((k : ℝ) * h) = sparseJet N 1 G h k i) :
    -((j.factorial : ℝ)⁻¹ *
      iteratedFDeriv ℝ j (model f p ((k : ℝ) * h) σ) h (fun _ => d)) ≤
        σ * h ^ (p - 1) * ε ^ 2 := by
  have hder := iteratedDeriv_model_of_sparseJet (by norm_num : 1 ≤ 1) hp hk
    (j := j) (σ := σ) (by omega) hh hjet
  simp only [Nat.descFactorial_of_lt (by omega : 1 < j), Nat.cast_zero, mul_zero,
    zero_mul, zero_add] at hder
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, hder]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [mul_comm (d ^ j)]
  have hcoef : σ / ((p + 1).factorial : ℝ) * ((p + 1).descFactorial j : ℝ) ≤ σ := by
    have hh' := mul_le_mul_of_nonneg_left
      (descFactorial_div_le_one (show j ≤ p + 1 by omega)) hσ
    convert hh' using 1 <;> ring
  have hfac : (j.factorial : ℝ)⁻¹ ≤ 1 := by
    apply (inv_le_one₀ (by positivity)).mpr
    exact_mod_cast Nat.factorial_pos j
  have hpow : h ^ (p + 1 - j) * ε ^ j ≤ h ^ (p - 1) * ε ^ 2 := by
    have he : j = (j - 2) + 2 := by omega
    calc
      _ = h ^ (p + 1 - j) * (ε ^ (j - 2) * ε ^ 2) := by rw [← pow_add, ← he]
      _ ≤ h ^ (p + 1 - j) * (h ^ (j - 2) * ε ^ 2) := by gcongr
      _ = _ := by rw [← mul_assoc, ← pow_add, show p + 1 - j + (j - 2) = p - 1 by omega]
  calc
    _ ≤ |(j.factorial : ℝ)⁻¹ *
        (σ / ((p + 1).factorial : ℝ) * ((p + 1).descFactorial j : ℝ) *
          h ^ (p + 1 - j) * d ^ j)| := neg_le_abs _
    _ = (j.factorial : ℝ)⁻¹ *
        (σ / ((p + 1).factorial : ℝ) * ((p + 1).descFactorial j : ℝ)) *
          (h ^ (p + 1 - j) * |d| ^ j) := by
      rw [abs_mul, abs_of_nonneg (by positivity), abs_mul,
        abs_of_nonneg (by positivity), abs_pow]
      ring
    _ ≤ 1 * σ * (h ^ (p + 1 - j) * ε ^ j) := by gcongr
    _ ≤ σ * (h ^ (p - 1) * ε ^ 2) := by simpa using mul_le_mul_of_nonneg_left hpow hσ
    _ = _ := by ring

/-- The affine model gradient vanishes at the positive regularized minimizer. -/
theorem model_deriv_affine_zero {N p k : ℕ} {f : ℝ → ℝ} {G h σ : ℝ}
    (hp : 1 ≤ p) (hk : k < N) (hh : 0 < h)
    (hscale : σ * h ^ p = (p.factorial : ℝ) * G)
    (hjet : ∀ i ≤ p, iteratedDeriv i f ((k : ℝ) * h) = sparseJet N 1 G h k i) :
    deriv (model f p ((k : ℝ) * h) σ) h = 0 := by
  have he := iteratedDeriv_model_of_sparseJet (by norm_num : 1 ≤ 1) hp hk
    (j := 1) (σ := σ) (by norm_num) hh hjet
  rw [iteratedDeriv_one] at he
  rw [he]
  norm_num only [Nat.factorial_one, Nat.cast_one, div_one, Nat.descFactorial_one,
    Nat.sub_self, pow_zero, mul_one, Nat.add_sub_cancel]
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  nlinarith [hscale]

/-- Uniform quadratic upper bounds for every actual model Taylor decrement. -/
theorem model_decrement_affine_le {N p k j : ℕ} {f : ℝ → ℝ} {G h σ ε d : ℝ}
    (hp : 1 ≤ p) (hk : k < N) (hjp : j ≤ p)
    (hh : 0 < h) (hσ : 0 ≤ σ) (hε : 0 ≤ ε) (hεh : ε ≤ h) (hd : |d| ≤ ε)
    (hscale : σ * h ^ p = (p.factorial : ℝ) * G)
    (hjet : ∀ i ≤ p, iteratedDeriv i f ((k : ℝ) * h) = sparseJet N 1 G h k i) :
    taylorDecrement (model f p ((k : ℝ) * h) σ) j h d ≤
      (j : ℝ) * (σ * h ^ (p - 1) * ε ^ 2) := by
  induction j with
  | zero => simp
  | succ j ih =>
    by_cases hj : j = 0
    · subst j
      rw [taylorDecrement_one]
      have he := model_deriv_affine_zero hp hk hh hscale hjet
      have hg : fderiv ℝ (model f p ((k : ℝ) * h) σ) h = 0 := by
        rw [← norm_eq_zero, ← norm_deriv_eq_norm_fderiv, he, norm_zero]
      rw [hg]
      simp only [zero_apply, neg_zero]
      positivity
    · rw [taylorDecrement_succ]
      have ht := model_term_affine hp hk (show 2 ≤ j + 1 by omega) hjp
        hh hσ hε hεh hd hjet
      have hi := ih (by omega)
      push_cast
      linarith

/-- All actual model criteria hold on the accuracy radius when the fixed regularization
parameter makes the selected affine-model step sufficiently large relative to that radius. -/
theorem model_quality_affine {N p q k : ℕ} {f : ℝ → ℝ} {G h σ ε : ℝ}
    (hq : 1 ≤ q) (hqp : q ≤ p) (hk : k < N) (hh : 0 < h) (hσ : 0 < σ)
    (hε : 0 < ε) (hε1 : ε < 1) (hG : G ≤ 2 * ε ^ q / (q.factorial : ℝ))
    (hscale : σ * h ^ p = (p.factorial : ℝ) * G)
    (hlarge : 4 * (p : ℝ) * p.factorial * ε ≤ h)
    (hjet : ∀ i ≤ p, iteratedDeriv i f ((k : ℝ) * h) = sparseJet N 1 G h k i) :
    ModelQuality (parameters p q hq hqp ε σ hε hε1 hσ) f ((k : ℝ) * h) h σ ε := by
  have hp : 1 ≤ p := hq.trans hqp
  have hpp : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpf : (1 : ℝ) ≤ p.factorial := by exact_mod_cast Nat.factorial_pos p
  have hεh : ε ≤ h :=
    (le_mul_of_one_le_left hε.le (show 1 ≤ 4 * (p : ℝ) * p.factorial by nlinarith)).trans hlarge
  let A := σ * h ^ (p - 1) * ε ^ 2
  let T := ε ^ (q + 1) / (2 * (q.factorial : ℝ))
  have hpa : (p : ℝ) * A ≤ T := by
    apply (mul_le_mul_iff_right₀ hh).mp
    calc
      h * ((p : ℝ) * A) = (p : ℝ) * p.factorial * G * ε ^ 2 := by
        dsimp [A]
        have he : h ^ (p - 1) * h = h ^ p := by
          rw [← pow_succ, Nat.sub_add_cancel hp]
        calc
          _ = (p : ℝ) * (σ * (h ^ (p - 1) * h)) * ε ^ 2 := by ring
          _ = _ := by rw [he, hscale]; ring
      _ ≤ (p : ℝ) * p.factorial * (2 * ε ^ q / (q.factorial : ℝ)) * ε ^ 2 := by
        gcongr
      _ = (4 * (p : ℝ) * p.factorial * ε) * T := by dsimp [T]; rw [pow_succ]; ring
      _ ≤ h * T := mul_le_mul_of_nonneg_right hlarge (by dsimp [T]; positivity)
  intro j hj hjq
  change j ≤ q at hjq
  change gapOn (taylorDecrement (model f p ((k : ℝ) * h) σ) j h) (closedBall 0 ε) ≤
    (1 / 2 : ℝ) * ε * ε ^ j / (j.factorial : ℝ)
  have ht : T ≤ (1 / 2 : ℝ) * ε * ε ^ j / (j.factorial : ℝ) := by
    have hpow : ε ^ (q + 1) ≤ ε ^ (j + 1) :=
      pow_le_pow_of_le_one hε.le hε1.le (by omega)
    have hfac : (j.factorial : ℝ) ≤ q.factorial := by exact_mod_cast Nat.factorial_le hjq
    calc
      T ≤ ε ^ (j + 1) / (2 * (q.factorial : ℝ)) := by
        dsimp [T]
        exact div_le_div_of_nonneg_right hpow (by positivity)
      _ ≤ ε ^ (j + 1) / (2 * (j.factorial : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr)
      _ = _ := by rw [pow_succ]; ring
  apply (gapOn_le (show (closedBall (0 : ℝ) ε).Nonempty by
    exact ⟨0, by simpa using hε.le⟩) ?_).trans ht
  intro d hd
  have hd' : |d| ≤ ε := by simpa [Real.dist_eq] using hd
  have hh' := model_decrement_affine_le hp hk (hjq.trans hqp)
    hh hσ.le hε.le hεh hd' hscale hjet
  have hja : (j : ℝ) * A ≤ (p : ℝ) * A :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hjq.trans hqp) (by dsimp [A]; positivity)
  exact hh'.trans (hja.trans hpa)

/-- Affine preterminal jets retain a nonzero terminal gradient on the other side of the
requested threshold. Only the small gradient difference must obey the high smoothness scale. -/
def affineJet (N : ℕ) (G H h : ℝ) (k j : ℕ) : ℝ :=
  if j = 0 then -(k : ℝ) * G * h else
  if j = 1 then if k < N then -G else -H else 0

/-- Before the endpoint the affine jets are the already established sparse first-order jets. -/
theorem affineJet_eq_sparse {N k : ℕ} {G H h : ℝ} (hk : k < N) :
    affineJet N G H h k = sparseJet N 1 G h k := by
  funext j
  simp [affineJet, sparseJet, hk]

/-- Uniform high-order Hermite compatibility for an affine chain requires only the terminal
gradient jump to have the order-r spacing scale. -/
theorem affineJet_compatible {N r : ℕ} {G H h κ : ℝ}
    (hr : 1 ≤ r) (hh : 0 ≤ h) (hκ : 0 ≤ κ) (hjump : |G - H| ≤ κ * h ^ r) :
    ∀ k < N, ∀ j ≤ r,
      |affineJet N G H h (k + 1) j -
        (Polynomial.derivative^[j] (Hermite.endpointTaylor r (affineJet N G H h k))).eval h| ≤
        κ * h ^ (r + 1 - j) := by
  intro k hk j _
  rw [affineJet_eq_sparse hk, endpointTaylor_sparseJet (by norm_num : 1 ≤ 1) hr hk]
  by_cases hj0 : j = 0
  · subst j
    simp only [Function.iterate_zero_apply, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X, affineJet,
      ↓reduceIte, Nat.cast_add, Nat.cast_one, Nat.factorial_one, Nat.cast_one,
      div_one, pow_one]
    have he : -((k : ℝ) + 1) * G * h - (-(k : ℝ) * G * h + -G * h) = 0 := by ring
    rw [he, abs_zero]
    positivity
  rw [eval_iterate_derivative_sparse (by omega : 0 < j)]
  by_cases hj1 : j = 1
  · subst j
    simp only [affineJet, Nat.one_ne_zero, ite_false, ite_true,
      Nat.factorial_one, Nat.cast_one, div_one, Nat.descFactorial_self, Nat.sub_self,
      pow_zero, mul_one, Nat.add_sub_cancel]
    split_ifs
    · simp only [sub_self, abs_zero]; positivity
    · convert hjump using 1; congr 1; ring
  · simp only [affineJet, ite_eq_right hj0, ite_eq_right hj1,
      Nat.factorial_one, Nat.cast_one, div_one,
      Nat.descFactorial_of_lt (by omega : 1 < j), Nat.cast_zero, mul_zero, zero_mul,
      sub_self, abs_zero]
    positivity

/-- Uniform high-order smooth bounded extensions of affine jets. The constants are selected
before the length, spacing, gradient threshold, and small endpoint perturbation. -/
theorem exists_affineJet_chain (r : ℕ) (hr : 1 ≤ r) (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ L B : ℝ≥0, ∀ N : ℕ, 0 < N → ∀ G H h : ℝ, 0 ≤ G → 0 < h →
      |G - H| ≤ κ * h ^ r → (N : ℝ) * G * h ≤ κ → G ≤ κ → h ≤ κ →
      ∃ f : ℝ → ℝ, ContDiff ℝ r f ∧ LipschitzWith L (iteratedDeriv r f) ∧
        (∀ k ≤ N, ∀ j ≤ r, iteratedDeriv j f ((k : ℝ) * h) = affineJet N G H h k j) ∧
        (∀ j ≤ r, ∀ x, |iteratedDeriv j f x| ≤ B) := by
  obtain ⟨L, B, hc⟩ := Hermite.exists_contDiff_lipschitz_iteratedDeriv_of_finite_jets r κ hκ
  refine ⟨L, B, ?_⟩
  intro N hN G H h hG hh hjump hdrop hGκ hhκ
  have he (k : ℕ) : ((k + 1 : ℕ) : ℝ) * h - (k : ℝ) * h = h := by push_cast; ring
  obtain ⟨f, hf, hLip, hjet, hb⟩ := hc N hN (fun k => (k : ℝ) * h) (affineJet N G H h)
    (fun k _ => by push_cast; nlinarith)
    (fun k hk j hj => by rw [he]; exact affineJet_compatible hr hh.le hκ hjump k hk j hj)
  refine ⟨f, hf, hLip, hjet, hb ?_ (fun k _ => by simpa only [he] using hhκ)⟩
  intro k hk j _
  rw [affineJet_eq_sparse hk]
  have hd : (N : ℝ) * G * h ^ 1 ≤ κ := by simpa using hdrop
  exact abs_sparseJet_le hG hh.le hκ hd hGκ k hk j

/-- The shared accepted-trial execution constructor, exposed for affine model constructions. -/
theorem execution_of_accepted {N : ℕ} {P : Parameters} {f : ℝ → ℝ} {h σ δ : ℝ}
    (hσ : P.sigmaMin ≤ σ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hfrac : P.fraction = 1)
    (hfailed : ∀ k < N, Nonempty (FailedTest P f ((k : ℝ) * h) (fun _ => δ)))
    (hpassed : PassedTest P f ((N : ℝ) * h) (fun _ => δ))
    (hmodel : ∀ k < N, model f P.p ((k : ℝ) * h) σ h <
      model f P.p ((k : ℝ) * h) σ 0)
    (hquality : ∀ k < N, ModelQuality P f ((k : ℝ) * h) h σ δ)
    (hratio : ∀ k < N, (f ((k : ℝ) * h) - f ((k : ℝ) * h + h)) /
      taylorDecrement f P.p ((k : ℝ) * h) h = 1) :
    ∃ run : OuterExecution P f 0 σ (fun _ => δ) N,
      run.state = state σ δ h ∧ run.last = .stopTest (run.state N) ∧
      (∀ k < N, ¬Nonempty (PassedTest P f (run.state k).point (run.state k).radii)) ∧
      run.functionCount = N + 1 ∧ run.derivativeCount = N * P.p + P.q :=
  HigherOrderApproximateRegularizationSharpness.execution_of_accepted
    hσ hδ hδ1 hfrac hfailed hpassed hmodel hquality hratio

/-- Every positive truncation order of the affine objective has the same linear decrement. -/
theorem decrement_affineJet {N r k j : ℕ} {f : ℝ → ℝ} {G H h : ℝ}
    (hj : j ≤ r)
    (hjet : ∀ i ≤ r, iteratedDeriv i f ((k : ℝ) * h) = affineJet N G H h k i) (d : ℝ) :
    taylorDecrement f j ((k : ℝ) * h) d =
      if j = 0 then 0 else (if k < N then G else H) * d := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [taylorDecrement_succ, ih (by omega),
      iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, hjet (j + 1) hj]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    by_cases he : j = 0
    · subst j
      simp only [affineJet, Nat.zero_add, Nat.one_ne_zero, ite_false, ite_true,
        Nat.factorial_one, Nat.cast_one, inv_one, one_mul, pow_one]
      split_ifs <;> ring
    · simp [affineJet, he]

/-- Exact maximizers for all affine objective Taylor gaps occur at the positive radius. -/
theorem gap_affineJet {N r k j : ℕ} {f : ℝ → ℝ} {G H h δ : ℝ}
    (hG : 0 ≤ G) (hH : 0 ≤ H) (hδ : 0 ≤ δ) (hj : j ≤ r)
    (hjet : ∀ i ≤ r, iteratedDeriv i f ((k : ℝ) * h) = affineJet N G H h k i) :
    gapOn (taylorDecrement f j ((k : ℝ) * h)) (closedBall 0 δ) =
      taylorDecrement f j ((k : ℝ) * h) δ := by
  apply le_antisymm
  · apply gapOn_le ⟨0, by simpa using hδ⟩
    intro d hd
    rw [decrement_affineJet hj hjet, decrement_affineJet hj hjet]
    split_ifs <;> first | exact le_rfl | skip
    all_goals
      apply mul_le_mul_of_nonneg_left _ (by assumption)
      exact (le_abs_self _).trans (by simpa [Real.dist_eq] using hd)
  · exact le_gapOn (isCompact_closedBall 0 δ)
      (continuous_taylorDecrement f j ((k : ℝ) * h)).continuousOn
      (by simp [abs_of_nonneg hδ])

/-- The affine regularization step strictly reduces the model under the exact stationarity
scaling. This calculation concerns the actual model, not a supplied decrease certificate. -/
theorem model_affine_strict {N p k : ℕ} {f : ℝ → ℝ} {G h σ : ℝ}
    (hp : 1 ≤ p) (hk : k < N) (hh : 0 < h) (hG : 0 < G)
    (hscale : σ * h ^ p = (p.factorial : ℝ) * G)
    (hjet : ∀ i ≤ p, iteratedDeriv i f ((k : ℝ) * h) = sparseJet N 1 G h k i) :
    model f p ((k : ℝ) * h) σ h < model f p ((k : ℝ) * h) σ 0 := by
  change HigherOrderRegularization.model f p ((k : ℝ) * h) σ h < _
  rw [model_of_sparseJet (by norm_num : 1 ≤ 1) hp hk hjet,
    model_zero, abs_of_pos hh]
  have hv : f ((k : ℝ) * h) = -(k : ℝ) * G * h := by
    simpa [sparseJet] using hjet 0 (by omega)
  rw [hv]
  simp only [Nat.factorial_one, Nat.cast_one, div_one, pow_one]
  have hr : σ / ((p + 1).factorial : ℝ) * h ^ (p + 1) = G * h / (p + 1 : ℝ) := by
    rw [Nat.factorial_succ, pow_succ]
    push_cast
    apply (eq_div_iff (by positivity : (p + 1 : ℝ) ≠ 0)).mpr
    field_simp
    nlinarith [hscale]
  rw [hr]
  have hp' : (1 : ℝ) < p + 1 := by exact_mod_cast (show 1 < p + 1 by omega)
  have hg' : G * h / (p + 1 : ℝ) < G * h :=
    (div_lt_self (by positivity) hp')
  linarith

/-- Affine jets on both sides of the endpoint threshold produce a complete legal run with
small model radii, and the actual strict stopping test first passes at the endpoint. -/
theorem run_of_affineJet {N p q r : ℕ} {f : ℝ → ℝ} {G H h σ ε : ℝ}
    (hq : 1 ≤ q) (hqp : q ≤ p) (hpr : p ≤ r) (hh : 0 < h) (hσ : 0 < σ)
    (hε : 0 < ε) (hε1 : ε < 1) (hG : 0 < G) (hH : 0 ≤ H)
    (hGupper : G ≤ 2 * ε ^ q / (q.factorial : ℝ))
    (hscale : σ * h ^ p = (p.factorial : ℝ) * G)
    (hlarge : 4 * (p : ℝ) * p.factorial * ε ≤ h)
    (hearlier : ∀ j, 1 ≤ j → j < q → G * ε < ε * ε ^ j / (j.factorial : ℝ))
    (hfail : ε * ε ^ q / (q.factorial : ℝ) ≤ G * ε)
    (hend : ∀ j, 1 ≤ j → j ≤ q → H * ε < ε * ε ^ j / (j.factorial : ℝ))
    (hjet : ∀ k ≤ N, ∀ j ≤ r, iteratedDeriv j f ((k : ℝ) * h) = affineJet N G H h k j) :
    let P := parameters p q hq hqp ε σ hε hε1 hσ
    ∃ run : OuterExecution P f 0 σ (fun _ => ε) N,
      run.state = state σ ε h ∧ run.last = .stopTest (run.state N) ∧
      (∀ k < N, ¬Nonempty (PassedTest P f (run.state k).point (run.state k).radii)) ∧
      run.functionCount = N + 1 ∧ run.derivativeCount = N * p + q := by
  let P := parameters p q hq hqp ε σ hε hε1 hσ
  have hp : 1 ≤ p := hq.trans hqp
  have hpre (k : ℕ) (hk : k < N) (j : ℕ) (hj : j ≤ p) :
      iteratedDeriv j f ((k : ℝ) * h) = sparseJet N 1 G h k j := by
    rw [hjet k hk.le j (hj.trans hpr), affineJet_eq_sparse hk]
  have hw (k : ℕ) (hk : k ≤ N) (j : ℕ) (hj : j ≤ q) :
      GapWitness f j ((k : ℝ) * h) ε P.fraction ε := by
    refine ⟨by simp [Real.norm_eq_abs, abs_of_pos hε], ?_⟩
    change 1 * gapOn _ _ ≤ _
    rw [one_mul, gap_affineJet hG.le hH hε.le ((hj.trans hqp).trans hpr) (hjet k hk)]
  have hf : ∀ k < N, Nonempty (FailedTest P f ((k : ℝ) * h) (fun _ => ε)) := by
    intro k hk
    refine ⟨⟨q, hq, le_rfl, fun _ => ε,
      fun j _ hj => hw k hk.le j hj, ?_, ?_⟩⟩
    · intro j hj hjq
      change taylorDecrement f j ((k : ℝ) * h) ε < 1 * ε * ε ^ j / (j.factorial : ℝ)
      rw [decrement_affineJet ((hjq.le.trans hqp).trans hpr) (hjet k hk.le),
        ite_eq_right (by omega : j ≠ 0), ite_eq_left hk, one_mul]
      exact hearlier j hj hjq
    · change 1 * ε * ε ^ q / (q.factorial : ℝ) ≤ taylorDecrement f q ((k : ℝ) * h) ε
      rw [decrement_affineJet (hqp.trans hpr) (hjet k hk.le),
        ite_eq_right (by omega : q ≠ 0), ite_eq_left hk, one_mul]
      exact hfail
  have ht : PassedTest P f ((N : ℝ) * h) (fun _ => ε) := by
    refine ⟨fun _ => ε, fun j _ hj => hw N le_rfl j hj, ?_⟩
    intro j hj hjq
    change taylorDecrement f j ((N : ℝ) * h) ε < 1 * ε * ε ^ j / (j.factorial : ℝ)
    rw [decrement_affineJet ((hjq.trans hqp).trans hpr) (hjet N le_rfl),
      ite_eq_right (by omega : j ≠ 0), ite_eq_right (by omega : ¬N < N), one_mul]
    exact hend j hj hjq
  apply execution_of_accepted le_rfl hε hε1.le rfl hf ht
    (fun k hk => model_affine_strict hp hk hh hG hscale (hpre k hk))
    (fun k hk => model_quality_affine hq hqp hk hh hσ hε hε1
      hGupper hscale hlarge (hpre k hk))
  intro k hk
  have hv (i : ℕ) (hi : i ≤ N) : f ((i : ℝ) * h) = -(i : ℝ) * G * h := by
    simpa [affineJet] using hjet i hi 0 (by omega)
  have hx : (k : ℝ) * h + h = ((k + 1 : ℕ) : ℝ) * h := by push_cast; ring
  change (f ((k : ℝ) * h) - f ((k : ℝ) * h + h)) /
    taylorDecrement f p ((k : ℝ) * h) h = 1
  rw [decrement_sparse (by norm_num : 1 ≤ 1) (hpre k hk) le_rfl,
    ite_eq_left ⟨hp, hk⟩, hx, hv k hk.le, hv (k + 1) hk]
  simp only [Nat.factorial_one, Nat.cast_one, div_one, pow_one]
  push_cast
  apply (div_eq_one_iff_eq (by positivity : G * h ≠ 0)).mpr
  ring

/-- A common affine gap below the highest-order threshold also passes all lower orders. -/
theorem affine_threshold_mono {q j : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hjq : j ≤ q) : ε ^ q / (q.factorial : ℝ) ≤ ε ^ j / (j.factorial : ℝ) := by
  calc
    ε ^ q / (q.factorial : ℝ) ≤ ε ^ j / (q.factorial : ℝ) :=
      div_le_div_of_nonneg_right (pow_le_pow_of_le_one hε.le hε1 hjq) (by positivity)
    _ ≤ ε ^ j / (j.factorial : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (by exact_mod_cast Nat.factorial_le hjq)

/-- With at most twice the highest-order threshold gradient, every strictly lower requested
order passes its test at the common small radius. -/
theorem affine_threshold_earlier {q j : ℕ} {G ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hj : 1 ≤ j) (hjq : j < q) (hG : G ≤ 2 * ε ^ q / (q.factorial : ℝ)) :
    G * ε < ε * ε ^ j / (j.factorial : ℝ) := by
  have hfac : 2 * (j.factorial : ℝ) ≤ q.factorial := by
    have hf := Nat.factorial_le (show j + 1 ≤ q by omega)
    rw [Nat.factorial_succ] at hf
    have he : 2 * j.factorial ≤ (j + 1) * j.factorial := Nat.mul_le_mul_right _ (by omega)
    exact_mod_cast he.trans hf
  have hpow : ε ^ q ≤ ε ^ (j + 1) := pow_le_pow_of_le_one hε.le hε1.le (by omega)
  have hu : G ≤ ε ^ (j + 1) / (j.factorial : ℝ) := by
    calc
      G ≤ 2 * ε ^ q / (q.factorial : ℝ) := hG
      _ ≤ 2 * ε ^ (j + 1) / (q.factorial : ℝ) := by gcongr
      _ ≤ 2 * ε ^ (j + 1) / (2 * (j.factorial : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hfac
      _ = _ := by ring
  have hh : ε ^ (j + 1) / (j.factorial : ℝ) < ε ^ j / (j.factorial : ℝ) := by
    apply (div_lt_div_iff_of_pos_right (by positivity)).mpr
    rw [pow_succ]
    exact mul_lt_of_lt_one_right (by positivity) hε1
  have hm := mul_lt_mul_of_pos_right (hu.trans_lt hh) hε
  convert hm using 1; ring

/-- A fixed step scaling large enough for all model-radius criteria. -/
def stepScale (p : ℕ) : ℝ := 4 * (p : ℝ) * p.factorial

/-- Fixed small regularization permits accuracy radii at every requested optimality order. -/
def affineSigma (p q : ℕ) : ℝ :=
  (p.factorial : ℝ) / ((q.factorial : ℝ) * stepScale p ^ p)

/-- The affine regularization parameter is positive at every positive model degree. -/
theorem affineSigma_pos {p : ℕ} (hp : 1 ≤ p) (q : ℕ) : 0 < affineSigma p q := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  unfold affineSigma stepScale
  positivity

/-- The affine-model sharp evaluation exponent. -/
def affineExponent (p q : ℕ) : ℝ := (q : ℝ) * ((p : ℝ) + 1) / p

/-- Arbitrarily high available smoothness does not improve the small-radius evaluation
exponent. Uniform bounded smooth objectives support actual legal executions with the exact
ceiling number of accepted trials, and the strict stopping test first passes at the endpoint. -/
theorem exists_hard_family (p q r : ℕ) (hq : 1 ≤ q) (hqp : q ≤ p) (hpr : p ≤ r) :
    ∃ L B : ℝ≥0, ∀ ε : ℝ, (hε : 0 < ε) → (hεsmall : ε ≤ 1 / 2) →
      let P := parameters p q hq hqp ε (affineSigma p q) hε (by linarith)
        (affineSigma_pos (hq.trans hqp) q)
      ∃ (f : ℝ → ℝ) (N : ℕ) (h : ℝ)
        (run : OuterExecution P f 0 (affineSigma p q) (fun _ => ε) N),
        ContDiff ℝ r f ∧ (∀ j ≤ r, LipschitzWith L (iteratedFDeriv ℝ j f)) ∧
        (∀ x, |f x| ≤ B) ∧ f 0 = 0 ∧ 0 < h ∧
        N = ⌈1 / ε ^ affineExponent p q⌉₊ ∧
        (∀ k < N, ε * ε ^ q / (q.factorial : ℝ) <
          gapOn (taylorDecrement f q ((k : ℝ) * h)) (closedBall 0 ε)) ∧
        (∀ j, 1 ≤ j → j ≤ q →
          gapOn (taylorDecrement f j ((N : ℝ) * h)) (closedBall 0 ε) <
            ε * ε ^ j / (j.factorial : ℝ)) ∧
        run.state = state (affineSigma p q) ε h ∧ run.last = .stopTest (run.state N) ∧
        (∀ k < N, ¬Nonempty (PassedTest P f (run.state k).point (run.state k).radii)) ∧
        run.functionCount = N + 1 ∧ run.derivativeCount = N * p + q := by
  have hp : 1 ≤ p := hq.trans hqp
  have hr : 1 ≤ r := hp.trans hpr
  have hp0 : p ≠ 0 := by omega
  have hpc : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  let C := stepScale p
  have hC : 1 ≤ C := by
    have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have hf : (1 : ℝ) ≤ p.factorial := by exact_mod_cast Nat.factorial_pos p
    dsimp [C, stepScale]
    nlinarith
  have hC0 : 0 < C := by linarith
  let κ := 8 * C + 4
  have hκ : 0 ≤ κ := by dsimp [κ]; positivity
  obtain ⟨L, B, hc⟩ := exists_affineJet_chain r hr κ hκ
  refine ⟨max L B, B, ?_⟩
  intro ε hε hεsmall
  dsimp only
  have hε1 : ε < 1 := by linarith
  let γ : ℝ := (q : ℝ) * r / p
  have hγ : (q : ℝ) ≤ γ := by
    apply (le_div_iff₀ hpc).mpr
    have hpr' : (p : ℝ) ≤ r := by exact_mod_cast hpr
    nlinarith
  let τ := ε ^ γ / 4
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτle : τ ≤ ε ^ q / 4 := by
    dsimp [τ]
    gcongr
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_ge hε hε1.le hγ
  let W := ε ^ ((q : ℝ) / p)
  have hW : 0 < W := Real.rpow_pos_of_pos hε _
  have hWp : W ^ p = ε ^ q := by
    dsimp [W]
    rw [← Real.rpow_mul_natCast hε.le, div_mul_cancel₀ _ hpc.ne', Real.rpow_natCast]
  let b := ε ^ q + τ
  have hb : 0 < b := by dsimp [b]; positivity
  let t := b ^ ((p : ℝ)⁻¹)
  have ht : 0 < t := Real.rpow_pos_of_pos hb _
  have htp : t ^ p = b := Real.rpow_inv_natCast_pow hb.le hp0
  have hWt : W ≤ t := by
    apply (pow_le_pow_iff_left₀ hW.le ht.le hp0).mp
    rw [hWp, htp]
    dsimp [b]
    linarith
  let h := C * t
  have hh : 0 < h := mul_pos hC0 ht
  have hWh : W ≤ h := hWt.trans (le_mul_of_one_le_left ht.le hC)
  have hεW : ε ≤ W := by
    apply (pow_le_pow_iff_left₀ hε.le hW.le hp0).mp
    rw [hWp]
    exact pow_le_pow_of_le_one hε.le hε1.le hqp
  have hlarge : 4 * (p : ℝ) * p.factorial * ε ≤ h := by
    change C * ε ≤ C * t
    gcongr
    exact hεW.trans hWt
  have h2p : (2 : ℝ) ≤ 2 ^ p := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hp
  have htupper : t ≤ 2 * W := by
    apply (pow_le_pow_iff_left₀ ht.le (by positivity : 0 ≤ 2 * W) hp0).mp
    rw [htp, mul_pow, hWp]
    dsimp [b]
    nlinarith [mul_le_mul_of_nonneg_right h2p (pow_nonneg hε.le q)]
  have hupper : h ≤ 2 * C * W := by dsimp [h]; nlinarith
  have hW1 : W ≤ 1 := Real.rpow_le_one hε.le hε1.le (by positivity)
  have hhκ : h ≤ κ := by dsimp [κ]; nlinarith
  let G := (ε ^ q + τ) / (q.factorial : ℝ)
  let H := (ε ^ q - τ) / (q.factorial : ℝ)
  have hG : 0 < G := by dsimp [G]; positivity
  have hH : 0 ≤ H := by
    dsimp [H]
    exact div_nonneg (by linarith) (by positivity)
  have hGupper : G ≤ 2 * ε ^ q / (q.factorial : ℝ) := by
    dsimp [G]
    gcongr
    linarith
  have hGκ : G ≤ κ := by
    have hf : (1 : ℝ) ≤ q.factorial := by exact_mod_cast Nat.factorial_pos q
    have he := pow_le_one₀ hε.le hε1.le (n := q)
    have hh' : G ≤ 2 := hGupper.trans ((div_le_iff₀ (by positivity)).mpr (by nlinarith))
    dsimp [κ]
    linarith
  have hscale : affineSigma p q * h ^ p = (p.factorial : ℝ) * G := by
    dsimp [affineSigma, h, G]
    rw [mul_pow, htp]
    change (p.factorial : ℝ) / ((q.factorial : ℝ) * C ^ p) * (C ^ p * b) = _
    dsimp [b]
    field_simp
  have hWr : W ^ r = ε ^ γ := by
    dsimp [W, γ]
    rw [← Real.rpow_mul_natCast hε.le]
    congr 1
    ring
  have hjump : |G - H| ≤ κ * h ^ r := by
    have he : G - H = 2 * τ / (q.factorial : ℝ) := by dsimp [G, H]; ring
    rw [he, abs_of_nonneg (by positivity)]
    have htbound : 2 * τ / (q.factorial : ℝ) ≤ ε ^ γ := by
      have hf : (1 : ℝ) ≤ q.factorial := by exact_mod_cast Nat.factorial_pos q
      dsimp [τ]
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith [Real.rpow_pos_of_pos hε γ]
    have hpow : ε ^ γ ≤ h ^ r := by rw [← hWr]; exact pow_le_pow_left₀ hW.le hWh _
    have hk1 : 1 ≤ κ := by dsimp [κ]; linarith
    exact htbound.trans (hpow.trans (le_mul_of_one_le_left (by positivity) hk1))
  let a := affineExponent p q
  have ha : 0 ≤ a := by dsimp [a, affineExponent]; positivity
  have hGhexp : G * h ≤ 4 * C * ε ^ a := by
    have hfac : (1 : ℝ) ≤ q.factorial := by exact_mod_cast Nat.factorial_pos q
    have hG' : G ≤ 2 * ε ^ q := hGupper.trans (div_le_self (by positivity) hfac)
    have hpow : ε ^ q * W = ε ^ a := by
      dsimp [W, a, affineExponent]
      rw [← Real.rpow_natCast, ← Real.rpow_add hε]
      congr 1
      field_simp
    calc
      G * h ≤ (2 * ε ^ q) * (2 * C * W) := mul_le_mul hG' hupper hh.le (by positivity)
      _ = _ := by rw [show 2 * ε ^ q * (2 * C * W) = 4 * C * (ε ^ q * W) by ring, hpow]
  let N : ℕ := ⌈1 / ε ^ a⌉₊
  have hN : 0 < N := Nat.ceil_pos.mpr (by positivity)
  have hn : (N : ℝ) * ε ^ a ≤ 2 := by
    have hh' := mul_le_mul_of_nonneg_right
      (Nat.ceil_lt_add_one (show 0 ≤ 1 / ε ^ a by positivity)).le (Real.rpow_nonneg hε.le a)
    have hcanc : (1 / ε ^ a + 1) * ε ^ a = 1 + ε ^ a := by field_simp
    rw [hcanc] at hh'
    exact hh'.trans (by linarith [Real.rpow_le_one hε.le hε1.le ha])
  have hdrop : (N : ℝ) * G * h ≤ κ := by
    have hh' := mul_le_mul_of_nonneg_left hGhexp (show (0 : ℝ) ≤ N by positivity)
    dsimp [κ]
    nlinarith [hn]
  obtain ⟨f, hf, hLip, hjet, hbnd⟩ := hc N hN G H h hG.le hh hjump hdrop hGκ hhκ
  have hearlier (j : ℕ) (hj : 1 ≤ j) (hjq : j < q) :
      G * ε < ε * ε ^ j / (j.factorial : ℝ) :=
    affine_threshold_earlier hε hε1 hj hjq hGupper
  have hfail : ε * ε ^ q / (q.factorial : ℝ) < G * ε := by
    have he : ε ^ q / (q.factorial : ℝ) < G := by dsimp [G]; gcongr; linarith
    convert mul_lt_mul_of_pos_right he hε using 1; ring
  have hend (j : ℕ) (_hj : 1 ≤ j) (hjq : j ≤ q) :
      H * ε < ε * ε ^ j / (j.factorial : ℝ) := by
    have he : H < ε ^ q / (q.factorial : ℝ) := by dsimp [H]; gcongr; linarith
    have hm := mul_lt_mul_of_pos_right
      (he.trans_le (affine_threshold_mono hε hε1.le hjq)) hε
    convert hm using 1; ring
  obtain ⟨run, hs, hl, hnot, hfun, hder⟩ := run_of_affineJet hq hqp hpr hh
    (affineSigma_pos hp q) hε hε1 hG hH hGupper hscale hlarge hearlier hfail.le hend hjet
  refine ⟨f, N, h, run, hf, all_derivatives_lipschitz hf hLip hbnd, ?_, ?_, hh, rfl,
    ?_, ?_, hs, hl, hnot, hfun, hder⟩
  · intro x
    simpa using hbnd 0 (by omega) x
  · simpa [affineJet] using hjet 0 (by omega) 0 (by omega)
  · intro k hk
    rw [gap_affineJet hG.le hH hε.le (hqp.trans hpr) (hjet k hk.le),
      decrement_affineJet (hqp.trans hpr) (hjet k hk.le),
      ite_eq_right (by omega : q ≠ 0), ite_eq_left hk]
    exact hfail
  · intro j hj hjq
    rw [gap_affineJet hG.le hH hε.le ((hjq.trans hqp).trans hpr) (hjet N le_rfl),
      decrement_affineJet ((hjq.trans hqp).trans hpr) (hjet N le_rfl),
      ite_eq_right (by omega : j ≠ 0), ite_eq_right (by omega : ¬N < N)]
    exact hend j hj hjq

end Optimization.HigherOrderAffineRegularizationSharpness

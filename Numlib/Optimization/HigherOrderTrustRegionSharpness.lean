import Numlib.Optimization.HigherOrderSharpness
import Numlib.Optimization.HigherOrderTrustRegion
import Numlib.Analysis.Calculus.EuclideanOneHigherDeriv

/-!
# Sharp arbitrary-order trust-region executions

Uniform sparse-jet interpolation gives bounded smooth objectives. Only the highest requested
Taylor derivative is active before the endpoint. Constant trust-region radii equal the requested
accuracy, as in the construction in Cartis, Gould and Toint, Appendix B, Chapter 12.
-/

noncomputable section
open scoped Nat NNReal
namespace Optimization.HigherOrderTrustRegionSharpness
open HigherOrderTrustRegion HigherOrderSharpness TaylorCriticality RegularizedTaylorModel
open EuclideanOne Metric Set

/-- Fixed admissible parameters, with exact Taylor-gap witnesses and no forced expansion. -/
def parameters : Parameters where
  eta1 := 1 / 4
  eta2 := 1 / 2
  gamma1 := 1 / 2
  gamma2 := 1 / 2
  gamma3 := 1
  fraction := 1
  theta := 1
  radiusMax := 1
  eta1_pos := by norm_num
  eta_le := by norm_num
  eta2_lt_one := by norm_num
  gamma1_pos := by norm_num
  gamma_le := le_rfl
  gamma2_lt_one := by norm_num
  one_le_gamma3 := le_rfl
  fraction_pos := by norm_num
  fraction_le_one := le_rfl
  theta_pos := by norm_num
  theta_le_one := le_rfl

/-- A constant-spacing execution; trial data after the stopping point are immaterial. -/
def trace (q : ℕ) (h : ℝ) : Trace (EuclideanSpace ℝ (Fin 1)) where
  point k := coord.symm ((k : ℝ) * h)
  step _ := coord.symm h
  radius _ := h
  witness _ _ := coord.symm h
  order _ := q

/-- Every lifted sparse jet has exactly one potentially nonzero Taylor decrement. -/
theorem decrement_sparse {N q k : ℕ} {G h : ℝ} {f : ℝ → ℝ}
    (hq : 1 ≤ q) (hf : ContDiff ℝ q f)
    (hjet : ∀ i ≤ q, iteratedDeriv i f ((k : ℝ) * h) = sparseJet N q G h k i)
    {j : ℕ} (hj : j ≤ q) (d : EuclideanSpace ℝ (Fin 1)) :
    taylorDecrement (lift f) j (coord.symm ((k : ℝ) * h)) d =
      if j = q ∧ k < N then G / q.factorial * (coord d) ^ q else 0 := by
  induction j with
  | zero => simp [show (0 : ℕ) ≠ q by omega]
  | succ j ih =>
    rw [taylorDecrement_succ, ih (by omega)]
    have hd := coord.toContinuousLinearEquiv.toContinuousLinearMap.iteratedFDeriv_comp_right
      (hf.of_le (show (j + 1 : WithTop ℕ∞) ≤ q by exact_mod_cast hj))
      (coord.symm ((k : ℝ) * h)) (by rfl)
    change iteratedFDeriv ℝ (j + 1) (lift f) _ = _ at hd
    rw [hd]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      LinearIsometryEquiv.apply_symm_apply, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
      hjet (j + 1) hj, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
    have hjn : j ≠ q := by omega
    simp only [hjn, false_and, zero_sub, sparseJet, Nat.add_eq_zero_iff,
      Nat.one_ne_zero, and_false, ↓reduceIte]
    by_cases he : j + 1 = q
    · subst q
      simp only [↓reduceIte, true_and]
      split_ifs <;> ring
    · simp [he]

/-- Before the endpoint, every positive testing radius fails the highest-order criterion.
This excludes premature approximate minimizers obtained by choosing another small radius. -/
theorem gap_failure_sparse {N q k : ℕ} {ε δ : ℝ} {f : ℝ → ℝ}
    (hq : 1 ≤ q) (hε : 0 < ε) (hδ : 0 < δ) (hk : k < N)
    (hf : ContDiff ℝ q f)
    (hjet : ∀ j ≤ q, iteratedDeriv j f ((k : ℝ) * ε) =
      sparseJet N q (2 * q.factorial * ε) ε k j) :
    (q.factorial : ℝ) * ε * δ ^ q / q.factorial <
      gapOn (taylorDecrement (lift f) q ((trace q ε).point k)) (closedBall 0 δ) := by
  have hd := decrement_sparse hq hf hjet le_rfl (coord.symm δ)
  rw [ite_eq_left ⟨rfl, hk⟩, LinearIsometryEquiv.apply_symm_apply] at hd
  have hl := le_gapOn (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 1)) δ)
    (continuous_taylorDecrement (lift f) q ((trace q ε).point k)).continuousOn
    (show coord.symm δ ∈ closedBall 0 δ by
      simp [coord.symm.norm_map, Real.norm_eq_abs, abs_of_pos hδ])
  change taylorDecrement (lift f) q (coord.symm ((k : ℝ) * ε)) (coord.symm δ) ≤ _ at hl
  rw [hd] at hl
  have hc : (2 * (q.factorial : ℝ) * ε) / q.factorial = 2 * ε := by field_simp
  have ht : (q.factorial : ℝ) * ε * δ ^ q / q.factorial = ε * δ ^ q := by
    field_simp
  rw [hc] at hl
  rw [ht]
  exact (show ε * δ ^ q < 2 * ε * δ ^ q by nlinarith [pow_pos hδ q]).trans_le hl

/-- Uniform derivative bounds give Lipschitz bounds at all lower orders. -/
theorem all_derivatives_lipschitz {q : ℕ} {f : ℝ → ℝ} {L B : ℝ≥0}
    (hf : ContDiff ℝ q f) (hL : LipschitzWith L (iteratedDeriv q f))
    (hb : ∀ j ≤ q, ∀ x, |iteratedDeriv j f x| ≤ B) :
    ∀ j ≤ q, LipschitzWith (max L B) (iteratedFDeriv ℝ j (lift f)) := by
  intro j hj
  apply EuclideanOne.iteratedFDeriv_lipschitz (hf.of_le (by exact_mod_cast hj))
  by_cases he : j = q
  · subst j
    exact hL.weaken (le_max_left _ _)
  · apply LipschitzWith.weaken (K := B) _ (le_max_right _ _)
    apply lipschitzWith_of_nnnorm_deriv_le
      (hf.differentiable_iteratedDeriv j (by exact_mod_cast (show j < q by omega)))
    intro x
    change ‖deriv (iteratedDeriv j f) x‖ ≤ (B : ℝ)
    simpa only [← iteratedDeriv_succ, Real.norm_eq_abs] using hb (j + 1) (by omega) x

/-- Sparse actual objective derivatives produce an admissible execution and its first stop. -/
theorem run_of_sparseJet {N q : ℕ} {h : ℝ} {f : ℝ → ℝ}
    (hq : 1 ≤ q) (hh : 0 < h) (hh1 : h ≤ 1) (hf : ContDiff ℝ q f)
    (hjet : ∀ k ≤ N, ∀ j ≤ q,
      iteratedDeriv j f ((k : ℝ) * h) = sparseJet N q (2 * q.factorial * h) h k j) :
    IsRun parameters q (fun j => j.factorial * h) (lift f) (trace q h) ∧
      (∀ k < N, ¬Stops parameters q (fun j => j.factorial * h) (lift f) (trace q h) k) ∧
      Stops parameters q (fun j => j.factorial * h) (lift f) (trace q h) N ∧
      derivativeBatches parameters (lift f) (trace q h) N = N + 1 := by
  have hr (k : ℕ) : testRadius parameters (trace q h) k = h := by
    simp [testRadius, trace, parameters, min_eq_left hh1]
  have hd (k : ℕ) (hk : k ≤ N) (j : ℕ) (hj : j ≤ q)
      (d : EuclideanSpace ℝ (Fin 1)) :
      taylorDecrement (lift f) j ((trace q h).point k) d =
        if j = q ∧ k < N then 2 * h * (coord d) ^ q else 0 := by
    rw [show (trace q h).point k = coord.symm ((k : ℝ) * h) from rfl,
      decrement_sparse hq hf (hjet k hk) hj]
    split_ifs <;> first | rfl | congr 1; field_simp
  have hw (k : ℕ) (hk : k ≤ N) (j : ℕ) (hj : j ≤ q) :
      taylorDecrement (lift f) j ((trace q h).point k) ((trace q h).witness k j) =
        if j = q ∧ k < N then 2 * h * h ^ q else 0 := by
    rw [hd k hk j hj]
    simp [trace]
  have ht (k j : ℕ) : parameters.fraction * ((j.factorial : ℝ) * h) *
      testRadius parameters (trace q h) k ^ j / j.factorial = h * h ^ j := by
    rw [hr]
    dsimp [parameters]
    field_simp
  have hstop : Stops parameters q (fun j => j.factorial * h) (lift f) (trace q h) N := by
    intro j _ hj
    rw [hw N le_rfl j hj, ht]
    simp only [lt_self_iff_false, and_false, ite_false]
    positivity
  have hnot (k : ℕ) (hk : k < N) :
      ¬Stops parameters q (fun j => j.factorial * h) (lift f) (trace q h) k := by
    intro hs
    have hh' := hs q hq le_rfl
    rw [hw k hk.le q le_rfl, ht, ite_eq_left ⟨rfl, hk⟩] at hh'
    nlinarith [pow_pos hh q]
  have hrat (k : ℕ) (hk : k < N) : ratio (lift f) (trace q h) k = 1 := by
    have hp : (trace q h).point k + (trace q h).step k =
        coord.symm (((k + 1 : ℕ) : ℝ) * h) := by
      simp only [trace, ← map_add, Nat.cast_add, Nat.cast_one]
      congr 1
      ring
    have hv (i : ℕ) (hi : i ≤ N) : f ((i : ℝ) * h) =
        -(i : ℝ) * (2 * q.factorial * h) * h ^ q / q.factorial := by
      simpa [sparseJet] using hjet i hi 0 (by omega)
    unfold ratio
    rw [hp, show (trace q h).order k = q from rfl,
      hd k hk.le q le_rfl, ite_eq_left ⟨rfl, hk⟩]
    simp only [trace, lift_apply, LinearIsometryEquiv.apply_symm_apply]
    rw [hv k hk.le, hv (k + 1) hk]
    push_cast
    field_simp
    ring
  have hprefix (M : ℕ) (hMN : M ≤ N) :
      LegalPrefix parameters q (fun j => j.factorial * h) (lift f) (trace q h) M := by
    constructor
    · exact hh
    · exact hh1
    · intro k _ j _ _
      rw [hr]
      simp [trace, coord.symm.norm_map, Real.norm_eq_abs, abs_of_pos hh]
    · intro k hk j _ hj
      rw [hr]
      simp only [parameters, one_mul]
      apply gapOn_le (show (closedBall (0 : EuclideanSpace ℝ (Fin 1)) h).Nonempty by
        exact ⟨0, by simpa using hh.le⟩)
      intro d hd'
      rw [hd k (hk.trans hMN) j hj d, hw k (hk.trans hMN) j hj]
      split_ifs
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hd'' : |coord d| ≤ h := by
          simpa only [mem_closedBall, dist_zero_right, ← coord.norm_map d,
            Real.norm_eq_abs] using hd'
        calc
          (coord d) ^ q ≤ |(coord d) ^ q| := le_abs_self _
          _ = |coord d| ^ q := abs_pow _ _
          _ ≤ h ^ q := pow_le_pow_left₀ (abs_nonneg _) hd'' _
      · exact le_rfl
    · intro k hk
      exact hnot k (hk.trans_le hMN)
    · intro k _
      exact hq
    · intro k _
      exact le_rfl
    · intro k hk j _ hj
      rw [hw k (hk.le.trans hMN) j (by exact hj.le), ht]
      simp only [show j ≠ q by exact ne_of_lt hj, false_and, ite_false]
      positivity
    · intro k hk
      rw [show (trace q h).order k = q from rfl,
        hw k (hk.le.trans hMN) q le_rfl, ht, ite_eq_left ⟨rfl, hk.trans_le hMN⟩]
      nlinarith [pow_pos hh q]
    · intro k _
      simp [trace, coord.symm.norm_map, Real.norm_eq_abs, abs_of_pos hh]
    · intro k _
      exact le_rfl
    · intro k hk
      rw [hrat k (hk.trans_le hMN)]
      norm_num [parameters]
      simp only [trace, ← map_add, Nat.cast_add, Nat.cast_one]
      congr 1
      ring
    · intro k hk
      rw [hrat k (hk.trans_le hMN)]
      norm_num [parameters, trace]
      exact hh1
  refine ⟨?_, hnot, hstop, ?_⟩
  · intro M hM
    apply hprefix
    by_contra hMN
    exact hM N (by omega) hstop
  · unfold derivativeBatches ParameterUpdates.successCount
    have he : (Finset.range N).filter (fun k => parameters.eta1 ≤ ratio (lift f) (trace q h) k) =
        Finset.range N := by
      apply Finset.filter_eq_self.mpr
      intro k hk
      rw [hrat k (Finset.mem_range.mp hk)]
      norm_num [parameters]
    rw [he, Finset.card_range]

/-- For every positive requested order, uniformly bounded objectives with uniformly Lipschitz
positive-order derivatives admit actual trust-region executions requiring the inverse
`(q+1)` power of the tolerance. The initial radius is explicitly the tolerance. -/
theorem exists_hard_family (q : ℕ) (hq : 1 ≤ q) :
    ∃ L B : ℝ≥0, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (f : EuclideanSpace ℝ (Fin 1) → ℝ) (N : ℕ),
        ContDiff ℝ q f ∧
        (∀ j ≤ q, LipschitzWith L (iteratedFDeriv ℝ j f)) ∧
        (∀ x, |f x| ≤ B) ∧ f 0 = 0 ∧
        (trace q ε).point 0 = 0 ∧ (trace q ε).radius 0 = ε ∧
        IsRun parameters q (fun j => j.factorial * ε) f (trace q ε) ∧
        (∀ k < N, ¬Stops parameters q (fun j => j.factorial * ε) f (trace q ε) k) ∧
        Stops parameters q (fun j => j.factorial * ε) f (trace q ε) N ∧
        (∀ k < N, ∀ δ : ℝ, 0 < δ →
          (q.factorial : ℝ) * ε * δ ^ q / q.factorial <
            gapOn (taylorDecrement f q ((trace q ε).point k)) (closedBall 0 δ)) ∧
        functionEvaluations N = N + 1 ∧
        derivativeBatches parameters f (trace q ε) N = N + 1 ∧
        1 / ε ^ (q + 1) ≤ (N : ℝ) := by
  let κ : ℝ := 4 * q.factorial
  have hκ : 0 ≤ κ := by dsimp [κ]; positivity
  have hκ1 : 1 ≤ κ := by
    have : (1 : ℝ) ≤ q.factorial := by exact_mod_cast Nat.factorial_pos q
    dsimp [κ]
    linarith
  obtain ⟨L, B, hc⟩ := exists_sparseJet_chain q q hq le_rfl κ hκ
  refine ⟨max L B, B, ?_⟩
  intro ε hε hε1
  let N : ℕ := ⌈1 / ε ^ (q + 1)⌉₊
  have hN : 0 < N := Nat.ceil_pos.mpr (by positivity)
  have hpow : 0 < ε ^ (q + 1) := pow_pos hε _
  have hn : (N : ℝ) * ε ^ (q + 1) ≤ 2 := by
    have hh := (mul_lt_mul_of_pos_right
      (Nat.ceil_lt_add_one (show 0 ≤ 1 / ε ^ (q + 1) by positivity)) hpow).le
    have he : (1 / ε ^ (q + 1) + 1) * ε ^ (q + 1) = 1 + ε ^ (q + 1) := by
      field_simp
    rw [he] at hh
    exact hh.trans (by linarith [pow_le_one₀ hε.le hε1 (n := q + 1)])
  have hdrop : (N : ℝ) * (2 * q.factorial * ε) * ε ^ q ≤ κ := by
    calc
      _ = (2 * q.factorial) * ((N : ℝ) * ε ^ (q + 1)) := by rw [pow_succ]; ring
      _ ≤ (2 * q.factorial) * 2 := mul_le_mul_of_nonneg_left hn (by positivity)
      _ = κ := by dsimp [κ]; ring
  have hG : 2 * (q.factorial : ℝ) * ε ≤ κ := by
    have hm := mul_le_mul_of_nonneg_left hε1 (show 0 ≤ 2 * (q.factorial : ℝ) by positivity)
    dsimp [κ]
    nlinarith
  obtain ⟨psi, hpsi, hLip, hjet, hb⟩ := hc N hN (2 * q.factorial * ε) ε
    (by positivity) hε (by simp only [Nat.sub_self, zero_add, pow_one]; dsimp [κ]; nlinarith)
    hdrop hG (hε1.trans hκ1)
  obtain ⟨hrun, hnot, hstop, hbatch⟩ := run_of_sparseJet hq hε hε1 hpsi hjet
  refine ⟨lift psi, N, EuclideanOne.contDiff hpsi,
    all_derivatives_lipschitz hpsi hLip hb, ?_, ?_, ?_, rfl, hrun, hnot, hstop,
    ?_, rfl, hbatch, Nat.le_ceil _⟩
  · intro x
    simpa using hb 0 (by omega) (coord x)
  · simpa [sparseJet] using hjet 0 (by omega) 0 (by omega)
  · simp [trace]
  · intro k hk δ hδ
    exact gap_failure_sparse hq hε hδ hk hpsi (hjet k hk.le)

end Optimization.HigherOrderTrustRegionSharpness

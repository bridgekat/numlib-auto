import Numlib.Optimization.AdaptiveInverseIterationBounds

/-!
# Local convergence of adaptive inverse iteration

The scalar estimates below implement the positivity and contraction bootstrap for the
actual inverse/Rayleigh update, using its derived spectral Rayleigh-error estimate.
-/

noncomputable section
open scoped InnerProductSpace Topology
open Filter
namespace Optimization.AdaptiveInverseIteration

/-- A small positive neighborhood turns a quadratic-batch Rayleigh error into positive,
contractive corrected powers, uniformly over all legal choices with bounded actual counts. -/
theorem Parameters.correctedPower_bounds (p : Parameters) (B : ℕ) {C eta : ℝ}
    (hC : 0 ≤ C) (heta1 : eta ≤ 1)
    (hlinear : C * eta ≤ 1)
    (hmargin : C * eta ^ p.exponentMargin ≤ p.dampingLower / 2)
    (hcontract : p.dampingUpper * (2 : ℝ) ^ (2 * B) *
      eta ^ (p.exponentLower - 1) ≤ 1 / 2)
    (c : Choice) (hc : c.Legal p) (hB : c.count ≤ B) {e r : ℝ}
    (he : 0 < e) (hee : e ≤ eta) (hr0 : 0 ≤ r) (hr : r ≤ C * e ^ (2 * c.count)) :
    (p.dampingLower / 2) * e ^ c.exponent ≤
      -r + c.damping * (e + r) ^ c.exponent ∧
    -r + c.damping * (e + r) ^ c.exponent ≤
      p.dampingUpper * (2 : ℝ) ^ (2 * B) * e ^ c.exponent ∧
    -r + c.damping * (e + r) ^ c.exponent ≤ e / 2 := by
  have he1 := hee.trans heta1
  have hg0 : 0 ≤ c.exponent := (lt_trans zero_lt_one p.exponent_lt).le.trans hc.2.2.2.1
  have hD0 : 0 ≤ c.damping := p.damping_pos.le.trans hc.2.2.1.1
  have hU0 : 0 ≤ p.dampingUpper := p.damping_pos.le.trans p.damping_le
  have hcount : (2 : ℝ) ≤ ((2 * c.count : ℕ) : ℝ) := by
    have hn := hc.1
    exact_mod_cast (by omega : 2 ≤ 2 * c.count)
  have hbound : c.exponent ≤ ((2 * B : ℕ) : ℝ) := by
    have hcast : (c.count : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
    have hg := hc.2.2.2.2
    push_cast
    linarith [p.margin_pos]
  have hpow2 : e ^ (2 * c.count) ≤ e ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge he he1 hcount
  have hre : r ≤ e := by
    calc
      r ≤ C * e ^ 2 := hr.trans (mul_le_mul_of_nonneg_left hpow2 hC)
      _ ≤ C * (eta * e) := mul_le_mul_of_nonneg_left
        (by nlinarith [mul_le_mul_of_nonneg_right hee he.le]) hC
      _ = (C * eta) * e := by ring
      _ ≤ 1 * e := mul_le_mul_of_nonneg_right hlinear he.le
      _ = e := one_mul e
  have hpowMargin : e ^ (2 * c.count) ≤ e ^ c.exponent * eta ^ p.exponentMargin := by
    calc
      e ^ (2 * c.count) = e ^ c.exponent *
          e ^ (((2 * c.count : ℕ) : ℝ) - c.exponent) := by
        rw [← Real.rpow_add he]
        rw [← Real.rpow_natCast]
        congr 1
        ring
      _ ≤ e ^ c.exponent * e ^ p.exponentMargin := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg he.le _)
        apply Real.rpow_le_rpow_of_exponent_ge he he1
        have hg := hc.2.2.2.2
        push_cast
        linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow he.le hee p.margin_pos.le) (Real.rpow_nonneg he.le _)
  have hrsmall : r ≤ (p.dampingLower / 2) * e ^ c.exponent := by
    calc
      r ≤ C * (e ^ c.exponent * eta ^ p.exponentMargin) :=
        hr.trans (mul_le_mul_of_nonneg_left hpowMargin hC)
      _ = (C * eta ^ p.exponentMargin) * e ^ c.exponent := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hmargin (Real.rpow_nonneg he.le _)
  have hlower : p.dampingLower * e ^ c.exponent ≤ c.damping * (e + r) ^ c.exponent :=
    mul_le_mul hc.2.2.1.1 (Real.rpow_le_rpow he.le (le_add_of_nonneg_right hr0) hg0)
      (Real.rpow_nonneg he.le _) hD0
  have hupper : -r + c.damping * (e + r) ^ c.exponent ≤
      p.dampingUpper * (2 : ℝ) ^ (2 * B) * e ^ c.exponent := by
    calc
      _ ≤ c.damping * (e + r) ^ c.exponent := by linarith
      _ ≤ p.dampingUpper * (2 * e) ^ c.exponent :=
        mul_le_mul hc.2.2.1.2
          (Real.rpow_le_rpow (by linarith) (by linarith) hg0)
          (Real.rpow_nonneg (by linarith) _) hU0
      _ = p.dampingUpper * (2 : ℝ) ^ c.exponent * e ^ c.exponent := by
        rw [Real.mul_rpow (by norm_num) he.le]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hbound) hU0)
        (Real.rpow_nonneg he.le _)
  refine ⟨by linarith, hupper, ?_⟩
  calc
    _ ≤ p.dampingUpper * (2 : ℝ) ^ (2 * B) * e ^ p.exponentLower :=
      hupper.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge he he1 hc.2.2.2.1) (by positivity))
    _ = (p.dampingUpper * (2 : ℝ) ^ (2 * B) * e ^ (p.exponentLower - 1)) * e := by
      have hsplit : e ^ p.exponentLower = e ^ (p.exponentLower - 1) * e := by
        calc
          _ = e ^ ((p.exponentLower - 1) + 1) := by congr 1; ring
          _ = _ := by rw [Real.rpow_add he, Real.rpow_one]
      rw [hsplit]
      ring
    _ ≤ (p.dampingUpper * (2 : ℝ) ^ (2 * B) * eta ^ (p.exponentLower - 1)) * e :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow he.le hee (by linarith [p.exponent_lt])) (by positivity)) he.le
    _ ≤ (1 / 2) * e := mul_le_mul_of_nonneg_right hcontract he.le
    _ = e / 2 := by ring

/-- There is a common positive radius satisfying all scalar positivity and contraction
tests. Its dependence on the actual global count bound is explicit. -/
theorem Parameters.exists_correctedPower_radius (p : Parameters) (B : ℕ) (C : ℝ) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ 1 ∧ C * eta ≤ 1 ∧
      C * eta ^ p.exponentMargin ≤ p.dampingLower / 2 ∧
      p.dampingUpper * (2 : ℝ) ^ (2 * B) * eta ^ (p.exponentLower - 1) ≤ 1 / 2 := by
  have hcont1 : Continuous (fun e : ℝ => C * e) := continuous_const.mul continuous_id
  have hlim1 : Tendsto (fun e : ℝ => C * e) (𝓝 0) (𝓝 0) := by
    simpa using hcont1.tendsto (0 : ℝ)
  have hlim2 : Tendsto (fun e : ℝ => C * e ^ p.exponentMargin) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous (fun e : ℝ => C * e ^ p.exponentMargin) :=
      continuous_const.mul (Real.continuous_rpow_const p.margin_pos.le)
    simpa [Real.zero_rpow p.margin_pos.ne'] using hcont.tendsto (0 : ℝ)
  have hlim3 : Tendsto (fun e : ℝ =>
      p.dampingUpper * (2 : ℝ) ^ (2 * B) * e ^ (p.exponentLower - 1)) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous (fun e : ℝ =>
        p.dampingUpper * (2 : ℝ) ^ (2 * B) * e ^ (p.exponentLower - 1)) :=
      continuous_const.mul (Real.continuous_rpow_const
        (show 0 ≤ p.exponentLower - 1 by linarith [p.exponent_lt]))
    simpa [Real.zero_rpow (show p.exponentLower - 1 ≠ 0 by linarith [p.exponent_lt])] using
      hcont.tendsto (0 : ℝ)
  have hall : ∀ᶠ e : ℝ in 𝓝[>] 0, e < 1 ∧ C * e < 1 ∧
      C * e ^ p.exponentMargin < p.dampingLower / 2 ∧
      p.dampingUpper * (2 : ℝ) ^ (2 * B) * e ^ (p.exponentLower - 1) < 1 / 2 :=
    ((eventually_lt_nhds zero_lt_one).and
      ((hlim1.eventually_lt_const zero_lt_one).and
        ((hlim2.eventually_lt_const (by linarith [p.damping_pos])).and
          (hlim3.eventually_lt_const (by norm_num))))).filter_mono nhdsWithin_le_nhds
  obtain ⟨eta, heta, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hall
  obtain ⟨h1, h2, h3, h4⟩ := hsub ⟨heta, le_rfl⟩
  exact ⟨eta, heta, h1.le, h2.le, h3.le, h4.le⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)

/-- The actual adaptive inverse iteration has a positive contracting neighborhood and
uniform consecutive power bounds. Its radius may depend on the actual eventually constant
count stream, but is independent of the initial shift. All Rayleigh estimates are derived
from the operator and the genuine initially present lowest spectral coordinate. -/
theorem exists_local_iterate_bounds (v : E) (c : ℕ → Choice) (p : Parameters)
    (h0 : ‖v‖ = 1) {i : Fin (Module.finrank ℝ E)}
    (hi : (hA.eigenvectorBasis rfl).repr v i ≠ 0)
    (hlo : ∀ j, hA.eigenvalues rfl i ≤ hA.eigenvalues rfl j)
    (hlegal : ∀ k, (c k).Legal p) (nbar : ℕ)
    (hc : ∀ᶠ k in atTop, (c k).count = nbar) :
    ∃ eta K : ℝ, 0 < eta ∧ 0 < K ∧ ∀ t,
      0 < t + hA.eigenvalues rfl i → t + hA.eigenvalues rfl i ≤ eta →
      let e := fun k => (iterate A ⟨t, v⟩ c k).shift + hA.eigenvalues rfl i;
      Tendsto e atTop (𝓝 0) ∧
      Tendsto (fun k => e (k + 1) / e k) atTop (𝓝 0) ∧ ∀ k, 0 < e k ∧
        (p.dampingLower / 2) * (e k) ^ (c k).exponent ≤ e (k + 1) ∧
        e (k + 1) ≤ K * (e k) ^ (c k).exponent ∧ e (k + 1) ≤ e k / 2 := by
  obtain ⟨B, hB⟩ := exists_count_bound_of_eventually_constant c nbar hc
  obtain ⟨C, hC, hRayleigh⟩ := exists_uniform_iterate_rayleighError_constant
    hA v c h0 hi hlo nbar hc
  obtain ⟨eta, heta, heta1, hlinear, hmargin, hcontract⟩ :=
    p.exists_correctedPower_radius B C
  let K := p.dampingUpper * (2 : ℝ) ^ (2 * B)
  have hK : 0 < K := mul_pos (p.damping_pos.trans_le p.damping_le) (by positivity)
  refine ⟨eta, K, heta, hK, ?_⟩
  intro t ht hte
  let s : State E := ⟨t, v⟩
  let e : ℕ → ℝ := fun k => (iterate A s c k).shift + hA.eigenvalues rfl i
  change Tendsto e atTop (𝓝 0) ∧ _
  have hstep : ∀ k, (∀ j ≤ k, 0 < e j) → e k ≤ eta →
      (p.dampingLower / 2) * (e k) ^ (c k).exponent ≤ e (k + 1) ∧
      e (k + 1) ≤ K * (e k) ^ (c k).exponent ∧ e (k + 1) ≤ e k / 2 := by
    intro k hprefix hke
    have hreg : ∀ j < k, ∀ l, (iterate A s c j).shift + hA.eigenvalues rfl l ≠ 0 :=
      fun j hj l => ne_of_gt (by
        have hp := hprefix j hj.le
        dsimp [e] at hp
        linarith [hlo l])
    have hn := norm_iterate_vector A s c h0 k (fun j hj =>
      Optimization.SecularResolvent.isUnit_shift hA _ (hreg j hj))
    have hregk : ∀ l, (iterate A s c k).shift + hA.eigenvalues rfl l ≠ 0 :=
      fun l => ne_of_gt (by
        have hp := hprefix k le_rfl
        dsimp [e] at hp
        linarith [hlo l])
    let r := inner ℝ (iterate A s c (k + 1)).vector
      (A (iterate A s c (k + 1)).vector) - hA.eigenvalues rfl i
    have hr0 : 0 ≤ r := by
      simpa only [r, iterate_succ, update_vector] using
        sub_nonneg.mpr (Krylov.inner_shiftedInverseBatch_ge hA
          (iterate A s c k).vector (norm_ne_zero_iff.mp (by rw [hn]; norm_num))
            hregk hlo (c k).count)
    have hr : r ≤ C * (e k) ^ (2 * (c k).count) := hRayleigh t k hprefix
    have hs := p.correctedPower_bounds B hC.le heta1 hlinear hmargin hcontract
      (c k) (hlegal k) (hB k) (hprefix k le_rfl) hke hr0 hr
    have heq : e (k + 1) = -r + (c k).damping * (e k + r) ^ (c k).exponent := by
      exact update_shift_error (iterate A s c k) (c k) (hA.eigenvalues rfl i)
    simpa only [← heq, K] using hs
  have hpos : ∀ k, 0 < e k ∧ e k ≤ eta := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      cases k with
      | zero => exact ⟨ht, hte⟩
      | succ k =>
        have hp : ∀ j ≤ k, 0 < e j := fun j hj =>
          (ih j (Nat.lt_succ_of_le hj)).1
        have hk := ih k (Nat.lt_succ_self k)
        have hs := hstep k hp hk.2
        have hpay : 0 < (p.dampingLower / 2) * (e k) ^ (c k).exponent :=
          mul_pos (by linarith [p.damping_pos]) (Real.rpow_pos_of_pos hk.1 _)
        exact ⟨hpay.trans_le hs.1, hs.2.2.trans ((by linarith : e k / 2 ≤ e k).trans hk.2)⟩
  have hb : ∀ k, 0 < e k ∧
      (p.dampingLower / 2) * (e k) ^ (c k).exponent ≤ e (k + 1) ∧
      e (k + 1) ≤ K * (e k) ^ (c k).exponent ∧ e (k + 1) ≤ e k / 2 :=
    fun k => ⟨(hpos k).1, hstep k (fun j _ => (hpos j).1) (hpos k).2⟩
  have hgeom : ∀ k, e k ≤ (1 / 2 : ℝ) ^ k * e 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        e (k + 1) ≤ e k / 2 := (hb k).2.2.2
        _ ≤ ((1 / 2 : ℝ) ^ k * e 0) / 2 := div_le_div_of_nonneg_right ih (by norm_num)
        _ = (1 / 2 : ℝ) ^ (k + 1) * e 0 := by rw [pow_succ]; ring
  have hlim : Tendsto (fun k => (1 / 2 : ℝ) ^ k * e 0) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (e 0)
  have hlimE := squeeze_zero (fun k => (hpos k).1.le) hgeom hlim
  have hlimPower : Tendsto (fun k => K * (e k) ^ (p.exponentLower - 1)) atTop (𝓝 0) := by
    have hcont : Continuous (fun x : ℝ => K * x ^ (p.exponentLower - 1)) :=
      continuous_const.mul (Real.continuous_rpow_const (by linarith [p.exponent_lt]))
    simpa [Function.comp_def,
      Real.zero_rpow (show p.exponentLower - 1 ≠ 0 by linarith [p.exponent_lt])] using
      (hcont.tendsto 0).comp hlimE
  have hratio : ∀ k, e (k + 1) / e k ≤ K * (e k) ^ (p.exponentLower - 1) := by
    intro k
    calc
      _ ≤ (K * (e k) ^ (c k).exponent) / e k :=
        div_le_div_of_nonneg_right (hb k).2.2.1 (hpos k).1.le
      _ = K * (e k) ^ ((c k).exponent - 1) := by
        rw [Real.rpow_sub_one (hpos k).1.ne']
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge (hpos k).1 ((hpos k).2.trans heta1)
          (by linarith [(hlegal k).2.2.2.1])) hK.le
  exact ⟨hlimE, squeeze_zero (fun k =>
    div_nonneg (hpos (k + 1)).1.le (hpos k).1.le) hratio hlimPower, hb⟩

end Optimization.AdaptiveInverseIteration

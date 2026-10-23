import Numlib.Optimization.TrustRegion.HighOrder.Radius
import Numlib.Optimization.EvaluationComplexity.Decrease

/-!
# Termination and evaluation counts for arbitrary-order trust regions

A uniformly positive fixed radius coefficient also covers objectives with zero initial
Taylor jet. Actual objective budgets bound accepted trials, and the proved endpoint
radius floor controls every trial through the logarithmic update count. All counters
include initialization. The stopping test is on computed Taylor decrements; its actual
criticality conclusion is derived from the algorithm's checked model approximation.
-/

namespace HighOrderTrustRegion
open Set EvaluationComplexity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Accuracy-independent settings of Algorithm 12.2.1. The chosen positive
optimality-radius cap is fixed before a request with minimum accuracy at most that cap. -/
structure Settings (q : ℕ) where
  order_pos : 0 < q
  zeta : ℝ
  zeta_pos : 0 < zeta
  zeta_le_one : zeta ≤ 1
  theta : ℝ
  theta_pos : 0 < theta
  theta_le_one : theta ≤ 1
  eta1 : ℝ
  eta2 : ℝ
  gamma1 : ℝ
  gamma2 : ℝ
  gamma3 : ℝ
  radiusMax : ℝ
  eta1_pos : 0 < eta1
  eta1_le_eta2 : eta1 ≤ eta2
  eta2_lt_one : eta2 < 1
  gamma1_pos : 0 < gamma1
  gamma1_le_gamma2 : gamma1 ≤ gamma2
  gamma2_lt_one : gamma2 < 1
  one_le_gamma3 : 1 ≤ gamma3

/-- Add an admissible accuracy request to fixed algorithm settings. -/
def Settings.withAccuracy {q : ℕ} (S : Settings q) (ε : Fin q → ℝ)
    (hε : ∀ a, 0 < ε a) (hε1 : ∀ a, ε a ≤ 1) (hεθ : ∃ a, ε a ≤ S.theta) : Parameters q := {
  order_pos := S.order_pos
  accuracy := ε
  accuracy_pos := hε
  accuracy_le_one := hε1
  zeta := S.zeta
  zeta_pos := S.zeta_pos
  zeta_le_one := S.zeta_le_one
  theta := S.theta
  theta_pos := S.theta_pos
  theta_le_one := S.theta_le_one
  min_accuracy_le_theta := hεθ
  eta1 := S.eta1
  eta2 := S.eta2
  gamma1 := S.gamma1
  gamma2 := S.gamma2
  gamma3 := S.gamma3
  radiusMax := S.radiusMax
  eta1_pos := S.eta1_pos
  eta1_le_eta2 := S.eta1_le_eta2
  eta2_lt_one := S.eta2_lt_one
  gamma1_pos := S.gamma1_pos
  gamma1_le_gamma2 := S.gamma1_le_gamma2
  gamma2_lt_one := S.gamma2_lt_one
  one_le_gamma3 := S.one_le_gamma3 }

/-- A canonical admissible request for fixed settings, used only to state positivity
of the fixed coefficients independently of any user-supplied accuracy values. -/
def Settings.defaultParameters {q : ℕ} (S : Settings q) : Parameters q :=
  S.withAccuracy (fun _ => S.theta) (fun _ => S.theta_pos) (fun _ => S.theta_le_one)
    ⟨⟨0,S.order_pos⟩, le_rfl⟩

/-- A uniformly positive variant of (12.2.14), using `max 1 B₀` so that its value is
fixed and positive even when the complete initial derivative jet vanishes. No accuracy
is an argument. On every nonterminal run it is no larger than the source coefficient. -/
noncomputable def positiveRadiusConstant (f : E → ℝ) (q : ℕ) (hq : 0 < q) (x₀ : E)
    (Δ₀ theta eta2 gamma1 L : ℝ) : ℝ :=
  gamma1 * (1 - eta2) / L * min theta
    (Δ₀ * min Δ₀ theta ^ q /
      (2 * (q.factorial : ℝ) * max 1 (initialDerivativeBound f q hq x₀)))

/-- The positive radius coefficient has the bounds needed by the uniform endpoint floor. -/
theorem positiveRadiusConstant_properties {q : ℕ} (f : E → ℝ) (P : Parameters q)
    (x₀ : E) {Δ₀ L : ℝ} (hΔ : 0 < Δ₀) (hL : 1 ≤ L) :
    let κ := positiveRadiusConstant f q P.order_pos x₀ Δ₀ P.theta P.eta2 P.gamma1 L
    0 < κ ∧ κ ≤ Δ₀ ∧ κ < P.gamma1 ∧ κ ≤ P.gamma1 * (1 - P.eta2) / L := by
  let B := max 1 (initialDerivativeBound f q P.order_pos x₀)
  let δ := min Δ₀ P.theta
  let c := P.gamma1 * (1 - P.eta2) / L
  have hB : 1 ≤ B := le_max_left _ _
  have hBpos : 0 < B := by linarith
  have hδ : 0 < δ := lt_min hΔ P.theta_pos
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans P.theta_le_one
  have hLp : 0 < L := by linarith
  have hηpos : 0 < 1 - P.eta2 := by linarith [P.eta2_lt_one]
  have hη0 : 0 < P.eta2 := P.eta1_pos.trans_le P.eta1_le_eta2
  have hc : 0 < c := div_pos (mul_pos P.gamma1_pos hηpos) hLp
  have hcγ : c < P.gamma1 := by
    apply (div_lt_iff₀ hLp).2
    nlinarith [P.gamma1_pos]
  have hc1 : c ≤ 1 := hcγ.le.trans (P.gamma1_le_gamma2.trans P.gamma2_lt_one.le)
  have hfact : (1 : ℝ) ≤ q.factorial := by exact_mod_cast Nat.factorial_pos q
  have hden : 1 ≤ 2 * (q.factorial : ℝ) * B := by nlinarith
  have hdenpos : 0 < 2 * (q.factorial : ℝ) * B := by positivity
  have hratio : Δ₀ * δ ^ q / (2 * (q.factorial : ℝ) * B) ≤ Δ₀ := by
    apply (div_le_iff₀ hdenpos).2
    have hp := pow_le_one₀ hδ.le hδ1 (n := q)
    nlinarith [mul_le_mul_of_nonneg_left hp hΔ.le,
      mul_le_mul_of_nonneg_left hden hΔ.le]
  have hmpos : 0 < min P.theta (Δ₀ * δ ^ q / (2 * (q.factorial : ℝ) * B)) :=
    lt_min P.theta_pos (div_pos (mul_pos hΔ (pow_pos hδ _)) hdenpos)
  have hm1 : min P.theta (Δ₀ * δ ^ q / (2 * (q.factorial : ℝ) * B)) ≤ 1 :=
    (min_le_left _ _).trans P.theta_le_one
  have hκc : c * min P.theta (Δ₀ * δ ^ q / (2 * (q.factorial : ℝ) * B)) ≤ c :=
    mul_le_of_le_one_right hc.le hm1
  refine ⟨mul_pos hc hmpos, ?_, hκc.trans_lt hcγ, hκc⟩
  exact (mul_le_of_le_one_left hmpos.le hc1).trans ((min_le_right _ _).trans hratio)

/-- The uniformly positive coefficient is at most the source coefficient whenever
there is a genuine initial failed stopping test. -/
theorem positiveRadiusConstant_le {q : ℕ} {f : E → ℝ} {P : Parameters q}
    {x s : ℕ → E} {d : ℕ → Fin q → E} {j : ℕ → Fin q} {Δ ρ : ℕ → ℝ} {N : ℕ}
    (h : Run f P x s d j Δ ρ N) (hN : 0 < N) {L : ℝ} (hL : 1 ≤ L) :
    positiveRadiusConstant f q P.order_pos (x 0) (Δ 0) P.theta P.eta2 P.gamma1 L ≤
      radiusConstant f q P.order_pos (x 0) (Δ 0) P.theta P.eta2 P.gamma1 L := by
  have hB := h.initialDerivativeBound_pos hN
  have hδ := (h.trials 0 hN).optimalityRadius_pos
  have hden : 0 < 2 * (q.factorial : ℝ) * initialDerivativeBound f q P.order_pos (x
    0) := by positivity
  have hratio := div_le_div_of_nonneg_left
    (mul_nonneg h.initial_radius_pos.le (pow_nonneg hδ.le q)) hden
    (mul_le_mul_of_nonneg_left (le_max_right 1 _) (by positivity : (0 : ℝ) ≤ 2 * q.factorial))
  have hc : 0 ≤ P.gamma1 * (1 - P.eta2) / L :=
    div_nonneg (mul_nonneg P.gamma1_pos.le (by linarith [P.eta2_lt_one])) (by linarith)
  exact mul_le_mul_of_nonneg_left (min_le_min_left P.theta hratio) hc

/-- The fixed inverse objective-decrease coefficient, as in (12.2.22). -/
noncomputable def successfulConstant (q : ℕ) (eta1 zeta κ : ℝ) : ℝ :=
  q.factorial / (eta1 * (zeta * κ) ^ (q + 1))

/-- The fixed logarithmic multiplicative factor for successful trials. -/
noncomputable def iterationFactor (gamma2 gamma3 : ℝ) : ℝ :=
  1 + Real.log gamma3 / |Real.log gamma2|

/-- Objective calls comprise initialization and one actual evaluation for each trial. -/
def functionEvaluations (N : ℕ) : ℕ := N + 1

/-- Each derivative order is evaluated initially and at each accepted new iterate.
The same bound applies to the whole collection of derivatives through order `q`. -/
noncomputable def derivativeEvaluations {q : ℕ} (P : Parameters q) (ρ : ℕ → ℝ) (N : ℕ) : ℕ :=
  (successfulIterations {i | P.eta1 ≤ ρ i} N).card + 1

/-- The terminal Step 1 computation: every computed direction is feasible and attains
the required fraction of the actual Taylor criticality measure. -/
def CheckedOracle {q : ℕ} (f : E → ℝ) (P : Parameters q) (x : E) (Δ : ℝ)
    (d : Fin q → E) : Prop :=
  ∀ a, ‖d a‖ ≤ optimalityRadius P Δ ∧
    P.zeta * TaylorModel.criticality f (modelOrder a) x (optimalityRadius P Δ) ≤
      TaylorModel.decrement f (modelOrder a) x (d a)

/-- The actual computed stopping tests in Step 1 of Algorithm 12.2.1. -/
def TestsPass {q : ℕ} (f : E → ℝ) (P : Parameters q) (x : E) (Δ : ℝ)
    (d : Fin q → E) : Prop :=
  ∀ a, TaylorModel.decrement f (modelOrder a) x (d a) ≤
    P.zeta * P.accuracy a * optimalityRadius P Δ ^ modelOrder a / (modelOrder a).factorial

/-- The checked model approximation and passed computed tests imply the genuine
per-order criticality bounds; the approximation statement is not the stopping conclusion. -/
theorem criticality_le_of_testsPass {q : ℕ} {f : E → ℝ} {P : Parameters q}
    {x : E} {Δ : ℝ} {d : Fin q → E} (hc : CheckedOracle f P x Δ d)
    (ht : TestsPass f P x Δ d) (a : Fin q) :
    TaylorModel.criticality f (modelOrder a) x (optimalityRadius P Δ) ≤
      P.accuracy a * optimalityRadius P Δ ^ modelOrder a / (modelOrder a).factorial := by
  have hh := (hc a).2.trans (ht a)
  have he : P.zeta * P.accuracy a * optimalityRadius P Δ ^ modelOrder a /
      (modelOrder a).factorial = P.zeta *
      (P.accuracy a * optimalityRadius P Δ ^ modelOrder a / (modelOrder a).factorial) := by ring
  rw [he] at hh
  exact (mul_le_mul_iff_of_pos_left P.zeta_pos).mp hh

/-- The largest reciprocal accuracy power across all requested derivative orders. -/
noncomputable def maximumInverseAccuracy {q : ℕ} (P : Parameters q) (p : ℕ) : ℝ :=
  Finset.univ.sup' ⟨⟨0,P.order_pos⟩, Finset.mem_univ _⟩ (fun a : Fin q => 1 / P.accuracy a ^ p)

/-- The reciprocal minimum-accuracy power is exactly the largest per-order reciprocal power. -/
theorem inverse_minimumAccuracy_pow {q : ℕ} (P : Parameters q) (p : ℕ) :
    1 / minimumAccuracy P ^ p = maximumInverseAccuracy P p := by
  have hm := minimumAccuracy_pos P
  apply le_antisymm
  · obtain ⟨a,_,ha⟩ := Finset.exists_mem_eq_inf'
      (show (Finset.univ : Finset (Fin q)).Nonempty from ⟨⟨0,P.order_pos⟩,
        Finset.mem_univ _⟩) P.accuracy
    have heq : minimumAccuracy P = P.accuracy a := ha
    rw [heq]
    exact Finset.le_sup' (fun b : Fin q => (1 : ℝ) / P.accuracy b ^ p) (Finset.mem_univ a)
  · apply Finset.sup'_le _ _
    intro a _
    exact one_div_le_one_div_of_le (pow_pos hm p)
      (pow_le_pow_left₀ hm.le (minimumAccuracy_le P a) p)

/-- The logarithmic accuracy term is bounded by every positive inverse accuracy power. -/
theorem abs_log_minimumAccuracy_le {q : ℕ} (P : Parameters q) {p : ℕ} (hp : 1 ≤ p) :
    |Real.log (minimumAccuracy P)| ≤ 1 / minimumAccuracy P ^ p := by
  have hm := minimumAccuracy_pos P
  have hm1 : minimumAccuracy P ≤ 1 := (minimumAccuracy_le_theta P).trans P.theta_le_one
  rw [abs_of_nonpos (Real.log_nonpos hm.le hm1)]
  have hl := Real.one_sub_inv_le_log_of_pos hm
  have hh : -Real.log (minimumAccuracy P) ≤ 1 / minimumAccuracy P := by
    rw [one_div]
    linarith
  have hpow : minimumAccuracy P ^ p ≤ minimumAccuracy P := by
    simpa using pow_le_pow_of_le_one hm.le hm1 hp
  exact hh.trans (one_div_le_one_div_of_le (pow_pos hm p) hpow)

/-- An explicit power-plus-log evaluation budget is bounded by a constant times the
maximum reciprocal accuracy power. This is a uniform form of the source big-O claim. -/
theorem budget_le_maximumInverseAccuracy {q : ℕ} (P : Parameters q) {p : ℕ} (hp : 1 ≤ p)
    {v A B C gap : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (h : v ≤ A * gap / minimumAccuracy P ^ p + B * |Real.log (minimumAccuracy P)| + C) :
    v ≤ (A * gap + B + C) * maximumInverseAccuracy P p := by
  have hm := minimumAccuracy_pos P
  have hm1 : minimumAccuracy P ≤ 1 := (minimumAccuracy_le_theta P).trans P.theta_le_one
  have hpow : minimumAccuracy P ^ p ≤ 1 := pow_le_one₀ hm.le hm1
  have hi : 1 ≤ 1 / minimumAccuracy P ^ p :=
    (le_div_iff₀ (pow_pos hm p)).2 (by simpa using hpow)
  have hlog := mul_le_mul_of_nonneg_left (abs_log_minimumAccuracy_le P hp) hB
  have hc : C ≤ C * (1 / minimumAccuracy P ^ p) :=
    le_mul_of_one_le_right hC hi
  apply h.trans
  rw [← inverse_minimumAccuracy_pow]
  ring_nf at hlog hc ⊢
  linarith

namespace Run
variable {q : ℕ} {f : E → ℝ} {P : Parameters q} {x s : ℕ → E}
  {d : ℕ → Fin q → E} {j : ℕ → Fin q} {Δ ρ : ℕ → ℝ} {N : ℕ}

/-- The positive coefficient gives the same guaranteed model reduction, also on the
last actual trial whose endpoint may satisfy the stopping test. -/
theorem positive_model_decrease (h : Run f P x s d j Δ ρ N) (hf : ContDiff ℝ q f)
    {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ (a : Fin q) y z, ‖iteratedFDeriv ℝ (modelOrder a) f y -
      iteratedFDeriv ℝ (modelOrder a) f z‖ ≤ L * ‖y - z‖)
    {k : ℕ} (hk : k < N) :
    (P.zeta * positiveRadiusConstant f q P.order_pos (x 0) (Δ 0) P.theta P.eta2
      P.gamma1 L) ^ (q + 1) /
      q.factorial * minimumAccuracy P ^ (q + 1) ≤
        TaylorModel.decrement f (modelOrder (j k)) (x k) (s k) := by
  have hc := h.model_decrease hf hL hlip hk
  apply le_trans _ hc
  have hp := (positiveRadiusConstant_properties f P (x 0) h.initial_radius_pos hL).1
  have hκ := positiveRadiusConstant_le h (by omega) hL
  have hε := minimumAccuracy_pos P
  have hζ := P.zeta_pos
  gcongr

/-- Every accepted trial attains the positive fixed objective-decrease coefficient. -/
theorem positive_function_decrease (h : Run f P x s d j Δ ρ N) (hf : ContDiff ℝ q f)
    {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ (a : Fin q) y z, ‖iteratedFDeriv ℝ (modelOrder a) f y -
      iteratedFDeriv ℝ (modelOrder a) f z‖ ≤ L * ‖y - z‖)
    {k : ℕ} (hk : k < N) (hs : P.eta1 ≤ ρ k) :
    P.eta1 * (P.zeta * positiveRadiusConstant f q P.order_pos (x 0) (Δ 0) P.theta
      P.eta2 P.gamma1 L) ^ (q + 1) /
      q.factorial * minimumAccuracy P ^ (q + 1) ≤ f (x k) - f (x (k + 1)) := by
  have ht := h.trials k hk
  have hd := mul_le_mul_of_nonneg_left (h.positive_model_decrease hf hL hlip hk) P.eta1_pos.le
  have ha := (le_div_iff₀ ht.denominator_pos).1 (ht.ratio ▸ hs)
  rw [ht.point_update, ite_eq_left hs]
  convert hd.trans ha using 1
  ring

/-- The uniform positive radius floor includes the terminal endpoint and uses only
preceding actual failed tests. It requires no failed stopping test at the endpoint. -/
theorem endpoint_radius_floor (h : Run f P x s d j Δ ρ N) (hf : ContDiff ℝ q f)
    {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ (a : Fin q) y z, ‖iteratedFDeriv ℝ (modelOrder a) f y -
      iteratedFDeriv ℝ (modelOrder a) f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i ≤ N) :
    P.zeta * positiveRadiusConstant f q P.order_pos (x 0) (Δ 0) P.theta P.eta2 P.gamma1 L *
      minimumAccuracy P ≤ Δ i := by
  let κ := positiveRadiusConstant f q P.order_pos (x 0) (Δ 0) P.theta P.eta2 P.gamma1 L
  let ε := minimumAccuracy P
  let c := (1 - P.eta2) / L
  have hp := positiveRadiusConstant_properties f P (x 0) h.initial_radius_pos hL
  have hκ0 : 0 < κ := hp.1
  have hκΔ : κ ≤ Δ 0 := hp.2.1
  have hκγ : κ < P.gamma1 := hp.2.2.1
  have hκc : κ ≤ P.gamma1 * c := hp.2.2.2.trans_eq (by dsimp [c]; ring)
  have hε : 0 < ε := minimumAccuracy_pos P
  have hεθ : ε ≤ P.theta := minimumAccuracy_le_theta P
  have hε1 : ε ≤ 1 := hεθ.trans P.theta_le_one
  have hc : 0 < c := div_pos (by linarith [P.eta2_lt_one]) (by linarith)
  have hζε : 0 < P.zeta * ε := mul_pos P.zeta_pos hε
  have hζε1 : P.zeta * ε ≤ 1 :=
    (mul_le_of_le_one_left hε.le P.zeta_le_one).trans hε1
  have hinit : P.zeta * κ * ε ≤ Δ 0 := by
    calc
      _ = κ * (P.zeta * ε) := by ring
      _ ≤ κ := mul_le_of_le_one_right hκ0.le hζε1
      _ ≤ _ := hκΔ
  have hstep : P.zeta * κ * ε ≤ P.gamma1 * min P.theta (c * (P.zeta * ε)) := by
    by_cases hs : P.theta ≤ c * (P.zeta * ε)
    · rw [min_eq_left hs]
      have hζεθ : P.zeta * ε ≤ P.theta :=
        (mul_le_of_le_one_left hε.le P.zeta_le_one).trans hεθ
      nlinarith [mul_le_mul hκγ.le hζεθ hζε.le P.gamma1_pos.le]
    · rw [min_eq_right (le_of_not_ge hs)]
      nlinarith [mul_le_mul_of_nonneg_right hκc hζε.le]
  apply (le_min hinit hstep).trans
  apply h.min_initial_threshold_le _ hi
  intro k hk hsmall
  have ht := h.trials k hk
  apply (ht.very_successful hf (by linarith) (hlip (j k)) _).1
  apply le_min
  · exact hsmall.le.trans (min_le_left _ _)
  · calc
      Δ k ≤ c * (P.zeta * ε) := hsmall.le.trans (min_le_right _ _)
      _ ≤ c * scaledGap f P (x k) (Δ k) (d k) (j k) :=
        mul_le_mul_of_nonneg_left
          ((mul_le_mul_of_nonneg_left (minimumAccuracy_le P (j k)) P.zeta_pos.le).trans
            (h.scaledGap_ge hk)) hc.le

/-- Unsuccessful actual trials preserve their current objective. -/
theorem objective_eq_of_unsuccessful (h : Run f P x s d j Δ ρ N)
    {i : ℕ} (hi : i < N) (hu : ¬P.eta1 ≤ ρ i) : f (x (i + 1)) = f (x i) := by
  rw [(h.trials i hi).point_update, ite_eq_right hu]

/-- The number of accepted trials is bounded by the available objective gap, with
no exceptional final accepted trial needed for a current-point Taylor stopping test. -/
theorem successful_card_le (h : Run f P x s d j Δ ρ N) (hf : ContDiff ℝ q f)
    {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ (a : Fin q) y z, ‖iteratedFDeriv ℝ (modelOrder a) f y -
      iteratedFDeriv ℝ (modelOrder a) f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ y, flow ≤ f y) :
    ((successfulIterations {i | P.eta1 ≤ ρ i} N).card : ℝ) ≤
      successfulConstant q P.eta1 P.zeta
        (positiveRadiusConstant f q P.order_pos (x 0) (Δ 0) P.theta P.eta2 P.gamma1 L) *
          (f (x 0) - flow) / minimumAccuracy P ^ (q + 1) := by
  have hκ := (positiveRadiusConstant_properties f P (x 0) h.initial_radius_pos hL).1
  have hε := minimumAccuracy_pos P
  have hζ := P.zeta_pos
  have hη := P.eta1_pos
  have hd : 0 < P.eta1 *
      (P.zeta * positiveRadiusConstant f q P.order_pos (x 0) (Δ 0) P.theta P.eta2
        P.gamma1 L) ^ (q + 1) /
        q.factorial * minimumAccuracy P ^ (q + 1) := by positivity
  have hb := card_successful_le_gap_div (S := {i | P.eta1 ≤ ρ i})
    (f := fun i => f (x i)) hd (hlow (x N))
    (fun i hi hs => h.positive_function_decrease hf hL hlip hi hs)
    (fun i hi hu => (h.objective_eq_of_unsuccessful hi hu).le)
  convert hb using 1
  unfold successfulConstant
  field_simp

/-- The three-case capped update bounds the radius enlargement at every accepted trial. -/
theorem successful_radius_le (h : Run f P x s d j Δ ρ N) {i : ℕ} (hi : i < N)
    (hs : P.eta1 ≤ ρ i) : Δ (i + 1) ≤ P.gamma3 * Δ i := by
  have ht := h.trials i hi
  have hu := ht.radius_update
  split_ifs at hu with hvery
  · exact hu.2.trans (min_le_right _ _)
  · exact hu.2.trans (le_mul_of_one_le_left ht.radius_pos.le P.one_le_gamma3)

/-- Unsuccessful actual trials contract the radius by at least `γ₂`. -/
theorem unsuccessful_radius_le (h : Run f P x s d j Δ ρ N) {i : ℕ} (hi : i < N)
    (hu : ¬P.eta1 ≤ ρ i) : Δ (i + 1) ≤ P.gamma2 * Δ i := by
  have hv : ¬P.eta2 ≤ ρ i := fun hh => hu (P.eta1_le_eta2.trans hh)
  have ht := (h.trials i hi).radius_update
  rw [ite_eq_right hv, ite_eq_right hu] at ht
  exact ht.2

/-- The full objective budget and actual update mechanism bound all trial iterations.
The endpoint radius floor avoids requiring a failed terminal stopping test. -/
theorem iterations_le (h : Run f P x s d j Δ ρ N) (hf : ContDiff ℝ q f)
    {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ (a : Fin q) y z, ‖iteratedFDeriv ℝ (modelOrder a) f y -
      iteratedFDeriv ℝ (modelOrder a) f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ y, flow ≤ f y) :
    let κ := positiveRadiusConstant f q P.order_pos (x 0) (Δ 0) P.theta P.eta2 P.gamma1 L
    (N : ℝ) ≤ successfulConstant q P.eta1 P.zeta κ * iterationFactor P.gamma2 P.gamma3 *
      (f (x 0) - flow) / minimumAccuracy P ^ (q + 1) +
      |Real.log (minimumAccuracy P)| / |Real.log P.gamma2| +
      |Real.log (P.zeta * κ / Δ 0)| / |Real.log P.gamma2| := by
  let κ := positiveRadiusConstant f q P.order_pos (x 0) (Δ 0) P.theta P.eta2 P.gamma1 L
  let ε := minimumAccuracy P
  have hκ : 0 < κ := (positiveRadiusConstant_properties f P (x 0) h.initial_radius_pos hL).1
  have hε : 0 < ε := minimumAccuracy_pos P
  have hb : 0 < P.zeta * κ * ε := mul_pos (mul_pos P.zeta_pos hκ) hε
  have hγ2 : 0 < P.gamma2 := P.gamma1_pos.trans_le P.gamma1_le_gamma2
  have hγ3 : 0 < P.gamma3 := zero_lt_one.trans_le P.one_le_gamma3
  have hD : 0 < |Real.log P.gamma2| := abs_pos.mpr (Real.log_neg hγ2 P.gamma2_lt_one).ne
  have hlog3 : 0 ≤ Real.log P.gamma3 := Real.log_nonneg P.one_le_gamma3
  have hA : 0 ≤ iterationFactor P.gamma2 P.gamma3 := by unfold iterationFactor; positivity
  have hn := iteration_bound_of_parameter_lower (S := {i | P.eta1 ≤ ρ i})
    (δ := Δ) (γs := P.gamma3) (γu := P.gamma2) (δmin := P.zeta * κ * ε)
    (fun i hi => hb.trans_le (h.endpoint_radius_floor hf hL hlip hi)) hγ3 hγ2 P.gamma2_lt_one
    (h.endpoint_radius_floor hf hL hlip le_rfl) hb
    (fun i hi hs => h.successful_radius_le hi hs) (fun i hi hu => h.unsuccessful_radius_le hi hu)
  have hratio : (P.zeta * κ * ε / Δ 0) = (P.zeta * κ / Δ 0) * ε := by ring
  have hlog : |Real.log (P.zeta * κ * ε / Δ 0)| ≤
      |Real.log (P.zeta * κ / Δ 0)| + |Real.log ε| := by
    rw [hratio, Real.log_mul (div_ne_zero (mul_ne_zero P.zeta_pos.ne' hκ.ne')
      h.initial_radius_pos.ne') hε.ne']
    exact abs_add_le _ _
  have hcard := mul_le_mul_of_nonneg_right (h.successful_card_le hf hL hlip hlow) hA
  have hlogs := div_le_div_of_nonneg_right hlog hD.le
  exact hn.trans ((add_le_add hcard hlogs).trans_eq (by dsimp [κ, ε, iterationFactor]; ring))

/-- Function evaluation count, including the initial objective call. -/
theorem functionEvaluations_le (h : Run f P x s d j Δ ρ N) (hf : ContDiff ℝ q f)
    {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ (a : Fin q) y z, ‖iteratedFDeriv ℝ (modelOrder a) f y -
      iteratedFDeriv ℝ (modelOrder a) f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ y, flow ≤ f y) :
    let κ := positiveRadiusConstant f q P.order_pos (x 0) (Δ 0) P.theta P.eta2 P.gamma1 L
    (functionEvaluations N : ℝ) ≤
      successfulConstant q P.eta1 P.zeta κ * iterationFactor P.gamma2 P.gamma3 *
        (f (x 0) - flow) / minimumAccuracy P ^ (q + 1) +
      |Real.log (minimumAccuracy P)| / |Real.log P.gamma2| +
      (|Real.log (P.zeta * κ / Δ 0)| / |Real.log P.gamma2| + 1) := by
  have hh := h.iterations_le hf hL hlip hlow
  simp only [functionEvaluations, Nat.cast_add, Nat.cast_one]
  linarith

/-- Each derivative order is evaluated only at initialization and accepted new iterates. -/
theorem derivativeEvaluations_le (h : Run f P x s d j Δ ρ N) (hf : ContDiff ℝ q f)
    {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ (a : Fin q) y z, ‖iteratedFDeriv ℝ (modelOrder a) f y -
      iteratedFDeriv ℝ (modelOrder a) f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ y, flow ≤ f y) :
    (derivativeEvaluations P ρ N : ℝ) ≤
      successfulConstant q P.eta1 P.zeta
        (positiveRadiusConstant f q P.order_pos (x 0) (Δ 0) P.theta P.eta2 P.gamma1 L) *
          (f (x 0) - flow) / minimumAccuracy P ^ (q + 1) + 1 := by
  have hh := h.successful_card_le hf hL hlip hlow
  simp only [derivativeEvaluations, Nat.cast_add, Nat.cast_one]
  linarith

end Run

/-- A consistent execution of the actual trial rules has a first passed stopping test.
Termination is derived from a uniform finite objective and radius budget. -/
theorem exists_termination {q : ℕ} {f : E → ℝ} {P : Parameters q}
    {x s : ℕ → E} {d : ℕ → Fin q → E} {j : ℕ → Fin q} {Δ ρ : ℕ → ℝ}
    (hprefix : ∀ N, (∀ i < N, ¬TestsPass f P (x i) (Δ i) (d i)) → Run f P x s d j Δ ρ N)
    (hf : ContDiff ℝ q f) {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ (a : Fin q) y z, ‖iteratedFDeriv ℝ (modelOrder a) f y -
      iteratedFDeriv ℝ (modelOrder a) f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ y, flow ≤ f y) :
    ∃ K, TestsPass f P (x K) (Δ K) (d K) ∧ Run f P x s d j Δ ρ K ∧
      ∀ i < K, ¬TestsPass f P (x i) (Δ i) (d i) := by
  classical
  have hex : ∃ K, TestsPass f P (x K) (Δ K) (d K) := by
    by_contra hn
    push Not at hn
    let κ := positiveRadiusConstant f q P.order_pos (x 0) (Δ 0) P.theta P.eta2 P.gamma1 L
    let bound := successfulConstant q P.eta1 P.zeta κ * iterationFactor P.gamma2 P.gamma3 *
      (f (x 0) - flow) / minimumAccuracy P ^ (q + 1) +
      |Real.log (minimumAccuracy P)| / |Real.log P.gamma2| +
      (|Real.log (P.zeta * κ / Δ 0)| / |Real.log P.gamma2| + 1)
    obtain ⟨N,hN⟩ := exists_nat_gt bound
    have hb := (hprefix N (fun i _ => hn i)).functionEvaluations_le hf hL hlip hlow
    have hNN : (N : ℝ) ≤ functionEvaluations N := by simp [functionEvaluations]
    exact (not_le_of_gt hN) (hNN.trans hb)
  refine ⟨Nat.find hex, Nat.find_spec hex, hprefix _ ?_, ?_⟩
  · intro i hi
    exact Nat.find_min hex hi
  · intro i hi
    exact Nat.find_min hex hi

/-- Uniform arbitrary-order evaluation complexity. Fixed positive constants are chosen
before every admissible accuracy request and every consistent execution from the same
initial data. The first passed computed test produces the genuine per-order Taylor
criticality bounds, and both counters include initialization. -/
theorem evaluation_complexity {q : ℕ} (f : E → ℝ) (S : Settings q) (x₀ : E)
    {Δ₀ : ℝ} (hΔ : 0 < Δ₀) (_hΔmax : Δ₀ ≤ S.radiusMax)
    (hf : ContDiff ℝ q f) (L : Fin q → ℝ) (hL : ∀ a, 1 ≤ L a)
    (hlip : ∀ (a : Fin q) y z, ‖iteratedFDeriv ℝ (modelOrder a) f y -
      iteratedFDeriv ℝ (modelOrder a) f z‖ ≤ L a * ‖y - z‖)
    {flow : ℝ} (hlow : ∀ y, flow ≤ f y) :
    ∃ κS > 0, ∃ κA > 0, ∃ κB > 0, ∃ κC > 0,
      ∀ (ε : Fin q → ℝ) (hε : ∀ a, 0 < ε a) (hε1 : ∀ a, ε a ≤ 1)
        (hεθ : ∃ a, ε a ≤ S.theta),
      let P := S.withAccuracy ε hε hε1 hεθ
      ∀ (x s : ℕ → E) (d : ℕ → Fin q → E) (j : ℕ → Fin q) (Δ ρ : ℕ → ℝ),
      x 0 = x₀ → Δ 0 = Δ₀ →
      (∀ N, (∀ i < N, ¬TestsPass f P (x i) (Δ i) (d i)) → Run f P x s d j Δ ρ N) →
      (∀ k, TestsPass f P (x k) (Δ k) (d k) → CheckedOracle f P (x k) (Δ k) (d k)) →
      ∃ K, TestsPass f P (x K) (Δ K) (d K) ∧ Run f P x s d j Δ ρ K ∧
        (∀ i < K, ¬TestsPass f P (x i) (Δ i) (d i)) ∧
        optimalityRadius P (Δ K) ∈ Ioc (0 : ℝ) 1 ∧
        (∀ a, TaylorModel.criticality f (modelOrder a) (x K) (optimalityRadius P (Δ K)) ≤
          ε a * optimalityRadius P (Δ K) ^ modelOrder a / (modelOrder a).factorial) ∧
        (functionEvaluations K : ℝ) ≤ κA * (f x₀ - flow) / minimumAccuracy P ^ (q + 1) +
          κB * |Real.log (minimumAccuracy P)| + κC ∧
        (derivativeEvaluations P ρ K : ℝ) ≤
          κS * (f x₀ - flow) / minimumAccuracy P ^ (q + 1) + 1 ∧
        (functionEvaluations K : ℝ) ≤
          (κA * (f x₀ - flow) + κB + κC) * maximumInverseAccuracy P (q + 1) ∧
        (derivativeEvaluations P ρ K : ℝ) ≤
          (κS * (f x₀ - flow) + 1) * maximumInverseAccuracy P (q + 1) := by
  let P₀ := S.defaultParameters
  let Lf := maxLipschitzConstant P₀ L
  have hLf : 1 ≤ Lf := (hL ⟨0,S.order_pos⟩).trans (le_maxLipschitzConstant P₀ L _)
  have hcommon : ∀ (a : Fin q) y z, ‖iteratedFDeriv ℝ (modelOrder a) f y -
      iteratedFDeriv ℝ (modelOrder a) f z‖ ≤ Lf * ‖y - z‖ := by
    intro a y z
    exact (hlip a y z).trans (mul_le_mul_of_nonneg_right (le_maxLipschitzConstant P₀
      L a) (norm_nonneg _))
  let κ := positiveRadiusConstant f q S.order_pos x₀ Δ₀ S.theta S.eta2 S.gamma1 Lf
  have hp := positiveRadiusConstant_properties f P₀ x₀ hΔ hLf
  have hκ : 0 < κ := hp.1
  have hγ2 : 0 < S.gamma2 := S.gamma1_pos.trans_le S.gamma1_le_gamma2
  have hD : 0 < |Real.log S.gamma2| := abs_pos.mpr (Real.log_neg hγ2 S.gamma2_lt_one).ne
  have hlog3 : 0 ≤ Real.log S.gamma3 := Real.log_nonneg S.one_le_gamma3
  have hA : 0 < iterationFactor S.gamma2 S.gamma3 := by unfold iterationFactor; positivity
  let κS := successfulConstant q S.eta1 S.zeta κ
  have hS : 0 < κS := div_pos (by positivity) (mul_pos S.eta1_pos (pow_pos (mul_pos
    S.zeta_pos hκ) _))
  refine ⟨κS, hS, κS * iterationFactor S.gamma2 S.gamma3, mul_pos hS hA,
    1 / |Real.log S.gamma2|, div_pos zero_lt_one hD,
    |Real.log (S.zeta * κ / Δ₀)| / |Real.log S.gamma2| + 1, by positivity, ?_⟩
  intro ε hε hε1 hεθ
  let P := S.withAccuracy ε hε hε1 hεθ
  dsimp only
  intro x s d j Δ ρ hx hΔeq hprefix hchecked
  obtain ⟨K,hstop,hK,hfirst⟩ := exists_termination hprefix hf hLf hcommon hlow
  have hκseq := (positiveRadiusConstant_properties f P (x 0) hK.initial_radius_pos hLf).1
  have hfloor := hK.endpoint_radius_floor hf hLf hcommon (i := K) le_rfl
  have hδK : 0 < Δ K :=
    (mul_pos (mul_pos P.zeta_pos hκseq) (minimumAccuracy_pos P)).trans_le hfloor
  have hδ : 0 < optimalityRadius P (Δ K) := lt_min hδK P.theta_pos
  have hF : (functionEvaluations K : ℝ) ≤
      κS * iterationFactor S.gamma2 S.gamma3 * (f x₀ - flow) / minimumAccuracy P ^ (q + 1) +
      (1 / |Real.log S.gamma2|) * |Real.log (minimumAccuracy P)| +
      (|Real.log (S.zeta * κ / Δ₀)| / |Real.log S.gamma2| + 1) := by
    have hb := hK.functionEvaluations_le hf hLf hcommon hlow
    rw [hx,hΔeq] at hb
    convert hb using 1
    dsimp [κS, κ, P, Settings.withAccuracy]
    ring
  have hDer : (derivativeEvaluations P ρ K : ℝ) ≤
      κS * (f x₀ - flow) / minimumAccuracy P ^ (q + 1) + 1 := by
    have hb := hK.derivativeEvaluations_le hf hLf hcommon hlow
    rw [hx,hΔeq] at hb
    exact hb
  refine ⟨K,hstop,hK,hfirst,⟨hδ,(optimalityRadius_le_theta P _).trans P.theta_le_one⟩,
    fun a => criticality_le_of_testsPass (hchecked K hstop) hstop a, hF, hDer, ?_, ?_⟩
  · exact budget_le_maximumInverseAccuracy P (by omega) (by positivity) (by positivity) hF
  · have hh := budget_le_maximumInverseAccuracy P (p := q + 1) (A := κS)
      (B := 0) (C := 1) (gap := f x₀ - flow) (by omega) (by norm_num) (by norm_num)
      (by simpa using hDer)
    simpa using hh

end HighOrderTrustRegion

import Numlib.Algebra.Order.Archimedean
import Numlib.Analysis.InnerProductSpace.PiL2
import Numlib.Data.Nat.SeqAppend
import Numlib.Optimization.Complexity.SlowExample.Basic
import Numlib.Optimization.Complexity.SlowExample.DynamicAccuracy
import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.ARqpEDA
import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.ARqpIDAExistence

/-!
# Slow runs of the dynamic-accuracy regularization methods

The slow regularization examples of [cartis2022evaluation], Theorems 12.2.15 and 12.2.17, lifted
to `ℝ¹` along the coordinate direction `e₁` (ridges `x ↦ g ⟪e₁, x⟫`), give runs of the
dynamic-accuracy regularization methods ARqpIDA and ARqpEDA ([cartis2022evaluation],
Algorithms 13.1.2 and 13.3.2, `Optimization.IsARqpIDARun`, `Optimization.IsARqpEDARun`) with exact
derivatives (and values) whose first approximately optimal iterate is `x_{k_ε}`, for each mode of
the radii control (`Optimization.ARqpDARadiiControl`). The class constants (`f_low`, the Lipschitz
constant `L`, the bound `ε₀` on `ε`) do not depend on `ε`.

The runs are built as follows.

* **Unit radii** (`q ≤ 2`, the example of Theorem 12.2.15, `σ₀ = p!/(q-1)!`, unit initial radii,
  `k_ε = ⌈ε^{-(p+1)/(p-q+1)}⌉`). The Step-1 radius of order `q` is the dyadic radius `2^{-m}` at
  the scale of the step: the model-decrease condition (13.1.54) holds at it and fails at twice it,
  so the halving loop of Step 1 stops there. This needs `ε ≤ ε₀(p, q)`.
* **Lower bounds, ARqpEDA** (the example of Theorem 12.2.17 with `r = p`, radii `ε`,
  `k_ε = ⌈ε^{-q(p+1)/p}⌉`). The weight is `σ₀ = (3/(p+2))^p/2`, and the Step-1 displacements
  achieve exactly the fraction `ς` of the measures.
* **Lower bounds, ARqpIDA, `q = p ≥ 3`** (pure `p`-th order spikes, `σ₀ = p`, initial radii `ε`,
  `k_ε = ⌈ε^{-(p+1)}⌉`). The Step-2 radii are `ε/p`, at which the model measures at the step
  vanish.

ARqpEDA is run on `f/2` so that it terminates at `k_ε`. ARqpIDA has no termination rule; after
`k_ε` its run continues by ARqpIDA iterations from the state at `k_ε`
(`Optimization.exists_arqpDA_steps`), spliced with `Optimization.ARqpDAStep.seqAppend`. The initial
accuracies are assumed to pass the accuracy test (13.1.46) along the steps and, for ARqpEDA, the
termination test (13.3.17).

## Main results

* `Optimization.exists_isARqpIDARun_slow`, `Optimization.exists_isARqpEDARun_slow`: unit-radii
  runs with `k_ε = ⌈ε^{-(p+1)/(p-q+1)}⌉`, `q ≤ 2`, satisfying both modes of the radii control;
* `Optimization.exists_isARqpEDARun_slowGrad`: an ARqpEDA run in the lower-bound mode with
  `k_ε = ⌈ε^{-q(p+1)/p}⌉`, for every `1 ≤ q ≤ p`;
* `Optimization.exists_isARqpIDARun_slowTop`: an ARqpIDA run in the lower-bound mode with
  `k_ε = ⌈ε^{-(p+1)}⌉`, for `q = p ≥ 3`.
-/

open Set Metric
open scoped Nat RealInnerProductSpace

namespace Optimization

open EuclideanSpace (norm_single_one inner_single_smul_self norm_smul_single
  norm_eq_abs_inner_single)

/-- The coordinate direction of `ℝ¹`. -/
local notation "e₀" => EuclideanSpace.single (0 : Fin 1) (1 : ℝ)

/-- **The slow regularization example on `ℝ¹`** (the data of [cartis2022evaluation],
Theorem 12.2.15, lifted along `e₁` and scaled by `λ ∈ (0, 1]`). For `1 ≤ q ≤ p` there are
`f_low` and `L ≥ 1` such that, for every `ε ∈ (0, 1]`, with `k_ε = ⌈ε^{-(p+1)/(p-q+1)}⌉`,
`a_k = λ (ε + ε (k_ε - k)/k_ε)` and points `x_{k+1} = x_k + a_k^{1/(p-q+1)}`, there is a `C^p`
function `g` of one variable whose ridge `f = g(⟪e₁, ·⟫)` is bounded below by `f_low` and has
`L`-Lipschitz derivatives of orders `0, …, p`, with spike jets `g^{(q)}(x_k) = -a_k` (other
derivatives of orders `1, …, p` zero) for `k ≤ k_ε` and
`g(x_{k+1}) = g(x_k) - a_k (x_{k+1} - x_k)^q/q!` for `k < k_ε`. -/
private theorem exists_slowARqp_ridge {p q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) {lam : ℝ}
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) :
    ∃ flow L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ xr : ℕ → ℝ,
      (∀ k < ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊, xr (k + 1) = xr k +
        (lam * (ε + ε * ((⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ : ℝ) - k) /
          ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊)) ^ (1 / ((p - q + 1 : ℕ) : ℝ))) →
      ∃ g : ℝ → ℝ, ContDiff ℝ p g ∧ (∀ y, flow ≤ ridge g e₀ y) ∧
        LipschitzDerivsAnchored (ridge g e₀) univ univ 0 p (fun _ => L) ∧
        (∀ k ≤ ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊, IsSpikeJetOf p g q (xr k)
          (lam * (ε + ε * ((⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ : ℝ) - k) /
            ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊))) ∧
        ∀ k < ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊, g (xr (k + 1)) = g (xr k) -
          lam * (ε + ε * ((⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ : ℝ) - k) /
            ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊) * (xr (k + 1) - xr k) ^ q / q ! := by
  obtain ⟨L, B, hL, hB, hG⟩ := exists_slowTaylorOrder_interpolant hq hqp hlam
  refine ⟨-B, max 1 (max L B), le_max_left _ _, fun ε hε hε1 xr hxr => ?_⟩
  obtain ⟨G, hGc, hGL, hGB, hGd, hGf⟩ := hG ε _ xr hε hε1 rfl hxr
  set g : ℝ → ℝ := fun t => lam * G t with hg
  obtain ⟨hfc, hfb, hfl⟩ := ridge_const_mul_slow_bounds (G := G) (lam := lam) (e := e₀) hGc hB
    hGL hGB hlam hlam1 (norm_single_one 0).le
  refine ⟨g, contDiff_const.mul hGc, hfb,
    .of_contDiff hfc (fun j hj => hfl j (Finset.mem_Icc.1 hj).2) univ,
    fun k hk => IsSpikeJetOf.const_mul (hGd k hk) lam, fun k hk => ?_⟩
  simp only [hg]
  rw [hGf k hk]; ring

/-- **The slow regularization run up to `k_ε`** (the example of [cartis2022evaluation],
Theorem 12.2.15 on `ℝ¹`, `f` scaled by `λ ∈ [½, 1]`, as a run of the ARqpIDA/ARqpEDA steps
with unit radii, `q ≤ 2`). There are `f_low`, `L ≥ 1` and `ε₀ ∈ (0, ¼]` such that for every
`ε ∈ (0, ε₀]` and constants with `σ₀ = p!/(q-1)!`, with `k_ε = ⌈ε^{-(p+1)/(p-q+1)}⌉`, some
`f ≥ f_low` with `L`-Lipschitz derivatives of orders `0, …, p`, iterates
`x_k` from `0`, radii `δ^{(1)}_k`, displacements `d_k`, steps `s_k` and levels `a_k` satisfy:
`a_k > λ ε` for `k < k_ε` and `a_{k_ε} = λ ε`; the measures at `x_k` (`k ≤ k_ε`) are `0` below
order `q` and `(a_k/q!) δ^q` at order `q`; the steps are short and their Taylor decrease is the
decrease of `f`; (13.1.53) fails at order `q` before `k_ε`; Step 1 at `k_ε` keeps the unit radii
with displacements achieving exactly the fraction `ς` of the measures; and for accuracies `h_k = h₀`
passing (13.1.46) along the steps (`h_{0,i} ≤ κ_s (ε/2)^{p-i+1}`), no accuracy-improving iteration
and ratios `ρ_k = 1` before `k_ε`, every iteration `k < k_ε` is an `ARqpDAStep` with `σ_k = σ₀`,
unit radii `δ_k = δ_{s_k} = 1`, `j_k = q` and exact Taylor data. -/
private theorem exists_slowARqp_run {p q : ℕ} (hq : 1 ≤ q) (hq2 : q ≤ 2) (hqp : q ≤ p)
    {lam : ℝ} (hlam : 1 / 2 ≤ lam) (hlam1 : lam ≤ 1) :
    ∃ flow L ε₀ : ℝ, 1 ≤ L ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 4 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ P : ARqpIDAParams, P.p = p → P.q = q → P.σ₀ = (p ! : ℝ) / (q - 1)! →
      (∀ j ∈ Finset.Icc 1 q, P.δ₀ j = 1) →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, (∀ y, flow ≤ f y) ∧
        LipschitzDerivsAnchored f univ univ 0 p (fun _ => L) ∧
        ∃ (X : ℕ → EuclideanSpace ℝ (Fin 1)) (δ₁ : ℕ → ℕ → ℝ)
          (dd : ℕ → ℕ → EuclideanSpace ℝ (Fin 1)) (s : ℕ → EuclideanSpace ℝ (Fin 1))
          (a : ℕ → ℝ), X 0 = 0 ∧
          (∀ k < ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊, lam * ε < a k) ∧
          a ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ = lam * ε ∧
          (∀ k ≤ ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊, ∀ j ∈ Finset.Icc 1 P.q,
            ∀ t : ℝ, 0 ≤ t → taylorMeasure (ftaylorSeries ℝ f (X k)) j t univ =
              (if j = P.q then a k / P.q ! else 0) * t ^ P.q) ∧
          (∀ k < ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊, X (k + 1) = X k + s k ∧
            ‖s k‖ < 1 ∧
            f (X k) - f (X k + s k) = (ftaylorSeries ℝ f (X k)).taylorDecrement P.p (s k) ∧
            0 < (ftaylorSeries ℝ f (X k)).taylorDecrement P.p (s k)) ∧
          (∀ k < ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊,
            ¬ arqpDAPass P (fun _ => ε) (fun i => ftaylorSeries ℝ f (X i)) δ₁ dd k P.q) ∧
          δ₁ ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ = (fun _ => 1) ∧
          (∀ j ∈ Finset.Icc 1 P.q,
            (ftaylorSeries ℝ f (X ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊)).taylorDecrement
              j (dd ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ j) =
            P.ς * (if j = P.q then a ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ / P.q !
              else 0)) ∧
          ARqpStep1 univ P (fun _ => ε) X (fun _ => P.σ₀) (fun _ => P.δ₀) δ₁
            (fun i => ftaylorSeries ℝ f (X i)) dd
            ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ ∧
          ∀ (h : ℕ → ℕ → ℝ) (acc : ℕ → Prop) (ρ : ℕ → ℝ),
            (∀ k ≤ ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊, h k = P.h₀) →
            (∀ i ∈ Finset.Icc 1 P.p, P.h₀ i ≤ P.κs * (ε / 2) ^ (P.p - i + 1)) →
            (∀ k < ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊, ¬ acc k) →
            (∀ k < ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊, ρ k = 1) →
            ∀ k < ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊,
            ARqpDAStep univ P (fun _ => ε) X (fun _ => P.σ₀) (fun _ => P.δ₀) δ₁ (fun _ => P.δ₀) h
              (fun i => ftaylorSeries ℝ f (X i)) dd (fun _ => P.q) s acc ρ k := by
  obtain ⟨flow, L, hL, H⟩ := exists_slowARqp_ridge hq hqp (by linarith : (0 : ℝ) < lam) hlam1
  have hR0 : p - q + 1 ≠ 0 := by omega
  have hRpos : (0 : ℝ) < ((p - q + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hR0
  have hK : (0 : ℝ) < (p ! : ℝ) / (q - 1)! * q ! / (p + 1)! := by positivity
  refine ⟨flow, L, min (1 / 4) ((p ! : ℝ) / (q - 1)! * q ! / (p + 1)! / 2 ^ (p - q + 1 + 1)),
    hL, by positivity, min_le_left _ _, fun ε hε hεε P hPp hPq hσ hδ₀ => ?_⟩
  subst hPp hPq
  have hε4 : ε ≤ 1 / 4 := hεε.trans (min_le_left _ _)
  have hεK : ε ≤ (P.p ! : ℝ) / (P.q - 1)! * P.q ! / (P.p + 1)! / 2 ^ (P.p - P.q + 1 + 1) :=
    hεε.trans (min_le_right _ _)
  obtain ⟨hκ1, -⟩ := one_le_ceil_rpow_neg_and_mul_le hε (by linarith)
    (le_of_lt (by positivity : (0 : ℝ) < (P.p + 1 : ℝ) / ((P.p - P.q + 1 : ℕ) : ℝ)))
  set κ := ⌈ε ^ (-((P.p + 1 : ℝ) / ((P.p - P.q + 1 : ℕ) : ℝ)))⌉₊ with hκ
  have hκpos : (0 : ℝ) < κ := by exact_mod_cast hκ1
  set R : ℕ := P.p - P.q + 1 with hR
  set K : ℝ := (P.p ! : ℝ) / (P.q - 1)! * P.q ! / (P.p + 1)! with hKdef
  -- the levels `a_k`, the step lengths `t_k` and the points
  set a : ℕ → ℝ := fun k => lam * (ε + ε * ((κ : ℝ) - k) / κ) with ha
  set t : ℕ → ℝ := fun k => a k ^ (1 / (R : ℝ)) with ht
  set xr : ℕ → ℝ := fun k => ∑ i ∈ Finset.range k, t i with hxr
  have hxr1 : ∀ k, xr (k + 1) = xr k + t k := fun k => Finset.sum_range_succ _ _
  obtain ⟨g, hgc, hb, hf, hspike, hval⟩ := H ε hε (by linarith) xr fun k _ => hxr1 k
  have ha_ge : ∀ k ≤ κ, lam * ε ≤ a k := fun k hk => by
    have := slowGap_nonneg hε.le hk; simp only [ha]; nlinarith
  have ha_gt : ∀ k < κ, lam * ε < a k := fun k hk => by
    have := slowGap_pos hε hk; simp only [ha]; nlinarith
  have ha_le : ∀ k ≤ κ, a k ≤ 2 * ε := fun k hk => by
    have := slowGap_le hε.le κ k; have := slowGap_nonneg hε.le hk; simp only [ha]; nlinarith
  have ha_eq : a κ = lam * ε := by simp only [ha]; rw [sub_self, mul_zero, zero_div, add_zero]
  have ha_pos : ∀ k ≤ κ, 0 < a k := fun k hk => by
    have := ha_ge k hk; nlinarith
  -- the step lengths
  have ht_ge : ∀ k ≤ κ, ε / 2 ≤ t k := fun k hk => by
    have h1 : a k ≤ a k ^ (1 / (R : ℝ)) := by
      conv_lhs => rw [← Real.rpow_one (a k)]
      exact Real.rpow_le_rpow_of_exponent_ge (ha_pos k hk) (by linarith [ha_le k hk])
        (by rw [div_le_one hRpos]; exact_mod_cast Nat.one_le_iff_ne_zero.2 hR0)
    simp only [ht]; nlinarith [ha_ge k hk]
  have ht_lt : ∀ k ≤ κ, t k < 1 := fun k hk =>
    Real.rpow_lt_one (ha_pos k hk).le (by linarith [ha_le k hk]) (by positivity)
  have ht_pos : ∀ k ≤ κ, 0 < t k := fun k hk => by linarith [ht_ge k hk]
  -- the function and its Taylor data
  set f : EuclideanSpace ℝ (Fin 1) → ℝ := ridge g e₀ with hfdef
  set X : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => xr k • e₀ with hX
  set s : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => t k • e₀ with hs
  have hXs : ∀ k, X (k + 1) = X k + s k := fun k => by
    simp only [hX, hs, hxr1, add_smul]
  have hspX : ∀ k ≤ κ, IsSpikeJetOf P.p g P.q ⟪e₀, X k⟫ (a k) := fun k hk => by
    rw [inner_single_smul_self]; exact hspike k hk
  have hspXq : ∀ k ≤ κ, IsSpikeJetOf P.q g P.q ⟪e₀, X k⟫ (a k) := fun k hk =>
    ⟨(hspX k hk).1, fun j h1 hj hne => (hspX k hk).2 j h1 (hj.trans P.q_le_p) hne⟩
  have hgp : ContDiff ℝ P.p g := hgc
  have hgq : ContDiff ℝ P.q g := hgp.of_le (by exact_mod_cast P.q_le_p)
  have hdec : ∀ k ≤ κ, ∀ j ≤ P.q, ∀ d, (ftaylorSeries ℝ f (X k)).taylorDecrement j d =
      (if j = P.q then a k / P.q ! else 0) * ⟪e₀, d⟫ ^ P.q := fun k hk j hj d => by
    rcases hj.lt_or_eq with hjq | rfl
    · rw [ite_eq_right hjq.ne, zero_mul]
      exact taylorDecrement_ridge_of_lt hgq hjq (hspXq k hk) d
    · rw [ite_eq_left rfl, taylorDecrement_ridge_spike hgq P.one_le_q le_rfl (hspXq k hk)]
      ring
  have hdecp : ∀ k ≤ κ, ∀ d, (ftaylorSeries ℝ f (X k)).taylorDecrement P.p d =
      a k / P.q ! * ⟪e₀, d⟫ ^ P.q := fun k hk d => by
    rw [taylorDecrement_ridge_spike hgp P.one_le_q P.q_le_p (hspX k hk)]
    ring
  have hmeas : ∀ k ≤ κ, ∀ j ∈ Finset.Icc 1 P.q, ∀ t' : ℝ, 0 ≤ t' →
      taylorMeasure (ftaylorSeries ℝ f (X k)) j t' univ =
        (if j = P.q then a k / P.q ! else 0) * t' ^ P.q := fun k hk j hj t' ht' =>
    slowARqp_taylorMeasure_eq (D := fun i => ftaylorSeries ℝ f (X i)) (norm_single_one 0)
      (ha_pos k hk).le (hdec k hk) (Finset.mem_Icc.1 hj).2 ht'
  have hσ0 : 0 < P.σ₀ := P.σ₀_pos
  -- the model minimizers
  have hlam1' : P.σ₀ * (P.q - 1)! / P.p ! = 1 := by rw [hσ]; field_simp
  have hmin : ∀ k ≤ κ, IsMinOn (regularizedModel (ftaylorSeries ℝ f (X k)) P.p P.σ₀) univ (s k) :=
    fun k hk => by
      obtain ⟨hm, -, -⟩ := isMinOn_neg_monomial_add_regularization P.one_le_q P.q_le_p hσ0
        (ha_pos k hk)
      rw [hlam1', div_one] at hm
      intro y _
      simp only [mem_ofPred_eq]
      rw [regularizedModel_ridge_spike norm_eq_abs_inner_single hgp P.one_le_q P.q_le_p (hspX k hk),
        ridge_apply, ridge_apply, show s k = t k • e₀ from rfl, inner_single_smul_self 0 (t k)]
      exact (add_le_add_iff_left _).2 (isMinOn_iff.1 hm _ (mem_univ _))
  have hnorm_s : ∀ k, ‖s k‖ = |t k| := fun k => norm_smul_single 0 _
  have hdecs : ∀ k ≤ κ, (ftaylorSeries ℝ f (X k)).taylorDecrement P.p (s k) =
      a k / P.q ! * t k ^ P.q := fun k hk => by rw [hdecp k hk, hs, inner_single_smul_self]
  have hfval : ∀ k < κ, f (X k) - f (X k + s k) =
      (ftaylorSeries ℝ f (X k)).taylorDecrement P.p (s k) := fun k hk => by
    rw [hdecs k hk.le, ← hXs, hfdef, ridge_apply, ridge_apply, hX, inner_single_smul_self,
        inner_single_smul_self,
      hval k hk, hxr1]
    ring
  -- the Step-1 radii `r_k` at which the halving loop stops
  set M : ℕ → ℝ := fun k => (a k - P.ς * ε / 4) / K with hM
  set r : ℕ → ℝ := fun k => M k ^ ((R : ℝ)⁻¹) with hr
  have hς := P.ς_pos
  have hς1 := P.ς_le_one
  have hM_pos : ∀ k < κ, 0 < M k := fun k hk => by
    have := ha_gt k hk
    have : P.ς * ε / 4 < a k := by nlinarith
    simp only [hM]; exact div_pos (by linarith) hK
  have hrR : ∀ k < κ, r k ^ R = M k := fun k hk => Real.rpow_inv_natCast_pow (hM_pos k hk).le hR0
  have hr_pos : ∀ k < κ, 0 < r k := fun k hk => Real.rpow_pos_of_pos (hM_pos k hk) _
  have hpow : ∀ y : ℝ, y ^ (P.p + 1) = y ^ P.q * y ^ R := fun y => by
    rw [← pow_add]; congr 1; omega
  have hKσ : K = P.σ₀ * P.q ! / (P.p + 1)! := by rw [hKdef, hσ]
  have h2r : ∀ k < κ, 2 * r k ≤ 1 := fun k hk => by
    have hle : (2 * r k) ^ R ≤ 1 := by
      rw [mul_pow, hrR k hk, hM]
      simp only
      have h1 : a k - P.ς * ε / 4 ≤ 2 * ε := by nlinarith [ha_le k hk.le]
      have h2 : 2 * ε ≤ 2 * (K / 2 ^ (R + 1)) := by linarith
      have h3 : (a k - P.ς * ε / 4) / K ≤ 2 * (K / 2 ^ (R + 1)) / K :=
        div_le_div_of_nonneg_right (h1.trans h2) hK.le
      have h4 : 2 * (K / 2 ^ (R + 1)) / K = 1 / 2 ^ R := by
        rw [pow_succ]; field_simp
      rw [h4] at h3
      calc (2 : ℝ) ^ R * ((a k - P.ς * ε / 4) / K) ≤ 2 ^ R * (1 / 2 ^ R) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = 1 := by field_simp
    exact (pow_le_one_iff_of_nonneg (by linarith [hr_pos k hk]) hR0).1 hle
  -- the dyadic radii `rd_k ∈ (r_k/2, r_k]` reached by halving from `1`
  have heq : ∀ k < κ, P.σ₀ / ((P.p + 1)! : ℝ) * r k ^ R = (a k - P.ς * ε / 4) / P.q ! :=
    fun k hk => by rw [hrR k hk, hM]; simp only; rw [hKσ]; field_simp
  choose! md hmd using fun k (hk : k < κ) => exists_one_div_two_pow_le_lt (hr_pos k hk) (h2r k hk)
  set rd : ℕ → ℝ := fun k => 1 / 2 ^ md k with hrd
  have hrd_pos : ∀ k, 0 < rd k := fun k => by positivity
  have h2rd : ∀ k < κ, 2 * rd k ≤ 1 := fun k hk => by
    have h1 := (hmd k hk).1
    simp only [hrd]
    rw [mul_one_div, div_le_one (by positivity)]
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ md k := pow_le_pow_right₀ one_le_two h1
  have hrd54 : ∀ k < κ, P.σ₀ / ((P.p + 1)! : ℝ) * rd k ^ (P.p + 1) ≤
      (a k - P.ς * ε / 4) / P.q ! * rd k ^ P.q := fun k hk => by
    rw [hpow, ← heq k hk]
    have h1 : rd k ^ R ≤ r k ^ R := pow_le_pow_left₀ (hrd_pos k).le (hmd k hk).2.1 R
    have h2 : 0 ≤ P.σ₀ / ((P.p + 1)! : ℝ) * rd k ^ P.q := by have := (hrd_pos k).le; positivity
    calc P.σ₀ / ((P.p + 1)! : ℝ) * (rd k ^ P.q * rd k ^ R)
        = P.σ₀ / ((P.p + 1)! : ℝ) * rd k ^ P.q * rd k ^ R := by ring
      _ ≤ P.σ₀ / ((P.p + 1)! : ℝ) * rd k ^ P.q * r k ^ R := mul_le_mul_of_nonneg_left h1 h2
      _ = P.σ₀ / ((P.p + 1)! : ℝ) * r k ^ R * rd k ^ P.q := by ring
  have hrd54' : ∀ k < κ, (a k - P.ς * ε / 4) / P.q ! * (2 * rd k) ^ P.q <
      P.σ₀ / ((P.p + 1)! : ℝ) * (2 * rd k) ^ (P.p + 1) := fun k hk => by
    rw [hpow, ← heq k hk]
    have h1 : r k ^ R < (2 * rd k) ^ R :=
      pow_lt_pow_left₀ (hmd k hk).2.2 (hr_pos k hk).le hR0
    have h2 : 0 < P.σ₀ / ((P.p + 1)! : ℝ) * (2 * rd k) ^ P.q := by
      have := hrd_pos k; positivity
    calc P.σ₀ / ((P.p + 1)! : ℝ) * r k ^ R * (2 * rd k) ^ P.q
        = P.σ₀ / ((P.p + 1)! : ℝ) * (2 * rd k) ^ P.q * r k ^ R := by ring
      _ < P.σ₀ / ((P.p + 1)! : ℝ) * (2 * rd k) ^ P.q * (2 * rd k) ^ R :=
          mul_lt_mul_of_pos_left h1 h2
      _ = P.σ₀ / ((P.p + 1)! : ℝ) * ((2 * rd k) ^ P.q * (2 * rd k) ^ R) := by ring
  -- the displacements at `k_ε`
  choose w hw using fun k => exists_isApproxMeasureStep_eq_mul_taylorMeasure (ftaylorSeries ℝ f
      (X k)) P.q zero_le_one
    ⟨P.ς_pos.le, P.ς_le_one⟩
  obtain ⟨δ₁, hδ₁⟩ : ∃ δ₁ : ℕ → ℕ → ℝ, ∀ k, δ₁ k =
      if k < κ then (fun j => if j = P.q then rd k else 1) else fun _ => 1 := ⟨_, fun _ => rfl⟩
  obtain ⟨dd, hdd⟩ : ∃ dd : ℕ → ℕ → EuclideanSpace ℝ (Fin 1), ∀ k, dd k =
      if k < κ then (fun j => if j = P.q then rd k • e₀ else 0)
      else fun j => if j = P.q then w k else 0 := ⟨_, fun _ => rfl⟩
  have hqm : P.q ∈ Finset.Icc 1 P.q := Finset.mem_Icc.2 ⟨P.one_le_q, le_rfl⟩
  have hεa : ∀ k < κ, ε / 2 < a k := fun k hk => by
    have h1 := ha_gt k hk
    have h2 : ε / 2 ≤ lam * ε := by nlinarith
    linarith
  have hdecq : ∀ k ≤ κ, ∀ y : ℝ, (ftaylorSeries ℝ f (X k)).taylorDecrement P.q (y • e₀) =
      a k / P.q ! * y ^ P.q := fun k hk y => by
    rw [hdec k hk _ le_rfl, ite_eq_left rfl, inner_single_smul_self]
  have hδ₁κ : δ₁ κ = fun _ => 1 := by rw [hδ₁, ite_eq_right (lt_irrefl κ)]
  have hddκ : dd κ = fun j => if j = P.q then w κ else 0 := by
    rw [hdd, ite_eq_right (lt_irrefl κ)]
  refine ⟨f, hb, hf, X, δ₁, dd, s, a, by simp [hX, hxr], ha_gt, ha_eq, hmeas,
    fun k hk => ⟨hXs k, by rw [hnorm_s, abs_of_pos (ht_pos k hk.le)]; exact ht_lt k hk.le,
      hfval k hk, by rw [hdecs k hk.le]; have := ha_pos k hk.le; have := ht_pos k hk.le
                     positivity⟩,
    fun k hk => slowARqp_not_arqpDAPass (D := fun i => ftaylorSeries ℝ f (X i)) hε
      (hεa k hk) (hrd_pos k) (by rw [hδ₁, ite_eq_left hk]; simp)
      (by rw [hdd, ite_eq_left hk]; simp) (hdecq k hk.le _),
    hδ₁κ, fun j hj => ?_, ?_, fun h acc ρ hh hh₀ hacc hρ k hk => ?_⟩
  · rw [hddκ]
    dsimp only
    split_ifs with hjq
    · subst hjq
      rw [(hw κ).2, hmeas κ le_rfl _ hqm 1 zero_le_one, ite_eq_left rfl, one_pow, mul_one]
    · rw [FormalMultilinearSeries.taylorDecrement_zero_right, mul_zero]
  · refine ⟨fun j _ => by rw [hδ₁κ]; exact one_pos, fun j hj => by rw [hδ₁κ, hδ₀ j hj],
      fun j hj hlt => by rw [hδ₁κ, hδ₀ j hj] at hlt; exact absurd hlt (lt_irrefl _),
      fun j hj => ⟨0, by rw [hδ₁κ, hδ₀ j hj]; norm_num⟩, fun j hj => ?_⟩
    rw [hδ₁κ, hddκ, Set.setOf_add_mem_univ]
    dsimp only
    split_ifs with hjq
    · subst hjq; exact (hw κ).1
    · refine ⟨⟨mem_closedBall_self zero_le_one, mem_univ _⟩, ?_⟩
      change P.ς * taylorMeasure _ j 1 univ ≤ _
      rw [hmeas κ le_rfl j hj 1 zero_le_one, ite_eq_right hjq, zero_mul, mul_zero,
        FormalMultilinearSeries.taylorDecrement_zero_right]
  · have hk1 : k + 1 ≤ κ := hk
    refine slowARqp_arqpDAStep (x := X) (σ := fun _ => P.σ₀) (δ := fun _ => P.δ₀) (δ₁ := δ₁)
      (δs := fun _ => P.δ₀) (h := h) (dd := dd) (jk := fun _ => P.q) (s := s) (acc := acc)
      (norm_single_one 0)
      (ρ := ρ) (k := k) (D := fun i => ftaylorSeries ℝ f (X i)) (r := rd k) (a := a k) hq2 hε
      (hεa k hk) (hrd_pos k) (h2rd k hk) ⟨md k, rfl⟩ (hrd54 k hk) (hrd54' k hk) hδ₀ rfl hδ₀
      (by rw [hδ₁, ite_eq_left hk]) (by rw [hdd, ite_eq_left hk]) rfl (hdec k hk.le)
      (hdecp k hk.le) (hmin k hk.le)
      (by rw [hnorm_s, abs_of_pos (ht_pos k hk.le)]; exact ht_lt k hk.le) (fun i hi => ?_)
      (hacc k hk) (hXs k) rfl P.σmin_le_σ₀ (by rw [hh k hk.le, hh (k + 1) hk1]) (hρ k hk)
    rw [hh k hk.le, hnorm_s, abs_of_pos (ht_pos k hk.le)]
    refine (hh₀ i hi).trans (mul_le_mul_of_nonneg_left ?_ P.κs_pos.le)
    exact pow_le_pow_left₀ (by positivity) (ht_ge k hk.le) _

/-- **A slow ARqpIDA run with unit radii** on `X = ℝ¹` with exact derivatives (`κ_{∇,i} = 0`),
for `q ∈ {1, 2}`. For `1 ≤ q ≤ min(2, p)` there are `f_low`, `L ≥ 1` and `ε₀ > 0` such that, for
every `ε ∈ (0, ε₀]` (all `ε_j = ε`) and all ARqpIDA constants with orders `p, q`,
`σ₀ = p!/(q-1)!`, unit initial radii and initial accuracies `0 < h_{0,i} ≤ κ_s (ε/2)^{p-i+1}` (so
that the accuracy test (13.1.46) passes along the steps), there is a `C^p` function `f ≥ f_low`
with `L`-Lipschitz derivatives of orders `0, …, p` and an ARqpIDA run with exact derivatives from
`x₀ = 0` satisfying the radii control in both modes (`Optimization.ARqpDARadiiControl u` for every
`u` and every `L̄ ≥ 1`: unit radii after every short trial step), whose first iterate that is
`(ε, δ)`-approximately optimal for some radii `δ ∈ (0, 1]^q` (`Optimization.arqpIDATest`) is
`x_{k_ε}`, `k_ε = ⌈ε^{-(p+1)/(p-q+1)}⌉`, after `k_ε + 1 ≥ ε^{-(p+1)/(p-q+1)} + 1` function and
derivative evaluations. The run follows the slow example of [cartis2022evaluation],
Theorem 12.2.15 (spike jets `f^{(q)}(x_k) = -(ε + ω_k)`, steps the global model minimizers,
`σ_k = σ₀`, `ρ_k = 1`, no accuracy-improving iteration) up to `k_ε`, the Step-1 radius of order
`q` being halved to the scale of the step (where (13.1.54) holds), and continues as any ARqpIDA
run from the state at `k_ε` (`Optimization.exists_arqpDA_steps`). For `q = 1` and for `q = p = 2`
the order `(p+1)/(p-q+1)` is also the order `q(p+1)/p` of the lower-bound mode. -/
theorem exists_isARqpIDARun_slow {p q : ℕ} (hq : 1 ≤ q) (hq2 : q ≤ 2) (hqp : q ≤ p) :
    ∃ flow L ε₀ : ℝ, 1 ≤ L ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ P : ARqpIDAParams,
      P.p = p → P.q = q → P.σ₀ = (p ! : ℝ) / (q - 1)! → (∀ j ∈ Finset.Icc 1 q, P.δ₀ j = 1) →
      (∀ i ∈ Finset.Icc 1 p, 0 < P.h₀ i ∧ P.h₀ i ≤ P.κs * (ε / 2) ^ (p - i + 1)) →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, (∀ y, flow ≤ f y) ∧
        LipschitzDerivsAnchored f univ univ 0 p (fun _ => L) ∧
        ∃ (x : ℕ → EuclideanSpace ℝ (Fin 1)) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ)
          (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 1)) ℝ)
          (dd : ℕ → ℕ → EuclideanSpace ℝ (Fin 1)) (jk : ℕ → ℕ)
          (s : ℕ → EuclideanSpace ℝ (Fin 1)) (acc : ℕ → Prop),
          IsARqpIDARun f univ (fun _ => 0) P (fun _ => ε) 0 x σ δ δ₁ δs h D dd jk s
            acc ∧
          (∀ k, D k = ftaylorSeries ℝ f (x k)) ∧
          (∀ (u : Prop) (Lb : ℝ), 1 ≤ Lb → ∀ k, ARqpDARadiiControl u P
              (fun _ => ε) Lb σ δs s acc k) ∧
          IsFirstHit (arqpIDATest f univ P (fun _ => ε) x)
            ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ ∧
          ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ))) + 1 ≤ (derivEvalCount (fun i => ¬ acc i)
            ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ : ℝ) ∧
          ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ))) + 1 ≤ (derivEvalCount
            (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i))
              ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ : ℝ) := by
  obtain ⟨flow, L, ε₀, hL, hε₀, hε₀4, H⟩ := exists_slowARqp_run hq hq2 hqp (lam := 1)
    (by norm_num) le_rfl
  refine ⟨flow, L, ε₀, hL, hε₀, fun ε hε hεε P hPp hPq hσ hδ₀ hh₀ => ?_⟩
  obtain ⟨f, hb, hf, X, δ₁p, ddp, sp, a, hX0, ha_gt, ha_eq, hmeas, hsp, hnp, -, -, -, hrun⟩ :=
    H ε hε hεε P hPp hPq hσ hδ₀
  subst hPp hPq
  refine ⟨f, hb, hf, ?_⟩
  set κ := ⌈ε ^ (-((P.p + 1 : ℝ) / ((P.p - P.q + 1 : ℕ) : ℝ)))⌉₊ with hκ
  have hκge : ε ^ (-((P.p + 1 : ℝ) / ((P.p - P.q + 1 : ℕ) : ℝ))) ≤ κ := Nat.le_ceil _
  clear_value κ
  have hκ1 : 1 ≤ κ := by
    have : 0 < ε ^ (-((P.p + 1 : ℝ) / ((P.p - P.q + 1 : ℕ) : ℝ))) := Real.rpow_pos_of_pos hε _
    exact_mod_cast (show (0 : ℝ) < κ by linarith)
  have hε1 : ε ≤ 1 := by linarith
  have hεv : ∀ j ∈ Finset.Icc 1 P.q, (fun _ : ℕ => ε) j ∈ Set.Ioc 0 1 := fun _ _ => ⟨hε, hε1⟩
  have hεδ : ∀ j ∈ Finset.Icc 1 P.q, (fun _ : ℕ => ε) j ≤ P.δ₀ j := fun j hj => by
    rw [hδ₀ j hj]; exact hε1
  obtain ⟨x', σ', δ', δ₁', δs', h', dd', jk', s', acc', hx'0, hσ'0, hδ'0, hh'0, -, hr, hrc'⟩ :=
    exists_arqpDA_steps (P := P) (ε := fun _ => ε) (fun y _ => ftaylorSeries ℝ f y)
      (κg := fun _ => 0) (L := fun _ => L) hf (fun _ _ => hL) hεv (fun _ _ => le_rfl) (X κ)
      P.σmin_le_σ₀ (fun j hj => P.δ₀_mem j hj) (fun i hi => ⟨(hh₀ i hi).1, P.h₀_le i hi⟩)
      fun _ _ _ => (jetApprox_self _ _).mono_err fun i _ => by simp
  -- the run: the slow example up to `κ`, then the run from `x_κ`
  have hρp : ∀ k < κ, arqpIDARatio f P (fun i => ftaylorSeries ℝ f (X i)) X sp k = 1 :=
    fun k hk => by
      obtain ⟨-, -, hfv, hpos⟩ := hsp k hk
      rw [arqpIDARatio, reductionRatio_def, hfv, div_self hpos.ne']
  set Xv := Nat.seqAppend κ X x' with hXv
  set σv := Nat.seqAppend κ (fun _ => P.σ₀) σ' with hσv
  set δv := Nat.seqAppend κ (fun _ => P.δ₀) δ' with hδv
  set δ₁v := Nat.seqAppend κ δ₁p δ₁' with hδ₁v
  set δsv := Nat.seqAppend κ (fun _ => P.δ₀) δs' with hδsv
  set hv := Nat.seqAppend κ (fun _ => P.h₀) h' with hhv
  set ddv := Nat.seqAppend κ ddp dd' with hddv
  set jkv := Nat.seqAppend κ (fun _ => P.q) jk' with hjkv
  set sv := Nat.seqAppend κ sp s' with hsv
  set accv := Nat.seqAppend κ (fun _ => False) acc' with haccv
  set Dv : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 1)) ℝ :=
    fun i => ftaylorSeries ℝ f (Xv i) with hDvdef
  have hDv : ∀ k, Dv k = ftaylorSeries ℝ f (Xv k) := fun _ => rfl
  have hstep : ∀ k, ARqpDAStep univ P (fun _ => ε) Xv σv δv δ₁v δsv hv Dv ddv jkv sv accv
      (arqpIDARatio f P Dv Xv sv) k :=
    ARqpDAStep.seqAppend (hrun (fun _ => P.h₀) (fun _ => False) _ (fun _ _ => rfl)
      (fun i hi => (hh₀ i hi).2) (fun _ _ => not_false) hρp) hr hx'0 hσ'0 hδ'0 hh'0
  have hXle : ∀ k ≤ κ, Xv k = X k := fun k hk => Nat.seqAppend_eq_of_le hx'0 hk
  have hσle : ∀ k ≤ κ, σv k = P.σ₀ := fun k hk => Nat.seqAppend_eq_of_le hσ'0 hk
  have hδle : ∀ k ≤ κ, δv k = P.δ₀ := fun k hk => Nat.seqAppend_eq_of_le hδ'0 hk
  have hhle : ∀ k ≤ κ, hv k = P.h₀ := fun k hk => Nat.seqAppend_eq_of_le hh'0 hk
  have hnacc : ∀ k < κ, ¬ accv k := fun k hk => by
    rw [haccv, Nat.seqAppend_of_lt hk]; exact not_false
  have hρ1 : ∀ k < κ, arqpIDARatio f P Dv Xv sv k = 1 := fun k hk => by
    rw [← hρp k hk]; simp only [arqpIDARatio, hDv, hXle k hk.le, hsv, Nat.seqAppend_of_lt hk]
  have hrun' : IsARqpIDARun f univ (fun _ => 0) P (fun _ => ε) 0 Xv σv δv δ₁v δsv
      hv Dv ddv jkv sv accv :=
    ⟨hεv, hεδ, fun _ _ => le_rfl, by rw [hXle 0 (Nat.zero_le _), hX0], mem_univ _,
      hσle 0 (Nat.zero_le _), hδle 0 (Nat.zero_le _), hhle 0 (Nat.zero_le _),
      fun k => by rw [hDv]; exact (jetApprox_self _ _).mono_err fun i _ => by simp, hstep⟩
  have htest : ∀ k ≤ κ, (arqpIDATest f univ P (fun _ => ε) Xv k ↔ k = κ) := fun k hk => by
    rw [arqpIDATest_univ_iff_of_taylorMeasure_eq hε (c := a k) fun j hj t ht => by
      rw [hXle k hk]; exact hmeas k hk j hj t ht]
    refine ⟨fun hc => ?_, fun h => by rw [h, ha_eq, one_mul]⟩
    by_contra hne
    linarith [ha_gt k (lt_of_le_of_ne hk hne)]
  refine ⟨Xv, σv, δv, δ₁v, δsv, hv, Dv, ddv, jkv, sv, accv, hrun', hDv,
    fun u Lb hLb k => ARqpDARadiiControl.of_unit hLb (fun _ _ => hε1) fun hk hs1 j hj => ?_,
    ⟨(htest κ le_rfl).2 rfl, fun i hi ht => hi.ne ((htest i hi.le).1 ht)⟩, ?_, ?_⟩
  · by_cases hkκ : k < κ
    · rw [hδsv, Nat.seqAppend_of_lt hkκ]; exact hδ₀ j hj
    · rw [hδsv, Nat.seqAppend_of_le (not_lt.1 hkκ)]
      rw [haccv, Nat.seqAppend_of_le (not_lt.1 hkκ)] at hk
      rw [hsv, Nat.seqAppend_of_le (not_lt.1 hkκ)] at hs1
      exact (hrc' (k - κ) hk hs1).1 hq2 j hj
  · rw [derivEvalCount_of_forall hnacc]; push_cast at hκge ⊢; linarith
  · rw [derivEvalCount_of_forall fun i hi => Or.inr ⟨hnacc i hi, by
      rw [hρ1 i hi]; exact P.η₁_le_η₂.trans P.η₂_lt_one.le⟩]
    push_cast at hκge ⊢; linarith

/-- **A slow ARqpEDA run with unit radii** on `X = ℝ¹` with exact derivatives and function
values, for `q ∈ {1, 2}`. For `1 ≤ q ≤ min(2, p)` there are `f_low`, `L ≥ 1` and `ε₀ > 0` such
that, for every `ε ∈ (0, ε₀]` (all `ε_j = ε`) and all ARqpEDA constants with orders `p, q`,
`σ₀ = p!/(q-1)!`, unit initial radii, (13.3.13) `κ_s ≤ min(η₁, 1 - η₂)/4`, initial accuracies
passing the accuracy test (13.1.46) along the steps (`h_{0,i} ≤ κ_s (ε/2)^{p-i+1}`) and the
termination test (13.3.17) at unit radii (`∑_{i=1}^j h_{0,i}/i! ≤ ½ ς ε/j!`), there is a `C^p`
function `f ≥ f_low` with `L`-Lipschitz derivatives of orders `0, …, p` and an ARqpEDA run with
exact derivatives and function values from `x₀ = 0` satisfying the radii control in both modes
(`Optimization.ARqpDARadiiControl u` for every `u` and every `L̄ ≥ 1`), which first terminates
at `k_ε = ⌈ε^{-(p+1)/(p-q+1)}⌉`, after `2 k_ε ≥ 2 ε^{-(p+1)/(p-q+1)}` function evaluations (each
value recomputed) and `k_ε + 1 ≥ ε^{-(p+1)/(p-q+1)} + 1` derivative evaluations. The run is the
slow example of [cartis2022evaluation], Theorem 12.2.15 with `f` halved (spike jets
`f^{(q)}(x_k) = -(ε + ω_k)/2`, steps the global model minimizers, `σ_k = σ₀`, `ρ_k = 1`, no
accuracy-improving iteration, the Step-1 radius of order `q` halved to the scale of the step), the
halving making the test (13.1.53), whose threshold is half that of ARqp, pass exactly at `k_ε`.
For `q = 1` and for `q = p = 2` the order `(p+1)/(p-q+1)` is also the order `q(p+1)/p` of the
lower-bound mode. -/
theorem exists_isARqpEDARun_slow {p q : ℕ} (hq : 1 ≤ q) (hq2 : q ≤ 2) (hqp : q ≤ p) :
    ∃ flow L ε₀ : ℝ, 1 ≤ L ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ P : ARqpIDAParams,
      P.p = p → P.q = q → P.σ₀ = (p ! : ℝ) / (q - 1)! → (∀ j ∈ Finset.Icc 1 q, P.δ₀ j = 1) →
      P.κs ≤ min P.η₁ (1 - P.η₂) / 4 →
      (∀ i ∈ Finset.Icc 1 p, P.h₀ i ≤ P.κs * (ε / 2) ^ (p - i + 1)) →
      (∀ j ∈ Finset.Icc 1 q, ∑ i ∈ Finset.Icc 1 j, P.h₀ i / i ! ≤ P.ς * ε / j ! / 2) →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, (∀ y, flow ≤ f y) ∧
        LipschitzDerivsAnchored f univ univ 0 p (fun _ => L) ∧
        ∃ (x : ℕ → EuclideanSpace ℝ (Fin 1)) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ)
          (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 1)) ℝ)
          (dd : ℕ → ℕ → EuclideanSpace ℝ (Fin 1)) (jk : ℕ → ℕ)
          (s : ℕ → EuclideanSpace ℝ (Fin 1)) (acc : ℕ → Prop) (fx fxs h₀ : ℕ → ℝ)
          (R : ℕ → Prop),
          IsARqpEDARun f univ P (fun _ => ε) 0 x σ δ δ₁ δs h D dd jk s acc fx fxs
            h₀ R ∧
          (∀ k, D k = ftaylorSeries ℝ f (x k) ∧ fx k = f (x k) ∧ fxs k = f (x k + s k)) ∧
          (∀ (u : Prop) (Lb : ℝ), 1 ≤ Lb → ∀ k, ARqpDARadiiControl u P
              (fun _ => ε) Lb σ δs s acc k) ∧
          IsFirstHit (edaStopAR P (fun _ => ε) D δ₁ h dd)
            ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ ∧
          2 * ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ))) ≤ (edaFunEvalCount acc R
            ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ : ℝ) ∧
          ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ))) + 1 ≤ (derivEvalCount (fun i => acc i ∨
            (¬ acc i ∧ P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i))
              ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ : ℝ) := by
  obtain ⟨flow, L, ε₀, hL, hε₀, hε₀4, H⟩ := exists_slowARqp_run hq hq2 hqp (lam := 1 / 2)
    le_rfl (by norm_num)
  refine ⟨flow, L, ε₀, hL, hε₀, fun ε hε hεε P hPp hPq hσ hδ₀ hκs hh₀ hsum => ?_⟩
  obtain ⟨f, hb, hf, X, δ₁, dd, s, a, hX0, ha_gt, ha_eq, -, hsp, hnp, hδ₁κ, hddκ, hstep1κ,
    hrun⟩ := H ε hε hεε P hPp hPq hσ hδ₀
  subst hPp hPq
  refine ⟨f, hb, hf, ?_⟩
  set κ := ⌈ε ^ (-((P.p + 1 : ℝ) / ((P.p - P.q + 1 : ℕ) : ℝ)))⌉₊ with hκ
  have hκge : ε ^ (-((P.p + 1 : ℝ) / ((P.p - P.q + 1 : ℕ) : ℝ))) ≤ κ := Nat.le_ceil _
  clear_value κ
  have hε1 : ε ≤ 1 := by linarith
  set D : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 1)) ℝ :=
    fun i => ftaylorSeries ℝ f (X i) with hD
  set fx : ℕ → ℝ := fun k => f (X k) with hfx
  set fxs : ℕ → ℝ := fun k => f (X k + s k) with hfxs
  set ρ : ℕ → ℝ := edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) with hρ
  have hρ1 : ∀ k < κ, ρ k = 1 := fun k hk => by
    obtain ⟨-, -, hfv, hpos⟩ := hsp k hk
    simp only [hρ, edaRatio, hfx, hfxs]
    rw [hfv, div_self hpos.ne']
  have hqm : P.q ∈ Finset.Icc 1 P.q := Finset.mem_Icc.2 ⟨P.one_le_q, le_rfl⟩
  have hstop : ∀ k ≤ κ, (edaStopAR P (fun _ => ε) D δ₁ (fun _ => P.h₀) dd k ↔ k = κ) := by
    intro k hk
    constructor
    · rintro ⟨hp, -⟩
      by_contra hne
      exact hnp k (lt_of_le_of_ne hk hne) (hp _ hqm)
    · rintro rfl
      refine ⟨fun j hj => ?_, fun j hj => ?_⟩
      · rw [arqpDAPass, hddκ j hj, hδ₁κ, one_pow, mul_one]
        split_ifs with hjq
        · subst hjq; rw [ha_eq]; apply le_of_eq; ring
        · rw [mul_zero]; have := P.ς_pos; positivity
      · rw [hδ₁κ]
        simp only [one_pow, mul_one]
        exact hsum j hj
  have hnstop : ∀ k < κ, ¬ edaStopAR P (fun _ => ε) D δ₁ (fun _ => P.h₀) dd k :=
    fun k hk hs => hk.ne ((hstop k hk.le).1 hs)
  have hreach : ∀ k, (∀ j < k, ¬ edaStopAR P (fun _ => ε) D δ₁ (fun _ => P.h₀) dd j) → k ≤ κ :=
    fun k hk => by
      by_contra hge
      exact hk κ (not_le.1 hge) ((hstop κ le_rfl).2 rfl)
  have hstep := hrun (fun _ => P.h₀) (fun _ => False) ρ (fun _ _ => rfl) hh₀
    (fun _ _ => not_false) hρ1
  have hrun' : IsARqpEDARun f univ P (fun _ => ε) 0 X (fun _ => P.σ₀)
      (fun _ => P.δ₀) δ₁ (fun _ => P.δ₀) (fun _ => P.h₀) D dd (fun _ => P.q) s (fun _ => False)
      fx fxs
      (fun k => P.κs * (D k).taylorDecrement P.p (s k)) (fun _ => True) := by
    refine ⟨hκs, fun _ _ => ⟨hε, hε1⟩, fun j hj => by rw [hδ₀ j hj]; exact hε1, hX0, mem_univ _,
      rfl, rfl, rfl, fun k _ => ?_, fun k hk => ?_, fun k hk => ?_⟩
    · exact (jetApprox_self _ _).mono_err fun i hi => P.h₀_nonneg i hi
    · rcases (hreach k hk).lt_or_eq with hlt | rfl
      · exact (hstep k hlt).toARqpStep1
      · exact hstep1κ
    · have hkκ : k < κ := by
        rcases (hreach k fun j hj => hk j hj.le).lt_or_eq with hlt | rfl
        · exact hlt
        · exact absurd ((hstop k le_rfl).2 rfl) (hk k le_rfl)
      obtain ⟨-, -, -, hpos⟩ := hsp k hkκ
      have hpos' : 0 < P.κs * (D k).taylorDecrement P.p (s k) := mul_pos P.κs_pos hpos
      exact ⟨hstep k hkκ, fun _ => ⟨hpos', le_rfl, by simp [hfxs, hpos'.le],
        by simp [hfx, hpos'.le], fun h => absurd trivial h⟩⟩
  refine ⟨X, fun _ => P.σ₀, fun _ => P.δ₀, δ₁, fun _ => P.δ₀, fun _ => P.h₀, D, dd,
    fun _ => P.q, s, fun _ => False, fx, fxs, fun k => P.κs * (D k).taylorDecrement P.p (s k),
    fun _ => True, hrun', fun k => ⟨rfl, rfl, rfl⟩,
    fun u Lb hLb k => ARqpDARadiiControl.of_unit hLb (fun _ _ => hε1) fun _ _ j hj => hδ₀ j hj,
    ⟨(hstop κ le_rfl).2 rfl, hnstop⟩, ?_, ?_⟩
  · rw [edaFunEvalCount, card_filter_range_of_forall fun _ _ => not_false,
      card_filter_range_of_forall fun _ _ => ⟨not_false, trivial⟩]
    push_cast at hκge ⊢; linarith
  · rw [derivEvalCount_of_forall fun i hi => Or.inr ⟨not_false, by
      rw [← hρ, hρ1 i hi]; exact P.η₁_le_η₂.trans P.η₂_lt_one.le⟩]
    push_cast at hκge ⊢; linarith

/-- The weight `σ = (3/(p+2))^p` of the gradient interpolant. -/
private theorem slowGrad_sigma_pos (p : ℕ) : (0 : ℝ) < (3 / ((p : ℝ) + 2)) ^ p := by positivity

/-- **The slow gradient example on `ℝ¹`** (the data of [cartis2022evaluation], Theorem 12.2.17
with `r = p` and the weight `σ = (3/(p+2))^p`, lifted along `e₁` and halved). For `1 ≤ q ≤ p`
there are `f_low` and `L ≥ 1` such that, for every `ε ∈ (0, 1]`, with `k_ε = ⌈ε^{-q(p+1)/p}⌉`,
`β_k = (ε^q + ε^{qp/p} (k_ε - k)/k_ε)/q!` and points `x_{k+1} = x_k + (p! β_k/σ)^{1/p}`, there is a
`C^p` function `g` of one variable whose ridge `f = g(⟪e₁, ·⟫)` is bounded below by `f_low` and
has `L`-Lipschitz derivatives of orders `0, …, p`, with spike jets `g'(x_k) = -β_k/2` (other
derivatives of orders `2, …, p` zero) for `k ≤ k_ε` and
`g(x_{k+1}) = g(x_k) - β_k/2 (x_{k+1} - x_k)` for `k < k_ε`. -/
private theorem exists_slowGrad_ridge {p q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) :
    ∃ flow L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ xr : ℕ → ℝ,
      (∀ k < ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊, xr (k + 1) = xr k + (p ! *
        ((ε ^ q + ε ^ ((q : ℝ) * p / p) * ((⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ : ℝ) - k) /
          ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊) / q !) / (3 / ((p : ℝ) + 2)) ^ p) ^
            (1 / (p : ℝ))) →
      ∃ g : ℝ → ℝ, ContDiff ℝ p g ∧ (∀ y, flow ≤ ridge g e₀ y) ∧
        LipschitzDerivsAnchored (ridge g e₀) univ univ 0 p (fun _ => L) ∧
        (∀ k ≤ ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊, IsSpikeJetOf p g 1 (xr k)
          ((ε ^ q + ε ^ ((q : ℝ) * p / p) * ((⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ : ℝ) - k) /
            ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊) / q ! / 2)) ∧
        ∀ k < ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊, g (xr (k + 1)) = g (xr k) -
          (ε ^ q + ε ^ ((q : ℝ) * p / p) * ((⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ : ℝ) - k) /
            ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊) / q ! / 2 * (xr (k + 1) - xr k) := by
  obtain ⟨L, B, hL, hB, hG⟩ :=
    exists_slowARqpSmooth_interpolant hq hqp le_rfl (slowGrad_sigma_pos p)
  refine ⟨-B, max 1 (max L B), le_max_left _ _, fun ε hε hε1 xr hxr => ?_⟩
  obtain ⟨G, hGc, hGL, hGB, hGd, hGf⟩ := hG ε _ xr hε hε1 rfl hxr
  set g : ℝ → ℝ := fun t => (1 / 2 : ℝ) * G t with hg
  obtain ⟨hfc, hfb, hfl⟩ := ridge_const_mul_slow_bounds (G := G) (lam := 1 / 2) (e := e₀) hGc hB
    hGL hGB (by norm_num) (by norm_num) (norm_single_one 0).le
  refine ⟨g, contDiff_const.mul hGc, hfb,
    .of_contDiff hfc (fun j hj => hfl j (Finset.mem_Icc.1 hj).2) univ,
    fun k hk => ?_, fun k hk => ?_⟩
  · have hspike : IsSpikeJetOf p G 1 (xr k) _ :=
      ⟨by rw [iteratedDeriv_one, (hGd k hk).1], fun j hj1 hjp hj => (hGd k hk).2 j (by omega) hjp⟩
    convert hspike.const_mul (1 / 2) using 1
    ring
  · simp only [hg]
    rw [hGf k hk]; ring

/-- **A slow ARqpEDA run in the lower-bound mode** of the radii control on `X = ℝ¹` with exact
derivatives and function values, for every `1 ≤ q ≤ p`. There are `f_low`, `L ≥ 1` and `ε₀ > 0`
such that, for every `ε ∈ (0, ε₀]` (all `ε_j = ε`) and all ARqpEDA constants with orders `p, q`,
weight `σ₀ = (3/(p+2))^p/2`, initial radii `δ₀ = ε`, (13.3.13) `κ_s ≤ min(η₁, 1 - η₂)/4`, initial
accuracies passing the accuracy test (13.1.46) along the steps (`h_{0,i} ≤ κ_s ε^{p-i+1}`) and the
termination test (13.3.17) at radius `ε` (`∑_{i=1}^j h_{0,i} ε^i/i! ≤ ½ ς ε ε^j/j!`), there is a
`C^p` function `f ≥ f_low` with `L`-Lipschitz derivatives of orders `0, …, p` and an ARqpEDA run
with exact derivatives and function values from `x₀ = 0` satisfying the radii control in the
lower-bound mode (`Optimization.ARqpDARadiiControl False` for every `L̄ ≥ 1`; all radii are `ε`),
which first terminates at `k_ε = ⌈ε^{-q(p+1)/p}⌉`, after `2 k_ε ≥ 2 ε^{-q(p+1)/p}` function
evaluations (each value recomputed) and `k_ε + 1 ≥ ε^{-q(p+1)/p} + 1` derivative evaluations.
The run is the slow example of [cartis2022evaluation], Theorem 12.2.17 (with `r = p`) with `f`
halved and a smaller weight: gradient spikes
`f'(x_k) = -β_k/2`, `β_k = (ε^q + ω_k)/q!`, steps the global model minimizers, `σ_k = σ₀`,
`ρ_k = 1`, no accuracy-improving iteration, and Step-1 displacements achieving exactly the
fraction `ς` of the measures; the weight is small enough for (13.1.54) to hold at these
displacements (unlike with the weight (12.2.85) of Theorem 12.2.17) and for the measures of the
model at its minimizer to vanish at radius `ε` ([cartis2022evaluation], Example 12.1.3). -/
theorem exists_isARqpEDARun_slowGrad {p q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) :
    ∃ flow L ε₀ : ℝ, 1 ≤ L ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ P : ARqpIDAParams,
      P.p = p → P.q = q → P.σ₀ = (3 / ((p : ℝ) + 2)) ^ p / 2 → (∀ j ∈ Finset.Icc 1 q, P.δ₀ j = ε) →
      P.κs ≤ min P.η₁ (1 - P.η₂) / 4 →
      (∀ i ∈ Finset.Icc 1 p, P.h₀ i ≤ P.κs * ε ^ (p - i + 1)) →
      (∀ j ∈ Finset.Icc 1 q, ∑ i ∈ Finset.Icc 1 j, P.h₀ i * ε ^ i / i ! ≤
        P.ς * ε * ε ^ j / j ! / 2) →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, (∀ y, flow ≤ f y) ∧
        LipschitzDerivsAnchored f univ univ 0 p (fun _ => L) ∧
        ∃ (x : ℕ → EuclideanSpace ℝ (Fin 1)) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ)
          (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 1)) ℝ)
          (dd : ℕ → ℕ → EuclideanSpace ℝ (Fin 1)) (jk : ℕ → ℕ)
          (s : ℕ → EuclideanSpace ℝ (Fin 1)) (acc : ℕ → Prop) (fx fxs h₀ : ℕ → ℝ)
          (R : ℕ → Prop),
          IsARqpEDARun f univ P (fun _ => ε) 0 x σ δ δ₁ δs h D dd jk s acc fx fxs
            h₀ R ∧
          (∀ k, D k = ftaylorSeries ℝ f (x k) ∧ fx k = f (x k) ∧ fxs k = f (x k + s k)) ∧
          (∀ Lb : ℝ, 1 ≤ Lb → ∀ k, ARqpDARadiiControl False P (fun _ => ε) Lb σ δs s acc k) ∧
          IsFirstHit (edaStopAR P (fun _ => ε) D δ₁ h dd)
            ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ ∧
          2 * ε ^ (-((q : ℝ) * (p + 1) / p)) ≤
            (edaFunEvalCount acc R ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ : ℝ) ∧
          ε ^ (-((q : ℝ) * (p + 1) / p)) + 1 ≤ (derivEvalCount (fun i => acc i ∨
            (¬ acc i ∧ P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i))
              ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ : ℝ) := by
  obtain ⟨flow, L, hL, H⟩ := exists_slowGrad_ridge hq hqp
  have hp : 1 ≤ p := hq.trans hqp
  have hσI := slowGrad_sigma_pos p
  refine ⟨flow, L, min (1 / 2) ((3 / ((p : ℝ) + 2)) ^ p / (4 * p !)), hL, by positivity,
    fun ε hε hεε P hPp hPq hσ hδ₀ hκs hh₀ hsum => ?_⟩
  subst hPp hPq
  have hε2 : ε ≤ 1 / 2 := hεε.trans (min_le_left _ _)
  have hεσ : ε ≤ (3 / ((P.p : ℝ) + 2)) ^ P.p / (4 * P.p !) := hεε.trans (min_le_right _ _)
  have hε1 : ε ≤ 1 := by linarith
  set σI : ℝ := (3 / ((P.p : ℝ) + 2)) ^ P.p with hσIdef
  have hσI1 : σI ≤ 1 := pow_le_one₀ (by positivity) (by
    rw [div_le_one (by positivity)]; have : (1 : ℝ) ≤ P.p := by exact_mod_cast hp
    linarith)
  have hκ1 : 1 ≤ ⌈ε ^ (-((P.q : ℝ) * (P.p + 1) / P.p))⌉₊ :=
    Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (Real.rpow_pos_of_pos hε _)).ne'
  have hκge : ε ^ (-((P.q : ℝ) * (P.p + 1) / P.p)) ≤ ⌈ε ^ (-((P.q : ℝ) * (P.p + 1) / P.p))⌉₊ :=
    Nat.le_ceil _
  set κ := ⌈ε ^ (-((P.q : ℝ) * (P.p + 1) / P.p))⌉₊ with hκ
  have hκpos : (0 : ℝ) < κ := by exact_mod_cast hκ1
  have hp0 : P.p ≠ 0 := by omega
  have hqpp : ε ^ ((P.q : ℝ) * P.p / P.p) = ε ^ P.q := by
    rw [mul_div_assoc, div_self (by exact_mod_cast hp0), mul_one, Real.rpow_natCast]
  have hqf : (0 : ℝ) < P.q ! := by positivity
  have hpf : (0 : ℝ) < P.p ! := by positivity
  -- the levels, the steps and the points
  set βI : ℕ → ℝ := fun k => (ε ^ P.q + ε ^ ((P.q : ℝ) * P.p / P.p) * ((κ : ℝ) - k) / κ) / P.q !
    with hβI
  set t : ℕ → ℝ := fun k => (P.p ! * βI k / σI) ^ (1 / (P.p : ℝ)) with ht
  set xr : ℕ → ℝ := fun k => ∑ i ∈ Finset.range k, t i with hxr
  have hxr1 : ∀ k, xr (k + 1) = xr k + t k := fun k => Finset.sum_range_succ _ _
  obtain ⟨g, hgc, hb, hf, hspike, hval⟩ := H ε hε hε1 xr fun k _ => hxr1 k
  have hω0 : ∀ k ≤ κ, 0 ≤ ε ^ P.q * ((κ : ℝ) - k) / κ := fun k hk =>
    slowGap_nonneg (by positivity) hk
  have hω1 : ∀ k ≤ κ, ε ^ P.q * ((κ : ℝ) - k) / κ ≤ ε ^ P.q := fun k _ =>
    slowGap_le (by positivity) κ k
  have hωpos : ∀ k < κ, 0 < ε ^ P.q * ((κ : ℝ) - k) / κ := fun k hk =>
    slowGap_pos (by positivity) hk
  have hβI : ∀ k, βI k = (ε ^ P.q + ε ^ P.q * ((κ : ℝ) - k) / κ) / P.q ! := fun k => by
    simp only [hβI, hqpp]
  have hβ_gt : ∀ k < κ, ε ^ P.q / P.q ! / 2 < βI k / 2 := fun k hk => by
    rw [hβI]
    have := hωpos k hk
    have : ε ^ P.q / P.q ! < (ε ^ P.q + ε ^ P.q * ((κ : ℝ) - k) / κ) / P.q ! :=
      div_lt_div_of_pos_right (by linarith) hqf
    linarith
  have hβ_ge : ∀ k ≤ κ, ε ^ P.q / P.q ! ≤ βI k := fun k hk => by
    rw [hβI]
    exact div_le_div_of_nonneg_right (by linarith [hω0 k hk]) hqf.le
  have hβ_le : ∀ k ≤ κ, βI k / 2 ≤ ε ^ P.q / P.q ! := fun k hk => by
    rw [hβI]
    have := hω1 k hk
    rw [div_div, div_le_div_iff₀ (by positivity) hqf]
    nlinarith
  have hβ_eq : βI κ / 2 = ε ^ P.q / P.q ! / 2 := by
    rw [hβI, sub_self, mul_zero, zero_div, add_zero]
  have hβ_pos : ∀ k ≤ κ, 0 < βI k := fun k hk =>
    lt_of_lt_of_le (by positivity) (hβ_ge k hk)
  -- the step lengths
  have hX_ge : ∀ k ≤ κ, (ε * ((P.p + 2) / 3)) ^ P.p ≤ P.p ! * βI k / σI := fun k hk => by
    have h1 : (ε * ((P.p + 2) / 3)) ^ P.p = ε ^ P.p / σI := by
      rw [hσIdef, mul_pow, div_pow, div_pow, div_div_eq_mul_div]
      field_simp
    rw [h1, div_le_div_iff_of_pos_right hσI]
    have h2 : ε ^ P.p ≤ ε ^ P.q := pow_le_pow_of_le_one hε.le hε1 P.q_le_p
    have h3 : ε ^ P.q ≤ P.p ! * (ε ^ P.q / P.q !) := by
      rw [mul_div_assoc', le_div_iff₀ hqf]
      have : (P.q ! : ℝ) ≤ P.p ! := by exact_mod_cast Nat.factorial_le P.q_le_p
      have := pow_pos hε P.q
      nlinarith
    calc ε ^ P.p ≤ P.p ! * (ε ^ P.q / P.q !) := h2.trans h3
      _ ≤ P.p ! * βI k := mul_le_mul_of_nonneg_left (hβ_ge k hk) hpf.le
  have hX_le : ∀ k ≤ κ, P.p ! * βI k / σI ≤ 1 / 2 := fun k hk => by
    have h1 : βI k ≤ 2 * ε := by
      have := hβ_le k hk
      have h2 : ε ^ P.q / P.q ! ≤ ε := by
        rw [div_le_iff₀ hqf]
        have : (1 : ℝ) ≤ P.q ! := by
          exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
        have : ε ^ P.q ≤ ε := pow_le_of_le_one hε.le hε1 (by have := P.one_le_q; omega)
        nlinarith
      linarith
    rw [div_le_iff₀ hσI]
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * P.p !)).1 hεσ
    nlinarith
  have ht_ge : ∀ k ≤ κ, ε * ((P.p + 2) / 3) ≤ t k := fun k hk => by
    have h := Real.rpow_le_rpow (by positivity) (hX_ge k hk) (by positivity : (0 : ℝ) ≤ 1 / P.p)
    rwa [one_div, Real.pow_rpow_inv_natCast (by positivity) hp0, ← one_div] at h
  have ht_lt : ∀ k ≤ κ, t k < 1 := fun k hk =>
    Real.rpow_lt_one (by have := hβ_pos k hk; positivity) (by linarith [hX_le k hk])
      (by positivity)
  have hεt : ∀ k ≤ κ, ε ≤ t k := fun k hk => by
    have := ht_ge k hk
    have : ε ≤ ε * ((P.p + 2) / 3) := by
      have : (1 : ℝ) ≤ (P.p + 2) / 3 := by
        rw [le_div_iff₀ (by norm_num)]; have : (1 : ℝ) ≤ P.p := by exact_mod_cast hp
        linarith
      nlinarith
    linarith
  -- the function and its Taylor data
  have hσ₀ : 0 < P.σ₀ := P.σ₀_pos
  set f : EuclideanSpace ℝ (Fin 1) → ℝ := ridge g e₀ with hfdef
  set X : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => xr k • e₀ with hX
  set s : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => t k • e₀ with hs
  have hXs : ∀ k, X (k + 1) = X k + s k := fun k => by
    simp only [hX, hs, hxr1, add_smul]
  have hspX : ∀ k ≤ κ, IsSpikeJetOf P.p g 1 ⟪e₀, X k⟫ (βI k / 2) := fun k hk => by
    rw [inner_single_smul_self]; exact hspike k hk
  have hdec : ∀ k ≤ κ, ∀ j ∈ Finset.Icc 1 P.p, ∀ d,
      (ftaylorSeries ℝ f (X k)).taylorDecrement j d = βI k / 2 * ⟪e₀, d⟫ := fun k hk j hj d => by
    obtain ⟨hj1, hjp⟩ := Finset.mem_Icc.1 hj
    rw [taylorDecrement_ridge_spike (hgc.of_le (by exact_mod_cast hjp)) le_rfl hj1
      ⟨(hspX k hk).1, fun i h1 hi hne => (hspX k hk).2 i h1 (hi.trans hjp) hne⟩ d]
    simp
  have htk : ∀ k, (βI k / 2 * P.p ! / P.σ₀) ^ (1 / (P.p : ℝ)) = t k := fun k => by
    simp only [ht]
    congr 1
    rw [hσ]
    field_simp
  have hmin : ∀ k ≤ κ, IsMinOn (regularizedModel (ftaylorSeries ℝ f (X k)) P.p P.σ₀) univ
      (s k) := fun k hk => by
    obtain ⟨hm, -, -⟩ := isMinOn_neg_monomial_add_regularization le_rfl hp hσ₀
      (by have := hβ_pos k hk; positivity : 0 < βI k / 2)
    have e : (βI k / 2 / (P.σ₀ * ((1 - 1)! : ℕ) / P.p !)) ^ (1 / ((P.p - 1 + 1 : ℕ) : ℝ)) =
        t k := by
      rw [Nat.sub_add_cancel hp, ← htk]
      congr 1
      simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, mul_one]
      field_simp
    rw [e] at hm
    intro y _
    simp only [mem_ofPred_eq]
    rw [regularizedModel_ridge_spike norm_eq_abs_inner_single hgc le_rfl hp (hspX k hk),
      ridge_apply, ridge_apply, show s k = t k • e₀ from rfl, inner_single_smul_self 0 (t k)]
    exact (add_le_add_iff_left _).2 (isMinOn_iff.1 hm _ (mem_univ _))
  have hmodel : ∀ k ≤ κ, ∀ ℓ ∈ Finset.Icc 1 P.q, ∀ d, ‖d‖ ≤ ε →
      (ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ f (X k)) P.p P.σ₀) (s k)).taylorDecrement
        ℓ d ≤ 0 := fun k hk ℓ hℓ d hd => by
    have h := taylorDecrement_regularizedModel_ridge_linear_nonpos (norm_single_one 0)
        norm_eq_abs_inner_single hp
      hgc (β := βI k / 2) (σ := P.σ₀) (δ := ε)
      (by have := hβ_pos k hk; positivity) hσ₀ (hspX k hk) (P.Icc_q_subset hℓ)
      (Or.inr (by rw [htk]; have := ht_ge k hk; nlinarith)) hd
    rwa [htk] at h
  have hdecs : ∀ k ≤ κ, (ftaylorSeries ℝ f (X k)).taylorDecrement P.p (s k) = βI k / 2 * t k :=
    fun k hk => by
      rw [hdec k hk _ (Finset.mem_Icc.2 ⟨hp, le_rfl⟩), show s k = t k • e₀ from rfl,
        inner_single_smul_self]
  have hfval : ∀ k < κ, f (X k) - f (X k + s k) =
      (ftaylorSeries ℝ f (X k)).taylorDecrement P.p (s k) := fun k hk => by
    rw [hdecs k hk.le, ← hXs, hfdef, ridge_apply, ridge_apply, hX, inner_single_smul_self,
        inner_single_smul_self,
      hval k hk, hxr1]
    ring
  have hdpos : ∀ k ≤ κ, 0 < (ftaylorSeries ℝ f (X k)).taylorDecrement P.p (s k) := fun k hk => by
    rw [hdecs k hk]
    have := hβ_pos k hk; have := hεt k hk
    have : 0 < t k := lt_of_lt_of_le hε this
    positivity
  have hσ54 : P.σ₀ / ((P.p + 1)! : ℝ) ≤ 1 / (4 * P.q !) := by
    have h1 : P.σ₀ ≤ 1 / 2 := by rw [hσ]; linarith
    have h2 : 2 * (P.q ! : ℝ) ≤ (P.p + 1)! := by
      have : (P.q ! : ℝ) ≤ P.p ! := by exact_mod_cast Nat.factorial_le P.q_le_p
      have e : ((P.p + 1)! : ℝ) = (P.p + 1) * P.p ! := by push_cast [Nat.factorial_succ]; ring
      rw [e]
      have : (1 : ℝ) ≤ P.p := by exact_mod_cast hp
      nlinarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  -- the Step-1 displacements
  choose w hw using fun k j => exists_isApproxMeasureStep_eq_mul_taylorMeasure (ftaylorSeries ℝ f
      (X k)) j hε.le
    ⟨P.ς_pos.le, P.ς_le_one⟩
  set D : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 1)) ℝ :=
    fun i => ftaylorSeries ℝ f (X i) with hD
  set fx : ℕ → ℝ := fun k => f (X k) with hfx
  set fxs : ℕ → ℝ := fun k => f (X k + s k) with hfxs
  set ρ : ℕ → ℝ := edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) with hρ
  have hρ1 : ∀ k < κ, ρ k = 1 := fun k hk => by
    simp only [hρ, edaRatio, hfx, hfxs, hD]
    rw [hfval k hk, div_self (hdpos k hk.le).ne']
  have hqm : P.q ∈ Finset.Icc 1 P.q := Finset.mem_Icc.2 ⟨P.one_le_q, le_rfl⟩
  have hdv : ∀ k ≤ κ, ∀ j ∈ Finset.Icc 1 P.q,
      (D k).taylorDecrement j (w k j) = P.ς * (βI k / 2 * ε) := fun k hk j hj =>
    slowGrad_taylorDecrement_eq (D := D) (dd := w) (norm_single_one 0) hε
      (by have := hβ_pos k hk; positivity) (hdec k hk) (fun j _ => hw k j) hj
  have hstop : ∀ k ≤ κ, (edaStopAR P (fun _ => ε) D (fun _ => P.δ₀) (fun _ => P.h₀) w k ↔
      k = κ) := by
    intro k hk
    constructor
    · rintro ⟨hp', -⟩
      by_contra hne
      exact slowGrad_not_arqpDAPass (δ₁ := fun _ => P.δ₀) hε (hβ_gt k (lt_of_le_of_ne hk hne))
        (hδ₀ _ hqm) (hdv k hk _ hqm) (hp' _ hqm)
    · rintro rfl
      refine ⟨fun j hj => ?_, fun j hj => by simp only [hδ₀ j hj]; exact hsum j hj⟩
      rw [arqpDAPass, hdv _ le_rfl j hj, hβ_eq, hδ₀ j hj]
      rcases (Finset.mem_Icc.1 hj).2.lt_or_eq with hjq | rfl
      · have h1 := pow_div_factorial_le_of_lt hε.le (by linarith only [hε2]) two_pos
          (by linarith only [hε2]) hjq
        have h2 : ε ^ P.q / P.q ! / 2 * ε ≤ ε * ε ^ j / j ! / 2 := by
          rw [show ε * ε ^ j / j ! / 2 = ε ^ j / j ! / 2 * ε by ring]
          refine mul_le_mul_of_nonneg_right ?_ hε.le
          have : 0 ≤ ε ^ P.q / P.q ! := by positivity
          linarith
        have e : P.ς * ε * ε ^ j / j ! / 2 = P.ς * (ε * ε ^ j / j ! / 2) := by ring
        rw [e]
        exact mul_le_mul_of_nonneg_left h2 P.ς_pos.le
      · apply le_of_eq; ring
  have hnstop : ∀ k < κ, ¬ edaStopAR P (fun _ => ε) D (fun _ => P.δ₀) (fun _ => P.h₀) w k :=
    fun k hk hs' => hk.ne ((hstop k hk.le).1 hs')
  have hreach : ∀ k, (∀ j < k, ¬ edaStopAR P (fun _ => ε) D (fun _ => P.δ₀) (fun _ => P.h₀) w j) →
      k ≤ κ := fun k hk => by
    by_contra hge
    exact hk κ (not_le.1 hge) ((hstop κ le_rfl).2 rfl)
  have hstep : ∀ k < κ, ARqpDAStep univ P (fun _ => ε) X (fun _ => P.σ₀) (fun _ => P.δ₀)
      (fun _ => P.δ₀) (fun _ => P.δ₀) (fun _ => P.h₀) D w (fun _ => P.q) s (fun _ => False) ρ k :=
    fun k hk => slowGrad_arqpDAStep (norm_single_one 0) norm_eq_abs_inner_single hε hε2 (hβ_gt k hk)
        (hβ_le k hk.le) hσ54 hδ₀ rfl rfl hδ₀ rfl
      (hdec k hk.le) (fun j _ => hw k j) (hmin k hk.le) (hmodel k hk.le)
      (by rw [show s k = t k • e₀ from rfl, norm_smul_single, abs_of_pos (lt_of_lt_of_le hε
        (hεt k hk.le))]; exact ht_lt k hk.le)
      (fun i hi => by
        rw [show s k = t k • e₀ from rfl, norm_smul_single, abs_of_pos (lt_of_lt_of_le hε
          (hεt k hk.le))]
        exact (hh₀ i hi).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hε.le (hεt k hk.le) _) P.κs_pos.le))
      not_false (hXs k) rfl P.σmin_le_σ₀ rfl (hρ1 k hk)
  have hrun : IsARqpEDARun f univ P (fun _ => ε) 0 X (fun _ => P.σ₀)
      (fun _ => P.δ₀) (fun _ => P.δ₀) (fun _ => P.δ₀) (fun _ => P.h₀) D w (fun _ => P.q) s
      (fun _ => False) fx fxs (fun k => P.κs * (D k).taylorDecrement P.p (s k))
      (fun _ => True) := by
    refine ⟨hκs, fun _ _ => ⟨hε, hε1⟩, fun j hj => by rw [hδ₀ j hj], by simp [hX, hxr],
      mem_univ _, rfl, rfl, rfl, fun k _ => ?_, fun k hk => ?_, fun k hk => ?_⟩
    · exact (jetApprox_self _ _).mono_err fun i hi => P.h₀_nonneg i hi
    · have hkκ := hreach k hk
      exact ⟨fun j hj => by simp only [hδ₀ j hj]; exact hε, fun _ _ => le_rfl,
        fun _ _ hlt => absurd hlt (lt_irrefl _), fun _ _ => ⟨0, by norm_num⟩,
        fun j hj => by simp only [hδ₀ j hj, Set.setOf_add_mem_univ]; exact (hw k j).1⟩
    · have hkκ : k < κ := by
        rcases (hreach k fun j hj => hk j hj.le).lt_or_eq with hlt | rfl
        · exact hlt
        · exact absurd ((hstop _ le_rfl).2 rfl) (hk _ le_rfl)
      have hpos' : 0 < P.κs * (D k).taylorDecrement P.p (s k) :=
        mul_pos P.κs_pos (hdpos k hkκ.le)
      exact ⟨hstep k hkκ, fun _ => ⟨hpos', le_rfl, by simp [hfxs, hpos'.le],
        by simp [hfx, hpos'.le], fun h => absurd trivial h⟩⟩
  refine ⟨f, hb, hf, X, fun _ => P.σ₀, fun _ => P.δ₀, fun _ => P.δ₀, fun _ => P.δ₀, fun _ => P.h₀,
    D, w,
    fun _ => P.q, s, fun _ => False, fx, fxs, fun k => P.κs * (D k).taylorDecrement P.p (s k),
    fun _ => True, hrun, fun k => ⟨rfl, rfl, rfl⟩, fun Lb hLb k _ _ => ⟨fun h => h.elim,
      fun _ j hj => ?_⟩, ⟨(hstop κ le_rfl).2 rfl, hnstop⟩, ?_, ?_⟩
  · have hM : 1 ≤ max Lb P.σ₀ := hLb.trans (le_max_left _ _)
    change P.ς * P.θ * ε / (24 * max Lb P.σ₀) ≤ P.δ₀ j
    rw [hδ₀ j hj, div_le_iff₀ (by positivity)]
    have h0 : P.ς * P.θ ≤ 1 := (mul_le_of_le_one_left P.θ_pos.le P.ς_le_one).trans P.θ_lt_one.le
    have h1 : P.ς * P.θ * ε ≤ ε := mul_le_of_le_one_left hε.le h0
    have h2 : ε ≤ ε * (24 * max Lb P.σ₀) := le_mul_of_one_le_right hε.le
      (hM.trans (le_mul_of_one_le_left (zero_le_one.trans hM) (by norm_num)))
    exact h1.trans h2
  · rw [edaFunEvalCount, card_filter_range_of_forall fun _ _ => not_false,
      card_filter_range_of_forall fun _ _ => ⟨not_false, trivial⟩, Nat.cast_add]
    linarith only [hκge]
  · rw [derivEvalCount_of_forall fun i hi => Or.inr ⟨not_false, by
      rw [← hρ, hρ1 i hi]; exact P.η₁_le_η₂.trans P.η₂_lt_one.le⟩, Nat.cast_add, Nat.cast_one]
    linarith only [hκge]

/-- **A slow ARqpIDA run in the lower-bound mode** of the radii control on `X = ℝ¹` with exact
derivatives, for `q = p ≥ 3` (order `q(p+1)/p = p+1`). There are `f_low`, `L ≥ 1` and `ε₀ > 0`
such that, for every `ε ∈ (0, ε₀]` (all `ε_j = ε`) and all ARqpIDA constants with `q = p`, weight
`σ₀ = p`, initial radii `δ₀ = ε` and initial accuracies `0 < h_{0,i} ≤ κ_s ε^{p-i+1}`, there is a
`C^p` function `f ≥ f_low` with `L`-Lipschitz derivatives of orders `0, …, p` and an ARqpIDA run
with exact derivatives from `x₀ = 0` satisfying the radii control in the lower-bound mode
(`Optimization.ARqpDARadiiControl False`), whose first iterate that is `(ε, δ)`-approximately
optimal for some radii `δ ∈ (0, 1]^q` (`Optimization.arqpIDATest`) is `x_{k_ε}`,
`k_ε = ⌈ε^{-(p+1)}⌉`, after `k_ε + 1 ≥ ε^{-(p+1)} + 1` function and derivative evaluations. The
run follows the slow example of [cartis2022evaluation], Theorem 12.2.15 with `q = p` (pure
`p`-th order spikes `f^{(p)}(x_k) = -(ε + ω_k)`, which fail the criterion at every radius; steps
the global model minimizers `t*_k = ε + ω_k`, `σ_k = σ₀`, `ρ_k = 1`) with Step-2 radii
`δ_{s_k} = ε/p`, at which the model measures at its minimizer vanish
(`Optimization.taylorMeasure_topMonomialRegModel_eq_zero`), and continues after `k_ε` as any
ARqpIDA iteration from the state at `k_ε` (`Optimization.exists_arqpDA_steps`). -/
theorem exists_isARqpIDARun_slowTop {p : ℕ} (hp : 3 ≤ p) :
    ∃ flow L ε₀ : ℝ, 1 ≤ L ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ P : ARqpIDAParams,
      P.p = p → P.q = p → P.σ₀ = p → (∀ j ∈ Finset.Icc 1 p, P.δ₀ j = ε) →
      (∀ i ∈ Finset.Icc 1 p, 0 < P.h₀ i ∧ P.h₀ i ≤ P.κs * ε ^ (p - i + 1)) →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, (∀ y, flow ≤ f y) ∧
        LipschitzDerivsAnchored f univ univ 0 p (fun _ => L) ∧
        ∃ (x : ℕ → EuclideanSpace ℝ (Fin 1)) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ)
          (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 1)) ℝ)
          (dd : ℕ → ℕ → EuclideanSpace ℝ (Fin 1)) (jk : ℕ → ℕ)
          (s : ℕ → EuclideanSpace ℝ (Fin 1)) (acc : ℕ → Prop),
          IsARqpIDARun f univ (fun _ => 0) P (fun _ => ε) 0 x σ δ δ₁ δs h D dd jk s
            acc ∧
          (∀ k, D k = ftaylorSeries ℝ f (x k)) ∧
          (∀ k, ARqpDARadiiControl False P (fun _ => ε)
            (lipMax (fun _ => L) P.p + ordMax P.p (fun _ => 0) * P.κh) σ δs s acc k) ∧
          IsFirstHit (arqpIDATest f univ P (fun _ => ε) x) ⌈(ε ^ (p + 1))⁻¹⌉₊ ∧
          (ε ^ (p + 1))⁻¹ + 1 ≤ (derivEvalCount (fun i => ¬ acc i) ⌈(ε ^ (p + 1))⁻¹⌉₊ : ℝ) ∧
          (ε ^ (p + 1))⁻¹ + 1 ≤ (derivEvalCount
            (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i))
              ⌈(ε ^ (p + 1))⁻¹⌉₊ : ℝ) := by
  obtain ⟨flow, L, hL, H⟩ := exists_slowARqp_ridge (p := p) (q := p) (by omega) le_rfl
    (lam := 1) one_pos le_rfl
  refine ⟨flow, L, 1 / 4, hL, by norm_num, fun ε hε hε4 P hPp hPq hσ hδ₀ hh₀ => ?_⟩
  have hR1 : ((p - p + 1 : ℕ) : ℝ) = 1 := by simp
  have hκeq : ⌈ε ^ (-((p + 1 : ℝ) / ((p - p + 1 : ℕ) : ℝ)))⌉₊ = ⌈(ε ^ (p + 1))⁻¹⌉₊ := by
    rw [hR1, div_one, Real.rpow_neg hε.le,
      show ((p : ℝ) + 1) = ((p + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  set κ := ⌈(ε ^ (p + 1))⁻¹⌉₊ with hκ
  have hκge : (ε ^ (p + 1))⁻¹ ≤ κ := Nat.le_ceil _
  have hκ1 : 1 ≤ κ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by positivity)).ne'
  have hκpos : (0 : ℝ) < κ := by exact_mod_cast hκ1
  have hε1 : ε ≤ 1 := by linarith
  have hp1 : 1 ≤ p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp1
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
  -- the levels, the steps and the points
  set a : ℕ → ℝ := fun k => 1 * (ε + ε * ((κ : ℝ) - k) / κ) with ha
  set t : ℕ → ℝ := fun k => a k ^ (1 / ((p - p + 1 : ℕ) : ℝ)) with ht
  have ht_eq : ∀ k, t k = a k := fun k => by simp only [ht, hR1, div_one, Real.rpow_one]
  set xr : ℕ → ℝ := fun k => ∑ i ∈ Finset.range k, t i with hxr
  have hxr1 : ∀ k, xr (k + 1) = xr k + t k := fun k => Finset.sum_range_succ _ _
  obtain ⟨g, hgc, hb, hf, hspike, hval⟩ := H ε hε hε1 xr fun k hk => by
    rw [hκeq] at hk; rw [hxr1, hκeq]
  rw [hκeq] at hspike hval
  have ha_ge : ∀ k ≤ κ, ε ≤ a k := fun k hk => by
    have := slowGap_nonneg hε.le hk; simp only [ha]; linarith
  have ha_gt : ∀ k < κ, ε < a k := fun k hk => by
    have := slowGap_pos hε hk; simp only [ha]; linarith
  have ha_le : ∀ k ≤ κ, a k ≤ 2 * ε := fun k hk => by
    have := slowGap_le hε.le κ k; simp only [ha]; linarith
  have ha0 : a 0 = 2 * ε := by
    simp only [ha, Nat.cast_zero, sub_zero]; rw [mul_div_assoc, div_self hκpos.ne']; ring
  have ha_eq : a κ = ε := by simp only [ha]; rw [sub_self, mul_zero, zero_div, add_zero, one_mul]
  -- the function and its Taylor data
  subst hPp
  set f : EuclideanSpace ℝ (Fin 1) → ℝ := ridge g e₀ with hfdef
  set X : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => xr k • e₀ with hX
  set s : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => t k • e₀ with hs
  have hXs : ∀ k, X (k + 1) = X k + s k := fun k => by simp only [hX, hs, hxr1, add_smul]
  have hspX : ∀ k ≤ κ, IsSpikeJetOf P.p g P.q ⟪e₀, X k⟫ (a k) := fun k hk => by
    rw [inner_single_smul_self, hPq]; exact hspike k hk
  have hgp : ContDiff ℝ P.p g := hgc
  have hqp : P.q = P.p := hPq
  have hdec : ∀ k ≤ κ, ∀ j ≤ P.q, ∀ d, (ftaylorSeries ℝ f (X k)).taylorDecrement j d =
      (if j = P.q then a k / P.q ! else 0) * ⟪e₀, d⟫ ^ P.q := fun k hk j hj d => by
    have hspXq : IsSpikeJetOf P.q g P.q ⟪e₀, X k⟫ (a k) := by rw [hqp]; rw [hqp] at hspX
                                                              exact hspX k hk
    have hgq : ContDiff ℝ P.q g := by rw [hqp]; exact hgp
    rcases hj.lt_or_eq with hjq | rfl
    · rw [ite_eq_right hjq.ne, zero_mul]
      exact taylorDecrement_ridge_of_lt hgq hjq hspXq d
    · rw [ite_eq_left rfl, taylorDecrement_ridge_spike hgq P.one_le_q le_rfl hspXq]
      ring
  have hdecp : ∀ k ≤ κ, ∀ d, (ftaylorSeries ℝ f (X k)).taylorDecrement P.p d =
      a k / P.q ! * ⟪e₀, d⟫ ^ P.q := fun k hk d => by
    rw [taylorDecrement_ridge_spike hgp P.one_le_q P.q_le_p (hspX k hk)]
    ring
  have hmeas : ∀ k ≤ κ, ∀ j ∈ Finset.Icc 1 P.q, ∀ t' : ℝ, 0 ≤ t' →
      taylorMeasure (ftaylorSeries ℝ f (X k)) j t' univ =
        (if j = P.q then a k / P.q ! else 0) * t' ^ P.q := fun k hk j hj t' ht' =>
    slowARqp_taylorMeasure_eq (D := fun i => ftaylorSeries ℝ f (X i)) (norm_single_one 0)
        (by linarith [ha_ge k hk])
      (hdec k hk) (Finset.mem_Icc.1 hj).2 ht'
  have hσ₀ : 0 < P.σ₀ := P.σ₀_pos
  have hmin : ∀ k ≤ κ, IsMinOn (regularizedModel (ftaylorSeries ℝ f (X k)) P.p P.σ₀) univ
      (s k) := fun k hk => by
    obtain ⟨hm, -, -⟩ := isMinOn_neg_monomial_add_regularization P.one_le_q P.q_le_p hσ₀
      (by linarith [ha_ge k hk] : 0 < a k)
    have e : (a k / (P.σ₀ * (P.q - 1)! / P.p !)) ^ (1 / ((P.p - P.q + 1 : ℕ) : ℝ)) = t k := by
      rw [ht_eq, hqp, Nat.sub_self, zero_add, Nat.cast_one, div_one, Real.rpow_one, hσ]
      obtain ⟨n, hn⟩ : ∃ n, P.p = n + 1 := ⟨P.p - 1, by omega⟩
      rw [hn, Nat.add_sub_cancel, Nat.factorial_succ]
      push_cast
      field_simp
    rw [e] at hm
    intro y _
    simp only [mem_ofPred_eq]
    rw [regularizedModel_ridge_spike norm_eq_abs_inner_single hgp P.one_le_q P.q_le_p (hspX k hk),
      ridge_apply, ridge_apply, show s k = t k • e₀ from rfl, inner_single_smul_self 0 (t k)]
    exact (add_le_add_iff_left _).2 (isMinOn_iff.1 hm _ (mem_univ _))
  have hmodel : ∀ k ≤ κ, ∀ ℓ ∈ Finset.Icc 1 P.q, ∀ d, ‖d‖ ≤ ε / P.p →
      (ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ f (X k)) P.p P.σ₀) (s k)).taylorDecrement
        ℓ d ≤ 0 := fun k hk ℓ hℓ d hd => by
    have hℓp : ℓ ≤ P.p := (Finset.mem_Icc.1 hℓ).2.trans P.q_le_p
    rw [show s k = t k • e₀ from rfl, taylorDecrement_regularizedModel_ridge_spike
        (norm_single_one 0)
      norm_eq_abs_inner_single hgp P.one_le_q P.q_le_p (hspX k hk) hℓp, ht_eq, hσ, hqp]
    have h0 := taylorMeasure_topMonomialRegModel_eq_zero (p := P.p) (j := ℓ)
      ⟨(Finset.mem_Icc.1 hℓ).1, hℓp⟩ (a := a k) (δ := ε / P.p) (by linarith [ha_ge k hk])
      (by
        have : ((P.p : ℝ) - 1) * (ε / P.p) ≤ ε := by
          rw [mul_div_assoc', div_le_iff₀ hpR]; nlinarith
        linarith [ha_ge k hk])
    have hle := taylorDecrement_le_taylorMeasure
      (ftaylorSeries ℝ (negMonomialRegModel P.p P.p P.p (a k)) (a k)) ℓ
      (S := univ) (δ := ε / P.p) (d := ⟪e₀, d⟫)
      ⟨mem_closedBall_zero_iff.2 (show ‖⟪e₀, d⟫‖ ≤ ε / P.p by
        rw [Real.norm_eq_abs, ← norm_eq_abs_inner_single]; exact hd), mem_univ _⟩
    rw [h0] at hle
    exact hle
  have hnorm_s : ∀ k ≤ κ, ‖s k‖ = a k := fun k hk => by
    rw [show s k = t k • e₀ from rfl, norm_smul_single, ht_eq,
      abs_of_pos (by linarith [ha_ge k hk])]
  have hdecs : ∀ k ≤ κ, (ftaylorSeries ℝ f (X k)).taylorDecrement P.p (s k) =
      a k / P.q ! * t k ^ P.q := fun k hk => by rw [hdecp k hk, hs, inner_single_smul_self]
  have hfval : ∀ k < κ, f (X k) - f (X k + s k) =
      (ftaylorSeries ℝ f (X k)).taylorDecrement P.p (s k) := fun k hk => by
    rw [hdecs k hk.le, ← hXs, hfdef, ridge_apply, ridge_apply, hX, inner_single_smul_self,
        inner_single_smul_self,
      hval k hk, hxr1, hqp]
    ring
  have hdpos : ∀ k ≤ κ, 0 < (ftaylorSeries ℝ f (X k)).taylorDecrement P.p (s k) := fun k hk => by
    rw [hdecs k hk, ht_eq]
    have := ha_ge k hk
    have : 0 < a k := by linarith
    positivity
  -- the continuation from the state at `κ`
  have hεv : ∀ j ∈ Finset.Icc 1 P.q, (fun _ : ℕ => ε) j ∈ Set.Ioc 0 1 := fun _ _ => ⟨hε, hε1⟩
  have hεp : 0 < ε / P.p := div_pos hε hpR
  have hεp1 : ε / P.p ≤ 1 := (div_le_self hε.le (by linarith)).trans hε1
  have hεpε : ε / P.p ≤ ε := div_le_self hε.le (by linarith)
  obtain ⟨x', σ', δ', δ₁', δs', h', dd', jk', s', acc', hx'0, hσ'0, hδ'0, hh'0, -, hr, hrc'⟩ :=
    exists_arqpDA_steps (P := P) (ε := fun _ => ε)
      (fun y _ => ftaylorSeries ℝ f y) (κg := fun _ => 0) (L := fun _ => L)
      hf (fun _ _ => hL) hεv
      (fun _ _ => le_rfl) (X κ) P.σmin_le_σ₀ (δ' := fun _ => ε / P.p)
      (fun _ _ => ⟨hεp, hεp1⟩) (fun i hi => ⟨(hh₀ i hi).1, P.h₀_le i hi⟩)
      fun _ _ _ => (jetApprox_self _ _).mono_err fun i _ => by simp
  -- the iterations up to `κ`
  set rad : ℕ → ℝ := fun k => if k = 0 then ε else ε / P.p with hrad
  set δp : ℕ → ℕ → ℝ := fun k => if k = 0 then P.δ₀ else fun _ => ε / P.p with hδp
  set ddp : ℕ → ℕ → EuclideanSpace ℝ (Fin 1) :=
    fun k j => if j = P.q then rad k • e₀ else 0 with hddp
  have hδrad : ∀ k, ∀ j ∈ Finset.Icc 1 P.q, δp k j = rad k := fun k j hj => by
    by_cases h0 : k = 0
    · simp only [hδp, hrad, h0, ite_true]; rw [← hPq] at hδ₀; exact hδ₀ j hj
    · simp only [hδp, hrad, h0, ite_false]
  have hδsucc : ∀ k, δp (k + 1) = fun _ => ε / P.p := fun k => by
    simp only [hδp, Nat.succ_ne_zero, ite_false]
  have hρp : ∀ k < κ, arqpIDARatio f P (fun i => ftaylorSeries ℝ f (X i)) X s k = 1 :=
    fun k hk => by rw [arqpIDARatio, reductionRatio_def, hfval k hk, div_self (hdpos k hk.le).ne']
  have hrad_pos : ∀ k, 0 < rad k := fun k => by
    simp only [hrad]; split_ifs <;> positivity
  have hpre : ∀ k < κ, ARqpDAStep univ P (fun _ => ε) X (fun _ => P.σ₀) δp δp
      (fun _ _ => ε / P.p) (fun _ => P.h₀) (fun i => ftaylorSeries ℝ f (X i)) ddp (fun _ => P.q) s
      (fun _ => False) (arqpIDARatio f P (fun i => ftaylorSeries ℝ f (X i)) X s) k := by
    intro k hk
    have hrk : rad k ≤ a k - ε / 4 := by
      simp only [hrad]
      split_ifs with h0
      · rw [h0, ha0]; linarith
      · have := ha_ge k hk.le
        have : ε / P.p ≤ ε / 3 := div_le_div_of_nonneg_left hε.le (by norm_num) hp3
        linarith
    refine slowARqpTop_arqpDAStep (r := rad k) (r' := ε / P.p) (a := a k) (norm_single_one 0) hε
      (by linarith [ha_ge k hk.le]) (hrad_pos k) hεp hεp1 ?_ (hδrad k) (hδsucc k) rfl
      (fun j _ => rfl) rfl rfl (hdec k hk.le) (hdecp k hk.le) (hmin k hk.le) (hmodel k hk.le)
      (by rw [hnorm_s k hk.le]; linarith [ha_le k hk.le]) (fun i hi => ?_) not_false (hXs k) rfl
      P.σmin_le_σ₀ rfl (hρp k hk)
    · rw [hσ, hqp]
      have hrk0 := (hrad_pos k).le
      have hf1 : ((P.p + 1)! : ℝ) = (P.p + 1) * P.p ! := by push_cast [Nat.factorial_succ]; ring
      have hpf : (0 : ℝ) < P.p ! := by positivity
      rw [pow_succ, hf1]
      have hrk' : rad k ≤ a k - P.ς * ε / 4 := by
        have := P.ς_le_one; nlinarith
      have h1 : (P.p : ℝ) / ((P.p + 1) * P.p !) * (rad k ^ P.p * rad k) =
          rad k ^ P.p / P.p ! * (P.p / (P.p + 1) * rad k) := by field_simp
      rw [h1]
      have h2 : (P.p : ℝ) / (P.p + 1) * rad k ≤ rad k := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
      calc rad k ^ P.p / P.p ! * (P.p / (P.p + 1) * rad k) ≤ rad k ^ P.p / P.p ! * rad k :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ ≤ rad k ^ P.p / P.p ! * (a k - P.ς * ε / 4) :=
            mul_le_mul_of_nonneg_left hrk' (by positivity)
        _ = (a k - P.ς * ε / 4) / P.p ! * rad k ^ P.p := by ring
    · rw [hnorm_s k hk.le]
      refine (hh₀ i hi).2.trans (mul_le_mul_of_nonneg_left ?_ P.κs_pos.le)
      exact pow_le_pow_left₀ hε.le (ha_ge k hk.le) _
  have hδκ : δ' 0 = δp κ := by
    rw [hδ'0]; simp only [hδp, show κ ≠ 0 by omega, ite_false]
  -- the spliced run
  set Xv := Nat.seqAppend κ X x' with hXv
  set σv := Nat.seqAppend κ (fun _ => P.σ₀) σ' with hσv
  set δv := Nat.seqAppend κ δp δ' with hδv
  set δ₁v := Nat.seqAppend κ δp δ₁' with hδ₁v
  set δsv := Nat.seqAppend κ (fun _ _ => ε / P.p) δs' with hδsv
  set hv := Nat.seqAppend κ (fun _ => P.h₀) h' with hhv
  set ddv := Nat.seqAppend κ ddp dd' with hddv
  set jkv := Nat.seqAppend κ (fun _ => P.q) jk' with hjkv
  set sv := Nat.seqAppend κ s s' with hsv
  set accv := Nat.seqAppend κ (fun _ => False) acc' with haccv
  set Dv : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 1)) ℝ :=
    fun i => ftaylorSeries ℝ f (Xv i) with hDvdef
  have hDv : ∀ k, Dv k = ftaylorSeries ℝ f (Xv k) := fun _ => rfl
  have hstep : ∀ k, ARqpDAStep univ P (fun _ => ε) Xv σv δv δ₁v δsv hv Dv ddv jkv sv accv
      (arqpIDARatio f P Dv Xv sv) k :=
    ARqpDAStep.seqAppend hpre hr hx'0 hσ'0 hδκ hh'0
  have hXle : ∀ k ≤ κ, Xv k = X k := fun k hk => Nat.seqAppend_eq_of_le hx'0 hk
  have hσle : ∀ k ≤ κ, σv k = P.σ₀ := fun k hk => Nat.seqAppend_eq_of_le hσ'0 hk
  have hhle : ∀ k ≤ κ, hv k = P.h₀ := fun k hk => Nat.seqAppend_eq_of_le hh'0 hk
  have hnacc : ∀ k < κ, ¬ accv k := fun k hk => by
    rw [haccv, Nat.seqAppend_of_lt hk]; exact not_false
  have hρ1 : ∀ k < κ, arqpIDARatio f P Dv Xv sv k = 1 := fun k hk => by
    rw [← hρp k hk]; simp only [arqpIDARatio, hDv, hXle k hk.le, hsv, Nat.seqAppend_of_lt hk]
  have hrun' : IsARqpIDARun f univ (fun _ => 0) P (fun _ => ε) 0 Xv σv δv δ₁v δsv
      hv Dv ddv jkv sv accv :=
    ⟨hεv, fun j hj => by rw [← hPq] at hδ₀; rw [hδ₀ j hj], fun _ _ => le_rfl,
      by rw [hXle 0 (Nat.zero_le _)]; simp [hX, hxr], mem_univ _,
      hσle 0 (Nat.zero_le _), by
        rw [hδv, Nat.seqAppend_of_lt (by omega)]; simp only [hδp, ite_true],
      hhle 0 (Nat.zero_le _),
      fun k => by rw [hDv]; exact (jetApprox_self _ _).mono_err fun i _ => by simp, hstep⟩
  have htest : ∀ k ≤ κ, (arqpIDATest f univ P (fun _ => ε) Xv k ↔ k = κ) := fun k hk => by
    rw [arqpIDATest_univ_iff_of_taylorMeasure_eq hε (c := a k) fun j hj t ht => by
      rw [hXle k hk]; exact hmeas k hk j hj t ht]
    refine ⟨fun hc => ?_, fun h => by rw [h, ha_eq]⟩
    by_contra hne
    linarith [ha_gt k (lt_of_le_of_ne hk hne)]
  refine ⟨f, hb, hf, Xv, σv, δv, δ₁v, δsv, hv, Dv, ddv, jkv, sv, accv, hrun', hDv,
    fun k hk' hs1 => ⟨fun h => h.elim, fun _ j hj => ?_⟩,
    ⟨(htest κ le_rfl).2 rfl, fun i hi ht' => hi.ne ((htest i hi.le).1 ht')⟩, ?_, ?_⟩
  · by_cases hkκ : k < κ
    · rw [hδsv, Nat.seqAppend_of_lt hkκ, hσv, Nat.seqAppend_of_lt hkκ, hσ]
      have hM : (P.p : ℝ) ≤ max (lipMax (fun _ => L) P.p + ordMax P.p (fun _ => 0) * P.κh) P.p :=
        le_max_right _ _
      have hM0 : (0 : ℝ) < max (lipMax (fun _ => L) P.p + ordMax P.p (fun _ => 0) * P.κh) P.p :=
        hpR.trans_le hM
      have h0 : P.ς * P.θ ≤ 1 := (mul_le_of_le_one_left P.θ_pos.le P.ς_le_one).trans P.θ_lt_one.le
      rw [div_le_div_iff₀ (by positivity) hpR]
      have h1 : P.ς * P.θ * ε ≤ ε := mul_le_of_le_one_left hε.le h0
      have h3 : (P.p : ℝ) ≤ 24 * max (lipMax (fun _ => L) P.p +
          ordMax P.p (fun _ => 0) * P.κh) P.p := hM.trans (le_mul_of_one_le_left hM0.le
            (by norm_num))
      calc P.ς * P.θ * ε * P.p ≤ ε * P.p := mul_le_mul_of_nonneg_right h1 hpR.le
        _ ≤ ε * (24 * max (lipMax (fun _ => L) P.p + ordMax P.p (fun _ => 0) * P.κh) P.p) :=
          mul_le_mul_of_nonneg_left h3 hε.le
    · rw [hδsv, Nat.seqAppend_of_le (not_lt.1 hkκ)]
      rw [haccv, Nat.seqAppend_of_le (not_lt.1 hkκ)] at hk'
      rw [hsv, Nat.seqAppend_of_le (not_lt.1 hkκ)] at hs1
      rw [hσv, Nat.seqAppend_of_le (not_lt.1 hkκ)]
      exact (hrc' (k - κ) hk' hs1).2 (by rw [hPq]; omega) j hj
  · rw [derivEvalCount_of_forall hnacc, Nat.cast_add, Nat.cast_one]; linarith only [hκge]
  · rw [derivEvalCount_of_forall fun i hi => Or.inr ⟨hnacc i hi, by
      rw [hρ1 i hi]; exact P.η₁_le_η₂.trans P.η₂_lt_one.le⟩, Nat.cast_add, Nat.cast_one]
    linarith only [hκge]

end Optimization

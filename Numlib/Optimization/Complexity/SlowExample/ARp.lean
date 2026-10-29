import Numlib.Analysis.InnerProductSpace.Normalize
import Numlib.Optimization.Complexity.SlowExample.Ridge
import Numlib.Optimization.Complexity.SlowExample.HighOrder
import Numlib.Optimization.ModelBased.ARpRun
import Numlib.Optimization.Optimality.Unconstrained

/-!
# Slow runs of ARp on one-dimensional spike data

The mechanism of the sharpness results for adaptive-regularization methods with `p`-th order
Taylor models of [cartis2022evaluation] (Theorems 3.3.6, 3.3.10, 4.1.6, 12.2.15): a function of
one variable whose jets at the points `x_k` have a single nonzero derivative ("spike jets", the
data of `Optimization.exists_slowTaylorOrder_interpolant`), lifted to a one-dimensional inner
product space along a unit vector `e` (`Optimization.ridge`), has the regularized Taylor model
`G(x_k) + negMonomialRegModel p q σ α t`, whose global minimizer is explicit
(`Optimization.isMinOn_neg_monomial_add_regularization`). Spacing the points by these minimizers
gives ARp runs with `σ_k = σ₀`, exact model minimization and `ρ_k = 1`.

## Main definitions

* `Optimization.monomialMinimizer p q σ α`: the minimizer `t* = (α/λ)^{1/(p-q+1)}`,
  `λ = σ (q-1)!/p!`.

## Main statements

* `Optimization.taylorPolynomial_ridge_spike`, `Optimization.regularizedModel_ridge_spike`: the
  Taylor polynomial and the model of a ridge function at a spike jet.
* `Optimization.taylorMeasure_eq_mul_pow_of_inner_pow`: the measure of a decrement
  `a ⟪e, d⟫^q` along a unit vector.
* `Optimization.iteratedDeriv_three_negMonomialRegModel_mem`,
  `Optimization.iteratedDeriv_two_negMonomialRegModel_mem`: the derivatives of the model at `t*`
  used by the third-order step condition (4.1.13) and the sets (4.1.14).
* `Optimization.ridge_const_mul_slow_bounds`: scaled ridges of the slow interpolants satisfy the
  Lipschitz and lower bounds of the function classes, with constants independent of `ε`.
* `Optimization.taylorDecrement_regularizedModel_ridge_spike`: the model decrements at a spike
  jet along the ridge are those of the one-dimensional monomial model.
* `Optimization.taylorDecrement_regularizedModel_ridge_linear_nonpos`: at a gradient spike the
  model decrements at its minimizer are nonpositive on small balls (Example 12.1.3).
* `Optimization.isARpStep_of_isMinOn`: global model minimizers are admissible ARp steps.
* `Optimization.arp_ridge_run`: the ARp run on spike data.
-/

open Set Finset
open scoped Nat RealInnerProductSpace

namespace Optimization

/-! ### One-dimensional spike jets and the monomial model -/

/-- The regularized monomial model is `C^p`. -/
theorem contDiff_negMonomialRegModel (p q : ℕ) (σ α : ℝ) :
    ContDiff ℝ p (negMonomialRegModel p q σ α) := by
  have h := contDiff_norm_pow (E := ℝ) (r := p + 1) (by omega)
  rw [Nat.add_sub_cancel] at h
  have : negMonomialRegModel p q σ α = fun t => -α * t ^ q / q ! +
      σ * ‖t‖ ^ (p + 1) / (p + 1)! := by
    funext t; simp [negMonomialRegModel, Real.norm_eq_abs]
  rw [this]
  exact ((contDiff_const.mul (contDiff_id.pow q)).div_const _).add
    ((contDiff_const.mul h).div_const _)

/-- The global minimizer `t* = (α/λ)^{1/(p-q+1)}`, `λ = σ (q-1)!/p!`, of the one-dimensional
model `negMonomialRegModel p q σ α`. -/
noncomputable def monomialMinimizer (p q : ℕ) (σ α : ℝ) : ℝ :=
  (α / (σ * (q - 1)! / p !)) ^ (1 / ((p - q + 1 : ℕ) : ℝ))

section Minimizer

variable {p q : ℕ} {σ α : ℝ}

theorem monomialMinimizer_pos (hσ : 0 < σ) (hα : 0 < α) : 0 < monomialMinimizer p q σ α := by
  unfold monomialMinimizer
  exact Real.rpow_pos_of_pos (by positivity) _

/-- `α = σ (q-1)!/p! t*^{p-q+1}`. -/
theorem eq_mul_monomialMinimizer_pow (hσ : 0 < σ) (hα : 0 < α) :
    α = σ * (q - 1)! / p ! * monomialMinimizer p q σ α ^ (p - q + 1) := by
  have hl : 0 < σ * (q - 1)! / p ! := by positivity
  have hR : ((p - q + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [monomialMinimizer, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
    one_div_mul_cancel hR, Real.rpow_one]
  field_simp

/-- The third derivative of the monomial model at its minimizer (for `q ≤ 3 ≤ p`):
`0 ≤ m'''(t*) ≤ σ t*^{p-2}/(p-2)!`. -/
theorem iteratedDeriv_three_negMonomialRegModel_mem (hq : 1 ≤ q) (hq3 : q ≤ 3) (hp : 3 ≤ p)
    (hσ : 0 < σ) (hα : 0 < α) :
    0 ≤ iteratedDeriv 3 (negMonomialRegModel p q σ α) (monomialMinimizer p q σ α) ∧
      iteratedDeriv 3 (negMonomialRegModel p q σ α) (monomialMinimizer p q σ α) ≤
        σ * monomialMinimizer p q σ α ^ (p - 2) / (p - 2)! := by
  have hj := (isMinOn_neg_monomial_add_regularization hq (hq3.trans hp) hσ hα).2.2 3
  rw [← monomialMinimizer] at hj
  have hαe := eq_mul_monomialMinimizer_pow (p := p) (q := q) hσ hα
  set t := monomialMinimizer p q σ α
  have ht := monomialMinimizer_pos (p := p) (q := q) hσ hα
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 3 := ⟨p - 3, by omega⟩
  have e1 : m + 3 + 1 - 3 = m + 1 := by omega
  have e2 : m + 3 - 2 = m + 1 := by omega
  rw [hj, e1, e2, ite_eq_left (by omega : 3 ≤ m + 3 + 1)]
  have hpos : 0 ≤ σ * t ^ (m + 1) / ((m + 1)! : ℝ) := by positivity
  rcases (by omega : q < 3 ∨ q = 3) with hq' | rfl
  · rw [ite_eq_right (by omega), zero_add]
    exact ⟨hpos, le_rfl⟩
  · rw [ite_eq_left le_rfl]
    have e3 : m + 3 - 3 + 1 = m + 1 := by omega
    rw [e3] at hαe
    have hf : ((m + 3)! : ℝ) = (m + 3) * (m + 2) * (m + 1)! := by
      push_cast [Nat.factorial_succ]; ring
    simp only [Nat.sub_self, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
    rw [hαe, hf]
    have hm : (0 : ℝ) < (m + 1)! := by positivity
    constructor
    · rw [show (3 - 1)! = 2 by rfl]
      have : (2 : ℝ) ≤ (m + 3) * (m + 2) := by nlinarith
      rw [show (((2 : ℕ) : ℝ)) = 2 by norm_num]
      have h1 : σ * 2 / ((m + 3) * (m + 2) * (m + 1)!) * t ^ (m + 1) ≤
          σ * t ^ (m + 1) / (m + 1)! := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hm]
        have : 0 ≤ σ * t ^ (m + 1) * (m + 1)! := by positivity
        nlinarith
      linarith
    · have : 0 ≤ σ * ((3 - 1)! : ℝ) / ((m + 3) * (m + 2) * (m + 1)!) * t ^ (m + 1) := by
        positivity
      linarith

/-- The second derivative of the monomial model with `q = 3` at its minimizer:
`0 ≤ m''(t*) ≤ σ t*^{p-1}/(p-1)!`. -/
theorem iteratedDeriv_two_negMonomialRegModel_mem (hp : 3 ≤ p) (hσ : 0 < σ) (hα : 0 < α) :
    0 ≤ iteratedDeriv 2 (negMonomialRegModel p 3 σ α) (monomialMinimizer p 3 σ α) ∧
      iteratedDeriv 2 (negMonomialRegModel p 3 σ α) (monomialMinimizer p 3 σ α) ≤
        σ * monomialMinimizer p 3 σ α ^ (p - 1) / (p - 1)! := by
  have hj := (isMinOn_neg_monomial_add_regularization (q := 3) (by norm_num) hp hσ hα).2.2 2
  rw [← monomialMinimizer] at hj
  have hαe := eq_mul_monomialMinimizer_pow (p := p) (q := 3) hσ hα
  set t := monomialMinimizer p 3 σ α
  have ht := monomialMinimizer_pos (p := p) (q := 3) hσ hα
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 3 := ⟨p - 3, by omega⟩
  have e1 : m + 3 + 1 - 2 = m + 2 := by omega
  have e2 : m + 3 - 1 = m + 2 := by omega
  have e3 : m + 3 - 3 + 1 = m + 1 := by omega
  rw [hj, e1, e2, ite_eq_left (by omega : 2 ≤ m + 3 + 1), ite_eq_left (by norm_num : 2 ≤ 3)]
  rw [e3] at hαe
  have hf : ((m + 3)! : ℝ) = (m + 3) * (m + 2)! := by
    push_cast [Nat.factorial_succ]; ring
  simp only [show 3 - 2 = 1 by rfl, pow_one, show (1 : ℕ)! = 1 by rfl, Nat.cast_one, div_one]
  rw [hαe, hf]
  have hm : (0 : ℝ) < (m + 2)! := by positivity
  have htp : t ^ (m + 1) * t = t ^ (m + 2) := by ring
  rw [show (3 - 1)! = 2 by rfl, show (((2 : ℕ) : ℝ)) = 2 by norm_num]
  have hrw : -(σ * 2 / ((m + 3) * (m + 2)!) * t ^ (m + 1)) * t =
      -(σ * 2 / ((m + 3) * (m + 2)!) * t ^ (m + 2)) := by rw [← htp]; ring
  rw [hrw]
  constructor
  · have h1 : σ * 2 / ((m + 3) * (m + 2)!) * t ^ (m + 2) ≤ σ * t ^ (m + 2) / (m + 2)! := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hm]
      have : 0 ≤ σ * t ^ (m + 2) * (m + 2)! := by positivity
      nlinarith
    linarith
  · have : 0 ≤ σ * 2 / ((m + 3) * ((m + 2)! : ℝ)) * t ^ (m + 2) := by positivity
    linarith

end Minimizer

section Ridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {e : E}

/-- **Bounds for scaled ridges of slow-example interpolants**: if `G` is `C^p` with
`L`-Lipschitz `p`-th derivative and `|G^{(j)}| ≤ B` for `j ≤ p` (the output of the interpolation
lemmas of `Numlib.Optimization.Complexity.SlowExample.HighOrder`), then for `λ ∈ (0, 1]` and
`‖e‖ ≤ 1` the ridge `f = λ G(⟪e, ·⟫)` is `C^p`, bounded below by `-B`, and its derivatives of
orders `0, …, p` are `max(1, L, B)`-Lipschitz. -/
theorem ridge_const_mul_slow_bounds {G : ℝ → ℝ} {p : ℕ} (hG : ContDiff ℝ p G) {L B lam : ℝ}
    (hB : 0 ≤ B)
    (hGL : ∀ s t, |iteratedDeriv p G s - iteratedDeriv p G t| ≤ L * |s - t|)
    (hGB : ∀ j ≤ p, ∀ t, |iteratedDeriv j G t| ≤ B) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (he : ‖e‖ ≤ 1) :
    ContDiff ℝ p (ridge (fun t => lam * G t) e) ∧ (∀ y, -B ≤ ridge (fun t => lam * G t) e y) ∧
      ∀ j ≤ p, IteratedFDerivLipschitzOn (ridge (fun t => lam * G t) e) j (max 1 (max L B))
        univ := by
  have hgc : ContDiff ℝ p (fun t => lam * G t) := contDiff_const.mul hG
  have hgj : ∀ j t, iteratedDeriv j (fun t => lam * G t) t = lam * iteratedDeriv j G t :=
    fun j t => iteratedDeriv_const_mul_field lam G
  have hM0 : 0 ≤ max 1 (max L B) := zero_le_one.trans (le_max_left _ _)
  have hlip : ∀ j ≤ p, ∀ s t, |iteratedDeriv j (fun t => lam * G t) s -
      iteratedDeriv j (fun t => lam * G t) t| ≤ max 1 (max L B) * |s - t| := by
    intro j hj s t
    rcases hj.lt_or_eq with hjp | rfl
    · refine (abs_iteratedDeriv_sub_le hgc hjp (B := B) (fun t => ?_) s t).trans
        (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) (abs_nonneg _))
      rw [hgj, abs_mul, abs_of_pos hlam]
      exact (mul_le_of_le_one_left (abs_nonneg _) hlam1).trans (hGB (j + 1) hjp t)
    · rw [hgj, hgj, ← mul_sub, abs_mul, abs_of_pos hlam]
      calc lam * |iteratedDeriv j G s - iteratedDeriv j G t| ≤ 1 * (L * |s - t|) :=
            mul_le_mul hlam1 (hGL s t) (abs_nonneg _) zero_le_one
        _ ≤ max 1 (max L B) * |s - t| := by
            rw [one_mul]
            exact mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _))
              (abs_nonneg _)
  refine ⟨contDiff_ridge hgc, fun y => ?_, fun j hj =>
    iteratedFDerivLipschitzOn_ridge hgc (by exact_mod_cast hj) he hM0 (hlip j hj)⟩
  have h0 := hGB 0 (Nat.zero_le p) ⟪e, y⟫
  rw [iteratedDeriv_zero] at h0
  rw [ridge_apply]
  nlinarith [(abs_le.1 h0).1, (abs_le.1 h0).2]

/-- The Taylor measure over the ball of radius `δ` of a decrement `d ↦ a ⟪e, d⟫^q` (`a ≥ 0`,
`‖e‖ = 1`) is `a δ^q`. -/
theorem taylorMeasure_eq_mul_pow_of_inner_pow {D : FormalMultilinearSeries ℝ E ℝ} {j q : ℕ}
    {a δ : ℝ} (he : ‖e‖ = 1) (ha : 0 ≤ a) (hδ : 0 ≤ δ)
    (hdec : ∀ d, D.taylorDecrement j d = a * ⟪e, d⟫ ^ q) :
    taylorMeasure D j δ univ = a * δ ^ q := by
  rw [taylorMeasure, show D.taylorDecrement j = fun d => a * ⟪e, d⟫ ^ q from funext hdec]
  exact decrementMeasure_mul_inner_pow he ha hδ

section Spike

variable {p q : ℕ} {G : ℝ → ℝ} {x : E} {α : ℝ}

/-- At a spike jet, `T_{f,p}(x, s) = G(a) - α t^q/q!` with `a = ⟪e, x⟫`, `t = ⟪e, s⟫`. -/
theorem taylorPolynomial_ridge_spike (hG : ContDiff ℝ p G) (hq : 1 ≤ q) (hqp : q ≤ p)
    (hd : IsSpikeJetOf p G q ⟪e, x⟫ α) (s : E) :
    taylorPolynomial (ridge G e) p x s = G ⟪e, x⟫ - α * ⟪e, s⟫ ^ q / q ! := by
  rw [taylorPolynomial_ridge hG, Finset.sum_eq_add_of_mem 0 q (by simp) (by simp; omega)
    (by omega)]
  · rw [hd.1]; simp; ring
  · intro c hc hc'
    rw [hd.2 c (by omega) (by simp at hc; omega) hc'.2]
    simp

/-- At a spike jet the model (4.1.2) is `G(a) + negMonomialRegModel p q σ α t`. -/
theorem regularizedModel_ridge_spike (hspan : ∀ s : E, ‖s‖ = |⟪e, s⟫|) (hG : ContDiff ℝ p G)
    (hq : 1 ≤ q) (hqp : q ≤ p) (hd : IsSpikeJetOf p G q ⟪e, x⟫ α) (σ : ℝ) :
    regularizedModel (ftaylorSeries ℝ (ridge G e) x) p σ =
      ridge (fun t => G ⟪e, x⟫ + negMonomialRegModel p q σ α t) e := by
  funext s
  rw [regularizedModel_def, ← taylorPolynomial_eq_taylorSum,
    taylorPolynomial_ridge_spike hG hq hqp hd, hspan, ridge_apply,
    negMonomialRegModel]
  ring

theorem taylorDecrement_ridge_spike (hG : ContDiff ℝ p G) (hq : 1 ≤ q) (hqp : q ≤ p)
    (hd : IsSpikeJetOf p G q ⟪e, x⟫ α) (s : E) :
    (ftaylorSeries ℝ (ridge G e) x).taylorDecrement p s = α * ⟪e, s⟫ ^ q / q ! := by
  rw [FormalMultilinearSeries.taylorDecrement, ← taylorPolynomial_eq_taylorSum,
    taylorPolynomial_ridge_spike hG hq hqp hd,
    taylorPolynomial_ridge_spike hG hq hqp hd]
  simp only [inner_zero_right]
  rw [zero_pow (by omega)]
  ring

/-- Below the order `q` of a spike jet (`G^{(i)}(⟪e, x⟫) = 0` for `1 ≤ i < q`) the Taylor
decrements of the ridge function `ridge G e` at `x` vanish. -/
theorem taylorDecrement_ridge_of_lt {j : ℕ} (hG : ContDiff ℝ q G) (hjq : j < q)
    (hd : IsSpikeJetOf q G q ⟪e, x⟫ α) (s : E) :
    (ftaylorSeries ℝ (ridge G e) x).taylorDecrement j s = 0 := by
  have hGj : ContDiff ℝ j G := hG.of_le (by exact_mod_cast hjq.le)
  have hT : ∀ t : E, taylorPolynomial (ridge G e) j x t = G ⟪e, x⟫ := fun t => by
    rw [taylorPolynomial_ridge hGj, Finset.sum_eq_single 0]
    · simp
    · intro i hi hi0
      have hij : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      rw [hd.2 i (Nat.one_le_iff_ne_zero.2 hi0) (by omega) (by omega)]
      simp
    · simp
  rw [FormalMultilinearSeries.taylorDecrement, ← taylorPolynomial_eq_taylorSum, hT, hT, sub_self]

end Spike

section Run

variable {p q : ℕ} {G : ℝ → ℝ}

/-- The derivatives of the model at a spike jet: `∇^j m(s)[d]^j = m_1^{(j)}(t) ⟪e, d⟫^j` with
`m_1 = negMonomialRegModel p q σ α`, `t = ⟪e, s⟫`, for `1 ≤ j ≤ p`. -/
theorem iteratedFDeriv_regularizedModel_ridge_spike (hspan : ∀ s : E, ‖s‖ = |⟪e, s⟫|)
    (hG : ContDiff ℝ p G) (hq : 1 ≤ q)
    (hqp : q ≤ p) {x : E} {α : ℝ} (hd : IsSpikeJetOf p G q ⟪e, x⟫ α)
    (σ : ℝ) {j : ℕ} (hj : 1 ≤ j) (hjp : j ≤ p) (s d : E) :
    iteratedFDeriv ℝ j (regularizedModel (ftaylorSeries ℝ (ridge G e) x) p σ) s (fun _ => d) =
      iteratedDeriv j (negMonomialRegModel p q σ α) ⟪e, s⟫ * ⟪e, d⟫ ^ j := by
  rw [regularizedModel_ridge_spike hspan hG hq hqp hd, iteratedFDeriv_ridge_apply_diag
    (contDiff_const.add (contDiff_negMonomialRegModel p q σ α)) (by exact_mod_cast hjp),
    iteratedDeriv_const_add (by omega)]

/-- The Taylor decrements of the model at a spike jet, at a point `t e` along the ridge, are the
one-dimensional Taylor decrements of `negMonomialRegModel p q σ α` at `t` along `⟪e, d⟫`
(orders `ℓ ≤ p`). -/
theorem taylorDecrement_regularizedModel_ridge_spike (he : ‖e‖ = 1)
    (hspan : ∀ s : E, ‖s‖ = |⟪e, s⟫|) (hG : ContDiff ℝ p G) (hq : 1 ≤ q) (hqp : q ≤ p) {x : E}
    {α σ : ℝ} (hd : IsSpikeJetOf p G q ⟪e, x⟫ α) {ℓ : ℕ} (hℓp : ℓ ≤ p) (t : ℝ) (d : E) :
    (ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ (ridge G e) x) p σ) (t • e)).taylorDecrement
        ℓ d = (ftaylorSeries ℝ (negMonomialRegModel p q σ α) t).taylorDecrement ℓ ⟪e, d⟫ := by
  have hee : ⟪e, t • e⟫ = t := inner_smul_self_of_norm_eq_one he t
  rw [FormalMultilinearSeries.taylorDecrement_eq, FormalMultilinearSeries.taylorDecrement_eq]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨hi1, hiℓ⟩ := Finset.mem_Icc.1 hi
  rw [ftaylorSeries_real_apply]
  change (i ! : ℝ)⁻¹ * iteratedFDeriv ℝ i (regularizedModel (ftaylorSeries ℝ (ridge G e) x) p σ)
    _ (fun _ => d) = _
  rw [iteratedFDeriv_regularizedModel_ridge_spike hspan hG hq hqp hd σ hi1 (hiℓ.trans hℓp), hee]

/-- **The model at a gradient spike is approximately critical at its minimizer** (Example 12.1.3
along a ridge): if `G'(⟪e, x⟫) = -β < 0` and the derivatives of orders `2, …, p` vanish, then the
Taylor decrements of order `ℓ ∈ [1, p]` of the model `m_x` of `ridge G e` (weight `σ > 0`) at
the point `t* e`, `t* = (β p!/σ)^{1/p}` (the global minimizer of `m_x`,
`Optimization.isMinOn_neg_monomial_add_regularization`), are
nonpositive on the ball of radius `δ`, provided `ℓ ≤ 2` or `(p - 1) δ ≤ 3 t*`
(`Optimization.taylorMeasure_linearRegModel_eq_zero`). -/
theorem taylorDecrement_regularizedModel_ridge_linear_nonpos (he : ‖e‖ = 1)
    (hspan : ∀ s : E, ‖s‖ = |⟪e, s⟫|) (hp : 1 ≤ p) (hG : ContDiff ℝ p G) {x : E} {β σ δ : ℝ}
    (hβ : 0 < β) (hσ : 0 < σ) (hd : IsSpikeJetOf p G 1 ⟪e, x⟫ β) {ℓ : ℕ} (hℓ : ℓ ∈ Finset.Icc 1 p)
    (hrad : ℓ ≤ 2 ∨ ((p : ℝ) - 1) * δ ≤ 3 * (β * p ! / σ) ^ (1 / (p : ℝ)))
    {d : E} (hdδ : ‖d‖ ≤ δ) :
    (ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ (ridge G e) x) p σ)
      (((β * p ! / σ) ^ (1 / (p : ℝ))) • e)).taylorDecrement ℓ d ≤ 0 := by
  have hee : ∀ c : ℝ, ⟪e, c • e⟫ = c := fun c => by
    rw [inner_smul_right, real_inner_self_eq_norm_sq, he]; ring
  have hm : (fun t : ℝ => -β * t + σ * |t| ^ (p + 1) / (p + 1)!) =
      negMonomialRegModel p 1 σ β := by
    funext t; simp [negMonomialRegModel]
  have h0 := taylorMeasure_linearRegModel_eq_zero (Finset.mem_Icc.1 hℓ) hβ hσ hrad
  rw [hm] at h0
  have hle := taylorDecrement_le_taylorMeasure
    (ftaylorSeries ℝ (negMonomialRegModel p 1 σ β) ((β * p ! / σ) ^ (1 / (p : ℝ)))) ℓ
    (S := univ) (δ := δ) (d := ⟪e, d⟫)
    ⟨mem_closedBall_zero_iff.2 (show ‖⟪e, d⟫‖ ≤ δ by
      rw [Real.norm_eq_abs, ← hspan]; exact hdδ), mem_univ _⟩
  rw [h0] at hle
  refine le_trans (le_of_eq ?_) hle
  rw [FormalMultilinearSeries.taylorDecrement_eq, FormalMultilinearSeries.taylorDecrement_eq]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨hi1, hip⟩ := Finset.mem_Icc.1 hi
  rw [ftaylorSeries_real_apply]
  change (i ! : ℝ)⁻¹ * iteratedFDeriv ℝ i (regularizedModel (ftaylorSeries ℝ (ridge G e) x) p σ)
    _ (fun _ => d) = _
  rw [iteratedFDeriv_regularizedModel_ridge_spike hspan hG le_rfl hp hd σ hi1
    (hip.trans (Finset.mem_Icc.1 hℓ).2), hee]

/-- **Global model minimizers are admissible steps** ([cartis2022evaluation], Step 2 of
Algorithm 4.1.1): a global minimizer `s` of the model (4.1.2) with `m(s) < m(0)` satisfies (4.1.10),
(4.1.11) (`∇m(s) = 0`) and, if `q ≥ 2` (so `p ≥ 2`), (4.1.12) (`∇²m(s) ⪰ 0`); for `q ≥ 3` the
condition (4.1.13) is an extra hypothesis. -/
theorem isARpStep_of_isMinOn {f : E → ℝ} {p q : ℕ} (P : ARpParams)
    {x s : E} {σ : ℝ} (hqp : 2 ≤ q → 2 ≤ p)
    (hmin : IsMinOn (regularizedModel (ftaylorSeries ℝ f x) p σ) univ s)
    (hdec : regularizedModel (ftaylorSeries ℝ f x) p σ s <
      regularizedModel (ftaylorSeries ℝ f x) p σ 0)
    (hthird : 3 ≤ q → ∀ d ∈ smallCurvatureDirections
      (iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ f x) p σ) s) (P.θ₂ * ‖s‖ ^ (p - 1)),
      |iteratedFDeriv ℝ 3 (regularizedModel (ftaylorSeries ℝ f x) p σ) s (fun _ => d)| ≤
        P.θ₃ * ‖s‖ ^ (p - 2)) :
    IsARpStep f p P q x σ s := by
  have hloc : IsLocalMin (regularizedModel (ftaylorSeries ℝ f x) p σ) s :=
    hmin.isLocalMin Filter.univ_mem
  refine ⟨hdec, ?_, fun hq => ?_, hthird⟩
  · rw [hloc.fderiv_eq_zero, norm_zero]
    exact mul_nonneg P.θ₁_pos.le (by positivity)
  · have h0 := Optimization.IsLocalMin.minCurvature_iteratedFDeriv_two_nonneg hloc
      ((contDiff_regularizedModel (D := ftaylorSeries ℝ f x) (p := p) (σ := σ)).contDiffAt.of_le
        (by exact_mod_cast hqp hq))
    have : 0 ≤ P.θ₂ * ‖s‖ ^ (p - 1) := mul_nonneg P.θ₂_pos.le (by positivity)
    linarith

/-- **ARp runs on one-dimensional spike data** (the mechanism of Theorem 4.1.6). Let `G` be `C^p`
with spike jets `G^{(q)}(x_k) = -α_k < 0` (other derivatives of orders `1, …, p` zero) at points
`x_k` (`k < K`, `1 ≤ q ≤ p`), spaced by the global minimizers `t_k` of the one-dimensional models
`-α_k t^q/q! + σ₀ |t|^{p+1}/(p+1)!`, with `G(x_{k+1}) = G(x_k) - α_k t_k^q/q!`. If a test holds
at `k ≤ K` exactly when `k = K`, then the points `x_k e` form an ARp run of order `r` on
`ridge G e` with this test, `σ_k = σ₀`, global model minimizers as steps and `ρ_k = 1`, which
terminates exactly at `K`. (For `r = 3`, (4.1.13) is guaranteed by `q ≤ 3 ≤ p` and
`σ₀ ≤ (p-2)! θ₃`.) -/
theorem arp_ridge_run (P : ARpParams) (he : ‖e‖ = 1) (hspan : ∀ s : E, ‖s‖ = |⟪e, s⟫|) {r : ℕ}
    (hq : 1 ≤ q) (hqp : q ≤ p)
    (hrp : 2 ≤ r → 2 ≤ p) (hthird : 3 ≤ r → q ≤ 3 ∧ 3 ≤ p ∧ P.σ₀ ≤ (p - 2)! * P.θ₃)
    (hG : ContDiff ℝ p G) {xr α : ℕ → ℝ} {K : ℕ} (hα : ∀ k < K, 0 < α k)
    (hd : ∀ k < K, IsSpikeJetOf p G q (xr k) (α k))
    (hx : ∀ k < K, xr (k + 1) = xr k + monomialMinimizer p q P.σ₀ (α k))
    (hval : ∀ k < K, G (xr (k + 1)) = G (xr k) - α k * (xr (k + 1) - xr k) ^ q / q !)
    {test : ℕ → Prop} (htest : ∀ k ≤ K, (test k ↔ K ≤ k)) :
    IsARpRun (ridge G e) p P r test (fun k => xr k • e)
      (fun k => (xr (k + 1) - xr k) • e) (fun _ => P.σ₀) ∧ IsFirstHit test K ∧
      ∀ k < K, IsMinOn (regularizedModel (ftaylorSeries ℝ (ridge G e) (xr k • e)) p P.σ₀) univ
          ((xr (k + 1) - xr k) • e) ∧
        taylorRatio (ridge G e) p (fun k => xr k • e)
          (fun k => (xr (k + 1) - xr k) • e) k = 1 := by
  set f := ridge G e
  set x : ℕ → E := fun k => xr k • e
  set s : ℕ → E := fun k => (xr (k + 1) - xr k) • e
  have hσ₀ := P.σ₀_pos
  have hee : ∀ c : ℝ, ⟪e, c • e⟫ = c := fun c => by
    rw [inner_smul_right, real_inner_self_eq_norm_sq, he]; ring
  have hxs : ∀ k, x k + s k = x (k + 1) := fun k => by simp only [x, s, ← add_smul]; ring_nf
  have hdx : ∀ k < K, IsSpikeJetOf p G q ⟪e, x k⟫ (α k) := fun k hk => by
    simp only [x]; rw [hee]; exact hd k hk
  have ht : ∀ k < K, ⟪e, s k⟫ = monomialMinimizer p q P.σ₀ (α k) := fun k hk => by
    simp only [s]; rw [hee, hx k hk]; ring
  have htpos : ∀ k < K, 0 < ⟪e, s k⟫ := fun k hk => by
    rw [ht k hk]; exact monomialMinimizer_pos hσ₀ (hα k hk)
  have hnorm : ∀ k < K, ‖s k‖ = monomialMinimizer p q P.σ₀ (α k) := fun k hk => by
    rw [hspan, abs_of_pos (htpos k hk), ht k hk]
  have hmin : ∀ k < K, IsMinOn (regularizedModel (ftaylorSeries ℝ f (x k)) p P.σ₀) univ (s k) :=
    fun k hk => by
      obtain ⟨hm, -, -⟩ := isMinOn_neg_monomial_add_regularization hq hqp hσ₀ (hα k hk)
      rw [← monomialMinimizer] at hm
      intro y _
      simp only [mem_ofPred_eq]
      rw [regularizedModel_ridge_spike hspan hG hq hqp (hdx k hk), ridge_apply, ridge_apply,
        ht k hk]
      exact (add_le_add_iff_left _).2 (isMinOn_iff.1 hm _ (mem_univ _))
  have hdec : ∀ k < K, regularizedModel (ftaylorSeries ℝ f (x k)) p P.σ₀ (s k) <
      regularizedModel (ftaylorSeries ℝ f (x k)) p P.σ₀ 0 := fun k hk => by
    obtain ⟨-, hv, -⟩ := isMinOn_neg_monomial_add_regularization hq hqp hσ₀ (hα k hk)
    rw [← monomialMinimizer] at hv
    rw [regularizedModel_ridge_spike hspan hG hq hqp (hdx k hk), ridge_apply, ridge_apply, ht k hk,
      hv,
      inner_zero_right, negMonomialRegModel, zero_pow (by omega),
      abs_zero, zero_pow (by omega)]
    have := hα k hk
    have := monomialMinimizer_pos (p := p) (q := q) hσ₀ (hα k hk)
    have : 0 < ((p - q + 1 : ℕ) : ℝ) / ((p + 1) * q !) * α k *
        monomialMinimizer p q P.σ₀ (α k) ^ q := by positivity
    simp only [neg_mul, mul_zero, zero_div, add_zero]
    linarith
  have hthird' : ∀ k < K, 3 ≤ r → ∀ d ∈ smallCurvatureDirections
      (iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ f (x k)) p P.σ₀) (s k))
      (P.θ₂ * ‖s k‖ ^ (p - 1)),
      |iteratedFDeriv ℝ 3 (regularizedModel (ftaylorSeries ℝ f (x k)) p P.σ₀) (s k)
        (fun _ => d)| ≤ P.θ₃ * ‖s k‖ ^ (p - 2) := fun k hk h3 d hd => by
    obtain ⟨hq3, hp3, hσθ⟩ := hthird h3
    have hd1 : |⟪e, d⟫| = 1 := by rw [← hspan, hd.1]
    rw [iteratedFDeriv_regularizedModel_ridge_spike hspan hG hq hqp (hdx k hk) _ (by norm_num)
      hp3, abs_mul, abs_pow, hd1, one_pow, mul_one, ht k hk, hnorm k hk]
    obtain ⟨h0, h1⟩ := iteratedDeriv_three_negMonomialRegModel_mem hq hq3 hp3 hσ₀ (hα k hk)
    rw [abs_of_nonneg h0]
    refine h1.trans ?_
    have hf : (0 : ℝ) < (p - 2)! := by positivity
    have := monomialMinimizer_pos (p := p) (q := q) hσ₀ (hα k hk)
    rw [div_le_iff₀ hf]
    have : 0 ≤ monomialMinimizer p q P.σ₀ (α k) ^ (p - 2) := by positivity
    nlinarith
  have hratio : ∀ k < K, taylorRatio f p x s k = 1 := fun k hk => by
    have hts : ⟪e, s k⟫ = xr (k + 1) - xr k := by simp only [s]; rw [hee]
    have hT := taylorDecrement_ridge_spike hG hq hqp (hdx k hk) (s k)
    have hpos : 0 < α k * (xr (k + 1) - xr k) ^ q / q ! := by
      have := hα k hk; have := htpos k hk; rw [hts] at this; positivity
    rw [taylorRatio_def, hT, hts, reductionRatio_def, hxs]
    simp only [f, x, ridge_apply, hee]
    rw [hval k hk, sub_sub_cancel, div_self hpos.ne']
  have hhit : IsFirstHit test K :=
    ⟨(htest K le_rfl).2 le_rfl, fun j hj h => absurd ((htest j hj.le).1 h) (not_le.2 hj)⟩
  refine ⟨isARpRun_iff.2 ⟨rfl, fun k hk h1 => ?_, fun k hk => ?_⟩, hhit,
    fun k hk => ⟨hmin k hk, hratio k hk⟩⟩
  · have hk' : k < K := by
      by_contra hle
      rcases (not_lt.1 hle).eq_or_lt with heq | hlt
      · exact h1 (heq ▸ hhit.test)
      · exact hk K hlt (Or.inl hhit.test)
    exact isARpStep_of_isMinOn P hrp (hmin k hk') (hdec k hk') (hthird' k hk')
  · have hk' : k < K := not_le.1 fun hle => hk K hle (Or.inl hhit.test)
    change ARAcceptance P.toARParams (taylorRatio f p x s k) (x k) (s k) (x (k + 1)) P.σ₀ P.σ₀
    rw [← hxs, hratio k hk']
    exact arAcceptance_of_one_le P.toARParams le_rfl _ _ P.σmin_le_σ₀ hσ₀.le

end Run

end Ridge

end Optimization

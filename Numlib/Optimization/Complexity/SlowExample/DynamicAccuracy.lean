import Numlib.Optimization.Complexity.SlowExample.ARp
import Numlib.Optimization.Complexity.SlowExample.Slit
import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.ARqpDAStep
import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.TRqIDA

/-!
# Slow iterations of the dynamic-accuracy methods

The slow examples of [cartis2022evaluation], §12.2 (Theorems 12.2.6, 12.2.15 and 12.2.17), lifted
along a unit vector `e` of a real inner product space (ridge functions `x ↦ g ⟪e, x⟫`), give
iterations of the dynamic-accuracy trust-region and regularization steps of Chapter 13
(`Optimization.TRqDAStep`, `Optimization.ARqpDAStep`) with exact Taylor data. Each lemma below
checks one iteration from the shape of the Taylor decrements at the iterate (a monomial
`a ⟪e, d⟫^q` of a single order, or a linear form), the Step-1 radii and displacements, the step
and the ratio; the sharpness theorems of §14.2 splice these iterations into runs.

The slit example (§14.2, a line and a parallel half-plane, `Optimization.slitSet`) adds a second
unit vector `e₂ ⊥ e₁` along which the Taylor models decrease linearly.

## Main results

* `Optimization.slowTRq_trqDAStep`: an iteration of the slow trust-region example
  (Theorem 12.2.6) is a TRqIDA/TRqEDA step;
* `Optimization.slowARqp_arqpDAStep`, `Optimization.slowARqpTop_arqpDAStep`: iterations of the
  slow regularization example (Theorem 12.2.15) with a halved Step-1 radius, or with small radii,
  are ARqpIDA/ARqpEDA steps;
* `Optimization.slowGrad_arqpDAStep`: an iteration of the slow gradient example
  (Theorem 12.2.17) is an ARqpIDA/ARqpEDA step;
* `Optimization.slit_arqpDAStep`, `Optimization.slit_arqpDAStep_of_acc`: trial and
  accuracy-improving iterations of the slit example on `slitSet e₂ ρ`.
-/

open Set Metric
open scoped Nat RealInnerProductSpace

namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {e : E}

/-- In finite dimension, without constraints, there are approximate optimality displacements for
a Taylor decrement achieving exactly the fraction `ς ∈ [0, 1]` of the measure. -/
theorem exists_isApproxMeasureStep_eq_mul_taylorMeasure [FiniteDimensional ℝ E]
    (D : FormalMultilinearSeries ℝ E ℝ) (j : ℕ) {δ ς : ℝ} (hδ : 0 ≤ δ) (hς : ς ∈ Icc (0 : ℝ) 1) :
    ∃ d, IsApproxMeasureStep (D.taylorDecrement j) δ univ ς d ∧
      D.taylorDecrement j d = ς * taylorMeasure D j δ univ :=
  exists_isApproxMeasureStep_eq isClosed_univ (mem_univ 0) (starConvex_univ 0) hδ
    (D.continuous_taylorDecrement j).continuousOn (D.taylorDecrement_zero_right j) hς

section SlowStep

variable {P : TRqIDAParams} {ε lam c : ℝ} {x : ℕ → E} {Δ : ℕ → ℝ}
  {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ E ℝ}
  {dd : ℕ → ℕ → E} {jk : ℕ → ℕ} {s : ℕ → E}
  {acc : ℕ → Prop} {ρ : ℕ → ℝ} {k : ℕ}

/-- The Step-1 decreases along the slow example: `ς a_j ε^q` with `a_q = λ ε c` and `a_j = 0`
otherwise. -/
theorem slowTRq_taylorDecrement_eq (he : ‖e‖ = 1) (hε : 0 < ε) (hA : 0 ≤ lam * ε * c)
    (hdec : ∀ j ∈ Finset.Icc 1 P.q, ∀ d,
      (D k).taylorDecrement j d = (if j = P.q then lam * ε * c else 0) * ⟪e, d⟫ ^ P.q)
    (hdd : ∀ j ∈ Finset.Icc 1 P.q,
      IsApproxMeasureStep ((D k).taylorDecrement j) ε univ P.ς (dd k j) ∧
        (D k).taylorDecrement j (dd k j) = P.ς * taylorMeasure (D k) j ε univ)
    {j : ℕ} (hj : j ∈ Finset.Icc 1 P.q) :
    (D k).taylorDecrement j (dd k j) = P.ς * ((if j = P.q then lam * ε * c else 0) * ε ^ P.q) := by
  rw [(hdd j hj).2, taylorMeasure_eq_mul_pow_of_inner_pow he (by split_ifs <;>
      [exact hA; exact le_rfl]) hε.le
    (hdec j hj)]

/-- Along the slow example the test (13.1.14) holds at order `q` (`λ c > ½`). -/
theorem slowTRq_trqDAFail (he : ‖e‖ = 1) (hε : 0 < ε) (hϑ : P.ϑ = ε) (hlamc : 1 < 2 * (lam * c))
    (hdec : ∀ j ∈ Finset.Icc 1 P.q, ∀ d,
      (D k).taylorDecrement j d = (if j = P.q then lam * ε * c else 0) * ⟪e, d⟫ ^ P.q)
    (hdd : ∀ j ∈ Finset.Icc 1 P.q,
      IsApproxMeasureStep ((D k).taylorDecrement j) ε univ P.ς (dd k j) ∧
        (D k).taylorDecrement j (dd k j) = P.ς * taylorMeasure (D k) j ε univ)
    (hΔ : Δ k = ε) : trqDAFail P (fun j => j ! * ε) D Δ dd k P.q := by
  have hqm : P.q ∈ Finset.Icc 1 P.q := Finset.mem_Icc.2 ⟨P.one_le_q, le_rfl⟩
  have hA : 0 ≤ lam * ε * c := by nlinarith
  have hς := P.ς_pos
  rw [trqDAFail, trqDARadius, hΔ, hϑ, min_self, slowTRq_taylorDecrement_eq he hε hA hdec hdd hqm,
      ite_eq_left rfl]
  have hqf : (0 : ℝ) < P.q ! := by positivity
  have e : P.ς * (P.q ! * ε) * ε ^ P.q / P.q ! / 2 = P.ς * ε ^ P.q * ε / 2 := by
    field_simp
  rw [e]
  have h0 : 0 < P.ς * ε ^ P.q * ε := by positivity
  nlinarith

/-- **One iteration of the slow example is a TRqIDA/TRqEDA step** (`X = univ`, exact Taylor data
`D k`): with `ϑ = Δ_k = Δ_{k+1} = ε`, decrements `a_j ⟪e, d⟫^q` (`a_q = λ ε c`, `λ c > ½`),
Step-1 displacements achieving the fraction `ς` of the measures, the step `s_k = ε e` along
which the iterate moves, `j_k = q`, accuracies passing (13.1.9) and the ratio `ρ_k = 1`. -/
theorem slowTRq_trqDAStep (he : ‖e‖ = 1) (hε : 0 < ε) (hϑ : P.ϑ = ε) (hΔmax : ε ≤ P.Δmax)
    (hlamc : 1 < 2 * (lam * c)) (hA : 0 ≤ lam * ε * c)
    (hdec : ∀ j ∈ Finset.Icc 1 P.q, ∀ d,
      (D k).taylorDecrement j d = (if j = P.q then lam * ε * c else 0) * ⟪e, d⟫ ^ P.q)
    (hdd : ∀ j ∈ Finset.Icc 1 P.q,
      IsApproxMeasureStep ((D k).taylorDecrement j) ε univ P.ς (dd k j) ∧
        (D k).taylorDecrement j (dd k j) = P.ς * taylorMeasure (D k) j ε univ)
    (hΔ : Δ k = ε) (hΔ1 : Δ (k + 1) = ε) (hh1 : h (k + 1) = h k)
    (hhk : ∀ i ∈ Finset.Icc 1 P.q, h k i ≤ P.κs * ε ^ (P.q - i + 1)) (hjk : jk k = P.q)
    (hs : s k = ε • e) (hacc : ¬ acc k) (hx1 : x (k + 1) = x k + ε • e) (hρ : ρ k = 1) :
    TRqDAStep univ P (fun j => j ! * ε) x Δ h D dd jk s acc ρ k := by
  have hqm : P.q ∈ Finset.Icc 1 P.q := Finset.mem_Icc.2 ⟨P.one_le_q, le_rfl⟩
  have hς := P.ς_pos
  have hς1 := P.ς_le_one
  have hrad : trqDARadius P Δ k = ε := by simp only [trqDARadius, hΔ, hϑ, min_self]
  have hfail := slowTRq_trqDAFail he hε hϑ hlamc hdec hdd hΔ
  have hnot : ∀ j ∈ Finset.Icc 1 P.q, j ≠ P.q → ¬ trqDAFail P (fun j => j ! * ε) D Δ dd k j := by
    intro j hj hjq hf
    rw [trqDAFail, hrad, slowTRq_taylorDecrement_eq he hε hA hdec hdd hj, ite_eq_right hjq,
        zero_mul, mul_zero] at hf
    have : 0 < P.ς * (j ! * ε) * ε ^ j / j ! / 2 := by positivity
    linarith
  have hη : P.η₁ ≤ 1 := P.η₁_le_η₂.trans P.η₂_lt_one.le
  refine ⟨fun j hj => ?_, fun hp => absurd hfail (hp _ hqm), fun _ => ?_, fun _ => ?_,
    fun _ => hΔ1 ▸ hΔmax, fun _ => hh1, fun _ hr => absurd hr (by rw [hρ]; exact not_lt.2 hη),
    fun ha => absurd ha hacc, fun ha => absurd ha hacc, fun ha => absurd ha hacc⟩
  · rw [hrad, Set.setOf_add_mem_univ]; exact (hdd j hj).1
  · refine ⟨by rw [hjk]; exact hqm, by rw [hjk]; exact hfail,
      fun j hj hlt => hnot j hj (by rw [hjk] at hlt; exact hlt.ne), mem_univ _,
      by rw [hs, hΔ, norm_smul_of_norm_eq_one he, abs_of_pos hε], ?_, iff_of_false hacc ?_⟩
    · rw [hjk, slowTRq_taylorDecrement_eq he hε hA hdec hdd hqm, hs, hdec _ hqm,
        inner_smul_self_of_norm_eq_one he,
        ite_eq_left rfl]
      have : 0 ≤ lam * ε * c * ε ^ P.q := by positivity
      nlinarith
    · rintro ⟨i, hi, hlt⟩
      rw [hs, norm_smul_of_norm_eq_one he, abs_of_pos hε] at hlt
      linarith [hhk i hi]
  · refine ⟨by rw [hρ, ite_eq_left hη, hs, hx1], ?_⟩
    rw [hρ, hΔ, hΔ1]
    exact ⟨fun _ => ⟨le_rfl, le_mul_of_one_le_left hε.le P.one_le_γ₃⟩,
      fun _ h2 => absurd h2 (not_lt.2 P.η₂_lt_one.le), fun h1 => absurd h1 (not_lt.2 hη)⟩

end SlowStep

/-- The ratio of a slow iteration is `1`: the decrease `λ ε^{q+1} c` of `f` equals the decrease
`λ ε c ε^q` of the Taylor model along `s_k = ε e`. -/
theorem slowTRq_trqRatio_eq_one {f : E → ℝ}
    {D : ℕ → FormalMultilinearSeries ℝ E ℝ}
    {x s : ℕ → E} {jk : ℕ → ℕ} {k q : ℕ} {ε lam c : ℝ} (hε : 0 < ε)
    (hlam : 0 < lam) (hc : 0 < c) (hjk : jk k = q) (hs : s k = ε • e)
    (hdec : (D k).taylorDecrement q (ε • e) = lam * ε * c * ε ^ q)
    (hf : f (x k + ε • e) = f (x k) - lam * ε ^ (q + 1) * c) :
    trqRatio f D x s jk k = 1 := by
  rw [trqRatio_eq, reductionRatio, hjk, hs, hdec, hf]
  have : 0 < lam * ε * c * ε ^ q := by positivity
  field_simp
  ring


section SlowARStep

variable {P : ARqpIDAParams} {ε a r : ℝ} {x : ℕ → E} {σ : ℕ → ℝ}
  {δ δ₁ δs : ℕ → ℕ → ℝ} {h : ℕ → ℕ → ℝ}
  {D : ℕ → FormalMultilinearSeries ℝ E ℝ}
  {dd : ℕ → ℕ → E} {jk : ℕ → ℕ} {s : ℕ → E}
  {acc : ℕ → Prop} {ρ : ℕ → ℝ} {k : ℕ}

/-- The Step-1 measures along the slow regularization example: `0` below `q` and `(a/q!) δ^q`
at order `q`. -/
theorem slowARqp_taylorMeasure_eq (he : ‖e‖ = 1) (ha : 0 ≤ a)
    (hdec : ∀ j ≤ P.q, ∀ d, (D k).taylorDecrement j d =
      (if j = P.q then a / P.q ! else 0) * ⟪e, d⟫ ^ P.q) {j : ℕ} (hj : j ≤ P.q) {t : ℝ}
    (ht : 0 ≤ t) :
    taylorMeasure (D k) j t univ = (if j = P.q then a / P.q ! else 0) * t ^ P.q :=
  taylorMeasure_eq_mul_pow_of_inner_pow he (by split_ifs <;> positivity) ht (hdec
      j hj)

/-- `½ ς ε t/c < (a/c) t` for `a > ε/2`, `ς ≤ 1`, `t, c > 0`. -/
theorem slowARqp_half_lt {ς ε a t c : ℝ} (hς1 : ς ≤ 1) (hε : 0 < ε) (ha : ε / 2 < a)
    (ht : 0 < t) (hc : 0 < c) : ς * ε * t / c / 2 < a / c * t := by
  rw [show ς * ε * t / c / 2 = ς * ε / 2 * t / c by ring, show a / c * t = a * t / c by ring]
  refine div_lt_div_of_pos_right ?_ hc
  have : ς * ε / 2 ≤ ε / 2 := by nlinarith
  nlinarith

/-- Along the slow regularization example the test (13.1.53) fails at order `q` with the
displacement `r e` (`a > ε/2`). -/
theorem slowARqp_not_arqpDAPass (hε : 0 < ε) (ha : ε / 2 < a) (hr : 0 < r)
    (hδ₁ : δ₁ k P.q = r) (hdd : dd k P.q = r • e)
    (hdq : (D k).taylorDecrement P.q (r • e) = a / P.q ! * r ^ P.q) :
    ¬ arqpDAPass P (fun _ => ε) D δ₁ dd k P.q := by
  rw [arqpDAPass, hδ₁, hdd, hdq]
  exact not_le.2 (slowARqp_half_lt P.ς_le_one hε ha (by positivity) (by positivity))

/-- **One iteration of the slow regularization example is an ARqpIDA/ARqpEDA step** (`X = univ`,
`q ≤ 2`, tolerances `ε_j = ε`): with unit radii `δ_k = δ_{k+1} = δ_{s_k} = 1`, decrements
`(a/q!) ⟪e, d⟫^q` at orders `q` and `p` (none below `q`) with `a > ε/2`, a Step-1 radius
`δ^{(1)}_{k,q} = r` at which (13.1.54) holds while it fails at `2 r ≤ 1` (the halving loop stops at
`r`), the Step-1 displacements `r e` (order `q`) and `0` (below), a global minimizer `s_k` of the
model as step with `‖s_k‖ < 1`, accuracies passing (13.1.46), and the ratio `ρ_k = 1`. -/
theorem slowARqp_arqpDAStep (he : ‖e‖ = 1) (hq2 : P.q ≤ 2) (hε : 0 < ε) (ha : ε / 2 < a)
    (hr : 0 < r) (h2r : 2 * r ≤ 1) (hrd : ∃ m : ℕ, r = 1 / 2 ^ m)
    (hr54 : σ k / ((P.p + 1)! : ℝ) * r ^ (P.p + 1) ≤ (a - P.ς * ε / 4) / P.q ! * r ^ P.q)
    (hr54' : (a - P.ς * ε / 4) / P.q ! * (2 * r) ^ P.q <
      σ k / ((P.p + 1)! : ℝ) * (2 * r) ^ (P.p + 1))
    (hδ : ∀ j ∈ Finset.Icc 1 P.q, δ k j = 1) (hδ1 : δ (k + 1) = δs k)
    (hδs : ∀ j ∈ Finset.Icc 1 P.q, δs k j = 1) (hδ₁ : δ₁ k = fun j => if j = P.q then r else 1)
    (hdd : dd k = fun j => if j = P.q then r • e else 0) (hjk : jk k = P.q)
    (hdec : ∀ j ≤ P.q, ∀ d, (D k).taylorDecrement j d =
      (if j = P.q then a / P.q ! else 0) * ⟪e, d⟫ ^ P.q)
    (hdecp : ∀ d, (D k).taylorDecrement P.p d = a / P.q ! * ⟪e, d⟫ ^ P.q)
    (hmin : IsMinOn (regularizedModel (D k) P.p (σ k)) univ (s k))
    (hs1 : ‖s k‖ < 1) (hhk : ∀ i ∈ Finset.Icc 1 P.p, h k i ≤ P.κs * ‖s k‖ ^ (P.p - i + 1))
    (hacc : ¬ acc k) (hx1 : x (k + 1) = x k + s k) (hσ1 : σ (k + 1) = σ k)
    (hσk : P.σmin ≤ σ k) (hh1 : h (k + 1) = h k) (hρ : ρ k = 1) :
    ARqpDAStep univ P (fun _ => ε) x σ δ δ₁ δs h D dd jk s acc ρ k := by
  have hqm : P.q ∈ Finset.Icc 1 P.q := Finset.mem_Icc.2 ⟨P.one_le_q, le_rfl⟩
  have hς := P.ς_pos
  have hς1 := P.ς_le_one
  have hqf : (0 : ℝ) < P.q ! := by positivity
  have ha0 : 0 < a := by linarith
  have hA : 0 < a / P.q ! := by positivity
  have hσ0 : 0 ≤ σ k := P.σmin_pos.le.trans hσk
  have hη : P.η₁ ≤ 1 := P.η₁_le_η₂.trans P.η₂_lt_one.le
  -- Taylor decrements along `t e`
  have hdq : ∀ t : ℝ, (D k).taylorDecrement P.q (t • e) = a / P.q ! * t ^ P.q := fun t => by
    rw [hdec _ le_rfl, ite_eq_left rfl, inner_smul_self_of_norm_eq_one he]
  have hdlt : ∀ j < P.q, ∀ d, (D k).taylorDecrement j d = 0 := fun j hj d => by
    rw [hdec j hj.le, ite_eq_right hj.ne, zero_mul]
  have hM : ∀ t : ℝ, 0 ≤ t → arModelDec P D σ k (t • e) =
      a / P.q ! * t ^ P.q - σ k / ((P.p + 1)! : ℝ) * t ^ (P.p + 1) := fun t ht => by
    rw [arModelDec_eq, hdecp, inner_smul_self_of_norm_eq_one he, norm_smul_of_norm_eq_one he,
        abs_of_nonneg ht]
  -- the test (13.1.53) fails at order `q` with the displacement `r e`
  have hfail : ¬ arqpDAPass P (fun _ => ε) D δ₁ dd k P.q :=
    slowARqp_not_arqpDAPass hε ha hr (by rw [hδ₁]; simp) (by rw [hdd]; simp) (hdq r)
  have hpass_lt : ∀ j ∈ Finset.Icc 1 P.q, j < P.q → arqpDAPass P (fun _ => ε) D δ₁ dd k j := by
    intro j hj hlt
    rw [arqpDAPass, hdd]
    simp only [ite_eq_right hlt.ne, FormalMultilinearSeries.taylorDecrement_zero_right]
    rw [hδ₁]
    simp only [ite_eq_right hlt.ne]
    positivity
  refine ⟨⟨fun j hj => ?_, fun j hj => ?_, fun j hj hlt => ?_, fun j hj => ?_, fun j hj => ?_⟩,
    fun hp => absurd (hp _ hqm) hfail, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => hh1,
    fun _ hr' => absurd hr' (by rw [hρ]; exact not_lt.2 hη), fun ha' => absurd ha' hacc,
    fun ha' => absurd ha' hacc, fun ha' => absurd ha' hacc, fun ha' => absurd ha' hacc⟩
  · rw [hδ₁]; dsimp only; split_ifs <;> positivity
  · rw [hδ₁, hδ j hj]; dsimp only; split_ifs <;> linarith
  · -- the halving loop stopped at `r`
    rw [hδ₁, hδ j hj] at hlt ⊢
    dsimp only at hlt ⊢
    by_cases hjq : j = P.q
    · subst hjq
      rw [ite_eq_left rfl] at hlt ⊢
      refine ⟨h2r, ⟨(2 * r) • e, by rw [norm_smul_of_norm_eq_one he, abs_of_pos (by positivity)],
          mem_univ _,
        ?_, ?_⟩, e, he.le, mem_univ _, ?_⟩
      · rw [hdq]
        exact slowARqp_half_lt hς1 hε ha (by positivity) hqf
      · rw [hM _ (by positivity)]
        have : P.ς * ε * (2 * r) ^ P.q / P.q ! / 4 = (P.ς * ε / 4) / P.q ! * (2 * r) ^ P.q := by
          ring
        rw [this]
        have e : (a - P.ς * ε / 4) / P.q ! * (2 * r) ^ P.q =
            a / P.q ! * (2 * r) ^ P.q - (P.ς * ε / 4) / P.q ! * (2 * r) ^ P.q := by ring
        linarith
      · have h1 : e = (1 : ℝ) • e := (one_smul ℝ e).symm
        rw [h1, hdq]
        exact slowARqp_half_lt hς1 hε ha (by positivity) hqf
    · rw [ite_eq_right hjq] at hlt
      exact absurd hlt (lt_irrefl _)
  · -- the radii are obtained by halving
    rw [hδ₁, hδ j hj]
    dsimp only
    split_ifs
    · exact hrd
    · exact ⟨0, by norm_num⟩
  · -- the Step-1 displacements
    have hj' := (Finset.mem_Icc.1 hj).2
    rw [hδ₁, hdd, Set.setOf_add_mem_univ]
    dsimp only
    by_cases hjq : j = P.q
    · subst hjq
      simp only [ite_true]
      refine ⟨⟨by rw [mem_closedBall_zero_iff, norm_smul_of_norm_eq_one he, abs_of_pos hr],
          mem_univ _⟩, ?_⟩
      change P.ς * taylorMeasure (D k) P.q r univ ≤ _
      rw [slowARqp_taylorMeasure_eq he ha0.le hdec le_rfl hr.le, ite_eq_left rfl, hdq]
      have : 0 ≤ a / P.q ! * r ^ P.q := by positivity
      nlinarith
    · simp only [ite_eq_right hjq]
      refine ⟨⟨mem_closedBall_self zero_le_one, mem_univ _⟩, ?_⟩
      change P.ς * taylorMeasure (D k) j 1 univ ≤ _
      rw [slowARqp_taylorMeasure_eq he ha0.le hdec hj' zero_le_one, ite_eq_right hjq, zero_mul,
          mul_zero,
        FormalMultilinearSeries.taylorDecrement_zero_right]
  · -- Step 2
    refine ⟨by rw [hjk]; exact hqm, by rw [hjk]; exact hfail,
      fun j hj hlt => hpass_lt j hj (by rw [hjk] at hlt; exact hlt),
      fun j hj hlt => absurd (Finset.mem_Icc.1 hj).2 (by rw [hjk] at hlt; omega), ?_,
      mem_univ _, ?_, Or.inr fun ℓ hℓ => ?_, iff_of_false hacc ?_⟩
    · rw [hjk, hdd, hδ₁]
      simp only [ite_true]
      rw [hM _ hr.le]
      have : P.ς * ε * r ^ P.q / P.q ! / 4 = (P.ς * ε / 4) / P.q ! * r ^ P.q := by ring
      rw [this]
      have e : (a - P.ς * ε / 4) / P.q ! * r ^ P.q =
          a / P.q ! * r ^ P.q - (P.ς * ε / 4) / P.q ! * r ^ P.q := by ring
      linarith
    · simp only [arModelDec]
      have := isMinOn_iff.1 hmin (dd k (jk k)) (mem_univ _)
      linarith
    · have hℓ2 : ℓ ∈ Finset.Icc 1 2 :=
        Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hℓ).1, (Finset.mem_Icc.1 hℓ).2.trans hq2⟩
      have hℓp : ℓ ≤ P.p := (Finset.mem_Icc.1 hℓ).2.trans P.q_le_p
      have hφ := taylorMeasure_eq_zero_of_isLocalMin
        ((contDiff_regularizedModel (D := D k) (p := P.p) (σ := σ k)).contDiffAt.of_le
          (by exact_mod_cast hℓp)) (hmin.isLocalMin Filter.univ_mem) hℓ2 zero_le_one
      rw [hδs ℓ hℓ, Set.setOf_add_mem_univ]
      refine ⟨⟨zero_lt_one, le_rfl⟩, 0, ⟨⟨mem_closedBall_self zero_le_one, mem_univ _⟩, ?_⟩, ?_⟩
      · change P.ς * taylorMeasure _ ℓ 1 univ ≤ _
        rw [hφ, mul_zero, FormalMultilinearSeries.taylorDecrement_zero_right]
      · rw [FormalMultilinearSeries.taylorDecrement_zero_right]
        have := P.θ_pos
        positivity
    · rintro ⟨-, i, hi, hlt⟩
      linarith [hhk i hi]
  · rw [hρ, hx1, hσ1]
    exact arAcceptance_of_one_le P.toARParams le_rfl _ _ hσk hσ0
  · rw [hδ1, hρ, ite_eq_left ⟨hη, hs1⟩]

/-- **One iteration of the slow regularization example with small radii** (`X = univ`, any
`q ≤ p`, tolerances `ε_j = ε`): with Step-1 radii `δ_k = δ^{(1)}_k = r` at every order (no
halving) at which (13.1.54) holds, decrements `(a/q!) ⟪e, d⟫^q` at orders `q` and `p` (none
below `q`) with `a > ε/2`, the Step-1 displacements `r e` (order `q`) and `0` (below), a global
minimizer `s_k` of the model as step, short, whose model decrements of orders `1, …, q` are
nonpositive on the ball of radius `r'` (the Step-2 radii `δ_{s_k} = r' = δ_{k+1}`), accuracies
passing (13.1.46), and the ratio `ρ_k = 1`. -/
theorem slowARqpTop_arqpDAStep (he : ‖e‖ = 1) {r' : ℝ} (hε : 0 < ε) (ha : ε / 2 < a) (hr : 0 < r)
    (hr' : 0 < r') (hr'1 : r' ≤ 1)
    (hr54 : σ k / ((P.p + 1)! : ℝ) * r ^ (P.p + 1) ≤ (a - P.ς * ε / 4) / P.q ! * r ^ P.q)
    (hδ : ∀ j ∈ Finset.Icc 1 P.q, δ k j = r) (hδ1 : δ (k + 1) = δs k) (hδ₁ : δ₁ k = δ k)
    (hδs : ∀ j ∈ Finset.Icc 1 P.q, δs k j = r')
    (hdd : dd k = fun j => if j = P.q then r • e else 0) (hjk : jk k = P.q)
    (hdec : ∀ j ≤ P.q, ∀ d, (D k).taylorDecrement j d =
      (if j = P.q then a / P.q ! else 0) * ⟪e, d⟫ ^ P.q)
    (hdecp : ∀ d, (D k).taylorDecrement P.p d = a / P.q ! * ⟪e, d⟫ ^ P.q)
    (hmin : IsMinOn (regularizedModel (D k) P.p (σ k)) univ (s k))
    (hmodel : ∀ ℓ ∈ Finset.Icc 1 P.q, ∀ d, ‖d‖ ≤ r' →
      (ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)).taylorDecrement ℓ d ≤ 0)
    (hs1 : ‖s k‖ < 1) (hhk : ∀ i ∈ Finset.Icc 1 P.p, h k i ≤ P.κs * ‖s k‖ ^ (P.p - i + 1))
    (hacc : ¬ acc k) (hx1 : x (k + 1) = x k + s k) (hσ1 : σ (k + 1) = σ k)
    (hσk : P.σmin ≤ σ k) (hh1 : h (k + 1) = h k) (hρ : ρ k = 1) :
    ARqpDAStep univ P (fun _ => ε) x σ δ δ₁ δs h D dd jk s acc ρ k := by
  have hqm : P.q ∈ Finset.Icc 1 P.q := Finset.mem_Icc.2 ⟨P.one_le_q, le_rfl⟩
  have hς := P.ς_pos
  have hς1 := P.ς_le_one
  have hqf : (0 : ℝ) < P.q ! := by positivity
  have ha0 : 0 < a := by linarith
  have hσ0 : 0 ≤ σ k := P.σmin_pos.le.trans hσk
  have hη : P.η₁ ≤ 1 := P.η₁_le_η₂.trans P.η₂_lt_one.le
  have hdq : ∀ t : ℝ, (D k).taylorDecrement P.q (t • e) = a / P.q ! * t ^ P.q := fun t => by
    rw [hdec _ le_rfl, ite_eq_left rfl, inner_smul_self_of_norm_eq_one he]
  have hM : ∀ t : ℝ, 0 ≤ t → arModelDec P D σ k (t • e) =
      a / P.q ! * t ^ P.q - σ k / ((P.p + 1)! : ℝ) * t ^ (P.p + 1) := fun t ht => by
    rw [arModelDec_eq, hdecp, inner_smul_self_of_norm_eq_one he, norm_smul_of_norm_eq_one he,
        abs_of_nonneg ht]
  have hfail : ¬ arqpDAPass P (fun _ => ε) D δ₁ dd k P.q :=
    slowARqp_not_arqpDAPass hε ha hr (by rw [hδ₁, hδ _ hqm]) (by rw [hdd]; simp) (hdq r)
  have hpass_lt : ∀ j ∈ Finset.Icc 1 P.q, j < P.q → arqpDAPass P (fun _ => ε) D δ₁ dd k j := by
    intro j hj hlt
    rw [arqpDAPass, hdd]
    simp only [ite_eq_right hlt.ne, FormalMultilinearSeries.taylorDecrement_zero_right]
    rw [hδ₁, hδ j hj]
    positivity
  refine ⟨⟨fun j hj => by rw [hδ₁, hδ j hj]; exact hr, fun j _ => by rw [hδ₁],
    fun j _ hlt => by rw [hδ₁] at hlt; exact absurd hlt (lt_irrefl _),
    fun j _ => ⟨0, by rw [hδ₁]; norm_num⟩, fun j hj => ?_⟩,
    fun hp => absurd (hp _ hqm) hfail, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => hh1,
    fun _ hr'' => absurd hr'' (by rw [hρ]; exact not_lt.2 hη), fun ha' => absurd ha' hacc,
    fun ha' => absurd ha' hacc, fun ha' => absurd ha' hacc, fun ha' => absurd ha' hacc⟩
  · -- the Step-1 displacements
    have hj' := (Finset.mem_Icc.1 hj).2
    rw [hδ₁, hδ j hj, hdd, Set.setOf_add_mem_univ]
    dsimp only
    by_cases hjq : j = P.q
    · subst hjq
      simp only [ite_true]
      refine ⟨⟨by rw [mem_closedBall_zero_iff, norm_smul_of_norm_eq_one he, abs_of_pos hr],
          mem_univ _⟩, ?_⟩
      change P.ς * taylorMeasure (D k) P.q r univ ≤ _
      rw [slowARqp_taylorMeasure_eq he ha0.le hdec le_rfl hr.le, ite_eq_left rfl, hdq]
      have : 0 ≤ a / P.q ! * r ^ P.q := by positivity
      nlinarith
    · simp only [ite_eq_right hjq]
      refine ⟨⟨mem_closedBall_self hr.le, mem_univ _⟩, ?_⟩
      change P.ς * taylorMeasure (D k) j r univ ≤ _
      rw [slowARqp_taylorMeasure_eq he ha0.le hdec hj' hr.le, ite_eq_right hjq, zero_mul, mul_zero,
        FormalMultilinearSeries.taylorDecrement_zero_right]
  · -- Step 2
    refine ⟨by rw [hjk]; exact hqm, by rw [hjk]; exact hfail,
      fun j hj hlt => hpass_lt j hj (by rw [hjk] at hlt; exact hlt),
      fun j hj hlt => absurd (Finset.mem_Icc.1 hj).2 (by rw [hjk] at hlt; omega), ?_,
      mem_univ _, ?_, Or.inr fun ℓ hℓ => ?_, iff_of_false hacc ?_⟩
    · rw [hjk, hdd, hδ₁, hδ _ hqm]
      simp only [ite_true]
      rw [hM _ hr.le]
      have : P.ς * ε * r ^ P.q / P.q ! / 4 = (P.ς * ε / 4) / P.q ! * r ^ P.q := by ring
      rw [this]
      have e : (a - P.ς * ε / 4) / P.q ! * r ^ P.q =
          a / P.q ! * r ^ P.q - (P.ς * ε / 4) / P.q ! * r ^ P.q := by ring
      linarith
    · simp only [arModelDec]
      have := isMinOn_iff.1 hmin (dd k (jk k)) (mem_univ _)
      linarith
    · have hℓ' : ∀ d ∈ closedBall (0 : E) r' ∩ univ,
          (ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)).taylorDecrement ℓ d ≤ 0 :=
        fun d hd => hmodel ℓ hℓ d (mem_closedBall_zero_iff.1 hd.1)
      rw [hδs ℓ hℓ, Set.setOf_add_mem_univ]
      refine ⟨⟨hr', hr'1⟩, 0, ⟨⟨mem_closedBall_self hr'.le, mem_univ _⟩, ?_⟩, ?_⟩
      · rw [FormalMultilinearSeries.taylorDecrement_zero_right]
        exact mul_nonpos_of_nonneg_of_nonpos hς.le
          (decrementMeasure_le ⟨0, mem_closedBall_self hr'.le, mem_univ _⟩ hℓ')
      · rw [FormalMultilinearSeries.taylorDecrement_zero_right]
        have := P.θ_pos
        positivity
    · rintro ⟨-, i, hi, hlt⟩
      linarith [hhk i hi]
  · rw [hρ, hx1, hσ1]
    exact arAcceptance_of_one_le P.toARParams le_rfl _ _ hσk hσ0
  · rw [hδ1, hρ, ite_eq_left ⟨hη, hs1⟩]

end SlowARStep

section SlowGradStep

variable {P : ARqpIDAParams} {ε β : ℝ} {x : ℕ → E} {σ : ℕ → ℝ}
  {δ δ₁ δs : ℕ → ℕ → ℝ} {h : ℕ → ℕ → ℝ}
  {D : ℕ → FormalMultilinearSeries ℝ E ℝ}
  {dd : ℕ → ℕ → E} {jk : ℕ → ℕ} {s : ℕ → E}
  {acc : ℕ → Prop} {ρ : ℕ → ℝ} {k : ℕ}

/-- The Step-1 decreases along the slow gradient example: `ς β ε` at every order. -/
theorem slowGrad_taylorDecrement_eq (he : ‖e‖ = 1) (hε : 0 < ε) (hβ : 0 < β)
    (hdec : ∀ j ∈ Finset.Icc 1 P.p, ∀ d, (D k).taylorDecrement j d = β * ⟪e, d⟫)
    (hdd : ∀ j ∈ Finset.Icc 1 P.q,
      IsApproxMeasureStep ((D k).taylorDecrement j) ε univ P.ς (dd k j) ∧
        (D k).taylorDecrement j (dd k j) = P.ς * taylorMeasure (D k) j ε univ)
    {j : ℕ} (hj : j ∈ Finset.Icc 1 P.q) :
    (D k).taylorDecrement j (dd k j) = P.ς * (β * ε) := by
  rw [(hdd j hj).2, taylorMeasure_eq_mul_pow_of_inner_pow he (q := 1) hβ.le hε.le
      fun d => by
    rw [hdec j (P.Icc_q_subset hj), pow_one], pow_one]

/-- Along the slow gradient example the test (13.1.53) fails at order `q` (`β > ε^q/(2 q!)`). -/
theorem slowGrad_not_arqpDAPass (hε : 0 < ε) (hβ : ε ^ P.q / P.q ! / 2 < β)
    (hδ₁ : δ₁ k P.q = ε) (hdq : (D k).taylorDecrement P.q (dd k P.q) = P.ς * (β * ε)) :
    ¬ arqpDAPass P (fun _ => ε) D δ₁ dd k P.q := by
  rw [arqpDAPass, hdq, hδ₁, not_le]
  have : ε * ε ^ P.q / P.q ! / 2 < β * ε := by
    rw [show ε * ε ^ P.q / P.q ! / 2 = ε ^ P.q / P.q ! / 2 * ε by ring]
    exact mul_lt_mul_of_pos_right hβ hε
  have e : P.ς * ε * ε ^ P.q / P.q ! / 2 = P.ς * (ε * ε ^ P.q / P.q ! / 2) := by ring
  rw [e]
  exact mul_lt_mul_of_pos_left this P.ς_pos

/-- **One iteration of the slow gradient example is an ARqpIDA/ARqpEDA step** (`X = univ`,
tolerances `ε_j = ε ≤ ½`): with radii `δ_k = δ^{(1)}_k = δ_{k+1} = δ_{s_k} = ε`, decrements
`β ⟪e, d⟫` at all orders `1, …, p` with `ε^q/(2 q!) < β ≤ ε^q/q!`, a weight with
`σ_k/(p+1)! ≤ 1/(4 q!)`, Step-1 displacements achieving the fraction `ς` of the measures, a global
minimizer `s_k` of the model as step, short, with nonpositive model decrements of orders
`1, …, q` on the ball of radius `ε` around it, accuracies passing (13.1.46), and the ratio
`ρ_k = 1`. -/
theorem slowGrad_arqpDAStep (he : ‖e‖ = 1) (hspan : ∀ v : E, ‖v‖ = |⟪e, v⟫|) (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2)
    (hβ : ε ^ P.q / P.q ! / 2 < β) (hβ1 : β ≤ ε ^ P.q / P.q !)
    (hσ54 : σ k / ((P.p + 1)! : ℝ) ≤ 1 / (4 * P.q !))
    (hδ : ∀ j ∈ Finset.Icc 1 P.q, δ k j = ε) (hδ1 : δ (k + 1) = δs k) (hδ₁ : δ₁ k = δ k)
    (hδs : ∀ j ∈ Finset.Icc 1 P.q, δs k j = ε) (hjk : jk k = P.q)
    (hdec : ∀ j ∈ Finset.Icc 1 P.p, ∀ d, (D k).taylorDecrement j d = β * ⟪e, d⟫)
    (hdd : ∀ j ∈ Finset.Icc 1 P.q,
      IsApproxMeasureStep ((D k).taylorDecrement j) ε univ P.ς (dd k j) ∧
        (D k).taylorDecrement j (dd k j) = P.ς * taylorMeasure (D k) j ε univ)
    (hmin : IsMinOn (regularizedModel (D k) P.p (σ k)) univ (s k))
    (hmodel : ∀ ℓ ∈ Finset.Icc 1 P.q, ∀ d, ‖d‖ ≤ ε →
      (ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)).taylorDecrement ℓ d ≤ 0)
    (hs1 : ‖s k‖ < 1) (hhk : ∀ i ∈ Finset.Icc 1 P.p, h k i ≤ P.κs * ‖s k‖ ^ (P.p - i + 1))
    (hacc : ¬ acc k) (hx1 : x (k + 1) = x k + s k) (hσ1 : σ (k + 1) = σ k)
    (hσk : P.σmin ≤ σ k) (hh1 : h (k + 1) = h k) (hρ : ρ k = 1) :
    ARqpDAStep univ P (fun _ => ε) x σ δ δ₁ δs h D dd jk s acc ρ k := by
  have hqm : P.q ∈ Finset.Icc 1 P.q := Finset.mem_Icc.2 ⟨P.one_le_q, le_rfl⟩
  have hς := P.ς_pos
  have hς1 := P.ς_le_one
  have hqf : (0 : ℝ) < P.q ! := by positivity
  have hβ0 : 0 < β := lt_of_le_of_lt (by positivity) hβ
  have hσ0 : 0 ≤ σ k := P.σmin_pos.le.trans hσk
  have hη : P.η₁ ≤ 1 := P.η₁_le_η₂.trans P.η₂_lt_one.le
  have hdv := fun {j} (hj : j ∈ Finset.Icc 1 P.q) => slowGrad_taylorDecrement_eq
      (dd := dd) he hε hβ0 hdec hdd hj
  have hfail : ¬ arqpDAPass P (fun _ => ε) D δ₁ dd k P.q :=
    slowGrad_not_arqpDAPass hε hβ (by rw [hδ₁, hδ _ hqm]) (hdv hqm)
  have hpass_lt : ∀ j ∈ Finset.Icc 1 P.q, j < P.q → arqpDAPass P (fun _ => ε) D δ₁ dd k j := by
    intro j hj hlt
    rw [arqpDAPass, hdv hj, hδ₁, hδ j hj]
    have h1 := pow_div_factorial_le_of_lt hε.le (by linarith only [hε2]) two_pos
      (by linarith only [hε2]) hlt
    have h2 : β * ε ≤ ε * ε ^ j / j ! / 2 := by
      rw [show ε * ε ^ j / j ! / 2 = ε ^ j / j ! / 2 * ε by ring]
      exact mul_le_mul_of_nonneg_right (hβ1.trans h1) hε.le
    have e : P.ς * ε * ε ^ j / j ! / 2 = P.ς * (ε * ε ^ j / j ! / 2) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left h2 hς.le
  refine ⟨⟨fun j hj => by rw [hδ₁, hδ j hj]; exact hε, fun j _ => by rw [hδ₁],
    fun j _ hlt => by rw [hδ₁] at hlt; exact absurd hlt (lt_irrefl _),
    fun j _ => ⟨0, by rw [hδ₁]; norm_num⟩, fun j hj => ?_⟩,
    fun hp => absurd (hp _ hqm) hfail, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => hh1,
    fun _ hr' => absurd hr' (by rw [hρ]; exact not_lt.2 hη), fun ha' => absurd ha' hacc,
    fun ha' => absurd ha' hacc, fun ha' => absurd ha' hacc, fun ha' => absurd ha' hacc⟩
  · rw [hδ₁, hδ j hj, Set.setOf_add_mem_univ]; exact (hdd j hj).1
  · -- Step 2
    refine ⟨by rw [hjk]; exact hqm, by rw [hjk]; exact hfail,
      fun j hj hlt => hpass_lt j hj (by rw [hjk] at hlt; exact hlt),
      fun j hj hlt => absurd (Finset.mem_Icc.1 hj).2 (by rw [hjk] at hlt; omega), ?_,
      mem_univ _, ?_, Or.inr fun ℓ hℓ => ?_, iff_of_false hacc ?_⟩
    · -- (13.1.54)
      rw [hjk, hδ₁, hδ _ hqm, arModelDec_eq]
      have hdq := hdv hqm
      have hdp : (D k).taylorDecrement P.p (dd k P.q) = P.ς * (β * ε) := by
        rw [hdec _ (Finset.mem_Icc.2 ⟨P.one_le_p, le_rfl⟩), ← hdec _ (P.Icc_q_subset hqm), hdq]
      have hin : ⟪e, dd k P.q⟫ = P.ς * ε := by
        rw [hdec _ (P.Icc_q_subset hqm)] at hdq
        have : β * ⟪e, dd k P.q⟫ = β * (P.ς * ε) := by rw [hdq]; ring
        exact mul_left_cancel₀ hβ0.ne' this
      rw [hdp, hspan, hin, abs_of_pos (by positivity)]
      have hpow : (P.ς * ε) ^ (P.p + 1) ≤ P.ς * ε ^ (P.q + 1) := by
        rw [mul_pow]
        exact mul_le_mul (pow_le_of_le_one hς.le hς1 (by omega))
          (pow_le_pow_of_le_one hε.le (by linarith) (by have := P.q_le_p; omega))
          (by positivity) hς.le
      have h3 : σ k / ((P.p + 1)! : ℝ) * (P.ς * ε) ^ (P.p + 1) ≤
          1 / (4 * P.q !) * (P.ς * ε ^ (P.q + 1)) :=
        mul_le_mul hσ54 hpow (by positivity) (by positivity)
      have h2 : P.ς * (ε * ε ^ P.q / P.q ! / 2) < P.ς * (β * ε) := by
        refine mul_lt_mul_of_pos_left ?_ hς
        rw [show ε * ε ^ P.q / P.q ! / 2 = ε ^ P.q / P.q ! / 2 * ε by ring]
        exact mul_lt_mul_of_pos_right hβ hε
      have e1 : P.ς * ε * ε ^ P.q / P.q ! / 4 = 1 / (4 * P.q !) * (P.ς * ε ^ (P.q + 1)) := by
        rw [pow_succ]; field_simp
      have e2 : P.ς * (ε * ε ^ P.q / P.q ! / 2) = 2 * (1 / (4 * P.q !) * (P.ς * ε ^ (P.q + 1))) :=
        by rw [pow_succ]; field_simp; ring
      linarith
    · simp only [arModelDec]
      have := isMinOn_iff.1 hmin (dd k (jk k)) (mem_univ _)
      linarith
    · have hℓ' : ∀ d ∈ closedBall (0 : E) ε ∩ univ,
          (ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)).taylorDecrement ℓ d ≤ 0 :=
        fun d hd => hmodel ℓ hℓ d (mem_closedBall_zero_iff.1 hd.1)
      rw [hδs ℓ hℓ, Set.setOf_add_mem_univ]
      refine ⟨⟨hε, by linarith⟩, 0, ⟨⟨mem_closedBall_self hε.le, mem_univ _⟩, ?_⟩, ?_⟩
      · rw [FormalMultilinearSeries.taylorDecrement_zero_right]
        exact mul_nonpos_of_nonneg_of_nonpos hς.le
          (decrementMeasure_le ⟨0, mem_closedBall_self hε.le, mem_univ _⟩ hℓ')
      · rw [FormalMultilinearSeries.taylorDecrement_zero_right]
        have := P.θ_pos
        positivity
    · rintro ⟨-, i, hi, hlt⟩
      linarith [hhk i hi]
  · rw [hρ, hx1, hσ1]
    exact arAcceptance_of_one_le P.toARParams le_rfl _ _ hσk hσ0
  · rw [hδ1, hρ, ite_eq_left ⟨hη, hs1⟩]

end SlowGradStep

section SlitStep

variable {e₁ e₂ : E} {P : ARqpIDAParams} {ε β ρ t : ℝ} {x : ℕ → E} {σ : ℕ → ℝ}
  {δ δ₁ δs : ℕ → ℕ → ℝ} {h : ℕ → ℕ → ℝ}
  {D : ℕ → FormalMultilinearSeries ℝ E ℝ}
  {dd : ℕ → ℕ → E} {jk : ℕ → ℕ} {s : ℕ → E}
  {acc : ℕ → Prop} {ρr : ℕ → ℝ} {k : ℕ}

/-- **One trial iteration of the slit example is an ARqpIDA-SC step** on `X = slitSet e₂ ρ`
(tolerances `ε_j = ε ≤ 1/4`, `ε < ρ`): at a point of the line with Taylor decrements
`β ⟪e₁, d⟫ + ⟪e₂, d⟫` at all orders `1, …, p`, `ε^q/q! < β ≤ 2 ε^q/q!`, radii
`δ_k = δ^{(1)}_k = δ_{s_k} = ε` (no halving), Step-1 displacements `ς ε e₁` (the fraction `ς` of
the measures `β ε`), a weight with `σ_k/(p+1)! ≤ 1/(2 q!)`, a short step `s_k = t e₁` minimizing
the model on the line, whose model decrements of orders `1, …, q` along the line are nonpositive
on the ball of radius `ε`, accuracies passing (13.1.46), and the ratio `ρ_k = 1`. -/
theorem slit_arqpDAStep (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1) (h12 : ⟪e₁, e₂⟫ = 0)
    (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) (hερ : ε < ρ)
    (hβ : ε ^ P.q / P.q ! ≤ β) (hβ1 : β ≤ 2 * ε ^ P.q / P.q !)
    (hσ54 : σ k / ((P.p + 1)! : ℝ) ≤ 1 / (2 * P.q !)) (hx : ⟪e₂, x k⟫ = 0)
    (hδ : ∀ j ∈ Finset.Icc 1 P.q, δ k j = ε) (hδ1 : δ (k + 1) = δs k) (hδ₁ : δ₁ k = δ k)
    (hδs : ∀ j ∈ Finset.Icc 1 P.q, δs k j = ε) (hdd : ∀ j, dd k j = (P.ς * ε) • e₁)
    (hjk : jk k = P.q)
    (hdec : ∀ j ∈ Finset.Icc 1 P.p, ∀ d, (D k).taylorDecrement j d = β * ⟪e₁, d⟫ + ⟪e₂, d⟫)
    (hs : s k = t • e₁)
    (hmin : ∀ c : ℝ, regularizedModel (D k) P.p (σ k) (s k) ≤
      regularizedModel (D k) P.p (σ k) (c • e₁))
    (hmodel : ∀ ℓ ∈ Finset.Icc 1 P.q, ∀ d, ‖d‖ ≤ ε → ⟪e₂, d⟫ = 0 →
      (ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)).taylorDecrement ℓ d ≤ 0)
    (hs1 : ‖s k‖ < 1) (hhk : ∀ i ∈ Finset.Icc 1 P.p, h k i ≤ P.κs * ‖s k‖ ^ (P.p - i + 1))
    (hacc : ¬ acc k) (hx1 : x (k + 1) = x k + s k) (hσ1 : σ (k + 1) = σ k)
    (hσk : P.σmin ≤ σ k) (hh1 : h (k + 1) = h k) (hρ : ρr k = 1) :
    ARqpDAStep (slitSet e₂ ρ) P (fun _ => ε) x σ δ δ₁ δs h D dd jk s acc ρr k := by
  have h11 : ∀ c : ℝ, ⟪e₁, c • e₁⟫ = c := fun c => by
    rw [inner_smul_right, inner_self_eq_one_of_norm_eq_one he₁, mul_one]
  have h21 : ∀ c : ℝ, ⟪e₂, c • e₁⟫ = 0 := fun c => by
    rw [inner_smul_right, real_inner_comm, h12, mul_zero]
  have hn1 : ∀ c : ℝ, ‖c • e₁‖ = |c| := fun c => by
    rw [norm_smul, he₁, mul_one, Real.norm_eq_abs]
  have hqm : P.q ∈ Finset.Icc 1 P.q := Finset.mem_Icc.2 ⟨P.one_le_q, le_rfl⟩
  have hς := P.ς_pos
  have hς1 := P.ς_le_one
  have hqf : (0 : ℝ) < P.q ! := by positivity
  have hβ0 : 0 < β := lt_of_lt_of_le (by positivity) hβ
  have hσ0 : 0 ≤ σ k := P.σmin_pos.le.trans hσk
  have hη : P.η₁ ≤ 1 := P.η₁_le_η₂.trans P.η₂_lt_one.le
  have hdv : ∀ j ∈ Finset.Icc 1 P.q, (D k).taylorDecrement j (dd k j) = P.ς * (β * ε) :=
    fun j hj => by
      rw [hdd, hdec j (P.Icc_q_subset hj), h11, h21]; ring
  have hfail : ¬ arqpDAPass P (fun _ => ε) D δ₁ dd k P.q := by
    rw [arqpDAPass, hdv _ hqm, hδ₁, hδ _ hqm, not_le]
    have : ε * ε ^ P.q / P.q ! / 2 < β * ε := by
      rw [show ε * ε ^ P.q / P.q ! / 2 = ε ^ P.q / P.q ! / 2 * ε by ring]
      exact mul_lt_mul_of_pos_right (by linarith [div_pos (pow_pos hε P.q) hqf]) hε
    rw [show P.ς * ε * ε ^ P.q / P.q ! / 2 = P.ς * (ε * ε ^ P.q / P.q ! / 2) by ring]
    exact mul_lt_mul_of_pos_left this hς
  have hpass_lt : ∀ j ∈ Finset.Icc 1 P.q, j < P.q → arqpDAPass P (fun _ => ε) D δ₁ dd k j := by
    intro j hj hlt
    rw [arqpDAPass, hdv j hj, hδ₁, hδ j hj]
    have h1 := pow_div_factorial_le_of_lt hε.le (by linarith only [hε4]) four_pos
      (by linarith only [hε4]) hlt
    have h2 : β * ε ≤ ε * ε ^ j / j ! / 2 := by
      rw [show ε * ε ^ j / j ! / 2 = ε ^ j / j ! / 2 * ε by ring]
      have e : 2 * ε ^ P.q / P.q ! = 2 * (ε ^ P.q / P.q !) := by ring
      exact mul_le_mul_of_nonneg_right (by linarith) hε.le
    rw [show P.ς * ε * ε ^ j / j ! / 2 = P.ς * (ε * ε ^ j / j ! / 2) by ring]
    exact mul_le_mul_of_nonneg_left h2 hς.le
  have hxs : ⟪e₂, x k + s k⟫ = 0 := by rw [inner_add_right, hx, hs, h21, add_zero]
  refine ⟨⟨fun j hj => by rw [hδ₁, hδ j hj]; exact hε, fun j _ => by rw [hδ₁],
    fun j _ hlt => by rw [hδ₁] at hlt; exact absurd hlt (lt_irrefl _),
    fun j _ => ⟨0, by rw [hδ₁]; norm_num⟩, fun j hj => ?_⟩,
    fun hp => absurd (hp _ hqm) hfail, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => hh1,
    fun _ hr' => absurd hr' (by rw [hρ]; exact not_lt.2 hη), fun ha' => absurd ha' hacc,
    fun ha' => absurd ha' hacc, fun ha' => absurd ha' hacc, fun ha' => absurd ha' hacc⟩
  · -- the Step-1 displacements
    rw [hδ₁, hδ j hj]
    have hn : dd k j ∈ closedBall (0 : E) ε := by
      rw [hdd, mem_closedBall_zero_iff, hn1, abs_of_pos (by positivity)]
      nlinarith
    have hmem : x k + dd k j ∈ slitSet e₂ ρ := by
      rw [hdd]
      exact add_mem_slitSet_of_inner_eq_zero hx
        (h21 _)
    refine ⟨⟨hn, hmem⟩, ?_⟩
    rw [hdv j hj]
    change P.ς * taylorMeasure (D k) j ε _ ≤ _
    rw [taylorMeasure_slitSet_of_lt he₁ he₂.le h12 hβ0.le hε.le hερ hx (hdec j
        (P.Icc_q_subset hj))]
  · -- Step 2
    refine ⟨by rw [hjk]; exact hqm, by rw [hjk]; exact hfail,
      fun j hj hlt => hpass_lt j hj (by rw [hjk] at hlt; exact hlt),
      fun j hj hlt => absurd (Finset.mem_Icc.1 hj).2 (by rw [hjk] at hlt; omega), ?_,
      Or.inl hxs, ?_, Or.inr fun ℓ hℓ => ?_, iff_of_false hacc ?_⟩
    · -- (13.1.54)
      rw [hjk, hδ₁, hδ _ hqm, arModelDec_eq, hdec _ (Finset.mem_Icc.2 ⟨P.one_le_p, le_rfl⟩),
        hdd, h11, h21, hn1, abs_of_pos (by
            positivity)]
      have hpow : (P.ς * ε) ^ (P.p + 1) ≤ P.ς * ε ^ (P.q + 1) := by
        rw [mul_pow]
        exact mul_le_mul (pow_le_of_le_one hς.le hς1 (by omega))
          (pow_le_pow_of_le_one hε.le (by linarith) (by have := P.q_le_p; omega))
          (by positivity) hς.le
      have h3 : σ k / ((P.p + 1)! : ℝ) * (P.ς * ε) ^ (P.p + 1) ≤
          1 / (2 * P.q !) * (P.ς * ε ^ (P.q + 1)) :=
        mul_le_mul hσ54 hpow (by positivity) (by positivity)
      have h2 : P.ς * (ε ^ P.q / P.q ! * ε) ≤ P.ς * (β * ε) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hβ hε.le) hς.le
      have e1 : P.ς * ε * ε ^ P.q / P.q ! / 4 = 1 / (4 * P.q !) * (P.ς * ε ^ (P.q + 1)) := by
        rw [pow_succ]; field_simp
      have e2 : P.ς * (ε ^ P.q / P.q ! * ε) = 4 * (1 / (4 * P.q !) * (P.ς * ε ^ (P.q + 1))) := by
        rw [pow_succ]; field_simp
      have e3 : 1 / (2 * P.q !) * (P.ς * ε ^ (P.q + 1)) =
          2 * (1 / (4 * P.q !) * (P.ς * ε ^ (P.q + 1))) := by field_simp; ring
      have : 0 ≤ 1 / (4 * P.q !) * (P.ς * ε ^ (P.q + 1)) := by positivity
      have h4 : P.ς * (β * ε) - σ k / ((P.p + 1)! : ℝ) * (P.ς * ε) ^ (P.p + 1) =
          β * (P.ς * ε) + 0 - σ k / ((P.p + 1)! : ℝ) * (P.ς * ε) ^ (P.p + 1) := by ring
      linarith
    · simp only [arModelDec]
      have := hmin (P.ς * ε)
      rw [hdd]
      linarith
    · have hℓ' : ∀ d ∈ closedBall (0 : E) ε ∩
          {e | x k + s k + e ∈ slitSet e₂ ρ},
          (ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)).taylorDecrement ℓ d ≤ 0 :=
        fun d hd => hmodel ℓ hℓ d (mem_closedBall_zero_iff.1 hd.1)
          (inner_eq_zero_of_add_mem_slitSet he₂.le hxs hd.2 ((mem_closedBall_zero_iff.1
              hd.1).trans_lt hερ))
      rw [hδs ℓ hℓ]
      have h0 : (0 : E) ∈ closedBall 0 ε ∩
          {e | x k + s k + e ∈ slitSet e₂ ρ} :=
        ⟨mem_closedBall_self hε.le,
          by simpa using add_mem_slitSet_of_inner_eq_zero (ρ := ρ) hxs (inner_zero_right e₂)⟩
      refine ⟨⟨hε, by linarith⟩, 0, ⟨h0, ?_⟩, ?_⟩
      · rw [FormalMultilinearSeries.taylorDecrement_zero_right]
        exact mul_nonpos_of_nonneg_of_nonpos hς.le (decrementMeasure_le ⟨0, h0⟩ hℓ')
      · rw [FormalMultilinearSeries.taylorDecrement_zero_right]
        have := P.θ_pos
        positivity
    · rintro ⟨-, i, hi, hlt⟩
      linarith [hhk i hi]
  · rw [hρ, hx1, hσ1]
    exact arAcceptance_of_one_le P.toARParams le_rfl _ _ hσk hσ0
  · rw [hδ1, hρ, ite_eq_left ⟨hη, hs1⟩]

/-- **An accuracy-improving iteration at a flat point of the line** (the continuation of the slit
example): at a point of the line where the Taylor decrements are `⟪e₂, d⟫` at all orders
`1, …, p`, with radii `δ_k = δ^{(1)}_k = ε < ρ` and zero Step-1 displacements, the test (13.1.53)
holds at every order, and Step 5 keeps the iterate, the weight and the radii and multiplies the
accuracies by `γ_h`. -/
theorem slit_arqpDAStep_of_acc (he₂ : ‖e₂‖ ≤ 1) (hε : 0 < ε) (hερ : ε < ρ) (hx : ⟪e₂, x k⟫ = 0)
    (hδ : ∀ j ∈ Finset.Icc 1 P.q, δ k j = ε) (hδ₁ : δ₁ k = δ k) (hdd : ∀ j, dd k j = 0)
    (hdec : ∀ j ∈ Finset.Icc 1 P.p, ∀ d, (D k).taylorDecrement j d = ⟪e₂, d⟫)
    (hacc : acc k) (hx1 : x (k + 1) = x k) (hδ1 : δ (k + 1) = δ k) (hσ1 : σ (k + 1) = σ k)
    (hh1 : ∀ i, h (k + 1) i = P.γh * h k i) :
    ARqpDAStep (slitSet e₂ ρ) P (fun _ => ε) x σ δ δ₁ δs h D dd jk s acc ρr k := by
  have hς := P.ς_pos
  have hpass : ∀ j ∈ Finset.Icc 1 P.q, arqpDAPass P (fun _ => ε) D δ₁ dd k j := fun j hj => by
    rw [arqpDAPass, hdd, FormalMultilinearSeries.taylorDecrement_zero_right, hδ₁, hδ j hj]
    positivity
  refine ⟨⟨fun j hj => by rw [hδ₁, hδ j hj]; exact hε, fun j _ => by rw [hδ₁],
    fun j _ hlt => by rw [hδ₁] at hlt; exact absurd hlt (lt_irrefl _),
    fun j _ => ⟨0, by rw [hδ₁]; norm_num⟩, fun j hj => ?_⟩,
    fun _ => hacc, fun ⟨j, hj, hj'⟩ => absurd (hpass j hj) hj', fun h' => absurd hacc h',
    fun h' => absurd hacc h', fun h' => absurd hacc h', fun h' => absurd hacc h',
    fun _ => hx1, fun _ => hδ1, fun _ => hσ1, fun _ => hh1⟩
  rw [hδ₁, hδ j hj, hdd]
  have h0 : (0 : E) ∈ closedBall 0 ε ∩ {e | x k + e ∈ slitSet e₂ ρ} :=
    ⟨mem_closedBall_self hε.le,
      by simpa using add_mem_slitSet_of_inner_eq_zero (ρ := ρ) hx (inner_zero_right e₂)⟩
  refine ⟨h0, ?_⟩
  rw [FormalMultilinearSeries.taylorDecrement_zero_right]
  refine mul_nonpos_of_nonneg_of_nonpos hς.le (decrementMeasure_le ⟨0, h0⟩ fun d hd => ?_)
  rw [hdec j (P.Icc_q_subset hj), inner_eq_zero_of_add_mem_slitSet he₂ hx hd.2
    ((mem_closedBall_zero_iff.1 hd.1).trans_lt hερ)]


end SlitStep

end Optimization

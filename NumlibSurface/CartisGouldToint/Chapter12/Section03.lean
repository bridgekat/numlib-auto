import NumlibSurface.CartisGouldToint.Chapter12.Section02

/-!
# Cartis–Gould–Toint §12.3: Inexact global minimization in the ARqp algorithm

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §12.3 (no numbered results),
together with the relaxed Step 2 of the Notes to §12.2.2.

The purpose of Step 2 of ARqp is a sufficient decrease of the Taylor model at successful
iterations. §12.3 observes that a step may be accepted (with (12.2.27)) without checking the
approximate model optimality (12.2.29) as soon as it achieves the sufficient decrease (12.3.1),
or is long, `‖s_k‖ ≥ κ_decr^{1/(p+1)} ε_min^{ω/(p+1)}` (12.3.2) (sufficient decrease then follows
from Lemma 4.1.1); the Notes to §12.2.2 propose the same relaxation for long steps and state that
"this modification does not affect the conclusions of the complexity theorem". Here this is made
precise: `IsARqpSufficientDecreaseRun` is the ARqp run with this relaxed Step 2
(every ARqp run is one), and `complexity_arqpSufficientDecrease` shows that the bounds of
Theorem 12.2.14 persist for `ω ≥ π_q` with `κ_{Δm}` replaced by
`min(κ_{Δm}, κ_decr, σ_min κ_decr/(p+1)!)` and `min_j ε_j^{π_j}` by `ε_min^ω`.

## Main definitions

* `ARqpRelaxedStep` — the relaxed Step 2;
* `IsARqpSufficientDecreaseRun` — ARqp with the relaxed Step 2.

## Main results

* `IsARqpSufficientDecreaseRun.of_algorithm_12_2_2` — every ARqp run is such a run;
* `complexity_arqpSufficientDecrease` — the complexity bounds of Theorem 12.2.14.

## Deviations from the book

* (12.3.1) is printed as `ΔT_{f,j}(x_k, s_k) ≥ κ_decr ε_j^ω` "for some `j`"; it is read with the
  decrease `ΔT_{f,p}(x_k, s_k)` that the ratio and the complexity analysis use, and with
  `ε_min^ω` (as in (12.3.2)).
* The complexity bound is stated for every `ω ≥ π_q` (the book's choice is `ω = π_q`, the exponent
  of Theorem 12.2.14), in terms of `ε_min^ω` instead of `min_j ε_j^{π_j}`.

## Not formalized

The qualitative discussion of premature termination of Algorithm 12.2.3 and of the practicality
of global polynomial minimization.
-/

open Set Metric Filter Optimization
open scoped Nat

namespace CartisGouldToint.Chapter12

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The relaxed Step 2 of ARqp** ([cartis2022evaluation], §12.3 and the Notes to §12.2.2): the
step `s` from `x` (model data `M`) satisfies the Step-2 conditions of ARqp, or it does not increase
the model (with termination only at a global model minimizer `0`), its radii lie in `(0, 1]`, and
it achieves the sufficient decrease `ΔT_{f,p}(x, s) ≥ κ_decr ε_min^ω` (12.3.1) or is long,
`‖s‖ ≥ κ_decr^{1/(p+1)} ε_min^{ω/(p+1)}` (12.3.2), with `ε_min = min_j ε_j`. -/
def ARqpRelaxedStep (P : ARqpParams) (p q : ℕ) (ε : ℕ → ℝ) (κdecr ω : ℝ) (M : ARqpData E)
    (x s : E) (δs : ℕ → ℝ) (dm : ℕ → E) : Prop :=
  ARqpStep univ P q ε M x s δs dm ∨
    (M.model s ≤ M.model 0 ∧ (M.model s = M.model 0 → IsMinOn M.model univ 0) ∧
      (∀ j ∈ Finset.Icc 1 q, 0 < δs j ∧ δs j ≤ 1) ∧
      (κdecr * finMin 1 ε q ^ ω ≤ M.pred s ∨
        κdecr ^ (1 / ((p + 1 : ℕ) : ℝ)) * finMin 1 ε q ^ (ω / ((p + 1 : ℕ) : ℝ)) ≤ ‖s‖))

/-- **ARqp with the relaxed Step 2** ([cartis2022evaluation], §12.3): the fields of
`algorithm_12_2_2` (Step 1 with the strict test and witnesses, Steps 3–4, radii inherited at
successful iterations and kept with the witnesses at unsuccessful ones), with Step 2 replaced by
`ARqpRelaxedStep` for the constants `κ_decr` and `ω`. -/
structure IsARqpSufficientDecreaseRun (f : E → ℝ) (P : ARqpParams) (p q : ℕ) (ε δ₀ : ℕ → ℝ)
    (κdecr ω : ℝ) (x s : ℕ → E) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → E) : Prop where
  /-- Steps 2–4: an adaptive-regularization run with the relaxed Step 2. -/
  toIsARRun : IsARRun P.toARParams (arqpStop₁ P q ε (arqpData f p x σ) δ d)
    (fun k => ARqpRelaxedStep P p q ε κdecr ω (arqpData f p x σ k) (x k) (s k) (δs k) (dm k))
    (arqpStop₂ (arqpData f p x σ) s) (arqpRho f p x s σ) x s σ
  /-- The initial radii. -/
  delta_zero : δ 0 = δ₀
  /-- Step 1: approximate optimality displacements at every iteration reached. -/
  witness : ∀ k, (∀ i < k, ¬ arqpStop f P p q ε x s σ δ d i) → ∀ j ∈ Finset.Icc 1 q,
    IsApproxMeasureStep ((ftaylorSeries ℝ f (x k)).taylorDecrement j) (δ k j) univ P.ς (d k j)
  /-- Step 3: radii and witnesses. -/
  radii : UntilHit (arqpStop f P p q ε x s σ δ d) fun k =>
    (P.η₁ ≤ arqpRho f p x s σ k → δ (k + 1) = δs k) ∧
      (¬ P.η₁ ≤ arqpRho f p x s σ k → δ (k + 1) = δ k ∧ d (k + 1) = d k)

variable {f : E → ℝ} {P : ARqpParams} {p q : ℕ} {ε δ₀ : ℕ → ℝ} {κdecr ω : ℝ} {x s : ℕ → E}
  {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → E} {L : ℕ → ℝ}

/-- **Every ARqp run is a run with the relaxed Step 2** (for any `κ_decr`, `ω`). -/
theorem IsARqpSufficientDecreaseRun.of_algorithm_12_2_2
    (h : algorithm_12_2_2 f P p q ε δ₀ x s σ δ δs d dm) :
    IsARqpSufficientDecreaseRun f P p q ε δ₀ κdecr ω x s σ δ δs d dm := by
  have hU : ∀ y : E, {e : E | y + e ∈ (univ : Set E)} = univ := fun y => by ext; simp
  refine ⟨h.toIsARRun.mono fun k hk => Or.inl hk, h.delta_zero, fun k hk j hj => ?_, h.radii⟩
  have := h.witness k hk j hj
  rwa [hU] at this

namespace IsARqpSufficientDecreaseRun

variable (h : IsARqpSufficientDecreaseRun f P p q ε δ₀ κdecr ω x s σ δ δs d dm)
include h

/-- The model decreases strictly before termination. -/
theorem model_lt {k : ℕ} (hk : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) :
    arqpModel f p x σ k (s k) < arqpModel f p x σ k 0 := by
  have hstep := h.toIsARRun.step_of_forall_le hk
  have hle : arqpModel f p x σ k (s k) ≤ arqpModel f p x σ k 0 := hstep.elim (·.model_le) (·.1)
  exact lt_of_le_of_ne hle fun h2 => hk k le_rfl (Or.inr h2)

/-- The radii returned by every step before termination lie in `(0, 1]`. -/
theorem stepRadii_mem {k : ℕ} (hk : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) :
    ∀ j ∈ Finset.Icc 1 q, 0 < δs k j ∧ δs k j ≤ 1 := by
  rcases h.toIsARRun.step_of_forall_le hk with hs | hs
  · exact fun j hj => ⟨hs.radius_pos j hj, hs.radius_le_one j hj⟩
  · exact hs.2.2.1

/-- The radii stay in `(0, 1]` up to termination. -/
theorem delta_mem (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1) :
    ∀ k, (∀ i < k, ¬ arqpStop f P p q ε x s σ δ d i) →
      ∀ j ∈ Finset.Icc 1 q, 0 < δ k j ∧ δ k j ≤ 1 := by
  intro k
  induction k with
  | zero => exact fun _ => by rw [h.delta_zero]; exact hδ₀
  | succ k ih =>
    intro hk j hj
    have hk' : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i := fun i hi => hk i (by omega)
    obtain ⟨hs, hu⟩ := h.radii k hk'
    by_cases hρ : P.η₁ ≤ arqpRho f p x s σ k
    · rw [hs hρ]; exact h.stepRadii_mem hk' j hj
    · rw [(hu hρ).1]; exact ih (fun i hi => hk' i hi.le) j hj

/-- Lemma 4.1.2 for the relaxed run: `σ_min ≤ σ_k ≤ σ_max` up to termination. -/
theorem sigma_le (hf : AssumptionD1pL f p L) (hp : 1 ≤ p) :
    ∀ k, (∀ i < k, ¬ arqpStop f P p q ε x s σ δ d i) →
      P.σmin ≤ σ k ∧ σ k ≤ arSigmaMax P.toARParams (L p) := by
  intro k hk
  have := IsARRun.sigma_le (f := f) (p := p) (x := x) (s := s) h.toIsARRun (C := univ)
    convex_univ (fun y _ => hf.contDiff.contDiffAt) (hf.lipschitz p (Finset.mem_Icc.2 ⟨hp, le_rfl⟩))
    (mem_univ _) (fun k hk _ => ⟨mem_univ _, h.model_lt hk⟩) k hk
  exact ⟨this.2.1, this.2.2⟩

/-- The Step-1 data at `k + 1` after a successful iteration `k`, in local form. -/
theorem next {k : ℕ} (hk : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i)
    (hs : P.η₁ ≤ arqpRho f p x s σ k) :
    x (k + 1) = x k + s k ∧ δ (k + 1) = δs k ∧
      (∀ j ∈ Finset.Icc 1 q, IsApproxMeasureStep
        ((ftaylorSeries ℝ f (x k + s k)).taylorDecrement j) (δs k j) univ P.ς (d (k + 1) j)) := by
  have hx1 := h.toIsARRun.eq_add_of_succ hk hs
  have hδ1 := (h.radii k hk).1 hs
  refine ⟨hx1, hδ1, fun j hj => ?_⟩
  have hw := h.witness (k + 1) (fun i hi => hk i (by omega)) j hj
  rwa [hx1, hδ1] at hw

end IsARqpSufficientDecreaseRun

/-- `π_j` is nondecreasing in `j ≤ p`. -/
theorem arqpPi_mono {p q j j' : ℕ} (hjj' : j ≤ j') (hj' : j' ≤ p) :
    arqpPi p q j ≤ arqpPi p q j' := by
  unfold arqpPi arqpPiOf
  split_ifs
  · apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact_mod_cast (show p - j' + 1 ≤ p - j + 1 by omega)
  · gcongr

/-- **Complexity of ARqp with the relaxed Step 2** ([cartis2022evaluation], §12.3 and the Notes to
§12.2.2: "this modification does not affect the conclusions of the complexity theorem"). Assume
f.Bb and f.D1pL, `1 ≤ q ≤ p`, `ε ∈ (0, 1]^q`, `δ₀ ∈ (0, 1]^q`, `σ_min > 0`, `θ < ς`, `κ_decr > 0`
and `ω ≥ π_q` (`ω = π_q` is the book's choice), and the radii hypotheses of Theorem 12.2.14 for the
steps of the original type (those satisfying the Step-2 conditions of ARqp): if `q ≤ 2`, their
radii are `1`; if `q > 2`, short ones come with `δ_{s_k,j} ≥ κ_δ(σ_k) ε_j` ((12.2.50)). Then a
run with the relaxed Step 2 terminates at some `k_ε` where `x_{k_ε}` is an
`(ε, δ_ε)`-approximate `q`-th order minimizer for some `δ_ε ∈ (0, 1]^q`, after at most
`κ^a (f(x₀) - f_low)/ε_min^ω + κ^c` evaluations of `f` and
`κ^s (f(x₀) - f_low)/ε_min^ω + 2` evaluations of the derivatives, where
`κ^s = 1/(η₁ κ')`, `κ^a = κ^s (1 + |log γ₁|/log γ₂)`, `κ^c` is that of Theorem 12.2.14 and
`κ' = min(κ_{Δm}, κ_decr, σ_min κ_decr/(p+1)!)`. -/
theorem complexity_arqpSufficientDecrease {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {d dm : ℕ → ℕ → EuclideanSpace ℝ (Fin n)} {flow : ℝ}
    (hb : Chapter02.AssumptionBb f flow) (hf : AssumptionD1pL f p L) (hq : 1 ≤ q) (hqp : q ≤ p)
    (hσmin : 0 < P.σmin) (hθς : P.θ < P.ς) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1)
    (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1) (hκ : 0 < κdecr) (hω : arqpPi p q q ≤ ω)
    (h : IsARqpSufficientDecreaseRun f P p q ε δ₀ κdecr ω x s σ δ δs d dm)
    (hrad : (q ≤ 2 → ∀ k, (∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) →
        ARqpStep univ P q ε (arqpData f p x σ k) (x k) (s k) (δs k) (dm k) →
        ∀ j ∈ Finset.Icc 1 q, δs k j = 1) ∧
      (2 < q → ∀ k, (∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) →
        ARqpStep univ P q ε (arqpData f p x σ k) (x k) (s k) (δs k) (dm k) → ‖s k‖ < 1 →
        ∀ j ∈ Finset.Icc 1 q, arqpKappaDelta P (finMax 1 L p) (σ k) * ε j ≤ δs k j)) :
    ∃ kε, IsFirstHit (arqpStop f P p q ε x s σ δ d) kε ∧
      (∃ δε : ℕ → ℝ, IsEpsDeltaApproxMinimizer f q ε δε (x kε)) ∧
      (funEvalCount kε : ℝ) ≤
        1 / (P.η₁ * min (arqpKappaDm P L p q) (min κdecr (P.σmin / ((p + 1)! : ℝ) * κdecr))) *
          (1 + |Real.log P.γ₁| / Real.log P.γ₂) * (f (x 0) - flow) / finMin 1 ε q ^ ω +
          kappaCARqp P L p ∧
      (derivEvalCount (fun k => P.η₁ ≤ arqpRho f p x s σ k) kε : ℝ) ≤
        1 / (P.η₁ * min (arqpKappaDm P L p q) (min κdecr (P.σmin / ((p + 1)! : ℝ) * κdecr))) *
          (f (x 0) - flow) / finMin 1 ε q ^ ω + 2 := by
  have hp : 1 ≤ p := hq.trans hqp
  have hLp : 1 ≤ L p := hf.one_le p (Finset.mem_Icc.2 ⟨hp, le_rfl⟩)
  have hL1 : 1 ≤ finMax 1 L p := one_le_finMax
  set εm := finMin 1 ε q with hεm_def
  have hεm : 0 < εm := finMin_pos one_pos fun j hj => (hε j hj).1
  have hεm1 : εm ≤ 1 := finMin_le_left
  set X := εm ^ ω with hX
  have hX0 : 0 < X := Real.rpow_pos_of_pos hεm _
  have hfacp : (0 : ℝ) < (p + 1)! := by positivity
  set κ' := min (arqpKappaDm P L p q) (min κdecr (P.σmin / ((p + 1)! : ℝ) * κdecr)) with hκ'
  have hκDm := arqpKappaDm_pos (q := q) hσmin hθς hLp
  have hκ'0 : 0 < κ' := lt_min hκDm (lt_min hκ (by positivity))
  have hη := P.η₁_pos
  have hπ0 : ∀ j, 0 ≤ arqpPi p q j := fun j => arqpPiOf_nonneg _ p j
  have hω0 : 0 ≤ ω := (hπ0 q).trans hω
  -- `ε_min^ω ≤ min_j ε_j^{π_j}`
  have hXm : X ≤ finMin 1 (fun j => ε j ^ arqpPi p q j) q := by
    refine le_finMin (Real.rpow_le_one hεm.le hεm1 hω0) fun j hj => ?_
    have hjq := (Finset.mem_Icc.1 hj).2
    calc X ≤ εm ^ arqpPi p q q := Real.rpow_le_rpow_of_exponent_ge hεm hεm1 hω
      _ ≤ εm ^ arqpPi p q j :=
          Real.rpow_le_rpow_of_exponent_ge hεm hεm1 (arqpPi_mono hjq hqp)
      _ ≤ ε j ^ arqpPi p q j := Real.rpow_le_rpow hεm.le (finMin_le hj) (hπ0 j)
  -- the decrease at successful iterations followed by a non-terminating one
  have hdec : ∀ k, (∀ i ≤ k + 1, ¬ arqpStop f P p q ε x s σ δ d i) →
      P.η₁ ≤ arqpRho f p x s σ k → P.η₁ * (κ' * X) ≤ f (x k) - f (x (k + 1)) := by
    intro k hk hs
    have hk' : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i := fun i hi => hk i (by omega)
    have hσ := h.sigma_le hf hp k fun i hi => hk' i hi.le
    have hlt := h.model_lt hk'
    have hT := lt_taylorDecrement_of_regularizedModel_lt hlt
    have hσ0 : 0 ≤ σ k := P.σmin_nonneg.trans hσ.1
    have hpos : 0 < (ftaylorSeries ℝ f (x k)).taylorDecrement p (s k) :=
      lt_of_le_of_lt (by positivity) hT
    have hmain : κ' * X ≤ (ftaylorSeries ℝ f (x k)).taylorDecrement p (s k) := by
      rcases h.toIsARRun.step_of_forall_le hk' with hst | ⟨-, -, -, hd | hlong⟩
      · obtain ⟨hx1, hδ1, hw⟩ := h.next hk' hs
        have hfail : ¬ MeasureTestPasses
            (fun j => (ftaylorSeries ℝ f (x k + s k)).taylorDecrement j) q P.ς ε (δs k)
            (d (k + 1)) := by
          intro ht
          refine hk (k + 1) le_rfl (Or.inl ?_)
          change MeasureTestPasses (fun j => (ftaylorSeries ℝ f (x (k + 1))).taylorDecrement j)
            q P.ς ε (δ (k + 1)) (d (k + 1))
          rwa [hx1, hδ1]
        have hrad' : (q ≤ 2 → ∀ j ∈ Finset.Icc 1 q, δs k j = 1) ∧
            (2 < q → 1 ≤ ‖s k‖ ∨ ∀ j ∈ Finset.Icc 1 q,
              arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)) * ε j ≤
                δs k j) := by
          refine ⟨fun hq2 => hrad.1 hq2 k hk' hst, fun hq2 => ?_⟩
          by_cases hlong : 1 ≤ ‖s k‖
          · exact Or.inl hlong
          refine Or.inr fun j hj => le_trans ?_ (hrad.2 hq2 k hk' hst (not_le.1 hlong) j hj)
          exact mul_le_mul_of_nonneg_right (arqpKappaDelta_anti P hL1 hσ0 hσ.2)
            (hε j hj).1.le
        have hU : {e : EuclideanSpace ℝ (Fin n) | x k + s k + e ∈ (univ : Set _)} = univ := by
          ext; simp
        have := arqp_decrease_local hf.on_univ (subset_univ _) hq hqp hθς hε (mem_univ _) hσ.1
          hσ.2 hst hlt (by rw [hU]; exact hw) hfail (u := q ≤ 2)
          ⟨hrad'.1, fun h' => hrad'.2 (not_le.1 h')⟩
        calc κ' * X ≤ arqpKappaDm P L p q * finMin 1 (fun j => ε j ^ arqpPi p q j) q :=
              mul_le_mul (min_le_left _ _) hXm hX0.le hκDm.le
          _ ≤ _ := this
      · calc κ' * X ≤ κdecr * X :=
              mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) hX0.le
          _ ≤ _ := hd
      · have hn : ((p + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        have hpow : κdecr * X ≤ ‖s k‖ ^ (p + 1) := by
          have := pow_le_pow_left₀ (by positivity) hlong (p + 1)
          refine le_trans (le_of_eq ?_) this
          rw [mul_pow, ← Real.rpow_natCast (κdecr ^ _), ← Real.rpow_natCast (εm ^ _),
            ← Real.rpow_mul hκ.le, ← Real.rpow_mul hεm.le, one_div_mul_cancel hn,
            div_mul_cancel₀ _ hn, Real.rpow_one]
        calc κ' * X ≤ P.σmin / ((p + 1)! : ℝ) * κdecr * X :=
              mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) hX0.le
          _ = P.σmin / ((p + 1)! : ℝ) * (κdecr * X) := by ring
          _ ≤ σ k / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) := by
              gcongr
              exact hσ.1
          _ ≤ _ := hT.le
    have := (h.toIsARRun.sub_ge_of_succ (w := f)
      (pred := fun k => (ftaylorSeries ℝ f (x k)).taylorDecrement p (s k)) hk' rfl hpos hs).2
    exact (mul_le_mul_of_nonneg_left hmain hη.le).trans this
  have hδ : 0 < P.η₁ * (κ' * X) := by positivity
  obtain ⟨kε, hk, hF, hD⟩ := h.toIsARRun.exists_isFirstHit_of_decrease
    (σmax := arSigmaMax P.toARParams (L p)) (fun k hk => (h.sigma_le hf hp k hk).2)
    (V := fun k => f (x k)) (Vlow := flow) hδ
    (fun k hk => by
      have hσ := h.toIsARRun.sigma_pos (K := k) (fun i hi => hk i hi.le) k le_rfl
      have hT := lt_taylorDecrement_of_regularizedModel_lt (h.model_lt hk)
      exact (h.toIsARRun.accept k hk).le (w := f) rfl (lt_of_le_of_lt (by positivity) hT))
    (fun k _ => hb (x k)) hdec
  have hlog := P.toARParams.log_γ₂_pos
  refine ⟨kε, hk, ?_, hF.trans_eq ?_, hD.trans_eq ?_⟩
  · by_cases h1 : arqpStop₁ P q ε (arqpData f p x σ) δ d kε
    · exact ⟨δ kε, fun j hj => ⟨hε j hj, h.delta_mem hδ₀ kε hk.2 j hj⟩,
        MeasureTestPasses.isEpsDeltaApprox P.ς_pos (h.witness kε hk.2) h1⟩
    · have h2 : arqpStop₂ (arqpData f p x σ) s kε := hk.1.resolve_left h1
      have hσ : 0 < σ kε := h.toIsARRun.sigma_pos hk.2 kε le_rfl
      have hU : {e : EuclideanSpace ℝ (Fin n) | x kε + e ∈ (univ : Set _)} = univ := by
        ext; simp
      have hmin : IsMinOn (arqpModel f p x σ kε) univ 0 := by
        rcases h.toIsARRun.step kε hk.2 h1 with hst | hst
        · have := hst.isMinOn_of_eq h2
          rwa [hU] at this
        · exact hst.2.1 h2
      exact ⟨_, isEpsDeltaApproxMinimizer_of_isMinOn_zero hf hqp hε hσ hmin⟩
  · rw [kappaCARqp]
    field_simp
  · field_simp

end CartisGouldToint.Chapter12

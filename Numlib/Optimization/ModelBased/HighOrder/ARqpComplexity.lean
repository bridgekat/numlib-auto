import Numlib.Analysis.Calculus.AnchoredLipschitzDerivs
import Numlib.Optimization.ModelBased.HighOrder.ARqp
import Numlib.Optimization.ModelBased.HighOrder.Orders
import Numlib.Optimization.ModelBased.HighOrderModel
import Numlib.Optimization.ModelBased.HighOrderStep
import Numlib.Optimization.Optimality.HighOrder

/-!
# Evaluation complexity of ARqp with exact derivatives

The complexity analysis of the adaptive-regularization method ARqp ([cartis2022evaluation],
§12.2.2, Algorithm 12.2.2) run with the exact model data
`arqpData f p x σ k = ARqpData.ofTaylor (ftaylorSeries ℝ f (x k)) p (σ k)` on a feasible set `X`
(the unconstrained method is `X = univ`; ARqp-SC of §14.2 is a closed `X`).

The smoothness hypothesis is the top-order anchored condition
`LipschitzDerivsAnchored f C A p p L` (`∇^p f` is `L_p`-Lipschitz anchored at the points of `A`,
`X ⊆ C` open and convex, `L_p ≥ 1`), where `A` contains the sublevel set `{y ∈ X | f(y) ≤ f(x₀)}`;
the jet bounds `‖∇^j f(x)‖ ≤ L_f` at the anchors (`j ∈ [2, p]`, `L_f = finMax 1 L p`) are only used
to certify a termination in Step 2 and to construct runs with the radii property. The iterates
stay in the sublevel set (`IsARqpRun.mem_sublevel`), the
models are built at the iterates, and the trial points are related to them by Taylor's theorem
anchored at the iterate. Lipschitz derivatives on `C` (e.g. on the whole space) are the case
`A = C`.

The Step-2 radii are handled in a *radii mode* `u`: unit radii if `u`, and the lower bound
`δ_{s_k,j} ≥ κ_δ(σ_max) ε_j` ((12.2.51)) at every order if `¬ u`; [cartis2022evaluation] analyses
the mode `u = (q ≤ 2)`. The exponents are `π_j = arqpPiOf u p j`.

## Main definitions

* `Optimization.arqpData`, `arqpModel`, `arqpStop`, `arqpRho`: the exact model data, model,
  termination test and ratio;
* `Optimization.arqpKappaDelta` (`κ_δ(σ)`), `arqpTau` (`τ_j`), `arqpKappaHat` (the
  `κ̂ = min(κ_{δ,min}, τ_q/2)`), `arqpPiOf`, `arqpKappaDmOf` (`κ_{Δm}`), `kappaSARqpOf`,
  `kappaAARqpOf`, `kappaCARqp`: the constants of Lemmas 12.2.9–12.2.13 and Theorem 12.2.14.

## Main results

* `Optimization.IsARqpRun.mem_sublevel`, `IsARqpRun.sigma_le_of_anchored` (Lemma 4.1.2 for
  ARqp);
* `Optimization.exists_isARqpRun_of_anchored`: runs with the radii property (12.2.50);
* `Optimization.ARqpStep.exists_radius_ineq` (Lemma 12.2.11, local form),
  `ARqpStep.exists_norm_pow_ge` (Lemma 12.2.12, local form),
  `ARqpStep.taylorDecrement_ge`, `IsARqpRun.decrease` (Lemma 12.2.13);
* `Optimization.isEpsDeltaApprox_of_isMinOn_zero_of_jet`: certification at a model minimizer
  (Lemma 12.2.10);
* `Optimization.IsARqpRun.complexity`: Theorem 12.2.14 — the run terminates at an
  `(ε, δ)`-approximate minimizer within `O((f(x₀) - f_low) / min_j ε_j^{π_j})` evaluations.
-/

open Set Metric Filter
open scoped Nat

namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p q : ℕ}

/-- The model data of ARqp at iteration `k` ([cartis2022evaluation], (12.2.23)): the Taylor
decrements of `f` at `x_k`, the model `m_k(s) = T_{f,p}(x_k, s) + σ_k ‖s‖^{p+1}/(p+1)!`, its
decrements, and the predicted decrease `ΔT_{f,p}(x_k, ·)`. -/
noncomputable abbrev arqpData (f : E → ℝ) (p : ℕ) (x : ℕ → E) (σ : ℕ → ℝ) (k : ℕ) :
    ARqpData E :=
  ARqpData.ofTaylor (ftaylorSeries ℝ f (x k)) p (σ k)

/-- The model `m_k` of (12.2.23). -/
noncomputable abbrev arqpModel (f : E → ℝ) (p : ℕ) (x : ℕ → E) (σ : ℕ → ℝ) (k : ℕ) : E → ℝ :=
  regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)

/-- The termination test of ARqp at iteration `k`: the Step-1 test, or the Step-2 test
`m_k(s_k) = m_k(0)`. -/
abbrev arqpStop (f : E → ℝ) (P : ARqpParams) (p q : ℕ) (ε : ℕ → ℝ) (x s : ℕ → E) (σ : ℕ → ℝ)
    (δ : ℕ → ℕ → ℝ) (d : ℕ → ℕ → E) (k : ℕ) : Prop :=
  IsARRun.Stop (arqpStop₁ P q ε (arqpData f p x σ) δ d) (arqpStop₂ (arqpData f p x σ) s) k

/-- The ratio (12.2.30) of ARqp. -/
noncomputable abbrev arqpRho (f : E → ℝ) (p : ℕ) (x s : ℕ → E) (σ : ℕ → ℝ) (k : ℕ) : ℝ :=
  arqpRatio f (arqpData f p x σ) x s k

/-- The radius constant `κ_δ(σ) = ς θ/(8 (3 L_f + σ))` of Lemma 12.2.9 ([cartis2022evaluation],
(12.2.45)); `κ_{δ,min} = κ_δ(σ_max)` ((12.2.51)). -/
noncomputable def arqpKappaDelta (P : ARqpParams) (Lf σ : ℝ) : ℝ :=
  P.ς * P.θ / (8 * (3 * Lf + σ))

theorem arqpKappaDelta_def (P : ARqpParams) (Lf σ : ℝ) :
    arqpKappaDelta P Lf σ = P.ς * P.θ / (8 * (3 * Lf + σ)) := rfl

theorem arqpKappaDelta_pos (P : ARqpParams) {Lf σ : ℝ} (hL : 0 ≤ Lf) (hσ : 0 < σ) :
    0 < arqpKappaDelta P Lf σ := by
  have := P.ς_pos; have := P.θ_pos
  unfold arqpKappaDelta; positivity

/-- `κ_δ(σ) < 1` for `L_f ≥ 1`, `σ ≥ 0`. -/
theorem arqpKappaDelta_lt_one (P : ARqpParams) {Lf σ : ℝ} (hL : 1 ≤ Lf) (hσ : 0 ≤ σ) :
    arqpKappaDelta P Lf σ < 1 := by
  have := P.ς_pos; have := P.θ_pos; have := P.ς_le_one; have := P.θ_lt_one
  unfold arqpKappaDelta
  rw [div_lt_one (by positivity)]
  nlinarith

/-- `κ_δ` is antitone in `σ`: `κ_{δ,min} = κ_δ(σ_max) ≤ κ_δ(σ_k)` for `σ_k ≤ σ_max`. -/
theorem arqpKappaDelta_anti (P : ARqpParams) {Lf σ σ' : ℝ} (hL : 1 ≤ Lf) (hσ : 0 ≤ σ)
    (hσσ' : σ ≤ σ') : arqpKappaDelta P Lf σ' ≤ arqpKappaDelta P Lf σ := by
  have := P.ς_pos; have := P.θ_pos
  have : 0 < 3 * Lf + σ := by linarith
  unfold arqpKappaDelta
  gcongr

/-- `τ_j = (ς - θ)/(j! (L_{f,p} + σ_max))`, the constant of Lemma 12.2.12
([cartis2022evaluation], (12.2.58)). -/
noncomputable def arqpTau (P : ARqpParams) (L : ℕ → ℝ) (p j : ℕ) : ℝ :=
  (P.ς - P.θ) / (j ! * (L p + arSigmaMax P.toARParams (L p)))

/-- The radius constant `κ̂ = min(κ_{δ,min}, τ_q/2)` of the step-length bound in the lower-bound
radii mode, with `κ_{δ,min} = κ_δ(σ_max)`. -/
noncomputable def arqpKappaHat (P : ARqpParams) (L : ℕ → ℝ) (p q : ℕ) : ℝ :=
  min (arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p))) (arqpTau P L p q / 2)

section Constants

variable (P : ARqpParams) (L : ℕ → ℝ)

theorem arqpTau_pos (hθς : P.θ < P.ς) (hL : 0 ≤ L p) (j : ℕ) : 0 < arqpTau P L p j := by
  have := arSigmaMax_pos P.toARParams (L p)
  unfold arqpTau
  have : 0 < P.ς - P.θ := sub_pos.2 hθς
  positivity

theorem arqpTau_le_one (hL : 1 ≤ L p) (j : ℕ) : arqpTau P L p j ≤ 1 := by
  have := arSigmaMax_pos P.toARParams (L p)
  have hj : (1 : ℝ) ≤ j ! := by exact_mod_cast Nat.one_le_iff_ne_zero.2 j.factorial_ne_zero
  have h1 : 1 ≤ (j ! : ℝ) * (L p + arSigmaMax P.toARParams (L p)) := by nlinarith
  unfold arqpTau
  rw [div_le_one (by linarith)]
  have := P.θ_pos; have := P.ς_le_one
  linarith

/-- `τ_j` is antitone in `j`: `τ_q ≤ τ_j` for `j ≤ q`. -/
theorem arqpTau_anti (hθς : P.θ < P.ς) (hL : 0 ≤ L p) {j q : ℕ} (hjq : j ≤ q) :
    arqpTau P L p q ≤ arqpTau P L p j := by
  have := arSigmaMax_pos P.toARParams (L p)
  have : 0 < P.ς - P.θ := sub_pos.2 hθς
  unfold arqpTau
  apply div_le_div_of_nonneg_left this.le (by positivity)
  gcongr

theorem arqpKappaHat_pos (hθς : P.θ < P.ς) (hL : 1 ≤ L p) (q : ℕ) :
    0 < arqpKappaHat P L p q :=
  lt_min (arqpKappaDelta_pos P (zero_le_one.trans le_finMax_left) (arSigmaMax_pos _ _))
    (half_pos (arqpTau_pos P L hθς (zero_le_one.trans hL) q))

theorem arqpKappaHat_le_one (q : ℕ) : arqpKappaHat P L p q ≤ 1 :=
  (min_le_left _ _).trans (arqpKappaDelta_lt_one P le_finMax_left
    (arSigmaMax_pos _ _).le).le

end Constants

/-- The exponents `π_j` of Lemma 12.2.13 ([cartis2022evaluation]) in radii mode `u`:
`(p+1)/(p-j+1)` for unit radii (`u`), `j(p+1)/p` under the lower bound (12.2.51) at every
order (`¬ u`). -/
noncomputable def arqpPiOf (u : Prop) [Decidable u] (p j : ℕ) : ℝ :=
  if u then ((p + 1 : ℕ) : ℝ) / ((p - j + 1 : ℕ) : ℝ) else (j : ℝ) * (p + 1) / p

/-- The constant `κ_{Δm}` of Lemma 12.2.13 ([cartis2022evaluation]) in radii mode `u`:
`σ_min/(p+1)! (τ_q/2)^{(p+1)/(p-q+1)}` for unit radii (`u`), and
`σ_min/(p+1)! ((τ_q/2) κ̂^{q-1})^{q(p+1)/p}` under (12.2.51) (`¬ u`). -/
noncomputable def arqpKappaDmOf (u : Prop) [Decidable u] (P : ARqpParams) (L : ℕ → ℝ)
    (p q : ℕ) : ℝ :=
  if u then
    P.σmin / ((p + 1)! : ℝ) * (arqpTau P L p q / 2) ^ (((p + 1 : ℕ) : ℝ) / ((p - q + 1 : ℕ) : ℝ))
  else
    P.σmin / ((p + 1)! : ℝ) * (arqpTau P L p q / 2 * arqpKappaHat P L p q ^ (q - 1)) ^
      ((q : ℝ) * (p + 1) / p)

theorem arqpPiOf_of_pos {u : Prop} [Decidable u] (hu : u) (p j : ℕ) :
    arqpPiOf u p j = ((p + 1 : ℕ) : ℝ) / ((p - j + 1 : ℕ) : ℝ) := by
  rw [arqpPiOf, ite_eq_left hu]

theorem arqpPiOf_of_neg {u : Prop} [Decidable u] (hu : ¬ u) (p j : ℕ) :
    arqpPiOf u p j = (j : ℝ) * (p + 1) / p := by
  rw [arqpPiOf, ite_eq_right hu]

/-- The first ARqp-SC exponent is `π_1 = (p+1)/p` in both radii modes. -/
theorem arqpPiOf_one (u : Prop) [Decidable u] {p : ℕ} (hp : 1 ≤ p) :
    arqpPiOf u p 1 = ((p : ℝ) + 1) / p := by
  by_cases hu : u
  · rw [arqpPiOf_of_pos hu, Nat.sub_add_cancel hp]; push_cast; ring
  · rw [arqpPiOf_of_neg hu]; ring

/-- The ARqp-SC exponent of order `1` ((14.2.12), either radii mode) is `(p+1)/p ≤ 3/2` for
`p ≥ 2`, so the order part of `theorem_14_3_9_false` applies to it. -/
theorem arqpPiOf_one_le (unit : Prop) [Decidable unit] {p : ℕ} (hp : 2 ≤ p) :
    arqpPiOf unit p 1 ≤ 3 / 2 := by
  rw [arqpPiOf_one unit (by omega)]
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- The ARqp-SC exponent of order `1` ((14.2.12), either radii mode) is `(p+1)/p ≥ 4/3` for
`1 ≤ p ≤ 3`; with `arqpPiOf_one_le` it lies in `[4/3, 3/2]` for `p ∈ {2, 3}`. -/
theorem four_thirds_le_arqpPiOf_one (unit : Prop) [Decidable unit] {p : ℕ} (hp1 : 1 ≤ p)
    (hp : p ≤ 3) : 4 / 3 ≤ arqpPiOf unit p 1 := by
  rw [arqpPiOf_one unit hp1]
  have h3 : (p : ℝ) ≤ 3 := by exact_mod_cast hp
  have h1 : (1 : ℝ) ≤ p := by exact_mod_cast hp1
  rw [le_div_iff₀ (by linarith)]
  linarith

theorem arqpPiOf_nonneg (u : Prop) [Decidable u] (p j : ℕ) : 0 ≤ arqpPiOf u p j := by
  unfold arqpPiOf
  split_ifs <;> positivity

theorem arqpKappaDmOf_of_pos {u : Prop} [Decidable u] (hu : u) (P : ARqpParams) (L : ℕ → ℝ)
    (p q : ℕ) : arqpKappaDmOf u P L p q = P.σmin / ((p + 1)! : ℝ) *
      (arqpTau P L p q / 2) ^ (((p + 1 : ℕ) : ℝ) / ((p - q + 1 : ℕ) : ℝ)) := by
  rw [arqpKappaDmOf, ite_eq_left hu]

theorem arqpKappaDmOf_of_neg {u : Prop} [Decidable u] (hu : ¬ u) (P : ARqpParams) (L : ℕ → ℝ)
    (p q : ℕ) : arqpKappaDmOf u P L p q = P.σmin / ((p + 1)! : ℝ) *
      (arqpTau P L p q / 2 * arqpKappaHat P L p q ^ (q - 1)) ^ ((q : ℝ) * (p + 1) / p) := by
  rw [arqpKappaDmOf, ite_eq_right hu]

theorem arqpKappaDmOf_nonneg {P : ARqpParams} {L : ℕ → ℝ} {p q : ℕ} (u : Prop) [Decidable u]
    (hθς : P.θ < P.ς) (hL : 1 ≤ L p) : 0 ≤ arqpKappaDmOf u P L p q := by
  have := P.σmin_nonneg
  have hτ := arqpTau_pos P L hθς (zero_le_one.trans hL) q
  have hκ := arqpKappaHat_pos P L hθς hL q
  unfold arqpKappaDmOf
  split_ifs <;> positivity

/-- The constant `κ^s = 1/(η₁ κ_{Δm})` of Theorem 12.2.14 in radii mode `u`
(`κ_{Δm} = arqpKappaDmOf u`; `kappaSARqp` is the mode `u = (q ≤ 2)`). -/
noncomputable def kappaSARqpOf (u : Prop) [Decidable u] (P : ARqpParams) (L : ℕ → ℝ)
    (p q : ℕ) : ℝ :=
  1 / (P.η₁ * arqpKappaDmOf u P L p q)

/-- The constant `κ^a = κ^s (1 + |log γ₁|/log γ₂)` of Theorem 12.2.14 in radii mode `u`
(`kappaAARqp` is the mode `u = (q ≤ 2)`). -/
noncomputable def kappaAARqpOf (u : Prop) [Decidable u] (P : ARqpParams) (L : ℕ → ℝ)
    (p q : ℕ) : ℝ :=
  kappaSARqpOf u P L p q * (1 + |Real.log P.γ₁| / Real.log P.γ₂)

/-- The constant `κ^c_{ARqp} = (|log γ₁| + log(σ_max/σ₀))/log γ₂ + 2` of Theorem 12.2.14. -/
noncomputable def kappaCARqp (P : ARqpParams) (L : ℕ → ℝ) (p : ℕ) : ℝ :=
  (|Real.log P.γ₁| + Real.log (arSigmaMax P.toARParams (L p) / P.σ₀)) / Real.log P.γ₂ + 2

theorem kappaAARqpOf_def (u : Prop) [Decidable u] (P : ARqpParams) (L : ℕ → ℝ) (p q : ℕ) :
    kappaAARqpOf u P L p q = kappaSARqpOf u P L p q * (1 + |Real.log P.γ₁| / Real.log P.γ₂) := rfl

theorem kappaCARqp_def (P : ARqpParams) (L : ℕ → ℝ) (p : ℕ) :
    kappaCARqp P L p =
      (|Real.log P.γ₁| + Real.log (arSigmaMax P.toARParams (L p) / P.σ₀)) / Real.log P.γ₂ + 2 :=
  rfl

theorem arqpKappaDmOf_pos {P : ARqpParams} {L : ℕ → ℝ} {p q : ℕ} (u : Prop) [Decidable u]
    (hσmin : 0 < P.σmin) (hθς : P.θ < P.ς) (hL : 1 ≤ L p) : 0 < arqpKappaDmOf u P L p q := by
  have hτ := arqpTau_pos P L hθς (zero_le_one.trans hL) q
  have hκ := arqpKappaHat_pos P L hθς hL q
  unfold arqpKappaDmOf
  split_ifs <;> positivity

theorem kappaSARqpOf_pos {P : ARqpParams} {L : ℕ → ℝ} {p q : ℕ} (u : Prop) [Decidable u]
    (hσmin : 0 < P.σmin) (hθς : P.θ < P.ς) (hL : 1 ≤ L p) : 0 < kappaSARqpOf u P L p q := by
  have := arqpKappaDmOf_pos (q := q) u hσmin hθς hL
  have := P.η₁_pos
  unfold kappaSARqpOf; positivity

variable {f : E → ℝ} {L : ℕ → ℝ} {P : ARqpParams} {ε δ₀ : ℕ → ℝ} {x s : ℕ → E}
  {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → E} {X C A : Set E}

/-- At a successful iteration before termination, `x_{k+1} = x_k + s_k` and
`δ_{k+1} = δ_{s_k}`. -/
theorem IsARqpRun.succ_eq (h : IsARqpRun f X P q ε δ₀ (arqpData f p x σ) x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) (hs : P.η₁ ≤ arqpRho f p x s σ k) :
    x (k + 1) = x k + s k ∧ δ (k + 1) = δs k :=
  ⟨h.toIsARRun.eq_add_of_succ hk hs, (h.radii k hk).1 hs⟩

/-- Before termination, the step is nonzero and `ΔT_{f,p}(x_k, s_k) > σ_k/(p+1)! ‖s_k‖^{p+1}`
(Lemma 4.1.1). -/
theorem IsARqpRun.taylorDecrement_gt (h : IsARqpRun f X P q ε δ₀ (arqpData f p x σ) x s σ δ δs d dm)
    {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) :
    s k ≠ 0 ∧ σ k / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) <
      (ftaylorSeries ℝ f (x k)).taylorDecrement p (s k) := by
  have hm := h.model_lt hk
  exact ⟨ne_zero_of_regularizedModel_lt hm, lt_taylorDecrement_of_regularizedModel_lt hm⟩

/-- The decreases `f(x_k) - f(x_{k+1})` are nonnegative before termination. -/
theorem IsARqpRun.objective_le
    (h : IsARqpRun f X P q ε δ₀ (arqpData f p x σ) x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) : f (x (k + 1)) ≤ f (x k) := by
  have hσ := h.toIsARRun.sigma_pos (K := k) (fun i hi => hk i hi.le) k le_rfl
  have hdec := (IsARqpRun.taylorDecrement_gt h hk).2
  exact (h.toIsARRun.accept k hk).le (w := f) rfl (lt_of_le_of_lt (by positivity) hdec)

/-- The iterates of a feasible ARqp run stay in the sublevel set `{y ∈ X | f(y) ≤ f(x₀)}` up to
termination. -/
theorem IsARqpRun.mem_sublevel (h : IsARqpRun f X P q ε δ₀ (arqpData f p x σ) x s σ δ δs d dm) :
    ∀ k, (∀ i < k, ¬ arqpStop f P p q ε x s σ δ d i) → x k ∈ X ∧ f (x k) ≤ f (x 0) := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨h.mem_zero, le_rfl⟩
  | succ k ih =>
    intro hk
    exact ⟨h.mem (k + 1) hk,
      (IsARqpRun.objective_le h fun i hi => hk i (Nat.lt_succ_of_le hi)).trans
      (ih fun i hi => hk i (Nat.lt_succ_of_lt hi)).2⟩

/-- **The regularization weights stay bounded** ([cartis2022evaluation], Lemma 4.1.2 for ARqp,
(4.1.19)): if `X ⊆ C` and `∇^p f` is `L_p`-Lipschitz anchored at the points of a set `A`
containing `{y ∈ X | f(y) ≤ f(x₀)}`, then up to (and including) termination of an ARqp run with
exact data on `X`, `σ_min ≤ σ_k ≤ σ_max = max(σ₀, γ₃ L_p/(1 - η₂))`. -/
theorem IsARqpRun.sigma_le_of_anchored (hf : LipschitzDerivsAnchored f C A p p L) (hXC : X ⊆ C)
    (hA : ∀ y ∈ X, f y ≤ f (x 0) → y ∈ A)
    (h : IsARqpRun f X P q ε δ₀ (arqpData f p x σ) x s σ δ δs d dm) :
    ∀ k, (∀ i < k, ¬ arqpStop f P p q ε x s σ δ d i) →
      P.σmin ≤ σ k ∧ σ k ≤ arSigmaMax P.toARParams (L p) := by
  intro k hk
  have := IsARRun.sigma_le_anchored (f := f) (p := p) (x := x) (s := s) h.toIsARRun (C := C)
    hf.convex hf.contDiffAt (fun k hk => by
      obtain ⟨hxk, hfk⟩ := IsARqpRun.mem_sublevel h k fun i hi => hk i hi.le
      exact hf.lipschitzAt (Finset.mem_Icc.2 ⟨le_rfl, le_rfl⟩) (hA _ hxk hfk))
    (hXC h.mem_zero) (fun k hk hst => ⟨hXC hst.mem, h.model_lt hk⟩) k hk
  exact ⟨this.2.1, this.2.2⟩

/-- **Runs with the radii property (12.2.50)** ([cartis2022evaluation], Lemmas 12.2.9 and
12.2.10). In finite dimension, let `1 ≤ q ≤ p`, `ε ∈ (0, 1]^q`, `δ₀ ∈ (0, 1]^q`, and let the jets
of `f` be bounded by `L_f = finMax 1 L p` at the points of a set `A` containing
`{y | f(y) ≤ f(x₀)}`. From `x₀` there is an unconstrained ARqp run with exact data whose Step-2
radii are `1` at the orders `j ≤ 2` (12.2.44) and satisfy `δs_{k,j} ≥ κ_δ(σ_k) ε_j` at every order
before termination ((12.2.45), (12.2.50)): the radii of Lemma 12.2.9 are computed from the jet at
the iterate, which lies in `A`. -/
theorem exists_isARqpRun_of_anchored [FiniteDimensional ℝ E]
    (hjet : ∀ j ∈ Finset.Icc 2 p, ∀ x ∈ A, ‖iteratedFDeriv ℝ j f x‖ ≤ finMax 1 L p) (P : ARqpParams)
      (hq : 1 ≤ q) (hqp : q ≤ p)
    {ε δ₀ : ℕ → ℝ} (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1)
    (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1) (x₀ : E) (hA : ∀ y, f y ≤ f x₀ → y ∈ A) :
    ∃ (x s : ℕ → E) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → E), x 0 = x₀ ∧
      IsARqpRun f univ P q ε δ₀ (arqpData f p x σ) x s σ δ δs d dm ∧
      (∀ k, (∀ i < k, ¬ arqpStop f P p q ε x s σ δ d i) →
        ∀ j ∈ Finset.Icc 1 q, j ≤ 2 → δs k j = 1) ∧
      ∀ k, (∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) →
        ∀ j ∈ Finset.Icc 1 q, arqpKappaDelta P (finMax 1 L p) (σ k) * ε j ≤ δs k j := by
  classical
  have hp : 1 ≤ p := hq.trans hqp
  have hL1 : 1 ≤ finMax 1 L p := one_le_finMax
  -- the jet bound `L_f` at the anchors, and any bound elsewhere
  let M : E → ℝ := fun y => if y ∈ A then finMax 1 L p else
    max (finMax 1 L p) (∑ i ∈ Finset.Icc 2 p, ‖iteratedFDeriv ℝ i f y‖)
  have hM0 : ∀ y, 0 ≤ M y := fun y => by
    simp only [M]
    split_ifs
    · linarith
    · exact le_max_of_le_left (by linarith)
  have hM : ∀ y, ∀ i ∈ Finset.Icc 2 p, ‖iteratedFDeriv ℝ i f y‖ ≤ M y := fun y i hi => by
    simp only [M]
    split_ifs with hy
    · exact hjet _ hi _ hy
    · exact le_max_of_le_right (Finset.single_le_sum
        (f := fun i => ‖iteratedFDeriv ℝ i f y‖) (fun _ _ => norm_nonneg _) hi)
  obtain ⟨x, s, σ, δ, δs, d, dm, h0, h, hrad⟩ := exists_isARqpRun f P hp hqp
    (fun j hj => (hε j hj).1) hδ₀ M hM0 hM x₀
  refine ⟨x, s, σ, δ, δs, d, dm, h0, h, fun k hk => (hrad k hk).1, fun k hk j hj => ?_⟩
  have hk' : ∀ i < k, ¬ arqpStop f P p q ε x s σ δ d i := fun i hi => hk i hi.le
  have hσ : 0 < σ k := h.toIsARRun.sigma_pos hk' k le_rfl
  have hxA : x k ∈ A := by
    have := (IsARqpRun.mem_sublevel (X := univ) h k hk').2
    rw [h0] at this
    exact hA _ this
  have hMk : M (x k) = finMax 1 L p := ite_eq_left hxA
  obtain ⟨hεj, hεj1⟩ := hε j hj
  have hκ1 := (arqpKappaDelta_lt_one P hL1 hσ.le).le
  by_cases hj2 : j ≤ 2
  · rw [(hrad k hk').1 j hj hj2]
    calc arqpKappaDelta P (finMax 1 L p) (σ k) * ε j ≤ 1 * 1 :=
          mul_le_mul hκ1 hεj1 hεj.le zero_le_one
      _ = 1 := one_mul 1
  · rw [(hrad k hk').2 j (Finset.mem_Icc.2 ⟨by omega, (Finset.mem_Icc.1 hj).2⟩), hMk]
    have hK : 0 < 3 * finMax 1 L p + σ k := by linarith
    have := P.ς_pos; have := P.θ_pos
    refine le_min ?_ ?_
    · calc arqpKappaDelta P (finMax 1 L p) (σ k) * ε j ≤ 1 * 1 :=
            mul_le_mul hκ1 hεj1 hεj.le zero_le_one
        _ = 1 := one_mul 1
    · rw [arqpKappaDelta]
      calc P.ς * P.θ / (8 * (3 * finMax 1 L p + σ k)) * ε j =
          P.ς * P.θ * ε j / (8 * (3 * finMax 1 L p + σ k)) := by ring
        _ ≤ P.ς * P.θ * ε j / (4 * (3 * finMax 1 L p + σ k)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)

/-- **The radius inequality for one iteration** ([cartis2022evaluation], Lemma 12.2.11, local
form). Let `∇^p f` be `L_p`-Lipschitz anchored at `y ∈ A` with respect to `C ⊇ X`, `L_p ≥ 1`.
If the step `t` from `y` satisfies the Step-2 conditions of ARqp with weight `0 ≤ σ_k ≤ σ_max`, is
short (`‖t‖ < 1`, so that (12.2.29) holds), and the Step-1 test at `y + t` with the radii `δ_k`
and displacements `d'` fails, then for some `j ∈ [1:q]`
`(ς - θ) ε_j δ_{k,j}^j/j! < (L_p + σ_max) ∑_{ℓ=1}^j δ_{k,j}^ℓ/ℓ! ‖t‖^{p-ℓ+1}` (12.2.52). -/
theorem ARqpStep.exists_radius_ineq (hf : LipschitzDerivsAnchored f C A p p L)
    (hL : 1 ≤ L p) (hXC : X ⊆ C)
    (hq : 1 ≤ q)
    (hqp : q ≤ p) {y t : E} (hy : y ∈ A)
    {σk : ℝ} (hσ0 : 0 ≤ σk) (hσmax : σk ≤ arSigmaMax P.toARParams (L p)) {δk : ℕ → ℝ}
    {dmk : ℕ → E}
    (hstep : ARqpStep X P q ε (ARqpData.ofTaylor (ftaylorSeries ℝ f y) p σk) y t δk dmk)
    (hshort : ‖t‖ < 1) {d' : ℕ → E}
    (hw : ∀ j ∈ Finset.Icc 1 q, IsApproxMeasureStep
      ((ftaylorSeries ℝ f (y + t)).taylorDecrement j) (δk j) {e | y + t + e ∈ X} P.ς (d' j))
    (hfail : ¬ MeasureTestPasses (fun j => (ftaylorSeries ℝ f (y + t)).taylorDecrement j) q P.ς
      ε δk d') :
    ∃ j ∈ Finset.Icc 1 q, (P.ς - P.θ) * ε j * δk j ^ j / j ! <
      (L p + arSigmaMax P.toARParams (L p)) *
        ∑ ℓ ∈ Finset.Icc 1 j, δk j ^ ℓ / ℓ ! * ‖t‖ ^ (p - ℓ + 1) := by
  have hp : 1 ≤ p := hq.trans hqp
  obtain ⟨j, hj, hlt, -⟩ := exists_lt_of_not_measureTestPasses hfail
  have hjp : j ≤ p := (Finset.mem_Icc.1 hj).2.trans hqp
  have hδ0 : 0 ≤ δk j := (norm_nonneg _).trans (hw j hj).norm_le
  have h₁ : P.ς * ε j * δk j ^ j / (j ! : ℝ) - 0 <
      taylorMeasure (ftaylorSeries ℝ f (y + t)) j (δk j) {e | y + t + e ∈ X} := by
    rw [sub_zero]
    exact hlt.trans_le (taylorDecrement_le_taylorMeasure _ j (hw j hj).1)
  obtain ⟨hdm, hsmall⟩ := (hstep.branch.resolve_left (not_le.2 hshort)) j hj
  have h₂ : taylorMeasure (ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ f y) p σk) t) j
      (δk j) {e | y + t + e ∈ X} ≤ P.θ * ε j * δk j ^ j / j ! := by
    have h2 := hdm.2.trans hsmall
    have : P.ς * P.θ * ε j * δk j ^ j / j ! = P.ς * (P.θ * ε j * δk j ^ j / j !) := by ring
    rw [this] at h2
    exact le_of_mul_le_mul_left h2 P.ς_pos
  have hS0 : (0 : E) ∈ {e | y + t + e ∈ X} := by
    change y + t + 0 ∈ X; rw [add_zero]; exact hstep.mem
  have := radius_inequality_of_measure_gt_anchored hf.convex hf.contDiffAt
    (hf.lipschitzAt (Finset.mem_Icc.2 ⟨le_rfl, le_rfl⟩) hy) (zero_le_one.trans hL) (hf.subset hy)
      (hXC hstep.mem)
    (jetApprox_self (ftaylorSeries ℝ f y) p) le_rfl le_rfl
    (fun i _ => by simp) hσ0 hσmax hjp hS0 hδ0 h₁ h₂
  refine ⟨j, hj, this.trans_eq ?_⟩
  ring

/-- The successor data of a successful ARqp iteration `k` before termination, in the form used
by the local lemmas: the Step-1 witnesses at `x_{k+1} = x_k + s_k` with radii `δs_k`. -/
theorem IsARqpRun.next_witness
    (h : IsARqpRun f X P q ε δ₀ (arqpData f p x σ) x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) (hs : P.η₁ ≤ arqpRho f p x s σ k) :
    ∀ j ∈ Finset.Icc 1 q, IsApproxMeasureStep
      ((ftaylorSeries ℝ f (x k + s k)).taylorDecrement j) (δs k j) {e | x k + s k + e ∈ X} P.ς
        (d (k + 1) j) := by
  obtain ⟨hx1, hδ1⟩ := IsARqpRun.succ_eq h hk hs
  intro j hj
  have hw := h.witness (k + 1) (fun i hi => hk i (by omega)) j hj
  change IsApproxMeasureStep ((ftaylorSeries ℝ f (x (k + 1))).taylorDecrement j) (δ (k + 1) j)
    {e | x (k + 1) + e ∈ X} P.ς (d (k + 1) j) at hw
  rwa [hx1, hδ1] at hw

/-- The failed Step-1 test at `k + 1` after a successful iteration, in local form. -/
theorem IsARqpRun.next_not_measureTestPasses
    (h : IsARqpRun f X P q ε δ₀ (arqpData f p x σ) x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) (hs : P.η₁ ≤ arqpRho f p x s σ k)
    (hk1 : ¬ arqpStop₁ P q ε (arqpData f p x σ) δ d (k + 1)) :
    ¬ MeasureTestPasses (fun j => (ftaylorSeries ℝ f (x k + s k)).taylorDecrement j) q P.ς ε
      (δs k) (d (k + 1)) := by
  obtain ⟨hx1, hδ1⟩ := IsARqpRun.succ_eq h hk hs
  change ¬ MeasureTestPasses (fun j => (ftaylorSeries ℝ f (x (k + 1))).taylorDecrement j) q P.ς
    ε (δ (k + 1)) (d (k + 1)) at hk1
  rwa [hx1, hδ1] at hk1

/-- **The step is long** ([cartis2022evaluation], Lemma 12.2.12, local form; the common core of
Lemmas 12.2.12 and 12.2.13). Under the hypotheses of `ARqpStep.exists_radius_ineq`
with `θ < ς`, `ε ∈ (0, 1]^q`, a decreasing step and the radii in mode `u` (unit radii if `u`; a
long step or the lower bound (12.2.51) if `¬ u`), for some `j ∈ [1:q]`:
`τ_j ε_j/2 ≤ ‖t‖^{p-j+1}` if `u`, and `τ_j/2 κ̂^{j-1} ε_j^j ≤ ‖t‖^p` if `¬ u`. -/
theorem ARqpStep.exists_norm_pow_ge (hf : LipschitzDerivsAnchored f C A p p L)
    (hL : 1 ≤ L p) (hXC : X ⊆ C)
    (hq : 1 ≤ q)
    (hqp : q ≤ p) (hθς : P.θ < P.ς) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) {y t : E}
    (hy : y ∈ A) {σk : ℝ}
    (hσ0 : 0 ≤ σk) (hσmax : σk ≤ arSigmaMax P.toARParams (L p)) {δk : ℕ → ℝ} {dmk : ℕ → E}
    (hstep : ARqpStep X P q ε (ARqpData.ofTaylor (ftaylorSeries ℝ f y) p σk) y t δk dmk)
    (hlt : regularizedModel (ftaylorSeries ℝ f y) p σk t <
      regularizedModel (ftaylorSeries ℝ f y) p σk 0) {d' : ℕ → E}
    (hw : ∀ j ∈ Finset.Icc 1 q, IsApproxMeasureStep
      ((ftaylorSeries ℝ f (y + t)).taylorDecrement j) (δk j) {e | y + t + e ∈ X} P.ς (d' j))
    (hfail : ¬ MeasureTestPasses (fun j => (ftaylorSeries ℝ f (y + t)).taylorDecrement j) q P.ς
      ε δk d')
    {u : Prop} (hrad : (u → ∀ j ∈ Finset.Icc 1 q, δk j = 1) ∧
      (¬ u → 1 ≤ ‖t‖ ∨ ∀ j ∈ Finset.Icc 1 q,
        arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)) * ε j ≤ δk j)) :
    ∃ j ∈ Finset.Icc 1 q,
      (u → arqpTau P L p j * ε j / 2 ≤ ‖t‖ ^ (p - j + 1)) ∧
      (¬ u → arqpTau P L p j / 2 * arqpKappaHat P L p q ^ (j - 1) * ε j ^ j ≤ ‖t‖ ^ p) := by
  have hp : 1 ≤ p := hq.trans hqp
  have hLp : 1 ≤ L p := hL
  have ht : 0 < ‖t‖ := norm_pos_iff.2 (ne_zero_of_regularizedModel_lt hlt)
  set A := L p + arSigmaMax P.toARParams (L p) with hA_def
  have hA : 0 < A := by have := arSigmaMax_pos P.toARParams (L p); linarith
  have hκ := arqpKappaHat_pos P L hθς hLp q
  have hκ1 := arqpKappaHat_le_one P L (p := p) q
  -- the trivial long-step case
  by_cases hlong : 1 ≤ ‖t‖
  · have h1 : 1 ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, hq⟩
    obtain ⟨hε0, hε1⟩ := hε 1 h1
    have hτ1 := arqpTau_le_one P L hLp 1
    have hτ0 := (arqpTau_pos P L hθς (zero_le_one.trans hLp) 1).le
    refine ⟨1, h1, fun _ => ?_, fun _ => ?_⟩
    · calc arqpTau P L p 1 * ε 1 / 2 ≤ 1 * 1 / 2 := by gcongr
        _ ≤ 1 := by norm_num
        _ ≤ ‖t‖ ^ (p - 1 + 1) := one_le_pow₀ hlong
    · calc arqpTau P L p 1 / 2 * arqpKappaHat P L p q ^ (1 - 1) * ε 1 ^ 1 ≤ 1 / 2 * 1 * 1 := by
            rw [Nat.sub_self, pow_zero, pow_one]; gcongr
        _ ≤ 1 := by norm_num
        _ ≤ ‖t‖ ^ p := one_le_pow₀ hlong
  have hshort : ‖t‖ < 1 := not_le.1 hlong
  obtain ⟨j, hj, hineq⟩ := ARqpStep.exists_radius_ineq hf hL hXC hq hqp hy hσ0
    hσmax hstep hshort hw
    hfail
  have hjp : j ≤ p := (Finset.mem_Icc.1 hj).2.trans hqp
  have hj1 : 1 ≤ j := (Finset.mem_Icc.1 hj).1
  obtain ⟨hε0, hε1⟩ := hε j hj
  have hMI : MeasureIneq A 0 (P.ς - P.θ) (ε j) (δk j) ‖t‖ j p := by
    rw [measureIneq_iff, zero_mul, add_zero]; exact hineq.le
  have ha : 0 < P.ς - P.θ := sub_pos.2 hθς
  have hfac : (0 : ℝ) < j ! := by exact_mod_cast j.factorial_pos
  have hτ : arqpTau P L p j = (P.ς - P.θ) / (A * j !) := by
    rw [arqpTau, hA_def, mul_comm]
  refine ⟨j, hj, fun hq2 => ?_, fun hq2 => ?_⟩
  · -- `δ_{k+1,j} = 1 ≥ ‖s_k‖`
    have hδ1 : δk j = 1 := hrad.1 hq2 j hj
    have h1 := hMI.div_le_of_le hA.le le_rfl ht (by rw [hδ1]; exact hshort.le) hjp
    rw [hτ]
    have e : (P.ς - P.θ) / (A * j !) * ε j / 2 = (P.ς - P.θ) * ε j / j ! / (2 * A) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    linarith
  · have hrad' := (hrad.2 hq2).resolve_left hlong j hj
    have hκδ : 0 < arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)) :=
      arqpKappaDelta_pos P (zero_le_one.trans le_finMax_left) (arSigmaMax_pos _ _)
    have hδpos : 0 < δk j := lt_of_lt_of_le (by positivity) hrad'
    have h1 := pow_ge_of_measure_ineq hMI hA ha hε0 ht hshort.le hδpos hj1 hjp hκδ hrad'
    rw [← hτ] at h1
    refine le_trans ?_ h1
    have hmin : arqpKappaHat P L p q ≤ min (arqpKappaDelta P (finMax 1 L p)
        (arSigmaMax P.toARParams (L p))) (arqpTau P L p j / 2) :=
      min_le_min le_rfl (by
        have := arqpTau_anti P L hθς (zero_le_one.trans hLp) (Finset.mem_Icc.1 hj).2
        linarith)
    have hτj := arqpTau_pos P L hθς (zero_le_one.trans hLp) j
    gcongr

/-- **The model decrease for one iteration** ([cartis2022evaluation], Lemma 12.2.13, local
form): under the hypotheses of `ARqpStep.exists_norm_pow_ge` with `σ_min ≤ σ_k`,
`ΔT_{f,p}(y, t) ≥ κ_{Δm} min_j ε_j^{π_j}` with `κ_{Δm} = arqpKappaDmOf u` and
`π_j = arqpPiOf u p j`. -/
theorem ARqpStep.taylorDecrement_ge (hf : LipschitzDerivsAnchored f C A p p L)
    (hL : 1 ≤ L p) (hXC : X ⊆ C)
    (hq : 1 ≤ q)
    (hqp : q ≤ p) (hθς : P.θ < P.ς) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) {y t : E}
    (hy : y ∈ A) {σk : ℝ}
    (hσmin : P.σmin ≤ σk) (hσmax : σk ≤ arSigmaMax P.toARParams (L p)) {δk : ℕ → ℝ}
    {dmk : ℕ → E}
    (hstep : ARqpStep X P q ε (ARqpData.ofTaylor (ftaylorSeries ℝ f y) p σk) y t δk dmk)
    (hlt : regularizedModel (ftaylorSeries ℝ f y) p σk t <
      regularizedModel (ftaylorSeries ℝ f y) p σk 0) {d' : ℕ → E}
    (hw : ∀ j ∈ Finset.Icc 1 q, IsApproxMeasureStep
      ((ftaylorSeries ℝ f (y + t)).taylorDecrement j) (δk j) {e | y + t + e ∈ X} P.ς (d' j))
    (hfail : ¬ MeasureTestPasses (fun j => (ftaylorSeries ℝ f (y + t)).taylorDecrement j) q P.ς
      ε δk d')
    {u : Prop} [Decidable u] (hrad : (u → ∀ j ∈ Finset.Icc 1 q, δk j = 1) ∧
      (¬ u → 1 ≤ ‖t‖ ∨ ∀ j ∈ Finset.Icc 1 q,
        arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)) * ε j ≤ δk j)) :
    arqpKappaDmOf u P L p q * finMin 1 (fun j => ε j ^ arqpPiOf u p j) q ≤
      (ftaylorSeries ℝ f y).taylorDecrement p t := by
  have hσ0 : 0 ≤ σk := P.σmin_nonneg.trans hσmin
  have hp : 1 ≤ p := hq.trans hqp
  have hLp : 1 ≤ L p := hL
  have hT := lt_taylorDecrement_of_regularizedModel_lt hlt
  have ht : 0 < ‖t‖ := norm_pos_iff.2 (ne_zero_of_regularizedModel_lt hlt)
  set m := finMin 1 (fun j => ε j ^ arqpPiOf u p j) q with hm_def
  have hm0 : 0 < m := finMin_pos one_pos fun j hj => Real.rpow_pos_of_pos (hε j hj).1 _
  have hfacp : (0 : ℝ) < (p + 1)! := by positivity
  have hσmin0 := P.σmin_nonneg
  -- the decrease at the step
  have hlow : P.σmin / ((p + 1)! : ℝ) * ‖t‖ ^ (p + 1) ≤
      (ftaylorSeries ℝ f y).taylorDecrement p t := by
    refine le_trans ?_ hT.le
    gcongr
  have hκq := arqpKappaHat_pos P L hθς hLp q
  have hκq1 := arqpKappaHat_le_one P L (p := p) q
  have hτq := arqpTau_pos P L hθς (zero_le_one.trans hLp) q
  have hτq1 := arqpTau_le_one P L hLp q
  obtain ⟨j, hj, h1, h2⟩ :=
    ARqpStep.exists_norm_pow_ge hf hL hXC hq hqp hθς hε hy hσ0 hσmax hstep hlt
      hw hfail hrad
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  have hjp : j ≤ p := hjq.trans hqp
  obtain ⟨hε0, hε1⟩ := hε j hj
  have hτj := arqpTau_pos P L hθς (zero_le_one.trans hLp) j
  have hτqj := arqpTau_anti P L hθς (zero_le_one.trans hLp) hjq
  have hmj : m ≤ ε j ^ arqpPiOf u p j := finMin_le hj
  -- the key bound `B m ≤ ‖s_k‖^{p+1}`, with `κ_{Δm} = σ_min/(p+1)! B`
  have key : ∃ B, arqpKappaDmOf u P L p q = P.σmin / ((p + 1)! : ℝ) * B ∧
      B * m ≤ ‖t‖ ^ (p + 1) := by
    by_cases hq2 : u
    · refine ⟨(arqpTau P L p q / 2) ^ (((p + 1 : ℕ) : ℝ) / ((p - q + 1 : ℕ) : ℝ)),
        arqpKappaDmOf_of_pos hq2 P L p q, ?_⟩
      have hπ : arqpPiOf u p j = ((p + 1 : ℕ) : ℝ) / ((p - j + 1 : ℕ) : ℝ) :=
        arqpPiOf_of_pos hq2 p j
      rw [hπ] at hmj
      have hexp : ((p + 1 : ℕ) : ℝ) / ((p - j + 1 : ℕ) : ℝ) ≤
          ((p + 1 : ℕ) : ℝ) / ((p - q + 1 : ℕ) : ℝ) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact_mod_cast (show p - q + 1 ≤ p - j + 1 by omega)
      have hB : (arqpTau P L p q / 2) ^ (((p + 1 : ℕ) : ℝ) / ((p - q + 1 : ℕ) : ℝ)) ≤
          (arqpTau P L p j / 2) ^ (((p + 1 : ℕ) : ℝ) / ((p - j + 1 : ℕ) : ℝ)) :=
        (Real.rpow_le_rpow_of_exponent_ge (by positivity) (by linarith) hexp).trans
          (Real.rpow_le_rpow (by positivity) (by linarith) (by positivity))
      calc (arqpTau P L p q / 2) ^ (((p + 1 : ℕ) : ℝ) / ((p - q + 1 : ℕ) : ℝ)) * m
          ≤ (arqpTau P L p j / 2) ^ (((p + 1 : ℕ) : ℝ) / ((p - j + 1 : ℕ) : ℝ)) *
              ε j ^ (((p + 1 : ℕ) : ℝ) / ((p - j + 1 : ℕ) : ℝ)) :=
            mul_le_mul hB hmj hm0.le (by positivity)
        _ = (arqpTau P L p j * ε j / 2) ^ (((p + 1 : ℕ) : ℝ) / ((p - j + 1 : ℕ) : ℝ)) := by
            rw [← Real.mul_rpow (by positivity) hε0.le]; ring_nf
        _ ≤ (‖t‖ ^ (p - j + 1)) ^ (((p + 1 : ℕ) : ℝ) / ((p - j + 1 : ℕ) : ℝ)) :=
            Real.rpow_le_rpow (by positivity) (h1 hq2) (by positivity)
        _ = ‖t‖ ^ (p + 1) := by rw [pow_rpow_div (by omega) ht.le, Real.rpow_natCast]
    · have hq2' : ¬ u := hq2
      set bq := arqpTau P L p q / 2 * arqpKappaHat P L p q ^ (q - 1) with hbq
      set bj := arqpTau P L p j / 2 * arqpKappaHat P L p q ^ (j - 1) with hbj
      refine ⟨bq ^ ((q : ℝ) * (p + 1) / p), arqpKappaDmOf_of_neg hq2 P L p q, ?_⟩
      have hπ : arqpPiOf u p j = (j : ℝ) * (p + 1) / p := arqpPiOf_of_neg hq2 p j
      rw [hπ] at hmj
      have hbq0 : 0 < bq := by positivity
      have hbq1 : bq ≤ 1 := by
        have : arqpKappaHat P L p q ^ (q - 1) ≤ 1 := pow_le_one₀ hκq.le hκq1
        calc bq ≤ 1 / 2 * 1 := by rw [hbq]; gcongr
          _ ≤ 1 := by norm_num
      have hbqj : bq ≤ bj := by
        rw [hbq, hbj]
        exact mul_le_mul (by linarith) (pow_le_pow_of_le_one hκq.le hκq1 (by omega))
          (by positivity) (by positivity)
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
      have hexp : ((p + 1 : ℕ) : ℝ) / (p : ℝ) ≤ (q : ℝ) * (p + 1) / p := by
        push_cast
        apply div_le_div_of_nonneg_right _ hp0.le
        have : (1 : ℝ) ≤ q := by exact_mod_cast hq
        nlinarith
      have hB : bq ^ ((q : ℝ) * (p + 1) / p) ≤ bj ^ (((p + 1 : ℕ) : ℝ) / (p : ℝ)) :=
        (Real.rpow_le_rpow_of_exponent_ge hbq0 hbq1 hexp).trans
          (Real.rpow_le_rpow hbq0.le hbqj (by positivity))
      have hεe : ε j ^ ((j : ℝ) * (p + 1) / p) = (ε j ^ j) ^ (((p + 1 : ℕ) : ℝ) / (p : ℝ)) := by
        rw [← Real.rpow_natCast (ε j) j, ← Real.rpow_mul hε0.le]
        push_cast
        ring_nf
      calc bq ^ ((q : ℝ) * (p + 1) / p) * m
          ≤ bj ^ (((p + 1 : ℕ) : ℝ) / (p : ℝ)) * ε j ^ ((j : ℝ) * (p + 1) / p) :=
            mul_le_mul hB hmj hm0.le (by positivity)
        _ = (bj * ε j ^ j) ^ (((p + 1 : ℕ) : ℝ) / (p : ℝ)) := by
            rw [hεe, ← Real.mul_rpow (by positivity) (by positivity)]
        _ ≤ (‖t‖ ^ p) ^ (((p + 1 : ℕ) : ℝ) / (p : ℝ)) :=
            Real.rpow_le_rpow (by positivity) (h2 hq2') (by positivity)
        _ = ‖t‖ ^ (p + 1) := by rw [pow_rpow_div (by omega) ht.le, Real.rpow_natCast]
  obtain ⟨B, hκ, hBm⟩ := key
  have hdec : arqpKappaDmOf u P L p q * m ≤ (ftaylorSeries ℝ f y).taylorDecrement p t := by
    rw [hκ]
    calc P.σmin / ((p + 1)! : ℝ) * B * m = P.σmin / ((p + 1)! : ℝ) * (B * m) := by ring
      _ ≤ P.σmin / ((p + 1)! : ℝ) * ‖t‖ ^ (p + 1) := by gcongr
      _ ≤ _ := hlow
  exact hdec

/-- **Sufficient decrease of ARqp** ([cartis2022evaluation], Lemmas 12.2.13 and 14.2.2). Let
`X ⊆ C`, `∇^p f` be `L_p`-Lipschitz anchored at the points of a set `A` containing
`{y ∈ X | f(y) ≤ f(x₀)}`, `L_p ≥ 1`, `1 ≤ q ≤ p`, `θ < ς` and `ε ∈ (0, 1]^q`. Every successful
iteration `k` of an ARqp run with exact data on `X` that is not
followed by termination, with the radii in mode `u` at `k + 1`, satisfies
`ΔT_{f,p}(x_k, s_k) ≥ κ_{Δm} min_j ε_j^{π_j}` and
`f(x_k) - f(x_{k+1}) ≥ η₁ κ_{Δm} min_j ε_j^{π_j}`. -/
theorem IsARqpRun.decrease (hf : LipschitzDerivsAnchored f C A p p L) (hL : 1 ≤ L p)
    (hXC : X ⊆ C) (hA : ∀ y ∈ X, f y ≤ f (x 0) → y ∈ A) (hq : 1 ≤ q)
    (hqp : q ≤ p)
    (hθς : P.θ < P.ς) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1)
    (h : IsARqpRun f X P q ε δ₀ (arqpData f p x σ) x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) (hs : P.η₁ ≤ arqpRho f p x s σ k)
    (hk1 : ¬ arqpStop₁ P q ε (arqpData f p x σ) δ d (k + 1))
    {u : Prop} [Decidable u] (hrad : (u → ∀ j ∈ Finset.Icc 1 q, δ (k + 1) j = 1) ∧
      (¬ u → 1 ≤ ‖s k‖ ∨ ∀ j ∈ Finset.Icc 1 q,
        arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)) * ε j ≤ δ (k + 1) j)) :
    arqpKappaDmOf u P L p q * finMin 1 (fun j => ε j ^ arqpPiOf u p j) q ≤
        (ftaylorSeries ℝ f (x k)).taylorDecrement p (s k) ∧
      P.η₁ * (arqpKappaDmOf u P L p q * finMin 1 (fun j => ε j ^ arqpPiOf u p j) q) ≤
        f (x k) - f (x (k + 1)) := by
  have hp : 1 ≤ p := hq.trans hqp
  have hσ := IsARqpRun.sigma_le_of_anchored hf hXC hA h k fun i hi => hk i hi.le
  obtain ⟨hxk, hfk⟩ := IsARqpRun.mem_sublevel h k fun i hi => hk i hi.le
  have hstep := h.step (fun i hi => hk i hi.le) fun h1 => hk k le_rfl (Or.inl h1)
  rw [(IsARqpRun.succ_eq h hk hs).2] at hrad
  have hdec := ARqpStep.taylorDecrement_ge hf hL hXC hq hqp hθς hε
    (hA _ hxk hfk) hσ.1
    hσ.2 hstep
    (h.model_lt hk)
    (IsARqpRun.next_witness h hk hs) (IsARqpRun.next_not_measureTestPasses h hk hs hk1) hrad
  refine ⟨hdec, ?_⟩
  have hT := (IsARqpRun.taylorDecrement_gt h hk).2
  have hpos : 0 < (ftaylorSeries ℝ f (x k)).taylorDecrement p (s k) := by
    have hσ0 := h.toIsARRun.sigma_pos (K := k) (fun i hi => hk i hi.le) k le_rfl
    exact lt_of_le_of_lt (by positivity) hT
  have := (h.toIsARRun.sub_ge_of_succ (w := f)
    (pred := fun k => (ftaylorSeries ℝ f (x k)).taylorDecrement p (s k)) hk rfl hpos hs).2
  exact (mul_le_mul_of_nonneg_left hdec P.η₁_pos.le).trans this

/-- The radii of an ARqp run stay equal to `1` at the orders `j ∈ [1:q]` if they start at `1`
and every step returns radii `1` there (as Lemma 12.2.9 allows for `q ≤ 2`). -/
theorem IsARqpRun.delta_eq_one (h : IsARqpRun f X P q ε δ₀ (arqpData f p x σ) x s σ δ δs d dm)
    (hδ₀ : ∀ j ∈ Finset.Icc 1 q, δ₀ j = 1)
    (hδs : ∀ k, (∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) → ∀ j ∈ Finset.Icc 1 q, δs k j = 1) :
    ∀ k, (∀ i < k, ¬ arqpStop f P p q ε x s σ δ d i) → ∀ j ∈ Finset.Icc 1 q, δ k j = 1 := by
  intro k
  induction k with
  | zero => exact fun _ j hj => by rw [h.delta_zero]; exact hδ₀ j hj
  | succ k ih =>
    intro hk j hj
    have hk' : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i := fun i hi => hk i (by omega)
    obtain ⟨hs, hu⟩ := h.radii k hk'
    by_cases hρ : P.η₁ ≤ arqpRho f p x s σ k
    · rw [hs hρ]; exact hδs k hk' j hj
    · rw [(hu hρ).1]; exact ih (fun i hi => hk' i hi.le) j hj

/-- **The counting argument of Theorem 12.2.14** ([cartis2022evaluation]): under the hypotheses
of `IsARqpRun.decrease`, with `f ≥ f_low` on `X`, `σ_min > 0` and the radii in mode
`u` after every successful iteration not followed by termination, an ARqp run with exact data on
`X` terminates within `κ^a (f(x₀) - f_low)/min_j ε_j^{π_j} + κ^c` evaluations of `f` and
`κ^s (f(x₀) - f_low)/min_j ε_j^{π_j} + 2` evaluations of the derivatives. -/
theorem IsARqpRun.exists_isFirstHit_of_anchored {flow : ℝ} (hb : ∀ y ∈ X, flow ≤ f y)
    (hf : LipschitzDerivsAnchored f C A p p L) (hL : 1 ≤ L p) (hXC : X ⊆ C)
    (hA : ∀ y ∈ X, f y ≤ f (x 0) → y ∈ A)
    (hq : 1 ≤ q) (hqp : q ≤ p) (hσmin : 0 < P.σmin) (hθς : P.θ < P.ς)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1)
    (h : IsARqpRun f X P q ε δ₀ (arqpData f p x σ) x s σ δ δs d dm)
    {u : Prop} [Decidable u] (hrad : ∀ k, (∀ i ≤ k + 1, ¬ arqpStop f P p q ε x s σ δ d i) →
      P.η₁ ≤ arqpRho f p x s σ k →
      (u → ∀ j ∈ Finset.Icc 1 q, δ (k + 1) j = 1) ∧
      (¬ u → 1 ≤ ‖s k‖ ∨ ∀ j ∈ Finset.Icc 1 q,
        arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)) * ε j ≤ δ (k + 1) j)) :
    ∃ kε, IsFirstHit (arqpStop f P p q ε x s σ δ d) kε ∧
      (funEvalCount kε : ℝ) ≤ kappaAARqpOf u P L p q * (f (x 0) - flow) /
        finMin 1 (fun j => ε j ^ arqpPiOf u p j) q + kappaCARqp P L p ∧
      (derivEvalCount (fun k => P.η₁ ≤ arqpRho f p x s σ k) kε : ℝ) ≤
        kappaSARqpOf u P L p q * (f (x 0) - flow) / finMin 1 (fun j => ε j ^ arqpPiOf u p j) q +
          2 := by
  have hp : 1 ≤ p := hq.trans hqp
  have hLp : 1 ≤ L p := hL
  set m := finMin 1 (fun j => ε j ^ arqpPiOf u p j) q with hm_def
  have hm0 : 0 < m := finMin_pos one_pos fun j hj => Real.rpow_pos_of_pos (hε j hj).1 _
  have hκ := arqpKappaDmOf_pos (q := q) u hσmin hθς hLp
  have hη := P.η₁_pos
  have hδ : 0 < P.η₁ * (arqpKappaDmOf u P L p q * m) := by positivity
  obtain ⟨kε, hk, hF, hD⟩ := h.toIsARRun.exists_isFirstHit_of_decrease
    (σmax := arSigmaMax P.toARParams (L p))
    (fun k hk => (IsARqpRun.sigma_le_of_anchored hf hXC hA h k hk).2)
    (V := fun k => f (x k)) (Vlow := flow) hδ (fun k hk => IsARqpRun.objective_le h hk)
    (fun k hk => hb _ (h.mem k hk))
    (fun k hk hs =>
      (IsARqpRun.decrease hf hL hXC hA hq hqp hθς hε h
        (fun i hi => hk i (by omega))
      hs
      (fun h1 => hk (k + 1) le_rfl (Or.inl h1)) (hrad k hk hs)).2)
  have hlog := P.toARParams.log_γ₂_pos
  refine ⟨kε, hk, hF.trans_eq ?_, hD.trans_eq ?_⟩
  · rw [kappaAARqpOf, kappaSARqpOf, kappaCARqp]
    field_simp
  · rw [kappaSARqpOf]
    field_simp

/-- **Certification at a model minimizer `0`, from the jet at `y`** (Lemma 12.2.10; §14.2): as
`isEpsDeltaApprox_of_isMinOn_zero`, with only `f` `C^p` at `y` and the jet bounds `‖∇^i f(y)‖ ≤
L_f`, `i ∈ [2:p]`, at `y` (as given at the iterates by the anchored assumptions). -/
theorem isEpsDeltaApprox_of_isMinOn_zero_of_jet {y : E} (hy : y ∈ X)
    (hy0 : ContDiffAt ℝ p f y)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ‖iteratedFDeriv ℝ i f y‖ ≤ finMax 1 L p) {σk : ℝ} (hqp : q ≤ p)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1)
    (hσ : 0 < σk)
    (hmin : IsMinOn (regularizedModel (ftaylorSeries ℝ f y) p σk) {e | y + e ∈ X} 0) :
    (∀ j ∈ Finset.Icc 1 q, min 1 (ε j / (4 * (3 * finMax 1 L p + σk))) ∈ Ioc 0 1) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f y) {e | y + e ∈ X} q ε
        (fun j => min 1 (ε j / (4 * (3 * finMax 1 L p + σk)))) := by
  have hL1 : 1 ≤ finMax 1 L p := one_le_finMax
  have hK : 0 < 3 * finMax 1 L p + σk := by linarith
  have hS0 : (0 : E) ∈ {e | y + e ∈ X} := by change y + 0 ∈ X; rw [add_zero]; exact hy
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · have := (hε j hj).1
    exact ⟨lt_min one_pos (by positivity), min_le_left _ _⟩
  · have hjp : j ≤ p := (Finset.mem_Icc.1 hj).2.trans hqp
    have hεj := (hε j hj).1
    have hδα : 4 * (3 * finMax 1 L p + σk) * min 1 (ε j / (4 * (3 * finMax 1 L p + σk))) ≤
        ε j := by
      calc 4 * (3 * finMax 1 L p + σk) * min 1 (ε j / (4 * (3 * finMax 1 L p + σk)))
          ≤ 4 * (3 * finMax 1 L p + σk) * (ε j / (4 * (3 * finMax 1 L p + σk))) := by
            gcongr; exact min_le_right _ _
        _ = ε j := by field_simp
    have := taylorMeasure_regularizedModel_le_of_isMinOn (D := ftaylorSeries ℝ f y)
      (zero_le_one.trans hL1)
      hjet hσ.le
      (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hj).1, hjp⟩) (by rw [norm_zero]; exact zero_le_one)
      hS0 (fun e he => by rw [zero_add]; exact hmin he) hεj
      (lt_min one_pos (by positivity)) (min_le_left _ _) hδα
    rw [taylorMeasure_regularizedModel_zero hy0 σk hjp] at this
    exact this

/-- **Evaluation complexity of ARqp** ([cartis2022evaluation], Theorem 12.2.14; Theorem 14.2.4
for ARqp-SC). Let `X ⊆ C`, `∇^p f` be `L_p`-Lipschitz anchored at the points of a set `A`
containing `{y ∈ X | f(y) ≤ f(x₀)}`, with jet bounds `L_f` at the anchors, `f ≥ f_low` on `X`,
`1 ≤ q ≤ p`, `σ_min > 0`, `θ < ς`, `ε ∈ (0, 1]^q`, `δ₀ ∈ (0, 1]^q`, and let the radii policy hold
in mode `u` (unit initial and returned radii if `u`; the lower bound `κ_δ(σ_k) ε_j` on the radii
of short steps if `¬ u`). Every ARqp run with exact data on `X` terminates at some `k_ε` with
`x_{k_ε} ∈ X` and an `(ε, δ_ε)`-approximate `q`-th order certificate over
`{d | x_{k_ε} + d ∈ X}` for some `δ_ε ∈ (0, 1]^q`, within the evaluation bounds of
`IsARqpRun.exists_isFirstHit_of_anchored`. -/
theorem IsARqpRun.complexity {flow : ℝ} (hb : ∀ y ∈ X, flow ≤ f y)
    (hf : LipschitzDerivsAnchored f C A p p L) (hL : 1 ≤ L p)
    (hjet : ∀ j ∈ Finset.Icc 2 p, ∀ x ∈ A, ‖iteratedFDeriv ℝ j f x‖ ≤ finMax 1 L p) (hXC : X ⊆ C)
      (hA : ∀ y ∈ X, f y ≤ f (x 0) → y ∈ A)
    (hq : 1 ≤ q) (hqp : q ≤ p)
    (hσmin : 0 < P.σmin) (hθς : P.θ < P.ς) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1)
    (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1)
    (h : IsARqpRun f X P q ε δ₀ (arqpData f p x σ) x s σ δ δs d dm)
    {u : Prop} [Decidable u]
    (hrad : (u → (∀ j ∈ Finset.Icc 1 q, δ₀ j = 1) ∧
        ∀ k, (∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) → ∀ j ∈ Finset.Icc 1 q, δs k j = 1) ∧
      (¬ u → ∀ k, (∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) → ‖s k‖ < 1 →
        ∀ j ∈ Finset.Icc 1 q, arqpKappaDelta P (finMax 1 L p) (σ k) * ε j ≤ δs k j)) :
    ∃ kε, IsFirstHit (arqpStop f P p q ε x s σ δ d) kε ∧ x kε ∈ X ∧
      (∃ δε : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, δε j ∈ Ioc 0 1) ∧
        IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) {e | x kε + e ∈ X} q ε δε) ∧
      (funEvalCount kε : ℝ) ≤ kappaAARqpOf u P L p q * (f (x 0) - flow) /
        finMin 1 (fun j => ε j ^ arqpPiOf u p j) q + kappaCARqp P L p ∧
      (derivEvalCount (fun k => P.η₁ ≤ arqpRho f p x s σ k) kε : ℝ) ≤
        kappaSARqpOf u P L p q * (f (x 0) - flow) / finMin 1 (fun j => ε j ^ arqpPiOf u p j) q +
          2 := by
  have hp : 1 ≤ p := hq.trans hqp
  have hL1 : 1 ≤ finMax 1 L p := one_le_finMax
  obtain ⟨kε, hk, hF, hD⟩ := IsARqpRun.exists_isFirstHit_of_anchored hb hf hL hXC hA hq hqp
    hσmin hθς hε h (u := u)
    fun k hk hs => by
    have hk' : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i := fun i hi => hk i (by omega)
    refine ⟨fun hq2 => ?_, fun hq2 => ?_⟩
    · exact IsARqpRun.delta_eq_one h (hrad.1 hq2).1 (hrad.1 hq2).2
        (k + 1) fun i hi => hk i (by omega)
    · by_cases hlong : 1 ≤ ‖s k‖
      · exact Or.inl hlong
      refine Or.inr fun j hj => ?_
      rw [(IsARqpRun.succ_eq h hk' hs).2]
      have hσ := IsARqpRun.sigma_le_of_anchored hf hXC hA h k fun i hi => hk' i hi.le
      have hσ0 : 0 ≤ σ k := P.σmin_nonneg.trans hσ.1
      refine le_trans ?_ (hrad.2 hq2 k hk' (not_le.1 hlong) j hj)
      exact mul_le_mul_of_nonneg_right (arqpKappaDelta_anti P hL1 hσ0 hσ.2) (hε j hj).1.le
  have hxk := h.mem kε hk.2
  have hxA := hA _ hxk (IsARqpRun.mem_sublevel h kε hk.2).2
  refine ⟨kε, hk, hxk, ?_, hF, hD⟩
  by_cases h1 : arqpStop₁ P q ε (arqpData f p x σ) δ d kε
  · exact ⟨δ kε, fun j hj => h.delta_mem hδ₀ kε hk.2 j hj,
      MeasureTestPasses.isEpsDeltaApprox P.ς_pos (h.witness kε hk.2) h1⟩
  · have hstep := h.step hk.2 h1
    have h2 : arqpStop₂ (arqpData f p x σ) s kε := hk.1.resolve_left h1
    have hσ : 0 < σ kε := h.toIsARRun.sigma_pos hk.2 kε le_rfl
    obtain ⟨hδ, hcert⟩ := isEpsDeltaApprox_of_isMinOn_zero_of_jet hxk
      (hf.contDiffAt _ (hf.subset hxA))
      (fun _ hi => hjet _ hi _ hxA) hqp hε hσ
      (hstep.isMinOn_of_eq h2)
    exact ⟨_, hδ, hcert⟩

end Optimization

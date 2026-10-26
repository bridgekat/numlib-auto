import Numlib.Optimization.Composite.MissingAccuracyCounterexample
import Numlib.Optimization.Composite.FunctionDecreaseCounterexample
import Numlib.Optimization.Composite.Sharpness
import Numlib.Optimization.Composite.ZeroReturnCounterexample
import Numlib.Optimization.Composite.Complexity
import Numlib.Optimization.Composite.ModelError
import Numlib.Optimization.Composite.OuterCounterexample
import Numlib.Optimization.Composite.Origin
import Numlib.Optimization.Composite.ModelCriticality
import Numlib.Optimization.Composite.ModelTaylor
import NumlibSurface.CartisGouldToint.Chapter04.Section01
import Numlib.Optimization.HighOrder.ModelDecrease
import Numlib.Optimization.Composite.Optimality
import Numlib.Optimization.Composite.Regularization
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Taylor decrease for composite regularization

The generalized composite Taylor model approximates the smooth maps `f` and `c` while keeping
`h` intact. A nonincreasing step for its regularization gives the full decrement estimate of
Lemma 14.1.5, irrespective of whether `h` is differentiable.

Lemma 14.1.1 derives global minimality of the first-order model at zero and vanishing
actual composite criticality. Its source assumptions on subadditivity and `h(0)` are
unnecessary: Lipschitz continuity and convexity of `h` suffice.

Lemmas 14.1.2--14.1.3 and the detailed-solver companion to Lemma 14.1.4 use
the smooth penalized scalar part and residual polynomial
for the model's genuine generalized Taylor criticality. They derive the exact
small-radius decrease, actual global-minimum step existence, quantitative radii,
and the objective optimality certified by a zero-decrease global-gap return.
Corollary 14.1.11 embeds actual uniform smooth sharpness runs with zero residual
and the nonzero convex outer function absolute value.
The literal outer Step2 lacks that global-gap condition. Its permitted large
zero-improvement return disproves literal Lemma 14.1.4 and Theorem 14.1.10, even
with unit first-order radii; the detailed-solver companions remain valid.

The detailed-solver companion to Theorem 14.1.10 proves both evaluation orders
with fixed positive constants before all accuracies. The corrected two-term
residual-value error changes permitted
constants while preserving the theorem's existential constant and rate claims.
The actual run enforces the accuracy ranges and detailed solver return checks.
-/

namespace CartisGouldToint

/-- The generalized Taylor model `T_{w,p}` of the composite objective `w = f + h ∘ c`. -/
noncomputable def compositeTaylorModel {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → ℝ) (c : E → F) (h : F → ℝ) (p : ℕ) (x s : E) : ℝ :=
  Composite.taylorModel f c h p x s

/-- At zero displacement the composite Taylor model equals the true composite objective. -/
@[simp] theorem compositeTaylorModel_zero {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → ℝ) (c : E → F) (h : F → ℝ) (p : ℕ) (x : E) :
    compositeTaylorModel f c h p x 0 = f x + h (c x) := by
  simp [compositeTaylorModel]

/-- Lemma 14.1.5: the composite Taylor decrement at an ARqpC model-improving step is at least
the norm-power regularization penalty. The single hypothesis is the model comparison (14.1.11)
made when choosing the step, with the model given explicitly by equation (14.1.5). -/
theorem lemma_14_1_5 {n m : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (p : ℕ) (σ : ℝ)
    (x s : EuclideanSpace ℝ (Fin n))
    (hs : ModelDecrease.penalized (compositeTaylorModel f c h p x) p σ s ≤
      ModelDecrease.penalized (compositeTaylorModel f c h p x) p σ 0) :
    σ / ((p + 1).factorial : ℝ) * ‖s‖ ^ (p + 1) ≤
      compositeTaylorModel f c h p x 0 - compositeTaylorModel f c h p x s :=
  ModelDecrease.penalty_le_decrement _ _ _ _ hs

end CartisGouldToint

namespace CartisGouldToint

/-- The composite criticality measure (14.1.6), the largest decrease of the actual
composite Taylor model over the closed displacement ball. -/
noncomputable def compositeCriticality {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → ℝ) (c : E → F) (h : F → ℝ) (p : ℕ) (x : E) (δ : ℝ) : ℝ :=
  Composite.criticality f c h p x δ

/-- **Lemma 14.1.1 (convex-composite first-order necessary optimality).**
A true global minimum of `f + h ∘ c` globally minimizes its first-order composite model
at zero and has zero first-order composite criticality at every positive radius.
The source's subadditivity and zero-value assumptions on `h` can be omitted; Lipschitz
continuity controls the genuine derivative remainders directly. -/
theorem lemma_14_1_1 {n m : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (x : EuclideanSpace ℝ (Fin n)) {K : NNReal}
    (hf : ContDiff ℝ 1 f) (hc : ContDiff ℝ 1 c)
    (hh : LipschitzWith K h) (hconv : ConvexOn ℝ Set.univ h)
    (hmin : IsMinOn (fun z => f z + h (c z)) Set.univ x) :
    IsMinOn (compositeTaylorModel f c h 1 x) Set.univ 0 ∧
      ∀ δ : ℝ, 0 < δ → compositeCriticality f c h 1 x δ = 0 := by
  have hm := Composite.taylorModel_one_isMinOn_of_isMinOn
    (hf.differentiable (by norm_num) x) (hc.differentiable (by norm_num) x) hh hconv hmin
  exact ⟨hm, fun _ hδ => Composite.criticality_eq_zero_of_model_min f c h 1 x hδ.le hm⟩

end CartisGouldToint

namespace CartisGouldToint

/-- The ARqpC model, actual ratio and parameter updates used in Lemma 14.1.6.
Step stationarity and stopping tests are unnecessary for this parameter bound. -/
abbrev compositeModelTrace {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → ℝ) (c : E → F) (h : F → ℝ) (p : ℕ)
    (x s : ℕ → E) (σ ρ : ℕ → ℝ)
    (η₁ η₂ γ₁ γ₂ γ₃ σmin : ℝ) (N : ℕ) : Prop :=
  Composite.ModelTrace f c h p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N

/-- **Lemma 14.1.6.** The parameter bound (14.1.26) with exactly the
combined Lipschitz constant (14.1.27). Residual smoothness is componentwise,
which accounts for the square-root dimension factor. Writing the model degree
as `p+1` covers every positive degree and preserves the source's finite smoothness. -/
theorem lemma_14_1_6 {n m p N : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {h : EuclideanSpace ℝ (Fin m) → ℝ}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin Lf Lc : ℝ} {Lh : NNReal}
    (ht : compositeModelTrace f c h (p + 1) x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hf : ContDiff ℝ (p + 1) f) (hLf : 0 ≤ Lf) (hLc : 0 ≤ Lc)
    (hc : ∀ i, ContDiff ℝ (p + 1) (fun z => c z i))
    (hlipf : ∀ y z, ‖iteratedFDeriv ℝ (p + 1) f y - iteratedFDeriv ℝ (p + 1) f z‖ ≤
      Lf * ‖y - z‖)
    (hlipc : ∀ i y z, ‖iteratedFDeriv ℝ (p + 1) (fun w => c w i) y -
      iteratedFDeriv ℝ (p + 1) (fun w => c w i) z‖ ≤ Lc * ‖y - z‖)
    (hh : LipschitzWith Lh h) :
    ∀ i ≤ N, σ i ≤ max (σ 0) (γ₃ * (Lf + Real.sqrt m * (Lh : ℝ) * Lc) / (1 - η₂)) :=
  fun _ hi => ht.parameter_le hf hLf hLc hc hlipf hlipc hh hi

/-- **Lemma 14.1.2.** A sufficiently small normalized generalized Taylor trial
retains half its decrease in the actual regularized composite model. The outer
function is retained exactly; its differentiability is unnecessary. The source's
subadditivity and zero-at-zero assumptions are not needed for this conclusion. -/
theorem lemma_14_1_2 {n m p j : ℕ} (hj : 1 ≤ j) (hjp : j ≤ p)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (_hf : ContDiff ℝ p f) (hc : ∀ i, ContDiff ℝ p (fun z => c z i))
    {Lf Lc σ α δ : ℝ} {K : NNReal} (hLf : 0 ≤ Lf) (hLc : 0 ≤ Lc)
    (hlipf : ∀ a, 1 ≤ a → a ≤ p → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ Lf * ‖u - v‖)
    (hlipc : ∀ i a, 1 ≤ a → a ≤ p → ∀ u v,
      ‖iteratedFDeriv ℝ a (fun z => c z i) u -
        iteratedFDeriv ℝ a (fun z => c z i) v‖ ≤ Lc * ‖u - v‖)
    (hh : LipschitzWith K h) (hσ : 0 < σ) (_hα : 0 < α)
    (x s d : EuclideanSpace ℝ (Fin n)) (hs : ‖s‖ ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hd : ‖d‖ ≤ δ)
    (hsmall : δ ≤ α / (4 * (3 * (Lf + Real.sqrt m * (K : ℝ) * Lc) + σ)))
    (htest : α * δ ^ j / j.factorial ≤
      Composite.decrement (Composite.smoothModel f p x σ)
        (Composite.residualModel c p x) h j s d) :
    α / 2 * δ ^ j / j.factorial ≤
      Composite.regularizedModel f c h p x σ s -
        Composite.regularizedModel f c h p x σ (s + d) := by
  have hcv : ContDiff ℝ p c := (contDiff_piLp 2).mpr hc
  apply Composite.regularizedModel_decrement_ge_half f c hj hjp hLf
    (mul_nonneg (Real.sqrt_nonneg _) hLc) hσ hh x s d hs
    (fun a ha hap => Composite.norm_iteratedFDeriv_le_of_lipschitz_lower hLf
      (fun b hb hbp => hlipf b hb hbp.le) ha hap x)
    (fun a ha hap => Composite.norm_iteratedFDeriv_le_componentwise hcv hLc
      (fun i b hb hbp => hlipc i b hb hbp.le) ha hap x)
    hδ hδ1 hd _ htest
  convert hsmall using 1
  ring

/-- **Lemma 14.1.3.** A genuine global composite model minimum supplies a step,
attaining generalized Taylor directions, and normalized criticality tests with
the exact source radius floor. A convex outer function permits unit first-order
radius. The radius floor also holds at order one and for large minimizing steps. -/
theorem lemma_14_1_3 {n m p q : ℕ} (_hq : 1 ≤ q) (hqp : q ≤ p)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (_hf : ContDiff ℝ p f) (hc : ∀ i, ContDiff ℝ p (fun z => c z i))
    {Lf Lc σ θ ζ : ℝ} {K : NNReal} (hLf : 1 ≤ Lf) (hLc : 0 ≤ Lc)
    (hlipf : ∀ a, 1 ≤ a → a ≤ p → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ Lf * ‖u - v‖)
    (hlipc : ∀ i a, 1 ≤ a → a ≤ p → ∀ u v,
      ‖iteratedFDeriv ℝ a (fun z => c z i) u -
        iteratedFDeriv ℝ a (fun z => c z i) v‖ ≤ Lc * ‖u - v‖)
    (hh : LipschitzWith K h) (hσ : 0 < σ) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (x : EuclideanSpace ℝ (Fin n))
    (ε : Fin q → ℝ) (hε : ∀ a, 0 < ε a ∧ ε a ≤ 1) :
    ∃ (s : EuclideanSpace ℝ (Fin n)) (δ : Fin q → ℝ)
      (d : Fin q → EuclideanSpace ℝ (Fin n)),
      Composite.regularizedModel f c h p x σ s ≤
        Composite.regularizedModel f c h p x σ 0 ∧
      (∀ a, 0 < δ a ∧ δ a ≤ 1) ∧
      (∀ a, a.val + 1 = 1 → ConvexOn ℝ Set.univ h → δ a = 1) ∧
      (∀ a, ζ * θ / (8 * (3 * (Lf + Real.sqrt m * (K : ℝ) * Lc) + σ)) * ε a ≤ δ a) ∧
      (1 < ‖s‖ ∨ ∀ a, ‖d a‖ ≤ δ a ∧
        ζ * Composite.criticality (Composite.smoothModel f p x σ)
          (Composite.residualModel c p x) h (a.val + 1) s (δ a) ≤
          Composite.decrement (Composite.smoothModel f p x σ)
            (Composite.residualModel c p x) h (a.val + 1) s (d a) ∧
        Composite.decrement (Composite.smoothModel f p x σ)
            (Composite.residualModel c p x) h (a.val + 1) s (d a) ≤
          ζ * θ * ε a * δ a ^ (a.val + 1) / (a.val + 1).factorial) := by
  have hcv : ContDiff ℝ p c := (contDiff_piLp 2).mpr hc
  obtain ⟨s, δ, d, hmin, hδ, hone, hfloor, htest⟩ :=
    Composite.exists_minimizer_with_criticality f c p (fun a : Fin q => a.val + 1)
      (fun a => ⟨by omega, (Nat.succ_le_of_lt a.isLt).trans hqp⟩) hLf
      (mul_nonneg (Real.sqrt_nonneg _) hLc) hσ hh hθ hθ1.le hζ hζ1 x ε hε
      (fun a ha hap => Composite.norm_iteratedFDeriv_le_of_lipschitz_lower
        (zero_le_one.trans hLf) (fun b hb hbp => hlipf b hb hbp.le) ha hap x)
      (fun a ha hap => Composite.norm_iteratedFDeriv_le_componentwise hcv hLc
        (fun i b hb hbp => hlipc i b hb hbp.le) ha hap x)
  refine ⟨s, δ, d, hmin 0, hδ, hone, ?_, ?_⟩
  · intro a
    convert hfloor a using 1
    ring
  · by_cases hs : ‖s‖ ≤ 1
    · exact Or.inr (htest hs)
    · exact Or.inl (lt_of_not_ge hs)

/-- **Detailed-solver companion to Lemma 14.1.4.** A zero-decrease Step2 return
satisfying the actual positive-fraction global-gap rule gives genuine
approximate composite optimality
at positive radii. It cannot follow a failed Step1 test when q=1 and h is convex. -/
theorem lemma_14_1_4_detailed_solver {n m p q : ℕ} (hqp : q ≤ p)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hf : ContDiff ℝ p f) (hc : ∀ i, ContDiff ℝ p (fun z => c z i))
    {Lf Lc σ μ ζ : ℝ} {K : NNReal} (hLf : 0 ≤ Lf) (hLc : 0 ≤ Lc)
    (hlipf : ∀ a, 1 ≤ a → a ≤ p → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ Lf * ‖u - v‖)
    (hlipc : ∀ i a, 1 ≤ a → a ≤ p → ∀ u v,
      ‖iteratedFDeriv ℝ a (fun z => c z i) u -
        iteratedFDeriv ℝ a (fun z => c z i) v‖ ≤ Lc * ‖u - v‖)
    (hh : LipschitzWith K h) (hσ : 0 < σ) (hμ : 0 < μ) (hζ : 0 < ζ)
    (x s : EuclideanSpace ℝ (Fin n))
    (hsolve : ModelDecrease.ApproximateGlobalStep
      (Composite.regularizedModel f c h p x σ) μ s)
    (hzero : Composite.regularizedModel f c h p x σ 0 =
      Composite.regularizedModel f c h p x σ s)
    (ε δ₀ : Fin q → ℝ) (hε : ∀ a, 0 < ε a) (hδ₀ : ∀ a, 0 < δ₀ a)
    (direction : Fin q → EuclideanSpace ℝ (Fin n))
    (hfeasible : ∀ a, ‖direction a‖ ≤ δ₀ a)
    (hfailed : ∃ a, ζ * ε a * δ₀ a ^ (a.val + 1) / (a.val + 1).factorial <
      Composite.decrement f c h (a.val + 1) x (direction a)) :
    (q = 1 → ¬ConvexOn ℝ Set.univ h) ∧
      ∃ δ : Fin q → ℝ, (∀ a, 0 < δ a ∧ δ a ≤ 1) ∧
        ∀ a, Composite.criticality f c h (a.val + 1) x (δ a) ≤
          ε a * δ a ^ (a.val + 1) / (a.val + 1).factorial := by
  have hcv : ContDiff ℝ p c := (contDiff_piLp 2).mpr hc
  exact Composite.zero_step_termination hqp hf.contDiffAt hcv.contDiffAt hLf
    (mul_nonneg (Real.sqrt_nonneg _) hLc) hσ hμ hζ hh
    (fun a ha hap => Composite.norm_iteratedFDeriv_le_of_lipschitz_lower hLf
      (fun b hb hbp => hlipf b hb hbp.le) ha hap x)
    (fun a ha hap => Composite.norm_iteratedFDeriv_le_componentwise hcv hLc
      (fun i b hb hbp => hlipc i b hb hbp.le) ha hap x)
    hsolve hzero ε δ₀ hε hδ₀ direction hfeasible hfailed

/-- **Counterexample to Lemma 14.1.7.** The literal outer Algorithm 14.1.1
admits an exact global model solve with a small first-order radius. All actual
smoothness, global-gap, criticality, ratio and update checks hold, while the
printed coefficient-one residual bound fails. The optional detailed solver's
convex unit-radius choice excludes this execution. -/
alias lemma_14_1_7_counterexample := Composite.OuterCounterexample.verified_counterexample

/-- **Corrected companion to Lemma 14.1.7.** Actual accepted-point optimality
failure and the operational model tests imply the weighted step obstruction with
twice the residual value error. Both outer increments contribute this error.
The parameter cap is derived from the actual model ratio and update trace. -/
theorem lemma_14_1_7_corrected {n m p q N : ℕ} (hqp : q ≤ p + 1)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (h : EuclideanSpace ℝ (Fin m) → ℝ)
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin Lf Lc θ : ℝ} {K : NNReal}
    (ht : Composite.ModelTrace f c h (p + 1) x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hf : ContDiff ℝ (p + 1) f) (hLf : 1 ≤ Lf) (hLc : 0 ≤ Lc)
    (hc : ∀ a, ContDiff ℝ (p + 1) (fun z => c z a))
    (hlipf : ∀ u v, ‖iteratedFDeriv ℝ (p + 1) f u -
      iteratedFDeriv ℝ (p + 1) f v‖ ≤ Lf * ‖u - v‖)
    (hlipc : ∀ a u v, ‖iteratedFDeriv ℝ (p + 1) (fun z => c z a) u -
      iteratedFDeriv ℝ (p + 1) (fun z => c z a) v‖ ≤ Lc * ‖u - v‖)
    (hh : LipschitzWith K h) (hθ : 0 ≤ θ) {i : ℕ} (hi : i < N)
    (_haccepted : η₁ ≤ ρ i) (hnext : x (i + 1) = x i + s i)
    (ε δ : Fin q → ℝ) (hε : ∀ a, 0 < ε a ∧ ε a ≤ 1)
    (hδ : ∀ a, 0 < δ a ∧ δ a ≤ 1)
    (htest : ‖s i‖ ≤ 1 → ∀ a,
      Composite.criticality (Composite.smoothModel f (p + 1) (x i) (σ i))
        (Composite.residualModel c (p + 1) (x i)) h (a.val + 1) (s i) (δ a) ≤
          θ * ε a * δ a ^ (a.val + 1) / (a.val + 1).factorial)
    (hnot : ¬∀ a, Composite.criticality f c h (a.val + 1) (x (i + 1)) (δ a) ≤
      ε a * δ a ^ (a.val + 1) / (a.val + 1).factorial) :
    let S := max (σ 0) (γ₃ * (Lf + Real.sqrt m * (K : ℝ) * Lc) / (1 - η₂))
    ∃ a, (1 - θ) * ε a * δ a ^ (a.val + 1) / (a.val + 1).factorial ≤
      (Lf + Real.sqrt m * (K : ℝ) * Lc + S) *
        (∑ b ∈ Finset.range (a.val + 1),
          δ a ^ (b + 1) * ‖s i‖ ^ (p + 1 - (b + 1) + 1) / (b + 1).factorial) +
      2 * Real.sqrt m * (K : ℝ) * Lc * ‖s i‖ ^ (p + 2) / (p + 2).factorial := by
  have hcv : ContDiff ℝ (p + 1) c := (contDiff_piLp 2).mpr hc
  have hcap := ht.parameter_le hf (zero_le_one.trans hLf) hLc hc hlipf hlipc hh
    (show i ≤ N by omega)
  have hσ := ht.updates.pos (show i ≤ N by omega)
  rw [hnext] at hnot
  obtain ⟨a, ha⟩ := Composite.criticality_obstruction hqp f c hf hcv hLf
    (mul_nonneg (Real.sqrt_nonneg _) hLc) hσ.le hcap hθ hh hlipf
    (Composite.norm_iteratedFDeriv_sub_le_componentwise hcv hLc hlipc)
    (x i) (s i) ε δ hε hδ htest hnot
  refine ⟨a, ?_⟩
  convert ha using 1
  ring

/-- **Detailed-solver companion to Theorem 14.1.10.** Both regimes hold with positive
constants chosen before all accuracies and actual execution data. The favorable
case produces a unit-radius first-order certificate; its accuracy factor is the
single requested accuracy raised to `(p+1)/p`. The general case uses the actual
minimum of `ε_j^(j+1)`. Counts include initialization and the first certificate.

The execution uses the detailed solver's positive global-gap fraction. True
certificate attainment is distinguished from the computed stopping test.
The corrected two-term residual estimate changes permissible constants but
preserves the two asserted evaluation orders. -/
theorem theorem_14_1_10_detailed_solver {n m p q : ℕ} (P : Composite.Settings p q)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hf : ContDiff ℝ p f) (hc : ∀ i, ContDiff ℝ p (fun z => c z i))
    {Lf Lc wlow : ℝ} {K : NNReal} (hLf : 1 ≤ Lf) (hLc : 0 ≤ Lc)
    (hlipf : ∀ a, 1 ≤ a → a ≤ p → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ Lf * ‖u - v‖)
    (hlipc : ∀ i a, 1 ≤ a → a ≤ p → ∀ u v,
      ‖iteratedFDeriv ℝ a (fun z => c z i) u -
        iteratedFDeriv ℝ a (fun z => c z i) v‖ ≤ Lc * ‖u - v‖)
    (hh : LipschitzWith K h) (_hsub : ∀ u v, h (u + v) ≤ h u + h v) (_hz : h 0 = 0)
    (hlow : ∀ x, wlow ≤ f x + h (c x)) :
    let Lw := Lf + (K : ℝ) * (Real.sqrt m * Lc)
    (q = 1 → ConvexOn ℝ Set.univ h →
      ∃ κs κa κc : ℝ, 0 < κs ∧ 0 < κa ∧ 0 < κc ∧
        ∀ (ε : Fin q → ℝ)
          (D : Composite.ExecutionData (EuclideanSpace ℝ (Fin n)) q),
          (∀ N, (∀ k < N, ¬Composite.TargetAt f c h P ε D k) →
            Composite.Run f c h P ε D N) →
          (∀ k a, D.solvedRadius k a = 1) →
          ∃ k, Composite.Run f c h P ε D k ∧
            (∀ a, Composite.criticality f c h 1 (D.point k) 1 ≤ ε a) ∧
            (Composite.functionEvaluations k : ℝ) ≤
              κa * (f (D.point 0) + h (c (D.point 0)) - wlow) /
                (ε ⟨0, P.order_pos⟩) ^ Composite.unitExponent p + κc ∧
            (Composite.derivativeEvaluations D.ratio P.eta1 k : ℝ) ≤
              κs * (f (D.point 0) + h (c (D.point 0)) - wlow) /
                (ε ⟨0, P.order_pos⟩) ^ Composite.unitExponent p + 2) ∧
      ((1 < q ∨ ¬ConvexOn ℝ Set.univ h) →
        ∃ κs κa κc : ℝ, 0 < κs ∧ 0 < κa ∧ 0 < κc ∧
          ∀ (ε : Fin q → ℝ)
            (D : Composite.ExecutionData (EuclideanSpace ℝ (Fin n)) q),
            (∀ N, (∀ k < N, ¬Composite.TargetAt f c h P ε D k) →
              Composite.Run f c h P ε D N) →
            (∀ k, ‖D.step k‖ < 1 → ∀ a,
              Composite.radiusCoefficient P Lw (HighOrderRegularization.parameterCap P Lw) *
                ε a ≤ D.solvedRadius k a) →
            ∃ (k : ℕ) (δ : Fin q → ℝ), Composite.Run f c h P ε D k ∧
              Composite.OptimalityAt f c h ε (D.point k) δ ∧
              (Composite.functionEvaluations k : ℝ) ≤
                κa * (f (D.point 0) + h (c (D.point 0)) - wlow) /
                  Composite.generalAccuracyFactor P ε + κc ∧
              (Composite.derivativeEvaluations D.ratio P.eta1 k : ℝ) ≤
                κs * (f (D.point 0) + h (c (D.point 0)) - wlow) /
                  Composite.generalAccuracyFactor P ε + 2) := by
  dsimp only
  have hcv : ContDiff ℝ p c := (contDiff_piLp 2).mpr hc
  have hlipv : ∀ a, 1 ≤ a → a ≤ p → ∀ u v,
      ‖iteratedFDeriv ℝ a c u - iteratedFDeriv ℝ a c v‖ ≤
        (Real.sqrt m * Lc) * ‖u - v‖ := by
    intro a ha hap u v
    exact Composite.norm_iteratedFDeriv_sub_le_componentwise
      (hcv.of_le (by exact_mod_cast hap)) hLc (fun i => hlipc i a ha hap) u v
  constructor
  · intro hq hconv
    obtain ⟨κs, κa, κc, hs, ha, hcpos, hb⟩ :=
      Composite.complexity_unit P hq f c hf hcv hLf
        (mul_nonneg (Real.sqrt_nonneg _) hLc) hh hconv hlipf hlipv hlow
    refine ⟨κs, κa, κc, hs, ha, hcpos, ?_⟩
    intro ε D hprefix hunit
    obtain ⟨k, hr, hcrit, hfun, hder⟩ := hb ε D hprefix hunit
    refine ⟨k, hr, hcrit, ?_, ?_⟩
    · simpa only [Composite.unitAccuracyFactor_eq_of_order_one P hq ε
        ⟨0, P.order_pos⟩] using hfun
    · simpa only [Composite.unitAccuracyFactor_eq_of_order_one P hq ε
        ⟨0, P.order_pos⟩] using hder
  · intro _
    exact Composite.complexity_general P f c hf hcv hLf
      (mul_nonneg (Real.sqrt_nonneg _) hLc) hh hlipf hlipv hlow

/-- **Counterexample to literal Lemma 14.1.4.** Legal outer Step2 exits for a
convex outer function and q=1. The sole produced point has no certifying radius.
The positive global-gap condition of detailed Algorithm 14.1.2 excludes it. -/
theorem lemma_14_1_4_counterexample :
    Composite.OuterZeroExit RegularizationZeroReturn.objective
      (fun _ : ℝ => (0 : ℝ)) abs Composite.ZeroReturnCounterexample.settings
      (fun _ : Fin 1 => 1 / 2) 0 4 (fun _ => 1) (fun _ => 1)
        (fun _ => 1) (fun _ => 0) 0 ∧
    ConvexOn ℝ Set.univ (abs : ℝ → ℝ) ∧
    ¬∃ (z : ℝ) (δ : Fin 1 → ℝ),
      Composite.ZeroReturnCounterexample.actual_exit.producedPoint z ∧
      Composite.OptimalityAt RegularizationZeroReturn.objective
        (fun _ : ℝ => (0 : ℝ)) abs (fun _ => 1 / 2) z δ := by
  exact ⟨Composite.ZeroReturnCounterexample.actual_exit,
    Composite.ZeroReturnCounterexample.outer_properties.2.1,
    Composite.ZeroReturnCounterexample.no_produced_certificate⟩

/-- **Counterexample to literal Theorem 14.1.10.** A globally smooth, bounded-below
problem satisfies all outer assumptions and the unit-radius policy. A permitted
immediate outer exit produces no point with the claimed true optimality.
-/
theorem theorem_14_1_10_counterexample :
    ContDiff ℝ 1 RegularizationZeroReturn.objective ∧
    ContDiff ℝ 1 (fun _ : ℝ => (0 : ℝ)) ∧
    (∀ x y, ‖iteratedFDeriv ℝ 1 RegularizationZeroReturn.objective x -
      iteratedFDeriv ℝ 1 RegularizationZeroReturn.objective y‖ ≤
      1 * ‖x - y‖) ∧
    (∀ x y, ‖iteratedFDeriv ℝ 1 (fun _ : ℝ => (0 : ℝ)) x -
      iteratedFDeriv ℝ 1 (fun _ : ℝ => (0 : ℝ)) y‖ ≤ 1 * ‖x - y‖) ∧
    (∀ x, 0 ≤ RegularizationZeroReturn.objective x + |(0 : ℝ)|) ∧
    LipschitzWith 1 (abs : ℝ → ℝ) ∧ ConvexOn ℝ Set.univ (abs : ℝ → ℝ) ∧
    (∀ u v : ℝ, |u + v| ≤ |u| + |v|) ∧ |(0 : ℝ)| = 0 ∧
    Composite.OuterZeroExit RegularizationZeroReturn.objective
      (fun _ : ℝ => (0 : ℝ)) abs Composite.ZeroReturnCounterexample.settings
      (fun _ : Fin 1 => 1 / 2) 0 4 (fun _ => 1) (fun _ => 1)
        (fun _ => 1) (fun _ => 0) 0 ∧
    ¬∃ (z : ℝ) (δ : Fin 1 → ℝ),
      Composite.ZeroReturnCounterexample.actual_exit.producedPoint z ∧
      Composite.OptimalityAt RegularizationZeroReturn.objective
        (fun _ : ℝ => (0 : ℝ)) abs (fun _ => 1 / 2) z δ :=
  Composite.ZeroReturnCounterexample.verified_counterexample

/-- **Corollary 14.1.11.** For every p≥1, fixed legal settings and uniform
problem constants precede accuracy. A genuine bounded smooth scalar objective,
zero residual and nonzero convex outer function admit actual ARqpC executions
whose first true certificate and every derivative evaluation count attain
ε^(-(p+1)/p). Both data functions are evaluated on the same actual schedule.
-/
theorem corollary_14_1_11 {p : ℕ} (hp : 1 ≤ p) :
    ContDiff ℝ p (fun _ : ℝ => (0 : ℝ)) ∧
    (∀ j ≤ p, ∀ x y : ℝ,
      ‖iteratedFDeriv ℝ j (fun _ : ℝ => (0 : ℝ)) x -
        iteratedFDeriv ℝ j (fun _ : ℝ => (0 : ℝ)) y‖ ≤ 1 * ‖x - y‖) ∧
    LipschitzWith 1 (abs : ℝ → ℝ) ∧ ConvexOn ℝ Set.univ (abs : ℝ → ℝ) ∧
    (∀ u v : ℝ, |u + v| ≤ |u| + |v|) ∧ |(0 : ℝ)| = 0 ∧ |(1 : ℝ)| ≠ 0 ∧
    ∃ P : Composite.Settings p 1, ∃ L B : ℝ, 1 ≤ L ∧ 0 < B ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∃ (f : ℝ → ℝ) (D : Composite.ExecutionData ℝ 1) (N : ℕ),
        ContDiff ℝ p f ∧ (∀ x, |f x| ≤ B) ∧
        (∀ j ≤ p, ∀ x y,
          ‖iteratedFDeriv ℝ j f x - iteratedFDeriv ℝ j f y‖ ≤ L * ‖x - y‖) ∧
        Composite.Run f (fun _ : ℝ => (0 : ℝ)) abs P (fun _ => ε) D N ∧
        StrictMono D.point ∧ D.selected N = none ∧
        (∀ k a, D.radius k a = 1 ∧ D.solvedRadius k a = 1) ∧
        Composite.criticality f (fun _ : ℝ => (0 : ℝ)) abs 1 (D.point N) 1 ≤ ε ∧
        (∀ k < N, ε < Composite.criticality f (fun _ : ℝ => (0 : ℝ)) abs 1 (D.point k) 1) ∧
        ε ^ (-((p + 1 : ℕ) : ℝ) / p) ≤ (N : ℝ) ∧
        Composite.functionEvaluations N = N + 1 ∧
        ∀ j, 1 ≤ j → j ≤ p →
          ε ^ (-((p + 1 : ℕ) : ℝ) / p) ≤
            ((HighOrderRegularization.Sharpness.derivativeEvaluationNodes
              D.selected j N).card : ℝ) := by
  refine ⟨contDiff_const, ?_, Composite.ZeroReturnCounterexample.outer_properties.1,
    Composite.ZeroReturnCounterexample.outer_properties.2.1,
    Composite.ZeroReturnCounterexample.outer_properties.2.2.1,
    Composite.ZeroReturnCounterexample.outer_properties.2.2.2.1,
    Composite.ZeroReturnCounterexample.outer_properties.2.2.2.2,
    Composite.exists_first_order_sharpness hp⟩
  intro j hj x y
  simp

/-- **Counterexample to literal Lemma 14.1.9.** An actual accepted detailed-solver
trial decreases the full composite objective and increases its smooth scalar
part f. It is the last trial before the successful endpoint check. The printed
statement requires only nontermination before this trial, and imposes no failure
of the next-iterate test. A valid decrease statement concerns w=f+h∘c.
-/
theorem lemma_14_1_9_counterexample :
    let f := Composite.FunctionDecreaseCounterexample.f
    let c := Composite.FunctionDecreaseCounterexample.c
    let settings := Composite.FunctionDecreaseCounterexample.settings
    let data := Composite.FunctionDecreaseCounterexample.data
    ContDiff ℝ 1 f ∧ ContDiff ℝ 1 c ∧
    (∀ x y, ‖iteratedFDeriv ℝ 1 f x - iteratedFDeriv ℝ 1 f y‖ ≤ 1 * ‖x - y‖) ∧
    (∀ x y, ‖iteratedFDeriv ℝ 1 c x - iteratedFDeriv ℝ 1 c y‖ ≤ 1 * ‖x - y‖) ∧
    (∀ x, 0 ≤ f x + |c x|) ∧
    LipschitzWith 1 (abs : ℝ → ℝ) ∧ ConvexOn ℝ Set.univ (abs : ℝ → ℝ) ∧
    (∀ u v : ℝ, |u + v| ≤ |u| + |v|) ∧ |(0 : ℝ)| = 0 ∧
    Composite.Run f c abs settings (fun _ : Fin 1 => 1 / 4) data 1 ∧
    settings.eta1 ≤ data.ratio 0 ∧
    max settings.sigmaInitial
      (settings.gamma3 * (1 + 1 * 1) / (1 - settings.eta2)) = 24 ∧
    settings.sigmaMin / (2 : ℕ).factorial *
      ((1 - settings.theta) / (3 * (1 : ℕ).factorial * (1 + (24 : ℝ)))) ^ 2 =
        1 / 90000 ∧
    f 0 + |c 0| - (f 1 + |c 1|) = 1 / 2 ∧ f 0 - f 1 = -(1 / 2) ∧
    ¬settings.eta1 * (1 / 90000 : ℝ) * (1 / 4 : ℝ) ^ 2 ≤
      f (data.point 0) - f (data.point 1) :=
  Composite.FunctionDecreaseCounterexample.verified_counterexample

end CartisGouldToint


namespace CartisGouldToint
open Composite.MissingAccuracyCounterexample
/-- **Counterexample to Lemma14.1.8's literal general branch.** The nonconvex,
unit Lipschitz, subadditive outer function is min(abs(t),1); the residual is
zero and the smooth objective is x^2/2. The actual accepted global-model step
has ratio3/4 and remains truly nonterminal at its endpoint. Unit solved radii
satisfy the source radius policy, but the printed accuracy-independent step
floor is violated. The alternative OCR reading of 3j! as (3j)! also fails. -/
theorem lemma_14_1_8_counterexample :
    let f := HighOrderRegularization.ObstructionCounterexample.objective
    let c := fun _ : ℝ => (0 : ℝ)
    let h := Composite.TruncatedAbs.h
    LipschitzWith 1 h ∧ (∀ x y, h (x+y) ≤ h x+h y) ∧ h 0 = 0 ∧ h 1 ≠ 0 ∧
      ¬ConvexOn ℝ Set.univ h ∧
      (ContDiff ℝ 1 f ∧ ContDiff ℝ 1 c ∧
        (∀ x y, ‖iteratedFDeriv ℝ 1 f x - iteratedFDeriv ℝ 1 f y‖ ≤ 1*‖x-y‖) ∧
        (∀ x y, ‖iteratedFDeriv ℝ 1 c x - iteratedFDeriv ℝ 1 c y‖ ≤ 1*‖x-y‖) ∧
        ∀ x, 0 ≤ f x+h 0) ∧
      Composite.Run f c h settings (fun _ : Fin 1 => epsilon) data 1 ∧
      settings.eta1 ≤ data.ratio 0 ∧
      ¬Composite.TargetAt f c h settings (fun _ : Fin 1 => epsilon) data 1 ∧
      (∀ k a, data.solvedRadius k a = 1) ∧
      (∀ k a, printedRadiusCoefficient*epsilon ≤ data.solvedRadius k a) ∧
      (printedCap = 24 ∧ printedRadiusCoefficient = 1/480 ∧ printedStepFloor = 1/74880) ∧
      ‖data.step 0‖ < printedStepFloor ∧
      ‖data.step 0‖ < ((1-settings.theta)*printedRadiusCoefficient^1 /
        (((3*1 : ℕ).factorial : ℝ)*((1+1)+printedCap))) ^ ((1 : ℝ)/(1-1+1)) := by
  dsimp only
  exact ⟨Composite.TruncatedAbs.lipschitz,Composite.TruncatedAbs.subadditive,
    Composite.TruncatedAbs.zero,by norm_num [Composite.TruncatedAbs.h],
    Composite.TruncatedAbs.not_convex,source_regularity,run,successful,not_target 1,
    fun _ _ => rfl,radius_floor,printed_constants,step_floor_violated,
    factorial_step_floor_violated⟩
end CartisGouldToint


namespace CartisGouldToint
open InexactTrustRegion
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {p q : ℕ} {f : E → ℝ} {c : E → F} {h : F → ℝ}
  {P : Composite.Settings p q} {ε : Fin q → ℝ} {D : Composite.ExecutionData E q} {N : ℕ}

/-- **Corrected general Lemma 14.1.8.** The missing accuracy factor is retained.
The parameter cap is derived from the actual model ratios and updates. The
explicit positive step coefficient depends only on fixed settings and smoothness
constants, before all accuracies. Require failure of the next true certificate;
the first terminal success is charged separately in the full complexity theorem. -/
theorem lemma_14_1_8_corrected_general (hr : Composite.Run f c h P ε D N)
    (hf : ContDiff ℝ p f) (hc : ContDiff ℝ p c) {Lf Lc : ℝ} {K : NNReal}
    (hLf : 1 ≤ Lf) (hLc : 0 ≤ Lc) (hh : LipschitzWith K h)
    (hlipf : ∀ u v,
      ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ Lf * ‖u - v‖)
    (hlipc : ∀ u v,
      ‖iteratedFDeriv ℝ p c u - iteratedFDeriv ℝ p c v‖ ≤ Lc * ‖u - v‖)
    {k : ℕ} (hk : k < N) (haccepted : P.eta1 ≤ D.ratio k)
    (hfloor : ‖D.step k‖ < 1 → ∀ a,
      Composite.radiusCoefficient P (Lf + (K : ℝ) * Lc)
        (HighOrderRegularization.parameterCap P (Lf + (K : ℝ) * Lc)) * ε a ≤
          D.solvedRadius k a)
    (hn : ¬Composite.TargetAt f c h P ε D (k + 1)) :
    ∃ a : Fin q, Composite.stepCoefficient P (Lf + (K : ℝ) * Lc)
        (HighOrderRegularization.parameterCap P (Lf + (K : ℝ) * Lc)) ^ (q + 1) *
      ε a ^ (modelOrder a + 1) ≤ ‖D.step k‖ ^ (p + 1) := by
  exact hr.exists_power_lower hf hc hLf hLc
    (HighOrderRegularization.parameterCap_pos P (Lf + (K : ℝ) * Lc)).le hh
    hlipf hlipc hk haccepted
    (hr.parameter_le hf hc (zero_le_one.trans hLf) hLc hh hlipf hlipc hk.le)
    hfloor hn

/-- **Corrected unit-radius branch of Lemma 14.1.8.** A first-order unit-radius
policy gives the sharper power p before the next true certificate. The cap is
derived from the actual execution. Convexity of the outer function is unnecessary
for this implication once the actual unit-radius solver policy is imposed. -/
theorem lemma_14_1_8_corrected_convex (hr : Composite.Run f c h P ε D N) (hq : q = 1)
    (hf : ContDiff ℝ p f) (hc : ContDiff ℝ p c) {Lf Lc : ℝ} {K : NNReal}
    (hLf : 1 ≤ Lf) (hLc : 0 ≤ Lc) (hh : LipschitzWith K h)
    (hlipf : ∀ u v,
      ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ Lf * ‖u - v‖)
    (hlipc : ∀ u v,
      ‖iteratedFDeriv ℝ p c u - iteratedFDeriv ℝ p c v‖ ≤ Lc * ‖u - v‖)
    {k : ℕ} (hk : k < N) (haccepted : P.eta1 ≤ D.ratio k)
    (hunit : ∀ a, D.solvedRadius k a = 1)
    (hn : ¬Composite.TargetAt f c h P ε D (k + 1)) :
    ∃ a : Fin q, CompositeStep.coefficient P.theta
      (Lf + (K : ℝ) * Lc + HighOrderRegularization.parameterCap P (Lf + (K : ℝ) * Lc))
      (2 * (Lf + (K : ℝ) * Lc)) 1 * ε a ≤
        ‖D.step k‖ ^ p := by
  exact hr.exists_unit_power_lower hq hf hc hLf hLc
    (HighOrderRegularization.parameterCap_pos P (Lf + (K : ℝ) * Lc)).le hh
    hlipf hlipc hk haccepted
    (hr.parameter_le hf hc (zero_le_one.trans hLf) hLc hh hlipf hlipc hk.le)
    hunit hn

/-- **Corrected general Lemma 14.1.9.** The decrease concerns the full objective
w=f+h∘c, with the missing accuracy dependence and a coefficient fixed before
accuracies. A next-iterate nontermination hypothesis excludes the terminal
success, whose decrease can be arbitrarily small. -/
theorem lemma_14_1_9_corrected_general (hr : Composite.Run f c h P ε D N)
    (hf : ContDiff ℝ p f) (hc : ContDiff ℝ p c) {Lf Lc : ℝ} {K : NNReal}
    (hLf : 1 ≤ Lf) (hLc : 0 ≤ Lc) (hh : LipschitzWith K h)
    (hlipf : ∀ u v,
      ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ Lf * ‖u - v‖)
    (hlipc : ∀ u v,
      ‖iteratedFDeriv ℝ p c u - iteratedFDeriv ℝ p c v‖ ≤ Lc * ‖u - v‖)
    {k : ℕ} (hk : k < N) (haccepted : P.eta1 ≤ D.ratio k)
    (hfloor : ‖D.step k‖ < 1 → ∀ a,
      Composite.radiusCoefficient P (Lf + (K : ℝ) * Lc)
        (HighOrderRegularization.parameterCap P (Lf + (K : ℝ) * Lc)) * ε a ≤ D.solvedRadius k a)
    (hn : ¬Composite.TargetAt f c h P ε D (k + 1)) :
    Composite.generalDecreaseCoefficient P (Lf + (K : ℝ) * Lc)
        (HighOrderRegularization.parameterCap P (Lf + (K : ℝ) * Lc)) *
          Composite.generalAccuracyFactor P ε ≤
      f (D.point k) + h (c (D.point k)) -
        (f (D.point (k + 1)) + h (c (D.point (k + 1)))) := by
  exact hr.function_decrease_general hf hc hLf hLc hh hlipf hlipc
    hk haccepted hfloor hn

/-- **Corrected unit-radius branch of Lemma 14.1.9.** Actual first-order unit
radii retain the sharp (p+1)/p accuracy power for the full composite objective.
The fixed decrease coefficient and actual parameter cap precede accuracies.
The next true certificate must still fail. -/
theorem lemma_14_1_9_corrected_convex (hr : Composite.Run f c h P ε D N) (hq : q = 1)
    (hf : ContDiff ℝ p f) (hc : ContDiff ℝ p c) {Lf Lc : ℝ} {K : NNReal}
    (hLf : 1 ≤ Lf) (hLc : 0 ≤ Lc) (hh : LipschitzWith K h)
    (hlipf : ∀ u v,
      ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ Lf * ‖u - v‖)
    (hlipc : ∀ u v,
      ‖iteratedFDeriv ℝ p c u - iteratedFDeriv ℝ p c v‖ ≤ Lc * ‖u - v‖)
    {k : ℕ} (hk : k < N) (haccepted : P.eta1 ≤ D.ratio k)
    (hunit : ∀ a, D.solvedRadius k a = 1)
    (hn : ¬Composite.TargetAt f c h P ε D (k + 1)) :
    Composite.unitDecreaseCoefficient P (Lf + (K : ℝ) * Lc)
        (HighOrderRegularization.parameterCap P (Lf + (K : ℝ) * Lc)) *
          Composite.unitAccuracyFactor P ε ≤
      f (D.point k) + h (c (D.point k)) -
        (f (D.point (k + 1)) + h (c (D.point (k + 1)))) := by
  exact hr.function_decrease_unit hq hf hc hLf hLc hh hlipf hlipc
    hk haccepted hunit hn

end CartisGouldToint

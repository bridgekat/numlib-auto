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

Lemmas 14.1.2--14.1.4 use the smooth penalized scalar part and residual polynomial
for the model's genuine generalized Taylor criticality. They derive the exact
small-radius decrease, actual global-minimum step existence, quantitative radii,
and the objective optimality certified by a zero-decrease global-gap return.
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
    (x s : ℕ → E) (σ ρ : ℕ → ℝ) (η₁ η₂ γ₁ γ₂ γ₃ σmin : ℝ) (N : ℕ) : Prop :=
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

/-- **Lemma 14.1.4.** A zero-decrease Step2 return satisfying the actual
positive-fraction global-gap rule gives genuine approximate composite optimality
at positive radii. It cannot follow a failed Step1 test when q=1 and h is convex. -/
theorem lemma_14_1_4 {n m p q : ℕ} (hqp : q ≤ p)
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

end CartisGouldToint

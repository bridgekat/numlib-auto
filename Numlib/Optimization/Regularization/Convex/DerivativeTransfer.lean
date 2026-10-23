import Numlib.Optimization.Regularization.Convex.DerivativeRun

/-!
# Actual constrained derivative tests transferred to the objective

Small steps place the objective-restricted unit directions inside their actual
model counterparts. Sharp derivative errors then transfer every enabled model
test. Thus failure of a true endpoint test forces a genuinely large step at
one enabled order, without assuming direction-set containment or optimality.
-/

namespace TaylorModel
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Inclusion is needed only on unit directions for the actual tensor measure. -/
theorem tensorCriticality_le_of_unit_subset {j : ℕ} (T : E [×j]→L[ℝ] ℝ)
    {A B : Set E} (hA : (0 : E) ∈ A)
    (hAB : ∀ d ∈ A, ‖d‖ ≤ 1 → d ∈ B) :
    tensorCriticality T A ≤ tensorCriticality T B :=
  (tensorCriticality_le_iff T hA).mpr
    (fun d hd hn => neg_diagonal_le_tensorCriticality T (hAB d hd hn) hn)

end TaylorModel

namespace ConvexRegularization
open Set TaylorModel HighOrderRegularization
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Nonnegative objective restriction tolerances retain the zero direction at all orders. -/
theorem zero_mem_objectiveRestrictedDirections {f : E → ℝ} {C : Set E} {x : E}
    {a b : ℝ} (hx : x ∈ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (j : Fin 3) :
    (0 : E) ∈ objectiveRestrictedDirections f C x a b j := by
  have hz : (0 : E) ∈ feasibleDisplacements C x := by simpa using hx
  fin_cases j
  · exact hz
  · exact zero_mem_firstRestrictedDirections hz ha
  · exact zero_mem_secondRestrictedDirections hz ha hb

/-- The exact source small-step threshold for each enabled derivative order. -/
noncomputable def derivativeStepThreshold {p : ℕ} {q : Fin 3}
    (P : DerivativeSettings p q) (L : ℝ) (j : Fin 3) : ℝ :=
  (p - j.val).factorial * (1 - P.fractions j) / (L + parameterCap P.toSettings L)

end ConvexRegularization

namespace ConvexRegularization
open Set TaylorModel HighOrderRegularization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- At a genuine trial, all enabled small-step conditions imply all actual
endpoint objective tests. The direction containment is proved from genuine
lower derivative errors, including the source tau/theta margins. -/
theorem DerivativeRun.stop_of_small_step {p : ℕ} {q : Fin 3}
    {f : E → ℝ} {C S : Set E} {P : DerivativeSettings p q} {ε : Fin 3 → ℝ}
    {D : Data E} {N i : ℕ} (h : DerivativeRun f C P ε D N)
    (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C) (hf : ContDiffOn ℝ p f S)
    {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (hi : i < N)
    (hsmall : ∀ j ≤ q, ‖D.step i‖ ^ (p - j.val) ≤ derivativeStepThreshold P L j * ε j) :
    derivativeStop f C P ε (D.point i + D.step i) := by
  have hcap : D.parameter i ≤ parameterCap P.toSettings L := by
    have hh := h.modelTrace.parameter_le_on hS hCS hC hf hL hlip
      (fun k hk => h.mem hk.le) h.feasible_trial hi.le
    simpa only [parameterCap,h.initial_parameter] using hh
  have hpos := h.modelTrace.updates.pos hi.le
  have hne := h.modelTrace.step_ne_zero hi
  have hden : 0 < L + parameterCap P.toSettings L :=
    add_pos_of_nonneg_of_pos hL (hpos.trans_le hcap)
  have herr : ∀ j ≤ q,
      ‖iteratedFDeriv ℝ (j.val + 1) f (D.point i + D.step i) -
        iteratedFDeriv ℝ (j.val + 1)
          (model f p (D.point i) (D.parameter i)) (D.step i)‖ ≤
      (1 - P.fractions j) * ε j := by
    intro j hj
    have hjp : j.val + 1 ≤ p := by
      have := Fin.le_iff_val_le_val.mp hj; have := P.enabled_order; omega
    have he := norm_model_derivative_error_le_on hjp hS hCS hC hf hL hpos.le hlip
      (h.mem hi.le) (h.feasible_trial i hi) hne
    rw [show p - (j.val + 1) + 1 = p - j.val by omega] at he
    have hc : (L + D.parameter i) / (p - j.val).factorial * ‖D.step i‖^(p - j.val) ≤
        (L + parameterCap P.toSettings L) / (p - j.val).factorial * ‖D.step i‖^(p - j.val) := by
      gcongr
    have hb := mul_le_mul_of_nonneg_left (hsmall j hj)
      (show 0 ≤ (L + parameterCap P.toSettings L) / (p - j.val).factorial by positivity)
    have heq : (L + parameterCap P.toSettings L) / (p - j.val).factorial *
        (derivativeStepThreshold P L j * ε j) = (1 - P.fractions j) * ε j := by
      unfold derivativeStepThreshold
      field_simp
    rw [heq] at hb
    exact he.trans (hc.trans hb)
  have hfirst : ∀ d ∈ firstRestrictedDirections f
      (feasibleDisplacements C (D.point i + D.step i)) (D.point i + D.step i) (P.tau * ε 0),
      ‖d‖ ≤ 1 → |fderiv ℝ (model f p (D.point i) (D.parameter i)) (D.step i) d| ≤
        P.fractions 0 * ε 0 := by
    intro d hd hn
    have he := (abs_diagonal_le_norm
      (iteratedFDeriv ℝ 1 f (D.point i + D.step i) -
        iteratedFDeriv ℝ 1 (model f p (D.point i) (D.parameter i)) (D.step i)) hn).trans
          (herr 0 (Fin.zero_le q))
    simp only [sub_apply,iteratedFDeriv_one_apply] at he
    have hθ : (1 - P.fractions 0) + P.tau ≤ P.fractions 0 := by
      change (1 - P.theta) + P.tau ≤ P.theta; linarith [P.theta_lower]
    have hh := mul_le_mul_of_nonneg_right hθ (h.accuracy_pos 0).le
    have hs := hd.2
    exact abs_le.mpr ⟨by linarith [(abs_le.mp he).2,(abs_le.mp hs).1],
      by linarith [(abs_le.mp he).1,(abs_le.mp hs).2]⟩
  have hsecond : 1 ≤ q.val → ∀ d ∈ secondRestrictedDirections f
      (feasibleDisplacements C (D.point i + D.step i)) (D.point i + D.step i)
      (P.tau * ε 0) (P.tauTwo * ε 1), ‖d‖ ≤ 1 →
      |iteratedFDeriv ℝ 2 (model f p (D.point i) (D.parameter i)) (D.step i)
        (fun _ => d)| ≤ P.fractions 1 * ε 1 := by
    intro hq d hd hn
    have he := (abs_diagonal_le_norm
      (iteratedFDeriv ℝ 2 f (D.point i + D.step i) -
        iteratedFDeriv ℝ 2 (model f p (D.point i) (D.parameter i)) (D.step i)) hn).trans
          (herr 1 (by exact hq))
    simp only [sub_apply] at he
    have hθ : (1 - P.fractions 1) + P.tauTwo ≤ P.fractions 1 := by
      change (1 - P.thetaTwo) + P.tauTwo ≤ P.thetaTwo; linarith [P.thetaTwo_lower]
    have hh := mul_le_mul_of_nonneg_right hθ (h.accuracy_pos 1).le
    have hs := hd.2
    exact abs_le.mpr ⟨by linarith [(abs_le.mp he).2,(abs_le.mp hs).1],
      by linarith [(abs_le.mp he).1,(abs_le.mp hs).2]⟩
  intro j hj
  have hz := zero_mem_objectiveRestrictedDirections (f := f) (h.feasible_trial i hi)
    (mul_pos P.tau_pos (h.accuracy_pos 0)).le
    (mul_pos P.tauTwo_pos (h.accuracy_pos 1)).le j
  have he := tensorCriticality_le_of_error _ _ hz (herr j hj)
  have hm := tensorCriticality_le_of_unit_subset
    (iteratedFDeriv ℝ (j.val + 1) (model f p (D.point i) (D.parameter i)) (D.step i)) hz
    (B := modelRestrictedDirections f p C (D.point i) (D.parameter i) (D.step i)
      (P.fractions 0 * ε 0) (P.fractions 1 * ε 1) j) (by
        intro d hd hn
        fin_cases j
        · exact hd
        · exact ⟨hd.1,hfirst d hd hn⟩
        · exact ⟨⟨hd.1.1,hfirst d hd.1 hn⟩,hsecond (by
            exact (by decide : 1 ≤ 2).trans hj) d hd hn⟩)
  have ht := h.model_test i hi j hj
  change objectiveDerivativeCriticality f C (D.point i + D.step i)
    (P.tau * ε 0) (P.tauTwo * ε 1) j ≤ ε j
  change tensorCriticality _ _ ≤ _
  change tensorCriticality _ _ ≤ _ at ht
  linarith

/-- An actual nonterminal accepted endpoint forces a strict step threshold
at at least one enabled derivative order. -/
theorem DerivativeRun.exists_large_step {p : ℕ} {q : Fin 3}
    {f : E → ℝ} {C S : Set E} {P : DerivativeSettings p q} {ε : Fin 3 → ℝ}
    {D : Data E} {N i : ℕ} (h : DerivativeRun f C P ε D N)
    (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C) (hf : ContDiffOn ℝ p f S)
    {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (hi : i + 1 < N) (hs : P.eta1 ≤ D.ratio i) :
    ∃ j ≤ q, derivativeStepThreshold P L j * ε j < ‖D.step i‖^(p - j.val) := by
  by_contra hn
  have hb : ∀ j ≤ q, ‖D.step i‖^(p - j.val) ≤ derivativeStepThreshold P L j * ε j := by
    intro j hj
    exact le_of_not_gt (fun hlt => hn ⟨j,hj,hlt⟩)
  have ht := h.stop_of_small_step hS hCS hC hf hL hlip (by omega) hb
  rw [←h.modelTrace.successful_point (by omega) hs] at ht
  exact h.continues (i + 1) hi ht

end ConvexRegularization

import NumlibSurface.CartisGouldToint.Chapter14.Section01.ARqpCInnerDecrease
import Numlib.Optimization.CompositeInnerReturn

/-!
# Chapter 14, Section 1: actual finite inner step existence

The actual composite model attains its minimum by radial domination. Legal exact-minimum
choices followed by finite pass/halving transitions construct a returned detailed execution.
Only the certified convex first radius is protected. All other orders, including the first
nonconvex order, retain the displayed source radius floor.
-/

noncomputable section
open scoped Nat NNReal
namespace CartisGouldToint.Chapter14.Section01
open Optimization CompositeTaylorModels CompositeRegularization
open HigherOrderApproximateRegularization (Parameters InnerState InnerInitial accuracyTarget
  accuracyTarget_bounds radiusFloor)

/-- The inherited source condition f.D1pL requires scalar derivative constants at least one.
The bundled composite problem's weaker nonnegative constants suffice for earlier results. -/
theorem CompositeProblem.one_le_derivativeConstant {n m p : ℕ} (C : CompositeProblem n m p)
    (hp : 1 ≤ p) (hLf : ∀ j ∈ Finset.Icc 1 p, (1 : ℝ) ≤ C.Lf j) :
    1 ≤ C.derivativeConstant := by
  have hf := (hLf 1 (Finset.mem_Icc.mpr ⟨le_rfl, hp⟩)).trans
    (HigherOrderDerivativeFamily.le_maxConstant (fun j => (C.Lf j : ℝ)) le_rfl hp)
  have hc : 0 ≤ C.componentConstant := (C.Lc 1).coe_nonneg.trans
    (HigherOrderDerivativeFamily.le_maxConstant (fun j => (C.Lc j : ℝ)) le_rfl hp)
  dsimp [CompositeProblem.derivativeConstant]
  have hterm : 0 ≤ Real.sqrt m * C.h.constant * C.componentConstant := by positivity
  change 1 ≤ C.scalarConstant at hf
  linarith only [hf, hterm]

/-- The analytic small-radius property of the actual composite model is Lemma 14.1.2. -/
theorem CompositeProblem.smallRadiusDecrease {n m : ℕ} (P : Parameters)
    (C : CompositeProblem n m P.p)
    (hLf : ∀ j ∈ Finset.Icc 1 P.p, (1 : ℝ) ≤ C.Lf j)
    (x : EuclideanSpace ℝ (Fin n)) {σ : ℝ} (hσ : 0 < σ) :
    CompositeRegularization.SmallRadiusDecrease P (smoothModel C.f P.p x σ)
      (vectorModel C.c P.p x) C.h (3 * C.derivativeConstant + σ) := by
  have hL := C.one_le_derivativeConstant (P.order_pos.trans P.order_le) hLf
  have hden : 0 < 4 * (3 * C.derivativeConstant + σ) := by positivity
  intro s hs j hj hjq δ hδ hδ1 hsmall d hd htarget
  have he := lemma_14_1_2 C hj hjq P.order_le x s d hs hσ
    (accuracyTarget_bounds P hj hjq).1 hδ
    (le_min hδ1 ((le_div_iff₀ hden).mpr (by nlinarith only [hsmall]))) hd htarget
  have heq : ∀ t, CompositeRegularization.objective
      (smoothModel C.f P.p x σ) (vectorModel C.c P.p x) C.h t =
      compositeRegularizedModel C.f C.c C.h P.p x σ t := by
    intro t
    dsimp [CompositeRegularization.objective, smoothModel, vectorModel, compositeRegularizedModel,
      CompositeTaylorModels.regularizedModel, model]
    ring
  simpa only [heq] using he

/-- Lemma 14.1.3: a legal pair is returned by an actual initialized finite detailed inner
execution. The source strict long boundary, certified unit convex first radius and every
quantitative affected-order floor hold. A strict model decrease is nonzero; zero is permitted
when the model is already minimized at zero. The requested initial fraction is preserved. -/
theorem lemma_14_1_3 {n m : ℕ} (P : Parameters) (C : CompositeProblem n m P.p)
    (hLf : ∀ j ∈ Finset.Icc 1 P.p, (1 : ℝ) ≤ C.Lf j)
    (x : EuclideanSpace ℝ (Fin n)) {σ μ : ℝ} (hσ : 0 < σ)
    (hμ : 0 < μ) (hμ1 : μ < 1) (convex : Bool)
    (hconv : convex = true → ConvexOn ℝ Set.univ C.h) :
    ∃ z N, ∃ run : algorithm_14_1_2 P C x σ convex hconv z N,
      (run.state 0).mu = μ ∧ (run.state N).phase = .returned ∧
      let s := (run.state N).step
      let δ := (run.state N).radii
      HigherOrderApproximateRegularization.ValidRadii P δ ∧
      compositeRegularizedModel C.f C.c C.h P.p x σ s ≤
        compositeRegularizedModel C.f C.c C.h P.p x σ 0 ∧
      (1 < ‖s‖ ∨ ∀ j, 1 ≤ j → j ≤ P.q → ∃ d,
        GapWitness (smoothModel C.f P.p x σ) (vectorModel C.c P.p x) C.h
          j s (δ j) P.fraction d ∧ modelDecrement C.f C.c C.h P.p j x σ s d ≤
            P.fraction * P.theta * P.epsilon j * δ j ^ j / (j ! : ℝ)) ∧
      (convex = true → δ 1 = 1) ∧
      (‖s‖ ≤ 1 → ∀ j, 1 ≤ j → j ≤ P.q → 2 ≤ j ∨ convex = false →
        P.fraction * P.theta / (8 * (3 * C.derivativeConstant + σ)) * P.epsilon j ≤ δ j) ∧
      ((∃ t, compositeRegularizedModel C.f C.c C.h P.p x σ t <
          compositeRegularizedModel C.f C.c C.h P.p x σ 0) → s ≠ 0) := by
  classical
  let g := smoothModel C.f P.p x σ
  let v := vectorModel C.c P.p x
  let w := CompositeRegularization.objective g v C.h
  have heq : ∀ t, w t = compositeRegularizedModel C.f C.c C.h P.p x σ t := by
    intro t
    dsimp [w, g, v, CompositeRegularization.objective, smoothModel, vectorModel,
      compositeRegularizedModel,
      CompositeTaylorModels.regularizedModel, model]
    ring
  obtain ⟨z₀, hz₀⟩ := exists_regularizedModel_minimizer C.f C.c C.h P.p x hσ
  have hz₀' : ∀ t, w z₀ ≤ w t := by simpa only [heq, compositeRegularizedModel] using hz₀
  let z := if w 0 = w z₀ then 0 else z₀
  have hz : ∀ t, w z ≤ w t := by
    intro t
    dsimp [z]
    split_ifs with he
    · rw [he]
      exact hz₀' t
    · exact hz₀' t
  have hboundary : ‖z‖ = 1 → w z < w 0 := by
    intro hnorm
    have hne : w 0 ≠ w z₀ := by
      intro he
      simp only [z, he, ite_true, norm_zero] at hnorm
      norm_num at hnorm
    simpa only [z, ite_eq_right hne] using lt_of_le_of_ne (hz₀' 0) (Ne.symm hne)
  have hg : ContDiff ℝ P.p g := by
    have he : g = HigherOrderRegularization.model C.f P.p x σ := by
      funext t
      exact smoothModel_eq_regularization C.f P.p x t σ
    rw [he]
    exact HigherOrderApproximateRegularization.contDiff_model C.f P.p x σ
  have hv : ContDiff ℝ P.p v := RegularizedTaylorModel.contDiff_taylorModel C.c P.p x P.p
  have hw : Continuous w := hg.continuous.add (C.h.lipschitz.continuous.comp hv.continuous)
  have hL := C.one_le_derivativeConstant (P.order_pos.trans P.order_le) hLf
  have hM : 1 ≤ 3 * C.derivativeConstant + σ := by linarith
  let a : InnerState (EuclideanSpace ℝ (Fin n)) := ⟨μ, fun _ => 1, 0, .minimize⟩
  have ha : InnerInitial a := ⟨hμ, hμ1.le, rfl, rfl⟩
  obtain ⟨N, run, hzero, hstop, hnorm⟩ := CompositeRegularization.exists_inner_return_execution P
    C.h.lipschitz hw
    (hg.differentiable (by exact_mod_cast (show P.p ≠ 0 by
      have := P.order_pos.trans P.order_le; omega))).differentiableAt
    (hv.differentiable (by exact_mod_cast (show P.p ≠ 0 by
      have := P.order_pos.trans P.order_le; omega))).differentiableAt
    hz hboundary hconv hM (C.smallRadiusDecrease P hLf x hσ) ha hμ1
  have hbound := run.bounds hM (C.smallRadiusDecrease P hLf x hσ) le_rfl
  have hfrac := run.fraction_of_ne_minimize le_rfl (by rw [hstop]; decide)
  have hnonincrease := HigherOrderApproximateRegularization.model_nonincrease_of_fraction
    hz (run.mu_bounds le_rfl).1.le hfrac
  refine ⟨z, N, run, by rw [hzero], hstop, hbound.radii_valid, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [← heq] using hnonincrease
  · exact (run.return_quality hstop).imp_left (fun hs => lt_of_le_of_ne hs (Ne.symm hnorm))
  · intro hc
    cases convex with
    | false => cases hc
    | true => exact run.convex_first_radius le_rfl
  · intro _ j hj hjq _
    have hf := hbound.radii_floor j hj hjq
    dsimp [radiusFloor, accuracyTarget] at hf
    convert hf using 1
    ring
  · rintro ⟨t, ht⟩ hstep
    have ht' : w t < w 0 := by simpa only [heq] using ht
    have hzstrict : w z < w 0 := (hz t).trans_lt ht'
    have hp : 0 < (run.state N).mu := (run.mu_bounds le_rfl).1
    rw [hstep] at hfrac
    have hh : 0 < (run.state N).mu * (w 0 - w z) := mul_pos hp (sub_pos.mpr hzstrict)
    change (run.state N).mu * (w 0 - w z) ≤ w 0 - w 0 at hfrac
    linarith only [hh, hfrac]

end CartisGouldToint.Chapter14.Section01

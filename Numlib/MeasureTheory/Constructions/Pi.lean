/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.MeasureTheory.Constructions.Pi` (the Fubini step `ℝ^{j+1} = ℝ × ℝ^j` and
the measurability of `Fin.cons`), `Mathlib.Data.Fin.Tuple.Basic` (the `succAbove` identities).
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Lebesgue integrals over `ℝ^{j+1}` as iterated integrals

The one-coordinate Fubini step behind Gagliardo's product lemma
(`Numlib/Analysis/Sobolev/Embedding`): an integral over `Fin (j + 1) → ℝ` is the integral over
the first coordinate of the integral over the remaining `j`, the point being read as
`Fin.cons s t` (`MeasureTheory.lintegral_fin_succ_eq'`); the integral over `ℝ^0` is evaluation at
the unique point (`MeasureTheory.lintegral_fin_zero`). With it the measurability of `Fin.cons`
and of the omission of a coordinate, and two identities on `Fin.succAbove`.
-/

open MeasureTheory
open scoped ENNReal

/-- Omitting the coordinate `succ j` from `x : Fin (n + 2) → α` keeps `x 0` in front:
`x ∘ (succ j).succAbove = Fin.cons (x 0) ((x ∘ succ) ∘ j.succAbove)`. -/
theorem Fin.comp_succ_succAbove {n : ℕ} {α : Type*} (x : Fin (n + 2) → α) (j : Fin (n + 1)) :
    x ∘ (Fin.succ j).succAbove = Fin.cons (x 0) ((x ∘ Fin.succ) ∘ j.succAbove) := by
  ext k
  refine Fin.cases ?_ (fun k ↦ ?_) k
  · simp
  · simp [Fin.succ_succAbove_succ]

/-- Omitting the coordinate `0` from `x : Fin (n + 1) → α` is `x ∘ succ`. -/
theorem Fin.comp_zero_succAbove {n : ℕ} {α : Type*} (x : Fin (n + 1) → α) :
    x ∘ (0 : Fin (n + 1)).succAbove = x ∘ Fin.succ := by
  ext k
  simp

/-- `Fin.cons` is measurable in the pair `(head, tail)`. -/
theorem measurable_fin_cons_prod {m : ℕ} :
    Measurable fun p : ℝ × (Fin m → ℝ) ↦ (Fin.cons p.1 p.2 : Fin (m + 1) → ℝ) := by
  refine Measurable.of_eval fun k ↦ ?_
  refine Fin.cases ?_ (fun k ↦ ?_) k
  · simp only [Fin.cons_zero]
    exact measurable_fst
  · simp only [Fin.cons_succ]
    exact (measurable_pi_apply k).comp measurable_snd

/-- `Fin.cons s` is measurable for a fixed head `s`. -/
theorem measurable_fin_cons_const {m : ℕ} (s : ℝ) :
    Measurable fun t : Fin m → ℝ ↦ (Fin.cons s t : Fin (m + 1) → ℝ) :=
  measurable_fin_cons_prod.comp (measurable_const.prodMk measurable_id)

/-- Omitting a coordinate is measurable. -/
theorem measurable_comp_succAbove {m : ℕ} (i : Fin (m + 1)) :
    Measurable fun x : Fin (m + 1) → ℝ ↦ x ∘ i.succAbove :=
  Measurable.of_eval fun _ ↦ measurable_pi_apply _

/-- **Fubini for one more coordinate, the first coordinate outermost**: an integral over
`ℝ^{j+1}` is the integral over the first coordinate of the integral over the last `j`, the
coordinates being read as `Fin.cons s t`. -/
theorem MeasureTheory.lintegral_fin_succ_eq' {j : ℕ} {H : (Fin (j + 1) → ℝ) → ℝ≥0∞}
    (hH : Measurable H) :
    ∫⁻ y, H y = ∫⁻ s : ℝ, ∫⁻ t : Fin j → ℝ, H (Fin.cons s t) := by
  have hmp := (volume_preserving_piFinSuccAbove (fun _ : Fin (j + 1) ↦ ℝ) 0).symm
  rw [← hmp.lintegral_comp hH, Measure.volume_eq_prod,
    lintegral_prod (fun a : ℝ × (Fin j → ℝ) ↦
      H ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (j + 1) ↦ ℝ) 0).symm a))
      (hH.comp hmp.measurable).aemeasurable]
  refine lintegral_congr fun s ↦ lintegral_congr fun t ↦ ?_
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero]
  rfl

/-- The integral over `ℝ^0` is evaluation at the unique point. -/
theorem MeasureTheory.lintegral_fin_zero (H : (Fin 0 → ℝ) → ℝ≥0∞) :
    ∫⁻ t : Fin 0 → ℝ, H t = H (Fin.elim0) := by
  rw [volume_pi, Measure.pi_of_empty, lintegral_dirac]
  exact congrArg H (funext fun k ↦ k.elim0)

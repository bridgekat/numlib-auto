/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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
# Lebesgue integrals over $\mathbb{R}^{j+1}$ as iterated integrals

This file proves the one-coordinate Fubini step behind Gagliardo's product lemma in
`Numlib.Analysis.Sobolev.Embedding`. A point of $\mathbb{R}^{j+1}$ is written as $(s, t)$ with
$s \in \mathbb{R}$ the first coordinate and $t \in \mathbb{R}^j$ the remaining ones. The lower
Lebesgue integral of a measurable function $H \colon \mathbb{R}^{j+1} \to [0, \infty]$ is then the
iterated integral over $s$ and $t$, in either order. The integral over $\mathbb{R}^0$ is the value
at the unique point. The file also proves the measurability of the maps that prepend or omit a
coordinate, and two identities for the omission of a coordinate from a tuple.

## Main results

* `MeasureTheory.lintegral_fin_succ_eq'`: $\int_{\mathbb{R}^{j+1}} H = \int_{\mathbb{R}}
  \int_{\mathbb{R}^j} H(s, t) \, dt \, ds$.
* `MeasureTheory.lintegral_fin_succ_eq`: $\int_{\mathbb{R}^{j+1}} H = \int_{\mathbb{R}^j}
  \int_{\mathbb{R}} H(s, t) \, ds \, dt$.
* `MeasureTheory.lintegral_fin_zero`: the integral over $\mathbb{R}^0$ is the value at the unique
  point.
* `measurable_fin_cons_prod`: the map $\mathbb{R} \times \mathbb{R}^m \to \mathbb{R}^{m+1}$,
  $(s, t) \mapsto (s, t_0, \dots, t_{m-1})$, is measurable.
* `measurable_comp_succAbove`: the omission of a coordinate is a measurable map
  $\mathbb{R}^{m+1} \to \mathbb{R}^m$.

## Implementation notes

* The space $\mathbb{R}^{j}$ is `Fin j → ℝ` with the product Lebesgue measure `volume`. The point
  $(s, t)$ is `Fin.cons s t`.
* The omission of the coordinate $i$ from $x$ is `x ∘ i.succAbove`.
-/

open MeasureTheory
open scoped ENNReal

/-- Let $x = (x_0, \dots, x_{n+1})$ be a tuple of $n + 2$ elements of a type $\alpha$, and let
$j \in \{0, \dots, n\}$. Omitting the coordinate $j + 1$ from $x$ gives the tuple that starts
with $x_0$ and continues with $(x_1, \dots, x_{n+1})$ with its coordinate $j$ omitted.

In Lean, the statement is `x ∘ (Fin.succ j).succAbove = Fin.cons (x 0) ((x ∘ Fin.succ) ∘
j.succAbove)`. -/
theorem Fin.comp_succ_succAbove {n : ℕ} {α : Type*} (x : Fin (n + 2) → α) (j : Fin (n + 1)) :
    x ∘ (Fin.succ j).succAbove = Fin.cons (x 0) ((x ∘ Fin.succ) ∘ j.succAbove) := by
  ext k
  refine Fin.cases ?_ (fun k ↦ ?_) k
  · simp
  · simp [Fin.succ_succAbove_succ]

/-- Let $x = (x_0, \dots, x_n)$ be a tuple of $n + 1$ elements of a type $\alpha$. Omitting the
coordinate $0$ from $x$ gives $(x_1, \dots, x_n)$, that is,
`x ∘ (0 : Fin (n + 1)).succAbove = x ∘ Fin.succ`. -/
theorem Fin.comp_zero_succAbove {n : ℕ} {α : Type*} (x : Fin (n + 1) → α) :
    x ∘ (0 : Fin (n + 1)).succAbove = x ∘ Fin.succ := by
  ext k
  simp

/-- The map $\mathbb{R} \times \mathbb{R}^m \to \mathbb{R}^{m+1}$ that sends $(s, t)$ to the tuple
$(s, t_0, \dots, t_{m-1})$ is measurable. -/
theorem measurable_fin_cons_prod {m : ℕ} :
    Measurable fun p : ℝ × (Fin m → ℝ) ↦ (Fin.cons p.1 p.2 : Fin (m + 1) → ℝ) := by
  refine Measurable.of_eval fun k ↦ ?_
  refine Fin.cases ?_ (fun k ↦ ?_) k
  · simp only [Fin.cons_zero]
    exact measurable_fst
  · simp only [Fin.cons_succ]
    exact (measurable_pi_apply k).comp measurable_snd

/-- For a fixed $s \in \mathbb{R}$, the map $\mathbb{R}^m \to \mathbb{R}^{m+1}$ that sends $t$ to
the tuple $(s, t_0, \dots, t_{m-1})$ is measurable. -/
theorem measurable_fin_cons_const {m : ℕ} (s : ℝ) :
    Measurable fun t : Fin m → ℝ ↦ (Fin.cons s t : Fin (m + 1) → ℝ) :=
  measurable_fin_cons_prod.comp (measurable_const.prodMk measurable_id)

/-- For every coordinate $i \in \{0, \dots, m\}$, the map $\mathbb{R}^{m+1} \to \mathbb{R}^m$ that
omits the coordinate $i$ is measurable. -/
theorem measurable_comp_succAbove {m : ℕ} (i : Fin (m + 1)) :
    Measurable fun x : Fin (m + 1) → ℝ ↦ x ∘ i.succAbove :=
  Measurable.of_eval fun _ ↦ measurable_pi_apply _

/-- **Fubini's theorem for one more coordinate**, with the first coordinate outermost. Let
$H \colon \mathbb{R}^{j+1} \to [0, \infty]$ be measurable. Then
$$\int_{\mathbb{R}^{j+1}} H(y) \, dy = \int_{\mathbb{R}} \int_{\mathbb{R}^j} H(s, t) \, dt \,
  ds,$$
where $(s, t)$ is the point with first coordinate $s$ and remaining coordinates $t$.

The integrals are lower Lebesgue integrals for the product Lebesgue measures, and the point
$(s, t)$ is `Fin.cons s t`. -/
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

/-- **Fubini's theorem for one more coordinate**, with the last $j$ coordinates outermost. Let
$H \colon \mathbb{R}^{j+1} \to [0, \infty]$ be measurable. Then
$$\int_{\mathbb{R}^{j+1}} H(y) \, dy = \int_{\mathbb{R}^j} \int_{\mathbb{R}} H(s, t) \, ds \,
  dt,$$
where $(s, t)$ is the point with first coordinate $s$ and remaining coordinates $t$.

The integrals are lower Lebesgue integrals for the product Lebesgue measures, and the point
$(s, t)$ is `Fin.cons s t`. The proof is `MeasureTheory.lintegral_fin_succ_eq'` and Tonelli's
theorem. -/
theorem MeasureTheory.lintegral_fin_succ_eq {j : ℕ} {H : (Fin (j + 1) → ℝ) → ℝ≥0∞}
    (hH : Measurable H) :
    ∫⁻ y, H y = ∫⁻ t : Fin j → ℝ, ∫⁻ s : ℝ, H (Fin.cons s t) := by
  rw [lintegral_fin_succ_eq' hH]
  exact lintegral_lintegral_swap (hH.comp measurable_fin_cons_prod).aemeasurable

/-- For every function $H \colon \mathbb{R}^0 \to [0, \infty]$, the lower Lebesgue integral of $H$
over $\mathbb{R}^0$ is the value of $H$ at the unique point of $\mathbb{R}^0$. -/
theorem MeasureTheory.lintegral_fin_zero (H : (Fin 0 → ℝ) → ℝ≥0∞) :
    ∫⁻ t : Fin 0 → ℝ, H t = H (Fin.elim0) := by
  rw [volume_pi, Measure.pi_of_empty, lintegral_dirac]
  exact congrArg H (funext fun k ↦ k.elim0)

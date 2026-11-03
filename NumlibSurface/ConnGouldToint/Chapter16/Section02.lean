import Numlib.Optimization.EpigraphPenalty
import Mathlib.Order.Filter.Extr

/-! # Composite nonsmooth equations -/

namespace ConnGouldToint.Chapter16

/-- The exact merit function (16.2.23) for the composite objective `h ∘ c`. -/
def epigraphMerit {X Y : Type*} (c : X → Y) (h : Y → ℝ)
    (x : X) (σ t : ℝ) : ℝ :=
  Numlib.Optimization.epigraphPenalty (h (c x)) σ t

/-- Lemma 16.2.3. The minimum merit value over the epigraph variable is `h (c x)`,
and the set of minimizers is the singleton with that same value. -/
theorem lemma_16_2_3 {X Y : Type*} (c : X → Y) (h : Y → ℝ)
    (x : X) {σ : ℝ} (hσ : 1 < σ) :
    IsLeast (Set.range (epigraphMerit c h x σ)) (h (c x)) ∧
      {t | IsMinOn (epigraphMerit c h x σ) Set.univ t} = {h (c x)} := by
  have htight : epigraphMerit c h x σ (h (c x)) = h (c x) :=
    (Numlib.Optimization.epigraphPenalty_eq_iff hσ).2 rfl
  have hbound (t : ℝ) : h (c x) ≤ epigraphMerit c h x σ t :=
    Numlib.Optimization.le_epigraphPenalty hσ.le
  refine ⟨⟨⟨h (c x), htight⟩, ?_⟩, ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact hbound t
  · ext t
    change IsMinOn (epigraphMerit c h x σ) Set.univ t ↔ t = h (c x)
    constructor
    · intro hmin
      have hle := isMinOn_univ_iff.mp hmin (h (c x))
      rw [htight] at hle
      exact (Numlib.Optimization.epigraphPenalty_eq_iff hσ).1 (le_antisymm hle (hbound t))
    · rintro rfl
      apply isMinOn_univ_iff.mpr
      intro y
      rw [htight]
      exact hbound y

end ConnGouldToint.Chapter16

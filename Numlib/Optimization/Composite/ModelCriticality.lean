import Numlib.Optimization.Composite.ModelMinimum

/-!
# Actual composite model minimizers and quantitative criticality radii

Positive Taylor trials would improve a genuine model minimizer, so the sharp
retained-decrease theorem bounds its actual generalized criticality. Attaining
directions and explicit radii give the normalized solver tests and the source
radius floor. Convex outer functions permit a unit first-order radius.
-/

namespace Composite
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- At an actual model minimizer, every sufficiently small positive Taylor criticality
threshold strictly exceeds the genuine generalized criticality. -/
theorem criticality_lt_of_isMin_regularizedModel (f : E → ℝ) (c : E → F) {h : F → ℝ}
    {p j : ℕ} (hj : 0 < j) (hjp : j ≤ p) {Df Dc σ α δ : ℝ} {K : NNReal}
    (hDf : 0 ≤ Df) (hDc : 0 ≤ Dc) (hσ : 0 < σ) (hh : LipschitzWith K h)
    (x s : E) (hs : ‖s‖ ≤ 1)
    (hAf : ∀ a, 2 ≤ a → a ≤ p → ‖iteratedFDeriv ℝ a f x‖ ≤ Df)
    (hAc : ∀ a, 2 ≤ a → a ≤ p → ‖iteratedFDeriv ℝ a c x‖ ≤ Dc)
    (hmin : ∀ t, regularizedModel f c h p x σ s ≤ regularizedModel f c h p x σ t)
    (hα : 0 < α) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsmall : δ ≤ α / (4 * (3 * (Df + (K : ℝ) * Dc) + σ))) :
    criticality (smoothModel f p x σ) (residualModel c p x) h j s δ <
      α * δ ^ j / j.factorial := by
  obtain ⟨d, hd, he⟩ := exists_decrement_eq_criticality
    (smoothModel f p x σ) (residualModel c p x) hh.continuous j s hδ.le
  by_contra hn
  have htest : α * δ ^ j / j.factorial ≤
      decrement (smoothModel f p x σ) (residualModel c p x) h j s d :=
    by
      change α * δ ^ j / j.factorial ≤ _ - _
      rw [he]
      exact le_of_not_gt hn
  have hdec := regularizedModel_decrement_ge_half f c hj hjp hDf hDc hσ hh x s d hs
    hAf hAc hδ hδ1 hd hsmall htest
  have hp : 0 < α / 2 * δ ^ j / (j.factorial : ℝ) := by positivity
  linarith [hmin (s + d)]

/-- At an actual global model minimum, a convex outer function gives zero first-order
criticality at every radius. -/
theorem criticality_one_regularizedModel_eq_zero (f : E → ℝ) (c : E → F) {h : F → ℝ}
    {p : ℕ} (hp : 1 ≤ p) {σ : ℝ} {K : NNReal} (hh : LipschitzWith K h)
    (hconv : ConvexOn ℝ Set.univ h) (x s : E)
    (hmin : ∀ t, regularizedModel f c h p x σ s ≤ regularizedModel f c h p x σ t)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    criticality (smoothModel f p x σ) (residualModel c p x) h 1 s δ = 0 := by
  apply criticality_eq_zero_of_model_min _ _ _ _ _ hδ
  have hF : ContDiff ℝ 1 (smoothModel f p x σ) :=
    ModelDecrease.contDiff_penalized_ofJet _ p 1 hp σ
  have hC : ContDiff ℝ 1 (residualModel c p x) := TaylorModel.contDiff_eval c p x 1
  apply taylorModel_one_isMinOn_of_isMinOn (hF.differentiable (by norm_num)).differentiableAt
    (hC.differentiable (by norm_num)).differentiableAt hh hconv
  intro t ht
  change smoothModel f p x σ s + h (residualModel c p x s) ≤
    smoothModel f p x σ t + h (residualModel c p x t)
  simpa only [regularizedModel_eq] using hmin t

/-- A genuine global composite model minimizer admits all requested generalized
Taylor criticality tests with the exact source radius floor. -/
theorem exists_minimizer_with_criticality (f : E → ℝ) (c : E → F) {h : F → ℝ}
    {ι : Type*} (p : ℕ) (order : ι → ℕ) (horder : ∀ a, 0 < order a ∧ order a ≤ p)
    {Df Dc σ θ ζ : ℝ} {K : NNReal}
    (hDf : 1 ≤ Df) (hDc : 0 ≤ Dc) (hσ : 0 < σ) (hh : LipschitzWith K h)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (x : E) (ε : ι → ℝ) (hε : ∀ a, 0 < ε a ∧ ε a ≤ 1)
    (hAf : ∀ a, 2 ≤ a → a ≤ p → ‖iteratedFDeriv ℝ a f x‖ ≤ Df)
    (hAc : ∀ a, 2 ≤ a → a ≤ p → ‖iteratedFDeriv ℝ a c x‖ ≤ Dc) :
    ∃ (s : E) (δ : ι → ℝ) (d : ι → E),
      (∀ t, regularizedModel f c h p x σ s ≤ regularizedModel f c h p x σ t) ∧
      (∀ a, 0 < δ a ∧ δ a ≤ 1) ∧
      (∀ a, order a = 1 → ConvexOn ℝ Set.univ h → δ a = 1) ∧
      (∀ a, ζ * θ / (8 * (3 * (Df + (K : ℝ) * Dc) + σ)) * ε a ≤ δ a) ∧
      (‖s‖ ≤ 1 → ∀ a, ‖d a‖ ≤ δ a ∧
        ζ * criticality (smoothModel f p x σ) (residualModel c p x) h (order a) s (δ a) ≤
          decrement (smoothModel f p x σ) (residualModel c p x) h (order a) s (d a) ∧
        decrement (smoothModel f p x σ) (residualModel c p x) h (order a) s (d a) ≤
          ζ * θ * ε a * δ a ^ order a / (order a).factorial) := by
  classical
  let B := 3 * (Df + (K : ℝ) * Dc) + σ
  have hDf0 : 0 ≤ Df := le_trans zero_le_one hDf
  have hB : 3 ≤ B := by dsimp [B]; nlinarith [mul_nonneg K.coe_nonneg hDc]
  have hBpos : 0 < B := by linarith
  obtain ⟨s, hs⟩ := exists_minimizer_regularizedModel f c hh p x hσ
  have hdr : ∀ a, ∃ δ : ℝ, (0 < δ ∧ δ ≤ 1) ∧
      (order a = 1 → ConvexOn ℝ Set.univ h → δ = 1) ∧
      ζ * θ / (8 * B) * ε a ≤ δ ∧
      (‖s‖ ≤ 1 → criticality (smoothModel f p x σ) (residualModel c p x) h
        (order a) s δ ≤ ζ * θ * ε a * δ ^ order a / (order a).factorial) := by
    intro a
    have hεa := hε a
    have hα : 0 < ζ * θ * ε a := mul_pos (mul_pos hζ hθ) hεa.1
    have hα1 : ζ * θ * ε a ≤ 1 := by
      have hzt : ζ * θ ≤ 1 := (mul_le_of_le_one_left hθ.le hζ1).trans hθ1
      exact (mul_le_of_le_one_left hεa.1.le hzt).trans hεa.2
    have hfloor : ζ * θ / (8 * B) * ε a ≤ 1 := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (by positivity : 0 < 8 * B)).mpr
      nlinarith
    by_cases ha : order a = 1 ∧ ConvexOn ℝ Set.univ h
    · refine ⟨1, ⟨by norm_num, le_rfl⟩, fun _ _ => rfl, hfloor, ?_⟩
      intro hsn
      rw [ha.1, criticality_one_regularizedModel_eq_zero f c
        (ha.1 ▸ (horder a).2) hh ha.2 x s hs (by norm_num)]
      positivity
    · let r := ζ * θ * ε a / (4 * B)
      have hr : 0 < r := div_pos hα (by positivity)
      have hr1 : r ≤ 1 := (div_le_iff₀ (by positivity : 0 < 4 * B)).mpr (by linarith)
      refine ⟨r, ⟨hr, hr1⟩, fun h1 hc => (ha ⟨h1, hc⟩).elim, ?_, ?_⟩
      · dsimp [r]
        rw [div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_left hα.le (by positivity) (by linarith)
      · intro hsn
        exact (criticality_lt_of_isMin_regularizedModel f c (horder a).1 (horder a).2
          hDf0 hDc hσ hh x s hsn hAf hAc hs hα hr hr1 le_rfl).le
  choose δ hδ hone hfloor hcrit using hdr
  have hdir : ∀ a, ∃ d : E, ‖d‖ ≤ δ a ∧
      decrement (smoothModel f p x σ) (residualModel c p x) h (order a) s d =
        criticality (smoothModel f p x σ) (residualModel c p x) h (order a) s (δ a) := by
    intro a
    exact exists_decrement_eq_criticality _ _ hh.continuous _ _ (hδ a).1.le
  choose d hd he using hdir
  refine ⟨s, δ, d, hs, hδ, hone, hfloor, ?_⟩
  intro hsn a
  refine ⟨hd a, ?_, ?_⟩
  · rw [he a]
    exact mul_le_of_le_one_left (criticality_nonneg _ _ hh.continuous _ _ (hδ a).1.le) hζ1
  · rw [he a]
    exact hcrit a hsn
end Composite

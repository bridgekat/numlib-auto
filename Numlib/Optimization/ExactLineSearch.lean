import Numlib.Optimization.SmoothDescent

/-!
# Exact line minimization and gradient-descent iteration bounds

Exactness means a global minimum over the nonnegative ray, with arbitrary tie breaking.
The run relation only prescribes searches before the first successful gradient test; it does
not assume an exact ray minimizer exists for every bounded-below smooth objective. Comparing
any actual minimizer with the step `1/L` gives the sharp quadratic decrease and an iteration
budget. No bound is claimed for the internal oracle cost of exact line minimization.
-/
noncomputable section

namespace LineSearch
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A global objective minimizer along the nonnegative ray from `x` in direction `d`. -/
def IsExact (f : E → ℝ) (x d : E) (t : ℝ) : Prop :=
  0 ≤ t ∧ IsMinOn (fun a : ℝ => f (x + a • d)) (Set.Ici 0) t

/-- An exact ray step is nonnegative. -/
theorem IsExact.nonneg {f : E → ℝ} {x d : E} {t : ℝ} (h : IsExact f x d t) : 0 ≤ t := h.1

/-- An exact ray minimizer compares with every nonnegative trial. -/
theorem IsExact.le_trial {f : E → ℝ} {x d : E} {t : ℝ} (h : IsExact f x d t)
    {a : ℝ} (ha : 0 ≤ a) : f (x + t • d) ≤ f (x + a • d) := h.2 ha

/-- At zero direction every nonnegative step is an exact ray minimizer. -/
@[simp] theorem isExact_zero_iff (f : E → ℝ) (x : E) (t : ℝ) :
    IsExact f x 0 t ↔ 0 ≤ t := by
  constructor
  · exact IsExact.nonneg
  · intro ht
    exact ⟨ht, fun a _ => by simp⟩

/-- An interior exact ray minimizer has zero scalar line derivative. -/
theorem IsExact.deriv_eq_zero {f : E → ℝ} {x d : E} {t : ℝ}
    (h : IsExact f x d t) (ht : 0 < t) :
    deriv (fun a : ℝ => f (x + a • d)) t = 0 :=
  (h.2.isLocalMin (Ici_mem_nhds ht)).deriv_eq_zero

end LineSearch

namespace Optimization.SmoothDescent
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact negative-gradient line minimization gives the standard `1/(2L)` decrease. -/
theorem exactLineSearch_decrease {f : E → ℝ} {g : E → E} {L t : ℝ}
    (hf : ∀ y, HasFDerivAt f (innerSL ℝ (g y)) y)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLpos : 0 < L)
    {x : E} (h : _root_.LineSearch.IsExact f x (-g x) t) :
    ‖g x‖ ^ 2 / (2 * L) ≤ f x - f (x - t • g x) := by
  have hm := h.le_trial (a := 1 / L) (by positivity)
  simp only [smul_neg, ← sub_eq_add_neg] at hm
  have hd := gradient_step_upper_bound hf hL x (t := 1 / L) (by positivity)
  have he : -(1 / L) * ‖g x‖ ^ 2 + L / 2 * (1 / L) ^ 2 * ‖g x‖ ^ 2 =
      -(‖g x‖ ^ 2 / (2 * L)) := by field_simp; ring
  linarith [he]

/-- A nonstationary negative-gradient exact search has a strictly positive step. -/
theorem exactLineSearch_step_pos {f : E → ℝ} {g : E → E} {L t : ℝ}
    (hf : ∀ y, HasFDerivAt f (innerSL ℝ (g y)) y)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLpos : 0 < L)
    {x : E} (h : LineSearch.IsExact f x (-g x) t) (hg : g x ≠ 0) : 0 < t := by
  have hd := exactLineSearch_decrease hf hL hLpos h
  have hp : 0 < ‖g x‖ ^ 2 / (2 * L) := by positivity
  by_contra! ht
  have hz : t = 0 := le_antisymm ht h.nonneg
  simp only [hz, zero_smul, sub_zero, sub_self] at hd
  linarith

/-- At a positive exact line step, the new gradient is orthogonal to the search direction.
Only the objective derivative at the new point is needed. -/
theorem exactLineSearch_inner_eq_zero {f : E → ℝ} {x g₀ g₁ : E} {t : ℝ}
    (h : LineSearch.IsExact f x (-g₀) t) (ht : 0 < t)
    (hf : HasFDerivAt f (innerSL ℝ g₁) (x - t • g₀)) :
    inner ℝ g₀ g₁ = 0 := by
  have hline : HasDerivAt (fun a : ℝ => f (x + a • (-g₀)))
      ((innerSL ℝ g₁) (-g₀)) t := by
    have hf' : HasFDerivAt f (innerSL ℝ g₁) (x + t • (-g₀)) := by
      simpa only [smul_neg, ← sub_eq_add_neg] using hf
    have hcomp := hf'.comp_hasDerivAt t
      ((hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const (-g₀)))
    simpa only [Function.comp_def, Pi.add_apply, id_eq, one_smul, zero_add] using hcomp
  have hz := h.deriv_eq_zero ht
  rw [hline.deriv] at hz
  simpa only [innerSL_apply_apply, inner_neg_right, neg_eq_zero, real_inner_comm] using hz

/-- Actual exact searches and negative-gradient steps, only before the first successful test.
Existence of a global ray minimizer is part of a lawful search, not inferred from a lower bound. -/
structure IsExactSequence (f : E → ℝ) (g : E → E) (ε : ℝ)
    (x : ℕ → E) (t : ℕ → ℝ) : Prop where
  /-- Every executed line search uses an actual global ray minimizer. -/
  search : ∀ k, (∀ j ≤ k, ε < ‖g (x j)‖) → _root_.LineSearch.IsExact f (x k) (-g (x k)) (t k)
  /-- Executed iterations take their exact negative-gradient step. -/
  step : ∀ k, (∀ j ≤ k, ε < ‖g (x j)‖) → x (k + 1) = x k - t k • g (x k)

/-- Any lawful exact-search run reaches its first small gradient within the descent budget. -/
theorem exists_stationary_of_exactLineSearch {f : E → ℝ} {g : E → E} {L ε low : ℝ}
    (hf : ∀ y, HasFDerivAt f (innerSL ℝ (g y)) y)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLpos : 0 < L) (hε : 0 < ε)
    {x : ℕ → E} {t : ℕ → ℝ} (hseq : IsExactSequence f g ε x t)
    (hlow : ∀ k, low ≤ f (x k)) :
    ∃ K, ‖g (x K)‖ ≤ ε ∧ (∀ j < K, ε < ‖g (x j)‖) ∧
      (K : ℝ) ≤ 2 * L * ((f (x 0) - low) / ε ^ 2) := by
  have hδ : 0 < ε ^ 2 / (2 * L) := by positivity
  obtain ⟨K, hK, hstop, hfirst⟩ := EvaluationComplexity.exists_first_of_decrease
    (u := fun k => f (x k)) (P := fun k => ‖g (x k)‖ ≤ ε) hδ hlow (by
      intro k hfail
      have hp : ∀ j ≤ k, ε < ‖g (x j)‖ := fun j hj => lt_of_not_ge (hfail j hj)
      have hd := exactLineSearch_decrease hf hL hLpos (hseq.search k hp)
      rw [← hseq.step k hp] at hd
      have hs : ε ^ 2 ≤ ‖g (x k)‖ ^ 2 := by nlinarith [hp k le_rfl]
      exact (div_le_div_of_nonneg_right hs (by positivity)).trans hd)
  refine ⟨K, hstop, fun j hj => lt_of_not_ge (hfirst j hj), ?_⟩
  have hn : 0 ≤ (f (x 0) - low) / (ε ^ 2 / (2 * L)) := by
    exact div_nonneg (sub_nonneg.mpr (hlow 0)) hδ.le
  have hreal := (Nat.cast_le.mpr hK).trans (Nat.floor_le hn)
  have he : (f (x 0) - low) / (ε ^ 2 / (2 * L)) =
      2 * L * ((f (x 0) - low) / ε ^ 2) := by field_simp
  rwa [he] at hreal

end Optimization.SmoothDescent

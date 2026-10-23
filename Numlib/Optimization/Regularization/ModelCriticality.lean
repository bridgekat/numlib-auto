import Numlib.Optimization.Regularization.ModelMinimum
import Numlib.Analysis.Calculus.TaylorModel.Smooth
import Numlib.Analysis.InnerProductSpace.NormPow.Smoothness
import Numlib.Optimization.HighOrder.CriticalityLocalMin
import Mathlib.Tactic

/-!
# Actual critical global minimizers of regularized finite models

Finite tensor polynomials with a positive norm-power penalty have global
minimizers. Their actual finite smoothness gives positive optimality radii and
attaining Taylor-decrement directions for every requested derivative order.
The first two radii may equal one. No quantitative lower radius bound or
finite operational solver is assumed or asserted here.
-/

namespace ModelDecrease
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The actual norm-regularized finite tensor polynomial is globally `C^n`
for each `n ≤ p`, including at the origin. -/
theorem contDiff_penalized_ofJet (A : FormalMultilinearSeries ℝ E ℝ)
    (p n : ℕ) (hn : n ≤ p) (σ : ℝ) :
    ContDiff ℝ n (penalized (TaylorModel.ofJet A p) p σ) := by
  have hpow : ContDiff ℝ n (fun x : E => ‖x‖ ^ (p + 1)) := by
    have hnp : (n : ℝ) < ((p + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_of_le hn
    simpa only [Real.rpow_natCast] using
      (contDiff_normRpow_of_nat_lt (E := E) hnp)
  exact (TaylorModel.contDiff_ofJet A p n).add (contDiff_const.mul hpow)

variable {ι : Type*}

/-- An actual global model minimizer admits positive radii and attaining
Taylor-decrement directions satisfying every requested normalized criticality
test. First- and second-order radii equal one. The theorem derives the actual
model regularity and criticality, and supplies no quantitative radius floor. -/
theorem exists_minimizer_with_criticality_ofJet
    (A : FormalMultilinearSeries ℝ E ℝ) (p : ℕ) (order : ι → ℕ)
    (horder : ∀ a, 0 < order a ∧ order a ≤ p)
    {σ θ ζ : ℝ} (hσ : 0 < σ) (hθ : 0 < θ) (hζ : ζ ≤ 1)
    (ε : ι → ℝ) (hε : ∀ a, 0 < ε a) :
    ∃ (s : E) (δ : ι → ℝ) (d : ι → E),
      (∀ t : E, penalized (TaylorModel.ofJet A p) p σ s ≤
        penalized (TaylorModel.ofJet A p) p σ t) ∧
      (∀ a, 0 < δ a ∧ δ a ≤ 1) ∧
      (∀ a, order a ≤ 2 → δ a = 1) ∧
      (∀ a, ‖d a‖ ≤ δ a ∧
        ζ * TaylorModel.criticality (penalized (TaylorModel.ofJet A p) p σ)
          (order a) s (δ a) ≤
          TaylorModel.decrement (penalized (TaylorModel.ofJet A p) p σ) (order a) s (d a) ∧
        TaylorModel.decrement (penalized (TaylorModel.ofJet A p) p σ) (order a) s (d a) ≤
          θ * ε a * δ a ^ order a / (order a).factorial) := by
  let m := penalized (TaylorModel.ofJet A p) p σ
  obtain ⟨s, hs⟩ := exists_minimizer_ofJet A p hσ
  have hlocal : IsLocalMin m s := Filter.Eventually.of_forall hs
  have hδ : ∀ a : ι, ∃ δ : ℝ, (0 < δ ∧ δ ≤ 1) ∧
      (order a ≤ 2 → δ = 1) ∧
      TaylorModel.criticality m (order a) s δ ≤
        θ * ε a * δ ^ order a / (order a).factorial := by
    intro a
    have haj : order a ≤ p := (horder a).2
    have hf := contDiff_penalized_ofJet A p (order a) haj σ
    by_cases ha : order a ≤ 2
    · refine ⟨1, ⟨by norm_num, le_rfl⟩, fun _ => rfl, ?_⟩
      have hz : TaylorModel.criticality m (order a) s 1 = 0 := by
        have hap : 0 < order a := (horder a).1
        rcases (show order a = 1 ∨ order a = 2 by omega) with h1 | h2
        · rw [h1]
          exact TaylorModel.criticality_one_eq_zero_of_isLocalMin hlocal (by norm_num)
        · rw [h2] at hf ⊢
          exact TaylorModel.criticality_two_eq_zero_of_isLocalMin hf hlocal (by norm_num)
      rw [hz]
      exact div_nonneg (mul_nonneg (mul_nonneg hθ.le (hε a).le) (by positivity))
        (Nat.cast_nonneg _)
    · obtain ⟨r, hr, hbound⟩ := TaylorModel.exists_pos_criticality_le_mul_pow
        (horder a).1 hf hlocal
          (div_pos (mul_pos hθ (hε a)) (by positivity : (0 : ℝ) < (order a).factorial))
      refine ⟨min 1 (r / 2), ⟨lt_min (by norm_num) (half_pos hr), min_le_left _ _⟩,
        fun h => (ha h).elim, ?_⟩
      have hb := hbound (min 1 (r / 2))
        (le_min (by norm_num) (half_pos hr).le)
        ((min_le_right _ _).trans_lt (half_lt_self hr))
      convert hb using 1; ring
  choose δ hδ hsmall hbound using hδ
  have hmax : ∀ a : ι, ∃ d : E, ‖d‖ ≤ δ a ∧
      TaylorModel.decrement m (order a) s d =
        TaylorModel.criticality m (order a) s (δ a) :=
    fun a => TaylorModel.exists_decrement_eq_criticality m (order a) s (hδ a).1.le
  choose d hd hmax using hmax
  refine ⟨s, δ, d, hs, hδ, hsmall, fun a => ⟨hd a, ?_, ?_⟩⟩
  · rw [hmax a]
    exact mul_le_of_le_one_left (TaylorModel.criticality_nonneg m (order a) s (hδ a).1.le) hζ
  · rw [hmax a]
    exact hbound a

end ModelDecrease

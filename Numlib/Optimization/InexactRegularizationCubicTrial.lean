import Numlib.Optimization.InexactRegularizationCubicInspection

/-!
# Failed inspections of cubic supplied models

An endpoint cubic witness fails the computed test at every radius. While its quartic
regularizer dominates, the model-decrease test also fails and forces actual halvings.
At the final radius a positive model decrease retains the same endpoint for Step 2.
-/

noncomputable section
open scoped Nat
namespace Optimization.InexactRegularization
open InexactTaylorModels TaylorCriticality

/-- Endpoint witnesses give a legal failed cubic search when the regularizer dominates
at every preceding radius. -/
def cubicFailedSearch (a σ : ℝ) (N : ℕ) (ha : 1 / 32 < a)
    (hbefore : ∀ k < N, 4 * a ≤ σ * halvedRadius 1 k) :
    RadiusSearch 0 (cubicCoefficients a) 3 3 σ 1 (1 / 8) (1 / 2) N where
  direction := halvedRadius 1
  witness := by
    intro k hk
    have hw := cubicCoefficients_witness (by linarith : 0 ≤ a)
      (halvedRadius_pos (by norm_num : (0 : ℝ) < 1) k).le
    refine ⟨hw.feasible, ?_⟩
    have hn : 0 ≤ decrement (cubicCoefficients a) 3 (halvedRadius 1 k) := by
      rw [decrement_cubicCoefficients]
      have ha0 : 0 ≤ a := by linarith
      have hr := halvedRadius_pos (by norm_num : (0 : ℝ) < 1) k
      positivity
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_left hw.fraction_le (by norm_num : (0 : ℝ) ≤ 1 / 8)).trans
        (by simpa using mul_le_of_le_one_left hn (by norm_num : (1 / 8 : ℝ) ≤ 1))
  failed := by
    intro k hk
    have hr := halvedRadius_pos (by norm_num : (0 : ℝ) < 1) k
    have ht := hbefore k hk
    have hprod := mul_le_mul_of_nonneg_right ht (pow_nonneg hr.le 3)
    rw [decrement_cubicCoefficients, regularizedPolynomial_cubicCoefficients]
    norm_num only [Nat.factorial]
    constructor <;> nlinarith [pow_pos hr 3]

/-- A full failed cubic inspection retains the positive endpoint at its last radius. -/
def cubicFailedInspection (P : Parameters) (hp : P.p = 3) (hq : P.q = 3)
    (hv : P.fraction = 1 / 8) (hε : P.epsilon = fun _ => 1 / 2)
    (a σ : ℝ) (N : ℕ) (ha : 1 / 32 < a)
    (hbefore : ∀ k < N, 4 * a ≤ σ * halvedRadius 1 k)
    (hlast : (1 / 8 : ℝ) * (1 / 2) * halvedRadius 1 N ^ 3 / 24 ≤
      a * halvedRadius 1 N ^ 3 / 6 - σ * halvedRadius 1 N ^ 4 / 24) :
    Inspection P 0 (cubicCoefficients a) σ (fun _ => 1) where
  order := 3
  order_pos := by norm_num
  order_le := by rw [hq]; norm_num
  halvings := fun j => if j = 3 then N else 0
  search := by
    intro j hj hjq hjo
    by_cases he : j = 3
    · subst j
      simp only [ite_true]
      exact {
        direction := (cubicFailedSearch a σ N ha hbefore).direction
        witness := by simpa only [hv] using (cubicFailedSearch a σ N ha hbefore).witness
        failed := by simpa only [hp, hv, hε] using
          (cubicFailedSearch a σ N ha hbefore).failed }
    · have hj2 : j ≤ 2 := by omega
      simp only [ite_eq_right he]
      refine ⟨fun _ => 0, ?_, ?_⟩
      · intro k hk
        have hk0 : k = 0 := by omega
        subst k
        have heq : decrement (cubicCoefficients a) j = fun _ : ℝ => 0 := by
          funext d
          exact decrement_cubicCoefficients_low _ _ hj2
        refine ⟨by simp [halvedRadius], ?_⟩
        rw [heq]
        simp [gapOn]
      · intro k hk
        omega
  earlier := by
    intro j hj hjq hjo
    rw [decrement_cubicCoefficients_low _ _ (by omega)]
    have hεpos := P.epsilon_pos j hj hjq
    have hvpos := P.fraction_pos
    have hr := halvedRadius_pos (by norm_num : (0 : ℝ) < 1)
      ((fun j => if j = 3 then N else 0) j)
    positivity
  failed := by
    intro hq
    have hr := halvedRadius_pos (by norm_num : (0 : ℝ) < 1) N
    change P.fraction * P.epsilon 3 * halvedRadius 1 N ^ 3 / (2 * (3! : ℝ)) <
      decrement (cubicCoefficients a) 3 (halvedRadius 1 N)
    rw [decrement_cubicCoefficients, hv, hε]
    norm_num only [Nat.factorial]
    nlinarith [pow_pos hr 3]
  retained := by
    intro hq
    change P.fraction * P.epsilon 3 * halvedRadius 1 N ^ 3 / (4 * (3! : ℝ)) ≤
      0 - regularizedPolynomial 0 (cubicCoefficients a) P.p σ (halvedRadius 1 N)
    rw [hp, regularizedPolynomial_cubicCoefficients, hv, hε]
    norm_num only [Nat.factorial] at *
    linarith

/-- A failed cubic inspection changes only its third radius. -/
theorem cubicFailedInspection_radii (P : Parameters) (hp : P.p = 3) (hq : P.q = 3)
    (hv : P.fraction = 1 / 8) (hε : P.epsilon = fun _ => 1 / 2)
    (a σ : ℝ) (N : ℕ) (ha : 1 / 32 < a)
    (hbefore : ∀ k < N, 4 * a ≤ σ * halvedRadius 1 k)
    (hlast : (1 / 8 : ℝ) * (1 / 2) * halvedRadius 1 N ^ 3 / 24 ≤
      a * halvedRadius 1 N ^ 3 / 6 - σ * halvedRadius 1 N ^ 4 / 24) :
    (cubicFailedInspection P hp hq hv hε a σ N ha hbefore hlast).radii =
      fun j => if j = 3 then halvedRadius 1 N else 1 := by
  funext j
  by_cases hj : j = 3
  · subst j
    simp [Inspection.radii, cubicFailedInspection]
  · simp [Inspection.radii, cubicFailedInspection, hj, halvedRadius]

/-- The selected failed cubic witness is the final positive endpoint. -/
theorem cubicFailedInspection_direction (P : Parameters) (hp : P.p = 3) (hq : P.q = 3)
    (hv : P.fraction = 1 / 8) (hε : P.epsilon = fun _ => 1 / 2)
    (a σ : ℝ) (N : ℕ) (ha : 1 / 32 < a)
    (hbefore : ∀ k < N, 4 * a ≤ σ * halvedRadius 1 k)
    (hlast : (1 / 8 : ℝ) * (1 / 2) * halvedRadius 1 N ^ 3 / 24 ≤
      a * halvedRadius 1 N ^ 3 / 6 - σ * halvedRadius 1 N ^ 4 / 24) :
    (cubicFailedInspection P hp hq hv hε a σ N ha hbefore hlast).direction
      (by simpa only [cubicFailedInspection] using (by omega : 3 ≤ P.q)) =
        halvedRadius 1 N := by
  simp [Inspection.direction, cubicFailedInspection, cubicFailedSearch]

end Optimization.InexactRegularization

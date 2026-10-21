import Numlib.Optimization.InexactTaylorModels
import Numlib.Optimization.TaylorModelRemainder

/-!
# Taylor truncation errors with bounded omitted coefficients

A top-order value remainder and bounds on the omitted derivative tensors control every
lower truncation, for maps with values in a normed vector space. The factorial tail bound
is uniform on the unit ball.
-/

noncomputable section
open scoped Nat
namespace Optimization.RegularizedTaylorModel

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Splitting a Taylor polynomial isolates its actual omitted homogeneous terms. -/
theorem taylorModel_eq_truncation_add (f : E → F) {j p : ℕ} (hjp : j ≤ p) (x d : E) :
    taylorModel f p x d = taylorModel f j x d +
      ∑ i ∈ Finset.Icc (j + 1) p, (i ! : ℝ)⁻¹ • iteratedFDeriv ℝ i f x (fun _ => d) := by
  induction p, hjp using Nat.le_induction with
  | base => simp
  | succ p hp ih =>
    rw [taylorModel_succ, ih, Finset.sum_Icc_succ_top (by omega : j + 1 ≤ p + 1)]
    abel

/-- A top value remainder and bounded omitted coefficients control every lower Taylor
truncation with the exact factorial tail and no smoothness requirement on the codomain. -/
theorem norm_sub_taylorModel_le_of_tail {f : E → F} {p j : ℕ} {x d : E} {M δ : ℝ}
    (hjp : j ≤ p) (hM : 0 ≤ M) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (hd : ‖d‖ ≤ δ)
    (hb : ∀ i ∈ Finset.Icc (j + 1) p, ‖iteratedFDeriv ℝ i f x‖ ≤ M)
    (hr : ‖f (x + d) - taylorModel f p x d‖ ≤
      M * δ ^ (p + 1) / ((p + 1)! : ℝ)) :
    ‖f (x + d) - taylorModel f j x d‖ ≤ 2 * M * δ ^ (j + 1) / (j ! : ℝ) := by
  have hterm : ∀ i ∈ Finset.Icc (j + 1) p,
      ‖(i ! : ℝ)⁻¹ • iteratedFDeriv ℝ i f x (fun _ => d)‖ ≤
        M * δ ^ i / (i ! : ℝ) := by
    intro i hi
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (i ! : ℝ))]
    have hb' := (iteratedFDeriv ℝ i f x).le_opNorm (fun _ => d)
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hb'
    have hn := hb'.trans (mul_le_mul (hb i hi)
      (pow_le_pow_left₀ (norm_nonneg d) hd _) (pow_nonneg (norm_nonneg d) _) hM)
    simpa only [div_eq_inv_mul] using mul_le_mul_of_nonneg_left hn
      (by positivity : (0 : ℝ) ≤ (i ! : ℝ)⁻¹)
  have hsum := (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
  have htotal : (∑ i ∈ Finset.Icc (j + 1) p, M * δ ^ i / (i ! : ℝ)) +
      M * δ ^ (p + 1) / ((p + 1)! : ℝ) ≤ 2 * M * δ ^ (j + 1) / (j ! : ℝ) := by
    calc
      _ = M * ∑ i ∈ Finset.Icc (j + 1) (p + 1), δ ^ i / (i ! : ℝ) := by
        rw [Finset.sum_Icc_succ_top (by omega : j + 1 ≤ p + 1), mul_add, Finset.mul_sum]
        simp only [mul_div_assoc]
      _ ≤ M * (2 * δ ^ (j + 1) / (j ! : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hM
        have hset : Finset.Icc (j + 1) (p + 1) =
            (Finset.range (p + 2)).filter (j + 1 ≤ ·) := by
          ext i
          simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_range]
          omega
        rw [hset]
        exact Real.sum_tail_pow_div_factorial_le hδ j (p + 2)
      _ = _ := by ring
  calc
    _ = ‖(f (x + d) - taylorModel f p x d) +
        (taylorModel f p x d - taylorModel f j x d)‖ := by congr 1; abel
    _ ≤ ‖f (x + d) - taylorModel f p x d‖ +
        ‖taylorModel f p x d - taylorModel f j x d‖ := norm_add_le _ _
    _ ≤ M * δ ^ (p + 1) / ((p + 1)! : ℝ) +
        ∑ i ∈ Finset.Icc (j + 1) p, M * δ ^ i / (i ! : ℝ) := by
      apply add_le_add hr
      simpa only [taylorModel_eq_truncation_add f hjp x d, add_sub_cancel_left] using hsum
    _ ≤ _ := by linarith only [htotal]

end Optimization.RegularizedTaylorModel

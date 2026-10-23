import Numlib.Optimization.LeastNorm.Regularity
import Numlib.Optimization.Constrained.TargetMerit
/-!
# Uniform target merit regularity

Positive derivatives are unaffected by an objective target shift. The target
merit is the sum of two actual least-squares merits. Its unit residual level
therefore has bounded Lipschitz derivatives with constants independent of the
target, derived from the original objective and constraint derivatives.
-/

namespace Constrained
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Positive-order objective derivatives are unchanged by subtracting a target. -/
theorem iteratedFDeriv_shift_target {f : E → ℝ} {p j : ℕ} {S : Set E}
    (hf : ContDiffOn ℝ p f S) (hS : IsOpen S) (hj : 1 ≤ j) (hjp : j ≤ p)
    {x : E} (hx : x ∈ S) (t : ℝ) :
    iteratedFDeriv ℝ j (fun z => f z - t) x = iteratedFDeriv ℝ j f x := by
  rw [fun_iteratedFDeriv_sub_apply
    ((hf.of_le (by exact_mod_cast hjp)).contDiffAt (hS.mem_nhds hx)) contDiffAt_const,
    iteratedFDeriv_const_of_ne (by omega : j ≠ 0) t]
  simp only [Pi.zero_apply, sub_zero]

/-- The actual target merit derivative is the sum of the two residual merit derivatives. -/
theorem iteratedFDeriv_targetMerit {f : E → ℝ} {c : E → F} {p j : ℕ} {S : Set E}
    (hf : ContDiffOn ℝ p f S) (hc : ContDiffOn ℝ p c S) (hS : IsOpen S)
    (hjp : j ≤ p) {x : E} (hx : x ∈ S) (t : ℝ) :
    iteratedFDeriv ℝ j (targetMerit f c t) x =
      iteratedFDeriv ℝ j (LeastNorm.merit c) x +
      iteratedFDeriv ℝ j (LeastNorm.merit (fun z => f z - t)) x := by
  have hfj : ContDiffOn ℝ j f S := hf.of_le (by exact_mod_cast hjp)
  have hcj : ContDiffOn ℝ j c S := hc.of_le (by exact_mod_cast hjp)
  have hshift : ContDiffOn ℝ j (fun z => f z - t) S := hfj.sub contDiffOn_const
  have he : targetMerit f c t = LeastNorm.merit c +
      LeastNorm.merit (fun z => f z - t) := by
    funext z
    simp [targetMerit, LeastNorm.merit, Real.norm_eq_abs, sq_abs]
  rw [he]
  apply iteratedFDeriv_add_apply
  · have hh := (hcj.norm_sq (𝕜 := ℝ)).const_smul (1 / 2 : ℝ)
    convert hh.contDiffAt (hS.mem_nhds hx) using 1
    funext z
    simp [LeastNorm.merit, smul_eq_mul]; ring
  · have hh := (hshift.norm_sq
      (𝕜 := ℝ)).const_smul (1 / 2 : ℝ)
    convert hh.contDiffAt (hS.mem_nhds hx) using 1
    funext z
    simp [LeastNorm.merit, smul_eq_mul]; ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ F] in
/-- The unit augmented residual level bounds both the equality residual and target gap. -/
theorem targetMerit_residual_bounds {f : E → ℝ} {c : E → F} {x : E} {t : ℝ}
    (h : targetMerit f c t x ≤ (1 / 2 : ℝ)) : ‖c x‖ ≤ 1 ∧ ‖f x - t‖ ≤ 1 := by
  dsimp [targetMerit] at h
  rw [Real.norm_eq_abs]
  constructor
  · nlinarith [sq_nonneg (f x - t), norm_nonneg (c x)]
  · apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg ‖c x‖]
/-- Smooth objective and constraint maps give a smooth target merit on the same domain. -/
theorem contDiffOn_targetMerit {f : E → ℝ} {c : E → F} {p : ℕ} {S : Set E}
    (hf : ContDiffOn ℝ p f S) (hc : ContDiffOn ℝ p c S) (t : ℝ) :
    ContDiffOn ℝ p (targetMerit f c t) S := by
  have hshift : ContDiffOn ℝ p (fun z => f z - t) S := hf.sub contDiffOn_const
  have hh := ((hc.norm_sq (𝕜 := ℝ)).const_smul (1 / 2 : ℝ)).add
    ((hshift.pow 2).const_smul (1 / 2 : ℝ))
  convert hh using 1
  funext z
  simp only [targetMerit, smul_eq_mul]
  ring

/-- Actual bounded Lipschitz objective and residual derivatives give uniform
target merit regularity on its unit residual level, with constants before all targets. -/
theorem targetMerit_uniform_regularity {f : E → ℝ} {c : E → F} {p : ℕ} {S : Set E}
    (hf : ContDiffOn ℝ p f S) (hc : ContDiffOn ℝ p c S) (hS : IsOpen S)
    (hconv : Convex ℝ S) {Bf Lf Bc Lc : ℝ}
    (hBf : 0 ≤ Bf) (hLf : 0 ≤ Lf) (hBc : 0 ≤ Bc) (hLc : 0 ≤ Lc)
    (hbf : ∀ j, 1 ≤ j → j ≤ p → ∀ x ∈ S, ‖iteratedFDeriv ℝ j f x‖ ≤ Bf)
    (hlf : ∀ j, 1 ≤ j → j ≤ p → ∀ x ∈ S, ∀ y ∈ S,
      ‖iteratedFDeriv ℝ j f x - iteratedFDeriv ℝ j f y‖ ≤ Lf * ‖x - y‖)
    (hbc : ∀ j, 1 ≤ j → j ≤ p → ∀ x ∈ S, ‖iteratedFDeriv ℝ j c x‖ ≤ Bc)
    (hlc : ∀ j, 1 ≤ j → j ≤ p → ∀ x ∈ S, ∀ y ∈ S,
      ‖iteratedFDeriv ℝ j c x - iteratedFDeriv ℝ j c y‖ ≤ Lc * ‖x - y‖) :
    ∃ L ≥ 1, ∃ B ≥ 1, ∀ t : ℝ, ContDiffOn ℝ p (targetMerit f c t) S ∧
      ∀ j, 1 ≤ j → j ≤ p → ∀ x ∈ S, targetMerit f c t x ≤ (1 / 2 : ℝ) →
        (∀ y ∈ S, ‖iteratedFDeriv ℝ j (targetMerit f c t) x -
          iteratedFDeriv ℝ j (targetMerit f c t) y‖ ≤ L * ‖x - y‖) ∧
        ‖iteratedFDeriv ℝ j (targetMerit f c t) x‖ ≤ B := by
  let A := (2 : ℝ) ^ p * (3 * Bc ^ 2 + 2 * Bc * Lc + 2 * Lc) +
    (2 : ℝ) ^ p * (3 * Bf ^ 2 + 2 * Bf * Lf + 2 * Lf)
  let C := (2 : ℝ) ^ p * (Bc ^ 2 + Bc) + (2 : ℝ) ^ p * (Bf ^ 2 + Bf)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨1+A, by linarith, 1+C, by linarith, ?_⟩
  intro t
  refine ⟨contDiffOn_targetMerit hf hc t, ?_⟩
  intro j hj hjp x hx hlevel
  have hnorm := targetMerit_residual_bounds hlevel
  have hshift : ContDiffOn ℝ p (fun z => f z - t) S := hf.sub contDiffOn_const
  have hbshift : ∀ i, 1 ≤ i → i ≤ p → ∀ z ∈ S,
      ‖iteratedFDeriv ℝ i (fun z => f z - t) z‖ ≤ Bf := by
    intro i hi hip z hz
    rw [iteratedFDeriv_shift_target hf hS hi hip hz]
    exact hbf i hi hip z hz
  have hlshift : ∀ i, 1 ≤ i → i ≤ p → ∀ z ∈ S, ∀ w ∈ S,
      ‖iteratedFDeriv ℝ i (fun z => f z - t) z -
        iteratedFDeriv ℝ i (fun z => f z - t) w‖ ≤ Lf * ‖z - w‖ := by
    intro i hi hip z hz w hw
    rw [iteratedFDeriv_shift_target hf hS hi hip hz,
      iteratedFDeriv_shift_target hf hS hi hip hw]
    exact hlf i hi hip z hz w hw
  have hcc := LeastNorm.merit_derivative_bounds_of_residual_bound
    hc hS hconv hBc hLc hbc hlc hj hjp hx hnorm.1
  have hff := LeastNorm.merit_derivative_bounds_of_residual_bound
    hshift hS hconv hBf hLf hbshift hlshift hj hjp hx hnorm.2
  refine ⟨?_, ?_⟩
  · intro y hy
    rw [iteratedFDeriv_targetMerit hf hc hS hjp hx,
      iteratedFDeriv_targetMerit hf hc hS hjp hy]
    have he : (iteratedFDeriv ℝ j (LeastNorm.merit c) x +
        iteratedFDeriv ℝ j (LeastNorm.merit (fun z => f z - t)) x) -
        (iteratedFDeriv ℝ j (LeastNorm.merit c) y +
        iteratedFDeriv ℝ j (LeastNorm.merit (fun z => f z - t)) y) =
        (iteratedFDeriv ℝ j (LeastNorm.merit c) x - iteratedFDeriv ℝ j (LeastNorm.merit c) y) +
        (iteratedFDeriv ℝ j (LeastNorm.merit (fun z => f z - t)) x -
          iteratedFDeriv ℝ j (LeastNorm.merit (fun z => f z - t)) y) := by abel
    rw [he]
    exact (norm_add_le _ _).trans (by
      have h1 := hcc.1 y hy
      have h2 := hff.1 y hy
      dsimp [A]
      nlinarith [norm_nonneg (x - y)])
  · rw [iteratedFDeriv_targetMerit hf hc hS hjp hx]
    exact (norm_add_le _ _).trans (by dsimp [C]; nlinarith [hcc.2, hff.2])
end Constrained

import Numlib.Optimization.QuadraticSubproblem
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Kernel completion of shifted quadratic stationarity

An orthogonal particular solution has the smallest norm among all solutions of a shifted
stationarity equation. The full kernel, rather than a chosen eigenvector, parametrizes every
solution, and the quadratic value depends only on its norm. This covers kernels of arbitrary
dimension and keeps the zero-multiplier ball condition distinct from the positive case.
-/

noncomputable section
open scoped InnerProductSpace
namespace Optimization.QuadraticSubproblem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Removing the kernel projection preserves a linear equation and produces a particular
solution orthogonal to the kernel. Only the kernel needs an orthogonal projection. -/
theorem exists_orthogonal_particular (A : E →L[ℝ] E) [A.ker.HasOrthogonalProjection]
    (s : E) : ∃ ss : E, A ss = A s ∧ ss ∈ A.kerᗮ := by
  refine ⟨s - A.ker.starProjection s, ?_, A.ker.sub_starProjection_mem_orthogonal s⟩
  rw [map_sub, show A (A.ker.starProjection s) = 0 from
    A.ker.starProjection_apply_mem s, sub_zero]

/-- An orthogonal particular solution gives the complete affine solution space, together
with its Pythagorean norm formula. -/
theorem eq_iff_kernel_completion {A : E →L[ℝ] E} {ss t : E} (hss : ss ∈ A.kerᗮ) :
    A t = A ss ↔ ∃ z ∈ A.ker, t = ss + z ∧ ‖t‖ ^ 2 = ‖ss‖ ^ 2 + ‖z‖ ^ 2 := by
  constructor
  · intro ht
    have hz : t - ss ∈ A.ker := by change A (t - ss) = 0; simp [ht]
    refine ⟨t - ss, hz, by abel, ?_⟩
    have hi : ⟪ss, t - ss⟫_ℝ = 0 := (A.ker.mem_orthogonal' ss).mp hss _ hz
    simpa only [add_sub_cancel, sq] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero ss (t - ss) hi
  · rintro ⟨z, hz, rfl, _⟩
    simp only [map_add, show A z = 0 from hz, add_zero]

/-- The orthogonal particular solution uniquely minimizes norm among all solutions. -/
theorem norm_le_of_orthogonal_particular {A : E →L[ℝ] E} {ss t : E}
    (hss : ss ∈ A.kerᗮ) (ht : A t = A ss) :
    ‖ss‖ ≤ ‖t‖ ∧ (‖ss‖ = ‖t‖ ↔ ss = t) := by
  obtain ⟨z, _, htz, hn⟩ := (eq_iff_kernel_completion hss).mp ht
  have hle : ‖ss‖ ≤ ‖t‖ := by nlinarith [sq_nonneg ‖z‖, norm_nonneg ss, norm_nonneg t]
  refine ⟨hle, ?_⟩
  constructor
  · intro heq
    have hz : ‖z‖ = 0 := by
      have hz2 : ‖z‖ ^ 2 = 0 := by rw [heq] at hn; linarith
      exact sq_eq_zero_iff.mp hz2
    simpa [norm_eq_zero.mp hz] using htz.symm
  · rintro rfl; rfl

/-- Every shifted stationary equation admits a minimum-norm particular solution whenever
its kernel admits orthogonal projection. All other solutions run over the entire kernel. -/
theorem minimizer_eigenspace_completion {g s : E} {H : E →L[ℝ] E} {lambda : ℝ}
    [(H + lambda • ContinuousLinearMap.id ℝ E).ker.HasOrthogonalProjection]
    (hstat : g + H s + lambda • s = 0) :
    ∃ ss : E, g + H ss + lambda • ss = 0 ∧
      ss ∈ (H + lambda • ContinuousLinearMap.id ℝ E).kerᗮ ∧
      ∀ t : E, g + H t + lambda • t = 0 ↔
        ∃ z ∈ (H + lambda • ContinuousLinearMap.id ℝ E).ker,
          t = ss + z ∧ ‖t‖ ^ 2 = ‖ss‖ ^ 2 + ‖z‖ ^ 2 := by
  let A := H + lambda • ContinuousLinearMap.id ℝ E
  obtain ⟨ss, hass, hss⟩ := exists_orthogonal_particular A s
  have heq (t : E) : g + H t + lambda • t = 0 ↔ A t = A s := by
    have has : g + A s = 0 := by simpa [A, add_assoc] using hstat
    have he : g + A t = 0 ↔ A t = A s := by
      constructor
      · intro ht; exact add_left_cancel (ht.trans has.symm)
      · intro ht; rw [ht]; exact has
    simpa [A, add_assoc] using he
  refine ⟨ss, (heq ss).mpr hass, hss, fun t => ?_⟩
  rw [heq, ← hass]
  exact eq_iff_kernel_completion hss

/-- At shifted stationarity the quadratic value has a direct norm formula. -/
theorem quadratic_eq_of_stationary {g s : E} {H : E →L[ℝ] E} {lambda : ℝ}
    (hstat : g + H s + lambda • s = 0) :
    quadratic g H s = (1 / 2 : ℝ) * ⟪g, s⟫_ℝ - lambda / 2 * ‖s‖ ^ 2 := by
  have h := congrArg (fun v => ⟪v, s⟫_ℝ) hstat
  simp only [inner_add_left, real_inner_smul_left, inner_zero_left,
    real_inner_self_eq_norm_sq] at h
  rw [real_inner_comm s (H s)] at h
  unfold quadratic
  linarith

/-- Kernel directions leave the linear term unchanged at a symmetric shifted stationary
point. Hence the completed quadratic value is independent of their direction. -/
theorem quadratic_kernel_completion_value {g ss z : E} {H : E →L[ℝ] E}
    (hH : H.IsSymmetric) {lambda : ℝ} (hstat : g + H ss + lambda • ss = 0)
    (hz : z ∈ (H + lambda • ContinuousLinearMap.id ℝ E).ker) :
    quadratic g H (ss + z) =
      (1 / 2 : ℝ) * ⟪g, ss⟫_ℝ - lambda / 2 * ‖ss + z‖ ^ 2 := by
  have haz : H z + lambda • z = 0 := hz
  have hgz : ⟪g, z⟫_ℝ = 0 := by
    have hg := congrArg (fun v => ⟪v, z⟫_ℝ) hstat
    have hh := congrArg (fun v => ⟪ss, v⟫_ℝ) haz
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, inner_zero_left, inner_zero_right] at hg hh
    rw [hH.apply_clm ss z] at hg
    linarith
  have hnew : g + H (ss + z) + lambda • (ss + z) = 0 := by
    rw [map_add, smul_add]
    calc
      g + (H ss + H z) + (lambda • ss + lambda • z) =
          (g + H ss + lambda • ss) + (H z + lambda • z) := by abel
      _ = 0 := by rw [hstat, haz, add_zero]
  simpa [inner_add_right, hgz] using quadratic_eq_of_stationary hnew

omit [InnerProductSpace ℝ E] in
/-- Complementarity makes the positive-multiplier norm constraint a sphere, while a zero
multiplier permits the whole ball. This formulation never forces an interior point to its
boundary. -/
theorem feasible_complementarity_iff {s : E} {delta lambda : ℝ} (hl : 0 ≤ lambda) :
    (‖s‖ ≤ delta ∧ lambda * (‖s‖ ^ 2 - delta ^ 2) = 0) ↔
      (lambda = 0 ∧ ‖s‖ ≤ delta) ∨ (0 < lambda ∧ ‖s‖ = delta) := by
  constructor
  · rintro ⟨hs, hc⟩
    rcases eq_or_lt_of_le hl with h | h
    · exact Or.inl ⟨h.symm, hs⟩
    · right
      refine ⟨h, ?_⟩
      have he : ‖s‖ ^ 2 = delta ^ 2 := by
        exact sub_eq_zero.mp ((mul_eq_zero.mp hc).resolve_left h.ne')
      nlinarith [norm_nonneg s]
  · rintro (⟨rfl, hs⟩ | ⟨_, hs⟩)
    · exact ⟨hs, by simp⟩
    · exact ⟨hs.le, by simp [hs]⟩

end Optimization.QuadraticSubproblem

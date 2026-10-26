import Numlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Radial and orthogonal diagonal derivatives of norm powers

The actual multilinear derivatives have explicit radial and orthogonal diagonal
values. In the finite differentiability range, these values are convex on the
orthogonal subspace, and on the radial subspace for even orders. These facts do
not require an equality between diagonal and multilinear operator norms.
-/

open scoped BigOperators InnerProductSpace
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem diagonal_normalize (j : ℕ) (T : E [×j]→L[ℝ] ℝ)
    {d : E} (hd : d ≠ 0) :
    T (fun _ => d) = ‖d‖ ^ j * T (fun _ => ‖d‖⁻¹ • d) := by
  have he : d = ‖d‖ • (‖d‖⁻¹ • d) := by
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hd), one_smul]
  calc
    T (fun _ => d) = T (fun _ => ‖d‖ • (‖d‖⁻¹ • d)) := by
      congr 1
      funext i
      exact he
    _ = _ := by simp [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]

/-- Applying a norm-power derivative repeatedly to its base point gives the
falling factorial times the original norm power. -/
theorem iteratedFDeriv_normRpow_apply_radial (lam : ℝ) (j : ℕ)
    {x : E} (hx : x ≠ 0) :
    iteratedFDeriv ℝ j (fun z : E => ‖z‖ ^ lam) x (fun _ => x) =
      (∏ i : Fin j, (lam - i)) * ‖x‖ ^ lam := by
  rw [diagonal_normalize j _ hx, iteratedFDeriv_normRpow_apply_unit lam j hx]
  calc
    _ = (∏ i : Fin j, (lam - i)) * (‖x‖ ^ (lam - j) * ‖x‖ ^ j) := by ring
    _ = _ := by
      rw [← Real.rpow_natCast, ← Real.rpow_add (norm_pos_iff.mpr hx)]
      simp

/-- Every odd derivative of the even scalar norm-line profile vanishes at zero. -/
theorem iteratedDeriv_one_add_sq_rpow_odd (lam : ℝ) (k : ℕ) :
    iteratedDeriv (2 * k + 1) (fun t : ℝ => (1 + t ^ 2) ^ (lam / 2)) 0 = 0 := by
  induction k with
  | zero => simp [iteratedDeriv_one]
  | succ k ih =>
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega,
        iteratedDeriv_one_add_sq_rpow_succ_succ, ih, mul_zero]

/-- Even diagonal derivatives in any orthogonal direction have an explicit
non-radial coefficient and a homogeneous even norm power. -/
theorem iteratedFDeriv_normRpow_apply_perp_even [FiniteDimensional ℝ E] (lam : ℝ) (k : ℕ)
    {x d : E} (hx : x ≠ 0) (hd : inner ℝ x d = 0) :
    iteratedFDeriv ℝ (2 * k) (fun z : E => ‖z‖ ^ lam) x (fun _ => d) =
      (‖x‖ ^ (lam - 2 * k) *
        ∏ i : Fin k, ((2 * (i : ℝ) + 1) * (lam - 2 * i))) * ‖d‖ ^ (2 * k) := by
  by_cases hk : k = 0
  · subst k
    simp [iteratedFDeriv_zero_apply]
  by_cases hd0 : d = 0
  · subst d
    rw [ContinuousMultilinearMap.map_coord_zero _ ⟨0, by omega⟩ rfl]
    simp [zero_pow (by omega : 2 * k ≠ 0)]
  rw [diagonal_normalize _ _ hd0,
    iteratedFDeriv_normRpow_apply_perp lam (2 * k) hx
      (by simp [norm_smul, norm_inv,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hd0)])
      (by simp [inner_smul_right, hd]),
    iteratedDeriv_one_add_sq_rpow_two_mul]
  push_cast
  ring

/-- Odd diagonal derivatives vanish in every orthogonal direction. -/
theorem iteratedFDeriv_normRpow_apply_perp_odd [FiniteDimensional ℝ E] (lam : ℝ) (k : ℕ)
    {x d : E} (hx : x ≠ 0) (hd : inner ℝ x d = 0) :
    iteratedFDeriv ℝ (2 * k + 1) (fun z : E => ‖z‖ ^ lam) x (fun _ => d) = 0 := by
  by_cases hd0 : d = 0
  · subst d
    exact ContinuousMultilinearMap.map_coord_zero _ ⟨0, by omega⟩ rfl
  rw [diagonal_normalize _ _ hd0,
    iteratedFDeriv_normRpow_apply_perp lam (2 * k + 1) hx
      (by simp [norm_smul, norm_inv,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hd0)])
      (by simp [inner_smul_right, hd]),
    iteratedDeriv_one_add_sq_rpow_odd, mul_zero, mul_zero]

/-- In the finite differentiability range, the diagonal derivative is convex
on the orthogonal complement of its nonzero base point. -/
theorem convexOn_iteratedFDeriv_normRpow_perp [FiniteDimensional ℝ E] (lam : ℝ) (j : ℕ)
    (hlam : (j : ℝ) - 1 < lam) {x : E} (hx : x ≠ 0) :
    ConvexOn ℝ {d : E | inner ℝ x d = 0}
      (fun d => iteratedFDeriv ℝ j (fun z : E => ‖z‖ ^ lam) x (fun _ => d)) := by
  have hc : Convex ℝ {d : E | inner ℝ x d = 0} :=
    (innerSL ℝ x).toLinearMap.ker.convex
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' j
  · have hcoef : 0 ≤ ‖x‖ ^ (lam - 2 * k) *
        ∏ i : Fin k, ((2 * (i : ℝ) + 1) * (lam - 2 * i)) := by
      apply mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Finset.prod_nonneg _)
      intro i _
      have hi : (i : ℝ) + 1 ≤ k := by exact_mod_cast i.isLt
      push_cast at hlam
      apply mul_nonneg (by positivity)
      linarith
    have hh := ((convexOn_norm hc).pow (fun _ _ => norm_nonneg _) (2 * k)).smul hcoef
    apply hh.congr
    intro d hd
    simpa only [Pi.pow_apply, smul_eq_mul] using
      (iteratedFDeriv_normRpow_apply_perp_even lam k hx hd).symm
  · apply (convexOn_const (0 : ℝ) hc).congr
    intro d hd
    exact (iteratedFDeriv_normRpow_apply_perp_odd lam k hx hd).symm

/-- Even diagonal derivatives in the finite differentiability range are convex
on the radial subspace through the nonzero base point. -/
theorem convexOn_iteratedFDeriv_normRpow_span_even (lam : ℝ) (j : ℕ)
    (hj : Even j) (hlam : (j : ℝ) - 1 < lam) {x : E} (hx : x ≠ 0) :
    ConvexOn ℝ (Submodule.span ℝ {x} : Set E)
      (fun d => iteratedFDeriv ℝ j (fun z : E => ‖z‖ ^ lam) x (fun _ => d)) := by
  let c : ℝ := (∏ i : Fin j, (lam - i)) * ‖x‖ ^ lam
  have hc : 0 ≤ c := by
    apply mul_nonneg (Finset.prod_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)
    intro i _
    have hi : (i : ℝ) ≤ (j : ℝ) - 1 := by
      have hin : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast i.isLt
      linarith
    linarith
  have heval (t : ℝ) :
      iteratedFDeriv ℝ j (fun z : E => ‖z‖ ^ lam) x (fun _ => t • x) = c * t ^ j := by
    rw [ContinuousMultilinearMap.map_smul_univ]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      iteratedFDeriv_normRpow_apply_radial lam j hx]
    dsimp [c]
    ring
  refine ⟨(Submodule.span ℝ {x}).convex, ?_⟩
  intro a ha b hb u v hu hv huv
  obtain ⟨ta, rfl⟩ := Submodule.mem_span_singleton.mp ha
  obtain ⟨tb, rfl⟩ := Submodule.mem_span_singleton.mp hb
  change iteratedFDeriv ℝ j (fun z : E => ‖z‖ ^ lam) x
      (fun _ => u • (ta • x) + v • (tb • x)) ≤
    u • iteratedFDeriv ℝ j (fun z : E => ‖z‖ ^ lam) x (fun _ => ta • x) +
      v • iteratedFDeriv ℝ j (fun z : E => ‖z‖ ^ lam) x (fun _ => tb • x)
  rw [show u • (ta • x) + v • (tb • x) = (u * ta + v * tb) • x by
    rw [smul_smul, smul_smul, add_smul], heval, heval, heval]
  have hh := (hj.convexOn_pow.smul hc).2 (mem_univ ta) (mem_univ tb) hu hv huv
  simpa only [smul_eq_mul] using hh

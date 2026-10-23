import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic

/-!
# Diagonal tensor seminorms and orthogonal projection

The supremum of the absolute homogeneous contraction on a closed unit ball agrees
with its unit-sphere formulation at positive order in nontrivial real inner product
spaces. Projecting the tensor in every argument gives precisely the norm restricted
to the projected subspace. No equality with the full multilinear operator norm is
assumed: that equality requires symmetry and is a separate theorem.
-/

open Set
namespace ContinuousMultilinearMap
section Normed
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The diagonal tensor seminorm, as the supremum of absolute homogeneous evaluations on
the closed unit ball. This is the first, diagonal definition of the symmetric tensor
norm in (A.7); the ball formulation also covers the zero-dimensional space. -/
noncomputable def diagonalNorm {p : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) ℝ) : ℝ :=
  sSup ((fun v : E => |T (fun _ => v)|) '' Metric.closedBall 0 1)

/-- A tensor is bounded on the diagonal unit ball by its multilinear norm. -/
theorem diagonalNorm_bddAbove {p : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) ℝ) :
    BddAbove ((fun v : E => |T (fun _ => v)|) '' Metric.closedBall 0 1) := by
  refine ⟨‖T‖, ?_⟩
  rintro _ ⟨v,hv,rfl⟩
  have hv' : ‖v‖ ≤ 1 := by simpa using hv
  have hh := T.le_opNorm (fun _ => v)
  simp only [Fin.prod_const, Real.norm_eq_abs] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left
    (pow_le_one₀ (norm_nonneg v) hv') (norm_nonneg T)).trans_eq (mul_one _))

/-- The diagonal norm is nonnegative, including when the tensor is zero. -/
theorem diagonalNorm_nonneg {p : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) ℝ) :
    0 ≤ diagonalNorm T := by
  exact (abs_nonneg _).trans (le_csSup (diagonalNorm_bddAbove T)
    ⟨0, by simp, rfl⟩)

/-- Every feasible diagonal evaluation is bounded by the diagonal tensor norm. -/
theorem abs_apply_le_diagonalNorm {p : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) ℝ)
    {v : E} (hv : ‖v‖ ≤ 1) : |T (fun _ => v)| ≤ diagonalNorm T :=
  le_csSup (diagonalNorm_bddAbove T) ⟨v, by simpa using hv, rfl⟩

/-- A bound for all diagonal unit-ball evaluations bounds the diagonal norm. -/
theorem diagonalNorm_le {p : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) ℝ) {a : ℝ}
    (h : ∀ v : E, ‖v‖ ≤ 1 → |T (fun _ => v)| ≤ a) : diagonalNorm T ≤ a := by
  unfold diagonalNorm
  refine csSup_le (show ((fun v : E => |T (fun _ => v)|) '' Metric.closedBall 0 1).Nonempty from
    ⟨|T (fun _ => 0)|, ⟨0, by simp, rfl⟩⟩) ?_
  rintro _ ⟨v,hv,rfl⟩
  exact h v (by simpa using hv)

/-- For positive tensor order on a nontrivial space, the closed-ball diagonal norm
is exactly the unit-sphere norm in the first equality of (A.7). -/
theorem diagonalNorm_eq_sSup_sphere [Nontrivial E] {p : ℕ} (hp : 0 < p)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) ℝ) :
    diagonalNorm T = sSup ((fun v : E => |T (fun _ => v)|) '' Metric.sphere 0 1) := by
  have hs : Metric.sphere (0 : E) 1 ⊆ Metric.closedBall 0 1 :=
    Metric.sphere_subset_closedBall
  have hb := (diagonalNorm_bddAbove T).mono (Set.image_mono hs)
  obtain ⟨u,hu⟩ := exists_norm_eq E (by norm_num : (0 : ℝ) ≤ 1)
  have hmem : |T (fun _ => u)| ∈
      (fun v : E => |T (fun _ => v)|) '' Metric.sphere 0 1 :=
    ⟨u, by simpa using hu, rfl⟩
  have hn := Set.nonempty_of_mem hmem
  have hnonneg : 0 ≤ sSup ((fun v : E => |T (fun _ => v)|) '' Metric.sphere 0 1) :=
    (abs_nonneg _).trans (le_csSup hb hmem)
  apply le_antisymm
  · apply diagonalNorm_le
    intro v hv
    by_cases hv0 : v = 0
    · subst v
      have hz : T (fun _ => (0 : E)) = 0 := T.map_coord_zero ⟨0,hp⟩ rfl
      simpa [hz] using hnonneg
    have hvpos := norm_pos_iff.mpr hv0
    let w := ‖v‖⁻¹ • v
    have hw : ‖w‖ = 1 := by
      simp [w, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hvpos.le), hvpos.ne']
    have hww : ‖v‖ • w = v := by simp [w, smul_smul, hvpos.ne']
    have hmap := T.map_smul_univ (fun _ => ‖v‖) (fun _ => w)
    have heq : T (fun _ => v) = ‖v‖ ^ p * T (fun _ => w) := by
      simpa only [hww, Fin.prod_const, smul_eq_mul] using hmap
    rw [heq, abs_mul, abs_of_nonneg (pow_nonneg (norm_nonneg v) p)]
    calc ‖v‖ ^ p * |T (fun _ => w)| ≤ |T (fun _ => w)| :=
        mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ (norm_nonneg v) hv)
      _ ≤ _ := le_csSup hb ⟨w, by simpa using hw, rfl⟩
  · apply csSup_le hn
    rintro _ ⟨v,hv,rfl⟩
    apply abs_apply_le_diagonalNorm
    exact (show ‖v‖ = 1 by simpa using hv).le

/-- A vanishing diagonal norm is equivalent to vanishing on every repeated direction. -/
theorem diagonalNorm_eq_zero_iff
    {p : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) ℝ) :
    diagonalNorm T = 0 ↔ ∀ v : E, T (fun _ => v) = 0 := by
  constructor
  · intro h v
    by_cases hv : v = 0
    · subst v
      have hh := abs_apply_le_diagonalNorm T (v := 0) (by simp)
      rw [h] at hh
      exact abs_nonpos_iff.mp hh
    have hvpos := norm_pos_iff.mpr hv
    have hunit : ‖‖v‖⁻¹ • v‖ ≤ 1 := by
      simp [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hvpos.le), hvpos.ne']
    have hh := abs_apply_le_diagonalNorm T hunit
    rw [h] at hh
    have hz : T (fun _ => ‖v‖⁻¹ • v) = 0 := abs_nonpos_iff.mp hh
    have hmap := T.map_smul_univ (fun _ => ‖v‖⁻¹) (fun _ => v)
    simp only [Fin.prod_const, smul_eq_mul] at hmap
    rw [hmap] at hz
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ (inv_ne_zero hvpos.ne'))
  · intro h
    apply le_antisymm _ (diagonalNorm_nonneg T)
    exact diagonalNorm_le T (fun v _ => by simp [h v])


end Normed

section Projection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Projecting a tensor in all arguments gives exactly its diagonal norm
restricted to the projected subspace. -/
theorem diagonalNorm_comp_starProjection
    {p : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) ℝ) (K : Submodule ℝ E) :
    diagonalNorm (T.compContinuousLinearMap (fun _ => K.starProjection)) =
      sSup ((fun v : E => |T (fun _ => v)|) '' (Metric.closedBall 0 1 ∩ (K : Set E))) := by
  have hb : BddAbove ((fun v : E => |T (fun _ => v)|) ''
      (Metric.closedBall 0 1 ∩ (K : Set E))) :=
    (diagonalNorm_bddAbove T).mono (Set.image_mono Set.inter_subset_left)
  have hn : ((fun v : E => |T (fun _ => v)|) ''
      (Metric.closedBall 0 1 ∩ (K : Set E))).Nonempty :=
    ⟨|T (fun _ => 0)|, ⟨0, ⟨by simp, K.zero_mem⟩, rfl⟩⟩
  apply le_antisymm
  · apply diagonalNorm_le
    intro v hv
    exact le_csSup hb ⟨K.starProjection v,
      ⟨by simpa using (K.norm_starProjection_apply_le v).trans hv,
        K.starProjection_apply_mem v⟩, rfl⟩
  · apply csSup_le hn
    rintro _ ⟨v,⟨hv,hvK⟩,rfl⟩
    have hh := abs_apply_le_diagonalNorm
      (T.compContinuousLinearMap (fun _ => K.starProjection)) (by simpa using hv)
    simpa [K.starProjection_eq_self_iff.mpr hvK] using hh

end Projection
end ContinuousMultilinearMap

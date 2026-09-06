/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Ring.Units`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Explicit Neumann-series and perturbation bounds

Quantitative versions of `Units.oneSub` / `Units.add` in a complete normed ring:
`‖(1 - t)⁻¹‖ ≤ 1 / (1 - ‖t‖)`, `‖(x + t)⁻¹‖ ≤ ‖x⁻¹‖ / (1 - ‖x⁻¹‖ ‖t‖)`, and the two-space
version for continuous linear equivalences. These are the explicit forms of the classical
geometric-series (Banach perturbation) estimates for the inverse of a small perturbation of an
invertible element.
-/

/-- `u ↦ 1 / (1 - u)` is monotone below `1`. -/
private theorem one_div_one_sub_le_one_div_one_sub {u v : ℝ} (huv : u ≤ v) (hv : v < 1) :
    1 / (1 - u) ≤ 1 / (1 - v) :=
  one_div_le_one_div_of_le (by linarith) (by linarith)

/-- `u ↦ u / (1 - u)` is monotone on `[0, 1)`. -/
private theorem div_one_sub_le_div_one_sub {u v : ℝ} (huv : u ≤ v) (hv : v < 1) :
    u / (1 - u) ≤ v / (1 - v) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

namespace NormedRing

/-- The Neumann bound without assuming `‖1‖ = 1`; only `‖1‖ ≤ 1` is used.  This form applies to
rings of continuous linear maps, which are not `NormOneClass` when the space is trivial. -/
private theorem norm_inverse_one_sub_le' {R : Type*} [NormedRing R] [HasSummableGeomSeries R]
    (h₁ : ‖(1 : R)‖ ≤ 1) {t : R} (h : ‖t‖ < 1) : ‖Ring.inverse (1 - t)‖ ≤ 1 / (1 - ‖t‖) := by
  rw [← geom_series_eq_inverse t h, one_div]
  have := tsum_geometric_le_of_norm_lt_one t h
  linarith

private theorem norm_inverse_one_sub_sub_one_le' {R : Type*} [NormedRing R]
    [HasSummableGeomSeries R] (h₁ : ‖(1 : R)‖ ≤ 1) {t : R} (h : ‖t‖ < 1) :
    ‖Ring.inverse (1 - t) - 1‖ ≤ ‖t‖ / (1 - ‖t‖) := by
  have key : Ring.inverse (1 - t) - 1 = t * Ring.inverse (1 - t) := by
    rw [← geom_series_eq_inverse t h, geom_series_mul_shift t h, geom_series_succ t h]
  rw [key]
  calc ‖t * Ring.inverse (1 - t)‖ ≤ ‖t‖ * ‖Ring.inverse (1 - t)‖ := norm_mul_le _ _
    _ ≤ ‖t‖ * (1 / (1 - ‖t‖)) :=
        mul_le_mul_of_nonneg_left (norm_inverse_one_sub_le' h₁ h) (norm_nonneg _)
    _ = ‖t‖ / (1 - ‖t‖) := by ring

variable {R : Type*} [NormedRing R] [NormOneClass R] [CompleteSpace R]

/-- Geometric series theorem with the explicit bound `‖(1 - t)⁻¹‖ ≤ 1 / (1 - ‖t‖)`. -/
theorem norm_inverse_one_sub_le {t : R} (h : ‖t‖ < 1) :
    ‖Ring.inverse (1 - t)‖ ≤ 1 / (1 - ‖t‖) :=
  norm_inverse_one_sub_le' norm_one.le h

/-- `‖(1 - t)⁻¹ - 1‖ ≤ ‖t‖ / (1 - ‖t‖)`. -/
theorem norm_inverse_one_sub_sub_one_le {t : R} (h : ‖t‖ < 1) :
    ‖Ring.inverse (1 - t) - 1‖ ≤ ‖t‖ / (1 - ‖t‖) :=
  norm_inverse_one_sub_sub_one_le' norm_one.le h

omit [NormOneClass R] [CompleteSpace R] in
/-- `1 - t^m = (1 - t) ∑_{i < m} t^i`, and the two factors commute. -/
private theorem one_sub_pow_eq (t : R) (m : ℕ) :
    (1 - t) * (∑ i ∈ Finset.range m, t ^ i) = 1 - t ^ m := by
  have h : (t - 1) * (∑ i ∈ Finset.range m, t ^ i) = t ^ m - 1 := mul_geom_sum t m
  have hneg : (1 - t) * (∑ i ∈ Finset.range m, t ^ i)
      = -((t - 1) * (∑ i ∈ Finset.range m, t ^ i)) := by rw [← neg_mul, neg_sub]
  rw [hneg, h, neg_sub]

omit [NormOneClass R] [CompleteSpace R] in
private theorem commute_one_sub_geom_sum (t : R) (m : ℕ) :
    Commute (1 - t) (∑ i ∈ Finset.range m, t ^ i) :=
  Commute.sum_right _ _ _ fun i _ =>
    (Commute.one_left (t ^ i)).sub_left ((Commute.refl t).pow_right i)

omit [NormOneClass R] in
/-- `‖t ^ m‖ < 1` for a single `m` already suffices for `1 - t` to be a unit. -/
theorem isUnit_one_sub_of_norm_pow_lt_one {t : R} {m : ℕ} (h : ‖t ^ m‖ < 1) : IsUnit (1 - t) := by
  have hprod : IsUnit ((1 - t) * ∑ i ∈ Finset.range m, t ^ i) := by
    rw [one_sub_pow_eq]
    exact isUnit_one_sub_of_norm_lt_one h
  exact ((commute_one_sub_geom_sum t m).isUnit_mul_iff.mp hprod).1

/-- The bound accompanying `isUnit_one_sub_of_norm_pow_lt_one`, in the form given by
Atkinson–Han, *Theoretical Numerical Analysis*, (2.3.6):
`‖(1 - t)⁻¹‖ ≤ (∑_{i < m} ‖t^i‖) / (1 - ‖t^m‖)`. -/
theorem norm_inverse_one_sub_le_of_norm_pow_lt_one {t : R} {m : ℕ} (h : ‖t ^ m‖ < 1) :
    ‖Ring.inverse (1 - t)‖ ≤ (∑ i ∈ Finset.range m, ‖t ^ i‖) / (1 - ‖t ^ m‖) := by
  have hunit : IsUnit (1 - t) := isUnit_one_sub_of_norm_pow_lt_one h
  have hpow : IsUnit (1 - t ^ m) := isUnit_one_sub_of_norm_lt_one h
  have h₁ : (1 - t) * ((∑ i ∈ Finset.range m, t ^ i) * Ring.inverse (1 - t ^ m)) = 1 := by
    rw [← mul_assoc, one_sub_pow_eq, Ring.mul_inverse_cancel _ hpow]
  have hkey : Ring.inverse (1 - t)
      = (∑ i ∈ Finset.range m, t ^ i) * Ring.inverse (1 - t ^ m) := by
    calc Ring.inverse (1 - t)
        = Ring.inverse (1 - t) *
            ((1 - t) * ((∑ i ∈ Finset.range m, t ^ i) * Ring.inverse (1 - t ^ m))) := by
          rw [h₁, mul_one]
      _ = (∑ i ∈ Finset.range m, t ^ i) * Ring.inverse (1 - t ^ m) := by
          rw [← mul_assoc, Ring.inverse_mul_cancel _ hunit, one_mul]
  rw [hkey]
  calc ‖(∑ i ∈ Finset.range m, t ^ i) * Ring.inverse (1 - t ^ m)‖
      ≤ ‖∑ i ∈ Finset.range m, t ^ i‖ * ‖Ring.inverse (1 - t ^ m)‖ := norm_mul_le _ _
    _ ≤ (∑ i ∈ Finset.range m, ‖t ^ i‖) * (1 / (1 - ‖t ^ m‖)) :=
        mul_le_mul (norm_sum_le _ _) (norm_inverse_one_sub_le h) (norm_nonneg _)
          (Finset.sum_nonneg fun i _ => norm_nonneg _)
    _ = (∑ i ∈ Finset.range m, ‖t ^ i‖) / (1 - ‖t ^ m‖) := by ring

end NormedRing

namespace Units

variable {R : Type*} [NormedRing R] [NormOneClass R] [CompleteSpace R]

omit [NormOneClass R] in
/-- Perturbation of a unit: `x + t` is a unit when `‖t‖ < ‖x⁻¹‖⁻¹` (Mathlib's `Units.add`). -/
theorem isUnit_add_of_norm_lt (x : Rˣ) (t : R) (h : ‖t‖ < ‖(↑x⁻¹ : R)‖⁻¹) :
    IsUnit ((x : R) + t) :=
  ⟨x.add t h, rfl⟩

omit [CompleteSpace R] in
private theorem norm_inv_mul_lt_one {x : Rˣ} {t : R} (h : ‖t‖ < ‖(↑x⁻¹ : R)‖⁻¹) :
    ‖(↑x⁻¹ : R)‖ * ‖t‖ < 1 := by
  have : Nontrivial R := NormOneClass.nontrivial
  have hpos : 0 < ‖(↑x⁻¹ : R)‖ := Units.norm_pos x⁻¹
  calc ‖(↑x⁻¹ : R)‖ * ‖t‖ < ‖(↑x⁻¹ : R)‖ * ‖(↑x⁻¹ : R)‖⁻¹ := by gcongr
    _ = 1 := mul_inv_cancel₀ hpos.ne'

omit [CompleteSpace R] in
private theorem norm_neg_inv_mul_lt_one {x : Rˣ} {t : R} (h : ‖t‖ < ‖(↑x⁻¹ : R)‖⁻¹) :
    ‖(-((↑x⁻¹ : R) * t))‖ < 1 :=
  lt_of_le_of_lt (by rw [norm_neg]; exact norm_mul_le _ _) (norm_inv_mul_lt_one h)

/-- Factorisation `(x + t)⁻¹ = (1 + x⁻¹ t)⁻¹ x⁻¹` behind the two perturbation bounds below. -/
private theorem inverse_add_eq (x : Rˣ) {t : R} (h : ‖t‖ < ‖(↑x⁻¹ : R)‖⁻¹) :
    Ring.inverse ((x : R) + t)
      = Ring.inverse (1 - -((↑x⁻¹ : R) * t)) * (↑x⁻¹ : R) := by
  have hs : IsUnit (1 - -((↑x⁻¹ : R) * t)) := isUnit_one_sub_of_norm_lt_one
    (norm_neg_inv_mul_lt_one h)
  have hfac : (x : R) + t = (x : R) * (1 - -((↑x⁻¹ : R) * t)) := by
    rw [sub_neg_eq_add, mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul]
  have hunit : IsUnit ((x : R) + t) := isUnit_add_of_norm_lt x t h
  have h₁ : ((x : R) + t) * (Ring.inverse (1 - -((↑x⁻¹ : R) * t)) * (↑x⁻¹ : R)) = 1 := by
    rw [hfac, mul_assoc, ← mul_assoc _ (Ring.inverse _), Ring.mul_inverse_cancel _ hs, one_mul,
      Units.mul_inv]
  calc Ring.inverse ((x : R) + t)
      = Ring.inverse ((x : R) + t) *
          (((x : R) + t) * (Ring.inverse (1 - -((↑x⁻¹ : R) * t)) * (↑x⁻¹ : R))) := by
        rw [h₁, mul_one]
    _ = Ring.inverse (1 - -((↑x⁻¹ : R) * t)) * (↑x⁻¹ : R) := by
        rw [← mul_assoc, Ring.inverse_mul_cancel _ hunit, one_mul]

/-- Perturbation bound for the inverse: `‖(x + t)⁻¹‖ ≤ ‖x⁻¹‖ / (1 - ‖x⁻¹‖ ‖t‖)`. -/
theorem norm_inverse_add_le (x : Rˣ) (t : R) (h : ‖t‖ < ‖(↑x⁻¹ : R)‖⁻¹) :
    ‖Ring.inverse ((x : R) + t)‖ ≤ ‖(↑x⁻¹ : R)‖ / (1 - ‖(↑x⁻¹ : R)‖ * ‖t‖) := by
  have hle : ‖(-((↑x⁻¹ : R) * t))‖ ≤ ‖(↑x⁻¹ : R)‖ * ‖t‖ := by
    rw [norm_neg]; exact norm_mul_le _ _
  rw [inverse_add_eq x h]
  calc ‖Ring.inverse (1 - -((↑x⁻¹ : R) * t)) * (↑x⁻¹ : R)‖
      ≤ ‖Ring.inverse (1 - -((↑x⁻¹ : R) * t))‖ * ‖(↑x⁻¹ : R)‖ := norm_mul_le _ _
    _ ≤ (1 / (1 - ‖(↑x⁻¹ : R)‖ * ‖t‖)) * ‖(↑x⁻¹ : R)‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact (NormedRing.norm_inverse_one_sub_le (norm_neg_inv_mul_lt_one h)).trans
          (one_div_one_sub_le_one_div_one_sub hle (norm_inv_mul_lt_one h))
    _ = ‖(↑x⁻¹ : R)‖ / (1 - ‖(↑x⁻¹ : R)‖ * ‖t‖) := by ring

/-- Perturbation bound for the change in the inverse:
`‖(x + t)⁻¹ - x⁻¹‖ ≤ ‖x⁻¹‖² ‖t‖ / (1 - ‖x⁻¹‖ ‖t‖)`. -/
theorem norm_inverse_add_sub_le (x : Rˣ) (t : R) (h : ‖t‖ < ‖(↑x⁻¹ : R)‖⁻¹) :
    ‖Ring.inverse ((x : R) + t) - ↑x⁻¹‖ ≤
      ‖(↑x⁻¹ : R)‖ ^ 2 * ‖t‖ / (1 - ‖(↑x⁻¹ : R)‖ * ‖t‖) := by
  have hle : ‖(-((↑x⁻¹ : R) * t))‖ ≤ ‖(↑x⁻¹ : R)‖ * ‖t‖ := by
    rw [norm_neg]; exact norm_mul_le _ _
  have hrw : Ring.inverse ((x : R) + t) - (↑x⁻¹ : R)
      = (Ring.inverse (1 - -((↑x⁻¹ : R) * t)) - 1) * (↑x⁻¹ : R) := by
    rw [inverse_add_eq x h, sub_mul, one_mul]
  rw [hrw]
  calc ‖(Ring.inverse (1 - -((↑x⁻¹ : R) * t)) - 1) * (↑x⁻¹ : R)‖
      ≤ ‖Ring.inverse (1 - -((↑x⁻¹ : R) * t)) - 1‖ * ‖(↑x⁻¹ : R)‖ := norm_mul_le _ _
    _ ≤ (‖(↑x⁻¹ : R)‖ * ‖t‖ / (1 - ‖(↑x⁻¹ : R)‖ * ‖t‖)) * ‖(↑x⁻¹ : R)‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact (NormedRing.norm_inverse_one_sub_sub_one_le (norm_neg_inv_mul_lt_one h)).trans
          (div_one_sub_le_div_one_sub hle (norm_inv_mul_lt_one h))
    _ = ‖(↑x⁻¹ : R)‖ ^ 2 * ‖t‖ / (1 - ‖(↑x⁻¹ : R)‖ * ‖t‖) := by ring

end Units

namespace ContinuousLinearEquiv

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace E]

/-- Two-space perturbation theorem, in the form of Atkinson–Han, *Theoretical Numerical
Analysis*, Thm 2.3.5: if `e : E ≃L F` and `‖e⁻¹‖ ‖t‖ < 1` then `e + t` is invertible with
`‖(e + t)⁻¹‖ ≤ ‖e⁻¹‖ / (1 - ‖e⁻¹‖ ‖t‖)` (Atkinson–Han (2.3.13)) and
`‖(e + t)⁻¹ - e⁻¹‖ ≤ ‖e⁻¹‖² ‖t‖ / (1 - ‖e⁻¹‖ ‖t‖)` (Atkinson–Han (2.3.14)). Completeness of `E`
suffices here, whereas Atkinson–Han Thm 2.3.5 assumes one of the two spaces complete. -/
theorem exists_symm_norm_le_of_add (e : E ≃L[𝕜] F) (t : E →L[𝕜] F)
    (h : ‖(e.symm : F →L[𝕜] E)‖ * ‖t‖ < 1) :
    ∃ e' : E ≃L[𝕜] F, (e' : E →L[𝕜] F) = (e : E →L[𝕜] F) + t ∧
      ‖(e'.symm : F →L[𝕜] E)‖ ≤
        ‖(e.symm : F →L[𝕜] E)‖ / (1 - ‖(e.symm : F →L[𝕜] E)‖ * ‖t‖) ∧
      ‖(e'.symm : F →L[𝕜] E) - (e.symm : F →L[𝕜] E)‖ ≤
        ‖(e.symm : F →L[𝕜] E)‖ ^ 2 * ‖t‖ / (1 - ‖(e.symm : F →L[𝕜] E)‖ * ‖t‖) := by
  have hnu : ‖(e.symm : F →L[𝕜] E).comp t‖ ≤ ‖(e.symm : F →L[𝕜] E)‖ * ‖t‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  have hnu1 : ‖(-((e.symm : F →L[𝕜] E).comp t) : E →L[𝕜] E)‖ < 1 := by
    rw [norm_neg]; linarith
  have hone : ‖(1 : E →L[𝕜] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  obtain ⟨v, hv⟩ : IsUnit (1 - -((e.symm : F →L[𝕜] E).comp t)) :=
    isUnit_one_sub_of_norm_lt_one hnu1
  refine ⟨(ContinuousLinearEquiv.ofUnit v).trans e, ?_, ?_, ?_⟩
  · ext x
    change e ((v : E →L[𝕜] E) x) = e x + t x
    rw [hv]
    simp
  all_goals
    have hvinv : ((↑v⁻¹ : E →L[𝕜] E)) = Ring.inverse (1 - -((e.symm : F →L[𝕜] E).comp t)) := by
      rw [← hv, Ring.inverse_unit]
    have hsymm : (((ContinuousLinearEquiv.ofUnit v).trans e).symm : F →L[𝕜] E)
        = (↑v⁻¹ : E →L[𝕜] E).comp (e.symm : F →L[𝕜] E) := by ext y; rfl
    rw [hsymm]
  · calc ‖(↑v⁻¹ : E →L[𝕜] E).comp (e.symm : F →L[𝕜] E)‖
        ≤ ‖(↑v⁻¹ : E →L[𝕜] E)‖ * ‖(e.symm : F →L[𝕜] E)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (1 / (1 - ‖(e.symm : F →L[𝕜] E)‖ * ‖t‖)) * ‖(e.symm : F →L[𝕜] E)‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          rw [hvinv]
          exact (NormedRing.norm_inverse_one_sub_le' hone hnu1).trans
            (one_div_one_sub_le_one_div_one_sub (by rwa [norm_neg]) h)
      _ = ‖(e.symm : F →L[𝕜] E)‖ / (1 - ‖(e.symm : F →L[𝕜] E)‖ * ‖t‖) := by ring
  · have hsub : (↑v⁻¹ : E →L[𝕜] E).comp (e.symm : F →L[𝕜] E) - (e.symm : F →L[𝕜] E)
        = ((↑v⁻¹ : E →L[𝕜] E) - 1).comp (e.symm : F →L[𝕜] E) := by
      ext y
      simp
    rw [hsub]
    calc ‖((↑v⁻¹ : E →L[𝕜] E) - 1).comp (e.symm : F →L[𝕜] E)‖
        ≤ ‖(↑v⁻¹ : E →L[𝕜] E) - 1‖ * ‖(e.symm : F →L[𝕜] E)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (‖(e.symm : F →L[𝕜] E)‖ * ‖t‖ / (1 - ‖(e.symm : F →L[𝕜] E)‖ * ‖t‖)) *
            ‖(e.symm : F →L[𝕜] E)‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          rw [hvinv]
          exact (NormedRing.norm_inverse_one_sub_sub_one_le' hone hnu1).trans
            (div_one_sub_le_div_one_sub (by rwa [norm_neg]) h)
      _ = ‖(e.symm : F →L[𝕜] E)‖ ^ 2 * ‖t‖ / (1 - ‖(e.symm : F →L[𝕜] E)‖ * ‖t‖) := by ring

omit [CompleteSpace E] in
/-- Consistency plus stability gives convergence: `‖v - vₙ‖ ≤ ‖Lₙ⁻¹‖ ‖(L - Lₙ) v‖` when
`L v = Lₙ vₙ`, so a uniform bound on `‖Lₙ⁻¹‖` (stability) turns the consistency error
`‖(L - Lₙ) v‖ → 0` into `vₙ → v`. -/
theorem norm_sub_le_of_apply_eq (L : E →L[𝕜] F) (Ln : E ≃L[𝕜] F) {v vn : E}
    (h : L v = Ln vn) : ‖v - vn‖ ≤ ‖(Ln.symm : F →L[𝕜] E)‖ * ‖(L - Ln) v‖ := by
  have hv : (Ln.symm : F →L[𝕜] E) ((L - (Ln : E →L[𝕜] F)) v) = vn - v := by simp [h]
  calc ‖v - vn‖ = ‖(Ln.symm : F →L[𝕜] E) ((L - (Ln : E →L[𝕜] F)) v)‖ := by
        rw [hv, norm_sub_rev]
    _ ≤ ‖(Ln.symm : F →L[𝕜] E)‖ * ‖(L - (Ln : E →L[𝕜] F)) v‖ := ContinuousLinearMap.le_opNorm _ _

end ContinuousLinearEquiv

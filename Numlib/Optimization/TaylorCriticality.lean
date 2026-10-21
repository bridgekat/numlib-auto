import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

/-!
# Compact optimality gaps

The gap is the greatest feasible value of a scalar decrement. The decrement is supplied as data,
so the same interface applies to exact and inexact polynomial models and to feasible restrictions.
Compactness and continuity enter the API where they ensure that the supremum is finite and attained.
-/

noncomputable section

namespace Optimization.TaylorCriticality

variable {E : Type*}

/-- The optimality gap of a scalar decrement on a displacement set. The compact continuous
API below ensures this real supremum is attained. -/
def gapOn (Δ : E → ℝ) (D : Set E) : ℝ := sSup (Δ '' D)

/-- A feasible decrement is below its gap whenever the decrement image is bounded above. -/
theorem le_gapOn_of_bddAbove {Δ : E → ℝ} {D : Set E}
    (hb : BddAbove (Δ '' D)) {d : E} (hd : d ∈ D) : Δ d ≤ gapOn Δ D :=
  le_csSup hb (Set.mem_image_of_mem Δ hd)

section Topological

variable [TopologicalSpace E] {Δ Γ : E → ℝ} {D S : Set E}

/-- A continuous decrement attains its gap on every nonempty compact displacement set. -/
theorem exists_eq_gapOn (hD : IsCompact D) (hne : D.Nonempty) (hΔ : ContinuousOn Δ D) :
    ∃ d ∈ D, Δ d = gapOn Δ D := by
  obtain ⟨d, hd, heq⟩ := hD.exists_sSup_image_eq hne hΔ
  exact ⟨d, hd, heq.symm⟩

/-- Every feasible decrement is bounded by the compact gap. -/
theorem le_gapOn (hD : IsCompact D) (hΔ : ContinuousOn Δ D) {d : E} (hd : d ∈ D) :
    Δ d ≤ gapOn Δ D :=
  le_gapOn_of_bddAbove (hD.image_of_continuousOn hΔ).bddAbove hd

omit [TopologicalSpace E] in
/-- A common upper bound on all feasible decrements bounds the gap. -/
theorem gapOn_le (hne : D.Nonempty) {c : ℝ} (h : ∀ d ∈ D, Δ d ≤ c) :
    gapOn Δ D ≤ c := by
  exact csSup_le (hne.image Δ) (by rintro _ ⟨d, hd, rfl⟩; exact h d hd)

/-- The compact gap is at most a scalar precisely when every feasible decrement is. -/
theorem gapOn_le_iff (hD : IsCompact D) (hne : D.Nonempty) (hΔ : ContinuousOn Δ D)
    {c : ℝ} : gapOn Δ D ≤ c ↔ ∀ d ∈ D, Δ d ≤ c :=
  ⟨fun h _ hd => (le_gapOn hD hΔ hd).trans h, gapOn_le hne⟩

/-- Enlarging the displacement set increases the gap whenever the larger image is bounded. -/
theorem gapOn_mono_set (hS : IsCompact S) (hΓ : ContinuousOn Δ S) (hne : D.Nonempty)
    (hDS : D ⊆ S) : gapOn Δ D ≤ gapOn Δ S :=
  gapOn_le hne fun _ hd => le_gapOn hS hΓ (hDS hd)

/-- Pointwise comparison of decrements passes to their compact gaps. -/
theorem gapOn_mono (hD : IsCompact D) (hne : D.Nonempty) (hΓ : ContinuousOn Γ D)
    (h : ∀ d ∈ D, Δ d ≤ Γ d) : gapOn Δ D ≤ gapOn Γ D :=
  gapOn_le hne fun _ hd => (h _ hd).trans (le_gapOn hD hΓ hd)

/-- A one-sided uniform decrement error bounds the corresponding gap error. -/
theorem gapOn_le_gapOn_add (hD : IsCompact D) (hne : D.Nonempty)
    (hΓ : ContinuousOn Γ D) {η : ℝ} (h : ∀ d ∈ D, Δ d ≤ Γ d + η) :
    gapOn Δ D ≤ gapOn Γ D + η :=
  gapOn_le hne fun _ hd => (h _ hd).trans (add_le_add (le_gapOn hD hΓ hd) le_rfl)

/-- A uniform absolute error in a pair of decrements bounds the absolute gap error. -/
theorem abs_gapOn_sub_le (hD : IsCompact D) (hne : D.Nonempty)
    (hΔ : ContinuousOn Δ D) (hΓ : ContinuousOn Γ D) {η : ℝ}
    (h : ∀ d ∈ D, |Δ d - Γ d| ≤ η) : |gapOn Δ D - gapOn Γ D| ≤ η := by
  apply abs_le.mpr
  constructor
  · have hh := gapOn_le_gapOn_add (Δ := Γ) hD hne hΔ (η := η) (fun d hd => by
      have := (abs_le.mp (h d hd)).1
      linarith)
    linarith
  · have hh := gapOn_le_gapOn_add (Δ := Δ) hD hne hΓ (η := η) (fun d hd => by
      have := (abs_le.mp (h d hd)).2
      linarith)
    linarith

variable [Zero E]

/-- Feasibility of zero and a zero decrement at zero make the compact gap nonnegative. -/
theorem gapOn_nonneg (hD : IsCompact D) (hΔ : ContinuousOn Δ D)
    (h0 : (0 : E) ∈ D) (hΔ0 : Δ 0 = 0) : 0 ≤ gapOn Δ D := by
  simpa only [hΔ0] using le_gapOn hD hΔ h0

/-- The gap vanishes precisely when no feasible displacement has positive decrement. -/
theorem gapOn_eq_zero_iff (hD : IsCompact D) (hΔ : ContinuousOn Δ D)
    (h0 : (0 : E) ∈ D) (hΔ0 : Δ 0 = 0) :
    gapOn Δ D = 0 ↔ ∀ d ∈ D, Δ d ≤ 0 := by
  constructor
  · intro h d hd
    exact (le_gapOn hD hΔ hd).trans h.le
  · intro h
    exact le_antisymm (gapOn_le ⟨0, h0⟩ h) (gapOn_nonneg hD hΔ h0 hΔ0)

end Topological

section Normed

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- On a closed ball, the gap of a negative linear functional is the radius times its dual norm.
Attainment additionally follows from compactness, for example in finite dimensions. -/
theorem gapOn_norm_linear (L : E →L[ℝ] ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    gapOn (fun d => -L d) (Metric.closedBall 0 δ) = δ * ‖L‖ := by
  have h0 : (0 : E) ∈ Metric.closedBall 0 δ := by simpa using hδ
  have hbound (d : E) (hd : d ∈ Metric.closedBall 0 δ) : -L d ≤ δ * ‖L‖ := by
    have hd' : ‖d‖ ≤ δ := by simpa using hd
    calc
      -L d ≤ ‖L d‖ := neg_le_abs _
      _ ≤ ‖L‖ * ‖d‖ := L.le_opNorm d
      _ ≤ δ * ‖L‖ := by nlinarith [norm_nonneg L]
  have hb : BddAbove ((fun d => -L d) '' Metric.closedBall 0 δ) := by
    refine ⟨δ * ‖L‖, ?_⟩
    rintro _ ⟨d, hd, rfl⟩
    exact hbound d hd
  have hle (d : E) (hd : d ∈ Metric.closedBall 0 δ) :
      -L d ≤ gapOn (fun d => -L d) (Metric.closedBall 0 δ) :=
    le_gapOn_of_bddAbove hb hd
  have hnonneg : 0 ≤ gapOn (fun d => -L d) (Metric.closedBall 0 δ) := by
    simpa only [map_zero, neg_zero] using hle 0 h0
  apply le_antisymm
  · exact gapOn_le ⟨0, h0⟩ hbound
  · by_cases hδ0 : δ = 0
    · simpa [hδ0] using hnonneg
    have hδpos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hδ0)
    have hnorm : ‖L‖ ≤ gapOn (fun d => -L d) (Metric.closedBall 0 δ) / δ := by
      apply ContinuousLinearMap.opNorm_le_of_unit_norm (div_nonneg hnonneg hδ)
      intro d hd
      have hp : δ * L d ≤ gapOn (fun d => -L d) (Metric.closedBall 0 δ) := by
        have hmem : (-δ) • d ∈ Metric.closedBall (0 : E) δ := by
          simp [norm_smul, hd, abs_of_nonneg hδ]
        simpa using hle _ hmem
      have hm : -(δ * L d) ≤ gapOn (fun d => -L d) (Metric.closedBall 0 δ) := by
        have hmem : δ • d ∈ Metric.closedBall (0 : E) δ := by
          simp [Metric.mem_closedBall, dist_zero_right, norm_smul, hd, abs_of_nonneg hδ]
        simpa using hle _ hmem
      rw [Real.norm_eq_abs, le_div_iff₀ hδpos]
      rcases le_total 0 (L d) with hd0 | hd0
      · rw [abs_of_nonneg hd0]
        nlinarith
      · rw [abs_of_nonpos hd0]
        nlinarith
    simpa [mul_comm] using (le_div_iff₀ hδpos).mp hnorm

/-- Coefficient errors control compact gaps whenever the supplied decrement difference has the
corresponding finite multilinear expansion. This applies to arbitrary Taylor coefficient families;
no assumption that they arise from derivatives of an objective is needed. -/
theorem gapOn_perturb_le {Δ Γ : E → ℝ} {D : Set E} {δ : ℝ} {q : ℕ}
    (A B : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ) (e : ℕ → ℝ)
    (hD : IsCompact D) (hne : D.Nonempty) (hΔ : ContinuousOn Δ D)
    (hΓ : ContinuousOn Γ D) (hδ : 0 ≤ δ) (hball : D ⊆ Metric.closedBall 0 δ)
    (hcoeff : ∀ i ∈ Finset.Icc 1 q, ‖A i - B i‖ ≤ e i)
    (hdiff : ∀ d ∈ D, Δ d - Γ d =
      -(∑ i ∈ Finset.Icc 1 q, (A i - B i) (fun _ => d) / (i.factorial : ℝ))) :
    |gapOn Δ D - gapOn Γ D| ≤
      ∑ i ∈ Finset.Icc 1 q, e i * δ ^ i / (i.factorial : ℝ) := by
  apply abs_gapOn_sub_le hD hne hΔ hΓ
  intro d hd
  rw [hdiff d hd, abs_neg, ← Real.norm_eq_abs]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  have hdnorm : ‖d‖ ≤ δ := by simpa using hball hd
  have hbound : ‖(A i - B i) (fun _ => d)‖ ≤ e i * δ ^ i := by
    calc
      _ ≤ ‖A i - B i‖ * ‖d‖ ^ i := by
        simpa using (A i - B i).le_opNorm (fun _ => d)
      _ ≤ e i * δ ^ i := by
        calc
          _ ≤ ‖A i - B i‖ * δ ^ i :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg d) hdnorm i)
              (norm_nonneg _)
          _ ≤ _ := mul_le_mul_of_nonneg_right (hcoeff i hi) (pow_nonneg hδ i)
  simpa only [norm_div, Real.norm_natCast] using
    div_le_div_of_nonneg_right hbound (Nat.cast_nonneg i.factorial)

end Normed

end Optimization.TaylorCriticality

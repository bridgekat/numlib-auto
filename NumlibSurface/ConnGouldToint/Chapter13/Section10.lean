import NumlibSurface.ConnGouldToint.Chapter13.Section06

/-! # Affine slices of the positive orthant -/

open Metric Set

namespace ConnGouldToint.Chapter13

/-- Algorithm 13.10.1 restricts the step to the equality nullspace and checks
the orthant clearance. Feasibility is explicit because the unsigned distance
also measures distances of exterior points. -/
def AffineOrthantBarrierTrial {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [AddCommGroup F] [Module ℝ F] (A : E →ₗ[ℝ] F) (C : Set E) (σ Δ : ℝ)
    (x s : E) (sufficient : E → Prop) : Prop :=
  ‖s‖ ≤ Δ ∧ A s = 0 ∧ BarrierAdmissibleTrial C σ x (x + s) ∧ sufficient s

/-- The distance to an affine hyperplane of nonzero normal `n` is the
positive slack divided by the normal length, as in (13.10.13). -/
theorem affineBarrier_hyperplane_distance {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {n x : E} {b : ℝ}
    (hn : n ≠ 0) (hx : 0 < b + inner ℝ n x) :
    infDist x {y : E | b + inner ℝ n y = 0} = (b + inner ℝ n x) / ‖n‖ := by
  have hnpos : 0 < ‖n‖ := norm_pos_iff.mpr hn
  let a := b + inner ℝ n x
  let y := x - (a / ‖n‖ ^ 2) • n
  have hy : y ∈ {v : E | b + inner ℝ n v = 0} := by
    change b + inner ℝ n (x - (a / ‖n‖ ^ 2) • n) = 0
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    rw [div_mul_cancel₀ _ (sq_pos_of_pos hnpos).ne']
    dsimp only [a]
    ring
  have hdist : dist x y = a / ‖n‖ := by
    rw [dist_eq_norm, show x - y = (a / ‖n‖ ^ 2) • n by simp [y], norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (div_nonneg hx.le (sq_nonneg _))]
    field_simp [hnpos.ne']
    rfl
  refine le_antisymm ((infDist_le_dist_of_mem hy).trans_eq hdist) ?_
  apply (le_infDist ⟨y, hy⟩).mpr
  intro v hv
  change b + inner ℝ n v = 0 at hv
  have he : a = inner ℝ n (x - v) := by rw [inner_sub_right]; dsimp only [a]; linarith
  rw [dist_eq_norm]
  apply (div_le_iff₀ hnpos).mpr
  change a ≤ ‖x - v‖ * ‖n‖
  rw [he, mul_comm]
  exact (le_abs_self _).trans (abs_real_inner_le_norm _ _)

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The ambient Euclidean distance to the orthant boundary in positive coordinates. -/
noncomputable def affineBarrierAmbientDistance (x : ι → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty x

private noncomputable def movableBounds (w : ι → ℝ) : Finset ι :=
  open Classical in Finset.univ.filter fun i ↦ 0 < w i

omit [Nonempty ι] in
private theorem movableBounds_nonempty (w : ι → ℝ) (hw : ∃ i, 0 < w i) :
    (movableBounds w).Nonempty := by
  classical
  obtain ⟨i, hi⟩ := hw
  exact ⟨i, by simp [movableBounds, hi]⟩

/-- The minimum in (13.10.10), after evaluating each hyperplane distance
as in (13.10.13). Constant coordinates give no hyperplane in the slice. -/
noncomputable def affineBarrierSliceDistance (w x : ι → ℝ) (hw : ∃ i, 0 < w i) : ℝ :=
  (movableBounds w).inf' (movableBounds_nonempty w hw) fun i ↦ x i / w i

/-- The geometric factor in (13.10.15) is the least positive length of a
coordinate normal projected onto the equality nullspace. -/
noncomputable def affineBarrierNormalFactor (w : ι → ℝ) (hw : ∃ i, 0 < w i) : ℝ :=
  (movableBounds w).inf' (movableBounds_nonempty w hw) w

/-- If a movable bound attains the ambient distance, (13.10.15) gives the
linear lower comparison with the relative distance. -/
theorem affineBarrier_normalFactor_mul_sliceDistance_le (w x : ι → ℝ) (hw : ∃ i, 0 < w i)
    (hx : ∀ i, 0 < x i) (hunit : ∀ i, w i ≤ 1)
    (hmovable : ∃ i, 0 < w i ∧ affineBarrierAmbientDistance x = x i) :
    affineBarrierNormalFactor w hw ∈ Ioc (0 : ℝ) 1 ∧
      affineBarrierNormalFactor w hw * affineBarrierSliceDistance w x hw ≤
        affineBarrierAmbientDistance x := by
  classical
  obtain ⟨i, hi, hdist⟩ := hmovable
  have him : i ∈ movableBounds w := by simp [movableBounds, hi]
  have hpos : 0 < affineBarrierNormalFactor w hw := by
    unfold affineBarrierNormalFactor
    rw [Finset.lt_inf'_iff]
    intro j hj
    exact (Finset.mem_filter.mp (show j ∈ Finset.univ.filter _ from hj)).2
  have hwle : affineBarrierNormalFactor w hw ≤ w i := Finset.inf'_le _ him
  have hsle : affineBarrierSliceDistance w x hw ≤ x i / w i := Finset.inf'_le _ him
  refine ⟨⟨hpos, hwle.trans (hunit i)⟩, ?_⟩
  calc
    _ ≤ affineBarrierNormalFactor w hw * (x i / w i) :=
      mul_le_mul_of_nonneg_left hsle hpos.le
    _ ≤ w i * (x i / w i) := mul_le_mul_of_nonneg_right hwle (div_nonneg (hx i).le hi.le)
    _ = x i := mul_div_cancel₀ _ hi.ne'
    _ = _ := hdist.symm

/-- Lemma 13.10.1 in orthonormal slice coordinates. The weights are the
projected normal lengths, so they are at most one. The distance comparison
is uniform over the entire positive slice. At least one bound must have a
nonzero projected normal for the relative boundary to be nonempty. -/
theorem lemma_13_10_1 (w c : ι → ℝ) (hw : ∃ i, 0 < w i)
    (hunit : ∀ i, w i ≤ 1) (hc : ∀ i, w i ≤ 0 → 0 < c i) :
    ∃ σ ∈ Ioo (0 : ℝ) 1, ∀ x : ι → ℝ, (∀ i, 0 < x i) →
      (∀ i, w i ≤ 0 → x i = c i) →
      affineBarrierAmbientDistance x ≤ affineBarrierSliceDistance w x hw ∧
      σ * min 1 (affineBarrierSliceDistance w x hw) ≤ affineBarrierAmbientDistance x := by
  classical
  let T := Finset.univ.image (fun i ↦ if 0 < w i then w i else c i)
  have hT : T.Nonempty := Finset.univ_nonempty.image _
  let σ := min (1 / 2) (T.inf' hT id)
  have hσ : σ ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨lt_min (by norm_num) ((Finset.lt_inf'_iff hT (f := id)).mpr ?_), ?_⟩
    · intro a ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      by_cases hi : 0 < w i
      · simp [hi]
      · simpa [hi] using hc i (le_of_not_gt hi)
    · exact (min_le_left _ _).trans_lt (by norm_num)
  have hσi (i : ι) : σ ≤ if 0 < w i then w i else c i :=
    (min_le_right _ _).trans (Finset.inf'_le id (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  refine ⟨σ, hσ, fun x hx hconst ↦ ⟨?_, ?_⟩⟩
  · unfold affineBarrierSliceDistance
    apply Finset.le_inf'
    intro i hi
    have hp : 0 < w i := (Finset.mem_filter.mp (show i ∈ Finset.univ.filter _ from hi)).2
    exact (Finset.inf'_le x (Finset.mem_univ i)).trans
      ((le_div_iff₀ hp).mpr (by nlinarith [mul_nonneg (hx i).le (sub_nonneg.mpr (hunit i))]))
  · unfold affineBarrierAmbientDistance
    apply Finset.le_inf'
    intro i _
    by_cases hp : 0 < w i
    · have hr : affineBarrierSliceDistance w x hw ≤ x i / w i :=
        Finset.inf'_le _ (by simp [movableBounds, hp])
      have hσw : σ ≤ w i := by simpa [hp] using hσi i
      have hpos : 0 ≤ x i / w i := div_nonneg (hx i).le hp.le
      calc
        _ ≤ σ * (x i / w i) := mul_le_mul_of_nonneg_left ((min_le_right _ _).trans hr) hσ.1.le
        _ ≤ w i * (x i / w i) := mul_le_mul_of_nonneg_right hσw hpos
        _ = x i := mul_div_cancel₀ _ hp.ne'
    · have hσc : σ ≤ c i := by simpa [hp] using hσi i
      exact ((mul_le_mul_of_nonneg_left (min_le_left _ _) hσ.1.le).trans_eq
        (mul_one _)).trans (hσc.trans_eq (hconst i (le_of_not_gt hp)).symm)

/-- Theorem 13.10.2. An ambient fraction-to-boundary test implies a
relative fraction-to-boundary test whenever the current relative distance
is at most one. -/
theorem theorem_13_10_2 (w c : ι → ℝ) (hw : ∃ i, 0 < w i)
    (hunit : ∀ i, w i ≤ 1) (hc : ∀ i, w i ≤ 0 → 0 < c i)
    {σ : ℝ} (hσ : σ ∈ Ioo (0 : ℝ) 1) :
    ∃ θ ∈ Ioo (0 : ℝ) 1, ∀ x y : ι → ℝ, (∀ i, 0 < x i) → (∀ i, 0 < y i) →
      (∀ i, w i ≤ 0 → x i = c i ∧ y i = c i) →
      σ * affineBarrierAmbientDistance x ≤ affineBarrierAmbientDistance y →
      affineBarrierSliceDistance w x hw ≤ 1 →
      θ * affineBarrierSliceDistance w x hw ≤ affineBarrierSliceDistance w y hw := by
  obtain ⟨a, ha, hb⟩ := lemma_13_10_1 w c hw hunit hc
  refine ⟨σ * a, ⟨mul_pos hσ.1 ha.1, (mul_lt_of_lt_one_right hσ.1 ha.2).trans hσ.2⟩, ?_⟩
  intro x y hx hy hconst hstep hsmall
  have hx' := (hb x hx (fun i hi ↦ (hconst i hi).1)).2
  rw [min_eq_right hsmall] at hx'
  rw [mul_assoc]
  exact ((mul_le_mul_of_nonneg_left hx' hσ.1.le).trans hstep).trans
    (hb y hy (fun i hi ↦ (hconst i hi).2)).1

end ConnGouldToint.Chapter13

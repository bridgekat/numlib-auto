import Numlib.Optimization.EvaluationComplexity.Updates

/-!
# Three-case parameter updates

The trust-region and adaptive-regularization update rules are predicates on finite
prefixes of parameter and acceptance-ratio sequences. They contain initialization,
parameter ranges and the permitted update intervals. Positivity and the iteration
counts are consequences of these rules.
-/

namespace EvaluationComplexity

/-- The trust-region radius component of an algorithm trace of length `k`. -/
structure TrustRegionRadiusUpdates (δ ρ : ℕ → ℝ) (η₁ η₂ γ₁ γ₂ γ₃ : ℝ) (k : ℕ) : Prop where
  initial_pos : 0 < δ 0
  eta1_pos : 0 < η₁
  eta1_le_eta2 : η₁ ≤ η₂
  eta2_lt_one : η₂ < 1
  gamma1_pos : 0 < γ₁
  gamma1_le_gamma2 : γ₁ ≤ γ₂
  gamma2_lt_one : γ₂ < 1
  one_lt_gamma3 : 1 < γ₃
  update : ∀ i < k,
    if η₂ ≤ ρ i then δ (i + 1) ∈ Set.Icc (δ i) (γ₃ * δ i)
    else if η₁ ≤ ρ i then δ (i + 1) ∈ Set.Icc (γ₂ * δ i) (δ i)
    else δ (i + 1) ∈ Set.Icc (γ₁ * δ i) (γ₂ * δ i)

namespace TrustRegionRadiusUpdates

variable {δ ρ : ℕ → ℝ} {η₁ η₂ γ₁ γ₂ γ₃ : ℝ} {k : ℕ}

/-- Each radius in a permitted finite trace is strictly positive. -/
theorem pos (h : TrustRegionRadiusUpdates δ ρ η₁ η₂ γ₁ γ₂ γ₃ k)
    {i : ℕ} (hi : i ≤ k) : 0 < δ i := by
  induction i with
  | zero => exact h.initial_pos
  | succ i ih =>
    have hp := ih (by omega)
    have hu := h.update i (by omega)
    split_ifs at hu with h₂ h₁
    · exact hp.trans_le hu.1
    · exact (mul_pos (h.gamma1_pos.trans_le h.gamma1_le_gamma2) hp).trans_le hu.1
    · exact (mul_pos h.gamma1_pos hp).trans_le hu.1

/-- A successful update enlarges the radius by at most `γ₃`. -/
theorem successful_le (h : TrustRegionRadiusUpdates δ ρ η₁ η₂ γ₁ γ₂ γ₃ k)
    {i : ℕ} (hi : i < k) (hs : η₁ ≤ ρ i) : δ (i + 1) ≤ γ₃ * δ i := by
  have hu := h.update i hi
  split_ifs at hu with h₂
  · exact hu.2
  · exact hu.2.trans (le_mul_of_one_le_left (h.pos (by omega)).le h.one_lt_gamma3.le)

/-- An unsuccessful update contracts the radius by at least the factor `γ₂`. -/
theorem unsuccessful_le (h : TrustRegionRadiusUpdates δ ρ η₁ η₂ γ₁ γ₂ γ₃ k)
    {i : ℕ} (hi : i < k) (hu : ¬η₁ ≤ ρ i) : δ (i + 1) ≤ γ₂ * δ i := by
  have h₂ : ¬η₂ ≤ ρ i := fun hh => hu (h.eta1_le_eta2.trans hh)
  have hh : δ (i + 1) ∈ Set.Icc (γ₁ * δ i) (γ₂ * δ i) := by
    simpa [h₂, hu] using h.update i hi
  exact hh.2

/-- A permitted update never contracts by more than the factor `γ₁`. -/
theorem gamma1_mul_le (h : TrustRegionRadiusUpdates δ ρ η₁ η₂ γ₁ γ₂ γ₃ k)
    {i : ℕ} (hi : i < k) : γ₁ * δ i ≤ δ (i + 1) := by
  have hu := h.update i hi
  have hp := (h.pos (show i ≤ k by omega)).le
  split_ifs at hu with h₂ h₁
  · exact (mul_le_of_le_one_left hp (h.gamma1_le_gamma2.trans h.gamma2_lt_one.le)).trans hu.1
  · exact (mul_le_mul_of_nonneg_right h.gamma1_le_gamma2 hp).trans hu.1
  · exact hu.1

/-- If every radius below a threshold gives a very successful iteration, the
radius stays above the smaller of its initial value and `γ₁` times that threshold. -/
theorem min_initial_threshold_le
    (h : TrustRegionRadiusUpdates δ ρ η₁ η₂ γ₁ γ₂ γ₃ k) {threshold : ℝ}
    (hgood : ∀ i < k, δ i < threshold → η₂ ≤ ρ i)
    {i : ℕ} (hi : i ≤ k) : min (δ 0) (γ₁ * threshold) ≤ δ i := by
  induction i with
  | zero => exact min_le_left _ _
  | succ i ih =>
    by_cases hsmall : δ i < threshold
    · have hu := h.update i (by omega)
      rw [ite_eq_left (hgood i (by omega) hsmall)] at hu
      exact (ih (by omega)).trans hu.1
    · exact (min_le_right _ _).trans
        ((mul_le_mul_of_nonneg_left (le_of_not_gt hsmall) h.gamma1_pos.le).trans
          (h.gamma1_mul_le (by omega)))

end TrustRegionRadiusUpdates

/-- The regularization-parameter component of an algorithm trace of length `k`. -/
structure RegularizationParameterUpdates (σ ρ : ℕ → ℝ)
    (η₁ η₂ γ₁ γ₂ γ₃ σmin : ℝ) (k : ℕ) : Prop where
  min_pos : 0 < σmin
  min_le_initial : σmin ≤ σ 0
  eta1_pos : 0 < η₁
  eta1_le_eta2 : η₁ ≤ η₂
  eta2_lt_one : η₂ < 1
  gamma1_pos : 0 < γ₁
  gamma1_lt_one : γ₁ < 1
  one_lt_gamma2 : 1 < γ₂
  gamma2_lt_gamma3 : γ₂ < γ₃
  update : ∀ i < k,
    if η₂ ≤ ρ i then σ (i + 1) ∈ Set.Icc (max σmin (γ₁ * σ i)) (σ i)
    else if η₁ ≤ ρ i then σ (i + 1) ∈ Set.Icc (σ i) (γ₂ * σ i)
    else σ (i + 1) ∈ Set.Icc (γ₂ * σ i) (γ₃ * σ i)

namespace RegularizationParameterUpdates

variable {σ ρ : ℕ → ℝ} {η₁ η₂ γ₁ γ₂ γ₃ σmin : ℝ} {k : ℕ}

/-- Every permitted parameter stays above its positive initialization floor. -/
theorem min_le (h : RegularizationParameterUpdates σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin k)
    {i : ℕ} (hi : i ≤ k) : σmin ≤ σ i := by
  induction i with
  | zero => exact h.min_le_initial
  | succ i ih =>
    have hp := ih (by omega)
    have hu := h.update i (by omega)
    split_ifs at hu with h₂ h₁
    · exact (le_max_left _ _).trans hu.1
    · exact hp.trans hu.1
    · exact hp.trans ((le_mul_of_one_le_left (h.min_pos.le.trans hp)
        h.one_lt_gamma2.le).trans hu.1)

/-- Every regularization parameter in a permitted prefix is strictly positive. -/
theorem pos (h : RegularizationParameterUpdates σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin k)
    {i : ℕ} (hi : i ≤ k) : 0 < σ i := h.min_pos.trans_le (h.min_le hi)

/-- A successful update reduces the parameter by at most the factor `γ₁`. -/
theorem successful_ge (h : RegularizationParameterUpdates σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin k)
    {i : ℕ} (hi : i < k) (hs : η₁ ≤ ρ i) : γ₁ * σ i ≤ σ (i + 1) := by
  have hu := h.update i hi
  split_ifs at hu with h₂
  · exact (le_max_right _ _).trans hu.1
  · exact (mul_le_of_le_one_left (h.pos (by omega)).le h.gamma1_lt_one.le).trans hu.1

/-- An unsuccessful update increases the parameter by at least `γ₂`. -/
theorem unsuccessful_ge (h : RegularizationParameterUpdates σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin k)
    {i : ℕ} (hi : i < k) (hu : ¬η₁ ≤ ρ i) : γ₂ * σ i ≤ σ (i + 1) := by
  have h₂ : ¬η₂ ≤ ρ i := fun hh => hu (h.eta1_le_eta2.trans hh)
  have hh : σ (i + 1) ∈ Set.Icc (γ₂ * σ i) (γ₃ * σ i) := by
    simpa [h₂, hu] using h.update i hi
  exact hh.1

/-- If reaching a threshold guarantees a very successful iteration, all
parameters are bounded by the larger of their initial value and `γ₃` times the
threshold. This is a consequence of the update mechanism, not a run invariant
that an algorithm must assume. -/
theorem le_max_initial_threshold
    (h : RegularizationParameterUpdates σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin k)
    {threshold : ℝ} (hgood : ∀ i < k, threshold ≤ σ i → η₂ ≤ ρ i)
    {i : ℕ} (hi : i ≤ k) : σ i ≤ max (σ 0) (γ₃ * threshold) := by
  induction i with
  | zero => exact le_max_left _ _
  | succ i ih =>
    have hp := ih (by omega)
    have hu := h.update i (by omega)
    by_cases h₂ : η₂ ≤ ρ i
    · simp only [h₂, ↓reduceIte] at hu
      exact hu.2.trans hp
    · have hsmall : σ i < threshold := lt_of_not_ge (fun hh => h₂ (hgood i (by omega) hh))
      have hγ₃ : 0 < γ₃ := lt_trans (lt_trans zero_lt_one h.one_lt_gamma2)
        h.gamma2_lt_gamma3
      have hup : σ (i + 1) ≤ γ₃ * σ i := by
        split_ifs at hu with h₁
        · exact hu.2.trans (mul_le_mul_of_nonneg_right h.gamma2_lt_gamma3.le
            (h.pos (by omega)).le)
        · exact hu.2
      exact hup.trans ((mul_le_mul_of_nonneg_left hsmall.le hγ₃.le).trans
        (le_max_right _ _))

end RegularizationParameterUpdates

end EvaluationComplexity

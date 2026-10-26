import NumlibSurface.CartisGouldToint.Chapter09.Section03

/-!
# Cartis–Gould–Toint §9.4: The trust-region subproblem

Surface file for [cartis2022evaluation] §9.4: initial bounds (9.4.1) on the multiplier of the
trust-region subproblem (8.1.2), and the bounds (9.4.5)–(9.4.7) on its optimal value
`m_Δ = min_{‖s‖_M ≤ Δ} m(s)` used for early termination of criticality tests. The trust-region
analogues of Algorithms 9.2.1 and 8.3.2 are `CartisGouldToint.Chapter09.algorithm_9_2_1` (with the
trust-region sets) and `CartisGouldToint.Chapter08.algorithm_8_3_2`.

## Corrections to the source

* (9.4.5) claims `m_{Δ₂} ≤ m_{Δ₁}` *if and only if* `Δ₂ ≥ Δ₁`; only the implication holds (for
  `g = 0`, `H = 0`, `m_Δ = 0` for all `Δ`).
* Not formalized: the tests (9.4.2)–(9.4.4) (they are uses of the bounds) and the Gertz–Gill
  approximate-solution criterion (9.4.8) quoted in the notes.
* (9.4.6), (9.4.7) hold for any `s_{Δ⁺}` (resp. `s_{Δ⁻}`) on the sphere of radius `Δ⁺` (resp.
  `Δ⁻`), not only for minimizers, and for `Δ ≤ Δ⁺` (resp. `Δ⁻ ≤ Δ`).
-/

open Matrix Set Metric
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter09

open Subproblem CartisGouldToint.Chapter08

variable {n : ℕ} {g : EuclideanSpace ℝ (Fin n)} {H M : Matrix (Fin n) (Fin n) ℝ}

/-- **Bounds on the multiplier, trust region** ([cartis2022evaluation] (9.4.1)). Let `Δ > 0` and
`s*` a global minimizer of (8.1.2) on the boundary, `‖s*‖_M = Δ`, with multiplier `λ*`
(`IsTrustRegionKKT`). Then `‖g‖_{M⁻¹}/Δ - λₙ ≤ λ* ≤ ‖g‖_{M⁻¹}/Δ - λ₁`, and the same with any outer
bounds `λ₁ᴸ ≤ λ₁`, `λₙᵁ ≥ λₙ`. -/
theorem lambdaStar_bounds_9_4_1 (hH : H.IsHermitian) (hM : M.PosDef) {Δ : ℝ} (hΔ : 0 < Δ)
    {s : EuclideanSpace ℝ (Fin n)} {lamStar : ℝ} (hkkt : IsTrustRegionKKT g H M Δ s lamStar)
    (hsΔ : mNorm M s = Δ) :
    mNorm M⁻¹ g / Δ - rightmostPencil hH hM ≤ lamStar ∧
      lamStar ≤ mNorm M⁻¹ g / Δ - leftmostPencil hH hM ∧
      ∀ l₁ lₙ : ℝ, l₁ ≤ leftmostPencil hH hM → rightmostPencil hH hM ≤ lₙ →
        mNorm M⁻¹ g / Δ - lₙ ≤ lamStar ∧ lamStar ≤ mNorm M⁻¹ g / Δ - l₁ := by
  have hT := isSymmetric_scaledOp (hM := hM) hH
  have hμ := (isTrustRegionKKT_iff_scaled hM hΔ).1 hkkt
  have hne : Nonempty (Fin n) := by
    by_contra h
    rw [not_nonempty_iff] at h
    rw [Subsingleton.elim s 0, mNorm, inner_zero_left, Real.sqrt_zero] at hsΔ
    exact hΔ.ne hsΔ
  have hl : -leftmost hT ≤ lamStar := (isPositive_add_smul_iff (hH := hT) lamStar).1 hμ.isPositive
  obtain ⟨h1, h2⟩ := norm_add_smul_apply_bounds (hH := hT) hl (toScaled hM s)
  rw [hμ.shifted, norm_neg, ← mNorm_eq_norm_toScaled hM, hsΔ] at h1 h2
  rw [mNorm_inv_eq_norm_scaledGrad hM, leftmostPencil_eq, rightmostPencil_eq]
  have hA : ‖scaledGrad hM g‖ / Δ - rightmost hT ≤ lamStar := by
    rw [sub_le_iff_le_add, div_le_iff₀ hΔ]; linarith
  have hB : lamStar ≤ ‖scaledGrad hM g‖ / Δ - leftmost hT := by
    rw [le_sub_iff_add_le, le_div_iff₀ hΔ]; linarith
  exact ⟨hA, hB, fun l₁ lₙ hl₁ hlₙ => ⟨by linarith, by linarith⟩⟩

/-- The **optimal value** `m_Δ = min_{‖s‖_M ≤ Δ} m(s)` of the trust-region subproblem (8.1.2)
([cartis2022evaluation] §9.4.2). -/
noncomputable def trValue (g : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ)
    (Δ : ℝ) : ℝ :=
  sInf (model g H '' {s | mNorm M s ≤ Δ})

/-- The optimal value is that of the operator subproblem in the `M`-inner product space. -/
theorem trValue_eq (hM : M.PosDef) (Δ : ℝ) :
    trValue g H M Δ = trustRegionValue (scaledGrad hM g) (scaledOp H hM) Δ := by
  rw [trValue, trustRegionValue]
  congr 1
  ext y
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨toScaled hM s, by rwa [mem_closedBall_zero_iff, ← mNorm_eq_norm_toScaled hM],
      (model_eq_quadModel hM s).symm⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨s, rfl⟩ := (toScaled hM).surjective x
    exact ⟨s, by rwa [mem_ofPred_eq, mNorm_eq_norm_toScaled hM, ← mem_closedBall_zero_iff],
      model_eq_quadModel hM s⟩

/-- **Bounds on the optimal value of the trust-region subproblem** ([cartis2022evaluation]
(9.4.5)–(9.4.7)). For `Δ ≥ 0` the value `m_Δ` is attained and `m_Δ ≤ 0`; (9.4.5) `m_Δ` is
antitone in `Δ` (the book's converse is false); (9.4.6) for `Δ ≤ Δ⁺` and `‖s_{Δ⁺}‖_M = Δ⁺`,
`m_{Δ⁺} ≤ m_Δ ≤ m((Δ/Δ⁺) s_{Δ⁺})`; (9.4.7) for `Δ⁻ ≤ Δ` and `‖s_{Δ⁻}‖_M = Δ⁻`,
`m_Δ ≤ min(m((Δ/Δ⁻) s_{Δ⁻}), m_{Δ⁻})`; and for `λ ∈ 𝓛 ∪ 𝓖` (`λ > λₛ`) with `Δ(λ) = ‖s(λ)‖_M`,
`m_{Δ(λ)} = ½ (⟪g, s(λ)⟫ - λ Δ(λ)²)`. -/
theorem optimalValue_bounds_9_4_6 (hH : H.IsHermitian) (hM : M.PosDef) :
    (∀ Δ : ℝ, 0 ≤ Δ → (∃ s, IsTrustRegionSolution g H M Δ s ∧ model g H s = trValue g H M Δ) ∧
      trValue g H M Δ ≤ 0) ∧
    (∀ Δ₁ Δ₂ : ℝ, 0 ≤ Δ₁ → Δ₁ ≤ Δ₂ → trValue g H M Δ₂ ≤ trValue g H M Δ₁) ∧
    (∀ (Δ Δp : ℝ) (sp : EuclideanSpace ℝ (Fin n)), 0 ≤ Δ → Δ ≤ Δp → mNorm M sp = Δp →
      trValue g H M Δp ≤ trValue g H M Δ ∧ trValue g H M Δ ≤ model g H ((Δ / Δp) • sp)) ∧
    (∀ (Δ Δm : ℝ) (sm : EuclideanSpace ℝ (Fin n)), 0 ≤ Δm → Δm ≤ Δ → mNorm M sm = Δm →
      trValue g H M Δ ≤ min (model g H ((Δ / Δm) • sm)) (trValue g H M Δm)) ∧
    (∀ lam, lambdaS hH hM < lam →
      trValue g H M (mNorm M (stepOf g H M lam)) =
        1 / 2 * (⟪g, stepOf g H M lam⟫ - lam * mNorm M (stepOf g H M lam) ^ 2)) := by
  have hT := isSymmetric_scaledOp (hM := hM) hH
  have hmodel : ∀ (c : ℝ) (v : EuclideanSpace ℝ (Fin n)),
      quadModel (scaledGrad hM g) (scaledOp H hM) (c • toScaled hM v) = model g H (c • v) :=
    fun c v => by rw [← map_smul, model_eq_quadModel hM]
  refine ⟨fun Δ hΔ => ⟨?_, ?_⟩, fun Δ₁ Δ₂ h₁ h => ?_, fun Δ Δp sp hΔ h hsp => ?_,
    fun Δ Δm sm hΔm h hsm => ?_, fun lam hlam => ?_⟩
  · obtain ⟨x, hx, hmin⟩ := exists_isMinOn_closedBall (scaledGrad hM g) (scaledOp H hM) hΔ
    obtain ⟨s, rfl⟩ := (toScaled hM).surjective x
    refine ⟨s, (isTrustRegionSolution_iff_scaled hM).2 ⟨hx, hmin⟩, ?_⟩
    rw [trValue_eq hM, hmin.trustRegionValue_eq hx, model_eq_quadModel hM]
  · rw [trValue_eq hM]
    exact (trustRegionValue_le (by simpa using hΔ)).trans_eq (quadModel_zero _ _)
  · rw [trValue_eq hM, trValue_eq hM]; exact trustRegionValue_antitone h₁ h
  · have hn : ‖toScaled hM sp‖ = Δp := by rw [← mNorm_eq_norm_toScaled hM]; exact hsp
    have := trustRegionValue_mem_Icc (g := scaledGrad hM g) (H := scaledOp H hM) hΔ h hn
    rw [trValue_eq hM, trValue_eq hM, ← hmodel]
    exact this
  · have hn : ‖toScaled hM sm‖ = Δm := by rw [← mNorm_eq_norm_toScaled hM]; exact hsm
    have := trustRegionValue_le_min (g := scaledGrad hM g) (H := scaledOp H hM) hΔm h hn
    rw [trValue_eq hM, trValue_eq hM, ← hmodel]
    exact this
  · have hl := neg_leftmost_lt_of_lambdaS_lt hH hM hlam
    have hl0 : 0 ≤ lam := (lambdaS_nonneg hH hM).trans hlam.le
    have hsh := add_smul_stepOf (g := g) hH hM hl
    have hsh' := (add_smul_scaledOp_toScaled_eq_neg_iff (hM := hM) lam g _).2 hsh
    have hμ : IsTrustRegionMultiplier (scaledGrad hM g) (scaledOp H hM)
        (mNorm M (stepOf g H M lam)) (toScaled hM (stepOf g H M lam)) lam :=
      ⟨hl0, hsh', isPositive_add_smul_of_le (hH := hT) hl.le,
        by rw [mNorm_eq_norm_toScaled hM, sub_self, mul_zero]⟩
    have hn : ‖toScaled hM (stepOf g H M lam)‖ ≤ mNorm M (stepOf g H M lam) :=
      (mNorm_eq_norm_toScaled hM _).ge
    rw [trValue_eq hM, (hμ.isMinOn hT).trustRegionValue_eq hn, quadModel_eq_of_shifted hsh',
      inner_scaledGrad_toScaled, ← mNorm_eq_norm_toScaled hM]

end CartisGouldToint.Chapter09

import Numlib.Optimization.ModelBased.QuadraticModel
import NumlibSurface.CartisGouldToint.Chapter09.Section03

/-!
# Cartis–Gould–Toint §9.4: The trust-region subproblem

Surface file for [cartis2022evaluation] §9.4: initial bounds (9.4.1) on the multiplier of the
trust-region subproblem (8.1.2), and the bounds (9.4.5)–(9.4.7) on its optimal value
`m_Δ = min_{‖s‖_M ≤ Δ} m(s)` used for early termination of criticality tests. The trust-region
analogues of Algorithms 9.2.1 and 8.3.2 are `CartisGouldToint.Chapter09.algorithm_9_2_1` (with the
trust-region sets) and `CartisGouldToint.Chapter08.algorithm_8_3_2`.

## Main results

* `lambdaStar_bounds_9_4_1` — (9.4.1).
* `optimalValue_bounds_9_4_6` — (9.4.5)–(9.4.7) and `m_{Δ(λ)}` for `λ ∈ 𝓛 ∪ 𝓖`; its parts
  without symmetry of `H` are `exists_trValue_eq`, `trValue_antitone` and `trValue_le_min`.
* `trValue_of_posDef` — the interior case `H ≻ 0`, `‖H⁻¹ g‖_M ≤ Δ`.
* `taylorMeasure_two_eq_neg_trValue_of_contDiffAt`, `test_9_4_2_iff_of_contDiffAt` —
  `φ^Δ_{f,2}(x) = -m_Δ` for `g = ∇f(x)`, `H = ∇²f(x)`, and the tests (9.4.2) as (9.4.3)–(9.4.4)
  (`taylorMeasure_two_eq_neg_trValue`, `test_9_4_2_iff` for any `g`, `H` with
  `T_{f,2}(x, s) = f(x) + m(s)`).
* `test_9_4_3_of_9_4_6`, `test_9_4_4_of_9_4_6`, `test_9_4_3_of_9_4_7` — sufficient conditions
  for (9.4.3) (with a feasible exemplar `s`, `m(s) ≤ mᴸ`) and (9.4.4).
* `tests_9_4_3_9_4_4_of_setL`, `test_9_4_3_of_setG`, `trValue_ge_of_setG` — the same with the
  radii `Δ(λ)` for `λ ∈ 𝓛` or `λ ∈ 𝓖`, and the bound of footnote 65.

## Corrections to the source

* (9.4.5) claims `m_{Δ₂} ≤ m_{Δ₁}` *if and only if* `Δ₂ ≥ Δ₁`; only the implication holds (for
  `g = 0`, `H = 0`, `m_Δ = 0` for all `Δ`).
* (9.4.6), (9.4.7) hold for any `s_{Δ⁺}` (resp. `s_{Δ⁻}`) on the sphere of radius `Δ⁺` (resp.
  `Δ⁻`), not only for minimizers, and for `Δ ≤ Δ⁺` (resp. `Δ⁻ ≤ Δ`).

## Conventions

The measure `φ^Δ_{f,2}(x)` of (9.4.2) is `Optimization.taylorMeasure (ftaylorSeries ℝ f x) 2 Δ univ`
and uses the Euclidean norm, so it is compared with `m_Δ` for `M = I`; the Hessian matrix
`∇²f(x)` is `Optimization.hessianMatrix f x`.

## Not formalized

The Gertz–Gill approximate-solution criterion (9.4.8) quoted in the notes, and the closing advice
to stop Algorithm 9.2.1 once (9.4.3) or (9.4.4) holds (a heuristic use of the tests above).
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

/-- The optimal value is attained for `Δ ≥ 0`: some global minimizer `s` of (8.1.2) has
`m(s) = m_Δ`. -/
theorem exists_trValue_eq (hM : M.PosDef) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    ∃ s, IsTrustRegionSolution g H M Δ s ∧ model g H s = trValue g H M Δ := by
  obtain ⟨x, hx, hmin⟩ := exists_isMinOn_closedBall (scaledGrad hM g) (scaledOp H hM) hΔ
  obtain ⟨s, rfl⟩ := (toScaled hM).surjective x
  refine ⟨s, (isTrustRegionSolution_iff_scaled hM).2 ⟨hx, hmin⟩, ?_⟩
  rw [trValue_eq hM, hmin.trustRegionValue_eq hx, model_eq_quadModel hM]

/-- (9.4.5) of [cartis2022evaluation], the valid direction: `m_Δ` is antitone in `Δ ≥ 0`. -/
theorem trValue_antitone (hM : M.PosDef) {Δ₁ Δ₂ : ℝ} (h₁ : 0 ≤ Δ₁) (h : Δ₁ ≤ Δ₂) :
    trValue g H M Δ₂ ≤ trValue g H M Δ₁ := by
  rw [trValue_eq hM, trValue_eq hM]; exact trustRegionValue_antitone h₁ h

/-- (9.4.7) of [cartis2022evaluation]: for `0 ≤ Δ⁻ ≤ Δ` and `‖s⁻‖_M = Δ⁻`,
`m_Δ ≤ min(m((Δ/Δ⁻) s⁻), m_{Δ⁻})`. -/
theorem trValue_le_min (hM : M.PosDef) {Δ Δm : ℝ} {sm : EuclideanSpace ℝ (Fin n)}
    (hΔm : 0 ≤ Δm) (h : Δm ≤ Δ) (hsm : mNorm M sm = Δm) :
    trValue g H M Δ ≤ min (model g H ((Δ / Δm) • sm)) (trValue g H M Δm) := by
  have hn : ‖toScaled hM sm‖ = Δm := by rw [← mNorm_eq_norm_toScaled hM]; exact hsm
  have := trustRegionValue_le_min (g := scaledGrad hM g) (H := scaledOp H hM) hΔm h hn
  rwa [← trValue_eq hM, ← trValue_eq hM, ← map_smul, ← model_eq_quadModel hM] at this

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
  · exact exists_trValue_eq hM hΔ
  · rw [trValue_eq hM]
    exact (trustRegionValue_le (by simpa using hΔ)).trans_eq (quadModel_zero _ _)
  · exact trValue_antitone hM h₁ h
  · have hn : ‖toScaled hM sp‖ = Δp := by rw [← mNorm_eq_norm_toScaled hM]; exact hsp
    have := trustRegionValue_mem_Icc (g := scaledGrad hM g) (H := scaledOp H hM) hΔ h hn
    rw [trValue_eq hM, trValue_eq hM, ← hmodel]
    exact this
  · exact trValue_le_min hM hΔm h hsm
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

/-! ### Early termination: the tests (9.4.2)–(9.4.4) -/

/-- **The value of the trust-region subproblem for a positive definite `H`**
([cartis2022evaluation] §9.4.2, after (9.4.5)): if `H ≻ 0` and `‖H⁻¹ g‖_M ≤ Δ`, then
`s_Δ = -H⁻¹ g` is the unique global minimizer of (8.1.2) and `m_Δ = -½ ⟪g, H⁻¹ g⟫`. -/
theorem trValue_of_posDef (hM : M.PosDef) (hpos : H.PosDef) {Δ : ℝ}
    (hs : mNorm M (toEuclideanLin H⁻¹ g) ≤ Δ) :
    IsTrustRegionSolution g H M Δ (-toEuclideanLin H⁻¹ g) ∧
      (∀ u, IsTrustRegionSolution g H M Δ u → u = -toEuclideanLin H⁻¹ g) ∧
      trValue g H M Δ = -(1 / 2) * ⟪g, toEuclideanLin H⁻¹ g⟫ := by
  have hH : H.IsHermitian := hpos.isHermitian
  have hT := isSymmetric_scaledOp (hM := hM) hH
  set s := -toEuclideanLin H⁻¹ g
  have hstep : stepOf g H M 0 = s := by rw [stepOf, zero_smul, add_zero, map_neg]
  have hns : ‖toScaled hM s‖ ≤ Δ := by
    rw [← mNorm_eq_norm_toScaled hM]
    simpa [s, mNorm, inner_neg_left, inner_neg_right] using hs
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · have hΔ : 0 ≤ Δ := (mNorm_nonneg _ _).trans hs
    have hsol : ∀ u, IsTrustRegionSolution g H M Δ u := fun u =>
      ⟨by rw [Subsingleton.elim u 0, mNorm, inner_zero_left, Real.sqrt_zero]; exact hΔ,
        fun v _ => by rw [Subsingleton.elim u v]⟩
    refine ⟨hsol _, fun u _ => Subsingleton.elim _ _, ?_⟩
    obtain ⟨v, hv, hval⟩ := exists_trValue_eq (g := g) (H := H) hM hΔ
    rw [← hval, Subsingleton.elim v 0, Subsingleton.elim g 0]
    simp [model]
  · have hc := (posDef_add_smul_iff_isSymmetricCoercive (hM := hM) 0).1 (by simpa using hpos)
    have hl : -leftmost hT < 0 := (isSymmetricCoercive_add_smul_iff (hH := hT) 0).1 hc
    have hsh := add_smul_stepOf (g := g) hH hM hl
    have hsh' := (add_smul_scaledOp_toScaled_eq_neg_iff (hM := hM) 0 g _).2 hsh
    rw [hstep] at hsh'
    have hμ : IsTrustRegionMultiplier (scaledGrad hM g) (scaledOp H hM) Δ (toScaled hM s) 0 :=
      ⟨le_rfl, hsh', isPositive_add_smul_of_le (hH := hT) hl.le, zero_mul _⟩
    have hmin := hμ.isMinOn hT
    have hsol : IsTrustRegionSolution g H M Δ s :=
      (isTrustRegionSolution_iff_scaled hM).2 ⟨hns, hmin⟩
    refine ⟨hsol, fun u hu => ?_, ?_⟩
    · obtain ⟨hu1, hu2⟩ := (isTrustRegionSolution_iff_scaled hM).1 hu
      exact (toScaled hM).injective
        (eq_of_isMinOn_closedBall_of_posDef hT hμ hns hc.isCoercive hu1 hu2)
    · rw [trValue_eq hM, hmin.trustRegionValue_eq hns, quadModel_eq_of_shifted hsh',
        inner_scaledGrad_toScaled, zero_mul, sub_zero, inner_neg_right]
      ring

/-- **The measure `φ^Δ_{f,2}` as an optimal value** ([cartis2022evaluation] §9.4.2, before
(9.4.2)): if the second-order Taylor model of `f` at `x` is `T_{f,2}(x, s) = f(x) + m(s)` (that
is, `m` is the model (8.1.1) with `g = ∇f(x)` and `H = ∇²f(x)`), then
`φ^Δ_{f,2}(x) = f(x) - min_{‖s‖ ≤ Δ} T_{f,2}(x, s) = -m_Δ` with `M = I`. -/
theorem taylorMeasure_two_eq_neg_trValue {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hT : ∀ s, taylorPolynomial f 2 x s = f x + model g H s)
    (Δ : ℝ) :
    Optimization.taylorMeasure (ftaylorSeries ℝ f x) 2 Δ univ = -trValue g H 1 Δ := by
  rw [Optimization.taylorMeasure_eq_sSup, inter_univ, trValue, ← Real.sSup_neg]
  congr 1
  ext y
  simp only [mem_image, mem_neg, mem_closedBall_zero_iff, mem_ofPred_eq, mNorm_one]
  refine exists_congr fun d => and_congr_right fun _ => ?_
  rw [FormalMultilinearSeries.taylorDecrement, ← taylorPolynomial_eq_taylorSum,
    taylorPolynomial_zero_right, hT]
  constructor <;> intro h <;> linarith

/-- **The tests (9.4.2) as (9.4.3)–(9.4.4)** ([cartis2022evaluation] §9.4.2): with
`T_{f,2}(x, s) = f(x) + m(s)`, `φ^Δ_{f,2}(x) ≥ φᵁ` iff `m_Δ ≤ mᴸ` and `φ^Δ_{f,2}(x) ≤ φᴸ` iff
`m_Δ ≥ mᵁ`, for `mᴸ = -φᵁ` and `mᵁ = -φᴸ` (and `M = I`). -/
theorem test_9_4_2_iff {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hT : ∀ s, taylorPolynomial f 2 x s = f x + model g H s) (Δ φL φU : ℝ) :
    (φU ≤ Optimization.taylorMeasure (ftaylorSeries ℝ f x) 2 Δ univ ↔
        trValue g H 1 Δ ≤ -φU) ∧
      (Optimization.taylorMeasure (ftaylorSeries ℝ f x) 2 Δ univ ≤ φL ↔
        -φL ≤ trValue g H 1 Δ) := by
  rw [taylorMeasure_two_eq_neg_trValue hT]
  exact ⟨le_neg, neg_le⟩

/-- For `f` twice differentiable at `x`, `T_{f,2}(x, s) = f(x) + m(s)` with `g = ∇f(x)` and
`H = ∇²f(x)` (the matrix `Optimization.hessianMatrix f x`). -/
theorem taylorPolynomial_two_eq_model {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hf : ContDiffAt ℝ 2 f x) (s : EuclideanSpace ℝ (Fin n)) :
    taylorPolynomial f 2 x s =
      f x + model (gradient f x) (Optimization.hessianMatrix f x) s := by
  rw [Optimization.taylorPolynomial_two_eq_quadModel hf, quadModel_def, model,
    Optimization.toEuclideanLin_hessianMatrix hf]
  rfl

/-- **The measure `φ^Δ_{f,2}` as an optimal value** ([cartis2022evaluation] §9.4.2, before
(9.4.2)), in the book's form: for `f` twice differentiable at `x`,
`φ^Δ_{f,2}(x) = -min_{‖s‖ ≤ Δ} m(s)` with `g = ∇f(x)`, `H = ∇²f(x)` and `M = I`. -/
theorem taylorMeasure_two_eq_neg_trValue_of_contDiffAt {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hf : ContDiffAt ℝ 2 f x) (Δ : ℝ) :
    Optimization.taylorMeasure (ftaylorSeries ℝ f x) 2 Δ univ =
      -trValue (gradient f x) (Optimization.hessianMatrix f x) 1 Δ :=
  taylorMeasure_two_eq_neg_trValue (taylorPolynomial_two_eq_model hf) Δ

/-- **The tests (9.4.2) as (9.4.3)–(9.4.4)** ([cartis2022evaluation] §9.4.2), in the book's form:
for `f` twice differentiable at `x`, `g = ∇f(x)`, `H = ∇²f(x)` and `M = I`,
`φ^Δ_{f,2}(x) ≥ φᵁ` iff `m_Δ ≤ -φᵁ` and `φ^Δ_{f,2}(x) ≤ φᴸ` iff `m_Δ ≥ -φᴸ`. -/
theorem test_9_4_2_iff_of_contDiffAt {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hf : ContDiffAt ℝ 2 f x) (Δ φL φU : ℝ) :
    (φU ≤ Optimization.taylorMeasure (ftaylorSeries ℝ f x) 2 Δ univ ↔
        trValue (gradient f x) (Optimization.hessianMatrix f x) 1 Δ ≤ -φU) ∧
      (Optimization.taylorMeasure (ftaylorSeries ℝ f x) 2 Δ univ ≤ φL ↔
        -φL ≤ trValue (gradient f x) (Optimization.hessianMatrix f x) 1 Δ) :=
  test_9_4_2_iff (taylorPolynomial_two_eq_model hf) Δ φL φU

/-- `‖(Δ/Δ⁺) s⁺‖_M ≤ Δ` when `‖s⁺‖_M = Δ⁺` and `0 ≤ Δ`, `0 ≤ Δ⁺` (equality unless `Δ⁺ = 0`). -/
theorem mNorm_div_smul_le (hM : M.PosDef) {Δ Δ' : ℝ} (hΔ : 0 ≤ Δ) (hΔ' : 0 ≤ Δ')
    {s : EuclideanSpace ℝ (Fin n)} (hs : mNorm M s = Δ') : mNorm M ((Δ / Δ') • s) ≤ Δ := by
  rw [mNorm_eq_norm_toScaled hM, map_smul, norm_smul, ← mNorm_eq_norm_toScaled hM, hs,
    Real.norm_eq_abs, abs_of_nonneg (div_nonneg hΔ hΔ')]
  rcases hΔ'.eq_or_lt with rfl | hpos
  · simpa using hΔ
  · rw [div_mul_cancel₀ _ hpos.ne']

/-- **Test (9.4.3) from (9.4.6)** ([cartis2022evaluation] §9.4.2): if `0 ≤ Δ ≤ Δ⁺`,
`‖s⁺‖_M = Δ⁺` and `m(α⁺ s⁺) ≤ mᴸ` with `α⁺ = Δ/Δ⁺`, then `m_Δ ≤ mᴸ`, and `α⁺ s⁺` is a feasible
exemplar: `‖α⁺ s⁺‖_M ≤ Δ` with `m(α⁺ s⁺) ≤ mᴸ`. -/
theorem test_9_4_3_of_9_4_6 (hM : M.PosDef) {Δ Δp mL : ℝ} {sp : EuclideanSpace ℝ (Fin n)}
    (hΔ : 0 ≤ Δ) (h : Δ ≤ Δp) (hsp : mNorm M sp = Δp) (hL : model g H ((Δ / Δp) • sp) ≤ mL) :
    trValue g H M Δ ≤ mL ∧ mNorm M ((Δ / Δp) • sp) ≤ Δ := by
  have hn : ‖toScaled hM sp‖ = Δp := by rw [← mNorm_eq_norm_toScaled hM]; exact hsp
  have := (trustRegionValue_mem_Icc (g := scaledGrad hM g) (H := scaledOp H hM) hΔ h hn).2
  rw [← trValue_eq hM, ← map_smul, ← model_eq_quadModel hM] at this
  exact ⟨this.trans hL, mNorm_div_smul_le hM hΔ (hΔ.trans h) hsp⟩

/-- **Test (9.4.4) from (9.4.6)** ([cartis2022evaluation] §9.4.2): if `0 ≤ Δ ≤ Δ⁺` and
`m_{Δ⁺} ≥ mᵁ`, then `m_Δ ≥ mᵁ`. -/
theorem test_9_4_4_of_9_4_6 (hM : M.PosDef) {Δ Δp mU : ℝ} (hΔ : 0 ≤ Δ) (h : Δ ≤ Δp)
    (hU : mU ≤ trValue g H M Δp) : mU ≤ trValue g H M Δ :=
  hU.trans (trValue_antitone hM hΔ h)

/-- **Test (9.4.3) from (9.4.7)** ([cartis2022evaluation] §9.4.2): if `0 ≤ Δ⁻ ≤ Δ`,
`‖s⁻‖_M = Δ⁻` and `min(m(α⁻ s⁻), m_{Δ⁻}) ≤ mᴸ` with `α⁻ = Δ/Δ⁻`, then `m_Δ ≤ mᴸ`, with a feasible
exemplar `s`, `‖s‖_M ≤ Δ` and `m(s) ≤ mᴸ` (`α⁻ s⁻` or a minimizer for the radius `Δ⁻`). -/
theorem test_9_4_3_of_9_4_7 (hM : M.PosDef) {Δ Δm mL : ℝ}
    {sm : EuclideanSpace ℝ (Fin n)} (hΔm : 0 ≤ Δm) (h : Δm ≤ Δ) (hsm : mNorm M sm = Δm)
    (hL : min (model g H ((Δ / Δm) • sm)) (trValue g H M Δm) ≤ mL) :
    trValue g H M Δ ≤ mL ∧ ∃ s, mNorm M s ≤ Δ ∧ model g H s ≤ mL := by
  refine ⟨(trValue_le_min hM hΔm h hsm).trans hL, ?_⟩
  rcases min_le_iff.1 hL with h1 | h2
  · exact ⟨_, mNorm_div_smul_le hM (hΔm.trans h) hΔm hsm, h1⟩
  · obtain ⟨s, hs, hval⟩ := exists_trValue_eq (g := g) (H := H) hM hΔm
    exact ⟨s, hs.1.trans h, hval ▸ h2⟩

/-- **The tests from `λ⁺ ∈ 𝓛`** ([cartis2022evaluation] §9.4.2, after (9.4.7)): for
`λ⁺ ∈ 𝓛`, `Δ⁺ = Δ(λ⁺) = ‖s(λ⁺)‖_M ≥ Δ` is a suitable radius for (9.4.6), with the computable
value `m_{Δ⁺} = ½ (⟪g, s(λ⁺)⟫ - λ⁺ Δ(λ⁺)²)`: (9.4.3) holds if `m(α⁺ s(λ⁺)) ≤ mᴸ` and (9.4.4)
holds if `½ (⟪g, s(λ⁺)⟫ - λ⁺ Δ(λ⁺)²) ≥ mᵁ`; in the first case `α⁺ s(λ⁺)` is a feasible
exemplar with `m ≤ mᴸ`. -/
theorem tests_9_4_3_9_4_4_of_setL (hH : H.IsHermitian) (hM : M.PosDef) {Δ lam mL mU : ℝ}
    (hΔ : 0 ≤ Δ) (hlam : lam ∈ setL_tr hH hM g Δ) :
    (model g H ((Δ / mNorm M (stepOf g H M lam)) • stepOf g H M lam) ≤ mL →
        trValue g H M Δ ≤ mL ∧ ∃ s, mNorm M s ≤ Δ ∧ model g H s ≤ mL) ∧
      (mU ≤ 1 / 2 * (⟪g, stepOf g H M lam⟫ - lam * mNorm M (stepOf g H M lam) ^ 2) →
        mU ≤ trValue g H M Δ) := by
  have hval := (optimalValue_bounds_9_4_6 (g := g) hH hM).2.2.2.2 lam hlam.1
  refine ⟨fun hL => ?_, fun hU => test_9_4_4_of_9_4_6 hM hΔ hlam.2 (hval ▸ hU)⟩
  obtain ⟨h1, h2⟩ := test_9_4_3_of_9_4_6 hM hΔ hlam.2 rfl hL
  exact ⟨h1, _, h2, hL⟩

/-- **Test (9.4.3) from `λ⁻ ∈ 𝓖`** ([cartis2022evaluation] §9.4.2, after (9.4.7)): for
`λ⁻ ∈ 𝓖`, `Δ⁻ = Δ(λ⁻) = ‖s(λ⁻)‖_M < Δ` is a suitable radius for (9.4.7), and (9.4.3) holds if
`min(m(α⁻ s(λ⁻)), ½ (⟪g, s(λ⁻)⟫ - λ⁻ Δ(λ⁻)²)) ≤ mᴸ`, with a feasible exemplar `s`,
`‖s‖_M ≤ Δ` and `m(s) ≤ mᴸ`. -/
theorem test_9_4_3_of_setG (hH : H.IsHermitian) (hM : M.PosDef) {Δ lam mL : ℝ}
    (hlam : lam ∈ setG_tr hH hM g Δ)
    (hL : min (model g H ((Δ / mNorm M (stepOf g H M lam)) • stepOf g H M lam))
      (1 / 2 * (⟪g, stepOf g H M lam⟫ - lam * mNorm M (stepOf g H M lam) ^ 2)) ≤ mL) :
    trValue g H M Δ ≤ mL ∧ ∃ s, mNorm M s ≤ Δ ∧ model g H s ≤ mL := by
  have hval := (optimalValue_bounds_9_4_6 (g := g) hH hM).2.2.2.2 lam hlam.1
  exact test_9_4_3_of_9_4_7 hM (mNorm_nonneg _ _) hlam.2.le rfl (hval ▸ hL)

/-- **Footnote 65 of [cartis2022evaluation]**: for `λ ∈ 𝓖`,
`m_{Δ(λ)} ≥ ½ (⟪g, s(λ)⟫ - λ Δ²)` (indeed `m_{Δ(λ)} = ½ (⟪g, s(λ)⟫ - λ Δ(λ)²)` and
`Δ(λ) < Δ`). -/
theorem trValue_ge_of_setG (hH : H.IsHermitian) (hM : M.PosDef) {Δ lam : ℝ}
    (hlam : lam ∈ setG_tr hH hM g Δ) :
    1 / 2 * (⟪g, stepOf g H M lam⟫ - lam * Δ ^ 2) ≤
      trValue g H M (mNorm M (stepOf g H M lam)) := by
  rw [(optimalValue_bounds_9_4_6 (g := g) hH hM).2.2.2.2 lam hlam.1]
  have hl0 : 0 ≤ lam := (lambdaS_nonneg hH hM).trans hlam.1.le
  have h0 := mNorm_nonneg M (stepOf g H M lam)
  have : mNorm M (stepOf g H M lam) ^ 2 ≤ Δ ^ 2 := pow_le_pow_left₀ h0 hlam.2.le 2
  nlinarith

end CartisGouldToint.Chapter09

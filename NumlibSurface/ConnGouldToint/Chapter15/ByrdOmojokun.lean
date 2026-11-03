import NumlibSurface.ConnGouldToint.Chapter15.Corrections

/-! # Byrd–Omojokun SQP convergence

The statements use the uniform full-trial error and accepted-step
variation bounds from the earlier corrected convergence results.
The correction variant retains the normal and tangential models and
penalty update, while distinguishing original-trial agreement from
accepted-iterate decrease.
-/

open Filter Topology
open scoped RealInnerProductSpace

namespace ConnGouldToint.Chapter15

open Chapter06

variable {E Y Z : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The model and penalty estimates used for the tangential convergence
of Byrd–Omojokun SQP. The uncorrected trial determines the small-radius
guarantee, and the accepted trial determines the merit decrease. -/
structure ByrdOmojokunTangentialData (P : BTRParams)
    (c : ℕ → Y) (g n : ℕ → E) (H : ℕ → E →L[ℝ] E) (NT : ℕ → E →L[ℝ] Z)
    (σ dN dT d v Δ original : ℕ → ℝ) (S : Set ℕ) where
  run : SQPTangentialRun P (fun k => ‖NT k (g k)‖) (fun k => ‖NT k (g k + H k (n k))‖)
    v Δ d original S
  G : ℝ
  B : ℝ
  U : ℝ
  D : ℝ
  bN : ℝ
  ν : ℝ
  τ₁ : ℝ
  τ₂ : ℝ
  C : ℝ
  κ : ℝ
  b : ℝ
  β : ℝ
  auxiliary : ℕ → ℝ
  auxiliaryBound : ℝ
  G_nonneg : 0 ≤ G
  B_nonneg : 0 ≤ B
  U_nonneg : 0 ≤ U
  D_nonneg : 0 ≤ D
  bN_pos : 0 < bN
  ν_pos : 0 < ν
  ν_lt_one : ν < 1
  τ₁_nonneg : 0 ≤ τ₁
  τ₂_pos : 0 < τ₂
  C_nonneg : 0 ≤ C
  κ_pos : 0 < κ
  b_pos : 0 < b
  β_pos : 0 < β
  penalty_initial : 0 < σ 0
  gradient_bound : ∀ k, ‖g k‖ ≤ G
  hessian_bound : ∀ k, ‖H k‖ ≤ B
  reduced_map_bound : ∀ k, ‖NT k‖ ≤ D
  constraint_bound : ∀ k, ‖c k‖ ≤ U
  normal_decrease : ∀ k, bN * ‖n k‖ ≤ dN k ∧ dN k ≤ ‖c k‖
  tangential_nonneg : ∀ k, 0 ≤ dT k
  auxiliary_bound : ∀ k, auxiliary k ≤ auxiliaryBound
  penalty_update : ∀ k,
    let dq := -⟪g k, n k⟫ - (1 / 2) * ⟪n k, H k (n k)⟫
    let required := if dN k = 0 then auxiliary k
      else max (auxiliary k) (sqpPenaltyThreshold ν (dN k) (dT k) dq)
    σ (k + 1) = sqpPenaltyUpdate τ₁ τ₂ required (σ k)
  model_split : ∀ k, d k = dT k + σ (k + 1) * dN k +
    (-⟪g k, n k⟫ - (1 / 2) * ⟪n k, H k (n k)⟫)
  tangential_cauchy : ∀ k,
    let w := ‖NT k (g k + H k (n k))‖
    κ * w * min (b * Δ k) (w / β) ≤ dT k
  original_error : ∀ k, |original k - d k| ≤ C * (1 + σ (k + 1)) * Δ k ^ 2

omit [NormedSpace ℝ Y] in
/-- The penalty update enforces (15.4.7). A zero normal decrease forces
the normal step to vanish, so the tangential decrease suffices in that case. -/
theorem ByrdOmojokunTangentialData.model_penalty {P : BTRParams}
    {c : ℕ → Y} {g n : ℕ → E} {H : ℕ → E →L[ℝ] E} {NT : ℕ → E →L[ℝ] Z}
    {σ dN dT d v Δ original : ℕ → ℝ} {S : Set ℕ}
    (data : ByrdOmojokunTangentialData P c g n H NT σ dN dT d v Δ original S) (k : ℕ) :
    data.ν * σ (k + 1) * dN k ≤ d k := by
  by_cases hzero : dN k = 0
  · have hn : n k = 0 := by
      by_contra h
      have hp := mul_pos data.bN_pos (norm_pos_iff.mpr h)
      exact (not_le_of_gt hp) ((data.normal_decrease k).1.trans_eq hzero)
    simpa only [data.model_split, hzero, mul_zero, add_zero, hn, inner_zero_right,
      neg_zero, map_zero, sub_zero] using data.tangential_nonneg k
  let dq := -⟪g k, n k⟫ - (1 / 2) * ⟪n k, H k (n k)⟫
  let threshold := sqpPenaltyThreshold data.ν (dN k) (dT k) dq
  have hd : 0 < dN k := lt_of_le_of_ne
    ((mul_nonneg data.bN_pos.le (norm_nonneg _)).trans (data.normal_decrease k).1) (Ne.symm hzero)
  have hσ : threshold ≤ σ (k + 1) := by
    rw [data.penalty_update, ite_eq_right hzero]
    change threshold ≤ sqpPenaltyUpdate data.τ₁ data.τ₂ (max (data.auxiliary k) threshold) (σ k)
    unfold sqpPenaltyUpdate
    split_ifs with h
    · exact (le_max_right _ _).trans h
    · exact (le_max_right _ _).trans (le_max_left _ _)
  rw [data.model_split]
  exact (sqpPenaltyThreshold_le_iff data.ν_lt_one hd).mp hσ

omit [NormedSpace ℝ Y] in
/-- Theorem 15.4.22. Feasibility makes the normal perturbation vanish.
The penalty stabilizes and the overall predicted decrease dominates a
fixed positive fraction of the tangential decrease on the stabilized tail. -/
theorem theorem_15_4_22 {P : BTRParams}
    {c : ℕ → Y} {g n : ℕ → E} {H : ℕ → E →L[ℝ] E} {NT : ℕ → E →L[ℝ] Z}
    {σ dN dT d v Δ original : ℕ → ℝ} {S : Set ℕ}
    (data : ByrdOmojokunTangentialData P c g n H NT σ dN dT d v Δ original S)
    (hc : Tendsto c atTop (𝓝 0))
    {L : ℝ} (hL : 0 ≤ L)
    (hmove : ∀ k ∈ S, ‖NT k (g k)‖ - ‖NT (k + 1) (g (k + 1))‖ ≤ L * Δ k)
    (hstay : ∀ k ∉ S, ‖NT (k + 1) (g (k + 1))‖ = ‖NT k (g k)‖) :
    (∃ σmax > 0, ∃ κ > 0, ∃ j, ∀ k ≥ j, σ (k + 1) = σmax ∧ κ * dT k ≤ d k) ∧
      Tendsto (fun k => ‖NT k (g k)‖) atTop (𝓝 0) := by
  have hN (k : ℕ) (_ : 0 ≤ k) : data.bN * ‖n k‖ ≤ dN k ∧ dN k ≤ data.U :=
    ⟨(data.normal_decrease k).1, (data.normal_decrease k).2.trans (data.constraint_bound k)⟩
  obtain ⟨σmax, hσ, B₀, hB₀, j, hj⟩ := theorem_15_4_8 g n H dN dT σ data.auxiliary
    data.G_nonneg data.B_nonneg data.U_nonneg data.bN_pos data.ν_lt_one
    data.τ₁_nonneg data.τ₂_pos data.penalty_initial data.gradient_bound
    data.hessian_bound hN data.tangential_nonneg data.auxiliary_bound data.penalty_update
  let κ := data.ν * σmax / (data.ν * σmax + B₀)
  have hκ : 0 < κ := by dsimp [κ]; positivity [data.ν_pos]
  have hdom (k : ℕ) (hk : j ≤ k) : κ * dT k ≤ d k := by
    obtain ⟨hstable, hmodel⟩ := hj k hk
    have h₁ : dT k + (σmax - B₀) * dN k ≤ d k := by
      rw [data.model_split, ← hstable]
      exact hmodel
    have h₂ : data.ν * σmax * dN k ≤ d k := by
      rw [← hstable]
      exact data.model_penalty k
    exact (lemma_15_4_9 data.ν_pos hσ hB₀
      ((mul_nonneg data.bN_pos.le (norm_nonneg _)).trans (data.normal_decrease k).1)
      h₁ h₂).2
  refine ⟨⟨σmax, hσ, κ, hκ, j, fun k hk => ⟨(hj k hk).1, hdom k hk⟩⟩, ?_⟩
  have hn : Tendsto n atTop (𝓝 0) := by
    have hc' : Tendsto (fun k => ‖c k‖) atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mp hc
    refine squeeze_zero_norm' (a := fun k => ‖c k‖ / data.bN)
      (Eventually.of_forall fun k => (le_div_iff₀ data.bN_pos).mpr ?_) ?_
    · rw [mul_comm]
      exact (data.normal_decrease k).1.trans (data.normal_decrease k).2
    · simpa only [zero_div] using hc'.div_const data.bN
  apply theorem_15_4_11 data.run (mul_pos hκ data.κ_pos) data.b_pos data.β_pos
    (mul_nonneg data.C_nonneg (by positivity : 0 ≤ 1 + σmax))
    (sqpReducedGradient_perturbation g n H NT data.D_nonneg data.hessian_bound
      data.reduced_map_bound hn) ?_ ?_ hL hmove hstay
  · filter_upwards [eventually_ge_atTop j] with k hk
    simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_left (data.tangential_cauchy k) hκ.le).trans (hdom k hk)
  · filter_upwards [eventually_ge_atTop j] with k hk
    simpa only [(hj k hk).1] using data.original_error k

omit [NormedSpace ℝ Y] in
/-- Theorem 15.4.23 for Byrd–Omojokun with second-order correction.
The original trial supplies the model agreement. The selected trial
supplies the actual decrease, and (15.4.155) bounds its displacement.
Uniform rank transfers normal criticality to feasibility, after which
the stabilized tangential estimates apply without changing the models. -/
theorem theorem_15_4_23 {P : BTRParams}
    (f : E → ℝ) (c : E → Y) (a : E → E) (x s correction g n : ℕ → E)
    (H : ℕ → E →L[ℝ] E) (NT : ℕ → E →L[ℝ] Z)
    {σ dN dT d v Δ original : ℕ → ℝ} {S : Set ℕ}
    (data : ByrdOmojokunTangentialData P (c ∘ x) g n H NT σ dN dT d v Δ original S)
    {fmin m κN cmax βN ξN L ξ χ : ℝ}
    (hm : 0 < m) (hκN : 0 < κN) (hcmax : 0 < cmax) (hβN : 0 < βN) (hξN : 0 < ξN)
    (hL : 0 ≤ L) (hξ : 0 ≤ ξ) (hχ : 0 ≤ χ)
    (hf : ∀ k, fmin ≤ f (x k))
    (hrank : ∀ k, m * ‖c (x k)‖ ≤ ‖a (x k)‖)
    (hpredN : ∀ k, κN * (‖a (x k)‖ / cmax) * min (ξN * Δ k) (‖a (x k)‖ / βN) ≤ dN k)
    (horiginal : ∀ k, original k =
      sqpMerit f c (σ (k + 1)) (x k) - sqpMerit f c (σ (k + 1)) (x k + s k))
    (haccepted : ∀ k ∈ S, P.η₁ * d k ≤ sqpMerit f c (σ (k + 1)) (x k) -
      sqpMerit f c (σ (k + 1)) (x (k + 1)))
    (hchosen : ∀ k ∈ S, x (k + 1) = x k + s k ∨ x (k + 1) = x k + s k + correction k)
    (hstep : ∀ k, ‖s k‖ ≤ ξ * Δ k)
    (hcorrection : ∀ k ∈ S, x (k + 1) = x k + s k + correction k → ‖correction k‖ ≤ χ * Δ k)
    (hreject : ∀ k ∉ S, x (k + 1) = x k)
    (haLip : ∀ i j, ‖a (x i) - a (x j)‖ ≤ L * ‖x i - x j‖)
    (hgLip : ∀ i j, |‖NT i (g i)‖ - ‖NT j (g j)‖| ≤ L * ‖x i - x j‖) :
    Tendsto (fun k => a (x k)) atTop (𝓝 0) ∧ Tendsto (c ∘ x) atTop (𝓝 0) ∧
      (∃ σmax > 0, ∃ κ > 0, ∃ j, ∀ k ≥ j, σ (k + 1) = σmax ∧ κ * dT k ≤ d k) ∧
      Tendsto (fun k => ‖NT k (g k)‖) atTop (𝓝 0) := by
  have hσmono : Monotone σ := monotone_nat_of_le_succ fun k => by
    rw [data.penalty_update, sqpPenaltyUpdate]
    split_ifs <;> first
      | exact le_rfl
      | exact (le_add_of_nonneg_right data.τ₂_pos.le).trans
          ((le_max_right _ _).trans (le_max_right _ _))
  have hσpos (k : ℕ) : 0 < σ (k + 1) :=
    data.penalty_initial.trans_le (hσmono (Nat.zero_le _))
  have htravel (k : ℕ) (hk : k ∈ S) : ‖x k - x (k + 1)‖ ≤ (ξ + χ) * Δ k := by
    rw [norm_sub_rev]
    rcases hchosen k hk with h | h
    · rw [h, add_sub_cancel_left]
      exact (hstep k).trans (by linarith only [mul_nonneg hχ (data.run.radius_pos k).le])
    · rw [h, show x k + s k + correction k - x k = s k + correction k by abel]
      exact (norm_add_le _ _).trans (by
        linarith only [hstep k, hcorrection k hk h,
          show (ξ + χ) * Δ k = ξ * Δ k + χ * Δ k by ring])
  have hscale (k : ℕ) (hk : k ∈ S) : L * ‖x k - x (k + 1)‖ ≤ (L * (ξ + χ)) * Δ k := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (htravel k hk) hL
  have hL' := mul_nonneg hL (add_nonneg hξ hχ)
  have ha : Tendsto (fun k => a (x k)) atTop (𝓝 0) := by
    refine sqp_normal_criticality_of_accepted_decrease f c a x s (fun k => σ (k + 1)) d Δ S
      P.eta₁_pos P.eta₂_lt_one (mul_pos data.ν_pos hκN) hcmax hβN hξN data.C_nonneg hL'
      data.penalty_initial P.gamma₁_pos
      (P.gamma₁_pos.le.trans P.gamma₁_le_gamma₂) P.gamma₂_lt_one hf
      (fun k => hσmono (Nat.zero_le _)) (fun _ _ hij => hσmono (Nat.succ_le_succ hij))
      data.run.radius_pos ?_ ?_ data.run.radius_lower haccepted ?_
      (fun k hk => ⟨hreject k hk, data.run.radius_rejected k hk⟩) ?_
    · intro k
      have hp := mul_le_mul_of_nonneg_left (hpredN k) (mul_nonneg data.ν_pos.le (hσpos k).le)
      exact (by simpa only [mul_left_comm, mul_comm, mul_assoc] using
        hp.trans (data.model_penalty k))
    · intro k
      rw [← abs_neg, neg_sub, show sqpMerit f c (σ (k + 1)) (x k) - d k -
        sqpMerit f c (σ (k + 1)) (x k + s k) = original k - d k by rw [horiginal]; ring]
      simpa only [mul_assoc] using data.original_error k
    · intro k hk
      apply data.run.very_successful k
      simpa only [horiginal, Optimization.reductionRatio] using hk
    · intro k hk
      exact ((norm_sub_norm_le _ _).trans (haLip k (k + 1))).trans (hscale k hk)
  have hc : Tendsto (c ∘ x) atTop (𝓝 0) :=
    corollary_15_4_20 (c ∘ x) (a ∘ x) hm hrank ha
  refine ⟨ha, hc, theorem_15_4_22 data hc hL' ?_ ?_⟩
  · intro k hk
    exact ((le_abs_self _).trans (hgLip k (k + 1))).trans (hscale k hk)
  · intro k hk
    have h := hgLip k (k + 1)
    rw [hreject k hk, sub_self, norm_zero, mul_zero] at h
    exact (sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))).symm

omit [InnerProductSpace ℝ E] in
/-- Theorem 15.4.24. A small-radius nonshrinkage rule keeps the radius
bounded below. The vanishing standard normal and tangential steps
then fit within their respective radii. On the trapped tail, the
accepted standard step or its full correction gives the local rate. -/
theorem theorem_15_4_24 (x s u nStandard tStandard : ℕ → E) (xstar : E) (ey Δ : ℕ → ℝ)
    {M D r r₀ γ ξN ξT : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D) (hr : 0 < r) (hr₀ : 0 < r₀)
    (hγ : 0 < γ) (hξN : 0 < ξN) (hξT : 0 < ξT)
    (hey : ∀ k, 0 ≤ ey k) (hylim : Tendsto ey atTop (𝓝 0))
    (hvisit : ∃ᶠ k in atTop, ‖x k - xstar‖ < r)
    (hΔ : ∀ k, 0 < Δ k) (hnext : ∀ k, γ * Δ k ≤ Δ (k + 1))
    (hkeep : ∀ᶠ k in atTop, Δ k ≤ r₀ → Δ k ≤ Δ (k + 1))
    (hn : Tendsto nStandard atTop (𝓝 0)) (ht : Tendsto tStandard atTop (𝓝 0))
    (hlocal : ∀ᶠ k in atTop, ‖x k - xstar‖ < r →
      ‖nStandard k‖ ≤ ξN * Δ k → ‖tStandard k‖ ≤ ξT * Δ k →
      (x (k + 1) = x k + s k ∨ x (k + 1) = x k + s k + u k) ∧
      ‖x k + s k - xstar‖ ≤ M * (‖x k - xstar‖ + ey k) * ‖x k - xstar‖ ∧
      ‖u k‖ ≤ D * (‖x k - xstar‖ + ey k) * ‖x k - xstar‖)
    (hsmall : (M + D) * (r + r) ≤ 1 / 2) :
    Chapter03.ConvergesQSuperlinearly x xstar ∧
      ((∃ C ≥ 0, ∀ᶠ k in atTop, ey k ≤ C * ‖x k - xstar‖) →
        Chapter03.ConvergesQQuadratically x xstar) := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp hkeep
  let floor := min (Δ K) (γ * r₀)
  have hfloor : 0 < floor := lt_min (hΔ K) (mul_pos hγ hr₀)
  have hbound (k : ℕ) (hk : K ≤ k) : floor ≤ Δ k := by
    induction k, hk using Nat.le_induction with
    | base => exact min_le_left _ _
    | succ k hk ih =>
      by_cases hh : Δ k ≤ r₀
      · exact ih.trans (hK k hk hh)
      · exact (min_le_right _ _).trans
          ((mul_le_mul_of_nonneg_left (le_of_not_ge hh) hγ.le).trans (hnext k))
  have hn' := tendsto_zero_iff_norm_tendsto_zero.mp hn
  have ht' := tendsto_zero_iff_norm_tendsto_zero.mp ht
  apply theorem_15_4_15 x s u xstar ey hM hD hr hey hylim hvisit ?_ hsmall
  filter_upwards [hlocal, eventually_ge_atTop K,
    hn'.eventually_lt_const (mul_pos hξN hfloor), ht'.eventually_lt_const (mul_pos hξT hfloor)]
    with k hk hK' hn₀ ht₀ hx
  exact hk hx (hn₀.le.trans (mul_le_mul_of_nonneg_left (hbound k hK') hξN.le))
    (ht₀.le.trans (mul_le_mul_of_nonneg_left (hbound k hK') hξT.le))

/-- Theorem 15.4.25 for the second-order Byrd–Omojokun variant.
Relative compactness supplies uniform tail coverage by the cluster
set. The large-normal-step branch and the negative-curvature branch
supply sufficient decrease, with the original or corrected acceptance
ratio determining which trial is accepted. -/
theorem theorem_15_4_25 {X ι : Type*} [TopologicalSpace X] [Fintype ι] [Nonempty ι]
    {P : BTRParams} (z : ℕ → X) (zstar : ι → X) (curvature : X → ℝ)
    (firstOrder : ι → Prop) (v Δ d dN dT nNorm original corrected : ℕ → ℝ)
    (S normal : Set ℕ) {U : Set X}
    (hU : IsCompact U) (hmem : ∀ᶠ k in atTop, z k ∈ U)
    (hcluster : ∀ x ∈ U, MapClusterPt x atTop z → x ∈ Set.range zstar)
    (hcont : ∀ i, ContinuousAt curvature (zstar i))
    (hfirst : ∀ i, firstOrder i)
    {a b κ β C : ℝ} (ha : 0 < a) (hb : 0 < b) (hκ : 0 < κ) (hβ : 0 < β) (hC : 0 ≤ C)
    (hv : ∀ k, 0 ≤ v k) (hmono : Antitone v) (hΔ : ∀ k, 0 < Δ k)
    (hnext : ∀ k, P.γ₁ * Δ k ≤ Δ (k + 1))
    (hrej : ∀ k ∉ S, Δ (k + 1) ≤ P.γ₂ * Δ k)
    (hnormal : ∀ k ∈ normal, a * Δ k ≤ nNorm k)
    (hN : ∀ k, b * nNorm k ≤ dN k)
    (hNmodel : ∀ k, κ * dN k ≤ d k)
    (hT : ∀ k ∉ normal, β * (-curvature (z k)) * Δ k ^ 2 ≤ dT k)
    (hTmodel : ∀ k, κ * dT k ≤ d k)
    (herror : ∀ k ∈ normal, |original k - d k| ≤ C * Δ k ^ 2)
    (hcorrected : ∀ ε > 0, ∃ r > 0, ∀ᶠ k in atTop, k ∉ normal → Δ k ≤ r →
      |corrected k - d k| ≤ ε * Δ k ^ 2)
    (hmerit : ∀ k ∈ S, P.η₁ * d k ≤ v k - v (k + 1))
    (hvery : ∀ k, P.η₂ ≤ original k / d k → k ∈ S ∧ Δ k ≤ Δ (k + 1))
    (haccepted : ∀ k ∉ normal, P.η₁ ≤ original k / d k → k ∈ S ∧ Δ k ≤ Δ (k + 1))
    (hcor : ∀ k ∉ normal, original k / d k < P.η₁ →
      P.η₂ ≤ corrected k / d k → k ∈ S ∧ Δ k ≤ Δ (k + 1)) :
    ∃ i, firstOrder i ∧ 0 ≤ curvature (zstar i) := by
  refine theorem_15_4_16 firstOrder (curvature ∘ zstar) (curvature ∘ z) v Δ S
    P.gamma₁_pos (P.gamma₁_pos.le.trans P.gamma₁_le_gamma₂) P.gamma₂_lt_one
    hfirst (sqp_curvature_tail_of_compact z zstar curvature hU hmem hcluster hcont)
    hv hmono hΔ hnext hrej ?_
  refine sqp_secondOrder_correction_progress (P := P) (curvature ∘ z) v Δ d original corrected S normal
    (mul_pos (mul_pos hκ hb) ha) (mul_pos hκ hβ) hC hΔ ?_ ?_
    herror hcorrected hmerit hvery haccepted hcor
  · intro k hk
    have h := mul_le_mul_of_nonneg_left (hnormal k hk) hb.le
    have hh := mul_le_mul_of_nonneg_left (h.trans (hN k)) hκ.le
    linarith only [hh, hNmodel k,
      show κ * b * a * Δ k = κ * (b * (a * Δ k)) by ring]
  · intro k hk
    have h := mul_le_mul_of_nonneg_left (hT k hk) hκ.le
    exact (by simpa only [Function.comp_apply, mul_assoc] using h.trans (hTmodel k))

end ConnGouldToint.Chapter15

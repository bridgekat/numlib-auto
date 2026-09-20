import NumlibSurface.AtkinsonHan.Chapter07.Section03

/-!
# Atkinson–Han §8.4: weak formulations of linear elliptic boundary value problems

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §8.4.

The section's one numbered result is **Lemma 8.4.1**: on a Lipschitz domain `Ω`, the quotient
norm `‖[v]‖_V = inf_{α ∈ ℝ} ‖v + α‖_1` of `V = H^1(Ω)/ℝ` is equivalent to the seminorm `|v|_1`,
which is what makes the bilinear form `ā([u], [v]) = ∫_Ω ∇u · ∇v` of the pure Neumann problem
(8.4.10) elliptic on `V`. It is here as `lemma_8_4_1`, a special case of Theorem 7.3.17 as the
book says, proved directly as the Deny–Lions equivalence `theorem_7_3_12` with `k = 1`, `p = 2`
and the one seminorm `f_1(v) = |∫_Ω v|`: the shift `α = −(∫_Ω v)/|Ω|` kills `f_1`, so
`inf_α ‖v + α‖_1 ≤ ‖v + α‖_1 ≤ c |v|_1`, and `|v|_1 = |v + α|_1 ≤ ‖v + α‖_1` for every `α`. The
domain hypothesis is the backbone's — a connected bounded extension domain, which the `C¹`
domains of Definition 7.2.1 are (`isSobolevExtensionDomainAll_of_definition_7_2_1`) — where the
book assumes a Lipschitz domain. The constant function `1` is carried by any element `𝟙` of
`H^1(Ω)` whose function is `1` almost everywhere on `Ω`; `exists_fn_ae_eq_one` supplies one.

The weak formulations (8.4.1)–(8.4.22) themselves — the homogeneous and non-homogeneous
Dirichlet, Neumann, pure Neumann, mixed and general second-order problems — quantify over the
trace `γ : H^1(Ω) → H^{1/2}(Γ)` of Theorem 7.3.10 (blocker 2 of `notes/frontier.md`) and are not
stated; their abstract content is `theorem_8_3_4`.
-/

open Filter MeasureTheory Set TopologicalSpace

open scoped ContDiff ENNReal NNReal Topology

namespace AtkinsonHan.Chapter08

open AtkinsonHan.Chapter07 SobolevMultiIndex

/-- The exponent `p = 2` in the form `((2 : ℝ≥0) : ℝ≥0∞)` of the backbone's Rellich–Kondrachov
theorem (`Numlib/Analysis/Sobolev/Compactness.lean` takes `p : ℝ≥0`); `H^1(Ω)` is
`SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume`, definitionally the space
`SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 2 Ω volume` of `corollary_7_2_4`; the instance
`Fact (1 ≤ 𝟚)` is `AtkinsonHan.Chapter07.fact_one_le_two_coe`. -/
local notation "𝟚" => ((2 : ℝ≥0) : ℝ≥0∞)

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **The constant function `1` lies in `H^1(Ω)`** for a bounded open `Ω`: there is an element
`𝟙` of `W^{1,2}(Ω)` whose function is `1` almost everywhere on `Ω` — the restriction of a smooth
compactly supported function equal to `1` on `closure Ω`. -/
theorem exists_fn_ae_eq_one
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    ∃ one : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume,
      fn one =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] 1 := by
  obtain ⟨R, -, hR⟩ := hb.subset_ball_lt 0 0
  have hcl : closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ Metric.closedBall 0 R :=
    closure_minimal (hR.trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall
  obtain ⟨φ, hφ, hφ1, hφs, -⟩ := hb.isCompact_closure.exists_contDiff_eqOn_one
    (Metric.isOpen_ball (x := (0 : EuclideanSpace ℝ (Fin (d + 1)))) (ε := R + 1))
    (hcl.trans (Metric.closedBall_subset_ball (by linarith)))
  have hφc : HasCompactSupport φ :=
    HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin (d + 1))) (R + 1))
      ((subset_tsupport φ).trans (hφs.trans Metric.ball_subset_closedBall))
  obtain ⟨one, hone⟩ := hφ.exists_sobolevMultiIndex_of_hasCompactSupport
    (b := stdBasis (d + 1)) (k := 1) (p := 𝟚) (Ω := Ω) (μ := volume) hφc
  refine ⟨one, hone.trans ?_⟩
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
  exact hφ1 (subset_closure hx)

/-- The top-order derivatives of an element of `H^1(Ω)` with constant function vanish, so its
seminorm `|·|_1` is zero. -/
theorem topSeminorm_eq_zero_of_fn_ae_eq_one
    {one : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume}
    (hone : fn one =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] 1) :
    topSeminorm ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume one = 0 := by
  rw [topSeminorm_eq_zero_iff]
  intro α
  rcases MultiIndexLE.eq_zero_or_exists_eq_single α.1 with h0 | ⟨i, hi⟩
  · have := α.2
    rw [h0] at this
    simp at this
  · rw [hi]
    -- the constant `1` has weak derivative `0` along every direction
    have h1 : HasWeakIteratedLineDerivOn ![stdBasis (d + 1) i] (fn one)
        (weakDeriv one (MultiIndexLE.singleLE i)) Ω volume :=
      hasWeakIteratedLineDerivOn_single (k := 0) one i
    have h2 : HasWeakIteratedLineDerivOn ![stdBasis (d + 1) i] (fn one) (fun _ ↦ (0 : ℝ))
        Ω volume := by
      have h := ((contDiff_const (c := (1 : ℝ))).hasWeakFDerivOn (Ω := Ω)
        (μ := volume)).lineDeriv ![stdBasis (d + 1) i]
      refine h.congr_ae hone.symm (Eventually.of_forall fun x ↦ ?_)
      simp
    exact Lp.ext (Filter.EventuallyEq.trans
      ((ae_restrict_iff' Ω.isOpen.measurableSet).2 (h1.ae_eq h2)) (Lp.coeFn_zero ℝ 𝟚 _).symm)

/-- The seminorm `|·|_1` does not see the constants: `|v + α 𝟙|_1 = |v|_1`. -/
theorem topSeminorm_add_smul_one
    {one : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume}
    (hone : fn one =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] 1)
    (v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume) (α : ℝ) :
    topSeminorm ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume (v + α • one)
      = topSeminorm ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume v :=
  (topSeminorm ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume).apply_add_smul_of_eq_zero
    (topSeminorm_eq_zero_of_fn_ae_eq_one hone) v α

/-- **The integral `v ↦ ∫_Ω v` is a bounded linear functional on `H^1(Ω)`** for a bounded `Ω`:
`L^2(Ω) ⊆ L^1(Ω)` on a set of finite measure, then the Bochner integral. -/
theorem exists_integralCLM (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    ∃ ℓ : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume →L[ℝ] ℝ,
      ∀ v, ℓ v = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), fn v x := by
  have hfin : IsFiniteMeasure (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    isFiniteMeasure_restrict.2 (hb.measure_lt_top (μ := volume)).ne
  obtain ⟨M, hM⟩ : ∃ M : Lp ℝ 𝟚 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) →L[ℝ]
      Lp ℝ 1 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      ∀ g, (M g : EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] g :=
    ⟨Lp.monoExponentL ℝ _ 𝟚 1 (by norm_num), fun g ↦ Lp.coeFn_monoExponentL (by norm_num) g⟩
  refine ⟨(L1.integralCLM (μ := volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (E := ℝ)).comp (M.comp (fnL ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume)), fun v ↦ ?_⟩
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← L1.integral_eq,
    L1.integral_eq_integral]
  refine integral_congr_ae ((hM _).trans ?_)
  exact Eventually.of_forall fun x ↦ by rw [fnL_apply]

/-- **(H2) for the seminorm `|∫_Ω v|`**: an element of `H^1(Ω)` of a nonempty bounded `Ω` which
is a constant polynomial almost everywhere and has vanishing integral is zero. -/
theorem eq_zero_of_integral_eq_zero
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hne : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).Nonempty)
    (v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume)
    (hv : ∃ q ∈ MvPolynomial.restrictTotalDegree (Fin (d + 1)) ℝ 0, fn v
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        fun x ↦ MvPolynomial.eval (fun i ↦ x i) q)
    (hint : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), fn v x = 0) : v = 0 := by
  have hμ : volume (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ≠ ⊤ :=
    (hb.measure_lt_top (μ := volume)).ne
  have hvol : 0 < volume.real (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) :=
    ENNReal.toReal_pos (Ω.isOpen.measure_pos volume hne).ne' hμ
  obtain ⟨q, hq, hvq⟩ := hv
  rw [MvPolynomial.mem_restrictTotalDegree, Nat.le_zero,
    MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hq
  have hvc : fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      fun _ ↦ q.coeff 0 := by
    refine hvq.trans (Eventually.of_forall fun x ↦ ?_)
    change MvPolynomial.eval (fun i ↦ x i) q = q.coeff 0
    conv_lhs => rw [hq]
    rw [MvPolynomial.eval_C]
  rw [integral_congr_ae hvc, setIntegral_const, smul_eq_mul] at hint
  have hzero : q.coeff 0 = 0 := (mul_eq_zero.1 hint).resolve_left hvol.ne'
  refine ext_of_fn_ae_eq (hvc.trans ?_)
  rw [hzero]
  exact fn_zero.symm

/-- **The Deny–Lions inequality with the seminorm `|∫_Ω v|`**: on a connected bounded extension
domain, `‖v‖_1 ≤ C (|v|_1 + |∫_Ω v|)` — `theorem_7_3_12` with `k = 1`, `p = 2` and `J = 1`. -/
theorem exists_norm_le_topSeminorm_add_abs_integral (hΩ : IsSobolevExtensionDomain (d + 1) 𝟚 Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hc : IsPreconnected (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hne : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).Nonempty)
    {ℓ : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume →L[ℝ] ℝ}
    (hℓ : ∀ v, ℓ v = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), fn v x) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume,
      ‖v‖ ≤ C * (topSeminorm ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume v + |ℓ v|) := by
  have hμ : volume (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ≠ ⊤ :=
    (hb.measure_lt_top (μ := volume)).ne
  have h2 : ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume,
      (∃ q ∈ MvPolynomial.restrictTotalDegree (Fin (d + 1)) ℝ 0, fn v
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
          fun x ↦ MvPolynomial.eval (fun i ↦ x i) q) → ℓ v = 0 → v = 0 := fun v hv h0 ↦
    eq_zero_of_integral_eq_zero hb hne v hv ((hℓ v).symm.trans h0)
  have h := SobolevEuclidean.exists_norm_le_topSeminorm_add_abs_of_isPreconnected
    (N := d + 1) (k := 0) (p := 2) hΩ hμ hc ℓ h2
  exact h

/-- **Lemma 8.4.1**: on a connected bounded extension domain `Ω ⊆ ℝ^{d+1}` (the book's Lipschitz
domain; the `C¹` domains of Definition 7.2.1 included), for `𝟙 ∈ H^1(Ω)` the constant function
`1`, the quotient norm `‖[v]‖_V = inf_{α ∈ ℝ} ‖v + α‖_1` of `V = H^1(Ω)/ℝ` is equivalent to the
seminorm `|v|_1`: `c₁ |v|_1 ≤ inf_α ‖v + α 𝟙‖_1 ≤ c₂ |v|_1` for all `v ∈ H^1(Ω)`, with
`c₁ = 1`. The book calls it a special case of Theorem 7.3.17; it is the Deny–Lions equivalence
`theorem_7_3_12` with `k = 1`, `p = 2` and the one seminorm `f_1(v) = |∫_Ω v|`
(`exists_norm_le_topSeminorm_add_abs_integral`), evaluated at the representative `v + α 𝟙` with
`α = −(∫_Ω v)/|Ω|`, for which `f_1` vanishes (`Seminorm.ciInf_norm_add_smul_le_mul`); and
`|v|_1 ≤ ‖v + α 𝟙‖_1` for every `α` because `|𝟙|_1 = 0` (`Seminorm.le_ciInf_norm_add_smul`).
`H^1(Ω)` is the space of Definition 7.2.2 in the book's own indexing, and `|v|_1` its top-order
seminorm `SobolevMultiIndex.topSeminorm`, the gradient norm `‖∇v‖_{L²(Ω)}`. -/
theorem lemma_8_4_1 (hΩ : IsSobolevExtensionDomain (d + 1) 𝟚 Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hc : IsPreconnected (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hne : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).Nonempty)
    {one : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume}
    (hone : fn one =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] 1) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume,
      c₁ * topSeminorm ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume v ≤ ⨅ α : ℝ, ‖v + α • one‖ ∧
      ⨅ α : ℝ, ‖v + α • one‖ ≤ c₂ * topSeminorm ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume v := by
  have hμ : volume (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ≠ ⊤ :=
    (hb.measure_lt_top (μ := volume)).ne
  have hvol : 0 < volume.real (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) :=
    ENNReal.toReal_pos (Ω.isOpen.measure_pos volume hne).ne' hμ
  have h := exists_integralCLM hb
  obtain ⟨ℓ, hℓ⟩ := h
  have hℓone : ℓ one ≠ 0 :=
    ((hℓ one).trans ((integral_congr_ae hone).trans (by simp))).trans_ne hvol.ne'
  have h' := exists_norm_le_topSeminorm_add_abs_integral hΩ hb hc hne hℓ
  obtain ⟨C, hC, hle⟩ := h'
  have h0 := topSeminorm_eq_zero_of_fn_ae_eq_one hone
  refine ⟨1, C, one_pos, hC, fun v ↦ ⟨?_, ?_⟩⟩
  · exact (one_mul _).trans_le (Seminorm.le_ciInf_norm_add_smul
      (topSeminorm ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume) topSeminorm_le_norm h0 v)
  · exact Seminorm.ciInf_norm_add_smul_le_mul (topSeminorm ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume)
      ℓ h0 hℓone hle v

end AtkinsonHan.Chapter08

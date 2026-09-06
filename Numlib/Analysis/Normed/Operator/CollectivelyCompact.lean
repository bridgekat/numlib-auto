/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Operator.Compact`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Collectively compact families of operators

A family `K : ι → V →L[𝕜] W` is **collectively compact** when the union of the images of one
neighborhood of the origin has compact closure — the exact analogue of Mathlib's
`IsCompactOperator`, so that a constant family is collectively compact precisely when its member is
a compact operator.

The point of the notion is that a pointwise convergent, collectively compact family `Kₙ → K`
satisfies `‖(K - Kₙ) ∘ Kₙ‖ → 0` even though `‖K - Kₙ‖` does not tend to zero. That is what makes
the Nyström method for integral equations of the second kind stable, and it is the hypothesis of
Anselone's perturbation theorem.

This is P. Anselone's theory, as presented in Atkinson–Han[^atkinson-han], Section 12.4.3
(assumptions A1–A3 and Lemma 12.4.7) and Section 12.1 (Lemmas 12.1.3 and 12.1.4).

## Main definitions

* `IsCollectivelyCompact`, with `isCollectivelyCompact_const_iff`,
  `IsCollectivelyCompact.isCompactOperator` and `IsCollectivelyCompact.comp`.

## Main statements

* `IsCollectivelyCompact.isCompactOperator_of_tendsto` — a pointwise limit of a collectively
  compact family is a compact operator.
* `IsCollectivelyCompact.exists_opNorm_le` — a collectively compact family is uniformly bounded.
* `IsCollectivelyCompact.tendsto_opNorm_sub_comp` — the estimate above.

The module also carries the two Banach–Steinhaus facts that both this theory and the theory of
projection methods rest on:

* `tendstoUniformlyOn_of_tendsto_of_isCompact` — a pointwise convergent sequence of bounded
  operators on a Banach space converges uniformly on every compact set;
* `tendsto_opNorm_comp_of_isCompactOperator` — hence `‖Aₙ ∘ M‖ → 0` whenever `Aₙ → 0` pointwise and
  `M` is a compact operator. With `Aₙ = 1 - Pₙ` this is the estimate `‖K - Pₙ K‖ → 0` that makes a
  projection method for a second-kind equation convergent, and with `Aₙ = K - Kₙ` it is one clause
  of the collective-compactness lemma below; the two should not be proved separately.

## References

[^atkinson-han]: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
  Analysis Framework*, 3rd edition, Springer, 2009.
-/

open Filter Topology Metric Set Bornology

section OpNorm

variable {𝕜 V W : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- A uniform bound on a ball around the origin bounds the operator norm. The factor `‖c‖`
is unavoidable over a general nontrivially normed field, where the norm need not take the
value `1`. -/
private theorem opNorm_le_of_forall_norm_lt {c : 𝕜} (hc : 1 < ‖c‖) {f : V →L[𝕜] W} {r C : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C) (h : ∀ x : V, ‖x‖ < r → ‖f x‖ ≤ C) : ‖f‖ ≤ ‖c‖ / r * C := by
  have hc0 : (0 : ℝ) < ‖c‖ := lt_trans one_pos hc
  refine ContinuousLinearMap.opNorm_le_of_shell hr (by positivity) hc fun x hx hlt => ?_
  refine (h x hlt).trans ?_
  calc C = ‖c‖ / r * C * (r / ‖c‖) := by field_simp
    _ ≤ ‖c‖ / r * C * ‖x‖ := mul_le_mul_of_nonneg_left hx (by positivity)

end OpNorm

section UniformOnCompact

variable {𝕜 U V W : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup U] [NormedSpace 𝕜 U]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- **Pointwise convergence of bounded operators is uniform on compact sets.** If `Aₙ → L`
pointwise on a Banach space `V`, the convergence is uniform on every compact subset of `V`.

Uniform boundedness makes the family equicontinuous, and equicontinuity turns a finite net of a
compact set into a uniform estimate. Atkinson–Han, *Theoretical Numerical Analysis*,
Lemma 12.1.3. -/
theorem tendstoUniformlyOn_of_tendsto_of_isCompact [CompleteSpace V] {A : ℕ → V →L[𝕜] W}
    {L : V →L[𝕜] W} (hA : ∀ x, Tendsto (fun n => A n x) atTop (𝓝 (L x)))
    {S : Set V} (hS : IsCompact S) :
    TendstoUniformlyOn (fun n => (A n : V → W)) L atTop S := by
  obtain ⟨M, hM⟩ : ∃ M, ∀ n, ‖A n‖ ≤ M := by
    refine banach_steinhaus fun x => ?_
    obtain ⟨C, hC⟩ :=
      isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _ (hA x))
    exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (A 0)) (hM 0)
  obtain ⟨C, hCpos, hCge⟩ : ∃ C : ℝ, 0 < C ∧ ‖L‖ + M ≤ C :=
    ⟨M + ‖L‖ + 1, by linarith [norm_nonneg L], by linarith⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨t, htf, hts⟩ :=
    Metric.totallyBounded_iff.1 hS.totallyBounded (ε / (3 * C)) (by positivity)
  have hev : ∀ᶠ n in atTop, ∀ y ∈ t, ‖L y - A n y‖ < ε / 3 := by
    rw [htf.eventually_all]
    intro y _
    have h0 : Tendsto (fun n => L y - A n y) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := L y)).sub (hA y)
    exact NormedAddGroup.tendsto_nhds_zero.1 h0 (ε / 3) (by positivity)
  filter_upwards [hev] with n hn x hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (hts hx)
  rw [mem_ball, dist_eq_norm] at hxy
  rw [dist_eq_norm]
  have hsplit : L x - A n x = L (x - y) + (L y - A n y) + A n (y - x) := by
    simp only [map_sub]
    abel
  have h1 : ‖L (x - y)‖ ≤ ‖L‖ * (ε / (3 * C)) :=
    (L.le_opNorm _).trans (by gcongr)
  have h2 : ‖A n (y - x)‖ ≤ M * (ε / (3 * C)) := by
    refine ((A n).le_opNorm _).trans ?_
    rw [norm_sub_rev]
    exact mul_le_mul (hM n) hxy.le (norm_nonneg _) hM0
  have h3 := hn y hy
  have hkey : ‖L x - A n x‖ ≤ ‖L (x - y)‖ + ‖L y - A n y‖ + ‖A n (y - x)‖ := by
    rw [hsplit]
    exact norm_add₃_le
  have hfrac : ‖L‖ * (ε / (3 * C)) + M * (ε / (3 * C)) ≤ ε / 3 := by
    rw [← add_mul]
    calc (‖L‖ + M) * (ε / (3 * C)) ≤ C * (ε / (3 * C)) :=
          mul_le_mul_of_nonneg_right hCge (by positivity)
      _ = ε / 3 := by field_simp
  linarith

/-- If `Aₙ → 0` pointwise and `M` is a compact operator, then `‖Aₙ ∘ M‖ → 0`.

The operator norm of `Aₙ ∘ M` is controlled by the values of `Aₙ` on the relatively compact image
of a ball under `M`, on which the convergence is uniform. Atkinson–Han, *Theoretical Numerical
Analysis*, Lemma 12.1.4 (with `Aₙ = 1 - Pₙ` for pointwise convergent projections, giving
`‖K - Pₙ K‖ → 0` for compact `K`) and Lemma 12.4.7 (3) (with `Aₙ = K - Kₙ`). -/
theorem tendsto_opNorm_comp_of_isCompactOperator [CompleteSpace V] {A : ℕ → V →L[𝕜] W}
    (hA : ∀ x, Tendsto (fun n => A n x) atTop (𝓝 0)) {M : U →L[𝕜] V}
    (hM : IsCompactOperator M) :
    Tendsto (fun n => ‖A n ∘L M‖) atTop (𝓝 0) := by
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  have hc0 : (0 : ℝ) < ‖c‖ := lt_trans one_pos hc
  have hMc : IsCompact (closure (M '' closedBall (0 : U) 1)) :=
    (isCompactOperator_iff_isCompact_closure_image_closedBall (M : U →ₗ[𝕜] V) one_pos).1 hM
  have hA0 : ∀ x, Tendsto (fun n => A n x) atTop (𝓝 (((0 : V →L[𝕜] W) : V → W) x)) := by
    simpa using hA
  have hunif : TendstoUniformlyOn (fun n => (A n : V → W)) ((0 : V →L[𝕜] W) : V → W) atTop
      (closure (M '' closedBall 0 1)) :=
    tendstoUniformlyOn_of_tendsto_of_isCompact hA0 hMc
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hunif (ε / (2 * ‖c‖)) (by positivity))
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  have hbound : ∀ x : U, ‖x‖ < 1 → ‖(A n ∘L M) x‖ ≤ ε / (2 * ‖c‖) := by
    intro x hx
    have hmem : M x ∈ closure (M '' closedBall (0 : U) 1) :=
      subset_closure ⟨x, mem_closedBall_zero_iff.2 hx.le, rfl⟩
    have hd := hN n hn (M x) hmem
    simp only [zero_apply, dist_zero_left] at hd
    rw [ContinuousLinearMap.comp_apply]
    exact hd.le
  refine lt_of_le_of_lt (opNorm_le_of_forall_norm_lt hc one_pos (by positivity) hbound) ?_
  have heq : ‖c‖ / 1 * (ε / (2 * ‖c‖)) = ε / 2 := by
    rw [div_one]
    field_simp
  rw [heq]
  linarith

end UniformOnCompact

/-- A family of operators is **collectively compact** when the union of the images of one
neighborhood of the origin is relatively compact.

This is the exact analogue of Mathlib's `IsCompactOperator` for a family, and a constant family is
collectively compact precisely when its member is a compact operator
(`isCollectivelyCompact_const_iff`). It is assumption A3 of the theory of collectively compact
operator approximations. -/
def IsCollectivelyCompact {ι 𝕜 V W : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (K : ι → V →L[𝕜] W) : Prop :=
  ∃ U ∈ 𝓝 (0 : V), IsCompact (closure (⋃ i, K i '' U))

namespace IsCollectivelyCompact

section Family

variable {ι ι' 𝕜 V W : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  {K : ι → V →L[𝕜] W}

/-- Every member of a collectively compact family is a compact operator. -/
theorem isCompactOperator (hK : IsCollectivelyCompact K) (i : ι) : IsCompactOperator (K i) := by
  obtain ⟨U, hU, hcpt⟩ := hK
  refine (isCompactOperator_iff_exists_mem_nhds_image_subset_compact _).2 ⟨U, hU, _, hcpt, ?_⟩
  exact (subset_iUnion (fun j => K j '' U) i).trans subset_closure

/-- A collectively compact family stays collectively compact after reindexing; in particular a
subfamily of a collectively compact family is collectively compact. -/
theorem comp (hK : IsCollectivelyCompact K) (f : ι' → ι) : IsCollectivelyCompact (K ∘ f) := by
  obtain ⟨U, hU, hcpt⟩ := hK
  refine ⟨U, hU, hcpt.of_isClosed_subset isClosed_closure (closure_mono ?_)⟩
  exact iUnion_subset fun j => subset_iUnion (fun i => K i '' U) (f j)

end Family

end IsCollectivelyCompact

section Const

variable {ι 𝕜 V W : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- A one-element family — more generally a constant family — is collectively compact exactly when
its member is a compact operator. -/
theorem isCollectivelyCompact_const_iff [Nonempty ι] {T : V →L[𝕜] W} :
    IsCollectivelyCompact (fun _ : ι => T) ↔ IsCompactOperator T := by
  rw [isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image]
  simp only [IsCollectivelyCompact, iUnion_const]

end Const

namespace IsCollectivelyCompact

section Limit

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **A pointwise limit of a collectively compact family is a compact operator**, because the
image of a neighborhood of the origin under the limit lies in the compact set of the definition.
Atkinson–Han, *Theoretical Numerical Analysis*, Lemma 12.4.7 (1). -/
theorem isCompactOperator_of_tendsto {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    {K : ℕ → V →L[𝕜] W} {L : V →L[𝕜] W} (hK : IsCollectivelyCompact K)
    (hL : ∀ x, Tendsto (fun n => K n x) atTop (𝓝 (L x))) :
    IsCompactOperator L := by
  obtain ⟨U, hU, hcpt⟩ := hK
  refine (isCompactOperator_iff_exists_mem_nhds_image_subset_compact _).2 ⟨U, hU, _, hcpt, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  refine isClosed_closure.mem_of_tendsto (hL x) (Eventually.of_forall fun n => ?_)
  exact subset_closure (mem_iUnion.2 ⟨n, ⟨x, hx, rfl⟩⟩)

/-- **A collectively compact family is uniformly bounded in operator norm**, because the compact
set of the definition is bounded. Atkinson–Han, *Theoretical Numerical Analysis*,
Lemma 12.4.7 (2). -/
theorem exists_opNorm_le {ι W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    {K : ι → V →L[𝕜] W} (hK : IsCollectivelyCompact K) : ∃ C, ∀ i, ‖K i‖ ≤ C := by
  obtain ⟨U, hU, hcpt⟩ := hK
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hcpt.isBounded
  refine ⟨‖c‖ / r * max M 0, fun i =>
    opNorm_le_of_forall_norm_lt hc hr (le_max_right _ _) fun x hx => ?_⟩
  exact (hM _ (subset_closure
    (mem_iUnion.2 ⟨i, ⟨x, hrU (mem_ball_zero_iff.2 hx), rfl⟩⟩))).trans (le_max_left _ _)

/-- **The estimate that makes collectively compact approximation work**: if `Kₙ` is a collectively
compact family converging pointwise to `K`, then `‖(K - Kₙ) ∘ Kₙ‖ → 0`, although `‖K - Kₙ‖` need
not tend to zero. Atkinson–Han, *Theoretical Numerical Analysis*, Lemma 12.4.7 (4). -/
theorem tendsto_opNorm_sub_comp [CompleteSpace V] {K : ℕ → V →L[𝕜] V} {L : V →L[𝕜] V}
    (hK : IsCollectivelyCompact K) (hL : ∀ x, Tendsto (fun n => K n x) atTop (𝓝 (L x))) :
    Tendsto (fun n => ‖(L - K n) ∘L K n‖) atTop (𝓝 0) := by
  obtain ⟨U, hU, hcpt⟩ := hK
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  have hc0 : (0 : ℝ) < ‖c‖ := lt_trans one_pos hc
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
  have hunif : TendstoUniformlyOn (fun n => (K n : V → V)) L atTop (closure (⋃ i, K i '' U)) :=
    tendstoUniformlyOn_of_tendsto_of_isCompact hL hcpt
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hunif (ε * r / (2 * ‖c‖)) (by positivity))
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  have hbound : ∀ x : V, ‖x‖ < r → ‖((L - K n) ∘L K n) x‖ ≤ ε * r / (2 * ‖c‖) := by
    intro x hx
    have hmem : K n x ∈ closure (⋃ i, K i '' U) :=
      subset_closure (mem_iUnion.2 ⟨n, ⟨x, hrU (mem_ball_zero_iff.2 hx), rfl⟩⟩)
    have hd := hN n hn (K n x) hmem
    rw [dist_eq_norm] at hd
    simpa using hd.le
  refine lt_of_le_of_lt (opNorm_le_of_forall_norm_lt hc hr (by positivity) hbound) ?_
  have heq : ‖c‖ / r * (ε * r / (2 * ‖c‖)) = ε / 2 := by field_simp
  rw [heq]
  linarith

end Limit

end IsCollectivelyCompact

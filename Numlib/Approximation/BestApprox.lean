import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Best approximation

`IsBestApprox K u v`: `v ∈ K` minimizes `‖u - v‖` over `K`. Existence from finite-dimensional
subspaces (Atkinson–Han[^atkinson-han] Thm 3.3.16, Kress[^kress] Thm 3.50), uniqueness in
strictly convex spaces (Atkinson–Han Thm 3.3.21), the Hilbert-space characterizations
(Atkinson–Han Lemma 3.4.1, Thm 3.4.6; Kress Thm 3.51) as glue to Mathlib's orthogonal
projection, and the Lebesgue lemma for projections (Atkinson–Han (3.7.11), (3.7.14), (3.7.21)).

## References

[^atkinson-han]: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
  Analysis Framework*, 3rd edition, Springer, 2009.
[^kress]: Rainer Kress, *Numerical Analysis*, Graduate Texts in Mathematics 181, Springer, 1998.
-/

section Normed

variable {V : Type*} [SeminormedAddCommGroup V]

/-- `v ∈ K` is a best approximation of `u` from `K`. -/
def IsBestApprox (K : Set V) (u v : V) : Prop := v ∈ K ∧ ∀ w ∈ K, ‖u - v‖ ≤ ‖u - w‖

/-- A best approximation attains the distance from `u` to `K`: the infimum defining
`Metric.infDist` is a minimum, realized at `v`. -/
theorem IsBestApprox.norm_sub_eq_infDist {K : Set V} {u v : V} (h : IsBestApprox K u v) :
    ‖u - v‖ = Metric.infDist u K := by
  refine le_antisymm ((Metric.le_infDist ⟨v, h.1⟩).2 fun w hw => ?_) ?_
  · rw [dist_eq_norm]; exact h.2 w hw
  · rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem h.1

/-- Conversely, an element of `K` sitting at distance `Metric.infDist u K` from `u` is a best
approximation. So the pointwise minimality of `IsBestApprox` and the metric description agree,
and either may be used as the definition. -/
theorem isBestApprox_iff_norm_sub_eq_infDist {K : Set V} {u v : V} (hv : v ∈ K) :
    IsBestApprox K u v ↔ ‖u - v‖ = Metric.infDist u K := by
  refine ⟨IsBestApprox.norm_sub_eq_infDist, fun h => ⟨hv, fun w hw => ?_⟩⟩
  rw [h, ← dist_eq_norm]
  exact Metric.infDist_le_dist_of_mem hw

end Normed

section Real

variable {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]

/-- A convex combination of the errors is the error of the convex combination. -/
private theorem sub_combo {a b : ℝ} (hab : a + b = 1) (u v₁ v₂ : V) :
    a • (u - v₁) + b • (u - v₂) = u - (a • v₁ + b • v₂) := by
  rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hab, one_smul]

/-- The set of best approximations from a convex set is convex
(Atkinson–Han, *Theoretical Numerical Analysis*, Thm 3.3.12). -/
theorem convex_setOf_isBestApprox {K : Set V} (hK : Convex ℝ K) (u : V) :
    Convex ℝ {v | IsBestApprox K u v} := by
  rintro v₁ h₁ v₂ h₂ a b ha hb hab
  refine ⟨hK h₁.1 h₂.1 ha hb hab, fun w hw => ?_⟩
  have h₂₁ : ‖u - v₂‖ ≤ ‖u - v₁‖ := h₂.2 _ h₁.1
  calc ‖u - (a • v₁ + b • v₂)‖ = ‖a • (u - v₁) + b • (u - v₂)‖ := by rw [sub_combo hab]
    _ ≤ a * ‖u - v₁‖ + b * ‖u - v₂‖ := by
        refine (norm_add_le _ _).trans_eq ?_
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    _ ≤ (a + b) * ‖u - v₁‖ := by nlinarith
    _ ≤ ‖u - w‖ := by rw [hab, one_mul]; exact h₁.2 w hw

end Real

section Existence

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- A closed subset of a finite-dimensional subspace admits best approximations: the workhorse
behind the two existence theorems below. -/
private theorem exists_isBestApprox_aux [CompleteSpace 𝕜] [LocallyCompactSpace 𝕜] {K : Set V}
    (hK : IsClosed K)
    (hne : K.Nonempty) (S : Submodule 𝕜 V) [FiniteDimensional 𝕜 S] (hKS : K ⊆ S) (u : V) :
    ∃ v, IsBestApprox K u v := by
  obtain ⟨v₀, hv₀⟩ := hne
  have : ProperSpace S := FiniteDimensional.proper 𝕜 S
  have hcont : Continuous fun w : S => ‖u - (w : V)‖ :=
    (continuous_const.sub continuous_subtype_val).norm
  have hTc : IsCompact {w : S | (w : V) ∈ K ∧ ‖u - (w : V)‖ ≤ ‖u - v₀‖} := by
    refine Metric.isCompact_of_isClosed_isBounded
      ((hK.preimage continuous_subtype_val).inter (isClosed_le hcont continuous_const)) ?_
    refine (Metric.isBounded_closedBall (x := (0 : S)) (r := ‖u‖ + ‖u - v₀‖)).subset ?_
    rintro w ⟨-, hw⟩
    have hb : ‖(w : V)‖ ≤ ‖u‖ + ‖u - v₀‖ :=
      calc ‖(w : V)‖ = ‖u - (u - (w : V))‖ := by rw [sub_sub_cancel]
        _ ≤ ‖u‖ + ‖u - (w : V)‖ := norm_sub_le _ _
        _ ≤ ‖u‖ + ‖u - v₀‖ := by gcongr
    simpa [Metric.mem_closedBall, dist_zero_right] using hb
  obtain ⟨w, hwT, hmin⟩ := hTc.exists_isMinOn ⟨⟨v₀, hKS hv₀⟩, hv₀, le_rfl⟩ hcont.continuousOn
  refine ⟨(w : V), hwT.1, fun z hz => ?_⟩
  by_cases hz' : ‖u - z‖ ≤ ‖u - v₀‖
  · exact isMinOn_iff.1 hmin ⟨z, hKS hz⟩ ⟨hz, hz'⟩
  · exact hwT.2.trans (not_le.1 hz').le

/-- Best approximations from finite-dimensional subspaces exist (Atkinson–Han, *Theoretical
Numerical Analysis*, Thm 3.3.16; Kress, *Numerical Analysis*, Thm 3.50). -/
theorem exists_isBestApprox_of_finiteDimensional [CompleteSpace 𝕜] [LocallyCompactSpace 𝕜]
    (K : Submodule 𝕜 V)
    [FiniteDimensional 𝕜 K] (u : V) : ∃ v, IsBestApprox (K : Set V) u v :=
  exists_isBestApprox_aux K.closed_of_finiteDimensional ⟨0, K.zero_mem⟩ K le_rfl u

/-- Best approximations from closed convex finite-dimensional sets exist (a closed subset of a
finite-dimensional subspace); Atkinson–Han, *Theoretical Numerical Analysis*, Thm 3.3.15. -/
theorem exists_isBestApprox_of_isClosed_of_finiteDimensional [CompleteSpace 𝕜]
    [LocallyCompactSpace 𝕜] {K : Set V}
    (hK : IsClosed K) (hne : K.Nonempty) (S : Submodule 𝕜 V) [FiniteDimensional 𝕜 S]
    (hKS : K ⊆ S) (u : V) : ∃ v, IsBestApprox K u v :=
  exists_isBestApprox_aux hK hne S hKS u

end Existence

section Uniqueness

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [StrictConvexSpace ℝ V]

/-- In a strictly convex space, best approximations from a convex set are unique
(Atkinson–Han, *Theoretical Numerical Analysis*, Thm 3.3.21). -/
theorem IsBestApprox.unique {K : Set V} (hK : Convex ℝ K) {u v₁ v₂ : V} (h₁ : IsBestApprox K u v₁)
    (h₂ : IsBestApprox K u v₂) : v₁ = v₂ := by
  by_contra hne
  have hab : (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1 := by norm_num
  have hlt : ‖(2 : ℝ)⁻¹ • (u - v₁) + (2 : ℝ)⁻¹ • (u - v₂)‖ < ‖u - v₁‖ :=
    norm_combo_lt_of_ne le_rfl (h₂.2 _ h₁.1) (fun h => hne (sub_right_injective h))
      (by norm_num) (by norm_num) hab
  rw [sub_combo hab] at hlt
  exact absurd (h₁.2 _ (hK h₁.1 h₂.1 (by norm_num) (by norm_num) hab)) (not_le.2 hlt)

end Uniqueness

section RealHilbert

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Variational characterization on convex sets in a real inner product space
(Atkinson–Han, *Theoretical Numerical Analysis*, Lemma 3.4.1): `v` is a best approximation of `u`
from convex `K` iff `⟪u - v, w - v⟫ ≤ 0` for all `w ∈ K`
(Mathlib: `norm_eq_iInf_iff_real_inner_le_zero`). -/
theorem isBestApprox_iff_inner_le_zero {K : Set V} (hK : Convex ℝ K) {u v : V} (hv : v ∈ K) :
    IsBestApprox K u v ↔ ∀ w ∈ K, inner ℝ (u - v) (w - v) ≤ 0 := by
  rw [isBestApprox_iff_norm_sub_eq_infDist hv, Metric.infDist_eq_iInf]
  simp only [dist_eq_norm]
  exact norm_eq_iInf_iff_real_inner_le_zero hK hv

/-- The metric projection onto a convex set is monotone and non-expansive, in pairs form
(Atkinson–Han, *Theoretical Numerical Analysis*, Prop 3.4.4). -/
theorem IsBestApprox.dist_le_dist {K : Set V} (hK : Convex ℝ K) {u₁ u₂ v₁ v₂ : V}
    (h₁ : IsBestApprox K u₁ v₁) (h₂ : IsBestApprox K u₂ v₂) :
    0 ≤ inner ℝ (v₁ - v₂) (u₁ - u₂) ∧ ‖v₁ - v₂‖ ≤ ‖u₁ - u₂‖ := by
  have e₁ := (isBestApprox_iff_inner_le_zero hK h₁.1).1 h₁ v₂ h₂.1
  have e₂ := (isBestApprox_iff_inner_le_zero hK h₂.1).1 h₂ v₁ h₁.1
  have expand : inner ℝ (u₁ - v₁) (v₂ - v₁) + inner ℝ (u₂ - v₂) (v₁ - v₂)
      = ‖v₁ - v₂‖ ^ 2 - inner ℝ (v₁ - v₂) (u₁ - u₂) := by
    rw [← real_inner_self_eq_norm_sq, real_inner_comm (v₂ - v₁) (u₁ - v₁),
      real_inner_comm (v₁ - v₂) (u₂ - v₂)]
    simp only [inner_sub_left, inner_sub_right]
    ring
  have key : ‖v₁ - v₂‖ ^ 2 ≤ inner ℝ (v₁ - v₂) (u₁ - u₂) := by linarith
  refine ⟨(sq_nonneg _).trans key, ?_⟩
  rcases (norm_nonneg (v₁ - v₂)).eq_or_lt with h | h
  · rw [← h]; exact norm_nonneg _
  · nlinarith [real_inner_le_norm (v₁ - v₂) (u₁ - u₂)]

end RealHilbert

section Hilbert

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- Membership in the orthogonal complement of a span is orthogonality to the generators. -/
private theorem mem_orthogonal_span_range_iff {ι : Type*} (u : ι → V) (x : V) :
    x ∈ (Submodule.span 𝕜 (Set.range u))ᗮ ↔ ∀ j, inner 𝕜 (u j) x = 0 := by
  rw [Submodule.mem_orthogonal']
  refine ⟨fun h j => inner_eq_zero_symm.1 (h _ (Submodule.subset_span (Set.mem_range_self j))),
    fun h y hy => ?_⟩
  have hle : Submodule.span 𝕜 (Set.range u) ≤
      LinearMap.ker ((innerSL 𝕜 x : V →L[𝕜] 𝕜) : V →ₗ[𝕜] 𝕜) := by
    rw [Submodule.span_le, Set.range_subset_iff]
    exact fun j => inner_eq_zero_symm.2 (h j)
  exact hle hy

/-- For subspaces, best approximation iff the error is orthogonal (Atkinson–Han, *Theoretical
Numerical Analysis*, Thm 3.4.6; Kress, *Numerical Analysis*, Thm 3.51). -/
theorem isBestApprox_iff_mem_orthogonal (K : Submodule 𝕜 V) {u v : V} (hv : v ∈ K) :
    IsBestApprox (K : Set V) u v ↔ u - v ∈ Kᗮ := by
  rw [isBestApprox_iff_norm_sub_eq_infDist hv, Metric.infDist_eq_iInf]
  simp only [dist_eq_norm]
  rw [Submodule.mem_orthogonal']
  exact K.norm_eq_iInf_iff_inner_eq_zero hv

/-- The best approximation from a subspace with an orthogonal projection is `P_K u`
(Atkinson–Han, *Theoretical Numerical Analysis*, Thm 3.4.6 and Thm 3.4.7;
Kress, *Numerical Analysis*, Thm 3.52). -/
theorem isBestApprox_starProjection (K : Submodule 𝕜 V) [K.HasOrthogonalProjection] (u : V) :
    IsBestApprox (K : Set V) u (K.starProjection u) :=
  (isBestApprox_iff_mem_orthogonal K (K.starProjection_apply_mem u)).2
    (K.sub_starProjection_mem_orthogonal u)

/-- Uniqueness in a subspace with an orthogonal projection: the orthogonal projection is the
*only* best approximation from `K`. With `isBestApprox_starProjection` this identifies the
metric projection onto a closed subspace of a Hilbert space with `Submodule.starProjection`. -/
theorem IsBestApprox.eq_starProjection (K : Submodule 𝕜 V) [K.HasOrthogonalProjection] {u v : V}
    (h : IsBestApprox (K : Set V) u v) : v = K.starProjection u :=
  (Submodule.eq_starProjection_of_mem_orthogonal h.1
    ((isBestApprox_iff_mem_orthogonal K h.1).1 h)).symm

/-- The normal equations (Kress, *Numerical Analysis*, Cor 3.53): with a basis `u i` of `K`,
`∑ a i • u i` is the best approximation of `w` iff `∑_i a i ⟪u j, u i⟫ = ⟪u j, w⟫` for all `j`. -/
theorem isBestApprox_sum_iff {ι : Type*} [Fintype ι] (u : ι → V) (a : ι → 𝕜) (w : V) :
    IsBestApprox (Submodule.span 𝕜 (Set.range u) : Set V) w (∑ i, a i • u i) ↔
      ∀ j, ∑ i, a i * inner 𝕜 (u j) (u i) = inner 𝕜 (u j) w := by
  rw [isBestApprox_iff_mem_orthogonal _ (Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))),
    mem_orthogonal_span_range_iff]
  simp only [inner_sub_right, inner_sum, inner_smul_right]
  exact forall_congr' fun _ => by rw [sub_eq_zero, eq_comm]

end Hilbert

section Lebesgue

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- Turn a uniform bound `r ≤ C ‖u - q‖` over a nonempty set into a bound by the distance. -/
private theorem le_mul_infDist {C r : ℝ} {u : V} {S : Set V} (hC : 0 ≤ C) (hS : S.Nonempty)
    (h : ∀ q ∈ S, r ≤ C * ‖u - q‖) : r ≤ C * Metric.infDist u S := by
  rcases hC.lt_or_eq with hC' | hC'
  · refine (div_le_iff₀' hC').1 ((Metric.le_infDist hS).2 fun q hq => ?_)
    rw [dist_eq_norm, div_le_iff₀' hC']
    exact h q hq
  · obtain ⟨q, hq⟩ := hS
    have := h q hq
    rw [← hC'] at this ⊢
    simpa using this

/-- A bounded projection acts as the identity on its range. -/
private theorem apply_of_mem_range {P : V →L[𝕜] V} (hP : IsIdempotentElem P) {q : V}
    (hq : q ∈ LinearMap.range (P : V →ₗ[𝕜] V)) : P q = q := by
  obtain ⟨y, rfl⟩ := hq
  simpa using DFunLike.congr_fun hP y

/-- Pointwise form: `‖u - P u‖ ≤ (1 + ‖P‖) ‖u - q‖` for every `q` in the range of `P`. -/
theorem norm_sub_apply_le_of_isIdempotentElem_of_mem (P : V →L[𝕜] V) (hP : IsIdempotentElem P)
    (u : V) {q : V} (hq : q ∈ LinearMap.range (P : V →ₗ[𝕜] V)) :
    ‖u - P u‖ ≤ (1 + ‖P‖) * ‖u - q‖ := by
  have key : u - P u = (u - q) - P (u - q) := by
    rw [map_sub, apply_of_mem_range hP hq]; abel
  rw [key]
  refine (norm_sub_le _ _).trans ?_
  rw [add_mul, one_mul]
  gcongr
  exact P.le_opNorm _

/-- Lebesgue lemma: for a bounded projection `P` (`P ∘ P = P`) onto `S = range P`,
`‖u - P u‖ ≤ (1 + ‖P‖) dist(u, S)`. That is, `P u` is a quasi-best approximation from `S`, with
`1 + ‖P‖` as the quasi-optimality constant. This is the abstract form of the estimates
Atkinson–Han, *Theoretical Numerical Analysis*, (3.7.11), (3.7.14) and (3.7.21) make for
particular projection methods. -/
theorem norm_sub_apply_le_of_isIdempotentElem (P : V →L[𝕜] V) (hP : IsIdempotentElem P) (u : V) :
    ‖u - P u‖ ≤ (1 + ‖P‖) * Metric.infDist u (LinearMap.range (P : V →ₗ[𝕜] V) : Set V) :=
  le_mul_infDist (by positivity) ⟨0, zero_mem _⟩ fun _ hq =>
    norm_sub_apply_le_of_isIdempotentElem_of_mem P hP u hq

/-- Sharper form `‖u - P u‖ ≤ ‖1 - P‖ dist(u, S)`. -/
theorem norm_sub_apply_le_of_isIdempotentElem' (P : V →L[𝕜] V) (hP : IsIdempotentElem P) (u : V) :
    ‖u - P u‖ ≤ ‖(1 : V →L[𝕜] V) - P‖ *
      Metric.infDist u (LinearMap.range (P : V →ₗ[𝕜] V) : Set V) := by
  refine le_mul_infDist (norm_nonneg _) ⟨0, zero_mem _⟩ fun q hq => ?_
  have key : u - P u = ((1 : V →L[𝕜] V) - P) (u - q) := by
    change u - P u = (u - q) - P (u - q)
    rw [map_sub, apply_of_mem_range hP hq]; abel
  rw [key]
  exact ((1 : V →L[𝕜] V) - P).le_opNorm _

/-- A nonzero bounded projection has norm `≥ 1`
(Atkinson–Han, *Theoretical Numerical Analysis*, Exercise 3.6.7). -/
theorem one_le_norm_of_isIdempotentElem {P : V →L[𝕜] V} (hP : IsIdempotentElem P) (h0 : P ≠ 0) :
    1 ≤ ‖P‖ := by
  have hpos : 0 < ‖P‖ := norm_pos_iff.2 h0
  have hle : ‖P‖ ≤ ‖P‖ * ‖P‖ := by
    conv_lhs => rw [← hP]
    exact norm_mul_le P P
  nlinarith

end Lebesgue

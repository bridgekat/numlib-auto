import Numlib.Analysis.Convex.Saddle.Rademacher
import Numlib.Analysis.Convex.Saddle.Subdifferential
import NumlibSurface.Rockafellar.Chapter07.Section33

/-!
# Rockafellar §35: continuity and differentiability of saddle-functions

Surface file for R. Tyrrell Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §35
(pp. 370–378): the §10 continuity and convergence theorems and the §23/§24/§25 differential theory,
read for a **concave-convex** function of a pair.

All twelve numbered results of §35 are formalized: Theorems 35.1–35.10 and Corollaries 35.7.1 and
35.8.1.

**The sign asymmetry.** `K` is concave in `u` and convex in `v`, so `∂₁K (u, v)` holds the
*super*gradients of the concave slice `K (·, v)` at `u` and `∂₂K (u, v)` the *sub*gradients of the
convex slice `K (u, ·)` at `v`, with `∂K = ∂₁K × ∂₂K`. The two inequalities point in **opposite**
directions, so `∂K` is not the subdifferential of `K` read on `ℝᵐ⁺ⁿ`, and is not a monotone
relation. The dictionary is `mem_subdiff₁_iff_neg_mem_subdifferential_neg`, and that single
`u* ↦ -u*` is what §37's Corollary 37.5.2 inserts to recover monotonicity.

`K′(u, v; u′, v′)` is `dirDerivReal K (u, v) (u′, v′)`, a genuine limit of difference quotients.
The `EReal`-valued `dirDeriv` of §23 is an infimum, which is that limit only along a line; the
difference between the two is exactly what Theorem 35.6 is about.

## Main definitions

* `subdiff₁`, `subdiff₂`, `subdiff` — Rockafellar's `∂₁K`, `∂₂K` and `∂K = ∂₁K × ∂₂K`. `∂K` is a
  **product**, not a set of pairs cut out by one inequality.

## Main results

* `theorem_35_1_continuousOn`, `theorem_35_1_lipschitzian` — a finite concave-convex function on a
  relatively open `C × D` is continuous, and Lipschitzian on every compact subset.
* `theorem_35_2`, `theorem_35_3`, `theorem_35_3_dense`, `theorem_35_4`, `theorem_35_5` — the
  equi-Lipschitz, parametric-continuity and convergence theorems of §10, for saddle-functions.
* `subdiff_eq_prod`, `mem_subdiff₁_iff`, `mem_subdiff₂_iff`,
  `mem_subdiff₁_iff_neg_mem_subdifferential_neg`, `convex_subdiff`,
  `superdifferentialFstOn_univ_eq`, `subdifferentialSndOn_univ_eq`,
  `saddleSubdifferentialOn_univ_eq` — the subdifferential of a saddle-function and the bridges
  between its two readings.
* `theorem_35_6`, `theorem_35_6_tendsto`, `theorem_35_6_concaveConvex`, `theorem_35_6_posHom` —
  the joint directional derivative exists, and is itself a finite positively homogeneous
  concave-convex function.
* `theorem_35_7_fst`, `theorem_35_7_snd`, `theorem_35_7_subdiff`, `corollary_35_7_1_fst`,
  `corollary_35_7_1_snd`, `corollary_35_7_1_subdiff` — semicontinuity of the two directional
  derivatives and of the subdifferential mapping.
* `theorem_35_8`, `theorem_35_8_gradient`, `corollary_35_8_1` — differentiability is a unique
  subgradient, and then `∂K (u, v) = {∇K (u, v)}`.
* `theorem_35_9_measure`, `theorem_35_9_dense`, `theorem_35_9_continuousOn`, `theorem_35_10`,
  `theorem_35_10_uniform` — differentiability almost everywhere with a continuous gradient, and
  convergence of gradients, uniformly on compact subsets.

## Divergences from the book

Theorems 35.6–35.10 are stated for a **real-valued** `K` on an open rectangle `C × D`, where the
book's `K` is `EReal`-valued on `ℝᵐ × ℝⁿ` and merely finite on `C × D`. So `∂₁K` and `∂₂K` are
tested against `C` and `D` rather than all of `ℝᵐ` and `ℝⁿ`; `superdifferentialFstOn_univ_eq` and
its two companions are the bridge, and the readings agree once `K` is extended off `C × D` by the
simple extension, which makes the extra inequalities vacuous.

The `εB` of Theorems 35.7, 35.9 and 35.10 is the **supremum** ball, Mathlib's norm on a product. It
differs from the book's Euclidean ball by a factor bounded by `√2`, and every such statement
quantifies over all `ε > 0`.
-/

open Set Filter Topology MeasureTheory
open scoped NNReal Pointwise

namespace Rockafellar

open ConvexAnalysis

/-! ### Two bookkeeping steps -/

section Bookkeeping

variable {m n : ℕ}

private theorem exists_lipschitz_of_lipschitzOnWith {E : Type*} [NormedAddCommGroup E]
    {f : E → ℝ} {S : Set E} {k : ℝ≥0} (h : LipschitzOnWith k f S) :
    ∃ α : ℝ, 0 ≤ α ∧ ∀ y ∈ S, ∀ x ∈ S, |f y - f x| ≤ α * ‖y - x‖ := by
  refine ⟨k, k.coe_nonneg, fun y hy x hx => ?_⟩
  have hd := h.dist_le_mul y hy x hx
  rwa [Real.dist_eq, dist_eq_norm] at hd

private theorem isCompact_prod_projections {C : Set (Rn m)} {D : Set (Rn n)}
    {E : Set (Rn m × Rn n)} (hE : IsCompact E) (hEsub : E ⊆ C ×ˢ D) :
    IsCompact (Prod.fst '' E) ∧ IsCompact (Prod.snd '' E) ∧ Prod.fst '' E ⊆ C ∧
      Prod.snd '' E ⊆ D ∧ E ⊆ (Prod.fst '' E) ×ˢ (Prod.snd '' E) := by
  refine ⟨hE.image continuous_fst, hE.image continuous_snd, ?_, ?_,
    fun p hp => ⟨⟨p, hp, rfl⟩, ⟨p, hp, rfl⟩⟩⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact (hEsub hp).1
  · rintro _ ⟨p, hp, rfl⟩
    exact (hEsub hp).2

end Bookkeeping

/-! ### Theorem 35.1 -/

section Thm351

variable {m n : ℕ} {C : Set (Rn m)} {D : Set (Rn n)} {K : Rn m × Rn n → ℝ}

/-- **Theorem 35.1**, first assertion: a finite concave-convex `K` on `C × D`, with `C` and `D`
relatively open convex, is continuous relative to `C × D`. "Relatively open" is `ri C = C`. -/
theorem theorem_35_1_continuousOn (hC : Convex ℝ C) (hCro : ri C = C) (hD : Convex ℝ D)
    (hDro : ri D = D) (hK : ConcaveConvexOn C D K) : ContinuousOn K (C ×ˢ D) := by
  have h := hK.continuousOn hC hD
  rwa [hCro, hDro] at h

/-- **Theorem 35.1**, second assertion: `K` is Lipschitzian on every closed bounded subset of
`C × D`. In `ℝᵐ⁺ⁿ` such a set is compact and lies in the rectangle spanned by its projections. -/
theorem theorem_35_1_lipschitzian (hC : Convex ℝ C) (hCro : ri C = C) (hD : Convex ℝ D)
    (hDro : ri D = D) (hK : ConcaveConvexOn C D K) {E : Set (Rn m × Rn n)} (hEcl : IsClosed E)
    (hEb : Bornology.IsBounded E) (hEsub : E ⊆ C ×ˢ D) :
    ∃ α : ℝ, 0 ≤ α ∧ ∀ q ∈ E, ∀ p ∈ E, |K q - K p| ≤ α * ‖q - p‖ := by
  obtain ⟨hS, hT, hSC, hTD, hrect⟩ := isCompact_prod_projections
    (Metric.isCompact_of_isClosed_isBounded hEcl hEb) hEsub
  have hSC' : Prod.fst '' E ⊆ ri C := by rw [hCro]; exact hSC
  have hTD' : Prod.snd '' E ⊆ ri D := by rw [hDro]; exact hTD
  obtain ⟨k, hk⟩ := hK.exists_lipschitzOnWith_of_isCompact hC hD hS hSC' hT hTD'
  exact exists_lipschitz_of_lipschitzOnWith (hk.mono hrect)

end Thm351

/-! ### Theorem 35.2 -/

section Thm352

variable {m n : ℕ} {ι : Type*} {C C' : Set (Rn m)} {D D' : Set (Rn n)}

/-- **Theorem 35.2.** For `C`, `D` relatively open convex and a family of finite concave-convex
functions on `C × D` that is pointwise bounded on a dense `C′ × D′`, the family is uniformly
bounded and equi-Lipschitzian relative to every closed bounded subset of `C × D`. The family is
indexed by an arbitrary type, so it may be empty.

Stated with `cl C′ ⊇ C` and `cl D′ ⊇ D` where the book asks for `conv (cl (C′ × D′)) ⊇ C × D`; the
convex hull is dropped, as `Rockafellar.theorem_10_6_ab` already does for the one-variable §10. -/
theorem theorem_35_2 (hC : Convex ℝ C) (hCro : ri C = C) (hD : Convex ℝ D) (hDro : ri D = D)
    {K : ι → Rn m × Rn n → ℝ} (hK : ∀ i, ConcaveConvexOn C D (K i)) (hC'sub : C' ⊆ C)
    (hCdense : C ⊆ closure C') (hD'sub : D' ⊆ D) (hDdense : D ⊆ closure D')
    (hbdd : ∀ u ∈ C', ∀ v ∈ D', Bornology.IsBounded (Set.range fun i => K i (u, v)))
    {E : Set (Rn m × Rn n)} (hEcl : IsClosed E) (hEb : Bornology.IsBounded E)
    (hEsub : E ⊆ C ×ˢ D) :
    (∃ α₁ α₂ : ℝ, ∀ p ∈ E, ∀ i, α₁ ≤ K i p ∧ K i p ≤ α₂) ∧
      ∃ α : ℝ, 0 ≤ α ∧ ∀ i, ∀ q ∈ E, ∀ p ∈ E, |K i q - K i p| ≤ α * ‖q - p‖ := by
  obtain ⟨hS, hT, hSC, hTD, hrect⟩ := isCompact_prod_projections
    (Metric.isCompact_of_isClosed_isBounded hEcl hEb) hEsub
  have hSC' : Prod.fst '' E ⊆ ri C := by rw [hCro]; exact hSC
  have hTD' : Prod.snd '' E ⊆ ri D := by rw [hDro]; exact hTD
  have hC'ri : C' ⊆ ri C := by rw [hCro]; exact hC'sub
  have hCd : ri C ⊆ closure C' := by rw [hCro]; exact hCdense
  have hD'ri : D' ⊆ ri D := by rw [hDro]; exact hD'sub
  have hDd : ri D ⊆ closure D' := by rw [hDro]; exact hDdense
  obtain ⟨⟨M, hM0, hM⟩, k, hk⟩ := exists_forall_abs_le_and_lipschitzOnWith_prod hC hD hK
    hC'ri hCd hD'ri hDd hbdd hS hSC' hT hTD'
  refine ⟨⟨-M, M, fun p hp i => abs_le.1 (hM i p (hrect hp))⟩, k, k.coe_nonneg,
    fun i q hq p hp => ?_⟩
  have hd := ((hk i).mono hrect).dist_le_mul q hq p hp
  rwa [Real.dist_eq, dist_eq_norm] at hd

end Thm352

/-! ### Theorem 35.3 -/

section Thm353

variable {m n : ℕ} {C C' : Set (Rn m)} {D D' : Set (Rn n)} {T : Type*} [TopologicalSpace T]
  [LocallyCompactSpace T] {F : (Rn m × Rn n) × T → ℝ}

/-- **Theorem 35.3.** For `C`, `D` relatively open convex, `T` locally compact, and `F (u, v, t)`
concave in `u`, convex in `v` and continuous in `t`, `F` is jointly continuous on `C × D × T`. The
two convex variables are grouped as a pair, since the concave-convex hypothesis lives there. -/
theorem theorem_35_3 (hC : Convex ℝ C) (hCro : ri C = C) (hD : Convex ℝ D) (hDro : ri D = D)
    (hF : ∀ t : T, ConcaveConvexOn C D fun p => F (p, t))
    (hcont : ∀ u ∈ C, ∀ v ∈ D, Continuous fun t => F ((u, v), t)) :
    ContinuousOn F ((C ×ˢ D) ×ˢ (Set.univ : Set T)) := by
  have hc : ∀ u ∈ ri C, ∀ v ∈ ri D, Continuous fun t => F ((u, v), t) := by
    rw [hCro, hDro]; exact hcont
  have h := continuousOn_prod_of_concaveConvexOn' hC hD hF hc
  rwa [hCro, hDro] at h

/-- **Theorem 35.3**, weakened hypothesis: continuity in `t` need only hold at the points of dense
subsets `C′` and `D′`. -/
theorem theorem_35_3_dense (hC : Convex ℝ C) (hCro : ri C = C) (hD : Convex ℝ D) (hDro : ri D = D)
    (hF : ∀ t : T, ConcaveConvexOn C D fun p => F (p, t)) (hC'sub : C' ⊆ C)
    (hCdense : C ⊆ closure C') (hD'sub : D' ⊆ D) (hDdense : D ⊆ closure D')
    (hcont : ∀ u ∈ C', ∀ v ∈ D', Continuous fun t => F ((u, v), t)) :
    ContinuousOn F ((C ×ˢ D) ×ˢ (Set.univ : Set T)) := by
  have hC'ri : C' ⊆ ri C := by rw [hCro]; exact hC'sub
  have hCd : ri C ⊆ closure C' := by rw [hCro]; exact hCdense
  have hD'ri : D' ⊆ ri D := by rw [hDro]; exact hD'sub
  have hDd : ri D ⊆ closure D' := by rw [hDro]; exact hDdense
  have h := continuousOn_prod_of_concaveConvexOn hC hD hF hC'ri hCd hD'ri hDd hcont
  rwa [hCro, hDro] at h

end Thm353

/-! ### Theorems 35.4 and 35.5 -/

section Convergence

variable {m n : ℕ} {C C' : Set (Rn m)} {D D' : Set (Rn n)} {K : ℕ → Rn m × Rn n → ℝ}

/-- **Theorem 35.4.** If finite concave-convex `K 1, K 2, …` on `C × D` converge to finite limits
on a dense `C′ × D′`, the limit exists everywhere on `C × D`, is finite and concave-convex, and the
convergence is uniform on every closed bounded subset of `C × D`. -/
theorem theorem_35_4 (hC : Convex ℝ C) (hCro : ri C = C) (hD : Convex ℝ D) (hDro : ri D = D)
    (hK : ∀ i, ConcaveConvexOn C D (K i)) (hC'sub : C' ⊆ C) (hCdense : C ⊆ closure C')
    (hD'sub : D' ⊆ D) (hDdense : D ⊆ closure D')
    (hcv : ∀ u ∈ C', ∀ v ∈ D', ∃ L : ℝ, Tendsto (fun i => K i (u, v)) atTop (𝓝 L)) :
    ∃ L : Rn m × Rn n → ℝ, ConcaveConvexOn C D L ∧
      (∀ p ∈ C ×ˢ D, Tendsto (fun i => K i p) atTop (𝓝 (L p))) ∧
      ∀ ⦃E : Set (Rn m × Rn n)⦄, IsClosed E → Bornology.IsBounded E → E ⊆ C ×ˢ D →
        TendstoUniformlyOn K L atTop E := by
  have hC'ri : C' ⊆ ri C := by rw [hCro]; exact hC'sub
  have hCd : ri C ⊆ closure C' := by rw [hCro]; exact hCdense
  have hD'ri : D' ⊆ ri D := by rw [hDro]; exact hD'sub
  have hDd : ri D ⊆ closure D' := by rw [hDro]; exact hDdense
  obtain ⟨L, hLcc, hLt, huc⟩ :=
    exists_tendstoUniformlyOn_prod_of_dense' hC hD hK hC'ri hCd hD'ri hDd hcv
  rw [hCro, hDro] at hLcc hLt
  refine ⟨L, hLcc, hLt, fun E hEcl hEb hEsub => ?_⟩
  obtain ⟨hS, hT, hSC, hTD, hrect⟩ := isCompact_prod_projections
    (Metric.isCompact_of_isClosed_isBounded hEcl hEb) hEsub
  have hSC' : Prod.fst '' E ⊆ ri C := by rw [hCro]; exact hSC
  have hTD' : Prod.snd '' E ⊆ ri D := by rw [hDro]; exact hTD
  exact (huc hS hSC' hT hTD').mono hrect

/-- **Theorem 35.5.** With "the limit exists" weakened to "the values are bounded", some
subsequence converges to a finite concave-convex function, uniformly on closed bounded subsets.
This is Arzelà–Ascoli for saddle-functions; the countable dense set comes from separability. -/
theorem theorem_35_5 (hC : Convex ℝ C) (hCro : ri C = C) (hD : Convex ℝ D) (hDro : ri D = D)
    (hK : ∀ i, ConcaveConvexOn C D (K i)) (hC'sub : C' ⊆ C) (hCdense : C ⊆ closure C')
    (hD'sub : D' ⊆ D) (hDdense : D ⊆ closure D')
    (hbdd : ∀ u ∈ C', ∀ v ∈ D', Bornology.IsBounded (Set.range fun i => K i (u, v))) :
    ∃ (φ : ℕ → ℕ) (L : Rn m × Rn n → ℝ), StrictMono φ ∧ ConcaveConvexOn C D L ∧
      (∀ p ∈ C ×ˢ D, Tendsto (fun i => K (φ i) p) atTop (𝓝 (L p))) ∧
      ∀ ⦃E : Set (Rn m × Rn n)⦄, IsClosed E → Bornology.IsBounded E → E ⊆ C ×ˢ D →
        TendstoUniformlyOn (fun i => K (φ i)) L atTop E := by
  have hC'ri : C' ⊆ ri C := by rw [hCro]; exact hC'sub
  have hCd : ri C ⊆ closure C' := by rw [hCro]; exact hCdense
  have hD'ri : D' ⊆ ri D := by rw [hDro]; exact hD'sub
  have hDd : ri D ⊆ closure D' := by rw [hDro]; exact hDdense
  obtain ⟨φ, L, hφ, hLcc, hLt, huc⟩ :=
    exists_subseq_tendstoUniformlyOn_prod hC hD hK hC'ri hCd hD'ri hDd hbdd
  rw [hCro, hDro] at hLcc hLt
  refine ⟨φ, L, hφ, hLcc, hLt, fun E hEcl hEb hEsub => ?_⟩
  obtain ⟨hS, hT, hSC, hTD, hrect⟩ := isCompact_prod_projections
    (Metric.isCompact_of_isClosed_isBounded hEcl hEb) hEsub
  have hSC' : Prod.fst '' E ⊆ ri C := by rw [hCro]; exact hSC
  have hTD' : Prod.snd '' E ⊆ ri D := by rw [hDro]; exact hTD
  exact (huc hS hSC' hT hTD').mono hrect

end Convergence

/-! ### The subdifferential of a saddle-function

Rockafellar's definition, for an arbitrary — hence `EReal`-valued — concave-convex `K`. -/

section Subdifferential

variable {m n : ℕ}

/-- Rockafellar's `∂₁K (u, v) = ∂_u K (u, v)`: the `u*` with `K (u′, v) ≤ K (u, v) + ⟨u*, u′ - u⟩`
for every `u′`, i.e. the **super**gradients at `u` of the concave slice `K (·, v)`. An `abbrev` for
`superdifferential` at the Euclidean pairing. -/
abbrev subdiff₁ (K : Rn m × Rn n → EReal) (p : Rn m × Rn n) : Set (Rn m) :=
  superdifferential (pairing m) (fun u => K (u, p.2)) p.1

/-- Rockafellar's `∂₂K (u, v) = ∂_v K (u, v)`: the `v*` with `K (u, v) + ⟨v*, v′ - v⟩ ≤ K (u, v′)`
for every `v′`, i.e. the **sub**gradients at `v` of the convex slice `K (u, ·)`. The inequality
points the other way from `subdiff₁`'s; that asymmetry is the whole sign convention. -/
abbrev subdiff₂ (K : Rn m × Rn n → EReal) (p : Rn m × Rn n) : Set (Rn n) :=
  subdifferential (pairing n) (fun v => K (p.1, v)) p.2

/-- Rockafellar's `∂K (u, v) = ∂₁K (u, v) × ∂₂K (u, v)`. It is a **product**, not a set of joint
subgradients, and its two factors carry opposite inequalities, so it is not the subdifferential of
`K` read as a function on `ℝᵐ⁺ⁿ`. -/
abbrev subdiff (K : Rn m × Rn n → EReal) (p : Rn m × Rn n) : Set (Rn m × Rn n) :=
  saddleSubdifferential (pairing m) (pairing n) K p

variable {K : Rn m × Rn n → EReal} {p : Rn m × Rn n}

/-- `∂K (u, v) = ∂₁K (u, v) × ∂₂K (u, v)`, definitionally. -/
theorem subdiff_eq_prod : subdiff K p = subdiff₁ K p ×ˢ subdiff₂ K p := rfl

/-- The defining inequality of `∂₁K (u, v)`. -/
theorem mem_subdiff₁_iff {y : Rn m} :
    y ∈ subdiff₁ K p ↔ ∀ u' : Rn m, K (u', p.2) ≤ K p + ((pairing m (u' - p.1) y : ℝ) : EReal) :=
  Iff.rfl

/-- The defining inequality of `∂₂K (u, v)`, pointing the opposite way. -/
theorem mem_subdiff₂_iff {y : Rn n} :
    y ∈ subdiff₂ K p ↔ ∀ v' : Rn n, K p + ((pairing n (v' - p.2) y : ℝ) : EReal) ≤ K (p.1, v') :=
  Iff.rfl

/-- **Where the sign flip sits.** `u*` is a supergradient of `K (·, v)` at `u` exactly when `-u*`
is a subgradient of `-K (·, v)` there. This negation is what §37 inserts in Corollary 37.5.2 to
make the relation monotone and in Corollary 37.5.1 to make the map `(u - u*, v* + v)`. -/
theorem mem_subdiff₁_iff_neg_mem_subdifferential_neg {y : Rn m} :
    y ∈ subdiff₁ K p ↔ -y ∈ subdifferential (pairing m) (fun u => -K (u, p.2)) p.1 :=
  mem_superdifferential_iff_neg_mem_subdifferential_neg

/-- `∂K (u, v)` is a convex subset of `ℝᵐ × ℝⁿ`, with no hypothesis on `K` at all. -/
theorem convex_subdiff : Convex ℝ (subdiff K p) := convex_saddleSubdifferential

end Subdifferential

/-! ### The bridge between the two readings of `∂K` -/

section Bridge

variable {m n : ℕ} (K : Rn m × Rn n → ℝ) (p : Rn m × Rn n)

/-- `∂₁` in rectangle-relative form is `∂₁` in the book's global form, at `C = ℝᵐ`. -/
theorem superdifferentialFstOn_univ_eq :
    superdifferentialFstOn (Set.univ : Set (Rn m)) K p
        = subdiff₁ (fun z => ((K z : ℝ) : EReal)) p := by
  ext y
  simp only [mem_superdifferentialFstOn, Set.mem_univ, forall_const, mem_superdifferential,
    pairing_apply]
  refine forall_congr' fun u' => ?_
  rw [← EReal.coe_add, EReal.coe_le_coe_iff]

/-- `∂₂` in rectangle-relative form is `∂₂` in the book's global form, at `D = ℝⁿ`. -/
theorem subdifferentialSndOn_univ_eq :
    subdifferentialSndOn (Set.univ : Set (Rn n)) K p
        = subdiff₂ (fun z => ((K z : ℝ) : EReal)) p := by
  ext y
  simp only [mem_subdifferentialSndOn, Set.mem_univ, forall_const, mem_subdifferential,
      pairing_apply]
  refine forall_congr' fun v' => ?_
  rw [← EReal.coe_add, EReal.coe_le_coe_iff]

/-- `∂K` in rectangle-relative form is `∂K` in the book's global form, at `C × D = ℝᵐ × ℝⁿ`. -/
theorem saddleSubdifferentialOn_univ_eq :
    saddleSubdifferentialOn (Set.univ : Set (Rn m)) (Set.univ : Set (Rn n)) K p
      = subdiff (fun z => ((K z : ℝ) : EReal)) p := by
  rw [subdiff_eq_prod, ← superdifferentialFstOn_univ_eq, ← subdifferentialSndOn_univ_eq]
  rfl

end Bridge

/-! ### Theorem 35.6, the splitting identity -/

section Thm356

variable {m n : ℕ} {C : Set (Rn m)} {D : Set (Rn n)} {K : Rn m × Rn n → ℝ} {u : Rn m} {v : Rn n}

/-- **Theorem 35.6**, the displayed equation: for `K` concave-convex and finite on an open
`C × D` and `(u, v) ∈ C × D`, `K′(u, v; u′, v′) = K′(u, v; u′, 0) + K′(u, v; 0, v′)`. Convexity of
`C` and `D` is not needed — only room around each point in each variable separately. -/
theorem theorem_35_6 (hCo : IsOpen C) (_hC : Convex ℝ C) (hDo : IsOpen D) (_hD : Convex ℝ D)
    (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D) (q : Rn m × Rn n) :
    dirDerivReal K (u, v) q
      = dirDerivReal K (u, v) (q.1, 0) + dirDerivReal K (u, v) (0, q.2) := by
  rw [dirDerivReal_prod hCo hDo hK hu hv q, dirDerivReal_prod_fst hCo hDo hK hu hv q.1,
    dirDerivReal_prod_snd hCo hDo hK hu hv q.2]

/-- **Theorem 35.6**, the existence clause: the joint difference quotient really has a limit, so
`K′(u, v; u′, v′)` exists. This is the part the book calls "problematical". -/
theorem theorem_35_6_tendsto (hCo : IsOpen C) (_hC : Convex ℝ C) (hDo : IsOpen D)
    (_hD : Convex ℝ D) (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D)
    (q : Rn m × Rn n) :
    Tendsto (fun t : ℝ => (K ((u, v) + t • q) - K (u, v)) / t) (𝓝[>] (0 : ℝ))
      (𝓝 (dirDerivReal K (u, v) q)) := by
  rw [dirDerivReal_prod hCo hDo hK hu hv q]
  exact tendsto_slope_dirDerivReal_prod hCo hDo hK hu hv q

/-- **Theorem 35.6**, the shape clause: `K′(u, v; ·, ·)` is a finite concave-convex function on
the whole of `ℝᵐ × ℝⁿ`. -/
theorem theorem_35_6_concaveConvex (hCo : IsOpen C) (_hC : Convex ℝ C) (hDo : IsOpen D)
    (_hD : Convex ℝ D) (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D) :
    ConcaveConvexOn (Set.univ : Set (Rn m)) (Set.univ : Set (Rn n))
      (dirDerivReal K (u, v)) :=
  concaveConvexOn_dirDerivReal hCo hDo hK hu hv

/-- **Theorem 35.6**, the homogeneity clause: `K′(u, v; ·, ·)` is positively homogeneous. -/
theorem theorem_35_6_posHom (hCo : IsOpen C) (_hC : Convex ℝ C) (hDo : IsOpen D)
    (_hD : Convex ℝ D) (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D) {c : ℝ}
    (hc : 0 < c) (q : Rn m × Rn n) :
    dirDerivReal K (u, v) (c • q) = c * dirDerivReal K (u, v) q :=
  dirDerivReal_prod_smul hCo hDo hK hu hv hc q

end Thm356

/-! ### Theorem 35.7 and Corollary 35.7.1 -/

section Thm357

variable {m n : ℕ} {C : Set (Rn m)} {D : Set (Rn n)} {Ks : ℕ → Rn m × Rn n → ℝ}
  {K : Rn m × Rn n → ℝ} {u : Rn m} {v : Rn n} {us : ℕ → Rn m} {vs : ℕ → Rn n}

/-- **Theorem 35.7**, first inequality: `liminf_i K_i′(u_i, v_i; u′, 0) ≥ K′(u, v; u′, 0)`, spelled
without junk values as: every real `μ` below the right-hand side eventually falls below
`K_i′(u_i, v_i; u′, 0)`. The step the book leaves out is that finite concave-convex functions
converge *continuously*, `K i (u i, v i) → K (u, v)` along a moving sequence. -/
theorem theorem_35_7_fst (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D) (hD : Convex ℝ D)
    (hKs : ∀ i, ConcaveConvexOn C D (Ks i)) (hK : ConcaveConvexOn C D K)
    (hconv : ∀ p ∈ C ×ˢ D, Tendsto (fun i => Ks i p) atTop (𝓝 (K p))) (hu : u ∈ C) (hv : v ∈ D)
    (hus : Tendsto us atTop (𝓝 u)) (hvs : Tendsto vs atTop (𝓝 v)) (u' : Rn m) {μ : ℝ}
    (hμ : μ < dirDerivReal K (u, v) (u', 0)) :
    ∀ᶠ i in atTop, μ < dirDerivReal (Ks i) (us i, vs i) (u', 0) := by
  rw [dirDerivReal_prod_fst hCo hDo hK hu hv u'] at hμ
  filter_upwards [eventually_lt_dirDerivReal_fst hCo hC hDo hD hKs hK hconv hu hv hus hvs hμ,
    hus.eventually_mem (hCo.mem_nhds hu), hvs.eventually_mem (hDo.mem_nhds hv)] with i h hui hvi
  rwa [dirDerivReal_prod_fst hCo hDo (hKs i) hui hvi u']

/-- **Theorem 35.7**, second inequality: `limsup_i K_i′(u_i, v_i; 0, v′) ≤ K′(u, v; 0, v′)`. -/
theorem theorem_35_7_snd (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D) (hD : Convex ℝ D)
    (hKs : ∀ i, ConcaveConvexOn C D (Ks i)) (hK : ConcaveConvexOn C D K)
    (hconv : ∀ p ∈ C ×ˢ D, Tendsto (fun i => Ks i p) atTop (𝓝 (K p))) (hu : u ∈ C) (hv : v ∈ D)
    (hus : Tendsto us atTop (𝓝 u)) (hvs : Tendsto vs atTop (𝓝 v)) (v' : Rn n) {μ : ℝ}
    (hμ : dirDerivReal K (u, v) (0, v') < μ) :
    ∀ᶠ i in atTop, dirDerivReal (Ks i) (us i, vs i) (0, v') < μ := by
  rw [dirDerivReal_prod_snd hCo hDo hK hu hv v'] at hμ
  filter_upwards [eventually_dirDerivReal_snd_lt hCo hC hDo hD hKs hK hconv hu hv hus hvs hμ,
    hus.eventually_mem (hCo.mem_nhds hu), hvs.eventually_mem (hDo.mem_nhds hv)] with i h hui hvi
  rwa [dirDerivReal_prod_snd hCo hDo (hKs i) hui hvi v']

/-- **Theorem 35.7**, third assertion: given `ε > 0` there is an `i₀` with
`∂K_i (u_i, v_i) ⊆ ∂K (u, v) + εB` for all `i ≥ i₀`. -/
theorem theorem_35_7_subdiff (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D) (hD : Convex ℝ D)
    (hKs : ∀ i, ConcaveConvexOn C D (Ks i)) (hK : ConcaveConvexOn C D K)
    (hconv : ∀ p ∈ C ×ˢ D, Tendsto (fun i => Ks i p) atTop (𝓝 (K p))) (hu : u ∈ C) (hv : v ∈ D)
    (hus : Tendsto us atTop (𝓝 u)) (hvs : Tendsto vs atTop (𝓝 v)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, saddleSubdifferentialOn C D (Ks i) (us i, vs i)
      ⊆ saddleSubdifferentialOn C D K (u, v) + Metric.closedBall (0 : Rn m × Rn n) ε :=
  eventually_saddleSubdifferentialOn_subset hCo hC hDo hD hKs hK hconv hu hv hus hvs hε

/-- **Corollary 35.7.1**, first assertion: for each `u′`, `K′(u, v; u′, 0)` is lower
semicontinuous in `(u, v)` on `C × D`. It is Theorem 35.7 for the constant sequence. -/
theorem corollary_35_7_1_fst (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D) (hD : Convex ℝ D)
    (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D) (u' : Rn m) :
    LowerSemicontinuousAt (fun p : Rn m × Rn n => dirDerivReal (fun w => K (w, p.2)) p.1 u')
      (u, v) :=
  lowerSemicontinuousAt_dirDerivReal_fst hCo hC hDo hD hK hu hv u'

/-- **Corollary 35.7.1**, second assertion: for each `v′`, `K′(u, v; 0, v′)` is upper
semicontinuous in `(u, v)` on `C × D`. -/
theorem corollary_35_7_1_snd (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D) (hD : Convex ℝ D)
    (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D) (v' : Rn n) :
    UpperSemicontinuousAt (fun p : Rn m × Rn n => dirDerivReal (fun x => K (p.1, x)) p.2 v')
      (u, v) :=
  upperSemicontinuousAt_dirDerivReal_snd hCo hC hDo hD hK hu hv v'

/-- **Corollary 35.7.1**, third assertion: given `(u, v) ∈ C × D` and `ε > 0` there is a `δ > 0`
with `∂K (x, y) ⊆ ∂K (u, v) + εB` for every `(x, y)` within `δ` of `(u, v)`. -/
theorem corollary_35_7_1_subdiff (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D)
    (hD : Convex ℝ D) (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ p : Rn m × Rn n, dist p (u, v) < δ →
      saddleSubdifferentialOn C D K p ⊆ saddleSubdifferentialOn C D K (u, v)
        + Metric.closedBall (0 : Rn m × Rn n) ε := by
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.1
    (eventually_nhds_saddleSubdifferentialOn_subset hCo hC hDo hD hK hu hv hε)
  exact ⟨δ, hδ, fun p hp => h hp⟩

end Thm357

/-! ### Theorem 35.8 and Corollary 35.8.1 -/

section Thm358

variable {m n : ℕ} {C : Set (Rn m)} {D : Set (Rn n)} {K : Rn m × Rn n → ℝ} {u : Rn m} {v : Rn n}
  {q : Rn m × Rn n}

/-- **Theorem 35.8**, first half: if `K` is differentiable at `(u, v)` then `∇K (u, v)` is its
unique subgradient there. `HasSaddleGradientAt K q p` reads `∇K p = q` with `q` a *pair* of
vectors, a product of inner-product spaces carrying the supremum norm in Mathlib. -/
theorem theorem_35_8_gradient (hCo : IsOpen C) (_hC : Convex ℝ C) (hDo : IsOpen D)
    (_hD : Convex ℝ D) (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D)
    (hd : HasSaddleGradientAt K q (u, v)) : saddleSubdifferentialOn C D K (u, v) = {q} :=
  saddleSubdifferentialOn_eq_singleton_of_hasSaddleGradientAt hCo hDo hK hu hv hd

/-- **Theorem 35.8**: `K` is differentiable at `(u, v)` if and only if it has a unique subgradient
there. The converse is proved from Corollary 35.7.1, which gives the Fréchet estimate directly. -/
theorem theorem_35_8 (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D) (hD : Convex ℝ D)
    (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D) :
    DifferentiableAt ℝ K (u, v) ↔ ∃ q, saddleSubdifferentialOn C D K (u, v) = {q} :=
  differentiableAt_iff_exists_saddleSubdifferentialOn_eq_singleton hCo hC hDo hD hK hu hv

/-- **Corollary 35.8.1**: for `K` concave-convex and finite on a neighbourhood of `(u, v)`,
differentiability there is exactly linearity of `K′(u, v; ·, ·)`. The corollary's last clause —
that finiteness of the `m + n` two-sided partial derivatives suffices — is not formalized. -/
theorem corollary_35_8_1 (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D) (hD : Convex ℝ D)
    (hK : ConcaveConvexOn C D K) (hu : u ∈ C) (hv : v ∈ D) :
    DifferentiableAt ℝ K (u, v) ↔ IsLinearMap ℝ (dirDerivReal K (u, v)) :=
  differentiableAt_iff_isLinearMap_dirDerivReal hCo hC hDo hD hK hu hv

end Thm358

/-! ### Theorems 35.9 and 35.10 -/

section Rademacher

variable {m n : ℕ} {C : Set (Rn m)} {D : Set (Rn n)} {K : Rn m × Rn n → ℝ}

/-- **Theorem 35.9**, measure clause: the set where a finite concave-convex `K` fails to be
differentiable on `C × D` is null. Proved from Theorem 35.1 plus Rademacher, as §25 does. -/
theorem theorem_35_9_measure (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D) (hD : Convex ℝ D)
    (hK : ConcaveConvexOn C D K) :
    volume ((C ×ˢ D) \ {p : Rn m × Rn n | DifferentiableAt ℝ K p}) = 0 := by
  have : (volume : Measure (Rn m × Rn n)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure volume volume
  exact measure_diff_differentiableAt_of_concaveConvexOn hCo hC hDo hD hK

/-- **Theorem 35.9**, density clause: the set of points of `C × D` at which `K` is differentiable
is dense in `C × D`. -/
theorem theorem_35_9_dense (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D) (hD : Convex ℝ D)
    (hK : ConcaveConvexOn C D K) : C ×ˢ D ⊆ closure {p : Rn m × Rn n | DifferentiableAt ℝ K p} :=
  subset_closure_differentiableAt_of_concaveConvexOn hCo hC hDo hD hK

/-- **Theorem 35.9**, continuity clause: the gradient mapping is continuous on the set where it
exists. There is no canonical `∇K` without choice, so the statement takes any `G` representing it
on `S`; `prodInnerL` is injective, so `G` is unique there, and `S = E` gives the book. -/
theorem theorem_35_9_continuousOn (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D)
    (hD : Convex ℝ D) (hK : ConcaveConvexOn C D K) {S : Set (Rn m × Rn n)} (hS : S ⊆ C ×ˢ D)
    {G : Rn m × Rn n → Rn m × Rn n} (hG : ∀ p ∈ S, HasSaddleGradientAt K (G p) p) :
    ContinuousOn G S :=
  continuousOn_saddleGradient hCo hC hDo hD hK hS hG

/-- **Theorem 35.10**: if finite differentiable concave-convex `K i` converge pointwise on an open
convex `C × D` to a finite differentiable concave-convex `K`, then `∇K i (u, v) → ∇K (u, v)`.
Differentiability is needed only at the point in question, not everywhere as the book assumes. -/
theorem theorem_35_10 (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D) (hD : Convex ℝ D)
    {Ks : ℕ → Rn m × Rn n → ℝ} (hKs : ∀ i, ConcaveConvexOn C D (Ks i))
    (hK : ConcaveConvexOn C D K)
    (hconv : ∀ p ∈ C ×ˢ D, Tendsto (fun i => Ks i p) atTop (𝓝 (K p))) {p : Rn m × Rn n}
    (hp : p ∈ C ×ˢ D) {G : ℕ → Rn m × Rn n} {G' : Rn m × Rn n}
    (hG : ∀ i, HasSaddleGradientAt (Ks i) (G i) p) (hG' : HasSaddleGradientAt K G' p) :
    Tendsto G atTop (𝓝 G') :=
  tendsto_of_hasSaddleGradientAt hCo hC hDo hD hKs hK hconv hp hG hG'

/-- **Theorem 35.10**, last sentence: the gradient mappings converge uniformly on every closed
bounded subset of `C × D`. -/
theorem theorem_35_10_uniform (hCo : IsOpen C) (hC : Convex ℝ C) (hDo : IsOpen D) (hD : Convex ℝ D)
    {Ks : ℕ → Rn m × Rn n → ℝ} (hKs : ∀ i, ConcaveConvexOn C D (Ks i))
    (hK : ConcaveConvexOn C D K)
    (hconv : ∀ p ∈ C ×ˢ D, Tendsto (fun i => Ks i p) atTop (𝓝 (K p)))
    {Gs : ℕ → Rn m × Rn n → Rn m × Rn n} {G : Rn m × Rn n → Rn m × Rn n}
    (hGs : ∀ i, ∀ p ∈ C ×ˢ D, HasSaddleGradientAt (Ks i) (Gs i p) p)
    (hG : ∀ p ∈ C ×ˢ D, HasSaddleGradientAt K (G p) p) {E : Set (Rn m × Rn n)}
    (hEcl : IsClosed E) (hEb : Bornology.IsBounded E) (hEsub : E ⊆ C ×ˢ D) :
    TendstoUniformlyOn Gs G atTop E :=
  tendstoUniformlyOn_saddleGradient hCo hC hDo hD hKs hK hconv hGs hG
    (Metric.isCompact_of_isClosed_isBounded hEcl hEb) hEsub

end Rademacher

end Rockafellar

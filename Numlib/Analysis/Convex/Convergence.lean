import Numlib.Analysis.Convex.Continuity

/-!
# Equi-Lipschitz families and convergence of convex functions

Four theorems about families of convex functions on a relatively open convex set. A pointwise
bounded family is uniformly bounded and equi-Lipschitzian on compact subsets; a function convex in
`x` and continuous in `t` is jointly continuous; pointwise convergence on a dense subset propagates
and becomes uniform on compact subsets; and a bounded sequence has a subsequence converging
uniformly on compact subsets.

Each theorem appears twice: an `interior` form, on an **open** convex set, which carries the whole
argument, and a `_relint` form, on `ri C` for an arbitrary convex `C`, obtained from it through the
linear chart of `Continuity.lean`. The hypotheses are the weakened pair throughout: a subset `C'`
with `ri C ⊆ cl C'` on which the family is pointwise bounded above, plus a single point of `ri C`
at which it is bounded below. Taking `C' = ri C` recovers the headline statements, and the two
convergence theorems *need* the weakened form, their own hypotheses being about a dense subset.

## Main results

* `exists_forall_abs_le_of_isCompact`, `exists_forall_lipschitzOnWith_of_isCompact` and their
  `_relint` twins — uniform boundedness and equi-Lipschitz continuity, with
  `exists_forall_abs_le_and_lipschitzOnWith_of_isCompact_relint` as the headline form for a
  pointwise bounded family. The uniform bound splits into `exists_forall_le_of_isCompact` and
  `exists_forall_ge_of_isBounded`, and `bddAbove_range_of_subset_convexHull_closure` is the step
  that spreads pointwise boundedness off a dense subset.
* `continuousOn_prod_of_convexOn`, `continuousOn_prod_of_convexOn_relint` — joint continuity, for
  an arbitrary locally compact `T`.
* `exists_tendstoUniformlyOn_of_dense`, `exists_tendstoUniformlyOn_of_dense_relint` — convergence
  from a dense subset, with `tendstoUniformlyOn_of_tendsto`(`_relint`) for the case where the limit
  is already known and `eventually_forall_le_add_of_eventually_le`(`_relint`) for the eventual
  upper bound. `uniformCauchySeqOn_of_dense` is the analytic core.
* `exists_subseq_tendstoUniformlyOn`, `exists_subseq_tendstoUniformlyOn_relint` — a uniformly
  convergent subsequence.
* `convexOn_ciSup` — a finite pointwise supremum of convex functions is convex.
* `convexOn_chart`, `mem_relint_of_mem_interior_chart`, `mem_interior_chart_of_mem_relint`,
  `chart_subset_interior_chart`, `interior_chart_subset_closure_chart` — the chart bookkeeping.

## Implementation notes

The functions are real-valued rather than `EReal`-valued: these theorems are about families
*finite* on a relatively open convex set, and every conclusion — a supremum, a Lipschitz constant,
a uniform bound, a limit — is a statement about real numbers. So the family is `f : ι → E → ℝ` with
`∀ i, ConvexOn ℝ C (f i)`, which composes directly with Mathlib; a caller holding an
`EReal`-valued `ConvexFn` converts with `ConvexFn.convexOn_toReal_dom`. The upper-bound hypothesis
actually needs only `C ⊆ conv (cl C')`, which is what
`bddAbove_range_of_subset_convexHull_closure` proves; the theorems are stated with `cl C'` because
the step from a bound to *uniform* convergence needs points of `C'` metrically near `S`, which a
convex hull does not supply. The subsequence theorem avoids a diagonal argument: the values on a
countable
dense subset live in a compact box in `ℕ → ℝ`, compact by Tychonoff and sequentially compact
because `ℕ → ℝ` is first countable.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §10.
-/
open Set Filter Topology Metric
open scoped NNReal Pointwise

namespace ConvexAnalysis

section OpenConvex

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {ι : Type*} {U : Set W} {f : ι → W → ℝ}

omit [FiniteDimensional ℝ W] in
/-- The pointwise supremum of a family of functions convex on `U` is convex on `U`, provided the
supremum is finite at every point of `U`. -/
theorem convexOn_ciSup [Nonempty ι] (hUc : Convex ℝ U) (hf : ∀ i, ConvexOn ℝ U (f i))
    (hbdd : ∀ x ∈ U, BddAbove (Set.range fun i => f i x)) :
    ConvexOn ℝ U fun x => ⨆ i, f i x := by
  refine ⟨hUc, fun x hx y hy a b ha hb hab => ?_⟩
  refine ciSup_le fun i => ((hf i).2 hx hy ha hb hab).trans ?_
  gcongr
  · exact le_ciSup (hbdd x hx) i
  · exact le_ciSup (hbdd y hy) i

/-- **Pointwise boundedness spreads through a convex hull.** If a family of functions convex on an
open convex set `U` is pointwise bounded above on a subset `C'` of `U` with `U ⊆ conv (cl C')`,
then it is pointwise bounded above on all of `U`. This is the weakest form of the upper-bound
hypothesis: the set of points where the family is bounded above is convex, so its closure
contains `conv (cl C')`, and a convex set contains the interior of its own closure. -/
theorem bddAbove_range_of_subset_convexHull_closure (hU : IsOpen U) (hUc : Convex ℝ U)
    (hf : ∀ i, ConvexOn ℝ U (f i)) {C' : Set W} (hC' : C' ⊆ U)
    (hdense : U ⊆ convexHull ℝ (closure C'))
    (hbdd : ∀ x ∈ C', BddAbove (Set.range fun i => f i x)) :
    ∀ x ∈ U, BddAbove (Set.range fun i => f i x) := by
  set A : Set W := {x ∈ U | BddAbove (Set.range fun i => f i x)} with hAdef
  have hAconv : Convex ℝ A := by
    rintro x ⟨hxU, Mx, hMx⟩ y ⟨hyU, My, hMy⟩ a b ha hb hab
    refine ⟨hUc hxU hyU ha hb hab, a * Mx + b * My, ?_⟩
    rintro _ ⟨i, rfl⟩
    have h1 : f i x ≤ Mx := hMx ⟨i, rfl⟩
    have h2 : f i y ≤ My := hMy ⟨i, rfl⟩
    calc f i (a • x + b • y) ≤ a * f i x + b * f i y := (hf i).2 hxU hyU ha hb hab
      _ ≤ a * Mx + b * My := by gcongr
  have hUA : U ⊆ interior (closure A) :=
    interior_maximal (hdense.trans (convexHull_min
      (closure_mono fun x hx => ⟨hC' hx, hbdd x hx⟩) (Convex.closure hAconv))) hU
  intro x hx
  have hne : (interior (closure A)).Nonempty := ⟨x, hUA hx⟩
  have htop : affineSpan ℝ (closure A) = ⊤ :=
    top_unique <| (isOpen_interior.affineSpan_eq_top hne).ge.trans
      (affineSpan_mono ℝ interior_subset)
  have hri : ri (closure A) = interior (closure A) := intrinsicInterior_eq_interior htop
  have hxA : x ∈ A := by
    have : x ∈ ri (closure A) := hri ▸ hUA hx
    rw [Convex.relint_closure hAconv] at this
    exact intrinsicInterior_subset this
  exact hxA.2

/-- **Uniform boundedness from above**: a family of functions convex on an open convex set `U` and
pointwise bounded above there is *uniformly* bounded above on every compact subset of `U`. The
pointwise supremum is a finite convex function, hence continuous, hence bounded on compact
sets. -/
theorem exists_forall_le_of_isCompact (hU : IsOpen U) (hUc : Convex ℝ U)
    (hf : ∀ i, ConvexOn ℝ U (f i)) (hbdd : ∀ x ∈ U, BddAbove (Set.range fun i => f i x))
    {S : Set W} (hS : IsCompact S) (hSU : S ⊆ U) :
    ∃ M : ℝ, ∀ i, ∀ x ∈ S, f i x ≤ M := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨0, fun i => (hι.false i).elim⟩
  have hg : ConvexOn ℝ U fun x => ⨆ i, f i x := convexOn_ciSup hUc hf hbdd
  have hcont : ContinuousOn (fun x => ⨆ i, f i x) U := by
    have h := ConvexOn.continuousOn_interior hg
    rwa [hU.interior_eq] at h
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn (hcont.mono hSU)
  refine ⟨M, fun i x hx => (le_ciSup (hbdd x (hSU hx)) i).trans ?_⟩
  have h := hM x hx
  rw [Real.norm_eq_abs] at h
  exact (le_abs_self _).trans h

/-- **Uniform boundedness from below**: if a family of functions convex on an open convex set
`U` is pointwise bounded above on `U` and bounded *below* at a single point
`x₀`, it is uniformly bounded below on every bounded subset of `U`. For `x ∈ U` the point
`z = x₀ + (δ/‖x₀ - x‖) • (x₀ - x)` lies on the sphere of radius `δ` about `x₀`, and `x₀` is a
convex combination of `z` and `x`, which gives a bound depending on `x` only through
`‖x₀ - x‖`. -/
theorem exists_forall_ge_of_isBounded (hU : IsOpen U) (hUc : Convex ℝ U)
    (hf : ∀ i, ConvexOn ℝ U (f i)) (hbdd : ∀ x ∈ U, BddAbove (Set.range fun i => f i x))
    {x₀ : W} (hx₀ : x₀ ∈ U) (hbelow : BddBelow (Set.range fun i => f i x₀))
    {S : Set W} (hSb : Bornology.IsBounded S) (hSU : S ⊆ U) :
    ∃ m : ℝ, ∀ i, ∀ x ∈ S, m ≤ f i x := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨0, fun i => (hι.false i).elim⟩
  obtain ⟨δ, hδ, hballU⟩ : ∃ δ > 0, closedBall x₀ δ ⊆ U := by
    obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
    exact ⟨ε / 2, by linarith, (closedBall_subset_ball (by linarith)).trans hsub⟩
  obtain ⟨M, hM⟩ := exists_forall_le_of_isCompact hU hUc hf hbdd (isCompact_closedBall x₀ δ) hballU
  set β₂ : ℝ := max M 0 with hβ₂def
  have hβ₂0 : 0 ≤ β₂ := le_max_right _ _
  have hβ₂ : ∀ i, ∀ z ∈ closedBall x₀ δ, f i z ≤ β₂ :=
    fun i z hz => (hM i z hz).trans (le_max_left _ _)
  obtain ⟨β₁, hβ₁⟩ := hbelow
  have hβ₁' : ∀ i, β₁ ≤ f i x₀ := fun i => hβ₁ ⟨i, rfl⟩
  have hle : β₁ - β₂ ≤ 0 := by
    obtain ⟨i⟩ := hι
    have h := (hβ₁' i).trans (hβ₂ i x₀ (mem_closedBall_self hδ.le))
    linarith
  obtain ⟨R₀, hR₀⟩ := hSb.subset_closedBall x₀
  set R : ℝ := max R₀ 0 with hRdef
  have hRnn : 0 ≤ R := le_max_right _ _
  have hRS : ∀ x ∈ S, ‖x₀ - x‖ ≤ R := by
    intro x hx
    have h := hR₀ hx
    rw [mem_closedBall, dist_comm, dist_eq_norm] at h
    exact h.trans (le_max_left _ _)
  refine ⟨(δ + R) * (β₁ - β₂) / δ, fun i x hx => ?_⟩
  have hbig : (δ + R) * (β₁ - β₂) / δ ≤ β₁ - β₂ := by
    rw [div_le_iff₀ hδ]
    nlinarith
  rcases eq_or_ne x x₀ with rfl | hne
  · linarith [hβ₁' i]
  have ht : 0 < ‖x₀ - x‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hne))
  set t : ℝ := ‖x₀ - x‖ with htdef
  have hδt : (0 : ℝ) < δ + t := by positivity
  have hzdist : dist (x₀ + (δ / t) • (x₀ - x)) x₀ = δ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < δ / t), ← htdef]
    field_simp
  have hzU : x₀ + (δ / t) • (x₀ - x) ∈ U := hballU (by rw [mem_closedBall, hzdist])
  have hlam0 : (0 : ℝ) ≤ δ / (δ + t) := by positivity
  have hlam1 : δ / (δ + t) ≤ 1 := by rw [div_le_one hδt]; linarith
  have hcombo : (1 - δ / (δ + t)) • (x₀ + (δ / t) • (x₀ - x)) + (δ / (δ + t)) • x = x₀ := by
    match_scalars <;> field_simp <;> ring
  have hconv := (hf i).2 hzU (hSU hx) (by linarith : (0 : ℝ) ≤ 1 - δ / (δ + t)) hlam0 (by ring)
  rw [hcombo] at hconv
  simp only [smul_eq_mul] at hconv
  have hzb : f i (x₀ + (δ / t) • (x₀ - x)) ≤ β₂ :=
    hβ₂ i _ (by rw [mem_closedBall, hzdist])
  have hstep : β₁ - β₂ ≤ (δ / (δ + t)) * f i x := by
    have h1 : (1 - δ / (δ + t)) * f i (x₀ + (δ / t) • (x₀ - x)) ≤ β₂ := by
      nlinarith
    linarith [hβ₁' i]
  have hlampos : (0 : ℝ) < δ / (δ + t) := by positivity
  have hfx : (δ + t) * (β₁ - β₂) / δ ≤ f i x := by
    have h2 : (δ + t) * (β₁ - β₂) ≤ (δ + t) * (δ / (δ + t) * f i x) :=
      mul_le_mul_of_nonneg_left hstep hδt.le
    have h3 : (δ + t) * (δ / (δ + t) * f i x) = δ * f i x := by field_simp
    rw [h3] at h2
    rw [div_le_iff₀ hδ, mul_comm (f i x) δ]
    linarith
  refine le_trans ?_ hfx
  have h4 : (δ + R) * (β₁ - β₂) ≤ (δ + t) * (β₁ - β₂) := by nlinarith [hRS x hx]
  gcongr

/-! ### Pointwise boundedness in the `interior` form -/

/-- **The uniform boundedness half**, in the interior form: a family of functions convex on an
open convex set `U`, pointwise bounded above on a subset `C'` whose closure
contains `U` and bounded below at a single point of `U`, is uniformly bounded on every compact
subset of `U`. Taking `C' = U` recovers the headline statement. -/
theorem exists_forall_abs_le_of_isCompact (hU : IsOpen U) (hUc : Convex ℝ U)
    (hf : ∀ i, ConvexOn ℝ U (f i)) {C' : Set W} (hC' : C' ⊆ U) (hdense : U ⊆ closure C')
    (hab : ∀ x ∈ C', BddAbove (Set.range fun i => f i x))
    (hbe : ∃ x₀ ∈ U, BddBelow (Set.range fun i => f i x₀))
    {S : Set W} (hS : IsCompact S) (hSU : S ⊆ U) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i, ∀ x ∈ S, |f i x| ≤ M := by
  obtain ⟨x₀, hx₀, hbelow⟩ := hbe
  have habU : ∀ x ∈ U, BddAbove (Set.range fun i => f i x) :=
    bddAbove_range_of_subset_convexHull_closure hU hUc hf hC'
      (hdense.trans (subset_convexHull ℝ _)) hab
  obtain ⟨M₁, hM₁⟩ := exists_forall_le_of_isCompact hU hUc hf habU hS hSU
  obtain ⟨m, hm⟩ := exists_forall_ge_of_isBounded hU hUc hf habU hx₀ hbelow hS.isBounded hSU
  refine ⟨max |M₁| |m|, le_trans (abs_nonneg M₁) (le_max_left _ _), fun i x hx => abs_le.2 ⟨?_, ?_⟩⟩
  · have h1 : -|m| ≤ m := neg_abs_le m
    have h2 : -max |M₁| |m| ≤ -|m| := neg_le_neg (le_max_right _ _)
    linarith [hm i x hx]
  · exact (hM₁ i x hx).trans ((le_abs_self M₁).trans (le_max_left _ _))

/-- **The equi-Lipschitz half**, in the interior form: under the hypotheses of
`exists_forall_abs_le_of_isCompact` a single Lipschitz constant works for every member of the
family on every compact subset of `U`. One `ε`-collar and one bound `M` feed
`ConvexOn.lipschitzOnWith_of_abs_le_of_cthickening_subset`, whose constant `2M/ε` does not mention
the function. -/
theorem exists_forall_lipschitzOnWith_of_isCompact (hU : IsOpen U) (hUc : Convex ℝ U)
    (hf : ∀ i, ConvexOn ℝ U (f i)) {C' : Set W} (hC' : C' ⊆ U) (hdense : U ⊆ closure C')
    (hab : ∀ x ∈ C', BddAbove (Set.range fun i => f i x))
    (hbe : ∃ x₀ ∈ U, BddBelow (Set.range fun i => f i x₀))
    {S : Set W} (hS : IsCompact S) (hSU : S ⊆ U) :
    ∃ K : ℝ≥0, ∀ i, LipschitzOnWith K (f i) S := by
  obtain ⟨ε, hε, hsub⟩ := hS.exists_cthickening_subset_open hU hSU
  obtain ⟨M, hM0, hM⟩ := exists_forall_abs_le_of_isCompact hU hUc hf hC' hdense hab hbe
    (hS.cthickening (r := ε)) hsub
  exact ⟨_, fun i => ConvexOn.lipschitzOnWith_of_abs_le_of_cthickening_subset
    (hf i) hε hM0 hsub (hM i)⟩

end OpenConvex

/-! ### Convergence from a dense subset -/

section Sequence

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {U : Set W} {f : ℕ → W → ℝ}

/-- **The uniform Cauchy property.** A sequence of functions convex on an open convex set `U`
which is pointwise Cauchy on a subset `C'` whose closure contains `U` is *uniformly* Cauchy on
every compact subset of `U`. Given `ε`, equi-Lipschitz continuity supplies one Lipschitz constant
for the whole sequence on a compact collar of `S`, and finitely many points of `C'` then
suffice. -/
theorem uniformCauchySeqOn_of_dense (hU : IsOpen U) (hUc : Convex ℝ U)
    (hf : ∀ i, ConvexOn ℝ U (f i)) {C' : Set W} (hC' : C' ⊆ U) (hdense : U ⊆ closure C')
    (hab : ∀ x ∈ C', BddAbove (Set.range fun i => f i x))
    (hbe : ∃ x₀ ∈ U, BddBelow (Set.range fun i => f i x₀))
    (hcau : ∀ x ∈ C', CauchySeq fun i => f i x)
    {S : Set W} (hS : IsCompact S) (hSU : S ⊆ U) :
    UniformCauchySeqOn f atTop S := by
  classical
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  obtain ⟨ε₀, hε₀, hcoll⟩ := hS.exists_cthickening_subset_open hU hSU
  obtain ⟨K, hK⟩ := exists_forall_lipschitzOnWith_of_isCompact hU hUc hf hC' hdense hab hbe
    (hS.cthickening (r := ε₀)) hcoll
  have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
  set r : ℝ := min ε₀ (ε / (3 * ((K : ℝ) + 1))) with hrdef
  have hr : 0 < r := lt_min hε₀ (by positivity)
  have hKrlt : (K : ℝ) * r < ε / 3 := by
    have h1 : r ≤ ε / (3 * ((K : ℝ) + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 3 * ((K : ℝ) + 1))] at h1
    nlinarith [hr]
  have hcover : S ⊆ ⋃ z ∈ C' ∩ cthickening ε₀ S, ball z r := by
    intro x hx
    obtain ⟨z, hzC', hxz⟩ := Metric.mem_closure_iff.1 (hdense (hSU hx)) r hr
    refine mem_biUnion ⟨hzC', ?_⟩ (by rwa [mem_ball])
    exact Metric.mem_cthickening_of_dist_le z x ε₀ S hx
      (by rw [dist_comm]; exact hxz.le.trans (min_le_left _ _))
  obtain ⟨b, hbsub, hbfin, hbcover⟩ :=
    hS.elim_finite_subcover_image (fun z (_ : z ∈ C' ∩ cthickening ε₀ S) => isOpen_ball) hcover
  have hNex : ∀ z : W, ∃ N : ℕ, z ∈ b → ∀ m ≥ N, ∀ n ≥ N, dist (f m z) (f n z) < ε / 3 := by
    intro z
    by_cases hz : z ∈ b
    · obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 (hcau z (hbsub hz).1) (ε / 3) (by positivity)
      exact ⟨N, fun _ => hN⟩
    · exact ⟨0, fun h => absurd h hz⟩
  choose Nf hNf using hNex
  refine ⟨hbfin.toFinset.sup Nf, fun m hm n hn x hx => ?_⟩
  obtain ⟨z, hzb, hxz⟩ := mem_iUnion₂.1 (hbcover hx)
  have hNz : Nf z ≤ hbfin.toFinset.sup Nf := Finset.le_sup (hbfin.mem_toFinset.2 hzb)
  have hmid : dist (f m z) (f n z) < ε / 3 := hNf z hzb m (hNz.trans hm) n (hNz.trans hn)
  have hzS' : z ∈ cthickening ε₀ S := (hbsub hzb).2
  have hxS' : x ∈ cthickening ε₀ S := Metric.self_subset_cthickening S hx
  have hdxz : dist x z < r := by rwa [mem_ball] at hxz
  have hKd : (K : ℝ) * dist x z ≤ (K : ℝ) * r := by nlinarith [dist_nonneg (x := x) (y := z)]
  have hd1 : dist (f m x) (f m z) ≤ (K : ℝ) * dist x z := (hK m).dist_le_mul x hxS' z hzS'
  have hd2 : dist (f n x) (f n z) ≤ (K : ℝ) * dist x z := (hK n).dist_le_mul x hxS' z hzS'
  have htri := dist_triangle4 (f m x) (f m z) (f n z) (f n x)
  rw [dist_comm (f n z) (f n x)] at htri
  linarith

/-- **Convergence from a dense subset**, in the interior form: a sequence of functions convex on
an open convex set `U` which converges pointwise on a subset `C'` whose closure contains `U`
converges pointwise
on all of `U`, the limit is convex, and the convergence is uniform on every compact subset of `U`.

Taking `C' = U` gives the version in which convergence is assumed everywhere. -/
theorem exists_tendstoUniformlyOn_of_dense (hU : IsOpen U) (hUc : Convex ℝ U)
    (hf : ∀ i, ConvexOn ℝ U (f i)) {C' : Set W} (hC' : C' ⊆ U) (hdense : U ⊆ closure C')
    (hcv : ∀ x ∈ C', ∃ L : ℝ, Tendsto (fun i => f i x) atTop (𝓝 L)) :
    ∃ g : W → ℝ, ConvexOn ℝ U g ∧ (∀ x ∈ U, Tendsto (fun i => f i x) atTop (𝓝 (g x))) ∧
      ∀ ⦃S : Set W⦄, IsCompact S → S ⊆ U → TendstoUniformlyOn f g atTop S := by
  rcases U.eq_empty_or_nonempty with rfl | hUne
  · refine ⟨fun _ => 0, ⟨convex_empty, by simp⟩, by simp, fun S hS hSU => ?_⟩
    rw [subset_empty_iff] at hSU
    subst hSU
    exact fun u hu => Filter.Eventually.of_forall (by simp)
  obtain ⟨x₁, hx₁⟩ := hUne
  have hC'ne : C'.Nonempty := by
    rcases C'.eq_empty_or_nonempty with rfl | h
    · exact absurd (hdense hx₁) (by simp)
    · exact h
  have hcau : ∀ x ∈ C', CauchySeq fun i => f i x := fun x hx => (hcv x hx).choose_spec.cauchySeq
  have hab : ∀ x ∈ C', BddAbove (Set.range fun i => f i x) :=
    fun x hx => (hcv x hx).choose_spec.bddAbove_range
  obtain ⟨z₀, hz₀⟩ := hC'ne
  have hbe : ∃ x₀ ∈ U, BddBelow (Set.range fun i => f i x₀) :=
    ⟨z₀, hC' hz₀, (hcv z₀ hz₀).choose_spec.bddBelow_range⟩
  have key : ∀ S : Set W, IsCompact S → S ⊆ U → UniformCauchySeqOn f atTop S :=
    fun S hS hSU => uniformCauchySeqOn_of_dense hU hUc hf hC' hdense hab hbe hcau hS hSU
  have hcauU : ∀ x ∈ U, CauchySeq fun i => f i x := fun x hx =>
    (key {x} isCompact_singleton (singleton_subset_iff.2 hx)).cauchySeq rfl
  refine ⟨fun x => limUnder atTop fun i => f i x, ⟨hUc, fun x hx y hy a b ha hb hs => ?_⟩,
    fun x hx => (hcauU x hx).tendsto_limUnder, fun S hS hSU =>
      (key S hS hSU).tendstoUniformlyOn_of_tendsto fun x hx =>
        (hcauU x (hSU hx)).tendsto_limUnder⟩
  exact le_of_tendsto_of_tendsto' ((hcauU _ (hUc hx hy ha hb hs)).tendsto_limUnder)
    (((hcauU x hx).tendsto_limUnder.const_mul a).add
      ((hcauU y hy).tendsto_limUnder.const_mul b)) fun i => (hf i).2 hx hy ha hb hs

/-- The same with the limit function supplied: **pointwise convergence on all of an open convex
`U` upgrades to uniform convergence on compact subsets.** -/
theorem tendstoUniformlyOn_of_tendsto (hU : IsOpen U) (hUc : Convex ℝ U)
    (hf : ∀ i, ConvexOn ℝ U (f i)) {g : W → ℝ}
    (hg : ∀ x ∈ U, Tendsto (fun i => f i x) atTop (𝓝 (g x)))
    {S : Set W} (hS : IsCompact S) (hSU : S ⊆ U) : TendstoUniformlyOn f g atTop S := by
  obtain ⟨g', -, hg', huc⟩ := exists_tendstoUniformlyOn_of_dense hU hUc hf (subset_refl U)
    subset_closure fun x hx => ⟨g x, hg x hx⟩
  exact (huc hS hSU).congr_right fun x hx =>
    tendsto_nhds_unique (hg' x (hSU hx)) (hg x (hSU hx))

/-- **An eventual upper bound**, in the interior form: if a sequence of functions convex on an
open convex set `U` satisfies `limsup_i f i x ≤ g x` pointwise for a convex `g`, then on each
compact
`S ⊆ U` the bound `f i ≤ g + ε` holds for all large `i`. The `limsup` hypothesis is spelled as "for
every `ε > 0`, eventually `f i x ≤ g x + ε`", which avoids the junk values `Filter.limsup` takes on
unbounded sequences. -/
theorem eventually_forall_le_add_of_eventually_le (hU : IsOpen U) (hUc : Convex ℝ U)
    (hf : ∀ i, ConvexOn ℝ U (f i)) {g : W → ℝ} (hg : ConvexOn ℝ U g)
    (hle : ∀ x ∈ U, ∀ δ > 0, ∀ᶠ i in atTop, f i x ≤ g x + δ)
    {S : Set W} (hS : IsCompact S) (hSU : S ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∀ x ∈ S, f i x ≤ g x + ε := by
  have hmax : ∀ i, ConvexOn ℝ U fun x => f i x ⊔ g x := fun i => (hf i).sup hg
  have hcv : ∀ x ∈ U, Tendsto (fun i => f i x ⊔ g x) atTop (𝓝 (g x)) := by
    intro x hx
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hle x hx (δ / 2) (by positivity))
    refine ⟨N, fun n hn => ?_⟩
    have h1 : g x ≤ f n x ⊔ g x := le_max_right _ _
    have h2 : f n x ⊔ g x ≤ g x + δ / 2 := max_le (hN n hn) (by linarith)
    rw [Real.dist_eq, abs_of_nonneg (by linarith)]
    linarith
  have huc := tendstoUniformlyOn_of_tendsto hU hUc hmax hcv hS hSU
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 huc ε hε] with i hi x hx
  have h1 := hi x hx
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by simp)] at h1
  exact (le_max_left (f i x) (g x)).trans (by linarith)

/-- **Arzelà–Ascoli for convex functions**, in the interior form: a sequence of functions convex
on an open convex set `U` whose values are bounded at each point of a subset `C'` with `U ⊆ cl C'`
has a subsequence
converging, uniformly on every compact subset of `U`, to a finite convex function. -/
theorem exists_subseq_tendstoUniformlyOn (hU : IsOpen U) (hUc : Convex ℝ U)
    (hf : ∀ i, ConvexOn ℝ U (f i)) {C' : Set W} (hC' : C' ⊆ U) (hdense : U ⊆ closure C')
    (hbdd : ∀ x ∈ C', Bornology.IsBounded (Set.range fun i => f i x)) :
    ∃ (φ : ℕ → ℕ) (g : W → ℝ), StrictMono φ ∧ ConvexOn ℝ U g ∧
      (∀ x ∈ U, Tendsto (fun i => f (φ i) x) atTop (𝓝 (g x))) ∧
      ∀ ⦃S : Set W⦄, IsCompact S → S ⊆ U →
        TendstoUniformlyOn (fun i => f (φ i)) g atTop S := by
  obtain ⟨C'', hC''sub, hC''cnt, hC''dense⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace C').exists_countable_dense_subset
  have hdense'' : U ⊆ closure C'' :=
    hdense.trans (closure_minimal hC''dense isClosed_closure)
  rcases C''.eq_empty_or_nonempty with hempty | hne
  · have hUempty : U = ∅ := by
      rw [hempty, closure_empty] at hdense''
      exact subset_empty_iff.1 hdense''
    subst hUempty
    refine ⟨id, fun _ => 0, strictMono_id, ⟨convex_empty, by simp⟩, by simp, fun S hS hSU => ?_⟩
    rw [subset_empty_iff] at hSU
    subst hSU
    exact fun u hu => Filter.Eventually.of_forall (by simp)
  obtain ⟨e, he⟩ := hC''cnt.exists_eq_range hne
  have hmemC' : ∀ n, e n ∈ C' := fun n => hC''sub (he ▸ mem_range_self n)
  have hBex : ∀ n, ∃ B : ℝ, ∀ i, |f i (e n)| ≤ B := by
    intro n
    obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1 (hbdd (e n) (hmemC' n))
    exact ⟨B, fun i => by simpa [Real.norm_eq_abs] using hB _ (mem_range_self i)⟩
  choose B hB using hBex
  have hKcpt : IsCompact (Set.pi univ fun n => Icc (-(B n)) (B n)) :=
    isCompact_univ_pi fun n => isCompact_Icc
  have hmem : ∀ i, (fun n => f i (e n)) ∈ Set.pi univ fun n => Icc (-(B n)) (B n) :=
    fun i n _ => Set.mem_Icc.2 (abs_le.1 (hB n i))
  obtain ⟨u, -, φ, hφ, hlim⟩ := hKcpt.isSeqCompact hmem
  have hptw : ∀ n, Tendsto (fun i => f (φ i) (e n)) atTop (𝓝 (u n)) :=
    fun n => tendsto_pi_nhds.1 hlim n
  obtain ⟨g, hgconv, hgU, huc⟩ := exists_tendstoUniformlyOn_of_dense hU hUc
    (fun i => hf (φ i)) (hC''sub.trans hC') hdense'' fun x hx => by
      rw [he] at hx
      obtain ⟨n, rfl⟩ := hx
      exact ⟨u n, hptw n⟩
  exact ⟨φ, g, hφ, hgconv, hgU, huc⟩

end Sequence

/-! ### Joint continuity -/

section JointContinuity

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {U : Set W} {T : Type*} [TopologicalSpace T] [LocallyCompactSpace T]

/-- **Joint continuity**, in the interior form: a real-valued function on `U × T`, with `U` open
and convex and `T` locally compact, that is convex in its first argument and continuous in its
second is *jointly* continuous. Continuity in `t` is only needed at the points of a subset `C'` of
`U` whose closure contains `U`; taking `C' = U` gives the headline statement. -/
theorem continuousOn_prod_of_convexOn (hU : IsOpen U) (hUc : Convex ℝ U) {F : W × T → ℝ}
    (hconv : ∀ t : T, ConvexOn ℝ U fun x => F (x, t))
    {C' : Set W} (hC' : C' ⊆ U) (hdense : U ⊆ closure C')
    (hcont : ∀ x ∈ C', Continuous fun t => F (x, t)) :
    ContinuousOn F (U ×ˢ (univ : Set T)) := by
  refine continuousOn_of_forall_continuousAt ?_
  rintro ⟨x₀, t₀⟩ ⟨hx₀, -⟩
  obtain ⟨T₀, hT₀c, hT₀n⟩ := exists_compact_mem_nhds t₀
  have ht₀T₀ : t₀ ∈ T₀ := mem_of_mem_nhds hT₀n
  -- the family indexed by `T₀`
  set G : T₀ → W → ℝ := fun t x => F (x, (t : T)) with hGdef
  have hGconv : ∀ t : T₀, ConvexOn ℝ U (G t) := fun t => hconv (t : T)
  have hbound : ∀ x ∈ C', ∃ M : ℝ, ∀ t : T₀, |G t x| ≤ M := by
    intro x hx
    obtain ⟨M, hM⟩ := hT₀c.exists_bound_of_continuousOn (hcont x hx).continuousOn
    exact ⟨M, fun t => by simpa [G, Real.norm_eq_abs] using hM (t : T) t.2⟩
  have hab : ∀ x ∈ C', BddAbove (Set.range fun t : T₀ => G t x) := by
    intro x hx
    obtain ⟨M, hM⟩ := hbound x hx
    exact ⟨M, by rintro _ ⟨t, rfl⟩; exact (le_abs_self _).trans (hM t)⟩
  obtain ⟨x₁', hx₁'⟩ : C'.Nonempty := by
    rcases C'.eq_empty_or_nonempty with rfl | h
    · exact absurd (hdense hx₀) (by simp)
    · exact h
  have hbe : ∃ z ∈ U, BddBelow (Set.range fun t : T₀ => G t z) := by
    obtain ⟨M, hM⟩ := hbound x₁' hx₁'
    exact ⟨x₁', hC' hx₁', -M, by rintro _ ⟨t, rfl⟩; linarith [neg_abs_le (G t x₁'), hM t]⟩
  -- a compact ball around `x₀` inside `U`, and a common Lipschitz constant on it
  obtain ⟨δ, hδ, hballU⟩ : ∃ δ > 0, closedBall x₀ δ ⊆ U := by
    obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
    exact ⟨ε / 2, by linarith, (closedBall_subset_ball (by linarith)).trans hsub⟩
  obtain ⟨K, hK⟩ := exists_forall_lipschitzOnWith_of_isCompact hU hUc hGconv hC' hdense hab hbe
    (isCompact_closedBall x₀ δ) hballU
  have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
  rw [ContinuousAt, nhds_prod_eq, Metric.tendsto_nhds]
  intro ε hε
  set δ' : ℝ := min δ (ε / (4 * ((K : ℝ) + 1))) with hδ'def
  have hδ' : 0 < δ' := lt_min hδ (by positivity)
  have hKδ' : (K : ℝ) * δ' < ε / 4 := by
    have h1 : δ' ≤ ε / (4 * ((K : ℝ) + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * ((K : ℝ) + 1))] at h1
    nlinarith [hδ']
  obtain ⟨x₁, hx₁C', hx₁d⟩ := Metric.mem_closure_iff.1 (hdense hx₀) δ' hδ'
  have hx₁ball : x₁ ∈ closedBall x₀ δ :=
    mem_closedBall.2 ((dist_comm x₀ x₁ ▸ hx₁d).le.trans (min_le_left _ _))
  have hx₀ball : x₀ ∈ closedBall x₀ δ := mem_closedBall_self hδ.le
  have hlipx₁ : ∀ t : T₀, dist (G t x₁) (G t x₀) < ε / 4 := by
    intro t
    have h := (hK t).dist_le_mul x₁ hx₁ball x₀ hx₀ball
    have h2 : (K : ℝ) * dist x₁ x₀ ≤ (K : ℝ) * δ' := by
      nlinarith [dist_nonneg (x := x₁) (y := x₀), (dist_comm x₀ x₁ ▸ hx₁d).le]
    linarith
  rw [Filter.eventually_prod_iff]
  refine ⟨fun x => dist x x₀ < δ', Metric.eventually_nhds_iff.2 ⟨δ', hδ', fun {y} hy => hy⟩,
    fun t => t ∈ T₀ ∧ dist (F (x₁, t)) (F (x₁, t₀)) < ε / 4, ?_, ?_⟩
  · filter_upwards [hT₀n, Metric.tendsto_nhds.1 ((hcont x₁ hx₁C').continuousAt) (ε / 4)
      (by positivity)] with t h1 h2 using ⟨h1, h2⟩
  · rintro x hxd t ⟨htT₀, htd⟩
    have hxball : x ∈ closedBall x₀ δ := mem_closedBall.2 (hxd.le.trans (min_le_left _ _))
    have h1 : dist (F (x, t)) (F (x₀, t)) < ε / 4 := by
      have h := (hK ⟨t, htT₀⟩).dist_le_mul x hxball x₀ hx₀ball
      have h2 : (K : ℝ) * dist x x₀ ≤ (K : ℝ) * δ' := by
        nlinarith [dist_nonneg (x := x) (y := x₀)]
      exact lt_of_le_of_lt (h.trans h2) hKδ'
    have h2 : dist (F (x₀, t)) (F (x₁, t)) < ε / 4 := by
      rw [dist_comm]; exact hlipx₁ ⟨t, htT₀⟩
    have h4 : dist (F (x₁, t₀)) (F (x₀, t₀)) < ε / 4 := hlipx₁ ⟨t₀, ht₀T₀⟩
    have htri := dist_triangle4 (F (x, t)) (F (x₀, t)) (F (x₁, t)) (F (x₀, t₀))
    have htri' := dist_triangle (F (x₁, t)) (F (x₁, t₀)) (F (x₀, t₀))
    linarith

end JointContinuity

/-! ### The chart: from `interior` to `ri`

Every statement above is transported to the relative interior by the linear chart of
`Continuity.lean`: `exists_chart_retraction` produces a subspace `V`, a continuous linear
retraction `r : E →L[ℝ] V`, and the identity `ri C = x₀ + ι (int (chart C x₀ V))`. The three
lemmas here are the bookkeeping that identity buys. -/

section Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {C C' : Set E} {x₀ : E} {V : Submodule ℝ E}

omit [FiniteDimensional ℝ E] in
/-- A function convex on `C` is convex on the chart of `C` at `x₀`. -/
theorem convexOn_chart {ψ : E → ℝ} (hψ : ConvexOn ℝ C ψ) :
    ConvexOn ℝ (chart C x₀ V) fun z : V => ψ (x₀ + (z : E)) := by
  have hshift : (AffineMap.const ℝ V x₀ + V.subtype.toAffineMap) ⁻¹' C = chart C x₀ V := rfl
  exact hshift ▸ hψ.comp_affineMap (AffineMap.const ℝ V x₀ + V.subtype.toAffineMap)

omit [FiniteDimensional ℝ E] in
/-- Points of the interior of the chart come from points of `ri C`. -/
theorem mem_relint_of_mem_interior_chart
    (himg : ri C = x₀ +ᵥ (V.subtype '' interior (chart C x₀ V))) {z : V}
    (hz : z ∈ interior (chart C x₀ V)) : x₀ + (z : E) ∈ ri C := by
  rw [himg]
  exact ⟨(z : E), ⟨z, hz, rfl⟩, rfl⟩

omit [FiniteDimensional ℝ E] in
/-- Points of `ri C` come from points of the interior of the chart. -/
theorem mem_interior_chart_of_mem_relint
    (himg : ri C = x₀ +ᵥ (V.subtype '' interior (chart C x₀ V))) {x : E} (hx : x ∈ ri C) :
    ∃ z ∈ interior (chart C x₀ V), x₀ + (z : E) = x := by
  rw [himg] at hx
  obtain ⟨w, ⟨z, hz, rfl⟩, rfl⟩ := hx
  exact ⟨z, hz, rfl⟩

omit [FiniteDimensional ℝ E] in
/-- A subset of `ri C` charts inside the interior of the chart. -/
theorem chart_subset_interior_chart
    (himg : ri C = x₀ +ᵥ (V.subtype '' interior (chart C x₀ V))) (hC' : C' ⊆ ri C) :
    chart C' x₀ V ⊆ interior (chart C x₀ V) := by
  intro z hz
  obtain ⟨w, hw, hwe⟩ := mem_interior_chart_of_mem_relint himg (hC' hz)
  have hzw : w = z := Subtype.ext (add_left_cancel hwe)
  exact hzw ▸ hw

omit [FiniteDimensional ℝ E] in
/-- Density transports to the chart: if `C'` is dense in `ri C`, its chart is dense in the interior
of the chart of `C`. -/
theorem interior_chart_subset_closure_chart
    (himg : ri C = x₀ +ᵥ (V.subtype '' interior (chart C x₀ V))) (hC' : C' ⊆ ri C)
    (hdense : ri C ⊆ closure C') :
    interior (chart C x₀ V) ⊆ closure (chart C' x₀ V) := by
  intro z hz
  refine Metric.mem_closure_iff.2 fun ε hε => ?_
  obtain ⟨x, hxC', hdist⟩ :=
    Metric.mem_closure_iff.1 (hdense (mem_relint_of_mem_interior_chart himg hz)) ε hε
  obtain ⟨w, -, hw⟩ := mem_interior_chart_of_mem_relint himg (hC' hxC')
  refine ⟨w, show x₀ + (w : E) ∈ C' from hw ▸ hxC', ?_⟩
  rw [Subtype.dist_eq, ← dist_add_left x₀ (z : E) (w : E), hw]
  exact hdist

end Chart

/-! ### Pointwise boundedness in the `ri` form -/

section Relint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} {C C' : Set E} {f : ι → E → ℝ}

/-- **The uniform boundedness half**: a family of functions convex on a convex set `C`, pointwise
bounded above on a subset `C'` of `ri C` whose closure contains `ri C` and bounded below at one
point of `ri C`, is uniformly bounded on every compact subset of `ri C`. Taking `C' = ri C` gives
the usual hypothesis, for a relatively open `C`. -/
theorem exists_forall_abs_le_of_isCompact_relint (hC : Convex ℝ C)
    (hf : ∀ i, ConvexOn ℝ C (f i)) (hC' : C' ⊆ ri C) (hdense : ri C ⊆ closure C')
    (hab : ∀ x ∈ C', BddAbove (Set.range fun i => f i x))
    (hbe : ∃ z ∈ ri C, BddBelow (Set.range fun i => f i z))
    {S : Set E} (hS : IsCompact S) (hSC : S ⊆ ri C) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i, ∀ x ∈ S, |f i x| ≤ M := by
  rcases (ri C).eq_empty_or_nonempty with hri | ⟨x₀, hx₀⟩
  · exact ⟨0, le_rfl, fun i x hx => absurd (hSC hx) (by rw [hri]; simp)⟩
  obtain ⟨V, r, himg, hmaps, hid⟩ := exists_chart_retraction hC (intrinsicInterior_subset hx₀)
  have hDconv : Convex ℝ (interior (chart C x₀ V)) := Convex.interior (convex_chart hC)
  have hgconv : ∀ i, ConvexOn ℝ (interior (chart C x₀ V)) fun z : V => f i (x₀ + (z : E)) :=
    fun i => (convexOn_chart (hf i)).subset interior_subset hDconv
  obtain ⟨z₀, hz₀ri, hz₀bd⟩ := hbe
  obtain ⟨w₀, hw₀, hw₀e⟩ := mem_interior_chart_of_mem_relint himg hz₀ri
  have hρ : Continuous fun x : E => r (x - x₀) :=
    r.continuous.comp (continuous_id.sub continuous_const)
  obtain ⟨M, hM0, hM⟩ := exists_forall_abs_le_of_isCompact isOpen_interior hDconv hgconv
    (chart_subset_interior_chart himg hC') (interior_chart_subset_closure_chart himg hC' hdense)
    (fun z hz => hab _ hz) ⟨w₀, hw₀, by rw [hw₀e]; exact hz₀bd⟩
    (hS.image hρ) (by rintro _ ⟨x, hx, rfl⟩; exact hmaps (hSC hx))
  refine ⟨M, hM0, fun i x hx => ?_⟩
  have h := hM i _ (Set.mem_image_of_mem (fun x : E => r (x - x₀)) hx)
  rwa [hid x (hSC hx)] at h

/-- **The equi-Lipschitz half**: under the hypotheses of
`exists_forall_abs_le_of_isCompact_relint` a *single* Lipschitz constant serves the whole family on
any compact subset of `ri C`. -/
theorem exists_forall_lipschitzOnWith_of_isCompact_relint (hC : Convex ℝ C)
    (hf : ∀ i, ConvexOn ℝ C (f i)) (hC' : C' ⊆ ri C) (hdense : ri C ⊆ closure C')
    (hab : ∀ x ∈ C', BddAbove (Set.range fun i => f i x))
    (hbe : ∃ z ∈ ri C, BddBelow (Set.range fun i => f i z))
    {S : Set E} (hS : IsCompact S) (hSC : S ⊆ ri C) :
    ∃ K : ℝ≥0, ∀ i, LipschitzOnWith K (f i) S := by
  rcases (ri C).eq_empty_or_nonempty with hri | ⟨x₀, hx₀⟩
  · rw [hri, subset_empty_iff] at hSC
    subst hSC
    exact ⟨0, fun i => by intro x hx; exact absurd hx (notMem_empty x)⟩
  obtain ⟨V, r, himg, hmaps, hid⟩ := exists_chart_retraction hC (intrinsicInterior_subset hx₀)
  have hDconv : Convex ℝ (interior (chart C x₀ V)) := Convex.interior (convex_chart hC)
  have hgconv : ∀ i, ConvexOn ℝ (interior (chart C x₀ V)) fun z : V => f i (x₀ + (z : E)) :=
    fun i => (convexOn_chart (hf i)).subset interior_subset hDconv
  obtain ⟨z₀, hz₀ri, hz₀bd⟩ := hbe
  obtain ⟨w₀, hw₀, hw₀e⟩ := mem_interior_chart_of_mem_relint himg hz₀ri
  have hρ : Continuous fun x : E => r (x - x₀) :=
    r.continuous.comp (continuous_id.sub continuous_const)
  obtain ⟨K, hK⟩ := exists_forall_lipschitzOnWith_of_isCompact isOpen_interior hDconv hgconv
    (chart_subset_interior_chart himg hC') (interior_chart_subset_closure_chart himg hC' hdense)
    (fun z hz => hab _ hz) ⟨w₀, hw₀, by rw [hw₀e]; exact hz₀bd⟩
    (hS.image hρ) (by rintro _ ⟨x, hx, rfl⟩; exact hmaps (hSC hx))
  have hrlip : LipschitzWith ‖r‖₊ (fun x : E => r (x - x₀)) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have hsub : (r (x - x₀) : V) - r (y - x₀) = r (x - y) := by
      rw [← map_sub]; congr 1; abel
    rw [dist_eq_norm, hsub, dist_eq_norm, coe_nnnorm]
    exact r.le_opNorm _
  refine ⟨K * ‖r‖₊, fun i => LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
  have hcomp : LipschitzOnWith (K * ‖r‖₊)
      ((fun z : V => f i (x₀ + (z : E))) ∘ fun x : E => r (x - x₀)) S :=
    (hK i).comp hrlip.lipschitzOnWith fun x hx => Set.mem_image_of_mem _ hx
  have h := hcomp.dist_le_mul x hx y hy
  rwa [Function.comp_apply, Function.comp_apply, hid x (hSC hx), hid y (hSC hy)] at h

end Relint

/-! ### Convergence, in the `ri` form -/

section RelintSequence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {C C' : Set E} {f : ℕ → E → ℝ}

/-- **Convergence from a dense subset**: a sequence of functions convex on a convex set `C`
which
converges pointwise on a subset `C'` of `ri C` whose closure contains `ri C` converges pointwise on
all of `ri C`, to a finite convex limit, uniformly on every compact subset of `ri C`. -/
theorem exists_tendstoUniformlyOn_of_dense_relint (hC : Convex ℝ C)
    (hf : ∀ i, ConvexOn ℝ C (f i)) (hC' : C' ⊆ ri C) (hdense : ri C ⊆ closure C')
    (hcv : ∀ x ∈ C', ∃ L : ℝ, Tendsto (fun i => f i x) atTop (𝓝 L)) :
    ∃ g : E → ℝ, ConvexOn ℝ (ri C) g ∧
      (∀ x ∈ ri C, Tendsto (fun i => f i x) atTop (𝓝 (g x))) ∧
      ∀ ⦃S : Set E⦄, IsCompact S → S ⊆ ri C → TendstoUniformlyOn f g atTop S := by
  rcases (ri C).eq_empty_or_nonempty with hri | ⟨x₀, hx₀⟩
  · refine ⟨fun _ => 0, ?_, ?_, fun S hS hSC => ?_⟩
    · rw [hri]; exact ⟨convex_empty, by simp⟩
    · rw [hri]; simp
    · rw [hri, subset_empty_iff] at hSC
      subst hSC
      exact fun u hu => Filter.Eventually.of_forall (by simp)
  obtain ⟨V, r, himg, hmaps, hid⟩ := exists_chart_retraction hC (intrinsicInterior_subset hx₀)
  have hDconv : Convex ℝ (interior (chart C x₀ V)) := Convex.interior (convex_chart hC)
  have hgconv : ∀ i, ConvexOn ℝ (interior (chart C x₀ V)) fun z : V => f i (x₀ + (z : E)) :=
    fun i => (convexOn_chart (hf i)).subset interior_subset hDconv
  have hρ : Continuous fun x : E => r (x - x₀) :=
    r.continuous.comp (continuous_id.sub continuous_const)
  obtain ⟨G, -, hGtend, hGunif⟩ := exists_tendstoUniformlyOn_of_dense isOpen_interior hDconv hgconv
    (chart_subset_interior_chart himg hC') (interior_chart_subset_closure_chart himg hC' hdense)
    fun z hz => hcv _ hz
  have hgri : ∀ x ∈ ri C, Tendsto (fun i => f i x) atTop (𝓝 (G (r (x - x₀)))) := by
    intro x hx
    have h := hGtend (r (x - x₀)) (hmaps hx)
    rwa [hid x hx] at h
  refine ⟨fun x => G (r (x - x₀)), ⟨Convex.relint hC, fun x hx y hy a b ha hb hs => ?_⟩, hgri,
    fun S hS hSC => Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_⟩
  · exact le_of_tendsto_of_tendsto' (hgri _ (Convex.relint hC hx hy ha hb hs))
      (((hgri x hx).const_mul a).add ((hgri y hy).const_mul b))
      fun i => (ConvexOn.subset (hf i) intrinsicInterior_subset (Convex.relint hC)).2
        hx hy ha hb hs
  · filter_upwards [Metric.tendstoUniformlyOn_iff.1
      (hGunif (hS.image hρ) (by rintro _ ⟨x, hx, rfl⟩; exact hmaps (hSC hx))) ε hε] with i hi x hx
    have h := hi (r (x - x₀)) (Set.mem_image_of_mem _ hx)
    rwa [hid x (hSC hx)] at h

/-- The same with the limit supplied: **pointwise convergence on `ri C` upgrades to uniform
convergence on its compact subsets.** -/
theorem tendstoUniformlyOn_of_tendsto_relint (hC : Convex ℝ C) (hf : ∀ i, ConvexOn ℝ C (f i))
    {g : E → ℝ} (hg : ∀ x ∈ ri C, Tendsto (fun i => f i x) atTop (𝓝 (g x)))
    {S : Set E} (hS : IsCompact S) (hSC : S ⊆ ri C) : TendstoUniformlyOn f g atTop S := by
  obtain ⟨g', -, hg', huc⟩ := exists_tendstoUniformlyOn_of_dense_relint hC hf
    (subset_refl (ri C)) subset_closure fun x hx => ⟨g x, hg x hx⟩
  refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 (huc hS hSC) ε hε] with i hi x hx
  rw [tendsto_nhds_unique (hg x (hSC hx)) (hg' x (hSC hx))]
  exact hi x hx

/-- **An eventual upper bound**: if `limsup_i f i x ≤ g x` for every `x ∈ ri C`, with `g`
convex, then on each compact `S ⊆ ri C` the bound `f i ≤ g + ε` holds uniformly for large `i`.

The `limsup` hypothesis is spelled as "for every `δ > 0`, eventually `f i x ≤ g x + δ`". -/
theorem eventually_forall_le_add_of_eventually_le_relint (hC : Convex ℝ C)
    (hf : ∀ i, ConvexOn ℝ C (f i)) {g : E → ℝ} (hg : ConvexOn ℝ C g)
    (hle : ∀ x ∈ ri C, ∀ δ > 0, ∀ᶠ i in atTop, f i x ≤ g x + δ)
    {S : Set E} (hS : IsCompact S) (hSC : S ⊆ ri C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∀ x ∈ S, f i x ≤ g x + ε := by
  have hmax : ∀ i, ConvexOn ℝ C fun x => f i x ⊔ g x := fun i => (hf i).sup hg
  have hcv : ∀ x ∈ ri C, Tendsto (fun i => f i x ⊔ g x) atTop (𝓝 (g x)) := by
    intro x hx
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hle x hx (δ / 2) (by positivity))
    refine ⟨N, fun n hn => ?_⟩
    have h1 : g x ≤ f n x ⊔ g x := le_max_right _ _
    have h2 : f n x ⊔ g x ≤ g x + δ / 2 := max_le (hN n hn) (by linarith)
    rw [Real.dist_eq, abs_of_nonneg (by linarith)]
    linarith
  have huc := tendstoUniformlyOn_of_tendsto_relint hC hmax hcv hS hSC
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 huc ε hε] with i hi x hx
  have h1 := hi x hx
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by simp)] at h1
  exact (le_max_left (f i x) (g x)).trans (by linarith)

/-- **Arzelà–Ascoli for convex functions**: a sequence of functions convex on `C` whose values are
bounded
at each point of a subset `C'` of `ri C` with `ri C ⊆ cl C'` has a subsequence converging uniformly
on the compact subsets of `ri C` to a finite convex function. -/
theorem exists_subseq_tendstoUniformlyOn_relint (hC : Convex ℝ C)
    (hf : ∀ i, ConvexOn ℝ C (f i)) (hC' : C' ⊆ ri C) (hdense : ri C ⊆ closure C')
    (hbdd : ∀ x ∈ C', Bornology.IsBounded (Set.range fun i => f i x)) :
    ∃ (φ : ℕ → ℕ) (g : E → ℝ), StrictMono φ ∧ ConvexOn ℝ (ri C) g ∧
      (∀ x ∈ ri C, Tendsto (fun i => f (φ i) x) atTop (𝓝 (g x))) ∧
      ∀ ⦃S : Set E⦄, IsCompact S → S ⊆ ri C →
        TendstoUniformlyOn (fun i => f (φ i)) g atTop S := by
  rcases (ri C).eq_empty_or_nonempty with hri | ⟨x₀, hx₀⟩
  · refine ⟨id, fun _ => 0, strictMono_id, ?_, ?_, fun S hS hSC => ?_⟩
    · rw [hri]; exact ⟨convex_empty, by simp⟩
    · rw [hri]; simp
    · rw [hri, subset_empty_iff] at hSC
      subst hSC
      exact fun u hu => Filter.Eventually.of_forall (by simp)
  obtain ⟨V, r, himg, hmaps, hid⟩ := exists_chart_retraction hC (intrinsicInterior_subset hx₀)
  have hDconv : Convex ℝ (interior (chart C x₀ V)) := Convex.interior (convex_chart hC)
  have hgconv : ∀ i, ConvexOn ℝ (interior (chart C x₀ V)) fun z : V => f i (x₀ + (z : E)) :=
    fun i => (convexOn_chart (hf i)).subset interior_subset hDconv
  obtain ⟨φ, G, hφ, -, hGtend, -⟩ := exists_subseq_tendstoUniformlyOn isOpen_interior hDconv hgconv
    (chart_subset_interior_chart himg hC') (interior_chart_subset_closure_chart himg hC' hdense)
    fun z hz => hbdd _ hz
  have hcv : ∀ x ∈ C', ∃ L : ℝ, Tendsto (fun i => f (φ i) x) atTop (𝓝 L) := by
    intro x hx
    obtain ⟨z, hz, hze⟩ := mem_interior_chart_of_mem_relint himg (hC' hx)
    exact ⟨G z, by rw [← hze]; exact hGtend z hz⟩
  obtain ⟨g, hgc, hgt, hgu⟩ := exists_tendstoUniformlyOn_of_dense_relint hC
    (fun i => hf (φ i)) hC' hdense hcv
  exact ⟨φ, g, hφ, hgc, hgt, hgu⟩

end RelintSequence

/-! ### Joint continuity, in the `ri` form -/

section RelintJoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {C C' : Set E} {T : Type*} [TopologicalSpace T] [LocallyCompactSpace T]

/-- **Joint continuity**: a real-valued function on `ri C × T`, with `T` locally compact,
convex in its first argument and continuous in its second, is jointly continuous relative to
`ri C × T`. -/
theorem continuousOn_prod_of_convexOn_relint (hC : Convex ℝ C) {F : E × T → ℝ}
    (hconv : ∀ t : T, ConvexOn ℝ C fun x => F (x, t))
    (hC' : C' ⊆ ri C) (hdense : ri C ⊆ closure C')
    (hcont : ∀ x ∈ C', Continuous fun t => F (x, t)) :
    ContinuousOn F (ri C ×ˢ (univ : Set T)) := by
  rcases (ri C).eq_empty_or_nonempty with hri | ⟨x₀, hx₀⟩
  · rw [hri, Set.empty_prod]
    exact continuousOn_empty F
  obtain ⟨V, r, himg, hmaps, hid⟩ := exists_chart_retraction hC (intrinsicInterior_subset hx₀)
  have hDconv : Convex ℝ (interior (chart C x₀ V)) := Convex.interior (convex_chart hC)
  have hG := continuousOn_prod_of_convexOn (F := fun p : V × T => F (x₀ + (p.1 : E), p.2))
    isOpen_interior hDconv
    (fun t => (convexOn_chart (hconv t)).subset interior_subset hDconv)
    (chart_subset_interior_chart himg hC') (interior_chart_subset_closure_chart himg hC' hdense)
    (fun z hz => hcont _ hz)
  have hρ : Continuous fun p : E × T => ((r (p.1 - x₀) : V), p.2) :=
    (r.continuous.comp (continuous_fst.sub continuous_const)).prodMk continuous_snd
  refine ContinuousOn.congr (hG.comp hρ.continuousOn ?_) ?_
  · rintro ⟨x, t⟩ ⟨hx, -⟩
    exact ⟨hmaps hx, mem_univ t⟩
  · rintro ⟨x, t⟩ ⟨hx, -⟩
    exact (congrArg (fun y => F (y, t)) (hid x hx)).symm

end RelintJoint

/-! ### The headline form -/

section Headline

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} {C : Set E} {f : ι → E → ℝ}

/-- **A family of convex functions finite and *pointwise bounded* on `ri C` is uniformly bounded
and equi-Lipschitzian on every compact subset of `ri C`.** -/
theorem exists_forall_abs_le_and_lipschitzOnWith_of_isCompact_relint (hC : Convex ℝ C)
    (hf : ∀ i, ConvexOn ℝ C (f i))
    (hbdd : ∀ x ∈ ri C, Bornology.IsBounded (Set.range fun i => f i x))
    {S : Set E} (hS : IsCompact S) (hSC : S ⊆ ri C) :
    (∃ M : ℝ, 0 ≤ M ∧ ∀ i, ∀ x ∈ S, |f i x| ≤ M) ∧
      ∃ K : ℝ≥0, ∀ i, LipschitzOnWith K (f i) S := by
  rcases (ri C).eq_empty_or_nonempty with hri | ⟨z, hz⟩
  · rw [hri, subset_empty_iff] at hSC
    subst hSC
    exact ⟨⟨0, le_rfl, by simp⟩, 0, fun i => by intro x hx; exact absurd hx (notMem_empty x)⟩
  have hab : ∀ x ∈ ri C, BddAbove (Set.range fun i => f i x) :=
    fun x hx => (isBounded_iff_bddBelow_bddAbove.1 (hbdd x hx)).2
  have hbe : ∃ z ∈ ri C, BddBelow (Set.range fun i => f i z) :=
    ⟨z, hz, (isBounded_iff_bddBelow_bddAbove.1 (hbdd z hz)).1⟩
  exact ⟨exists_forall_abs_le_of_isCompact_relint hC hf (subset_refl _) subset_closure hab hbe
      hS hSC,
    exists_forall_lipschitzOnWith_of_isCompact_relint hC hf (subset_refl _) subset_closure hab hbe
      hS hSC⟩

end Headline







end ConvexAnalysis


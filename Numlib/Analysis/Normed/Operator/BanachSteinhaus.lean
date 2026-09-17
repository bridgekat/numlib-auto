/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Operator.BanachSteinhaus`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-!
# The convergence half of the Banach–Steinhaus theorem, and its corollaries

Mathlib's `banach_steinhaus` is the uniform boundedness principle: a pointwise bounded family of
operators out of a Banach space is bounded in norm. This file adds the companion that the
applications use, and which needs neither completeness nor a Baire argument, together with the
corollaries of the principle stated in [brezis2011functional] §2.2 that Mathlib does not state:
the lower semicontinuity of the operator norm under pointwise convergence, and the two
"weakly bounded implies bounded" statements.

## Main statements

* `ContinuousLinearMap.tendsto_of_tendsto_on_dense_of_bounded` — a uniformly bounded family that
  converges pointwise on a dense *set* to a bounded operator converges pointwise everywhere. This
  is the ε/3 argument, and it holds along an arbitrary filter on an arbitrary index type.
* `ContinuousLinearMap.tendsto_iff_tendsto_on_dense_of_completeSpace` — the two halves combined,
  as an `Iff` on a complete space: a sequence converges pointwise everywhere exactly when it
  converges on a dense set and is uniformly bounded. This is the criterion by which a family of
  quadrature rules, or of interpolation projections, is shown to converge on all of `C[a, b]`
  from its convergence on the polynomials.
* `ContinuousLinearMap.exists_not_tendsto_of_not_bddAbove` — the contrapositive of
  `banach_steinhaus`: unbounded operator norms produce a vector whose images do not converge.
  With the Lebesgue constants of the Fourier projections this is the existence of a continuous
  function whose Fourier series diverges.
* `ContinuousLinearMap.opNorm_le_liminf_opNorm_of_tendsto` — the operator norm is lower
  semicontinuous under pointwise convergence of a uniformly bounded sequence,
  `‖L‖ ≤ liminf ‖Lₙ‖` ([brezis2011functional], Corollary 2.3 (c)).
* `isBounded_of_forall_dual_image_isBounded`, `isBounded_iff_forall_dual_image_isBounded` — a
  set is bounded iff every bounded linear functional is bounded on it (Corollary 2.4, "weakly
  bounded implies bounded"), by the uniform boundedness principle in the (always complete) dual.
* `StrongDual.isBounded_of_forall_eval_isBounded` — a set of functionals on a Banach space that
  is bounded at every point is bounded in norm (Corollary 2.5, "weak-∗ bounded implies bounded").
-/

open Filter Topology Bornology Metric

namespace ContinuousLinearMap

variable {𝕜 V W : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- **The ε/3 argument.** A family of operators bounded uniformly in norm, converging pointwise
along a filter on a dense set to a bounded operator, converges pointwise everywhere.

Neither completeness of `V` nor linearity of the dense set is used, and the index type and the
filter are arbitrary; only the boundedness of the limit operator `L` matters, which is why `L` is
given as a `ContinuousLinearMap` rather than as a bare function. -/
theorem tendsto_of_tendsto_on_dense_of_bounded {ι : Type*} {l : Filter ι} {s : Set V}
    (hs : Dense s) {L : V →L[𝕜] W} {Ln : ι → V →L[𝕜] W} {C : ℝ} (hC : ∀ n, ‖Ln n‖ ≤ C)
    (h : ∀ v ∈ s, Tendsto (fun n => Ln n v) l (𝓝 (L v))) (v : V) :
    Tendsto (fun n => Ln n v) l (𝓝 (L v)) := by
  -- a bound on operator norms may be negative only over an empty index type; replace it
  set M : ℝ := max C 0
  have hM0 : 0 ≤ M := le_max_right _ _
  have hCM : ∀ n, ‖Ln n‖ ≤ M := fun n => (hC n).trans (le_max_left _ _)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hM : 0 < M + ‖L‖ + 1 := by positivity
  obtain ⟨u, hu, hdist⟩ := hs.exists_dist_lt v (ε := ε / (3 * (M + ‖L‖ + 1))) (by positivity)
  have hvu : ‖v - u‖ < ε / (3 * (M + ‖L‖ + 1)) := by rwa [← dist_eq_norm]
  have hsum : (M + ‖L‖) * ‖v - u‖ < ε / 3 := by
    have hle : (M + ‖L‖) * ‖v - u‖ ≤ (M + ‖L‖ + 1) * ‖v - u‖ := by
      nlinarith [norm_nonneg (v - u)]
    have hval : (M + ‖L‖ + 1) * (ε / (3 * (M + ‖L‖ + 1))) = ε / 3 := by field_simp
    nlinarith [mul_lt_mul_of_pos_left hvu hM]
  filter_upwards [Metric.tendsto_nhds.mp (h u hu) (ε / 3) (by positivity)] with n hn
  have h1 : ‖Ln n v - Ln n u‖ ≤ M * ‖v - u‖ := by
    rw [← map_sub]
    exact ((Ln n).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hCM n) (norm_nonneg _))
  have h2 : ‖L u - L v‖ ≤ ‖L‖ * ‖v - u‖ := by
    rw [← map_sub, ← norm_neg, ← map_neg, neg_sub]
    exact L.le_opNorm _
  have h3 : ‖Ln n u - L u‖ < ε / 3 := by rw [← dist_eq_norm]; exact hn
  have hsplit : ‖Ln n v - L v‖ ≤ ‖Ln n v - Ln n u‖ + ‖Ln n u - L u‖ + ‖L u - L v‖ := by
    have hrw : Ln n v - L v = Ln n v - Ln n u + (Ln n u - L u) + (L u - L v) := by abel
    rw [hrw]
    exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
  rw [dist_eq_norm]
  nlinarith

/-- A convergent sequence in a normed space has bounded norms. -/
private theorem exists_norm_le_of_tendsto {X : Type*} [NormedAddCommGroup X] {f : ℕ → X} {a : X}
    (h : Tendsto f atTop (𝓝 a)) : ∃ C : ℝ, ∀ n, ‖f n‖ ≤ C := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _ h)
  exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩

/-- **Banach–Steinhaus, the convergence form.** On a Banach space, a sequence of bounded operators
converges pointwise to a bounded operator `L` if and only if it converges pointwise on a dense set
and its norms are uniformly bounded.

The forward direction is `banach_steinhaus`, the uniform boundedness principle, and is where
completeness of `V` is used; the backward direction is the ε/3 argument
`ContinuousLinearMap.tendsto_of_tendsto_on_dense_of_bounded`. -/
theorem tendsto_iff_tendsto_on_dense_of_completeSpace [CompleteSpace V] {s : Set V} (hs : Dense s)
    (L : V →L[𝕜] W) (Ln : ℕ → V →L[𝕜] W) :
    (∀ v, Tendsto (fun n => Ln n v) atTop (𝓝 (L v))) ↔
      (∀ v ∈ s, Tendsto (fun n => Ln n v) atTop (𝓝 (L v))) ∧ ∃ C, ∀ n, ‖Ln n‖ ≤ C := by
  refine ⟨fun h => ⟨fun v _ => h v, banach_steinhaus fun v => exists_norm_le_of_tendsto (h v)⟩, ?_⟩
  rintro ⟨hdense, C, hC⟩
  exact tendsto_of_tendsto_on_dense_of_bounded hs hC hdense

/-- **The contrapositive of the uniform boundedness principle.** If the norms `‖Lₙ‖` are unbounded
then, for every candidate limit `L`, some vector has `Lₙ v ↛ L v`.

Applied to a sequence of projections whose norms grow — the Fourier projections on the continuous
periodic functions, whose norms are the Lebesgue constants — with `L` the identity, this produces
a function that its own approximations do not converge to. -/
theorem exists_not_tendsto_of_not_bddAbove [CompleteSpace V] {Ln : ℕ → V →L[𝕜] W}
    (h : ¬ BddAbove (Set.range fun n => ‖Ln n‖)) (L : V →L[𝕜] W) :
    ∃ v : V, ¬ Tendsto (fun n => Ln n v) atTop (𝓝 (L v)) := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  obtain ⟨C, hC⟩ := banach_steinhaus fun v => exists_norm_le_of_tendsto (hcon v)
  exact h ⟨C, by rintro x ⟨n, rfl⟩; exact hC n⟩

/-- **The operator norm is lower semicontinuous under pointwise convergence**
([brezis2011functional], Corollary 2.3 (c)): if `Lₙ v → L v` for every `v` and the norms `‖Lₙ‖`
are bounded, then `‖L‖ ≤ liminf ‖Lₙ‖`. For each `v ≠ 0`, `‖L v‖ / ‖v‖` is the limit of
`‖Lₙ v‖ / ‖v‖ ≤ ‖Lₙ‖`, and the bound on the norms makes the comparison of `liminf`s legitimate.
On a Banach space the boundedness of the norms is automatic (`banach_steinhaus`). -/
theorem opNorm_le_liminf_opNorm_of_tendsto {L : V →L[𝕜] W} {Ln : ℕ → V →L[𝕜] W}
    (h : ∀ v, Tendsto (fun n => Ln n v) atTop (𝓝 (L v)))
    (hb : BddAbove (Set.range fun n => ‖Ln n‖)) :
    ‖L‖ ≤ liminf (fun n => ‖Ln n‖) atTop := by
  obtain ⟨C, hC⟩ := hb
  have hC' : ∀ n, ‖Ln n‖ ≤ C := fun n => hC ⟨n, rfl⟩
  have hcobdd : IsCoboundedUnder (· ≥ ·) atTop fun n => ‖Ln n‖ :=
    isCoboundedUnder_ge_of_le atTop hC'
  have hM : 0 ≤ liminf (fun n => ‖Ln n‖) atTop :=
    le_liminf_of_le hcobdd (Eventually.of_forall fun n => norm_nonneg _)
  refine opNorm_le_bound' L hM fun v hv => ?_
  have hv' : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)
  rw [← div_le_iff₀ hv']
  have hlim : Tendsto (fun n => ‖Ln n v‖ / ‖v‖) atTop (𝓝 (‖L v‖ / ‖v‖)) :=
    (h v).norm.div_const _
  calc ‖L v‖ / ‖v‖ = liminf (fun n => ‖Ln n v‖ / ‖v‖) atTop := hlim.liminf_eq.symm
    _ ≤ liminf (fun n => ‖Ln n‖) atTop := by
        refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
          (isBoundedUnder_of ⟨0, fun n => by positivity⟩) hcobdd
        rw [div_le_iff₀ hv']
        exact (Ln n).le_opNorm v

end ContinuousLinearMap

section Corollaries

open NormedSpace

variable {𝕜 G : Type*}

/-- **Weakly bounded implies bounded** ([brezis2011functional], Corollary 2.4): a subset `B` of
a normed space over `RCLike 𝕜` on which every bounded linear functional is bounded is bounded.
The uniform boundedness principle in the (complete) dual `StrongDual 𝕜 G`, applied to the
evaluations `f ↦ f b`, `b ∈ B`, bounds their norms uniformly, and evaluation at `b` has norm
`‖b‖` (the canonical embedding in the bidual is an isometry). Completeness of `G` is not
needed. -/
theorem isBounded_of_forall_dual_image_isBounded [RCLike 𝕜] [NormedAddCommGroup G]
    [NormedSpace 𝕜 G] {B : Set G} (h : ∀ f : StrongDual 𝕜 G, IsBounded (f '' B)) :
    IsBounded B := by
  have hpt : ∀ f : StrongDual 𝕜 G, ∃ C, ∀ b : B, ‖inclusionInDoubleDual 𝕜 G b f‖ ≤ C := fun f => by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (h f)
    exact ⟨C, fun b => hC _ ⟨b, b.2, rfl⟩⟩
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun b : B => inclusionInDoubleDual 𝕜 G b) hpt
  refine isBounded_iff_forall_norm_le.2 ⟨C, fun b hb => ?_⟩
  have := hC ⟨b, hb⟩
  rwa [show inclusionInDoubleDual 𝕜 G b = inclusionInDoubleDualLi 𝕜 b from rfl,
    (inclusionInDoubleDualLi 𝕜).norm_map] at this

/-- A set is bounded iff every bounded linear functional is bounded on it
([brezis2011functional], Corollary 2.4, as an equivalence). -/
theorem isBounded_iff_forall_dual_image_isBounded [RCLike 𝕜] [NormedAddCommGroup G]
    [NormedSpace 𝕜 G] {B : Set G} :
    IsBounded B ↔ ∀ f : StrongDual 𝕜 G, IsBounded (f '' B) :=
  ⟨fun hB f => f.lipschitzWith.isBounded_image hB, isBounded_of_forall_dual_image_isBounded⟩

/-- **Weak-∗ bounded implies bounded** ([brezis2011functional], Corollary 2.5): a set of bounded
linear functionals on a Banach space `G` that is bounded at every point of `G` is bounded in
norm. This is the uniform boundedness principle itself, for the family of functionals indexed
by the set. -/
theorem StrongDual.isBounded_of_forall_eval_isBounded [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G] {B : Set (StrongDual 𝕜 G)}
    (h : ∀ x : G, IsBounded ((fun f : StrongDual 𝕜 G => f x) '' B)) : IsBounded B := by
  have hpt : ∀ x : G, ∃ C, ∀ f : B, ‖(f : StrongDual 𝕜 G) x‖ ≤ C := fun x => by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (h x)
    exact ⟨C, fun f => hC _ ⟨f, f.2, rfl⟩⟩
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun f : B => (f : StrongDual 𝕜 G)) hpt
  exact isBounded_iff_forall_norm_le.2 ⟨C, fun f hf => hC ⟨f, hf⟩⟩

end Corollaries

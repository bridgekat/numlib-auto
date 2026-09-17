/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Module.WeakDual`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-!
# Weak sequential convergence in a normed space

Weak convergence `vₙ ⇀ u` in a normed space `V` is convergence of `toWeakSpace 𝕜 V (vₙ)` in the
weak topology of `WeakSpace 𝕜 V`, and `tendsto_toWeakSpace_iff` says that this is exactly
convergence of `ℓ (vₙ)` for every bounded linear functional `ℓ`.

## Main statements

* `tendsto_toWeakSpace_iff` — weak convergence is pointwise convergence of the bounded linear
  functionals;
* `exists_norm_le_of_tendsto_toWeakSpace` — a weakly convergent sequence is bounded in norm, by
  uniform boundedness applied to its image in the double dual;
* `norm_le_liminf_norm_of_weak_tendsto` — **the norm is weakly sequentially lower semicontinuous**,
  `‖u‖ ≤ liminf ‖vₙ‖`, by evaluating a norming functional of `u`. This is what makes a
  minimization problem over a weakly closed set solvable: a minimizing sequence has a weak limit
  point whose norm is no larger;
* `tendsto_apply_of_tendsto_toWeakSpace_of_tendsto` — `fₙ (vₙ) → g u` when `vₙ ⇀ u` and
  `fₙ → g` in norm;
* `WeakDual.continuous_weakSpace_toWeakDual` — on the dual, the weak-∗ topology `WeakDual 𝕜 V` is
  coarser than the weak topology `WeakSpace 𝕜 (StrongDual 𝕜 V)`, and the weak-∗ versions of the
  three sequential facts, `exists_norm_le_of_tendsto_toWeakDual`,
  `norm_le_liminf_norm_of_weakStar_tendsto` and `tendsto_apply_of_tendsto_toWeakDual_of_tendsto`,
  which need `V` complete because the uniform boundedness principle is applied on `V` itself.

These are [brezis2011functional] Propositions 3.5 and 3.13.
-/

open Filter Topology Bornology

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **Weak convergence is pointwise convergence of the bounded linear functionals**: a net
converges in `WeakSpace 𝕜 V` if and only if `ℓ (vₙ) → ℓ u` for every `ℓ` in the dual. -/
theorem tendsto_toWeakSpace_iff {ι : Type*} {l : Filter ι} {v : ι → V} {u : V} :
    Tendsto (fun n => toWeakSpace 𝕜 V (v n)) l (𝓝 (toWeakSpace 𝕜 V u)) ↔
      ∀ ℓ : StrongDual 𝕜 V, Tendsto (fun n => ℓ (v n)) l (𝓝 (ℓ u)) :=
  WeakBilin.tendsto_iff_forall_eval_tendsto (B := (topDualPairing 𝕜 V).flip) fun _ _ h => by
    by_contra hne
    obtain ⟨f, hf⟩ := SeparatingDual.exists_separating_of_ne (R := 𝕜) hne
    exact hf (DFunLike.congr_fun h f)

/-- A weakly convergent sequence is bounded in norm.

This is the uniform boundedness principle applied to the images of the `vₙ` in the double dual,
which is a family of functionals on the (complete) dual: weak convergence makes the family
pointwise bounded there, and the isometric inclusion carries the resulting bound back. -/
theorem exists_norm_le_of_tendsto_toWeakSpace {v : ℕ → V} {u : V}
    (h : Tendsto (fun n => toWeakSpace 𝕜 V (v n)) atTop (𝓝 (toWeakSpace 𝕜 V u))) :
    ∃ C : ℝ, ∀ n, ‖v n‖ ≤ C := by
  rw [tendsto_toWeakSpace_iff] at h
  have hb : ∀ ℓ : StrongDual 𝕜 V,
      ∃ C : ℝ, ∀ n, ‖NormedSpace.inclusionInDoubleDual 𝕜 V (v n) ℓ‖ ≤ C := by
    intro ℓ
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _ (h ℓ))
    exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩
  obtain ⟨C, hC⟩ := banach_steinhaus hb
  refine ⟨C, fun n => ?_⟩
  rw [← (NormedSpace.inclusionInDoubleDualLi 𝕜).norm_map (v n)]
  exact hC n

/-- **The norm is weakly sequentially lower semicontinuous**: `vₙ ⇀ u` implies
`‖u‖ ≤ liminf ‖vₙ‖`.

Equality can fail — an orthonormal sequence in a Hilbert space converges weakly to `0` while every
term has norm `1` — so the norm is not weakly continuous, only lower semicontinuous. The proof
evaluates a norming functional `ℓ` of `u`, for which `‖u‖ = ℓ u = lim ℓ (vₙ)` and
`‖ℓ (vₙ)‖ ≤ ‖vₙ‖`; boundedness of `‖vₙ‖` is what makes the `liminf` comparison legitimate. -/
theorem norm_le_liminf_norm_of_weak_tendsto {v : ℕ → V} {u : V}
    (h : Tendsto (fun n => toWeakSpace 𝕜 V (v n)) atTop (𝓝 (toWeakSpace 𝕜 V u))) :
    ‖u‖ ≤ liminf (fun n => ‖v n‖) atTop := by
  obtain ⟨C, hC⟩ := exists_norm_le_of_tendsto_toWeakSpace h
  rw [tendsto_toWeakSpace_iff] at h
  obtain ⟨ℓ, hℓ, hval⟩ := exists_dual_vector'' 𝕜 u
  have hlim : Tendsto (fun n => ‖ℓ (v n)‖) atTop (𝓝 ‖ℓ u‖) := (h ℓ).norm
  have hcobdd : IsCoboundedUnder (· ≥ ·) atTop fun n => ‖v n‖ := by
    refine ⟨C, fun a ha => ?_⟩
    rw [Filter.eventually_map] at ha
    obtain ⟨n, hn⟩ := ha.exists
    exact hn.trans (hC n)
  have hle : ∀ n, ‖ℓ (v n)‖ ≤ ‖v n‖ := fun n =>
    (ℓ.le_opNorm (v n)).trans (by simpa using mul_le_mul_of_nonneg_right hℓ (norm_nonneg (v n)))
  calc ‖u‖ = ‖ℓ u‖ := by rw [hval, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg u)]
    _ = liminf (fun n => ‖ℓ (v n)‖) atTop := hlim.liminf_eq.symm
    _ ≤ liminf (fun n => ‖v n‖) atTop :=
        liminf_le_liminf (Filter.Eventually.of_forall hle) hlim.isBoundedUnder_ge hcobdd

/-- **A weakly convergent sequence paired with a norm-convergent sequence of functionals
converges**: if `xₙ ⇀ u` weakly and `fₙ → g` in the dual norm then `fₙ (xₙ) → g u`.

The estimate is `‖fₙ (xₙ) - g u‖ ≤ ‖fₙ - g‖ ‖xₙ‖ + ‖g (xₙ) - g u‖`, where the first term tends to
`0` because a weakly convergent sequence is bounded (`exists_norm_le_of_tendsto_toWeakSpace`) and
the second by weak convergence tested against `g`. -/
theorem tendsto_apply_of_tendsto_toWeakSpace_of_tendsto {x : ℕ → V} {u : V}
    {f : ℕ → StrongDual 𝕜 V} {g : StrongDual 𝕜 V}
    (hx : Tendsto (fun n => toWeakSpace 𝕜 V (x n)) atTop (𝓝 (toWeakSpace 𝕜 V u)))
    (hf : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun n => f n (x n)) atTop (𝓝 (g u)) := by
  obtain ⟨C, hC⟩ := exists_norm_le_of_tendsto_toWeakSpace hx
  rw [tendsto_toWeakSpace_iff] at hx
  rw [tendsto_iff_norm_sub_tendsto_zero] at hf ⊢
  have h1 : Tendsto (fun n => ‖f n - g‖ * C + ‖g (x n) - g u‖) atTop (𝓝 0) := by
    have := (hf.mul_const C).add ((tendsto_iff_norm_sub_tendsto_zero.1 (hx g)))
    simpa using this
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h1
  calc ‖f n (x n) - g u‖ = ‖(f n - g) (x n) + (g (x n) - g u)‖ := by
        congr 1; simp
    _ ≤ ‖(f n - g) (x n)‖ + ‖g (x n) - g u‖ := norm_add_le _ _
    _ ≤ ‖f n - g‖ * C + ‖g (x n) - g u‖ := by
        gcongr
        exact ((f n - g).le_opNorm (x n)).trans (by gcongr; exact hC n)

/-!
### The weak-∗ topology on the dual

On the dual `V'` there are three topologies, norm ≥ weak ≥ weak-∗: the weak topology is
`WeakSpace 𝕜 (StrongDual 𝕜 V)` and the weak-∗ topology is `WeakDual 𝕜 V`. Mathlib's
`NormedSpace.Dual.toWeakDual_continuous` compares the first and the third; the statements below
compare the second and the third, and give the weak-∗ versions of the three sequential facts
above. Boundedness of a weak-∗ convergent sequence is the uniform boundedness principle on `V`
itself, so it needs `V` complete, whereas the weak statements needed nothing (they were proved in
the complete dual).
-/

/-- **The weak-∗ topology is coarser than the weak topology of the dual**: the identity from
`WeakSpace 𝕜 (StrongDual 𝕜 V)` to `WeakDual 𝕜 V` is continuous. Evaluation at `x : V` is the
bounded functional `inclusionInDoubleDual 𝕜 V x` on the dual, hence continuous for the dual's
weak topology. -/
theorem WeakDual.continuous_weakSpace_toWeakDual :
    Continuous (fun f : WeakSpace 𝕜 (StrongDual 𝕜 V) =>
      StrongDual.toWeakDual ((toWeakSpace 𝕜 (StrongDual 𝕜 V)).symm f)) := by
  refine WeakDual.continuous_of_continuous_eval fun x => ?_
  exact WeakBilin.eval_continuous (topDualPairing 𝕜 (StrongDual 𝕜 V)).flip
    (NormedSpace.inclusionInDoubleDual 𝕜 V x)

/-- A sequence of functionals converging weakly (in `σ(V', V'')`) converges weak-∗
(in `σ(V', V)`). -/
theorem tendsto_toWeakDual_of_tendsto_toWeakSpace {f : ℕ → StrongDual 𝕜 V} {g : StrongDual 𝕜 V}
    (h : Tendsto (fun n => toWeakSpace 𝕜 _ (f n)) atTop (𝓝 (toWeakSpace 𝕜 _ g))) :
    Tendsto (fun n => StrongDual.toWeakDual (f n)) atTop (𝓝 (StrongDual.toWeakDual g)) :=
  (WeakDual.continuous_weakSpace_toWeakDual.tendsto _).comp h

/-- **A weak-∗ convergent sequence in the dual of a Banach space is bounded in norm**: weak-∗
convergence makes the family `fₙ` pointwise bounded on `V`, and the uniform boundedness principle
(`banach_steinhaus`, which is where completeness of `V` enters) gives a uniform bound. -/
theorem exists_norm_le_of_tendsto_toWeakDual [CompleteSpace V] {f : ℕ → StrongDual 𝕜 V}
    {g : StrongDual 𝕜 V}
    (h : Tendsto (fun n => StrongDual.toWeakDual (f n)) atTop (𝓝 (StrongDual.toWeakDual g))) :
    ∃ C : ℝ, ∀ n, ‖f n‖ ≤ C := by
  rw [tendsto_iff_forall_eval_tendsto_topDualPairing] at h
  have hb : ∀ x : V, ∃ C : ℝ, ∀ n, ‖f n x‖ ≤ C := fun x => by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _ (h x))
    exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩
  exact banach_steinhaus hb

/-- **The dual norm is weak-∗ sequentially lower semicontinuous**: if `fₙ ⇀∗ g` in the dual of a
Banach space then `‖g‖ ≤ liminf ‖fₙ‖`.

For each `x`, `‖g x‖ = lim ‖fₙ x‖ ≤ liminf (‖fₙ‖ ‖x‖) = (liminf ‖fₙ‖) ‖x‖`, the last step because
`t ↦ t ‖x‖` is monotone and continuous and the sequence `‖fₙ‖` is bounded
(`exists_norm_le_of_tendsto_toWeakDual`); then `ContinuousLinearMap.opNorm_le_bound`. -/
theorem norm_le_liminf_norm_of_weakStar_tendsto [CompleteSpace V] {f : ℕ → StrongDual 𝕜 V}
    {g : StrongDual 𝕜 V}
    (h : Tendsto (fun n => StrongDual.toWeakDual (f n)) atTop (𝓝 (StrongDual.toWeakDual g))) :
    ‖g‖ ≤ liminf (fun n => ‖f n‖) atTop := by
  obtain ⟨C, hC⟩ := exists_norm_le_of_tendsto_toWeakDual h
  rw [tendsto_iff_forall_eval_tendsto_topDualPairing] at h
  have hcobdd : IsCoboundedUnder (· ≥ ·) atTop fun n => ‖f n‖ :=
    isCoboundedUnder_ge_of_eventually_le atTop (Filter.Eventually.of_forall hC)
  have hbdd : IsBoundedUnder (· ≥ ·) atTop fun n => ‖f n‖ :=
    isBoundedUnder_of ⟨0, fun n => norm_nonneg _⟩
  have hL : 0 ≤ liminf (fun n => ‖f n‖) atTop :=
    le_liminf_of_le hcobdd (Filter.Eventually.of_forall fun n => norm_nonneg _)
  refine ContinuousLinearMap.opNorm_le_bound _ hL fun x => ?_
  have hlim : Tendsto (fun n => ‖f n x‖) atTop (𝓝 ‖g x‖) := (h x).norm
  have hle : ∀ n, ‖f n x‖ ≤ ‖f n‖ * ‖x‖ := fun n => (f n).le_opNorm x
  calc ‖g x‖ = liminf (fun n => ‖f n x‖) atTop := hlim.liminf_eq.symm
    _ ≤ liminf (fun n => ‖f n‖ * ‖x‖) atTop :=
        liminf_le_liminf (Filter.Eventually.of_forall hle) hlim.isBoundedUnder_ge
          (isCoboundedUnder_ge_of_eventually_le atTop (Filter.Eventually.of_forall fun n =>
            mul_le_mul_of_nonneg_right (hC n) (norm_nonneg x)))
    _ = liminf (fun n => ‖f n‖) atTop * ‖x‖ := by
        have hmono : Monotone (fun t : ℝ => t * ‖x‖) :=
          fun a b hab => mul_le_mul_of_nonneg_right hab (norm_nonneg x)
        exact (hmono.map_liminf_of_continuousAt (fun n => ‖f n‖)
          (continuous_id.mul continuous_const).continuousAt hcobdd hbdd).symm

/-- **A weak-∗ convergent sequence of functionals paired with a norm-convergent sequence
converges**: if `fₙ ⇀∗ g` in the dual of a Banach space and `xₙ → u` in norm then
`fₙ (xₙ) → g u`. The estimate is `‖fₙ (xₙ) - g u‖ ≤ ‖fₙ‖ ‖xₙ - u‖ + ‖fₙ u - g u‖`, with `‖fₙ‖`
bounded by `exists_norm_le_of_tendsto_toWeakDual`. -/
theorem tendsto_apply_of_tendsto_toWeakDual_of_tendsto [CompleteSpace V] {f : ℕ → StrongDual 𝕜 V}
    {g : StrongDual 𝕜 V} {x : ℕ → V} {u : V}
    (hf : Tendsto (fun n => StrongDual.toWeakDual (f n)) atTop (𝓝 (StrongDual.toWeakDual g)))
    (hx : Tendsto x atTop (𝓝 u)) :
    Tendsto (fun n => f n (x n)) atTop (𝓝 (g u)) := by
  obtain ⟨C, hC⟩ := exists_norm_le_of_tendsto_toWeakDual hf
  rw [tendsto_iff_forall_eval_tendsto_topDualPairing] at hf
  rw [tendsto_iff_norm_sub_tendsto_zero] at hx ⊢
  have h1 : Tendsto (fun n => C * ‖x n - u‖ + ‖f n u - g u‖) atTop (𝓝 0) := by
    have := (hx.const_mul C).add ((tendsto_iff_norm_sub_tendsto_zero.1 (hf u)))
    rw [mul_zero, add_zero] at this
    exact this
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h1
  calc ‖f n (x n) - g u‖ = ‖f n (x n - u) + (f n u - g u)‖ := by
        congr 1; simp
    _ ≤ ‖f n (x n - u)‖ + ‖f n u - g u‖ := norm_add_le _ _
    _ ≤ C * ‖x n - u‖ + ‖f n u - g u‖ := by
        gcongr
        exact ((f n).le_opNorm (x n - u)).trans (by gcongr; exact hC n)

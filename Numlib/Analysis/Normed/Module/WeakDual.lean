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
  point whose norm is no larger.
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

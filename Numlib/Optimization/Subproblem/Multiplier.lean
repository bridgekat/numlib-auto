import Numlib.Optimization.Subproblem.Regularization
import Numlib.Optimization.Subproblem.Secular

/-!
# The optimal multiplier and the secular equation

Let `H` be a symmetric operator on a finite-dimensional real inner product space, `λ₁ = leftmost hH`
its leftmost eigenvalue and `λₛ = shiftThreshold hH = max 0 (-λ₁)`. The global minimizers of the
trust-region and regularization subproblems solve a shifted system `(H + λ*) s = -g` with
`λ* ≥ λₛ` and `‖s‖² = τ(λ*)` for a *target* `τ` (`Δ²` for the trust region,
`(λ/σ)^{2/(r-2)}` for the regularization; [cartis2022evaluation] (8.2.9)). This file locates `λ*`
on the secular function `π(λ) = ‖s(λ)‖²` ([cartis2022evaluation] Lemma 8.2.1, §8.3).

Everything is first proved for an abstract target `τ`, monotone on `[λₛ, ∞)` and positive on
`(λₛ, ∞)`, and an abstract shifted solution `(H + μ) s = -g`, `λₛ ≤ μ`, `‖s‖² ≤ τ μ` with equality
when `μ > λₛ`; the two subproblems are then instances.

## Main statements

* `Subproblem.existsUnique_secular_root`: Lemma 8.2.1, the secular equation `π = τ` has a unique
  root to the right of `λₛ` when `π > τ` near `λₛ`; `Subproblem.existsUnique_secular_root_of_lt`
  is the same under the book's hypothesis `π(λₛ) > τ(λₛ)`, with `π(λₛ) = ‖sₛ‖²` or `+∞`
  (`Subproblem.tendsto_secular_shiftThreshold`, `Subproblem.tendsto_secular_shiftThreshold_atTop`).
* `Subproblem.le_secular_iff_of_shifted`, `Subproblem.le_secular_iff_of_trustRegion`,
  `Subproblem.le_secular_iff_of_regularization`: for `λ > λₛ`, `τ(λ) ≤ π(λ) ↔ λ ≤ λ*`. This is
  the book's partition of `(λₛ, ∞)` into `𝓛 = (λₛ, λ*]` and `𝓖 = (λ*, ∞)`, including the hard case
  (where `𝓛 = ∅`).
* `Subproblem.shiftThreshold_le_of_isTrustRegionMultiplier`,
  `Subproblem.shiftThreshold_le_of_isMinOn_regModel`: `λₛ ≤ λ*`, and every minimizer is the
  minimum-norm solution `particular hH g λ*` plus a kernel vector orthogonal to `g`, the kernel
  vector vanishing when `λ* > -λ₁` (Corollaries 8.3.1/8.3.2, (8.3.1)–(8.3.2)).
* `Subproblem.multiplier_classification` and its instances
  `Subproblem.multiplier_classification_of_trustRegion`,
  `Subproblem.multiplier_classification_of_regularization`: `λ* = λₛ` exactly when `g` is
  orthogonal to `ker (H + λₛ)` and `‖particular hH g λₛ‖² ≤ τ(λₛ)` (the interior and hard cases);
  otherwise `λ* > λₛ` (the easy case) and the minimizer is `step g H λ*`.
* `Subproblem.isMinOn_closedBall_of_hardCase`, `Subproblem.isMinOn_regModel_of_hardCase`,
  `Subproblem.exists_norm_particular_add_smul_eq`: the hard-case solutions `sₛ + α v₁`.
* `Subproblem.optimalValue_eq_of_trustRegion`, `Subproblem.optimalValue_eq_of_regularization`:
  the optimal values (8.3.5) and (8.3.3).

## Implementation notes

The book describes `𝓝 = (-∞, λₛ]` also as "`H + λM` is not positive definite"; the two differ when
`λ₁ > 0` (then `(-λ₁, 0]` is in the first set but not in the second). The interval description is
the one used here.
-/

open Set Filter Topology
open scoped RealInnerProductSpace

namespace Subproblem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : E →L[ℝ] E} {hH : (H : E →ₗ[ℝ] E).IsSymmetric} {g : E}

/-! ### Solutions of a shifted system -/

section Shifted

/-- **Structure of the solutions of a shifted system.** If `(H + μ) s = -g` then the system is
consistent, `g ⊥ ker (H + μ)`; `s` is the minimum-norm solution `particular hH g μ` plus a vector
`w = s - particular hH g μ` of `ker (H + μ)` with `⟪g, w⟫ = 0`; `‖particular hH g μ‖ ≤ ‖s‖`; and
`s = step g H μ` when `μ > -λ₁`. -/
theorem particular_add_of_shifted {μ : ℝ} {s : E} (hs : (H + μ • (1 : E →L[ℝ] E)) s = -g) :
    g ∈ (LinearMap.ker ((H + μ • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ ∧
      s - particular hH g μ ∈ LinearMap.ker ((H + μ • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E) ∧
      ⟪g, s - particular hH g μ⟫ = 0 ∧ ‖particular hH g μ‖ ≤ ‖s‖ ∧
      (-leftmost hH < μ → s = step g H μ) := by
  have hcons : g ∈ (LinearMap.ker ((H + μ • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hv
    have h := ContinuousLinearMap.isSymmetric_add_smul_one hH μ v s
    simp only [ContinuousLinearMap.coe_coe] at h
    rw [← neg_neg g, ← hs, inner_neg_right, ← h, hv, inner_zero_left, neg_zero]
  obtain ⟨-, hiff, hmin, horth⟩ := (particular_spec (hH := hH) (g := g) μ).2.1 hcons
  have hker := (hiff s).1 hs
  exact ⟨hcons, hker, horth _ hker, hmin s hs, fun hμ => (step_spec hμ).2 s hs⟩

/-- The secular function is antitone on `λ > -λ₁` (for every `g`; strictly for `g ≠ 0`). -/
theorem secular_antitoneOn : AntitoneOn (secular g H) (Ioi (-leftmost hH)) := by
  rcases eq_or_ne g 0 with rfl | hg
  · rw [secular_zero_left]; exact fun _ _ _ _ _ => le_rfl
  · exact ((secular_shape (hH := hH) hg 1).2.2.1).antitoneOn

/-- `(a / e)² ≤ (a / d)²` for `0 < d ≤ e`. -/
private theorem div_sq_le_div_sq {a d e : ℝ} (hd : 0 < d) (hde : d ≤ e) :
    (a / e) ^ 2 ≤ (a / d) ^ 2 := by
  rw [div_pow, div_pow]
  exact div_le_div_of_nonneg_left (sq_nonneg a) (by positivity) (pow_le_pow_left₀ hd.le hde 2)

/-- `(a / e)² < (a / d)²` for `0 < d < e` and `a ≠ 0`. -/
private theorem div_sq_lt_div_sq {a d e : ℝ} (ha : a ≠ 0) (hd : 0 < d) (hde : d < e) :
    (a / e) ^ 2 < (a / d) ^ 2 := by
  rw [div_pow, div_pow]
  exact div_lt_div_of_pos_left (by positivity) (by positivity)
    (pow_lt_pow_left₀ hde hd.le two_ne_zero)

/-- **The secular function lies below the minimum-norm solution.** If `g ≠ 0` is orthogonal to
`ker (H + μ)` with `μ ≥ -λ₁`, then `π(λ) < ‖particular hH g μ‖²` for every `λ > μ`. In the hard
case `μ = -λ₁` this says that `π` stays below its limit `‖sₛ‖²` at the threshold. -/
theorem secular_lt_norm_particular_sq (hg : g ≠ 0) {μ lam : ℝ} (hμ : -leftmost hH ≤ μ)
    (hlt : μ < lam) (hcons : g ∈ (LinearMap.ker ((H + μ • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ) :
    secular g H lam < ‖particular hH g μ‖ ^ 2 := by
  have hlam : -leftmost hH < lam := by linarith
  have hγ : ∀ i, μ + hH.eigenvalues rfl i = 0 → ⟪hH.eigenvectorBasis rfl i, g⟫ = 0 :=
    fun i hi => Submodule.inner_right_of_mem_orthogonal (eigenvectorBasis_mem_ker hi) hcons
  have hd : ∀ i, 0 ≤ μ + hH.eigenvalues rfl i := fun i => by
    have := leftmost_le_eigenvalues (hH := hH) i; linarith
  obtain ⟨i, hi⟩ : ∃ i, ⟪hH.eigenvectorBasis rfl i, g⟫ ≠ 0 := by
    by_contra h
    push Not at h
    exact hg (eq_of_inner_eigenvectorBasis (hH := hH) fun i => by rw [h i, inner_zero_right])
  rw [secular, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    inner_eq_sum_eigenvectorBasis (hH := hH), inner_eq_sum_eigenvectorBasis (hH := hH)]
  simp only [inner_eigenvectorBasis_step hlam, inner_eigenvectorBasis_particular, ← sq]
  refine Finset.sum_lt_sum (fun j _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
  · rcases (hd j).eq_or_lt with h | h
    · rw [hγ j h.symm]; simp
    · exact div_sq_le_div_sq h (by linarith)
  · have hdi : 0 < μ + hH.eigenvalues rfl i :=
      (hd i).lt_of_ne fun h => hi (hγ i h.symm)
    exact div_sq_lt_div_sq (neg_ne_zero.2 hi) hdi (by linarith)

/-- If `(H + μ) s = -g` with `μ ≥ -λ₁`, then `π(λ) ≤ ‖s‖²` for `λ > μ`, strictly if `g ≠ 0`. -/
theorem secular_lt_norm_sq_of_shifted (hg : g ≠ 0) {μ lam : ℝ} {s : E}
    (hμ : -leftmost hH ≤ μ) (hs : (H + μ • (1 : E →L[ℝ] E)) s = -g) (hlt : μ < lam) :
    secular g H lam < ‖s‖ ^ 2 := by
  obtain ⟨hcons, -, -, hle, -⟩ := particular_add_of_shifted (hH := hH) hs
  exact (secular_lt_norm_particular_sq hg hμ hlt hcons).trans_le
    (pow_le_pow_left₀ (norm_nonneg _) hle 2)

end Shifted

/-! ### Lemma 8.2.1 -/

section Root

/-- **Lemma 8.2.1** (root of the secular equation). Let `τ` be continuous, monotone and
nonnegative on `(λₛ, ∞)` and not identically zero there, and suppose `π > τ` near `λₛ`:
`∀ᶠ λ in 𝓝[>] λₛ, τ λ < π λ` (the book's `π(λₛ) > τ(λₛ)`, with `π(λₛ)` read as the right limit of
`π`, possibly `+∞`; see `tendsto_step_threshold`). Then the secular equation `π = τ` has a unique
root `λ* > λₛ`; moreover `τ < π` on `(λₛ, λ*)` and `π < τ` on `(λ*, ∞)`. -/
theorem existsUnique_secular_root {τ : ℝ → ℝ} (hτc : ContinuousOn τ (Ioi (shiftThreshold hH)))
    (hτm : MonotoneOn τ (Ioi (shiftThreshold hH)))
    (hτ0 : ∀ lam ∈ Ioi (shiftThreshold hH), 0 ≤ τ lam)
    (hτne : ∃ lam ∈ Ioi (shiftThreshold hH), τ lam ≠ 0)
    (hleft : ∀ᶠ lam in 𝓝[>] (shiftThreshold hH), τ lam < secular g H lam) :
    ∃ lamStar, shiftThreshold hH < lamStar ∧ secular g H lamStar = τ lamStar ∧
      (∀ lam ∈ Ioo (shiftThreshold hH) lamStar, τ lam < secular g H lam) ∧
      (∀ lam ∈ Ioi lamStar, secular g H lam < τ lam) ∧
      ∀ lam, shiftThreshold hH < lam → secular g H lam = τ lam → lam = lamStar := by
  set ls := shiftThreshold hH
  obtain ⟨a, ⟨hτa, has⟩⟩ := (hleft.and self_mem_nhdsWithin).exists
  have has : ls < a := has
  have hg : g ≠ 0 := by
    rintro rfl
    rw [secular_zero_left] at hτa
    exact (hτ0 a has).not_gt hτa
  -- `Ψ = π - τ` is strictly decreasing and continuous on `(λₛ, ∞)`
  have hsub := Ioi_shiftThreshold_subset (hH := hH)
  obtain ⟨-, hπc, hπa, -, hπ0, -⟩ := secular_shape (hH := hH) hg 1
  have hΨ : StrictAntiOn (fun lam => secular g H lam - τ lam) (Ioi ls) := fun x hx y hy hxy => by
    have := hπa (hsub hx) (hsub hy) hxy
    have := hτm hx hy hxy.le
    simp only; linarith
  have hΨc : ContinuousOn (fun lam => secular g H lam - τ lam) (Ioi ls) :=
    (hπc.mono hsub).sub hτc
  -- a point where `Ψ < 0`
  obtain ⟨c, hcs, hτc0⟩ := hτne
  have hτcpos : 0 < τ c := (hτ0 c hcs).lt_of_ne' hτc0
  obtain ⟨b, hb⟩ := (eventually_ge_atTop (max a c) |>.and
    (hπ0.eventually (gt_mem_nhds hτcpos))).exists
  have hab : a ≤ b := (le_max_left _ _).trans hb.1
  have hcb : c ≤ b := (le_max_right _ _).trans hb.1
  have hbs : ls < b := has.trans_le hab
  have hΨb : secular g H b - τ b < 0 := by have := hτm hcs hbs hcb; linarith [hb.2]
  have hΨa : 0 < secular g H a - τ a := by linarith
  obtain ⟨lamStar, hmem, hroot⟩ := intermediate_value_Icc' hab
    (hΨc.mono fun x hx => has.trans_le hx.1) ⟨hΨb.le, hΨa.le⟩
  have hls : ls < lamStar := has.trans_le hmem.1
  simp only at hroot
  refine ⟨lamStar, hls, by linarith, fun lam hlam => ?_, fun lam hlam => ?_, fun lam hlam h => ?_⟩
  · have := hΨ hlam.1 hls hlam.2; simp only at this; linarith
  · have := hΨ hls (hls.trans hlam) hlam; simp only at this; linarith
  · by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := hΨ hlam hls hlt; simp only at this; linarith
    · have := hΨ hls hlam hlt; simp only at this; linarith

/-- The secular function tends to `‖particular hH g λₛ‖²` as `λ ↓ λₛ` when the system at `λₛ` is
consistent, `g ⊥ ker (H + λₛ)`: at `λₛ = -λ₁` this is `tendsto_step_threshold`, and for
`λₛ > -λ₁` it is continuity of `π` at `λₛ`, where `particular hH g λₛ = s(λₛ)`. -/
theorem tendsto_secular_shiftThreshold
    (hg : g ∈ (LinearMap.ker ((H + shiftThreshold hH • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ) :
    Tendsto (secular g H) (𝓝[>] (shiftThreshold hH))
      (𝓝 (‖particular hH g (shiftThreshold hH)‖ ^ 2)) := by
  rcases neg_leftmost_le_shiftThreshold (hH := hH).eq_or_lt with h | h
  · rw [← h] at hg ⊢
    exact ((tendsto_step_threshold (hH := hH) (g := g)).1 hg).2
  · have hc : ContinuousAt (secularSum (hH.eigenvalues rfl) (secularWeight hH g))
        (shiftThreshold hH) :=
      continuousOn_secularSum.continuousAt (secularDomain_mem_nhds (mem_secularDomain_of_lt h))
    have hc' : ContinuousAt (secular g H) (shiftThreshold hH) :=
      hc.congr (secular_eventuallyEq h).symm
    rw [(particular_spec (hH := hH) (g := g) _).2.2 h]
    exact hc'.tendsto.mono_left nhdsWithin_le_nhds

/-- If `g` is not orthogonal to `ker (H + λₛ)`, then `λₛ = -λ₁` and `π(λ) → +∞` as `λ ↓ λₛ`. -/
theorem tendsto_secular_shiftThreshold_atTop
    (hg : g ∉ (LinearMap.ker ((H + shiftThreshold hH • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ) :
    Tendsto (secular g H) (𝓝[>] (shiftThreshold hH)) atTop := by
  rcases neg_leftmost_le_shiftThreshold (hH := hH).eq_or_lt with h | h
  · rw [← h] at hg ⊢
    exact (tendsto_step_threshold (hH := hH) (g := g)).2 hg
  · exfalso
    refine hg ((Submodule.mem_orthogonal' _ _).2 fun v hv => ?_)
    have hv0 : v = 0 := by
      refine injective_add_smul (hH := hH) h ?_
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hv
      rw [hv, map_zero]
    rw [hv0, inner_zero_right]

/-- **Lemma 8.2.1 with the book's hypothesis** `π(λₛ) > τ(λₛ)`. Here `π(λₛ)` is the right limit of
`π` at `λₛ`: it is `‖particular hH g λₛ‖²` (`= ‖s(λₛ)‖²` when `λₛ > -λ₁`) if the system at `λₛ` is
consistent, `g ⊥ ker (H + λₛ)`, and `+∞` otherwise (`tendsto_secular_shiftThreshold`,
`tendsto_secular_shiftThreshold_atTop`). So the hypothesis is
`g ⊥ ker (H + λₛ) → τ(λₛ) < ‖particular hH g λₛ‖²`. With `τ` continuous on `[λₛ, ∞)`, monotone
and nonnegative on `(λₛ, ∞)` and not identically zero there, the secular equation `π = τ` has a
unique root `λ* > λₛ`, with `τ < π` on `(λₛ, λ*)` and `π < τ` on `(λ*, ∞)`. -/
theorem existsUnique_secular_root_of_lt {τ : ℝ → ℝ}
    (hτc : ContinuousOn τ (Ici (shiftThreshold hH)))
    (hτm : MonotoneOn τ (Ioi (shiftThreshold hH)))
    (hτ0 : ∀ lam ∈ Ioi (shiftThreshold hH), 0 ≤ τ lam)
    (hτne : ∃ lam ∈ Ioi (shiftThreshold hH), τ lam ≠ 0)
    (hπ : g ∈ (LinearMap.ker ((H + shiftThreshold hH • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ →
      τ (shiftThreshold hH) < ‖particular hH g (shiftThreshold hH)‖ ^ 2) :
    ∃ lamStar, shiftThreshold hH < lamStar ∧ secular g H lamStar = τ lamStar ∧
      (∀ lam ∈ Ioo (shiftThreshold hH) lamStar, τ lam < secular g H lam) ∧
      (∀ lam ∈ Ioi lamStar, secular g H lam < τ lam) ∧
      ∀ lam, shiftThreshold hH < lam → secular g H lam = τ lam → lam = lamStar := by
  have hτt : Tendsto τ (𝓝[>] (shiftThreshold hH)) (𝓝 (τ (shiftThreshold hH))) :=
    ((hτc (shiftThreshold hH) self_mem_Ici).mono Ioi_subset_Ici_self).tendsto
  refine existsUnique_secular_root (hτc.mono Ioi_subset_Ici_self) hτm hτ0 hτne ?_
  by_cases hg : g ∈ (LinearMap.ker ((H + shiftThreshold hH • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ
  · exact hτt.eventually_lt (tendsto_secular_shiftThreshold hg) (hπ hg)
  · filter_upwards [hτt.eventually (gt_mem_nhds (lt_add_one (τ (shiftThreshold hH)))),
      (tendsto_secular_shiftThreshold_atTop hg).eventually_gt_atTop (τ (shiftThreshold hH) + 1)]
      with lam h1 h2
    exact h1.trans h2

end Root

/-! ### The multiplier versus the secular function, for an abstract target -/

section Abstract

variable {τ : ℝ → ℝ} {μ : ℝ} {s : E}

/-- **Location of the multiplier** (abstract target). Let `τ` be monotone on `[λₛ, ∞)` and
positive on `(λₛ, ∞)`, and let `(H + μ) s = -g` with `λₛ ≤ μ`, `‖s‖² ≤ τ μ`, and `‖s‖² = τ μ`
when `μ > λₛ`. Then for every `λ > λₛ`: `τ λ ≤ π(λ) ↔ λ ≤ μ`. -/
theorem le_secular_iff_of_shifted (hτ : MonotoneOn τ (Ici (shiftThreshold hH)))
    (hτpos : ∀ lam, shiftThreshold hH < lam → 0 < τ lam) (hμ : shiftThreshold hH ≤ μ)
    (hs : (H + μ • (1 : E →L[ℝ] E)) s = -g) (hsτ : ‖s‖ ^ 2 ≤ τ μ)
    (heq : shiftThreshold hH < μ → τ μ ≤ ‖s‖ ^ 2) {lam : ℝ} (hlam : shiftThreshold hH < lam) :
    τ lam ≤ secular g H lam ↔ lam ≤ μ := by
  have hμ1 : -leftmost hH ≤ μ := neg_leftmost_le_shiftThreshold.trans hμ
  have hlam1 : -leftmost hH < lam := neg_leftmost_le_shiftThreshold.trans_lt hlam
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    have hlt' : secular g H lam < τ lam := by
      rcases eq_or_ne g 0 with rfl | hg
      · rw [secular_zero_left]; exact hτpos lam hlam
      · calc secular g H lam < ‖s‖ ^ 2 := secular_lt_norm_sq_of_shifted hg hμ1 hs hlt
          _ ≤ τ μ := hsτ
          _ ≤ τ lam := hτ hμ (hμ.trans hlt.le) hlt.le
    linarith
  · intro hle
    have hμs : shiftThreshold hH < μ := hlam.trans_le hle
    have hstep := (particular_add_of_shifted (hH := hH) hs).2.2.2.2
      (neg_leftmost_le_shiftThreshold.trans_lt hμs)
    calc τ lam ≤ τ μ := hτ hlam.le hμ hle
      _ ≤ ‖s‖ ^ 2 := heq hμs
      _ = secular g H μ := by rw [secular, hstep]
      _ ≤ secular g H lam := secular_antitoneOn hlam1 (hlam1.trans_le hle) hle

/-- **Easy/hard case classification** (abstract target). Under the hypotheses of
`le_secular_iff_of_shifted`, the multiplier sits at the threshold, `μ = λₛ`, exactly when the
system at `λₛ` is consistent, `g ⊥ ker (H + λₛ)`, and its minimum-norm solution
`sₛ = particular hH g λₛ` satisfies `‖sₛ‖² ≤ τ(λₛ)` (the interior and hard cases). Otherwise
`μ > λₛ` (the easy case) and `s = step g H μ`. -/
theorem multiplier_classification (hτ : MonotoneOn τ (Ici (shiftThreshold hH)))
    (hτpos : ∀ lam, shiftThreshold hH < lam → 0 < τ lam) (hμ : shiftThreshold hH ≤ μ)
    (hs : (H + μ • (1 : E →L[ℝ] E)) s = -g) (hsτ : ‖s‖ ^ 2 ≤ τ μ)
    (heq : shiftThreshold hH < μ → τ μ ≤ ‖s‖ ^ 2) :
    (μ = shiftThreshold hH ↔
      g ∈ (LinearMap.ker ((H + shiftThreshold hH • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ ∧
        ‖particular hH g (shiftThreshold hH)‖ ^ 2 ≤ τ (shiftThreshold hH)) ∧
    (shiftThreshold hH < μ → s = step g H μ) := by
  refine ⟨⟨?_, fun ⟨hcons, hnorm⟩ => ?_⟩, fun hμs => ?_⟩
  · rintro rfl
    obtain ⟨hcons, -, -, hle, -⟩ := particular_add_of_shifted (hH := hH) hs
    exact ⟨hcons, (pow_le_pow_left₀ (norm_nonneg _) hle 2).trans hsτ⟩
  · by_contra hne
    have hμs : shiftThreshold hH < μ := hμ.lt_of_ne (Ne.symm hne)
    have hstep := (particular_add_of_shifted (hH := hH) hs).2.2.2.2
      (neg_leftmost_le_shiftThreshold.trans_lt hμs)
    have h1 : τ μ ≤ secular g H μ := by rw [secular, ← hstep]; exact heq hμs
    rcases eq_or_ne g 0 with rfl | hg
    · rw [secular_zero_left] at h1
      exact (hτpos μ hμs).not_ge h1
    · have := secular_lt_norm_particular_sq hg neg_leftmost_le_shiftThreshold hμs hcons
      have := hτ (mem_Ici.2 le_rfl) hμ hμs.le
      linarith
  · exact (particular_add_of_shifted (hH := hH) hs).2.2.2.2
      (neg_leftmost_le_shiftThreshold.trans_lt hμs)

end Abstract

/-! ### The trust-region subproblem -/

section TrustRegion

variable {Δ μ : ℝ} {s : E}

/-- **Trust-region multipliers lie at or to the right of the threshold**, and the minimizer is the
minimum-norm solution plus a kernel vector (Corollary 8.3.2, (8.3.1)–(8.3.2)): if
`IsTrustRegionMultiplier g H Δ s μ` then `λₛ ≤ μ`, `s - particular hH g μ ∈ ker (H + μ)`,
`⟪g, s - particular hH g μ⟫ = 0`, and `s = particular hH g μ = step g H μ` when `μ > -λ₁`. -/
theorem shiftThreshold_le_of_isTrustRegionMultiplier (h : IsTrustRegionMultiplier g H Δ s μ) :
    shiftThreshold hH ≤ μ ∧
      s - particular hH g μ ∈ LinearMap.ker ((H + μ • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E) ∧
      ⟪g, s - particular hH g μ⟫ = 0 ∧
      (-leftmost hH < μ → s = particular hH g μ ∧ s = step g H μ) := by
  obtain ⟨-, hker, horth, -, hstep⟩ := particular_add_of_shifted (hH := hH) h.shifted
  refine ⟨shiftThreshold_le_of_isPositive h.nonneg h.isPositive, hker, horth, fun hμ => ?_⟩
  rw [(particular_spec (hH := hH) (g := g) μ).2.2 hμ]
  exact ⟨hstep hμ, hstep hμ⟩

/-- For a trust-region multiplier `μ` of a feasible step `s` and `Δ > 0`: `‖s‖² ≤ Δ²`, with
equality when `μ > λₛ`. -/
theorem IsTrustRegionMultiplier.norm_sq_le (h : IsTrustRegionMultiplier g H Δ s μ)
    (hs : ‖s‖ ≤ Δ) : ‖s‖ ^ 2 ≤ Δ ^ 2 ∧ (shiftThreshold hH < μ → ‖s‖ ^ 2 = Δ ^ 2) :=
  ⟨pow_le_pow_left₀ (norm_nonneg _) hs 2, fun hμ => by
    rw [h.norm_eq_of_pos (shiftThreshold_nonneg.trans_lt hμ)]⟩

/-- **The sets `𝓛` and `𝓖` of the trust-region subproblem** (§8.3.2). Let `0 < Δ` and let `s` be a
feasible step with trust-region multiplier `μ` (i.e. a global minimizer, `isMinOn_closedBall_iff`).
Then for every `λ > λₛ`: `Δ² ≤ π(λ) ↔ λ ≤ μ`. So `(λₛ, ∞)` splits into `𝓛 = (λₛ, μ]`, where
`‖s(λ)‖ ≥ Δ`, and `𝓖 = (μ, ∞)`, where `‖s(λ)‖ < Δ`. -/
theorem le_secular_iff_of_trustRegion (hΔ : 0 < Δ) (h : IsTrustRegionMultiplier g H Δ s μ)
    (hs : ‖s‖ ≤ Δ) {lam : ℝ} (hlam : shiftThreshold hH < lam) :
    Δ ^ 2 ≤ secular g H lam ↔ lam ≤ μ :=
  le_secular_iff_of_shifted (τ := fun _ => Δ ^ 2) (fun _ _ _ _ _ => le_rfl)
    (fun _ _ => by positivity) (shiftThreshold_le_of_isTrustRegionMultiplier h).1 h.shifted
    (h.norm_sq_le (hH := hH) hs).1 (fun hμ => ((h.norm_sq_le (hH := hH) hs).2 hμ).ge) hlam

/-- In the easy case `μ > λₛ` of the trust-region subproblem, `μ` is a root of the secular
equation `π(λ) = Δ²` (book §8.3.2), and by `le_secular_iff_of_trustRegion` the only root in
`(λₛ, ∞)`. -/
theorem secular_eq_of_trustRegion (h : IsTrustRegionMultiplier g H Δ s μ)
    (hμ : shiftThreshold hH < μ) : secular g H μ = Δ ^ 2 := by
  have hstep := ((shiftThreshold_le_of_isTrustRegionMultiplier (hH := hH) h).2.2.2
    (neg_leftmost_le_shiftThreshold.trans_lt hμ)).2
  rw [secular, ← hstep, h.norm_eq_of_pos (shiftThreshold_nonneg.trans_lt hμ)]

/-- **Easy/hard case classification for the trust-region subproblem** (§8.3.2, Corollary 8.3.2).
Let `0 < Δ` and `s` a feasible step with trust-region multiplier `μ`. Then `μ = λₛ` iff
`g ⊥ ker (H + λₛ)` and `‖particular hH g λₛ‖ ≤ Δ`: for `λ₁ ≥ 0` (`λₛ = 0`) this is the interior
case `g ∈ range H`, `‖H⁺ g‖ ≤ Δ`; for `λ₁ < 0` it is the hard case. Otherwise `μ > λₛ` and
`s = step g H μ`. -/
theorem multiplier_classification_of_trustRegion (hΔ : 0 < Δ)
    (h : IsTrustRegionMultiplier g H Δ s μ) (hs : ‖s‖ ≤ Δ) :
    (μ = shiftThreshold hH ↔
      g ∈ (LinearMap.ker ((H + shiftThreshold hH • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ ∧
        ‖particular hH g (shiftThreshold hH)‖ ≤ Δ) ∧
    (shiftThreshold hH < μ → s = step g H μ) := by
  have := multiplier_classification (τ := fun _ => Δ ^ 2) (fun _ _ _ _ _ => le_rfl)
    (fun _ _ => by positivity) (shiftThreshold_le_of_isTrustRegionMultiplier (hH := hH) h).1
    h.shifted (h.norm_sq_le (hH := hH) hs).1 fun hμ => ((h.norm_sq_le (hH := hH) hs).2 hμ).ge
  refine ⟨this.1.trans (and_congr_right fun _ => ?_), this.2⟩
  exact pow_le_pow_iff_left₀ (norm_nonneg _) hΔ.le two_ne_zero

/-- **Hard-case solutions of the trust-region subproblem are global minimizers** (sufficiency,
§8.3.2). Let `μ ≥ 0` with `μ ≥ -λ₁`, `g ⊥ ker (H + μ)`, `w ∈ ker (H + μ)`, and suppose the step
`particular hH g μ + w` is feasible and active unless `μ = 0`. Then it is a global minimizer: it
lies in the ball and minimizes the model there. -/
theorem isMinOn_closedBall_of_hardCase {w : E} (hμ0 : 0 ≤ μ) (hμ : -leftmost hH ≤ μ)
    (hg : g ∈ (LinearMap.ker ((H + μ • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ)
    (hw : w ∈ LinearMap.ker ((H + μ • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))
    (hΔ : ‖particular hH g μ + w‖ ≤ Δ) (hact : μ = 0 ∨ ‖particular hH g μ + w‖ = Δ) :
    particular hH g μ + w ∈ Metric.closedBall (0 : E) Δ ∧
      IsMinOn (quadModel g H) (Metric.closedBall 0 Δ) (particular hH g μ + w) := by
  obtain ⟨-, hiff, -, -⟩ := (particular_spec (hH := hH) (g := g) μ).2.1 hg
  have hsol : (H + μ • (1 : E →L[ℝ] E)) (particular hH g μ + w) = -g :=
    (hiff _).2 (by rwa [add_sub_cancel_left])
  refine IsTrustRegionMultiplier.isMinOn_of_norm_le hH
    ⟨hμ0, hsol, isPositive_add_smul_of_le hμ, ?_⟩ hΔ
  rcases hact with h | h
  · rw [h, zero_mul]
  · rw [h, sub_self, mul_zero]

/-- **Optimal value of the trust-region subproblem** ((8.3.5)). If `s` has trust-region
multiplier `μ` then `m(s) = ½ (⟪g, particular hH g μ⟫ - μ Δ²)`. -/
theorem optimalValue_eq_of_trustRegion (h : IsTrustRegionMultiplier g H Δ s μ) :
    quadModel g H s = (1 / 2) * (⟪g, particular hH g μ⟫ - μ * Δ ^ 2) := by
  obtain ⟨-, -, horth, -, -⟩ := particular_add_of_shifted (hH := hH) h.shifted
  have hg : ⟪g, s⟫ = ⟪g, particular hH g μ⟫ := by
    rw [inner_sub_right, sub_eq_zero] at horth; exact horth
  have hc : μ * ‖s‖ ^ 2 = μ * Δ ^ 2 := by
    have := h.complementarity
    have h2 : μ * ‖s‖ = μ * Δ := by linarith [show μ * (‖s‖ - Δ) = μ * ‖s‖ - μ * Δ by ring]
    calc μ * ‖s‖ ^ 2 = (μ * ‖s‖) * ‖s‖ := by ring
      _ = (μ * Δ) * ‖s‖ := by rw [h2]
      _ = Δ * (μ * ‖s‖) := by ring
      _ = μ * Δ ^ 2 := by rw [h2]; ring
  rw [quadModel_eq_of_shifted h.shifted, hg, hc]

end TrustRegion

/-! ### The regularization subproblem -/

section Regularization

variable {σ r : ℝ} {s : E}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The regularization target `τ(λ) = (λ/σ)^{2/(r-2)}` ((8.2.9)) at the multiplier
`λ = σ‖s‖^{r-2}` is `‖s‖²`. -/
theorem norm_sq_eq_rpow (hσ : 0 < σ) (hr : 2 < r) (s : E) :
    ‖s‖ ^ 2 = (σ * ‖s‖ ^ (r - 2) / σ) ^ (2 / (r - 2)) := by
  rw [mul_div_cancel_left₀ _ hσ.ne', ← Real.rpow_mul (norm_nonneg _),
    mul_div_cancel₀ _ (by linarith : r - 2 ≠ 0)]
  norm_cast

/-- The regularization target `λ ↦ (λ/σ)^{2/(r-2)}` is monotone on `λ ≥ 0`. -/
theorem monotoneOn_regTarget (hσ : 0 < σ) (hr : 2 < r) :
    MonotoneOn (fun lam : ℝ => (lam / σ) ^ (2 / (r - 2))) (Ici 0) := fun x hx y _ hxy =>
  Real.rpow_le_rpow (div_nonneg hx hσ.le) (div_le_div_of_nonneg_right hxy hσ.le)
    (div_nonneg zero_le_two (by linarith))

/-- **Regularization multipliers lie at or to the right of the threshold**, and the minimizer is
the minimum-norm solution plus a kernel vector (Corollary 8.3.1, (8.3.1)–(8.3.2)): if `s` globally
minimizes `regModel g H σ r` (`σ > 0`, `r > 2`) and `μ = σ‖s‖^{r-2}`, then `λₛ ≤ μ`,
`s - particular hH g μ ∈ ker (H + μ)`, `⟪g, s - particular hH g μ⟫ = 0`, and
`s = particular hH g μ = step g H μ` when `μ > -λ₁`. -/
theorem shiftThreshold_le_of_isMinOn_regModel (hσ : 0 < σ) (hr : 2 < r)
    (hmin : IsMinOn (regModel g H σ r) univ s) :
    shiftThreshold hH ≤ σ * ‖s‖ ^ (r - 2) ∧
      s - particular hH g (σ * ‖s‖ ^ (r - 2)) ∈
        LinearMap.ker ((H + (σ * ‖s‖ ^ (r - 2)) • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E) ∧
      ⟪g, s - particular hH g (σ * ‖s‖ ^ (r - 2))⟫ = 0 ∧
      (-leftmost hH < σ * ‖s‖ ^ (r - 2) →
        s = particular hH g (σ * ‖s‖ ^ (r - 2)) ∧ s = step g H (σ * ‖s‖ ^ (r - 2))) := by
  obtain ⟨hshift, hpos⟩ := (isMinOn_regModel_iff hH hσ hr).1 hmin
  obtain ⟨-, hker, horth, -, hstep⟩ := particular_add_of_shifted (hH := hH) hshift
  refine ⟨shiftThreshold_le_of_isPositive (by positivity) hpos, hker, horth, fun hμ => ?_⟩
  rw [(particular_spec (hH := hH) (g := g) _).2.2 hμ]
  exact ⟨hstep hμ, hstep hμ⟩

/-- **The sets `𝓛` and `𝓖` of the regularization subproblem** (§8.3.1). Let `σ > 0`, `r > 2`, `s`
a global minimizer of `regModel g H σ r` and `μ = σ‖s‖^{r-2}`. Then for every `λ > λₛ`:
`(λ/σ)^{2/(r-2)} ≤ π(λ) ↔ λ ≤ μ`. So `(λₛ, ∞)` splits into `𝓛 = (λₛ, μ]`, where
`‖s(λ)‖ ≥ (λ/σ)^{1/(r-2)}`, and `𝓖 = (μ, ∞)`. -/
theorem le_secular_iff_of_regularization (hσ : 0 < σ) (hr : 2 < r)
    (hmin : IsMinOn (regModel g H σ r) univ s) {lam : ℝ} (hlam : shiftThreshold hH < lam) :
    (lam / σ) ^ (2 / (r - 2)) ≤ secular g H lam ↔ lam ≤ σ * ‖s‖ ^ (r - 2) :=
  le_secular_iff_of_shifted (τ := fun lam => (lam / σ) ^ (2 / (r - 2)))
    ((monotoneOn_regTarget hσ hr).mono fun _ hx => shiftThreshold_nonneg.trans hx)
    (fun _ hl => Real.rpow_pos_of_pos (div_pos (shiftThreshold_nonneg.trans_lt hl) hσ) _)
    (shiftThreshold_le_of_isMinOn_regModel (hH := hH) hσ hr hmin).1
    ((isMinOn_regModel_iff hH hσ hr).1 hmin).1 (norm_sq_eq_rpow hσ hr s).le
    (fun _ => (norm_sq_eq_rpow hσ hr s).ge) hlam

/-- In the easy case `μ > λₛ` of the regularization subproblem, `μ = σ‖s‖^{r-2}` is a root of the
secular equation `π(λ) = (λ/σ)^{2/(r-2)}` ((8.2.42), §8.3.1), and by
`le_secular_iff_of_regularization` the only root in `(λₛ, ∞)`. -/
theorem secular_eq_of_regularization (hσ : 0 < σ) (hr : 2 < r)
    (hmin : IsMinOn (regModel g H σ r) univ s) (hμ : shiftThreshold hH < σ * ‖s‖ ^ (r - 2)) :
    secular g H (σ * ‖s‖ ^ (r - 2)) = (σ * ‖s‖ ^ (r - 2) / σ) ^ (2 / (r - 2)) := by
  have hstep := ((shiftThreshold_le_of_isMinOn_regModel (hH := hH) hσ hr hmin).2.2.2
    (neg_leftmost_le_shiftThreshold.trans_lt hμ)).2
  rw [secular, ← hstep, norm_sq_eq_rpow hσ hr s]

/-- **Easy/hard case classification for the regularization subproblem** (§8.3.1,
Corollary 8.3.1). Let `σ > 0`, `r > 2`, `s` a global minimizer and `μ = σ‖s‖^{r-2}`. Then
`μ = λₛ` iff `g ⊥ ker (H + λₛ)` and `‖particular hH g λₛ‖² ≤ (λₛ/σ)^{2/(r-2)}`: for `λ₁ ≥ 0`
(`λₛ = 0`) this says `g = 0`; for `λ₁ < 0` it is the hard case. Otherwise `μ > λₛ` and
`s = step g H μ`. -/
theorem multiplier_classification_of_regularization (hσ : 0 < σ) (hr : 2 < r)
    (hmin : IsMinOn (regModel g H σ r) univ s) :
    (σ * ‖s‖ ^ (r - 2) = shiftThreshold hH ↔
      g ∈ (LinearMap.ker ((H + shiftThreshold hH • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ ∧
        ‖particular hH g (shiftThreshold hH)‖ ^ 2 ≤ (shiftThreshold hH / σ) ^ (2 / (r - 2))) ∧
    (shiftThreshold hH < σ * ‖s‖ ^ (r - 2) → s = step g H (σ * ‖s‖ ^ (r - 2))) :=
  multiplier_classification (τ := fun lam => (lam / σ) ^ (2 / (r - 2)))
    ((monotoneOn_regTarget hσ hr).mono fun _ hx => shiftThreshold_nonneg.trans hx)
    (fun _ hl => Real.rpow_pos_of_pos (div_pos (shiftThreshold_nonneg.trans_lt hl) hσ) _)
    (shiftThreshold_le_of_isMinOn_regModel (hH := hH) hσ hr hmin).1
    ((isMinOn_regModel_iff hH hσ hr).1 hmin).1 (norm_sq_eq_rpow hσ hr s).le
    fun _ => (norm_sq_eq_rpow hσ hr s).ge

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- If `‖s‖² = (μ/σ)^{2/(r-2)}` with `μ ≥ 0` then `σ‖s‖^{r-2} = μ`. -/
theorem mul_norm_rpow_eq_of_norm_sq_eq (hσ : 0 < σ) (hr : 2 < r) {μ : ℝ} (hμ : 0 ≤ μ)
    (h : ‖s‖ ^ 2 = (μ / σ) ^ (2 / (r - 2))) : σ * ‖s‖ ^ (r - 2) = μ := by
  have hr2 : r - 2 ≠ 0 := by linarith
  have h1 : ‖s‖ ^ (r - 2) = (‖s‖ ^ 2) ^ ((r - 2) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]; congr 1; push_cast; ring
  have he : 2 / (r - 2) * ((r - 2) / 2) = 1 := by field_simp
  rw [h1, h, ← Real.rpow_mul (div_nonneg hμ hσ.le), he, Real.rpow_one, mul_div_cancel₀ _ hσ.ne']

/-- **Hard-case solutions of the regularization subproblem are global minimizers** (sufficiency,
§8.3.1). Let `μ ≥ 0` with `μ ≥ -λ₁`, `g ⊥ ker (H + μ)`, `w ∈ ker (H + μ)` and
`‖particular hH g μ + w‖² = (μ/σ)^{2/(r-2)}`. Then `particular hH g μ + w` minimizes
`regModel g H σ r`. -/
theorem isMinOn_regModel_of_hardCase (hσ : 0 < σ) (hr : 2 < r) {μ : ℝ} {w : E} (hμ0 : 0 ≤ μ)
    (hμ : -leftmost hH ≤ μ)
    (hg : g ∈ (LinearMap.ker ((H + μ • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ)
    (hw : w ∈ LinearMap.ker ((H + μ • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))
    (hnorm : ‖particular hH g μ + w‖ ^ 2 = (μ / σ) ^ (2 / (r - 2))) :
    IsMinOn (regModel g H σ r) univ (particular hH g μ + w) := by
  obtain ⟨-, hiff, -, -⟩ := (particular_spec (hH := hH) (g := g) μ).2.1 hg
  have hsol : (H + μ • (1 : E →L[ℝ] E)) (particular hH g μ + w) = -g :=
    (hiff _).2 (by rwa [add_sub_cancel_left])
  rw [isMinOn_regModel_iff hH hσ hr, mul_norm_rpow_eq_of_norm_sq_eq hσ hr hμ0 hnorm]
  exact ⟨hsol, isPositive_add_smul_of_le hμ⟩

/-- **Optimal value of the regularization subproblem** ((8.3.3)). If `s` globally minimizes
`regModel g H σ r` (`σ > 0`, `r > 2`) and `μ = σ‖s‖^{r-2}`, then
`m^R(s) = ½ (⟪g, particular hH g μ⟫ - ((r-2)/r) μ (μ/σ)^{2/(r-2)})`. -/
theorem optimalValue_eq_of_regularization (hσ : 0 < σ) (hr : 2 < r)
    (hmin : IsMinOn (regModel g H σ r) univ s) :
    regModel g H σ r s = (1 / 2) * (⟪g, particular hH g (σ * ‖s‖ ^ (r - 2))⟫ -
      ((r - 2) / r) * (σ * ‖s‖ ^ (r - 2)) * (σ * ‖s‖ ^ (r - 2) / σ) ^ (2 / (r - 2))) := by
  have hshift := ((isMinOn_regModel_iff hH hσ hr).1 hmin).1
  obtain ⟨-, -, horth, -, -⟩ := particular_add_of_shifted (hH := hH) hshift
  have hg : ⟪g, s⟫ = ⟪g, particular hH g (σ * ‖s‖ ^ (r - 2))⟫ := by
    rw [inner_sub_right, sub_eq_zero] at horth; exact horth
  rw [regModel_eq_of_shifted (by linarith) hshift, hg, ← norm_sq_eq_rpow hσ hr s]

end Regularization

/-! ### Existence of hard-case solutions -/

omit [FiniteDimensional ℝ E] in
/-- **The roots `α` of the hard case.** If `p ⊥ v`, `v ≠ 0` and `‖p‖² ≤ t`, then
`‖p + α v‖² = t` for `α = ±√(t - ‖p‖²) / ‖v‖`; in particular some `α` works. Applied with
`p = sₛ = particular hH g (-λ₁)` and an eigenvector `v = v₁` for `λ₁`, which is orthogonal to `sₛ`
by `particular_spec`, this produces the hard-case solutions `sₛ + α v₁` of §8.3. -/
theorem exists_norm_particular_add_smul_eq {p v : E} (hpv : ⟪p, v⟫ = 0) (hv : v ≠ 0) {t : ℝ}
    (ht : ‖p‖ ^ 2 ≤ t) :
    ∃ α : ℝ, ‖p + α • v‖ ^ 2 = t ∧ ‖p - α • v‖ ^ 2 = t := by
  have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
  have key : ∀ β : ℝ, ‖p + β • v‖ ^ 2 = ‖p‖ ^ 2 + β ^ 2 * ‖v‖ ^ 2 := fun β => by
    rw [norm_add_sq_real, inner_smul_right, hpv, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  set α := √(t - ‖p‖ ^ 2) / ‖v‖
  have hα : α ^ 2 * ‖v‖ ^ 2 = t - ‖p‖ ^ 2 := by
    rw [div_pow, Real.sq_sqrt (sub_nonneg.2 ht)]
    field_simp
  refine ⟨α, ?_, ?_⟩
  · rw [key, hα]; ring
  · rw [sub_eq_add_neg, ← neg_smul, key, neg_sq, hα]; ring

end Subproblem

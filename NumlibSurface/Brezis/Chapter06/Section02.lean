import Numlib.Analysis.Normed.Operator.Compact.Banach
import Numlib.Variational.WeakMinimization
import NumlibSurface.Brezis.Chapter03.Section05

/-!
# Brezis §6.2: the Riesz–Fredholm theory

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §6.2, over a real normed (Lemma 6.1, Theorem 6.5) or
Banach (Theorem 6.6) space `E`. Riesz's lemma and Riesz's theorem are Mathlib's
(`riesz_lemma_of_lt_one`, `FiniteDimensional.of_isCompact_closedBall₀`); the Fredholm
alternative for `I - T`, `T` compact, delegates clause by clause to the backbone
`Numlib/Analysis/Normed/Operator/Compact/Banach` (and `…/Riesz`), which states its results for
`μ • 1 - T` with `μ ≠ 0` — every node here is the instance `μ = 1`, rewritten by `one_smul`.
The book's `I - T` is `(1 : E →L[ℝ] E) - T`; the adjoint `T*` is chapter 2's
`ContinuousLinearMap.strongDualMap T`, and `N(I - T*)^⊥ ⊆ E` is chapter 1's
`Submodule.strongDualCoannihilator` of the kernel. The unnumbered claim of the Comments that
`I - T` is a Fredholm operator of index zero is stated here as well, in Mathlib's
`ContinuousLinearMap.IsFredholm` and `LinearMap.index`.

## Main results

* `lemma_6_1`, `remark_6_3`, `remark_6_3_reflexive` — Riesz's lemma, and the case `ε = 0` for
  a finite-dimensional or (more generally) a reflexive subspace.
* `theorem_6_5` — Riesz's theorem: a normed space with compact unit ball is finite dimensional.
* `theorem_6_6_a`, `theorem_6_6_b_isClosed`, `theorem_6_6_b`, `theorem_6_6_c`, `theorem_6_6_d`
  — the Fredholm alternative: `N(I - T)` is finite dimensional, `R(I - T) = N(I - T*)^⊥` is
  closed, `I - T` is injective iff surjective, and `dim N(I - T) = dim N(I - T*)`.
* `remark_6_4`, `remark_6_5` — the alternative as a dichotomy for the equation `u - T u = f`,
  and the finite-dimensional fact behind (c).
* `oneSubCompact_isFredholm_index_zero` — `I - T` is a Fredholm operator of index zero
  (Comments on Chapter 6, 1).
-/

open Metric

noncomputable section

namespace Brezis.Chapter06

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Riesz's lemma and Riesz's theorem -/

/-- **Lemma 6.1 (Riesz's lemma).** Let `E` be a normed space and `M ⊆ E` a closed linear
subspace with `M ≠ E`. Then for every `ε > 0` there is `u ∈ E` with `‖u‖ = 1` and
`dist (u, M) ≥ 1 - ε`. -/
theorem lemma_6_1 {M : Submodule ℝ E} (hM : IsClosed (M : Set E)) (hne : M ≠ ⊤) {ε : ℝ}
    (hε : 0 < ε) : ∃ u : E, ‖u‖ = 1 ∧ 1 - ε ≤ infDist u M := by
  obtain ⟨x, -, hx⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.2 hne)
  obtain ⟨u, -, hu1, hu⟩ := riesz_lemma_of_lt_one (𝕜 := ℝ) hM ⟨x, hx⟩ (by linarith : 1 - ε < 1)
  refine ⟨u, hu1, (le_infDist ⟨0, M.zero_mem⟩).2 fun y hy => ?_⟩
  rw [dist_eq_norm]
  exact hu y hy

/-- The normalization step of the proof of Lemma 6.1, with `ε = 0`: if the distance from
`v ∉ M` to the subspace `M` is attained at `m₀ ∈ M`, then `u = (v - m₀) / ‖v - m₀‖` has
`‖u‖ = 1` and `dist (u, M) = 1`, because `m₀ + ‖v - m₀‖ m ∈ M` for every `m ∈ M`. -/
private theorem exists_norm_eq_one_infDist_eq_one_of_isBestApprox {M : Submodule ℝ E} {v m₀ : E}
    (hv : v ∉ M) (hm₀ : IsBestApprox (M : Set E) v m₀) :
    ∃ u : E, ‖u‖ = 1 ∧ infDist u M = 1 := by
  have hne : v - m₀ ≠ 0 := fun h => hv (by rw [sub_eq_zero.1 h]; exact hm₀.1)
  have hpos : 0 < ‖v - m₀‖ := norm_pos_iff.2 hne
  have hu1 : ‖‖v - m₀‖⁻¹ • (v - m₀)‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos.ne']
  refine ⟨‖v - m₀‖⁻¹ • (v - m₀), hu1, le_antisymm ?_ ?_⟩
  · calc infDist (‖v - m₀‖⁻¹ • (v - m₀)) M ≤ dist (‖v - m₀‖⁻¹ • (v - m₀)) 0 :=
        infDist_le_dist_of_mem M.zero_mem
      _ = 1 := by rw [dist_zero_right, hu1]
  · refine (le_infDist ⟨0, M.zero_mem⟩).2 fun m hm => ?_
    have hmem : m₀ + ‖v - m₀‖ • m ∈ M := M.add_mem hm₀.1 (M.smul_mem _ hm)
    have hd : ‖v - m₀‖ ≤ ‖v - (m₀ + ‖v - m₀‖ • m)‖ := hm₀.2 _ hmem
    have hrw : ‖v - m₀‖⁻¹ • (v - m₀) - m = ‖v - m₀‖⁻¹ • (v - (m₀ + ‖v - m₀‖ • m)) := by
      rw [smul_sub, smul_sub, smul_add, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul, sub_sub]
    rw [dist_eq_norm, hrw, norm_smul, norm_inv, norm_norm, ← div_eq_inv_mul,
      le_div_iff₀ hpos, one_mul]
    exact hd

/-- **Remark 3, the finite-dimensional case.** If `M` is finite dimensional (and `M ≠ E`) one
can choose `ε = 0` in Lemma 6.1: there is `u` with `‖u‖ = 1` and `dist (u, M) = 1`, since the
distance to `M` is attained. -/
theorem remark_6_3 (M : Submodule ℝ E) [FiniteDimensional ℝ M] (hne : M ≠ ⊤) :
    ∃ u : E, ‖u‖ = 1 ∧ infDist u M = 1 := by
  obtain ⟨v, -, hv⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.2 hne)
  obtain ⟨m₀, hm₀⟩ := exists_isBestApprox_of_finiteDimensional M v
  exact exists_norm_eq_one_infDist_eq_one_of_isBestApprox hv hm₀

/-- **Remark 3, the reflexive case.** If `M ⊆ E` is a reflexive subspace (chapter 3's
`IsReflexive`, for `M` as a normed space; in particular a closed subspace of a reflexive Banach
space, by Proposition 3.20) with `M ≠ E`, one can choose `ε = 0` in Lemma 6.1: the distance to
`M` is attained, by the direct method of the calculus of variations in `M` (bounded sequences of
`M` have weakly convergent subsequences, and the norm is weakly lower semicontinuous). "But this
is not true in general (see Exercise 1.17)." -/
theorem remark_6_3_reflexive {M : Submodule ℝ E} (hM : Brezis.Chapter03.IsReflexive M)
    (hne : M ≠ ⊤) : ∃ u : E, ‖u‖ = 1 ∧ infDist u M = 1 := by
  have := Brezis.Chapter03.isReflexive_iff.1 hM
  obtain ⟨v, -, hv⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.2 hne)
  -- the distance from `v` to `M` is attained: minimize the convex, continuous, coercive
  -- functional `m ↦ ‖v - m‖` on the reflexive space `M`
  have hconv : ConvexOn ℝ (Set.univ : Set M) fun m : M => ‖v - (m : E)‖ := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    have hcomb : a • (v - (x : E)) + b • (v - (y : E)) = v - ((a • x + b • y : M) : E) := by
      rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, smul_sub, smul_sub,
        ← add_sub_add_comm, ← add_smul, hab, one_smul]
    calc ‖v - ((a • x + b • y : M) : E)‖ = ‖a • (v - (x : E)) + b • (v - (y : E))‖ := by
          rw [hcomb]
      _ ≤ ‖a • (v - (x : E))‖ + ‖b • (v - (y : E))‖ := norm_add_le _ _
      _ = a • ‖v - (x : E)‖ + b • ‖v - (y : E)‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb, smul_eq_mul,
            smul_eq_mul]
  have hcont : Continuous fun m : M => ‖v - (m : E)‖ :=
    (continuous_const.sub continuous_subtype_val).norm
  have hcoer : IsCoerciveFunctionalOn (fun m : M => ‖v - (m : E)‖) Set.univ := fun C =>
    ⟨C + ‖v‖, fun m _ hm => by
      have h := norm_sub_norm_le (m : E) v
      rw [norm_sub_rev, Submodule.norm_coe] at h
      linarith⟩
  obtain ⟨m₀, -, hm₀⟩ := exists_isMinOn_of_convexOn Set.univ_nonempty isClosed_univ convex_univ
    hconv hcont.continuousOn.lowerSemicontinuousOn (Or.inr hcoer)
  refine exists_norm_eq_one_infDist_eq_one_of_isBestApprox hv ⟨m₀.2, fun w hw => ?_⟩
  exact isMinOn_iff.1 hm₀ ⟨w, hw⟩ (Set.mem_univ _)

/-- **Theorem 6.5 (Riesz).** Let `E` be a normed space with `B_E` compact. Then `E` is finite
dimensional. -/
theorem theorem_6_5 (h : IsCompact (closedBall (0 : E) 1)) : FiniteDimensional ℝ E :=
  FiniteDimensional.of_isCompact_closedBall₀ ℝ one_pos h

/-! ### The Fredholm alternative -/

variable [CompleteSpace E]

omit [CompleteSpace E] in
/-- **Theorem 6.6 (a).** Let `T ∈ K(E)`. Then `N(I - T)` is finite dimensional. -/
theorem theorem_6_6_a {T : E →L[ℝ] E} (hT : IsCompactOperator T) :
    FiniteDimensional ℝ ((1 : E →L[ℝ] E) - T).ker := by
  have := hT.finiteDimensional_ker_pow one_ne_zero 1
  rwa [one_smul, pow_one] at this

omit [CompleteSpace E] in
/-- **Theorem 6.6 (b), first clause.** For `T ∈ K(E)`, `R(I - T)` is closed. -/
theorem theorem_6_6_b_isClosed {T : E →L[ℝ] E} (hT : IsCompactOperator T) :
    IsClosed (((1 : E →L[ℝ] E) - T).range : Set E) := by
  have := hT.isClosed_range_smul_sub one_ne_zero
  rwa [one_smul] at this

omit [CompleteSpace E] in
/-- **Theorem 6.6 (b), "and more precisely `R(I - T) = N(I - T*)^⊥`".** For `T ∈ K(E)`, the
range of `I - T` is the set of `f ∈ E` annihilated by every `v ∈ N(I - T*)`, the kernel of
`I - T*` in `E*`. -/
theorem theorem_6_6_b {T : E →L[ℝ] E} (hT : IsCompactOperator T) :
    ((1 : E →L[ℝ] E) - T).range =
      ((1 : StrongDual ℝ E →L[ℝ] StrongDual ℝ E) -
        T.strongDualMap).ker.strongDualCoannihilator := by
  have := hT.range_smul_one_sub_eq_strongDualCoannihilator_ker_strongDualMap one_ne_zero
  rwa [one_smul, one_smul] at this

/-- **Theorem 6.6 (c).** For `T ∈ K(E)`, `N(I - T) = {0}` iff `R(I - T) = E`. -/
theorem theorem_6_6_c {T : E →L[ℝ] E} (hT : IsCompactOperator T) :
    ((1 : E →L[ℝ] E) - T).ker = ⊥ ↔ ((1 : E →L[ℝ] E) - T).range = ⊤ := by
  have := hT.injective_iff_surjective_smul_one_sub one_ne_zero
  rw [one_smul] at this
  rw [LinearMap.ker_eq_bot, LinearMap.range_eq_top, ContinuousLinearMap.coe_coe]
  exact this

/-- **Theorem 6.6 (d).** For `T ∈ K(E)`, `dim N(I - T) = dim N(I - T*)`. -/
theorem theorem_6_6_d {T : E →L[ℝ] E} (hT : IsCompactOperator T) :
    Module.finrank ℝ ((1 : E →L[ℝ] E) - T).ker =
      Module.finrank ℝ ((1 : StrongDual ℝ E →L[ℝ] StrongDual ℝ E) - T.strongDualMap).ker := by
  have := hT.finrank_ker_smul_one_sub_eq_finrank_ker_strongDualMap one_ne_zero
  rwa [one_smul, one_smul] at this

/-- **Remark 4, the Fredholm alternative as a dichotomy.** For `T ∈ K(E)`: either for every
`f ∈ E` the equation `u - T u = f` has a unique solution, or the homogeneous equation
`u - T u = 0` admits `n = dim N(I - T) > 0` linearly independent solutions, and then the
inhomogeneous equation `u - T u = f` is solvable iff `f` satisfies the `n` orthogonality
conditions `f ∈ N(I - T*)^⊥`. -/
theorem remark_6_4 {T : E →L[ℝ] E} (hT : IsCompactOperator T) :
    (∀ f : E, ∃! u, u - T u = f) ∨
      (0 < Module.finrank ℝ ((1 : E →L[ℝ] E) - T).ker ∧
        ∀ f : E, (∃ u, u - T u = f) ↔
          f ∈ ((1 : StrongDual ℝ E →L[ℝ] StrongDual ℝ E) -
            T.strongDualMap).ker.strongDualCoannihilator) := by
  have happly : ∀ u, ((1 : E →L[ℝ] E) - T) u = u - T u := fun u => by
    rw [sub_apply, one_apply_eq_self]
  by_cases hker : ((1 : E →L[ℝ] E) - T).ker = ⊥
  · left
    have hinj : Function.Injective ((1 : E →L[ℝ] E) - T) :=
      LinearMap.ker_eq_bot.1 hker
    have hsurj : Function.Surjective ((1 : E →L[ℝ] E) - T) :=
      LinearMap.range_eq_top.1 ((theorem_6_6_c hT).1 hker)
    intro f
    obtain ⟨u, hu⟩ := hsurj f
    have hu' : u - T u = f := by rw [← happly]; exact hu
    exact ⟨u, hu', fun w hw =>
      hinj (by rw [happly, happly]; exact (show w - T w = f from hw).trans hu'.symm)⟩
  · right
    have := theorem_6_6_a hT
    refine ⟨Nat.pos_of_ne_zero fun h => hker (Submodule.finrank_eq_zero.1 h), fun f => ?_⟩
    rw [← theorem_6_6_b hT, LinearMap.mem_range]
    simp only [ContinuousLinearMap.coe_coe, happly]

omit [CompleteSpace E] in
/-- **Remark 5.** Property (c) is familiar in finite-dimensional spaces: if `dim E < ∞`, a
linear operator from `E` into itself is injective iff it is surjective. (In infinite dimension
a bounded operator may be injective without being surjective, e.g. the right shift on `ℓ²`,
`remark_6_6_rightShift` in §6.3; so (c) is a remarkable property of the operators `I - T`,
`T ∈ K(E)`.) -/
theorem remark_6_5 [FiniteDimensional ℝ E] (A : E →L[ℝ] E) :
    Function.Injective A ↔ Function.Surjective A :=
  LinearMap.injective_iff_surjective (f := (A : E →ₗ[ℝ] E))

/-- **Comments on Chapter 6, 1**: "`A = I - T` with `T ∈ K(E)` is a Fredholm operator of index
zero; this follows from Theorem 6.6". In Mathlib's vocabulary, `ContinuousLinearMap.IsFredholm`
(finite-dimensional kernel, closed range of finite codimension, plus the automatically satisfied
strictness and complemented-kernel fields) and `LinearMap.index = dim N(A) - codim R(A)`. -/
theorem oneSubCompact_isFredholm_index_zero {T : E →L[ℝ] E} (hT : IsCompactOperator T) :
    ((1 : E →L[ℝ] E) - T).IsFredholm ∧ ((1 : E →L[ℝ] E) - T).index = 0 := by
  have h1 := hT.isFredholm_smul_one_sub one_ne_zero
  have h2 := hT.index_smul_one_sub one_ne_zero
  rw [one_smul] at h1 h2
  exact ⟨h1, h2⟩

end Brezis.Chapter06

end

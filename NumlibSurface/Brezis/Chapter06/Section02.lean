/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Normed.Operator.Compact.Banach
import Numlib.Variational.WeakMinimization
import NumlibSurface.Brezis.Chapter03.Section05

/-!
# Brezis, Section 6.2: The Riesz–Fredholm theory

This module formalizes Section 6.2 of [brezis2011functional] for a real normed space $E$, which is a
Banach space where a statement needs it. Riesz's lemma gives, for a closed subspace $M \neq E$ and
$\varepsilon > 0$, a unit vector at distance at least $1 - \varepsilon$ from $M$ (Lemma 6.1). It
follows that a normed space with compact closed unit ball is finite dimensional (Theorem 6.5,
Riesz). For a compact operator $T \in \mathcal{K}(E)$ the Fredholm alternative holds (Theorem 6.6):
$N(I - T)$ is finite dimensional, $R(I - T) = N(I - T^\star)^\perp$ is closed, $I - T$ is injective
if and only if it is surjective, and $\dim N(I - T) = \dim N(I - T^\star)$. In particular $I - T$ is
a Fredholm operator of index zero.

Riesz's lemma and Riesz's theorem are Mathlib's `riesz_lemma_of_lt_one` and
`FiniteDimensional.of_isCompact_closedBall₀`. The Fredholm alternative specializes the backbone
modules `Numlib.Analysis.Normed.Operator.Compact.Banach` and
`Numlib.Analysis.Normed.Operator.Riesz`, which state their results for $\mu I - T$ with
$\mu \neq 0$; every result here is the case $\mu = 1$.

## Main results

* Lemma 6.1, `Brezis.Chapter06.lemma_6_1` (Riesz's lemma): for a closed subspace $M \neq E$ and
  $\varepsilon > 0$ there is $u$ with $\|u\| = 1$ and
  $\operatorname{dist}(u, M) \ge 1 - \varepsilon$.
* Remark 3, `Brezis.Chapter06.remark_6_3`: one can take $\varepsilon = 0$ if $M$ is finite
  dimensional.
* Remark 3, `Brezis.Chapter06.remark_6_3_reflexive`: one can take $\varepsilon = 0$ if $M$ is
  reflexive.
* Theorem 6.5, `Brezis.Chapter06.theorem_6_5` (Riesz): a normed space with compact closed unit ball
  is finite dimensional.
* Theorem 6.6(a), `Brezis.Chapter06.theorem_6_6_a`: $N(I - T)$ is finite dimensional.
* Theorem 6.6(b), `Brezis.Chapter06.theorem_6_6_b_isClosed` and `Brezis.Chapter06.theorem_6_6_b`:
  $R(I - T)$ is closed and equals $N(I - T^\star)^\perp$.
* Theorem 6.6(c), `Brezis.Chapter06.theorem_6_6_c`: $N(I - T) = \{0\}$ if and only if
  $R(I - T) = E$.
* Theorem 6.6(d), `Brezis.Chapter06.theorem_6_6_d`: $\dim N(I - T) = \dim N(I - T^\star)$.
* Remark 4, `Brezis.Chapter06.remark_6_4`: the Fredholm alternative as a dichotomy for the equation
  $u - Tu = f$.
* Remark 5, `Brezis.Chapter06.remark_6_5`: in finite dimension a linear operator is injective if and
  only if it is surjective.
* Comments on Chapter 6, item 1, `Brezis.Chapter06.oneSubCompact_isFredholm_index_zero`: $I - T$ is
  a Fredholm operator of index zero.

## Conventions

* The operator $I - T$ is `(1 : E →L[ℝ] E) - T`.
* The adjoint $T^\star$ is `ContinuousLinearMap.strongDualMap T`, as in Chapter 2.
* For a subspace $N$ of $E^\star$, the orthogonal $N^\perp \subseteq E$ is
  `Submodule.strongDualCoannihilator N`, as in Chapter 1.

## Deviations from the source

* **Theorem 6.6(a) and (b)** (generalization). The source assumes that $E$ is a Banach space. Parts
  (a) and (b) are proved for every normed space. See `Brezis.Chapter06.theorem_6_6_a`,
  `Brezis.Chapter06.theorem_6_6_b_isClosed` and `Brezis.Chapter06.theorem_6_6_b`.
-/

open Metric

noncomputable section

namespace Brezis.Chapter06

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Riesz's lemma and Riesz's theorem -/

/-- **Lemma 6.1** of [brezis2011functional] (Riesz's lemma). Let $E$ be a normed space and let
$M \subseteq E$ be a closed linear subspace with $M \neq E$. Then for every $\varepsilon > 0$
there is $u \in E$ with $\|u\| = 1$ and $\operatorname{dist}(u, M) \ge 1 - \varepsilon$. -/
theorem lemma_6_1 {M : Submodule ℝ E} (hM : IsClosed (M : Set E)) (hne : M ≠ ⊤) {ε : ℝ}
    (hε : 0 < ε) : ∃ u : E, ‖u‖ = 1 ∧ 1 - ε ≤ infDist u M := by
  obtain ⟨x, -, hx⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.2 hne)
  obtain ⟨u, -, hu1, hu⟩ := riesz_lemma_of_lt_one (𝕜 := ℝ) hM ⟨x, hx⟩ (by linarith : 1 - ε < 1)
  refine ⟨u, hu1, (le_infDist ⟨0, M.zero_mem⟩).2 fun y hy => ?_⟩
  rw [dist_eq_norm]
  exact hu y hy

/-- If $v \notin M$ and the distance from $v$ to the subspace $M$ is attained at $m_0 \in M$, then
$u = (v - m_0)/\|v - m_0\|$ has $\|u\| = 1$ and $\operatorname{dist}(u, M) = 1$. -/
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

/-- **Remark 3** in Chapter 6 of [brezis2011functional], the finite-dimensional case. Let $E$ be a
normed space and let $M$ be a finite-dimensional subspace with $M \neq E$. Then one can take
$\varepsilon = 0$ in Lemma 6.1: there is $u \in E$ with $\|u\| = 1$ and
$\operatorname{dist}(u, M) = 1$.

The proof uses that the distance from a point to $M$ is attained. -/
theorem remark_6_3 (M : Submodule ℝ E) [FiniteDimensional ℝ M] (hne : M ≠ ⊤) :
    ∃ u : E, ‖u‖ = 1 ∧ infDist u M = 1 := by
  obtain ⟨v, -, hv⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.2 hne)
  obtain ⟨m₀, hm₀⟩ := exists_isBestApprox_of_finiteDimensional M v
  exact exists_norm_eq_one_infDist_eq_one_of_isBestApprox hv hm₀

/-- **Remark 3** in Chapter 6 of [brezis2011functional], the reflexive case. Let $E$ be a normed
space and let $M$ be a subspace with $M \neq E$ that is reflexive as a normed space. Then one
can take $\varepsilon = 0$ in Lemma 6.1: there is $u \in E$ with $\|u\| = 1$ and
$\operatorname{dist}(u, M) = 1$.

Reflexivity is `Brezis.Chapter03.IsReflexive` for $M$. A closed subspace of a reflexive Banach
space is reflexive (Proposition 3.20 of the source). The distance from a point to $M$ is
attained by the direct method of the calculus of variations in $M$: bounded sequences of $M$
have weakly convergent subsequences, and the norm is weakly lower semicontinuous. The source
adds that the statement "is not true in general (see Exercise 1.17)". -/
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

/-- **Theorem 6.5** of [brezis2011functional] (Riesz). Let $E$ be a normed space whose closed unit
ball $B_E$ is compact. Then $E$ is finite dimensional. -/
theorem theorem_6_5 (h : IsCompact (closedBall (0 : E) 1)) : FiniteDimensional ℝ E :=
  FiniteDimensional.of_isCompact_closedBall₀ ℝ one_pos h

/-! ### The Fredholm alternative -/

variable [CompleteSpace E]

omit [CompleteSpace E] in
/-- **Theorem 6.6(a)** of [brezis2011functional]. Let $E$ be a normed space and let
$T \in \mathcal{K}(E)$. Then $N(I - T)$ is finite dimensional.

**Generalization.** The source assumes that $E$ is a Banach space. The statement holds for every
normed space. -/
theorem theorem_6_6_a {T : E →L[ℝ] E} (hT : IsCompactOperator T) :
    FiniteDimensional ℝ ((1 : E →L[ℝ] E) - T).ker := by
  have := hT.finiteDimensional_ker_pow one_ne_zero 1
  rwa [one_smul, pow_one] at this

omit [CompleteSpace E] in
/-- **Theorem 6.6(b)** of [brezis2011functional], closedness. Let $E$ be a normed space and let
$T \in \mathcal{K}(E)$. Then the range $R(I - T)$ is closed.

**Generalization.** The source assumes that $E$ is a Banach space. The statement holds for every
normed space. -/
theorem theorem_6_6_b_isClosed {T : E →L[ℝ] E} (hT : IsCompactOperator T) :
    IsClosed (((1 : E →L[ℝ] E) - T).range : Set E) := by
  have := hT.isClosed_range_smul_sub one_ne_zero
  rwa [one_smul] at this

omit [CompleteSpace E] in
/-- **Theorem 6.6(b)** of [brezis2011functional], the range. Let $E$ be a normed space and let
$T \in \mathcal{K}(E)$. Then
$$R(I - T) = N(I - T^\star)^\perp,$$
that is, $f \in E$ lies in the range of $I - T$ if and only if $\langle v, f \rangle = 0$ for
every $v \in E^\star$ with $v - T^\star v = 0$.

**Generalization.** The source assumes that $E$ is a Banach space. The statement holds for every
normed space.

The source writes this as "more precisely $R(I - T) = N(I - T^\star)^\perp$". The orthogonal is
`Submodule.strongDualCoannihilator`. -/
theorem theorem_6_6_b {T : E →L[ℝ] E} (hT : IsCompactOperator T) :
    ((1 : E →L[ℝ] E) - T).range =
      ((1 : StrongDual ℝ E →L[ℝ] StrongDual ℝ E) -
        T.strongDualMap).ker.strongDualCoannihilator := by
  have := hT.range_smul_one_sub_eq_strongDualCoannihilator_ker_strongDualMap one_ne_zero
  rwa [one_smul, one_smul] at this

/-- **Theorem 6.6(c)** of [brezis2011functional]. Let $E$ be a Banach space and let
$T \in \mathcal{K}(E)$. Then $N(I - T) = \{0\}$ if and only if $R(I - T) = E$. -/
theorem theorem_6_6_c {T : E →L[ℝ] E} (hT : IsCompactOperator T) :
    ((1 : E →L[ℝ] E) - T).ker = ⊥ ↔ ((1 : E →L[ℝ] E) - T).range = ⊤ := by
  have := hT.injective_iff_surjective_smul_one_sub one_ne_zero
  rw [one_smul] at this
  rw [LinearMap.ker_eq_bot, LinearMap.range_eq_top, ContinuousLinearMap.coe_coe]
  exact this

/-- **Theorem 6.6(d)** of [brezis2011functional]. Let $E$ be a Banach space and let
$T \in \mathcal{K}(E)$. Then
$$\dim N(I - T) = \dim N(I - T^\star).$$

The dimensions are `Module.finrank`. Both kernels are finite dimensional, so no value of
`Module.finrank` at an infinite-dimensional space enters. -/
theorem theorem_6_6_d {T : E →L[ℝ] E} (hT : IsCompactOperator T) :
    Module.finrank ℝ ((1 : E →L[ℝ] E) - T).ker =
      Module.finrank ℝ ((1 : StrongDual ℝ E →L[ℝ] StrongDual ℝ E) - T.strongDualMap).ker := by
  have := hT.finrank_ker_smul_one_sub_eq_finrank_ker_strongDualMap one_ne_zero
  rwa [one_smul, one_smul] at this

/-- **Remark 4** in Chapter 6 of [brezis2011functional], the Fredholm alternative. Let $E$ be a
Banach space and let $T \in \mathcal{K}(E)$. Then one of the following holds:

* for every $f \in E$ the equation $u - Tu = f$ has a unique solution $u \in E$;
* the homogeneous equation $u - Tu = 0$ has $n = \dim N(I - T) > 0$ linearly independent
  solutions, and the equation $u - Tu = f$ has a solution if and only if $f$ satisfies the $n$
  orthogonality conditions $f \in N(I - T^\star)^\perp$. -/
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
/-- **Remark 5** in Chapter 6 of [brezis2011functional]. Let $E$ be a finite-dimensional normed
space. Then a linear operator $A \in \mathcal{L}(E)$ is injective if and only if it is
surjective.

This is the finite-dimensional fact behind Theorem 6.6(c). In infinite dimension a bounded
operator may be injective without being surjective, for example the right shift on $\ell^2$
(`Brezis.Chapter06.remark_6_6_rightShift`). So property (c) is a remarkable property of the
operators $I - T$ with $T$ compact. -/
theorem remark_6_5 [FiniteDimensional ℝ E] (A : E →L[ℝ] E) :
    Function.Injective A ↔ Function.Surjective A :=
  LinearMap.injective_iff_surjective (f := (A : E →ₗ[ℝ] E))

/-- **Comments on Chapter 6, item 1,** of [brezis2011functional]. Let $E$ be a Banach space and let
$T \in \mathcal{K}(E)$. Then $A = I - T$ is a Fredholm operator of index zero: $N(A)$ is finite
dimensional, $R(A)$ is closed of finite codimension, and
$\dim N(A) - \operatorname{codim} R(A) = 0$.

The source says that this "follows from Theorem 6.6". The Fredholm property is Mathlib's
`ContinuousLinearMap.IsFredholm`. It also asks that $A$ be a strict map and that $N(A)$ be
topologically complemented; both hold automatically here. The index is `LinearMap.index`. -/
theorem oneSubCompact_isFredholm_index_zero {T : E →L[ℝ] E} (hT : IsCompactOperator T) :
    ((1 : E →L[ℝ] E) - T).IsFredholm ∧ ((1 : E →L[ℝ] E) - T).index = 0 := by
  have h1 := hT.isFredholm_smul_one_sub one_ne_zero
  have h2 := hT.index_smul_one_sub one_ne_zero
  rw [one_smul] at h1 h2
  exact ⟨h1, h2⟩

end Brezis.Chapter06

end

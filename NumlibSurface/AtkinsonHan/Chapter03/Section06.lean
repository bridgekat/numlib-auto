/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.Analysis.InnerProductSpace.Projection.ObliqueProjection
import Numlib.Analysis.Normed.Module.BestApprox
import Numlib.Approximation.Interpolation
import Numlib.Approximation.Trigonometric
import NumlibSurface.AtkinsonHan.Chapter03.Section03

/-!
# Atkinson and Han, Section 3.6: Projection operators

This module formalizes §3.6 of [han2009theoretical]. A space $V$ is the direct sum
$V = V_1 \oplus V_2$ of two subspaces if every $v \in V$ is $v = v_1 + v_2$ with unique
$v_i \in V_i$. Direct sums correspond to idempotent linear maps $P$, with $V_1 = P(V)$ and
$V_2 = (I - P)(V)$. A projection operator on a Banach space is a bounded linear $P$ with $P^2 = P$.
On a Hilbert space it is an orthogonal projection if $(Pv, (I - P)w) = 0$ for all $v$ and $w$
(3.6.2). An orthogonal projection is self-adjoint, has norm $1$ unless it is $0$, and is determined
by its closed range $V_1$, and then $V = V_1 \oplus V_1^\perp$.

The concrete projections of the section are Lagrange interpolation and piecewise linear
interpolation on $C[a, b]$, the expansion in a finite orthonormal family, and the Fourier projection
$\mathcal{F}_n$ on the space $C_p(2\pi)$ of continuous $2\pi$-periodic functions. The proofs
specialize the oblique projection theory of
`Numlib.Analysis.InnerProductSpace.Projection.ObliqueProjection`, the interpolation operators of
`Numlib.Approximation.Interpolation`, and the Fourier projection of
`Numlib.Approximation.Trigonometric`.

## Main definitions

* Definition 3.6.1, `AtkinsonHan.Chapter03.IsDirectSum`: $V = V_1 \oplus V_2$. It is Mathlib's
  `IsCompl` by `AtkinsonHan.Chapter03.isDirectSum_iff_isCompl`.
* Definition 3.6.1, `AtkinsonHan.Chapter03.IsOrthogonalDirectSum`: a direct sum of two mutually
  orthogonal subspaces.
* Definition 3.6.3, `AtkinsonHan.Chapter03.IsProjectionOperator`: a bounded linear $P$ on a Banach
  space with $P^2 = P$. It is Mathlib's `IsIdempotentElem` by definition.
* Definition 3.6.3 and (3.6.2), `AtkinsonHan.Chapter03.IsOrthogonalProjectionOperator`: a bounded
  projection with $(Pv, (I - P)w) = 0$ for all $v, w$. It is Mathlib's
  `LinearMap.IsSymmetricProjection` by `AtkinsonHan.Chapter03.isOrthogonalProjectionOperator_iff`.
* `AtkinsonHan.Chapter03.IsPeriodicCont` and `AtkinsonHan.Chapter03.PeriodicCont`: the space
  $C_p(2\pi)$, as continuous $2\pi$-periodic functions on $\mathbb{R}$ and as continuous functions
  on the circle $\mathbb{R}/2\pi\mathbb{Z}$. §3.7 uses the same space.

## Main results

* Proposition 3.6.2, `AtkinsonHan.Chapter03.proposition_3_6_2`: $V = V_1 \oplus V_2$ if and only if
  there is an idempotent linear map with range $V_1$ whose complement $I - P$ has range $V_2$.
* Example 3.6.4, `AtkinsonHan.Chapter03.example_3_6_4`: $(v_1, v_2) \mapsto (v_1, 0)$ is an
  orthogonal projection of $\mathbb{R}^2$ onto the $x_1$-axis.
* Example 3.6.5, `AtkinsonHan.Chapter03.example_3_6_5`: Lagrange interpolation is a projection of
  $C[a, b]$ onto $\mathcal{P}_n$, with norm equal to the Lebesgue constant of the nodes.
* Example 3.6.6, `AtkinsonHan.Chapter03.example_3_6_6`: piecewise linear interpolation is a
  projection of $C[a, b]$ with norm $1$.
* Example 3.6.7, `AtkinsonHan.Chapter03.example_3_6_7`: $v \mapsto \sum_i (v, \varphi_i) \varphi_i$
  is an orthogonal projection for a finite orthonormal family.
* Example 3.6.8, `AtkinsonHan.Chapter03.example_3_6_8`: the Fourier projection $\mathcal{F}_n$ is a
  projection of $C_p(2\pi)$ onto $\mathcal{T}_n$, with norm equal to the Lebesgue constant $L_n$.
* Example 3.6.8, `AtkinsonHan.Chapter03.example_3_6_8_l2`: the error $f - \mathcal{F}_n f$ is
  $L^2$-orthogonal to $\mathcal{T}_n$.
* Proposition 3.6.9(a), `AtkinsonHan.Chapter03.proposition_3_6_9_a`: a bounded projection is
  orthogonal if and only if it is self-adjoint.
* Proposition 3.6.9(b), `AtkinsonHan.Chapter03.proposition_3_6_9_b`: an orthogonal projection has
  $\|P\| \le 1$, and $\|P\| = 1$ unless $P = 0$.
* Proposition 3.6.9(c), `AtkinsonHan.Chapter03.proposition_3_6_9_c` and
  `AtkinsonHan.Chapter03.proposition_3_6_9_c'`: $H = V_1 \oplus V_1^\perp$ for a closed subspace
  $V_1$.
* Proposition 3.6.9(d), `AtkinsonHan.Chapter03.proposition_3_6_9_d`: there is exactly one orthogonal
  projection with range $V_1$. It realizes the distance to $V_1$, and $I - P$ is the orthogonal
  projection onto $V_1^\perp$.
* Proposition 3.6.9(e), `AtkinsonHan.Chapter03.proposition_3_6_9_e`: the range of an orthogonal
  projection is closed, and $H = P(H) \oplus P(H)^\perp$ with $P(H)^\perp = (I - P)(H)$.
* Exercise 3.6.1, `AtkinsonHan.Chapter03.exercise_3_6_1`: $I - P$ is a projection whenever $P$ is.
* Exercise 3.6.7, `AtkinsonHan.Chapter03.exercise_3_6_7`: a nonzero bounded projection has norm at
  least $1$.

## Deviations from the source

* **Definitions 3.6.1 and 3.6.3** (reading). The direct sum is stated for normed spaces.
  A bounded projection can be orthogonal even if the inner product space is incomplete.
* **Proposition 3.6.2 and Exercises 3.6.1 and 3.6.7** (reading). The component formula
  follows from the direct-sum characterization. The complementary idempotent and the
  norm lower bound hold before assuming completeness.
* **Example 3.6.4** (reading). The book's $V_1$ is a general line through the origin of
  $\mathbb{R}^2$, drawn in Figure 3.4. The library states the displayed formula, for $V_1$ the
  $x_1$-axis. See `AtkinsonHan.Chapter03.example_3_6_4`.
* **Examples 3.6.5–3.6.8** (reading). Lagrange nodes need not include the endpoints.
  The interpolation examples state the operator norms from Exercise 3.6.8. Example 3.6.7
  concludes orthogonal idempotence, with the span identified in the proof. The Fourier
  residual for continuous periodic data uses probability Haar measure.

## Not formalized

The section states the numbered definitions, examples and propositions, and selected exercises.
-/

namespace AtkinsonHan.Chapter03

/-! ### Definition 3.6.1 and Proposition 3.6.2: direct sums -/

section DirectSum

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **Definition 3.6.1** of [han2009theoretical]. Let $V_1$ and $V_2$ be subspaces of a normed space
$V$ over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. Then $V$ is the **direct sum**
$V = V_1 \oplus V_2$ if every $v \in V$ can be written in exactly one way as $v = v_1 + v_2$
with $v_1 \in V_1$ and $v_2 \in V_2$.

**Reading.** The source uses a linear space. The declaration is stated for a real or complex
normed space, although the unique decomposition is algebraic. -/
def IsDirectSum (V₁ V₂ : Submodule 𝕜 V) : Prop :=
  ∀ v : V, ∃! p : V × V, p.1 ∈ V₁ ∧ p.2 ∈ V₂ ∧ v = p.1 + p.2

/-- The direct sum $V = V_1 \oplus V_2$ of Definition 3.6.1 holds if and only if $V_1$ and $V_2$ are
complements in the lattice of subspaces (Mathlib's `IsCompl`): $V_1 \cap V_2 = \{0\}$ and
$V_1 + V_2 = V$. -/
theorem isDirectSum_iff_isCompl (V₁ V₂ : Submodule 𝕜 V) : IsDirectSum V₁ V₂ ↔ IsCompl V₁ V₂ := by
  constructor
  · intro h
    rw [isCompl_iff]
    refine ⟨?_, ?_⟩
    · rw [disjoint_iff_inf_le]
      intro x hx
      obtain ⟨p, -, huniq⟩ := h x
      have e₁ : ((x, 0) : V × V) = p := huniq _ ⟨hx.1, V₂.zero_mem, by simp⟩
      have e₂ : ((0, x) : V × V) = p := huniq _ ⟨V₁.zero_mem, hx.2, by simp⟩
      have hxx : ((x, 0) : V × V) = ((0, x) : V × V) := e₁.trans e₂.symm
      simpa using (Prod.ext_iff.1 hxx).1
    · rw [codisjoint_iff_le_sup]
      intro x _
      obtain ⟨p, ⟨hp₁, hp₂, hp₃⟩, -⟩ := h x
      rw [hp₃]
      exact Submodule.add_mem_sup hp₁ hp₂
  · intro h v
    obtain ⟨u₁, u₂, hsum, huniq⟩ := Submodule.existsUnique_add_of_isCompl h v
    refine ⟨((u₁ : V), (u₂ : V)), ⟨u₁.2, u₂.2, hsum.symm⟩, ?_⟩
    rintro ⟨w₁, w₂⟩ ⟨hw₁, hw₂, hw⟩
    obtain ⟨e₁, e₂⟩ := huniq ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ hw.symm
    exact Prod.ext (congrArg Subtype.val e₁) (congrArg Subtype.val e₂)

/-- **Proposition 3.6.2** of [han2009theoretical]. Let $V_1$ and $V_2$ be subspaces of a normed
space $V$ over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. Then $V = V_1 \oplus V_2$ if and only
if there is a linear map $P : V \to V$ with $P^2 = P$, $P(V) = V_1$ and $(I - P)(V) = V_2$.

The statement does not include the book's formulas $v_1 = Pv$ and $v_2 = (I - P)v$ for the
components of $v$.

**Reading.** The source also identifies the components as $Pv$ and $(I-P)v$ explicitly. They
follow from the range conditions and uniqueness of the direct-sum decomposition. -/
theorem proposition_3_6_2 (V₁ V₂ : Submodule 𝕜 V) :
    IsDirectSum V₁ V₂ ↔ ∃ P : V →ₗ[𝕜] V, P ∘ₗ P = P ∧ LinearMap.range P = V₁ ∧
      LinearMap.range (LinearMap.id - P) = V₂ := by
  rw [isDirectSum_iff_isCompl]
  constructor
  · intro h
    have hidem : IsIdempotentElem (V₁.projection V₂ h) := Submodule.isIdempotentElem_projection h
    refine ⟨V₁.projection V₂ h, hidem, Submodule.range_projection h, ?_⟩
    rw [← LinearMap.IsIdempotentElem.ker_eq_range hidem]
    exact Submodule.ker_projection h
  · rintro ⟨P, hP, hr, hk⟩
    have hidem : IsIdempotentElem P := hP
    have hc : IsCompl (LinearMap.range P) (LinearMap.ker P) :=
      LinearMap.IsProj.isCompl (LinearMap.IsIdempotentElem.isProj_range P hidem)
    rwa [hr, LinearMap.IsIdempotentElem.ker_eq_range hidem, hk] at hc

/-- **Definition 3.6.1** of [han2009theoretical], for inner product spaces. Two subspaces $V_1$ and
$V_2$ of an inner product space $H$ form an **orthogonal direct sum** if $H = V_1 \oplus V_2$
and $(v_1, v_2) = 0$ for all $v_1 \in V_1$ and $v_2 \in V_2$. -/
def IsOrthogonalDirectSum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (V₁ V₂ : Submodule 𝕜 H) : Prop :=
  IsDirectSum V₁ V₂ ∧ V₁ ⟂ V₂

/-- **Definition 3.6.3** of [han2009theoretical]. Let $V$ be a Banach space. A bounded linear
operator $P : V \to V$ is a **projection operator** if $P^2 = P$.

The definition is Mathlib's `IsIdempotentElem P`, which is the form of the backbone's lemmas on
projections. -/
def IsProjectionOperator [CompleteSpace V] (P : V →L[𝕜] V) : Prop := IsIdempotentElem P

/-- A bounded linear operator on a Banach space is a projection operator in the sense of Definition
3.6.3 if and only if it is idempotent (`IsIdempotentElem`). The two notions agree by definition. -/
theorem isProjectionOperator_iff [CompleteSpace V] (P : V →L[𝕜] V) :
    IsProjectionOperator P ↔ IsIdempotentElem P := Iff.rfl

/-- **Exercise 3.6.1** of [han2009theoretical]. Let $P$ be a bounded linear operator on a normed
space $V$ with $P^2 = P$. Then $(I - P)^2 = I - P$, $\ker P = (I - P)(V)$ and
$P(V) = \ker(I - P)$.

**Reading.** The operator identity and range/kernel statements apply to bounded idempotents
without completeness. The orthogonal case of the exercise is included in `proposition_3_6_9_d`. -/
theorem exercise_3_6_1 {P : V →L[𝕜] V} (hP : IsIdempotentElem P) :
    IsIdempotentElem ((1 : V →L[𝕜] V) - P) ∧
      LinearMap.ker (P : V →ₗ[𝕜] V) = LinearMap.range (1 - (P : V →ₗ[𝕜] V)) ∧
      LinearMap.range (P : V →ₗ[𝕜] V) = LinearMap.ker (1 - (P : V →ₗ[𝕜] V)) := by
  have hlin : IsIdempotentElem (P : V →ₗ[𝕜] V) :=
    ContinuousLinearMap.IsIdempotentElem.toLinearMap hP
  exact ⟨IsIdempotentElem.one_sub hP, LinearMap.IsIdempotentElem.ker_eq_range_one_sub hlin,
    LinearMap.IsIdempotentElem.range_eq_ker_one_sub hlin⟩

/-- **Exercise 3.6.7** of [han2009theoretical]. Let $P$ be a bounded linear operator on a normed
space $V$ with $P^2 = P$ and $P \neq 0$. Then $\|P\| \ge 1$.

**Reading.** The norm lower bound holds without completeness. The orthogonal norm equality
from the exercise is in `proposition_3_6_9_b`. -/
theorem exercise_3_6_7 (P : V →L[𝕜] V) (hP : IsIdempotentElem P) (h0 : P ≠ 0) : 1 ≤ ‖P‖ :=
  one_le_norm_of_isIdempotentElem hP h0

end DirectSum

/-! ### Definition 3.6.3 and Proposition 3.6.9: orthogonal projections -/

section Hilbert

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- **Definition 3.6.3** of [han2009theoretical], with (3.6.2). Let $H$ be an inner product space
over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. A bounded linear operator $P : H \to H$ is an
**orthogonal projection operator** if $P^2 = P$ and
$$(Pv, (I - P)w) = 0 \quad \text{for all } v, w \in H. \qquad (3.6.2)$$

The Lean condition is `inner 𝕜 (P v) ((1 - P) w) = 0`, the complex conjugate of the book's inner
product, so it is the same condition.

**Generalization.** The definition uses a bounded operator on an inner product space.
The book introduces it for Hilbert spaces. -/
def IsOrthogonalProjectionOperator (P : H →L[𝕜] H) : Prop :=
  IsIdempotentElem P ∧ ∀ v w : H, inner 𝕜 (P v) (((1 : H →L[𝕜] H) - P) w) = 0

/-- **Proposition 3.6.9(a)** of [han2009theoretical]. Let $H$ be an inner product space over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let $P$ be a bounded linear operator on $H$ with
$P^2 = P$. Then $P$ satisfies the orthogonality condition (3.6.2) if and only if $P$ is
self-adjoint: $(Pu, v) = (u, Pv)$ for all $u, v \in H$.

**Reading.** This version starts from a bounded idempotent and identifies (3.6.2) with
symmetry. Completeness is unnecessary, and the full projection equivalence is in
`isOrthogonalProjectionOperator_iff`. -/
theorem proposition_3_6_9_a (P : H →L[𝕜] H) (hP : IsIdempotentElem P) :
    (∀ v w : H, inner 𝕜 (P v) (((1 : H →L[𝕜] H) - P) w) = 0) ↔ (P : H →ₗ[𝕜] H).IsSymmetric := by
  have hPP : ∀ x : H, P (P x) = P x := fun x => DFunLike.congr_fun hP x
  have hexp : ∀ v w : H, inner 𝕜 (P v) (((1 : H →L[𝕜] H) - P) w)
      = inner 𝕜 (P v) w - inner 𝕜 (P v) (P w) := by
    intro v w
    rw [← inner_sub_right]
    simp
  constructor
  · intro h v w
    have h₁ : inner 𝕜 (P v) w = inner 𝕜 (P v) (P w) := by
      have hvw := hexp v w
      rw [h v w] at hvw
      linear_combination (norm := module) -hvw
    have h₂ : inner 𝕜 (P w) v = inner 𝕜 (P w) (P v) := by
      have hwv := hexp w v
      rw [h w v] at hwv
      linear_combination (norm := module) -hwv
    calc inner 𝕜 ((P : H →ₗ[𝕜] H) v) w = inner 𝕜 (P v) (P w) := h₁
      _ = starRingEnd 𝕜 (inner 𝕜 (P w) (P v)) := (inner_conj_symm _ _).symm
      _ = starRingEnd 𝕜 (inner 𝕜 (P w) v) := by rw [h₂]
      _ = inner 𝕜 v ((P : H →ₗ[𝕜] H) w) := inner_conj_symm _ _
  · intro h v w
    rw [hexp v w]
    have e₁ := h v (P w)
    have e₂ := h v w
    simp only [ContinuousLinearMap.coe_coe, hPP] at e₁ e₂
    rw [e₁, ← e₂, sub_self]

/-- A bounded linear operator on an inner product space is an orthogonal projection operator in the
sense of Definition 3.6.3 if and only if it is a symmetric idempotent map (Mathlib's
`LinearMap.IsSymmetricProjection`).

**Generalization.** The equivalence holds for bounded maps on incomplete inner product spaces,
whereas Proposition 3.6.9(a) is in a Hilbert space. -/
theorem isOrthogonalProjectionOperator_iff (P : H →L[𝕜] H) :
    IsOrthogonalProjectionOperator P ↔ (P : H →ₗ[𝕜] H).IsSymmetricProjection := by
  constructor
  · rintro ⟨hP, horth⟩
    exact ⟨ContinuousLinearMap.IsIdempotentElem.toLinearMap hP, (proposition_3_6_9_a P hP).1 horth⟩
  · rintro ⟨hidem, hsym⟩
    have hP : IsIdempotentElem P := ContinuousLinearMap.isIdempotentElem_toLinearMap_iff.1 hidem
    exact ⟨hP, (proposition_3_6_9_a P hP).2 hsym⟩

/-- **Example 3.6.7** of [han2009theoretical]. Let $H$ be a Hilbert space over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let $\varphi_1, \ldots, \varphi_n$ be orthonormal
in $H$. Then the operator
$$Pv = \sum_{i=1}^{n} (v, \varphi_i)\, \varphi_i$$
is an orthogonal projection operator.

The operator is the sum of the rank-one operators `InnerProductSpace.rankOne 𝕜 (u i) (u i)`, and
the family $\varphi_i$ is `u`.

**Reading.** The displayed sum is an orthogonal projection. Its range is the span of the
orthonormal family, used in the proof; the declaration concludes orthogonal idempotence. -/
theorem example_3_6_7 [CompleteSpace H] {n : ℕ} {u : Fin n → H} (hu : Orthonormal 𝕜 u) :
    IsOrthogonalProjectionOperator (∑ i, InnerProductSpace.rankOne 𝕜 (u i) (u i)) := by
  classical
  have hsp : (Submodule.span 𝕜 ((Finset.univ : Finset (Fin n)).image u : Set H)).starProjection
      = ∑ i, InnerProductSpace.rankOne 𝕜 (u i) (u i) := by
    rw [(OrthonormalBasis.span hu Finset.univ).starProjection_eq_sum_rankOne]
    simp only [OrthonormalBasis.span_apply]
    exact Finset.sum_coe_sort Finset.univ fun i => InnerProductSpace.rankOne 𝕜 (u i) (u i)
  rw [← hsp, isOrthogonalProjectionOperator_iff]
  exact Submodule.isSymmetricProjection_starProjection _

/-- **Proposition 3.6.9(b)** of [han2009theoretical]. Let $P$ be an orthogonal projection operator
on a Hilbert space $H$ over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. Then $\|P\| \le 1$, and
$\|P\| = 1$ if $P \neq 0$.

The boundedness of $P$, which the book also states, is part of its type. -/
theorem proposition_3_6_9_b [CompleteSpace H] (P : H →L[𝕜] H)
    (hP : IsOrthogonalProjectionOperator P) :
    ‖P‖ ≤ 1 ∧ (P ≠ 0 → ‖P‖ = 1) := by
  have hone : P ≠ 0 → ‖P‖ = 1 := fun h0 =>
    (ContinuousLinearMap.IsIdempotentElem.norm_eq_one_iff_isSymmetric hP.1 h0).2
      ((proposition_3_6_9_a P hP.1).1 hP.2)
  refine ⟨?_, hone⟩
  rcases eq_or_ne P 0 with h0 | h0
  · rw [h0, norm_zero]; norm_num
  · exact (hone h0).le

/-- **Proposition 3.6.9(c)** of [han2009theoretical]. Let $V_1$ be a closed subspace of a Hilbert
space $H$ over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. Then $H = V_1 \oplus V_1^\perp$: the
subspaces $V_1$ and $V_1^\perp$ are complements (`IsCompl`). -/
theorem proposition_3_6_9_c [CompleteSpace H] (V₁ : Submodule 𝕜 H) (h : IsClosed (V₁ : Set H)) :
    IsCompl V₁ V₁ᗮ :=
  have := h.completeSpace_coe
  Submodule.isCompl_orthogonal V₁

/-- **Proposition 3.6.9(c)** of [han2009theoretical], as an orthogonal direct sum. Let $V_1$ be a
closed subspace of a Hilbert space $H$ over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. Then
$H = V_1 \oplus V_1^\perp$ is an orthogonal direct sum in the sense of Definition 3.6.1. -/
theorem proposition_3_6_9_c' [CompleteSpace H] (V₁ : Submodule 𝕜 H) (h : IsClosed (V₁ : Set H)) :
    IsOrthogonalDirectSum V₁ V₁ᗮ :=
  ⟨(isDirectSum_iff_isCompl V₁ V₁ᗮ).2 (proposition_3_6_9_c V₁ h),
    Submodule.isOrtho_orthogonal_right V₁⟩

/-- Let $V_1$ be a subspace of an inner product space $H$ that has an orthogonal projection, and let
$P$ be an orthogonal projection operator in the sense of Definition 3.6.3 with range $V_1$. Then
$P$ is Mathlib's orthogonal projection `V₁.starProjection` onto $V_1$.

**Generalization.** The uniqueness part applies whenever the subspace admits orthogonal
projection, without the ambient completeness and closedness assumptions of the source. -/
theorem eq_starProjection_of_isOrthogonalProjectionOperator (V₁ : Submodule 𝕜 H)
    [V₁.HasOrthogonalProjection] {P : H →L[𝕜] H} (hP : IsOrthogonalProjectionOperator P)
    (hr : LinearMap.range (P : H →ₗ[𝕜] H) = V₁) : P = V₁.starProjection := by
  obtain ⟨hinst, hPeq⟩ := LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.1
    ((isOrthogonalProjectionOperator_iff P).1 hP)
  subst hr
  ext x
  exact congrFun (congrArg DFunLike.coe hPeq) x

/-- **Proposition 3.6.9(d)** of [han2009theoretical]. Let $V_1$ be a closed subspace of a Hilbert
space $H$ over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. Then there is exactly one orthogonal
projection operator $P$ with $P(H) = V_1$. Moreover, every orthogonal projection operator $P$
with $P(H) = V_1$ satisfies

* $\|v - Pv\| = \inf_{w \in V_1} \|v - w\|$ for all $v \in H$;
* $I - P$ is an orthogonal projection operator;
* $(I - P)(H) = V_1^\perp$. -/
theorem proposition_3_6_9_d [CompleteSpace H] (V₁ : Submodule 𝕜 H) (h : IsClosed (V₁ : Set H)) :
    (∃! P : H →L[𝕜] H,
        IsOrthogonalProjectionOperator P ∧ LinearMap.range (P : H →ₗ[𝕜] H) = V₁) ∧
      ∀ P : H →L[𝕜] H, IsOrthogonalProjectionOperator P →
        LinearMap.range (P : H →ₗ[𝕜] H) = V₁ →
        (∀ v : H, ‖v - P v‖ = ⨅ w : V₁, ‖v - (w : H)‖) ∧
          IsOrthogonalProjectionOperator ((1 : H →L[𝕜] H) - P) ∧
            LinearMap.range (((1 : H →L[𝕜] H) - P : H →L[𝕜] H) : H →ₗ[𝕜] H) = V₁ᗮ := by
  have hcs := h.completeSpace_coe
  have hrange : LinearMap.range ((V₁.starProjection : H →L[𝕜] H) : H →ₗ[𝕜] H) = V₁ :=
    V₁.range_starProjection
  have hop : IsOrthogonalProjectionOperator (V₁.starProjection : H →L[𝕜] H) :=
    (isOrthogonalProjectionOperator_iff _).2 (Submodule.isSymmetricProjection_starProjection V₁)
  have honesub : (1 : H →L[𝕜] H) - V₁.starProjection = V₁ᗮ.starProjection :=
    (Submodule.starProjection_orthogonal' V₁).symm
  refine ⟨⟨V₁.starProjection, ⟨hop, hrange⟩, fun Q hQ =>
      eq_starProjection_of_isOrthogonalProjectionOperator V₁ hQ.1 hQ.2⟩, ?_⟩
  intro P hP hPr
  have hPeq : P = V₁.starProjection :=
    eq_starProjection_of_isOrthogonalProjectionOperator V₁ hP hPr
  subst hPeq
  refine ⟨fun v => ((isBestApprox_iff_norm_eq_iInf _ _ _).1
      (isBestApprox_starProjection V₁ v)).2, ?_, ?_⟩
  · rw [honesub]
    exact (isOrthogonalProjectionOperator_iff _).2
      (Submodule.isSymmetricProjection_starProjection _)
  · rw [honesub]
    exact V₁ᗮ.range_starProjection

/-- **Proposition 3.6.9(e)** of [han2009theoretical]. Let $P$ be an orthogonal projection operator
on a Hilbert space $H$ over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. Then the range $P(H)$ is
closed, $H = P(H) \oplus (I - P)(H)$, and $(I - P)(H) = P(H)^\perp$. -/
theorem proposition_3_6_9_e [CompleteSpace H] (P : H →L[𝕜] H)
    (hP : IsOrthogonalProjectionOperator P) :
    IsClosed (LinearMap.range (P : H →ₗ[𝕜] H) : Set H) ∧
      IsCompl (LinearMap.range (P : H →ₗ[𝕜] H))
        (LinearMap.range (((1 : H →L[𝕜] H) - P : H →L[𝕜] H) : H →ₗ[𝕜] H)) ∧
      LinearMap.range (((1 : H →L[𝕜] H) - P : H →L[𝕜] H) : H →ₗ[𝕜] H)
        = (LinearMap.range (P : H →ₗ[𝕜] H))ᗮ := by
  have hlin : IsIdempotentElem (P : H →ₗ[𝕜] H) :=
    ContinuousLinearMap.IsIdempotentElem.toLinearMap hP.1
  have hsym : (P : H →ₗ[𝕜] H).IsSymmetric := (proposition_3_6_9_a P hP.1).1 hP.2
  have hker : LinearMap.ker (P : H →ₗ[𝕜] H) = LinearMap.range (1 - (P : H →ₗ[𝕜] H)) :=
    LinearMap.IsIdempotentElem.ker_eq_range_one_sub hlin
  have hcoe : (((1 : H →L[𝕜] H) - P : H →L[𝕜] H) : H →ₗ[𝕜] H) = 1 - (P : H →ₗ[𝕜] H) := rfl
  refine ⟨ContinuousLinearMap.IsIdempotentElem.isClosed_range hP.1, ?_, ?_⟩
  · rw [hcoe, ← hker]
    exact LinearMap.IsProj.isCompl (LinearMap.IsIdempotentElem.isProj_range _ hlin)
  · rw [hcoe, ← hker, ← LinearMap.IsSymmetric.orthogonal_range hsym]

end Hilbert

/-!
### $C_p(2\pi)$, the space of Example 3.6.8

$C_p(2\pi)$ is the space of the Fourier projection of Example 3.6.8. §3.7 states Jackson's theorem
and the bounds on the Lebesgue constants on the same space.
-/

section Spaces

open Real

/-- The space $C_p(2\pi)$ of [han2009theoretical], as the book describes it: a function
$g : \mathbb{R} \to \mathbb{R}$ is in $C_p(2\pi)$ if it is continuous and $2\pi$-periodic. -/
def IsPeriodicCont (g : ℝ → ℝ) : Prop := Continuous g ∧ Function.Periodic g (2 * π)

/-- The space $C_p(2\pi)$ of [han2009theoretical], as continuous real functions on the circle
$\mathbb{R}/2\pi\mathbb{Z}$. The circle is compact, so the space carries the uniform norm
$\|\cdot\|_\infty$ of the book. -/
abbrev PeriodicCont : Type := C(AddCircle (2 * π), ℝ)

/-- A continuous $2\pi$-periodic function $g$ on $\mathbb{R}$, as an element of $C_p(2\pi)$: the
continuous function on the circle $\mathbb{R}/2\pi\mathbb{Z}$ induced by $g$. -/
noncomputable def PeriodicCont.ofIsPeriodicCont {g : ℝ → ℝ} (h : IsPeriodicCont g) :
    PeriodicCont :=
  ⟨h.2.lift, continuous_quot_lift _ h.1⟩

/-- The function on the circle that `AtkinsonHan.Chapter03.PeriodicCont.ofIsPeriodicCont` makes from
$g$ takes the value $g(x)$ at the class of $x \in \mathbb{R}$. -/
@[simp] theorem PeriodicCont.ofIsPeriodicCont_coe {g : ℝ → ℝ} (h : IsPeriodicCont g) (x : ℝ) :
    PeriodicCont.ofIsPeriodicCont h (x : AddCircle (2 * π)) = g x :=
  h.2.lift_coe x

end Spaces

/-! ### Examples 3.6.4, 3.6.5, 3.6.6 and 3.6.8: the concrete projections -/

section Examples

open MeasureTheory Real

/-- **Example 3.6.4** of [han2009theoretical]. The operator $P$ on $\mathbb{R}^2$ with
$P(v_1, v_2) = (v_1, 0)$ is an orthogonal projection operator in the sense of Definition 3.6.3
and (3.6.2). It projects onto the $x_1$-axis.

**Reading.** The book's $V_1$ is a general line through the origin, and its Figure 3.4 is a
picture of the orthogonal decomposition. The statement here is the displayed formula, for $V_1$
the $x_1$-axis.

The space is `EuclideanSpace ℝ (Fin 2)`, and $v_1$ is the coordinate `v 0`. -/
theorem example_3_6_4 :
    ∃ P : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2),
      (∀ v : EuclideanSpace ℝ (Fin 2), P v = EuclideanSpace.single 0 (v 0)) ∧
        IsOrthogonalProjectionOperator P := by
  set P : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    (EuclideanSpace.proj (0 : Fin 2)).smulRight (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
    with hPdef
  have hP : ∀ v : EuclideanSpace ℝ (Fin 2), P v = EuclideanSpace.single 0 (v 0) := by
    intro v
    ext i
    fin_cases i <;> simp [hPdef]
  refine ⟨P, hP, ?_, fun v w => ?_⟩
  · refine ContinuousLinearMap.ext fun v => ?_
    change P (P v) = P v
    rw [hP v, hP (EuclideanSpace.single 0 (v 0))]
    congr 1
  · change inner ℝ (P v) (w - P w) = 0
    rw [hP v, hP w, PiLp.inner_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    fin_cases i <;> simp

/-- **Example 3.6.5** of [han2009theoretical]. Let $x_0, \ldots, x_n$ be $n + 1$ distinct nodes in
$[a, b]$, and let $\ell_0, \ldots, \ell_n$ be their Lagrange basis polynomials. Then the
Lagrange interpolation operator $P_n f = \sum_{i=0}^{n} f(x_i)\, \ell_i$ is a projection
operator on $C[a, b]$ with range $\mathcal{P}_n$, the polynomials of degree at most $n$. Its
norm is the Lebesgue constant of the nodes,
$$\|P_n\| = \sup_{t \in [a, b]} \sum_{i=0}^{n} |\ell_i(t)|.$$

The basis polynomial $\ell_i$ is `Lagrange.basisCM x i`, and the operator is
`Lagrange.interpolateCLM x`. The interval $[a, b]$ is compact and nonempty, so the supremum is
attained.

**Generalization.** The nodes need only be distinct points of the interval, without including
both endpoints. The operator norm is the answer to Exercise 3.6.8(a). -/
theorem example_3_6_5 {a b : ℝ} {n : ℕ} {x : Fin (n + 1) → Set.Icc a b}
    (hx : Function.Injective x) :
    IsProjectionOperator (Lagrange.interpolateCLM x) ∧
      LinearMap.range ((Lagrange.interpolateCLM x :
          C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) :
          C(Set.Icc a b, ℝ) →ₗ[ℝ] C(Set.Icc a b, ℝ)) = polyLE a b n ∧
      ‖Lagrange.interpolateCLM x‖ = sSup (Set.range fun t => ∑ i, |Lagrange.basisCM x i t|) := by
  have : Nonempty (Set.Icc a b) := ⟨x 0⟩
  refine ⟨Lagrange.isIdempotentElem_interpolateCLM hx, ?_, Lagrange.norm_interpolateCLM hx⟩
  rw [Lagrange.range_interpolateCLM hx, polyLE_eq]

/-- **Example 3.6.6** of [han2009theoretical]. Let $a = x_0 < x_1 < \cdots < x_{n+1} = b$ be a
partition of $[a, b]$. Then piecewise linear interpolation at these nodes is a projection
operator on $C[a, b]$ of norm $1$.

On each subinterval the interpolant is a convex combination of two values of the function, and
the interpolation of a constant is the constant itself. The operator is
`piecewiseLinearInterpCLM n x`, where only the first $n + 2$ terms of the sequence `x` are used.

**Reading.** The theorem states idempotence and the norm asked for in Exercise 3.6.8(b).
The nodal interpolation formulas are given in Section 3.2. -/
theorem example_3_6_6 {a b : ℝ} {n : ℕ} {x : ℕ → Set.Icc a b}
    (hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ)) (hfirst : (x 0 : ℝ) = a)
    (hlast : (x (n + 1) : ℝ) = b) :
    IsProjectionOperator (piecewiseLinearInterpCLM n x) ∧
      ‖piecewiseLinearInterpCLM n x‖ = 1 :=
  ⟨isIdempotentElem_piecewiseLinearInterpCLM ⟨fun i hi => hstep i (by omega), hfirst, hlast⟩,
    norm_piecewiseLinearInterpCLM ⟨fun i hi => hstep i (by omega), hfirst, hlast⟩⟩

/-- **Example 3.6.8** of [han2009theoretical]. The Fourier projection $\mathcal{F}_n$ is a
projection operator on $C_p(2\pi)$. Its range is the space $\mathcal{T}_n$ of trigonometric
polynomials of degree at most $n$, and its norm is the $n$-th Lebesgue constant
$$\|\mathcal{F}_n\| = L_n = \frac{1}{\pi} \int_{-\pi}^{\pi} |D_n(\theta)|\, d\theta$$
of (3.7.9), where $D_n$ is the Dirichlet kernel.

The operator is `PeriodicCont.fourierProj n`, the integral operator of the Dirichlet kernel, and
$L_n$ is `PeriodicCont.lebesgueConstant n`. -/
theorem example_3_6_8 (n : ℕ) :
    IsProjectionOperator (_root_.PeriodicCont.fourierProj n) ∧
      LinearMap.range ((_root_.PeriodicCont.fourierProj n : PeriodicCont →L[ℝ] PeriodicCont) :
          PeriodicCont →ₗ[ℝ] PeriodicCont) = trigPolyLE (2 * π) n ∧
      ‖_root_.PeriodicCont.fourierProj n‖ = _root_.PeriodicCont.lebesgueConstant n :=
  ⟨_root_.PeriodicCont.isIdempotentElem_fourierProj n, _root_.PeriodicCont.range_fourierProj n,
    _root_.PeriodicCont.norm_fourierProj n⟩

/-- **Example 3.6.8** of [han2009theoretical], the closing remark. Let $f \in C_p(2\pi)$ and let
$\varphi_m$, $|m| \le n$, be the members of the real trigonometric system that span
$\mathcal{T}_n$. Then
$$(\varphi_m, f - \mathcal{F}_n f) = 0$$
in $L^2(0, 2\pi)$. So $f - \mathcal{F}_n f$ is orthogonal to $\mathcal{T}_n$, and
$\mathcal{F}_n$ is also the orthogonal projection of $L^2(0, 2\pi)$ onto $\mathcal{T}_n$, read
on the continuous functions.

The inner product is that of $L^2$ for the probability Haar measure of the circle, and
$\varphi_m$ is `trigLp (2 * π) m`. The Fourier projection is not orthogonal for the uniform norm
of $C_p(2\pi)$: its norm is $L_n$, which grows like $\log n$
(`PeriodicCont.log_le_lebesgueConstant`), whereas an orthogonal projection has norm $1$ by
Proposition 3.6.9(b).

**Reading.** The theorem gives the residual orthogonality for continuous periodic inputs,
using probability Haar measure. The full $L^2$ statement is `example_3_4_9`. -/
theorem example_3_6_8_l2 {n : ℕ} (f : PeriodicCont) {m : ℤ} (hm : m.natAbs ≤ n) :
    inner ℝ (trigLp (2 * π) m)
        (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℝ f -
          ContinuousMap.toLp 2 AddCircle.haarAddCircle ℝ
            (_root_.PeriodicCont.fourierProj n f)) = 0 := by
  classical
  have hbridge : ∀ g : C(AddCircle (2 * π), ℝ),
      inner ℝ (trigLp (2 * π) m) (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℝ g)
        = realFourierCoeff (⇑g) m := by
    intro g
    rw [trigLp, ContinuousMap.inner_toLp, realFourierCoeff_apply]
    simp [mul_comm]
  have hsum : ContinuousMap.toLp 2 AddCircle.haarAddCircle ℝ
      (_root_.PeriodicCont.fourierProj n f)
      = ∑ j ∈ Finset.Icc (-(n : ℤ)) n, realFourierCoeff (⇑f) j • trigLp (2 * π) j := by
    rw [_root_.PeriodicCont.fourierProj_eq_sum, map_sum]
    exact Finset.sum_congr rfl fun j _ => map_smul _ _ _
  rw [inner_sub_right, hbridge f, hsum, inner_sum]
  have hstep : ∀ j ∈ Finset.Icc (-(n : ℤ)) n,
      inner ℝ (trigLp (2 * π) m) (realFourierCoeff (⇑f) j • trigLp (2 * π) j)
        = if m = j then realFourierCoeff (⇑f) j else 0 := by
    intro j _
    rw [real_inner_smul_right, orthonormal_iff_ite.1 orthonormal_trigFun m j]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_ite_eq _ m,
    ite_eq_left (Finset.mem_Icc.2 (Set.mem_Icc.1 (mem_Icc_iff_natAbs_le.2 hm)))]
  ring

end Examples

end AtkinsonHan.Chapter03

/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Convex.Strong
import Numlib.Variational.Inequality.Basic
import Numlib.Variational.Minimization
import NumlibSurface.AtkinsonHan.Chapter05.Section03
import NumlibSurface.AtkinsonHan.Chapter08.Section03
import NumlibSurface.AtkinsonHan.Chapter11.Section01

/-!
# Atkinson and Han, Section 11.2: Existence and uniqueness based on convex minimization

This module formalizes Section 11.2 of [han2009theoretical]. The section turns a constrained convex
minimization problem into an elliptic variational inequality and back. Theorem 11.2.1 does this for
a Gâteaux differentiable convex functional $f$ plus a second convex functional $j$ that need not be
differentiable: $u \in K$ minimizes $f + j$ over a convex set $K$ if and only if $\langle f'(u), v -
u \rangle + j(v) - j(u) \ge 0$ for all $v \in K$. Theorem 11.2.2 does this for the energy
$$E(v) = \tfrac12 a(v, v) + j(v) - \ell(v)$$
of a bounded, symmetric, $V$-elliptic bilinear form $a$ on a real Hilbert space $V$. There the
minimizer over a nonempty closed convex set exists and is unique, and it is the solution of the
variational inequality $a(u, v - u) + j(v) - j(u) \ge \ell(v - u)$ for all $v \in K$. Exercise
11.2.1 is the same result on a complex Hilbert space.

Examples 11.2.3 and 11.2.4 apply Theorem 11.2.2 to the obstacle problem and to the simplified
friction problem of Section 11.1. The abstract results specialize `isMinOn_add_iff_forall_le` of
`Numlib.Analysis.Convex.Gateaux` and `existsUnique_isMinOn_energy_add` of
`Numlib.Variational.Inequality.Basic`.

## Main results

* Theorem 11.2.1, `AtkinsonHan.Chapter11.theorem_11_2_1`: $u$ minimizes $f + j$ over $K$ (11.2.1) if
  and only if $u$ solves the variational inequality (11.2.2).
* (11.2.3), `AtkinsonHan.Chapter05.theorem_5_3_19_submodule`: over a subspace and with $j = 0$, the
  variational inequality is the equation $\langle f'(u), v \rangle = 0$.
* Theorem 11.2.2, `AtkinsonHan.Chapter11.theorem_11_2_2`: the energy $E$ has exactly one minimizer
  on a nonempty closed convex set $K$.
* Theorem 11.2.2, `AtkinsonHan.Chapter11.theorem_11_2_2_iff`: the minimizers of $E$ over $K$ are the
  solutions of the variational inequality (11.3.12).
* Theorem 11.2.2 with $j = 0$, `AtkinsonHan.Chapter11.theorem_11_2_2_zero`: exactly one minimizer,
  and exactly one solution of $a(u, v - u) \ge \ell(v - u)$ for all $v \in K$.
* Example 11.2.3, `AtkinsonHan.Chapter11.example_11_2_3`: the obstacle problem has a nonempty closed
  convex admissible set and a strictly convex, coercive, continuous energy, and the minimization
  problem (11.1.6) and the variational inequality (11.1.7) each have exactly one solution.
* Example 11.2.4, `AtkinsonHan.Chapter11.example_11_2_4`: the variational inequality (11.1.13) of
  the simplified friction problem has exactly one solution.
* Exercise 11.2.1, `AtkinsonHan.Chapter11.exercise_11_2_1`: Theorem 11.2.2 for a Hermitian
  $V$-elliptic sesquilinear form on a complex Hilbert space.

## Implementation notes

* Theorem 11.2.1 extends Theorem 5.3.19 (`AtkinsonHan.Chapter05.theorem_5_3_19`) by the term $j$.
  Formula (11.2.3) is `AtkinsonHan.Chapter05.theorem_5_3_19_submodule` and is not restated here.
* The variational inequality of Theorem 11.2.2 is written out as
  $a(u, v - u) + j(v) - j(u) \ge \ell(v - u)$. This is the inequality (11.3.12) of Section 11.3,
  where it is `AtkinsonHan.Chapter11.IsVariationalInequalitySolution` for the operator
  `AtkinsonHan.BilinForm.toOperator` of $a$ and the Riesz representative `SesqForm.rieszRep` of
  $\ell$. The identification is
  `AtkinsonHan.Chapter11.isVariationalInequalitySolution_toOperator_iff`.
* The source obtains the minimizer of Theorem 11.2.2 from its Theorem 3.3.12, with the reflexivity
  of $V$. The proof here stays in the Hilbert space: the parallelogram law makes every minimizing
  sequence a Cauchy sequence. The statement is the one of the source.
* Exercise 11.2.1 states both claims in one theorem, because the two claims share the passage to the
  real form $b(u, v) = \operatorname{Re} a(u, v)$, which is the whole proof.

## Deviations from the source

* **Example 11.2.3** (reading). The condition "$\psi \le 0$ on $\Gamma$" on the obstacle is read as:
  $\max\{\psi, 0\}$ is the function of an element of $H^1_0(\Omega)$. See
  `AtkinsonHan.Chapter11.example_11_2_3`.
* **Example 11.2.4** (reading). The Lipschitz domain of the source is a domain with a boundary trace
  in the sense of `BoundaryData.TraceFamily`, for example a bounded $C^1$ domain or a polygon
  without slits. See `AtkinsonHan.Chapter11.example_11_2_4`.
-/

open Filter MeasureTheory Set TopologicalSpace Topology
open scoped ENNReal InnerProductSpace

namespace AtkinsonHan.Chapter11

/-! ### Theorem 11.2.1: minimization and the variational inequality -/

section Gateaux

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {K : Set V} {f j : V → ℝ} {f' : V → V →L[ℝ] ℝ}

/-- **Theorem 11.2.1** of [han2009theoretical]. Let $V$ be a real normed space and $K \subseteq V$.
Let $f, j \colon V \to \mathbb{R}$ be convex on $K$, and let $f$ have the Gâteaux derivative
$f'(u) \in V'$ at every $u \in K$. Then $u \in K$ minimizes $f + j$ over $K$, which is (11.2.1),
if and only if
$$\langle f'(u), v - u \rangle + j(v) - j(u) \ge 0 \quad \text{for all } v \in K,$$
which is (11.2.2).

The convexity of $K$ is part of `ConvexOn ℝ K f` and is not a separate hypothesis. The Gâteaux
derivative is `AtkinsonHan.Chapter05.HasGateauxDerivAt`. The case $j = 0$ is
`AtkinsonHan.Chapter05.theorem_5_3_19`, and the case of a subspace with $j = 0$, (11.2.3), is
`AtkinsonHan.Chapter05.theorem_5_3_19_submodule`. The proof specializes
`isMinOn_add_iff_forall_le`. -/
theorem theorem_11_2_1 (hf : ConvexOn ℝ K f) (hj : ConvexOn ℝ K j)
    (hG : ∀ u ∈ K, Chapter05.HasGateauxDerivAt f (f' u) u) {u : V} (hu : u ∈ K) :
    IsMinOn (f + j) K u ↔ ∀ v ∈ K, 0 ≤ f' u (v - u) + j v - j u :=
  isMinOn_add_iff_forall_le hf hj hG hu

end Gateaux

/-! ### Theorem 11.2.2: the quadratic energy on a real Hilbert space -/

section Real

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable {a : BilinForm V} {M α : ℝ}

/-- **Theorem 11.2.2** of [han2009theoretical], existence and uniqueness. Let $V$ be a real Hilbert
space and let $K \subseteq V$ be nonempty, closed and convex. Let $a$ be a bilinear form on $V$
that is bounded with constant $M$, symmetric, and $V$-elliptic with constant $\alpha > 0$. Let
$\ell \in V'$, and let $j \colon V \to \mathbb{R}$ be convex and lower semicontinuous on $K$.
Then the energy
$$E(v) = \tfrac12 a(v, v) + j(v) - \ell(v)$$
has exactly one minimizer $u \in K$ over $K$.

The source derives the existence from its Theorem 3.3.12, with the reflexivity of $V$. The proof
here is the Hilbert-space one: the parallelogram law makes every minimizing sequence a Cauchy
sequence, and the affine minorant of Lemma 11.3.5 makes the energy bounded below. It specializes
`existsUnique_isMinOn_energy_add`. The energy $\frac12 a(v, v) - \ell(v)$ is
`AtkinsonHan.BilinForm.energy`. The characterization of the minimizer by the variational
inequality is `AtkinsonHan.Chapter11.theorem_11_2_2_iff`. -/
theorem theorem_11_2_2 (hM : a.IsBoundedWith M) (hα : 0 < α) (ha : a.IsEllipticWith α)
    (hs : LinearMap.BilinForm.IsSymm a) (ℓ : StrongDual ℝ V) {j : V → ℝ} {K : Set V}
    (hKne : K.Nonempty) (hKcl : IsClosed K) (hKcv : Convex ℝ K) (hj : ConvexOn ℝ K j)
    (hjlsc : LowerSemicontinuousOn j K) : ∃! u, u ∈ K ∧ IsMinOn (a.energy ℓ + j) K u :=
  existsUnique_isMinOn_energy_add ((BilinForm.isSymm_iff_isHermitian hM).mp hs) hα
    ((BilinForm.isEllipticWith_iff_isCoerciveWith hM).mp ha) ℓ hKne hKcl hKcv hj hjlsc

/-- **Theorem 11.2.2** of [han2009theoretical], characterization. Let $V$ be a real Hilbert space
and let $K \subseteq V$ be convex. Let $a$ be a bilinear form on $V$ that is bounded with
constant $M$, symmetric, and $V$-elliptic with constant $\alpha > 0$. Let $\ell \in V'$, and let
$j$ be convex on $K$. Then $u \in K$ minimizes $E(v) = \frac12 a(v, v) + j(v) - \ell(v)$ over
$K$ if and only if
$$a(u, v - u) + j(v) - j(u) \ge \ell(v - u) \quad \text{for all } v \in K.$$

This is the variational inequality (11.3.12) of Section 11.3. The closedness of $K$ and the
lower semicontinuity of $j$ are not needed here; they are what make a minimizer exist. -/
theorem theorem_11_2_2_iff (hM : a.IsBoundedWith M) (hα : 0 < α) (ha : a.IsEllipticWith α)
    (hs : LinearMap.BilinForm.IsSymm a) (ℓ : StrongDual ℝ V) {j : V → ℝ} {K : Set V}
    (hKcv : Convex ℝ K) (hj : ConvexOn ℝ K j) {u : V} (hu : u ∈ K) :
    IsMinOn (a.energy ℓ + j) K u ↔ ∀ v ∈ K, a u (v - u) + j v - j u ≥ ℓ (v - u) := by
  have hh : SesqForm.IsHermitian (𝕜 := ℝ) (a.toCLM hM) :=
    (BilinForm.isSymm_iff_isHermitian hM).mp hs
  have hcoer : SesqForm.IsCoerciveWith (𝕜 := ℝ) (a.toCLM hM) α :=
    (BilinForm.isEllipticWith_iff_isCoerciveWith hM).mp ha
  refine (isMinOn_energy_add_iff hh hα.le hcoer ℓ hKcv hj hu).trans ?_
  simp only [_root_.IsVariationalInequalitySolution, BilinForm.inner_toOperator,
    BilinForm.inner_rieszRep, ge_iff_le]
  exact ⟨fun h => h.2, fun h => ⟨hu, h⟩⟩

end Real

/-! ### Exercise 11.2.1: the complex case -/

section Complex

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- **Exercise 11.2.1** of [han2009theoretical], the complex case of Theorem 11.2.2. Let $V$ be a
complex Hilbert space and let $K \subseteq V$ be nonempty, closed and convex. Let $a$ be a
bounded Hermitian sesquilinear form on $V$ with $\alpha \|v\|^2 \le \operatorname{Re} a(v, v)$
for all $v$, for some $\alpha > 0$. Let $\ell \in V'$, and let $j \colon V \to \mathbb{R}$ be
convex and lower semicontinuous on $K$. Then the energy
$$E(v) = \tfrac12 \operatorname{Re} a(v, v) + j(v) - \operatorname{Re} \ell(v)$$
has exactly one minimizer on $K$. Moreover, $u \in K$ minimizes $E$ over $K$ if and only if
$$\operatorname{Re} a(u, v - u) + j(v) - j(u) \ge \operatorname{Re} \ell(v - u) \quad \text{for
  all } v \in K.$$

The real parts are those of the source: $a(v, v)$ is real for a Hermitian form, and the
minimized quantity is real. The convexity of $K$ is convexity for real scalars, which is what
convexity means on a complex vector space. The form $a$ is a `SesqForm ℂ V`, which is
conjugate-linear in its first argument. The proof applies Theorem 11.2.2 to the real bilinear
form $b(u, v) = \operatorname{Re} a(u, v)$ on $V$ with the real inner product
$\operatorname{Re} \langle \cdot, \cdot \rangle$. This form is symmetric and $V$-elliptic with
the same constant, and it has the same energy as $a$. The real inner product structure is
introduced inside the proof, because `InnerProductSpace.complexToReal` is not an instance. -/
theorem exercise_11_2_1 {a : SesqForm ℂ V} (ha : a.IsHermitian) {α : ℝ} (hα : 0 < α)
    (hcoer : a.IsCoerciveWith α) (ℓ : V →L[ℂ] ℂ) {j : V → ℝ} {K : Set V} (hKne : K.Nonempty)
    (hKcl : IsClosed K) (hKcv : Convex ℝ K) (hj : ConvexOn ℝ K j)
    (hjlsc : LowerSemicontinuousOn j K) :
    (∃! u, u ∈ K ∧ IsMinOn (a.energy ℓ + j) K u) ∧
      ∀ u ∈ K, (IsMinOn (a.energy ℓ + j) K u ↔
        ∀ v ∈ K, RCLike.re (a u (v - u)) + j v - j u ≥ RCLike.re (ℓ (v - u))) := by
  let _ : InnerProductSpace ℝ V := InnerProductSpace.complexToReal
  obtain ⟨b, hbdef⟩ : ∃ b : SesqForm ℝ V,
      b = (innerSL ℝ).comp ((SesqForm.toOperator a : V →L[ℂ] V).restrictScalars ℝ) := ⟨_, rfl⟩
  obtain ⟨L, hLdef⟩ : ∃ L : V →L[ℝ] ℝ, L = RCLike.reCLM.comp (ℓ.restrictScalars ℝ) := ⟨_, rfl⟩
  have hbap : ∀ u v : V, b u v = RCLike.re (a u v) := by
    intro u v
    rw [hbdef]
    change inner ℝ (SesqForm.toOperator a u) v = _
    rw [real_inner_eq_re_inner ℂ, SesqForm.inner_toOperator]
  have hLap : ∀ v : V, L v = RCLike.re (ℓ v) := by
    intro v
    rw [hLdef]
    rfl
  have hherm : b.IsHermitian := by
    intro u v
    simp [hbap, ha v u]
  have hbcoer : b.IsCoerciveWith α := fun v => by simpa [hbap v v] using hcoer v
  have henergy : b.energy L + j = a.energy ℓ + j := by
    funext v
    simp only [Pi.add_apply, SesqForm.energy, hbap v v, hLap v, RCLike.re_to_real]
  rw [← henergy]
  refine ⟨existsUnique_isMinOn_energy_add hherm hα hbcoer L hKne hKcl hKcv hj hjlsc,
    fun u hu => (isMinOn_energy_add_iff hherm hα.le hbcoer L hKcv hj hu).trans ?_⟩
  constructor
  · rintro ⟨-, h⟩ v hv
    have hv' := h v hv
    rwa [SesqForm.inner_toOperator, SesqForm.inner_rieszRep, hbap, hLap] at hv'
  · intro h
    refine ⟨hu, fun v hv => ?_⟩
    rw [SesqForm.inner_toOperator, SesqForm.inner_rieszRep, hbap, hLap]
    exact h v hv

end Complex

/-! ### Example 11.2.3: the obstacle problem -/

section Obstacle

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {a : BilinForm V} {M α : ℝ}

/-- **Theorem 11.2.2** of [han2009theoretical] with $j = 0$. Let $V$ be a real Hilbert space and let
$K \subseteq V$ be nonempty, closed and convex. Let $a$ be a bilinear form on $V$ that is
bounded with constant $M$, symmetric, and $V$-elliptic with constant $\alpha > 0$, and let
$\ell \in V'$. Then the energy $E(v) = \frac12 a(v, v) - \ell(v)$ has exactly one minimizer on
$K$, and the variational inequality
$$u \in K, \qquad a(u, v - u) \ge \ell(v - u) \quad \text{for all } v \in K,$$
which is (11.3.13), has exactly one solution.

This combines `AtkinsonHan.Chapter11.theorem_11_2_2` and
`AtkinsonHan.Chapter11.theorem_11_2_2_iff` at $j = 0$. It is stated for an abstract space so
that Example 11.2.3 is a single application of it. -/
theorem theorem_11_2_2_zero (hM : a.IsBoundedWith M) (hα : 0 < α) (ha : a.IsEllipticWith α)
    (hs : LinearMap.BilinForm.IsSymm a) (ℓ : StrongDual ℝ V) {K : Set V}
    (hKne : K.Nonempty) (hKcl : IsClosed K) (hKcv : Convex ℝ K) :
    (∃! u, u ∈ K ∧ IsMinOn (a.energy ℓ) K u) ∧
      ∃! u, u ∈ K ∧ ∀ v ∈ K, a u (v - u) ≥ ℓ (v - u) := by
  have hmin := theorem_11_2_2 hM hα ha hs ℓ (j := fun _ ↦ (0 : ℝ)) hKne hKcl hKcv
    (convexOn_const _ hKcv) (lowerSemicontinuous_const.lowerSemicontinuousOn _)
  have e0 : a.energy ℓ + (fun _ ↦ (0 : ℝ)) = a.energy ℓ := funext fun v ↦ add_zero _
  rw [e0] at hmin
  refine ⟨hmin, ?_⟩
  have hiff : ∀ u ∈ K, IsMinOn (a.energy ℓ) K u ↔ ∀ v ∈ K, a u (v - u) ≥ ℓ (v - u) :=
    fun u hu ↦ by
      have h := theorem_11_2_2_iff hM hα ha hs ℓ (j := fun _ ↦ (0 : ℝ)) hKcv (convexOn_const _ hKcv)
        hu
      rw [e0] at h
      simp only [sub_zero, add_zero] at h
      exact h
  obtain ⟨u, ⟨hu, humin⟩, huniq⟩ := hmin
  refine ⟨u, ⟨hu, (hiff u hu).1 humin⟩, ?_⟩
  rintro y ⟨hy, hyvi⟩
  exact huniq y ⟨hy, (hiff y hy).2 hyvi⟩

variable {d : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1))))

/-- **Example 11.2.3** of [han2009theoretical] (the obstacle problem). Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be open with $\Omega \subseteq B(0, R)$ for some $R \ge 0$.
Let $\psi \in H^1(\Omega)$ be an obstacle such that $\max\{\psi, 0\}$ is almost everywhere equal
to the function of an element of $H^1_0(\Omega)$, and let $f \in L^2(\Omega)$. Let
$$K = \{v \in H^1_0(\Omega) : v \ge \psi \text{ a.e. in } \Omega\}, \qquad E(v) = \int_\Omega
  \Bigl(\tfrac12 |\nabla v|^2 - f v\Bigr) \, dx.$$
Then $K$ is nonempty, closed and convex, and $E$ is strictly convex on $K$, coercive on $K$ and
continuous. The minimization problem (11.1.6) of $E$ over $K$ has exactly one solution
$u \in K$. The variational inequality (11.1.7),
$$u \in K, \qquad \int_\Omega \nabla u \cdot \nabla (v - u) \, dx \ge \int_\Omega f (v - u) \,
  dx \quad \text{for all } v \in K,$$
also has exactly one solution.

**Reading.** The source asks that $\psi \le 0$ on $\Gamma$. Without a trace, this is read as the
condition that $\max\{\psi, 0\}$ is the function of an element of $H^1_0(\Omega)$, as in Example
11.1.1. Then $\max\{\psi, 0\} \in K$.

The set $K$ is `AtkinsonHan.Chapter11.obstacleSet` and the energy is
`AtkinsonHan.Chapter11.obstacleEnergy`. The coercivity is `IsCoerciveFunctionalOn`:
$E(v) \to \infty$ as $\|v\| \to \infty$ in $K$. The set-theoretic clauses are
`AtkinsonHan.Chapter11.obstacleSet_nonempty`, `AtkinsonHan.Chapter11.isClosed_obstacleSet` and
`AtkinsonHan.Chapter11.convex_obstacleSet`. Strict convexity and coercivity follow from the
strong convexity of the energy of a symmetric $V$-elliptic form,
`SesqForm.strongConvexOn_energy`, with the Poincaré constant $(1 + (2R)^2)^{-1}$, and from
`StrongConvexOn.isCoerciveFunctionalOn_of_continuous`. Continuity is
`SesqForm.continuous_energy`. The minimizer and the solution of the inequality come from
`AtkinsonHan.Chapter11.theorem_11_2_2_zero`. -/
theorem example_11_2_3 {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ Metric.ball 0 R)
    {ψ : SobolevEuclidean (d + 1) 1 2 Ω}
    (hψ : ∃ w ∈ SobolevEuclideanZero (d + 1) 1 2 Ω, SobolevMultiIndex.fn w
      =ᵐ[MeasureTheory.volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        fun x ↦ max (SobolevMultiIndex.fn ψ x) 0)
    (f : MeasureTheory.Lp ℝ 2
      (MeasureTheory.volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    (obstacleSet Ω ψ).Nonempty ∧ IsClosed (obstacleSet Ω ψ) ∧ Convex ℝ (obstacleSet Ω ψ) ∧
    StrictConvexOn ℝ (obstacleSet Ω ψ) (obstacleEnergy Ω f) ∧
    IsCoerciveFunctionalOn (obstacleEnergy Ω f) (obstacleSet Ω ψ) ∧
    Continuous (obstacleEnergy Ω f) ∧
    (∃! u, u ∈ obstacleSet Ω ψ ∧ IsMinOn (obstacleEnergy Ω f) (obstacleSet Ω ψ) u) ∧
    ∃! u, u ∈ obstacleSet Ω ψ ∧ ∀ v ∈ obstacleSet Ω ψ,
      ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
        f x * SobolevMultiIndex.fn ((v - u : SobolevEuclideanZero (d + 1) 1 2 Ω) :
          SobolevEuclidean (d + 1) 1 2 Ω) x
      ≤ ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
        ∑ i, SobolevMultiIndex.weakDeriv (u : SobolevEuclidean (d + 1) 1 2 Ω)
          (MultiIndexLE.single i) x
          * SobolevMultiIndex.weakDeriv ((v - u : SobolevEuclideanZero (d + 1) 1 2 Ω) :
            SobolevEuclidean (d + 1) 1 2 Ω) (MultiIndexLE.single i) x := by
  have hM := dirichletBilinForm_isBoundedWith Ω
  have hα := dirichletBilinForm_isEllipticWith Ω hR hΩ
  have hs := dirichletBilinForm_isSymm Ω
  have hpos : (0 : ℝ) < (1 + (2 * R) ^ 2)⁻¹ := by positivity
  have hne := obstacleSet_nonempty Ω hψ
  have hcl := isClosed_obstacleSet Ω ψ
  have hcv := convex_obstacleSet Ω ψ
  have hstrong : StrongConvexOn (obstacleSet Ω ψ) (1 + (2 * R) ^ 2)⁻¹ (obstacleEnergy Ω f) :=
    (SesqForm.strongConvexOn_energy ((BilinForm.isSymm_iff_isHermitian hM).mp hs)
      ((BilinForm.isEllipticWith_iff_isCoerciveWith hM).mp hα) (loadZero Ω f)).mono_of_univ hcv
  have hcont : Continuous (obstacleEnergy Ω f) :=
    SesqForm.continuous_energy ((dirichletBilinForm Ω).toCLM hM) (loadZero Ω f)
  obtain ⟨hmin, hvi⟩ := theorem_11_2_2_zero hM hpos hα hs (loadZero Ω f) hne hcl hcv
  refine ⟨hne, hcl, hcv, hstrong.strictConvexOn hpos,
    hstrong.isCoerciveFunctionalOn_of_continuous hpos hne hcont, hcont, hmin, ?_⟩
  have e : ∀ v w : SobolevEuclideanZero (d + 1) 1 2 Ω, dirichletBilinForm Ω v w
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
        ∑ i, SobolevMultiIndex.weakDeriv (v : SobolevEuclidean (d + 1) 1 2 Ω)
          (MultiIndexLE.single i) x
          * SobolevMultiIndex.weakDeriv (w : SobolevEuclidean (d + 1) 1 2 Ω)
            (MultiIndexLE.single i) x := fun v w ↦
    (dirichletBilinForm_apply Ω v w).trans (Elliptic.dirichletForm_apply Ω v w)
  simp only [e, loadZero_apply, ge_iff_le] at hvi
  exact hvi

end Obstacle

/-! ### Example 11.2.4: the simplified friction problem -/

section Friction

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))} (B : BoundaryData Ω) (𝒯 : B.TraceFamily)

/-- The Euclidean space $\mathbb{R}^N$, as local notation. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-- **Example 11.2.4** of [han2009theoretical] (the simplified friction problem). Let
$\Omega \subseteq \mathbb{R}^N$ be open, with boundary data $B$ (a surface measure $ds$ on
$\Gamma = \partial\Omega$) and a boundary trace $\gamma$ given by `𝒯 : B.TraceFamily`. Let
$g > 0$ and $f \in L^2(\Omega)$. Then the variational inequality (11.1.13),
$$u \in H^1(\Omega), \qquad \int_\Omega \bigl[\nabla u \cdot \nabla (v - u) + u (v - u)\bigr]
  dx + g \int_\Gamma \bigl(|\gamma v| - |\gamma u|\bigr) ds \ge \int_\Omega f (v - u) \, dx
  \quad \text{for all } v \in H^1(\Omega),$$
has exactly one solution.

**Reading.** The source poses the problem on a Lipschitz domain. Here the domain is any open set
with a boundary trace in the sense of `BoundaryData.TraceFamily`, for example a bounded $C^1$
domain or a polygon without slits.

The proof applies Theorem 11.2.2 on $V = H^1(\Omega)$ with $K = V$. The form $a(u, v) =
\int_\Omega (\nabla u \cdot \nabla v + u v)$ is `AtkinsonHan.Chapter11.frictionBilinForm`; it is
the inner product of $H^1(\Omega)$, so it is bounded, symmetric and $V$-elliptic with constant
$1$. The load is $\ell(v) = \int_\Omega f v$. The friction functional
$j(v) = g \int_\Gamma |\gamma v| \, ds$ is `AtkinsonHan.Chapter11.frictionFunctional`; it is
convex and continuous by `AtkinsonHan.Chapter11.convexOn_frictionFunctional` and
`AtkinsonHan.Chapter11.continuous_frictionFunctional`. The minimizer of the energy (11.1.12)
solves (11.1.13) by `AtkinsonHan.Chapter11.example_11_1_2`. -/
theorem example_11_2_4 {g : ℝ} (hg : 0 < g) (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) :
    ∃! u : SobolevEuclidean N 1 2 Ω, ∀ v : SobolevEuclidean N 1 2 Ω,
      ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn (v - u) x
        ≤ (∫ x in (Ω : Set 𝔼), ((∑ i, SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
            * SobolevMultiIndex.weakDeriv (v - u) (MultiIndexLE.single i) x)
            + SobolevMultiIndex.fn u x * SobolevMultiIndex.fn (v - u) x))
          + g * ∫ x, (|(𝒯.traceL 2 ENNReal.ofNat_ne_top v : 𝔼 → ℝ) x|
            - |(𝒯.traceL 2 ENNReal.ofNat_ne_top u : 𝔼 → ℝ) x|) ∂B.σ := by
  have hmin := theorem_11_2_2 frictionBilinForm_isBoundedWith one_pos
    frictionBilinForm_isEllipticWith frictionBilinForm_isSymm (Elliptic.load Ω f)
    (j := frictionFunctional B 𝒯 g) univ_nonempty isClosed_univ convex_univ
    (convexOn_frictionFunctional B 𝒯 hg.le)
    ((continuous_frictionFunctional B 𝒯 g).lowerSemicontinuous.lowerSemicontinuousOn univ)
  have e : (frictionBilinForm (Ω := Ω)).energy (Elliptic.load Ω f) + frictionFunctional B 𝒯 g
      = frictionEnergy B 𝒯 g f := rfl
  rw [e] at hmin
  obtain ⟨u, ⟨-, hu⟩, huniq⟩ := hmin
  refine ⟨u, (example_11_1_2 B 𝒯 hg f u).1 hu, fun y hy ↦ huniq y ⟨mem_univ _, ?_⟩⟩
  exact (example_11_1_2 B 𝒯 hg f y).2 hy

end Friction

end AtkinsonHan.Chapter11

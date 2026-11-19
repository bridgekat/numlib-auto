/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter12.Section02
import Numlib.Analysis.Convex.RelativeInterior
import NumlibSurface.ConnGouldToint.Chapter06.Section04
import NumlibSurface.ConnGouldToint.Chapter03.Section02
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Conn, Gould and Toint, Section 12.3: active constraints at limit points

This module formalizes Section 12.3 of [conn2000trust], which studies the active constraints of the
iterates of a projection-based trust-region method near its limit points. The feasible set is
$C = \{x : c_i(x) \ge 0 \text{ for all } i\}$ with finitely many constraints, and the active set at
$x$ is $\mathcal{A}(x) = \{i : c_i(x) = 0\}$. At a limit point $z$ the module assumes that the
active gradients are linearly independent (AO.1c) and that strict complementarity holds:
$\nabla f(z) = \sum_i \mu_i \nabla c_i(z)$ with $\mu_i > 0$ exactly on $\mathcal{A}(z)$, as in
(12.3.1). The relative-interior condition AO.4b gives these strictly positive multipliers, and
independence makes them unique. Under these conditions the active set is locally constant on the set
of limit points (Lemma 12.3.1), different active sets on a compact limit set are uniformly separated
(Lemma 12.3.2), and the iterates eventually stay near one component of the limit set (Theorem
12.3.3).

The main subject is Theorem 12.3.8, which asserts that the iterates and the generalized Cauchy
points eventually have the active set of the limit. The printed theorem and the subsequence claim of
Lemma 12.3.7 fail; the counterexamples are in
`NumlibSurface.ConnGouldToint.Chapter12.Section03Counterexample` and
`NumlibSurface.ConnGouldToint.Chapter12.Section03IterateCounterexample`. This module proves
corrected versions. The key estimate is a uniform lower bound on the tangent component
$\|P_{T(u)}[-\nabla f(x)]\|$ at points $u$ near $z$ with a different active set. At small radii it
gives a model decrease linear in the radius, so a Cauchy point with the wrong active set comes from
a very successful iteration. The module also proves Lemmas 12.3.5 and 12.3.6, Corollary 12.3.9 under
eventual identification, and a relaxed form of Theorem 12.3.4. The proofs use the projections and
cones of `Numlib.Optimization.ModelBased.ProjectedPath`, the normal-cone formula
`ConnGouldToint.Chapter03.theorem_3_2_10_normalCone`, and the run of Algorithm 6.1.1 in
`ConnGouldToint.Chapter06.BTRRun`.

## Main definitions

* `ConnGouldToint.Chapter12.activeConstraintSet`: the active set
  $\mathcal{A}(x) = \{i : c_i(x) = 0\}$.
* Equation (12.3.1), `ConnGouldToint.Chapter12.HasStrictActiveMultipliers`:
  $g(x) = \sum_i \mu_i n_i(x)$ with $\mu_i > 0$ on $\mathcal{A}(x)$ and $\mu_i = 0$ off it.

## Main results

* Lemma 12.3.1, `ConnGouldToint.Chapter12.lemma_12_3_1`: the active set is constant on a connected
  set of strictly complementary points with independent active normals.
* Lemma 12.3.2, `ConnGouldToint.Chapter12.lemma_12_3_2`: on a compact such set, points with
  different active sets are at distance at least some $\psi \in (0, 1)$.
* Theorem 12.3.3, `ConnGouldToint.Chapter12.theorem_12_3_3`: the iterates eventually lie in a
  $\delta$-neighborhood of a compact component of the limit set, in which no constraint inactive on
  the component becomes active.
* Theorem 12.3.4, `ConnGouldToint.Chapter12.theorem_12_3_4_relaxed`: a lower bound $\varepsilon$ on
  the capped criticality measure of the relaxed feasible set.
* Lemma 12.3.5, `ConnGouldToint.Chapter12.lemma_12_3_5`: at small radii an iteration that satisfies
  AA.1b is very successful and the radius does not decrease.
* Lemma 12.3.6, `ConnGouldToint.Chapter12.lemma_12_3_6`: projected gradients tend to zero at nearby
  feasible points with the active set of the limit set.
* Lemma 12.3.7, `ConnGouldToint.Chapter12.lemma_12_3_7_of_normal_certificates`: with a common active
  set on the limit set and normal certificates, infinitely many successful iterates have that active
  set.
* Theorem 12.3.8,
  `ConnGouldToint.Chapter12.theorem_12_3_8_of_compact_run_of_Cauchy_displacements_tendsto_zero`: in
  a compact run with vanishing Cauchy and iterate displacements, the late iterates and Cauchy points
  have the common active set of the limit points.
* Theorem 12.3.8, `ConnGouldToint.Chapter12.theorem_12_3_8_of_smooth_compact_run`: the same
  conclusion for continuously differentiable constraints and objective.
* Theorem 12.3.8,
  `ConnGouldToint.Chapter12.theorem_12_3_8_of_convergent_run_of_radius_tendsto_zero`: the same
  conclusion for a convergent run with vanishing radii.
* Corollary 12.3.9, `ConnGouldToint.Chapter12.corollary_12_3_9_of_eventually_active`: if the
  iterates eventually have the active set of the limit set, the projected gradients tend to zero.

## Conventions

* The constraints are $c_i \ge 0$ with $i$ in a finite type $\iota$, and
  $C = \{x : c_i(x) \ge 0 \text{ for all } i\}$ is `ConnGouldToint.Chapter03.AC7 C c`. AC.2
  (`ConnGouldToint.Chapter03.AC2`) says that $C$ is nonempty, closed and convex.
* $T(x)$ and $N(x)$ are the tangent and normal cones of $C$ at $x$ (`Optimization.tangentDirections`
  and `Optimization.normalDirections`), and $P_K$ is the projection onto a closed convex set $K$
  (`bestApprox`). The point $P_C[x - t \nabla f(x)]$ of the projected-gradient path (12.1.4) is
  `ConnGouldToint.Chapter12.projectedGradientPath C f x t`.
* The tangent qualification at $x$ is `ConnGouldToint.Chapter03.ActiveLinearizedConeMatches C c x`:
  the tangent cone of $C$ at $x$ is $\{d : Dc_i(x)\, d \ge 0 \text{ for all } i \in
  \mathcal{A}(x)\}$.
* A **supported normal representation** of $v$ at $u$ is a family $\mu$ with
  $v = \sum_i \mu_i n_i(u)$ and $\mu_i = 0$ for $i \notin \mathcal{A}(u)$. Several results take such
  representations of approximations of $g(x_k)$ as hypotheses ("normal certificates").
* AO.1c at $z$ is the linear independence of the active normals $(n_i(z))_{i \in \mathcal{A}(z)}$,
  and AO.4b at $z$ is $-\nabla f(z) \in \operatorname{ri} N(z)$, with `intrinsicInterior ℝ` for the
  relative interior.
* A run is `ConnGouldToint.Chapter06.BTRRun` with iterates $x_k$, steps $s_k$, radii $\Delta_k$ and
  models $m_k$, and $\rho_k$ is the ratio `ConnGouldToint.Chapter06.btrRatio`. An iteration is
  successful if $\rho_k \ge \eta_1$ and very successful if $\rho_k \ge \eta_2$.
* $\kappa_{\mathrm{up}} < \kappa_{\mathrm{lo}}$, $\kappa_{\mathrm{fr}}$ and $\kappa_{\mathrm{ep}}$
  are the constants of the generalized Cauchy point (12.2.1)–(12.2.4), the fields `upperSlope`,
  `lowerSlope`, `radiusFraction` and `endpointFactor` of
  `ConnGouldToint.Chapter12.GeneralizedCauchyParams`. The capped criticality measure (12.2.15) is
  $\pi_C(x) = \min\{1, \chi_C(x)\}$, where $\chi_C(x)$ is the criticality measure (12.1.13) with
  radius $1$.

## Deviations from the source

* **Representation.** The strict multiplier equivalence and uniqueness are proved separately from
  the smooth constraint representation. See
  `ConnGouldToint.Chapter12.strictActiveMultipliers_iff_mem_relint_normalDirections`,
  `ConnGouldToint.Chapter12.activeCoefficients_unique`,
  `ConnGouldToint.Chapter12.activeLinearizedConeMatches_of_activeGradient_independent`,
  `ConnGouldToint.Chapter12.strictActiveMultipliers_of_activeGradient_independent_of_mem_relint`.
* **Reading.** The projected-trial identification results specify displacement-to-time or bounded
  positive trial-time hypotheses. See
  `ConnGouldToint.Chapter12.eventually_tangentProjection_lower_of_active_mismatch`,
  `ConnGouldToint.Chapter12.eventually_activeConstraintSet_eq_of_projectedGradient_residual`,
  `ConnGouldToint.Chapter12.eventually_activeConstraintSet_eq_projectedGradientPath`,
  `ConnGouldToint.Chapter12.eventually_activeConstraintSet_eq_of_small_Cauchy_radius`.
* **Generalization.** The component geometry uses abstract continuous normal data and gives pairwise
  uniform separation of differing active sets. See
  `ConnGouldToint.Chapter12.eventually_activeConstraintSet_eq`,
  `ConnGouldToint.Chapter12.lemma_12_3_1`, `ConnGouldToint.Chapter12.lemma_12_3_2`.
* **Correction.** The corrected successful-subsequence and identification claims assume supported
  normal certificates. See
  `ConnGouldToint.Chapter12.eventually_activeConstraintSet_eq_of_compact_normal_certificates`,
  `ConnGouldToint.Chapter12.theorem_12_3_8_of_normal_certificates`,
  `ConnGouldToint.Chapter12.lemma_12_3_7_of_normal_certificates`.
* **Generalization.** The geometric trapping statement allows a compact superset of cluster points
  and chooses a late connected component per iterate. See
  `ConnGouldToint.Chapter12.activeConstraintSet_eq_on_limits_of_vanishing_steps`,
  `ConnGouldToint.Chapter12.theorem_12_3_3`.
* **Correction.** The pointwise comparison uses the relaxed feasible set and a shifted displacement;
  the full-domain comparison can fail. See
  `ConnGouldToint.Chapter12.relaxedCriticality_lower_bound_of_nearby`,
  `ConnGouldToint.Chapter12.theorem_12_3_4_relaxed`,
  `ConnGouldToint.Chapter12.missing_active_local_criticality_counterexample`.
* **Reading.** The trial proof steps make the tangent lower bound, radius and model controls, and
  face preservation explicit. See
  `ConnGouldToint.Chapter12.cauchyDecrease_linear_of_tangentProjection_lower`,
  `ConnGouldToint.Chapter12.radius_le_mul_displacement_of_tangentProjection_lower`,
  `ConnGouldToint.Chapter12.eventually_verySuccessful_of_active_mismatch`,
  `ConnGouldToint.Chapter12.frequently_active_eq_at_Cauchy_trial_of_radius_tendsto_zero`,
  `ConnGouldToint.Chapter12.prediction_le_of_common_center`,
  `ConnGouldToint.Chapter12.eventually_CauchyTrial_preserves_active_face`,
  `ConnGouldToint.Chapter12.eventually_rejection_then_identified`,
  `ConnGouldToint.Chapter12.frequently_successful_identified_of_radius_tendsto_zero`.
* **Correction.** The eventual identification variants impose explicit displacement, radius, or
  trial-time conditions absent from the printed theorem. See
  `ConnGouldToint.Chapter12.theorem_12_3_8_of_compact_run_of_Cauchy_displacements_tendsto_zero`,
  `ConnGouldToint.Chapter12.theorem_12_3_8_of_smooth_compact_run`,
  `ConnGouldToint.Chapter12.theorem_12_3_8_of_compact_run_of_trial_displacements_tendsto_zero`,
  `ConnGouldToint.Chapter12.theorem_12_3_8_of_compact_run_of_radius_tendsto_zero`,
  `ConnGouldToint.Chapter12.theorem_12_3_8_of_convergent_run_of_radius_tendsto_zero`,
  `ConnGouldToint.Chapter12.theorem_12_3_8_of_bounded_trial_times`.
* **Representation.** The small-radius success lemma takes the Taylor error bound and model decrease
  directly. See `ConnGouldToint.Chapter12.lemma_12_3_5`.
* **Reading.** The projected-gradient limit uses explicit active-set hypotheses; the corollary
  assumes eventual identification. See `ConnGouldToint.Chapter12.lemma_12_3_6`,
  `ConnGouldToint.Chapter12.corollary_12_3_9_of_eventually_active`.
* **Theorem 12.3.4** (correction). The local comparison bounds the criticality measure of the
  relaxed feasible set, with a shifted displacement; a half-line example shows that the trial
  conditions alone do not give the bound for the full feasible set. See
  `ConnGouldToint.Chapter12.theorem_12_3_4_relaxed` and
  `ConnGouldToint.Chapter12.missing_active_local_criticality_counterexample`.
* **Lemma 12.3.7** (correction). The subsequence claim fails; it holds when the limit set has a
  common active set and the iterates carry asymptotically accurate normal certificates. See
  `ConnGouldToint.Chapter12.lemma_12_3_7_of_normal_certificates`.
* **Theorem 12.3.8** (correction). Eventual identification fails at the Cauchy points for
  nonvanishing radii and at the iterates for constant radii. The corrected versions assume normal
  certificates, vanishing radii, vanishing Cauchy and iterate displacements, vanishing trial
  displacements, or bounded positive trial times. See
  `ConnGouldToint.Chapter12.theorem_12_3_8_of_compact_run_of_Cauchy_displacements_tendsto_zero`.
* **Corollary 12.3.9** (correction). The corollary assumes that the iterates eventually have the
  active set of the limit set, which the printed Theorem 12.3.8 does not provide. See
  `ConnGouldToint.Chapter12.corollary_12_3_9_of_eventually_active`.
-/

open Filter Topology
open scoped RealInnerProductSpace Matrix

namespace ConnGouldToint.Chapter12

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Section 12.3** of [conn2000trust], active set. For constraints $c_i : E \to \mathbb{R}$, the
**active set** at $x$ is the set of indices of the constraints that vanish there:
$$\mathcal{A}(x) = \{i : c_i(x) = 0\}.$$
-/
def activeConstraintSet (c : ι → E → ℝ) (x : E) : Set ι := {i | c i x = 0}

/-- **Equation (12.3.1)** of [conn2000trust]. Let $c_i : E \to \mathbb{R}$ be constraints,
$n_i : E \to E$ vector fields and $g : E \to E$. The field $g$ has **strictly positive active
multipliers** at $x$ if there is $\mu \in \mathbb{R}^\iota$ with
$$g(x) = \sum_i \mu_i\, n_i(x), \qquad \mu_i > 0 \text{ for } i \in \mathcal{A}(x), \qquad
  \mu_i = 0 \text{ for } i \notin \mathcal{A}(x).$$

With $n_i = \nabla c_i$ and $g = \nabla f$, this is the stationarity condition (12.3.1) with
strict complementarity, in the convention $c_i \ge 0$ of the source; AO.1c and AO.4b imply it.
The fields $n_i$ are the inward constraint gradients. -/
def HasStrictActiveMultipliers [Fintype ι] (c : ι → E → ℝ) (n : ι → E → E)
    (g : E → E) (x : E) : Prop :=
  ∃ μ : ι → ℝ, g x = ∑ i, μ i • n i x ∧
    (∀ i ∈ activeConstraintSet c x, 0 < μ i) ∧
    ∀ i ∉ activeConstraintSet c x, μ i = 0

open Optimization ConvexAnalysis in
/-- **Section 12.3** of [conn2000trust], AO.4b and the multipliers (12.3.1). Let $E$ be a
finite-dimensional real inner product space, let $C$ satisfy AC.2 and AC.7 for the constraints
$c_i$, let $x \in C$, and let the tangent qualification hold at $x$. Then $g$ has strictly
positive active multipliers with respect to the gradients $\nabla c_i$ at $x$ if and only if
$$-g(x) \in \operatorname{ri} N(x).$$

The equivalence needs no independence of the active gradients. The proof uses the normal-cone
formula `ConnGouldToint.Chapter03.theorem_3_2_10_normalCone`.

**Reading.** The multiplier argument separates the tangent qualification, relative-interior
equivalence and uniqueness from the smooth feasible-set description that implies these hypotheses.
-/
theorem strictActiveMultipliers_iff_mem_relint_normalDirections [Fintype ι]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    {C : Set E} {c : ι → E → ℝ} {g : E → E} {x : E}
    (hC : Chapter03.AC2 C) (hset : Chapter03.AC7 C c) (hx : x ∈ C)
    (hQ : Chapter03.ActiveLinearizedConeMatches C c x) :
    HasStrictActiveMultipliers c (fun i ↦ gradient (c i)) g x ↔
      -g x ∈ intrinsicInterior ℝ (normalDirections C x) := by
  classical
  let J := {i : ι // c i x = 0}
  let A := Fintype.linearCombination ℝ (fun i : J ↦ -gradient (c i) x)
  let orthant := Set.univ.pi (fun _ : J ↦ Set.Ici (0 : ℝ))
  have horthant : Convex ℝ orthant := by
    intro p hp q hq a b ha hb _
    simp only [orthant, Set.mem_univ_pi, Set.mem_Ici] at hp hq ⊢
    intro i
    exact add_nonneg (mul_nonneg ha (hp i)) (mul_nonneg hb (hq i))
  have hx' : ∀ i, 0 ≤ c i x := by rwa [hset] at hx
  have hN : normalDirections C x = A '' orthant := by
    ext y
    rw [Chapter03.theorem_3_2_10_normalCone hC hset hx' hQ y]
    simp only [Set.mem_image, orthant, Set.mem_univ_pi, Set.mem_Ici,
      A, Fintype.linearCombination_apply]
    rfl
  rw [hN, horthant.relint_image A]
  have hri : intrinsicInterior ℝ orthant = Set.univ.pi (fun _ : J ↦ Set.Ioi (0 : ℝ)) := by
    dsimp only [orthant]
    rw [Convex.relint_univ_pi _ (fun _ ↦ convex_Ici _)]
    simp only [intrinsicInterior_Ici]
  rw [hri]
  simp only [Set.mem_image, Set.mem_univ_pi, Set.mem_Ioi, A, Fintype.linearCombination_apply,
    smul_neg, Finset.sum_neg_distrib, neg_inj]
  constructor
  · rintro ⟨μ, hμ, hpos, hzero⟩
    refine ⟨fun i : J ↦ μ i, fun i ↦ hpos _ i.2, ?_⟩
    have hsumzero : (∑ i : {i // c i x ≠ 0}, μ i • gradient (c i) x) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [hzero i i.2, zero_smul]
    have hsum := Fintype.sum_subtype_add_sum_subtype (fun i ↦ c i x = 0)
      (fun i ↦ μ i • gradient (c i) x)
    rw [hsumzero, add_zero] at hsum
    exact hsum.trans hμ.symm
  · rintro ⟨μ, hpos, hμ⟩
    let m (i : ι) := if hi : c i x = 0 then μ ⟨i, hi⟩ else 0
    have hsumzero : (∑ i : {i // c i x ≠ 0}, m i • gradient (c i) x) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      simp [m, i.2]
    have hsum : (∑ i : J, μ i • gradient (c i) x) = ∑ i, m i • gradient (c i) x := by
      rw [← Fintype.sum_subtype_add_sum_subtype (fun i ↦ c i x = 0), hsumzero, add_zero]
      apply Finset.sum_congr rfl
      intro i _
      simp [m, i.2]
    refine ⟨m, hμ.symm.trans hsum, fun i hi ↦ ?_, fun i hi ↦ dite_eq_right hi⟩
    change c i x = 0 at hi
    simpa only [m, dite_eq_left hi] using hpos ⟨i, hi⟩

/-- **Equation (12.3.1)** of [conn2000trust], uniqueness of the multipliers. Let the active normals
$(n_i(x))_{i \in \mathcal{A}(x)}$ be linearly independent, and let
$\mu, \nu \in \mathbb{R}^\iota$ vanish outside $\mathcal{A}(x)$. If
$\sum_i \mu_i n_i(x) = \sum_i \nu_i n_i(x)$, then $\mu = \nu$.

**Reading.** The multiplier argument separates the tangent qualification, relative-interior
equivalence and uniqueness from the smooth feasible-set description that implies these hypotheses.
-/
theorem activeCoefficients_unique [Fintype ι] {c : ι → E → ℝ} {n : ι → E → E}
    {x : E} {μ ν : ι → ℝ}
    (hind : LinearIndependent ℝ (fun i : activeConstraintSet c x ↦ n i x))
    (hμ : ∀ i ∉ activeConstraintSet c x, μ i = 0)
    (hν : ∀ i ∉ activeConstraintSet c x, ν i = 0)
    (he : (∑ i, μ i • n i x) = ∑ i, ν i • n i x) : μ = ν := by
  classical
  let J := activeConstraintSet c x
  have hsum (w : ι → ℝ) (hw : ∀ i ∉ J, w i = 0) :
      (∑ i : J, w i • n i x) = ∑ i, w i • n i x := by
    have hz : (∑ i : {i // i ∉ J}, w i • n i x) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [hw i i.2, zero_smul]
    simpa only [hz, add_zero] using
      Fintype.sum_subtype_add_sum_subtype (· ∈ J) (fun i ↦ w i • n i x)
  have hj : LinearIndependent ℝ (fun i : J ↦ n i x) := hind
  have hA := linearIndependent_iff_injective_fintypeLinearCombination.mp hj
  have hr : (fun i : J ↦ μ i) = fun i : J ↦ ν i := by
    apply hA
    rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply]
    change (∑ i : J, μ i • n i x) = ∑ i : J, ν i • n i x
    rw [hsum μ hμ, hsum ν hν, he]
  funext i
  by_cases hi : i ∈ J
  · exact congrFun hr ⟨i, hi⟩
  · rw [hμ i hi, hν i hi]

omit [InnerProductSpace ℝ E] in
private theorem eventually_activeConstraintSet_subset_of_tendsto [Finite ι]
    {α : Type*} {l : Filter α} {c : ι → E → ℝ} {u : α → E} {z : E}
    (hc : ∀ i, Continuous (c i)) (hu : Tendsto u l (𝓝 z)) :
    ∀ᶠ k in l, activeConstraintSet c (u k) ⊆ activeConstraintSet c z := by
  refine (eventually_all.mpr fun i ↦ ?_).mono fun _ h i ↦ h i
  by_cases hi : c i z = 0
  · exact .of_forall fun _ _ ↦ hi
  · have he := ((hc i).continuousAt.tendsto.comp hu).eventually
      ((show IsOpen {r : ℝ | r ≠ 0} from isOpen_ne).mem_nhds hi)
    exact he.mono fun _ hk hzero ↦ (hk hzero).elim

/-- **Section 12.3** of [conn2000trust], active-set perturbation. Let the $c_i$ and $n_i$ be
continuous, let the active normals at $x$ be linearly independent, and let $g$ have strictly
positive active multipliers at $x$. Then for every pair $(y, v)$ close enough to $(x, g(x))$: if
$v$ has a supported normal representation $v = \sum_i \mu_i n_i(y)$ with $\mu_i = 0$ for
$i \notin \mathcal{A}(y)$, then $\mathcal{A}(y) = \mathcal{A}(x)$.

The represented vector $v$ may differ from $g(y)$; it only has to be close to $g(x)$. -/
theorem eventually_activeConstraintSet_eq_of_normal_representation [Fintype ι]
    {c : ι → E → ℝ} {n : ι → E → E} {g : E → E} {x : E}
    (hc : ∀ i, Continuous (c i)) (hn : ∀ i, Continuous (n i))
    (hind : LinearIndependent ℝ (fun i : activeConstraintSet c x ↦ n i x))
    (hmul : HasStrictActiveMultipliers c n g x) :
    ∀ᶠ y : E × E in 𝓝 (x, g x),
      (∃ μ : ι → ℝ, y.2 = ∑ i, μ i • n i y.1 ∧
        ∀ i ∉ activeConstraintSet c y.1, μ i = 0) →
      activeConstraintSet c y.1 = activeConstraintSet c x := by
  classical
  let w₀ : E × E := (x, g x)
  let J := activeConstraintSet c x
  have hsub : ∀ᶠ y in 𝓝 x, activeConstraintSet c y ⊆ J :=
    eventually_activeConstraintSet_subset_of_tendsto hc tendsto_id
  let G (y : E × E) : Matrix J J ℝ := Matrix.gram ℝ (fun i : J ↦ n i y.1)
  let rhs (y : E × E) (i : J) := ⟪n i y.1, y.2⟫
  let a (y : E × E) := (G y)⁻¹ *ᵥ rhs y
  have hG : Continuous G := continuous_matrix fun i j ↦
    ((hn i).comp continuous_fst).inner ((hn j).comp continuous_fst)
  have hdet : (G w₀).det ≠ 0 := (Matrix.det_gram_ne_zero_iff_linearIndependent).mpr hind
  have hdnear : ∀ᶠ y in 𝓝 w₀, (G y).det ≠ 0 :=
    hG.matrix_det.continuousAt ((show IsOpen {y : ℝ | y ≠ 0} from isOpen_ne).mem_nhds hdet)
  have hGi : ContinuousAt (fun y ↦ (G y)⁻¹) w₀ := by
    apply (continuousAt_matrix_inv (G w₀) ?_).comp hG.continuousAt
    change ContinuousAt (fun y : ℝ ↦ Ring.inverse y) (G w₀).det
    simp_rw [Ring.inverse_eq_inv]
    exact continuousAt_inv₀ hdet
  have ha (i : J) : ContinuousAt (fun y ↦ a y i) w₀ := by
    change ContinuousAt (fun y ↦ ∑ j : J, (G y)⁻¹ i j * rhs y j) w₀
    apply tendsto_finsetSum _ fun j _ ↦ ?_
    have hrhs : ContinuousAt (fun y : E × E ↦ ⟪n j y.1, y.2⟫) w₀ :=
      (((hn j).comp continuous_fst).inner continuous_snd).continuousAt
    exact ((continuous_apply j).continuousAt.comp
      ((continuous_apply i).continuousAt.comp hGi)).mul hrhs
  have hcoef (y : E × E) (hJ : activeConstraintSet c y.1 ⊆ J) (hdet' : (G y).det ≠ 0)
      (μ : ι → ℝ) (hstat : y.2 = ∑ i, μ i • n i y.1)
      (hzero : ∀ i ∉ activeConstraintSet c y.1, μ i = 0) :
      a y = fun i : J ↦ μ i := by
    let μJ : J → ℝ := fun i ↦ μ i
    have hsum : (∑ i : J, μ i • n i y.1) = ∑ i, μ i • n i y.1 := by
      have hzero' : (∑ i : {i // i ∉ J}, μ i • n i y.1) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [hzero i (fun hai ↦ i.2 (hJ hai)), zero_smul]
      simpa only [hzero', add_zero] using
        Fintype.sum_subtype_add_sum_subtype (· ∈ J) (fun i ↦ μ i • n i y.1)
    have hnormal : G y *ᵥ μJ = rhs y := by
      funext i
      change (∑ j : J, ⟪n i y.1, n j y.1⟫ * μ j) = ⟪n i y.1, y.2⟫
      rw [hstat, ← hsum, inner_sum]
      simp only [real_inner_smul_right, mul_comm]
    change (G y)⁻¹ *ᵥ rhs y = μJ
    rw [← hnormal, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet'),
      Matrix.one_mulVec]
  obtain ⟨μ, hμ, hμpos, hμzero⟩ := hmul
  have hax := hcoef w₀ (fun _ hi ↦ hi) hdet μ hμ hμzero
  have hposnear : ∀ᶠ y in 𝓝 w₀, ∀ i : J, 0 < a y i := by
    apply eventually_all.mpr
    intro i
    have hi : 0 < a w₀ i := by rw [hax]; exact hμpos i i.2
    exact (ha i).eventually (lt_mem_nhds hi)
  have hfst : Tendsto (Prod.fst : E × E → E) (𝓝 w₀) (𝓝 x) :=
    continuous_fst.continuousAt
  have hsub' : ∀ᶠ y : E × E in 𝓝 w₀, activeConstraintSet c y.1 ⊆ J :=
    hfst.eventually hsub
  filter_upwards [hsub', hdnear, hposnear] with y hyJ hyd hypos
  intro hy
  refine Set.Subset.antisymm hyJ ?_
  intro i hi
  obtain ⟨ν, hν, hνzero⟩ := hy
  have haν := hcoef y hyJ hyd ν hν hνzero
  have hi' := hypos ⟨i, hi⟩
  rw [haν] at hi'
  exact not_not.mp fun hn ↦ hi'.ne' (hνzero i hn)

/-- **Section 12.3** of [conn2000trust], sequential active-set identification. Let the $c_i$ and
$n_i$ be continuous, let the active normals at $x$ be linearly independent, and let $g$ have
strictly positive active multipliers at $x$. Let $u_k \to x$ and $v_k \to g(x)$ along a filter,
and suppose that eventually $v_k$ has a supported normal representation at $u_k$. Then
eventually $\mathcal{A}(u_k) = \mathcal{A}(x)$. -/
theorem eventually_activeConstraintSet_eq_of_tendsto [Fintype ι] {α : Type*}
    {l : Filter α} {u v : α → E} {c : ι → E → ℝ} {n : ι → E → E}
    {g : E → E} {x : E}
    (hc : ∀ i, Continuous (c i)) (hn : ∀ i, Continuous (n i))
    (hind : LinearIndependent ℝ (fun i : activeConstraintSet c x ↦ n i x))
    (hmul : HasStrictActiveMultipliers c n g x)
    (hu : Tendsto u l (𝓝 x)) (hv : Tendsto v l (𝓝 (g x)))
    (hrep : ∀ᶠ k in l, ∃ μ : ι → ℝ, v k = ∑ i, μ i • n i (u k) ∧
      ∀ i ∉ activeConstraintSet c (u k), μ i = 0) :
    ∀ᶠ k in l, activeConstraintSet c (u k) = activeConstraintSet c x := by
  filter_upwards [(hu.prodMk_nhds hv).eventually
    (eventually_activeConstraintSet_eq_of_normal_representation hc hn hind hmul), hrep]
    with k hnear hrep
  exact hnear hrep

/-- **Section 12.3** of [conn2000trust], persistence of AO.1c. Let the $c_i$ and $n_i$ be
continuous, and let the active normals $(n_i(x))_{i \in \mathcal{A}(x)}$ be linearly
independent. Then for every $y$ near $x$ the active normals $(n_i(y))_{i \in \mathcal{A}(y)}$
are linearly independent.

Near $x$ the inactive constraints stay inactive, so $\mathcal{A}(y) \subseteq \mathcal{A}(x)$,
and the Gram matrix of the normals indexed by $\mathcal{A}(x)$ stays nonsingular. -/
theorem eventually_activeGradient_independent [Finite ι] {c : ι → E → ℝ}
    {n : ι → E → E} {x : E}
    (hc : ∀ i, Continuous (c i)) (hn : ∀ i, Continuous (n i))
    (hind : LinearIndependent ℝ (fun i : activeConstraintSet c x ↦ n i x)) :
    ∀ᶠ y in 𝓝 x, LinearIndependent ℝ (fun i : activeConstraintSet c y ↦ n i y) := by
  classical
  have := Fintype.ofFinite ι
  let J := activeConstraintSet c x
  let G (y : E) : Matrix J J ℝ := Matrix.gram ℝ (fun i : J ↦ n i y)
  have hG : Continuous G := continuous_matrix fun i j ↦ (hn i).inner (hn j)
  have hdet : (G x).det ≠ 0 := Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hind
  have hnear : ∀ᶠ y in 𝓝 x, (G y).det ≠ 0 :=
    hG.matrix_det.continuousAt ((show IsOpen {r : ℝ | r ≠ 0} from isOpen_ne).mem_nhds hdet)
  have hsub := eventually_activeConstraintSet_subset_of_tendsto hc (tendsto_id (x := 𝓝 x))
  filter_upwards [hnear, hsub] with y hy hJy
  let j (i : activeConstraintSet c y) : J := ⟨i, hJy i.2⟩
  have hj : Function.Injective j := fun _ _ h ↦ Subtype.ext (congrArg (fun z : J ↦ (z : ι)) h)
  exact (Matrix.det_gram_ne_zero_iff_linearIndependent.mp hy).comp j hj

/-- **Section 12.3** of [conn2000trust], the tangent qualification from AC.1, AC.7 and AO.1c. Let
$E$ be a finite-dimensional real inner product space, let $C$ satisfy AC.7 for the constraints
$c_i$, and let $x \in C$. Suppose that each $c_i$ is strictly differentiable at $x$ and that the
active gradients $(\nabla c_i(x))_{i \in \mathcal{A}(x)}$ are linearly independent. Then the
tangent qualification holds at $x$: the tangent cone of $C$ at $x$ is $\{d : Dc_i(x)\, d \ge 0
\text{ for all } i \in \mathcal{A}(x)\}$.

The tangent cone is Mathlib's `posTangentConeAt`.

**Reading.** The multiplier argument separates the tangent qualification, relative-interior
equivalence and uniqueness from the smooth feasible-set description that implies these hypotheses.
-/
theorem activeLinearizedConeMatches_of_activeGradient_independent [Fintype ι]
    [CompleteSpace E] [FiniteDimensional ℝ E] {C : Set E} {c : ι → E → ℝ} {x : E}
    (hset : Chapter03.AC7 C c) (hx : x ∈ C)
    (hc : ∀ i, HasStrictFDerivAt (c i) (fderiv ℝ (c i) x) x)
    (hind : LinearIndependent ℝ (fun i : activeConstraintSet c x ↦ gradient (c i) x)) :
    Chapter03.ActiveLinearizedConeMatches C c x := by
  classical
  have hfeas : ∀ i, 0 ≤ c i x := by rwa [hset] at hx
  intro d
  constructor
  · intro hd i hi
    have hmin : IsMinOn (c i) C x := by
      apply isMinOn_iff.mpr
      intro y hy
      rw [hset] at hy
      simpa only [hi] using (show ∀ j, 0 ≤ c j y from hy) i
    exact hmin.isLocalMinOn.hasFDerivWithinAt_nonneg
      (hc i).hasFDerivAt.hasFDerivWithinAt hd
  · intro hd
    let h : Empty → E → ℝ := Empty.elim
    let h' : Empty → E → E →L[ℝ] ℝ := Empty.elim
    let g (i : ι) (y : E) := -c i y
    let g' (i : ι) (_ : E) := -fderiv ℝ (c i) x
    have hactive : Constrained.activeSet g x = activeConstraintSet c x := by
      ext i
      simp [Constrained.activeSet, activeConstraintSet, g]
    have hset' : Constrained.feasible h g = C := by
      rw [hset]
      ext y
      simp [Constrained.feasible, g]
    let R := (InnerProductSpace.toDual ℝ E).toLinearEquiv
    have hi : LinearIndependent ℝ (fun i : activeConstraintSet c x ↦
        -fderiv ℝ (c i) x) := by
      have hmap := hind.map' R.toLinearMap (LinearMap.ker_eq_bot.mpr R.injective)
      have he : R.toLinearMap ∘ (fun i : activeConstraintSet c x ↦ gradient (c i) x) =
          fun i : activeConstraintSet c x ↦ fderiv ℝ (c i) x := by
        funext i
        exact toDual_gradient
      rw [he] at hmap
      exact hmap.neg
    have hi' : LinearIndependent ℝ (fun i : Constrained.activeSet g x ↦ g' i x) := by
      rw [hactive]
      exact hi
    have hreg : Constrained.IsRegularPointIneq h h' g g' x := by
      refine ⟨fun i ↦ i.elim, fun i ↦ neg_nonpos.mpr (hfeas i), ?_⟩
      have he : Sum.elim (fun i ↦ h' i x) (fun i : Constrained.activeSet g x ↦ g' i x) =
          (fun i : Constrained.activeSet g x ↦ g' i x) ∘ Equiv.emptySum Empty _ := by
        funext i
        cases i with
        | inl i => exact i.elim
        | inr i => simp
      rw [he]
      exact hi'.comp _ (Equiv.emptySum Empty _).injective
    rw [← hset']
    exact Constrained.mem_posTangentConeAt_of_isRegularPointIneq hreg
      (fun i ↦ i.elim) (fun i ↦ (hc i).neg) (fun i ↦ i.elim)
      (fun i hi ↦ by
        rw [hactive] at hi
        exact neg_nonpos.mpr (hd i hi))

open Optimization in
/-- **Equation (12.3.1)** of [conn2000trust], from AC.1, AC.2, AC.7, AO.1c and AO.4b. Let $E$ be a
finite-dimensional real inner product space, let $C$ satisfy AC.2 and AC.7, let $x \in C$, let
each $c_i$ be strictly differentiable at $x$, and let the active gradients at $x$ be linearly
independent. If $-g(x) \in \operatorname{ri} N(x)$, then $g$ has strictly positive active
multipliers with respect to the gradients $\nabla c_i$ at $x$.

The proof combines
`ConnGouldToint.Chapter12.activeLinearizedConeMatches_of_activeGradient_independent` and
`ConnGouldToint.Chapter12.strictActiveMultipliers_iff_mem_relint_normalDirections`.

**Reading.** The multiplier argument separates the tangent qualification, relative-interior
equivalence and uniqueness from the smooth feasible-set description that implies these hypotheses.
-/
theorem strictActiveMultipliers_of_activeGradient_independent_of_mem_relint
    [Fintype ι] [CompleteSpace E] [FiniteDimensional ℝ E]
    {C : Set E} {c : ι → E → ℝ} {g : E → E} {x : E}
    (hC : Chapter03.AC2 C) (hset : Chapter03.AC7 C c) (hx : x ∈ C)
    (hc : ∀ i, HasStrictFDerivAt (c i) (fderiv ℝ (c i) x) x)
    (hind : LinearIndependent ℝ (fun i : activeConstraintSet c x ↦ gradient (c i) x))
    (hri : -g x ∈ intrinsicInterior ℝ (normalDirections C x)) :
    HasStrictActiveMultipliers c (fun i ↦ gradient (c i)) g x :=
  (strictActiveMultipliers_iff_mem_relint_normalDirections hC hset hx
    (activeLinearizedConeMatches_of_activeGradient_independent hset hx hc hind)).mpr hri

open Optimization in
private theorem exists_activeCoefficients_of_neg_mem_normal
    [Fintype ι] [CompleteSpace E] [FiniteDimensional ℝ E]
    {C : Set E} {c : ι → E → ℝ} {u v : E}
    (hC : Chapter03.AC2 C) (hset : Chapter03.AC7 C c) (hu : u ∈ C)
    (hQ : Chapter03.ActiveLinearizedConeMatches C c u)
    (hvn : -v ∈ normalDirections C u) :
    ∃ μ : ι → ℝ, v = ∑ i, μ i • gradient (c i) u ∧
      ∀ i ∉ activeConstraintSet c u, μ i = 0 := by
  classical
  have hfeas : ∀ i, 0 ≤ c i (u) := by
    rw [hset] at hu
    exact hu
  obtain ⟨μ, _, hμ⟩ := (Chapter03.theorem_3_2_10_normalCone hC hset hfeas hQ (-v)).mp hvn
  let m (i : ι) := if hi : c i (u) = 0 then μ ⟨i, hi⟩ else 0
  have hzsum : (∑ i : {i // c i (u) ≠ 0}, m i • gradient (c i) (u)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp [m, i.2]
  have hsum : (∑ i : {i // c i (u) = 0}, μ i • gradient (c i) (u)) =
      ∑ i, m i • gradient (c i) (u) := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun i ↦ c i (u) = 0), hzsum, add_zero]
    apply Finset.sum_congr rfl
    intro i _
    simp [m, i.2]
  refine ⟨m, ?_, fun i hi ↦ dite_eq_right hi⟩
  rw [← hsum]
  simpa only [smul_neg, Finset.sum_neg_distrib, neg_inj, eq_comm] using hμ

open Optimization ConvexAnalysis in
private theorem sub_tangentProjection_mem_normal [CompleteSpace E] (C : Set E) (u d : E) :
    d - bestApprox (tangentDirections C u) d ∈ normalDirections C u := by
  let K := tangentDirections C u
  let p := bestApprox K d
  have hzero : (0 : E) ∈ K := by simp [K, tangentDirections, mem_polarCone]
  have hcl : IsClosed K := isClosed_polarCone
  have hconv : Convex ℝ K := convex_polarCone _ _
  have hp : p ∈ K := bestApprox_mem ⟨0, hzero⟩ hcl hconv d
  have hvar := inner_sub_bestApprox_le_zero ⟨0, hzero⟩ hcl hconv d
  have h2p : (2 : ℝ) • p ∈ K := by
    apply mem_polarCone.mpr
    intro n hn
    rw [innerₗ_apply_apply, real_inner_smul_right]
    exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) (mem_polarCone.mp hp n hn)
  have horth : ⟪d - p, p⟫ = 0 := by
    have hlo := hvar 0 hzero
    have hhi := hvar ((2 : ℝ) • p) h2p
    change ⟪d - p, 0 - p⟫ ≤ 0 at hlo
    change ⟪d - p, (2 : ℝ) • p - p⟫ ≤ 0 at hhi
    rw [zero_sub, inner_neg_right] at hlo
    rw [inner_sub_right, real_inner_smul_right] at hhi
    linarith
  apply mem_normalDirections.mpr
  intro y hy
  have hdir : y - u ∈ K := by
    exact mem_polarCone.mpr fun n hn ↦ mem_normalDirections.mp hn y hy
  have hh := hvar (y - u) hdir
  change ⟪d - p, y - u - p⟫ ≤ 0 at hh
  rwa [inner_sub_right, horth, sub_zero] at hh

open Optimization in
/-- **Section 12.3** of [conn2000trust], tangent-gradient gap. Let $E$ be a finite-dimensional real
inner product space, let $C$ satisfy AC.2 and AC.7, and let $c_i$, $\nabla c_i$ and $\nabla f$
be continuous. At $z$ let the active gradients be linearly independent, and let $\nabla f$ have
strictly positive active multipliers with respect to the $\nabla c_i$. Let $x_k \to z$ and
$u_k \to z$ along a filter, and suppose that eventually $u_k \in C$ and the tangent
qualification holds at $u_k$. Then there is $\gamma > 0$ such that eventually
$$\mathcal{A}(u_k) \neq \mathcal{A}(z) \implies \gamma \le \|P_{T(u_k)}[-\nabla f(x_k)]\|.$$

The gradient is evaluated at the separate sequence $x_k$ of base points.

**Reading.** Identification is obtained from asymptotically accurate projection certificates near
the limit. The concrete forms use vanishing normalized displacement, trial times bounded away from
zero and infinity, or vanishing radii with radius-to-time ratio tending to zero.
-/
theorem eventually_tangentProjection_lower_of_active_mismatch
    [Fintype ι] [CompleteSpace E] [FiniteDimensional ℝ E] {α : Type*}
    {l : Filter α} {C : Set E} {c : ι → E → ℝ} {f : E → ℝ}
    {x u : α → E} {z : E}
    (hC : Chapter03.AC2 C) (hset : Chapter03.AC7 C c)
    (hc : ∀ i, Continuous (c i)) (hn : ∀ i, Continuous (gradient (c i)))
    (hg : Continuous (gradient f))
    (hind : LinearIndependent ℝ (fun i : activeConstraintSet c z ↦ gradient (c i) z))
    (hmul : HasStrictActiveMultipliers c (fun i ↦ gradient (c i)) (gradient f) z)
    (hx : Tendsto x l (𝓝 z)) (hu : Tendsto u l (𝓝 z))
    (hfeas : ∀ᶠ k in l, u k ∈ C)
    (hQ : ∀ᶠ k in l, Chapter03.ActiveLinearizedConeMatches C c (u k)) :
    ∃ γ > 0, ∀ᶠ k in l, activeConstraintSet c (u k) ≠ activeConstraintSet c z →
      γ ≤ ‖bestApprox (tangentDirections C (u k)) (-gradient f (x k))‖ := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (eventually_activeConstraintSet_eq_of_normal_representation hc hn hind hmul)
  have hgx := hg.continuousAt.tendsto.comp hx
  refine ⟨ε / 2, half_pos hε, ?_⟩
  filter_upwards [hu.eventually (Metric.ball_mem_nhds z hε),
    hgx.eventually (Metric.ball_mem_nhds (gradient f z) (half_pos hε)), hfeas, hQ]
    with k huk hgk hk hQk
  intro hneq
  by_contra! hs
  let p := bestApprox (tangentDirections C (u k)) (-gradient f (x k))
  let v := gradient f (x k) + p
  have hv : (u k, v) ∈ Metric.ball (z, gradient f z) ε := by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    refine ⟨huk, ?_⟩
    have hgk' : ‖gradient f (x k) - gradient f z‖ < ε / 2 := by
      simpa only [Metric.mem_ball, dist_eq_norm, Function.comp_apply] using hgk
    change dist v (gradient f z) < ε
    rw [dist_eq_norm, show v - gradient f z = (gradient f (x k) - gradient f z) + p by
      dsimp [v]; abel]
    exact (norm_add_le _ _).trans_lt (by linarith only [hgk', hs])
  have hvn : -v ∈ normalDirections C (u k) := by
    simpa only [v, neg_add, ← sub_eq_add_neg, p] using
      sub_tangentProjection_mem_normal C (u k) (-gradient f (x k))
  exact hneq (hball hv (exists_activeCoefficients_of_neg_mem_normal hC hset hk hQk hvn))

open Optimization in
/-- **Section 12.3** of [conn2000trust], identification from a vanishing normalized displacement.
Let $E$ be a finite-dimensional real inner product space, let $C$ satisfy AC.2 and AC.7, and let
$c_i$, $\nabla c_i$ and $\nabla f$ be continuous; assume AO.1c and strictly positive active
multipliers at $z$. Let $x_k \to z$ along a filter, let eventually $t_k > 0$, and put
$p_k = P_C[x_k - t_k \nabla f(x_k)]$. If $p_k \to z$, $(p_k - x_k)/t_k \to 0$, and eventually
the tangent qualification holds at $p_k$, then eventually $\mathcal{A}(p_k) = \mathcal{A}(z)$.

The tangent qualification at $p_k$ gives a supported normal representation of the projection
residual, to which `ConnGouldToint.Chapter12.eventually_activeConstraintSet_eq_of_tendsto`
applies.

**Reading.** Identification is obtained from asymptotically accurate projection certificates near
the limit. The concrete forms use vanishing normalized displacement, trial times bounded away from
zero and infinity, or vanishing radii with radius-to-time ratio tending to zero.
-/
theorem eventually_activeConstraintSet_eq_of_projectedGradient_residual
    [Fintype ι] [CompleteSpace E] [FiniteDimensional ℝ E] {α : Type*}
    {l : Filter α} {C : Set E} {c : ι → E → ℝ} {f : E → ℝ}
    {x : α → E} {t : α → ℝ} {z : E}
    (hC : Chapter03.AC2 C) (hset : Chapter03.AC7 C c)
    (hc : ∀ i, Continuous (c i)) (hn : ∀ i, Continuous (gradient (c i)))
    (hg : Continuous (gradient f))
    (hind : LinearIndependent ℝ (fun i : activeConstraintSet c z ↦ gradient (c i) z))
    (hmul : HasStrictActiveMultipliers c (fun i ↦ gradient (c i)) (gradient f) z)
    (hx : Tendsto x l (𝓝 z)) (ht : ∀ᶠ k in l, 0 < t k)
    (hu : Tendsto (fun k ↦ projectedGradientPath C f (x k) (t k)) l (𝓝 z))
    (huv : Tendsto (fun k ↦ (t k)⁻¹ •
      (projectedGradientPath C f (x k) (t k) - x k)) l (𝓝 0))
    (hQ : ∀ᶠ k in l, Chapter03.ActiveLinearizedConeMatches C c
      (projectedGradientPath C f (x k) (t k))) :
    ∀ᶠ k in l, activeConstraintSet c (projectedGradientPath C f (x k) (t k)) =
      activeConstraintSet c z := by
  classical
  let u (k : α) := projectedGradientPath C f (x k) (t k)
  let v (k : α) := gradient f (x k) + (t k)⁻¹ • (u k - x k)
  have hgz : Tendsto (fun k ↦ gradient f (x k)) l (𝓝 (gradient f z)) :=
    hg.continuousAt.tendsto.comp hx
  have hv : Tendsto v l (𝓝 (gradient f z)) := by simpa only [add_zero] using hgz.add huv
  apply eventually_activeConstraintSet_eq_of_tendsto hc hn hind hmul hu hv
  filter_upwards [ht, hQ] with k htp hQk
  have huk := projectedRay_mem hC.1 hC.2.1 hC.2.2 (x k) (-gradient f (x k)) (t k)
  have hres := projectedRay_residual_mem_normal hC.1 hC.2.1 hC.2.2
    (x k) (-gradient f (x k)) (t k)
  have hvn : -v k ∈ normalDirections C (u k) := by
    apply mem_normalDirections.mpr
    intro y hy
    have hh := mem_normalDirections.mp hres y hy
    change ⟪x k + t k • (-gradient f (x k)) - u k, y - u k⟫ ≤ 0 at hh
    have he : -v k = (t k)⁻¹ • (x k + t k • (-gradient f (x k)) - u k) := by
      simp only [v, smul_sub, smul_add, smul_smul, inv_mul_cancel₀ htp.ne', one_smul]
      module
    rw [he, real_inner_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr htp.le) hh
  exact exists_activeCoefficients_of_neg_mem_normal hC hset huk hQk hvn

open Optimization in
/-- **Section 12.3** of [conn2000trust], identification at projected-gradient trials with bounded
positive times. Let $E$ be a finite-dimensional real inner product space, let $C$ satisfy AC.2
and AC.7, and let $c_i$, $\nabla c_i$ and $\nabla f$ be continuous. Let $z \in C$ be stationary,
$-\nabla f(z) \in N(z)$, with AO.1c and strictly positive active multipliers at $z$. Let
$x_k \to z$ along a filter, let $0 < a$ and eventually $a \le t_k \le b$, and put
$p_k = P_C[x_k - t_k \nabla f(x_k)]$. If eventually the tangent qualification holds at $p_k$,
then eventually $\mathcal{A}(p_k) = \mathcal{A}(z)$.

**Reading.** Identification is obtained from asymptotically accurate projection certificates near
the limit. The concrete forms use vanishing normalized displacement, trial times bounded away from
zero and infinity, or vanishing radii with radius-to-time ratio tending to zero.
-/
theorem eventually_activeConstraintSet_eq_projectedGradientPath
    [Fintype ι] [CompleteSpace E] [FiniteDimensional ℝ E] {α : Type*}
    {l : Filter α} {C : Set E} {c : ι → E → ℝ} {f : E → ℝ}
    {x : α → E} {t : α → ℝ} {z : E} {a b : ℝ}
    (hC : Chapter03.AC2 C) (hset : Chapter03.AC7 C c) (hz : z ∈ C)
    (hstat : -gradient f z ∈ normalDirections C z)
    (hc : ∀ i, Continuous (c i)) (hn : ∀ i, Continuous (gradient (c i)))
    (hg : Continuous (gradient f))
    (hind : LinearIndependent ℝ (fun i : activeConstraintSet c z ↦ gradient (c i) z))
    (hmul : HasStrictActiveMultipliers c (fun i ↦ gradient (c i)) (gradient f) z)
    (hx : Tendsto x l (𝓝 z)) (ha : 0 < a)
    (ht : ∀ᶠ k in l, a ≤ t k ∧ t k ≤ b)
    (hQ : ∀ᶠ k in l, Chapter03.ActiveLinearizedConeMatches C c
      (projectedGradientPath C f (x k) (t k))) :
    ∀ᶠ k in l, activeConstraintSet c (projectedGradientPath C f (x k) (t k)) =
      activeConstraintSet c z := by
  let u (k : α) := projectedGradientPath C f (x k) (t k)
  have hgz : Tendsto (fun k ↦ gradient f (x k)) l (𝓝 (gradient f z)) :=
    hg.continuousAt.tendsto.comp hx
  have hu : Tendsto u l (𝓝 z) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    refine squeeze_zero' (.of_forall fun _ ↦ norm_nonneg _)
      (g := fun k ↦ ‖x k - z‖ + b * ‖gradient f (x k) - gradient f z‖) ?_ ?_
    · filter_upwards [ht] with k hk
      have htz := (projectedRay_eq_self_iff hC.1 hC.2.1 hC.2.2 hz).mpr hstat
        (t k) (ha.le.trans hk.1)
      calc
        ‖u k - z‖ ≤ ‖(x k + t k • (-gradient f (x k))) -
            (z + t k • (-gradient f z))‖ := by
          conv_lhs => rw [← htz]
          exact norm_bestApprox_sub_bestApprox_le hC.1 hC.2.1 hC.2.2 _ _
        _ = ‖(x k - z) - t k • (gradient f (x k) - gradient f z)‖ := by
          congr 1
          module
        _ ≤ _ := by
          refine (norm_sub_le _ _).trans (add_le_add_right ?_ _)
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ha.le.trans hk.1)]
          exact mul_le_mul_of_nonneg_right hk.2 (norm_nonneg _)
    · simpa only [mul_zero, add_zero] using
        (tendsto_iff_norm_sub_tendsto_zero.mp hx).add
          ((tendsto_iff_norm_sub_tendsto_zero.mp hgz).const_mul b)
  have huv : Tendsto (fun k ↦ (t k)⁻¹ • (u k - x k)) l (𝓝 0) := by
    have hux : Tendsto (fun k ↦ u k - x k) l (𝓝 0) := by simpa using hu.sub hx
    refine squeeze_zero_norm' (a := fun k ↦ a⁻¹ * ‖u k - x k‖) ?_ ?_
    · filter_upwards [ht] with k hk
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (ha.le.trans hk.1))]
      exact mul_le_mul_of_nonneg_right (inv_le_inv₀ (ha.trans_le hk.1) ha |>.2 hk.1)
        (norm_nonneg _)
    · simpa only [mul_zero] using
        (tendsto_zero_iff_norm_tendsto_zero.mp hux).const_mul a⁻¹
  exact eventually_activeConstraintSet_eq_of_projectedGradient_residual hC hset hc hn hg hind
    hmul hx (ht.mono fun _ hk ↦ ha.trans_le hk.1) hu huv hQ

open Optimization in
/-- **Section 12.3** of [conn2000trust], identification at Cauchy trials with vanishing radii. Let
$E$ be a finite-dimensional real inner product space, let $C$ satisfy AC.2 and AC.7, and let
$c_i$, $\nabla c_i$ and $\nabla f$ be continuous; assume AO.1c and strictly positive active
multipliers at $z$. Let $x_k \to z$ along a filter, let eventually $t_k > 0$, and put
$p_k = P_C[x_k - t_k \nabla f(x_k)]$. Suppose that $\Delta_k \to 0$, $\Delta_k / t_k \to 0$,
eventually $\|p_k - x_k\| \le \Delta_k$, and eventually the tangent qualification holds at
$p_k$. Then eventually $\mathcal{A}(p_k) = \mathcal{A}(z)$.

**Reading.** Identification is obtained from asymptotically accurate projection certificates near
the limit. The concrete forms use vanishing normalized displacement, trial times bounded away from
zero and infinity, or vanishing radii with radius-to-time ratio tending to zero.
-/
theorem eventually_activeConstraintSet_eq_of_small_Cauchy_radius
    [Fintype ι] [CompleteSpace E] [FiniteDimensional ℝ E] {α : Type*}
    {l : Filter α} {C : Set E} {c : ι → E → ℝ} {f : E → ℝ}
    {x : α → E} {t Δ : α → ℝ} {z : E}
    (hC : Chapter03.AC2 C) (hset : Chapter03.AC7 C c)
    (hc : ∀ i, Continuous (c i)) (hn : ∀ i, Continuous (gradient (c i)))
    (hg : Continuous (gradient f))
    (hind : LinearIndependent ℝ (fun i : activeConstraintSet c z ↦ gradient (c i) z))
    (hmul : HasStrictActiveMultipliers c (fun i ↦ gradient (c i)) (gradient f) z)
    (hx : Tendsto x l (𝓝 z)) (ht : ∀ᶠ k in l, 0 < t k)
    (hΔ : Tendsto Δ l (𝓝 0)) (hratio : Tendsto (fun k ↦ Δ k / t k) l (𝓝 0))
    (hstep : ∀ᶠ k in l, ‖projectedGradientPath C f (x k) (t k) - x k‖ ≤ Δ k)
    (hQ : ∀ᶠ k in l, Chapter03.ActiveLinearizedConeMatches C c
      (projectedGradientPath C f (x k) (t k))) :
    ∀ᶠ k in l, activeConstraintSet c (projectedGradientPath C f (x k) (t k)) =
      activeConstraintSet c z := by
  let u (k : α) := projectedGradientPath C f (x k) (t k)
  have hux : Tendsto (fun k ↦ u k - x k) l (𝓝 0) := squeeze_zero_norm' hstep hΔ
  have hu : Tendsto u l (𝓝 z) := by
    simpa only [sub_add_cancel, zero_add] using hux.add hx
  have huv : Tendsto (fun k ↦ (t k)⁻¹ • (u k - x k)) l (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun k ↦ Δ k / t k) ?_ hratio
    filter_upwards [ht, hstep] with k htk hsk
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr htk.le),
      mul_comm, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right hsk htk.le
  exact eventually_activeConstraintSet_eq_of_projectedGradient_residual
    hC hset hc hn hg hind hmul hx ht hu huv hQ

/-- **Lemma 12.3.1** of [conn2000trust], local constancy. Let $S \subseteq E$ and $x \in S$, let the
$c_i$, $n_i$ and $g$ be continuous, let the active normals at $x$ be linearly independent, and
let $g$ have strictly positive active multipliers at every point of $S$. Then
$\mathcal{A}(y) = \mathcal{A}(x)$ for every $y \in S$ near $x$.

**Generalization.** The local constancy and separation arguments use continuous constraint and
normal data with independent active normals and positive supported multipliers on the relevant set.
The separation is formulated pairwise, which gives the source's component bound.
-/
theorem eventually_activeConstraintSet_eq [Fintype ι] {S : Set E}
    {c : ι → E → ℝ} {n : ι → E → E} {g : E → E} {x : E}
    (hx : x ∈ S) (hc : ∀ i, Continuous (c i)) (hn : ∀ i, Continuous (n i))
    (hg : Continuous g)
    (hind : LinearIndependent ℝ (fun i : activeConstraintSet c x ↦ n i x))
    (hmul : ∀ y ∈ S, HasStrictActiveMultipliers c n g y) :
    ∀ᶠ y in 𝓝 x, y ∈ S → activeConstraintSet c y = activeConstraintSet c x := by
  have hpair : Tendsto (fun y ↦ (y, g y)) (𝓝 x) (𝓝 (x, g x)) :=
    continuousAt_id.prodMk hg.continuousAt
  filter_upwards [hpair.eventually
    (eventually_activeConstraintSet_eq_of_normal_representation hc hn hind (hmul x hx))]
    with y hy hyS
  obtain ⟨μ, hstat, _, hzero⟩ := hmul y hyS
  exact hy ⟨μ, hstat, hzero⟩

private theorem activeConstraintSet_continuousOn [Fintype ι]
    [TopologicalSpace (Set ι)] [DiscreteTopology (Set ι)] {S : Set E}
    {c : ι → E → ℝ} {n : ι → E → E} {g : E → E}
    (hc : ∀ i, Continuous (c i)) (hn : ∀ i, Continuous (n i)) (hg : Continuous g)
    (hind : ∀ x ∈ S, LinearIndependent ℝ (fun i : activeConstraintSet c x ↦ n i x))
    (hmul : ∀ x ∈ S, HasStrictActiveMultipliers c n g x) :
    ContinuousOn (activeConstraintSet c) S := by
  intro x hx
  apply (continuousWithinAt_const (b := activeConstraintSet c x)).congr_of_eventuallyEq
  · filter_upwards [(eventually_activeConstraintSet_eq hx hc hn hg (hind x hx) hmul).filter_mono
      nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hy hyS
    exact hy hyS
  · rfl

/-- **Lemma 12.3.1** of [conn2000trust]. Let $S \subseteq E$ be nonempty and connected, and let the
$c_i$, $n_i$ and $g$ be continuous. Suppose that at every $x \in S$ the active normals
$(n_i(x))_{i \in \mathcal{A}(x)}$ are linearly independent and $g$ has strictly positive active
multipliers. Then the active set is constant on $S$: there is $\mathcal{A}$ with
$\mathcal{A}(x) = \mathcal{A}$ for all $x \in S$.

The proof uses only the local constancy
`ConnGouldToint.Chapter12.eventually_activeConstraintSet_eq` and the connectedness of $S$;
path-connectedness is not needed.

**Generalization.** The local constancy and separation arguments use continuous constraint and
normal data with independent active normals and positive supported multipliers on the relevant set.
The separation is formulated pairwise, which gives the source's component bound.
-/
theorem lemma_12_3_1 [Fintype ι] {S : Set E}
    {c : ι → E → ℝ} {n : ι → E → E} {g : E → E}
    (hS : IsConnected S) (hc : ∀ i, Continuous (c i)) (hn : ∀ i, Continuous (n i))
    (hg : Continuous g)
    (hind : ∀ x ∈ S, LinearIndependent ℝ (fun i : activeConstraintSet c x ↦ n i x))
    (hmul : ∀ x ∈ S, HasStrictActiveMultipliers c n g x) :
    ∃ A : Set ι, ∀ x ∈ S, activeConstraintSet c x = A := by
  let : TopologicalSpace (Set ι) := ⊥
  let : DiscreteTopology (Set ι) := ⟨rfl⟩
  have hcont := activeConstraintSet_continuousOn hc hn hg hind hmul
  obtain ⟨x, hx⟩ := hS.nonempty
  exact ⟨activeConstraintSet c x, fun y hy ↦ hS.isPreconnected.constant hcont hy hx⟩

/-- **Section 12.3** of [conn2000trust], identification along a compact run from normal
certificates. Let $K$ be compact, $x_k \in K$, and let every limit of a subsequence of $(x_k)$
lie in $S$. Let the $c_i$, $n_i$ and $g$ be continuous, and suppose that at every $z \in S$ the
active normals are linearly independent, $g$ has strictly positive active multipliers, and
$\mathcal{A}(z) = \mathcal{A}$. If $u_k - x_k \to 0$, $v_k - g(x_k) \to 0$, and eventually $v_k$
has a supported normal representation at $u_k$, then eventually
$\mathcal{A}(u_k) = \mathcal{A}$.

**Correction.** The corrected subsequence and eventual identification claims use asymptotically
accurate supported normal certificates. The subsequence theorem also explicitly assumes infinitely
many successful iterations and a common active set on the limit set.
-/
theorem eventually_activeConstraintSet_eq_of_compact_normal_certificates [Fintype ι]
    {K S : Set E} {c : ι → E → ℝ} {n : ι → E → E} {g : E → E}
    {x u v : ℕ → E} {A : Set ι}
    (hK : IsCompact K) (hx : ∀ k, x k ∈ K)
    (hlim : ∀ z (j : ℕ → ℕ), StrictMono j → Tendsto (x ∘ j) atTop (𝓝 z) → z ∈ S)
    (hc : ∀ i, Continuous (c i)) (hn : ∀ i, Continuous (n i)) (hg : Continuous g)
    (hind : ∀ z ∈ S, LinearIndependent ℝ (fun i : activeConstraintSet c z ↦ n i z))
    (hstat : ∀ z ∈ S, HasStrictActiveMultipliers c n g z)
    (hAS : ∀ z ∈ S, activeConstraintSet c z = A)
    (hu : Tendsto (fun k ↦ u k - x k) atTop (𝓝 0))
    (hv : Tendsto (fun k ↦ v k - g (x k)) atTop (𝓝 0))
    (hrep : ∀ᶠ k in atTop, ∃ μ : ι → ℝ, v k = ∑ i, μ i • n i (u k) ∧
      ∀ i ∉ activeConstraintSet c (u k), μ i = 0) :
    ∀ᶠ k in atTop, activeConstraintSet c (u k) = A := by
  by_contra! hbad
  obtain ⟨j, hj, hjbad⟩ := extraction_of_frequently_atTop hbad
  obtain ⟨z, _, i, hi, hzi⟩ := hK.isSeqCompact (fun k ↦ hx (j k))
  let w := j ∘ i
  have hw : StrictMono w := hj.comp hi
  have hxw : Tendsto (x ∘ w) atTop (𝓝 z) := hzi
  have hz := hlim z w hw hxw
  have huw : Tendsto (u ∘ w) atTop (𝓝 z) := by
    change Tendsto (fun k ↦ u (w k)) atTop (𝓝 z)
    simpa only [Function.comp_apply, sub_add_cancel, zero_add] using
      (hu.comp hw.tendsto_atTop).add hxw
  have hgw : Tendsto (g ∘ x ∘ w) atTop (𝓝 (g z)) := hg.continuousAt.tendsto.comp hxw
  have hvw : Tendsto (v ∘ w) atTop (𝓝 (g z)) := by
    change Tendsto (fun k ↦ v (w k)) atTop (𝓝 (g z))
    simpa only [Function.comp_apply, sub_add_cancel, zero_add] using
      (hv.comp hw.tendsto_atTop).add hgw
  have hgood := eventually_activeConstraintSet_eq_of_tendsto hc hn (hind z hz) (hstat z hz)
    huw hvw (hw.tendsto_atTop.eventually hrep)
  obtain ⟨k, hk⟩ := hgood.exists
  exact hjbad (i k) (hk.trans (hAS z hz))

/-- **Theorem 12.3.8** of [conn2000trust], with normal certificates. Let $K$ be compact,
$x_k \in K$, let $S$ be connected, and let every limit of a subsequence of $(x_k)$ lie in $S$.
Let the $c_i$, $n_i$ and $g$ be continuous, and suppose that at every $z \in S$ the active
normals are linearly independent and $g$ has strictly positive active multipliers. Let
$u_k - x_k \to 0$, $v_k - g(x_k) \to 0$ and $w_k - g(x_k) \to 0$, and suppose that eventually
$v_k$ has a supported normal representation at $x_k$ and $w_k$ has one at $u_k$. Then there is
$\mathcal{A}$ with $\mathcal{A}(z) = \mathcal{A}$ for all $z \in S$, and eventually
$$\mathcal{A}(x_k) = \mathcal{A} \quad\text{and}\quad \mathcal{A}(u_k) = \mathcal{A}.$$

**Correction.** The printed theorem fails at the Cauchy points and at the iterates; see
`ConnGouldToint.Chapter12.theorem_12_3_8_nonvanishing_radius_counterexample` and
`ConnGouldToint.Chapter12.theorem_12_3_8_iterate_identification_counterexample`. This version
assumes asymptotically accurate supported normal certificates $v_k$ at the iterates and $w_k$ at
the Cauchy points $u_k$.

Lemma 12.3.1 gives the common active set on $S$.

**Correction.** The corrected subsequence and eventual identification claims use asymptotically
accurate supported normal certificates. The subsequence theorem also explicitly assumes infinitely
many successful iterations and a common active set on the limit set.
-/
theorem theorem_12_3_8_of_normal_certificates [Fintype ι]
    {K S : Set E} {c : ι → E → ℝ} {n : ι → E → E} {g : E → E}
    {x u v w : ℕ → E}
    (hK : IsCompact K) (hx : ∀ k, x k ∈ K) (hS : IsConnected S)
    (hlim : ∀ z (j : ℕ → ℕ), StrictMono j → Tendsto (x ∘ j) atTop (𝓝 z) → z ∈ S)
    (hc : ∀ i, Continuous (c i)) (hn : ∀ i, Continuous (n i)) (hg : Continuous g)
    (hind : ∀ z ∈ S, LinearIndependent ℝ (fun i : activeConstraintSet c z ↦ n i z))
    (hstat : ∀ z ∈ S, HasStrictActiveMultipliers c n g z)
    (hu : Tendsto (fun k ↦ u k - x k) atTop (𝓝 0))
    (hv : Tendsto (fun k ↦ v k - g (x k)) atTop (𝓝 0))
    (hw : Tendsto (fun k ↦ w k - g (x k)) atTop (𝓝 0))
    (hvrep : ∀ᶠ k in atTop, ∃ μ : ι → ℝ, v k = ∑ i, μ i • n i (x k) ∧
      ∀ i ∉ activeConstraintSet c (x k), μ i = 0)
    (hwrep : ∀ᶠ k in atTop, ∃ μ : ι → ℝ, w k = ∑ i, μ i • n i (u k) ∧
      ∀ i ∉ activeConstraintSet c (u k), μ i = 0) :
    ∃ A : Set ι, (∀ z ∈ S, activeConstraintSet c z = A) ∧
      ∀ᶠ k in atTop, activeConstraintSet c (x k) = A ∧ activeConstraintSet c (u k) = A := by
  obtain ⟨A, hA⟩ := lemma_12_3_1 hS hc hn hg hind hstat
  have hzero : Tendsto (fun k ↦ x k - x k) atTop (𝓝 0) := by
    simpa only [sub_self] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : E)) atTop (𝓝 0))
  exact ⟨A, hA,
    (eventually_activeConstraintSet_eq_of_compact_normal_certificates
      hK hx hlim hc hn hg hind hstat hA hzero hv hvrep).and
    (eventually_activeConstraintSet_eq_of_compact_normal_certificates
      hK hx hlim hc hn hg hind hstat hA hu hw hwrep)⟩

/-- **Lemma 12.3.7** of [conn2000trust], with normal certificates. Let $K$ be compact, $x_k \in K$,
and let every limit of a subsequence of $(x_k)$ lie in $S$. Let the $c_i$, $n_i$ and $g$ be
continuous, and suppose that at every $z \in S$ the active normals are linearly independent, $g$
has strictly positive active multipliers, and $\mathcal{A}(z) = \mathcal{A}$. Let
$v_k - g(x_k) \to 0$, let eventually $v_k$ have a supported normal representation at $x_k$, and
let a property "successful" hold for infinitely many $k$. Then there is a strictly increasing
sequence $(j_i)$ such that, for every $i$, iteration $j_i$ is successful and
$\mathcal{A}(x_{j_i}) = \mathcal{A}$.

**Correction.** The printed lemma claims such a subsequence without the normal certificates; the
claim fails, see
`ConnGouldToint.Chapter12.theorem_12_3_8_iterate_identification_counterexample`. This version
assumes a common active set on the limit set and supported normal certificates at the iterates.

**Correction.** The corrected subsequence and eventual identification claims use asymptotically
accurate supported normal certificates. The subsequence theorem also explicitly assumes infinitely
many successful iterations and a common active set on the limit set.
-/
theorem lemma_12_3_7_of_normal_certificates [Fintype ι]
    {K S : Set E} {c : ι → E → ℝ} {n : ι → E → E} {g : E → E}
    {x v : ℕ → E} {A : Set ι} {success : ℕ → Prop}
    (hK : IsCompact K) (hx : ∀ k, x k ∈ K)
    (hlim : ∀ z (j : ℕ → ℕ), StrictMono j → Tendsto (x ∘ j) atTop (𝓝 z) → z ∈ S)
    (hc : ∀ i, Continuous (c i)) (hn : ∀ i, Continuous (n i)) (hg : Continuous g)
    (hind : ∀ z ∈ S, LinearIndependent ℝ (fun i : activeConstraintSet c z ↦ n i z))
    (hstat : ∀ z ∈ S, HasStrictActiveMultipliers c n g z)
    (hA : ∀ z ∈ S, activeConstraintSet c z = A)
    (hv : Tendsto (fun k ↦ v k - g (x k)) atTop (𝓝 0))
    (hrep : ∀ᶠ k in atTop, ∃ μ : ι → ℝ, v k = ∑ i, μ i • n i (x k) ∧
      ∀ i ∉ activeConstraintSet c (x k), μ i = 0)
    (hsuccess : ∃ᶠ k in atTop, success k) :
    ∃ j : ℕ → ℕ, StrictMono j ∧ ∀ i, success (j i) ∧ activeConstraintSet c (x (j i)) = A := by
  have hzero : Tendsto (fun k ↦ x k - x k) atTop (𝓝 0) := by
    simpa only [sub_self] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : E)) atTop (𝓝 0))
  have hid := eventually_activeConstraintSet_eq_of_compact_normal_certificates
    hK hx hlim hc hn hg hind hstat hA hzero hv hrep
  exact extraction_of_frequently_atTop (hsuccess.and_eventually hid)

/-- **Lemma 12.3.2** of [conn2000trust]. Let $S \subseteq E$ be compact, let the $c_i$, $n_i$ and
$g$ be continuous, and suppose that at every $x \in S$ the active normals are linearly
independent and $g$ has strictly positive active multipliers. Then there is $\psi \in (0, 1)$
such that for all $x, y \in S$,
$$\mathcal{A}(x) \neq \mathcal{A}(y) \implies \psi \le \operatorname{dist}(x, y).$$

The statement is pairwise. It also separates a point from any nonempty component of $S$ with a
different active set.

**Generalization.** The local constancy and separation arguments use continuous constraint and
normal data with independent active normals and positive supported multipliers on the relevant set.
The separation is formulated pairwise, which gives the source's component bound.
-/
theorem lemma_12_3_2 [Fintype ι] {S : Set E}
    {c : ι → E → ℝ} {n : ι → E → E} {g : E → E}
    (hS : IsCompact S) (hc : ∀ i, Continuous (c i)) (hn : ∀ i, Continuous (n i))
    (hg : Continuous g)
    (hind : ∀ x ∈ S, LinearIndependent ℝ (fun i : activeConstraintSet c x ↦ n i x))
    (hmul : ∀ x ∈ S, HasStrictActiveMultipliers c n g x) :
    ∃ ψ ∈ Set.Ioo (0 : ℝ) 1, ∀ x ∈ S, ∀ y ∈ S,
      activeConstraintSet c x ≠ activeConstraintSet c y → ψ ≤ dist x y := by
  let : TopologicalSpace (Set ι) := ⊥
  let : DiscreteTopology (Set ι) := ⟨rfl⟩
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let a (x : S) := activeConstraintSet c x
  have ha : Continuous a :=
    continuousOn_iff_continuous_domRestrict.mp (activeConstraintSet_continuousOn hc hn hg hind hmul)
  let T : Set (S × S) := {p | a p.1 ≠ a p.2}
  have hT : IsCompact T := by
    have hd : DiscreteTopology ((Set ι) × (Set ι)) := inferInstance
    exact ((isClosed_discrete {q : Set ι × Set ι | q.1 ≠ q.2}).preimage
      ((ha.comp continuous_fst).prodMk (ha.comp continuous_snd))).isCompact
  let D (p : S × S) := dist (p.1 : E) (p.2 : E)
  have hD : Continuous D :=
    (continuous_subtype_val.comp continuous_fst).dist (continuous_subtype_val.comp continuous_snd)
  by_cases hne : T.Nonempty
  · obtain ⟨p, hp, hmin⟩ := hT.exists_isMinOn hne hD.continuousOn
    have hp₀ : 0 < D p := by
      change a p.1 ≠ a p.2 at hp
      apply dist_pos.mpr
      intro he
      exact hp (congrArg a (Subtype.ext he))
    refine ⟨min (1 / 2) (D p), ⟨lt_min (by norm_num) hp₀,
      (min_le_left _ _).trans_lt (by norm_num)⟩, ?_⟩
    intro x hx y hy hxy
    exact (min_le_right _ _).trans ((isMinOn_iff.mp hmin) (⟨x, hx⟩, ⟨y, hy⟩) hxy)
  · refine ⟨1 / 2, by norm_num [Set.mem_Ioo], ?_⟩
    intro x hx y hy hxy
    exact (hne ⟨(⟨x, hx⟩, ⟨y, hy⟩), hxy⟩).elim

/-- **Section 12.3** of [conn2000trust], common active set of the limit points. Let $S$ and $K$ be
compact, let $x_k \in K$, and let $S$ be exactly the set of limits of subsequences of $(x_k)$.
Suppose that $\operatorname{dist}(x_{k+1}, x_k) \to 0$, that the $c_i$, $n_i$ and $g$ are
continuous, and that at every $z \in S$ the active normals are linearly independent and $g$ has
strictly positive active multipliers. Then there is $\mathcal{A}$ with
$\mathcal{A}(z) = \mathcal{A}$ for all $z \in S$.

The limit set may have several connected components; the uniform separation of Lemma 12.3.2 and
the vanishing steps rule out different active sets on different components.

**Generalization.** The compact set may contain more than the cluster points. The late neighborhood
conclusion selects a connected component for each sufficiently late iterate. With vanishing
successive displacements the cluster points themselves have a common active set.
-/
theorem activeConstraintSet_eq_on_limits_of_vanishing_steps [Fintype ι]
    {S K : Set E} {x : ℕ → E} {c : ι → E → ℝ} {n : ι → E → E} {g : E → E}
    (hS : IsCompact S) (hK : IsCompact K) (hx : ∀ k, x k ∈ K)
    (hlim : ∀ z, z ∈ S ↔ ∃ j : ℕ → ℕ, StrictMono j ∧ Tendsto (x ∘ j) atTop (𝓝 z))
    (hstep : Tendsto (fun k ↦ dist (x (k + 1)) (x k)) atTop (𝓝 0))
    (hc : ∀ i, Continuous (c i)) (hn : ∀ i, Continuous (n i)) (hg : Continuous g)
    (hind : ∀ z ∈ S, LinearIndependent ℝ (fun i : activeConstraintSet c z ↦ n i z))
    (hmul : ∀ z ∈ S, HasStrictActiveMultipliers c n g z) :
    ∃ A : Set ι, ∀ z ∈ S, activeConstraintSet c z = A := by
  obtain ⟨z, _, j, hj, hjz⟩ := hK.isSeqCompact hx
  have hSne : S.Nonempty := ⟨z, (hlim z).mpr ⟨j, hj, hjz⟩⟩
  obtain ⟨ψ, hψ, hsep⟩ := lemma_12_3_2 hS hc hn hg hind hmul
  choose y hy hyclose using fun k ↦ hS.exists_infDist_eq_dist hSne (x k)
  have hdist : Tendsto (fun k ↦ dist (x k) (y k)) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    by_contra! hbad
    obtain ⟨l, hl, hlbad⟩ := extraction_of_frequently_atTop hbad
    obtain ⟨w, _, i, hi, hiw⟩ := hK.isSeqCompact (fun k ↦ hx (l k))
    have hwS := (hlim w).mpr ⟨l ∘ i, hl.comp hi, hiw⟩
    obtain ⟨k, hk⟩ := (hiw.eventually (Metric.ball_mem_nhds w hε)).exists
    have hbadk := hlbad (i k)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg, ← hyclose] at hbadk
    exact (not_lt_of_ge (hbadk.trans (Metric.infDist_le_dist_of_mem hwS))) hk
  have hsuc : Tendsto (fun k : ℕ ↦ k + 1) atTop atTop :=
    tendsto_atTop_mono (fun k ↦ Nat.le_succ k) tendsto_id
  have hψ₃ : 0 < ψ / 3 := div_pos hψ.1 (by norm_num)
  have hsmall := hdist.eventually (gt_mem_nhds hψ₃)
  have hsmallStep := hstep.eventually (gt_mem_nhds hψ₃)
  have hsame : ∀ᶠ k in atTop,
      activeConstraintSet c (y (k + 1)) = activeConstraintSet c (y k) := by
    filter_upwards [hsmall, hsuc.eventually hsmall, hsmallStep] with k hk hk' hs
    by_contra! hneq
    have hfar := hsep _ (hy _) _ (hy _) hneq
    have htri := dist_triangle (y (k + 1)) (x (k + 1)) (y k)
    have htri' := dist_triangle (x (k + 1)) (x k) (y k)
    rw [dist_comm (y (k + 1)) (x (k + 1))] at htri
    linarith only [hfar, htri, htri', hk, hk', hs]
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsame
  have htail : ∀ᶠ k in atTop, activeConstraintSet c (y k) = activeConstraintSet c (y N) := by
    refine eventually_atTop.mpr ⟨N, fun k hk ↦ ?_⟩
    induction k, hk using Nat.le_induction with
    | base => rfl
    | succ k hk ih => exact (hN k hk).trans ih
  refine ⟨activeConstraintSet c (y N), fun w hw ↦ ?_⟩
  obtain ⟨l, hl, hlw⟩ := (hlim w).mp hw
  have hyl : Tendsto (y ∘ l) atTop (𝓝 w) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [(hdist.comp hl.tendsto_atTop).eventually (gt_mem_nhds (half_pos hε)),
      hlw.eventually (Metric.ball_mem_nhds w (half_pos hε))] with k hk hkw
    have ht := dist_triangle (y (l k)) (x (l k)) w
    rw [dist_comm (y (l k)) (x (l k))] at ht
    change dist (x (l k)) (y (l k)) < ε / 2 at hk
    change dist (x (l k)) w < ε / 2 at hkw
    exact ht.trans_lt (by linarith only [hk, hkw])
  have hnear := hyl.eventually (eventually_activeConstraintSet_eq hw hc hn hg (hind w hw) hmul)
  obtain ⟨k, hk₁, hk₂⟩ := (hnear.and (hl.tendsto_atTop.eventually htail)).exists
  exact (hk₁ (hy (l k))).symm.trans hk₂

/-- **Theorem 12.3.3** of [conn2000trust], with (12.3.9)–(12.3.10). Let $S$ and $\Omega$ be compact,
let $x_k \in \Omega$, and let every limit of a subsequence of $(x_k)$ lie in $S$. Let the $c_i$,
$n_i$ and $g$ be continuous, and suppose that at every $z \in S$ the active normals are linearly
independent and $g$ has strictly positive active multipliers. Then there are $\psi \in (0, 1)$
and $\delta \in (0, \psi/4)$ such that

* any two points of $S$ with different active sets are at distance at least $\psi$, and
* for all large $k$ there is $z \in S$ whose connected component $S_z$ in $S$ is compact, such
  that $x_k$ lies in the closed $\delta$-neighborhood of $S_z$ and every $y$ in that
  neighborhood satisfies $\mathcal{A}(y) \subseteq \mathcal{A}(z)$.

The closed neighborhood is `Metric.cthickening δ`, and the component is
`connectedComponentIn S z`.

**Generalization.** The compact set may contain more than the cluster points. The late neighborhood
conclusion selects a connected component for each sufficiently late iterate. With vanishing
successive displacements the cluster points themselves have a common active set.
-/
theorem theorem_12_3_3 [Fintype ι] {S Ω : Set E} {x : ℕ → E}
    {c : ι → E → ℝ} {n : ι → E → E} {g : E → E}
    (hS : IsCompact S) (hΩ : IsCompact Ω) (hx : ∀ k, x k ∈ Ω)
    (hlimit : ∀ z (j : ℕ → ℕ), StrictMono j → Tendsto (x ∘ j) atTop (𝓝 z) → z ∈ S)
    (hc : ∀ i, Continuous (c i)) (hn : ∀ i, Continuous (n i)) (hg : Continuous g)
    (hind : ∀ z ∈ S, LinearIndependent ℝ (fun i : activeConstraintSet c z ↦ n i z))
    (hmul : ∀ z ∈ S, HasStrictActiveMultipliers c n g z) :
    ∃ ψ ∈ Set.Ioo (0 : ℝ) 1, ∃ δ ∈ Set.Ioo (0 : ℝ) (ψ / 4),
      (∀ u ∈ S, ∀ v ∈ S, activeConstraintSet c u ≠ activeConstraintSet c v → ψ ≤ dist u v) ∧
      ∀ᶠ k in atTop, ∃ z ∈ S, IsCompact (connectedComponentIn S z) ∧
        x k ∈ Metric.cthickening δ (connectedComponentIn S z) ∧
        ∀ y ∈ Metric.cthickening δ (connectedComponentIn S z),
          activeConstraintSet c y ⊆ activeConstraintSet c z := by
  classical
  obtain ⟨ψ, hψ, hsep⟩ := lemma_12_3_2 hS hc hn hg hind hmul
  let : TopologicalSpace (Set ι) := ⊥
  let : DiscreteTopology (Set ι) := ⟨rfl⟩
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have ha : Continuous (fun z : S ↦ activeConstraintSet c z) :=
    continuousOn_iff_continuous_domRestrict.mp
      (activeConstraintSet_continuousOn hc hn hg hind hmul)
  let T (i : ι) : Set E := {z ∈ S | c i z ≠ 0}
  have hT (i : ι) : IsCompact (T i) := by
    let A : Set (Set ι) := {a | i ∉ a}
    have hcompact := ((isClosed_discrete A).preimage ha).isCompact.image continuous_subtype_val
    convert hcompact using 1
    ext z
    constructor
    · rintro ⟨hz, hi⟩
      exact ⟨⟨z, hz⟩, hi, rfl⟩
    · rintro ⟨⟨z, hz⟩, hi, rfl⟩
      exact ⟨hz, hi⟩
  have hε (i : ι) : ∃ ε > 0, Metric.cthickening ε (T i) ⊆ {z | c i z ≠ 0} :=
    (hT i).exists_cthickening_subset_open
      ((show IsOpen {z : ℝ | z ≠ 0} from isOpen_ne).preimage (hc i)) (fun z hz ↦ hz.2)
  choose ε hεpos hεsub using hε
  have hcommon : ∃ r > 0, ∀ i, r ≤ ε i := by
    by_cases hι : Nonempty ι
    · let : Nonempty ι := hι
      obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ ε Finset.univ_nonempty
      exact ⟨ε i, hεpos i, fun j ↦ hi j (Finset.mem_univ _)⟩
    · exact ⟨1, zero_lt_one, fun i ↦ (hι ⟨i⟩).elim⟩
  obtain ⟨r, hr, hrε⟩ := hcommon
  let δ := min r (ψ / 8)
  have hδ : 0 < δ := lt_min hr (div_pos hψ.1 (by norm_num))
  have hδψ : δ < ψ / 4 := (min_le_right _ _).trans_lt (by linarith [hψ.1])
  refine ⟨ψ, hψ, δ, ⟨hδ, hδψ⟩, hsep, ?_⟩
  have hnear : ∀ᶠ k in atTop, x k ∈ Metric.thickening δ S := by
    by_contra! hbad
    let K := Ω ∩ (Metric.thickening δ S)ᶜ
    have hK : IsCompact K := hΩ.inter_right Metric.isOpen_thickening.isClosed_compl
    have hfreq : ∃ᶠ k in atTop, x k ∈ K := hbad.mono fun k hk ↦ ⟨hx k, hk⟩
    obtain ⟨z, hz, j, hj, ht⟩ := hK.tendsto_subseq' hfreq
    exact hz.2 (Metric.mem_thickening_iff.mpr
      ⟨z, hlimit z j hj ht, by simpa using hδ⟩)
  filter_upwards [hnear] with k hk
  obtain ⟨z, hz, hdist⟩ := Metric.mem_thickening_iff.mp hk
  let K := connectedComponentIn S z
  have hK : IsCompact K := by
    rw [show K = _ from connectedComponentIn_eq_image hz]
    exact isClosed_connectedComponent.isCompact.image continuous_subtype_val
  have hzK : z ∈ K := mem_connectedComponentIn hz
  have hKS : K ⊆ S := connectedComponentIn_subset S z
  have hKconn : IsConnected K := isConnected_connectedComponentIn_iff.mpr hz
  obtain ⟨A, hA⟩ := lemma_12_3_1 hKconn hc hn hg
    (fun w hw ↦ hind w (hKS hw)) (fun w hw ↦ hmul w (hKS hw))
  refine ⟨z, hz, hK, Metric.mem_cthickening_of_dist_le _ _ _ _ hzK hdist.le, ?_⟩
  intro y hy i hi
  by_contra hnot
  have hKT : K ⊆ T i := by
    intro w hw
    refine ⟨hKS hw, ?_⟩
    change i ∉ activeConstraintSet c w
    rwa [hA w hw, ← hA z hzK]
  have hye : y ∈ Metric.cthickening (ε i) (T i) :=
    Metric.cthickening_mono ((min_le_left _ _).trans (hrε i)) (T i)
      (Metric.cthickening_subset_of_subset δ hKT hy)
  exact hεsub i hye hi

open Optimization in
/-- **Equations (12.3.15)–(12.3.16)** of [conn2000trust], relaxed comparison. Let $E$ be a real
Hilbert space, $R \subseteq E$, and let $x, z, d \in E$ with $z + d \in R$, $\|d\| \le 1/2$ and
$\|z - x\| \le 1/2$. Then
$$\langle -\nabla f(z), d \rangle - \|\nabla f(x) - \nabla f(z)\|\, \|d\| - \|\nabla f(x)\|\,
  \|z - x\| \le \chi_R(x),$$
where $\chi_R(x)$ is the criticality measure (12.1.13) of $R$ at $x$ with radius $1$.

The set $R$ is the relaxed feasible set, in which a constraint is dropped. Moving the base point
from $z$ to $x$ changes the displacement from $d$ to $z - x + d$, which has norm at most $1$.
This comparison replaces the pointwise comparison with the full feasible set in the proof of
Theorem 12.3.4, which `ConnGouldToint.Chapter12.missing_active_local_criticality_counterexample`
shows to be unavailable.

**Correction.** The lower bound uses a point feasible for the relaxed domain and shifts the
displacement from the reference point to the base. The half-line counterexample shows that the local
trial assumptions alone do not support the corresponding bound for the full feasible domain.
-/
theorem relaxedCriticality_lower_bound_of_nearby [CompleteSpace E]
    {R : Set E} {f : E → ℝ} {x z d : E}
    (hd : z + d ∈ R) (hdnorm : ‖d‖ ≤ 1 / 2) (hxz : ‖z - x‖ ≤ 1 / 2) :
    ⟪-gradient f z, d⟫ - ‖gradient f x - gradient f z‖ * ‖d‖ -
        ‖gradient f x‖ * ‖z - x‖ ≤ criticality R f x 1 := by
  let w := d + (z - x)
  have hw : x + w = z + d := by dsimp [w]; abel
  have hn : ‖w‖ ≤ 1 := (norm_add_le _ _).trans (by linarith)
  have hχ := inner_le_linearDecrease (v := -gradient f x) (hw ▸ hd) hn
  have h₁ := neg_abs_le (⟪gradient f z - gradient f x, d⟫)
  have h₁' := abs_real_inner_le_norm (gradient f z - gradient f x) d
  rw [norm_sub_rev] at h₁'
  have h₂ := neg_abs_le (⟪-gradient f x, z - x⟫)
  have h₂' := abs_real_inner_le_norm (-gradient f x) (z - x)
  rw [norm_neg] at h₂'
  change ⟪-gradient f x, w⟫ ≤ criticality R f x 1 at hχ
  rw [show w = d + (z - x) from rfl, inner_add_right] at hχ
  simp only [inner_sub_left] at h₁ h₁'
  simp only [inner_neg_left] at h₂ h₂' hχ ⊢
  linarith only [h₁, h₁', h₂, h₂', hχ]

open Optimization in
/-- **Theorem 12.3.4** of [conn2000trust], relaxed criticality bound. Let $E$ be a real Hilbert
space, $R \subseteq E$, $\varepsilon \le 1$, and let $x, z, d \in E$ with $z + d \in R$,
$\|d\| \le 1/2$ and $\|z - x\| \le 1/2$. Suppose that
$$2 \varepsilon \le \langle -\nabla f(z), d \rangle, \qquad \|\nabla f(x) - \nabla f(z)\| \le
  \varepsilon, \qquad \|\nabla f(x)\|\, \|z - x\| \le \varepsilon / 2.$$
Then $\varepsilon \le \pi_R(x)$, where $\pi_R$ is the capped criticality measure (12.2.15) of
$R$.

**Correction.** The comparison in the proof of the source bounds the criticality measure of the
full feasible set. The trial conditions alone do not give that bound; see
`ConnGouldToint.Chapter12.missing_active_local_criticality_counterexample`. Here the transported
trial $z + d$ must be feasible for the set $R$ whose criticality is bounded, and the linear
decrease pays for the translation of the base point.

**Correction.** The lower bound uses a point feasible for the relaxed domain and shifts the
displacement from the reference point to the base. The half-line counterexample shows that the local
trial assumptions alone do not support the corresponding bound for the full feasible domain.
-/
theorem theorem_12_3_4_relaxed [CompleteSpace E] {R : Set E} {f : E → ℝ} {x z d : E}
    {ε : ℝ} (hε : ε ≤ 1) (hd : z + d ∈ R) (hdnorm : ‖d‖ ≤ 1 / 2)
    (hxz : ‖z - x‖ ≤ 1 / 2)
    (hgap : 2 * ε ≤ ⟪-gradient f z, d⟫)
    (hgrad : ‖gradient f x - gradient f z‖ ≤ ε)
    (htranslate : ‖gradient f x‖ * ‖z - x‖ ≤ ε / 2) :
    ε ≤ cappedCriticality R f x := by
  have hterm : ‖gradient f x - gradient f z‖ * ‖d‖ ≤ ε / 2 :=
    (mul_le_mul_of_nonneg_left hdnorm (norm_nonneg _)).trans (by linarith)
  have hb := relaxedCriticality_lower_bound_of_nearby (f := f) hd hdnorm hxz
  have hχ : ε ≤ criticality R f x 1 := by linarith
  exact le_min hε hχ

open Optimization in
private theorem cauchyProjection_linear_lower [CompleteSpace E] {C : Set E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) {f : E → ℝ} {x : E} (hx : x ∈ C)
    {t γ : ℝ} (ht : 0 < t) (hγ : 0 < γ)
    (hproj : γ ≤ ‖bestApprox (tangentDirections C (projectedGradientPath C f x t))
      (-gradient f x)‖) :
    let u := projectedGradientPath C f x t
    0 < ‖u - x‖ ∧ γ * ‖u - x‖ ≤ -⟪gradient f x, u - x⟫ := by
  let u := projectedGradientPath C f x t
  let r := ‖u - x‖
  let L := -⟪gradient f x, u - x⟫
  have hspeed : γ ≤ r / t :=
    hproj.trans (norm_tangentProjection_projectedRay_le ⟨x, hx⟩ hclosed hconv x
      (-gradient f x) ht)
  have hrpos : 0 < r := (div_pos_iff_of_pos_right ht).mp (hγ.trans_le hspeed)
  have hvar := mem_normalDirections.mp
    (projectedRay_residual_mem_normal ⟨x, hx⟩ hclosed hconv x (-gradient f x) t) x hx
  change ⟪x + t • (-gradient f x) - u, x - u⟫ ≤ 0 at hvar
  rw [show x + t • (-gradient f x) - u = t • (-gradient f x) - (u - x) by abel,
    show x - u = -(u - x) by abel, inner_neg_right, neg_nonpos, inner_sub_left,
    real_inner_smul_left, inner_neg_left, real_inner_self_eq_norm_sq, sub_nonneg] at hvar
  have hlin : γ * r ≤ L := by
    have htγ := (le_div_iff₀ ht).mp hspeed
    apply (le_of_mul_le_mul_left _ ht)
    calc
      t * (γ * r) = (γ * t) * r := by ring
      _ ≤ r * r := mul_le_mul_of_nonneg_right htγ hrpos.le
      _ ≤ t * L := by simpa only [pow_two, L] using hvar
  exact ⟨hrpos, hlin⟩

open Optimization in
/-- **Section 12.3** of [conn2000trust], linear decrease at a tangent-gradient gap. Let $E$ be a
real Hilbert space, $C$ closed and convex, $x \in C$, and $\Delta, \beta, \gamma > 0$ with
$\beta \Delta / 2 < (1 - \kappa_{\mathrm{lo}}) \gamma$. Let $u$ be an approximate generalized
Cauchy point for $C$, $f$, $m$, $x$ and $\Delta$, and suppose that
$$\gamma \le \|P_{T(u)}[-\nabla f(x)]\| \quad\text{and}\quad m(u) - m(x) - \langle \nabla f(x),
  u - x \rangle \le \tfrac{\beta}{2} \|u - x\|^2.$$
Then
$$\kappa_{\mathrm{up}}\, \kappa_{\mathrm{fr}}\, \gamma\, \Delta \le m(x) - m(u).$$

The estimate uses the actual feasible trial $u$ and does not compare criticality measures of the
full and the relaxed feasible sets.

**Reading.** The proof steps use explicit lower bounds for tangent projection, radius and model
controls, or face preservation, according to the claimed implication. The successful-trial
conclusion assumes vanishing radii and infinitely many successful iterations.
-/
theorem cauchyDecrease_linear_of_tangentProjection_lower [CompleteSpace E]
    (P : GeneralizedCauchyParams) {C : Set E} (hclosed : IsClosed C) (hconv : Convex ℝ C)
    {f m : E → ℝ} {x u : E} (hx : x ∈ C) {Δ β γ : ℝ}
    (hΔ : 0 < Δ) (hβ : 0 < β) (hγ : 0 < γ)
    (hsmall : β * Δ / 2 < (1 - P.lowerSlope) * γ)
    (hc : IsApproxGeneralizedCauchyPoint P C f m x Δ u)
    (hproj : γ ≤ ‖bestApprox (tangentDirections C u) (-gradient f x)‖)
    (hTaylor : m u - (m x + ⟪gradient f x, u - x⟫) ≤ β * ‖u - x‖ ^ 2 / 2) :
    P.upperSlope * (P.radiusFraction * γ) * Δ ≤ m x - m u := by
  obtain ⟨t, ht, rfl, hball, hupper, hstop⟩ := hc
  let u := projectedGradientPath C f x t
  let r := ‖u - x‖
  let L := -⟪gradient f x, u - x⟫
  obtain ⟨hrpos, hlin⟩ := cauchyProjection_linear_lower hclosed hconv hx ht hγ hproj
  have hL : 0 ≤ L := (mul_nonneg hγ.le hrpos.le).trans hlin
  have hgoal : P.radiusFraction * γ * Δ ≤ L := by
    rcases hstop with hR | hlow | hend
    · calc
        _ = γ * (P.radiusFraction * Δ) := by ring
        _ ≤ γ * r := mul_le_mul_of_nonneg_left hR hγ.le
        _ ≤ L := hlin
    · exfalso
      have hrel : (1 - P.lowerSlope) * L ≤ β * r ^ 2 / 2 := by
        dsimp only [L, r]
        linarith only [hTaylor, hlow]
      have hrel' := (mul_le_mul_of_nonneg_left hlin (sub_nonneg.mpr P.lower_lt_one.le)).trans hrel
      have hball' : r ≤ Δ := hball
      have hmul := mul_le_mul_of_nonneg_left hball' (half_pos hβ).le
      have hsmall' : β / 2 * Δ < (1 - P.lowerSlope) * γ := by
        simpa only [div_mul_eq_mul_div] using hsmall
      have hstrict := mul_lt_mul_of_pos_right (hmul.trans_lt hsmall') hrpos
      nlinarith only [hstrict, hrel']
    · have hbound : γ ≤ P.endpointFactor * (L / Δ) := by
        apply hproj.trans
        have hAbs : |⟪gradient f x, u - x⟫| = L := abs_of_nonpos (neg_nonneg.mp hL)
        rw [← hAbs]
        exact hend
      have hcoeff : P.radiusFraction * P.endpointFactor ≤ 1 :=
        (mul_le_mul P.fraction_lt_one.le (P.endpoint_lt_half.le.trans (by norm_num))
          P.endpoint_pos.le (by norm_num)).trans_eq (one_mul 1)
      have htimes := mul_le_mul_of_nonneg_right hbound hΔ.le
      rw [mul_assoc, div_mul_cancel₀ _ hΔ.ne'] at htimes
      calc
        _ = P.radiusFraction * (γ * Δ) := by ring
        _ ≤ P.radiusFraction * (P.endpointFactor * L) :=
          mul_le_mul_of_nonneg_left htimes P.fraction_pos.le
        _ ≤ L := by
          rw [← mul_assoc]
          exact mul_le_of_le_one_left hL hcoeff
  calc
    _ = P.upperSlope * (P.radiusFraction * γ * Δ) := by ring
    _ ≤ P.upperSlope * L := mul_le_mul_of_nonneg_left hgoal P.upper_pos.le
    _ ≤ _ := by
      change m u ≤ m x + P.upperSlope * ⟪gradient f x, u - x⟫ at hupper
      dsimp only [L]
      linarith only [hupper]

open Optimization in
/-- **Section 12.3** of [conn2000trust], radius estimate at a tangent-gradient gap. Let $E$ be a
real Hilbert space, $C$ closed and convex, $x \in C$, $\Delta > 0$, $\gamma > 0$ and
$\|\nabla f(x)\| \le G$. Let $u$ be an approximate generalized Cauchy point for $C$, $f$, $m$,
$x$ and $\Delta$ with $\beta \|u - x\| / 2 < (1 - \kappa_{\mathrm{lo}}) \gamma$, and suppose
that
$$\gamma \le \|P_{T(u)}[-\nabla f(x)]\| \quad\text{and}\quad m(u) - m(x) - \langle \nabla f(x),
  u - x \rangle \le \tfrac{\beta}{2} \|u - x\|^2.$$
Then
$$\Delta \le \max\Bigl\{\kappa_{\mathrm{fr}}^{-1}, \frac{\kappa_{\mathrm{ep}}\,
  G}{\gamma}\Bigr\} \|u - x\|.$$

The radius itself need not be small; only the displacement $\|u - x\|$ enters the smallness
condition.

**Reading.** The proof steps use explicit lower bounds for tangent projection, radius and model
controls, or face preservation, according to the claimed implication. The successful-trial
conclusion assumes vanishing radii and infinitely many successful iterations.
-/
theorem radius_le_mul_displacement_of_tangentProjection_lower [CompleteSpace E]
    (P : GeneralizedCauchyParams) {C : Set E} (hclosed : IsClosed C) (hconv : Convex ℝ C)
    {f m : E → ℝ} {x u : E} (hx : x ∈ C) {Δ β γ G : ℝ}
    (hΔ : 0 < Δ) (hγ : 0 < γ) (hG : ‖gradient f x‖ ≤ G)
    (hsmall : β * ‖u - x‖ / 2 < (1 - P.lowerSlope) * γ)
    (hc : IsApproxGeneralizedCauchyPoint P C f m x Δ u)
    (hproj : γ ≤ ‖bestApprox (tangentDirections C u) (-gradient f x)‖)
    (hTaylor : m u - (m x + ⟪gradient f x, u - x⟫) ≤ β * ‖u - x‖ ^ 2 / 2) :
    Δ ≤ max P.radiusFraction⁻¹ (P.endpointFactor * G / γ) * ‖u - x‖ := by
  obtain ⟨t, ht, rfl, _, _, hstop⟩ := hc
  let u := projectedGradientPath C f x t
  let r := ‖u - x‖
  let L := -⟪gradient f x, u - x⟫
  obtain ⟨hrpos, hlin⟩ := cauchyProjection_linear_lower hclosed hconv hx ht hγ hproj
  rcases hstop with hR | hlow | hend
  · have h := (le_div_iff₀ P.fraction_pos).mpr (by simpa only [mul_comm] using hR)
    calc
      Δ ≤ P.radiusFraction⁻¹ * r := by simpa only [div_eq_mul_inv, mul_comm] using h
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hrpos.le
  · exfalso
    have hrel : (1 - P.lowerSlope) * L ≤ β * r ^ 2 / 2 := by
      dsimp only [L, r]
      linarith only [hTaylor, hlow]
    have hrel' := (mul_le_mul_of_nonneg_left hlin (sub_nonneg.mpr P.lower_lt_one.le)).trans hrel
    have hstrict := mul_lt_mul_of_pos_right hsmall hrpos
    change β * r / 2 * r < (1 - P.lowerSlope) * γ * r at hstrict
    nlinarith only [hstrict, hrel']
  · have hprod := mul_le_mul_of_nonneg_right (hproj.trans hend) hΔ.le
    rw [mul_assoc, div_mul_cancel₀ _ hΔ.ne'] at hprod
    have hbound := (abs_real_inner_le_norm (gradient f x) (u - x)).trans
      (mul_le_mul_of_nonneg_right hG hrpos.le)
    have hp := hprod.trans (mul_le_mul_of_nonneg_left hbound P.endpoint_pos.le)
    calc
      Δ ≤ (P.endpointFactor * G / γ) * r := by
        rw [div_mul_eq_mul_div]
        exact (le_div_iff₀ hγ).mpr (by nlinarith only [hp])
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hrpos.le

open Optimization Chapter06 in
/-- **Section 12.3** of [conn2000trust], very successful misidentified trials. Let $E$ be a
finite-dimensional real inner product space, let $C$ satisfy AC.2 and AC.7, and let $c_i$,
$\nabla c_i$ and $\nabla f$ be continuous. At $z$ let the active gradients be linearly
independent and let $\nabla f$ have strictly positive active multipliers. Along a filter let
$x_k \to z$, $u_k \to z$ and $\Delta_k \to 0$, and let eventually the tangent qualification hold
at $u_k$. Let $\beta > 0$ and $B$ be constants, and suppose that eventually

* $x_k \in C$, $\Delta_k > 0$, and $u_k$ is an approximate generalized Cauchy point for $C$,
  $f$, $m_k$, $x_k$ and $\Delta_k$;
* $m_k(u_k) - m_k(x_k) - \langle \nabla f(x_k), u_k - x_k \rangle \le \frac{\beta}{2} \|u_k -
  x_k\|^2$;
* $f(x_k) = m_k(x_k)$, $m_k(x_k + s_k) \le m_k(u_k)$ and $|f(x_k + s_k) - m_k(x_k + s_k)| \le B
  \Delta_k^2$.

Then there is $\kappa > 0$ such that eventually, if $\mathcal{A}(u_k) \neq \mathcal{A}(z)$, then
$\kappa \Delta_k \le m_k(x_k) - m_k(x_k + s_k)$ and $\rho_k \ge \eta_2$, where $\rho_k$ is the
ratio (6.1.4) of the step $s_k$.

The proof combines the tangent-gradient gap
`ConnGouldToint.Chapter12.eventually_tangentProjection_lower_of_active_mismatch` with the linear
decrease `ConnGouldToint.Chapter12.cauchyDecrease_linear_of_tangentProjection_lower`.

**Reading.** The proof steps use explicit lower bounds for tangent projection, radius and model
controls, or face preservation, according to the claimed implication. The successful-trial
conclusion assumes vanishing radii and infinitely many successful iterations.
-/
theorem eventually_verySuccessful_of_active_mismatch [Fintype ι] [CompleteSpace E]
    [FiniteDimensional ℝ E] {α : Type*} {l : Filter α} {C : Set E} {c : ι → E → ℝ}
    {f : E → ℝ} {m : α → E → ℝ} {x u s : α → E} {z : E} {Δ : α → ℝ}
    (Q : GeneralizedCauchyParams) (P : BTRParams)
    (hC : Chapter03.AC2 C) (hset : Chapter03.AC7 C c)
    (hc : ∀ i, Continuous (c i)) (hn : ∀ i, Continuous (gradient (c i)))
    (hg : Continuous (gradient f))
    (hind : LinearIndependent ℝ (fun i : activeConstraintSet c z ↦ gradient (c i) z))
    (hmul : HasStrictActiveMultipliers c (fun i ↦ gradient (c i)) (gradient f) z)
    (hx : Tendsto x l (𝓝 z)) (hu : Tendsto u l (𝓝 z)) (hΔ : Tendsto Δ l (𝓝 0))
    (hQ : ∀ᶠ k in l, Chapter03.ActiveLinearizedConeMatches C c (u k))
    {β B : ℝ} (hβ : 0 < β)
    (htrial : ∀ᶠ k in l, x k ∈ C ∧ 0 < Δ k ∧
      IsApproxGeneralizedCauchyPoint Q C f (m k) (x k) (Δ k) (u k))
    (hTaylor : ∀ᶠ k in l, m k (u k) - (m k (x k) + ⟪gradient f (x k), u k - x k⟫) ≤
      β * ‖u k - x k‖ ^ 2 / 2)
    (hfit : ∀ᶠ k in l, f (x k) = m k (x k) ∧ m k (x k + s k) ≤ m k (u k) ∧
      |f (x k + s k) - m k (x k + s k)| ≤ B * Δ k ^ 2) :
    ∃ κ > 0, ∀ᶠ k in l, activeConstraintSet c (u k) ≠ activeConstraintSet c z →
      κ * Δ k ≤ m k (x k) - m k (x k + s k) ∧
      P.η₂ ≤ btrRatio f (m k) (x k) (s k) := by
  have hfeas : ∀ᶠ k in l, u k ∈ C := htrial.mono fun k ⟨_, _, t, _, hut, _⟩ ↦
    hut.symm ▸ projectedRay_mem hC.1 hC.2.1 hC.2.2 (x k) (-gradient f (x k)) t
  obtain ⟨γ, hγ, hgap⟩ := eventually_tangentProjection_lower_of_active_mismatch
    hC hset hc hn hg hind hmul hx hu hfeas hQ
  let κ := Q.upperSlope * (Q.radiusFraction * γ)
  have hκ : 0 < κ := mul_pos Q.upper_pos (mul_pos Q.fraction_pos hγ)
  have ht₁ : ∀ᶠ k in l, β * Δ k / 2 < (1 - Q.lowerSlope) * γ := by
    have hpos := mul_pos (sub_pos.mpr Q.lower_lt_one) hγ
    have ht := ((hΔ.const_mul β).div_const (2 : ℝ)).eventually
      (gt_mem_nhds (show (β * 0 / 2 : ℝ) < _ by simpa using hpos))
    exact ht
  have ht₂ : ∀ᶠ k in l, B * Δ k ≤ (1 - P.η₂) * κ := by
    have hpos := mul_pos (sub_pos.mpr P.eta₂_lt_one) hκ
    exact ((hΔ.const_mul B).eventually
      (gt_mem_nhds (show B * 0 < _ by simpa using hpos))).mono fun _ hk ↦ hk.le
  refine ⟨κ, hκ, ?_⟩
  filter_upwards [htrial, hTaylor, hfit, hgap, ht₁, ht₂]
    with k ⟨hkx, hkΔ, hkC⟩ hTk ⟨hvk, hmk, hek⟩ hgk ht₁k ht₂k
  intro hneq
  have hdec := cauchyDecrease_linear_of_tangentProjection_lower
    Q hC.2.1 hC.2.2 hkx hkΔ hβ hγ ht₁k hkC (hgk hneq) hTk
  have hpred : κ * Δ k ≤ m k (x k) - m k (x k + s k) := hdec.trans (sub_le_sub_left hmk _)
  have hpredpos := (mul_pos hκ hkΔ).trans_le hpred
  have herr' : |f (x k + s k) - (f (x k) - (m k (x k) - m k (x k + s k)))| ≤
      (1 - P.η₂) * (m k (x k) - m k (x k + s k)) := by
    rw [hvk, sub_sub_cancel]
    apply hek.trans
    have hp₁ := mul_le_mul_of_nonneg_right ht₂k hkΔ.le
    have hp₂ := mul_le_mul_of_nonneg_left hpred (sub_nonneg.mpr P.eta₂_lt_one.le)
    nlinarith only [hp₁, hp₂]
  exact ⟨hpred, by simpa [btrRatio] using le_reductionRatio_of_abs_sub_le hpredpos herr'⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
open Chapter06 in
/-- **Section 12.3** of [conn2000trust], identified Cauchy trials at vanishing radii. Let
$\Delta_k > 0$ with $\Delta_k \to 0$, let the radii follow the update (6.1.5) with ratios
$\rho_k$, and suppose that eventually $\mathcal{A}(u_k) \neq \mathcal{A}$ implies
$\rho_k \ge \eta_2$. Then $\mathcal{A}(u_k) = \mathcal{A}$ for infinitely many $k$.

A very successful iteration does not decrease the radius, so the radii could not tend to zero if
all late trials were misidentified.

**Reading.** The proof steps use explicit lower bounds for tangent projection, radius and model
controls, or face preservation, according to the claimed implication. The successful-trial
conclusion assumes vanishing radii and infinitely many successful iterations.
-/
theorem frequently_active_eq_at_Cauchy_trial_of_radius_tendsto_zero
    {P : BTRParams} {ρ Δ : ℕ → ℝ} {u : ℕ → E} {c : ι → E → ℝ} {A : Set ι}
    (hΔ : Tendsto Δ atTop (𝓝 0)) (hpos : ∀ k, 0 < Δ k)
    (hupdate : ∀ k, BTRRadiusUpdate P (ρ k) (Δ k) (Δ (k + 1)))
    (hmiss : ∀ᶠ k in atTop, activeConstraintSet c (u k) ≠ A → P.η₂ ≤ ρ k) :
    ∃ᶠ k in atTop, activeConstraintSet c (u k) = A := by
  by_contra! hbad
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hmiss.and hbad)
  have hmono (j : ℕ) : Δ N ≤ Δ (N + j) := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hk := hN (N + j) (Nat.le_add_right _ _)
      exact ih.trans ((hupdate (N + j)).very_successful (hk.1 hk.2))
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hΔ.eventually (gt_mem_nhds (hpos N)))
  exact (not_lt_of_ge (hmono M)) (hM (N + M) (Nat.le_add_left _ _))

open Optimization in
/-- **Section 12.3** of [conn2000trust], comparison of predictions at a common center. Let
$x + s' \in C$, let $n$ be a normal vector of $C$ at $x + s$, and suppose that
$$|m(x + s) - m(x) - \langle g, s \rangle| \le e, \qquad |m'(x + s') - m'(x) - \langle g, s'
  \rangle| \le e'.$$
Then
$$m'(x) - m'(x + s') \le m(x) - m(x + s) + e + e' + \|-g - n\|\, \|s' - s\|.$$

This applies to a rejected trial $x + s$ and the next trial $x + s'$ from the same center $x$.

**Reading.** The proof steps use explicit lower bounds for tangent projection, radius and model
controls, or face preservation, according to the claimed implication. The successful-trial
conclusion assumes vanishing radii and infinitely many successful iterations.
-/
theorem prediction_le_of_common_center {C : Set E}
    {m m' : E → ℝ} {x s s' g n : E} {e e' : ℝ}
    (hfeas : x + s' ∈ C) (hn : n ∈ normalDirections C (x + s))
    (he : |m (x + s) - m x - ⟪g, s⟫| ≤ e)
    (he' : |m' (x + s') - m' x - ⟪g, s'⟫| ≤ e') :
    m' x - m' (x + s') ≤ m x - m (x + s) + e + e' + ‖-g - n‖ * ‖s' - s‖ := by
  have hnormal := mem_normalDirections.mp hn (x + s') hfeas
  rw [add_sub_add_left_eq_sub] at hnormal
  have he₁ := le_trans (le_abs_self _) he
  have he₂ := (neg_le_neg he').trans (neg_abs_le _)
  have hlinear : ⟪-g, s' - s⟫ ≤ ‖-g - n‖ * ‖s' - s‖ := calc
    _ = ⟪-g - n, s' - s⟫ + ⟪n, s' - s⟫ := by rw [inner_sub_left]; ring
    _ ≤ ⟪-g - n, s' - s⟫ := add_le_of_nonpos_right hnormal
    _ ≤ _ := real_inner_le_norm _ _
  rw [inner_neg_left, inner_sub_right] at hlinear
  linarith only [he₁, he₂, hlinear]

open Optimization in
private theorem exists_continuous_normal_on_active_face [Fintype ι] [CompleteSpace E]
    {C : Set E} {c : ι → E → ℝ} {f : E → ℝ} {z : E}
    (hn : ∀ i, Continuous (gradient (c i)))
    (hstat : HasStrictActiveMultipliers c (fun i ↦ gradient (c i)) (gradient f) z)
    (hnormal : ∀ y ∈ C, ∀ i ∈ activeConstraintSet c y,
      -gradient (c i) y ∈ normalDirections C y) :
    ∃ w : E → E, Continuous w ∧ w z = -gradient f z ∧
      ∀ y ∈ C, activeConstraintSet c y = activeConstraintSet c z →
        w y ∈ normalDirections C y := by
  obtain ⟨μ, hμ, hμpos, hμzero⟩ := hstat
  let w (v : E) := ∑ i, μ i • (-gradient (c i) v)
  refine ⟨w, continuous_finsetSum _ (fun i _ ↦ continuous_const.smul (hn i).neg), ?_, ?_⟩
  · simp only [w, smul_neg, Finset.sum_neg_distrib, ← hμ]
  · intro y hy hA
    apply mem_normalDirections.mpr
    intro q hq
    change ⟪∑ i, μ i • (-gradient (c i) y), q - y⟫ ≤ 0
    rw [sum_inner]
    apply Finset.sum_nonpos
    intro i _
    rw [real_inner_smul_left]
    by_cases hi : i ∈ activeConstraintSet c z
    · exact mul_nonpos_of_nonneg_of_nonpos (hμpos i hi).le
        (mem_normalDirections.mp (hnormal _ hy i (hA.symm ▸ hi)) q hq)
    · rw [hμzero i hi, zero_mul]

open Optimization in
/-- **Theorem 12.3.8** of [conn2000trust], preservation of the limiting active set. Let $E$ be a
finite-dimensional real inner product space, let $C$ satisfy AC.2 and AC.7, let $c_i$,
$\nabla c_i$ and $\nabla f$ be continuous, and let $-\nabla c_i(y) \in N(y)$ for every $y \in C$
and $i \in \mathcal{A}(y)$. At $z$ let the active gradients be linearly independent and let
$\nabla f$ have strictly positive active multipliers. Along a filter let $x_k \to z$ and
$u_k \to z$, let eventually the tangent qualification hold at $u_k$, and let eventually
$x_k \in C$ and $u_k = P_C[x_k - t \nabla f(x_k)]$ for some $t > 0$. Then eventually, if
$\mathcal{A}(x_k) = \mathcal{A}(z)$, then $\mathcal{A}(u_k) = \mathcal{A}(z)$.

**Reading.** The proof steps use explicit lower bounds for tangent projection, radius and model
controls, or face preservation, according to the claimed implication. The successful-trial
conclusion assumes vanishing radii and infinitely many successful iterations.
-/
theorem eventually_CauchyTrial_preserves_active_face [Fintype ι] [CompleteSpace E]
    [FiniteDimensional ℝ E] {α : Type*} {l : Filter α} {C : Set E} {c : ι → E → ℝ}
    {f : E → ℝ} {x u : α → E} {z : E}
    (hC : Chapter03.AC2 C) (hset : Chapter03.AC7 C c)
    (hc : ∀ i, Continuous (c i)) (hn : ∀ i, Continuous (gradient (c i)))
    (hg : Continuous (gradient f))
    (hind : LinearIndependent ℝ (fun i : activeConstraintSet c z ↦ gradient (c i) z))
    (hmul : HasStrictActiveMultipliers c (fun i ↦ gradient (c i)) (gradient f) z)
    (hnormal : ∀ y ∈ C, ∀ i ∈ activeConstraintSet c y,
      -gradient (c i) y ∈ normalDirections C y)
    (hx : Tendsto x l (𝓝 z)) (hu : Tendsto u l (𝓝 z))
    (hQ : ∀ᶠ k in l, Chapter03.ActiveLinearizedConeMatches C c (u k))
    (htrial : ∀ᶠ k in l, x k ∈ C ∧
      ∃ t > 0, u k = projectedGradientPath C f (x k) t) :
    ∀ᶠ k in l, activeConstraintSet c (x k) = activeConstraintSet c z →
      activeConstraintSet c (u k) = activeConstraintSet c z := by
  have hfeas : ∀ᶠ k in l, u k ∈ C := htrial.mono fun k ⟨_, t, _, hut⟩ ↦
    hut.symm ▸ projectedRay_mem hC.1 hC.2.1 hC.2.2 (x k) (-gradient f (x k)) t
  obtain ⟨γ, hγ, hgap⟩ := eventually_tangentProjection_lower_of_active_mismatch
    hC hset hc hn hg hind hmul hx hu hfeas hQ
  obtain ⟨w, hw, hwz, hwn⟩ := exists_continuous_normal_on_active_face hn hmul hnormal
  have hlim : Tendsto (fun k ↦ ‖-gradient f (x k) - w (x k)‖) l (𝓝 0) := by
    simpa only [hwz, sub_self, norm_zero, Function.comp_apply] using
      ((hg.continuousAt.tendsto.comp hx).neg.sub (hw.continuousAt.tendsto.comp hx)).norm
  filter_upwards [htrial, hgap, hlim.eventually (gt_mem_nhds hγ)]
    with k ⟨hk, t, ht, hut⟩ hgapk hsmall
  intro hA
  by_contra! hbad
  have hfix := (projectedRay_eq_self_iff hC.1 hC.2.1 hC.2.2 hk).mpr (hwn _ hk hA) t ht.le
  have hdist : ‖u k - x k‖ ≤ t * ‖-gradient f (x k) - w (x k)‖ := by
    calc
      ‖u k - x k‖ = ‖bestApprox C (x k + t • (-gradient f (x k))) -
          bestApprox C (x k + t • w (x k))‖ :=
        congrArg₂ (fun a b : E ↦ ‖a - b‖) hut hfix.symm
      _ ≤ _ := by
        refine (norm_bestApprox_sub_bestApprox_le hC.1 hC.2.1 hC.2.2 _ _).trans_eq ?_
        rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  have hspeed := norm_tangentProjection_projectedRay_le
    hC.1 hC.2.1 hC.2.2 (x k) (-gradient f (x k)) ht
  rw [← show u k = projectedRay C (x k) (-gradient f (x k)) t from hut] at hspeed
  have hle : ‖u k - x k‖ / t ≤ ‖-gradient f (x k) - w (x k)‖ :=
    (div_le_iff₀ ht).mpr (by simpa only [mul_comm] using hdist)
  exact (not_lt_of_ge ((hgapk hbad).trans (hspeed.trans hle))) hsmall

open Optimization Chapter06 in
private theorem eventually_rejection_then_identifiedOn [Fintype ι] [CompleteSpace E]
    {C : Set E} {c : ι → E → ℝ} {f : E → ℝ} {P : BTRParams}
    {sufficient : ℕ → (E → ℝ) → E → E → Prop}
    (run : BTRRun f P sufficient) {u : ℕ → E} {z : E} {l : Filter ℕ}
    (hl : l ≤ atTop)
    (hg : Continuous (gradient f)) (hn : ∀ i, Continuous (gradient (c i)))
    (hstat : HasStrictActiveMultipliers c (fun i ↦ gradient (c i)) (gradient f) z)
    (hnormal : ∀ y ∈ C, ∀ i ∈ activeConstraintSet c y,
      -gradient (c i) y ∈ normalDirections C y)
    (hx : Tendsto run.x l (𝓝 z)) (hΔ : Tendsto run.Δ l (𝓝 0))
    (hstep : ∀ k, ‖run.s k‖ ≤ run.Δ k)
    (hfeas : ∀ k, run.x k + run.s k ∈ C)
    (hface : ∀ᶠ k in l, activeConstraintSet c (u k) = activeConstraintSet c z →
      activeConstraintSet c (run.x k + run.s k) = activeConstraintSet c z)
    {β B κ : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ)
    (hTaylor : ∀ k, |run.model k (run.x k + run.s k) - run.model k (run.x k) -
      ⟪gradient f (run.x k), run.s k⟫| ≤ β * run.Δ k ^ 2)
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (herr : ∀ k, |f (run.x k + run.s k) - run.model k (run.x k + run.s k)| ≤ B * run.Δ k ^ 2)
    (hmiss : ∀ᶠ k in atTop, activeConstraintSet c (u k) ≠ activeConstraintSet c z →
      κ * run.Δ k ≤ run.model k (run.x k) - run.model k (run.x k + run.s k) ∧
      k ∈ run.verySuccessful) :
    ∀ᶠ k in l, k ∉ run.successful →
      activeConstraintSet c (u (k + 1)) = activeConstraintSet c z := by
  obtain ⟨w, hw, hwz, hwn⟩ := exists_continuous_normal_on_active_face hn hstat hnormal
  let y (k : ℕ) := run.x k + run.s k
  have hsn : Tendsto run.s l (𝓝 0) := squeeze_zero_norm hstep hΔ
  have hy : Tendsto y l (𝓝 z) := by simpa only [add_zero] using hx.add hsn
  let d (k : ℕ) := ‖-gradient f (run.x k) - w (y k)‖
  have hd : Tendsto d l (𝓝 0) := by
    simpa only [d, hwz, sub_self, norm_zero, Function.comp_apply] using
      ((hg.continuousAt.tendsto.comp hx).neg.sub (hw.continuousAt.tendsto.comp hy)).norm
  let a := κ * P.γ₁ / 2
  have ha : 0 < a := half_pos (mul_pos hκ P.gamma₁_pos)
  have hsmall₁ : ∀ᶠ k in l, 2 * β * run.Δ k + 2 * d k < a := by
    have hlim := (hΔ.const_mul (2 * β)).add (hd.const_mul 2)
    have hlim' : Tendsto (fun k ↦ 2 * β * run.Δ k + 2 * d k) l (𝓝 0) := by
      simpa only [mul_zero, add_zero] using hlim
    exact hlim'.eventually (gt_mem_nhds ha)
  have hsmall₂ : ∀ᶠ k in l, B * run.Δ k < (1 - P.η₁) * a := by
    have hpos := mul_pos (sub_pos.mpr (P.eta₁_le_eta₂.trans_lt P.eta₂_lt_one)) ha
    have hlim : Tendsto (fun k ↦ B * run.Δ k) l (𝓝 0) := by
      simpa only [mul_zero] using hΔ.const_mul B
    exact hlim.eventually (gt_mem_nhds hpos)
  have hsuc : Tendsto (fun k : ℕ ↦ k + 1) atTop atTop :=
    tendsto_atTop_mono (fun k ↦ Nat.le_succ k) tendsto_id
  filter_upwards [hmiss.filter_mono hl, (hsuc.eventually hmiss).filter_mono hl, hsmall₁, hsmall₂,
    hface]
    with k hmk hmk' hs₁ hs₂ hfacek
  intro hreject
  by_contra! hbad
  have hcenter := run.iterate_eq_of_unsuccessful hreject
  have hsame : activeConstraintSet c (y k) = activeConstraintSet c z := by
    apply hfacek
    by_contra! hbad
    exact hreject (run.verySuccessful_subset_successful (hmk hbad).2)
  have hr := (run.radius_update k).unsuccessful (lt_of_not_ge hreject)
  have hrad : run.Δ (k + 1) ≤ run.Δ k :=
    hr.2.trans (mul_le_of_le_one_left (run.delta_pos k).le P.gamma₂_lt_one.le)
  have hpredNew := (hmk' hbad).1
  have hTaylorNew := hTaylor (k + 1)
  rw [hcenter] at hpredNew hTaylorNew
  have hnewFeas := hfeas (k + 1)
  rw [hcenter] at hnewFeas
  have hcmp :=
    prediction_le_of_common_center hnewFeas (hwn _ (hfeas k) hsame) (hTaylor k) hTaylorNew
  have hdist : ‖run.s (k + 1) - run.s k‖ ≤ 2 * run.Δ k := by
    calc
      _ ≤ ‖run.s (k + 1)‖ + ‖run.s k‖ := norm_sub_le _ _
      _ ≤ run.Δ k + run.Δ k := add_le_add ((hstep _).trans hrad) (hstep _)
      _ = _ := by ring
  have hsq : β * run.Δ (k + 1) ^ 2 ≤ β * run.Δ k ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (run.delta_pos _).le hrad _) hβ
  have hdterm := mul_le_mul_of_nonneg_left hdist (norm_nonneg
    (-gradient f (run.x k) - w (y k)))
  have hlow := (mul_le_mul_of_nonneg_left hr.1 hκ.le).trans hpredNew
  have hbudget := mul_lt_mul_of_pos_right hs₁ (run.delta_pos k)
  have hpred : a * run.Δ k ≤ run.model k (run.x k) - run.model k (y k) := by
    change _ ≤ run.model k (run.x k) - run.model k (run.x k + run.s k)
    change d k * ‖run.s (k + 1) - run.s k‖ ≤ d k * (2 * run.Δ k) at hdterm
    change _ ≤ _ + _ + _ + d k * ‖run.s (k + 1) - run.s k‖ at hcmp
    dsimp only [a] at hbudget ⊢
    nlinarith only [hcmp, hsq, hdterm, hlow, hbudget]
  have hp := (mul_pos ha (run.delta_pos k)).trans_le hpred
  have he : |f (y k) - (f (run.x k) - (run.model k (run.x k) - run.model k (y k)))| ≤
      (1 - P.η₁) * (run.model k (run.x k) - run.model k (y k)) := by
    rw [hval k, sub_sub_cancel]
    apply (herr k).trans
    have h₁ := mul_le_mul_of_nonneg_right hs₂.le (run.delta_pos k).le
    have h₂ := mul_le_mul_of_nonneg_left hpred
      (sub_nonneg.mpr (P.eta₁_le_eta₂.trans P.eta₂_lt_one.le))
    nlinarith only [h₁, h₂]
  apply hreject
  simpa [BTRRun.successful, btrRatio, y] using le_reductionRatio_of_abs_sub_le hp he

open Optimization Chapter06 in
/-- **Lemma 12.3.7** of [conn2000trust], the rejection step in the proof. Consider a run of the
basic trust-region algorithm, and let $u_k$ be points. Let $\nabla f$ and the $\nabla c_i$ be
continuous, let $\nabla f$ have strictly positive active multipliers at $z$, and let
$-\nabla c_i(y) \in N(y)$ for every $y \in C$ and $i \in \mathcal{A}(y)$. Suppose that
$x_k \to z$, $\Delta_k \to 0$, $\|s_k\| \le \Delta_k$ and $x_k + s_k \in C$ for all $k$, and
that eventually $\mathcal{A}(u_k) = \mathcal{A}(z)$ implies
$\mathcal{A}(x_k + s_k) = \mathcal{A}(z)$. Let $\beta \ge 0$, $\kappa > 0$ and $B$ be constants
with
$$|m_k(x_k + s_k) - m_k(x_k) - \langle \nabla f(x_k), s_k \rangle| \le \beta \Delta_k^2, \qquad
  f(x_k) = m_k(x_k), \qquad |f(x_k + s_k) - m_k(x_k + s_k)| \le B \Delta_k^2$$
for all $k$, and suppose that eventually $\mathcal{A}(u_k) \neq \mathcal{A}(z)$ implies
$\kappa \Delta_k \le m_k(x_k) - m_k(x_k + s_k)$ and that iteration $k$ is very successful. Then
eventually, if iteration $k$ is not successful, then $\mathcal{A}(u_{k+1}) = \mathcal{A}(z)$.

A rejected step $x_k + s_k$ inherits the identified active set of its Cauchy point, which allows
the comparison `ConnGouldToint.Chapter12.prediction_le_of_common_center` at the common center
$x_{k+1} = x_k$.

**Reading.** The proof steps use explicit lower bounds for tangent projection, radius and model
controls, or face preservation, according to the claimed implication. The successful-trial
conclusion assumes vanishing radii and infinitely many successful iterations.
-/
theorem eventually_rejection_then_identified [Fintype ι] [CompleteSpace E]
    {C : Set E} {c : ι → E → ℝ} {f : E → ℝ} {P : BTRParams}
    {sufficient : ℕ → (E → ℝ) → E → E → Prop}
    (run : BTRRun f P sufficient) {u : ℕ → E} {z : E}
    (hg : Continuous (gradient f)) (hn : ∀ i, Continuous (gradient (c i)))
    (hstat : HasStrictActiveMultipliers c (fun i ↦ gradient (c i)) (gradient f) z)
    (hnormal : ∀ y ∈ C, ∀ i ∈ activeConstraintSet c y,
      -gradient (c i) y ∈ normalDirections C y)
    (hx : Tendsto run.x atTop (𝓝 z)) (hΔ : Tendsto run.Δ atTop (𝓝 0))
    (hstep : ∀ k, ‖run.s k‖ ≤ run.Δ k)
    (hfeas : ∀ k, run.x k + run.s k ∈ C)
    (hface : ∀ᶠ k in atTop, activeConstraintSet c (u k) = activeConstraintSet c z →
      activeConstraintSet c (run.x k + run.s k) = activeConstraintSet c z)
    {β B κ : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ)
    (hTaylor : ∀ k, |run.model k (run.x k + run.s k) - run.model k (run.x k) -
      ⟪gradient f (run.x k), run.s k⟫| ≤ β * run.Δ k ^ 2)
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (herr : ∀ k, |f (run.x k + run.s k) - run.model k (run.x k + run.s k)| ≤ B * run.Δ k ^ 2)
    (hmiss : ∀ᶠ k in atTop, activeConstraintSet c (u k) ≠ activeConstraintSet c z →
      κ * run.Δ k ≤ run.model k (run.x k) - run.model k (run.x k + run.s k) ∧
      k ∈ run.verySuccessful) :
    ∀ᶠ k in atTop, k ∉ run.successful →
      activeConstraintSet c (u (k + 1)) = activeConstraintSet c z :=
  eventually_rejection_then_identifiedOn run le_rfl hg hn hstat hnormal hx hΔ
    hstep hfeas hface hβ hκ hTaylor hval herr hmiss

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
open Chapter06 in
private theorem frequently_successful_identified_of_frequently_identified
    {P : BTRParams} {ρ : ℕ → ℝ} {u : ℕ → E} {c : ι → E → ℝ} {A : Set ι}
    (hidentified : ∃ᶠ k in atTop, activeConstraintSet c (u k) = A)
    (hnext : ∀ᶠ k in atTop, ρ k < P.η₁ → activeConstraintSet c (u (k + 1)) = A)
    (hsuccess : ∃ᶠ k in atTop, P.η₁ ≤ ρ k) :
    ∃ᶠ k in atTop, P.η₁ ≤ ρ k ∧ activeConstraintSet c (u k) = A := by
  classical
  apply frequently_atTop.mpr
  intro N
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hnext
  obtain ⟨i, hi, hactive⟩ := frequently_atTop.mp hidentified (max N N₀)
  have hiN := (le_max_left N N₀).trans hi
  have hi₀ := (le_max_right N N₀).trans hi
  have hex : ∃ j, P.η₁ ≤ ρ (i + j) := by
    obtain ⟨k, hk, hsk⟩ := frequently_atTop.mp hsuccess i
    exact ⟨k - i, by simpa [Nat.add_sub_of_le hk] using hsk⟩
  let j := Nat.find hex
  have hj : P.η₁ ≤ ρ (i + j) := Nat.find_spec hex
  refine ⟨i + j, hiN.trans (Nat.le_add_right _ _), hj, ?_⟩
  cases hjn : j with
  | zero => simpa using hactive
  | succ l =>
    have hfail : ρ (i + l) < P.η₁ :=
      lt_of_not_ge (Nat.find_min hex (show l < j by rw [hjn]; exact Nat.lt_succ_self l))
    exact hN₀ (i + l) (hi₀.trans (Nat.le_add_right _ _)) hfail

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
open Chapter06 in
/-- **Lemma 12.3.7** of [conn2000trust], successful identified trials at vanishing radii. Let
$\Delta_k > 0$ with $\Delta_k \to 0$, and let the radii follow the update (6.1.5) with ratios
$\rho_k$. Suppose that eventually $\mathcal{A}(u_k) \neq \mathcal{A}$ implies
$\rho_k \ge \eta_2$, that eventually $\rho_k < \eta_1$ implies
$\mathcal{A}(u_{k+1}) = \mathcal{A}$, and that $\rho_k \ge \eta_1$ for infinitely many $k$. Then
there are infinitely many $k$ with $\rho_k \ge \eta_1$ and $\mathcal{A}(u_k) = \mathcal{A}$.

**Reading.** The proof steps use explicit lower bounds for tangent projection, radius and model
controls, or face preservation, according to the claimed implication. The successful-trial
conclusion assumes vanishing radii and infinitely many successful iterations.
-/
theorem frequently_successful_identified_of_radius_tendsto_zero
    {P : BTRParams} {ρ Δ : ℕ → ℝ} {u : ℕ → E} {c : ι → E → ℝ} {A : Set ι}
    (hΔ : Tendsto Δ atTop (𝓝 0)) (hpos : ∀ k, 0 < Δ k)
    (hupdate : ∀ k, BTRRadiusUpdate P (ρ k) (Δ k) (Δ (k + 1)))
    (hmiss : ∀ᶠ k in atTop, activeConstraintSet c (u k) ≠ A → P.η₂ ≤ ρ k)
    (hnext : ∀ᶠ k in atTop, ρ k < P.η₁ → activeConstraintSet c (u (k + 1)) = A)
    (hsuccess : ∃ᶠ k in atTop, P.η₁ ≤ ρ k) :
    ∃ᶠ k in atTop, P.η₁ ≤ ρ k ∧ activeConstraintSet c (u k) = A :=
  frequently_successful_identified_of_frequently_identified
    (frequently_active_eq_at_Cauchy_trial_of_radius_tendsto_zero hΔ hpos hupdate hmiss)
    hnext hsuccess

omit [InnerProductSpace ℝ E] in
private theorem convergent_subseq_of_compact_atTop {K : Set E} {x : ℕ → E} {j : ℕ → ℕ}
    (hK : IsCompact K) (hx : ∀ k, x k ∈ K) (hj : Tendsto j atTop atTop) :
    ∃ z : E, ∃ i : ℕ → ℕ, StrictMono i ∧ StrictMono (j ∘ i) ∧
      Tendsto (x ∘ (j ∘ i)) atTop (𝓝 z) := by
  obtain ⟨q, hq, hjq⟩ := strictMono_subseq_of_tendsto_atTop hj
  obtain ⟨z, _, r, hr, hz⟩ := hK.isSeqCompact (fun k ↦ hx (j (q k)))
  exact ⟨z, q ∘ r, hq.comp hr, hjq.comp hr, hz⟩

omit [InnerProductSpace ℝ E] in
private theorem eventually_of_compact_local {K : Set E} {x : ℕ → E} {p : ℕ → Prop}
    (hK : IsCompact K) (hx : ∀ k, x k ∈ K)
    (hlocal : ∀ z (j : ℕ → ℕ), StrictMono j → Tendsto (x ∘ j) atTop (𝓝 z) →
      ∀ᶠ k in atTop, p (j k)) :
    ∀ᶠ k in atTop, p k := by
  by_contra! hbad
  obtain ⟨j, hj, hjbad⟩ := extraction_of_frequently_atTop hbad
  obtain ⟨z, i, hi, hji, hz⟩ := convergent_subseq_of_compact_atTop hK hx hj.tendsto_atTop
  obtain ⟨k, hk⟩ := (hlocal z (j ∘ i) hji hz).exists
  exact hjbad (i k) hk

omit [InnerProductSpace ℝ E] in
private theorem exists_pos_eventually_of_compact_local {K : Set E} {x : ℕ → E}
    {p : ℝ → ℕ → Prop} (hK : IsCompact K) (hx : ∀ k, x k ∈ K)
    (hmono : ∀ {a b : ℝ} {k : ℕ}, a ≤ b → p b k → p a k)
    (hlocal : ∀ z (j : ℕ → ℕ), StrictMono j → Tendsto (x ∘ j) atTop (𝓝 z) →
      ∃ a > 0, ∀ᶠ k in atTop, p a (j k)) :
    ∃ a > 0, ∀ᶠ k in atTop, p a k := by
  classical
  by_contra! hbad
  let a (n : ℕ) := (1 : ℝ) / ((n : ℝ) + 1)
  have hbad' (n : ℕ) : ∃ k ≥ n, ¬p (a n) k :=
    frequently_atTop.mp (hbad (a n) (by dsimp [a]; positivity)) n
  choose j hj hjbad using hbad'
  have hjtop : Tendsto j atTop atTop := tendsto_atTop_mono hj tendsto_id
  obtain ⟨z, i, hi, hji, hz⟩ := convergent_subseq_of_compact_atTop hK hx hjtop
  obtain ⟨b, hb, hgood⟩ := hlocal z (j ∘ i) hji hz
  have halim : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hab := (halim.comp hi.tendsto_atTop).eventually (gt_mem_nhds hb)
  obtain ⟨k, hak, hpk⟩ := (hab.and hgood).exists
  exact hjbad (i k) (hmono hak.le hpk)

open Chapter06 in
private theorem eventually_iterate_eq_limit_of_finitely_successful
    {f : E → ℝ} {P : BTRParams} {sufficient : ℕ → (E → ℝ) → E → E → Prop}
    (run : BTRRun f P sufficient) {z : E}
    (hx : Tendsto run.x atTop (𝓝 z)) (hf : ¬ ∃ᶠ k in atTop, k ∈ run.successful) :
    ∀ᶠ k in atTop, run.x k = z := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (not_frequently.mp hf)
  have hconst : ∀ k ≥ N, run.x k = run.x N := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => rfl
    | succ k hk ih => exact (run.iterate_eq_of_unsuccessful (hN k hk)).trans ih
  have hxN : run.x N = z := tendsto_nhds_unique
    (tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨N, fun k hk ↦ (hconst k hk).symm⟩)) hx
  exact eventually_atTop.mpr ⟨N, fun k hk ↦ (hconst k hk).trans hxN⟩

/-- **Section 12.3** of [conn2000trust], the tangent qualification at late Cauchy points. Let $E$ be
a finite-dimensional real inner product space, let $C$ satisfy AC.7, and let each $c_i$ be
strictly differentiable at every point with continuous $c_i$ and $\nabla c_i$. Let $K$ be
compact, $x_k \in K$, and let every limit of a subsequence of $(x_k)$ lie in $S$, where the
active gradients are linearly independent at every point of $S$. If $u_k - x_k \to 0$ and
eventually $u_k \in C$, then eventually the tangent qualification holds at $u_k$. -/
theorem eventually_activeLinearizedConeMatches_of_compact [Fintype ι] [CompleteSpace E]
    [FiniteDimensional ℝ E] {C K S : Set E} {c : ι → E → ℝ} {x u : ℕ → E}
    (hset : Chapter03.AC7 C c)
    (hc : ∀ i, Continuous (c i)) (hn : ∀ i, Continuous (gradient (c i)))
    (hder : ∀ i y, HasStrictFDerivAt (c i) (fderiv ℝ (c i) y) y)
    (hK : IsCompact K) (hx : ∀ k, x k ∈ K)
    (hlim : ∀ z (j : ℕ → ℕ), StrictMono j → Tendsto (x ∘ j) atTop (𝓝 z) → z ∈ S)
    (hind : ∀ z ∈ S, LinearIndependent ℝ (fun i : activeConstraintSet c z ↦ gradient (c i) z))
    (hu : Tendsto (fun k ↦ u k - x k) atTop (𝓝 0)) (hfeas : ∀ᶠ k in atTop, u k ∈ C) :
    ∀ᶠ k in atTop, Chapter03.ActiveLinearizedConeMatches C c (u k) := by
  apply eventually_of_compact_local hK hx
  intro z j hj hz
  have hzS := hlim z j hj hz
  have huj : Tendsto (fun k ↦ u (j k)) atTop (𝓝 z) := by
    simpa only [Function.comp_apply, sub_add_cancel, zero_add] using
      (hu.comp hj.tendsto_atTop).add hz
  filter_upwards [huj.eventually (eventually_activeGradient_independent hc hn (hind z hzS)),
    hj.tendsto_atTop.eventually hfeas] with k hindk hfk
  exact activeLinearizedConeMatches_of_activeGradient_independent hset hfk
    (fun i ↦ hder i _) hindk

open Optimization Chapter06 in
/-- **Theorem 12.3.8** of [conn2000trust], corrected, for compact runs with vanishing Cauchy and
iterate displacements. Let $E$ be a finite-dimensional real inner product space, let $C$ satisfy
AC.2 and AC.7, let $c_i$, $\nabla c_i$ and $\nabla f$ be continuous, and let
$-\nabla c_i(y) \in N(y)$ for every $y \in C$ and $i \in \mathcal{A}(y)$. Consider a run of the
basic trust-region algorithm for $f$, parameters of the generalized Cauchy point, and points
$u_k$. Let $S$ and $K$ be compact, $x_k \in K$, and let $S$ be exactly the set of limits of
subsequences of $(x_k)$. At every $z \in S$ let the active gradients be linearly independent and
let $\nabla f$ have strictly positive active multipliers. Let $\beta > 0$ and $B$ be constants.
Suppose that

* $\operatorname{dist}(x_{k+1}, x_k) \to 0$ and $u_k - x_k \to 0$, and eventually the tangent
  qualification holds at $u_k$;
* for every $k$: $x_k \in C$, $\|s_k\| \le \Delta_k$, $x_k + s_k \in C$, $u_k$ is an approximate
  generalized Cauchy point for $C$, $f$, $m_k$, $x_k$ and $\Delta_k$,
  $m_k(x_k + s_k) \le m_k(u_k)$, and $\mathcal{A}(u_k) \subseteq \mathcal{A}(x_k + s_k)$ (AA.5);
* for every $k$: $f(x_k) = m_k(x_k)$, $|f(x_k + s_k) - m_k(x_k + s_k)| \le B \Delta_k^2$, and
$$m_k(u_k) - m_k(x_k) - \langle \nabla f(x_k), u_k - x_k \rangle \le \tfrac{\beta}{2} \|u_k -
  x_k\|^2, \qquad |m_k(x_k + s_k) - m_k(x_k) - \langle \nabla f(x_k), s_k \rangle| \le \beta
  \Delta_k^2.$$

Then there is $\mathcal{A}$ with $\mathcal{A}(z) = \mathcal{A}$ for all $z \in S$, and
eventually $\mathcal{A}(x_k) = \mathcal{A}$ and $\mathcal{A}(u_k) = \mathcal{A}$.

**Correction.** The printed theorem fails at the Cauchy points for nonvanishing radii and at the
iterates for constant radii; see
`ConnGouldToint.Chapter12.theorem_12_3_8_nonvanishing_radius_counterexample` and
`ConnGouldToint.Chapter12.theorem_12_3_8_iterate_identification_counterexample`. This version
adds the vanishing Cauchy displacements $u_k - x_k \to 0$ and iterate displacements
$x_{k+1} - x_k \to 0$. The limit set may have several connected components.

A misidentified trial gives a model decrease linear in the radius and is very successful. A
rejected trial can have a large step only if it does not precede a misidentified trial.

**Correction.** The source claims unconditional eventual identification under its standing
hypotheses. These variants add vanishing Cauchy and accepted-iterate displacements, vanishing trial
displacements with Cauchy control, vanishing radii, or convergent runs with bounded positive
projected trial times and the specified normal and face conditions.
-/
theorem theorem_12_3_8_of_compact_run_of_Cauchy_displacements_tendsto_zero
    [Fintype ι] [CompleteSpace E] [FiniteDimensional ℝ E]
    {C : Set E} {c : ι → E → ℝ} {f : E → ℝ} {P : BTRParams}
    {sufficient : ℕ → (E → ℝ) → E → E → Prop}
    (run : BTRRun f P sufficient) (Q : GeneralizedCauchyParams) {u : ℕ → E} {S K : Set E}
    (hC : Chapter03.AC2 C) (hset : Chapter03.AC7 C c)
    (hc : ∀ i, Continuous (c i)) (hn : ∀ i, Continuous (gradient (c i)))
    (hg : Continuous (gradient f))
    (hind : ∀ z ∈ S, LinearIndependent ℝ (fun i : activeConstraintSet c z ↦ gradient (c i) z))
    (hstat : ∀ z ∈ S, HasStrictActiveMultipliers c (fun i ↦ gradient (c i)) (gradient f) z)
    (hnormal : ∀ y ∈ C, ∀ i ∈ activeConstraintSet c y,
      -gradient (c i) y ∈ normalDirections C y)
    (hS : IsCompact S) (hK : IsCompact K) (hxK : ∀ k, run.x k ∈ K)
    (hlim : ∀ z, z ∈ S ↔ ∃ j : ℕ → ℕ, StrictMono j ∧ Tendsto (run.x ∘ j) atTop (𝓝 z))
    (hxs : Tendsto (fun k ↦ dist (run.x (k + 1)) (run.x k)) atTop (𝓝 0))
    (hu' : Tendsto (fun k ↦ u k - run.x k) atTop (𝓝 0))
    (hxC : ∀ k, run.x k ∈ C) (hstep : ∀ k, ‖run.s k‖ ≤ run.Δ k)
    (hfeas : ∀ k, run.x k + run.s k ∈ C)
    (hface : ∀ k, activeConstraintSet c (u k) ⊆ activeConstraintSet c (run.x k + run.s k))
    (hQ : ∀ᶠ k in atTop, Chapter03.ActiveLinearizedConeMatches C c (u k))
    (htrial : ∀ k, IsApproxGeneralizedCauchyPoint Q C f (run.model k) (run.x k) (run.Δ k) (u k))
    (hcmp : ∀ k, run.model k (run.x k + run.s k) ≤ run.model k (u k))
    {β B : ℝ} (hβ : 0 < β)
    (hTaylorC : ∀ k, run.model k (u k) -
      (run.model k (run.x k) + ⟪gradient f (run.x k), u k - run.x k⟫) ≤
      β * ‖u k - run.x k‖ ^ 2 / 2)
    (hTaylor : ∀ k, |run.model k (run.x k + run.s k) - run.model k (run.x k) -
      ⟪gradient f (run.x k), run.s k⟫| ≤ β * run.Δ k ^ 2)
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (herr : ∀ k, |f (run.x k + run.s k) - run.model k (run.x k + run.s k)| ≤ B * run.Δ k ^ 2) :
    ∃ A : Set ι, (∀ z ∈ S, activeConstraintSet c z = A) ∧
      ∀ᶠ k in atTop, activeConstraintSet c (run.x k) = A ∧ activeConstraintSet c (u k) = A := by
  classical
  have hsucc_eq (k : ℕ) (hk : k ∈ run.successful) :
      run.x (k + 1) = run.x k + run.s k := by
    rw [run.iterate_update, acceptStep_of_le hk]
  obtain ⟨A, hA⟩ := activeConstraintSet_eq_on_limits_of_vanishing_steps hS hK hxK hlim hxs
    hc hn hg hind hstat
  have huLocal (z : E) (j : ℕ → ℕ) (hj : StrictMono j)
      (hz : Tendsto (run.x ∘ j) atTop (𝓝 z)) : Tendsto (u ∘ j) atTop (𝓝 z) := by
    change Tendsto (fun k ↦ u (j k)) atTop (𝓝 z)
    simpa only [Function.comp_apply, sub_add_cancel, zero_add] using
      (hu'.comp hj.tendsto_atTop).add hz
  have hfaceAccepted : ∀ᶠ k in atTop, k ∈ run.successful →
      activeConstraintSet c (u k) = A → activeConstraintSet c (run.x (k + 1)) = A := by
    apply eventually_of_compact_local hK hxK
    intro z j hj hz
    have hzS := (hlim z).mpr ⟨j, hj, hz⟩
    have hsnj : Tendsto (fun k ↦ run.x (j k + 1) - run.x (j k)) atTop (𝓝 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      have ht : Tendsto (fun k ↦ dist (run.x (j k + 1)) (run.x (j k))) atTop (𝓝 0) :=
        hxs.comp hj.tendsto_atTop
      simpa only [dist_eq_norm] using ht
    have hnextx : Tendsto (fun k ↦ run.x (j k + 1)) atTop (𝓝 z) := by
      simpa only [Function.comp_apply, sub_add_cancel, zero_add] using hsnj.add hz
    filter_upwards [eventually_activeConstraintSet_subset_of_tendsto hc hnextx] with k hk
    intro hks huA
    exact Set.Subset.antisymm ((hA z hzS) ▸ hk)
      ((hsucc_eq (j k) hks).symm ▸ (huA ▸ hface (j k)))
  let bad : Set ℕ := {k | activeConstraintSet c (u k) ≠ A}
  have huFeas (k : ℕ) : u k ∈ C := by
    obtain ⟨t, _, he, _⟩ := htrial k
    rw [he]
    exact projectedRay_mem hC.1 hC.2.1 hC.2.2 (run.x k) (-gradient f (run.x k)) t
  have hgap0 : ∃ γ > 0, ∀ᶠ k in atTop, k ∈ bad →
      γ ≤ ‖bestApprox (tangentDirections C (u k)) (-gradient f (run.x k))‖ := by
    apply exists_pos_eventually_of_compact_local hK hxK
    · intro a b k hab hb hk
      exact hab.trans (hb hk)
    · intro z j hj hz
      have hzS := (hlim z).mpr ⟨j, hj, hz⟩
      obtain ⟨γ, hγ, hgap⟩ := eventually_tangentProjection_lower_of_active_mismatch
        hC hset hc hn hg (hind z hzS) (hstat z hzS) hz (huLocal z j hj hz)
        (.of_forall fun k ↦ huFeas (j k)) (hj.tendsto_atTop.eventually hQ)
      refine ⟨γ, hγ, hgap.mono fun k hgk hk ↦ hgk ?_⟩
      simpa only [bad, Set.mem_ofPred_eq, Function.comp_apply, hA z hzS] using hk
  obtain ⟨γ, hγ, hgap⟩ := hgap0
  obtain ⟨G, hG⟩ := hK.bddAbove_image hg.norm.continuousOn
  let D := max Q.radiusFraction⁻¹ (Q.endpointFactor * G / γ)
  have hr := tendsto_zero_iff_norm_tendsto_zero.mp hu'
  have hΔbad : Tendsto run.Δ (atTop ⊓ 𝓟 bad) (𝓝 0) := by
    refine squeeze_zero' (g := fun k ↦ D * ‖u k - run.x k‖)
      (.of_forall fun k ↦ (run.delta_pos k).le) ?_ ?_
    · apply eventually_inf_principal.mpr
      have ht : Tendsto (fun k ↦ β * ‖u k - run.x k‖ / 2) atTop (𝓝 0) := by
        simpa only [mul_zero, zero_div] using (hr.const_mul β).div_const (2 : ℝ)
      filter_upwards [hgap, ht.eventually
        (gt_mem_nhds (mul_pos (sub_pos.mpr Q.lower_lt_one) hγ))] with k hgk htk
      intro hk
      exact radius_le_mul_displacement_of_tangentProjection_lower Q hC.2.1 hC.2.2
        (hxC k) (run.delta_pos k) hγ (hG ⟨run.x k, hxK k, rfl⟩) htk
        (htrial k) (hgk hk) (hTaylorC k)
    · simpa only [mul_zero] using (hr.const_mul D).mono_left inf_le_left
  have hmiss0 : ∃ κ > 0, ∀ᶠ k in atTop, activeConstraintSet c (u k) ≠ A →
      κ * run.Δ k ≤ run.model k (run.x k) - run.model k (run.x k + run.s k) ∧
      k ∈ run.verySuccessful := by
    apply exists_pos_eventually_of_compact_local hK hxK
    · intro a b k hab hb hneq
      obtain ⟨hpred, hvery⟩ := hb hneq
      exact ⟨(mul_le_mul_of_nonneg_right hab (run.delta_pos k).le).trans hpred, hvery⟩
    · intro z j hj hz
      have hzS := (hlim z).mpr ⟨j, hj, hz⟩
      let l := map j atTop ⊓ 𝓟 bad
      have hl : l ≤ atTop ⊓ 𝓟 bad := inf_le_inf_right _ hj.tendsto_atTop
      have hxj : Tendsto run.x (map j atTop) (𝓝 z) := hz
      have huj : Tendsto u (map j atTop) (𝓝 z) := huLocal z j hj hz
      obtain ⟨κ, hκ, hh⟩ := eventually_verySuccessful_of_active_mismatch
        (l := l) (m := run.model) (s := run.s) Q P hC hset hc hn hg
        (hind z hzS) (hstat z hzS) (hxj.mono_left inf_le_left)
        (huj.mono_left inf_le_left) (hΔbad.mono_left hl)
        (hQ.filter_mono (hl.trans inf_le_left)) hβ
        (.of_forall fun k ↦ ⟨hxC k, run.delta_pos k, htrial k⟩)
        (.of_forall hTaylorC) (.of_forall fun k ↦ ⟨hval k, hcmp k, herr k⟩)
      refine ⟨κ, hκ, ?_⟩
      have hh' := eventually_inf_principal.mp hh
      exact hh'.mono fun k hk hneq ↦ hk hneq (by rwa [hA z hzS])
  obtain ⟨κ, hκ, hmiss⟩ := hmiss0
  have hnext : ∀ᶠ k in atTop, k ∉ run.successful → activeConstraintSet c (u (k + 1)) = A := by
    apply eventually_of_compact_local hK hxK
    intro z j hj hz
    have hzS := (hlim z).mpr ⟨j, hj, hz⟩
    have hAz := hA z hzS
    let R : Set ℕ := {k | k ∉ run.successful ∧ k + 1 ∈ bad}
    let l := map j atTop ⊓ 𝓟 R
    have hl : l ≤ atTop := inf_le_left.trans hj.tendsto_atTop
    have hR : ∀ᶠ k in l, k ∈ R :=
      (show ∀ᶠ k in 𝓟 R, k ∈ R from mem_principal_self R).filter_mono inf_le_right
    have hsucc : Tendsto (fun k : ℕ ↦ k + 1) l (atTop ⊓ 𝓟 bad) := by
      apply tendsto_inf.mpr
      refine ⟨?_, tendsto_principal.mpr (hR.mono fun _ hk ↦ hk.2)⟩
      exact (tendsto_atTop_mono (fun k ↦ Nat.le_succ k) tendsto_id).mono_left hl
    have hΔl : Tendsto run.Δ l (𝓝 0) := by
      refine squeeze_zero' (g := fun k ↦ run.Δ (k + 1) / P.γ₁)
        (.of_forall fun k ↦ (run.delta_pos k).le) ?_ ?_
      · filter_upwards [hR] with k hk
        exact (le_div_iff₀ P.gamma₁_pos).mpr (by simpa only [mul_comm] using
          ((run.radius_update k).unsuccessful (lt_of_not_ge hk.1)).1)
      · simpa only [zero_div, Function.comp_apply] using (hΔbad.comp hsucc).div_const P.γ₁
    have hxj : Tendsto run.x (map j atTop) (𝓝 z) := hz
    have hxl := hxj.mono_left (show l ≤ map j atTop from inf_le_left)
    have hyl : Tendsto (fun k ↦ run.x k + run.s k) l (𝓝 z) := by
      simpa only [add_zero] using hxl.add (squeeze_zero_norm hstep hΔl)
    have hfaceR : ∀ᶠ k in l, activeConstraintSet c (u k) = activeConstraintSet c z →
        activeConstraintSet c (run.x k + run.s k) = activeConstraintSet c z :=
      (eventually_activeConstraintSet_subset_of_tendsto hc hyl).mono fun k hk huA ↦
        Set.Subset.antisymm hk (huA ▸ hface k)
    have he := eventually_rejection_then_identifiedOn run hl hg hn (hstat z hzS)
      hnormal hxl hΔl hstep hfeas hfaceR
      hβ.le hκ hTaylor hval herr (hAz.symm ▸ hmiss)
    have hh := eventually_inf_principal.mp (hAz ▸ he)
    exact hh.mono fun k hk hrj ↦ by
      by_contra hbad
      exact hbad (hk ⟨hrj, hbad⟩ hrj)
  have hidentified : ∃ᶠ k in atTop, activeConstraintSet c (u k) = A := by
    by_contra! hbad
    have he : Tendsto run.Δ atTop (𝓝 0) :=
      hΔbad.mono_left (le_inf le_rfl (le_principal_iff.mpr hbad))
    exact (not_frequently.mpr hbad)
      (frequently_active_eq_at_Cauchy_trial_of_radius_tendsto_zero he run.delta_pos
        run.radius_update
        (hmiss.mono fun _ hk h ↦ (hk h).2))
  have hkeep : ∀ᶠ k in atTop, activeConstraintSet c (run.x k) = A →
      activeConstraintSet c (u k) = A := by
    apply eventually_of_compact_local hK hxK
    intro z j hj hz
    have hzS := (hlim z).mpr ⟨j, hj, hz⟩
    have hh := eventually_CauchyTrial_preserves_active_face
      hC hset hc hn hg (hind z hzS) (hstat z hzS) hnormal hz (huLocal z j hj hz)
      (hj.tendsto_atTop.eventually hQ) (.of_forall fun k ↦ by
        obtain ⟨t, ht, he, _⟩ := htrial (j k)
        exact ⟨hxC (j k), t, ht, he⟩)
    exact (hA z hzS) ▸ hh
  have hbase : ∀ᶠ k in atTop, activeConstraintSet c (run.x k) = A := by
    by_cases hf : ∃ᶠ k in atTop, k ∈ run.successful
    · have hseed := frequently_successful_identified_of_frequently_identified hidentified
        (hnext.mono fun _ hk hr ↦ hk (not_le.mpr hr)) hf
      obtain ⟨N, hN⟩ := eventually_atTop.mp (hkeep.and hfaceAccepted)
      obtain ⟨j, hj, hjS, hjA⟩ := frequently_atTop.mp hseed N
      have hjx : activeConstraintSet c (run.x (j + 1)) = A := (hN j hj).2 hjS hjA
      refine eventually_atTop.mpr ⟨j + 1, fun k hk ↦ ?_⟩
      induction k, hk using Nat.le_induction with
      | base => exact hjx
      | succ k hk ih =>
        by_cases hks : k ∈ run.successful
        · have hkN := hj.trans ((Nat.le_succ j).trans hk)
          exact (hN k hkN).2 hks ((hN k hkN).1 ih)
        · rwa [run.iterate_eq_of_unsuccessful hks]
    · obtain ⟨N, hN⟩ := eventually_atTop.mp (not_frequently.mp hf)
      have hconst : ∀ k ≥ N, run.x k = run.x N := by
        intro k hk
        induction k, hk using Nat.le_induction with
        | base => rfl
        | succ k hk ih => exact (run.iterate_eq_of_unsuccessful (hN k hk)).trans ih
      have hlimN : Tendsto run.x atTop (𝓝 (run.x N)) :=
        tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨N, fun k hk ↦ (hconst k hk).symm⟩)
      have hAN := hA _ ((hlim _).mpr ⟨id, strictMono_id, hlimN⟩)
      exact eventually_atTop.mpr
        ⟨N, fun k hk ↦ (congrArg (activeConstraintSet c) (hconst k hk)).trans hAN⟩
  exact ⟨A, hA, hbase.and (hbase.mp hkeep)⟩

open Optimization Chapter06 in
/-- **Theorem 12.3.8** of [conn2000trust], corrected, for smooth constraints and compact runs. Let
$E$ be a finite-dimensional real inner product space, let $C$ satisfy AC.2 and AC.7, and let the
$c_i$ and $f$ be continuously differentiable. Suppose that the run, the points $u_k$, the
compact sets $S$ and $K$, and the constants $\beta > 0$ and $B$ satisfy all hypotheses of
`ConnGouldToint.Chapter12.theorem_12_3_8_of_compact_run_of_Cauchy_displacements_tendsto_zero`
except two, which are dropped: the normality of $-\nabla c_i$ and the tangent qualification at
$u_k$. The remaining hypotheses are AO.1c and strictly positive active multipliers at every
point of the limit set $S$, $\operatorname{dist}(x_{k+1}, x_k) \to 0$, $u_k - x_k \to 0$, the
conditions on $x_k$, $s_k$ and $u_k$ including AA.5, and the model estimates with $\beta$ and
$B$. Then there is $\mathcal{A}$ with $\mathcal{A}(z) = \mathcal{A}$ for all $z \in S$, and
eventually $\mathcal{A}(x_k) = \mathcal{A}$ and $\mathcal{A}(u_k) = \mathcal{A}$.

**Correction.** This version of the printed theorem, which fails in general, adds vanishing
Cauchy and iterate displacements; see
`ConnGouldToint.Chapter12.theorem_12_3_8_of_compact_run_of_Cauchy_displacements_tendsto_zero`.

The smooth constraints make the inward gradients normal to $C$, and active-gradient independence
at the cluster points gives the tangent qualification at the late Cauchy points
(`ConnGouldToint.Chapter12.eventually_activeLinearizedConeMatches_of_compact`).

**Correction.** The source claims unconditional eventual identification under its standing
hypotheses. These variants add vanishing Cauchy and accepted-iterate displacements, vanishing trial
displacements with Cauchy control, vanishing radii, or convergent runs with bounded positive
projected trial times and the specified normal and face conditions.
-/
theorem theorem_12_3_8_of_smooth_compact_run
    [Fintype ι] [CompleteSpace E] [FiniteDimensional ℝ E]
    {C : Set E} {c : ι → E → ℝ} {f : E → ℝ} {P : BTRParams}
    {sufficient : ℕ → (E → ℝ) → E → E → Prop}
    (run : BTRRun f P sufficient) (Q : GeneralizedCauchyParams) {u : ℕ → E} {S K : Set E}
    (hC : Chapter03.AC2 C) (hset : Chapter03.AC7 C c)
    (hc : ∀ i, ContDiff ℝ 1 (c i)) (hf : ContDiff ℝ 1 f)
    (hind : ∀ z ∈ S, LinearIndependent ℝ (fun i : activeConstraintSet c z ↦ gradient (c i) z))
    (hstat : ∀ z ∈ S, HasStrictActiveMultipliers c (fun i ↦ gradient (c i)) (gradient f) z)
    (hS : IsCompact S) (hK : IsCompact K) (hxK : ∀ k, run.x k ∈ K)
    (hlim : ∀ z, z ∈ S ↔ ∃ j : ℕ → ℕ, StrictMono j ∧ Tendsto (run.x ∘ j) atTop (𝓝 z))
    (hxs : Tendsto (fun k ↦ dist (run.x (k + 1)) (run.x k)) atTop (𝓝 0))
    (hu' : Tendsto (fun k ↦ u k - run.x k) atTop (𝓝 0))
    (hxC : ∀ k, run.x k ∈ C) (hstep : ∀ k, ‖run.s k‖ ≤ run.Δ k)
    (hfeas : ∀ k, run.x k + run.s k ∈ C)
    (hface : ∀ k, activeConstraintSet c (u k) ⊆ activeConstraintSet c (run.x k + run.s k))
    (htrial : ∀ k, IsApproxGeneralizedCauchyPoint Q C f (run.model k) (run.x k) (run.Δ k) (u k))
    (hcmp : ∀ k, run.model k (run.x k + run.s k) ≤ run.model k (u k))
    {β B : ℝ} (hβ : 0 < β)
    (hTaylorC : ∀ k, run.model k (u k) -
      (run.model k (run.x k) + ⟪gradient f (run.x k), u k - run.x k⟫) ≤
      β * ‖u k - run.x k‖ ^ 2 / 2)
    (hTaylor : ∀ k, |run.model k (run.x k + run.s k) - run.model k (run.x k) -
      ⟪gradient f (run.x k), run.s k⟫| ≤ β * run.Δ k ^ 2)
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (herr : ∀ k, |f (run.x k + run.s k) - run.model k (run.x k + run.s k)| ≤ B * run.Δ k ^ 2) :
    ∃ A : Set ι, (∀ z ∈ S, activeConstraintSet c z = A) ∧
      ∀ᶠ k in atTop, activeConstraintSet c (run.x k) = A ∧ activeConstraintSet c (u k) = A := by
  have hgrad (g : E → ℝ) (h : ContDiff ℝ 1 g) : Continuous (gradient g) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp (h.continuous_fderiv one_ne_zero)
  have hder (i : ι) (y : E) : HasStrictFDerivAt (c i) (fderiv ℝ (c i) y) y :=
    (hc i).contDiffAt.hasStrictFDerivAt one_ne_zero
  have hnormal (y : E) (hy : y ∈ C) (i : ι) (hi : i ∈ activeConstraintSet c y) :
      -gradient (c i) y ∈ normalDirections C y := by
    change c i y = 0 at hi
    apply mem_normalDirections.mpr
    intro w hw
    rw [inner_neg_left, neg_nonpos]
    have hm : IsMinOn (c i) C y := by
      apply isMinOn_iff.mpr
      intro v hv
      rw [hset] at hv
      simpa only [hi] using (show ∀ j, 0 ≤ c j v from hv) i
    have ht := sub_mem_posTangentConeAt_of_segment_subset (hC.2.2.segment_subset hy hw)
    have hd := hm.isLocalMinOn.hasFDerivWithinAt_nonneg
      (hder i y).hasFDerivAt.hasFDerivWithinAt ht
    rwa [← toDual_gradient, InnerProductSpace.toDual_apply_apply] at hd
  have huC (k : ℕ) : u k ∈ C := by
    obtain ⟨t, _, he, _⟩ := htrial k
    rw [he]
    exact projectedRay_mem hC.1 hC.2.1 hC.2.2 (run.x k) (-gradient f (run.x k)) t
  have hQ := eventually_activeLinearizedConeMatches_of_compact hset
    (fun i ↦ (hc i).continuous) (fun i ↦ hgrad _ (hc i)) hder hK hxK
    (fun z j hj hz ↦ (hlim z).mpr ⟨j, hj, hz⟩) hind hu' (.of_forall huC)
  exact theorem_12_3_8_of_compact_run_of_Cauchy_displacements_tendsto_zero run Q
    hC hset (fun i ↦ (hc i).continuous) (fun i ↦ hgrad _ (hc i)) (hgrad _ hf)
    hind hstat hnormal hS hK hxK hlim hxs hu' hxC hstep hfeas hface hQ
    htrial hcmp hβ hTaylorC hTaylor hval herr

open Optimization Chapter06 in
/-- **Theorem 12.3.8** of [conn2000trust], corrected, with vanishing trial displacements. Let $E$,
$C$, the $c_i$, $f$, the run, the points $u_k$, the sets $S$ and $K$ and the constants
$\beta > 0$ and $B$ satisfy the hypotheses of
`ConnGouldToint.Chapter12.theorem_12_3_8_of_compact_run_of_Cauchy_displacements_tendsto_zero`,
with two changes: the steps satisfy $s_k \to 0$ in place of
$\operatorname{dist}(x_{k+1}, x_k) \to 0$, and the tangent qualification holds at $u_k$ for
every $k$. Then there is $\mathcal{A}$ with $\mathcal{A}(z) = \mathcal{A}$ for all $z \in S$,
and eventually $\mathcal{A}(x_k) = \mathcal{A}$ and $\mathcal{A}(u_k) = \mathcal{A}$.

**Correction.** This version of the printed theorem, which fails in general, adds the vanishing
trial displacements $s_k \to 0$ and $u_k - x_k \to 0$.

The radius need only shrink on misidentified trials, and the tangent-gradient gap shows that it
does.

**Correction.** The source claims unconditional eventual identification under its standing
hypotheses. These variants add vanishing Cauchy and accepted-iterate displacements, vanishing trial
displacements with Cauchy control, vanishing radii, or convergent runs with bounded positive
projected trial times and the specified normal and face conditions.
-/
theorem theorem_12_3_8_of_compact_run_of_trial_displacements_tendsto_zero
    [Fintype ι] [CompleteSpace E] [FiniteDimensional ℝ E]
    {C : Set E} {c : ι → E → ℝ} {f : E → ℝ} {P : BTRParams}
    {sufficient : ℕ → (E → ℝ) → E → E → Prop}
    (run : BTRRun f P sufficient) (Q : GeneralizedCauchyParams) {u : ℕ → E} {S K : Set E}
    (hC : Chapter03.AC2 C) (hset : Chapter03.AC7 C c)
    (hc : ∀ i, Continuous (c i)) (hn : ∀ i, Continuous (gradient (c i)))
    (hg : Continuous (gradient f))
    (hind : ∀ z ∈ S, LinearIndependent ℝ (fun i : activeConstraintSet c z ↦ gradient (c i) z))
    (hstat : ∀ z ∈ S, HasStrictActiveMultipliers c (fun i ↦ gradient (c i)) (gradient f) z)
    (hnormal : ∀ y ∈ C, ∀ i ∈ activeConstraintSet c y,
      -gradient (c i) y ∈ normalDirections C y)
    (hS : IsCompact S) (hK : IsCompact K) (hxK : ∀ k, run.x k ∈ K)
    (hlim : ∀ z, z ∈ S ↔ ∃ j : ℕ → ℕ, StrictMono j ∧ Tendsto (run.x ∘ j) atTop (𝓝 z))
    (hsn : Tendsto run.s atTop (𝓝 0))
    (hu' : Tendsto (fun k ↦ u k - run.x k) atTop (𝓝 0))
    (hxC : ∀ k, run.x k ∈ C) (hstep : ∀ k, ‖run.s k‖ ≤ run.Δ k)
    (hfeas : ∀ k, run.x k + run.s k ∈ C)
    (hface : ∀ k, activeConstraintSet c (u k) ⊆ activeConstraintSet c (run.x k + run.s k))
    (hQ : ∀ k, Chapter03.ActiveLinearizedConeMatches C c (u k))
    (htrial : ∀ k, IsApproxGeneralizedCauchyPoint Q C f (run.model k) (run.x k) (run.Δ k) (u k))
    (hcmp : ∀ k, run.model k (run.x k + run.s k) ≤ run.model k (u k))
    {β B : ℝ} (hβ : 0 < β)
    (hTaylorC : ∀ k, run.model k (u k) -
      (run.model k (run.x k) + ⟪gradient f (run.x k), u k - run.x k⟫) ≤
      β * ‖u k - run.x k‖ ^ 2 / 2)
    (hTaylor : ∀ k, |run.model k (run.x k + run.s k) - run.model k (run.x k) -
      ⟪gradient f (run.x k), run.s k⟫| ≤ β * run.Δ k ^ 2)
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (herr : ∀ k, |f (run.x k + run.s k) - run.model k (run.x k + run.s k)| ≤ B * run.Δ k ^ 2) :
    ∃ A : Set ι, (∀ z ∈ S, activeConstraintSet c z = A) ∧
      ∀ᶠ k in atTop, activeConstraintSet c (run.x k) = A ∧ activeConstraintSet c (u k) = A := by
  have hsucc_eq (k : ℕ) (hk : k ∈ run.successful) :
      run.x (k + 1) = run.x k + run.s k := by
    rw [run.iterate_update, acceptStep_of_le hk]
  have hxs : Tendsto (fun k ↦ dist (run.x (k + 1)) (run.x k)) atTop (𝓝 0) := by
    refine squeeze_zero' (g := fun k ↦ ‖run.s k‖) (.of_forall fun _ ↦ dist_nonneg) ?_ ?_
    · apply Eventually.of_forall
      intro k
      by_cases hk : k ∈ run.successful
      · rw [hsucc_eq k hk, dist_eq_norm, add_sub_cancel_left]
      · rw [run.iterate_eq_of_unsuccessful hk, dist_self]
        exact norm_nonneg _
    · simpa only [norm_zero] using hsn.norm
  exact theorem_12_3_8_of_compact_run_of_Cauchy_displacements_tendsto_zero run Q
    hC hset hc hn hg hind hstat hnormal hS hK hxK hlim hxs hu'
    hxC hstep hfeas hface (.of_forall hQ) htrial hcmp hβ hTaylorC hTaylor hval herr

open Optimization Chapter06 in
/-- **Theorem 12.3.8** of [conn2000trust], corrected, for compact runs with vanishing radii. Let
$E$, $C$, the $c_i$, $f$, the run, the points $u_k$, the sets $S$ and $K$ and the constants
$\beta > 0$ and $B$ satisfy the hypotheses of
`ConnGouldToint.Chapter12.theorem_12_3_8_of_compact_run_of_Cauchy_displacements_tendsto_zero`,
with these changes: the radii satisfy $\Delta_k \to 0$ in place of the conditions
$\operatorname{dist}(x_{k+1}, x_k) \to 0$ and $u_k - x_k \to 0$, and the tangent qualification
holds at $u_k$ for every $k$. Then there is $\mathcal{A}$ with $\mathcal{A}(z) = \mathcal{A}$
for all $z \in S$, and eventually $\mathcal{A}(x_k) = \mathcal{A}$ and
$\mathcal{A}(u_k) = \mathcal{A}$.

**Correction.** This version of the printed theorem, which fails in general, adds the vanishing
radii $\Delta_k \to 0$.

Compactness and strict complementarity give a uniform model decrease on misidentified trials.

**Correction.** The source claims unconditional eventual identification under its standing
hypotheses. These variants add vanishing Cauchy and accepted-iterate displacements, vanishing trial
displacements with Cauchy control, vanishing radii, or convergent runs with bounded positive
projected trial times and the specified normal and face conditions.
-/
theorem theorem_12_3_8_of_compact_run_of_radius_tendsto_zero
    [Fintype ι] [CompleteSpace E] [FiniteDimensional ℝ E]
    {C : Set E} {c : ι → E → ℝ} {f : E → ℝ} {P : BTRParams}
    {sufficient : ℕ → (E → ℝ) → E → E → Prop}
    (run : BTRRun f P sufficient) (Q : GeneralizedCauchyParams) {u : ℕ → E} {S K : Set E}
    (hC : Chapter03.AC2 C) (hset : Chapter03.AC7 C c)
    (hc : ∀ i, Continuous (c i)) (hn : ∀ i, Continuous (gradient (c i)))
    (hg : Continuous (gradient f))
    (hind : ∀ z ∈ S, LinearIndependent ℝ (fun i : activeConstraintSet c z ↦ gradient (c i) z))
    (hstat : ∀ z ∈ S, HasStrictActiveMultipliers c (fun i ↦ gradient (c i)) (gradient f) z)
    (hnormal : ∀ y ∈ C, ∀ i ∈ activeConstraintSet c y,
      -gradient (c i) y ∈ normalDirections C y)
    (hS : IsCompact S) (hK : IsCompact K) (hxK : ∀ k, run.x k ∈ K)
    (hlim : ∀ z, z ∈ S ↔ ∃ j : ℕ → ℕ, StrictMono j ∧ Tendsto (run.x ∘ j) atTop (𝓝 z))
    (hΔ : Tendsto run.Δ atTop (𝓝 0))
    (hxC : ∀ k, run.x k ∈ C) (hstep : ∀ k, ‖run.s k‖ ≤ run.Δ k)
    (hfeas : ∀ k, run.x k + run.s k ∈ C)
    (hface : ∀ k, activeConstraintSet c (u k) ⊆ activeConstraintSet c (run.x k + run.s k))
    (hQ : ∀ k, Chapter03.ActiveLinearizedConeMatches C c (u k))
    (htrial : ∀ k, IsApproxGeneralizedCauchyPoint Q C f (run.model k) (run.x k) (run.Δ k) (u k))
    (hcmp : ∀ k, run.model k (run.x k + run.s k) ≤ run.model k (u k))
    {β B : ℝ} (hβ : 0 < β)
    (hTaylorC : ∀ k, run.model k (u k) -
      (run.model k (run.x k) + ⟪gradient f (run.x k), u k - run.x k⟫) ≤
      β * ‖u k - run.x k‖ ^ 2 / 2)
    (hTaylor : ∀ k, |run.model k (run.x k + run.s k) - run.model k (run.x k) -
      ⟪gradient f (run.x k), run.s k⟫| ≤ β * run.Δ k ^ 2)
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (herr : ∀ k, |f (run.x k + run.s k) - run.model k (run.x k + run.s k)| ≤ B * run.Δ k ^ 2) :
    ∃ A : Set ι, (∀ z ∈ S, activeConstraintSet c z = A) ∧
      ∀ᶠ k in atTop, activeConstraintSet c (run.x k) = A ∧ activeConstraintSet c (u k) = A := by
  have hsn : Tendsto run.s atTop (𝓝 0) := squeeze_zero_norm hstep hΔ
  have hu' : Tendsto (fun k ↦ u k - run.x k) atTop (𝓝 0) :=
    squeeze_zero_norm (fun k ↦ by obtain ⟨_, _, _, h, _⟩ := htrial k; exact h) hΔ
  exact theorem_12_3_8_of_compact_run_of_trial_displacements_tendsto_zero run Q
    hC hset hc hn hg hind hstat hnormal hS hK hxK hlim hsn hu'
    hxC hstep hfeas hface hQ htrial hcmp hβ hTaylorC hTaylor hval herr

open Optimization Chapter06 in
/-- **Theorem 12.3.8** of [conn2000trust], corrected, for convergent runs with vanishing radii. Let
$E$ be a finite-dimensional real inner product space, let $C$ satisfy AC.2 and AC.7, let $c_i$,
$\nabla c_i$ and $\nabla f$ be continuous, and let $-\nabla c_i(y) \in N(y)$ for every $y \in C$
and $i \in \mathcal{A}(y)$. Consider a run of the basic trust-region algorithm for $f$,
parameters of the generalized Cauchy point, and points $u_k$, with $x_k \to z$ and
$\Delta_k \to 0$. At $z$ let the active gradients be linearly independent and let $\nabla f$
have strictly positive active multipliers. Let $\beta > 0$ and $B$ be constants, and suppose
that for every $k$:

* the tangent qualification holds at $u_k$;
* $x_k \in C$, $\|s_k\| \le \Delta_k$, $x_k + s_k \in C$, $u_k$ is an approximate generalized
  Cauchy point for $C$, $f$, $m_k$, $x_k$ and $\Delta_k$, $m_k(x_k + s_k) \le m_k(u_k)$, and
  $\mathcal{A}(u_k) \subseteq \mathcal{A}(x_k + s_k)$ (AA.5);
* $f(x_k) = m_k(x_k)$, $|f(x_k + s_k) - m_k(x_k + s_k)| \le B \Delta_k^2$, and
$$m_k(u_k) - m_k(x_k) - \langle \nabla f(x_k), u_k - x_k \rangle \le \tfrac{\beta}{2} \|u_k -
  x_k\|^2, \qquad |m_k(x_k + s_k) - m_k(x_k) - \langle \nabla f(x_k), s_k \rangle| \le \beta
  \Delta_k^2.$$

Then eventually $\mathcal{A}(x_k) = \mathcal{A}(z)$ and $\mathcal{A}(u_k) = \mathcal{A}(z)$.

**Correction.** This version of the printed theorem, which fails in general, assumes a
convergent run with vanishing radii.

The argument uses the tangent gradients at the trials, and it keeps all constraints active at
the Cauchy point active at the step, as AA.5 requires.

**Correction.** The source claims unconditional eventual identification under its standing
hypotheses. These variants add vanishing Cauchy and accepted-iterate displacements, vanishing trial
displacements with Cauchy control, vanishing radii, or convergent runs with bounded positive
projected trial times and the specified normal and face conditions.
-/
theorem theorem_12_3_8_of_convergent_run_of_radius_tendsto_zero
    [Fintype ι] [CompleteSpace E] [FiniteDimensional ℝ E]
    {C : Set E} {c : ι → E → ℝ} {f : E → ℝ} {P : BTRParams}
    {sufficient : ℕ → (E → ℝ) → E → E → Prop}
    (run : BTRRun f P sufficient) (Q : GeneralizedCauchyParams) {u : ℕ → E} {z : E}
    (hC : Chapter03.AC2 C) (hset : Chapter03.AC7 C c)
    (hc : ∀ i, Continuous (c i)) (hn : ∀ i, Continuous (gradient (c i)))
    (hg : Continuous (gradient f))
    (hind : LinearIndependent ℝ (fun i : activeConstraintSet c z ↦ gradient (c i) z))
    (hstat : HasStrictActiveMultipliers c (fun i ↦ gradient (c i)) (gradient f) z)
    (hnormal : ∀ y ∈ C, ∀ i ∈ activeConstraintSet c y,
      -gradient (c i) y ∈ normalDirections C y)
    (hx : Tendsto run.x atTop (𝓝 z)) (hΔ : Tendsto run.Δ atTop (𝓝 0))
    (hxC : ∀ k, run.x k ∈ C) (hstep : ∀ k, ‖run.s k‖ ≤ run.Δ k)
    (hfeas : ∀ k, run.x k + run.s k ∈ C)
    (hface : ∀ k, activeConstraintSet c (u k) ⊆ activeConstraintSet c (run.x k + run.s k))
    (hQ : ∀ k, Chapter03.ActiveLinearizedConeMatches C c (u k))
    (htrial : ∀ k, IsApproxGeneralizedCauchyPoint Q C f (run.model k) (run.x k) (run.Δ k) (u k))
    (hcmp : ∀ k, run.model k (run.x k + run.s k) ≤ run.model k (u k))
    {β B : ℝ} (hβ : 0 < β)
    (hTaylorC : ∀ k, run.model k (u k) -
      (run.model k (run.x k) + ⟪gradient f (run.x k), u k - run.x k⟫) ≤
      β * ‖u k - run.x k‖ ^ 2 / 2)
    (hTaylor : ∀ k, |run.model k (run.x k + run.s k) - run.model k (run.x k) -
      ⟪gradient f (run.x k), run.s k⟫| ≤ β * run.Δ k ^ 2)
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (herr : ∀ k, |f (run.x k + run.s k) - run.model k (run.x k + run.s k)| ≤ B * run.Δ k ^ 2) :
    ∀ᶠ k in atTop, activeConstraintSet c (run.x k) = activeConstraintSet c z ∧
      activeConstraintSet c (u k) = activeConstraintSet c z := by
  have hlim (w : E) : w ∈ ({z} : Set E) ↔
      ∃ j : ℕ → ℕ, StrictMono j ∧ Tendsto (run.x ∘ j) atTop (𝓝 w) := by
    constructor
    · rintro rfl
      exact ⟨id, strictMono_id, hx⟩
    · rintro ⟨j, hj, hjw⟩
      exact tendsto_nhds_unique hjw (hx.comp hj.tendsto_atTop)
  obtain ⟨A, hA, hfinal⟩ := theorem_12_3_8_of_compact_run_of_radius_tendsto_zero run Q
    hC hset hc hn hg
    (by rintro w rfl; exact hind)
    (by rintro w rfl; exact hstat) hnormal
    (isCompact_singleton (x := z)) hx.isCompact_insert_range
    (fun k ↦ Set.mem_insert_of_mem _ (Set.mem_range_self k)) hlim
    hΔ hxC hstep hfeas hface hQ htrial hcmp hβ hTaylorC hTaylor hval herr
  exact (hA z (Set.mem_singleton z)).symm ▸ hfinal

open Optimization Chapter06 in
/-- **Theorem 12.3.8** of [conn2000trust], for convergent runs with bounded positive trial times.
Let $E$ be a finite-dimensional real inner product space, let $C$ satisfy AC.2 and AC.7, and let
$c_i$, $\nabla c_i$ and $\nabla f$ be continuous. Let $z \in C$ with $-\nabla f(z) \in N(z)$,
let the active gradients at $z$ be linearly independent, and let $\nabla f$ have strictly
positive active multipliers at $z$. Consider a run of the basic trust-region algorithm for $f$
with $x_k \to z$, let $0 < a$, let eventually $a \le t_k \le b$, and put
$p_k = P_C[x_k - t_k \nabla f(x_k)]$. Suppose that eventually the tangent qualification holds at
$p_k$ and $\mathcal{A}(p_k) \subseteq \mathcal{A}(x_k + s_k)$. Then eventually
$\mathcal{A}(x_k) = \mathcal{A}(z)$ and $\mathcal{A}(p_k) = \mathcal{A}(z)$.

**Correction.** This version of the printed theorem, which fails in general, assumes that the
trial times stay in a fixed interval $[a, b]$ with $a > 0$.

The radii need not tend to zero, and no estimate of the model curvature is needed.

**Correction.** The source claims unconditional eventual identification under its standing
hypotheses. These variants add vanishing Cauchy and accepted-iterate displacements, vanishing trial
displacements with Cauchy control, vanishing radii, or convergent runs with bounded positive
projected trial times and the specified normal and face conditions.
-/
theorem theorem_12_3_8_of_bounded_trial_times
    [Fintype ι] [CompleteSpace E] [FiniteDimensional ℝ E]
    {C : Set E} {c : ι → E → ℝ} {f : E → ℝ} {P : BTRParams}
    {sufficient : ℕ → (E → ℝ) → E → E → Prop}
    (run : BTRRun f P sufficient) {t : ℕ → ℝ} {z : E} {a b : ℝ}
    (hC : Chapter03.AC2 C) (hset : Chapter03.AC7 C c) (hz : z ∈ C)
    (hstat : -gradient f z ∈ normalDirections C z)
    (hc : ∀ i, Continuous (c i)) (hn : ∀ i, Continuous (gradient (c i)))
    (hg : Continuous (gradient f))
    (hind : LinearIndependent ℝ (fun i : activeConstraintSet c z ↦ gradient (c i) z))
    (hmul : HasStrictActiveMultipliers c (fun i ↦ gradient (c i)) (gradient f) z)
    (hx : Tendsto run.x atTop (𝓝 z)) (ha : 0 < a)
    (ht : ∀ᶠ k in atTop, a ≤ t k ∧ t k ≤ b)
    (hQ : ∀ᶠ k in atTop, Chapter03.ActiveLinearizedConeMatches C c
      (projectedGradientPath C f (run.x k) (t k)))
    (hface : ∀ᶠ k in atTop, activeConstraintSet c (projectedGradientPath C f (run.x k) (t k)) ⊆
      activeConstraintSet c (run.x k + run.s k)) :
    ∀ᶠ k in atTop, activeConstraintSet c (run.x k) = activeConstraintSet c z ∧
      activeConstraintSet c (projectedGradientPath C f (run.x k) (t k)) =
        activeConstraintSet c z := by
  have htrial := eventually_activeConstraintSet_eq_projectedGradientPath
    hC hset hz hstat hc hn hg hind hmul hx ha ht hQ
  have hsuc : Tendsto (fun k : ℕ ↦ k + 1) atTop atTop :=
    tendsto_atTop_mono (fun k ↦ Nat.le_succ k) tendsto_id
  have hsub := eventually_activeConstraintSet_subset_of_tendsto hc (hx.comp hsuc)
  have hacc : ∀ᶠ k in atTop, k ∈ run.successful →
      activeConstraintSet c (run.x (k + 1)) = activeConstraintSet c z := by
    filter_upwards [htrial, hface, hsub] with k htk hfk hsk
    intro hsucc
    have hupdate : run.x (k + 1) = run.x k + run.s k := by
      rw [run.iterate_update, acceptStep_of_le hsucc]
    exact Set.Subset.antisymm hsk (by rw [hupdate, ← htk]; exact hfk)
  have hbase : ∀ᶠ k in atTop, activeConstraintSet c (run.x k) = activeConstraintSet c z := by
    by_cases hf : ∃ᶠ k in atTop, k ∈ run.successful
    · obtain ⟨N, hN⟩ := eventually_atTop.mp hacc
      obtain ⟨j, hj, hjs⟩ := frequently_atTop.mp hf N
      refine eventually_atTop.mpr ⟨j + 1, fun k hk ↦ ?_⟩
      induction k, hk using Nat.le_induction with
      | base => exact hN j hj hjs
      | succ k hk ih =>
        by_cases hks : k ∈ run.successful
        · exact hN k (hj.trans ((Nat.le_succ j).trans hk)) hks
        · rwa [run.iterate_eq_of_unsuccessful hks]
    · exact (eventually_iterate_eq_limit_of_finitely_successful run hx hf).mono
        fun k hk ↦ congrArg (activeConstraintSet c) hk
  exact hbase.and htrial

open Optimization in
/-- **Theorem 12.3.4** of [conn2000trust], counterexample to the pointwise comparison in the proof.
Let $0 < x \le 1$, take $C = [0, \infty)$ with the single constraint $c(y) = y$, and take $f$
and the model $m$ equal to the identity. Then, for any parameters of the generalized Cauchy
point,

* $x/2$ is an approximate generalized Cauchy point for $C$, $f$, $m$, $x$ and the radius $x/2$;
* the active set at $x/2$ differs from the active set at the limit $0$;
* the capped criticality measure (12.2.15) is $\pi_C(x) = x$.

So the Cauchy point at the radius boundary misses the active constraint of the limit, while the
base point and the criticality measure both tend to zero as $x \to 0$. Missing an active
constraint at a generalized Cauchy point therefore does not bound the criticality measure of the
full feasible set away from zero. The example concerns the local comparison only, without a run.

**Correction.** The lower bound uses a point feasible for the relaxed domain and shifts the
displacement from the reference point to the base. The half-line counterexample shows that the local
trial assumptions alone do not support the corresponding bound for the full feasible domain.
-/
theorem missing_active_local_criticality_counterexample
    (P : GeneralizedCauchyParams) {x : ℝ} (hx : 0 < x) (hx₁ : x ≤ 1) :
    IsApproxGeneralizedCauchyPoint P (Set.Ici (0 : ℝ)) id id x (x / 2) (x / 2) ∧
      activeConstraintSet (fun _ : Unit ↦ id) 0 ≠
        activeConstraintSet (fun _ : Unit ↦ id) (x / 2) ∧
      cappedCriticality (Set.Ici (0 : ℝ)) id x = x := by
  let C := Set.Ici (0 : ℝ)
  have hg : gradient (id : ℝ → ℝ) x = 1 := by rw [gradient_eq_deriv', deriv_id]
  have hhalf : 0 < x / 2 := half_pos hx
  have hdiff : ‖x / 2 - x‖ = x / 2 := by
    rw [Real.norm_eq_abs, abs_of_neg (by linarith : x / 2 - x < 0)]
    ring
  have hpath : projectedGradientPath C id x (x / 2) = x / 2 := by
    unfold projectedGradientPath
    change bestApprox C (x + (x / 2) • (-gradient (id : ℝ → ℝ) x)) = x / 2
    rw [hg, smul_eq_mul, show x + x / 2 * (-1) = x / 2 by ring]
    exact (bestApprox_eq_iff ⟨0, by simp⟩ isClosed_Ici (convex_Ici _)).mpr
      ⟨hhalf.le, by simp⟩
  refine ⟨⟨x / 2, hhalf, hpath.symm, hdiff.le, ?_, Or.inl ?_⟩, ?_, ?_⟩
  · simp only [id_eq, hg, Real.inner_apply, one_mul]
    have h := mul_nonneg (sub_nonneg.mpr (P.slope_order.trans P.lower_lt_one).le) hhalf.le
    nlinarith only [h]
  · rw [hdiff]
    exact mul_le_of_le_one_left hhalf.le P.fraction_lt_one.le
  · intro he
    have h0 : () ∈ activeConstraintSet (fun _ : Unit ↦ id) (0 : ℝ) := rfl
    have hn := he ▸ h0
    exact hhalf.ne' hn
  · have hχ : criticality C id x 1 = x := by
      unfold criticality
      rw [hg]
      apply le_antisymm
      · apply linearDecrease_le (show x ∈ C from hx.le) zero_le_one
        intro d hd _
        change 0 ≤ x + d at hd
        simp only [Real.inner_apply]
        linarith only [hd]
      · have hnorm : ‖-x‖ ≤ (1 : ℝ) := by
          simpa only [norm_neg, Real.norm_eq_abs, abs_of_pos hx] using hx₁
        have h := inner_le_linearDecrease (v := (-1 : ℝ))
          (show x + -x ∈ C by simp [C]) hnorm
        simpa only [Real.inner_apply, neg_mul_neg, one_mul, neg_mul, mul_neg, mul_one,
          neg_neg] using h
    rw [cappedCriticality, hχ, min_eq_right hx₁]

open ConnGouldToint.Chapter06 in
/-- **Lemma 12.3.5** of [conn2000trust]. Let $E$ be a real Hilbert space, let $0 < \beta \le B$,
$\Delta > 0$, $0 < \kappa < 1$, and let $\pi = \pi_C(x) > 0$ be the capped criticality measure
(12.2.15). Suppose that $f(x) = m(x)$, that the model decrease condition AA.1b holds,
$$\kappa\, \pi \min\{\pi / \beta, \Delta\} \le m(x) - m(x + s),$$
that $|f(x + s) - m(x + s)| \le B \Delta^2$, and that
$$\Delta \le \frac{\kappa\, \pi\, (1 - \eta_2)}{B}.$$
If $\Delta'$ is obtained from $\Delta$ by the radius update (6.1.5) with the ratio $\rho$ of the
step $s$, then $\rho \ge \eta_2$ and $\Delta \le \Delta'$.

**Reading.** The single-iteration result takes the needed Taylor error bound and AA.1b inequality
directly and specifies a positive current criticality and curvature bound. It uses the radius update
as a hypothesis.
-/
theorem lemma_12_3_5 [CompleteSpace E] {P : BTRParams} {C : Set E}
    {f m : E → ℝ} {x s : E} {β Δ Δ' κ B : ℝ}
    (hβ : 0 < β) (hβB : β ≤ B) (hΔ : 0 < Δ)
    (hπ : 0 < cappedCriticality C f x) (hκ : 0 < κ) (hκ' : κ < 1)
    (hval : f x = m x)
    (hdec : κ * cappedCriticality C f x * min (cappedCriticality C f x / β) Δ ≤
      m x - m (x + s))
    (herr : |f (x + s) - m (x + s)| ≤ B * Δ ^ 2)
    (hsmall : Δ ≤ κ * cappedCriticality C f x * (1 - P.η₂) / B)
    (hupdate : BTRRadiusUpdate P (btrRatio f m x s) Δ Δ') :
    P.η₂ ≤ btrRatio f m x s ∧ Δ ≤ Δ' := by
  have hsuccess := btrRatio_ge_eta₂_of_small_radius_of_decrease
    hβ hβB hΔ hπ hκ hκ' hval hdec herr hsmall
  exact ⟨hsuccess, hupdate.very_successful hsuccess⟩

open Optimization ConvexAnalysis in
/-- Lemma 12.3.6 of [conn2000trust] when the points $u_k$ only eventually have the active set
$\mathcal{A}$: the projections $P_{T(u_k)}[-g(x_k)]$ tend to zero. -/
private theorem projectedGradient_tendsto_zero_of_eventually_active [Fintype ι] [CompleteSpace E]
    {C K S : Set E}
    {c : ι → E → ℝ} {n : ι → E → E} {g : E → E}
    {x u : ℕ → E} {A : Set ι}
    (hK : IsCompact K) (hx : ∀ k, x k ∈ K)
    (hlim : ∀ z (j : ℕ → ℕ), StrictMono j → Tendsto (x ∘ j) atTop (𝓝 z) → z ∈ S)
    (hclose : Tendsto (fun k ↦ u k - x k) atTop (𝓝 0))
    (hu : ∀ k, u k ∈ C) (hAu : ∀ᶠ k in atTop, activeConstraintSet c (u k) = A)
    (hAS : ∀ z ∈ S, activeConstraintSet c z = A)
    (hstat : ∀ z ∈ S, HasStrictActiveMultipliers c n g z)
    (hg : Continuous g) (hn : ∀ i, Continuous (n i))
    (hnormal : ∀ y ∈ C, ∀ i ∈ activeConstraintSet c y, -n i y ∈ normalDirections C y) :
    Tendsto (fun k ↦ bestApprox (tangentDirections C (u k)) (-g (x k))) atTop (𝓝 0) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  by_contra! hbad
  obtain ⟨j, hj, hjbad⟩ := extraction_of_frequently_atTop hbad
  obtain ⟨z, _, i, hi, hzi⟩ := hK.isSeqCompact (fun k ↦ hx (j k))
  let q := j ∘ i
  have hq : StrictMono q := hj.comp hi
  have hxq : Tendsto (x ∘ q) atTop (𝓝 z) := hzi
  have hz := hlim z q hq hxq
  obtain ⟨μ, hμ, hpos, hzero⟩ := hstat z hz
  have huq : Tendsto (u ∘ q) atTop (𝓝 z) := by
    change Tendsto (fun k ↦ u (q k)) atTop (𝓝 z)
    simpa only [Function.comp_apply, sub_add_cancel, zero_add] using
      (hclose.comp hq.tendsto_atTop).add hxq
  let w (y : E) := ∑ a, μ a • (-n a y)
  have hw : Continuous w := continuous_finsetSum _ fun a _ ↦
    continuous_const.smul (hn a).neg
  have hwz : w z = -g z := by
    simp only [w, smul_neg, Finset.sum_neg_distrib, ← hμ]
  have hwmem (k : ℕ) (hk : activeConstraintSet c (u (q k)) = A) :
      w (u (q k)) ∈ normalDirections C (u (q k)) := by
    apply mem_normalDirections.mpr
    intro y hy
    change ⟪∑ a, μ a • (-n a (u (q k))), y - u (q k)⟫ ≤ 0
    rw [sum_inner]
    apply Finset.sum_nonpos
    intro a _
    rw [real_inner_smul_left]
    by_cases ha : a ∈ activeConstraintSet c z
    · have hau : a ∈ activeConstraintSet c (u (q k)) := by
        rwa [hk, ← hAS z hz]
      exact mul_nonpos_of_nonneg_of_nonpos (hpos a ha).le
        (mem_normalDirections.mp (hnormal _ (hu _) a hau) y hy)
    · rw [hzero a ha, zero_mul]
  have hbound (k : ℕ) (hk : activeConstraintSet c (u (q k)) = A) :
      ‖bestApprox (tangentDirections C (u (q k))) (-g (x (q k)))‖ ≤
        ‖-g (x (q k)) - w (u (q k))‖ := by
    let T := tangentDirections C (u (q k))
    have hTzero : (0 : E) ∈ T := by simp [T, tangentDirections, mem_polarCone]
    have hTclosed : IsClosed T := isClosed_polarCone
    have hTconvex : Convex ℝ T := convex_polarCone _ _
    have hproj : bestApprox T (w (u (q k))) = 0 := by
      apply (bestApprox_eq_iff ⟨0, hTzero⟩ hTclosed hTconvex).2
      refine ⟨hTzero, fun y hy ↦ ?_⟩
      simpa only [sub_zero, innerₗ_apply_apply] using (mem_polarCone.mp hy) _ (hwmem k hk)
    simpa only [hproj, sub_zero] using
      norm_bestApprox_sub_bestApprox_le ⟨0, hTzero⟩ hTclosed hTconvex
        (-g (x (q k))) (w (u (q k)))
  have hgq : Tendsto (fun k ↦ g (x (q k))) atTop (𝓝 (g z)) :=
    hg.continuousAt.tendsto.comp hxq
  have hwq : Tendsto (fun k ↦ w (u (q k))) atTop (𝓝 (w z)) :=
    hw.continuousAt.tendsto.comp huq
  have ht : Tendsto (fun k ↦ ‖-g (x (q k)) - w (u (q k))‖) atTop (𝓝 0) := by
    simpa only [hwz, sub_self, norm_zero] using (hgq.neg.sub hwq).norm
  have he := ht.eventually (gt_mem_nhds hε)
  obtain ⟨k, hk, hak⟩ := (he.and (hq.tendsto_atTop.eventually hAu)).exists
  exact (not_lt_of_ge (hjbad (i k))) (by
    rw [dist_zero_right]
    exact (hbound k hak).trans_lt hk)

open Optimization ConvexAnalysis in
/-- **Lemma 12.3.6** of [conn2000trust]. Let $E$ be a real Hilbert space, let $K$ be compact,
$x_k \in K$, and let every limit of a subsequence of $(x_k)$ lie in $S$. Let $u_k \in C$ with
$u_k - x_k \to 0$ and $\mathcal{A}(u_k) = \mathcal{A}$ for all $k$, and let
$\mathcal{A}(z) = \mathcal{A}$ and $g$ have strictly positive active multipliers at every
$z \in S$. Let $g$ and the $n_i$ be continuous, and let $-n_i(y) \in N(y)$ for every $y \in C$
and $i \in \mathcal{A}(y)$. Then
$$P_{T(u_k)}[-g(x_k)] \to 0.$$

The sequence is the subsequence of the source, already reindexed. At each $u_k$ the outward
normals $-n_i(u_k)$, $i \in \mathcal{A}$, are supporting directions of $C$, and nearby
combinations of them approximate $-g(x_k)$.

**Reading.** The lemma takes a full sequence satisfying the stated closeness and active-set
hypotheses, so a qualifying subsequence can be reindexed. The corollary assumes eventual active-set
identification rather than deriving it from the uncorrected theorem.
-/
theorem lemma_12_3_6 [Fintype ι] [CompleteSpace E] {C K S : Set E}
    {c : ι → E → ℝ} {n : ι → E → E} {g : E → E}
    {x u : ℕ → E} {A : Set ι}
    (hK : IsCompact K) (hx : ∀ k, x k ∈ K)
    (hlim : ∀ z (j : ℕ → ℕ), StrictMono j → Tendsto (x ∘ j) atTop (𝓝 z) → z ∈ S)
    (hclose : Tendsto (fun k ↦ u k - x k) atTop (𝓝 0))
    (hu : ∀ k, u k ∈ C) (hAu : ∀ k, activeConstraintSet c (u k) = A)
    (hAS : ∀ z ∈ S, activeConstraintSet c z = A)
    (hstat : ∀ z ∈ S, HasStrictActiveMultipliers c n g z)
    (hg : Continuous g) (hn : ∀ i, Continuous (n i))
    (hnormal : ∀ y ∈ C, ∀ i ∈ activeConstraintSet c y, -n i y ∈ normalDirections C y) :
    Tendsto (fun k ↦ bestApprox (tangentDirections C (u k)) (-g (x k))) atTop (𝓝 0) :=
  projectedGradient_tendsto_zero_of_eventually_active hK hx hlim hclose hu
    (Eventually.of_forall hAu) hAS hstat hg hn hnormal

open Optimization ConvexAnalysis in
/-- **Corollary 12.3.9** of [conn2000trust], under eventual identification. Let $E$ be a real
Hilbert space, let $K$ be compact, $x_k \in K \cap C$, and let every limit of a subsequence of
$(x_k)$ lie in $S$. Suppose that eventually $\mathcal{A}(x_k) = \mathcal{A}$, that
$\mathcal{A}(z) = \mathcal{A}$ and $g$ has strictly positive active multipliers at every
$z \in S$, that $g$ and the $n_i$ are continuous, and that $-n_i(y) \in N(y)$ for every
$y \in C$ and $i \in \mathcal{A}(y)$. Then
$$P_{T(x_k)}[-g(x_k)] \to 0.$$

**Correction.** The printed corollary takes the eventual identification of the active set from
Theorem 12.3.8, which fails as printed. Here the identification $\mathcal{A}(x_k) = \mathcal{A}$
is a hypothesis.

**Reading.** The lemma takes a full sequence satisfying the stated closeness and active-set
hypotheses, so a qualifying subsequence can be reindexed. The corollary assumes eventual active-set
identification rather than deriving it from the uncorrected theorem.
-/
theorem corollary_12_3_9_of_eventually_active [Fintype ι] [CompleteSpace E]
    {C K S : Set E} {c : ι → E → ℝ} {n : ι → E → E} {g : E → E}
    {x : ℕ → E} {A : Set ι}
    (hK : IsCompact K) (hx : ∀ k, x k ∈ K)
    (hlim : ∀ z (j : ℕ → ℕ), StrictMono j → Tendsto (x ∘ j) atTop (𝓝 z) → z ∈ S)
    (hfeas : ∀ k, x k ∈ C) (hA : ∀ᶠ k in atTop, activeConstraintSet c (x k) = A)
    (hAS : ∀ z ∈ S, activeConstraintSet c z = A)
    (hstat : ∀ z ∈ S, HasStrictActiveMultipliers c n g z)
    (hg : Continuous g) (hn : ∀ i, Continuous (n i))
    (hnormal : ∀ y ∈ C, ∀ i ∈ activeConstraintSet c y, -n i y ∈ normalDirections C y) :
    Tendsto (fun k ↦ bestApprox (tangentDirections C (x k)) (-g (x k))) atTop (𝓝 0) := by
  apply projectedGradient_tendsto_zero_of_eventually_active hK hx hlim _ hfeas
    hA hAS hstat hg hn hnormal
  simpa only [sub_self] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : E)) atTop (𝓝 0))

end ConnGouldToint.Chapter12

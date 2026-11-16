/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Numlib.Analysis.InnerProductSpace.Projection.ObliqueProjection
import Numlib.Analysis.Normed.Module.BestApprox
import Numlib.Projection.Optimality
import Numlib.Variational.LaxMilgram

/-!
# Galerkin and Petrov–Galerkin methods for variational problems

Let $a$ be a bounded sesquilinear form on an inner product space $V$, let $\ell$ be a bounded
functional, and let $u^*$ solve $a(u^*, v) = \ell(v)$ for all $v \in V$. The **Galerkin solution**
on a subspace $K$ is the $u_N \in K$ with $a(u_N, v) = \ell(v)$ for all $v \in K$
([han2009theoretical], (9.1.4)). In matrix form, this is a linear system in the stiffness matrix
$A_{ij} = a(\varphi_j, \varphi_i)$ of a basis $\varphi$ of $K$ ((9.1.5)). If $a$ is bounded with
constant $M$ and coercive with constant $c > 0$, **Céa's lemma** gives $\|u^* - u_N\| \le (M / c)
\inf_{v \in K} \|u^* - v\|$ (Proposition 9.1.3, inequality (9.1.11)). If $a$ is also Hermitian,
$u_N$ is the best approximation of $u^*$ from $K$ in the energy norm, and the constant improves to
$\sqrt{M / c}$. Galerkin solutions on a monotone family of subspaces with dense union converge to
$u^*$ (Corollary 9.1.4).

The **Petrov–Galerkin method** for a form on $U \times V$ takes its solution in a trial space
$K \subseteq U$ and tests with a test space $L \subseteq V$ ((9.2.5)). Under the discrete inf–sup
condition with constant $\alpha_N > 0$ and $\dim K = \dim L$, the solution exists, is unique and
satisfies Babuška's bound $\|u^* - u_N\| \le (1 + M / \alpha_N) \|u^* - w\|$ for $w \in K$ (Theorem
9.2.1), and the solutions converge (Corollary 9.2.3). The map $u \mapsto u_N$ is a bounded
idempotent operator $P_N$ with range $K$ and $\|P_N\| \le M / \alpha_N$. With Kato's identity
$\|1 - P\| = \|P\|$, this gives the Xu–Zikatanov bound $\|u^* - u_N\| \le (M / \alpha_N) \inf_{w \in
K} \|u^* - w\|$ (Remark 9.2.2). The module also proves Strang's first lemma for the generalized
Galerkin method (Theorem 9.3.1), the Aubin–Nitsche duality argument, which bounds the Galerkin error
in a norm weaker than the norm of coercivity (Theorem 10.4.3 and Corollary 10.4.4), and versions of
Céa's lemma and Strang's first lemma in a seminorm.

## Main definitions

* `IsGalerkinSolution`: the Galerkin problem on a subspace $K$.
* `IsPetrovGalerkinSolution`: the Petrov–Galerkin problem with trial space $K$ and test space $L$.
* `SesqForm.gramMatrix`: the stiffness matrix $A_{ij} = a(\varphi_j, \varphi_i)$ of a finite family
  $\varphi$.
* `IsPetrovGalerkinSolution.DiscreteInfSup`: the discrete inf–sup condition.
* `IsPetrovGalerkinSolution.projection`: the Petrov–Galerkin projector $P_N$.
* `IsGeneralizedGalerkinSolution`: the generalized Galerkin problem with an approximate form and an
  approximate functional.

## Main results

* `IsGalerkinSolution.existsUnique`: the Galerkin problem for a coercive form on a complete subspace
  has exactly one solution.
* `IsGalerkinSolution.norm_sub_le`, `IsGalerkinSolution.norm_sub_le_infDist`: Céa's lemma.
* `IsGalerkinSolution.energyNorm_sub_le`, `IsGalerkinSolution.norm_sub_le_sqrt`: for a Hermitian
  form, the Galerkin solution is optimal in the energy norm, and Céa's constant improves to
  $\sqrt{M / c}$.
* `IsGalerkinSolution.iff_mulVec`, `IsGalerkinSolution.iff_gramMatrix_mulVec`: the Galerkin problem
  is a linear system in the stiffness matrix.
* `SesqForm.gramMatrix_posDef`: the stiffness matrix of a symmetric coercive real form in a linearly
  independent family is positive definite.
* `IsGalerkinSolution.tendsto`, `IsPetrovGalerkinSolution.tendsto`: convergence for a monotone
  family of trial spaces with dense union.
* `IsPetrovGalerkinSolution.existsUnique`, `IsPetrovGalerkinSolution.norm_sub_le`: Babuška's
  theorem.
* `IsPetrovGalerkinSolution.norm_projection_le`,
  `IsPetrovGalerkinSolution.norm_sub_le_div_mul_infDist`: the bound on the Petrov–Galerkin projector
  and the Xu–Zikatanov bound.
* `strang_first`: Strang's first lemma.
* `norm_map_sq_le_of_dual`, `norm_map_le_of_dual_approx`: the Aubin–Nitsche estimate.
* `seminorm_sub_le_of_galerkin_orthogonal`, `seminorm_sub_le_of_generalizedGalerkin`: Céa's lemma
  and Strang's first lemma in a seminorm.

## Implementation notes

* `IsGalerkinSolution a ℓ K u` and `IsPetrovGalerkinSolution a ℓ K K u` are the same proposition.
  `IsGalerkinSolution.iff_isGalerkin` relates the Galerkin problem for the form to the operator
  specification `IsGalerkin` of `Numlib.Projection.Basic`, with the operator `SesqForm.toOperator a`
  and the right-hand side `SesqForm.rieszRep ℓ`.
* The exact solution $u^*$ is a hypothesis `hstar : ∀ v, a ustar v = ℓ v`, not a definition. The
  quasi-optimality bounds are stated for every $v \in K$, and also against the distance
  `Metric.infDist`.
* Several bounds assume $M \ge 0$ or $\delta \ge 0$. In degenerate cases, such as a zero trial
  space, the other hypotheses do not imply these signs, and the bounds are false without them.
  `IsPetrovGalerkinSolution.norm_sub_le` and `strang_first` give counterexamples.
* The seminorm versions need no topology, no completeness and no inner product. They are the form of
  the estimates that the $H^1$-seminorm bounds of Theorems 12.3 and 12.4 of
  [quarteroni2000numerical] use: on $H^1(a, b)$ the elliptic form is bounded and coercive for the
  seminorm $|\cdot|_{H^1}$ only on the subspace $H^1_0(a, b)$, so a hypothesis of boundedness on the
  whole space would not apply.
-/

open scoped InnerProductSpace

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- The **Galerkin problem** on a subspace $K$ ([han2009theoretical], (9.1.4)): a vector $u$ is a
Galerkin solution for the form $a$ and the functional $\ell$ if $u \in K$ and
$a(u, v) = \ell(v)$ for all $v \in K$.

The trial space and the test space are the same subspace $K$. -/
def IsGalerkinSolution (a : SesqForm 𝕜 V) (ℓ : V →L[𝕜] 𝕜) (K : Submodule 𝕜 V) (u : V) : Prop :=
  u ∈ K ∧ ∀ v ∈ K, a u v = ℓ v

/-- The **Petrov–Galerkin problem** ([han2009theoretical], (9.2.5)): for a form $a$ on $U \times V$,
a functional $\ell$ on $V$, a trial space $K \subseteq U$ and a test space $L \subseteq V$, a
vector $u$ is a Petrov–Galerkin solution if $u \in K$ and $a(u, v) = \ell(v)$ for all $v \in L$.

The trial space and the test space can differ, and they can lie in different spaces. -/
def IsPetrovGalerkinSolution {U : Type*} [NormedAddCommGroup U] [InnerProductSpace 𝕜 U]
    (a : SesqForm₂ 𝕜 U V) (ℓ : V →L[𝕜] 𝕜) (K : Submodule 𝕜 U) (L : Submodule 𝕜 V) (u : U) :
    Prop :=
  u ∈ K ∧ ∀ v ∈ L, a u v = ℓ v

/-- A vector $u$ is a Galerkin solution on $K$ if and only if it is a Petrov–Galerkin solution with
trial space $K$ and test space $K$, for $a$ as a form on $V \times V$.

So every result on the Petrov–Galerkin method applies to the Galerkin method. The two
definitions are the same proposition. -/
theorem isGalerkinSolution_iff_isPetrovGalerkinSolution (a : SesqForm 𝕜 V) (ℓ : V →L[𝕜] 𝕜)
    (K : Submodule 𝕜 V) (u : V) :
    IsGalerkinSolution a ℓ K u ↔ IsPetrovGalerkinSolution (a : SesqForm₂ 𝕜 V V) ℓ K K u :=
  Iff.rfl

/-- The restriction of a form on $U \times V$ to a pair of subspaces $K \subseteq U$ and
$L \subseteq V$. -/
private noncomputable def SesqForm₂.restrict {U : Type*} [NormedAddCommGroup U]
    [InnerProductSpace 𝕜 U] (a : SesqForm₂ 𝕜 U V) (K : Submodule 𝕜 U) (L : Submodule 𝕜 V) :
    SesqForm₂ 𝕜 K L :=
  ((a.comp K.subtypeL).flip.comp L.subtypeL).flip

/-!
### Quasi-optimality in a normed space

Céa's lemma, Babuška's lemma and the Xu–Zikatanov bound have the same form: the error of the
discrete solution is at most a constant times the distance from the exact solution to any element of
the trial space. Two consequences of this form are needed for each of them: the same bound with the
infimum over the trial space, and convergence along a monotone family of trial spaces with dense
union. They depend only on this form, so they are proved once here in a normed space.
-/

section QuasiOptimal

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Let $X$ be a normed space, let $K$ be a subspace, let $C \in \mathbb{R}$, and let $u^* \in X$
and $u \in K$. If $\|u^* - u\| \le C \|u^* - w\|$ for every $w \in K$, then
$$\|u^* - u\| \le C \operatorname{dist}(u^*, K).$$

No sign hypothesis on $C$ is needed: if $C < 0$, the test $w = u$ gives $u = u^*$. -/
theorem norm_sub_le_mul_infDist {K : Submodule 𝕜 X} {C : ℝ} {ustar u : X} (hu : u ∈ K)
    (h : ∀ w ∈ K, ‖ustar - u‖ ≤ C * ‖ustar - w‖) :
    ‖ustar - u‖ ≤ C * Metric.infDist ustar (K : Set X) := by
  rcases le_or_gt C 0 with hC | hC
  · have h0 : ‖ustar - u‖ ≤ 0 := by nlinarith [h u hu, norm_nonneg (ustar - u)]
    have hd : Metric.infDist ustar (K : Set X) = 0 :=
      le_antisymm ((Metric.infDist_le_dist_of_mem hu).trans (by rwa [dist_eq_norm]))
        Metric.infDist_nonneg
    rw [hd, mul_zero]
    exact h0
  · rw [← div_le_iff₀' hC, Metric.le_infDist ⟨0, K.zero_mem⟩]
    intro w hw
    rw [div_le_iff₀' hC, dist_eq_norm]
    exact h w hw

/-- Let $(K_n)$ be a monotone sequence of subspaces of a normed space $X$ whose union is dense in
$X$. Then $\operatorname{dist}(u, K_n) \to 0$ as $n \to \infty$ for every $u \in X$.

This is the part on approximation that Corollaries 9.1.4 and 9.2.3 of [han2009theoretical]
share. Together with a quasi-optimality bound, it gives convergence of the discrete solutions. -/
theorem tendsto_infDist_of_monotone_dense {K : ℕ → Submodule 𝕜 X} (hmono : Monotone K)
    (hdense : Dense (⋃ n, (K n : Set X))) (u : X) :
    Filter.Tendsto (fun n => Metric.infDist u (K n : Set X)) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨w, hw, hwd⟩ := Metric.mem_closure_iff.mp (hdense u) ε hε
  obtain ⟨N, hwN⟩ := Set.mem_iUnion.mp hw
  refine ⟨N, fun n hn => ?_⟩
  have hmem : w ∈ (K n : Set X) := hmono hn hwN
  have h1 : Metric.infDist u (K n : Set X) ≤ dist u w := Metric.infDist_le_dist_of_mem hmem
  rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.infDist_nonneg]
  linarith

/-- Let $(K_n)$ be a monotone sequence of subspaces of a normed space $X$ whose union is dense, let
$C \in \mathbb{R}$, let $u^* \in X$, and let $u_n \in K_n$ satisfy
$\|u^* - u_n\| \le C \|u^* - w\|$ for every $n$ and every $w \in K_n$. Then $u_n \to u^*$.

This is the common core of Corollaries 9.1.4 and 9.2.3 of [han2009theoretical]: the
approximation error tends to zero by `tendsto_infDist_of_monotone_dense`, and the
quasi-optimality bound transfers this to the error. -/
theorem tendsto_of_forall_norm_sub_le {K : ℕ → Submodule 𝕜 X} (hmono : Monotone K)
    (hdense : Dense (⋃ n, (K n : Set X))) {C : ℝ} {uN : ℕ → X} {ustar : X}
    (hmem : ∀ n, uN n ∈ K n) (h : ∀ n, ∀ w ∈ K n, ‖ustar - uN n‖ ≤ C * ‖ustar - w‖) :
    Filter.Tendsto uN Filter.atTop (nhds ustar) := by
  have hzero : Filter.Tendsto (fun n => ‖ustar - uN n‖) Filter.atTop (nhds 0) := by
    refine squeeze_zero (fun n => norm_nonneg _)
      (fun n => norm_sub_le_mul_infDist (hmem n) (h n)) ?_
    simpa using (tendsto_infDist_of_monotone_dense hmono hdense ustar).const_mul C
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [norm_sub_rev] using hzero

end QuasiOptimal

namespace IsGalerkinSolution

variable {a : SesqForm 𝕜 V} {ℓ : V →L[𝕜] 𝕜} {K : Submodule 𝕜 V} {u : V}

/-- On a Hilbert space $V$, a vector $u$ is a Galerkin solution on $K$ for the form $a$ and the
functional $\ell$ if and only if $u \in K$ and $f - Au \perp K$, where $A$ is the operator of
$a$ and $f$ is the Riesz representative of $\ell$.

The right side is the operator specification `IsGalerkin` of `Numlib.Projection.Basic` with the
initial guess $x_0 = 0$. -/
theorem iff_isGalerkin [CompleteSpace V] :
    IsGalerkinSolution a ℓ K u ↔
      IsGalerkin (SesqForm.toOperator a : V →ₗ[𝕜] V) (SesqForm.rieszRep ℓ) 0 K u := by
  constructor
  · rintro ⟨hu, h⟩
    refine ⟨by simpa using hu, (Submodule.mem_orthogonal' _ _).mpr fun w hw => ?_⟩
    rw [inner_sub_left, SesqForm.inner_rieszRep, ContinuousLinearMap.coe_coe,
      SesqForm.inner_toOperator, h w hw, sub_self]
  · rintro ⟨hu, horth⟩
    refine ⟨by simpa using hu, fun w hw => ?_⟩
    have hz := (Submodule.mem_orthogonal' _ _).mp horth w hw
    rw [inner_sub_left, SesqForm.inner_rieszRep, ContinuousLinearMap.coe_coe,
      SesqForm.inner_toOperator, sub_eq_zero] at hz
    exact hz.symm

/-- Let $a$ be coercive with a constant $c > 0$, and let $K$ be a complete subspace. Then the
Galerkin problem on $K$ has exactly one solution.

The restriction of $a$ to $K$ is bounded and coercive with the same constant, so the Lax–Milgram
theorem applies on $K$ ([han2009theoretical], §9.1). -/
theorem existsUnique {c : ℝ} (hc : 0 < c) (ha : a.IsCoerciveWith c) [CompleteSpace K] :
    ∃! u, IsGalerkinSolution a ℓ K u := by
  have hcoer : SesqForm.IsCoerciveWith
      (SesqForm₂.restrict (a : SesqForm₂ 𝕜 V V) K K) c := fun v => ha (v : V)
  obtain ⟨w, hw, hwu⟩ := SesqForm.laxMilgram
    (SesqForm₂.restrict (a : SesqForm₂ 𝕜 V V) K K) (ℓ.comp K.subtypeL) hc hcoer
  refine ⟨(w : V), ⟨w.2, fun v hv => hw ⟨v, hv⟩⟩, ?_⟩
  rintro y ⟨hyK, hy⟩
  exact congrArg Subtype.val (hwu ⟨y, hyK⟩ fun z => hy (z : V) z.2)

/-- **Galerkin orthogonality.** Let $u$ be a Galerkin solution on $K$, and let $u^*$ satisfy
$a(u^*, v) = \ell(v)$ for all $v \in V$. Then $a(u^* - u, v) = 0$ for every $v \in K$. -/
theorem apply_sub_eq_zero (hN : IsGalerkinSolution a ℓ K u) {ustar : V}
    (hstar : ∀ v, a ustar v = ℓ v) {v : V} (hv : v ∈ K) : a (ustar - u) v = 0 := by
  rw [map_sub, sub_apply, hstar v, hN.2 v hv, sub_self]

/-- If $a$ is bounded with constant $M$, then $M \|z\| \ge 0$ for every $z$, with no sign hypothesis
on $M$. -/
private theorem nonneg_mul_norm {M : ℝ} (hM : a.IsBoundedWith M) (z : V) : 0 ≤ M * ‖z‖ := by
  rcases eq_or_lt_of_le (norm_nonneg z) with h | h
  · simp [← h]
  · nlinarith [norm_nonneg (a z z), hM z z]

/-- **Céa's lemma** ([han2009theoretical], Proposition 9.1.3, inequality (9.1.11)). Let $a$ be
bounded with constant $M$ and coercive with constant $c > 0$. Let $u$ be a Galerkin solution on
$K$, and let $u^*$ satisfy $a(u^*, v) = \ell(v)$ for all $v \in V$. Then for every $v \in K$,
$$\|u^* - u\| \le \frac{M}{c} \|u^* - v\|.$$

So the Galerkin error is, up to the factor $M / c$, no worse than the error of the best
approximation from $K$. -/
theorem norm_sub_le {M c : ℝ} (hc : 0 < c) (hM : a.IsBoundedWith M) (ha : a.IsCoerciveWith c)
    (hN : IsGalerkinSolution a ℓ K u) {ustar : V} (hstar : ∀ v, a ustar v = ℓ v) {v : V}
    (hv : v ∈ K) : ‖ustar - u‖ ≤ M / c * ‖ustar - v‖ := by
  have horth : a (ustar - u) (v - u) = 0 := hN.apply_sub_eq_zero hstar (K.sub_mem hv hN.1)
  have hsplit : a (ustar - u) (ustar - u) = a (ustar - u) (ustar - v) := by
    have h1 : (ustar - u : V) = (ustar - v) + (v - u) := by abel
    nth_rewrite 2 [h1]
    rw [map_add, horth, add_zero]
  have key : c * ‖ustar - u‖ ^ 2 ≤ M * ‖ustar - u‖ * ‖ustar - v‖ := by
    calc c * ‖ustar - u‖ ^ 2 ≤ RCLike.re (a (ustar - u) (ustar - u)) := ha _
      _ = RCLike.re (a (ustar - u) (ustar - v)) := by rw [hsplit]
      _ ≤ ‖a (ustar - u) (ustar - v)‖ := RCLike.re_le_norm _
      _ ≤ M * ‖ustar - u‖ * ‖ustar - v‖ := hM _ _
  have hcM : c * ‖ustar - u‖ ≤ M * ‖ustar - v‖ := by
    rcases eq_or_lt_of_le (norm_nonneg (ustar - u)) with h | h
    · rw [← h, mul_zero]
      exact nonneg_mul_norm hM (ustar - v)
    · refine le_of_mul_le_mul_right ?_ h
      calc c * ‖ustar - u‖ * ‖ustar - u‖ = c * ‖ustar - u‖ ^ 2 := by ring
        _ ≤ M * ‖ustar - u‖ * ‖ustar - v‖ := key
        _ = M * ‖ustar - v‖ * ‖ustar - u‖ := by ring
  rw [div_mul_eq_mul_div, le_div_iff₀ hc, mul_comm]
  exact hcM

/-- **Céa's lemma** with the infimum. Under the hypotheses of `IsGalerkinSolution.norm_sub_le`,
$$\|u^* - u\| \le \frac{M}{c} \operatorname{dist}(u^*, K).$$
-/
theorem norm_sub_le_infDist {M c : ℝ} (hc : 0 < c) (hM : a.IsBoundedWith M)
    (ha : a.IsCoerciveWith c) (hN : IsGalerkinSolution a ℓ K u) {ustar : V}
    (hstar : ∀ v, a ustar v = ℓ v) : ‖ustar - u‖ ≤ M / c * Metric.infDist ustar (K : Set V) :=
  norm_sub_le_mul_infDist hN.1 fun _ hv => norm_sub_le hc hM ha hN hstar hv

/-- Let $a$ be Hermitian with $\operatorname{Re} a(v, v) \ge 0$ for all $v$. Let $u$ be a Galerkin
solution on $K$, and let $u^*$ satisfy $a(u^*, v) = \ell(v)$ for all $v \in V$. Then for every
$v \in K$,
$$\|u^* - u\|_a \le \|u^* - v\|_a,$$
where $\|w\|_a = \sqrt{\operatorname{Re} a(w, w)}$ is the energy norm.

So $u$ is the best approximation of $u^*$ from $K$ in the energy norm, that is, the orthogonal
projection of $u^*$ onto $K$ for the inner product $a$. This is the remark after Proposition
9.1.3 of [han2009theoretical], and it is the exact form of the equivalence between the Galerkin
problem (9.1.4) and the Ritz problem (9.1.8) of minimizing the energy functional (9.1.7) over
$K$.

The positivity hypothesis cannot be dropped. Take $V = \mathbb{R}^2$,
$a(u, v) = u_1 v_1 - u_2 v_2$, $K = \operatorname{span}\{(1, 2)\}$, $u^* = (3, 0)$ and
$\ell = a(u^*, \cdot)$. Then $u = (-1, -2)$ is the Galerkin solution, and $v = 0 \in K$ gives
$\|u^* - u\|_a = \sqrt{12} > 3 = \|u^* - v\|_a$. Positivity is what makes the energy norm a
seminorm, so it is the minimal additional hypothesis. -/
theorem energyNorm_sub_le (ha : a.IsHermitian) (hpos : a.IsCoerciveWith 0)
    (hN : IsGalerkinSolution a ℓ K u) {ustar : V} (hstar : ∀ v, a ustar v = ℓ v) {v : V}
    (hv : v ∈ K) : a.energyNorm (ustar - u) ≤ a.energyNorm (ustar - v) := by
  have h0 : a (ustar - u) (u - v) = 0 := hN.apply_sub_eq_zero hstar (K.sub_mem hN.1 hv)
  have h0' : a (u - v) (ustar - u) = 0 := by
    rw [ha (u - v) (ustar - u), h0, map_zero]
  have hsum : (ustar - v : V) = (ustar - u) + (u - v) := by abel
  have hexp : RCLike.re (a (ustar - v) (ustar - v))
      = RCLike.re (a (ustar - u) (ustar - u)) + RCLike.re (a (u - v) (u - v)) := by
    rw [hsum]
    simp only [map_add, add_apply, h0, h0', add_zero, zero_add, map_add]
  rw [SesqForm.energyNorm, SesqForm.energyNorm, hexp]
  refine Real.sqrt_le_sqrt ?_
  have := hpos (u - v)
  simp only [zero_mul] at this
  linarith

/-- **Céa's lemma for a Hermitian form.** Let $a$ be bounded with constant $M$, coercive with
constant $c > 0$ and Hermitian. Let $u$ be a Galerkin solution on $K$, and let $u^*$ satisfy
$a(u^*, v) = \ell(v)$ for all $v \in V$. Then for every $v \in K$,
$$\|u^* - u\| \le \sqrt{\frac{M}{c}} \, \|u^* - v\|.$$

The proof passes through the energy norm, in which $u$ is optimal by
`IsGalerkinSolution.energyNorm_sub_le`, and uses the norm equivalence
$\sqrt{c} \|w\| \le \|w\|_a \le \sqrt{M} \|w\|$ at each end. -/
theorem norm_sub_le_sqrt {M c : ℝ} (hc : 0 < c) (hM : a.IsBoundedWith M) (ha : a.IsCoerciveWith c)
    (hh : a.IsHermitian) (hN : IsGalerkinSolution a ℓ K u) {ustar : V}
    (hstar : ∀ v, a ustar v = ℓ v) {v : V} (hv : v ∈ K) :
    ‖ustar - u‖ ≤ Real.sqrt (M / c) * ‖ustar - v‖ := by
  have hpos : a.IsCoerciveWith 0 := SesqForm.IsCoerciveWith.mono a ha hc.le
  have h1 : Real.sqrt c * ‖ustar - u‖ ≤ a.energyNorm (ustar - u) :=
    a.sqrt_mul_norm_le_energyNorm hc.le ha _
  have h2 := hN.energyNorm_sub_le hh hpos hstar hv
  have h3 : a.energyNorm (ustar - v) ≤ Real.sqrt M * ‖ustar - v‖ :=
    a.energyNorm_le_sqrt_mul_norm hM _
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  rw [Real.sqrt_div' M hc.le, div_mul_eq_mul_div, le_div_iff₀ hsc, mul_comm]
  linarith

/-- **The Galerkin problem as a linear system** ([han2009theoretical], (9.1.5)). Let
$\varphi = (\varphi_j)_{j \in \iota}$ be a finite basis of $K$, and let
$\xi \in \mathbb{K}^\iota$. Then $\sum_j \xi_j \varphi_j$ is a Galerkin solution on $K$ if and
only if
$$\sum_j a(\varphi_j, \varphi_i) \, \overline{\xi_j} = \ell(\varphi_i) \quad \text{for all }
  i.$$

The matrix $(a(\varphi_j, \varphi_i))_{ij}$ is the stiffness matrix and the right side is the
load vector.

The coefficient vector is conjugated because $a$ is conjugate-linear in its first argument:
$a(\sum_j \xi_j \varphi_j, \varphi_i) = \sum_j \overline{\xi_j} \, a(\varphi_j, \varphi_i)$.
Over $\mathbb{R}$, `star` is the identity, and the statement is (9.1.5) as printed. -/
theorem iff_mulVec {ι : Type*} [Fintype ι] (φ : Module.Basis ι 𝕜 K) (ξ : ι → 𝕜) :
    IsGalerkinSolution a ℓ K (∑ j, ξ j • (φ j : V)) ↔
      (Matrix.of fun i j => a (φ j : V) (φ i)).mulVec (star ξ) = fun i => ℓ (φ i) := by
  have hmem : (∑ j, ξ j • (φ j : V)) ∈ K := K.sum_mem fun j _ => K.smul_mem _ (φ j).2
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : V, u₀ = ∑ j, ξ j • (φ j : V) := ⟨_, rfl⟩
  have happ : ∀ w : V, a u₀ w = ∑ j, starRingEnd 𝕜 (ξ j) * a (φ j : V) w := by
    intro w
    rw [hu₀, map_sum]
    simp only [sum_apply, map_smulₛₗ, smul_apply,
      smul_eq_mul]
  rw [← hu₀] at hmem ⊢
  have hmul : ∀ i, (Matrix.of fun i j => a (φ j : V) (φ i)).mulVec (star ξ) i
      = ∑ j, starRingEnd 𝕜 (ξ j) * a (φ j : V) (φ i) := by
    intro i
    simp only [Matrix.mulVec, Matrix.of_apply, dotProduct, Pi.star_apply, starRingEnd_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hkey : (∀ i, a u₀ (φ i : V) = ℓ (φ i))
      ↔ (Matrix.of fun i j => a (φ j : V) (φ i)).mulVec (star ξ) = fun i => ℓ (φ i) := by
    constructor
    · intro h
      funext i
      rw [hmul i, ← happ, h i]
    · intro h i
      have hi := congrFun h i
      rw [hmul i] at hi
      rw [happ]
      exact hi
  rw [← hkey]
  constructor
  · rintro ⟨-, h⟩ i
    exact h _ (φ i).2
  · intro h
    refine ⟨hmem, fun w hw => ?_⟩
    have heq : (((a u₀).comp K.subtypeL : K →L[𝕜] 𝕜) : K →ₗ[𝕜] 𝕜)
        = ((ℓ.comp K.subtypeL : K →L[𝕜] 𝕜) : K →ₗ[𝕜] 𝕜) :=
      φ.ext fun i => h i
    exact LinearMap.congr_fun heq ⟨w, hw⟩

end IsGalerkinSolution

/-- **Corollary 9.1.4** of [han2009theoretical]. Let $a$ be bounded with constant $M$ and coercive
with constant $c > 0$. Let $(K_n)$ be a monotone sequence of subspaces whose union is dense in
$V$, let $u_n$ be a Galerkin solution on $K_n$ for every $n$, and let $u^*$ satisfy
$a(u^*, v) = \ell(v)$ for all $v \in V$. Then $u_n \to u^*$. -/
theorem IsGalerkinSolution.tendsto {a : SesqForm 𝕜 V} {ℓ : V →L[𝕜] 𝕜} {M c : ℝ} (hc : 0 < c)
    (hM : a.IsBoundedWith M) (ha : a.IsCoerciveWith c) {K : ℕ → Submodule 𝕜 V}
    (hmono : Monotone K) (hdense : Dense (⋃ n, (K n : Set V))) {uN : ℕ → V}
    (hN : ∀ n, IsGalerkinSolution a ℓ (K n) (uN n))
    {ustar : V} (hstar : ∀ v, a ustar v = ℓ v) :
    Filter.Tendsto uN Filter.atTop (nhds ustar) :=
  tendsto_of_forall_norm_sub_le hmono hdense (fun n => (hN n).1)
    fun n _ hw => (hN n).norm_sub_le hc hM ha hstar hw

/-!
### The stiffness matrix of a form in a finite family

For a finite family $\varphi$, the matrix $A_{ij} = a(\varphi_j, \varphi_i)$ is the stiffness matrix
of the finite element literature. When $a$ is Hermitian and coercive, it is the Gram matrix of
$\varphi$ for the energy inner product. It is the matrix of `IsGalerkinSolution.iff_mulVec`. A
linear solver needs two facts about it, Hermitian symmetry and positive definiteness, and both
follow from the corresponding properties of the form.
-/

section GramMatrix

variable {ι : Type*}

namespace SesqForm

/-- The **stiffness matrix** (Gram matrix) of a form $a$ in a family
$\varphi = (\varphi_i)_{i \in \iota}$ of vectors: the matrix $A$ with entries
$A_{ij} = a(\varphi_j, \varphi_i)$.

With this order of the indices, the Galerkin problem is the linear system $A \xi = b$ with
$b_i = \ell(\varphi_i)$, as in `IsGalerkinSolution.iff_mulVec`. -/
def gramMatrix (a : SesqForm 𝕜 V) (φ : ι → V) : Matrix ι ι 𝕜 :=
  Matrix.of fun i j => a (φ j) (φ i)

/-- The entries of the stiffness matrix are $A_{ij} = a(\varphi_j, \varphi_i)$.

The form is evaluated with the column index first, so that the Galerkin condition is
$A \xi = b$. -/
@[simp]
theorem gramMatrix_apply (a : SesqForm 𝕜 V) (φ : ι → V) (i j : ι) :
    a.gramMatrix φ i j = a (φ j) (φ i) := rfl

/-- The stiffness matrix of a Hermitian form in any family is Hermitian. -/
theorem gramMatrix_isHermitian {a : SesqForm 𝕜 V} (h : a.IsHermitian) (φ : ι → V) :
    (a.gramMatrix φ).IsHermitian := by
  ext i j
  simpa only [Matrix.conjTranspose_apply, gramMatrix_apply, RCLike.star_def]
    using (h (φ j) (φ i)).symm

variable [Fintype ι]

/-- **The Galerkin problem as a linear system in the stiffness matrix.** Let $\varphi$ be a finite
basis of $K$, let $A$ be the stiffness matrix of $a$ in $\varphi$, and let
$\xi \in \mathbb{K}^\iota$. Then $\sum_j \xi_j \varphi_j$ is a Galerkin solution on $K$ if and
only if $A \overline{\xi} = (\ell(\varphi_i))_i$.

This is `IsGalerkinSolution.iff_mulVec` with the matrix named. -/
theorem _root_.IsGalerkinSolution.iff_gramMatrix_mulVec {a : SesqForm 𝕜 V} {ℓ : V →L[𝕜] 𝕜}
    {K : Submodule 𝕜 V} (φ : Module.Basis ι 𝕜 K) (ξ : ι → 𝕜) :
    IsGalerkinSolution a ℓ K (∑ j, ξ j • (φ j : V)) ↔
      (a.gramMatrix fun i => (φ i : V)).mulVec (star ξ) = fun i => ℓ (φ i) :=
  IsGalerkinSolution.iff_mulVec φ ξ

/-- For the stiffness matrix $A$ of $a$ in a finite family $\varphi$ and vectors
$\xi, \eta \in \mathbb{K}^\iota$,
$$\sum_i \eta_i \, (A \overline{\xi})_i = a\Big(\sum_j \xi_j \varphi_j, \sum_i \eta_i
  \varphi_i\Big).$$

The conjugation of $\xi$ is the one that $a$ carries in its first argument, and it disappears
over $\mathbb{R}$. -/
theorem dotProduct_gramMatrix_mulVec (a : SesqForm 𝕜 V) (φ : ι → V) (ξ η : ι → 𝕜) :
    η ⬝ᵥ (a.gramMatrix φ).mulVec (star ξ) = a (∑ j, ξ j • φ j) (∑ i, η i • φ i) := by
  have hfirst : ∀ w : V, a (∑ j, ξ j • φ j) w = ∑ j, starRingEnd 𝕜 (ξ j) * a (φ j) w := by
    intro w
    simp [map_sum, map_smulₛₗ, smul_eq_mul]
  have hsecond : a (∑ j, ξ j • φ j) (∑ i, η i • φ i)
      = ∑ i, η i * a (∑ j, ξ j • φ j) (φ i) := by
    simp [map_sum, smul_eq_mul]
  rw [hsecond]
  simp only [hfirst, Matrix.mulVec, dotProduct, gramMatrix_apply, Pi.star_apply,
    starRingEnd_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end SesqForm

section Real

variable [Fintype ι] {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- Over $\mathbb{R}$, for the stiffness matrix $A$ of $a$ in a finite family $\varphi$ and vectors
$\xi, \eta \in \mathbb{R}^\iota$,
$$\eta^T A \xi = a\Big(\sum_j \xi_j \varphi_j, \sum_i \eta_i \varphi_i\Big).$$
-/
theorem SesqForm.dotProduct_gramMatrix_mulVec_real (a : SesqForm ℝ W) (φ : ι → W) (ξ η : ι → ℝ) :
    η ⬝ᵥ (a.gramMatrix φ).mulVec ξ = a (∑ j, ξ j • φ j) (∑ i, η i • φ i) :=
  a.dotProduct_gramMatrix_mulVec φ ξ η

/-- Over $\mathbb{R}$, for the stiffness matrix $A$ of $a$ in a finite family $\varphi$ and a vector
$\xi \in \mathbb{R}^\iota$, the entries of $A \xi$ are $(A \xi)_i = a(\sum_j \xi_j \varphi_j,
\varphi_i)$. -/
theorem SesqForm.gramMatrix_mulVec_apply (a : SesqForm ℝ W) (φ : ι → W) (ξ : ι → ℝ)
    (i : ι) : (a.gramMatrix φ).mulVec ξ i = a (∑ j, ξ j • φ j) (φ i) := by
  rw [Matrix.mulVec, dotProduct]
  simp only [SesqForm.gramMatrix_apply, map_sum, map_smulₛₗ, RCLike.conj_to_real,
    _root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- Over $\mathbb{R}$, let $a$ be coercive with a constant $c > 0$, let $\varphi$ be a finite
linearly independent family, and let $A$ be the stiffness matrix of $a$ in $\varphi$. Then
$\xi^T A \xi > 0$ for every $\xi \neq 0$.

Symmetry of $a$ is not needed for this half of positive definiteness. -/
theorem SesqForm.gramMatrix_dotProduct_pos {a : SesqForm ℝ W} {c : ℝ} (hc : 0 < c)
    (ha : a.IsCoerciveWith c) {φ : ι → W} (hφ : LinearIndependent ℝ φ) {ξ : ι → ℝ}
    (hξ : ξ ≠ 0) : 0 < ξ ⬝ᵥ (a.gramMatrix φ).mulVec ξ := by
  rw [a.dotProduct_gramMatrix_mulVec_real φ ξ ξ]
  have hne : (∑ j, ξ j • φ j) ≠ 0 := fun h =>
    hξ (funext fun i => Fintype.linearIndependent_iff.mp hφ ξ h i)
  have hnorm : 0 < ‖(∑ j, ξ j • φ j : W)‖ := norm_pos_iff.mpr hne
  exact lt_of_lt_of_le (mul_pos hc (pow_pos hnorm 2)) (ha _)

set_option linter.unusedFintypeInType false in
/-- Over $\mathbb{R}$, let $a$ be symmetric and coercive with a constant $c > 0$, and let $\varphi$
be a finite linearly independent family. Then the stiffness matrix of $a$ in $\varphi$ is
positive definite.

This is why the linear systems of the finite element method can be solved by conjugate
gradients. -/
theorem SesqForm.gramMatrix_posDef {a : SesqForm ℝ W} {c : ℝ} (hc : 0 < c)
    (hsymm : a.IsHermitian) (ha : a.IsCoerciveWith c) {φ : ι → W}
    (hφ : LinearIndependent ℝ φ) : (a.gramMatrix φ).PosDef :=
  Matrix.PosDef.of_dotProduct_mulVec_pos (a.gramMatrix_isHermitian hsymm φ) fun ξ hξ => by
    rw [show star ξ = ξ from funext fun i => star_trivial (ξ i)]
    exact SesqForm.gramMatrix_dotProduct_pos hc ha hφ hξ

end Real

end GramMatrix

namespace IsPetrovGalerkinSolution

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace 𝕜 U] {a : SesqForm₂ 𝕜 U V}
  {ℓ : V →L[𝕜] 𝕜} {K : Submodule 𝕜 U} {L : Submodule 𝕜 V} {u : U}

/-- The **discrete inf–sup condition** ([han2009theoretical], (9.2.6)) with constant $\alpha$, for a
form $a$ on $U \times V$, a trial space $K \subseteq U$ and a test space $L \subseteq V$:
$$\alpha \|w\| \le \sup_{v \in L, \, v \neq 0} \frac{|a(w, v)|}{\|v\|} \quad \text{for all } w
  \in K.$$

The supremum is stated as the norm of the functional $a(w, \cdot)$ restricted to $L$. This is
the discrete counterpart of `SesqForm₂.InfSupWith`, and it does not follow from it, because the
supremum is taken over the smaller test space $L$. -/
def DiscreteInfSup (a : SesqForm₂ 𝕜 U V) (K : Submodule 𝕜 U) (L : Submodule 𝕜 V) (α : ℝ) :
    Prop :=
  ∀ w ∈ K, α * ‖w‖ ≤ ‖(a w).comp L.subtypeL‖

/-- The operator from $K$ to $L$ that sends $w$ to the Riesz representative in $L$ of the functional
$a(w, \cdot)$ on $L$; it is linear because both $a$ and the inverse Riesz map are
conjugate-linear. -/
private noncomputable def rieszOp (a : SesqForm₂ 𝕜 U V) (K : Submodule 𝕜 U)
    (L : Submodule 𝕜 V) [CompleteSpace L] : K →ₗ[𝕜] L where
  toFun w := (InnerProductSpace.toDual 𝕜 L).symm (SesqForm₂.restrict a K L w)
  map_add' x y := by simp
  map_smul' r x := by
    simp only [map_smulₛₗ, RingHom.id_apply, starRingEnd_self_apply]

/-- The inner product of the image of $w$ under this operator with $v \in L$ is $a(w, v)$. -/
private theorem inner_rieszOp (a : SesqForm₂ 𝕜 U V) (K : Submodule 𝕜 U) (L : Submodule 𝕜 V)
    [CompleteSpace L] (w : K) (v : L) :
    inner 𝕜 (rieszOp a K L w) v = a (w : U) (v : V) := by
  change inner 𝕜 ((InnerProductSpace.toDual 𝕜 L).symm (SesqForm₂.restrict a K L w)) v = _
  exact InnerProductSpace.toDual_symm_apply

/-- The image of $w$ under this operator has the norm of the functional $a(w, \cdot)$ on $L$. -/
private theorem norm_rieszOp_apply (a : SesqForm₂ 𝕜 U V) (K : Submodule 𝕜 U) (L : Submodule 𝕜 V)
    [CompleteSpace L] (w : K) : ‖rieszOp a K L w‖ = ‖(a (w : U)).comp L.subtypeL‖ := by
  change ‖(InnerProductSpace.toDual 𝕜 L).symm (SesqForm₂.restrict a K L w)‖ = _
  exact (InnerProductSpace.toDual 𝕜 L).symm.norm_map _

/-- **Theorem 9.2.1** of [han2009theoretical] (Babuška), existence and uniqueness. Let
$K \subseteq U$ and $L \subseteq V$ be finite-dimensional with $\dim K = \dim L$, and let the
discrete inf–sup condition hold with a constant $\alpha > 0$. Then for every functional $\ell$
on $V$, the Petrov–Galerkin problem has exactly one solution.

Because the dimensions are equal, injectivity gives surjectivity, so no density argument is
needed. -/
theorem existsUnique [FiniteDimensional 𝕜 K] [FiniteDimensional 𝕜 L]
    (hdim : Module.finrank 𝕜 K = Module.finrank 𝕜 L) {α : ℝ} (hα : 0 < α)
    (hinf : DiscreteInfSup a K L α) : ∃! u, IsPetrovGalerkinSolution a ℓ K L u := by
  have hbd : ∀ w : K, α * ‖w‖ ≤ ‖rieszOp a K L w‖ := fun w => by
    rw [norm_rieszOp_apply]
    exact hinf (w : U) w.2
  have hinj : Function.Injective (rieszOp a K L) := by
    intro x y hxy
    have hx := hbd (x - y)
    rw [map_sub, hxy, sub_self, norm_zero] at hx
    have hx0 : ‖x - y‖ ≤ 0 := by nlinarith [norm_nonneg (x - y)]
    exact sub_eq_zero.mp (norm_le_zero_iff.mp hx0)
  have hsurj : Function.Surjective (rieszOp a K L) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  obtain ⟨w, hw⟩ := hsurj (SesqForm.rieszRep (ℓ.comp L.subtypeL))
  have hw' : rieszOp a K L w = SesqForm.rieszRep (ℓ.comp L.subtypeL) := hw
  refine ⟨(w : U), ⟨w.2, fun v hv => ?_⟩, ?_⟩
  · have h1 := inner_rieszOp a K L w ⟨v, hv⟩
    rw [hw', SesqForm.inner_rieszRep] at h1
    exact h1.symm
  · rintro y ⟨hyK, hy⟩
    have hkey : rieszOp a K L ⟨y, hyK⟩ = rieszOp a K L w := by
      rw [hw']
      refine ext_inner_right 𝕜 fun v => ?_
      rw [inner_rieszOp, SesqForm.inner_rieszRep]
      exact hy (v : V) v.2
    exact congrArg Subtype.val (hinj hkey)

set_option linter.unusedVariables false in
/-- **Theorem 9.2.1** of [han2009theoretical] (Babuška), estimate (9.2.7). Let $K \subseteq U$ and
$L \subseteq V$ be finite-dimensional with $\dim K = \dim L$, let $a$ be bounded with a constant
$M \ge 0$, and let the discrete inf–sup condition hold with a constant $\alpha > 0$. Let $u$ be
a Petrov–Galerkin solution, and let $u^* \in U$ satisfy $a(u^*, v) = \ell(v)$ for all $v \in V$.
Then for every $w \in K$,
$$\|u^* - u\| \le \Big(1 + \frac{M}{\alpha}\Big) \|u^* - w\|.$$

This is the Petrov–Galerkin analogue of Céa's lemma.

The hypothesis $M \ge 0$ cannot be dropped. Take $V = 0$, $U = \mathbb{R}$, $K = L = 0$,
$a = 0$, $\alpha = 1$ and $M = -1$. Then every hypothesis holds, and the conclusion is
$\|u^*\| \le 0$. The hypotheses $\dim K = \dim L$ and finite dimension are part of the statement
because Theorem 9.2.1 states the estimate together with unique solvability, but the proof of the
estimate does not use them: it holds for any solution of the discrete problem. For this reason
the linter for unused variables is off here. -/
theorem norm_sub_le [FiniteDimensional 𝕜 K] [FiniteDimensional 𝕜 L]
    (hdim : Module.finrank 𝕜 K = Module.finrank 𝕜 L) {M α : ℝ} (hα : 0 < α) (hM0 : 0 ≤ M)
    (hM : a.IsBoundedWith M) (hinf : DiscreteInfSup a K L α)
    (hN : IsPetrovGalerkinSolution a ℓ K L u) {ustar : U} (hstar : ∀ v, a ustar v = ℓ v) {w : U}
    (hw : w ∈ K) : ‖ustar - u‖ ≤ (1 + M / α) * ‖ustar - w‖ := by
  -- the restricted functionals of `u - w` and of `ustar - w` agree on `L`
  have hres : (a (u - w)).comp L.subtypeL = (a (ustar - w)).comp L.subtypeL := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, map_sub,
      sub_apply, hN.2 (v : V) v.2, hstar (v : V)]
  have hMnn : 0 ≤ M * ‖ustar - w‖ := mul_nonneg hM0 (norm_nonneg _)
  have hbound : ‖(a (ustar - w)).comp L.subtypeL‖ ≤ M * ‖ustar - w‖ :=
    ContinuousLinearMap.opNorm_le_bound _ hMnn fun v => hM (ustar - w) (v : V)
  have huw : α * ‖u - w‖ ≤ M * ‖ustar - w‖ := by
    calc α * ‖u - w‖ ≤ ‖(a (u - w)).comp L.subtypeL‖ := hinf _ (K.sub_mem hN.1 hw)
      _ = ‖(a (ustar - w)).comp L.subtypeL‖ := by rw [hres]
      _ ≤ M * ‖ustar - w‖ := hbound
  have huw' : ‖u - w‖ ≤ M / α * ‖ustar - w‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hα, mul_comm]
    exact huw
  have htri : ‖ustar - u‖ ≤ ‖ustar - w‖ + ‖w - u‖ := by
    simpa [dist_eq_norm] using dist_triangle ustar w u
  calc ‖ustar - u‖ ≤ ‖ustar - w‖ + ‖w - u‖ := htri
    _ = ‖ustar - w‖ + ‖u - w‖ := by rw [norm_sub_rev w u]
    _ ≤ ‖ustar - w‖ + M / α * ‖ustar - w‖ := by linarith
    _ = (1 + M / α) * ‖ustar - w‖ := by ring

/-- **Corollary 9.2.3** of [han2009theoretical]. Let $(K_n)$ and $(L_n)$ be finite-dimensional trial
and test spaces with $\dim K_n = \dim L_n$, let $a$ be bounded with a constant $M \ge 0$, and
let the discrete inf–sup condition hold on $K_n \times L_n$ with one constant $\alpha > 0$ for
all $n$. Let $(K_n)$ be monotone with dense union in $U$, let $u_n$ be a Petrov–Galerkin
solution on $K_n \times L_n$, and let $u^*$ satisfy $a(u^*, v) = \ell(v)$ for all $v \in V$.
Then $u_n \to u^*$.

The hypothesis $M \ge 0$ is needed for the same reason as in
`IsPetrovGalerkinSolution.norm_sub_le`. -/
theorem tendsto {K : ℕ → Submodule 𝕜 U} {L : ℕ → Submodule 𝕜 V} [∀ n, FiniteDimensional 𝕜 (K n)]
    [∀ n, FiniteDimensional 𝕜 (L n)] (hdim : ∀ n, Module.finrank 𝕜 (K n) = Module.finrank 𝕜 (L n))
    {M α : ℝ} (hα : 0 < α) (hM0 : 0 ≤ M) (hM : a.IsBoundedWith M)
    (hinf : ∀ n, DiscreteInfSup a (K n) (L n) α) (hmono : Monotone K)
    (hdense : Dense (⋃ n, (K n : Set U))) {uN : ℕ → U}
    (hN : ∀ n, IsPetrovGalerkinSolution a ℓ (K n) (L n) (uN n)) {ustar : U}
    (hstar : ∀ v, a ustar v = ℓ v) : Filter.Tendsto uN Filter.atTop (nhds ustar) :=
  tendsto_of_forall_norm_sub_le hmono hdense (fun n => (hN n).1)
    fun n _ hw => norm_sub_le (hdim n) hα hM0 hM (hinf n) (hN n) hstar hw

/-! ### The Petrov–Galerkin projector and the Xu–Zikatanov bound -/

section Projector

/-- If $a$ is bounded with a constant $M \ge 0$, then the functional $a(u, \cdot)$ restricted to $L$
has norm at most $M \|u\|$. -/
private theorem norm_comp_subtypeL_le {M : ℝ} (hM0 : 0 ≤ M)
    (hM : a.IsBoundedWith M) (u : U) :
    ‖(a u).comp L.subtypeL‖ ≤ M * ‖u‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hM0 (norm_nonneg _)) fun v => hM u (v : V)

variable [FiniteDimensional 𝕜 K] [FiniteDimensional 𝕜 L]

/-- The Petrov–Galerkin approximation of $u \in U$: the unique solution in $K$ of the
Petrov–Galerkin problem with the functional $a(u, \cdot)$. -/
private noncomputable def projFun (a : SesqForm₂ 𝕜 U V) (K : Submodule 𝕜 U) (L : Submodule 𝕜 V)
    [FiniteDimensional 𝕜 K] [FiniteDimensional 𝕜 L]
    (hdim : Module.finrank 𝕜 K = Module.finrank 𝕜 L) {α : ℝ} (hα : 0 < α)
    (hinf : DiscreteInfSup a K L α) (u : U) : U :=
  (existsUnique (a := a) (ℓ := a u) (K := K) (L := L) hdim hα hinf).choose

/-- The Petrov–Galerkin approximation of $u$ solves the Petrov–Galerkin problem with the functional
$a(u, \cdot)$. -/
private theorem projFun_spec (hdim : Module.finrank 𝕜 K = Module.finrank 𝕜 L) {α : ℝ}
    (hα : 0 < α) (hinf : DiscreteInfSup a K L α) (u : U) :
    IsPetrovGalerkinSolution a (a u) K L (projFun a K L hdim hα hinf u) :=
  (existsUnique (a := a) (ℓ := a u) (K := K) (L := L) hdim hα hinf).choose_spec.1

/-- Every solution of the Petrov–Galerkin problem with the functional $a(u, \cdot)$ is the
Petrov–Galerkin approximation of $u$. -/
private theorem eq_projFun (hdim : Module.finrank 𝕜 K = Module.finrank 𝕜 L) {α : ℝ}
    (hα : 0 < α) (hinf : DiscreteInfSup a K L α) {u w : U}
    (hw : IsPetrovGalerkinSolution a (a u) K L w) : w = projFun a K L hdim hα hinf u :=
  (existsUnique (a := a) (ℓ := a u) (K := K) (L := L) hdim hα hinf).choose_spec.2 w hw

/-- If $a$ is bounded with a constant $M \ge 0$, the Petrov–Galerkin approximation of $u$ has norm
at most $(M / \alpha) \|u\|$. -/
private theorem norm_projFun_le (hdim : Module.finrank 𝕜 K = Module.finrank 𝕜 L) {α : ℝ}
    (hα : 0 < α) (hinf : DiscreteInfSup a K L α) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : a.IsBoundedWith M) (u : U) :
    ‖projFun a K L hdim hα hinf u‖ ≤ M / α * ‖u‖ := by
  have hspec := projFun_spec hdim hα hinf u
  have heq : (a (projFun a K L hdim hα hinf u)).comp L.subtypeL = (a u).comp L.subtypeL := by
    ext v
    exact hspec.2 (v : V) v.2
  have h1 : α * ‖projFun a K L hdim hα hinf u‖ ≤ M * ‖u‖ := by
    calc α * ‖projFun a K L hdim hα hinf u‖
        ≤ ‖(a (projFun a K L hdim hα hinf u)).comp L.subtypeL‖ := hinf _ hspec.1
      _ = ‖(a u).comp L.subtypeL‖ := by rw [heq]
      _ ≤ M * ‖u‖ := norm_comp_subtypeL_le hM0 hM u
  rw [div_mul_eq_mul_div, le_div_iff₀ hα, mul_comm]
  exact h1

/-- **The Petrov–Galerkin projector** $P_N$ ([han2009theoretical], Remark 9.2.2). Let
$K \subseteq U$ and $L \subseteq V$ be finite-dimensional with $\dim K = \dim L$, and let the
discrete inf–sup condition hold with a constant $\alpha > 0$. Then $P_N$ is the bounded operator
on $U$ that sends $u$ to the unique $u_N \in K$ with $a(u_N, v) = a(u, v)$ for every $v \in L$.

The map does not depend on $\alpha$. The constant $\alpha$ enters through the proof of unique
solvability and through the bound $\|P_N\| \le M / \alpha$ of
`IsPetrovGalerkinSolution.norm_projection_le`. Boundedness is not automatic, because $U$ need
not be finite-dimensional; the discrete inf–sup condition makes the solution operator
continuous. -/
noncomputable def projection (a : SesqForm₂ 𝕜 U V) (K : Submodule 𝕜 U) (L : Submodule 𝕜 V)
    [FiniteDimensional 𝕜 K] [FiniteDimensional 𝕜 L]
    (hdim : Module.finrank 𝕜 K = Module.finrank 𝕜 L) {α : ℝ} (hα : 0 < α)
    (hinf : DiscreteInfSup a K L α) : U →L[𝕜] U :=
  LinearMap.mkContinuous
    { toFun := projFun a K L hdim hα hinf
      map_add' := fun x y => by
        refine (eq_projFun hdim hα hinf ?_).symm
        refine ⟨K.add_mem (projFun_spec hdim hα hinf x).1 (projFun_spec hdim hα hinf y).1,
          fun v hv => ?_⟩
        simp only [map_add, add_apply, (projFun_spec hdim hα hinf x).2 v hv,
          (projFun_spec hdim hα hinf y).2 v hv]
      map_smul' := fun r x => by
        simp only [RingHom.id_apply]
        refine (eq_projFun hdim hα hinf ?_).symm
        refine ⟨K.smul_mem r (projFun_spec hdim hα hinf x).1, fun v hv => ?_⟩
        simp only [map_smulₛₗ, smul_apply, (projFun_spec hdim hα hinf x).2 v hv] }
    (‖a‖ / α)
    (norm_projFun_le hdim hα hinf (norm_nonneg a) fun w v =>
      ((a w).le_opNorm v).trans (mul_le_mul_of_nonneg_right (a.le_opNorm w) (norm_nonneg v)))

/-- For every $u \in U$, the vector $P_N u$ solves the Petrov–Galerkin problem with the functional
$a(u, \cdot)$: $P_N u \in K$ and $a(P_N u, v) = a(u, v)$ for all $v \in L$. -/
theorem projection_spec
    (hdim : Module.finrank 𝕜 K = Module.finrank 𝕜 L) {α : ℝ} (hα : 0 < α)
    (hinf : DiscreteInfSup a K L α) (u : U) :
    IsPetrovGalerkinSolution a (a u) K L (projection a K L hdim hα hinf u) :=
  projFun_spec hdim hα hinf u

/-- The Petrov–Galerkin projector maps $U$ into the trial space: $P_N u \in K$ for every $u \in U$.
-/
theorem projection_apply_mem (hdim : Module.finrank 𝕜 K = Module.finrank 𝕜 L) {α : ℝ}
    (hα : 0 < α) (hinf : DiscreteInfSup a K L α) (u : U) :
    projection a K L hdim hα hinf u ∈ K :=
  (projection_spec hdim hα hinf u).1

/-- The Petrov–Galerkin projector fixes the trial space: $P_N w = w$ for every $w \in K$. -/
theorem projection_apply_of_mem (hdim : Module.finrank 𝕜 K = Module.finrank 𝕜 L) {α : ℝ}
    (hα : 0 < α) (hinf : DiscreteInfSup a K L α) {w : U} (hw : w ∈ K) :
    projection a K L hdim hα hinf w = w :=
  (eq_projFun hdim hα hinf ⟨hw, fun _ _ => rfl⟩).symm

/-- The Petrov–Galerkin projector is idempotent: $P_N^2 = P_N$. -/
theorem isIdempotentElem_projection (hdim : Module.finrank 𝕜 K = Module.finrank 𝕜 L) {α : ℝ}
    (hα : 0 < α) (hinf : DiscreteInfSup a K L α) :
    IsIdempotentElem (projection a K L hdim hα hinf) :=
  ContinuousLinearMap.ext fun u =>
    projection_apply_of_mem hdim hα hinf (projection_apply_mem hdim hα hinf u)

/-- The range of the Petrov–Galerkin projector is the trial space $K$. -/
theorem range_projection (hdim : Module.finrank 𝕜 K = Module.finrank 𝕜 L) {α : ℝ}
    (hα : 0 < α) (hinf : DiscreteInfSup a K L α) :
    LinearMap.range (projection a K L hdim hα hinf : U →ₗ[𝕜] U) = K := by
  refine le_antisymm ?_ fun w hw => ⟨w, projection_apply_of_mem hdim hα hinf hw⟩
  rintro _ ⟨v, rfl⟩
  exact projection_apply_mem hdim hα hinf v

/-- Let $u$ be a Petrov–Galerkin solution, and let $u^* \in U$ satisfy $a(u^*, v) = \ell(v)$ for all
$v \in V$. Then $P_N u^* = u$.

So the error $u^* - u$ is the value $(1 - P_N) u^*$. -/
theorem projection_apply_eq_of_isPetrovGalerkinSolution
    (hdim : Module.finrank 𝕜 K = Module.finrank 𝕜 L) {α : ℝ} (hα : 0 < α)
    (hinf : DiscreteInfSup a K L α) (hN : IsPetrovGalerkinSolution a ℓ K L u) {ustar : U}
    (hstar : ∀ v, a ustar v = ℓ v) : projection a K L hdim hα hinf ustar = u :=
  (eq_projFun hdim hα hinf ⟨hN.1, fun v hv => by rw [hN.2 v hv, hstar v]⟩).symm

/-- ([han2009theoretical], Remark 9.2.2.) Let $a$ be bounded with a constant $M \ge 0$, and let the
discrete inf–sup condition hold with a constant $\alpha > 0$. Then the Petrov–Galerkin projector
satisfies $\|P_N\| \le M / \alpha$. -/
theorem norm_projection_le (hdim : Module.finrank 𝕜 K = Module.finrank 𝕜 L) {α : ℝ}
    (hα : 0 < α) (hinf : DiscreteInfSup a K L α) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : a.IsBoundedWith M) : ‖projection a K L hdim hα hinf‖ ≤ M / α :=
  ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hM0 hα.le)
    (norm_projFun_le hdim hα hinf hM0 hM)

/-- **The Xu–Zikatanov bound** ([han2009theoretical], Remark 9.2.2, estimate (9.2.10)). Let
$K \subseteq U$ and $L \subseteq V$ be finite-dimensional with $\dim K = \dim L$ and $K \neq 0$,
let $a$ be bounded with a constant $M \ge 0$, and let the discrete inf–sup condition hold with a
constant $\alpha > 0$. Let $u$ be a Petrov–Galerkin solution, and let $u^* \in U$ satisfy
$a(u^*, v) = \ell(v)$ for all $v \in V$. Then
$$\|u^* - u\| \le \frac{M}{\alpha} \operatorname{dist}(u^*, K).$$

This improves the factor $1 + M / \alpha$ of `IsPetrovGalerkinSolution.norm_sub_le` to
$M / \alpha$. When $K \neq 0$, the constants satisfy $\alpha \le M$, so $M / \alpha \ge 1$.

The hypothesis $K \neq 0$ cannot be dropped. For $K = 0$, the projector is $0$ and the bound is
$\|u^*\| \le (M / \alpha) \|u^*\|$, which fails for $a = 0$, $M = 0$ and $\alpha = 1$, where
every other hypothesis holds.

The proof uses the identity $u^* - u = (1 - P_N)(u^* - w)$ for every $w \in K$ and Kato's
identity $\|1 - P\| = \|P\|$ for an idempotent $P \neq 0, 1$
(`ContinuousLinearMap.IsIdempotentElem.norm_one_sub_eq`). -/
theorem norm_sub_le_div_mul_infDist (hdim : Module.finrank 𝕜 K = Module.finrank 𝕜 L) {α : ℝ}
    (hα : 0 < α) (hinf : DiscreteInfSup a K L α) (hK : K ≠ ⊥) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : a.IsBoundedWith M) (hN : IsPetrovGalerkinSolution a ℓ K L u) {ustar : U}
    (hstar : ∀ v, a ustar v = ℓ v) :
    ‖ustar - u‖ ≤ M / α * Metric.infDist ustar (K : Set U) := by
  have hMa : 0 ≤ M / α := div_nonneg hM0 hα.le
  have hPu : projection a K L hdim hα hinf ustar = u :=
    projection_apply_eq_of_isPetrovGalerkinSolution hdim hα hinf hN hstar
  -- every `w ∈ K` gives the pointwise bound; the infimum follows
  have hstep : ∀ w ∈ K, ‖ustar - u‖ ≤ M / α * ‖ustar - w‖ := by
    rcases eq_or_ne (projection a K L hdim hα hinf) 1 with h1 | h1
    · have hu : ustar = u := by rw [← hPu, h1, one_apply_eq_self]
      intro w _
      rw [hu, sub_self, norm_zero]
      exact mul_nonneg hMa (norm_nonneg _)
    have h0 : projection a K L hdim hα hinf ≠ 0 := by
      intro h
      refine hK (le_antisymm (fun w hw => ?_) bot_le)
      have hw' := projection_apply_of_mem hdim hα hinf hw
      rw [h] at hw'
      simpa using hw'.symm
    have hnorm : ‖1 - projection a K L hdim hα hinf‖ = ‖projection a K L hdim hα hinf‖ :=
      ContinuousLinearMap.IsIdempotentElem.norm_one_sub_eq
        (isIdempotentElem_projection hdim hα hinf) h0 h1
    intro w hw
    have hid : ustar - u = (1 - projection a K L hdim hα hinf) (ustar - w) := by
      rw [sub_apply, one_apply_eq_self, map_sub, hPu, projection_apply_of_mem hdim hα hinf hw]
      abel
    calc ‖ustar - u‖ = ‖(1 - projection a K L hdim hα hinf) (ustar - w)‖ := by rw [hid]
      _ ≤ ‖1 - projection a K L hdim hα hinf‖ * ‖ustar - w‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖projection a K L hdim hα hinf‖ * ‖ustar - w‖ := by rw [hnorm]
      _ ≤ M / α * ‖ustar - w‖ :=
          mul_le_mul_of_nonneg_right (norm_projection_le hdim hα hinf hM0 hM) (norm_nonneg _)
  exact norm_sub_le_mul_infDist hN.1 hstep

end Projector

end IsPetrovGalerkinSolution

section Strang

/-!
### The generalized Galerkin method

This section follows [han2009theoretical], §9.3. The discrete space need not be a subspace of $V$,
and the form and the functional are themselves approximated. So the error has a consistency term in
addition to the approximation term.

The results are stated in one normed space $W$, which stands for the space $V + V_N$ of the source
with the norm $\|\cdot\|_N$ that depends on the discretization. The data are the exact solution $u$,
a form $a_N$ that is bounded on $W \times K$ and coercive on $K$, and a functional $\ell_N$ on $K$.
The Hilbert space $V$ and the original problem do not appear.
-/

section Defn

variable {W : Type*} [AddCommGroup W] [Module 𝕜 W]

/-- The **generalized Galerkin problem** ([han2009theoretical], (9.3.1)): for a bilinear map $a_N$
and a linear functional $\ell_N$ on a vector space $W$, and a subspace $K$, a vector $u_N$ is a
generalized Galerkin solution if $u_N \in K$ and $a_N(u_N, v) = \ell_N(v)$ for all $v \in K$.

Only the vector space structure of $W$ is used. The norm enters the analysis of the method
(`strang_first`), not its statement. This matters for discretizations whose trial space is not a
subspace of a normed function space: for example, a generalized Galerkin method whose form
evaluates derivatives at quadrature nodes lives on the polynomials $\mathbb{K}[X]$, which carry
no norm. -/
def IsGeneralizedGalerkinSolution (aN : W →ₗ[𝕜] W →ₗ[𝕜] 𝕜) (ℓN : W →ₗ[𝕜] 𝕜) (K : Submodule 𝕜 W)
    (uN : W) : Prop :=
  uN ∈ K ∧ ∀ v ∈ K, aN uN v = ℓN v

end Defn

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- **Strang's first lemma** ([han2009theoretical], Theorem 9.3.1, estimate (9.3.2)). Let $W$ be a
normed space over $\mathbb{K}$, let $K \subseteq W$ be a subspace, let $a_N$ be a bilinear map
on $W$ and let $\ell_N$ be a linear functional on $W$. Let $c > 0$ and $M \ge 0$, and assume
$$|a_N(w, v)| \le M \|w\| \|v\| \quad (w \in W, \ v \in K), \qquad c \|v\|^2 \le
  \operatorname{Re} a_N(v, v) \quad (v \in K).$$
Let $u_N$ be a generalized Galerkin solution on $K$, let $u \in W$, and let $\delta \ge 0$
satisfy $|a_N(u, w) - \ell_N(w)| \le \delta \|w\|$ for all $w \in K$. Then for every $v \in K$,
$$\|u - u_N\| \le \Big(1 + \frac{M}{c}\Big) \|u - v\| + \frac{\delta}{c}.$$

The first term is the approximation error, as in Céa's lemma. The second term measures how far
$u$ is from a solution of the perturbed problem. When $a_N = a$ and $\ell_N = \ell$, one can
take $\delta = 0$ and obtain Céa's lemma.

The hypotheses $M \ge 0$ and $\delta \ge 0$ do not follow from the two bounds, which hold for
any constants when $K = 0$. Without them the statement is false: $W = \mathbb{R}$, $K = 0$,
$c = 1$, $M = \delta = -1$ and $u = u_N = v = 0$ give $0 \le -1$. -/
theorem strang_first {aN : W →ₗ[𝕜] W →ₗ[𝕜] 𝕜} {ℓN : W →ₗ[𝕜] 𝕜} {K : Submodule 𝕜 W} {M c : ℝ}
    (hc : 0 < c) (hM0 : 0 ≤ M) (hM : ∀ w, ∀ v ∈ K, ‖aN w v‖ ≤ M * ‖w‖ * ‖v‖)
    (hcoer : ∀ v ∈ K, c * ‖v‖ ^ 2 ≤ RCLike.re (aN v v)) {uN : W}
    (hN : IsGeneralizedGalerkinSolution aN ℓN K uN) (u : W) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : ∀ w ∈ K, ‖aN u w - ℓN w‖ ≤ δ * ‖w‖) {v : W} (hv : v ∈ K) :
    ‖u - uN‖ ≤ (1 + M / c) * ‖u - v‖ + δ / c := by
  have hwK : uN - v ∈ K := K.sub_mem hN.1 hv
  have hkey : c * ‖uN - v‖ ^ 2
      ≤ ‖aN u (uN - v) - ℓN (uN - v)‖ + ‖aN (u - v) (uN - v)‖ := by
    have hid : aN (uN - v) (uN - v)
        = -(aN u (uN - v) - ℓN (uN - v)) + aN (u - v) (uN - v) := by
      simp only [map_sub, LinearMap.sub_apply, hN.2 uN hN.1, hN.2 v hv]
      ring
    calc c * ‖uN - v‖ ^ 2 ≤ RCLike.re (aN (uN - v) (uN - v)) := hcoer _ hwK
      _ ≤ ‖aN (uN - v) (uN - v)‖ := RCLike.re_le_norm _
      _ ≤ ‖aN u (uN - v) - ℓN (uN - v)‖ + ‖aN (u - v) (uN - v)‖ := by
          rw [hid]
          exact le_trans (norm_add_le _ _) (by rw [norm_neg])
  have hbound : c * ‖uN - v‖ ^ 2 ≤ (δ + M * ‖u - v‖) * ‖uN - v‖ := by
    have h1 := hδ _ hwK
    have h2 := hM (u - v) _ hwK
    nlinarith
  have hstep : c * ‖uN - v‖ ≤ δ + M * ‖u - v‖ := by
    rcases eq_or_lt_of_le (norm_nonneg (uN - v)) with h | h
    · rw [← h, mul_zero]
      have := mul_nonneg hM0 (norm_nonneg (u - v))
      linarith
    · refine le_of_mul_le_mul_right ?_ h
      calc c * ‖uN - v‖ * ‖uN - v‖ = c * ‖uN - v‖ ^ 2 := by ring
        _ ≤ (δ + M * ‖u - v‖) * ‖uN - v‖ := hbound
  have htri : ‖u - uN‖ ≤ ‖u - v‖ + ‖v - uN‖ := by
    simpa [dist_eq_norm] using dist_triangle u v uN
  calc ‖u - uN‖ ≤ ‖u - v‖ + ‖v - uN‖ := htri
    _ = ‖u - v‖ + ‖uN - v‖ := by rw [norm_sub_rev v uN]
    _ ≤ ‖u - v‖ + (δ + M * ‖u - v‖) / c := by
        gcongr
        rw [le_div_iff₀ hc, mul_comm]
        exact hstep
    _ = (1 + M / c) * ‖u - v‖ + δ / c := by field_simp; ring

/-- Let $K$ be a finite-dimensional subspace of a normed space $W$, let $a_N$ be a bilinear map and
$\ell_N$ a linear functional on $W$, and let $c \|v\|^2 \le \operatorname{Re} a_N(v, v)$ for all
$v \in K$ with a constant $c > 0$. Then the generalized Galerkin problem on $K$ has exactly one
solution.

The proof uses only finite dimension, not the Lax–Milgram theorem. -/
theorem existsUnique_isGeneralizedGalerkinSolution (aN : W →ₗ[𝕜] W →ₗ[𝕜] 𝕜) (ℓN : W →ₗ[𝕜] 𝕜)
    (K : Submodule 𝕜 W) [FiniteDimensional 𝕜 K] {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ v ∈ K, c * ‖v‖ ^ 2 ≤ RCLike.re (aN v v)) :
    ∃! uN, IsGeneralizedGalerkinSolution aN ℓN K uN := by
  set T : K →ₗ[𝕜] Module.Dual 𝕜 K := K.subtype.dualMap ∘ₗ (aN ∘ₗ K.subtype) with hT
  have hTinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have h := hcoer (w : W) w.2
    rw [show aN (w : W) (w : W) = T w w from rfl, hw] at h
    simp only [LinearMap.zero_apply, map_zero] at h
    have hw2 : ‖(w : W)‖ ^ 2 ≤ 0 := le_of_mul_le_mul_left (by simpa using h) hc
    have hw0 : ‖(w : W)‖ = 0 :=
      pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm hw2 (sq_nonneg _))
    exact Subtype.ext (norm_eq_zero.mp hw0)
  have hTsurj : Function.Surjective T := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hTinj
    exact (Subspace.dual_finrank_eq).symm
  obtain ⟨w, hw⟩ := hTsurj (K.subtype.dualMap ℓN)
  refine ⟨(w : W), ⟨w.2, fun v hv => ?_⟩, ?_⟩
  · exact congrArg (fun f => f ⟨v, hv⟩) hw
  · rintro y ⟨hyK, hy⟩
    have hTy : T ⟨y, hyK⟩ = T w := by
      rw [hw]
      ext z
      exact hy (z : W) z.2
    exact congrArg Subtype.val (hTinj hTy)

end Strang

section AubinNitsche

/-!
### The Aubin–Nitsche duality argument

This section bounds a Galerkin error in a norm that is weaker than the norm in which the form is
coercive. The setting is two inner product spaces $V$ and $H$ and a bounded linear map
$\iota \colon V \to H$, which stands for the embedding of the energy space into the pivot space. In
the finite element method it is the embedding $H^1(\Omega) \subseteq L^2(\Omega)$, but the results
do not need a function space.

Let $e \in V$ be an error with $a(e, v) = 0$ for all $v \in K$, as
`IsGalerkinSolution.apply_sub_eq_zero` gives for $e = u - u_N$. Let $\varphi$ solve the dual problem
$a(v, \varphi) = \langle \iota v, \iota e \rangle$ for all $v$. The test $v = e$ in the dual problem
gives $\|\iota e\|^2 = a(e, \varphi)$. Orthogonality then replaces $\varphi$ by $\varphi - w$ for
any $w \in K$, and boundedness of the form gives
$$\|\iota e\|^2 \le M \|e\| \|\varphi - w\|.$$

This is the complete argument, and `norm_map_sq_le_of_dual` states it for each $w$, with no infimum,
no supremum and no claim that $\varphi$ exists. The theorem `norm_map_le_of_dual_approx` is the form
in which it is used: if every dual solution can be approximated from $K$ to within $\delta$ times
the norm of its datum, then $\|\iota e\| \le M \delta \|e\|$. In a finite element space, $\delta$ is
of order $h$, and this is the origin of the extra power of $h$ in an $L^2$ error estimate. The bound
on $\delta$ comes from elliptic regularity theory and is not part of the argument.

The theorem is due to Aubin and to Nitsche. The presentation follows Theorem 10.4.3 and Corollary
10.4.4 of [han2009theoretical].
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- **The Aubin–Nitsche estimate.** Let $V$ and $H$ be inner product spaces, let
$\iota \colon V \to H$ be a bounded linear map, let $a$ be a form on $V$ that is bounded with
constant $M$, and let $K$ be a subspace of $V$. Let $e \in V$ satisfy $a(e, v) = 0$ for all
$v \in K$, and let $\varphi \in V$ satisfy $a(v, \varphi) = \langle \iota v, \iota e \rangle$
for all $v \in V$. Then for every $w \in K$,
$$\|\iota e\|^2 \le M \|e\| \|\varphi - w\|.$$

The test $v = e$ in the dual problem gives $\|\iota e\|^2 = a(e, \varphi)$, orthogonality
replaces $\varphi$ by $\varphi - w$, and boundedness of $a$ gives the bound. -/
theorem norm_map_sq_le_of_dual {a : SesqForm 𝕜 V} {M : ℝ} (hM : a.IsBoundedWith M)
    {K : Submodule 𝕜 V} (ι : V →L[𝕜] H) {e : V} (horth : ∀ v ∈ K, a e v = 0) {φ : V}
    (hφ : ∀ v : V, a v φ = inner 𝕜 (ι v) (ι e)) {w : V} (hw : w ∈ K) :
    ‖ι e‖ ^ 2 ≤ M * ‖e‖ * ‖φ - w‖ := by
  have hsub : a e (φ - w) = a e φ := by rw [map_sub, horth w hw, sub_zero]
  calc ‖ι e‖ ^ 2 = RCLike.re (inner 𝕜 (ι e) (ι e) : 𝕜) := by
        rw [inner_self_eq_norm_sq_to_K]; simp
    _ = RCLike.re (a e (φ - w)) := by rw [hsub, hφ e]
    _ ≤ ‖a e (φ - w)‖ := RCLike.re_le_norm _
    _ ≤ M * ‖e‖ * ‖φ - w‖ := hM _ _

/-- **The Aubin–Nitsche estimate** with a uniform bound on the approximation of the dual solutions.
Let $V$, $H$, $\iota$, $a$, $M$ and $K$ be as in `norm_map_sq_le_of_dual`, and let
$\delta \ge 0$. Assume that for every $g \in H$ there is a $\varphi \in V$ with
$a(v, \varphi) = \langle \iota v, g \rangle$ for all $v \in V$ and $\operatorname{dist}(\varphi,
K) \le \delta \|g\|$. Then every $e \in V$ with $a(e, v) = 0$ for all $v \in K$ satisfies
$$\|\iota e\| \le M \delta \|e\|.$$

The duality argument gains exactly the approximation power of the dual problem, which in a
finite element space is one power of the mesh size more than the energy-norm estimate has. -/
theorem norm_map_le_of_dual_approx {a : SesqForm 𝕜 V} {M δ : ℝ} (hM : a.IsBoundedWith M)
    (hδ : 0 ≤ δ) {K : Submodule 𝕜 V} (ι : V →L[𝕜] H) {e : V} (horth : ∀ v ∈ K, a e v = 0)
    (hdual : ∀ g : H, ∃ φ : V, (∀ v : V, a v φ = inner 𝕜 (ι v) g) ∧
      Metric.infDist φ (K : Set V) ≤ δ * ‖g‖) :
    ‖ι e‖ ≤ M * δ * ‖e‖ := by
  have hKne : (K : Set V).Nonempty := ⟨0, K.zero_mem⟩
  have hMe : 0 ≤ M * ‖e‖ := by
    rcases eq_or_lt_of_le (norm_nonneg e) with h | h
    · simp [← h]
    · nlinarith [norm_nonneg (a e e), hM e e]
  obtain ⟨φ, hφ, hφd⟩ := hdual (ι e)
  rcases eq_or_lt_of_le (norm_nonneg (ι e)) with h0 | h0
  · rw [← h0]
    linarith [mul_nonneg hδ hMe]
  · have key : ‖ι e‖ ^ 2 ≤ M * ‖e‖ * Metric.infDist φ (K : Set V) := by
      rcases eq_or_lt_of_le hMe with hMe0 | hMe0
      · have h := norm_map_sq_le_of_dual hM ι horth hφ K.zero_mem
        rw [← hMe0] at h ⊢
        simpa using h
      · rw [← div_le_iff₀' hMe0, Metric.le_infDist hKne]
        intro w hw
        rw [div_le_iff₀' hMe0, dist_eq_norm]
        exact norm_map_sq_le_of_dual hM ι horth hφ hw
    have hle : ‖ι e‖ ^ 2 ≤ M * ‖e‖ * (δ * ‖ι e‖) :=
      key.trans (mul_le_mul_of_nonneg_left hφd hMe)
    exact le_of_mul_le_mul_right (by linarith : ‖ι e‖ * ‖ι e‖ ≤ M * δ * ‖e‖ * ‖ι e‖) h0

end AubinNitsche

/-!
### Céa's and Strang's lemmas in a seminorm

The quasi-optimality arguments above need neither a topology nor an inner product. They are the
short computation $c \, q(e)^2 \le a(e, e) = a(e, u - w) \le M q(e) q(u - w)$, which holds for a
seminorm $q$ on a real vector space. Two generalizations are needed for the finite element estimates
of [quarteroni2000numerical], §12.4:

* the error is measured in a seminorm, because the natural constants of an elliptic problem on an
  interval are those of the $H^1$ seminorm and not those of the $H^1$ norm;
* boundedness and coercivity hold only on a subspace $W$, because the Poincaré inequality, which
  makes the form bounded and coercive for the seminorm, holds only on the subspace of functions that
  vanish at the boundary.

`IsGalerkinSolution.norm_sub_le` and `strang_first` are the cases of a norm on a Hilbert space.
-/

section SeminormQuasiOptimal

/-- **Céa's lemma in a seminorm, on a subspace $W$.** Let $V$ be a real vector space with a seminorm
$q$, let $B \colon V \times V \to \mathbb{R}$ be additive in its second argument, and let $W$ be
a subspace. Let $c > 0$, and assume
$$|B(u, v)| \le M q(u) q(v) \quad \text{and} \quad c \, q(v)^2 \le B(v, v) \quad \text{for all }
  u, v \in W.$$
Let $K \subseteq W$ be a subspace, let $u \in W$ and $u_h \in K$, and let $B(u - u_h, v) = 0$
for all $v \in K$. Then for every $w \in K$,
$$q(u - u_h) \le \frac{M}{c} \, q(u - w).$$

Only additivity of $B$ in its second argument is used, so $B$ is any function. No topology,
completeness or inner product appears. The condition $M \ge 0$ is not assumed, because it
follows from the two bounds at $u - w$. -/
theorem seminorm_sub_le_of_galerkin_orthogonal {V : Type*} [AddCommGroup V] [Module ℝ V]
    (q : Seminorm ℝ V) (B : V → V → ℝ) (hadd : ∀ x y z, B x (y + z) = B x y + B x z)
    {W : Submodule ℝ V} {M c : ℝ} (hc : 0 < c)
    (hM : ∀ u ∈ W, ∀ v ∈ W, |B u v| ≤ M * q u * q v) (hcoer : ∀ v ∈ W, c * q v ^ 2 ≤ B v v)
    {K : Submodule ℝ V} (hK : K ≤ W) {u uh : V} (hu : u ∈ W) (huh : uh ∈ K)
    (horth : ∀ v ∈ K, B (u - uh) v = 0) {w : V} (hw : w ∈ K) :
    q (u - uh) ≤ M / c * q (u - w) := by
  have he : u - uh ∈ W := W.sub_mem hu (hK huh)
  have hsplit : B (u - uh) (u - uh) = B (u - uh) (u - w) := by
    have h : u - uh = (u - w) + (w - uh) := by abel
    nth_rewrite 2 [h]
    rw [hadd, horth _ (K.sub_mem hw huh), add_zero]
  have key : c * q (u - uh) ^ 2 ≤ M * q (u - uh) * q (u - w) := by
    calc c * q (u - uh) ^ 2 ≤ B (u - uh) (u - uh) := hcoer _ he
      _ = B (u - uh) (u - w) := hsplit
      _ ≤ |B (u - uh) (u - w)| := le_abs_self _
      _ ≤ M * q (u - uh) * q (u - w) := hM _ he _ (W.sub_mem hu (hK hw))
  have hM0 : 0 ≤ M * q (u - w) := by
    rcases eq_or_lt_of_le (apply_nonneg q (u - w)) with h | h
    · rw [← h, mul_zero]
    · have hw' : u - w ∈ W := W.sub_mem hu (hK hw)
      have h1 : c * q (u - w) ^ 2 ≤ M * q (u - w) ^ 2 :=
        (hcoer _ hw').trans ((le_abs_self _).trans
          (by have := hM _ hw' _ hw'; rwa [mul_assoc, ← sq] at this))
      have hcM : c ≤ M := le_of_mul_le_mul_right h1 (by positivity)
      exact mul_nonneg (hc.le.trans hcM) h.le
  rcases eq_or_lt_of_le (apply_nonneg q (u - uh)) with h | h
  · rw [← h]
    exact div_mul_eq_mul_div M c (q (u - w)) ▸ div_nonneg hM0 hc.le
  · rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    nlinarith [key, apply_nonneg q (u - w)]

/-- **Strang's first lemma in a seminorm, on a subspace $W$.** Let $V$ be a real vector space with a
seminorm $q$, let $B \colon V \times V \to \mathbb{R}$ satisfy
$B(x - y, z) = B(x, z) - B(y, z)$, and let $\ell \colon V \to \mathbb{R}$ be any function. Let
$W$ be a subspace, $K \subseteq W$ a subspace, $c > 0$, $M \ge 0$ and $\delta \ge 0$, and assume
$$|B(x, v)| \le M q(x) q(v) \quad (x \in W, \ v \in K), \qquad c \, q(v)^2 \le B(v, v) \quad (v
  \in K).$$
Let $u \in W$ and $u_N \in K$ with $B(u_N, v) = \ell(v)$ and
$|B(u, v) - \ell(v)| \le \delta \, q(v)$ for all $v \in K$. Then for every $w \in K$,
$$q(u - u_N) \le \Big(1 + \frac{M}{c}\Big) q(u - w) + \frac{\delta}{c}.$$

The first term is the approximation error, as in Céa's lemma. The second term measures how far
$u$ is from a solution of the perturbed problem. The case $\delta = 0$ gives
`seminorm_sub_le_of_galerkin_orthogonal`, with a larger constant. Only additivity of $B$ in its
first argument is used, and $\ell$ can be any function. As in `strang_first`, the conditions
$M \ge 0$ and $\delta \ge 0$ must be assumed, because the two bounds hold for any constants when
$q$ is zero on $K$. -/
theorem seminorm_sub_le_of_generalizedGalerkin {V : Type*} [AddCommGroup V] [Module ℝ V]
    (q : Seminorm ℝ V) (B : V → V → ℝ) (ℓ : V → ℝ)
    (hsub : ∀ x y z, B (x - y) z = B x z - B y z) {W : Submodule ℝ V} {M c δ : ℝ} (hc : 0 < c)
    (hM0 : 0 ≤ M) (hδ0 : 0 ≤ δ) {K : Submodule ℝ V} (hK : K ≤ W)
    (hM : ∀ x ∈ W, ∀ v ∈ K, |B x v| ≤ M * q x * q v) (hcoer : ∀ v ∈ K, c * q v ^ 2 ≤ B v v)
    {u uN : V} (hu : u ∈ W) (huN : uN ∈ K) (hgal : ∀ v ∈ K, B uN v = ℓ v)
    (hδ : ∀ v ∈ K, |B u v - ℓ v| ≤ δ * q v) {w : V} (hw : w ∈ K) :
    q (u - uN) ≤ (1 + M / c) * q (u - w) + δ / c := by
  have heK : uN - w ∈ K := K.sub_mem huN hw
  have hid : B (uN - w) (uN - w) =
      -(B u (uN - w) - ℓ (uN - w)) + B (u - w) (uN - w) := by
    rw [hsub, hsub, hgal _ heK]; ring
  have key : c * q (uN - w) ^ 2 ≤ (δ + M * q (u - w)) * q (uN - w) := by
    have h1 := hδ _ heK
    have h2 := hM _ (W.sub_mem hu (hK hw)) _ heK
    calc c * q (uN - w) ^ 2 ≤ B (uN - w) (uN - w) := hcoer _ heK
      _ ≤ |B u (uN - w) - ℓ (uN - w)| + |B (u - w) (uN - w)| := by
          rw [hid]
          exact (le_abs_self _).trans ((abs_add_le _ _).trans (by rw [abs_neg]))
      _ ≤ (δ + M * q (u - w)) * q (uN - w) := by nlinarith
  have hstep : c * q (uN - w) ≤ δ + M * q (u - w) := by
    rcases eq_or_lt_of_le (apply_nonneg q (uN - w)) with h | h
    · rw [← h, mul_zero]
      have := mul_nonneg hM0 (apply_nonneg q (u - w))
      linarith
    · exact le_of_mul_le_mul_right (by nlinarith) h
  have htri : q (u - uN) ≤ q (u - w) + q (uN - w) := by
    have h : u - uN = (u - w) - (uN - w) := by abel
    rw [h]
    exact (map_sub_le_add q _ _)
  have hdiv : q (uN - w) ≤ (δ + M * q (u - w)) / c := by
    rw [le_div_iff₀ hc, mul_comm]
    exact hstep
  calc q (u - uN) ≤ q (u - w) + q (uN - w) := htri
    _ ≤ q (u - w) + (δ + M * q (u - w)) / c := by gcongr
    _ = (1 + M / c) * q (u - w) + δ / c := by field_simp; ring

end SeminormQuasiOptimal

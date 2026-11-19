/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Numlib.Approximation.CompositeQuadrature
import Numlib.Approximation.Interpolation
import Numlib.Approximation.PiecewiseLinearL2
import Numlib.IntegralEquations.Basic
import NumlibSurface.AtkinsonHan.Chapter12.Section01

/-!
# Atkinson and Han, Section 12.3: Iterated projection methods

This module formalizes Section 12.3 of [han2009theoretical]. Let $u_n$ be a projection solution of
$(\lambda - K) u = f$. One step of the fixed-point iteration gives the iterated projection solution
$\hat u_n = (f + K u_n)/\lambda$ of (12.3.1), as observed by Sloan. Its error satisfies $(\lambda -
K P_n)(u - \hat u_n) = K (I - P_n) u$, so the factor $I - P_n$ appears inside $K$, and $\hat u_n$
converges faster than $u_n$, whatever the size of $\|K\|$. Jacobson's identity (Lemma 12.3.1) shows
that $\lambda - K P_n$ is invertible whenever $\lambda - P_n K$ is, with a uniform bound on the
inverse.

The module then proves two instances. For collocation with continuous piecewise quadratic functions
on a uniform mesh of width $h$ (§12.3.2), $\|u - u_n\|_\infty = O(h^3)$ but
$\|u - \hat u_n\|_\infty = O(h^4)$, and $u_n$ is also $O(h^4)$ accurate at the mesh points (Theorem
12.3.3). For the Galerkin method with discontinuous piecewise linear functions applied to
$50 u - K u = f$ with the kernel $e^{xy}$ (Example 12.3.2), $\|u - u_n\| = O(h^2)$ and
$\|u - \hat u_n\| = O(h^4)$. The proofs specialize `Numlib.IntegralEquations.SecondKind`,
`Numlib.Approximation.Interpolation`, `Numlib.Approximation.CompositeQuadrature` and
`Numlib.Approximation.PiecewiseLinearL2`.

## Main definitions

* Equation (12.3.1), `AtkinsonHan.Chapter12.iteratedSolution`: the iterated projection solution
  $\hat u_n = (f + K u_n)/\lambda$.
* Equation (12.3.24), `AtkinsonHan.Chapter12.quadInterpCLM`: interpolation by continuous piecewise
  quadratic functions on a uniform mesh.
* Equation (12.3.18), `AtkinsonHan.Chapter12.expKernel` and `AtkinsonHan.Chapter12.expKernelCLM`:
  the kernel $e^{xy}$ on $[0, 1]^2$ and its integral operator on $L^2(0, 1)$.
* Example 12.3.2, `AtkinsonHan.Chapter12.discGalerkinProj`: the orthogonal projection onto the
  discontinuous piecewise linear functions of the uniform mesh of width $1/n$.

## Main results

* Equation (12.3.2), `AtkinsonHan.Chapter12.equation_12_3_2`: $P \hat u_n = u_n$.
* Equation (12.3.3), `AtkinsonHan.Chapter12.equation_12_3_3`: $(\lambda - K P) \hat u_n = f$.
* Lemma 12.3.1, `AtkinsonHan.Chapter12.lemma_12_3_1`: $\lambda - A B$ is invertible if and only if
  $\lambda - B A$ is, and then $(\lambda - B A)^{-1} = \lambda^{-1} [I + B (\lambda - A B)^{-1} A]$,
  which is (12.3.9).
* Lemma 12.3.1, `AtkinsonHan.Chapter12.lemma_12_3_1_projection`: the case $A = P$, $B = K$, with a
  bound on $\|(\lambda - K P)^{-1}\|$.
* Equation (12.3.11), `AtkinsonHan.Chapter12.equation_12_3_11`:
  $(\lambda - K P)(u - \hat u_n) = K (I - P) u$ and $\|u - \hat u_n\| \le \|(\lambda - K P)^{-1}\|
  \|K (I - P)\| \|u - P u\|$.
* Equation (12.3.27), `AtkinsonHan.Chapter12.norm_sub_quadInterpCLM_le`: $\|u - P_n u\|_\infty \le
  (\sqrt{3}/27) h^3 \|u'''\|_\infty$.
* Equation (12.3.31), `AtkinsonHan.Chapter12.norm_kernelCLM_sub_quadInterpCLM_le`:
  $\|K (I - P_n) u\|_\infty = O(h^4)$.
* Theorem 12.3.3, `AtkinsonHan.Chapter12.theorem_12_3_3`: the bounds (12.3.32), (12.3.33) and
  (12.3.34) for iterated piecewise quadratic collocation.
* Example 12.3.2, `AtkinsonHan.Chapter12.example_12_3_2`: the rates (12.3.19) and (12.3.20) of the
  Galerkin and the iterated Galerkin solutions.

## Conventions

* The scalar $\lambda$ of the source is `μ`, because `λ` is the Lean lambda binder.
* In the abstract results the sequence of projections $P_n$ of the source is one bounded idempotent
  operator `P`.
* The uniform mesh of §12.3.2 has $n = 2(p + 1)$ subintervals of width $h = (b - a)/n$,
  `AtkinsonHan.Chapter12.quadMesh a b p`, and $p + 1$ panels $[x_{2k}, x_{2k+2}]$. The Lean
  statements are indexed by $p$.

## Implementation notes

* The route to (12.3.31) differs from the proof in the source, which differentiates a Newton divided
  difference in $y$; `Numlib.Approximation.DividedDifference` has no derivative rule. Instead the
  kernel is split on each panel, and the main term is the error of Simpson's rule on the panel. This
  route needs only a Lipschitz condition on the kernel in $y$.
* In Example 12.3.2 the hypothesis $\|K - P_n K\| \to 0$ of Theorem 12.1.2 is the explicit bound
  $\|K - P_n K\| \le e h^2/8$, in place of the compactness argument (12.3.15) of the source. The
  source states the estimate $\|(I - P_n) K^*\| = O(h^2)$ without proof. The operator $50 - K$ is
  invertible by the Neumann series, because $\|K\| \le e < 50$.
* `AtkinsonHan.Chapter12.expKernel` is defined here, in the first section that uses it, and Section
  12.4 uses it again.

## Deviations from the source

* **Equations (12.3.2) and (12.3.3)** (generalization). The iterated projection identities hold
  for any bounded idempotent projection, including those with infinite-dimensional range.
* **Lemma 12.3.1** (generalization). The source states the lemma on a Banach space. Completeness is
  not used, and the statement holds on every normed space. See `AtkinsonHan.Chapter12.lemma_12_3_1`.
* **Equation (12.3.11)** (generalization). The source derives the bound for an orthogonal projection
  on a Hilbert space. Only $P^2 = P$ is used, and the statement holds for every bounded idempotent
  operator on a normed space. See `AtkinsonHan.Chapter12.equation_12_3_11`.
* **Equation (12.3.31) and Theorem 12.3.3** (generalization). The source assumes that the kernel is
  continuously differentiable in $y$. The statements assume only that it is Lipschitz in $y$, which
  a $C^1$ kernel on the compact square is. See
  `AtkinsonHan.Chapter12.norm_kernelCLM_sub_quadInterpCLM_le` and
  `AtkinsonHan.Chapter12.theorem_12_3_3`.

## Not formalized

* **§12.3.2, the concrete computations and the linear system for the iterated collocation
  solution.**
* **Table 12.2 of Example 12.3.2.** It contains measured errors for $n = 2, 4, 8$. The rates that it
  confirms are `AtkinsonHan.Chapter12.example_12_3_2`.
* **The dimension $d_n = 2n$ of the trial space in Example 12.3.2.** It is a remark on the size of
  the linear system, and (12.3.19) and (12.3.20) do not use it.
-/

open Filter Topology

namespace AtkinsonHan.Chapter12

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-! ### The iterated projection solution -/

/-- **Equation (12.3.1)** of [han2009theoretical]. Let $K$ be a bounded operator, $\lambda$ a scalar
and $f, u_n$ vectors. The **iterated projection solution** is $$\hat u_n = \frac{1}{\lambda}
(f + K u_n),$$ one step of the fixed-point iteration $u \mapsto (f + K u)/\lambda$ applied to
$u_n$.

This is `SecondKind.iterated`. It is defined for every $u_n$; the identities
`AtkinsonHan.Chapter12.equation_12_3_2` and `AtkinsonHan.Chapter12.equation_12_3_3` use that
$u_n$ is a projection solution (12.1.18). -/
noncomputable abbrev iteratedSolution (μ : 𝕜) (K : X →L[𝕜] X) (f un : X) : X :=
  SecondKind.iterated μ K f un

/-- **Equation (12.3.2)** of [han2009theoretical]. Let $\lambda \neq 0$, let $K$ and $P$ be bounded
operators with $P^2 = P$, and let $u_n$ be a projection solution of $(\lambda - K) u = f$. Then
the iterated solution satisfies $$P \hat u_n = u_n.$$

**Reading.** Holds for any bounded idempotent instead of finite-dimensional projections.
-/
theorem equation_12_3_2 {μ : 𝕜} (hμ : μ ≠ 0) {K P : X →L[𝕜] X} (hP : IsIdempotentElem P)
    {f un : X} (hun : IsProjectionSolution μ K P f un) :
    P (iteratedSolution μ K f un) = un :=
  SecondKind.apply_iterated hμ hP hun

/-- **Equation (12.3.3)** of [han2009theoretical]. Let $\lambda \neq 0$, let $K$ and $P$ be bounded
operators with $P^2 = P$, and let $u_n$ be a projection solution of $(\lambda - K) u = f$. Then
the iterated solution satisfies $$(\lambda - K P) \hat u_n = f.$$

This is the counterpart, under Jacobson's identity `AtkinsonHan.Chapter12.lemma_12_3_1`, of the
projection equations $(\lambda - P K) u_n = P f$.

**Reading.** Iterated equation for any bounded idempotent instead of finite-dimensional projections.
-/
theorem equation_12_3_3 {μ : 𝕜} (hμ : μ ≠ 0) {K P : X →L[𝕜] X} (hP : IsIdempotentElem P)
    {f un : X} (hun : IsProjectionSolution μ K P f un) :
    (μ • 1 - K ∘L P : X →L[𝕜] X) (iteratedSolution μ K f un) = f :=
  SecondKind.smul_sub_comp_iterated hμ hP hun

/-! ### Jacobson's identity -/

/-- **Lemma 12.3.1** of [han2009theoretical] (Jacobson's identity). Let $A$ and $B$ be bounded
operators on a normed space and let $\lambda \neq 0$. Then $\lambda - A B$ has a bounded inverse
if and only if $\lambda - B A$ has one. Moreover, if $\lambda - A B$ is invertible, then
$\lambda - B A$ is invertible with $$(\lambda - B A)^{-1} = \frac{1}{\lambda} \left[I + B
(\lambda - A B)^{-1} A\right],$$ which is (12.3.9).

**Generalization.** The source states the lemma on a Banach space. The proof checks the formula
by multiplying out, so it uses neither completeness nor compactness. -/
theorem lemma_12_3_1 {μ : 𝕜} (hμ : μ ≠ 0) (A B : X →L[𝕜] X) :
    (IsUnit (μ • 1 - A ∘L B : X →L[𝕜] X) ↔ IsUnit (μ • 1 - B ∘L A : X →L[𝕜] X)) ∧
      ∀ e : X ≃L[𝕜] X, (e : X →L[𝕜] X) = μ • 1 - A ∘L B →
        ∃ e' : X ≃L[𝕜] X, (e' : X →L[𝕜] X) = μ • 1 - B ∘L A ∧
          (e'.symm : X →L[𝕜] X) = μ⁻¹ • (1 + B ∘L ((e.symm : X →L[𝕜] X) ∘L A)) :=
  ⟨SecondKind.isUnit_smul_sub_comp_comm hμ A B,
    fun e he => SecondKind.exists_equiv_smul_sub_comp_comm hμ e he⟩

/-- **Lemma 12.3.1** of [han2009theoretical], applied to the projection method with $A = P$ and
$B = K$. Let $\lambda \neq 0$, let $K$ and $P$ be bounded operators on a normed space, and let
$\lambda - P K$ be invertible. Then $\lambda - K P$ is invertible, $$(\lambda - K P)^{-1} =
\frac{1}{\lambda} \left[I + K (\lambda - P K)^{-1} P\right], \qquad \|(\lambda - K P)^{-1}\| \le
\frac{1 + \|K\| \|(\lambda - P K)^{-1}\| \|P\|}{|\lambda|}.$$

A uniform bound on $\|(\lambda - P_n K)^{-1}\|$, which `AtkinsonHan.Chapter12.theorem_12_1_2`
supplies, therefore gives a uniform bound on $\|(\lambda - K P_n)^{-1}\|$. This makes
`AtkinsonHan.Chapter12.equation_12_3_11` an error estimate.

**Reading.** Inverse identity for bounded maps on general normed spaces.
-/
theorem lemma_12_3_1_projection {μ : 𝕜} (hμ : μ ≠ 0) (K P : X →L[𝕜] X) {e' : X ≃L[𝕜] X}
    (he' : (e' : X →L[𝕜] X) = μ • 1 - P ∘L K) :
    ∃ e'' : X ≃L[𝕜] X, (e'' : X →L[𝕜] X) = μ • 1 - K ∘L P ∧
      (e''.symm : X →L[𝕜] X) = μ⁻¹ • (1 + K ∘L ((e'.symm : X →L[𝕜] X) ∘L P)) ∧
      ‖(e''.symm : X →L[𝕜] X)‖ ≤
        ‖μ‖⁻¹ * (1 + ‖K‖ * (‖(e'.symm : X →L[𝕜] X)‖ * ‖P‖)) := by
  obtain ⟨e'', he''coe, he''symm⟩ := SecondKind.exists_equiv_smul_sub_comp_comm hμ e' he'
  refine ⟨e'', he''coe, he''symm, ?_⟩
  rw [he''symm, norm_smul, norm_inv]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_add_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le ?_)
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))

/-! ### The error of the iterated solution -/

/-- **Equation (12.3.11)** of [han2009theoretical] (Sloan's superconvergence). Let $\lambda \neq 0$,
let $K$ and $P$ be bounded operators on a normed space with $P^2 = P$, and let $\lambda - K P$
be invertible. If $(\lambda - K) u = f$ and $u_n$ is a projection solution, then $$(\lambda - K
P)(u - \hat u_n) = K (I - P) u, \qquad \|u - \hat u_n\| \le \|(\lambda - K P)^{-1}\| \, \|K (I -
P)\| \, \|u - P u\|.$$

**Generalization.** The source works on a Hilbert space with an orthogonal projection $P$. The
proof uses only $(I - P)^2 = I - P$.

Because $I - P$ is idempotent, it can be inserted twice, and the bound is $\|K (I - P)\|$ times
the approximation error $\|u - P u\|$. This is better than the bound $\|u - u_n\| \le |\lambda|
\|(\lambda - P K)^{-1}\| \|u - P u\|$ of (12.1.24) by the factor $\|K (I - P_n)\|$, which tends
to $0$ for a compact $K$. -/
theorem equation_12_3_11 {μ : 𝕜} (hμ : μ ≠ 0) {K P : X →L[𝕜] X} (hP : IsIdempotentElem P)
    {e'' : X ≃L[𝕜] X} (he'' : (e'' : X →L[𝕜] X) = μ • 1 - K ∘L P) {f u un : X}
    (hu : (μ • 1 - K : X →L[𝕜] X) u = f) (hun : IsProjectionSolution μ K P f un) :
    (μ • 1 - K ∘L P : X →L[𝕜] X) (u - iteratedSolution μ K f un) = K (u - P u) ∧
      ‖u - iteratedSolution μ K f un‖ ≤
        ‖(e''.symm : X →L[𝕜] X)‖ * ‖K ∘L (1 - P)‖ * ‖u - P u‖ := by
  have hkey : (μ • 1 - K ∘L P : X →L[𝕜] X) (u - iteratedSolution μ K f un) = K (u - P u) :=
    SecondKind.iterated_error_eq hμ hP hu hun
  refine ⟨hkey, ?_⟩
  -- `I - P` is idempotent, so the error is `K (I - P)` applied to the approximation error
  have hPP : P (P u) = P u := DFunLike.congr_fun hP u
  have hins : K (u - P u) = (K ∘L (1 - P) : X →L[𝕜] X) (u - P u) := by
    simp only [ContinuousLinearMap.comp_apply, sub_apply, one_apply_eq_self, map_sub, hPP,
      sub_self, map_zero, sub_zero]
  have herr : u - iteratedSolution μ K f un = e''.symm ((K ∘L (1 - P) : X →L[𝕜] X) (u - P u)) := by
    rw [← hins, ← hkey, ← he'', ContinuousLinearEquiv.coe_coe, e''.symm_apply_apply]
  rw [herr]
  calc ‖e''.symm ((K ∘L (1 - P) : X →L[𝕜] X) (u - P u))‖
      ≤ ‖(e''.symm : X →L[𝕜] X)‖ * ‖(K ∘L (1 - P) : X →L[𝕜] X) (u - P u)‖ :=
        ContinuousLinearMap.le_opNorm (e''.symm : X →L[𝕜] X) _
    _ ≤ ‖(e''.symm : X →L[𝕜] X)‖ * (‖K ∘L (1 - P)‖ * ‖u - P u‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ = ‖(e''.symm : X →L[𝕜] X)‖ * ‖K ∘L (1 - P)‖ * ‖u - P u‖ := by ring

/-! ### The piecewise quadratic interpolatory projection -/

section PiecewiseQuadratic

variable {a b : ℝ}

/-- The $j$-th point $a + j (b - a)/n$ of the uniform mesh of $[a, b]$ with $n$ subintervals, as a
point of $[a, b]$. The value is projected onto $[a, b]$ by `Set.projIcc`. For $n = 0$ the step
$(b - a)/0$ is $0$ in Lean, so every point is $a$. -/
noncomputable def meshPoint (hab : a ≤ b) (n j : ℕ) : Set.Icc a b :=
  Set.projIcc a b hab (a + (j : ℝ) * ((b - a) / n))

/-- For $n > 0$ and $j \le n$, the mesh point is $a + j (b - a)/n$, without clamping. -/
theorem coe_meshPoint (hab : a ≤ b) {n j : ℕ} (hn : 0 < n) (hj : j ≤ n) :
    (meshPoint hab n j : ℝ) = a + (j : ℝ) * ((b - a) / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hba : (0 : ℝ) ≤ b - a := sub_nonneg.mpr hab
  have hjn : (j : ℝ) ≤ n := by exact_mod_cast hj
  have hnonneg : (0 : ℝ) ≤ (j : ℝ) * ((b - a) / n) := by positivity
  have hcan : (n : ℝ) * ((b - a) / n) = b - a := by field_simp
  have hle : (j : ℝ) * ((b - a) / n) ≤ b - a := by
    have h1 : (j : ℝ) * ((b - a) / n) ≤ (n : ℝ) * ((b - a) / n) :=
      mul_le_mul_of_nonneg_right hjn (by positivity)
    rwa [hcan] at h1
  rw [meshPoint, Set.coe_projIcc, min_eq_right (by linarith), max_eq_right (by linarith)]

/-- For $a < b$, $n > 0$ and $j, k \le n$, equal mesh points have equal indices. -/
theorem meshPoint_inj (hab : a < b) {n j k : ℕ} (hn : 0 < n) (hj : j ≤ n) (hk : k ≤ n)
    (h : (meshPoint hab.le n j : ℝ) = (meshPoint hab.le n k : ℝ)) : j = k := by
  have hδ : (0 : ℝ) < (b - a) / n := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact div_pos (sub_pos.mpr hab) this
  rw [coe_meshPoint hab.le hn hj, coe_meshPoint hab.le hn hk] at h
  have hmul : (j : ℝ) * ((b - a) / n) = (k : ℝ) * ((b - a) / n) := by linarith
  exact_mod_cast mul_right_cancel₀ (ne_of_gt hδ) hmul

/-- The **mesh size** $h = (b - a)/n$ of the piecewise quadratic method of §12.3.2, with
$n = 2(p + 1)$ subintervals and $p + 1$ panels. -/
noncomputable def quadMesh (a b : ℝ) (p : ℕ) : ℝ := (b - a) / (2 * (p + 1))

/-- For $a < b$ the mesh size $h$ is positive. -/
theorem quadMesh_pos (hab : a < b) (p : ℕ) : 0 < quadMesh a b p :=
  div_pos (sub_pos.mpr hab) (by positivity)

/-- The breakpoint $x_{2k} = a + 2 k h$ of the piecewise quadratic trial space of §12.3.2. The
$p + 1$ panels are $[x_0, x_2], \dots, [x_{n-2}, x_n]$ with $n = 2(p + 1)$. -/
noncomputable def quadBreak (hab : a ≤ b) (p k : ℕ) : Set.Icc a b :=
  meshPoint hab (2 * (p + 1)) (2 * k)

/-- The three interpolation nodes $x_{2k}, x_{2k+1}, x_{2k+2}$ of the $k$-th panel. -/
noncomputable def quadNode (hab : a ≤ b) (p k : ℕ) (i : Fin 3) : Set.Icc a b :=
  meshPoint hab (2 * (p + 1)) (2 * k + (i : ℕ))

/-- For $k \le p + 1$ the breakpoint $x_{2k}$ is $a + 2 k h$. -/
theorem coe_quadBreak (hab : a ≤ b) {p k : ℕ} (hk : k ≤ p + 1) :
    (quadBreak hab p k : ℝ) = a + 2 * (k : ℝ) * quadMesh a b p := by
  rw [quadBreak, coe_meshPoint hab (by omega) (by omega), quadMesh]
  push_cast
  ring

/-- For $k \le p$ and $i \in \{0, 1, 2\}$ the node $x_{2k+i}$ is $a + (2k + i) h$. -/
theorem coe_quadNode (hab : a ≤ b) {p k : ℕ} (hk : k ≤ p) (i : Fin 3) :
    (quadNode hab p k i : ℝ) = a + (2 * (k : ℝ) + ((i : ℕ) : ℝ)) * quadMesh a b p := by
  have hi := i.isLt
  rw [quadNode, coe_meshPoint hab (by omega) (by omega), quadMesh]
  push_cast
  ring

/-- For $a < b$, the breakpoints and nodes of the piecewise quadratic method form a panel node
system (`IsPanelNodes`): the panels $[x_{2k}, x_{2k+2}]$ increase from $a$ to $b$, and each
carries the three nodes $x_{2k}, x_{2k+1}, x_{2k+2}$, of which the outer two are its endpoints.
This makes the interpolant continuous. -/
theorem isPanelNodes_quad (hab : a < b) (p : ℕ) :
    IsPanelNodes p 2 (quadBreak hab.le p) (quadNode hab.le p) := by
  have hδ : 0 < quadMesh a b p := quadMesh_pos hab p
  refine ⟨fun k hk => ?_, ?_, ?_, fun k hk i => ?_, fun k hk => ?_, fun k hk => ?_,
    fun k hk => ?_⟩
  · rw [coe_quadBreak hab.le (by omega), coe_quadBreak hab.le (by omega)]
    push_cast
    linarith
  · rw [coe_quadBreak hab.le (by omega)]
    norm_num
  · rw [coe_quadBreak hab.le (le_refl (p + 1)), quadMesh]
    push_cast
    field_simp
    ring
  · have hi := i.isLt
    have hi0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
    have hi2 : ((i : ℕ) : ℝ) ≤ 2 := by exact_mod_cast Nat.lt_succ_iff.mp hi
    rw [coe_quadNode hab.le hk i, coe_quadBreak hab.le (by omega),
      coe_quadBreak hab.le (by omega)]
    push_cast
    constructor <;> nlinarith
  · intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have hidx : 2 * k + (i : ℕ) = 2 * k + (j : ℕ) :=
      meshPoint_inj hab (by omega) (by omega) (by omega) hij
    exact Fin.ext (by omega)
  · simp only [quadNode, quadBreak, Fin.val_zero, Nat.add_zero]
  · have hidx : 2 * k + ((Fin.last 2 : Fin 3) : ℕ) = 2 * (k + 1) := by
      simp only [Fin.val_last]
      omega
    rw [quadNode, quadBreak, hidx]

/-- For $a < b$ and $k \le p$, the panel $[x_{2k}, x_{2k+2}]$ has length $2h$. -/
theorem quadBreak_sub (hab : a < b) {p k : ℕ} (hk : k ≤ p) :
    (quadBreak hab.le p (k + 1) : ℝ) - (quadBreak hab.le p k : ℝ) = 2 * quadMesh a b p := by
  rw [coe_quadBreak hab.le (by omega), coe_quadBreak hab.le (by omega)]
  push_cast
  ring

/-- For $a < b$ and $k \le p$, two distinct nodes of the $k$-th panel are at distance at least $h$.
-/
theorem quadNode_sep (hab : a < b) {p k : ℕ} (hk : k ≤ p) (i i' : Fin 3) (hii : i ≠ i') :
    quadMesh a b p ≤ |((quadNode hab.le p k i : ℝ)) - ((quadNode hab.le p k i' : ℝ))| := by
  have hδ : 0 < quadMesh a b p := quadMesh_pos hab p
  have hne : ((i : ℕ) : ℝ) ≠ ((i' : ℕ) : ℝ) := by
    exact_mod_cast fun hc => hii (Fin.ext (by exact_mod_cast hc))
  have hone : (1 : ℝ) ≤ |((i : ℕ) : ℝ) - ((i' : ℕ) : ℝ)| := by
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · rw [abs_of_nonpos (by linarith)]
      have : ((i : ℕ) : ℝ) + 1 ≤ ((i' : ℕ) : ℝ) := by
        have : (i : ℕ) < (i' : ℕ) := by exact_mod_cast hlt
        exact_mod_cast this
      linarith
    · rw [abs_of_nonneg (by linarith)]
      have : ((i' : ℕ) : ℝ) + 1 ≤ ((i : ℕ) : ℝ) := by
        have : (i' : ℕ) < (i : ℕ) := by exact_mod_cast hlt
        exact_mod_cast this
      linarith
  rw [coe_quadNode hab.le hk i, coe_quadNode hab.le hk i']
  have hrw : a + (2 * (k : ℝ) + ((i : ℕ) : ℝ)) * quadMesh a b p
      - (a + (2 * (k : ℝ) + ((i' : ℕ) : ℝ)) * quadMesh a b p)
      = (((i : ℕ) : ℝ) - ((i' : ℕ) : ℝ)) * quadMesh a b p := by ring
  rw [hrw, abs_mul, abs_of_pos hδ]
  nlinarith

/-- For $a < b$, the nodes of the piecewise quadratic method have the local Lebesgue bound $12$ on
every panel (`IsPanelLebesgueBound`), uniformly in the mesh. This is the bound $(m + 1)(D/d)^m$
of `isPanelLebesgueBound_of_sep` with $m = 2$, $D = 2h$ and $d = h$. -/
theorem isPanelLebesgueBound_quad (hab : a < b) (p : ℕ) :
    IsPanelLebesgueBound p 2 (quadBreak hab.le p) (quadNode hab.le p) 12 := by
  have hδ : 0 < quadMesh a b p := quadMesh_pos hab p
  have h := isPanelLebesgueBound_of_sep (isPanelNodes_quad hab p) (d := fun _ => quadMesh a b p)
    (ρ := 2) (fun _ _ => hδ) (fun k hk => le_of_eq (by rw [quadBreak_sub hab hk]))
    (fun k hk i i' hii => quadNode_sep hab hk i i' hii)
  have hval : ((2 : ℕ) + 1 : ℝ) * (2 : ℝ) ^ 2 = 12 := by norm_num
  rwa [hval] at h

/-- **Equation (12.3.24)** of [han2009theoretical]. The **piecewise quadratic interpolatory
projection** $P_n$ is the bounded operator on $C[a, b]$ that maps $u$ to the continuous function
that is quadratic on each panel $[x_{2k}, x_{2k+2}]$ and interpolates $u$ at the $n + 1$ mesh
points, with $n = 2(p + 1)$.

It is `piecewisePolyInterpCLM` with degree $2$ on the uniform mesh. -/
noncomputable def quadInterpCLM (hab : a ≤ b) (p : ℕ) :
    C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ) :=
  piecewisePolyInterpCLM p 2 (quadBreak hab p) (quadNode hab p)

/-- For $a < b$ the piecewise quadratic interpolation is a projection: $P_n^2 = P_n$. -/
theorem isIdempotentElem_quadInterpCLM (hab : a < b) (p : ℕ) :
    IsIdempotentElem (quadInterpCLM hab.le p) :=
  isIdempotentElem_piecewisePolyInterpCLM (isPanelNodes_quad hab p)

/-- For $a < b$ the piecewise quadratic interpolation satisfies $\|P_n\| \le 12$, uniformly in the
mesh. -/
theorem norm_quadInterpCLM_le (hab : a < b) (p : ℕ) : ‖quadInterpCLM hab.le p‖ ≤ 12 :=
  norm_piecewisePolyInterpCLM_le (isPanelNodes_quad hab p) (isPanelLebesgueBound_quad hab p)

/-- For $a < b$, $P_n u$ and $u$ agree at each of the $n + 1$ mesh points $x_j$, $j \le n$. -/
theorem quadInterpCLM_apply_meshPoint (hab : a < b) (p : ℕ) (g : C(Set.Icc a b, ℝ)) {j : ℕ}
    (hj : j ≤ 2 * (p + 1)) :
    quadInterpCLM hab.le p g (meshPoint hab.le (2 * (p + 1)) j)
      = g (meshPoint hab.le (2 * (p + 1)) j) := by
  obtain ⟨k, i, hk, hki⟩ : ∃ (k : ℕ) (i : Fin 3), k ≤ p ∧ j = 2 * k + (i : ℕ) := by
    rcases Nat.lt_or_ge j (2 * p + 2) with hlt | hge
    · refine ⟨j / 2, ⟨j % 2, by omega⟩, by omega, ?_⟩
      change j = 2 * (j / 2) + j % 2
      omega
    · refine ⟨p, ⟨2, by norm_num⟩, le_rfl, ?_⟩
      change j = 2 * p + 2
      omega
  subst hki
  exact piecewisePolyInterpCLM_apply_node (isPanelNodes_quad hab p) g hk i

open Filter Topology in
/-- For $a < b$ and every $v \in C[a, b]$, $P_n v \to v$ in the uniform norm as $p \to \infty$. With
Lemma 12.1.4 this gives $\|K - P_n K\| \to 0$ for a compact $K$. -/
theorem tendsto_quadInterpCLM (hab : a < b) (v : C(Set.Icc a b, ℝ)) :
    Tendsto (fun p => quadInterpCLM hab.le p v) atTop (𝓝 v) := by
  refine tendsto_piecewisePolyInterpCLM (hs := fun p => 2 * quadMesh a b p) (Λ := 12)
    (fun p => isPanelNodes_quad hab p) (fun p => isPanelLebesgueBound_quad hab p)
    (fun p k hk => le_of_eq (quadBreak_sub hab hk)) ?_ v
  have hlim : Tendsto (fun p : ℕ => (b - a) / (2 * ((p : ℝ) + 1))) atTop (𝓝 0) := by
    apply Filter.Tendsto.div_atTop (tendsto_const_nhds (x := b - a))
    exact Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop |>.const_mul_atTop
      (by norm_num)
  have h2 : Tendsto (fun p : ℕ => 2 * quadMesh a b p) atTop (𝓝 0) := by
    have := hlim.const_mul (2 : ℝ)
    simpa [quadMesh] using this
  exact h2

end PiecewiseQuadratic

/-! ### The interpolation error (12.3.27) and the smoothing estimate (12.3.31) -/

section QuadraticError

open IntegralOperator MeasureTheory

variable {a b : ℝ}

/-- For $a < b$, $k \le p$ and $s$ in the panel $[x_{2k}, x_{2k+2}]$, the nodal polynomial of the
panel satisfies $\left|\prod_{i=0}^{2} (s - x_{2k+i})\right| \le 2\sqrt{3} h^3 / 9$. -/
theorem abs_prod_quadNode_le (hab : a < b) {p k : ℕ} (hk : k ≤ p) {s : ℝ}
    (hs : s ∈ Set.Icc ((quadBreak hab.le p k : ℝ)) ((quadBreak hab.le p (k + 1) : ℝ))) :
    |∏ i, (s - ((quadNode hab.le p k i : ℝ)))| ≤ 2 * Real.sqrt 3 * quadMesh a b p ^ 3 / 9 := by
  have hδ : 0 < quadMesh a b p := quadMesh_pos hab p
  have h0 : ((quadNode hab.le p k 0 : ℝ)) = a + 2 * (k : ℝ) * quadMesh a b p := by
    rw [coe_quadNode hab.le hk]
    norm_num
  have h1 : ((quadNode hab.le p k 1 : ℝ)) = a + (2 * (k : ℝ) + 1) * quadMesh a b p := by
    rw [coe_quadNode hab.le hk]
    norm_num
  have h2 : ((quadNode hab.le p k 2 : ℝ)) = a + (2 * (k : ℝ) + 2) * quadMesh a b p := by
    rw [coe_quadNode hab.le hk]
    norm_num
  rw [coe_quadBreak hab.le (by omega), coe_quadBreak hab.le (by omega)] at hs
  obtain ⟨hs1, hs2⟩ := hs
  push_cast at hs1 hs2
  set w : ℝ := s - (a + (2 * (k : ℝ) + 1) * quadMesh a b p) with hw
  have hwabs : |w| ≤ quadMesh a b p := by
    rw [abs_le, hw]
    constructor <;> nlinarith
  have hrw : ∏ i, (s - ((quadNode hab.le p k i : ℝ)))
      = (w + quadMesh a b p) * w * (w - quadMesh a b p) := by
    rw [Fin.prod_univ_three, h0, h1, h2, hw]
    ring
  rw [hrw]
  exact abs_add_mul_mul_sub_le hδ hwabs

/-- **Equation (12.3.27)** of [han2009theoretical]. Let $a < b$ and let $u \in C[a, b]$ be the
restriction of a $C^3$ function $G$ with $|G'''| \le M_3$ on $[a, b]$. Then the piecewise
quadratic interpolation satisfies $$\|u - P_n u\|_\infty \le \frac{\sqrt{3}}{27} h^3 M_3.$$

The proof divides the panel error formula of `exists_sub_piecewisePolyInterpCLM_apply_eq` by
$3! = 6$ and uses the maximum $2\sqrt{3} h^3/9$ of the nodal polynomial on a panel. -/
theorem norm_sub_quadInterpCLM_le (hab : a < b) (p : ℕ) {G : ℝ → ℝ}
    (hG : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) G) {u : C(Set.Icc a b, ℝ)}
    (hu : ∀ t : Set.Icc a b, u t = G ((t : ℝ))) {M₃ : ℝ}
    (hM₃ : ∀ s ∈ Set.Icc a b, |iteratedDeriv 3 G s| ≤ M₃) :
    ‖u - quadInterpCLM hab.le p u‖ ≤ Real.sqrt 3 / 27 * quadMesh a b p ^ 3 * M₃ := by
  have h := norm_sub_piecewisePolyInterpCLM_le (isPanelNodes_quad hab p) hG hu
    (W := 2 * Real.sqrt 3 * quadMesh a b p ^ 3 / 9) (M := M₃)
    (fun k hk s hs => abs_prod_quadNode_le hab hk hs) hM₃
  have hfact : (((2 + 1 : ℕ)).factorial : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [quadInterpCLM]
  refine h.trans (le_of_eq ?_)
  rw [hfact]
  ring

end QuadraticError


section Smoothing

open IntegralOperator MeasureTheory

variable {a b : ℝ}

/-- Let $a < b$, let the kernel satisfy $|k(x, y) - k(x, z)| \le L |y - z|$ with $L \ge 0$, let $u$
be the restriction of a $C^4$ function $G$ with $|G''''| \le M_4$ on $[a, b]$, and let
$\|u - P_n u\| \le E$. Then for every $x$ and every panel $[x_{2j}, x_{2j+2}]$ with $j \le p$,
$$\left| \int_{x_{2j}}^{x_{2j+2}} k(x, y) (u - P_n u)(y)\, dy \right| \le \frac{\|k\|_\infty M_4
h^5}{90} + 4 L h^2 E.$$ The proof writes $k(x, y) = k(x, x_{2j}) + (k(x, y) - k(x, x_{2j}))$ and
reads the first part as the error of Simpson's rule on the panel
(`Quadrature.abs_integral_mul_sub_eval_le`).

**Reading.** Local cancellation estimate with a Lipschitz kernel bound.
-/
private theorem abs_panel_integral_le (hab : a < b) {k : C(Set.Icc a b × Set.Icc a b, ℝ)} {L : ℝ}
    (hL0 : 0 ≤ L) (hL : ∀ x y z : Set.Icc a b, |k (x, y) - k (x, z)| ≤ L * |(y : ℝ) - (z : ℝ)|)
    {G : ℝ → ℝ} (hG : ContDiff ℝ ((4 : ℕ) : WithTop ℕ∞) G) {u : C(Set.Icc a b, ℝ)}
    (hu : ∀ t : Set.Icc a b, u t = G ((t : ℝ))) {M₄ E : ℝ}
    (hM₄ : ∀ s ∈ Set.Icc a b, |iteratedDeriv 4 G s| ≤ M₄) (p : ℕ)
    (hE : ‖u - quadInterpCLM hab.le p u‖ ≤ E) (x : Set.Icc a b) {j : ℕ} (hj : j ≤ p) :
    |∫ y in ((quadBreak hab.le p j : ℝ))..((quadBreak hab.le p (j + 1) : ℝ)),
        k (x, Set.projIcc a b hab.le y)
          * (u - quadInterpCLM hab.le p u) (Set.projIcc a b hab.le y)|
      ≤ ‖k‖ * M₄ * quadMesh a b p ^ 5 / 90 + 4 * L * quadMesh a b p ^ 2 * E := by
  have hδ : 0 < quadMesh a b p := quadMesh_pos hab p
  have hnodes := isPanelNodes_quad hab p
  have hle : ((quadBreak hab.le p j : ℝ)) ≤ ((quadBreak hab.le p (j + 1) : ℝ)) :=
    (hnodes.step j hj).le
  have hlen : ((quadBreak hab.le p (j + 1) : ℝ)) - ((quadBreak hab.le p j : ℝ))
      = 2 * quadMesh a b p := quadBreak_sub hab hj
  have hmemab : ∀ y ∈ Set.Icc ((quadBreak hab.le p j : ℝ)) ((quadBreak hab.le p (j + 1) : ℝ)),
      y ∈ Set.Icc a b := fun y hy =>
    ⟨le_trans (quadBreak hab.le p j).2.1 hy.1, le_trans hy.2 (quadBreak hab.le p (j + 1)).2.2⟩
  -- the kernel row, as a function on the line
  have hκc : Continuous fun y : ℝ => k (x, Set.projIcc a b hab.le y) :=
    k.continuous.comp (continuous_const.prodMk continuous_projIcc)
  -- the panel interpolant, and its values at the three nodes
  have hinj : Set.InjOn (fun q => ((quadNode hab.le p j q : ℝ)))
      (↑(Finset.univ : Finset (Fin (2 + 1)))) := (hnodes.injective j hj).injOn
  have hqnode : ∀ i : Fin 3,
      (panelPoly (quadNode hab.le p) j u).eval ((quadNode hab.le p j i : ℝ))
        = G ((quadNode hab.le p j i : ℝ)) := by
    intro i
    rw [panelPoly, Lagrange.eval_interpolate_at_node _ hinj (Finset.mem_univ i), hu]
  have hqdeg : (panelPoly (quadNode hab.le p) j u).natDegree ≤ 3 := by
    have hdeg := Lagrange.degree_interpolate_lt (s := (Finset.univ : Finset (Fin 3)))
      (v := fun q => ((quadNode hab.le p j q : ℝ))) (r := fun i => u (quadNode hab.le p j i)) hinj
    rw [Finset.card_univ, Fintype.card_fin] at hdeg
    exact Polynomial.natDegree_le_iff_degree_le.mpr hdeg.le
  have hn0 : ((quadNode hab.le p j 0 : ℝ)) = ((quadBreak hab.le p j : ℝ)) := by
    rw [hnodes.node_zero j hj]
  have hn2 : ((quadNode hab.le p j 2 : ℝ)) = ((quadBreak hab.le p (j + 1) : ℝ)) := by
    have h := hnodes.node_last j hj
    rw [show (Fin.last 2 : Fin 3) = 2 from rfl] at h
    rw [h]
  have hn1 : ((quadNode hab.le p j 1 : ℝ))
      = (((quadBreak hab.le p j : ℝ)) + ((quadBreak hab.le p (j + 1) : ℝ))) / 2 := by
    have hA : ((quadNode hab.le p j 1 : ℝ)) = a + (2 * (j : ℝ) + 1) * quadMesh a b p := by
      rw [coe_quadNode hab.le hj]
      norm_num
    rw [hA, coe_quadBreak hab.le (by omega), coe_quadBreak hab.le (by omega)]
    push_cast
    ring
  have hqα : (panelPoly (quadNode hab.le p) j u).eval ((quadBreak hab.le p j : ℝ))
      = G ((quadBreak hab.le p j : ℝ)) := by
    rw [← hn0]
    exact hqnode 0
  have hqβ : (panelPoly (quadNode hab.le p) j u).eval ((quadBreak hab.le p (j + 1) : ℝ))
      = G ((quadBreak hab.le p (j + 1) : ℝ)) := by
    rw [← hn2]
    exact hqnode 2
  have hqm : (panelPoly (quadNode hab.le p) j u).eval
        (((quadBreak hab.le p j : ℝ) + (quadBreak hab.le p (j + 1) : ℝ)) / 2)
      = G (((quadBreak hab.le p j : ℝ) + (quadBreak hab.le p (j + 1) : ℝ)) / 2) := by
    rw [← hn1]
    exact hqnode 1
  -- the interpolation error on the panel, as a function on the line
  have hεval : ∀ y ∈ Set.Icc ((quadBreak hab.le p j : ℝ)) ((quadBreak hab.le p (j + 1) : ℝ)),
      (u - quadInterpCLM hab.le p u) (Set.projIcc a b hab.le y)
        = G y - (panelPoly (quadNode hab.le p) j u).eval y := by
    intro y hy
    have hproj : ((Set.projIcc a b hab.le y : Set.Icc a b) : ℝ) = y := by
      rw [Set.projIcc_of_mem hab.le (hmemab y hy)]
    rw [ContinuousMap.sub_apply, hu, hproj, quadInterpCLM,
      piecewisePolyInterpCLM_apply_of_mem hnodes u hj (by rw [hproj]; exact hy.1)
        (by rw [hproj]; exact hy.2), hproj]
  have hcongr : (∫ y in ((quadBreak hab.le p j : ℝ))..((quadBreak hab.le p (j + 1) : ℝ)),
        k (x, Set.projIcc a b hab.le y)
          * (u - quadInterpCLM hab.le p u) (Set.projIcc a b hab.le y))
      = ∫ y in ((quadBreak hab.le p j : ℝ))..((quadBreak hab.le p (j + 1) : ℝ)),
          k (x, Set.projIcc a b hab.le y)
            * (G y - (panelPoly (quadNode hab.le p) j u).eval y) := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [Set.uIcc_of_le hle] at hy
    simp only [hεval y hy]
  have hstep : ∀ i : ℕ, i < 4 → ∀ y : ℝ,
      HasDerivAt (iteratedDeriv i G) (iteratedDeriv (i + 1) G y) y := by
    intro i hi y
    have hd := ((hG.differentiable_iteratedDeriv i (by exact_mod_cast hi)) y).hasDerivAt
    rwa [← iteratedDeriv_succ] at hd
  have hc4 : Continuous (iteratedDeriv 4 G) := hG.continuous_iteratedDeriv 4 le_rfl
  have hLd : ∀ y ∈ Set.Icc ((quadBreak hab.le p j : ℝ)) ((quadBreak hab.le p (j + 1) : ℝ)),
      |k (x, Set.projIcc a b hab.le y)
          - k (x, Set.projIcc a b hab.le ((quadBreak hab.le p j : ℝ)))|
        ≤ L * (2 * quadMesh a b p) := by
    intro y hy
    have hprojy : ((Set.projIcc a b hab.le y : Set.Icc a b) : ℝ) = y := by
      rw [Set.projIcc_of_mem hab.le (hmemab y hy)]
    have hproja : ((Set.projIcc a b hab.le ((quadBreak hab.le p j : ℝ)) : Set.Icc a b) : ℝ)
        = ((quadBreak hab.le p j : ℝ)) := by
      rw [Set.projIcc_of_mem hab.le (hmemab _ ⟨le_rfl, hle⟩)]
    refine le_trans (hL x _ _) ?_
    rw [hprojy, hproja, abs_of_nonneg (by linarith [hy.1])]
    nlinarith [hlen, hL0, hy.1, hy.2]
  have hEd : ∀ y ∈ Set.Icc ((quadBreak hab.le p j : ℝ)) ((quadBreak hab.le p (j + 1) : ℝ)),
      |G y - (panelPoly (quadNode hab.le p) j u).eval y| ≤ E := by
    intro y hy
    rw [← hεval y hy]
    exact le_trans (by simpa using (u - quadInterpCLM hab.le p u).norm_coe_le_norm _) hE
  have h := Quadrature.abs_integral_mul_sub_eval_le (g := G) (g' := iteratedDeriv 1 G)
    (g'' := iteratedDeriv 2 G) (g₃ := iteratedDeriv 3 G) (g₄ := iteratedDeriv 4 G) hle
    (fun y _ => by simpa only [iteratedDeriv_zero] using hstep 0 (by norm_num) y)
    (fun y _ => hstep 1 (by norm_num) y) (fun y _ => hstep 2 (by norm_num) y)
    (fun y _ => hstep 3 (by norm_num) y) hc4.continuousOn (fun t ht => hM₄ t (hmemab t ht))
    hqdeg hqα hqm hqβ hκc.continuousOn (by simpa using k.norm_coe_le_norm _) hLd hEd
  rw [hcongr]
  refine h.trans (le_of_eq ?_)
  rw [hlen]
  ring

/-- **Equation (12.3.31)** of [han2009theoretical]. Let $a < b$, let $K$ be the integral operator on
$C[a, b]$ of a continuous kernel with $|k(x, y) - k(x, z)| \le L |y - z|$ for all $x, y, z$,
where $L \ge 0$, and let $u$ be the restriction of a $C^4$ function $G$ with $|G'''| \le M_3$
and $|G''''| \le M_4$ on $[a, b]$. Then $$\|K (I - P_n) u\|_\infty \le (b - a) \left(
\frac{\|k\|_\infty M_4}{180} + \frac{2\sqrt{3} L M_3}{27} \right) h^4,$$ so
$K (I - P_n) u = O(h^4)$, one power of $h$ better than $\|(I - P_n) u\| = O(h^3)$.

**Generalization.** The source assumes that $k$ is continuously differentiable in $y$. Only a
Lipschitz bound in $y$ is assumed here, and a kernel that is $C^1$ in $y$ satisfies it on the
compact square.

The source differentiates a Newton divided difference in $y$. Here the kernel is split on each
panel, and the main term is the error of Simpson's rule on that panel, which is $O(h^5)$.
Summing over the $(b - a)/(2h)$ panels gives $O(h^4)$. The norm $\|k\|_\infty$ is the uniform
norm of the kernel, and $K$ integrates against Lebesgue measure
`IntegralOperator.iccMeasure a b`. -/
theorem norm_kernelCLM_sub_quadInterpCLM_le (hab : a < b)
    {k : C(Set.Icc a b × Set.Icc a b, ℝ)} {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ x y z : Set.Icc a b, |k (x, y) - k (x, z)| ≤ L * |(y : ℝ) - (z : ℝ)|)
    {G : ℝ → ℝ} (hG : ContDiff ℝ ((4 : ℕ) : WithTop ℕ∞) G) {u : C(Set.Icc a b, ℝ)}
    (hu : ∀ t : Set.Icc a b, u t = G ((t : ℝ))) {M₃ M₄ : ℝ}
    (hM₃ : ∀ s ∈ Set.Icc a b, |iteratedDeriv 3 G s| ≤ M₃)
    (hM₄ : ∀ s ∈ Set.Icc a b, |iteratedDeriv 4 G s| ≤ M₄) (p : ℕ) :
    ‖kernelCLM (iccMeasure a b) k (u - quadInterpCLM hab.le p u)‖
      ≤ (b - a) * (‖k‖ * M₄ / 180 + 2 * Real.sqrt 3 * L * M₃ / 27) * quadMesh a b p ^ 4 := by
  have hδ : 0 < quadMesh a b p := quadMesh_pos hab p
  have hnodes := isPanelNodes_quad hab p
  have hab0 : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hM30 : 0 ≤ M₃ := le_trans (abs_nonneg _) (hM₃ a ⟨le_rfl, hab.le⟩)
  have hM40 : 0 ≤ M₄ := le_trans (abs_nonneg _) (hM₄ a ⟨le_rfl, hab.le⟩)
  have hs30 : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hE : ‖u - quadInterpCLM hab.le p u‖ ≤ Real.sqrt 3 / 27 * quadMesh a b p ^ 3 * M₃ :=
    norm_sub_quadInterpCLM_le hab p (hG.of_le (by norm_num)) hu hM₃
  have hrhs0 : (0 : ℝ)
      ≤ (b - a) * (‖k‖ * M₄ / 180 + 2 * Real.sqrt 3 * L * M₃ / 27) * quadMesh a b p ^ 4 := by
    refine mul_nonneg (mul_nonneg hab0.le (add_nonneg ?_ ?_)) (pow_nonneg hδ.le 4)
    · exact div_nonneg (mul_nonneg (norm_nonneg k) hM40) (by norm_num)
    · exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) hL0) hM30) (by norm_num)
  rw [ContinuousMap.norm_le _ hrhs0]
  intro x
  rw [kernelCLM_apply, Real.norm_eq_abs]
  have hFc : Continuous fun y : ℝ => k (x, Set.projIcc a b hab.le y)
      * (u - quadInterpCLM hab.le p u) (Set.projIcc a b hab.le y) :=
    (k.continuous.comp (continuous_const.prodMk continuous_projIcc)).mul
      ((u - quadInterpCLM hab.le p u).continuous.comp continuous_projIcc)
  have hconv : (∫ y, k (x, y) * (u - quadInterpCLM hab.le p u) y ∂iccMeasure a b)
      = ∫ y in a..b, k (x, Set.projIcc a b hab.le y)
          * (u - quadInterpCLM hab.le p u) (Set.projIcc a b hab.le y) := by
    rw [← IntegralOperator.integral_iccMeasure hab.le fun y => k (x, Set.projIcc a b hab.le y)
      * (u - quadInterpCLM hab.le p u) (Set.projIcc a b hab.le y)]
    simp
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun j => ((quadBreak hab.le p j : ℝ))) (n := p + 1)
    (f := fun y : ℝ => k (x, Set.projIcc a b hab.le y)
      * (u - quadInterpCLM hab.le p u) (Set.projIcc a b hab.le y))
    (μ := MeasureTheory.volume) fun j _ => Continuous.intervalIntegrable hFc _ _
  rw [(hnodes.first : ((quadBreak hab.le p 0 : ℝ)) = a),
    (hnodes.last : ((quadBreak hab.le p (p + 1) : ℝ)) = b)] at hsum
  have hpd : ((p : ℝ) + 1) * quadMesh a b p = (b - a) / 2 := by
    rw [quadMesh]
    field_simp
  rw [hconv, ← hsum]
  calc |∑ j ∈ Finset.range (p + 1),
        ∫ y in ((quadBreak hab.le p j : ℝ))..((quadBreak hab.le p (j + 1) : ℝ)),
          k (x, Set.projIcc a b hab.le y)
            * (u - quadInterpCLM hab.le p u) (Set.projIcc a b hab.le y)|
      ≤ ∑ j ∈ Finset.range (p + 1),
          |∫ y in ((quadBreak hab.le p j : ℝ))..((quadBreak hab.le p (j + 1) : ℝ)),
            k (x, Set.projIcc a b hab.le y)
              * (u - quadInterpCLM hab.le p u) (Set.projIcc a b hab.le y)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range (p + 1), (‖k‖ * M₄ * quadMesh a b p ^ 5 / 90
          + 4 * L * quadMesh a b p ^ 2 * (Real.sqrt 3 / 27 * quadMesh a b p ^ 3 * M₃)) :=
        Finset.sum_le_sum fun j hj => abs_panel_integral_le hab hL0 hL hG hu hM₄ p hE x
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    _ = ((p : ℝ) + 1) * (‖k‖ * M₄ * quadMesh a b p ^ 5 / 90
          + 4 * L * quadMesh a b p ^ 2 * (Real.sqrt 3 / 27 * quadMesh a b p ^ 3 * M₃)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ = (b - a) * (‖k‖ * M₄ / 180 + 2 * Real.sqrt 3 * L * M₃ / 27) * quadMesh a b p ^ 4 := by
        linear_combination (quadMesh a b p ^ 4 *
          (‖k‖ * M₄ / 90 + 4 * Real.sqrt 3 * L * M₃ / 27)) * hpd


end Smoothing


/-! ### Theorem 12.3.3 -/

section Theorem3

open IntegralOperator MeasureTheory

variable {a b : ℝ}

/-- **Theorem 12.3.3** of [han2009theoretical] (superconvergence of iterated piecewise quadratic
collocation). Let $a < b$, let $K$ be the integral operator on $C[a, b]$ of a continuous kernel
with $|k(x, y) - k(x, z)| \le L |y - z|$ for all $x, y, z$, where $L \ge 0$, and let
$\lambda \neq 0$ be such that $\lambda - K$ is invertible. Let $u$ be the restriction of a $C^4$
function $G$ with $|G'''| \le M_3$ and $|G''''| \le M_4$ on $[a, b]$, and let
$f = (\lambda - K) u$, which is (12.3.23). Let $P_n$ be piecewise quadratic interpolation on the
uniform mesh with $n = 2(p + 1)$ subintervals of width $h$. Then there are constants $M$ and $c$
such that for all large $n$ the operator $\lambda - P_n K$ is invertible with
$\|(\lambda - P_n K)^{-1}\| \le M$, the collocation equations have exactly one solution for
every right-hand side, and the collocation solution $u_n$ for $f$ satisfies

* $\|u - u_n\|_\infty \le |\lambda| M \|u - P_n u\|_\infty \le (\sqrt{3} |\lambda| M / 27)\, h^3
  M_3$, which is (12.3.32);
* $\|u - \hat u_n\|_\infty \le c h^4$, which is (12.3.33);
* $|u(x_j) - u_n(x_j)| \le c h^4$ at each of the $n + 1$ mesh points $x_j$, which is (12.3.34).

**Generalization.** The source assumes that the kernel is continuously differentiable in $y$.
Only a Lipschitz bound in $y$ is assumed here, and a kernel that is $C^1$ in $y$ satisfies it on
the compact square.

The operator bounds come from `AtkinsonHan.Chapter12.theorem_12_1_2` and
`AtkinsonHan.Chapter12.lemma_12_3_1_projection`. The first inequality of (12.3.32) is
`AtkinsonHan.Chapter12.equation_12_1_24`, the second is
`AtkinsonHan.Chapter12.norm_sub_quadInterpCLM_le`, and (12.3.33) is
`AtkinsonHan.Chapter12.equation_12_3_11` together with
`AtkinsonHan.Chapter12.norm_kernelCLM_sub_quadInterpCLM_le`. For (12.3.34), $P_n \hat u_n = u_n$
and $P_n$ reproduces the values at the mesh points, so $u_n$ and $\hat u_n$ agree there. -/
theorem theorem_12_3_3 (hab : a < b) {k : C(Set.Icc a b × Set.Icc a b, ℝ)} {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ x y z : Set.Icc a b, |k (x, y) - k (x, z)| ≤ L * |(y : ℝ) - (z : ℝ)|)
    {μ : ℝ} (hμ : μ ≠ 0) {e : C(Set.Icc a b, ℝ) ≃L[ℝ] C(Set.Icc a b, ℝ)}
    (he : (e : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))
      = μ • 1 - kernelCLM (iccMeasure a b) k)
    {G : ℝ → ℝ} (hG : ContDiff ℝ ((4 : ℕ) : WithTop ℕ∞) G) {u : C(Set.Icc a b, ℝ)}
    (hu : ∀ t : Set.Icc a b, u t = G ((t : ℝ))) {M₃ M₄ : ℝ}
    (hM₃ : ∀ s ∈ Set.Icc a b, |iteratedDeriv 3 G s| ≤ M₃)
    (hM₄ : ∀ s ∈ Set.Icc a b, |iteratedDeriv 4 G s| ≤ M₄) {f : C(Set.Icc a b, ℝ)}
    (hf : (μ • 1 - kernelCLM (iccMeasure a b) k :
      C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) u = f) :
    ∃ M c : ℝ, ∀ᶠ p in atTop, ∃ e' : C(Set.Icc a b, ℝ) ≃L[ℝ] C(Set.Icc a b, ℝ),
      (e' : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))
          = μ • 1 - quadInterpCLM hab.le p ∘L kernelCLM (iccMeasure a b) k ∧
        ‖(e'.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖ ≤ M ∧
        (∀ g : C(Set.Icc a b, ℝ), ∃! un : C(Set.Icc a b, ℝ), IsProjectionSolution μ
          (kernelCLM (iccMeasure a b) k) (quadInterpCLM hab.le p) g un) ∧
        ∀ un : C(Set.Icc a b, ℝ), IsProjectionSolution μ (kernelCLM (iccMeasure a b) k)
            (quadInterpCLM hab.le p) f un →
          ‖u - un‖ ≤ |μ| * M * ‖u - quadInterpCLM hab.le p u‖ ∧
          ‖u - un‖ ≤ Real.sqrt 3 * (|μ| * M) / 27 * quadMesh a b p ^ 3 * M₃ ∧
          ‖u - iteratedSolution μ (kernelCLM (iccMeasure a b) k) f un‖
            ≤ c * quadMesh a b p ^ 4 ∧
          ∀ j ≤ 2 * (p + 1),
            |u (meshPoint hab.le (2 * (p + 1)) j) - un (meshPoint hab.le (2 * (p + 1)) j)|
              ≤ c * quadMesh a b p ^ 4 := by
  classical
  have hKc : IsCompactOperator (kernelCLM (iccMeasure a b) k) :=
    isCompactOperator_kernelCLM _ k
  have hS0 : (0 : ℝ) ≤ ‖(e.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖ := norm_nonneg _
  -- the uniform bounds
  refine ⟨2 * ‖(e.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖,
    |μ|⁻¹ * (1 + ‖kernelCLM (iccMeasure a b) k‖ *
        (2 * ‖(e.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖ * 12)) *
      ((b - a) * (‖k‖ * M₄ / 180 + 2 * Real.sqrt 3 * L * M₃ / 27)), ?_⟩
  have hzero : Tendsto (fun p => ‖(e.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖ *
      ‖kernelCLM (iccMeasure a b) k
        - quadInterpCLM hab.le p ∘L kernelCLM (iccMeasure a b) k‖) atTop (𝓝 0) := by
    have h := (lemma_12_1_4 hKc (tendsto_quadInterpCLM hab)).const_mul
      ‖(e.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖
    simpa using h
  filter_upwards [hzero.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)] with p hp
  -- Theorem 12.1.2 and the uniform bound on the inverses
  obtain ⟨e', he'coe, he'norm, he'sol⟩ := theorem_12_1_2 hμ (isIdempotentElem_quadInterpCLM hab p)
    e he (lt_of_lt_of_le hp (by norm_num))
  have hden : (0 : ℝ) < 1 - ‖(e.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖ *
      ‖kernelCLM (iccMeasure a b) k
        - quadInterpCLM hab.le p ∘L kernelCLM (iccMeasure a b) k‖ := by linarith
  have hM : ‖(e'.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖
      ≤ 2 * ‖(e.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖ := by
    refine he'norm.trans ?_
    rw [div_le_iff₀ hden]
    nlinarith [hS0, hp]
  refine ⟨e', he'coe, hM, he'sol, fun un hun => ?_⟩
  -- (12.3.32)
  have h1224 := (equation_12_1_24 (isIdempotentElem_quadInterpCLM hab p) he'coe hf hun).2
  rw [Real.norm_eq_abs] at h1224
  have hinterp : ‖u - quadInterpCLM hab.le p u‖
      ≤ Real.sqrt 3 / 27 * quadMesh a b p ^ 3 * M₃ :=
    norm_sub_quadInterpCLM_le hab p (hG.of_le (by norm_num)) hu hM₃
  have hfirst : ‖u - un‖ ≤ |μ| * (2 * ‖(e.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖)
      * ‖u - quadInterpCLM hab.le p u‖ := by
    exact h1224.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hM (abs_nonneg μ)) (norm_nonneg _))
  have hsecond : ‖u - un‖ ≤ Real.sqrt 3 *
      (|μ| * (2 * ‖(e.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖)) / 27
        * quadMesh a b p ^ 3 * M₃ := by
    refine hfirst.trans ?_
    have h0 : (0 : ℝ) ≤ |μ| * (2 * ‖(e.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖) := by
      positivity
    nlinarith [hinterp, h0]
  -- Lemma 12.3.1 applied to the projection, and the error identity (12.3.11)
  obtain ⟨e'', he''coe, -, he''norm⟩ := lemma_12_3_1_projection hμ
    (kernelCLM (iccMeasure a b) k) (quadInterpCLM hab.le p) he'coe
  have hMpp : ‖(e''.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖
      ≤ |μ|⁻¹ * (1 + ‖kernelCLM (iccMeasure a b) k‖ *
        (2 * ‖(e.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖ * 12)) := by
    refine he''norm.trans ?_
    rw [Real.norm_eq_abs]
    have hP12 : ‖quadInterpCLM hab.le p‖ ≤ 12 := norm_quadInterpCLM_le hab p
    have hKn : (0 : ℝ) ≤ ‖kernelCLM (iccMeasure a b) k‖ := norm_nonneg _
    have hinv : (0 : ℝ) ≤ |μ|⁻¹ := by positivity
    have hmono : ‖kernelCLM (iccMeasure a b) k‖ *
        (‖(e'.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖ * ‖quadInterpCLM hab.le p‖)
        ≤ ‖kernelCLM (iccMeasure a b) k‖ *
          (2 * ‖(e.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖ * 12) := by
      refine mul_le_mul_of_nonneg_left ?_ hKn
      have h1 : (0 : ℝ) ≤ ‖quadInterpCLM hab.le p‖ := norm_nonneg _
      have h2 : (0 : ℝ) ≤ ‖(e'.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖ :=
        norm_nonneg _
      nlinarith [hM, hP12, hS0]
    exact mul_le_mul_of_nonneg_left (by linarith) hinv
  have hid := (equation_12_3_11 hμ (isIdempotentElem_quadInterpCLM hab p) he''coe hf hun).1
  have herr : u - iteratedSolution μ (kernelCLM (iccMeasure a b) k) f un
      = e''.symm (kernelCLM (iccMeasure a b) k (u - quadInterpCLM hab.le p u)) := by
    rw [← hid, ← he''coe, ContinuousLinearEquiv.coe_coe, e''.symm_apply_apply]
  have h1231 := norm_kernelCLM_sub_quadInterpCLM_le hab hL0 hL hG hu hM₃ hM₄ p
  have hthird : ‖u - iteratedSolution μ (kernelCLM (iccMeasure a b) k) f un‖
      ≤ |μ|⁻¹ * (1 + ‖kernelCLM (iccMeasure a b) k‖ *
          (2 * ‖(e.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖ * 12)) *
        ((b - a) * (‖k‖ * M₄ / 180 + 2 * Real.sqrt 3 * L * M₃ / 27)) * quadMesh a b p ^ 4 := by
    rw [herr]
    have hstep1 : ‖e''.symm (kernelCLM (iccMeasure a b) k (u - quadInterpCLM hab.le p u))‖
        ≤ ‖(e''.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖
          * ‖kernelCLM (iccMeasure a b) k (u - quadInterpCLM hab.le p u)‖ :=
      ContinuousLinearMap.le_opNorm (e''.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) _
    have hnn : (0 : ℝ) ≤ ‖kernelCLM (iccMeasure a b) k (u - quadInterpCLM hab.le p u)‖ :=
      norm_nonneg _
    have hMpp0 : (0 : ℝ) ≤ |μ|⁻¹ * (1 + ‖kernelCLM (iccMeasure a b) k‖ *
        (2 * ‖(e.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖ * 12)) :=
      le_trans (norm_nonneg _) hMpp
    calc ‖e''.symm (kernelCLM (iccMeasure a b) k (u - quadInterpCLM hab.le p u))‖
        ≤ ‖(e''.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖
            * ‖kernelCLM (iccMeasure a b) k (u - quadInterpCLM hab.le p u)‖ := hstep1
      _ ≤ (|μ|⁻¹ * (1 + ‖kernelCLM (iccMeasure a b) k‖ *
            (2 * ‖(e.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖ * 12)))
            * ‖kernelCLM (iccMeasure a b) k (u - quadInterpCLM hab.le p u)‖ :=
          mul_le_mul_of_nonneg_right hMpp hnn
      _ ≤ (|μ|⁻¹ * (1 + ‖kernelCLM (iccMeasure a b) k‖ *
            (2 * ‖(e.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))‖ * 12)))
            * ((b - a) * (‖k‖ * M₄ / 180 + 2 * Real.sqrt 3 * L * M₃ / 27)
              * quadMesh a b p ^ 4) := mul_le_mul_of_nonneg_left h1231 hMpp0
      _ = _ := by ring
  -- (12.3.34): the collocation solution agrees with the iterated solution at the mesh points
  refine ⟨hfirst, hsecond, hthird, fun j hj => ?_⟩
  have hnode : un (meshPoint hab.le (2 * (p + 1)) j)
      = iteratedSolution μ (kernelCLM (iccMeasure a b) k) f un
        (meshPoint hab.le (2 * (p + 1)) j) := by
    have hproj := equation_12_3_2 hμ (isIdempotentElem_quadInterpCLM hab p) hun
    calc un (meshPoint hab.le (2 * (p + 1)) j)
        = quadInterpCLM hab.le p (iteratedSolution μ (kernelCLM (iccMeasure a b) k) f un)
            (meshPoint hab.le (2 * (p + 1)) j) := by rw [hproj]
      _ = iteratedSolution μ (kernelCLM (iccMeasure a b) k) f un
            (meshPoint hab.le (2 * (p + 1)) j) :=
          quadInterpCLM_apply_meshPoint hab p _ hj
  rw [hnode]
  have hval : |u (meshPoint hab.le (2 * (p + 1)) j)
      - iteratedSolution μ (kernelCLM (iccMeasure a b) k) f un
        (meshPoint hab.le (2 * (p + 1)) j)|
      ≤ ‖u - iteratedSolution μ (kernelCLM (iccMeasure a b) k) f un‖ := by
    have := (u - iteratedSolution μ (kernelCLM (iccMeasure a b) k) f un).norm_coe_le_norm
      (meshPoint hab.le (2 * (p + 1)) j)
    simpa using this
  exact hval.trans hthird

end Theorem3


/-! ### Example 12.3.2: the iterated Galerkin method with discontinuous piecewise linears -/

section IteratedGalerkin

open MeasureTheory IntegralOperator

local notation "L²" => Lp ℝ 2 (IntegralOperator.iccMeasure 0 1)

/-- **Equation (12.3.18)** of [han2009theoretical], the kernel. The kernel $k(x, y) = e^{xy}$ on
$[0, 1] \times [0, 1]$, as a continuous function.

The same kernel appears in (12.2.8) and in (12.4.7), the equations of Examples 12.2.1 and
12.4.1. It is defined here, in the first section that uses it, and Section 12.4 uses it again. -/
noncomputable def expKernel : C(Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1, ℝ) :=
  ⟨fun p => Real.exp ((p.1 : ℝ) * (p.2 : ℝ)), by fun_prop⟩

/-- The kernel of (12.3.18) has the value $e^{xy}$ at $(x, y)$. -/
theorem expKernel_apply (p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1) :
    expKernel p = Real.exp ((p.1 : ℝ) * (p.2 : ℝ)) := rfl

/-- The kernel of (12.3.18) satisfies $\|k\|_\infty \le e$ on the unit square. -/
theorem norm_expKernel_le : ‖expKernel‖ ≤ Real.exp 1 := by
  refine (ContinuousMap.norm_le _ (Real.exp_nonneg 1)).2 fun p => ?_
  rw [expKernel_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.2 ?_
  nlinarith [p.1.2.1, p.1.2.2, p.2.2.1, p.2.2.2]

/-- **Equation (12.3.18)** of [han2009theoretical], the operator. The integral operator
$K u(x) = \int_0^1 e^{xy} u(y)\, dy$ on $L^2(0, 1)$.

It is `IntegralOperator.l2KernelCLM` for the kernel `AtkinsonHan.Chapter12.expKernel`. -/
noncomputable def expKernelCLM : L² →L[ℝ] L² :=
  l2KernelCLM (memLp_prod_iccMeasure expKernel)

/-- The operator of (12.3.18) satisfies $\|K\| \le e$.

In particular $\|K\| < 50 = \lambda$, so the equation (12.3.18) is uniquely solvable by the
Neumann series, without a compactness argument. -/
theorem norm_expKernelCLM_le : ‖expKernelCLM‖ ≤ Real.exp 1 := by
  have h := norm_l2KernelCLM_comp_le (a := 0) (b := 1) zero_le_one
    (memLp_prod_iccMeasure expKernel) (Q := (1 : L² →L[ℝ] L²)) (IsSelfAdjoint.one _)
    (ε := Real.exp 1) (Real.exp_nonneg 1) ?_
  · rw [show (l2KernelCLM (memLp_prod_iccMeasure expKernel) ∘L (1 : L² →L[ℝ] L²))
      = expKernelCLM from mul_one _] at h
    simpa using h
  · intro z
    rw [one_apply_eq_self]
    refine (norm_iccToLp_le zero_le_one _).trans ?_
    have hrow : ‖expKernel.curry z‖ ≤ ‖expKernel‖ :=
      (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun t => expKernel.norm_coe_le_norm (z, t)
    simpa using hrow.trans norm_expKernel_le

/-- The operator of (12.3.18) satisfies $\|K\| < |\lambda|$ at the value $\lambda = 50$ of the
source. -/
theorem norm_expKernelCLM_lt : ‖expKernelCLM‖ < |(50 : ℝ)| := by
  have h := norm_expKernelCLM_le
  have he := Real.exp_one_lt_d9
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 50)]
  linarith

/-- The operator of (12.3.18) is self-adjoint, $K^* = K$, because the kernel $e^{xy}$ is symmetric.
-/
theorem isSelfAdjoint_expKernelCLM : IsSelfAdjoint expKernelCLM :=
  isSelfAdjoint_l2KernelCLM _
    (Filter.Eventually.of_forall fun p => by simp [expKernel_apply, mul_comm])

/-- The uniform mesh $x_j = j h$, $h = 1/n$, of $[0, 1]$ with $n$ subintervals, as used in Example
12.3.2.

The partition has $n$ panels, so the panel count argument of `discPiecewiseLinearProjCLM`, which
takes the number of panels minus one, is $n - 1$ here. -/
noncomputable def unitMesh (n j : ℕ) : Set.Icc (0 : ℝ) 1 := meshPoint zero_le_one n j

/-- For $n > 0$ and $j \le n$, the mesh point is $x_j = j/n$. -/
theorem coe_unitMesh {n j : ℕ} (hn : 0 < n) (hj : j ≤ n) :
    (unitMesh n j : ℝ) = (j : ℝ) / n := by
  rw [unitMesh, coe_meshPoint zero_le_one hn hj]
  ring

/-- For $n > 0$ the mesh points $x_0 < x_1 < \dots < x_n$ increase. -/
theorem unitMesh_step {n : ℕ} (hn : 0 < n) :
    ∀ i ≤ n - 1, (unitMesh n i : ℝ) < (unitMesh n (i + 1) : ℝ) := by
  intro i hi
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [coe_unitMesh hn (by omega), coe_unitMesh hn (by omega)]
  gcongr
  linarith

/-- The mesh starts at $x_0 = 0$. -/
theorem unitMesh_first (n : ℕ) : (unitMesh n 0 : ℝ) = 0 := by
  rw [unitMesh, meshPoint]
  simp

/-- For $n > 0$ the mesh ends at $x_n = 1$. -/
theorem unitMesh_last {n : ℕ} (hn : 0 < n) : (unitMesh n (n - 1 + 1) : ℝ) = 1 := by
  rw [show n - 1 + 1 = n by omega, coe_unitMesh hn le_rfl]
  field_simp

/-- For $n > 0$ every subinterval of the mesh has length at most $h = 1/n$. -/
theorem unitMesh_mesh {n : ℕ} (hn : 0 < n) :
    ∀ i ≤ n - 1, (unitMesh n (i + 1) : ℝ) - (unitMesh n i : ℝ) ≤ 1 / n := by
  intro i hi
  rw [coe_unitMesh hn (by omega), coe_unitMesh hn (by omega)]
  push_cast
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  field_simp
  linarith

/-- **Example 12.3.2** of [han2009theoretical], the projection. The projection $P_n$ is the
orthogonal projection of $L^2(0, 1)$ onto the functions that are linear on each subinterval of
the uniform mesh of width $h = 1/n$, without the continuity condition of §12.2.3.

It is `discPiecewiseLinearProjCLM`. The dimension $d_n = 2n$ of the trial space, which the
source gives, is not formalized: it concerns the size of the linear system, and (12.3.19) and
(12.3.20) do not use it. -/
noncomputable def discGalerkinProj (n : ℕ) : L² →L[ℝ] L² :=
  discPiecewiseLinearProjCLM 0 1 (n - 1) (unitMesh n)

/-- **Example 12.3.2** of [han2009theoretical]. The operator $P_n$ is a projection: $P_n^2 = P_n$.
-/
theorem isIdempotentElem_discGalerkinProj (n : ℕ) : IsIdempotentElem (discGalerkinProj n) :=
  isIdempotentElem_discPiecewiseLinearProjCLM 0 1 (n - 1) (unitMesh n)

/-- **Example 12.3.2** of [han2009theoretical]. The operator $P_n$ is self-adjoint, because it is an
orthogonal projection. Equation (12.3.13) uses this. -/
theorem isSelfAdjoint_discGalerkinProj (n : ℕ) : IsSelfAdjoint (discGalerkinProj n) :=
  isSelfAdjoint_discPiecewiseLinearProjCLM 0 1 (n - 1) (unitMesh n)

/-- **Example 12.3.2** of [han2009theoretical], the estimate that the source states without proof.
For $n > 0$ and $h = 1/n$, $$\|K (I - P_n)\| \le \frac{e h^2}{8}.$$

The functions $y \mapsto e^{xy}$ are $C^2$ with $|\partial_y^2 e^{xy}| = x^2 e^{xy} \le e$ on
the unit square, so the $O(h^2)$ approximation order of $P_n$ applies to them uniformly in $x$. -/
theorem norm_expKernelCLM_comp_sub_discGalerkinProj_le {n : ℕ} (hn : 0 < n) :
    ‖expKernelCLM ∘L (1 - discGalerkinProj n)‖ ≤ (1 / (n : ℝ)) ^ 2 / 8 * Real.exp 1 := by
  have key := norm_l2KernelCLM_comp_sub_discPiecewiseLinearProjCLM_le (a := 0) (b := 1)
    zero_le_one ⟨fun i hi => unitMesh_step hn i (by omega), unitMesh_first n, unitMesh_last hn⟩
    (memLp_prod_iccMeasure expKernel) (G := fun z t => Real.exp ((z : ℝ) * t))
    (fun _ => Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))
    (fun _ _ => rfl) (unitMesh_mesh hn) (M := Real.exp 1) ?_
  · simpa [expKernelCLM, discGalerkinProj] using key
  · intro z t ht
    rw [iteratedDeriv_exp_const_mul, abs_of_nonneg (by positivity)]
    have h1 : (z : ℝ) ^ 2 ≤ 1 := by nlinarith [z.2.1, z.2.2]
    have h2 : Real.exp ((z : ℝ) * t) ≤ Real.exp 1 :=
      Real.exp_le_exp.2 (by nlinarith [z.2.1, z.2.2, ht.1, ht.2])
    nlinarith [Real.exp_pos ((z : ℝ) * t), Real.exp_pos (1 : ℝ), sq_nonneg (z : ℝ)]

/-- **Equation (12.3.13)** of [han2009theoretical], in Example 12.3.2. For $n > 0$ and $h = 1/n$,
$$\|K - P_n K\| \le \frac{e h^2}{8}.$$

Here $\|K - P_n K\| = \|(I - P_n) K^*\| = \|K (I - P_n)\|$, because $K^* = K$ (the kernel is
symmetric), $P_n$ is self-adjoint, and an operator and its adjoint have the same norm. This
bound is the hypothesis of `AtkinsonHan.Chapter12.theorem_12_1_2`, and it replaces the
compactness argument of (12.3.15). -/
theorem norm_sub_comp_expKernelCLM_le {n : ℕ} (hn : 0 < n) :
    ‖expKernelCLM - discGalerkinProj n ∘L expKernelCLM‖
      ≤ (1 / (n : ℝ)) ^ 2 / 8 * Real.exp 1 := by
  have hsub : expKernelCLM - discGalerkinProj n ∘L expKernelCLM
      = (1 - discGalerkinProj n) ∘L expKernelCLM := by
    rw [ContinuousLinearMap.sub_comp, show (1 : L² →L[ℝ] L²) ∘L expKernelCLM
      = expKernelCLM from one_mul _]
  have hadj : ContinuousLinearMap.adjoint ((1 - discGalerkinProj n) ∘L expKernelCLM)
      = expKernelCLM ∘L (1 - discGalerkinProj n) := by
    rw [ContinuousLinearMap.adjoint_comp, isSelfAdjoint_expKernelCLM.adjoint_eq,
      (IsSelfAdjoint.sub (IsSelfAdjoint.one _) (isSelfAdjoint_discGalerkinProj n)).adjoint_eq]
  rw [hsub, ← ContinuousLinearMap.adjoint.norm_map, hadj]
  exact norm_expKernelCLM_comp_sub_discGalerkinProj_le hn

/-- If $\lambda \neq 0$ and $\|K\| < |\lambda|$ on a Banach space, then $\lambda - K$ is invertible.
-/
private theorem exists_equiv_smul_sub_of_norm_lt {Y : Type*} [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] [CompleteSpace Y] {μ : ℝ} (hμ : μ ≠ 0) {K : Y →L[ℝ] Y} (h : ‖K‖ < |μ|) :
    ∃ e : Y ≃L[ℝ] Y, (e : Y →L[ℝ] Y) = μ • 1 - K := by
  have habs : (0 : ℝ) < |μ| := abs_pos.2 hμ
  let v : (Y →L[ℝ] Y)ˣ :=
    { val := μ • 1
      inv := μ⁻¹ • 1
      val_inv := by ext x; simp [smul_smul, inv_mul_cancel₀ hμ]
      inv_val := by ext x; simp [smul_smul, mul_inv_cancel₀ hμ] }
  set e₀ : Y ≃L[ℝ] Y := ContinuousLinearEquiv.ofUnit v with he₀def
  have he₀ : (e₀ : Y →L[ℝ] Y) = μ • 1 := by ext x; rfl
  have hsymm : (e₀.symm : Y →L[ℝ] Y) = μ⁻¹ • 1 := by ext y; rfl
  have hns : ‖(e₀.symm : Y →L[ℝ] Y)‖ ≤ |μ|⁻¹ := by
    rw [hsymm, norm_smul, norm_inv, Real.norm_eq_abs]
    calc |μ|⁻¹ * ‖(1 : Y →L[ℝ] Y)‖ ≤ |μ|⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (by positivity)
      _ = |μ|⁻¹ := mul_one _
  have hlt : ‖(e₀.symm : Y →L[ℝ] Y)‖ * ‖(-K : Y →L[ℝ] Y)‖ < 1 := by
    rw [norm_neg]
    calc ‖(e₀.symm : Y →L[ℝ] Y)‖ * ‖K‖ ≤ |μ|⁻¹ * ‖K‖ :=
          mul_le_mul_of_nonneg_right hns (norm_nonneg _)
      _ < 1 := by rw [inv_mul_lt_one₀ habs]; exact h
  obtain ⟨e, he, -, -⟩ := ContinuousLinearEquiv.exists_symm_norm_le_of_add e₀ (-K) hlt
  exact ⟨e, by rw [he, he₀, ← sub_eq_add_neg]⟩

/-- **Example 12.3.2** of [han2009theoretical]. The exact solution $u(x) = e^x$, as a continuous
function on $[0, 1]$. -/
noncomputable def expSolutionFun : C(Set.Icc (0 : ℝ) 1, ℝ) := ⟨fun t => Real.exp t, by fun_prop⟩

/-- **Example 12.3.2** of [han2009theoretical]. The exact solution $u(x) = e^x$, as an element of
$L^2(0, 1)$. -/
noncomputable def expSolution : L² := iccToLp 0 1 expSolutionFun

/-- **Example 12.3.2** of [han2009theoretical]. The right-hand side $f = 50 u - K u$ of (12.3.18)
for $\lambda = 50$ and $u(x) = e^x$. -/
noncomputable def expRhs : L² := ((50 : ℝ) • 1 - expKernelCLM : L² →L[ℝ] L²) expSolution

/-- **Example 12.3.2** of [han2009theoretical], the second estimate. For $n > 0$ and $h = 1/n$, the
solution $u(x) = e^x$ satisfies $$\|u - P_n u\|_{L^2} \le \frac{e h^2}{8}.$$ The function $u$ is
$C^2$ with $|u''| \le e$ on $[0, 1]$, so the $O(h^2)$ approximation order of the discontinuous
piecewise linear projection applies. -/
theorem norm_sub_discGalerkinProj_expSolution_le {n : ℕ} (hn : 0 < n) :
    ‖expSolution - discGalerkinProj n expSolution‖ ≤ (1 / (n : ℝ)) ^ 2 / 8 * Real.exp 1 := by
  have hiter : iteratedDeriv 2 Real.exp = Real.exp := by
    simpa using iteratedDeriv_exp_const_mul 2 1
  have hinterp := norm_sub_piecewiseLinearInterpCLM_le
    ⟨fun i hi => unitMesh_step hn i (by omega), unitMesh_first n, unitMesh_last hn⟩
    (g := Real.exp) Real.contDiff_exp (f := expSolutionFun) (fun _ => rfl)
    (unitMesh_mesh hn) (M := Real.exp 1) (fun t ht => by
      rw [hiter, abs_of_pos (Real.exp_pos t)]
      exact Real.exp_le_exp.2 ht.2)
  refine (norm_sub_discPiecewiseLinearProjCLM_le (a := 0) (b := 1) zero_le_one
    ⟨fun i hi => unitMesh_step hn i (by omega), unitMesh_first n, unitMesh_last hn⟩
    expSolutionFun).trans ?_
  rw [show (1 : ℝ) - 0 = 1 by ring, Real.sqrt_one, one_mul]
  exact hinterp

/-- **Example 12.3.2** of [han2009theoretical] (the iterated Galerkin method). Consider the equation
$$50 u(x) - \int_0^1 e^{xy} u(y)\, dy = f(x), \qquad 0 \le x \le 1,$$ which is (12.3.18), on
$L^2(0, 1)$, with the exact solution $u(x) = e^x$, and the Galerkin method with the
discontinuous piecewise linear functions on the uniform mesh of width $h = 1/n$. There are
constants $c_1$ and $c_2$ such that for all large $n$ the Galerkin equations have exactly one
solution for every right-hand side, and the Galerkin solution $u_n$ for this $f$ and the
iterated solution $\hat u_n = (f + K u_n)/50$ satisfy $$\|u - u_n\|_{L^2} \le c_1 h^2 \quad
(12.3.19), \qquad \|u - \hat u_n\|_{L^2} \le c_2 h^4 \quad (12.3.20).$$

The two estimates that the source states without proof are
`AtkinsonHan.Chapter12.norm_sub_comp_expKernelCLM_le`, $\|K - P_n K\| = O(h^2)$, and
`AtkinsonHan.Chapter12.norm_sub_discGalerkinProj_expSolution_le`, $\|u - P_n u\| = O(h^2)$. With
them, (12.3.19) is `AtkinsonHan.Chapter12.equation_12_1_24` and (12.3.20) is
`AtkinsonHan.Chapter12.equation_12_3_11`, whose right-hand side is the product of the two.
Unique solvability comes from `AtkinsonHan.Chapter12.theorem_12_1_2`, and $50 - K$ is invertible
by the Neumann series, because $\|K\| \le e < 50$. The source does not give $c_1$ and $c_2$; the
proof gives $c_1 = 25 e \|(50 - K)^{-1}\| / 2$ and a $c_2$ of the same form. Table 12.2 of
measured errors is not formalized. -/
theorem example_12_3_2 :
    ∃ c₁ c₂ : ℝ, ∀ᶠ n : ℕ in atTop,
      (∀ f : L², ∃! un : L²,
        IsProjectionSolution (50 : ℝ) expKernelCLM (discGalerkinProj n) f un) ∧
      ∀ un : L²,
        IsProjectionSolution (50 : ℝ) expKernelCLM (discGalerkinProj n) expRhs un →
          ‖expSolution - un‖ ≤ c₁ * (1 / (n : ℝ)) ^ 2 ∧
          ‖expSolution - iteratedSolution (50 : ℝ) expKernelCLM expRhs un‖
            ≤ c₂ * (1 / (n : ℝ)) ^ 4 := by
  obtain ⟨e, he⟩ := exists_equiv_smul_sub_of_norm_lt (μ := (50 : ℝ)) (by norm_num)
    norm_expKernelCLM_lt
  set A : ℝ := ‖(e.symm : L² →L[ℝ] L²)‖ with hAdef
  have hA0 : (0 : ℝ) ≤ A := norm_nonneg _
  set B : ℝ := 1 / 50 * (1 + Real.exp 1 * (2 * A)) with hBdef
  refine ⟨50 * (2 * A) * (Real.exp 1 / 8), B * (Real.exp 1 / 8) * (Real.exp 1 / 8), ?_⟩
  have hu : ((50 : ℝ) • 1 - expKernelCLM : L² →L[ℝ] L²) expSolution = expRhs := rfl
  have htend : Tendsto (fun n : ℕ => A * ((1 / (n : ℝ)) ^ 2 / 8 * Real.exp 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (1 / (n : ℝ))) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have h2 := ((h1.pow 2).div_const 8).const_mul (Real.exp 1)
    simpa [mul_comm, mul_left_comm, mul_assoc] using h2.const_mul A
  filter_upwards [eventually_gt_atTop 0,
    htend.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num))] with n hn hsmall
  have hKP := norm_sub_comp_expKernelCLM_le hn
  have hprod : A * ‖expKernelCLM - discGalerkinProj n ∘L expKernelCLM‖ < 1 / 2 :=
    lt_of_le_of_lt (by gcongr) hsmall
  obtain ⟨e', he'coe, he'norm, huniq⟩ := theorem_12_1_2 (μ := (50 : ℝ)) (by norm_num)
    (isIdempotentElem_discGalerkinProj n) e he (by rw [← hAdef]; linarith)
  have hb1 : ‖(e'.symm : L² →L[ℝ] L²)‖ ≤ 2 * A := by
    refine he'norm.trans ?_
    rw [← hAdef, div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg (expKernelCLM - discGalerkinProj n ∘L expKernelCLM)]
  refine ⟨huniq, fun un hun => ⟨?_, ?_⟩⟩
  · -- (12.3.19), from (12.1.24)
    have hkey := (equation_12_1_24 (isIdempotentElem_discGalerkinProj n) he'coe hu hun).2
    have hproj := norm_sub_discGalerkinProj_expSolution_le hn
    calc ‖expSolution - un‖
        ≤ ‖(50 : ℝ)‖ * ‖(e'.symm : L² →L[ℝ] L²)‖
            * ‖expSolution - discGalerkinProj n expSolution‖ := hkey
      _ ≤ 50 * (2 * A) * ((1 / (n : ℝ)) ^ 2 / 8 * Real.exp 1) := by
          rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 50)]
          gcongr
      _ = 50 * (2 * A) * (Real.exp 1 / 8) * (1 / (n : ℝ)) ^ 2 := by ring
  · -- (12.3.20), from (12.3.11)
    obtain ⟨e'', he''coe, -, he''norm⟩ := lemma_12_3_1_projection (μ := (50 : ℝ)) (by norm_num)
      expKernelCLM (discGalerkinProj n) he'coe
    have hP : ‖discGalerkinProj n‖ ≤ 1 :=
      norm_discPiecewiseLinearProjCLM_le_one 0 1 (n - 1) (unitMesh n)
    have hb2 : ‖(e''.symm : L² →L[ℝ] L²)‖ ≤ B := by
      refine he''norm.trans ?_
      rw [hBdef, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 50)]
      have hep : ‖(e'.symm : L² →L[ℝ] L²)‖ * ‖discGalerkinProj n‖ ≤ 2 * A := by
        calc ‖(e'.symm : L² →L[ℝ] L²)‖ * ‖discGalerkinProj n‖
            ≤ (2 * A) * 1 := mul_le_mul hb1 hP (norm_nonneg _) (by linarith)
          _ = 2 * A := mul_one _
      have hmul : ‖expKernelCLM‖ * (‖(e'.symm : L² →L[ℝ] L²)‖ * ‖discGalerkinProj n‖)
          ≤ Real.exp 1 * (2 * A) :=
        mul_le_mul norm_expKernelCLM_le hep (by positivity) (Real.exp_nonneg 1)
      rw [inv_eq_one_div]
      exact mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
    have hkey := (equation_12_3_11 (μ := (50 : ℝ)) (by norm_num)
      (isIdempotentElem_discGalerkinProj n) he''coe hu hun).2
    have hproj := norm_sub_discGalerkinProj_expSolution_le hn
    have hcomp := norm_expKernelCLM_comp_sub_discGalerkinProj_le hn
    calc ‖expSolution - iteratedSolution (50 : ℝ) expKernelCLM expRhs un‖
        ≤ ‖(e''.symm : L² →L[ℝ] L²)‖ * ‖expKernelCLM ∘L (1 - discGalerkinProj n)‖
            * ‖expSolution - discGalerkinProj n expSolution‖ := hkey
      _ ≤ B * ((1 / (n : ℝ)) ^ 2 / 8 * Real.exp 1) * ((1 / (n : ℝ)) ^ 2 / 8 * Real.exp 1) := by
          have hB0 : (0 : ℝ) ≤ B := le_trans (norm_nonneg _) hb2
          have hX0 : (0 : ℝ) ≤ (1 / (n : ℝ)) ^ 2 / 8 * Real.exp 1 := by positivity
          exact mul_le_mul (mul_le_mul hb2 hcomp (norm_nonneg _) hB0) hproj (norm_nonneg _)
            (mul_nonneg hB0 hX0)
      _ = B * (Real.exp 1 / 8) * (Real.exp 1 / 8) * (1 / (n : ℝ)) ^ 4 := by ring

end IteratedGalerkin

end AtkinsonHan.Chapter12

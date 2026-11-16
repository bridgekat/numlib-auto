/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Subdifferential.Differentiability
import Numlib.Analysis.Convex.Subdifferential.EssentiallySmooth

/-!
# Essential smoothness in terms of directional derivatives

Let $E$ be a finite-dimensional real inner product space, let $f : E \to [-\infty, +\infty]$ be
closed, proper and convex, and let $C = \operatorname{int}(\operatorname{dom} f)$. Essential
smoothness (`ConvexAnalysis.EssentiallySmooth`) asks that (a) $C$ is nonempty, (b) $f$ is
differentiable on $C$, and (c) $\|\nabla f(x_i)\| \to \infty$ for every sequence in $C$ that
converges to a point outside $C$. Given (a) and (b), condition (c) can be replaced by
$$\text{(c')} \qquad f'(x + \lambda (a - x); a - x) \to -\infty \text{ as } \lambda \downarrow 0,
  \quad \text{for every } a \in C \text{ and every } x \notin C.$$
This is Lemma 26.2 of [rockafellar1970convex].

At a single point $x$, both conditions say that $\partial f(x) = \emptyset$. For (c) this holds
because $\partial f$ has a closed graph and is recovered from limits of gradients. For (c') it holds
because, along the line through $x$ and $a$, the directional derivative tends to $-\infty$ exactly
when $\partial f(x)$ is empty. The two halves are separate theorems, so each can be used alone. The
proofs restrict $f$ to a line and use the theory of convex functions of one variable.

## Main results

* `ConvexAnalysis.closedProperConvexFn_lineRestrict`: the restriction $t \mapsto f(x + t y)$ of a
  closed proper convex function to a line that meets $\operatorname{dom} f$ is closed, proper and
  convex, for any base point $x$ of the line.
* `ConvexAnalysis.subdifferential_eq_empty_iff_tendsto_dirDeriv`,
  `ConvexAnalysis.subdifferential_eq_empty_iff_tendsto_norm_fderiv`: condition (c') at $x$ and
  condition (c) at $x$ each say that $\partial f(x) = \emptyset$.
* `ConvexAnalysis.essentiallySmooth_iff_tendsto_dirDeriv`: given (a) and (b), essential smoothness
  is equivalent to (c'). This is Lemma 26.2 of [rockafellar1970convex].

## Implementation notes

* The function $f$ is assumed closed. [rockafellar1970convex] instead replaces $f$ by
  $\operatorname{cl} f$ "without loss of generality". Every use of these results already has the
  hypothesis `ConvexAnalysis.ClosedConvex f`.
* Condition (c') is stated as convergence to $-\infty$ (`Filter.Tendsto` to `𝓝 ⊥`). The arrow
  $\downarrow$ in [rockafellar1970convex] also records that
  $\lambda \mapsto f'(x + \lambda (a - x); a - x)$ is monotone, but only the value of the limit is
  used.
* The gradient in condition (c) is the Fréchet derivative `fderiv ℝ (fun w => (f w).toReal)` of the
  real values of $f$, and $\|\nabla f\|$ is its operator norm.
-/

namespace ConvexAnalysis

open Filter Metric Topology

/-! ### The restriction to a line, based at an arbitrary point -/

section LineRestrict

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → EReal} {x y : E}

/-- Let $E$ be a real normed space and let $f : E \to [-\infty, +\infty]$ be proper and closed. Then
for all $x, y \in E$ the restriction $t \mapsto f(x + t y)$ of $f$ to a line is closed. -/
theorem closedConvex_lineRestrict (hp : ProperConvex f) (hcl : ClosedConvex f) (x y : E) :
    ClosedConvex fun t : ℝ => f (x + t • y) := by
  have hcont : Continuous fun s : ℝ => x + s • y := by fun_prop
  exact (closedConvex_iff_lowerSemicontinuous fun _ => hp.ne_bot _).2 fun t c hc =>
    (hcont.tendsto t).eventually (hcl.lowerSemicontinuous _ c hc)

/-- Let $f$ be proper. If the line $t \mapsto x + t y$ meets $\operatorname{dom} f$, then the
restriction $t \mapsto f(x + t y)$ is proper.

Unlike `ConvexAnalysis.properConvex_lineRestrict`, this does not require the base point $x$ to
lie in $\operatorname{dom} f$. Here $x$ is exactly the point that may lie outside
$\operatorname{dom} f$. -/
theorem properConvex_lineRestrict_of_mem_convexDom (hp : ProperConvex f) {t₀ : ℝ}
    (ht : x + t₀ • y ∈ convexDom f) :
    ProperConvex fun t : ℝ => f (x + t • y) :=
  ⟨⟨t₀, ht⟩, fun _ => hp.ne_bot _⟩

/-- Let $E$ be a real normed space, let $f : E \to [-\infty, +\infty]$ be closed, proper and convex,
and let $x, y \in E$ with $x + t_0 y \in \operatorname{dom} f$ for some $t_0 \in \mathbb{R}$.
Then the restriction
$$g(t) = f(x + t y), \qquad t \in \mathbb{R},$$
is a closed proper convex function on $\mathbb{R}$.

The base point $x$ need not lie in $\operatorname{dom} f$. The theory of closed proper convex
functions of one variable then applies to $g$. -/
theorem closedProperConvexFn_lineRestrict (hf : ConvexFn f) (hp : ProperConvex f)
    (hcl : ClosedConvex f)
    {t₀ : ℝ} (ht : x + t₀ • y ∈ convexDom f) :
    ClosedProperConvexFn fun t : ℝ => f (x + t • y) :=
  ⟨convexFn_lineRestrict hf x y, closedConvex_lineRestrict hp hcl x y,
    properConvex_lineRestrict_of_mem_convexDom hp ht⟩

/-- Let $f$ be proper, let $x, y \in E$, and let $g(s) = f(x + s y)$. If $f(x + s y) < +\infty$ for
some $s > t$, then the right derivative of $g$ at $t$ is the directional derivative of $f$ along
the line:
$$g'_+(t) = f'(x + t y; y).$$

Both sides are $-\infty$ where $f(x + t y) = +\infty$. Without the hypothesis, $g'_+(t)$ is
$+\infty$ by the convention of `ConvexAnalysis.rightDeriv`, and the two sides differ. -/
theorem rightDeriv_lineRestrict_eq_dirDeriv (hp : ProperConvex f) (x y : E) {t : ℝ}
    (ht : ∃ s, t < s ∧ f (x + s • y) < ⊤) :
    rightDeriv (fun s : ℝ => f (x + s • y)) t = dirDeriv f (x + t • y) y := by
  rcases eq_or_lt_of_le (le_top : f (x + t • y) ≤ ⊤) with htop | htop
  · rw [rightDeriv_eq_bot_of_eq_top htop ht, dirDeriv_eq_bot_of_eq_top htop y]
  · rw [rightDeriv_eq_dirDeriv htop (hp.ne_bot _), dirDeriv_lineRestrict, one_smul]

end LineRestrict

/-! ### The directional derivative along a segment -/

section LineSegment

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → EReal} {a : E}

/-- Let $f$ be closed, proper and convex, let $a \in \operatorname{dom} f$, and let $x \in E$. Let
$g(s) = f(x + s(a - x))$ be the restriction of $f$ to the line through $x$ and $a$. Then
$$f'(x + t(a - x); a - x) \to g'_+(0) \quad \text{as } t \downarrow 0.$$
-/
theorem tendsto_dirDeriv_lineRestrict (hf : ConvexFn f) (hp : ProperConvex f) (hcl : ClosedConvex f)
    (ha : a ∈ convexDom f) (x : E) :
    Tendsto (fun t : ℝ => dirDeriv f (x + t • (a - x)) (a - x)) (𝓝[>] 0)
      (𝓝 (rightDeriv (fun s : ℝ => f (x + s • (a - x))) 0)) := by
  set y : E := a - x with hy
  have hone : x + (1 : ℝ) • y = a := by rw [hy]; module
  have hcpc : ClosedProperConvexFn fun s : ℝ => f (x + s • y) :=
    closedProperConvexFn_lineRestrict hf hp hcl (t₀ := 1) (by rw [hone]; exact ha)
  refine (tendsto_rightDeriv_nhdsWithin_Ioi hcpc 0).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
  exact rightDeriv_lineRestrict_eq_dirDeriv hp x y ⟨1, ht.2, by rw [hone]; exact mem_convexDom.1 ha⟩

end LineSegment

/-! ### Condition (c') at a single point -/

section Condition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {a x : E}


/-- Let $E$ be a finite-dimensional real inner product space, let $f$ be proper and convex, let
$a \in \operatorname{ri}(\operatorname{dom} f)$, and let $x \in E$. Let
$g(s) = f(x + s(a - x))$. Then $g'_+(0) = -\infty$ if and only if $\partial f(x) = \emptyset$.

Off $\operatorname{dom} f$ both sides hold. On $\operatorname{dom} f$ the right derivative is
$f'(x; a - x)$, which is $-\infty$ exactly when $\partial f(x)$ is empty. -/
theorem rightDeriv_lineRestrict_zero_eq_bot_iff (hf : ConvexFn f) (hp : ProperConvex f)
    (ha : a ∈ ri (convexDom f)) (x : E) :
    rightDeriv (fun s : ℝ => f (x + s • (a - x))) 0 = ⊥ ↔ subdifferential (innerₗ E) f x = ∅ := by
  set y : E := a - x with hy
  have hone : x + (1 : ℝ) • y = a := by rw [hy]; module
  have hex : ∃ s, (0 : ℝ) < s ∧ f (x + s • y) < ⊤ :=
    ⟨1, zero_lt_one, by rw [hone]; exact mem_convexDom.1 (intrinsicInterior_subset ha)⟩
  rw [rightDeriv_lineRestrict_eq_dirDeriv hp x y hex, zero_smul, add_zero]
  rcases eq_or_lt_of_le (le_top : f x ≤ ⊤) with htop | htop
  · refine ⟨fun _ => ?_, fun _ => dirDeriv_eq_bot_of_eq_top htop y⟩
    refine Set.eq_empty_of_forall_notMem fun v hv => ?_
    exact absurd (mem_convexDom.1 (mem_convexDom_of_mem_subdifferential hp hv)) (by rw [htop]; simp)
  · refine ⟨fun hbot => ?_, fun hempty => ?_⟩
    · exact (subdifferential_eq_empty_iff_exists_dirDeriv_eq_bot (B := innerₗ E) hf htop.ne
        (hp.ne_bot x)).2 ⟨y, hbot⟩
    · have h := dirDeriv_eq_bot_of_subdifferential_eq_empty (B := innerₗ E) hf htop.ne
        (hp.ne_bot x) hempty ha
      rwa [hy]

/-- Let $E$ be a finite-dimensional real inner product space, let $f : E \to [-\infty, +\infty]$ be
closed, proper and convex, let $a \in \operatorname{ri}(\operatorname{dom} f)$, and let
$x \in E$. Then
$$\partial f(x) = \emptyset \iff f'(x + t(a - x); a - x) \to -\infty \text{ as } t \downarrow
  0.$$

This is condition (c') at the point $x$ in the direction of $a$. The subdifferential is taken
for the inner product `innerₗ E`. -/
theorem subdifferential_eq_empty_iff_tendsto_dirDeriv (hf : ConvexFn f) (hp : ProperConvex f)
    (hcl : ClosedConvex f) (ha : a ∈ ri (convexDom f)) (x : E) :
    subdifferential (innerₗ E) f x = ∅ ↔
      Tendsto (fun t : ℝ => dirDeriv f (x + t • (a - x)) (a - x)) (𝓝[>] 0) (𝓝 ⊥) := by
  have htend := tendsto_dirDeriv_lineRestrict hf hp hcl (intrinsicInterior_subset ha) x
  refine ⟨fun hempty => ?_, fun hlim => ?_⟩
  · rwa [(rightDeriv_lineRestrict_zero_eq_bot_iff hf hp ha x).2 hempty] at htend
  · exact (rightDeriv_lineRestrict_zero_eq_bot_iff hf hp ha x).1
      (tendsto_nhds_unique htend hlim)

/-- Let $E$ be a finite-dimensional real inner product space, let $f : E \to [-\infty, +\infty]$ be
closed, proper and convex, let $C = \operatorname{int}(\operatorname{dom} f)$ be nonempty, and
let $f$ be differentiable at every point of $C$. Then for every $x \in E$,
$\partial f(x) = \emptyset$ if and only if $\|\nabla f(z_i)\| \to \infty$ for every sequence
$(z_i)$ in $C$ with $z_i \to x$.

This is condition (c) at the point $x$. For the forward implication, a bounded subsequence of
gradients has a convergent subsequence whose limit is a subgradient at $x$. For the reverse
implication, a subgradient at $x$ is built from limits of gradients, which gives a convergent
sequence of gradients and contradicts condition (c). The gradient is
`fderiv ℝ (fun w => (f w).toReal)`. -/
theorem subdifferential_eq_empty_iff_tendsto_norm_fderiv (hf : ConvexFn f) (hp : ProperConvex f)
    (hcl : ClosedConvex f) (hne : (interior (convexDom f)).Nonempty)
    (hdiff : ∀ ⦃z : E⦄, z ∈ interior (convexDom f) → DifferentiableAtFn f z) (x : E) :
    subdifferential (innerₗ E) f x = ∅ ↔
      ∀ zs : ℕ → E, (∀ i, zs i ∈ interior (convexDom f)) → Tendsto zs atTop (𝓝 x) →
        Tendsto (fun i => ‖fderiv ℝ (fun w => (f w).toReal) (zs i)‖) atTop atTop := by
  constructor
  · intro hempty zs hzs hlim
    by_contra hcon
    -- A bounded subsequence of gradients, converging after a second extraction.
    obtain ⟨b, hb⟩ := not_forall.1 (Filter.tendsto_atTop.not.1 hcon)
    obtain ⟨φ, hφ, hφb⟩ := Filter.extraction_of_frequently_atTop (Filter.not_eventually.1 hb)
    set vs : ℕ → E := fun i => (InnerProductSpace.toDual ℝ E).symm
      (fderiv ℝ (fun w => (f w).toReal) (zs i)) with hvsdef
    have hgrad : ∀ i, HasGradientAtFn f (InnerProductSpace.toDual ℝ E (vs i)) (zs i) := fun i => by
      rw [hvsdef, LinearIsometryEquiv.apply_symm_apply]
      exact (hdiff (hzs i)).hasGradientAtFn_fderiv
    have hvsb : ∀ n, vs (φ n) ∈ closedBall (0 : E) b := fun n => by
      rw [mem_closedBall_zero_iff, hvsdef, LinearIsometryEquiv.norm_map]
      exact (not_le.1 (hφb n)).le
    obtain ⟨w, -, ψ, hψ, hψlim⟩ := (isCompact_closedBall (0 : E) b).tendsto_subseq hvsb
    have hmem : w ∈ gradientLimits f x :=
      ⟨fun n => zs (φ (ψ n)), fun n => vs (φ (ψ n)), hlim.comp (hφ.comp hψ).tendsto_atTop,
        fun n => hgrad (φ (ψ n)), hψlim⟩
    exact absurd (gradientLimits_subset_subdifferential hf hp hcl hmem) (by rw [hempty]; simp)
  · intro hc
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨v, hv⟩
    -- A subgradient is built from limits of gradients, by convex hull and normal cone.
    rw [subdifferential_eq_closure_convexHull_gradientLimits_add_normalCone hf hp hcl hne] at hv
    obtain ⟨u, hu, -, -, -⟩ := hv
    obtain ⟨w, xs, vs, hxs, hgrad, hvs⟩ : (gradientLimits f x).Nonempty := by
      rcases (gradientLimits f x).eq_empty_or_nonempty with hempty | hne'
      · rw [hempty, convexHull_empty, closure_empty] at hu
        exact absurd hu (Set.notMem_empty u)
      · exact hne'
    have hnorm : ∀ i, ‖fderiv ℝ (fun z => (f z).toReal) (xs i)‖ = ‖vs i‖ := fun i => by
      rw [(hgrad i).fderiv_toReal_eq, LinearIsometryEquiv.norm_map]
    have htop := hc xs (fun i => (hgrad i).mem_interior_convexDom) hxs
    rw [tendsto_congr hnorm] at htop
    exact not_tendsto_atTop_of_tendsto_nhds hvs.norm htop

/-- Let $E$ be a finite-dimensional real inner product space, let $f$ be closed, proper and convex,
let $C = \operatorname{int}(\operatorname{dom} f)$ be nonempty, let $f$ be differentiable on
$C$, and let $a \in C$. Then for every $x \in E$, condition (c) at $x$ holds if and only if
condition (c') holds at $x$ in the direction of $a$: $\|\nabla f(z_i)\| \to \infty$ for every
sequence $(z_i)$ in $C$ with $z_i \to x$ if and only if $f'(x + t(a - x); a - x) \to -\infty$ as
$t \downarrow 0$. -/
theorem tendsto_norm_fderiv_iff_tendsto_dirDeriv (hf : ConvexFn f) (hp : ProperConvex f)
    (hcl : ClosedConvex f) (hne : (interior (convexDom f)).Nonempty)
    (hdiff : ∀ ⦃z : E⦄, z ∈ interior (convexDom f) → DifferentiableAtFn f z)
    (ha : a ∈ interior (convexDom f)) (x : E) :
    (∀ zs : ℕ → E, (∀ i, zs i ∈ interior (convexDom f)) → Tendsto zs atTop (𝓝 x) →
        Tendsto (fun i => ‖fderiv ℝ (fun w => (f w).toReal) (zs i)‖) atTop atTop)
      ↔ Tendsto (fun t : ℝ => dirDeriv f (x + t • (a - x)) (a - x)) (𝓝[>] 0) (𝓝 ⊥) :=
  (subdifferential_eq_empty_iff_tendsto_norm_fderiv hf hp hcl hne hdiff x).symm.trans
    (subdifferential_eq_empty_iff_tendsto_dirDeriv hf hp hcl
      (Convex.interior_subset_relint ha) x)

/-- Let $E$ be a finite-dimensional real inner product space, let $f : E \to [-\infty, +\infty]$ be
closed, proper and convex, let $C = \operatorname{int}(\operatorname{dom} f)$ be nonempty, and
let $f$ be differentiable at every point of $C$. Then $f$ is essentially smooth if and only if
$$f'(x + t(a - x); a - x) \to -\infty \text{ as } t \downarrow 0 \quad \text{for every } x
  \notin C \text{ and every } a \in C.$$

This is Lemma 26.2 of [rockafellar1970convex]. Essential smoothness is
`ConvexAnalysis.EssentiallySmooth`. The hypotheses are its conditions (a) and (b), and the
equivalence replaces condition (c) by condition (c'). -/
theorem essentiallySmooth_iff_tendsto_dirDeriv (hf : ConvexFn f) (hp : ProperConvex f)
    (hcl : ClosedConvex f)
    (hne : (interior (convexDom f)).Nonempty)
    (hdiff : ∀ ⦃z : E⦄, z ∈ interior (convexDom f) → DifferentiableAtFn f z) :
    EssentiallySmooth f ↔ ∀ x ∉ interior (convexDom f), ∀ a ∈ interior (convexDom f),
      Tendsto (fun t : ℝ => dirDeriv f (x + t • (a - x)) (a - x)) (𝓝[>] 0) (𝓝 ⊥) := by
  constructor
  · intro hes x hx a haC
    exact (tendsto_norm_fderiv_iff_tendsto_dirDeriv hf hp hcl hne hdiff haC x).1
      (hes.tendsto_norm_fderiv hx)
  · intro hc
    obtain ⟨a, haC⟩ := id hne
    exact ⟨hne, hdiff, fun z hz =>
      (tendsto_norm_fderiv_iff_tendsto_dirDeriv hf hp hcl hne hdiff haC z).2 (hc z hz a haC)⟩

end Condition

end ConvexAnalysis

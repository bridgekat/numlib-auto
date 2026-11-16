/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Convex.Exposed
import Numlib.Analysis.Convex.Convergence
import Numlib.Analysis.Convex.Subdifferential.Bounded

/-!
# Convergence of directional derivatives and of subgradients

Let $E$ be a finite-dimensional real normed space, let $U \subseteq E$ be open and convex, and let
convex functions $f_i$, finite on $U$, converge pointwise on $U$ to a convex function $g$. Then the
convergence is uniform on compact subsets of $U$, hence continuous: $f_i(x_i) \to g(x)$ for every
sequence $x_i \to x \in U$. Derivatives do not pass to the limit; only an inequality for the upper
limit holds. For $x_i \to x \in U$ and $y_i \to y$,
$$\limsup_{i \to \infty} f_i'(x_i; y_i) \le g'(x; y), \qquad \partial f_i(x_i) \subseteq \partial
  g(x) + \varepsilon B \text{ for all large } i,$$
for every $\varepsilon > 0$, where $B$ is the closed unit ball. Equality can fail: for
$f_i(x) = |x|^{p_i}$ with $p_i \downarrow 1$ on $U = \mathbb{R}$, every $f_i'(0; 1)$ is $0$, while
$g'(0; 1) = 1$. For a constant sequence $f_i = f$, the two statements give upper semicontinuity of
$(x, y) \mapsto f'(x; y)$ and of $x \mapsto \partial f(x)$. The module also treats an approach
$x_i \to x$ to a point of $\operatorname{dom} f$ that need not be interior, along a limiting
direction $y$. The presentation follows [rockafellar1970convex], §24.

## Main results

* `ConvexAnalysis.tendsto_eval_of_tendsto`: continuous convergence, $f_i(x_i) \to g(x)$.
* `ConvexAnalysis.eventually_dirDeriv_lt`,
  `ConvexAnalysis.eventually_subdifferential_subset_add_closedBall`: the two displayed statements.
  This is Theorem 24.5 of [rockafellar1970convex].
* `ConvexAnalysis.upperSemicontinuousAt_dirDeriv`,
  `ConvexAnalysis.eventually_nhds_subdifferential_subset_add_closedBall`: for one function $f$,
  upper semicontinuity of $f'(x; y)$ in $(x, y)$ and of $\partial f$ at interior points of
  $\operatorname{dom} f$.
* `ConvexAnalysis.eventually_dirDeriv_lt_of_tendsto_dir`,
  `ConvexAnalysis.eventually_subdifferential_subset_exposed_add_closedBall`: the same two statements
  for an approach to a point $x \in \operatorname{dom} f$ that need not be interior, along a
  limiting direction $y$. The bound is the directional derivative of $f'(x; \cdot)$ at $y$, and the
  face of $\partial f(x)$ exposed by $y$ replaces $\partial f(x)$. This is Theorem 24.6 of
  [rockafellar1970convex].
* `ConvexAnalysis.subdifferential_dirDeriv`: $\partial (f'(x; \cdot))(y)$ is the face of
  $\partial f(x)$ on which $\langle y, \cdot \rangle$ attains its maximum.

## Implementation notes

* The upper limit is stated without values at infinity: every real $\mu$ above $g'(x; y)$ is
  eventually an upper bound of $f_i'(x_i; y_i)$.
* The convergence theory of `Numlib.Analysis.Convex.Convergence` is for real-valued functions that
  are convex on $U$ (`ConvexOn ℝ U`), while subgradients are for functions with values in
  $[-\infty, +\infty]$. The link is `ConvexAnalysis.ConvexFn.convexOn_toReal_convexDom`.
* The ball $\varepsilon B$ needs a norm on the dual space, so the statements about subgradients are
  for a real inner product space paired with itself by `innerₗ E`.
* Two classical hypotheses are not needed. The sequence $(x_i)$ need not lie in $U$; it only has to
  converge to a point of $U$. The approach to a boundary point needs neither closedness of $f$ nor
  the usual construction with a simplex: monotonicity of the difference quotient in its step
  replaces the vanishing step $\|x_i - x\|$ by a fixed larger step, and after that only continuity
  at interior points is used.
-/

open Set Filter Topology
open scoped NNReal Pointwise RealInnerProductSpace

namespace ConvexAnalysis

/-! ### The support function of a ball -/

section Ball

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Let $E$ be a real inner product space and $\varepsilon \ge 0$. The support function of the
closed ball of radius $\varepsilon$ about the origin is $\varepsilon \| \cdot \|$:
$$\sup_{\|x\| \le \varepsilon} \langle x, y \rangle = \varepsilon \|y\| \quad \text{for all } y
  \in E.$$
-/
theorem supportFn_closedBall {ε : ℝ} (hε : 0 ≤ ε) (y : E) :
    supportFn (innerₗ E) (Metric.closedBall (0 : E) ε) y = ((ε * ‖y‖ : ℝ) : EReal) := by
  refine le_antisymm (supportFn_le_coe_iff.2 fun z hz => ?_) ?_
  · rw [Metric.mem_closedBall, dist_zero_right] at hz
    have hcs : (innerₗ E) z y ≤ ‖z‖ * ‖y‖ := by
      rw [innerₗ_apply_apply]; exact real_inner_le_norm z y
    exact hcs.trans (by gcongr)
  · rcases eq_or_ne y 0 with rfl | hy
    · have h0 : (0 : E) ∈ Metric.closedBall (0 : E) ε := Metric.mem_closedBall_self hε
      have h := le_supportFn (B := innerₗ E) h0 (0 : E)
      simpa using h
    have hmem : (ε / ‖y‖) • y ∈ Metric.closedBall (0 : E) ε := by
      have hpos : (0 : ℝ) ≤ ε / ‖y‖ := by positivity
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hpos]
      field_simp
      exact le_rfl
    have h := le_supportFn (B := innerₗ E) hmem y
    have hval : (innerₗ E) ((ε / ‖y‖) • y) y = ε * ‖y‖ := by
      rw [innerₗ_apply_apply, real_inner_smul_left, real_inner_self_eq_norm_mul_norm]
      field_simp
    rwa [hval] at h

end Ball

/-! ### The directional derivative at an interior point -/

section Interior

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {g : E → EReal} {x : E}

/-- Let $E$ be finite-dimensional, let $g$ be proper and convex, and let
$x \in \operatorname{int}(\operatorname{dom} g)$. Then $g'(x; z)$ is finite for every $z$, so it
is equal to the real number `(dirDeriv g x z).toReal`, viewed in $[-\infty, +\infty]$. -/
theorem dirDeriv_eq_coe_toReal_of_mem_interior_convexDom (hg : ConvexFn g) (hgp : ProperConvex g)
    (hx : x ∈ interior (convexDom g)) (z : E) :
    dirDeriv g x z = (((dirDeriv g x z).toReal : ℝ) : EReal) := by
  have hri : x ∈ ri (convexDom g) := Convex.interior_subset_relint hx
  have hbot : dirDeriv g x z ≠ ⊥ :=
      (properConvex_dirDeriv_of_mem_relint_convexDom hg hgp hri).ne_bot z
  have hdom := (convexDom_dirDeriv_eq_univ_iff_mem_interior_convexDom hg hgp hri).2 hx
  have htop : dirDeriv g x z ≠ ⊤ := (mem_convexDom.1 (hdom ▸ Set.mem_univ z)).ne
  exact (EReal.coe_toReal htop hbot).symm

/-- Let $E$ be finite-dimensional, let $g$ be proper and convex, and let
$x \in \operatorname{int}(\operatorname{dom} g)$. Then the real-valued function
$z \mapsto g'(x; z)$ is convex on all of $E$. -/
theorem convexOn_toReal_dirDeriv (hg : ConvexFn g) (hgp : ProperConvex g)
    (hx : x ∈ interior (convexDom g)) :
    ConvexOn ℝ (univ : Set E) fun z => (dirDeriv g x z).toReal := by
  have hri : x ∈ ri (convexDom g) := Convex.interior_subset_relint hx
  have hdom := (convexDom_dirDeriv_eq_univ_iff_mem_interior_convexDom hg hgp hri).2 hx
  have hxdom : x ∈ convexDom g := interior_subset hx
  have h :=
      (convexFn_dirDeriv hg (mem_convexDom.1 hxdom).ne (hgp.ne_bot x)).convexOn_toReal_convexDom
    (properConvex_dirDeriv_of_mem_relint_convexDom hg hgp hri)
  rwa [hdom] at h

/-- Let $E$ be finite-dimensional, let $g$ be proper and convex, let
$x \in \operatorname{int}(\operatorname{dom} g)$, and let $c > 0$. Then
$g'(x; cz) = c \, g'(x; z)$ for every $z$, as an equation of real numbers. -/
theorem toReal_dirDeriv_smul (hg : ConvexFn g) (hgp : ProperConvex g)
    (hx : x ∈ interior (convexDom g))
    {c : ℝ} (hc : 0 < c) (z : E) :
    (dirDeriv g x (c • z)).toReal = c * (dirDeriv g x z).toReal := by
  have h := posHomogeneous_dirDeriv g x c hc z
  rw [dirDeriv_eq_coe_toReal_of_mem_interior_convexDom hg hgp hx z, ← EReal.coe_mul] at h
  rw [h, EReal.toReal_coe]

end Interior

/-! ### Continuous convergence -/

section Eval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {U : Set E} {f : ℕ → E → ℝ} {g : E → ℝ}

/-- Let $E$ be a finite-dimensional real normed space, let $U \subseteq E$ be open and convex, and
let $f_i : E \to \mathbb{R}$ and $g : E \to \mathbb{R}$ be convex on $U$, with $f_i(z) \to g(z)$
for every $z \in U$. Then the convergence is continuous on $U$: for every $x \in U$ and every
sequence $x_i \to x$,
$$f_i(x_i) \to g(x).$$

The sequence $(x_i)$ need not lie in $U$. This is the practical form of the fact that pointwise
convergence of convex functions on an open convex set is uniform on compact subsets. -/
theorem tendsto_eval_of_tendsto (hU : IsOpen U) (hUc : Convex ℝ U)
    (hf : ∀ i, ConvexOn ℝ U (f i)) (hg : ConvexOn ℝ U g)
    (hconv : ∀ z ∈ U, Tendsto (fun i => f i z) atTop (𝓝 (g z)))
    {x : E} (hx : x ∈ U) {xs : ℕ → E} (hxs : Tendsto xs atTop (𝓝 x)) :
    Tendsto (fun i => f i (xs i)) atTop (𝓝 (g x)) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU x hx
  have hhalf : 0 < r / 2 := by linarith
  have hSU : Metric.closedBall x (r / 2) ⊆ U := fun z hz =>
    hball (Metric.closedBall_subset_ball (by linarith) hz)
  have huc := tendstoUniformlyOn_of_tendsto hU hUc hf hconv
    (isCompact_closedBall x (r / 2)) hSU
  have hcont : ContinuousWithinAt g (Metric.closedBall x (r / 2)) x := by
    have hgU : ContinuousOn g U := by
      rw [← hU.interior_eq]; exact hg.continuousOn_interior
    exact ((hgU.continuousAt (hU.mem_nhds hx)).continuousWithinAt)
  have hnw : Tendsto xs atTop (𝓝[Metric.closedBall x (r / 2)] x) :=
    tendsto_nhdsWithin_iff.2 ⟨hxs, hxs.eventually_mem (Metric.closedBall_mem_nhds x hhalf)⟩
  exact huc.tendsto_comp hcont hnw

end Eval

/-! ### Upper semicontinuity of the directional derivative -/

section DirDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {U : Set E} {f : ℕ → E → EReal} {g : E → EReal}

/-- **Upper semicontinuity of directional derivatives under pointwise convergence.** Let $E$ be a
finite-dimensional real normed space, and let $U \subseteq E$ be open and convex. Let
$f_i : E \to [-\infty, +\infty]$ and $g : E \to [-\infty, +\infty]$ be proper and convex, with
$U \subseteq \operatorname{dom} f_i$ for every $i$ and $U \subseteq \operatorname{dom} g$, and
let $f_i(z) \to g(z)$ for every $z \in U$. Let $x_i \to x \in U$ and $y_i \to y$. Then
$$\limsup_{i \to \infty} f_i'(x_i; y_i) \le g'(x; y),$$
in the form: for every real $\mu > g'(x; y)$, $f_i'(x_i; y_i) < \mu$ for all large $i$.

This is the first assertion of Theorem 24.5 of [rockafellar1970convex]. The form with a real
$\mu$ avoids values at infinity of the upper limit. The sequence $(x_i)$ need not lie in $U$. -/
theorem eventually_dirDeriv_lt (hU : IsOpen U) (hUc : Convex ℝ U)
    (hf : ∀ i, ConvexFn (f i)) (hfp : ∀ i, ProperConvex (f i)) (hfU : ∀ i, U ⊆ convexDom (f i))
    (hg : ConvexFn g) (hgp : ProperConvex g) (hgU : U ⊆ convexDom g)
    (hconv : ∀ z ∈ U, Tendsto (fun i => f i z) atTop (𝓝 (g z)))
    {x : E} (hx : x ∈ U) {xs : ℕ → E} (hxs : Tendsto xs atTop (𝓝 x))
    {y : E} {ys : ℕ → E} (hys : Tendsto ys atTop (𝓝 y))
    {μ : ℝ} (hμ : dirDeriv g x y < (μ : EReal)) :
    ∀ᶠ i in atTop, dirDeriv (f i) (xs i) (ys i) < (μ : EReal) := by
  set F : ℕ → E → ℝ := fun i z => (f i z).toReal with hFdef
  set G : E → ℝ := fun z => (g z).toReal with hGdef
  have hgeq : ∀ z ∈ U, g z = ((G z : ℝ) : EReal) := fun z hz =>
    (EReal.coe_toReal (mem_convexDom.1 (hgU hz)).ne (hgp.ne_bot z)).symm
  have hfeq : ∀ i, ∀ z ∈ U, f i z = ((F i z : ℝ) : EReal) := fun i z hz =>
    (EReal.coe_toReal (mem_convexDom.1 (hfU i hz)).ne ((hfp i).ne_bot z)).symm
  have hFconv : ∀ i, ConvexOn ℝ U (F i) := fun i =>
    ((hf i).convexOn_toReal_convexDom (hfp i)).subset (hfU i) hUc
  have hGconv : ConvexOn ℝ U G := (hg.convexOn_toReal_convexDom hgp).subset hgU hUc
  have hconvR : ∀ z ∈ U, Tendsto (fun i => F i z) atTop (𝓝 (G z)) := by
    intro z hz
    rw [← EReal.tendsto_coe]
    have hfun : (fun i => ((F i z : ℝ) : EReal)) = fun i => f i z := by
      funext i; exact (hfeq i z hz).symm
    rw [hfun, ← hgeq z hz]
    exact hconv z hz
  -- A step `a > 0` small enough to stay in `U` and to realise a quotient below `μ`.
  obtain ⟨a₀, ha₀, hlt0⟩ := dirDeriv_lt_iff.1 hμ
  have hmemU : ∀ᶠ t in 𝓝 (0 : ℝ), x + t • y ∈ U := by
    have hc : Continuous fun t : ℝ => x + t • y := by fun_prop
    have hc0 := hc.tendsto 0
    simp only [zero_smul, add_zero] at hc0
    exact hc0.eventually_mem (hU.mem_nhds hx)
  obtain ⟨δ, hδ, hδU⟩ := Metric.eventually_nhds_iff.1 hmemU
  set a : ℝ := min a₀ (δ / 2) with hadef
  have ha : 0 < a := lt_min ha₀ (by linarith)
  have haU : x + a • y ∈ U := by
    refine hδU ?_
    rw [Real.dist_eq, sub_zero, abs_of_pos ha]
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hq : (g (x + a • y) - g x) / (a : EReal) < (μ : EReal) :=
    lt_of_le_of_lt (monotoneOn_sub_div hg (hgeq x hx) y (mem_Ioi.2 ha) (mem_Ioi.2 ha₀)
      (min_le_left _ _)) hlt0
  have hquotR : (G (x + a • y) - G x) / a < μ := by
    rw [hgeq _ haU, hgeq x hx, ← EReal.coe_sub, ← EReal.coe_div,
      EReal.coe_lt_coe_iff] at hq
    exact hq
  -- Continuous convergence at the two moving points.
  have hzs : Tendsto (fun i => xs i + a • ys i) atTop (𝓝 (x + a • y)) := hxs.add (hys.const_smul a)
  have hev1 : Tendsto (fun i => F i (xs i)) atTop (𝓝 (G x)) :=
    tendsto_eval_of_tendsto hU hUc hFconv hGconv hconvR hx hxs
  have hev2 : Tendsto (fun i => F i (xs i + a • ys i)) atTop (𝓝 (G (x + a • y))) :=
    tendsto_eval_of_tendsto hU hUc hFconv hGconv hconvR haU hzs
  have hevlt : ∀ᶠ i in atTop, (F i (xs i + a • ys i) - F i (xs i)) / a < μ :=
    ((hev2.sub hev1).div_const a).eventually_lt_const hquotR
  filter_upwards [hevlt, hxs.eventually_mem (hU.mem_nhds hx),
    hzs.eventually_mem (hU.mem_nhds haU)] with i hi hiU hiU'
  calc dirDeriv (f i) (xs i) (ys i)
      ≤ (f i (xs i + a • ys i) - f i (xs i)) / (a : EReal) := dirDeriv_le _ _ _ ha
    _ = (((F i (xs i + a • ys i) - F i (xs i)) / a : ℝ) : EReal) := by
        rw [hfeq i _ hiU', hfeq i _ hiU, ← EReal.coe_sub, ← EReal.coe_div]
    _ < (μ : EReal) := by exact_mod_cast hi

end DirDeriv

/-! ### The local form for a single function -/

section LocalDirDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {x : E}

/-- Let $E$ be a finite-dimensional real normed space, let $f : E \to [-\infty, +\infty]$ be proper
and convex, let $x \in \operatorname{int}(\operatorname{dom} f)$, and let $y \in E$. Then the
function $(z, v) \mapsto f'(z; v)$ on $E \times E$ is upper semicontinuous at $(x, y)$.

This is `ConvexAnalysis.eventually_dirDeriv_lt` for the constant sequence $f, f, f, \dots$,
transferred from sequences to the neighbourhood filter. -/
theorem upperSemicontinuousAt_dirDeriv (hf : ConvexFn f) (hfp : ProperConvex f)
    (hx : x ∈ interior (convexDom f)) (y : E) :
    UpperSemicontinuousAt (fun p : E × E => dirDeriv f p.1 p.2) (x, y) := by
  intro c hc
  obtain ⟨μ, hμ₁, hμ₂⟩ := EReal.lt_iff_exists_real_btwn.1 hc
  have h : ∀ᶠ p : E × E in 𝓝 (x, y), dirDeriv f p.1 p.2 < (μ : EReal) := by
    rw [Filter.eventually_iff_seq_eventually]
    intro ps hps
    rw [nhds_prod_eq] at hps
    exact eventually_dirDeriv_lt isOpen_interior hf.convex_convexDom.interior (fun _ => hf)
      (fun _ => hfp) (fun _ => interior_subset) hf hfp interior_subset
      (fun z _ => tendsto_const_nhds) hx hps.fst hps.snd hμ₁
  exact h.mono fun p hp => hp.trans hμ₂

end LocalDirDeriv

/-! ### Upper semicontinuity of the subdifferential -/

section Subdifferential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {U : Set E} {f : ℕ → E → EReal} {g : E → EReal} {x : E}

/-- Let $E$ be a finite-dimensional real inner product space, let $g$ be proper and convex, and let
$x \in \operatorname{ri}(\operatorname{dom} g)$. Then the support function of $\partial g(x)$ is
$g'(x; \cdot)$:
$$\sup_{y \in \partial g(x)} \langle z, y \rangle = g'(x; z) \quad \text{for all } z \in E.$$
This is the case of the inner product of
`ConvexAnalysis.dirDeriv_eq_supportFn_of_mem_relint_convexDom`. -/
theorem supportFn_subdifferential (hg : ConvexFn g) (hgp : ProperConvex g)
    (hx : x ∈ ri (convexDom g)) :
    supportFn (innerₗ E) (subdifferential (innerₗ E) g x) = dirDeriv g x := by
  rw [dirDeriv_eq_supportFn_of_mem_relint_convexDom (B := innerₗ E) hg hgp hx, flip_innerₗ]

/-- Let $p, q : E \to [-\infty, +\infty]$ be proper and convex, let
$u \in \operatorname{int}(\operatorname{dom} p)$ and
$v \in \operatorname{int}(\operatorname{dom} q)$, and let $\varepsilon > 0$. If
$p'(u; z) \le q'(v; z) + \varepsilon$ for every $z$ in the closed unit ball, then
$$\partial p(u) \subseteq \partial q(v) + \varepsilon B,$$
where $B$ is the closed unit ball.

This is the common last step of
`ConvexAnalysis.eventually_subdifferential_subset_add_closedBall` and
`ConvexAnalysis.eventually_subdifferential_subset_exposed_add_closedBall`. Positive homogeneity
extends the bound to every direction, and support functions order closed convex sets. -/
theorem subdifferential_subset_add_closedBall_of_forall_dirDeriv_le {p q : E → EReal} {u v : E}
    (hp : ConvexFn p) (hpp : ProperConvex p) (hu : u ∈ interior (convexDom p))
    (hq : ConvexFn q) (hqp : ProperConvex q) (hv : v ∈ interior (convexDom q)) {ε : ℝ} (hε : 0 < ε)
    (hb : ∀ z ∈ Metric.closedBall (0 : E) 1,
      (dirDeriv p u z).toReal ≤ (dirDeriv q v z).toReal + ε) :
    subdifferential (innerₗ E) p u
      ⊆ subdifferential (innerₗ E) q v + Metric.closedBall (0 : E) ε := by
  have huri : u ∈ ri (convexDom p) := Convex.interior_subset_relint hu
  have hvri : v ∈ ri (convexDom q) := Convex.interior_subset_relint hv
  have hhom : ∀ z : E, dirDeriv p u z ≤ (((dirDeriv q v z).toReal + ε * ‖z‖ : ℝ) : EReal) := by
    intro z
    have hreal : (dirDeriv p u z).toReal ≤ (dirDeriv q v z).toReal + ε * ‖z‖ := by
      rcases eq_or_ne z 0 with rfl | hz
      · have h1 : dirDeriv p u 0 = 0 :=
          dirDeriv_zero (mem_convexDom.1 (interior_subset hu)).ne (hpp.ne_bot u)
        have h2 : dirDeriv q v 0 = 0 :=
          dirDeriv_zero (mem_convexDom.1 (interior_subset hv)).ne (hqp.ne_bot v)
        simp [h1, h2]
      have hc : (0 : ℝ) < ‖z‖ := norm_pos_iff.2 hz
      have hwz : ‖z‖ • (‖z‖⁻¹ • z) = z := by
        rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
      have hwnorm : ‖(‖z‖⁻¹ : ℝ) • z‖ = 1 := by
        rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hc, inv_mul_cancel₀ hc.ne']
      have hbz := hb ((‖z‖⁻¹ : ℝ) • z) (by rw [Metric.mem_closedBall, dist_zero_right, hwnorm])
      have hpz := toReal_dirDeriv_smul hp hpp hu hc ((‖z‖⁻¹ : ℝ) • z)
      have hqz := toReal_dirDeriv_smul hq hqp hv hc ((‖z‖⁻¹ : ℝ) • z)
      rw [hwz] at hpz hqz
      calc (dirDeriv p u z).toReal
          = ‖z‖ * (dirDeriv p u ((‖z‖⁻¹ : ℝ) • z)).toReal := hpz
        _ ≤ ‖z‖ * ((dirDeriv q v ((‖z‖⁻¹ : ℝ) • z)).toReal + ε) :=
            mul_le_mul_of_nonneg_left hbz (norm_nonneg z)
        _ = ‖z‖ * (dirDeriv q v ((‖z‖⁻¹ : ℝ) • z)).toReal + ε * ‖z‖ := by ring
        _ = (dirDeriv q v z).toReal + ε * ‖z‖ := by rw [← hqz]
    rw [dirDeriv_eq_coe_toReal_of_mem_interior_convexDom hp hpp hu z]
    exact_mod_cast hreal
  have hcpt : IsCompact (subdifferential (innerₗ E) q v) := isCompact_subdifferential hq hqp hv
  have hcvx : Convex ℝ (subdifferential (innerₗ E) q v + Metric.closedBall (0 : E) ε) :=
    (convex_subdifferential _ _ _).add (convex_closedBall _ _)
  have hcptsum : IsCompact (subdifferential (innerₗ E) q v + Metric.closedBall (0 : E) ε) :=
    hcpt.add (isCompact_closedBall _ _)
  have hsupple : supportFn (innerₗ E) (subdifferential (innerₗ E) p u)
      ≤ supportFn (innerₗ E) (subdifferential (innerₗ E) q v + Metric.closedBall (0 : E) ε) := by
    intro z
    rw [supportFn_add, Pi.add_apply, supportFn_subdifferential hp hpp huri,
      supportFn_subdifferential hq hqp hvri, supportFn_closedBall hε.le]
    calc dirDeriv p u z ≤ (((dirDeriv q v z).toReal + ε * ‖z‖ : ℝ) : EReal) := hhom z
      _ = dirDeriv q v z + ((ε * ‖z‖ : ℝ) : EReal) := by
          rw [EReal.coe_add, ← dirDeriv_eq_coe_toReal_of_mem_interior_convexDom hq hqp hv z]
  have hincl := (closure_convexHull_subset_iff_supportFn_le (B := innerₗ E) _ _).2 hsupple
  rw [hcvx.convexHull_eq, hcptsum.isClosed.closure_eq] at hincl
  exact fun w hw => hincl (subset_closure (subset_convexHull ℝ _ hw))

/-- **Upper semicontinuity of subdifferentials under pointwise convergence.** Let $E$ be a
finite-dimensional real inner product space, and let $U \subseteq E$ be open and convex. Let
$f_i : E \to [-\infty, +\infty]$ and $g : E \to [-\infty, +\infty]$ be proper and convex, with
$U \subseteq \operatorname{dom} f_i$ for every $i$ and $U \subseteq \operatorname{dom} g$, and
let $f_i(z) \to g(z)$ for every $z \in U$. Let $x_i \to x \in U$ and $\varepsilon > 0$. Then
$$\partial f_i(x_i) \subseteq \partial g(x) + \varepsilon B \quad \text{for all large } i,$$
where $B$ is the closed unit ball.

This is the second assertion of Theorem 24.5 of [rockafellar1970convex]. The subdifferentials
are the sets that have the directional derivatives as support functions, and
`ConvexAnalysis.eventually_dirDeriv_lt` bounds the directional derivatives pointwise. The bound
is made uniform on the compact unit ball and then extended by positive homogeneity. -/
theorem eventually_subdifferential_subset_add_closedBall (hU : IsOpen U) (hUc : Convex ℝ U)
    (hf : ∀ i, ConvexFn (f i)) (hfp : ∀ i, ProperConvex (f i)) (hfU : ∀ i, U ⊆ convexDom (f i))
    (hg : ConvexFn g) (hgp : ProperConvex g) (hgU : U ⊆ convexDom g)
    (hconv : ∀ z ∈ U, Tendsto (fun i => f i z) atTop (𝓝 (g z)))
    (hx : x ∈ U) {xs : ℕ → E} (hxs : Tendsto xs atTop (𝓝 x)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, subdifferential (innerₗ E) (f i) (xs i)
      ⊆ subdifferential (innerₗ E) g x + Metric.closedBall (0 : E) ε := by
  classical
  -- Replace `xs` by a sequence lying in `U` for *every* index; the two agree eventually.
  have hxsU : ∀ᶠ i in atTop, xs i ∈ U := hxs.eventually_mem (hU.mem_nhds hx)
  set xs' : ℕ → E := fun i => if xs i ∈ U then xs i else x with hxs'def
  have hxs'eq : ∀ᶠ i in atTop, xs' i = xs i :=
    hxsU.mono fun i hi => by simp only [hxs'def, hi, ite_true]
  have hxsU' : ∀ i, xs' i ∈ U := fun i => by
    simp only [hxs'def]
    split
    · assumption
    · exact hx
  have hxs' : Tendsto xs' atTop (𝓝 x) := hxs.congr' (hxs'eq.mono fun i hi => hi.symm)
  suffices h : ∀ᶠ i in atTop, subdifferential (innerₗ E) (f i) (xs' i)
      ⊆ subdifferential (innerₗ E) g x + Metric.closedBall (0 : E) ε by
    filter_upwards [h, hxs'eq] with i hi hieq
    rwa [hieq] at hi
  have hxint : x ∈ interior (convexDom g) := interior_maximal hgU hU hx
  have hxsint : ∀ i, xs' i ∈ interior (convexDom (f i)) :=
      fun i => interior_maximal (hfU i) hU (hxsU' i)
  -- The pointwise bound of the previous theorem, in real form.
  have hle : ∀ z ∈ (univ : Set E), ∀ δ > 0, ∀ᶠ i in atTop,
      (dirDeriv (f i) (xs' i) z).toReal ≤ (dirDeriv g x z).toReal + δ := by
    intro z _ δ hδ
    have hlt : dirDeriv g x z < (((dirDeriv g x z).toReal + δ : ℝ) : EReal) :=
      lt_of_eq_of_lt (dirDeriv_eq_coe_toReal_of_mem_interior_convexDom hg hgp hxint z)
        (EReal.coe_lt_coe_iff.2 (by linarith))
    filter_upwards [eventually_dirDeriv_lt hU hUc hf hfp hfU hg hgp hgU hconv hx hxs'
      (ys := fun _ => z) tendsto_const_nhds hlt] with i hi
    rw [dirDeriv_eq_coe_toReal_of_mem_interior_convexDom (hf i) (hfp i) (hxsint i) z] at hi
    exact (EReal.coe_lt_coe_iff.1 hi).le
  -- Made uniform on the unit ball.
  have hunif : ∀ᶠ i in atTop, ∀ z ∈ Metric.closedBall (0 : E) 1,
      (dirDeriv (f i) (xs' i) z).toReal ≤ (dirDeriv g x z).toReal + ε :=
    eventually_forall_le_add_of_eventually_le isOpen_univ convex_univ
      (fun i => convexOn_toReal_dirDeriv (hf i) (hfp i) (hxsint i))
      (convexOn_toReal_dirDeriv hg hgp hxint) hle (isCompact_closedBall (0 : E) 1)
      (subset_univ _) hε
  filter_upwards [hunif] with i hi
  exact subdifferential_subset_add_closedBall_of_forall_dirDeriv_le (hf i) (hfp i) (hxsint i)
    hg hgp hxint hε hi

end Subdifferential

/-! ### The local form of the subgradient statement -/

section LocalSubdifferential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {x : E}

/-- Let $E$ be a finite-dimensional real inner product space, let $f : E \to [-\infty, +\infty]$ be
proper and convex, let $x \in \operatorname{int}(\operatorname{dom} f)$, and let
$\varepsilon > 0$. Then for all $z$ in a neighbourhood of $x$,
$$\partial f(z) \subseteq \partial f(x) + \varepsilon B,$$
where $B$ is the closed unit ball. So $\partial f$ is upper semicontinuous at every interior
point of $\operatorname{dom} f$. -/
theorem eventually_nhds_subdifferential_subset_add_closedBall (hf : ConvexFn f)
    (hfp : ProperConvex f)
    (hx : x ∈ interior (convexDom f)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in 𝓝 x, subdifferential (innerₗ E) f z
      ⊆ subdifferential (innerₗ E) f x + Metric.closedBall (0 : E) ε := by
  rw [Filter.eventually_iff_seq_eventually]
  intro zs hzs
  exact eventually_subdifferential_subset_add_closedBall isOpen_interior
      hf.convex_convexDom.interior
    (fun _ => hf) (fun _ => hfp) (fun _ => interior_subset) hf hfp interior_subset
    (fun z _ => tendsto_const_nhds) hx hzs hε

end LocalSubdifferential

/-! ### Approach to a point of the domain along a direction -/

section Boundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {x y : E}

omit [FiniteDimensional ℝ E] in
/-- **The segment principle for effective domains.** Let $f$ be convex, let
$x \in \operatorname{dom} f$, and let $\alpha > 0$ with $x + \alpha u \in
\operatorname{int}(\operatorname{dom} f)$. Then $x + t u \in
\operatorname{int}(\operatorname{dom} f)$ for every $t \in (0, \alpha]$. -/
theorem mem_interior_convexDom_smul (hf : ConvexFn f) (hx : x ∈ convexDom f) {u : E} {α t : ℝ}
    (hα : 0 < α)
    (hu : x + α • u ∈ interior (convexDom f)) (ht : 0 < t) (htα : t ≤ α) :
    x + t • u ∈ interior (convexDom f) := by
  have hle : (0 : ℝ) ≤ 1 - t / α := by
    rw [sub_nonneg]
    exact (div_le_one hα).2 htα
  have h := hf.convex_convexDom.combo_interior_self_mem_interior hu hx (a := t / α) (b := 1 - t / α)
    (by positivity) hle (by ring)
  have heq : (t / α) • (x + α • u) + (1 - t / α) • x = x + t • u := by
    match_scalars <;> (field_simp; try ring)
  rwa [heq] at h

omit [FiniteDimensional ℝ E] in
/-- Let $f$ be convex, let $x \in \operatorname{dom} f$, and let $x_i \to x$ with $x_i \ne x$ and
$$\frac{x_i - x}{\|x_i - x\|} \to y.$$
If $x + \alpha y \in \operatorname{int}(\operatorname{dom} f)$ for some $\alpha > 0$, then $x_i
\in \operatorname{int}(\operatorname{dom} f)$ for all large $i$.

This makes the subgradient half of the boundary statement accessible: the functions
$f'(x_i; \cdot)$ are then finite everywhere, so the theory of uniform convergence applies to
them. -/
theorem eventually_mem_interior_convexDom_of_tendsto_dir (hf : ConvexFn f) (hx : x ∈ convexDom f)
    {xs : ℕ → E} (hxsne : ∀ i, xs i ≠ x) (hxs : Tendsto xs atTop (𝓝 x))
    (hdir : Tendsto (fun i => ‖xs i - x‖⁻¹ • (xs i - x)) atTop (𝓝 y))
    {α : ℝ} (hα : 0 < α) (hαy : x + α • y ∈ interior (convexDom f)) :
    ∀ᶠ i in atTop, xs i ∈ interior (convexDom f) := by
  have heten : Tendsto (fun i => ‖xs i - x‖) atTop (𝓝 0) := by
    have h : Tendsto (fun i => ‖xs i - x‖) atTop (𝓝 ‖x - x‖) := (hxs.sub_const x).norm
    rwa [sub_self, norm_zero] at h
  have hmem : ∀ᶠ i in atTop, x + α • (‖xs i - x‖⁻¹ • (xs i - x)) ∈ interior (convexDom f) :=
    (((by fun_prop : Continuous fun v : E => x + α • v).tendsto _).comp hdir).eventually_mem
      (isOpen_interior.mem_nhds hαy)
  filter_upwards [hmem, heten.eventually_le_const hα] with i hi hie
  have hpos : 0 < ‖xs i - x‖ := norm_pos_iff.2 (sub_ne_zero.2 (hxsne i))
  have h := mem_interior_convexDom_smul hf hx hα hi hpos hie
  rwa [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul,
    show x + (xs i - x) = xs i from by abel] at h

omit [FiniteDimensional ℝ E] in
/-- Let $f$ be proper, let $x \in \operatorname{dom} f$, and let $\alpha > 0$ with $x + \alpha y \in
\operatorname{int}(\operatorname{dom} f)$. Then $y$ is an interior point of the effective domain
of $f'(x; \cdot)$.

A single difference quotient bounds $f'(x; \cdot)$ from above near $y$. -/
theorem mem_interior_convexDom_dirDeriv (hfp : ProperConvex f) (hx : x ∈ convexDom f) {α : ℝ}
    (hα : 0 < α) (hαy : x + α • y ∈ interior (convexDom f)) :
    y ∈ interior (convexDom (dirDeriv f x)) := by
  have hcont : Continuous fun v : E => x + α • v := by fun_prop
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hfp.ne_bot x) (mem_convexDom.1 hx)
  refine interior_maximal (fun v hv => ?_) (hcont.isOpen_preimage _ isOpen_interior)
    (show y ∈ (fun v : E => x + α • v) ⁻¹' interior (convexDom f) from hαy)
  obtain ⟨s, hs⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hfp.ne_bot (x + α • v))
    (mem_convexDom.1 (interior_subset hv))
  refine mem_convexDom.2 (lt_of_le_of_lt (dirDeriv_le f x v hα) ?_)
  rw [hs, hr, ← EReal.coe_sub, ← EReal.coe_div]
  exact EReal.coe_lt_top _

omit [FiniteDimensional ℝ E] in
/-- Let $f$ be proper and convex, let $x \in \operatorname{dom} f$, let $y$ be an interior point of
the effective domain of $f'(x; \cdot)$, and let $f'(x; y) \ne -\infty$. Then $f'(x; \cdot)$ is
proper.

A convex function that takes the value $-\infty$ takes it on the whole relative interior of its
effective domain, so one finite value at an interior point excludes $-\infty$ everywhere. -/
theorem properConvex_dirDeriv_of_ne_bot (hf : ConvexFn f) (hfp : ProperConvex f)
    (hx : x ∈ convexDom f)
    (hy : y ∈ interior (convexDom (dirDeriv f x))) (hne : dirDeriv f x y ≠ ⊥) :
    ProperConvex (dirDeriv f x) := by
  have hconv : ConvexFn (dirDeriv f x) :=
      convexFn_dirDeriv hf (mem_convexDom.1 hx).ne (hfp.ne_bot x)
  by_contra h
  exact hne (ConvexFn.eq_bot_of_mem_relint_convexDom hconv h
    (Convex.interior_subset_relint hy))

/-- **Upper semicontinuity of directional derivatives at a point that need not be interior.** Let
$E$ be a finite-dimensional real normed space, and let $f : E \to [-\infty, +\infty]$ be proper
and convex. Let $x \in \operatorname{dom} f$, and let $(x_i)$ be a sequence in
$\operatorname{dom} f$ with $x_i \ne x$, $x_i \to x$ and
$$\frac{x_i - x}{\|x_i - x\|} \to y.$$
Let $f'(x; y) > -\infty$, and let $x + \alpha y \in \operatorname{int}(\operatorname{dom} f)$
for some $\alpha > 0$. Write $f'(x; y; z)$ for the directional derivative of $f'(x; \cdot)$ at
$y$ in the direction $z$. Then for every $z \in E$
$$\limsup_{i \to \infty} f'(x_i; z) \le f'(x; y; z),$$
in the form: for every real $\mu > f'(x; y; z)$, $f'(x_i; z) < \mu$ for all large $i$.

This is the first assertion of Theorem 24.6 of [rockafellar1970convex]. As in
`ConvexAnalysis.eventually_dirDeriv_lt`, the form with a real $\mu$ avoids values at infinity.
The derivative $f'(x; y; z)$ is `dirDeriv (dirDeriv f x) y z`. -/
theorem eventually_dirDeriv_lt_of_tendsto_dir (hf : ConvexFn f) (hfp : ProperConvex f)
    (hx : x ∈ convexDom f)
    {xs : ℕ → E} (hxsdom : ∀ i, xs i ∈ convexDom f) (hxsne : ∀ i, xs i ≠ x)
    (hxs : Tendsto xs atTop (𝓝 x))
    (hdir : Tendsto (fun i => ‖xs i - x‖⁻¹ • (xs i - x)) atTop (𝓝 y))
    (hy : dirDeriv f x y ≠ ⊥) {α : ℝ} (hα : 0 < α) (hαy : x + α • y ∈ interior (convexDom f))
    {z : E} {μ : ℝ} (hμ : dirDeriv (dirDeriv f x) y z < (μ : EReal)) :
    ∀ᶠ i in atTop, dirDeriv f (xs i) z < (μ : EReal) := by
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hfp.ne_bot x) (mem_convexDom.1 hx)
  have hgconv : ConvexFn (dirDeriv f x) :=
    convexFn_dirDeriv hf (mem_convexDom.1 hx).ne (hfp.ne_bot x)
  have hyint : y ∈ interior (convexDom (dirDeriv f x)) :=
      mem_interior_convexDom_dirDeriv hfp hx hα hαy
  have hgp : ProperConvex (dirDeriv f x) := properConvex_dirDeriv_of_ne_bot hf hfp hx hyint hy
  obtain ⟨c, hc⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hgp.ne_bot y)
    (mem_convexDom.1 (interior_subset hyint))
  -- A step `lam > 0` realising a quotient of `f'(x; ·)` below `μ` and keeping the ray interior.
  obtain ⟨lam0, hlam0, hq0⟩ := dirDeriv_lt_iff.1 hμ
  have hmemW : ∀ᶠ t in 𝓝 (0 : ℝ), x + α • (y + t • z) ∈ interior (convexDom f) := by
    have hcont : Continuous fun t : ℝ => x + α • (y + t • z) := by fun_prop
    have h0 := hcont.tendsto 0
    simp only [zero_smul, add_zero] at h0
    exact h0.eventually_mem (isOpen_interior.mem_nhds hαy)
  obtain ⟨δ, hδ, hδW⟩ := Metric.eventually_nhds_iff.1 hmemW
  set lam : ℝ := min lam0 (δ / 2) with hlamdef
  have hlampos : 0 < lam := lt_min hlam0 (by linarith)
  have hlamle : lam ≤ lam0 := min_le_left _ _
  have hlamW : x + α • (y + lam • z) ∈ interior (convexDom f) := by
    refine hδW ?_
    rw [Real.dist_eq, sub_zero, abs_of_pos hlampos]
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hqlam : (dirDeriv f x (y + lam • z) - dirDeriv f x y) / (lam : EReal) < (μ : EReal) :=
    lt_of_le_of_lt (monotoneOn_sub_div hgconv hc z (mem_Ioi.2 hlampos) (mem_Ioi.2 hlam0) hlamle)
      hq0
  have hgu : dirDeriv f x (y + lam • z) < ((c + μ * lam : ℝ) : EReal) := by
    rw [hc] at hqlam
    by_contra hcon
    push Not at hcon
    exact absurd ((EReal.coe_le_sub_div_iff hlampos _).2 hcon) (not_le.2 hqlam)
  -- A step `b > 0`, at most `α / 2`, realising a quotient of `f` below `c + μ lam`.
  obtain ⟨b0, hb0, hqb0⟩ := dirDeriv_lt_iff.1 hgu
  set b : ℝ := min b0 (α / 2) with hbdef
  have hbpos : 0 < b := lt_min hb0 (by linarith)
  have hble : b ≤ b0 := min_le_left _ _
  have hbα : b ≤ α / 2 := min_le_right _ _
  have hqb : (f (x + b • (y + lam • z)) - f x) / (b : EReal) < ((c + μ * lam : ℝ) : EReal) :=
    lt_of_le_of_lt (monotoneOn_sub_div hf hr (y + lam • z) (mem_Ioi.2 hbpos) (mem_Ioi.2 hb0) hble)
      hqb0
  have hbu : x + b • (y + lam • z) ∈ interior (convexDom f) :=
    mem_interior_convexDom_smul hf hx hα hlamW hbpos (by linarith)
  -- The three sequences.
  obtain ⟨e, Y, U, hedef, hYdef, hUdef⟩ :
      ∃ (e : ℕ → ℝ) (Y U : ℕ → E), (∀ i, e i = ‖xs i - x‖) ∧
        (∀ i, Y i = (e i)⁻¹ • (xs i - x)) ∧ (∀ i, U i = Y i + lam • z) :=
    ⟨_, _, fun i => ‖xs i - x‖⁻¹ • (xs i - x) + lam • z, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  have hepos : ∀ i, 0 < e i := fun i => by
    rw [hedef]
    exact norm_pos_iff.2 (sub_ne_zero.2 (hxsne i))
  have heten : Tendsto e atTop (𝓝 0) := by
    have h : Tendsto (fun i => ‖xs i - x‖) atTop (𝓝 ‖x - x‖) := (hxs.sub_const x).norm
    rw [sub_self, norm_zero] at h
    exact h.congr fun i => (hedef i).symm
  have hYten : Tendsto Y atTop (𝓝 y) := hdir.congr fun i => by rw [hYdef, hedef]
  have hUten : Tendsto U atTop (𝓝 (y + lam • z)) :=
    (hYten.add_const (lam • z)).congr fun i => (hUdef i).symm
  -- The two limits, on the two sides of the inequality.
  have hScont : ContinuousAt (fun v => (dirDeriv f x v).toReal) y :=
    (hgconv.continuousOn_toReal_relint_convexDom hgp).continuousAt (mem_nhds_iff.2
      ⟨interior (convexDom (dirDeriv f x)),
        Convex.interior_subset_relint, isOpen_interior, hyint⟩)
  have hSten : Tendsto (fun i => (dirDeriv f x (Y i)).toReal) atTop (𝓝 c) := by
    have h := hScont.tendsto.comp hYten
    rwa [hc, EReal.toReal_coe] at h
  have hFcont : ContinuousAt (fun v => (f v).toReal) (x + b • (y + lam • z)) :=
    (hf.continuousOn_toReal_relint_convexDom hfp).continuousAt (mem_nhds_iff.2
      ⟨interior (convexDom f), Convex.interior_subset_relint,
        isOpen_interior, hbu⟩)
  have hpt : Tendsto (fun i => x + (e i + b) • U i) atTop (𝓝 (x + b • (y + lam • z))) := by
    have h : Tendsto (fun i => x + (e i + b) • U i) atTop
        (𝓝 (x + ((0 : ℝ) + b) • (y + lam • z))) :=
      tendsto_const_nhds.add ((heten.add tendsto_const_nhds).smul hUten)
    simpa using h
  have hQten : Tendsto (fun i => ((f (x + (e i + b) • U i)).toReal - r) / (e i + b)) atTop
      (𝓝 (((f (x + b • (y + lam • z))).toReal - r) / b)) :=
    ((hFcont.tendsto.comp hpt).sub tendsto_const_nhds).div
      (by simpa using heten.add (tendsto_const_nhds (x := b))) hbpos.ne'
  obtain ⟨q, hq⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hfp.ne_bot _)
    (mem_convexDom.1 (interior_subset hbu))
  have hQlt : ((f (x + b • (y + lam • z))).toReal - r) / b - c < μ * lam := by
    rw [hq, hr, ← EReal.coe_sub, ← EReal.coe_div, EReal.coe_lt_coe_iff] at hqb
    rw [hq, EReal.toReal_coe]
    linarith
  -- Everything that has to hold only for large indices.
  filter_upwards [heten.eventually_le_const (show (0 : ℝ) < α / 2 by linarith),
    (((by fun_prop : Continuous fun v : E => x + α • v).tendsto _).comp hUten).eventually_mem
      (isOpen_interior.mem_nhds hlamW),
    hYten.eventually_mem (isOpen_interior.mem_nhds hyint),
    (hQten.sub hSten).eventually_lt_const hQlt] with i hei heU heY hQS
  have hei0 : 0 < e i := hepos i
  have hxeq : x + e i • Y i = xs i := by
    rw [hYdef i, smul_smul, mul_inv_cancel₀ hei0.ne', one_smul]
    abel
  have hxeq2 : x + e i • U i = xs i + e i • (lam • z) := by
    rw [hUdef i, smul_add, ← hxeq]
    abel
  have hmem1 : x + e i • U i ∈ interior (convexDom f) :=
    mem_interior_convexDom_smul hf hx hα heU hei0 (by linarith)
  have hmem2 : x + (e i + b) • U i ∈ interior (convexDom f) :=
    mem_interior_convexDom_smul hf hx hα heU (by linarith) (by linarith)
  obtain ⟨a1, ha1⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hfp.ne_bot (xs i))
    (mem_convexDom.1 (hxsdom i))
  obtain ⟨m1, hm1⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hfp.ne_bot (x + e i • U i))
    (mem_convexDom.1 (interior_subset hmem1))
  obtain ⟨m2, hm2⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hfp.ne_bot (x + (e i + b) • U i))
    (mem_convexDom.1 (interior_subset hmem2))
  obtain ⟨s1, hs1⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hgp.ne_bot (Y i))
    (mem_convexDom.1 (interior_subset heY))
  have step1 : dirDeriv f x (Y i) ≤ (((a1 - r) / e i : ℝ) : EReal) := by
    have h := dirDeriv_le f x (Y i) hei0
    rwa [hxeq, ha1, hr, ← EReal.coe_sub, ← EReal.coe_div] at h
  have step2 : (lam : EReal) * dirDeriv f (xs i) z ≤ (((m1 - a1) / e i : ℝ) : EReal) := by
    have h := dirDeriv_le f (xs i) (lam • z) hei0
    rw [posHomogeneous_dirDeriv f (xs i) lam hlampos z, ← hxeq2, hm1, ha1,
      ← EReal.coe_sub, ← EReal.coe_div] at h
    exact h
  have step3 : dirDeriv f x (Y i) + (lam : EReal) * dirDeriv f (xs i) z
      ≤ (((m1 - r) / e i : ℝ) : EReal) := by
    have h := add_le_add step1 step2
    rwa [← EReal.coe_add,
      show (a1 - r) / e i + (m1 - a1) / e i = (m1 - r) / e i from by field_simp; ring] at h
  have step4 : (((m1 - r) / e i : ℝ) : EReal) ≤ (((m2 - r) / (e i + b) : ℝ) : EReal) := by
    have h : (f (x + e i • U i) - f x) / ((e i : ℝ) : EReal)
        ≤ (f (x + (e i + b) • U i) - f x) / ((e i + b : ℝ) : EReal) :=
      monotoneOn_sub_div hf hr (U i) (mem_Ioi.2 hei0)
        (mem_Ioi.2 (by linarith : (0 : ℝ) < e i + b)) (by linarith)
    rwa [hm1, hm2, hr, ← EReal.coe_sub, ← EReal.coe_div, ← EReal.coe_sub,
      ← EReal.coe_div] at h
  rw [hm2, hs1, EReal.toReal_coe, EReal.toReal_coe] at hQS
  by_contra hcon
  push Not at hcon
  have h5 : ((lam * μ : ℝ) : EReal) ≤ (lam : EReal) * dirDeriv f (xs i) z := by
    rw [EReal.coe_mul]
    exact (EReal.coe_mul_le_coe_mul_iff hlampos).2 hcon
  have h6 : ((s1 + lam * μ : ℝ) : EReal) ≤ (((m2 - r) / (e i + b) : ℝ) : EReal) := by
    rw [EReal.coe_add]
    refine le_trans (add_le_add ?_ h5) (step3.trans step4)
    rw [hs1]
  rw [EReal.coe_le_coe_iff] at h6
  linarith [mul_comm lam μ]

end Boundary

/-! ### The face of $\partial f(x)$ exposed by a direction -/

section ExposedFace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {x y : E}

/-- Let $E$ be a finite-dimensional real normed space, let $F$ be a locally convex topological
vector space, and let the pairing be compatible with the topologies of $E$ and of $F$. Let
$f : E \to [-\infty, +\infty]$ be convex with $f(x)$ finite, let $f'(x; \cdot)$ be proper, and
let $y$ lie in the relative interior of the effective domain of $f'(x; \cdot)$. Then the
subdifferential of $f'(x; \cdot)$ at $y$ is the face $\partial f(x)_y$ of $\partial f(x)$
exposed by $y$:
$$\partial (f'(x; \cdot))(y) = \{v \in \partial f(x) \mid \langle y, w \rangle \le \langle y, v
  \rangle \text{ for all } w \in \partial f(x)\}.$$

This set appears in `ConvexAnalysis.eventually_subdifferential_subset_exposed_add_closedBall`.
The proof combines the description of $f'(x; \cdot)$ as a support function with the conjugate
characterization of the subdifferential. Properness of $f'(x; \cdot)$ makes $\partial f(x)$
nonempty, so nonemptiness is not a separate hypothesis. Compatibility of $B$ and of `B.flip` is
`ConvexAnalysis.IsCompatiblePairing`. -/
theorem subdifferential_dirDeriv [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hf : ConvexFn f) (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) (hgp : ProperConvex (dirDeriv f x))
    (hy : y ∈ ri (convexDom (dirDeriv f x))) :
    subdifferential B (dirDeriv f x) y
      = {v ∈ subdifferential B f x | ∀ w ∈ subdifferential B f x, B y w ≤ B y v} := by
  have hgc : ConvexFn (dirDeriv f x) := convexFn_dirDeriv hf ht hb
  obtain ⟨v₀, hv₀⟩ := subdifferential_nonempty_of_mem_relint_convexDom (B := B) hgc hgp hy
  have hCne : (subdifferential B f x).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hemp
    obtain ⟨z, hz⟩ := (subdifferential_eq_empty_iff_exists_dirDeriv_eq_bot (B := B) hf ht hb).1 hemp
    exact hgp.ne_bot z hz
  have hsupp := subdifferential_supportFn (B := B.flip) (isClosed_subdifferential (B := B) f x)
    (convex_subdifferential B f x) hCne y
  rw [LinearMap.flip_flip] at hsupp
  rw [← subdifferential_convexCl (B := B) hgc hv₀, convexCl_dirDeriv (B := B) hf ht hb, hsupp]
  simp only [LinearMap.flip_apply]

/-- Under the hypotheses of `ConvexAnalysis.subdifferential_dirDeriv`, the face $\partial f(x)_y$ is
the set of subgradients at which $y$ is normal to $\partial f(x)$:
$$\partial (f'(x; \cdot))(y) = \{v \in \partial f(x) \mid y \in N_{\partial f(x)}(v)\}.$$
The normal cone is taken for the flipped pairing `B.flip`. -/
theorem subdifferential_dirDeriv_eq_sep_normalCone [IsCompatiblePairing B]
    [IsCompatiblePairing B.flip] (hf : ConvexFn f) (ht : f x ≠ ⊤) (hb : f x ≠ ⊥)
    (hgp : ProperConvex (dirDeriv f x)) (hy : y ∈ ri (convexDom (dirDeriv f x))) :
    subdifferential B (dirDeriv f x) y
      = {v ∈ subdifferential B f x | y ∈ normalCone B.flip (subdifferential B f x) v} := by
  rw [subdifferential_dirDeriv (B := B) hf ht hb hgp hy]
  ext v
  simp only [Set.mem_sep_iff, mem_normalCone, map_sub, LinearMap.sub_apply, LinearMap.flip_apply,
    sub_nonpos]

/-- Under the hypotheses of `ConvexAnalysis.subdifferential_dirDeriv`, the set
$\partial (f'(x; \cdot))(y)$ is an exposed face of $\partial f(x)$ in the sense of Mathlib
(`IsExposed`): it is the set of points of $\partial f(x)$ at which the continuous linear
functional $\langle y, \cdot \rangle$ attains its maximum. With
`ConvexAnalysis.IsExposed.isFace` it is a face of $\partial f(x)$ in the sense of
`ConvexAnalysis.IsFace`. -/
theorem isExposed_subdifferential_dirDeriv [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hf : ConvexFn f) (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) (hgp : ProperConvex (dirDeriv f x))
    (hy : y ∈ ri (convexDom (dirDeriv f x))) :
    IsExposed ℝ (subdifferential B f x) (subdifferential B (dirDeriv f x) y) := by
  have hcont : Continuous fun v : F => B y v := by
    simpa only [LinearMap.flip_apply] using continuous_pairing B.flip y
  exact fun _ => ⟨⟨B y, hcont⟩, subdifferential_dirDeriv (B := B) hf ht hb hgp hy⟩

end ExposedFace

/-! ### The subgradient half of the boundary statement -/

section BoundarySubdifferential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {x y : E}

/-- **Upper semicontinuity of subdifferentials at a point that need not be interior.** Let $E$ be a
finite-dimensional real inner product space, and let $f : E \to [-\infty, +\infty]$ be proper
and convex. Let $x \in \operatorname{dom} f$, and let $(x_i)$ be a sequence in
$\operatorname{dom} f$ with $x_i \ne x$, $x_i \to x$ and
$$\frac{x_i - x}{\|x_i - x\|} \to y.$$
Let $f'(x; y) > -\infty$, let $x + \alpha y \in \operatorname{int}(\operatorname{dom} f)$ for
some $\alpha > 0$, and let $\varepsilon > 0$. Then for all large $i$
$$\partial f(x_i) \subseteq \partial f(x)_y + \varepsilon B, \qquad \partial f(x)_y = \{v \in
  \partial f(x) \mid \langle y, w \rangle \le \langle y, v \rangle \text{ for all } w \in
  \partial f(x)\},$$
where $B$ is the closed unit ball.

This is the second assertion of Theorem 24.6 of [rockafellar1970convex]. The set
$\partial f(x)_y$ is $\partial (f'(x; \cdot))(y)$ by `ConvexAnalysis.subdifferential_dirDeriv`.
The proof is that of `ConvexAnalysis.eventually_subdifferential_subset_add_closedBall`, with
$f'(x; \cdot)$ replaced by $f'(x; y; \cdot)$. The step that is usually left implicit is
`ConvexAnalysis.eventually_mem_interior_convexDom_of_tendsto_dir`, which makes the functions
$f'(x_i; \cdot)$ finite everywhere. -/
theorem eventually_subdifferential_subset_exposed_add_closedBall (hf : ConvexFn f)
    (hfp : ProperConvex f)
    (hx : x ∈ convexDom f) {xs : ℕ → E} (hxsdom : ∀ i, xs i ∈ convexDom f) (hxsne : ∀ i, xs i ≠ x)
    (hxs : Tendsto xs atTop (𝓝 x))
    (hdir : Tendsto (fun i => ‖xs i - x‖⁻¹ • (xs i - x)) atTop (𝓝 y))
    (hy : dirDeriv f x y ≠ ⊥) {α : ℝ} (hα : 0 < α) (hαy : x + α • y ∈ interior (convexDom f))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, subdifferential (innerₗ E) f (xs i)
      ⊆ {v ∈ subdifferential (innerₗ E) f x | ∀ w ∈ subdifferential (innerₗ E) f x, ⟪y, w⟫ ≤ ⟪y, v⟫}
        + Metric.closedBall (0 : E) ε := by
  classical
  have hgc : ConvexFn (dirDeriv f x) := convexFn_dirDeriv hf (mem_convexDom.1 hx).ne (hfp.ne_bot x)
  have hyint : y ∈ interior (convexDom (dirDeriv f x)) :=
      mem_interior_convexDom_dirDeriv hfp hx hα hαy
  have hgp : ProperConvex (dirDeriv f x) := properConvex_dirDeriv_of_ne_bot hf hfp hx hyint hy
  have hyri : y ∈ ri (convexDom (dirDeriv f x)) :=
    Convex.interior_subset_relint hyint
  -- The exposed face is `∂(f'(x; ·))(y)`.
  have hflip : IsCompatiblePairing ((innerₗ E).flip) := by rw [flip_innerₗ]; infer_instance
  have hface : subdifferential (innerₗ E) (dirDeriv f x) y
      = {v ∈ subdifferential (innerₗ E) f x |
          ∀ w ∈ subdifferential (innerₗ E) f x, ⟪y, w⟫ ≤ ⟪y, v⟫} := by
    have h :=
        subdifferential_dirDeriv (B := innerₗ E) hf (mem_convexDom.1 hx).ne (hfp.ne_bot x) hgp hyri
    simpa only [innerₗ_apply_apply] using h
  rw [← hface]
  -- The approaching points are eventually interior, so `f'(x i; ·)` is finite everywhere.
  have hint : ∀ᶠ i in atTop, xs i ∈ interior (convexDom f) :=
    eventually_mem_interior_convexDom_of_tendsto_dir hf hx hxsne hxs hdir hα hαy
  set xs' : ℕ → E := fun i => if xs i ∈ interior (convexDom f) then xs i else x + α • y with hxs'def
  have hxs'int : ∀ i, xs' i ∈ interior (convexDom f) := fun i => by
    simp only [hxs'def]
    split
    · assumption
    · exact hαy
  have hxs'eq : ∀ᶠ i in atTop, xs' i = xs i :=
    hint.mono fun i hi => by simp only [hxs'def, hi, ite_true]
  -- The pointwise bound of the first assertion, in real form.
  have hle : ∀ z ∈ (univ : Set E), ∀ δ > 0, ∀ᶠ i in atTop,
      (dirDeriv f (xs' i) z).toReal ≤ (dirDeriv (dirDeriv f x) y z).toReal + δ := by
    intro z _ δ hδ
    have hlt : dirDeriv (dirDeriv f x) y z
        < (((dirDeriv (dirDeriv f x) y z).toReal + δ : ℝ) : EReal) :=
      lt_of_eq_of_lt (dirDeriv_eq_coe_toReal_of_mem_interior_convexDom hgc hgp hyint z)
        (EReal.coe_lt_coe_iff.2 (by linarith))
    filter_upwards [eventually_dirDeriv_lt_of_tendsto_dir hf hfp hx hxsdom hxsne hxs hdir hy
      hα hαy hlt, hxs'eq, hint] with i hi hieq hiint
    rw [hieq]
    rw [dirDeriv_eq_coe_toReal_of_mem_interior_convexDom hf hfp hiint z] at hi
    exact (EReal.coe_lt_coe_iff.1 hi).le
  -- Made uniform on the unit ball.
  have hunif : ∀ᶠ i in atTop, ∀ z ∈ Metric.closedBall (0 : E) 1,
      (dirDeriv f (xs' i) z).toReal ≤ (dirDeriv (dirDeriv f x) y z).toReal + ε :=
    eventually_forall_le_add_of_eventually_le isOpen_univ convex_univ
      (fun i => convexOn_toReal_dirDeriv hf hfp (hxs'int i))
      (convexOn_toReal_dirDeriv hgc hgp hyint) hle (isCompact_closedBall (0 : E) 1)
      (subset_univ _) hε
  filter_upwards [hunif, hxs'eq] with i hi hieq
  rw [← hieq]
  exact subdifferential_subset_add_closedBall_of_forall_dirDeriv_le hf hfp (hxs'int i) hgc hgp
    hyint hε hi

end BoundarySubdifferential

end ConvexAnalysis

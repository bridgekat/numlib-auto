/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Subdifferential.Rademacher

/-!
# Convergence of gradients

Let $U$ be an open convex subset of a finite-dimensional real inner product space $E$, and let $f_i$
and $f$ be proper convex functions that are finite and differentiable on $U$. If $f_i \to f$
pointwise on $U$, then $\nabla f_i \to \nabla f$ pointwise on $U$, and uniformly on every compact
subset of $U$. This is Theorem 25.7 of [rockafellar1970convex]. For differentiable functions that
are not convex, the statement is false.

Convexity enters through the upper semicontinuity of the subdifferential under pointwise
convergence. Both subdifferentials are singletons, so an inclusion $\partial f_i(x) \subseteq
\partial f(x) + \varepsilon B$, with $B$ the closed unit ball, is a bound $\|\nabla f_i(x) - \nabla
f(x)\| \le \varepsilon$.

## Main results

* `ConvexAnalysis.dist_le_of_subdifferential_subset`: an inclusion $\partial p(u) \subseteq \partial
  q(v) + \varepsilon B$ between singleton subdifferentials is the bound
  $\|\nabla p(u) - \nabla q(v)\| \le \varepsilon$.
* `ConvexAnalysis.tendsto_of_hasGradientAtFn`: the gradients converge at every point of $U$
  ([rockafellar1970convex], Theorem 25.7).
* `ConvexAnalysis.tendstoUniformlyOn_fderiv_toReal`: the gradients converge uniformly on every
  compact subset of $U$ ([rockafellar1970convex], Theorem 25.7).

## Implementation notes

* Subgradients are taken for the pairing `innerₗ E`, so they are vectors of $E$, while a gradient is
  an element of `StrongDual ℝ E`. The Riesz isomorphism translates between the two. It is an
  isometry, so the translation costs no constant.
-/

namespace ConvexAnalysis

open Filter Metric Topology Pointwise

section GradientLimit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : ℕ → E → EReal} {g : E → EReal} {U : Set E} {x : E}

/-- Let $E$ be a finite-dimensional real inner product space, let
$p, q \colon E \to [-\infty, +\infty]$ be convex, let $p$ have the gradient $a$ at $u$, and let
$q$ have the gradient $b$ at $v$. If
$$\partial p(u) \subseteq \partial q(v) + \bar B(0, \varepsilon),$$
then $\|a - b\| \le \varepsilon$.

Here $\partial p(u) = \{a\}$ and $\partial q(v) = \{b\}$, as vectors through the Riesz
isomorphism. The subgradients are taken for the pairing `innerₗ E`, the gradients are elements
of `StrongDual ℝ E`, and the conclusion is `dist a b ≤ ε`. -/
theorem dist_le_of_subdifferential_subset {p q : E → EReal} {u v : E} {a b : StrongDual ℝ E} {ε : ℝ}
    (hp : ConvexFn p) (hq : ConvexFn q) (ha : HasGradientAtFn p a u) (hb : HasGradientAtFn q b v)
    (hsub : subdifferential (innerₗ E) p u
      ⊆ subdifferential (innerₗ E) q v + closedBall (0 : E) ε) :
    dist a b ≤ ε := by
  have hmem : (InnerProductSpace.toDual ℝ E).symm a ∈ subdifferential (innerₗ E) p u := by
    rw [subdifferential_innerL_eq_singleton hp ha]
    rfl
  have hin := hsub hmem
  rw [subdifferential_innerL_eq_singleton hq hb] at hin
  obtain ⟨c, hc, d, hd, hcd⟩ := hin
  rw [Set.mem_singleton_iff] at hc
  subst hc
  rw [mem_closedBall_zero_iff] at hd
  have hdist : dist a b = ‖(InnerProductSpace.toDual ℝ E).symm a
      - (InnerProductSpace.toDual ℝ E).symm b‖ := by
    rw [dist_eq_norm, ← (InnerProductSpace.toDual ℝ E).symm.norm_map (a - b), map_sub]
  rw [hdist, ← hcd, add_sub_cancel_left]
  exact hd

/-- Let $E$ be a finite-dimensional real inner product space, and let $U \subseteq E$ be open and
convex. Let $f_i$ for $i \in \mathbb{N}$ and $g$ be proper convex functions
$E \to [-\infty, +\infty]$ that are finite on $U$, and let $f_i(z) \to g(z)$ for every
$z \in U$. Let $x \in U$, let $f_i$ have the gradient $G_i$ at $x$, and let $g$ have the
gradient $G'$ at $x$. Then
$$G_i \to G' \qquad \text{as } i \to \infty.$$
This is the pointwise part of Theorem 25.7 of [rockafellar1970convex].

The proof is the upper semicontinuity of the subdifferential under pointwise convergence, at the
constant sequence $x_i = x$. -/
theorem tendsto_of_hasGradientAtFn (hU : IsOpen U) (hUc : Convex ℝ U) (hf : ∀ i, ConvexFn (f i))
    (hfp : ∀ i, ProperConvex (f i)) (hfU : ∀ i, U ⊆ convexDom (f i)) (hg : ConvexFn g)
        (hgp : ProperConvex g)
    (hgU : U ⊆ convexDom g) (hconv : ∀ z ∈ U, Tendsto (fun i => f i z) atTop (𝓝 (g z))) (hx : x ∈ U)
    {G : ℕ → StrongDual ℝ E} {G' : StrongDual ℝ E} (hG : ∀ i, HasGradientAtFn (f i) (G i) x)
    (hG' : HasGradientAtFn g G' x) : Tendsto G atTop (𝓝 G') := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  have hev := eventually_subdifferential_subset_add_closedBall hU hUc hf hfp hfU hg hgp hgU hconv hx
    (tendsto_const_nhds (x := x) (f := (atTop : Filter ℕ))) (half_pos hε)
  filter_upwards [hev] with i hi
  exact lt_of_le_of_lt (dist_le_of_subdifferential_subset (hf i) hg (hG i) hG' hi) (half_lt_self hε)

/-- Let $E$ be a finite-dimensional real inner product space, and let $U \subseteq E$ be open and
convex. Let $f_i$ for $i \in \mathbb{N}$ and $g$ be proper convex functions
$E \to [-\infty, +\infty]$ that are finite and differentiable at every point of $U$, and let
$f_i(z) \to g(z)$ for every $z \in U$. Then for every compact $S \subseteq U$,
$$\nabla f_i \to \nabla g \qquad \text{uniformly on } S.$$
This is the uniform part of Theorem 25.7 of [rockafellar1970convex].

The gradients are the Fréchet derivatives `fderiv ℝ` of the real-valued functions
`fun w => (f i w).toReal` and `fun w => (g w).toReal`. If the convergence is not uniform, there
are points $z_n \in S$ with $\|\nabla g(z_n) - \nabla f_{\varphi(n)}(z_n)\| \ge \varepsilon$. A
convergent subsequence $z_n \to w$, the subdifferential inclusion along the subsequence and the
upper semicontinuity of $\partial g$ at $w$ give two bounds by $\varepsilon/3$ that contradict
this. -/
theorem tendstoUniformlyOn_fderiv_toReal (hU : IsOpen U) (hUc : Convex ℝ U)
    (hf : ∀ i, ConvexFn (f i)) (hfp : ∀ i, ProperConvex (f i)) (hfU : ∀ i, U ⊆ convexDom (f i))
    (hg : ConvexFn g) (hgp : ProperConvex g) (hgU : U ⊆ convexDom g)
    (hconv : ∀ z ∈ U, Tendsto (fun i => f i z) atTop (𝓝 (g z)))
    (hfd : ∀ i, ∀ z ∈ U, DifferentiableAtFn (f i) z) (hgd : ∀ z ∈ U, DifferentiableAtFn g z)
    {S : Set E} (hS : IsCompact S) (hSU : S ⊆ U) :
    TendstoUniformlyOn (fun i => fderiv ℝ fun w => (f i w).toReal)
      (fderiv ℝ fun w => (g w).toReal) atTop S := by
  set Gf : ℕ → E → StrongDual ℝ E := fun i => fderiv ℝ fun w => (f i w).toReal with hGfdef
  set Gg : E → StrongDual ℝ E := fderiv ℝ fun w => (g w).toReal with hGgdef
  have hgradf : ∀ i, ∀ z ∈ U, HasGradientAtFn (f i) (Gf i z) z := fun i z hz =>
    DifferentiableAtFn.hasGradientAtFn_fderiv (hfd i z hz)
  have hgradg : ∀ z ∈ U, HasGradientAtFn g (Gg z) z := fun z hz =>
    DifferentiableAtFn.hasGradientAtFn_fderiv (hgd z hz)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra hcon
  have hfreq : ∃ᶠ i in atTop, ∃ z ∈ S, ε ≤ dist (Gg z) (Gf i z) := by
    refine (Filter.not_eventually.1 hcon).mono fun i hi => ?_
    push Not at hi
    exact hi
  obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_of_frequently_atTop hfreq
  choose zs hzsS hzsdist using hφP
  obtain ⟨w, hwS, ψ, hψ, hψlim⟩ := hS.tendsto_subseq hzsS
  have hwU : w ∈ U := hSU hwS
  have hlim : Tendsto (fun n => zs (ψ n)) atTop (𝓝 w) := hψlim
  have hsub : ∀ z ∈ U, Tendsto (fun n => f (φ (ψ n)) z) atTop (𝓝 (g z)) := fun z hz =>
    (hconv z hz).comp (hφ.comp hψ).tendsto_atTop
  have h1 := eventually_subdifferential_subset_add_closedBall hU hUc (fun n => hf (φ (ψ n)))
    (fun n => hfp (φ (ψ n))) (fun n => hfU (φ (ψ n))) hg hgp hgU hsub hwU hlim
    (by positivity : (0 : ℝ) < ε / 3)
  have hwint : w ∈ interior (convexDom g) := interior_maximal hgU hU hwU
  have h2 : ∀ᶠ n in atTop, subdifferential (innerₗ E) g (zs (ψ n))
      ⊆ subdifferential (innerₗ E) g w + closedBall (0 : E) (ε / 3) :=
    hlim.eventually (eventually_nhds_subdifferential_subset_add_closedBall hg hgp hwint
      (by positivity))
  obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
  have hzU : zs (ψ n) ∈ U := hSU (hzsS (ψ n))
  have hA : dist (Gf (φ (ψ n)) (zs (ψ n))) (Gg w) ≤ ε / 3 :=
    dist_le_of_subdifferential_subset (hf _) hg (hgradf _ _ hzU) (hgradg w hwU) hn1
  have hB : dist (Gg (zs (ψ n))) (Gg w) ≤ ε / 3 :=
    dist_le_of_subdifferential_subset hg hg (hgradg _ hzU) (hgradg w hwU) hn2
  have hlow := hzsdist (ψ n)
  have htri := dist_triangle (Gg (zs (ψ n))) (Gg w) (Gf (φ (ψ n)) (zs (ψ n)))
  rw [dist_comm (Gg w)] at htri
  linarith

end GradientLimit

end ConvexAnalysis

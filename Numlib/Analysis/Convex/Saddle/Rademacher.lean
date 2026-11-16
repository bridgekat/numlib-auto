/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Rademacher
import Numlib.Analysis.Convex.Saddle.Differential

/-!
# Differentiability almost everywhere of a saddle-function

Let $C \subseteq U$ and $D \subseteq X$ be open convex sets in finite-dimensional real normed
spaces, and let $K : U \times X \to \mathbb{R}$ be concave-convex on $C \times D$. Then $K$ is
differentiable at almost every point of $C \times D$, its points of differentiability are dense in
$C \times D$, and, in inner product spaces, the gradient mapping
$\nabla K = (\nabla_1 K, \nabla_2 K)$ is continuous on the set of these points. If concave-convex
functions $K_i$ converge pointwise to $K$ on $C \times D$, then their gradients converge to
$\nabla K$ at each point where all the gradients exist, and uniformly on every compact subset of
$C \times D$ when all the gradients exist everywhere. The presentation follows
[rockafellar1970convex], §35.

Concavity and convexity give a Lipschitz constant on a ball around each point, and Rademacher's
theorem then gives differentiability almost everywhere. The statements on convergence come from the
upper semicontinuity of the saddle subdifferential $\partial K$, which reduces to a single point
where $K$ is differentiable. For this reason the pointwise statement needs differentiability only at
the point in question.

## Main results

* `ConvexAnalysis.ConcaveConvexOn.exists_lipschitzOnWith_ball`: $K$ is Lipschitz on a ball around
  each point of $C \times D$.
* `ConvexAnalysis.ae_differentiableAt_of_concaveConvexOn`,
  `ConvexAnalysis.measure_diff_differentiableAt_of_concaveConvexOn`: $K$ is differentiable almost
  everywhere on $C \times D$, in two forms; this is Theorem 35.9 of [rockafellar1970convex].
* `ConvexAnalysis.subset_closure_differentiableAt_of_concaveConvexOn`,
  `ConvexAnalysis.continuousOn_saddleGradient`: the points of differentiability are dense, and the
  gradient is continuous on them; this is also part of Theorem 35.9 of [rockafellar1970convex].
* `ConvexAnalysis.tendsto_of_hasSaddleGradientAt`,
  `ConvexAnalysis.tendstoUniformlyOn_saddleGradient`: gradients converge under pointwise convergence
  of the functions, uniformly on compact sets; this is Theorem 35.10 of [rockafellar1970convex].

## Implementation notes

* `ConvexAnalysis.HasSaddleGradientAt K q p` says $\nabla K(p) = q$ for a pair $q \in U \times X$.
  There is no canonical $\nabla K$ without choice, so the statements on continuity and convergence
  take any $G$ with `ConvexAnalysis.HasSaddleGradientAt K (G p) p` on the set in question. Such a
  $G$ is unique there, because `ConvexAnalysis.prodInnerL` is injective.
* The ball $\varepsilon B$ is the ball of the supremum norm of `U × X`. The Euclidean ball differs
  from it by a bounded factor, and every statement quantifies over all $\varepsilon > 0$.
-/

open Set Filter MeasureTheory Metric Topology
open scoped NNReal Pointwise

namespace ConvexAnalysis

/-! ### A Lipschitz constant on a ball -/

section Lipschitz

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  {C : Set U} {D : Set X} {K : U × X → ℝ} {p : U × X}

/-- Let $C \subseteq U$ and $D \subseteq X$ be open convex sets in finite-dimensional real normed
spaces, and let $K : U \times X \to \mathbb{R}$ be concave-convex on $C \times D$. Then for
every $p \in C \times D$ there is $r > 0$ such that the ball $B(p, r)$ lies in $C \times D$ and
$K$ is Lipschitz on $B(p, r)$ with some constant $k \ge 0$.

The ball is open, which is what Rademacher's theorem needs: differentiability within an open set
is differentiability. Local Lipschitz continuity first gives a constant on a product of compact
sets, and the proof then shrinks this product to an open ball. -/
theorem ConcaveConvexOn.exists_lipschitzOnWith_ball (hCo : IsOpen C) (hCc : Convex ℝ C)
    (hDo : IsOpen D) (hDc : Convex ℝ D) (hK : ConcaveConvexOn C D K) (hp : p ∈ C ×ˢ D) :
    ∃ r > 0, ball p r ⊆ C ×ˢ D ∧ ∃ k : ℝ≥0, LipschitzOnWith k K (ball p r) := by
  obtain ⟨u, v⟩ := p
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 (hCo.prod hDo) (u, v) hp
  have hhalf : r / 2 < r := by linarith
  have hcb : closedBall u (r / 2) ×ˢ closedBall v (r / 2) ⊆ C ×ˢ D := by
    refine subset_trans ?_ hsub
    rw [← ball_prod_same]
    exact Set.prod_mono (closedBall_subset_ball hhalf) (closedBall_subset_ball hhalf)
  have hzero : (0 : ℝ) ≤ r / 2 := by linarith
  have hriC : closedBall u (r / 2) ⊆ ri C := fun w hw =>
    Convex.interior_subset_relint
      (by rw [hCo.interior_eq]; exact (hcb (Set.mk_mem_prod hw (mem_closedBall_self hzero))).1)
  have hriD : closedBall v (r / 2) ⊆ ri D := fun x hx =>
    Convex.interior_subset_relint
      (by rw [hDo.interior_eq]; exact (hcb (Set.mk_mem_prod (mem_closedBall_self hzero) hx)).2)
  obtain ⟨k, hk⟩ := hK.exists_lipschitzOnWith_of_isCompact hCc hDc
    (isCompact_closedBall u (r / 2)) hriC (isCompact_closedBall v (r / 2)) hriD
  refine ⟨r / 2, by linarith, (ball_subset_ball hhalf.le).trans hsub, k, hk.mono ?_⟩
  rw [← ball_prod_same]
  exact Set.prod_mono ball_subset_closedBall ball_subset_closedBall

end Lipschitz

/-! ### Differentiability almost everywhere -/

section AlmostEverywhere

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  {C : Set U} {D : Set X} {K : U × X → ℝ}
  [MeasurableSpace (U × X)] [BorelSpace (U × X)] {μ : Measure (U × X)} [μ.IsAddHaarMeasure]

/-- Let $C \subseteq U$ and $D \subseteq X$ be open convex sets in finite-dimensional real normed
spaces, let $K : U \times X \to \mathbb{R}$ be concave-convex on $C \times D$, and let $\mu$ be
an additive Haar measure on $U \times X$. Then for $\mu$-almost every $p$, if $p \in C \times D$
then $K$ is differentiable at $p$. This is part of Theorem 35.9 of [rockafellar1970convex]. -/
theorem ae_differentiableAt_of_concaveConvexOn (hCo : IsOpen C) (hCc : Convex ℝ C) (hDo : IsOpen D)
    (hDc : Convex ℝ D) (hK : ConcaveConvexOn C D K) :
    ∀ᵐ p ∂μ, p ∈ C ×ˢ D → DifferentiableAt ℝ K p := by
  choose! r hr hball k hk using fun p (hp : p ∈ C ×ˢ D) =>
    hK.exists_lipschitzOnWith_ball hCo hCc hDo hDc hp
  obtain ⟨T, hTc, hTeq⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun q : (C ×ˢ D : Set (U × X)) => ball (q : U × X) (r q)) fun _ => isOpen_ball
  have hcover : ∀ p ∈ C ×ˢ D, ∃ q ∈ T, p ∈ ball ((q : U × X)) (r q) := by
    intro p hp
    have hmem : p ∈ ⋃ q : (C ×ˢ D : Set (U × X)), ball ((q : U × X)) (r q) :=
      Set.mem_iUnion.2 ⟨⟨p, hp⟩, mem_ball_self (hr p hp)⟩
    rw [← hTeq] at hmem
    simpa using hmem
  have hae : ∀ᵐ p ∂μ, ∀ q ∈ T, p ∈ ball ((q : U × X)) (r q) →
      DifferentiableWithinAt ℝ K (ball ((q : U × X)) (r q)) p :=
    (ae_ball_iff hTc).2 fun q _ => (hk (q : U × X) q.2).ae_differentiableWithinAt_of_mem
  filter_upwards [hae] with p hp hpU
  obtain ⟨q, hqT, hpq⟩ := hcover p hpU
  exact (hp q hqT hpq).differentiableAt (isOpen_ball.mem_nhds hpq)

/-- Under the hypotheses of `ConvexAnalysis.ae_differentiableAt_of_concaveConvexOn`, the set of
points of $C \times D$ at which $K$ is not differentiable has $\mu$-measure zero. -/
theorem measure_diff_differentiableAt_of_concaveConvexOn (hCo : IsOpen C) (hCc : Convex ℝ C)
    (hDo : IsOpen D) (hDc : Convex ℝ D) (hK : ConcaveConvexOn C D K) :
    μ ((C ×ˢ D) \ {p | DifferentiableAt ℝ K p}) = 0 := by
  have hae := ae_differentiableAt_of_concaveConvexOn (μ := μ) hCo hCc hDo hDc hK
  rw [ae_iff] at hae
  refine measure_mono_null (fun p hp => ?_) hae
  change ¬(p ∈ C ×ˢ D → DifferentiableAt ℝ K p)
  exact fun hcon => hp.2 (hcon hp.1)

end AlmostEverywhere

section Dense

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  {C : Set U} {D : Set X} {K : U × X → ℝ}

/-- Let $C \subseteq U$ and $D \subseteq X$ be open convex sets in finite-dimensional real normed
spaces, and let $K : U \times X \to \mathbb{R}$ be concave-convex on $C \times D$. Then
$C \times D$ lies in the closure of the set of points at which $K$ is differentiable. This is
part of Theorem 35.9 of [rockafellar1970convex].

No measure appears in the statement; the proof uses an additive Haar measure and
`ConvexAnalysis.measure_diff_differentiableAt_of_concaveConvexOn`. -/
theorem subset_closure_differentiableAt_of_concaveConvexOn (hCo : IsOpen C) (hCc : Convex ℝ C)
    (hDo : IsOpen D) (hDc : Convex ℝ D) (hK : ConcaveConvexOn C D K) :
    C ×ˢ D ⊆ closure {p | DifferentiableAt ℝ K p} := by
  let _ : MeasurableSpace (U × X) := borel (U × X)
  have _ : BorelSpace (U × X) := ⟨rfl⟩
  let w := Module.Basis.ofVectorSpace ℝ (U × X)
  intro p hp
  refine mem_closure_iff.2 fun V hV hpV => ?_
  by_contra hne
  have hsub : V ∩ (C ×ˢ D) ⊆ (C ×ˢ D) \ {z | DifferentiableAt ℝ K z} := by
    rintro z ⟨hzV, hzU⟩
    exact ⟨hzU, fun hzD => hne ⟨z, hzV, hzD⟩⟩
  have hpos : 0 < w.addHaar (V ∩ (C ×ˢ D)) :=
    (hV.inter (hCo.prod hDo)).measure_pos _ ⟨p, hpV, hp⟩
  exact hpos.ne' (measure_mono_null hsub
    (measure_diff_differentiableAt_of_concaveConvexOn hCo hCc hDo hDc hK))

end Dense

/-! ### Continuity of the gradient -/

section GradientContinuity

variable {U X : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  {C : Set U} {D : Set X} {K : U × X → ℝ}

/-- Let $C \subseteq U$ and $D \subseteq X$ be open convex sets in finite-dimensional real inner
product spaces, and let $K : U \times X \to \mathbb{R}$ be concave-convex on $C \times D$. Let
$S \subseteq C \times D$, and let $G : U \times X \to U \times X$ satisfy $\nabla K(p) = G(p)$
for every $p \in S$. Then $G$ is continuous on $S$. This is part of Theorem 35.9 of
[rockafellar1970convex].

The proof uses the upper semicontinuity of $\partial K$, where both halves of $\partial K$
reduce to a single point. -/
theorem continuousOn_saddleGradient (hCo : IsOpen C) (hCc : Convex ℝ C) (hDo : IsOpen D)
    (hDc : Convex ℝ D) (hK : ConcaveConvexOn C D K) {S : Set (U × X)} (hS : S ⊆ C ×ˢ D)
    {G : U × X → U × X} (hG : ∀ p ∈ S, HasSaddleGradientAt K (G p) p) : ContinuousOn G S := by
  intro x hx
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  have hev := eventually_nhds_saddleSubdifferentialOn_subset hCo hCc hDo hDc hK (hS hx).1 (hS hx).2
    (half_pos hε)
  have hxs : saddleSubdifferentialOn C D K x = {G x} :=
    saddleSubdifferentialOn_eq_singleton_of_hasSaddleGradientAt hCo hDo hK (hS hx).1 (hS hx).2
      (hG x hx)
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with z hzsub hzS
  have hzs : saddleSubdifferentialOn C D K z = {G z} :=
    saddleSubdifferentialOn_eq_singleton_of_hasSaddleGradientAt hCo hDo hK (hS hzS).1 (hS hzS).2
      (hG z hzS)
  have hmem : G z ∈ saddleSubdifferentialOn C D K x + closedBall (0 : U × X) (ε / 2) :=
    hzsub (by rw [hzs]; rfl)
  rw [hxs] at hmem
  rw [dist_eq_norm]
  exact lt_of_le_of_lt (norm_sub_le_of_mem_singleton_add_closedBall hmem) (half_lt_self hε)

end GradientContinuity

/-! ### Convergence of gradients -/

section GradientLimit

variable {U X : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  {C : Set U} {D : Set X} {K : U × X → ℝ} {Ks : ℕ → U × X → ℝ} {p : U × X}

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] in
/-- **An inclusion of single-point subdifferentials bounds the distance of the gradients.** Let
$C \subseteq U$ and $D \subseteq X$ be open sets in real inner product spaces, and let
$L, M : U \times X \to \mathbb{R}$ be concave-convex on $C \times D$. Let $p, p' \in C \times D$
with $\nabla L(p) = a$ and $\nabla M(p') = b$, and let $\varepsilon \in \mathbb{R}$. If
$$\partial L(p) \subseteq \partial M(p') + \varepsilon B,$$
where $\varepsilon B$ is the closed ball of radius $\varepsilon$ about the origin, then
$\operatorname{dist}(a, b) \le \varepsilon$.

The subdifferentials are `ConvexAnalysis.saddleSubdifferentialOn C D`, and the distance and the
ball are those of the supremum norm of `U × X`. -/
theorem dist_le_of_saddleSubdifferentialOn_subset (hCo : IsOpen C) (hDo : IsOpen D)
    {L M : U × X → ℝ} {p' a b : U × X} {ε : ℝ} (hL : ConcaveConvexOn C D L)
    (hM : ConcaveConvexOn C D M) (hp : p ∈ C ×ˢ D) (hp' : p' ∈ C ×ˢ D)
    (ha : HasSaddleGradientAt L a p) (hb : HasSaddleGradientAt M b p')
    (hsub : saddleSubdifferentialOn C D L p
      ⊆ saddleSubdifferentialOn C D M p' + closedBall (0 : U × X) ε) :
    dist a b ≤ ε := by
  have hLa : saddleSubdifferentialOn C D L p = {a} :=
    saddleSubdifferentialOn_eq_singleton_of_hasSaddleGradientAt hCo hDo hL hp.1 hp.2 ha
  have hMb : saddleSubdifferentialOn C D M p' = {b} :=
    saddleSubdifferentialOn_eq_singleton_of_hasSaddleGradientAt hCo hDo hM hp'.1 hp'.2 hb
  have hmem : a ∈ saddleSubdifferentialOn C D M p' + closedBall (0 : U × X) ε :=
    hsub (by rw [hLa]; rfl)
  rw [hMb] at hmem
  rw [dist_eq_norm]
  exact norm_sub_le_of_mem_singleton_add_closedBall hmem

/-- Let $C \subseteq U$ and $D \subseteq X$ be open convex sets in finite-dimensional real inner
product spaces, let $K_i$ ($i \in \mathbb{N}$) and $K$ be functions $U \times X \to \mathbb{R}$
that are concave-convex on $C \times D$, and let $K_i(q) \to K(q)$ for every $q \in C \times D$.
Let $p \in C \times D$, and let $\nabla K_i(p) = G_i$ for every $i$ and $\nabla K(p) = G'$. Then
$G_i \to G'$. This is part of Theorem 35.10 of [rockafellar1970convex].

The proof uses the convergence of the subdifferentials along the constant sequence of points,
where all the subdifferentials reduce to single points. Differentiability is needed only at $p$. -/
theorem tendsto_of_hasSaddleGradientAt (hCo : IsOpen C) (hCc : Convex ℝ C) (hDo : IsOpen D)
    (hDc : Convex ℝ D) (hKs : ∀ i, ConcaveConvexOn C D (Ks i)) (hK : ConcaveConvexOn C D K)
    (hconv : ∀ q ∈ C ×ˢ D, Tendsto (fun i => Ks i q) atTop (𝓝 (K q))) (hp : p ∈ C ×ˢ D)
    {G : ℕ → U × X} {G' : U × X} (hG : ∀ i, HasSaddleGradientAt (Ks i) (G i) p)
    (hG' : HasSaddleGradientAt K G' p) : Tendsto G atTop (𝓝 G') := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  have hev := eventually_saddleSubdifferentialOn_subset hCo hCc hDo hDc hKs hK hconv hp.1 hp.2
    (tendsto_const_nhds (x := p.1) (f := (atTop : Filter ℕ)))
    (tendsto_const_nhds (x := p.2) (f := (atTop : Filter ℕ))) (half_pos hε)
  filter_upwards [hev] with i hi
  exact lt_of_le_of_lt
    (dist_le_of_saddleSubdifferentialOn_subset hCo hDo (hKs i) hK hp hp (hG i) hG' hi)
    (half_lt_self hε)

/-- Let $C \subseteq U$ and $D \subseteq X$ be open convex sets in finite-dimensional real inner
product spaces, let $K_i$ ($i \in \mathbb{N}$) and $K$ be functions $U \times X \to \mathbb{R}$
that are concave-convex on $C \times D$, and let $K_i(q) \to K(q)$ for every $q \in C \times D$.
Let $G_i$ and $G$ satisfy $\nabla K_i(q) = G_i(q)$ and $\nabla K(q) = G(q)$ for every
$q \in C \times D$. Then $G_i \to G$ uniformly on every compact set $S \subseteq C \times D$.
This is part of Theorem 35.10 of [rockafellar1970convex].

If the convergence is not uniform on $S$, there are indices $\varphi(n)$ and points $z_n \in S$
with $\|\nabla K(z_n) - \nabla K_{\varphi(n)}(z_n)\| \ge \varepsilon$. A subsequence of $(z_n)$
converges to some $w \in S$, and the convergence of the subdifferentials along this subsequence
and the upper semicontinuity at $w$ give two bounds $\varepsilon / 3$ that contradict this
inequality. -/
theorem tendstoUniformlyOn_saddleGradient (hCo : IsOpen C) (hCc : Convex ℝ C) (hDo : IsOpen D)
    (hDc : Convex ℝ D) (hKs : ∀ i, ConcaveConvexOn C D (Ks i)) (hK : ConcaveConvexOn C D K)
    (hconv : ∀ q ∈ C ×ˢ D, Tendsto (fun i => Ks i q) atTop (𝓝 (K q)))
    {Gs : ℕ → U × X → U × X} {G : U × X → U × X}
    (hGs : ∀ i, ∀ q ∈ C ×ˢ D, HasSaddleGradientAt (Ks i) (Gs i q) q)
    (hG : ∀ q ∈ C ×ˢ D, HasSaddleGradientAt K (G q) q)
    {S : Set (U × X)} (hS : IsCompact S) (hSU : S ⊆ C ×ˢ D) :
    TendstoUniformlyOn Gs G atTop S := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra hcon
  have hfreq : ∃ᶠ i in atTop, ∃ z ∈ S, ε ≤ dist (G z) (Gs i z) := by
    refine (Filter.not_eventually.1 hcon).mono fun i hi => ?_
    push Not at hi
    exact hi
  obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_of_frequently_atTop hfreq
  choose zs hzsS hzsdist using hφP
  obtain ⟨w, hwS, ψ, hψ, hψlim⟩ := hS.tendsto_subseq hzsS
  have hwU : w ∈ C ×ˢ D := hSU hwS
  have hlim : Tendsto (fun n => zs (ψ n)) atTop (𝓝 w) := hψlim
  have hsub : ∀ q ∈ C ×ˢ D, Tendsto (fun n => Ks (φ (ψ n)) q) atTop (𝓝 (K q)) := fun q hq =>
    (hconv q hq).comp (hφ.comp hψ).tendsto_atTop
  have h1 := eventually_saddleSubdifferentialOn_subset hCo hCc hDo hDc (fun n => hKs (φ (ψ n))) hK
    hsub hwU.1 hwU.2 ((continuous_fst.tendsto w).comp hlim) ((continuous_snd.tendsto w).comp hlim)
    (by positivity : (0 : ℝ) < ε / 3)
  have h2 : ∀ᶠ n in atTop, saddleSubdifferentialOn C D K (zs (ψ n))
      ⊆ saddleSubdifferentialOn C D K w + closedBall (0 : U × X) (ε / 3) :=
    hlim.eventually (eventually_nhds_saddleSubdifferentialOn_subset hCo hCc hDo hDc hK hwU.1 hwU.2
      (by positivity))
  obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
  have hzU : zs (ψ n) ∈ C ×ˢ D := hSU (hzsS (ψ n))
  have hA : dist (Gs (φ (ψ n)) (zs (ψ n))) (G w) ≤ ε / 3 :=
    dist_le_of_saddleSubdifferentialOn_subset hCo hDo (hKs _) hK hzU
        hwU (hGs _ _ hzU) (hG w hwU) hn1
  have hB : dist (G (zs (ψ n))) (G w) ≤ ε / 3 :=
    dist_le_of_saddleSubdifferentialOn_subset hCo hDo hK hK hzU hwU (hG _ hzU) (hG w hwU) hn2
  have hlow := hzsdist (ψ n)
  have htri := dist_triangle (G (zs (ψ n))) (G w) (Gs (φ (ψ n)) (zs (ψ n)))
  rw [dist_comm (G w)] at htri
  linarith

end GradientLimit

end ConvexAnalysis

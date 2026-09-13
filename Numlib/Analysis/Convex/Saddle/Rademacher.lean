import Mathlib.Analysis.Calculus.Rademacher
import Numlib.Analysis.Convex.Saddle.Differential

/-!
# Differentiability almost everywhere of a saddle-function

A finite concave-convex function on an open rectangle `C × D` is differentiable almost everywhere
there, its points of differentiability are dense, and the gradient mapping is continuous on them.
Gradients also converge wherever the functions converge pointwise, uniformly on every compact
subset.

Convexity supplies only a local Lipschitz constant on a ball, after which Rademacher's theorem does
the analysis. The convergence statements come from upper semicontinuity of the saddle
subdifferential, with the subdifferentials collapsed to singletons at points of differentiability;
in particular the pointwise clause needs differentiability only at the point in question.

## Main results

* `ConcaveConvexOn.exists_lipschitzOnWith_ball` — a Lipschitz constant on a *ball*, which is what
  Rademacher's theorem needs: differentiability within an open set is differentiability.
* `ae_differentiableAt_of_concaveConvexOn`, `measure_diff_differentiableAt_of_concaveConvexOn`,
  `subset_closure_differentiableAt_of_concaveConvexOn`, `continuousOn_saddleGradient` —
  differentiability almost everywhere in two forms, then density and continuity of the gradient
  (Theorem 35.9 in [^1]).
* `tendsto_of_hasSaddleGradientAt`, `tendstoUniformlyOn_saddleGradient` — gradients converge under
  pointwise convergence, uniformly on compact sets (Theorem 35.10 in [^1]).

## Implementation notes

`HasSaddleGradientAt K q p` says `∇K p = q` for a pair `q : U × X`, and there is no canonical `∇K`
without choice, so the continuity and convergence statements take any `G` with
`HasSaddleGradientAt K (G p) p` on the set in question; `prodInnerL` is injective, so such a `G` is
unique there. The `εB` is the supremum ball of `U × X`; the Euclidean ball differs from it by a
bounded factor, and every statement quantifies over all `ε > 0`.

## References

[^1]: R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §35.
-/

open Set Filter MeasureTheory Metric Topology
open scoped NNReal Pointwise

namespace ConvexAnalysis

/-! ### A Lipschitz constant on a ball -/

section Lipschitz

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  {C : Set U} {D : Set X} {K : U × X → ℝ} {p : U × X}

/-- A finite concave-convex function on an open rectangle is Lipschitz on a whole *ball* around
each of its points. Local Lipschitzness gives a constant on a product of compact sets; shrinking to
an open ball makes it open as well, which is what upgrades `DifferentiableWithinAt` to
`DifferentiableAt`. -/
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
    Convex.interior_subset_relint hCc ⟨u, by rw [hCo.interior_eq]; exact hp.1⟩
      (by rw [hCo.interior_eq]; exact (hcb (Set.mk_mem_prod hw (mem_closedBall_self hzero))).1)
  have hriD : closedBall v (r / 2) ⊆ ri D := fun x hx =>
    Convex.interior_subset_relint hDc ⟨v, by rw [hDo.interior_eq]; exact hp.2⟩
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

/-- A finite concave-convex function on an open rectangle is differentiable at almost every point
of it. -/
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

/-- The points of the open rectangle at which `K` is not differentiable form a null set. -/
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

/-- The points of differentiability are dense in the open rectangle. No measure appears in the
statement; the proof borrows one. -/
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

/-- The gradient mapping is continuous on any set of points of the open rectangle at which it
exists: upper semicontinuity of `∂K` with both subdifferentials collapsed to singletons. -/
theorem continuousOn_saddleGradient (hCo : IsOpen C) (hCc : Convex ℝ C) (hDo : IsOpen D)
    (hDc : Convex ℝ D) (hK : ConcaveConvexOn C D K) {S : Set (U × X)} (hS : S ⊆ C ×ˢ D)
    {G : U × X → U × X} (hG : ∀ p ∈ S, HasSaddleGradientAt K (G p) p) : ContinuousOn G S := by
  intro x hx
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  have hev := eventually_nhds_subgradientSaddle_subset hCo hCc hDo hDc hK (hS hx).1 (hS hx).2
    (half_pos hε)
  have hxs : subgradientSaddle C D K x = {G x} :=
    subgradientSaddle_eq_singleton_of_hasSaddleGradientAt hCo hDo hK (hS hx).1 (hS hx).2 (hG x hx)
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with z hzsub hzS
  have hzs : subgradientSaddle C D K z = {G z} :=
    subgradientSaddle_eq_singleton_of_hasSaddleGradientAt hCo hDo hK (hS hzS).1 (hS hzS).2
      (hG z hzS)
  have hmem : G z ∈ subgradientSaddle C D K x + closedBall (0 : U × X) (ε / 2) :=
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
/-- **An inclusion of singleton subdifferentials is a bound on gradients.** If `∇L(p) = a`,
`∇M(p') = b` and `∂L(p) ⊆ ∂M(p') + εB`, then `‖a - b‖ ≤ ε`. -/
theorem dist_le_of_subgradientSaddle_subset (hCo : IsOpen C) (hDo : IsOpen D)
    {L M : U × X → ℝ} {p' a b : U × X} {ε : ℝ} (hL : ConcaveConvexOn C D L)
    (hM : ConcaveConvexOn C D M) (hp : p ∈ C ×ˢ D) (hp' : p' ∈ C ×ˢ D)
    (ha : HasSaddleGradientAt L a p) (hb : HasSaddleGradientAt M b p')
    (hsub : subgradientSaddle C D L p ⊆ subgradientSaddle C D M p' + closedBall (0 : U × X) ε) :
    dist a b ≤ ε := by
  have hLa : subgradientSaddle C D L p = {a} :=
    subgradientSaddle_eq_singleton_of_hasSaddleGradientAt hCo hDo hL hp.1 hp.2 ha
  have hMb : subgradientSaddle C D M p' = {b} :=
    subgradientSaddle_eq_singleton_of_hasSaddleGradientAt hCo hDo hM hp'.1 hp'.2 hb
  have hmem : a ∈ subgradientSaddle C D M p' + closedBall (0 : U × X) ε :=
    hsub (by rw [hLa]; rfl)
  rw [hMb] at hmem
  rw [dist_eq_norm]
  exact norm_sub_le_of_mem_singleton_add_closedBall hmem

/-- The gradients of finite concave-convex functions converging pointwise on an open rectangle
converge at every point of it. Subdifferential convergence along the constant sequence of points,
with the subdifferentials collapsed to singletons; differentiability is needed only at the point in
question. -/
theorem tendsto_of_hasSaddleGradientAt (hCo : IsOpen C) (hCc : Convex ℝ C) (hDo : IsOpen D)
    (hDc : Convex ℝ D) (hKs : ∀ i, ConcaveConvexOn C D (Ks i)) (hK : ConcaveConvexOn C D K)
    (hconv : ∀ q ∈ C ×ˢ D, Tendsto (fun i => Ks i q) atTop (𝓝 (K q))) (hp : p ∈ C ×ˢ D)
    {G : ℕ → U × X} {G' : U × X} (hG : ∀ i, HasSaddleGradientAt (Ks i) (G i) p)
    (hG' : HasSaddleGradientAt K G' p) : Tendsto G atTop (𝓝 G') := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  have hev := eventually_subgradientSaddle_subset hCo hCc hDo hDc hKs hK hconv hp.1 hp.2
    (tendsto_const_nhds (x := p.1) (f := (atTop : Filter ℕ)))
    (tendsto_const_nhds (x := p.2) (f := (atTop : Filter ℕ))) (half_pos hε)
  filter_upwards [hev] with i hi
  exact lt_of_le_of_lt (dist_le_of_subgradientSaddle_subset hCo hDo (hKs i) hK hp hp (hG i) hG' hi)
    (half_lt_self hε)

/-- On every compact subset of the open rectangle the gradients converge uniformly.

A failure of uniform convergence on a compact `S` produces indices `φ n` and points `zₙ ∈ S` with
`‖∇K(zₙ) - ∇K_{φ n}(zₙ)‖ ≥ ε`; a convergent subsequence `zₙ → w ∈ S` turns subdifferential
convergence along the subsequence and upper semicontinuity at `w` into two `ε/3` bounds that
contradict it. -/
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
  have h1 := eventually_subgradientSaddle_subset hCo hCc hDo hDc (fun n => hKs (φ (ψ n))) hK hsub
    hwU.1 hwU.2 ((continuous_fst.tendsto w).comp hlim) ((continuous_snd.tendsto w).comp hlim)
    (by positivity : (0 : ℝ) < ε / 3)
  have h2 : ∀ᶠ n in atTop, subgradientSaddle C D K (zs (ψ n))
      ⊆ subgradientSaddle C D K w + closedBall (0 : U × X) (ε / 3) :=
    hlim.eventually (eventually_nhds_subgradientSaddle_subset hCo hCc hDo hDc hK hwU.1 hwU.2
      (by positivity))
  obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
  have hzU : zs (ψ n) ∈ C ×ˢ D := hSU (hzsS (ψ n))
  have hA : dist (Gs (φ (ψ n)) (zs (ψ n))) (G w) ≤ ε / 3 :=
    dist_le_of_subgradientSaddle_subset hCo hDo (hKs _) hK hzU hwU (hGs _ _ hzU) (hG w hwU) hn1
  have hB : dist (G (zs (ψ n))) (G w) ≤ ε / 3 :=
    dist_le_of_subgradientSaddle_subset hCo hDo hK hK hzU hwU (hG _ hzU) (hG w hwU) hn2
  have hlow := hzsdist (ψ n)
  have htri := dist_triangle (G (zs (ψ n))) (G w) (Gs (φ (ψ n)) (zs (ψ n)))
  rw [dist_comm (G w)] at htri
  linarith

end GradientLimit

end ConvexAnalysis

/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Module.WeakDual`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-!
# Weak sequential convergence in a normed space

Let $V$ be a normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. A sequence $(v_n)$
**converges weakly** to $u$, written $v_n \rightharpoonup u$, if $\ell(v_n) \to \ell(u)$ for every
$\ell \in V^*$. This file proves the basic facts on weak convergence: a weakly convergent sequence
is bounded, the norm is weakly sequentially lower semicontinuous, $\|u\| \le \liminf_n \|v_n\|$, and
$f_n(v_n) \to g(u)$ when $v_n \rightharpoonup u$ and $f_n \to g$ in norm. It proves the same facts
for weak-$*$ convergence in the dual of a Banach space, and the sequential Banach–Alaoglu theorem
for a space isometric to the dual of a separable space. These are Propositions 3.5 and 3.13 and
Corollary 3.30 of [brezis2011functional].

## Main results

* `tendsto_toWeakSpace_iff`: weak convergence is convergence of $\ell(v_n)$ for every bounded linear
  functional $\ell$.
* `exists_norm_le_of_tendsto_toWeakSpace`: a weakly convergent sequence is bounded in norm.
* `norm_le_liminf_norm_of_weak_tendsto`: **the norm is weakly sequentially lower semicontinuous**,
  $\|u\| \le \liminf_n \|v_n\|$. This makes a minimization problem over a weakly closed set
  solvable: a minimizing sequence has a weak limit point whose norm is not larger.
* `tendsto_apply_of_tendsto_toWeakSpace_of_tendsto`: $f_n(v_n) \to g(u)$ when
  $v_n \rightharpoonup u$ and $f_n \to g$ in norm.
* `WeakDual.continuous_weakSpace_toWeakDual`: on the dual, the weak-$*$ topology is coarser than the
  weak topology.
* `exists_norm_le_of_tendsto_toWeakDual`, `norm_le_liminf_norm_of_weakStar_tendsto` and
  `tendsto_apply_of_tendsto_toWeakDual_of_tendsto`: the weak-$*$ versions of the three sequential
  facts, for the dual of a Banach space.
* `LinearIsometryEquiv.exists_subseq_tendsto_apply`: a bounded sequence in a space isometric to the
  dual of a separable space has a weak-$*$ convergent subsequence.

## Implementation notes

* Weak convergence $v_n \rightharpoonup u$ is convergence of `toWeakSpace 𝕜 V (v n)` to
  `toWeakSpace 𝕜 V u` in the weak topology of `WeakSpace 𝕜 V`, and `tendsto_toWeakSpace_iff` relates
  it to the definition above. Weak-$*$ convergence in the dual is convergence in `WeakDual 𝕜 V`.
* The weak-$*$ facts need $V$ complete, because the uniform boundedness principle is applied on $V$
  itself. The weak facts need no completeness, because the principle is applied on the dual, which
  is always complete.
-/

open Filter Topology Bornology

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- Let $V$ be a normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $(v_i)$ be a net
in $V$ along a filter $l$, and let $u \in V$. Then $v_i$ converges to $u$ in the weak topology
if and only if $\ell(v_i) \to \ell(u)$ for every $\ell \in V^*$. -/
theorem tendsto_toWeakSpace_iff {ι : Type*} {l : Filter ι} {v : ι → V} {u : V} :
    Tendsto (fun n => toWeakSpace 𝕜 V (v n)) l (𝓝 (toWeakSpace 𝕜 V u)) ↔
      ∀ ℓ : StrongDual 𝕜 V, Tendsto (fun n => ℓ (v n)) l (𝓝 (ℓ u)) :=
  WeakBilin.tendsto_iff_forall_eval_tendsto (B := (topDualPairing 𝕜 V).flip) fun _ _ h => by
    by_contra hne
    obtain ⟨f, hf⟩ := SeparatingDual.exists_separating_of_ne (R := 𝕜) hne
    exact hf (DFunLike.congr_fun h f)

/-- Let $V$ be a normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. If
$v_n \rightharpoonup u$ weakly, then there is $C$ with $\|v_n\| \le C$ for all $n$.

The proof applies the uniform boundedness principle to the images of the $v_n$ in the bidual, a
family of functionals on the complete space $V^*$. Weak convergence makes this family pointwise
bounded, and the isometric embedding carries the resulting bound back to $V$. -/
theorem exists_norm_le_of_tendsto_toWeakSpace {v : ℕ → V} {u : V}
    (h : Tendsto (fun n => toWeakSpace 𝕜 V (v n)) atTop (𝓝 (toWeakSpace 𝕜 V u))) :
    ∃ C : ℝ, ∀ n, ‖v n‖ ≤ C := by
  rw [tendsto_toWeakSpace_iff] at h
  have hb : ∀ ℓ : StrongDual 𝕜 V,
      ∃ C : ℝ, ∀ n, ‖NormedSpace.inclusionInDoubleDual 𝕜 V (v n) ℓ‖ ≤ C := by
    intro ℓ
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _ (h ℓ))
    exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩
  obtain ⟨C, hC⟩ := banach_steinhaus hb
  refine ⟨C, fun n => ?_⟩
  rw [← (NormedSpace.inclusionInDoubleDualLi 𝕜).norm_map (v n)]
  exact hC n

/-- Let $V$ be a normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. If
$v_n \rightharpoonup u$ weakly, then $$\|u\| \le \liminf_{n \to \infty} \|v_n\|.$$ So the norm
is weakly sequentially lower semicontinuous.

Equality can fail: an orthonormal sequence in a Hilbert space converges weakly to $0$, while
every term has norm $1$. So the norm is not weakly continuous. The proof evaluates a norming
functional $\ell$ of $u$, for which $\|u\| = \ell(u) = \lim_n \ell(v_n)$ and
$|\ell(v_n)| \le \|v_n\|$. The boundedness of $(\|v_n\|)$ makes the comparison of the $\liminf$
valid. -/
theorem norm_le_liminf_norm_of_weak_tendsto {v : ℕ → V} {u : V}
    (h : Tendsto (fun n => toWeakSpace 𝕜 V (v n)) atTop (𝓝 (toWeakSpace 𝕜 V u))) :
    ‖u‖ ≤ liminf (fun n => ‖v n‖) atTop := by
  obtain ⟨C, hC⟩ := exists_norm_le_of_tendsto_toWeakSpace h
  rw [tendsto_toWeakSpace_iff] at h
  obtain ⟨ℓ, hℓ, hval⟩ := exists_dual_vector'' 𝕜 u
  have hlim : Tendsto (fun n => ‖ℓ (v n)‖) atTop (𝓝 ‖ℓ u‖) := (h ℓ).norm
  have hcobdd : IsCoboundedUnder (· ≥ ·) atTop fun n => ‖v n‖ := by
    refine ⟨C, fun a ha => ?_⟩
    rw [Filter.eventually_map] at ha
    obtain ⟨n, hn⟩ := ha.exists
    exact hn.trans (hC n)
  have hle : ∀ n, ‖ℓ (v n)‖ ≤ ‖v n‖ := fun n =>
    (ℓ.le_opNorm (v n)).trans (by simpa using mul_le_mul_of_nonneg_right hℓ (norm_nonneg (v n)))
  calc ‖u‖ = ‖ℓ u‖ := by rw [hval, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg u)]
    _ = liminf (fun n => ‖ℓ (v n)‖) atTop := hlim.liminf_eq.symm
    _ ≤ liminf (fun n => ‖v n‖) atTop :=
        liminf_le_liminf (Filter.Eventually.of_forall hle) hlim.isBoundedUnder_ge hcobdd

/-- Let $V$ be a normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. If
$x_n \rightharpoonup u$ weakly in $V$ and $f_n \to g$ in the norm of $V^*$, then
$f_n(x_n) \to g(u)$.

The estimate is $|f_n(x_n) - g(u)| \le \|f_n - g\| \, \|x_n\| + |g(x_n) - g(u)|$. The first term
tends to $0$ because a weakly convergent sequence is bounded
(`exists_norm_le_of_tendsto_toWeakSpace`), and the second term tends to $0$ by weak convergence
tested against $g$. -/
theorem tendsto_apply_of_tendsto_toWeakSpace_of_tendsto {x : ℕ → V} {u : V}
    {f : ℕ → StrongDual 𝕜 V} {g : StrongDual 𝕜 V}
    (hx : Tendsto (fun n => toWeakSpace 𝕜 V (x n)) atTop (𝓝 (toWeakSpace 𝕜 V u)))
    (hf : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun n => f n (x n)) atTop (𝓝 (g u)) := by
  obtain ⟨C, hC⟩ := exists_norm_le_of_tendsto_toWeakSpace hx
  rw [tendsto_toWeakSpace_iff] at hx
  rw [tendsto_iff_norm_sub_tendsto_zero] at hf ⊢
  have h1 : Tendsto (fun n => ‖f n - g‖ * C + ‖g (x n) - g u‖) atTop (𝓝 0) := by
    have := (hf.mul_const C).add ((tendsto_iff_norm_sub_tendsto_zero.1 (hx g)))
    simpa using this
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h1
  calc ‖f n (x n) - g u‖ = ‖(f n - g) (x n) + (g (x n) - g u)‖ := by
        congr 1; simp
    _ ≤ ‖(f n - g) (x n)‖ + ‖g (x n) - g u‖ := norm_add_le _ _
    _ ≤ ‖f n - g‖ * C + ‖g (x n) - g u‖ := by
        gcongr
        exact ((f n - g).le_opNorm (x n)).trans (by gcongr; exact hC n)

/-!
### The weak-$*$ topology on the dual

On the dual $V^*$ there are three topologies: the norm topology, the weak topology
`WeakSpace 𝕜 (StrongDual 𝕜 V)`, and the weak-$*$ topology `WeakDual 𝕜 V`, each coarser than the one
before. The Mathlib theorem `NormedSpace.Dual.toWeakDual_continuous` compares the first and the
third. The statements below compare the second and the third, and give the weak-$*$ versions of the
three sequential facts above. Boundedness of a weak-$*$ convergent sequence is the uniform
boundedness principle on $V$ itself, so it needs $V$ complete, whereas the weak statements need
nothing, because they apply the principle on the complete dual.
-/

/-- Let $V$ be a normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. The identity map from
$V^*$ with the weak topology $\sigma(V^*, V^{**})$ to $V^*$ with the weak-$*$ topology
$\sigma(V^*, V)$ is continuous. So the weak-$*$ topology is coarser than the weak topology.

The evaluation at $x \in V$ is the bounded functional `NormedSpace.inclusionInDoubleDual 𝕜 V x`
on $V^*$, hence continuous for the weak topology of $V^*$. -/
theorem WeakDual.continuous_weakSpace_toWeakDual :
    Continuous (fun f : WeakSpace 𝕜 (StrongDual 𝕜 V) =>
      StrongDual.toWeakDual ((toWeakSpace 𝕜 (StrongDual 𝕜 V)).symm f)) := by
  refine WeakDual.continuous_of_continuous_eval fun x => ?_
  exact WeakBilin.eval_continuous (topDualPairing 𝕜 (StrongDual 𝕜 V)).flip
    (NormedSpace.inclusionInDoubleDual 𝕜 V x)

/-- Let $V$ be a normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. If a sequence $(f_n)$
in $V^*$ converges to $g$ in the weak topology $\sigma(V^*, V^{**})$, then it converges to $g$
in the weak-$*$ topology $\sigma(V^*, V)$. -/
theorem tendsto_toWeakDual_of_tendsto_toWeakSpace {f : ℕ → StrongDual 𝕜 V} {g : StrongDual 𝕜 V}
    (h : Tendsto (fun n => toWeakSpace 𝕜 _ (f n)) atTop (𝓝 (toWeakSpace 𝕜 _ g))) :
    Tendsto (fun n => StrongDual.toWeakDual (f n)) atTop (𝓝 (StrongDual.toWeakDual g)) :=
  (WeakDual.continuous_weakSpace_toWeakDual.tendsto _).comp h

/-- Let $V$ be a Banach space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. If a sequence $(f_n)$
in $V^*$ converges to $g$ in the weak-$*$ topology, then there is $C$ with $\|f_n\| \le C$ for
all $n$.

Weak-$*$ convergence makes the family $(f_n)$ pointwise bounded on $V$, and the uniform
boundedness principle (`banach_steinhaus`, where the completeness of $V$ is used) gives a
uniform bound. -/
theorem exists_norm_le_of_tendsto_toWeakDual [CompleteSpace V] {f : ℕ → StrongDual 𝕜 V}
    {g : StrongDual 𝕜 V}
    (h : Tendsto (fun n => StrongDual.toWeakDual (f n)) atTop (𝓝 (StrongDual.toWeakDual g))) :
    ∃ C : ℝ, ∀ n, ‖f n‖ ≤ C := by
  rw [tendsto_iff_forall_eval_tendsto_topDualPairing] at h
  have hb : ∀ x : V, ∃ C : ℝ, ∀ n, ‖f n x‖ ≤ C := fun x => by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _ (h x))
    exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩
  exact banach_steinhaus hb

/-- Let $V$ be a Banach space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. If a sequence $(f_n)$
in $V^*$ converges to $g$ in the weak-$*$ topology, then $$\|g\| \le \liminf_{n \to \infty}
\|f_n\|.$$ So the dual norm is weak-$*$ sequentially lower semicontinuous.

For each $x \in V$, $|g(x)| = \lim_n |f_n(x)| \le \liminf_n (\|f_n\| \, \|x\|) = (\liminf_n
\|f_n\|) \|x\|$. The last step holds because $t \mapsto t \|x\|$ is monotone and continuous and
the sequence $(\|f_n\|)$ is bounded (`exists_norm_le_of_tendsto_toWeakDual`). Then
`ContinuousLinearMap.opNorm_le_bound` concludes. -/
theorem norm_le_liminf_norm_of_weakStar_tendsto [CompleteSpace V] {f : ℕ → StrongDual 𝕜 V}
    {g : StrongDual 𝕜 V}
    (h : Tendsto (fun n => StrongDual.toWeakDual (f n)) atTop (𝓝 (StrongDual.toWeakDual g))) :
    ‖g‖ ≤ liminf (fun n => ‖f n‖) atTop := by
  obtain ⟨C, hC⟩ := exists_norm_le_of_tendsto_toWeakDual h
  rw [tendsto_iff_forall_eval_tendsto_topDualPairing] at h
  have hcobdd : IsCoboundedUnder (· ≥ ·) atTop fun n => ‖f n‖ :=
    isCoboundedUnder_ge_of_eventually_le atTop (Filter.Eventually.of_forall hC)
  have hbdd : IsBoundedUnder (· ≥ ·) atTop fun n => ‖f n‖ :=
    isBoundedUnder_of ⟨0, fun n => norm_nonneg _⟩
  have hL : 0 ≤ liminf (fun n => ‖f n‖) atTop :=
    le_liminf_of_le hcobdd (Filter.Eventually.of_forall fun n => norm_nonneg _)
  refine ContinuousLinearMap.opNorm_le_bound _ hL fun x => ?_
  have hlim : Tendsto (fun n => ‖f n x‖) atTop (𝓝 ‖g x‖) := (h x).norm
  have hle : ∀ n, ‖f n x‖ ≤ ‖f n‖ * ‖x‖ := fun n => (f n).le_opNorm x
  calc ‖g x‖ = liminf (fun n => ‖f n x‖) atTop := hlim.liminf_eq.symm
    _ ≤ liminf (fun n => ‖f n‖ * ‖x‖) atTop :=
        liminf_le_liminf (Filter.Eventually.of_forall hle) hlim.isBoundedUnder_ge
          (isCoboundedUnder_ge_of_eventually_le atTop (Filter.Eventually.of_forall fun n =>
            mul_le_mul_of_nonneg_right (hC n) (norm_nonneg x)))
    _ = liminf (fun n => ‖f n‖) atTop * ‖x‖ := by
        have hmono : Monotone (fun t : ℝ => t * ‖x‖) :=
          fun a b hab => mul_le_mul_of_nonneg_right hab (norm_nonneg x)
        exact (hmono.map_liminf_of_continuousAt (fun n => ‖f n‖)
          (continuous_id.mul continuous_const).continuousAt hcobdd hbdd).symm

/-- Let $V$ be a Banach space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. If a sequence $(f_n)$
in $V^*$ converges to $g$ in the weak-$*$ topology and $x_n \to u$ in norm in $V$, then
$f_n(x_n) \to g(u)$.

The estimate is $|f_n(x_n) - g(u)| \le \|f_n\| \, \|x_n - u\| + |f_n(u) - g(u)|$, with $\|f_n\|$
bounded by `exists_norm_le_of_tendsto_toWeakDual`. -/
theorem tendsto_apply_of_tendsto_toWeakDual_of_tendsto [CompleteSpace V] {f : ℕ → StrongDual 𝕜 V}
    {g : StrongDual 𝕜 V} {x : ℕ → V} {u : V}
    (hf : Tendsto (fun n => StrongDual.toWeakDual (f n)) atTop (𝓝 (StrongDual.toWeakDual g)))
    (hx : Tendsto x atTop (𝓝 u)) :
    Tendsto (fun n => f n (x n)) atTop (𝓝 (g u)) := by
  obtain ⟨C, hC⟩ := exists_norm_le_of_tendsto_toWeakDual hf
  rw [tendsto_iff_forall_eval_tendsto_topDualPairing] at hf
  rw [tendsto_iff_norm_sub_tendsto_zero] at hx ⊢
  have h1 : Tendsto (fun n => C * ‖x n - u‖ + ‖f n u - g u‖) atTop (𝓝 0) := by
    have := (hx.const_mul C).add ((tendsto_iff_norm_sub_tendsto_zero.1 (hf u)))
    rw [mul_zero, add_zero] at this
    exact this
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h1
  calc ‖f n (x n) - g u‖ = ‖f n (x n - u) + (f n u - g u)‖ := by
        congr 1; simp
    _ ≤ ‖f n (x n - u)‖ + ‖f n u - g u‖ := norm_add_le _ _
    _ ≤ C * ‖x n - u‖ + ‖f n u - g u‖ := by
        gcongr
        exact ((f n).le_opNorm (x n - u)).trans (by gcongr; exact hC n)

/-- **Sequential Banach–Alaoglu theorem** for a space isometric to a separable dual. Let $V$ be a
separable normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $X$ be a normed
space, and let $e \colon X \to V^*$ be an isometric isomorphism. Let $(f_n)$ be a sequence in
$X$ with $\|f_n\| \le C$ for all $n$. Then there are a strictly increasing
$\varphi \colon \mathbb{N} \to \mathbb{N}$ and $g \in X$ with $$e(f_{\varphi(k)})(x) \to e(g)(x)
\quad \text{for every } x \in V.$$ This is Corollary 3.30 of [brezis2011functional].

The convergence is weak-$*$ convergence, transported to $X$ by $e$. The proof uses the Mathlib
theorem `WeakDual.isSeqCompact_closedBall`. The case $X = L^\infty = (L^1)^*$ is §4.3 C of
[brezis2011functional]. -/
theorem LinearIsometryEquiv.exists_subseq_tendsto_apply [TopologicalSpace.SeparableSpace V]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] (e : X ≃ₗᵢ[𝕜] StrongDual 𝕜 V)
    {f : ℕ → X} {C : ℝ} (hf : ∀ n, ‖f n‖ ≤ C) :
    ∃ (φ : ℕ → ℕ) (g : X), StrictMono φ ∧
      ∀ x : V, Tendsto (fun k => e (f (φ k)) x) atTop (𝓝 (e g x)) := by
  have hmem : ∀ n, StrongDual.toWeakDual (e (f n)) ∈
      WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual 𝕜 V) C := fun n => by
    rw [Set.mem_preimage, StrongDual.toStrongDual_toWeakDual, Metric.mem_closedBall,
      dist_zero_right, e.norm_map]
    exact hf n
  obtain ⟨a, -, φ, hφ, hlim⟩ := WeakDual.isSeqCompact_closedBall 𝕜 V 0 C hmem
  refine ⟨φ, e.symm (WeakDual.toStrongDual a), hφ, fun x => ?_⟩
  rw [e.apply_symm_apply]
  exact tendsto_iff_forall_eval_tendsto_topDualPairing.1 hlim x

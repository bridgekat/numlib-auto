/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.FunctionalSpaces.SobolevInequality`, beside the embeddings on a
domain of `Numlib/Analysis/Sobolev/EmbeddingDomain.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Calculus.HolderSpace
import Numlib.Analysis.Sobolev.DenyLions
import Numlib.MeasureTheory.Function.ContinuousOnClosure

/-!
# The Sobolev embeddings into the Hölder spaces $C^{k,\theta}(\bar\Omega)$

This module proves the Hölder case of the Sobolev embedding theorem on a bounded open set
$\Omega \subseteq \mathbb{R}^N$ that is an extension domain, in the form of Theorems 7.3.7(c) and
7.3.8(c) of [han2009theoretical] and of Corollary 9.15 and Theorem 9.16 of [brezis2011functional].
Let $1 \le p < \infty$, with $N \ge 2$ or $p > 1$, and let $k + N/p < m$. Then the space
$W^{m,p}(\Omega)$ embeds continuously into the Hölder space $C^{k,\theta}(\bar\Omega)$ of
`Numlib.Analysis.Calculus.HolderSpace`. The exponent is the sharp $\theta = m - N/p - k$ when this
number is less than $1$, and every $\theta < 1$ when $m - N/p - k = 1$, which is the case "$N/p$ an
integer". The space $W^{m,p}(\Omega)$ also embeds compactly into $C^{k,\theta'}(\bar\Omega)$ for
every $\theta'$ with $0 < \theta' < \theta$.

Each embedding sends $u$ to its continuous representative $\tilde u$, of class $C^k$ on $\Omega$.
The lower derivatives $D^i \tilde u$, $i < k$, are moreover uniformly Hölder continuous in terms of
$\|u\|$, which is the equicontinuity that the Arzelà–Ascoli theorem needs for the compact
embeddings.

## Main results

* `SobolevEuclidean.exists_continuousLinearMap_toHolderSpace`: $W^{m,p}(\Omega) \hookrightarrow
  C^{k,\theta'}(\bar\Omega)$ for $k + N/p < m$ and every $\theta' \le \theta$, where $\theta$ is the
  exponent of Corollary 9.15 of [brezis2011functional], sharp when $m - N/p - k < 1$.
* `SobolevEuclidean.exists_continuousLinearMap_toHolderSpace_of_eq_one`: the integer case
  $m - N/p - k = 1$, $W^{m,p}(\Omega) \hookrightarrow C^{k,\theta'}(\bar\Omega)$ for every
  $\theta' < 1$.
* `SobolevEuclidean.exists_isCompactEmbedding_toHolderSpace`,
  `SobolevEuclidean.exists_isCompactEmbedding_toHolderSpace_of_eq_one`: the compact embeddings
  $W^{m,p}(\Omega) \hookrightarrow\hookrightarrow C^{k,\theta'}(\bar\Omega)$ for every $\theta'$
  with $0 < \theta' < \theta$, and with $0 < \theta' < 1$ in the integer case.
* `SobolevEuclidean.exists_continuousLinearMap_toHolderSpace_of_le`,
  `SobolevEuclidean.exists_isCompactEmbedding_toHolderSpace_of_lt`: the two cases in one statement,
  in the form of [han2009theoretical].

## Proof outline

In the non-integer case, the representatives of Corollary 9.15 of [brezis2011functional]
(`SobolevEuclidean.exists_forall_contDiffOn_closure_ae_eq_of_order`) give the derivatives of order
at most $k$ as continuous functions on $\bar\Omega$, bounded by $C \|u\|$, the top one
$\theta$-Hölder. They form an element of $C^{k,\theta'}(\bar\Omega)$, and the map is linear because
the continuous representative is unique. In the integer case, the embedding factors as
$W^{m,p}(\Omega) \to W^{k+1,q}(\Omega)$ for a large $q$, followed by Morrey's theorem
$W^{k+1,q}(\Omega) \hookrightarrow C^{k,1 - N/q}(\bar\Omega)$. The compact embeddings follow from
the Arzelà–Ascoli theorem with Hölder interpolation
(`HolderSpace.isCompactEmbedding_toLowerL_comp`).

## Implementation notes

* $W^{m,p}(\Omega)$ is `SobolevEuclidean N m p Ω`, with `p : ℝ≥0` and `[Fact (1 ≤ (p : ℝ≥0∞))]`, and
  $C^{k,\theta}(\bar\Omega)$ is `HolderSpace Ω ℝ k θ`. An element of `HolderSpace` is the tuple of
  the continuous extensions of its derivatives to $\bar\Omega$, and `HolderSpace.deriv` gives its
  entries.
* The hypothesis of [han2009theoretical] is a Lipschitz domain. The hypothesis here is
  `IsSobolevExtensionDomainAll N Ω`: $\Omega$ has a bounded $W^{1,q}$-extension operator for every
  $q$. A bounded open set of class $C^1$ has this property by Theorem 9.7 of [brezis2011functional].
* The lowering of the order $W^{m,p}(\Omega) \to W^{k+1,q}(\Omega)$ from an $L^q$ bound on
  $W^{m-k-1,p}(\Omega)$ is `SobolevEuclidean.exists_continuousLinearMap_of_forall_eLpNorm_fn_le`,
  with its inductive step `SobolevMultiIndex.exists_succ_of_partialDeriv`. These are in
  `Numlib.Analysis.Sobolev.EmbeddingDomain` and `Numlib.Analysis.Sobolev.Operators`.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace

open scoped BoundedContinuousFunction ContDiff ENNReal NNReal Topology

noncomputable section


/-! ### The $C^k(\bar\Omega)$ representative as a tuple of derivatives -/

section Rep

open SobolevMultiIndex

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]

omit [Fact (1 ≤ (p : ℝ≥0∞))] in
/-- Let $u \in W^{m,p}(\Omega)$ for an open set $\Omega \subseteq \mathbb{R}^N$. If
$f, g \colon \mathbb{R}^N \to \mathbb{R}$ are continuous and both are equal to $u$ almost
everywhere on $\Omega$, then $f = g$ on the closure $\bar\Omega$.

The proof is `ContinuousOn.eqOn_closure_of_ae_eq`. -/
theorem SobolevEuclidean.eqOn_closure_of_ae_eq {m : ℕ} {u : SobolevEuclidean N m p Ω}
    {f g : EuclideanSpace ℝ (Fin N) → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] f)
    (hgu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] g) :
    EqOn f g (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  hf.continuousOn.eqOn_closure_of_ae_eq Ω.isOpen hg.continuousOn (hfu.symm.trans hgu)

/-- Let $\Omega \subseteq \mathbb{R}^N$ be an open set that is a $W^{1,q}$-extension domain for
every $q$, let $1 \le p < \infty$ with $N \ge 2$ or $p > 1$, and let $k, m \in \mathbb{N}$ with
$k + N/p < m$. Then there are $C \ge 0$ and $\theta \in (0, 1]$, with $\theta = m - N/p - k$ if
$m - N/p - k < 1$, such that every $u \in W^{m,p}(\Omega)$ has the following representative.
There are a continuous function $\tilde u \colon \mathbb{R}^N \to \mathbb{R}$ of class $C^k$ on
$\Omega$ with $u = \tilde u$ almost everywhere on $\Omega$, and continuous functions $G_i \colon
\mathbb{R}^N \to \mathcal{L}^i(\mathbb{R}^N; \mathbb{R})$, $0 \le i \le k$, such that

* $G_i = D^i \tilde u$ on $\Omega$ for every $i$,
* $\|G_i(x)\| \le C \|u\|$ for every $i$ and every $x \in \mathbb{R}^N$,
* $\|G_k(x) - G_k(y)\| \le C \|u\| \, \|x - y\|^\theta$ for all $x, y \in \bar\Omega$.

This is Corollary 9.15 of [brezis2011functional], with footnote 16, in the form of a tuple of
derivatives. Here $\mathcal{L}^i(\mathbb{R}^N; \mathbb{R})$ is the space of continuous
$i$-linear forms, and $\|u\|$ is the norm of $W^{m,p}(\Omega)$. The functions $G_i$ are the
extensions of the derivatives of $\tilde u$ given by
`SobolevEuclidean.exists_forall_contDiffOn_closure_ae_eq_of_order`. The Hölder bound passes to
$G_k$ by continuity, because $\Omega$ is dense in its closure. -/
theorem SobolevEuclidean.exists_forall_rep_tuple (k : ℕ) {m : ℕ}
    (hΩ : IsSobolevExtensionDomainAll N Ω) (hN : 2 ≤ N ∨ 1 < p) (hm : (k : ℝ) + N / p < m) :
    ∃ C θ : ℝ, 0 ≤ C ∧ 0 < θ ∧ θ ≤ 1 ∧ ((m : ℝ) - N / p - k < 1 → θ = m - N / p - k) ∧
      ∀ u : SobolevEuclidean N m p Ω, ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, Continuous ũ ∧
        ContDiffOn ℝ k ũ Ω ∧ fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ ∧
        ∃ G : ∀ i : Fin (k + 1), EuclideanSpace ℝ (Fin N) →
            (EuclideanSpace ℝ (Fin N) [×(i : ℕ)]→L[ℝ] ℝ),
          (∀ i, Continuous (G i)) ∧
          (∀ i : Fin (k + 1), EqOn (iteratedFDeriv ℝ (i : ℕ) ũ) (G i) Ω) ∧
          (∀ i x, ‖G i x‖ ≤ C * ‖u‖) ∧
          ∀ x ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin N))),
            ∀ y ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin N))),
              ‖G (Fin.last k) x - G (Fin.last k) y‖ ≤ C * ‖u‖ * ‖x - y‖ ^ θ := by
  have h := SobolevEuclidean.exists_forall_contDiffOn_closure_ae_eq_of_order (N := N) k hΩ hN hm
  obtain ⟨C, θ, hC0, hθ0, hθ1, hθ, hC⟩ := h
  refine ⟨C, θ, hC0, hθ0, hθ1, hθ, fun u ↦ ?_⟩
  obtain ⟨ũ, hũc, hũk, hũae, hG, G, hGc, hGeq, -, hGh⟩ := hC u
  choose Gl hGlc hGleq hGlb using hG
  refine ⟨ũ, hũc, hũk, hũae, fun i ↦ Gl i (Nat.lt_succ_iff.1 i.2), fun i ↦ hGlc _ _,
    fun i ↦ hGleq _ _, fun i x ↦ hGlb _ _ x, fun x hx y hy ↦ ?_⟩
  -- the top entry agrees with the Hölder extension on `closure Ω`
  have heq₀ : EqOn (Gl (Fin.last k) (Nat.lt_succ_iff.1 (Fin.last k).2)) G
      (Ω : Set (EuclideanSpace ℝ (Fin N))) := fun z hz ↦ by
    rw [← hGleq _ _ hz, ← hGeq hz]
    rfl
  have heq : EqOn (Gl (Fin.last k) (Nat.lt_succ_iff.1 (Fin.last k).2)) G
      (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    heq₀.of_subset_closure (hGlc _ _).continuousOn hGc.continuousOn subset_closure subset_rfl
  beta_reduce
  rw [heq hx, heq hy]
  exact hGh x y

end Rep

/-! ### The embedding $W^{m,p}(\Omega) \hookrightarrow C^{k,\theta}(\bar\Omega)$ -/

section Embedding

open SobolevMultiIndex HolderSpace

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]

/-- Let $\Omega \subseteq \mathbb{R}^N$ be a bounded open set, let $1 \le p < \infty$, let
$k, m \in \mathbb{N}$, and let $C \ge 0$ and $\theta > 0$. Assume that every
$u \in W^{m,p}(\Omega)$ has a representative $\tilde u$ with derivatives $G_0, \dots, G_k$ as in
the conclusion of `SobolevEuclidean.exists_forall_rep_tuple`, with the constants $C$ and
$\theta$. Then for every $\theta' \le \theta$ there is a bounded linear map $T \colon
W^{m,p}(\Omega) \to C^{k,\theta'}(\bar\Omega)$ such that for every $u$ there is a continuous
$\tilde u \colon \mathbb{R}^N \to \mathbb{R}$ of class $C^k$ on $\Omega$ with $u = \tilde u$
almost everywhere on $\Omega$, $Tu = \tilde u$ on $\bar\Omega$, and $(Tu)_i = D^i \tilde u$ on
$\Omega$ for every $i \le k$.

Here $(Tu)_i$ is the $i$-th entry `HolderSpace.deriv (T u) i`. The map is linear because the
continuous representative is unique (`HolderSpace.ext_of_eqOn`). -/
theorem SobolevEuclidean.exists_continuousLinearMap_toHolderSpace_of_rep (k : ℕ) {m : ℕ}
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N)))) {C θ : ℝ} (hC : 0 ≤ C)
    (hθ : 0 < θ)
    (rep : ∀ u : SobolevEuclidean N m p Ω, ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, Continuous ũ ∧
      ContDiffOn ℝ k ũ Ω ∧ fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ ∧
      ∃ G : ∀ i : Fin (k + 1), EuclideanSpace ℝ (Fin N) →
          (EuclideanSpace ℝ (Fin N) [×(i : ℕ)]→L[ℝ] ℝ),
        (∀ i, Continuous (G i)) ∧
        (∀ i : Fin (k + 1), EqOn (iteratedFDeriv ℝ (i : ℕ) ũ) (G i) Ω) ∧
        (∀ i x, ‖G i x‖ ≤ C * ‖u‖) ∧
        ∀ x ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin N))),
          ∀ y ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin N))),
            ‖G (Fin.last k) x - G (Fin.last k) y‖ ≤ C * ‖u‖ * ‖x - y‖ ^ θ)
    {θ' : ℝ≥0} (hθ' : (θ' : ℝ) ≤ θ) :
    ∃ T : SobolevEuclidean N m p Ω →L[ℝ] HolderSpace Ω ℝ k θ',
      ∀ u, ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, Continuous ũ ∧ ContDiffOn ℝ k ũ Ω ∧
        fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ ∧
        (∀ x, T u x = ũ x) ∧
        ∀ (i : Fin (k + 1)) (x : EuclideanSpace ℝ (Fin N)) (hx : x ∈ Ω),
          (T u).deriv i ⟨x, subset_closure hx⟩ = iteratedFDeriv ℝ i ũ x := by
  choose ũ hũc hũk hũae G hGc hGeq hGb hGh using rep
  -- the Hölder constant at the exponent `θ'`
  obtain ⟨R, hR⟩ := Metric.isBounded_iff.1 hb.closure
  obtain ⟨θn, hθn⟩ : ∃ θn : ℝ≥0, (θn : ℝ) = θ := ⟨θ.toNNReal, Real.coe_toNNReal _ hθ.le⟩
  have hθ'n : θ' ≤ θn := NNReal.coe_le_coe.1 (hθn ▸ hθ')
  have hD : ∀ x ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin N))),
      ∀ y ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin N))), edist x y ≤ (R.toNNReal : ℝ≥0∞) :=
    fun x hx y hy ↦ by rw [edist_dist]; exact ENNReal.ofReal_le_ofReal (hR hx hy)
  have hH : ∀ u : SobolevEuclidean N m p Ω,
      HolderOnWith ((C * ‖u‖).toNNReal * R.toNNReal ^ ((θn : ℝ) - θ')) θ' (G u (Fin.last k))
        (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) := fun u ↦ by
    refine HolderOnWith.of_le hD (holderOnWith_of_dist_le fun x hx y hy ↦ ?_) hθ'n
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity), hθn]
    exact hGh u x hx y hy
  -- the element of `C^{k,θ'}(Ω̄)` attached to `u`
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : SobolevEuclidean N m p Ω → HolderSpace Ω ℝ k θ', Φ = fun u ↦
      mk' (ũ u) (hũk u) (G u) (fun i ↦ (hGc u i).continuousOn) (fun _ ↦ C * ‖u‖)
        (fun i x _ ↦ hGb u i x) (fun i x hx ↦ (hGeq u i hx).symm) (hH u) :=
    ⟨_, rfl⟩
  have hΦval : ∀ u (x : closure (Ω : Set (EuclideanSpace ℝ (Fin N)))), Φ u x = ũ u x := by
    intro u x
    rw [hΦ]
    have heq₀ : EqOn (fun z ↦ continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin N)) ℝ
        (G u 0 z)) (ũ u) (Ω : Set (EuclideanSpace ℝ (Fin N))) := fun z hz ↦ by
      change continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin N)) ℝ (G u 0 z) = ũ u z
      rw [← hGeq u 0 hz]
      exact (continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin N)) ℝ).apply_symm_apply
        (ũ u z)
    have heq : EqOn (fun z ↦ continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin N)) ℝ
        (G u 0 z)) (ũ u) (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
      heq₀.of_subset_closure ((continuousMultilinearCurryFin0 ℝ _ ℝ).continuous.comp_continuousOn
        (hGc u 0).continuousOn) (hũc u).continuousOn subset_closure subset_rfl
    exact heq x.2
  have hΦadd : ∀ u v, Φ (u + v) = Φ u + Φ v := fun u v ↦ ext_of_eqOn fun x hx ↦ by
    rw [coe_add, hΦval, hΦval, hΦval]
    have h1 : fn (u + v) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        fun z ↦ ũ u z + ũ v z :=
      (fn_add u v).trans ((hũae u).add (hũae v))
    exact SobolevEuclidean.eqOn_closure_of_ae_eq (hũc _) ((hũc u).add (hũc v)) (hũae _) h1
      (subset_closure hx)
  have hΦsmul : ∀ (c : ℝ) u, Φ (c • u) = c • Φ u := fun c u ↦ ext_of_eqOn fun x hx ↦ by
    rw [coe_smul, hΦval, hΦval]
    have h1 : fn (c • u) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        fun z ↦ c • ũ u z :=
      (fn_smul c u).trans ((hũae u).const_smul c)
    exact SobolevEuclidean.eqOn_closure_of_ae_eq (hũc _) ((hũc u).const_smul c) (hũae _) h1
      (subset_closure hx)
  have hΦn : ∀ u, ‖Φ u‖ ≤ ((k + 1) * C + C * (R.toNNReal : ℝ) ^ ((θn : ℝ) - θ')) * ‖u‖ := by
    intro u
    rw [hΦ]
    refine (norm_mk'_le _ _ _ _ _ (fun _ ↦ by positivity) _ _ _).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, NNReal.coe_mul,
      NNReal.coe_rpow, Real.coe_toNNReal _ (by positivity)]
    push_cast
    ring
  refine ⟨LinearMap.mkContinuous { toFun := Φ, map_add' := hΦadd, map_smul' := hΦsmul }
    ((k + 1) * C + C * (R.toNNReal : ℝ) ^ ((θn : ℝ) - θ')) hΦn, fun u ↦ ?_⟩
  refine ⟨ũ u, hũc u, hũk u, hũae u, fun x ↦ hΦval u x, fun i x hx ↦ ?_⟩
  change (Φ u).deriv i ⟨x, subset_closure hx⟩ = _
  rw [hΦ]
  exact (hGeq u i hx).symm

end Embedding

/-!
### The main theorems

The embedding $W^{m,p}(\Omega) \hookrightarrow C^{k,\theta}(\bar\Omega)$ and the compact embeddings
$W^{m,p}(\Omega) \hookrightarrow\hookrightarrow C^{k,\theta'}(\bar\Omega)$.
-/

section Main

open SobolevMultiIndex HolderSpace

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]

/-- Let $\Omega \subseteq \mathbb{R}^N$ be an open set that is a $W^{1,q}$-extension domain for
every $q$, let $1 \le p < \infty$ with $N \ge 2$ or $p > 1$, and let $k, m \in \mathbb{N}$ with
$k + N/p < m$. Let $T \colon W^{m,p}(\Omega) \to C^{k,\theta'}(\bar\Omega)$ be a bounded linear
map such that for every $u$ there is a continuous $\tilde u \colon \mathbb{R}^N \to \mathbb{R}$
of class $C^k$ on $\Omega$ with $u = \tilde u$ almost everywhere on $\Omega$, $Tu = \tilde u$ on
$\bar\Omega$, and $(Tu)_i = D^i \tilde u$ on $\Omega$ for every $i \le k$. Then for every
$i < k$ there are $C \ge 0$ and $\theta_i > 0$ such that for every $u$ the entry $(Tu)_i$ is
$\theta_i$-Hölder continuous with constant $C \|u\|$.

This is the equicontinuity that the Arzelà–Ascoli theorem needs for the compact embedding
$W^{m,p}(\Omega) \hookrightarrow\hookrightarrow C^{k,\theta'}(\bar\Omega)$. The proof applies
the embedding theorem at order $i$ (`SobolevEuclidean.exists_forall_rep_tuple`) and uses the
uniqueness of the continuous representative. -/
theorem SobolevEuclidean.exists_forall_holderWith_deriv (k : ℕ) {m : ℕ}
    (hΩ : IsSobolevExtensionDomainAll N Ω) (hN : 2 ≤ N ∨ 1 < p) (hm : (k : ℝ) + N / p < m)
    {θ' : ℝ≥0} {T : SobolevEuclidean N m p Ω →L[ℝ] HolderSpace Ω ℝ k θ'}
    (hT : ∀ u, ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, Continuous ũ ∧ ContDiffOn ℝ k ũ Ω ∧
      fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ ∧
      (∀ x, T u x = ũ x) ∧
      ∀ (i : Fin (k + 1)) (x : EuclideanSpace ℝ (Fin N)) (hx : x ∈ Ω),
        (T u).deriv i ⟨x, subset_closure hx⟩ = iteratedFDeriv ℝ i ũ x)
    (i : Fin (k + 1)) (hi : (i : ℕ) < k) :
    ∃ C θ : ℝ≥0, 0 < θ ∧ ∀ u, HolderWith (C * ‖u‖₊) θ ((T u).deriv i) := by
  have hm' : ((i : ℕ) : ℝ) + N / p < m := by
    have : ((i : ℕ) : ℝ) < k := by exact_mod_cast hi
    linarith
  obtain ⟨C, θ, hC0, hθ0, -, -, rep⟩ := SobolevEuclidean.exists_forall_rep_tuple i hΩ hN hm'
  refine ⟨C.toNNReal, θ.toNNReal, by simpa using hθ0, fun u ↦ ?_⟩
  obtain ⟨ũ, hũc, -, hũae, -, hTd⟩ := hT u
  obtain ⟨ũᵢ, hũᵢc, -, hũᵢae, Gᵢ, hGᵢc, hGᵢeq, -, hGᵢh⟩ := rep u
  -- the `i`-th entry of `T u` is the Hölder extension of `D^i ũᵢ`
  have hfun : ⇑((T u).deriv i) = fun x : closure (Ω : Set (EuclideanSpace ℝ (Fin N))) ↦
      Gᵢ (Fin.last i) x := by
    refine eq_of_forall_eq_of_continuous ((T u).deriv i).continuous
      ((hGᵢc _).comp continuous_subtype_val) fun x hx ↦ ?_
    rw [hTd i x hx]
    have hev : ũ =ᶠ[𝓝 x] ũᵢ := by
      filter_upwards [Ω.isOpen.mem_nhds hx] with z hz
      exact SobolevEuclidean.eqOn_closure_of_ae_eq hũc hũᵢc hũae hũᵢae (subset_closure hz)
    change iteratedFDeriv ℝ i ũ x = Gᵢ (Fin.last i) x
    rw [(hev.iteratedFDeriv (𝕜 := ℝ) i).eq_of_nhds]
    exact hGᵢeq (Fin.last i) hx
  refine holderWith_of_dist_le fun x y ↦ ?_
  rw [hfun, dist_eq_norm, Subtype.dist_eq, dist_eq_norm, NNReal.coe_mul,
    Real.coe_toNNReal _ hC0, coe_nnnorm, Real.coe_toNNReal _ hθ0.le]
  exact hGᵢh x x.2 y y.2

/-- The **Sobolev embedding** $W^{m,p}(\Omega) \hookrightarrow C^{k,\theta'}(\bar\Omega)$. Let
$\Omega \subseteq \mathbb{R}^N$ be a bounded open set that is a $W^{1,q}$-extension domain for
every $q$, let $1 \le p < \infty$ with $N \ge 2$ or $p > 1$, and let $k, m \in \mathbb{N}$ with
$k + N/p < m$. Then there is a Hölder exponent $\theta \in (0, 1]$, with $\theta = m - N/p - k$
if $m - N/p - k < 1$, such that for every $\theta' \le \theta$ there is a bounded linear map $T
\colon W^{m,p}(\Omega) \to C^{k,\theta'}(\bar\Omega)$ with the following two properties.

* For every $u$ there is a continuous $\tilde u \colon \mathbb{R}^N \to \mathbb{R}$ with
  $u = \tilde u$ almost everywhere on $\Omega$ and $Tu = \tilde u$ on $\bar\Omega$.
* For every $i < k$ there are $C \ge 0$ and $\theta_i > 0$ such that for every $u$ the entry
  $(Tu)_i$ is $\theta_i$-Hölder continuous with constant $C \|u\|$.

This is Corollary 9.15 of [brezis2011functional] and the non-integer case of Theorem 7.3.7(c) of
[han2009theoretical], with the Lipschitz domain of the second source replaced by an extension
domain. The second property is the hypothesis of `HolderSpace.isCompactEmbedding_toLowerL_comp`. -/
theorem SobolevEuclidean.exists_continuousLinearMap_toHolderSpace (k : ℕ) {m : ℕ}
    (hΩ : IsSobolevExtensionDomainAll N Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N)))) (hN : 2 ≤ N ∨ 1 < p)
    (hm : (k : ℝ) + N / p < m) :
    ∃ θ : ℝ≥0, 0 < θ ∧ θ ≤ 1 ∧ ((m : ℝ) - N / p - k < 1 → (θ : ℝ) = m - N / p - k) ∧
      ∀ θ' : ℝ≥0, θ' ≤ θ → ∃ T : SobolevEuclidean N m p Ω →L[ℝ] HolderSpace Ω ℝ k θ',
        (∀ u, ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, Continuous ũ ∧
          fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ ∧ ∀ x, T u x = ũ x) ∧
        ∀ i : Fin (k + 1), (i : ℕ) < k →
          ∃ C θᵢ : ℝ≥0, 0 < θᵢ ∧ ∀ u, HolderWith (C * ‖u‖₊) θᵢ ((T u).deriv i) := by
  obtain ⟨C, θ, hC0, hθ0, hθ1, hθ, rep⟩ := SobolevEuclidean.exists_forall_rep_tuple k hΩ hN hm
  refine ⟨θ.toNNReal, by simpa using hθ0, by simpa using hθ1, fun h ↦ ?_, fun θ' hθ' ↦ ?_⟩
  · rw [Real.coe_toNNReal _ hθ0.le]
    exact hθ h
  obtain ⟨T, hT⟩ := SobolevEuclidean.exists_continuousLinearMap_toHolderSpace_of_rep k hb hC0 hθ0
    rep (θ' := θ') (by rw [← Real.coe_toNNReal _ hθ0.le]; exact_mod_cast hθ')
  refine ⟨T, fun u ↦ ?_, fun i hi ↦
    SobolevEuclidean.exists_forall_holderWith_deriv k hΩ hN hm hT i hi⟩
  obtain ⟨ũ, hc, -, hae, hv, -⟩ := hT u
  exact ⟨ũ, hc, hae, hv⟩

/-- Let $\Omega \subseteq \mathbb{R}^N$ be open and let $T \colon W^{m,p}(\Omega) \to
C^{k,\theta'}(\bar\Omega)$ be a bounded linear map such that for every $u$ there is a continuous
$\tilde u \colon \mathbb{R}^N \to \mathbb{R}$ with $u = \tilde u$ almost everywhere on $\Omega$
and $Tu = \tilde u$ on $\bar\Omega$. Then $T$ is injective. -/
theorem SobolevEuclidean.injective_of_forall_exists_ae_eq {m : ℕ} {k : ℕ} {θ' : ℝ≥0}
    (T : SobolevEuclidean N m p Ω →L[ℝ] HolderSpace Ω ℝ k θ')
    (hT : ∀ u, ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, Continuous ũ ∧
      fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ ∧ ∀ x, T u x = ũ x) :
    Function.Injective T := fun u v huv ↦ by
  obtain ⟨ũ, -, hu, hu'⟩ := hT u
  obtain ⟨vt, -, hv, hv'⟩ := hT v
  refine ext_of_fn_ae_eq (hu.trans (Filter.EventuallyEq.trans ?_ hv.symm))
  refine ae_restrict_of_forall_mem Ω.isOpen.measurableSet fun x hx ↦ ?_
  rw [← hu' ⟨x, subset_closure hx⟩, ← hv' ⟨x, subset_closure hx⟩, huv]

/-- Let $\Omega \subseteq \mathbb{R}^N$ be open and let $T \colon W^{m,p}(\Omega) \to
C^{k,\theta'}(\bar\Omega)$ be a bounded linear map such that for every $u$ there is a continuous
$\tilde u \colon \mathbb{R}^N \to \mathbb{R}$ with $u = \tilde u$ almost everywhere on $\Omega$
and $Tu = \tilde u$ on $\bar\Omega$. Then $T$ is a continuous embedding, that is, an injective
bounded linear map (`IsContinuousEmbedding`). -/
theorem SobolevEuclidean.isContinuousEmbedding_of_forall_exists_ae_eq {m : ℕ} {k : ℕ} {θ' : ℝ≥0}
    (T : SobolevEuclidean N m p Ω →L[ℝ] HolderSpace Ω ℝ k θ')
    (hT : ∀ u, ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, Continuous ũ ∧
      fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ ∧ ∀ x, T u x = ũ x) :
    IsContinuousEmbedding T.toLinearMap :=
  ⟨SobolevEuclidean.injective_of_forall_exists_ae_eq T hT, _, T.le_opNorm⟩

/-- The **compact Sobolev embedding** $W^{m,p}(\Omega) \hookrightarrow\hookrightarrow
C^{k,\theta'}(\bar\Omega)$. Let $\Omega \subseteq \mathbb{R}^N$ be a bounded open set that is a
$W^{1,q}$-extension domain for every $q$, let $1 \le p < \infty$ with $N \ge 2$ or $p > 1$, and
let $k, m \in \mathbb{N}$ with $k + N/p < m$. Then there is a Hölder exponent
$\theta \in (0, 1]$, with $\theta = m - N/p - k$ if $m - N/p - k < 1$, such that for every
$\theta'$ with $0 < \theta' < \theta$ there is a compact embedding $T \colon W^{m,p}(\Omega) \to
C^{k,\theta'}(\bar\Omega)$ such that for every $u$ there is a continuous
$\tilde u \colon \mathbb{R}^N \to \mathbb{R}$ with $u = \tilde u$ almost everywhere on $\Omega$
and $Tu = \tilde u$ on $\bar\Omega$.

This is Theorem 9.16 of [brezis2011functional] at higher order, and Theorem 7.3.8(c) of
[han2009theoretical]. The exponent $\theta$ is the one of
`SobolevEuclidean.exists_continuousLinearMap_toHolderSpace`. The proof is the Arzelà–Ascoli
theorem with Hölder interpolation (`HolderSpace.isCompactEmbedding_toLowerL_comp`). A compact
embedding is `IsCompactEmbedding`. -/
theorem SobolevEuclidean.exists_isCompactEmbedding_toHolderSpace (k : ℕ) {m : ℕ}
    (hΩ : IsSobolevExtensionDomainAll N Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N)))) (hN : 2 ≤ N ∨ 1 < p)
    (hm : (k : ℝ) + N / p < m) :
    ∃ θ : ℝ≥0, 0 < θ ∧ θ ≤ 1 ∧ ((m : ℝ) - N / p - k < 1 → (θ : ℝ) = m - N / p - k) ∧
      ∀ θ' : ℝ≥0, 0 < θ' → θ' < θ → ∃ T : SobolevEuclidean N m p Ω →L[ℝ] HolderSpace Ω ℝ k θ',
        (∀ u, ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, Continuous ũ ∧
          fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ ∧ ∀ x, T u x = ũ x) ∧
        IsCompactEmbedding T.toLinearMap := by
  obtain ⟨θ, hθ0, hθ1, hθ, hT⟩ :=
    SobolevEuclidean.exists_continuousLinearMap_toHolderSpace k hΩ hb hN hm
  refine ⟨θ, hθ0, hθ1, hθ, fun θ' hθ'0 hθ' ↦ ?_⟩
  obtain ⟨T₀, hT₀, hlow⟩ := hT θ le_rfl
  refine ⟨(toLowerL Ω ℝ k hb hθ'.le).comp T₀, fun u ↦ ?_,
    isCompactEmbedding_toLowerL_comp hb hθ'0 hθ' T₀
      (SobolevEuclidean.injective_of_forall_exists_ae_eq T₀ hT₀) hlow⟩
  obtain ⟨ũ, hc, hae, hv⟩ := hT₀ u
  exact ⟨ũ, hc, hae, fun x ↦ hv x⟩

end Main

/-! ### The integer case $m - N/p - k = 1$: every exponent $\theta' < 1$ -/

section Integer

open SobolevMultiIndex HolderSpace

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]

/-- Let $N \in \mathbb{N}$, $p \ge 0$ and $0 \le \theta' < 1$. Then there is $q \ge p$ with $q > N$
and $N/q \le 1 - \theta'$, for example $q = \max(p, N/(1 - \theta') + 1)$.

This is the auxiliary exponent of the integer case. -/
theorem NNReal.exists_integer_case_exponent (N : ℕ) (p : ℝ≥0) {θ' : ℝ≥0} (hθ' : θ' < 1) :
    ∃ q : ℝ≥0, p ≤ q ∧ (N : ℝ) < q ∧ (N : ℝ) / q ≤ 1 - θ' := by
  have hθ'r : (θ' : ℝ) < 1 := by exact_mod_cast hθ'
  have h1 : (0 : ℝ) < 1 - θ' := sub_pos.2 hθ'r
  obtain ⟨q, hq⟩ : ∃ q : ℝ≥0, q = max p ((N : ℝ≥0) / (1 - θ') + 1) := ⟨_, rfl⟩
  have hqr : (N : ℝ) / (1 - θ') + 1 ≤ q := by
    have := NNReal.coe_le_coe.2 (hq ▸ le_max_right p ((N : ℝ≥0) / (1 - θ') + 1))
    rwa [NNReal.coe_add, NNReal.coe_div, NNReal.coe_sub hθ'.le, NNReal.coe_one,
      NNReal.coe_natCast] at this
  have hNdiv : (N : ℝ) ≤ N / (1 - θ') := by
    rw [le_div_iff₀ h1]
    nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N), θ'.coe_nonneg]
  have hNq : (N : ℝ) < q := by linarith
  refine ⟨q, hq ▸ le_max_left _ _, hNq, ?_⟩
  have hq0 : (0 : ℝ) < q := lt_of_le_of_lt (Nat.cast_nonneg N) hNq
  rw [div_le_iff₀ hq0]
  have h2 : (N : ℝ) / (1 - θ') ≤ q := by linarith
  rw [div_le_iff₀ h1] at h2
  linarith

/-- The **Sobolev embedding** $W^{m,p}(\Omega) \hookrightarrow C^{k,\theta'}(\bar\Omega)$ in the
integer case $m - N/p - k = 1$. Let $\Omega \subseteq \mathbb{R}^N$, $N \ge 1$, be a bounded
open set that is a $W^{1,q}$-extension domain for every $q$, let $1 \le p < \infty$ with
$N \ge 2$ or $p > 1$, and let $k, m \in \mathbb{N}$ with $m - N/p - k = 1$. Then for every
$\theta' < 1$ there is a bounded linear map $T \colon W^{m,p}(\Omega) \to
C^{k,\theta'}(\bar\Omega)$ with the following two properties.

* For every $u$ there is a continuous $\tilde u \colon \mathbb{R}^N \to \mathbb{R}$ with
  $u = \tilde u$ almost everywhere on $\Omega$ and $Tu = \tilde u$ on $\bar\Omega$.
* For every $i < k$ there are $C \ge 0$ and $\theta_i > 0$ such that for every $u$ the entry
  $(Tu)_i$ is $\theta_i$-Hölder continuous with constant $C \|u\|$.

This is Theorem 7.3.7(c) of [han2009theoretical] in the case "$N/p$ an integer". The map is the
composition of $W^{m,p}(\Omega) \to W^{k+1,q}(\Omega)$ for a large $q$, from the critical
embedding $W^{m-k-1,p}(\Omega) \subset L^q(\Omega)$ at every order
(`SobolevEuclidean.exists_continuousLinearMap_of_forall_eLpNorm_fn_le`), with Morrey's theorem
$W^{k+1,q}(\Omega) \hookrightarrow C^{k,1 - N/q}(\bar\Omega)$, where $1 - N/q \ge \theta'$
(`NNReal.exists_integer_case_exponent`). -/
theorem SobolevEuclidean.exists_continuousLinearMap_toHolderSpace_of_eq_one (k : ℕ) {m : ℕ}
    (hΩ : IsSobolevExtensionDomainAll N Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N)))) (hN0 : 0 < N)
    (hN : 2 ≤ N ∨ 1 < p) (hm : (m : ℝ) - N / p - k = 1) {θ' : ℝ≥0} (hθ' : θ' < 1) :
    ∃ T : SobolevEuclidean N m p Ω →L[ℝ] HolderSpace Ω ℝ k θ',
      (∀ u, ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, Continuous ũ ∧
        fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ ∧ ∀ x, T u x = ũ x) ∧
      ∀ i : Fin (k + 1), (i : ℕ) < k →
        ∃ C θᵢ : ℝ≥0, 0 < θᵢ ∧ ∀ u, HolderWith (C * ‖u‖₊) θᵢ ((T u).deriv i) := by
  have hp1 : (1 : ℝ≥0) ≤ p := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p)
  -- `m = ℓ + k + 1` with `ℓ = N/p`
  obtain ⟨ℓ, rfl⟩ : ∃ ℓ, m = ℓ + k + 1 := by
    refine ⟨m - k - 1, ?_⟩
    have h0 : (0 : ℝ) ≤ N / p := by positivity
    have : k + 1 ≤ m := by
      have : ((k : ℝ) + 1) ≤ m := by linarith
      exact_mod_cast this
    omega
  have hℓ : (ℓ : ℝ) = N / p := by
    push_cast at hm
    linarith
  -- the auxiliary exponent
  obtain ⟨q, hpq, hNq, hq⟩ := NNReal.exists_integer_case_exponent N p hθ'
  have : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨by exact_mod_cast hp1.trans hpq⟩
  have hNq' : 2 ≤ N ∨ 1 < q := hN.imp id fun h ↦ h.trans_le hpq
  have hN0' : (N : ℝ) ≠ 0 := by exact_mod_cast hN0.ne'
  have hq' : (p : ℝ)⁻¹ - ℓ / N ≤ (q : ℝ)⁻¹ := by
    rw [hℓ, div_div, mul_comm, ← div_div, div_self hN0', one_div, sub_self]
    positivity
  -- the order-lowering map and Morrey's map
  obtain ⟨K, hK, hKu⟩ :=
    SobolevEuclidean.exists_forall_eLpNorm_fn_le_of_order_of_hasSobolevExtension ℓ hΩ hN hpq hq'
  obtain ⟨T₁, hT₁⟩ :=
    SobolevEuclidean.exists_continuousLinearMap_of_forall_eLpNorm_fn_le (N := N) (Ω := Ω) k hK hKu
  have hm' : (k : ℝ) + N / q < ((k + 1 : ℕ) : ℝ) := by
    push_cast
    have : (N : ℝ) / q < 1 := (div_lt_one (lt_of_le_of_lt (Nat.cast_nonneg N) hNq)).2 hNq
    linarith
  obtain ⟨θ, -, -, hθ, hT⟩ :=
    SobolevEuclidean.exists_continuousLinearMap_toHolderSpace (p := q) k hΩ hb hNq' hm'
  have hNq0 : (0 : ℝ) < N / q :=
    div_pos (by exact_mod_cast hN0) (lt_of_le_of_lt (Nat.cast_nonneg N) hNq)
  have hθq : (θ : ℝ) = 1 - N / q := by
    rw [hθ (by push_cast; linarith)]
    push_cast
    ring
  obtain ⟨T₂, hT₂, hlow⟩ := hT θ' (by
    rw [← NNReal.coe_le_coe, hθq]
    linarith)
  refine ⟨T₂.comp T₁, fun u ↦ ?_, fun i hi ↦ ?_⟩
  · obtain ⟨ũ, hc, hae, hv⟩ := hT₂ (T₁ u)
    exact ⟨ũ, hc, (hT₁ u).symm.trans hae, hv⟩
  · obtain ⟨C, θᵢ, hθᵢ, hC⟩ := hlow i hi
    refine ⟨C * ‖T₁‖₊, θᵢ, hθᵢ, fun u ↦ (hC (T₁ u)).mono ?_⟩
    rw [mul_assoc]
    gcongr
    exact T₁.le_opNNNorm u

/-- The **compact Sobolev embedding** $W^{m,p}(\Omega) \hookrightarrow\hookrightarrow
C^{k,\theta'}(\bar\Omega)$ in the integer case $m - N/p - k = 1$. Let
$\Omega \subseteq \mathbb{R}^N$, $N \ge 1$, be a bounded open set that is a $W^{1,q}$-extension
domain for every $q$, let $1 \le p < \infty$ with $N \ge 2$ or $p > 1$, and let
$k, m \in \mathbb{N}$ with $m - N/p - k = 1$. Then for every $\theta'$ with $0 < \theta' < 1$
there is a compact embedding $T \colon W^{m,p}(\Omega) \to C^{k,\theta'}(\bar\Omega)$ such that
for every $u$ there is a continuous $\tilde u \colon \mathbb{R}^N \to \mathbb{R}$ with
$u = \tilde u$ almost everywhere on $\Omega$ and $Tu = \tilde u$ on $\bar\Omega$.

This is Theorem 7.3.8(c) of [han2009theoretical] in the case "$N/p$ an integer". The proof goes
through $C^{k,\theta''}(\bar\Omega)$ for some $\theta'' \in (\theta', 1)$ and the Arzelà–Ascoli
theorem. -/
theorem SobolevEuclidean.exists_isCompactEmbedding_toHolderSpace_of_eq_one (k : ℕ) {m : ℕ}
    (hΩ : IsSobolevExtensionDomainAll N Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N)))) (hN0 : 0 < N)
    (hN : 2 ≤ N ∨ 1 < p) (hm : (m : ℝ) - N / p - k = 1) {θ' : ℝ≥0} (hθ'0 : 0 < θ')
    (hθ' : θ' < 1) :
    ∃ T : SobolevEuclidean N m p Ω →L[ℝ] HolderSpace Ω ℝ k θ',
      (∀ u, ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, Continuous ũ ∧
        fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ ∧ ∀ x, T u x = ũ x) ∧
      IsCompactEmbedding T.toLinearMap := by
  have hθ'r : (θ' : ℝ) < 1 := by exact_mod_cast hθ'
  obtain ⟨θ'', hθ''₁, hθ''₂⟩ : ∃ θ'' : ℝ≥0, θ' < θ'' ∧ θ'' < 1 :=
    ⟨(θ' + 1) / 2, by
      rw [← NNReal.coe_lt_coe, NNReal.coe_div, NNReal.coe_add, NNReal.coe_one, NNReal.coe_ofNat]
      linarith, by
      rw [← NNReal.coe_lt_coe, NNReal.coe_div, NNReal.coe_add, NNReal.coe_one, NNReal.coe_ofNat]
      linarith⟩
  obtain ⟨T₀, hT₀, hlow⟩ :=
    SobolevEuclidean.exists_continuousLinearMap_toHolderSpace_of_eq_one k hΩ hb hN0 hN hm hθ''₂
  refine ⟨(toLowerL Ω ℝ k hb hθ''₁.le).comp T₀, fun u ↦ ?_,
    isCompactEmbedding_toLowerL_comp hb hθ'0 hθ''₁ T₀
      (SobolevEuclidean.injective_of_forall_exists_ae_eq T₀ hT₀) hlow⟩
  obtain ⟨ũ, hc, hae, hv⟩ := hT₀ u
  exact ⟨ũ, hc, hae, fun x ↦ hv x⟩

end Integer

/-! ### The two cases in one statement -/

section Combined

open SobolevMultiIndex HolderSpace

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]

/-- The **compact Sobolev embedding** for $0 < \theta' < m - N/p - k \le 1$. Let
$\Omega \subseteq \mathbb{R}^N$, $N \ge 1$, be a bounded open set that is a $W^{1,q}$-extension
domain for every $q$, let $1 \le p < \infty$ with $N \ge 2$ or $p > 1$, and let
$k, m \in \mathbb{N}$ with $k + N/p < m$ and $m - N/p - k \le 1$. Then for every $\theta'$ with
$0 < \theta' < m - N/p - k$ there is a compact embedding $T \colon W^{m,p}(\Omega) \to
C^{k,\theta'}(\bar\Omega)$ such that for every $u$ there is a continuous
$\tilde u \colon \mathbb{R}^N \to \mathbb{R}$ with $u = \tilde u$ almost everywhere on $\Omega$
and $Tu = \tilde u$ on $\bar\Omega$.

This states the non-integer and the integer case of Theorem 7.3.8(c) of [han2009theoretical]
together. With $k = m - [N/p] - 1$, the bound $m - N/p - k = [N/p] + 1 - N/p$ is the one of the
source, and it equals $1$ exactly when $N/p$ is an integer. -/
theorem SobolevEuclidean.exists_isCompactEmbedding_toHolderSpace_of_lt (k : ℕ) {m : ℕ}
    (hΩ : IsSobolevExtensionDomainAll N Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N)))) (hN0 : 0 < N)
    (hN : 2 ≤ N ∨ 1 < p) (hm : (k : ℝ) + N / p < m) (hle : (m : ℝ) - N / p - k ≤ 1) {θ' : ℝ≥0}
    (hθ'0 : 0 < θ') (hθ' : (θ' : ℝ) < m - N / p - k) :
    ∃ T : SobolevEuclidean N m p Ω →L[ℝ] HolderSpace Ω ℝ k θ',
      (∀ u, ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, Continuous ũ ∧
        fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ ∧ ∀ x, T u x = ũ x) ∧
      IsCompactEmbedding T.toLinearMap := by
  rcases hle.lt_or_eq with hlt | heq
  · obtain ⟨θ, -, -, hθeq, hT⟩ :=
      SobolevEuclidean.exists_isCompactEmbedding_toHolderSpace k hΩ hb hN hm
    exact hT θ' hθ'0 (by rw [← NNReal.coe_lt_coe, hθeq hlt]; exact hθ')
  · exact SobolevEuclidean.exists_isCompactEmbedding_toHolderSpace_of_eq_one k hΩ hb hN0 hN heq
      hθ'0 (by rw [← NNReal.coe_lt_coe, NNReal.coe_one, ← heq]; exact hθ')

/-- The **Sobolev embedding** for $\theta' \le m - N/p - k \le 1$ and $\theta' < 1$. Let
$\Omega \subseteq \mathbb{R}^N$, $N \ge 1$, be a bounded open set that is a $W^{1,q}$-extension
domain for every $q$, let $1 \le p < \infty$ with $N \ge 2$ or $p > 1$, and let
$k, m \in \mathbb{N}$ with $k + N/p < m$ and $m - N/p - k \le 1$. Then for every $\theta' \ge 0$
with $\theta' \le m - N/p - k$ and $\theta' < 1$ there is a continuous embedding $T \colon
W^{m,p}(\Omega) \to C^{k,\theta'}(\bar\Omega)$ such that for every $u$ there is a continuous
$\tilde u \colon \mathbb{R}^N \to \mathbb{R}$ with $u = \tilde u$ almost everywhere on $\Omega$
and $Tu = \tilde u$ on $\bar\Omega$.

This states the non-integer and the integer case of Theorem 7.3.7(c) of [han2009theoretical]
together. -/
theorem SobolevEuclidean.exists_continuousLinearMap_toHolderSpace_of_le (k : ℕ) {m : ℕ}
    (hΩ : IsSobolevExtensionDomainAll N Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N)))) (hN0 : 0 < N)
    (hN : 2 ≤ N ∨ 1 < p) (hm : (k : ℝ) + N / p < m) (hle : (m : ℝ) - N / p - k ≤ 1) {θ' : ℝ≥0}
    (hθ' : (θ' : ℝ) ≤ m - N / p - k) (hθ'1 : θ' < 1) :
    ∃ T : SobolevEuclidean N m p Ω →L[ℝ] HolderSpace Ω ℝ k θ',
      (∀ u, ∃ ũ : EuclideanSpace ℝ (Fin N) → ℝ, Continuous ũ ∧
        fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ ∧ ∀ x, T u x = ũ x) ∧
      IsContinuousEmbedding T.toLinearMap := by
  rcases hle.lt_or_eq with hlt | heq
  · obtain ⟨θ, -, -, hθeq, hT⟩ :=
      SobolevEuclidean.exists_continuousLinearMap_toHolderSpace k hΩ hb hN hm
    obtain ⟨T, hT, -⟩ := hT θ' (by rw [← NNReal.coe_le_coe, hθeq hlt]; exact hθ')
    exact ⟨T, hT, SobolevEuclidean.isContinuousEmbedding_of_forall_exists_ae_eq T hT⟩
  · obtain ⟨T, hT, -⟩ := SobolevEuclidean.exists_continuousLinearMap_toHolderSpace_of_eq_one k hΩ
      hb hN0 hN heq hθ'1
    exact ⟨T, hT, SobolevEuclidean.isContinuousEmbedding_of_forall_exists_ae_eq T hT⟩

end Combined

/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Calculus.ContDiffOnClosure
import Numlib.Analysis.Calculus.ProdContDiff
import Numlib.Analysis.Calculus.SpaceTime
import Numlib.Analysis.PDE.Bochner
import Numlib.MeasureTheory.Function.ContinuousOnClosure
import Numlib.Analysis.Sobolev.EmbeddingDomain

/-!
# The space–time reading of a curve of Sobolev functions

Let $\Omega \subseteq \mathbb{R}^N$ be open, and let $t \mapsto u(t)$ be a curve with values in
$L^2(\Omega)$ that is, on a set of times $s$, of class $C^k(s; H^m(\Omega))$ in the sense of
`Bochner.ContDiffOnThrough`: it factors through the inclusion $H^m(\Omega) \to L^2(\Omega)$ by a
$C^k$ curve in $H^m(\Omega)$. This file reads such a curve as a function $U(x, t)$ of space and
time, through the continuous representatives that the Sobolev embedding theorems on a domain give
(Corollaries 9.14–9.15 of [brezis2011functional], in `Numlib.Analysis.Sobolev.EmbeddingDomain`).
This is the sense in which Theorem 10.1 (5), Theorem 10.2 (c), Corollary 10.5 and Theorem 10.8 of
[brezis2011functional] state the regularity of the solutions of the heat and wave equations in space
and time.

Let $\Omega$ be an extension domain for every exponent, for example an open set of class $C^1$ with
bounded boundary, or the half space. If $m > N/2$ and $u \in C(s; H^m(\Omega))$, there is a
representative $U$ that is continuous on $\bar\Omega \times s$ with $U(\cdot, t) = u(t)$ almost
everywhere on $\Omega$ for each $t \in s$. If $k + N/2 < m$ and $u \in C^k(s; H^m(\Omega))$, the
representative is $C^k$ on $\Omega \times s$, and its derivatives extend continuously to
$\bar\Omega \times s$. If $u \in C^\infty(s; H^m(\Omega))$ for every $m$, the representative is of
class $C^\infty(\bar\Omega \times \bar s')$ for every open $s'$ with $\bar s' \subseteq s$.

## Main results

* `Bochner.continuousOn_prod_of_forall_norm_sub_le`: if $\operatorname{rep}(w)$ is continuous on $K$
  for every $w$ and $\|\operatorname{rep}(w_1)(x) - \operatorname{rep}(w_2)(x)\| \le C \|w_1 -
  w_2\|$ on $K$, then $(x, t) \mapsto \operatorname{rep}(v(t))(x)$ is continuous on $K \times s$ for
  every $v$ continuous on $s$.
* `Bochner.continuousOn_spaceTime_of_contDiffOnThrough`: for $m > N/2$, a curve
  $u \in C(s; H^m(\Omega))$ has a space–time representative continuous on $\bar\Omega \times s$.
  Corollary 10.5 of [brezis2011functional] ($u \in C(\bar Q)$) needs this.
* `Bochner.exists_contDiffOnExtendsTo_spaceTime_of_contDiffOnThrough`: for $k + N/2 < m$, a curve
  $u \in C^k(s; H^m(\Omega))$ has a space–time representative of class $C^k$ on $\Omega \times s$
  whose derivatives extend continuously to $\bar\Omega \times s$.
* `Bochner.contDiffOnClosure_spaceTime_of_forall_contDiffOnThrough`: a curve
  $u \in C^\infty(s; H^m(\Omega))$ for every $m$ has a space–time representative of class
  $C^\infty(\bar\Omega \times \bar s')$ for every open $s'$ with $\bar s' \subseteq s$. This gives
  Theorem 10.1 (5) ($u \in C^\infty(\bar\Omega \times [\varepsilon, \infty))$ for every
  $\varepsilon > 0$), Theorem 10.2 (c) and Theorem 10.8
  ($u \in C^\infty(\bar\Omega \times [0, \infty))$) of [brezis2011functional].
* `Bochner.contDiffOnClosure_spaceTime_of_forall_contDiffOnThrough_Ioi`,
  `Bochner.contDiffOnClosure_spaceTime_of_forall_contDiffOnThrough_Ici`,
  `Bochner.contDiffOnExtendsTo_spaceTime_of_forall_contDiffOnThrough`: the variants on
  $(a, \infty)$, on $[a, \infty)$, and with derivatives within $\Omega \times s$.

## Proof outline

The partial derivatives $\partial_t^j D_x^i U(x, t)$ are $D^i(\operatorname{rep}(u^{(j)}(t)))(x)$,
the continuous extensions of the derivatives of the canonical $C^k(\bar\Omega)$ representatives of
Corollary 9.15. By the uniqueness of continuous representatives, these are linear in $u$ on
$\bar\Omega$ (`Bochner.eqOn_closure_deriv_rep_add`, `Bochner.eqOn_closure_deriv_rep_smul`). So the
evaluation at a point commutes with $d/dt$ (`Bochner.hasDerivWithinAt_of_forall_add_smul_norm_le`),
and the product-calculus theorem `contDiffOnExtendsTo_prod_of_partials` assembles the joint
derivatives.

## Implementation notes

* An extension domain for every exponent is `IsSobolevExtensionDomainAll N Ω`. The space
  $H^m(\Omega)$ is the Sobolev space `SobolevMultiIndex` for the standard basis of $\mathbb{R}^N$,
  with $p = 2$, and the inclusion $H^m(\Omega) \to L^2(\Omega)$ is `SobolevMultiIndex.fnL`.
* The class $C^k$ with derivatives extending to a larger set is `ContDiffOnExtendsTo` of
  `Numlib.Analysis.Calculus.ProdContDiff`. The class $C^\infty(\bar\Omega \times \bar s')$ is
  `ContDiffOnClosure` on $\Omega \times s'$, which is the class of Chapter 9, footnote 16 of
  [brezis2011functional].
* The extension stops at $\bar s' \subseteq s$, because the curve need not be continuous into
  $H^m(\Omega)$ at the boundary of $s$.
-/

open Filter MeasureTheory Set Topology TopologicalSpace
open scoped ContDiff ENNReal NNReal

namespace Bochner

/-! ### Joint continuity of $(x, t) \mapsto \operatorname{rep}(v(t))(x)$ -/

/-- **Joint continuity from a uniformly Lipschitz family of continuous functions.** Let $X$ be a
pseudometric space, $V$ and $F$ normed groups, $K \subseteq X$ and $C \in \mathbb{R}$. Let
$\operatorname{rep} : V \to (X \to F)$ be such that every $\operatorname{rep}(w)$ is continuous
on $K$, and
$$\|\operatorname{rep}(w_1)(x) - \operatorname{rep}(w_2)(x)\| \le C \|w_1 - w_2\|, \qquad w_1,
  w_2 \in V, \ x \in K.$$
Then for every $v : \mathbb{R} \to V$ continuous on $s \subseteq \mathbb{R}$, the function
$(x, t) \mapsto \operatorname{rep}(v(t))(x)$ is continuous on $K \times s$.

The difference of the values at $(x, t)$ and $(x_0, t_0)$ is at most $C \|v(t) - v(t_0)\| +
\|\operatorname{rep}(v(t_0))(x) - \operatorname{rep}(v(t_0))(x_0)\|$. -/
theorem continuousOn_prod_of_forall_norm_sub_le {X V F : Type*} [PseudoMetricSpace X]
    [NormedAddCommGroup V] [NormedAddCommGroup F] {rep : V → X → F} {K : Set X} {C : ℝ}
    (hcont : ∀ w, ContinuousOn (rep w) K)
    (hsub : ∀ w₁ w₂, ∀ x ∈ K, ‖rep w₁ x - rep w₂ x‖ ≤ C * ‖w₁ - w₂‖)
    {v : ℝ → V} {s : Set ℝ} (hv : ContinuousOn v s) :
    ContinuousOn (fun q : X × ℝ ↦ rep (v q.2) q.1) (K ×ˢ s) := by
  intro q hq
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.continuousWithinAt_iff.1 (hv q.2 hq.2) (ε / (2 * (|C| + 1)))
    (by positivity)
  obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.continuousWithinAt_iff.1 (hcont (v q.2) q.1 hq.1) (ε / 2)
    (by positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun {p} hp hpq ↦ ?_⟩
  have hp1 : dist p.1 q.1 < δ₂ :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (Prod.dist_eq (x := p) (y := q)).ge)
      (hpq.trans_le (min_le_right _ _))
  have hp2 : dist p.2 q.2 < δ₁ :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (Prod.dist_eq (x := p) (y := q)).ge)
      (hpq.trans_le (min_le_left _ _))
  have hA : dist (rep (v p.2) p.1) (rep (v q.2) p.1) ≤ ε / 2 := by
    rw [dist_eq_norm]
    refine (hsub _ _ p.1 hp.1).trans ?_
    have h3 := h₁ hp.2 hp2
    rw [dist_eq_norm] at h3
    calc C * ‖v p.2 - v q.2‖ ≤ |C| * ‖v p.2 - v q.2‖ :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _)
      _ ≤ |C| * (ε / (2 * (|C| + 1))) := mul_le_mul_of_nonneg_left h3.le (abs_nonneg C)
      _ ≤ ε / 2 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_nonneg (abs_nonneg C) hε.le]
  calc dist (rep (v p.2) p.1) (rep (v q.2) q.1)
      ≤ dist (rep (v p.2) p.1) (rep (v q.2) p.1) + dist (rep (v q.2) p.1) (rep (v q.2) q.1) :=
        dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt hA (h₂ hp.1 hp1)
    _ = ε := add_halves ε

/-! ### Continuity in space and time -/

variable {N m : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **Joint continuity from continuity into $H^m(\Omega)$.** Let $\Omega \subseteq \mathbb{R}^N$ be
an extension domain for every exponent (an open set of class $C^1$ with bounded boundary, or the
half space), let $m > N/2$ and $s \subseteq \mathbb{R}$. Let $u : \mathbb{R} \to L^2(\Omega)$ be
of class $C(s; H^m(\Omega))$: it factors on $s$ through the inclusion
$H^m(\Omega) \to L^2(\Omega)$ by a curve $v$ continuous on $s$. Then there is $U : \mathbb{R}^N
\times \mathbb{R} \to \mathbb{R}$, continuous on $\bar\Omega \times s$, with
$U(\cdot, t) = u(t)$ almost everywhere on $\Omega$ for every $t \in s$. Corollary 10.5 of
[brezis2011functional] ($u \in C(\bar Q)$) needs this.

The hypothesis on $\Omega$ is `IsSobolevExtensionDomainAll N Ω`. Proof idea: Corollary 9.15 at
order $0$ (`SobolevEuclidean.exists_forall_continuous_ae_eq_of_order_of_hasSobolevExtension`)
gives every $w \in H^m(\Omega)$ a continuous representative $\tilde w$ on $\mathbb{R}^N$ with
$\|\tilde w\|_\infty \le C \|w\|$. The representative is unique on $\bar\Omega$
(`ContinuousOn.eqOn_closure_of_ae_eq`), so $w \mapsto \tilde w$ is additive there and $|\tilde
w_1(x) - \tilde w_2(x)| \le C \|w_1 - w_2\|$ for $x \in \bar\Omega$. Then
$U(x, t) = \widetilde{v(t)}(x)$ is jointly continuous by
`Bochner.continuousOn_prod_of_forall_norm_sub_le`. -/
theorem continuousOn_spaceTime_of_contDiffOnThrough (hΩ : IsSobolevExtensionDomainAll N Ω)
    (hm : (N : ℝ) / 2 < m) {s : Set ℝ}
    {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hu : ContDiffOnThrough (SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
      m 2 Ω volume) 0 u s) :
    ∃ U : EuclideanSpace ℝ (Fin N) × ℝ → ℝ,
      ContinuousOn U (closure (Ω : Set (EuclideanSpace ℝ (Fin N))) ×ˢ s) ∧
      ∀ t ∈ s, (fun x ↦ U (x, t)) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u t := by
  obtain ⟨v, hv, huv⟩ := hu
  have : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by exact_mod_cast one_le_two⟩
  obtain ⟨C, θ, hC0, -, -, -, hrep⟩ :=
    SobolevEuclidean.exists_forall_continuous_ae_eq_of_order_of_hasSobolevExtension (p := 2)
      (m := m) hΩ (Or.inr one_lt_two) (by exact_mod_cast hm)
  choose rep hrepc hrepae hrepb hrepH using hrep
  clear hrepH
  -- the representatives are additive on `closure Ω`
  have hsub : ∀ w₁ w₂ : SobolevEuclidean N m ((2 : ℝ≥0) : ℝ≥0∞) Ω,
      ∀ x ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin N))),
        ‖rep w₁ x - rep w₂ x‖ ≤ C * ‖w₁ - w₂‖ := by
    intro w₁ w₂ x hx
    -- `rep (w₁ − w₂) + rep w₂` and `rep w₁` are continuous representatives of `fn w₁`
    have h1 : SobolevMultiIndex.fn w₁ =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        SobolevMultiIndex.fn (w₁ - w₂) + SobolevMultiIndex.fn w₂ := by
      have h2 := SobolevMultiIndex.fn_add (w₁ - w₂) w₂
      rwa [sub_add_cancel] at h2
    have heq : EqOn (rep w₁) (rep (w₁ - w₂) + rep w₂)
        (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
      refine ContinuousOn.eqOn_closure_of_ae_eq (μ := volume) Ω.isOpen (hrepc w₁).continuousOn
        ((hrepc _).add (hrepc w₂)).continuousOn ?_
      filter_upwards [hrepae w₁, hrepae w₂, hrepae (w₁ - w₂), h1] with x hx₁ hx₂ hx₃ hx₄
      rw [← hx₁, hx₄, Pi.add_apply, Pi.add_apply, hx₂, hx₃]
    have h3 := heq hx
    rw [Pi.add_apply] at h3
    rw [h3, add_sub_cancel_right]
    exact hrepb _ x
  refine ⟨fun q ↦ rep (v q.2) q.1, ?_, fun t ht ↦ ?_⟩
  · exact continuousOn_prod_of_forall_norm_sub_le (fun w ↦ (hrepc w).continuousOn) hsub
      hv.continuousOn
  · rw [huv t ht, SobolevMultiIndex.fnL_apply]
    exact (hrepae (v t)).symm


/-! ### The canonical $C^k(\bar\Omega)$ representatives are linear on the closure -/

section Linearity

variable {N m : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))} {p : ℝ≥0∞}
  {rep : SobolevEuclidean N m p Ω → EuclideanSpace ℝ (Fin N) → ℝ}

/-- Let $\operatorname{rep}(w) : \mathbb{R}^N \to \mathbb{R}$, for $w \in W^{m,p}(\Omega)$, be
continuous and equal to $w$ almost everywhere on $\Omega$. Then $\operatorname{rep}(w_1 + w_2) =
\operatorname{rep}(w_1) + \operatorname{rep}(w_2)$ on $\bar\Omega$, by the uniqueness of
continuous representatives (`ContinuousOn.eqOn_closure_of_ae_eq`). -/
theorem eqOn_closure_rep_add (hrepc : ∀ w, Continuous (rep w))
    (hrepae : ∀ w, SobolevMultiIndex.fn w
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] rep w)
    (w₁ w₂ : SobolevEuclidean N m p Ω) :
    EqOn (rep (w₁ + w₂)) (rep w₁ + rep w₂) (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
  refine ContinuousOn.eqOn_closure_of_ae_eq (μ := volume) Ω.isOpen (hrepc _).continuousOn
    ((hrepc w₁).add (hrepc w₂)).continuousOn ?_
  filter_upwards [hrepae w₁, hrepae w₂, hrepae (w₁ + w₂), SobolevMultiIndex.fn_add w₁ w₂]
    with x h₁ h₂ h₃ h₄
  rw [← h₃, h₄, Pi.add_apply, Pi.add_apply, h₁, h₂]

/-- Let $\operatorname{rep}(w) : \mathbb{R}^N \to \mathbb{R}$, for $w \in W^{m,p}(\Omega)$, be
continuous and equal to $w$ almost everywhere on $\Omega$. Then $\operatorname{rep}(cw) = c
\operatorname{rep}(w)$ on $\bar\Omega$ for every $c \in \mathbb{R}$. -/
theorem eqOn_closure_rep_smul (hrepc : ∀ w, Continuous (rep w))
    (hrepae : ∀ w, SobolevMultiIndex.fn w
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] rep w)
    (c : ℝ) (w : SobolevEuclidean N m p Ω) :
    EqOn (rep (c • w)) (c • rep w) (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
  refine ContinuousOn.eqOn_closure_of_ae_eq (μ := volume) Ω.isOpen (hrepc _).continuousOn
    ((hrepc w).const_smul c).continuousOn ?_
  filter_upwards [hrepae w, hrepae (c • w), SobolevMultiIndex.fn_smul c w] with x h₁ h₂ h₃
  rw [← h₂, h₃, Pi.smul_apply, Pi.smul_apply, h₁]

variable {k : ℕ} {G : SobolevEuclidean N m p Ω → EuclideanSpace ℝ (Fin N) →
  (EuclideanSpace ℝ (Fin N) [×k]→L[ℝ] ℝ)}

/-- Let $f_1, f_2 : \mathbb{R}^N \to \mathbb{R}$ be of class $C^k$ on the open set $\Omega$, and let
$f = f_1 + f_2$ on $\Omega$. Then $D^k f(x) = D^k f_1(x) + D^k f_2(x)$ for every $x \in \Omega$. -/
theorem iteratedFDeriv_add_of_eqOn {f f₁ f₂ : EuclideanSpace ℝ (Fin N) → ℝ}
    (h : EqOn f (f₁ + f₂) (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (h₁ : ContDiffOn ℝ k f₁ Ω) (h₂ : ContDiffOn ℝ k f₂ Ω) {x : EuclideanSpace ℝ (Fin N)}
    (hx : x ∈ Ω) :
    iteratedFDeriv ℝ k f x = iteratedFDeriv ℝ k f₁ x + iteratedFDeriv ℝ k f₂ x := by
  have heq : f =ᶠ[𝓝 x] f₁ + f₂ := eventually_of_mem (Ω.isOpen.mem_nhds hx) h
  rw [(heq.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds, ← iteratedFDerivWithin_of_isOpen k Ω.isOpen hx,
    ← iteratedFDerivWithin_of_isOpen k Ω.isOpen hx, ← iteratedFDerivWithin_of_isOpen k Ω.isOpen hx,
    iteratedFDerivWithin_add_apply (h₁ x hx) (h₂ x hx) Ω.isOpen.uniqueDiffOn hx]

/-- Let $f_1 : \mathbb{R}^N \to \mathbb{R}$ be of class $C^k$ on the open set $\Omega$, let
$c \in \mathbb{R}$, and let $f = c f_1$ on $\Omega$. Then $D^k f(x) = c D^k f_1(x)$ for every
$x \in \Omega$. -/
theorem iteratedFDeriv_smul_of_eqOn {f f₁ : EuclideanSpace ℝ (Fin N) → ℝ} {c : ℝ}
    (h : EqOn f (c • f₁) (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (h₁ : ContDiffOn ℝ k f₁ Ω) {x : EuclideanSpace ℝ (Fin N)} (hx : x ∈ Ω) :
    iteratedFDeriv ℝ k f x = c • iteratedFDeriv ℝ k f₁ x := by
  have heq : f =ᶠ[𝓝 x] c • f₁ := eventually_of_mem (Ω.isOpen.mem_nhds hx) h
  rw [(heq.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds, ← iteratedFDerivWithin_of_isOpen k Ω.isOpen hx,
    ← iteratedFDerivWithin_of_isOpen k Ω.isOpen hx,
    iteratedFDerivWithin_const_smul_apply (h₁ x hx) Ω.isOpen.uniqueDiffOn hx]

/-- Let $\operatorname{rep}(w) : \mathbb{R}^N \to \mathbb{R}$, for $w \in W^{m,p}(\Omega)$, be
continuous, equal to $w$ almost everywhere on $\Omega$, and of class $C^k$ on $\Omega$. Let
$G(w)$ be continuous on $\mathbb{R}^N$ and equal to $D^k \operatorname{rep}(w)$ on $\Omega$.
Then $G(w_1 + w_2) = G(w_1) + G(w_2)$ on $\bar\Omega$. -/
theorem eqOn_closure_deriv_rep_add (hrepc : ∀ w, Continuous (rep w))
    (hrepae : ∀ w, SobolevMultiIndex.fn w
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] rep w)
    (hrepd : ∀ w, ContDiffOn ℝ k (rep w) Ω) (hGc : ∀ w, Continuous (G w))
    (hGe : ∀ w, EqOn (iteratedFDeriv ℝ k (rep w)) (G w) Ω) (w₁ w₂ : SobolevEuclidean N m p Ω) :
    EqOn (G (w₁ + w₂)) (G w₁ + G w₂) (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
  refine EqOn.of_subset_closure (fun x hx ↦ ?_) (hGc _).continuousOn
    ((hGc w₁).add (hGc w₂)).continuousOn subset_closure subset_rfl
  rw [Pi.add_apply, ← hGe _ hx, ← hGe _ hx, ← hGe _ hx]
  exact iteratedFDeriv_add_of_eqOn (eqOn_closure_rep_add hrepc hrepae w₁ w₂ |>.mono
    subset_closure) (hrepd w₁) (hrepd w₂) hx

/-- Let $\operatorname{rep}(w) : \mathbb{R}^N \to \mathbb{R}$, for $w \in W^{m,p}(\Omega)$, be
continuous, equal to $w$ almost everywhere on $\Omega$, and of class $C^k$ on $\Omega$. Let
$G(w)$ be continuous on $\mathbb{R}^N$ and equal to $D^k \operatorname{rep}(w)$ on $\Omega$.
Then $G(cw) = c G(w)$ on $\bar\Omega$ for every $c \in \mathbb{R}$. -/
theorem eqOn_closure_deriv_rep_smul (hrepc : ∀ w, Continuous (rep w))
    (hrepae : ∀ w, SobolevMultiIndex.fn w
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] rep w)
    (hrepd : ∀ w, ContDiffOn ℝ k (rep w) Ω) (hGc : ∀ w, Continuous (G w))
    (hGe : ∀ w, EqOn (iteratedFDeriv ℝ k (rep w)) (G w) Ω) (c : ℝ)
    (w : SobolevEuclidean N m p Ω) :
    EqOn (G (c • w)) (c • G w) (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
  refine EqOn.of_subset_closure (fun x hx ↦ ?_) (hGc _).continuousOn
    ((hGc w).const_smul c).continuousOn subset_closure subset_rfl
  rw [Pi.smul_apply, ← hGe _ hx, ← hGe _ hx]
  exact iteratedFDeriv_smul_of_eqOn (eqOn_closure_rep_smul hrepc hrepae c w |>.mono
    subset_closure) (hrepd w) hx

end Linearity

/-! ### Lowering the Sobolev order of a curve -/

section LowerOrder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Fintype ι]
  [LinearOrder ι] {b : Module.Basis ι ℝ E} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens E}
  {μ : Measure E}

/-- **Lowering the Sobolev order of a curve.** Let $k' \le k$. A curve
$u : \mathbb{R} \to L^p(\Omega)$ of class $C^n(s; W^{k,p}(\Omega))$ is of class
$C^n(s; W^{k',p}(\Omega))$.

So the hypothesis "$u \in C^\infty(s; H^m(\Omega))$ for every $m$" of the space–time results
follows from $u \in C^\infty(s; H^{2\ell}(\Omega))$ for every $\ell$. -/
theorem ContDiffOnThrough.sobolev_of_le {k k' : ℕ} (hk : k' ≤ k) {n : WithTop ℕ∞}
    {u : ℝ → Lp F p (μ.restrict (Ω : Set E))} {s : Set ℝ}
    (hu : ContDiffOnThrough (SobolevMultiIndex.fnL F b k p Ω μ) n u s) :
    ContDiffOnThrough (SobolevMultiIndex.fnL F b k' p Ω μ) n u s := by
  rw [← SobolevMultiIndex.fnL_comp_toLowerOrderL hk] at hu
  exact hu.of_comp

end LowerOrder

/-! ### Regularity of order $k$ in space and time -/

section Bridge

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **Joint $C^k$ regularity from $C^k$ regularity into $H^m(\Omega)$.** Let
$\Omega \subseteq \mathbb{R}^N$ be an extension domain for every exponent, let
$s \subseteq \mathbb{R}$ have unique derivatives, and let $k + N/2 < m$. Let
$u : \mathbb{R} \to L^2(\Omega)$ be of class $C^k(s; H^m(\Omega))$: it factors on $s$ through
the inclusion $H^m(\Omega) \to L^2(\Omega)$ by a curve $v$ of class $C^k$ on $s$. Then there is
$U : \mathbb{R}^N \times \mathbb{R} \to \mathbb{R}$ such that, for every $t \in s$, the function
$U(\cdot, t)$ is continuous and equal to $u(t)$ almost everywhere on $\Omega$, and $U$ is $C^k$
on $\Omega \times s$ with every derivative within $\Omega \times s$ extending continuously to
$\bar\Omega \times s$.

The conclusion on $U$ is `ContDiffOnExtendsTo ℝ k U (Ω ×ˢ s) (closure Ω ×ˢ s)`. Proof idea:
Corollary 9.15 (`SobolevEuclidean.exists_forall_contDiffOn_closure_ae_eq_of_order`) gives every
$w \in H^m(\Omega)$ a representative $\operatorname{rep}(w)$, continuous on $\mathbb{R}^N$ and
$C^k$ on $\Omega$, whose derivatives $D^i \operatorname{rep}(w)$, $i \le k$, extend continuously
to $\mathbb{R}^N$ with norm at most $C\|w\|$. The extensions are linear in $w$ on $\bar\Omega$
(`Bochner.eqOn_closure_deriv_rep_add`, `Bochner.eqOn_closure_deriv_rep_smul`), so evaluation at
a point of $\bar\Omega$ is a bounded linear functional. With $v^{(j)}$ the $j$-th derivative of
$v$ within $s$, the functions $g_{ij}(x, t) = D^i \operatorname{rep}(v^{(j)}(t))(x)$ are jointly
continuous on $\bar\Omega \times s$ (`Bochner.continuousOn_prod_of_forall_norm_sub_le`). The
$x$-derivative of $g_{ij}$ is $g_{i+1,j}$, and the $t$-derivative of $g_{ij}$ is $g_{i,j+1}$
(`Bochner.hasDerivWithinAt_of_forall_add_smul_norm_le`). The product-calculus theorem
`contDiffOnExtendsTo_prod_of_partials` then applies to $U = g_{00}$. This makes explicit at a
fixed order the step "$u \in C^k((0, \infty); H^{2\ell}(\Omega))$ for all $k, \ell$ implies $u
\in C^\infty(\bar\Omega \times [\varepsilon, \infty))$" of the proof of Theorem 10.1 of
[brezis2011functional]. -/
theorem exists_contDiffOnExtendsTo_spaceTime_of_contDiffOnThrough
    (hΩ : IsSobolevExtensionDomainAll N Ω) {s : Set ℝ} (hs : UniqueDiffOn ℝ s) {k m : ℕ}
    (hm : (k : ℝ) + N / 2 < m)
    {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hu : ContDiffOnThrough (SobolevMultiIndex.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
      m 2 Ω volume) k u s) :
    ∃ U : EuclideanSpace ℝ (Fin N) × ℝ → ℝ,
      (∀ t ∈ s, Continuous fun x ↦ U (x, t)) ∧
      (∀ t ∈ s, (fun x ↦ U (x, t)) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u t) ∧
      ContDiffOnExtendsTo ℝ k U ((Ω : Set (EuclideanSpace ℝ (Fin N))) ×ˢ s)
        (closure (Ω : Set (EuclideanSpace ℝ (Fin N))) ×ˢ s) := by
  obtain ⟨v, hv, huv⟩ := hu
  have : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by exact_mod_cast one_le_two⟩
  obtain ⟨C, θ, hC0, -, -, -, hrep⟩ :=
    SobolevEuclidean.exists_forall_contDiffOn_closure_ae_eq_of_order (p := 2) (m := m) k hΩ
      (Or.inr one_lt_two) (by exact_mod_cast hm)
  choose rep hrepc hrepd hrepae hG hGk using hrep
  clear hGk
  -- a total family of continuous extensions of the derivatives `D^j (rep w)`, `j ≤ k`
  have hG' : ∀ w : SobolevEuclidean N m ((2 : ℝ≥0) : ℝ≥0∞) Ω,
      ∃ G : (j : ℕ) → EuclideanSpace ℝ (Fin N) → (EuclideanSpace ℝ (Fin N) [×j]→L[ℝ] ℝ),
        ∀ j ≤ k, Continuous (G j) ∧ EqOn (iteratedFDeriv ℝ j (rep w)) (G j) Ω ∧
          ∀ x, ‖G j x‖ ≤ C * ‖w‖ := by
    intro w
    choose G hG using hG w
    exact ⟨fun j ↦ if h : j ≤ k then G j h else 0, fun j hj ↦ by
      simp only [dite_eq_left hj]
      exact hG j hj⟩
  choose G hG using hG'
  have hGc : ∀ j ≤ k, ∀ w, Continuous (G w j) := fun j hj w ↦ (hG w j hj).1
  have hGe : ∀ j ≤ k, ∀ w, EqOn (iteratedFDeriv ℝ j (rep w)) (G w j) Ω :=
    fun j hj w ↦ (hG w j hj).2.1
  have hGb : ∀ j ≤ k, ∀ w x, ‖G w j x‖ ≤ C * ‖w‖ := fun j hj w x ↦ (hG w j hj).2.2 x
  -- the extensions are linear on `closure Ω`
  have hGadd : ∀ j ≤ k, ∀ w₁ w₂, ∀ x ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin N))),
      G (w₁ + w₂) j x = G w₁ j x + G w₂ j x := fun j hj w₁ w₂ x hx ↦
    eqOn_closure_deriv_rep_add hrepc hrepae (fun w ↦ (hrepd w).of_le (by exact_mod_cast hj))
      (hGc j hj) (hGe j hj) w₁ w₂ hx
  have hGsmul : ∀ j ≤ k, ∀ (c : ℝ) w, ∀ x ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin N))),
      G (c • w) j x = c • G w j x := fun j hj c w x hx ↦
    eqOn_closure_deriv_rep_smul hrepc hrepae (fun w ↦ (hrepd w).of_le (by exact_mod_cast hj))
      (hGc j hj) (hGe j hj) c w hx
  -- the time derivatives of the lift
  have hv'c : ∀ j ≤ k, ContinuousOn (iteratedDerivWithin j v s) s := fun j hj ↦
    hv.continuousOn_iteratedDerivWithin (by exact_mod_cast hj) hs
  have hv'd : ∀ j < k, ∀ t ∈ s,
      HasDerivWithinAt (iteratedDerivWithin j v s) (iteratedDerivWithin (j + 1) v s t) s t := by
    intro j hj t ht
    rw [iteratedDerivWithin_succ]
    exact (hv.differentiableOn_iteratedDerivWithin (by exact_mod_cast hj) hs t ht).hasDerivWithinAt
  -- the family of partial derivatives `g i j (x, t) = D^i (rep (v^{(j)} t)) x`
  have hgc : ∀ i j, i + j ≤ k → ContinuousOn
      (fun q : EuclideanSpace ℝ (Fin N) × ℝ ↦ G (iteratedDerivWithin j v s q.2) i q.1)
      (closure (Ω : Set (EuclideanSpace ℝ (Fin N))) ×ˢ s) := by
    intro i j hij
    refine continuousOn_prod_of_forall_norm_sub_le (rep := fun w x ↦ G w i x) (C := C)
      (fun w ↦ (hGc i (by omega) w).continuousOn) (fun w₁ w₂ x hx ↦ ?_) (hv'c j (by omega))
    exact norm_sub_le_of_forall_add_smul_norm_le (Φ := fun w ↦ G w i x)
      (fun w₁ w₂ ↦ hGadd i (by omega) w₁ w₂ x hx) (fun c w ↦ hGsmul i (by omega) c w x hx)
      (fun w ↦ hGb i (by omega) w x) w₁ w₂
  have hgx : ∀ i j, i + 1 + j ≤ k → ∀ x ∈ Ω, ∀ t ∈ s,
      HasFDerivAt (fun y ↦ G (iteratedDerivWithin j v s t) i y)
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) ↦ EuclideanSpace ℝ (Fin N)) ℝ
          (G (iteratedDerivWithin j v s t) (i + 1) x)) x := by
    intro i j hij x hx t ht
    have hd : DifferentiableOn ℝ (iteratedFDeriv ℝ i (rep (iteratedDerivWithin j v s t))) Ω := by
      have := (hrepd (iteratedDerivWithin j v s t)).differentiableOn_iteratedFDerivWithin (m := i)
        (by exact_mod_cast (by omega : i < k)) Ω.isOpen.uniqueDiffOn
      exact this.congr fun y hy ↦ (iteratedFDerivWithin_of_isOpen i Ω.isOpen hy).symm
    have h1 := (hd.differentiableAt (Ω.isOpen.mem_nhds hx)).hasFDerivAt
    have h2 : fderiv ℝ (iteratedFDeriv ℝ i (rep (iteratedDerivWithin j v s t))) x =
        continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) ↦ EuclideanSpace ℝ (Fin N)) ℝ
          (iteratedFDeriv ℝ (i + 1) (rep (iteratedDerivWithin j v s t)) x) := by
      ext y w
      rw [continuousMultilinearCurryLeftEquiv_apply, iteratedFDeriv_succ_apply_left,
        Fin.cons_zero, Fin.tail_cons]
    rw [h2, hGe (i + 1) (by omega) _ hx] at h1
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
    exact (hGe i (by omega) _ hy).symm
  have hgt : ∀ i j, i + (j + 1) ≤ k → ∀ x ∈ Ω, ∀ t ∈ s,
      HasDerivWithinAt (fun r ↦ G (iteratedDerivWithin j v s r) i x)
        (G (iteratedDerivWithin (j + 1) v s t) i x) s t := by
    intro i j hij x hx t ht
    exact hasDerivWithinAt_of_forall_add_smul_norm_le (Φ := fun w ↦ G w i x)
      (fun w₁ w₂ ↦ hGadd i (by omega) w₁ w₂ x (subset_closure hx))
      (fun c w ↦ hGsmul i (by omega) c w x (subset_closure hx)) (fun w ↦ hGb i (by omega) w x)
      (hv'd j (by omega) t ht)
  have hmain := contDiffOnExtendsTo_prod_of_partials Ω.isOpen hs
    (prod_mono_left subset_closure)
    (g := fun i j q ↦ G (iteratedDerivWithin j v s q.2) i q.1) hgc hgx hgt k 0 0 (by omega)
  have hv0 : iteratedDerivWithin 0 v s = v := iteratedDerivWithin_zero
  refine ⟨fun q ↦ continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin N)) ℝ
    (G (iteratedDerivWithin 0 v s q.2) 0 q.1), fun t ht ↦ ?_, fun t ht ↦ ?_, ?_⟩
  · exact (continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin N)) ℝ).continuous.comp
      (hGc 0 (by omega) (iteratedDerivWithin 0 v s t))
  · rw [huv t ht, SobolevMultiIndex.fnL_apply]
    refine EventuallyEq.trans ?_ (hrepae (v t)).symm
    refine (ae_restrict_iff' Ω.isOpen.measurableSet).2 (Eventually.of_forall fun x hx ↦ ?_)
    change continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin N)) ℝ
      (G (iteratedDerivWithin 0 v s t) 0 x) = rep (v t) x
    rw [← hGe 0 (by omega) _ hx, continuousMultilinearCurryFin0_apply, iteratedFDeriv_zero_apply]
    exact congrArg (fun w ↦ rep w x) (congrFun hv0 t)
  · exact hmain.continuousLinearMap_comp
      ((continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin N)) ℝ).toContinuousLinearEquiv :
        (EuclideanSpace ℝ (Fin N) [×0]→L[ℝ] ℝ) →L[ℝ] ℝ)
      (UniqueDiffOn.prod Ω.isOpen.uniqueDiffOn hs)


/-- **Joint smoothness from smoothness into every $H^m(\Omega)$, with derivatives within
$\Omega \times s$.** Let $\Omega \subseteq \mathbb{R}^N$ be an extension domain for every
exponent, let $s \subseteq \mathbb{R}$ have unique derivatives, and let
$u : \mathbb{R} \to L^2(\Omega)$ be of class $C^\infty(s; H^m(\Omega))$ for every $m$. Then
there is $U : \mathbb{R}^N \times \mathbb{R} \to \mathbb{R}$ with $U(\cdot, t) = u(t)$ almost
everywhere on $\Omega$ for $t \in s$, which is $C^\infty$ on $\Omega \times s$ with every
derivative within $\Omega \times s$ extending continuously to $\bar\Omega \times s$.

Each order $k$ is `Bochner.exists_contDiffOnExtendsTo_spaceTime_of_contDiffOnThrough` with
$m = k + N + 1$. The functions $U$ of the different orders agree on $\bar\Omega \times s$ by the
uniqueness of continuous representatives (`ContinuousOn.eqOn_closure_of_ae_eq`), so the one of
order $0$ serves for all orders. -/
theorem contDiffOnExtendsTo_spaceTime_of_forall_contDiffOnThrough
    (hΩ : IsSobolevExtensionDomainAll N Ω) {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hu : ∀ m : ℕ, ContDiffOnThrough (SobolevMultiIndex.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis m 2 Ω volume) ∞ u s) :
    ∃ U : EuclideanSpace ℝ (Fin N) × ℝ → ℝ,
      (∀ t ∈ s, (fun x ↦ U (x, t)) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u t) ∧
      ContDiffOnExtendsTo ℝ ∞ U ((Ω : Set (EuclideanSpace ℝ (Fin N))) ×ˢ s)
        (closure (Ω : Set (EuclideanSpace ℝ (Fin N))) ×ˢ s) := by
  have hpack : ∀ k : ℕ, ∃ U : EuclideanSpace ℝ (Fin N) × ℝ → ℝ,
      (∀ t ∈ s, Continuous fun x ↦ U (x, t)) ∧
      (∀ t ∈ s, (fun x ↦ U (x, t)) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u t) ∧
      ContDiffOnExtendsTo ℝ k U ((Ω : Set (EuclideanSpace ℝ (Fin N))) ×ˢ s)
        (closure (Ω : Set (EuclideanSpace ℝ (Fin N))) ×ˢ s) := fun k ↦
    exists_contDiffOnExtendsTo_spaceTime_of_contDiffOnThrough hΩ hs (m := k + N + 1)
      (by push_cast; linarith [half_le_self (Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
      ((hu (k + N + 1)).of_le (by simp))
  choose U hUc hUae hU using hpack
  refine ⟨U 0, hUae 0, contDiffOnExtendsTo_infty_iff.2 fun k ↦ (hU k).congr fun q hq ↦ ?_⟩
  obtain ⟨x, t⟩ := q
  obtain ⟨hx, ht⟩ : x ∈ Ω ∧ t ∈ s := hq
  exact ContinuousOn.eqOn_closure_of_ae_eq (μ := volume) Ω.isOpen (hUc 0 t ht).continuousOn
    (hUc k t ht).continuousOn
    ((hUae 0 t ht).trans (hUae k t ht).symm) (subset_closure hx)

/-- **Joint smoothness from smoothness into every $H^m(\Omega)$.** Let
$\Omega \subseteq \mathbb{R}^N$ be an extension domain for every exponent (an open set of class
$C^1$ with bounded boundary, or the half space), let $s \subseteq \mathbb{R}$ have unique
derivatives, and let $u : \mathbb{R} \to L^2(\Omega)$ be of class $C^\infty(s; H^m(\Omega))$ for
every $m$. Then there is $U : \mathbb{R}^N \times \mathbb{R} \to \mathbb{R}$ with
$U(\cdot, t) = u(t)$ almost everywhere on $\Omega$ for every $t \in s$, which is of class
$C^\infty(\bar\Omega \times \bar s')$ for every open $s' \subseteq \mathbb{R}$ with
$\bar s' \subseteq s$: it is $C^\infty$ on $\Omega \times s'$, and every derivative extends
continuously to $\bar\Omega \times \bar s'$.

With $s = (0, \infty)$ and $s' = (\varepsilon, \infty)$ this is Theorem 10.1 (5) of
[brezis2011functional], $u \in C^\infty(\bar\Omega \times [\varepsilon, \infty))$ for every
$\varepsilon > 0$. With $s = [0, \infty)$ and $s' = (0, \infty)$ it is Theorem 10.2 (c) and
Theorem 10.8, $u \in C^\infty(\bar\Omega \times [0, \infty))$.

The class is `ContDiffOnClosure ℝ ∞ U (Ω ×ˢ s')`. The extension is asked only up to
$\bar s' \subseteq s$, because the curve need not be continuous into $H^m(\Omega)$ at the
boundary of $s$: the heat equation with $L^2$ data is not smooth at $t = 0$. The proof combines
`Bochner.contDiffOnExtendsTo_spaceTime_of_forall_contDiffOnThrough` and
`ContDiffOnExtendsTo.contDiffOnClosure`. -/
theorem contDiffOnClosure_spaceTime_of_forall_contDiffOnThrough
    (hΩ : IsSobolevExtensionDomainAll N Ω) {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hu : ∀ m : ℕ, ContDiffOnThrough (SobolevMultiIndex.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis m 2 Ω volume) ∞ u s) :
    ∃ U : EuclideanSpace ℝ (Fin N) × ℝ → ℝ,
      (∀ t ∈ s, (fun x ↦ U (x, t)) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u t) ∧
      ∀ s' : Set ℝ, IsOpen s' → closure s' ⊆ s →
        ContDiffOnClosure ℝ ∞ U ((Ω : Set (EuclideanSpace ℝ (Fin N))) ×ˢ s') := by
  obtain ⟨U, hUae, hU⟩ := contDiffOnExtendsTo_spaceTime_of_forall_contDiffOnThrough hΩ hs hu
  refine ⟨U, hUae, fun s' hs' hs's ↦ hU.contDiffOnClosure (Ω.isOpen.prod hs')
    (prod_mono_right (subset_closure.trans hs's)) ?_⟩
  rw [closure_prod_eq]
  exact prod_mono_right hs's

/-- **The space–time reading on $(a, \infty)$.** Let $\Omega \subseteq \mathbb{R}^N$ be an extension
domain for every exponent, and let $u : \mathbb{R} \to L^2(\Omega)$ be of class
$C^\infty((a, \infty); H^m(\Omega))$ for every $m$. Then there is $U : \mathbb{R}^N \times
\mathbb{R} \to \mathbb{R}$ with $U(\cdot, t) = u(t)$ almost everywhere on $\Omega$ for every
$t > a$, which is of class $C^\infty(\bar\Omega \times [\varepsilon, \infty))$ for every
$\varepsilon > a$. With $a = 0$ this is Theorem 10.1 (5) of [brezis2011functional].

The class is `ContDiffOnClosure ℝ ∞ U (Ω ×ˢ Ioi ε)`. -/
theorem contDiffOnClosure_spaceTime_of_forall_contDiffOnThrough_Ioi
    (hΩ : IsSobolevExtensionDomainAll N Ω) {a : ℝ}
    {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hu : ∀ m : ℕ, ContDiffOnThrough (SobolevMultiIndex.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis m 2 Ω volume) ∞ u (Ioi a)) :
    ∃ U : EuclideanSpace ℝ (Fin N) × ℝ → ℝ,
      (∀ t ∈ Ioi a,
        (fun x ↦ U (x, t)) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u t) ∧
      ∀ ε > a, ContDiffOnClosure ℝ ∞ U ((Ω : Set (EuclideanSpace ℝ (Fin N))) ×ˢ Ioi ε) := by
  obtain ⟨U, hUae, hU⟩ :=
    contDiffOnClosure_spaceTime_of_forall_contDiffOnThrough hΩ (uniqueDiffOn_Ioi a) hu
  exact ⟨U, hUae, fun ε hε ↦ hU (Ioi ε) isOpen_Ioi (by rw [closure_Ioi]; exact Ici_subset_Ioi.2 hε)⟩

/-- **The space–time reading on $[a, \infty)$.** Let $\Omega \subseteq \mathbb{R}^N$ be an extension
domain for every exponent, and let $u : \mathbb{R} \to L^2(\Omega)$ be of class
$C^\infty([a, \infty); H^m(\Omega))$ for every $m$. Then there is $U : \mathbb{R}^N \times
\mathbb{R} \to \mathbb{R}$ with $U(\cdot, t) = u(t)$ almost everywhere on $\Omega$ for every
$t \ge a$, which is of class $C^\infty(\bar\Omega \times [a, \infty))$: it is $C^\infty$ on
$\Omega \times (a, \infty)$, and every derivative extends continuously to
$\bar\Omega \times [a, \infty)$, the closure of $\Omega \times (a, \infty)$. With $a = 0$ this
is Theorem 10.2 (c) and Theorem 10.8 of [brezis2011functional].

The class is `ContDiffOnClosure ℝ ∞ U (Ω ×ˢ Ioi a)`. -/
theorem contDiffOnClosure_spaceTime_of_forall_contDiffOnThrough_Ici
    (hΩ : IsSobolevExtensionDomainAll N Ω) {a : ℝ}
    {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hu : ∀ m : ℕ, ContDiffOnThrough (SobolevMultiIndex.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis m 2 Ω volume) ∞ u (Ici a)) :
    ∃ U : EuclideanSpace ℝ (Fin N) × ℝ → ℝ,
      (∀ t ∈ Ici a,
        (fun x ↦ U (x, t)) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] u t) ∧
      ContDiffOnClosure ℝ ∞ U ((Ω : Set (EuclideanSpace ℝ (Fin N))) ×ˢ Ioi a) := by
  obtain ⟨U, hUae, hU⟩ :=
    contDiffOnClosure_spaceTime_of_forall_contDiffOnThrough hΩ (uniqueDiffOn_Ici a) hu
  exact ⟨U, hUae, hU (Ioi a) isOpen_Ioi (by rw [closure_Ioi])⟩

end Bridge

end Bochner

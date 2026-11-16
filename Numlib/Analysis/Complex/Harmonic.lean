/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Complex.Harmonic.Analytic`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

/-!
# Harmonic functions in the plane under a change of variable

A real-valued function $u$ on $\mathbb{C}$ is harmonic at a point if it is of class $C^2$ there and
its Laplacian vanishes in a neighbourhood of the point. Mathlib knows that harmonicity is preserved
by post-composition with a continuous linear map (`InnerProductSpace.HarmonicAt.comp_CLM`). This
module proves the two pre-composition results that potential theory in the plane needs: harmonicity
of $u$ is preserved by $u \mapsto u \circ g$ for a holomorphic map $g$, and by
$u \mapsto u \circ \overline{\,\cdot\,}$ for complex conjugation. Together they say that harmonicity
is preserved by any conformal or anticonformal change of variable. This is the property that makes
conformal mapping a tool for Laplace's equation.

Both results rest on `InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq`: a harmonic
function on a ball is the real part of a holomorphic function. The conjugation case also needs the
**Schwarz reflection**: $z \mapsto \overline{F(\bar z)}$ is holomorphic wherever $F$ is. This module
proves it from the difference quotient.

## Main results

* `HasDerivAt.conj_comp_conj` and `AnalyticOnNhd.conj_comp_conj`: Schwarz reflection, for the
  derivative at a point and for analyticity on a ball.
* `InnerProductSpace.HarmonicAt.comp_analyticAt`: harmonicity is preserved by precomposition with a
  holomorphic map.
* `InnerProductSpace.HarmonicAt.comp_conj`: harmonicity is preserved by precomposition with complex
  conjugation.

## Implementation notes

* Harmonicity is Mathlib's `InnerProductSpace.HarmonicAt`, for $\mathbb{C}$ as a real inner product
  space. Complex conjugation is `starRingEnd ℂ`.
-/

open Complex Filter Metric Topology InnerProductSpace

/-! ### Schwarz reflection -/

/-- **Schwarz reflection**, for the derivative. Let $F : \mathbb{C} \to \mathbb{C}$ have the complex
derivative $c$ at $w$. Then the function $z \mapsto \overline{F(\bar z)}$ has the complex
derivative $\bar c$ at $\bar w$. -/
theorem HasDerivAt.conj_comp_conj {F : ℂ → ℂ} {w c : ℂ} (h : HasDerivAt F c w) :
    HasDerivAt (fun z => (starRingEnd ℂ) (F ((starRingEnd ℂ) z))) ((starRingEnd ℂ) c)
      ((starRingEnd ℂ) w) := by
  rw [hasDerivAt_iff_tendsto_slope] at h ⊢
  have hconj : Tendsto (starRingEnd ℂ) (𝓝[≠] ((starRingEnd ℂ) w)) (𝓝[≠] w) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : Tendsto (starRingEnd ℂ) (𝓝 ((starRingEnd ℂ) w)) (𝓝 w) := by
        simpa using Complex.continuous_conj.tendsto ((starRingEnd ℂ) w)
      exact hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz ⊢
      intro hcon
      exact hz (by rw [← hcon, Complex.conj_conj])
  refine ((Complex.continuous_conj.tendsto c).comp (h.comp hconj)).congr fun z => ?_
  simp only [Function.comp_apply, slope_def_field, Complex.conj_conj]
  rw [← map_sub, show z - (starRingEnd ℂ) w = (starRingEnd ℂ) ((starRingEnd ℂ) z - w) by
      rw [map_sub, Complex.conj_conj], ← map_div₀]

/-- **Schwarz reflection** on a ball. Let $F : \mathbb{C} \to \mathbb{C}$ be analytic on the open
ball $B(w, R)$. Then the function $z \mapsto \overline{F(\bar z)}$ is analytic on the reflected
ball $B(\bar w, R)$. -/
theorem AnalyticOnNhd.conj_comp_conj {F : ℂ → ℂ} {w : ℂ} {R : ℝ}
    (h : AnalyticOnNhd ℂ F (ball w R)) :
    AnalyticOnNhd ℂ (fun z => (starRingEnd ℂ) (F ((starRingEnd ℂ) z))) (ball ((starRingEnd ℂ) w) R)
    := by
  have hmem : ∀ z ∈ ball ((starRingEnd ℂ) w) R, (starRingEnd ℂ) z ∈ ball w R := by
    intro z hz
    rw [mem_ball, Complex.dist_eq] at hz ⊢
    rw [show (starRingEnd ℂ) z - w = (starRingEnd ℂ) (z - (starRingEnd ℂ) w) by
      rw [map_sub, Complex.conj_conj], RCLike.norm_conj]
    exact hz
  refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_ball
  have hd := ((h _ (hmem z hz)).differentiableAt.hasDerivAt).conj_comp_conj
  rw [Complex.conj_conj] at hd
  exact hd.differentiableAt.differentiableWithinAt

/-! ### Harmonicity under a change of variable -/

/-- **Harmonicity is preserved by precomposition with a holomorphic map.** Let
$u : \mathbb{C} \to \mathbb{R}$, $g : \mathbb{C} \to \mathbb{C}$ and $x \in \mathbb{C}$. If $u$
is harmonic at $g(x)$ and $g$ is analytic at $x$, then $u \circ g$ is harmonic at $x$. -/
theorem InnerProductSpace.HarmonicAt.comp_analyticAt {u : ℂ → ℝ} {g : ℂ → ℂ} {x : ℂ}
    (hu : HarmonicAt u (g x)) (hg : AnalyticAt ℂ g x) :
    HarmonicAt (fun z => u (g z)) x := by
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.1 (isOpen_setOfPred_harmonicAt (f := u)) _ hu
  obtain ⟨F, hF, hFeq⟩ :=
    InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq (fun y hy => hball hy)
  have hev : ∀ᶠ z in 𝓝 x, g z ∈ ball (g x) ε :=
    hg.continuousAt.eventually_mem (ball_mem_nhds _ hε)
  have hFg : AnalyticAt ℂ (fun z => F (g z)) x := (hF (g x) (mem_ball_self hε)).comp hg
  refine (harmonicAt_congr_nhds (f₁ := fun z => (F (g z)).re) ?_).1 (AnalyticAt.harmonicAt_re hFg)
  filter_upwards [hev] with z hz using hFeq hz

/-- **Harmonicity is preserved by precomposition with complex conjugation.** Let
$u : \mathbb{C} \to \mathbb{R}$ and $x \in \mathbb{C}$. If $u$ is harmonic at $\bar x$, then
$z \mapsto u(\bar z)$ is harmonic at $x$. -/
theorem InnerProductSpace.HarmonicAt.comp_conj {u : ℂ → ℝ} {x : ℂ}
    (hu : HarmonicAt u ((starRingEnd ℂ) x)) :
    HarmonicAt (fun z => u ((starRingEnd ℂ) z)) x := by
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.1 (isOpen_setOfPred_harmonicAt (f := u)) _ hu
  obtain ⟨F, hF, hFeq⟩ :=
    InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq (fun y hy => hball hy)
  have hG := hF.conj_comp_conj
  rw [Complex.conj_conj] at hG
  have hmem : ∀ z ∈ ball x ε, (starRingEnd ℂ) z ∈ ball ((starRingEnd ℂ) x) ε := by
    intro z hz
    rw [mem_ball, Complex.dist_eq] at hz ⊢
    rw [← map_sub, RCLike.norm_conj]
    exact hz
  have hGa : AnalyticAt ℂ (fun z => (starRingEnd ℂ) (F ((starRingEnd ℂ) z))) x :=
    hG x (mem_ball_self hε)
  refine (harmonicAt_congr_nhds
    (f₁ := fun z => ((starRingEnd ℂ) (F ((starRingEnd ℂ) z))).re) ?_).1
    (AnalyticAt.harmonicAt_re hGa)
  filter_upwards [ball_mem_nhds x hε] with z hz
  rw [Complex.conj_re]
  exact hFeq (hmem z hz)

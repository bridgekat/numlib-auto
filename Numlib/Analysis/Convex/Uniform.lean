/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Convex.Uniform`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Convex.Uniform
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Module.HahnBanach
import Numlib.Analysis.Normed.Module.WeakDual

/-!
# The Radon–Riesz property

A normed space has the **Radon–Riesz property**, also called the Kadec–Klee property or property
(H), if weak convergence together with convergence of the norms implies convergence in norm: if
$v_n \rightharpoonup u$ weakly and $\|v_n\| \to \|u\|$, then $v_n \to u$. This module proves that
every uniformly convex space has this property, and that every inner product space has it. In an
inner product space, the proof is the expansion of $\|v_n - u\|^2$, and it needs neither
completeness nor uniform convexity. These two statements are Exercises 2.7.3 and 2.7.4(c) of
[han2009theoretical].

## Main results

* `tendsto_of_forall_dual_tendsto_of_tendsto_norm`: in a uniformly convex space,
  $v_n \rightharpoonup u$ and $\|v_n\| \to \|u\|$ imply $v_n \to u$.
* `tendsto_of_forall_dual_tendsto_of_limsup_norm_le`: the same conclusion with the one-sided
  hypothesis $\limsup \|v_n\| \le \|u\|$, as in Proposition 3.32 of [brezis2011functional].
* `tendsto_of_forall_inner_tendsto_of_tendsto_norm`: in an inner product space, $v_n \to u$ if and
  only if $\langle v_n, w \rangle \to \langle u, w \rangle$ for every $w$ and $\|v_n\| \to \|u\|$.
* `uniformConvexSpace_of_linearIsometryEquiv`: uniform convexity is preserved by a linear isometric
  isomorphism.

## Implementation notes

* Weak convergence is written in the sequential form `∀ ℓ, Tendsto (fun n => ℓ (v n)) atTop (𝓝 (ℓ
  u))`, with `ℓ` ranging over `StrongDual ℝ E`, and not through a weak topology. This is the form in
  which the numerical analysis literature states it, and the form that the users of this module
  need.
-/

open Filter Topology RCLike
open scoped InnerProductSpace

section UniformConvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [UniformConvexSpace E]

/-- Let $E$ be a uniformly convex real normed space, and let $(v_n)$ be a sequence in $E$ and
$u \in E$. If $\ell(v_n) \to \ell(u)$ for every continuous linear functional $\ell$ on $E$ and
$\|v_n\| \to \|u\|$, then $v_n \to u$ in norm.

This is the **Radon–Riesz property** of a uniformly convex space. The proof divides $v_n$ and
$u$ by $\max(\|v_n\|, \|u\|)$, so that both vectors lie in the closed unit ball, and tests their
sum against a norming functional at $u$. Then $\|a_n + b_n\| \to 2$ for the normalized vectors
$a_n$ and $b_n$, and uniform convexity gives $\|a_n - b_n\| \to 0$. -/
theorem tendsto_of_forall_dual_tendsto_of_tendsto_norm {v : ℕ → E} {u : E}
    (hweak : ∀ ℓ : StrongDual ℝ E, Tendsto (fun n => ℓ (v n)) atTop (𝓝 (ℓ u)))
    (hnorm : Tendsto (fun n => ‖v n‖) atTop (𝓝 ‖u‖)) :
    Tendsto v atTop (𝓝 u) := by
  rcases eq_or_ne u 0 with rfl | hu
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa using hnorm
  -- A norming functional at `u`.
  obtain ⟨ℓ, hℓ, hℓu⟩ := exists_dual_vector ℝ u (norm_ne_zero_iff.2 hu)
  have hu0 : 0 < ‖u‖ := norm_pos_iff.2 hu
  set t : ℕ → ℝ := fun n => max ‖v n‖ ‖u‖ with ht
  have htu : Tendsto t atTop (𝓝 ‖u‖) := by
    simpa [ht] using hnorm.max (tendsto_const_nhds (x := ‖u‖))
  have htpos : ∀ n, 0 < t n := fun n => lt_of_lt_of_le hu0 (le_max_right _ _)
  -- The normalized vectors lie in the closed unit ball.
  have hball : ∀ n, ‖(t n)⁻¹ • v n‖ ≤ 1 ∧ ‖(t n)⁻¹ • u‖ ≤ 1 := by
    refine fun n => ⟨?_, ?_⟩ <;>
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (htpos n),
        inv_mul_le_iff₀ (htpos n), mul_one]
    exacts [le_max_left _ _, le_max_right _ _]
  have hℓu' : ℓ u = ‖u‖ := by simpa using hℓu
  -- Their sum has norm tending to `2`, because `ℓ` sees the full norm of `u`.
  have hsum : Tendsto (fun n => ‖(t n)⁻¹ • v n + (t n)⁻¹ • u‖) atTop (𝓝 2) := by
    have hlow : Tendsto (fun n => (t n)⁻¹ * (ℓ (v n) + ℓ u)) atTop (𝓝 2) := by
      have hval : (‖u‖)⁻¹ * (ℓ u + ℓ u) = 2 := by
        rw [hℓu']
        field_simp
        norm_num
      have := (htu.inv₀ hu0.ne').mul ((hweak ℓ).add (tendsto_const_nhds (x := ℓ u)))
      rwa [hval] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
      (fun n => ?_) (fun n => ?_)
    · have hb := ℓ.le_opNorm ((t n)⁻¹ • v n + (t n)⁻¹ • u)
      rw [hℓ, one_mul] at hb
      refine le_trans (le_trans (le_abs_self _) ?_) hb
      rw [← Real.norm_eq_abs, map_add, map_smul, map_smul]
      simp [smul_eq_mul, mul_add]
    · exact le_trans (norm_add_le _ _) (by linarith [(hball n).1, (hball n).2])
  -- Uniform convexity turns that into `‖vₙ - u‖ → 0`.
  rw [tendsto_iff_norm_sub_tendsto_zero, NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨δ, hδ, hconv⟩ :=
    exists_forall_closed_ball_dist_add_le_two_sub E (ε := ε / (‖u‖ + 1)) (by positivity)
  have hne : ∀ᶠ n in atTop, 2 - δ < ‖(t n)⁻¹ • v n + (t n)⁻¹ • u‖ :=
    hsum.eventually (eventually_gt_nhds (by linarith))
  filter_upwards [hne, htu.eventually (eventually_lt_nhds (show ‖u‖ < ‖u‖ + 1 by linarith))]
    with n hn hbd
  have hlt : ‖(t n)⁻¹ • v n - (t n)⁻¹ • u‖ < ε / (‖u‖ + 1) := by
    by_contra hcon
    push Not at hcon
    exact absurd (hconv (hball n).1 (hball n).2 hcon) (by linarith)
  rw [← smul_sub, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (htpos n),
    inv_mul_lt_iff₀ (htpos n)] at hlt
  calc ‖‖v n - u‖‖ = ‖v n - u‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    _ < t n * (ε / (‖u‖ + 1)) := hlt
    _ ≤ (‖u‖ + 1) * (ε / (‖u‖ + 1)) := mul_le_mul_of_nonneg_right hbd.le (by positivity)
    _ = ε := by field_simp

/-- Let $E$ be a uniformly convex real normed space, and let $(v_n)$ be a sequence in $E$ and
$u \in E$. If $\ell(v_n) \to \ell(u)$ for every continuous linear functional $\ell$ on $E$ and
$$\limsup_{n \to \infty} \|v_n\| \le \|u\|,$$
then $v_n \to u$ in norm.

This is Proposition 3.32 of [brezis2011functional]. Weak convergence already gives
$\|u\| \le \liminf \|v_n\|$ (`norm_le_liminf_norm_of_weak_tendsto`) and a bound on $\|v_n\|$, so
$\|v_n\| \to \|u\|$, and `tendsto_of_forall_dual_tendsto_of_tendsto_norm` applies. -/
theorem tendsto_of_forall_dual_tendsto_of_limsup_norm_le {v : ℕ → E} {u : E}
    (hweak : ∀ ℓ : StrongDual ℝ E, Tendsto (fun n => ℓ (v n)) atTop (𝓝 (ℓ u)))
    (hlim : limsup (fun n => ‖v n‖) atTop ≤ ‖u‖) :
    Tendsto v atTop (𝓝 u) := by
  have hw : Tendsto (fun n => toWeakSpace ℝ E (v n)) atTop (𝓝 (toWeakSpace ℝ E u)) :=
    tendsto_toWeakSpace_iff.2 hweak
  obtain ⟨C, hC⟩ := exists_norm_le_of_tendsto_toWeakSpace hw
  have hnorm : Tendsto (fun n => ‖v n‖) atTop (𝓝 ‖u‖) :=
    tendsto_of_le_liminf_of_limsup_le (norm_le_liminf_norm_of_weak_tendsto hw) hlim
      (isBoundedUnder_of ⟨C, hC⟩) (isBoundedUnder_of ⟨0, fun n => norm_nonneg _⟩)
  exact tendsto_of_forall_dual_tendsto_of_tendsto_norm hweak hnorm

end UniformConvex

section Transport

variable {R E F : Type*} [Semiring R] [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  [Module R E] [Module R F]

/-- Let $E$ and $F$ be seminormed modules over a semiring $R$, and let $e \colon E \to F$ be a
linear isometric isomorphism. If $F$ is uniformly convex, then $E$ is uniformly convex.

The modulus of convexity involves only the norms of $x$, $y$, $x - y$ and $x + y$, which $e$
preserves. -/
theorem uniformConvexSpace_of_linearIsometryEquiv [UniformConvexSpace F] (e : E ≃ₗᵢ[R] F) :
    UniformConvexSpace E := by
  refine ⟨fun ε hε => ?_⟩
  obtain ⟨δ, hδ, h⟩ := exists_forall_sphere_dist_add_le_two_sub F hε
  refine ⟨δ, hδ, fun x hx y hy hxy => ?_⟩
  have := h (x := e x) (by rw [e.norm_map, hx]) (y := e y) (by rw [e.norm_map, hy])
    (by rw [← map_sub, e.norm_map]; exact hxy)
  rwa [← map_add, e.norm_map] at this

end Transport

section Inner

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Let $E$ be an inner product space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let
$(v_n)$ be a sequence in $E$ and $u \in E$. Then $v_n \to u$ in norm if and only if
$$\langle v_n, w \rangle \to \langle u, w \rangle \text{ for every } w \in E
  \quad\text{and}\quad \|v_n\| \to \|u\|.$$

This is the **Radon–Riesz property** of an inner product space, stated as a characterization of
norm convergence. The forward direction is the continuity of the inner product and of the norm.
The converse is the expansion $\|v_n - u\|^2 = \|v_n\|^2 - 2 \operatorname{Re} \langle v_n, u
\rangle + \|u\|^2$, so neither completeness nor uniform convexity is used. -/
theorem tendsto_of_forall_inner_tendsto_of_tendsto_norm {v : ℕ → E} {u : E} :
    Tendsto v atTop (𝓝 u) ↔
      (∀ w : E, Tendsto (fun n => ⟪v n, w⟫_𝕜) atTop (𝓝 ⟪u, w⟫_𝕜)) ∧
        Tendsto (fun n => ‖v n‖) atTop (𝓝 ‖u‖) := by
  constructor
  · exact fun h => ⟨fun w => h.inner tendsto_const_nhds, h.norm⟩
  · rintro ⟨hinner, hnorm⟩
    have hsq : Tendsto (fun n => ‖v n - u‖ ^ 2) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => ⟪v n, u⟫_𝕜) atTop (𝓝 ⟪u, u⟫_𝕜) := hinner u
      have hre : Tendsto (fun n => re ⟪v n, u⟫_𝕜) atTop (𝓝 (‖u‖ ^ 2)) := by
        have := (RCLike.continuous_re (K := 𝕜)).continuousAt.tendsto.comp h1
        rwa [Function.comp_def, inner_self_eq_norm_sq (𝕜 := 𝕜)] at this
      have heq : ‖u‖ ^ 2 - 2 * ‖u‖ ^ 2 + ‖u‖ ^ 2 = 0 := by ring
      have h2 := ((hnorm.pow 2).sub (hre.const_mul 2)).add
        (tendsto_const_nhds (x := ‖u‖ ^ 2) (f := atTop (α := ℕ)))
      rw [heq] at h2
      simpa [norm_sub_sq (𝕜 := 𝕜)] using h2
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa [Real.sqrt_sq, norm_nonneg] using hsq.sqrt

end Inner

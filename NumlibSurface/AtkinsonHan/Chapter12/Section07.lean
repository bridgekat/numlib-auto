/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Calculus.MeanValue
import NumlibSurface.AtkinsonHan.Chapter05.Section01
import NumlibSurface.AtkinsonHan.Chapter05.Section05
import NumlibSurface.AtkinsonHan.Chapter12.Section01

/-!
# Atkinson and Han, Section 12.7: Projection methods for nonlinear equations

This module formalizes Section 12.7.1 of [han2009theoretical]. The problem is the fixed point
equation $u = T u$ for a completely continuous operator $T$ on a Banach space $V$, approximated by
the projection equations $u_n = P_n T u_n$. Section 12.7.1 linearizes at an isolated fixed point
$u^*$. The linear theory of Section 12.1, applied to $I - T'(u^*)$, gives a uniformly bounded
inverse of $I - P_n T'(u^*)$. The second-order Taylor bounds of Lemma 12.7.1 on the remainder
$R(v; v_0) = T v - T v_0 - T'(v_0)(v - v_0)$ then make the projection equation a contraction of a
small ball about $u^*$. The result is that, for all large $n$, the projection equation has a unique
solution $u_n$ near $u^*$, with $\|u^* - u_n\| \le c \|u^* - P_n u^*\|$, and the constant $c$ is
asymptotically $\|(I - T'(u^*))^{-1}\|$ (12.7.13).

The proofs use the linear projection theory of Section 12.1
(`NumlibSurface.AtkinsonHan.Chapter12.Section01`), Proposition 5.5.5 on the compactness of the
derivative of a completely continuous operator, the Banach fixed-point theorem of Section 5.1, and
the second-order mean value inequality of `Numlib.Analysis.Calculus.MeanValue`.

## Main definitions

* (12.7.4), `AtkinsonHan.Chapter12.linearizationRemainder`: the remainder
  $R(v; v_0) = T v - T v_0 - T'(v_0)(v - v_0)$ of the linearization of $T$ at $v_0$.

## Main results

* Lemma 12.7.1 and Exercise 12.7.1, `AtkinsonHan.Chapter12.lemma_12_7_1`: the bounds (12.7.5),
  (12.7.6) and (12.7.7) on $T'$ and on the remainder, for $\|T''\| \le M$ on a convex set.
* Exercise 12.7.3, `AtkinsonHan.Chapter12.exercise_12_7_3`: for all large $n$, the projection
  equation has a unique solution $u_n$ in a fixed ball about $u^*$, and
  $\|u^* - u_n\| \le c \|u^* - P_n u^*\|$.
* (12.7.13), `AtkinsonHan.Chapter12.equation_12_7_13`: the same bound with the constant
  $\|(I - T'(u^*))^{-1}\| (1 + \gamma_n)$, where $\gamma_n \to 0$.

## Conventions

* The derivatives $T'$ and $T''$ are given as functions `T'` and `T''` with `HasFDerivAt` hypotheses
  at the points where they are used.
* The invertibility of $I - T'(u^*)$ is an equivalence `e : V ≃L[ℝ] V` with `↑e = 1 - T' ustar`, and
  the fixed point $u^*$ is `ustar`.
* The projections $P_n$ are bounded linear operators `P n` with `IsIdempotentElem (P n)`.

## Deviations from the source

* **Lemma 12.7.1** (generalization). The book asks for $T$ to be twice continuously differentiable
  on an open set $H$ and works on a closed bounded convex set $B \subseteq H$. The lemma assumes
  only derivatives at the points of a convex set and a bound on the second derivative there;
  continuity of $T''$ and boundedness of $B$ are not used. See `AtkinsonHan.Chapter12.lemma_12_7_1`.
* **Exercise 12.7.3 and (12.7.13)** (generalization). The differentiability hypotheses are made only
  on a closed ball about $u^*$, with a bound on $T''$ there. See
  `AtkinsonHan.Chapter12.exercise_12_7_3`.

## Not formalized

* **Section 12.7.2**, the homotopy argument, which computes the index of $\Phi_n(v) = v - P_n T v$
  from that of $\Phi(v) = v - T v$ with the rotation of a completely continuous vector field
  (properties P1–P5 of Section 5.5.1). Mathlib has no degree theory, and the book quotes these
  properties without proof.
* **Section 12.7.3**, the nonlinear systems (12.7.21) and (12.7.24) for the Urysohn and the
  Hammerstein equations. They are implementation.
* **Exercises 12.7.4–12.7.7.**
-/

open Filter Topology

namespace AtkinsonHan.Chapter12

/-! ### The linearization remainder -/

section Linearization

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Equation (12.7.4)** of [han2009theoretical]. Let $V$ be a real normed space, $T : V \to V$,
and let $T'(v_0)$ be a bounded linear operator for each $v_0 \in V$. The **remainder of the
linearization** of $T$ at $v_0$ is $$R(v; v_0) = T v - T v_0 - T'(v_0)(v - v_0).$$

The base point is the first argument, so `linearizationRemainder T T' v₀` is the function
$R(\cdot\,; v_0)$ of the book. -/
def linearizationRemainder (T : V → V) (T' : V → V →L[ℝ] V) (v₀ v : V) : V :=
  T v - T v₀ - T' v₀ (v - v₀)

/-- **Lemma 12.7.1** and **Exercise 12.7.1** of [han2009theoretical]. Let $V$ be a real normed space
and $B \subseteq V$ convex. Let $T : V \to V$ have the Fréchet derivative $T'(z)$ at every
$z \in B$, let $T'$ have the Fréchet derivative $T''(z)$ at every $z \in B$, and let
$\|T''(z)\| \le M$ for $z \in B$. Then for all $v_0, v_1, v_2 \in B$: $$\|T'(v_2) - T'(v_1)\|
\le M \|v_2 - v_1\| \qquad (12.7.6),$$ $$\|R(v_2; v_1)\| \le \tfrac{1}{2} M \|v_1 - v_2\|^2
\qquad (12.7.5),$$ $$\|R(v_1; v_0) - R(v_2; v_0)\| \le M \bigl(\|v_1 - v_0\| + \tfrac{1}{2}
\|v_1 - v_2\|\bigr) \|v_1 - v_2\| \qquad (12.7.7).$$ The bound (12.7.7) is Exercise 12.7.1.

**Generalization.** The book asks for $T$ to be twice continuously differentiable on an open set
$H$ and takes $B \subseteq H$ closed, bounded and convex. Only the derivatives at the points of
$B$ and the bound on $T''$ are used, so continuity of $T''$ and boundedness of $B$ are not
assumed.

The first bound is the first-order mean value inequality for $T'$. The second is the sharp
second-order inequality `Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le`, which keeps
the constant $\tfrac{1}{2}$ that Mathlib's
`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'` loses. The third uses the identity
$R(v_1; v_0) - R(v_2; v_0) = -R(v_2; v_1) + (T'(v_1) - T'(v_0))(v_1 - v_2)$ and the other two
bounds. Section 12.7.1 uses the third bound, because $R(\cdot\,; u^*)$ is the nonlinearity that
the projection equations must contract. -/
theorem lemma_12_7_1 {T : V → V} {T' : V → V →L[ℝ] V} {T'' : V → V →L[ℝ] V →L[ℝ] V} {B : Set V}
    (hB : Convex ℝ B) (hT : ∀ z ∈ B, HasFDerivAt T (T' z) z)
    (hT' : ∀ z ∈ B, HasFDerivAt T' (T'' z) z) {M : ℝ} (hM : ∀ z ∈ B, ‖T'' z‖ ≤ M) :
    (∀ v₁ ∈ B, ∀ v₂ ∈ B, ‖T' v₂ - T' v₁‖ ≤ M * ‖v₂ - v₁‖) ∧
      (∀ v₁ ∈ B, ∀ v₂ ∈ B,
        ‖linearizationRemainder T T' v₁ v₂‖ ≤ M / 2 * ‖v₁ - v₂‖ ^ 2) ∧
      (∀ v₀ ∈ B, ∀ v₁ ∈ B, ∀ v₂ ∈ B,
        ‖linearizationRemainder T T' v₀ v₁ - linearizationRemainder T T' v₀ v₂‖ ≤
          M * (‖v₁ - v₀‖ + ‖v₁ - v₂‖ / 2) * ‖v₁ - v₂‖) := by
  -- (12.7.6): the mean value inequality for `T'`
  have h6 : ∀ v₁ ∈ B, ∀ v₂ ∈ B, ‖T' v₂ - T' v₁‖ ≤ M * ‖v₂ - v₁‖ := fun v₁ h1 v₂ h2 =>
    hB.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz => (hT' z hz).hasFDerivWithinAt) hM h1 h2
  -- (12.7.5): the sharp second-order inequality, whose hypothesis is (12.7.6)
  have h5 : ∀ v₁ ∈ B, ∀ v₂ ∈ B,
      ‖linearizationRemainder T T' v₁ v₂‖ ≤ M / 2 * ‖v₁ - v₂‖ ^ 2 := by
    intro v₁ h1 v₂ h2
    have h := Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le hB hT h1 h2
      (fun z hz => h6 v₁ h1 z hz)
    rw [norm_sub_rev v₁ v₂]
    exact h
  refine ⟨h6, h5, ?_⟩
  -- (12.7.7): the difference of two remainders at the same base point
  intro v₀ h0 v₁ h1 v₂ h2
  have hid : linearizationRemainder T T' v₀ v₁ - linearizationRemainder T T' v₀ v₂
      = -linearizationRemainder T T' v₁ v₂ + (T' v₁ - T' v₀) (v₁ - v₂) := by
    simp only [linearizationRemainder, sub_apply, map_sub]
    abel
  rw [hid]
  calc ‖-linearizationRemainder T T' v₁ v₂ + (T' v₁ - T' v₀) (v₁ - v₂)‖
      ≤ ‖-linearizationRemainder T T' v₁ v₂‖ + ‖(T' v₁ - T' v₀) (v₁ - v₂)‖ := norm_add_le _ _
    _ ≤ M / 2 * ‖v₁ - v₂‖ ^ 2 + M * ‖v₁ - v₀‖ * ‖v₁ - v₂‖ := by
        refine add_le_add ?_ ?_
        · rw [norm_neg]
          exact h5 v₁ h1 v₂ h2
        · exact (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right (h6 v₀ h0 v₁ h1) (norm_nonneg _))
    _ = M * (‖v₁ - v₀‖ + ‖v₁ - v₂‖ / 2) * ‖v₁ - v₂‖ := by ring

end Linearization

/-! ### The projection equations for a nonlinear problem -/

/-- For $\Gamma, x, B \in \mathbb{R}$ with $2 \Gamma \le B$, $B > 0$ and $x < 1/2$, the bound
$\Gamma / (1 - x) \le B$ holds. -/
private theorem div_le_of_two_mul_le {Γ x B : ℝ} (h2 : 2 * Γ ≤ B) (hB : 0 < B) (hx : x < 1 / 2) :
    Γ / (1 - x) ≤ B := by
  have hpos : (0 : ℝ) < 1 - x := by linarith
  rw [div_le_iff₀ hpos]
  nlinarith [mul_pos hB (show (0 : ℝ) < 1 / 2 - x by linarith)]

section ProjectionMap

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The map $F_n v = v + R_n (P_n T v - v)$ of Section 12.7.1, where `e` gives the inverse
$R_n = (I - P_n T'(u^*))^{-1}$. -/
private noncomputable def projectionMap (e : V ≃L[ℝ] V) (P : V →L[ℝ] V) (T : V → V) (v : V) : V :=
  v + e.symm (P (T v) - v)

/-- The fixed points of $F_n$ are the solutions of the projection equation $v = P_n T v$, because
$R_n$ is injective. -/
private theorem projectionMap_eq_self_iff (e : V ≃L[ℝ] V) (P : V →L[ℝ] V) (T : V → V) (u : V) :
    projectionMap e P T u = u ↔ P (T u) = u := by
  have hzero : e.symm (P (T u) - u) = 0 ↔ P (T u) - u = 0 := by
    refine ⟨fun h => ?_, fun h => by rw [h, map_zero]⟩
    have hx := congrArg (fun y : V => e y) h
    simpa using hx
  rw [projectionMap]
  refine ⟨fun h => ?_, fun h => by rw [h, sub_self, map_zero, add_zero]⟩
  rw [← sub_eq_zero]
  exact hzero.1 (by simpa using sub_eq_zero_of_eq h)

/-- If $e = I - P_n T'(u^*)$, then $F_n v - F_n w = R_n P_n \bigl(T v - T w - T'(u^*)(v - w)\bigr)$,
which is $R_n P_n (R(v; u^*) - R(w; u^*))$. -/
private theorem projectionMap_sub (e : V ≃L[ℝ] V) {P : V →L[ℝ] V} {T : V → V}
    {T' : V → V →L[ℝ] V} {u : V} (he : (e : V →L[ℝ] V) = 1 - P ∘L T' u) (v w : V) :
    projectionMap e P T v - projectionMap e P T w
      = e.symm (P (T v - T w - T' u (v - w))) := by
  have he' : ∀ x : V, e x = x - P (T' u x) := by
    intro x
    have hx := congrArg (fun Z : V →L[ℝ] V => Z x) he
    simpa using hx
  have hinv : ∀ x : V, e.symm (x - P (T' u x)) = x := fun x => by
    rw [← he' x]; exact e.symm_apply_apply x
  have harg : (v - w) - P (T' u (v - w)) + ((P (T v) - v) - (P (T w) - w))
      = P (T v - T w - T' u (v - w)) := by
    simp only [map_sub]
    abel
  calc projectionMap e P T v - projectionMap e P T w
      = (v - w) + e.symm ((P (T v) - v) - (P (T w) - w)) := by
        simp only [projectionMap, map_sub]
        abel
    _ = e.symm ((v - w) - P (T' u (v - w))) + e.symm ((P (T v) - v) - (P (T w) - w)) := by
        rw [hinv (v - w)]
    _ = e.symm ((v - w) - P (T' u (v - w)) + ((P (T v) - v) - (P (T w) - w))) :=
        (map_add _ _ _).symm
    _ = e.symm (P (T v - T w - T' u (v - w))) := by rw [harg]

end ProjectionMap

/-- **Exercise 12.7.3** of [han2009theoretical], with the linearization analysis of Section 12.7.1.
Let $V$ be a real Banach space, let $H \subseteq V$ be open, and let $T : V \to V$ be completely
continuous on $H$. Let $u^* \in H$ be a fixed point, $T u^* = u^*$. Let $\rho > 0$, and on the
closed ball $\bar B(u^*, \rho)$ let $T$ have the Fréchet derivative $T'$, let $T'$ have the
Fréchet derivative $T''$, and let $\|T''\| \le M$. Let $I - T'(u^*)$ be invertible. Let $P_n$ be
bounded projections on $V$ with $P_n v \to v$ for every $v \in V$. Then there are
$c \in \mathbb{R}$ and $r$ with $0 < r \le \rho$ such that, for all sufficiently large $n$, the
projection equation $$u_n = P_n T u_n$$ has exactly one solution $u_n$ in the closed ball
$\bar B(u^*, r)$, and every solution $u_n$ in this ball satisfies $$\|u^* - u_n\| \le c \,
\|u^* - P_n u^*\|.$$

**Generalization.** The book asks for $T$ to be twice continuously differentiable on $H$. Here
$T$ need only be twice differentiable on the closed ball $\bar B(u^*, \rho)$, with $T''$ bounded
there.

The radius $r$ is at most the radius $\rho$ of differentiability, so that
`AtkinsonHan.Chapter12.equation_12_7_13` can use (12.7.5) at the solutions that this theorem
gives. The proof follows the book. `AtkinsonHan.Chapter05.proposition_5_5_5` makes $T'(u^*)$
compact, so `AtkinsonHan.Chapter12.lemma_12_1_4` gives $\|T'(u^*) - P_n T'(u^*)\| \to 0$, and
`AtkinsonHan.Chapter12.theorem_12_1_2` makes $I - P_n T'(u^*)$ invertible with a uniformly
bounded inverse $R_n$. The map $F_n v = v + R_n (P_n T v - v)$ has the same fixed points as the
projection equation and satisfies $F_n v - F_n w = R_n P_n (R(v; u^*) - R(w; u^*))$, so
`AtkinsonHan.Chapter12.lemma_12_7_1` makes it a contraction of the ball of radius $r$ for small
$r$, and the Banach fixed-point theorem (Theorem 5.1.3) gives the solution. The error constant
is $c = 2 \sup_n \|R_n\|$, and the contraction constant is $1/2$. The uniform boundedness of the
projections is the Banach–Steinhaus theorem, which uses completeness a second time. The sharp
constant of (12.7.13) is not claimed here. -/
theorem exercise_12_7_3 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {T : V → V} {T' : V → V →L[ℝ] V} {T'' : V → V →L[ℝ] V →L[ℝ] V}
    {H : Set V} (hH : IsOpen H) (hcc : Chapter05.IsCompletelyContinuousOn T H)
    {ustar : V} (hmem : ustar ∈ H) (hfix : T ustar = ustar) {ρ : ℝ} (hρ : 0 < ρ)
    (hT : ∀ z ∈ Metric.closedBall ustar ρ, HasFDerivAt T (T' z) z)
    (hT' : ∀ z ∈ Metric.closedBall ustar ρ, HasFDerivAt T' (T'' z) z)
    {M : ℝ} (hM : ∀ z ∈ Metric.closedBall ustar ρ, ‖T'' z‖ ≤ M)
    {e : V ≃L[ℝ] V} (he : (e : V →L[ℝ] V) = 1 - T' ustar)
    {P : ℕ → V →L[ℝ] V} (hPidem : ∀ n, IsIdempotentElem (P n))
    (hP : ∀ v, Tendsto (fun n => P n v) atTop (𝓝 v)) :
    ∃ c r : ℝ, 0 < r ∧ r ≤ ρ ∧ ∀ᶠ n in atTop,
      (∃! un : V, un ∈ Metric.closedBall ustar r ∧ P n (T un) = un) ∧
        ∀ un ∈ Metric.closedBall ustar r, P n (T un) = un →
          ‖ustar - un‖ ≤ c * ‖ustar - P n ustar‖ := by
  have hcen : ustar ∈ Metric.closedBall ustar ρ := Metric.mem_closedBall_self hρ.le
  -- the derivative at the fixed point is compact, so the linear theory of §12.1 applies to it
  have hA : IsCompactOperator (T' ustar) := Chapter05.proposition_5_5_5 hcc hH hmem (hT ustar hcen)
  have hconv : Tendsto (fun n => ‖T' ustar - P n ∘L T' ustar‖) atTop (𝓝 0) := lemma_12_1_4 hA hP
  -- the projections are uniformly bounded, by Banach–Steinhaus
  obtain ⟨Cp, hCp⟩ : ∃ C : ℝ, ∀ n, ‖P n‖ ≤ C :=
    banach_steinhaus fun x => by
      obtain ⟨m, hm⟩ := ((hP x).norm).bddAbove_range
      exact ⟨m, fun n => hm ⟨n, rfl⟩⟩
  have hCp0 : (0 : ℝ) ≤ Cp := le_trans (norm_nonneg _) (hCp 0)
  have hM0 : (0 : ℝ) ≤ M := le_trans (norm_nonneg _) (hM ustar hcen)
  -- a positive uniform bound for the approximate inverses
  obtain ⟨B, hB0, hBle⟩ : ∃ B : ℝ, 0 < B ∧ 2 * ‖(e.symm : V →L[ℝ] V)‖ ≤ B :=
    ⟨2 * ‖(e.symm : V →L[ℝ] V)‖ + 1, by positivity, by linarith⟩
  have hBne : B ≠ 0 := ne_of_gt hB0
  -- a radius small enough to make the nonlinearity a half-contraction
  obtain ⟨r, hr0, hrρ, hrsmall⟩ :
      ∃ r : ℝ, 0 < r ∧ r ≤ ρ ∧ 2 * (B * (Cp * M)) * r ≤ 1 / 2 := by
    have hκ0 : (0 : ℝ) ≤ B * (Cp * M) := mul_nonneg hB0.le (mul_nonneg hCp0 hM0)
    have hD : (0 : ℝ) < 4 * (B * (Cp * M) + 1) := by linarith
    obtain ⟨d, hd0, hdle⟩ : ∃ d : ℝ, 0 < d ∧ 4 * (B * (Cp * M) + 1) * d = 1 :=
      ⟨(4 * (B * (Cp * M) + 1))⁻¹, inv_pos.2 hD, mul_inv_cancel₀ (ne_of_gt hD)⟩
    refine ⟨min ρ d, lt_min hρ hd0, min_le_left _ _, ?_⟩
    have hr' : min ρ d ≤ d := min_le_right _ _
    have hr0' : (0 : ℝ) < min ρ d := lt_min hρ hd0
    nlinarith [mul_le_mul_of_nonneg_left hr'
      (show (0 : ℝ) ≤ 2 * (B * (Cp * M) + 1) by linarith)]
  have hsub : Metric.closedBall ustar r ⊆ Metric.closedBall ustar ρ :=
    Metric.closedBall_subset_closedBall hrρ
  have hcen' : ustar ∈ Metric.closedBall ustar r := Metric.mem_closedBall_self hr0.le
  -- (12.7.7) on the small ball
  have h7 := (lemma_12_7_1 (convex_closedBall ustar r) (fun z hz => hT z (hsub hz))
    (fun z hz => hT' z (hsub hz)) (fun z hz => hM z (hsub hz))).2.2
  refine ⟨2 * B, r, hr0, hrρ, ?_⟩
  have heps1 : ∀ᶠ n in atTop,
      ‖(e.symm : V →L[ℝ] V)‖ * ‖T' ustar - P n ∘L T' ustar‖ < 1 / 2 := by
    have h0 : Tendsto (fun n => ‖(e.symm : V →L[ℝ] V)‖ * ‖T' ustar - P n ∘L T' ustar‖)
        atTop (𝓝 0) := by simpa using hconv.const_mul ‖(e.symm : V →L[ℝ] V)‖
    exact h0.eventually (eventually_lt_nhds (by norm_num))
  have heps2 : ∀ᶠ n in atTop, ‖ustar - P n ustar‖ ≤ r / (2 * B) := by
    have h1 : Tendsto (fun n => ustar - P n ustar) atTop (𝓝 (ustar - ustar)) :=
      tendsto_const_nhds.sub (hP ustar)
    rw [sub_self] at h1
    have h0 : Tendsto (fun n => ‖ustar - P n ustar‖) atTop (𝓝 0) := by simpa using h1.norm
    exact (h0.eventually (eventually_lt_nhds (div_pos hr0 (by linarith)))).mono fun n h => h.le
  filter_upwards [heps1, heps2] with n hn1 hn2
  -- the approximate inverse of `I - P_n T'(u*)`, bounded by `B`
  obtain ⟨en, hen, hennorm, -⟩ :=
    theorem_12_1_2 (μ := (1 : ℝ)) one_ne_zero (hPidem n) e (by rw [he, one_smul]) (by linarith)
  have hRB : ‖(en.symm : V →L[ℝ] V)‖ ≤ B :=
    hennorm.trans (div_le_of_two_mul_le hBle hB0 hn1)
  have hen1 : (en : V →L[ℝ] V) = 1 - P n ∘L T' ustar := by rw [hen, one_smul]
  -- the map whose fixed points are the projection solutions
  obtain ⟨F, hF⟩ : ∃ F : V → V, ∀ v, F v = projectionMap en (P n) T v := ⟨_, fun _ => rfl⟩
  have hFsub : ∀ v w : V, F v - F w = en.symm (P n (T v - T w - T' ustar (v - w))) := fun v w => by
    rw [hF v, hF w]
    exact projectionMap_sub en hen1 v w
  -- `F` is a half-contraction of the small ball
  have hcontract : ∀ v ∈ Metric.closedBall ustar r, ∀ w ∈ Metric.closedBall ustar r,
      ‖F v - F w‖ ≤ 1 / 2 * ‖v - w‖ := by
    intro v hv w hw
    have hvu : ‖v - ustar‖ ≤ r := mem_closedBall_iff_norm.1 hv
    have hwu : ‖w - ustar‖ ≤ r := mem_closedBall_iff_norm.1 hw
    have hvw : ‖v - w‖ ≤ 2 * r := by
      have hsplit : v - w = (v - ustar) - (w - ustar) := by abel
      rw [hsplit]
      exact (norm_sub_le _ _).trans (by linarith)
    have hRdiff : linearizationRemainder T T' ustar v - linearizationRemainder T T' ustar w
        = T v - T w - T' ustar (v - w) := by
      simp only [linearizationRemainder, map_sub]
      abel
    have hx : ‖T v - T w - T' ustar (v - w)‖ ≤ 2 * M * r * ‖v - w‖ := by
      have h := h7 ustar hcen' v hv w hw
      rw [hRdiff] at h
      refine h.trans ?_
      have hsum : ‖v - ustar‖ + ‖v - w‖ / 2 ≤ 2 * r := by linarith
      calc M * (‖v - ustar‖ + ‖v - w‖ / 2) * ‖v - w‖
          ≤ M * (2 * r) * ‖v - w‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hM0) (norm_nonneg _)
        _ = 2 * M * r * ‖v - w‖ := by ring
    rw [hFsub]
    calc ‖en.symm (P n (T v - T w - T' ustar (v - w)))‖
        ≤ ‖(en.symm : V →L[ℝ] V)‖ * ‖P n (T v - T w - T' ustar (v - w))‖ :=
          ContinuousLinearMap.le_opNorm (en.symm : V →L[ℝ] V) _
      _ ≤ B * ‖P n (T v - T w - T' ustar (v - w))‖ :=
          mul_le_mul_of_nonneg_right hRB (norm_nonneg _)
      _ ≤ B * (Cp * ‖T v - T w - T' ustar (v - w)‖) :=
          mul_le_mul_of_nonneg_left
            ((ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul_of_nonneg_right (hCp n) (norm_nonneg _))) hB0.le
      _ ≤ B * (Cp * (2 * M * r * ‖v - w‖)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx hCp0) hB0.le
      _ = 2 * (B * (Cp * M)) * r * ‖v - w‖ := by ring
      _ ≤ 1 / 2 * ‖v - w‖ := mul_le_mul_of_nonneg_right hrsmall (norm_nonneg _)
  -- the displacement at the centre is the approximation error of `u*`
  have hcenter : ‖F ustar - ustar‖ ≤ B * ‖ustar - P n ustar‖ := by
    have hid : F ustar - ustar = en.symm (P n ustar - ustar) := by
      rw [hF ustar, projectionMap, hfix]
      abel
    rw [hid]
    calc ‖en.symm (P n ustar - ustar)‖
        ≤ ‖(en.symm : V →L[ℝ] V)‖ * ‖P n ustar - ustar‖ :=
          ContinuousLinearMap.le_opNorm (en.symm : V →L[ℝ] V) _
      _ ≤ B * ‖P n ustar - ustar‖ := mul_le_mul_of_nonneg_right hRB (norm_nonneg _)
      _ = B * ‖ustar - P n ustar‖ := by rw [norm_sub_rev]
  have hFcenter : ‖F ustar - ustar‖ ≤ r / 2 := by
    refine hcenter.trans ?_
    calc B * ‖ustar - P n ustar‖ ≤ B * (r / (2 * B)) :=
          mul_le_mul_of_nonneg_left hn2 hB0.le
      _ = r / 2 := by field_simp
  -- `F` maps the small ball into itself, so Theorem 5.1.3 applies
  have hmaps : Set.MapsTo F (Metric.closedBall ustar r) (Metric.closedBall ustar r) := by
    intro v hv
    have hvu : ‖v - ustar‖ ≤ r := mem_closedBall_iff_norm.1 hv
    have h1 : ‖F v - F ustar‖ ≤ 1 / 2 * ‖v - ustar‖ := hcontract v hv ustar hcen'
    have hsplit : F v - ustar = (F v - F ustar) + (F ustar - ustar) := by abel
    refine mem_closedBall_iff_norm.2 ?_
    calc ‖F v - ustar‖ ≤ ‖F v - F ustar‖ + ‖F ustar - ustar‖ := by
          rw [hsplit]; exact norm_add_le _ _
      _ ≤ 1 / 2 * r + r / 2 := add_le_add (h1.trans (by linarith)) hFcenter
      _ = r := by ring
  have hcon : Chapter05.ContractiveOn F (Metric.closedBall ustar r) (1 / 2) :=
    ⟨by norm_num, by norm_num, fun u hu v hv => hcontract u hu v hv⟩
  -- the fixed points of `F` are exactly the projection solutions
  have hfixiff : ∀ u : V, F u = u ↔ P n (T u) = u := fun u => by
    rw [hF u]
    exact projectionMap_eq_self_iff en (P n) T u
  obtain ⟨u0, ⟨hu0mem, hu0fix⟩, hu0uniq⟩ :=
    (Chapter05.theorem_5_1_3 Metric.isClosed_closedBall ⟨ustar, hcen'⟩ hmaps hcon).1
  refine ⟨⟨u0, ⟨hu0mem, (hfixiff u0).1 hu0fix⟩, ?_⟩, ?_⟩
  · rintro y ⟨hy1, hy2⟩
    exact hu0uniq y ⟨hy1, (hfixiff y).2 hy2⟩
  · intro un hun hunfix
    have hFun : F un = un := (hfixiff un).2 hunfix
    have h1 : ‖ustar - un‖ ≤ ‖ustar - F ustar‖ + ‖F ustar - F un‖ := by
      have hsplit : ustar - un = (ustar - F ustar) + (F ustar - F un) := by rw [hFun]; abel
      rw [hsplit]
      exact norm_add_le _ _
    have h2 : ‖ustar - F ustar‖ ≤ B * ‖ustar - P n ustar‖ := by
      rw [norm_sub_rev]; exact hcenter
    have h3 : ‖F ustar - F un‖ ≤ 1 / 2 * ‖ustar - un‖ := hcontract ustar hcen' un hun
    linarith

/-- **Equation (12.7.13)** of [han2009theoretical]. Under the hypotheses of
`AtkinsonHan.Chapter12.exercise_12_7_3`, there are a sequence $\gamma_n \to 0$ and a radius
$r > 0$ such that, for all sufficiently large $n$, the projection equation $u_n = P_n T u_n$ has
exactly one solution $u_n$ in the closed ball $\bar B(u^*, r)$, and every solution $u_n$ in this
ball satisfies $$\|u^* - u_n\| \le \|(I - T'(u^*))^{-1}\| \, (1 + \gamma_n) \, \|u^* - P_n
u^*\|.$$

**Generalization.** As in Exercise 12.7.3, $T$ need only be twice differentiable on the closed
ball $\bar B(u^*, \rho)$, with $T''$ bounded there.

The new part, compared with Exercise 12.7.3, is the constant. There it is a fixed multiple of
the uniform bound on the perturbed inverses $(I - P_n T'(u^*))^{-1}$; here it is asymptotically
the norm of the exact inverse, as in Exercise 12.1.3 for a linear equation. The book quotes the
bound from a paper of Atkinson without proof, and the proof here is the linear argument with the
nonlinearity absorbed into $\gamma_n$. Subtracting $u_n = P_n T u_n$ from $u^* = T u^*$ gives
$(I - P_n T'(u^*))(u^* - u_n) = (u^* - P_n u^*) - P_n R(u_n; u^*)$, and by (12.7.5) the term
$P_n R(u_n; u^*)$ is quadratic in $\|u^* - u_n\|$. The crude bound of Exercise 12.7.3 makes it
$\delta_n \|u^* - u_n\|$ with $\delta_n \to 0$, and Theorem 12.1.2 gives $\|R_n\| \le \|(I -
T'(u^*))^{-1}\| (1 + 2 \|(I - T'(u^*))^{-1}\| \|T'(u^*) - P_n T'(u^*)\|)$. The inverse
$(I - T'(u^*))^{-1}$ is `e.symm`. -/
theorem equation_12_7_13 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {T : V → V} {T' : V → V →L[ℝ] V} {T'' : V → V →L[ℝ] V →L[ℝ] V}
    {H : Set V} (hH : IsOpen H) (hcc : Chapter05.IsCompletelyContinuousOn T H)
    {ustar : V} (hmem : ustar ∈ H) (hfix : T ustar = ustar) {ρ : ℝ} (hρ : 0 < ρ)
    (hT : ∀ z ∈ Metric.closedBall ustar ρ, HasFDerivAt T (T' z) z)
    (hT' : ∀ z ∈ Metric.closedBall ustar ρ, HasFDerivAt T' (T'' z) z)
    {M : ℝ} (hM : ∀ z ∈ Metric.closedBall ustar ρ, ‖T'' z‖ ≤ M)
    {e : V ≃L[ℝ] V} (he : (e : V →L[ℝ] V) = 1 - T' ustar)
    {P : ℕ → V →L[ℝ] V} (hPidem : ∀ n, IsIdempotentElem (P n))
    (hP : ∀ v, Tendsto (fun n => P n v) atTop (𝓝 v)) :
    ∃ γ : ℕ → ℝ, Tendsto γ atTop (𝓝 0) ∧ ∃ r : ℝ, 0 < r ∧ ∀ᶠ n in atTop,
      (∃! un : V, un ∈ Metric.closedBall ustar r ∧ P n (T un) = un) ∧
        ∀ un ∈ Metric.closedBall ustar r, P n (T un) = un →
          ‖ustar - un‖ ≤ ‖(e.symm : V →L[ℝ] V)‖ * (1 + γ n) * ‖ustar - P n ustar‖ := by
  have hcen : ustar ∈ Metric.closedBall ustar ρ := Metric.mem_closedBall_self hρ.le
  have hcomp : IsCompactOperator (T' ustar) :=
    Chapter05.proposition_5_5_5 hcc hH hmem (hT ustar hcen)
  have hconv : Tendsto (fun n => ‖T' ustar - P n ∘L T' ustar‖) atTop (𝓝 0) := lemma_12_1_4 hcomp hP
  obtain ⟨Cp, hCp⟩ : ∃ C : ℝ, ∀ n, ‖P n‖ ≤ C :=
    banach_steinhaus fun x => by
      obtain ⟨m, hm⟩ := ((hP x).norm).bddAbove_range
      exact ⟨m, fun n => hm ⟨n, rfl⟩⟩
  have hCp0 : (0 : ℝ) ≤ Cp := le_trans (norm_nonneg _) (hCp 0)
  have hM0 : (0 : ℝ) ≤ M := le_trans (norm_nonneg _) (hM ustar hcen)
  obtain ⟨c, r, hr0, hrρ, hev⟩ := exercise_12_7_3 hH hcc hmem hfix hρ hT hT' hM he hPidem hP
  have hsub : Metric.closedBall ustar r ⊆ Metric.closedBall ustar ρ :=
    Metric.closedBall_subset_closedBall hrρ
  -- (12.7.5) at the base point `u*`
  have h5 := (lemma_12_7_1 (convex_closedBall ustar ρ) hT hT' hM).2.1
  -- the approximation error of the fixed point tends to zero
  have hPu : Tendsto (fun n => ‖ustar - P n ustar‖) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => ustar - P n ustar) atTop (𝓝 (ustar - ustar)) :=
      tendsto_const_nhds.sub (hP ustar)
    rw [sub_self] at h1
    simpa using h1.norm
  set A : ℝ := ‖(e.symm : V →L[ℝ] V)‖ with hAdef
  have hA0 : (0 : ℝ) ≤ A := norm_nonneg _
  refine ⟨fun n => (1 + 2 * (A * ‖T' ustar - P n ∘L T' ustar‖)) *
    (1 + 2 * (A * Cp * M * |c| * ‖ustar - P n ustar‖)) - 1, ?_, r, hr0, ?_⟩
  · have h1 : Tendsto (fun n => 1 + 2 * (A * ‖T' ustar - P n ∘L T' ustar‖)) atTop (𝓝 1) := by
      have h := (hconv.const_mul A).const_mul 2
      rw [mul_zero, mul_zero] at h
      simpa using tendsto_const_nhds.add h
    have h2 : Tendsto (fun n => 1 + 2 * (A * Cp * M * |c| * ‖ustar - P n ustar‖))
        atTop (𝓝 1) := by
      have h := (hPu.const_mul (A * Cp * M * |c|)).const_mul 2
      rw [mul_zero, mul_zero] at h
      simpa using tendsto_const_nhds.add h
    have h := (h1.mul h2).sub_const 1
    simpa using h
  have hsmall : ∀ᶠ n in atTop, A * ‖T' ustar - P n ∘L T' ustar‖ < 1 / 2 := by
    have h0 : Tendsto (fun n => A * ‖T' ustar - P n ∘L T' ustar‖) atTop (𝓝 0) := by
      simpa using hconv.const_mul A
    exact h0.eventually (eventually_lt_nhds (by norm_num))
  have hδsmall : ∀ᶠ n in atTop, A * Cp * M * |c| * ‖ustar - P n ustar‖ ≤ 1 / 2 := by
    have h0 : Tendsto (fun n => A * Cp * M * |c| * ‖ustar - P n ustar‖) atTop (𝓝 0) := by
      simpa using hPu.const_mul (A * Cp * M * |c|)
    exact (h0.eventually (eventually_lt_nhds (by norm_num))).mono fun n h => h.le
  filter_upwards [hev, hsmall, hδsmall] with n hn hns hnδ
  refine ⟨hn.1, fun un hun hunfix => ?_⟩
  set s : ℝ := A * ‖T' ustar - P n ∘L T' ustar‖ with hsdef
  set p : ℝ := ‖ustar - P n ustar‖ with hpdef
  set δ : ℝ := A * Cp * M * |c| * p with hδdef
  have hs0 : (0 : ℝ) ≤ s := by positivity
  have hp0 : (0 : ℝ) ≤ p := norm_nonneg _
  have hδ0 : (0 : ℝ) ≤ δ := by positivity
  obtain ⟨en, hen, hennorm, -⟩ :=
    theorem_12_1_2 (μ := (1 : ℝ)) one_ne_zero (hPidem n) e (by rw [he, one_smul]) (by linarith)
  have hen1 : (en : V →L[ℝ] V) = 1 - P n ∘L T' ustar := by rw [hen, one_smul]
  set Rn : ℝ := ‖(en.symm : V →L[ℝ] V)‖ with hRndef
  have hRn0 : (0 : ℝ) ≤ Rn := norm_nonneg _
  have hpos : (0 : ℝ) < 1 - s := by linarith
  have hRnle : Rn ≤ A * (1 + 2 * s) := by
    refine hennorm.trans ?_
    rw [div_le_iff₀ hpos]
    nlinarith [mul_nonneg (mul_nonneg hA0 hs0) (show (0 : ℝ) ≤ 1 - 2 * s by linarith)]
  have hRn2 : Rn ≤ 2 * A := by
    refine hennorm.trans ?_
    rw [div_le_iff₀ hpos]
    nlinarith [mul_nonneg hA0 (show (0 : ℝ) ≤ 1 - 2 * s by linarith)]
  -- the exact error identity
  have hkey : (en : V →L[ℝ] V) (ustar - un)
      = (ustar - P n ustar) - P n (linearizationRemainder T T' ustar un) := by
    rw [hen1]
    simp only [sub_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply,
      linearizationRemainder, map_sub, hfix, hunfix]
    abel
  have hsol : ustar - un
      = en.symm ((ustar - P n ustar) - P n (linearizationRemainder T T' ustar un)) := by
    rw [← hkey, ContinuousLinearEquiv.coe_coe, en.symm_apply_apply]
  set x : ℝ := ‖ustar - un‖ with hxdef
  have hx0 : (0 : ℝ) ≤ x := norm_nonneg _
  have hR : ‖linearizationRemainder T T' ustar un‖ ≤ M / 2 * x ^ 2 := h5 ustar hcen un (hsub hun)
  have hinner : ‖(ustar - P n ustar) - P n (linearizationRemainder T T' ustar un)‖
      ≤ p + Cp * (M / 2 * x ^ 2) := by
    have h1 : ‖P n (linearizationRemainder T T' ustar un)‖ ≤ Cp * (M / 2 * x ^ 2) :=
      ((P n).le_opNorm _).trans (mul_le_mul (hCp n) hR (norm_nonneg _) hCp0)
    have h2 : ‖(ustar - P n ustar) - P n (linearizationRemainder T T' ustar un)‖
        ≤ p + ‖P n (linearizationRemainder T T' ustar un)‖ := norm_sub_le _ _
    linarith
  have hmain : x ≤ Rn * (p + Cp * (M / 2 * x ^ 2)) := by
    calc x = ‖en.symm ((ustar - P n ustar) - P n (linearizationRemainder T T' ustar un))‖ :=
          congrArg norm hsol
      _ ≤ Rn * ‖(ustar - P n ustar) - P n (linearizationRemainder T T' ustar un)‖ :=
          ContinuousLinearMap.le_opNorm (en.symm : V →L[ℝ] V) _
      _ ≤ Rn * (p + Cp * (M / 2 * x ^ 2)) := mul_le_mul_of_nonneg_left hinner hRn0
  have hcrude : x ≤ |c| * p := le_trans (hn.2 un hun hunfix) (by nlinarith [le_abs_self c])
  -- the quadratic term is `δ x` with `δ → 0`
  have hquad : Rn * (Cp * (M / 2 * x ^ 2)) ≤ δ * x := by
    have hq : (0 : ℝ) ≤ Cp * (M / 2) := by positivity
    have h0 : Rn * x ≤ 2 * A * (|c| * p) :=
      (mul_le_mul_of_nonneg_right hRn2 hx0).trans
        (mul_le_mul_of_nonneg_left hcrude (by positivity))
    have h1 : Rn * (Cp * (M / 2 * x ^ 2)) ≤ 2 * A * (Cp * (M / 2 * (|c| * p) * x)) := by
      have h2 := mul_le_mul_of_nonneg_right h0 (mul_nonneg hq hx0)
      nlinarith [h2]
    calc Rn * (Cp * (M / 2 * x ^ 2)) ≤ 2 * A * (Cp * (M / 2 * (|c| * p) * x)) := h1
      _ = δ * x := by rw [hδdef]; ring
  have hstep : x * (1 - δ) ≤ Rn * p := by nlinarith
  have hfinal : x ≤ Rn * p * (1 + 2 * δ) := by
    nlinarith [mul_le_mul_of_nonneg_right hstep (show (0 : ℝ) ≤ 1 + 2 * δ by linarith),
      mul_nonneg (mul_nonneg hx0 hδ0) (show (0 : ℝ) ≤ 1 - 2 * δ by linarith)]
  calc x ≤ Rn * p * (1 + 2 * δ) := hfinal
    _ ≤ A * (1 + 2 * s) * p * (1 + 2 * δ) := by
        have := mul_le_mul_of_nonneg_right hRnle hp0
        nlinarith
    _ = A * (1 + ((1 + 2 * s) * (1 + 2 * δ) - 1)) * p := by ring

end AtkinsonHan.Chapter12

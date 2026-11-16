/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.MeanValue
import Numlib.Analysis.Calculus.MultivariateTaylor.Remainder

/-!
# Lipschitz $p$-th derivative versus bounded $(p+1)$-st derivative

Let $f : E \to F$ be a function between real normed spaces that is $C^{p+1}$ on an open convex set
$C$, and let $L \ge 0$. Then the $p$-th derivative $\nabla^p f$ is $L$-Lipschitz on $C$ if and only
if $\|\nabla^{p+1} f\| \le L$ on $C$. This is Theorem A.8.5 of [cartis2022evaluation]. With the
operator norms of Mathlib, no identity for norms of symmetric tensors is needed: the derivative of
$\nabla^p f$ is $\nabla^{p+1} f$ in curried form, with the same norm (Mathlib's
`norm_fderiv_iteratedFDeriv`).

## Main results

* `iteratedFDerivLipschitzOn_of_norm_le`: a bound on $\nabla^{p+1} f$ gives a Lipschitz
  $\nabla^p f$, by the mean value inequality. Here $C$ is convex and need not be open.
* `norm_iteratedFDeriv_succ_le_of_lipschitzOn`: a Lipschitz $\nabla^p f$ on an open set bounds
  $\nabla^{p+1} f$. No differentiability is needed.
* `iteratedFDerivLipschitzOn_iff_norm_le`: the equivalence on an open convex set.
-/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {f : E → F} {p : ℕ} {L : ℝ} {C : Set E}

/-- Let $C \subseteq E$ be convex, let $f$ be $C^{p+1}$ at every point of $C$, and let
$\|\nabla^{p+1} f(x)\| \le L$ for all $x \in C$. Then $\nabla^p f$ is $L$-Lipschitz on $C$:
$$\|\nabla^p f(x) - \nabla^p f(y)\| \le L \|x - y\| \quad \text{for all } x, y \in C.$$

This is the implication (A.21) $\Rightarrow$ (A.18) of Theorem A.8.5 of [cartis2022evaluation].
The set $C$ need not be open. The Lipschitz condition is `IteratedFDerivLipschitzOn`. -/
theorem iteratedFDerivLipschitzOn_of_norm_le (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ (p + 1) f y)
    (hb : ∀ x ∈ C, ‖iteratedFDeriv ℝ (p + 1) f x‖ ≤ L) : IteratedFDerivLipschitzOn f p L C := by
  rw [iteratedFDerivLipschitzOn_iff]
  intro x hx y hy
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hf z hz).differentiableAt_iteratedFDeriv (by norm_cast; omega))
    (fun z hz => norm_fderiv_iteratedFDeriv.le.trans (hb z hz)) hC hy hx

/-- Let $C \subseteq E$ be open, let $L \ge 0$, and let $\nabla^p f$ be $L$-Lipschitz on $C$. Then
$\|\nabla^{p+1} f(x)\| \le L$ for every $x \in C$.

This is the implication (A.18) $\Rightarrow$ (A.21) of Theorem A.8.5 of [cartis2022evaluation].
No differentiability is assumed: where $\nabla^p f$ is not differentiable, both sides of
`norm_fderiv_iteratedFDeriv` are $0$. The condition $L \ge 0$ is needed when $E$ is trivial. -/
theorem norm_iteratedFDeriv_succ_le_of_lipschitzOn (hC : IsOpen C) (hL0 : 0 ≤ L)
    (hL : IteratedFDerivLipschitzOn f p L C) {x : E} (hx : x ∈ C) :
    ‖iteratedFDeriv ℝ (p + 1) f x‖ ≤ L := by
  rw [← norm_fderiv_iteratedFDeriv]
  have hlip : LipschitzOnWith ⟨L, hL0⟩ (iteratedFDeriv ℝ p f) C :=
    iteratedFDerivLipschitzOn_iff_lipschitzOnWith.1 hL
  exact norm_fderiv_le_of_lipschitzOn ℝ (hC.mem_nhds hx) hlip

/-- Let $C \subseteq E$ be open and convex, let $L \ge 0$, and let $f$ be $C^{p+1}$ at every point
of $C$. Then $\nabla^p f$ is $L$-Lipschitz on $C$ if and only if $\|\nabla^{p+1} f(x)\| \le L$
for all $x \in C$.

This is Theorem A.8.5 of [cartis2022evaluation]. -/
theorem iteratedFDerivLipschitzOn_iff_norm_le (hCo : IsOpen C) (hC : Convex ℝ C) (hL0 : 0 ≤ L)
    (hf : ∀ y ∈ C, ContDiffAt ℝ (p + 1) f y) :
    IteratedFDerivLipschitzOn f p L C ↔ ∀ x ∈ C, ‖iteratedFDeriv ℝ (p + 1) f x‖ ≤ L :=
  ⟨fun hL _ hx => norm_iteratedFDeriv_succ_le_of_lipschitzOn hCo hL0 hL hx,
    iteratedFDerivLipschitzOn_of_norm_le hC hf⟩

/-- For a function $g : \mathbb{R} \to \mathbb{R}$, a Lipschitz $j$-th Fréchet derivative gives a
Lipschitz $j$-th derivative: if $\nabla^j g$ is $L$-Lipschitz on $C \subseteq \mathbb{R}$, then
$|g^{(j)}(s) - g^{(j)}(t)| \le L |s - t|$ for all $s, t \in C$. -/
theorem IteratedFDerivLipschitzOn.abs_iteratedDeriv_sub_le {g : ℝ → ℝ} {j : ℕ} {L : ℝ}
    {C : Set ℝ} (h : IteratedFDerivLipschitzOn g j L C) {s t : ℝ} (hs : s ∈ C) (ht : t ∈ C) :
    |iteratedDeriv j g s - iteratedDeriv j g t| ≤ L * |s - t| := by
  have := (iteratedFDerivLipschitzOn_iff.1 h) s hs t ht
  rwa [iteratedFDeriv_eq_equiv_comp, Function.comp_apply, Function.comp_apply, ← map_sub,
    LinearIsometryEquiv.norm_map, Real.norm_eq_abs, Real.norm_eq_abs] at this

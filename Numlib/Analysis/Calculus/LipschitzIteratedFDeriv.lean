import Mathlib.Analysis.Calculus.MeanValue
import Numlib.Analysis.Calculus.MultivariateTaylor.Remainder

/-!
# Lipschitz `p`-th derivative versus bounded `(p+1)`-st derivative

For `f : E → F` between real normed spaces, the `p`-th derivative is `L`-Lipschitz on an open convex
set `C` iff `‖∇^{p+1} f‖ ≤ L` on `C`, when `f` is `C^{p+1}` on `C` ([cartis2022evaluation]
Theorem A.8.5, `iteratedFDerivLipschitzOn_iff_norm_le`). With Mathlib's operator norms no identity
for norms of symmetric tensors is needed: the derivative of `∇^p f` is `∇^{p+1} f` curried, with
the same norm (`norm_fderiv_iteratedFDeriv`).

* `iteratedFDerivLipschitzOn_of_norm_le`: a bound on `∇^{p+1} f` gives a Lipschitz `∇^p f`
  (mean value inequality; `C` convex, not necessarily open);
* `norm_iteratedFDeriv_succ_le_of_lipschitzOn`: a Lipschitz `∇^p f` on an open set bounds
  `∇^{p+1} f` (no differentiability needed).
-/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {f : E → F} {p : ℕ} {L : ℝ} {C : Set E}

/-- **Theorem A.8.5 of [cartis2022evaluation], (A.21) ⇒ (A.18).** If `C` is convex, `f` is
`C^{p+1}` at every point of `C` and `‖∇^{p+1} f(x)‖ ≤ L` on `C`, then `∇^p f` is `L`-Lipschitz on
`C`. (The book assumes `C` open; convexity suffices.) -/
theorem iteratedFDerivLipschitzOn_of_norm_le (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ (p + 1) f y)
    (hb : ∀ x ∈ C, ‖iteratedFDeriv ℝ (p + 1) f x‖ ≤ L) : IteratedFDerivLipschitzOn f p L C := by
  rw [iteratedFDerivLipschitzOn_iff]
  intro x hx y hy
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hf z hz).differentiableAt_iteratedFDeriv (by norm_cast; omega))
    (fun z hz => norm_fderiv_iteratedFDeriv.le.trans (hb z hz)) hC hy hx

/-- **Theorem A.8.5 of [cartis2022evaluation], (A.18) ⇒ (A.21).** If `C` is open and `∇^p f` is
`L`-Lipschitz on `C` with `L ≥ 0`, then `‖∇^{p+1} f(x)‖ ≤ L` for `x ∈ C`. (No differentiability is
needed: where `∇^p f` is not differentiable both sides of `norm_fderiv_iteratedFDeriv` vanish.
The sign condition on `L` is needed when `E` is trivial.) -/
theorem norm_iteratedFDeriv_succ_le_of_lipschitzOn (hC : IsOpen C) (hL0 : 0 ≤ L)
    (hL : IteratedFDerivLipschitzOn f p L C) {x : E} (hx : x ∈ C) :
    ‖iteratedFDeriv ℝ (p + 1) f x‖ ≤ L := by
  rw [← norm_fderiv_iteratedFDeriv]
  have hlip : LipschitzOnWith ⟨L, hL0⟩ (iteratedFDeriv ℝ p f) C :=
    iteratedFDerivLipschitzOn_iff_lipschitzOnWith.1 hL
  exact norm_fderiv_le_of_lipschitzOn ℝ (hC.mem_nhds hx) hlip

/-- **Theorem A.8.5 of [cartis2022evaluation].** On an open convex set `C` on which `f` is
`C^{p+1}`, `∇^p f` is `L`-Lipschitz iff `‖∇^{p+1} f‖ ≤ L` on `C` (`L ≥ 0`). -/
theorem iteratedFDerivLipschitzOn_iff_norm_le (hCo : IsOpen C) (hC : Convex ℝ C) (hL0 : 0 ≤ L)
    (hf : ∀ y ∈ C, ContDiffAt ℝ (p + 1) f y) :
    IteratedFDerivLipschitzOn f p L C ↔ ∀ x ∈ C, ‖iteratedFDeriv ℝ (p + 1) f x‖ ≤ L :=
  ⟨fun hL _ hx => norm_iteratedFDeriv_succ_le_of_lipschitzOn hCo hL0 hL hx,
    iteratedFDerivLipschitzOn_of_norm_le hC hf⟩

/-- For a function of one real variable, a Lipschitz `j`-th Fréchet derivative is a Lipschitz
`j`-th derivative: `|g^{(j)}(s) - g^{(j)}(t)| ≤ L |s - t|` on `C`. -/
theorem IteratedFDerivLipschitzOn.abs_iteratedDeriv_sub_le {g : ℝ → ℝ} {j : ℕ} {L : ℝ}
    {C : Set ℝ} (h : IteratedFDerivLipschitzOn g j L C) {s t : ℝ} (hs : s ∈ C) (ht : t ∈ C) :
    |iteratedDeriv j g s - iteratedDeriv j g t| ≤ L * |s - t| := by
  have := (iteratedFDerivLipschitzOn_iff.1 h) s hs t ht
  rwa [iteratedFDeriv_eq_equiv_comp, Function.comp_apply, Function.comp_apply, ← map_sub,
    LinearIsometryEquiv.norm_map, Real.norm_eq_abs, Real.norm_eq_abs] at this

/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Composite.TaylorModel
import Numlib.Optimization.ModelBased.TaylorModel
import Numlib.Analysis.Calculus.MultivariateTaylor.DerivBound
import Numlib.Analysis.Calculus.LipschitzIteratedFDeriv
import Numlib.Analysis.SpecialFunctions.FactorialSum

/-!
# The regularized composite model

Consider a composite objective $w = f + h \circ c$ as in §14.1 of [cartis2022evaluation], with
$h : F \to \mathbb{R}$ Lipschitz and possibly nonsmooth. At each iterate, the ARqpC algorithm
(Algorithm 14.1.1) approximately minimizes the regularized composite model (14.1.11)
$$\hat m(s) = T_{f,p}(s) + h(T_{c,p}(s)) + \frac{\sigma}{(p + 1)!} \|s\|^{p+1},$$
where $T_{f,p}(s) = \sum_{i=0}^{p} \frac{1}{i!} D_{f,i}[s]^i$ and $T_{c,p}(s) = \sum_{i=0}^{p}
\frac{1}{i!} D_{c,i}[s]^i$ are the Taylor sums of derivative data $D_f$ and $D_c$. The data are the
jets of $f$ and $c$ at the iterate, or any other sequences of multilinear maps. The optimality
measure of the model at a trial step $s$ uses the decrement $\Delta T_{\hat m,j}(s, d)$ of
(14.1.14): the composite decrement of the jets at $s$ of the smooth part $s \mapsto T_{f,p}(s) +
\frac{\sigma}{(p+1)!} \|s\|^{p+1}$ and of $T_{c,p}$.

This module proves the model lemmas of §14.1: a decrease of the model from a large model decrement
(Lemma 14.1.2), small model measures at a model minimizer (Lemma 14.1.3), small composite measures
when $0$ minimizes the model (Lemma 14.1.4), the lower bound on the decrement from a model decrease
(Lemma 14.1.5), and the one-step comparison of the measures of $w$ and of $\hat m$ behind Lemma
14.1.7. With $h = 0$ the model is the regularized Taylor model `Optimization.regularizedModel` of
ARqp (§12.2.2). Lemma 12.2.8 (`Optimization.sub_regularizedModel_ge_of_taylorDecrement_ge`) is
derived from Lemma 14.1.2 here, and the smooth part
`Optimization.taylorDecrement_le_add_of_regularizedModel` of the comparison is the measure transfer
of Lemma 12.2.11.

## Main definitions

* `Optimization.compositeRegularizedModel`: the model $\hat m$ of (14.1.11).
* `Optimization.compositeModelDecrement`: the decrement $\Delta T_{\hat m,j}(s, d)$ of (14.1.14).

## Main results

* `Optimization.le_compositeTaylorDecrement_of_compositeRegularizedModel_le`: if
  $\hat m(s) \le \hat m(0)$, then $\Delta T_{w,p}(s) \ge \frac{\sigma}{(p+1)!} \|s\|^{p+1}$ (Lemma
  14.1.5).
* `Optimization.compositeRegularizedModel_sub_ge_of_decrement_ge`: a model decrement $\Delta T_{\hat
  m,j}(s, d) \ge \alpha \delta^j / j!$ along a small step $d$ gives the model decrease $\hat m(s) -
  \hat m(s + d) \ge \frac{\alpha}{2} \delta^j / j!$ (Lemma 14.1.2).
* `Optimization.compositeTaylorMeasure_model_le_of_isMinOn`: at a minimizer $s$ of the model, the
  model measure is at most $\alpha \delta^j / j!$ for the radii of Lemma 14.1.3.
* `Optimization.exists_isMinOn_compositeRegularizedModel`: in finite dimension, the model has a
  global minimizer on every closed feasible set that contains $0$.
* `Optimization.exists_radius_of_isMinOn_compositeRegularizedModel_zero`: if $0$ globally minimizes
  the model, the composite measures are at most $\varepsilon \delta^j / j!$ for all small radii
  $\delta$ (Lemma 14.1.4).
* `Optimization.compositeTaylorDecrement_le_of_step` and
  `Optimization.compositeTaylorMeasure_le_of_step`: the decrement and the measure of $w$ at $x + s$
  are at most those of the model at $s$ plus explicit terms in $\|s\|$, with the factor $2$ on the
  $\|s\|^{p+1}$ term (the comparison behind Lemma 14.1.7).

## Implementation notes

* The constants $L_f$ and $L_c$ bound the operator norms $\|D_{f,i}\|$ and $\|D_{c,i}\|$ for
  $i = 2, \dots, p$, and $L_c$ is the Lipschitz constant of $\nabla^p c$ in operator norm.
  Componentwise constants for $c : \mathbb{R}^n \to \mathbb{R}^m$ give $L_c = \sqrt{m} \, L_{c,p}$
  (see `ContinuousMultilinearMap.norm_le_sqrt_card_mul_of_euclidean`), which explains the factors
  $\sqrt{m}$ in [cartis2022evaluation].
* The model measure at $s$ is `Optimization.compositeTaylorMeasure` of the jets at $s$ of
  `Optimization.regularizedModel Df p σ` and of `Dc.taylorSum p`.
-/

open Set Metric Finset Filter Topology
open scoped Nat

namespace Optimization

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-! ### The jet of the regularized model -/

section ModelJet

variable (D : FormalMultilinearSeries ℝ E ℝ) (p : ℕ) (σ : ℝ)

/-- Let $D$ be real derivative data, $p \in \mathbb{N}$, $\sigma \in \mathbb{R}$, and $m(s) =
T_p(s) + \frac{\sigma}{(p+1)!} \|s\|^{p+1}$ the regularized model of
`Optimization.regularizedModel`. For $j \le p$ and $s, d \in E$, the Taylor sum of order $j$ of
$m$ at $s$ splits into the Taylor sums at $s$ of $T_p$ and of the regularization term:
$$T_{m,j}(s, d) = T_{T_p,j}(s, d) + \frac{\sigma}{(p+1)!} T_{\|\cdot\|^{p+1},j}(s, d).$$
-/
theorem taylorSum_ftaylorSeries_regularizedModel {j : ℕ} (hj : j ≤ p) (s d : E) :
    (ftaylorSeries ℝ (regularizedModel D p σ) s).taylorSum j d =
      (ftaylorSeries ℝ (D.taylorSum p) s).taylorSum j d +
        σ / ((p + 1)! : ℝ) *
          (ftaylorSeries ℝ (fun y : E => ‖y‖ ^ (p + 1)) s).taylorSum j d := by
  simp only [FormalMultilinearSeries.taylorSum_def, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ p := (Nat.lt_succ_iff.1 (mem_range.1 hi)).trans hj
  simp only [ftaylorSeries, iteratedFDeriv_regularizedModel (Or.inl hi'),
    add_apply, smul_apply, smul_eq_mul]
  ring

/-- For $j \le p$ and $s, d \in E$, the Taylor decrement of order $j$ of the regularized model $m$
at $s$ splits in the same way:
$$\Delta T_{m,j}(s, d) = \Delta T_{T_p,j}(s, d) + \frac{\sigma}{(p+1)!} \Delta
  T_{\|\cdot\|^{p+1},j}(s, d).$$
-/
theorem taylorDecrement_ftaylorSeries_regularizedModel {j : ℕ} (hj : j ≤ p) (s d : E) :
    (ftaylorSeries ℝ (regularizedModel D p σ) s).taylorDecrement j d =
      (ftaylorSeries ℝ (D.taylorSum p) s).taylorDecrement j d +
        σ / ((p + 1)! : ℝ) *
          (ftaylorSeries ℝ (fun y : E => ‖y‖ ^ (p + 1)) s).taylorDecrement j d := by
  simp only [FormalMultilinearSeries.taylorDecrement,
    taylorSum_ftaylorSeries_regularizedModel D p σ hj]
  ring

end ModelJet

/-! ### The model -/

section Model

variable (Df : FormalMultilinearSeries ℝ E ℝ) (Dc : FormalMultilinearSeries ℝ E F) (h : F → ℝ)
  (p : ℕ) (σ : ℝ)

/-- Let $D_f$ and $D_c$ be derivative data on $E$ with values in $\mathbb{R}$ and in $F$, let
$h : F \to \mathbb{R}$, $p \in \mathbb{N}$ and $\sigma \in \mathbb{R}$. The **regularized
composite model** of ARqpC is
$$\hat m(s) = T_{f,p}(s) + h(T_{c,p}(s)) + \frac{\sigma}{(p + 1)!} \|s\|^{p+1},$$
where $T_{f,p}$ and $T_{c,p}$ are the Taylor sums `Df.taylorSum p` and `Dc.taylorSum p`. This is
(14.1.11) of [cartis2022evaluation].

The definition is `Optimization.regularizedModel Df p σ s + h (Dc.taylorSum p s)`. -/
noncomputable def compositeRegularizedModel (s : E) : ℝ :=
  regularizedModel Df p σ s + h (Dc.taylorSum p s)

/-- The model $\hat m(s)$ is `Optimization.regularizedModel Df p σ s` plus $h(T_{c,p}(s))$. -/
theorem compositeRegularizedModel_def (s : E) :
    compositeRegularizedModel Df Dc h p σ s = regularizedModel Df p σ s + h (Dc.taylorSum p s) :=
  rfl

/-- At the zero step, $\hat m(0) = T_{f,p}(0) + h(T_{c,p}(0))$. For the exact jets of $f$ and $c$ at
$x$ this is $w(x)$. -/
@[simp]
theorem compositeRegularizedModel_zero_right :
    compositeRegularizedModel Df Dc h p σ 0 = Df.taylorSum p 0 + h (Dc.taylorSum p 0) := by
  simp [compositeRegularizedModel_def]

/-- With $h = 0$, the composite model is the regularized Taylor model
`Optimization.regularizedModel`. -/
@[simp]
theorem compositeRegularizedModel_zero_fun :
    compositeRegularizedModel Df Dc (0 : F → ℝ) p σ = regularizedModel Df p σ := by
  funext s
  simp [compositeRegularizedModel_def]

/-- If $h$ is continuous, then the composite model is continuous. -/
theorem continuous_compositeRegularizedModel (hc : Continuous h) :
    Continuous (compositeRegularizedModel Df Dc h p σ) :=
  (continuous_regularizedModel Df p σ).add (hc.comp (Dc.contDiff_taylorSum p (n := 0)).continuous)

/-- Let $D_f$, $D_c$ be derivative data, $h : F \to \mathbb{R}$, $p, j \in \mathbb{N}$,
$\sigma \in \mathbb{R}$ and $s, d \in E$. The **decrement of the composite model** at the trial
step $s$ along $d$ is
$$\Delta T_{\hat m,j}(s, d) = T_{\hat m,j}(s, 0) - T_{\hat m,j}(s, d),$$
the composite decrement `Optimization.compositeTaylorDecrement` of the jets at $s$ of the smooth
part $s \mapsto T_{f,p}(s) + \frac{\sigma}{(p+1)!} \|s\|^{p+1}$ and of $T_{c,p}$. This is
(14.1.14) of [cartis2022evaluation].

The supremum over $d \in S$ with $\|d\| \le \delta$ is the model measure
$\varphi^\delta_{\hat m,j}(s)$, which is `Optimization.compositeTaylorMeasure` of the same jets. -/
noncomputable def compositeModelDecrement (j : ℕ) (s d : E) : ℝ :=
  compositeTaylorDecrement (ftaylorSeries ℝ (regularizedModel Df p σ) s)
    (ftaylorSeries ℝ (Dc.taylorSum p) s) h j d

/-- The model decrement is the composite decrement of the jets at $s$ of
`Optimization.regularizedModel Df p σ` and of `Dc.taylorSum p`. -/
theorem compositeModelDecrement_def (j : ℕ) (s d : E) :
    compositeModelDecrement Df Dc h p σ j s d =
      compositeTaylorDecrement (ftaylorSeries ℝ (regularizedModel Df p σ) s)
        (ftaylorSeries ℝ (Dc.taylorSum p) s) h j d := rfl

/-- With $h = 0$, the model decrement at $s$ is the Taylor decrement at $s$ of the regularized
model. -/
@[simp]
theorem compositeModelDecrement_zero_fun (j : ℕ) (s : E) :
    compositeModelDecrement Df Dc (0 : F → ℝ) p σ j s =
      (ftaylorSeries ℝ (regularizedModel Df p σ) s).taylorDecrement j := by
  funext d
  rw [compositeModelDecrement_def, compositeTaylorDecrement_zero_fun]

/-- **The formula (14.1.14)** of [cartis2022evaluation]. For $j \le p$ and $s, d \in E$,
$$\Delta T_{\hat m,j}(s, d) = \Delta T_{T_{f,p},j}(s, d) + \frac{\sigma}{(p+1)!} \Delta
  T_{\|\cdot\|^{p+1},j}(s, d) + h(T_{c,p}(s)) - h(T_{T_{c,p},j}(s, d)),$$
where $\Delta T_{g,j}(s, d) = -\sum_{\ell=1}^{j} \frac{1}{\ell!} \nabla^\ell g(s)[d]^\ell$ and
$T_{g,j}(s, d) = \sum_{\ell=0}^{j} \frac{1}{\ell!} \nabla^\ell g(s)[d]^\ell$ for a smooth $g$.

The jets at $s$ are `ftaylorSeries ℝ g s` for $g = T_{f,p}$, $g = \|\cdot\|^{p+1}$ and
$g = T_{c,p}$. -/
theorem compositeModelDecrement_eq {j : ℕ} (hj : j ≤ p) (s d : E) :
    compositeModelDecrement Df Dc h p σ j s d =
      (ftaylorSeries ℝ (Df.taylorSum p) s).taylorDecrement j d +
        σ / ((p + 1)! : ℝ) *
          (ftaylorSeries ℝ (fun y : E => ‖y‖ ^ (p + 1)) s).taylorDecrement j d +
        (h (Dc.taylorSum p s) - h ((ftaylorSeries ℝ (Dc.taylorSum p) s).taylorSum j d)) := by
  rw [compositeModelDecrement_def, compositeTaylorDecrement_eq,
    taylorDecrement_ftaylorSeries_regularizedModel Df p σ hj]
  have : (ftaylorSeries ℝ (Dc.taylorSum p) s).taylorSum j 0 = Dc.taylorSum p s :=
    taylorPolynomial_zero_right (Dc.taylorSum p) j s
  rw [this]

variable {Df Dc h p σ}

/-- **Lemma 14.1.5** of [cartis2022evaluation], (14.1.25). Let $D_f$, $D_c$ be derivative data,
$h : F \to \mathbb{R}$, $p \in \mathbb{N}$ and $\sigma \in \mathbb{R}$. If the step $s$
satisfies $\hat m(s) \le \hat m(0)$, then
$$\Delta T_{w,p}(s) \ge \frac{\sigma}{(p+1)!} \|s\|^{p+1},$$
where $\Delta T_{w,p}$ is the composite decrement `Optimization.compositeTaylorDecrement Df Dc h
p`. -/
theorem le_compositeTaylorDecrement_of_compositeRegularizedModel_le {s : E}
    (hs : compositeRegularizedModel Df Dc h p σ s ≤ compositeRegularizedModel Df Dc h p σ 0) :
    σ / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) ≤ compositeTaylorDecrement Df Dc h p s := by
  rw [compositeRegularizedModel_zero_right, compositeRegularizedModel_def,
    regularizedModel_def] at hs
  rw [compositeTaylorDecrement]
  linarith

/-- **Lemma 14.1.5** of [cartis2022evaluation], strict form. If $\hat m(s) < \hat m(0)$, then
$\Delta T_{w,p}(s) > \frac{\sigma}{(p+1)!} \|s\|^{p+1}$. -/
theorem lt_compositeTaylorDecrement_of_compositeRegularizedModel_lt {s : E}
    (hs : compositeRegularizedModel Df Dc h p σ s < compositeRegularizedModel Df Dc h p σ 0) :
    σ / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) < compositeTaylorDecrement Df Dc h p s := by
  rw [compositeRegularizedModel_zero_right, compositeRegularizedModel_def,
    regularizedModel_def] at hs
  rw [compositeTaylorDecrement]
  linarith

end Model

/-! ### Model decrease from a large model decrement (Lemma 14.1.2) -/

section Decrease

variable {Df : FormalMultilinearSeries ℝ E ℝ} {Dc : FormalMultilinearSeries ℝ E F} {h : F → ℝ}
  {p : ℕ} {σ Lf Lc Lh : ℝ}

/-- **Core estimate of Lemma 14.1.2** of [cartis2022evaluation], (14.1.20)–(14.1.23). Let $h$ be
subadditive with $h(0) = 0$ and Lipschitz constant $L_h$. Let $L_f, L_c \ge 0$ with
$\|D_{f,i}\| \le L_f$ and $\|D_{c,i}\| \le L_c$ for $i = 2, \dots, p$, and let $\sigma \ge 0$
and $1 \le j \le p$. Let $\|s\| \le 1$, $0 \le \delta \le 1$ and $\|d\| \le \delta$. Then the
model decrease along $d$ differs from the model decrement by at most $2 (3 (L_f + L_h L_c) +
\sigma) \delta^{j+1} / j!$:
$$\hat m(s) - \hat m(s + d) \ge \Delta T_{\hat m,j}(s, d) - \frac{2 (3 (L_f + L_h L_c) + \sigma)
  \delta^{j+1}}{j!}.$$
-/
theorem sub_compositeRegularizedModel_ge (hLip : HasLipschitzConst h Lh) (hh : IsSubadditive h)
    (h0 : h 0 = 0) (hLf : 0 ≤ Lf) (hLc : 0 ≤ Lc)
    (hDf : ∀ i ∈ Finset.Icc 2 p, ‖Df i‖ ≤ Lf) (hDc : ∀ i ∈ Finset.Icc 2 p, ‖Dc i‖ ≤ Lc)
    (hσ : 0 ≤ σ) {j : ℕ} (hj : j ∈ Finset.Icc 1 p) {s d : E} (hs : ‖s‖ ≤ 1) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hd : ‖d‖ ≤ δ) :
    compositeModelDecrement Df Dc h p σ j s d -
        2 * (3 * (Lf + Lh * Lc) + σ) * δ ^ (j + 1) / j ! ≤
      compositeRegularizedModel Df Dc h p σ s - compositeRegularizedModel Df Dc h p σ (s + d) := by
  obtain ⟨hj1, hjp⟩ := Finset.mem_Icc.1 hj
  have hLh := hLip.nonneg
  have hc : 0 ≤ σ / ((p + 1)! : ℝ) := by positivity
  have hcfac : σ / ((p + 1)! : ℝ) * ((p + 1)! : ℝ) = σ := by field_simp
  have hhigh : ∀ ℓ ∈ Finset.Icc (j + 1) p, ∀ i ∈ Finset.Icc ℓ p, i ∈ Finset.Icc 2 p :=
    fun ℓ hℓ i hi => by
      have := Finset.mem_Icc.1 hℓ; have := Finset.mem_Icc.1 hi
      exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  -- the polynomial parts are their own Taylor polynomials at `s`
  have hA := Df.taylorSum_add_eq_taylorPolynomial p s d
  have hB := Dc.taylorSum_add_eq_taylorPolynomial p s d
  -- the regularization term: Taylor remainder (B.4.3)
  have hNrem : ‖s + d‖ ^ (p + 1) -
      (ftaylorSeries ℝ (fun y : E => ‖y‖ ^ (p + 1)) s).taylorSum p d ≤ δ ^ (p + 1) := by
    have := abs_norm_pow_sub_taylorPolynomial_le (E := E) (r := p + 1) (by omega) s d
    rw [Nat.add_sub_cancel] at this
    exact (le_abs_self _).trans (this.trans (pow_le_pow_left₀ (norm_nonneg _) hd _))
  -- the terms of orders `j + 1, …, p`
  have hAhi : (ftaylorSeries ℝ (Df.taylorSum p) s).taylorSum p d -
      (ftaylorSeries ℝ (Df.taylorSum p) s).taylorSum j d ≤
        3 * Lf * ∑ ℓ ∈ Finset.Icc (j + 1) p, δ ^ ℓ / (ℓ ! : ℝ) := by
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs]
    exact FormalMultilinearSeries.norm_taylorSum_sub_taylorSum_le_of_norm_le _ hjp
      (fun ℓ hℓ => Df.norm_iteratedFDeriv_taylorSum_le_three_mul hLf
        (fun i hi => hDf i (hhigh ℓ hℓ i hi)) hs) hd
  have hBhi : ‖(ftaylorSeries ℝ (Dc.taylorSum p) s).taylorSum p d -
      (ftaylorSeries ℝ (Dc.taylorSum p) s).taylorSum j d‖ ≤
        3 * Lc * ∑ ℓ ∈ Finset.Icc (j + 1) p, δ ^ ℓ / (ℓ ! : ℝ) :=
    FormalMultilinearSeries.norm_taylorSum_sub_taylorSum_le_of_norm_le _ hjp
      (fun ℓ hℓ => Dc.norm_iteratedFDeriv_taylorSum_le_three_mul hLc
        (fun i hi => hDc i (hhigh ℓ hℓ i hi)) hs) hd
  have hNhi : (ftaylorSeries ℝ (fun y : E => ‖y‖ ^ (p + 1)) s).taylorSum p d -
      (ftaylorSeries ℝ (fun y : E => ‖y‖ ^ (p + 1)) s).taylorSum j d ≤
        ((p + 1)! : ℝ) * ∑ ℓ ∈ Finset.Icc (j + 1) p, δ ^ ℓ / (ℓ ! : ℝ) := by
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs]
    refine FormalMultilinearSeries.norm_taylorSum_sub_taylorSum_le_of_norm_le _ hjp
      (fun ℓ hℓ => ?_) hd
    have := Finset.mem_Icc.1 hℓ
    exact norm_iteratedFDeriv_norm_pow_le_factorial (by omega) (Or.inr (by omega)) hs
  -- subadditivity of `h` separates the orders `≤ j` from the orders `> j`
  have hsub : h ((ftaylorSeries ℝ (Dc.taylorSum p) s).taylorSum p d) -
      h ((ftaylorSeries ℝ (Dc.taylorSum p) s).taylorSum j d) ≤
        Lh * (3 * Lc * ∑ ℓ ∈ Finset.Icc (j + 1) p, δ ^ ℓ / (ℓ ! : ℝ)) := by
    have := hh.sub_le_mul_norm h0 hLip ((ftaylorSeries ℝ (Dc.taylorSum p) s).taylorSum j d)
      ((ftaylorSeries ℝ (Dc.taylorSum p) s).taylorSum p d -
        (ftaylorSeries ℝ (Dc.taylorSum p) s).taylorSum j d)
    rw [add_sub_cancel] at this
    exact this.trans (mul_le_mul_of_nonneg_left hBhi hLh)
  -- the model decrement and the model values
  have hdec := compositeModelDecrement_eq Df Dc h p σ hjp s d
  simp only [FormalMultilinearSeries.taylorDecrement] at hdec
  have hz : ∀ (G : Type _) [NormedAddCommGroup G] [NormedSpace ℝ G] (g : E → G),
      (ftaylorSeries ℝ g s).taylorSum j 0 = g s := fun _ _ _ g => taylorPolynomial_zero_right g j s
  rw [hz, hz] at hdec
  have hms : compositeRegularizedModel Df Dc h p σ s =
      Df.taylorSum p s + σ / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) + h (Dc.taylorSum p s) := rfl
  have hmsd : compositeRegularizedModel Df Dc h p σ (s + d) =
      (ftaylorSeries ℝ (Df.taylorSum p) s).taylorSum p d +
        σ / ((p + 1)! : ℝ) * ‖s + d‖ ^ (p + 1) +
          h ((ftaylorSeries ℝ (Dc.taylorSum p) s).taylorSum p d) := by
    rw [compositeRegularizedModel_def, regularizedModel_def, hA, hB]; rfl
  -- the sum bound (A.33)
  set S := ∑ ℓ ∈ Finset.Icc (j + 1) p, δ ^ ℓ / (ℓ ! : ℝ) with hS
  set K := 3 * (Lf + Lh * Lc) + σ with hK
  have hST : S + δ ^ (p + 1) / ((p + 1)! : ℝ) ≤ 2 * δ ^ (j + 1) / j ! := by
    have := sum_pow_div_factorial_Icc_succ_le hδ0 hδ1 j p
    rwa [Finset.sum_Icc_succ_top (by omega)] at this
  have hK0 : σ ≤ K := by rw [hK]; nlinarith
  have hT0 : 0 ≤ δ ^ (p + 1) / ((p + 1)! : ℝ) := by positivity
  have h1 : σ * (δ ^ (p + 1) / ((p + 1)! : ℝ)) ≤ K * (δ ^ (p + 1) / ((p + 1)! : ℝ)) :=
    mul_le_mul_of_nonneg_right hK0 hT0
  have h2 : K * (S + δ ^ (p + 1) / ((p + 1)! : ℝ)) ≤ K * (2 * δ ^ (j + 1) / j !) :=
    mul_le_mul_of_nonneg_left hST (hσ.trans hK0)
  have h3 : σ / ((p + 1)! : ℝ) *
      (‖s + d‖ ^ (p + 1) - (ftaylorSeries ℝ (fun y : E => ‖y‖ ^ (p + 1)) s).taylorSum j d) ≤
        σ / ((p + 1)! : ℝ) * (δ ^ (p + 1) + ((p + 1)! : ℝ) * S) :=
    mul_le_mul_of_nonneg_left (by linarith) hc
  have h4 : σ / ((p + 1)! : ℝ) * (δ ^ (p + 1) + ((p + 1)! : ℝ) * S) =
      σ * (δ ^ (p + 1) / ((p + 1)! : ℝ)) + σ * S := by
    rw [mul_add, ← mul_assoc, hcfac]; ring
  rw [hdec, hms, hmsd]
  have e : 2 * K * δ ^ (j + 1) / j ! = K * (2 * δ ^ (j + 1) / j !) := by ring
  rw [e]
  nlinarith

/-- **Lemma 14.1.2** of [cartis2022evaluation] (for $h = 0$, Lemma 12.2.8): a model decrease from a
large model decrement. Let $h$ be subadditive with $h(0) = 0$ and Lipschitz constant $L_h$. Let
$L_f, L_c \ge 0$ with $\|D_{f,i}\| \le L_f$ and $\|D_{c,i}\| \le L_c$ for $i = 2, \dots, p$, and
let $\sigma \ge 0$, $\|s\| \le 1$ and $1 \le j \le p$. Let $\alpha \in \mathbb{R}$ and
$0 \le \delta \le 1$ with $4 (3 (L_f + L_h L_c) + \sigma) \delta \le \alpha$, and let
$\|d\| \le \delta$. If
$$\Delta T_{\hat m,j}(s, d) \ge \alpha \frac{\delta^j}{j!}$$
as in (14.1.18), then
$$\hat m(s) - \hat m(s + d) \ge \frac{\alpha}{2} \frac{\delta^j}{j!},$$
which is (14.1.19).

With $L_w = L_f + L_h L_c$, the condition on the radius is the condition (14.1.17) $\delta \le
\min(1, \alpha / (4 (3 L_w + \sigma)))$ of the source. -/
theorem compositeRegularizedModel_sub_ge_of_decrement_ge (hLip : HasLipschitzConst h Lh)
    (hh : IsSubadditive h) (h0 : h 0 = 0) (hLf : 0 ≤ Lf) (hLc : 0 ≤ Lc)
    (hDf : ∀ i ∈ Finset.Icc 2 p, ‖Df i‖ ≤ Lf) (hDc : ∀ i ∈ Finset.Icc 2 p, ‖Dc i‖ ≤ Lc)
    (hσ : 0 ≤ σ) {j : ℕ} (hj : j ∈ Finset.Icc 1 p) {s d : E} (hs : ‖s‖ ≤ 1) {α δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hδα : 4 * (3 * (Lf + Lh * Lc) + σ) * δ ≤ α) (hd : ‖d‖ ≤ δ)
    (hdec : α * δ ^ j / j ! ≤ compositeModelDecrement Df Dc h p σ j s d) :
    α / 2 * δ ^ j / j ! ≤
      compositeRegularizedModel Df Dc h p σ s - compositeRegularizedModel Df Dc h p σ (s + d) := by
  exact half_mul_pow_div_factorial_le hδ0 hδα hdec
    (sub_compositeRegularizedModel_ge hLip hh h0 hLf hLc hDf hDc hσ hj hs hδ0 hδ1 hd)

/-- **Radii at a model minimizer**, the content of Lemma 14.1.3 of [cartis2022evaluation] (for
$h = 0$, Lemma 12.2.9). Let $h$ be subadditive with $h(0) = 0$ and Lipschitz constant $L_h$. Let
$L_f, L_c \ge 0$ with $\|D_{f,i}\| \le L_f$ and $\|D_{c,i}\| \le L_c$ for $i = 2, \dots, p$, and
let $\sigma \ge 0$, $1 \le j \le p$ and $\|s\| \le 1$. Let $S \subseteq E$ be a set of feasible
displacements with $0 \in S$, and suppose that $s$ minimizes the model over $s + S$:
$\hat m(s) \le \hat m(s + d)$ for all $d \in S$. If $\alpha > 0$, $0 < \delta \le 1$ and $4 (3
(L_f + L_h L_c) + \sigma) \delta \le \alpha$, then the model measure at $s$ is small:
$$\varphi^\delta_{\hat m,j}(s) \le \alpha \frac{\delta^j}{j!}.$$

The model measure is `Optimization.compositeTaylorMeasure` of the jets at $s$ of
`Optimization.regularizedModel Df p σ` and of `Dc.taylorSum p`, over $S$. The proof applies
`Optimization.compositeRegularizedModel_sub_ge_of_decrement_ge` to an argument by contradiction. -/
theorem compositeTaylorMeasure_model_le_of_isMinOn (hLip : HasLipschitzConst h Lh)
    (hh : IsSubadditive h) (h0 : h 0 = 0) (hLf : 0 ≤ Lf) (hLc : 0 ≤ Lc)
    (hDf : ∀ i ∈ Finset.Icc 2 p, ‖Df i‖ ≤ Lf) (hDc : ∀ i ∈ Finset.Icc 2 p, ‖Dc i‖ ≤ Lc)
    (hσ : 0 ≤ σ) {j : ℕ} (hj : j ∈ Finset.Icc 1 p) {s : E} (hs : ‖s‖ ≤ 1) {S : Set E}
    (hS0 : (0 : E) ∈ S)
    (hmin : ∀ d ∈ S, compositeRegularizedModel Df Dc h p σ s ≤
      compositeRegularizedModel Df Dc h p σ (s + d))
    {α δ : ℝ} (hα : 0 < α) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hδα : 4 * (3 * (Lf + Lh * Lc) + σ) * δ ≤ α) :
    compositeTaylorMeasure (ftaylorSeries ℝ (regularizedModel Df p σ) s)
      (ftaylorSeries ℝ (Dc.taylorSum p) s) h j δ S ≤ α * δ ^ j / j ! := by
  refine decrementMeasure_le ⟨0, mem_closedBall_self hδ0.le, hS0⟩ fun d hd => ?_
  by_contra hlt
  push Not at hlt
  have hdec := compositeRegularizedModel_sub_ge_of_decrement_ge hLip hh h0 hLf hLc hDf hDc hσ hj
    hs hδ0.le hδ1 hδα (mem_closedBall_zero_iff.1 hd.1) hlt.le
  have hpos : 0 < α / 2 * δ ^ j / j ! := by positivity
  linarith [hmin d hd.2]

end Decrease

/-! ### Minimizers of the model (Lemma 14.1.4) -/

section Minimizer

variable {Df : FormalMultilinearSeries ℝ E ℝ} {Dc : FormalMultilinearSeries ℝ E F} {h : F → ℝ}
  {p : ℕ} {σ Lh : ℝ}

/-- **Pointwise bound behind Lemma 14.1.4** of [cartis2022evaluation], Appendix B. Let $h$ be
subadditive with $h(0) = 0$ and Lipschitz constant $L_h$, and let $j \le p$. If
$\hat m(0) \le \hat m(d)$, then
$$\Delta T_{w,j}(d) \le \sum_{\ell=j+1}^{p} \bigl(\|D_{f,\ell}\| + L_h \|D_{c,\ell}\|\bigr)
  \frac{\|d\|^\ell}{\ell!} + \frac{\sigma}{(p+1)!} \|d\|^{p+1}.$$
-/
theorem compositeTaylorDecrement_le_of_compositeRegularizedModel_le
    (hLip : HasLipschitzConst h Lh) (hh : IsSubadditive h) (h0 : h 0 = 0) {j : ℕ} (hjp : j ≤ p)
    {d : E}
    (hd : compositeRegularizedModel Df Dc h p σ 0 ≤ compositeRegularizedModel Df Dc h p σ d) :
    compositeTaylorDecrement Df Dc h j d ≤
      ∑ ℓ ∈ Finset.Icc (j + 1) p, (‖Df ℓ‖ + Lh * ‖Dc ℓ‖) * ‖d‖ ^ ℓ / ℓ ! +
        σ / ((p + 1)! : ℝ) * ‖d‖ ^ (p + 1) := by
  rw [compositeRegularizedModel_zero_right, compositeRegularizedModel_def, regularizedModel_def,
    Df.taylorSum_zero_right, Dc.taylorSum_zero_right] at hd
  rw [compositeTaylorDecrement, Df.taylorSum_zero_right, Dc.taylorSum_zero_right]
  have h1 : Df.taylorSum p d - Df.taylorSum j d ≤
      ∑ ℓ ∈ Finset.Icc (j + 1) p, ‖Df ℓ‖ * ‖d‖ ^ ℓ / ℓ ! := by
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs]
    exact Df.norm_taylorSum_sub_taylorSum_le hjp d
  have h2 : h (Dc.taylorSum p d) - h (Dc.taylorSum j d) ≤
      Lh * ∑ ℓ ∈ Finset.Icc (j + 1) p, ‖Dc ℓ‖ * ‖d‖ ^ ℓ / ℓ ! := by
    have := hh.sub_le_mul_norm h0 hLip (Dc.taylorSum j d) (Dc.taylorSum p d - Dc.taylorSum j d)
    rw [add_sub_cancel] at this
    exact this.trans (mul_le_mul_of_nonneg_left (Dc.norm_taylorSum_sub_taylorSum_le hjp d)
      hLip.nonneg)
  have he : ∑ ℓ ∈ Finset.Icc (j + 1) p, (‖Df ℓ‖ + Lh * ‖Dc ℓ‖) * ‖d‖ ^ ℓ / ℓ ! =
      ∑ ℓ ∈ Finset.Icc (j + 1) p, ‖Df ℓ‖ * ‖d‖ ^ ℓ / ℓ ! +
        Lh * ∑ ℓ ∈ Finset.Icc (j + 1) p, ‖Dc ℓ‖ * ‖d‖ ^ ℓ / ℓ ! := by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun _ _ => by ring
  rw [he]
  linarith

/-- **Lemma 14.1.4** of [cartis2022evaluation] (for $h = 0$, Lemma 12.2.10). Let $h$ be subadditive
with $h(0) = 0$ and with a Lipschitz constant, let $\sigma \ge 0$ and $j \le p$, and let
$T \subseteq E$ be a set of feasible displacements with $0 \in T$. If $0$ globally minimizes the
composite model $\hat m$ on $T$, then for every $\varepsilon > 0$ there is $\delta_0 \in (0, 1]$
such that
$$\varphi^\delta_{w,j} \le \varepsilon \frac{\delta^j}{j!} \qquad \text{for every } \delta \in
  [0, \delta_0].$$
So the iterate is an $(\varepsilon, \delta)$-approximate minimizer of order $j$ in the sense of
(14.1.9) for all small radii.

The measure $\varphi^\delta_{w,j}$ is `Optimization.compositeTaylorMeasure Df Dc h j δ T`, the
measure of the data themselves. The proof uses
`Optimization.compositeTaylorDecrement_le_of_compositeRegularizedModel_le`. -/
theorem exists_radius_of_isMinOn_compositeRegularizedModel_zero (hLip : HasLipschitzConst h Lh)
    (hh : IsSubadditive h) (h0 : h 0 = 0) (hσ : 0 ≤ σ) {T : Set E} (hT0 : (0 : E) ∈ T)
    (hmin : IsMinOn (compositeRegularizedModel Df Dc h p σ) T 0) {j : ℕ} (hjp : j ≤ p) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ₀, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ δ, 0 ≤ δ → δ ≤ δ₀ →
      compositeTaylorMeasure Df Dc h j δ T ≤ ε * δ ^ j / j ! := by
  set K := ∑ ℓ ∈ Finset.Icc (j + 1) p, (‖Df ℓ‖ + Lh * ‖Dc ℓ‖) / (ℓ ! : ℝ) +
    σ / ((p + 1)! : ℝ) with hK
  have hLh := hLip.nonneg
  have hK0 : 0 ≤ K := by positivity
  have hf : (0 : ℝ) < (j ! : ℝ) := by positivity
  refine ⟨min 1 (ε / ((j ! : ℝ) * (K + 1))), lt_min one_pos (by positivity), min_le_left _ _,
    fun δ hδ0 hδ => ?_⟩
  have hδ1 : δ ≤ 1 := hδ.trans (min_le_left _ _)
  have hδε : δ ≤ ε / ((j ! : ℝ) * (K + 1)) := hδ.trans (min_le_right _ _)
  refine decrementMeasure_le ⟨0, mem_closedBall_self hδ0, hT0⟩ fun d hd => ?_
  have hdδ : ‖d‖ ≤ δ := mem_closedBall_zero_iff.1 hd.1
  have hpowle : ∀ ℓ, j + 1 ≤ ℓ → ‖d‖ ^ ℓ ≤ δ ^ (j + 1) := fun ℓ hℓ =>
    (pow_le_pow_left₀ (norm_nonneg _) hdδ ℓ).trans (pow_le_pow_of_le_one hδ0 hδ1 hℓ)
  have hb := compositeTaylorDecrement_le_of_compositeRegularizedModel_le hLip hh h0 hjp
    (isMinOn_iff.1 hmin d hd.2)
  have hsum : ∑ ℓ ∈ Finset.Icc (j + 1) p, (‖Df ℓ‖ + Lh * ‖Dc ℓ‖) * ‖d‖ ^ ℓ / ℓ ! +
      σ / ((p + 1)! : ℝ) * ‖d‖ ^ (p + 1) ≤ K * δ ^ (j + 1) := by
    rw [hK, add_mul, sum_mul]
    refine add_le_add (sum_le_sum fun ℓ hℓ => ?_) ?_
    · have ha : 0 ≤ (‖Df ℓ‖ + Lh * ‖Dc ℓ‖) / (ℓ ! : ℝ) := by positivity
      calc (‖Df ℓ‖ + Lh * ‖Dc ℓ‖) * ‖d‖ ^ ℓ / (ℓ ! : ℝ)
          = (‖Df ℓ‖ + Lh * ‖Dc ℓ‖) / (ℓ ! : ℝ) * ‖d‖ ^ ℓ := by ring
        _ ≤ (‖Df ℓ‖ + Lh * ‖Dc ℓ‖) / (ℓ ! : ℝ) * δ ^ (j + 1) :=
          mul_le_mul_of_nonneg_left (hpowle ℓ (Finset.mem_Icc.1 hℓ).1) ha
    · gcongr
      exact hpowle (p + 1) (by omega)
  have hKδ : K * δ ≤ ε / j ! := by
    calc K * δ ≤ (K + 1) * δ := by nlinarith
      _ ≤ (K + 1) * (ε / ((j ! : ℝ) * (K + 1))) := by gcongr
      _ = ε / j ! := by field_simp
  calc compositeTaylorDecrement Df Dc h j d ≤ K * δ ^ (j + 1) := hb.trans hsum
    _ = K * δ * δ ^ j := by ring
    _ ≤ ε / j ! * δ ^ j := by gcongr
    _ = ε * δ ^ j / j ! := by ring

/-- If the data $D$ are symmetric up to order $p$ and $i \le p$, then the $i$-th derivative at $0$
of the regularized model $m(s) = T_p(s) + \frac{\sigma}{(p+1)!} \|s\|^{p+1}$ is $D_i$. The
reason is that the term $\|s\|^{p+1}$ is flat to order $p$ at $0$. -/
theorem ftaylorSeries_regularizedModel_zero (hD : Df.IsSymm p) {i : ℕ} (hi : i ≤ p) :
    ftaylorSeries ℝ (regularizedModel Df p σ) 0 i = Df i := by
  have hlt : ((i : ℕ) : ℝ) < ((p + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_of_le hi
  change iteratedFDeriv ℝ i (regularizedModel Df p σ) 0 = Df i
  rw [iteratedFDeriv_regularizedModel (Or.inl hi), NormPowIteratedFDeriv.norm_pow_eq_normRpow,
    iteratedFDeriv_normRpow_zero hlt, smul_zero, add_zero]
  exact FormalMultilinearSeries.iteratedFDeriv_taylorSum_zero hD hi

/-- **The composite model at the zero step**, which for $h = 0$ is (12.2.49) of
[cartis2022evaluation]. If $D_f$ and $D_c$ are symmetric up to order $p$ and $j \le p$, then the
decrement of order $j$ of the model at the step $0$ is the composite decrement of the data:
$$\Delta T_{\hat m,j}(0, d) = \Delta T_{w,j}(d) \qquad \text{for all } d \in E.$$

The symmetry of the data is `FormalMultilinearSeries.IsSymm`. -/
theorem compositeModelDecrement_zero_left (hDf : Df.IsSymm p) (hDc : Dc.IsSymm p) {j : ℕ}
    (hjp : j ≤ p) :
    compositeModelDecrement Df Dc h p σ j 0 = compositeTaylorDecrement Df Dc h j := by
  funext d
  rw [compositeModelDecrement_def, compositeTaylorDecrement, compositeTaylorDecrement,
    FormalMultilinearSeries.taylorSum_congr (D := ftaylorSeries ℝ (regularizedModel Df p σ) 0)
      (D' := Df) fun i hi => ftaylorSeries_regularizedModel_zero hDf (hi.trans hjp),
    FormalMultilinearSeries.taylorSum_congr (D := ftaylorSeries ℝ (Dc.taylorSum p) 0)
      (D' := Dc) fun i hi =>
        FormalMultilinearSeries.iteratedFDeriv_taylorSum_zero hDc (hi.trans hjp)]

/-- **Lemma 14.1.4, first part** of [cartis2022evaluation], with Lemma 14.1.1. Let $h$ be convex
with a Lipschitz constant, let $D_f$ and $D_c$ be symmetric up to order $p$ with $p \ge 1$, and
let $T \subseteq E$ be a convex set of feasible displacements with $0 \in T$. If $0$ is a local
minimizer of the composite model $\hat m$ on $T$, then
$$\Delta T_{w,1}(d) \le 0 \qquad \text{for every } d \in T.$$
So the first-order measure vanishes, and ARqpC cannot stop in Step 2 when $q = 1$.

The proof applies `Optimization.compositeTaylorDecrement_one_nonpos_of_isLocalMinOn` to the
model, whose first-order jet at $0$ is that of the data by
`Optimization.compositeModelDecrement_zero_left`. -/
theorem compositeTaylorDecrement_one_nonpos_of_isLocalMinOn_compositeRegularizedModel
    (hLip : HasLipschitzConst h Lh) (hconv : ConvexOn ℝ univ h) (hDf : Df.IsSymm p)
    (hDc : Dc.IsSymm p) (hp : 1 ≤ p) {T : Set E} (hT : Convex ℝ T) (hT0 : (0 : E) ∈ T)
    (hmin : IsLocalMinOn (compositeRegularizedModel Df Dc h p σ) T 0) {d : E} (hd : d ∈ T) :
    compositeTaylorDecrement Df Dc h 1 d ≤ 0 := by
  have hf : DifferentiableAt ℝ (regularizedModel Df p σ) 0 :=
    ((contDiff_regularizedModel (D := Df) (σ := σ)).differentiable
      (by exact_mod_cast (show p ≠ 0 by omega))) 0
  have hc : DifferentiableAt ℝ (Dc.taylorSum p) 0 :=
    (Dc.contDiff_taylorSum p (n := 1)).differentiable one_ne_zero 0
  have := compositeTaylorDecrement_one_nonpos_of_isLocalMinOn hT hT0 hf hc hconv hLip hmin
    (s := d) (by simpa using hd)
  rwa [← compositeModelDecrement_def, compositeModelDecrement_zero_left hDf hDc hp] at this

end Minimizer

/-! ### Existence of model minimizers -/

section Existence

variable {Df : FormalMultilinearSeries ℝ E ℝ} {Dc : FormalMultilinearSeries ℝ E F} {h : F → ℝ}
  {p : ℕ} {σ Lh : ℝ}

/-- **Coercivity of the composite model**, the remark after (14.1.14) of [cartis2022evaluation]. Let
$E$ be proper. If $\sigma > 0$ and $h$ has a Lipschitz constant, then $\hat m(s) \to \infty$ as
$\|s\| \to \infty$, because $T_{f,p} + h \circ T_{c,p}$ grows at most like $\|s\|^p$.

The limit is along the filter `Filter.cocompact E`. -/
theorem tendsto_compositeRegularizedModel_cocompact [ProperSpace E]
    (hLip : HasLipschitzConst h Lh) (hσ : 0 < σ) :
    Tendsto (compositeRegularizedModel Df Dc h p σ) (cocompact E) atTop := by
  set Kc := ∑ i ∈ Finset.Icc 1 p, ‖Dc i‖ / (i ! : ℝ)
  set K := ∑ i ∈ Finset.Icc 1 p, ‖Df i‖ / (i ! : ℝ) + Lh * Kc
  set c := σ / ((p + 1)! : ℝ)
  set A := Df 0 0 + h (Dc 0 0)
  have hc : 0 < c := by positivity
  have hLh := hLip.nonneg
  have hg : Tendsto (fun t : ℝ => A + (c * t - K)) atTop atTop :=
    tendsto_atTop_add_const_left _ _
      (tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop hc))
  have hev : ∀ᶠ t in atTop, 1 ≤ t ∧ K ≤ c * t :=
    (eventually_ge_atTop 1).and
      ((tendsto_id.const_mul_atTop hc).eventually (eventually_ge_atTop K))
  have hlow : ∀ᶠ s in cocompact E,
      A + (c * ‖s‖ - K) ≤ compositeRegularizedModel Df Dc h p σ s := by
    filter_upwards [tendsto_norm_cocompact_atTop.eventually hev] with s ⟨hs1, hsK⟩
    have hT := taylorSum_ge_of_one_le_norm Df p hs1
    have hC : ‖Dc.taylorSum p 0 - Dc.taylorSum p s‖ ≤ Kc * ‖s‖ ^ p := by
      refine (norm_taylorSum_zero_sub_le Dc p s).trans ?_
      rw [sum_mul]
      refine sum_le_sum fun i hi => ?_
      rw [div_mul_eq_mul_div, mul_div_assoc, mul_div_assoc]
      have : ‖s‖ ^ i ≤ ‖s‖ ^ p := pow_le_pow_right₀ hs1 (Finset.mem_Icc.1 hi).2
      gcongr
    rw [Dc.taylorSum_zero_right] at hC
    have hh : h (Dc 0 0) - Lh * (Kc * ‖s‖ ^ p) ≤ h (Dc.taylorSum p s) := by
      have := hLip.abs_sub_le (Dc 0 0) (Dc.taylorSum p s)
      have := (le_abs_self _).trans this
      nlinarith [mul_le_mul_of_nonneg_left hC hLh]
    have hsp : 1 ≤ ‖s‖ ^ p := one_le_pow₀ hs1
    have hpow : ‖s‖ ^ (p + 1) = ‖s‖ ^ p * ‖s‖ := pow_succ _ _
    have : c * ‖s‖ - K ≤ ‖s‖ ^ p * (c * ‖s‖ - K) := le_mul_of_one_le_left (by linarith) hsp
    rw [compositeRegularizedModel_def, regularizedModel_def, hpow]
    change A + (c * ‖s‖ - K) ≤ Df.taylorSum p s + c * (‖s‖ ^ p * ‖s‖) + h (Dc.taylorSum p s)
    nlinarith
  exact tendsto_atTop_mono' _ hlow (hg.comp tendsto_norm_cocompact_atTop)

/-- **Global minimizers of the composite model.** Let $E$ be finite-dimensional, $\sigma > 0$, and
let $h$ have a Lipschitz constant. If $T \subseteq E$ is closed and $0 \in T$, then the model
$\hat m$ has a global minimizer on $T$: there is $s \in T$ with $\hat m(s) \le \hat m(t)$ for
all $t \in T$.

The model is continuous and coercive
(`Optimization.tendsto_compositeRegularizedModel_cocompact`). -/
theorem exists_isMinOn_compositeRegularizedModel [FiniteDimensional ℝ E]
    (hLip : HasLipschitzConst h Lh) (hσ : 0 < σ) {T : Set E} (hT : IsClosed T)
    (hT0 : (0 : E) ∈ T) :
    ∃ s ∈ T, IsMinOn (compositeRegularizedModel Df Dc h p σ) T s := by
  have := FiniteDimensional.proper_real E
  refine (continuous_compositeRegularizedModel Df Dc h p σ hLip.continuous).continuousOn
    |>.exists_isMinOn' hT hT0 ?_
  exact Filter.Eventually.filter_mono inf_le_left
    ((tendsto_compositeRegularizedModel_cocompact hLip hσ).eventually
      (eventually_ge_atTop (compositeRegularizedModel Df Dc h p σ 0)))

end Existence

/-! ### One-step comparison of measures (Lemma 14.1.7) -/

section Step

variable {f : E → ℝ} {c : E → F} {h : F → ℝ} {p : ℕ} {σ Lf Lc Lh : ℝ} {C : Set E} {x s : E}

/-- A sum over $\{0, \dots, j\}$ is its term at $0$ plus the sum over $\{1, \dots, j\}$. -/
private theorem sum_range_succ_eq_add_sum_Icc (g : ℕ → ℝ) (j : ℕ) :
    ∑ i ∈ Finset.range (j + 1), g i = g 0 + ∑ i ∈ Finset.Icc 1 j, g i := by
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos j),
    ← Finset.Ico_add_one_right_eq_Icc]
  rfl

/-- **Smooth part of the one-step comparison, anchored form.** Let $C \subseteq E$ be convex, let
$f : E \to \mathbb{R}$ be $p$ times continuously differentiable at every point of $C$, and
suppose that $\|\nabla^p f(y) - \nabla^p f(x)\| \le L_f \|y - x\|$ for $y \in C$. Let
$x, x + s \in C$, $\sigma \ge 0$, $j \le p$ and $d \in E$. Let $m$ be the regularized model
built from the jet of $f$ at $x$. Then
$$\Delta T_{f,j}(x + s, d) \le \Delta T_{m,j}(s, d) + (L_f + \sigma) \sum_{\ell=1}^{j}
  \frac{\|d\|^\ell}{\ell!} \frac{\|s\|^{p-\ell+1}}{(p-\ell+1)!}.$$

This is `Optimization.taylorDecrement_le_add_of_regularizedModel` with $\nabla^p f$ only
Lipschitz with anchor $x$. The model $m$ is `Optimization.regularizedModel (ftaylorSeries ℝ f x)
p σ`. -/
theorem taylorDecrement_le_add_of_regularizedModel_anchored (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y)
    (hLf : ∀ y ∈ C, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f x‖ ≤ Lf * ‖y - x‖)
    (hx : x ∈ C) (hxs : x + s ∈ C) (hσ : 0 ≤ σ) {j : ℕ} (hjp : j ≤ p) (d : E) :
    (ftaylorSeries ℝ f (x + s)).taylorDecrement j d ≤
      (ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ f x) p σ) s).taylorDecrement j d +
        (Lf + σ) *
          ∑ ℓ ∈ Finset.Icc 1 j, ‖d‖ ^ ℓ / ℓ ! * (‖s‖ ^ (p - ℓ + 1) / ((p - ℓ + 1)! : ℝ)) := by
  rw [FormalMultilinearSeries.taylorDecrement_eq, FormalMultilinearSeries.taylorDecrement_eq,
    mul_sum]
  have key : ∑ ℓ ∈ Finset.Icc 1 j,
      ((ℓ ! : ℝ)⁻¹ * ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ f x) p σ) s ℓ
          (fun _ => d) - (ℓ ! : ℝ)⁻¹ * ftaylorSeries ℝ f (x + s) ℓ (fun _ => d)) ≤
      ∑ ℓ ∈ Finset.Icc 1 j,
        (Lf + σ) * (‖d‖ ^ ℓ / ℓ ! * (‖s‖ ^ (p - ℓ + 1) / ((p - ℓ + 1)! : ℝ))) := by
    refine sum_le_sum fun ℓ hℓ => ?_
    have hℓp : ℓ ≤ p := (Finset.mem_Icc.1 hℓ).2.trans hjp
    have hb := abs_iteratedFDeriv_apply_le_of_regularizedModel_anchored hC hf hLf hx hxs hσ hℓp d
    rw [abs_sub_comm] at hb
    have hfac : (0 : ℝ) ≤ (ℓ ! : ℝ)⁻¹ := by positivity
    calc (ℓ ! : ℝ)⁻¹ * ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ f x) p σ) s ℓ
            (fun _ => d) - (ℓ ! : ℝ)⁻¹ * ftaylorSeries ℝ f (x + s) ℓ (fun _ => d)
        = (ℓ ! : ℝ)⁻¹ * (iteratedFDeriv ℝ ℓ (regularizedModel (ftaylorSeries ℝ f x) p σ) s
            (fun _ => d) - iteratedFDeriv ℝ ℓ f (x + s) (fun _ => d)) := by
          simp only [ftaylorSeries]; ring
      _ ≤ (ℓ ! : ℝ)⁻¹ * ((Lf + σ) / ((p - ℓ + 1)! : ℝ) * ‖s‖ ^ (p - ℓ + 1) * ‖d‖ ^ ℓ) :=
          mul_le_mul_of_nonneg_left ((le_abs_self _).trans hb) hfac
      _ = (Lf + σ) * (‖d‖ ^ ℓ / ℓ ! * (‖s‖ ^ (p - ℓ + 1) / ((p - ℓ + 1)! : ℝ))) := by ring
  rw [sum_sub_distrib] at key
  linarith

/-- **Smooth part of the one-step comparison**, (12.2.53)–(12.2.56), (B.14.2) and (B.14.6) of
[cartis2022evaluation]. Let $C \subseteq E$ be convex, let $f : E \to \mathbb{R}$ be $p$ times
continuously differentiable at every point of $C$, with $\nabla^p f$ Lipschitz with constant
$L_f$ on $C$. Let $x, x + s \in C$, $\sigma \ge 0$, $j \le p$ and $d \in E$. Let $m$ be the
regularized model built from the jet of $f$ at $x$. Then the Taylor decrement of order $j$ of
$f$ at $x + s$ exceeds that of $m$ at $s$ by at most
$$(L_f + \sigma) \sum_{\ell=1}^{j} \frac{\|d\|^\ell}{\ell!}
  \frac{\|s\|^{p-\ell+1}}{(p-\ell+1)!}.$$

The model $m$ is `Optimization.regularizedModel (ftaylorSeries ℝ f x) p σ`. -/
theorem taylorDecrement_le_add_of_regularizedModel (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hLf : IteratedFDerivLipschitzOn f p Lf C)
    (hx : x ∈ C) (hxs : x + s ∈ C) (hσ : 0 ≤ σ) {j : ℕ} (hjp : j ≤ p) (d : E) :
    (ftaylorSeries ℝ f (x + s)).taylorDecrement j d ≤
      (ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ f x) p σ) s).taylorDecrement j d +
        (Lf + σ) *
          ∑ ℓ ∈ Finset.Icc 1 j, ‖d‖ ^ ℓ / ℓ ! * (‖s‖ ^ (p - ℓ + 1) / ((p - ℓ + 1)! : ℝ)) :=
  taylorDecrement_le_add_of_regularizedModel_anchored hC hf
    (fun y hy => iteratedFDerivLipschitzOn_iff.1 hLf y hy x hx) hx hxs hσ hjp d

/-- **One-step comparison of composite decrements, anchored form.** This is
`Optimization.compositeTaylorDecrement_le_of_step` with $\nabla^p f$ and $\nabla^p c$ only
Lipschitz with anchor $x$: $\|\nabla^p f(y) - \nabla^p f(x)\| \le L_f \|y - x\|$ and $\|\nabla^p
c(y) - \nabla^p c(x)\| \le L_c \|y - x\|$ for $y \in C$. Under these hypotheses, for
$x, x + s \in C$, $\sigma \ge 0$, $j \le p$ and $d \in E$,
$$\Delta T_{w,j}(x + s, d) \le \Delta T_{\hat m,j}(s, d) + (L_f + L_h L_c + \sigma)
  \sum_{\ell=1}^{j} \frac{\|d\|^\ell}{\ell!} \frac{\|s\|^{p-\ell+1}}{(p-\ell+1)!} + \frac{2 L_h
  L_c}{(p+1)!} \|s\|^{p+1}.$$
-/
theorem compositeTaylorDecrement_le_of_step_anchored (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hc : ∀ y ∈ C, ContDiffAt ℝ p c y)
    (hLf : ∀ y ∈ C, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f x‖ ≤ Lf * ‖y - x‖)
    (hLc : ∀ y ∈ C, ‖iteratedFDeriv ℝ p c y - iteratedFDeriv ℝ p c x‖ ≤ Lc * ‖y - x‖)
    (hLip : HasLipschitzConst h Lh) (hx : x ∈ C) (hxs : x + s ∈ C) (hσ : 0 ≤ σ) {j : ℕ}
    (hjp : j ≤ p) (d : E) :
    compositeTaylorDecrement (ftaylorSeries ℝ f (x + s)) (ftaylorSeries ℝ c (x + s)) h j d ≤
      compositeModelDecrement (ftaylorSeries ℝ f x) (ftaylorSeries ℝ c x) h p σ j s d +
        (Lf + Lh * Lc + σ) *
          ∑ ℓ ∈ Finset.Icc 1 j, ‖d‖ ^ ℓ / ℓ ! * (‖s‖ ^ (p - ℓ + 1) / ((p - ℓ + 1)! : ℝ)) +
        2 * Lh * Lc / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) := by
  have hLh := hLip.nonneg
  have hsmooth := taylorDecrement_le_add_of_regularizedModel_anchored hC hf hLf hx hxs hσ hjp d
  set Ssum := ∑ ℓ ∈ Finset.Icc 1 j, ‖d‖ ^ ℓ / ℓ ! * (‖s‖ ^ (p - ℓ + 1) / ((p - ℓ + 1)! : ℝ))
  -- (B.14.3): the values of `c` and of its Taylor polynomial at `x + s`
  have h1 : h (c (x + s)) - h ((ftaylorSeries ℝ c x).taylorSum p s) ≤
      Lh * (Lc / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1)) :=
    (le_abs_self _).trans ((hLip.abs_sub_le _ _).trans (mul_le_mul_of_nonneg_left
      (norm_sub_taylorPolynomial_le_of_lipschitzAnchored hC hc hLc hx hxs) hLh))
  -- (B.14.4): the Taylor polynomials of order `j` of `c` at `x + s` and of `T_{c,p}` at `s`
  set B := ftaylorSeries ℝ ((ftaylorSeries ℝ c x).taylorSum p) s
  set C' := ftaylorSeries ℝ c (x + s)
  have hdiff : ∀ i ≤ p, ‖B i - C' i‖ ≤ Lc / ((p - i + 1)! : ℝ) * ‖s‖ ^ (p - i + 1) :=
    fun i hi => by
      rw [norm_sub_rev]
      exact norm_iteratedFDeriv_sub_taylorPolynomial_le_of_lipschitzAnchored hC hc hLc hx hxs hi
  have h2 : h (B.taylorSum j d) - h (C'.taylorSum j d) ≤
      Lh * (Lc / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) + Lc * Ssum) := by
    have hn : ‖B.taylorSum j d - C'.taylorSum j d‖ ≤
        Lc / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) + Lc * Ssum := by
      rw [← FormalMultilinearSeries.taylorSum_sub]
      refine ((B - C').norm_taylorSum_le j d).trans ?_
      rw [sum_range_succ_eq_add_sum_Icc, mul_sum]
      refine add_le_add ?_ (sum_le_sum fun i hi => ?_)
      · simpa using hdiff 0 (Nat.zero_le _)
      · have hip : i ≤ p := (Finset.mem_Icc.1 hi).2.trans hjp
        calc ‖(B - C') i‖ * ‖d‖ ^ i / (i ! : ℝ)
            ≤ Lc / ((p - i + 1)! : ℝ) * ‖s‖ ^ (p - i + 1) * ‖d‖ ^ i / (i ! : ℝ) := by
              gcongr; exact hdiff i hip
          _ = Lc * (‖d‖ ^ i / i ! * (‖s‖ ^ (p - i + 1) / ((p - i + 1)! : ℝ))) := by ring
    exact (le_abs_self _).trans ((hLip.abs_sub_le _ _).trans
      (mul_le_mul_of_nonneg_left hn hLh))
  have hz : C'.taylorSum j 0 = c (x + s) := taylorPolynomial_zero_right c j (x + s)
  have hz' : B.taylorSum j 0 = (ftaylorSeries ℝ c x).taylorSum p s :=
    taylorPolynomial_zero_right _ j s
  rw [compositeTaylorDecrement_eq, compositeModelDecrement_def, compositeTaylorDecrement_eq, hz,
    hz']
  have e : Lh * (Lc / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1)) +
      Lh * (Lc / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) + Lc * Ssum) + (Lf + σ) * Ssum =
      (Lf + Lh * Lc + σ) * Ssum + 2 * Lh * Lc / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) := by ring
  linarith

/-- **One-step comparison of composite decrements**, the content of Lemma 14.1.7 of
[cartis2022evaluation], Appendix B, (B.14.1)–(B.14.6). Let $C \subseteq E$ be convex, and let
$f : E \to \mathbb{R}$ and $c : E \to F$ be $p$ times continuously differentiable at every point
of $C$, with $\nabla^p f$ Lipschitz with constant $L_f$ and $\nabla^p c$ Lipschitz with constant
$L_c$ on $C$. Let $h$ have Lipschitz constant $L_h$, and let $x, x + s \in C$, $\sigma \ge 0$,
$j \le p$ and $d \in E$. Let $\hat m$ be the composite model built from the jets of $f$ and $c$
at $x$. Then the composite decrement of $w = f + h \circ c$ at $x + s$ satisfies
$$\Delta T_{w,j}(x + s, d) \le \Delta T_{\hat m,j}(s, d) + (L_f + L_h L_c + \sigma)
  \sum_{\ell=1}^{j} \frac{\|d\|^\ell}{\ell!} \frac{\|s\|^{p-\ell+1}}{(p-\ell+1)!} + \frac{2 L_h
  L_c}{(p+1)!} \|s\|^{p+1}.$$

The factor $2$ on the last term comes from (B.14.3) and from the term $\ell = 0$ of (B.14.4),
which each contribute $L_h L_c \|s\|^{p+1} / (p+1)!$. The exponent of $\|s\|$ in (B.14.6) is
$p - \ell + 1$. -/
theorem compositeTaylorDecrement_le_of_step (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hc : ∀ y ∈ C, ContDiffAt ℝ p c y)
    (hLf : IteratedFDerivLipschitzOn f p Lf C) (hLc : IteratedFDerivLipschitzOn c p Lc C)
    (hLip : HasLipschitzConst h Lh) (hx : x ∈ C) (hxs : x + s ∈ C) (hσ : 0 ≤ σ) {j : ℕ}
    (hjp : j ≤ p) (d : E) :
    compositeTaylorDecrement (ftaylorSeries ℝ f (x + s)) (ftaylorSeries ℝ c (x + s)) h j d ≤
      compositeModelDecrement (ftaylorSeries ℝ f x) (ftaylorSeries ℝ c x) h p σ j s d +
        (Lf + Lh * Lc + σ) *
          ∑ ℓ ∈ Finset.Icc 1 j, ‖d‖ ^ ℓ / ℓ ! * (‖s‖ ^ (p - ℓ + 1) / ((p - ℓ + 1)! : ℝ)) +
        2 * Lh * Lc / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) :=
  compositeTaylorDecrement_le_of_step_anchored hC hf hc
    (fun y hy => iteratedFDerivLipschitzOn_iff.1 hLf y hy x hx)
    (fun y hy => iteratedFDerivLipschitzOn_iff.1 hLc y hy x hx) hLip hx hxs hσ hjp d

/-- **One-step comparison of composite measures, anchored form.** This is
`Optimization.compositeTaylorMeasure_le_of_step` with $\nabla^p f$ and $\nabla^p c$ only
Lipschitz with anchor $x$. Under the hypotheses of
`Optimization.compositeTaylorDecrement_le_of_step_anchored`, with $L_f, L_c \ge 0$, a set $S$ of
feasible displacements with $0 \in S$, and $\delta \ge 0$,
$$\varphi^\delta_{w,j}(x + s) \le \varphi^\delta_{\hat m,j}(s) + (L_f + L_h L_c + \sigma)
  \sum_{\ell=1}^{j} \frac{\delta^\ell}{\ell!} \frac{\|s\|^{p-\ell+1}}{(p-\ell+1)!} + \frac{2 L_h
  L_c}{(p+1)!} \|s\|^{p+1}.$$
-/
theorem compositeTaylorMeasure_le_of_step_anchored (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hc : ∀ y ∈ C, ContDiffAt ℝ p c y)
    (hLf : ∀ y ∈ C, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f x‖ ≤ Lf * ‖y - x‖)
    (hLc : ∀ y ∈ C, ‖iteratedFDeriv ℝ p c y - iteratedFDeriv ℝ p c x‖ ≤ Lc * ‖y - x‖)
    (hLip : HasLipschitzConst h Lh) (hLf0 : 0 ≤ Lf) (hLc0 : 0 ≤ Lc) (hx : x ∈ C)
    (hxs : x + s ∈ C) (hσ : 0 ≤ σ) {j : ℕ} (hjp : j ≤ p) {S : Set E} (hS0 : (0 : E) ∈ S)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    compositeTaylorMeasure (ftaylorSeries ℝ f (x + s)) (ftaylorSeries ℝ c (x + s)) h j δ S ≤
      compositeTaylorMeasure
          (ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ f x) p σ) s)
          (ftaylorSeries ℝ ((ftaylorSeries ℝ c x).taylorSum p) s) h j δ S +
        (Lf + Lh * Lc + σ) *
          ∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ / ℓ ! * (‖s‖ ^ (p - ℓ + 1) / ((p - ℓ + 1)! : ℝ)) +
        2 * Lh * Lc / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) := by
  have hK : 0 ≤ Lf + Lh * Lc + σ := by have := hLip.nonneg; positivity
  refine decrementMeasure_le ⟨0, mem_closedBall_self hδ, hS0⟩ fun d hd => ?_
  have hdδ : ‖d‖ ≤ δ := mem_closedBall_zero_iff.1 hd.1
  refine (compositeTaylorDecrement_le_of_step_anchored hC hf hc hLf hLc hLip hx hxs hσ hjp
    d).trans ?_
  refine add_le_add (add_le_add (compositeTaylorDecrement_le_compositeTaylorMeasure hLip hd) ?_)
    le_rfl
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun ℓ _ => ?_) hK
  gcongr

/-- **One-step comparison of composite measures**, Lemma 14.1.7 of [cartis2022evaluation] before the
Step-2 condition (14.1.13) is used. Assume the hypotheses of
`Optimization.compositeTaylorDecrement_le_of_step`, with $L_f, L_c \ge 0$, a set $S$ of feasible
displacements with $0 \in S$, and $\delta \ge 0$. Then
$$\varphi^\delta_{w,j}(x + s) \le \varphi^\delta_{\hat m,j}(s) + (L_f + L_h L_c + \sigma)
  \sum_{\ell=1}^{j} \frac{\delta^\ell}{\ell!} \frac{\|s\|^{p-\ell+1}}{(p-\ell+1)!} + \frac{2 L_h
  L_c}{(p+1)!} \|s\|^{p+1},$$
where both measures are suprema over $d \in S$ with $\|d\| \le \delta$.

The measure $\varphi^\delta_{w,j}(x + s)$ is `Optimization.compositeTaylorMeasure` of the jets
of $f$ and $c$ at $x + s$. The model measure $\varphi^\delta_{\hat m,j}(s)$ is
`Optimization.compositeTaylorMeasure` of the jets at $s$ of the regularized model built from the
jet of $f$ at $x$ and of the Taylor sum of the jet of $c$ at $x$. -/
theorem compositeTaylorMeasure_le_of_step (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hc : ∀ y ∈ C, ContDiffAt ℝ p c y)
    (hLf : IteratedFDerivLipschitzOn f p Lf C) (hLc : IteratedFDerivLipschitzOn c p Lc C)
    (hLip : HasLipschitzConst h Lh) (hLf0 : 0 ≤ Lf) (hLc0 : 0 ≤ Lc) (hx : x ∈ C)
    (hxs : x + s ∈ C) (hσ : 0 ≤ σ) {j : ℕ} (hjp : j ≤ p) {S : Set E} (hS0 : (0 : E) ∈ S)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    compositeTaylorMeasure (ftaylorSeries ℝ f (x + s)) (ftaylorSeries ℝ c (x + s)) h j δ S ≤
      compositeTaylorMeasure
          (ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ f x) p σ) s)
          (ftaylorSeries ℝ ((ftaylorSeries ℝ c x).taylorSum p) s) h j δ S +
        (Lf + Lh * Lc + σ) *
          ∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ / ℓ ! * (‖s‖ ^ (p - ℓ + 1) / ((p - ℓ + 1)! : ℝ)) +
        2 * Lh * Lc / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) :=
  compositeTaylorMeasure_le_of_step_anchored hC hf hc
    (fun y hy => iteratedFDerivLipschitzOn_iff.1 hLf y hy x hx)
    (fun y hy => iteratedFDerivLipschitzOn_iff.1 hLc y hy x hx) hLip hLf0 hLc0 hx hxs hσ hjp hS0 hδ

end Step

end Optimization

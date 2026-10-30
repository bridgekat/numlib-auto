import Numlib.Optimization.Optimality.Approximate
import Numlib.Analysis.Calculus.Gradient
import Numlib.Analysis.Calculus.LipschitzIteratedFDeriv
import Numlib.Analysis.SpecialFunctions.FactorialSum

/-!
# Inexact derivative data and Taylor decrements

Methods with *dynamic accuracy* ([cartis2022evaluation], §13.1.2 and §13.3) build their models from
inexact derivatives `\overline{∇^i_x f}(x)`. An inexact jet is just another
`D̄ : FormalMultilinearSeries ℝ E ℝ`; its distance to the exact jet `D` (typically
`ftaylorSeries ℝ f x`) is recorded order by order by `Optimization.JetApprox`. The book's error
model (13.1.2), `‖D̄_i - D_i‖ ≤ κ_{∇,i} h_{k,i}`, and the explicit one (13.3.4) with `κ_{∇,i} = 1`
are both `JetApprox D D̄ p (fun i => κ i * h i)`.

Everything is stated for arbitrary data `D D̄`, so the results also serve model-versus-model
comparisons. The inexact decrement `D̄.taylorDecrement` does not involve `D̄ 0`; function values
enter only through `taylorSum` ((13.1.4), (13.1.7), (13.3.11)).

## Main definitions

* `Optimization.JetApprox D D̄ p err`: `‖D̄_i - D_i‖ ≤ err i` for `1 ≤ i ≤ p`.

## Main results

* `Optimization.norm_le_of_jetApprox`: `‖D̄_i‖ ≤ ‖D_i‖ + err i` ((13.1.24), (13.1.63));
* `Optimization.abs_taylorDecrement_sub_le_of_jetApprox`: (13.1.3) and its `‖s‖ ≤ 1` form;
* `Optimization.abs_taylorDecrement_sub_le_of_stepAccuracy`: step-scaled accuracy
  ((13.1.9) ⇒ (13.1.10), (13.1.46) ⇒ (13.1.47));
* `Optimization.abs_taylorSum_sub_le_of_jetApprox`: model values ((13.1.4), (13.1.7)–(13.1.8),
  (13.3.11));
* `Optimization.taylorMeasure_le_add_of_jetApprox`: the exact measure from the inexact one
  ((13.1.6));
* `Optimization.taylorMeasure_le_of_inexact_certificate`: certification of approximate optimality
  from inexact data (the common core of Lemmas 13.1.7, 13.1.15, 13.3.3(i), 13.3.6(i)).
-/

open Set Metric Finset
open scoped Nat

namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Approximate jets -/

section JetApprox

variable {D D' Dbar : FormalMultilinearSeries ℝ E ℝ} {p p' : ℕ} {err err' : ℕ → ℝ}

/-- The inexact jet `Dbar` approximates `D` up to order `p` with errors `err`:
`‖Dbar_i - D_i‖ ≤ err i` for `1 ≤ i ≤ p` ([cartis2022evaluation], (13.1.2) with
`err i = κ_{∇,i} h_{k,i}`, (13.3.4) with `err i = h_{k,i}`). The values `D 0`, `Dbar 0` are not
constrained. -/
def JetApprox (D Dbar : FormalMultilinearSeries ℝ E ℝ) (p : ℕ) (err : ℕ → ℝ) : Prop :=
  ∀ i ∈ Finset.Icc 1 p, ‖Dbar i - D i‖ ≤ err i

/-- Unfolding lemma for `JetApprox`. -/
theorem jetApprox_iff :
    JetApprox D Dbar p err ↔ ∀ i ∈ Finset.Icc 1 p, ‖Dbar i - D i‖ ≤ err i := Iff.rfl

/-- Exact data approximate themselves with zero error. -/
theorem jetApprox_self (D : FormalMultilinearSeries ℝ E ℝ) (p : ℕ) : JetApprox D D p 0 :=
  fun i _ => by simp

/-- `JetApprox` is symmetric in the two jets. -/
theorem JetApprox.symm (h : JetApprox D Dbar p err) : JetApprox Dbar D p err :=
  fun i hi => norm_sub_rev (D i) (Dbar i) ▸ h i hi

/-- `JetApprox` is monotone in the errors. -/
theorem JetApprox.mono_err (h : JetApprox D Dbar p err)
    (herr : ∀ i ∈ Finset.Icc 1 p, err i ≤ err' i) : JetApprox D Dbar p err' :=
  fun i hi => (h i hi).trans (herr i hi)

/-- `JetApprox` up to order `p` implies it up to any lower order. -/
theorem JetApprox.mono (h : JetApprox D Dbar p err) (hp : p' ≤ p) : JetApprox D Dbar p' err :=
  fun i hi => h i (Icc_subset_Icc le_rfl hp hi)

/-- The errors of an approximate jet are nonnegative. -/
theorem JetApprox.nonneg (h : JetApprox D Dbar p err) {i : ℕ} (hi : i ∈ Finset.Icc 1 p) :
    0 ≤ err i :=
  (norm_nonneg _).trans (h i hi)

/-- **Norms of inexact derivatives** ([cartis2022evaluation], (13.1.24), (13.1.63)):
`‖Dbar_i‖ ≤ ‖D_i‖ + err i`. -/
theorem norm_le_of_jetApprox (h : JetApprox D Dbar p err) {i : ℕ} (hi : i ∈ Finset.Icc 1 p) :
    ‖Dbar i‖ ≤ ‖D i‖ + err i := by
  calc ‖Dbar i‖ = ‖D i + (Dbar i - D i)‖ := by rw [add_sub_cancel]
    _ ≤ ‖D i‖ + ‖Dbar i - D i‖ := norm_add_le _ _
    _ ≤ ‖D i‖ + err i := by gcongr; exact h i hi

/-- (13.1.24), (13.1.63) with the book's constants: if `‖D_i‖ ≤ L`,
`err i = κ_i h_i`, `0 ≤ κ_i ≤ κmax` and `0 ≤ h_i ≤ κh`, then `‖Dbar_i‖ ≤ L + κmax κh`. -/
theorem norm_le_add_mul_of_jetApprox {κ hh : ℕ → ℝ} {L κmax κh : ℝ}
    (h : JetApprox D Dbar p (fun i => κ i * hh i)) {i : ℕ} (hi : i ∈ Finset.Icc 1 p)
    (hD : ‖D i‖ ≤ L) (hκ : 0 ≤ κ i) (hκmax : κ i ≤ κmax) (hh0 : 0 ≤ hh i) (hhh : hh i ≤ κh) :
    ‖Dbar i‖ ≤ L + κmax * κh := by
  have := norm_le_of_jetApprox h hi
  have : κ i * hh i ≤ κmax * κh := mul_le_mul hκmax hhh hh0 (hκ.trans hκmax)
  linarith

/-- (13.1.24) for a jet of a function: if `∇^i f` is `L`-Lipschitz on an open set containing `x`
(`L ≥ 0`) and `Dbar` approximates `ftaylorSeries ℝ f x` up to order `i + 1`, then
`‖Dbar_{i+1}‖ ≤ L + err (i + 1)`. -/
theorem norm_le_of_jetApprox_of_lipschitz {f : E → ℝ} {x : E} {C : Set E} {L : ℝ} {i : ℕ}
    (h : JetApprox (ftaylorSeries ℝ f x) Dbar p err) (hi : i + 1 ≤ p) (hC : IsOpen C)
    (hL0 : 0 ≤ L) (hL : IteratedFDerivLipschitzOn f i L C) (hx : x ∈ C) :
    ‖Dbar (i + 1)‖ ≤ L + err (i + 1) := by
  have h1 := norm_le_of_jetApprox h (mem_Icc.2 ⟨Nat.le_add_left 1 i, hi⟩)
  have h2 : ‖ftaylorSeries ℝ f x (i + 1)‖ ≤ L :=
    norm_iteratedFDeriv_succ_le_of_lipschitzOn hC hL0 hL hx
  linarith

end JetApprox

/-! ### Decrements, model values and measures -/

section Bounds

variable {D Dbar : FormalMultilinearSeries ℝ E ℝ} {p j : ℕ} {err : ℕ → ℝ} {s : E}

/-- **(13.1.3)** If `JetApprox D Dbar p err` and `j ≤ p`, then
`|ΔT̄_j(s) - ΔT_j(s)| ≤ ∑_{i=1}^j err i ‖s‖^i / i!`. -/
theorem abs_taylorDecrement_sub_le_of_jetApprox (h : JetApprox D Dbar p err) (hj : j ≤ p)
    (s : E) :
    |Dbar.taylorDecrement j s - D.taylorDecrement j s| ≤
      ∑ i ∈ Finset.Icc 1 j, err i * ‖s‖ ^ i / i ! := by
  refine (Dbar.abs_taylorDecrement_sub_le D j s).trans (sum_le_sum fun i hi => ?_)
  gcongr
  exact h i (Icc_subset_Icc le_rfl hj hi)

/-- (13.1.3) in the shape of (13.1.6): if moreover `‖s‖ ≤ 1` and `0 ≤ err i ≤ e` for
`1 ≤ i ≤ j` (with `0 ≤ e`), then `|ΔT̄_j(s) - ΔT_j(s)| ≤ 2 e ‖s‖` (sum bound (A.34)); hence
`≤ 2 e`. -/
theorem abs_taylorDecrement_sub_le_two_mul_of_jetApprox {e : ℝ} (h : JetApprox D Dbar p err)
    (hj : j ≤ p) (hs : ‖s‖ ≤ 1) (he : ∀ i ∈ Finset.Icc 1 j, err i ≤ e) (he0 : 0 ≤ e) :
    |Dbar.taylorDecrement j s - D.taylorDecrement j s| ≤ 2 * e * ‖s‖ := by
  calc |Dbar.taylorDecrement j s - D.taylorDecrement j s|
      ≤ ∑ i ∈ Finset.Icc 1 j, err i * ‖s‖ ^ i / i ! :=
        abs_taylorDecrement_sub_le_of_jetApprox h hj s
    _ ≤ ∑ i ∈ Finset.Icc 1 j, e * (‖s‖ ^ i / i !) := by
        refine sum_le_sum fun i hi => ?_
        rw [mul_div_assoc]
        gcongr
        exact he i hi
    _ = e * ∑ i ∈ Finset.Icc 1 j, ‖s‖ ^ i / i ! := by rw [mul_sum]
    _ ≤ e * (2 * ‖s‖) := by gcongr; exact sum_pow_div_factorial_le_two_mul (norm_nonneg s) hs j
    _ = 2 * e * ‖s‖ := by ring

/-- **Step-scaled accuracy** ([cartis2022evaluation], (13.1.9) ⇒ (13.1.10), (13.1.46) ⇒ (13.1.47)).
If `JetApprox D Dbar r err` with `err i ≤ κ κs ‖s‖^{r-i+1}` for `1 ≤ i ≤ r` (`κ, κs ≥ 0`), then for
every `j ≤ r`, `|ΔT̄_j(s) - ΔT_j(s)| ≤ 2 κs κ ‖s‖^{r+1}` (each term is `κ κs ‖s‖^{r+1} / i!` and
`∑_{i=1}^j 1/i! ≤ 2`). -/
theorem abs_taylorDecrement_sub_le_of_stepAccuracy {r : ℕ} {κ κs : ℝ} (hκ : 0 ≤ κ)
    (hκs : 0 ≤ κs) (h : JetApprox D Dbar r err)
    (herr : ∀ i ∈ Finset.Icc 1 r, err i ≤ κ * κs * ‖s‖ ^ (r - i + 1)) (hj : j ≤ r) :
    |Dbar.taylorDecrement j s - D.taylorDecrement j s| ≤ 2 * κs * κ * ‖s‖ ^ (r + 1) := by
  calc |Dbar.taylorDecrement j s - D.taylorDecrement j s|
      ≤ ∑ i ∈ Finset.Icc 1 j, err i * ‖s‖ ^ i / i ! :=
        abs_taylorDecrement_sub_le_of_jetApprox h hj s
    _ ≤ ∑ i ∈ Finset.Icc 1 j, κ * κs * ‖s‖ ^ (r + 1) * ((1 : ℝ) ^ i / i !) := by
        refine sum_le_sum fun i hi => ?_
        have hir : i ≤ r := (mem_Icc.1 hi).2.trans hj
        have hpow : ‖s‖ ^ (r - i + 1) * ‖s‖ ^ i = ‖s‖ ^ (r + 1) := by
          rw [← pow_add]; congr 1; omega
        rw [one_pow, mul_one_div, ← hpow, ← mul_assoc]
        gcongr
        exact herr i (Icc_subset_Icc le_rfl hj hi)
    _ = κ * κs * ‖s‖ ^ (r + 1) * ∑ i ∈ Finset.Icc 1 j, (1 : ℝ) ^ i / i ! := by rw [mul_sum]
    _ ≤ κ * κs * ‖s‖ ^ (r + 1) * 2 := by
        gcongr
        simpa using sum_pow_div_factorial_le_two_mul zero_le_one le_rfl j
    _ = 2 * κs * κ * ‖s‖ ^ (r + 1) := by ring

/-- The difference of Taylor sums is the difference of values minus the difference of
decrements. -/
theorem taylorSum_sub_eq (D Dbar : FormalMultilinearSeries ℝ E ℝ) (j : ℕ) (s : E) :
    Dbar.taylorSum j s - D.taylorSum j s =
      (Dbar.taylorSum j 0 - D.taylorSum j 0) -
        (Dbar.taylorDecrement j s - D.taylorDecrement j s) := by
  simp only [FormalMultilinearSeries.taylorDecrement]
  ring

/-- **(13.1.4)** If `JetApprox D Dbar p err` and `j ≤ p`, then
`|T̄_j(s) - T_j(s)| ≤ |T̄_j(0) - T_j(0)| + ∑_{i=1}^j err i ‖s‖^i / i!` (`T_j(0)` is the zeroth
term, the function value). -/
theorem abs_taylorSum_sub_le_of_jetApprox (h : JetApprox D Dbar p err) (hj : j ≤ p) (s : E) :
    |Dbar.taylorSum j s - D.taylorSum j s| ≤
      |Dbar.taylorSum j 0 - D.taylorSum j 0| + ∑ i ∈ Finset.Icc 1 j, err i * ‖s‖ ^ i / i ! := by
  rw [taylorSum_sub_eq]
  exact (abs_sub _ _).trans (add_le_add le_rfl (abs_taylorDecrement_sub_le_of_jetApprox h hj s))

/-- **(13.1.7)–(13.1.8)**: with exact function values, the model error is the decrement error,
`T̄_j(s) - T_j(s) = -(ΔT̄_j(s) - ΔT_j(s))`. -/
theorem taylorSum_sub_eq_of_value_eq (h0 : Dbar.taylorSum j 0 = D.taylorSum j 0) (s : E) :
    Dbar.taylorSum j s - D.taylorSum j s =
      -(Dbar.taylorDecrement j s - D.taylorDecrement j s) := by
  rw [taylorSum_sub_eq, h0, sub_self, zero_sub]

/-- **(13.3.11)**: with inexact values `|T̄_j(0) - T_j(0)| ≤ h₀` and the step-scaled accuracy of
`abs_taylorDecrement_sub_le_of_stepAccuracy`, `|T̄_j(s) - T_j(s)| ≤ h₀ + 2 κs κ ‖s‖^{r+1}`. -/
theorem abs_taylorSum_sub_le_of_stepAccuracy {r : ℕ} {κ κs h₀ : ℝ} (hκ : 0 ≤ κ) (hκs : 0 ≤ κs)
    (h : JetApprox D Dbar r err)
    (herr : ∀ i ∈ Finset.Icc 1 r, err i ≤ κ * κs * ‖s‖ ^ (r - i + 1)) (hj : j ≤ r)
    (h0 : |Dbar.taylorSum j 0 - D.taylorSum j 0| ≤ h₀) :
    |Dbar.taylorSum j s - D.taylorSum j s| ≤ h₀ + 2 * κs * κ * ‖s‖ ^ (r + 1) := by
  rw [taylorSum_sub_eq]
  exact (abs_sub _ _).trans
    (add_le_add h0 (abs_taylorDecrement_sub_le_of_stepAccuracy hκ hκs h herr hj))

variable {δ : ℝ} {S : Set E}

/-- **(13.1.6)** If `JetApprox D Dbar q err`, `j ≤ q`, `δ ≥ 0` and `0 ∈ S`, then
`φ^δ_j(D) ≤ φ^δ_j(Dbar) + ∑_{i=1}^j err i δ^i / i!`. (Both directions hold by symmetry of
`JetApprox`.) -/
theorem taylorMeasure_le_add_of_jetApprox {q : ℕ} (h : JetApprox D Dbar q err) (hj : j ≤ q)
    (h0 : (0 : E) ∈ S) (hδ : 0 ≤ δ) :
    taylorMeasure D j δ S ≤
      taylorMeasure Dbar j δ S + ∑ i ∈ Finset.Icc 1 j, err i * δ ^ i / i ! := by
  have habs := abs_taylorMeasure_sub_le D Dbar j h0 hδ
  have hsum : ∑ i ∈ Finset.Icc 1 j, ‖D i - Dbar i‖ * δ ^ i / i ! ≤
      ∑ i ∈ Finset.Icc 1 j, err i * δ ^ i / i ! := by
    refine sum_le_sum fun i hi => ?_
    rw [norm_sub_rev]
    gcongr
    exact h i (Icc_subset_Icc le_rfl hj hi)
  linarith [le_abs_self (taylorMeasure D j δ S - taylorMeasure Dbar j δ S)]

/-- (13.1.6) with a uniform error: if moreover `δ ≤ 1`, `0 ≤ e` and `err i ≤ e` for
`1 ≤ i ≤ j`, then `φ^δ_j(D) ≤ φ^δ_j(Dbar) + 2 e δ` (hence `≤ φ^δ_j(Dbar) + 2 e`, the book's
`e = κ_{∇,max} h_{k,max}`). -/
theorem taylorMeasure_le_add_two_mul_of_jetApprox {q : ℕ} {e : ℝ} (h : JetApprox D Dbar q err)
    (hj : j ≤ q) (h0 : (0 : E) ∈ S) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (he : ∀ i ∈ Finset.Icc 1 j, err i ≤ e) (he0 : 0 ≤ e) :
    taylorMeasure D j δ S ≤ taylorMeasure Dbar j δ S + 2 * e * δ := by
  refine (taylorMeasure_le_add_of_jetApprox h hj h0 hδ).trans (add_le_add le_rfl ?_)
  calc ∑ i ∈ Finset.Icc 1 j, err i * δ ^ i / i ! ≤ ∑ i ∈ Finset.Icc 1 j, e * (δ ^ i / i !) := by
        refine sum_le_sum fun i hi => ?_
        rw [mul_div_assoc]
        gcongr
        exact he i hi
    _ = e * ∑ i ∈ Finset.Icc 1 j, δ ^ i / i ! := by rw [mul_sum]
    _ ≤ e * (2 * δ) := by gcongr; exact sum_pow_div_factorial_le_two_mul hδ hδ1 j
    _ = 2 * e * δ := by ring

/-- **Certification of approximate optimality from inexact data** (the common core of the
proofs of Lemmas 13.1.7, 13.1.15, 13.3.3(i) and 13.3.6(i) of [cartis2022evaluation]). Let
`JetApprox D Dbar q err`, `j ≤ q`, `δ ≥ 0`, `0 ∈ S`, `ς > 0`, and let `d` satisfy
`ς φ^δ_j(Dbar) ≤ ΔT̄_j(d) ≤ ς ε δ^j / j! / 2` (Step 1 found no significant inexact decrease at
order `j`), where the data are accurate enough at that radius:
`∑_{i=1}^j err i δ^i / i! ≤ ε δ^j / j! / 2`. Then the exact measure satisfies
`φ^δ_j(D) ≤ ε δ^j / j!` ((12.1.25) at order `j`). (No bound `δ ≤ 1`, `ς ≤ 1`, `ε ≥ 0` or
`‖d‖ ≤ δ` is needed.) -/
theorem taylorMeasure_le_of_inexact_certificate {q : ℕ} {ς ε : ℝ} {d : E}
    (h : JetApprox D Dbar q err) (hj : j ≤ q) (h0 : (0 : E) ∈ S) (hδ : 0 ≤ δ) (hς : 0 < ς)
    (hφ : ς * taylorMeasure Dbar j δ S ≤ Dbar.taylorDecrement j d)
    (hd : Dbar.taylorDecrement j d ≤ ς * ε * δ ^ j / j ! / 2)
    (hacc : ∑ i ∈ Finset.Icc 1 j, err i * δ ^ i / i ! ≤ ε * δ ^ j / j ! / 2) :
    taylorMeasure D j δ S ≤ ε * δ ^ j / j ! := by
  have h1 := taylorMeasure_le_add_of_jetApprox h hj h0 hδ
  have h2 : taylorMeasure Dbar j δ S ≤ ε * δ ^ j / j ! / 2 := by
    refine le_of_mul_le_mul_left ?_ hς
    calc ς * taylorMeasure Dbar j δ S ≤ ς * ε * δ ^ j / j ! / 2 := hφ.trans hd
      _ = ς * (ε * δ ^ j / j ! / 2) := by ring
  linarith

/-- **Uniform-error certificate** (the form used in Lemmas 13.1.7 and 13.1.15 of
[cartis2022evaluation]): if `JetApprox D Dbar q err`, `1 ≤ j ≤ q`, `0 ≤ δ ≤ 1`, `ς > 0`,
`err i ≤ e` for `1 ≤ i ≤ j` with `e ≤ ε δ^j / (4 j!)`, and Step 1 found
`ς φ^δ_j(Dbar) ≤ ΔT̄_j(d) ≤ ς ε δ^j / j! / 2`, then `φ^δ_j(D) ≤ ε δ^j / j!`. -/
theorem taylorMeasure_le_of_inexact_certificate_uniform {q : ℕ} {ς ε e : ℝ} {d : E}
    (h : JetApprox D Dbar q err) (hj : j ∈ Finset.Icc 1 q) (h0 : (0 : E) ∈ S) (hδ : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hς : 0 < ς)
    (hφ : ς * taylorMeasure Dbar j δ S ≤ Dbar.taylorDecrement j d)
    (hd : Dbar.taylorDecrement j d ≤ ς * ε * δ ^ j / j ! / 2)
    (he : ∀ i ∈ Finset.Icc 1 j, err i ≤ e) (heε : e ≤ ε * δ ^ j / (4 * j !)) :
    taylorMeasure D j δ S ≤ ε * δ ^ j / j ! := by
  obtain ⟨hj1, hjq⟩ := mem_Icc.1 hj
  have he0 : 0 ≤ e := (h.nonneg (mem_Icc.2 ⟨le_rfl, hj1.trans hjq⟩)).trans
    (he 1 (mem_Icc.2 ⟨le_rfl, hj1⟩))
  refine taylorMeasure_le_of_inexact_certificate h hjq h0 hδ hς hφ hd ?_
  calc ∑ i ∈ Finset.Icc 1 j, err i * δ ^ i / i ! ≤ ∑ i ∈ Finset.Icc 1 j, e * (δ ^ i / i !) := by
        refine sum_le_sum fun i hi => ?_
        rw [mul_div_assoc]
        gcongr
        exact he i hi
    _ = e * ∑ i ∈ Finset.Icc 1 j, δ ^ i / i ! := by rw [mul_sum]
    _ ≤ e * (2 * δ) := by gcongr; exact sum_pow_div_factorial_le_two_mul hδ hδ1 j
    _ ≤ e * 2 := by gcongr; linarith
    _ ≤ ε * δ ^ j / (4 * j !) * 2 := by gcongr
    _ = ε * δ ^ j / j ! / 2 := by field_simp; ring

end Bounds

/-! ### Jets with a replaced first- or second-order term -/

section Jets

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

open scoped RealInnerProductSpace

/-- The jet `D` with its first-order term replaced by the linear form `⟪v, ·⟫` (an approximate
gradient `v`). -/
noncomputable def gradientJet (D : FormalMultilinearSeries ℝ V ℝ) (v : V) :
    FormalMultilinearSeries ℝ V ℝ :=
  fun i => match i with
  | 1 => (continuousMultilinearCurryFin1 ℝ V ℝ).symm (innerSL ℝ v)
  | i => D i

@[simp]
theorem gradientJet_apply_one (D : FormalMultilinearSeries ℝ V ℝ) (v : V) (m : Fin 1 → V) :
    gradientJet D v 1 m = ⟪v, m 0⟫ := by
  simp [gradientJet]

theorem gradientJet_apply_of_ne (D : FormalMultilinearSeries ℝ V ℝ) (v : V) {i : ℕ}
    (hi : i ≠ 1) : gradientJet D v i = D i := by
  match i, hi with
  | 0, _ => rfl
  | _ + 2, _ => rfl

/-- The bilinear form `(u, w) ↦ ⟪u, A w⟫` of an operator `A`, as a continuous multilinear map. -/
noncomputable def bilinearOfOperator (A : V →L[ℝ] V) : V [×2]→L[ℝ] ℝ :=
  (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => V) ℝ).symm
    ((↑(continuousMultilinearCurryFin1 ℝ V ℝ).symm : (V →L[ℝ] ℝ) →L[ℝ] V [×1]→L[ℝ] ℝ).comp
      ((ContinuousLinearMap.compL ℝ V V ℝ).flip A ∘L innerSL ℝ))

@[simp]
theorem bilinearOfOperator_apply (A : V →L[ℝ] V) (m : Fin 2 → V) :
    bilinearOfOperator A m = ⟪m 0, A (m 1)⟫ := by
  simp [bilinearOfOperator]
  rfl

/-- `‖(u, w) ↦ ⟪u, A w⟫‖ ≤ ‖A‖`. -/
theorem norm_bilinearOfOperator_le (A : V →L[ℝ] V) : ‖bilinearOfOperator A‖ ≤ ‖A‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) fun m => ?_
  rw [bilinearOfOperator_apply, Real.norm_eq_abs, Fin.prod_univ_two]
  calc |⟪m 0, A (m 1)⟫| ≤ ‖m 0‖ * ‖A (m 1)‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖m 0‖ * (‖A‖ * ‖m 1‖) := by gcongr; exact A.le_opNorm _
    _ = ‖A‖ * (‖m 0‖ * ‖m 1‖) := by ring

/-- The jet `D` with its second-order term replaced by the bilinear form of an operator `A` (an
approximate Hessian). -/
noncomputable def hessianJet (D : FormalMultilinearSeries ℝ V ℝ) (A : V →L[ℝ] V) :
    FormalMultilinearSeries ℝ V ℝ :=
  fun i => match i with
  | 2 => bilinearOfOperator A
  | i => D i

@[simp]
theorem hessianJet_apply_two (D : FormalMultilinearSeries ℝ V ℝ) (A : V →L[ℝ] V)
    (m : Fin 2 → V) : hessianJet D A 2 m = ⟪m 0, A (m 1)⟫ := by
  simp [hessianJet]

theorem hessianJet_apply_of_ne (D : FormalMultilinearSeries ℝ V ℝ) (A : V →L[ℝ] V) {i : ℕ}
    (hi : i ≠ 2) : hessianJet D A i = D i := by
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | _ + 3, _ => rfl

variable [CompleteSpace V]

/-- An approximate gradient within `c` of `∇f(x)` gives a jet approximating the Taylor jet of `f`
at `x` to order `1` with error `c` ((13.1.2)). -/
theorem jetApprox_gradientJet {f : V → ℝ} {x v : V} {c : ℝ} (hv : ‖v - gradient f x‖ ≤ c) :
    JetApprox (ftaylorSeries ℝ f x) (gradientJet (ftaylorSeries ℝ f x) v) 1
      (fun _ => c) := by
  intro i hi
  obtain rfl : i = 1 := by simpa using hi
  have : gradientJet (ftaylorSeries ℝ f x) v 1 - ftaylorSeries ℝ f x 1 =
      (continuousMultilinearCurryFin1 ℝ V ℝ).symm (innerSL ℝ (v - gradient f x)) := by
    change (continuousMultilinearCurryFin1 ℝ V ℝ).symm (innerSL ℝ v) - iteratedFDeriv ℝ 1 f x = _
    ext m
    rw [sub_apply, iteratedFDeriv_one_apply, fderiv_eq_innerSL_gradient]
    simp
  rw [this, LinearIsometryEquiv.norm_map, innerSL_apply_norm]
  exact hv

/-- An approximate Hessian within `c` of `∇²f(x)` (for `f` `C²` at `x`) gives a jet approximating
the Taylor jet of `f` at `x` to order `2` with errors `0` at order `1` and `c` at order `2`. -/
theorem jetApprox_hessianJet {f : V → ℝ} {x : V} (hf : ContDiffAt ℝ 2 f x) {A : V →L[ℝ] V}
    {c : ℝ} (hA : ‖A - hessianOperator f x‖ ≤ c) :
    JetApprox (ftaylorSeries ℝ f x) (hessianJet (ftaylorSeries ℝ f x) A) 2
      (fun i => if i = 2 then c else 0) := by
  intro i hi
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hi
  rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl
  · rw [hessianJet_apply_of_ne _ _ (by norm_num), sub_self, norm_zero]
    simp
  · have : hessianJet (ftaylorSeries ℝ f x) A 2 - ftaylorSeries ℝ f x 2 =
        bilinearOfOperator (A - hessianOperator f x) := by
      ext m
      have hm : m = ![m 0, m 1] := by ext j; fin_cases j <;> rfl
      simp only [sub_apply, hessianJet_apply_two,
        bilinearOfOperator_apply, inner_sub_right, ftaylorSeries]
      rw [hm, ← inner_hessianOperator_apply hf]
      rfl
    rw [this]
    simpa using (norm_bilinearOfOperator_le _).trans hA

end Jets

end Optimization

import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.Analysis.Calculus.MultivariateTaylor.LinearComp
import Numlib.Analysis.Calculus.MultivariateTaylor.VectorRemainder
import Numlib.Optimization.ModelBased.HighOrder.ARqp
import Numlib.Optimization.ModelBased.HighOrderStep
import Numlib.Optimization.Complexity.SlowExampleARp
import Numlib.Optimization.Optimality.CurveConditions
import NumlibSurface.CartisGouldToint.Chapter12.Section02

/-!
# Cartis–Gould–Toint §14.1: Composite optimization problems

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §14.1: the composite problem
`min_x w(x) = f(x) + h(c(x))` (14.1.1) with smooth `f : ℝⁿ → ℝ`, `c : ℝⁿ → ℝᵐ` and a Lipschitz,
subadditive, possibly nonsmooth `h : ℝᵐ → ℝ`, its high-order measures, and the
adaptive-regularization algorithm ARqpC.

The generalized Taylor model `T_{w,j}(x, s) = T_{f,j}(x, s) + h(T_{c,j}(x, s))` (14.1.5), its
decrement and the measure `φ^δ_{w,j}(x)` (14.1.6) are the backbone
`Optimization.compositeTaylorDecrement` and `Optimization.compositeTaylorMeasure` of the jets
`ftaylorSeries ℝ f x`, `ftaylorSeries ℝ c x`; the regularized model `m̂_k` (14.1.11) and its
decrements (14.1.14) are `Optimization.compositeRegularizedModel` and
`Optimization.compositeModelDecrement`. ARqpC is the backbone ARqp run
`Optimization.IsARqpRun` with composite model data `Optimization.ARqpData.ofComposite`, whose
Step 2 is the detailed Step 2 `Optimization.IsDetailedStepOutput`. A feasible set `X` (closed,
`x₀ ∈ X`) is carried throughout: `X = univ` is ARqpC, a general `X` is ARqpC-SC of §14.2.

Assumption f.D1pL is `Chapter12.AssumptionD1pL f p Lf` (constants `L_{f,j} ≥ 1`), and the
maxima `L_f`, `L_c` of (14.1.3) are `Chapter12.finMax 1 Lf p` and `Chapter12.finMax 0 Lc p`.

## Main definitions

* `AssumptionCD1pL`, `AssumptionHLip`, `AssumptionHS0`, `AssumptionWBb` — c.D1pL, h.L, h.S0, w.Bb;
* `compositeLipschitzW`, `compositeLipschitzWp` — the constants `L_w` (14.1.3), `L_{w,p}`
  (14.1.27);
* `ARqpCParams`, `algorithm_14_1_2` (detailed Step 2), `algorithm_14_1_1` (ARqpC).

## Main results

* `lemma_14_1_1`, `example_14_1_1` — first-order necessary condition and its failure at order 2;
* `lemma_14_1_2` – `lemma_14_1_9`, `theorem_14_1_10_i`, `theorem_14_1_10_ii`;
* `exists_isARqpCRun` — ARqpC(-SC) runs exist; `algorithm_14_1_1.radius_policy` — every run
  satisfies the radius policy (14.1.28) (Lemma 14.1.3 for every output of Algorithm 14.1.2).
* `algorithm_14_1_2_of_isMinOn` — for `q = 1` and convex `h`, `X`, global model minimizers are
  outputs of Algorithm 14.1.2;
* `corollary_14_1_11` — sharpness of the bound of Theorem 14.1.10 (1).

## Deviations from the book

* Lemma 14.1.1 needs neither h.S0 nor global minimality nor continuity of the derivatives: a
  local minimizer and differentiability at `x⋆` suffice.
* c.D1pL is stated with componentwise constants as printed; the vector-valued derivatives then
  have constants `√m L_{c,j}`, and (14.1.2) reads `‖∇^j c(x)‖ ≤ √m L_{c,j-1}` (the book drops the
  `√m`).
* Lemma 14.1.3: the radius lower bound is also needed (and holds) for `j = 1` when `h` (or `X`)
  is nonconvex; the book lists only `j ∈ [2 : q]`. The bound is
  `δ_{s,j} ≥ κ_δ(σ) ε_j` for `j ∈ J = {j ≥ 2} ∪ ({1} if h or X nonconvex)` and `δ_{s,j} = 1`
  otherwise.
* Lemma 14.1.7: with `ς < 1` the printed factor `(1 - θ)` is wrong; Step 1 only certifies
  `φ_{w,j} > ς ε_j δ^j/j!` and the factor is `(ς - θ)` (assuming `θ < ς`). The `‖s_k‖^{p+1}`
  term carries a factor `2`. The inequality is strict, and h.S0 is not needed.
* Lemmas 14.1.4 and 14.1.6: only the smoothness and Lipschitz properties actually used (`f`, `c`
  of class `C^p`; f.DpL, c.DpL, h.L) are assumed.
* Lemma 14.1.9 and Theorem 14.1.10, part 2: the minimum `min_j ε_j^{j+1}` may be replaced by any
  positive lower bound `m_ε`; the decrease is stated for the order `j` produced by Lemma 14.1.8.
* Lemma 14.1.8: the second case of (14.1.31) misses the factor `ε_j^{(j+1)/(p+1)}` (derived in
  Appendix B); `(1 - θ)` becomes `(ς - θ)`.
* Lemma 14.1.9: `L_{f,p}` and `f` read `L_{w,p}` and `w`; the decrease holds at successful
  iterations not followed by termination (as for Lemma 12.2.13).
* Theorem 14.1.10: `3j!` in the constants reads `3q!`; `(1 - θ)` becomes `(ς - θ)`. The radius
  policies the book assumes ("suppose that the ARqpC algorithm ensures …") are proved for every
  run; part 1 needs `δ_{0,1} = 1`.
* Corollary 14.1.11: the book's one-line proof ("take `w = |c|` with `c` the positive function of
  Theorem 12.2.15") does not check that the slow ARqp steps are admissible ARqpC steps for `|c|`.
  They are: since `|t| ≥ t`, the composite model lies above the smooth model and agrees with it at
  the slow step, where `T_{c,p}(x_k, s_k) = c(x_{k+1}) > 0`; and `c(x_k) ≥ |c'(x_k)|` makes the
  measure `φ^1_{w,1}(x_k) = min(c(x_k), |c'(x_k)|)` equal to `|c'(x_k)|`. The example `c` is the
  interpolant of Theorem 12.2.15 shifted to be `≥ 2`, lifted to `ℝ¹ → ℝ¹`; it works for every
  `σ₀` (the book fixes `σ₀ = p!`) and every `ε ∈ (0, 1]` (the book takes `ε ≤ ½`).
-/

open Set Metric
open scoped Nat

namespace CartisGouldToint.Chapter14

variable {n m : ℕ}

set_option hygiene false in
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

set_option hygiene false in
local notation "ℝᵐ" => EuclideanSpace ℝ (Fin m)

/-! ### Assumptions and constants -/

/-- **Assumption c.D1pL** of [cartis2022evaluation], §14.1.1: `c` is `p` times continuously
differentiable and, for `j ∈ [1 : p]`, the `j`-th derivative of each component `c_i` is Lipschitz
continuous with constant `L_{c,j} ≥ 0`. -/
structure AssumptionCD1pL (c : ℝⁿ → ℝᵐ) (p : ℕ) (Lc : ℕ → ℝ) : Prop where
  contDiff : ContDiff ℝ p c
  nonneg : ∀ j ∈ Finset.Icc 1 p, 0 ≤ Lc j
  lipschitz_component : ∀ i, ∀ j ∈ Finset.Icc 1 p,
    IteratedFDerivLipschitzOn (fun x => c x i) j (Lc j) univ

/-- **Assumption h.L** of [cartis2022evaluation], §14.1.1: `h` is Lipschitz continuous with
constant `L_{h,0} ≥ 0`: the backbone `Optimization.HasLipschitzConst`. -/
abbrev AssumptionHLip (h : ℝᵐ → ℝ) (Lh : ℝ) : Prop := Optimization.HasLipschitzConst h Lh

theorem assumptionHLip_iff {h : ℝᵐ → ℝ} {Lh : ℝ} :
    AssumptionHLip h Lh ↔ 0 ≤ Lh ∧ ∀ a b, |h a - h b| ≤ Lh * ‖a - b‖ :=
  ⟨fun hh => ⟨hh.nonneg, hh.abs_sub_le⟩, fun hh => ⟨hh.1, hh.2⟩⟩

/-- **Assumption h.S0** of [cartis2022evaluation], §14.1.1: `h` is subadditive and `h(0) = 0`
(the book's "in `ℝ`" means `ℝᵐ`). -/
def AssumptionHS0 (h : ℝᵐ → ℝ) : Prop := Optimization.IsSubadditive h ∧ h 0 = 0

/-- **Assumption w.Bb** of [cartis2022evaluation], §14.1.1: `w = f + h ∘ c ≥ w_low` (on the feasible
set `X`; `X = univ` in §14.1). -/
def AssumptionWBb (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (h : ℝᵐ → ℝ) (X : Set ℝⁿ) (wlow : ℝ) : Prop :=
  ∀ x ∈ X, wlow ≤ f x + h (c x)

theorem AssumptionHLip.hasLipschitzConst {h : ℝᵐ → ℝ} {Lh : ℝ} (hh : AssumptionHLip h Lh) :
    Optimization.HasLipschitzConst h Lh := hh

/-- (14.1.4): under h.L and h.S0, `|h(a)| ≤ L_{h,0} ‖a‖`. -/
theorem AssumptionHS0.abs_le {h : ℝᵐ → ℝ} {Lh : ℝ} (hS : AssumptionHS0 h)
    (hL : AssumptionHLip h Lh) (a : ℝᵐ) : |h a| ≤ Lh * ‖a‖ := by
  simpa [hS.2] using hL.abs_sub_le a 0

/-- Under c.D1pL, `∇^j c` is `√m L_{c,j}`-Lipschitz for `j ∈ [1 : p]`. -/
theorem AssumptionCD1pL.lipschitz {c : ℝⁿ → ℝᵐ} {p : ℕ} {Lc : ℕ → ℝ}
    (hc : AssumptionCD1pL c p Lc) {j : ℕ} (hj : j ∈ Finset.Icc 1 p) :
    IteratedFDerivLipschitzOn c j (Real.sqrt m * Lc j) univ :=
  iteratedFDerivLipschitzOn_of_forall_component
    (fun _ _ => hc.contDiff.contDiffAt.of_le (by exact_mod_cast (Finset.mem_Icc.1 hj).2))
    fun i => hc.lipschitz_component i j hj

/-- (14.1.2) under c.D1pL (with the factor `√m` of componentwise constants):
`‖∇^j c(x)‖ ≤ √m L_{c,j-1}` for `j ∈ [2 : p]`. -/
theorem AssumptionCD1pL.norm_iteratedFDeriv_le {c : ℝⁿ → ℝᵐ} {p : ℕ} {Lc : ℕ → ℝ}
    (hc : AssumptionCD1pL c p Lc) {j : ℕ} (hj : j ∈ Finset.Icc 2 p) (x : ℝⁿ) :
    ‖iteratedFDeriv ℝ j c x‖ ≤ Real.sqrt m * Lc (j - 1) := by
  obtain ⟨hj2, hjp⟩ := Finset.mem_Icc.1 hj
  have hj' : j - 1 ∈ Finset.Icc 1 p := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have h0 : 0 ≤ Real.sqrt m * Lc (j - 1) := by
    have := hc.nonneg (j - 1) hj'
    positivity
  have := norm_iteratedFDeriv_succ_le_of_lipschitzOn isOpen_univ h0 (hc.lipschitz hj')
    (mem_univ x)
  rwa [show j - 1 + 1 = j by omega] at this

/-- The constant `L_w = L_f + √m L_{h,0} L_c` of [cartis2022evaluation], (14.1.3), with
`L_f = max_{j ∈ [1 : p]} L_{f,j}` and `L_c = max_{j ∈ [1 : p]} L_{c,j}`. -/
noncomputable def compositeLipschitzW (Lf Lc : ℕ → ℝ) (Lh : ℝ) (p m : ℕ) : ℝ :=
  Chapter12.finMax 1 Lf p + Real.sqrt m * Lh * Chapter12.finMax 0 Lc p

/-- The constant `L_{w,p} = L_{f,p} + √m L_{h,0} L_{c,p}` of [cartis2022evaluation], (14.1.27). -/
noncomputable def compositeLipschitzWp (Lf Lc : ℕ → ℝ) (Lh : ℝ) (p m : ℕ) : ℝ :=
  Lf p + Real.sqrt m * Lh * Lc p

/-- `L_{w,p} ≤ L_w`. -/
theorem compositeLipschitzWp_le {Lf Lc : ℕ → ℝ} {Lh : ℝ} {p : ℕ} (hp : 1 ≤ p) (hLh : 0 ≤ Lh) :
    compositeLipschitzWp Lf Lc Lh p m ≤ compositeLipschitzW Lf Lc Lh p m := by
  have hp' : p ∈ Finset.Icc 1 p := Finset.mem_Icc.2 ⟨hp, le_rfl⟩
  unfold compositeLipschitzWp compositeLipschitzW
  have := Chapter12.le_finMax (b := 0) (u := Lc) hp'
  gcongr
  exact Chapter12.le_finMax hp'

/-! ### Lemma 14.1.1 and Example 14.1.1 -/

/-- **Lemma 14.1.1** of [cartis2022evaluation] (convex-composite first-order necessary
optimality). Let `f` and `c` be continuously differentiable, `h` convex with h.L, and `x⋆` a
global minimizer of `w = f + h ∘ c`. Then `0` is a global minimizer of
`s ↦ T_{w,1}(x⋆, s) = T_{f,1}(x⋆, s) + h(T_{c,1}(x⋆, s))`, and `φ^δ_{w,1}(x⋆) = 0` for all
`δ > 0`. (h.S0 is not needed; the backbone version
`Optimization.compositeTaylorDecrement_one_nonpos_of_isLocalMinOn` only needs a local minimizer
on a convex set and differentiability at `x⋆`.) -/
theorem lemma_14_1_1 {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {h : ℝᵐ → ℝ} {Lh : ℝ} {xs : ℝⁿ}
    (hf : ContDiff ℝ 1 f) (hc : ContDiff ℝ 1 c) (hL : AssumptionHLip h Lh)
    (hconv : ConvexOn ℝ univ h) (hmin : ∀ x, f xs + h (c xs) ≤ f x + h (c x)) :
    (∀ s, (ftaylorSeries ℝ f xs).taylorSum 1 0 + h ((ftaylorSeries ℝ c xs).taylorSum 1 0) ≤
      (ftaylorSeries ℝ f xs).taylorSum 1 s + h ((ftaylorSeries ℝ c xs).taylorSum 1 s)) ∧
    ∀ δ > 0, Optimization.compositeTaylorMeasure (ftaylorSeries ℝ f xs) (ftaylorSeries ℝ c xs)
      h 1 δ univ = 0 := by
  have hmin' : IsLocalMinOn (fun z => f z + h (c z)) univ xs :=
    (isMinOn_univ_iff.2 hmin).isLocalMinOn
  have hfd := hf.contDiffAt.differentiableAt one_ne_zero (x := xs)
  have hcd := hc.contDiffAt.differentiableAt one_ne_zero (x := xs)
  have hU : {d | xs + d ∈ (univ : Set ℝⁿ)} = univ := by ext; simp
  refine ⟨fun s => ?_, fun δ hδ => ?_⟩
  · have := Optimization.compositeTaylorDecrement_one_nonpos_of_isLocalMinOn convex_univ
      (mem_univ xs) hfd hcd hconv hL.hasLipschitzConst hmin' (s := s) (mem_univ _)
    rw [Optimization.compositeTaylorDecrement] at this
    linarith
  · have := Optimization.compositeTaylorMeasure_one_eq_zero_of_isLocalMinOn convex_univ
      (mem_univ xs) hfd hcd hconv hL.hasLipschitzConst hmin' hδ.le
    rwa [hU] at this

section Example

/-- The objective `f(x) = -(2/5) x` of Example 14.1.1. -/
noncomputable def example1411F : ℝ → ℝ := fun x => -(2 / 5) * x

/-- The inner function `c(x) = x - x² + 2x³` of Example 14.1.1. -/
noncomputable def example1411C : ℝ → ℝ := fun x => x - x ^ 2 + 2 * x ^ 3

private theorem icc_one_three : (Finset.Icc 1 3 : Finset ℕ) = {1, 2, 3} := by decide

private theorem icc_one_two : (Finset.Icc 1 2 : Finset ℕ) = {1, 2} := by decide

private theorem example1411F_taylor (s : ℝ) :
    (ftaylorSeries ℝ example1411F 0).taylorSum 2 s = -(2 / 5) * s := by
  have hcd : ContDiffAt ℝ (3 : ℕ) example1411F 0 := by unfold example1411F; fun_prop
  have := Optimization.taylorPolynomial_eq_of_poly (N := 3) (x := 0) (d := s)
    (a := fun i => if i = 1 then -(2 / 5) * s else 0) hcd
    (Filter.Eventually.of_forall fun t => by
      rw [icc_one_three]; simp [example1411F]; ring) (p := 2) (by norm_num)
  rw [← taylorPolynomial_eq_taylorSum, this, icc_one_two]
  simp [example1411F]

private theorem example1411C_taylor (s : ℝ) :
    (ftaylorSeries ℝ example1411C 0).taylorSum 2 s = s - s ^ 2 := by
  have hcd : ContDiffAt ℝ (3 : ℕ) example1411C 0 := by unfold example1411C; fun_prop
  have := Optimization.taylorPolynomial_eq_of_poly (N := 3) (x := 0) (d := s)
    (a := fun i => if i = 1 then s else if i = 2 then -s ^ 2 else 2 * s ^ 3) hcd
    (Filter.Eventually.of_forall fun t => by
      rw [icc_one_three]; simp [example1411C]; ring) (p := 2) (by norm_num)
  rw [← taylorPolynomial_eq_taylorSum, this, icc_one_two]
  simp [example1411C]
  ring

/-- The second-order composite decrement of Example 14.1.1:
`ΔT_{w,2}(0, d) = (2/5) d - |d - d²|`. -/
private theorem example1411_decrement (d : ℝ) :
    Optimization.compositeTaylorDecrement (ftaylorSeries ℝ example1411F 0)
      (ftaylorSeries ℝ example1411C 0) (fun a => |a|) 2 d = 2 / 5 * d - |d - d ^ 2| := by
  rw [Optimization.compositeTaylorDecrement, example1411F_taylor, example1411C_taylor,
    example1411F_taylor, example1411C_taylor]
  simp
  ring

/-- **Example 14.1.1** of [cartis2022evaluation] (`n = m = 1`, stated on `ℝ`): `f(x) = -(2/5) x`,
`c(x) = x - x² + 2x³`, `h = |·|` (convex, h.L with `L_{h,0} = 1`, h.S0). Then
(i) `x⋆ = 0` is a global minimizer of `w(x) = -(2/5) x + |x - x² + 2x³|`;
(ii) `T_{w,2}(0, s) = -(2/5) s + |s - s²|`, whose global minimum `-2/5 < w(0)` is attained at
`s = 1`;
(iii) `φ^1_{w,2}(0) = 2/5 > 0`;
(iv) `φ^δ_{w,2}(0) = 0` for every `δ ∈ (0, 3/5]` (the book: "smaller than ½, say").
So Lemma 14.1.1 does not extend to `q = 2`. -/
theorem example_14_1_1 :
    (∀ x, example1411F 0 + |example1411C 0| ≤ example1411F x + |example1411C x|) ∧
    (∀ s, (ftaylorSeries ℝ example1411F 0).taylorSum 2 s +
        |(ftaylorSeries ℝ example1411C 0).taylorSum 2 s| = -(2 / 5) * s + |s - s ^ 2|) ∧
    (∀ s : ℝ, -(2 / 5) ≤ -(2 / 5) * s + |s - s ^ 2|) ∧ -(2 / 5) * 1 + |(1 : ℝ) - 1 ^ 2| = -(2 / 5) ∧
    Optimization.compositeTaylorMeasure (ftaylorSeries ℝ example1411F 0)
      (ftaylorSeries ℝ example1411C 0) (fun a => |a|) 2 1 univ = 2 / 5 ∧
    ∀ δ ∈ Ioc (0 : ℝ) (3 / 5), Optimization.compositeTaylorMeasure
      (ftaylorSeries ℝ example1411F 0) (ftaylorSeries ℝ example1411C 0) (fun a => |a|) 2 δ
      univ = 0 := by
  refine ⟨fun x => ?_, fun s => by rw [example1411F_taylor, example1411C_taylor],
    fun s => ?_, by norm_num, ?_, fun δ hδ => ?_⟩
  · simp only [example1411F, example1411C]
    norm_num
    rcases le_or_gt 0 x with hx | hx
    · rw [abs_of_nonneg (by nlinarith [sq_nonneg (x - 1 / 4)])]
      nlinarith [sq_nonneg (x - 1 / 4), mul_nonneg hx (sq_nonneg (x - 1 / 4))]
    · rw [abs_of_neg (by nlinarith [sq_nonneg (x - 1 / 4)])]
      nlinarith [sq_nonneg (x - 1 / 4), mul_nonneg (neg_nonneg.2 hx.le) (sq_nonneg (x - 1 / 4))]
  · rcases le_or_gt s 0 with hs | hs
    · nlinarith [abs_nonneg (s - s ^ 2)]
    · rcases le_or_gt s 1 with hs1 | hs1
      · rw [abs_of_nonneg (by nlinarith)]; nlinarith
      · rw [abs_of_neg (by nlinarith)]; nlinarith
  · rw [Optimization.compositeTaylorMeasure_eq_sSup]
    refine IsGreatest.csSup_eq ⟨⟨1, ⟨by simp, mem_univ _⟩, by
      rw [example1411_decrement]; norm_num⟩, ?_⟩
    rintro _ ⟨d, ⟨hd, -⟩, rfl⟩
    rw [example1411_decrement]
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs, abs_le] at hd
    rcases le_or_gt d 0 with hd0 | hd0
    · nlinarith [abs_nonneg (d - d ^ 2)]
    · rw [abs_of_nonneg (by nlinarith)]; nlinarith
  · rw [Optimization.compositeTaylorMeasure_eq_sSup]
    refine IsGreatest.csSup_eq ⟨⟨0, ⟨mem_closedBall_self hδ.1.le, mem_univ _⟩, by
      rw [example1411_decrement]; norm_num⟩, ?_⟩
    rintro _ ⟨d, ⟨hd, -⟩, rfl⟩
    rw [example1411_decrement]
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs, abs_le] at hd
    rcases le_or_gt d 0 with hd0 | hd0
    · nlinarith [abs_nonneg (d - d ^ 2)]
    · rw [abs_of_nonneg (by nlinarith [hδ.2])]; nlinarith [hδ.2]

end Example


/-! ### The ARqpC algorithm (Algorithms 14.1.1 and 14.1.2) -/

/-- The constants of ARqpC ([cartis2022evaluation], Algorithm 14.1.1, Step 0): those of ARqp
(`Optimization.ARqpParams`: `σ₀`, `0 < η₁ ≤ η₂ < 1`, `0 < γ₁ < 1 < γ₂ ≤ γ₃`, `θ ∈ (0, 1)`,
`ς ∈ (0, 1]`) with `σ_min ∈ (0, σ₀]`. (The complexity analysis moreover needs `θ < ς`, imposed
where used.) -/
structure ARqpCParams extends Optimization.ARqpParams where
  σmin_pos : 0 < σmin

/-- The model data of ARqpC at the iterate `y` with weight `σ`: generalized Taylor decrements of
`w`, the model `m̂` (14.1.11) and its decrements (14.1.14), and the predicted decrease
`ΔT_{w,p}`. -/
noncomputable abbrev arqpcData (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (h : ℝᵐ → ℝ) (p : ℕ) (y : ℝⁿ)
    (σ : ℝ) : Optimization.ARqpData ℝⁿ :=
  Optimization.ARqpData.ofComposite (ftaylorSeries ℝ f y) (ftaylorSeries ℝ c y) h p σ

/-- The orders at which Step 2.4.3 of Algorithm 14.1.2 may halve the radius: `j ≥ 2`, and all
orders if `h` (or, for ARqpC-SC, the feasible set `X`) is not convex. (The book's algorithm uses
the *known* convexity; if it is unknown, the algorithm halves at order `1` as well, which is the
nonconvex case of the analysis: every statement below holds for that variant with the
nonconvex-case conclusions.) -/
def halvingSet (h : ℝᵐ → ℝ) (X : Set ℝⁿ) : Set ℕ :=
  {j | 2 ≤ j ∨ ¬ (ConvexOn ℝ univ h ∧ Convex ℝ X)}

/-- **Algorithm 14.1.2** of [cartis2022evaluation] (detailed Step 2 of ARqpC) as an output
predicate: `(s, δ_s)` is returned by some execution of Algorithm 14.1.2 for the model
`m̂ = compositeRegularizedModel (ftaylorSeries ℝ f x) (ftaylorSeries ℝ c x) h p σ` over the
feasible steps `{s | x + s ∈ X}` (displacements `{d | x + s + d ∈ X}`), with model decrements
(14.1.14) and halving set `halvingSet h X`. It is the backbone transition system
`Optimization.DetailedStepTrans`, whose `h = 0`, `J = {j ≥ 3}` instance is Algorithm 12.2.3. -/
def algorithm_14_1_2 (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (h : ℝᵐ → ℝ) (X : Set ℝⁿ) (p q : ℕ)
    (P : ARqpCParams) (ε : ℕ → ℝ) (σ : ℝ) (x s : ℝⁿ) (δs : ℕ → ℝ) : Prop :=
  Optimization.IsDetailedStepOutput
    (Optimization.compositeRegularizedModel (ftaylorSeries ℝ f x) (ftaylorSeries ℝ c x) h p σ)
    {s | x + s ∈ X} (fun s => {d | x + s + d ∈ X})
    (fun j s d => Optimization.compositeModelDecrement (ftaylorSeries ℝ f x)
      (ftaylorSeries ℝ c x) h p σ j s d) q P.ς P.θ ε (halvingSet h X) s δs

/-- The termination test of ARqpC at iteration `k` (Step 1 or Step 2). -/
abbrev arqpcStop (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (h : ℝᵐ → ℝ) (p q : ℕ) (P : ARqpCParams)
    (ε : ℕ → ℝ) (x s : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ : ℕ → ℕ → ℝ) (d : ℕ → ℕ → ℝⁿ) (k : ℕ) : Prop :=
  Optimization.IsARRun.Stop
    (Optimization.arqpStop₁ P.toARqpParams q ε (fun k => arqpcData f c h p (x k) (σ k)) δ d)
    (Optimization.arqpStop₂ (fun k => arqpcData f c h p (x k) (σ k)) s) k

/-- **Algorithm 14.1.1 (ARqpC)** of [cartis2022evaluation] (with a closed feasible set `X`: the
ARqpC-SC variant of §14.2; `X = univ` is ARqpC) as a run predicate on the iterates `x`, steps
`s`, weights `σ`, Step-1 radii `δ` and optimality displacements `d`, and Step-2 radii `δs` and
model displacements `dm`. Given `1 ≤ q ≤ p`, `ε ∈ (0, 1]^q`, `δ₀ ∈ (0, 1]^q`: the run is the
backbone ARqp run `Optimization.IsARqpRun` for `w = f + h ∘ c` with composite model data
(Step 1: (14.1.10); Step 2: (14.1.12)–(14.1.13), termination if `m̂_k(s_k) = m̂_k(0)`; Steps 3–4:
(14.1.15)–(14.1.16), radii `δ_{k+1} = δ_{s_k}` after success), and the Step-2 pair
`(s_k, δ_{s_k})` is an output of Algorithm 14.1.2 at every iteration reaching Step 2.
(Closedness of `X` is not part of the predicate: it is needed only for the existence of runs,
`exists_isARqpCRun`.) -/
structure algorithm_14_1_1 (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (h : ℝᵐ → ℝ) (X : Set ℝⁿ) (p q : ℕ)
    (P : ARqpCParams) (ε δ₀ : ℕ → ℝ) (x s : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ)
    (d dm : ℕ → ℕ → ℝⁿ) : Prop where
  one_le_q : 1 ≤ q
  q_le_p : q ≤ p
  ε_mem : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1
  δ₀_mem : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1
  /-- Steps 1–4: the ARqp run with composite model data. -/
  run : Optimization.IsARqpRun (fun y => f y + h (c y)) X P.toARqpParams q ε δ₀
    (fun k => arqpcData f c h p (x k) (σ k)) x s σ δ δs d dm
  /-- Step 2 is computed by Algorithm 14.1.2. -/
  detailed : ∀ k, (∀ i < k, ¬ arqpcStop f c h p q P ε x s σ δ d i) →
    ¬ Optimization.arqpStop₁ P.toARqpParams q ε (fun k => arqpcData f c h p (x k) (σ k)) δ d k →
    algorithm_14_1_2 f c h X p q P ε (σ k) (x k) (s k) (δs k)

/-! ### Lemmas 14.1.2 and 14.1.3: model decrease and existence of a step -/

section Step

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {h : ℝᵐ → ℝ} {p : ℕ} {Lf Lc : ℕ → ℝ} {Lh : ℝ}

/-- The jet bounds `‖∇^i f(x)‖ ≤ L_f`, `‖∇^i c(x)‖ ≤ √m L_c` for `i ∈ [2 : p]` used by the model
lemmas. -/
private theorem jet_bounds
    (hf : Chapter12.AssumptionD1pL f p Lf)
    (hc : AssumptionCD1pL c p Lc) (x : ℝⁿ) :
    (∀ i ∈ Finset.Icc 2 p, ‖ftaylorSeries ℝ f x i‖ ≤ Chapter12.finMax 1 Lf p) ∧
    (∀ i ∈ Finset.Icc 2 p, ‖ftaylorSeries ℝ c x i‖ ≤ Real.sqrt m * Chapter12.finMax 0 Lc p) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have hi' : i - 1 ∈ Finset.Icc 1 p := by
      have := Finset.mem_Icc.1 hi; exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
    exact (hf.norm_iteratedFDeriv_le hi x).trans (Chapter12.le_finMax hi')
  · have hi' : i - 1 ∈ Finset.Icc 1 p := by
      have := Finset.mem_Icc.1 hi; exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
    exact (hc.norm_iteratedFDeriv_le hi x).trans
      (mul_le_mul_of_nonneg_left (Chapter12.le_finMax hi') (Real.sqrt_nonneg _))

private theorem one_le_compositeLipschitzW
    (hf : Chapter12.AssumptionD1pL f p Lf)
    (hc : AssumptionCD1pL c p Lc) (hL : AssumptionHLip h Lh) (hp : 1 ≤ p) :
    1 ≤ compositeLipschitzW Lf Lc Lh p m := by
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 p := Finset.mem_Icc.2 ⟨le_rfl, hp⟩
  have hf1 := (hf.one_le 1 h1).trans (Chapter12.le_finMax (b := 1) (u := Lf) h1)
  have hc1 := (hc.nonneg 1 h1).trans (Chapter12.le_finMax (b := 0) (u := Lc) h1)
  have := hL.nonneg
  unfold compositeLipschitzW
  have : 0 ≤ Real.sqrt m * Lh * Chapter12.finMax 0 Lc p := by positivity
  linarith

/-- **Lemma 14.1.2** of [cartis2022evaluation] (relationship between the composite model and its
generalized Taylor decrements). Under f.D1pL, c.D1pL, h.L and h.S0, for every `x`, `σ ≥ 0`,
`s` with `‖s‖ ≤ 1`, `j ∈ [1 : p]`, `α > 0`, `δ ∈ (0, min(1, α/(4(3L_w + σ)))]` (14.1.17) and `d`
with `‖d‖ ≤ δ` and `ΔT_{m̂,j}(s, d) ≥ α δ^j/j!` (14.1.18): `m̂(s) - m̂(s + d) ≥ ½ α δ^j/j!`
(14.1.19). -/
theorem lemma_14_1_2 (hf : Chapter12.AssumptionD1pL f p Lf)
    (hc : AssumptionCD1pL c p Lc) (hL : AssumptionHLip h Lh) (hS : AssumptionHS0 h) (x : ℝⁿ)
    {σ : ℝ} (hσ : 0 ≤ σ) {s : ℝⁿ} (hs : ‖s‖ ≤ 1) {j : ℕ} (hj : j ∈ Finset.Icc 1 p) {α δ : ℝ}
    (hδ0 : 0 < δ)
    (hδ : δ ≤ min 1 (α / (4 * (3 * compositeLipschitzW Lf Lc Lh p m + σ)))) {d : ℝⁿ}
    (hd : ‖d‖ ≤ δ)
    (hdec : α * δ ^ j / j ! ≤ Optimization.compositeModelDecrement (ftaylorSeries ℝ f x)
      (ftaylorSeries ℝ c x) h p σ j s d) :
    α / 2 * δ ^ j / j ! ≤
      Optimization.compositeRegularizedModel (ftaylorSeries ℝ f x) (ftaylorSeries ℝ c x) h p σ s -
        Optimization.compositeRegularizedModel (ftaylorSeries ℝ f x) (ftaylorSeries ℝ c x) h p σ
          (s + d) := by
  obtain ⟨hDf, hDc⟩ := jet_bounds hf hc x
  have hp : 1 ≤ p := (Finset.mem_Icc.1 hj).1.trans (Finset.mem_Icc.1 hj).2
  have hW := one_le_compositeLipschitzW hf hc hL hp
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 p := Finset.mem_Icc.2 ⟨le_rfl, hp⟩
  have hLf0 : 0 ≤ Chapter12.finMax 1 Lf p := zero_le_one.trans Chapter12.le_finMax_left
  have hLc0 : 0 ≤ Real.sqrt m * Chapter12.finMax 0 Lc p :=
    mul_nonneg (Real.sqrt_nonneg _)
      ((hc.nonneg 1 h1).trans (Chapter12.le_finMax (b := 0) (u := Lc) h1))
  have hK : 0 < 3 * compositeLipschitzW Lf Lc Lh p m + σ := by linarith
  have hδα : 4 * (3 * (Chapter12.finMax 1 Lf p + Lh * (Real.sqrt m * Chapter12.finMax 0 Lc p)) +
      σ) * δ ≤ α := by
    have e : Chapter12.finMax 1 Lf p + Lh * (Real.sqrt m * Chapter12.finMax 0 Lc p) =
        compositeLipschitzW Lf Lc Lh p m := by
      unfold compositeLipschitzW; ring
    rw [e]
    have := hδ.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  exact Optimization.compositeRegularizedModel_sub_ge_of_decrement_ge hL.hasLipschitzConst hS.1
    hS.2 hLf0 hLc0 hDf hDc hσ hj hs hδ0.le (hδ.trans (min_le_left _ _)) hδα hd hdec

/-- **Lemma 14.1.3** of [cartis2022evaluation] (existence of a step for ARqpC), **with the
corrected index range**. Under f.D1pL, c.D1pL, h.L and h.S0, for a closed feasible set `X ∋ x`,
`σ > 0`, `1 ≤ q ≤ p` and `ε ∈ (0, 1]^q`, Algorithm 14.1.2 has an output `(s, δ_s)` (so (14.1.12)
holds, and `‖s‖ ≥ 1` or (14.1.13), by `Optimization.IsDetailedStepOutput.spec`) such that
`δ_{s,j} = 1` at the orders that are never halved (`j = 1` when `h` and `X` are convex), and, if
`‖s‖ < 1`, `δ_{s,j} ≥ κ_δ(σ) ε_j` for every halved order `j ∈ [1 : q]`, with
`κ_δ(σ) = ςθ/(8(3L_w + σ))` (14.1.24). (The book lists only `j ∈ [2 : q]`, but the bound is also
needed, and holds, for `j = 1` when `h` is nonconvex.) -/
theorem lemma_14_1_3 (hf : Chapter12.AssumptionD1pL f p Lf)
    (hc : AssumptionCD1pL c p Lc) (hL : AssumptionHLip h Lh) (hS : AssumptionHS0 h)
    (P : ARqpCParams) {q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) {ε : ℕ → ℝ}
    (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1) {X : Set ℝⁿ} (hX : IsClosed X) {x : ℝⁿ}
    (hx : x ∈ X) {σ : ℝ} (hσ : 0 < σ) :
    ∃ s δs, algorithm_14_1_2 f c h X p q P ε σ x s δs ∧ (∀ j ∉ halvingSet h X, δs j = 1) ∧
      (‖s‖ < 1 → ∀ j ∈ Finset.Icc 1 q, j ∈ halvingSet h X →
        P.ς * P.θ / (8 * (3 * compositeLipschitzW Lf Lc Lh p m + σ)) * ε j ≤ δs j) := by
  set Df := ftaylorSeries ℝ f x
  set Dc := ftaylorSeries ℝ c x
  set mod := Optimization.compositeRegularizedModel Df Dc h p σ
  set T : Set ℝⁿ := {s | x + s ∈ X}
  have hp : 1 ≤ p := hq.trans hqp
  have hW := one_le_compositeLipschitzW hf hc hL hp
  set K := 3 * compositeLipschitzW Lf Lc Lh p m + σ
  have hK : 3 ≤ K := by simp only [K]; linarith
  have hTc : IsClosed T := hX.preimage (continuous_const.add continuous_id)
  have hT0 : (0 : ℝⁿ) ∈ T := by simpa [T] using hx
  obtain ⟨sstar, hsT, hmin⟩ := Optimization.exists_isMinOn_compositeRegularizedModel
    (Df := Df) (Dc := Dc) (p := p) hL.hasLipschitzConst hσ hTc hT0
  have hinf : sInf (mod '' T) = mod sstar :=
    IsLeast.csInf_eq ⟨⟨sstar, hsT, rfl⟩, by rintro _ ⟨t, ht, rfl⟩; exact isMinOn_iff.1 hmin t ht⟩
  rcases le_or_gt 1 ‖sstar‖ with hlong | hshort
  · -- a long step: returned at once (Step 2.3)
    refine ⟨sstar, fun _ => 1, ⟨1, ⟨one_pos, le_rfl⟩, Relation.ReflTransGen.single
      (Optimization.DetailedStepTrans.ret hsT (by rw [hinf, one_mul]) hlong)⟩,
      fun _ _ => rfl, fun h' => absurd h' (not_lt.2 hlong)⟩
  · -- a short step: Lemma 12.2.9's argument (`Optimization.exists_isDetailedStepOutput`)
    have hς := P.ς_pos
    have hθ := P.θ_pos
    set δbar : ℕ → ℝ := fun j => min 1 (P.ς * P.θ * ε j / (4 * K))
    have hfeas : ∀ d ∈ {d | x + sstar + d ∈ X}, sstar + d ∈ T := fun d hd => by
      simpa [T, add_assoc] using hd
    have hSd : IsClosed {d : ℝⁿ | x + sstar + d ∈ X} :=
      hX.preimage (continuous_const.add continuous_id)
    have hSd0 : (0 : ℝⁿ) ∈ {d : ℝⁿ | x + sstar + d ∈ X} := by simpa [T] using hsT
    obtain ⟨δs, hout, h1, h2⟩ := Optimization.exists_isDetailedStepOutput (m := mod) (T := T)
      (Sd := fun s => {d | x + s + d ∈ X})
      (ΔT := fun j s d => Optimization.compositeModelDecrement Df Dc h p σ j s d)
      (J := halvingSet h X) (δbar := δbar) (ε := ε) (ς := P.ς) (θ := P.θ) hq hsT
      (fun t ht => isMinOn_iff.1 hmin t ht) hfeas hSd0 hς P.ς_le_one hθ
      (fun j hj => (hε j hj).1)
      (fun j _ => by simp [Optimization.compositeModelDecrement_def])
      (fun j _ δ hδ => by
        obtain ⟨d, hd, heq⟩ := Optimization.exists_compositeTaylorMeasure_eq
          (Df := ftaylorSeries ℝ (Optimization.regularizedModel Df p σ) sstar)
          (Dc := ftaylorSeries ℝ (Dc.taylorSum p) sstar) (h := h) (j := j)
          hL.hasLipschitzConst.continuous hSd hSd0 hδ.1.le
        refine ⟨d, hd, fun d' hd' => ?_⟩
        simp only [Optimization.compositeModelDecrement_def]
        rw [heq]
        exact Optimization.compositeTaylorDecrement_le_compositeTaylorMeasure
          hL.hasLipschitzConst hd')
      (fun j hj hjJ d hd => by
        simp only [halvingSet, mem_ofPred_eq, not_or, not_le, not_not] at hjJ
        obtain ⟨hj2, hconvh, hconvX⟩ := hjJ
        have hj1 : j = 1 := by have := (Finset.mem_Icc.1 hj).1; omega
        subst hj1
        have hTconv : Convex ℝ T := hconvX.translate_preimage_right x
        have hmloc : IsLocalMinOn (fun z => Optimization.regularizedModel Df p σ z +
            h (Dc.taylorSum p z)) T sstar := hmin.isLocalMinOn
        exact Optimization.compositeTaylorDecrement_one_nonpos_of_isLocalMinOn hTconv hsT
          ((Optimization.contDiff_regularizedModel (D := Df) (p := p) (σ := σ)).differentiable
            (by exact_mod_cast Nat.one_le_iff_ne_zero.1 hp) sstar)
          ((Dc.contDiff_taylorSum p (n := 1)).differentiable one_ne_zero sstar)
          hconvh hL.hasLipschitzConst hmloc (hfeas d hd.2))
      (fun j hj _ => ⟨lt_min one_pos (by have := (hε j hj).1; positivity), min_le_left _ _⟩)
      (fun j hj _ δ hδ d hd hdec => by
        have hj' : j ∈ Finset.Icc 1 p := Finset.mem_Icc.2
          ⟨(Finset.mem_Icc.1 hj).1, (Finset.mem_Icc.1 hj).2.trans hqp⟩
        have := lemma_14_1_2 hf hc hL hS x hσ.le hshort.le hj'
          (α := P.ς * P.θ * ε j) hδ.1
          (by
            refine hδ.2.trans (min_le_min le_rfl (le_of_eq ?_))
            simp only [K])
          (mem_closedBall_zero_iff.1 hd.1) hdec
        calc P.ς * P.θ * ε j * δ ^ j / (2 * j !) = P.ς * P.θ * ε j / 2 * δ ^ j / j ! := by
              field_simp
          _ ≤ _ := this)
    refine ⟨sstar, δs, hout, h1, fun _ j hj hjJ => (le_of_eq ?_).trans (h2 j hj hjJ)⟩
    have hε1 := hε j hj
    have hsm : P.ς * P.θ * ε j / (4 * K) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : P.ς * P.θ * ε j ≤ 1 := by
        have := P.ς_le_one; have := P.θ_lt_one.le
        have := hε1.1.le
        calc P.ς * P.θ * ε j ≤ 1 * 1 * 1 := by gcongr; exact hε1.2
          _ = 1 := by ring
      linarith
    simp only [δbar, min_eq_right hsm]
    field_simp
    ring

/-- An output of Algorithm 14.1.2 satisfies the Step-2 conditions of the ARqp run
(`Optimization.ARqpStep`) for suitable model displacements `dm` (`σ > 0`, `x ∈ X`, `X` closed). -/
theorem algorithm_14_1_2.exists_arqpStep (hL : AssumptionHLip h Lh) {X : Set ℝⁿ}
    (hX : IsClosed X) {P : ARqpCParams} {q : ℕ} {ε : ℕ → ℝ} {σ : ℝ} (hσ : 0 < σ) {x s : ℝⁿ}
    (hx : x ∈ X) {δs : ℕ → ℝ} (hout : algorithm_14_1_2 f c h X p q P ε σ x s δs) :
    ∃ dm : ℕ → ℝⁿ,
      Optimization.ARqpStep X P.toARqpParams q ε (arqpcData f c h p x σ) x s δs dm := by
  classical
  obtain ⟨hsT, -, hrad, -, hbr⟩ := hout.spec
  have hTc : IsClosed {s : ℝⁿ | x + s ∈ X} := hX.preimage (continuous_const.add continuous_id)
  have hT0 : (0 : ℝⁿ) ∈ {s : ℝⁿ | x + s ∈ X} := by simpa using hx
  obtain ⟨smin, -, hmin⟩ := Optimization.exists_isMinOn_compositeRegularizedModel
    (Df := ftaylorSeries ℝ f x) (Dc := ftaylorSeries ℝ c x) (p := p) hL hσ hTc hT0
  have hbdd : BddBelow (Optimization.compositeRegularizedModel (ftaylorSeries ℝ f x)
      (ftaylorSeries ℝ c x) h p σ '' {s | x + s ∈ X}) :=
    ⟨_, by rintro _ ⟨t, ht, rfl⟩; exact isMinOn_iff.1 hmin t ht⟩
  have hdm : ∀ j, ∃ d : ℝⁿ, j ∈ Finset.Icc 1 q → ‖s‖ < 1 →
      Optimization.IsApproxMeasureStep ((arqpcData f c h p x σ).modelDec j s) (δs j)
          {e | x + s + e ∈ X} P.ς d ∧
        (arqpcData f c h p x σ).modelDec j s d ≤ P.ς * P.θ * ε j * δs j ^ j / j ! := by
    intro j
    by_cases hj : j ∈ Finset.Icc 1 q
    · rcases hbr with hlong | hshort
      · exact ⟨0, fun _ h' => absurd hlong (not_le.2 h')⟩
      · obtain ⟨d, hd, h1, h2⟩ := hshort j hj
        exact ⟨d, fun _ _ => ⟨⟨hd, h1⟩, h2⟩⟩
    · exact ⟨0, fun h' => absurd h' hj⟩
  choose dm hdm using hdm
  refine ⟨dm, ⟨hsT, hout.le_of_bddBelow hT0 hbdd, fun heq => hout.isMinOn_of_eq hbdd heq,
    fun j _ => (hrad j).1, fun j _ => (hrad j).2, ?_⟩⟩
  rcases le_or_gt 1 ‖s‖ with hlong | hshort
  · exact Or.inl hlong
  · exact Or.inr fun j hj => hdm j hj hshort

/-- One ARqpC iteration's state in the existence proof: iterate, weight, Step-1 radii and
displacements, and the Step-2 step, radii and model displacements. -/
private structure ARqpCState (n : ℕ) where
  x : EuclideanSpace ℝ (Fin n)
  σ : ℝ
  δ : ℕ → ℝ
  d : ℕ → EuclideanSpace ℝ (Fin n)
  s : EuclideanSpace ℝ (Fin n)
  δs : ℕ → ℝ
  dm : ℕ → EuclideanSpace ℝ (Fin n)

/-- **Existence of ARqpC(-SC) runs** ([cartis2022evaluation], Algorithms 14.1.1–14.1.2 are well
defined): under f.D1pL, c.D1pL, h.L and h.S0, for a closed feasible set `X`, `x₀ ∈ X`,
`1 ≤ q ≤ p`, `ε ∈ (0, 1]^q` and `δ₀ ∈ (0, 1]^q`, there is an ARqpC run from `x₀` (Step-1
displacements are exact maximizers, Step 2 is the output of Lemma 14.1.3, and the regularization
parameters are any admissible updates). -/
theorem exists_isARqpCRun (hf : Chapter12.AssumptionD1pL f p Lf) (hc : AssumptionCD1pL c p Lc)
    (hL : AssumptionHLip h Lh) (hS : AssumptionHS0 h) (P : ARqpCParams) {q : ℕ} (hq : 1 ≤ q)
    (hqp : q ≤ p) {ε δ₀ : ℕ → ℝ} (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1)
    (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1) {X : Set ℝⁿ} (hX : IsClosed X) {x₀ : ℝⁿ}
    (hx₀ : x₀ ∈ X) :
    ∃ (x s : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → ℝⁿ), x 0 = x₀ ∧
      algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm := by
  classical
  let M : ℝⁿ → ℝ → Optimization.ARqpData ℝⁿ := fun y σ => arqpcData f c h p y σ
  -- Step-1 displacements
  have hwit : ∀ (y : ℝⁿ) (δ : ℕ → ℝ), ∃ d : ℕ → ℝⁿ, ∀ j, y ∈ X → 0 ≤ δ j →
      Optimization.IsApproxMeasureStep ((M y 1).dec j) (δ j) {e | y + e ∈ X} P.ς (d j) := by
    intro y δ
    have h' : ∀ j, ∃ dj : ℝⁿ, y ∈ X → 0 ≤ δ j →
        Optimization.IsApproxMeasureStep ((M y 1).dec j) (δ j) {e | y + e ∈ X} P.ς dj := by
      intro j
      by_cases hy : y ∈ X
      · by_cases hδ : 0 ≤ δ j
        · obtain ⟨dj, hdj⟩ := Optimization.exists_isApproxMeasureStep
            (hX.preimage (continuous_const.add continuous_id)) (by simpa using hy) hδ
            (Optimization.continuous_compositeTaylorDecrement _ _ h j hL.continuous).continuousOn
            (Optimization.compositeTaylorDecrement_zero_right _ _ h j) P.ς_le_one
          exact ⟨dj, fun _ _ => hdj⟩
        · exact ⟨0, fun _ h'' => absurd h'' hδ⟩
      · exact ⟨0, fun h'' => absurd h'' hy⟩
    choose d hd using h'
    exact ⟨d, hd⟩
  choose wit hwit using hwit
  -- Step-2 steps (Lemma 14.1.3)
  have hstp : ∀ (y : ℝⁿ) (σ : ℝ), ∃ t : ℝⁿ × (ℕ → ℝ) × (ℕ → ℝⁿ), y ∈ X → 0 < σ →
      algorithm_14_1_2 f c h X p q P ε σ y t.1 t.2.1 ∧
        Optimization.ARqpStep X P.toARqpParams q ε (M y σ) y t.1 t.2.1 t.2.2 := by
    intro y σ
    by_cases hy : y ∈ X
    · by_cases hσ : 0 < σ
      · obtain ⟨s, δs, hout, -⟩ := lemma_14_1_3 hf hc hL hS P hq hqp hε hX hy hσ
        obtain ⟨dm, hdm⟩ := hout.exists_arqpStep hL hX hσ hy
        exact ⟨(s, δs, dm), fun _ _ => ⟨hout, hdm⟩⟩
      · exact ⟨(0, 0, 0), fun _ h' => absurd h' hσ⟩
    · exact ⟨(0, 0, 0), fun h' => absurd h' hy⟩
  choose stp hstp using hstp
  let mk : ℝⁿ → ℝ → (ℕ → ℝ) → (ℕ → ℝⁿ) → ARqpCState n := fun y σ δ d =>
    ⟨y, σ, δ, d, (stp y σ).1, (stp y σ).2.1, (stp y σ).2.2⟩
  let Good : ARqpCState n → Prop := fun a =>
    a.x ∈ X ∧ P.σmin ≤ a.σ ∧ 0 < a.σ ∧ (∀ j ∈ Finset.Icc 1 q, 0 < a.δ j ∧ a.δ j ≤ 1) ∧
      (∀ j ∈ Finset.Icc 1 q, Optimization.IsApproxMeasureStep ((M a.x a.σ).dec j) (a.δ j)
        {e | a.x + e ∈ X} P.ς (a.d j)) ∧
      algorithm_14_1_2 f c h X p q P ε a.σ a.x a.s a.δs ∧
      Optimization.ARqpStep X P.toARqpParams q ε (M a.x a.σ) a.x a.s a.δs a.dm
  have hmk : ∀ y σ δ d, y ∈ X → P.σmin ≤ σ → 0 < σ →
      (∀ j ∈ Finset.Icc 1 q, 0 < δ j ∧ δ j ≤ 1) →
      (∀ j ∈ Finset.Icc 1 q, Optimization.IsApproxMeasureStep ((M y σ).dec j) (δ j)
        {e | y + e ∈ X} P.ς (d j)) → Good (mk y σ δ d) :=
    fun y σ δ d hy h1 h2 h3 h4 => ⟨hy, h1, h2, h3, h4, hstp y σ hy h2⟩
  let stopS : ARqpCState n → Prop := fun a =>
    Optimization.MeasureTestPasses (M a.x a.σ).dec q P.ς ε a.δ a.d ∨
      (M a.x a.σ).model a.s = (M a.x a.σ).model 0
  let ratio : ARqpCState n → ℝ := fun a =>
    Optimization.reductionRatio (fun y => f y + h (c y)) a.x a.s ((M a.x a.σ).pred a.s)
  let Trans : ARqpCState n → ARqpCState n → Prop := fun a b =>
    Optimization.ARAcceptance P.toARParams (ratio a) a.x a.s b.x a.σ b.σ ∧
      (P.η₁ ≤ ratio a → b.δ = a.δs) ∧ (¬ P.η₁ ≤ ratio a → b.δ = a.δ ∧ b.d = a.d)
  have hnext : ∀ a, Good a → ∃ b, Good b ∧ Trans a b := by
    rintro a ⟨hx, hmin, hpos, hδ, hw, -, hst⟩
    obtain ⟨σ', hacc, hmin', hpos'⟩ :=
      Optimization.exists_arAcceptance P.toARParams (ratio a) a.x a.s hmin
    by_cases hρ : P.η₁ ≤ ratio a
    · simp only [hρ, ↓reduceIte] at hacc
      refine ⟨mk (a.x + a.s) σ' a.δs (wit (a.x + a.s) a.δs), hmk _ _ _ _ hst.mem hmin'
        (hpos' hpos) (fun j hj => ⟨hst.radius_pos j hj, hst.radius_le_one j hj⟩)
        (fun j hj => hwit _ _ j hst.mem (hst.radius_pos j hj).le), hacc, fun _ => rfl,
        fun h' => absurd hρ h'⟩
    · simp only [hρ, ↓reduceIte] at hacc
      exact ⟨mk a.x σ' a.δ a.d, hmk _ _ _ _ hx hmin' (hpos' hpos) hδ hw, hacc,
        fun h' => absurd h' hρ, fun _ => ⟨rfl, rfl⟩⟩
  set a₀ := mk x₀ P.σ₀ δ₀ (wit x₀ δ₀) with ha₀
  have hgood₀ : Good a₀ := hmk _ _ _ _ hx₀ P.σmin_le_σ₀ P.σ₀_pos hδ₀
    (fun j hj => hwit _ _ j hx₀ (hδ₀ j hj).1.le)
  obtain ⟨r, hr0, hr⟩ := Optimization.exists_run_of_forall_exists_of_invariant
    (init := fun a => a = a₀) (inv := fun _ a => Good a) (stop := fun _ a => stopS a)
    (step := fun _ a b => Trans a b ∧ Good b) ⟨a₀, rfl⟩ (fun a ha => ha ▸ hgood₀)
    (fun _ a ha _ => by
      obtain ⟨b, hb, hab⟩ := hnext a ha
      exact ⟨b, hb, hab, hb⟩)
  have hgood : ∀ k, (∀ i < k, ¬ stopS (r i)) → Good (r k) := by
    intro k hk
    cases k with
    | zero => rw [hr0]; exact hgood₀
    | succ k => exact (hr k fun j hj => hk j (Nat.lt_succ_of_le hj)).2.2
  refine ⟨fun k => (r k).x, fun k => (r k).s, fun k => (r k).σ, fun k => (r k).δ,
    fun k => (r k).δs, fun k => (r k).d, fun k => (r k).dm, by simp [hr0, ha₀, mk], ?_⟩
  exact ⟨hq, hqp, hε, hδ₀, ⟨⟨by simp [hr0, ha₀, mk], fun k hk _ => (hgood k hk).2.2.2.2.2.2,
    fun k hk => (hr k hk).2.1.1⟩, (hgood 0 fun _ h => absurd h (Nat.not_lt_zero _)).1,
    by simp [hr0, ha₀, mk], fun k hk => (hgood k hk).2.2.2.2.1, fun k hk => (hr k hk).2.1.2⟩,
    fun k hk _ => (hgood k hk).2.2.2.2.2.1⟩

end Step


/-! ### Lemmas 14.1.4–14.1.6 -/

namespace algorithm_14_1_1

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {h : ℝᵐ → ℝ} {X : Set ℝⁿ} {p q : ℕ} {P : ARqpCParams}
  {ε δ₀ : ℕ → ℝ} {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → ℝⁿ}

/-- The Step-1 test of ARqpC at iteration `k` ((14.1.10), normalized). -/
abbrev Stop₁ (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (h : ℝᵐ → ℝ) (p q : ℕ) (P : ARqpCParams)
    (ε : ℕ → ℝ) (x : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ : ℕ → ℕ → ℝ) (d : ℕ → ℕ → ℝⁿ) (k : ℕ) : Prop :=
  Optimization.arqpStop₁ P.toARqpParams q ε (fun k => arqpcData f c h p (x k) (σ k)) δ d k

/-- The iterates of an ARqpC run stay in `X` up to termination. -/
theorem mem (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i < k, ¬ arqpcStop f c h p q P ε x s σ δ d i) : x k ∈ X :=
  hr.run.mem k hk

/-- The radii of an ARqpC run stay in `(0, 1]` up to termination. -/
theorem delta_mem (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i < k, ¬ arqpcStop f c h p q P ε x s σ δ d i) :
    ∀ j ∈ Finset.Icc 1 q, 0 < δ k j ∧ δ k j ≤ 1 :=
  hr.run.delta_mem hr.δ₀_mem k hk

/-- The value `w(x) = T_{w,p}(x, 0)`, so the predicted decrease is `w(x) - T_{w,p}(x, s)`. -/
theorem compositeTaylorDecrement_eq_sub (y t : ℝⁿ) :
    Optimization.compositeTaylorDecrement (ftaylorSeries ℝ f y) (ftaylorSeries ℝ c y) h p t =
      (f y + h (c y)) - (taylorPolynomial f p y t + h ((ftaylorSeries ℝ c y).taylorSum p t)) := by
  rw [Optimization.compositeTaylorDecrement, ← taylorPolynomial_eq_taylorSum f,
    ← taylorPolynomial_eq_taylorSum c, taylorPolynomial_zero_right, taylorPolynomial_zero_right]

end algorithm_14_1_1

section Analysis

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {h : ℝᵐ → ℝ} {X : Set ℝⁿ} {p q : ℕ} {P : ARqpCParams}
  {ε δ₀ : ℕ → ℝ} {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → ℝⁿ}
  {Lf Lc : ℕ → ℝ} {Lh : ℝ}

/-- **Lemma 14.1.4** of [cartis2022evaluation] (termination in Step 2 of ARqpC). For an ARqpC run
with `f`, `c` of class `C^p`, h.L and h.S0:
(i) if `q = 1` and `h` and `X` are convex, termination never happens in Step 2: at every
iteration reaching Step 2, `m̂_k(s_k) < m̂_k(0)`;
(ii) if Step 2 terminates at iteration `k` (`m̂_k(s_k) = m̂_k(0)`), then `x_k` is an
`(ε, δ)`-approximate `q`-th order minimizer (14.1.9) over `X` for some `δ ∈ (0, 1]^q`. -/
theorem lemma_14_1_4 (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hfC : ContDiff ℝ p f) (hcC : ContDiff ℝ p c) (hL : AssumptionHLip h Lh)
    (hS : AssumptionHS0 h) :
    (q = 1 → ConvexOn ℝ univ h → Convex ℝ X → ∀ k,
      (∀ i < k, ¬ arqpcStop f c h p q P ε x s σ δ d i) →
      ¬ algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d k →
      Optimization.compositeRegularizedModel (ftaylorSeries ℝ f (x k)) (ftaylorSeries ℝ c (x k))
          h p (σ k) (s k) <
        Optimization.compositeRegularizedModel (ftaylorSeries ℝ f (x k))
          (ftaylorSeries ℝ c (x k)) h p (σ k) 0) ∧
    (∀ k, (∀ i < k, ¬ arqpcStop f c h p q P ε x s σ δ d i) →
      ¬ algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d k →
      Optimization.compositeRegularizedModel (ftaylorSeries ℝ f (x k)) (ftaylorSeries ℝ c (x k))
          h p (σ k) (s k) =
        Optimization.compositeRegularizedModel (ftaylorSeries ℝ f (x k))
          (ftaylorSeries ℝ c (x k)) h p (σ k) 0 →
      ∃ δ' : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, 0 < δ' j ∧ δ' j ≤ 1) ∧
        Optimization.IsEpsDeltaApproxComposite (ftaylorSeries ℝ f (x k))
          (ftaylorSeries ℝ c (x k)) h {e | x k + e ∈ X} q ε δ') := by
  have hp : 1 ≤ p := hr.one_le_q.trans hr.q_le_p
  refine ⟨fun hq hconv hX k hk h1 => ?_, fun k hk h1 heq => ?_⟩
  · have hstep := hr.run.step hk h1
    refine lt_of_le_of_ne hstep.model_le fun heq => h1 ?_
    have hmin := hstep.isMinOn_of_eq heq
    -- `0` minimizes the model on the feasible displacements: the Step-1 test passes
    intro j hj
    have hj1 : j = 1 := by have := Finset.mem_Icc.1 hj; omega
    subst hj1
    have hw := hr.run.witness k hk 1 hj
    have hδ := (hr.delta_mem hk 1 hj).1
    have hε := (hr.ε_mem 1 hj).1
    have hTconv : Convex ℝ {e | x k + e ∈ X} := hX.translate_preimage_right (x k)
    have hT0 : (0 : ℝⁿ) ∈ {e | x k + e ∈ X} := by simpa using hr.mem hk
    have hdec :=
      Optimization.compositeTaylorDecrement_one_nonpos_of_isLocalMinOn_compositeRegularizedModel
      hL.hasLipschitzConst hconv (hfC.contDiffAt.isSymm_ftaylorSeries le_rfl)
      (hcC.contDiffAt.isSymm_ftaylorSeries le_rfl) hp hTconv hT0 hmin.isLocalMinOn hw.mem
    change Optimization.compositeTaylorDecrement _ _ h 1 (d k 1) ≤ _
    refine hdec.trans ?_
    have := P.ς_pos
    positivity
  · have hmin := (hr.run.step hk h1).isMinOn_of_eq heq
    have hT0 : (0 : ℝⁿ) ∈ {e | x k + e ∈ X} := by simpa using hr.mem hk
    have hσ : 0 ≤ σ k := (hr.run.toIsARRun.sigma_pos hk k le_rfl).le
    have hex : ∀ j, ∃ δ' : ℝ, j ∈ Finset.Icc 1 q → 0 < δ' ∧ δ' ≤ 1 ∧
        Optimization.compositeTaylorMeasure (ftaylorSeries ℝ f (x k)) (ftaylorSeries ℝ c (x k))
          h j δ' {e | x k + e ∈ X} ≤ ε j * δ' ^ j / j ! := by
      intro j
      by_cases hj : j ∈ Finset.Icc 1 q
      · obtain ⟨δ₁, h1, h2, h3⟩ :=
          Optimization.exists_radius_of_isMinOn_compositeRegularizedModel_zero
            hL.hasLipschitzConst hS.1 hS.2 hσ hT0 hmin
            ((Finset.mem_Icc.1 hj).2.trans hr.q_le_p) (hr.ε_mem j hj).1
        exact ⟨δ₁, fun _ => ⟨h1, h2, h3 δ₁ h1.le le_rfl⟩⟩
      · exact ⟨1, fun h' => absurd h' hj⟩
    choose δ' hδ' using hex
    exact ⟨δ', fun j hj => ⟨(hδ' j hj).1, (hδ' j hj).2.1⟩, fun j hj => (hδ' j hj).2.2⟩

/-- **Lemma 14.1.5** of [cartis2022evaluation] (Taylor decrease for ARqpC). At every iteration
`k` of an ARqpC run at which Step 2 is executed,
`ΔT_{w,p}(x_k, s_k) ≥ σ_k/(p+1)! ‖s_k‖^{p+1}` (14.1.25); the decrease is positive unless Step 2
terminates. -/
theorem lemma_14_1_5 (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i < k, ¬ arqpcStop f c h p q P ε x s σ δ d i)
    (h1 : ¬ algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d k) :
    σ k / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) ≤
      Optimization.compositeTaylorDecrement (ftaylorSeries ℝ f (x k)) (ftaylorSeries ℝ c (x k))
        h p (s k) ∧
    (¬ Optimization.arqpStop₂ (fun k => arqpcData f c h p (x k) (σ k)) s k →
      0 < Optimization.compositeTaylorDecrement (ftaylorSeries ℝ f (x k))
        (ftaylorSeries ℝ c (x k)) h p (s k)) := by
  have hstep := hr.run.step hk h1
  refine ⟨Optimization.le_compositeTaylorDecrement_of_compositeRegularizedModel_le
    hstep.model_le, fun h2 => ?_⟩
  have hlt := Optimization.lt_compositeTaylorDecrement_of_compositeRegularizedModel_lt
    (lt_of_le_of_ne hstep.model_le h2)
  have hσ := hr.run.toIsARRun.sigma_pos hk k le_rfl
  exact lt_of_le_of_lt (by positivity) hlt

/-- **Lemma 14.1.6** of [cartis2022evaluation] (upper bound on the regularization parameter for
ARqpC). Under f.DpL (`f` is `C^p` with `L_{f,p}`-Lipschitz `∇^p f`), c.DpL (componentwise
constant `L_{c,p}`) and h.L, every ARqpC run satisfies
`σ_k ≤ σ_max = max(σ₀, γ₃ L_{w,p}/(1 - η₂))` (14.1.26) up to (and including) its first
termination index, with `L_{w,p} = L_{f,p} + √m L_{h,0} L_{c,p}` (14.1.27). -/
theorem lemma_14_1_6 (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hfC : ContDiff ℝ p f) (hLfp : IteratedFDerivLipschitzOn f p (Lf p) univ)
    (hLf0 : 0 ≤ Lf p) (hcC : ContDiff ℝ p c)
    (hLcp : ∀ i, IteratedFDerivLipschitzOn (fun y => c y i) p (Lc p) univ) (hLc0 : 0 ≤ Lc p)
    (hL : AssumptionHLip h Lh) {K : ℕ} (hK : ∀ i < K, ¬ arqpcStop f c h p q P ε x s σ δ d i) :
    ∀ k ≤ K, σ k ≤ Optimization.arSigmaMax P.toARParams (compositeLipschitzWp Lf Lc Lh p m) := by
  set Lw := compositeLipschitzWp Lf Lc Lh p m
  have hLw : 0 ≤ Lw := by have := hL.nonneg; unfold Lw compositeLipschitzWp; positivity
  have hη := P.one_sub_η₂_pos
  have hLc : IteratedFDerivLipschitzOn c p (Real.sqrt m * Lc p) univ :=
    iteratedFDerivLipschitzOn_of_forall_component (fun _ _ => hcC.contDiffAt) hLcp
  have hforce : ∀ k, (∀ j ≤ k, ¬ arqpcStop f c h p q P ε x s σ δ d j) →
      Lw / (1 - P.η₂) ≤ σ k →
        P.η₂ ≤ Optimization.arqpRatio (fun y => f y + h (c y))
          (fun k => arqpcData f c h p (x k) (σ k)) x s k := by
    intro k hk hσk
    have hk' : ∀ i < k, ¬ arqpcStop f c h p q P ε x s σ δ d i := fun i hi => hk i hi.le
    have h1 : ¬ algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d k := fun h' => hk k le_rfl (Or.inl h')
    have h2 : ¬ Optimization.arqpStop₂ (fun k => arqpcData f c h p (x k) (σ k)) s k :=
      fun h' => hk k le_rfl (Or.inr h')
    obtain ⟨hdec, hpos⟩ := lemma_14_1_5 hr hk' h1
    have hpos := hpos h2
    set pred := Optimization.compositeTaylorDecrement (ftaylorSeries ℝ f (x k))
      (ftaylorSeries ℝ c (x k)) h p (s k)
    have hrem := Optimization.abs_sub_compositeTaylor_le_of_lipschitz convex_univ
      (fun _ _ => hfC.contDiffAt) (fun _ _ => hcC.contDiffAt) hLfp hLc
      hL.hasLipschitzConst
      (x := x k) (s := s k) (mem_univ _) (mem_univ _)
    have hLw' : Lf p + Lh * (Real.sqrt m * Lc p) = Lw := by
      unfold Lw compositeLipschitzWp; ring
    rw [hLw'] at hrem
    have hσL : Lw ≤ (1 - P.η₂) * σ k := by
      rw [div_le_iff₀ hη] at hσk; linarith
    have hfac : (0 : ℝ) < ((p + 1)! : ℝ) := by positivity
    have hR : Lw / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) ≤ (1 - P.η₂) * pred := by
      calc Lw / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1)
          ≤ (1 - P.η₂) * σ k / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) := by gcongr
        _ = (1 - P.η₂) * (σ k / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1)) := by ring
        _ ≤ (1 - P.η₂) * pred := by gcongr
    have hval : f (x k) + h (c (x k)) - pred =
        taylorPolynomial f p (x k) (s k) + h ((ftaylorSeries ℝ c (x k)).taylorSum p (s k)) := by
      have := algorithm_14_1_1.compositeTaylorDecrement_eq_sub (f := f) (c := c) (h := h)
        (p := p) (x k) (s k)
      linarith
    have := Optimization.le_reductionRatio_of_abs_sub_le (f := fun y => f y + h (c y))
      (x := x k) (s := s k) hpos (c := 1 - P.η₂) (by
        rw [hval]
        exact hrem.trans hR)
    change P.η₂ ≤ Optimization.reductionRatio _ _ _ pred
    linarith
  intro k hkK
  have := (hr.run.toIsARRun.sigma_le_max hforce hK k hkK).2.2
  refine this.trans (le_of_eq ?_)
  rw [Optimization.arSigmaMax_def, mul_div_assoc]

end Analysis


/-! ### Lemmas 14.1.7 and 14.1.8 -/

section StepLength

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {h : ℝᵐ → ℝ} {X : Set ℝⁿ} {p q : ℕ} {P : ARqpCParams}
  {ε δ₀ : ℕ → ℝ} {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → ℝⁿ}
  {Lf Lc : ℕ → ℝ} {Lh : ℝ}

/-- The bound `σ_max = max(σ₀, γ₃ L_{w,p}/(1 - η₂))` of Lemma 14.1.6. -/
noncomputable abbrev arqpcSigmaMax (P : ARqpCParams) (Lf Lc : ℕ → ℝ) (Lh : ℝ) (p m : ℕ) : ℝ :=
  Optimization.arSigmaMax P.toARParams (compositeLipschitzWp Lf Lc Lh p m)

/-- The constant `κ_{δ,min} = ςθ/(8(3L_w + σ_max))` of (14.1.29). -/
noncomputable def kappaDeltaMin (P : ARqpCParams) (Lf Lc : ℕ → ℝ) (Lh : ℝ) (p m : ℕ) : ℝ :=
  P.ς * P.θ / (8 * (3 * compositeLipschitzW Lf Lc Lh p m + arqpcSigmaMax P Lf Lc Lh p m))

/-- Lemma 14.1.6 under f.D1pL and c.D1pL: `σ_k ≤ σ_max` up to termination. -/
theorem sigma_le_arqpcSigmaMax (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hf : Chapter12.AssumptionD1pL f p Lf)
    (hc : AssumptionCD1pL c p Lc) (hL : AssumptionHLip h Lh) {K : ℕ}
    (hK : ∀ i < K, ¬ arqpcStop f c h p q P ε x s σ δ d i) :
    ∀ k ≤ K, σ k ≤ arqpcSigmaMax P Lf Lc Lh p m := by
  have hp' : p ∈ Finset.Icc 1 p := Finset.mem_Icc.2 ⟨hr.one_le_q.trans hr.q_le_p, le_rfl⟩
  exact lemma_14_1_6 hr hf.contDiff (hf.lipschitz p hp') (zero_le_one.trans (hf.one_le p hp'))
    hc.contDiff
    (fun i => hc.lipschitz_component i p hp') (hc.nonneg p hp') hL hK

/-- **Lemma 14.1.7** of [cartis2022evaluation] (a useful inequality for ARqpC), **corrected**.
Under f.D1pL, c.D1pL and h.L: if iteration `k` of an ARqpC run is successful, the
run has not terminated up to `k`, the Step-1 test fails at `k + 1`, and the step is short
(`‖s_k‖ < 1`, so that (14.1.13) holds), then for some `j ∈ [1 : q]`
`(ς - θ) ε_j δ_{k+1,j}^j/j! < (L_{w,p} + σ_max) ∑_{ℓ=1}^j δ_{k+1,j}^ℓ/ℓ! ‖s_k‖^{p-ℓ+1} +
2 √m L_{h,0} L_{c,p}/(p+1)! ‖s_k‖^{p+1}` (14.1.30). (The printed `(1 - θ)` presumes `ς = 1`, and
the last term lacks the factor `2`.) -/
private theorem lemma_14_1_7_of_short (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hf : Chapter12.AssumptionD1pL f p Lf)
    (hc : AssumptionCD1pL c p Lc) (hL : AssumptionHLip h Lh) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpcStop f c h p q P ε x s σ δ d i)
    (hsucc : P.η₁ ≤ Optimization.arqpRatio (fun y => f y + h (c y))
      (fun k => arqpcData f c h p (x k) (σ k)) x s k)
    (h1 : ¬ algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d (k + 1)) (hshort : ‖s k‖ < 1) :
    ∃ j ∈ Finset.Icc 1 q, (P.ς - P.θ) * ε j * δ (k + 1) j ^ j / j ! <
      (compositeLipschitzWp Lf Lc Lh p m + arqpcSigmaMax P Lf Lc Lh p m) *
        ∑ ℓ ∈ Finset.Icc 1 j, δ (k + 1) j ^ ℓ / ℓ ! * ‖s k‖ ^ (p - ℓ + 1) +
      2 * Real.sqrt m * Lh * Lc p / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) := by
  have hp' : p ∈ Finset.Icc 1 p := Finset.mem_Icc.2 ⟨hr.one_le_q.trans hr.q_le_p, le_rfl⟩
  have hk' : ∀ i < k + 1, ¬ arqpcStop f c h p q P ε x s σ δ d i :=
    fun i hi => hk i (Nat.lt_succ_iff.1 hi)
  have hstep := hr.run.step (fun i hi => hk i hi.le) fun h' => hk k le_rfl (Or.inl h')
  have hbr := hstep.branch.resolve_left (not_le.2 hshort)
  have hrad := ((hr.run.radii k hk).1 hsucc)
  have hx1 : x (k + 1) = x k + s k := hr.run.toIsARRun.eq_add_of_succ hk hsucc
  -- the failed Step-1 test at `k + 1`
  simp only [algorithm_14_1_1.Stop₁, Optimization.arqpStop₁, Optimization.MeasureTestPasses,
    not_forall, not_le] at h1
  obtain ⟨j, hj, hlt⟩ := h1
  refine ⟨j, hj, ?_⟩
  have hjp : j ≤ p := (Finset.mem_Icc.1 hj).2.trans hr.q_le_p
  have hw := hr.run.witness (k + 1) hk' j hj
  have hδ := (hr.delta_mem hk' j hj).1
  have hmem : x (k + 1) ∈ X := hr.mem hk'
  have hS0 : (0 : ℝⁿ) ∈ {e | x k + s k + e ∈ X} := by simpa [← hx1] using hmem
  have hσ0 : 0 ≤ σ k := (hr.run.toIsARRun.sigma_pos hk' k k.le_succ).le
  have hσmax := sigma_le_arqpcSigmaMax hr hf hc hL hk' k k.le_succ
  -- the measure at `x_{k+1}` exceeds `ς ε δ^j/j!`
  have h₁ : P.ς * ε j * δ (k + 1) j ^ j / (j ! : ℝ) - 0 <
      Optimization.compositeTaylorMeasure (ftaylorSeries ℝ f (x k + s k))
        (ftaylorSeries ℝ c (x k + s k)) h j (δ (k + 1) j) {e | x k + s k + e ∈ X} := by
    rw [sub_zero]
    have hdm : Optimization.compositeTaylorDecrement (ftaylorSeries ℝ f (x (k + 1)))
        (ftaylorSeries ℝ c (x (k + 1))) h j (d (k + 1) j) ≤
        Optimization.compositeTaylorMeasure (ftaylorSeries ℝ f (x (k + 1)))
          (ftaylorSeries ℝ c (x (k + 1))) h j (δ (k + 1) j) {e | x (k + 1) + e ∈ X} :=
      Optimization.compositeTaylorDecrement_le_compositeTaylorMeasure hL.hasLipschitzConst hw.1
    change P.ς * ε j * δ (k + 1) j ^ j / (j ! : ℝ) <
      Optimization.compositeTaylorDecrement (ftaylorSeries ℝ f (x (k + 1)))
        (ftaylorSeries ℝ c (x (k + 1))) h j (d (k + 1) j) at hlt
    rw [hx1] at hdm hlt
    exact hlt.trans_le hdm
  -- the model measure at `s_k` is at most `θ ε δ^j/j!`
  have h₂ : Optimization.compositeTaylorMeasure
      (ftaylorSeries ℝ (Optimization.regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)) (s k))
      (ftaylorSeries ℝ ((ftaylorSeries ℝ c (x k)).taylorSum p) (s k)) h j (δ (k + 1) j)
      {e | x k + s k + e ∈ X} ≤ P.θ * ε j * δ (k + 1) j ^ j / j ! := by
    obtain ⟨happ, hsmall⟩ := hbr j hj
    rw [hrad]
    have hm := happ.2.trans hsmall
    have hς := P.ς_pos
    have : P.ς * Optimization.compositeTaylorMeasure
        (ftaylorSeries ℝ (Optimization.regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)) (s k))
        (ftaylorSeries ℝ ((ftaylorSeries ℝ c (x k)).taylorSum p) (s k)) h j (δs k j)
        {e | x k + s k + e ∈ X} ≤ P.ς * (P.θ * ε j * δs k j ^ j / j !) := by
      refine hm.trans (le_of_eq ?_)
      ring
    exact le_of_mul_le_mul_left this hς
  have := Optimization.radius_inequality_of_compositeTaylorMeasure_gt convex_univ
    (fun _ _ => hf.contDiff.contDiffAt) (fun _ _ => hc.contDiff.contDiffAt) (hf.lipschitz p hp')
    (hc.lipschitz hp') hL.hasLipschitzConst (zero_le_one.trans (hf.one_le p hp'))
    (mul_nonneg (Real.sqrt_nonneg _) (hc.nonneg p hp')) (mem_univ (x k)) (mem_univ _) hσ0
    hσmax hjp hS0 hδ.le h₁ h₂
  have e1 : Lf p + Lh * (Real.sqrt m * Lc p) = compositeLipschitzWp Lf Lc Lh p m := by
    unfold compositeLipschitzWp; ring
  have e2 : 2 * Lh * (Real.sqrt m * Lc p) = 2 * Real.sqrt m * Lh * Lc p := by ring
  rw [e1, e2, add_zero] at this
  exact this

/-- **Lemma 14.1.7** of [cartis2022evaluation] (a useful inequality for ARqpC), **corrected**.
Under f.D1pL, c.D1pL and h.L: if iteration `k` of an ARqpC run is successful, the run has not
terminated up to `k`, and the Step-1 test fails at `k + 1`, then for some `j ∈ [1 : q]`
`(ς - θ) ε_j δ_{k+1,j}^j/j! < (L_{w,p} + σ_max) ∑_{ℓ=1}^j δ_{k+1,j}^ℓ/ℓ! ‖s_k‖^{p-ℓ+1} +
2 √m L_{h,0} L_{c,p}/(p+1)! ‖s_k‖^{p+1}` (14.1.30). (The printed `(1 - θ)` presumes `ς = 1`, and
the last term lacks the factor `2`. For short steps the inequality comes from the model test
(14.1.13); for long steps, `‖s_k‖ ≥ 1`, it holds trivially.) -/
theorem lemma_14_1_7 (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hf : Chapter12.AssumptionD1pL f p Lf)
    (hc : AssumptionCD1pL c p Lc) (hL : AssumptionHLip h Lh) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpcStop f c h p q P ε x s σ δ d i)
    (hsucc : P.η₁ ≤ Optimization.arqpRatio (fun y => f y + h (c y))
      (fun k => arqpcData f c h p (x k) (σ k)) x s k)
    (h1 : ¬ algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d (k + 1)) :
    ∃ j ∈ Finset.Icc 1 q, (P.ς - P.θ) * ε j * δ (k + 1) j ^ j / j ! <
      (compositeLipschitzWp Lf Lc Lh p m + arqpcSigmaMax P Lf Lc Lh p m) *
        ∑ ℓ ∈ Finset.Icc 1 j, δ (k + 1) j ^ ℓ / ℓ ! * ‖s k‖ ^ (p - ℓ + 1) +
      2 * Real.sqrt m * Lh * Lc p / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) := by
  rcases lt_or_ge ‖s k‖ 1 with hshort | hlong
  · exact lemma_14_1_7_of_short hr hf hc hL hk hsucc h1 hshort
  have hp' : p ∈ Finset.Icc 1 p := Finset.mem_Icc.2 ⟨hr.one_le_q.trans hr.q_le_p, le_rfl⟩
  have hk' : ∀ i < k + 1, ¬ arqpcStop f c h p q P ε x s σ δ d i :=
    fun i hi => hk i (Nat.lt_succ_iff.1 hi)
  have hj1 : (1 : ℕ) ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, hr.one_le_q⟩
  refine ⟨1, hj1, ?_⟩
  have hδ := (hr.delta_mem hk' 1 hj1).1
  have hε := hr.ε_mem 1 hj1
  have hA : 1 ≤ compositeLipschitzWp Lf Lc Lh p m + arqpcSigmaMax P Lf Lc Lh p m := by
    have := hf.one_le p hp'
    have := hc.nonneg p hp'
    have := hL.nonneg
    have := Optimization.arSigmaMax_pos P.toARParams (compositeLipschitzWp Lf Lc Lh p m)
    unfold compositeLipschitzWp
    have : 0 ≤ Real.sqrt m * Lh * Lc p := by positivity
    linarith
  have hB : 0 ≤ 2 * Real.sqrt m * Lh * Lc p / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) := by
    have := hc.nonneg p hp'
    have := hL.nonneg
    positivity
  have hsp : 1 ≤ ‖s k‖ ^ (p - 1 + 1) := one_le_pow₀ hlong
  have hlhs : (P.ς - P.θ) * ε 1 < 1 := by
    have := P.ς_le_one; have := P.θ_pos
    nlinarith [hε.1, hε.2]
  simp only [Finset.Icc_self, Finset.sum_singleton, pow_one, Nat.factorial_one, Nat.cast_one,
    div_one]
  nlinarith [mul_le_mul_of_nonneg_left hsp hδ.le]

end StepLength


section StepLength2

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {h : ℝᵐ → ℝ} {X : Set ℝⁿ} {p q : ℕ} {P : ARqpCParams}
  {ε δ₀ : ℕ → ℝ} {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → ℝⁿ}
  {Lf Lc : ℕ → ℝ} {Lh : ℝ}

/-- The step-length bound of the first case of (14.1.31):
`(a/(j! A) ε/3)^{1/(p-j+1)}` with `a = ς - θ`, `A = L_{w,p} + σ_max` (equal to the book's
`((ς - θ) ε_j / (3 j! A))^{1/p}` for `j = 1`). -/
noncomputable def stepBound1 (P : ARqpCParams) (Lf Lc : ℕ → ℝ) (Lh : ℝ) (p m j : ℕ) (εj : ℝ) :
    ℝ :=
  ((P.ς - P.θ) / ((j ! : ℝ) * (compositeLipschitzWp Lf Lc Lh p m +
    arqpcSigmaMax P Lf Lc Lh p m)) * εj / 3) ^ (1 / ((p : ℝ) - j + 1))

/-- The step-length bound of the second case of (14.1.31), with the factor `ε_j^{(j+1)/(p+1)}`:
`(a κ^j/(3 j! A))^{1/(p-j+1)} ε_j^{(j+1)/(p+1)}`, `κ = κ_{δ,min}`. -/
noncomputable def stepBound2 (P : ARqpCParams) (Lf Lc : ℕ → ℝ) (Lh : ℝ) (p m j : ℕ) (εj : ℝ) :
    ℝ :=
  ((P.ς - P.θ) / ((j ! : ℝ) * (compositeLipschitzWp Lf Lc Lh p m +
    arqpcSigmaMax P Lf Lc Lh p m)) * kappaDeltaMin P Lf Lc Lh p m ^ j / 3) ^
      (1 / ((p : ℝ) - j + 1)) * εj ^ (((j : ℝ) + 1) / ((p : ℝ) + 1))

/-- Positivity and size facts for the constants of Lemma 14.1.8. -/
private theorem consts_facts (hθς : P.θ < P.ς) (hL : AssumptionHLip h Lh)
    (hf : Chapter12.AssumptionD1pL f p Lf)
    (hc : AssumptionCD1pL c p Lc) (hp : 1 ≤ p) {j : ℕ} :
    0 < P.ς - P.θ ∧ P.ς - P.θ ≤ (j ! : ℝ) *
      (compositeLipschitzWp Lf Lc Lh p m + arqpcSigmaMax P Lf Lc Lh p m) ∧
    0 < compositeLipschitzWp Lf Lc Lh p m + arqpcSigmaMax P Lf Lc Lh p m ∧
    0 ≤ 2 * Real.sqrt m * Lh * Lc p / ((p + 1)! : ℝ) ∧
    2 * Real.sqrt m * Lh * Lc p / ((p + 1)! : ℝ) ≤
      compositeLipschitzWp Lf Lc Lh p m + arqpcSigmaMax P Lf Lc Lh p m ∧
    0 < kappaDeltaMin P Lf Lc Lh p m ∧ kappaDeltaMin P Lf Lc Lh p m ≤ 1 := by
  have hp' : p ∈ Finset.Icc 1 p := Finset.mem_Icc.2 ⟨hp, le_rfl⟩
  have hLfp := (hf.one_le p hp')
  have hLcp := hc.nonneg p hp'
  have hLh := hL.nonneg
  have hσ := Optimization.arSigmaMax_pos P.toARParams (compositeLipschitzWp Lf Lc Lh p m)
  have hW := one_le_compositeLipschitzW hf hc hL hp
  have hB0 : 0 ≤ Real.sqrt m * Lh * Lc p := by positivity
  have hWp : Lf p + Real.sqrt m * Lh * Lc p = compositeLipschitzWp Lf Lc Lh p m := rfl
  have hfac2 : (2 : ℝ) ≤ ((p + 1)! : ℝ) := by
    have : 2 ≤ (p + 1)! := by
      calc 2 = (1 + 1)! := rfl
        _ ≤ (p + 1)! := Nat.factorial_le (by omega)
    exact_mod_cast this
  have hjf : (1 : ℝ) ≤ (j ! : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero j)
  have hς1 := P.ς_le_one
  have hθ := P.θ_pos
  refine ⟨by linarith, ?_, by rw [← hWp]; positivity, by positivity, ?_, ?_, ?_⟩
  · calc P.ς - P.θ ≤ 1 := by linarith
      _ ≤ 1 * (compositeLipschitzWp Lf Lc Lh p m + arqpcSigmaMax P Lf Lc Lh p m) := by
          rw [one_mul, ← hWp]; linarith
      _ ≤ _ := by gcongr; rw [← hWp]; positivity
  · rw [div_le_iff₀ (by positivity), ← hWp]
    nlinarith
  · unfold kappaDeltaMin; have := P.ς_pos; positivity
  · unfold kappaDeltaMin
    rw [div_le_one (by positivity)]
    have : P.ς * P.θ ≤ 1 := by nlinarith [P.θ_lt_one]
    linarith

/-- **Lemma 14.1.8** of [cartis2022evaluation] (lower bound on the step for ARqpC),
**corrected**. Under f.D1pL, c.D1pL and h.L with `θ < ς`, if iteration `k` of an ARqpC run is
successful, the run has not terminated up to `k` and the Step-1 test fails at `k + 1`, then there
is `j ∈ [1 : q]` such that
* if `δ_{s_k,j} = δ_{k+1,j} = 1` (the policy for `q = 1` and `h` convex),
  `‖s_k‖ ≥ ((ς - θ)/(j! A) ε_j/3)^{1/(p-j+1)}` (first case of (14.1.31));
* if `δ_{k+1,j} ≥ κ_{δ,min} ε_j` (the policy (14.1.28)),
  `‖s_k‖ ≥ ((ς - θ) κ_{δ,min}^j/(3 j! A))^{1/(p-j+1)} ε_j^{(j+1)/(p+1)}` (second case of
  (14.1.31), with the factor `ε_j^{(j+1)/(p+1)}` omitted by the book),
where `A = L_{w,p} + σ_max` and `(1 - θ)` is replaced by `(ς - θ)`. Long steps (`‖s_k‖ ≥ 1`)
satisfy both bounds. -/
theorem lemma_14_1_8 (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hθς : P.θ < P.ς) (hf : Chapter12.AssumptionD1pL f p Lf)
    (hc : AssumptionCD1pL c p Lc) (hL : AssumptionHLip h Lh) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpcStop f c h p q P ε x s σ δ d i)
    (hsucc : P.η₁ ≤ Optimization.arqpRatio (fun y => f y + h (c y))
      (fun k => arqpcData f c h p (x k) (σ k)) x s k)
    (h1 : ¬ algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d (k + 1)) :
    ∃ j ∈ Finset.Icc 1 q,
      (δ (k + 1) j = 1 → stepBound1 P Lf Lc Lh p m j (ε j) ≤ ‖s k‖) ∧
      (kappaDeltaMin P Lf Lc Lh p m * ε j ≤ δ (k + 1) j →
        stepBound2 P Lf Lc Lh p m j (ε j) ≤ ‖s k‖) := by
  have hp : 1 ≤ p := hr.one_le_q.trans hr.q_le_p
  have hk' : ∀ i < k + 1, ¬ arqpcStop f c h p q P ε x s σ δ d i :=
    fun i hi => hk i (Nat.lt_succ_iff.1 hi)
  -- bounds below `1`
  have hsmall : ∀ j ∈ Finset.Icc 1 q, stepBound1 P Lf Lc Lh p m j (ε j) ≤ 1 ∧
      stepBound2 P Lf Lc Lh p m j (ε j) ≤ 1 := by
    intro j hj
    obtain ⟨ha, haA, hA, -, -, hκ, hκ1⟩ := consts_facts (j := j) hθς hL hf hc hp
    have hjp : j ≤ p := (Finset.mem_Icc.1 hj).2.trans hr.q_le_p
    have hε := hr.ε_mem j hj
    have hα : 0 ≤ (P.ς - P.θ) / ((j ! : ℝ) * (compositeLipschitzWp Lf Lc Lh p m +
        arqpcSigmaMax P Lf Lc Lh p m)) := by positivity
    have hα1 : (P.ς - P.θ) / ((j ! : ℝ) * (compositeLipschitzWp Lf Lc Lh p m +
        arqpcSigmaMax P Lf Lc Lh p m)) ≤ 1 := by
      rw [div_le_one (by positivity)]; exact haA
    have he : 0 ≤ 1 / ((p : ℝ) - j + 1) := by
      have : (j : ℝ) ≤ p := by exact_mod_cast hjp
      exact div_nonneg zero_le_one (by linarith)
    refine ⟨Real.rpow_le_one (by have := hε.1.le; positivity)
      (by nlinarith [hε.2]) he, ?_⟩
    have hb1 : ((P.ς - P.θ) / ((j ! : ℝ) * (compositeLipschitzWp Lf Lc Lh p m +
        arqpcSigmaMax P Lf Lc Lh p m)) * kappaDeltaMin P Lf Lc Lh p m ^ j / 3) ^
          (1 / ((p : ℝ) - j + 1)) ≤ 1 := by
      have : kappaDeltaMin P Lf Lc Lh p m ^ j ≤ 1 := pow_le_one₀ hκ.le hκ1
      exact Real.rpow_le_one (by positivity) (by nlinarith [pow_nonneg hκ.le j]) he
    have hb2 : ε j ^ (((j : ℝ) + 1) / ((p : ℝ) + 1)) ≤ 1 :=
      Real.rpow_le_one hε.1.le hε.2 (by positivity)
    unfold stepBound2
    calc _ ≤ 1 * 1 := mul_le_mul hb1 hb2 (Real.rpow_nonneg hε.1.le _) zero_le_one
      _ = 1 := one_mul 1
  rcases le_or_gt 1 ‖s k‖ with hlong | hshort
  · have hj1 : (1 : ℕ) ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, hr.one_le_q⟩
    exact ⟨1, hj1, fun _ => (hsmall 1 hj1).1.trans hlong,
      fun _ => (hsmall 1 hj1).2.trans hlong⟩
  · obtain ⟨j, hj, hlt⟩ := lemma_14_1_7 hr hf hc hL hk hsucc h1
    refine ⟨j, hj, ?_⟩
    obtain ⟨ha, haA, hA, hB, hBA, hκ, hκ1⟩ := consts_facts (j := j) hθς hL hf hc hp
    have hjp : j ≤ p := (Finset.mem_Icc.1 hj).2.trans hr.q_le_p
    have hε := hr.ε_mem j hj
    have hδ := (hr.delta_mem hk' j hj).1
    -- the step is nonzero: the predicted decrease is positive
    have ht : 0 < ‖s k‖ := by
      refine norm_pos_iff.2 fun h0 => ?_
      have hpos := (lemma_14_1_5 hr (fun i hi => hk i hi.le)
        (fun h' => hk k le_rfl (Or.inl h'))).2 (fun h' => hk k le_rfl (Or.inr h'))
      rw [h0, Optimization.compositeTaylorDecrement_zero_right] at hpos
      exact lt_irrefl _ hpos
    have hineq : Optimization.MeasureIneq
        (compositeLipschitzWp Lf Lc Lh p m + arqpcSigmaMax P Lf Lc Lh p m)
        (2 * Real.sqrt m * Lh * Lc p / ((p + 1)! : ℝ)) (P.ς - P.θ) (ε j) (δ (k + 1) j) ‖s k‖
        j p := by
      rw [Optimization.measureIneq_iff]
      exact hlt.le
    obtain ⟨hc1, hc2⟩ := Optimization.norm_step_ge_of_measure_ineq hineq hA hB hBA ha haA hε.1
      hε.2 ht hδ hjp
    refine ⟨fun hδ1 => hc1 (by rw [hδ1]; exact hshort.le), fun hpol => ?_⟩
    exact hc2 _ hκ hκ1 hpol

end StepLength2

/-! ### The radius policies -/

section RadiusPolicy

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {h : ℝᵐ → ℝ} {X : Set ℝⁿ} {p q : ℕ} {P : ARqpCParams}
  {ε δ₀ : ℕ → ℝ} {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → ℝⁿ}
  {Lf Lc : ℕ → ℝ} {Lh : ℝ}

/-- At the orders that Algorithm 14.1.2 never halves (`j = 1` when `h` and `X` are convex), the
Step-2 radius is `1`. -/
theorem algorithm_14_1_1.radius_eq_one (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    {k : ℕ} (hk : ∀ i < k, ¬ arqpcStop f c h p q P ε x s σ δ d i)
    (h1 : ¬ algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d k) {j : ℕ} (hj : j ∉ halvingSet h X) :
    δs k j = 1 :=
  (hr.detailed k hk h1).spec.2.2.2.1 j hj

/-- **The radius policy (14.1.28)** holds for every ARqpC run (Lemma 14.1.3 for every output of
Algorithm 14.1.2): under f.D1pL, c.D1pL, h.L and h.S0, at every iteration reaching Step 2,
`‖s_k‖ ≥ 1` or `δ_{s_k,j} ≥ κ_{δ,min} ε_j` for all `j ∈ [1 : q]`. -/
theorem algorithm_14_1_1.radius_policy
    (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hf : Chapter12.AssumptionD1pL f p Lf) (hc : AssumptionCD1pL c p Lc)
    (hL : AssumptionHLip h Lh) (hS : AssumptionHS0 h) {k : ℕ}
    (hk : ∀ i < k, ¬ arqpcStop f c h p q P ε x s σ δ d i)
    (h1 : ¬ algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d k) :
    1 ≤ ‖s k‖ ∨ ∀ j ∈ Finset.Icc 1 q, kappaDeltaMin P Lf Lc Lh p m * ε j ≤ δs k j := by
  rcases le_or_gt 1 ‖s k‖ with hlong | hshort
  · exact Or.inl hlong
  refine Or.inr fun j hj => ?_
  have hp : 1 ≤ p := hr.one_le_q.trans hr.q_le_p
  have hε := hr.ε_mem j hj
  have hσ : 0 < σ k := hr.run.toIsARRun.sigma_pos hk k le_rfl
  have hσmax := sigma_le_arqpcSigmaMax hr hf hc hL hk k le_rfl
  have hW := one_le_compositeLipschitzW hf hc hL hp
  have hς := P.ς_pos
  have hθ := P.θ_pos
  have hςθ : P.ς * P.θ ≤ 1 := by nlinarith [P.ς_le_one, P.θ_lt_one]
  set K := 3 * compositeLipschitzW Lf Lc Lh p m + σ k
  have hK : 3 ≤ K := by simp only [K]; linarith
  have hκ1 : kappaDeltaMin P Lf Lc Lh p m * ε j ≤ P.ς * P.θ / (8 * K) * ε j := by
    unfold kappaDeltaMin
    gcongr
    · exact hε.1.le
    · simp only [K]; linarith
  refine hκ1.trans ?_
  by_cases hJ : j ∈ halvingSet h X
  · set δbar : ℕ → ℝ := fun i => min 1 (P.ς * P.θ * ε i / (4 * K))
    have hsm : P.ς * P.θ * ε j / (4 * K) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith [hε.2, hε.1]
    have hge := (hr.detailed k hk h1).radius_ge (δbar := δbar) hr.one_le_q
      (fun i _ _ => min_le_left _ _)
      (fun s' hs' hs'1 i _ hiq δ' hδ' d' hd' hdec => by
        have hi' : i ∈ Finset.Icc 1 p := Finset.mem_Icc.2
          ⟨(Finset.mem_Icc.1 hiq).1, (Finset.mem_Icc.1 hiq).2.trans hr.q_le_p⟩
        have hεi := hr.ε_mem i hiq
        have := lemma_14_1_2 hf hc hL hS (x k) hσ.le hs'1.le hi'
          (α := P.ς * P.θ * ε i) hδ'.1 (hδ'.2.trans (min_le_min le_rfl le_rfl))
          (mem_closedBall_zero_iff.1 hd'.1) hdec
        calc P.ς * P.θ * ε i * δ' ^ i / (2 * i !) = P.ς * P.θ * ε i / 2 * δ' ^ i / i ! := by
              field_simp
          _ ≤ _ := this) j hJ hj
    refine le_trans (le_of_eq ?_) hge
    simp only [δbar, min_eq_right hsm]
    field_simp
    ring
  · rw [hr.radius_eq_one hk h1 hJ]
    have : P.ς * P.θ / (8 * K) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    nlinarith [hε.2, hε.1, div_nonneg (by positivity : (0 : ℝ) ≤ P.ς * P.θ)
      (by positivity : (0 : ℝ) ≤ 8 * K)]

end RadiusPolicy


/-! ### Lemma 14.1.9 and Theorem 14.1.10 -/

section Complexity

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {h : ℝᵐ → ℝ} {X : Set ℝⁿ} {p q : ℕ} {P : ARqpCParams}
  {ε δ₀ : ℕ → ℝ} {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → ℝⁿ}
  {Lf Lc : ℕ → ℝ} {Lh : ℝ}

/-- The constant `κ_{Δm}` of Lemma 14.1.9 in the case `q = 1`, `h` convex:
`σ_min/(p+1)! ((ς - θ)/(3 (L_{w,p} + σ_max)))^{(p+1)/p}`. -/
noncomputable def kappaDm1 (P : ARqpCParams) (Lf Lc : ℕ → ℝ) (Lh : ℝ) (p m : ℕ) : ℝ :=
  P.σmin / ((p + 1)! : ℝ) * ((P.ς - P.θ) /
    (compositeLipschitzWp Lf Lc Lh p m + arqpcSigmaMax P Lf Lc Lh p m) / 3) ^
      (((p : ℝ) + 1) / p)

/-- The constant `κ_{Δm}` of Lemma 14.1.9 in the general case:
`σ_min/(p+1)! ((ς - θ) κ_{δ,min}^q/(3 q! (L_{w,p} + σ_max)))^{(p+1)/(p-q+1)}`. -/
noncomputable def kappaDm2 (P : ARqpCParams) (Lf Lc : ℕ → ℝ) (Lh : ℝ) (p q m : ℕ) : ℝ :=
  P.σmin / ((p + 1)! : ℝ) * ((P.ς - P.θ) /
    ((q ! : ℝ) * (compositeLipschitzWp Lf Lc Lh p m + arqpcSigmaMax P Lf Lc Lh p m)) *
      kappaDeltaMin P Lf Lc Lh p m ^ q / 3) ^ (((p : ℝ) + 1) / ((p : ℝ) - q + 1))

/-- `(b^{1/e})^{p+1} = b^{(p+1)/e}`. -/
private theorem rpow_pow_succ {b e : ℝ} (hb : 0 ≤ b) (p : ℕ) :
    (b ^ (1 / e)) ^ (p + 1) = b ^ (((p : ℝ) + 1) / e) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hb]
  congr 1
  push_cast
  ring

/-- **Lemma 14.1.9** of [cartis2022evaluation] (model and function decreases for ARqpC),
**corrected**. Under f.D1pL, c.D1pL and h.L with `θ < ς`, if iteration `k` of an ARqpC run is
successful, the run has not terminated up to `k` and the Step-1 test fails at `k + 1`, then:
* (`q = 1`, policy `δ_{k+1,1} = 1`) `ΔT_{w,p}(x_k, s_k) ≥ κ_{Δm} ε_1^{(p+1)/p}` (14.1.32) and
  `w(x_k) - w(x_{k+1}) ≥ η₁ κ_{Δm} ε_1^{(p+1)/p}` (14.1.33), `κ_{Δm} = kappaDm1`;
* (policy (14.1.28): `‖s_k‖ ≥ 1` or `δ_{k+1,j} ≥ κ_{δ,min} ε_j` for all `j`) for some
  `j ∈ [1 : q]`, `ΔT_{w,p}(x_k, s_k) ≥ κ_{Δm} ε_j^{j+1}` and
  `w(x_k) - w(x_{k+1}) ≥ η₁ κ_{Δm} ε_j^{j+1}`, `κ_{Δm} = kappaDm2`.
(The book writes `f`, `L_{f,p}` for `w`, `L_{w,p}`, assumes only f.D1qL, and claims (14.1.32) at
every iteration before termination; `(1 - θ)` is replaced by `(ς - θ)`.) -/
theorem lemma_14_1_9 (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hθς : P.θ < P.ς) (hf : Chapter12.AssumptionD1pL f p Lf)
    (hc : AssumptionCD1pL c p Lc) (hL : AssumptionHLip h Lh) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpcStop f c h p q P ε x s σ δ d i)
    (hsucc : P.η₁ ≤ Optimization.arqpRatio (fun y => f y + h (c y))
      (fun k => arqpcData f c h p (x k) (σ k)) x s k)
    (h1 : ¬ algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d (k + 1)) :
    (q = 1 → δ (k + 1) 1 = 1 →
      kappaDm1 P Lf Lc Lh p m * ε 1 ^ (((p : ℝ) + 1) / p) ≤
        Optimization.compositeTaylorDecrement (ftaylorSeries ℝ f (x k))
          (ftaylorSeries ℝ c (x k)) h p (s k) ∧
      P.η₁ * (kappaDm1 P Lf Lc Lh p m * ε 1 ^ (((p : ℝ) + 1) / p)) ≤
        (f (x k) + h (c (x k))) - (f (x (k + 1)) + h (c (x (k + 1))))) ∧
    ((1 ≤ ‖s k‖ ∨ ∀ j ∈ Finset.Icc 1 q, kappaDeltaMin P Lf Lc Lh p m * ε j ≤ δ (k + 1) j) →
      ∃ j ∈ Finset.Icc 1 q,
        kappaDm2 P Lf Lc Lh p q m * ε j ^ (j + 1) ≤
          Optimization.compositeTaylorDecrement (ftaylorSeries ℝ f (x k))
            (ftaylorSeries ℝ c (x k)) h p (s k) ∧
        P.η₁ * (kappaDm2 P Lf Lc Lh p q m * ε j ^ (j + 1)) ≤
          (f (x k) + h (c (x k))) - (f (x (k + 1)) + h (c (x (k + 1))))) := by
  have hp : 1 ≤ p := hr.one_le_q.trans hr.q_le_p
  set pred := Optimization.compositeTaylorDecrement (ftaylorSeries ℝ f (x k))
    (ftaylorSeries ℝ c (x k)) h p (s k)
  have hk' : ∀ i < k, ¬ arqpcStop f c h p q P ε x s σ δ d i := fun i hi => hk i hi.le
  obtain ⟨hpred5, hpos⟩ := lemma_14_1_5 hr hk' (fun h' => hk k le_rfl (Or.inl h'))
  have hpos := hpos fun h' => hk k le_rfl (Or.inr h')
  have hσmin : P.σmin ≤ σ k := hr.run.toIsARRun.sigmaMin_le hk' k le_rfl
  have hfac : (0 : ℝ) < ((p + 1)! : ℝ) := by positivity
  have hpred : P.σmin / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) ≤ pred :=
    le_trans (by gcongr) hpred5
  have hdecr : P.η₁ * pred ≤ (f (x k) + h (c (x k))) - (f (x (k + 1)) + h (c (x (k + 1)))) :=
    (hr.run.toIsARRun.sub_ge_of_succ (w := fun y => f y + h (c y))
      (pred := fun k => Optimization.compositeTaylorDecrement (ftaylorSeries ℝ f (x k))
        (ftaylorSeries ℝ c (x k)) h p (s k)) hk rfl hpos hsucc).2
  have hη := P.η₁_pos
  have hσm := P.σmin_pos
  have finish : ∀ v : ℝ, v ≤ pred →
      v ≤ pred ∧ P.η₁ * v ≤ (f (x k) + h (c (x k))) - (f (x (k + 1)) + h (c (x (k + 1)))) :=
    fun v hv => ⟨hv, (mul_le_mul_of_nonneg_left hv hη.le).trans hdecr⟩
  obtain ⟨j₀, hj₀, hb1, hb2⟩ := lemma_14_1_8 hr hθς hf hc hL hk hsucc h1
  refine ⟨fun hq hδ1 => ?_, fun hpol => ?_⟩
  · -- the case `q = 1`
    have hj₀1 : j₀ = 1 := by have := Finset.mem_Icc.1 hj₀; omega
    subst hj₀1
    have hb := hb1 hδ1
    obtain ⟨ha, -, hA, -⟩ := consts_facts (j := 1) hθς hL hf hc hp
    have hε := hr.ε_mem 1 hj₀
    have hbase : 0 ≤ (P.ς - P.θ) / (((1 : ℕ)! : ℝ) * (compositeLipschitzWp Lf Lc Lh p m +
        arqpcSigmaMax P Lf Lc Lh p m)) * ε 1 / 3 :=
      div_nonneg (mul_nonneg (div_nonneg ha.le (mul_nonneg (by positivity) hA.le)) hε.1.le)
        (by norm_num)
    refine finish _ ((le_of_eq ?_).trans (le_trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Real.rpow_nonneg hbase _) hb (p + 1)) (by positivity)) hpred))
    unfold kappaDm1
    have hexp : (p : ℝ) - ((1 : ℕ) : ℝ) + 1 = p := by push_cast; ring
    rw [hexp, rpow_pow_succ hbase, Nat.factorial_one, Nat.cast_one, one_mul,
      show (P.ς - P.θ) / (compositeLipschitzWp Lf Lc Lh p m +
        arqpcSigmaMax P Lf Lc Lh p m) * ε 1 / 3 = ((P.ς - P.θ) /
        (compositeLipschitzWp Lf Lc Lh p m + arqpcSigmaMax P Lf Lc Lh p m) / 3) * ε 1 by ring,
      Real.mul_rpow (by positivity) hε.1.le]
    ring
  · -- the general case
    obtain ⟨ha1, -, hA1, -, -, hκ, hκ1⟩ := consts_facts (j := 1) hθς hL hf hc hp
    set A := compositeLipschitzWp Lf Lc Lh p m + arqpcSigmaMax P Lf Lc Lh p m
    set κ := kappaDeltaMin P Lf Lc Lh p m
    -- the base `B_q ≤ 1` of `kappaDm2`
    have hq1 : (1 : ℝ) ≤ (q ! : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero q)
    have hBq0 : 0 < (P.ς - P.θ) / ((q ! : ℝ) * A) * κ ^ q / 3 := by positivity
    have hqp : (q : ℝ) ≤ p := by exact_mod_cast hr.q_le_p
    have hBq1 : (P.ς - P.θ) / ((q ! : ℝ) * A) * κ ^ q / 3 ≤ 1 := by
      have h1' : (P.ς - P.θ) / ((q ! : ℝ) * A) ≤ 1 := by
        rw [div_le_one (by positivity)]
        have := (consts_facts (j := q) hθς hL hf hc hp).2.1
        exact this
      have h2' : κ ^ q ≤ 1 := pow_le_one₀ hκ.le hκ1
      have : 0 ≤ (P.ς - P.θ) / ((q ! : ℝ) * A) := by positivity
      nlinarith [pow_nonneg hκ.le q]
    have hKdm : kappaDm2 P Lf Lc Lh p q m ≤ P.σmin / ((p + 1)! : ℝ) := by
      unfold kappaDm2
      have : ((P.ς - P.θ) / ((q ! : ℝ) * A) * κ ^ q / 3) ^ (((p : ℝ) + 1) / ((p : ℝ) - q + 1))
          ≤ 1 := Real.rpow_le_one hBq0.le hBq1 (div_nonneg (by positivity) (by linarith))
      calc _ ≤ P.σmin / ((p + 1)! : ℝ) * 1 := by gcongr
        _ = _ := mul_one _
    rcases le_or_gt 1 ‖s k‖ with hlong | hshort
    · -- a long step
      have hj1 : (1 : ℕ) ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, hr.one_le_q⟩
      refine ⟨1, hj1, finish _ (le_trans ?_ hpred)⟩
      have hε := hr.ε_mem 1 hj1
      have h1' : ε 1 ^ (1 + 1) ≤ 1 := pow_le_one₀ hε.1.le hε.2
      have h2' : 1 ≤ ‖s k‖ ^ (p + 1) := one_le_pow₀ hlong
      have h3' : 0 ≤ kappaDm2 P Lf Lc Lh p q m := by
        unfold kappaDm2; exact mul_nonneg (by positivity) (Real.rpow_nonneg hBq0.le _)
      calc kappaDm2 P Lf Lc Lh p q m * ε 1 ^ (1 + 1) ≤ kappaDm2 P Lf Lc Lh p q m * 1 :=
            mul_le_mul_of_nonneg_left h1' h3'
        _ ≤ P.σmin / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) := by nlinarith
    · have hpol' := hpol.resolve_left (not_le.2 hshort)
      have hb := hb2 (hpol' j₀ hj₀)
      refine ⟨j₀, hj₀, finish _ (le_trans ?_ hpred)⟩
      have hε := hr.ε_mem j₀ hj₀
      obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj₀
      have hjq' : (j₀ : ℝ) ≤ q := by exact_mod_cast hjq
      have hBj0 : 0 < (P.ς - P.θ) / ((j₀ ! : ℝ) * A) * κ ^ j₀ / 3 := by positivity
      -- `B_q ≤ B_j`
      have hBqj : (P.ς - P.θ) / ((q ! : ℝ) * A) * κ ^ q / 3 ≤
          (P.ς - P.θ) / ((j₀ ! : ℝ) * A) * κ ^ j₀ / 3 := by
        have hf : (j₀ ! : ℝ) ≤ (q ! : ℝ) := by exact_mod_cast Nat.factorial_le hjq
        have hk' : κ ^ q ≤ κ ^ j₀ := pow_le_pow_of_le_one hκ.le hκ1 hjq
        have hd : (P.ς - P.θ) / ((q ! : ℝ) * A) ≤ (P.ς - P.θ) / ((j₀ ! : ℝ) * A) :=
          div_le_div_of_nonneg_left ha1.le (by positivity) (by gcongr)
        have : 0 ≤ (P.ς - P.θ) / ((q ! : ℝ) * A) := by positivity
        gcongr
      have hBj1 : (P.ς - P.θ) / ((j₀ ! : ℝ) * A) * κ ^ j₀ / 3 ≤ 1 := by
        have h1' : (P.ς - P.θ) / ((j₀ ! : ℝ) * A) ≤ 1 := by
          rw [div_le_one (by positivity)]
          exact (consts_facts (j := j₀) hθς hL hf hc hp).2.1
        have h2' : κ ^ j₀ ≤ 1 := pow_le_one₀ hκ.le hκ1
        have : 0 ≤ (P.ς - P.θ) / ((j₀ ! : ℝ) * A) := by positivity
        nlinarith [pow_nonneg hκ.le j₀]
      have hej : 0 < (p : ℝ) - j₀ + 1 := by linarith
      have heq : 0 < (p : ℝ) - q + 1 := by linarith
      have hexp : ((p : ℝ) + 1) / ((p : ℝ) - j₀ + 1) ≤ ((p : ℝ) + 1) / ((p : ℝ) - q + 1) :=
        div_le_div_of_nonneg_left (by positivity) heq (by linarith)
      have hmono : ((P.ς - P.θ) / ((q ! : ℝ) * A) * κ ^ q / 3) ^
            (((p : ℝ) + 1) / ((p : ℝ) - q + 1)) ≤
          ((P.ς - P.θ) / ((j₀ ! : ℝ) * A) * κ ^ j₀ / 3) ^
            (((p : ℝ) + 1) / ((p : ℝ) - j₀ + 1)) :=
        (Real.rpow_le_rpow hBq0.le hBqj (by positivity)).trans
          (Real.rpow_le_rpow_of_exponent_ge hBj0 hBj1 hexp)
      have hsb : (stepBound2 P Lf Lc Lh p m j₀ (ε j₀)) ^ (p + 1) =
          ((P.ς - P.θ) / ((j₀ ! : ℝ) * A) * κ ^ j₀ / 3) ^
            (((p : ℝ) + 1) / ((p : ℝ) - j₀ + 1)) * ε j₀ ^ (j₀ + 1) := by
        unfold stepBound2
        rw [mul_pow, rpow_pow_succ hBj0.le, ← Real.rpow_natCast (ε j₀ ^ _),
          ← Real.rpow_mul hε.1.le, ← Real.rpow_natCast (ε j₀) (j₀ + 1)]
        congr 2
        have : (p : ℝ) + 1 ≠ 0 := by positivity
        push_cast
        field_simp
      have hsb0 : 0 ≤ stepBound2 P Lf Lc Lh p m j₀ (ε j₀) :=
        mul_nonneg (Real.rpow_nonneg hBj0.le _) (Real.rpow_nonneg hε.1.le _)
      have hpow := pow_le_pow_left₀ hsb0 hb (p + 1)
      rw [hsb] at hpow
      unfold kappaDm2
      calc P.σmin / ((p + 1)! : ℝ) * ((P.ς - P.θ) / ((q ! : ℝ) * A) * κ ^ q / 3) ^
            (((p : ℝ) + 1) / ((p : ℝ) - q + 1)) * ε j₀ ^ (j₀ + 1)
          ≤ P.σmin / ((p + 1)! : ℝ) * (((P.ς - P.θ) / ((j₀ ! : ℝ) * A) * κ ^ j₀ / 3) ^
            (((p : ℝ) + 1) / ((p : ℝ) - j₀ + 1)) * ε j₀ ^ (j₀ + 1)) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmono
              (pow_nonneg hε.1.le _)) (by positivity)
        _ ≤ P.σmin / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) := by gcongr

end Complexity


section Theorem

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {h : ℝᵐ → ℝ} {X : Set ℝⁿ} {p q : ℕ} {P : ARqpCParams}
  {ε δ₀ : ℕ → ℝ} {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → ℝⁿ}
  {Lf Lc : ℕ → ℝ} {Lh : ℝ}

/-- The objective `w = f + h ∘ c` does not increase along an ARqpC run (before termination). -/
private theorem w_succ_le (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpcStop f c h p q P ε x s σ δ d i) :
    f (x (k + 1)) + h (c (x (k + 1))) ≤ f (x k) + h (c (x k)) := by
  by_cases hs : P.η₁ ≤ Optimization.arqpRatio (fun y => f y + h (c y))
      (fun k => arqpcData f c h p (x k) (σ k)) x s k
  · have hk' : ∀ i < k, ¬ arqpcStop f c h p q P ε x s σ δ d i := fun i hi => hk i hi.le
    have hpos := (lemma_14_1_5 hr hk' (fun h' => hk k le_rfl (Or.inl h'))).2
      (fun h' => hk k le_rfl (Or.inr h'))
    have := (hr.run.toIsARRun.sub_ge_of_succ (w := fun y => f y + h (c y))
      (pred := fun k => Optimization.compositeTaylorDecrement (ftaylorSeries ℝ f (x k))
        (ftaylorSeries ℝ c (x k)) h p (s k)) hk rfl hpos hs).2
    have := mul_pos P.η₁_pos hpos
    linarith
  · rw [hr.run.toIsARRun.eq_of_not_succ hk (not_le.1 hs)]

/-- The radii policy `δ_{k,1} = 1` propagates along the run. -/
private theorem delta_one_eq (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hδ₀ : δ₀ 1 = 1)
    (hpol : ∀ k, (∀ i < k, ¬ arqpcStop f c h p q P ε x s σ δ d i) →
      ¬ algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d k → δs k 1 = 1) :
    ∀ k, (∀ i < k, ¬ arqpcStop f c h p q P ε x s σ δ d i) → δ k 1 = 1 := by
  intro k
  induction k with
  | zero => intro _; rw [hr.run.delta_zero, hδ₀]
  | succ k ih =>
    intro hk
    have hk' : ∀ i ≤ k, ¬ arqpcStop f c h p q P ε x s σ δ d i :=
      fun i hi => hk i (Nat.lt_succ_of_le hi)
    obtain ⟨h1, h2⟩ := hr.run.radii k hk'
    by_cases hs : P.η₁ ≤ Optimization.arqpRatio (fun y => f y + h (c y))
        (fun k => arqpcData f c h p (x k) (σ k)) x s k
    · rw [h1 hs]
      exact hpol k (fun i hi => hk' i hi.le) fun h' => hk' k le_rfl (Or.inl h')
    · rw [(h2 hs).1]
      exact ih fun i hi => hk' i hi.le

/-- The Step-1 termination certifies (14.1.9) with the current radii. -/
private theorem isEpsDeltaApprox_of_stop₁
    (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i < k, ¬ arqpcStop f c h p q P ε x s σ δ d i)
    (h1 : algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d k) :
    Optimization.IsEpsDeltaApproxComposite (ftaylorSeries ℝ f (x k)) (ftaylorSeries ℝ c (x k))
      h {e | x k + e ∈ X} q ε (δ k) :=
  Optimization.MeasureTestPasses.isEpsDeltaApproxComposite P.ς_pos
    (fun j hj => hr.run.witness k hk j hj) h1

/-- **Theorem 14.1.10, part 1** of [cartis2022evaluation] (`q = 1`, `h` convex; for ARqpC-SC also
`X` convex). Under f.D1pL, c.D1pL, h.L, h.S0, w.Bb (on `X`) and `θ < ς`, if the initial
radius is `δ_{0,1} = 1` (Algorithm 14.1.2 then keeps `δ_{s_k,1} = 1`, since it never halves the
first-order radius when `h` and `X` are convex), the ARqpC run terminates at some
`k_ε` with `φ^1_{w,1}(x_{k_ε}) ≤ ε_1`, using at most
`κ_A (w(x₀) - w_low)/δ + κ_C` evaluations of `f` and `c` (14.1.34) and at most
`(w(x₀) - w_low)/δ + 2` evaluations of their derivatives (14.1.35), where
`δ = η₁ κ_{Δm} ε_1^{(p+1)/p}` (`κ_{Δm} = kappaDm1`, so that `1/(η₁ κ_{Δm}) = κ^{s,1}`),
`κ_A = 1 + |log γ₁|/log γ₂` (`κ^{a,1} = κ^{s,1} κ_A`) and
`κ_C = (|log γ₁| + log(σ_max/σ₀))/log γ₂ + 2`. This is `O(ε_1^{-(p+1)/p})`. -/
theorem theorem_14_1_10_i (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hθς : P.θ < P.ς) (hf : Chapter12.AssumptionD1pL f p Lf)
    (hc : AssumptionCD1pL c p Lc) (hL : AssumptionHLip h Lh) (hS : AssumptionHS0 h) {wlow : ℝ}
    (hw : AssumptionWBb f c h X wlow) (hq : q = 1) (hconv : ConvexOn ℝ univ h)
    (hXc : Convex ℝ X) (hδ₀ : δ₀ 1 = 1) :
    ∃ kε, Optimization.IsFirstHit (arqpcStop f c h p q P ε x s σ δ d) kε ∧
      Optimization.compositeTaylorMeasure (ftaylorSeries ℝ f (x kε)) (ftaylorSeries ℝ c (x kε))
        h 1 1 {e | x kε + e ∈ X} ≤ ε 1 ∧
      (Optimization.funEvalCount kε : ℝ) ≤
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
          ((f (x 0) + h (c (x 0)) - wlow) /
            (P.η₁ * (kappaDm1 P Lf Lc Lh p m * ε 1 ^ (((p : ℝ) + 1) / p)))) +
        ((|Real.log P.γ₁| + Real.log (arqpcSigmaMax P Lf Lc Lh p m / P.σ₀)) /
          Real.log P.γ₂ + 2) ∧
      (Optimization.derivEvalCount (fun k => P.η₁ ≤ Optimization.arqpRatio
          (fun y => f y + h (c y)) (fun k => arqpcData f c h p (x k) (σ k)) x s k) kε : ℝ) ≤
        (f (x 0) + h (c (x 0)) - wlow) /
          (P.η₁ * (kappaDm1 P Lf Lc Lh p m * ε 1 ^ (((p : ℝ) + 1) / p))) + 2 := by
  have hp : 1 ≤ p := hr.one_le_q.trans hr.q_le_p
  have hpol : ∀ k, (∀ i < k, ¬ arqpcStop f c h p q P ε x s σ δ d i) →
      ¬ algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d k → δs k 1 = 1 := fun k hk h1 =>
    hr.radius_eq_one hk h1 (by simp [halvingSet, hconv, hXc])
  have hj1 : (1 : ℕ) ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, hr.one_le_q⟩
  have hε := hr.ε_mem 1 hj1
  obtain ⟨ha, -, hA, -⟩ := consts_facts (j := 1) hθς hL hf hc hp
  have hκ : 0 < kappaDm1 P Lf Lc Lh p m := by
    unfold kappaDm1
    have := P.σmin_pos
    exact mul_pos (by positivity) (Real.rpow_pos_of_pos
      (div_pos (div_pos ha hA) (by norm_num)) _)
  have hδ : 0 < P.η₁ * (kappaDm1 P Lf Lc Lh p m * ε 1 ^ (((p : ℝ) + 1) / p)) :=
    mul_pos P.η₁_pos (mul_pos hκ (Real.rpow_pos_of_pos hε.1 _))
  obtain ⟨kε, hhit, hF, hD⟩ := hr.run.toIsARRun.exists_isFirstHit_of_decrease
    (σmax := arqpcSigmaMax P Lf Lc Lh p m)
    (fun k hk => sigma_le_arqpcSigmaMax hr hf hc hL hk k le_rfl)
    (V := fun k => f (x k) + h (c (x k))) (Vlow := wlow) hδ
    (fun k hk => w_succ_le hr hk) (fun k hk => hw _ (hr.mem hk))
    (fun k hk hs => by
      have hk' : ∀ i ≤ k, ¬ arqpcStop f c h p q P ε x s σ δ d i :=
        fun i hi => hk i (hi.trans k.le_succ)
      have h1 : ¬ algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d (k + 1) :=
        fun h' => hk (k + 1) le_rfl (Or.inl h')
      have hδ1 := delta_one_eq hr hδ₀ hpol (k + 1) fun i hi => hk i hi.le
      exact ((lemma_14_1_9 hr hθς hf hc hL hk' hs h1).1 hq hδ1).2)
  refine ⟨kε, hhit, ?_, hF, hD⟩
  -- termination is in Step 1, with `δ_{k_ε,1} = 1`
  have hbef := hhit.2
  have h1 : algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d kε := by
    rcases hhit.1 with h1 | h2
    · exact h1
    · by_contra hn
      exact ne_of_lt ((lemma_14_1_4 hr hf.contDiff hc.contDiff hL hS).1 hq hconv hXc kε hbef hn) h2
  have happ := isEpsDeltaApprox_of_stop₁ hr hbef h1 1 hj1
  rw [delta_one_eq hr hδ₀ hpol kε hbef] at happ
  simpa using happ

/-- **Theorem 14.1.10, part 2** of [cartis2022evaluation] (`h` nonconvex or `q > 1`). Under
f.D1pL, c.D1pL, h.L, h.S0, w.Bb (on `X`) and `θ < ς` (the radius policy (14.1.28) holds for
every run: `algorithm_14_1_1.radius_policy`), if
`0 < m_ε ≤ ε_j^{j+1}` for `j ∈ [1 : q]` (e.g. `m_ε = min_j ε_j^{j+1}`), the ARqpC run terminates
at some `k_ε` at which `x_{k_ε}` is an `(ε, δ_ε)`-approximate `q`-th order minimizer (14.1.9)
for some `δ_ε ∈ (0, 1]^q`, using at most `κ_A (w(x₀) - w_low)/δ + κ_C` evaluations of `f` and `c`
(14.1.36) and at most `(w(x₀) - w_low)/δ + 2` evaluations of their derivatives (14.1.37), where
`δ = η₁ κ_{Δm} m_ε` (`κ_{Δm} = kappaDm2`, so that `1/(η₁ κ_{Δm}) = κ^{s,2}` with the book's `3j!`
read as `3q!` and `(1 - θ)` as `(ς - θ)`). This is `O(max_j ε_j^{-(j+1)})`. -/
theorem theorem_14_1_10_ii (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hθς : P.θ < P.ς) (hf : Chapter12.AssumptionD1pL f p Lf)
    (hc : AssumptionCD1pL c p Lc) (hL : AssumptionHLip h Lh) (hS : AssumptionHS0 h) {wlow : ℝ}
    (hw : AssumptionWBb f c h X wlow) {mε : ℝ} (hmε0 : 0 < mε)
    (hmε : ∀ j ∈ Finset.Icc 1 q, mε ≤ ε j ^ (j + 1)) :
    ∃ kε, Optimization.IsFirstHit (arqpcStop f c h p q P ε x s σ δ d) kε ∧
      (∃ δε : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, 0 < δε j ∧ δε j ≤ 1) ∧
        Optimization.IsEpsDeltaApproxComposite (ftaylorSeries ℝ f (x kε))
          (ftaylorSeries ℝ c (x kε)) h {e | x kε + e ∈ X} q ε δε) ∧
      (Optimization.funEvalCount kε : ℝ) ≤
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
          ((f (x 0) + h (c (x 0)) - wlow) / (P.η₁ * (kappaDm2 P Lf Lc Lh p q m * mε))) +
        ((|Real.log P.γ₁| + Real.log (arqpcSigmaMax P Lf Lc Lh p m / P.σ₀)) /
          Real.log P.γ₂ + 2) ∧
      (Optimization.derivEvalCount (fun k => P.η₁ ≤ Optimization.arqpRatio
          (fun y => f y + h (c y)) (fun k => arqpcData f c h p (x k) (σ k)) x s k) kε : ℝ) ≤
        (f (x 0) + h (c (x 0)) - wlow) / (P.η₁ * (kappaDm2 P Lf Lc Lh p q m * mε)) + 2 := by
  have hp : 1 ≤ p := hr.one_le_q.trans hr.q_le_p
  have hpol := fun k hk h1 => hr.radius_policy hf hc hL hS (k := k) hk h1
  obtain ⟨ha, -, hA, -, -, hκδ, hκδ1⟩ := consts_facts (j := 1) hθς hL hf hc hp
  have hBq0 : 0 < (P.ς - P.θ) / ((q ! : ℝ) * (compositeLipschitzWp Lf Lc Lh p m +
      arqpcSigmaMax P Lf Lc Lh p m)) * kappaDeltaMin P Lf Lc Lh p m ^ q / 3 := by
    have : 0 < (P.ς - P.θ) / ((q ! : ℝ) * (compositeLipschitzWp Lf Lc Lh p m +
      arqpcSigmaMax P Lf Lc Lh p m)) := div_pos ha (by positivity)
    positivity
  have hκ : 0 < kappaDm2 P Lf Lc Lh p q m := by
    unfold kappaDm2
    have := P.σmin_pos
    exact mul_pos (by positivity) (Real.rpow_pos_of_pos hBq0 _)
  have hδ : 0 < P.η₁ * (kappaDm2 P Lf Lc Lh p q m * mε) :=
    mul_pos P.η₁_pos (mul_pos hκ hmε0)
  obtain ⟨kε, hhit, hF, hD⟩ := hr.run.toIsARRun.exists_isFirstHit_of_decrease
    (σmax := arqpcSigmaMax P Lf Lc Lh p m)
    (fun k hk => sigma_le_arqpcSigmaMax hr hf hc hL hk k le_rfl)
    (V := fun k => f (x k) + h (c (x k))) (Vlow := wlow) hδ
    (fun k hk => w_succ_le hr hk) (fun k hk => hw _ (hr.mem hk))
    (fun k hk hs => by
      have hk' : ∀ i ≤ k, ¬ arqpcStop f c h p q P ε x s σ δ d i :=
        fun i hi => hk i (hi.trans k.le_succ)
      have h1 : ¬ algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d (k + 1) :=
        fun h' => hk (k + 1) le_rfl (Or.inl h')
      have hrad : δ (k + 1) = δs k := (hr.run.radii k hk').1 hs
      have hpol' := hpol k (fun i hi => hk' i hi.le) fun h' => hk' k le_rfl (Or.inl h')
      rw [← hrad] at hpol'
      obtain ⟨j, hj, -, hdec⟩ := (lemma_14_1_9 hr hθς hf hc hL hk' hs h1).2 hpol'
      refine le_trans ?_ hdec
      gcongr
      · exact P.η₁_pos.le
      · exact hmε j hj)
  refine ⟨kε, hhit, ?_, hF, hD⟩
  have hbef := hhit.2
  rcases em (algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d kε) with h1 | h1
  · exact ⟨δ kε, hr.delta_mem hbef, isEpsDeltaApprox_of_stop₁ hr hbef h1⟩
  · have h2 := hhit.1.resolve_left h1
    exact (lemma_14_1_4 hr hf.contDiff hc.contDiff hL hS).2 kε hbef h1 h2

end Theorem

/-! ### Corollary 14.1.11: sharpness for `q = 1` and convex `h` -/

/-- **Global model minimizers are outputs of Algorithm 14.1.2 for `q = 1`** (convex `h` and
`X`). If `x + s ∈ X` and `s` globally minimizes the composite model `m̂` over the feasible steps,
then `(s, 1)` is an output of Algorithm 14.1.2 with `q = 1`: a long step is returned at once, and
for a short step the order-`1` model decrements at `s` are nonpositive (Lemma 14.1.1 applied to
`m̂`), so the displacement `0` passes the order-`1` test with radius `1`. -/
theorem algorithm_14_1_2_of_isMinOn {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {h : ℝᵐ → ℝ} {Lh : ℝ}
    {X : Set ℝⁿ} {p : ℕ} (hp : 1 ≤ p) (hL : AssumptionHLip h Lh) (hconv : ConvexOn ℝ univ h)
    (hX : Convex ℝ X) (P : ARqpCParams) {ε : ℕ → ℝ} (hε : 0 ≤ ε 1) {σ : ℝ} {x s : ℝⁿ}
    (hs : x + s ∈ X)
    (hmin : IsMinOn (Optimization.compositeRegularizedModel (ftaylorSeries ℝ f x)
      (ftaylorSeries ℝ c x) h p σ) {t | x + t ∈ X} s) :
    algorithm_14_1_2 f c h X p 1 P ε σ x s (fun _ => 1) := by
  set mod := Optimization.compositeRegularizedModel (ftaylorSeries ℝ f x) (ftaylorSeries ℝ c x) h
    p σ
  set T : Set ℝⁿ := {t | x + t ∈ X}
  have hsT : s ∈ T := hs
  have hinf : sInf (mod '' T) = mod s :=
    IsLeast.csInf_eq ⟨⟨s, hsT, rfl⟩, by rintro _ ⟨t, ht, rfl⟩; exact isMinOn_iff.1 hmin t ht⟩
  rcases le_or_gt 1 ‖s‖ with hlong | hshort
  · exact ⟨1, ⟨one_pos, le_rfl⟩, Relation.ReflTransGen.single
      (Optimization.DetailedStepTrans.ret hsT (by rw [hinf, one_mul]) hlong)⟩
  set D : Set ℝⁿ := closedBall (0 : ℝⁿ) 1 ∩ {d | x + s + d ∈ X}
  have hnp : ∀ d ∈ D, Optimization.compositeModelDecrement (ftaylorSeries ℝ f x)
      (ftaylorSeries ℝ c x) h p σ 1 s d ≤ 0 := fun d hd =>
    Optimization.compositeTaylorDecrement_one_nonpos_of_isLocalMinOn
      (hX.translate_preimage_right x) hsT
      ((Optimization.contDiff_regularizedModel (D := ftaylorSeries ℝ f x) (p := p)
        (σ := σ)).differentiable (by exact_mod_cast Nat.one_le_iff_ne_zero.1 hp) s)
      (((ftaylorSeries ℝ c x).contDiff_taylorSum p (n := 1)).differentiable one_ne_zero s)
      hconv hL.hasLipschitzConst hmin.isLocalMinOn (by simpa [T, add_assoc] using hd.2)
  have h0 : (0 : ℝⁿ) ∈ D := ⟨by simp, by simpa using hs⟩
  have hsup : sSup ((fun d => Optimization.compositeModelDecrement (ftaylorSeries ℝ f x)
      (ftaylorSeries ℝ c x) h p σ 1 s d) '' D) ≤ 0 :=
    csSup_le ⟨_, ⟨0, h0, rfl⟩⟩ (by rintro _ ⟨d, hd, rfl⟩; exact hnp d hd)
  have hdec0 : Optimization.compositeModelDecrement (ftaylorSeries ℝ f x) (ftaylorSeries ℝ c x)
      h p σ 1 s 0 = 0 := by
    simp [Optimization.compositeModelDecrement_def]
  refine ⟨1, ⟨one_pos, le_rfl⟩, Relation.ReflTransGen.head
    (Optimization.DetailedStepTrans.start hsT (by rw [hinf, one_mul]) hshort)
    (Relation.ReflTransGen.single (Optimization.DetailedStepTrans.finish (d := 0) h0 ?_ ?_ le_rfl))⟩
  · rw [hdec0]
    exact mul_nonpos_of_nonneg_of_nonpos P.ς_pos.le hsup
  · rw [hdec0]
    have := P.ς_pos
    have := P.θ_pos
    positivity

section Corollary

open scoped RealInnerProductSpace

/-- The unit vector `e₁` of `ℝ¹`. -/
private noncomputable def e₁ : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1

private theorem norm_e₁ : ‖e₁‖ = 1 := by simp [e₁]

private theorem inner_e₁ (v : EuclideanSpace ℝ (Fin 1)) : ⟪e₁, v⟫ = v 0 := by
  simp [e₁, EuclideanSpace.inner_single_left]

private theorem norm_eq_abs_inner_e₁ (v : EuclideanSpace ℝ (Fin 1)) : ‖v‖ = |⟪e₁, v⟫| := by
  rw [inner_e₁, EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, Real.sqrt_sq_eq_abs,
    abs_abs]

private theorem smul_e₁_apply (r : ℝ) (i : Fin 1) : (r • e₁) i = r := by
  fin_cases i
  simp [e₁]

private theorem norm_smul_e₁ (r : ℝ) : ‖r • e₁‖ = |r| := by
  rw [norm_smul, norm_e₁, mul_one, Real.norm_eq_abs]

private theorem inner_smul_e₁ (r : ℝ) : ⟪e₁, r • e₁⟫ = r := by
  rw [inner_smul_right, real_inner_self_eq_norm_sq, norm_e₁]
  ring

/-- The vector function `c(y) = g(y₀) e₁` on `ℝ¹`. -/
private noncomputable def liftC (g : ℝ → ℝ) (y : EuclideanSpace ℝ (Fin 1)) :
    EuclideanSpace ℝ (Fin 1) :=
  Optimization.ridge g e₁ y • e₁

private theorem taylorSum_liftC {g : ℝ → ℝ} {p j : ℕ} (hg : ContDiff ℝ p g) (hj1 : 1 ≤ j)
    (hjp : j ≤ p) {y : EuclideanSpace ℝ (Fin 1)} {α : ℝ}
    (hd : Optimization.IsSpikeJetOf p g 1 ⟪e₁, y⟫ α) (t : EuclideanSpace ℝ (Fin 1)) :
    (ftaylorSeries ℝ (liftC g) y).taylorSum j t = (g ⟪e₁, y⟫ - α * ⟪e₁, t⟫) • e₁ := by
  have hgj : ContDiff ℝ j g := hg.of_le (by exact_mod_cast hjp)
  have hd' : Optimization.IsSpikeJetOf j g 1 ⟪e₁, y⟫ α :=
    ⟨hd.1, fun i hi1 hij hi => hd.2 i hi1 (hij.trans hjp) hi⟩
  rw [← taylorPolynomial_eq_taylorSum, show liftC g = fun y => Optimization.ridge g e₁ y • e₁ from
    rfl, taylorPolynomial_smul_const (Optimization.contDiff_ridge hgj).contDiffAt,
    Optimization.taylorPolynomial_ridge_spike hgj le_rfl hj1 hd']
  simp

private theorem taylorSum_zero_fun {j : ℕ} (y t : EuclideanSpace ℝ (Fin 1)) :
    (ftaylorSeries ℝ (fun _ : EuclideanSpace ℝ (Fin 1) => (0 : ℝ)) y).taylorSum j t = 0 := by
  rw [← taylorPolynomial_eq_taylorSum, taylorPolynomial_apply]
  simp


/-- h.L for the norm of `ℝ¹`, with `L_{h,0} = 1`. -/
private theorem assumptionHLip_norm : AssumptionHLip (fun v : EuclideanSpace ℝ (Fin 1) => ‖v‖) 1 :=
  ⟨zero_le_one, fun a b => by rw [one_mul]; exact abs_norm_sub_norm_le a b⟩

private theorem lipschitz_of_iteratedFDerivLipschitzOn {g : ℝ → ℝ} {j : ℕ} {L : ℝ}
    (h : IteratedFDerivLipschitzOn g j L univ) (s t : ℝ) :
    |iteratedDeriv j g s - iteratedDeriv j g t| ≤ L * |s - t| := by
  have := (iteratedFDerivLipschitzOn_iff.1 h) s (mem_univ s) t (mem_univ t)
  rwa [iteratedFDeriv_eq_equiv_comp, Function.comp_apply, Function.comp_apply, ← map_sub,
    LinearIsometryEquiv.norm_map, Real.norm_eq_abs, Real.norm_eq_abs] at this

section LiftC

variable {g : ℝ → ℝ} {p : ℕ} {y : EuclideanSpace ℝ (Fin 1)} {α : ℝ}

private theorem compositeTaylorDecrement_liftC (hg : ContDiff ℝ p g) {j : ℕ} (hj1 : 1 ≤ j)
    (hjp : j ≤ p) (hd : Optimization.IsSpikeJetOf p g 1 ⟪e₁, y⟫ α)
    (t : EuclideanSpace ℝ (Fin 1)) :
    Optimization.compositeTaylorDecrement (ftaylorSeries ℝ (fun _ => (0 : ℝ)) y)
      (ftaylorSeries ℝ (liftC g) y) (fun v => ‖v‖) j t =
      |g ⟪e₁, y⟫| - |g ⟪e₁, y⟫ - α * ⟪e₁, t⟫| := by
  rw [Optimization.compositeTaylorDecrement, taylorSum_zero_fun, taylorSum_zero_fun,
    taylorSum_liftC hg hj1 hjp hd, taylorSum_liftC hg hj1 hjp hd, norm_smul_e₁, norm_smul_e₁,
    inner_zero_right]
  ring_nf

private theorem compositeRegularizedModel_liftC (hg : ContDiff ℝ p g) (hp : 1 ≤ p)
    (hd : Optimization.IsSpikeJetOf p g 1 ⟪e₁, y⟫ α) (σ : ℝ) (t : EuclideanSpace ℝ (Fin 1)) :
    Optimization.compositeRegularizedModel (ftaylorSeries ℝ (fun _ => (0 : ℝ)) y)
      (ftaylorSeries ℝ (liftC g) y) (fun v => ‖v‖) p σ t =
      g ⟪e₁, y⟫ + Optimization.negMonomialRegModel p 1 σ α ⟪e₁, t⟫ +
        (|g ⟪e₁, y⟫ - α * ⟪e₁, t⟫| - (g ⟪e₁, y⟫ - α * ⟪e₁, t⟫)) := by
  rw [Optimization.compositeRegularizedModel_def, Optimization.regularizedModel_def,
    taylorSum_zero_fun, taylorSum_liftC hg hp le_rfl hd, norm_smul_e₁,
    Optimization.negMonomialRegModel, norm_eq_abs_inner_e₁ t]
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one]
  ring

/-- The Step-1 measure of `|liftC g|` at `y`: `φ^1_{w,1}(y) = α` when `g(y₀) ≥ 2 ≥ α ≥ 0`. -/
private theorem compositeTaylorMeasure_liftC (hg : ContDiff ℝ p g) (hp : 1 ≤ p)
    (hd : Optimization.IsSpikeJetOf p g 1 ⟪e₁, y⟫ α) (hg2 : 2 ≤ g ⟪e₁, y⟫) (hα0 : 0 ≤ α)
    (hα2 : α ≤ 2) :
    Optimization.compositeTaylorMeasure (ftaylorSeries ℝ (fun _ => (0 : ℝ)) y)
      (ftaylorSeries ℝ (liftC g) y) (fun v => ‖v‖) 1 1 univ = α := by
  rw [Optimization.compositeTaylorMeasure_eq_sSup]
  have hdec := compositeTaylorDecrement_liftC hg le_rfl hp hd
  refine IsGreatest.csSup_eq ⟨⟨e₁, ⟨by simp [norm_e₁], mem_univ _⟩, ?_⟩, ?_⟩
  · rw [hdec, real_inner_self_eq_norm_sq, norm_e₁, abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith)]
    ring
  · rintro _ ⟨t, ⟨ht, -⟩, rfl⟩
    have ht1 : |⟪e₁, t⟫| ≤ 1 := by
      rw [← norm_eq_abs_inner_e₁]; simpa using ht
    have h1 := (abs_le.1 ht1).1
    have h2 := (abs_le.1 ht1).2
    have hat : α * ⟪e₁, t⟫ ≤ α := by nlinarith
    have hat' : -α ≤ α * ⟪e₁, t⟫ := by nlinarith
    rw [hdec, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith

/-- The global minimizer of the composite model of `|liftC g|` at a spike jet, when the Taylor
model of `g` stays nonnegative at the step. -/
private theorem isMinOn_liftC (hg : ContDiff ℝ p g) (hp : 1 ≤ p)
    (hd : Optimization.IsSpikeJetOf p g 1 ⟪e₁, y⟫ α) {σ : ℝ} (hσ : 0 < σ) (hα : 0 < α)
    (hpos : 0 ≤ g ⟪e₁, y⟫ - α * Optimization.monomialMinimizer p 1 σ α) :
    IsMinOn (Optimization.compositeRegularizedModel (ftaylorSeries ℝ (fun _ => (0 : ℝ)) y)
      (ftaylorSeries ℝ (liftC g) y) (fun v => ‖v‖) p σ) univ
        (Optimization.monomialMinimizer p 1 σ α • e₁) ∧
      Optimization.compositeRegularizedModel (ftaylorSeries ℝ (fun _ => (0 : ℝ)) y)
        (ftaylorSeries ℝ (liftC g) y) (fun v => ‖v‖) p σ
          (Optimization.monomialMinimizer p 1 σ α • e₁) <
      Optimization.compositeRegularizedModel (ftaylorSeries ℝ (fun _ => (0 : ℝ)) y)
        (ftaylorSeries ℝ (liftC g) y) (fun v => ‖v‖) p σ 0 := by
  obtain ⟨hm, hv, -⟩ := Optimization.isMinOn_neg_monomial_add_regularization le_rfl hp hσ hα
  rw [← Optimization.monomialMinimizer] at hm hv
  set τ := Optimization.monomialMinimizer p 1 σ α
  have hτ : 0 < τ := Optimization.monomialMinimizer_pos hσ hα
  have hmod := compositeRegularizedModel_liftC hg hp hd σ
  have hval : Optimization.compositeRegularizedModel (ftaylorSeries ℝ (fun _ => (0 : ℝ)) y)
      (ftaylorSeries ℝ (liftC g) y) (fun v => ‖v‖) p σ (τ • e₁) =
      g ⟪e₁, y⟫ + Optimization.negMonomialRegModel p 1 σ α τ := by
    rw [hmod, inner_smul_e₁, abs_of_nonneg hpos, sub_self, add_zero]
  refine ⟨isMinOn_iff.2 fun t _ => ?_, ?_⟩
  · rw [hval, hmod]
    have := isMinOn_iff.1 hm ⟪e₁, t⟫ (mem_univ _)
    have := le_abs_self (g ⟪e₁, y⟫ - α * ⟪e₁, t⟫)
    linarith
  · rw [hval, hmod, inner_zero_right, mul_zero, sub_zero, hv]
    have := le_abs_self (g ⟪e₁, y⟫)
    have h0 : Optimization.negMonomialRegModel p 1 σ α 0 = 0 := by
      simp [Optimization.negMonomialRegModel]
    rw [h0]
    have : 0 < (((p - 1 + 1 : ℕ) : ℝ) / ((p + 1) * (1 ! : ℕ))) * α * τ ^ 1 := by positivity
    linarith

end LiftC

/-- **Corollary 14.1.11** of [cartis2022evaluation] (slow convergence of ARqpC for `q = 1` and
convex `h`). Let `p ≥ 1` and fix the ARqpC constants `P`. Take `n = m = 1`, `f = 0` (f.D1pL with
constants `1`) and the convex `h = ‖·‖` (h.L with `L_{h,0} = 1`, h.S0). There is `L ≥ 1`
(depending only on `p` and `P`) such that for every `ε ∈ (0, 1]` (all `ε_1 = ε`) some
`c : ℝ¹ → ℝ¹` satisfying c.D1pL with constants `L`, with `‖c(0)‖ ≤ L` (so
`w(x₀) - w_low ≤ L` independently of `ε`) and `c(y)₀ ≥ 2` (so w.Bb holds with `w_low = 0`),
admits an ARqpC run (Algorithm 14.1.1 with `q = 1`, `δ₀ = 1`, Step 2 computed by
Algorithm 14.1.2) from `x₀ = 0` whose iterations are all successful (`ρ_k = 1`) and which
first terminates at `k_ε = ⌈ε^{-(p+1)/p}⌉`, where `φ^1_{w,1}(x_{k_ε}) ≤ ε`, while
`φ^1_{w,1}(x_k) > ε` for every `k < k_ε`. So ARqpC needs at least `ε^{-(p+1)/p} + 1`
evaluations of `c` and of its derivatives: the bounds of Theorem 14.1.10 (1) are sharp in
order.

The function `c(y) = g(y₀) e₁` lifts the slow example of Theorem 12.2.15 (data
`Optimization.exists_slowTaylorOrder_interpolant` with `q = 1`, for any `σ₀`), shifted so that
`g ≥ 2`. The steps of that example are admissible ARqpC steps for `w = |c|`: since
`|t| ≥ t`, the composite model `|T_{c,p}(x_k, s)| + σ₀ ‖s‖^{p+1}/(p+1)!` lies above the smooth
model `T_{c,p}(x_k, s) + σ₀ ‖s‖^{p+1}/(p+1)!` and agrees with it at its global minimizer `s_k`,
where `T_{c,p}(x_k, s_k) = c(x_{k+1}) > 0`; so `s_k` is a global minimizer of the composite model
and an output of Algorithm 14.1.2 (`algorithm_14_1_2_of_isMinOn`). Since `c(x_k) ≥ 2 ≥ |c'(x_k)|`,
the measure is `φ^1_{w,1}(x_k) = |c'(x_k)| = ε + ω_k`, as in the smooth case. -/
theorem corollary_14_1_11 {p : ℕ} (hp : 1 ≤ p) (P : ARqpCParams) :
    Chapter12.AssumptionD1pL (fun _ : EuclideanSpace ℝ (Fin 1) => (0 : ℝ)) p (fun _ => 1) ∧
    AssumptionHLip (fun v : EuclideanSpace ℝ (Fin 1) => ‖v‖) 1 ∧
    AssumptionHS0 (fun v : EuclideanSpace ℝ (Fin 1) => ‖v‖) ∧
    ConvexOn ℝ univ (fun v : EuclideanSpace ℝ (Fin 1) => ‖v‖) ∧
    ∃ L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ c : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1),
        AssumptionCD1pL c p (fun _ => L) ∧ ‖c 0‖ ≤ L ∧ (∀ y, 2 ≤ c y 0) ∧
        AssumptionWBb (fun _ => 0) c (fun v => ‖v‖) univ 0 ∧
        ∃ (x s : ℕ → EuclideanSpace ℝ (Fin 1)) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ)
          (d dm : ℕ → ℕ → EuclideanSpace ℝ (Fin 1)),
          algorithm_14_1_1 (fun _ => 0) c (fun v => ‖v‖) univ p 1 P (fun _ => ε) (fun _ => 1)
            x s σ δ δs d dm ∧ x 0 = 0 ∧
          Optimization.IsFirstHit
            (arqpcStop (fun _ => 0) c (fun v => ‖v‖) p 1 P (fun _ => ε) x s σ δ d)
            ⌈ε ^ (-((p + 1 : ℝ) / p))⌉₊ ∧
          (∀ k < ⌈ε ^ (-((p + 1 : ℝ) / p))⌉₊, Optimization.arqpRatio (fun y => 0 + ‖c y‖)
            (fun k => arqpcData (fun _ => 0) c (fun v => ‖v‖) p (x k) (σ k)) x s k = 1) ∧
          ε ^ (-((p + 1 : ℝ) / p)) + 1 ≤
            (Optimization.funEvalCount ⌈ε ^ (-((p + 1 : ℝ) / p))⌉₊ : ℝ) ∧
          ε ^ (-((p + 1 : ℝ) / p)) + 1 ≤ (Optimization.derivEvalCount (fun k => P.η₁ ≤
            Optimization.arqpRatio (fun y => 0 + ‖c y‖)
              (fun k => arqpcData (fun _ => 0) c (fun v => ‖v‖) p (x k) (σ k)) x s k)
            ⌈ε ^ (-((p + 1 : ℝ) / p))⌉₊ : ℝ) ∧
          Optimization.compositeTaylorMeasure
            (ftaylorSeries ℝ (fun _ => (0 : ℝ)) (x ⌈ε ^ (-((p + 1 : ℝ) / p))⌉₊))
            (ftaylorSeries ℝ c (x ⌈ε ^ (-((p + 1 : ℝ) / p))⌉₊)) (fun v => ‖v‖) 1 1 univ ≤ ε ∧
          ∀ k < ⌈ε ^ (-((p + 1 : ℝ) / p))⌉₊, ε < Optimization.compositeTaylorMeasure
            (ftaylorSeries ℝ (fun _ => (0 : ℝ)) (x k)) (ftaylorSeries ℝ c (x k))
            (fun v => ‖v‖) 1 1 univ := by
  have hf0 : Chapter12.AssumptionD1pL (fun _ : EuclideanSpace ℝ (Fin 1) => (0 : ℝ)) p
      (fun _ => 1) :=
    ⟨contDiff_const, fun _ _ => le_rfl, fun j _ => (iteratedFDerivLipschitzOn_iff).2
      fun a _ b _ => by simp⟩
  refine ⟨hf0, assumptionHLip_norm, ⟨Optimization.isSubadditive_norm, norm_zero⟩,
    convexOn_norm convex_univ, ?_⟩
  have hσ₀ := P.σ₀_pos
  obtain ⟨L₀, B, hL₀, hB, hG⟩ := Optimization.exists_slowTaylorOrder_interpolant (q := 1) le_rfl
    hp (c := (p ! : ℝ) / P.σ₀) (by positivity)
  set L : ℝ := max 1 (max L₀ (B + (B + 2))) with hLdef
  refine ⟨L, le_max_left _ _, fun ε hε hε1 => ?_⟩
  have hR : ((p - 1 + 1 : ℕ) : ℝ) = p := by rw [Nat.sub_add_cancel hp]
  set kε : ℕ := ⌈ε ^ (-((p + 1 : ℝ) / p))⌉₊ with hkε
  have hkε1 : 1 ≤ kε := Nat.one_le_iff_ne_zero.2 (by
    rw [hkε]; exact (Nat.ceil_pos.2 (Real.rpow_pos_of_pos hε _)).ne')
  have hkεpos : (0 : ℝ) < kε := by exact_mod_cast hkε1
  set a : ℕ → ℝ := fun k => ε + ε * ((kε : ℝ) - k) / kε with ha
  set st : ℕ → ℝ := fun k => Optimization.monomialMinimizer p 1 P.σ₀ (a k) with hst
  set xr : ℕ → ℝ := fun k => ∑ i ∈ Finset.range k, st i with hxr
  have hxs : ∀ k, xr (k + 1) = xr k + st k := fun k => by
    simp only [hxr, Finset.sum_range_succ]
  have hstc : ∀ k, st k = ((p ! : ℝ) / P.σ₀ * a k) ^ (1 / ((p - 1 + 1 : ℕ) : ℝ)) := fun k => by
    simp only [hst, Optimization.monomialMinimizer, Nat.sub_self, Nat.factorial_zero,
      Nat.cast_one, mul_one]
    congr 1
    field_simp
  obtain ⟨G, hGc, hGL, hGB, hGd, hGf⟩ := hG ε kε xr hε hε1 (by rw [hkε, hR])
    fun k _ => by rw [hxs k, hstc k]
  clear_value kε
  -- the sequence `a_k = ε + ω_k`
  have ha_ge : ∀ k ≤ kε, ε ≤ a k := fun k hk => by
    simp only [ha]
    have : (0 : ℝ) ≤ ε * ((kε : ℝ) - k) / kε := by
      have : (k : ℝ) ≤ kε := by exact_mod_cast hk
      have : 0 ≤ (kε : ℝ) - k := by linarith
      positivity
    linarith
  have ha_gt : ∀ k < kε, ε < a k := fun k hk => by
    simp only [ha]
    have : (0 : ℝ) < ε * ((kε : ℝ) - k) / kε := by
      have : (k : ℝ) < kε := by exact_mod_cast hk
      have : 0 < (kε : ℝ) - k := by linarith
      positivity
    linarith
  have ha_le : ∀ k, a k ≤ 2 := fun k => by
    simp only [ha]
    have : ε * ((kε : ℝ) - k) / kε ≤ ε := by
      rw [div_le_iff₀ hkεpos]
      have : (0 : ℝ) ≤ k := k.cast_nonneg
      nlinarith
    linarith
  have ha_eq : a kε = ε := by simp only [ha]; rw [sub_self, mul_zero, zero_div, add_zero]
  -- the shifted interpolant `g = (B + 2) + G ≥ 2`
  set g : ℝ → ℝ := fun t => (B + 2) + G t with hgdef
  have hg : ContDiff ℝ p g := contDiff_const.add hGc
  have hgder : ∀ j, 1 ≤ j → ∀ t, iteratedDeriv j g t = iteratedDeriv j G t := fun j hj t =>
    iteratedDeriv_const_add (by omega) _
  have hg2 : ∀ t, 2 ≤ g t := fun t => by
    have := hGB 0 (Nat.zero_le p) t
    rw [iteratedDeriv_zero] at this
    simp only [hgdef]
    linarith [(abs_le.1 this).1]
  have hgD : Chapter12.AssumptionD1pL g p (fun _ => L) := by
    refine Chapter12.assumptionD1pL_real hg (fun s t => ?_) (fun j hj t => ?_)
    · rw [hgder p hp, hgder p hp]; exact hGL s t
    · rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [iteratedDeriv_zero]
        have := hGB 0 (Nat.zero_le p) t
        rw [iteratedDeriv_zero] at this
        simp only [hgdef]
        calc |B + 2 + G t| ≤ |B + 2| + |G t| := abs_add_le _ _
          _ ≤ B + (B + 2) := by rw [abs_of_nonneg (by linarith)]; linarith
      · rw [hgder j hj0 t]
        linarith [hGB j hj t]
  have hspike : ∀ k ≤ kε, Optimization.IsSpikeJetOf p g 1 (xr k) (a k) := fun k hk =>
    ⟨by rw [hgder 1 le_rfl, (hGd k hk).1], fun j hj1 hjp hj => by
      rw [hgder j hj1, (hGd k hk).2 j hj1 hjp hj]⟩
  have hgval : ∀ k < kε, g (xr (k + 1)) = g (xr k) - a k * st k := fun k hk => by
    simp only [hgdef]
    rw [hGf k hk, hxs k]
    simp
    ring
  -- the problem
  set c : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1) := liftC g with hcdef
  have hcD : AssumptionCD1pL c p (fun _ => L) := by
    refine ⟨(Optimization.contDiff_ridge hg).smul contDiff_const, fun _ _ =>
      zero_le_one.trans (le_max_left _ _), fun i j hj => ?_⟩
    have hci : (fun y => c y i) = Optimization.ridge g e₁ := funext fun y => smul_e₁_apply _ i
    rw [hci]
    exact Optimization.iteratedFDerivLipschitzOn_ridge hg
      (by exact_mod_cast (Finset.mem_Icc.1 hj).2) norm_e₁.le
      (zero_le_one.trans (le_max_left _ _))
      (lipschitz_of_iteratedFDerivLipschitzOn (hgD.lipschitz j hj))
  have hc0 : ∀ y, c y 0 = g ⟪e₁, y⟫ := fun y => smul_e₁_apply _ 0
  have hnc : ∀ y, ‖c y‖ = g ⟪e₁, y⟫ := fun y => by
    rw [hcdef, liftC, norm_smul_e₁, Optimization.ridge_apply,
      abs_of_nonneg (by linarith [hg2 ⟪e₁, y⟫])]
  -- the iterates
  set x : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => xr k • e₁ with hxdef
  set sv : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => st k • e₁ with hsvdef
  set σs : ℕ → ℝ := fun _ => P.σ₀ with hσs
  have hxe : ∀ k, ⟪e₁, x k⟫ = xr k := fun k => inner_smul_e₁ _
  have hxsv : ∀ k, x (k + 1) = x k + sv k := fun k => by
    simp only [hxdef, hsvdef, hxs k, add_smul]
  have hspk : ∀ k ≤ kε, Optimization.IsSpikeJetOf p g 1 ⟪e₁, x k⟫ (a k) := fun k hk => by
    rw [hxe]; exact hspike k hk
  have hapos : ∀ k ≤ kε, 0 < a k := fun k hk => hε.trans_le (ha_ge k hk)
  have hstpos : ∀ k ≤ kε, 0 < st k := fun k hk =>
    Optimization.monomialMinimizer_pos hσ₀ (hapos k hk)
  have hnext : ∀ k < kε, 0 ≤ g ⟪e₁, x k⟫ - a k * Optimization.monomialMinimizer p 1 P.σ₀ (a k) :=
    fun k hk => by
      rw [hxe, show Optimization.monomialMinimizer p 1 P.σ₀ (a k) = st k from rfl, ← hgval k hk]
      linarith [hg2 (xr (k + 1))]
  have hmin : ∀ k < kε, _ := fun k hk => isMinOn_liftC hg hp (hspk k hk.le) hσ₀
    (hapos k hk.le) (hnext k hk)
  -- the measures
  have hmeas : ∀ k ≤ kε, Optimization.compositeTaylorMeasure
      (ftaylorSeries ℝ (fun _ => (0 : ℝ)) (x k)) (ftaylorSeries ℝ c (x k))
      (fun v => ‖v‖) 1 1 univ = a k := fun k hk =>
    compositeTaylorMeasure_liftC hg hp (hspk k hk) (hg2 _) (hapos k hk).le (ha_le k)
  have hU : ∀ y : EuclideanSpace ℝ (Fin 1), {e : EuclideanSpace ℝ (Fin 1) | y + e ∈ univ} = univ :=
    fun y => by ext; simp
  -- Step-1 witnesses
  have hw : ∀ k j, ∃ e : EuclideanSpace ℝ (Fin 1),
      Optimization.IsApproxMeasureStep
        ((arqpcData (fun _ => 0) c (fun v => ‖v‖) p (x k) (σs k)).dec j) 1 univ P.ς e ∧
      (arqpcData (fun _ => 0) c (fun v => ‖v‖) p (x k) (σs k)).dec j e =
        P.ς * Optimization.decrementMeasure
          ((arqpcData (fun _ => 0) c (fun v => ‖v‖) p (x k) (σs k)).dec j) 1 univ := fun k j =>
    Optimization.exists_isApproxMeasureStep_eq isClosed_univ (mem_univ 0) (starConvex_univ 0)
      zero_le_one (Optimization.continuous_compositeTaylorDecrement _ _ _ j
        assumptionHLip_norm.continuous).continuousOn
      (Optimization.compositeTaylorDecrement_zero_right _ _ _ j) ⟨P.ς_pos.le, P.ς_le_one⟩
  choose d hd hdeq using hw
  set δ : ℕ → ℕ → ℝ := fun _ _ => 1 with hδ
  have hstop₁ : ∀ k ≤ kε, (Optimization.arqpStop₁ P.toARqpParams 1 (fun _ => ε)
      (fun k => arqpcData (fun _ => 0) c (fun v => ‖v‖) p (x k) (σs k)) δ d k ↔ k = kε) := by
    intro k hk
    have hd1 : (arqpcData (fun _ => 0) c (fun v => ‖v‖) p (x k) (σs k)).dec 1 (d k 1) =
        P.ς * a k := by
      rw [hdeq, ← hmeas k hk]; rfl
    simp only [Optimization.arqpStop₁, Optimization.measureTestPasses_iff, Finset.Icc_self,
      Finset.mem_singleton, forall_eq, hd1, hδ, one_pow, mul_one, Nat.factorial_one,
      Nat.cast_one, div_one]
    constructor
    · intro h
      by_contra hne
      have := ha_gt k (lt_of_le_of_ne hk hne)
      nlinarith [P.ς_pos]
    · rintro rfl
      rw [ha_eq]
  -- Step 2: global model minimizers, outputs of Algorithm 14.1.2
  have halg : ∀ k < kε, algorithm_14_1_2 (fun _ => 0) c (fun v => ‖v‖) univ p 1 P (fun _ => ε)
      (σs k) (x k) (sv k) (fun _ => 1) := fun k hk =>
    algorithm_14_1_2_of_isMinOn hp assumptionHLip_norm (convexOn_norm convex_univ) convex_univ P
      (ε := fun _ => ε) hε.le (mem_univ _) (by rw [hU]; exact (hmin k hk).1)
  have hdm : ∀ k, ∃ e : ℕ → EuclideanSpace ℝ (Fin 1), k < kε →
      Optimization.ARqpStep univ P.toARqpParams 1 (fun _ => ε)
        (arqpcData (fun _ => 0) c (fun v => ‖v‖) p (x k) (σs k)) (x k) (sv k) (fun _ => 1) e := by
    intro k
    by_cases hk : k < kε
    · obtain ⟨e, he⟩ := (halg k hk).exists_arqpStep assumptionHLip_norm isClosed_univ hσ₀
        (mem_univ _)
      exact ⟨e, fun _ => he⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose dm hdm using hdm
  -- the ratio
  have hratio : ∀ k < kε, Optimization.arqpRatio (fun y => 0 + ‖c y‖)
      (fun k => arqpcData (fun _ => 0) c (fun v => ‖v‖) p (x k) (σs k)) x sv k = 1 := by
    intro k hk
    have hpred : Optimization.compositeTaylorDecrement (ftaylorSeries ℝ (fun _ => (0 : ℝ)) (x k))
        (ftaylorSeries ℝ c (x k)) (fun v => ‖v‖) p (sv k) = a k * st k := by
      rw [compositeTaylorDecrement_liftC hg hp le_rfl (hspk k hk.le), hxe,
        show ⟪e₁, sv k⟫ = st k from inner_smul_e₁ _,
        ← hgval k hk, abs_of_nonneg (by linarith [hg2 (xr k)]),
        abs_of_nonneg (by linarith [hg2 (xr (k + 1))])]
      rw [hgval k hk]
      ring
    have hpos : 0 < a k * st k := mul_pos (hapos k hk.le) (hstpos k hk.le)
    change Optimization.reductionRatio _ (x k) (sv k)
      (Optimization.compositeTaylorDecrement _ _ _ p (sv k)) = 1
    rw [Optimization.reductionRatio_def, hpred, ← hxsv, hnc, hnc, hxe, hxe, hgval k hk,
      div_eq_one_iff_eq hpos.ne']
    ring
  have hη1 : P.η₁ ≤ 1 := P.η₁_le_η₂.trans P.η₂_lt_one.le
  -- termination
  have hstop₂ : ∀ k < kε, ¬ Optimization.arqpStop₂
      (fun k => arqpcData (fun _ => 0) c (fun v => ‖v‖) p (x k) (σs k)) sv k :=
    fun k hk h2 => (hmin k hk).2.ne h2
  have hfirst : Optimization.IsFirstHit
      (arqpcStop (fun _ => 0) c (fun v => ‖v‖) p 1 P (fun _ => ε) x sv σs δ d) kε :=
    ⟨Or.inl ((hstop₁ kε le_rfl).2 rfl), fun i hi h' => h'.elim
      (fun h1 => hi.ne ((hstop₁ i hi.le).1 h1)) (hstop₂ i hi)⟩
  have hbefore : ∀ k, (∀ i ≤ k, ¬ arqpcStop (fun _ => 0) c (fun v => ‖v‖) p 1 P (fun _ => ε)
      x sv σs δ d i) → k < kε := fun k hk => by
    by_contra hge
    exact hk kε (not_lt.1 hge) hfirst.1
  have hbefore' : ∀ k, (∀ i < k, ¬ arqpcStop (fun _ => 0) c (fun v => ‖v‖) p 1 P (fun _ => ε)
      x sv σs δ d i) → ¬ Optimization.arqpStop₁ P.toARqpParams 1 (fun _ => ε)
        (fun k => arqpcData (fun _ => 0) c (fun v => ‖v‖) p (x k) (σs k)) δ d k → k < kε :=
    fun k hk h1 => by
      have hle : k ≤ kε := by
        by_contra hge
        exact hk kε (not_le.1 hge) hfirst.1
      exact lt_of_le_of_ne hle fun heq => h1 ((hstop₁ k hle).2 heq)
  have hkge : ε ^ (-((p + 1 : ℝ) / p)) ≤ kε := hkε ▸ Nat.le_ceil _
  have hderiv : Optimization.derivEvalCount (fun k => P.η₁ ≤ Optimization.arqpRatio
      (fun y => 0 + ‖c y‖) (fun k => arqpcData (fun _ => 0) c (fun v => ‖v‖) p (x k) (σs k))
        x sv k) kε = kε + 1 := by
    classical
    rw [Optimization.derivEvalCount, Finset.filter_true_of_mem fun k hk => by
      rw [hratio k (Finset.mem_range.1 hk)]; exact hη1, Finset.card_range]
  have hc0L : ‖c 0‖ ≤ L := by
    rw [hnc, inner_zero_right]
    have := hGB 0 (Nat.zero_le p) 0
    rw [iteratedDeriv_zero] at this
    simp only [hgdef]
    linarith [(abs_le.1 this).2, le_max_right L₀ (B + (B + 2)),
      le_max_right 1 (max L₀ (B + (B + 2)))]
  refine ⟨c, hcD, hc0L, fun y => by rw [hc0]; exact hg2 _, fun y _ => by positivity, x, sv, σs, δ,
    fun _ _ => 1, d, dm, ⟨le_rfl, hp, fun _ _ => ⟨hε, hε1⟩, fun _ _ => ⟨one_pos, le_rfl⟩,
    ⟨⟨rfl, fun k hk h1 => hdm k (hbefore' k hk h1), fun k hk => ?_⟩, mem_univ _, rfl,
      fun k _ j _ => by rw [hU]; exact hd k j, fun k hk => ⟨fun _ => rfl, fun hρ =>
        (hρ (le_of_le_of_eq hη1 (hratio k (hbefore k hk)).symm)).elim⟩⟩,
    fun k hk h1 => halg k (hbefore' k hk h1)⟩, by simp [hxdef, hxr], hfirst, hratio,
    by rw [Optimization.funEvalCount_eq]; push_cast; linarith,
    by rw [hderiv]; push_cast; linarith, ?_, fun k hk => ?_⟩
  · beta_reduce
    rw [hxsv]
    exact Optimization.arAcceptance_of_one_le P.toARParams (hratio k (hbefore k hk)).ge (x k)
      (sv k) P.σmin_le_σ₀ hσ₀.le
  · rw [hmeas kε le_rfl, ha_eq]
  · rw [hmeas k hk.le]
    exact ha_gt k hk

end Corollary

end CartisGouldToint.Chapter14

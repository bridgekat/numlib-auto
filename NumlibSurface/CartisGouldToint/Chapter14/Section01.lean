import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.Analysis.Calculus.MultivariateTaylor.LinearComp
import Numlib.Analysis.Calculus.MultivariateTaylor.VectorRemainder
import Numlib.Optimization.ModelBased.HighOrder.ARqp
import Numlib.Optimization.ModelBased.HighOrder.ARqpCComplexity
import Numlib.Optimization.ModelBased.HighOrderStep
import Numlib.Optimization.Complexity.SlowExample.ARp
import Numlib.Optimization.Optimality.CurveConditions
import NumlibSurface.CartisGouldToint.Chapter03.Section02
import NumlibSurface.CartisGouldToint.Chapter12.Section02
import Numlib.Analysis.Calculus.AnchoredLipschitz

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
`Optimization.IsARqpRun` with composite model data `Optimization.arqpcData`, whose Step 2 is the
detailed Step 2 `Optimization.IsARqpCDetailedStep`
(`Numlib.Optimization.ModelBased.HighOrder.ARqpC`). A feasible set `X` (closed, `x₀ ∈ X`) is
carried throughout: `X = univ` is ARqpC, a general `X` is ARqpC-SC of §14.2. The analysis
(Lemmas 14.1.3–14.1.9, Theorem 14.1.10) is the backbone
`Numlib.Optimization.ModelBased.HighOrder.ARqpCComplexity`, stated in normed spaces under the
top-order anchored conditions `LipschitzDerivsAnchored` on `f` and `c`; the results below are its
instances, with the componentwise constants of c.D1pL giving the operator-norm constants
`√m L_{c,j}` (`compositeLipschitzWp_eq`, `compositeLipschitzW_eq`) and the book's constants being
those of the backbone (`kappaDeltaMin_eq`, `stepBound1_eq`, `stepBound2_eq`, `kappaDm1_eq`,
`kappaDm2_eq`).

Assumption f.D1pL is `Chapter12.AssumptionD1pL f p Lf` (constants `L_{f,j} ≥ 1`), and the
maxima `L_f`, `L_c` of (14.1.3) are `Optimization.finMax 1 Lf p` and `Optimization.finMax 0 Lc p`.

## Main definitions

* `AssumptionCD1pL`, `AssumptionHLip`, `AssumptionHS0`, `AssumptionWBb` — c.D1pL, h.L, h.S0, w.Bb;
* `compositeLipschitzW`, `compositeLipschitzWp` — the constants `L_w` (14.1.3), `L_{w,p}`
  (14.1.27);
* `ARqpCParams`, `algorithm_14_1_2` (detailed Step 2), `algorithm_14_1_1` (ARqpC).

## Main results

* `lemma_14_1_1`, `example_14_1_1` — first-order necessary condition and its failure at order 2;
* `lemma_14_1_2` – `lemma_14_1_9`, `theorem_14_1_10_i`, `theorem_14_1_10_ii`;
* `exists_algorithm_14_1_1` — ARqpC(-SC) runs exist; `algorithm_14_1_1.radius_policy` — every run
  satisfies the radius policy (14.1.28) (Lemma 14.1.3 for every output of Algorithm 14.1.2), in
  the stronger form `algorithm_14_1_1.kappaDeltaMin_mul_le_radius` (the radius bound also holds
  after long steps).
* `algorithm_14_1_2_of_isMinOn` — for `q = 1` and convex `h`, `X`, global model minimizers are
  outputs of Algorithm 14.1.2;
* anchored analysis (the book's remark after (14.2.10) that only f.D1pLaB.X is used):
  `AnchoredCompositeBounds` (top-order Lipschitz condition anchored on a set `A ⊆ X₀` and jet
  bounds on `A`, implied by f.D1pL, c.D1pL via `AnchoredCompositeBounds.of_global`; it is the
  backbone `LipschitzDerivsAnchored` for `f` and `c` with jet bounds,
  `anchoredCompositeBounds_iff`), and, with `A`
  the sublevel set `compositeSublevel f c h X x₀` (which contains every iterate,
  `algorithm_14_1_1.mem_compositeSublevel`), `lemma_14_1_6_anchored`,
  `sigma_le_arqpcSigmaMax_anchored`, `lemma_14_1_7_anchored`, `lemma_14_1_8_anchored`,
  `algorithm_14_1_1.kappaDeltaMin_mul_le_radius_anchored`, `lemma_14_1_9_anchored`,
  `theorem_14_1_10_ii_anchored`; the global versions are their instances with `X₀ = ℝⁿ`. Trial
  points need only lie in `X ⊆ X₀`: Taylor's theorem is applied with the Lipschitz condition
  anchored at the iterate (`Optimization.abs_sub_compositeTaylor_le_of_lipschitzAnchored`,
  `Optimization.radius_inequality_of_compositeTaylorMeasure_gt_anchored`);
* `lemma_14_1_2_of_jet`, `lemma_14_1_3_of_jet` (Lemmas 14.1.2–14.1.3 at a point with given jet
  bounds), `exists_algorithm_14_1_1_of_hLip` (ARqpC runs exist for any `f`, `c`, under h.L and
  h.S0),
  `lemma_14_1_4_ii` (Lemma 14.1.4 (ii) needs no smoothness);
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
  Optimization.finMax 1 Lf p + Real.sqrt m * Lh * Optimization.finMax 0 Lc p

/-- The constant `L_{w,p} = L_{f,p} + √m L_{h,0} L_{c,p}` of [cartis2022evaluation], (14.1.27). -/
noncomputable def compositeLipschitzWp (Lf Lc : ℕ → ℝ) (Lh : ℝ) (p m : ℕ) : ℝ :=
  Lf p + Real.sqrt m * Lh * Lc p

/-- `L_{w,p} = L_{f,p} + L_{h,0} (√m L_{c,p})`: the constant of the backbone analysis
(`Optimization.IsARqpRun.sigma_le_of_compositeAnchored`) with the operator-norm constant
`√m L_{c,p}` of `∇^p c`. -/
theorem compositeLipschitzWp_eq {Lf Lc : ℕ → ℝ} {Lh : ℝ} {p : ℕ} :
    compositeLipschitzWp Lf Lc Lh p m = Lf p + Lh * (Real.sqrt m * Lc p) := by
  unfold compositeLipschitzWp; ring

/-- `L_w = L_f + L_{h,0} (√m L_c)`, the jet constant of the backbone analysis. -/
theorem compositeLipschitzW_eq {Lf Lc : ℕ → ℝ} {Lh : ℝ} {p : ℕ} :
    compositeLipschitzW Lf Lc Lh p m =
      Optimization.finMax 1 Lf p + Lh * (Real.sqrt m * Optimization.finMax 0 Lc p) := by
  unfold compositeLipschitzW; ring

/-- `L_{w,p} ≤ L_w`. -/
theorem compositeLipschitzWp_le {Lf Lc : ℕ → ℝ} {Lh : ℝ} {p : ℕ} (hp : 1 ≤ p) (hLh : 0 ≤ Lh) :
    compositeLipschitzWp Lf Lc Lh p m ≤ compositeLipschitzW Lf Lc Lh p m := by
  have hp' : p ∈ Finset.Icc 1 p := Finset.mem_Icc.2 ⟨hp, le_rfl⟩
  unfold compositeLipschitzWp compositeLipschitzW
  have := Optimization.le_finMax (b := 0) (u := Lc) hp'
  gcongr
  exact Optimization.le_finMax hp'

/-- `L_w ≥ 1` as soon as `L_{h,0} ≥ 0` (the maxima in (14.1.3) are taken with `1` and `0`). -/
theorem one_le_compositeLipschitzW_of {Lf Lc : ℕ → ℝ} {Lh : ℝ} {p : ℕ} (hLh : 0 ≤ Lh) :
    1 ≤ compositeLipschitzW Lf Lc Lh p m := by
  unfold compositeLipschitzW
  have h1 : (1 : ℝ) ≤ Optimization.finMax 1 Lf p := Optimization.le_finMax_left
  have h2 : (0 : ℝ) ≤ Optimization.finMax 0 Lc p := Optimization.le_finMax_left
  have : 0 ≤ Real.sqrt m * Lh * Optimization.finMax 0 Lc p := by positivity
  linarith

/-! ### Anchored assumptions -/

/-- The sublevel set `{y ∈ X | w(y) ≤ w(x₀)}` of the composite objective `w = f + h ∘ c` (the set
`𝓛_f(x₀)` of [cartis2022evaluation], (14.2.8), for `w`). -/
def compositeSublevel (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (h : ℝᵐ → ℝ) (X : Set ℝⁿ) (x₀ : ℝⁿ) :
    Set ℝⁿ :=
  {y ∈ X | f y + h (c y) ≤ f x₀ + h (c x₀)}

theorem mem_compositeSublevel {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {h : ℝᵐ → ℝ} {X : Set ℝⁿ}
    {x₀ y : ℝⁿ} :
    y ∈ compositeSublevel f c h X x₀ ↔ y ∈ X ∧ f y + h (c y) ≤ f x₀ + h (c x₀) := Iff.rfl

/-- **Anchored smoothness of the data `f`, `c` of ARqpC** (the form of f.D1pLaB.X of
[cartis2022evaluation], §14.2.1, used by the analysis of ARqpC-SC): `f` and `c` are `C^p` on an
open convex set `X₀`, the anchor set `A ⊆ X₀` (in applications the sublevel set
`compositeSublevel f c h X x₀`, which contains all iterates) satisfies
* `‖∇^p f(x) - ∇^p f(y)‖ ≤ L_{f,p} ‖x - y‖` and `‖∇^p c(x) - ∇^p c(y)‖ ≤ √m L_{c,p} ‖x - y‖` for
  `x ∈ A`, `y ∈ X₀` (the anchored condition (14.2.9) at the top order), and
* `‖∇^i f(x)‖ ≤ L_{f,i-1}` and `‖∇^i c(x)‖ ≤ √m L_{c,i-1}` for `x ∈ A`, `i ∈ [2 : p]` (the bounds
  (14.1.2) on the jets at the iterates, i.e. (14.2.10)),

with `L_{f,p} ≥ 1` and `L_{c,p} ≥ 0`. Under the global f.D1pL and c.D1pL it holds with `X₀ = ℝⁿ`
and any anchor set (`AnchoredCompositeBounds.of_global`). The book's f.D1pLaB.X with constants
`L_{f,j}` (anchored Lipschitz, (14.2.9)) and `B_{f,j}` (bounds, (14.2.10)) on `A = 𝓛_f(x₀)` gives
it with the constants `max(L_{f,i}, B_{f,i+1})` (the bound of order `i` enters as the constant of
order `i - 1`). -/
structure AnchoredCompositeBounds (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (X₀ A : Set ℝⁿ) (p : ℕ)
    (Lf Lc : ℕ → ℝ) : Prop where
  isOpen : IsOpen X₀
  convex : Convex ℝ X₀
  subset : A ⊆ X₀
  contDiffOn_f : ContDiffOn ℝ p f X₀
  contDiffOn_c : ContDiffOn ℝ p c X₀
  one_le : 1 ≤ Lf p
  nonneg : 0 ≤ Lc p
  lipschitz_f : IteratedFDerivLipschitzAnchored f p (Lf p) A X₀
  lipschitz_c : IteratedFDerivLipschitzAnchored c p (Real.sqrt m * Lc p) A X₀
  norm_f : ∀ i ∈ Finset.Icc 2 p, ∀ x ∈ A, ‖iteratedFDeriv ℝ i f x‖ ≤ Lf (i - 1)
  norm_c : ∀ i ∈ Finset.Icc 2 p, ∀ x ∈ A, ‖iteratedFDeriv ℝ i c x‖ ≤ Real.sqrt m * Lc (i - 1)

namespace AnchoredCompositeBounds

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {X₀ A : Set ℝⁿ} {p : ℕ} {Lf Lc : ℕ → ℝ}

/-- The global assumptions f.D1pL and c.D1pL give the anchored ones on `X₀ = ℝⁿ`, for every anchor
set. -/
theorem of_global (hf : Chapter12.AssumptionD1pL f p Lf) (hc : AssumptionCD1pL c p Lc)
    (hp : 1 ≤ p) (A : Set ℝⁿ) : AnchoredCompositeBounds f c univ A p Lf Lc where
  isOpen := isOpen_univ
  convex := convex_univ
  subset := subset_univ A
  contDiffOn_f := hf.contDiff.contDiffOn
  contDiffOn_c := hc.contDiff.contDiffOn
  one_le := hf.one_le p (Finset.mem_Icc.2 ⟨hp, le_rfl⟩)
  nonneg := hc.nonneg p (Finset.mem_Icc.2 ⟨hp, le_rfl⟩)
  lipschitz_f := (hf.lipschitz p (Finset.mem_Icc.2 ⟨hp, le_rfl⟩)).anchored (subset_univ A)
  lipschitz_c := (hc.lipschitz (Finset.mem_Icc.2 ⟨hp, le_rfl⟩)).anchored (subset_univ A)
  norm_f _ hi x _ := hf.norm_iteratedFDeriv_le hi x
  norm_c _ hi x _ := hc.norm_iteratedFDeriv_le hi x

/-- A smaller anchor set. -/
theorem mono (hA : AnchoredCompositeBounds f c X₀ A p Lf Lc) {A' : Set ℝⁿ} (h : A' ⊆ A) :
    AnchoredCompositeBounds f c X₀ A' p Lf Lc where
  isOpen := hA.isOpen
  convex := hA.convex
  subset := h.trans hA.subset
  contDiffOn_f := hA.contDiffOn_f
  contDiffOn_c := hA.contDiffOn_c
  one_le := hA.one_le
  nonneg := hA.nonneg
  lipschitz_f := hA.lipschitz_f.mono_left h
  lipschitz_c := hA.lipschitz_c.mono_left h
  norm_f i hi x hx := hA.norm_f i hi x (h hx)
  norm_c i hi x hx := hA.norm_c i hi x (h hx)

theorem contDiffAt_f (hA : AnchoredCompositeBounds f c X₀ A p Lf Lc) {y : ℝⁿ} (hy : y ∈ X₀) :
    ContDiffAt ℝ p f y :=
  hA.contDiffOn_f.contDiffAt (hA.isOpen.mem_nhds hy)

theorem contDiffAt_c (hA : AnchoredCompositeBounds f c X₀ A p Lf Lc) {y : ℝⁿ} (hy : y ∈ X₀) :
    ContDiffAt ℝ p c y :=
  hA.contDiffOn_c.contDiffAt (hA.isOpen.mem_nhds hy)

/-- The jet bounds `‖∇^i f(x)‖ ≤ L_f`, `‖∇^i c(x)‖ ≤ √m L_c` (`i ∈ [2 : p]`) at anchors `x`. -/
theorem jet_bounds (hA : AnchoredCompositeBounds f c X₀ A p Lf Lc) {x : ℝⁿ} (hx : x ∈ A) :
    (∀ i ∈ Finset.Icc 2 p, ‖ftaylorSeries ℝ f x i‖ ≤ Optimization.finMax 1 Lf p) ∧
    (∀ i ∈ Finset.Icc 2 p, ‖ftaylorSeries ℝ c x i‖ ≤ Real.sqrt m * Optimization.finMax 0 Lc p) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have hi' : i - 1 ∈ Finset.Icc 1 p := by
      have := Finset.mem_Icc.1 hi; exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
    exact (hA.norm_f i hi x hx).trans (Optimization.le_finMax hi')
  · have hi' : i - 1 ∈ Finset.Icc 1 p := by
      have := Finset.mem_Icc.1 hi; exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
    exact (hA.norm_c i hi x hx).trans
      (mul_le_mul_of_nonneg_left (Optimization.le_finMax hi') (Real.sqrt_nonneg _))

/-- The jet bounds on `f` in the form of the backbone analyses: `‖∇^i f(y)‖ ≤ L_f` for
`i ∈ [2 : p]` and `y ∈ A`. -/
theorem jet_f (hA : AnchoredCompositeBounds f c X₀ A p Lf Lc) :
    ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ Optimization.finMax 1 Lf p :=
  fun i hi _ hy => (hA.jet_bounds hy).1 i hi

/-- The anchored condition on `f` in the form of the backbone assumption (orders `[p, p]`). -/
theorem lipschitzDerivsAnchored_f (hA : AnchoredCompositeBounds f c X₀ A p Lf Lc) :
    LipschitzDerivsAnchored f X₀ A p p Lf :=
  ⟨hA.isOpen, hA.convex, hA.subset, fun _ hy => hA.contDiffAt_f hy, fun j hj => by
    obtain rfl : j = p := le_antisymm (Finset.mem_Icc.1 hj).2 (Finset.mem_Icc.1 hj).1
    exact hA.lipschitz_f⟩

/-- The anchored condition on `c` in the form of the backbone assumption (orders `[p, p]`), with
the operator-norm constants `√m L_{c,j}`. -/
theorem lipschitzDerivsAnchored_c (hA : AnchoredCompositeBounds f c X₀ A p Lf Lc) :
    LipschitzDerivsAnchored c X₀ A p p (fun j => Real.sqrt m * Lc j) :=
  ⟨hA.isOpen, hA.convex, hA.subset, fun _ hy => hA.contDiffAt_c hy, fun j hj => by
    obtain rfl : j = p := le_antisymm (Finset.mem_Icc.1 hj).2 (Finset.mem_Icc.1 hj).1
    exact hA.lipschitz_c⟩

theorem sqrt_mul_nonneg (hA : AnchoredCompositeBounds f c X₀ A p Lf Lc) :
    0 ≤ Real.sqrt m * Lc p :=
  mul_nonneg (Real.sqrt_nonneg _) hA.nonneg

/-- `AnchoredCompositeBounds` is the backbone top-order anchored condition
(`LipschitzDerivsAnchored`) on `f` and on `c` (with the operator-norm constants `√m L_{c,j}`),
with `L_{f,p} ≥ 1`, `L_{c,p} ≥ 0`, and the jet bounds at the anchors. -/
theorem _root_.CartisGouldToint.Chapter14.anchoredCompositeBounds_iff :
    AnchoredCompositeBounds f c X₀ A p Lf Lc ↔
      LipschitzDerivsAnchored f X₀ A p p Lf ∧
      LipschitzDerivsAnchored c X₀ A p p (fun j => Real.sqrt m * Lc j) ∧ 1 ≤ Lf p ∧
      0 ≤ Lc p ∧ (∀ i ∈ Finset.Icc 2 p, ∀ x ∈ A, ‖iteratedFDeriv ℝ i f x‖ ≤ Lf (i - 1)) ∧
      ∀ i ∈ Finset.Icc 2 p, ∀ x ∈ A, ‖iteratedFDeriv ℝ i c x‖ ≤ Real.sqrt m * Lc (i - 1) := by
  refine ⟨fun hA => ⟨hA.lipschitzDerivsAnchored_f, hA.lipschitzDerivsAnchored_c, hA.one_le,
    hA.nonneg, hA.norm_f, hA.norm_c⟩, fun ⟨hf, hc, h1, h0, hnf, hnc⟩ => ?_⟩
  have hpp : p ∈ Finset.Icc p p := Finset.mem_Icc.2 ⟨le_rfl, le_rfl⟩
  exact ⟨hf.isOpen, hf.convex, hf.subset, fun y hy => (hf.contDiffAt y hy).contDiffWithinAt,
    fun y hy => (hc.contDiffAt y hy).contDiffWithinAt, h1, h0, hf.lipschitzAnchored p hpp,
    hc.lipschitzAnchored p hpp, hnf, hnc⟩

end AnchoredCompositeBounds

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
orders if `h` (or, for ARqpC-SC, the feasible set `X`) is not convex
(`Optimization.compositeHalvingSet`). (The book's algorithm uses the *known* convexity; if it is
unknown, the algorithm halves at order `1` as well, which is the nonconvex case of the analysis:
every statement below holds for that variant with the nonconvex-case conclusions.) -/
abbrev halvingSet (h : ℝᵐ → ℝ) (X : Set ℝⁿ) : Set ℕ :=
  Optimization.compositeHalvingSet h X

/-- **Algorithm 14.1.2** of [cartis2022evaluation] (detailed Step 2 of ARqpC) as an output
predicate: `(s, δ_s)` is returned by some execution of Algorithm 14.1.2 for the model
`m̂ = compositeRegularizedModel (ftaylorSeries ℝ f x) (ftaylorSeries ℝ c x) h p σ` over the
feasible steps `{s | x + s ∈ X}` (displacements `{d | x + s + d ∈ X}`), with model decrements
(14.1.14) and halving set `halvingSet h X`. It is the backbone transition system
`Optimization.DetailedStepTrans`, whose `h = 0`, `J = {j ≥ 3}` instance is Algorithm 12.2.3. -/
abbrev algorithm_14_1_2 (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (h : ℝᵐ → ℝ) (X : Set ℝⁿ) (p q : ℕ)
    (P : ARqpCParams) (ε : ℕ → ℝ) (σ : ℝ) (x s : ℝⁿ) (δs : ℕ → ℝ) : Prop :=
  Optimization.IsARqpCDetailedStep f c h X p q P.toARqpParams ε (halvingSet h X) σ x s δs

/-- The termination test of ARqpC at iteration `k` (Step 1 or Step 2,
`Optimization.arqpcStop_iff`). -/
abbrev arqpcStop (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (h : ℝᵐ → ℝ) (p q : ℕ) (P : ARqpCParams)
    (ε : ℕ → ℝ) (x s : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ : ℕ → ℕ → ℝ) (d : ℕ → ℕ → ℝⁿ) (k : ℕ) : Prop :=
  Optimization.arqpcStop f c h P.toARqpParams p q ε x s σ δ d k

/-- **Algorithm 14.1.1 (ARqpC)** of [cartis2022evaluation] (with a closed feasible set `X`: the
ARqpC-SC variant of §14.2; `X = univ` is ARqpC) as a run predicate on the iterates `x`, steps
`s`, weights `σ`, Step-1 radii `δ` and optimality displacements `d`, and Step-2 radii `δs` and
model displacements `dm`: the backbone ARqpC run `Optimization.IsARqpCRun` with the halving set
`halvingSet h X`. Given `1 ≤ q ≤ p`, `ε ∈ (0, 1]^q`, `δ₀ ∈ (0, 1]^q`: the run is the ARqp run
`Optimization.IsARqpRun` for `w = f + h ∘ c` with composite model data (Step 1: (14.1.10);
Step 2: (14.1.12)–(14.1.13), termination if `m̂_k(s_k) = m̂_k(0)`; Steps 3–4:
(14.1.15)–(14.1.16), radii `δ_{k+1} = δ_{s_k}` after success), and the Step-2 pair
`(s_k, δ_{s_k})` is an output of Algorithm 14.1.2 at every iteration reaching Step 2.
(Closedness of `X` is not part of the predicate: it is needed only for the existence of runs,
`exists_algorithm_14_1_1`.) -/
abbrev algorithm_14_1_1 (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (h : ℝᵐ → ℝ) (X : Set ℝⁿ) (p q : ℕ)
    (P : ARqpCParams) (ε δ₀ : ℕ → ℝ) (x s : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ)
    (d dm : ℕ → ℕ → ℝⁿ) : Prop :=
  Optimization.IsARqpCRun f c h X p q P.toARqpParams (halvingSet h X) ε δ₀ x s σ δ δs d dm

/-! ### Lemmas 14.1.2 and 14.1.3: model decrease and existence of a step -/

section Step

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {h : ℝᵐ → ℝ} {p : ℕ} {Lf Lc : ℕ → ℝ} {Lh : ℝ}

/-- `L_w ≥ 1` under f.D1pL, c.D1pL and h.L. -/
theorem one_le_compositeLipschitzW
    (hf : Chapter12.AssumptionD1pL f p Lf)
    (hc : AssumptionCD1pL c p Lc) (hL : AssumptionHLip h Lh) (hp : 1 ≤ p) :
    1 ≤ compositeLipschitzW Lf Lc Lh p m := by
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 p := Finset.mem_Icc.2 ⟨le_rfl, hp⟩
  have hf1 := (hf.one_le 1 h1).trans (Optimization.le_finMax (b := 1) (u := Lf) h1)
  have hc1 := (hc.nonneg 1 h1).trans (Optimization.le_finMax (b := 0) (u := Lc) h1)
  have := hL.nonneg
  unfold compositeLipschitzW
  have : 0 ≤ Real.sqrt m * Lh * Optimization.finMax 0 Lc p := by positivity
  linarith

/-- **Lemma 14.1.2** of [cartis2022evaluation] at a point with given jet bounds: under h.L and
h.S0, if `‖∇^i f(x)‖ ≤ K_f` and `‖∇^i c(x)‖ ≤ K_c` for `i ∈ [2 : p]` (`K_f ≥ 1`, `K_c ≥ 0`), then
for every `σ ≥ 0`, `s` with `‖s‖ ≤ 1`, `j ∈ [1 : p]`, `α > 0`,
`δ ∈ (0, min(1, α/(4(3(K_f + L_{h,0} K_c) + σ)))]` and `d` with `‖d‖ ≤ δ` and
`ΔT_{m̂,j}(s, d) ≥ α δ^j/j!`: `m̂(s) - m̂(s + d) ≥ ½ α δ^j/j!`. -/
theorem lemma_14_1_2_of_jet (hL : AssumptionHLip h Lh) (hS : AssumptionHS0 h) {x : ℝⁿ}
    {Kf Kc : ℝ} (hKf : 1 ≤ Kf) (hKc : 0 ≤ Kc)
    (hDf : ∀ i ∈ Finset.Icc 2 p, ‖ftaylorSeries ℝ f x i‖ ≤ Kf)
    (hDc : ∀ i ∈ Finset.Icc 2 p, ‖ftaylorSeries ℝ c x i‖ ≤ Kc)
    {σ : ℝ} (hσ : 0 ≤ σ) {s : ℝⁿ} (hs : ‖s‖ ≤ 1) {j : ℕ} (hj : j ∈ Finset.Icc 1 p) {α δ : ℝ}
    (hδ0 : 0 < δ) (hδ : δ ≤ min 1 (α / (4 * (3 * (Kf + Lh * Kc) + σ)))) {d : ℝⁿ}
    (hd : ‖d‖ ≤ δ)
    (hdec : α * δ ^ j / j ! ≤ Optimization.compositeModelDecrement (ftaylorSeries ℝ f x)
      (ftaylorSeries ℝ c x) h p σ j s d) :
    α / 2 * δ ^ j / j ! ≤
      Optimization.compositeRegularizedModel (ftaylorSeries ℝ f x) (ftaylorSeries ℝ c x) h p σ s -
        Optimization.compositeRegularizedModel (ftaylorSeries ℝ f x) (ftaylorSeries ℝ c x) h p σ
          (s + d) := by
  have hLh := hL.nonneg
  have hK : 0 < 3 * (Kf + Lh * Kc) + σ := by
    have : 0 ≤ Lh * Kc := mul_nonneg hLh hKc
    linarith
  have hδα : 4 * (3 * (Kf + Lh * Kc) + σ) * δ ≤ α := by
    have := hδ.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  exact Optimization.compositeRegularizedModel_sub_ge_of_decrement_ge hL.hasLipschitzConst hS.1
    hS.2 (zero_le_one.trans hKf) hKc hDf hDc hσ hj hs hδ0.le (hδ.trans (min_le_left _ _)) hδα hd
    hdec

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
  have hp : 1 ≤ p := (Finset.mem_Icc.1 hj).1.trans (Finset.mem_Icc.1 hj).2
  obtain ⟨hDf, hDc⟩ := (AnchoredCompositeBounds.of_global hf hc hp univ).jet_bounds (mem_univ x)
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 p := Finset.mem_Icc.2 ⟨le_rfl, hp⟩
  have hLc0 : 0 ≤ Real.sqrt m * Optimization.finMax 0 Lc p :=
    mul_nonneg (Real.sqrt_nonneg _) Optimization.le_finMax_left
  have e : Optimization.finMax 1 Lf p + Lh * (Real.sqrt m * Optimization.finMax 0 Lc p) =
      compositeLipschitzW Lf Lc Lh p m := by
    unfold compositeLipschitzW; ring
  exact lemma_14_1_2_of_jet hL hS Optimization.le_finMax_left hLc0 hDf hDc hσ hs hj hδ0
    (by rwa [e]) hd hdec

/-- **Lemma 14.1.3** of [cartis2022evaluation] at a point with given jet bounds: under h.L and
h.S0, if `‖∇^i f(x)‖ ≤ K_f` and `‖∇^i c(x)‖ ≤ K_c` for `i ∈ [2 : p]` (`K_f ≥ 1`, `K_c ≥ 0`), then
for a closed feasible set `X ∋ x`, `σ > 0`, `1 ≤ q ≤ p` and `ε ∈ (0, 1]^q`, Algorithm 14.1.2 has
an output `(s, δ_s)` with `δ_{s,j} = 1` at the orders that are never halved and, if `‖s‖ < 1`,
`δ_{s,j} ≥ ςθ/(8(3(K_f + L_{h,0} K_c) + σ)) ε_j` at every halved order `j ∈ [1 : q]`. -/
theorem lemma_14_1_3_of_jet (hL : AssumptionHLip h Lh) (hS : AssumptionHS0 h)
    (P : ARqpCParams) {q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) {ε : ℕ → ℝ}
    (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1) {X : Set ℝⁿ} (hX : IsClosed X) {x : ℝⁿ}
    (hx : x ∈ X) {Kf Kc : ℝ} (hKf : 1 ≤ Kf) (hKc : 0 ≤ Kc)
    (hDf : ∀ i ∈ Finset.Icc 2 p, ‖ftaylorSeries ℝ f x i‖ ≤ Kf)
    (hDc : ∀ i ∈ Finset.Icc 2 p, ‖ftaylorSeries ℝ c x i‖ ≤ Kc) {σ : ℝ} (hσ : 0 < σ) :
    ∃ s δs, algorithm_14_1_2 f c h X p q P ε σ x s δs ∧ (∀ j ∉ halvingSet h X, δs j = 1) ∧
      (‖s‖ < 1 → ∀ j ∈ Finset.Icc 1 q, j ∈ halvingSet h X →
        P.ς * P.θ / (8 * (3 * (Kf + Lh * Kc) + σ)) * ε j ≤ δs j) :=
  Optimization.exists_isARqpCDetailedStep hL hS.1 hS.2 P.toARqpParams hq hqp hε hX hx hKf hKc
    hDf hDc hσ fun _ hj hjJ => Optimization.eq_one_of_notMem_compositeHalvingSet hj hjJ

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
  obtain ⟨hDf, hDc⟩ :=
    (AnchoredCompositeBounds.of_global hf hc (hq.trans hqp) univ).jet_bounds (mem_univ x)
  have hLc0 : 0 ≤ Real.sqrt m * Optimization.finMax 0 Lc p :=
    mul_nonneg (Real.sqrt_nonneg _) Optimization.le_finMax_left
  have e : Optimization.finMax 1 Lf p + Lh * (Real.sqrt m * Optimization.finMax 0 Lc p) =
      compositeLipschitzW Lf Lc Lh p m := by
    unfold compositeLipschitzW; ring
  obtain ⟨s, δs, h1, h2, h3⟩ := lemma_14_1_3_of_jet hL hS P hq hqp hε hX hx
    Optimization.le_finMax_left hLc0 hDf hDc hσ
  rw [e] at h3
  exact ⟨s, δs, h1, h2, h3⟩

/-- An output of Algorithm 14.1.2 satisfies the Step-2 conditions of the ARqp run
(`Optimization.ARqpStep`) for suitable model displacements `dm` (`σ > 0`, `x ∈ X`, `X` closed). -/
theorem algorithm_14_1_2.exists_arqpStep (hL : AssumptionHLip h Lh) {X : Set ℝⁿ}
    (hX : IsClosed X) {P : ARqpCParams} {q : ℕ} {ε : ℕ → ℝ} {σ : ℝ} (hσ : 0 < σ) {x s : ℝⁿ}
    (hx : x ∈ X) {δs : ℕ → ℝ} (hout : algorithm_14_1_2 f c h X p q P ε σ x s δs) :
    ∃ dm : ℕ → ℝⁿ,
      Optimization.ARqpStep X P.toARqpParams q ε (arqpcData f c h p x σ) x s δs dm :=
  Optimization.IsARqpCDetailedStep.exists_arqpStep hL hX hσ hx hout

/-- **Existence of ARqpC(-SC) runs without smoothness assumptions** ([cartis2022evaluation],
Algorithms 14.1.1–14.1.2 are well defined for any data): under h.L and h.S0, for any `f`, `c`, a
closed feasible set `X`, `x₀ ∈ X`, `1 ≤ q ≤ p`, `ε ∈ (0, 1]^q` and `δ₀ ∈ (0, 1]^q`, there is an
ARqpC run from `x₀` (Step 2 is the output of `lemma_14_1_3_of_jet` with the jet bounds at the
current iterate). -/
theorem exists_algorithm_14_1_1_of_hLip (hL : AssumptionHLip h Lh) (hS : AssumptionHS0 h)
    (P : ARqpCParams) {q : ℕ} (hq : 1 ≤ q)
    (hqp : q ≤ p) {ε δ₀ : ℕ → ℝ} (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1)
    (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1) {X : Set ℝⁿ} (hX : IsClosed X) {x₀ : ℝⁿ}
    (hx₀ : x₀ ∈ X) :
    ∃ (x s : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → ℝⁿ), x 0 = x₀ ∧
      algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm :=
  Optimization.exists_isARqpCRun_compositeHalvingSet hL hS.1 hS.2 P.toARqpParams hq hqp hε hδ₀
    hX hx₀

/-- **Existence of ARqpC(-SC) runs** ([cartis2022evaluation], Algorithms 14.1.1–14.1.2 are well
defined): under f.D1pL, c.D1pL, h.L and h.S0, for a closed feasible set `X`, `x₀ ∈ X`,
`1 ≤ q ≤ p`, `ε ∈ (0, 1]^q` and `δ₀ ∈ (0, 1]^q`, there is an ARqpC run from `x₀` (Step-1
displacements are exact maximizers, Step 2 is the output of Lemma 14.1.3, and the regularization
parameters are any admissible updates). The smoothness assumptions are not needed:
`exists_algorithm_14_1_1_of_hLip`. -/
theorem exists_algorithm_14_1_1 (_hf : Chapter12.AssumptionD1pL f p Lf)
    (_hc : AssumptionCD1pL c p Lc)
    (hL : AssumptionHLip h Lh) (hS : AssumptionHS0 h) (P : ARqpCParams) {q : ℕ} (hq : 1 ≤ q)
    (hqp : q ≤ p) {ε δ₀ : ℕ → ℝ} (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1)
    (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1) {X : Set ℝⁿ} (hX : IsClosed X) {x₀ : ℝⁿ}
    (hx₀ : x₀ ∈ X) :
    ∃ (x s : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → ℝⁿ), x 0 = x₀ ∧
      algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm :=
  exists_algorithm_14_1_1_of_hLip hL hS P hq hqp hε hδ₀ hX hx₀

end Step


/-! ### Lemmas 14.1.4–14.1.6 -/

namespace algorithm_14_1_1

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {h : ℝᵐ → ℝ} {X : Set ℝⁿ} {p q : ℕ} {P : ARqpCParams}
  {ε δ₀ : ℕ → ℝ} {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → ℝⁿ}

/-- The Step-1 test of ARqpC at iteration `k` ((14.1.10), normalized). -/
abbrev Stop₁ (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (h : ℝᵐ → ℝ) (p q : ℕ) (P : ARqpCParams)
    (ε : ℕ → ℝ) (x : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ : ℕ → ℕ → ℝ) (d : ℕ → ℕ → ℝⁿ) (k : ℕ) : Prop :=
  Optimization.arqpStop₁ P.toARqpParams q ε (Optimization.arqpcData f c h p x σ) δ d k

end algorithm_14_1_1

section Analysis

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {h : ℝᵐ → ℝ} {X : Set ℝⁿ} {p q : ℕ} {P : ARqpCParams}
  {ε δ₀ : ℕ → ℝ} {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → ℝⁿ}
  {Lf Lc : ℕ → ℝ} {Lh : ℝ}

/-- **Lemma 14.1.4 (ii)** of [cartis2022evaluation] (no smoothness needed): under h.L and h.S0,
if Step 2 of an ARqpC run terminates at iteration `k` (`m̂_k(s_k) = m̂_k(0)`), then `x_k` is an
`(ε, δ)`-approximate `q`-th order minimizer (14.1.9) over `X` for some `δ ∈ (0, 1]^q`. -/
theorem lemma_14_1_4_ii (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hL : AssumptionHLip h Lh) (hS : AssumptionHS0 h) {k : ℕ}
    (hk : ∀ i < k, ¬ arqpcStop f c h p q P ε x s σ δ d i)
    (h1 : ¬ algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d k)
    (heq : Optimization.compositeRegularizedModel (ftaylorSeries ℝ f (x k))
        (ftaylorSeries ℝ c (x k)) h p (σ k) (s k) =
      Optimization.compositeRegularizedModel (ftaylorSeries ℝ f (x k))
        (ftaylorSeries ℝ c (x k)) h p (σ k) 0) :
    ∃ δ' : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, 0 < δ' j ∧ δ' j ≤ 1) ∧
      Optimization.IsEpsDeltaApproxComposite (ftaylorSeries ℝ f (x k))
        (ftaylorSeries ℝ c (x k)) h {e | x k + e ∈ X} q ε δ' :=
  hr.run.exists_isEpsDeltaApproxComposite_of_stop₂ hL hS.1 hS.2 hr.q_le_p
    (fun j hj => (hr.ε_mem j hj).1) hk h1 heq

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
          (ftaylorSeries ℝ c (x k)) h {e | x k + e ∈ X} q ε δ') :=
  ⟨fun hq hconv hX _ hk h1 => hr.run.compositeModel_lt_of_convex hL hconv hX
    (fun _ _ => hfC.contDiffAt) (fun _ _ => hcC.contDiffAt) hq (hr.one_le_q.trans hr.q_le_p)
    (fun j hj => (hr.ε_mem j hj).1) hr.δ₀_mem hk h1,
    fun _ hk h1 heq => lemma_14_1_4_ii hr hL hS hk h1 heq⟩

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
        (ftaylorSeries ℝ c (x k)) h p (s k)) :=
  hr.run.compositeTaylorDecrement_ge hk h1

/-- The objective `w = f + h ∘ c` does not increase along an ARqpC run (before termination). -/
theorem algorithm_14_1_1.w_succ_le (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpcStop f c h p q P ε x s σ δ d i) :
    f (x (k + 1)) + h (c (x (k + 1))) ≤ f (x k) + h (c (x k)) :=
  hr.run.composite_objective_succ_le hk

/-- The iterates of an ARqpC run lie in the sublevel set `{y ∈ X | w(y) ≤ w(x₀)}` up to (and
including) the first termination index. -/
theorem algorithm_14_1_1.mem_compositeSublevel
    (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i < k, ¬ arqpcStop f c h p q P ε x s σ δ d i) :
    x k ∈ compositeSublevel f c h X (x 0) :=
  hr.run.mem_compositeSublevel hk

/-- **Lemma 14.1.6** of [cartis2022evaluation] (upper bound on the regularization parameter for
ARqpC). Under f.DpL (`f` is `C^p` with `L_{f,p}`-Lipschitz `∇^p f`), c.DpL (componentwise
constant `L_{c,p}`) and h.L, every ARqpC run satisfies
`σ_k ≤ σ_max = max(σ₀, γ₃ L_{w,p}/(1 - η₂))` (14.1.26) up to (and including) its first
termination index, with `L_{w,p} = L_{f,p} + √m L_{h,0} L_{c,p}` (14.1.27). -/
theorem lemma_14_1_6 (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hfC : ContDiff ℝ p f) (hLfp : IteratedFDerivLipschitzOn f p (Lf p) univ)
    (hcC : ContDiff ℝ p c)
    (hLcp : ∀ i, IteratedFDerivLipschitzOn (fun y => c y i) p (Lc p) univ)
    (hL : AssumptionHLip h Lh) {K : ℕ} (hK : ∀ i < K, ¬ arqpcStop f c h p q P ε x s σ δ d i) :
    ∀ k ≤ K, σ k ≤ Optimization.arSigmaMax P.toARParams (compositeLipschitzWp Lf Lc Lh p m) := by
  have hpp : ∀ j ∈ Finset.Icc p p, j = p := fun j hj =>
    le_antisymm (Finset.mem_Icc.1 hj).2 (Finset.mem_Icc.1 hj).1
  exact hr.run.sigma_le_of_compositeAnchored (A := univ)
    (LipschitzDerivsAnchored.of_contDiff hfC (fun j hj => hpp j hj ▸ hLfp) univ)
    (LipschitzDerivsAnchored.of_contDiff hcC (L := fun j => Real.sqrt m * Lc j) (fun j hj =>
      hpp j hj ▸ iteratedFDerivLipschitzOn_of_forall_component (fun _ _ => hcC.contDiffAt) hLcp)
      univ)
    hL compositeLipschitzWp_eq.ge (subset_univ X) (fun _ _ _ => mem_univ _) hK

/-- **Lemma 14.1.6** of [cartis2022evaluation] under the anchored assumptions
(`AnchoredCompositeBounds` on the sublevel set of `w` at `x₀`, with an open convex `X₀ ⊇ X`):
every ARqpC run satisfies `σ_k ≤ σ_max = max(σ₀, γ₃ L_{w,p}/(1 - η₂))` up to (and including) its
first termination index. -/
theorem lemma_14_1_6_anchored (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    {X₀ : Set ℝⁿ} (hA : AnchoredCompositeBounds f c X₀ (compositeSublevel f c h X (x 0)) p Lf Lc)
    (hX : X ⊆ X₀) (hL : AssumptionHLip h Lh) {K : ℕ}
    (hK : ∀ i < K, ¬ arqpcStop f c h p q P ε x s σ δ d i) :
    ∀ k ≤ K, σ k ≤ Optimization.arSigmaMax P.toARParams (compositeLipschitzWp Lf Lc Lh p m) :=
  hr.run.sigma_le_of_compositeAnchored hA.lipschitzDerivsAnchored_f hA.lipschitzDerivsAnchored_c hL
    compositeLipschitzWp_eq.ge hX
    (fun _ hy hw => ⟨hy, hw⟩) hK

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

/-- `κ_{δ,min}` is the backbone radius constant `κ_δ(σ_max)` of the composite constant `L_w`. -/
theorem kappaDeltaMin_eq (P : ARqpCParams) (Lf Lc : ℕ → ℝ) (Lh : ℝ) (p m : ℕ) :
    kappaDeltaMin P Lf Lc Lh p m = Optimization.arqpKappaDelta P.toARqpParams
      (compositeLipschitzW Lf Lc Lh p m) (arqpcSigmaMax P Lf Lc Lh p m) := rfl

/-- Lemma 14.1.6 under f.D1pL and c.D1pL: `σ_k ≤ σ_max` up to termination. -/
theorem sigma_le_arqpcSigmaMax (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hf : Chapter12.AssumptionD1pL f p Lf)
    (hc : AssumptionCD1pL c p Lc) (hL : AssumptionHLip h Lh) {K : ℕ}
    (hK : ∀ i < K, ¬ arqpcStop f c h p q P ε x s σ δ d i) :
    ∀ k ≤ K, σ k ≤ arqpcSigmaMax P Lf Lc Lh p m := by
  have hp' : p ∈ Finset.Icc 1 p := Finset.mem_Icc.2 ⟨hr.one_le_q.trans hr.q_le_p, le_rfl⟩
  exact lemma_14_1_6 hr hf.contDiff (hf.lipschitz p hp') hc.contDiff
    (fun i => hc.lipschitz_component i p hp') hL hK

/-- Lemma 14.1.6 under the anchored assumptions: `σ_k ≤ σ_max` up to termination. -/
theorem sigma_le_arqpcSigmaMax_anchored (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    {X₀ : Set ℝⁿ} (hA : AnchoredCompositeBounds f c X₀ (compositeSublevel f c h X (x 0)) p Lf Lc)
    (hX : X ⊆ X₀) (hL : AssumptionHLip h Lh) {K : ℕ}
    (hK : ∀ i < K, ¬ arqpcStop f c h p q P ε x s σ δ d i) :
    ∀ k ≤ K, σ k ≤ arqpcSigmaMax P Lf Lc Lh p m :=
  lemma_14_1_6_anchored hr hA hX hL hK

/-- **Lemma 14.1.7** of [cartis2022evaluation] (a useful inequality for ARqpC), **corrected**,
under the anchored assumptions (`AnchoredCompositeBounds` on the sublevel set of `w` at `x₀`,
with an open convex `X₀ ⊇ X`) and h.L: if iteration `k` of an ARqpC run is successful, the run has
not terminated up to `k`, and the Step-1 test fails at `k + 1`, then for some `j ∈ [1 : q]`
`(ς - θ) ε_j δ_{k+1,j}^j/j! < (L_{w,p} + σ_max) ∑_{ℓ=1}^j δ_{k+1,j}^ℓ/ℓ! ‖s_k‖^{p-ℓ+1} +
2 √m L_{h,0} L_{c,p}/(p+1)! ‖s_k‖^{p+1}` (14.1.30). (The printed `(1 - θ)` presumes `ς = 1`, and
the last term lacks the factor `2`. For short steps the inequality comes from the model test
(14.1.13); for long steps, `‖s_k‖ ≥ 1`, it holds trivially.) -/
theorem lemma_14_1_7_anchored (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    {X₀ : Set ℝⁿ} (hA : AnchoredCompositeBounds f c X₀ (compositeSublevel f c h X (x 0)) p Lf Lc)
    (hX : X ⊆ X₀) (hL : AssumptionHLip h Lh) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpcStop f c h p q P ε x s σ δ d i)
    (hsucc : P.η₁ ≤ Optimization.arqpRatio (fun y => f y + h (c y))
      (fun k => arqpcData f c h p (x k) (σ k)) x s k)
    (h1 : ¬ algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d (k + 1)) :
    ∃ j ∈ Finset.Icc 1 q, (P.ς - P.θ) * ε j * δ (k + 1) j ^ j / j ! <
      (compositeLipschitzWp Lf Lc Lh p m + arqpcSigmaMax P Lf Lc Lh p m) *
        ∑ ℓ ∈ Finset.Icc 1 j, δ (k + 1) j ^ ℓ / ℓ ! * ‖s k‖ ^ (p - ℓ + 1) +
      2 * Real.sqrt m * Lh * Lc p / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) := by
  obtain ⟨j, hj, hlt⟩ := hr.run.exists_composite_radius_ineq hA.lipschitzDerivsAnchored_f
    hA.lipschitzDerivsAnchored_c hL hA.one_le
    hA.sqrt_mul_nonneg compositeLipschitzWp_eq.ge hX (fun _ hy hw => ⟨hy, hw⟩) hr.one_le_q
    hr.q_le_p hr.ε_mem hr.δ₀_mem hk hsucc h1
  exact ⟨j, hj, hlt.trans_eq (by ring)⟩

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
  exact lemma_14_1_7_anchored hr (AnchoredCompositeBounds.of_global hf hc
    (hr.one_le_q.trans hr.q_le_p) _) (subset_univ X) hL hk hsucc h1

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

/-- The bounds of (14.1.31) are the backbone `Optimization.arqpcStepBoundUnit` and
`Optimization.arqpcStepBound` of the constants `L_{w,p}`, `L_w`. -/
theorem stepBound1_eq (P : ARqpCParams) (Lf Lc : ℕ → ℝ) (Lh : ℝ) (p m j : ℕ) (εj : ℝ) :
    stepBound1 P Lf Lc Lh p m j εj = Optimization.arqpcStepBoundUnit P.toARqpParams
      (compositeLipschitzWp Lf Lc Lh p m) p j εj := rfl

theorem stepBound2_eq (P : ARqpCParams) (Lf Lc : ℕ → ℝ) (Lh : ℝ) (p m j : ℕ) (εj : ℝ) :
    stepBound2 P Lf Lc Lh p m j εj = Optimization.arqpcStepBound P.toARqpParams
      (compositeLipschitzWp Lf Lc Lh p m) (compositeLipschitzW Lf Lc Lh p m) p j εj := rfl

/-- **Lemma 14.1.8** of [cartis2022evaluation] (lower bound on the step for ARqpC),
**corrected**, under the anchored assumptions (`AnchoredCompositeBounds` on the sublevel set of
`w` at `x₀`, with an open convex `X₀ ⊇ X`) and h.L with `θ < ς`: if iteration `k` of an ARqpC run is
successful, the run has not terminated up to `k` and the Step-1 test fails at `k + 1`, then there
is `j ∈ [1 : q]` such that
* if `δ_{s_k,j} = δ_{k+1,j} = 1` (the policy for `q = 1` and `h` convex),
  `‖s_k‖ ≥ ((ς - θ)/(j! A) ε_j/3)^{1/(p-j+1)}` (first case of (14.1.31));
* if `δ_{k+1,j} ≥ κ_{δ,min} ε_j` (the policy (14.1.28)),
  `‖s_k‖ ≥ ((ς - θ) κ_{δ,min}^j/(3 j! A))^{1/(p-j+1)} ε_j^{(j+1)/(p+1)}` (second case of
  (14.1.31), with the factor `ε_j^{(j+1)/(p+1)}` omitted by the book),
where `A = L_{w,p} + σ_max` and `(1 - θ)` is replaced by `(ς - θ)`. Long steps (`‖s_k‖ ≥ 1`)
satisfy both bounds. -/
theorem lemma_14_1_8_anchored (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hθς : P.θ < P.ς) {X₀ : Set ℝⁿ}
    (hA : AnchoredCompositeBounds f c X₀ (compositeSublevel f c h X (x 0)) p Lf Lc)
    (hX : X ⊆ X₀) (hL : AssumptionHLip h Lh) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpcStop f c h p q P ε x s σ δ d i)
    (hsucc : P.η₁ ≤ Optimization.arqpRatio (fun y => f y + h (c y))
      (fun k => arqpcData f c h p (x k) (σ k)) x s k)
    (h1 : ¬ algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d (k + 1)) :
    ∃ j ∈ Finset.Icc 1 q,
      (δ (k + 1) j = 1 → stepBound1 P Lf Lc Lh p m j (ε j) ≤ ‖s k‖) ∧
      (kappaDeltaMin P Lf Lc Lh p m * ε j ≤ δ (k + 1) j →
        stepBound2 P Lf Lc Lh p m j (ε j) ≤ ‖s k‖) :=
  hr.run.composite_norm_step_ge (Kw := compositeLipschitzW Lf Lc Lh p m)
    hA.lipschitzDerivsAnchored_f hA.lipschitzDerivsAnchored_c hL hA.one_le
    hA.sqrt_mul_nonneg compositeLipschitzWp_eq.ge (one_le_compositeLipschitzW_of hL.nonneg) hX
    (fun _ hy hw => ⟨hy, hw⟩) hr.one_le_q hr.q_le_p hθς hr.ε_mem hr.δ₀_mem hk hsucc h1

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
  exact lemma_14_1_8_anchored hr hθς (AnchoredCompositeBounds.of_global hf hc
    (hr.one_le_q.trans hr.q_le_p) _) (subset_univ X) hL hk hsucc h1

end StepLength2

/-! ### The radius policies -/

section RadiusPolicy

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {h : ℝᵐ → ℝ} {X : Set ℝⁿ} {p q : ℕ} {P : ARqpCParams}
  {ε δ₀ : ℕ → ℝ} {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → ℝⁿ}
  {Lf Lc : ℕ → ℝ} {Lh : ℝ}

/-- **The radii of Algorithm 14.1.2 are bounded below at every iteration reaching Step 2**
([cartis2022evaluation], Lemma 14.1.3), under the anchored assumptions (`AnchoredCompositeBounds`
on the sublevel set of `w` at `x₀`, with an open convex `X₀ ⊇ X`), h.L and h.S0:
`δ_{s_k,j} ≥ κ_{δ,min} ε_j` for `j ∈ [1 : q]`, whatever
the length of the step (radii are only halved while short trial steps are checked). -/
theorem algorithm_14_1_1.kappaDeltaMin_mul_le_radius_anchored
    (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    {X₀ : Set ℝⁿ} (hA : AnchoredCompositeBounds f c X₀ (compositeSublevel f c h X (x 0)) p Lf Lc)
    (hX : X ⊆ X₀)
    (hL : AssumptionHLip h Lh) (hS : AssumptionHS0 h) {k : ℕ}
    (hk : ∀ i < k, ¬ arqpcStop f c h p q P ε x s σ δ d i)
    (h1 : ¬ algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d k) :
    ∀ j ∈ Finset.Icc 1 q, kappaDeltaMin P Lf Lc Lh p m * ε j ≤ δs k j :=
  hr.arqpKappaDelta_mul_le_radius (Kf := Optimization.finMax 1 Lf p)
    (Kc := Real.sqrt m * Optimization.finMax 0 Lc p) hA.lipschitzDerivsAnchored_f
    hA.lipschitzDerivsAnchored_c hL hS.1 hS.2
    compositeLipschitzWp_eq.ge (zero_le_one.trans Optimization.le_finMax_left)
    (mul_nonneg (Real.sqrt_nonneg _) Optimization.le_finMax_left) compositeLipschitzW_eq.ge
    (one_le_compositeLipschitzW_of hL.nonneg) (fun i hi _ hy => (hA.jet_bounds hy).1 i hi)
    (fun i hi _ hy => (hA.jet_bounds hy).2 i hi) hX (fun _ hy hw => ⟨hy, hw⟩) hk h1

/-- **The radii of Algorithm 14.1.2 are bounded below at every iteration reaching Step 2**
([cartis2022evaluation], Lemma 14.1.3): `δ_{s_k,j} ≥ κ_{δ,min} ε_j` for `j ∈ [1 : q]`, whatever
the length of the step (radii are only halved while short trial steps are checked). -/
theorem algorithm_14_1_1.kappaDeltaMin_mul_le_radius
    (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hf : Chapter12.AssumptionD1pL f p Lf) (hc : AssumptionCD1pL c p Lc)
    (hL : AssumptionHLip h Lh) (hS : AssumptionHS0 h) {k : ℕ}
    (hk : ∀ i < k, ¬ arqpcStop f c h p q P ε x s σ δ d i)
    (h1 : ¬ algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d k) :
    ∀ j ∈ Finset.Icc 1 q, kappaDeltaMin P Lf Lc Lh p m * ε j ≤ δs k j := by
  exact hr.kappaDeltaMin_mul_le_radius_anchored (AnchoredCompositeBounds.of_global hf hc
    (hr.one_le_q.trans hr.q_le_p) _) (subset_univ X) hL hS hk h1

/-- **The radius policy (14.1.28)** holds for every ARqpC run (Lemma 14.1.3 for every output of
Algorithm 14.1.2): under f.D1pL, c.D1pL, h.L and h.S0, at every iteration reaching Step 2,
`‖s_k‖ ≥ 1` or `δ_{s_k,j} ≥ κ_{δ,min} ε_j` for all `j ∈ [1 : q]` (in fact the second alternative
always holds, `algorithm_14_1_1.kappaDeltaMin_mul_le_radius`). -/
theorem algorithm_14_1_1.radius_policy
    (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hf : Chapter12.AssumptionD1pL f p Lf) (hc : AssumptionCD1pL c p Lc)
    (hL : AssumptionHLip h Lh) (hS : AssumptionHS0 h) {k : ℕ}
    (hk : ∀ i < k, ¬ arqpcStop f c h p q P ε x s σ δ d i)
    (h1 : ¬ algorithm_14_1_1.Stop₁ f c h p q P ε x σ δ d k) :
    1 ≤ ‖s k‖ ∨ ∀ j ∈ Finset.Icc 1 q, kappaDeltaMin P Lf Lc Lh p m * ε j ≤ δs k j :=
  Or.inr (hr.kappaDeltaMin_mul_le_radius hf hc hL hS hk h1)

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

/-- The constants of Lemma 14.1.9 are the backbone `Optimization.arqpcKappaDmUnit` and
`Optimization.arqpcKappaDm` of the constants `L_{w,p}`, `L_w`. -/
theorem kappaDm1_eq (P : ARqpCParams) (Lf Lc : ℕ → ℝ) (Lh : ℝ) (p m : ℕ) :
    kappaDm1 P Lf Lc Lh p m = Optimization.arqpcKappaDmUnit P.toARqpParams
      (compositeLipschitzWp Lf Lc Lh p m) p := rfl

theorem kappaDm2_eq (P : ARqpCParams) (Lf Lc : ℕ → ℝ) (Lh : ℝ) (p q m : ℕ) :
    kappaDm2 P Lf Lc Lh p q m = Optimization.arqpcKappaDm P.toARqpParams
      (compositeLipschitzWp Lf Lc Lh p m) (compositeLipschitzW Lf Lc Lh p m) p q := rfl

/-- **Lemma 14.1.9** of [cartis2022evaluation] (model and function decreases for ARqpC),
**corrected**, under the anchored assumptions (`AnchoredCompositeBounds` on the sublevel set of `w`
at `x₀`, with an open convex `X₀ ⊇ X`) and h.L with `θ < ς`: if iteration `k` of an ARqpC run is
successful, the run has not terminated up to `k` and the Step-1 test fails at `k + 1`, then:
* (`q = 1`, policy `δ_{k+1,1} = 1`) `ΔT_{w,p}(x_k, s_k) ≥ κ_{Δm} ε_1^{(p+1)/p}` (14.1.32) and
  `w(x_k) - w(x_{k+1}) ≥ η₁ κ_{Δm} ε_1^{(p+1)/p}` (14.1.33), `κ_{Δm} = kappaDm1`;
* (policy (14.1.28): `‖s_k‖ ≥ 1` or `δ_{k+1,j} ≥ κ_{δ,min} ε_j` for all `j`) for some
  `j ∈ [1 : q]`, `ΔT_{w,p}(x_k, s_k) ≥ κ_{Δm} ε_j^{j+1}` and
  `w(x_k) - w(x_{k+1}) ≥ η₁ κ_{Δm} ε_j^{j+1}`, `κ_{Δm} = kappaDm2`.
(The book writes `f`, `L_{f,p}` for `w`, `L_{w,p}`, assumes only f.D1qL, and claims (14.1.32) at
every iteration before termination; `(1 - θ)` is replaced by `(ς - θ)`.) -/
theorem lemma_14_1_9_anchored (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hθς : P.θ < P.ς) {X₀ : Set ℝⁿ}
    (hA : AnchoredCompositeBounds f c X₀ (compositeSublevel f c h X (x 0)) p Lf Lc)
    (hX : X ⊆ X₀) (hL : AssumptionHLip h Lh) {k : ℕ}
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
          (f (x k) + h (c (x k))) - (f (x (k + 1)) + h (c (x (k + 1))))) :=
  ⟨fun hq hδ1 => hr.run.composite_decrease_unit hA.lipschitzDerivsAnchored_f
    hA.lipschitzDerivsAnchored_c hL hA.one_le hA.sqrt_mul_nonneg
    compositeLipschitzWp_eq.ge hX (fun _ hy hw => ⟨hy, hw⟩) hq hr.q_le_p hθς hr.ε_mem hr.δ₀_mem hk
    hsucc h1 hδ1,
    fun hpol => hr.run.composite_decrease (Kw := compositeLipschitzW Lf Lc Lh p m)
    hA.lipschitzDerivsAnchored_f hA.lipschitzDerivsAnchored_c hL
      hA.one_le hA.sqrt_mul_nonneg compositeLipschitzWp_eq.ge
      (one_le_compositeLipschitzW_of hL.nonneg) hX (fun _ hy hw => ⟨hy, hw⟩) hr.one_le_q hr.q_le_p
      hθς hr.ε_mem hr.δ₀_mem hk hsucc h1 hpol⟩

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
  exact lemma_14_1_9_anchored hr hθς (AnchoredCompositeBounds.of_global hf hc
    (hr.one_le_q.trans hr.q_le_p) _) (subset_univ X) hL hk hsucc h1

end Complexity

section Theorem

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {h : ℝᵐ → ℝ} {X : Set ℝⁿ} {p q : ℕ} {P : ARqpCParams}
  {ε δ₀ : ℕ → ℝ} {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → ℝⁿ}
  {Lf Lc : ℕ → ℝ} {Lh : ℝ}

/-- **Theorem 14.1.10, part 1** of [cartis2022evaluation] (`q = 1`, `h` convex; for ARqpC-SC also
`X` convex). Under f.D1pL, c.D1pL, h.L, w.Bb (on `X`) and `θ < ς` (h.S0 is not needed), if the
initial radius is `δ_{0,1} = 1` (Algorithm 14.1.2 then keeps `δ_{s_k,1} = 1`, since it never
halves the first-order radius when `h` and `X` are convex), the ARqpC run terminates at some
`k_ε` with `φ^1_{w,1}(x_{k_ε}) ≤ ε_1`, using at most
`κ_A (w(x₀) - w_low)/δ + κ_C` evaluations of `f` and `c` (14.1.34) and at most
`(w(x₀) - w_low)/δ + 2` evaluations of their derivatives (14.1.35), where
`δ = η₁ κ_{Δm} ε_1^{(p+1)/p}` (`κ_{Δm} = kappaDm1`, so that `1/(η₁ κ_{Δm}) = κ^{s,1}` with the
book's `(1 - θ)` read as `(ς - θ)`), `κ_A = 1 + |log γ₁|/log γ₂` (`κ^{a,1} = κ^{s,1} κ_A`) and
`κ_C = (|log γ₁| + log(σ_max/σ₀))/log γ₂ + 2`. This is `O(ε_1^{-(p+1)/p})`. -/
theorem theorem_14_1_10_i (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hθς : P.θ < P.ς) (hf : Chapter12.AssumptionD1pL f p Lf)
    (hc : AssumptionCD1pL c p Lc) (hL : AssumptionHLip h Lh) {wlow : ℝ}
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
  have hA := AnchoredCompositeBounds.of_global hf hc (hr.one_le_q.trans hr.q_le_p)
    (compositeSublevel f c h X (x 0))
  exact hr.complexity_unit hA.lipschitzDerivsAnchored_f hA.lipschitzDerivsAnchored_c hL hconv hXc
    hA.one_le hA.sqrt_mul_nonneg compositeLipschitzWp_eq.ge (subset_univ X)
    (fun _ hy hw => ⟨hy, hw⟩) hq hθς P.σmin_pos hδ₀
    (Optimization.one_notMem_compositeHalvingSet hconv hXc) hw

/-- **Theorem 14.1.10, part 2** of [cartis2022evaluation] (`h` nonconvex or `q > 1`) under the
anchored assumptions (`AnchoredCompositeBounds` on the sublevel set of `w` at `x₀`, with an open
convex `X₀ ⊇ X`; the book's f.D1pLaB.X), h.L, h.S0, w.Bb (on `X`) and `θ < ς` (the radius policy
(14.1.28) holds for
every run: `algorithm_14_1_1.radius_policy`), if
`0 < m_ε ≤ ε_j^{j+1}` for `j ∈ [1 : q]` (e.g. `m_ε = min_j ε_j^{j+1}`), the ARqpC run terminates
at some `k_ε` at which `x_{k_ε}` is an `(ε, δ_ε)`-approximate `q`-th order minimizer (14.1.9)
for some `δ_ε ∈ (0, 1]^q`, using at most `κ_A (w(x₀) - w_low)/δ + κ_C` evaluations of `f` and `c`
(14.1.36) and at most `(w(x₀) - w_low)/δ + 2` evaluations of their derivatives (14.1.37), where
`δ = η₁ κ_{Δm} m_ε` (`κ_{Δm} = kappaDm2`, so that `1/(η₁ κ_{Δm}) = κ^{s,2}` with the book's `3j!`
read as `3q!` and `(1 - θ)` as `(ς - θ)`). This is `O(max_j ε_j^{-(j+1)})`. -/
theorem theorem_14_1_10_ii_anchored (hr : algorithm_14_1_1 f c h X p q P ε δ₀ x s σ δ δs d dm)
    (hθς : P.θ < P.ς) {X₀ : Set ℝⁿ}
    (hA : AnchoredCompositeBounds f c X₀ (compositeSublevel f c h X (x 0)) p Lf Lc)
    (hX : X ⊆ X₀)
    (hL : AssumptionHLip h Lh) (hS : AssumptionHS0 h) {wlow : ℝ}
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
        (f (x 0) + h (c (x 0)) - wlow) / (P.η₁ * (kappaDm2 P Lf Lc Lh p q m * mε)) + 2 :=
  hr.complexity (Kf := Optimization.finMax 1 Lf p)
    (Kc := Real.sqrt m * Optimization.finMax 0 Lc p) hA.lipschitzDerivsAnchored_f
    hA.lipschitzDerivsAnchored_c hL hS.1 hS.2 hA.one_le
    hA.sqrt_mul_nonneg compositeLipschitzWp_eq.ge (zero_le_one.trans Optimization.le_finMax_left)
    (mul_nonneg (Real.sqrt_nonneg _) Optimization.le_finMax_left) compositeLipschitzW_eq.ge
    (one_le_compositeLipschitzW_of hL.nonneg) (fun i hi _ hy => (hA.jet_bounds hy).1 i hi)
    (fun i hi _ hy => (hA.jet_bounds hy).2 i hi) hX (fun _ hy hw => ⟨hy, hw⟩) hθς P.σmin_pos hw
    hmε0 hmε

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
  exact theorem_14_1_10_ii_anchored hr hθς (AnchoredCompositeBounds.of_global hf hc
    (hr.one_le_q.trans hr.q_le_p) _) (subset_univ X) hL hS hw hmε0 hmε

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
    algorithm_14_1_2 f c h X p 1 P ε σ x s (fun _ => 1) :=
  Optimization.isARqpCDetailedStep_of_isMinOn hp hL hconv hX P.toARqpParams (halvingSet h X) hε hs
    hmin

section Corollary

open scoped RealInnerProductSpace
open Chapter02 (e₀ norm_e₀ norm_smul_e₀ inner_e₀_smul)
open Chapter03 (norm_eq_abs_inner_e₀)

private theorem smul_e₀_apply (r : ℝ) (i : Fin 1) : (r • e₀) i = r := by
  fin_cases i
  simp [e₀]

/-- The vector function `c(y) = g(y₀) e₀` on `ℝ¹`. -/
private noncomputable def liftC (g : ℝ → ℝ) (y : EuclideanSpace ℝ (Fin 1)) :
    EuclideanSpace ℝ (Fin 1) :=
  Optimization.ridge g e₀ y • e₀

private theorem taylorSum_liftC {g : ℝ → ℝ} {p j : ℕ} (hg : ContDiff ℝ p g) (hj1 : 1 ≤ j)
    (hjp : j ≤ p) {y : EuclideanSpace ℝ (Fin 1)} {α : ℝ}
    (hd : Optimization.IsSpikeJetOf p g 1 ⟪e₀, y⟫ α) (t : EuclideanSpace ℝ (Fin 1)) :
    (ftaylorSeries ℝ (liftC g) y).taylorSum j t = (g ⟪e₀, y⟫ - α * ⟪e₀, t⟫) • e₀ := by
  have hgj : ContDiff ℝ j g := hg.of_le (by exact_mod_cast hjp)
  have hd' : Optimization.IsSpikeJetOf j g 1 ⟪e₀, y⟫ α :=
    ⟨hd.1, fun i hi1 hij hi => hd.2 i hi1 (hij.trans hjp) hi⟩
  rw [← taylorPolynomial_eq_taylorSum, show liftC g = fun y => Optimization.ridge g e₀ y • e₀ from
    rfl, taylorPolynomial_smul_const (Optimization.contDiff_ridge hgj).contDiffAt,
    Optimization.taylorPolynomial_ridge_spike hgj le_rfl hj1 hd']
  simp


/-- h.L for the norm of `ℝ¹`, with `L_{h,0} = 1`. -/
private theorem assumptionHLip_norm : AssumptionHLip (fun v : EuclideanSpace ℝ (Fin 1) => ‖v‖) 1 :=
  ⟨zero_le_one, fun a b => by rw [one_mul]; exact abs_norm_sub_norm_le a b⟩

section LiftC

variable {g : ℝ → ℝ} {p : ℕ} {y : EuclideanSpace ℝ (Fin 1)} {α : ℝ}

private theorem compositeTaylorDecrement_liftC (hg : ContDiff ℝ p g) {j : ℕ} (hj1 : 1 ≤ j)
    (hjp : j ≤ p) (hd : Optimization.IsSpikeJetOf p g 1 ⟪e₀, y⟫ α)
    (t : EuclideanSpace ℝ (Fin 1)) :
    Optimization.compositeTaylorDecrement (ftaylorSeries ℝ (fun _ => (0 : ℝ)) y)
      (ftaylorSeries ℝ (liftC g) y) (fun v => ‖v‖) j t =
      |g ⟪e₀, y⟫| - |g ⟪e₀, y⟫ - α * ⟪e₀, t⟫| := by
  rw [Optimization.compositeTaylorDecrement, ← taylorPolynomial_eq_taylorSum,
    taylorPolynomial_zero_fun, taylorPolynomial_zero_fun,
    taylorSum_liftC hg hj1 hjp hd, taylorSum_liftC hg hj1 hjp hd, norm_smul_e₀, norm_smul_e₀,
    inner_zero_right]
  ring_nf

private theorem compositeRegularizedModel_liftC (hg : ContDiff ℝ p g) (hp : 1 ≤ p)
    (hd : Optimization.IsSpikeJetOf p g 1 ⟪e₀, y⟫ α) (σ : ℝ) (t : EuclideanSpace ℝ (Fin 1)) :
    Optimization.compositeRegularizedModel (ftaylorSeries ℝ (fun _ => (0 : ℝ)) y)
      (ftaylorSeries ℝ (liftC g) y) (fun v => ‖v‖) p σ t =
      g ⟪e₀, y⟫ + Optimization.negMonomialRegModel p 1 σ α ⟪e₀, t⟫ +
        (|g ⟪e₀, y⟫ - α * ⟪e₀, t⟫| - (g ⟪e₀, y⟫ - α * ⟪e₀, t⟫)) := by
  rw [Optimization.compositeRegularizedModel_def, Optimization.regularizedModel_def,
    ← taylorPolynomial_eq_taylorSum, taylorPolynomial_zero_fun, taylorSum_liftC hg hp le_rfl hd,
    norm_smul_e₀,
    Optimization.negMonomialRegModel, norm_eq_abs_inner_e₀ t]
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one]
  ring

/-- The Step-1 measure of `|liftC g|` at `y`: `φ^1_{w,1}(y) = α` when `g(y₀) ≥ 2 ≥ α ≥ 0`. -/
private theorem compositeTaylorMeasure_liftC (hg : ContDiff ℝ p g) (hp : 1 ≤ p)
    (hd : Optimization.IsSpikeJetOf p g 1 ⟪e₀, y⟫ α) (hg2 : 2 ≤ g ⟪e₀, y⟫) (hα0 : 0 ≤ α)
    (hα2 : α ≤ 2) :
    Optimization.compositeTaylorMeasure (ftaylorSeries ℝ (fun _ => (0 : ℝ)) y)
      (ftaylorSeries ℝ (liftC g) y) (fun v => ‖v‖) 1 1 univ = α := by
  rw [Optimization.compositeTaylorMeasure_eq_sSup]
  have hdec := compositeTaylorDecrement_liftC hg le_rfl hp hd
  refine IsGreatest.csSup_eq ⟨⟨e₀, ⟨by simp, mem_univ _⟩, ?_⟩, ?_⟩
  · rw [hdec, real_inner_self_eq_norm_sq, norm_e₀, abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith)]
    ring
  · rintro _ ⟨t, ⟨ht, -⟩, rfl⟩
    have ht1 : |⟪e₀, t⟫| ≤ 1 := by
      rw [← norm_eq_abs_inner_e₀]; simpa using ht
    have h1 := (abs_le.1 ht1).1
    have h2 := (abs_le.1 ht1).2
    have hat : α * ⟪e₀, t⟫ ≤ α := by nlinarith
    have hat' : -α ≤ α * ⟪e₀, t⟫ := by nlinarith
    rw [hdec, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith

/-- The global minimizer of the composite model of `|liftC g|` at a spike jet, when the Taylor
model of `g` stays nonnegative at the step. -/
private theorem isMinOn_liftC (hg : ContDiff ℝ p g) (hp : 1 ≤ p)
    (hd : Optimization.IsSpikeJetOf p g 1 ⟪e₀, y⟫ α) {σ : ℝ} (hσ : 0 < σ) (hα : 0 < α)
    (hpos : 0 ≤ g ⟪e₀, y⟫ - α * Optimization.monomialMinimizer p 1 σ α) :
    IsMinOn (Optimization.compositeRegularizedModel (ftaylorSeries ℝ (fun _ => (0 : ℝ)) y)
      (ftaylorSeries ℝ (liftC g) y) (fun v => ‖v‖) p σ) univ
        (Optimization.monomialMinimizer p 1 σ α • e₀) ∧
      Optimization.compositeRegularizedModel (ftaylorSeries ℝ (fun _ => (0 : ℝ)) y)
        (ftaylorSeries ℝ (liftC g) y) (fun v => ‖v‖) p σ
          (Optimization.monomialMinimizer p 1 σ α • e₀) <
      Optimization.compositeRegularizedModel (ftaylorSeries ℝ (fun _ => (0 : ℝ)) y)
        (ftaylorSeries ℝ (liftC g) y) (fun v => ‖v‖) p σ 0 := by
  obtain ⟨hm, hv, -⟩ := Optimization.isMinOn_neg_monomial_add_regularization le_rfl hp hσ hα
  rw [← Optimization.monomialMinimizer] at hm hv
  set τ := Optimization.monomialMinimizer p 1 σ α
  have hτ : 0 < τ := Optimization.monomialMinimizer_pos hσ hα
  have hmod := compositeRegularizedModel_liftC hg hp hd σ
  have hval : Optimization.compositeRegularizedModel (ftaylorSeries ℝ (fun _ => (0 : ℝ)) y)
      (ftaylorSeries ℝ (liftC g) y) (fun v => ‖v‖) p σ (τ • e₀) =
      g ⟪e₀, y⟫ + Optimization.negMonomialRegModel p 1 σ α τ := by
    rw [hmod, inner_e₀_smul, abs_of_nonneg hpos, sub_self, add_zero]
  refine ⟨isMinOn_iff.2 fun t _ => ?_, ?_⟩
  · rw [hval, hmod]
    have := isMinOn_iff.1 hm ⟪e₀, t⟫ (mem_univ _)
    have := le_abs_self (g ⟪e₀, y⟫ - α * ⟪e₀, t⟫)
    linarith
  · rw [hval, hmod, inner_zero_right, mul_zero, sub_zero, hv]
    have := le_abs_self (g ⟪e₀, y⟫)
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

The function `c(y) = g(y₀) e₀` lifts the slow example of Theorem 12.2.15 (data
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
    have hci : (fun y => c y i) = Optimization.ridge g e₀ := funext fun y => smul_e₀_apply _ i
    rw [hci]
    exact Optimization.iteratedFDerivLipschitzOn_ridge hg
      (by exact_mod_cast (Finset.mem_Icc.1 hj).2) norm_e₀.le
      (zero_le_one.trans (le_max_left _ _))
      (fun a b => (hgD.lipschitz j hj).abs_iteratedDeriv_sub_le (mem_univ a) (mem_univ b))
  have hc0 : ∀ y, c y 0 = g ⟪e₀, y⟫ := fun y => smul_e₀_apply _ 0
  have hnc : ∀ y, ‖c y‖ = g ⟪e₀, y⟫ := fun y => by
    rw [hcdef, liftC, norm_smul_e₀, Optimization.ridge_apply,
      abs_of_nonneg (by linarith [hg2 ⟪e₀, y⟫])]
  -- the iterates
  set x : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => xr k • e₀ with hxdef
  set sv : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => st k • e₀ with hsvdef
  set σs : ℕ → ℝ := fun _ => P.σ₀ with hσs
  have hxe : ∀ k, ⟪e₀, x k⟫ = xr k := fun k => inner_e₀_smul _
  have hxsv : ∀ k, x (k + 1) = x k + sv k := fun k => by
    simp only [hxdef, hsvdef, hxs k, add_smul]
  have hspk : ∀ k ≤ kε, Optimization.IsSpikeJetOf p g 1 ⟪e₀, x k⟫ (a k) := fun k hk => by
    rw [hxe]; exact hspike k hk
  have hapos : ∀ k ≤ kε, 0 < a k := fun k hk => hε.trans_le (ha_ge k hk)
  have hstpos : ∀ k ≤ kε, 0 < st k := fun k hk =>
    Optimization.monomialMinimizer_pos hσ₀ (hapos k hk)
  have hnext : ∀ k < kε, 0 ≤ g ⟪e₀, x k⟫ - a k * Optimization.monomialMinimizer p 1 P.σ₀ (a k) :=
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
    simp only [Optimization.arqpStop₁_iff, Finset.Icc_self,
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
        show ⟪e₀, sv k⟫ = st k from inner_e₀_smul _,
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

import Numlib.Optimization.ModelBased.HighOrder.MeasureTest
import Numlib.Analysis.Calculus.MultivariateTaylor.Remainder
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Module.Seminorm.Basic

/-!
# Generalized Taylor models and criticality of composite functions

For a composite objective `w = f + h ∘ c` with `f : E → ℝ`, `c : E → F` smooth and `h : F → ℝ`
Lipschitz (possibly nonsmooth), [cartis2022evaluation] (§14.1) uses the *generalized Taylor model*
`T_{w,j}(x, s) = T_{f,j}(x, s) + h(T_{c,j}(x, s))` ((14.1.5)), in which `h` is kept exactly, and the
criticality measure `φ^δ_{w,j}(x) = w(x) - min_{‖d‖ ≤ δ} T_{w,j}(x, d)` ((14.1.6)).

As for the core `Optimization.taylorMeasure`, everything is built from derivative *data*
`Df : FormalMultilinearSeries ℝ E ℝ`, `Dc : FormalMultilinearSeries ℝ E F`, so that the same
definitions serve the function (`Df = ftaylorSeries ℝ f x`, `Dc = ftaylorSeries ℝ c x`) and the
regularized model of ARqpC at a trial step ((14.1.14)), and the measure is an instance of
`Optimization.decrementMeasure` over a set `S` of feasible displacements (`S = univ`
unconstrained, `S = {d | x + d ∈ X}` in §14.2).

## Main definitions

* `Optimization.IsSubadditive h`: `h (a + b) ≤ h a + h b` (part of the book's assumption h.S0);
* `Optimization.compositeTaylorDecrement Df Dc h j d = T_{w,j}(0) - T_{w,j}(d)`;
* `Optimization.compositeTaylorMeasure Df Dc h j δ S`, the measure (14.1.6);
* `Optimization.IsEpsDeltaApproxComposite Df Dc h S q ε δ`, condition (14.1.9).

## Main results

* `Optimization.abs_compositeTaylorDecrement_le`: the decrement is bounded on balls, so the measure
  is a finite supremum (nonnegative, monotone in `δ` and `S`);
* `Optimization.exists_compositeTaylorMeasure_eq`: attainment in finite dimension;
* `Optimization.compositeTaylorDecrement_one_nonpos_of_isLocalMinOn`: first-order necessity for
  convex `h` (Lemma 14.1.1, for local minimizers over a convex set);
* `Optimization.abs_sub_compositeTaylor_le_of_lipschitz`: the value remainder of the composite
  model (proof of Lemma 14.1.6).
-/

open Set Metric Finset Filter Topology
open scoped Nat

namespace Optimization

section Subadditive

/-- `h` is *subadditive*: `h (a + b) ≤ h a + h b` (the book's assumption h.S0, which also asks
`h 0 = 0`; Mathlib's `Subadditive` is about sequences). -/
def IsSubadditive {F : Type*} [Add F] (h : F → ℝ) : Prop := ∀ a b, h (a + b) ≤ h a + h b

/-- Seminorms are subadditive. -/
theorem _root_.Seminorm.isSubadditive {G : Type*} [AddCommGroup G] [Module ℝ G]
    (p : Seminorm ℝ G) :
    IsSubadditive (p : G → ℝ) :=
  fun a b => map_add_le_add p a b

variable {F : Type*} [NormedAddCommGroup F]

/-- `h` is Lipschitz continuous with the real constant `L ≥ 0`: `|h a - h b| ≤ L ‖a - b‖`
([cartis2022evaluation], assumption h.L, with `L = L_{h,0}`). Real constants are used since they
enter explicit bounds; `HasLipschitzConst.of_lipschitzWith` converts from Mathlib's
`LipschitzWith`. -/
structure HasLipschitzConst (h : F → ℝ) (L : ℝ) : Prop where
  nonneg : 0 ≤ L
  abs_sub_le : ∀ a b, |h a - h b| ≤ L * ‖a - b‖

/-- Mathlib's `LipschitzWith K h` gives `HasLipschitzConst h K`. -/
theorem HasLipschitzConst.of_lipschitzWith {h : F → ℝ} {K : NNReal} (hK : LipschitzWith K h) :
    HasLipschitzConst h K :=
  ⟨K.2, fun a b => by simpa [Real.dist_eq, dist_eq_norm] using hK.dist_le_mul a b⟩

/-- A function with a Lipschitz constant is `LipschitzWith` that constant. -/
theorem HasLipschitzConst.lipschitzWith {h : F → ℝ} {L : ℝ} (hL : HasLipschitzConst h L) :
    LipschitzWith ⟨L, hL.nonneg⟩ h :=
  LipschitzWith.of_dist_le_mul fun a b => by
    rw [Real.dist_eq, dist_eq_norm]
    exact hL.abs_sub_le a b

/-- A function with a Lipschitz constant is continuous. -/
theorem HasLipschitzConst.continuous {h : F → ℝ} {L : ℝ} (hL : HasLipschitzConst h L) :
    Continuous h :=
  hL.lipschitzWith.continuous

variable {h h' : F → ℝ} {Lh : ℝ}

/-- Unfolding lemma for `IsSubadditive`. -/
theorem isSubadditive_iff : IsSubadditive h ↔ ∀ a b, h (a + b) ≤ h a + h b := Iff.rfl

/-- A sum of subadditive functions is subadditive. -/
theorem IsSubadditive.add (hh : IsSubadditive h) (hh' : IsSubadditive h') :
    IsSubadditive (h + h') := fun a b => by
  simp only [Pi.add_apply]
  linarith [hh a b, hh' a b]

/-- The norm is subadditive. -/
theorem isSubadditive_norm : IsSubadditive (fun a : F => ‖a‖) := norm_add_le

/-- An odd subadditive function is additive. -/
theorem IsSubadditive.map_add_of_odd (hh : IsSubadditive h) (hodd : ∀ a, h (-a) = -h a)
    (a b : F) : h (a + b) = h a + h b := by
  have := hh (a + b) (-b)
  rw [add_neg_cancel_right, hodd] at this
  linarith [hh a b]

/-- A subadditive `h` increases by at most `h b` along `b`: `h (a + b) - h a ≤ h b`. -/
theorem IsSubadditive.sub_le (hh : IsSubadditive h) (a b : F) : h (a + b) - h a ≤ h b := by
  linarith [hh a b]

/-- (14.1.4) If `h 0 = 0` and `h` has Lipschitz constant `Lh`, then `|h a| ≤ Lh ‖a‖`. -/
theorem abs_le_of_lipschitz_of_map_zero (h0 : h 0 = 0)
    (hLip : HasLipschitzConst h Lh) (a : F) : |h a| ≤ Lh * ‖a‖ := by
  simpa [h0] using hLip.abs_sub_le a 0

/-- For subadditive Lipschitz `h` with `h 0 = 0`: `h (a + b) - h a ≤ h b ≤ Lh ‖b‖`. -/
theorem IsSubadditive.sub_le_mul_norm (hh : IsSubadditive h) (h0 : h 0 = 0)
    (hLip : HasLipschitzConst h Lh) (a b : F) : h (a + b) - h a ≤ Lh * ‖b‖ :=
  (hh.sub_le a b).trans ((le_abs_self _).trans (abs_le_of_lipschitz_of_map_zero h0 hLip b))

end Subadditive

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-! ### The composite decrement and measure -/

section Decrement

variable (Df : FormalMultilinearSeries ℝ E ℝ) (Dc : FormalMultilinearSeries ℝ E F) (h : F → ℝ)
  (j : ℕ)

/-- The decrease `ΔT_{w,j}(d) = T_{w,j}(0) - T_{w,j}(d)` of the generalized Taylor model
`T_{w,j}(s) = T_{f,j}(s) + h(T_{c,j}(s))` built from the jets `Df`, `Dc` ([cartis2022evaluation],
(14.1.5)–(14.1.6)). `h` is kept exactly: `T_{w,j}` is not a Taylor polynomial of `w`. -/
noncomputable def compositeTaylorDecrement (d : E) : ℝ :=
  (Df.taylorSum j 0 + h (Dc.taylorSum j 0)) - (Df.taylorSum j d + h (Dc.taylorSum j d))

/-- The composite decrement is the Taylor decrement of `Df` plus the decrease of `h`. -/
theorem compositeTaylorDecrement_eq (d : E) :
    compositeTaylorDecrement Df Dc h j d =
      Df.taylorDecrement j d + (h (Dc.taylorSum j 0) - h (Dc.taylorSum j d)) := by
  rw [compositeTaylorDecrement, FormalMultilinearSeries.taylorDecrement]
  ring

/-- With `h = 0` the composite decrement is the Taylor decrement. -/
@[simp]
theorem compositeTaylorDecrement_zero_fun :
    compositeTaylorDecrement Df Dc (0 : F → ℝ) j = Df.taylorDecrement j := by
  ext d
  simp [compositeTaylorDecrement_eq]

/-- The composite decrement vanishes at `d = 0`. -/
@[simp]
theorem compositeTaylorDecrement_zero_right : compositeTaylorDecrement Df Dc h j 0 = 0 :=
  sub_self _

/-- The composite decrement is continuous when `h` is. -/
theorem continuous_compositeTaylorDecrement (hc : Continuous h) :
    Continuous (compositeTaylorDecrement Df Dc h j) :=
  continuous_const.sub ((Df.contDiff_taylorSum j (n := 0)).continuous.add
    (hc.comp (Dc.contDiff_taylorSum j (n := 0)).continuous))

/-- `‖T_{c,j}(0) - T_{c,j}(d)‖ ≤ ∑_{i=1}^j ‖Dc_i‖ ‖d‖^i / i!`. -/
theorem norm_taylorSum_zero_sub_le (d : E) :
    ‖Dc.taylorSum j 0 - Dc.taylorSum j d‖ ≤ ∑ i ∈ Finset.Icc 1 j, ‖Dc i‖ * ‖d‖ ^ i / i ! := by
  rw [Dc.taylorSum_zero_right, Dc.taylorSum_eq_add, sub_add_cancel_left, norm_neg]
  refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
  rw [norm_smul, norm_inv, Real.norm_natCast, inv_mul_eq_div]
  gcongr
  exact Dc.norm_apply_diagonal_le i d

variable {Df Dc h j} {Lh : ℝ}

/-- **Bound on the composite decrement.** If `h` has Lipschitz constant `Lh`, then
`|ΔT_{w,j}(d)| ≤ ∑_{i=1}^j (‖Df_i‖ + Lh ‖Dc_i‖) ‖d‖^i / i!`. -/
theorem abs_compositeTaylorDecrement_le (hLip : HasLipschitzConst h Lh) (d : E) :
    |compositeTaylorDecrement Df Dc h j d| ≤
      ∑ i ∈ Finset.Icc 1 j, (‖Df i‖ + Lh * ‖Dc i‖) * ‖d‖ ^ i / i ! := by
  rw [compositeTaylorDecrement_eq]
  have h1 := Df.abs_taylorDecrement_le j d
  have h2 : |h (Dc.taylorSum j 0) - h (Dc.taylorSum j d)| ≤
      Lh * ∑ i ∈ Finset.Icc 1 j, ‖Dc i‖ * ‖d‖ ^ i / i ! :=
    (hLip.abs_sub_le _ _).trans
      (mul_le_mul_of_nonneg_left (norm_taylorSum_zero_sub_le Dc j d) hLip.nonneg)
  have he : ∑ i ∈ Finset.Icc 1 j, (‖Df i‖ + Lh * ‖Dc i‖) * ‖d‖ ^ i / i ! =
      ∑ i ∈ Finset.Icc 1 j, ‖Df i‖ * ‖d‖ ^ i / i ! +
        Lh * ∑ i ∈ Finset.Icc 1 j, ‖Dc i‖ * ‖d‖ ^ i / i ! := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => by ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- The composite decreases over a feasible ball are bounded above. -/
theorem bddAbove_compositeTaylorDecrement (hLip : HasLipschitzConst h Lh) (δ : ℝ) (S : Set E) :
    BddAbove (compositeTaylorDecrement Df Dc h j '' (closedBall 0 δ ∩ S)) := by
  refine ⟨∑ i ∈ Finset.Icc 1 j, (‖Df i‖ + Lh * ‖Dc i‖) * δ ^ i / i !,
    forall_mem_image.2 fun d hd => ?_⟩
  refine (le_abs_self _).trans ((abs_compositeTaylorDecrement_le hLip d).trans
    (sum_le_sum fun i _ => ?_))
  have := hLip.nonneg
  gcongr
  exact mem_closedBall_zero_iff.1 hd.1

end Decrement

section Measure

variable (Df : FormalMultilinearSeries ℝ E ℝ) (Dc : FormalMultilinearSeries ℝ E F) (h : F → ℝ)
  (j : ℕ) (δ : ℝ) (S : Set E)

/-- The composite criticality measure `φ^δ_{w,j} = sup {ΔT_{w,j}(d) | ‖d‖ ≤ δ, d ∈ S}`
([cartis2022evaluation], (14.1.6), with the minimization variable `d`): for
`Df = ftaylorSeries ℝ f x`, `Dc = ftaylorSeries ℝ c x` and `S = univ` it is
`w(x) - min_{‖d‖ ≤ δ} T_{w,j}(x, d)`; with `S = {d | x + d ∈ X}` it is the constrained measure of
§14.2; with the jets of the regularized model at a trial step it is `φ^δ_{m̂,j}(s)` of
(14.1.14). -/
noncomputable def compositeTaylorMeasure : ℝ :=
  decrementMeasure (compositeTaylorDecrement Df Dc h j) δ S

/-- Unfolding lemma for `compositeTaylorMeasure`. -/
theorem compositeTaylorMeasure_eq_sSup :
    compositeTaylorMeasure Df Dc h j δ S =
      sSup (compositeTaylorDecrement Df Dc h j '' (closedBall 0 δ ∩ S)) := rfl

/-- With `h = 0` the composite measure is the Taylor measure. -/
@[simp]
theorem compositeTaylorMeasure_zero_fun :
    compositeTaylorMeasure Df Dc (0 : F → ℝ) j δ S = taylorMeasure Df j δ S := by
  rw [compositeTaylorMeasure, compositeTaylorDecrement_zero_fun]
  rfl

variable {Df Dc h j δ S} {Lh : ℝ} {d : E}

/-- Every feasible composite decrease is at most the measure (`h` Lipschitz). -/
theorem compositeTaylorDecrement_le_compositeTaylorMeasure (hLip : HasLipschitzConst h Lh)
    (hd : d ∈ closedBall 0 δ ∩ S) :
    compositeTaylorDecrement Df Dc h j d ≤ compositeTaylorMeasure Df Dc h j δ S :=
  le_decrementMeasure (bddAbove_compositeTaylorDecrement hLip δ S) hd

/-- The composite measure is nonnegative when `0` is feasible (`h` Lipschitz). -/
theorem compositeTaylorMeasure_nonneg (hLip : HasLipschitzConst h Lh)
    (h0 : (0 : E) ∈ S) (hδ : 0 ≤ δ) : 0 ≤ compositeTaylorMeasure Df Dc h j δ S :=
  decrementMeasure_nonneg (bddAbove_compositeTaylorDecrement hLip δ S) h0 hδ
    (compositeTaylorDecrement_zero_right Df Dc h j)

/-- The composite measure is monotone in the radius. -/
theorem compositeTaylorMeasure_mono_radius {δ' : ℝ} (hLip : HasLipschitzConst h Lh)
    (h0 : (0 : E) ∈ S) (hδ : 0 ≤ δ) (hδδ' : δ ≤ δ') :
    compositeTaylorMeasure Df Dc h j δ S ≤ compositeTaylorMeasure Df Dc h j δ' S :=
  decrementMeasure_mono_radius ⟨0, mem_closedBall_self hδ, h0⟩
    (bddAbove_compositeTaylorDecrement hLip δ' S) hδδ'

/-- The composite measure is monotone in the feasible set. -/
theorem compositeTaylorMeasure_mono_set {S' : Set E} (hLip : HasLipschitzConst h Lh)
    (h0 : (0 : E) ∈ S) (hδ : 0 ≤ δ) (hSS' : S ⊆ S') :
    compositeTaylorMeasure Df Dc h j δ S ≤ compositeTaylorMeasure Df Dc h j δ S' :=
  decrementMeasure_mono_set ⟨0, mem_closedBall_self hδ, h0⟩
    (bddAbove_compositeTaylorDecrement hLip δ S') hSS'

/-- In finite dimension, with `h` continuous, `S` closed and `0 ∈ S`, the composite measure is
attained at an optimality displacement. -/
theorem exists_compositeTaylorMeasure_eq [FiniteDimensional ℝ E] (hc : Continuous h)
    (hS : IsClosed S) (h0 : (0 : E) ∈ S) (hδ : 0 ≤ δ) :
    ∃ d ∈ closedBall 0 δ ∩ S,
      compositeTaylorDecrement Df Dc h j d = compositeTaylorMeasure Df Dc h j δ S :=
  exists_decrementMeasure_eq hS h0 hδ
    (continuous_compositeTaylorDecrement Df Dc h j hc).continuousOn

end Measure

/-! ### Approximate minimizers -/

section Approx

variable {Df : FormalMultilinearSeries ℝ E ℝ} {Dc : FormalMultilinearSeries ℝ E F} {h : F → ℝ}
  {S : Set E} {q : ℕ} {ε δ : ℕ → ℝ}

/-- `(ε, δ)`-approximate `q`-th order optimality for a composite function
([cartis2022evaluation], (14.1.9)): `φ^{δ_j}_{w,j} ≤ ε_j δ_j^j / j!` for `1 ≤ j ≤ q`, for the jets
`Df = ftaylorSeries ℝ f x`, `Dc = ftaylorSeries ℝ c x` and feasible displacements `S`. -/
def IsEpsDeltaApproxComposite (Df : FormalMultilinearSeries ℝ E ℝ)
    (Dc : FormalMultilinearSeries ℝ E F) (h : F → ℝ) (S : Set E) (q : ℕ) (ε δ : ℕ → ℝ) : Prop :=
  ∀ j ∈ Finset.Icc 1 q, compositeTaylorMeasure Df Dc h j (δ j) S ≤ ε j * δ j ^ j / j !

/-- Unfolding lemma for `IsEpsDeltaApproxComposite`. -/
theorem isEpsDeltaApproxComposite_iff :
    IsEpsDeltaApproxComposite Df Dc h S q ε δ ↔
      ∀ j ∈ Finset.Icc 1 q, compositeTaylorMeasure Df Dc h j (δ j) S ≤ ε j * δ j ^ j / j ! :=
  Iff.rfl

/-- With `h = 0`, composite approximate optimality is the smooth one (12.1.25). -/
theorem isEpsDeltaApproxComposite_zero_fun_iff :
    IsEpsDeltaApproxComposite Df Dc (0 : F → ℝ) S q ε δ ↔ IsEpsDeltaApprox Df S q ε δ := by
  simp only [IsEpsDeltaApproxComposite, compositeTaylorMeasure_zero_fun, IsEpsDeltaApprox]

/-- Certification by the Step-1 test (14.1.10): passing the test with approximate optimality
displacements of the composite decrements certifies (14.1.9). -/
theorem MeasureTestPasses.isEpsDeltaApproxComposite {ς : ℝ} {d : ℕ → E} (hς : 0 < ς)
    (hd : ∀ j ∈ Finset.Icc 1 q,
      IsApproxMeasureStep (compositeTaylorDecrement Df Dc h j) (δ j) S ς (d j))
    (htest : MeasureTestPasses (fun j => compositeTaylorDecrement Df Dc h j) q ς ε δ d) :
    IsEpsDeltaApproxComposite Df Dc h S q ε δ :=
  isEpsDeltaApprox_of_measureTestPasses (Δ := fun j => compositeTaylorDecrement Df Dc h j) hς hd
    htest

end Approx

/-! ### First-order necessity (Lemma 14.1.1) -/

section Necessity

/-- The first-order Taylor polynomial along a ray: `T_{g,1}(x, α s) = g(x) + α ∇g(x)[s]`. -/
private theorem taylorSum_one_ftaylorSeries_smul {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (g : E → G) (x s : E) (α : ℝ) :
    (ftaylorSeries ℝ g x).taylorSum 1 (α • s) = g x + α • fderiv ℝ g x s := by
  rw [FormalMultilinearSeries.taylorSum_eq_add, Finset.Icc_self, sum_singleton]
  simp only [ftaylorSeries, iteratedFDeriv_zero_apply, Nat.factorial_one, Nat.cast_one,
    inv_one, one_smul]
  rw [show (fun _ : Fin 1 => α • s) = fun i : Fin 1 => (fun _ => α) i • (fun _ => s) i from rfl,
    ContinuousMultilinearMap.map_smul_univ, iteratedFDeriv_one_apply]
  simp

private theorem taylorSum_ftaylorSeries_zero {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (g : E → G) (x : E) (p : ℕ) :
    (ftaylorSeries ℝ g x).taylorSum p 0 = g x :=
  taylorPolynomial_zero_right g p x

/-- The first-order composite decrement along a ray: `ΔT_{w,1}(x, α s) = w(x) - (f(x) +
α ∇f(x)[s] + h(c(x) + α ∇c(x)[s]))`. -/
private theorem compositeTaylorDecrement_one_smul (f : E → ℝ) (c : E → F) (h : F → ℝ) (x s : E)
    (α : ℝ) :
    compositeTaylorDecrement (ftaylorSeries ℝ f x) (ftaylorSeries ℝ c x) h 1 (α • s) =
      (f x + h (c x)) - (f x + α * fderiv ℝ f x s + h (c x + α • fderiv ℝ c x s)) := by
  rw [compositeTaylorDecrement, taylorSum_one_ftaylorSeries_smul f,
    taylorSum_one_ftaylorSeries_smul c, taylorSum_ftaylorSeries_zero f,
    taylorSum_ftaylorSeries_zero c, smul_eq_mul]

/-- **First-order necessity for composite problems** ([cartis2022evaluation], Lemma 14.1.1,
generalized). Let `X ⊆ E` be convex, `x ∈ X`, `f` and `c` differentiable at `x`, `h` convex with
Lipschitz constant `Lh`, and `x` a local minimizer of `w = f + h ∘ c` on `X`. Then for every `s`
with `x + s ∈ X`, `ΔT_{w,1}(x, s) ≤ 0`: `0` is a global minimizer of `T_{w,1}(x, ·)` over `X - x`.
(The book assumes a global minimizer; local minimality, plain Lipschitz continuity of `h` and no
subadditivity suffice.) -/
theorem compositeTaylorDecrement_one_nonpos_of_isLocalMinOn {f : E → ℝ} {c : E → F} {h : F → ℝ}
    {Lh : ℝ} {X : Set E} {x : E} (hX : Convex ℝ X) (hx : x ∈ X) (hf : DifferentiableAt ℝ f x)
    (hc : DifferentiableAt ℝ c x) (hconv : ConvexOn ℝ univ h)
    (hLip : HasLipschitzConst h Lh)
    (hmin : IsLocalMinOn (fun z => f z + h (c z)) X x) {s : E} (hs : x + s ∈ X) :
    compositeTaylorDecrement (ftaylorSeries ℝ f x) (ftaylorSeries ℝ c x) h 1 s ≤ 0 := by
  set Δ := compositeTaylorDecrement (ftaylorSeries ℝ f x) (ftaylorSeries ℝ c x) h 1 s with hΔ
  by_contra hpos
  push Not at hpos
  set a := fderiv ℝ f x s
  set b := fderiv ℝ c x s
  -- the decrement along `α s` is at least `α Δ` (convexity of the model in `α`)
  have hlin : ∀ α ∈ Icc (0 : ℝ) 1,
      α * Δ ≤ (f x + h (c x)) - (f x + α * a + h (c x + α • b)) := by
    intro α hα
    have hΔ1 := compositeTaylorDecrement_one_smul f c h x s 1
    rw [one_smul, one_smul, one_mul] at hΔ1
    have hcv := hconv.2 (mem_univ (c x)) (mem_univ (c x + b)) (sub_nonneg.2 hα.2) hα.1
      (by ring)
    rw [smul_eq_mul, smul_eq_mul, smul_add, ← add_assoc, ← add_smul, sub_add_cancel, one_smul]
      at hcv
    rw [hΔ, hΔ1]
    nlinarith
  -- first-order expansions of `f` and `c` along the ray
  have hline : HasDerivAt (fun α : ℝ => x + α • s) s 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const s).const_add x
  have hx0 : x + (0 : ℝ) • s = x := by simp
  have hfo := hasDerivAt_iff_isLittleO.1
    (HasFDerivAt.comp_hasDerivAt (0 : ℝ) (hx0 ▸ hf.hasFDerivAt) hline)
  have hco := hasDerivAt_iff_isLittleO.1
    (HasFDerivAt.comp_hasDerivAt (0 : ℝ) (hx0 ▸ hc.hasFDerivAt) hline)
  set ε := Δ / (2 * (1 + |Lh|))
  have hε : 0 < ε := by positivity
  have hf' := (hfo.def hε).filter_mono (nhdsWithin_le_nhds (s := Ioi 0))
  have hc' := (hco.def hε).filter_mono (nhdsWithin_le_nhds (s := Ioi 0))
  -- local minimality along the ray
  have hray : Tendsto (fun α : ℝ => x + α • s) (𝓝[Ioo 0 1] 0) (𝓝[X] x) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun α hα => ?_⟩
    · have := (hline.continuousAt.tendsto).mono_left (nhdsWithin_le_nhds (s := Ioo 0 1))
      simpa using this
    · have := hX.add_smul_mem hx hs ⟨hα.1.le, hα.2.le⟩
      simpa using this
  have hmin' := hray.eventually hmin
  have hIoo : 𝓝[Ioo (0 : ℝ) 1] 0 = 𝓝[>] 0 := nhdsWithin_Ioo_eq_nhdsGT one_pos
  rw [hIoo] at hmin'
  have hpos' : ∀ᶠ α in 𝓝[>] (0 : ℝ), α ∈ Ioo (0 : ℝ) 1 := by
    rw [← hIoo]; exact self_mem_nhdsWithin
  obtain ⟨α, ⟨hα0, hα1⟩, hm, hfα, hcα⟩ := (hpos'.and (hmin'.and (hf'.and hc'))).exists
  simp only [Function.comp_apply, zero_smul, add_zero, sub_zero, smul_eq_mul, Real.norm_eq_abs,
    abs_of_pos hα0] at hm hfα hcα
  have hl := hlin α ⟨hα0.le, hα1.le⟩
  -- `w(x + α s) ≤ T_{w,1}(x, α s) + ε α (1 + |Lh|)`
  have hhα : h (c (x + α • s)) - h (c x + α • b) ≤ |Lh| * (ε * α) := by
    have := hLip.abs_sub_le (c (x + α • s)) (c x + α • b)
    have hcα' : ‖c (x + α • s) - (c x + α • b)‖ ≤ ε * α := by
      rw [← sub_sub]; exact hcα
    calc h (c (x + α • s)) - h (c x + α • b) ≤ Lh * ‖c (x + α • s) - (c x + α • b)‖ :=
          (le_abs_self _).trans this
      _ ≤ |Lh| * ‖c (x + α • s) - (c x + α • b)‖ := by gcongr; exact le_abs_self _
      _ ≤ |Lh| * (ε * α) := by gcongr
  have hfα' : f (x + α • s) - f x - α * a ≤ ε * α := (le_abs_self _).trans hfα
  have hεΔ : ε * (1 + |Lh|) = Δ / 2 := by
    simp only [ε]; field_simp
  nlinarith [abs_nonneg Lh]

/-- Consequence of Lemma 14.1.1: at a local minimizer of `f + h ∘ c` on a convex `X` (with `h`
convex and Lipschitz), the first-order composite measure over `{d | x + d ∈ X}` vanishes for every
`δ ≥ 0`. -/
theorem compositeTaylorMeasure_one_eq_zero_of_isLocalMinOn {f : E → ℝ} {c : E → F} {h : F → ℝ}
    {Lh : ℝ} {X : Set E} {x : E} (hX : Convex ℝ X) (hx : x ∈ X) (hf : DifferentiableAt ℝ f x)
    (hc : DifferentiableAt ℝ c x) (hconv : ConvexOn ℝ univ h)
    (hLip : HasLipschitzConst h Lh)
    (hmin : IsLocalMinOn (fun z => f z + h (c z)) X x) {δ : ℝ} (hδ : 0 ≤ δ) :
    compositeTaylorMeasure (ftaylorSeries ℝ f x) (ftaylorSeries ℝ c x) h 1 δ
      {d | x + d ∈ X} = 0 := by
  have h0 : (0 : E) ∈ closedBall 0 δ ∩ {d | x + d ∈ X} :=
    ⟨mem_closedBall_self hδ, by simpa using hx⟩
  have hle : ∀ d ∈ closedBall 0 δ ∩ {d | x + d ∈ X},
      compositeTaylorDecrement (ftaylorSeries ℝ f x) (ftaylorSeries ℝ c x) h 1 d ≤ 0 :=
    fun d hd => compositeTaylorDecrement_one_nonpos_of_isLocalMinOn hX hx hf hc hconv hLip hmin hd.2
  refine le_antisymm (decrementMeasure_le ⟨0, h0⟩ hle) ?_
  have := le_decrementMeasure ⟨0, forall_mem_image.2 hle⟩ h0
  rwa [compositeTaylorDecrement_zero_right] at this

end Necessity

/-! ### Value remainder -/

/-- **Remainder of the composite model** (proof of Lemma 14.1.6 of [cartis2022evaluation], with
`L_{w,p} = L_{f,p} + L_{h,0} L_{c,p}` (14.1.27)). If `f`, `c` are `C^p` on the convex set `C`, with
`∇^p f` `Lf`-Lipschitz and `∇^p c` `Lc`-Lipschitz on `C`, and `h` has Lipschitz constant `Lh`,
then for `x, x + s ∈ C`,
`|w(x + s) - T_{w,p}(x, s)| ≤ (Lf + Lh Lc) / (p + 1)! ‖s‖^{p+1}`. (The book's `√m` comes from
componentwise constants, see `ContinuousMultilinearMap.norm_le_sqrt_card_mul_of_euclidean`.) -/
theorem abs_sub_compositeTaylor_le_of_lipschitz {f : E → ℝ} {c : E → F} {h : F → ℝ} {p : ℕ}
    {Lf Lc Lh : ℝ} {C : Set E} (hC : Convex ℝ C) (hf : ∀ y ∈ C, ContDiffAt ℝ p f y)
    (hc : ∀ y ∈ C, ContDiffAt ℝ p c y) (hLf : IteratedFDerivLipschitzOn f p Lf C)
    (hLc : IteratedFDerivLipschitzOn c p Lc C) (hLip : HasLipschitzConst h Lh)
    {x s : E} (hx : x ∈ C) (hxs : x + s ∈ C) :
    |(f (x + s) + h (c (x + s))) -
        (taylorPolynomial f p x s + h ((ftaylorSeries ℝ c x).taylorSum p s))| ≤
      (Lf + Lh * Lc) / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) := by
  have h1 := abs_sub_taylorPolynomial_le_of_lipschitz hC hf hLf hx hxs
  have h2 := norm_sub_taylorPolynomial_le_of_lipschitz hC hc hLc hx hxs
  have h3 : |h (c (x + s)) - h ((ftaylorSeries ℝ c x).taylorSum p s)| ≤
      Lh * (Lc / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1)) :=
    (hLip.abs_sub_le _ _).trans (mul_le_mul_of_nonneg_left h2 hLip.nonneg)
  calc _ = |(f (x + s) - taylorPolynomial f p x s) +
        (h (c (x + s)) - h ((ftaylorSeries ℝ c x).taylorSum p s))| := by ring_nf
    _ ≤ |f (x + s) - taylorPolynomial f p x s| +
        |h (c (x + s)) - h ((ftaylorSeries ℝ c x).taylorSum p s)| := abs_add_le _ _
    _ ≤ Lf / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) + Lh * (Lc / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1)) :=
        add_le_add h1 h3
    _ = (Lf + Lh * Lc) / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) := by ring

end Optimization

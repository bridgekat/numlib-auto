import Numlib.Optimization.Complexity.Basic
import Numlib.Optimization.Complexity.SlowExample.SeparatedJets
import Numlib.Optimization.ModelBased.QuadraticModel
import NumlibSurface.CartisGouldToint.Chapter01.Section01
import NumlibSurface.CartisGouldToint.Chapter02.Section01

/-!
# Cartis–Gould–Toint §3.1: Slow convergence of Newton's method

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §3.1, on
`ℝⁿ = EuclideanSpace ℝ (Fin n)`.

## Main definitions

* `AssumptionC2 f` — f.C2: `f` is twice continuously differentiable.
* `AssumptionHL f L` — f.HL: `f` is `C²` with `L`-Lipschitz Hessian (3.1.3), `L = L_{f,2} ≥ 1`.
* `IsNewtonStep f x s` — the Newton equation (3.1.1) `∇²f(x) s = -∇f(x)`.
* `algorithm_3_1_1 f ε x s` — Algorithm 3.1.1 (Newton's method) as a run predicate.

## Main results

* `isNewtonStep_iff_isMinOn` — (3.1.2): when `∇²f(x)` is positive definite, the Newton step is the
  unique global minimizer of the quadratic Taylor model `T_{f,2}(x, ·)`.
* `theorem_3_1_1` — Theorem 3.1.1: Newton's method may need `⌈ε₁⁻²⌉ + 1` evaluations of `f`,
  `∇f` and `∇²f` on a function satisfying f.Bb, f.gL and f.HL (constants independent of `ε₁`).

## Implementation notes

The two-dimensional example `f_SN` of (3.1.7) is built from the data (3.1.4)–(3.1.6) with the
smooth bump gluing `Optimization.exists_contDiff_interpolating_separated_jets` in place of the
book's piecewise-polynomial bump; the data are interpolated at `x_0, …, x_{k_ε}`, `k_ε = ⌈ε₁⁻²⌉`.
At the last point `x_{k_ε}` the gradient is prescribed to be `0` (instead of the value of (3.1.4)),
so that the method terminates there and every Newton run from the origin terminates exactly at
`k_ε`. The construction (`NewtonSlow.exists_example`) is reused for Theorem 3.2.2.
-/

open Set Finset Optimization
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter03

variable {n : ℕ}

/-! ### Assumptions f.C2 and f.HL -/

/-- **Assumption f.C2** of [cartis2022evaluation] (§3.1): `f` is twice continuously
differentiable. -/
def AssumptionC2 (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ContDiff ℝ 2 f

theorem assumptionC2_iff {f : EuclideanSpace ℝ (Fin n) → ℝ} : AssumptionC2 f ↔ ContDiff ℝ 2 f :=
  Iff.rfl

/-- **Assumption f.HL** of [cartis2022evaluation] (§3.1): `f` is twice continuously
differentiable and its Hessian is Lipschitz continuous with constant `L = L_{f,2} ≥ 1`,
`‖∇²f(x) - ∇²f(y)‖ ≤ L ‖x - y‖` for all `x, y` (3.1.3) (operator norm of bilinear forms). -/
structure AssumptionHL (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ) : Prop where
  /-- `f` is twice continuously differentiable. -/
  contDiff : ContDiff ℝ 2 f
  /-- The Lipschitz constant satisfies `L_{f,2} ≥ 1`. -/
  one_le : 1 ≤ L
  /-- The Hessian is `L`-Lipschitz (3.1.3). -/
  lipschitz : ∀ x y, ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ ≤ L * ‖x - y‖

namespace AssumptionHL

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ}

/-- f.HL implies f.C2. -/
theorem assumptionC2 (h : AssumptionHL f L) : AssumptionC2 f :=
  h.contDiff

theorem nonneg (h : AssumptionHL f L) : 0 ≤ L :=
  zero_le_one.trans h.one_le

theorem pos (h : AssumptionHL f L) : 0 < L :=
  zero_lt_one.trans_le h.one_le

/-- **Bridge to the backbone**: under f.HL, `IteratedFDerivLipschitzOn f 2 L univ`. -/
theorem iteratedFDerivLipschitzOn (h : AssumptionHL f L) :
    IteratedFDerivLipschitzOn f 2 L univ :=
  iteratedFDerivLipschitzOn_iff.2 fun x _ y _ => h.lipschitz x y

theorem contDiffAt (h : AssumptionHL f L) (x : EuclideanSpace ℝ (Fin n)) :
    ContDiffAt ℝ 2 f x :=
  h.contDiff.contDiffAt

/-- A larger constant is also a Lipschitz constant. -/
theorem mono (h : AssumptionHL f L) {L' : ℝ} (hL : L ≤ L') : AssumptionHL f L' :=
  ⟨h.contDiff, h.one_le.trans hL, fun x y =>
    (h.lipschitz x y).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))⟩

end AssumptionHL

theorem assumptionHL_iff {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ} :
    AssumptionHL f L ↔ ContDiff ℝ 2 f ∧ 1 ≤ L ∧ IteratedFDerivLipschitzOn f 2 L univ :=
  ⟨fun h => ⟨h.contDiff, h.one_le, h.iteratedFDerivLipschitzOn⟩, fun ⟨h1, h2, h3⟩ =>
    ⟨h1, h2, fun x y => iteratedFDerivLipschitzOn_iff.1 h3 x (mem_univ _) y (mem_univ _)⟩⟩

/-- f.HL holds if `f ∈ C³` has bounded third derivatives ([cartis2022evaluation], remark after
(3.1.3)). -/
theorem AssumptionHL.of_norm_iteratedFDeriv_three_le {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ}
    (hf : ContDiff ℝ 3 f) (hL : 1 ≤ L) (hb : ∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ L) :
    AssumptionHL f L :=
  assumptionHL_iff.2 ⟨hf.of_le (by norm_num), hL,
    iteratedFDerivLipschitzOn_of_norm_le convex_univ (fun y _ => hf.contDiffAt)
      fun x _ => hb x⟩

/-- A smooth function whose values and derivatives of order `≤ 3` are bounded by `B` satisfies
f.Bb (with `f_low = -B`), f.gL and f.HL (with constant `max B 1`). -/
theorem assumptions_of_bounded {f : EuclideanSpace ℝ (Fin n) → ℝ} {B : ℝ}
    (hf : ContDiff ℝ 3 f) (hb : ∀ y, |f y| ≤ B ∧ ∀ j ≤ 3, ‖iteratedFDeriv ℝ j f y‖ ≤ B) :
    Chapter02.AssumptionBb f (-B) ∧ Chapter02.AssumptionGL f (max B 1) ∧
      AssumptionHL f (max B 1) := by
  refine ⟨fun y => by linarith [neg_abs_le (f y), (hb y).1], ⟨hf.of_le (by norm_num),
    le_max_right _ _, fun x y => ?_⟩, AssumptionHL.of_norm_iteratedFDeriv_three_le hf
      (le_max_right _ _) fun x => ((hb x).2 3 le_rfl).trans (le_max_left _ _)⟩
  have hL : IteratedFDerivLipschitzOn f 1 (max B 1) univ :=
    iteratedFDerivLipschitzOn_of_norm_le convex_univ
      (fun y _ => (hf.of_le (by norm_num)).contDiffAt)
      fun x _ => ((hb x).2 2 (by norm_num)).trans (le_max_left _ _)
  have := iteratedFDerivLipschitzOn_iff.1 hL x (mem_univ _) y (mem_univ _)
  rwa [Chapter02.norm_iteratedFDeriv_one_sub, Chapter02.norm_fderiv_sub_fderiv] at this

/-! ### Newton's method -/

/-- The **Newton equation** (3.1.1) of [cartis2022evaluation]: `∇²f(x) s = -∇f(x)`, written with
the Hessian as a bilinear form, `∇²f(x)[s, v] = -⟪∇f(x), v⟫` for all `v`. -/
def IsNewtonStep (f : EuclideanSpace ℝ (Fin n) → ℝ) (x s : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ v, iteratedFDeriv ℝ 2 f x ![s, v] = -⟪gradient f x, v⟫

section NewtonStep

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {x s : EuclideanSpace ℝ (Fin n)}

/-- For `f` `C²` at `x`, the Newton equation in operator form: `∇²f(x) s = -∇f(x)`. -/
theorem isNewtonStep_iff (hf : ContDiffAt ℝ 2 f x) :
    IsNewtonStep f x s ↔ hessianOperator f x s = -gradient f x := by
  have hsym : ∀ v, iteratedFDeriv ℝ 2 f x ![s, v] = ⟪hessianOperator f x s, v⟫ := fun v => by
    rw [← inner_hessianOperator_apply hf]
    exact (hessianOperator_isSymmetric hf s v).symm
  simp only [IsNewtonStep, hsym]
  constructor
  · intro h
    refine ext_inner_right ℝ fun v => ?_
    rw [h v, inner_neg_left]
  · intro h v
    rw [h, inner_neg_left]

/-- `T_{f,2}(x, s + d) - T_{f,2}(x, s) = ½ ∇²f(x)[d, d]` at a Newton step `s`. -/
theorem taylorPolynomial_two_add_sub (hf : ContDiffAt ℝ 2 f x) (hs : IsNewtonStep f x s)
    (d : EuclideanSpace ℝ (Fin n)) :
    taylorPolynomial f 2 x (s + d) - taylorPolynomial f 2 x s =
      1 / 2 * iteratedFDeriv ℝ 2 f x (fun _ => d) := by
  rw [taylorPolynomial_two_eq_quadModel hf, taylorPolynomial_two_eq_quadModel hf,
    Subproblem.quadModel_def, Subproblem.quadModel_def, apply_diag_eq_vec,
    ← inner_hessianOperator_apply hf]
  have hH := (isNewtonStep_iff hf).1 hs
  have h1 : ⟪s, hessianOperator f x d⟫ = -⟪gradient f x, d⟫ := by
    have hsym := hessianOperator_isSymmetric hf s d
    change ⟪hessianOperator f x s, d⟫ = ⟪s, hessianOperator f x d⟫ at hsym
    rw [← hsym, hH, inner_neg_left]
  have h2 : ⟪d, hessianOperator f x s⟫ = -⟪gradient f x, d⟫ := by
    rw [hH, inner_neg_right, real_inner_comm]
  rw [map_add, inner_add_left, inner_add_right, inner_add_right, inner_add_right, h1, h2]
  ring

/-- **(3.1.2)** of [cartis2022evaluation]: if `f` is `C²` at `x` with positive definite Hessian
(`λ_min[∇²f(x)] > 0`) and `s` solves the Newton equation (3.1.1), then the Newton steps and the
global minimizers of the quadratic Taylor model `T_{f,2}(x, ·)` are both exactly `s`. -/
theorem isNewtonStep_iff_isMinOn (hf : ContDiffAt ℝ 2 f x)
    (hpd : 0 < Chapter01.hessianMinEig f x) (hs : IsNewtonStep f x s)
    (s' : EuclideanSpace ℝ (Fin n)) :
    (IsNewtonStep f x s' ↔ s' = s) ∧
      (IsMinOn (taylorPolynomial f 2 x) univ s' ↔ s' = s) := by
  have hpos : ∀ d, d ≠ 0 → 0 < iteratedFDeriv ℝ 2 f x (fun _ => d) := fun d hd =>
    lt_of_lt_of_le (by have := norm_pos_iff.2 hd; positivity)
      (minCurvature_mul_norm_sq_le (iteratedFDeriv ℝ 2 f x) d)
  have hdiff := taylorPolynomial_two_add_sub hf hs
  refine ⟨⟨fun hs' => ?_, fun h => h ▸ hs⟩, ⟨fun hmin => ?_, fun h => h ▸ fun y _ => ?_⟩⟩
  · by_contra hne
    have h1 := (isNewtonStep_iff hf).1 hs
    have h2 := (isNewtonStep_iff hf).1 hs'
    have hd := hpos (s' - s) (sub_ne_zero.2 hne)
    rw [apply_diag_eq_vec, ← inner_hessianOperator_apply hf, map_sub, h1, h2, sub_self,
      inner_zero_right] at hd
    exact lt_irrefl _ hd
  · by_contra hne
    have h1 := hmin (mem_univ s)
    have h2 := hdiff (s' - s)
    rw [add_sub_cancel] at h2
    have := hpos (s' - s) (sub_ne_zero.2 hne)
    simp only [mem_ofPred_eq] at h1
    linarith
  · have := hdiff (y - s)
    rw [add_sub_cancel] at this
    have h0 : 0 ≤ iteratedFDeriv ℝ 2 f x (fun _ => y - s) :=
      (mul_nonneg hpd.le (sq_nonneg _)).trans (minCurvature_mul_norm_sq_le _ _)
    simp only [mem_ofPred_eq]
    linarith

end NewtonStep

/-- **Algorithm 3.1.1** (Newton's method for unconstrained minimization) of
[cartis2022evaluation], as a run predicate on iterates `x` and steps `s`: `ε > 0`, and at every
iteration `k` before the termination test `‖∇f(x_k)‖ ≤ ε` first holds, `s_k` solves the Newton
equation (3.1.1) and `x_{k+1} = x_k + s_k`. (The book presumes the Hessians positive definite,
when `s_k` is the unique minimizer of `T_{f,2}(x_k, ·)`, `isNewtonStep_iff_isMinOn`.) -/
structure algorithm_3_1_1 (f : EuclideanSpace ℝ (Fin n) → ℝ) (ε : ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) : Prop where
  /-- The accuracy level is positive. -/
  ε_pos : 0 < ε
  /-- Step 2: the Newton equation (3.1.1). -/
  step : UntilHit (fun k => ‖gradient f (x k)‖ ≤ ε) fun k => IsNewtonStep f (x k) (s k)
  /-- Step 3: the new iterate. -/
  next : UntilHit (fun k => ‖gradient f (x k)‖ ≤ ε) fun k => x (k + 1) = x k + s k

/-! ### The example of Theorem 3.1.1 -/

namespace NewtonSlow

/-- The first unit vector of `ℝ²`. -/
noncomputable abbrev e₁ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1

/-- The second unit vector of `ℝ²`. -/
noncomputable abbrev e₂ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 1

theorem norm_e₁ : ‖e₁‖ = 1 := by simp [e₁]

theorem norm_e₂ : ‖e₂‖ = 1 := by simp [e₂]

theorem inner_e₁_e₁ : ⟪e₁, e₁⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, norm_e₁, one_pow]

theorem inner_e₂_e₂ : ⟪e₂, e₂⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, norm_e₂, one_pow]

theorem inner_e₁_e₂ : ⟪e₁, e₂⟫ = 0 := by
  simp [e₁, e₂, EuclideanSpace.inner_single_left]

theorem inner_e₂_e₁ : ⟪e₂, e₁⟫ = 0 := by
  rw [real_inner_comm, inner_e₁_e₂]

theorem norm_sq_eq (d : EuclideanSpace ℝ (Fin 2)) : ‖d‖ ^ 2 = ⟪e₁, d⟫ ^ 2 + ⟪e₂, d⟫ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  simp [e₁, e₂, EuclideanSpace.inner_single_left]

theorem abs_inner_e₁_le (d : EuclideanSpace ℝ (Fin 2)) : |⟪e₁, d⟫| ≤ ‖d‖ :=
  (abs_real_inner_le_norm _ _).trans (by rw [norm_e₁, one_mul])

/-- The rank-one bilinear form `(v, w) ↦ ⟪e, v⟫ ⟪e, w⟫`. -/
noncomputable def rankOne (e : EuclideanSpace ℝ (Fin 2)) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 2 => EuclideanSpace ℝ (Fin 2)) ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
    fun _ => innerSL ℝ e

theorem rankOne_apply (e : EuclideanSpace ℝ (Fin 2)) (v : Fin 2 → EuclideanSpace ℝ (Fin 2)) :
    rankOne e v = ⟪e, v 0⟫ * ⟪e, v 1⟫ := by
  simp [rankOne, Fin.prod_univ_two]

theorem norm_rankOne_le {e : EuclideanSpace ℝ (Fin 2)} (he : ‖e‖ = 1) : ‖rankOne e‖ ≤ 1 := by
  refine ContinuousMultilinearMap.opNorm_le_bound zero_le_one fun v => ?_
  rw [rankOne_apply, Real.norm_eq_abs, abs_mul, Fin.prod_univ_two, one_mul]
  have h0 := abs_real_inner_le_norm e (v 0)
  have h1 := abs_real_inner_le_norm e (v 1)
  rw [he, one_mul] at h0 h1
  exact mul_le_mul h0 h1 (abs_nonneg _) (norm_nonneg _)

/-- `k_ε = ⌈ε⁻²⌉`. -/
noncomputable def kε (ε : ℝ) : ℕ := ⌈(ε ^ 2)⁻¹⌉₊

/-- The function values `f_k = 2 - k ε²` of (3.1.4). -/
noncomputable def fval (ε : ℝ) (k : ℕ) : ℝ := 2 - k * ε ^ 2

/-- The Newton steps `s_k = f_k⁻¹ (1, ε)` of (3.1.5) for `k < k_ε` (and `0` afterwards). -/
noncomputable def step (ε : ℝ) (k : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  if k < kε ε then (fval ε k)⁻¹ • (e₁ + ε • e₂) else 0

/-- The iterates `x_k = ∑_{j<k} s_j` of (3.1.6). -/
noncomputable def iter (ε : ℝ) (k : ℕ) : EuclideanSpace ℝ (Fin 2) := ∑ j ∈ range k, step ε j

/-- The gradients `g_k = -(ε² f_k, ε f_k)` of (3.1.4) for `k < k_ε`, and `0` at `k_ε`. -/
noncomputable def grad (ε : ℝ) (k : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  if k < kε ε then -((ε ^ 2 * fval ε k) • e₁) - (ε * fval ε k) • e₂ else 0

/-- The Hessians `H_k = diag(ε² f_k², f_k²)` of (3.1.4). -/
noncomputable def hess (ε : ℝ) (k : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 2 => EuclideanSpace ℝ (Fin 2)) ℝ :=
  (ε ^ 2 * fval ε k ^ 2) • rankOne e₁ + fval ε k ^ 2 • rankOne e₂

theorem iter_zero (ε : ℝ) : iter ε 0 = 0 := by simp [iter]

theorem iter_succ (ε : ℝ) (k : ℕ) : iter ε (k + 1) = iter ε k + step ε k := by
  simp [iter, sum_range_succ]

theorem hess_apply (ε : ℝ) (k : ℕ) (v : Fin 2 → EuclideanSpace ℝ (Fin 2)) :
    hess ε k v = ε ^ 2 * fval ε k ^ 2 * (⟪e₁, v 0⟫ * ⟪e₁, v 1⟫) +
      fval ε k ^ 2 * (⟪e₂, v 0⟫ * ⟪e₂, v 1⟫) := by
  simp [hess, rankOne_apply]

section Bounds

variable {ε : ℝ}

theorem kε_mul_lt (hε : 0 < ε) (hε1 : ε < 1) : (kε ε : ℝ) * ε ^ 2 < 2 := by
  have h2 : 0 < ε ^ 2 := by positivity
  have := Nat.ceil_lt_add_one (inv_nonneg.2 h2.le)
  have h3 : (kε ε : ℝ) * ε ^ 2 < ((ε ^ 2)⁻¹ + 1) * ε ^ 2 :=
    mul_lt_mul_of_pos_right this h2
  rw [add_mul, inv_mul_cancel₀ h2.ne'] at h3
  have : ε ^ 2 < 1 := by nlinarith
  linarith

theorem fval_pos (hε : 0 < ε) (hε1 : ε < 1) {k : ℕ} (hk : k ≤ kε ε) : 0 < fval ε k := by
  have h := kε_mul_lt hε hε1
  have : (k : ℝ) * ε ^ 2 ≤ kε ε * ε ^ 2 :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (by positivity)
  unfold fval; linarith

theorem one_lt_fval (hε : 0 < ε) {k : ℕ} (hk : k < kε ε) : 1 < fval ε k := by
  have h2 : 0 < ε ^ 2 := by positivity
  have : (k : ℝ) < (ε ^ 2)⁻¹ := Nat.lt_ceil.1 hk
  have : (k : ℝ) * ε ^ 2 < 1 := by
    have := mul_lt_mul_of_pos_right this h2
    rwa [inv_mul_cancel₀ h2.ne'] at this
  unfold fval; linarith

theorem fval_le_two (ε : ℝ) (k : ℕ) : fval ε k ≤ 2 := by
  unfold fval
  have : 0 ≤ (k : ℝ) * ε ^ 2 := by positivity
  linarith

theorem inner_e₁_step {k : ℕ} (hk : k < kε ε) : ⟪e₁, step ε k⟫ = (fval ε k)⁻¹ := by
  rw [step, ite_eq_left hk, inner_smul_right, inner_add_right, inner_smul_right, inner_e₁_e₁,
    inner_e₁_e₂]
  ring

theorem inner_e₂_step {k : ℕ} (hk : k < kε ε) : ⟪e₂, step ε k⟫ = ε * (fval ε k)⁻¹ := by
  rw [step, ite_eq_left hk, inner_smul_right, inner_add_right, inner_smul_right, inner_e₂_e₂,
    inner_e₂_e₁]
  ring

/-- The iterates are `1/2` apart: their first coordinates increase by `1/f_k ≥ 1/2`. -/
theorem half_le_norm_iter_sub (hε : 0 < ε) (hε1 : ε < 1) {i j : ℕ} (hij : i < j) (hj : j ≤ kε ε) :
    1 / 2 ≤ ‖iter ε j - iter ε i‖ := by
  have hsum : iter ε j - iter ε i = ∑ l ∈ Finset.Ico i j, step ε l := by
    rw [iter, iter, sum_Ico_eq_sub _ hij.le]
  have hin : ⟪e₁, iter ε j - iter ε i⟫ = ∑ l ∈ Finset.Ico i j, (fval ε l)⁻¹ := by
    rw [hsum, inner_sum]
    refine sum_congr rfl fun l hl => inner_e₁_step ?_
    exact (Finset.mem_Ico.1 hl).2.trans_le hj
  have hge : 1 / 2 ≤ ⟪e₁, iter ε j - iter ε i⟫ := by
    rw [hin]
    have hi : i ∈ Finset.Ico i j := Finset.mem_Ico.2 ⟨le_rfl, hij⟩
    have hnn : ∀ l ∈ Finset.Ico i j, 0 ≤ (fval ε l)⁻¹ := fun l hl =>
      (inv_pos.2 (fval_pos hε hε1 ((Finset.mem_Ico.1 hl).2.le.trans hj))).le
    calc (1 : ℝ) / 2 ≤ (fval ε i)⁻¹ := by
          rw [one_div]
          exact inv_anti₀ (fval_pos hε hε1 (hij.le.trans hj)) (fval_le_two ε i)
      _ ≤ ∑ l ∈ Finset.Ico i j, (fval ε l)⁻¹ :=
          single_le_sum (f := fun l => (fval ε l)⁻¹) hnn hi
  exact hge.trans ((le_abs_self _).trans (abs_inner_e₁_le _))

theorem norm_grad_le (hε : 0 < ε) (hε1 : ε < 1) (k : ℕ) : ‖grad ε k‖ ≤ 8 := by
  unfold grad
  split_ifs with hk
  · have hf := fval_pos hε hε1 hk.le
    have hf2 := fval_le_two ε k
    calc ‖-((ε ^ 2 * fval ε k) • e₁) - (ε * fval ε k) • e₂‖
        ≤ ‖(ε ^ 2 * fval ε k) • e₁‖ + ‖(ε * fval ε k) • e₂‖ := by
          rw [sub_eq_add_neg]
          exact (norm_add_le _ _).trans (by rw [norm_neg, norm_neg])
      _ = ε ^ 2 * fval ε k + ε * fval ε k := by
          rw [norm_smul, norm_smul, norm_e₁, norm_e₂, Real.norm_of_nonneg (by positivity),
            Real.norm_of_nonneg (by positivity)]
          ring
      _ ≤ 8 := by nlinarith
  · simp

theorem norm_hess_le (hε : 0 < ε) (hε1 : ε < 1) {k : ℕ} (hk : k ≤ kε ε) : ‖hess ε k‖ ≤ 8 := by
  have hf := fval_pos hε hε1 hk
  have hf2 := fval_le_two ε k
  calc ‖hess ε k‖ ≤ ‖(ε ^ 2 * fval ε k ^ 2) • rankOne e₁‖ + ‖fval ε k ^ 2 • rankOne e₂‖ :=
        norm_add_le _ _
    _ ≤ ε ^ 2 * fval ε k ^ 2 * 1 + fval ε k ^ 2 * 1 := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by positivity),
          Real.norm_of_nonneg (by positivity)]
        gcongr
        · exact norm_rankOne_le norm_e₁
        · exact norm_rankOne_le norm_e₂
    _ ≤ 8 := by
        have h4 : fval ε k ^ 2 ≤ 4 := by nlinarith
        have h1 : ε ^ 2 ≤ 1 := by nlinarith
        have : ε ^ 2 * fval ε k ^ 2 ≤ 1 * fval ε k ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
        linarith

/-- The Hessians are uniformly positive definite: `H_k[d, d] ≥ ε² f_k² ‖d‖²`. -/
theorem le_hess_apply (hε : 0 < ε) (hε1 : ε < 1) {k : ℕ} (d : EuclideanSpace ℝ (Fin 2)) :
    ε ^ 2 * fval ε k ^ 2 * ‖d‖ ^ 2 ≤ hess ε k (fun _ => d) := by
  rw [hess_apply, norm_sq_eq]
  have : ε ^ 2 ≤ 1 := by nlinarith
  have h0 : 0 ≤ fval ε k ^ 2 * ⟪e₂, d⟫ ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right this h0]

/-- The Newton equation holds at the data: `H_k s_k = -g_k` for `k < k_ε`. -/
theorem hess_step_apply (hε : 0 < ε) (hε1 : ε < 1) {k : ℕ} (hk : k < kε ε)
    (v : EuclideanSpace ℝ (Fin 2)) :
    hess ε k ![step ε k, v] = -⟪grad ε k, v⟫ := by
  have hf := (fval_pos hε hε1 hk.le).ne'
  rw [hess_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [inner_e₁_step hk, inner_e₂_step hk, grad, ite_eq_left hk, inner_sub_left,
    inner_neg_left, inner_smul_left, inner_smul_left]
  simp only [conj_trivial]
  field_simp
  ring

theorem lt_norm_grad (hε : 0 < ε) (hε1 : ε < 1) {k : ℕ} (hk : k < kε ε) : ε < ‖grad ε k‖ := by
  have hf := one_lt_fval hε hk
  have hsq : ‖grad ε k‖ ^ 2 = ε ^ 2 * fval ε k ^ 2 * (ε ^ 2 + 1) := by
    rw [norm_sq_eq, grad, ite_eq_left hk, inner_sub_right, inner_neg_right, inner_smul_right,
      inner_smul_right, inner_sub_right, inner_neg_right, inner_smul_right, inner_smul_right,
      inner_e₁_e₁, inner_e₁_e₂, inner_e₂_e₁, inner_e₂_e₂]
    ring
  have : ε ^ 2 < ‖grad ε k‖ ^ 2 := by
    rw [hsq]
    have : 1 < fval ε k ^ 2 * (ε ^ 2 + 1) := by nlinarith
    have := mul_lt_mul_of_pos_left this (pow_pos hε 2)
    linarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) this

end Bounds

theorem hess_symm (ε : ℝ) (k : ℕ) (v w : EuclideanSpace ℝ (Fin 2)) :
    hess ε k ![v, w] = hess ε k ![w, v] := by
  simp only [hess_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- A function with the Hessians `H_k` at `x_k` has positive definite Hessians there. -/
theorem hessianMinEig_pos {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) {k : ℕ} (hk : k ≤ kε ε)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} (h2 : iteratedFDeriv ℝ 2 f (iter ε k) = hess ε k) :
    0 < Chapter01.hessianMinEig f (iter ε k) := by
  have hfk := fval_pos hε hε1 hk
  refine lt_of_lt_of_le (by positivity : 0 < ε ^ 2 * fval ε k ^ 2) ?_
  rw [Chapter01.hessianMinEig, h2]
  exact le_minCurvature_iff.2 fun d => le_hess_apply hε hε1 d

/-- A function with the jets `(g_k, H_k)` at `x_k` has the Newton steps `s_k` there. -/
theorem isNewtonStep_of_jet {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) {k : ℕ} (hk : k < kε ε)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hg : gradient f (iter ε k) = grad ε k)
    (h2 : iteratedFDeriv ℝ 2 f (iter ε k) = hess ε k) :
    IsNewtonStep f (iter ε k) (step ε k) := fun v => by
  rw [h2, hg]
  exact hess_step_apply hε hε1 hk v

/-- **The example of Theorem 3.1.1** ((3.1.4)–(3.1.7)): there is `B ≥ 0` such that for every
`ε ∈ (0,1)` there is a smooth `f : ℝ² → ℝ` with `|f|` and its derivatives of order `≤ 3` bounded
by `B`, interpolating `(f_k, g_k, H_k)` at `x_k` for `k ≤ k_ε` (with `g_{k_ε} = 0`). -/
theorem exists_example :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ f : EuclideanSpace ℝ (Fin 2) → ℝ,
      ContDiff ℝ 3 f ∧ (∀ y, |f y| ≤ B ∧ ∀ j ≤ 3, ‖iteratedFDeriv ℝ j f y‖ ≤ B) ∧
      ∀ k ≤ kε ε, f (iter ε k) = fval ε k ∧ gradient f (iter ε k) = grad ε k ∧
        iteratedFDeriv ℝ 2 f (iter ε k) = hess ε k := by
  obtain ⟨B, hB, H⟩ := exists_contDiff_interpolating_separated_jets
    (E := EuclideanSpace ℝ (Fin 2)) (r := 1 / 2) (κ := 8) (by norm_num) (by norm_num)
  refine ⟨B, hB, fun ε hε hε1 => ?_⟩
  obtain ⟨f, hf, hjet, hbd⟩ := H (kε ε) (iter ε) (fval ε) (grad ε) (hess ε)
    (fun i hi j hj hij => by
      rcases lt_or_gt_of_ne hij with h | h
      · rw [norm_sub_rev]; exact half_le_norm_iter_sub hε hε1 h hj
      · exact half_le_norm_iter_sub hε hε1 h hi)
    (fun k _ => hess_symm ε k)
    (fun k hk => ⟨by
      rw [abs_of_pos (fval_pos hε hε1 hk)]; linarith [fval_le_two ε k],
      norm_grad_le hε hε1 k, norm_hess_le hε hε1 hk⟩)
  exact ⟨f, hf.of_le (by norm_cast), hbd, hjet⟩

end NewtonSlow

open NewtonSlow in
/-- **Theorem 3.1.1** of [cartis2022evaluation] (slow first-order convergence of Newton's
method). There are `f_low`, `L₁ ≥ 1` and `L₂ ≥ 1` such that for every `ε₁ ∈ (0,1)` there is
`f : ℝ² → ℝ` satisfying f.Bb, f.gL and f.HL (with these constants) for which a Newton run from
`x₀ = 0` exists and every Newton run from `x₀ = 0` has positive definite Hessians
`λ_min[∇²f(x_k)] > 0` for `k ≤ k_ε = ⌈ε₁⁻²⌉` and terminates exactly at iteration `k_ε`: it needs
`k_ε + 1 > ⌈ε₁⁻²⌉` evaluations of `f`, `∇f` and `∇²f`. -/
theorem theorem_3_1_1 :
    ∃ flow L₁ L₂ : ℝ, 1 ≤ L₁ ∧ 1 ≤ L₂ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ f : EuclideanSpace ℝ (Fin 2) → ℝ, Chapter02.AssumptionBb f flow ∧
        Chapter02.AssumptionGL f L₁ ∧ AssumptionHL f L₂ ∧
        (∃ x s, x 0 = 0 ∧ algorithm_3_1_1 f ε x s) ∧
        ∀ x s, x 0 = 0 → algorithm_3_1_1 f ε x s →
          (∀ k ≤ ⌈(ε ^ 2)⁻¹⌉₊, 0 < Chapter01.hessianMinEig f (x k)) ∧
          IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) ⌈(ε ^ 2)⁻¹⌉₊ := by
  obtain ⟨B, -, H⟩ := exists_example
  refine ⟨-B, max B 1, max B 1, le_max_right _ _, le_max_right _ _, fun ε hε hε1 => ?_⟩
  obtain ⟨f, hf, hbd, hjet⟩ := H ε hε hε1
  obtain ⟨hb, hgl, hhl⟩ := assumptions_of_bounded hf hbd
  set K := kε ε
  have hgrad : ∀ k ≤ K, ‖gradient f (iter ε k)‖ ≤ ε ↔ K ≤ k := fun k hk => by
    rw [(hjet k hk).2.1]
    constructor
    · intro h
      by_contra hlt
      exact absurd h (not_le.2 (lt_norm_grad hε hε1 (not_le.1 hlt)))
    · intro h
      rw [grad, ite_eq_right (not_lt.2 h), norm_zero]; exact hε.le
  have hhit : IsFirstHit (fun k => ‖gradient f (iter ε k)‖ ≤ ε) K :=
    ⟨(hgrad K le_rfl).2 le_rfl, fun j hj h => absurd ((hgrad j hj.le).1 h) (not_le.2 hj)⟩
  have hpd : ∀ k ≤ K, 0 < Chapter01.hessianMinEig f (iter ε k) := fun k hk =>
    hessianMinEig_pos hε hε1 hk (hjet k hk).2.2
  have hnewton : ∀ k < K, IsNewtonStep f (iter ε k) (step ε k) := fun k hk =>
    isNewtonStep_of_jet hε hε1 hk (hjet k hk.le).2.1 (hjet k hk.le).2.2
  refine ⟨f, hb, hgl, hhl, ⟨iter ε, step ε, iter_zero ε, hε, fun k hk => hnewton k ?_,
    fun k _ => iter_succ ε k⟩, fun x s hx0 h => ?_⟩
  · exact not_le.1 fun hle => hk K hle hhit.test
  -- every run follows the data
  have heq : ∀ k ≤ K, ∀ j ≤ k, x j = iter ε j := by
    intro k
    induction k with
    | zero => exact fun _ j hj => by rw [Nat.le_zero.1 hj, hx0, iter_zero]
    | succ k ih =>
      intro hk j hj
      have hx := ih (Nat.le_of_succ_le hk)
      rcases Nat.lt_or_eq_of_le hj with hj | rfl
      · exact hx j (Nat.lt_succ_iff.1 hj)
      have hkK : k < K := hk
      have hstop : ∀ i ≤ k, ¬ ‖gradient f (x i)‖ ≤ ε := fun i hi => by
        rw [hx i hi]; exact hhit.not_test_of_lt (hi.trans_lt hkK)
      have hs : IsNewtonStep f (iter ε k) (s k) := hx k le_rfl ▸ h.step k hstop
      have hsk := ((isNewtonStep_iff_isMinOn (hhl.contDiffAt _) (hpd k hkK.le)
        (hnewton k hkK) (s k)).1).1 hs
      rw [h.next k hstop, hx k le_rfl, hsk, iter_succ]
  rw [show ⌈(ε ^ 2)⁻¹⌉₊ = K from rfl]
  refine ⟨fun k hk => by rw [heq K le_rfl k hk]; exact hpd k hk,
    ⟨by simp only; rw [heq K le_rfl K le_rfl]; exact hhit.test, fun j hj => ?_⟩⟩
  simp only
  rw [heq K le_rfl j hj.le]
  exact hhit.not_test_of_lt hj

end CartisGouldToint.Chapter03

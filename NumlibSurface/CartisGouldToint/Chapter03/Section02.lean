import Numlib.Optimization.Complexity.Telescoping
import NumlibSurface.CartisGouldToint.Chapter02.Section02
import NumlibSurface.CartisGouldToint.Chapter02.Section03
import NumlibSurface.CartisGouldToint.Chapter03.Section01

/-!
# Cartis–Gould–Toint §3.2: The trust-region method using second derivatives

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §3.2: the second-order
trust-region algorithm TR2 on `ℝⁿ = EuclideanSpace ℝ (Fin n)`.

The model is the quadratic Taylor model `T_{f,2}(x_k, s) = f(x_k) + ⟪∇f(x_k), s⟫ +
½ ⟪s, ∇²f(x_k) s⟫`, i.e. the TR1 model (2.3.1) with `B_k = ∇²f(x_k)` (`tr2Model`, equal to
`taylorPolynomial f 2 x_k` for `C²` functions, `tr2Model_eq_taylorPolynomial`). TR2 is an instance
of the generic trust-region run `Optimization.IsTRRun`.

## Main definitions

* `AssumptionHBa f κH` — f.HBa: the Hessian is bounded by `κ_H ≥ 1`.
* `IsApproxSecondOrderMinimizer f x ε₁ ε₂` — (3.2.6); `stopTest f ε₁ ε₂ x` — the termination test
  of TR2 and AR2 with `ε₂ : Option ℝ` (`none` standing for `ε₂ = +∞`).
* `IsEigenpointStep g H Δ u t` — `t` minimizes the model along the eigenvector `u` in the trust
  region (3.2.5).
* `tr2Step`, `tr2Ratio` — Step 2 ((2.3.4)–(2.3.5) and (3.2.10)) and the ratio (3.2.11).
* `algorithm_3_2_1 f P ε₁ ε₂ x s Δ` — Algorithm 3.2.1 (TR2); `exists_algorithm_3_2_1`.

## Main results

* `theorem_3_2_1`, `theorem_3_2_2` — first-order complexity of TR2 (via Theorem 2.3.7) and its
  sharpness (the Newton example of Theorem 3.1.1).
* `lemma_3_2_3`, `lemma_3_2_4`, `lemma_3_2_5`, `theorem_3_2_6` — second-order complexity.
* `theorem_3_2_7` — sharpness of the second-order bound.

## Fixes with respect to the book

* The trust-region constraints on the Cauchy and eigenpoint steps, written `x_k - t g ∈ 𝓡_k` and
  `x_k + t u ∈ 𝓑_{Δ_k}`, are read as `‖t g‖ ≤ Δ_k` and `‖t u‖ ≤ Δ_k`.
* Step 1 of TR2 also terminates at "`ε`-approximate strict local minimizers" (`‖∇f‖ ≤ ε₁`,
  `λ_min > ε₂`); these satisfy (3.2.9), so the termination test is (3.2.9) alone.
* Theorem 3.2.2: the book claims `‖∇f(x_k)‖ > ε₁` for all `k ≤ ⌈ε₁⁻²⌉` with the data (3.1.4);
  for `ε₁` not small `f_{k_ε} = 2 - ⌈ε₁⁻²⌉ ε₁²` may be smaller than `1` and the claim fails at
  `k = k_ε`. The example prescribes `∇f(x_{k_ε}) = 0` and the run terminates exactly at
  `k_ε = ⌈ε₁⁻²⌉`, after `k_ε + 1` evaluations.
* Lemma 3.2.5 is stated for every `k` up to (and including) termination.
* Theorem 3.2.6: the printed `κ^F_TR2 = min(γ₁(1-η₂)/(Δ₀ max(4κ_H, L_{f,2}/3)), Δ₀)/|log γ₂| + 1`
  lacks the `|log ·|`; the proof gives `κ^F = |log(κ_Δ/Δ₀)|/|log γ₂| + 1` (`kappaFTR2`), which is
  at most the book's constant with `|log ·|` inserted (`kappaFTR2_le_book`). The bound holds for
  all `ε₁ > 0` (the book's `ε₁ ≤ 1` is not used).
* Theorem 3.2.7: (3.2.25) `x_k = (k - 1) ε` is a typo for `x_k = k ε`; "`s₁ = ε`" means `s₀`.
  The claim `f_{k_ε} ≥ 0` needs `ε⁻³` to be an integer; only boundedness of `f` is used.
-/

open Set Finset Optimization Subproblem
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter03

variable {n : ℕ}

/-! ### Assumption f.HBa and approximate second-order minimizers -/

/-- **Assumption f.HBa** of [cartis2022evaluation] (§3.2.2): `f` is twice continuously
differentiable and its Hessian is uniformly bounded, `‖∇²f(x)‖ ≤ κ_H` for all `x`, with
`κ_H ≥ 1`. -/
structure AssumptionHBa (f : EuclideanSpace ℝ (Fin n) → ℝ) (κH : ℝ) : Prop where
  /-- `f` is twice continuously differentiable. -/
  contDiff : ContDiff ℝ 2 f
  /-- `κ_H ≥ 1`. -/
  one_le : 1 ≤ κH
  /-- The Hessian bound. -/
  bound : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ κH

namespace AssumptionHBa

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {κH : ℝ}

theorem nonneg (h : AssumptionHBa f κH) : 0 ≤ κH :=
  zero_le_one.trans h.one_le

/-- **f.HBa implies f.gL** with `L_{f,1} = κ_H` ([cartis2022evaluation], (3.2.13), Theorem
A.8.5). -/
theorem assumptionGL (h : AssumptionHBa f κH) : Chapter02.AssumptionGL f κH :=
  .of_iteratedFDerivLipschitzOn (h.contDiff.of_le (by norm_num)) h.one_le
    (iteratedFDerivLipschitzOn_of_norm_le convex_univ (fun y _ => h.contDiff.contDiffAt)
      fun x _ => h.bound x)

/-- The Hessian operators along any sequence satisfy m.HBa with `κ_B = κ_H` ((3.2.13)). -/
theorem assumptionMHBa (h : AssumptionHBa f κH) (x : ℕ → EuclideanSpace ℝ (Fin n)) :
    Chapter02.AssumptionMHBa (fun k => hessianOperator f (x k)) κH :=
  ⟨h.nonneg, fun _ => (norm_hessianOperator_le h.contDiff.contDiffAt).trans (h.bound _)⟩

end AssumptionHBa

/-- An **`(ε₁, ε₂)`-approximate second-order minimizer** ([cartis2022evaluation], (3.2.6)):
`‖∇f(x)‖ ≤ ε₁` and `λ_min[∇²f(x)] ≥ -ε₂`. -/
def IsApproxSecondOrderMinimizer (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (ε₁ ε₂ : ℝ) : Prop :=
  ‖gradient f x‖ ≤ ε₁ ∧ -ε₂ ≤ Chapter01.hessianMinEig f x

theorem isApproxSecondOrderMinimizer_def {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {ε₁ ε₂ : ℝ} :
    IsApproxSecondOrderMinimizer f x ε₁ ε₂ ↔
      ‖gradient f x‖ ≤ ε₁ ∧ -ε₂ ≤ Chapter01.hessianMinEig f x :=
  Iff.rfl

/-- (3.2.6) is the backbone's `Optimization.IsApproxSecondOrder`. -/
theorem isApproxSecondOrderMinimizer_iff {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {ε₁ ε₂ : ℝ} :
    IsApproxSecondOrderMinimizer f x ε₁ ε₂ ↔ IsApproxSecondOrder f x ε₁ ε₂ := by
  rw [IsApproxSecondOrderMinimizer, isApproxSecondOrder_iff, norm_gradient_eq]
  rfl

/-- The termination test (3.2.9)/(3.3.4) of TR2 and AR2 with `ε₂ : Option ℝ` (`none` standing for
`ε₂ = +∞`, when only `‖∇f(x)‖ ≤ ε₁` is tested). -/
def stopTest (f : EuclideanSpace ℝ (Fin n) → ℝ) (ε₁ : ℝ) (ε₂ : Option ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  ‖gradient f x‖ ≤ ε₁ ∧ ∀ e ∈ ε₂, -e ≤ Chapter01.hessianMinEig f x

section stopTest

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)} {ε₁ : ℝ}

theorem stopTest_def {ε₂ : Option ℝ} :
    stopTest f ε₁ ε₂ x ↔ ‖gradient f x‖ ≤ ε₁ ∧ ∀ e ∈ ε₂, -e ≤ Chapter01.hessianMinEig f x :=
  Iff.rfl

@[simp]
theorem stopTest_none : stopTest f ε₁ none x ↔ ‖gradient f x‖ ≤ ε₁ := by
  simp [stopTest]

theorem stopTest_none_eq : stopTest f ε₁ none = fun x => ‖gradient f x‖ ≤ ε₁ :=
  funext fun _ => propext stopTest_none

@[simp]
theorem stopTest_some {e : ℝ} :
    stopTest f ε₁ (some e) x ↔ IsApproxSecondOrderMinimizer f x ε₁ e := by
  simp [stopTest, IsApproxSecondOrderMinimizer]

/-- The test fails iff `‖∇f(x)‖ > ε₁` or `λ_min[∇²f(x)] < -ε₂` ((3.2.18)). -/
theorem not_stopTest_some {e : ℝ} :
    ¬ stopTest f ε₁ (some e) x ↔ ε₁ < ‖gradient f x‖ ∨ Chapter01.hessianMinEig f x < -e := by
  rw [stopTest_some, IsApproxSecondOrderMinimizer, not_and_or, not_le, not_le]

/-- The strict-local-minimizer test of Step 1 implies (3.2.9). -/
theorem stopTest_of_strict {e : ℝ} (he : 0 ≤ e) (hg : ‖gradient f x‖ ≤ ε₁)
    (hl : e < Chapter01.hessianMinEig f x) : stopTest f ε₁ (some e) x :=
  stopTest_some.2 ⟨hg, by linarith⟩

end stopTest

/-! ### The TR2 algorithm -/

/-- The quadratic Taylor model `T_{f,2}(x, s) = f(x) + ⟪∇f(x), s⟫ + ½⟪s, ∇²f(x) s⟫` of TR2: the
TR1 model (2.3.1) with `B = ∇²f(x)`. -/
noncomputable def tr2Model (f : EuclideanSpace ℝ (Fin n) → ℝ) (x s : EuclideanSpace ℝ (Fin n)) :
    ℝ :=
  Chapter02.tr1Model f x (hessianOperator f x) s

section Model

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {x s : EuclideanSpace ℝ (Fin n)}

theorem tr2Model_eq : tr2Model f x s = f x + quadModel (gradient f x) (hessianOperator f x) s :=
  Chapter02.tr1Model_eq

/-- For `f` `C²` at `x`, the TR2 model is the Taylor polynomial `T_{f,2}(x, ·)`. -/
theorem tr2Model_eq_taylorPolynomial (hf : ContDiffAt ℝ 2 f x) :
    tr2Model f x s = taylorPolynomial f 2 x s := by
  rw [tr2Model_eq, taylorPolynomial_two_eq_quadModel hf]

theorem tr2Model_zero_sub :
    tr2Model f x 0 - tr2Model f x s = -quadModel (gradient f x) (hessianOperator f x) s :=
  Chapter02.tr1Model_zero_sub

end Model

/-- The **eigenpoint step** (3.2.5) of [cartis2022evaluation]: `t ≥ 0` minimizes the model
`q(τ u)` over `τ ≥ 0` with `τ u` in the trust region `‖τ u‖ ≤ Δ`. -/
def IsEigenpointStep {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (g : E)
    (H : E →L[ℝ] E) (Δ : ℝ) (u : E) (t : ℝ) : Prop :=
  0 ≤ t ∧ t * ‖u‖ ≤ Δ ∧ ∀ τ, 0 ≤ τ → τ * ‖u‖ ≤ Δ → quadModel g H (t • u) ≤ quadModel g H (τ • u)

/-- The eigenpoint condition (3.2.10) of TR2 at an iterate `x` with radius `Δ`: if
`λ_min[∇²f(x)] < 0`, the step decreases the model at least as much as the eigenpoint `t u` for a
unit eigenvector `u` of `λ_min` with `⟪u, ∇f(x)⟫ ≤ 0` (3.2.3) and an eigenpoint step `t` (3.2.5);
otherwise `s^E = 0`. -/
def tr2EigenCondition (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) (Δ : ℝ)
    (s : EuclideanSpace ℝ (Fin n)) : Prop :=
  (Chapter01.hessianMinEig f x < 0 → ∃ u t, ‖u‖ = 1 ∧
      hessianOperator f x u = Chapter01.hessianMinEig f x • u ∧ ⟪u, gradient f x⟫ ≤ 0 ∧
      IsEigenpointStep (gradient f x) (hessianOperator f x) Δ u t ∧
      tr2Model f x s ≤ tr2Model f x (t • u)) ∧
    (0 ≤ Chapter01.hessianMinEig f x → tr2Model f x s ≤ tr2Model f x 0)

/-- Step 2 of Algorithm 3.2.1: the TR1 conditions (trust region and Cauchy decrease (2.3.4)–(2.3.5))
for `B = ∇²f(x)` and, if `ε₂ < ∞`, the eigenpoint condition (3.2.10). -/
def tr2Step (f : EuclideanSpace ℝ (Fin n) → ℝ) (ε₂ : Option ℝ) (x : EuclideanSpace ℝ (Fin n))
    (Δ : ℝ) (s : EuclideanSpace ℝ (Fin n)) : Prop :=
  Chapter02.tr1Step f (hessianOperator f x) x Δ s ∧ (ε₂ ≠ none → tr2EigenCondition f x Δ s)

/-- The ratio (3.2.11): `ρ = (f(x) - f(x + s)) / (T_{f,2}(x, 0) - T_{f,2}(x, s))`. -/
noncomputable def tr2Ratio (f : EuclideanSpace ℝ (Fin n) → ℝ) (x s : EuclideanSpace ℝ (Fin n)) :
    ℝ :=
  Chapter02.tr1Ratio f x (hessianOperator f x) s

theorem tr2Ratio_eq (f : EuclideanSpace ℝ (Fin n) → ℝ) (x s : EuclideanSpace ℝ (Fin n)) :
    tr2Ratio f x s = reductionRatio f x s (-quadModel (gradient f x) (hessianOperator f x) s) := by
  rw [tr2Ratio, Chapter02.tr1Ratio_def, Chapter02.tr1Model_zero_sub]

/-- **Algorithm 3.2.1** (TR2) of [cartis2022evaluation], as a run predicate on iterates `x`, steps
`s` and radii `Δ` (constants `P` as in (3.2.8)): `ε₁ > 0`, `ε₂ > 0` if finite, and the generic
trust-region run `Optimization.IsTRRun` with the termination test `stopTest f ε₁ ε₂` (3.2.9),
Step 2 `tr2Step` and the ratio (3.2.11) `tr2Ratio`: `Δ_0 = Δ₀` and, before termination, the step
conditions, the acceptance of Step 3 and the radius update (3.2.12). -/
structure algorithm_3_2_1 (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : Chapter02.TR1Params)
    (ε₁ : ℝ) (ε₂ : Option ℝ) (x s : ℕ → EuclideanSpace ℝ (Fin n)) (Δ : ℕ → ℝ) : Prop where
  /-- The first-order tolerance is positive. -/
  ε₁_pos : 0 < ε₁
  /-- The second-order tolerance is positive. -/
  ε₂_pos : ∀ e ∈ ε₂, 0 < e
  /-- Steps 1–4. -/
  run : IsTRRun P.toTRParams (fun k => stopTest f ε₁ ε₂ (x k))
    (fun k => tr2Step f ε₂ (x k) (Δ k) (s k)) (fun k => tr2Ratio f (x k) (s k)) x s Δ

/-! ### Lemma 3.2.3: the eigenpoint -/

section Eigenpoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Lemma 3.2.3** of [cartis2022evaluation], the eigenpoint. Let `u` be a unit vector with
`⟪u, H u⟫ = λ < 0` and `⟪u, g⟫ ≤ 0` (3.2.3), and `Δ ≥ 0`. Then the eigenpoint step (3.2.5) is
`t = Δ` (it is one, and every eigenpoint step is `Δ`, so `s^E = Δ u` is on the boundary), and
`q(Δ u) ≤ -½ |λ| Δ²` (3.2.15). -/
theorem lemma_3_2_3 {g : E} {H : E →L[ℝ] E} {u : E} {lam Δ : ℝ} (hu : ‖u‖ = 1)
    (hHu : ⟪u, H u⟫ = lam) (hlam : lam < 0) (hgu : ⟪u, g⟫ ≤ 0) (hΔ : 0 ≤ Δ) :
    IsEigenpointStep g H Δ u Δ ∧ (∀ t, IsEigenpointStep g H Δ u t → t = Δ) ∧
      quadModel g H (Δ • u) ≤ -(1 / 2 * |lam| * Δ ^ 2) := by
  have hgu' : ⟪g, u⟫ ≤ 0 := by rwa [real_inner_comm]
  have hq : ∀ τ, quadModel g H (τ • u) = τ * ⟪g, u⟫ + τ ^ 2 / 2 * lam := fun τ => by
    rw [quadModel_smul, hHu]
  refine ⟨⟨hΔ, by rw [hu, mul_one], fun τ hτ hτΔ => ?_⟩, fun t ⟨ht0, htΔ, ht⟩ => ?_, ?_⟩
  · rw [hu, mul_one] at hτΔ
    exact ((quadModel_smul_le_of_curvature hHu hlam.le hgu' hΔ).2 τ ⟨hτ, hτΔ⟩)
  · rw [hu, mul_one] at htΔ
    by_contra hne
    have hlt : t < Δ := lt_of_le_of_ne htΔ hne
    have := ht Δ hΔ (by rw [hu, mul_one])
    rw [hq, hq] at this
    have : (Δ - t) * (⟪g, u⟫ + lam / 2 * (t + Δ)) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) (by nlinarith)
    nlinarith
  · have := (quadModel_smul_le_of_curvature hHu hlam.le hgu' hΔ).1
    rw [abs_of_neg hlam]
    linarith

end Eigenpoint

section Run

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : Chapter02.TR1Params} {ε₁ : ℝ}
  {ε₂ : Option ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)} {Δ : ℕ → ℝ}

namespace algorithm_3_2_1

/-- The radii are positive up to (and including) termination. -/
theorem delta_pos (h : algorithm_3_2_1 f P ε₁ ε₂ x s Δ) {k : ℕ}
    (hk : ∀ j < k, ¬ stopTest f ε₁ ε₂ (x j)) : 0 < Δ k :=
  h.run.delta_pos hk k le_rfl

/-- With `ε₂ = +∞`, a TR2 run is a TR1 run with `B_k = ∇²f(x_k)` ([cartis2022evaluation],
§3.2.2), provided the Hessians are symmetric (e.g. `f` is `C²`). -/
theorem toAlgorithm_2_3_1 (h : algorithm_3_2_1 f P ε₁ none x s Δ) (hf : ContDiff ℝ 2 f) :
    Chapter02.algorithm_2_3_1 f P ε₁ (fun k => hessianOperator f (x k)) x s Δ := by
  refine ⟨h.ε₁_pos, fun k => hessianOperator_isSymmetric hf.contDiffAt, ?_⟩
  have hrun := h.run.mono (step' := fun k => Chapter02.tr1Step f (hessianOperator f (x k)) (x k)
    (Δ k) (s k)) fun k hk => hk.1
  simp only [stopTest_none] at hrun
  exact hrun

/-- The model decrease of a TR2 step dominates the Cauchy decrease (2.3.12). -/
theorem cauchy_le_pred (h : algorithm_3_2_1 f P ε₁ ε₂ x s Δ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopTest f ε₁ ε₂ (x j)) :
    1 / 2 * ‖gradient f (x k)‖ *
        min (‖gradient f (x k)‖ / (1 + ‖hessianOperator f (x k)‖)) (Δ k) ≤
      tr2Model f (x k) 0 - tr2Model f (x k) (s k) := by
  obtain ⟨⟨-, t, ht, hm⟩, -⟩ := h.run.step k hk
  have := Chapter02.lemma_2_3_2 f (x k) (hessianOperator f (x k)) ht
  unfold tr2Model
  linarith

/-- The eigenpoint decrease (3.2.15) of a TR2 step when `ε₂ < ∞` and `λ_min[∇²f(x_k)] < 0`:
`T_{f,2}(x_k, 0) - T_{f,2}(x_k, s_k) ≥ ½ |λ_min| Δ_k²`, together with the eigenpoint `Δ_k u_k`
satisfying (3.2.10) along an eigenvector `u_k` of (3.2.3). -/
theorem eigen_le_pred (h : algorithm_3_2_1 f P ε₁ ε₂ x s Δ) (hε₂ : ε₂ ≠ none) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopTest f ε₁ ε₂ (x j)) (hlam : Chapter01.hessianMinEig f (x k) < 0) :
    (∃ u, ‖u‖ = 1 ∧ ⟪u, hessianOperator f (x k) u⟫ = Chapter01.hessianMinEig f (x k) ∧
      ⟪gradient f (x k), u⟫ ≤ 0 ∧
      quadModel (gradient f (x k)) (hessianOperator f (x k)) (s k) ≤
        quadModel (gradient f (x k)) (hessianOperator f (x k)) (Δ k • u)) ∧
      1 / 2 * |Chapter01.hessianMinEig f (x k)| * Δ k ^ 2 ≤
        tr2Model f (x k) 0 - tr2Model f (x k) (s k) := by
  obtain ⟨-, heig⟩ := h.run.step k hk
  obtain ⟨u, t, hu, hHu, hgu, ht, hm⟩ := (heig hε₂).1 hlam
  have hΔ : 0 ≤ Δ k := (h.delta_pos fun j hj => hk j hj.le).le
  have hHu' : ⟪u, hessianOperator f (x k) u⟫ = Chapter01.hessianMinEig f (x k) := by
    rw [hHu, inner_smul_right, real_inner_self_eq_norm_sq, hu]; ring
  obtain ⟨-, huniq, hdec⟩ := lemma_3_2_3 (g := gradient f (x k)) hu hHu' hlam hgu hΔ
  rw [huniq t ht] at hm
  rw [tr2Model_eq, tr2Model_eq] at hm
  refine ⟨⟨u, hu, hHu', by rwa [real_inner_comm], by linarith⟩, ?_⟩
  rw [tr2Model_zero_sub]
  linarith

end algorithm_3_2_1

/-- **Lemma 3.2.3**, second part: in a TR2 run with `ε₂ < ∞`, if `λ_min[∇²f(x_k)] < 0` at an
iteration `k` before termination, the denominator of the ratio (3.2.11) is positive. -/
theorem lemma_3_2_3_pred_pos (h : algorithm_3_2_1 f P ε₁ ε₂ x s Δ) (hε₂ : ε₂ ≠ none) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopTest f ε₁ ε₂ (x j)) (hlam : Chapter01.hessianMinEig f (x k) < 0) :
    0 < tr2Model f (x k) 0 - tr2Model f (x k) (s k) := by
  have hΔ := h.delta_pos fun j hj => hk j hj.le
  refine lt_of_lt_of_le ?_ (h.eigen_le_pred hε₂ hk hlam).2
  have := abs_pos.2 hlam.ne
  positivity

/-- **Lemma 3.2.4** of [cartis2022evaluation]. Under f.HL, in a TR2 run with `ε₂ < ∞`, if `k` is
before termination, `λ_min[∇²f(x_k)] < 0` and `Δ_k < 3(1 - η₂) |λ_min[∇²f(x_k)]| / L_{f,2}`
(3.2.16), then `ρ_k ≥ η₂`, iteration `k` is successful and `Δ_{k+1} ≥ Δ_k`. -/
theorem lemma_3_2_4 {L₂ : ℝ} (hf : AssumptionHL f L₂) (h : algorithm_3_2_1 f P ε₁ ε₂ x s Δ)
    (hε₂ : ε₂ ≠ none) {k : ℕ} (hk : ∀ j ≤ k, ¬ stopTest f ε₁ ε₂ (x j))
    (hlam : Chapter01.hessianMinEig f (x k) < 0)
    (hΔk : Δ k < 3 * (1 - P.η₂) * |Chapter01.hessianMinEig f (x k)| / L₂) :
    P.η₂ ≤ tr2Ratio f (x k) (s k) ∧ P.η₁ ≤ tr2Ratio f (x k) (s k) ∧ Δ k ≤ Δ (k + 1) := by
  obtain ⟨⟨u, hu, hHu, hgu, hsE⟩, -⟩ := h.eigen_le_pred hε₂ hk hlam
  obtain ⟨⟨hs, -⟩, -⟩ := h.run.step k hk
  have hΔ := h.delta_pos fun j hj => hk j hj.le
  have h2 : P.η₂ ≤ tr2Ratio f (x k) (s k) := by
    rw [tr2Ratio_eq]
    exact le_reductionRatio_trust_second_of_curvature convex_univ
      (fun y _ => hf.contDiffAt y) hf.iteratedFDerivLipschitzOn hf.pos (mem_univ _) (mem_univ _)
      hHu hlam hgu hsE hs hΔ hΔk
  exact ⟨h2, P.η₁_le_η₂.trans h2, (h.run.update hk).le_of_very_successful h2⟩

/-- **Lemma 2.3.3 for TR2** (first-order successful iterations): under f.HBa, if `k` is before
termination and `Δ_k < (1 - η₂) ‖∇f(x_k)‖ / (4 κ_H)` then `ρ_k ≥ η₂`. -/
theorem tr2_ratio_ge_of_first {κH : ℝ} (hf : AssumptionHBa f κH)
    (h : algorithm_3_2_1 f P ε₁ ε₂ x s Δ) {k : ℕ} (hk : ∀ j ≤ k, ¬ stopTest f ε₁ ε₂ (x j))
    (hg : 0 < ‖gradient f (x k)‖) (hΔk : Δ k < (1 - P.η₂) * ‖gradient f (x k)‖ / (4 * κH)) :
    P.η₂ ≤ tr2Ratio f (x k) (s k) := by
  have hΔ := h.delta_pos fun j hj => hk j hj.le
  exact Chapter02.tr1Ratio_ge_of_tr1Step hf.assumptionGL (h.run.step k hk).1
    ((hf.assumptionMHBa x).bound k) hΔ hg (P.η₁_pos.trans_le P.η₁_le_η₂).le
    (by rw [show 2 * (κH + κH) = 4 * κH by ring]; exact hΔk)

end Run

/-! ### One-dimensional examples

The sharpness examples of Chapter 3 are ridge functions `x ↦ G ⟪e₀, x⟫` on `ℝ¹` (with
`Chapter02.e₀` the unit vector). Their Taylor models, gradients, Hessians and curvatures reduce to
those of `G`. -/

section OneDim

open Chapter02 (e₀ norm_e₀ inner_e₀_smul)

/-- Every vector of `ℝ¹` is a multiple of `e₀`. -/
theorem eq_inner_e₀_smul (s : EuclideanSpace ℝ (Fin 1)) : s = ⟪e₀, s⟫ • e₀ :=
  EuclideanSpace.eq_inner_single_smul s

theorem norm_eq_abs_inner_e₀ (s : EuclideanSpace ℝ (Fin 1)) : ‖s‖ = |⟪e₀, s⟫| :=
  EuclideanSpace.norm_eq_abs_inner_single s

theorem inner_e₀_sq (s : EuclideanSpace ℝ (Fin 1)) : ⟪e₀, s⟫ ^ 2 = ‖s‖ ^ 2 :=
  EuclideanSpace.inner_single_sq s

/-- The quadratic Taylor polynomial of a ridge function on `ℝ¹`:
`T_{f,2}(x, s) = G(a) + G'(a) t + G''(a) t²/2` with `a = ⟪e₀, x⟫`, `t = ⟪e₀, s⟫`. -/
theorem taylorPolynomial_two_ridge {G : ℝ → ℝ} (hG : ContDiff ℝ 2 G)
    (x s : EuclideanSpace ℝ (Fin 1)) :
    taylorPolynomial (ridge G e₀) 2 x s =
      G ⟪e₀, x⟫ + deriv G ⟪e₀, x⟫ * ⟪e₀, s⟫ + iteratedDeriv 2 G ⟪e₀, x⟫ * ⟪e₀, s⟫ ^ 2 / 2 := by
  rw [taylorPolynomial_ridge hG]
  simp [sum_range_succ, Nat.factorial, iteratedDeriv_one]
  ring

/-- The Hessian of a ridge function on `ℝ¹` acts as multiplication by `G''(⟪e₀, x⟫)`. -/
theorem hessianOperator_ridge {G : ℝ → ℝ} (hG : ContDiff ℝ 2 G)
    (x u : EuclideanSpace ℝ (Fin 1)) :
    hessianOperator (ridge G e₀) x u = iteratedDeriv 2 G ⟪e₀, x⟫ • u :=
  Optimization.hessianOperator_ridge_single hG x u

/-- The least curvature of a ridge function on `ℝ¹` is `G''(⟪e₀, x⟫)`. -/
theorem hessianMinEig_ridge {G : ℝ → ℝ} (hG : ContDiff ℝ 2 G) (x : EuclideanSpace ℝ (Fin 1)) :
    Chapter01.hessianMinEig (ridge G e₀) x = iteratedDeriv 2 G ⟪e₀, x⟫ :=
  minCurvature_iteratedFDeriv_ridge_of_forall hG norm_e₀ inner_e₀_sq x

/-- A one-dimensional `C²` function `G` with `|G^{(j)}| ≤ B` (`j ≤ 2`) and `L`-Lipschitz second
derivative, lifted to `ℝ¹` along `e₀`, satisfies f.Bb (`f_low = -B`), f.gL and f.HBa (constant
`max B 1`) and f.HL (constant `max L 1`); its gradient is `G'(⟪e₀, x⟫) e₀`. -/
theorem ridge_assumptions_two {G : ℝ → ℝ} {L B : ℝ} (hG : ContDiff ℝ 2 G)
    (hGL : ∀ s t, |iteratedDeriv 2 G s - iteratedDeriv 2 G t| ≤ L * |s - t|)
    (hGB : ∀ j ≤ 2, ∀ t, |iteratedDeriv j G t| ≤ B) :
    Chapter02.AssumptionBb (ridge G e₀) (-B) ∧ Chapter02.AssumptionGL (ridge G e₀) (max B 1) ∧
      AssumptionHBa (ridge G e₀) (max B 1) ∧ AssumptionHL (ridge G e₀) (max L 1) ∧
      ∀ y, gradient (ridge G e₀) y = deriv G ⟪e₀, y⟫ • e₀ := by
  have hL0 : 0 ≤ L := by
    by_contra hneg
    have := (abs_nonneg _).trans (hGL 1 0)
    simp at this
    linarith
  have hHBa : AssumptionHBa (ridge G e₀) (max B 1) := ⟨contDiff_ridge hG, le_max_right _ _,
    fun x => (norm_iteratedFDeriv_ridge_le hG (by norm_num) norm_e₀.le x).trans
      ((hGB 2 le_rfl _).trans (le_max_left _ _))⟩
  have hb : Chapter02.AssumptionBb (ridge G e₀) (-B) := fun y => by
    have := hGB 0 (by norm_num) ⟪e₀, y⟫
    rw [iteratedDeriv_zero] at this
    rw [ridge_apply]; linarith [neg_abs_le (G ⟪e₀, y⟫)]
  have hlip : ∀ x y, ‖iteratedFDeriv ℝ 2 (ridge G e₀) x - iteratedFDeriv ℝ 2 (ridge G e₀) y‖ ≤
      max L 1 * ‖x - y‖ := fun x y => by
    have h := iteratedFDerivLipschitzOn_ridge hG (by norm_num) norm_e₀.le hL0 hGL
    exact (iteratedFDerivLipschitzOn_iff.1 h x (mem_univ _) y (mem_univ _)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  exact ⟨hb, hHBa.assumptionGL, hHBa, .of_lipschitz (contDiff_ridge hG) (le_max_right _ _) hlip,
    gradient_ridge (hG.differentiable (by norm_num))⟩

end OneDim

section Main

variable {f : EuclideanSpace ℝ (Fin n) → ℝ}

/-! ### Existence of TR2 runs -/

/-- **Eigenvectors of the leftmost eigenvalue** (3.2.3): for `f` `C²` at `x` with
`λ_min[∇²f(x)] < 0` there is a unit `u` with `∇²f(x) u = λ_min u` and `⟪u, ∇f(x)⟫ ≤ 0`. -/
theorem exists_eigenvector_hessianMinEig {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hf : ContDiffAt ℝ 2 f x)
    (hlam : Chapter01.hessianMinEig f x < 0) :
    ∃ u, ‖u‖ = 1 ∧ hessianOperator f x u = Chapter01.hessianMinEig f x • u ∧
      ⟪u, gradient f x⟫ ≤ 0 :=
  exists_eigenvector_hessianOperator hf hlam

/-- A global minimizer of the TR2 model in the trust region satisfies Step 2 of TR2. -/
theorem tr2Step_of_isMinOn {x : EuclideanSpace ℝ (Fin n)} (hf : ContDiffAt ℝ 2 f x)
    (ε₂ : Option ℝ) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    {s : EuclideanSpace ℝ (Fin n)} (hs : ‖s‖ ≤ Δ)
    (hmin : IsMinOn (quadModel (gradient f x) (hessianOperator f x)) (Metric.closedBall 0 Δ) s) :
    tr2Step f ε₂ x Δ s := by
  obtain ⟨hC, hE⟩ := quadModel_le_of_isMinOn_ball hmin
  obtain ⟨t, ht⟩ := exists_isCauchyStep (gradient f x) (hessianOperator f x) hΔ
  refine ⟨⟨hs, t, ht, ?_⟩, fun _ => ⟨fun hlam => ?_, fun _ => ?_⟩⟩
  · rw [Chapter02.tr1Model_eq, Chapter02.tr1Model_eq]
    linarith [hC t ht]
  · obtain ⟨u, hu, hHu, hgu⟩ := exists_eigenvector_hessianMinEig hf hlam
    have hHu' : ⟪u, hessianOperator f x u⟫ = Chapter01.hessianMinEig f x := by
      rw [hHu, inner_smul_right, real_inner_self_eq_norm_sq, hu]; ring
    refine ⟨u, Δ, hu, hHu, hgu, (lemma_3_2_3 hu hHu' hlam hgu hΔ).1, ?_⟩
    rw [tr2Model_eq, tr2Model_eq]
    linarith [hE hΔ u hu]
  · rw [tr2Model_eq, tr2Model_eq]
    have := hmin (Metric.mem_closedBall_self hΔ)
    simp only [mem_ofPred_eq] at this
    linarith

/-- **Existence of TR2 runs** ([cartis2022evaluation], Algorithm 3.2.1 is well defined): for a
`C²` function, all constants, tolerances `ε₁ > 0`, `ε₂ > 0` (or `+∞`) and every starting point
there is a TR2 run (the global minimizer of the model in the trust region satisfies the Cauchy and
eigenpoint conditions). -/
theorem exists_algorithm_3_2_1 (hf : ContDiff ℝ 2 f) (P : Chapter02.TR1Params) {ε₁ : ℝ}
    (hε₁ : 0 < ε₁) {ε₂ : Option ℝ} (hε₂ : ∀ e ∈ ε₂, 0 < e) (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∃ x s Δ, x 0 = x₀ ∧ algorithm_3_2_1 f P ε₁ ε₂ x s Δ := by
  obtain ⟨x, s, Δ, hx0, hrun, -⟩ := exists_isTRRun P.toTRParams (Inv := fun _ => True)
    (test := stopTest f ε₁ ε₂) (stepOK := fun _ y Δ s => tr2Step f ε₂ y Δ s)
    (fun _ y _ s => tr2Ratio f y s) (fun _ y Δ _ hΔ _ => by
      obtain ⟨s, hs, hmin, -, -⟩ :=
        exists_isMinOn_quadModel_ball (gradient f y) (hessianOperator f y) hΔ.le
      exact ⟨s, tr2Step_of_isMinOn hf.contDiffAt ε₂ hΔ.le hs hmin, trivial⟩) trivial
  exact ⟨x, s, Δ, hx0, hε₁, hε₂, hrun⟩

/-! ### Theorem 3.2.1 -/

/-- The constant `κ^S_TR2 = 8 κ_H/(γ₁ η₁ (1 - η₂)) max(1, ‖∇f(x₀)‖/Δ₀)` of Theorem 3.2.1
(with `g₀ = ‖∇f(x₀)‖`). -/
noncomputable def kappaSTR2 (P : Chapter02.TR1Params) (κH g₀ : ℝ) : ℝ :=
  8 * κH / (P.γ₁ * P.η₁ * (1 - P.η₂)) * max 1 (g₀ / P.Δ₀)

/-- The constant `κ^C_TR2 = |log(γ₁ (1 - η₂)/(4 Δ₀ κ_H) min(1, Δ₀/‖∇f(x₀)‖))|/|log γ₂| + 1` of
Theorem 3.2.1. -/
noncomputable def kappaCTR2 (P : Chapter02.TR1Params) (κH g₀ : ℝ) : ℝ :=
  |Real.log (P.γ₁ * (1 - P.η₂) / (4 * P.Δ₀ * κH) * min 1 (P.Δ₀ / g₀))| / |Real.log P.γ₂| + 1

/-- `κ^S_TR2` is TR1's `κ^S` with `κ_B = κ_H = L_{f,1}` ((3.2.13)). -/
theorem kappaSTR2_eq (P : Chapter02.TR1Params) (κH g₀ : ℝ) :
    kappaSTR2 P κH g₀ = Chapter02.kappaSTR1 P κH κH g₀ := by
  rw [kappaSTR2, Chapter02.kappaSTR1]; ring

/-- `κ^C_TR2` is TR1's `κ^C` with `κ_B = κ_H = L_{f,1}` ((3.2.13)). -/
theorem kappaCTR2_eq (P : Chapter02.TR1Params) (κH g₀ : ℝ) :
    kappaCTR2 P κH g₀ = Chapter02.kappaCTR1 P κH κH g₀ := by
  rw [kappaCTR2, Chapter02.kappaCTR1]
  congr 4
  ring

/-- **Theorem 3.2.1** of [cartis2022evaluation] (first-order complexity of TR2). Under f.Bb and
f.HBa, every TR2 run with `ε₂ = +∞` terminates at an iteration `k_ε` (the first with
`‖∇f(x_k)‖ ≤ ε₁`) after at most `κ^A (f(x₀) - f_low)/ε₁² + κ^B |log ε₁| + κ^C` evaluations of `f`
and at most `κ^S (f(x₀) - f_low)/ε₁² + 1` evaluations of `∇f` and `∇²f`, with `κ^S = kappaSTR2`,
`κ^A = κ^S (1 + log γ₃/|log γ₂|)`, `κ^B = 1/|log γ₂|` and `κ^C = kappaCTR2`. (TR2 with `ε₂ = +∞`
is TR1 with `B_k = ∇²f(x_k)`, and Theorem 2.3.7 applies with `κ_B = κ_H = L_{f,1}`.) -/
theorem theorem_3_2_1 {P : Chapter02.TR1Params} {ε₁ κH flow : ℝ}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {Δ : ℕ → ℝ} (hb : Chapter02.AssumptionBb f flow)
    (hf : AssumptionHBa f κH) (h : algorithm_3_2_1 f P ε₁ none x s Δ) :
    ∃ kε, IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε₁) kε ∧
      (funEvalCount kε : ℝ) ≤
        kappaSTR2 P κH ‖gradient f (x 0)‖ * (1 + Real.log P.γ₃ / |Real.log P.γ₂|) *
            (f (x 0) - flow) / ε₁ ^ 2 +
          1 / |Real.log P.γ₂| * |Real.log ε₁| + kappaCTR2 P κH ‖gradient f (x 0)‖ ∧
      (derivEvalCount (fun k => P.η₁ ≤ tr2Ratio f (x k) (s k)) kε : ℝ) ≤
        kappaSTR2 P κH ‖gradient f (x 0)‖ * (f (x 0) - flow) / ε₁ ^ 2 + 1 := by
  rw [kappaSTR2_eq, kappaCTR2_eq]
  exact Chapter02.theorem_2_3_7 hb hf.assumptionGL (hf.assumptionMHBa x)
    (h.toAlgorithm_2_3_1 hf.contDiff)

/-! ### Theorem 3.2.2 -/

open NewtonSlow in
/-- **Theorem 3.2.2** of [cartis2022evaluation] (slow first-order convergence of TR2). There are
`f_low`, `κ_H ≥ 1` and `L_{f,2} ≥ 1` such that for every `ε₁ ∈ (0,1)` there is `f : ℝ² → ℝ`
satisfying f.Bb, f.HBa and f.HL (the function of Theorem 3.1.1) such that, for all TR2 constants
with `Δ₀ = 2` and every `ε₂` (finite or not), the Newton iterates form a TR2 run from `x₀ = 0` with
`Δ_k = 2` and `ρ_k = 1` (every iteration very successful), which terminates exactly at iteration
`k_ε = ⌈ε₁⁻²⌉`, after `k_ε + 1` evaluations of `f`, `∇f` and `∇²f`. -/
theorem theorem_3_2_2 :
    ∃ flow κH L₂ : ℝ, 1 ≤ κH ∧ 1 ≤ L₂ ∧ ∀ ε₁ : ℝ, 0 < ε₁ → ε₁ < 1 →
      ∃ f : EuclideanSpace ℝ (Fin 2) → ℝ, Chapter02.AssumptionBb f flow ∧
        AssumptionHBa f κH ∧ AssumptionHL f L₂ ∧
        ∀ P : Chapter02.TR1Params, P.Δ₀ = 2 → ∀ ε₂ : Option ℝ, (∀ e ∈ ε₂, 0 < e) →
          ∃ x s Δ, x 0 = 0 ∧ algorithm_3_2_1 f P ε₁ ε₂ x s Δ ∧ (∀ k, Δ k = 2) ∧
            (∀ k < ⌈(ε₁ ^ 2)⁻¹⌉₊, tr2Ratio f (x k) (s k) = 1) ∧
            IsFirstHit (fun k => stopTest f ε₁ ε₂ (x k)) ⌈(ε₁ ^ 2)⁻¹⌉₊ := by
  obtain ⟨B, -, H⟩ := exists_example
  refine ⟨-B, max B 1, max B 1, le_max_right _ _, le_max_right _ _, fun ε hε hε1 => ?_⟩
  obtain ⟨f, hf, hbd, hjet⟩ := H ε hε hε1
  obtain ⟨hb, -, hhl⟩ := assumptions_of_bounded hf hbd
  have hHBa : AssumptionHBa f (max B 1) := ⟨hf.of_le (by norm_num), le_max_right _ _,
    fun x => ((hbd x).2 2 (by norm_num)).trans (le_max_left _ _)⟩
  refine ⟨f, hb, hHBa, hhl, fun P hP ε₂ hε₂ => ?_⟩
  set K := kε ε
  have hC2 : ∀ y, ContDiffAt ℝ 2 f y := fun y => hhl.contDiffAt y
  have hpd : ∀ k ≤ K, 0 < Chapter01.hessianMinEig f (iter ε k) := fun k hk =>
    hessianMinEig_pos hε hε1 hk (hjet k hk).2.2
  have hnewton : ∀ k < K, IsNewtonStep f (iter ε k) (NewtonSlow.step ε k) := fun k hk =>
    isNewtonStep_of_jet hε hε1 hk (hjet k hk.le).2.1 (hjet k hk.le).2.2
  have hmin : ∀ k < K, IsMinOn (tr2Model f (iter ε k)) univ (NewtonSlow.step ε k) := fun k hk => by
    have := ((isNewtonStep_iff_isMinOn (hC2 _) (hpd k hk.le) (hnewton k hk)
      (NewtonSlow.step ε k)).2).2 rfl
    intro y _
    simp only [mem_ofPred_eq, tr2Model_eq_taylorPolynomial (hC2 _)]
    exact this (mem_univ y)
  -- the test
  have htest : ∀ k ≤ K, (stopTest f ε ε₂ (iter ε k) ↔ K ≤ k) := fun k hk => by
    constructor
    · intro h
      by_contra hlt
      exact absurd h.1 (by rw [(hjet k hk).2.1]; exact not_le.2 (lt_norm_grad hε hε1
        (not_le.1 hlt)))
    · intro hKk
      refine ⟨by rw [(hjet k hk).2.1, grad, ite_eq_right (not_lt.2 hKk), norm_zero]; exact hε.le,
        fun e he => by linarith [hε₂ e he, hpd k hk]⟩
  have hhit : IsFirstHit (fun k => stopTest f ε ε₂ (iter ε k)) K :=
    ⟨(htest K le_rfl).2 le_rfl, fun j hj h => absurd ((htest j hj.le).1 h) (not_le.2 hj)⟩
  -- the ratio
  have hratio : ∀ k < K, tr2Ratio f (iter ε k) (NewtonSlow.step ε k) = 1 := fun k hk => by
    have hd := taylorPolynomial_two_add_sub (hC2 (iter ε k)) (hnewton k hk) (-NewtonSlow.step ε k)
    rw [add_neg_cancel, taylorPolynomial_zero_right] at hd
    have hss : iteratedFDeriv ℝ 2 f (iter ε k) (fun _ => -NewtonSlow.step ε k) = 2 * ε ^ 2 := by
      rw [(hjet k hk.le).2.2, hess_apply]
      simp only [inner_neg_right, inner_e₁_step hk, inner_e₂_step hk]
      have := (fval_pos hε hε1 hk.le).ne'
      field_simp
      ring
    rw [hss] at hd
    rw [tr2Ratio, Chapter02.tr1Ratio_def, ← tr2Model, ← tr2Model,
      tr2Model_eq_taylorPolynomial (hC2 _), tr2Model_eq_taylorPolynomial (hC2 _),
      taylorPolynomial_zero_right, reductionRatio_def, ← iter_succ, (hjet k hk.le).1,
      (hjet (k + 1) hk).1]
    have hpred : fval ε k - taylorPolynomial f 2 (iter ε k) (NewtonSlow.step ε k) = ε ^ 2 := by
      rw [← (hjet k hk.le).1]; linarith
    rw [hpred, fval, fval]
    push_cast
    field_simp
    ring
  have hbefore : ∀ k, (∀ j ≤ k, ¬ stopTest f ε ε₂ (iter ε j)) → k < K := fun k hk =>
    not_le.1 fun hle => hk K hle hhit.test
  have hstep : ∀ k < K, tr2Step f ε₂ (iter ε k) 2 (NewtonSlow.step ε k) := fun k hk => by
    have hs2 : ‖NewtonSlow.step ε k‖ ≤ 2 := by
      have hf1 := one_lt_fval hε hk
      have hsq : ‖NewtonSlow.step ε k‖ ^ 2 = (fval ε k)⁻¹ ^ 2 * (1 + ε ^ 2) := by
        rw [norm_sq_eq, inner_e₁_step hk, inner_e₂_step hk]; ring
      have : (fval ε k)⁻¹ ^ 2 < 1 := by
        rw [inv_pow]; exact inv_lt_one_of_one_lt₀ (by nlinarith)
      have : ‖NewtonSlow.step ε k‖ ^ 2 ≤ 2 ^ 2 := by
        rw [hsq]; nlinarith [sq_nonneg ε, sq_nonneg (fval ε k)⁻¹]
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) (by norm_num)).1 this
    obtain ⟨t, ht⟩ := exists_isCauchyStep (gradient f (iter ε k))
      (hessianOperator f (iter ε k)) (by norm_num : (0 : ℝ) ≤ 2)
    refine ⟨⟨hs2, t, ht, hmin k hk (mem_univ _)⟩, fun _ => ⟨fun hlam => ?_,
      fun _ => hmin k hk (mem_univ _)⟩⟩
    exact absurd hlam (not_lt.2 (hpd k hk.le).le)
  refine ⟨iter ε, NewtonSlow.step ε, fun _ => 2, iter_zero ε, ⟨hε, hε₂, ⟨hP.symm, fun k hk => ?_,
    fun k hk => ?_⟩⟩, fun _ => rfl, fun k hk => hratio k hk, hhit⟩
  · exact hstep k (hbefore k hk)
  · have hk' := hbefore k hk
    change TRAcceptance P.toTRParams (tr2Ratio f (iter ε k) (NewtonSlow.step ε k)) (iter ε k)
      (NewtonSlow.step ε k)
      (iter ε (k + 1)) 2 2
    rw [iter_succ, hratio k hk']
    exact trAcceptance_of_one_le P.toTRParams le_rfl _ _ (by norm_num)

/-! ### Lemma 3.2.5 and Theorem 3.2.6 -/

/-- The constant `κ_Δ = min(γ₁ (1 - η₂)/max(4 κ_H, L_{f,2}/3), Δ₀)` of Lemma 3.2.5. -/
noncomputable def kappaDeltaTR2 (P : Chapter02.TR1Params) (κH L₂ : ℝ) : ℝ :=
  min (P.γ₁ * (1 - P.η₂) / max (4 * κH) (L₂ / 3)) P.Δ₀

section KappaDelta

variable {P : Chapter02.TR1Params} {κH L₂ : ℝ}

theorem kappaDeltaTR2_pos (hκ : 1 ≤ κH) : 0 < kappaDeltaTR2 P κH L₂ := by
  have := P.γ₁_pos; have := sub_pos.2 P.η₂_lt_one
  have : 0 < max (4 * κH) (L₂ / 3) := lt_max_of_lt_left (by linarith)
  exact lt_min (by positivity) P.Δ₀_pos

/-- `κ_Δ ∈ (0, 1)`: in fact `κ_Δ ≤ 1/4`. -/
theorem kappaDeltaTR2_le_one (hκ : 1 ≤ κH) : kappaDeltaTR2 P κH L₂ ≤ 1 := by
  refine (min_le_left _ _).trans ?_
  have h4 : 0 < 4 * κH := by linarith
  rw [div_le_one (lt_max_of_lt_left h4)]
  have := P.γ₁_le_one; have := P.γ₁_pos; have := P.η₁_pos; have := P.η₁_le_η₂
  have := P.η₂_lt_one
  calc P.γ₁ * (1 - P.η₂) ≤ 1 * 1 := by
        apply mul_le_mul <;> linarith
    _ ≤ 4 * κH := by linarith
    _ ≤ max (4 * κH) (L₂ / 3) := le_max_left _ _

end KappaDelta

variable {P : Chapter02.TR1Params} {ε₁ e κH L₂ : ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)}
  {Δ : ℕ → ℝ}

/-- **Lemma 3.2.5** of [cartis2022evaluation]. Under f.HBa and f.HL, for a TR2 run with
`ε₂ = e ∈ (0, 1]`, at every iteration `k` up to (and including) termination,
`Δ_k ≥ κ_Δ min(ε₁, ε₂)` (3.2.17), with `κ_Δ = kappaDeltaTR2 ∈ (0, 1)`. -/
theorem lemma_3_2_5 (hf : AssumptionHBa f κH) (hl : AssumptionHL f L₂)
    (h : algorithm_3_2_1 f P ε₁ (some e) x s Δ) (he1 : e ≤ 1) {k : ℕ}
    (hk : ∀ j < k, ¬ stopTest f ε₁ (some e) (x j)) :
    kappaDeltaTR2 P κH L₂ * min ε₁ e ≤ Δ k := by
  set m := min ε₁ e
  have he : 0 < e := h.ε₂_pos e rfl
  have hm : 0 < m := lt_min h.ε₁_pos he
  have hm1 : m ≤ 1 := (min_le_right _ _).trans he1
  set M := max (4 * κH) (L₂ / 3)
  have h4 : 0 < 4 * κH := by linarith [hf.one_le]
  have hM : 0 < M := lt_max_of_lt_left h4
  have h1η := sub_pos.2 P.η₂_lt_one
  set θ := (1 - P.η₂) * m / M
  have hmin := h.run.delta_ge (θ := fun _ => θ) hk (fun _ _ => le_rfl) (fun j hj hΔ => by
    have hj' : ∀ i ≤ j, ¬ stopTest f ε₁ (some e) (x i) := fun i hi => hk i (hi.trans_lt hj)
    rcases not_stopTest_some.1 (hj' j le_rfl) with hg | hlam
    · refine tr2_ratio_ge_of_first hf h hj' (h.ε₁_pos.trans hg) (hΔ.trans_le ?_)
      calc θ ≤ (1 - P.η₂) * ε₁ / (4 * κH) :=
            div_le_div₀ (mul_nonneg h1η.le h.ε₁_pos.le)
              (mul_le_mul_of_nonneg_left (min_le_left _ _) h1η.le) h4
              (le_max_left _ _)
        _ ≤ (1 - P.η₂) * ‖gradient f (x j)‖ / (4 * κH) := by gcongr
    · have hlam0 : Chapter01.hessianMinEig f (x j) < 0 := hlam.trans (neg_neg_of_pos he)
      refine (lemma_3_2_4 hl h (Option.some_ne_none e) hj' hlam0 (hΔ.trans_le ?_)).1
      have hL3 : 0 < L₂ / 3 := by linarith [hl.one_le]
      calc θ ≤ (1 - P.η₂) * e / (L₂ / 3) :=
            div_le_div₀ (mul_nonneg h1η.le he.le)
              (mul_le_mul_of_nonneg_left (min_le_right _ _) h1η.le)
              hL3 (le_max_right _ _)
        _ ≤ 3 * (1 - P.η₂) * |Chapter01.hessianMinEig f (x j)| / L₂ := by
            rw [abs_of_neg hlam0]
            have : e ≤ -Chapter01.hessianMinEig f (x j) := by linarith
            rw [div_div_eq_mul_div, div_le_div_iff_of_pos_right hl.pos]
            nlinarith) k le_rfl
  refine le_trans ?_ hmin
  rw [kappaDeltaTR2]
  rcases le_total (P.γ₁ * (1 - P.η₂) / M) P.Δ₀ with hle | hle
  · rw [min_eq_left hle]
    have hγ := P.γ₁_pos
    refine le_min ((mul_le_of_le_one_right (div_nonneg (mul_nonneg hγ.le h1η.le) hM.le)
      hm1).trans hle) (le_of_eq ?_)
    simp only [θ]; ring
  · rw [min_eq_right hle]
    exact le_min (mul_le_of_le_one_right P.Δ₀_pos.le hm1)
      ((mul_le_mul_of_nonneg_right hle hm.le).trans (le_of_eq (by simp only [θ]; ring)))

/-- The model decrease (3.2.22) of TR2 before termination:
`T_{f,2}(x_k, 0) - T_{f,2}(x_k, s_k) ≥ ½ min(1/(1 + κ_H), κ_Δ²) min(ε₁² ε₂, ε₂³)`. -/
theorem tr2_pred_ge (hf : AssumptionHBa f κH) (hl : AssumptionHL f L₂)
    (h : algorithm_3_2_1 f P ε₁ (some e) x s Δ) (he1 : e ≤ 1) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopTest f ε₁ (some e) (x j)) :
    1 / 2 * min (1 / (1 + κH)) (kappaDeltaTR2 P κH L₂ ^ 2) * min (ε₁ ^ 2 * e) (e ^ 3) ≤
      tr2Model f (x k) 0 - tr2Model f (x k) (s k) := by
  set κΔ := kappaDeltaTR2 P κH L₂
  set m := min ε₁ e
  set c := min (1 / (1 + κH)) (κΔ ^ 2)
  have he : 0 < e := h.ε₂_pos e rfl
  have hε₁ := h.ε₁_pos
  have hκΔ := kappaDeltaTR2_pos (P := P) (L₂ := L₂) hf.one_le
  have hκΔ1 := kappaDeltaTR2_le_one (P := P) (L₂ := L₂) hf.one_le
  have hκH := hf.nonneg
  have hΔk := lemma_3_2_5 hf hl h he1 fun j hj => hk j hj.le
  have hm : 0 < m := lt_min hε₁ he
  have hc : 0 ≤ c := le_min (div_nonneg zero_le_one (by linarith)) (by positivity)
  have hmin3 : 0 ≤ min (ε₁ ^ 2 * e) (e ^ 3) := le_min (by positivity) (by positivity)
  rcases not_stopTest_some.1 (hk k le_rfl) with hg | hlam
  · -- first-order decrease
    have hcau := h.cauchy_le_pred hk
    have hH : ‖hessianOperator f (x k)‖ ≤ κH := (hf.assumptionMHBa x).bound k
    have hmn : ε₁ * min (ε₁ / (1 + κH)) (κΔ * m) ≤
        ‖gradient f (x k)‖ * min (‖gradient f (x k)‖ / (1 + ‖hessianOperator f (x k)‖)) (Δ k) := by
      apply mul_le_mul hg.le _ (le_min (by positivity) (by positivity)) (by positivity)
      exact min_le_min (div_le_div₀ (by positivity) hg.le (by positivity) (by linarith)) hΔk
    have key : c * min (ε₁ ^ 2 * e) (e ^ 3) ≤ ε₁ * min (ε₁ / (1 + κH)) (κΔ * m) := by
      rcases le_total (ε₁ / (1 + κH)) (κΔ * m) with h1 | h1
      · rw [min_eq_left h1]
        calc c * min (ε₁ ^ 2 * e) (e ^ 3) ≤ 1 / (1 + κH) * (ε₁ ^ 2 * e) :=
              mul_le_mul (min_le_left _ _) (min_le_left _ _) hmin3 (by positivity)
          _ ≤ 1 / (1 + κH) * (ε₁ ^ 2 * 1) := by gcongr
          _ = ε₁ * (ε₁ / (1 + κH)) := by ring
      · rw [min_eq_right h1]
        have hεm : min (ε₁ ^ 2 * e) (e ^ 3) ≤ ε₁ * m := by
          rcases le_total ε₁ e with h2 | h2
          · rw [show m = ε₁ from min_eq_left h2]
            exact (min_le_left _ _).trans (by nlinarith)
          · rw [show m = e from min_eq_right h2]
            refine (min_le_right _ _).trans ?_
            nlinarith [mul_le_mul_of_nonneg_left he1 (sq_nonneg e)]
        calc c * min (ε₁ ^ 2 * e) (e ^ 3) ≤ κΔ ^ 2 * (ε₁ * m) :=
              mul_le_mul (min_le_right _ _) hεm hmin3 (by positivity)
          _ ≤ κΔ * (ε₁ * m) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              nlinarith
          _ = ε₁ * (κΔ * m) := by ring
    nlinarith
  · -- second-order decrease
    have hlam0 : Chapter01.hessianMinEig f (x k) < 0 := hlam.trans (neg_neg_of_pos he)
    have hE := (h.eigen_le_pred (Option.some_ne_none e) hk hlam0).2
    have habs : e ≤ |Chapter01.hessianMinEig f (x k)| := by
      rw [abs_of_neg hlam0]; linarith
    have hΔ2 : (κΔ * m) ^ 2 ≤ Δ k ^ 2 := pow_le_pow_left₀ (by positivity) hΔk 2
    have hem : min (ε₁ ^ 2 * e) (e ^ 3) ≤ e * m ^ 2 := by
      rcases le_total ε₁ e with h2 | h2
      · rw [show m = ε₁ from min_eq_left h2]
        exact (min_le_left _ _).trans (le_of_eq (by ring))
      · rw [show m = e from min_eq_right h2]
        exact (min_le_right _ _).trans (le_of_eq (by ring))
    calc 1 / 2 * c * min (ε₁ ^ 2 * e) (e ^ 3) ≤ 1 / 2 * κΔ ^ 2 * (e * m ^ 2) := by
          gcongr
          exact min_le_right _ _
      _ = 1 / 2 * e * (κΔ * m) ^ 2 := by ring
      _ ≤ 1 / 2 * |Chapter01.hessianMinEig f (x k)| * Δ k ^ 2 := by gcongr
      _ ≤ _ := hE

/-- The constant `κ^T_TR2 = (½ η₁ min(1/(1 + κ_H), κ_Δ²))⁻¹` of Theorem 3.2.6. -/
noncomputable def kappaTTR2 (P : Chapter02.TR1Params) (κH L₂ : ℝ) : ℝ :=
  (1 / 2 * P.η₁ * min (1 / (1 + κH)) (kappaDeltaTR2 P κH L₂ ^ 2))⁻¹

/-- The constant `κ^F_TR2 = |log(κ_Δ/Δ₀)|/|log γ₂| + 1` of Theorem 3.2.6 (**corrected**: the
proof of Theorem 3.2.6 prints `min(γ₁(1 - η₂)/(Δ₀ max(4κ_H, L_{f,2}/3)), Δ₀)/|log γ₂| + 1`,
without the `|log ·|`; with it inserted, the book's constant is an upper bound,
`kappaFTR2_le_book`). -/
noncomputable def kappaFTR2 (P : Chapter02.TR1Params) (κH L₂ : ℝ) : ℝ :=
  |Real.log (kappaDeltaTR2 P κH L₂ / P.Δ₀)| / |Real.log P.γ₂| + 1

/-- The proof's `κ^F_TR2` is at most the book's constant (with the missing `|log ·|` inserted):
`|log min(u/Δ₀, Δ₀)|/|log γ₂| + 1`, `u = γ₁(1 - η₂)/max(4κ_H, L_{f,2}/3)`. -/
theorem kappaFTR2_le_book {P : Chapter02.TR1Params} {κH L₂ : ℝ} (hκ : 1 ≤ κH) :
    kappaFTR2 P κH L₂ ≤
      |Real.log (min (P.γ₁ * (1 - P.η₂) / (P.Δ₀ * max (4 * κH) (L₂ / 3))) P.Δ₀)| /
        |Real.log P.γ₂| + 1 := by
  set a := P.γ₁ * (1 - P.η₂) / (P.Δ₀ * max (4 * κH) (L₂ / 3))
  have hΔ := P.Δ₀_pos
  have hM : 0 < max (4 * κH) (L₂ / 3) := lt_max_of_lt_left (by linarith)
  have ha : 0 < a := by
    have := P.γ₁_pos; have := sub_pos.2 P.η₂_lt_one; simp only [a]; positivity
  have hk : kappaDeltaTR2 P κH L₂ / P.Δ₀ = min a 1 := by
    rw [kappaDeltaTR2, ← min_div_div_right hΔ.le, div_self hΔ.ne']
    congr 1
    simp only [a]; field_simp
  have key : |Real.log (min a 1)| ≤ |Real.log (min a P.Δ₀)| := by
    rcases le_total 1 a with h | h
    · rw [min_eq_right h, Real.log_one, abs_zero]; exact abs_nonneg _
    · rw [min_eq_left h, abs_of_nonpos (Real.log_nonpos ha.le h),
        abs_of_nonpos (Real.log_nonpos (lt_min ha hΔ).le ((min_le_left _ _).trans h))]
      exact neg_le_neg (Real.log_le_log (lt_min ha hΔ) (min_le_left _ _))
  rw [kappaFTR2, hk]
  have := div_le_div_of_nonneg_right key (abs_nonneg (Real.log P.γ₂))
  linarith

/-- **Theorem 3.2.6** of [cartis2022evaluation] (second-order complexity of TR2). Under f.Bb,
f.HBa and f.HL, for all `ε₁ > 0` and `ε₂ = e ∈ (0, 1]`, every TR2 run terminates at an
iteration `k_ε` (an `(ε₁, ε₂)`-approximate second-order minimizer (3.2.9)) after at most
`κ^D (f(x₀) - f_low)/min(ε₁² ε₂, ε₂³) + κ^E |log min(ε₁, ε₂)| + κ^F` evaluations of `f` (3.2.20)
and at most `κ^T (f(x₀) - f_low)/min(ε₁² ε₂, ε₂³) + 1` evaluations of `∇f` and `∇²f` (3.2.21),
with `κ^T = kappaTTR2`, `κ^D = κ^T (1 + log γ₃/|log γ₂|)`, `κ^E = 1/|log γ₂|` and the corrected
`κ^F = kappaFTR2`. -/
theorem theorem_3_2_6 {flow : ℝ} (hb : Chapter02.AssumptionBb f flow)
    (hf : AssumptionHBa f κH) (hl : AssumptionHL f L₂)
    (h : algorithm_3_2_1 f P ε₁ (some e) x s Δ) (he1 : e ≤ 1) :
    ∃ kε, IsFirstHit (fun k => stopTest f ε₁ (some e) (x k)) kε ∧
      (funEvalCount kε : ℝ) ≤
        kappaTTR2 P κH L₂ * (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * (f (x 0) - flow) /
            min (ε₁ ^ 2 * e) (e ^ 3) +
          1 / |Real.log P.γ₂| * |Real.log (min ε₁ e)| + kappaFTR2 P κH L₂ ∧
      (derivEvalCount (fun k => P.η₁ ≤ tr2Ratio f (x k) (s k)) kε : ℝ) ≤
        kappaTTR2 P κH L₂ * (f (x 0) - flow) / min (ε₁ ^ 2 * e) (e ^ 3) + 1 := by
  set κΔ := kappaDeltaTR2 P κH L₂
  set m := min ε₁ e
  set Mn := min (ε₁ ^ 2 * e) (e ^ 3)
  set c := min (1 / (1 + κH)) (κΔ ^ 2)
  set succ := fun k => P.η₁ ≤ tr2Ratio f (x k) (s k)
  have he : 0 < e := h.ε₂_pos e rfl
  have hε₁ := h.ε₁_pos
  have hκΔ := kappaDeltaTR2_pos (P := P) (L₂ := L₂) hf.one_le
  have hm : 0 < m := lt_min hε₁ he
  have hMn : 0 < Mn := lt_min (by positivity) (by positivity)
  have hc : 0 < c := lt_min (div_pos one_pos (by linarith [hf.nonneg])) (by positivity)
  have hη := P.η₁_pos
  have hlog2 : 0 < |Real.log P.γ₂| := abs_pos.2 (Real.log_neg P.γ₂_pos P.γ₂_lt_one).ne
  set δ := P.η₁ * (1 / 2 * c * Mn)
  have hδ : 0 < δ := by positivity
  set N := kappaTTR2 P κH L₂ * (f (x 0) - flow) / Mn
  have hNδ : (f (x 0) - flow) / δ = N := by
    have hc' : min (1 / (1 + κH)) (kappaDeltaTR2 P κH L₂ ^ 2) = c := rfl
    simp only [N, δ, kappaTTR2, hc']
    field_simp
  have hf0 : 0 ≤ f (x 0) - flow := sub_nonneg.2 (hb (x 0))
  have hsucc : ∀ k, (∀ j ≤ k, ¬ stopTest f ε₁ (some e) (x j)) →
      ((successSet succ k).card : ℝ) ≤ N := by
    intro k hk
    rw [← hNδ]
    refine card_successSet_le_div_of_decrease (φ := fun j => f (x j)) hδ
      (fun j hj hs => by rw [h.run.eq_of_not_succ (fun i hi => hk i (hi.trans hj)) (not_le.1 hs)])
      (fun j hj hs => ?_) (hb (x (k + 1)))
    have hj' : ∀ i ≤ j, ¬ stopTest f ε₁ (some e) (x i) := fun i hi => hk i (hi.trans hj)
    have hpred := tr2_pred_ge hf hl h he1 hj'
    have hpos : 0 < tr2Model f (x j) 0 - tr2Model f (x j) (s j) :=
      lt_of_lt_of_le (by positivity) hpred
    have hsub := (h.run.sub_ge_of_succ (f := f)
      (pred := fun j => tr2Model f (x j) 0 - tr2Model f (x j) (s j)) hj' rfl hpos hs).2
    have := mul_le_mul_of_nonneg_left hpred hη.le
    change P.η₁ * (1 / 2 * min (1 / (1 + κH)) (kappaDeltaTR2 P κH L₂ ^ 2) *
      min (ε₁ ^ 2 * e) (e ^ 3)) ≤ f (x j) - f (x (j + 1))
    linarith
  have hA : 0 ≤ 1 + Real.log P.γ₃ / |Real.log P.γ₂| := by
    have := Real.log_nonneg P.one_le_γ₃; positivity
  have hN : 0 ≤ N := by
    have : 0 ≤ kappaTTR2 P κH L₂ := by unfold kappaTTR2; positivity
    positivity
  set c' := |Real.log (κΔ / P.Δ₀)|
  have hcount : ∀ k, (∀ j ≤ k, ¬ stopTest f ε₁ (some e) (x j)) →
      (k + 1 : ℝ) ≤ (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * (successSet succ k).card +
        (1 / |Real.log P.γ₂| * |Real.log m| + c' / |Real.log P.γ₂|) := by
    intro k hk
    have hΔ := lemma_3_2_5 hf hl h he1 (k := k + 1) fun j hj => hk j (Nat.lt_succ_iff.1 hj)
    have hcnt := h.run.succ_count hk (mul_pos hκΔ hm) hΔ
    have hlog : |Real.log (κΔ * m / P.Δ₀)| ≤ c' + |Real.log m| := by
      rw [show κΔ * m / P.Δ₀ = κΔ / P.Δ₀ * m by ring,
        Real.log_mul (div_pos hκΔ P.Δ₀_pos).ne' hm.ne']
      exact abs_add_le _ _
    have : |Real.log (κΔ * m / P.Δ₀)| / |Real.log P.γ₂| ≤
        1 / |Real.log P.γ₂| * |Real.log m| + c' / |Real.log P.γ₂| := by
      rw [div_le_iff₀ hlog2]
      field_simp
      linarith
    have e1 : ((successSet succ k).card : ℝ) * (1 + Real.log P.γ₃ / |Real.log P.γ₂|) =
        (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * (successSet succ k).card := mul_comm _ _
    linarith
  obtain ⟨kε, hk, hF, hD⟩ := exists_isFirstHit_evalCount_le_of_counting hA hN (by positivity)
    hcount hsucc
  refine ⟨kε, hk, ?_, hD⟩
  have : (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * N =
      kappaTTR2 P κH L₂ * (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * (f (x 0) - flow) / Mn := by
    simp only [N]; ring
  rw [kappaFTR2]
  linarith

/-! ### Theorem 3.2.7 -/

open Chapter02 (e₀ norm_e₀ inner_e₀_smul) in
/-- **Theorem 3.2.7** of [cartis2022evaluation] (slow second-order convergence of TR2). There are
`f_low`, `κ_H ≥ 1` and `L_{f,2} ≥ 1` such that for every `ε ∈ (0, 1]` there is `f : ℝ¹ → ℝ`
satisfying f.Bb, f.HBa and f.HL such that, for all TR2 constants with `Δ₀ = ε`, there is a TR2 run
with `ε₁ = ε₂ = ε` from `x₀ = 0` with `Δ_k = ε`, steps `s_k = ε` (to the trust-region boundary) and
`ρ_k = 1` (every iteration very successful), which terminates exactly at iteration
`k_ε = ⌈ε⁻³⌉`, after `k_ε + 1` evaluations of `f`, `∇f` and `∇²f`. The data are (3.2.24)–(3.2.25)
with `x_k = k ε` (the book prints `(k - 1) ε`): `g_k = 0`, `H_k = -ε (2 - k/k_ε)`. -/
theorem theorem_3_2_7 :
    ∃ flow κH L₂ : ℝ, 1 ≤ κH ∧ 1 ≤ L₂ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, Chapter02.AssumptionBb f flow ∧
        AssumptionHBa f κH ∧ AssumptionHL f L₂ ∧
        ∀ P : Chapter02.TR1Params, P.Δ₀ = ε →
          ∃ x s Δ, x 0 = 0 ∧ algorithm_3_2_1 f P ε (some ε) x s Δ ∧ (∀ k, Δ k = ε) ∧
            (∀ k < ⌈(ε ^ 3)⁻¹⌉₊, s k = ε • e₀ ∧ tr2Ratio f (x k) (s k) = 1) ∧
            IsFirstHit (fun k => stopTest f ε (some ε) (x k)) ⌈(ε ^ 3)⁻¹⌉₊ := by
  obtain ⟨L, B, -, -, H⟩ := exists_slowNegCurvature_interpolant (a := 1) (b := 1) one_pos le_rfl
  refine ⟨-B, max B 1, max L 1, le_max_right _ _, le_max_right _ _, fun ε hε hε1 => ?_⟩
  set K := ⌈(ε ^ 3)⁻¹⌉₊ with hK
  set fv : ℕ → ℝ := fun k => 1 + ∑ j ∈ range k, -ε * (2 - j / K) * (1 * ε) ^ 2 / 2
  obtain ⟨G, hG, hGL, hGB, hGk⟩ := H ε (fun _ => 1) (fun k => k * ε) fv hε hε1
    (fun _ _ => ⟨le_rfl, le_rfl⟩) (fun k _ => by push_cast; ring) (by simp [fv])
    (fun k _ => by simp only [fv, sum_range_succ]; ring)
  obtain ⟨hb, -, hHBa, hhl, hgrad⟩ := ridge_assumptions_two hG hGL hGB
  refine ⟨ridge G e₀, hb, hHBa, hhl, fun P hP => ?_⟩
  set f := ridge G e₀
  set x : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => (k * ε) • e₀
  have hK0 : (0 : ℝ) < K := by
    have : (0 : ℝ) < (ε ^ 3)⁻¹ := by positivity
    exact_mod_cast Nat.lt_ceil.2 (by simpa using this)
  have hx : ∀ k, ⟪e₀, x k⟫ = k * ε := fun k => inner_e₀_smul _
  have hg : ∀ k ≤ K, gradient f (x k) = 0 := fun k hk => by
    rw [hgrad, hx, (hGk k hk).2.1, zero_smul]
  have hlam : ∀ k ≤ K, Chapter01.hessianMinEig f (x k) = -ε * (2 - k / K) := fun k hk => by
    rw [hessianMinEig_ridge hG, hx, (hGk k hk).2.2]
  have hHop : ∀ k ≤ K, ∀ u, hessianOperator f (x k) u = (-ε * (2 - k / K)) • u :=
    fun k hk u => by rw [hessianOperator_ridge hG, hx, (hGk k hk).2.2]
  have hc : ∀ k < K, 1 < 2 - (k : ℝ) / K := fun k hk => by
    have : (k : ℝ) / K < 1 := (div_lt_one hK0).2 (by exact_mod_cast hk)
    linarith
  have htest : ∀ k ≤ K, (stopTest f ε (some ε) (x k) ↔ K ≤ k) := fun k hk => by
    rw [stopTest_some, IsApproxSecondOrderMinimizer, hg k hk, norm_zero, hlam k hk]
    constructor
    · rintro ⟨-, h2⟩
      by_contra hlt
      have := hc k (not_le.1 hlt)
      nlinarith
    · intro hKk
      have : k = K := le_antisymm hk hKk
      subst this
      refine ⟨hε.le, le_of_eq ?_⟩
      rw [div_self hK0.ne']; ring
  have hhit : IsFirstHit (fun k => stopTest f ε (some ε) (x k)) K :=
    ⟨(htest K le_rfl).2 le_rfl, fun j hj h => absurd ((htest j hj.le).1 h) (not_le.2 hj)⟩
  have hbefore : ∀ k, (∀ j ≤ k, ¬ stopTest f ε (some ε) (x j)) → k < K := fun k hk =>
    not_le.1 fun hle => hk K hle hhit.test
  have hnext : ∀ k, x k + ε • e₀ = x (k + 1) := fun k => by
    simp only [x, ← add_smul]; push_cast; ring_nf
  have hq : ∀ k ≤ K, quadModel (gradient f (x k)) (hessianOperator f (x k)) (ε • e₀) =
      ε ^ 2 / 2 * (-ε * (2 - k / K)) := fun k hk => by
    rw [quadModel_smul, hg k hk, hHop k hk, inner_zero_left, inner_smul_right,
      real_inner_self_eq_norm_sq, norm_e₀]
    ring
  have hratio : ∀ k < K, tr2Ratio f (x k) (ε • e₀) = 1 := fun k hk => by
    have hnum : f (x k) - f (x (k + 1)) = ε ^ 3 * (2 - k / K) / 2 := by
      simp only [f, ridge_apply, hx]
      rw [(hGk k hk.le).1, (hGk (k + 1) hk).1]
      simp only [fv, sum_range_succ]
      ring
    have hpos : 0 < ε ^ 3 * (2 - k / K) / 2 := by have := hc k hk; positivity
    rw [tr2Ratio_eq, hq k hk.le, reductionRatio_def, hnext, hnum,
      show -(ε ^ 2 / 2 * (-ε * (2 - (k : ℝ) / K))) = ε ^ 3 * (2 - k / K) / 2 by ring,
      div_self hpos.ne']
  have hstep : ∀ k < K, tr2Step f (some ε) (x k) ε (ε • e₀) := fun k hk => by
    have hl0 : Chapter01.hessianMinEig f (x k) < 0 := by
      rw [hlam k hk.le]; nlinarith [hc k hk]
    have hHu : hessianOperator f (x k) e₀ = Chapter01.hessianMinEig f (x k) • e₀ := by
      rw [hHop k hk.le, hlam k hk.le]
    have hgu : ⟪e₀, gradient f (x k)⟫ ≤ 0 := by rw [hg k hk.le, inner_zero_right]
    have hHu' : ⟪e₀, hessianOperator f (x k) e₀⟫ = Chapter01.hessianMinEig f (x k) := by
      rw [hHu, inner_smul_right, real_inner_self_eq_norm_sq, norm_e₀]; ring
    have hcau : IsCauchyStep (gradient f (x k)) (hessianOperator f (x k)) ε 0 := by
      rw [hg k hk.le]
      exact ⟨le_rfl, by simpa using hε.le, fun τ _ _ => by simp [quadModel_def]⟩
    refine ⟨⟨by rw [norm_smul, norm_e₀, mul_one, Real.norm_of_nonneg hε.le], 0, hcau, ?_⟩,
      fun _ => ⟨fun _ => ⟨e₀, ε, norm_e₀, hHu, hgu,
        (lemma_3_2_3 norm_e₀ hHu' hl0 hgu hε.le).1, le_rfl⟩,
      fun h0 => absurd h0 (not_le.2 hl0)⟩⟩
    rw [Chapter02.tr1Model_eq, Chapter02.tr1Model_eq, hq k hk.le, hg k hk.le, zero_smul, neg_zero,
      quadModel_zero]
    have h1 : 0 ≤ ε ^ 2 / 2 * (ε * (2 - (k : ℝ) / K)) := by have := hc k hk; positivity
    linarith [show ε ^ 2 / 2 * (-ε * (2 - (k : ℝ) / K)) = -(ε ^ 2 / 2 * (ε * (2 - (k : ℝ) / K)))
      by ring]
  refine ⟨x, fun _ => ε • e₀, fun _ => ε, by simp [x], ⟨hε, fun e he => ?_, ⟨hP.symm,
    fun k hk => hstep k (hbefore k hk), fun k hk => ?_⟩⟩, fun _ => rfl,
    fun k hk => ⟨rfl, hratio k hk⟩, hhit⟩
  · rw [Option.mem_def, Option.some_inj] at he; rw [← he]; exact hε
  · have hk' := hbefore k hk
    change TRAcceptance P.toTRParams (tr2Ratio f (x k) (ε • e₀)) (x k) (ε • e₀) (x (k + 1)) ε ε
    rw [← hnext, hratio k hk']
    exact trAcceptance_of_one_le P.toTRParams le_rfl _ _ hε.le

end Main

end CartisGouldToint.Chapter03

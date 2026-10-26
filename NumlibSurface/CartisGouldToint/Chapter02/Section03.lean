import Numlib.Optimization.Complexity.Telescoping
import Numlib.Optimization.ModelBased.QuadraticModel
import Numlib.Optimization.ModelBased.TRRun
import NumlibSurface.CartisGouldToint.Chapter02.Section02

/-!
# Cartis–Gould–Toint §2.3: The trust-region method

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §2.3: the first-order
trust-region algorithm TR1 on `ℝⁿ = EuclideanSpace ℝ (Fin n)`.

The model (2.3.1) is `m_k(s) = f(x_k) + ⟪∇f(x_k), s⟫ + ½⟪s, B_k s⟫` (`tr1Model`), with `B_k` a
self-adjoint operator on `ℝⁿ` (the book's symmetric matrix; `‖B_k‖` is the operator norm, the
spectral norm of the matrix). TR1 is an instance of the generic trust-region run
`Optimization.IsTRRun`; its Steps 3–4 are `Optimization.TRAcceptance`.

## Main definitions

* `TR1Params` — the constants (2.3.3).
* `tr1Model`, `tr1Step`, `tr1Ratio` — the model (2.3.1), the Step-2 conditions (2.3.4)–(2.3.5)
  (the Cauchy step being `Optimization.IsCauchyStep`) and the ratio (2.3.6).
* `algorithm_2_3_1 f P ε B x s Δ` — Algorithm 2.3.1 (TR1) as a run predicate;
  `exists_algorithm_2_3_1`: a run exists for every choice of self-adjoint `B_k`.
* `AssumptionMHBa B κB` — assumption m.HBa.
* `gradMin f x k = min_{i ∈ [0:k]} ‖∇f(x_i)‖`.

## Main results

Lemmas 2.3.1–2.3.6 (`lemma_2_3_1`, …, `lemma_2_3_6`), Theorem 2.3.7 (`theorem_2_3_7`, the
complexity bound with the book's constants (2.3.21)–(2.3.23)) and Theorem 2.3.8
(`theorem_2_3_8`, sharpness).

## Fixes with respect to the book

* Lemma 2.3.5 writes the model decrease as `m_k(x_k) - m_k(x_k + s_k)`; as `m_k` is a function of
  the step, the decrease is `m_k(0) - m_k(s_k)`.
* Lemma 2.3.4 is stated for every `k` up to (and including) termination, where the run is
  defined.
* Theorem 2.3.8 (discussion before it): with `B_k = 2t⁻¹` the Cauchy step would be half the
  iterate step, violating (2.3.4). The example uses `B_k = t⁻¹ I` with `t = Δ₀/2`, a constant
  radius `Δ_k = Δ₀`, and then `ρ_k = 2` (not `1`); every iteration is very successful.
-/

open Set Finset Optimization Subproblem
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter02

variable {n : ℕ}

/-- The constants of Algorithm 2.3.1 ([cartis2022evaluation], (2.3.3)): `Δ₀ > 0`,
`0 < η₁ ≤ η₂ < 1` and `0 < γ₁ ≤ γ₂ < 1 < γ₃`. -/
structure TR1Params extends Optimization.TRParams where
  /-- `γ₃ > 1`. -/
  one_lt_γ₃ : 1 < γ₃

/-- The quadratic model (2.3.1) of TR1: `m(s) = f(x) + ⟪∇f(x), s⟫ + ½⟪s, B s⟫`. -/
noncomputable def tr1Model (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  f x + ⟪gradient f x, s⟫ + 1 / 2 * ⟪s, B s⟫

section Model

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {x s : EuclideanSpace ℝ (Fin n)}
  {B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}

theorem tr1Model_eq : tr1Model f x B s = f x + quadModel (gradient f x) B s := by
  rw [tr1Model, quadModel_def]; ring

theorem tr1Model_zero_sub :
    tr1Model f x B 0 - tr1Model f x B s = -quadModel (gradient f x) B s := by
  rw [tr1Model_eq, tr1Model_eq, quadModel_zero]; ring

end Model

/-- Step 2 of Algorithm 2.3.1: `s` lies in the trust region `‖s‖ ≤ Δ` and decreases the model at
least as much as the Cauchy step `s^C = -t^C ∇f(x)` ((2.3.4)–(2.3.5)), for some Cauchy step
length `t^C` (`Optimization.IsCauchyStep`). -/
def tr1Step (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n))
    (Δ : ℝ) (s : EuclideanSpace ℝ (Fin n)) : Prop :=
  ‖s‖ ≤ Δ ∧ ∃ t, IsCauchyStep (gradient f x) B Δ t ∧
    tr1Model f x B s ≤ tr1Model f x B (-(t • gradient f x))

/-- The ratio (2.3.6): `ρ = (f(x) - f(x + s)) / (m(0) - m(s))`. -/
noncomputable def tr1Ratio (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  reductionRatio f x s (tr1Model f x B 0 - tr1Model f x B s)

/-- **Algorithm 2.3.1** (TR1) of [cartis2022evaluation], as a run predicate: iterates `x`, trial
steps `s`, radii `Δ` and model Hessians `B` (self-adjoint). It is the generic trust-region run
`Optimization.IsTRRun` with the termination test `‖∇f(x_k)‖ ≤ ε`, the Step-2 conditions
`tr1Step` and the ratio `tr1Ratio`: `Δ_0 = Δ₀` and, before termination, `‖s_k‖ ≤ Δ_k`, the Cauchy
decrease (2.3.4), `x_{k+1} = x_k + s_k` if `ρ_k ≥ η₁` and `x_k` otherwise (Step 3), and the radius
update (2.3.7) (Step 4). -/
structure algorithm_2_3_1 (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : TR1Params) (ε : ℝ)
    (B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (Δ : ℕ → ℝ) : Prop where
  /-- The accuracy level is positive. -/
  ε_pos : 0 < ε
  /-- The model Hessians are symmetric. -/
  symm : ∀ k, (B k : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric
  /-- Steps 1–4. -/
  run : IsTRRun P.toTRParams (fun k => ‖gradient f (x k)‖ ≤ ε)
    (fun k => tr1Step f (B k) (x k) (Δ k) (s k)) (fun k => tr1Ratio f (x k) (B k) (s k)) x s Δ

/-- **Existence of TR1 runs**: for all constants, `ε > 0`, every sequence of self-adjoint model
Hessians `B_k` and every starting point there is a TR1 run (the global minimizer of the model in
the trust region satisfies the Cauchy condition, `Optimization.exists_isMinOn_quadModel_ball`). -/
theorem exists_algorithm_2_3_1 (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : TR1Params) {ε : ℝ}
    (hε : 0 < ε) (B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hB : ∀ k, (B k : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∃ x s Δ, x 0 = x₀ ∧ algorithm_2_3_1 f P ε B x s Δ := by
  obtain ⟨x, s, Δ, hx0, hrun, -⟩ := exists_isTRRun P.toTRParams (Inv := fun _ => True)
    (test := fun y => ‖gradient f y‖ ≤ ε) (stepOK := fun k y Δ s => tr1Step f (B k) y Δ s)
    (fun k y _ s => tr1Ratio f y (B k) s) (fun k y Δ _ hΔ _ => by
      obtain ⟨s, hs, -, hC, -⟩ := exists_isMinOn_quadModel_ball (gradient f y) (B k) hΔ.le
      obtain ⟨t, ht⟩ := exists_isCauchyStep (gradient f y) (B k) hΔ.le
      refine ⟨s, ⟨hs, t, ht, ?_⟩, trivial⟩
      rw [tr1Model_eq, tr1Model_eq]
      linarith [hC t ht]) trivial
  exact ⟨x, s, Δ, hx0, hε, hB, hrun⟩

/-- **Assumption m.HBa** of [cartis2022evaluation]: the model Hessians are uniformly bounded,
`‖B_k‖ ≤ κ_B` for all `k`, with `κ_B ≥ 0`. -/
structure AssumptionMHBa (B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (κB : ℝ) : Prop where
  /-- `κ_B ≥ 0`. -/
  nonneg : 0 ≤ κB
  /-- `‖B_k‖ ≤ κ_B`. -/
  bound : ∀ k, ‖B k‖ ≤ κB

/-! ### The minimum gradient norm -/

/-- `min_{i ∈ [0:k]} ‖∇f(x_i)‖`. -/
noncomputable def gradMin (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (k : ℕ) : ℝ :=
  (range (k + 1)).inf' nonempty_range_add_one fun i => ‖gradient f (x i)‖

section GradMin

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : ℕ → EuclideanSpace ℝ (Fin n)} {k : ℕ}

theorem gradMin_le {i : ℕ} (hi : i ≤ k) : gradMin f x k ≤ ‖gradient f (x i)‖ :=
  inf'_le _ (mem_range.2 (Nat.lt_succ_of_le hi))

theorem le_gradMin {c : ℝ} (h : ∀ i ≤ k, c ≤ ‖gradient f (x i)‖) : c ≤ gradMin f x k :=
  le_inf' _ _ fun i hi => h i (Nat.lt_succ_iff.1 (mem_range.1 hi))

theorem gradMin_nonneg : 0 ≤ gradMin f x k :=
  le_gradMin fun _ _ => norm_nonneg _

theorem gradMin_succ_le : gradMin f x (k + 1) ≤ gradMin f x k :=
  le_gradMin fun _ hi => gradMin_le (hi.trans k.le_succ)

theorem gradMin_le_zero : gradMin f x k ≤ ‖gradient f (x 0)‖ :=
  gradMin_le (Nat.zero_le k)

end GradMin

namespace algorithm_2_3_1

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : TR1Params} {ε : ℝ}
  {B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
  {x s : ℕ → EuclideanSpace ℝ (Fin n)} {Δ : ℕ → ℝ}

/-- The radii are positive up to (and including) termination. -/
theorem delta_pos (h : algorithm_2_3_1 f P ε B x s Δ) {k : ℕ}
    (hk : ∀ j < k, ¬ ‖gradient f (x j)‖ ≤ ε) : 0 < Δ k :=
  h.run.delta_pos hk k le_rfl

end algorithm_2_3_1

/-! ### Lemmas 2.3.1–2.3.6 -/

section Lemmas

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : TR1Params} {ε L κB flow : ℝ}
  {B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
  {x s : ℕ → EuclideanSpace ℝ (Fin n)} {Δ : ℕ → ℝ}

/-- **Lemma 2.3.1** of [cartis2022evaluation] ((2.3.11)). For a TR1 run, if the method has not
terminated before iteration `k` and `Δ_k ≥ Δ_min > 0`, then
`k ≤ |𝒮_k| (1 + log γ₃ / |log γ₂|) + |log(Δ_min/Δ₀)| / |log γ₂|`, where
`𝒮_k = {j ≤ k | ρ_j ≥ η₁}`. Only the radius update (2.3.7) is used. -/
theorem lemma_2_3_1 (h : algorithm_2_3_1 f P ε B x s Δ) {k : ℕ}
    (hk : ∀ j < k, ¬ ‖gradient f (x j)‖ ≤ ε) {Δmin : ℝ} (hmin : 0 < Δmin) (hΔ : Δmin ≤ Δ k) :
    (k : ℝ) ≤ (successSet (fun j => P.η₁ ≤ tr1Ratio f (x j) (B j) (s j)) k).card *
        (1 + Real.log P.γ₃ / |Real.log P.γ₂|) +
      |Real.log (Δmin / P.Δ₀)| / |Real.log P.γ₂| :=
  h.run.le_succ_count hk hmin hΔ

/-- **Lemma 2.3.2** of [cartis2022evaluation] ((2.3.12)): for the quadratic model (2.3.1) and a
Cauchy step `s^C = -t ∇f(x)` in the trust region of radius `Δ`,
`m(0) - m(s^C) ≥ ½ ‖∇f(x)‖ min(‖∇f(x)‖/(1 + ‖B‖), Δ)`. -/
theorem lemma_2_3_2 (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) {Δ t : ℝ}
    (ht : IsCauchyStep (gradient f x) B Δ t) :
    1 / 2 * ‖gradient f x‖ * min (‖gradient f x‖ / (1 + ‖B‖)) Δ ≤
      tr1Model f x B 0 - tr1Model f x B (-(t • gradient f x)) := by
  rw [tr1Model_zero_sub]
  have := neg_quadModel_cauchy_ge ht
  linarith

/-- The model decrease of a TR1 step dominates the Cauchy decrease (2.3.12). -/
theorem algorithm_2_3_1.cauchy_le_pred (h : algorithm_2_3_1 f P ε B x s Δ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ ‖gradient f (x j)‖ ≤ ε) :
    1 / 2 * ‖gradient f (x k)‖ * min (‖gradient f (x k)‖ / (1 + ‖B k‖)) (Δ k) ≤
      tr1Model f (x k) (B k) 0 - tr1Model f (x k) (B k) (s k) := by
  obtain ⟨-, t, ht, hm⟩ := h.run.step k hk
  linarith [lemma_2_3_2 f (x k) (B k) ht]

/-- **Lemma 2.3.2**, second part: before termination the denominator of the ratio (2.3.6) is
positive, so the ratio is well defined. -/
theorem lemma_2_3_2_pred_pos (h : algorithm_2_3_1 f P ε B x s Δ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ ‖gradient f (x j)‖ ≤ ε) :
    0 < tr1Model f (x k) (B k) 0 - tr1Model f (x k) (B k) (s k) := by
  have hg : 0 < ‖gradient f (x k)‖ := h.ε_pos.trans (not_le.1 (hk k le_rfl))
  have hΔ : 0 < Δ k := h.delta_pos fun j hj => hk j hj.le
  refine lt_of_lt_of_le ?_ (h.cauchy_le_pred hk)
  have : 0 < min (‖gradient f (x k)‖ / (1 + ‖B k‖)) (Δ k) := lt_min (by positivity) hΔ
  positivity

/-- **Lemma 2.3.3** of [cartis2022evaluation]. Under f.gL and m.HBa, if the TR1 run has not
terminated at iteration `k` and `Δ_k < (1 - η₂) ‖∇f(x_k)‖ / (2(L + κ_B))` (2.3.15), then
`ρ_k ≥ η₂`, iteration `k` is successful and `Δ_{k+1} ≥ Δ_k`. -/
theorem lemma_2_3_3 (hf : AssumptionGL f L) (hB : AssumptionMHBa B κB)
    (h : algorithm_2_3_1 f P ε B x s Δ) {k : ℕ} (hk : ∀ j ≤ k, ¬ ‖gradient f (x j)‖ ≤ ε)
    (hΔk : Δ k < (1 - P.η₂) * ‖gradient f (x k)‖ / (2 * (L + κB))) :
    P.η₂ ≤ tr1Ratio f (x k) (B k) (s k) ∧ P.η₁ ≤ tr1Ratio f (x k) (B k) (s k) ∧
      Δ k ≤ Δ (k + 1) := by
  obtain ⟨hs, t, ht, hm⟩ := h.run.step k hk
  have hg : 0 < ‖gradient f (x k)‖ := h.ε_pos.trans (not_le.1 (hk k le_rfl))
  have hΔ : 0 < Δ k := h.delta_pos fun j hj => hk j hj.le
  have hsC : quadModel (gradient f (x k)) (B k) (s k) ≤
      quadModel (gradient f (x k)) (B k) (-(t • gradient f (x k))) := by
    rw [tr1Model_eq, tr1Model_eq] at hm; linarith
  have h2 : P.η₂ ≤ tr1Ratio f (x k) (B k) (s k) := by
    rw [tr1Ratio, tr1Model_zero_sub]
    exact le_reductionRatio_trust_first_of_isCauchyStep convex_univ
      (fun y _ => hf.contDiff.contDiffAt) hf.iteratedFDerivLipschitzOn hf.one_le (mem_univ _)
      (mem_univ _) (hB.bound k) ht hsC hs hΔ hg (P.η₁_pos.trans_le P.η₁_le_η₂).le hΔk
  exact ⟨h2, P.η₁_le_η₂.trans h2, (h.run.update hk).le_of_very_successful h2⟩

/-- The constant `α = (1 - η₂)/(2(L + κ_B)) min(1, Δ₀/‖∇f(x₀)‖)` of the proof of Lemma 2.3.4
(with `g₀ = ‖∇f(x₀)‖`). -/
noncomputable def tr1Alpha (P : TR1Params) (L κB g₀ : ℝ) : ℝ :=
  (1 - P.η₂) / (2 * (L + κB)) * min 1 (P.Δ₀ / g₀)

section Alpha

variable {P : TR1Params} {L κB g₀ m : ℝ}

private theorem coef_nonneg (hL : 1 ≤ L) (hκ : 0 ≤ κB) : 0 ≤ (1 - P.η₂) / (2 * (L + κB)) :=
  div_nonneg (sub_nonneg.2 P.η₂_lt_one.le) (by linarith)

private theorem coef_le_one (hL : 1 ≤ L) (hκ : 0 ≤ κB) : (1 - P.η₂) / (2 * (L + κB)) ≤ 1 := by
  rw [div_le_one (by linarith)]
  linarith [P.η₁_pos, P.η₁_le_η₂]

private theorem min_nonneg (hg₀ : 0 ≤ g₀) : 0 ≤ min 1 (P.Δ₀ / g₀) :=
  le_min zero_le_one (div_nonneg P.Δ₀_pos.le hg₀)

theorem tr1Alpha_nonneg (hL : 1 ≤ L) (hκ : 0 ≤ κB) (hg₀ : 0 ≤ g₀) : 0 ≤ tr1Alpha P L κB g₀ :=
  mul_nonneg (coef_nonneg hL hκ) (min_nonneg hg₀)

theorem tr1Alpha_pos (hL : 1 ≤ L) (hκ : 0 ≤ κB) (hg₀ : 0 < g₀) : 0 < tr1Alpha P L κB g₀ :=
  mul_pos (div_pos (sub_pos.2 P.η₂_lt_one) (by linarith))
    (lt_min zero_lt_one (div_pos P.Δ₀_pos hg₀))

/-- `α m ≤ (1 - η₂)/(2(L + κ_B)) m'` for `0 ≤ m ≤ m'`. -/
theorem tr1Alpha_mul_le (hL : 1 ≤ L) (hκ : 0 ≤ κB) (hm : 0 ≤ m) {m' : ℝ}
    (hmm' : m ≤ m') : tr1Alpha P L κB g₀ * m ≤ (1 - P.η₂) * m' / (2 * (L + κB)) := by
  rw [tr1Alpha, mul_div_right_comm]
  have h1 : min 1 (P.Δ₀ / g₀) * m ≤ m' := by
    calc min 1 (P.Δ₀ / g₀) * m ≤ 1 * m := mul_le_mul_of_nonneg_right (min_le_left _ _) hm
      _ ≤ m' := by rw [one_mul]; exact hmm'
  rw [mul_assoc]
  calc (1 - P.η₂) / (2 * (L + κB)) * (min 1 (P.Δ₀ / g₀) * m)
      ≤ (1 - P.η₂) / (2 * (L + κB)) * m' := mul_le_mul_of_nonneg_left h1 (coef_nonneg hL hκ)
    _ = (1 - P.η₂) / (2 * (L + κB)) * m' := rfl

/-- `α m ≤ Δ₀` for `0 ≤ m ≤ g₀`. -/
theorem tr1Alpha_mul_le_delta (hL : 1 ≤ L) (hκ : 0 ≤ κB) (hm : 0 ≤ m) (hmg : m ≤ g₀) :
    tr1Alpha P L κB g₀ * m ≤ P.Δ₀ := by
  have hg₀ : 0 ≤ g₀ := hm.trans hmg
  rcases hg₀.eq_or_lt with h0 | h0
  · have : m = 0 := le_antisymm (h0 ▸ hmg) hm
    rw [this, mul_zero]; exact P.Δ₀_pos.le
  have h1 : min 1 (P.Δ₀ / g₀) * m ≤ P.Δ₀ :=
    calc min 1 (P.Δ₀ / g₀) * m ≤ P.Δ₀ / g₀ * g₀ :=
          mul_le_mul (min_le_right _ _) hmg hm (div_nonneg P.Δ₀_pos.le h0.le)
      _ = P.Δ₀ := div_mul_cancel₀ _ h0.ne'
  rw [tr1Alpha, mul_assoc]
  calc (1 - P.η₂) / (2 * (L + κB)) * (min 1 (P.Δ₀ / g₀) * m) ≤ 1 * P.Δ₀ :=
        mul_le_mul (coef_le_one hL hκ) h1 (mul_nonneg (min_nonneg h0.le) hm) zero_le_one
    _ = P.Δ₀ := one_mul _

end Alpha

/-- The radius is forced to be very successful below `α min_{i≤j} ‖∇f(x_i)‖` (Lemma 2.3.3). -/
private theorem force (hf : AssumptionGL f L) (hB : AssumptionMHBa B κB)
    (h : algorithm_2_3_1 f P ε B x s Δ) {j : ℕ} (hj : ∀ i ≤ j, ¬ ‖gradient f (x i)‖ ≤ ε)
    (hΔ : Δ j < tr1Alpha P L κB ‖gradient f (x 0)‖ * gradMin f x j) :
    P.η₂ ≤ tr1Ratio f (x j) (B j) (s j) :=
  (lemma_2_3_3 hf hB h hj (hΔ.trans_le (tr1Alpha_mul_le hf.one_le hB.nonneg
    gradMin_nonneg (gradMin_le le_rfl)))).1

/-- **Lemma 2.3.4** of [cartis2022evaluation] ((2.3.17)). Under f.gL and m.HBa, for every
iteration `k` of a TR1 run up to (and including) termination,
`Δ_k ≥ γ₁ (1 - η₂)/(2(L + κ_B)) min(1, Δ₀/‖∇f(x₀)‖) min_{i ∈ [0:k]} ‖∇f(x_i)‖`
(the constant is `γ₁ tr1Alpha`). -/
theorem lemma_2_3_4 (hf : AssumptionGL f L) (hB : AssumptionMHBa B κB)
    (h : algorithm_2_3_1 f P ε B x s Δ) {k : ℕ} (hk : ∀ j < k, ¬ ‖gradient f (x j)‖ ≤ ε) :
    P.γ₁ * tr1Alpha P L κB ‖gradient f (x 0)‖ * gradMin f x k ≤ Δ k := by
  set α' := tr1Alpha P L κB ‖gradient f (x 0)‖
  have hα' : 0 ≤ α' := tr1Alpha_nonneg hf.one_le hB.nonneg (norm_nonneg _)
  have hmin := h.run.delta_ge (θ := fun j => α' * gradMin f x j) hk
    (fun j _ => mul_le_mul_of_nonneg_left gradMin_succ_le hα')
    (fun j hj hΔ => force hf hB h (fun i hi => hk i (hi.trans_lt hj)) hΔ) k le_rfl
  have hle : P.γ₁ * (α' * gradMin f x k) ≤ P.Δ₀ :=
    (mul_le_of_le_one_left (mul_nonneg hα' gradMin_nonneg) P.γ₁_le_one).trans
      (tr1Alpha_mul_le_delta hf.one_le hB.nonneg gradMin_nonneg gradMin_le_zero)
  rw [min_eq_right hle] at hmin
  rw [mul_assoc]; exact hmin

/-- **Lemma 2.3.4** for the next radius: if the TR1 run has not terminated at iteration `k`,
then `Δ_{k+1} ≥ γ₁ α min_{i ∈ [0:k]} ‖∇f(x_i)‖`. -/
theorem lemma_2_3_4_succ (hf : AssumptionGL f L) (hB : AssumptionMHBa B κB)
    (h : algorithm_2_3_1 f P ε B x s Δ) {k : ℕ} (hk : ∀ j ≤ k, ¬ ‖gradient f (x j)‖ ≤ ε) :
    P.γ₁ * tr1Alpha P L κB ‖gradient f (x 0)‖ * gradMin f x k ≤ Δ (k + 1) := by
  set α' := tr1Alpha P L κB ‖gradient f (x 0)‖
  have hα' : 0 ≤ α' := tr1Alpha_nonneg hf.one_le hB.nonneg (norm_nonneg _)
  have hk' : ∀ j < k + 1, ¬ ‖gradient f (x j)‖ ≤ ε := fun j hj => hk j (Nat.lt_succ_iff.1 hj)
  have hmin := h.run.delta_succ_ge (θ := fun j => α' * gradMin f x j) hk'
    (fun j _ => mul_le_mul_of_nonneg_left gradMin_succ_le hα')
    (fun j hj hΔ => force hf hB h (fun i hi => hk' i (hi.trans_lt hj)) hΔ) k k.lt_succ_self
  have hle : P.γ₁ * (α' * gradMin f x k) ≤ P.Δ₀ :=
    (mul_le_of_le_one_left (mul_nonneg hα' gradMin_nonneg) P.γ₁_le_one).trans
      (tr1Alpha_mul_le_delta hf.one_le hB.nonneg gradMin_nonneg gradMin_le_zero)
  rw [min_eq_right hle] at hmin
  rw [mul_assoc]; exact hmin

/-- The constant `κ_decr` of (2.3.20) (with `g₀ = ‖∇f(x₀)‖`):
`½ min(1/(1 + κ_B), γ₁ (1 - η₂)/(2(L + κ_B)) min(1, Δ₀/g₀))`. -/
noncomputable def kappaDecrTR1 (P : TR1Params) (L κB g₀ : ℝ) : ℝ :=
  1 / 2 * min (1 / (1 + κB)) (P.γ₁ * tr1Alpha P L κB g₀)

/-- **Lemma 2.3.5** of [cartis2022evaluation] ((2.3.19)–(2.3.20)). Under f.gL and m.HBa, at
every iteration `k` before termination of a TR1 run, the model decrease satisfies
`m_k(0) - m_k(s_k) ≥ κ_decr ‖∇f(x_k)‖ min_{i ∈ [0:k]} ‖∇f(x_i)‖`. (The book writes
`m_k(x_k) - m_k(x_k + s_k)`.) -/
theorem lemma_2_3_5 (hf : AssumptionGL f L) (hB : AssumptionMHBa B κB)
    (h : algorithm_2_3_1 f P ε B x s Δ) {k : ℕ} (hk : ∀ j ≤ k, ¬ ‖gradient f (x j)‖ ≤ ε) :
    kappaDecrTR1 P L κB ‖gradient f (x 0)‖ * ‖gradient f (x k)‖ * gradMin f x k ≤
      tr1Model f (x k) (B k) 0 - tr1Model f (x k) (B k) (s k) := by
  set g := ‖gradient f (x k)‖
  set m := gradMin f x k
  set c := min (1 / (1 + κB)) (P.γ₁ * tr1Alpha P L κB ‖gradient f (x 0)‖)
  have hm : 0 ≤ m := gradMin_nonneg
  have hmg : m ≤ g := gradMin_le le_rfl
  have hκ := hB.nonneg
  have h1 : m * c ≤ g / (1 + ‖B k‖) := by
    calc m * c ≤ m * (1 / (1 + κB)) := mul_le_mul_of_nonneg_left (min_le_left _ _) hm
      _ = m / (1 + κB) := by ring
      _ ≤ g / (1 + ‖B k‖) := div_le_div₀ (hm.trans hmg) hmg (by positivity)
          (by linarith [hB.bound k])
  have h2 : m * c ≤ Δ k := by
    calc m * c ≤ m * (P.γ₁ * tr1Alpha P L κB ‖gradient f (x 0)‖) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hm
      _ = P.γ₁ * tr1Alpha P L κB ‖gradient f (x 0)‖ * m := by ring
      _ ≤ Δ k := lemma_2_3_4 hf hB h fun j hj => hk j hj.le
  have h3 := h.cauchy_le_pred hk
  have h4 : 1 / 2 * g * (m * c) ≤ 1 / 2 * g * min (g / (1 + ‖B k‖)) (Δ k) :=
    mul_le_mul_of_nonneg_left (le_min h1 h2) (by positivity)
  calc kappaDecrTR1 P L κB ‖gradient f (x 0)‖ * g * m = 1 / 2 * g * (m * c) := by
        rw [kappaDecrTR1]; ring
    _ ≤ _ := h4.trans h3

/-- The constant `κ^S_TR1 = 4(L + κ_B)/(γ₁ η₁ (1 - η₂)) max(1, ‖∇f(x₀)‖/Δ₀)` of (2.3.21). -/
noncomputable def kappaSTR1 (P : TR1Params) (L κB g₀ : ℝ) : ℝ :=
  4 * (L + κB) / (P.γ₁ * P.η₁ * (1 - P.η₂)) * max 1 (g₀ / P.Δ₀)

theorem kappaSTR1_nonneg {P : TR1Params} {L κB g₀ : ℝ} (hL : 1 ≤ L) (hκ : 0 ≤ κB) :
    0 ≤ kappaSTR1 P L κB g₀ := by
  have := P.γ₁_pos; have := P.η₁_pos; have := sub_pos.2 P.η₂_lt_one
  unfold kappaSTR1
  have : 0 ≤ max 1 (g₀ / P.Δ₀) := zero_le_one.trans (le_max_left _ _)
  have : 0 ≤ L + κB := by linarith
  positivity

/-- `κ^S_TR1 = (η₁ κ_decr)⁻¹` when `‖∇f(x₀)‖ > 0` (the last step of the proof of Lemma 2.3.6). -/
theorem eta_mul_kappaDecrTR1 {P : TR1Params} {L κB g₀ : ℝ} (hL : 1 ≤ L) (hκ : 0 ≤ κB)
    (hg₀ : 0 < g₀) : P.η₁ * kappaDecrTR1 P L κB g₀ * kappaSTR1 P L κB g₀ = 1 := by
  have hγ := P.γ₁_pos; have hη := P.η₁_pos; have h1η := sub_pos.2 P.η₂_lt_one
  have hLκ : 0 < L + κB := by linarith
  have hmin : P.γ₁ * tr1Alpha P L κB g₀ ≤ 1 / (1 + κB) := by
    rw [tr1Alpha, le_div_iff₀ (by linarith)]
    have hc := coef_le_one (P := P) hL hκ
    have hm : min 1 (P.Δ₀ / g₀) ≤ 1 := min_le_left _ _
    have hm0 : 0 ≤ min 1 (P.Δ₀ / g₀) := min_nonneg hg₀.le
    have : (1 - P.η₂) / (2 * (L + κB)) * (1 + κB) ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_one (by linarith)]
      nlinarith [P.η₁_le_η₂]
    have hcn := coef_nonneg (P := P) hL hκ
    calc P.γ₁ * ((1 - P.η₂) / (2 * (L + κB)) * min 1 (P.Δ₀ / g₀)) * (1 + κB)
        = P.γ₁ * min 1 (P.Δ₀ / g₀) * ((1 - P.η₂) / (2 * (L + κB)) * (1 + κB)) := by ring
      _ ≤ 1 * 1 * 1 := by
        gcongr
        · exact P.γ₁_le_one
      _ = 1 := by norm_num
  have hmm : min 1 (P.Δ₀ / g₀) * max 1 (g₀ / P.Δ₀) = 1 := by
    have ha : 0 < P.Δ₀ / g₀ := div_pos P.Δ₀_pos hg₀
    have hinv : g₀ / P.Δ₀ = (P.Δ₀ / g₀)⁻¹ := (inv_div _ _).symm
    rw [hinv]
    rcases le_total 1 (P.Δ₀ / g₀) with h | h
    · rw [min_eq_left h, max_eq_left (inv_le_one_of_one_le₀ h), one_mul]
    · rw [min_eq_right h, max_eq_right ((one_le_inv₀ ha).2 h), mul_inv_cancel₀ ha.ne']
  rw [kappaDecrTR1, min_eq_right hmin, kappaSTR1, tr1Alpha]
  have : P.η₁ * (1 / 2 * (P.γ₁ * ((1 - P.η₂) / (2 * (L + κB)) * min 1 (P.Δ₀ / g₀)))) *
      (4 * (L + κB) / (P.γ₁ * P.η₁ * (1 - P.η₂)) * max 1 (g₀ / P.Δ₀)) =
      min 1 (P.Δ₀ / g₀) * max 1 (g₀ / P.Δ₀) := by
    field_simp
    ring
  rw [this, hmm]

/-- **Lemma 2.3.6** of [cartis2022evaluation] ((2.3.21)). Under f.Bb, f.gL and m.HBa, at every
iteration `k` before termination of a TR1 run (so `‖∇f(x_j)‖ > ε` for `j ≤ k`), the number of
successful iterations satisfies `|𝒮_k| ≤ κ^S_TR1 (f(x₀) - f_low)/ε²`. -/
theorem lemma_2_3_6 (hb : AssumptionBb f flow) (hf : AssumptionGL f L)
    (hB : AssumptionMHBa B κB) (h : algorithm_2_3_1 f P ε B x s Δ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ ‖gradient f (x j)‖ ≤ ε) :
    ((successSet (fun j => P.η₁ ≤ tr1Ratio f (x j) (B j) (s j)) k).card : ℝ) ≤
      kappaSTR1 P L κB ‖gradient f (x 0)‖ * (f (x 0) - flow) / ε ^ 2 := by
  set g₀ := ‖gradient f (x 0)‖
  have hε := h.ε_pos
  have hg₀ : 0 < g₀ := hε.trans (not_le.1 (hk 0 (Nat.zero_le k)))
  set κd := kappaDecrTR1 P L κB g₀
  have hκd : 0 ≤ κd := by
    have := tr1Alpha_nonneg (P := P) hf.one_le hB.nonneg hg₀.le
    have := hB.nonneg; have := P.γ₁_pos
    unfold κd kappaDecrTR1
    have : 0 ≤ min (1 / (1 + κB)) (P.γ₁ * tr1Alpha P L κB g₀) := le_min (by positivity)
      (by positivity)
    positivity
  have hdec : ∀ j ≤ k, P.η₁ ≤ tr1Ratio f (x j) (B j) (s j) →
      P.η₁ * κd * ε ^ 2 ≤ f (x j) - f (x (j + 1)) := by
    intro j hj hs
    have hj' : ∀ i ≤ j, ¬ ‖gradient f (x i)‖ ≤ ε := fun i hi => hk i (hi.trans hj)
    have hpred := lemma_2_3_2_pred_pos h hj'
    have hsub := (h.run.sub_ge_of_succ (f := f)
      (pred := fun j => tr1Model f (x j) (B j) 0 - tr1Model f (x j) (B j) (s j)) hj' rfl hpred
      hs).2
    have h5 := lemma_2_3_5 hf hB h hj'
    have hgj : ε ≤ ‖gradient f (x j)‖ := (not_le.1 (hj' j le_rfl)).le
    have hmj : ε ≤ gradMin f x j := le_gradMin fun i hi => (not_le.1 (hj' i hi)).le
    have : κd * ε ^ 2 ≤ κd * ‖gradient f (x j)‖ * gradMin f x j := by
      rw [mul_assoc, sq]
      exact mul_le_mul_of_nonneg_left (mul_le_mul hgj hmj hε.le (hε.le.trans hgj)) hκd
    have := mul_le_mul_of_nonneg_left (this.trans h5) P.η₁_pos.le
    linarith
  have hcard := card_successSet_mul_le_of_decrease (φ := fun j => f (x j))
    (fun j hj hs => by rw [h.run.eq_of_not_succ (fun i hi => hk i (hi.trans hj)) (not_le.1 hs)])
    hdec (hb (x (k + 1)))
  have hid := eta_mul_kappaDecrTR1 (P := P) hf.one_le hB.nonneg hg₀
  have hκS : 0 < kappaSTR1 P L κB g₀ := by
    rcases (kappaSTR1_nonneg (P := P) (g₀ := g₀) hf.one_le hB.nonneg).eq_or_lt with h0 | h0
    · rw [← h0, mul_zero] at hid; exact absurd hid zero_ne_one
    · exact h0
  rw [le_div_iff₀ (pow_pos hε 2)]
  have : P.η₁ * κd = 1 / kappaSTR1 P L κB g₀ := by
    rw [eq_div_iff hκS.ne']; exact hid
  rw [this] at hcard
  have := mul_le_mul_of_nonneg_left hcard hκS.le
  field_simp at this
  linarith

/-- The constant `κ^C_TR1` of (2.3.23) (with `g₀ = ‖∇f(x₀)‖`):
`|log(γ₁(1 - η₂)/(2Δ₀(L + κ_B)) min(1, Δ₀/g₀))| / |log γ₂| + 1`. -/
noncomputable def kappaCTR1 (P : TR1Params) (L κB g₀ : ℝ) : ℝ :=
  |Real.log (P.γ₁ * (1 - P.η₂) / (2 * P.Δ₀ * (L + κB)) * min 1 (P.Δ₀ / g₀))| /
    |Real.log P.γ₂| + 1

theorem kappaCTR1_eq (P : TR1Params) (L κB g₀ : ℝ) :
    kappaCTR1 P L κB g₀ =
      |Real.log (P.γ₁ * tr1Alpha P L κB g₀ / P.Δ₀)| / |Real.log P.γ₂| + 1 := by
  have := P.Δ₀_pos
  rw [kappaCTR1, tr1Alpha]
  congr 4
  field_simp

/-- **Theorem 2.3.7** of [cartis2022evaluation]. Under f.Bb, f.gL and m.HBa, every TR1 run
terminates at an iteration `k_ε` after at most
`κ^A (f(x₀) - f_low)/ε² + κ^B |log ε| + κ^C` evaluations of `f` and at most
`κ^S (f(x₀) - f_low)/ε² + 1` evaluations of `∇f` (one at `x₀` and one per successful
iteration), with `κ^S = kappaSTR1` (2.3.21), `κ^A = κ^S (1 + log γ₃/|log γ₂|)`,
`κ^B = 1/|log γ₂|` (2.3.22) and `κ^C = kappaCTR1` (2.3.23). -/
theorem theorem_2_3_7 (hb : AssumptionBb f flow) (hf : AssumptionGL f L)
    (hB : AssumptionMHBa B κB) (h : algorithm_2_3_1 f P ε B x s Δ) :
    ∃ kε, IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) kε ∧
      (funEvalCount kε : ℝ) ≤
        kappaSTR1 P L κB ‖gradient f (x 0)‖ * (1 + Real.log P.γ₃ / |Real.log P.γ₂|) *
            (f (x 0) - flow) / ε ^ 2 +
          1 / |Real.log P.γ₂| * |Real.log ε| + kappaCTR1 P L κB ‖gradient f (x 0)‖ ∧
      (derivEvalCount (fun k => P.η₁ ≤ tr1Ratio f (x k) (B k) (s k)) kε : ℝ) ≤
        kappaSTR1 P L κB ‖gradient f (x 0)‖ * (f (x 0) - flow) / ε ^ 2 + 1 := by
  set g₀ := ‖gradient f (x 0)‖
  set κS := kappaSTR1 P L κB g₀
  set A := 1 + Real.log P.γ₃ / |Real.log P.γ₂|
  set N := κS * (f (x 0) - flow) / ε ^ 2
  set c := |Real.log (P.γ₁ * tr1Alpha P L κB g₀ / P.Δ₀)|
  have hε := h.ε_pos
  have hlog2 : 0 < |Real.log P.γ₂| :=
    abs_pos.2 (Real.log_neg P.γ₂_pos P.γ₂_lt_one).ne
  have hA : 0 ≤ A := by
    have := Real.log_nonneg P.one_le_γ₃; positivity
  have hN : 0 ≤ N := by
    have := kappaSTR1_nonneg (P := P) (g₀ := g₀) hf.one_le hB.nonneg
    have := sub_nonneg.2 (hb (x 0)); positivity
  have hBnn : 0 ≤ 1 / |Real.log P.γ₂| * |Real.log ε| + c / |Real.log P.γ₂| := by positivity
  have hcount : ∀ k, (∀ j ≤ k, ¬ ‖gradient f (x j)‖ ≤ ε) →
      (k + 1 : ℝ) ≤ A * (successSet (fun k => P.η₁ ≤ tr1Ratio f (x k) (B k) (s k)) k).card +
        (1 / |Real.log P.γ₂| * |Real.log ε| + c / |Real.log P.γ₂|) := by
    -- the radius stays above `Δ_min = γ₁ α ε`
    intro k hk
    have hg₀ : 0 < g₀ := hε.trans (not_le.1 (hk 0 (Nat.zero_le k)))
    have hα := tr1Alpha_pos (P := P) (κB := κB) hf.one_le hB.nonneg hg₀
    have hγα : 0 < P.γ₁ * tr1Alpha P L κB g₀ := mul_pos P.γ₁_pos hα
    have hΔ : P.γ₁ * tr1Alpha P L κB g₀ * ε ≤ Δ (k + 1) :=
      (mul_le_mul_of_nonneg_left (le_gradMin fun i hi => (not_le.1 (hk i hi)).le)
        hγα.le).trans (lemma_2_3_4_succ hf hB h hk)
    have hcount := h.run.succ_count hk (mul_pos hγα hε) hΔ
    have hlog : |Real.log (P.γ₁ * tr1Alpha P L κB g₀ * ε / P.Δ₀)| ≤ c + |Real.log ε| := by
      have : P.γ₁ * tr1Alpha P L κB g₀ * ε / P.Δ₀ =
          P.γ₁ * tr1Alpha P L κB g₀ / P.Δ₀ * ε := by ring
      rw [this, Real.log_mul (div_pos hγα P.Δ₀_pos).ne' hε.ne']
      exact abs_add_le _ _
    have : |Real.log (P.γ₁ * tr1Alpha P L κB g₀ * ε / P.Δ₀)| / |Real.log P.γ₂| ≤
        1 / |Real.log P.γ₂| * |Real.log ε| + c / |Real.log P.γ₂| := by
      rw [div_le_iff₀ hlog2]
      field_simp
      linarith
    linarith
  obtain ⟨kε, hk, hF, hD⟩ := exists_isFirstHit_evalCount_le_of_counting hA hN (by positivity)
    hcount fun k hk => lemma_2_3_6 hb hf hB h hk
  refine ⟨kε, hk, ?_, hD⟩
  rw [kappaCTR1_eq]
  have : A * N = κS * A * (f (x 0) - flow) / ε ^ 2 := by ring
  linarith

end Lemmas

/-! ### Theorem 2.3.8 -/

/-- **Theorem 2.3.8** of [cartis2022evaluation] (sharpness of TR1). For all TR1 constants there
are `L ≥ 1`, `f_low` and `κ_B ≥ 0` such that for every `ε ∈ (0,1)` with `k_ε = ε⁻²` an integer
there are `f : ℝ¹ → ℝ` satisfying f.Bb and f.gL and a TR1 run from `x₀ = 0` satisfying m.HBa in
which every iteration is successful and which terminates exactly at iteration `k_ε`, after
`k_ε + 1` evaluations of `f` and of `∇f`. The run uses `B_k = t⁻¹ I` with `t = Δ₀/2` and
`Δ_k = Δ₀`; its steps are the Cauchy steps `-t∇f(x_k)` and `ρ_k = 2`. -/
theorem theorem_2_3_8 (P : TR1Params) :
    ∃ L flow κB : ℝ, 1 ≤ L ∧ 0 ≤ κB ∧ ∀ (ε : ℝ) (kε : ℕ), 0 < ε → ε < 1 →
      (kε : ℝ) * ε ^ 2 = 1 →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, AssumptionBb f flow ∧ AssumptionGL f L ∧
        ∃ (B : ℕ → EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1))
          (x s : ℕ → EuclideanSpace ℝ (Fin 1)) (Δ : ℕ → ℝ),
          x 0 = 0 ∧ AssumptionMHBa B κB ∧ algorithm_2_3_1 f P ε B x s Δ ∧
          (∀ k < kε, tr1Ratio f (x k) (B k) (s k) = 2) ∧
          IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) kε ∧
          funEvalCount kε = kε + 1 ∧
          derivEvalCount (fun k => P.η₁ ≤ tr1Ratio f (x k) (B k) (s k)) kε = kε + 1 := by
  set t := P.Δ₀ / 2
  have ht : 0 < t := half_pos P.Δ₀_pos
  obtain ⟨L, flow, hL, H⟩ := exists_slow_example ht
  refine ⟨L, flow, t⁻¹, hL, (inv_pos.2 ht).le, fun ε kε hε hε1 hkε => ?_⟩
  obtain ⟨f, hb, hgl, hfk⟩ := H ε kε hε hε1.le hkε
  set x : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => slowX t ε kε k • e₀
  set Bop : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    t⁻¹ • ContinuousLinearMap.id ℝ _
  set s : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => -(t • gradient f (x k))
  have hhit : IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) kε :=
    isFirstHit_slow hε (fun _ _ => rfl) fun k hk => (hfk k hk).2
  have hbefore : ∀ k, (∀ j ≤ k, ¬ ‖gradient f (x j)‖ ≤ ε) → k < kε := fun k hk =>
    not_le.1 fun hle => hk kε hle hhit.test
  have hBop : ∀ u, Bop u = t⁻¹ • u := fun u => rfl
  have hq : ∀ (g : EuclideanSpace ℝ (Fin 1)) (τ : ℝ),
      quadModel g Bop (-(τ • g)) = -τ * ‖g‖ ^ 2 + τ ^ 2 / (2 * t) * ‖g‖ ^ 2 := by
    intro g τ
    rw [quadModel_neg_smul, hBop, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  -- data at iteration `k < k_ε`
  have hg : ∀ k ≤ kε, ‖gradient f (x k)‖ = ε + slowOmega ε kε k := fun k hk => by
    simp only [x]
    rw [(hfk k hk).2, norm_smul, norm_e₀, mul_one, norm_neg, Real.norm_eq_abs, abs_of_nonneg]
    have : (k : ℝ) ≤ kε := by exact_mod_cast hk
    have : 0 ≤ slowOmega ε kε k := by unfold slowOmega; positivity
    linarith
  have hω : ∀ k ≤ kε, slowOmega ε kε k ≤ ε := fun k hk => by
    have hk' : (k : ℝ) ≤ kε := by exact_mod_cast hk
    have hkε0 : (0 : ℝ) < kε := by
      rcases Nat.eq_zero_or_pos kε with h0 | h0
      · rw [h0] at hkε; norm_num at hkε
      · exact_mod_cast h0
    unfold slowOmega
    rw [div_le_iff₀ hkε0]
    nlinarith
  have hstep : ∀ k < kε, x k + s k = x (k + 1) := fun k hk => by
    simp only [x, s]
    rw [(hfk k hk.le).2, slowX_succ]
    module
  have hpred : ∀ k < kε, tr1Model f (x k) Bop 0 - tr1Model f (x k) Bop (s k) =
      t / 2 * ‖gradient f (x k)‖ ^ 2 := fun k _ => by
    rw [tr1Model_zero_sub, hq]; field_simp; ring
  have hratio : ∀ k < kε, tr1Ratio f (x k) Bop (s k) = 2 := fun k hk => by
    have hgk : 0 < ‖gradient f (x k)‖ := by rw [hg k hk.le]; linarith [slowOmega_pos hε hk]
    have hfx : ∀ j ≤ kε, f (x j) = slowF t ε kε j := fun j hj => (hfk j hj).1
    rw [tr1Ratio, hpred k hk, reductionRatio_def, hstep k hk, hfx k hk.le, hfx (k + 1) hk,
      slowF_succ, ← hg k hk.le]
    field_simp
    ring
  have hrun : algorithm_2_3_1 f P ε (fun _ => Bop) x s fun _ => P.Δ₀ := by
    refine ⟨hε, fun _ u v => ?_, ⟨rfl, fun k hk => ?_, fun k hk => ?_⟩⟩
    · change ⟪Bop u, v⟫ = ⟪u, Bop v⟫
      rw [hBop, hBop, inner_smul_left, inner_smul_right]; simp
    · have hk := hbefore k hk
      have hgk : ‖gradient f (x k)‖ ≤ 2 := by
        rw [hg k hk.le]; linarith [hω k hk.le]
      have hts : t * ‖gradient f (x k)‖ ≤ P.Δ₀ := by
        have := mul_le_mul_of_nonneg_left hgk ht.le
        simp only [t] at this ⊢; linarith
      refine ⟨by simpa [s, norm_smul, abs_of_pos ht] using hts, t, ⟨ht.le, hts, fun τ _ _ => ?_⟩,
        le_rfl⟩
      rw [hq, hq]
      have : 0 ≤ (τ - t) ^ 2 / (2 * t) * ‖gradient f (x k)‖ ^ 2 := by positivity
      have e : -τ * ‖gradient f (x k)‖ ^ 2 + τ ^ 2 / (2 * t) * ‖gradient f (x k)‖ ^ 2 -
          (-t * ‖gradient f (x k)‖ ^ 2 + t ^ 2 / (2 * t) * ‖gradient f (x k)‖ ^ 2) =
          (τ - t) ^ 2 / (2 * t) * ‖gradient f (x k)‖ ^ 2 := by
        field_simp; ring
      linarith
    · have hk := hbefore k hk
      change TRAcceptance P.toTRParams (tr1Ratio f (x k) Bop (s k)) (x k) (s k) (x (k + 1))
        P.Δ₀ P.Δ₀
      rw [hratio k hk]
      have h1 : P.η₁ ≤ 2 := by linarith [P.η₁_le_η₂, P.η₂_lt_one]
      refine ⟨by rw [ite_eq_left h1, hstep k hk], fun _ => ⟨le_rfl, ?_⟩,
        fun _ h2 => absurd h2 (not_lt.2 (by linarith [P.η₂_lt_one])),
        fun h3 => absurd h3 (not_lt.2 h1)⟩
      exact le_mul_of_one_le_left P.Δ₀_pos.le P.one_le_γ₃
  refine ⟨f, hb, hgl, fun _ => Bop, x, s, fun _ => P.Δ₀, by simp [x, slowX],
    ⟨(inv_pos.2 ht).le, fun _ => ?_⟩, hrun, hratio, hhit, funEvalCount_eq kε, ?_⟩
  · calc ‖Bop‖ ≤ ‖t⁻¹‖ * ‖ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))‖ := norm_smul_le _ _
      _ ≤ t⁻¹ * 1 := by
        rw [Real.norm_of_nonneg (inv_pos.2 ht).le]
        exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le) (inv_pos.2 ht).le
      _ = t⁻¹ := mul_one _
  · classical
    rw [derivEvalCount_eq_count]
    have : Nat.count (fun k => P.η₁ ≤ tr1Ratio f (x k) Bop (s k)) kε = kε := by
      rw [Nat.count_eq_card_filter_range, filter_true_of_mem, card_range]
      intro k hk
      rw [hratio k (mem_range.1 hk)]
      linarith [P.η₁_le_η₂, P.η₂_lt_one]
    rw [this]

end CartisGouldToint.Chapter02

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Numlib.Optimization.ModelBased.TaylorModel
import Numlib.Optimization.Subproblem.Regularization
import NumlibSurface.CartisGouldToint.Chapter03.Section02

/-!
# Cartis–Gould–Toint §3.4: More algorithms with `O(ε^{-3/2})` complexity

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §3.4: the trust-region variant
TRε with a fixed quadratic regularization (Algorithm 3.4.1) and the inexact regularized Newton
framework iRN (Algorithm 3.4.2), on `ℝⁿ = EuclideanSpace ℝ (Fin n)`.

TRε is an instance of the generic trust-region run `Optimization.IsTRRun` (model (3.4.1)
`treModel`, ratio (3.4.6) `tr2Ratio`); iRN has its own run predicate (ratio (3.4.35) with
predicted decrease `‖s_k‖³`, the two-sided bounds `σᴸ_k, σᵁ_k` of Step 5). The matrices `Q_k`
with orthonormal columns of (3.4.32) are represented by their ranges `V_k`, a subspace, and
`λ_min[Q_kᵀ A Q_k]` by the least curvature of `A` restricted to `V_k` (`minCurvatureOn`).

## Main definitions

* `TREpsParams`, `treModel`, `treStep`, `algorithm_3_4_1` — Algorithm 3.4.1 (TRε);
  `exists_algorithm_3_4_1`.
* `IRNParams`, `irnGrad`, `irnStep`, `irnRatio`, `irnTest`, `irnUpdate`, `algorithm_3_4_2` —
  Algorithm 3.4.2 (iRN); `exists_algorithm_3_4_2`.
* Constants `kappaDeltaF` (3.4.15), `kappaSTREps`, `kappaATREps`, `kappaCTREps` (3.4.20)–(3.4.22),
  `sigmaUMax` (3.4.38), `irnUnsuccBound` (3.4.42), `kappaSIRN`, `kappaAIRN`, `kappaBIRN`,
  `kappaTIRN`, `kappaCIRN` (Appendix B).

## Main results

* `lemma_3_4_1` – `lemma_3_4_4`, `theorem_3_4_5`, `theorem_3_4_6` (TRε).
* `lemma_3_4_7` – `lemma_3_4_10`, `theorem_3_4_11`, `theorem_3_4_12` (iRN).
* `tre_slow_example`, `irn_slow_example` — the TRε and iRN runs on the data (3.5.12) used in
  Corollary 3.5.5.
* `card_successSet_le_two_mul_add_one` — the counting device of the corrected Theorems 3.4.6 and
  3.4.12: if every successful iteration lacking the required decrease is followed by a
  successful iteration with it, then `|𝒮_k| ≤ 2 |𝒢_k| + 1`.

## Fixes with respect to the book

* Lemma 3.4.3 (OCR l. 3658–3664): the quadratic inequality is misprinted (`½L + θ₁‖s‖²`) and the
  root is divided by `L_{f,2}` instead of `L_{f,2} + θ₁`; the stated bound (3.4.10) is proved
  directly from `½(L_{f,2} + θ₁)‖s‖² + ε_*‖s‖ ≥ ‖∇f(x_{k+1})‖` (`le_of_le_quadratic`).
* Lemma 3.4.4 (l. 3709–3721): the case labels (3.4.13)/(3.4.14) of the proof are swapped.
* Theorem 3.4.6 (l. 3823): the claim "`x_{j+1}` is on the trust-region boundary" is wrong; the
  boundary step is taken at the next successful iteration. The bounds hold with a factor `2` on
  the leading terms (and `+2` instead of `+1` for the derivative evaluations).
* Theorem 3.4.11 (App. B, l. 19055): multiplying the number of successful iterations by
  the bound (3.4.42) does not count the successful iterations themselves nor the final block of
  unsuccessful iterations; the corrected constants are `κ^A = κ^S (M + 1)`, `κ^B = 2M + 3`
  (`M` the bound (3.4.42)).
* Theorem 3.4.12 (App. B, l. 19097): "`‖∇f(x_k)‖ ≤ ε₁` for all `k ≥ k₁`" is unjustified; the
  bounds hold with a factor `2` on the leading terms (corrected constants as for 3.4.11).
* Lemma 3.4.7 uses (A.19) (`L/6 ‖s‖³`); the book's `½ L ‖s‖³` is weaker.
* Lemma 3.4.10 is stated for any block of unsuccessful iterations followed by an iteration before
  termination; a final block before termination may have one more element
  (`lemma_3_4_10_last`).
* Corollary 3.5.5 for iRN: the ratio (3.4.35) is not scale invariant; on the data (3.5.12) it is
  `4f_k³/θ_k³ > ½`, so for `η > ½` the example is rescaled (`irn_slow_example`).
-/

open Set Finset Optimization Subproblem
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter03

variable {n : ℕ}

/-! ### A counting lemma -/

/-- **Counting successes with a good successor.** Let `good j` imply `succ j` for `j ≤ K`, and
suppose that whenever a successful iteration `j` is not good, the next successful iteration
`j' ≤ K` (no success strictly between) is good. Then `|𝒮_k| ≤ 2 |𝒢_k| + 1` for every `k ≤ K`,
where `𝒢_k` are the good iterations in `[0, k]`. -/
theorem card_successSet_le_two_mul_add_one {succ good : ℕ → Prop} {K : ℕ}
    (hgood : ∀ j ≤ K, good j → succ j)
    (hnext : ∀ j j', j < j' → j' ≤ K → succ j → ¬ good j → succ j' →
      (∀ i, j < i → i < j' → ¬ succ i) → good j') :
    ∀ k ≤ K, (successSet succ k).card ≤ 2 * (successSet good k).card + 1 := by
  -- `b k`: some bad success `j ≤ k` has no success after it up to `k`
  let b : ℕ → Prop := fun k => ∃ j ≤ k, succ j ∧ ¬ good j ∧ ∀ i, j < i → i ≤ k → ¬ succ i
  have key : ∀ k ≤ K, (b k → (successSet succ k).card ≤ 2 * (successSet good k).card + 1) ∧
      (¬ b k → (successSet succ k).card ≤ 2 * (successSet good k).card) := by
    intro k
    induction k with
    | zero =>
      intro _
      by_cases hs : succ 0
      · by_cases hg : good 0
        · rw [successSet_zero_of_succ hs, successSet_zero_of_succ hg]
          simp
        · have hb : b 0 := ⟨0, le_rfl, hs, hg, fun i hi hi' => absurd hi' (by omega)⟩
          rw [successSet_zero_of_succ hs]
          exact ⟨fun _ => by simp, fun h => absurd hb h⟩
      · rw [successSet_zero_of_not_succ hs]
        simp
    | succ k ih =>
      intro hk
      obtain ⟨ih1, ih2⟩ := ih (Nat.le_of_succ_le hk)
      by_cases hs : succ (k + 1)
      · rw [card_successSet_add_one_of_succ hs]
        by_cases hg : good (k + 1)
        · rw [card_successSet_add_one_of_succ hg]
          have : (successSet succ k).card ≤ 2 * (successSet good k).card + 1 := by
            by_cases hb : b k
            · exact ih1 hb
            · exact (ih2 hb).trans (Nat.le_succ _)
          constructor <;> intro <;> omega
        · rw [card_successSet_add_one_of_not_succ hg]
          have hnb : ¬ b k := by
            rintro ⟨j, hj, hsj, hgj, hnone⟩
            exact hg (hnext j (k + 1) (by omega) hk hsj hgj hs fun i hi hi' =>
              hnone i hi (by omega))
          have := ih2 hnb
          refine ⟨fun _ => by omega, fun hb => absurd ⟨k + 1, le_rfl, hs, hg,
            fun i hi hi' => absurd hi' (by omega)⟩ hb⟩
      · rw [card_successSet_add_one_of_not_succ hs,
          card_successSet_add_one_of_not_succ fun hg => hs (hgood _ hk hg)]
        have hbb : b (k + 1) ↔ b k := by
          constructor
          · rintro ⟨j, hj, hsj, hgj, hnone⟩
            rcases Nat.lt_or_eq_of_le hj with hj | rfl
            · exact ⟨j, Nat.lt_succ_iff.1 hj, hsj, hgj, fun i hi hi' => hnone i hi (by omega)⟩
            · exact absurd hsj hs
          · rintro ⟨j, hj, hsj, hgj, hnone⟩
            refine ⟨j, hj.trans k.le_succ, hsj, hgj, fun i hi hi' => ?_⟩
            rcases Nat.lt_or_eq_of_le hi' with hi' | rfl
            · exact hnone i hi (Nat.lt_succ_iff.1 hi')
            · exact hs
        rw [hbb]
        exact ⟨ih1, ih2⟩
  intro k hk
  by_cases hb : b k
  · exact (key k hk).1 hb
  · exact ((key k hk).2 hb).trans (Nat.le_succ _)

/-- A real inequality behind Lemma 3.4.3: if `0 ≤ G ≤ a t² + ε t` with `a ≥ 0`, `ε > 0`, `t ≥ 0`,
then `t ≥ min(ε, G/ε)/√(1 + 4a)`. -/
theorem le_of_le_quadratic {a ε t G : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) (ht : 0 ≤ t) (hG : 0 ≤ G)
    (h : G ≤ a * t ^ 2 + ε * t) : 1 / √(1 + 4 * a) * min ε (G / ε) ≤ t := by
  set u := √(1 + 4 * a) with hu
  have hu2 : u ^ 2 = 1 + 4 * a := Real.sq_sqrt (by linarith)
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu1 : 1 ≤ u := by nlinarith
  have hu3 : u ≤ 1 + 3 * a := by nlinarith
  set M := min ε (G / ε)
  have hM1 : M ≤ ε := min_le_left _ _
  have hM2 : ε * M ≤ G := by
    have := min_le_right ε (G / ε)
    rw [le_div_iff₀ hε] at this
    linarith
  have hM0 : 0 ≤ M := le_min hε.le (div_nonneg hG hε.le)
  rw [one_div, ← div_eq_inv_mul, div_le_iff₀ (by linarith)]
  by_contra hlt
  push Not at hlt
  have h1 : u ^ 2 * G ≤ a * (u * t) ^ 2 + ε * u * (u * t) := by
    have := mul_le_mul_of_nonneg_left h (sq_nonneg u)
    nlinarith
  have hut : 0 ≤ u * t := mul_nonneg hu0 ht
  have h2 : a * (u * t) ^ 2 ≤ a * M ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hut (by linarith) 2) ha
  have h3 : ε * u * (u * t) < ε * u * M := mul_lt_mul_of_pos_left (by linarith) (by positivity)
  have h4 : M ^ 2 ≤ ε * M := by nlinarith
  have h5 : a * M ^ 2 + ε * u * M ≤ (a + u) * G := by nlinarith
  have h6 : (a + u) * G ≤ u ^ 2 * G := mul_le_mul_of_nonneg_right (by nlinarith) hG
  linarith

/-! ### The TRε algorithm -/

/-- The constants of Algorithm 3.4.1 (TRε): those of TR1 ((2.3.3)) and `θ₁ > 0`. (The condition
`Δ₀ > ε_*` is part of the run predicate.) -/
structure TREpsParams extends Chapter02.TR1Params where
  /-- The tolerance of the step condition (3.4.5). -/
  θ₁ : ℝ
  /-- `θ₁ > 0`. -/
  θ₁_pos : 0 < θ₁

/-- The regularized quadratic model (3.4.1) of TRε: `m(s) = T_{f,2}(x, s) + ½ ε_* ‖s‖²`. -/
noncomputable def treModel (f : EuclideanSpace ℝ (Fin n) → ℝ) (εs : ℝ)
    (x s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  tr2Model f x s + εs / 2 * ‖s‖ ^ 2

section TREpsModel

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {εs : ℝ} {x s : EuclideanSpace ℝ (Fin n)}

theorem treModel_def : treModel f εs x s = tr2Model f x s + εs / 2 * ‖s‖ ^ 2 := rfl

theorem tr2Model_zero_eq : tr2Model f x 0 = f x := by
  rw [tr2Model_eq, quadModel_zero, add_zero]

theorem treModel_zero : treModel f εs x 0 = f x := by
  rw [treModel_def, tr2Model_zero_eq, norm_zero]; ring

/-- For `f` `C²` at `x`, the model (3.4.1) is `T_{f,2}(x, s) + ½ ε_* ‖s‖²`. -/
theorem treModel_eq_taylorPolynomial (hf : ContDiffAt ℝ 2 f x) :
    treModel f εs x s = taylorPolynomial f 2 x s + εs / 2 * ‖s‖ ^ 2 := by
  rw [treModel_def, tr2Model_eq_taylorPolynomial hf]

/-- The gradient of the model (3.4.1): `∇m(s) = ∇f(x) + ∇²f(x) s + ε_* s`. -/
theorem hasFDerivAt_treModel (hf : ContDiffAt ℝ 2 f x) (s : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (treModel f εs x)
      (innerSL ℝ (gradient f x + hessianOperator f x s + εs • s)) s := by
  have hq := hasFDerivAt_quadModel (g := gradient f x) (hessianOperator_isSymmetric hf) s
  have hn := ((hasFDerivAt_id s).norm_sq).const_mul (εs / 2)
  have : treModel f εs x = fun s => f x + quadModel (gradient f x) (hessianOperator f x) s +
      εs / 2 * ‖s‖ ^ 2 := funext fun s => by rw [treModel_def, tr2Model_eq]
  rw [this]
  refine ((hq.const_add (f x)).add hn).congr_fderiv ?_
  ext v
  simp
  ring

theorem norm_fderiv_treModel (hf : ContDiffAt ℝ 2 f x) :
    ‖fderiv ℝ (treModel f εs x) s‖ = ‖gradient f x + hessianOperator f x s + εs • s‖ := by
  rw [(hasFDerivAt_treModel hf s).fderiv, innerSL_apply_norm]

/-- The quadratic Taylor model has gradient `∇f(x) + ∇²f(x) s`, so
`‖∇f(x + s)‖ ≤ L/2 ‖s‖² + ‖∇f(x) + ∇²f(x) s‖` under f.HL ((A.20) with `j = 1`, `p = 2`). -/
theorem norm_gradient_add_le {L : ℝ} (hL : AssumptionHL f L) :
    ‖gradient f (x + s)‖ ≤ L / 2 * ‖s‖ ^ 2 + ‖gradient f x + hessianOperator f x s‖ := by
  have hfx := hL.contDiffAt x
  have h := norm_fderiv_le_of_taylorPolynomial convex_univ (fun y _ => hL.contDiffAt y)
    (by norm_num : 1 ≤ 2) hL.iteratedFDerivLipschitzOn (mem_univ x) (mem_univ (x + s))
  have hT : taylorPolynomial f 2 x =
      fun s => f x + quadModel (gradient f x) (hessianOperator f x) s :=
    funext fun s => taylorPolynomial_two_eq_quadModel hfx s
  have hd : fderiv ℝ (taylorPolynomial f 2 x) s =
      innerSL ℝ (gradient f x + hessianOperator f x s) := by
    rw [hT]
    exact ((hasFDerivAt_quadModel (hessianOperator_isSymmetric hfx) s).const_add (f x)).fderiv
  rw [hd, innerSL_apply_norm, ← norm_gradient_eq] at h
  norm_num [Nat.factorial] at h
  linarith

end TREpsModel

/-- Step 2 of Algorithm 3.4.1 at an iterate `x` with radius `Δ`: `‖s‖ ≤ Δ`, `m(s) < m(0)`, the
gradient condition (3.4.5) `‖∇m(s)‖ ≤ ½ θ₁ ‖s‖²` when the step is interior (`‖s‖ < Δ`), and, if
`ε₂ < ∞` and `λ_min[∇²f(x)] < -ε₂`, a step on the boundary `‖s‖ = Δ`. -/
def treStep (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : TREpsParams) (εs : ℝ) (ε₂ : Option ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (Δ : ℝ) (s : EuclideanSpace ℝ (Fin n)) : Prop :=
  ‖s‖ ≤ Δ ∧ treModel f εs x s < treModel f εs x 0 ∧
    (‖s‖ < Δ → ‖fderiv ℝ (treModel f εs x) s‖ ≤ P.θ₁ / 2 * ‖s‖ ^ 2) ∧
    ∀ e ∈ ε₂, Chapter01.hessianMinEig f x < -e → ‖s‖ = Δ

/-- **Algorithm 3.4.1** (TRε) of [cartis2022evaluation], as a run predicate on iterates `x`, steps
`s` and radii `Δ`, with regularization weight `ε_* = εs`: `ε₁, ε_* ∈ (0, 1]`, `ε₂ ∈ (0, 1]` if
finite, `Δ₀ > ε_*`, and the generic trust-region run `Optimization.IsTRRun` with the termination
test `stopTest f ε₁ ε₂` ((3.4.3)–(3.4.4)), Step 2 `treStep` and the ratio (3.4.6)
`(f(x_k) - f(x_k + s_k)) / (f(x_k) - T_{f,2}(x_k, s_k))` (`tr2Ratio`). The book couples the
weight to the tolerances in Step 1 (`ε_* = √ε₁` if `ε₂ = ∞`, `ε_* = ε₂` otherwise); the run
predicate takes `ε_*` as a parameter and the complexity theorems impose the coupling. -/
structure algorithm_3_4_1 (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : TREpsParams) (ε₁ : ℝ)
    (ε₂ : Option ℝ) (εs : ℝ) (x s : ℕ → EuclideanSpace ℝ (Fin n)) (Δ : ℕ → ℝ) : Prop where
  /-- `ε₁ ∈ (0, 1]`. -/
  ε₁_pos : 0 < ε₁
  /-- `ε₁ ≤ 1`. -/
  ε₁_le_one : ε₁ ≤ 1
  /-- `ε₂ ∈ (0, 1]` if finite. -/
  ε₂_mem : ∀ e ∈ ε₂, 0 < e ∧ e ≤ 1
  /-- `ε_* > 0`. -/
  εs_pos : 0 < εs
  /-- `ε_* ≤ 1`. -/
  εs_le_one : εs ≤ 1
  /-- `Δ₀ > ε_*`. -/
  εs_lt_Δ₀ : εs < P.Δ₀
  /-- Steps 1–4. -/
  run : IsTRRun P.toTRParams (fun k => stopTest f ε₁ ε₂ (x k))
    (fun k => treStep f P εs ε₂ (x k) (Δ k) (s k)) (fun k => tr2Ratio f (x k) (s k)) x s Δ

/-! ### Existence of TRε runs -/

section TREpsExistence

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {εs : ℝ} {x : EuclideanSpace ℝ (Fin n)}

/-- The model (3.4.1) is the quadratic model with Hessian `∇²f(x) + ε_* I`. -/
theorem treModel_eq_quadModel (s : EuclideanSpace ℝ (Fin n)) :
    treModel f εs x s = f x + quadModel (gradient f x)
      (hessianOperator f x + εs • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
      s := by
  rw [treModel_def, tr2Model_eq, quadModel_def, quadModel_def]
  simp only [add_apply, smul_apply,
    one_apply_eq_self, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
  ring

/-- `m(s + v) + m(s - v) - 2 m(s) = ⟪v, ∇²f(x) v⟫ + ε_* ‖v‖²`. -/
theorem treModel_add_add_sub (s v : EuclideanSpace ℝ (Fin n)) :
    treModel f εs x (s + v) + treModel f εs x (s - v) - 2 * treModel f εs x s =
      ⟪v, hessianOperator f x v⟫ + εs * ‖v‖ ^ 2 := by
  simp only [treModel_def, tr2Model_eq, quadModel_def, map_add, map_sub, inner_add_left,
    inner_add_right, inner_sub_left, inner_sub_right, norm_add_sq_real, norm_sub_sq_real]
  ring

/-- **A TRε step exists** at every iterate where the test fails, when `f` is `C²` at `x`, `Δ > 0`
and `ε_* ≤ ε₂` (the book's coupling): the global minimizer of the model (3.4.1) in the trust
region is admissible (Step 2 of Algorithm 3.4.1). -/
theorem exists_treStep (hf : ContDiffAt ℝ 2 f x) (P : TREpsParams) {ε₁ : ℝ} {ε₂ : Option ℝ}
    {Δ : ℝ} (hε₁ : 0 ≤ ε₁) (hεs : 0 < εs) (hε₂ : ∀ e ∈ ε₂, εs ≤ e) (hΔ : 0 < Δ)
    (hnot : ¬ stopTest f ε₁ ε₂ x) : ∃ s, treStep f P εs ε₂ x Δ s := by
  set H' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    hessianOperator f x + εs • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
  set g := gradient f x
  have hm : treModel f εs x = fun s => f x + quadModel g H' s :=
    funext fun s => treModel_eq_quadModel s
  obtain ⟨s, hsΔ, hmin, hC, -⟩ := exists_isMinOn_quadModel_ball g H' hΔ.le
  have hneg : ∀ e ∈ ε₂, Chapter01.hessianMinEig f x < -e → ∃ u, ‖u‖ = 1 ∧
      ⟪u, hessianOperator f x u⟫ + εs < 0 ∧ ⟪u, g⟫ ≤ 0 := by
    intro e he hlam
    obtain ⟨u, hu, hHu, hgu⟩ := exists_eigenvector_hessianMinEig hf
      (hlam.trans_le (by linarith [hεs.le.trans (hε₂ e he)]))
    refine ⟨u, hu, ?_, hgu⟩
    rw [hHu, inner_smul_right, real_inner_self_eq_norm_sq, hu]
    linarith [hε₂ e he]
  have hq : ∀ u, ‖u‖ = 1 → quadModel g H' (Δ • u) =
      Δ * ⟪u, g⟫ + Δ ^ 2 / 2 * (⟪u, hessianOperator f x u⟫ + εs) := fun u hu => by
    rw [quadModel_smul, real_inner_comm]
    simp only [H', add_apply, smul_apply,
      one_apply_eq_self, inner_add_right, inner_smul_right,
      real_inner_self_eq_norm_sq, hu]
    ring
  refine ⟨s, hsΔ, ?_, fun hint => ?_, fun e he hlam => ?_⟩
  · rw [hm]
    simp only [quadModel_zero, add_zero, add_lt_iff_neg_left]
    rcases not_and_or.1 hnot with hg | hl
    · have hg : 0 < ‖g‖ := lt_of_le_of_lt hε₁ (not_le.1 hg)
      obtain ⟨t, ht⟩ := exists_isCauchyStep g H' hΔ.le
      have := neg_quadModel_cauchy_ge ht
      have hpos : 0 < ‖g‖ / 2 * min (‖g‖ / (1 + ‖H'‖)) Δ := by
        have : 0 < min (‖g‖ / (1 + ‖H'‖)) Δ := lt_min (by positivity) hΔ
        positivity
      linarith [hC t ht]
    · push Not at hl
      obtain ⟨e, he, hlam⟩ := hl
      obtain ⟨u, hu, hc, hgu⟩ := hneg e he hlam
      have h1 := hmin (show Δ • u ∈ Metric.closedBall 0 Δ by
        rw [Metric.mem_closedBall, dist_zero_right, norm_smul, hu, Real.norm_of_nonneg hΔ.le,
          mul_one])
      simp only [mem_ofPred_eq] at h1
      rw [hq u hu] at h1
      have : Δ * ⟪u, g⟫ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hΔ.le hgu
      have : Δ ^ 2 / 2 * (⟪u, hessianOperator f x u⟫ + εs) < 0 :=
        mul_neg_of_pos_of_neg (by positivity) hc
      linarith
  · have hball : s ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) Δ := by
      rwa [Metric.mem_ball, dist_zero_right]
    have hloc : IsLocalMin (treModel f εs x) s := by
      rw [hm]
      have hl : IsLocalMin (quadModel g H') s := hmin.isLocalMin
        (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hball) Metric.ball_subset_closedBall)
      exact isLocalMin_const.add hl
    rw [hloc.fderiv_eq_zero, norm_zero]
    exact mul_nonneg (by linarith [P.θ₁_pos]) (sq_nonneg _)
  · by_contra hne
    have hlt : ‖s‖ < Δ := lt_of_le_of_ne hsΔ hne
    obtain ⟨u, hu, hc, -⟩ := hneg e he hlam
    set t := Δ - ‖s‖
    have ht : 0 < t := sub_pos.2 hlt
    have hmem : ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ ≤ t → s + v ∈ Metric.closedBall 0 Δ ∧
        s - v ∈ Metric.closedBall 0 Δ := fun v hv => by
      simp only [Metric.mem_closedBall, dist_zero_right]
      constructor
      · linarith [norm_add_le s v]
      · linarith [norm_sub_le s v]
    have hv : ‖t • u‖ ≤ t := by rw [norm_smul, hu, Real.norm_of_nonneg ht.le, mul_one]
    obtain ⟨h1, h2⟩ := hmem _ hv
    have e1 := hmin h1
    have e2 := hmin h2
    simp only [mem_ofPred_eq] at e1 e2
    have hid := treModel_add_add_sub (f := f) (εs := εs) (x := x) s (t • u)
    rw [hm] at hid
    simp only at hid
    have : ⟪t • u, hessianOperator f x (t • u)⟫ + εs * ‖t • u‖ ^ 2 =
        t ^ 2 * (⟪u, hessianOperator f x u⟫ + εs) := by
      rw [map_smul, inner_smul_left, inner_smul_right, norm_smul, hu, Real.norm_of_nonneg ht.le]
      simp only [conj_trivial]
      ring
    have hneg' : t ^ 2 * (⟪u, hessianOperator f x u⟫ + εs) < 0 :=
      mul_neg_of_pos_of_neg (by positivity) hc
    linarith

/-- **Existence of TRε runs** ([cartis2022evaluation], Algorithm 3.4.1): for `C²` `f`, admissible
tolerances (`ε₁, ε_* ∈ (0, 1]`, `ε₂ ∈ (0, 1]` if finite, `ε_* < Δ₀`) with `ε_* ≤ ε₂` (the book's
coupling `ε_* = ε₂`), and every starting point, a TRε run exists. -/
theorem exists_algorithm_3_4_1 (hf : ContDiff ℝ 2 f) (P : TREpsParams) {ε₁ : ℝ}
    {ε₂ : Option ℝ} (hε₁ : 0 < ε₁) (hε₁1 : ε₁ ≤ 1) (hε₂ : ∀ e ∈ ε₂, 0 < e ∧ e ≤ 1)
    (hεs : 0 < εs) (hεs1 : εs ≤ 1) (hΔ₀ : εs < P.Δ₀) (hεs₂ : ∀ e ∈ ε₂, εs ≤ e)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∃ x s Δ, x 0 = x₀ ∧ algorithm_3_4_1 f P ε₁ ε₂ εs x s Δ := by
  obtain ⟨x, s, Δ, hx0, hrun, -⟩ := exists_isTRRun P.toTRParams (Inv := fun _ => True)
    (test := fun y => stopTest f ε₁ ε₂ y) (stepOK := fun _ y Δ s => treStep f P εs ε₂ y Δ s)
    (fun _ y _ s => tr2Ratio f y s) (fun _ y Δ _ hΔ hnot => by
      obtain ⟨s, hs⟩ := exists_treStep hf.contDiffAt P hε₁.le hεs hεs₂ hΔ hnot
      exact ⟨s, hs, trivial⟩) trivial
  exact ⟨x, s, Δ, hx0, hε₁, hε₁1, hε₂, hεs, hεs1, hΔ₀, hrun⟩

end TREpsExistence

/-! ### Lemmas 3.4.1–3.4.4 -/

section TREpsLemmas

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : TREpsParams} {ε₁ : ℝ} {ε₂ : Option ℝ}
  {εs : ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)} {Δ : ℕ → ℝ} {L : ℝ}

/-- **Lemma 3.4.1** of [cartis2022evaluation] ((3.4.7)). At every iteration `k` before
termination of a TRε run, `T_{f,2}(x_k, 0) - T_{f,2}(x_k, s_k) ≥ ½ ε_* ‖s_k‖²` (in fact `>`). -/
theorem lemma_3_4_1 (h : algorithm_3_4_1 f P ε₁ ε₂ εs x s Δ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopTest f ε₁ ε₂ (x j)) :
    εs / 2 * ‖s k‖ ^ 2 < tr2Model f (x k) 0 - tr2Model f (x k) (s k) := by
  obtain ⟨-, hm, -, -⟩ := h.run.step k hk
  rw [treModel_def, treModel_def, norm_zero] at hm
  linarith

namespace algorithm_3_4_1

/-- The predicted decrease of TRε is positive before termination. -/
theorem pred_pos (h : algorithm_3_4_1 f P ε₁ ε₂ εs x s Δ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopTest f ε₁ ε₂ (x j)) :
    0 < -quadModel (gradient f (x k)) (hessianOperator f (x k)) (s k) := by
  rw [← tr2Model_zero_sub]
  exact lt_of_le_of_lt (by have := h.εs_pos; positivity) (lemma_3_4_1 h hk)

/-- The decrease on successful iterations: `f(x_k) - f(x_{k+1}) ≥ η₁ (T(0) - T(s_k))`. -/
theorem sub_ge (h : algorithm_3_4_1 f P ε₁ ε₂ εs x s Δ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopTest f ε₁ ε₂ (x j)) (hs : P.η₁ ≤ tr2Ratio f (x k) (s k)) :
    x (k + 1) = x k + s k ∧
      P.η₁ * (tr2Model f (x k) 0 - tr2Model f (x k) (s k)) ≤ f (x k) - f (x (k + 1)) := by
  rw [tr2Model_zero_sub]
  exact h.run.sub_ge_of_succ (f := f)
    (pred := fun k => -quadModel (gradient f (x k)) (hessianOperator f (x k)) (s k)) hk
    (tr2Ratio_eq _ _ _) (h.pred_pos hk) hs

/-- The objective does not increase before termination. -/
theorem le (h : algorithm_3_4_1 f P ε₁ ε₂ εs x s Δ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopTest f ε₁ ε₂ (x j)) : f (x (k + 1)) ≤ f (x k) :=
  (h.run.accept k hk).le (tr2Ratio_eq _ _ _) (h.pred_pos hk)

end algorithm_3_4_1

/-- **Lemma 3.4.2** of [cartis2022evaluation], first part. Under f.HL, if `k` is before
termination of a TRε run and `Δ_k < 3(1 - η₂) ε_* / L_{f,2}` (3.4.8), then `ρ_k ≥ η₂`, iteration
`k` is successful and `Δ_{k+1} ≥ Δ_k`. -/
theorem lemma_3_4_2 (hf : AssumptionHL f L) (h : algorithm_3_4_1 f P ε₁ ε₂ εs x s Δ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopTest f ε₁ ε₂ (x j)) (hΔk : Δ k < 3 * (1 - P.η₂) * εs / L) :
    P.η₂ ≤ tr2Ratio f (x k) (s k) ∧ P.η₁ ≤ tr2Ratio f (x k) (s k) ∧ Δ k ≤ Δ (k + 1) := by
  obtain ⟨hsΔ, -, -, -⟩ := h.run.step k hk
  have hεs := h.εs_pos
  have hL := hf.pos
  set pred := -quadModel (gradient f (x k)) (hessianOperator f (x k)) (s k)
  have hpred : εs / 2 * ‖s k‖ ^ 2 < pred := by
    have := lemma_3_4_1 h hk; rwa [tr2Model_zero_sub] at this
  have hpos : 0 < pred := h.pred_pos hk
  have habs : |f (x k + s k) - (f (x k) - pred)| ≤ L / 6 * ‖s k‖ ^ 3 := by
    have h1 := abs_sub_taylorPolynomial_le_of_lipschitz convex_univ (fun y _ => hf.contDiffAt y)
      hf.iteratedFDerivLipschitzOn (mem_univ (x k)) (mem_univ (x k + s k))
    have h2 : f (x k) - pred = taylorPolynomial f 2 (x k) (s k) := by
      rw [← tr2Model_eq_taylorPolynomial (hf.contDiffAt _), tr2Model_eq]; ring
    rw [h2]
    norm_num [Nat.factorial] at h1
    linarith
  set c := L * Δ k / (3 * εs)
  have hc : c < 1 - P.η₂ := by
    rw [lt_div_iff₀ hL] at hΔk
    rw [div_lt_iff₀ (by positivity)]
    linarith
  have hcp : L / 6 * ‖s k‖ ^ 3 ≤ c * pred := by
    have hΔ0 : 0 ≤ Δ k := (norm_nonneg _).trans hsΔ
    have : L / 6 * ‖s k‖ ^ 3 ≤ c * (εs / 2 * ‖s k‖ ^ 2) := by
      have e : c * (εs / 2 * ‖s k‖ ^ 2) = L / 6 * (Δ k * ‖s k‖ ^ 2) := by
        simp only [c]; field_simp; ring
      rw [e]
      have : ‖s k‖ ^ 3 ≤ Δ k * ‖s k‖ ^ 2 := by
        rw [pow_succ']; exact mul_le_mul_of_nonneg_right hsΔ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have hc0 : 0 ≤ c := by positivity
    nlinarith
  have hρ := le_reductionRatio_of_abs_sub_le hpos (habs.trans hcp)
  have h2 : P.η₂ ≤ tr2Ratio f (x k) (s k) := by rw [tr2Ratio_eq]; linarith
  exact ⟨h2, P.η₁_le_η₂.trans h2, (h.run.update hk).le_of_very_successful h2⟩

/-- The radius forcing threshold of Lemma 3.4.2 dominates the lower bound (3.4.9). -/
private theorem tre_min_ge (hL : 1 ≤ L) (hεs : 0 < εs) (hΔ₀ : εs < P.Δ₀) :
    (1 - P.η₂) * P.γ₁ * εs / L ≤ min P.Δ₀ (P.γ₁ * (3 * (1 - P.η₂) * εs / L)) := by
  have h1η : 0 < 1 - P.η₂ := sub_pos.2 P.η₂_lt_one
  have hγ := P.γ₁_pos
  have hL0 : 0 < L := by linarith
  refine le_min ?_ ?_
  · have : (1 - P.η₂) * P.γ₁ / L ≤ 1 := by
      rw [div_le_one hL0]
      nlinarith [P.γ₁_le_one, P.η₁_pos, P.η₁_le_η₂]
    calc (1 - P.η₂) * P.γ₁ * εs / L = (1 - P.η₂) * P.γ₁ / L * εs := by ring
      _ ≤ 1 * εs := mul_le_mul_of_nonneg_right this hεs.le
      _ ≤ P.Δ₀ := by linarith
  · rw [mul_div_assoc', div_le_div_iff_of_pos_right hL0]
    nlinarith [mul_pos h1η hγ]

/-- **Lemma 3.4.2** of [cartis2022evaluation], second part ((3.4.9)). Under f.HL, for every `k` up
to (and including) termination of a TRε run, `Δ_k ≥ (1 - η₂) γ₁ ε_* / L_{f,2}`. -/
theorem lemma_3_4_2_delta (hf : AssumptionHL f L) (h : algorithm_3_4_1 f P ε₁ ε₂ εs x s Δ)
    {k : ℕ} (hk : ∀ j < k, ¬ stopTest f ε₁ ε₂ (x j)) :
    (1 - P.η₂) * P.γ₁ * εs / L ≤ Δ k :=
  (tre_min_ge hf.one_le h.εs_pos h.εs_lt_Δ₀).trans (h.run.delta_ge
    (θ := fun _ => 3 * (1 - P.η₂) * εs / L) hk (fun _ _ => le_rfl)
    (fun _ hj hΔ => (lemma_3_4_2 hf h (fun i hi => hk i (hi.trans_lt hj)) hΔ).1) k le_rfl)

/-- (3.4.9) for the next radius: if the TRε run has not terminated at `k`, then
`Δ_{k+1} ≥ (1 - η₂) γ₁ ε_* / L_{f,2}`. -/
theorem lemma_3_4_2_delta_succ (hf : AssumptionHL f L) (h : algorithm_3_4_1 f P ε₁ ε₂ εs x s Δ)
    {k : ℕ} (hk : ∀ j ≤ k, ¬ stopTest f ε₁ ε₂ (x j)) :
    (1 - P.η₂) * P.γ₁ * εs / L ≤ Δ (k + 1) := by
  have hk' : ∀ j < k + 1, ¬ stopTest f ε₁ ε₂ (x j) := fun j hj => hk j (Nat.lt_succ_iff.1 hj)
  exact (tre_min_ge hf.one_le h.εs_pos h.εs_lt_Δ₀).trans (h.run.delta_succ_ge
    (θ := fun _ => 3 * (1 - P.η₂) * εs / L) hk' (fun _ _ => le_rfl)
    (fun j hj hΔ => (lemma_3_4_2 hf h (fun i hi => hk' i (hi.trans_lt hj)) hΔ).1) k
    k.lt_succ_self)

/-- **Lemma 3.4.3** of [cartis2022evaluation] ((3.4.10)). Under f.HL, if iteration `k` of a TRε
run (before termination) is successful and the step is interior (`‖s_k‖ < Δ_k`), then
`‖s_k‖ ≥ min(ε_*, ‖∇f(x_{k+1})‖/ε_*)/√(1 + 2(L_{f,2} + θ₁))`. (The printed derivation
(3.4.11)–(3.4.12) has algebraic misprints; the quadratic inequality is
`½(L_{f,2} + θ₁)‖s‖² + ε_*‖s‖ ≥ ‖∇f(x_{k+1})‖`.) -/
theorem lemma_3_4_3 (hf : AssumptionHL f L) (h : algorithm_3_4_1 f P ε₁ ε₂ εs x s Δ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopTest f ε₁ ε₂ (x j)) (hs : P.η₁ ≤ tr2Ratio f (x k) (s k))
    (hint : ‖s k‖ < Δ k) :
    1 / √(1 + 2 * (L + P.θ₁)) * min εs (‖gradient f (x (k + 1))‖ / εs) ≤ ‖s k‖ := by
  obtain ⟨-, -, hgrad, -⟩ := h.run.step k hk
  have hxk := (h.sub_ge hk hs).1
  have hfx := hf.contDiffAt (x k)
  have h1 := norm_gradient_add_le hf (x := x k) (s := s k)
  have h2 := hgrad hint
  rw [norm_fderiv_treModel hfx] at h2
  have h3 : ‖gradient f (x k) + hessianOperator f (x k) (s k)‖ ≤
      ‖gradient f (x k) + hessianOperator f (x k) (s k) + εs • s k‖ + εs * ‖s k‖ := by
    have := norm_sub_le (gradient f (x k) + hessianOperator f (x k) (s k) + εs • s k) (εs • s k)
    rw [add_sub_cancel_right, norm_smul, Real.norm_of_nonneg h.εs_pos.le] at this
    exact this
  rw [hxk]
  have := le_of_le_quadratic (a := (L + P.θ₁) / 2) (by linarith [hf.nonneg, P.θ₁_pos])
    h.εs_pos (norm_nonneg (s k)) (norm_nonneg (gradient f (x k + s k))) (by linarith)
  rwa [show 1 + 4 * ((L + P.θ₁) / 2) = 1 + 2 * (L + P.θ₁) by ring] at this

/-- The constant `κ_Δf = ½ η₁ min(γ₁²(1 - η₂)²/L², 1/(1 + 2(L + θ₁)))` of (3.4.15). -/
noncomputable def kappaDeltaF (P : TREpsParams) (L : ℝ) : ℝ :=
  P.η₁ / 2 * min (P.γ₁ ^ 2 * (1 - P.η₂) ^ 2 / L ^ 2) (1 / (1 + 2 * (L + P.θ₁)))

theorem kappaDeltaF_pos (P : TREpsParams) {L : ℝ} (hL : 0 < L) : 0 < kappaDeltaF P L := by
  have := P.η₁_pos; have := P.γ₁_pos; have := sub_pos.2 P.η₂_lt_one; have := P.θ₁_pos
  unfold kappaDeltaF
  have : 0 < min (P.γ₁ ^ 2 * (1 - P.η₂) ^ 2 / L ^ 2) (1 / (1 + 2 * (L + P.θ₁))) :=
    lt_min (by positivity) (by positivity)
  positivity

private theorem mul_min_sq {εs G : ℝ} (hεs : 0 < εs) (hG : 0 ≤ G) :
    εs * min εs (G / εs) ^ 2 = min (εs ^ 3) (G ^ 2 / εs) := by
  have h0 : 0 ≤ G / εs := div_nonneg hG hεs.le
  rcases le_total εs (G / εs) with hle | hle
  · rw [min_eq_left hle, min_eq_left]
    · ring
    · rw [le_div_iff₀ hεs]
      have := pow_le_pow_left₀ hεs.le hle 2
      rw [div_pow, le_div_iff₀ (by positivity)] at this
      nlinarith
  · rw [min_eq_right hle, min_eq_right]
    · field_simp
    · rw [div_le_iff₀ hεs]
      have := pow_le_pow_left₀ h0 hle 2
      rw [div_pow, div_le_iff₀ (by positivity)] at this
      nlinarith

/-- **Lemma 3.4.4** of [cartis2022evaluation]. Under f.HL, on every successful iteration `k`
(before termination) of a TRε run, `f(x_k) - f(x_{k+1}) ≥ κ_Δf min(ε_*³, ‖∇f(x_{k+1})‖²/ε_*)`
if the step is interior (3.4.13), and `≥ κ_Δf ε_*³` if it is on the boundary (3.4.14). (The
proof's case labels "(3.4.13)"/"(3.4.14)" are swapped in the book.) -/
theorem lemma_3_4_4 (hf : AssumptionHL f L) (h : algorithm_3_4_1 f P ε₁ ε₂ εs x s Δ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopTest f ε₁ ε₂ (x j)) (hs : P.η₁ ≤ tr2Ratio f (x k) (s k)) :
    (‖s k‖ < Δ k → kappaDeltaF P L * min (εs ^ 3) (‖gradient f (x (k + 1))‖ ^ 2 / εs) ≤
      f (x k) - f (x (k + 1))) ∧
    (‖s k‖ = Δ k → kappaDeltaF P L * εs ^ 3 ≤ f (x k) - f (x (k + 1))) := by
  have hεs := h.εs_pos
  have hL := hf.pos
  have hdec := (h.sub_ge hk hs).2
  have hpred := lemma_3_4_1 h hk
  have hη := P.η₁_pos
  have hmin1 : min (P.γ₁ ^ 2 * (1 - P.η₂) ^ 2 / L ^ 2) (1 / (1 + 2 * (L + P.θ₁))) ≤
      P.γ₁ ^ 2 * (1 - P.η₂) ^ 2 / L ^ 2 := min_le_left _ _
  have hmin2 : min (P.γ₁ ^ 2 * (1 - P.η₂) ^ 2 / L ^ 2) (1 / (1 + 2 * (L + P.θ₁))) ≤
      1 / (1 + 2 * (L + P.θ₁)) := min_le_right _ _
  have hθ : 0 < 1 + 2 * (L + P.θ₁) := by linarith [P.θ₁_pos]
  constructor
  · intro hint
    set G := ‖gradient f (x (k + 1))‖
    set M := min εs (G / εs)
    have h3 := lemma_3_4_3 hf h hk hs hint
    have hM0 : 0 ≤ M := le_min hεs.le (div_nonneg (norm_nonneg _) hεs.le)
    have hsq : M ^ 2 / (1 + 2 * (L + P.θ₁)) ≤ ‖s k‖ ^ 2 := by
      have h4 := pow_le_pow_left₀ (by positivity) h3 2
      rw [mul_pow, div_pow, one_pow, Real.sq_sqrt hθ.le] at h4
      calc M ^ 2 / (1 + 2 * (L + P.θ₁)) = 1 / (1 + 2 * (L + P.θ₁)) * M ^ 2 := by ring
        _ ≤ _ := h4
    rw [← mul_min_sq hεs (norm_nonneg _)]
    unfold kappaDeltaF
    have : P.η₁ / 2 * min (P.γ₁ ^ 2 * (1 - P.η₂) ^ 2 / L ^ 2) (1 / (1 + 2 * (L + P.θ₁))) *
        (εs * M ^ 2) ≤ P.η₁ * (εs / 2 * (M ^ 2 / (1 + 2 * (L + P.θ₁)))) := by
      have hM2 : 0 ≤ εs * M ^ 2 := by positivity
      calc P.η₁ / 2 * min (P.γ₁ ^ 2 * (1 - P.η₂) ^ 2 / L ^ 2) (1 / (1 + 2 * (L + P.θ₁))) *
            (εs * M ^ 2) ≤ P.η₁ / 2 * (1 / (1 + 2 * (L + P.θ₁))) * (εs * M ^ 2) := by gcongr
        _ = P.η₁ * (εs / 2 * (M ^ 2 / (1 + 2 * (L + P.θ₁)))) := by ring
    have h5 : P.η₁ * (εs / 2 * (M ^ 2 / (1 + 2 * (L + P.θ₁)))) ≤
        P.η₁ * (εs / 2 * ‖s k‖ ^ 2) := by gcongr
    nlinarith
  · intro hbd
    have hΔ := lemma_3_4_2_delta hf h (k := k) fun j hj => hk j hj.le
    rw [← hbd] at hΔ
    have hc0 : 0 ≤ (1 - P.η₂) * P.γ₁ * εs / L := by
      have := sub_pos.2 P.η₂_lt_one; have := P.γ₁_pos; positivity
    have h4 := pow_le_pow_left₀ hc0 hΔ 2
    unfold kappaDeltaF
    have e : P.η₁ / 2 * (P.γ₁ ^ 2 * (1 - P.η₂) ^ 2 / L ^ 2) * εs ^ 3 =
        P.η₁ * (εs / 2 * ((1 - P.η₂) * P.γ₁ * εs / L) ^ 2) := by
      field_simp
    calc P.η₁ / 2 * min (P.γ₁ ^ 2 * (1 - P.η₂) ^ 2 / L ^ 2) (1 / (1 + 2 * (L + P.θ₁))) *
          εs ^ 3 ≤ P.η₁ / 2 * (P.γ₁ ^ 2 * (1 - P.η₂) ^ 2 / L ^ 2) * εs ^ 3 := by gcongr
      _ = P.η₁ * (εs / 2 * ((1 - P.η₂) * P.γ₁ * εs / L) ^ 2) := e
      _ ≤ P.η₁ * (εs / 2 * ‖s k‖ ^ 2) := by gcongr
      _ ≤ _ := by nlinarith

end TREpsLemmas

/-! ### Theorems 3.4.5 and 3.4.6 -/

/-- The constant `κ^S_TRε = κ_Δf⁻¹` of (3.4.20). -/
noncomputable def kappaSTREps (P : TREpsParams) (L : ℝ) : ℝ := (kappaDeltaF P L)⁻¹

/-- The constant `κ^A_TRε = κ^S_TRε (1 + log γ₃/|log γ₂|)` of (3.4.21). -/
noncomputable def kappaATREps (P : TREpsParams) (L : ℝ) : ℝ :=
  kappaSTREps P L * (1 + Real.log P.γ₃ / |Real.log P.γ₂|)

/-- The constant `κ^C_TRε = (log γ₃ + |log((1 - η₂) γ₁/(Δ₀ L))|)/|log γ₂| + 2` of (3.4.22). -/
noncomputable def kappaCTREps (P : TREpsParams) (L : ℝ) : ℝ :=
  (Real.log P.γ₃ + |Real.log ((1 - P.η₂) * P.γ₁ / (P.Δ₀ * L))|) / |Real.log P.γ₂| + 2

section TREpsTheorems

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : TREpsParams} {ε₁ : ℝ} {ε₂ : Option ℝ}
  {εs : ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)} {Δ : ℕ → ℝ} {L flow : ℝ}

/-- The counting step common to Theorems 3.4.5 and 3.4.6: if `|𝒮_k| ≤ N` before termination, the
run terminates with `#f ≤ (1 + log γ₃/|log γ₂|) N + (|log c| + |log ε_*|)/|log γ₂| + 1` and
`#∇f ≤ N + 1`, where `c = (1 - η₂) γ₁/(Δ₀ L)`. -/
private theorem tre_count (hf : AssumptionHL f L) (h : algorithm_3_4_1 f P ε₁ ε₂ εs x s Δ)
    {N : ℝ} (hN : 0 ≤ N)
    (hsucc : ∀ k, (∀ j ≤ k, ¬ stopTest f ε₁ ε₂ (x j)) →
      ((successSet (fun j => P.η₁ ≤ tr2Ratio f (x j) (s j)) k).card : ℝ) ≤ N) :
    ∃ kε, IsFirstHit (fun k => stopTest f ε₁ ε₂ (x k)) kε ∧
      (funEvalCount kε : ℝ) ≤ (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * N +
        (|Real.log ((1 - P.η₂) * P.γ₁ / (P.Δ₀ * L))| + |Real.log εs|) / |Real.log P.γ₂| + 1 ∧
      (derivEvalCount (fun k => P.η₁ ≤ tr2Ratio f (x k) (s k)) kε : ℝ) ≤ N + 1 := by
  have hεs := h.εs_pos
  have hL := hf.pos
  have hc : 0 < (1 - P.η₂) * P.γ₁ / (P.Δ₀ * L) := by
    have := sub_pos.2 P.η₂_lt_one; have := P.γ₁_pos; have := P.Δ₀_pos; positivity
  have hlog2 : 0 < |Real.log P.γ₂| := abs_pos.2 (Real.log_neg P.γ₂_pos P.γ₂_lt_one).ne
  have hA : 0 ≤ 1 + Real.log P.γ₃ / |Real.log P.γ₂| := by
    have := Real.log_nonneg P.one_le_γ₃; positivity
  set B := (|Real.log ((1 - P.η₂) * P.γ₁ / (P.Δ₀ * L))| + |Real.log εs|) / |Real.log P.γ₂|
  have hB : 0 ≤ B := by positivity
  refine exists_isFirstHit_evalCount_le_of_counting hA hN (by positivity) (fun k hk => ?_) hsucc
  have hΔ := lemma_3_4_2_delta_succ hf h hk
  have hmin : 0 < (1 - P.η₂) * P.γ₁ * εs / L := by
    have := sub_pos.2 P.η₂_lt_one; have := P.γ₁_pos; positivity
  have hcount := h.run.succ_count hk hmin hΔ
  have e : (1 - P.η₂) * P.γ₁ * εs / L / P.Δ₀ = (1 - P.η₂) * P.γ₁ / (P.Δ₀ * L) * εs := by
    have := P.Δ₀_pos; field_simp
  have hlog : |Real.log ((1 - P.η₂) * P.γ₁ * εs / L / P.Δ₀)| ≤
      |Real.log ((1 - P.η₂) * P.γ₁ / (P.Δ₀ * L))| + |Real.log εs| := by
    rw [e, Real.log_mul hc.ne' hεs.ne']
    exact abs_add_le _ _
  have : |Real.log ((1 - P.η₂) * P.γ₁ * εs / L / P.Δ₀)| / |Real.log P.γ₂| ≤ B :=
    div_le_div_of_nonneg_right hlog hlog2.le
  linarith

/-- **Theorem 3.4.5** of [cartis2022evaluation]. Under f.Bb and f.HL, every TRε run with
`ε_* = √ε₁` and `ε₂ = ∞` terminates at an iteration `k_ε` (`‖∇f(x_{k_ε})‖ ≤ ε₁`) after at most
`κ^A (f(x₀) - f_low)/ε₁^{3/2} + κ^B |log ε₁| + κ^C` evaluations of `f` and at most
`κ^S (f(x₀) - f_low)/ε₁^{3/2} + 2` evaluations of `∇f` and `∇²f`, with `κ^S = κ_Δf⁻¹` (3.4.20),
`κ^A = κ^S (1 + log γ₃/|log γ₂|)`, `κ^B = 1/(2|log γ₂|)` and `κ^C` of (3.4.22). -/
theorem theorem_3_4_5 (hb : Chapter02.AssumptionBb f flow) (hf : AssumptionHL f L)
    (h : algorithm_3_4_1 f P ε₁ none (√ε₁) x s Δ) :
    ∃ kε, IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε₁) kε ∧
      (funEvalCount kε : ℝ) ≤ kappaATREps P L * (f (x 0) - flow) / ε₁ ^ (3 / 2 : ℝ) +
        1 / (2 * |Real.log P.γ₂|) * |Real.log ε₁| + kappaCTREps P L ∧
      (derivEvalCount (fun k => P.η₁ ≤ tr2Ratio f (x k) (s k)) kε : ℝ) ≤
        kappaSTREps P L * (f (x 0) - flow) / ε₁ ^ (3 / 2 : ℝ) + 2 := by
  have hε := h.ε₁_pos
  set r := √ε₁ with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hε
  have hr2 : r ^ 2 = ε₁ := Real.sq_sqrt hε.le
  have hr3 : ε₁ ^ (3 / 2 : ℝ) = r ^ 3 := by
    rw [hr, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hε.le]; norm_num
  have hκ := kappaDeltaF_pos P hf.pos
  set X := (f (x 0) - flow) / ε₁ ^ (3 / 2 : ℝ)
  have hX : 0 ≤ X := div_nonneg (sub_nonneg.2 (hb _)) (by positivity)
  set N := kappaSTREps P L * X
  have hN : 0 ≤ N := mul_nonneg (inv_nonneg.2 hκ.le) hX
  have hsucc : ∀ k, (∀ j ≤ k + 1, ¬ stopTest f ε₁ none (x j)) →
      ((successSet (fun j => P.η₁ ≤ tr2Ratio f (x j) (s j)) k).card : ℝ) ≤ N := by
    intro k hk
    have hc : 0 < kappaDeltaF P L * r ^ 3 := by positivity
    have := card_successSet_le_div_of_decrease (φ := fun j => f (x j)) hc
      (fun j hj hs => by
        rw [h.run.eq_of_not_succ (fun i hi => hk i (hi.trans (hj.trans k.le_succ)))
          (not_le.1 hs)])
      (fun j hj hs => by
        have hj' : ∀ i ≤ j, ¬ stopTest f ε₁ none (x i) := fun i hi =>
          hk i (hi.trans (hj.trans k.le_succ))
        have hG : ε₁ < ‖gradient f (x (j + 1))‖ := by
          have := hk (j + 1) (Nat.succ_le_succ hj)
          rwa [stopTest_none, not_le] at this
        have hmin : r ^ 3 ≤ min (r ^ 3) (‖gradient f (x (j + 1))‖ ^ 2 / r) := by
          refine le_min le_rfl ?_
          rw [le_div_iff₀ hr0]
          have : (r ^ 2) ^ 2 ≤ ‖gradient f (x (j + 1))‖ ^ 2 :=
            pow_le_pow_left₀ (by positivity) (by rw [hr2]; exact hG.le) 2
          nlinarith
        obtain ⟨h1, h2⟩ := lemma_3_4_4 hf h hj' hs
        obtain ⟨hsΔ, -⟩ := h.run.step j hj'
        rcases lt_or_eq_of_le hsΔ with hlt | heq
        · exact (mul_le_mul_of_nonneg_left hmin hκ.le).trans (h1 hlt)
        · exact h2 heq)
      (hb (x (k + 1)))
    refine this.trans_eq ?_
    simp only [N, X, kappaSTREps, hr3]
    field_simp
  obtain ⟨kε, hk, hF, hD⟩ := tre_count hf h (by linarith)
    (card_successSet_le_add_one_of_forall hN hsucc)
  simp only [stopTest_none] at hk
  have hNe : N = kappaSTREps P L * (f (x 0) - flow) / ε₁ ^ (3 / 2 : ℝ) := by
    simp only [N, X]; ring
  refine ⟨kε, hk, ?_, by linarith⟩
  have hlogr : |Real.log r| = |Real.log ε₁| / 2 := by
    rw [hr, Real.log_sqrt hε.le, abs_div, abs_two]
  have hlog2 : 0 < |Real.log P.γ₂| := abs_pos.2 (Real.log_neg P.γ₂_pos P.γ₂_lt_one).ne
  rw [hlogr] at hF
  have e1 : (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * (N + 1) +
      (|Real.log ((1 - P.η₂) * P.γ₁ / (P.Δ₀ * L))| + |Real.log ε₁| / 2) / |Real.log P.γ₂| + 1 =
      kappaATREps P L * (f (x 0) - flow) / ε₁ ^ (3 / 2 : ℝ) +
        1 / (2 * |Real.log P.γ₂|) * |Real.log ε₁| + kappaCTREps P L := by
    simp only [N, X, kappaATREps, kappaCTREps]
    field_simp
    ring
  linarith

/-- The iterate is unchanged between a successful iteration `j` and the next successful one. -/
private theorem tre_x_eq (h : algorithm_3_4_1 f P ε₁ ε₂ εs x s Δ) {j j' : ℕ}
    (hstop : ∀ i < j', ¬ stopTest f ε₁ ε₂ (x i))
    (hnone : ∀ i, j < i → i < j' → ¬ P.η₁ ≤ tr2Ratio f (x i) (s i)) :
    ∀ m, j + 1 ≤ m → m ≤ j' → x m = x (j + 1) := by
  intro m hm hmj
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    rw [h.run.eq_of_not_succ (fun i hi => hstop i (by omega)) (not_le.1 (hnone m (by omega)
      (by omega))), ih (by omega)]

/-- **Theorem 3.4.6** of [cartis2022evaluation], **corrected constants**. Under f.Bb and f.HL,
every TRε run with `ε₁, ε₂ ∈ (0, 1]` and `ε_* = ε₂` terminates at an iteration `k_ε` with
`‖∇f(x_{k_ε})‖ ≤ ε₁` and `λ_min[∇²f(x_{k_ε})] ≥ -ε₂`, after at most
`2 κ^A (f(x₀) - f_low)/min(ε₁² ε₂⁻¹, ε₂³) + κ^D |log ε₂| + κ^C` evaluations of `f` and at most
`2 κ^S (f(x₀) - f_low)/min(ε₁² ε₂⁻¹, ε₂³) + 2` evaluations of `∇f` and `∇²f` (`κ^S, κ^A, κ^C` as
in Theorem 3.4.5, `κ^D = 1/|log γ₂|`). Correction: the book's proof claims that when
`λ_min[∇²f(x_{j+1})] < -ε₂` "`x_{j+1}` is on the trust-region boundary"; the boundary step is
taken at the *next* successful iteration from `x_{j+1}`. A successful iteration without the
required decrease is followed by one with decrease `≥ κ_Δf ε₂³`, whence the factor `2`. -/
theorem theorem_3_4_6 (hb : Chapter02.AssumptionBb f flow) (hf : AssumptionHL f L) {e : ℝ}
    (h : algorithm_3_4_1 f P ε₁ (some e) e x s Δ) :
    ∃ kε, IsFirstHit (fun k => stopTest f ε₁ (some e) (x k)) kε ∧
      (funEvalCount kε : ℝ) ≤
        2 * kappaATREps P L * (f (x 0) - flow) / min (ε₁ ^ 2 / e) (e ^ 3) +
          1 / |Real.log P.γ₂| * |Real.log e| + kappaCTREps P L ∧
      (derivEvalCount (fun k => P.η₁ ≤ tr2Ratio f (x k) (s k)) kε : ℝ) ≤
        2 * kappaSTREps P L * (f (x 0) - flow) / min (ε₁ ^ 2 / e) (e ^ 3) + 2 := by
  have hε := h.ε₁_pos
  have he := h.εs_pos
  have hκ := kappaDeltaF_pos P hf.pos
  set m := min (ε₁ ^ 2 / e) (e ^ 3)
  have hm : 0 < m := lt_min (by positivity) (by positivity)
  set X := (f (x 0) - flow) / m
  have hX : 0 ≤ X := div_nonneg (sub_nonneg.2 (hb _)) hm.le
  set N := kappaSTREps P L * X
  have hN : 0 ≤ N := mul_nonneg (inv_nonneg.2 hκ.le) hX
  set succ := fun j => P.η₁ ≤ tr2Ratio f (x j) (s j)
  have hsucc : ∀ k, (∀ j ≤ k, ¬ stopTest f ε₁ (some e) (x j)) →
      ((successSet succ k).card : ℝ) ≤ 2 * N + 1 := by
    intro k hk
    set good := fun j => succ j ∧ (‖s j‖ = Δ j ∨ ε₁ < ‖gradient f (x (j + 1))‖)
    have hcard := card_successSet_le_two_mul_add_one (succ := succ) (good := good) (K := k)
      (fun j _ hg => hg.1) (fun j j' hjj' hj'k hsj hgj hsj' hnone => by
        refine ⟨hsj', Or.inl ?_⟩
        have hstop : ∀ i < j', ¬ stopTest f ε₁ (some e) (x i) := fun i hi => hk i (by omega)
        have hx := tre_x_eq h hstop hnone j' (by omega) le_rfl
        have hg : ‖gradient f (x (j + 1))‖ ≤ ε₁ := by
          by_contra hlt
          exact hgj ⟨hsj, Or.inr (not_le.1 hlt)⟩
        have hnot := hk j' hj'k
        rw [not_stopTest_some, hx] at hnot
        have hlam := hnot.resolve_left (not_lt.2 hg)
        rw [← hx] at hlam
        exact (h.run.step j' fun i hi => hk i (hi.trans hj'k)).2.2.2 e rfl hlam) k le_rfl
    have hc : 0 < kappaDeltaF P L * m := by positivity
    have hG := card_le_div_of_decrease (φ := fun j => f (x j)) (T := successSet good k) hc
      successSet_subset_range (fun j hj => h.le fun i hi => hk i (hi.trans hj))
      (fun j hj => by
        rw [mem_successSet] at hj
        obtain ⟨hjk, hsj, hgj⟩ := hj
        have hj' : ∀ i ≤ j, ¬ stopTest f ε₁ (some e) (x i) := fun i hi => hk i (hi.trans hjk)
        obtain ⟨h1, h2⟩ := lemma_3_4_4 hf h hj' hsj
        obtain ⟨hsΔ, -⟩ := h.run.step j hj'
        have hme : m ≤ e ^ 3 := min_le_right _ _
        rcases lt_or_eq_of_le hsΔ with hlt | heq
        · rcases hgj with heq | hgr
          · exact absurd heq hlt.ne
          · refine (mul_le_mul_of_nonneg_left (le_min hme ?_) hκ.le).trans (h1 hlt)
            refine (min_le_left _ _).trans ?_
            exact div_le_div_of_nonneg_right
              (pow_le_pow_left₀ hε.le hgr.le 2) he.le
        · exact (mul_le_mul_of_nonneg_left hme hκ.le).trans (h2 heq))
      (hb (x (k + 1)))
    have : ((successSet succ k).card : ℝ) ≤ 2 * (successSet good k).card + 1 := by
      exact_mod_cast hcard
    have hGN : ((successSet good k).card : ℝ) ≤ N := by
      refine hG.trans_eq ?_
      simp only [N, X, kappaSTREps]
      field_simp
    linarith
  obtain ⟨kε, hk, hF, hD⟩ := tre_count hf h (by linarith) hsucc
  have hNe : N = kappaSTREps P L * (f (x 0) - flow) / m := by simp only [N, X]; ring
  refine ⟨kε, hk, ?_, hD.trans_eq (by rw [hNe]; ring)⟩
  have e1 : (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * (2 * N + 1) +
      (|Real.log ((1 - P.η₂) * P.γ₁ / (P.Δ₀ * L))| + |Real.log e|) / |Real.log P.γ₂| + 1 =
      2 * kappaATREps P L * (f (x 0) - flow) / m + 1 / |Real.log P.γ₂| * |Real.log e| +
        kappaCTREps P L := by
    have hlog2 : 0 < |Real.log P.γ₂| := abs_pos.2 (Real.log_neg P.γ₂_pos P.γ₂_lt_one).ne
    simp only [N, X, kappaATREps, kappaCTREps]
    field_simp
    ring
  linarith

end TREpsTheorems

/-! ### The iRN framework -/

/-- The least curvature of a bilinear form `A` restricted to a subspace `V`:
`λ_min[Qᵀ A Q]` for a matrix `Q` with orthonormal columns spanning `V` ([cartis2022evaluation],
(3.4.32)); for `V = ⊤` (`Q = I`) it is `λ_min[A]`. -/
noncomputable def minCurvatureOn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ) (V : Submodule ℝ E) : ℝ :=
  minCurvature (A.compContinuousLinearMap fun _ => V.subtypeL)

section MinCurvatureOn

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ} {V : Submodule ℝ E}

/-- `λ_min[Qᵀ A Q] ‖d‖² ≤ A[d, d]` for `d ∈ V`. -/
theorem minCurvatureOn_mul_norm_sq_le {d : E} (hd : d ∈ V) :
    minCurvatureOn A V * ‖d‖ ^ 2 ≤ A (fun _ => d) := by
  have := minCurvature_mul_norm_sq_le (A.compContinuousLinearMap fun _ => V.subtypeL)
    (⟨d, hd⟩ : V)
  rw [minCurvatureOn]
  simpa using this

/-- `c ≤ λ_min[Qᵀ A Q]` if `c ‖d‖² ≤ A[d, d]` on `V` and `c ≤ 0`. -/
theorem le_minCurvatureOn {c : ℝ} (hc : c ≤ 0) (h : ∀ d ∈ V, c * ‖d‖ ^ 2 ≤ A (fun _ => d)) :
    c ≤ minCurvatureOn A V := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · rw [minCurvatureOn, minCurvature_of_subsingleton]; exact hc
  · refine le_minCurvature_iff.2 fun d => ?_
    simpa using h d d.2

end MinCurvatureOn

/-- The constants of Algorithm 3.4.2 (iRN): `0 < σ_min ≤ σ_max`, `0 < η < 1`, `1 < γ₁ ≤ γ₂`,
`κ₁, κ₂, κ₃, κ₄ > 0` ((3.4.29)–(3.4.32)) and the initial upper bound `σ₀ᵁ ∈ [σ_min, σ_max]`. -/
structure IRNParams where
  /-- The lower regularization bound. -/
  σmin : ℝ
  /-- The upper regularization bound. -/
  σmax : ℝ
  /-- The acceptance threshold. -/
  η : ℝ
  /-- The lower increase factor. -/
  γ₁ : ℝ
  /-- The upper increase factor. -/
  γ₂ : ℝ
  /-- The constant of (3.4.29) (first part). -/
  κ₁ : ℝ
  /-- The constant of (3.4.29) (second part). -/
  κ₂ : ℝ
  /-- The constant of (3.4.30). -/
  κ₃ : ℝ
  /-- The constant of (3.4.32). -/
  κ₄ : ℝ
  /-- The initial upper regularization bound `σ₀ᵁ`. -/
  σU₀ : ℝ
  /-- `σ_min > 0`. -/
  σmin_pos : 0 < σmin
  /-- `σ_min ≤ σ_max`. -/
  σmin_le_σmax : σmin ≤ σmax
  /-- `η > 0`. -/
  η_pos : 0 < η
  /-- `η < 1`. -/
  η_lt_one : η < 1
  /-- `γ₁ > 1`. -/
  one_lt_γ₁ : 1 < γ₁
  /-- `γ₁ ≤ γ₂`. -/
  γ₁_le_γ₂ : γ₁ ≤ γ₂
  /-- `κ₁ > 0`. -/
  κ₁_pos : 0 < κ₁
  /-- `κ₂ > 0`. -/
  κ₂_pos : 0 < κ₂
  /-- `κ₃ > 0`. -/
  κ₃_pos : 0 < κ₃
  /-- `κ₄ > 0`. -/
  κ₄_pos : 0 < κ₄
  /-- `σ_min ≤ σ₀ᵁ`. -/
  σmin_le_σU₀ : σmin ≤ σU₀
  /-- `σ₀ᵁ ≤ σ_max`. -/
  σU₀_le_σmax : σU₀ ≤ σmax

/-- The gradient (3.4.31) of the iRN model (3.4.27): `∇m(s) = ∇f(x) + (∇²f(x) + λ I) s`. -/
noncomputable def irnGrad (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (lam : ℝ) (s : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  gradient f x + hessianOperator f x s + lam • s

/-- Step 2 of Algorithm 3.4.2 at the iterate `x` with bounds `σᴸ, σᵁ`, multiplier `λ` and
subspace `V` (the range of `Q_k`): (3.4.28) `σᴸ ‖s‖ ≤ λ ≤ σᵁ ‖s‖`, the slope condition (3.4.29),
the gradient bound (3.4.30) and, if `ε₂ < ∞`, the curvature condition (3.4.32)
`λ_min[Qᵀ (∇²f(x) + λ I) Q] ≥ -κ₄ ‖s‖`. -/
def irnStep (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : IRNParams) (ε₂ : Option ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (σL σU lam : ℝ) (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (s : EuclideanSpace ℝ (Fin n)) : Prop :=
  σL * ‖s‖ ≤ lam ∧ lam ≤ σU * ‖s‖ ∧
    ⟪s, irnGrad f x lam s⟫ ≤ min (P.κ₁ * ‖s‖ ^ 2)
      (1 / 2 * ⟪s, hessianOperator f x s + lam • s⟫ + 1 / 2 * P.κ₂ * ‖s‖ ^ 3) ∧
    ‖irnGrad f x lam s‖ ≤ lam * ‖s‖ + P.κ₃ * ‖s‖ ^ 2 ∧
    (ε₂ ≠ none → -(P.κ₄ * ‖s‖) ≤ minCurvatureOn (iteratedFDeriv ℝ 2 f x + lam • innerForm) V)

/-- The ratio (3.4.35) of iRN: `ρ = (f(x) - f(x + s)) / ‖s‖³`. -/
noncomputable def irnRatio (f : EuclideanSpace ℝ (Fin n) → ℝ) (x s : EuclideanSpace ℝ (Fin n)) :
    ℝ :=
  reductionRatio f x s (‖s‖ ^ 3)

/-- The termination test of iRN: `‖∇f(x)‖ ≤ ε₁` and, if `ε₂ < ∞`,
`λ_min[Qᵀ ∇²f(x) Q] ≥ -ε₂` (3.4.34) (the strict-local-minimizer test of Step 3 implies it). -/
def irnTest (f : EuclideanSpace ℝ (Fin n) → ℝ) (ε₁ : ℝ) (ε₂ : Option ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) : Prop :=
  ‖gradient f x‖ ≤ ε₁ ∧ ∀ e ∈ ε₂, -e ≤ minCurvatureOn (iteratedFDeriv ℝ 2 f x) V

/-- Step 5 of Algorithm 3.4.2 (the update of `σᴸ, σᵁ`) for the ratio `ρ`, multiplier `λ` and step
`s`. -/
def irnUpdate (P : IRNParams) (ρ lam : ℝ) (s : EuclideanSpace ℝ (Fin n)) (σU σL' σU' : ℝ) :
    Prop :=
  (P.η ≤ ρ → σL' = 0 ∧ σU' = σU) ∧
    (ρ < P.η → lam < P.σmin * ‖s‖ →
      P.σmin ≤ σL' ∧ σL' ≤ P.σmax ∧ σL' ≤ σU' ∧ σU' ≤ P.σmax) ∧
    (ρ < P.η → P.σmin * ‖s‖ ≤ lam → σL' = P.γ₁ * (lam / ‖s‖) ∧ σU' = P.γ₂ * (lam / ‖s‖))

/-- **Algorithm 3.4.2** (iRN) of [cartis2022evaluation], as a run predicate on iterates `x`,
steps `s`, multipliers `lam`, bounds `σL, σU` and subspaces `V` (the ranges of the matrices `Q_k`
with orthonormal columns of (3.4.32); `V k = ⊤` is `Q_k = I`): `ε₁ ∈ (0, 1]`, `ε₂ > 0` if finite,
`σᴸ_0 = 0`, `σᵁ_0 = σ₀ᵁ`; Step 2 at every iteration reached at which the first-order test of
Step 1 (only active if `ε₂ = ∞`) fails; and, before termination (test `irnTest`, Steps 1 and 3),
the acceptance of Step 4 with the ratio (3.4.35) and the update of Step 5. -/
structure algorithm_3_4_2 (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : IRNParams) (ε₁ : ℝ)
    (ε₂ : Option ℝ) (x s : ℕ → EuclideanSpace ℝ (Fin n)) (lam σL σU : ℕ → ℝ)
    (V : ℕ → Submodule ℝ (EuclideanSpace ℝ (Fin n))) : Prop where
  /-- `ε₁ > 0`. -/
  ε₁_pos : 0 < ε₁
  /-- `ε₁ ≤ 1`. -/
  ε₁_le_one : ε₁ ≤ 1
  /-- `ε₂ > 0` if finite. -/
  ε₂_pos : ∀ e ∈ ε₂, 0 < e
  /-- `σᴸ_0 = 0`. -/
  sigmaL_zero : σL 0 = 0
  /-- `σᵁ_0 = σ₀ᵁ`. -/
  sigmaU_zero : σU 0 = P.σU₀
  /-- Step 2. -/
  step : ∀ k, (∀ j < k, ¬ irnTest f ε₁ ε₂ (x j) (V j)) →
    (ε₂ = none → ¬ ‖gradient f (x k)‖ ≤ ε₁) →
    irnStep f P ε₂ (x k) (σL k) (σU k) (lam k) (V k) (s k)
  /-- Step 4. -/
  accept : UntilHit (fun k => irnTest f ε₁ ε₂ (x k) (V k)) fun k =>
    x (k + 1) = if P.η ≤ irnRatio f (x k) (s k) then x k + s k else x k
  /-- Step 5. -/
  update : UntilHit (fun k => irnTest f ε₁ ε₂ (x k) (V k)) fun k =>
    irnUpdate P (irnRatio f (x k) (s k)) (lam k) (s k) (σU k) (σL (k + 1)) (σU (k + 1))

namespace algorithm_3_4_2

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : IRNParams} {ε₁ : ℝ} {ε₂ : Option ℝ}
  {x s : ℕ → EuclideanSpace ℝ (Fin n)} {lam σL σU : ℕ → ℝ}
  {V : ℕ → Submodule ℝ (EuclideanSpace ℝ (Fin n))}

/-- Step 2 holds at every iteration before termination. -/
theorem step_of_le (h : algorithm_3_4_2 f P ε₁ ε₂ x s lam σL σU V) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ irnTest f ε₁ ε₂ (x j) (V j)) :
    irnStep f P ε₂ (x k) (σL k) (σU k) (lam k) (V k) (s k) :=
  h.step k (fun j hj => hk j hj.le) fun he hg => hk k le_rfl ⟨hg, by simp [he]⟩

/-- Before termination the step is nonzero (a zero step would satisfy the termination test). -/
theorem s_ne_zero (h : algorithm_3_4_2 f P ε₁ ε₂ x s lam σL σU V) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ irnTest f ε₁ ε₂ (x j) (V j)) : s k ≠ 0 := by
  intro hs0
  obtain ⟨h1, h2, -, h4, h5⟩ := h.step_of_le hk
  rw [hs0, norm_zero, mul_zero] at h1 h2
  have hl : lam k = 0 := le_antisymm h2 h1
  have hg : ‖gradient f (x k)‖ ≤ 0 := by simpa [irnGrad, hs0, hl] using h4
  refine hk k le_rfl ⟨hg.trans h.ε₁_pos.le, fun e he => ?_⟩
  have := h5 (by rintro rfl; simp at he)
  rw [hs0, hl, norm_zero, mul_zero, neg_zero, zero_smul, add_zero] at this
  linarith [h.ε₂_pos e he]

/-- The lower bounds `σᴸ_k` are nonnegative up to (and including) termination. -/
theorem sigmaL_nonneg (h : algorithm_3_4_2 f P ε₁ ε₂ x s lam σL σU V) :
    ∀ k, (∀ j < k, ¬ irnTest f ε₁ ε₂ (x j) (V j)) → 0 ≤ σL k := by
  intro k
  induction k with
  | zero => intro _; rw [h.sigmaL_zero]
  | succ k ih =>
    intro hk
    have hk' : ∀ j ≤ k, ¬ irnTest f ε₁ ε₂ (x j) (V j) := fun j hj => hk j (Nat.lt_succ_of_le hj)
    obtain ⟨u1, u2, u3⟩ := h.update k hk'
    by_cases hs : P.η ≤ irnRatio f (x k) (s k)
    · rw [(u1 hs).1]
    · have hs := not_le.1 hs
      by_cases hl : lam k < P.σmin * ‖s k‖
      · exact P.σmin_pos.le.trans (u2 hs hl).1
      · rw [(u3 hs (not_lt.1 hl)).1]
        have : 0 ≤ lam k := (mul_nonneg P.σmin_pos.le (norm_nonneg _)).trans (not_lt.1 hl)
        have := P.one_lt_γ₁
        positivity

/-- A successful iteration moves to the trial point. -/
theorem eq_add (h : algorithm_3_4_2 f P ε₁ ε₂ x s lam σL σU V) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ irnTest f ε₁ ε₂ (x j) (V j)) (hs : P.η ≤ irnRatio f (x k) (s k)) :
    x (k + 1) = x k + s k := by
  rw [h.accept k hk, ite_eq_left hs]

/-- An unsuccessful iteration keeps the iterate. -/
theorem eq_self (h : algorithm_3_4_2 f P ε₁ ε₂ x s lam σL σU V) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ irnTest f ε₁ ε₂ (x j) (V j)) (hs : irnRatio f (x k) (s k) < P.η) :
    x (k + 1) = x k := by
  rw [h.accept k hk, ite_eq_right (not_le.2 hs)]

/-- The decrease on a successful iteration: `f(x_k) - f(x_{k+1}) ≥ η ‖s_k‖³`. -/
theorem sub_ge (h : algorithm_3_4_2 f P ε₁ ε₂ x s lam σL σU V) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ irnTest f ε₁ ε₂ (x j) (V j)) (hs : P.η ≤ irnRatio f (x k) (s k)) :
    P.η * ‖s k‖ ^ 3 ≤ f (x k) - f (x (k + 1)) := by
  rw [h.eq_add hk hs]
  exact sub_le_of_le_reductionRatio (by have := h.s_ne_zero hk; positivity) hs

/-- The objective does not increase before termination. -/
theorem le (h : algorithm_3_4_2 f P ε₁ ε₂ x s lam σL σU V) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ irnTest f ε₁ ε₂ (x j) (V j)) : f (x (k + 1)) ≤ f (x k) := by
  by_cases hs : P.η ≤ irnRatio f (x k) (s k)
  · have := h.sub_ge hk hs
    have : 0 ≤ P.η * ‖s k‖ ^ 3 := mul_nonneg P.η_pos.le (by positivity)
    linarith
  · rw [h.eq_self hk (not_le.1 hs)]

end algorithm_3_4_2

/-! ### Lemmas 3.4.7–3.4.10 -/

section IRNLemmas

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : IRNParams} {ε₁ : ℝ} {ε₂ : Option ℝ}
  {x s : ℕ → EuclideanSpace ℝ (Fin n)} {lam σL σU : ℕ → ℝ}
  {V : ℕ → Submodule ℝ (EuclideanSpace ℝ (Fin n))} {L : ℝ}

/-- **Lemma 3.4.7** of [cartis2022evaluation] (one iteration). Under f.HL, if the step `s ≠ 0`
and the multiplier `λ` satisfy (3.4.29) at `x` and `λ ≥ (2η + κ₂ + L_{f,2}) ‖s‖` (3.4.37), then
`ρ ≥ η` for the ratio (3.4.35). -/
theorem lemma_3_4_7_step (hf : AssumptionHL f L) {y d : EuclideanSpace ℝ (Fin n)} {l : ℝ}
    (hd : d ≠ 0)
    (h29 : ⟪d, irnGrad f y l d⟫ ≤ 1 / 2 * ⟪d, hessianOperator f y d + l • d⟫ +
      1 / 2 * P.κ₂ * ‖d‖ ^ 3)
    (hl : (2 * P.η + P.κ₂ + L) * ‖d‖ ≤ l) : P.η ≤ irnRatio f y d := by
  have ht : 0 < ‖d‖ := norm_pos_iff.2 hd
  have habs := abs_sub_taylorPolynomial_le_of_lipschitz convex_univ (fun z _ => hf.contDiffAt z)
    hf.iteratedFDerivLipschitzOn (mem_univ y) (mem_univ (y + d))
  rw [taylorPolynomial_two_eq_quadModel (hf.contDiffAt y), quadModel_def,
    show ((Nat.factorial (2 + 1 : ℕ) : ℕ) : ℝ) = 6 by norm_num [Nat.factorial],
    show (2 + 1 : ℕ) = 3 from rfl] at habs
  have hlow := le_abs_self (f (y + d) - (f y + (⟪gradient f y, d⟫ +
    1 / 2 * ⟪d, hessianOperator f y d⟫)))
  rw [irnGrad, inner_add_right, inner_add_right, inner_add_right, inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm] at h29
  rw [irnRatio, le_reductionRatio_iff (by positivity)]
  have hL := hf.nonneg
  have : (2 * P.η + P.κ₂ + L) * ‖d‖ * ‖d‖ ^ 2 ≤ l * ‖d‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hl (sq_nonneg _)
  nlinarith [pow_pos ht 3]

/-- **Lemma 3.4.7** of [cartis2022evaluation]. Under f.HL, if at an iteration `k` before
termination of an iRN run `λ_k ≥ (2η + κ₂ + L_{f,2}) ‖s_k‖` (3.4.37), then `ρ_k ≥ η` and the
iteration is successful. -/
theorem lemma_3_4_7 (hf : AssumptionHL f L) (h : algorithm_3_4_2 f P ε₁ ε₂ x s lam σL σU V)
    {k : ℕ} (hk : ∀ j ≤ k, ¬ irnTest f ε₁ ε₂ (x j) (V j))
    (hl : (2 * P.η + P.κ₂ + L) * ‖s k‖ ≤ lam k) : P.η ≤ irnRatio f (x k) (s k) :=
  lemma_3_4_7_step hf (h.s_ne_zero hk) ((h.step_of_le hk).2.2.1.trans (min_le_right _ _)) hl

/-- The bound `σ^U_max = max(σ_max, γ₂ (2η + κ₂ + L_{f,2}))` of (3.4.38). -/
noncomputable def sigmaUMax (P : IRNParams) (L : ℝ) : ℝ :=
  max P.σmax (P.γ₂ * (2 * P.η + P.κ₂ + L))

theorem σmin_le_sigmaUMax (P : IRNParams) (L : ℝ) : P.σmin ≤ sigmaUMax P L :=
  P.σmin_le_σmax.trans (le_max_left _ _)

theorem sigmaUMax_pos (P : IRNParams) (L : ℝ) : 0 < sigmaUMax P L :=
  P.σmin_pos.trans_le (σmin_le_sigmaUMax P L)

/-- **Lemma 3.4.8** of [cartis2022evaluation] ((3.4.38)). Under f.HL, for every `k` up to (and
including) termination of an iRN run, `σᵁ_k ≤ σᵁ_max`. -/
theorem lemma_3_4_8 (hf : AssumptionHL f L) (h : algorithm_3_4_2 f P ε₁ ε₂ x s lam σL σU V) :
    ∀ k, (∀ j < k, ¬ irnTest f ε₁ ε₂ (x j) (V j)) → σU k ≤ sigmaUMax P L := by
  intro k
  induction k with
  | zero => intro _; rw [h.sigmaU_zero]; exact P.σU₀_le_σmax.trans (le_max_left _ _)
  | succ k ih =>
    intro hk
    have hk' : ∀ j ≤ k, ¬ irnTest f ε₁ ε₂ (x j) (V j) := fun j hj => hk j (Nat.lt_succ_of_le hj)
    obtain ⟨u1, u2, u3⟩ := h.update k hk'
    by_cases hs : P.η ≤ irnRatio f (x k) (s k)
    · rw [(u1 hs).2]; exact ih fun j hj => hk' j hj.le
    · have hs := not_le.1 hs
      by_cases hl : lam k < P.σmin * ‖s k‖
      · exact (u2 hs hl).2.2.2.trans (le_max_left _ _)
      · rw [(u3 hs (not_lt.1 hl)).2]
        have hpos : 0 < ‖s k‖ := norm_pos_iff.2 (h.s_ne_zero hk')
        have hlt : lam k < (2 * P.η + P.κ₂ + L) * ‖s k‖ := by
          by_contra hge
          exact absurd (lemma_3_4_7 hf h hk' (not_lt.1 hge)) (not_le.2 hs)
        refine le_trans ?_ (le_max_right _ _)
        have hγ : 0 < P.γ₂ := by linarith [P.one_lt_γ₁, P.γ₁_le_γ₂]
        refine mul_le_mul_of_nonneg_left ?_ hγ.le
        rw [div_le_iff₀ hpos]; exact hlt.le

/-- **Lemma 3.4.9** of [cartis2022evaluation], first part ((3.4.39)). Under f.HL, if iteration
`k` (before termination) of an iRN run is successful, then
`‖s_k‖² ≥ 2/(L_{f,2} + 4 σᵁ_max + 2κ₃) ‖∇f(x_{k+1})‖`. -/
theorem lemma_3_4_9 (hf : AssumptionHL f L) (h : algorithm_3_4_2 f P ε₁ ε₂ x s lam σL σU V)
    {k : ℕ} (hk : ∀ j ≤ k, ¬ irnTest f ε₁ ε₂ (x j) (V j)) (hs : P.η ≤ irnRatio f (x k) (s k)) :
    2 / (L + 4 * sigmaUMax P L + 2 * P.κ₃) * ‖gradient f (x (k + 1))‖ ≤ ‖s k‖ ^ 2 := by
  obtain ⟨h1, h2, -, h4, -⟩ := h.step_of_le hk
  have hσ := lemma_3_4_8 hf h k fun j hj => hk j hj.le
  rw [h.eq_add hk hs]
  have hG := norm_gradient_add_le hf (x := x k) (s := s k)
  set t := ‖s k‖
  have hg : ‖gradient f (x k) + hessianOperator f (x k) (s k)‖ ≤
      ‖irnGrad f (x k) (lam k) (s k)‖ + lam k * t := by
    have := norm_sub_le (irnGrad f (x k) (lam k) (s k)) (lam k • s k)
    rw [irnGrad, add_sub_cancel_right, norm_smul] at this
    have hl0 : 0 ≤ lam k :=
      (mul_nonneg (h.sigmaL_nonneg k fun j hj => hk j hj.le) (norm_nonneg _)).trans h1
    rwa [Real.norm_of_nonneg hl0] at this
  have hlt : lam k * t ≤ sigmaUMax P L * t ^ 2 := by
    have := mul_le_mul_of_nonneg_right hσ (norm_nonneg (s k))
    nlinarith [norm_nonneg (s k)]
  have hC : 0 < L + 4 * sigmaUMax P L + 2 * P.κ₃ := by
    linarith [hf.nonneg, sigmaUMax_pos P L, P.κ₃_pos]
  rw [div_mul_eq_mul_div, div_le_iff₀ hC]
  nlinarith

/-- **Lemma 3.4.9** of [cartis2022evaluation], second part ((3.4.40)). Under f.HL, if (3.4.32)
holds at iteration `k` (before termination, `ε₂ < ∞`) of an iRN run, then
`‖s_k‖ ≥ -λ_min[Q_kᵀ ∇²f(x_k) Q_k]/(κ₄ + σᵁ_max)`. -/
theorem lemma_3_4_9_curv (hf : AssumptionHL f L)
    (h : algorithm_3_4_2 f P ε₁ ε₂ x s lam σL σU V) (hε₂ : ε₂ ≠ none) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ irnTest f ε₁ ε₂ (x j) (V j)) :
    -minCurvatureOn (iteratedFDeriv ℝ 2 f (x k)) (V k) / (P.κ₄ + sigmaUMax P L) ≤ ‖s k‖ := by
  obtain ⟨-, h2, -, -, h5⟩ := h.step_of_le hk
  have hσ := lemma_3_4_8 hf h k fun j hj => hk j hj.le
  have hc : 0 < P.κ₄ + sigmaUMax P L := by linarith [P.κ₄_pos, sigmaUMax_pos P L]
  have hlam : lam k ≤ sigmaUMax P L * ‖s k‖ :=
    h2.trans (mul_le_mul_of_nonneg_right hσ (norm_nonneg _))
  have key : -((P.κ₄ + sigmaUMax P L) * ‖s k‖) ≤
      minCurvatureOn (iteratedFDeriv ℝ 2 f (x k)) (V k) := by
    refine le_minCurvatureOn (by have := norm_nonneg (s k); nlinarith) fun d hd => ?_
    have := minCurvatureOn_mul_norm_sq_le (A := iteratedFDeriv ℝ 2 f (x k) + lam k • innerForm) hd
    have h6 := mul_le_mul_of_nonneg_right (h5 hε₂) (sq_nonneg ‖d‖)
    simp only [add_apply, smul_apply, innerForm_apply_diag, smul_eq_mul] at this
    have : lam k * ‖d‖ ^ 2 ≤ sigmaUMax P L * ‖s k‖ * ‖d‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hlam (sq_nonneg _)
    nlinarith
  rw [div_le_iff₀ hc]
  linarith

/-- The constant `log(σᵁ_max/σ_min)/log γ₁ + 1` of (3.4.42). -/
noncomputable def irnUnsuccBound (P : IRNParams) (L : ℝ) : ℝ :=
  Real.log (sigmaUMax P L / P.σmin) / Real.log P.γ₁ + 1

theorem one_le_irnUnsuccBound (P : IRNParams) (L : ℝ) : 1 ≤ irnUnsuccBound P L := by
  have := Real.log_nonneg ((one_le_div P.σmin_pos).2 (σmin_le_sigmaUMax P L))
  have := Real.log_pos P.one_lt_γ₁
  unfold irnUnsuccBound
  have : 0 ≤ Real.log (sigmaUMax P L / P.σmin) / Real.log P.γ₁ := by positivity
  linarith

/-- The growth of `σᴸ` along a block of `m ≥ 1` unsuccessful iterations `i, …, i + m - 1` before
termination: `σᴸ_{i+m} ≥ γ₁^{m-1} σ_min`. -/
private theorem irn_sigmaL_ge (h : algorithm_3_4_2 f P ε₁ ε₂ x s lam σL σU V) {i : ℕ} :
    ∀ m, 1 ≤ m → (∀ j < i + m, ¬ irnTest f ε₁ ε₂ (x j) (V j)) →
      (∀ l, i ≤ l → l < i + m → irnRatio f (x l) (s l) < P.η) →
      P.γ₁ ^ (m - 1) * P.σmin ≤ σL (i + m) := by
  have hγ := P.one_lt_γ₁
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    intro hstop hfail
    have hi : ∀ j ≤ i, ¬ irnTest f ε₁ ε₂ (x j) (V j) := fun j hj => hstop j (by omega)
    obtain ⟨-, u2, u3⟩ := h.update i hi
    have hs := hfail i le_rfl (by omega)
    rw [Nat.sub_self, pow_zero, one_mul]
    by_cases hl : lam i < P.σmin * ‖s i‖
    · exact (u2 hs hl).1
    · rw [(u3 hs (not_lt.1 hl)).1]
      have hpos : 0 < ‖s i‖ := norm_pos_iff.2 (h.s_ne_zero hi)
      have : P.σmin ≤ lam i / ‖s i‖ := by rw [le_div_iff₀ hpos]; exact not_lt.1 hl
      nlinarith [P.σmin_pos]
  | succ m hm ih =>
    intro hstop hfail
    have hprev := ih (fun j hj => hstop j (by omega)) fun l hl hl' => hfail l hl (by omega)
    have hl : ∀ j ≤ i + m, ¬ irnTest f ε₁ ε₂ (x j) (V j) := fun j hj => hstop j (by omega)
    obtain ⟨-, u2, u3⟩ := h.update (i + m) hl
    have hs := hfail (i + m) (by omega) (by omega)
    obtain ⟨h1, -⟩ := h.step_of_le hl
    have hpos : 0 < ‖s (i + m)‖ := norm_pos_iff.2 (h.s_ne_zero hl)
    have hpow : 1 ≤ P.γ₁ ^ (m - 1) := one_le_pow₀ hγ.le
    have hL : σL (i + m) ≤ lam (i + m) / ‖s (i + m)‖ := by rw [le_div_iff₀ hpos]; exact h1
    have hge : P.σmin * ‖s (i + m)‖ ≤ lam (i + m) := by
      have := mul_le_mul_of_nonneg_right (hprev.trans hL) hpos.le
      rw [div_mul_cancel₀ _ hpos.ne'] at this
      have h3 : P.σmin * ‖s (i + m)‖ ≤ P.γ₁ ^ (m - 1) * P.σmin * ‖s (i + m)‖ := by
        have := mul_le_mul_of_nonneg_right hpow (mul_nonneg P.σmin_pos.le hpos.le)
        linarith
      linarith
    rw [show i + (m + 1) = i + m + 1 by ring, (u3 hs hge).1,
      show m + 1 - 1 = m - 1 + 1 by omega, pow_succ]
    nlinarith [P.σmin_pos]

/-- **Lemma 3.4.10** of [cartis2022evaluation] ((3.4.42)). Under f.HL, a block of `m`
consecutive unsuccessful iterations `i, …, i + m - 1` of an iRN run which is followed by an
iteration `i + m` before termination (e.g. the iterations strictly between two consecutive
successful ones, or before the first one) has `m ≤ log(σᵁ_max/σ_min)/log γ₁ + 1`. -/
theorem lemma_3_4_10 (hf : AssumptionHL f L) (h : algorithm_3_4_2 f P ε₁ ε₂ x s lam σL σU V)
    {i m : ℕ} (hstop : ∀ j ≤ i + m, ¬ irnTest f ε₁ ε₂ (x j) (V j))
    (hfail : ∀ l, i ≤ l → l < i + m → irnRatio f (x l) (s l) < P.η) :
    (m : ℝ) ≤ irnUnsuccBound P L := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [CharP.cast_eq_zero]; linarith [one_le_irnUnsuccBound P L]
  have hσL := irn_sigmaL_ge h m hm (fun j hj => hstop j hj.le) hfail
  obtain ⟨h1, h2, -⟩ := h.step_of_le hstop
  have hpos : 0 < ‖s (i + m)‖ := norm_pos_iff.2 (h.s_ne_zero hstop)
  have hU := lemma_3_4_8 hf h (i + m) fun j hj => hstop j hj.le
  have hLU : σL (i + m) ≤ σU (i + m) := by
    have := h1.trans h2
    exact le_of_mul_le_mul_right this hpos
  have hγ := P.one_lt_γ₁
  have key : P.γ₁ ^ (m - 1) ≤ sigmaUMax P L / P.σmin := by
    rw [le_div_iff₀ P.σmin_pos]; linarith
  have hlog := Real.log_le_log (by positivity) key
  rw [Real.log_pow] at hlog
  have hl1 := Real.log_pos hγ
  unfold irnUnsuccBound
  rw [← sub_le_iff_le_add, le_div_iff₀ hl1]
  have : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by rw [Nat.cast_sub hm]; simp
  rw [this] at hlog
  linarith

/-- The final block of unsuccessful iterations before termination: if iterations
`i, …, i + m - 1` are unsuccessful and none of the iterations `j < i + m` terminates, then
`m ≤ log(σᵁ_max/σ_min)/log γ₁ + 2`. -/
theorem lemma_3_4_10_last (hf : AssumptionHL f L)
    (h : algorithm_3_4_2 f P ε₁ ε₂ x s lam σL σU V) {i m : ℕ}
    (hstop : ∀ j < i + m, ¬ irnTest f ε₁ ε₂ (x j) (V j))
    (hfail : ∀ l, i ≤ l → l < i + m → irnRatio f (x l) (s l) < P.η) :
    (m : ℝ) ≤ irnUnsuccBound P L + 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [CharP.cast_eq_zero]; linarith [one_le_irnUnsuccBound P L]
  have hσL := irn_sigmaL_ge h m hm hstop hfail
  -- the last unsuccessful iteration bounds `σᴸ_{i+m} ≤ γ₁ σᵁ_max`
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hl : ∀ j ≤ i + m', ¬ irnTest f ε₁ ε₂ (x j) (V j) := fun j hj => hstop j (by omega)
  obtain ⟨-, u2, u3⟩ := h.update (i + m') hl
  have hs := hfail (i + m') (by omega) (by omega)
  have hU := lemma_3_4_8 hf h (i + m') fun j hj => hl j hj.le
  have hγ := P.one_lt_γ₁
  have hσU := sigmaUMax_pos P L
  have hup : σL (i + (m' + 1)) ≤ P.γ₁ * sigmaUMax P L := by
    rw [show i + (m' + 1) = i + m' + 1 by ring]
    by_cases hlt : lam (i + m') < P.σmin * ‖s (i + m')‖
    · refine (u2 hs hlt).2.1.trans ?_
      have : P.σmax ≤ sigmaUMax P L := le_max_left _ _
      nlinarith
    · rw [(u3 hs (not_lt.1 hlt)).1]
      obtain ⟨-, h2, -⟩ := h.step_of_le hl
      have hpos : 0 < ‖s (i + m')‖ := norm_pos_iff.2 (h.s_ne_zero hl)
      have : lam (i + m') / ‖s (i + m')‖ ≤ sigmaUMax P L := by
        rw [div_le_iff₀ hpos]; nlinarith
      nlinarith
  have key : P.γ₁ ^ m' ≤ P.γ₁ * (sigmaUMax P L / P.σmin) := by
    rw [mul_div_assoc', le_div_iff₀ P.σmin_pos]
    simp only [add_tsub_cancel_right] at hσL
    linarith
  have hlog := Real.log_le_log (by positivity) key
  rw [Real.log_pow, Real.log_mul (by positivity) (by have := P.σmin_pos; positivity)] at hlog
  have hl1 := Real.log_pos hγ
  unfold irnUnsuccBound
  push_cast
  have : (m' : ℝ) ≤ 1 + Real.log (sigmaUMax P L / P.σmin) / Real.log P.γ₁ := by
    rw [← sub_le_iff_le_add', le_div_iff₀ hl1]; linarith
  linarith

end IRNLemmas

/-! ### Theorems 3.4.11 and 3.4.12 -/

/-- `t³ ≥ 2√2 ε^{3/2} / C^{3/2}` whenever `t² ≥ 2ε/C` (`t, ε ≥ 0`, `C > 0`). -/
theorem rpow_three_halves_div_le {t C ε : ℝ} (ht : 0 ≤ t) (hC : 0 < C) (hε : 0 ≤ ε)
    (h : 2 / C * ε ≤ t ^ 2) : ε ^ (3 / 2 : ℝ) / (C ^ (3 / 2 : ℝ) / (2 * √2)) ≤ t ^ 3 := by
  have h3 : (t ^ 2) ^ (3 / 2 : ℝ) = t ^ 3 := by
    rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht]; norm_num
  have h2 : (2 : ℝ) ^ (3 / 2 : ℝ) = 2 * √2 := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one,
      Real.sqrt_eq_rpow]
  have hm := Real.rpow_le_rpow (by positivity) h (by norm_num : (0 : ℝ) ≤ 3 / 2)
  rw [h3, Real.mul_rpow (by positivity) hε, Real.div_rpow (by norm_num) hC.le, h2] at hm
  have : 0 < C ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hC _
  calc ε ^ (3 / 2 : ℝ) / (C ^ (3 / 2 : ℝ) / (2 * √2)) =
      2 * √2 / C ^ (3 / 2 : ℝ) * ε ^ (3 / 2 : ℝ) := by field_simp
    _ ≤ t ^ 3 := hm

/-- The constant `κ^S_iRN = (L_{f,2} + 4 σᵁ_max + 2κ₃)^{3/2}/(2√2 η)` (Appendix B). -/
noncomputable def kappaSIRN (P : IRNParams) (L : ℝ) : ℝ :=
  (L + 4 * sigmaUMax P L + 2 * P.κ₃) ^ (3 / 2 : ℝ) / (2 * √2) / P.η

/-- The corrected constant `κ^A_iRN = κ^S_iRN (log(σᵁ_max/σ_min)/log γ₁ + 2)`. -/
noncomputable def kappaAIRN (P : IRNParams) (L : ℝ) : ℝ :=
  kappaSIRN P L * (irnUnsuccBound P L + 1)

/-- The corrected constant `κ^B_iRN = 2(log(σᵁ_max/σ_min)/log γ₁ + 1) + 3`. -/
noncomputable def kappaBIRN (P : IRNParams) (L : ℝ) : ℝ := 2 * irnUnsuccBound P L + 3

/-- The constant `κ^T_iRN = η⁻¹ max((L + 4σᵁ_max + 2κ₃)^{3/2}/(2√2), (κ₄ + σᵁ_max)³)`
(Appendix B). -/
noncomputable def kappaTIRN (P : IRNParams) (L : ℝ) : ℝ :=
  P.η⁻¹ * max ((L + 4 * sigmaUMax P L + 2 * P.κ₃) ^ (3 / 2 : ℝ) / (2 * √2))
    ((P.κ₄ + sigmaUMax P L) ^ 3)

/-- The corrected constant `κ^C_iRN = κ^T_iRN (log(σᵁ_max/σ_min)/log γ₁ + 2)`. -/
noncomputable def kappaCIRN (P : IRNParams) (L : ℝ) : ℝ :=
  kappaTIRN P L * (irnUnsuccBound P L + 1)

section IRNTheorems

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : IRNParams} {ε₁ : ℝ} {ε₂ : Option ℝ}
  {x s : ℕ → EuclideanSpace ℝ (Fin n)} {lam σL σU : ℕ → ℝ}
  {V : ℕ → Submodule ℝ (EuclideanSpace ℝ (Fin n))} {L flow : ℝ}

/-- The iterate is unchanged between a successful iteration `j` and the next successful one. -/
private theorem irn_x_eq (h : algorithm_3_4_2 f P ε₁ ε₂ x s lam σL σU V) {j j' : ℕ}
    (hstop : ∀ i < j', ¬ irnTest f ε₁ ε₂ (x i) (V i))
    (hnone : ∀ i, j < i → i < j' → ¬ P.η ≤ irnRatio f (x i) (s i)) :
    ∀ m, j + 1 ≤ m → m ≤ j' → x m = x (j + 1) := by
  intro m hm hmj
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    rw [h.eq_self (fun i hi => hstop i (by omega)) (not_le.1 (hnone m (by omega) (by omega))),
      ih (by omega)]

/-- The counting of iRN iterations: if `|𝒮_k| ≤ N` before termination, then the run terminates
at some `k_ε` with `#f ≤ (M + 1) N + M + 2` and `#∇f ≤ N + 1`, where `M` is the bound (3.4.42) on
blocks of unsuccessful iterations (Lemma 3.4.10; the final block may have one more). -/
private theorem irn_count (hf : AssumptionHL f L) (h : algorithm_3_4_2 f P ε₁ ε₂ x s lam σL σU V)
    {N : ℝ} (hN : 0 ≤ N)
    (hsucc : ∀ k, (∀ j ≤ k, ¬ irnTest f ε₁ ε₂ (x j) (V j)) →
      ((successSet (fun j => P.η ≤ irnRatio f (x j) (s j)) k).card : ℝ) ≤ N) :
    ∃ kε, IsFirstHit (fun k => irnTest f ε₁ ε₂ (x k) (V k)) kε ∧
      (funEvalCount kε : ℝ) ≤ (irnUnsuccBound P L + 1) * N + irnUnsuccBound P L + 2 ∧
      (derivEvalCount (fun k => P.η ≤ irnRatio f (x k) (s k)) kε : ℝ) ≤ N + 1 := by
  classical
  set succ := fun k => P.η ≤ irnRatio f (x k) (s k)
  set M := irnUnsuccBound P L
  have hM := one_le_irnUnsuccBound P L
  have hD : ∀ k, (derivEvalCount succ (k + 1) : ℝ) =
      derivEvalCount succ k + if succ k then 1 else 0 := by
    intro k
    rw [derivEvalCount_eq_count, derivEvalCount_eq_count, Nat.count_succ]
    split_ifs <;> push_cast <;> ring
  -- the invariant
  have inv : ∀ k, (∀ j < k, ¬ irnTest f ε₁ ε₂ (x j) (V j)) → ∃ u ≤ k,
      (∀ l, k - u ≤ l → l < k → ¬ succ l) ∧
      (k : ℝ) ≤ (M + 1) * ((derivEvalCount succ k : ℝ) - 1) + u := by
    intro k
    induction k with
    | zero => intro _; exact ⟨0, le_rfl, fun l _ hl => absurd hl (Nat.not_lt_zero _), by simp⟩
    | succ k ih =>
      intro hk
      obtain ⟨u, hu, hblock, hbound⟩ := ih fun j hj => hk j (hj.trans k.lt_succ_self)
      by_cases hs : succ k
      · have hu' := lemma_3_4_10 (i := k - u) (m := u) hf h
          (fun j hj => hk j (by omega)) fun l hl hl' => not_le.1 (hblock l hl (by omega))
        refine ⟨0, Nat.zero_le _, fun l hl hl' => by omega, ?_⟩
        rw [hD, ite_eq_left hs]
        push_cast
        nlinarith
      · refine ⟨u + 1, by omega, fun l hl hl' => ?_, ?_⟩
        · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 hl') with hl' | rfl
          · exact hblock l (by omega) hl'
          · exact hs
        · rw [hD, ite_eq_right hs]
          push_cast
          linarith
  have hbd : ∀ K, (∀ j < K, ¬ irnTest f ε₁ ε₂ (x j) (V j)) →
      (K : ℝ) ≤ (M + 1) * N + M + 1 ∧ (derivEvalCount succ K : ℝ) ≤ N + 1 := by
    intro K hK
    obtain ⟨u, hu, hblock, hbound⟩ := inv K hK
    have hu' := lemma_3_4_10_last (i := K - u) (m := u) hf h (fun j hj => hK j (by omega))
      fun l hl hl' => not_le.1 (hblock l hl (by omega))
    have hDK : (derivEvalCount succ K : ℝ) ≤ N + 1 := by
      cases K with
      | zero => simp [hN]
      | succ k =>
        rw [derivEvalCount_add_one]
        push_cast
        linarith [hsucc k fun j hj => hK j (Nat.lt_succ_of_le hj)]
    refine ⟨?_, hDK⟩
    have : (M + 1) * ((derivEvalCount succ K : ℝ) - 1) ≤ (M + 1) * N :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  have hex : ∃ k, irnTest f ε₁ ε₂ (x k) (V k) := by
    by_contra hne
    push Not at hne
    have := (hbd (⌊(M + 1) * N + M + 1⌋₊ + 1) fun j _ => hne j).1
    push_cast at this
    linarith [Nat.lt_floor_add_one ((M + 1) * N + M + 1)]
  obtain ⟨kε, hkε⟩ := exists_isFirstHit hex
  obtain ⟨h1, h2⟩ := hbd kε fun j hj => hkε.not_test_of_lt hj
  refine ⟨kε, hkε, ?_, h2⟩
  rw [funEvalCount_eq]
  push_cast
  linarith

/-- **Theorem 3.4.11** of [cartis2022evaluation] (proof in Appendix B), **corrected constants**.
Under f.Bb and f.HL, every iRN run with `ε₂ = ∞` terminates at an iteration `k_ε` with
`‖∇f(x_{k_ε})‖ ≤ ε₁` after at most `κ^A (f(x₀) - f_low)/ε₁^{3/2} + κ^B` evaluations of `f` and at
most `κ^S (f(x₀) - f_low)/ε₁^{3/2} + 2` evaluations of `∇f` and `∇²f` (3.4.43)–(3.4.44), with
`κ^S = (L_{f,2} + 4σᵁ_max + 2κ₃)^{3/2}/(2√2 η)`, `κ^A = κ^S (M + 1)` and `κ^B = 2M + 3`, where
`M = log(σᵁ_max/σ_min)/log γ₁ + 1` is the bound (3.4.42). Correction: the appendix multiplies the
bound on successful iterations by `M`, which does not count the successful iterations themselves
nor the final block of unsuccessful iterations (which may have `M + 1` elements); the book's
`κ^A = κ^S M`, `κ^B = 2M` are replaced accordingly. -/
theorem theorem_3_4_11 (hb : Chapter02.AssumptionBb f flow) (hf : AssumptionHL f L)
    (h : algorithm_3_4_2 f P ε₁ none x s lam σL σU V) :
    ∃ kε, IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε₁) kε ∧
      (funEvalCount kε : ℝ) ≤ kappaAIRN P L * (f (x 0) - flow) / ε₁ ^ (3 / 2 : ℝ) +
        kappaBIRN P L ∧
      (derivEvalCount (fun k => P.η ≤ irnRatio f (x k) (s k)) kε : ℝ) ≤
        kappaSIRN P L * (f (x 0) - flow) / ε₁ ^ (3 / 2 : ℝ) + 2 := by
  have hε := h.ε₁_pos
  set C := L + 4 * sigmaUMax P L + 2 * P.κ₃
  have hC : 0 < C := by linarith [hf.nonneg, sigmaUMax_pos P L, P.κ₃_pos]
  have ha : 0 < C ^ (3 / 2 : ℝ) / (2 * √2) := by
    have := Real.rpow_pos_of_pos hC (3 / 2 : ℝ); positivity
  have hη := P.η_pos
  have hε32 : 0 < ε₁ ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hε _
  set X := (f (x 0) - flow) / ε₁ ^ (3 / 2 : ℝ)
  have hX : 0 ≤ X := div_nonneg (sub_nonneg.2 (hb _)) hε32.le
  set N := kappaSIRN P L * X
  have hN : 0 ≤ N := mul_nonneg (by unfold kappaSIRN; positivity) hX
  have hsucc : ∀ k, (∀ j ≤ k + 1, ¬ irnTest f ε₁ none (x j) (V j)) →
      ((successSet (fun j => P.η ≤ irnRatio f (x j) (s j)) k).card : ℝ) ≤ N := by
    intro k hk
    have hc : 0 < P.η * (ε₁ ^ (3 / 2 : ℝ) / (C ^ (3 / 2 : ℝ) / (2 * √2))) := by positivity
    have := card_successSet_le_div_of_decrease (φ := fun j => f (x j)) hc
      (fun j hj hs => by
        rw [h.eq_self (fun i hi => hk i (hi.trans (hj.trans k.le_succ))) (not_le.1 hs)])
      (fun j hj hs => by
        have hj' : ∀ i ≤ j, ¬ irnTest f ε₁ none (x i) (V i) := fun i hi =>
          hk i (hi.trans (hj.trans k.le_succ))
        have hG : ε₁ < ‖gradient f (x (j + 1))‖ := by
          by_contra hle
          exact hk (j + 1) (Nat.succ_le_succ hj) ⟨not_lt.1 hle, by simp⟩
        have h9 := lemma_3_4_9 hf h hj' hs
        have ht := rpow_three_halves_div_le (norm_nonneg (s j)) hC hε.le
          ((mul_le_mul_of_nonneg_left hG.le (by positivity)).trans h9)
        exact (mul_le_mul_of_nonneg_left ht hη.le).trans (h.sub_ge hj' hs))
      (hb (x (k + 1)))
    refine this.trans_eq ?_
    simp only [N, X, kappaSIRN]
    field_simp
    rfl
  obtain ⟨kε, hk, hF, hD⟩ := irn_count hf h (by linarith)
    (card_successSet_le_add_one_of_forall hN hsucc)
  have hk' : IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε₁) kε :=
    ⟨hk.test.1, fun j hj hg => hk.not_test_of_lt hj ⟨hg, by simp⟩⟩
  have hNe : N = kappaSIRN P L * (f (x 0) - flow) / ε₁ ^ (3 / 2 : ℝ) := by
    simp only [N, X]; ring
  refine ⟨kε, hk', hF.trans_eq ?_, hD.trans_eq (by rw [hNe]; ring)⟩
  simp only [kappaAIRN, kappaBIRN, hNe]
  ring

/-- **Theorem 3.4.12** of [cartis2022evaluation] (proof in Appendix B), **corrected constants**.
Under f.Bb and f.HL, every iRN run with `ε₁, ε₂ ∈ (0, 1]` (`ε₂ < ∞`) terminates at an iteration
`k_ε` with `‖∇f(x_{k_ε})‖ ≤ ε₁` and `λ_min[Q_{k_ε}ᵀ ∇²f(x_{k_ε}) Q_{k_ε}] ≥ -ε₂`, after at most
`2 κ^C (f(x₀) - f_low)/min(ε₁^{3/2}, ε₂³) + κ^D` evaluations of `f` and at most
`2 κ^T (f(x₀) - f_low)/min(ε₁^{3/2}, ε₂³) + 2` evaluations of `∇f` and `∇²f`, with `κ^T` as in the
appendix, `κ^C = κ^T (M + 1)` and `κ^D = 2M + 3` (`M` the bound (3.4.42)). Corrections: the
appendix's claim "`‖∇f(x_k)‖ ≤ ε₁` for all `k ≥ k₁`" is unjustified (the gradient may grow
again); instead, every successful iteration lacking the required decrease is followed by one with
decrease `≥ κ₆ ε₂³`, whence the factor `2`; the count of all iterations also includes the
successful ones and the final block (as in Theorem 3.4.11). -/
theorem theorem_3_4_12 (hb : Chapter02.AssumptionBb f flow) (hf : AssumptionHL f L) {e : ℝ}
    (h : algorithm_3_4_2 f P ε₁ (some e) x s lam σL σU V) :
    ∃ kε, IsFirstHit (fun k => irnTest f ε₁ (some e) (x k) (V k)) kε ∧
      (funEvalCount kε : ℝ) ≤
        2 * kappaCIRN P L * (f (x 0) - flow) / min (ε₁ ^ (3 / 2 : ℝ)) (e ^ 3) +
          (2 * irnUnsuccBound P L + 3) ∧
      (derivEvalCount (fun k => P.η ≤ irnRatio f (x k) (s k)) kε : ℝ) ≤
        2 * kappaTIRN P L * (f (x 0) - flow) / min (ε₁ ^ (3 / 2 : ℝ)) (e ^ 3) + 2 := by
  have hε := h.ε₁_pos
  have he := h.ε₂_pos e rfl
  set C := L + 4 * sigmaUMax P L + 2 * P.κ₃
  have hC : 0 < C := by linarith [hf.nonneg, sigmaUMax_pos P L, P.κ₃_pos]
  set a := C ^ (3 / 2 : ℝ) / (2 * √2)
  have ha : 0 < a := by have := Real.rpow_pos_of_pos hC (3 / 2 : ℝ); positivity
  set b := (P.κ₄ + sigmaUMax P L) ^ 3
  have hκσ : 0 < P.κ₄ + sigmaUMax P L := by linarith [P.κ₄_pos, sigmaUMax_pos P L]
  have hb' : 0 < b := by positivity
  have hη := P.η_pos
  have hε32 : 0 < ε₁ ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hε _
  set m := min (ε₁ ^ (3 / 2 : ℝ)) (e ^ 3)
  have hm : 0 < m := lt_min hε32 (by positivity)
  set X := (f (x 0) - flow) / m
  have hX : 0 ≤ X := div_nonneg (sub_nonneg.2 (hb _)) hm.le
  set N := kappaTIRN P L * X
  have hκT : kappaTIRN P L = P.η⁻¹ * max a b := rfl
  have hN : 0 ≤ N := mul_nonneg (by rw [hκT]; positivity) hX
  set succ := fun j => P.η ≤ irnRatio f (x j) (s j)
  have hsucc : ∀ k, (∀ j ≤ k, ¬ irnTest f ε₁ (some e) (x j) (V j)) →
      ((successSet succ k).card : ℝ) ≤ 2 * N + 1 := by
    intro k hk
    set good := fun j => succ j ∧
      (minCurvatureOn (iteratedFDeriv ℝ 2 f (x j)) (V j) < -e ∨
        ε₁ < ‖gradient f (x (j + 1))‖)
    have hcard := card_successSet_le_two_mul_add_one (succ := succ) (good := good) (K := k)
      (fun j _ hg => hg.1) (fun j j' hjj' hj'k hsj hgj hsj' hnone => by
        refine ⟨hsj', Or.inl ?_⟩
        have hstop : ∀ i < j', ¬ irnTest f ε₁ (some e) (x i) (V i) := fun i hi => hk i (by omega)
        have hx := irn_x_eq h hstop hnone j' (by omega) le_rfl
        have hg : ‖gradient f (x (j + 1))‖ ≤ ε₁ := by
          by_contra hlt
          exact hgj ⟨hsj, Or.inr (not_le.1 hlt)⟩
        by_contra hge
        exact hk j' hj'k ⟨by rw [hx]; exact hg, fun e' he' => by
          simp only [Option.mem_def, Option.some.injEq] at he'
          subst he'
          exact not_lt.1 hge⟩) k le_rfl
    have hc : 0 < m / (P.η⁻¹ * max a b) := by positivity
    have hG := card_le_div_of_decrease (φ := fun j => f (x j)) (T := successSet good k) hc
      successSet_subset_range (fun j hj => h.le fun i hi => hk i (hi.trans hj))
      (fun j hj => by
        rw [mem_successSet] at hj
        obtain ⟨hjk, hsj, hgj⟩ := hj
        have hj' : ∀ i ≤ j, ¬ irnTest f ε₁ (some e) (x i) (V i) := fun i hi => hk i (hi.trans hjk)
        refine le_trans ?_ (h.sub_ge hj' hsj)
        have hmax : 0 < max a b := lt_max_of_lt_left ha
        rw [div_eq_mul_inv, mul_inv, inv_inv]
        have hT : m / max a b ≤ ‖s j‖ ^ 3 := by
          rcases hgj with hl | hgr
          · have h9 := lemma_3_4_9_curv hf h (by simp) hj'
            have hse : e / (P.κ₄ + sigmaUMax P L) ≤ ‖s j‖ :=
              (div_le_div_of_nonneg_right (by linarith) hκσ.le).trans h9
            have h3 := pow_le_pow_left₀ (by positivity) hse 3
            rw [div_pow] at h3
            calc m / max a b ≤ e ^ 3 / b :=
                  div_le_div₀ (by positivity) (min_le_right _ _) hb' (le_max_right _ _)
              _ ≤ _ := h3
          · have h9 := lemma_3_4_9 hf h hj' hsj
            have ht := rpow_three_halves_div_le (norm_nonneg (s j)) hC hε.le
              ((mul_le_mul_of_nonneg_left hgr.le (by positivity)).trans h9)
            calc m / max a b ≤ ε₁ ^ (3 / 2 : ℝ) / a :=
                  div_le_div₀ hε32.le (min_le_left _ _) ha (le_max_left _ _)
              _ ≤ _ := ht
        calc m * (P.η * (max a b)⁻¹) = P.η * (m / max a b) := by ring
          _ ≤ P.η * ‖s j‖ ^ 3 := mul_le_mul_of_nonneg_left hT hη.le)
      (hb (x (k + 1)))
    have : ((successSet succ k).card : ℝ) ≤ 2 * (successSet good k).card + 1 := by
      exact_mod_cast hcard
    have hGN : ((successSet good k).card : ℝ) ≤ N := by
      refine hG.trans_eq ?_
      simp only [N, X, hκT]
      field_simp
    linarith
  obtain ⟨kε, hk, hF, hD⟩ := irn_count hf h (by linarith) hsucc
  have hNe : N = kappaTIRN P L * (f (x 0) - flow) / m := by simp only [N, X]; ring
  refine ⟨kε, hk, hF.trans_eq ?_, hD.trans_eq (by rw [hNe]; ring)⟩
  simp only [kappaCIRN, hNe]
  ring

end IRNTheorems

/-! ### Existence of iRN runs -/

section IRNExistence

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {y : EuclideanSpace ℝ (Fin n)}

/-- A global minimizer `s` of the cubic model `T_{f,2}(y, s) + σ/3 ‖s‖³` (`σ ∈ [σᴸ, σᵁ]`,
`σ > 0`) with `λ = σ ‖s‖` and `Q = I` (`V = ⊤`) satisfies Step 2 of Algorithm 3.4.2. -/
theorem irnStep_of_isMinOn (hf : ContDiffAt ℝ 2 f y) (P : IRNParams) (ε₂ : Option ℝ)
    {σL σU σ : ℝ} {s : EuclideanSpace ℝ (Fin n)} (hσ : 0 < σ) (hσL : σL ≤ σ) (hσU : σ ≤ σU)
    (hmin : IsMinOn (regModel (gradient f y) (hessianOperator f y) σ 3) univ s) :
    irnStep f P ε₂ y σL σU (σ * ‖s‖) ⊤ s ∧ irnGrad f y (σ * ‖s‖) s = 0 := by
  have hsym := hessianOperator_isSymmetric hf
  obtain ⟨hshift, hpos⟩ := (isMinOn_regModel_iff hsym hσ (by norm_num)).1 hmin
  have h1 : ‖s‖ ^ ((3 : ℝ) - 2) = ‖s‖ := by norm_num
  rw [h1] at hshift hpos
  have h2 : hessianOperator f y s + (σ * ‖s‖) • s = -gradient f y := by
    simpa using hshift
  have hg : irnGrad f y (σ * ‖s‖) s = 0 := by
    rw [irnGrad, add_assoc, h2, add_neg_cancel]
  have hpsd : ∀ d, 0 ≤ ⟪d, hessianOperator f y d⟫ + σ * ‖s‖ * ‖d‖ ^ 2 := fun d => by
    have := hpos.inner_nonneg_right d
    simp only [ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul,
      LinearMap.add_apply,
      LinearMap.smul_apply, ContinuousLinearMap.coe_coe, one_apply_eq_self, inner_add_right,
      inner_smul_right, real_inner_self_eq_norm_sq] at this
    exact this
  have hn := norm_nonneg s
  refine ⟨⟨mul_le_mul_of_nonneg_right hσL hn, mul_le_mul_of_nonneg_right hσU hn, ?_, ?_,
    fun _ => ?_⟩, hg⟩
  · rw [hg, inner_zero_right]
    refine le_min (by have := P.κ₁_pos; positivity) ?_
    have := hpsd s
    rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
    have := P.κ₂_pos
    have : 0 ≤ 1 / 2 * P.κ₂ * ‖s‖ ^ 3 := by positivity
    nlinarith
  · rw [hg, norm_zero]
    have := P.κ₃_pos
    positivity
  · refine le_minCurvatureOn (by have := P.κ₄_pos; nlinarith) fun d _ => ?_
    simp only [add_apply, smul_apply, innerForm_apply_diag, smul_eq_mul]
    rw [apply_diag_eq_vec, ← inner_hessianOperator_apply hf]
    have := hpsd d
    have : -(P.κ₄ * ‖s‖) * ‖d‖ ^ 2 ≤ 0 := by
      have := P.κ₄_pos; have : 0 ≤ P.κ₄ * ‖s‖ * ‖d‖ ^ 2 := by positivity
      linarith
    linarith

/-- **Existence of iRN runs** ([cartis2022evaluation], Algorithm 3.4.2): for `C²` `f`, every
`ε₁ ∈ (0, 1]`, `ε₂ > 0` (or `∞`) and every starting point there is an iRN run, with `Q_k = I`
(`V k = ⊤`), `s_k` a global minimizer of the cubic model `T_{f,2}(x_k, s) + σᵁ_k/3 ‖s‖³` and
`λ_k = σᵁ_k ‖s_k‖`. -/
theorem exists_algorithm_3_4_2 (hf : ContDiff ℝ 2 f) (P : IRNParams) {ε₁ : ℝ} {ε₂ : Option ℝ}
    (hε₁ : 0 < ε₁) (hε₁1 : ε₁ ≤ 1) (hε₂ : ∀ e ∈ ε₂, 0 < e) (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∃ (x s : ℕ → EuclideanSpace ℝ (Fin n)) (lam σL σU : ℕ → ℝ), x 0 = x₀ ∧
      algorithm_3_4_2 f P ε₁ ε₂ x s lam σL σU (fun _ => ⊤) := by
  classical
  let S : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n) := fun y σ =>
    if h : 0 < σ then (exists_isMinOn_regModel (gradient f y) (hessianOperator f y) h
      (by norm_num : (2 : ℝ) < 3)).choose else 0
  have hS : ∀ y σ, 0 < σ →
      IsMinOn (regModel (gradient f y) (hessianOperator f y) σ 3) univ (S y σ) := fun y σ h => by
    simp only [S, h, dite_true]
    exact (exists_isMinOn_regModel (gradient f y) (hessianOperator f y) h
      (by norm_num : (2 : ℝ) < 3)).choose_spec
  -- states `(x_k, σᴸ_k, σᵁ_k)`
  let inv : EuclideanSpace ℝ (Fin n) × ℝ × ℝ → Prop := fun a =>
    0 ≤ a.2.1 ∧ a.2.1 ≤ a.2.2 ∧ 0 < a.2.2
  have hstepOK : ∀ a, inv a → irnStep f P ε₂ a.1 a.2.1 a.2.2 (a.2.2 * ‖S a.1 a.2.2‖) ⊤
      (S a.1 a.2.2) ∧ irnGrad f a.1 (a.2.2 * ‖S a.1 a.2.2‖) (S a.1 a.2.2) = 0 :=
    fun a ha => irnStep_of_isMinOn hf.contDiffAt P ε₂ ha.2.2 ha.2.1 le_rfl (hS _ _ ha.2.2)
  have hne : ∀ a, inv a → ¬ irnTest f ε₁ ε₂ a.1 ⊤ → S a.1 a.2.2 ≠ 0 := by
    intro a ha hnot h0
    obtain ⟨⟨-, -, -, -, h5⟩, hg⟩ := hstepOK a ha
    rw [irnGrad, h0, map_zero, add_zero, smul_zero, add_zero] at hg
    refine hnot ⟨by rw [hg, norm_zero]; exact hε₁.le, fun e he => ?_⟩
    have := h5 (by rintro rfl; simp at he)
    rw [h0, norm_zero, mul_zero, mul_zero, neg_zero, zero_smul, add_zero] at this
    linarith [hε₂ e he]
  let next : EuclideanSpace ℝ (Fin n) × ℝ × ℝ → EuclideanSpace ℝ (Fin n) × ℝ × ℝ := fun a =>
    let s := S a.1 a.2.2
    let l := a.2.2 * ‖s‖
    (if P.η ≤ irnRatio f a.1 s then a.1 + s else a.1,
      if P.η ≤ irnRatio f a.1 s then (0, a.2.2)
      else if l < P.σmin * ‖s‖ then (P.σmin, P.σmax) else (P.γ₁ * (l / ‖s‖), P.γ₂ * (l / ‖s‖)))
  have hnext : ∀ a, inv a → ¬ irnTest f ε₁ ε₂ a.1 ⊤ → inv (next a) ∧
      irnUpdate P (irnRatio f a.1 (S a.1 a.2.2)) (a.2.2 * ‖S a.1 a.2.2‖) (S a.1 a.2.2) a.2.2
        (next a).2.1 (next a).2.2 := by
    intro a ha hnot
    have hpos : 0 < ‖S a.1 a.2.2‖ := norm_pos_iff.2 (hne a ha hnot)
    have hγ := P.one_lt_γ₁
    have hγ2 := P.γ₁_le_γ₂
    by_cases hs : P.η ≤ irnRatio f a.1 (S a.1 a.2.2)
    · simp only [next, hs, ite_true]
      exact ⟨⟨le_rfl, ha.1.trans ha.2.1, ha.2.2⟩, fun _ => ⟨rfl, rfl⟩,
        fun h => absurd h (not_lt.2 hs), fun h => absurd h (not_lt.2 hs)⟩
    · simp only [next, hs, ite_false]
      by_cases hl : a.2.2 * ‖S a.1 a.2.2‖ < P.σmin * ‖S a.1 a.2.2‖
      · simp only [hl, ite_true]
        exact ⟨⟨P.σmin_pos.le, P.σmin_le_σmax, P.σmin_pos.trans_le P.σmin_le_σmax⟩,
          fun h => absurd h hs, fun _ _ => ⟨le_rfl, P.σmin_le_σmax, P.σmin_le_σmax, le_rfl⟩,
          fun _ h => absurd h (not_le.2 hl)⟩
      · simp only [hl, ite_false]
        have hd : a.2.2 * ‖S a.1 a.2.2‖ / ‖S a.1 a.2.2‖ = a.2.2 := by field_simp
        refine ⟨⟨?_, ?_, ?_⟩, fun h => absurd h hs, fun _ h => absurd h hl,
          fun _ _ => ⟨rfl, rfl⟩⟩ <;> rw [hd]
        · exact mul_nonneg (by linarith) ha.2.2.le
        · exact mul_le_mul_of_nonneg_right hγ2 ha.2.2.le
        · exact mul_pos (by linarith) ha.2.2
  obtain ⟨r, hr0, hr⟩ := exists_run_of_forall_exists_of_invariant
    (α := EuclideanSpace ℝ (Fin n) × ℝ × ℝ) (init := fun a => a = (x₀, 0, P.σU₀))
    (inv := fun _ a => inv a) (stop := fun _ a => irnTest f ε₁ ε₂ a.1 ⊤)
    (step := fun _ a b => b = next a ∧ inv b ∧ irnUpdate P (irnRatio f a.1 (S a.1 a.2.2))
      (a.2.2 * ‖S a.1 a.2.2‖) (S a.1 a.2.2) a.2.2 b.2.1 b.2.2)
    ⟨_, rfl⟩ (fun a ha => by
      subst ha
      exact ⟨le_rfl, P.σmin_pos.le.trans P.σmin_le_σU₀, P.σmin_pos.trans_le P.σmin_le_σU₀⟩)
    (fun k a ha hnot => ⟨next a, (hnext a ha hnot).1, rfl, hnext a ha hnot⟩)
  have hinv : ∀ k, (∀ j < k, ¬ irnTest f ε₁ ε₂ (r j).1 ⊤) → inv (r k) := by
    intro k hk
    cases k with
    | zero => rw [hr0]; exact ⟨le_rfl, P.σmin_pos.le.trans P.σmin_le_σU₀,
        P.σmin_pos.trans_le P.σmin_le_σU₀⟩
    | succ k => exact (hr k fun j hj => hk j (Nat.lt_succ_of_le hj)).2.2.1
  refine ⟨fun k => (r k).1, fun k => S (r k).1 (r k).2.2,
    fun k => (r k).2.2 * ‖S (r k).1 (r k).2.2‖,
    fun k => (r k).2.1, fun k => (r k).2.2, by simp only [hr0], hε₁, hε₁1, hε₂,
    by simp only [hr0], by simp only [hr0], fun k hk _ => (hstepOK _ (hinv k hk)).1,
    fun k hk => ?_, fun k hk => ?_⟩
  · obtain ⟨hb, -, -⟩ := (hr k hk).2
    rw [hb]
  · exact (hr k hk).2.2.2

end IRNExistence

/-! ### One-dimensional examples (for Corollary 3.5.5) -/

section Examples

open Chapter02 (e₀ norm_e₀ inner_e₀_smul)

variable {G : ℝ → ℝ}

theorem tr2Model_ridge (hG : ContDiff ℝ 2 G) (y : EuclideanSpace ℝ (Fin 1)) (t : ℝ) :
    tr2Model (ridge G e₀) y (t • e₀) =
      G ⟪e₀, y⟫ + deriv G ⟪e₀, y⟫ * t + iteratedDeriv 2 G ⟪e₀, y⟫ * t ^ 2 / 2 := by
  rw [tr2Model_eq_taylorPolynomial (contDiff_ridge hG).contDiffAt, taylorPolynomial_two_ridge hG,
    inner_e₀_smul]

theorem treModel_ridge (hG : ContDiff ℝ 2 G) (εs : ℝ) (y : EuclideanSpace ℝ (Fin 1)) (t : ℝ) :
    treModel (ridge G e₀) εs y (t • e₀) =
      G ⟪e₀, y⟫ + deriv G ⟪e₀, y⟫ * t + iteratedDeriv 2 G ⟪e₀, y⟫ * t ^ 2 / 2 +
        εs / 2 * t ^ 2 := by
  rw [treModel_def, tr2Model_ridge hG, norm_smul, norm_e₀, mul_one, Real.norm_eq_abs, sq_abs]

theorem norm_gradient_ridge_e₀ (hG : ContDiff ℝ 2 G) (y : EuclideanSpace ℝ (Fin 1)) :
    ‖gradient (ridge G e₀) y‖ = |deriv G ⟪e₀, y⟫| := by
  rw [gradient_ridge (hG.differentiable (by norm_num)), norm_smul, norm_e₀, mul_one,
    Real.norm_eq_abs]

/-- The model gradient of a ridge function along `e₀`:
`∇f(y) + (∇²f(y) + λ I)(t e₀) = (G'(a) + (G''(a) + λ) t) e₀`. -/
theorem irnGrad_ridge (hG : ContDiff ℝ 2 G) (y : EuclideanSpace ℝ (Fin 1)) (l t : ℝ) :
    irnGrad (ridge G e₀) y l (t • e₀) =
      (deriv G ⟪e₀, y⟫ + (iteratedDeriv 2 G ⟪e₀, y⟫ + l) * t) • e₀ := by
  rw [irnGrad, gradient_ridge (hG.differentiable (by norm_num)), hessianOperator_ridge hG,
    smul_smul, smul_smul, ← add_smul, ← add_smul]
  ring_nf

theorem norm_fderiv_treModel_ridge (hG : ContDiff ℝ 2 G) (εs : ℝ) (y : EuclideanSpace ℝ (Fin 1))
    (t : ℝ) : ‖fderiv ℝ (treModel (ridge G e₀) εs y) (t • e₀)‖ =
      |deriv G ⟪e₀, y⟫ + (iteratedDeriv 2 G ⟪e₀, y⟫ + εs) * t| := by
  rw [norm_fderiv_treModel (contDiff_ridge hG).contDiffAt]
  have := irnGrad_ridge hG y εs (t • e₀ |> fun _ => t)
  rw [irnGrad] at this
  rw [this, norm_smul, norm_e₀, mul_one, Real.norm_eq_abs]

/-- Facts on `k_ε = ⌈ε^{-3/2}⌉`: `k ε^{3/2} < 1` for `k < k_ε`, and `1 ≤ k_ε ε^{3/2} ≤ 2`. -/
theorem ceil_rpow_facts {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∀ k < ⌈ε ^ (-(3 / 2 : ℝ))⌉₊, (k : ℝ) * ε ^ (3 / 2 : ℝ) < 1) ∧
      1 ≤ (⌈ε ^ (-(3 / 2 : ℝ))⌉₊ : ℝ) * ε ^ (3 / 2 : ℝ) ∧
      (⌈ε ^ (-(3 / 2 : ℝ))⌉₊ : ℝ) * ε ^ (3 / 2 : ℝ) ≤ 2 := by
  have he : 0 < ε ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hε _
  have he1 : ε ^ (3 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hε.le hε1 (by norm_num)
  have hneg : ε ^ (-(3 / 2 : ℝ)) = (ε ^ (3 / 2 : ℝ))⁻¹ := Real.rpow_neg hε.le _
  rw [hneg]
  refine ⟨fun k hk => ?_, ?_, ?_⟩
  · have h2 := mul_lt_mul_of_pos_right (Nat.lt_ceil.1 hk) he
    rwa [inv_mul_cancel₀ he.ne'] at h2
  · have h2 := mul_le_mul_of_nonneg_right (Nat.le_ceil (ε ^ (3 / 2 : ℝ))⁻¹) he.le
    rwa [inv_mul_cancel₀ he.ne'] at h2
  · have := Nat.ceil_lt_add_one (inv_nonneg.2 he.le)
    have h2 := mul_lt_mul_of_pos_right this he
    rw [add_mul, inv_mul_cancel₀ he.ne'] at h2
    linarith

/-- **The TRε example of Corollary 3.5.5** ([cartis2022evaluation], (3.5.12)). There are
`f_low`, `L₁ ≥ 1`, `L₂ ≥ 1` and `B` such that for all TRε constants and every `ε ∈ (0, 1)` with
`√ε < Δ₀` there are `f : ℝ¹ → ℝ` satisfying f.Bb, f.gL, f.HL with these constants and `|f| ≤ B`,
and a TRε run with `ε_* = √ε`, `ε₂ = ∞` from `x₀ = 0` which terminates exactly at iteration
`⌈ε^{-3/2}⌉`. The run has `Δ_k = Δ₀`, interior steps `s_k = 2√ε f_k/(4f_k² + 1)` (the exact
minimizers of the model (3.4.1), step factors `θ_k = 4f_k²/(4f_k² + 1)`) and `ρ_k ≥ 1`. -/
theorem tre_slow_example :
    ∃ flow L₁ L₂ B : ℝ, 1 ≤ L₁ ∧ 1 ≤ L₂ ∧ ∀ (P : TREpsParams) (ε : ℝ), 0 < ε → ε < 1 →
      √ε < P.Δ₀ → ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, Chapter02.AssumptionBb f flow ∧
        Chapter02.AssumptionGL f L₁ ∧ AssumptionHL f L₂ ∧ (∀ y, |f y| ≤ B) ∧
        ∃ (x s : ℕ → EuclideanSpace ℝ (Fin 1)) (Δ : ℕ → ℝ), x 0 = 0 ∧
          algorithm_3_4_1 f P ε none (√ε) x s Δ ∧
          IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) ⌈ε ^ (-(3 / 2 : ℝ))⌉₊ := by
  obtain ⟨L, B, hL, hB, H⟩ := exists_slowSecondOrder_interpolant (a := 1 / 2) (b := 1)
    (by norm_num) (by norm_num)
  refine ⟨-B, max B 1, max L 1, B, le_max_right _ _, le_max_right _ _,
    fun P ε hε hε1 hΔ₀ => ?_⟩
  set K := ⌈ε ^ (-(3 / 2 : ℝ))⌉₊
  obtain ⟨hKlt, hKge, hKle⟩ := ceil_rpow_facts hε hε1.le
  set r := √ε with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hε
  have hr2 : r ^ 2 = ε := Real.sq_sqrt hε.le
  have hhalf : ε ^ (1 / 2 : ℝ) = r := by rw [hr, Real.sqrt_eq_rpow]
  have h32 : ε ^ (3 / 2 : ℝ) = r ^ 3 := by
    rw [hr, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hε.le]; norm_num
  set F : ℕ → ℝ := fun k => 1 - k * ε ^ (3 / 2 : ℝ) / 2
  set θ : ℕ → ℝ := fun k => 4 * F k ^ 2 / (4 * F k ^ 2 + 1)
  set X : ℕ → ℝ := fun k => ∑ j ∈ range k, θ j * ε ^ (1 / 2 : ℝ) / (2 * F j)
  have hF : ∀ k < K, 1 / 2 < F k ∧ F k ≤ 1 := fun k hk => by
    have := hKlt k hk
    have : 0 ≤ (k : ℝ) * ε ^ (3 / 2 : ℝ) := by positivity
    simp only [F]; constructor <;> linarith
  have hFK : 0 ≤ F K ∧ F K ≤ 1 / 2 := by simp only [F]; constructor <;> linarith
  have hθ : ∀ k < K, θ k ∈ Icc (1 / 2 : ℝ) 1 := fun k hk => by
    obtain ⟨h1, -⟩ := hF k hk
    have hd : 0 < 4 * F k ^ 2 + 1 := by positivity
    simp only [θ, Set.mem_Icc]
    constructor
    · rw [le_div_iff₀ hd]; nlinarith
    · rw [div_le_one hd]; linarith
  have hX : ∀ k < K,
      X (k + 1) = X k + θ k * ε ^ (1 / 2 : ℝ) / (2 * (1 - k * ε ^ (3 / 2 : ℝ) / 2)) :=
    fun k _ => by simp [X, F, sum_range_succ]
  obtain ⟨G, hG, hGL, hGB, hGk⟩ := H ε θ X hε hε1.le hθ hX
  obtain ⟨hb, hgl, -, hhl, hgrad⟩ := ridge_assumptions_two hG hGL hGB
  set f := ridge G e₀
  set x : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => X k • e₀
  set t : ℕ → ℝ := fun k => θ k * r / (2 * F k)
  set s : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => t k • e₀
  have hxe : ∀ k, ⟪e₀, x k⟫ = X k := fun k => inner_e₀_smul _
  have hval : ∀ k ≤ K, G (X k) = F k ∧ deriv G (X k) = -2 * ε * F k ∧
      iteratedDeriv 2 G (X k) = 4 * r * F k ^ 2 := fun k hk => by
    obtain ⟨h1, h2, h3⟩ := hGk k hk
    exact ⟨h1, h2, by rw [h3, hhalf]⟩
  have hnorm : ∀ k ≤ K, ‖gradient f (x k)‖ = 2 * ε * F k := fun k hk => by
    rw [norm_gradient_ridge_e₀ hG, hxe, (hval k hk).2.1]
    have : 0 ≤ F k := by
      rcases lt_or_eq_of_le hk with h | rfl
      · linarith [(hF k h).1]
      · exact hFK.1
    rw [show -2 * ε * F k = -(2 * ε * F k) by ring, abs_neg, abs_of_nonneg (by positivity)]
  have hhit : IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) K := by
    refine ⟨?_, fun j hj => ?_⟩
    · simp only; rw [hnorm K le_rfl]; nlinarith [hFK.2]
    · simp only; rw [hnorm j hj.le, not_le]; nlinarith [(hF j hj).1]
  have hbefore : ∀ k, (∀ j ≤ k, ¬ stopTest f ε none (x j)) → k < K := fun k hk =>
    not_le.1 fun hle => hk K hle (stopTest_none.2 hhit.test)
  have hstepx : ∀ k < K, x (k + 1) = x k + s k := fun k hk => by
    simp only [x, s, t]
    rw [hX k hk, add_smul, hhalf]
  -- the step facts at iteration `k < K`
  have hpos : ∀ k < K, 0 < t k := fun k hk => by
    have := (hF k hk).1; have := (hθ k hk).1; simp only [t]; positivity
  have hstat : ∀ k < K, -2 * ε * F k + (4 * r * F k ^ 2 + r) * t k = 0 := fun k hk => by
    have := (hF k hk).1
    simp only [t, θ]
    rw [← hr2]
    field_simp
    ring
  have hstep : ∀ k < K, treStep f P r none (x k) P.Δ₀ (s k) := fun k hk => by
    have hFk := hF k hk
    have htk := hpos k hk
    obtain ⟨hv1, hv2, hv3⟩ := hval k hk.le
    have hst := hstat k hk
    have hts : ‖s k‖ = t k := by
      simp only [s]; rw [norm_smul, norm_e₀, mul_one, Real.norm_of_nonneg htk.le]
    have hsmall : t k ≤ r / 2 := by
      have hd : 0 < 4 * F k ^ 2 + 1 := by positivity
      have e : t k = r * (2 * F k / (4 * F k ^ 2 + 1)) := by
        simp only [t, θ]; field_simp; ring
      have h2 : 2 * F k / (4 * F k ^ 2 + 1) ≤ 1 / 2 := by
        rw [div_le_iff₀ hd]; nlinarith [sq_nonneg (2 * F k - 1)]
      rw [e]
      nlinarith
    refine ⟨by rw [hts]; linarith, ?_, fun _ => ?_, fun e he => by simp at he⟩
    · have hfx : f (x k) = F k := by simp only [f, ridge_apply, hxe]; exact hv1
      rw [treModel_zero, treModel_ridge hG, hxe, hv1, hv2, hv3, hfx]
      have : (4 * r * F k ^ 2 + r) * t k = 2 * ε * F k := by linarith
      nlinarith [mul_pos htk (mul_pos (mul_pos two_pos hε) (by linarith [hFk.1] : 0 < F k))]
    · rw [norm_fderiv_treModel_ridge hG, hxe, hv2, hv3, hst, abs_zero]
      have := P.θ₁_pos
      positivity
  have hρ : ∀ k < K, 1 ≤ tr2Ratio f (x k) (s k) := fun k hk => by
    have hFk := hF k hk
    have htk := hpos k hk
    obtain ⟨hv1, hv2, hv3⟩ := hval k hk.le
    obtain ⟨hw1, -, -⟩ := hval (k + 1) hk
    have hθk := hθ k hk
    rw [tr2Ratio, Chapter02.tr1Ratio]
    have hpred : Chapter02.tr1Model f (x k) (hessianOperator f (x k)) 0 -
        Chapter02.tr1Model f (x k) (hessianOperator f (x k)) (s k) =
        r ^ 3 * (θ k - θ k ^ 2 / 2) := by
      have e1 := tr2Model_ridge hG (x k) 0
      have e2 := tr2Model_ridge hG (x k) (t k)
      rw [zero_smul] at e1
      unfold tr2Model at e1 e2
      rw [e1, e2, hxe, hv2, hv3, ← hr2]
      have hF0 : F k ≠ 0 := by linarith [hFk.1]
      simp only [t]
      field_simp
      ring
    refine one_le_reductionRatio
      (by rw [hpred]; exact mul_pos (pow_pos hr0 3) (by nlinarith [hθk.1, hθk.2])) ?_
    rw [hpred, ← hstepx k hk]
    simp only [f, ridge_apply, hxe]
    rw [hv1, hw1]
    simp only [F]
    rw [h32]
    push_cast
    nlinarith [mul_nonneg (pow_pos hr0 3).le (sq_nonneg (1 - θ k))]
  refine ⟨f, hb, hgl, hhl, fun y => ?_, x, s, fun _ => P.Δ₀, by simp [x, X], ?_, hhit⟩
  · have := hGB 0 (by norm_num) ⟪e₀, y⟫
    rwa [iteratedDeriv_zero] at this
  refine ⟨hε, hε1.le, fun e he => by simp at he, hr0, ?_, hΔ₀, rfl,
    fun k hk => hstep k (hbefore k hk), fun k hk => ?_⟩
  · rw [Real.sqrt_le_one]; exact hε1.le
  · have hk' := hbefore k hk
    dsimp only
    rw [hstepx k hk']
    exact trAcceptance_of_one_le P.toTRParams (hρ k hk') _ _ P.Δ₀_pos.le


private theorem irn_alg {c r F θ q σ : ℝ} (hF : F ≠ 0) (hq : q * (8 * c * F ^ 3) = σ)
    (hθ : θ + q * θ ^ 2 = 1) :
    -2 * (c * r ^ 2) * F + (c * (4 * r * F ^ 2) + σ * (θ * r / (2 * F))) * (θ * r / (2 * F)) =
      0 := by
  rw [← hq]
  have e1 : c * (4 * r * F ^ 2) * (θ * r / (2 * F)) = 2 * c * r ^ 2 * F * θ := by
    field_simp; ring
  have e2 : q * (8 * c * F ^ 3) * (θ * r / (2 * F)) * (θ * r / (2 * F)) =
      2 * c * r ^ 2 * F * (q * θ ^ 2) := by
    field_simp; ring
  rw [add_mul, e1, e2]
  linear_combination (2 * c * r ^ 2 * F) * hθ

private theorem irn_ratio_alg {c r F θ η : ℝ} (hr : 0 < r) (hF : 1 / 2 < F) (hθ0 : 0 < θ)
    (hθ1 : θ ≤ 1) (hη : 2 * η ≤ c) (hη0 : 0 < η) : η * (θ * r / (2 * F)) ^ 3 ≤ c * r ^ 3 / 2 := by
  have hF0 : 0 < F := by linarith
  have e : (θ * r / (2 * F)) ^ 3 = θ ^ 3 * r ^ 3 / (8 * F ^ 3) := by field_simp; ring
  have hF3 : 1 < 8 * F ^ 3 := by
    have := pow_lt_pow_left₀ hF (by norm_num) (by norm_num : (3 : ℕ) ≠ 0); norm_num at this
    linarith
  have hθ3 : θ ^ 3 ≤ 1 := pow_le_one₀ hθ0.le hθ1
  have hr3 := pow_pos hr 3
  rw [e]
  have h1 : θ ^ 3 * r ^ 3 / (8 * F ^ 3) ≤ r ^ 3 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  nlinarith

set_option maxHeartbeats 400000 in
-- the proof elaborates many local definitions (`set`) in one declaration
/-- **The iRN example of Corollary 3.5.5** ([cartis2022evaluation], (3.5.12), rescaled). For all
iRN constants there are `f_low`, `L₁ ≥ 1`, `L₂ ≥ 1` and `B` such that for every `ε ∈ (0, 1)`
there are `f : ℝ¹ → ℝ` satisfying f.Bb, f.gL, f.HL with these constants and `|f| ≤ B`, and an
iRN run with `ε₂ = ∞` (`Q_k = I`, `σᴸ_k = 0`, `σᵁ_k = σ₀ᵁ`, `λ_k = σ₀ᵁ ‖s_k‖`, `s_k` the exact
minimizer of the cubic model, all iterations successful) from `x₀ = 0` which terminates exactly at
iteration `⌈(ε/c)^{-3/2}⌉ ≥ ⌈ε^{-3/2}⌉`, where `c = max(1, 2η)` (so exactly at `⌈ε^{-3/2}⌉` when
`η ≤ ½`). The function is `c` times the function of (3.5.12) for the tolerance `ε/c`: the ratio
(3.4.35) is not scale invariant and equals `4 c f_k³/θ_k³ > c/2` on these data, so the factor `c`
is needed when `η > ½`. -/
theorem irn_slow_example (P : IRNParams) :
    ∃ flow L₁ L₂ B : ℝ, 1 ≤ L₁ ∧ 1 ≤ L₂ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, Chapter02.AssumptionBb f flow ∧
        Chapter02.AssumptionGL f L₁ ∧ AssumptionHL f L₂ ∧ (∀ y, |f y| ≤ B) ∧
        ∃ (x s : ℕ → EuclideanSpace ℝ (Fin 1)) (lam σL σU : ℕ → ℝ), x 0 = 0 ∧
          algorithm_3_4_2 f P ε none x s lam σL σU (fun _ => ⊤) ∧
          IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε)
            ⌈(ε / max 1 (2 * P.η)) ^ (-(3 / 2 : ℝ))⌉₊ ∧
          ⌈ε ^ (-(3 / 2 : ℝ))⌉₊ ≤ ⌈(ε / max 1 (2 * P.η)) ^ (-(3 / 2 : ℝ))⌉₊ := by
  set σ := P.σU₀
  have hσ : 0 < σ := P.σmin_pos.trans_le P.σmin_le_σU₀
  set c := max 1 (2 * P.η)
  have hc1 : 1 ≤ c := le_max_left _ _
  have hc0 : 0 < c := by linarith
  have hcη : 2 * P.η ≤ c := le_max_right _ _
  obtain ⟨L, B, hL, hB, H⟩ := exists_slowSecondOrder_interpolant (a := 1 / (1 + σ)) (b := 1)
    (by positivity) (by rw [div_le_one (by linarith)]; linarith)
  refine ⟨-(c * B), max (c * B) 1, max (c * L) 1, c * B, le_max_right _ _, le_max_right _ _,
    fun ε hε hε1 => ?_⟩
  set ε' := ε / c
  have hε' : 0 < ε' := div_pos hε hc0
  have hε'1 : ε' ≤ 1 := by rw [div_le_one hc0]; linarith
  have hεε : ε = c * ε' := by simp only [ε']; field_simp
  set K := ⌈ε' ^ (-(3 / 2 : ℝ))⌉₊
  obtain ⟨hKlt, hKge, hKle⟩ := ceil_rpow_facts hε' hε'1
  set r := √ε' with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hε'
  have hr2 : r ^ 2 = ε' := Real.sq_sqrt hε'.le
  have hhalf : ε' ^ (1 / 2 : ℝ) = r := by rw [hr, Real.sqrt_eq_rpow]
  have h32 : ε' ^ (3 / 2 : ℝ) = r ^ 3 := by
    rw [hr, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hε'.le]; norm_num
  set F : ℕ → ℝ := fun k => 1 - k * ε' ^ (3 / 2 : ℝ) / 2
  set q : ℕ → ℝ := fun k => σ / (8 * c * F k ^ 3)
  set θ : ℕ → ℝ := fun k => 2 / (1 + √(1 + 4 * q k))
  set X : ℕ → ℝ := fun k => ∑ j ∈ range k, θ j * ε' ^ (1 / 2 : ℝ) / (2 * F j)
  have hF : ∀ k < K, 1 / 2 < F k ∧ F k ≤ 1 := fun k hk => by
    have := hKlt k hk
    have : 0 ≤ (k : ℝ) * ε' ^ (3 / 2 : ℝ) := by positivity
    simp only [F]; constructor <;> linarith
  have hFK : 0 ≤ F K ∧ F K ≤ 1 / 2 := by simp only [F]; constructor <;> linarith
  -- the step factors solve `θ + q θ² = 1` and lie in `[1/(1+σ), 1]`
  have hθq : ∀ k < K, 0 < q k ∧ q k ≤ σ ∧ θ k + q k * θ k ^ 2 = 1 ∧ 0 < θ k ∧ θ k ≤ 1 ∧
      1 / (1 + σ) ≤ θ k := fun k hk => by
    obtain ⟨h1, -⟩ := hF k hk
    have hF3 : 1 / 8 < F k ^ 3 := by
      have := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num : (3 : ℕ) ≠ 0); norm_num at this
      linarith
    have hq0 : 0 < q k := by simp only [q]; positivity
    have hqσ : q k ≤ σ := by
      have h8 : 1 ≤ 8 * c * F k ^ 3 := by nlinarith
      simp only [q]; rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left h8 hσ.le]
    set u := √(1 + 4 * q k)
    have hu2 : u ^ 2 = 1 + 4 * q k := Real.sq_sqrt (by linarith)
    have hu0 : 0 ≤ u := Real.sqrt_nonneg _
    have hu1 : 1 ≤ u := by nlinarith
    have hu3 : u ≤ 1 + 2 * q k := by nlinarith
    have hθ : θ k = 2 / (1 + u) := rfl
    refine ⟨hq0, hqσ, ?_, by rw [hθ]; positivity, ?_, ?_⟩
    · rw [hθ]; field_simp; nlinarith
    · rw [hθ, div_le_one (by linarith)]; linarith
    · rw [hθ, div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
  have hθ : ∀ k < K, θ k ∈ Icc (1 / (1 + σ)) 1 := fun k hk =>
    ⟨(hθq k hk).2.2.2.2.2, (hθq k hk).2.2.2.2.1⟩
  have hX : ∀ k < K,
      X (k + 1) = X k + θ k * ε' ^ (1 / 2 : ℝ) / (2 * (1 - k * ε' ^ (3 / 2 : ℝ) / 2)) :=
    fun k _ => by simp [X, F, sum_range_succ]
  obtain ⟨G, hG, hGL, hGB, hGk⟩ := H ε' θ X hε' hε'1 hθ hX
  set G' : ℝ → ℝ := fun t => c * G t
  have hG' : ContDiff ℝ 2 G' := contDiff_const.mul hG
  have hid : ∀ j t, iteratedDeriv j G' t = c * iteratedDeriv j G t := fun j t =>
    iteratedDeriv_const_mul_field c G
  have hG'L : ∀ a b, |iteratedDeriv 2 G' a - iteratedDeriv 2 G' b| ≤ c * L * |a - b| := by
    intro a b
    rw [hid, hid, ← mul_sub, abs_mul, abs_of_pos hc0, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hGL a b) hc0.le
  have hG'B : ∀ j ≤ 2, ∀ t, |iteratedDeriv j G' t| ≤ c * B := fun j hj t => by
    rw [hid, abs_mul, abs_of_pos hc0]
    exact mul_le_mul_of_nonneg_left (hGB j hj t) hc0.le
  obtain ⟨hb, hgl, -, hhl, -⟩ := ridge_assumptions_two hG' hG'L hG'B
  set f := ridge G' e₀
  set x : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => X k • e₀
  set t : ℕ → ℝ := fun k => θ k * r / (2 * F k)
  set s : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => t k • e₀
  have hxe : ∀ k, ⟪e₀, x k⟫ = X k := fun k => inner_e₀_smul _
  have hval : ∀ k ≤ K, G' (X k) = c * F k ∧ deriv G' (X k) = -2 * ε * F k ∧
      iteratedDeriv 2 G' (X k) = c * (4 * r * F k ^ 2) := fun k hk => by
    obtain ⟨h1, h2, h3⟩ := hGk k hk
    have hd : deriv G' (X k) = c * deriv G (X k) := by
      have := hid 1 (X k); simpa [iteratedDeriv_one] using this
    refine ⟨by simp only [G']; rw [h1], by rw [hd, h2, hεε]; ring, by rw [hid, h3, hhalf]⟩
  have hnorm : ∀ k ≤ K, ‖gradient f (x k)‖ = 2 * ε * F k := fun k hk => by
    rw [norm_gradient_ridge_e₀ hG', hxe, (hval k hk).2.1]
    have : 0 ≤ F k := by
      rcases lt_or_eq_of_le hk with h | rfl
      · linarith [(hF k h).1]
      · exact hFK.1
    rw [show -2 * ε * F k = -(2 * ε * F k) by ring, abs_neg, abs_of_nonneg (by positivity)]
  have hhit : IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) K := by
    refine ⟨?_, fun j hj => ?_⟩
    · simp only; rw [hnorm K le_rfl]; nlinarith [hFK.2]
    · simp only; rw [hnorm j hj.le, not_le]; nlinarith [(hF j hj).1]
  have hstepx : ∀ k < K, x (k + 1) = x k + s k := fun k hk => by
    simp only [x, s, t]
    rw [hX k hk, add_smul, hhalf]
  have htest : ∀ k, (∀ j ≤ k, ¬ irnTest f ε none (x j) ⊤) → k < K := fun k hk =>
    not_le.1 fun hle => hk K hle ⟨hhit.test, by simp⟩
  -- the step facts at iteration `k < K`
  have hpos : ∀ k < K, 0 < t k := fun k hk => by
    have := (hF k hk).1; have := (hθq k hk).2.2.2.1; simp only [t]; positivity
  have hgrad0 : ∀ k < K, irnGrad f (x k) (σ * ‖s k‖) (s k) = 0 := fun k hk => by
    have hFk := (hF k hk).1
    obtain ⟨-, -, hθe, -, -, -⟩ := hθq k hk
    obtain ⟨-, hv2, hv3⟩ := hval k hk.le
    have hts : ‖s k‖ = t k := by
      simp only [s]; rw [norm_smul, norm_e₀, mul_one, Real.norm_of_nonneg (hpos k hk).le]
    have hF0 : F k ≠ 0 := by linarith
    have hq : q k * (8 * c * F k ^ 3) = σ := by
      simp only [q]; field_simp
    rw [hts, irnGrad_ridge hG', hxe, hv2, hv3, hεε, ← hr2]
    simp only [t]
    rw [irn_alg hF0 hq hθe, zero_smul]
  have hstep : ∀ k < K, irnStep f P none (x k) 0 σ (σ * ‖s k‖) ⊤ (s k) := fun k hk => by
    have hg := hgrad0 k hk
    obtain ⟨-, -, hv3⟩ := hval k hk.le
    have hts : ‖s k‖ = t k := by
      simp only [s]; rw [norm_smul, norm_e₀, mul_one, Real.norm_of_nonneg (hpos k hk).le]
    have htk := hpos k hk
    have hFk := (hF k hk).1
    refine ⟨by rw [zero_mul]; positivity, le_rfl, ?_, ?_, fun h => absurd rfl h⟩
    · rw [hg, inner_zero_right]
      refine le_min (by have := P.κ₁_pos; positivity) ?_
      have hH : ⟪s k, hessianOperator f (x k) (s k) + (σ * ‖s k‖) • s k⟫ =
          (c * (4 * r * F k ^ 2) + σ * t k) * t k ^ 2 := by
        simp only [s]
        rw [hessianOperator_ridge hG', hxe, hv3, hts, smul_smul, smul_smul, ← add_smul,
          inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq, norm_e₀]
        simp only [conj_trivial]
        ring
      rw [hH, hts]
      have := P.κ₂_pos
      have : 0 ≤ (c * (4 * r * F k ^ 2) + σ * t k) * t k ^ 2 := by positivity
      have : 0 ≤ 1 / 2 * P.κ₂ * t k ^ 3 := by positivity
      linarith
    · rw [hg, norm_zero, hts]
      have := P.κ₃_pos
      positivity
  have hρ : ∀ k < K, P.η ≤ irnRatio f (x k) (s k) := fun k hk => by
    have htk := hpos k hk
    have hFk := hF k hk
    obtain ⟨-, -, -, hθ0, hθ1, -⟩ := hθq k hk
    obtain ⟨hv1, -, -⟩ := hval k hk.le
    obtain ⟨hw1, -, -⟩ := hval (k + 1) hk
    have hts : ‖s k‖ = t k := by
      simp only [s]; rw [norm_smul, norm_e₀, mul_one, Real.norm_of_nonneg htk.le]
    have hp : 0 < ‖s k‖ ^ 3 := pow_pos (hts ▸ htk) 3
    change P.η ≤ reductionRatio f (x k) (s k) (‖s k‖ ^ 3)
    rw [le_reductionRatio_iff hp, ← hstepx k hk, hts]
    have hfx : ∀ j, f (x j) = G' (X j) := fun j => by simp only [f, ridge_apply, hxe]
    rw [hfx, hfx, hv1, hw1]
    have hFs : F (k + 1) = F k - r ^ 3 / 2 := by
      simp only [F]; push_cast; rw [h32]; ring
    rw [hFs]
    have := irn_ratio_alg hr0 hFk.1 hθ0 hθ1 hcη P.η_pos
    simp only [t]
    linarith
  refine ⟨f, hb, hgl, hhl, fun y => ?_, x, s, fun k => σ * ‖s k‖, fun _ => 0, fun _ => σ,
    by simp only [x, X, Finset.range_zero, Finset.sum_empty, zero_smul], ?_, hhit, ?_⟩
  · have := hG'B 0 (by norm_num) ⟪e₀, y⟫
    rwa [iteratedDeriv_zero] at this
  · refine ⟨hε, hε1.le, fun e he => by simp at he, rfl, rfl, fun k hk hn => ?_,
      fun k hk => ?_, fun k hk => ?_⟩
    · have hk' : k < K := by
        rcases lt_trichotomy k K with h | rfl | h
        · exact h
        · exact absurd hhit.test (hn rfl)
        · exact absurd ⟨hhit.test, by simp⟩ (hk K h)
      exact hstep k hk'
    · have hk' := htest k hk
      dsimp only
      rw [ite_eq_left (hρ k hk'), hstepx k hk']
    · have hk' := htest k hk
      exact ⟨fun _ => ⟨rfl, rfl⟩, fun h => absurd (hρ k hk') (not_le.2 h),
        fun h => absurd (hρ k hk') (not_le.2 h)⟩
  · refine Nat.ceil_mono (Real.rpow_le_rpow_of_nonpos hε' ?_ (by norm_num))
    simp only [ε']; exact div_le_self hε.le hc1

end Examples

end CartisGouldToint.Chapter03

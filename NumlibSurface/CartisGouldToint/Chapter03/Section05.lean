import Numlib.Optimization.Complexity.ZeroChain
import Numlib.Optimization.ModelBased.TaylorModel
import NumlibSurface.CartisGouldToint.Chapter02.Section02
import NumlibSurface.CartisGouldToint.Chapter03.Section03
import NumlibSurface.CartisGouldToint.Chapter03.Section04

/-!
# Cartis–Gould–Toint §3.5: Optimal complexity for methods using second derivatives

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §§3.5.1–3.5.2 and the
corresponding proofs of Appendix B (Lemmas 3.5.1–3.5.3, Theorem 3.5.4), and Corollary 3.5.5, on
`ℝⁿ = EuclideanSpace ℝ (Fin n)`.

## Main definitions

* `IsMClassEquation f x s lam r` — the linear system (3.5.2) `(∇²f(x) + λ I) s = -∇f(x) + r`.
* `IsMClassStepWith f κrg κrs κlam x s lam r`, `IsMClassStep f κrg κrs κlam x s` — the conditions
  (3.5.2)–(3.5.4) on one step `s ≠ 0` from `x`, with given or existential `λ`, `r`.
* `IsMClassMethod κrg κrs κlam M f ε` — a deterministic second-order oracle method
  `M : Optimization.OracleMethod ℝⁿ (Optimization.Jet ℝⁿ 2)` (its iterates are functions of
  `f(x_i), ∇f(x_i), ∇²f(x_i)` at the previous iterates) is in the class `𝓜` on `f`: every step
  `s_k = x_{k+1} - x_k` (3.5.1) before the first `k` with `‖∇f(x_k)‖ ≤ ε` satisfies
  (3.5.2)–(3.5.4).
* `ridgeJet` — the second-order jet of a ridge function on `ℝ¹` (the data (3.5.11)–(3.5.12) are
  `Optimization.secondOrderK`, `secondOrderF`, `secondOrderG`, `secondOrderH`).

## Main results

* `lemma_3_5_1`, `lemma_3_5_2`, `lemma_3_5_2_sqrt`, `lemma_3_5_3` — Lemmas 3.5.1–3.5.3.
* `exists_slowSecondOrder_ridge` — the one-dimensional function of the proof of Theorem 3.5.4,
  for arbitrary step factors `θ_k ∈ [a, b]` (also used for Corollary 3.5.5).
* `theorem_3_5_4` — Theorem 3.5.4: for every method in `𝓜` (from any starting point) there is a
  function satisfying f.Bb, f.gL and f.HL (constants independent of `ε₁`) on which the method
  terminates exactly at iteration `⌈ε₁^{-3/2}⌉`.
* `isMClassStepWith_ridge` — one-dimensional criterion for steps of class `𝓜` on ridge functions.
* `corollary_3_5_5_i`, `corollary_3_5_5_ii`, `corollary_3_5_5_iii` — Corollary 3.5.5 for AR2, TRε
  and iRN: runs whose steps are of class `𝓜` (constants independent of `ε₁`) terminating at
  `⌈ε₁^{-3/2}⌉`, matching the upper bounds of Theorems 3.3.5, 3.4.5, 3.4.11.

## Fixes and deviations with respect to the book

* **Lemma 3.5.1**: the printed constant `κ_λ = 2√(κ_λ(1 + κ_rg))` is self-referential; the proof
  (Appendix B) gives `κ_λ = 2√(κ̄_λ(1 + κ_rg))`, which is used. The lemma holds without (3.5.3),
  without `κ_rg < 1` and without `s ≠ 0` (only `κ_rg ≥ 0`, `κ̄_λ ≥ 1` are used).
* **Lemma 3.5.2**: f.Bb and f.gL are not needed. The proof gives `‖∇f(x⁺)‖ ≤ C ‖s‖²` with
  `C = L_{f,2}/2 + κ_rs + κ̄_λ`, hence `‖s‖ ≥ C^{-1/2} ‖∇f(x⁺)‖^{1/2}` (`lemma_3_5_2_sqrt`); the
  printed `κ̄_s = C⁻¹` follows since `C ≥ 1` (`lemma_3_5_2`).
* **Lemma 3.5.3**: f.Bb, f.HL and (3.5.1) are not needed (the hypotheses are stated about `x_k`,
  `x_{k+1}` directly).
* **Theorem 3.5.4**: the bound `|f| ≤ B` holds on all of `ℝ` (the book: `f(x) ∈ [a, b]` for
  `x ≥ 0`). The proof only uses the part `‖r_k‖ ≤ κ_rg ‖∇f(x_k)‖` of (3.5.2), which gives the step
  factors `θ_k ∈ [(1 - κ_rg)/κ_λ, 1 + κ_rg]` of (3.5.19) directly; the book's detour through the
  quadratic inequalities after (3.5.16) and the constant `κ_r` of (3.5.18) are not needed, and
  (3.5.17) has a sign typo (`s_k = +θ_k ε₁^{1/2}/(2f_k)`). The claim (3.5.13) `f_k ∈ [1/2, 1]` holds
  for `k < k_ε` only; `f_{k_ε} ∈ (0, 1/2]`, which is what makes `k_ε` the first termination
  index. Since the function depends on the method, the method's iterates on the data (3.5.12)
  are computed first (they depend only on the oracle answers), and the step factors are clipped
  to `[(1 - κ_rg)/κ_λ, 1 + κ_rg]`; for a method in `𝓜` the clipping is inactive.
* **Corollary 3.5.5**: the AR2 example is that of Theorem 3.3.6 (data of Theorem 12.2.15 with
  zero Hessians), not (3.5.12). For iRN the ratio (3.4.35) is not scale invariant and the data
  (3.5.12) are rescaled to `c G(x/c)`, `c = min(1, (2η)^{-1/2})` (which keeps the gradients and the
  termination index); the book's sketch omits this.
* The powers `‖∇f(x)‖^{1/2}` are written `√‖∇f(x)‖`; the positive semidefiniteness in (3.5.3) is
  `∇²f(x)[d, d] + λ ‖d‖² ≥ 0` for all `d`.
-/

open Set Finset Optimization
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter03

variable {n : ℕ}

/-! ### The class `𝓜` -/

/-- The linear system (3.5.2) of [cartis2022evaluation]: `(∇²f(x) + λ I) s = -∇f(x) + r`, i.e.
`∇²f(x)[s, v] + λ ⟪s, v⟫ = -⟪∇f(x), v⟫ + ⟪r, v⟫` for all `v`. -/
def IsMClassEquation (f : EuclideanSpace ℝ (Fin n) → ℝ) (x s : EuclideanSpace ℝ (Fin n))
    (lam : ℝ) (r : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ v, iteratedFDeriv ℝ 2 f x ![s, v] + lam * ⟪s, v⟫ = -⟪gradient f x, v⟫ + ⟪r, v⟫

/-- The conditions (3.5.2)–(3.5.4) of [cartis2022evaluation] on a step `s ≠ 0` from `x`, with
multiplier `λ` and residual `r`: the system (3.5.2) with
`‖r‖ ≤ min(κ_rg ‖∇f(x)‖, κ_rs ‖s‖²)`, `λ ≥ 0` and `∇²f(x) + λ I ⪰ 0` (3.5.3), and
`λ_min[∇²f(x)] + λ ≤ κ_λ max(|λ_min[∇²f(x)]|, ‖∇f(x)‖^{1/2})` (3.5.4). -/
structure IsMClassStepWith (f : EuclideanSpace ℝ (Fin n) → ℝ) (κrg κrs κlam : ℝ)
    (x s : EuclideanSpace ℝ (Fin n)) (lam : ℝ) (r : EuclideanSpace ℝ (Fin n)) : Prop where
  /-- The step is nonzero. -/
  ne_zero : s ≠ 0
  /-- The system (3.5.2). -/
  equation : IsMClassEquation f x s lam r
  /-- The residual bound of (3.5.2). -/
  residual : ‖r‖ ≤ min (κrg * ‖gradient f x‖) (κrs * ‖s‖ ^ 2)
  /-- `λ ≥ 0` (3.5.3). -/
  nonneg : 0 ≤ lam
  /-- `∇²f(x) + λ I` is positive semidefinite (3.5.3). -/
  psd : ∀ d, 0 ≤ iteratedFDeriv ℝ 2 f x (fun _ => d) + lam * ‖d‖ ^ 2
  /-- The bound (3.5.4). -/
  bound : Chapter01.hessianMinEig f x + lam ≤
    κlam * max |Chapter01.hessianMinEig f x| √‖gradient f x‖

/-- A step `s` from `x` is admissible for the class `𝓜` of [cartis2022evaluation] (§3.5.1):
(3.5.2)–(3.5.4) hold for some multiplier `λ` and residual `r`. -/
def IsMClassStep (f : EuclideanSpace ℝ (Fin n) → ℝ) (κrg κrs κlam : ℝ)
    (x s : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ lam r, IsMClassStepWith f κrg κrs κlam x s lam r

/-- A deterministic second-order oracle method `M` is in the **class `𝓜`** of
[cartis2022evaluation] (§3.5.1) on `f` with constants `κ_rg, κ_rs, κ_λ`: along its iterates
`x_k = M.iterate (jetOracle f 2) k`, every step `s_k = x_{k+1} - x_k` (3.5.1) taken before the
first `k` with `‖∇f(x_k)‖ ≤ ε` satisfies (3.5.2)–(3.5.4). -/
def IsMClassMethod (κrg κrs κlam : ℝ)
    (M : OracleMethod (EuclideanSpace ℝ (Fin n)) (Jet (EuclideanSpace ℝ (Fin n)) 2))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (ε : ℝ) : Prop :=
  UntilHit (fun k => ‖gradient f (M.iterate (jetOracle f 2) k)‖ ≤ ε) fun k =>
    IsMClassStep f κrg κrs κlam (M.iterate (jetOracle f 2) k)
      (M.iterate (jetOracle f 2) (k + 1) - M.iterate (jetOracle f 2) k)

/-! ### Lemmas 3.5.1–3.5.3 -/

section Lemmas

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {x s r : EuclideanSpace ℝ (Fin n)} {lam : ℝ}

/-- `|A[v, w]| ≤ ‖A‖ ‖v‖ ‖w‖` for a bilinear form. -/
private theorem abs_apply_vec_le
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => EuclideanSpace ℝ (Fin n)) ℝ)
    (v w : EuclideanSpace ℝ (Fin n)) : |A ![v, w]| ≤ ‖A‖ * ‖v‖ * ‖w‖ := by
  have := A.le_opNorm ![v, w]
  simpa [Fin.prod_univ_two, mul_assoc] using this

/-- The system (3.5.2) tested against `s`: `∇²f(x)[s, s] + λ ‖s‖² = ⟪-∇f(x) + r, s⟫`. -/
private theorem IsMClassEquation.apply_self (h : IsMClassEquation f x s lam r) :
    iteratedFDeriv ℝ 2 f x (fun _ => s) + lam * ‖s‖ ^ 2 = -⟪gradient f x, s⟫ + ⟪r, s⟫ := by
  rw [apply_diag_eq_vec, ← real_inner_self_eq_norm_sq]
  exact h s

/-- **Lemma 3.5.1** of [cartis2022evaluation] (bounded multiplier), with the **corrected
constant**. If `s, λ, r` satisfy the system (3.5.2) with `‖r‖ ≤ κ_rg ‖∇f(x)‖` (`κ_rg ≥ 0`) and
`λ ≤ κ̄_λ ‖s‖` (3.5.6) with `κ̄_λ ≥ 1`, then (3.5.4) holds with `κ_λ = 2√(κ̄_λ(1 + κ_rg))`:
`λ_min[∇²f(x)] + λ ≤ 2√(κ̄_λ(1 + κ_rg)) max(|λ_min[∇²f(x)]|, ‖∇f(x)‖^{1/2})`. (The book prints the
self-referential `κ_λ = 2√(κ_λ(1 + κ_rg))`; (3.5.3) is not needed.) -/
theorem lemma_3_5_1 {κrg κbar : ℝ} (hrg : 0 ≤ κrg) (hκ : 1 ≤ κbar)
    (heq : IsMClassEquation f x s lam r) (hr : ‖r‖ ≤ κrg * ‖gradient f x‖)
    (hlam : lam ≤ κbar * ‖s‖) :
    Chapter01.hessianMinEig f x + lam ≤
      2 * √(κbar * (1 + κrg)) * max |Chapter01.hessianMinEig f x| √‖gradient f x‖ := by
  set m := Chapter01.hessianMinEig f x
  set g := ‖gradient f x‖
  set c := κbar * (1 + κrg)
  have hc1 : 1 ≤ c := by nlinarith
  have hsc : 1 ≤ √c := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hc1
  set M := max |m| (√c * √g)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (le_max_left _ _)
  have hMsq : c * g ≤ M ^ 2 := by
    have h1 : √c * √g ≤ M := le_max_right _ _
    have h2 : (√c * √g) ^ 2 = c * g := by
      rw [mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt (norm_nonneg _)]
    nlinarith [mul_nonneg (Real.sqrt_nonneg c) (Real.sqrt_nonneg g)]
  have hMle : M ≤ √c * max |m| √g := by
    refine max_le ?_ ?_
    · calc |m| = 1 * |m| := (one_mul _).symm
        _ ≤ √c * max |m| √g := mul_le_mul hsc (le_max_left _ _) (abs_nonneg _) (by linarith)
    · exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith)
  -- `(λ_min + λ) ‖s‖² ≤ (1 + κ_rg) ‖∇f(x)‖ ‖s‖`
  have hkey : (m + lam) * ‖s‖ ^ 2 ≤ (1 + κrg) * g * ‖s‖ := by
    have h1 := heq.apply_self
    have h2 := minCurvature_mul_norm_sq_le (iteratedFDeriv ℝ 2 f x) s
    have h3 : -⟪gradient f x, s⟫ + ⟪r, s⟫ ≤ g * ‖s‖ + ‖r‖ * ‖s‖ := by
      have := real_inner_le_norm r s
      have := neg_le_of_abs_le (abs_real_inner_le_norm (gradient f x) s)
      linarith
    have h4 : ‖r‖ * ‖s‖ ≤ κrg * g * ‖s‖ := mul_le_mul_of_nonneg_right hr (norm_nonneg _)
    change m * ‖s‖ ^ 2 ≤ _ at h2
    nlinarith
  have hmain : m + lam ≤ 2 * M := by
    by_contra hcon
    push Not at hcon
    have hlamM : M < lam := by
      have := le_abs_self m
      have := le_max_left |m| (√c * √g)
      linarith
    have hs : 0 < ‖s‖ := by
      have : 0 < κbar * ‖s‖ := by linarith
      exact pos_of_mul_pos_right this (by linarith)
    have h1 : (m + lam) * ‖s‖ ≤ (1 + κrg) * g := by
      have := hkey
      rw [sq, ← mul_assoc] at this
      exact le_of_mul_le_mul_right this hs
    have h2 : (m + lam) * lam ≤ c * g := by
      have hpos : 0 ≤ m + lam := by linarith
      calc (m + lam) * lam ≤ (m + lam) * (κbar * ‖s‖) := mul_le_mul_of_nonneg_left hlam hpos
        _ = κbar * ((m + lam) * ‖s‖) := by ring
        _ ≤ κbar * ((1 + κrg) * g) := mul_le_mul_of_nonneg_left h1 (by linarith)
        _ = c * g := by ring
    nlinarith
  calc m + lam ≤ 2 * M := hmain
    _ ≤ 2 * (√c * max |m| √g) := by linarith
    _ = _ := by ring

/-- The gradient at the trial point for a step solving (3.5.2), under f.HL:
`‖∇f(x + s)‖ ≤ L/2 ‖s‖² + ‖r - λ s‖`. -/
private theorem norm_gradient_add_le_of_equation {L : ℝ} (hf : AssumptionHL f L)
    (heq : IsMClassEquation f x s lam r) :
    ‖gradient f (x + s)‖ ≤ L / 2 * ‖s‖ ^ 2 + ‖r - lam • s‖ := by
  have hfx := hf.contDiffAt x
  have hvec : gradient f x + hessianOperator f x s = r - lam • s := by
    refine ext_inner_right ℝ fun v => ?_
    have hsym := hessianOperator_isSymmetric hfx s v
    change ⟪hessianOperator f x s, v⟫ = ⟪s, hessianOperator f x v⟫ at hsym
    have h1 := heq v
    rw [← inner_hessianOperator_apply hfx] at h1
    rw [inner_add_left, hsym, inner_sub_left, inner_smul_left]
    simp only [conj_trivial]
    linarith
  rw [← hvec]
  exact norm_gradient_add_le hf

/-- **Lemma 3.5.2** of [cartis2022evaluation], sharp form. Under f.HL, if `s, λ, r` satisfy
(3.5.2) with `‖r‖ ≤ κ_rs ‖s‖²`, `0 ≤ λ ≤ κ̄_λ ‖s‖` (3.5.6), then with
`C = L_{f,2}/2 + κ_rs + κ̄_λ`: `‖∇f(x + s)‖ ≤ C ‖s‖²` and `‖s‖ ≥ C^{-1/2} ‖∇f(x + s)‖^{1/2}`.
(f.Bb and f.gL are not needed.) -/
theorem lemma_3_5_2_sqrt {L κrs κbar : ℝ} (hf : AssumptionHL f L) (hrs : 0 ≤ κrs)
    (hκ : 0 ≤ κbar) (heq : IsMClassEquation f x s lam r) (hr : ‖r‖ ≤ κrs * ‖s‖ ^ 2)
    (hlam0 : 0 ≤ lam) (hlam : lam ≤ κbar * ‖s‖) :
    ‖gradient f (x + s)‖ ≤ (L / 2 + κrs + κbar) * ‖s‖ ^ 2 ∧
      (√(L / 2 + κrs + κbar))⁻¹ * √‖gradient f (x + s)‖ ≤ ‖s‖ := by
  have h1 := norm_gradient_add_le_of_equation hf heq
  have h2 : ‖r - lam • s‖ ≤ (κrs + κbar) * ‖s‖ ^ 2 := by
    calc ‖r - lam • s‖ ≤ ‖r‖ + ‖lam • s‖ := norm_sub_le _ _
      _ = ‖r‖ + lam * ‖s‖ := by rw [norm_smul, Real.norm_of_nonneg hlam0]
      _ ≤ κrs * ‖s‖ ^ 2 + κbar * ‖s‖ * ‖s‖ := by gcongr
      _ = (κrs + κbar) * ‖s‖ ^ 2 := by ring
  have hgrad : ‖gradient f (x + s)‖ ≤ (L / 2 + κrs + κbar) * ‖s‖ ^ 2 := by nlinarith
  refine ⟨hgrad, ?_⟩
  have hC : 0 < L / 2 + κrs + κbar := by linarith [hf.one_le]
  rw [inv_mul_le_iff₀ (Real.sqrt_pos.2 hC)]
  calc √‖gradient f (x + s)‖ ≤ √((L / 2 + κrs + κbar) * ‖s‖ ^ 2) := Real.sqrt_le_sqrt hgrad
    _ = √(L / 2 + κrs + κbar) * ‖s‖ := by
      rw [Real.sqrt_mul hC.le, Real.sqrt_sq (norm_nonneg _)]

/-- **Lemma 3.5.2** of [cartis2022evaluation] (lower bound on the step), with the printed
constant. Under f.HL, if `s, λ, r` satisfy (3.5.2) with `‖r‖ ≤ κ_rs ‖s‖²` (`κ_rs ≥ 0`) and
`0 ≤ λ ≤ κ̄_λ ‖s‖` (3.5.6) with `κ̄_λ > 1`, then `‖s‖ ≥ κ̄_s ‖∇f(x + s)‖^{1/2}` (3.5.7) with
`κ̄_s = [L_{f,2}/2 + κ_rs + κ̄_λ]⁻¹`. (The sharper `C^{-1/2}` is `lemma_3_5_2_sqrt`.) -/
theorem lemma_3_5_2 {L κrs κbar : ℝ} (hf : AssumptionHL f L) (hrs : 0 ≤ κrs)
    (hκ : 1 < κbar) (heq : IsMClassEquation f x s lam r) (hr : ‖r‖ ≤ κrs * ‖s‖ ^ 2)
    (hlam0 : 0 ≤ lam) (hlam : lam ≤ κbar * ‖s‖) :
    (L / 2 + κrs + κbar)⁻¹ * √‖gradient f (x + s)‖ ≤ ‖s‖ := by
  have h := (lemma_3_5_2_sqrt hf hrs (by linarith) heq hr hlam0 hlam).2
  set C := L / 2 + κrs + κbar
  have hC : 1 ≤ C := by have := hf.one_le; simp only [C]; linarith
  have hsC : √C ≤ C := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  refine le_trans ?_ h
  gcongr

/-- **Lemma 3.5.3** of [cartis2022evaluation] (a necessary condition for fast rates). Under f.gL
with constant `L₁`, if every step `s_k` from `x_k` solves (3.5.2) with `‖r_k‖ ≤ κ_rg ‖∇f(x_k)‖`
(`κ_rg < 1`) and `0 ≤ λ_k ≤ κ̄_λ` (3.5.8), and the gradients converge quadratically,
`‖∇f(x_{k+1})‖ ≤ κ_c ‖∇f(x_k)‖²` (3.5.9) with `κ_c > 0`, then (3.5.7) holds:
`‖s_k‖ ≥ κ̄_s ‖∇f(x_{k+1})‖^{1/2}` with `κ̄_s = (1 - κ_rg)/((L₁ + κ̄_λ) √κ_c)`. (f.Bb, f.HL and
(3.5.1) are not needed.) -/
theorem lemma_3_5_3 {L₁ κrg κbar κc : ℝ} (hf : Chapter02.AssumptionGL f L₁) (hrg : κrg < 1)
    (hκc : 0 < κc) {x s r : ℕ → EuclideanSpace ℝ (Fin n)} {lam : ℕ → ℝ}
    (heq : ∀ k, IsMClassEquation f (x k) (s k) (lam k) (r k))
    (hr : ∀ k, ‖r k‖ ≤ κrg * ‖gradient f (x k)‖) (hlam : ∀ k, 0 ≤ lam k ∧ lam k ≤ κbar)
    (hquad : ∀ k, ‖gradient f (x (k + 1))‖ ≤ κc * ‖gradient f (x k)‖ ^ 2) (k : ℕ) :
    (1 - κrg) / ((L₁ + κbar) * √κc) * √‖gradient f (x (k + 1))‖ ≤ ‖s k‖ := by
  set g := ‖gradient f (x k)‖
  set w := -gradient f (x k) + r k
  have hκ : 0 ≤ κbar := (hlam 0).1.trans (hlam 0).2
  have hLκ : 0 < L₁ + κbar := by linarith [hf.one_le]
  have hHn := hf.norm_iteratedFDeriv_two_le (x k)
  -- `‖w‖ ≤ (L₁ + κ̄_λ) ‖s_k‖`
  have hw : ‖w‖ ≤ (L₁ + κbar) * ‖s k‖ := by
    have h1 := heq k w
    have h2 : ‖w‖ ^ 2 = iteratedFDeriv ℝ 2 f (x k) ![s k, w] + lam k * ⟪s k, w⟫ := by
      rw [h1, ← inner_neg_left, ← inner_add_left, real_inner_self_eq_norm_sq]
    have h3 := abs_apply_vec_le (iteratedFDeriv ℝ 2 f (x k)) (s k) w
    have h4 := abs_real_inner_le_norm (s k) w
    have h5 : lam k * ⟪s k, w⟫ ≤ κbar * (‖s k‖ * ‖w‖) := by
      calc lam k * ⟪s k, w⟫ ≤ lam k * (‖s k‖ * ‖w‖) :=
            mul_le_mul_of_nonneg_left ((le_abs_self _).trans h4) (hlam k).1
        _ ≤ κbar * (‖s k‖ * ‖w‖) := mul_le_mul_of_nonneg_right (hlam k).2 (by positivity)
    have h6 : iteratedFDeriv ℝ 2 f (x k) ![s k, w] ≤ L₁ * ‖s k‖ * ‖w‖ :=
      (le_abs_self _).trans (h3.trans (by gcongr))
    rcases (norm_nonneg w).eq_or_lt with h0 | h0
    · rw [← h0]; positivity
    · have : ‖w‖ * ‖w‖ ≤ ((L₁ + κbar) * ‖s k‖) * ‖w‖ := by nlinarith
      exact le_of_mul_le_mul_right this h0
  -- `(1 - κ_rg) ‖∇f(x_k)‖ ≤ ‖w‖`
  have hgw : (1 - κrg) * g ≤ ‖w‖ := by
    have : g - ‖r k‖ ≤ ‖w‖ := by
      have := norm_sub_norm_le (-gradient f (x k)) (-(r k))
      rw [norm_neg, norm_neg, sub_neg_eq_add] at this
      exact this
    linarith [hr k]
  have hsq : √‖gradient f (x (k + 1))‖ ≤ √κc * g := by
    calc √‖gradient f (x (k + 1))‖ ≤ √(κc * g ^ 2) := Real.sqrt_le_sqrt (hquad k)
      _ = √κc * g := by rw [Real.sqrt_mul hκc.le, Real.sqrt_sq (norm_nonneg _)]
  have hsκ : 0 < √κc := Real.sqrt_pos.2 hκc
  calc (1 - κrg) / ((L₁ + κbar) * √κc) * √‖gradient f (x (k + 1))‖
      ≤ (1 - κrg) / ((L₁ + κbar) * √κc) * (√κc * g) :=
        mul_le_mul_of_nonneg_left hsq (div_nonneg (by linarith) (by positivity))
    _ = (1 - κrg) * g / (L₁ + κbar) := by field_simp
    _ ≤ ‖s k‖ := by
        rw [div_le_iff₀ hLκ]; linarith

end Lemmas

/-! ### The data (3.5.12) and the one-dimensional example -/


/-- The second-order jet `(c₀, c₁ ⟪e, ·⟫, c₂ ⟪e, ·⟫⟪e, ·⟫)` with coefficients `c : Fin 3 → ℝ` along
`e` (the jets of a ridge function `x ↦ G ⟪e, x⟫`, `jetOracle_ridge`). -/
noncomputable def ridgeJet (e : EuclideanSpace ℝ (Fin n)) (c : Fin 3 → ℝ) :
    Jet (EuclideanSpace ℝ (Fin n)) 2 := fun j =>
  c j • (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin j) ℝ).compContinuousLinearMap
    fun _ => innerSL ℝ e

/-- The second-order oracle of a ridge function `x ↦ G ⟪e, x⟫` is the ridge jet with
coefficients `G^{(j)}(⟪e, x⟫)`. -/
theorem jetOracle_ridge {G : ℝ → ℝ} (hG : ContDiff ℝ 2 G) (e x : EuclideanSpace ℝ (Fin n)) :
    jetOracle (ridge G e) 2 x = ridgeJet e fun j => iteratedDeriv j G ⟪e, x⟫ := by
  funext j
  ext m
  have hj : ((j : ℕ) : WithTop ℕ∞) ≤ 2 := by exact_mod_cast Nat.lt_succ_iff.1 j.isLt
  rw [jetOracle_apply, iteratedFDeriv_ridge_apply hG hj]
  simp [ridgeJet, mul_comm]

/-- **The one-dimensional example of Theorem 3.5.4** ([cartis2022evaluation], (3.5.11)–(3.5.21)
and its proof in Appendix B). For step factors in `[a, b]` (`0 < a ≤ b`) there are `L₁, L₂ ≥ 1`
and `B ≥ 0` (depending only on `a, b`) such that for every `ε ∈ (0, 1]`, every `θ` with
`θ_k ∈ [a, b]` and every sequence of abscissae with `x_{k+1} = x_k + θ_k ε^{1/2}/(2 f_k)`
(`k < k_ε`), there is a `C²` function `G : ℝ → ℝ` whose ridge `f = ridge G e₀` on `ℝ¹` satisfies
f.Bb (with `f_low = -B`), f.gL (`L₁`), f.HL (`L₂`), `|f| ≤ B`, and `G` interpolates the data
(3.5.12) `(f_k, g_k, H_k)` at `x_k` for `k ≤ k_ε`. -/
theorem exists_slowSecondOrder_ridge {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ L₁ L₂ B : ℝ, 1 ≤ L₁ ∧ 1 ≤ L₂ ∧ 0 ≤ B ∧ ∀ (ε : ℝ) (θ x : ℕ → ℝ), 0 < ε → ε ≤ 1 →
      (∀ k < secondOrderK ε, θ k ∈ Icc a b) →
      (∀ k < secondOrderK ε,
        x (k + 1) = x k + θ k * ε ^ (1 / 2 : ℝ) / (2 * secondOrderF ε k)) →
      ∃ G : ℝ → ℝ, ContDiff ℝ 2 G ∧
        Chapter02.AssumptionBb (ridge G Chapter02.e₀) (-B) ∧
        Chapter02.AssumptionGL (ridge G Chapter02.e₀) L₁ ∧
        AssumptionHL (ridge G Chapter02.e₀) L₂ ∧ (∀ y, |ridge G Chapter02.e₀ y| ≤ B) ∧
        ∀ k ≤ secondOrderK ε, G (x k) = secondOrderF ε k ∧
          deriv G (x k) = secondOrderG ε k ∧ iteratedDeriv 2 G (x k) = secondOrderH ε k := by
  obtain ⟨L, B, hL, hB, H⟩ := exists_slowSecondOrder_interpolant ha hab
  refine ⟨max B 1, max L 1, B, le_max_right _ _, le_max_right _ _, hB,
    fun ε θ x hε hε1 hθ hx => ?_⟩
  obtain ⟨G, hG, hGL, hGB, hGk⟩ := H ε θ x hε hε1 hθ (fun k hk => by
    rw [hx k hk]; rfl)
  obtain ⟨hb, hgl, -, hhl, -⟩ := ridge_assumptions_two hG hGL hGB
  refine ⟨G, hG, hb, hgl, hhl, fun y => by simpa [ridge_apply] using hGB 0 (by norm_num) _,
    fun k hk => ?_⟩
  obtain ⟨h0, h1, h2⟩ := hGk k hk
  exact ⟨h0, by rw [h1]; rfl, by rw [h2]; rfl⟩

/-! ### Theorem 3.5.4 -/

section Theorem354

variable {ε : ℝ}

/-- The data jet `(f_k, g_k e₀, H_k e₀ e₀ᵀ)` of (3.5.12) at the `k`-th iterate. -/
private noncomputable def dataJet (ε : ℝ) (k : ℕ) : Jet (EuclideanSpace ℝ (Fin 1)) 2 :=
  ridgeJet Chapter02.e₀ ![secondOrderF ε k, secondOrderG ε k, secondOrderH ε k]

/-- The abscissae of the iterates the method would produce on the data (3.5.12). -/
private noncomputable def dataIter
    (M : OracleMethod (EuclideanSpace ℝ (Fin 1)) (Jet (EuclideanSpace ℝ (Fin 1)) 2)) (ε : ℝ) :
    ℕ → EuclideanSpace ℝ (Fin 1)
  | 0 => M.x₀
  | k + 1 => M.next k fun i => dataJet ε i

/-- `c_k = ε^{1/2}/(2 f_k)`, the reference step at the `k`-th iterate. -/
private noncomputable def refStep (ε : ℝ) (k : ℕ) : ℝ := ε ^ (1 / 2 : ℝ) / (2 * secondOrderF ε k)

/-- The step factors of the method on the data, clipped to `[a, b]`. -/
private noncomputable def clipFactor (a b : ℝ)
    (M : OracleMethod (EuclideanSpace ℝ (Fin 1)) (Jet (EuclideanSpace ℝ (Fin 1)) 2)) (ε : ℝ)
    (k : ℕ) : ℝ :=
  max a (min b (⟪Chapter02.e₀, dataIter M ε (k + 1) - dataIter M ε k⟫ / refStep ε k))

/-- The interpolation abscissae `x_{k+1} = x_k + θ_k c_k`, `x_0 = ⟪e₀, M.x₀⟫`. -/
private noncomputable def nodes (a b : ℝ)
    (M : OracleMethod (EuclideanSpace ℝ (Fin 1)) (Jet (EuclideanSpace ℝ (Fin 1)) 2)) (ε : ℝ)
    (k : ℕ) : ℝ :=
  ⟪Chapter02.e₀, M.x₀⟫ + ∑ j ∈ range k, clipFactor a b M ε j * refStep ε j

/-- The step-factor bounds (3.5.19) for a step of class `𝓜` on the data (3.5.12): if at a point
with derivatives `g < 0`, `H > 0` and `H ≥ |g|^{1/2}`, the step `t` satisfies
`(H + λ) t = -g + ρ` with `λ ≥ 0`, `|ρ| ≤ κ_rg |g|` and `H + λ ≤ κ_λ H`, then
`t = θ (-g/H)` with `θ ∈ [(1 - κ_rg)/κ_λ, 1 + κ_rg]`. -/
private theorem factor_mem {g H lam t ρ κrg κlam : ℝ} (hrg : κrg ≤ 1) (hg : g < 0) (hH : 0 < H)
    (hlam : 0 ≤ lam) (heq : (H + lam) * t = -g + ρ) (hρ : |ρ| ≤ κrg * |g|)
    (hb : H + lam ≤ κlam * H) :
    t / (-g / H) ∈ Icc ((1 - κrg) / κlam) (1 + κrg) := by
  have hκlam : 0 < κlam := by
    by_contra h; push Not at h; nlinarith
  have hHl : 0 < H + lam := by linarith
  have hg' : |g| = -g := abs_of_neg hg
  rw [hg'] at hρ
  have ht0 : t = (-g + ρ) / (H + lam) := by
    rw [eq_div_iff hHl.ne', mul_comm]; exact heq
  have ht : t / (-g / H) = (-g + ρ) * H / ((H + lam) * -g) := by
    rw [ht0]
    field_simp
  have hρ' := abs_le.1 hρ
  rw [ht]
  constructor
  · rw [div_le_div_iff₀ hκlam (by nlinarith)]
    nlinarith [mul_le_mul_of_nonneg_left hb (by nlinarith : (0 : ℝ) ≤ (1 - κrg) * -g),
      mul_le_mul_of_nonneg_right (by linarith : (1 - κrg) * -g ≤ -g + ρ) hH.le]
  · rw [div_le_iff₀ (by nlinarith)]
    have h1 : (-g + ρ) * H ≤ (1 + κrg) * -g * H :=
      mul_le_mul_of_nonneg_right (by linarith) hH.le
    have h2 : (1 + κrg) * -g * H ≤ (1 + κrg) * ((H + lam) * -g) := by
      have : 0 ≤ (1 + κrg) * -g := by nlinarith [abs_nonneg ρ]
      nlinarith
    linarith

/-- **Theorem 3.5.4** of [cartis2022evaluation] (a complexity lower bound for methods in `𝓜`).
For all constants `κ_rg ∈ [0, 1)`, `κ_rs > 0`, `κ_λ > 1` there are `f_low`, `L₁ ≥ 1`, `L₂ ≥ 1` and
`B` such that for every `ε₁ ∈ (0, 1)` and every second-order oracle method `M` on `ℝ¹` (with any
starting point `x₀`) there is `f : ℝ¹ → ℝ` satisfying f.Bb, f.gL and f.HL with these constants,
`|f| ≤ B` and `f(x₀) = 1`, such that, if `M` is in the class `𝓜` on `f`, then the first iterate with
`‖∇f(x_k)‖ ≤ ε₁` is `x_{k_ε}`, `k_ε = ⌈ε₁^{-3/2}⌉`: the method needs `k_ε + 1` evaluations of `f`,
`∇f` and `∇²f`. -/
theorem theorem_3_5_4 {κrg κrs κlam : ℝ} (hrg0 : 0 ≤ κrg) (hrg1 : κrg < 1) (_hrs : 0 < κrs)
    (hlam1 : 1 < κlam) :
    ∃ flow L₁ L₂ B : ℝ, 1 ≤ L₁ ∧ 1 ≤ L₂ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ M : OracleMethod (EuclideanSpace ℝ (Fin 1)) (Jet (EuclideanSpace ℝ (Fin 1)) 2),
        ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, Chapter02.AssumptionBb f flow ∧
          Chapter02.AssumptionGL f L₁ ∧ AssumptionHL f L₂ ∧ (∀ y, |f y| ≤ B) ∧ f M.x₀ = 1 ∧
          (IsMClassMethod κrg κrs κlam M f ε →
            IsFirstHit (fun k => ‖gradient f (M.iterate (jetOracle f 2) k)‖ ≤ ε)
              ⌈ε ^ (-(3 / 2 : ℝ))⌉₊) := by
  set a := (1 - κrg) / κlam
  set b := 1 + κrg
  have ha : 0 < a := div_pos (by linarith) (by linarith)
  have hab : a ≤ b := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  obtain ⟨L₁, L₂, B, hL₁, hL₂, -, H⟩ := exists_slowSecondOrder_ridge ha hab
  refine ⟨-B, L₁, L₂, B, hL₁, hL₂, fun ε hε hε1 M => ?_⟩
  set K := secondOrderK ε
  set xs := nodes a b M ε
  have hθ : ∀ k, clipFactor a b M ε k ∈ Icc a b := fun k =>
    ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  obtain ⟨G, hG, hb, hgl, hhl, hB, hGk⟩ := H ε (clipFactor a b M ε) xs hε hε1.le
    (fun k _ => hθ k) (fun k _ => by
      simp only [xs, nodes, sum_range_succ, refStep, mul_div_assoc]; ring)
  set f := ridge G Chapter02.e₀
  have hxs0 : xs 0 = ⟪Chapter02.e₀, M.x₀⟫ := by simp [xs, nodes]
  have hx0' : M.x₀ = xs 0 • Chapter02.e₀ := by rw [hxs0]; exact eq_inner_e₀_smul _
  have hf0 : f M.x₀ = 1 := by
    have := (hGk 0 (Nat.zero_le _)).1
    simp only [f, ridge_apply]
    rw [← hxs0, this]; simp [secondOrderF]
  refine ⟨f, hb, hgl, hhl, hB, hf0, fun hM => ?_⟩
  -- facts on the data
  have hr : 0 < ε ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hε _
  have hfpos : ∀ k ≤ K, 0 < secondOrderF ε k := fun k hk => secondOrderF_pos hε hε1 hk
  have hgrad : ∀ y, gradient f y = deriv G ⟪Chapter02.e₀, y⟫ • Chapter02.e₀ :=
    gradient_ridge (hG.differentiable (by norm_num))
  have hnorm : ∀ k ≤ K, ‖gradient f (xs k • Chapter02.e₀)‖ = 2 * ε * secondOrderF ε k :=
    fun k hk => by
      rw [hgrad, Chapter02.inner_e₀_smul, (hGk k hk).2.1, norm_smul, Chapter02.norm_e₀,
        mul_one, secondOrderG, Real.norm_eq_abs, abs_of_neg]
      · ring
      · have := hfpos k hk; nlinarith
  have htest : ∀ k ≤ K, (‖gradient f (xs k • Chapter02.e₀)‖ ≤ ε ↔ K ≤ k) := fun k hk => by
    rw [hnorm k hk]
    constructor
    · intro h
      by_contra hlt
      have := secondOrderF_gt_half hε (not_le.1 hlt)
      nlinarith
    · intro h
      have hkK : k = K := le_antisymm hk h
      rw [hkK]
      have := secondOrderF_K_le_half hε
      nlinarith
  have hjet : ∀ k ≤ K, jetOracle f 2 (xs k • Chapter02.e₀) = dataJet ε k := fun k hk => by
    rw [jetOracle_ridge hG, Chapter02.inner_e₀_smul, dataJet]
    congr 1
    funext j
    obtain ⟨h0, h1, h2⟩ := hGk k hk
    fin_cases j
    · simpa using h0
    · simpa using h1
    · simpa using h2
  -- the iterates follow the nodes
  have hiter : ∀ k ≤ K, ∀ i ≤ k, M.iterate (jetOracle f 2) i = xs i • Chapter02.e₀ := by
    intro k
    induction k with
    | zero => intro _ i hi; rw [Nat.le_zero.1 hi, M.iterate_zero, hx0']
    | succ k ih =>
      intro hk i hi
      have hx := ih (Nat.le_of_succ_le hk)
      rcases Nat.lt_or_eq_of_le hi with hi | rfl
      · exact hx i (Nat.lt_succ_iff.1 hi)
      have hkK : k < K := hk
      -- the next iterate is the data iterate
      have hnext : M.iterate (jetOracle f 2) (k + 1) = dataIter M ε (k + 1) := by
        rw [M.iterate_succ]
        simp only [dataIter]
        congr 1
        funext i
        rw [hx i (Nat.lt_succ_iff.1 i.isLt), hjet i (by omega)]
      have hprev : dataIter M ε k = xs k • Chapter02.e₀ := by
        cases k with
        | zero => simp [dataIter, hx0']
        | succ m =>
          rw [← hx (m + 1) le_rfl, M.iterate_succ]
          simp only [dataIter]
          congr 1
          funext i
          rw [hx i (by omega), hjet i (by omega)]
      -- the class condition at iteration `k`
      have hstop : ∀ j ≤ k, ¬ ‖gradient f (M.iterate (jetOracle f 2) j)‖ ≤ ε := fun j hj => by
        rw [hx j hj, htest j (by omega)]; omega
      obtain ⟨lam, r, hstep⟩ := hM k hstop
      rw [hnext, hx k le_rfl] at hstep
      set p := xs k • Chapter02.e₀
      set s := dataIter M ε (k + 1) - p
      set t := ⟪Chapter02.e₀, s⟫
      have hG2 : ContDiff ℝ 2 G := hG
      obtain ⟨hf0k, hf1k, hf2k⟩ := hGk k hkK.le
      have hinner : ⟪Chapter02.e₀, p⟫ = xs k := Chapter02.inner_e₀_smul _
      -- the equation tested against `e₀`
      have heq := hstep.equation Chapter02.e₀
      rw [iteratedFDeriv_ridge_apply hG2 (by norm_num), hgrad, hinner, hf2k, hf1k,
        real_inner_smul_left, real_inner_self_eq_norm_sq, Chapter02.norm_e₀] at heq
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        real_inner_self_eq_norm_sq, Chapter02.norm_e₀] at heq
      -- the curvature and the gradient norm at `x_k`
      have hmin : Chapter01.hessianMinEig f p = secondOrderH ε k := by
        rw [Chapter01.hessianMinEig_def, minCurvature_iteratedFDeriv_ridge_of_forall hG2
          Chapter02.norm_e₀ (fun d => ?_), hinner, hf2k]
        conv_rhs => rw [eq_inner_e₀_smul d]
        rw [norm_smul, Chapter02.norm_e₀, mul_one, Real.norm_eq_abs, sq_abs]
      have hgn : ‖gradient f p‖ = 2 * ε * secondOrderF ε k := hnorm k hkK.le
      have hfk := secondOrderF_gt_half hε hkK
      have hfk1 := secondOrderF_le_one hε k
      have hHpos : 0 < secondOrderH ε k := by unfold secondOrderH; positivity
      have hr2 : (ε ^ (1 / 2 : ℝ)) ^ 2 = ε := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]; norm_num
      have hsqrt : √‖gradient f p‖ ≤ secondOrderH ε k := by
        have h8 : 1 ≤ 8 * secondOrderF ε k ^ 3 := by
          have := pow_le_pow_left₀ (by norm_num) hfk.le 3
          norm_num at this; linarith
        have hle : 2 * ε * secondOrderF ε k ≤ secondOrderH ε k ^ 2 := by
          rw [secondOrderH, mul_pow, mul_pow, hr2]
          have := mul_le_mul_of_nonneg_left h8
            (by positivity : (0 : ℝ) ≤ 2 * ε * secondOrderF ε k)
          nlinarith
        rw [hgn]
        exact (Real.sqrt_le_sqrt hle).trans (Real.sqrt_sq hHpos.le).le
      have hbound := hstep.bound
      rw [hmin, abs_of_pos hHpos, max_eq_left hsqrt] at hbound
      have hρ : |⟪r, Chapter02.e₀⟫| ≤ κrg * |secondOrderG ε k| := by
        have h1 := abs_real_inner_le_norm r Chapter02.e₀
        rw [Chapter02.norm_e₀, mul_one] at h1
        have h2 := hstep.residual.trans (min_le_left _ _)
        rw [hgn] at h2
        refine h1.trans (h2.trans (le_of_eq ?_))
        rw [secondOrderG, abs_of_neg (by nlinarith)]
        ring
      have hg : secondOrderG ε k < 0 := by unfold secondOrderG; nlinarith
      have hmem := factor_mem hrg1.le hg hHpos hstep.nonneg
        (t := t) (ρ := ⟪r, Chapter02.e₀⟫) (by
          simp only [one_pow, mul_one] at heq
          rw [real_inner_comm s Chapter02.e₀] at heq
          rw [show t = ⟪s, Chapter02.e₀⟫ from real_inner_comm _ _]
          linarith) hρ hbound
      -- the clipping is inactive and the node is the iterate
      have hc : -secondOrderG ε k / secondOrderH ε k = refStep ε k := by
        unfold secondOrderG secondOrderH refStep
        have hf0 := hfpos k hkK.le
        rw [div_eq_div_iff (by positivity) (by positivity)]
        linear_combination (-4 * secondOrderF ε k ^ 2) * hr2
      have hclip : clipFactor a b M ε k = t / refStep ε k := by
        rw [clipFactor, hprev, ← hc, min_eq_right hmem.2, max_eq_right hmem.1]
      have hrefpos : 0 < refStep ε k := by unfold refStep; have := hfpos k hkK.le; positivity
      have hxs : xs (k + 1) = xs k + t := by
        simp only [xs, nodes, sum_range_succ]
        rw [hclip, div_mul_cancel₀ _ hrefpos.ne']
        ring
      have hs' : t • Chapter02.e₀ = s := (eq_inner_e₀_smul s).symm
      rw [hxs, add_smul, hnext, hs']
      exact (add_sub_cancel p _).symm
  have hK := hiter K le_rfl
  rw [show ⌈ε ^ (-(3 / 2 : ℝ))⌉₊ = K from rfl]
  refine ⟨by simp only; rw [hK K le_rfl]; exact (htest K le_rfl).2 le_rfl, fun j hj => ?_⟩
  simp only
  rw [hK j hj.le, htest j hj.le]
  exact not_le.2 hj

end Theorem354

/-! ### Corollary 3.5.5 -/

section RidgeClass

open Chapter02 (e₀ norm_e₀ inner_e₀_smul)

/-- **Steps of class `𝓜` on a ridge function of `ℝ¹`.** At `x` with `a = ⟪e₀, x⟫`, a step
`t e₀` (`t ≠ 0`) with multiplier `λ ≥ 0` and scalar residual `ρ` satisfies (3.5.2)–(3.5.4) as soon
as the one-dimensional conditions hold: `(G''(a) + λ) t = -G'(a) + ρ`,
`|ρ| ≤ min(κ_rg |G'(a)|, κ_rs t²)`, `G''(a) + λ ≥ 0` and
`G''(a) + λ ≤ κ_λ max(|G''(a)|, |G'(a)|^{1/2})`. -/
theorem isMClassStepWith_ridge {G : ℝ → ℝ} (hG : ContDiff ℝ 2 G) (x : EuclideanSpace ℝ (Fin 1))
    {t lam ρ κrg κrs κlam : ℝ} (ht : t ≠ 0) (hlam : 0 ≤ lam)
    (heq : (iteratedDeriv 2 G ⟪e₀, x⟫ + lam) * t = -deriv G ⟪e₀, x⟫ + ρ)
    (hres : |ρ| ≤ min (κrg * |deriv G ⟪e₀, x⟫|) (κrs * t ^ 2))
    (hpsd : 0 ≤ iteratedDeriv 2 G ⟪e₀, x⟫ + lam)
    (hbd : iteratedDeriv 2 G ⟪e₀, x⟫ + lam ≤
      κlam * max |iteratedDeriv 2 G ⟪e₀, x⟫| √|deriv G ⟪e₀, x⟫|) :
    IsMClassStepWith (ridge G e₀) κrg κrs κlam x (t • e₀) lam (ρ • e₀) := by
  have hgrad : gradient (ridge G e₀) x = deriv G ⟪e₀, x⟫ • e₀ :=
    gradient_ridge (hG.differentiable (by norm_num)) x
  have hng : ‖gradient (ridge G e₀) x‖ = |deriv G ⟪e₀, x⟫| := by
    rw [hgrad, norm_smul, norm_e₀, mul_one, Real.norm_eq_abs]
  refine ⟨smul_ne_zero ht (by intro h; simpa [h] using norm_e₀), fun v => ?_, ?_, hlam,
    fun d => ?_, ?_⟩
  · rw [iteratedFDeriv_ridge_apply hG (by norm_num), hgrad]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, inner_e₀_smul,
      real_inner_smul_left]
    linear_combination ⟪e₀, v⟫ * heq
  · rw [hng, norm_smul, norm_smul, norm_e₀, mul_one, mul_one, Real.norm_eq_abs,
      Real.norm_eq_abs, sq_abs]
    exact hres
  · rw [iteratedFDeriv_ridge_apply_diag hG (by norm_num), ← inner_e₀_sq d]
    nlinarith [sq_nonneg ⟪e₀, d⟫]
  · rw [hessianMinEig_ridge hG, hng]
    exact hbd

end RidgeClass

/-- **Corollary 3.5.5** of [cartis2022evaluation] for **AR2** (optimal complexity in `𝓜`). For
all AR2 constants there are `f_low`, `L_{f,1}, L_{f,2} ≥ 1`, `B` and `κ_λ > 1` such that for every
`ε₁ ∈ (0, 1]` there are `f : ℝ¹ → ℝ` satisfying f.Bb, f.gL, f.HL and `|f| ≤ B` and an AR2 run with
`ε₂ = +∞` from `x₀ = 0` which terminates exactly at iteration `k_ε = ⌈ε₁^{-3/2}⌉`, whose steps are
of class `𝓜` (with `κ_rg = 0`, `κ_rs = 1`, `κ_λ`, `λ_k = σ₀ ‖s_k‖/2`), so the lower bound of
Theorem 3.5.4 is attained by AR2, while the upper bound of Theorem 3.3.5 for this run,
`κ^A (f(x₀) - f_low)/ε₁^{3/2} + κ^C` with `f(x₀) - f_low ≤ 2B`, is of the same order
`ε₁^{-3/2}` with constants independent of `ε₁`. The example is that of Theorem 3.3.6 (the data of
Theorem 12.2.15 with `p = 2`, `q = 1`: zero Hessians at the iterates and exact global model
minimizers with `σ_k = σ₀`), not the data (3.5.12). -/
theorem corollary_3_5_5_i (P : AR2Params) :
    ∃ flow L₁ L₂ B κlam : ℝ, 1 ≤ L₁ ∧ 1 ≤ L₂ ∧ 1 < κlam ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, Chapter02.AssumptionBb f flow ∧
        Chapter02.AssumptionGL f L₁ ∧ AssumptionHL f L₂ ∧ (∀ y, |f y| ≤ B) ∧
        ∃ x s σ, x 0 = 0 ∧ algorithm_3_3_1 f P ε none x s σ ∧
          IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) ⌈ε ^ (-(3 / 2 : ℝ))⌉₊ ∧
          (∀ k < ⌈ε ^ (-(3 / 2 : ℝ))⌉₊, IsMClassStep f 0 1 κlam (x k) (x (k + 1) - x k)) ∧
          f (x 0) - flow ≤ 2 * B ∧
          ((⌈ε ^ (-(3 / 2 : ℝ))⌉₊ + 1 : ℕ) : ℝ) ≤
            kappaSAR2 P L₂ * (1 + |Real.log P.γ₁| / Real.log P.γ₂) * (2 * B) /
              ε ^ (3 / 2 : ℝ) + kappaCAR2 P L₂ := by
  obtain ⟨L₁, L₂, B, hL₁, hL₂, -, H⟩ := exists_ar2_slow_data P le_rfl (by norm_num : 1 ≤ 2)
  have hσ₀ := P.σ₀_pos
  set κlam := 1 + √(P.σ₀ / 2)
  refine ⟨-B, L₁, L₂, B, κlam, hL₁, hL₂, by
    have := Real.sqrt_pos.2 (half_pos hσ₀); simp only [κlam]; linarith, fun ε hε hε1 => ?_⟩
  obtain ⟨G, xr, hG, hb, hgl, hhl, hB, hx0, hd, hx, hv⟩ := H ε hε hε1
  have hK := ar2SlowK_pos (q := 1) hε
  set K := ar2SlowK 1 ε
  have htest : ∀ k ≤ K, (stopTest (ridge G Chapter02.e₀) ε none (xr k • Chapter02.e₀) ↔
      K ≤ k) := fun k hk => by
    rw [stopTest_none, gradient_ridge (hG.differentiable (by norm_num)),
      Chapter02.inner_e₀_smul, ← iteratedDeriv_one, (hd k hk).1, norm_smul, Chapter02.norm_e₀,
      mul_one, norm_neg, Real.norm_of_nonneg (ar2SlowAlpha_pos hε hK hk).le]
    exact ar2SlowAlpha_le_iff hε hK hk
  obtain ⟨x, s, σ, hx0', hrun, -, -, hhit, hxk⟩ := exists_ar2_ridge_run P hε hε1
    (ε₂ := none) (fun _ h => absurd h (by simp)) le_rfl (by norm_num) hG
    (fun k hk => ar2SlowAlpha_pos hε hK hk.le) (fun k hk => hd k hk.le) hx hv htest
  have hhit' : IsFirstHit (fun k => ‖gradient (ridge G Chapter02.e₀) (x k)‖ ≤ ε) K := by
    simpa only [stopTest_none] using hhit
  have hf0 : ridge G Chapter02.e₀ (x 0) - -B ≤ 2 * B := by
    linarith [le_abs_self (ridge G Chapter02.e₀ (x 0)), hB (x 0)]
  rw [← ar2SlowK_one]
  refine ⟨ridge G Chapter02.e₀, hb, hgl, hhl, hB, x, s, σ, by rw [hx0', hx0, zero_smul], hrun,
    hhit', fun k hk => ?_, hf0, ?_⟩
  · -- the step is of class `𝓜` with `λ = σ₀ t/2`, `r = 0`
    set α := ar2SlowAlpha ε K k
    have hα : 0 < α := ar2SlowAlpha_pos hε hK hk.le
    set y := α / (P.σ₀ * ((1 - 1).factorial : ℝ) / ((2 : ℕ).factorial : ℝ))
    have hy : y = 2 * α / P.σ₀ := by
      simp only [y]; norm_num [Nat.factorial]; rw [div_div_eq_mul_div, mul_comm]
    set t := xr (k + 1) - xr k
    have ht : t = √y := by
      simp only [t]; rw [hx k hk, Real.sqrt_eq_rpow]; simp only [y, α]; norm_num
    have hy0 : 0 < y := by rw [hy]; positivity
    have ht0 : 0 < t := by rw [ht]; exact Real.sqrt_pos.2 hy0
    have ht2 : t ^ 2 = 2 * α / P.σ₀ := by rw [ht, Real.sq_sqrt hy0.le, hy]
    have hstep : x (k + 1) - x k = t • Chapter02.e₀ := by rw [hxk, hxk, ← sub_smul]
    have hxe : ⟪Chapter02.e₀, x k⟫ = xr k := by rw [hxk]; exact Chapter02.inner_e₀_smul _
    obtain ⟨h1, h2⟩ := hd k hk.le
    have hg : deriv G (xr k) = -α := by rw [← iteratedDeriv_one]; exact h1
    have hH : iteratedDeriv 2 G (xr k) = 0 := h2 2 (by norm_num) le_rfl (by norm_num)
    rw [hstep]
    refine ⟨P.σ₀ * t / 2, (0 : ℝ) • Chapter02.e₀, isMClassStepWith_ridge hG (x k) ht0.ne'
      (lam := P.σ₀ * t / 2) (ρ := 0) (by positivity) ?_ ?_ ?_ ?_⟩
    · rw [hxe, hH, hg]
      have : P.σ₀ * t / 2 * t = α := by
        rw [show P.σ₀ * t / 2 * t = P.σ₀ / 2 * t ^ 2 by ring, ht2]; field_simp
      linarith
    · rw [abs_zero]; exact le_min (by simp) (by positivity)
    · rw [hxe, hH]; positivity
    · rw [hxe, hH, hg, abs_zero, abs_neg, abs_of_pos hα, zero_add,
        max_eq_right (Real.sqrt_nonneg _)]
      have hsq : P.σ₀ * t / 2 = √(P.σ₀ / 2) * √α := by
        rw [← Real.sqrt_mul (by positivity)]
        refine (Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)).2 ?_ |>.symm
        rw [show P.σ₀ * t / 2 * (P.σ₀ * t / 2) = P.σ₀ ^ 2 / 4 * t ^ 2 by ring, ht2]
        field_simp
        ring
      rw [hsq]
      have := Real.sqrt_nonneg α
      simp only [κlam]
      nlinarith
  · obtain ⟨kε, hk, hF, -⟩ := theorem_3_3_5 hb hhl hrun
    rw [hk.unique hhit', funEvalCount_eq] at hF
    refine hF.trans ?_
    have hA : 0 ≤ kappaSAR2 P L₂ * (1 + |Real.log P.γ₁| / Real.log P.γ₂) := by
      have := kappaSAR2_pos (P := P) hhl.nonneg
      have := P.ar.log_γ₂_pos
      positivity
    gcongr

/-- **Corollary 3.5.5** of [cartis2022evaluation] for **TRε** (optimal complexity in `𝓜`). There
are `f_low`, `L_{f,1}, L_{f,2} ≥ 1` and `B` such that for all TRε constants and every
`ε₁ ∈ (0, 1)` with `√ε₁ < Δ₀` (TRε requires `Δ₀ > ε_*`) there are `f : ℝ¹ → ℝ` satisfying f.Bb,
f.gL, f.HL and `|f| ≤ B` and a TRε run with `ε_* = √ε₁`, `ε₂ = +∞` from `x₀ = 0` (interior steps,
constant radius) which terminates exactly at iteration `k_ε = ⌈ε₁^{-3/2}⌉`, whose steps are of
class `𝓜` (with `κ_rg = 0`, `κ_rs = 1`, `κ_λ = 2`, `λ_k = ε_*`), while the upper bound of
Theorem 3.4.5 for this run is `κ^A 2B ε₁^{-3/2} + κ^B |log ε₁| + κ^C`, of the same order up to the
logarithmic term. -/
theorem corollary_3_5_5_ii :
    ∃ flow L₁ L₂ B : ℝ, 1 ≤ L₁ ∧ 1 ≤ L₂ ∧ ∀ (P : TREpsParams) (ε : ℝ), 0 < ε → ε < 1 →
      √ε < P.Δ₀ → ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, Chapter02.AssumptionBb f flow ∧
        Chapter02.AssumptionGL f L₁ ∧ AssumptionHL f L₂ ∧ (∀ y, |f y| ≤ B) ∧
        ∃ (x s : ℕ → EuclideanSpace ℝ (Fin 1)) (Δ : ℕ → ℝ), x 0 = 0 ∧
          algorithm_3_4_1 f P ε none (√ε) x s Δ ∧
          IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) ⌈ε ^ (-(3 / 2 : ℝ))⌉₊ ∧
          (∀ k < ⌈ε ^ (-(3 / 2 : ℝ))⌉₊, IsMClassStep f 0 1 2 (x k) (x (k + 1) - x k)) ∧
          ((⌈ε ^ (-(3 / 2 : ℝ))⌉₊ + 1 : ℕ) : ℝ) ≤
            kappaATREps P L₂ * (2 * B) / ε ^ (3 / 2 : ℝ) +
              1 / (2 * |Real.log P.γ₂|) * |Real.log ε| + kappaCTREps P L₂ := by
  obtain ⟨flow, L₁, L₂, B, hL₁, hL₂, H⟩ := tre_slow_example
  refine ⟨-B, L₁, L₂, B, hL₁, hL₂, fun P ε hε hε1 hΔ => ?_⟩
  obtain ⟨G, X, t, hG, -, hgl, hhl, hB, hdata, x, s, Δ, hx0, hxk, hrun, hhit⟩ :=
    H P ε hε hε1 hΔ
  set f := ridge G Chapter02.e₀
  have hb : Chapter02.AssumptionBb f (-B) := fun y => by linarith [neg_abs_le (f y), hB y]
  refine ⟨f, hb, hgl, hhl, hB, x, s, Δ, hx0, hrun, hhit, fun k hk => ?_, ?_⟩
  · obtain ⟨hXs, ht, hH, hstat⟩ := hdata k hk
    have hxe : ⟪Chapter02.e₀, x k⟫ = X k := by rw [hxk]; exact Chapter02.inner_e₀_smul _
    have hr := Real.sqrt_pos.2 hε
    rw [show x (k + 1) - x k = t k • Chapter02.e₀ by
      rw [hxk, hxk, hXs, add_smul, add_sub_cancel_left]]
    refine ⟨√ε, (0 : ℝ) • Chapter02.e₀, isMClassStepWith_ridge hG (x k) ht.ne' (lam := √ε)
      (ρ := 0) hr.le ?_ ?_ ?_ ?_⟩
    · rw [hxe]; linarith
    · rw [abs_zero]; exact le_min (by simp) (by positivity)
    · rw [hxe]; linarith
    · rw [hxe, abs_of_pos (hr.trans_le hH)]
      have := le_max_left (iteratedDeriv 2 G (X k)) √|deriv G (X k)|
      linarith
  · obtain ⟨kε, hk, hF, -⟩ := theorem_3_4_5 hb hhl hrun
    rw [hk.unique hhit, funEvalCount_eq] at hF
    refine hF.trans ?_
    have hA : 0 ≤ kappaATREps P L₂ := by
      have := kappaDeltaF_pos P hhl.pos
      have := Real.log_nonneg P.one_le_γ₃
      unfold kappaATREps kappaSTREps
      positivity
    have hf0 : f (x 0) - -B ≤ 2 * B := by linarith [le_abs_self (f (x 0)), hB (x 0)]
    gcongr

/-- **Corollary 3.5.5** of [cartis2022evaluation] for **iRN** (optimal complexity in `𝓜`),
**with a rescaled example**. For all iRN constants there are `f_low`, `L_{f,1}, L_{f,2} ≥ 1` and
`B` such that for every `ε₁ ∈ (0, 1)` there are `f : ℝ¹ → ℝ` satisfying f.Bb, f.gL, f.HL and
`|f| ≤ B` and an iRN run (`Q_k = I`, `ε₂ = +∞`, `λ_k = σ₀ᵁ ‖s_k‖`) from `x₀ = 0` terminating
exactly at iteration `k_ε = ⌈ε₁^{-3/2}⌉`, whose steps are of class `𝓜` (with `κ_rg = 0`,
`κ_rs = 1`, `κ_λ = 2 + σ₀ᵁ`), while the upper bound of Theorem 3.4.11 for this run is
`κ^A 2B ε₁^{-3/2} + κ^B`. (iRN's ratio (3.4.35) is not scale invariant: on the data (3.5.12) it
is `4 f_k³/θ_k³ ≥ 1/2`, which may be below `η` when `η > 1/2`; the example is therefore
`f(x) = c G(x/c)` with `c = min(1, (2η)^{-1/2})`, which leaves the gradients at the iterates, and
hence the termination index, unchanged and makes the ratio at least `1/(2c²) ≥ η`. The book's
sketch omits this.) -/
theorem corollary_3_5_5_iii (P : IRNParams) :
    ∃ flow L₁ L₂ B : ℝ, 1 ≤ L₁ ∧ 1 ≤ L₂ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, Chapter02.AssumptionBb f flow ∧
        Chapter02.AssumptionGL f L₁ ∧ AssumptionHL f L₂ ∧ (∀ y, |f y| ≤ B) ∧
        ∃ (x s : ℕ → EuclideanSpace ℝ (Fin 1)) (lam σL σU : ℕ → ℝ), x 0 = 0 ∧
          algorithm_3_4_2 f P ε none x s lam σL σU (fun _ => ⊤) ∧
          IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) ⌈ε ^ (-(3 / 2 : ℝ))⌉₊ ∧
          (∀ k < ⌈ε ^ (-(3 / 2 : ℝ))⌉₊,
            IsMClassStep f 0 1 (2 + P.σU₀) (x k) (x (k + 1) - x k)) ∧
          ((⌈ε ^ (-(3 / 2 : ℝ))⌉₊ + 1 : ℕ) : ℝ) ≤
            kappaAIRN P L₂ * (2 * B) / ε ^ (3 / 2 : ℝ) + kappaBIRN P L₂ := by
  obtain ⟨flow, L₁, L₂, B, hL₁, hL₂, H⟩ := irn_slow_example P
  refine ⟨-B, L₁, L₂, B, hL₁, hL₂, fun ε hε hε1 => ?_⟩
  obtain ⟨G, X, t, hG, -, hgl, hhl, hB, hdata, x, s, lam, σL, σU, hx0, hxk, -, hrun, hhit⟩ :=
    H ε hε hε1
  set f := ridge G Chapter02.e₀
  have hσ : 0 < P.σU₀ := P.σmin_pos.trans_le P.σmin_le_σU₀
  have hb : Chapter02.AssumptionBb f (-B) := fun y => by linarith [neg_abs_le (f y), hB y]
  refine ⟨f, hb, hgl, hhl, hB, x, s, lam, σL, σU, hx0, hrun, hhit, fun k hk => ?_, ?_⟩
  · obtain ⟨hXs, ht, hH, hstat⟩ := hdata k hk
    have hxe : ⟪Chapter02.e₀, x k⟫ = X k := by rw [hxk]; exact Chapter02.inner_e₀_smul _
    rw [show x (k + 1) - x k = t k • Chapter02.e₀ by
      rw [hxk, hxk, hXs, add_smul, add_sub_cancel_left]]
    refine ⟨P.σU₀ * t k, (0 : ℝ) • Chapter02.e₀, isMClassStepWith_ridge hG (x k) ht.ne'
      (lam := P.σU₀ * t k) (ρ := 0) (by positivity) ?_ ?_ ?_ ?_⟩
    · rw [hxe]; linarith
    · rw [abs_zero]; exact le_min (by simp) (by positivity)
    · rw [hxe]; nlinarith
    · rw [hxe, abs_of_pos (ht.trans_le hH)]
      have := le_max_left (iteratedDeriv 2 G (X k)) √|deriv G (X k)|
      nlinarith [mul_le_mul_of_nonneg_left hH hσ.le]
  · obtain ⟨kε, hk, hF, -⟩ := theorem_3_4_11 hb hhl hrun
    rw [hk.unique hhit, funEvalCount_eq] at hF
    refine hF.trans ?_
    have hA : 0 ≤ kappaAIRN P L₂ := by
      have hC : 0 < L₂ + 4 * sigmaUMax P L₂ + 2 * P.κ₃ := by
        linarith [hhl.nonneg, sigmaUMax_pos P L₂, P.κ₃_pos]
      have := Real.rpow_pos_of_pos hC (3 / 2 : ℝ)
      have := P.η_pos
      have := one_le_irnUnsuccBound P L₂
      unfold kappaAIRN kappaSIRN
      have : 0 ≤ irnUnsuccBound P L₂ + 1 := by linarith
      positivity
    have hf0 : f (x 0) - -B ≤ 2 * B := by linarith [le_abs_self (f (x 0)), hB (x 0)]
    gcongr

end CartisGouldToint.Chapter03

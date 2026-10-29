import Numlib.Analysis.Calculus.AnchoredLipschitzDerivs
import Numlib.Analysis.SpecialFunctions.FactorialSum
import Numlib.Data.Set.Basic
import Numlib.Optimization.ModelBased.HighOrder.Orders
import Numlib.Optimization.ModelBased.InexactTaylor

/-!
# Dynamic-accuracy methods: common bounds

Elementary bounds shared by the high-order methods with inexact derivatives and dynamic
accuracy ([cartis2022evaluation], Chapter 13): the TRqIDA/TRqEDA and ARqpIDA/ARqpEDA analyses.

* Consequences of the smoothness hypothesis `LipschitzDerivsAnchored f C A 0 q L` (the function
  and its derivatives of orders `0, …, q` are anchored-Lipschitz, [cartis2022evaluation] f.D0qL)
  at the anchors, with normalized constants `L_j ≥ 1`: Taylor's theorem anchored at an anchor,
  the bound `‖∇^i f(x)‖ ≤ L_f = lipMax L q` ((13.1.24)) and its inexact version
  `‖∇̄^i f(x)‖ ≤ L_f + κ_{∇,max} κ_h` ((13.1.63)).
* `taylorDecrement_le_two_mul`: the Taylor decrement of a short step is at most `2 L ‖s‖`.
-/

open Set
open scoped Nat

namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- With normalized constants `L_j ≥ 1` (`j ≤ q`), `L_f = max_{j ≤ q} L_j ≥ 1`. -/
theorem one_le_lipMax {L : ℕ → ℝ} {q : ℕ} (hL : ∀ j ≤ q, 1 ≤ L j) : 1 ≤ lipMax L q :=
  (hL 0 (Nat.zero_le q)).trans (le_lipMax (Nat.zero_le q))

end Optimization

namespace LipschitzDerivsAnchored

open Optimization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {C A : Set E} {q : ℕ}
  {L : ℕ → ℝ}

/-- Taylor's theorem anchored at `x ∈ A` for the orders `j ≤ q` of
`LipschitzDerivsAnchored f C A 0 q L` ((A.19)): for `x + s ∈ C`,
`|f(x + s) - (f(x) - ΔT_{f,j}(x, s))| ≤ L_j/(j+1)! ‖s‖^{j+1}`. -/
theorem abs_sub_taylorDecrement_le_of_le (hf : LipschitzDerivsAnchored f C A 0 q L) {j : ℕ}
    (hj : j ≤ q) {x s : E} (hx : x ∈ A) (hxs : x + s ∈ C) :
    |f (x + s) - (f x - (ftaylorSeries ℝ f x).taylorDecrement j s)| ≤
      L j / ((j + 1)! : ℝ) * ‖s‖ ^ (j + 1) :=
  hf.abs_sub_taylorDecrement_le (Finset.mem_Icc.2 ⟨Nat.zero_le j, hj⟩) hx hxs

/-- The anchored condition of order `j ≤ q` at an anchor `x ∈ A`. -/
theorem lipschitzAt_of_le (hf : LipschitzDerivsAnchored f C A 0 q L) {j : ℕ} (hj : j ≤ q) {x : E}
    (hx : x ∈ A) :
    ∀ y ∈ C, ‖iteratedFDeriv ℝ j f y - iteratedFDeriv ℝ j f x‖ ≤ L j * ‖y - x‖ :=
  hf.lipschitzAt (Finset.mem_Icc.2 ⟨Nat.zero_le j, hj⟩) hx

/-- With `A = C`, the derivative of order `j ≤ q` is Lipschitz on `C`. -/
theorem lipschitzOn_of_le (hf : LipschitzDerivsAnchored f C C 0 q L) {j : ℕ} (hj : j ≤ q) :
    IteratedFDerivLipschitzOn f j (L j) C :=
  hf.lipschitzOn (Finset.mem_Icc.2 ⟨Nat.zero_le j, hj⟩)

/-- **(13.1.24) at the anchors**: `‖∇^i f(x)‖ ≤ L_{i-1} ≤ L_f` for `i ∈ [1, q]` and `x ∈ A`. -/
theorem norm_iteratedFDeriv_le_lipMax (hf : LipschitzDerivsAnchored f C A 0 q L)
    (hL : ∀ j ≤ q, 1 ≤ L j) {i : ℕ} (hi : i ∈ Finset.Icc 1 q) {x : E} (hx : x ∈ A) :
    ‖iteratedFDeriv ℝ i f x‖ ≤ lipMax L q := by
  obtain ⟨hi1, hiq⟩ := Finset.mem_Icc.1 hi
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  have hm : m ≤ q := by omega
  exact (hf.norm_iteratedFDeriv_le (Finset.mem_Icc.2 ⟨Nat.zero_le m, hm⟩)
    (zero_le_one.trans (hL m hm)) hx).trans (le_lipMax hm)

/-- **(13.1.24), (13.1.63) at the anchors**: inexact derivatives at `x ∈ A` within `κ_{∇,i} h_i`
of the exact ones, with `0 ≤ κ_{∇,i}`, `0 ≤ h_i ≤ κ_h`, satisfy
`‖∇̄^i f(x)‖ ≤ L_f + κ_{∇,max} κ_h`. -/
theorem norm_le_of_jetApprox (hf : LipschitzDerivsAnchored f C A 0 q L) (hL : ∀ j ≤ q, 1 ≤ L j)
    {D : FormalMultilinearSeries ℝ E ℝ} {κg hh : ℕ → ℝ} {κh : ℝ} {x : E} (hx : x ∈ A)
    (hD : JetApprox (ftaylorSeries ℝ f x) D q (fun i => κg i * hh i))
    (hκ : ∀ i ∈ Finset.Icc 1 q, 0 ≤ κg i) (hh0 : ∀ i ∈ Finset.Icc 1 q, 0 ≤ hh i)
    (hhκ : ∀ i ∈ Finset.Icc 1 q, hh i ≤ κh) {i : ℕ} (hi : i ∈ Finset.Icc 1 q) :
    ‖D i‖ ≤ lipMax L q + ordMax q κg * κh :=
  norm_le_add_mul_of_jetApprox hD hi (hf.norm_iteratedFDeriv_le_lipMax hL hi hx) (hκ i hi)
    (le_ordMax hi) (hh0 i hi) (hhκ i hi)

end LipschitzDerivsAnchored

namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The decrement is small for short steps: if `‖D_i‖ ≤ Lb` for `i ∈ [1, j]`, `0 ≤ Lb` and
`‖s‖ ≤ 1`, then `ΔT_j(s) ≤ 2 Lb ‖s‖` (sum bound (A.34)). -/
theorem taylorDecrement_le_two_mul {D : FormalMultilinearSeries ℝ E ℝ} {j : ℕ} {Lb : ℝ}
    (hLb : 0 ≤ Lb) (hD : ∀ i ∈ Finset.Icc 1 j, ‖D i‖ ≤ Lb) {s : E} (hs : ‖s‖ ≤ 1) :
    D.taylorDecrement j s ≤ 2 * Lb * ‖s‖ := by
  refine (le_abs_self _).trans ((D.abs_taylorDecrement_le j s).trans ?_)
  calc ∑ i ∈ Finset.Icc 1 j, ‖D i‖ * ‖s‖ ^ i / i !
      ≤ ∑ i ∈ Finset.Icc 1 j, Lb * (‖s‖ ^ i / i !) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [mul_div_assoc]
        gcongr
        exact hD i hi
    _ = Lb * ∑ i ∈ Finset.Icc 1 j, ‖s‖ ^ i / i ! := by rw [Finset.mul_sum]
    _ ≤ Lb * (2 * ‖s‖) := by gcongr; exact sum_pow_div_factorial_le_two_mul (norm_nonneg s) hs j
    _ = 2 * Lb * ‖s‖ := by ring

/-- A sequence that does not increase on `[0, k]` stays below its first term:
`u_{i+1} ≤ u_i` for `i < k` gives `u_k ≤ u_0`. -/
theorem le_zero_of_forall_succ_le {u : ℕ → ℝ} {k : ℕ} (h : ∀ i < k, u (i + 1) ≤ u i) :
    u k ≤ u 0 := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact (h k k.lt_succ_self).trans (ih fun i hi => h i (hi.trans k.lt_succ_self))

end Optimization

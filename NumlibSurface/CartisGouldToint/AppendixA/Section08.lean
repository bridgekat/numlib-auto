import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.Analysis.Calculus.LipschitzIteratedFDeriv
import Numlib.Analysis.Calculus.Taylor

/-!
# Cartis–Gould–Toint §A.8: Taylor's theorem

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §A.8.

Univariate statements use `ψ : ℝ → ℝ` and the Taylor approximation
`τ_k(t, h) = ψ(t) + ∑_{i=1}^k ψ^{(i)}(t) h^i / i!` (`taylorApprox`), whose derivatives are taken
within the interval on which `ψ` is assumed smooth (one-sided at its endpoints). Multivariate
statements are on `ℝⁿ = EuclideanSpace ℝ (Fin n)`: `∇^j f(x)` is `iteratedFDeriv ℝ j f x`, the
tensor norm (A.7) is the operator norm of multilinear maps, `T_{f,p}(x, s)` of (A.10) is
`taylorPolynomial f p x s`, `∇^j_s T_{f,p}(x, s)` is
`iteratedFDeriv ℝ j (taylorPolynomial f p x) s`, and `(k + β)! = ∏_{ℓ=1}^k (ℓ + β)` is
`holderFactorial k β`.

## Main results

* `theorem_A_8_1` — Taylor's theorem with integral remainder (A.9).
* `theorem_A_8_2` — Taylor's theorem with Lagrange remainder.
* `theorem_A_8_3` — remainder bounds (A.14), (A.15) for a Hölder `p`-th derivative (A.13);
  `eq_A_16` — the Beta integral (A.16) used in its proof.
* `corollary_A_8_4` — remainder bounds (A.19), (A.20) for a Lipschitz `p`-th derivative (A.18).
* `theorem_A_8_5` — `∇^p f` is `L`-Lipschitz iff `‖∇^{p+1} f‖ ≤ L` (A.21).

## Deviations from the book

* Theorem A.8.5 assumes `L ≥ 0`. The book leaves the sign of the Lipschitz constant implicit; on
  `ℝ⁰` with `L < 0` the Lipschitz condition holds trivially while (A.21) fails.
* Theorem A.8.1 is stated for `k ≥ 1` and `h ≥ 0` (the book leaves both implicit: the
  remainder involves `(k-1)!` and the interval `[t, t + h]`).
* Theorem A.8.2 gives `ξ` strictly between `t` and `t + h` (`uIoo`), for either sign of `h`;
  this needs `h ≠ 0` (the open interval is empty when `h = 0`, where the identity holds with
  `ξ = t`).
* Theorem A.8.3: the proof of (A.15) displays the constant `(p-j+1)!/(p-j+β)!`; the stated
  `1/(p-j+β)!` is what is proved. The backbone form also covers `j = 0` and every `β ≥ 0`.
* (A.12) is stated for `f` merely `n` times differentiable at `x`; the library proves it for `f`
  of class `C^n` at `x` (`Numlib.Analysis.Calculus.MultivariateTaylor.Peano`).
-/

open Set
open scoped Nat

namespace CartisGouldToint.AppendixA

/-! ### Univariate Taylor theorems -/

/-- The `k`-th degree Taylor approximation `τ_k(t, h) = ψ(t) + ∑_{i=1}^k (1/i!) ψ^{(i)}(t) h^i`
of `ψ(t + h)` about `t` ([cartis2022evaluation], Theorem A.8.1), the derivatives `ψ^{(i)}` being
taken within the set `I` (the interval on which `ψ` is smooth). -/
noncomputable def taylorApprox (ψ : ℝ → ℝ) (I : Set ℝ) (k : ℕ) (t h : ℝ) : ℝ :=
  ψ t + ∑ i ∈ Finset.Icc 1 k, (i ! : ℝ)⁻¹ * iteratedDerivWithin i ψ I t * h ^ i

/-- `τ_k(t, h)` is Mathlib's Taylor polynomial `taylorWithinEval ψ k I t` evaluated at `t + h`. -/
theorem taylorApprox_eq_taylorWithinEval (ψ : ℝ → ℝ) (I : Set ℝ) (k : ℕ) (t h : ℝ) :
    taylorApprox ψ I k t h = taylorWithinEval ψ k I t (t + h) := by
  rw [taylor_within_apply, Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos k), Nat.succ_eq_add_one,
    Finset.Ico_add_one_right_eq_Icc, zero_add, taylorApprox]
  simp only [add_sub_cancel_left, smul_eq_mul]
  congr 1
  · simp
  · exact Finset.sum_congr rfl fun i _ => by ring

/-- **Theorem A.8.1 (Taylor's theorem for a univariate function)** of [cartis2022evaluation].
If `k ≥ 1`, `h ≥ 0` and `ψ` is `k` times continuously differentiable on `[t, t + h]`, then (A.9)
`ψ(t + h) - τ_k(t, h) = 1/(k-1)! ∫_0^h (h - ξ)^{k-1} (ψ^{(k)}(t + ξ) - ψ^{(k)}(t)) dξ`. -/
theorem theorem_A_8_1 {ψ : ℝ → ℝ} {k : ℕ} {t h : ℝ} (hk : 1 ≤ k) (hh : 0 ≤ h)
    (hψ : ContDiffOn ℝ k ψ (Icc t (t + h))) :
    ψ (t + h) - taylorApprox ψ (Icc t (t + h)) k t h =
      1 / ((k - 1)! : ℝ) * ∫ ξ in (0 : ℝ)..h, (h - ξ) ^ (k - 1) *
        (iteratedDerivWithin k ψ (Icc t (t + h)) (t + ξ) -
          iteratedDerivWithin k ψ (Icc t (t + h)) t) := by
  rw [taylorApprox_eq_taylorWithinEval, one_div]
  exact taylor_integral_remainder_sub hk hh hψ

/-- **Theorem A.8.2 (Univariate Taylor's theorem, Lagrange form)** of [cartis2022evaluation].
If `ψ` is `k + 1` times continuously differentiable on the interval between `t` and `t + h`,
`h ≠ 0`, then there is `ξ` strictly between `t` and `t + h` with
`ψ(t + h) - τ_k(t, h) = ψ^{(k+1)}(ξ) h^{k+1}/(k+1)!`. (For `h = 0` both sides vanish with `ξ = t`;
the hypothesis `h ≠ 0` is needed only for `ξ` to lie in the open interval.) -/
theorem theorem_A_8_2 {ψ : ℝ → ℝ} {k : ℕ} {t h : ℝ} (hh : h ≠ 0)
    (hψ : ContDiffOn ℝ (k + 1) ψ (uIcc t (t + h))) :
    ∃ ξ ∈ uIoo t (t + h), ψ (t + h) - taylorApprox ψ (uIcc t (t + h)) k t h =
      iteratedDeriv (k + 1) ψ ξ * h ^ (k + 1) / ((k + 1)! : ℝ) := by
  obtain ⟨ξ, hξ, e⟩ :=
    exists_taylorWithinEval_add_iteratedDeriv_mul (fun e => hh (by linarith)) hψ
  refine ⟨ξ, hξ, ?_⟩
  rw [taylorApprox_eq_taylorWithinEval, e]
  simp only [add_sub_cancel_left]

/-! ### Multivariate Taylor theorems -/

variable {n : ℕ}

/-- **(A.16)** of [cartis2022evaluation]: for `k ≥ 1` and `β ∈ [0, 1]`,
`∫_0^1 ξ^β (1 - ξ)^{k-1} dξ = (k-1)!/(k+β)!`. -/
theorem eq_A_16 {k : ℕ} (hk : 1 ≤ k) {β : ℝ} (hβ0 : 0 ≤ β) (_hβ1 : β ≤ 1) :
    ∫ ξ in (0 : ℝ)..1, ξ ^ β * (1 - ξ) ^ (k - 1) = ((k - 1)! : ℝ) / holderFactorial k β :=
  integral_rpow_mul_one_sub_pow hk hβ0

/-- **Theorem A.8.3 (Taylor's theorem for a multivariate Hölder function)** of
[cartis2022evaluation]. Let `C ⊆ ℝⁿ` be convex, `D ⊇ C` open, `f` `p` times continuously
differentiable on `D`, and let `∇^p f` be Hölder continuous on `C` with constant `H` and
exponent `β ∈ [0, 1]` (A.13). Then for `x, x + s ∈ C`,
(A.14) `|f(x + s) - T_{f,p}(x, s)| ≤ H/(p+β)! ‖s‖^{p+β}`, and
(A.15) `‖∇^j f(x + s) - ∇^j_s T_{f,p}(x, s)‖ ≤ H/(p-j+β)! ‖s‖^{p-j+β}` for `j ∈ [1 : p]`. -/
theorem theorem_A_8_3 {C D : Set (EuclideanSpace ℝ (Fin n))} (hC : Convex ℝ C) (hD : IsOpen D)
    (hCD : C ⊆ D) {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} (hf : ContDiffOn ℝ p f D)
    {H β : ℝ} (hβ0 : 0 ≤ β) (_hβ1 : β ≤ 1)
    (hH : ∀ x ∈ C, ∀ y ∈ C,
      ‖iteratedFDeriv ℝ p f x - iteratedFDeriv ℝ p f y‖ ≤ H * ‖x - y‖ ^ β)
    {x s : EuclideanSpace ℝ (Fin n)} (hx : x ∈ C) (hxs : x + s ∈ C) :
    |f (x + s) - taylorPolynomial f p x s| ≤ H / holderFactorial p β * ‖s‖ ^ ((p : ℝ) + β) ∧
      ∀ j, 1 ≤ j → j ≤ p → ‖iteratedFDeriv ℝ j f (x + s) -
          iteratedFDeriv ℝ j (taylorPolynomial f p x) s‖ ≤
        H / holderFactorial (p - j) β * ‖s‖ ^ (((p - j : ℕ) : ℝ) + β) := by
  have hf' : ∀ y ∈ C, ContDiffAt ℝ p f y := fun y hy => hf.contDiffAt (hD.mem_nhds (hCD hy))
  have hH' : IteratedFDerivHolderOn f p H β C := iteratedFDerivHolderOn_iff.2 hH
  exact ⟨abs_sub_taylorPolynomial_le_of_holder hC hf' hβ0 hH' hx hxs, fun _ _ hj =>
    norm_iteratedFDeriv_sub_taylorPolynomial_le_of_holder hC hf' hβ0 hH' hx hxs hj⟩

/-- **Corollary A.8.4 (Taylor's theorem for a multivariate Lipschitz function)** of
[cartis2022evaluation]. Let `C ⊆ ℝⁿ` be convex, `D ⊇ C` open, `f` `p` times continuously
differentiable on `D`, and let `∇^p f` be Lipschitz continuous on `C` with constant `L` (A.18).
Then for `x, x + s ∈ C`,
(A.19) `|f(x + s) - T_{f,p}(x, s)| ≤ L/(p+1)! ‖s‖^{p+1}`, and
(A.20) `‖∇^j f(x + s) - ∇^j_s T_{f,p}(x, s)‖ ≤ L/(p-j+1)! ‖s‖^{p-j+1}` for `j ∈ [1 : p]`. -/
theorem corollary_A_8_4 {C D : Set (EuclideanSpace ℝ (Fin n))} (hC : Convex ℝ C)
    (hD : IsOpen D) (hCD : C ⊆ D) {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ}
    (hf : ContDiffOn ℝ p f D) {L : ℝ}
    (hL : ∀ x ∈ C, ∀ y ∈ C, ‖iteratedFDeriv ℝ p f x - iteratedFDeriv ℝ p f y‖ ≤ L * ‖x - y‖)
    {x s : EuclideanSpace ℝ (Fin n)} (hx : x ∈ C) (hxs : x + s ∈ C) :
    |f (x + s) - taylorPolynomial f p x s| ≤ L / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) ∧
      ∀ j, 1 ≤ j → j ≤ p → ‖iteratedFDeriv ℝ j f (x + s) -
          iteratedFDeriv ℝ j (taylorPolynomial f p x) s‖ ≤
        L / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) := by
  have hf' : ∀ y ∈ C, ContDiffAt ℝ p f y := fun y hy => hf.contDiffAt (hD.mem_nhds (hCD hy))
  have hL' : IteratedFDerivLipschitzOn f p L C := iteratedFDerivLipschitzOn_iff.2 hL
  exact ⟨abs_sub_taylorPolynomial_le_of_lipschitz hC hf' hL' hx hxs, fun _ _ hj =>
    norm_iteratedFDeriv_sub_taylorPolynomial_le_of_lipschitz hC hf' hL' hx hxs hj⟩

/-- **Theorem A.8.5 (Lipschitz if and only if bounded derivatives)** of [cartis2022evaluation].
Let `C ⊆ ℝⁿ` be open and convex and `f` `p + 1` times continuously differentiable on `C`. Then
`∇^p f` is Lipschitz continuous on `C` with constant `L` (A.18) iff `‖∇^{p+1} f(x)‖ ≤ L` for all
`x ∈ C` (A.21). (The Lipschitz constant is assumed nonnegative.) -/
theorem theorem_A_8_5 {C : Set (EuclideanSpace ℝ (Fin n))} (hCo : IsOpen C) (hC : Convex ℝ C)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} (hf : ContDiffOn ℝ (p + 1) f C) {L : ℝ}
    (hL : 0 ≤ L) :
    (∀ x ∈ C, ∀ y ∈ C, ‖iteratedFDeriv ℝ p f x - iteratedFDeriv ℝ p f y‖ ≤ L * ‖x - y‖) ↔
      ∀ x ∈ C, ‖iteratedFDeriv ℝ (p + 1) f x‖ ≤ L := by
  rw [← iteratedFDerivLipschitzOn_iff]
  exact iteratedFDerivLipschitzOn_iff_norm_le hCo hC hL fun y hy =>
    hf.contDiffAt (hCo.mem_nhds hy)

end CartisGouldToint.AppendixA

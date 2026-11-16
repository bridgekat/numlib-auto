/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Numlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Numlib.Approximation.Hermite

/-!
# Piecewise Hermite interpolation with uniform derivative bounds

A jet of order $p$ at a point is a list $a_0, \dots, a_p$ of prescribed values of a function and its
first $p$ derivatives. This file constructs two-point Hermite interpolants of degree $2p + 1$ and
their piecewise versions on the real line, with bounds on the derivatives that depend only on $p$
and on a consistency constant $\kappa$ of the jets. The construction follows Appendix A.9 of
[cartis2022evaluation]. It is the tool with which the slow-convergence examples of
[cartis2022evaluation] are built: jets prescribed at a sequence of points are interpolated by a
function whose derivatives are bounded and Lipschitz, with constants independent of the number and
the spacing of the points.

The consistency condition (A.30) and (A.32) asks that the jet $b$ at the right end $s$ of an
interval agrees, up to $\kappa s^{p-j+1}$, with the Taylor expansion of degree $p$ of the jet $a$ at
the left end: $$\Big| b_j - \sum_{i=j}^p \frac{a_i\, s^{i-j}}{(i - j)!} \Big| \le \kappa\,
s^{p-j+1}, \qquad j \le p.$$ Taylor's theorem gives exactly this for the jets of a function whose
derivative of order $p$ is $\kappa$-Lipschitz.

## Main results

* `Hermite.exists_twoPoint_interpolant`: Theorem A.9.1 of [cartis2022evaluation]. For consistent
  jets at $0$ and $s$, there is a polynomial $\pi$ of degree at most $2p + 1$ with these jets and
  with $|\pi^{(j)}(\tau)| \le \sum_{i=j}^p |a_i| s^{i-j}/(i - j)! + C\kappa s^{p+1-j}$ on $[0, s]$
  for $j \le p + 1$, where $C$ depends only on $p$; in particular $\pi^{(p)}$ is $C\kappa$-Lipschitz
  on $[0, s]$.
* `Hermite.exists_twoPoint_interpolant_bounded`: the second part of Theorem A.9.1. If also
  $|a_j| \le \kappa$ and $s \le \kappa$, the bounds depend only on $p$ and $\kappa$.
* `Hermite.exists_contDiff_interpolating_jets`: Theorem A.9.2. Consistent jets at nodes
  $x_0 < \dots < x_K$ are interpolated by a $C^p$ function on $\mathbb{R}$ whose derivative of order
  $p$ is $L$-Lipschitz, where $L$ depends only on $p$ and $\kappa$.
* `Hermite.exists_contDiff_interpolating_jets_bounded`: Theorem A.9.2, bounded version. If also the
  jets are bounded by $\kappa$ and the gaps are at most $\kappa$, the interpolant can be chosen with
  all derivatives of order at most $p$ bounded by a constant that depends only on $p$ and $\kappa$,
  and constant outside $[x_0 - 1, x_K + 1]$. The bound on the last jet follows from the consistency
  condition; `Hermite.exists_contDiff_interpolating_jets_bounded_of_forall_le` assumes it, and
  allows $K = 0$.

## Implementation notes

* The two-point interpolant is written as $T(\tau) + s^{p+1} R(\tau/s)$, with $T$ the Taylor
  polynomial of the left jet and $R = \sum_l D_l H_l$ a combination of fixed Hermite basis
  polynomials on $[0, 1]$ (zero jet at $0$, unit jets at $1$). The weights $D_j = r_j/s^{p+1-j}$ are
  bounded by $\kappa$. This avoids the explicit matrix $A_p$ of the source.
* Pieces are glued with `Hermite.glue`, the function equal to $u$ on $(-\infty, a]$ and to $v$ on
  $(a, \infty)$; `Hermite.glue3` glues three functions at $0$ and $1$. When the jets of order $p$ of
  $u$ and $v$ agree at $a$, the glued function is again $C^p$ (`Hermite.contDiff_glue`).
* In the bounded version the outer pieces are Hermite pieces of length $1$ towards constant jets, as
  in the source, with the consistency constant $(p + 2)\kappa$.
* In Theorem A.9.2 the steps $s_k > 0$ are indexed by $k < k_e$, and the bound holds for all
  $x \in \mathbb{R}$.
* A jet is a function `ℕ → ℝ`, of which only the values at $0, \dots, p$ are used, and a family of
  jets at the nodes is a function `F : ℕ → ℕ → ℝ`, with $F_{k,j}$ the prescribed derivative of order
  $j$ at $x_k$.
-/

open Polynomial
open scoped Polynomial

namespace Hermite

/-! ### Taylor polynomials of jets -/

/-- The **Taylor polynomial** of degree $p$ of a jet $a$: $$\sum_{i=0}^p \frac{a_i}{i!} X^i.$$
-/
noncomputable def jetTaylorPoly (p : ℕ) (a : ℕ → ℝ) : ℝ[X] :=
  ∑ i ∈ Finset.range (p + 1), C (a i / i.factorial) * X ^ i

/-- The derivative of order $j$ of the Taylor polynomial of degree $p$ of a jet $a$, at $\tau$, is
$$\sum_{i=j}^p \frac{a_i\, \tau^{i-j}}{(i - j)!}.$$
-/
theorem eval_iterate_derivative_jetTaylorPoly (p : ℕ) (a : ℕ → ℝ) (j : ℕ) (τ : ℝ) :
    (derivative^[j] (jetTaylorPoly p a)).eval τ =
      ∑ i ∈ Finset.Icc j p, a i * τ ^ (i - j) / (i - j).factorial := by
  simp only [jetTaylorPoly, iterate_derivative_sum, iterate_derivative_C_mul,
    iterate_derivative_X_pow_eq_C_mul, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  symm
  calc ∑ i ∈ Finset.Icc j p, a i * τ ^ (i - j) / ((i - j).factorial : ℝ)
      = ∑ i ∈ Finset.Icc j p, a i / i.factorial * ((i.descFactorial j : ℝ) * τ ^ (i - j)) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hji := (Finset.mem_Icc.1 hi).1
        have h : ((i - j).factorial : ℝ) * i.descFactorial j = i.factorial := by
          exact_mod_cast Nat.factorial_mul_descFactorial hji
        have hf : ((i - j).factorial : ℝ) ≠ 0 := by positivity
        have hd : (i.descFactorial j : ℝ) ≠ 0 :=
          Nat.cast_ne_zero.2 (by rw [Ne, Nat.descFactorial_eq_zero_iff_lt]; omega)
        rw [← h]
        field_simp
    _ = _ := by
        refine Finset.sum_subset (fun i hi => ?_) fun i hi hni => ?_
        · simp only [Finset.mem_Icc, Finset.mem_range] at hi ⊢
          omega
        · simp only [Finset.mem_Icc, Finset.mem_range, not_and_or, not_le] at hi hni
          have : i < j := by omega
          rw [Nat.descFactorial_eq_zero_iff_lt.2 this]
          simp

/-- For $j \le p$, the Taylor sum of a jet at the displacement $0$ returns the jet:
$\sum_{i=j}^p a_i\, 0^{i-j}/(i - j)! = a_j$. -/
theorem sum_Icc_zero_pow (a : ℕ → ℝ) {j p : ℕ} (hj : j ≤ p) :
    ∑ i ∈ Finset.Icc j p, a i * (0 : ℝ) ^ (i - j) / (i - j).factorial = a j := by
  rw [Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    have : i - j ≠ 0 := by
      have := (Finset.mem_Icc.1 hi).1
      omega
    simp [zero_pow this]
  · intro h
    exact absurd (Finset.mem_Icc.2 ⟨le_rfl, hj⟩) h

/-- The jet of the constant function $c$: $c$ at order $0$, and $0$ at every higher order. -/
def constJet (c : ℝ) (i : ℕ) : ℝ := if i = 0 then c else 0

/-- The Taylor sum of the jet of a constant is that jet, at every displacement $\tau$:
$\sum_{i=j}^p c_i\, \tau^{i-j}/(i - j)! = c_j$ for the jet $c_i$ of the constant $c$. -/
theorem sum_Icc_constJet (c : ℝ) (j p : ℕ) (τ : ℝ) :
    ∑ i ∈ Finset.Icc j p, constJet c i * τ ^ (i - j) / (i - j).factorial = constJet c j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [Finset.sum_eq_single 0]
    · simp
    · intro i _ hi
      simp [constJet, hi]
    · intro h
      exact absurd (Finset.mem_Icc.2 ⟨le_rfl, Nat.zero_le p⟩) h
  · rw [Finset.sum_eq_zero]
    · simp [constJet, hj.ne']
    · intro i hi
      have : i ≠ 0 := by
        have := (Finset.mem_Icc.1 hi).1
        omega
      simp [constJet, this]

/-- If $|c| \le \kappa$, every entry of the jet of the constant $c$ has absolute value at most
$\kappa$. -/
theorem abs_constJet_le {c κ : ℝ} (hc : |c| ≤ κ) (i : ℕ) : |constJet c i| ≤ κ := by
  unfold constJet
  split_ifs
  · exact hc
  · simpa using (abs_nonneg c).trans hc

/-! ### Polynomial pieces -/

/-- The derivative of order $j$ of the rescaled polynomial $q(cX)$ is $c^j q^{(j)}(cX)$. -/
theorem iterate_derivative_comp_C_mul_X (q : ℝ[X]) (c : ℝ) (j : ℕ) :
    derivative^[j] (q.comp (C c * X)) = C (c ^ j) * (derivative^[j] q).comp (C c * X) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, derivative_C_mul, derivative_comp, derivative_C_mul_X,
      Function.iterate_succ_apply', pow_succ, C_mul]
    ring

/-- For a polynomial $\pi$ and $x_0 \in \mathbb{R}$, the function $t \mapsto \pi(t - x_0)$ is
smooth. -/
theorem contDiff_eval_sub (π : ℝ[X]) (x₀ : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n fun t => π.eval (t - x₀) := by
  have h : ContDiff ℝ n fun t => π.eval t := by
    simpa [coe_aeval_eq_eval] using π.contDiff_aeval (𝕜 := ℝ) n
  exact h.comp (contDiff_id.sub contDiff_const)

/-- The derivative of order $j$ of $t \mapsto \pi(t - x_0)$ is $t \mapsto \pi^{(j)}(t - x_0)$. -/
theorem iteratedDeriv_eval_sub (π : ℝ[X]) (x₀ : ℝ) (j : ℕ) :
    iteratedDeriv j (fun t => π.eval (t - x₀)) = fun t => (derivative^[j] π).eval (t - x₀) := by
  rw [iteratedDeriv_comp_sub_const j (fun t => π.eval t) x₀, Polynomial.iteratedDeriv_eval]

/-- The mean value bound for the derivatives of a polynomial: if $|\pi^{(j+1)}| \le M$ on $[a, b]$,
then $|\pi^{(j)}(\tau_1) - \pi^{(j)}(\tau_2)| \le M |\tau_1 - \tau_2|$ for
$\tau_1, \tau_2 \in [a, b]$. -/
theorem abs_eval_iterate_derivative_sub_le (π : ℝ[X]) (j : ℕ) {a b M : ℝ}
    (hM : ∀ τ ∈ Set.Icc a b, |(derivative^[j + 1] π).eval τ| ≤ M) {τ₁ τ₂ : ℝ}
    (h₁ : τ₁ ∈ Set.Icc a b) (h₂ : τ₂ ∈ Set.Icc a b) :
    |(derivative^[j] π).eval τ₁ - (derivative^[j] π).eval τ₂| ≤ M * |τ₁ - τ₂| := by
  have hd : ∀ τ ∈ Set.Icc a b, HasDerivWithinAt (fun τ => (derivative^[j] π).eval τ)
      ((derivative^[j + 1] π).eval τ) (Set.Icc a b) τ := fun τ _ => by
    rw [Function.iterate_succ_apply']
    exact (Polynomial.hasDerivAt _ τ).hasDerivWithinAt
  have := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le hd
    (fun τ hτ => by rw [Real.norm_eq_abs]; exact hM τ hτ) h₂ h₁
  simpa [Real.norm_eq_abs] using this

/-! ### Two-point Hermite interpolation -/

/-- **The Hermite basis on $[0, 1]$.** For all $p$ and $l$ there is a polynomial $H$ of degree less
than $2p + 2$ with $H^{(j)}(0) = 0$ for all $j \le p$, and $H^{(j)}(1) = 1$ if $j = l$ and
$H^{(j)}(1) = 0$ otherwise, for all $j \le p$. -/
theorem exists_unitJet (p l : ℕ) : ∃ H : ℝ[X], H.degree < ((2 * p + 2 : ℕ) : WithBot ℕ) ∧
    ∀ j ≤ p, (derivative^[j] H).eval 0 = 0 ∧
      (derivative^[j] H).eval 1 = if j = l then 1 else 0 := by
  have hx : Function.Injective (![0, 1] : Fin 2 → ℝ) := by
    intro i k h
    fin_cases i <;> fin_cases k <;> simp_all
  obtain ⟨H, ⟨hdeg, hH⟩, -⟩ := isUnisolvent hx (m := fun _ => p) (M := 2 * p + 2)
    (by simp; ring) ![fun _ => 0, fun j => if j = l then 1 else 0]
  exact ⟨H, hdeg, fun j hj => ⟨by simpa using hH 0 j hj, by simpa using hH 1 j hj⟩⟩

/-- **Two-point Hermite interpolation with uniform bounds.** For every $p \in \mathbb{N}$ there is a
constant $C \ge 0$ with the following property. Let $s > 0$, $\kappa \in \mathbb{R}$, and let
$a, b$ be jets with the consistency condition (A.30) $$\Big| b_j - \sum_{i=j}^p \frac{a_i\,
s^{i-j}}{(i - j)!} \Big| \le \kappa\, s^{p-j+1}, \qquad j \le p.$$ Then there is a polynomial
$\pi$ of degree at most $2p + 1$ such that:

* $\pi^{(j)}(0) = a_j$ and $\pi^{(j)}(s) = b_j$ for $j \le p$ (A.24);
* $|\pi^{(j)}(\tau)| \le \sum_{i=j}^p |a_i|\, s^{i-j}/(i - j)! + C\kappa\, s^{p+1-j}$ for
  $\tau \in [0, s]$ and $j \le p + 1$ (A.27);
* $|\pi^{(p)}(\tau_1) - \pi^{(p)}(\tau_2)| \le C\kappa\, |\tau_1 - \tau_2|$ for
  $\tau_1, \tau_2 \in [0, s]$ (A.28).

This is Theorem A.9.1 of [cartis2022evaluation].

The constant $C$ depends only on $p$: it is chosen before $s$, $\kappa$, $a$ and $b$. -/
theorem exists_twoPoint_interpolant (p : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (s κ : ℝ) (a b : ℕ → ℝ), 0 < s →
      (∀ j ≤ p, |b j - ∑ i ∈ Finset.Icc j p, a i * s ^ (i - j) / (i - j).factorial| ≤
        κ * s ^ (p - j + 1)) →
      ∃ π : ℝ[X], π.natDegree ≤ 2 * p + 1 ∧
        (∀ j ≤ p, (derivative^[j] π).eval 0 = a j) ∧
        (∀ j ≤ p, (derivative^[j] π).eval s = b j) ∧
        (∀ j ≤ p + 1, ∀ τ ∈ Set.Icc 0 s, |(derivative^[j] π).eval τ| ≤
          ∑ i ∈ Finset.Icc j p, |a i| * s ^ (i - j) / (i - j).factorial +
            C * κ * s ^ (p + 1 - j)) ∧
        ∀ τ₁ ∈ Set.Icc 0 s, ∀ τ₂ ∈ Set.Icc 0 s,
          |(derivative^[p] π).eval τ₁ - (derivative^[p] π).eval τ₂| ≤ C * κ * |τ₁ - τ₂| := by
  choose H hHdeg hH using exists_unitJet p
  have hbd : ∀ l j : ℕ, ∃ B, ∀ u ∈ Set.Icc (0 : ℝ) 1, ‖(derivative^[j] (H l)).eval u‖ ≤ B :=
    fun l j => isCompact_Icc.exists_bound_of_continuousOn
      (Polynomial.continuous _).continuousOn
  choose B hB using hbd
  set Cp : ℝ := ∑ l ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (p + 2), |B l j| with hCdef
  have hC : 0 ≤ Cp := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨Cp, hC, fun s κ a b hs hab => ?_⟩
  set r : ℕ → ℝ := fun j => b j - ∑ i ∈ Finset.Icc j p, a i * s ^ (i - j) / (i - j).factorial
  set D : ℕ → ℝ := fun j => r j / s ^ (p - j + 1)
  have hκ : 0 ≤ κ := by
    have h := (abs_nonneg _).trans (hab 0 (Nat.zero_le p))
    exact nonneg_of_mul_nonneg_left h (by positivity)
  have hD : ∀ j ≤ p, |D j| ≤ κ := fun j hj => by
    simp only [D, abs_div, abs_of_pos (pow_pos hs _)]
    rw [div_le_iff₀ (by positivity)]
    exact hab j hj
  set R : ℝ[X] := ∑ l ∈ Finset.range (p + 1), C (D l) * H l
  set π : ℝ[X] := jetTaylorPoly p a + C (s ^ (p + 1)) * R.comp (C s⁻¹ * X)
  have hpow : ∀ j ≤ p + 1, s ^ (p + 1) * s⁻¹ ^ j = s ^ (p + 1 - j) := fun j hj => by
    rw [pow_sub₀ _ hs.ne' hj, inv_pow]
  have hR : ∀ j u, (derivative^[j] R).eval u =
      ∑ l ∈ Finset.range (p + 1), D l * (derivative^[j] (H l)).eval u := fun j u => by
    simp [R, iterate_derivative_sum, iterate_derivative_C_mul, eval_finsetSum]
  have hπ : ∀ j τ, (derivative^[j] π).eval τ =
      ∑ i ∈ Finset.Icc j p, a i * τ ^ (i - j) / (i - j).factorial +
        s ^ (p + 1) * s⁻¹ ^ j * (derivative^[j] R).eval (s⁻¹ * τ) := fun j τ => by
    simp only [π, iterate_derivative_add, iterate_derivative_C_mul,
      iterate_derivative_comp_C_mul_X, eval_add, eval_mul, eval_C, eval_comp, eval_X,
      eval_iterate_derivative_jetTaylorPoly]
    ring
  refine ⟨π, ?_, fun j hj => ?_, fun j hj => ?_, fun j hj τ hτ => ?_, ?_⟩
  · -- degree
    have hR : R.natDegree ≤ 2 * p + 1 := by
      refine natDegree_sum_le_of_forall_le _ _ fun l _ => (natDegree_C_mul_le _ _).trans ?_
      have h := hHdeg l
      rw [Polynomial.degree_lt_iff_coeff_zero] at h
      refine natDegree_le_iff_coeff_eq_zero.2 fun N hN => h N ?_
      exact_mod_cast (show 2 * p + 2 ≤ N by exact_mod_cast hN)
    have hT : (jetTaylorPoly p a).natDegree ≤ 2 * p + 1 := by
      refine natDegree_sum_le_of_forall_le _ _ fun i hi => (natDegree_C_mul_le _ _).trans ?_
      rw [natDegree_X_pow]
      have := Finset.mem_range.1 hi
      omega
    refine (natDegree_add_le _ _).trans (max_le hT ((natDegree_C_mul_le _ _).trans ?_))
    refine (natDegree_comp_le).trans ?_
    have h1 : (C s⁻¹ * X : ℝ[X]).natDegree ≤ 1 :=
      (natDegree_C_mul_le _ _).trans natDegree_X_le
    calc R.natDegree * (C s⁻¹ * X : ℝ[X]).natDegree ≤ (2 * p + 1) * 1 :=
          Nat.mul_le_mul hR h1
      _ = 2 * p + 1 := by ring
  · -- left jet
    rw [hπ, mul_zero, hR, sum_Icc_zero_pow a hj]
    simp [(hH _ j hj).1]
  · -- right jet
    rw [hπ, hpow j (by omega), hR, inv_mul_cancel₀ hs.ne']
    have hsum : ∑ l ∈ Finset.range (p + 1), D l * (derivative^[j] (H l)).eval 1 = D j := by
      rw [Finset.sum_eq_single j]
      · simp [(hH j j hj).2]
      · intro l _ hl
        simp [(hH l j hj).2, Ne.symm hl]
      · intro h
        exact absurd (Finset.mem_range.2 (by omega)) h
    rw [hsum]
    simp only [D, r]
    rw [show p + 1 - j = p - j + 1 by omega]
    field_simp
    ring
  · -- derivative bounds
    rw [hπ, hpow j hj]
    have hu : s⁻¹ * τ ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨mul_nonneg (inv_nonneg.2 hs.le) hτ.1, ?_⟩
      rw [inv_mul_le_iff₀ hs, mul_one]
      exact hτ.2
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_div, abs_mul, abs_pow, Nat.abs_cast, abs_of_nonneg hτ.1]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hτ.1 hτ.2 _) (abs_nonneg _)) (by positivity)
    · rw [abs_mul, abs_of_pos (by positivity), hR, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ l ∈ Finset.range (p + 1), |D l * (derivative^[j] (H l)).eval (s⁻¹ * τ)|
          ≤ ∑ l ∈ Finset.range (p + 1), κ * ∑ j' ∈ Finset.range (p + 2), |B l j'| := by
            refine Finset.sum_le_sum fun l hl => ?_
            rw [abs_mul]
            refine mul_le_mul (hD l (by have := Finset.mem_range.1 hl; omega)) ?_
              (abs_nonneg _) hκ
            refine ((Real.norm_eq_abs _).symm.le.trans (hB l j _ hu)).trans
              ((le_abs_self _).trans ?_)
            exact Finset.single_le_sum (f := fun j' => |B l j'|) (fun _ _ => abs_nonneg _)
              (Finset.mem_range.2 (by omega))
        _ = Cp * κ := by rw [← Finset.mul_sum, hCdef, mul_comm]
  · -- Lipschitz `p`-th derivative
    intro τ₁ h₁ τ₂ h₂
    refine abs_eval_iterate_derivative_sub_le π p (fun τ hτ => ?_) h₁ h₂
    rw [hπ, hpow (p + 1) le_rfl, Nat.sub_self, pow_zero, one_mul, hR,
      Finset.Icc_eq_empty (by omega), Finset.sum_empty, zero_add]
    have hu : s⁻¹ * τ ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨mul_nonneg (inv_nonneg.2 hs.le) hτ.1, ?_⟩
      rw [inv_mul_le_iff₀ hs, mul_one]
      exact hτ.2
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ l ∈ Finset.range (p + 1), |D l * (derivative^[p + 1] (H l)).eval (s⁻¹ * τ)|
        ≤ ∑ l ∈ Finset.range (p + 1), κ * ∑ j' ∈ Finset.range (p + 2), |B l j'| := by
          refine Finset.sum_le_sum fun l hl => ?_
          rw [abs_mul]
          refine mul_le_mul (hD l (by have := Finset.mem_range.1 hl; omega)) ?_
            (abs_nonneg _) hκ
          refine ((Real.norm_eq_abs _).symm.le.trans (hB l (p + 1) _ hu)).trans
            ((le_abs_self _).trans ?_)
          exact Finset.single_le_sum (f := fun j' => |B l j'|) (fun _ _ => abs_nonneg _)
            (Finset.mem_range.2 (by omega))
      _ = Cp * κ := by rw [← Finset.mul_sum, hCdef, mul_comm]

/-! ### Gluing two functions at a point -/

/-- The function **glued** at $a$ from $u$ and $v$: it equals $u(t)$ for $t \le a$ and $v(t)$ for
$t > a$. -/
noncomputable def glue (a : ℝ) (u v : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t ≤ a then u t else v t

section Glue

variable {a t : ℝ} {u v : ℝ → ℝ}

/-- The glued function equals $u(t)$ for $t \le a$. -/
theorem glue_of_le (h : t ≤ a) : glue a u v t = u t := by
  simp [glue, h]

/-- The glued function equals $v(t)$ for $t > a$. -/
theorem glue_of_lt (h : a < t) : glue a u v t = v t := by
  simp [glue, not_le.2 h]

/-- If $u(a) = v(a)$, the glued function equals $v(t)$ for $t \ge a$. -/
theorem glue_of_ge (hav : u a = v a) (h : a ≤ t) : glue a u v t = v t := by
  rcases h.lt_or_eq with h | rfl
  · exact glue_of_lt h
  · rw [glue_of_le le_rfl, hav]

/-- Let $u$ and $v$ be differentiable on $\mathbb{R}$ with derivatives $u'$ and $v'$, and let
$u(a) = v(a)$ and $u'(a) = v'(a)$. Then the glued function is differentiable at every $t$, and
its derivative is the function glued from $u'$ and $v'$. -/
theorem hasDerivAt_glue {u' v' : ℝ → ℝ} (hu : ∀ t, HasDerivAt u (u' t) t)
    (hv : ∀ t, HasDerivAt v (v' t) t) (h0 : u a = v a) (h1 : u' a = v' a) (t : ℝ) :
    HasDerivAt (glue a u v) (glue a u' v' t) t := by
  rcases lt_trichotomy t a with ht | rfl | ht
  · rw [glue_of_le ht.le]
    exact (hu t).congr_of_eventuallyEq
      (Filter.mem_of_superset (Iio_mem_nhds ht) fun y hy => glue_of_le (le_of_lt hy))
  · rw [glue_of_le le_rfl]
    have h₁ : HasDerivWithinAt (glue t u v) (u' t) (Set.Iic t) t :=
      (hu t).hasDerivWithinAt.congr (fun y hy => glue_of_le hy) (glue_of_le le_rfl)
    have h₂ : HasDerivWithinAt (glue t u v) (u' t) (Set.Ici t) t := by
      rw [h1]
      exact (hv t).hasDerivWithinAt.congr (fun y hy => glue_of_ge h0 hy) (glue_of_ge h0 le_rfl)
    have := h₁.union h₂
    rwa [Set.Iic_union_Ici, hasDerivWithinAt_univ] at this
  · rw [glue_of_lt ht]
    exact (hv t).congr_of_eventuallyEq
      (Filter.mem_of_superset (Ioi_mem_nhds ht) fun y hy => glue_of_lt hy)

/-- If $u$ and $v$ are continuous and $u(a) = v(a)$, the glued function is continuous. -/
theorem continuous_glue (hu : Continuous u) (hv : Continuous v) (h : u a = v a) :
    Continuous (glue a u v) :=
  Continuous.if_le hu hv continuous_id continuous_const fun x hx => by
    rw [show x = a from hx]
    exact h

/-- **Gluing $C^n$ functions.** Let $u$ and $v$ be of class $C^n$ on $\mathbb{R}$,
$n \in \mathbb{N}$, with $u^{(j)}(a) = v^{(j)}(a)$ for all $j \le n$. Then the glued function is
of class $C^n$, and for $j \le n$ its derivative of order $j$ is the function glued from
$u^{(j)}$ and $v^{(j)}$. -/
theorem contDiff_glue {n : ℕ} (hu : ContDiff ℝ n u) (hv : ContDiff ℝ n v)
    (h : ∀ j ≤ n, iteratedDeriv j u a = iteratedDeriv j v a) :
    ContDiff ℝ n (glue a u v) ∧
      ∀ j ≤ n, iteratedDeriv j (glue a u v) = glue a (iteratedDeriv j u) (iteratedDeriv j v) := by
  have hd : ∀ k < n, ∀ b ∈ (Set.univ : Set ℝ),
      HasDerivAt (glue a (iteratedDeriv k u) (iteratedDeriv k v))
        (glue a (iteratedDeriv (k + 1) u) (iteratedDeriv (k + 1) v) b) b := by
    intro k hk b _
    have hdu : ∀ t, HasDerivAt (iteratedDeriv k u) (iteratedDeriv (k + 1) u t) t := fun t => by
      rw [iteratedDeriv_succ]
      exact ((hu.differentiable_iteratedDeriv k (by exact_mod_cast hk)) t).hasDerivAt
    have hdv : ∀ t, HasDerivAt (iteratedDeriv k v) (iteratedDeriv (k + 1) v t) t := fun t => by
      rw [iteratedDeriv_succ]
      exact ((hv.differentiable_iteratedDeriv k (by exact_mod_cast hk)) t).hasDerivAt
    exact hasDerivAt_glue hdu hdv (h k hk.le) (h (k + 1) hk) b
  have hc : ContinuousOn (glue a (iteratedDeriv n u) (iteratedDeriv n v)) Set.univ :=
    (continuous_glue (hu.continuous_iteratedDeriv n le_rfl) (hv.continuous_iteratedDeriv n le_rfl)
      (h n le_rfl)).continuousOn
  obtain ⟨h1, h2⟩ := contDiffOn_of_hasDerivAt_chain
    (G := fun k => glue a (iteratedDeriv k u) (iteratedDeriv k v)) isOpen_univ hd hc
  simp only [iteratedDeriv_zero] at h1 h2
  exact ⟨contDiffOn_univ.1 h1, fun j hj => funext fun t => h2 j hj (Set.mem_univ t)⟩

/-- **A Lipschitz bound for a glued function.** Let $s \subseteq \mathbb{R}$ be order-connected, let
$u$ be $L$-Lipschitz on $s \cap (-\infty, a]$ and $v$ be $L$-Lipschitz on $s \cap [a, \infty)$,
and let $u(a) = v(a)$. Then the glued function is $L$-Lipschitz on $s$. -/
theorem abs_glue_sub_le {s : Set ℝ} (hs : s.OrdConnected) {L : ℝ}
    (hu : ∀ x ∈ s, ∀ y ∈ s, x ≤ a → y ≤ a → |u x - u y| ≤ L * |x - y|)
    (hv : ∀ x ∈ s, ∀ y ∈ s, a ≤ x → a ≤ y → |v x - v y| ≤ L * |x - y|) (h : u a = v a)
    {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) : |glue a u v x - glue a u v y| ≤ L * |x - y| := by
  wlog hxy : x ≤ y generalizing x y
  · rw [abs_sub_comm, abs_sub_comm x]
    exact this hy hx (le_of_not_ge hxy)
  by_cases hya : y ≤ a
  · rw [glue_of_le (hxy.trans hya), glue_of_le hya]
    exact hu x hx y hy (hxy.trans hya) hya
  rw [not_le] at hya
  by_cases hxa : a ≤ x
  · rw [glue_of_ge h hxa, glue_of_ge h hya.le]
    exact hv x hx y hy hxa hya.le
  rw [not_le] at hxa
  have ha : a ∈ s := hs.out hx hy ⟨hxa.le, hya.le⟩
  rw [glue_of_le hxa.le, glue_of_lt hya]
  have h1 := hu x hx a ha hxa.le le_rfl
  have h2 := hv a ha y hy le_rfl hya.le
  rw [abs_of_nonpos (sub_nonpos.2 hxa.le)] at h1
  rw [abs_of_nonpos (sub_nonpos.2 hya.le)] at h2
  rw [abs_of_nonpos (sub_nonpos.2 hxy)]
  calc |u x - v y| = |(u x - u a) + (v a - v y)| := by rw [h]; ring_nf
    _ ≤ |u x - u a| + |v a - v y| := abs_add_le _ _
    _ ≤ L * -(x - a) + L * -(a - y) := add_le_add h1 h2
    _ = L * -(x - y) := by ring

end Glue

/-! ### Gluing three functions at $0$ and $1$ -/

/-- The function **glued** from three functions: it equals $l(t)$ for $t \le 0$, $m(t)$ for
$0 < t \le 1$, and $r(t)$ for $t > 1$. -/
noncomputable def glue3 (l m r : ℝ → ℝ) (t : ℝ) : ℝ :=
  glue 0 l (glue 1 m r) t

section Glue3

variable {l m r l' m' r' : ℝ → ℝ} {t : ℝ}

/-- The three-piece function equals $l(t)$ for $t \le 0$. -/
theorem glue3_of_nonpos (ht : t ≤ 0) : glue3 l m r t = l t :=
  glue_of_le ht

/-- If $l(0) = m(0)$, the three-piece function equals $m(t)$ for $t \in [0, 1]$. -/
theorem glue3_of_mem_Icc (h0 : l 0 = m 0) (ht : t ∈ Set.Icc (0 : ℝ) 1) : glue3 l m r t = m t := by
  rcases ht.1.lt_or_eq with h | rfl
  · rw [glue3, glue_of_lt h, glue_of_le ht.2]
  · rw [glue3_of_nonpos le_rfl, h0]

/-- If $m(1) = r(1)$, the three-piece function equals $r(t)$ for $t \ge 1$. -/
theorem glue3_of_one_le (h1 : m 1 = r 1) (ht : 1 ≤ t) : glue3 l m r t = r t := by
  rw [glue3, glue_of_lt (by linarith), glue_of_ge h1 ht]

/-- Let $l$, $m$ and $r$ be differentiable on $\mathbb{R}$ with derivatives $l'$, $m'$ and $r'$,
with $l(0) = m(0)$, $l'(0) = m'(0)$, $m(1) = r(1)$ and $m'(1) = r'(1)$. Then the three-piece
function is differentiable at every $t$, and its derivative is the three-piece function of $l'$,
$m'$ and $r'$. -/
theorem hasDerivAt_glue3 (hl : ∀ t, HasDerivAt l (l' t) t) (hm : ∀ t, HasDerivAt m (m' t) t)
    (hr : ∀ t, HasDerivAt r (r' t) t) (h0 : l 0 = m 0) (h0' : l' 0 = m' 0) (h1 : m 1 = r 1)
    (h1' : m' 1 = r' 1) (t : ℝ) : HasDerivAt (glue3 l m r) (glue3 l' m' r' t) t := by
  have hin : ∀ t, HasDerivAt (glue 1 m r) (glue 1 m' r' t) t :=
    hasDerivAt_glue hm hr h1 h1'
  have := hasDerivAt_glue (a := 0) hl hin
    (by rw [glue_of_le zero_le_one, h0])
    (by rw [glue_of_le zero_le_one, h0']) t
  exact this

/-- If $|l| \le B$ on $(-\infty, 0]$, $|m| \le B$ on $[0, 1]$ and $|r| \le B$ on $[1, \infty)$, then
the three-piece function is bounded by $B$ in absolute value. -/
theorem abs_glue3_le {B : ℝ} (hl : ∀ t ≤ 0, |l t| ≤ B) (hm : ∀ t ∈ Set.Icc (0 : ℝ) 1, |m t| ≤ B)
    (hr : ∀ t, 1 ≤ t → |r t| ≤ B) (t : ℝ) : |glue3 l m r t| ≤ B := by
  rcases le_or_gt t 0 with h | h
  · rw [glue3_of_nonpos h]; exact hl t h
  rw [glue3, glue_of_lt h]
  rcases le_or_gt t 1 with h' | h'
  · rw [glue_of_le h']; exact hm t ⟨h.le, h'⟩
  · rw [glue_of_lt h']; exact hr t h'.le

/-- If $l$, $m$ and $r$ are continuous, $l(0) = m(0)$ and $m(1) = r(1)$, the three-piece function is
continuous. -/
theorem continuous_glue3 {l m r : ℝ → ℝ} (hl : Continuous l) (hm : Continuous m)
    (hr : Continuous r) (h0 : l 0 = m 0) (h1 : m 1 = r 1) : Continuous (glue3 l m r) :=
  continuous_glue hl (continuous_glue hm hr h1)
    (by rw [glue_of_le zero_le_one, h0])

end Glue3

/-! ### Piecewise Hermite interpolation -/

/-- The derivative of order $j$ of $t \mapsto T(t - x_0)$, for the Taylor polynomial $T$ of degree
$p$ of a jet $a$, is $\sum_{i=j}^p a_i (t - x_0)^{i-j}/(i - j)!$. -/
theorem iteratedDeriv_jetTaylorPoly_sub (p : ℕ) (a : ℕ → ℝ) (x₀ : ℝ) (j : ℕ) (t : ℝ) :
    iteratedDeriv j (fun t => (jetTaylorPoly p a).eval (t - x₀)) t =
      ∑ i ∈ Finset.Icc j p, a i * (t - x₀) ^ (i - j) / (i - j).factorial := by
  simp only [iteratedDeriv_eval_sub, eval_iterate_derivative_jetTaylorPoly]

/-- For $j \le p$, the derivative of order $j$ of $t \mapsto T(t - x_0)$ at $x_0$ is $a_j$, where
$T$ is the Taylor polynomial of degree $p$ of the jet $a$. -/
theorem iteratedDeriv_jetTaylorPoly_sub_self {p : ℕ} (a : ℕ → ℝ) (x₀ : ℝ) {j : ℕ}
    (hj : j ≤ p) :
    iteratedDeriv j (fun t => (jetTaylorPoly p a).eval (t - x₀)) x₀ = a j := by
  rw [iteratedDeriv_jetTaylorPoly_sub, sub_self, sum_Icc_zero_pow a hj]

/-- The derivative of order $p$ of $t \mapsto T(t - x_0)$ is the constant $a_p$, where $T$ is the
Taylor polynomial of degree $p$ of the jet $a$. -/
theorem iteratedDeriv_jetTaylorPoly_sub_top (p : ℕ) (a : ℕ → ℝ) (x₀ t : ℝ) :
    iteratedDeriv p (fun t => (jetTaylorPoly p a).eval (t - x₀)) t = a p := by
  rw [iteratedDeriv_jetTaylorPoly_sub, Finset.Icc_self, Finset.sum_singleton]
  simp

/-- If $x_k < x_{k+1}$ for all $k < K$, then $x_i \le x_j$ for $i \le j \le K$. -/
private theorem le_of_lt_succ_of_le {K : ℕ} {x : ℕ → ℝ} (hx : ∀ k < K, x k < x (k + 1))
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ K) : x i ≤ x j :=
  (strictMonoOn_Iic_of_lt_succ (ψ := x) fun m hm => by simpa using hx m hm).monotoneOn
    (Set.mem_Iic.2 (hij.trans hj)) (Set.mem_Iic.2 hj) hij

/-- **Gluing the interior pieces.** Let $x_0 < x_1 < \dots < x_K$ and let $s_k = x_{k+1} - x_k$. For
$k < K$ let $\pi_k$ be a polynomial with $\pi_k^{(j)}(0) = F_{k,j}$ and
$\pi_k^{(j)}(s_k) = F_{k+1,j}$ for $j \le p$, whose derivative of order $p$ is $L$-Lipschitz on
$[0, s_k]$ and whose derivatives of order at most $p$ are bounded by $B$ on $[0, s_k]$. Let also
$|F_{0,j}| \le B$ for $j \le p$. Then for every $K' \le K$ there is a $C^p$ function
$M : \mathbb{R} \to \mathbb{R}$ with $M^{(j)}(x_k) = F_{k,j}$ for $k \le K'$ and $j \le p$,
whose derivative of order $p$ is $L$-Lipschitz on $[x_0, x_{K'}]$, and whose derivatives of
order at most $p$ are bounded by $B$ on $[x_0, x_{K'}]$. -/
theorem exists_glued_pieces {p : ℕ} {L B : ℝ} {K : ℕ} {x : ℕ → ℝ} {F : ℕ → ℕ → ℝ}
    (π : ℕ → ℝ[X]) (hx : ∀ k < K, x k < x (k + 1))
    (h0 : ∀ k < K, ∀ j ≤ p, (derivative^[j] (π k)).eval 0 = F k j)
    (h1 : ∀ k < K, ∀ j ≤ p, (derivative^[j] (π k)).eval (x (k + 1) - x k) = F (k + 1) j)
    (hL : ∀ k < K, ∀ τ₁ ∈ Set.Icc 0 (x (k + 1) - x k), ∀ τ₂ ∈ Set.Icc 0 (x (k + 1) - x k),
      |(derivative^[p] (π k)).eval τ₁ - (derivative^[p] (π k)).eval τ₂| ≤ L * |τ₁ - τ₂|)
    (hB : ∀ k < K, ∀ j ≤ p, ∀ τ ∈ Set.Icc 0 (x (k + 1) - x k),
      |(derivative^[j] (π k)).eval τ| ≤ B)
    (hB0 : ∀ j ≤ p, |F 0 j| ≤ B) :
    ∀ K' ≤ K, ∃ M : ℝ → ℝ, ContDiff ℝ p M ∧
      (∀ k ≤ K', ∀ j ≤ p, iteratedDeriv j M (x k) = F k j) ∧
      (∀ t₁ ∈ Set.Icc (x 0) (x K'), ∀ t₂ ∈ Set.Icc (x 0) (x K'),
        |iteratedDeriv p M t₁ - iteratedDeriv p M t₂| ≤ L * |t₁ - t₂|) ∧
      ∀ j ≤ p, ∀ t ∈ Set.Icc (x 0) (x K'), |iteratedDeriv j M t| ≤ B := by
  intro K' hK'
  induction K' with
  | zero =>
    refine ⟨fun t => (jetTaylorPoly p (F 0)).eval (t - x 0), contDiff_eval_sub _ _,
      fun k hk j hj => ?_, fun t₁ h₁ t₂ h₂ => ?_, fun j hj t ht => ?_⟩
    · obtain rfl : k = 0 := by omega
      exact iteratedDeriv_jetTaylorPoly_sub_self _ _ hj
    · obtain rfl : t₁ = x 0 := le_antisymm h₁.2 h₁.1
      obtain rfl : t₂ = x 0 := le_antisymm h₂.2 h₂.1
      simp
    · obtain rfl : t = x 0 := le_antisymm ht.2 ht.1
      rw [iteratedDeriv_jetTaylorPoly_sub_self _ _ hj]
      exact hB0 j hj
  | succ K' ih =>
    obtain ⟨M, hM, hMj, hML, hMB⟩ := ih (by omega)
    have hK : K' < K := by omega
    set P : ℝ → ℝ := fun t => (π K').eval (t - x K')
    have hPj : ∀ j, iteratedDeriv j P = fun t => (derivative^[j] (π K')).eval (t - x K') :=
      fun j => iteratedDeriv_eval_sub _ _ j
    have hjet : ∀ j ≤ p, iteratedDeriv j M (x K') = iteratedDeriv j P (x K') := fun j hj => by
      simp only [hMj K' le_rfl j hj, hPj, sub_self, h0 K' hK j hj]
    obtain ⟨hG, hGj⟩ := contDiff_glue hM (contDiff_eval_sub _ _) hjet
    have hx0 : x 0 ≤ x K' := le_of_lt_succ_of_le hx (Nat.zero_le _) (by omega)
    have hxK := hx K' hK
    refine ⟨glue (x K') M P, hG, fun k hk j hj => ?_, fun t₁ h₁ t₂ h₂ => ?_,
      fun j hj t ht => ?_⟩
    · rw [hGj j hj]
      rcases Nat.lt_or_ge k (K' + 1) with hk' | hk'
      · rw [glue_of_le (le_of_lt_succ_of_le hx (by omega) (by omega))]
        exact hMj k (by omega) j hj
      · obtain rfl : k = K' + 1 := by omega
        rw [glue_of_lt hxK, hPj]
        exact h1 K' hK j hj
    · rw [hGj p le_rfl]
      refine abs_glue_sub_le Set.ordConnected_Icc (fun y hy z hz hya hza => ?_)
        (fun y hy z hz hya hza => ?_) (hjet p le_rfl) h₁ h₂
      · exact hML y ⟨hy.1, hya⟩ z ⟨hz.1, hza⟩
      · rw [hPj]
        have := hL K' hK (y - x K') ⟨sub_nonneg.2 hya, by linarith [hy.2]⟩ (z - x K')
          ⟨sub_nonneg.2 hza, by linarith [hz.2]⟩
        rwa [sub_sub_sub_cancel_right] at this
    · rw [hGj j hj]
      by_cases htK : t ≤ x K'
      · rw [glue_of_le htK]
        exact hMB j hj t ⟨ht.1, htK⟩
      · rw [not_le] at htK
        rw [glue_of_lt htK, hPj]
        exact hB K' hK j hj _ ⟨by linarith, by linarith [ht.2]⟩

/-- **Piecewise Hermite interpolation with a Lipschitz derivative.** For every $p \in \mathbb{N}$
and $\kappa \ge 0$ there is $L \ge 0$ with the following property. Let
$x_0 < x_1 < \dots < x_K$, let $s_k = x_{k+1} - x_k$, and let $F_{k,j}$ ($k \le K$, $j \le p$)
be jets with the consistency condition (A.32) $$\Big| F_{k+1,j} - \sum_{i=j}^p \frac{F_{k,i}\,
s_k^{i-j}}{(i - j)!} \Big| \le \kappa\, s_k^{p-j+1}, \qquad k < K, \ j \le p.$$ Then there is a
function $g : \mathbb{R} \to \mathbb{R}$ of class $C^p$ with $$g^{(j)}(x_k) = F_{k,j} \quad (k
\le K, \ j \le p), \qquad |g^{(p)}(t_1) - g^{(p)}(t_2)| \le L |t_1 - t_2| \quad (t_1, t_2 \in
\mathbb{R}).$$ This is Theorem A.9.2 of [cartis2022evaluation].

The constant $L$ depends only on $p$ and $\kappa$: it is chosen before $K$, the nodes and the
jets. -/
theorem exists_contDiff_interpolating_jets (p : ℕ) {κ : ℝ} (hκ : 0 ≤ κ) : ∃ L : ℝ, 0 ≤ L ∧
    ∀ (K : ℕ) (x : ℕ → ℝ) (F : ℕ → ℕ → ℝ), (∀ k < K, x k < x (k + 1)) →
      (∀ k < K, ∀ j ≤ p, |F (k + 1) j - ∑ i ∈ Finset.Icc j p,
        F k i * (x (k + 1) - x k) ^ (i - j) / (i - j).factorial| ≤
          κ * (x (k + 1) - x k) ^ (p - j + 1)) →
      ∃ g : ℝ → ℝ, ContDiff ℝ p g ∧
        (∀ t₁ t₂, |iteratedDeriv p g t₁ - iteratedDeriv p g t₂| ≤ L * |t₁ - t₂|) ∧
        ∀ k ≤ K, ∀ j ≤ p, iteratedDeriv j g (x k) = F k j := by
  obtain ⟨C, hC, htwo⟩ := exists_twoPoint_interpolant p
  have hL0 : 0 ≤ C * κ := mul_nonneg hC hκ
  refine ⟨C * κ, hL0, fun K x F hx hF => ?_⟩
  -- the bound of the pieces' derivatives (finitely many pieces)
  set bnd : ℕ → ℕ → ℝ := fun k j => ∑ i ∈ Finset.Icc j p,
    |F k i| * (x (k + 1) - x k) ^ (i - j) / (i - j).factorial +
      C * κ * (x (k + 1) - x k) ^ (p + 1 - j)
  set B : ℝ := ∑ k ∈ Finset.range K, ∑ j ∈ Finset.range (p + 1), |bnd k j| +
    ∑ j ∈ Finset.range (p + 1), |F 0 j|
  have hbndB : ∀ k < K, ∀ j ≤ p, bnd k j ≤ B := fun k hk j hj => by
    refine (le_abs_self _).trans (le_add_of_le_of_nonneg ?_
      (Finset.sum_nonneg fun _ _ => abs_nonneg _))
    refine le_trans ?_ (Finset.single_le_sum (f := fun k => ∑ j ∈ Finset.range (p + 1), |bnd k j|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_range.2 hk))
    exact Finset.single_le_sum (f := fun j => |bnd k j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 (by omega))
  have hB0 : ∀ j ≤ p, |F 0 j| ≤ B := fun j hj => by
    refine le_add_of_nonneg_of_le (Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => abs_nonneg _) ?_
    exact Finset.single_le_sum (f := fun j => |F 0 j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 (by omega))
  -- the pieces
  have hpiece : ∀ k, ∃ π : ℝ[X], k < K →
      (∀ j ≤ p, (derivative^[j] π).eval 0 = F k j) ∧
      (∀ j ≤ p, (derivative^[j] π).eval (x (k + 1) - x k) = F (k + 1) j) ∧
      (∀ j ≤ p + 1, ∀ τ ∈ Set.Icc 0 (x (k + 1) - x k), |(derivative^[j] π).eval τ| ≤
        bnd k j) ∧
      ∀ τ₁ ∈ Set.Icc 0 (x (k + 1) - x k), ∀ τ₂ ∈ Set.Icc 0 (x (k + 1) - x k),
        |(derivative^[p] π).eval τ₁ - (derivative^[p] π).eval τ₂| ≤ C * κ * |τ₁ - τ₂| := by
    intro k
    by_cases hk : k < K
    · obtain ⟨π, -, h0, h1, hb, hl⟩ :=
        htwo (x (k + 1) - x k) κ (F k) (F (k + 1)) (sub_pos.2 (hx k hk)) (hF k hk)
      exact ⟨π, fun _ => ⟨h0, h1, hb, hl⟩⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose π hπ using hpiece
  obtain ⟨M, hM, hMj, hML, -⟩ := exists_glued_pieces π hx (fun k hk => (hπ k hk).1)
    (fun k hk => (hπ k hk).2.1) (fun k hk => (hπ k hk).2.2.2)
    (fun k hk j hj τ hτ => ((hπ k hk).2.2.1 j (by omega) τ hτ).trans (hbndB k hk j hj)) hB0
    K le_rfl
  -- the two Taylor tails
  set T0 : ℝ → ℝ := fun t => (jetTaylorPoly p (F 0)).eval (t - x 0) with hT0
  set TK : ℝ → ℝ := fun t => (jetTaylorPoly p (F K)).eval (t - x K) with hTK
  have hT0c : ContDiff ℝ p T0 := contDiff_eval_sub _ _
  have hTKc : ContDiff ℝ p TK := contDiff_eval_sub _ _
  have hT0j : ∀ j ≤ p, iteratedDeriv j T0 (x 0) = F 0 j := fun j hj =>
    iteratedDeriv_jetTaylorPoly_sub_self _ _ hj
  have hTKj : ∀ j ≤ p, iteratedDeriv j TK (x K) = F K j := fun j hj =>
    iteratedDeriv_jetTaylorPoly_sub_self _ _ hj
  have hT0p : ∀ t, iteratedDeriv p T0 t = F 0 p := fun t =>
    iteratedDeriv_jetTaylorPoly_sub_top _ _ _ _
  have hTKp : ∀ t, iteratedDeriv p TK t = F K p := fun t =>
    iteratedDeriv_jetTaylorPoly_sub_top _ _ _ _
  clear_value T0 TK
  have hx0K : x 0 ≤ x K := le_of_lt_succ_of_le hx (Nat.zero_le K) le_rfl
  obtain ⟨hG, hGj⟩ := contDiff_glue hM hTKc fun j hj => by rw [hMj K le_rfl j hj, hTKj j hj]
  have hG0 : ∀ j ≤ p, iteratedDeriv j T0 (x 0) = iteratedDeriv j (glue (x K) M TK) (x 0) :=
    fun j hj => by rw [hGj j hj, glue_of_le hx0K, hMj 0 (Nat.zero_le K) j hj, hT0j j hj]
  obtain ⟨hg, hgj⟩ := contDiff_glue hT0c hG hG0
  refine ⟨glue (x 0) T0 (glue (x K) M TK), hg, fun t₁ t₂ => ?_, fun k hk j hj => ?_⟩
  · rw [hgj p le_rfl]
    refine abs_glue_sub_le Set.ordConnected_univ (fun y _ z _ _ _ => ?_)
      (fun y _ z _ hy hz => ?_) (hG0 p le_rfl) (Set.mem_univ t₁) (Set.mem_univ t₂)
    · rw [hT0p, hT0p, sub_self, abs_zero]
      positivity
    · rw [hGj p le_rfl]
      refine abs_glue_sub_le (Set.ordConnected_Ici (a := x 0))
        (fun y hy z hz hyK hzK => hML y ⟨hy, hyK⟩ z ⟨hz, hzK⟩) (fun y _ z _ _ _ => ?_)
        (by rw [hMj K le_rfl p le_rfl, hTKj p le_rfl]) hy hz
      rw [hTKp, hTKp, sub_self, abs_zero]
      positivity
  · rw [hgj j hj]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [glue_of_le le_rfl, hT0j j hj]
    · have h01 : x 0 < x 1 := hx 0 (by omega)
      have h1k : x 1 ≤ x k := le_of_lt_succ_of_le hx hk0 hk
      rw [glue_of_lt (h01.trans_le h1k), hGj j hj,
        glue_of_le (le_of_lt_succ_of_le hx hk le_rfl)]
      exact hMj k hk j hj

/-- Let $|a_i| \le \kappa$ for $i \le p$, and let $0 \le s \le m$ with $m \ge 1$. Then $\sum_{i=j}^p
|a_i|\, s^{i-j}/(i - j)! \le (p + 1)\kappa\, m^p$.
-/
theorem sum_Icc_abs_mul_pow_le {p j : ℕ} {a : ℕ → ℝ} {κ s m : ℝ} (ha : ∀ i ≤ p, |a i| ≤ κ)
    (hs : 0 ≤ s) (hsm : s ≤ m) (hm : 1 ≤ m) :
    ∑ i ∈ Finset.Icc j p, |a i| * s ^ (i - j) / (i - j).factorial ≤ (p + 1) * κ * m ^ p := by
  have hκ : 0 ≤ κ := (abs_nonneg _).trans (ha 0 (Nat.zero_le p))
  calc ∑ i ∈ Finset.Icc j p, |a i| * s ^ (i - j) / (i - j).factorial
      ≤ ∑ _i ∈ Finset.Icc j p, κ * m ^ p := Finset.sum_le_sum fun i hi => by
        have hip := (Finset.mem_Icc.1 hi).2
        have h1 : s ^ (i - j) ≤ m ^ p :=
          (pow_le_pow_left₀ hs hsm _).trans (pow_le_pow_right₀ hm (by omega))
        have hf : (1 : ℝ) ≤ (i - j).factorial := by exact_mod_cast Nat.factorial_pos _
        calc |a i| * s ^ (i - j) / (i - j).factorial ≤ |a i| * s ^ (i - j) :=
              div_le_self (by positivity) hf
          _ ≤ κ * m ^ p := mul_le_mul (ha i hip) h1 (by positivity) hκ
    _ = (Finset.Icc j p).card * (κ * m ^ p) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (p + 1) * (κ * m ^ p) := by
        gcongr
        rw [Nat.card_Icc]
        exact_mod_cast Nat.sub_le _ _
    _ = (p + 1) * κ * m ^ p := by ring

/-- **Theorem A.9.2, bounded version, with all jets bounded.** For every $p \in \mathbb{N}$ and
$\kappa \ge 0$ there are $L, B \ge 0$ with the following property. Let $x_0 < x_1 < \dots < x_K$
with $s_k = x_{k+1} - x_k \le \kappa$ for $k < K$, and let $F_{k,j}$ be jets with
$|F_{k,j}| \le \kappa$ for $k \le K$ and $j \le p$ and with the consistency condition (A.32) of
`Hermite.exists_contDiff_interpolating_jets`. Then there is a function
$g : \mathbb{R} \to \mathbb{R}$ of class $C^p$ such that:

* $g^{(j)}(x_k) = F_{k,j}$ for $k \le K$ and $j \le p$;
* $g^{(p)}$ is $L$-Lipschitz on $\mathbb{R}$;
* $|g^{(j)}(t)| \le B$ for all $t \in \mathbb{R}$ and $j \le p$;
* $g(t) = F_{0,0}$ for $t \le x_0 - 1$, and $g(t) = F_{K,0}$ for $t \ge x_K + 1$.

In particular $g$ is bounded below, and its derivatives of orders $1, \dots, p$ are Lipschitz.
The constants $L$ and $B$ depend only on $p$ and $\kappa$. This version allows $K = 0$. -/
theorem exists_contDiff_interpolating_jets_bounded_of_forall_le (p : ℕ) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ L B : ℝ, 0 ≤ L ∧ 0 ≤ B ∧
      ∀ (K : ℕ) (x : ℕ → ℝ) (F : ℕ → ℕ → ℝ), (∀ k < K, x k < x (k + 1)) →
        (∀ k < K, x (k + 1) - x k ≤ κ) → (∀ k ≤ K, ∀ j ≤ p, |F k j| ≤ κ) →
        (∀ k < K, ∀ j ≤ p, |F (k + 1) j - ∑ i ∈ Finset.Icc j p,
          F k i * (x (k + 1) - x k) ^ (i - j) / (i - j).factorial| ≤
            κ * (x (k + 1) - x k) ^ (p - j + 1)) →
        ∃ g : ℝ → ℝ, ContDiff ℝ p g ∧
          (∀ t₁ t₂, |iteratedDeriv p g t₁ - iteratedDeriv p g t₂| ≤ L * |t₁ - t₂|) ∧
          (∀ j ≤ p, ∀ t, |iteratedDeriv j g t| ≤ B) ∧
          (∀ k ≤ K, ∀ j ≤ p, iteratedDeriv j g (x k) = F k j) ∧
          (∀ t ≤ x 0 - 1, g t = F 0 0) ∧ ∀ t, x K + 1 ≤ t → g t = F K 0 := by
  obtain ⟨C, hC, htwo⟩ := exists_twoPoint_interpolant p
  set κ₁ : ℝ := (p + 2) * κ with hκ₁
  set m : ℝ := max 1 κ with hm
  have hm1 : 1 ≤ m := le_max_left _ _
  have hκm : κ ≤ m := le_max_right _ _
  have hκκ₁ : κ ≤ κ₁ := by
    rw [hκ₁]
    nlinarith
  have hκ₁0 : 0 ≤ κ₁ := hκ.trans hκκ₁
  set L : ℝ := C * κ₁
  set B : ℝ := (p + 1) * κ * m ^ p + C * κ₁ * m ^ (p + 1)
  have hL0 : 0 ≤ L := mul_nonneg hC hκ₁0
  have hκB : κ ≤ B := by
    have h1 : κ ≤ (p + 1) * κ * m ^ p := by
      have : (1 : ℝ) ≤ (p + 1) * m ^ p := by
        have := one_le_pow₀ (n := p) hm1
        nlinarith
      nlinarith
    have h2 : 0 ≤ C * κ₁ * m ^ (p + 1) := by positivity
    linarith
  have hB0 : 0 ≤ B := hκ.trans hκB
  -- the bound of a piece with bounded left jet and length at most `m`
  have hpb : ∀ (a : ℕ → ℝ) (s : ℝ), 0 ≤ s → s ≤ m → (∀ i ≤ p, |a i| ≤ κ) → ∀ j,
      ∑ i ∈ Finset.Icc j p, |a i| * s ^ (i - j) / (i - j).factorial +
        C * κ₁ * s ^ (p + 1 - j) ≤ B := fun a s hs hsm ha j => by
    refine add_le_add (sum_Icc_abs_mul_pow_le ha hs hsm hm1) ?_
    have : s ^ (p + 1 - j) ≤ m ^ (p + 1) :=
      (pow_le_pow_left₀ hs hsm _).trans (pow_le_pow_right₀ hm1 (by omega))
    exact mul_le_mul_of_nonneg_left this (by positivity)
  refine ⟨L, B, hL0, hB0, fun K x F hx hgap hFb hF => ?_⟩
  -- interior pieces
  have hpiece : ∀ k, ∃ π : ℝ[X], k < K →
      (∀ j ≤ p, (derivative^[j] π).eval 0 = F k j) ∧
      (∀ j ≤ p, (derivative^[j] π).eval (x (k + 1) - x k) = F (k + 1) j) ∧
      (∀ j ≤ p + 1, ∀ τ ∈ Set.Icc 0 (x (k + 1) - x k), |(derivative^[j] π).eval τ| ≤ B) ∧
      ∀ τ₁ ∈ Set.Icc 0 (x (k + 1) - x k), ∀ τ₂ ∈ Set.Icc 0 (x (k + 1) - x k),
        |(derivative^[p] π).eval τ₁ - (derivative^[p] π).eval τ₂| ≤ L * |τ₁ - τ₂| := by
    intro k
    by_cases hk : k < K
    · have hs := sub_pos.2 (hx k hk)
      obtain ⟨π, -, h0, h1, hb, hl⟩ :=
        htwo (x (k + 1) - x k) κ₁ (F k) (F (k + 1)) hs fun j hj =>
          (hF k hk j hj).trans (mul_le_mul_of_nonneg_right hκκ₁ (by positivity))
      exact ⟨π, fun _ => ⟨h0, h1, fun j hj τ hτ => (hb j hj τ hτ).trans
        (hpb _ _ hs.le ((hgap k hk).trans hκm) (fun i hi => hFb k hk.le i hi) j), hl⟩⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose π hπ using hpiece
  obtain ⟨M, hM, hMj, hML, hMB⟩ := exists_glued_pieces π hx (fun k hk => (hπ k hk).1)
    (fun k hk => (hπ k hk).2.1) (fun k hk => (hπ k hk).2.2.2)
    (fun k hk j hj τ hτ => (hπ k hk).2.2.1 j (by omega) τ hτ)
    (fun j hj => (hFb 0 (Nat.zero_le K) j hj).trans hκB) K le_rfl
  -- the outer pieces, of length `1`, towards constant jets
  obtain ⟨πL, -, hL0j, hL1j, hLb, hLl⟩ := htwo 1 κ₁ (constJet (F 0 0)) (F 0) one_pos
    fun j hj => by
      rw [show (∑ i ∈ Finset.Icc j p, constJet (F 0 0) i * (1 : ℝ) ^ (i - j) /
        (i - j).factorial) = constJet (F 0 0) j from sum_Icc_constJet _ _ _ _, one_pow, mul_one]
      unfold constJet
      split_ifs with h
      · subst h
        simpa using hκ₁0
      · simpa using (hFb 0 (Nat.zero_le K) j hj).trans hκκ₁
  obtain ⟨πR, -, hR0j, hR1j, hRb, hRl⟩ := htwo 1 κ₁ (F K) (constJet (F K 0)) one_pos
    fun j _ => by
      rw [one_pow, mul_one]
      refine (abs_sub _ _).trans ?_
      have h1 := abs_constJet_le (hFb K le_rfl 0 (Nat.zero_le p)) j
      have h2 : |∑ i ∈ Finset.Icc j p, F K i * (1 : ℝ) ^ (i - j) / (i - j).factorial| ≤
          (p + 1) * κ * 1 ^ p := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq_of_le ?_
          (sum_Icc_abs_mul_pow_le (j := j) (fun i hi => hFb K le_rfl i hi) zero_le_one le_rfl
            le_rfl))
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [abs_div, abs_mul, Nat.abs_cast, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 ^ (i - j))]
      rw [one_pow, mul_one] at h2
      rw [hκ₁]
      linarith
  -- names for the five pieces and their properties
  set cL : ℝ → ℝ := fun t => (jetTaylorPoly p (constJet (F 0 0))).eval (t - (x 0 - 1)) with hcL
  set cR : ℝ → ℝ := fun t => (jetTaylorPoly p (constJet (F K 0))).eval (t - (x K + 1)) with hcR
  set PL : ℝ → ℝ := fun t => πL.eval (t - (x 0 - 1)) with hPL
  set PR : ℝ → ℝ := fun t => πR.eval (t - x K) with hPR
  have hcLc : ContDiff ℝ p cL := contDiff_eval_sub _ _
  have hcRc : ContDiff ℝ p cR := contDiff_eval_sub _ _
  have hPLc : ContDiff ℝ p PL := contDiff_eval_sub _ _
  have hPRc : ContDiff ℝ p PR := contDiff_eval_sub _ _
  have hcLj : ∀ j t, iteratedDeriv j cL t = constJet (F 0 0) j := fun j t => by
    rw [hcL, iteratedDeriv_jetTaylorPoly_sub, sum_Icc_constJet]
  have hcRj : ∀ j t, iteratedDeriv j cR t = constJet (F K 0) j := fun j t => by
    rw [hcR, iteratedDeriv_jetTaylorPoly_sub, sum_Icc_constJet]
  have hPLj : ∀ j t, iteratedDeriv j PL t = (derivative^[j] πL).eval (t - (x 0 - 1)) :=
    fun j t => by rw [hPL, iteratedDeriv_eval_sub]
  have hPRj : ∀ j t, iteratedDeriv j PR t = (derivative^[j] πR).eval (t - x K) :=
    fun j t => by rw [hPR, iteratedDeriv_eval_sub]
  clear_value cL cR PL PR
  have hx0K : x 0 ≤ x K := le_of_lt_succ_of_le hx (Nat.zero_le K) le_rfl
  -- gluing, from the right
  obtain ⟨hG3, hG3j⟩ := contDiff_glue (a := x K + 1) hPRc hcRc fun j hj => by
    rw [hPRj, hcRj, add_sub_cancel_left, hR1j j hj]
  have hJ2 : ∀ j ≤ p, iteratedDeriv j M (x K) = iteratedDeriv j (glue (x K + 1) PR cR) (x K) :=
    fun j hj => by
      rw [hG3j j hj, glue_of_le (by linarith), hPRj, sub_self, hR0j j hj, hMj K le_rfl j hj]
  obtain ⟨hG2, hG2j⟩ := contDiff_glue hM hG3 hJ2
  have hJ1 : ∀ j ≤ p, iteratedDeriv j PL (x 0) =
      iteratedDeriv j (glue (x K) M (glue (x K + 1) PR cR)) (x 0) := fun j hj => by
    rw [hG2j j hj, glue_of_le hx0K, hPLj, sub_sub_cancel, hL1j j hj, hMj 0 (Nat.zero_le K) j hj]
  obtain ⟨hG1, hG1j⟩ := contDiff_glue hPLc hG2 hJ1
  have hJ0 : ∀ j ≤ p, iteratedDeriv j cL (x 0 - 1) =
      iteratedDeriv j (glue (x 0) PL (glue (x K) M (glue (x K + 1) PR cR))) (x 0 - 1) :=
    fun j hj => by
      rw [hG1j j hj, glue_of_le (by linarith), hPLj, sub_self, hL0j j hj, hcLj]
  obtain ⟨hg, hgj⟩ := contDiff_glue hcLc hG1 hJ0
  refine ⟨glue (x 0 - 1) cL (glue (x 0) PL (glue (x K) M (glue (x K + 1) PR cR))), hg,
    fun t₁ t₂ => ?_, fun j hj t => ?_, fun k hk j hj => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · -- Lipschitz `p`-th derivative, from the right
    have hl3 : ∀ y ∈ Set.Ici (x K), ∀ z ∈ Set.Ici (x K),
        |iteratedDeriv p (glue (x K + 1) PR cR) y - iteratedDeriv p (glue (x K + 1) PR cR) z| ≤
          L * |y - z| := fun y hy z hz => by
      rw [hG3j p le_rfl]
      refine abs_glue_sub_le Set.ordConnected_Ici (fun y hy z hz hya hza => ?_)
        (fun y _ z _ _ _ => ?_) (by rw [hPRj, hcRj, add_sub_cancel_left, hR1j p le_rfl]) hy hz
      · rw [hPRj, hPRj]
        have := hRl (y - x K) ⟨sub_nonneg.2 hy, by linarith⟩ (z - x K)
          ⟨sub_nonneg.2 hz, by linarith⟩
        rwa [sub_sub_sub_cancel_right] at this
      · rw [hcRj, hcRj, sub_self, abs_zero]
        positivity
    have hl2 : ∀ y ∈ Set.Ici (x 0), ∀ z ∈ Set.Ici (x 0),
        |iteratedDeriv p (glue (x K) M (glue (x K + 1) PR cR)) y -
          iteratedDeriv p (glue (x K) M (glue (x K + 1) PR cR)) z| ≤ L * |y - z| :=
      fun y hy z hz => by
        rw [hG2j p le_rfl]
        exact abs_glue_sub_le Set.ordConnected_Ici
          (fun y hy z hz hya hza => hML y ⟨hy, hya⟩ z ⟨hz, hza⟩)
          (fun y _ z _ hya hza => hl3 y hya z hza) (hJ2 p le_rfl) hy hz
    have hl1 : ∀ y ∈ Set.Ici (x 0 - 1), ∀ z ∈ Set.Ici (x 0 - 1),
        |iteratedDeriv p (glue (x 0) PL (glue (x K) M (glue (x K + 1) PR cR))) y -
          iteratedDeriv p (glue (x 0) PL (glue (x K) M (glue (x K + 1) PR cR))) z| ≤
            L * |y - z| := fun y hy z hz => by
      rw [hG1j p le_rfl]
      refine abs_glue_sub_le Set.ordConnected_Ici (fun y hy z hz hya hza => ?_)
        (fun y _ z _ hya hza => hl2 y hya z hza) (hJ1 p le_rfl) hy hz
      rw [hPLj, hPLj]
      have := hLl (y - (x 0 - 1)) ⟨sub_nonneg.2 hy, by linarith⟩ (z - (x 0 - 1))
        ⟨sub_nonneg.2 hz, by linarith⟩
      rwa [sub_sub_sub_cancel_right] at this
    rw [hgj p le_rfl]
    refine abs_glue_sub_le Set.ordConnected_univ (fun y _ z _ _ _ => ?_)
      (fun y _ z _ hya hza => hl1 y hya z hza) (hJ0 p le_rfl) (Set.mem_univ t₁)
      (Set.mem_univ t₂)
    rw [hcLj, hcLj, sub_self, abs_zero]
    positivity
  · -- bounds
    rw [hgj j hj]
    by_cases h0 : t ≤ x 0 - 1
    · rw [glue_of_le h0, hcLj]
      exact (abs_constJet_le (hFb 0 (Nat.zero_le K) 0 (Nat.zero_le p)) j).trans hκB
    rw [not_le] at h0
    rw [glue_of_lt h0, hG1j j hj]
    by_cases h1 : t ≤ x 0
    · rw [glue_of_le h1, hPLj]
      exact (hLb j (by omega) _ ⟨by linarith, by linarith⟩).trans
        (hpb _ _ zero_le_one hm1 (fun i _ => abs_constJet_le
          (hFb 0 (Nat.zero_le K) 0 (Nat.zero_le p)) i) j)
    rw [not_le] at h1
    rw [glue_of_lt h1, hG2j j hj]
    by_cases h2 : t ≤ x K
    · rw [glue_of_le h2]
      exact hMB j hj t ⟨h1.le, h2⟩
    rw [not_le] at h2
    rw [glue_of_lt h2, hG3j j hj]
    by_cases h3 : t ≤ x K + 1
    · rw [glue_of_le h3, hPRj]
      exact (hRb j (by omega) _ ⟨by linarith, by linarith⟩).trans
        (hpb _ _ zero_le_one hm1 (fun i hi => hFb K le_rfl i hi) j)
    rw [not_le] at h3
    rw [glue_of_lt h3, hcRj]
    exact (abs_constJet_le (hFb K le_rfl 0 (Nat.zero_le p)) j).trans hκB
  · -- interpolation
    rw [hgj j hj, glue_of_lt (by linarith [le_of_lt_succ_of_le hx (Nat.zero_le k) hk]), hG1j j hj]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [glue_of_le le_rfl, hPLj, sub_sub_cancel, hL1j j hj]
    · have h01 : x 0 < x 1 := hx 0 (by omega)
      have h1k : x 1 ≤ x k := le_of_lt_succ_of_le hx hk0 hk
      rw [glue_of_lt (h01.trans_le h1k), hG2j j hj,
        glue_of_le (le_of_lt_succ_of_le hx hk le_rfl)]
      exact hMj k hk j hj
  · -- constant on the left
    rw [glue_of_le ht, ← iteratedDeriv_zero (f := cL), hcLj]
    simp [constJet]
  · -- constant on the right
    have hv3 : PR (x K + 1) = cR (x K + 1) := by
      have h := hPRj 0 (x K + 1)
      have h' := hcRj 0 (x K + 1)
      rw [iteratedDeriv_zero] at h h'
      rw [h, h', add_sub_cancel_left, Function.iterate_zero_apply,
        ← Function.iterate_zero_apply derivative πR, hR1j 0 (Nat.zero_le p)]
    rw [glue_of_lt (by linarith), glue_of_lt (by linarith), glue_of_lt (by linarith),
      glue_of_ge hv3 ht, ← iteratedDeriv_zero (f := cR), hcRj]
    simp [constJet]

/-- **Theorem A.9.2, bounded version.** For every $p \in \mathbb{N}$ and $\kappa \ge 0$ there are
$L, B \ge 0$ with the following property. Let $K > 0$, let $x_0 < x_1 < \dots < x_K$ with
$s_k = x_{k+1} - x_k \le \kappa$ for $k < K$, and let $F_{k,j}$ be jets with
$|F_{k,j}| \le \kappa$ for $k < K$ and $j \le p$ and with the consistency condition (A.32)
$$\Big| F_{k+1,j} - \sum_{i=j}^p \frac{F_{k,i}\, s_k^{i-j}}{(i - j)!} \Big| \le \kappa\,
s_k^{p-j+1}, \qquad k < K, \ j \le p.$$ Then there is a function $g : \mathbb{R} \to \mathbb{R}$
of class $C^p$ such that:

* $g^{(j)}(x_k) = F_{k,j}$ for $k \le K$ and $j \le p$;
* $g^{(p)}$ is $L$-Lipschitz on $\mathbb{R}$;
* $|g^{(j)}(t)| \le B$ for all $t \in \mathbb{R}$ and $j \le p$;
* $g(t) = F_{0,0}$ for $t \le x_0 - 1$, and $g(t) = F_{K,0}$ for $t \ge x_K + 1$.

In particular $g$ is bounded below, and its derivatives of orders $1, \dots, p$ are Lipschitz.
This is the bounded version of Theorem A.9.2 of [cartis2022evaluation].

The bound on the last jet $F_{K,j}$ is not assumed: it follows from the consistency condition,
with a larger constant. The proof applies
`Hermite.exists_contDiff_interpolating_jets_bounded_of_forall_le`. The constants $L$ and $B$
depend only on $p$ and $\kappa$. -/
theorem exists_contDiff_interpolating_jets_bounded (p : ℕ) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ L B : ℝ, 0 ≤ L ∧ 0 ≤ B ∧
      ∀ (K : ℕ) (x : ℕ → ℝ) (F : ℕ → ℕ → ℝ), 0 < K → (∀ k < K, x k < x (k + 1)) →
        (∀ k < K, x (k + 1) - x k ≤ κ) → (∀ k < K, ∀ j ≤ p, |F k j| ≤ κ) →
        (∀ k < K, ∀ j ≤ p, |F (k + 1) j - ∑ i ∈ Finset.Icc j p,
          F k i * (x (k + 1) - x k) ^ (i - j) / (i - j).factorial| ≤
            κ * (x (k + 1) - x k) ^ (p - j + 1)) →
        ∃ g : ℝ → ℝ, ContDiff ℝ p g ∧
          (∀ t₁ t₂, |iteratedDeriv p g t₁ - iteratedDeriv p g t₂| ≤ L * |t₁ - t₂|) ∧
          (∀ j ≤ p, ∀ t, |iteratedDeriv j g t| ≤ B) ∧
          (∀ k ≤ K, ∀ j ≤ p, iteratedDeriv j g (x k) = F k j) ∧
          (∀ t ≤ x 0 - 1, g t = F 0 0) ∧ ∀ t, x K + 1 ≤ t → g t = F K 0 := by
  set m : ℝ := max 1 κ with hm
  have hm1 : 1 ≤ m := le_max_left _ _
  have hκm : κ ≤ m := le_max_right _ _
  set κ' : ℝ := (p + 1) * κ * m ^ p + κ * m ^ (p + 1) + κ with hκ'
  have hκκ' : κ ≤ κ' := by
    have : 0 ≤ (p + 1) * κ * m ^ p + κ * m ^ (p + 1) := by positivity
    linarith
  obtain ⟨L, B, hL, hB, hH⟩ :=
    exists_contDiff_interpolating_jets_bounded_of_forall_le p (hκ.trans hκκ')
  refine ⟨L, B, hL, hB, fun K x F hK hx hgap hFb hF => hH K x F hx
    (fun k hk => (hgap k hk).trans hκκ') (fun k hk j hj => ?_)
    (fun k hk j hj => (hF k hk j hj).trans
      (mul_le_mul_of_nonneg_right hκκ' (by have := hx k hk; positivity)))⟩
  rcases hk.lt_or_eq with hk | rfl
  · exact (hFb k hk j hj).trans hκκ'
  -- the last jet is controlled by the consistency condition
  obtain ⟨K', rfl⟩ : ∃ K', k = K' + 1 := ⟨k - 1, by omega⟩
  have hK' : K' < K' + 1 := Nat.lt_succ_self K'
  have hs0 : 0 ≤ x (K' + 1) - x K' := (sub_pos.2 (hx K' hK')).le
  have hsm : x (K' + 1) - x K' ≤ m := (hgap K' hK').trans hκm
  have h1 := hF K' hK' j hj
  have h2 : |∑ i ∈ Finset.Icc j p, F K' i * (x (K' + 1) - x K') ^ (i - j) / (i - j).factorial|
      ≤ (p + 1) * κ * m ^ p := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq_of_le ?_
      (sum_Icc_abs_mul_pow_le (j := j) (fun i hi => hFb K' hK' i hi) hs0 hsm hm1))
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [abs_div, abs_mul, abs_pow, abs_of_nonneg hs0, Nat.abs_cast]
  have h3 : κ * (x (K' + 1) - x K') ^ (p - j + 1) ≤ κ * m ^ (p + 1) :=
    mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ hs0 hsm _).trans
      (pow_le_pow_right₀ hm1 (by omega))) hκ
  have h4 := abs_sub_abs_le_abs_sub (F (K' + 1) j)
    (∑ i ∈ Finset.Icc j p, F K' i * (x (K' + 1) - x K') ^ (i - j) / (i - j).factorial)
  rw [hκ']
  linarith

/-- **Theorem A.9.1, second part.** For every $p \in \mathbb{N}$ there is a constant $C \ge 0$ with
the following property. Let $0 < s \le \kappa$, let $a, b$ be jets with $|a_j| \le \kappa$ for
$j \le p$ (A.31) and with the consistency condition (A.30) of
`Hermite.exists_twoPoint_interpolant`. Then there is a polynomial $\pi$ of degree at most
$2p + 1$ with $\pi^{(j)}(0) = a_j$ and $\pi^{(j)}(s) = b_j$ for $j \le p$, with
$$|\pi^{(j)}(\tau)| \le (p + 1)\kappa\, m^p + C\kappa\, m^{p+1}, \qquad \tau \in [0, s], \ j \le
p + 1,$$ where $m = \max\{1, \kappa\}$, and with $|\pi^{(p)}(\tau_1) - \pi^{(p)}(\tau_2)| \le
C\kappa |\tau_1 - \tau_2|$ for $\tau_1, \tau_2 \in [0, s]$. This is the second part of Theorem
A.9.1 of [cartis2022evaluation]; the bound depends only on $p$ and $\kappa$. -/
theorem exists_twoPoint_interpolant_bounded (p : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (s κ : ℝ) (a b : ℕ → ℝ), 0 < s → s ≤ κ → (∀ j ≤ p, |a j| ≤ κ) →
      (∀ j ≤ p, |b j - ∑ i ∈ Finset.Icc j p, a i * s ^ (i - j) / (i - j).factorial| ≤
        κ * s ^ (p - j + 1)) →
      ∃ π : ℝ[X], π.natDegree ≤ 2 * p + 1 ∧
        (∀ j ≤ p, (derivative^[j] π).eval 0 = a j) ∧
        (∀ j ≤ p, (derivative^[j] π).eval s = b j) ∧
        (∀ j ≤ p + 1, ∀ τ ∈ Set.Icc 0 s, |(derivative^[j] π).eval τ| ≤
          (p + 1) * κ * max 1 κ ^ p + C * κ * max 1 κ ^ (p + 1)) ∧
        ∀ τ₁ ∈ Set.Icc 0 s, ∀ τ₂ ∈ Set.Icc 0 s,
          |(derivative^[p] π).eval τ₁ - (derivative^[p] π).eval τ₂| ≤ C * κ * |τ₁ - τ₂| := by
  obtain ⟨C, hC, htwo⟩ := exists_twoPoint_interpolant p
  refine ⟨C, hC, fun s κ a b hs hsκ ha hab => ?_⟩
  obtain ⟨π, hdeg, h0, h1, hb, hl⟩ := htwo s κ a b hs hab
  have hκ : 0 ≤ κ := hs.le.trans hsκ
  have hm1 : (1 : ℝ) ≤ max 1 κ := le_max_left _ _
  have hsm : s ≤ max 1 κ := hsκ.trans (le_max_right _ _)
  refine ⟨π, hdeg, h0, h1, fun j hj τ hτ => (hb j hj τ hτ).trans (add_le_add
    (sum_Icc_abs_mul_pow_le ha hs.le hsm hm1) ?_), hl⟩
  exact mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ hs.le hsm _).trans
    (pow_le_pow_right₀ hm1 (by omega))) (by positivity)

end Hermite

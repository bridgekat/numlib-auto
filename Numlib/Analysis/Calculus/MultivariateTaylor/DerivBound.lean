import Numlib.Analysis.Calculus.LipschitzIteratedFDeriv
import Numlib.Analysis.SpecialFunctions.FactorialSum

/-!
# Norm bounds for the derivatives of a Taylor sum

For arbitrary (not necessarily symmetric) derivative data `D : FormalMultilinearSeries ℝ E F`, the
`ℓ`-th derivative of the Taylor sum `s ↦ D.taylorSum p s = ∑_{i ≤ p} (1/i!) D_i[s]^i` satisfies
`‖∇^ℓ_s T_p(s)‖ ≤ ∑_{i=ℓ}^p ‖D_i‖ ‖s‖^{i-ℓ} / (i-ℓ)!`
(`FormalMultilinearSeries.norm_iteratedFDeriv_taylorSum_le`). For symmetric data this follows from
the exact formula (A.11) of [cartis2022evaluation]; the bound itself needs no symmetry. Since the
derivative is linear in the data (`FormalMultilinearSeries.iteratedFDeriv_taylorSum_sub`), the
bound applies to differences of jets, as in the inexact-model estimates (13.1.48)–(13.1.50) and in
the proof of Lemma 12.2.7 of [cartis2022evaluation].

## Main results

* `ContinuousMultilinearMap.norm_iteratedFDeriv_comp_diagonal_le`: for an `n`-multilinear map `A`,
  `‖∇^ℓ (y ↦ A[y]^n)(s)‖ ≤ n (n-1) ⋯ (n-ℓ+1) ‖A‖ ‖s‖^{n-ℓ}`;
* `FormalMultilinearSeries.iteratedFDeriv_taylorSum_sub`: linearity in the data;
* `FormalMultilinearSeries.norm_iteratedFDeriv_taylorSum_le`: the bound above, and its quadratic
  case on a ball `FormalMultilinearSeries.norm_iteratedFDeriv_taylorSum_two_le`;
* `FormalMultilinearSeries.norm_iteratedFDeriv_taylorSum_le_three_mul`: `‖∇^ℓ T_p(s)‖ ≤ 3 L` on the
  unit ball when `‖D_i‖ ≤ L` for `i ≥ ℓ` (proof of Lemma 12.2.7);
* `FormalMultilinearSeries.taylorSum_add_eq_taylorPolynomial`: a Taylor sum is its own Taylor
  polynomial at every point (no symmetry needed).
-/

open Finset
open scoped Nat

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The diagonal embedding `y ↦ (y, …, y)` has norm at most one. -/
theorem ContinuousLinearMap.norm_pi_id_le_one (n : ℕ) :
    ‖ContinuousLinearMap.pi (fun _ : Fin n => ContinuousLinearMap.id ℝ E)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by
    rw [one_mul]
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg y)).2 fun _ => le_rfl

/-- **Derivatives of a multilinear map on the diagonal.** For `A` an `n`-multilinear map, the
`ℓ`-th derivative of `y ↦ A (y, …, y)` at `s` has norm at most
`n (n-1) ⋯ (n-ℓ+1) ‖A‖ ‖s‖^{n-ℓ}` (and vanishes for `ℓ > n`). No symmetry of `A` is needed. -/
theorem ContinuousMultilinearMap.norm_iteratedFDeriv_comp_diagonal_le {n : ℕ}
    (A : E [×n]→L[ℝ] F) (ℓ : ℕ) (s : E) :
    ‖iteratedFDeriv ℝ ℓ (fun y => A (fun _ => y)) s‖ ≤
      (n.descFactorial ℓ : ℝ) * ‖A‖ * ‖s‖ ^ (n - ℓ) := by
  let g : E →L[ℝ] (Fin n → E) := ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ E
  have hg : ‖g‖ ≤ 1 := ContinuousLinearMap.norm_pi_id_le_one n
  have hgs : ‖g s‖ ≤ ‖s‖ := by simpa using g.le_of_opNorm_le hg s
  change ‖iteratedFDeriv ℝ ℓ (A ∘ g) s‖ ≤ _
  rw [g.iteratedFDeriv_comp_right A.contDiff s (i := ℓ) (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : ∏ _i : Fin ℓ, ‖g‖ ≤ 1 := by
    simpa using pow_le_one₀ (norm_nonneg g) hg
  calc ‖iteratedFDeriv ℝ ℓ A (g s)‖ * ∏ _i : Fin ℓ, ‖g‖
      ≤ ‖iteratedFDeriv ℝ ℓ A (g s)‖ * 1 := by gcongr
    _ ≤ (n.descFactorial ℓ : ℝ) * ‖A‖ * ‖g s‖ ^ (n - ℓ) := by
      simpa using A.norm_iteratedFDeriv_le ℓ (g s)
    _ ≤ (n.descFactorial ℓ : ℝ) * ‖A‖ * ‖s‖ ^ (n - ℓ) := by gcongr

namespace FormalMultilinearSeries

variable (D D' : FormalMultilinearSeries ℝ E F) (p : ℕ)

/-- The derivatives of the Taylor sum are linear in the data:
`∇^ℓ (D - D').taylorSum p = ∇^ℓ D.taylorSum p - ∇^ℓ D'.taylorSum p`. -/
theorem iteratedFDeriv_taylorSum_sub (ℓ : ℕ) (s : E) :
    iteratedFDeriv ℝ ℓ ((D - D').taylorSum p) s =
      iteratedFDeriv ℝ ℓ (D.taylorSum p) s - iteratedFDeriv ℝ ℓ (D'.taylorSum p) s := by
  have h : (D - D').taylorSum p = D.taylorSum p - D'.taylorSum p :=
    funext fun s => taylorSum_sub D D' p s
  rw [h, iteratedFDeriv_sub_apply (D.contDiff_taylorSum p).contDiffAt
    (D'.contDiff_taylorSum p).contDiffAt]

/-- **Derivative bound for Taylor sums** ([cartis2022evaluation], (A.11), proofs of Lemma 12.2.7
and (13.1.48)). For arbitrary data `D`,
`‖∇^ℓ_s T_p(s)‖ ≤ ∑_{i=ℓ}^p ‖D_i‖ ‖s‖^{i-ℓ} / (i-ℓ)!`. -/
theorem norm_iteratedFDeriv_taylorSum_le (ℓ : ℕ) (s : E) :
    ‖iteratedFDeriv ℝ ℓ (D.taylorSum p) s‖ ≤
      ∑ i ∈ Icc ℓ p, ‖D i‖ * ‖s‖ ^ (i - ℓ) / ((i - ℓ)! : ℝ) := by
  have hfun : D.taylorSum p = fun y => ∑ i ∈ range (p + 1), (i ! : ℝ)⁻¹ • D i (fun _ => y) := rfl
  rw [hfun, iteratedFDeriv_fun_sum_apply fun i _ =>
    ((D.contDiff_apply_diagonal i).const_smul _).contDiffAt]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ i ∈ range (p + 1),
      ‖iteratedFDeriv ℝ ℓ (fun y => (i ! : ℝ)⁻¹ • D i (fun _ => y)) s‖ ≤
        if ℓ ≤ i then ‖D i‖ * ‖s‖ ^ (i - ℓ) / ((i - ℓ)! : ℝ) else 0 := by
    intro i _
    rw [iteratedFDeriv_const_smul_apply' (D.contDiff_apply_diagonal i).contDiffAt, norm_smul,
      Real.norm_of_nonneg (by positivity)]
    refine (mul_le_mul_of_nonneg_left ((D i).norm_iteratedFDeriv_comp_diagonal_le ℓ s)
      (by positivity)).trans (le_of_eq ?_)
    split_ifs with h
    · have hf := Nat.factorial_mul_descFactorial h
      have : ((i - ℓ)! : ℝ) ≠ 0 := by positivity
      rw [← hf, Nat.cast_mul]
      have : (i.descFactorial ℓ : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.descFactorial_pos.2 h).ne'
      field_simp
    · simp [Nat.descFactorial_eq_zero_iff_lt.2 (not_le.1 h)]
  refine (sum_le_sum hterm).trans (le_of_eq ?_)
  rw [← sum_filter]
  refine sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [mem_filter, mem_range, mem_Icc]
  omega


/-- **Quadratic Taylor sums on a ball**: if `‖D_i‖ ≤ κ` for `i ≤ 2` and `‖s‖ ≤ ρ`, then
`‖∇^m T_2(s)‖ ≤ 3 κ (1 + ρ)²` for every `m`. -/
theorem norm_iteratedFDeriv_taylorSum_two_le {κ ρ : ℝ} (hκ : 0 ≤ κ) (hρ : 0 ≤ ρ)
    (hD : ∀ i ≤ 2, ‖D i‖ ≤ κ) (m : ℕ) {s : E} (hs : ‖s‖ ≤ ρ) :
    ‖iteratedFDeriv ℝ m (D.taylorSum 2) s‖ ≤ 3 * κ * (1 + ρ) ^ 2 := by
  refine (D.norm_iteratedFDeriv_taylorSum_le 2 m s).trans ?_
  have hterm : ∀ i ∈ Icc m 2, ‖D i‖ * ‖s‖ ^ (i - m) / ((i - m)! : ℝ) ≤ κ * (1 + ρ) ^ 2 := by
    intro i hi
    obtain ⟨hmi, hi2⟩ := mem_Icc.1 hi
    have h1 : ‖s‖ ^ (i - m) ≤ (1 + ρ) ^ 2 :=
      (pow_le_pow_left₀ (norm_nonneg s) (by linarith) _).trans
        (pow_le_pow_right₀ (by linarith) (by omega))
    have h2 : (1 : ℝ) ≤ ((i - m)! : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos _)
    calc ‖D i‖ * ‖s‖ ^ (i - m) / ((i - m)! : ℝ) ≤ ‖D i‖ * ‖s‖ ^ (i - m) :=
          div_le_self (by positivity) h2
      _ ≤ κ * (1 + ρ) ^ 2 := mul_le_mul (hD i hi2) h1 (by positivity) hκ
  refine (sum_le_card_nsmul _ _ _ hterm).trans ?_
  rw [nsmul_eq_mul, Nat.card_Icc]
  have : ((2 + 1 - m : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (by omega : 2 + 1 - m ≤ 3)
  have : 0 ≤ κ * (1 + ρ) ^ 2 := by positivity
  nlinarith

/-- The `p`-th derivative of a Taylor sum of degree `p` is constant, hence `0`-Lipschitz. -/
theorem iteratedFDerivLipschitzOn_taylorSum (p : ℕ) :
    IteratedFDerivLipschitzOn (D.taylorSum p) p 0 Set.univ :=
  iteratedFDerivLipschitzOn_of_norm_le convex_univ
    (fun _ _ => (D.contDiff_taylorSum p).contDiffAt) fun x _ => by
      refine (D.norm_iteratedFDeriv_taylorSum_le p (p + 1) x).trans_eq ?_
      rw [Icc_eq_empty (by omega), sum_empty]

/-- **A Taylor sum is its own Taylor polynomial**: `T_p(s + d) = T_{T_p,p}(s, d)` for all `s, d`
(the expansion of a polynomial of degree `p` at any point is exact). No symmetry of `D` is
needed. -/
theorem taylorSum_add_eq_taylorPolynomial (p : ℕ) (s d : E) :
    D.taylorSum p (s + d) = taylorPolynomial (D.taylorSum p) p s d := by
  have h := norm_sub_taylorPolynomial_le_of_lipschitz convex_univ
    (fun y _ => (D.contDiff_taylorSum p).contDiffAt) (D.iteratedFDerivLipschitzOn_taylorSum p)
    (Set.mem_univ s) (Set.mem_univ (s + d))
  rw [zero_div, zero_mul] at h
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h)

/-- **Derivatives of a Taylor sum on the unit ball** (proof of [cartis2022evaluation],
Lemma 12.2.7, with (A.33)): if `‖D_i‖ ≤ L` for `i = ℓ, …, p` and `‖s‖ ≤ 1`, then
`‖∇^ℓ T_p(s)‖ ≤ 3 L`. -/
theorem norm_iteratedFDeriv_taylorSum_le_three_mul {ℓ p : ℕ} {L : ℝ} (hL : 0 ≤ L)
    (hD : ∀ i ∈ Icc ℓ p, ‖D i‖ ≤ L) {s : E} (hs : ‖s‖ ≤ 1) :
    ‖iteratedFDeriv ℝ ℓ (D.taylorSum p) s‖ ≤ 3 * L := by
  calc ‖iteratedFDeriv ℝ ℓ (D.taylorSum p) s‖
      ≤ ∑ i ∈ Icc ℓ p, ‖D i‖ * ‖s‖ ^ (i - ℓ) / ((i - ℓ)! : ℝ) :=
        D.norm_iteratedFDeriv_taylorSum_le p ℓ s
    _ ≤ ∑ i ∈ Icc ℓ p, L * (‖s‖ ^ (i - ℓ) / ((i - ℓ)! : ℝ)) :=
        sum_le_sum fun i hi => by rw [mul_div_assoc]; gcongr; exact hD i hi
    _ = L * ∑ i ∈ Icc ℓ p, ‖s‖ ^ (i - ℓ) / ((i - ℓ)! : ℝ) := (mul_sum _ _ _).symm
    _ ≤ L * (1 + 2 * ‖s‖) := by
        gcongr; exact sum_pow_div_factorial_le_one_add_two_mul (norm_nonneg _) hs ℓ p
    _ ≤ 3 * L := by nlinarith


end FormalMultilinearSeries

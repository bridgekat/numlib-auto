import Mathlib.Algebra.Order.Star.Real
import Numlib.Surface.FongSaunders.Sec4

/-!
# §5: Table 5.1, the summary of monotonicity properties

Surface file for D. C.-L. Fong and M. A. Saunders, *CG versus MINRES: an empirical
comparison*, SQU Journal for Science **17** (2012) 44–62 (Report SOL 2011-2R).

Table 5.1 collects the monotonicity properties of CG and MINRES on a symmetric positive definite
system.  `MonotoneProfile` and `MinresProfile` package the rows of the table; `cg_profile`,
`minres_profile` and `cr_profile` are the table's ↗/↘ entries, assembled from §2 and §3.  The two
"not monotonic" entries of the CG column are read as the existence of counterexamples and proved
by explicit computation on diagonal matrices.

Left out (see `tracker/fongsaunders.md`): Table 5.2 and the §5 discussion of the
least-squares solvers LSQR and LSMR, which are results of other papers.

The extra import `Mathlib.Algebra.Order.Star.Real` provides the instance `StarOrderedRing ℝ`
required by `Matrix.posDef_diagonal_iff` in the counterexamples.
-/

namespace FongSaunders

open Krylov Matrix

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {b : Vec n}

/-! ### D11: the rows of Table 5.1 -/

/-- Rows 1–3 of Table 5.1 for a sequence of iterates `x_k` with exact solution `x*`: the norm of
the iterate increases, the error and the energy norm of the error decrease. -/
structure MonotoneProfile (A : Matrix (Fin n) (Fin n) ℝ) (xstar : Vec n) (x : ℕ → Vec n) :
    Prop where
  /-- `‖x_k‖ ↗` (CG: Steihaug Thm 2.1; MINRES: Thm 2.3). -/
  norm_iterate : Monotone fun k => ‖x k‖
  /-- `‖x* − x_k‖ ↘` (CG: Hestenes–Stiefel Thm 4:3; MINRES: Thm 2.4). -/
  norm_error : Antitone fun k => ‖xstar - x k‖
  /-- `‖x* − x_k‖_A ↘` (CG: Hestenes–Stiefel Thm 6:3; MINRES: Thm 2.5). -/
  energyNorm_error : Antitone fun k => energyNorm A (xstar - x k)

/-- All five rows of Table 5.1, i.e. the MINRES column: the three rows of `MonotoneProfile`
together with the monotone residual norm and the monotone backward error. -/
structure MinresProfile (A : Matrix (Fin n) (Fin n) ℝ) (b xstar : Vec n) (x : ℕ → Vec n) : Prop
    extends MonotoneProfile A xstar x where
  /-- `‖r_k‖ ↘` (Hestenes–Stiefel Thm 7:2). -/
  norm_residual : Antitone fun k => ‖b - A ⬝ x k‖
  /-- `‖r_k‖/‖x_k‖ ↘` (Thm 3.1); at `k = 0` the ratio is `‖b‖/0`, so the row is stated for
  `k ≥ 1`. -/
  backwardError : AntitoneOn (fun k => ‖b - A ⬝ x k‖ / ‖x k‖) (Set.Ici 1)

/-! ### R5.1: the monotone entries of Table 5.1 -/

/-- Table 5.1, CG column (rows 1–3): `‖x_k‖ ↗`, `‖x* − x_k‖ ↘`, `‖x* − x_k‖_A ↘`. -/
theorem cg_profile (hA : A.PosDef) {xstar : Vec n} (hstar : A ⬝ xstar = b) :
    MonotoneProfile A xstar fun k => (cg A b k).x where
  norm_iterate := by
    simp only [cg_x]
    exact CG.norm_iterate_monotone b (isSymmetricCoercive_of_posDef hA)
  norm_error := by
    simp only [cg_x]
    exact CG.norm_error_antitone b 0 (isSymmetricCoercive_of_posDef hA) hstar
  energyNorm_error := by
    simp only [energyNorm_eq, cg_x]
    exact CG.energyNorm_error_antitone b 0 (isSymmetricCoercive_of_posDef hA) hstar

/-- Table 5.1, MINRES column (all five rows). -/
theorem minres_profile (hA : A.PosDef) (hb : b ≠ 0) {xstar : Vec n} (hstar : A ⬝ xstar = b)
    {x : ℕ → Vec n} (hx : ∀ k, IsMinresIterate A b k (x k)) : MinresProfile A b xstar x where
  norm_iterate := theorem_2_3_minres hA hx
  norm_error := theorem_2_4_minres hA hstar hx
  energyNorm_error := theorem_2_5_minres_antitone hA hstar hx
  norm_residual :=
    Krylov.IsMinResIterate.norm_residual_antitone fun k => isMinresIterate_iff.1 (hx k)
  backwardError :=
    Krylov.IsMinResIterate.norm_residual_div_norm_antitoneOn
      (isSymmetricCoercive_of_posDef hA) (fun k => isMinresIterate_iff.1 (hx k)) hb

/-- Table 5.1, MINRES column, for the CR iterates (which are the MINRES iterates, R2.2). -/
theorem cr_profile (hA : A.PosDef) (hb : b ≠ 0) {xstar : Vec n} (hstar : A ⬝ xstar = b) :
    MinresProfile A b xstar fun k => (cr A b k).x :=
  minres_profile hA hb hstar fun k => cr_isMinresIterate hA k

/-! ### R5.2: the two "not monotonic" entries of the CG column

Table 5.1 leaves the CG entries for `‖r_k‖` and `‖r_k‖/‖x_k‖` blank ("not monotonic").  Read
faithfully, this is the *existence* of a symmetric positive definite system on which the two
quantities fail to be monotonic; both witnesses below are diagonal.
-/

section Counterexamples

open EuclideanSpace

/-- The inner product in coordinates. -/
private theorem inner_eq (u v : Vec n) :
    ⟪u, v⟫_ℝ = ∑ i, WithLp.ofLp u i * WithLp.ofLp v i := by
  simp [PiLp.inner_apply, mul_comm]

/-- The `2 × 2` witness `A = diag(1, 9)`. -/
private def A2 : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1, 9]

/-- The `2 × 2` witness `b = (3, 1)ᵀ`. -/
private def b2 : Vec 2 := !₂[3, 1]

private theorem posDef_A2 : A2.PosDef := by
  rw [A2, Matrix.posDef_diagonal_iff]
  intro i
  fin_cases i <;> norm_num

private theorem rho2_zero : (cg A2 b2 0).ρ = 10 := by
  simp only [cg_zero, cgInit, real_norm_sq_eq, b2, Fin.sum_univ_two, cons_val_zero,
    cons_val_one]
  norm_num

private theorem rho2_one : (cg A2 b2 1).ρ = 160 / 9 := by
  rw [cg_succ, cg_zero]
  simp only [cgStep, cgInit, inner_eq, real_norm_sq_eq, WithLp.ofLp_sub,
    WithLp.ofLp_smul, ofLp_mulVecE, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, b2, A2,
    Fin.sum_univ_two, mulVec_diagonal, cons_val_zero, cons_val_one]
  norm_num

/-- R5.2, first entry: the CG residual norm is not monotonic.  On `A = diag(1, 9)` with
`b = (3, 1)ᵀ` one has `‖r_0‖² = 10` and `‖r_1‖² = 160/9 > 10`. -/
theorem cg_norm_residual_not_antitone :
    ∃ (A : Matrix (Fin 2) (Fin 2) ℝ) (b : Vec 2), A.PosDef ∧
      ¬ Antitone fun k => ‖(cg A b k).r‖ := by
  refine ⟨A2, b2, posDef_A2, fun h => ?_⟩
  have h0 : ‖(cg A2 b2 0).r‖ ^ 2 = 10 := by rw [← cg_rho, rho2_zero]
  have h1 : ‖(cg A2 b2 1).r‖ ^ 2 = 160 / 9 := by rw [← cg_rho, rho2_one]
  have hle := h (Nat.zero_le 1)
  simp only at hle
  nlinarith [norm_nonneg (cg A2 b2 0).r, norm_nonneg (cg A2 b2 1).r]

/-- The `3 × 3` witness `A = diag(1, 13, 16)`. -/
private def A3 : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![1, 13, 16]

/-- The `3 × 3` witness `b = (1, 5, 1)ᵀ`. -/
private def b3 : Vec 3 := !₂[1, 5, 1]

private theorem posDef_A3 : A3.PosDef := by
  rw [A3, Matrix.posDef_diagonal_iff]
  intro i
  fin_cases i <;> norm_num

private theorem cg3_one_x : WithLp.ofLp (cg A3 b3 1).x = ![3 / 38, 15 / 38, 3 / 38] := by
  rw [cg_succ, cg_zero]
  simp only [cgStep, cgInit, inner_eq, real_norm_sq_eq, WithLp.ofLp_add,
    WithLp.ofLp_sub, WithLp.ofLp_smul, ofLp_mulVecE, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    b3, A3,
    Fin.sum_univ_three, mulVec_diagonal, cons_val_two, tail_cons, head_cons]
  funext i
  fin_cases i <;> norm_num [mulVec_diagonal, cons_val_two, tail_cons, head_cons]

private theorem cg3_one_r : WithLp.ofLp (cg A3 b3 1).r = ![35 / 38, -5 / 38, -5 / 19] := by
  rw [cg_succ, cg_zero]
  simp only [cgStep, cgInit, inner_eq, real_norm_sq_eq, WithLp.ofLp_sub,
    WithLp.ofLp_smul, ofLp_mulVecE, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, b3, A3,
    Fin.sum_univ_three,
    mulVec_diagonal, cons_val_two, tail_cons, head_cons]
  funext i
  fin_cases i <;> norm_num [mulVec_diagonal, cons_val_two, tail_cons, head_cons]

private theorem cg3_one_p :
    WithLp.ofLp (cg A3 b3 1).p = ![345 / 361, 15 / 361, -165 / 722] := by
  rw [cg_succ, cg_zero]
  simp only [cgStep, cgInit, inner_eq, real_norm_sq_eq, WithLp.ofLp_add, WithLp.ofLp_sub,
    WithLp.ofLp_smul, ofLp_mulVecE, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    b3, A3, Fin.sum_univ_three, mulVec_diagonal, cons_val_two, tail_cons, head_cons]
  funext i
  fin_cases i <;>
    norm_num [mulVec_diagonal, cons_val_two, tail_cons, head_cons, vecHead, vecTail]

private theorem cg3_one_rho : (cg A3 b3 1).ρ = 675 / 722 := by
  rw [cg_succ, cg_zero]
  simp only [cgStep, cgInit, inner_eq, real_norm_sq_eq, WithLp.ofLp_sub,
    WithLp.ofLp_smul, ofLp_mulVecE, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, b3, A3,
    Fin.sum_univ_three,
    mulVec_diagonal, cons_val_two, tail_cons, head_cons]
  norm_num

private theorem cg3_two : cg A3 b3 2 = cgStep A3 (cg A3 b3 1) := cg_succ 1

private theorem cg3_two_x : WithLp.ofLp (cg A3 b3 2).x = ![7 / 12, 5 / 12, -1 / 24] := by
  rw [cg3_two]
  simp only [cgStep, inner_eq, WithLp.ofLp_add, WithLp.ofLp_smul, ofLp_mulVecE,
    cg3_one_x, cg3_one_p, cg3_one_rho]
  simp only [A3, Fin.sum_univ_three, mulVec_diagonal, cons_val_zero, cons_val_one, cons_val_two,
    tail_cons, head_cons]
  funext i
  fin_cases i <;>
    norm_num [mulVec_diagonal, cons_val_two, tail_cons, head_cons, vecHead, vecTail]

private theorem cg3_two_r : WithLp.ofLp (cg A3 b3 2).r = ![5 / 12, -5 / 12, 5 / 3] := by
  rw [cg3_two]
  simp only [cgStep, inner_eq, WithLp.ofLp_sub, WithLp.ofLp_smul, ofLp_mulVecE, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, cg3_one_r, cg3_one_p, cg3_one_rho]
  simp only [A3, Fin.sum_univ_three, mulVec_diagonal, cons_val_zero, cons_val_one, cons_val_two,
    tail_cons, head_cons]
  funext i
  fin_cases i <;>
    norm_num [mulVec_diagonal, cons_val_two, tail_cons, head_cons, vecHead, vecTail]

/-- R5.2, second entry: the CG backward error `‖r_k‖/‖x_k‖` is not monotonic on `k ≥ 1`.  On
`A = diag(1, 13, 16)` with `b = (1, 5, 1)ᵀ` one has `(‖r_1‖/‖x_1‖)² = 50/9 < 200/33 =
(‖r_2‖/‖x_2‖)²`.  No `2 × 2` witness exists: there `r_2 = 0`. -/
theorem cg_backwardError_not_antitoneOn :
    ∃ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n), A.PosDef ∧
      ¬ AntitoneOn (fun k => ‖(cg A b k).r‖ / ‖(cg A b k).x‖) (Set.Ici 1) := by
  refine ⟨3, A3, b3, posDef_A3, fun h => ?_⟩
  have hx1 : ‖(cg A3 b3 1).x‖ ^ 2 = 243 / 1444 := by
    rw [real_norm_sq_eq, cg3_one_x]
    norm_num [Fin.sum_univ_three, cons_val_two, tail_cons, head_cons]
  have hr1 : ‖(cg A3 b3 1).r‖ ^ 2 = 675 / 722 := by
    rw [real_norm_sq_eq, cg3_one_r]
    norm_num [Fin.sum_univ_three, cons_val_two, tail_cons, head_cons]
  have hx2 : ‖(cg A3 b3 2).x‖ ^ 2 = 33 / 64 := by
    rw [real_norm_sq_eq, cg3_two_x]
    norm_num [Fin.sum_univ_three, cons_val_two, tail_cons, head_cons]
  have hr2 : ‖(cg A3 b3 2).r‖ ^ 2 = 25 / 8 := by
    rw [real_norm_sq_eq, cg3_two_r]
    norm_num [Fin.sum_univ_three, cons_val_two, tail_cons, head_cons]
  have hx1p : 0 < ‖(cg A3 b3 1).x‖ := by nlinarith [norm_nonneg (cg A3 b3 1).x]
  have hx2p : 0 < ‖(cg A3 b3 2).x‖ := by nlinarith [norm_nonneg (cg A3 b3 2).x]
  have hkey : ‖(cg A3 b3 1).r‖ * ‖(cg A3 b3 2).x‖ < ‖(cg A3 b3 2).r‖ * ‖(cg A3 b3 1).x‖ := by
    have hsq : (‖(cg A3 b3 1).r‖ * ‖(cg A3 b3 2).x‖) ^ 2
        < (‖(cg A3 b3 2).r‖ * ‖(cg A3 b3 1).x‖) ^ 2 := by
      rw [mul_pow, mul_pow, hr1, hx2, hr2, hx1]
      norm_num
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
  have hle := h (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 (by norm_num)) (by norm_num : (1 : ℕ) ≤ 2)
  simp only at hle
  rw [div_le_div_iff₀ hx2p hx1p] at hle
  linarith

end Counterexamples

end FongSaunders

import Mathlib.Algebra.Order.Star.Real
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Krylov.CG
import Numlib.Krylov.Iterate
import Numlib.Krylov.Monotonicity
import Numlib.Krylov.Subspace
import NumlibSurface.FongSaunders.Section04

/-!
# Fong–Saunders §5: Table 5.1, the summary of monotonicity properties

Surface file for D. C.-L. Fong and M. A. Saunders, *CG versus MINRES: an empirical comparison*, SQU
Journal for Science **17** (2012) 44–62 (Report SOL 2011-2R), §5.

Table 5.1 collects the monotonicity properties of CG and MINRES on a symmetric positive definite
system.  `MonotoneProfile` and `MinresProfile` package the rows of the table; `cg_profile`,
`minres_profile` and `cr_profile` are the table's ↗/↘ entries, assembled from §2 and §3.  The two
"not monotonic" entries of the CG column are read as the existence of counterexamples and proved
by explicit computation on diagonal matrices.

The `3 × 3` counterexample (4.2) of §4.2 is here too, since it is of the same shape and it is what
makes the table's MINRES column sharp: `minres_norm_iterate_not_monotone` and
`minres_backwardError_not_antitoneOn` exhibit a nonsingular *indefinite* system on which the two
rows Theorems 2.3 and 3.1 supply for MINRES both fail, and `indefinite_witness` shows that what
fails for it is exactly the hypothesis `A ≻ 0`.  Because that witness is nonsingular the MINRES
iterate is unique at every step, so the three statements quantify over *every* sequence of MINRES
iterates rather than over one algorithm's output.

Left out (see `plans/fongsaunders.md`): Table 5.2 and the §5 discussion of the
least-squares solvers LSQR and LSMR, which are results of other papers; and the MINRES-QLP
factorization argument of §4.2, whose missing ingredient is named in that plan.

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

/-! ### R4.6: the `3 × 3` indefinite counterexample (4.2)

§4.2 exhibits the nonsingular *indefinite* system `A = [[2,1,1],[1,0,1],[1,1,2]]`, `b = (0,1,1)ᵀ`
on which MINRES gives non-monotonic solution norms, and hence non-monotonic backward errors
(Figure 4.6).  It is the converse half of the paper's message: Theorems 2.3 and 3.1 assume
`A ≻ 0`, and this is the witness that the hypothesis cannot be dropped.

`A` is nonsingular (`det A = −2`), so the MINRES iterate is unique at every step
(`Krylov.existsUnique_isMinResIterate_of_injective`) and the two theorems below can be quantified
over *every* sequence of MINRES iterates without assuming positive definiteness anywhere.
-/

section Indefinite

open EuclideanSpace

/-- The `3 × 3` indefinite witness of (4.2). -/
private def A4 : Matrix (Fin 3) (Fin 3) ℝ := !![2, 1, 1; 1, 0, 1; 1, 1, 2]

/-- The right-hand side of (4.2). -/
private def b4 : Vec 3 := !₂[0, 1, 1]

/-- The first MINRES iterate of (4.2), `x_1 = (2/7) b`. -/
private noncomputable def x4one : Vec 3 := !₂[0, 2 / 7, 2 / 7]

/-- The second MINRES iterate of (4.2), `x_2 = (2/19) b + (1/19) A b`. -/
private noncomputable def x4two : Vec 3 := !₂[2 / 19, 3 / 19, 5 / 19]

/-- Multiplying by the identity matrix does nothing. -/
private theorem one_mulVecE (v : Vec n) : (1 : Matrix (Fin n) (Fin n) ℝ) ⬝ v = v := by
  change Matrix.toEuclideanLin 1 v = v
  rw [Matrix.toEuclideanLin_one]
  rfl

private theorem isSymm_A4 : A4.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A4]

private theorem det_A4 : A4.det = -2 := by
  norm_num [A4, Matrix.det_fin_three, cons_val_two, tail_cons, head_cons]

private theorem isUnit_det_A4 : IsUnit A4.det := by
  rw [det_A4]
  exact isUnit_iff_ne_zero.2 (by norm_num)

private theorem injective_A4 : Function.Injective (Matrix.toEuclideanLin A4) := by
  have h : Function.Injective A4.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det A4).2 isUnit_det_A4)
  intro u v huv
  refine WithLp.ofLp_injective 2 (h ?_)
  rw [← ofLp_mulVecE, ← ofLp_mulVecE]
  exact congrArg WithLp.ofLp huv

/-- `A b = (2, 1, 3)ᵀ`. -/
private theorem ofLp_A4_b4 : WithLp.ofLp (A4 ⬝ b4) = ![2, 1, 3] := by
  rw [ofLp_mulVecE]
  funext i
  fin_cases i <;>
    norm_num [A4, b4, Matrix.mulVec, dotProduct, Fin.sum_univ_three, cons_val_two, tail_cons,
      head_cons]

/-- `A² b = (8, 5, 9)ᵀ`. -/
private theorem ofLp_A4_A4_b4 : WithLp.ofLp (A4 ⬝ (A4 ⬝ b4)) = ![8, 5, 9] := by
  rw [ofLp_mulVecE, ofLp_A4_b4]
  funext i
  fin_cases i <;>
    norm_num [A4, Matrix.mulVec, dotProduct, Fin.sum_univ_three, cons_val_two, tail_cons,
      head_cons]

/-- The residual of `x_1`: `r_1 = (−4/7, 5/7, 1/7)ᵀ`. -/
private theorem ofLp_res_one : WithLp.ofLp (b4 - A4 ⬝ x4one) = ![-4 / 7, 5 / 7, 1 / 7] := by
  rw [WithLp.ofLp_sub, ofLp_mulVecE]
  funext i
  fin_cases i <;>
    norm_num [A4, b4, x4one, Matrix.mulVec, dotProduct, Fin.sum_univ_three, cons_val_two,
      tail_cons, head_cons]

/-- The residual of `x_2`: `r_2 = (−12/19, 12/19, 4/19)ᵀ`. -/
private theorem ofLp_res_two : WithLp.ofLp (b4 - A4 ⬝ x4two) = ![-12 / 19, 12 / 19, 4 / 19] := by
  rw [WithLp.ofLp_sub, ofLp_mulVecE]
  funext i
  fin_cases i <;>
    norm_num [A4, b4, x4two, Matrix.mulVec, dotProduct, Fin.sum_univ_three, cons_val_two,
      tail_cons, head_cons]

/-- The Krylov subspace is spanned by the powers, so orthogonality to `A 𝒦_k` is orthogonality
to the `k` vectors `A (A^i b)`. -/
private theorem inner_mulVecE_eq_zero_of_generators {m : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {b r : Vec n} (h : ∀ i < m, ⟪r, A ⬝ ((A ^ i) ⬝ b)⟫_ℝ = 0) :
    ∀ z ∈ krylov A b m, ⟪r, A ⬝ z⟫_ℝ = 0 := by
  intro z hz
  simp only [krylov] at hz
  induction hz using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact h i i.2
  | zero => rw [mulVecE_zero, inner_zero_right]
  | add u v _ _ hu hv => rw [mulVecE_add, inner_add_right, hu, hv, add_zero]
  | smul c u _ hu => rw [mulVecE_smul, real_inner_smul_right, hu, mul_zero]

/-- A point of `𝒦_k` whose residual is orthogonal to `A 𝒦_k` is a MINRES iterate: the
normal-equations characterization of the least-squares minimizer, specialized to `𝒦_k`. -/
private theorem isMinresIterate_of_orth {k : ℕ} {x : Vec n} (hmem : x ∈ krylov A b k)
    (horth : ∀ z ∈ krylov A b k, ⟪b - A ⬝ x, A ⬝ z⟫_ℝ = 0) : IsMinresIterate A b k x := by
  refine ⟨hmem, fun y hy => ?_⟩
  have hres : b - A ⬝ y = (b - A ⬝ x) - A ⬝ (y - x) := by rw [mulVecE_sub]; abel
  have h0 : ⟪b - A ⬝ x, A ⬝ (y - x)⟫_ℝ = 0 := horth _ (Submodule.sub_mem _ hy hmem)
  have hsq : ‖b - A ⬝ y‖ ^ 2 = ‖b - A ⬝ x‖ ^ 2 + ‖A ⬝ (y - x)‖ ^ 2 := by
    rw [hres, @norm_sub_sq_real, h0]
    ring
  nlinarith [norm_nonneg (b - A ⬝ y), norm_nonneg (b - A ⬝ x), sq_nonneg ‖A ⬝ (y - x)‖]

private theorem isMinresIterate_x4one : IsMinresIterate A4 b4 1 x4one := by
  refine isMinresIterate_of_orth ?_ (inner_mulVecE_eq_zero_of_generators ?_)
  · have hb : b4 ∈ krylov A4 b4 1 := by
      simp only [krylov]
      exact Submodule.subset_span ⟨0, by simp [one_mulVecE]⟩
    have hx : x4one = (2 / 7 : ℝ) • b4 := by
      refine WithLp.ofLp_injective 2 ?_
      funext i
      fin_cases i <;> norm_num [x4one, b4]
    rw [hx]
    exact Submodule.smul_mem _ _ hb
  · intro i hi
    interval_cases i
    rw [pow_zero, one_mulVecE, inner_eq, ofLp_res_one, ofLp_A4_b4]
    norm_num [Fin.sum_univ_three, cons_val_two, tail_cons, head_cons]

private theorem isMinresIterate_x4two : IsMinresIterate A4 b4 2 x4two := by
  refine isMinresIterate_of_orth ?_ (inner_mulVecE_eq_zero_of_generators ?_)
  · have hb : b4 ∈ krylov A4 b4 2 := by
      simp only [krylov]
      exact Submodule.subset_span ⟨0, by simp [one_mulVecE]⟩
    have hAb : A4 ⬝ b4 ∈ krylov A4 b4 2 := by
      simp only [krylov]
      exact Submodule.subset_span ⟨1, by simp⟩
    have hx : x4two = (2 / 19 : ℝ) • b4 + (1 / 19 : ℝ) • (A4 ⬝ b4) := by
      refine WithLp.ofLp_injective 2 ?_
      rw [WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_smul, ofLp_A4_b4]
      funext i
      fin_cases i <;> norm_num [x4two, b4]
    rw [hx]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hb) (Submodule.smul_mem _ _ hAb)
  · intro i hi
    interval_cases i
    · rw [pow_zero, one_mulVecE, inner_eq, ofLp_res_two, ofLp_A4_b4]
      norm_num [Fin.sum_univ_three, cons_val_two, tail_cons, head_cons]
    · rw [pow_one, inner_eq, ofLp_res_two, ofLp_A4_A4_b4]
      norm_num [Fin.sum_univ_three, cons_val_two, tail_cons, head_cons]

/-- The MINRES iterate of the witness system is unique at every step, because `A` is
nonsingular. -/
private theorem eq_of_isMinresIterate {k : ℕ} {x y : Vec 3} (hx : IsMinresIterate A4 b4 k x)
    (hy : IsMinresIterate A4 b4 k y) : x = y := by
  obtain ⟨z, _, hz⟩ := Krylov.existsUnique_isMinResIterate_of_injective injective_A4 b4 0 k
  rw [hz x (isMinresIterate_iff.1 hx), hz y (isMinresIterate_iff.1 hy)]

private theorem norm_sq_x4one : ‖x4one‖ ^ 2 = 8 / 49 := by
  rw [real_norm_sq_eq]
  simp [x4one, Fin.sum_univ_three]
  norm_num

private theorem norm_sq_x4two : ‖x4two‖ ^ 2 = 2 / 19 := by
  rw [real_norm_sq_eq]
  simp [x4two, Fin.sum_univ_three]
  norm_num

private theorem norm_sq_res_one : ‖b4 - A4 ⬝ x4one‖ ^ 2 = 6 / 7 := by
  rw [real_norm_sq_eq, ofLp_res_one]
  simp [Fin.sum_univ_three]
  norm_num

private theorem norm_sq_res_two : ‖b4 - A4 ⬝ x4two‖ ^ 2 = 16 / 19 := by
  rw [real_norm_sq_eq, ofLp_res_two]
  simp [Fin.sum_univ_three]
  norm_num

/-- **§4.2**: the witness of (4.2) is indefinite — `⟪A e_0, e_0⟫ = 2 > 0` while
`⟪A w, w⟫ = −2 < 0` at `w = (1, −2, 1)ᵀ` — so the hypothesis `A ≻ 0` of Theorems 2.3 and 3.1
fails for it, and it is nonsingular, so MINRES is defined at every step. -/
theorem indefinite_witness :
    ∃ (A : Matrix (Fin 3) (Fin 3) ℝ) (u w : Vec 3), A.IsSymm ∧ IsUnit A.det ∧
      0 < ⟪u, A ⬝ u⟫_ℝ ∧ ⟪w, A ⬝ w⟫_ℝ < 0 := by
  refine ⟨A4, !₂[1, 0, 0], !₂[1, -2, 1], isSymm_A4, isUnit_det_A4, ?_, ?_⟩
  · rw [inner_eq, ofLp_mulVecE]
    norm_num [A4, Matrix.mulVec, dotProduct, Fin.sum_univ_three, cons_val_two, tail_cons,
      head_cons]
  · rw [inner_eq, ofLp_mulVecE]
    norm_num [A4, Matrix.mulVec, dotProduct, Fin.sum_univ_three, cons_val_two, tail_cons,
      head_cons]

/-- **§4.2, (4.2), first half**: on the nonsingular indefinite system
`A = [[2,1,1],[1,0,1],[1,1,2]]`,
`b = (0,1,1)ᵀ`, MINRES produces non-monotonic solution norms.  The iterates are
`x_1 = (0, 2/7, 2/7)ᵀ` and `x_2 = (2/19, 3/19, 5/19)ᵀ` with `‖x_1‖² = 8/49 > 2/19 = ‖x_2‖²`, so
Theorem 2.3 fails as soon as `A ≻ 0` is dropped. -/
theorem minres_norm_iterate_not_monotone :
    ∃ (A : Matrix (Fin 3) (Fin 3) ℝ) (b : Vec 3), A.IsSymm ∧ IsUnit A.det ∧
      ∀ x : ℕ → Vec 3, (∀ k, IsMinresIterate A b k (x k)) → ¬ Monotone fun k => ‖x k‖ := by
  refine ⟨A4, b4, isSymm_A4, isUnit_det_A4, fun x hx hmono => ?_⟩
  have h1 : x 1 = x4one := eq_of_isMinresIterate (hx 1) isMinresIterate_x4one
  have h2 : x 2 = x4two := eq_of_isMinresIterate (hx 2) isMinresIterate_x4two
  have hle := hmono (by norm_num : (1 : ℕ) ≤ 2)
  simp only [h1, h2] at hle
  nlinarith [norm_sq_x4one, norm_sq_x4two, norm_nonneg x4one, norm_nonneg x4two]

/-- **§4.2, (4.2), second half**: on the same system the MINRES backward errors `‖r_k‖/‖x_k‖` are
not monotonic either — `(‖r_1‖/‖x_1‖)² = 21/4 < 8 = (‖r_2‖/‖x_2‖)²` — so Theorem 3.1 also fails
without `A ≻ 0`.  This is the content of Figure 4.6. -/
theorem minres_backwardError_not_antitoneOn :
    ∃ (A : Matrix (Fin 3) (Fin 3) ℝ) (b : Vec 3), A.IsSymm ∧ IsUnit A.det ∧
      ∀ x : ℕ → Vec 3, (∀ k, IsMinresIterate A b k (x k)) →
        ¬ AntitoneOn (fun k => ‖b - A ⬝ x k‖ / ‖x k‖) (Set.Ici 1) := by
  refine ⟨A4, b4, isSymm_A4, isUnit_det_A4, fun x hx hanti => ?_⟩
  have h1 : x 1 = x4one := eq_of_isMinresIterate (hx 1) isMinresIterate_x4one
  have h2 : x 2 = x4two := eq_of_isMinresIterate (hx 2) isMinresIterate_x4two
  have hx1p : 0 < ‖x4one‖ := by nlinarith [norm_sq_x4one, norm_nonneg x4one]
  have hx2p : 0 < ‖x4two‖ := by nlinarith [norm_sq_x4two, norm_nonneg x4two]
  have hle := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 (by norm_num)) (by norm_num : (1:ℕ) ≤ 2)
  simp only [h1, h2] at hle
  rw [div_le_div_iff₀ hx2p hx1p] at hle
  have hkey : ‖b4 - A4 ⬝ x4one‖ * ‖x4two‖ < ‖b4 - A4 ⬝ x4two‖ * ‖x4one‖ := by
    refine lt_of_pow_lt_pow_left₀ 2 (by positivity) ?_
    rw [mul_pow, mul_pow, norm_sq_res_one, norm_sq_x4two, norm_sq_res_two, norm_sq_x4one]
    norm_num
  linarith

end Indefinite

end FongSaunders

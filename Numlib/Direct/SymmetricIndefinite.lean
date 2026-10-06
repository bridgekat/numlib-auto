import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.LinearAlgebra.Matrix.CauchyBinet
import Numlib.LinearAlgebra.Matrix.LeastSquares.Weighted
import Numlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Symmetric indefinite systems: Bunch–Parlett growth and the Stewart–Todd bound

Numerical facts about symmetric indefinite systems ([golub2013matrix] §4.4.4–4.4.5;
[higham2002accuracy] Ch. 11; Bunch–Parlett 1971; Stewart 1989, Todd 1990): the element growth of
Bunch–Parlett pivoting, and the uniform bound on weighted least-squares operators behind the
equilibrium systems.

One step of a block `L D Lᵀ` factorization eliminates either one pivot (`1 × 1`, the Schur
complement `Matrix.schurComplementSingle`) or a `2 × 2` pivot block (`Matrix.schurComplement` of
the block indexing `{p, q} ⊕ rest`). With `μ₀ = max |a_ij|` and `μ₁ = max |a_ii|`, the
Bunch–Parlett rule takes a `1 × 1` pivot when `μ₁ ≥ α μ₀` and the `2 × 2` pivot of an off-diagonal
entry of modulus `μ₀` otherwise; the two element-growth bounds are

* `BunchParlett.abs_schurComplementSingle_le` ([golub2013matrix] (4.4.16)): `|ã_ij| ≤ (1 + α⁻¹) μ₀`;
* `BunchParlett.abs_schurComplement_two_le` ([golub2013matrix] (4.4.17)):
  `|ã_ij| ≤ (3 − α)/(1 − α) μ₀`, the pivot block being nonsingular;

and `BunchParlett.alpha_eq` identifies the parameter `α = (1 + √17)/8` that equates the growth
of two `1 × 1` steps with that of one `2 × 2` step.

For the equilibrium systems of §4.4.5, `Matrix.exists_forall_l2_opNorm_weightedLeastSquaresOp_le`
is the Stewart–Todd bound (4.4.21): the weighted least-squares operators `(Bᵀ D B)⁻¹ Bᵀ D` of a
matrix of full column rank are bounded uniformly in the positive diagonal weights. Its proof goes
through the Cauchy–Binet formula (`Matrix.factorial_mul_det_transpose_mul_diagonal_mul` of
`Numlib/LinearAlgebra/Matrix/CauchyBinet`, stated symmetrized over the orderings of the row
selections so that no sorted subsets appear), which writes the operator as a convex combination
of the inverses of the nonsingular `p × p` row submatrices.

The specifications of the factorizations themselves (`Matrix.IsAasen`, `Matrix.IsBlockLDL`) are
in `Numlib/LinearAlgebra/Matrix/SymmetricIndefinite`; the equilibrium matrix `[C B; Bᵀ 0]` of
§4.4.5 is `Matrix.saddleMatrix` of `Numlib/LinearAlgebra/Matrix/SchurComplement`.

The hypotheses are the weakest the arguments use: the `1 × 1` bound needs only
`α μ₀ ≤ |a_pp|` (the maximal diagonal entry is one such pivot), the `2 × 2` bound only
`|a_pp|, |a_qq| ≤ α μ₀` and `|a_qp| = μ₀`.
-/

open Matrix

/-! ### Element growth of the Bunch–Parlett pivoting strategy -/

namespace BunchParlett

variable {n : Type*}

/-- **The `1 × 1` Bunch–Parlett step** ([golub2013matrix] (4.4.16), P4.4.6): if every entry of
`A` has modulus at most `μ₀ > 0` and the pivot satisfies `α μ₀ ≤ |a_pp|` (`α > 0`; the book takes
`p` with `|a_pp| = μ₁ = max |a_ii| ≥ α μ₀`), every entry of the Schur complement
`Ã = B − v vᵀ / a_pp` has `|ã_ij| ≤ (1 + α⁻¹) μ₀`:
`|a_ij − a_ip a_pj / a_pp| ≤ μ₀ + μ₀² / |a_pp| ≤ μ₀ + μ₀ / α`. -/
theorem abs_schurComplementSingle_le {A : Matrix n n ℝ} {p : n} {α μ₀ : ℝ} (hα : 0 < α)
    (hμ₀ : 0 < μ₀) (hA : ∀ i j, |A i j| ≤ μ₀) (hp : α * μ₀ ≤ |A p p|)
    (i j : {i : n // i ≠ p}) :
    |A.schurComplementSingle p i j| ≤ (1 + α⁻¹) * μ₀ := by
  have hαμ : 0 < α * μ₀ := mul_pos hα hμ₀
  rw [schurComplementSingle_apply]
  calc |A i.1 j.1 - A i.1 p * (A p p)⁻¹ * A p j.1|
      ≤ |A i.1 j.1| + |A i.1 p * (A p p)⁻¹ * A p j.1| := abs_sub _ _
    _ = |A i.1 j.1| + |A i.1 p| * |A p j.1| / |A p p| := by
        rw [abs_mul, abs_mul, abs_inv]
        ring
    _ ≤ μ₀ + μ₀ * μ₀ / (α * μ₀) := by
        gcongr
        · exact hA _ _
        · exact hA _ _
        · exact hA _ _
    _ = (1 + α⁻¹) * μ₀ := by
        field_simp

/-- The Schur complement of a `2 × 2` pivot block: with the pivot rows `p`, `q` first,
`ã_ij = a_ij − [a_ip a_iq] E⁻¹ [a_pj; a_qj]`, `E⁻¹ = det(E)⁻¹ adj(E)`. -/
private theorem schurComplement_two_apply (A : Matrix n n ℝ) (p q : n)
    (i j : {i : n // i ≠ p ∧ i ≠ q}) :
    (A.submatrix (Sum.elim ![p, q] Subtype.val) (Sum.elim ![p, q] Subtype.val)).schurComplement
        i j =
      A i j - (A i p * (A q q * A p j - A p q * A q j) + A i q * (A p p * A q j - A q p * A p j))
        / (A p p * A q q - A p q * A q p) := by
  simp only [schurComplement_eq, Matrix.sub_apply, toBlocks₂₂, toBlocks₂₁, toBlocks₁₁,
    toBlocks₁₂, inv_def, adjugate_fin_two, det_fin_two, Ring.inverse_eq_inv', mul_apply,
    Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_two, of_apply, submatrix_apply, Sum.elim_inl,
    Sum.elim_inr]
  simp only [cons_val_zero, cons_val_one, cons_val_fin_one, Fin.isValue]
  ring

/-- **The `2 × 2` Bunch–Parlett step** ([golub2013matrix] (4.4.17), P4.4.6): let `A` be symmetric
with every entry of modulus at most `μ₀ > 0`, `0 < α < 1`, and a `2 × 2` pivot
`E = A{p, q}` with `|a_qp| = μ₀` and `|a_pp|, |a_qq| ≤ α μ₀` (the book's case `μ₁ < α μ₀`). Then
`E` is nonsingular, `|det E| ≥ μ₀² − α²μ₀²`, and every entry of the Schur complement
`Ã = B − C E⁻¹ Cᵀ` has `|ã_ij| ≤ (3 − α)/(1 − α) μ₀`: an entry of `C adj(E) Cᵀ` is bounded by
`2 μ₀³ (1 + α)`, so `|(C E⁻¹ Cᵀ)_ij| ≤ 2 μ₀ / (1 − α)`. The Schur complement is
`Matrix.schurComplement` of the reindexing `{p, q} ⊕ rest`. -/
theorem abs_schurComplement_two_le {A : Matrix n n ℝ} (hA : A.IsSymm) {p q : n} {α μ₀ : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1) (hμ₀ : 0 < μ₀) (hAμ : ∀ i j, |A i j| ≤ μ₀) (hqp : |A q p| = μ₀)
    (hpp : |A p p| ≤ α * μ₀) (hqq : |A q q| ≤ α * μ₀) :
    IsUnit (A.submatrix ![p, q] ![p, q]) ∧
      ∀ i j : {i : n // i ≠ p ∧ i ≠ q},
        |(A.submatrix (Sum.elim ![p, q] Subtype.val)
          (Sum.elim ![p, q] Subtype.val)).schurComplement i j| ≤ (3 - α) / (1 - α) * μ₀ := by
  have hpq : A p q = A q p := by
    have := congrFun (congrFun hA q) p
    simpa [transpose_apply] using this
  have hαμ : 0 ≤ α * μ₀ := by positivity
  -- the determinant of the pivot block is bounded away from zero
  have hdet : μ₀ ^ 2 * (1 - α ^ 2) ≤ |A p p * A q q - A p q * A q p| := by
    have h1 : |A p p * A q q| ≤ (α * μ₀) ^ 2 := by
      rw [abs_mul, sq]
      exact mul_le_mul hpp hqq (abs_nonneg _) hαμ
    have h2 : |A p q * A q p| = μ₀ ^ 2 := by rw [abs_mul, hpq, hqp, sq]
    have h3 := abs_sub_abs_le_abs_sub (A p q * A q p) (A p p * A q q)
    rw [abs_sub_comm] at h3
    nlinarith
  have hdet₀ : 0 < μ₀ ^ 2 * (1 - α ^ 2) := by
    have : α ^ 2 < 1 := by nlinarith
    have : 0 < μ₀ ^ 2 := by positivity
    nlinarith
  have hD : A p p * A q q - A p q * A q p ≠ 0 := fun h => by
    rw [h, abs_zero] at hdet
    linarith
  refine ⟨?_, fun i j => ?_⟩
  · rw [isUnit_iff_isUnit_det, isUnit_iff_ne_zero, det_fin_two]
    simpa using hD
  rw [schurComplement_two_apply]
  have hN : |A i p * (A q q * A p j - A p q * A q j) + A i q * (A p p * A q j - A q p * A p j)|
      ≤ 2 * μ₀ ^ 3 * (1 + α) := by
    have e1 : |A q q * A p j - A p q * A q j| ≤ α * μ₀ * μ₀ + μ₀ * μ₀ := by
      refine (abs_sub _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
      · exact mul_le_mul hqq (hAμ _ _) (abs_nonneg _) hαμ
      · exact mul_le_mul (hAμ _ _) (hAμ _ _) (abs_nonneg _) hμ₀.le
    have e2 : |A p p * A q j - A q p * A p j| ≤ α * μ₀ * μ₀ + μ₀ * μ₀ := by
      refine (abs_sub _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
      · exact mul_le_mul hpp (hAμ _ _) (abs_nonneg _) hαμ
      · exact mul_le_mul (hAμ _ _) (hAμ _ _) (abs_nonneg _) hμ₀.le
    have hs : 0 ≤ α * μ₀ * μ₀ + μ₀ * μ₀ := by positivity
    calc _ ≤ |A i p * (A q q * A p j - A p q * A q j)| +
          |A i q * (A p p * A q j - A q p * A p j)| := abs_add_le _ _
      _ ≤ μ₀ * (α * μ₀ * μ₀ + μ₀ * μ₀) + μ₀ * (α * μ₀ * μ₀ + μ₀ * μ₀) := by
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul (hAμ _ _) e1 (abs_nonneg _) hμ₀.le)
            (mul_le_mul (hAμ _ _) e2 (abs_nonneg _) hμ₀.le)
      _ = 2 * μ₀ ^ 3 * (1 + α) := by ring
  have hq : |(A i p * (A q q * A p j - A p q * A q j) + A i q * (A p p * A q j - A q p * A p j))
      / (A p p * A q q - A p q * A q p)| ≤ 2 * μ₀ / (1 - α) := by
    rw [abs_div]
    calc _ ≤ 2 * μ₀ ^ 3 * (1 + α) / (μ₀ ^ 2 * (1 - α ^ 2)) :=
          div_le_div₀ (by positivity) hN hdet₀ hdet
      _ = 2 * μ₀ / (1 - α) := by
          rw [div_eq_div_iff hdet₀.ne' (by linarith)]
          ring
  calc _ ≤ |A i j| + |(A i p * (A q q * A p j - A p q * A q j) +
        A i q * (A p p * A q j - A q p * A p j)) / (A p p * A q q - A p q * A q p)| := abs_sub _ _
    _ ≤ μ₀ + 2 * μ₀ / (1 - α) := add_le_add (hAμ _ _) hq
    _ = (3 - α) / (1 - α) * μ₀ := by
        have : 1 - α ≠ 0 := by linarith
        field_simp
        ring

/-- **The Bunch–Parlett parameter** ([golub2013matrix] §4.4.4, "equating the growth factor of two
`s = 1` steps with that of one `s = 2` step"): `α = (1 + √17)/8` is the unique `α ∈ (0, 1)` with
`(1 + α⁻¹)² = (3 − α)/(1 − α)`. Clearing denominators, `(1 + α)² (1 − α) = α² (3 − α)`, which is
`4α² − α − 1 = 0` after the cubic terms cancel. -/
theorem alpha_eq :
    {α : ℝ | 0 < α ∧ α < 1 ∧ (1 + α⁻¹) ^ 2 = (3 - α) / (1 - α)} = {(1 + √17) / 8} := by
  have h17 : √17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have h17' : 0 ≤ √17 := Real.sqrt_nonneg _
  -- the equation is the quadratic `4α² − α − 1 = 0` on `(0, 1)`
  have key : ∀ α : ℝ, 0 < α → α < 1 →
      ((1 + α⁻¹) ^ 2 = (3 - α) / (1 - α) ↔ 4 * α ^ 2 - α - 1 = 0) := by
    intro α h0 h1
    have ha : α ≠ 0 := h0.ne'
    have hb : 1 - α ≠ 0 := by linarith
    have e : (1 + α⁻¹) ^ 2 * (1 - α) - (3 - α) = -(4 * α ^ 2 - α - 1) / α ^ 2 := by
      field_simp
      ring
    rw [eq_div_iff hb, ← sub_eq_zero, e, div_eq_zero_iff, neg_eq_zero,
      or_iff_left (pow_ne_zero 2 ha)]
  ext α
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h0, h1, h⟩
    have hq := (key α h0 h1).1 h
    have hsq : (8 * α - 1) ^ 2 = √17 ^ 2 := by rw [h17]; linear_combination 16 * hq
    have hnn : 0 ≤ 8 * α - 1 := by nlinarith
    have := (sq_eq_sq₀ hnn h17').1 hsq
    linarith
  · rintro rfl
    have hlt : √17 < 7 := by nlinarith
    refine ⟨by positivity, by linarith, (key _ (by positivity) (by linarith)).2 ?_⟩
    linear_combination h17 / 16

end BunchParlett

namespace Matrix

/-! ### The Stewart–Todd bound -/

/-- Cramer's rule, weighted: `det A · (Cramer A v)_k = det(A)² (A⁻¹ v)_k`, both sides vanishing for
a singular `A`. -/
private theorem det_mul_cramer_apply {p : Type*} [Fintype p] [DecidableEq p] (A : Matrix p p ℝ)
    (v : p → ℝ) (k : p) : A.det * cramer A v k = A.det ^ 2 * (A⁻¹ *ᵥ v) k := by
  by_cases hA : A.det = 0
  · rw [hA]
    ring
  · rw [inv_def, Ring.inverse_eq_inv', smul_mulVec, ← cramer_eq_adjugate_mulVec, Pi.smul_apply,
      smul_eq_mul]
    field_simp

open scoped Matrix.Norms.L2Operator in
/-- **The Stewart–Todd bound** ([golub2013matrix] (4.4.21); Stewart 1989, O'Leary 1990,
Todd 1990): for `B : Matrix n p ℝ` of full column rank the weighted least-squares operators
`(Bᵀ D B)⁻¹ Bᵀ D` are bounded independently of the positive diagonal weights `D`. By Cramer's
rule and the Cauchy–Binet formula, `(Bᵀ D B)⁻¹ Bᵀ D b = ∑_r λ_r B_r⁻¹ b_r`, a convex combination
over the row selections `r` with weights `λ_r ∝ (∏ d_{r i}) det(B_r)²` (Dikin; Ben-Tal–Teboulle),
so `ψ_B = √p ∑_r ‖B_r⁻¹‖₂` works. -/
theorem exists_forall_l2_opNorm_weightedLeastSquaresOp_le {n p : Type*} [Fintype n]
    [DecidableEq n] [Fintype p] [DecidableEq p] {B : Matrix n p ℝ}
    (hB : LinearIndependent ℝ Bᵀ) :
    ∃ ψ : ℝ, ∀ d : n → ℝ, (∀ i, 0 < d i) →
      ‖weightedLeastSquaresOp (diagonal d) B‖ ≤ ψ := by
  classical
  refine ⟨√(Fintype.card p : ℝ) * ∑ r : p → n, ‖(B.submatrix r id)⁻¹‖, fun d hd => ?_⟩
  set M := Bᵀ * diagonal d * B with hM
  have hW : weightedLeastSquaresOp (diagonal d) B = M⁻¹ * Bᵀ * diagonal d := by
    rw [weightedLeastSquaresOp_def, conjTranspose_eq_transpose_of_trivial]
  -- `Bᵀ D B` is positive definite
  have hinj := mulVec_injective_of_linearIndependent_transpose hB
  have hMpd : M.PosDef := by
    refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
    · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, hM, transpose_mul, transpose_mul,
        transpose_transpose, diagonal_transpose, Matrix.mul_assoc]
    · have hBx : B *ᵥ x ≠ 0 := fun h => hx (hinj (by rw [h, mulVec_zero]))
      rw [star_trivial, hM, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hBx
      simp only [dotProduct, mulVec_diagonal]
      refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
      · have := hd j
        nlinarith [mul_self_nonneg ((B *ᵥ x) j)]
      · have := hd i
        have := mul_self_pos.2 hi
        nlinarith
  have hdet : 0 < M.det := hMpd.det_pos
  -- Cauchy–Binet for `det M`
  have hfac : (0 : ℝ) < (Fintype.card p).factorial := by exact_mod_cast Nat.factorial_pos _
  set D := ((Fintype.card p).factorial : ℝ) * M.det with hD
  have hD0 : 0 < D := mul_pos hfac hdet
  have hDsum : D = ∑ r : p → n, (∏ i, d (r i)) * (B.submatrix r id).det ^ 2 := by
    rw [hD, factorial_mul_det_transpose_mul_diagonal_mul]
    exact Finset.sum_congr rfl fun r _ => by ring
  set lam : (p → n) → ℝ := fun r => (∏ i, d (r i)) * (B.submatrix r id).det ^ 2 / D with hlam
  have hlam0 : ∀ r, 0 ≤ lam r := fun r =>
    div_nonneg (mul_nonneg (Finset.prod_nonneg fun i _ => (hd _).le) (sq_nonneg _)) hD0.le
  have hlam1 : ∑ r, lam r = 1 := by
    rw [hlam, ← Finset.sum_div, ← hDsum, div_self hD0.ne']
  have hlamle : ∀ r, lam r ≤ 1 := fun r =>
    hlam1 ▸ Finset.single_le_sum (fun r _ => hlam0 r) (Finset.mem_univ r)
  refine l2_opNorm_le_of_forall_norm_toEuclideanLin_le _ (by positivity) fun b => ?_
  -- the solution as a convex combination of basic solutions
  set y : (p → n) → p → ℝ := fun r => (B.submatrix r id)⁻¹ *ᵥ fun i => WithLp.ofLp b (r i)
  have hx : WithLp.ofLp (toEuclideanLin (weightedLeastSquaresOp (diagonal d) B) b) =
      ∑ r, lam r • y r := by
    funext k
    have hWb : weightedLeastSquaresOp (diagonal d) B *ᵥ WithLp.ofLp b =
        M⁻¹ *ᵥ ((Bᵀ * diagonal d) *ᵥ WithLp.ofLp b) := by
      rw [hW, Matrix.mul_assoc, ← mulVec_mulVec]
    rw [ofLp_toEuclideanLin, hWb, inv_def, Ring.inverse_eq_inv', smul_mulVec,
      ← cramer_eq_adjugate_mulVec, Pi.smul_apply, smul_eq_mul, cramer_apply,
      Finset.sum_apply]
    -- the numerator by Cauchy–Binet
    have hupd : M.updateCol k ((Bᵀ * diagonal d) *ᵥ WithLp.ofLp b) =
        Bᵀ * diagonal d * B.updateCol k (WithLp.ofLp b) := by
      ext i j
      rw [updateCol_apply, mul_apply]
      split_ifs with hj
      · subst hj
        simp [mulVec, dotProduct]
      · simp [hM, mul_apply, hj]
    have hnum : ((Fintype.card p).factorial : ℝ) *
        (M.updateCol k ((Bᵀ * diagonal d) *ᵥ WithLp.ofLp b)).det =
        ∑ r : p → n, (∏ i, d (r i)) * (B.submatrix r id).det ^ 2 * y r k := by
      rw [hupd, factorial_mul_det_transpose_mul_diagonal_mul]
      refine Finset.sum_congr rfl fun r _ => ?_
      have : (B.updateCol k (WithLp.ofLp b)).submatrix r id =
          (B.submatrix r id).updateCol k fun i => WithLp.ofLp b (r i) := by
        ext i j
        simp [updateCol_apply]
      rw [this, ← cramer_apply, mul_assoc, det_mul_cramer_apply]
      ring
    have e : (M.det)⁻¹ * (M.updateCol k ((Bᵀ * diagonal d) *ᵥ WithLp.ofLp b)).det =
        (((Fintype.card p).factorial : ℝ) *
          (M.updateCol k ((Bᵀ * diagonal d) *ᵥ WithLp.ofLp b)).det) / D := by
      rw [hD]
      field_simp
    rw [e, hnum, Finset.sum_div]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, hlam]
    ring
  -- the norm estimate
  have hbr : ∀ r : p → n, ‖(WithLp.toLp 2 fun i => WithLp.ofLp b (r i) :
      EuclideanSpace ℝ p)‖ ≤ √(Fintype.card p : ℝ) * ‖b‖ := fun r => by
    refine le_of_sq_le_sq ?_ (by positivity)
    rw [mul_pow, Real.sq_sqrt (by positivity), EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖(WithLp.toLp 2 fun i => WithLp.ofLp b (r i) : EuclideanSpace ℝ p) i‖ ^ 2
        ≤ ∑ _i : p, ‖b‖ ^ 2 := Finset.sum_le_sum fun i _ =>
          pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le b (r i)) 2
      _ = (Fintype.card p : ℝ) * ‖b‖ ^ 2 := by simp
  have hy : ∀ r, ‖(WithLp.toLp 2 (y r) : EuclideanSpace ℝ p)‖ ≤
      ‖(B.submatrix r id)⁻¹‖ * (√(Fintype.card p : ℝ) * ‖b‖) := fun r => by
    rw [← toEuclideanLin_toLp]
    exact (norm_toEuclideanLin_apply_le _ _).trans
      (mul_le_mul_of_nonneg_left (hbr r) (norm_nonneg _))
  calc ‖toEuclideanLin (weightedLeastSquaresOp (diagonal d) B) b‖
      = ‖(WithLp.toLp 2 (∑ r, lam r • y r) : EuclideanSpace ℝ p)‖ := by
        rw [← hx]
    _ ≤ ∑ r, lam r * ‖(WithLp.toLp 2 (y r) : EuclideanSpace ℝ p)‖ := by
        rw [WithLp.toLp_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
        rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hlam0 r)]
    _ ≤ ∑ r, ‖(B.submatrix r id)⁻¹‖ * (√(Fintype.card p : ℝ) * ‖b‖) :=
        Finset.sum_le_sum fun r _ => (mul_le_mul (hlamle r) (hy r) (norm_nonneg _)
          zero_le_one).trans_eq (one_mul _)
    _ = √(Fintype.card p : ℝ) * (∑ r : p → n, ‖(B.submatrix r id)⁻¹‖) * ‖b‖ := by
        rw [← Finset.sum_mul]
        ring

end Matrix

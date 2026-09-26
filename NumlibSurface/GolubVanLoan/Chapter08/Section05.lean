import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.Eigen.Jacobi

/-!
# Golub–Van Loan §8.5: Jacobi methods

Surface file for [golub2013matrix] §8.5: the off-diagonal mass and Jacobi rotations (§8.5.1,
(8.5.1)–(8.5.2)), the two-by-two symmetric Schur decomposition (§8.5.2, (8.5.3), Algorithm 8.5.1),
the classical and cyclic-by-row algorithms (Algorithms 8.5.2–8.5.3) with the linear convergence of
the classical one, the block-Jacobi identity (§8.5.6) and the parallel ordering (§8.5.7).

## Conventions

The book's Jacobi rotation `J(p, q, θ)` has `c` at `(p, p)` and `(q, q)`, `s` at `(p, q)` and `-s`
at `(q, p)`; it is the backbone's `Matrix.planeRotation p q c (-s)`, which is chapter 5's
`givensRotation p q c s` ("Jacobi rotations are no different from Givens rotations", §8.5.1).
`off(A)` is `off A`, the square root of the backbone's `Matrix.offDiagNormSq`. The rotation of
Algorithm 8.5.1 is the backbone's `(Matrix.jacobiCosSmall, Matrix.jacobiSinSmall)`, and the
conjugation by it is `Matrix.jacobiStep`; the classical iteration is
`Matrix.classicalJacobiIterate`.

## Not formalized

The quadratic convergence of the classical and cyclic methods (Henrici, Schönhage, van Kempen,
Wilkinson — quoted without proof), Brent–Luk's `log n` sweep count, the error analysis of §8.5.5
including (8.5.4), and the flop counts.

## Sources

Backbone `Numlib/Eigen/Jacobi`, `Numlib/LinearAlgebra/Matrix/PlaneRotation`.
-/

open Matrix

namespace GolubVanLoan.Chapter08

variable {n : ℕ}

/-! ### §8.5.1 The Jacobi idea -/

/-- **§8.5.1, `off(A)`**: the Frobenius norm of the off-diagonal part,
`off(A) = √(∑_{i ≠ j} a_ij²)`. -/
noncomputable def off (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.sqrt (offDiagNormSq A)

/-- `off(A)² = ∑_{i ≠ j} a_ij²`. -/
theorem off_sq (A : Matrix (Fin n) (Fin n) ℝ) : off A ^ 2 = offDiagNormSq A :=
  Real.sq_sqrt (offDiagNormSq_nonneg A)

/-- `off(A)` is nonnegative. -/
theorem off_nonneg (A : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ off A :=
  Real.sqrt_nonneg _

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- `off(A)² = ‖A‖_F² - ∑_i a_ii²`. -/
theorem off_sq_eq (A : Matrix (Fin n) (Fin n) ℝ) : off A ^ 2 = ‖A‖ ^ 2 - ∑ i, A i i ^ 2 := by
  rw [off_sq, frobenius_norm_sq_eq_sum_sq]
  simp only [Real.norm_eq_abs, sq_abs]
  linarith [offDiagNormSq_add_sum_diag_sq_real A]

end Frobenius

/-- `(JᵀMJ)(q, p)` for a plane rotation `J`, from the `(p, q)` entry of the transpose. -/
private theorem conj_planeRotation_apply_kj {p q : Fin n} (hpq : p ≠ q)
    (M : Matrix (Fin n) (Fin n) ℝ) (c s : ℝ) :
    ((planeRotation p q c s)ᵀ * M * planeRotation p q c s) q p =
      c * (-s * M p p + c * M q p) + s * (-s * M p q + c * M q q) := by
  have h := conj_planeRotation_apply_jk (c := c) (s := s) hpq Mᵀ
  rw [← transpose_apply ((planeRotation p q c s)ᵀ * M * planeRotation p q c s),
    transpose_mul, transpose_mul, transpose_transpose, ← Matrix.mul_assoc]
  simpa using h

/-- **(8.5.1)** and the remark after it: for `B = J(p,q,θ)ᵀ A J(p,q,θ)`, `p ≠ q`, the `2 × 2` block
of `B` in rows and columns `p`, `q` is `[c s; -s c]ᵀ [a_pp a_pq; a_qp a_qq] [c s; -s c]`, and `B`
agrees with `A` outside rows and columns `p` and `q`. -/
theorem equation_8_5_1 (A : Matrix (Fin n) (Fin n) ℝ) {p q : Fin n} (hpq : p ≠ q) (c s : ℝ) :
    !![((planeRotation p q c (-s))ᵀ * A * planeRotation p q c (-s)) p p,
        ((planeRotation p q c (-s))ᵀ * A * planeRotation p q c (-s)) p q;
      ((planeRotation p q c (-s))ᵀ * A * planeRotation p q c (-s)) q p,
        ((planeRotation p q c (-s))ᵀ * A * planeRotation p q c (-s)) q q] =
      !![c, s; -s, c]ᵀ * !![A p p, A p q; A q p, A q q] * !![c, s; -s, c] ∧
    ∀ i j, i ≠ p → i ≠ q → j ≠ p → j ≠ q →
      ((planeRotation p q c (-s))ᵀ * A * planeRotation p q c (-s)) i j = A i j := by
  refine ⟨?_, fun i j hip hiq hjp hjq => conj_planeRotation_apply_of_ne hpq A hip hiq hjp hjq⟩
  rw [conj_planeRotation_apply_jj hpq, conj_planeRotation_apply_jk hpq,
    conj_planeRotation_apply_kj hpq, conj_planeRotation_apply_kk hpq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **(8.5.2).** For symmetric `A`, `p ≠ q`, `c² + s² = 1` and `B = J(p,q,θ)ᵀ A J(p,q,θ)` with
`b_pq = 0`: `a_pp² + a_qq² + 2 a_pq² = b_pp² + b_qq²` and `off(B)² = off(A)² - 2 a_pq²`. -/
theorem equation_8_5_2 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {p q : Fin n} (hpq : p ≠ q)
    {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1)
    (h0 : ((planeRotation p q c (-s))ᵀ * A * planeRotation p q c (-s)) p q = 0) :
    A p p ^ 2 + A q q ^ 2 + 2 * A p q ^ 2 =
        ((planeRotation p q c (-s))ᵀ * A * planeRotation p q c (-s)) p p ^ 2 +
          ((planeRotation p q c (-s))ᵀ * A * planeRotation p q c (-s)) q q ^ 2 ∧
      off ((planeRotation p q c (-s))ᵀ * A * planeRotation p q c (-s)) ^ 2 =
        off A ^ 2 - 2 * A p q ^ 2 := by
  have hcs' : c ^ 2 + (-s) ^ 2 = 1 := by rw [neg_sq]; exact hcs
  refine ⟨?_, ?_⟩
  · have hqp : A q p = A p q := hA.apply p q
    rw [conj_planeRotation_apply_jk hpq, hqp] at h0
    rw [conj_planeRotation_apply_jj hpq, conj_planeRotation_apply_kk hpq, hqp]
    linear_combination (-(c ^ 2 + s ^ 2 + 1) * (A p p ^ 2 + A q q ^ 2 + 2 * A p q ^ 2)) * hcs +
      (2 * (c * (-(-s) * A p p + c * A p q) + -s * (-(-s) * A p q + c * A q q))) * h0
  · rw [off_sq, off_sq]
    exact offDiagNormSq_conj_planeRotation_of_apply_eq_zero A hA hpq hcs' h0

/-! ### §8.5.2 The 2-by-2 symmetric Schur decomposition -/

/-- **(8.5.3)** and §8.5.2. For symmetric `A` and `p ≠ q`: the `(p, q)` entry of
`B = J(p,q,θ)ᵀ A J(p,q,θ)` is `b_pq = a_pq (c² - s²) + (a_pp - a_qq) c s`; if `a_pq ≠ 0` and
`c ≠ 0`, then with `τ = (a_qq - a_pp)/(2 a_pq)` and `t = s/c`, `b_pq = 0` iff `t² + 2τt - 1 = 0`;
the smaller root `t_min` (`Matrix.jacobiTanSmall`) solves it and has `|t_min| ≤ 1` (`|θ| ≤ π/4`);
and `c = 1/√(1 + t_min²)`, `s = t_min c` annihilate `b_pq`. -/
theorem equation_8_5_3 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {p q : Fin n}
    (hpq : p ≠ q) :
    (∀ c s : ℝ, ((planeRotation p q c (-s))ᵀ * A * planeRotation p q c (-s)) p q =
      A p q * (c ^ 2 - s ^ 2) + (A p p - A q q) * c * s) ∧
    (∀ c s : ℝ, A p q ≠ 0 → c ≠ 0 →
      (((planeRotation p q c (-s))ᵀ * A * planeRotation p q c (-s)) p q = 0 ↔
        (s / c) ^ 2 + 2 * ((A q q - A p p) / (2 * A p q)) * (s / c) - 1 = 0)) ∧
    (A p q ≠ 0 → jacobiTanSmall A p q ^ 2 +
      2 * ((A q q - A p p) / (2 * A p q)) * jacobiTanSmall A p q - 1 = 0) ∧
    |jacobiTanSmall A p q| ≤ 1 ∧
    jacobiCosSmall A p q = 1 / Real.sqrt (1 + jacobiTanSmall A p q ^ 2) ∧
    jacobiSinSmall A p q = jacobiTanSmall A p q * jacobiCosSmall A p q ∧
    ((planeRotation p q (jacobiCosSmall A p q) (-jacobiSinSmall A p q))ᵀ * A *
      planeRotation p q (jacobiCosSmall A p q) (-jacobiSinSmall A p q)) p q = 0 := by
  have hqp : A q p = A p q := hA.apply p q
  have hform : ∀ c s : ℝ, ((planeRotation p q c (-s))ᵀ * A * planeRotation p q c (-s)) p q =
      A p q * (c ^ 2 - s ^ 2) + (A p p - A q q) * c * s := fun c s => by
    rw [conj_planeRotation_apply_jk hpq, hqp]
    ring
  refine ⟨hform, fun c s ha hc => ?_, jacobiTanSmall_sq A p q, abs_jacobiTanSmall_le_one A p q,
    rfl, rfl, ?_⟩
  · have key : A p q * (c ^ 2 - s ^ 2) + (A p p - A q q) * c * s =
        -(c ^ 2 * A p q) * ((s / c) ^ 2 + 2 * ((A q q - A p p) / (2 * A p q)) * (s / c) - 1) := by
      field_simp
      ring
    rw [hform, key]
    constructor
    · intro h
      rcases mul_eq_zero.1 h with h | h
      · exact absurd (neg_eq_zero.1 h) (mul_ne_zero (pow_ne_zero 2 hc) ha)
      · exact h
    · intro h
      rw [h, mul_zero]
  · rw [hform]
    linear_combination jacobiSmall_annihilate A p q

/-- **Algorithm 8.5.1** (`symSchur2`): given symmetric `A` and `p < q`, the cosine–sine pair
`(c, s)` with `b_pq = b_qp = 0` for `B = J(p,q,θ)ᵀ A J(p,q,θ)`. Every `+ − × / √` result passes
through `rnd`; the tests `a_pq ≠ 0` and `τ ≥ 0` are exact comparisons. -/
noncomputable def algorithm_8_5_1 {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) : M (ℝ × ℝ) :=
  if A p q ≠ 0 then do
    let num ← rnd (A q q - A p p)
    let den ← rnd (2 * A p q)
    let τ ← rnd (num / den)
    let τ2 ← rnd (τ * τ)
    let r ← rnd (1 + τ2)
    let sq ← rnd (Real.sqrt r)
    let t ← if 0 ≤ τ then (do rnd (1 / (← rnd (τ + sq)))) else (do rnd (1 / (← rnd (τ - sq))))
    let t2 ← rnd (t * t)
    let u ← rnd (1 + t2)
    let v ← rnd (Real.sqrt u)
    let c ← rnd (1 / v)
    let s ← rnd (t * c)
    pure (c, s)
  else pure (1, 0)

/-- **Algorithm 8.5.1, exact semantics**: in exact arithmetic `symSchur2` returns the backbone's
small-angle pair `(Matrix.jacobiCosSmall A p q, Matrix.jacobiSinSmall A p q)`; hence for symmetric
`A` and `p ≠ q`, `J(p,q,θ)` is the backbone's `Matrix.jacobiRotation A p q` and
`b_pq = b_qp = 0`. -/
theorem algorithm_8_5_1_spec {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {p q : Fin n}
    (hpq : p ≠ q) :
    Id.run (algorithm_8_5_1 pure A p q) = (jacobiCosSmall A p q, jacobiSinSmall A p q) ∧
      planeRotation p q (Id.run (algorithm_8_5_1 pure A p q)).1
          (-(Id.run (algorithm_8_5_1 pure A p q)).2) = jacobiRotation A p q ∧
      ((jacobiRotation A p q)ᵀ * A * jacobiRotation A p q) p q = 0 ∧
      ((jacobiRotation A p q)ᵀ * A * jacobiRotation A p q) q p = 0 := by
  have hrun :
      Id.run (algorithm_8_5_1 pure A p q) = (jacobiCosSmall A p q, jacobiSinSmall A p q) := by
    by_cases h : A p q = 0
    · simp [algorithm_8_5_1, h, jacobiCosSmall, jacobiSinSmall, jacobiTanSmall]
    · unfold algorithm_8_5_1 jacobiSinSmall jacobiCosSmall jacobiTanSmall
      simp only [ne_eq, h, not_false_eq_true, ite_true, ite_false, pure_bind, sq]
      generalize (A q q - A p p) / (2 * A p q) = τ
      split_ifs with hτ
      · rfl
      · have : -1 / (-τ + Real.sqrt (1 + τ * τ)) = 1 / (τ - Real.sqrt (1 + τ * τ)) := by
          rw [show -τ + Real.sqrt (1 + τ * τ) = -(τ - Real.sqrt (1 + τ * τ)) by ring, div_neg,
            neg_div, neg_neg]
        rw [this]
        rfl
  have h0 := jacobiStep_apply_eq_zero A hA hpq
  refine ⟨hrun, by rw [hrun, jacobiRotation_eq_planeRotation_small], h0, ?_⟩
  have hsym := isSymm_jacobiStep hA p q
  change jacobiStep A p q q p = 0
  rw [hsym.apply p q]
  exact h0

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **§8.5.2, the distance moved by a Jacobi update.** With the rotation of Algorithm 8.5.1
(`c = 1/√(1 + t_min²)`, `s = t_min c`) and `B = J(p,q,θ)ᵀ A J(p,q,θ)`,
`‖B - A‖_F² = 4(1 - c) ∑_{i ≠ p,q} (a_ip² + a_iq²) + 2 a_pq² / c²` — which the choice of `t_min`
(maximal `c`) minimizes. -/
theorem jacobi_frobenius_dist {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {p q : Fin n}
    (hpq : p ≠ q) :
    ‖(planeRotation p q (jacobiCosSmall A p q) (-jacobiSinSmall A p q))ᵀ * A *
        planeRotation p q (jacobiCosSmall A p q) (-jacobiSinSmall A p q) - A‖ ^ 2 =
      4 * (1 - jacobiCosSmall A p q) *
          ∑ i ∈ (Finset.univ.erase p).erase q, (A i p ^ 2 + A i q ^ 2) +
        2 * A p q ^ 2 / jacobiCosSmall A p q ^ 2 := by
  rw [← jacobiRotation_eq_planeRotation_small, jacobiCosSmall_eq]
  change ‖jacobiStep A p q - A‖ ^ 2 = _
  set B := jacobiStep A p q with hBdef
  set C := jacobiCos A p q with hCdef
  set S := jacobiSin A p q with hSdef
  have hB : B = (planeRotation p q C S)ᵀ * A * planeRotation p q C S := rfl
  have hcs : C ^ 2 + S ^ 2 = 1 := jacobiCos_sq_add_jacobiSin_sq A p q
  have hqp : A q p = A p q := hA.apply p q
  have hmem : ∀ i, i ∈ (Finset.univ.erase p).erase q → i ≠ p ∧ i ≠ q := fun i hi => by
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hi
    exact ⟨hi.2, hi.1⟩
  -- the entries of `B`
  have hBij : ∀ i j, i ∈ (Finset.univ.erase p).erase q → j ∈ (Finset.univ.erase p).erase q →
      B i j = A i j := fun i j hi hj => by
    rw [hB]
    exact conj_planeRotation_apply_of_ne hpq A (hmem i hi).1 (hmem i hi).2 (hmem j hj).1
      (hmem j hj).2
  have hBip : ∀ i ∈ (Finset.univ.erase p).erase q, B i p = C * A i p + S * A i q := fun i hi => by
    rw [hB]; exact conj_planeRotation_apply_col_j hpq A (hmem i hi).1 (hmem i hi).2
  have hBiq : ∀ i ∈ (Finset.univ.erase p).erase q, B i q = -S * A i p + C * A i q :=
    fun i hi => by rw [hB]; exact conj_planeRotation_apply_col_k hpq A (hmem i hi).1 (hmem i hi).2
  have hBpj : ∀ j ∈ (Finset.univ.erase p).erase q, B p j = C * A p j + S * A q j := fun j hj => by
    rw [hB]; exact conj_planeRotation_apply_row_j hpq A (hmem j hj).1 (hmem j hj).2
  have hBqj : ∀ j ∈ (Finset.univ.erase p).erase q, B q j = -S * A p j + C * A q j :=
    fun j hj => by rw [hB]; exact conj_planeRotation_apply_row_k hpq A (hmem j hj).1 (hmem j hj).2
  have hBpq : B p q = 0 := jacobiStep_apply_eq_zero A hA hpq
  have hBqp : B q p = 0 := ((isSymm_jacobiStep hA p q).apply p q).trans hBpq
  have hBpp : B p p - A p p = jacobiTan A p q * A p q := jacobiStep_apply_jj_sub A hA hpq
  have hBqq : B q q - A q q = -(jacobiTan A p q * A p q) := jacobiStep_apply_kk_sub A hA hpq
  -- `c² = 1 / (1 + t²)`
  have hC2 : 2 * A p q ^ 2 / C ^ 2 = 2 * A p q ^ 2 * (1 + jacobiTan A p q ^ 2) := by
    have hpos : 0 < 1 + jacobiTan A p q ^ 2 := by positivity
    have : C ^ 2 = 1 / (1 + jacobiTan A p q ^ 2) := by
      rw [hCdef, jacobiCos, div_pow, one_pow, Real.sq_sqrt hpos.le]
    rw [this]
    field_simp
  -- split every sum over `Fin n` at `p` and `q`
  have hsplit : ∀ h : Fin n → ℝ,
      ∑ j, h j = h p + h q + ∑ j ∈ (Finset.univ.erase p).erase q, h j := fun h => by
    rw [← Finset.add_sum_erase Finset.univ h (Finset.mem_univ p),
      ← Finset.add_sum_erase (Finset.univ.erase p) h
        (Finset.mem_erase.2 ⟨hpq.symm, Finset.mem_univ q⟩)]
    ring
  rw [frobenius_norm_sq_eq_sum_sq]
  simp only [Matrix.sub_apply, Real.norm_eq_abs, sq_abs]
  rw [Finset.sum_congr rfl fun i _ => hsplit (fun j => (B i j - A i j) ^ 2),
    hsplit (fun i => (B i p - A i p) ^ 2 + (B i q - A i q) ^ 2 +
      ∑ j ∈ (Finset.univ.erase p).erase q, (B i j - A i j) ^ 2)]
  have h1 : ∑ i ∈ (Finset.univ.erase p).erase q, ((B i p - A i p) ^ 2 + (B i q - A i q) ^ 2 +
      ∑ j ∈ (Finset.univ.erase p).erase q, (B i j - A i j) ^ 2) =
      (2 - 2 * C) * ∑ i ∈ (Finset.univ.erase p).erase q, (A i p ^ 2 + A i q ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_eq_zero fun j hj => by rw [hBij i j hi hj]; ring, hBip i hi, hBiq i hi]
    linear_combination (A i p ^ 2 + A i q ^ 2) * hcs
  have h2 : ∑ j ∈ (Finset.univ.erase p).erase q, (B p j - A p j) ^ 2 +
      ∑ j ∈ (Finset.univ.erase p).erase q, (B q j - A q j) ^ 2 =
      (2 - 2 * C) * ∑ i ∈ (Finset.univ.erase p).erase q, (A i p ^ 2 + A i q ^ 2) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hBpj j hj, hBqj j hj, hA.apply j p, hA.apply j q]
    linear_combination (A j p ^ 2 + A j q ^ 2) * hcs
  rw [h1, hBpp, hBqq, hBpq, hBqp, hqp, hC2]
  linear_combination h2

end Frobenius

/-! ### §8.5.3 The classical Jacobi algorithm -/

/-- **§8.5.3**: with the rotation of Algorithm 8.5.1 (`t = t_min`), `b_pp = a_pp - t a_pq` and
`b_qq = a_qq + t a_pq` — "this precludes interchanging nearly converged diagonal entries". -/
theorem jacobi_diag_update {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {p q : Fin n}
    (hpq : p ≠ q) :
    jacobiStep A p q p p = A p p - jacobiTanSmall A p q * A p q ∧
      jacobiStep A p q q q = A q q + jacobiTanSmall A p q * A p q := by
  have h1 := jacobiStep_apply_jj_sub A hA hpq
  have h2 := jacobiStep_apply_kk_sub A hA hpq
  rw [jacobiTanSmall_eq_neg_jacobiTan]
  constructor <;> linarith

/-- **§8.5.3, the linear rate of the classical method.** For symmetric `A`, `N = n(n-1)/2` and
`(p, q)` with `|a_pq| = max_{i ≠ j} |a_ij|`: `off(A)² ≤ N (a_pq² + a_qp²)`; after the Jacobi update
`B = J(p,q,θ)ᵀ A J(p,q,θ)` of Algorithm 8.5.1, `off(B)² ≤ (1 - 1/N) off(A)²`; and the classical
iterates satisfy `off(A^{(k)})² ≤ (1 - 1/N)^k off(A^{(0)})²`. -/
theorem classicalJacobi_linear [NeZero n] {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    {p q : Fin n} (hpq : p ≠ q) (hmax : ∀ i j, i ≠ j → |A i j| ≤ |A p q|) :
    off A ^ 2 ≤ ((n : ℝ) * (n - 1) / 2) * (A p q ^ 2 + A q p ^ 2) ∧
      off (jacobiStep A p q) ^ 2 ≤ (1 - 1 / ((n : ℝ) * (n - 1) / 2)) * off A ^ 2 ∧
      ∀ k, off (classicalJacobiIterate A k) ^ 2 ≤
        (1 - 1 / ((n : ℝ) * (n - 1) / 2)) ^ k * off A ^ 2 := by
  have hqp : A q p = A p q := hA.apply p q
  have hN : (1 : ℝ) / ((n : ℝ) * (n - 1) / 2) = 2 / ((Fintype.card (Fin n) : ℝ) ^ 2 -
      Fintype.card (Fin n)) := by
    rw [Fintype.card_fin, one_div_div]
    ring
  have hbound := offDiagNormSq_le_mul_sq A (j := p) (k := q) fun x hx => hmax x.1 x.2 hx
  rw [Fintype.card_fin] at hbound
  have h1 : off A ^ 2 ≤ ((n : ℝ) * (n - 1) / 2) * (A p q ^ 2 + A q p ^ 2) := by
    rw [off_sq, hqp]
    linarith
  refine ⟨h1, ?_, fun k => ?_⟩
  · rw [off_sq, offDiagNormSq_jacobiStep A hA hpq, ← off_sq]
    have hn : (2 : ℝ) ≤ n := by
      have h1 := Fin.val_ne_of_ne hpq
      have h2 := p.isLt
      have h3 := q.isLt
      exact_mod_cast (show 2 ≤ n by omega)
    have hNpos : (0 : ℝ) < (n : ℝ) * (n - 1) / 2 := by nlinarith
    rw [hqp] at h1
    have : 2 * A p q ^ 2 ≥ off A ^ 2 / ((n : ℝ) * (n - 1) / 2) := by
      rw [ge_iff_le, div_le_iff₀ hNpos]
      linarith
    rw [sub_mul, one_mul, div_mul_eq_mul_div, one_mul]
    linarith
  · rw [off_sq, off_sq, hN]
    exact offDiagNormSq_classicalJacobiIterate_le hA k

/-! ### §8.5.6 Block Jacobi procedures -/

/-- The off-diagonal mass of a `2 × 2` block matrix: that of the diagonal blocks plus the full mass
of the off-diagonal blocks. -/
private theorem offDiagNormSq_fromBlocks {κ₁ κ₂ : Type*} [Fintype κ₁] [DecidableEq κ₁]
    [Fintype κ₂] [DecidableEq κ₂] (P : Matrix κ₁ κ₁ ℝ) (Q : Matrix κ₁ κ₂ ℝ) (R : Matrix κ₂ κ₁ ℝ)
    (S : Matrix κ₂ κ₂ ℝ) :
    offDiagNormSq (fromBlocks P Q R S) = offDiagNormSq P + offDiagNormSq S +
      ∑ i, ∑ j, Q i j ^ 2 + ∑ i, ∑ j, R i j ^ 2 := by
  have h := offDiagNormSq_add_sum_diag_sq_real (fromBlocks P Q R S)
  have hP := offDiagNormSq_add_sum_diag_sq_real P
  have hS := offDiagNormSq_add_sum_diag_sq_real S
  simp only [Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
    fromBlocks_apply₂₂, Finset.sum_add_distrib] at h
  linarith

/-- The off-diagonal mass after a rotation acting on a set of coordinates: if `V` is the
orthogonal `W` on the coordinates `e(κ)` and the identity elsewhere, then
`off(VᵀAV)² = off(A)² - off(A_e)² + off(Wᵀ A_e W)²` for the principal block `A_e` on `e(κ)`. -/
private theorem offDiagNormSq_conj_block {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (A : Matrix ι ι ℝ) {e : κ → ι} (he : Function.Injective e)
    {W : Matrix κ κ ℝ} (hW : Wᵀ * W = 1) {V : Matrix ι ι ℝ} (hV : ∀ a b, V (e a) (e b) = W a b)
    (hV' : ∀ i j, (i ∉ Set.range e ∨ j ∉ Set.range e) → V i j = (1 : Matrix ι ι ℝ) i j) :
    offDiagNormSq (Vᵀ * A * V) = offDiagNormSq A - offDiagNormSq (A.submatrix e e) +
      offDiagNormSq (Wᵀ * A.submatrix e e * W) := by
  classical
  let σ : κ ⊕ {i // i ∉ Set.range e} ≃ ι :=
    (Equiv.sumCongr (Equiv.ofInjective e he) (Equiv.refl _)).trans
      (Equiv.sumCompl (· ∈ Set.range e))
  have hσl : ∀ a, σ (Sum.inl a) = e a := fun a => rfl
  have hσr : ∀ b, σ (Sum.inr b) = b.1 := fun b => rfl
  -- reindexing preserves the off-diagonal mass
  have hre : ∀ M : Matrix ι ι ℝ, offDiagNormSq (M.submatrix σ σ) = offDiagNormSq M := fun M => by
    have h1 := offDiagNormSq_add_sum_diag_sq_real (M.submatrix σ σ)
    have h2 := offDiagNormSq_add_sum_diag_sq_real M
    have e1 : ∑ i, (M.submatrix σ σ i i) ^ 2 = ∑ i, M i i ^ 2 :=
      Equiv.sum_comp σ (fun i => M i i ^ 2)
    have e2 : ∑ i, ∑ j, (M.submatrix σ σ i j) ^ 2 = ∑ i, ∑ j, M i j ^ 2 := by
      rw [← Equiv.sum_comp σ (fun i => ∑ j, M i j ^ 2)]
      exact Finset.sum_congr rfl fun i _ => Equiv.sum_comp σ (fun j => M (σ i) j ^ 2)
    linarith
  -- in the reindexed coordinates `V` is `diag(W, I)`
  have hVs : V.submatrix σ σ = fromBlocks W 0 0 1 := by
    ext i j
    rcases i with a | b <;> rcases j with a' | b'
    · exact hV a a'
    · rw [submatrix_apply, hσl, hσr, hV' _ _ (Or.inr b'.2), fromBlocks_apply₁₂, Matrix.zero_apply,
        one_apply_ne]
      intro h
      exact b'.2 ⟨a, h⟩
    · rw [submatrix_apply, hσl, hσr, hV' _ _ (Or.inl b.2), fromBlocks_apply₂₁, Matrix.zero_apply,
        one_apply_ne]
      intro h
      exact b.2 ⟨a', h.symm⟩
    · rw [submatrix_apply, hσr, hσr, hV' _ _ (Or.inl b.2), fromBlocks_apply₂₂]
      by_cases h : b = b'
      · subst h
        simp
      · rw [one_apply_ne (fun h' => h (Subtype.ext h')), one_apply_ne h]
  set U : Matrix (κ ⊕ {i // i ∉ Set.range e}) (κ ⊕ {i // i ∉ Set.range e}) ℝ :=
    fromBlocks W 0 0 1 with hUdef
  have hU : Uᵀ * U = 1 := by
    rw [hUdef, fromBlocks_transpose, fromBlocks_multiply]
    simp [hW, fromBlocks_one]
  have hBs : (Vᵀ * A * V).submatrix σ σ = Uᵀ * A.submatrix σ σ * U := by
    rw [← submatrix_mul_equiv _ _ _ σ _, ← submatrix_mul_equiv _ _ _ σ _, ← transpose_submatrix,
      hVs]
  have hblk : Uᵀ * A.submatrix σ σ * U =
      fromBlocks (Wᵀ * (A.submatrix σ σ).toBlocks₁₁ * W) (Wᵀ * (A.submatrix σ σ).toBlocks₁₂)
        ((A.submatrix σ σ).toBlocks₂₁ * W) (A.submatrix σ σ).toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks (A.submatrix σ σ)]
    simp only [hUdef, fromBlocks_transpose, fromBlocks_multiply, transpose_zero, transpose_one,
      Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.one_mul, Matrix.mul_one]
  have e1 := hre (Vᵀ * A * V)
  rw [hBs] at e1
  have e2 := hre A
  have hT1 := offDiagNormSq_add_sum_diag_sq_real (Uᵀ * A.submatrix σ σ * U)
  have hT2 := offDiagNormSq_add_sum_diag_sq_real (A.submatrix σ σ)
  have hT3 := sum_sq_conj_eq (A.submatrix σ σ) U hU
  have hd1 : ∑ i, (Uᵀ * A.submatrix σ σ * U) i i ^ 2 =
      ∑ a, (Wᵀ * A.submatrix e e * W) a a ^ 2 + ∑ b, (A.submatrix σ σ).toBlocks₂₂ b b ^ 2 := by
    rw [hblk, Fintype.sum_sum_type]
    rfl
  have hd2 : ∑ i, (A.submatrix σ σ) i i ^ 2 =
      ∑ a, (A.submatrix e e) a a ^ 2 + ∑ b, (A.submatrix σ σ).toBlocks₂₂ b b ^ 2 := by
    rw [Fintype.sum_sum_type]
    rfl
  have hW1 := offDiagNormSq_add_sum_diag_sq_real (Wᵀ * A.submatrix e e * W)
  have hW2 := offDiagNormSq_add_sum_diag_sq_real (A.submatrix e e)
  have hW3 := sum_sq_conj_eq (A.submatrix e e) W hW
  linarith

/-- **§8.5.6, the block-Jacobi identity.** Let `A` be symmetric, partitioned into `N × N` blocks
of size `r` (rows and columns indexed by `(block, position) ∈ Fin N × Fin r`, so `A_pq` is
`A.submatrix (Prod.mk p) (Prod.mk q)`), and `p ≠ q`. If the orthogonal `2r × 2r` matrix
`[V_pp V_pq; V_qp V_qq]` diagonalizes the `(p, q)` subproblem,
`[V_pp V_pq; V_qp V_qq]ᵀ [A_pp A_pq; A_qp A_qq] [V_pp V_pq; V_qp V_qq] = diag(D_pp, D_qq)` with
`D_pp`, `D_qq` diagonal, and `V` is the block rotation made up of the `V_ij` (the identity outside
block rows and columns `p`, `q`), then
`off(VᵀAV)² = off(A)² - (2 ‖A_pq‖_F² + off(A_pp)² + off(A_qq)²)` (with `off(·)²` of the whole
matrix the backbone's `Matrix.offDiagNormSq`). -/
theorem blockJacobi_off {N r : ℕ} {A : Matrix (Fin N × Fin r) (Fin N × Fin r) ℝ} (hA : A.IsSymm)
    {p q : Fin N} (hpq : p ≠ q) {Vpp Vpq Vqp Vqq Dpp Dqq : Matrix (Fin r) (Fin r) ℝ}
    (hW : fromBlocks Vpp Vpq Vqp Vqq ∈ orthogonalGroup (Fin r ⊕ Fin r) ℝ)
    (hD : (fromBlocks Vpp Vpq Vqp Vqq)ᵀ *
        fromBlocks (A.submatrix (Prod.mk p) (Prod.mk p)) (A.submatrix (Prod.mk p) (Prod.mk q))
          (A.submatrix (Prod.mk q) (Prod.mk p)) (A.submatrix (Prod.mk q) (Prod.mk q)) *
        fromBlocks Vpp Vpq Vqp Vqq = fromBlocks Dpp 0 0 Dqq)
    (hDpp : Dpp.IsDiag) (hDqq : Dqq.IsDiag) {V : Matrix (Fin N × Fin r) (Fin N × Fin r) ℝ}
    (hV : ∀ i j, V (p, i) (p, j) = Vpp i j ∧ V (p, i) (q, j) = Vpq i j ∧
      V (q, i) (p, j) = Vqp i j ∧ V (q, i) (q, j) = Vqq i j)
    (hV' : ∀ x y : Fin N × Fin r, (x.1 ≠ p ∧ x.1 ≠ q) ∨ (y.1 ≠ p ∧ y.1 ≠ q) →
      V x y = if x = y then 1 else 0) :
    offDiagNormSq (Vᵀ * A * V) = offDiagNormSq A -
      (2 * ∑ i, ∑ j, A (p, i) (q, j) ^ 2 + off (A.submatrix (Prod.mk p) (Prod.mk p)) ^ 2 +
        off (A.submatrix (Prod.mk q) (Prod.mk q)) ^ 2) := by
  set e : Fin r ⊕ Fin r → Fin N × Fin r := Sum.elim (Prod.mk p) (Prod.mk q) with hedef
  have he : Function.Injective e := by
    rintro (a | a) (b | b) h <;>
      simp only [hedef, Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq] at h <;> simp_all
  have hsub : A.submatrix e e = fromBlocks (A.submatrix (Prod.mk p) (Prod.mk p))
      (A.submatrix (Prod.mk p) (Prod.mk q)) (A.submatrix (Prod.mk q) (Prod.mk p))
      (A.submatrix (Prod.mk q) (Prod.mk q)) := by
    ext (a | a) (b | b) <;> rfl
  have hVe : ∀ a b, V (e a) (e b) = fromBlocks Vpp Vpq Vqp Vqq a b := by
    rintro (a | a) (b | b)
    exacts [(hV a b).1, (hV a b).2.1, (hV a b).2.2.1, (hV a b).2.2.2]
  have hrange : ∀ x : Fin N × Fin r, x ∉ Set.range e → x.1 ≠ p ∧ x.1 ≠ q := fun x hx =>
    ⟨fun h => hx ⟨Sum.inl x.2, Prod.ext h.symm rfl⟩, fun h => hx ⟨Sum.inr x.2, Prod.ext h.symm rfl⟩⟩
  have hVe' : ∀ i j, (i ∉ Set.range e ∨ j ∉ Set.range e) →
      V i j = (1 : Matrix (Fin N × Fin r) (Fin N × Fin r) ℝ) i j := fun i j h => by
    rw [hV' i j (h.imp (hrange i) (hrange j)), one_apply]
  have hWW : (fromBlocks Vpp Vpq Vqp Vqq)ᵀ * fromBlocks Vpp Vpq Vqp Vqq = 1 :=
    (mem_orthogonalGroup_iff' _ ℝ).1 hW
  have key := offDiagNormSq_conj_block A he hWW hVe hVe'
  have hD0 : offDiagNormSq (fromBlocks Dpp 0 0 Dqq) = 0 := by
    refine offDiagNormSq_eq_zero_iff.2 ?_
    rintro (a | a) (b | b) h
    · exact hDpp fun h' => h (congrArg Sum.inl h')
    · rfl
    · rfl
    · exact hDqq fun h' => h (congrArg Sum.inr h')
  rw [key, hsub, hD, hD0, add_zero, offDiagNormSq_fromBlocks, off_sq, off_sq]
  have hsym : ∑ i, ∑ j, A.submatrix (Prod.mk q) (Prod.mk p) i j ^ 2 =
      ∑ i, ∑ j, A (p, i) (q, j) ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [submatrix_apply, hA.apply (p, i) (q, j)]
  rw [hsym]
  simp only [submatrix_apply]
  ring

/-! ### §8.5.7 A note on the parallel ordering -/

/-- The seat of player `x ≥ 1` (0-based players, `2m` of them) on the merry-go-round of §8.5.7 at
the start of the tournament. With top row `t₁, …, t_m` and bottom row `b₁, …, b_m` of the `m`
tables, player `0` stays at `t₁` while players `1, …, 2m - 1` circulate along the cycle of seats
`b₁, t₂, …, t_m, b_m, …, b₂` (of length `2m - 1`); in round `0` player `x` sits at table
`⌊x / 2⌋ + 1`, which is seat number `parallelSeat m x` of that cycle. -/
def parallelSeat (m x : ℕ) : ℕ :=
  if x = 1 then 0 else if x % 2 = 0 then x / 2 else (4 * m - 1 - x) / 2

/-- Players `a` and `b` (0-based) sit at the same table in round `k` (0-based) of the §8.5.7
tournament with `2m` players. Seats `i` and `j` of the cycle of length `M = 2m - 1` face each
other iff `M ∣ i + j` (seat `0` faces the fixed player `0`), and in round `k` player `x ≥ 1` sits
at seat `parallelSeat m x + k` modulo `M`. -/
def ParallelPaired (m k a b : ℕ) : Prop :=
  if a = 0 then 2 * m - 1 ∣ parallelSeat m b + k
  else if b = 0 then 2 * m - 1 ∣ parallelSeat m a + k
  else 2 * m - 1 ∣ parallelSeat m a + parallelSeat m b + 2 * k

/-- `ParallelPaired` is decidable. -/
instance (m k a b : ℕ) : Decidable (ParallelPaired m k a b) := by
  unfold ParallelPaired; infer_instance

/-- **§8.5.7, the parallel ordering.** Round `k` (`0 ≤ k < 2m - 1`) of the round-robin ("chess
tournament") schedule for `2m` players, 0-based (the book's player `i + 1` is our `i`): the pairs
`(i, j)`, `i < j`, of players seated at the same table, player `0` staying put and players
`1, …, 2m - 1` moving merry-go-round between rounds as in the book. Round `0` is the book's
`rot.set(1) = {(1, 2), (3, 4), …, (2m - 1, 2m)}`; see `parallelOrdering_four` for all seven
rounds when `m = 4`. -/
def parallelOrdering (m : ℕ) (k : Fin (2 * m - 1)) : Finset (Fin (2 * m) × Fin (2 * m)) :=
  Finset.univ.filter fun ij => ij.1 < ij.2 ∧ ParallelPaired m k ij.1 ij.2

/-- Two residues `a, b < M` with `M ∣ x + a` and `M ∣ x + b` agree. -/
private lemma eq_of_dvd_add {M x a b : ℕ} (ha : a < M) (hb : b < M) (hxa : M ∣ x + a)
    (hxb : M ∣ x + b) : a = b := by
  wlog h : a ≤ b generalizing a b
  · exact (this hb ha hxb hxa (by omega)).symm
  have hd := Nat.dvd_sub hxb hxa
  rw [show x + b - (x + a) = b - a by omega] at hd
  have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
  omega

/-- For odd `M`, `M ∣ 2y` implies `M ∣ y`. -/
private lemma dvd_of_dvd_two_mul {M y : ℕ} (hM : M % 2 = 1) (h : M ∣ 2 * y) : M ∣ y := by
  obtain ⟨e, rfl⟩ : ∃ e, M = 2 * e + 1 := ⟨M / 2, by omega⟩
  have h' : 2 * e + 1 ∣ (2 * e + 1) * y + y := by
    rw [show (2 * e + 1) * y + y = (e + 1) * (2 * y) by ring]
    exact Dvd.dvd.mul_left h _
  exact (Nat.dvd_add_right (dvd_mul_right _ _)).1 h'

/-- For odd `M`, two residues `a, b < M` with `M ∣ x + 2a` and `M ∣ x + 2b` agree. -/
private lemma eq_of_dvd_add_two_mul {M x a b : ℕ} (hM : M % 2 = 1) (ha : a < M) (hb : b < M)
    (hxa : M ∣ x + 2 * a) (hxb : M ∣ x + 2 * b) : a = b := by
  wlog h : a ≤ b generalizing a b
  · exact (this hb ha hxb hxa (by omega)).symm
  have hd := Nat.dvd_sub hxb hxa
  rw [show x + 2 * b - (x + 2 * a) = 2 * (b - a) by omega] at hd
  have := Nat.eq_zero_of_dvd_of_lt (dvd_of_dvd_two_mul hM hd) (by omega)
  omega

/-- Every `x` has a complement `c < M` with `M ∣ x + c`. -/
private lemma exists_dvd_add {M : ℕ} (hM : 0 < M) (x : ℕ) : ∃ c < M, M ∣ x + c := by
  have h := Nat.div_add_mod x M
  have hr := Nat.mod_lt x hM
  by_cases h0 : x % M = 0
  · exact ⟨0, hM, by rw [Nat.add_zero]; exact Nat.dvd_of_mod_eq_zero h0⟩
  · refine ⟨M - x % M, by omega, x / M + 1, ?_⟩
    rw [Nat.mul_add, Nat.mul_one]
    omega

/-- Seats lie on the cycle of length `2m - 1`. -/
private lemma parallelSeat_lt {m x : ℕ} (hx : x < 2 * m) : parallelSeat m x < 2 * m - 1 := by
  unfold parallelSeat; split_ifs <;> omega

/-- Players `1, …, 2m - 1` occupy distinct seats. -/
private lemma parallelSeat_inj {m x y : ℕ} (hx0 : x ≠ 0) (hx : x < 2 * m) (hy0 : y ≠ 0)
    (hy : y < 2 * m) (h : parallelSeat m x = parallelSeat m y) : x = y := by
  unfold parallelSeat at h; split_ifs at h <;> omega

/-- Every seat of the cycle is occupied by one of the players `1, …, 2m - 1`. -/
private lemma exists_parallelSeat_eq {m c : ℕ} (hc : c < 2 * m - 1) :
    ∃ x, x ≠ 0 ∧ x < 2 * m ∧ parallelSeat m x = c := by
  by_cases h0 : c = 0
  · exact ⟨1, by omega, by omega, by simp [parallelSeat, h0]⟩
  by_cases h1 : c < m
  · refine ⟨2 * c, by omega, by omega, ?_⟩
    unfold parallelSeat; split_ifs <;> omega
  · refine ⟨4 * m - 1 - 2 * c, by omega, by omega, ?_⟩
    unfold parallelSeat; split_ifs <;> omega

/-- Sitting at the same table is a symmetric relation. -/
private lemma parallelPaired_comm {m k a b : ℕ} :
    ParallelPaired m k a b ↔ ParallelPaired m k b a := by
  unfold ParallelPaired
  by_cases ha : a = 0 <;> by_cases hb : b = 0
  · simp [ha, hb]
  · simp [ha, hb]
  · simp [ha, hb]
  · simp only [ha, hb, ↓reduceIte]
    rw [Nat.add_comm (parallelSeat m a)]

/-- In each round every player has at most one opponent. -/
private lemma parallelPaired_unique {m k a b b' : ℕ} (ha : a < 2 * m)
    (hb : b < 2 * m) (hb' : b' < 2 * m) (hab : a ≠ b) (hab' : a ≠ b')
    (h : ParallelPaired m k a b) (h' : ParallelPaired m k a b') : b = b' := by
  unfold ParallelPaired at h h'
  have hsa := parallelSeat_lt ha
  have hsb := parallelSeat_lt hb
  have hsb' := parallelSeat_lt hb'
  by_cases ha0 : a = 0
  · rw [ite_eq_left ha0] at h h'
    refine parallelSeat_inj (by omega) hb (by omega) hb' (eq_of_dvd_add (x := k) hsb hsb' ?_ ?_)
    · rw [Nat.add_comm]; exact h
    · rw [Nat.add_comm]; exact h'
  rw [ite_eq_right ha0] at h h'
  by_cases hb0 : b = 0 <;> by_cases hb0' : b' = 0
  · rw [hb0, hb0']
  · rw [ite_eq_left hb0] at h
    rw [ite_eq_right hb0'] at h'
    have h2 : 2 * m - 1 ∣ parallelSeat m a + k + (parallelSeat m b' + k) := by
      rw [show parallelSeat m a + k + (parallelSeat m b' + k) =
        parallelSeat m a + parallelSeat m b' + 2 * k by ring]
      exact h'
    have h3 := (Nat.dvd_add_right h).1 h2
    have := parallelSeat_inj ha0 ha hb0' hb' (eq_of_dvd_add hsa hsb' (by rwa [Nat.add_comm])
      (by rwa [Nat.add_comm]))
    exact absurd this hab'
  · rw [ite_eq_right hb0] at h
    rw [ite_eq_left hb0'] at h'
    have h2 : 2 * m - 1 ∣ parallelSeat m a + k + (parallelSeat m b + k) := by
      rw [show parallelSeat m a + k + (parallelSeat m b + k) =
        parallelSeat m a + parallelSeat m b + 2 * k by ring]
      exact h
    have h3 := (Nat.dvd_add_right h').1 h2
    have := parallelSeat_inj ha0 ha hb0 hb (eq_of_dvd_add hsa hsb (by rwa [Nat.add_comm])
      (by rwa [Nat.add_comm]))
    exact absurd this hab
  · rw [ite_eq_right hb0] at h
    rw [ite_eq_right hb0'] at h'
    refine parallelSeat_inj hb0 hb hb0' hb'
      (eq_of_dvd_add (x := parallelSeat m a + 2 * k) hsb hsb' ?_ ?_)
    · rwa [Nat.add_right_comm] at h
    · rwa [Nat.add_right_comm] at h'

/-- In each round every player has an opponent. -/
private lemma exists_parallelPaired {m k a : ℕ} (hk : k < 2 * m - 1) (ha : a < 2 * m) :
    ∃ b < 2 * m, a ≠ b ∧ ParallelPaired m k a b := by
  have hM : 0 < 2 * m - 1 := by omega
  unfold ParallelPaired
  by_cases ha0 : a = 0
  · obtain ⟨c, hc, hdvd⟩ := exists_dvd_add hM k
    obtain ⟨b, hb0, hb, rfl⟩ := exists_parallelSeat_eq hc
    refine ⟨b, hb, by omega, ?_⟩
    rw [ite_eq_left ha0, Nat.add_comm]
    exact hdvd
  · by_cases hak : 2 * m - 1 ∣ parallelSeat m a + k
    · exact ⟨0, by omega, ha0, by rw [ite_eq_right ha0, ite_eq_left rfl]; exact hak⟩
    · obtain ⟨c, hc, hdvd⟩ := exists_dvd_add hM (parallelSeat m a + 2 * k)
      obtain ⟨b, hb0, hb, rfl⟩ := exists_parallelSeat_eq hc
      refine ⟨b, hb, fun hab => hak ?_, ?_⟩
      · rw [← hab] at hdvd
        refine dvd_of_dvd_two_mul (by omega) ?_
        rw [show 2 * (parallelSeat m a + k) =
          parallelSeat m a + 2 * k + parallelSeat m a by ring]
        exact hdvd
      · rw [ite_eq_right ha0, ite_eq_right hb0, Nat.add_right_comm]
        exact hdvd

/-- Every pair `i < j` of players meets in exactly one round. -/
private lemma existsUnique_parallelPaired {m i j : ℕ} (hij : i < j) (hj : j < 2 * m) :
    ∃! k, k < 2 * m - 1 ∧ ParallelPaired m k i j := by
  have hM : 0 < 2 * m - 1 := by omega
  have hj0 : j ≠ 0 := by omega
  have hsi := parallelSeat_lt (m := m) (x := i) (by omega)
  have hsj := parallelSeat_lt hj
  unfold ParallelPaired
  by_cases hi0 : i = 0
  · simp only [ite_eq_left hi0]
    obtain ⟨k, hk, hdvd⟩ := exists_dvd_add hM (parallelSeat m j)
    exact ⟨k, ⟨hk, hdvd⟩, fun k' hk' => eq_of_dvd_add hk'.1 hk hk'.2 hdvd⟩
  · simp only [ite_eq_right hi0, ite_eq_right hj0]
    obtain ⟨k, hk, t, ht⟩ : ∃ k < 2 * m - 1, ∃ t,
        parallelSeat m i + parallelSeat m j + 2 * k = (2 * m - 1) * t := by
      by_cases hev : (parallelSeat m i + parallelSeat m j) % 2 = 0
      · by_cases h0 : parallelSeat m i + parallelSeat m j = 0
        · exact ⟨0, hM, 0, by omega⟩
        · exact ⟨2 * m - 1 - (parallelSeat m i + parallelSeat m j) / 2, by omega, 2, by omega⟩
      · by_cases hle : parallelSeat m i + parallelSeat m j ≤ 2 * m - 1
        · exact ⟨(2 * m - 1 - (parallelSeat m i + parallelSeat m j)) / 2, by omega, 1, by omega⟩
        · exact ⟨(3 * (2 * m - 1) - (parallelSeat m i + parallelSeat m j)) / 2, by omega, 3,
            by omega⟩
    exact ⟨k, ⟨hk, t, ht⟩, fun k' hk' =>
      eq_of_dvd_add_two_mul (by omega) hk'.1 hk hk'.2 ⟨t, ht⟩⟩

/-- **§8.5.7, the parallel ordering is a one-factorization of `K_{2m}`.** Each rotation set
`parallelOrdering m k` consists of pairs `i < j`; two distinct pairs of one rotation set share no
index (nonconflicting subproblems); each rotation set has exactly `m` pairs; and every pair
`i < j` of the `2m` indices lies in exactly one of the `2m - 1` rotation sets, so these partition
the `m(2m - 1)` off-diagonal index pairs. -/
theorem parallelOrdering_spec (m : ℕ) :
    (∀ k, ∀ ij ∈ parallelOrdering m k, ij.1 < ij.2) ∧
    (∀ k, ∀ ij ∈ parallelOrdering m k, ∀ ij' ∈ parallelOrdering m k, ij ≠ ij' →
      ij.1 ≠ ij'.1 ∧ ij.1 ≠ ij'.2 ∧ ij.2 ≠ ij'.1 ∧ ij.2 ≠ ij'.2) ∧
    (∀ k, (parallelOrdering m k).card = m) ∧
    ∀ i j : Fin (2 * m), i < j → ∃! k, (i, j) ∈ parallelOrdering m k := by
  have hmem : ∀ k ij, ij ∈ parallelOrdering m k ↔ ij.1 < ij.2 ∧ ParallelPaired m k ij.1 ij.2 :=
    fun k ij => by simp only [parallelOrdering, Finset.mem_filter, Finset.mem_univ, true_and]
  have hlt : ∀ k, ∀ ij ∈ parallelOrdering m k, ij.1 < ij.2 := fun k ij h => ((hmem k ij).1 h).1
  have hP : ∀ k, ∀ ij ∈ parallelOrdering m k,
      ParallelPaired m k ij.1 ij.2 ∧ ParallelPaired m k ij.2 ij.1 := fun k ij h =>
    ⟨((hmem k ij).1 h).2, parallelPaired_comm.1 ((hmem k ij).1 h).2⟩
  have key : ∀ (k : Fin (2 * m - 1)) (a b b' : Fin (2 * m)), a ≠ b → a ≠ b' →
      ParallelPaired m k a b → ParallelPaired m k a b' → b = b' := fun k a b b' h1 h2 h3 h4 =>
    Fin.ext (parallelPaired_unique a.2 b.2 b'.2 (fun h => h1 (Fin.ext h))
      (fun h => h2 (Fin.ext h)) h3 h4)
  have hdisj : ∀ k, ∀ ij ∈ parallelOrdering m k, ∀ ij' ∈ parallelOrdering m k, ij ≠ ij' →
      ij.1 ≠ ij'.1 ∧ ij.1 ≠ ij'.2 ∧ ij.2 ≠ ij'.1 ∧ ij.2 ≠ ij'.2 := by
    intro k ij h ij' h' hne
    obtain ⟨p1, p2⟩ := hP k ij h
    obtain ⟨q1, q2⟩ := hP k ij' h'
    have l := hlt k ij h
    have l' := hlt k ij' h'
    refine ⟨fun e => hne ?_, fun e => ?_, fun e => ?_, fun e => hne ?_⟩
    · rw [← e] at q1 l'
      exact Prod.ext e (key k ij.1 _ _ l.ne l'.ne p1 q1)
    · rw [← e] at q2 l'
      have e' := key k ij.1 _ _ l.ne l'.ne' p1 q2
      rw [← e'] at l'
      exact absurd l (lt_asymm l')
    · rw [← e] at q1 l'
      have e' := key k ij.2 _ _ l.ne' l'.ne p2 q1
      rw [← e'] at l'
      exact absurd l (lt_asymm l')
    · rw [← e] at q2 l'
      exact Prod.ext (key k ij.2 _ _ l.ne' l'.ne' p2 q2) e
  refine ⟨hlt, hdisj, fun k => ?_, fun i j hij => ?_⟩
  · -- a rotation set times `Bool` is in bijection with the players
    have hinj : ∀ x ∈ parallelOrdering m k ×ˢ (Finset.univ : Finset Bool),
        ∀ y ∈ parallelOrdering m k ×ˢ (Finset.univ : Finset Bool),
        (bif x.2 then x.1.1 else x.1.2) = (bif y.2 then y.1.1 else y.1.2) → x = y := by
      rintro ⟨ij, b⟩ hx ⟨ij', b'⟩ hy he
      rw [Finset.mem_product] at hx hy
      have hd := hdisj k ij hx.1 ij' hy.1
      cases b <;> cases b' <;> simp only [Bool.cond_true, Bool.cond_false] at he
      · rw [Classical.byContradiction fun hne => (hd hne).2.2.2 he]
      · have e : ij = ij' := Classical.byContradiction fun hne => (hd hne).2.2.1 he
        subst e
        exact absurd he (hlt k ij hx.1).ne'
      · have e : ij = ij' := Classical.byContradiction fun hne => (hd hne).2.1 he
        subst e
        exact absurd he (hlt k ij hx.1).ne
      · rw [Classical.byContradiction fun hne => (hd hne).1 he]
    have hsurj : ∀ a ∈ (Finset.univ : Finset (Fin (2 * m))),
        ∃ x, ∃ (_ : x ∈ parallelOrdering m k ×ˢ (Finset.univ : Finset Bool)),
          (bif x.2 then x.1.1 else x.1.2) = a := by
      intro a _
      obtain ⟨b, hb, hab, hp⟩ := exists_parallelPaired k.2 a.2
      rcases lt_or_gt_of_ne hab with h | h
      · exact ⟨((a, ⟨b, hb⟩), true),
          Finset.mem_product.2 ⟨(hmem _ _).2 ⟨Fin.lt_def.2 h, hp⟩,
            Finset.mem_univ _⟩, rfl⟩
      · exact ⟨((⟨b, hb⟩, a), false),
          Finset.mem_product.2 ⟨(hmem _ _).2 ⟨Fin.lt_def.2 h,
            parallelPaired_comm.1 hp⟩, Finset.mem_univ _⟩, rfl⟩
    have h := Finset.card_bij
      (fun (x : (Fin (2 * m) × Fin (2 * m)) × Bool) _ => bif x.2 then x.1.1 else x.1.2)
      (fun _ _ => Finset.mem_univ _) hinj hsurj
    simp only [Finset.card_product, Finset.card_univ, Fintype.card_bool, Fintype.card_fin] at h
    omega
  · obtain ⟨k, ⟨hk, hkP⟩, hku⟩ := existsUnique_parallelPaired (m := m)
      (Fin.lt_def.1 hij) j.2
    exact ⟨⟨k, hk⟩, (hmem _ _).2 ⟨hij, hkP⟩,
      fun k' hk' => Fin.ext (hku k' ⟨k'.2, ((hmem _ _).1 hk').2⟩)⟩

/-- **§8.5.7, `m = 4`.** The seven rounds of `parallelOrdering 4` are the book's rotation sets
`rot.set(1), …, rot.set(7)` (with 0-based players). -/
theorem parallelOrdering_four :
    parallelOrdering 4 ⟨0, by decide⟩ = {(0, 1), (2, 3), (4, 5), (6, 7)} ∧
    parallelOrdering 4 ⟨1, by decide⟩ = {(0, 3), (1, 5), (2, 7), (4, 6)} ∧
    parallelOrdering 4 ⟨2, by decide⟩ = {(0, 5), (3, 7), (1, 6), (2, 4)} ∧
    parallelOrdering 4 ⟨3, by decide⟩ = {(0, 7), (5, 6), (3, 4), (1, 2)} ∧
    parallelOrdering 4 ⟨4, by decide⟩ = {(0, 6), (4, 7), (2, 5), (1, 3)} ∧
    parallelOrdering 4 ⟨5, by decide⟩ = {(0, 4), (2, 6), (1, 7), (3, 5)} ∧
    parallelOrdering 4 ⟨6, by decide⟩ = {(0, 2), (1, 4), (3, 6), (5, 7)} := by
  decide

end GolubVanLoan.Chapter08

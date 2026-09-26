import NumlibSurface.GolubVanLoan.Chapter03.Section02

/-!
# Golub–Van Loan §3.3: roundoff error in Gaussian elimination

Surface file for Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th edition, §3.3:
Theorem 3.3.1 (the computed LU factors) and Theorem 3.3.2 (factor, then the two triangular solves),
both about the runs of the programs of §3.1–3.2 in the relational rounding model
`FloatingPoint.RoundingModel ℝ`.

## Design

The book's first-order bounds `2(n-1)u(|A| + |L̂||Û|) + O(u²)` and `nu(2|A| + 4|L̂||Û|) + O(u²)` are
stated in their rigorous `γ` forms ([higham2002accuracy] Theorems 9.3–9.4), `|H| ≤ γ_n |L̂||Û|` and
`|E| ≤ γ_{3n} |L̂||Û|` entrywise, which are sharper to first order (`γ_n = nu + O(u²)`, and no `|A|`
term) and imply the printed forms. Each theorem is a bridge of §3.1–3.2 followed by the backbone
theorem about the relation (`FloatingPoint.exists_roundsLU_mul_eq_add`,
`FloatingPoint.exists_roundsLU_solveDot_eq`, `FloatingPoint.exists_roundsLU_solve_eq`). The
hypotheses are about the returned packed factors only (convention 9), and the composite of factoring
and solving is stated nested, one program per quantifier.

The book's hypothesis "`A` is an `n`-by-`n` matrix of floating point numbers" has no counterpart in
the relational model (inputs are arbitrary reals) and is dropped. The proof-internal displays
(3.3.3)–(3.3.13) are not formalized: the backbone proves Higham's Theorem 9.3 entrywise.
-/

open FloatingPoint Matrix

namespace GolubVanLoan.Chapter03

variable {fp : RoundingModel ℝ} {n : ℕ}

/-- **Theorem 3.3.1**, rigorous form: "assume that `A` is an `n`-by-`n` matrix … If no zero pivots
are encountered during the execution of Algorithm 3.2.1, then the computed triangular matrices
`L̂` and `Û` satisfy `L̂ Û = A + H`", with `|H| ≤ γ_n |L̂| |Û|` entrywise — the book's
`|H| ≤ 2(n-1)u(|A| + |L̂||Û|) + O(u²)` to first order. Only the pivots that are divisors are
needed nonzero. -/
theorem theorem_3_3_1 (hu : fp.u < 1) (hn : (n : ℝ) * fp.u < 1) (A : Matrix (Fin n) (Fin n) ℝ) :
    ∀ F ∈ (algorithm_3_2_1 fp.round A).run, (∀ j : Fin n, (j : ℕ) + 1 < n → F j j ≠ 0) →
      ∃ H : Matrix (Fin n) (Fin n) ℝ, packedL F * packedU F = A + H ∧
        H.abs ≤ₑ gamma fp.u n • ((packedL F).abs * (packedU F).abs) := by
  intro F hF hpiv
  obtain ⟨H, hH, hLU⟩ := exists_roundsLU_mul_eq_add hu (by simpa using hn)
    (algorithm_3_2_1_rounds A F hF) fun j i hji => by
      rw [packedU_apply_of_le F le_rfl]
      exact hpiv j (by have := Fin.lt_def.1 hji; omega)
  exact ⟨H, hLU, by simpa using hH⟩

/-- §3.3.1, "the error bounds that we derive also apply to the gaxpy formulation (Algorithm
3.2.2)": Theorem 3.3.1 for the runs `(L̂, Û)` of Algorithm 3.2.2 whose divisor pivots `û_jj`,
`j + 1 < n`, are nonzero: `L̂ Û = A + H` with `|H| ≤ γ_n |L̂| |Û|`. -/
theorem theorem_3_3_1_gaxpy (hu : fp.u < 1) (hn : (n : ℝ) * fp.u < 1)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    ∀ out ∈ (algorithm_3_2_2 fp.round A).run, (∀ j : Fin n, (j : ℕ) + 1 < n → out.2 j j ≠ 0) →
      ∃ H : Matrix (Fin n) (Fin n) ℝ, out.1 * out.2 = A + H ∧
        H.abs ≤ₑ gamma fp.u n • (out.1.abs * out.2.abs) := by
  intro out hout hpiv
  obtain ⟨H, hH, hLU⟩ := exists_roundsLU_mul_eq_add hu (by simpa using hn)
    (algorithm_3_2_2_rounds A out hout) fun j i hji =>
      hpiv j (by have := Fin.lt_def.1 hji; omega)
  exact ⟨H, hLU, by simpa using hH⟩

/-- **Theorem 3.3.2**, rigorous form: "let `L̂` and `Û` be the computed LU factors of the `n`-by-`n`
floating point matrix `A` obtained by Algorithm 3.2.1. Suppose the methods of §3.1 are used to
produce the computed solution `ŷ` to `L̂ y = b` and the computed solution `x̂` to `Û x = ŷ`. Then
`(A + E) x̂ = b`" with `|E| ≤ γ_{3n} |L̂| |Û|` entrywise (the row-oriented solves, Algorithms
3.1.1–3.1.2) — the book's `|E| ≤ nu(2|A| + 4|L̂||Û|) + O(u²)` to first order. -/
theorem theorem_3_3_2 (hu : fp.u < 1) (hn : ((3 * n : ℕ) : ℝ) * fp.u < 1)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    ∀ F ∈ (algorithm_3_2_1 fp.round A).run, (∀ j, F j j ≠ 0) →
      ∀ y ∈ (algorithm_3_1_1 fp.round (packedL F) b).run,
      ∀ x ∈ (algorithm_3_1_2 fp.round (packedU F) y).run,
        ∃ E : Matrix (Fin n) (Fin n) ℝ, (A + E) *ᵥ x = b ∧
          E.abs ≤ₑ gamma fp.u (3 * n) • ((packedL F).abs * (packedU F).abs) := by
  intro F hF hpiv y hy x hx
  obtain ⟨E, hE, hAx⟩ := exists_roundsLU_solveDot_eq hu (by simpa using hn)
    (algorithm_3_2_1_rounds A F hF) (fun j => by rw [packedU_apply_of_le F le_rfl]; exact hpiv j)
    (algorithm_3_1_1_rounds fp _ b y hy) (algorithm_3_1_2_rounds fp _ y x hx)
  exact ⟨E, hAx, by simpa using hE⟩

/-- Theorem 3.3.2 with the column-oriented solves of §3.1.3 ("the methods of §3.1" covers both):
`ŷ` from Algorithm 3.1.3 and `x̂` from Algorithm 3.1.4 give the same backward error
`|E| ≤ γ_{3n} |L̂| |Û|` ([higham2002accuracy] Theorem 9.4). -/
theorem theorem_3_3_2_column (hu : fp.u < 1) (hn : ((3 * n : ℕ) : ℝ) * fp.u < 1)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    ∀ F ∈ (algorithm_3_2_1 fp.round A).run, (∀ j, F j j ≠ 0) →
      ∀ y ∈ (algorithm_3_1_3 fp.round (packedL F) b).run,
      ∀ x ∈ (algorithm_3_1_4 fp.round (packedU F) y).run,
        ∃ E : Matrix (Fin n) (Fin n) ℝ, (A + E) *ᵥ x = b ∧
          E.abs ≤ₑ gamma fp.u (3 * n) • ((packedL F).abs * (packedU F).abs) := by
  intro F hF hpiv y hy x hx
  obtain ⟨E, hE, hAx⟩ := exists_roundsLU_solve_eq hu (by simpa using hn)
    (algorithm_3_2_1_rounds A F hF) (fun j => by rw [packedU_apply_of_le F le_rfl]; exact hpiv j)
    (algorithm_3_1_3_rounds fp _ b y hy) (algorithm_3_1_4_rounds fp _ y x hx)
  exact ⟨E, hAx, by simpa using hE⟩

end GolubVanLoan.Chapter03

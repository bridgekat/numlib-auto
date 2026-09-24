import Numlib.Eigen.Jacobi
import Numlib.Eigen.Sturm
import NumlibSurface.QuarteroniSaccoSaleri.Chapter05.Section09

/-!
# Quarteroni–Sacco–Saleri §5.10: methods for eigenvalues of symmetric matrices

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §5.10, over the backbone `Numlib/Eigen/Jacobi` (the Jacobi rotation,
the off-diagonal mass and its decrease, the classical method), `Numlib/LinearAlgebra/Matrix/
PlaneRotation` (the entries of a matrix conjugated by a plane rotation) and `Numlib/Eigen/Sturm`
(Sturm sequences, strict interlacing, the sign-change count and Givens' bisection).

## Conventions

The book's Givens matrix `G(p, q, θ)` of (5.43) has `+sin θ` in position `(p, q)`; the backbone's
`Matrix.planeRotation p q c s` has `−s` there, so the book's `G_pq` with `c = cos θ`, `s = sin θ`
is `planeRotation p q c (−s)`. The rotation angle of (5.61)–(5.62) is the root `t` of
`t² + 2ηt − 1 = 0` of smaller modulus, `jacobiTanBook`, which is the backbone's
`Matrix.jacobiTanSmall`; the book's `(c, s)` is `equation_5_61`, and the matrix
`A^(k) = G_pqᵀ A^(k−1) G_pq` built from it is `jacobiRotate`, which is the backbone's
`Matrix.jacobiStep` (`jacobiRotate_eq_jacobiStep`). The off-diagonal mass `Ψ(M)` of (5.63) is
`equation_5_63`, the square root of the backbone's `Matrix.offDiagNormSq`. The tridiagonal matrix
`T = tridiag(b, d, b)` of §5.10.2 is `Matrix.symmTridiagonalOf d b n`, built from `ℕ`-indexed
diagonals (`d i` is the book's `d_{i+1}`, `b i` its `b_{i+1}`) so that its leading principal
minor `T_i` is the same construction at order `i`; the Sturm sequence (5.65) is `sturmSeq d b`,
which is the backbone's `Sturm.seq`; the sorted eigenvalues `λ_1(T_i) ≥ … ≥ λ_i(T_i)` are
`Sturm.eigenvalues d b i : Fin i → ℝ` (Mathlib's `Matrix.IsHermitian.eigenvalues₀` reindexed), and
`s(μ)` with the book's sign convention is `Sturm.signChanges d b n μ`.

## Contents

* `equation_5_60`, `jacobiTanBook`, `equation_5_61`, `equation_5_61_eq`, `equation_5_61_root`,
  `jacobiRotate`, `jacobiRotate_eq_jacobiStep`, `equation_5_59` — the Jacobi rotation.
* `equation_5_63`, `equation_5_63_eq`, `equation_5_64` — the off-diagonal mass and its decrease.
* `classicalJacobi`, `cyclicPairs`, `cyclicJacobiSweep`, `cyclicJacobiIterate`,
  `cyclicJacobiSweep_spec` — the classical and the row-cyclic method.
* `sturmSeq`, `sturmSeq_eq`, `equation_5_65`, `property_5_11_interlace`, `property_5_11_count` —
  Sturm sequences.
* `givensBisection`, `givensBisection_spec`, `givensBisection_error` — Givens' method.

## Readings and errata

Property 5.11's count is read with `≤ μ`: with the stated convention (a vanishing `p_i(μ)` takes
the sign opposite to `p_{i−1}(μ)`), `s(μ)` counts the eigenvalues at most `μ`, not "strictly less
than `μ`" (for `n = 1`, `μ = d_1`, the sequence `1, 0` has one sign change and no eigenvalue below
`μ`); the two agree off the spectrum. A consequence for Givens' method started from the
Gershgorin interval `[α, β]`: when `α` is itself the smallest eigenvalue the bracket `(a_r, b_r]`
degenerates to `a_r = α` for every `r`, so the eigenvalue is enclosed by the *closed* interval
`[a_r, b_r]`, which is what `givensBisection_error` states and what the error bound needs. The
quadratic convergence of the cyclic Jacobi method (Wilkinson) is not formalized; the record is
below. Examples 5.15–5.17 are numerical.

## Not formalized here

* **§5.10.1, Wilkinson's quadratic convergence of the cyclic Jacobi method.** The claim, stated
  by the book without proof and attributed to [Wil62], [Wil65]: if the eigenvalues of the
  symmetric `A` are separated, `|λ_i − λ_j| ≥ δ` for `i ≠ j`, then one full sweep of `N = n(n−1)/2`
  row-cyclic rotations squares the off-diagonal mass,
  `Ψ(A^{(k+N)}) ≤ Ψ(A^{(k)})² / (δ √2)`, with `Ψ` the Frobenius norm of the off-diagonal part
  (5.63). Two findings from examining it are worth keeping.

  (a) **The inequality needs no smallness hypothesis, and that is not a simplification but the
  location of the content.** `Ψ` is non-increasing along any sequence of Jacobi rotations
  (`equation_5_64` here, the backbone's `Matrix.offDiagNormSq_conj_planeRotation_of_apply_eq_zero`:
  one rotation removes `2 a_pq²` from `Ψ²`), so whenever `Ψ(A^{(k)}) ≥ δ √2` the right-hand side
  `Ψ(A^{(k)})²/(δ √2)` already exceeds `Ψ(A^{(k)})` and the inequality is free. All of the content
  is the regime `Ψ < δ √2`, and a proof that starts by assuming smallness has assumed the theorem's
  hypothesis-free form away.

  (b) **That regime is an induction over the sweep, not an estimate on one rotation.** Each
  rotation angle is `O(Ψ/δ)` by Gershgorin — the diagonal entries are within `Ψ` of the
  eigenvalues — and a pair annihilated earlier in the sweep is refilled only to second order; so
  the argument is an induction over the `n(n−1)/2` rotations of a sweep carrying a second-order
  bound on *every* off-diagonal entry, and the sharp constant `1/(δ √2)` is obtained by Wilkinson
  only with the ordering of the sweep taken into account. The library has no counterpart: a
  sweep-indexed invariant of this kind does not exist anywhere in `Numlib/`.

  What exists here and in `Numlib/Eigen/Jacobi`: the sweep and the iteration themselves
  (`cyclicPairs`, `cyclicJacobiSweep`, `cyclicJacobiIterate`, `cyclicJacobiSweep_spec`), the
  off-diagonal mass `equation_5_63` with `equation_5_63_eq` and the one-rotation decrease
  `equation_5_64` (the book's (5.64)), and the convergence of the *classical* method,
  `Matrix.tendsto_classicalJacobiIterate`. Nothing near a diagonal matrix, and nothing about a
  whole sweep. Estimate: comfortably over a thousand lines, most of it the sweep-indexed
  invariant. Nothing downstream depends on it.
-/

open Filter Finset Matrix Polynomial Topology

namespace QuarteroniSaccoSaleri.Chapter05

variable {n : ℕ}

/-! ### §5.10.1: the Jacobi rotation -/

/-- **(5.60).** With `c = cos θ`, `s = sin θ` and `G_pq = G(p, q, θ)` the Givens matrix of (5.43)
(`+s` in position `(p, q)`, so `planeRotation p q c (−s)`), the entries of
`A^(k) = G_pqᵀ A^(k−1) G_pq` that change are those in rows and columns `p`, `q`, and the `2 × 2`
block at `(p, p), (p, q), (q, q)` is
`[[c, s], [−s, c]]ᵀ [[a_pp, a_pq], [a_pq, a_qq]] [[c, s], [−s, c]]`. Backbone
`Matrix.conj_planeRotation_apply_jj/_jk/_kk/_of_ne`. -/
theorem equation_5_60 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {p q : Fin n} (hpq : p ≠ q)
    (c s : ℝ) :
    let G := planeRotation p q c (-s)
    let M := !![c, s; -s, c]ᵀ * !![A p p, A p q; A p q, A q q] * !![c, s; -s, c]
    (Gᵀ * A * G) p p = M 0 0 ∧ (Gᵀ * A * G) p q = M 0 1 ∧ (Gᵀ * A * G) q q = M 1 1 ∧
      ∀ i j, i ≠ p → i ≠ q → j ≠ p → j ≠ q → (Gᵀ * A * G) i j = A i j := by
  intro G M
  have hqp : A q p = A p q := hA.apply p q
  refine ⟨?_, ?_, ?_, fun i j hip hiq hjp hjq =>
    conj_planeRotation_apply_of_ne hpq A hip hiq hjp hjq⟩
  · rw [conj_planeRotation_apply_jj hpq A, hqp]
    simp [M, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · rw [conj_planeRotation_apply_jk hpq A, hqp]
    simp [M, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · rw [conj_planeRotation_apply_kk hpq A, hqp]
    simp [M, Matrix.mul_apply, Fin.sum_univ_two]
    ring

/-- **(5.61), the rotation angle.** For `a_pq ≠ 0` and `η = (a_qq − a_pp)/(2 a_pq)`, the root of
`t² + 2ηt − 1 = 0` chosen by the book: `t = 1/(η + √(1 + η²))` if `η ≥ 0`, `t = −1/(−η + √(1 + η²))`
otherwise; for `a_pq = 0` the rotation is the identity, `t = 0` (Program 39). It is the backbone's
`Matrix.jacobiTanSmall`, the root of smaller modulus. -/
noncomputable def jacobiTanBook (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) : ℝ :=
  if A p q = 0 then 0
  else
    let η := (A q q - A p p) / (2 * A p q)
    if 0 ≤ η then 1 / (η + Real.sqrt (1 + η ^ 2)) else -1 / (-η + Real.sqrt (1 + η ^ 2))

/-- **(5.62), the book's `(c, s)`.** `c = 1/√(1 + t²)`, `s = c t`, and `(c, s) = (1, 0)` when
`a_pq = 0` (Program 39, `symschur`). -/
noncomputable def equation_5_61 (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) : ℝ × ℝ :=
  if A p q = 0 then (1, 0)
  else (1 / Real.sqrt (1 + jacobiTanBook A p q ^ 2),
    1 / Real.sqrt (1 + jacobiTanBook A p q ^ 2) * jacobiTanBook A p q)

/-- The book's `t` is the backbone's `Matrix.jacobiTanSmall`. -/
theorem jacobiTanBook_eq (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) :
    jacobiTanBook A p q = jacobiTanSmall A p q := rfl

/-- The book's `(c, s)` are the backbone's `Matrix.jacobiCosSmall`, `Matrix.jacobiSinSmall`. -/
theorem equation_5_61_eq (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) :
    equation_5_61 A p q = (jacobiCosSmall A p q, jacobiSinSmall A p q) := by
  simp only [equation_5_61, jacobiSinSmall, jacobiCosSmall, jacobiTanBook_eq]
  split_ifs with h
  · simp [jacobiTanSmall, h]
  · rw [mul_comm]

/-- **(5.61)–(5.62), the properties of the angle.** For `a_pq ≠ 0` the book's `t` solves
`t² + 2ηt − 1 = 0`; it has `|t| ≤ 1` (the rotation angle is at most `π/4`); and `c² + s² = 1`.
Backbone `Matrix.jacobiTanSmall_sq`, `Matrix.abs_jacobiTanSmall_le_one`,
`Matrix.jacobiCosSmall_sq_add_jacobiSinSmall_sq`. -/
theorem equation_5_61_root (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) :
    (A p q ≠ 0 → jacobiTanBook A p q ^ 2 + 2 * ((A q q - A p p) / (2 * A p q)) * jacobiTanBook A p q
      - 1 = 0) ∧
      |jacobiTanBook A p q| ≤ 1 ∧
      (equation_5_61 A p q).1 ^ 2 + (equation_5_61 A p q).2 ^ 2 = 1 := by
  rw [jacobiTanBook_eq, equation_5_61_eq]
  exact ⟨jacobiTanSmall_sq A p q, abs_jacobiTanSmall_le_one A p q,
    jacobiCosSmall_sq_add_jacobiSinSmall_sq A p q⟩

/-- **The Jacobi transformation** `A^(k) = G_pqᵀ A^(k−1) G_pq` of §5.10.1, with `G_pq` the Givens
matrix built from the `(c, s)` of (5.61)–(5.62). -/
noncomputable def jacobiRotate (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) :
    Matrix (Fin n) (Fin n) ℝ :=
  (planeRotation p q (equation_5_61 A p q).1 (-(equation_5_61 A p q).2))ᵀ * A *
    planeRotation p q (equation_5_61 A p q).1 (-(equation_5_61 A p q).2)

/-- The book's Jacobi transformation is the backbone's `Matrix.jacobiStep`: the rotation matrix
built from the book's `(c, s)` in the book's sign convention is `Matrix.jacobiRotation`
(`Matrix.jacobiRotation_eq_planeRotation_small`). -/
theorem jacobiRotate_eq_jacobiStep (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) :
    jacobiRotate A p q = jacobiStep A p q := by
  rw [jacobiRotate, jacobiStep, jacobiRotation_eq_planeRotation_small, equation_5_61_eq]

/-- **(5.59).** The Jacobi transformation annihilates the chosen entry: `a^(k)_pq = 0` for the
`(c, s)` of (5.61)–(5.62), the `(p, q)` entry of (5.60) being `(c² − s²) a_pq − c s (a_qq − a_pp)`,
which vanishes exactly when `t = s/c` solves (5.61). Backbone `Matrix.jacobiStep_apply_eq_zero`
(`Matrix.jacobiSmall_annihilate` is the identity in the book's convention). -/
theorem equation_5_59 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {p q : Fin n} (hpq : p ≠ q) :
    jacobiRotate A p q p q = 0 := by
  rw [jacobiRotate_eq_jacobiStep]
  exact jacobiStep_apply_eq_zero A hA hpq

/-! ### (5.63)–(5.64): the off-diagonal mass -/

/-- **(5.63).** For `M ∈ ℝ^{n×n}`, `Ψ(M) = (∑_{i ≠ j} m_ij²)^{1/2}`. -/
noncomputable def equation_5_63 (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j ∈ univ.erase i, M i j ^ 2)

/-- `Ψ(M)` is the square root of the backbone's off-diagonal mass `Matrix.offDiagNormSq M`. -/
theorem equation_5_63_eq_sqrt (M : Matrix (Fin n) (Fin n) ℝ) :
    equation_5_63 M = Real.sqrt (offDiagNormSq M) := by
  rw [equation_5_63, offDiagNormSq_real]

open scoped Matrix.Norms.Frobenius in
/-- **(5.63), the two forms.** `Ψ(M)² = ∑_{i ≠ j} m_ij²` is the backbone's off-diagonal mass
`Matrix.offDiagNormSq M`, `Ψ(M) ≥ 0`, and `Ψ(M) = (‖M‖_F² − ∑ᵢ m_ii²)^{1/2}` (Mathlib's Frobenius
norm, `Matrix.offDiagNormSq_add_sum_diag_sq_real`). -/
theorem equation_5_63_eq (M : Matrix (Fin n) (Fin n) ℝ) :
    equation_5_63 M ^ 2 = offDiagNormSq M ∧ 0 ≤ equation_5_63 M ∧
      equation_5_63 M = Real.sqrt (‖M‖ ^ 2 - ∑ i, M i i ^ 2) := by
  refine ⟨?_, Real.sqrt_nonneg _, ?_⟩
  · rw [equation_5_63_eq_sqrt, Real.sq_sqrt (offDiagNormSq_nonneg M)]
  · rw [equation_5_63_eq_sqrt, frobenius_norm_sq_eq_sum_sq]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [← offDiagNormSq_add_sum_diag_sq_real, add_sub_cancel_right]

/-- **(5.64).** For a symmetric `A`, `p ≠ q` and any Givens rotation `G_pq` (`c² + s² = 1`) with
`(G_pqᵀ A G_pq)_pq = 0` — in particular the one of (5.59) — the off-diagonal mass drops by exactly
`2 a_pq²`: `Ψ(G_pqᵀ A G_pq)² = Ψ(A)² − 2 a_pq²`, hence `Ψ(A^(k)) ≤ Ψ(A^(k−1))`. Backbone
`Matrix.offDiagNormSq_conj_planeRotation_of_apply_eq_zero`. -/
theorem equation_5_64 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {p q : Fin n} (hpq : p ≠ q)
    {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1)
    (h0 : ((planeRotation p q c (-s))ᵀ * A * planeRotation p q c (-s)) p q = 0) :
    equation_5_63 ((planeRotation p q c (-s))ᵀ * A * planeRotation p q c (-s)) ^ 2 =
        equation_5_63 A ^ 2 - 2 * A p q ^ 2 ∧
      equation_5_63 ((planeRotation p q c (-s))ᵀ * A * planeRotation p q c (-s)) ≤
        equation_5_63 A ∧
      equation_5_63 (jacobiRotate A p q) ^ 2 = equation_5_63 A ^ 2 - 2 * A p q ^ 2 := by
  have hcs' : c ^ 2 + (-s) ^ 2 = 1 := by rwa [neg_sq]
  have key := offDiagNormSq_conj_planeRotation_of_apply_eq_zero A hA hpq hcs' h0
  refine ⟨?_, ?_, ?_⟩
  · rw [(equation_5_63_eq _).1, (equation_5_63_eq _).1, key]
  · rw [equation_5_63_eq_sqrt, equation_5_63_eq_sqrt, key]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (A p q)])
  · rw [(equation_5_63_eq _).1, (equation_5_63_eq _).1, jacobiRotate_eq_jacobiStep,
      offDiagNormSq_jacobiStep A hA hpq]

/-! ### The classical and the row-cyclic Jacobi method -/

/-- **The classical Jacobi method** (§5.10.1, the "optimal choice" of `(p, q)`): at each step the
pair `(p, q)` is one at which `|a^(k−1)_pq| = max_{i ≠ j} |a^(k−1)_ij|` (backbone
`Matrix.classicalJacobiIterate`, `Matrix.maxOffDiagPair`). The iterates are symmetric, keep the
characteristic polynomial of `A` (they are orthogonally similar to it), satisfy
`Ψ(A^(ν))² ≤ (1 − 2/(n² − n))^ν Ψ(A)²`, and converge to a diagonal matrix whose entries are the
eigenvalues of `A`. Backbone `Matrix.isSymm_classicalJacobiIterate`,
`Matrix.charpoly_classicalJacobiIterate`, `Matrix.offDiagNormSq_classicalJacobiIterate_le`,
`Matrix.tendsto_classicalJacobiIterate`. The book states the convergence without a theorem. -/
theorem classicalJacobi [Nonempty (Fin n)] {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (hn : 2 ≤ n) :
    (∀ ν, (classicalJacobiIterate A ν).IsSymm) ∧
      (∀ ν, (classicalJacobiIterate A ν).charpoly = A.charpoly) ∧
      (∀ ν, equation_5_63 (classicalJacobiIterate A ν) ^ 2 ≤
        (1 - 2 / ((n : ℝ) ^ 2 - n)) ^ ν * equation_5_63 A ^ 2) ∧
      ∃ Λ : Matrix (Fin n) (Fin n) ℝ, Λ.IsDiag ∧ Λ.charpoly = A.charpoly ∧
        Tendsto (classicalJacobiIterate A) atTop (𝓝 Λ) := by
  have hn' : 2 ≤ Fintype.card (Fin n) := by rwa [Fintype.card_fin]
  refine ⟨isSymm_classicalJacobiIterate hA, charpoly_classicalJacobiIterate hn', fun ν => ?_,
    tendsto_classicalJacobiIterate hA hn'⟩
  rw [(equation_5_63_eq _).1, (equation_5_63_eq _).1]
  simpa using offDiagNormSq_classicalJacobiIterate_le hA ν

/-- The pairs `(p, q)`, `1 ≤ p < q ≤ n`, in the row order of the cyclic Jacobi method: for each
row `p = 1, …, n − 1`, the columns `q = p + 1, …, n`. -/
def cyclicPairs (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun p => ((List.finRange n).filter fun q => p < q).map fun q => (p, q)

/-- Every pair of the row-cyclic order is off the diagonal. -/
theorem cyclicPairs_ne {pq : Fin n × Fin n} (h : pq ∈ cyclicPairs n) : pq.1 ≠ pq.2 := by
  simp only [cyclicPairs, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_finRange,
    true_and, decide_eq_true_eq] at h
  obtain ⟨p, q, hpq, rfl⟩ := h
  exact hpq.ne

/-- **One sweep of the row-cyclic Jacobi method** (§5.10.1, Program 40): the Jacobi
transformations (5.59)–(5.62) applied at the pairs `(p, q)` of `cyclicPairs` in row order, `p = 1,
…, n − 1`, `q = p + 1, …, n`; a sweep is `N = n(n − 1)/2` transformations. -/
noncomputable def cyclicJacobiSweep (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (cyclicPairs n).foldl (fun M pq => jacobiRotate M pq.1 pq.2) A

/-- The row-cyclic Jacobi method: `A^(k+N)` is the `k`-th sweep applied to `A`. -/
noncomputable def cyclicJacobiIterate (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  cyclicJacobiSweep^[k] A

/-- A run of Jacobi transformations at off-diagonal pairs keeps a symmetric matrix symmetric,
keeps its characteristic polynomial, and does not increase `Ψ`. -/
theorem foldl_jacobiRotate_spec (l : List (Fin n × Fin n)) (hl : ∀ pq ∈ l, pq.1 ≠ pq.2)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    (l.foldl (fun M pq => jacobiRotate M pq.1 pq.2) A).IsSymm ∧
      (l.foldl (fun M pq => jacobiRotate M pq.1 pq.2) A).charpoly = A.charpoly ∧
      offDiagNormSq (l.foldl (fun M pq => jacobiRotate M pq.1 pq.2) A) ≤ offDiagNormSq A := by
  induction l generalizing A with
  | nil => exact ⟨hA, rfl, le_rfl⟩
  | cons pq l ih =>
    have hpq : pq.1 ≠ pq.2 := hl pq (List.mem_cons_self ..)
    have hl' : ∀ pq ∈ l, pq.1 ≠ pq.2 := fun pq h => hl pq (List.mem_cons_of_mem _ h)
    rw [List.foldl_cons]
    obtain ⟨h1, h2, h3⟩ := ih hl' (A := jacobiRotate A pq.1 pq.2)
      (by rw [jacobiRotate_eq_jacobiStep]; exact isSymm_jacobiStep hA _ _)
    refine ⟨h1, ?_, h3.trans ?_⟩
    · rw [h2, jacobiRotate_eq_jacobiStep, charpoly_jacobiStep A hpq]
    · rw [jacobiRotate_eq_jacobiStep, offDiagNormSq_jacobiStep A hA hpq]
      nlinarith [sq_nonneg (A pq.1 pq.2)]

/-- **The sweeps of the cyclic Jacobi method** are orthogonal similarities of `A`: every iterate
is symmetric with the characteristic polynomial of `A`, and `Ψ` does not increase from one sweep
to the next ((5.64) at every transformation). -/
theorem cyclicJacobiSweep_spec {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (k : ℕ) :
    (cyclicJacobiIterate A k).IsSymm ∧ (cyclicJacobiIterate A k).charpoly = A.charpoly ∧
      equation_5_63 (cyclicJacobiIterate A (k + 1)) ≤ equation_5_63 (cyclicJacobiIterate A k) := by
  have hstep : ∀ {B : Matrix (Fin n) (Fin n) ℝ}, B.IsSymm →
      (cyclicJacobiSweep B).IsSymm ∧ (cyclicJacobiSweep B).charpoly = B.charpoly ∧
        offDiagNormSq (cyclicJacobiSweep B) ≤ offDiagNormSq B :=
    fun hB => foldl_jacobiRotate_spec (cyclicPairs n) (fun _ h => cyclicPairs_ne h) hB
  have hiter : ∀ k, (cyclicJacobiIterate A k).IsSymm ∧
      (cyclicJacobiIterate A k).charpoly = A.charpoly := by
    intro k
    induction k with
    | zero => exact ⟨hA, rfl⟩
    | succ k ih =>
      rw [cyclicJacobiIterate, Function.iterate_succ_apply']
      exact ⟨(hstep ih.1).1, (hstep ih.1).2.1.trans ih.2⟩
  refine ⟨(hiter k).1, (hiter k).2, ?_⟩
  rw [cyclicJacobiIterate, Function.iterate_succ_apply', equation_5_63_eq_sqrt,
    equation_5_63_eq_sqrt]
  exact Real.sqrt_le_sqrt (hstep (hiter k).1).2.2

/-! ### §5.10.2: Sturm sequences -/

/-- **(5.65), the Sturm sequence.** For `T = tridiag(b, d, b)` (diagonal `d_1, …, d_n`, off-diagonal
`b_1, …, b_{n−1}`; here `d i = d_{i+1}`, `b i = b_{i+1}`): `p_0(x) = 1`, `p_1(x) = d_1 − x`,
`p_i(x) = (d_i − x) p_{i−1}(x) − b_{i−1}² p_{i−2}(x)` for `i = 2, …, n`. -/
noncomputable def sturmSeq (d b : ℕ → ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => C (d 0) - X
  | i + 2 => (C (d (i + 1)) - X) * sturmSeq d b (i + 1) - C (b i) ^ 2 * sturmSeq d b i

/-- The book's recurrence is the backbone's `Sturm.seq`. -/
theorem sturmSeq_eq (d b : ℕ → ℝ) : ∀ i, sturmSeq d b i = Sturm.seq d b i
  | 0 => rfl
  | 1 => rfl
  | i + 2 => by
    rw [sturmSeq, Sturm.seq_add_two, sturmSeq_eq d b (i + 1), sturmSeq_eq d b i]

/-- **(5.65), the determinant form.** `p_i(x) = det (T_i − x I_i)` for the principal minor `T_i`
of order `i`, and `p_n` is the characteristic polynomial of `T` — in the book's convention
`det (T − x I)`, that is `(−1)^n` times Mathlib's `charpoly`. Backbone `Sturm.seq_eq_det`,
`Sturm.seq_eq_charpoly`. -/
theorem equation_5_65 (d b : ℕ → ℝ) (i : ℕ) :
    sturmSeq d b i = ((symmTridiagonalOf d b i).map (C : ℝ → ℝ[X]) -
        (X : ℝ[X]) • (1 : Matrix (Fin i) (Fin i) ℝ[X])).det ∧
      sturmSeq d b i = (-1) ^ i * (symmTridiagonalOf d b i).charpoly := by
  rw [sturmSeq_eq]
  exact ⟨Sturm.seq_eq_det d b i, Sturm.seq_eq_charpoly d b i⟩

/-- **Property 5.11, first clause (strict interlacing).** For an unreduced `T` (`b_i ≠ 0` for all
`i`) and `i = 2, …, n` (here `i + 1` with `i ≥ 1`), the eigenvalues of `T_{i−1}` strictly separate
those of `T_i`: with the sorted eigenvalues `λ_1(T_i) > … > λ_i(T_i)`,
`λ_{k+1}(T_i) < λ_k(T_{i−1}) < λ_k(T_i)` for `k = 1, …, i − 1`. Backbone
`Sturm.eigenvalues_succ_lt`, `Sturm.eigenvalues_lt_castSucc` (Cauchy interlacing for the leading
principal submatrix, made strict by the absence of common roots of consecutive `p_i`); the
eigenvalues of an unreduced `T` are therefore simple (`Sturm.eigenvalues_simple`). -/
theorem property_5_11_interlace (d b : ℕ → ℝ) (hb : ∀ i, b i ≠ 0) (i : ℕ) (k : Fin i) :
    Sturm.eigenvalues d b (i + 1) k.succ < Sturm.eigenvalues d b i k ∧
      Sturm.eigenvalues d b i k < Sturm.eigenvalues d b (i + 1) k.castSucc :=
  ⟨Sturm.eigenvalues_succ_lt d b i (fun j _ => hb j) k,
    Sturm.eigenvalues_lt_castSucc d b i (fun j _ => hb j) k⟩

/-- **Property 5.11, second clause (the sign-change count).** For an unreduced `T` and any real
`μ`, two consecutive elements of `S_μ = {p_0(μ), …, p_n(μ)}` cannot vanish together, and the
number `s(μ)` of sign changes in `S_μ` — with the convention that a vanishing `p_i(μ)` has the
sign opposite to `p_{i−1}(μ)` (`Sturm.sign`, `Sturm.signChanges`) — is the number of eigenvalues
of `T` that are at most `μ`, counted with multiplicity (`Polynomial.countRootsIn (Set.Iic μ)` of
the characteristic polynomial). Backbone `Sturm.eval_ne_zero_or_eval_ne_zero`,
`Sturm.signChanges_eq_countRootsIn`. Reading: the book says "strictly less than `μ`"; under its
own sign convention the count includes an eigenvalue equal to `μ` (for `n = 1`, `μ = d_1`, the
sequence `1, 0` has one sign change), and the two agree off the spectrum. -/
theorem property_5_11_count (d b : ℕ → ℝ) (hb : ∀ i, b i ≠ 0) (n : ℕ) (μ : ℝ) :
    (∀ i, (sturmSeq d b i).eval μ ≠ 0 ∨ (sturmSeq d b (i + 1)).eval μ ≠ 0) ∧
      Sturm.signChanges d b n μ =
        (symmTridiagonalOf d b n).charpoly.countRootsIn (Set.Iic μ) := by
  simp only [sturmSeq_eq]
  exact ⟨fun i => Sturm.eval_ne_zero_or_eval_ne_zero d b i (fun j _ => hb j) μ,
    Sturm.signChanges_eq_countRootsIn d b n (fun j _ => hb j) μ⟩

/-! ### Givens' method -/

/-- **Givens' method** (§5.10.2, Programs 42–44). With `b_0 = b_n = 0`, Theorem 5.2 gives the
interval `J = [α, β]` containing the spectrum of `T`, `α = min_i (d_i − (|b_{i−1}| + |b_i|))`,
`β = max_i (d_i + (|b_{i−1}| + |b_i|))` (the radii are `Sturm.gershgorinRadius`); for the `i`-th
eigenvalue (counting from the largest) the bisection starts from `a^(0) = α`, `b^(0) = β` and at
each step sets `c = (a + b)/2`, `b := c` if `s(c) > n − i` and `a := c` otherwise
(`Sturm.bisectionStep`); `givensBisection d b n i r = (a^(r), b^(r))`. -/
noncomputable def givensBisection (d b : ℕ → ℝ) (n i : ℕ) (r : ℕ) : ℝ × ℝ :=
  Sturm.bisectionIterate d b n i
    (⨅ j : Fin n, (d j - Sturm.gershgorinRadius b n j),
      ⨆ j : Fin n, (d j + Sturm.gershgorinRadius b n j)) r

/-- **Givens' method, the enclosure and the step.** The interval `[α, β]` contains the spectrum
of `T` (`Sturm.spectrum_subset_Icc`, Theorem 5.2), and one step is the bisection
`c = (a^(r) + b^(r))/2`, `(a^(r+1), b^(r+1)) = (a^(r), c)` if `s(c) > n − i`, `(c, b^(r))`
otherwise. -/
theorem givensBisection_spec (d b : ℕ → ℝ) (n i : ℕ) :
    spectrum ℝ (symmTridiagonalOf d b n) ⊆
        Set.Icc (givensBisection d b n i 0).1 (givensBisection d b n i 0).2 ∧
      ∀ r, givensBisection d b n i (r + 1) =
        if n - i < Sturm.signChanges d b n
            (((givensBisection d b n i r).1 + (givensBisection d b n i r).2) / 2) then
          ((givensBisection d b n i r).1,
            ((givensBisection d b n i r).1 + (givensBisection d b n i r).2) / 2)
        else (((givensBisection d b n i r).1 + (givensBisection d b n i r).2) / 2,
          (givensBisection d b n i r).2) :=
  ⟨Sturm.spectrum_subset_Icc d b n, fun _ => rfl⟩

-- TODO(backbone): natural home `Numlib/Eigen/Sturm`, beside
-- `Sturm.eigenvalues_mem_bisectionIterate`, whose half-open bracket fails when the Gershgorin
-- bound `α` is itself the smallest eigenvalue.
/-- **Givens' bisection from the Gershgorin interval encloses the eigenvalue**: for an unreduced
`T` and `1 ≤ i ≤ n`, the `i`-th largest eigenvalue lies in the *closed* interval `[a^(r), b^(r)]`
for every `r`. When `s(α) ≤ n − i` this is `Sturm.eigenvalues_mem_bisectionIterate` (with
`s(β) = n`); otherwise `α` is the smallest eigenvalue, `i = n`, and the left endpoint never
moves. -/
theorem eigenvalues_mem_Icc_givensBisection (d b : ℕ → ℝ) (hb : ∀ i, b i ≠ 0) {n i : ℕ}
    (hi : 1 ≤ i) (hin : i ≤ n) (r : ℕ) :
    Sturm.eigenvalues d b n ⟨i - 1, by omega⟩ ∈
      Set.Icc (givensBisection d b n i r).1 (givensBisection d b n i r).2 := by
  set α := ⨅ j : Fin n, (d j - Sturm.gershgorinRadius b n j) with hα
  set β := ⨆ j : Fin n, (d j + Sturm.gershgorinRadius b n j) with hβ
  have hn : 0 < n := by omega
  have hβs : n - i < Sturm.signChanges d b n β := by
    rw [Sturm.signChanges_eq_count d b n (fun j _ => hb j), Sturm.count_eq_of_le d b le_rfl]
    omega
  by_cases hαs : Sturm.signChanges d b n α ≤ n - i
  · exact Set.Ioc_subset_Icc_self
      (Sturm.eigenvalues_mem_bisectionIterate d b (fun j _ => hb j) hi hin (ab := (α, β)) ⟨hαs, hβs⟩
        r)
  push Not at hαs
  -- `α` is an eigenvalue, hence the smallest one, and `i = n`
  have hpos : 0 < Sturm.count d b n α := by
    rw [← Sturm.signChanges_eq_count d b n (fun j _ => hb j)]; omega
  obtain ⟨k, hk⟩ : ∃ k, Sturm.eigenvalues d b n k ≤ α := by
    rw [Sturm.count, Finset.card_pos] at hpos
    obtain ⟨k, hk⟩ := hpos
    exact ⟨k, (Finset.mem_filter.mp hk).2⟩
  have hlast : Sturm.eigenvalues d b n ⟨n - 1, by omega⟩ = α :=
    le_antisymm ((Sturm.antitone_eigenvalues d b n
      (Fin.le_iff_val_le_val.mpr (by simp; omega))).trans hk) (Sturm.eigenvalues_mem_Icc d b n _).1
  have hcount : Sturm.count d b n α = 1 := by
    have h := Sturm.count_eigenvalues d b (n := n) (fun j _ => hb j) ⟨n - 1, by omega⟩
    rw [hlast] at h
    rw [h]
    simp only
    omega
  have hin' : i = n := by
    rw [Sturm.signChanges_eq_count d b n (fun j _ => hb j), hcount] at hαs
    omega
  subst hin'
  -- the left endpoint never moves
  have hleft : ∀ r, (givensBisection d b i i r).1 = α ∧ α ≤ (givensBisection d b i i r).2 := by
    intro r
    induction r with
    | zero => exact ⟨rfl, ((Sturm.eigenvalues_mem_Icc d b i ⟨0, hn⟩).1).trans
        (Sturm.eigenvalues_mem_Icc d b i ⟨0, hn⟩).2⟩
    | succ r ih =>
      have hc : α ≤ ((givensBisection d b i i r).1 + (givensBisection d b i i r).2) / 2 := by
        rw [ih.1]; linarith [ih.2]
      have hs : i - i < Sturm.signChanges d b i
          (((givensBisection d b i i r).1 + (givensBisection d b i i r).2) / 2) :=
        lt_of_lt_of_le hαs (Sturm.signChanges_monotone d b i (fun j _ => hb j) hc)
      rw [(givensBisection_spec d b i i).2 r, ite_eq_left hs]
      exact ⟨ih.1, hc⟩
  rw [hlast, (hleft r).1]
  exact ⟨le_rfl, (hleft r).2⟩

/-- **Givens' method, the error bound** (§5.10.2). For an unreduced `T` and `1 ≤ i ≤ n`, after
`r` bisection steps from `[α, β]` the interval `[a^(r), b^(r)]` contains `λ_i`, has length
`(β − α)/2^r`, and its midpoint `c^(r) = (a^(r) + b^(r))/2` approximates `λ_i` within
`(β − α) 2^{−(r+1)} ≤ (|α| + |β|) 2^{−(r+1)}`, the bound the book quotes from (6.9). Backbone
`Sturm.bisectionIterate_length` with `eigenvalues_mem_Icc_givensBisection`. -/
theorem givensBisection_error (d b : ℕ → ℝ) (hb : ∀ i, b i ≠ 0) {n i : ℕ} (hi : 1 ≤ i)
    (hin : i ≤ n) (r : ℕ) :
    Sturm.eigenvalues d b n ⟨i - 1, by omega⟩ ∈
        Set.Icc (givensBisection d b n i r).1 (givensBisection d b n i r).2 ∧
      (givensBisection d b n i r).2 - (givensBisection d b n i r).1 =
        ((givensBisection d b n i 0).2 - (givensBisection d b n i 0).1) / 2 ^ r ∧
      |((givensBisection d b n i r).1 + (givensBisection d b n i r).2) / 2 -
          Sturm.eigenvalues d b n ⟨i - 1, by omega⟩| ≤
        ((givensBisection d b n i 0).2 - (givensBisection d b n i 0).1) / 2 ^ (r + 1) ∧
      ((givensBisection d b n i 0).2 - (givensBisection d b n i 0).1) / 2 ^ (r + 1) ≤
        (|(givensBisection d b n i 0).1| + |(givensBisection d b n i 0).2|) / 2 ^ (r + 1) := by
  have hmem := eigenvalues_mem_Icc_givensBisection d b hb hi hin r
  have hlen : (givensBisection d b n i r).2 - (givensBisection d b n i r).1 =
      ((givensBisection d b n i 0).2 - (givensBisection d b n i 0).1) / 2 ^ r :=
    Sturm.bisectionIterate_length d b n i _ r
  refine ⟨hmem, hlen, ?_, ?_⟩
  · rw [abs_le, pow_succ, ← div_div, ← hlen]
    constructor <;> linarith [hmem.1, hmem.2]
  · refine div_le_div_of_nonneg_right ?_ (by positivity)
    linarith [le_abs_self (givensBisection d b n i 0).2, neg_le_abs (givensBisection d b n i 0).1]

end QuarteroniSaccoSaleri.Chapter05

import Numlib.Eigen.Perturbation
import Numlib.LinearAlgebra.Matrix.DiagDominant
import NumlibSurface.QuarteroniSaccoSaleri.Chapter01.Section11

/-!
# Quarteroni–Sacco–Saleri §5.1: geometrical location of the eigenvalues

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §5.1, over the backbone `Numlib/Eigen/Perturbation` (Hirsch's bounds,
the Gershgorin discs and the counting theorem), `Numlib/LinearAlgebra/Matrix/HermitianPart` (the
Hermitian and skew-Hermitian parts), `Numlib/LinearAlgebra/Sparse/Pattern` (irreducibility as
strong connectivity of the adjacency quiver) and `Numlib/LinearAlgebra/Matrix/DiagDominant` (the
third Gershgorin theorem), and over Chapter 1's Theorem 1.4 for the norm bound (5.1).

## Conventions

The book works in `ℂ^{n×n}`, which is `Matrix (Fin n) (Fin n) ℂ`; the spectrum is
`spectrum ℂ A`. The Gershgorin row circle `R_i` is `Metric.closedBall (A i i) (∑_{j ≠ i} ‖A i j‖)`
and the column circle `C_j` is `Metric.closedBall (A j j) (∑_{i ≠ j} ‖A i j‖)`, written out in
every statement so that each one is the backbone's verbatim. The Hermitian part `H = (A + Aᴴ)/2`
is `Matrix.hermitianPart A` and the matrix `S = (A − Aᴴ)/(2i)` of Theorem 5.1 is
`Matrix.skewHermitianPart A`; `λ_min`, `λ_max` are the infimum and supremum of Mathlib's
eigenvalue function `Matrix.IsHermitian.eigenvalues`. "Exactly `m` eigenvalues, each counted with
its algebraic multiplicity" is `Polynomial.countRootsIn S A.charpoly = m`. A reducible matrix
(Definition 5.1) is `definition_5_1`, stated for any entry type with a zero, since only the zero
pattern matters; the book's `P A Pᵀ` is `A.submatrix σ σ` for the permutation `σ` and the index set
of the leading block `B₁₁` is a proper nonempty `Finset`.

## Contents

* `equation_5_1` — `|λ| ≤ ‖A‖` for a consistent matrix norm.
* `theorem_5_1_re`, `theorem_5_1_im` — Hirsch's theorem, (5.2).
* `theorem_5_2`, `equation_5_6`, `property_5_1`, `property_5_2` — the row and column circles,
  the first and the second Gershgorin theorem.
* `definition_5_1`, `definition_5_1_iff`, `property_5_3`, `property_5_4` — reducibility, its
  agreement with the backbone's pattern irreducibility, the oriented-graph characterization and
  the third Gershgorin theorem.

## Readings

Definition 5.1 and the backbone's `Matrix.IsPatternIrreducible` differ for `n = 1`: the `1 × 1`
zero matrix is pattern-reducible (no path of positive length) but not reducible in the book's
sense (no proper nonempty block). The hypothesis `2 ≤ n` on `definition_5_1_iff`, `property_5_3`
and `property_5_4` records it. Example 5.1 is a numerical table and Remark 5.1 is prose; neither
is a node.
-/

open Finset Matrix

namespace QuarteroniSaccoSaleri.Chapter05

variable {n : ℕ}

/-! ### (5.1) and Theorem 5.1 -/

/-- **(5.1).** For every consistent matrix norm `‖·‖` on `ℂ^{n×n}` (a seminorm `N` on the matrices
consistent with a definite vector norm `p`, Definition 1.20) and every `λ ∈ σ(A)`,
`|λ| ≤ ‖A‖`: all the eigenvalues of `A` lie in the disc of radius `‖A‖` about the origin. This is
Theorem 1.4, `ρ(A) ≤ ‖A‖`, read at one eigenvalue. -/
theorem equation_5_1 {N : Seminorm ℂ (Matrix (Fin n) (Fin n) ℂ)} {p : Seminorm ℂ (Fin n → ℂ)}
    (hp : ∀ x, p x = 0 → x = 0) (hN : IsConsistent N p p) (A : Matrix (Fin n) (Fin n) ℂ) :
    ∀ μ ∈ spectrum ℂ A, ‖μ‖ ≤ N A := by
  intro μ hμ
  have h : (‖μ‖₊ : ENNReal) ≤ ENNReal.ofReal (N A) := by
    refine le_trans ?_ (Chapter01.theorem_1_4 hp hN A)
    rw [spectralRadius_eq_of_unital]
    exact le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ A) => (‖k‖₊ : ENNReal)) μ hμ
  rwa [← enorm_eq_nnnorm, ← ofReal_norm, ENNReal.ofReal_le_ofReal_iff (apply_nonneg N A)] at h

/-- **Theorem 5.1 (Hirsch), real part, (5.2).** Let `H = (A + Aᴴ)/2` be the Hermitian part of
`A ∈ ℂ^{n×n}`. For any `λ ∈ σ(A)`, `λ_min(H) ≤ Re λ ≤ λ_max(H)`. Backbone `Matrix.hirsch_re`
(Bendixson's theorem read through `Matrix.toEuclideanLin`). -/
theorem theorem_5_1_re (A : Matrix (Fin n) (Fin n) ℂ) {μ : ℂ} (hμ : μ ∈ spectrum ℂ A) :
    (⨅ i, (hermitianPart_isHermitian A).eigenvalues i) ≤ μ.re ∧
      μ.re ≤ ⨆ i, (hermitianPart_isHermitian A).eigenvalues i :=
  hirsch_re A hμ

/-- **Theorem 5.1 (Hirsch), imaginary part, (5.2).** Let `S = (A − Aᴴ)/(2i)`, so that `iS` is
the skew-Hermitian part of `A ∈ ℂ^{n×n}` and `S` itself is Hermitian. For any `λ ∈ σ(A)`,
`λ_min(S) ≤ Im λ ≤ λ_max(S)`. Backbone `Matrix.hirsch_im` (the real half for `−iA`). -/
theorem theorem_5_1_im (A : Matrix (Fin n) (Fin n) ℂ) {μ : ℂ} (hμ : μ ∈ spectrum ℂ A) :
    (⨅ i, (skewHermitianPart_isHermitian A).eigenvalues i) ≤ μ.im ∧
      μ.im ≤ ⨆ i, (skewHermitianPart_isHermitian A).eigenvalues i :=
  hirsch_im A hμ

/-! ### Theorem 5.2 and the first two Gershgorin theorems -/

/-- **Theorem 5.2 (of the Gershgorin circles), (5.4).** For `A ∈ ℂ^{n×n}`,
`σ(A) ⊆ S_R = ⋃ᵢ R_i` with the row circles `R_i = {z : |z − a_ii| ≤ ∑_{j ≠ i} |a_ij|}`.
Backbone `Matrix.spectrum_subset_iUnion_closedBall`. -/
theorem theorem_5_2 (A : Matrix (Fin n) (Fin n) ℂ) :
    spectrum ℂ A ⊆ ⋃ i, Metric.closedBall (A i i) (∑ j ∈ univ.erase i, ‖A i j‖) :=
  spectrum_subset_iUnion_closedBall A

/-- **(5.6).** Since `A` and `Aᵀ` share the same spectrum, Theorem 5.2 also holds with the column
circles `C_j = {z : |z − a_jj| ≤ ∑_{i ≠ j} |a_ij|}`: `σ(A) ⊆ S_C = ⋃ⱼ C_j`. Backbone
`Matrix.spectrum_subset_iUnion_closedBall_col`. -/
theorem equation_5_6 (A : Matrix (Fin n) (Fin n) ℂ) :
    spectrum ℂ A ⊆ ⋃ j, Metric.closedBall (A j j) (∑ i ∈ univ.erase j, ‖A i j‖) :=
  spectrum_subset_iUnion_closedBall_col A

/-- **Property 5.1 (First Gershgorin theorem), (5.7).** For `A ∈ ℂ^{n×n}`, every `λ ∈ σ(A)` lies
in `S_R ∩ S_C`, the intersection of the union of the row circles with the union of the column
circles: (5.4) and (5.6) together. -/
theorem property_5_1 (A : Matrix (Fin n) (Fin n) ℂ) :
    spectrum ℂ A ⊆
      (⋃ i, Metric.closedBall (A i i) (∑ j ∈ univ.erase i, ‖A i j‖)) ∩
        ⋃ j, Metric.closedBall (A j j) (∑ i ∈ univ.erase j, ‖A i j‖) :=
  Set.subset_inter (theorem_5_2 A) (equation_5_6 A)

/-- **Property 5.2 (Second Gershgorin theorem).** Let `S₁` be the union of the row circles `R_i`
indexed by a set `τ` of `m` indices (the book's `i = 1, …, m`) and `S₂` the union of the remaining
ones. If `S₁ ∩ S₂ = ∅`, then `S₁` contains exactly `m` eigenvalues of `A`, each counted with its
algebraic multiplicity, while the remaining `n − m` eigenvalues are contained in `S₂`: the counts
are `Polynomial.countRootsIn` of the characteristic polynomial, and every eigenvalue outside `S₁`
lies in `S₂`. Backbone `Matrix.card_spectrum_of_disjoint_gershgorin`, applied to `τ` and to its
complement, with Theorem 5.2 for the last clause. -/
theorem property_5_2 (A : Matrix (Fin n) (Fin n) ℂ) (τ : Finset (Fin n)) {S₁ S₂ : Set ℂ}
    (hS₁ : S₁ = ⋃ i ∈ τ, Metric.closedBall (A i i) (∑ j ∈ univ.erase i, ‖A i j‖))
    (hS₂ : S₂ = ⋃ i ∈ τᶜ, Metric.closedBall (A i i) (∑ j ∈ univ.erase i, ‖A i j‖))
    (hdisj : Disjoint S₁ S₂) :
    A.charpoly.countRootsIn S₁ = τ.card ∧ A.charpoly.countRootsIn S₂ = n - τ.card ∧
      ∀ μ ∈ spectrum ℂ A, μ ∉ S₁ → μ ∈ S₂ := by
  refine ⟨card_spectrum_of_disjoint_gershgorin A τ hS₁ hS₂ hdisj, ?_, fun μ hμ hμ₁ => ?_⟩
  · rw [card_spectrum_of_disjoint_gershgorin A τᶜ hS₂ (by rw [compl_compl]; exact hS₁) hdisj.symm,
      card_compl, Fintype.card_fin]
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (theorem_5_2 A hμ)
    by_cases hiτ : i ∈ τ
    · exact absurd (hS₁ ▸ Set.mem_iUnion₂.mpr ⟨i, hiτ, hi⟩) hμ₁
    · exact hS₂ ▸ Set.mem_iUnion₂.mpr ⟨i, Finset.mem_compl.mpr hiτ, hi⟩

/-! ### Definition 5.1 and the third Gershgorin theorem -/

/-- **Definition 5.1.** A matrix `A ∈ ℂ^{n×n}` is *reducible* if there is a permutation matrix
`P` such that `P A Pᵀ = [[B₁₁, B₁₂], [0, B₂₂]]` with `B₁₁` and `B₂₂` square: here `P A Pᵀ` is
`A.submatrix σ σ` for a permutation `σ` of the indices, `s` is the (proper, nonempty) index set of
the leading block `B₁₁`, and the zero block is the condition that the entries from `sᶜ` to `s`
vanish. `A` is *irreducible* if it is not reducible. The definition only looks at the zero
pattern, so it is stated for any entry type with a zero; the book states it over `ℂ` and uses it
over `ℝ` in Property 5.3. -/
def definition_5_1 {R : Type*} [Zero R] (A : Matrix (Fin n) (Fin n) R) : Prop :=
  ∃ (σ : Equiv.Perm (Fin n)) (s : Finset (Fin n)), s.Nonempty ∧ s ≠ univ ∧
    ∀ i ∉ s, ∀ j ∈ s, A.submatrix σ σ i j = 0

/-- **Definition 5.1 agrees with the backbone**: for `n ≥ 2`, `A` is reducible in the sense of
Definition 5.1 iff it is not pattern-irreducible (`Matrix.IsPatternIrreducible`, strong
connectivity of the adjacency quiver). This is
`Matrix.not_isPatternIrreducible_iff_exists_submatrix_blockTriangular` with the block set
replaced by its complement: the backbone zeroes the entries from `s` to `sᶜ`, the book those from
`sᶜ` to `s`. For `n = 1` the two notions differ (the `1 × 1` zero matrix is pattern-reducible but
not reducible), hence the hypothesis. -/
theorem definition_5_1_iff {R : Type*} [NormedAddCommGroup R] (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) R) : definition_5_1 A ↔ ¬ A.IsPatternIrreducible := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rw [not_isPatternIrreducible_iff_exists_submatrix_blockTriangular]
  constructor
  · rintro ⟨σ, s, hs, hsu, hz⟩
    exact ⟨σ, sᶜ, Finset.nonempty_iff_ne_empty.mpr (mt s.compl_eq_empty_iff.mp hsu),
      s.compl_ne_univ_iff_nonempty.mpr hs,
      fun i hi j hj => hz i (Finset.mem_compl.mp hi) j (by simpa using hj)⟩
  · rintro ⟨σ, s, hs, hsu, hz⟩
    exact ⟨σ, sᶜ, Finset.nonempty_iff_ne_empty.mpr (mt s.compl_eq_empty_iff.mp hsu),
      s.compl_ne_univ_iff_nonempty.mpr hs,
      fun i hi j hj => hz i (by simpa using hi) j (Finset.mem_compl.mp hj)⟩

/-- **Property 5.3.** A matrix `A ∈ ℝ^{n×n}` (`n ≥ 2`) is irreducible iff its oriented graph is
strongly connected: the graph joins the vertices `P_i`, `P_j` by a line oriented from `P_i` to
`P_j` iff `a_ij ≠ 0` (Mathlib's `Matrix.adjQuiver A`, whose arrows `i ⟶ j` are exactly the
nonzero entries, `Matrix.nonempty_adjQuiver_hom_iff`), and strong connectivity asks for an
oriented path between every pair of distinct vertices. Backbone
`Matrix.isPatternIrreducible_iff_nonempty_path` through `definition_5_1_iff`; the book cites
[Var62] for the proof. -/
theorem property_5_3 (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) :
    ¬ definition_5_1 A ↔
      letI := A.adjQuiver; ∀ i j : Fin n, i ≠ j → Nonempty (Quiver.Path i j) := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  let _ : Quiver (Fin n) := A.adjQuiver
  rw [definition_5_1_iff hn, not_not, isPatternIrreducible_iff_nonempty_path]
  refine ⟨fun h i j _ => h i j, fun h i j => ?_⟩
  by_cases hij : i = j
  · subst hij
    exact ⟨Quiver.Path.nil⟩
  · exact h i j hij

/-- **Property 5.4 (Third Gershgorin theorem).** Let `A ∈ ℂ^{n×n}` (`n ≥ 2`) be irreducible. An
eigenvalue `λ ∈ σ(A)` cannot lie on the boundary of `S_R` unless it belongs to the boundary of
every circle `R_i`, `i = 1, …, n`: if `λ ∈ frontier S_R` then `|λ − a_ii| = ∑_{j ≠ i} |a_ij|`
for every `i`. Backbone `Matrix.IsPatternIrreducible.norm_sub_eq_of_mem_frontier` through
`definition_5_1_iff`. -/
theorem property_5_4 (hn : 2 ≤ n) {A : Matrix (Fin n) (Fin n) ℂ} (hA : ¬ definition_5_1 A)
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ A)
    (hfr : μ ∈ frontier (⋃ i, Metric.closedBall (A i i) (∑ j ∈ univ.erase i, ‖A i j‖)))
    (i : Fin n) : ‖μ - A i i‖ = ∑ j ∈ univ.erase i, ‖A i j‖ :=
  (not_not.mp ((definition_5_1_iff hn A).not.mp hA)).norm_sub_eq_of_mem_frontier hμ hfr i

end QuarteroniSaccoSaleri.Chapter05

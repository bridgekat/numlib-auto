import Numlib.Direct.Substitution
import Numlib.FloatingPoint.Stationary
import Numlib.LinearAlgebra.Matrix.PosDef
import Numlib.Stationary.Block
import Numlib.Stationary.ConsistentlyOrdered
import Numlib.Stationary.DiagDominant
import Numlib.Stationary.SPD
import Numlib.Stationary.Sweep
import NumlibSurface.QuarteroniSaccoSaleri.Chapter04.Section01

/-!
# Quarteroni–Sacco–Saleri §4.2: linear iterative methods

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §4.2, over the backbone `Numlib/Stationary/Splitting` (splittings
`A = P - N` and the Jacobi, JOR, Gauss–Seidel, SOR and SSOR splittings), `Numlib/Stationary/Sweep`
(the componentwise sweeps and their identification with the splitting steps),
`Numlib/Stationary/SPD` (the Householder–John theorem and the energy-norm theory for symmetric
positive definite matrices, Kahan's bound), `Numlib/Stationary/DiagDominant` (strict diagonal
dominance), `Numlib/Stationary/ConsistentlyOrdered` (Young's theory of SOR) and
`Numlib/Stationary/Block` (block Jacobi).

## Conventions

A splitting `A = P - N` with `P` nonsingular is `Splitting A`, the backbone's
`Stationary.Splitting A`, with `P = s.m` and `N = s.n`; the iteration (4.6),
`P x⁽ᵏ⁺¹⁾ = N x⁽ᵏ⁾ + b`, is the step `Stationary.Splitting.mulVecStep s b`, and its iteration
matrix is `s.iterationOperator`. The letters of §4.2.1 are `D A = diagPart A`,
`E A = -strictLower A`, `F A = -strictUpper A`, so that `A = D - E - F` (`decomp`). The hypothesis
"the diagonal entries of `A` are nonzero" is `IsUnit (diagPart A)` (backbone
`Matrix.isUnit_diagPart_iff`). The Jacobi, JOR, Gauss–Seidel and SOR methods are the sweeps
`Matrix.jorSweep A 1 b`, `Matrix.jorSweep A ω b`, `Matrix.sorSweep A 1 b` and
`Matrix.sorSweep A ω b` of the backbone, defined by their matrix formulas; their componentwise
recursions (4.10), (4.13), (4.15) are theorems, and each sweep is the step of its splitting.

Every convergence statement reads "for every right-hand side `b` and every `x⁽⁰⁾`, the iterates
tend to `A⁻¹ b`", `Tendsto (fun k => (sweep)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b))`, and is obtained from a
spectral-radius bound on the real iteration matrix (`Matrix.complexSpectralRadius`) through
Theorem 4.1 (`Splitting.tendsto`, `Splitting.forall_tendsto_iff`). Energy norms are the real
quadratic forms `(A *ᵥ e) ⬝ᵥ e`; "`‖B‖_A = ρ(B)`" is the pair of statements
`(A (B e)) ⬝ (B e) ≤ ρ(B)² ((A e) ⬝ e)` for all `e` and equality for some `e ≠ 0`, and "monotone
convergence in `‖·‖_A`" is the strict decrease `(A (B e)) ⬝ (B e) < (A e) ⬝ e` for `e ≠ 0` along
the error recursion `e⁽ᵏ⁺¹⁾ = B e⁽ᵏ⁾` of (4.4). The book's matrices have positive order, which is
the `[NeZero n]` of the statements whose existence clauses need it.

## Contents

* `Splitting`, `Splitting.consistent`, `Splitting.tendsto`, `Splitting.forall_tendsto_iff`,
  `equation_4_6`, `equation_4_7` — splittings and Theorem 4.1 for them.
* `property_4_1_spectralRadius_lt_one`, `property_4_1_energyNorm`, `property_4_1_monotone`,
  `property_4_2_isUnit`, `property_4_2`, `property_4_2_monotone` — the two convergence results
  for symmetric positive definite `A`.
* `D`, `E`, `F`, `decomp`, `equation_4_10`, `equation_4_12`, `equation_4_13`, `equation_4_15`,
  `equation_4_16`, `equation_4_17`, `sor_step_eq_add_inv_mulVec` — §4.2.1.
* `theorem_4_2_jacobi`, `theorem_4_2_jacobi_linfty`, `theorem_4_2_gaussSeidel`, `theorem_4_3`,
  `theorem_4_3_energyNorm`, `theorem_4_4`, `theorem_4_4_iff`, `theorem_4_5`, `equation_4_18`,
  `definition_4_3`, `definition_4_3_iff`, `equation_4_18_of_hasAProperty`, `theorem_4_6` — §4.2.2.
* `theorem_4_7`, `theorem_4_7_zero`, `property_4_3`, `property_4_3_diagDominant`, `property_4_4`,
  `property_4_4_optimal` — §4.2.3.
* `example_4_3_matrix`, `example_4_3_solution`, `example_4_3_spectralRadius`, `perturbedIterate`,
  `equation_4_20`, `equation_4_20_iterate`, `equation_4_20_bound` — §4.2.4.
* `theorem_4_3_block` — §4.2.5.
* `backwardGaussSeidel_step`, `equation_4_21`, `property_4_5`, `equation_4_22`, `ssor_tendsto`
  — §4.2.6.

Example 4.2 is a table of numerically computed spectral radii and has no node; Programs 15–16 are
not nodes, the sweeps they implement being `Matrix.jorSweep` and `Matrix.sorSweep`.

## Readings and errata

Property 4.5 says "`B_SGS` is symmetric positive definite"; that is false as printed (for a
diagonal `A`, `B_SGS = 0`, and `B_SGS` is not Euclidean-symmetric in general). What holds, and what
its source (Hackbusch) proves, is that `B_SGS` is self-adjoint and positive semidefinite in the
`A`-inner product: `A B_SGS` is symmetric positive semidefinite (`property_4_5`). Theorem 4.7 is
stated "for any `ω ∈ ℝ`"; at `ω = 0` the SOR matrix is the identity, with spectral radius
`1 = |0 - 1|` (`theorem_4_7_zero`). Definition 4.3 differs from Saad's and Young's Property A: it
takes consistent ordering (in the spectral sense the definition spells out, backbone
`Matrix.IsConsistentlyOrdered`) *and* the printed `2 × 2` block form with diagonal blocks as
hypotheses; only the first is used by (4.18) and Property 4.4. The energy-norm clauses of Property
4.1 need only `A` and `P` symmetric positive definite, not `2P - A`; they are stated so.
-/

open Filter Finset Matrix Stationary Topology WithLp
open scoped ENNReal NNReal

namespace QuarteroniSaccoSaleri.Chapter04

variable {n : ℕ}

/-! ### Splittings, (4.6)–(4.7), and Theorem 4.1 for them -/

/-- **§4.2, the splitting `A = P - N`** with `P` nonsingular, the *preconditioning matrix* or
*preconditioner*: the backbone's `Stationary.Splitting A`, with `P = s.m` and `N = s.n = P - A`. -/
abbrev Splitting (A : Matrix (Fin n) (Fin n) ℝ) := Stationary.Splitting A

variable {A : Matrix (Fin n) (Fin n) ℝ}

/-- **(4.6).** The iteration `P x⁽ᵏ⁺¹⁾ = N x⁽ᵏ⁾ + b` of a splitting `A = P - N`: its step is
`Stationary.Splitting.mulVecStep s b`, it is the method (4.2) with iteration matrix `B = P⁻¹ N` and
`f = P⁻¹ b`. -/
theorem equation_4_6 (s : Splitting A) (b x : Fin n → ℝ) :
    A = s.m - s.n ∧ s.m *ᵥ (s.mulVecStep b x) = s.n *ᵥ x + b ∧
      s.mulVecStep b x = affineStep s.iterationOperator (s.m⁻¹ *ᵥ b) x ∧
      s.iterationOperator = s.m⁻¹ * s.n := by
  refine ⟨s.m_sub_n.symm, mulVec_nonsing_inv_mulVec s.isUnit _,
    s.mulVecStep_eq_iterationOperator_mulVec_add b x, ?_⟩
  rw [s.iterationOperator_eq, nonsing_inv_eq_ringInverse]

/-- **(4.7)–(4.8).** The step of (4.6) is the update `x⁽ᵏ⁺¹⁾ = x⁽ᵏ⁾ + P⁻¹ r⁽ᵏ⁾` by the
preconditioned residual `r⁽ᵏ⁾ = b - A x⁽ᵏ⁾`, and it is consistent: its fixed points are the
solutions of `A x = b`. -/
theorem equation_4_7 (s : Splitting A) (b x : Fin n → ℝ) :
    s.mulVecStep b x = x + s.m⁻¹ *ᵥ (b - A *ᵥ x) ∧ (s.mulVecStep b x = x ↔ A *ᵥ x = b) :=
  ⟨s.mulVecStep_eq_add_inv_mulVec b x, s.mulVecStep_fixed_iff b x⟩

/-- The splitting iteration is consistent in the sense of Definition 4.1 when `A` is nonsingular:
`x = A⁻¹ b` is a fixed point of `x ↦ P⁻¹ N x + P⁻¹ b`. -/
theorem Splitting.consistent (s : Splitting A) (hA : IsUnit A) (b : Fin n → ℝ) :
    definition_4_1 A b s.iterationOperator (s.m⁻¹ *ᵥ b) := by
  have h := (s.mulVecStep_fixed_iff b (A⁻¹ *ᵥ b)).mpr (mulVec_nonsing_inv_mulVec hA b)
  rw [s.mulVecStep_eq_iterationOperator_mulVec_add] at h
  exact h.symm

/-- **Theorem 4.1 for a splitting, the sufficiency**: if `ρ(P⁻¹ N) < 1`, the iteration (4.6)
converges to `A⁻¹ b` from every `x⁽⁰⁾`, for every `b` (`A` is then automatically nonsingular). -/
theorem Splitting.tendsto (s : Splitting A) (hs : complexSpectralRadius s.iterationOperator < 1)
    (b x₀ : Fin n → ℝ) :
    Tendsto (fun k => (s.mulVecStep b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b)) := by
  have hstep : s.mulVecStep b = affineStep s.iterationOperator (s.m⁻¹ *ᵥ b) :=
    funext fun x => s.mulVecStep_eq_iterationOperator_mulVec_add b x
  rw [hstep]
  exact (theorem_4_1 (s.consistent (s.isUnit_of_complexSpectralRadius_lt_one hs) b)).2 hs x₀

/-- **Theorem 4.1 for a splitting**: the iteration (4.6) converges to `A⁻¹ b` from every `x⁽⁰⁾`,
for every `b`, iff `ρ(P⁻¹ N) < 1`. -/
theorem Splitting.forall_tendsto_iff (s : Splitting A) :
    (∀ b x₀, Tendsto (fun k => (s.mulVecStep b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b))) ↔
      complexSpectralRadius s.iterationOperator < 1 := by
  refine ⟨fun h => ?_, fun hs b x₀ => s.tendsto hs b x₀⟩
  have hstep : s.mulVecStep 0 = affineStep s.iterationOperator (s.m⁻¹ *ᵥ 0) :=
    funext fun x => s.mulVecStep_eq_iterationOperator_mulVec_add 0 x
  refine complexSpectralRadius_lt_one_of_forall_tendsto (x := A⁻¹ *ᵥ 0) (f := s.m⁻¹ *ᵥ 0)
    fun x₀ => ?_
  rw [← hstep]
  exact h 0 x₀

/-! ### Properties 4.1 and 4.2 -/

section SPD

/-- For a symmetric `P`, the Householder–John matrix `P + Pᵀ - A` is `2P - A`. -/
private theorem add_transpose_sub_of_isHermitian {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : P.IsHermitian) : P + Pᵀ - A = 2 • P - A := by
  rw [← conjTranspose_eq_transpose_of_trivial, hP.eq, two_smul]

/-- **Property 4.1, convergence.** Let `A = P - N` with `A` and `P` symmetric positive definite.
If `2P - A` is positive definite then `ρ(B) < 1` and the iteration (4.7) converges for every
`x⁽⁰⁾` (and every `b`). Householder–John (backbone
`Stationary.Splitting.complexSpectralRadius_lt_one_of_posDef`) with `P + Pᵀ - A = 2P - A`. -/
theorem property_4_1_spectralRadius_lt_one (hA : A.PosDef) (s : Splitting A) (hP : s.m.PosDef)
    (h2 : (2 • s.m - A).PosDef) :
    complexSpectralRadius s.iterationOperator < 1 ∧
      ∀ b x₀, Tendsto (fun k => (s.mulVecStep b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b)) := by
  have hρ := s.complexSpectralRadius_lt_one_of_posDef hA
    (by rwa [add_transpose_sub_of_isHermitian hP.1])
  exact ⟨hρ, fun b x₀ => s.tendsto hρ b x₀⟩

/-- The energy form of an eigenvector: `(X (B e)) ⬝ (B e) = μ² ((X e) ⬝ e)` when `B e = μ e`. -/
private theorem energy_of_mulVec_eq_smul {B X : Matrix (Fin n) (Fin n) ℝ} {e : Fin n → ℝ} {μ : ℝ}
    (h : B *ᵥ e = μ • e) : (X *ᵥ (B *ᵥ e)) ⬝ᵥ (B *ᵥ e) = μ ^ 2 * ((X *ᵥ e) ⬝ᵥ e) := by
  rw [h, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  ring

/-- **Property 4.1, `ρ(B) = ‖B‖_A = ‖B‖_P`.** For `A` and `P` symmetric positive definite (this
clause does not need `2P - A`), the operator norms of `B = P⁻¹ N` induced by the energy norms
`‖·‖_A` and `‖·‖_P` are both `ρ(B)`: `‖B e‖_A ≤ ρ(B) ‖e‖_A` for every `e` with equality for some
`e ≠ 0`, and likewise for `‖·‖_P`, written with the squared forms. Backbone
`Stationary.Splitting.energyNorm_mulVec_iterationOperator_le_complexSpectralRadius` and
`Stationary.Splitting.energyNorm_m_mulVec_iterationOperator_le_complexSpectralRadius`; the
equalities hold at a real eigenvector of modulus `ρ(B)`
(`Stationary.Splitting.exists_mulVec_iterationOperator_eq_smul`). -/
theorem property_4_1_energyNorm [NeZero n] (hA : A.PosDef) (s : Splitting A) (hP : s.m.PosDef) :
    (∀ e, (A *ᵥ (s.iterationOperator *ᵥ e)) ⬝ᵥ (s.iterationOperator *ᵥ e) ≤
        (complexSpectralRadius s.iterationOperator).toReal ^ 2 * ((A *ᵥ e) ⬝ᵥ e)) ∧
      (∃ e ≠ 0, (A *ᵥ (s.iterationOperator *ᵥ e)) ⬝ᵥ (s.iterationOperator *ᵥ e) =
        (complexSpectralRadius s.iterationOperator).toReal ^ 2 * ((A *ᵥ e) ⬝ᵥ e)) ∧
      (∀ e, (s.m *ᵥ (s.iterationOperator *ᵥ e)) ⬝ᵥ (s.iterationOperator *ᵥ e) ≤
        (complexSpectralRadius s.iterationOperator).toReal ^ 2 * ((s.m *ᵥ e) ⬝ᵥ e)) ∧
      ∃ e ≠ 0, (s.m *ᵥ (s.iterationOperator *ᵥ e)) ⬝ᵥ (s.iterationOperator *ᵥ e) =
        (complexSpectralRadius s.iterationOperator).toReal ^ 2 * ((s.m *ᵥ e) ⬝ᵥ e) := by
  obtain ⟨e, he, μ, hμ, hBe⟩ := s.exists_mulVec_iterationOperator_eq_smul hA hP.1
  refine ⟨s.energyNorm_mulVec_iterationOperator_le_complexSpectralRadius hA hP.1,
    ⟨e, he, ?_⟩, s.energyNorm_m_mulVec_iterationOperator_le_complexSpectralRadius hA.1 hP,
    ⟨e, he, ?_⟩⟩ <;>
  · rw [energy_of_mulVec_eq_smul hBe, ← hμ, sq_abs]

/-- **Property 4.1, monotonicity.** Under the hypotheses of `property_4_1_spectralRadius_lt_one`
the convergence is monotone in both energy norms: `‖e⁽ᵏ⁺¹⁾‖_P < ‖e⁽ᵏ⁾‖_P` and
`‖e⁽ᵏ⁺¹⁾‖_A < ‖e⁽ᵏ⁾‖_A` along the error recursion `e⁽ᵏ⁺¹⁾ = B e⁽ᵏ⁾`, for every `e⁽ᵏ⁾ ≠ 0`. The
`A`-clause is `Stationary.Splitting.energyNorm_mulVec_iterationOperator_lt`; the `P`-clause follows
from `‖B e‖_P ≤ ρ(B) ‖e‖_P` and `ρ(B) < 1`. -/
theorem property_4_1_monotone (hA : A.PosDef) (s : Splitting A) (hP : s.m.PosDef)
    (h2 : (2 • s.m - A).PosDef) {e : Fin n → ℝ} (he : e ≠ 0) :
    (A *ᵥ (s.iterationOperator *ᵥ e)) ⬝ᵥ (s.iterationOperator *ᵥ e) < (A *ᵥ e) ⬝ᵥ e ∧
      (s.m *ᵥ (s.iterationOperator *ᵥ e)) ⬝ᵥ (s.iterationOperator *ᵥ e) < (s.m *ᵥ e) ⬝ᵥ e := by
  have hQ : (s.m + s.mᵀ - A).PosDef := by rwa [add_transpose_sub_of_isHermitian hP.1]
  refine ⟨s.energyNorm_mulVec_iterationOperator_lt hA hQ he, ?_⟩
  have hρ := (property_4_1_spectralRadius_lt_one hA s hP h2).1
  have hρ' : (complexSpectralRadius s.iterationOperator).toReal < 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_strict_mono ENNReal.one_ne_top hρ
  have hle := s.energyNorm_m_mulVec_iterationOperator_le_complexSpectralRadius hA.1 hP e
  have hpos : 0 < (s.m *ᵥ e) ⬝ᵥ e := by
    have := hP.dotProduct_mulVec_pos he
    rwa [star_trivial, dotProduct_comm] at this
  have hsq : (complexSpectralRadius s.iterationOperator).toReal ^ 2 < 1 :=
    (pow_lt_one_iff_of_nonneg ENNReal.toReal_nonneg two_ne_zero).mpr hρ'
  nlinarith

/-- **Property 4.2, `P` is invertible.** If `A` and `P + Pᵀ - A` are positive definite then `P` is
nonsingular, so that `A = P - N` is a splitting in the sense of §4.2:
`P + Pᵀ = (P + Pᵀ - A) + A` is positive definite. -/
theorem property_4_2_isUnit (hA : A.PosDef) {P : Matrix (Fin n) (Fin n) ℝ}
    (hQ : (P + Pᵀ - A).PosDef) : IsUnit P :=
  isUnit_of_posDef_add_transpose (by simpa using hQ.add hA)

/-- **Property 4.2.** Let `A = P - N` with `A` symmetric positive definite. If `P + Pᵀ - A` is
positive definite then `P` is invertible (`property_4_2_isUnit`, so that `A = P - N` is a
splitting `s` in the sense of §4.2, with `P = s.m`), the iteration (4.7) converges for every
`x⁽⁰⁾` and every `b`, and `ρ(B) ≤ ‖B‖_A < 1`: there is `q < 1` with `ρ(B) ≤ q` and
`‖B e‖_A ≤ q ‖e‖_A` for every `e`. Householder–John
(`Stationary.Splitting.complexSpectralRadius_lt_one_of_posDef`) and the uniform energy contraction
(`Stationary.Splitting.exists_complexSpectralRadius_le_and_energyNorm_mulVec_le`). -/
theorem property_4_2 (hA : A.PosDef) (s : Splitting A) (hQ : (s.m + s.mᵀ - A).PosDef) :
    complexSpectralRadius s.iterationOperator < 1 ∧
      (∀ b x₀, Tendsto (fun k => (s.mulVecStep b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b))) ∧
      ∃ q : ℝ, q < 1 ∧ (complexSpectralRadius s.iterationOperator).toReal ≤ q ∧
        ∀ e : Fin n → ℝ, (A *ᵥ (s.iterationOperator *ᵥ e)) ⬝ᵥ (s.iterationOperator *ᵥ e) ≤
          q ^ 2 * ((A *ᵥ e) ⬝ᵥ e) := by
  have hρ := s.complexSpectralRadius_lt_one_of_posDef hA hQ
  exact ⟨hρ, fun b x₀ => s.tendsto hρ b x₀,
    s.exists_complexSpectralRadius_le_and_energyNorm_mulVec_le hA hQ⟩

/-- **Property 4.2, monotone convergence in `‖·‖_A`**: under its hypotheses, `‖B e‖_A < ‖e‖_A` for
every `e ≠ 0` (`Stationary.Splitting.energyNorm_mulVec_iterationOperator_lt`). -/
theorem property_4_2_monotone (hA : A.PosDef) (s : Splitting A) (hQ : (s.m + s.mᵀ - A).PosDef)
    {e : Fin n → ℝ} (he : e ≠ 0) :
    (A *ᵥ (s.iterationOperator *ᵥ e)) ⬝ᵥ (s.iterationOperator *ᵥ e) < (A *ᵥ e) ⬝ᵥ e :=
  s.energyNorm_mulVec_iterationOperator_lt hA hQ he

end SPD

/-! ### §4.2.1 Jacobi, Gauss–Seidel and relaxation methods -/

section Classical

/-- **§4.2.1, the letter `D`**: the diagonal matrix of the diagonal entries of `A`. -/
def D (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := diagPart A

/-- **§4.2.1, the letter `E`**: the lower triangular matrix with entries `e_ij = -a_ij` for `i > j`
and `e_ij = 0` for `i ≤ j`, that is `-strictLower A`. -/
def E (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := -strictLower A

/-- **§4.2.1, the letter `F`**: the upper triangular matrix with entries `f_ij = -a_ij` for `j > i`
and `f_ij = 0` for `j ≤ i`, that is `-strictUpper A`. -/
def F (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := -strictUpper A

/-- **§4.2.1, `A = D - (E + F)`**: the splitting of `A` into its diagonal, its strictly lower and
its strictly upper parts, in the letters of the book. -/
theorem decomp (A : Matrix (Fin n) (Fin n) ℝ) : A = D A - E A - F A :=
  (diagPart_sub_neg_strictLower_sub_neg_strictUpper A).symm

/-- `D - E = diagPart A + strictLower A`, the matrix the forward sweeps invert. -/
theorem D_sub_E (A : Matrix (Fin n) (Fin n) ℝ) : D A - E A = diagPart A + strictLower A := by
  rw [D, E, sub_neg_eq_add]

/-- `D - F = diagPart A + strictUpper A`, the matrix the backward sweeps invert. -/
theorem D_sub_F (A : Matrix (Fin n) (Fin n) ℝ) : D A - F A = diagPart A + strictUpper A := by
  rw [D, F, sub_neg_eq_add]

/-- `D - ω E = diagPart A + ω • strictLower A`. -/
theorem D_sub_smul_E (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) :
    D A - ω • E A = diagPart A + ω • strictLower A := by
  rw [D, E, smul_neg, sub_neg_eq_add]

/-- `D - ω F = diagPart A + ω • strictUpper A`. -/
theorem D_sub_smul_F (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) :
    D A - ω • F A = diagPart A + ω • strictUpper A := by
  rw [D, F, smul_neg, sub_neg_eq_add]

/-- **(4.9)–(4.11), the Jacobi method.** If the diagonal entries of `A` are nonzero, the Jacobi
step computes `x_i⁽ᵏ⁺¹⁾ = (b_i - ∑_{j ≠ i} a_ij x_j⁽ᵏ⁾) / a_ii` (4.10); it is the step of the
splitting `P = D`, `N = D - A = E + F` (`Matrix.jacobiSplitting`, backbone
`Matrix.jorSweep_one_eq_mulVecStep`), whose iteration matrix is `B_J = D⁻¹ (E + F) = I - D⁻¹ A`
(4.11). -/
theorem equation_4_10 (h : IsUnit (diagPart A)) (b x : Fin n → ℝ) :
    (∀ i, jorSweep A 1 b x i = (b i - ∑ j ∈ univ.erase i, A i j * x j) / A i i) ∧
      jorSweep A 1 b x = (jacobiSplitting A h).mulVecStep b x ∧
      (jacobiSplitting A h).m = D A ∧ (jacobiSplitting A h).n = E A + F A ∧
      (jacobiSplitting A h).iterationOperator = (D A)⁻¹ * (E A + F A) ∧
      (jacobiSplitting A h).iterationOperator = 1 - (D A)⁻¹ * A := by
  refine ⟨fun i => ?_, congrFun (jorSweep_one_eq_mulVecStep A h b) x, rfl, ?_, ?_, ?_⟩
  · rw [jorSweep, sub_self, zero_mul, add_zero, div_mul_eq_mul_div, one_mul]
  · rw [jacobiSplitting_n, E, F, neg_add]
  · rw [jacobiSplitting_iterationOperator, D, E, F, ← neg_add, mul_neg, neg_mul]
  · rw [D, nonsing_inv_eq_ringInverse]
    rfl

/-- The inverse of a nonzero multiple of an invertible matrix. -/
private theorem inv_smul_of_isUnit {c : ℝ} (hc : c ≠ 0) {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsUnit M) : (c • M)⁻¹ = c⁻¹ • M⁻¹ := by
  refine inv_eq_left_inv ?_
  rw [smul_mul_smul_comm, inv_mul_cancel₀ hc, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hM),
    one_smul]

/-- **(4.12), the JOR method.** With a relaxation parameter `ω ≠ 0`, the over-relaxation step
`x_i⁽ᵏ⁺¹⁾ = (ω / a_ii) (b_i - ∑_{j ≠ i} a_ij x_j⁽ᵏ⁾) + (1 - ω) x_i⁽ᵏ⁾` is the step of the splitting
`P = ω⁻¹ D` (`Matrix.jorSplitting`, backbone `Matrix.jorSweep_eq_mulVecStep`); its iteration
matrix is `B_{Jω} = ω B_J + (1 - ω) I` (4.12), in the form (4.7) it reads
`x⁽ᵏ⁺¹⁾ = x⁽ᵏ⁾ + ω D⁻¹ r⁽ᵏ⁾`, it is consistent for every `ω ≠ 0`, and for `ω = 1` it is the Jacobi
method. -/
theorem equation_4_12 (h : IsUnit (diagPart A)) {ω : ℝ} (hω : ω ≠ 0) (b x : Fin n → ℝ) :
    (∀ i, jorSweep A ω b x i =
        ω / A i i * (b i - ∑ j ∈ univ.erase i, A i j * x j) + (1 - ω) * x i) ∧
      jorSweep A ω b x = (jorSplitting A h hω).mulVecStep b x ∧
      (jorSplitting A h hω).iterationOperator =
        ω • (jacobiSplitting A h).iterationOperator + (1 - ω) • 1 ∧
      jorSweep A ω b x = x + ω • ((D A)⁻¹ *ᵥ (b - A *ᵥ x)) ∧
      (jorSweep A ω b x = x ↔ A *ᵥ x = b) ∧ jorSplitting A h one_ne_zero = jacobiSplitting A h := by
  have hstep := congrFun (jorSweep_eq_mulVecStep A h hω b) x
  refine ⟨fun i => rfl, hstep, by rw [jorSplitting_iterationOperator, add_comm], ?_,
    by rw [hstep, Splitting.mulVecStep_fixed_iff], jorSplitting_one A h⟩
  rw [hstep, Splitting.mulVecStep_eq_add_inv_mulVec]
  have hm : (jorSplitting A h hω).m = ω⁻¹ • diagPart A := rfl
  rw [hm, inv_smul_of_isUnit (inv_ne_zero hω) h, inv_inv, smul_mulVec, D]

/-- **(4.13)–(4.14), the Gauss–Seidel method.** The step `y = x⁽ᵏ⁺¹⁾` from `x = x⁽ᵏ⁾` computes
`y_i = (b_i - ∑_{j < i} a_ij y_j - ∑_{j > i} a_ij x_j) / a_ii`, using the already updated
components (4.13; backbone `Matrix.sorSweep_apply` at `ω = 1`); it is the step of the splitting
`P = D - E`, `N = F` (`Matrix.gaussSeidelSplitting`, backbone `Matrix.sorSweep_one_eq_mulVecStep`),
with iteration matrix `B_GS = (D - E)⁻¹ F` (4.14). -/
theorem equation_4_13 (h : IsUnit (diagPart A)) (b x : Fin n → ℝ) :
    (∀ i, sorSweep A 1 b x i = (b i - ∑ j ∈ univ.filter (· < i), A i j * sorSweep A 1 b x j
        - ∑ j ∈ univ.filter (i < ·), A i j * x j) / A i i) ∧
      sorSweep A 1 b x = (gaussSeidelSplitting A h).mulVecStep b x ∧
      (gaussSeidelSplitting A h).m = D A - E A ∧ (gaussSeidelSplitting A h).n = F A ∧
      (gaussSeidelSplitting A h).iterationOperator = (D A - E A)⁻¹ * F A := by
  refine ⟨fun i => ?_, congrFun (sorSweep_one_eq_mulVecStep A h b) x, ?_, ?_, ?_⟩
  · rw [sorSweep_apply A h 1 b x i, sub_self, zero_mul, add_zero, div_mul_eq_mul_div, one_mul]
  · rw [D_sub_E]
    rfl
  · rw [gaussSeidelSplitting_n]
    rfl
  · rw [Splitting.iterationOperator_eq, gaussSeidelSplitting_n, ← nonsing_inv_eq_ringInverse,
      D_sub_E]
    rfl

/-- **(4.15), the SOR method.** For `ω ≠ 0`, the successive over-relaxation step `y = x⁽ᵏ⁺¹⁾` from
`x = x⁽ᵏ⁾` computes `y_i = (ω / a_ii) (b_i - ∑_{j < i} a_ij y_j - ∑_{j > i} a_ij x_j) + (1 - ω) x_i`
(backbone `Matrix.sorSweep_apply`), and it is the step of the splitting `P = ω⁻¹ D - E`
(`Matrix.sorSplitting`, backbone `Matrix.sorSweep_eq_mulVecStep`). -/
theorem equation_4_15 (h : IsUnit (diagPart A)) {ω : ℝ} (hω : ω ≠ 0) (b x : Fin n → ℝ) :
    (∀ i, sorSweep A ω b x i =
        ω / A i i * (b i - ∑ j ∈ univ.filter (· < i), A i j * sorSweep A ω b x j
          - ∑ j ∈ univ.filter (i < ·), A i j * x j) + (1 - ω) * x i) ∧
      sorSweep A ω b x = (sorSplitting A h hω).mulVecStep b x :=
  ⟨sorSweep_apply A h ω b x, congrFun (sorSweep_eq_mulVecStep A h hω b) x⟩

/-- `I - ω D⁻¹ E = D⁻¹ (D + ω L)` and `(1 - ω) I + ω D⁻¹ F = D⁻¹ ((1 - ω) D - ω U)`, the two
sides of (4.16) multiplied through by `D`. -/
private theorem one_sub_smul_inv_D_mul_E (h : IsUnit (diagPart A)) (ω : ℝ) :
    (1 : Matrix (Fin n) (Fin n) ℝ) - ω • ((D A)⁻¹ * E A) =
        (diagPart A)⁻¹ * (diagPart A + ω • strictLower A) ∧
      (1 - ω) • (1 : Matrix (Fin n) (Fin n) ℝ) + ω • ((D A)⁻¹ * F A) =
        (diagPart A)⁻¹ * ((1 - ω) • diagPart A - ω • strictUpper A) := by
  have hD : (diagPart A)⁻¹ * diagPart A = 1 :=
    nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp h)
  constructor
  · rw [D, E, mul_neg, smul_neg, sub_neg_eq_add, mul_add, hD, Matrix.mul_smul]
  · rw [D, F, mul_neg, smul_neg, ← sub_eq_add_neg, mul_sub, Matrix.mul_smul, Matrix.mul_smul, hD]

/-- **(4.16), the SOR method in vector form**:
`(I - ω D⁻¹ E) x⁽ᵏ⁺¹⁾ = [(1 - ω) I + ω D⁻¹ F] x⁽ᵏ⁾ + ω D⁻¹ b`, the triangular system
`(D + ω L) y = ((1 - ω) D - ω U) x + ω b` solved by the sweep (backbone
`Matrix.diagPart_add_smul_strictLower_mulVec_sorSweep`) multiplied by `D⁻¹`. -/
theorem equation_4_16 (h : IsUnit (diagPart A)) (ω : ℝ) (b x : Fin n → ℝ) :
    (1 - ω • ((D A)⁻¹ * E A)) *ᵥ sorSweep A ω b x =
      ((1 - ω) • 1 + ω • ((D A)⁻¹ * F A)) *ᵥ x + ω • ((D A)⁻¹ *ᵥ b) := by
  obtain ⟨h1, h2⟩ := one_sub_smul_inv_D_mul_E h ω
  rw [h1, h2, ← mulVec_mulVec, ← mulVec_mulVec, diagPart_add_smul_strictLower_mulVec_sorSweep A h,
    mulVec_add, mulVec_smul, D]

/-- **(4.17), the SOR iteration matrix**
`B(ω) = (I - ω D⁻¹ E)⁻¹ [(1 - ω) I + ω D⁻¹ F]`; it is `Matrix.sorIterationMatrix A ω`, the
iteration operator of `Matrix.sorSplitting` (backbone `Matrix.sorSplitting_iterationOperator`,
`Matrix.sorSplitting_iterationOperator_eq`). -/
theorem equation_4_17 (h : IsUnit (diagPart A)) {ω : ℝ} (hω : ω ≠ 0) :
    (sorSplitting A h hω).iterationOperator =
        (1 - ω • ((D A)⁻¹ * E A))⁻¹ * ((1 - ω) • 1 + ω • ((D A)⁻¹ * F A)) ∧
      (sorSplitting A h hω).iterationOperator = sorIterationMatrix A ω := by
  refine ⟨?_, sorSplitting_iterationOperator_eq A h hω⟩
  obtain ⟨h1, h2⟩ := one_sub_smul_inv_D_mul_E h ω
  have hDdet : IsUnit (diagPart A).det := (isUnit_iff_isUnit_det _).mp h
  rw [sorSplitting_iterationOperator, h1, h2, Matrix.mul_inv_rev, nonsing_inv_nonsing_inv _ hDdet,
    Matrix.mul_assoc, ← Matrix.mul_assoc (diagPart A), mul_nonsing_inv _ hDdet, Matrix.one_mul]

/-- **The display after (4.17)**: in the form (4.7), the SOR method is
`x⁽ᵏ⁺¹⁾ = x⁽ᵏ⁾ + (ω⁻¹ D - E)⁻¹ r⁽ᵏ⁾`; it is consistent for every `ω ≠ 0`, and for `ω = 1` it is the
Gauss–Seidel method (backbone `Matrix.sorSplitting_one`). -/
theorem sor_step_eq_add_inv_mulVec (h : IsUnit (diagPart A)) {ω : ℝ} (hω : ω ≠ 0)
    (b x : Fin n → ℝ) :
    sorSweep A ω b x = x + (ω⁻¹ • D A - E A)⁻¹ *ᵥ (b - A *ᵥ x) ∧
      (sorSweep A ω b x = x ↔ A *ᵥ x = b) ∧
      sorSplitting A h one_ne_zero = gaussSeidelSplitting A h := by
  have hstep := congrFun (sorSweep_eq_mulVecStep A h hω b) x
  refine ⟨?_, by rw [hstep, Splitting.mulVecStep_fixed_iff], sorSplitting_one A h⟩
  rw [hstep, Splitting.mulVecStep_eq_add_inv_mulVec, D, E, sub_neg_eq_add]
  rfl

end Classical

/-! ### §4.2.2 Convergence results for the Jacobi and Gauss–Seidel methods -/

section Convergence

/-- **Theorem 4.2, Jacobi.** If `A` is strictly diagonally dominant by rows, the Jacobi method
converges (to `A⁻¹ b`, for every `b` and every `x⁽⁰⁾`): backbone
`Matrix.jacobi_complexSpectralRadius_lt_one` through Theorem 4.1. -/
theorem theorem_4_2_jacobi (hA : A.IsStrictDiagDominant) (b x₀ : Fin n → ℝ) :
    Tendsto (fun k => (jorSweep A 1 b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b)) := by
  rw [jorSweep_one_eq_mulVecStep A hA.isUnit_diagPart b]
  exact Splitting.tendsto _ (jacobi_complexSpectralRadius_lt_one hA _) b x₀

open scoped Matrix.Norms.Operator in
/-- **Theorem 4.2, the book's proof for Jacobi**: for a strictly row diagonally dominant `A`,
`‖B_J‖_∞ = max_i ∑_{j ≠ i} |a_ij| / |a_ii| < 1` (backbone `Matrix.linfty_opNorm_jacobi_iterMatrix`
and `Matrix.IsStrictDiagDominant.jacobiContraction_lt_one`). -/
theorem theorem_4_2_jacobi_linfty [NeZero n] (hA : A.IsStrictDiagDominant) :
    ‖(jacobiSplitting A hA.isUnit_diagPart).iterationOperator‖ =
        univ.sup' univ_nonempty (fun i => (∑ j ∈ univ.erase i, ‖A i j‖) / ‖A i i‖) ∧
      ‖(jacobiSplitting A hA.isUnit_diagPart).iterationOperator‖ < 1 := by
  rw [linfty_opNorm_jacobi_iterMatrix]
  exact ⟨rfl, hA.jacobiContraction_lt_one⟩

/-- **Theorem 4.2, Gauss–Seidel** (the half the book delegates to [Axe94] and to Exercise 2). If
`A` is strictly diagonally dominant by rows, the Gauss–Seidel method converges: backbone
`Matrix.gaussSeidel_complexSpectralRadius_lt_one` through Theorem 4.1. -/
theorem theorem_4_2_gaussSeidel (hA : A.IsStrictDiagDominant) (b x₀ : Fin n → ℝ) :
    Tendsto (fun k => (sorSweep A 1 b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b)) := by
  rw [sorSweep_one_eq_mulVecStep A hA.isUnit_diagPart b]
  exact Splitting.tendsto _ (gaussSeidel_complexSpectralRadius_lt_one hA _) b x₀

/-- **Theorem 4.3, convergence.** If `A` and `2D - A` are symmetric positive definite, the Jacobi
method converges: Property 4.1 with `P = D` (backbone
`Matrix.jacobiSplitting_complexSpectralRadius_lt_one_of_posDef`). -/
theorem theorem_4_3 (hA : A.PosDef) (h2 : (2 • D A - A).PosDef) (b x₀ : Fin n → ℝ) :
    Tendsto (fun k => (jorSweep A 1 b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b)) := by
  rw [jorSweep_one_eq_mulVecStep A hA.diagPart.isUnit b]
  exact Splitting.tendsto _ (jacobiSplitting_complexSpectralRadius_lt_one_of_posDef hA h2 _) b x₀

/-- **Theorem 4.3, `ρ(B_J) = ‖B_J‖_A = ‖B_J‖_D`**, in the sense of `property_4_1_energyNorm` with
`P = D`: the energy operator norms of the Jacobi matrix are its spectral radius. -/
theorem theorem_4_3_energyNorm [NeZero n] (hA : A.PosDef) :
    (∀ e, (A *ᵥ ((jacobiSplitting A hA.diagPart.isUnit).iterationOperator *ᵥ e)) ⬝ᵥ
          ((jacobiSplitting A hA.diagPart.isUnit).iterationOperator *ᵥ e) ≤
        (complexSpectralRadius (jacobiSplitting A hA.diagPart.isUnit).iterationOperator).toReal ^ 2
          * ((A *ᵥ e) ⬝ᵥ e)) ∧
      (∃ e ≠ 0, (A *ᵥ ((jacobiSplitting A hA.diagPart.isUnit).iterationOperator *ᵥ e)) ⬝ᵥ
          ((jacobiSplitting A hA.diagPart.isUnit).iterationOperator *ᵥ e) =
        (complexSpectralRadius (jacobiSplitting A hA.diagPart.isUnit).iterationOperator).toReal ^ 2
          * ((A *ᵥ e) ⬝ᵥ e)) ∧
      (∀ e, (D A *ᵥ ((jacobiSplitting A hA.diagPart.isUnit).iterationOperator *ᵥ e)) ⬝ᵥ
          ((jacobiSplitting A hA.diagPart.isUnit).iterationOperator *ᵥ e) ≤
        (complexSpectralRadius (jacobiSplitting A hA.diagPart.isUnit).iterationOperator).toReal ^ 2
          * ((D A *ᵥ e) ⬝ᵥ e)) ∧
      ∃ e ≠ 0, (D A *ᵥ ((jacobiSplitting A hA.diagPart.isUnit).iterationOperator *ᵥ e)) ⬝ᵥ
          ((jacobiSplitting A hA.diagPart.isUnit).iterationOperator *ᵥ e) =
        (complexSpectralRadius (jacobiSplitting A hA.diagPart.isUnit).iterationOperator).toReal ^ 2
          * ((D A *ᵥ e) ⬝ᵥ e) :=
  property_4_1_energyNorm hA (jacobiSplitting A hA.diagPart.isUnit) hA.diagPart

/-- **Theorem 4.4.** If `A` is symmetric positive definite, the JOR method converges if
`0 < ω < 2 / ρ(D⁻¹ A)` (backbone `Matrix.jorSplitting_complexSpectralRadius_lt_one_iff_of_posDef`,
whose proof is the book's: `B_{Jω} = I - ω D⁻¹ A` and `D⁻¹ A` has real positive eigenvalues). -/
theorem theorem_4_4 [NeZero n] (hA : A.PosDef) {ω : ℝ} (hω0 : 0 < ω)
    (hω2 : ω < 2 / (complexSpectralRadius ((D A)⁻¹ * A)).toReal) (b x₀ : Fin n → ℝ) :
    Tendsto (fun k => (jorSweep A ω b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b)) := by
  rw [jorSweep_eq_mulVecStep A hA.diagPart.isUnit hω0.ne' b]
  exact Splitting.tendsto _
    ((jorSplitting_complexSpectralRadius_lt_one_iff_of_posDef hA _ hω0.ne').mpr ⟨hω0, hω2⟩) b x₀

/-- **Theorem 4.4, as the equivalence the backbone proves**: for `A` symmetric positive definite
and `ω ≠ 0`, the JOR method converges for every `b` and `x⁽⁰⁾` iff `0 < ω < 2 / ρ(D⁻¹ A)`. -/
theorem theorem_4_4_iff [NeZero n] (hA : A.PosDef) {ω : ℝ} (hω : ω ≠ 0) :
    (∀ b x₀, Tendsto (fun k => (jorSweep A ω b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b))) ↔
      0 < ω ∧ ω < 2 / (complexSpectralRadius ((D A)⁻¹ * A)).toReal := by
  simp only [jorSweep_eq_mulVecStep A hA.diagPart.isUnit hω]
  rw [Splitting.forall_tendsto_iff, jorSplitting_complexSpectralRadius_lt_one_iff_of_posDef hA _ hω]
  rfl

/-- **Theorem 4.5.** If `A` is symmetric positive definite, the Gauss–Seidel method is
monotonically convergent with respect to `‖·‖_A`: it converges for every `b` and `x⁽⁰⁾`, and
`‖B_GS e‖_A < ‖e‖_A` for every `e ≠ 0`. Property 4.2 with `P = D - E`, whose `P + Pᵀ - A = D` is
positive definite because the diagonal of a positive definite matrix is positive (backbone
`Matrix.gaussSeidelSplitting_complexSpectralRadius_lt_one_of_posDef` and
`Stationary.Splitting.energyNorm_mulVec_iterationOperator_lt`). -/
theorem theorem_4_5 (hA : A.PosDef) :
    (∀ b x₀, Tendsto (fun k => (sorSweep A 1 b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b))) ∧
      ∀ e ≠ 0, (A *ᵥ ((gaussSeidelSplitting A hA.diagPart.isUnit).iterationOperator *ᵥ e)) ⬝ᵥ
          ((gaussSeidelSplitting A hA.diagPart.isUnit).iterationOperator *ᵥ e) <
        (A *ᵥ e) ⬝ᵥ e := by
  have h := hA.diagPart.isUnit
  refine ⟨fun b x₀ => ?_, fun e he => ?_⟩
  · rw [sorSweep_one_eq_mulVecStep A h b]
    exact Splitting.tendsto _ (gaussSeidelSplitting_complexSpectralRadius_lt_one_of_posDef hA _)
      b x₀
  · refine Splitting.energyNorm_mulVec_iterationOperator_lt _ hA ?_ he
    rw [← sorSplitting_one A h]
    exact sorSplitting_m_add_transpose_sub_posDef hA.1 (fun i => hA.diag_pos) h one_pos one_lt_two

/-- The real spectral radius of the Jacobi and Gauss–Seidel matrices, read through the
complexification, where Young's theory lives. -/
private theorem complexSpectralRadius_jacobi_gaussSeidel (h : IsUnit (diagPart A)) :
    complexSpectralRadius (jacobiSplitting A h).iterationOperator =
        spectralRadius ℂ
          (jacobiSplitting (complexify A) (isUnit_diagPart_complexify h)).iterationOperator ∧
      complexSpectralRadius (gaussSeidelSplitting A h).iterationOperator =
        spectralRadius ℂ
          (gaussSeidelSplitting (complexify A)
            (isUnit_diagPart_complexify h)).iterationOperator := by
  constructor
  · rw [complexSpectralRadius, complexify_jacobi_iterationOperator A h]
  · rw [complexSpectralRadius, complexify_gaussSeidel_iterationOperator A h]

/-- **(4.18) and the sentence before it.** If `A` is positive definite and tridiagonal, the Jacobi
method converges and `ρ(B_GS) = ρ(B_J)²`, so that Gauss–Seidel converges faster than Jacobi.
A tridiagonal matrix is consistently ordered (backbone `Matrix.IsTridiagonal.isConsistentlyOrdered`)
and the identity is `Matrix.IsConsistentlyOrdered.spectralRadius_gaussSeidel_eq_sq` for the
complexification; Jacobi then converges because `ρ(B_J)² = ρ(B_GS) < 1` (Theorem 4.5). -/
theorem equation_4_18 (hA : A.PosDef) (ht : A.IsTridiagonal) :
    (∀ b x₀, Tendsto (fun k => (jorSweep A 1 b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b))) ∧
      complexSpectralRadius (gaussSeidelSplitting A hA.diagPart.isUnit).iterationOperator =
        complexSpectralRadius (jacobiSplitting A hA.diagPart.isUnit).iterationOperator ^ 2 := by
  have h := hA.diagPart.isUnit
  have hsq : complexSpectralRadius (gaussSeidelSplitting A h).iterationOperator =
      complexSpectralRadius (jacobiSplitting A h).iterationOperator ^ 2 := by
    rw [(complexSpectralRadius_jacobi_gaussSeidel h).1,
      (complexSpectralRadius_jacobi_gaussSeidel h).2]
    exact (ht.complexify.isConsistentlyOrdered (isUnit_diagPart_complexify h))
      |>.spectralRadius_gaussSeidel_eq_sq _
  refine ⟨fun b x₀ => ?_, hsq⟩
  rw [jorSweep_one_eq_mulVecStep A h b]
  refine Splitting.tendsto _ ?_ b x₀
  have hGS := gaussSeidelSplitting_complexSpectralRadius_lt_one_of_posDef hA h
  rw [hsq] at hGS
  by_contra hge
  exact absurd hGS (not_lt.mpr (one_le_pow₀ (not_lt.mp hge)))

/-- **Definition 4.3, as printed.** A matrix `M ∈ ℝ^{n×n}` *enjoys the `A`-property* when it is
consistently ordered — `α D⁻¹ E + α⁻¹ D⁻¹ F` has eigenvalues that do not depend on `α ≠ 0`, where
`M = D - E - F` as in §4.2.1; this is `Matrix.IsConsistentlyOrdered` of its complexification,
spelled out in `definition_4_3_iff` — and it can be partitioned in the `2 × 2` block form
`[D̃₁ M₁₂; M₂₁ D̃₂]` with `D̃₁`, `D̃₂` diagonal: for some `k ≤ n`, the off-diagonal entries with
both indices `< k`, or both `≥ k`, vanish. The partition is the printed contiguous one, and both
clauses are hypotheses; Saad's and Young's Property A is the second up to a permutation. -/
def definition_4_3 (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsConsistentlyOrdered (complexify M) ∧
    ∃ k ≤ n, ∀ i j : Fin n, i ≠ j →
      (((i : ℕ) < k ∧ (j : ℕ) < k) ∨ (k ≤ (i : ℕ) ∧ k ≤ (j : ℕ))) → M i j = 0

/-- **Definition 4.3, the consistently-ordered clause in the book's letters**: the spectrum of
`α D⁻¹ E + α⁻¹ D⁻¹ F` (over `ℂ`) is that of `D⁻¹ E + D⁻¹ F` for every `α ≠ 0`. The backbone's
`Matrix.jacobiLower`, `Matrix.jacobiUpper` are exactly `D⁻¹ E` and `D⁻¹ F`. -/
theorem definition_4_3_iff (M : Matrix (Fin n) (Fin n) ℝ) :
    IsConsistentlyOrdered (complexify M) ↔ ∀ α : ℂ, α ≠ 0 →
      spectrum ℂ (α • ((complexify (D M))⁻¹ * complexify (E M)) +
          α⁻¹ • ((complexify (D M))⁻¹ * complexify (F M))) =
        spectrum ℂ ((complexify (D M))⁻¹ * complexify (E M) +
          (complexify (D M))⁻¹ * complexify (F M)) := by
  have hL : (complexify (D M))⁻¹ * complexify (E M) = jacobiLower (complexify M) := by
    rw [D, E, complexify_neg, complexify_strictLower, complexify_diagPart, jacobiLower, mul_neg,
      neg_mul]
  have hU : (complexify (D M))⁻¹ * complexify (F M) = jacobiUpper (complexify M) := by
    rw [D, F, complexify_neg, complexify_strictUpper, complexify_diagPart, jacobiUpper, mul_neg,
      neg_mul]
  rw [hL, hU]
  rfl

/-- **(4.18) for a matrix with the `A`-property**: "relation (4.18) holds even if `A` enjoys the
`A`-property". Only the consistently-ordered clause of Definition 4.3 is used (backbone
`Matrix.IsConsistentlyOrdered.spectralRadius_gaussSeidel_eq_sq`). -/
theorem equation_4_18_of_hasAProperty (hP : definition_4_3 A) (h : IsUnit (diagPart A)) :
    complexSpectralRadius (gaussSeidelSplitting A h).iterationOperator =
      complexSpectralRadius (jacobiSplitting A h).iterationOperator ^ 2 := by
  rw [(complexSpectralRadius_jacobi_gaussSeidel h).1,
    (complexSpectralRadius_jacobi_gaussSeidel h).2]
  exact hP.1.spectralRadius_gaussSeidel_eq_sq _

/-- **Theorem 4.6.** If the Jacobi method is convergent (`ρ(B_J) < 1`), then the JOR method
converges for `0 < ω ≤ 1`: the eigenvalues of `B_{Jω} = ω B_J + (1 - ω) I` are `ω λ + 1 - ω`, of
modulus at most `ω |λ| + 1 - ω < 1` (backbone
`Matrix.jorSplitting_complexSpectralRadius_lt_one_of_le_one`). -/
theorem theorem_4_6 (h : IsUnit (diagPart A))
    (hJ : complexSpectralRadius (jacobiSplitting A h).iterationOperator < 1) {ω : ℝ}
    (hω0 : 0 < ω) (hω1 : ω ≤ 1) (b x₀ : Fin n → ℝ) :
    Tendsto (fun k => (jorSweep A ω b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b)) := by
  rw [jorSweep_eq_mulVecStep A h hω0.ne' b]
  exact Splitting.tendsto _ (jorSplitting_complexSpectralRadius_lt_one_of_le_one h hJ hω0 hω1) b x₀

end Convergence

/-! ### §4.2.3 Convergence results for the relaxation method -/

section Relaxation

/-- **Theorem 4.7 (Kahan).** For every `ω ≠ 0`, `ρ(B(ω)) ≥ |ω - 1|`; therefore the SOR method
fails to converge if `ω ≤ 0` or `ω ≥ 2`. The product of the eigenvalues of `B(ω)` is
`det B(ω) = (1 - ω)ⁿ` (backbone `Matrix.abs_one_sub_le_sorSplitting_complexSpectralRadius`,
`Matrix.lt_two_of_sorSplitting_complexSpectralRadius_lt_one`). The case `ω = 0` of the printed
"any `ω ∈ ℝ`" is `theorem_4_7_zero`. -/
theorem theorem_4_7 [NeZero n] (h : IsUnit (diagPart A)) {ω : ℝ} (hω : ω ≠ 0) :
    ENNReal.ofReal |ω - 1| ≤ complexSpectralRadius (sorSplitting A h hω).iterationOperator ∧
      (ω ≤ 0 ∨ 2 ≤ ω → ¬ complexSpectralRadius (sorSplitting A h hω).iterationOperator < 1) := by
  refine ⟨by rw [abs_sub_comm]; exact abs_one_sub_le_sorSplitting_complexSpectralRadius h hω,
    fun hout hρ => ?_⟩
  obtain ⟨h0, h2⟩ := lt_two_of_sorSplitting_complexSpectralRadius_lt_one h hω hρ
  rcases hout with hle | hge
  · exact absurd h0 (not_lt.mpr hle)
  · exact absurd h2 (not_lt.mpr hge)

/-- **Theorem 4.7 at `ω = 0`**: the SOR matrix (4.17) is `B(0) = I`, whose spectral radius is
`1 = |0 - 1|`; the method is then the trivial iteration `x⁽ᵏ⁺¹⁾ = x⁽ᵏ⁾`, which does not
converge. -/
theorem theorem_4_7_zero [NeZero n] (h : IsUnit (diagPart A)) :
    sorIterationMatrix A 0 = 1 ∧ complexSpectralRadius (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  have hDdet : IsUnit (diagPart A).det := (isUnit_iff_isUnit_det _).mp h
  refine ⟨?_, ?_⟩
  · rw [sorIterationMatrix, zero_smul, add_zero, sub_zero, zero_smul, sub_zero, one_smul,
      nonsing_inv_mul _ hDdet]
  · rw [complexSpectralRadius, complexify_one]
    have : Nontrivial (Matrix (Fin n) (Fin n) ℂ) := inferInstance
    exact spectrum.spectralRadius_one

/-- **Property 4.3 (Ostrowski).** If `A` is symmetric positive definite, the SOR method (with
`ω ≠ 0`) converges for every `b` and `x⁽⁰⁾` iff `0 < ω < 2`, and then its convergence is monotone
with respect to `‖·‖_A`. The equivalence is backbone
`Matrix.sorSplitting_complexSpectralRadius_lt_one_iff` (Householder–John and Kahan) through
Theorem 4.1; the monotonicity is Property 4.2 for `P = ω⁻¹ D - E`, whose `P + Pᵀ - A = (2/ω - 1) D`
is positive definite for `0 < ω < 2` (backbone `Matrix.sorSplitting_m_add_transpose_sub_posDef`,
`Stationary.Splitting.energyNorm_mulVec_iterationOperator_lt`). -/
theorem property_4_3 [NeZero n] (hA : A.PosDef) {ω : ℝ} (hω : ω ≠ 0) :
    ((∀ b x₀, Tendsto (fun k => (sorSweep A ω b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b))) ↔
        0 < ω ∧ ω < 2) ∧
      (0 < ω → ω < 2 → ∀ e ≠ 0,
        (A *ᵥ ((sorSplitting A hA.diagPart.isUnit hω).iterationOperator *ᵥ e)) ⬝ᵥ
            ((sorSplitting A hA.diagPart.isUnit hω).iterationOperator *ᵥ e) <
          (A *ᵥ e) ⬝ᵥ e) := by
  have h := hA.diagPart.isUnit
  refine ⟨?_, fun hω0 hω2 e he => ?_⟩
  · simp only [sorSweep_eq_mulVecStep A h hω]
    rw [Splitting.forall_tendsto_iff, sorSplitting_complexSpectralRadius_lt_one_iff hA h hω]
  · exact Splitting.energyNorm_mulVec_iterationOperator_lt _ hA
      (sorSplitting_m_add_transpose_sub_posDef hA.1 (fun i => hA.diag_pos) h hω0 hω2) he

/-- **Property 4.3, last sentence.** If `A` is strictly diagonally dominant by rows, the SOR method
converges if `0 < ω ≤ 1` (backbone `Matrix.sorSplitting_complexSpectralRadius_lt_one_of_le_one`). -/
theorem property_4_3_diagDominant (hA : A.IsStrictDiagDominant) {ω : ℝ} (hω0 : 0 < ω)
    (hω1 : ω ≤ 1) (b x₀ : Fin n → ℝ) :
    Tendsto (fun k => (sorSweep A ω b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b)) := by
  rw [sorSweep_eq_mulVecStep A hA.isUnit_diagPart hω0.ne' b]
  exact Splitting.tendsto _ (sorSplitting_complexSpectralRadius_lt_one_of_le_one hA _ hω0 hω1) b x₀

/-- The real Jacobi matrix has real eigenvalues, in the backbone's form, iff its complexification
has. -/
private theorem forall_im_eq_zero_iff (h : IsUnit (diagPart A)) :
    (∀ μ ∈ spectrum ℂ (complexify (jacobiSplitting A h).iterationOperator), μ.im = 0) ↔
      ∀ μ ∈ spectrum ℂ
        (jacobiSplitting (complexify A) (isUnit_diagPart_complexify h)).iterationOperator,
        μ.im = 0 := by
  rw [complexify_jacobi_iterationOperator A h]

/-- The spectral radius of the real SOR matrix `B(ω)` is that of the complexified one. -/
private theorem complexSpectralRadius_sorIterationMatrix (ω : ℝ) :
    complexSpectralRadius (sorIterationMatrix A ω) =
      spectralRadius ℂ (sorIterationMatrix (complexify A) ω) := by
  rw [complexSpectralRadius, complexify_sorIterationMatrix]

/-- **Property 4.4, the equivalence.** If `A` enjoys the `A`-property (only its
consistently-ordered clause is used), its diagonal is nonzero and `B_J` has real eigenvalues, then
for `ω ≠ 0` the SOR method converges for every `b` and `x⁽⁰⁾` iff `ρ(B_J) < 1` and `0 < ω < 2`.
Young's theory (backbone `Matrix.IsConsistentlyOrdered.spectralRadius_sor_lt_one`,
`Matrix.IsConsistentlyOrdered.spectralRadius_jacobi_lt_one_of_sor`) and Kahan's condition, through
Theorem 4.1. -/
theorem property_4_4 [NeZero n] (hP : definition_4_3 A) (h : IsUnit (diagPart A))
    (hreal : ∀ μ ∈ spectrum ℂ (complexify (jacobiSplitting A h).iterationOperator), μ.im = 0)
    {ω : ℝ} (hω : ω ≠ 0) :
    (∀ b x₀, Tendsto (fun k => (sorSweep A ω b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b))) ↔
      complexSpectralRadius (jacobiSplitting A h).iterationOperator < 1 ∧ 0 < ω ∧ ω < 2 := by
  have hreal' := (forall_im_eq_zero_iff h).mp hreal
  have hJ := (complexSpectralRadius_jacobi_gaussSeidel h).1
  have hS : complexSpectralRadius (sorSplitting A h hω).iterationOperator =
      spectralRadius ℂ (sorIterationMatrix (complexify A) ω) := by
    rw [sorSplitting_iterationOperator_eq A h hω, complexSpectralRadius_sorIterationMatrix]
  simp only [sorSweep_eq_mulVecStep A h hω]
  rw [Splitting.forall_tendsto_iff]
  constructor
  · intro hρ
    obtain ⟨hω0, hω2⟩ := lt_two_of_sorSplitting_complexSpectralRadius_lt_one h hω hρ
    rw [hS] at hρ
    refine ⟨?_, hω0, hω2⟩
    rw [hJ]
    exact hP.1.spectralRadius_jacobi_lt_one_of_sor _ hreal' hω0 hω2 hρ
  · rintro ⟨hlt, hω0, hω2⟩
    rw [hS]
    rw [hJ] at hlt
    exact hP.1.spectralRadius_sor_lt_one _ hreal' hlt hω0 hω2

/-- **Property 4.4, (4.19) and the optimal spectral radius.** Under the hypotheses of
`property_4_4` with `ρ_J = ρ(B_J) < 1`, the relaxation parameter
`ω_opt = 2 / (1 + √(1 - ρ_J²))` minimizes `ρ(B(ω))` over `0 < ω < 2`, and the corresponding
asymptotic convergence factor is `ρ(B(ω_opt)) = (1 - √(1 - ρ_J²)) / (1 + √(1 - ρ_J²))`
(`= ω_opt - 1`). Backbone `Matrix.IsConsistentlyOrdered.isMinOn_complexSpectralRadius_sor` and
`Matrix.IsConsistentlyOrdered.spectralRadius_sor_optimalRelaxation`, with `B(ω)` the SOR matrix
`Matrix.sorIterationMatrix A ω` of (4.17). -/
theorem property_4_4_optimal [NeZero n] (hP : definition_4_3 A) (h : IsUnit (diagPart A))
    (hreal : ∀ μ ∈ spectrum ℂ (complexify (jacobiSplitting A h).iterationOperator), μ.im = 0)
    (hlt : complexSpectralRadius (jacobiSplitting A h).iterationOperator < 1) :
    IsMinOn (fun ω : ℝ => complexSpectralRadius (sorIterationMatrix A ω)) (Set.Ioo 0 2)
        (2 / (1 + √(1 -
          (complexSpectralRadius (jacobiSplitting A h).iterationOperator).toReal ^ 2))) ∧
      complexSpectralRadius (sorIterationMatrix A (2 / (1 + √(1 -
          (complexSpectralRadius (jacobiSplitting A h).iterationOperator).toReal ^ 2)))) =
        ENNReal.ofReal
          ((1 - √(1 - (complexSpectralRadius (jacobiSplitting A h).iterationOperator).toReal ^ 2))
            / (1 + √(1 -
              (complexSpectralRadius (jacobiSplitting A h).iterationOperator).toReal ^ 2))) := by
  have hreal' := (forall_im_eq_zero_iff h).mp hreal
  have hJ := (complexSpectralRadius_jacobi_gaussSeidel h).1
  rw [hJ] at hlt ⊢
  set r := (spectralRadius ℂ
    (jacobiSplitting (complexify A) (isUnit_diagPart_complexify h)).iterationOperator).toReal
    with hr
  have hopt : (2 / (1 + √(1 - r ^ 2))) = optimalRelaxation r := rfl
  simp only [complexSpectralRadius_sorIterationMatrix, hopt]
  refine ⟨hP.1.isMinOn_complexSpectralRadius_sor _ hreal' hlt, ?_⟩
  rw [hP.1.spectralRadius_sor_optimalRelaxation _ hreal' hlt]
  congr 1
  have hs : 0 ≤ √(1 - r ^ 2) := Real.sqrt_nonneg _
  rw [optimalRelaxation]
  field_simp
  ring

end Relaxation

/-! ### §4.2.4 A priori forward analysis: Example 4.3 and the rounding-error decomposition -/

section Forward

/-- **Example 4.3, the matrix**: the lower bidiagonal matrix of order `m` with `a_ii = 3/2` and
`a_{i,i-1} = 1` (the book takes `m = 100`). -/
noncomputable def example_4_3_matrix (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => if i = j then 3 / 2 else if (j : ℕ) + 1 = i then 1 else 0

/-- Row `i` of Example 4.3's matrix splits into its diagonal and its subdiagonal entry. -/
private theorem example_4_3_matrix_apply (m : ℕ) (i j : Fin m) :
    example_4_3_matrix m i j =
      (if i = j then 3 / 2 else 0) + (if (j : ℕ) + 1 = i then 1 else 0) := by
  simp only [example_4_3_matrix, of_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij]

/-- Example 4.3's system, for every order: `A x = b` with `b_i = 5/2` and
`x_i = 1 - (-2/3)^i` (`1`-based). -/
private theorem example_4_3_mulVec (m : ℕ) :
    example_4_3_matrix m *ᵥ (fun i : Fin m => 1 - (-2 / 3 : ℝ) ^ ((i : ℕ) + 1)) =
      fun _ => 5 / 2 := by
  funext i
  simp only [mulVec, dotProduct, example_4_3_matrix_apply, add_mul, sum_add_distrib, ite_mul,
    zero_mul, one_mul, sum_ite_eq, mem_univ, ite_true]
  rcases i with ⟨i, hi⟩
  cases i with
  | zero =>
    rw [sum_eq_zero fun j _ => by simp]
    norm_num
  | succ k =>
    rw [sum_eq_single ⟨k, by omega⟩]
    · simp only [ite_true]
      ring
    · intro j _ hj
      split_ifs with hjk
      · exact absurd (Fin.ext (by simpa using hjk)) hj
      · rfl
    · intro habs
      exact absurd (mem_univ _) habs

/-- **Example 4.3, the exact solution.** For the lower bidiagonal `A ∈ ℝ^{100×100}` with
`a_ii = 3/2`, `a_{i,i-1} = 1` and the right-hand side `b_i = 5/2`, the solution of `A x = b` has
components `x_i = 1 - (-2/3)^i` (`1`-based; the `0`-based `x_i = 1 - (-2/3)^{i+1}`). The
divergence of Program 16 in floating point is a numerical experiment and is not formalized. -/
theorem example_4_3_solution :
    example_4_3_matrix 100 *ᵥ (fun i : Fin 100 => 1 - (-2 / 3 : ℝ) ^ ((i : ℕ) + 1)) =
      fun _ => 5 / 2 :=
  example_4_3_mulVec 100

/-- Example 4.3's matrix is lower triangular. -/
private theorem example_4_3_matrix_isLowerTriangular (m : ℕ) :
    (example_4_3_matrix m).IsLowerTriangular := by
  intro i j hij
  have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
  have h1 : i ≠ j := hij'.ne
  have h2 : (j : ℕ) + 1 ≠ i := by
    have := Fin.lt_def.mp hij'
    omega
  simp [example_4_3_matrix, h1, h2]

/-- Example 4.3's matrix has an invertible diagonal. -/
private theorem example_4_3_matrix_isUnit_diagPart (m : ℕ) :
    IsUnit (diagPart (example_4_3_matrix m)) :=
  (isUnit_diagPart_iff _).mpr fun i => by simp [example_4_3_matrix]

/-- **Example 4.3, `ρ(B(3/2)) = 0.5`.** For the lower bidiagonal matrix of the example the SOR
method with `ω = 3/2` "should be convergent, working in exact arithmetic, since
`ρ(B(1.5)) = 0.5`": the matrix is lower triangular, so `ρ(B(ω)) = |1 - ω|` for every `ω`
(backbone `Matrix.complexSpectralRadius_sorSplitting_of_isLowerTriangular`). -/
theorem example_4_3_spectralRadius :
    complexSpectralRadius (sorSplitting (example_4_3_matrix 100)
        (example_4_3_matrix_isUnit_diagPart 100) (by norm_num : (3 / 2 : ℝ) ≠ 0)).iterationOperator
      = ENNReal.ofReal (1 / 2) := by
  rw [complexSpectralRadius_sorSplitting_of_isLowerTriangular
    (example_4_3_matrix_isLowerTriangular 100)]
  norm_num

/-- **(4.20), the computed sequence.** The iteration (4.6) run in finite arithmetic produces
`x̂⁽⁰⁾ = x⁽⁰⁾` and `P x̂⁽ᵏ⁺¹⁾ = N x̂⁽ᵏ⁾ + b - ζ_k`, the vector `ζ_k` collecting the rounding errors
of step `k`; it is the backbone's `Stationary.forcedIterate` with forcing `P⁻¹ b - P⁻¹ ζ_k`
(`toLp_perturbedIterate`). -/
noncomputable def perturbedIterate (s : Splitting A) (b : Fin n → ℝ) (ζ : ℕ → Fin n → ℝ)
    (x₀ : Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0 => x₀
  | k + 1 => s.m⁻¹ *ᵥ (s.n *ᵥ perturbedIterate s b ζ x₀ k + b - ζ k)

/-- Under `WithLp.toLp 2`, the computed sequence (4.20) is the forced iteration
`Stationary.forcedIterate` of `B = P⁻¹ N` with forcing terms `P⁻¹ b - P⁻¹ ζ_k`. -/
theorem toLp_perturbedIterate (s : Splitting A) (b : Fin n → ℝ) (ζ : ℕ → Fin n → ℝ)
    (x₀ : Fin n → ℝ) (k : ℕ) :
    (toLp 2 (perturbedIterate s b ζ x₀ k) : EuclideanSpace ℝ (Fin n)) =
      Stationary.forcedIterate (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) s.iterationOperator)
        (fun j => toLp 2 (s.m⁻¹ *ᵥ b) - toLp 2 (s.m⁻¹ *ᵥ ζ j)) (toLp 2 x₀) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Stationary.forcedIterate_succ, ← ih, perturbedIterate, toEuclideanCLM_toLp, ← toLp_sub,
      ← toLp_add, mulVec_sub, mulVec_add, mulVec_mulVec, s.iterationOperator_eq,
      nonsing_inv_eq_ringInverse, add_sub_assoc]

/-- **§4.2.4, the closed form of the computed sequence**:
`x̂⁽ᵏ⁺¹⁾ = Bᵏ⁺¹ x⁽⁰⁾ + ∑_{j=0}^{k} Bʲ P⁻¹ (b - ζ_{k-j})` (backbone
`Stationary.forcedIterate_eq`). -/
theorem equation_4_20_iterate (s : Splitting A) (b : Fin n → ℝ) (ζ : ℕ → Fin n → ℝ)
    (x₀ : Fin n → ℝ) (k : ℕ) :
    perturbedIterate s b ζ x₀ (k + 1) =
      (s.iterationOperator ^ (k + 1)) *ᵥ x₀ +
        ∑ j ∈ range (k + 1), (s.iterationOperator ^ j) *ᵥ (s.m⁻¹ *ᵥ (b - ζ (k - j))) := by
  have h := Stationary.forcedIterate_eq (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) s.iterationOperator)
    (fun j => toLp 2 (s.m⁻¹ *ᵥ b) - toLp 2 (s.m⁻¹ *ᵥ ζ j)) (toLp 2 x₀) (k + 1)
  rw [← toLp_perturbedIterate] at h
  simp only [Nat.add_sub_cancel, ← toLp_sub, ← mulVec_sub, ← map_pow, toEuclideanCLM_toLp,
    ← toLp_sum, ← toLp_add] at h
  exact toLp_injective 2 h

/-- **(4.20), the error decomposition of §4.2.4.** For the computed sequence with rounding errors
`ζ_k`, the absolute error `ê⁽ᵏ⁺¹⁾ = x - x̂⁽ᵏ⁺¹⁾`, with `x = A⁻¹ b`, is
`ê⁽ᵏ⁺¹⁾ = Bᵏ⁺¹ e⁽⁰⁾ + ∑_{j=0}^{k} Bʲ P⁻¹ ζ_{k-j}`: the first term is the error of the exact method,
negligible for large `k` when it converges, the second the propagated rounding error, whose
analysis the book leaves to [Hig88] (`equation_4_20_bound` is its simplest form). Backbone
`Stationary.sub_forcedIterate_eq`. -/
theorem equation_4_20 (s : Splitting A) (hA : IsUnit A) (b : Fin n → ℝ) (ζ : ℕ → Fin n → ℝ)
    (x₀ : Fin n → ℝ) (k : ℕ) :
    A⁻¹ *ᵥ b - perturbedIterate s b ζ x₀ (k + 1) =
      (s.iterationOperator ^ (k + 1)) *ᵥ (A⁻¹ *ᵥ b - x₀) +
        ∑ j ∈ range (k + 1), (s.iterationOperator ^ j) *ᵥ (s.m⁻¹ *ᵥ ζ (k - j)) := by
  have hfix : toEuclideanCLM (n := Fin n) (𝕜 := ℝ) s.iterationOperator (toLp 2 (A⁻¹ *ᵥ b)) +
      toLp 2 (s.m⁻¹ *ᵥ b) = (toLp 2 (A⁻¹ *ᵥ b) : EuclideanSpace ℝ (Fin n)) := by
    rw [toEuclideanCLM_toLp, ← toLp_add, ← s.consistent hA b]
  have h := Stationary.sub_forcedIterate_eq
    (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) s.iterationOperator) (toLp 2 (s.m⁻¹ *ᵥ b)) hfix
    (fun j => toLp 2 (s.m⁻¹ *ᵥ ζ j)) (toLp 2 x₀) k
  rw [← toLp_perturbedIterate] at h
  simp only [← toLp_sub, ← map_pow, toEuclideanCLM_toLp, ← toLp_sum, ← toLp_add] at h
  exact toLp_injective 2 h

open scoped Matrix.Norms.L2Operator in
/-- **The rounding-error term of (4.20), bounded** (the analysis the book cites from [Hig88], in
its simplest form): if `‖B‖₂ < 1` and `‖P⁻¹ ζ_k‖₂ ≤ ε` for all `k`, then
`‖x̂⁽ᵏ⁾ - x‖₂ ≤ ‖B‖₂ᵏ ‖x⁽⁰⁾ - x‖₂ + ε / (1 - ‖B‖₂)`: the exact-arithmetic error plus a floor
proportional to the rounding errors (backbone `Stationary.norm_perturbed_iterate_sub_le`). -/
theorem equation_4_20_bound (s : Splitting A) (hA : IsUnit A) (hB : ‖s.iterationOperator‖ < 1)
    (b : Fin n → ℝ) {ζ : ℕ → Fin n → ℝ} {ε : ℝ}
    (hζ : ∀ k, ‖(toLp 2 (s.m⁻¹ *ᵥ ζ k) : EuclideanSpace ℝ (Fin n))‖ ≤ ε) (x₀ : Fin n → ℝ)
    (k : ℕ) :
    ‖(toLp 2 (perturbedIterate s b ζ x₀ k - A⁻¹ *ᵥ b) : EuclideanSpace ℝ (Fin n))‖ ≤
      ‖s.iterationOperator‖ ^ k * ‖(toLp 2 (x₀ - A⁻¹ *ᵥ b) : EuclideanSpace ℝ (Fin n))‖ +
        ε / (1 - ‖s.iterationOperator‖) := by
  have hfix : toEuclideanCLM (n := Fin n) (𝕜 := ℝ) s.iterationOperator (toLp 2 (A⁻¹ *ᵥ b)) +
      toLp 2 (s.m⁻¹ *ᵥ b) = (toLp 2 (A⁻¹ *ᵥ b) : EuclideanSpace ℝ (Fin n)) := by
    rw [toEuclideanCLM_toLp, ← toLp_add, ← s.consistent hA b]
  have hstep : ∀ j, (toLp 2 (perturbedIterate s b ζ x₀ (j + 1)) : EuclideanSpace ℝ (Fin n)) =
      toEuclideanCLM (n := Fin n) (𝕜 := ℝ) s.iterationOperator
          (toLp 2 (perturbedIterate s b ζ x₀ j)) +
        toLp 2 (s.m⁻¹ *ᵥ b) + -toLp 2 (s.m⁻¹ *ᵥ ζ j) := by
    intro j
    rw [toLp_perturbedIterate, toLp_perturbedIterate, Stationary.forcedIterate_succ,
      sub_eq_add_neg, add_assoc]
  have hξ : ∀ j, ‖(-toLp 2 (s.m⁻¹ *ᵥ ζ j) : EuclideanSpace ℝ (Fin n))‖ ≤ ε := fun j => by
    rw [norm_neg]
    exact hζ j
  have hG : ‖toEuclideanCLM (n := Fin n) (𝕜 := ℝ) s.iterationOperator‖ < 1 := by
    rwa [l2_opNorm_toEuclideanCLM]
  have h := Stationary.norm_perturbed_iterate_sub_le
    (x := fun j => toLp 2 (perturbedIterate s b ζ x₀ j)) hstep hξ hG hfix k
  rwa [l2_opNorm_toEuclideanCLM, ← toLp_sub, ← toLp_sub, perturbedIterate] at h

end Forward

/-! ### §4.2.5 Block matrices -/

section Block

variable {ι : Type*} [LinearOrder ι]

/-- The block diagonal part of a symmetric matrix is symmetric. -/
private theorem blockDiagPart_transpose_of_isHermitian (π : Fin n → ι) (hA : A.IsHermitian) :
    (blockDiagPart π A)ᵀ = blockDiagPart π A := by
  have hsymm : ∀ i j, A j i = A i j := fun i j => by
    simpa using congrFun (congrFun hA.eq i) j
  ext i j
  rw [transpose_apply, blockDiagPart_apply, blockDiagPart_apply, hsymm]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · rfl

/-- **§4.2.5, "Theorem 4.3 is still valid provided `D` is substituted by the block diagonal
matrix"**: for a block labelling `π` of the indices, if `A` is symmetric positive definite, the
diagonal blocks are nonsingular and `2D - A` is positive definite for the block diagonal part
`D = blockDiagPart π A`, then the block Jacobi method `P = D`, `N = D - A`
(`Matrix.blockJacobiSplitting`) converges for every `b` and `x⁽⁰⁾`. Householder–John with
`M = D` symmetric. The block Gauss–Seidel and block SOR methods "introduced in a similar manner"
are `Matrix.blockGaussSeidelSplitting` and `Matrix.blockSORSplitting` of the backbone. -/
theorem theorem_4_3_block (π : Fin n → ι) (hA : A.PosDef) (h : IsUnit (blockDiagPart π A))
    (h2 : (2 • blockDiagPart π A - A).PosDef) (b x₀ : Fin n → ℝ) :
    Tendsto (fun k => ((blockJacobiSplitting π A h).mulVecStep b)^[k] x₀) atTop
      (𝓝 (A⁻¹ *ᵥ b)) := by
  refine Splitting.tendsto _ (Splitting.complexSpectralRadius_lt_one_of_posDef _ hA ?_) b x₀
  have hm : (blockJacobiSplitting π A h).m = blockDiagPart π A := rfl
  rw [hm, blockDiagPart_transpose_of_isHermitian π hA.1, ← two_smul ℕ]
  exact h2

end Block

/-! ### §4.2.6 Symmetric form of the Gauss–Seidel and SOR methods -/

section Symmetric

/-- Two steps of (4.2) compose into one: `B₂ (B₁ x + f₁) + f₂ = (B₂ B₁) x + (B₂ f₁ + f₂)`. -/
private theorem affineStep_affineStep (B₁ B₂ : Matrix (Fin n) (Fin n) ℝ) (f₁ f₂ x : Fin n → ℝ) :
    affineStep B₂ f₂ (affineStep B₁ f₁ x) = affineStep (B₂ * B₁) (B₂ *ᵥ f₁ + f₂) x := by
  simp only [affineStep, mulVec_add, mulVec_mulVec, add_assoc]

/-- **§4.2.6, the backward Gauss–Seidel method** `(D - F) x⁽ᵏ⁺¹⁾ = E x⁽ᵏ⁾ + b`, obtained by
exchanging `E` with `F`: its sweep computes `y_i = (b_i - ∑_{j > i} a_ij y_j - ∑_{j < i} a_ij x_j)
/ a_ii` (backbone `Matrix.backwardSorSweep_apply`), it is the step of the splitting `P = D - F`,
`N = E` (`Matrix.backwardGaussSeidelSplitting`), and its iteration matrix is
`B_GSb = (D - F)⁻¹ E`. -/
theorem backwardGaussSeidel_step (h : IsUnit (diagPart A)) (b x : Fin n → ℝ) :
    (∀ i, backwardSorSweep A 1 b x i =
        (b i - ∑ j ∈ univ.filter (i < ·), A i j * backwardSorSweep A 1 b x j
          - ∑ j ∈ univ.filter (· < i), A i j * x j) / A i i) ∧
      backwardSorSweep A 1 b x = (backwardGaussSeidelSplitting A h).mulVecStep b x ∧
      (backwardGaussSeidelSplitting A h).m = D A - F A ∧
      (backwardGaussSeidelSplitting A h).n = E A ∧
      (D A - F A) *ᵥ backwardSorSweep A 1 b x = E A *ᵥ x + b ∧
      (backwardGaussSeidelSplitting A h).iterationOperator = (D A - F A)⁻¹ * E A := by
  have hm : (backwardGaussSeidelSplitting A h).m = D A - F A := by
    rw [D_sub_F]
    rfl
  have hn : (backwardGaussSeidelSplitting A h).n = E A := by
    change diagPart A + strictUpper A - A = -strictLower A
    rw [eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, add_right_comm,
      diagPart_add_strictLower_add_strictUpper, sub_self]
  have hstep := congrFun (backwardSorSweep_one_eq_mulVecStep A h b) x
  refine ⟨fun i => ?_, hstep, hm, hn, ?_, ?_⟩
  · rw [backwardSorSweep_apply A h 1 b x i, sub_self, zero_mul, add_zero, div_mul_eq_mul_div,
      one_mul]
  · rw [hstep, ← hm, ← hn]
    exact mulVec_nonsing_inv_mulVec (backwardGaussSeidelSplitting A h).isUnit _
  · rw [Splitting.iterationOperator_eq, hm, hn, nonsing_inv_eq_ringInverse]

/-- The Gauss–Seidel sweep as a step of (4.2), in the letters of the book. -/
private theorem sorSweep_one_eq_affineStep (h : IsUnit (diagPart A)) (b x : Fin n → ℝ) :
    sorSweep A 1 b x = affineStep ((D A - E A)⁻¹ * F A) ((D A - E A)⁻¹ *ᵥ b) x := by
  obtain ⟨-, h1, h2, -, h3⟩ := equation_4_13 h b x
  rw [h1, Splitting.mulVecStep_eq_iterationOperator_mulVec_add, h2, h3]
  rfl

/-- The backward Gauss–Seidel sweep as a step of (4.2), in the letters of the book. -/
private theorem backwardSorSweep_one_eq_affineStep (h : IsUnit (diagPart A)) (b x : Fin n → ℝ) :
    backwardSorSweep A 1 b x = affineStep ((D A - F A)⁻¹ * E A) ((D A - F A)⁻¹ *ᵥ b) x := by
  obtain ⟨-, h1, h2, -, -, h3⟩ := backwardGaussSeidel_step h b x
  rw [h1, Splitting.mulVecStep_eq_iterationOperator_mulVec_add, h2, h3]
  rfl

/-- **(4.21), the symmetric Gauss–Seidel method.** One Gauss–Seidel step followed by one backward
Gauss–Seidel step, `(D - E) x⁽ᵏ⁺¹ᐟ²⁾ = F x⁽ᵏ⁾ + b`, `(D - F) x⁽ᵏ⁺¹⁾ = E x⁽ᵏ⁺¹ᐟ²⁾ + b`, is the
iteration `x⁽ᵏ⁺¹⁾ = B_SGS x⁽ᵏ⁾ + b_SGS` with `B_SGS = (D - F)⁻¹ E (D - E)⁻¹ F` and
`b_SGS = (D - F)⁻¹ [E (D - E)⁻¹ + I] b`; its preconditioning matrix is
`P_SGS = (D - E) D⁻¹ (D - F)`, that is, the composite step is the step of the SSOR splitting at
`ω = 1` (backbone `Matrix.ssorSplitting_iterationOperator_eq_mul`, `Matrix.ssorSplitting_one_m`,
`Matrix.ssorSweep_eq_mulVecStep`). -/
theorem equation_4_21 (h : IsUnit (diagPart A)) (b x : Fin n → ℝ) :
    backwardSorSweep A 1 b (sorSweep A 1 b x) =
        affineStep ((D A - F A)⁻¹ * E A * (D A - E A)⁻¹ * F A)
          ((D A - F A)⁻¹ *ᵥ ((E A * (D A - E A)⁻¹ + 1) *ᵥ b)) x ∧
      (ssorSplitting A h one_ne_zero one_lt_two.ne).iterationOperator =
        (D A - F A)⁻¹ * E A * (D A - E A)⁻¹ * F A ∧
      (ssorSplitting A h one_ne_zero one_lt_two.ne).m = (D A - E A) * (D A)⁻¹ * (D A - F A) ∧
      backwardSorSweep A 1 b (sorSweep A 1 b x) =
        (ssorSplitting A h one_ne_zero one_lt_two.ne).mulVecStep b x := by
  refine ⟨?_, ?_, ?_, ssorSweep_eq_mulVecStep A h one_ne_zero one_lt_two.ne b x⟩
  · rw [sorSweep_one_eq_affineStep h, backwardSorSweep_one_eq_affineStep h, affineStep_affineStep]
    congr 1
    · simp only [Matrix.mul_assoc]
    · rw [add_mulVec, one_mulVec, mulVec_add, ← mulVec_mulVec, ← mulVec_mulVec]
  · rw [ssorSplitting_iterationOperator_eq_mul, backwardSorSplitting_one, sorSplitting_one,
      (equation_4_13 h b x).2.2.2.2, (backwardGaussSeidel_step h b x).2.2.2.2.2]
    simp only [Matrix.mul_assoc]
  · rw [ssorSplitting_one_m, D_sub_E, D_sub_F, D]

/-- **Property 4.5.** If `A` is symmetric positive definite, the symmetric Gauss–Seidel method
converges (for every `b` and `x⁽⁰⁾`), and `B_SGS` is self-adjoint and positive semidefinite in
the `A`-inner product: `A B_SGS` is symmetric positive semidefinite. The printed "`B_SGS` is
symmetric positive definite" is false (for a diagonal `A`, `B_SGS = 0`); what its source proves is
this, since `B_SGS = I - P_SGS⁻¹ A` with `P_SGS` symmetric and `P_SGS - A = E D⁻¹ F ≥ 0`, whence the
eigenvalues of `B_SGS` lie in `[0, 1)`. Backbone `Matrix.ssorSplitting_complexSpectralRadius_lt_one`
and `Matrix.ssorSplitting_iterationOperator_posSemidef_energy` at `ω = 1`. -/
theorem property_4_5 (hA : A.PosDef) :
    (∀ b x₀, Tendsto (fun k => (fun y => backwardSorSweep A 1 b (sorSweep A 1 b y))^[k] x₀) atTop
        (𝓝 (A⁻¹ *ᵥ b))) ∧
      (A * ((D A - F A)⁻¹ * E A * (D A - E A)⁻¹ * F A)).IsSymm ∧
      (A * ((D A - F A)⁻¹ * E A * (D A - E A)⁻¹ * F A)).PosSemidef := by
  have h := hA.diagPart.isUnit
  have hB := (equation_4_21 h 0 0).2.1
  have hpsd := ssorSplitting_iterationOperator_posSemidef_energy hA h one_pos one_lt_two
  rw [hB] at hpsd
  refine ⟨fun b x₀ => ?_, isHermitian_iff_isSymm.mp hpsd.1, hpsd⟩
  have hsweep : (fun y => backwardSorSweep A 1 b (sorSweep A 1 b y)) =
      (ssorSplitting A h one_ne_zero one_lt_two.ne).mulVecStep b :=
    funext fun y => ssorSweep_eq_mulVecStep A h one_ne_zero one_lt_two.ne b y
  rw [hsweep]
  exact Splitting.tendsto _ (ssorSplitting_complexSpectralRadius_lt_one hA h one_pos one_lt_two)
    b x₀

/-- The SOR sweep as a step of (4.2), in the letters of the book:
`B(ω) = (D - ωE)⁻¹ (ωF + (1 - ω) D)`, `f = ω (D - ωE)⁻¹ b`. -/
private theorem sorSweep_eq_affineStep (h : IsUnit (diagPart A)) {ω : ℝ} (hω : ω ≠ 0)
    (b x : Fin n → ℝ) :
    sorSweep A ω b x = affineStep ((D A - ω • E A)⁻¹ * (ω • F A + (1 - ω) • D A))
      (ω • ((D A - ω • E A)⁻¹ *ᵥ b)) x := by
  rw [(equation_4_15 h hω b x).2, Splitting.mulVecStep_eq_iterationOperator_mulVec_add,
    sorSplitting_iterationOperator, D_sub_smul_E, F, smul_neg, neg_add_eq_sub, D]
  have hm : (sorSplitting A h hω).m = ω⁻¹ • (diagPart A + ω • strictLower A) := by
    change ω⁻¹ • diagPart A + strictLower A = _
    rw [smul_add, smul_smul, inv_mul_cancel₀ hω, one_smul]
  rw [hm, inv_smul_of_isUnit (inv_ne_zero hω) (isUnit_diagPart_add_smul_strictLower h ω), inv_inv,
    smul_mulVec]
  rfl

/-- The backward SOR sweep as a step of (4.2), in the letters of the book:
`(D - ωF)⁻¹ (ωE + (1 - ω) D)`, `f = ω (D - ωF)⁻¹ b`. -/
private theorem backwardSorSweep_eq_affineStep (h : IsUnit (diagPart A)) {ω : ℝ} (hω : ω ≠ 0)
    (b x : Fin n → ℝ) :
    backwardSorSweep A ω b x = affineStep ((D A - ω • F A)⁻¹ * (ω • E A + (1 - ω) • D A))
      (ω • ((D A - ω • F A)⁻¹ *ᵥ b)) x := by
  rw [congrFun (backwardSorSweep_eq_mulVecStep A h hω b) x,
    Splitting.mulVecStep_eq_iterationOperator_mulVec_add, backwardSorSplitting_iterationOperator,
    D_sub_smul_F, E, smul_neg, neg_add_eq_sub, D]
  have hm : (backwardSorSplitting A h hω).m = ω⁻¹ • (diagPart A + ω • strictUpper A) := by
    change ω⁻¹ • diagPart A + strictUpper A = _
    rw [smul_add, smul_smul, inv_mul_cancel₀ hω, one_smul]
  rw [hm, inv_smul_of_isUnit (inv_ne_zero hω) (isUnit_diagPart_add_smul_strictUpper h ω), inv_inv,
    smul_mulVec]
  rfl

/-- `(ωE + (1 - ω) D) (D - ωE)⁻¹ + I = (2 - ω) D (D - ωE)⁻¹`: the identity behind `b_ω`. -/
private theorem smul_E_add_smul_D_mul_inv_add_one (h : IsUnit (diagPart A)) (ω : ℝ) :
    (ω • E A + (1 - ω) • D A) * (D A - ω • E A)⁻¹ + 1 = (2 - ω) • (D A * (D A - ω • E A)⁻¹) := by
  have hu : IsUnit (D A - ω • E A) := by
    rw [D_sub_smul_E]
    exact isUnit_diagPart_add_smul_strictLower h ω
  rw [← mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hu), ← add_mul, ← Matrix.smul_mul]
  congr 1
  module

/-- **(4.22), the SSOR method.** One SOR step followed by one backward SOR step
`(D - ωF) x⁽ᵏ⁺¹⁾ = [ωE + (1 - ω) D] x⁽ᵏ⁾ + ωb` is the iteration `x⁽ᵏ⁺¹⁾ = B_s(ω) x⁽ᵏ⁾ + b_ω` with
`B_s(ω) = (D - ωF)⁻¹ (ωE + (1 - ω) D) (D - ωE)⁻¹ (ωF + (1 - ω) D)` and
`b_ω = ω (2 - ω) (D - ωF)⁻¹ D (D - ωE)⁻¹ b`; its preconditioning matrix is
`P_SSOR(ω) = (ω⁻¹ D - E) (ω / (2 - ω)) D⁻¹ (ω⁻¹ D - F)` (4.22), that is, the composite step is the
step of `Matrix.ssorSplitting` (backbone `Matrix.ssorSplitting_iterationOperator_eq_mul`,
`Matrix.ssorSweep_eq_mulVecStep`). -/
theorem equation_4_22 (h : IsUnit (diagPart A)) {ω : ℝ} (hω : ω ≠ 0) (hω2 : ω ≠ 2)
    (b x : Fin n → ℝ) :
    backwardSorSweep A ω b (sorSweep A ω b x) =
        affineStep ((D A - ω • F A)⁻¹ * (ω • E A + (1 - ω) • D A) * (D A - ω • E A)⁻¹ *
            (ω • F A + (1 - ω) • D A))
          ((ω * (2 - ω)) • ((D A - ω • F A)⁻¹ *ᵥ (D A *ᵥ ((D A - ω • E A)⁻¹ *ᵥ b)))) x ∧
      (ssorSplitting A h hω hω2).iterationOperator =
        (D A - ω • F A)⁻¹ * (ω • E A + (1 - ω) • D A) * (D A - ω • E A)⁻¹ *
          (ω • F A + (1 - ω) • D A) ∧
      (ssorSplitting A h hω hω2).m =
        (ω⁻¹ • D A - E A) * ((ω / (2 - ω)) • (D A)⁻¹) * (ω⁻¹ • D A - F A) ∧
      backwardSorSweep A ω b (sorSweep A ω b x) = (ssorSplitting A h hω hω2).mulVecStep b x := by
  refine ⟨?_, ?_, ?_, ssorSweep_eq_mulVecStep A h hω hω2 b x⟩
  · rw [sorSweep_eq_affineStep h hω, backwardSorSweep_eq_affineStep h hω, affineStep_affineStep]
    congr 1
    · simp only [Matrix.mul_assoc]
    · have key : (ω • E A + (1 - ω) • D A) *ᵥ ((D A - ω • E A)⁻¹ *ᵥ b) + b =
          (2 - ω) • (D A *ᵥ ((D A - ω • E A)⁻¹ *ᵥ b)) := by
        have := congrArg (· *ᵥ b) (smul_E_add_smul_D_mul_inv_add_one h ω)
        simpa only [add_mulVec, one_mulVec, ← mulVec_mulVec, smul_mulVec] using this
      rw [mulVec_smul, ← smul_add, ← mulVec_mulVec, ← mulVec_add, key, mulVec_smul, smul_smul]
  · rw [ssorSplitting_iterationOperator_eq_mul, backwardSorSplitting_iterationOperator,
      sorSplitting_iterationOperator, D_sub_smul_E, D_sub_smul_F, E, F, D, smul_neg, smul_neg,
      neg_add_eq_sub, neg_add_eq_sub]
    simp only [Matrix.mul_assoc]
  · have hD : (D A)⁻¹ = (diagPart A)⁻¹ := rfl
    rw [hD, show ω⁻¹ • D A - E A = ω⁻¹ • (diagPart A + ω • strictLower A) by
        rw [D, E, sub_neg_eq_add, smul_add, smul_smul, inv_mul_cancel₀ hω, one_smul],
      show ω⁻¹ • D A - F A = ω⁻¹ • (diagPart A + ω • strictUpper A) by
        rw [D, F, sub_neg_eq_add, smul_add, smul_smul, inv_mul_cancel₀ hω, one_smul]]
    change (ω * (2 - ω))⁻¹ • ((diagPart A + ω • strictLower A) * (diagPart A)⁻¹ *
      (diagPart A + ω • strictUpper A)) = _
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    have h2 : (2 : ℝ) - ω ≠ 0 := sub_ne_zero_of_ne hω2.symm
    field_simp

/-- **§4.2.6, "If `A` is symmetric and positive definite, the SSOR method is convergent if
`0 < ω < 2`"** (backbone `Matrix.ssorSplitting_complexSpectralRadius_lt_one`, Householder–John
for the symmetric positive definite `P_SSOR(ω)`, which dominates `A`). The comparison with SOR
and the choice of `ω` are prose. -/
theorem ssor_tendsto (hA : A.PosDef) {ω : ℝ} (hω0 : 0 < ω) (hω2 : ω < 2) (b x₀ : Fin n → ℝ) :
    Tendsto (fun k => (fun y => backwardSorSweep A ω b (sorSweep A ω b y))^[k] x₀) atTop
      (𝓝 (A⁻¹ *ᵥ b)) := by
  have h := hA.diagPart.isUnit
  have hsweep : (fun y => backwardSorSweep A ω b (sorSweep A ω b y)) =
      (ssorSplitting A h hω0.ne' hω2.ne).mulVecStep b :=
    funext fun y => ssorSweep_eq_mulVecStep A h hω0.ne' hω2.ne b y
  rw [hsweep]
  exact Splitting.tendsto _ (ssorSplitting_complexSpectralRadius_lt_one hA h hω0 hω2) b x₀

end Symmetric

end QuarteroniSaccoSaleri.Chapter04

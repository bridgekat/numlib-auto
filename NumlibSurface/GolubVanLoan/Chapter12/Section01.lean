import Numlib.Analysis.Fourier.SineCosineTransform
import Numlib.FloatingPoint.Program
import Numlib.LinearAlgebra.Matrix.Displacement
import NumlibSurface.GolubVanLoan.Chapter01.Section02

/-!
# Golub–Van Loan §12.1: linear systems with displacement structure

Surface file for §12.1 of Golub and Van Loan, *Matrix Computations* (4th edition): displacement rank
(12.1.1)–(12.1.3), Cauchy and Cauchy-like matrices (12.1.4), the generator update Theorem 12.1.1,
the fast LU Algorithms 12.1.1 (`LUdisp`) and 12.1.2 (`LUdispPiv`), Toeplitz-, Hankel- and
Toeplitz-plus-Hankel-like matrices (12.1.7)–(12.1.11), and the conversion to Cauchy-like form with
the fast eigensystems (12.1.12)–(12.1.13).

## Design

Matrices are real, `Matrix (Fin n) (Fin n) ℝ`, 0-based. The displacement `F A − A G` is chapter 7's
Sylvester operator `Matrix.sylvesterMap F G A`, and the `{F, G}`-displacement rank is
`Matrix.displacementRank F G A`; the book puts the nonsingularity of the Sylvester operator into the
definition (12.1.2), here it is a hypothesis exactly where it is used. The book's `λ` is `ν` (`λ` is
a Lean keyword). `Z_φ` is `Matrix.cyclicShift n φ`, `Y_{γ,δ}` is `Matrix.cornerTridiagonal n γ δ`.
The block partitions `A = [α gᵀ; f B]`, `R = [r₁ᵀ; R₁]` are read through `Fin.succ`.

The algorithms are monadic programs with a rounding hook `rnd` (the conventions of
`NumlibSurface/GolubVanLoan`), recursive on the size `N + 1`; their vectors are computed entry by
entry by `List.foldlM` over `List.finRange` (`vecLoop`), dot products by chapter 1's
`FloatingPoint.dotAccum`. The book analyses no rounding errors in this chapter, so there are only
exact specifications.

## Not formalized here

The non-recursive sketch of Algorithm 12.1.1, the `n = 4` Cauchy update example of §12.1.3, the
"Steps 1–4" framework of §12.1.8 beyond its correctness statement, and the flop counts.
-/

open Matrix

namespace GolubVanLoan.Chapter12

variable {n : ℕ}

/-! ### Displacement rank and Cauchy-like matrices (§12.1.1–12.1.2) -/

/-- **(12.1.3)**: if `rank_{F,G}(A) = r` there are generators `R, S ∈ ℝ^{n×r}` with `F A − A G = R
Sᵀ`. The book's precondition that the Sylvester map be nonsingular is not needed. -/
theorem equation_12_1_3 {F G A : Matrix (Fin n) (Fin n) ℝ} {r : ℕ}
    (h : displacementRank F G A = r) :
    ∃ R S : Matrix (Fin n) (Fin r) ℝ, F * A - A * G = R * Sᵀ := by
  obtain ⟨R, S, hRS⟩ := displacementRank_le_iff_exists.mp h.le
  exact ⟨R, S, hRS⟩

/-- **§12.1.2**: for `ω, ν ∈ ℝⁿ` with `ω_k ≠ ν_j` for all `k, j`, the Cauchy matrix `a_kj = 1/(ω_k −
ν_j)` satisfies `Ω A − A Λ = e eᵀ` (`Ω = diag(ω)`, `Λ = diag(ν)`, `e` the vector of ones) and has
`{Ω, Λ}`-displacement rank `1` (for `n ≥ 1`). -/
theorem cauchy_displacement {ω ν : Fin n → ℝ} (h : ∀ k j, ω k ≠ ν j) :
    diagonal ω * cauchy ω (-ν) - cauchy ω (-ν) * diagonal ν = vecMulVec 1 1 ∧
      (n ≠ 0 → displacementRank (diagonal ω) (diagonal ν) (cauchy ω (-ν)) = 1) :=
  sylvesterMap_diagonal_cauchy h

/-- **§12.1.2**, Definition: `A` is Cauchy-like with respect to `ω`, `ν` if
`diag(ω) A − A diag(ν) = R Sᵀ` for some `R, S ∈ ℝ^{n×r}` of full column rank `r` ((12.1.4); the
book's "`r ≪ n`" is informal and not part of the definition). -/
def IsCauchyLike (ω ν : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ (r : ℕ) (R S : Matrix (Fin n) (Fin r) ℝ), R.rank = r ∧ S.rank = r ∧
    diagonal ω * A - A * diagonal ν = R * Sᵀ

/-- **(12.1.4)** and the display after it: if `ω_k ≠ ν_j` for all `k, j`, then `Ω A − A Λ = R Sᵀ`
holds exactly when `a_kj = r_kᵀ s_j / (ω_k − ν_j)` (`r_k`, `s_j` the rows of `R`, `S`): a
Cauchy-like matrix is determined by `{ω, ν, R, S}`. -/
theorem equation_12_1_4 {ω ν : Fin n → ℝ} (h : ∀ k j, ω k ≠ ν j) {r : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {R S : Matrix (Fin n) (Fin r) ℝ} :
    diagonal ω * A - A * diagonal ν = R * Sᵀ ↔ ∀ k j, A k j = (R k ⬝ᵥ S j) / (ω k - ν j) :=
  apply_eq_of_sylvesterMap_diagonal_eq h

/-! ### The generator update (Theorem 12.1.1) -/

section Update

variable {N r : ℕ}

/-- **Theorem 12.1.1**: for `A ∈ ℝ^{n×n}` with `Ω A − A Λ = R Sᵀ` (12.1.5), `Ω = diag(ω)`, `Λ =
diag(ν)` with no common diagonal entries, `A = [α gᵀ; f B]`, `R = [r₁ᵀ; R₁]`, `S = [s₁ᵀ; S₁]` and `α
≠ 0`: `Ω₁ A₁ − A₁ Λ₁ = R̃₁ S̃₁ᵀ` (12.1.6) with `A₁ = B − f gᵀ/α`, `R̃₁ = R₁ − f r₁ᵀ/α`, `S̃₁ = S₁ −
g s₁ᵀ/α`, `Ω₁ = diag(ω₂, …, ω_n)`, `Λ₁ = diag(ν₂, …, ν_n)`. (The hypothesis on the diagonal entries
is kept as printed; the identity does not use it.) -/
theorem theorem_12_1_1 {ω ν : Fin (N + 1) → ℝ} (_hων : ∀ k j, ω k ≠ ν j)
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} {R S : Matrix (Fin (N + 1)) (Fin r) ℝ}
    (h : diagonal ω * A - A * diagonal ν = R * Sᵀ) (hα : A 0 0 ≠ 0) :
    diagonal (ω ∘ Fin.succ) * (A.submatrix Fin.succ Fin.succ -
        (A 0 0)⁻¹ • vecMulVec (fun i => A i.succ 0) fun j => A 0 j.succ) -
      (A.submatrix Fin.succ Fin.succ -
        (A 0 0)⁻¹ • vecMulVec (fun i => A i.succ 0) fun j => A 0 j.succ) * diagonal (ν ∘ Fin.succ) =
      (R.submatrix Fin.succ id - (A 0 0)⁻¹ • vecMulVec (fun i => A i.succ 0) (R 0)) *
        (S.submatrix Fin.succ id - (A 0 0)⁻¹ • vecMulVec (fun j => A 0 j.succ) (S 0))ᵀ :=
  sylvesterMap_diagonal_schurComplement h hα

/-- **The display after Theorem 12.1.1**: `rank_{Ω,Λ}(A) ≤ r ⇒ rank_{Ω₁,Λ₁}(A₁) ≤ r`, `A₁` being the
Schur complement of `α ≠ 0`. -/
theorem theorem_12_1_1_b {ω ν : Fin (N + 1) → ℝ} {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (h : displacementRank (diagonal ω) (diagonal ν) A ≤ r) (hα : A 0 0 ≠ 0) :
    displacementRank (diagonal (ω ∘ Fin.succ)) (diagonal (ν ∘ Fin.succ))
      (A.submatrix Fin.succ Fin.succ -
        (A 0 0)⁻¹ • vecMulVec (fun i => A i.succ 0) fun j => A 0 j.succ) ≤ r :=
  displacementRank_diagonal_schurComplement_le h hα

end Update

/-! ### Fast LU for Cauchy-like matrices (Algorithm 12.1.1) -/

section LUdisp

/-- A vector computed entry by entry, in the order of the index list `l`: the loop
`for i in l, y(i) = f(i), end` as a `List.foldlM` (entries not in `l` stay `0`). -/
def vecLoopOn {M : Type → Type} [Monad M] {β : Type} [Zero β] {k : ℕ} (l : List (Fin k))
    (f : Fin k → M β) : M (Fin k → β) :=
  l.foldlM (fun (y : Fin k → β) i => do
    let b ← f i
    pure (Function.update y i b)) 0

/-- A vector computed entry by entry, in increasing index order: the loop
`for i = 1:k, y(i) = f(i), end` as a `List.foldlM` over `List.finRange k`. -/
def vecLoop {M : Type → Type} [Monad M] {β : Type} [Zero β] {k : ℕ} (f : Fin k → M β) :
    M (Fin k → β) :=
  vecLoopOn (List.finRange k) f

/-- In exact arithmetic a loop over a duplicate-free list of all indices computes every entry. -/
theorem idRun_vecLoopOn {β : Type} [Zero β] {k : ℕ} {l : List (Fin k)} (f : Fin k → Id β)
    (hl : l.Nodup) (hall : ∀ i, i ∈ l) : Id.run (vecLoopOn l f) = fun i => Id.run (f i) := by
  funext i
  have := List.idRun_foldlM_update_apply (fun a (_ : β) => f a) l hl 0 i
  simpa [vecLoopOn, hall i] using this

/-- In exact arithmetic the loop computes every entry. -/
theorem idRun_vecLoop {β : Type} [Zero β] {k : ℕ} (f : Fin k → Id β) :
    Id.run (vecLoop f) = fun i => Id.run (f i) :=
  idRun_vecLoopOn f (List.nodup_finRange k) (List.mem_finRange)

/-- **Algorithm 12.1.1** (`LUdisp`): from `ω`, `ν ∈ ℝⁿ` and generators `R, S ∈ ℝ^{n×r}` of a
Cauchy-like `A` (`Ω A − A Λ = R Sᵀ`), the factors `L`, `U` of `A = L U`, recursively on the size `n
= N + 1`, every arithmetic result passing through the rounding hook `rnd`. For `n = 1`, `L = 1`, `U
= r₁ᵀ s₁/(ω₁ − ν₁)`; otherwise `a = (R s₁) ./ (ω − ν₁)`, `α = a₁`, `f = a(2:n)`, `g = (S₁ r₁) ./ (ω₁
− ν(2:n))`, `R̃₁ = R₁ − f r₁ᵀ/α`, `S̃₁ = S₁ − g s₁ᵀ/α`, `[L₁, U₁] = LUdisp(ω(2:n), ν(2:n), R̃₁,
S̃₁)`, and `L = [1 0; f/α L₁]`, `U = [α gᵀ; 0 U₁]`. -/
noncomputable def algorithm_12_1_1 {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) {r : ℕ} :
    (N : ℕ) → (ω ν : Fin (N + 1) → ℝ) → (R S : Matrix (Fin (N + 1)) (Fin r) ℝ) →
      M (Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ × Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
  | 0, ω, ν, R, S => do
      let t ← FloatingPoint.dotAccum rnd (List.finRange r) (R 0) (S 0) 0
      let u ← rnd (t / (← rnd (ω 0 - ν 0)))
      pure (1, of fun _ _ => u)
  | N + 1, ω, ν, R, S => do
      let a ← vecLoop fun i : Fin (N + 2) => do
        let t ← FloatingPoint.dotAccum rnd (List.finRange r) (R i) (S 0) 0
        rnd (t / (← rnd (ω i - ν 0)))
      let g ← vecLoop fun j : Fin (N + 1) => do
        let t ← FloatingPoint.dotAccum rnd (List.finRange r) (S j.succ) (R 0) 0
        rnd (t / (← rnd (ω 0 - ν j.succ)))
      let R₁ ← vecLoop fun i : Fin (N + 1) => vecLoop fun c : Fin r => do
        rnd (R i.succ c - (← rnd ((← rnd (a i.succ * R 0 c)) / a 0)))
      let S₁ ← vecLoop fun j : Fin (N + 1) => vecLoop fun c : Fin r => do
        rnd (S j.succ c - (← rnd ((← rnd (g j * S 0 c)) / a 0)))
      let LU₁ ← algorithm_12_1_1 rnd N (fun i => ω i.succ) (fun j => ν j.succ) (of R₁) (of S₁)
      let l ← vecLoop fun i : Fin (N + 1) => rnd (a i.succ / a 0)
      pure (of fun i j => Fin.cases (Fin.cases 1 (fun _ => 0) j)
          (fun i' => Fin.cases (l i') (fun j' => LU₁.1 i' j') j) i,
        of fun i j => Fin.cases (Fin.cases (a 0) g j)
          (fun i' => Fin.cases 0 (fun j' => LU₁.2 i' j') j) i)

variable {r : ℕ}

/-- The exact run of Algorithm 12.1.1 on one entry: `n = 1`. -/
theorem algorithm_12_1_1_zero (ω ν : Fin 1 → ℝ) (R S : Matrix (Fin 1) (Fin r) ℝ) :
    Id.run (algorithm_12_1_1 pure 0 ω ν R S) = (1, of fun _ _ => (R 0 ⬝ᵥ S 0) / (ω 0 - ν 0)) := by
  simp [algorithm_12_1_1, FloatingPoint.dotAccum_id_finRange]

/-- The exact run of Algorithm 12.1.1: one elimination step on the generators, then the recursion.
-/
theorem algorithm_12_1_1_succ {N : ℕ} (ω ν : Fin (N + 2) → ℝ)
    (R S : Matrix (Fin (N + 2)) (Fin r) ℝ) :
    Id.run (algorithm_12_1_1 pure (N + 1) ω ν R S) =
      let a : Fin (N + 2) → ℝ := fun i => (R i ⬝ᵥ S 0) / (ω i - ν 0)
      let g : Fin (N + 1) → ℝ := fun j => (S j.succ ⬝ᵥ R 0) / (ω 0 - ν j.succ)
      let LU₁ := Id.run (algorithm_12_1_1 pure N (fun i => ω i.succ) (fun j => ν j.succ)
        (of fun i c => R i.succ c - a i.succ * R 0 c / a 0)
        (of fun j c => S j.succ c - g j * S 0 c / a 0))
      (of fun i j => Fin.cases (Fin.cases 1 (fun _ => 0) j)
          (fun i' => Fin.cases (a i'.succ / a 0) (fun j' => LU₁.1 i' j') j) i,
        of fun i j => Fin.cases (Fin.cases (a 0) g j)
          (fun i' => Fin.cases 0 (fun j' => LU₁.2 i' j') j) i) := by
  simp only [algorithm_12_1_1, Id.run_bind, Id.run_pure, idRun_vecLoop,
    FloatingPoint.dotAccum_id_finRange, zero_add]

/-- The first row and column of an LU factorization. -/
private theorem isLU_apply_zero_succ {N : ℕ} {A L U : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ}
    (h : IsLU A L U) :
    (∀ j, A 0 j = U 0 j) ∧ (∀ i : Fin (N + 1), A i.succ 0 = L i.succ 0 * U 0 0) ∧
      ∀ i j : Fin (N + 1), A i.succ j.succ =
        L i.succ 0 * U 0 j.succ + ∑ k : Fin (N + 1), L i.succ k.succ * U k.succ j.succ := by
  have hL : ∀ k : Fin (N + 1), L 0 k.succ = 0 :=
    fun k => h.isUnitLowerTriangular.isLowerTriangular (Fin.succ_pos k)
  have hU : ∀ k : Fin (N + 1), U k.succ 0 = 0 := fun k => h.isUpperTriangular (Fin.succ_pos k)
  refine ⟨fun j => ?_, fun i => ?_, fun i j => ?_⟩
  · rw [← h.mul_eq, mul_apply, Fin.sum_univ_succ, h.isUnitLowerTriangular.diag_eq_one]
    simp [hL]
  · rw [← h.mul_eq, mul_apply, Fin.sum_univ_succ]
    simp [hU]
  · rw [← h.mul_eq, mul_apply, Fin.sum_univ_succ]

/-- The Schur complement of an LU factorization with a nonzero pivot is the product of the trailing
factors. -/
private theorem isLU_schur {N : ℕ} {A L U : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ}
    (h : IsLU A L U) (hα : U 0 0 ≠ 0) :
    IsLU (A.submatrix Fin.succ Fin.succ -
        (A 0 0)⁻¹ • vecMulVec (fun i => A i.succ 0) fun j => A 0 j.succ)
      (L.submatrix Fin.succ Fin.succ) (U.submatrix Fin.succ Fin.succ) := by
  obtain ⟨h0j, hi0, hij⟩ := isLU_apply_zero_succ h
  refine ⟨⟨fun i j hij' => h.isUnitLowerTriangular.isLowerTriangular (Fin.succ_lt_succ_iff.2 hij'),
    fun i => h.isUnitLowerTriangular.diag_eq_one _⟩,
    fun i j hij' => h.isUpperTriangular (Fin.succ_lt_succ_iff.2 hij'), ?_⟩
  ext i j
  rw [mul_apply, Matrix.sub_apply, submatrix_apply, Matrix.smul_apply, vecMulVec_apply, hij, hi0,
    h0j, h0j]
  simp only [submatrix_apply, smul_eq_mul]
  field_simp
  ring

/-- The exact run of Algorithm 12.1.1, whenever `A` has an LU factorization with nonzero pivots
`u₁₁, …, u_{n−1,n−1}`, is an LU factorization of `A`. -/
private theorem algorithm_12_1_1_spec_aux : ∀ (N : ℕ) {ω ν : Fin (N + 1) → ℝ}
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} {R S : Matrix (Fin (N + 1)) (Fin r) ℝ},
    (∀ k j, ω k ≠ ν j) → diagonal ω * A - A * diagonal ν = R * Sᵀ →
    (∃ L U, IsLU A L U ∧ ∀ i : Fin N, U i.castSucc i.castSucc ≠ 0) →
    IsLU A (Id.run (algorithm_12_1_1 pure N ω ν R S)).1
      (Id.run (algorithm_12_1_1 pure N ω ν R S)).2
  | 0, ω, ν, A, R, S, hων, h, _ => by
      have hA := (equation_12_1_4 hων).1 h 0 0
      rw [algorithm_12_1_1_zero]
      have h0 : ∀ i : Fin (0 + 1), i = 0 := fun i => Fin.ext (Nat.lt_one_iff.1 i.isLt)
      refine ⟨isUnitLowerTriangular_one, fun i j hij => absurd hij (by simp [h0 i, h0 j]),
        ?_⟩
      ext i j
      rw [h0 i, h0 j]
      simp [hA]
  | N + 1, ω, ν, A, R, S, hων, h, ⟨L, U, hLU, hpiv⟩ => by
      obtain ⟨h0j, hi0, hij⟩ := isLU_apply_zero_succ hLU
      have hU0 : U 0 0 ≠ 0 := hpiv 0
      have hα : A 0 0 ≠ 0 := by rw [h0j]; exact hU0
      have ha : ∀ i, (R i ⬝ᵥ S 0) / (ω i - ν 0) = A i 0 := fun i =>
        ((equation_12_1_4 hων).1 h i 0).symm
      have hg : ∀ j : Fin (N + 1), (S j.succ ⬝ᵥ R 0) / (ω 0 - ν j.succ) = A 0 j.succ := fun j => by
        rw [dotProduct_comm]; exact ((equation_12_1_4 hων).1 h 0 j.succ).symm
      set A₁ := A.submatrix Fin.succ Fin.succ -
        (A 0 0)⁻¹ • vecMulVec (fun i => A i.succ 0) fun j => A 0 j.succ with hA₁
      have hS₁ := theorem_12_1_1 hων h hα
      have hR₁ : (of fun i c => R i.succ c - A i.succ 0 * R 0 c / A 0 0 :
          Matrix (Fin (N + 1)) (Fin r) ℝ) =
          R.submatrix Fin.succ id - (A 0 0)⁻¹ • vecMulVec (fun i => A i.succ 0) (R 0) := by
        ext i c
        simp only [of_apply, Matrix.sub_apply, submatrix_apply, id, Matrix.smul_apply,
          vecMulVec_apply, smul_eq_mul]
        ring
      have hS₁' : (of fun j c => S j.succ c - A 0 j.succ * S 0 c / A 0 0 :
          Matrix (Fin (N + 1)) (Fin r) ℝ) =
          S.submatrix Fin.succ id - (A 0 0)⁻¹ • vecMulVec (fun j => A 0 j.succ) (S 0) := by
        ext j c
        simp only [of_apply, Matrix.sub_apply, submatrix_apply, id, Matrix.smul_apply,
          vecMulVec_apply, smul_eq_mul]
        ring
      have hrec := algorithm_12_1_1_spec_aux N (ω := fun i => ω i.succ) (ν := fun j => ν j.succ)
        (A := A₁) (R := of fun i c => R i.succ c - A i.succ 0 * R 0 c / A 0 0)
        (S := of fun j c => S j.succ c - A 0 j.succ * S 0 c / A 0 0)
        (fun k j => hων _ _) (by rw [hR₁, hS₁']; exact hS₁)
        ⟨_, _, isLU_schur hLU hU0, fun i => hpiv i.succ⟩
      rw [algorithm_12_1_1_succ]
      simp only [ha, hg]
      set LU₁ := Id.run (algorithm_12_1_1 pure N (fun i => ω i.succ) (fun j => ν j.succ)
        (of fun i c => R i.succ c - A i.succ 0 * R 0 c / A 0 0)
        (of fun j c => S j.succ c - A 0 j.succ * S 0 c / A 0 0))
      refine ⟨⟨fun i j hij' => ?_, fun i => ?_⟩, fun i j hij' => ?_, ?_⟩
      · revert hij'
        refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
          intro hij' <;> simp only [of_apply, Fin.cases_zero, Fin.cases_succ]
        · exact absurd hij' (lt_irrefl _)
        · exact absurd hij' (Fin.succ_pos _).not_gt
        · exact hrec.isUnitLowerTriangular.isLowerTriangular (Fin.succ_lt_succ_iff.1 hij')
      · refine Fin.cases ?_ (fun i => ?_) i <;> simp only [of_apply, Fin.cases_zero, Fin.cases_succ]
        exact hrec.isUnitLowerTriangular.diag_eq_one i
      · revert hij'
        refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
          intro hij' <;> simp only [of_apply, Fin.cases_zero, Fin.cases_succ]
        · exact absurd hij' (lt_irrefl _)
        · exact absurd hij' (Fin.succ_pos _).not_gt
        · exact hrec.isUpperTriangular (Fin.succ_lt_succ_iff.1 hij')
      · ext i j
        refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
          simp only [mul_apply, Fin.sum_univ_succ, of_apply, Fin.cases_zero, Fin.cases_succ,
            one_mul, zero_mul, Finset.sum_const_zero, add_zero, mul_zero]
        · rw [div_mul_cancel₀ _ hα]
        · have := congrFun (congrFun hrec.mul_eq i) j
          rw [mul_apply, Fin.sum_univ_succ] at this
          rw [this, hA₁, Matrix.sub_apply, submatrix_apply, Matrix.smul_apply, vecMulVec_apply,
            smul_eq_mul]
          field_simp
          ring

/-- **Correctness of Algorithm 12.1.1** in exact arithmetic: if `ω_k ≠ ν_j` for all `k, j`,
`Ω A − A Λ = R Sᵀ`, and the strict leading principal submatrices of `A` are nonsingular (the book's
"has an LU factorization": the pivots met in the recursion are those of Gaussian elimination), then
the computed `(L, U)` is an LU factorization of `A`. -/
theorem algorithm_12_1_1_spec {N : ℕ} {ω ν : Fin (N + 1) → ℝ}
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} {R S : Matrix (Fin (N + 1)) (Fin r) ℝ}
    (hων : ∀ k j, ω k ≠ ν j) (h : diagonal ω * A - A * diagonal ν = R * Sᵀ)
    (hA : ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k)) :
    IsLU A (Id.run (algorithm_12_1_1 pure N ω ν R S)).1
      (Id.run (algorithm_12_1_1 pure N ω ν R S)).2 := by
  obtain ⟨L, U, hLU⟩ := exists_isLU_of_forall_isUnit_strictLeadingPrincipalSubmatrix hA
  refine algorithm_12_1_1_spec_aux N hων h ⟨L, U, hLU, fun i => ?_⟩
  have hdet := hLU.det_strictLeadingPrincipalSubmatrix i.succ
  have hu := (isUnit_iff_isUnit_det _).1 (hA i.succ)
  rw [hdet] at hu
  exact (Finset.prod_ne_zero_iff.1 hu.ne_zero) i.castSucc
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, Fin.castSucc_lt_succ⟩)

end LUdisp

/-! ### Permutations of Cauchy-like matrices (§12.1.6) -/

/-- A permutation matrix conjugates a diagonal matrix into the permuted diagonal. -/
theorem permMatrix_mul_diagonal_mul_transpose (σ : Equiv.Perm (Fin n)) (d : Fin n → ℝ) :
    σ.permMatrix ℝ * diagonal d * (σ.permMatrix ℝ)ᵀ = diagonal (d ∘ σ) := by
  rw [transpose_permMatrix, Equiv.Perm.permMatrix, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simp [diagonal_apply, Equiv.Perm.inv_def]

/-- A permutation matrix is orthogonal: `Pᵀ P = I`. -/
theorem transpose_permMatrix_mul_self (σ : Equiv.Perm (Fin n)) :
    (σ.permMatrix ℝ)ᵀ * σ.permMatrix ℝ = 1 := by
  rw [transpose_permMatrix, ← permMatrix_mul, mul_inv_cancel, permMatrix_one]

/-- **§12.1.6**: for permutations `P`, `Q`, `(P Ω Pᵀ)(P A Qᵀ) − (P A Qᵀ)(Q Λ Qᵀ) = (P R)(Q S)ᵀ`, and
`P Ω Pᵀ`, `Q Λ Qᵀ` are again diagonal: row and column permutations of a Cauchy-like matrix are
tracked on `{Ω, Λ, R, S}`. -/
theorem displacement_permute {ω ν : Fin n → ℝ} {r : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {R S : Matrix (Fin n) (Fin r) ℝ} (h : diagonal ω * A - A * diagonal ν = R * Sᵀ)
    (σ τ : Equiv.Perm (Fin n)) :
    (σ.permMatrix ℝ * diagonal ω * (σ.permMatrix ℝ)ᵀ) *
          (σ.permMatrix ℝ * A * (τ.permMatrix ℝ)ᵀ) -
        (σ.permMatrix ℝ * A * (τ.permMatrix ℝ)ᵀ) *
          (τ.permMatrix ℝ * diagonal ν * (τ.permMatrix ℝ)ᵀ) =
      (σ.permMatrix ℝ * R) * (τ.permMatrix ℝ * S)ᵀ ∧
      σ.permMatrix ℝ * diagonal ω * (σ.permMatrix ℝ)ᵀ = diagonal (ω ∘ σ) ∧
      τ.permMatrix ℝ * diagonal ν * (τ.permMatrix ℝ)ᵀ = diagonal (ν ∘ τ) := by
  refine ⟨?_, permMatrix_mul_diagonal_mul_transpose σ ω,
    permMatrix_mul_diagonal_mul_transpose τ ν⟩
  have hP := transpose_permMatrix_mul_self σ
  have hQ := transpose_permMatrix_mul_self τ
  calc _ = σ.permMatrix ℝ * (diagonal ω * A - A * diagonal ν) * (τ.permMatrix ℝ)ᵀ := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (σ.permMatrix ℝ)ᵀ, hP, Matrix.one_mul,
          ← Matrix.mul_assoc (τ.permMatrix ℝ)ᵀ, hQ, Matrix.one_mul]
    _ = _ := by
        rw [h, transpose_mul]
        simp only [Matrix.mul_assoc]

/-! ### Fast LU with partial pivoting (Algorithm 12.1.2) -/

section LUdispPiv

/-- The pivot of Algorithm 12.1.2: the first index of largest `|a_i|` (the book's "`|[P a]₁|`
maximal", ties to the smallest index; the comparisons act on computed values and are exact). -/
noncomputable def pivotIndex {k : ℕ} (a : Fin (k + 1) → ℝ) : Fin (k + 1) :=
  (List.finRange (k + 1)).foldl (fun best i => if |a best| < |a i| then i else best) 0

/-- The running maximum of a scan dominates its start and every scanned entry. -/
private theorem abs_le_abs_foldl_max {k : ℕ} (a : Fin k → ℝ) (l : List (Fin k)) (b : Fin k) :
    |a b| ≤ |a (l.foldl (fun best i => if |a best| < |a i| then i else best) b)| ∧
      ∀ i ∈ l, |a i| ≤ |a (l.foldl (fun best i => if |a best| < |a i| then i else best) b)| := by
  induction l generalizing b with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    set b' := if |a b| < |a x| then x else b
    have hb : |a b| ≤ |a b'| ∧ |a x| ≤ |a b'| := by
      simp only [b']
      split_ifs with h
      · exact ⟨h.le, le_rfl⟩
      · exact ⟨le_rfl, not_lt.1 h⟩
    obtain ⟨ih1, ih2⟩ := ih b'
    exact ⟨hb.1.trans ih1, hb.2.trans ih1, ih2⟩

/-- The pivot has the entry of largest modulus. -/
theorem abs_le_abs_pivotIndex {k : ℕ} (a : Fin (k + 1) → ℝ) (i : Fin (k + 1)) :
    |a i| ≤ |a (pivotIndex a)| :=
  (abs_le_abs_foldl_max a _ 0).2 i (List.mem_finRange i)

/-- **Algorithm 12.1.2** (`LUdispPiv`): as `LUdisp`, with partial pivoting. After
`a = (R s₁) ./ (ω − ν₁)`, a row of largest `|a_i|` is swapped to the top of `a`, `R` and `ω` (the
permutation `P = swap(1, i)`); then `α = a₁`, `f = a(2:n)`, `g`, `R̃₁`, `S̃₁` as in `LUdisp`,
`[L₁, U₁, P₁] = LUdispPiv(ω(2:n), ν(2:n), R̃₁, S̃₁)`, and `L = [1 0; P₁ f/α L₁]`, `U = [α gᵀ; 0
U₁]`, `P = diag(1, P₁) P`. A permutation is returned as an `Equiv.Perm`, its matrix being
`permMatrix`. -/
noncomputable def algorithm_12_1_2 {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) {r : ℕ} :
    (N : ℕ) → (ω ν : Fin (N + 1) → ℝ) → (R S : Matrix (Fin (N + 1)) (Fin r) ℝ) →
      M (Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ × Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ ×
        Equiv.Perm (Fin (N + 1)))
  | 0, ω, ν, R, S => do
      let t ← FloatingPoint.dotAccum rnd (List.finRange r) (R 0) (S 0) 0
      let u ← rnd (t / (← rnd (ω 0 - ν 0)))
      pure (1, of fun _ _ => u, 1)
  | N + 1, ω, ν, R, S => do
      let a₀ ← vecLoop fun i : Fin (N + 2) => do
        let t ← FloatingPoint.dotAccum rnd (List.finRange r) (R i) (S 0) 0
        rnd (t / (← rnd (ω i - ν 0)))
      let σ := Equiv.swap 0 (pivotIndex a₀)
      let g ← vecLoop fun j : Fin (N + 1) => do
        let t ← FloatingPoint.dotAccum rnd (List.finRange r) (S j.succ) (R (σ 0)) 0
        rnd (t / (← rnd (ω (σ 0) - ν j.succ)))
      let R₁ ← vecLoop fun i : Fin (N + 1) => vecLoop fun c : Fin r => do
        rnd (R (σ i.succ) c - (← rnd ((← rnd (a₀ (σ i.succ) * R (σ 0) c)) / a₀ (σ 0))))
      let S₁ ← vecLoop fun j : Fin (N + 1) => vecLoop fun c : Fin r => do
        rnd (S j.succ c - (← rnd ((← rnd (g j * S 0 c)) / a₀ (σ 0))))
      let LUP₁ ← algorithm_12_1_2 rnd N (fun i => ω (σ i.succ)) (fun j => ν j.succ) (of R₁) (of S₁)
      let l ← vecLoop fun i : Fin (N + 1) => rnd (a₀ (σ i.succ) / a₀ (σ 0))
      pure (of fun i j => Fin.cases (Fin.cases 1 (fun _ => 0) j)
          (fun i' => Fin.cases (l (LUP₁.2.2 i')) (fun j' => LUP₁.1 i' j') j) i,
        of fun i j => Fin.cases (Fin.cases (a₀ (σ 0)) g j)
          (fun i' => Fin.cases 0 (fun j' => LUP₁.2.1 i' j') j) i,
        Equiv.Perm.decomposeFin.symm (pivotIndex a₀, LUP₁.2.2))

variable {r : ℕ}

/-- The exact run of Algorithm 12.1.2 on one entry. -/
theorem algorithm_12_1_2_zero (ω ν : Fin 1 → ℝ) (R S : Matrix (Fin 1) (Fin r) ℝ) :
    Id.run (algorithm_12_1_2 pure 0 ω ν R S) =
      (1, of fun _ _ => (R 0 ⬝ᵥ S 0) / (ω 0 - ν 0), 1) := by
  simp [algorithm_12_1_2, FloatingPoint.dotAccum_id_finRange]

/-- The exact run of Algorithm 12.1.2: the pivoting step, one elimination step on the generators,
then the recursion. -/
theorem algorithm_12_1_2_succ {N : ℕ} (ω ν : Fin (N + 2) → ℝ)
    (R S : Matrix (Fin (N + 2)) (Fin r) ℝ) :
    Id.run (algorithm_12_1_2 pure (N + 1) ω ν R S) =
      let a₀ : Fin (N + 2) → ℝ := fun i => (R i ⬝ᵥ S 0) / (ω i - ν 0)
      let σ := Equiv.swap 0 (pivotIndex a₀)
      let g : Fin (N + 1) → ℝ := fun j => (S j.succ ⬝ᵥ R (σ 0)) / (ω (σ 0) - ν j.succ)
      let LUP₁ := Id.run (algorithm_12_1_2 pure N (fun i => ω (σ i.succ)) (fun j => ν j.succ)
        (of fun i c => R (σ i.succ) c - a₀ (σ i.succ) * R (σ 0) c / a₀ (σ 0))
        (of fun j c => S j.succ c - g j * S 0 c / a₀ (σ 0)))
      (of fun i j => Fin.cases (Fin.cases 1 (fun _ => 0) j)
          (fun i' => Fin.cases (a₀ (σ (LUP₁.2.2 i').succ) / a₀ (σ 0))
            (fun j' => LUP₁.1 i' j') j) i,
        of fun i j => Fin.cases (Fin.cases (a₀ (σ 0)) g j)
          (fun i' => Fin.cases 0 (fun j' => LUP₁.2.1 i' j') j) i,
        Equiv.Perm.decomposeFin.symm (pivotIndex a₀, LUP₁.2.2)) := by
  simp only [algorithm_12_1_2, Id.run_bind, Id.run_pure, idRun_vecLoop,
    FloatingPoint.dotAccum_id_finRange, zero_add]

/-- The Schur complement of a nonsingular matrix with a nonzero pivot is nonsingular. -/
private theorem isUnit_schur {N : ℕ} {A : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ} (hA : IsUnit A)
    (hα : A 0 0 ≠ 0) :
    IsUnit (A.submatrix Fin.succ Fin.succ -
      (A 0 0)⁻¹ • vecMulVec (fun i => A i.succ 0) fun j => A 0 j.succ) := by
  have h := isUnit_schurComplementSingle hA hα
  have he : A.submatrix Fin.succ Fin.succ -
      (A 0 0)⁻¹ • vecMulVec (fun i => A i.succ 0) (fun j => A 0 j.succ) =
        (A.schurComplementSingle 0).submatrix (finSuccAboveEquiv 0) (finSuccAboveEquiv 0) := by
    ext i j
    simp only [Matrix.sub_apply, submatrix_apply, Matrix.smul_apply, vecMulVec_apply,
      smul_eq_mul, schurComplementSingle_apply, finSuccAboveEquiv_apply, Fin.succAbove_zero]
    ring
  rw [he, isUnit_iff_isUnit_det, det_submatrix_equiv_self, ← isUnit_iff_isUnit_det]
  exact h

private theorem algorithm_12_1_2_spec_aux : ∀ (N : ℕ) {ω ν : Fin (N + 1) → ℝ}
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} {R S : Matrix (Fin (N + 1)) (Fin r) ℝ},
    (∀ k j, ω k ≠ ν j) → diagonal ω * A - A * diagonal ν = R * Sᵀ → IsUnit A →
    IsLU ((Id.run (algorithm_12_1_2 pure N ω ν R S)).2.2.permMatrix ℝ * A)
        (Id.run (algorithm_12_1_2 pure N ω ν R S)).1
        (Id.run (algorithm_12_1_2 pure N ω ν R S)).2.1 ∧
      ∀ i j, |(Id.run (algorithm_12_1_2 pure N ω ν R S)).1 i j| ≤ 1
  | 0, ω, ν, A, R, S, hων, h, _ => by
      have hA := (equation_12_1_4 hων).1 h 0 0
      rw [algorithm_12_1_2_zero]
      have h0 : ∀ i : Fin (0 + 1), i = 0 := fun i => Fin.ext (Nat.lt_one_iff.1 i.isLt)
      refine ⟨⟨isUnitLowerTriangular_one, fun i j hij => absurd hij (by simp [h0 i, h0 j]), ?_⟩,
        fun i j => ?_⟩
      · ext i j
        rw [h0 i, h0 j]
        simp [hA]
      · rw [h0 i, h0 j]
        simp
  | N + 1, ω, ν, A, R, S, hων, h, hunit => by
      have hcol : ∀ i, (R i ⬝ᵥ S 0) / (ω i - ν 0) = A i 0 := fun i =>
        ((equation_12_1_4 hων).1 h i 0).symm
      set a₀ : Fin (N + 2) → ℝ := fun i => (R i ⬝ᵥ S 0) / (ω i - ν 0) with ha₀
      set σ := Equiv.swap 0 (pivotIndex a₀) with hσ
      have hσ0 : σ 0 = pivotIndex a₀ := Equiv.swap_apply_left _ _
      have hα : A (σ 0) 0 ≠ 0 := by
        intro h0
        have hall : ∀ i, A i 0 = 0 := fun i => by
          have := abs_le_abs_pivotIndex a₀ i
          rw [← hσ0, show a₀ (σ 0) = A (σ 0) 0 from hcol _, h0, abs_zero] at this
          rw [← hcol i]
          exact abs_nonpos_iff.1 this
        exact ((isUnit_iff_isUnit_det A).1 hunit).ne_zero (det_eq_zero_of_column_eq_zero 0 hall)
      set A' := A.submatrix σ id with hA'
      have hων' : ∀ k j, (ω ∘ σ) k ≠ ν j := fun k j => hων _ _
      have h' : diagonal (ω ∘ σ) * A' - A' * diagonal ν = R.submatrix σ id * Sᵀ :=
        (equation_12_1_4 hων').2 fun k j => (equation_12_1_4 hων).1 h (σ k) j
      have hunit' : IsUnit A' := by
        rw [hA', isUnit_iff_isUnit_det, det_permute]
        refine IsUnit.mul ?_ ((isUnit_iff_isUnit_det A).1 hunit)
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
      have hα' : A' 0 0 ≠ 0 := hα
      have hS₁ := theorem_12_1_1 hων' h' hα'
      set A₁ := A'.submatrix Fin.succ Fin.succ -
        (A' 0 0)⁻¹ • vecMulVec (fun i => A' i.succ 0) fun j => A' 0 j.succ with hA₁
      have hg : ∀ j : Fin (N + 1), (S j.succ ⬝ᵥ R (σ 0)) / (ω (σ 0) - ν j.succ) = A' 0 j.succ :=
        fun j => by rw [dotProduct_comm]; exact ((equation_12_1_4 hων).1 h (σ 0) j.succ).symm
      have hR₁ : (of fun i c => R (σ i.succ) c - a₀ (σ i.succ) * R (σ 0) c / a₀ (σ 0) :
          Matrix (Fin (N + 1)) (Fin r) ℝ) =
          (R.submatrix σ id).submatrix Fin.succ id -
            (A' 0 0)⁻¹ • vecMulVec (fun i => A' i.succ 0) (R.submatrix σ id 0) := by
        ext i c
        simp only [of_apply, Matrix.sub_apply, submatrix_apply, id, Matrix.smul_apply,
          vecMulVec_apply, smul_eq_mul, ha₀, hcol, hA']
        ring
      have hS₁' : (of fun j c => S j.succ c -
            (S j.succ ⬝ᵥ R (σ 0)) / (ω (σ 0) - ν j.succ) * S 0 c / a₀ (σ 0) :
          Matrix (Fin (N + 1)) (Fin r) ℝ) =
          S.submatrix Fin.succ id - (A' 0 0)⁻¹ • vecMulVec (fun j => A' 0 j.succ) (S 0) := by
        ext j c
        simp only [of_apply, Matrix.sub_apply, submatrix_apply, id, Matrix.smul_apply,
          vecMulVec_apply, smul_eq_mul, hg, ha₀, hcol]
        rw [hA']
        simp only [submatrix_apply, id]
        ring
      obtain ⟨hrec, hbound⟩ := algorithm_12_1_2_spec_aux N (ω := fun i => ω (σ i.succ))
        (ν := fun j => ν j.succ) (A := A₁)
        (R := of fun i c => R (σ i.succ) c - a₀ (σ i.succ) * R (σ 0) c / a₀ (σ 0))
        (S := of fun j c => S j.succ c -
            (S j.succ ⬝ᵥ R (σ 0)) / (ω (σ 0) - ν j.succ) * S 0 c / a₀ (σ 0))
        (fun k j => hων _ _) (by rw [hR₁, hS₁']; exact hS₁) (isUnit_schur hunit' hα')
      rw [algorithm_12_1_2_succ]
      simp only [← hσ, ← ha₀]
      set LUP₁ := Id.run (algorithm_12_1_2 pure N (fun i => ω (σ i.succ)) (fun j => ν j.succ)
        (of fun i c => R (σ i.succ) c - a₀ (σ i.succ) * R (σ 0) c / a₀ (σ 0))
        (of fun j c => S j.succ c -
            (S j.succ ⬝ᵥ R (σ 0)) / (ω (σ 0) - ν j.succ) * S 0 c / a₀ (σ 0)))
      have ha : ∀ x, a₀ x = A x 0 := hcol
      have hP : (Equiv.Perm.decomposeFin.symm (pivotIndex a₀, LUP₁.2.2)).permMatrix ℝ * A =
          of fun i j => Fin.cases (A' 0 j) (fun i' => A' (LUP₁.2.2 i').succ j) i := by
        rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]
        ext i j
        refine Fin.cases ?_ (fun i => ?_) i
        · simp [hA', hσ0]
        · simp [hA', hσ]
      refine ⟨⟨⟨fun i j hij' => ?_, fun i => ?_⟩, fun i j hij' => ?_, ?_⟩, fun i j => ?_⟩
      · revert hij'
        refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
          intro hij' <;> simp only [of_apply, Fin.cases_zero, Fin.cases_succ]
        · exact absurd hij' (lt_irrefl _)
        · exact absurd hij' (Fin.succ_pos _).not_gt
        · exact hrec.isUnitLowerTriangular.isLowerTriangular (Fin.succ_lt_succ_iff.1 hij')
      · refine Fin.cases ?_ (fun i => ?_) i <;> simp only [of_apply, Fin.cases_zero, Fin.cases_succ]
        exact hrec.isUnitLowerTriangular.diag_eq_one i
      · revert hij'
        refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
          intro hij' <;> simp only [of_apply, Fin.cases_zero, Fin.cases_succ]
        · exact absurd hij' (lt_irrefl _)
        · exact absurd hij' (Fin.succ_pos _).not_gt
        · exact hrec.isUpperTriangular (Fin.succ_lt_succ_iff.1 hij')
      · rw [hP]
        have hmul := hrec.mul_eq
        rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul] at hmul
        ext i j
        refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
          simp only [mul_apply, Fin.sum_univ_succ, of_apply, Fin.cases_zero, Fin.cases_succ,
            one_mul, zero_mul, Finset.sum_const_zero, add_zero, mul_zero, hcol]
        · rfl
        · exact hg j
        · rw [div_mul_cancel₀ _ hα]
          rfl
        · have := congrFun (congrFun hmul i) j
          rw [mul_apply, Fin.sum_univ_succ] at this
          rw [this, hg, hA₁, submatrix_apply, Matrix.sub_apply, submatrix_apply, Matrix.smul_apply,
            vecMulVec_apply, smul_eq_mul]
          have hα'' : ∀ x, A (σ x) 0 = A' x 0 := fun _ => rfl
          simp only [hα'', id]
          field_simp
          ring
      · refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
          simp only [of_apply, Fin.cases_zero, Fin.cases_succ, hcol]
        · simp
        · simp
        · rw [abs_div, div_le_one (abs_pos.2 hα)]
          have := abs_le_abs_pivotIndex a₀ (σ (LUP₁.2.2 i).succ)
          rw [← hσ0, ha, ha] at this
          exact this
        · exact hbound i j

/-- **Correctness of Algorithm 12.1.2** in exact arithmetic: if `ω_k ≠ ν_j` for all `k, j`,
`Ω A − A Λ = R Sᵀ` and `A` is nonsingular, the computed `(L, U, P)` satisfy `P A = L U` with `L`
unit lower triangular, `U` upper triangular, and `|l_ij| ≤ 1` (partial pivoting). The row swap is
tracked on the generators (§12.1.6), and nonsingularity passes to the Schur complement, `|α| = max
|a_i| > 0` since the first column of a nonsingular `A` is nonzero. -/
theorem algorithm_12_1_2_spec {N : ℕ} {ω ν : Fin (N + 1) → ℝ}
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} {R S : Matrix (Fin (N + 1)) (Fin r) ℝ}
    (hων : ∀ k j, ω k ≠ ν j) (h : diagonal ω * A - A * diagonal ν = R * Sᵀ) (hA : IsUnit A) :
    IsLU ((Id.run (algorithm_12_1_2 pure N ω ν R S)).2.2.permMatrix ℝ * A)
        (Id.run (algorithm_12_1_2 pure N ω ν R S)).1
        (Id.run (algorithm_12_1_2 pure N ω ν R S)).2.1 ∧
      ∀ i j, |(Id.run (algorithm_12_1_2 pure N ω ν R S)).1 i j| ≤ 1 :=
  algorithm_12_1_2_spec_aux N hων h hA

end LUdispPiv

/-! ### Toeplitz-like and Hankel-like matrices (§12.1.7) -/

/-- **§12.1.7**, Definition: `A` is Toeplitz-like of displacement rank at most `r` if
`Z₁ A − A Z₋₁ = R Sᵀ` for some `R, S ∈ ℝ^{n×r}` (the book's `r ≪ n` is informal). -/
def IsToeplitzLike (r : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  displacementRank (cyclicShift n 1) (cyclicShift n (-1)) A ≤ r

/-- **§12.1.7**, Definition: `A` is Hankel-like of displacement rank at most `r` if
`Z₁ᵀ A − A Z₋₁ = R Sᵀ` for some `R, S ∈ ℝ^{n×r}`. -/
def IsHankelLike (r : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  displacementRank (cyclicShift n 1)ᵀ (cyclicShift n (-1)) A ≤ r

/-- **§12.1.7**, Definition: `A` is Toeplitz-plus-Hankel-like of displacement rank at most `r` if
`Y₀₀ A − A Y₁₁ = R Sᵀ` for some `R, S ∈ ℝ^{n×r}`. -/
def IsToeplitzPlusHankelLike (r : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  displacementRank (cornerTridiagonal n 0 0) (cornerTridiagonal n 1 1) A ≤ r

/-- **(12.1.8)**: for a Toeplitz `T`, `Z₁ T − T Z₋₁` vanishes outside the first row and the last
column, so `T` is Toeplitz-like of displacement rank at most `2`. -/
theorem equation_12_1_8 {T : Matrix (Fin n) (Fin n) ℝ} (hT : T.IsToeplitz) :
    (∀ i j : Fin n, 0 < (i : ℕ) → (j : ℕ) + 1 < n →
      (cyclicShift n 1 * T - T * cyclicShift n (-1) : Matrix (Fin n) (Fin n) ℝ) i j = 0) ∧
      IsToeplitzLike 2 T :=
  ⟨fun _ _ hi hj => sylvesterMap_cyclicShift_toeplitz_apply hT hi hj,
    displacementRank_cyclicShift_toeplitz_le hT⟩

/-- **(12.1.9)**: for a Toeplitz `T`, `Y₀₀ T − T Y₁₁` vanishes off the border (the first and last
rows and columns), so `T` is Toeplitz-plus-Hankel-like of displacement rank at most `4`. -/
theorem equation_12_1_9 {T : Matrix (Fin n) (Fin n) ℝ} (hT : T.IsToeplitz) :
    (∀ i j : Fin n, 0 < (i : ℕ) → (i : ℕ) + 1 < n → 0 < (j : ℕ) → (j : ℕ) + 1 < n →
      (cornerTridiagonal n 0 0 * T - T * cornerTridiagonal n 1 1 : Matrix (Fin n) (Fin n) ℝ) i j
        = 0) ∧
      IsToeplitzPlusHankelLike 4 T :=
  ⟨fun _ _ hi₀ hi hj₀ hj => sylvesterMap_cornerTridiagonal_toeplitz_apply hT hi₀ hi hj₀ hj,
    displacementRank_cornerTridiagonal_toeplitz_le hT⟩

/-- `Z_φ` satisfies `Z_φᵀⁿ = φ I` as well. -/
private theorem transpose_cyclicShift_pow_card (φ : ℝ) :
    (cyclicShift n φ)ᵀ ^ n = φ • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  rw [← transpose_pow, cyclicShift_pow_card, transpose_smul, transpose_one]

/-- The `{Z₁ᵀ, Z₋₁}` Sylvester operator is injective (as P12.1.1(a)): `Z₁ᵀ X = X Z₋₁` gives
`Z₁ᵀⁿ X = X Z₋₁ⁿ`, that is `X = −X`. -/
theorem sylvesterMap_transpose_cyclicShift_injective :
    Function.Injective (sylvesterMap (cyclicShift n (1 : ℝ))ᵀ (cyclicShift n (-1))) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro X hX
  rw [sylvesterMap_apply, sub_eq_zero] at hX
  have hsc : SemiconjBy X (cyclicShift n (-1)) (cyclicShift n 1)ᵀ := hX.symm
  have hpow := (hsc.pow_right n).eq
  rw [transpose_cyclicShift_pow_card, cyclicShift_pow_card, one_smul, Matrix.one_mul,
    Matrix.mul_smul, Matrix.mul_one, neg_one_smul, neg_eq_iff_add_eq_zero, ← two_smul ℝ X] at hpow
  exact (smul_eq_zero.mp hpow).resolve_left two_ne_zero

/-- An injective Sylvester operator between real matrices means disjoint complex spectra. -/
private theorem disjoint_spectrum_of_injective {F G : Matrix (Fin n) (Fin n) ℝ}
    (h : Function.Injective (sylvesterMap F G)) :
    Disjoint (spectrum ℂ F.complexify) (spectrum ℂ G.complexify) := by
  have hinj : Function.Injective (sylvesterMap F.complexify G.complexify) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro X hX
    rw [sylvesterMap_apply, sub_eq_zero] at hX
    have hre : sylvesterMap F G (X.map Complex.re) = 0 := by
      ext i j
      have := congrArg Complex.re (congrFun (congrFun hX i) j)
      simp only [mul_apply, complexify_apply, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero] at this
      simp only [sylvesterMap_apply, Matrix.sub_apply, mul_apply, map_apply, Matrix.zero_apply,
        sub_eq_zero]
      exact this
    have him : sylvesterMap F G (X.map Complex.im) = 0 := by
      ext i j
      have := congrArg Complex.im (congrFun (congrFun hX i) j)
      simp only [mul_apply, complexify_apply, Complex.im_sum, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, mul_zero, zero_add] at this
      simp only [sylvesterMap_apply, Matrix.sub_apply, mul_apply, map_apply, Matrix.zero_apply,
        sub_eq_zero]
      exact this
    have h1 := h (hre.trans (map_zero _).symm)
    have h2 := h (him.trans (map_zero _).symm)
    ext i j
    apply Complex.ext
    · simpa using congrFun (congrFun h1 i) j
    · simpa using congrFun (congrFun h2 i) j
  exact sylvesterMap_bijective_iff_disjoint_spectrum.1
    ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩

/-- **§12.1.7**, after (12.1.9) (printed "`λ(Z₋₁) ∪ λ(Z₁) = ∅`", read `∩`): no complex number is an
eigenvalue of both `Z₁` and `Z₋₁` (nor of `Z₁ᵀ` and `Z₋₁`), nor of both `Y₀₀` and `Y₁₁`;
equivalently, the Sylvester maps `X ↦ Z₁ X − X Z₋₁`, `X ↦ Z₁ᵀ X − X Z₋₁` and `X ↦ Y₀₀ X − X Y₁₁` are
injective, which is the precondition of the definition (12.1.2) for the displacement ranks of
§12.1.7. -/
theorem disjoint_spectra_displacement_operators :
    Function.Injective (sylvesterMap (cyclicShift n (1 : ℝ)) (cyclicShift n (-1))) ∧
      Function.Injective (sylvesterMap (cyclicShift n (1 : ℝ))ᵀ (cyclicShift n (-1))) ∧
      Function.Injective (sylvesterMap (cornerTridiagonal n 0 0) (cornerTridiagonal n 1 1)) ∧
      Disjoint (spectrum ℂ (cyclicShift n (1 : ℝ)).complexify)
        (spectrum ℂ (cyclicShift n (-1 : ℝ)).complexify) ∧
      Disjoint (spectrum ℂ (cyclicShift n (1 : ℝ))ᵀ.complexify)
        (spectrum ℂ (cyclicShift n (-1 : ℝ)).complexify) ∧
      Disjoint (spectrum ℂ (cornerTridiagonal n 0 0).complexify)
        (spectrum ℂ (cornerTridiagonal n 1 1).complexify) := by
  have h1 := sylvesterMap_cyclicShift_one_neg_one_injective (K := ℝ) (n := n) two_ne_zero
  have h2 := sylvesterMap_transpose_cyclicShift_injective (n := n)
  have h3 := sylvesterMap_cornerTridiagonal_injective (n := n)
  exact ⟨h1, h2, h3, disjoint_spectrum_of_injective h1, disjoint_spectrum_of_injective h2,
    disjoint_spectrum_of_injective h3⟩

/-- **(12.1.10)**: for a Hankel `H`, `Z₁ᵀ H − H Z₋₁` vanishes outside the last row and the last
column, so `H` is Hankel-like of displacement rank at most `2`; and `ℰ_n H` is Toeplitz. -/
theorem equation_12_1_10 {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsHankel) :
    (∀ i j : Fin n, (i : ℕ) + 1 < n → (j : ℕ) + 1 < n →
      ((cyclicShift n 1)ᵀ * H - H * cyclicShift n (-1) : Matrix (Fin n) (Fin n) ℝ) i j = 0) ∧
      IsHankelLike 2 H ∧
      (exchange n * H).IsToeplitz :=
  ⟨fun _ _ hi hj => sylvesterMap_cyclicShift_hankel_apply hH hi hj,
    displacementRank_cyclicShift_hankel_le hH, exchange_mul_isHankel hH⟩

/-- **(12.1.11)** and the sentence after it: for a Hankel `H`, `Y₀₀ H − H Y₁₁` vanishes off the
border and `rank_{Y₀₀, Y₁₁}(H) ≤ 4`; and for `A = T + H` with `T` Toeplitz, `rank_{Y₀₀, Y₁₁}(A) ≤
4`. -/
theorem equation_12_1_11 {T H : Matrix (Fin n) (Fin n) ℝ} (hT : T.IsToeplitz) (hH : H.IsHankel) :
    (∀ i j : Fin n, 0 < (i : ℕ) → (i : ℕ) + 1 < n → 0 < (j : ℕ) → (j : ℕ) + 1 < n →
      (cornerTridiagonal n 0 0 * H - H * cornerTridiagonal n 1 1 : Matrix (Fin n) (Fin n) ℝ) i j
        = 0) ∧
      IsToeplitzPlusHankelLike 4 H ∧ IsToeplitzPlusHankelLike 4 (T + H) :=
  ⟨fun _ _ hi₀ hi hj₀ hj => sylvesterMap_cornerTridiagonal_hankel_apply hH hi₀ hi hj₀ hj,
    displacementRank_cornerTridiagonal_hankel_le hH,
    displacementRank_cornerTridiagonal_toeplitz_add_hankel_le hT hH⟩

/-! ### Conversion to Cauchy-like form (§12.1.8) -/

/-- **§12.1.8**: if `F A − A G = R Sᵀ` and `X_F⁻¹ F X_F = Ω`, `X_G⁻¹ G X_G = Λ` are real
diagonalizations, then
`Ã = X_F⁻¹ A X_G` satisfies `Ω Ã − Ã Λ = R̃ S̃ᵀ` with `R̃ = X_F⁻¹ R`, `S̃ = X_Gᵀ S` (the book's
first display writes `X_G⁻¹ G X_F` for `X_G⁻¹ G X_G`); and Steps 1–4 are correct: if `Ã x̃ = X_F⁻¹
b` then `x = X_G x̃` solves `A x = b`. -/
theorem cauchyLike_of_diagonalizable {F G A X_F X_G : Matrix (Fin n) (Fin n) ℝ} {r : ℕ}
    {R S : Matrix (Fin n) (Fin r) ℝ} {ω ν : Fin n → ℝ} (hXF : IsUnit X_F) (hXG : IsUnit X_G)
    (h : F * A - A * G = R * Sᵀ) (hΩ : X_F⁻¹ * F * X_F = diagonal ω)
    (hΛ : X_G⁻¹ * G * X_G = diagonal ν) :
    diagonal ω * (X_F⁻¹ * A * X_G) - (X_F⁻¹ * A * X_G) * diagonal ν = (X_F⁻¹ * R) * (X_Gᵀ * S)ᵀ ∧
      ∀ b x : Fin n → ℝ, (X_F⁻¹ * A * X_G) *ᵥ x = X_F⁻¹ *ᵥ b → A *ᵥ (X_G *ᵥ x) = b := by
  have h1 : X_F * X_F⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hXF)
  have h2 : X_G * X_G⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hXG)
  refine ⟨?_, fun b x hx => ?_⟩
  · rw [← hΩ, ← hΛ]
    calc _ = X_F⁻¹ * (F * A - A * G) * X_G := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
          rw [← Matrix.mul_assoc X_F, h1, Matrix.one_mul, ← Matrix.mul_assoc X_G, h2,
            Matrix.one_mul]
      _ = _ := by
          rw [h, transpose_mul, transpose_transpose]
          simp only [Matrix.mul_assoc]
  · have := congrArg (X_F *ᵥ ·) hx
    simp only [mulVec_mulVec, ← Matrix.mul_assoc, h1, Matrix.one_mul, one_mulVec] at this
    rw [mulVec_mulVec]
    exact this

/-! ### Fast eigensystems (12.1.12)–(12.1.13) -/

/-- The book's DST-I matrix `𝒮_n`, `[𝒮_n]_kj = √(2/(n+1)) sin(kjπ/(n+1))` (§12.1.8, (12.1.12)): the
backbone's `Matrix.dst1` scaled to be orthogonal. -/
noncomputable def dstMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  √(2 / ((n : ℝ) + 1)) • dst1 n

/-- **(12.1.12)**: `𝒮_n` is symmetric and orthogonal, and
`𝒮_nᵀ Y₀₀ 𝒮_n = 2 diag(cos(π/(n+1)), …, cos(nπ/(n+1)))` (0-based: the `k`-th entry `2
cos((k+1)π/(n+1))`). -/
theorem equation_12_1_12 :
    (dstMatrix n)ᵀ = dstMatrix n ∧ (dstMatrix n)ᵀ * dstMatrix n = 1 ∧
      (dstMatrix n)ᵀ * cornerTridiagonal n 0 0 * dstMatrix n =
        diagonal fun k : Fin n => 2 * Real.cos ((((k : ℕ) : ℝ) + 1) * Real.pi / ((n : ℝ) + 1)) := by
  have hc : √(2 / ((n : ℝ) + 1)) * √(2 / ((n : ℝ) + 1)) * (((n : ℝ) + 1) / 2) = 1 := by
    rw [Real.mul_self_sqrt (by positivity)]
    field_simp
  have hT : (dstMatrix n)ᵀ = dstMatrix n := by
    rw [dstMatrix, transpose_smul, dst1_transpose]
  have hcol : cornerTridiagonal n 0 0 * dst1 n =
      dst1 n * diagonal fun k : Fin n => 2 * Real.cos ((((k : ℕ) : ℝ) + 1) * Real.pi /
        ((n : ℝ) + 1)) := by
    ext i j
    have h := congrFun (symmTridiagonalToeplitz_mulVec_sineVec (n := n) (a := (1 : ℝ)) (b := 0) j) i
    rw [mul_diagonal, dst1_apply_eq_sineVec, cornerTridiagonal_zero_zero, mul_apply]
    simp only [dst1_apply_eq_sineVec]
    rw [show ∑ k, symmTridiagonalToeplitz n (1 : ℝ) 0 i k * sineVec n j k =
      (symmTridiagonalToeplitz n (1 : ℝ) 0 *ᵥ sineVec n j) i from rfl, h, Pi.smul_apply,
      smul_eq_mul]
    ring
  refine ⟨hT, ?_, ?_⟩
  · rw [hT, dstMatrix, Matrix.smul_mul, Matrix.mul_smul, dst1_mul_self, smul_smul, smul_smul, hc,
      one_smul]
  · rw [hT, dstMatrix, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, hcol,
      ← Matrix.mul_assoc, dst1_mul_self, Matrix.smul_mul, Matrix.one_mul, smul_smul, smul_smul, hc,
      one_smul]

/-- The column normalization `√(2/n) q_j` of the book's DCT-II matrix `𝒞_n` (`q₁ = 1/√2`, `q_j = 1`
otherwise): `√(1/n)` for the first column, `√(2/n)` for the others. -/
noncomputable def dctScale (n : ℕ) (j : Fin n) : ℝ :=
  if (j : ℕ) = 0 then √(1 / (n : ℝ)) else √(2 / (n : ℝ))

/-- The book's DCT-II matrix `𝒞_n`, `[𝒞_n]_kj = √(2/n) cos((2k−1)(j−1)π/(2n)) q_j` ((12.1.13)): the
transpose of the backbone's `Matrix.dct2` with the columns normalized. -/
noncomputable def dctMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (dct2 n)ᵀ * diagonal (dctScale n)

/-- **(12.1.13)**: `𝒞_n` is orthogonal and `𝒞_nᵀ Y₁₁ 𝒞_n = 2 diag(1, cos(π/n), …, cos((n−1)π/n))`
(P12.1.5). -/
theorem equation_12_1_13 :
    (dctMatrix n)ᵀ * dctMatrix n = 1 ∧
      (dctMatrix n)ᵀ * cornerTridiagonal n 1 1 * dctMatrix n =
        diagonal fun k : Fin n => 2 * Real.cos ((k : ℕ) * Real.pi / n) := by
  set d : Fin n → ℝ := fun k => if (k : ℕ) = 0 then (n : ℝ) else n / 2 with hd
  have hwd : ∀ k, dctScale n k * d k * dctScale n k = 1 := by
    intro k
    have hn : (0 : ℝ) < n := by exact_mod_cast k.pos
    simp only [dctScale, hd]
    split_ifs
    · rw [mul_comm, ← mul_assoc, Real.mul_self_sqrt (by positivity)]
      field_simp
    · rw [mul_comm, ← mul_assoc, Real.mul_self_sqrt (by positivity)]
      field_simp
  have hrow : dct2 n * cornerTridiagonal n 1 1 =
      (diagonal fun k : Fin n => 2 * Real.cos ((k : ℕ) * Real.pi / n)) * dct2 n := by
    rw [← dct2_mul_cornerTridiagonal_one_one_mul_inv, Matrix.mul_assoc _ (dct2 n)⁻¹,
      nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp (isUnit_dct2 n)), Matrix.mul_one]
  have hC : (dctMatrix n)ᵀ = diagonal (dctScale n) * dct2 n := by
    rw [dctMatrix, transpose_mul, diagonal_transpose, transpose_transpose]
  have hD : dct2 n * (dct2 n)ᵀ = diagonal d := dct2_mul_transpose n
  constructor
  · rw [hC, dctMatrix, Matrix.mul_assoc, ← Matrix.mul_assoc (dct2 n), hD, diagonal_mul_diagonal,
      diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    rw [← mul_assoc]
    exact hwd k
  · rw [hC, dctMatrix, Matrix.mul_assoc (diagonal _) (dct2 n), hrow]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (dct2 n), hD, diagonal_mul_diagonal, diagonal_mul_diagonal,
      diagonal_mul_diagonal]
    congr 1
    funext k
    linear_combination (2 * Real.cos ((k : ℕ) * Real.pi / n)) * hwd k

end GolubVanLoan.Chapter12

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Numlib.Analysis.Fourier.SineCosineTransform
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Eigen.InvariantSubspace
import Numlib.Krylov.Convergence.Polynomial
import Numlib.LinearAlgebra.Matrix.KroneckerSum
import Numlib.RingTheory.Polynomial.ChebyshevMinimax
import Numlib.Stationary.Block
import Numlib.Stationary.DiagDominant
import Numlib.Stationary.SPD
import Numlib.Stationary.Sweep
import NumlibSurface.GolubVanLoan.Chapter01.Section01
import NumlibSurface.GolubVanLoan.Chapter01.Section04
import NumlibSurface.GolubVanLoan.Chapter04.Section08
import NumlibSurface.GolubVanLoan.Chapter07.Section03

/-!
# Golub–Van Loan §11.2: the classical iterations

Surface file for Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th edition, §11.2:
the Jacobi and Gauss–Seidel iterations (11.2.2)–(11.2.5) and their block versions, splittings and
Theorem 11.2.1, the diagonal-dominance and positive-definiteness theorems 11.2.2–11.2.3, the model
problem (11.2.10)–(11.2.17) with its alternating-direction variant, SOR and SSOR
((11.2.18)–(11.2.27), Theorem 11.2.4), and the Chebyshev semi-iterative method (11.2.28)–(11.2.30).

## Design

Everything the section proves already lives in the backbone `Numlib/Stationary/*`: a splitting
`A = M − N` is `Stationary.Splitting A` (determined by `M`, with `N := M − A`), its iteration matrix
`G = M⁻¹N` is `s.iterationOperator`, one step `M x⁺ = N x + b` is `s.mulVecStep b x`, and `ρ(G)` is
`Matrix.complexSpectralRadius G`, the spectral radius of the complexification (an `ℝ≥0∞`). The
book's `L_A, D_A, U_A` are `Matrix.strictLower A`, `Matrix.diagPart A`, `Matrix.strictUpper A`.

The componentwise loops (11.2.2), (11.2.3) and the two SOR sweeps of §11.2.7 are programs in the
conventions of `NumlibSurface/GolubVanLoan` (a monad `M`, a rounding hook `rnd : ℝ → M ℝ` after
every `+`, `−`, `×`, `/`, loops as `List.foldlM`). Their exact semantics (`M := Id`,
`rnd := pure`) is the backbone sweep: an in-place loop over a list whose step `i` rewrites entry
`i` from the current vector computes, at entry `i`, its formula on the vector "new entries before
`i`, old ones after" (`List.foldl_update_apply_of_pairwise_rel`); the componentwise recursion
`Matrix.sorSweep_apply` determines its solution uniquely, by well-founded induction along the sweep
order.

The model problem uses `Matrix.symmTridiagonalToeplitz` (`T_m = tridiag(−1, 2, −1)`,
`E_m = tridiag(1, 0, 1)`), the Kronecker sum `Matrix.kroneckerSum` on `Fin n₁ × Fin n₂` (the
lexicographic order of the pairs is the book's row-by-row order of the grid) and the sine transform
matrix `Matrix.dst1` of the backbone, whose columns `Matrix.sineVec` are the eigenvectors. The
earlier chapters' restatements are used where they apply: the nonsingularity of `S_m` from §4.8.6
(`Chapter04.dd_eigen`) and the Schur power bound (7.3.15) (`Chapter07.lemma_7_3_2`).

Indices are 0-based: the book's `x_i`, `a_ij` (`i, j = 1:n`) are `x (i − 1)`, `A (i − 1) (j − 1)`;
the book's `μ_k^{(m)}` (`k = 1:m`) is `modelEEigenvalues m (k − 1)`.

## Main results

* `jacobiSweep`, `gaussSeidelSweep`, `sorSweep`, `backwardSorSweep`, `ssorSweep` — the programs,
  with `equation_11_2_4`, `equation_11_2_5`, `equation_11_2_19`, `equation_11_2_21`,
  `equation_11_2_22`, `equation_11_2_25` their exact semantics.
* `theorem_11_2_1` — convergence for every start iff `ρ(G) < 1`; `theorem_11_2_2`, `theorem_11_2_3`,
  `theorem_11_2_4` — Jacobi, Gauss–Seidel and SSOR convergence.
* `poissonJacobiArray_eq`, `poissonGaussSeidelArray_eq` — the array averagings of §11.2.6 are one
  Jacobi and one Gauss–Seidel step for the model system (the latter with the unknowns in the
  book's row-by-row order, `poissonMatrixLex`).
* `equation_11_2_15`, `equation_11_2_17` — the spectral radii of Jacobi and of the
  alternating-direction iteration on the model problem.
* `chebyshevSemiIterative_norm_le`, `chebyshevSemiIterative_spec` — the Chebyshev semi-iterative
  method.

## Not formalized here

The 3-by-3 display (11.2.1) (the case `n = 3` of (11.2.2)); the discussion of vectorization and
parallelism; the remark that the Jacobi radius (11.2.15) approaches unity (a limit the text does
not state precisely); Young's theory of the optimal `ω`; the Problems. The book's errors are
recorded in the docstrings concerned: (11.2.8) (corner `kαλ^{k−1}`), the proof of Theorem 11.2.1
(`E = T − D`, `‖E‖_F`), Theorem 11.2.2 (`G_J` for `A`), (11.2.18)–(11.2.21) (the signs of `U_A`,
`L_A`), (11.2.17) (`= =`), and §11.2.8 (`λ(G)` for `λ(A)`).
-/

open Filter Topology Polynomial Finset
open scoped Matrix Kronecker

namespace GolubVanLoan.Chapter11

variable {n : ℕ}

/-! ### Loop lemmas -/

section Loops

variable {ι : Type*}

/-- **Uniqueness of a triangular recursion.** Two vectors satisfying the same recursion
`z i = g i z`, where `g i` reads only the entries `r`-before `i`, agree when `r` is well founded. -/
private theorem eq_of_forall_eq_apply (r : ι → ι → Prop) (wf : WellFounded r) {z S : ι → ℝ}
    (g : ι → (ι → ℝ) → ℝ) (hg : ∀ i u v, (∀ j, r j i → u j = v j) → g i u = g i v)
    (hz : ∀ i, z i = g i z) (hS : ∀ i, S i = g i S) : z = S :=
  funext fun i => wf.induction (C := fun i => z i = S i) i fun i ih => by
    rw [hz, hS]; exact hg i z S ih

end Loops

/-- The off-diagonal sum splits into the parts before and after the diagonal. -/
private theorem sum_ne_eq_sum_lt_add_sum_gt (g : Fin n → ℝ) (i : Fin n) :
    ∑ j ∈ univ.filter (· ≠ i), g j =
      ∑ j ∈ univ.filter (· < i), g j + ∑ j ∈ univ.filter (i < ·), g j := by
  rw [← Finset.sum_union (Finset.disjoint_filter.2 fun j _ h1 h2 => lt_asymm h1 h2),
    ← Finset.filter_or]
  exact Finset.sum_congr (Finset.filter_congr fun j _ => ne_iff_lt_or_gt) fun _ _ => rfl

/-! ### The componentwise programs -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The off-diagonal residual `b_i − ∑_{j < i} a_ij x_j − ∑_{j > i} a_ij x_j` of the componentwise
iterations, accumulated from `b_i` in increasing `j` with every product and every difference
rounded. -/
def offDiagResidual (A : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) (i : Fin n) : M ℝ :=
  ((List.finRange n).filter (· ≠ i)).foldlM (fun s j => do rnd (s - (← rnd (A i j * x j)))) (b i)

/-- **The Jacobi step (11.2.2).**
```
for i = 1:n
    x_i^(k) = (b_i − ∑_{j=1}^{i−1} a_ij x_j^(k−1) − ∑_{j=i+1}^{n} a_ij x_j^(k−1)) / a_ii
end
```
Every `x_j` read is the old vector `x`. -/
noncomputable def jacobiSweep (A : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) :
    M (Fin n → ℝ) :=
  (List.finRange n).foldlM (fun y i => do
    let s ← offDiagResidual rnd A b x i
    let xi ← rnd (s / A i i)
    pure (Function.update y i xi)) x

/-- **The Gauss–Seidel step (11.2.3).**
```
for i = 1:n
    x_i^(k) = (b_i − ∑_{j=1}^{i−1} a_ij x_j^(k) − ∑_{j=i+1}^{n} a_ij x_j^(k−1)) / a_ii
end
```
The same arithmetic as `jacobiSweep`, but `x` is updated in place, so that the most recent estimates
are used. -/
noncomputable def gaussSeidelSweep (A : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) :
    M (Fin n → ℝ) :=
  (List.finRange n).foldlM (fun y i => do
    let s ← offDiagResidual rnd A b y i
    let xi ← rnd (s / A i i)
    pure (Function.update y i xi)) x

/-- **SOR at the component level** (§11.2.7; the display carries no tag in the source and is taken
to be the lost (11.2.20)):
```
for i = 1:n
    x_i^(k) = ω (b_i − ∑_{j=1}^{i−1} a_ij x_j^(k) − ∑_{j=i+1}^{n} a_ij x_j^(k−1)) / a_ii
              + (1 − ω) x_i^(k−1)
end
```
in place, with `1 − ω` computed (and rounded) once. -/
noncomputable def sorSweep (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) (b x : Fin n → ℝ) :
    M (Fin n → ℝ) := do
  let c ← rnd (1 - ω)
  (List.finRange n).foldlM (fun y i => do
    let s ← offDiagResidual rnd A b y i
    let g ← rnd (s / A i i)
    let t ← rnd (ω * g)
    let u ← rnd (c * y i)
    let xi ← rnd (t + u)
    pure (Function.update y i xi)) x

/-- **Backward SOR** (§11.2.7, "we can just as easily update from bottom to top"): the arithmetic
of `sorSweep` with `i` running from `n` down to `1`. -/
noncomputable def backwardSorSweep (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) (b x : Fin n → ℝ) :
    M (Fin n → ℝ) := do
  let c ← rnd (1 - ω)
  (List.finRange n).reverse.foldlM (fun y i => do
    let s ← offDiagResidual rnd A b y i
    let g ← rnd (s / A i i)
    let t ← rnd (ω * g)
    let u ← rnd (c * y i)
    let xi ← rnd (t + u)
    pure (Function.update y i xi)) x

/-- **One SSOR step** ((11.2.22)–(11.2.23)): a forward SOR sweep producing `y^(k)`, then a backward
one from `y^(k)`. -/
noncomputable def ssorSweep (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) (b x : Fin n → ℝ) :
    M (Fin n → ℝ) := do
  let y ← sorSweep rnd A ω b x
  backwardSorSweep rnd A ω b y

end Programs

/-! ### Exact semantics of the programs -/

/-- The exact off-diagonal residual. -/
private theorem offDiagResidual_id (A : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) (i : Fin n) :
    Id.run (offDiagResidual pure A b x i) = b i - ∑ j ∈ univ.filter (· ≠ i), A i j * x j := by
  rw [offDiagResidual, List.idRun_foldlM]
  exact (List.foldl_sub_eq_sub_sum_map (fun j => A i j * x j) _ _).trans
    (by rw [List.sum_map_filter_finRange])

/-- The weight function of `List.foldl_update_apply_of_pairwise_rel` along `List.finRange n`,
summed off the diagonal. -/
private theorem sum_ne_forward (A : Matrix (Fin n) (Fin n) ℝ) (z x : Fin n → ℝ) (i : Fin n) :
    ∑ j ∈ univ.filter (· ≠ i), A i j * (if j ∈ List.finRange n ∧ j < i then z j else x j) =
      ∑ j ∈ univ.filter (· < i), A i j * z j + ∑ j ∈ univ.filter (i < ·), A i j * x j := by
  rw [sum_ne_eq_sum_lt_add_sum_gt]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [ite_eq_left ⟨List.mem_finRange j, (Finset.mem_filter.1 hj).2⟩]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [ite_eq_right fun h => lt_asymm h.2 (Finset.mem_filter.1 hj).2]

/-- The weight function of `List.foldl_update_apply_of_pairwise_rel` along the reversed
`List.finRange n`. -/
private theorem sum_ne_backward (A : Matrix (Fin n) (Fin n) ℝ) (z x : Fin n → ℝ) (i : Fin n) :
    ∑ j ∈ univ.filter (· ≠ i),
        A i j * (if j ∈ (List.finRange n).reverse ∧ i < j then z j else x j) =
      ∑ j ∈ univ.filter (· < i), A i j * x j + ∑ j ∈ univ.filter (i < ·), A i j * z j := by
  rw [sum_ne_eq_sum_lt_add_sum_gt]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [ite_eq_right fun h => lt_asymm h.2 (Finset.mem_filter.1 hj).2]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [ite_eq_left ⟨List.mem_reverse.2 (List.mem_finRange j), (Finset.mem_filter.1 hj).2⟩]

/-- The forward SOR recursion, with the old value of entry `i` read in place. -/
private theorem sorSweep_run (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) (b x : Fin n → ℝ) :
    Id.run (sorSweep pure A ω b x) = (List.finRange n).foldl (fun y i => Function.update y i
      (ω * (Id.run (offDiagResidual pure A b y i) / A i i) + (1 - ω) * y i)) x :=
  List.idRun_foldlM

/-- The backward SOR recursion. -/
private theorem backwardSorSweep_run (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) (b x : Fin n → ℝ) :
    Id.run (backwardSorSweep pure A ω b x) = (List.finRange n).reverse.foldl
      (fun y i => Function.update y i
        (ω * (Id.run (offDiagResidual pure A b y i) / A i i) + (1 - ω) * y i)) x :=
  List.idRun_foldlM

/-- **The exact forward SOR program is the backbone SOR sweep.** -/
private theorem sorSweep_id (A : Matrix (Fin n) (Fin n) ℝ) (h : IsUnit (Matrix.diagPart A))
    (ω : ℝ) (b x : Fin n → ℝ) : Id.run (sorSweep pure A ω b x) = A.sorSweep ω b x := by
  rw [sorSweep_run]
  refine eq_of_forall_eq_apply (· < ·) wellFounded_lt
    (fun i u => ω / A i i * (b i - ∑ j ∈ univ.filter (· < i), A i j * u j
      - ∑ j ∈ univ.filter (i < ·), A i j * x j) + (1 - ω) * x i) ?_ (fun i => ?_)
    (fun i => Matrix.sorSweep_apply A h ω b x i)
  · intro i u v huv
    rw [Finset.sum_congr rfl fun j hj => by rw [huv j (Finset.mem_filter.1 hj).2]]
  · rw [List.foldl_update_apply_of_pairwise_rel (· < ·) (fun _ _ h h' => lt_asymm h h') _
      (List.pairwise_lt_finRange n) x (List.mem_finRange i), offDiagResidual_id, sum_ne_forward]
    simp only [lt_self_iff_false, and_false, ↓reduceIte]
    ring

/-- **The exact backward SOR program is the backbone backward SOR sweep.** -/
private theorem backwardSorSweep_id (A : Matrix (Fin n) (Fin n) ℝ)
    (h : IsUnit (Matrix.diagPart A)) (ω : ℝ) (b x : Fin n → ℝ) :
    Id.run (backwardSorSweep pure A ω b x) = A.backwardSorSweep ω b x := by
  rw [backwardSorSweep_run]
  refine eq_of_forall_eq_apply (· > ·) wellFounded_gt
    (fun i u => ω / A i i * (b i - ∑ j ∈ univ.filter (i < ·), A i j * u j
      - ∑ j ∈ univ.filter (· < i), A i j * x j) + (1 - ω) * x i) ?_ (fun i => ?_)
    (fun i => Matrix.backwardSorSweep_apply A h ω b x i)
  · intro i u v huv
    rw [Finset.sum_congr rfl fun j hj => by rw [huv j (Finset.mem_filter.1 hj).2]]
  · have hpw : ((List.finRange n).reverse).Pairwise (fun a b => b < a) :=
      List.pairwise_reverse.2 (List.pairwise_lt_finRange n)
    rw [List.foldl_update_apply_of_pairwise_rel (fun a b => b < a) (fun _ _ h h' => lt_asymm h h')
      _ hpw x
      (List.mem_reverse.2 (List.mem_finRange i)), offDiagResidual_id, sum_ne_backward]
    simp only [lt_self_iff_false, and_false, ↓reduceIte]
    ring

/-- **(11.2.4): the Jacobi step is `M_J x⁽ᵏ⁾ = N_J x⁽ᵏ⁻¹⁾ + b`** with `M_J = D_A` and
`N_J = −(L_A + U_A)`: if every `a_ii ≠ 0`, the exact run of (11.2.2) is the step of the Jacobi
splitting. -/
theorem equation_11_2_4 (A : Matrix (Fin n) (Fin n) ℝ) (h : IsUnit (Matrix.diagPart A))
    (b x : Fin n → ℝ) :
    Id.run (jacobiSweep pure A b x) = (Matrix.jacobiSplitting A h).mulVecStep b x ∧
      (Matrix.jacobiSplitting A h).m = Matrix.diagPart A ∧
      (Matrix.jacobiSplitting A h).n = -(Matrix.strictLower A + Matrix.strictUpper A) := by
  refine ⟨?_, rfl, Matrix.jacobiSplitting_n A h⟩
  have hrun : Id.run (jacobiSweep pure A b x) = (List.finRange n).foldl (fun y i =>
      Function.update y i (Id.run (offDiagResidual pure A b x i) / A i i)) x :=
    List.idRun_foldlM
  rw [← Matrix.jorSweep_one_eq_mulVecStep A h b, hrun]
  funext i
  rw [List.foldl_update_apply_of_pairwise_rel (· < ·) (fun _ _ h h' => lt_asymm h h')
    (fun i _ => Id.run (offDiagResidual pure A b x i) / A i i) (List.pairwise_lt_finRange n) x
    (List.mem_finRange i), offDiagResidual_id, Matrix.jorSweep, Finset.filter_ne']
  ring

/-- **(11.2.5): the Gauss–Seidel step is `M_GS x⁽ᵏ⁾ = N_GS x⁽ᵏ⁻¹⁾ + b`** with `M_GS = D_A + L_A`
and `N_GS = −U_A`: if every `a_ii ≠ 0`, the exact run of (11.2.3) is the step of the Gauss–Seidel
splitting. -/
theorem equation_11_2_5 (A : Matrix (Fin n) (Fin n) ℝ) (h : IsUnit (Matrix.diagPart A))
    (b x : Fin n → ℝ) :
    Id.run (gaussSeidelSweep pure A b x) = (Matrix.gaussSeidelSplitting A h).mulVecStep b x ∧
      (Matrix.gaussSeidelSplitting A h).m = Matrix.diagPart A + Matrix.strictLower A ∧
      (Matrix.gaussSeidelSplitting A h).n = -Matrix.strictUpper A := by
  refine ⟨?_, rfl, Matrix.gaussSeidelSplitting_n A h⟩
  have hrun : Id.run (gaussSeidelSweep pure A b x) = (List.finRange n).foldl (fun y i =>
      Function.update y i (Id.run (offDiagResidual pure A b y i) / A i i)) x :=
    List.idRun_foldlM
  rw [← Matrix.sorSweep_one_eq_mulVecStep A h b, hrun]
  refine eq_of_forall_eq_apply (· < ·) wellFounded_lt
    (fun i u => 1 / A i i * (b i - ∑ j ∈ univ.filter (· < i), A i j * u j
      - ∑ j ∈ univ.filter (i < ·), A i j * x j) + (1 - 1) * x i) ?_ (fun i => ?_)
    (fun i => Matrix.sorSweep_apply A h 1 b x i)
  · intro i u v huv
    rw [Finset.sum_congr rfl fun j hj => by rw [huv j (Finset.mem_filter.1 hj).2]]
  · rw [List.foldl_update_apply_of_pairwise_rel (· < ·) (fun _ _ h h' => lt_asymm h h')
      (fun i y => Id.run (offDiagResidual pure A b y i) / A i i) (List.pairwise_lt_finRange n) x
      (List.mem_finRange i), offDiagResidual_id, sum_ne_forward]
    ring

/-! ### Steps of a splitting -/

section Step

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- One step of a splitting contracts the error by `G`. -/
private theorem mulVecStep_sub {A : Matrix ι ι ℝ} (s : Stationary.Splitting A)
    {b x : ι → ℝ} (hx : A *ᵥ x = b) (y : ι → ℝ) :
    s.mulVecStep b y - x = s.iterationOperator *ᵥ (y - x) := by
  conv_lhs => rw [← (Stationary.Splitting.mulVecStep_fixed_iff s b x).2 hx]
  rw [Stationary.Splitting.mulVecStep_eq_iterationOperator_mulVec_add,
    Stationary.Splitting.mulVecStep_eq_iterationOperator_mulVec_add, Matrix.mulVec_sub]
  abel

/-- `y` is the step of a splitting exactly when it solves `M y = N x + b`. -/
private theorem eq_mulVecStep_iff {A : Matrix ι ι ℝ} (s : Stationary.Splitting A)
    (b x y : ι → ℝ) : y = s.mulVecStep b x ↔ s.m *ᵥ y = s.n *ᵥ x + b := by
  constructor
  · rintro rfl
    exact Matrix.mulVec_nonsing_inv_mulVec s.isUnit _
  · intro h
    change y = s.m⁻¹ *ᵥ (s.n *ᵥ x + b)
    rw [← h, Matrix.nonsing_inv_mulVec_mulVec s.isUnit]

end Step

/-- Row `r` of `D x` for the block diagonal part `D`: the sum over the columns in `r`'s block. -/
private theorem blockDiagPart_mulVec_apply {p : ℕ} (π : Fin n → Fin p)
    (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (r : Fin n) :
    (Matrix.blockDiagPart π A *ᵥ v) r = ∑ c ∈ univ.filter (fun c => π c = π r), A r c * v c := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.blockDiagPart_apply]
  by_cases hc : π c = π r
  · rw [ite_eq_left hc.symm, ite_eq_left hc]
  · rw [ite_eq_right (Ne.symm hc), ite_eq_right hc, zero_mul]

/-- Row `r` of `L x` for the strict block-lower part `L`. -/
private theorem blockStrictLower_mulVec_apply {p : ℕ} (π : Fin n → Fin p)
    (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (r : Fin n) :
    (Matrix.blockStrictLower π A *ᵥ v) r = ∑ c ∈ univ.filter (fun c => π c < π r), A r c * v c := by
  simp only [Matrix.mulVec, dotProduct, Matrix.blockStrictLower_apply, ite_mul, zero_mul]
  rw [Finset.sum_filter]

/-- Row `r` of `U x` for the strict block-upper part `U`. -/
private theorem blockStrictUpper_mulVec_apply {p : ℕ} (π : Fin n → Fin p)
    (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (r : Fin n) :
    (Matrix.blockStrictUpper π A *ᵥ v) r = ∑ c ∈ univ.filter (fun c => π r < π c), A r c * v c := by
  simp only [Matrix.mulVec, dotProduct, Matrix.blockStrictUpper_apply, ite_mul, zero_mul]
  rw [Finset.sum_filter]

/-- Row `r` of `A x`, split by blocks. -/
private theorem mulVec_apply_eq_block {p : ℕ} (π : Fin n → Fin p)
    (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (r : Fin n) :
    (A *ᵥ v) r = ∑ c ∈ univ.filter (fun c => π c = π r), A r c * v c +
      ∑ c ∈ univ.filter (fun c => π c < π r), A r c * v c +
      ∑ c ∈ univ.filter (fun c => π r < π c), A r c * v c := by
  conv_lhs => rw [← Matrix.blockDiagPart_add_blockStrictLower_add_blockStrictUpper π A]
  rw [Matrix.add_mulVec, Matrix.add_mulVec, Pi.add_apply, Pi.add_apply,
    blockDiagPart_mulVec_apply, blockStrictLower_mulVec_apply, blockStrictUpper_mulVec_apply]

/-! ### Block versions -/

/-- **Block Jacobi (§11.2.2).** For a block labelling `π` of the unknowns with nonsingular diagonal
blocks, `x⁺` satisfies the book's block equations
`A_ii x⁺_i = b_i − ∑_{j ≠ i} A_ij x_j` (row by row: the columns in the block of the row carry `x⁺`,
all others the old `x`) exactly when it is the step of the block Jacobi splitting. -/
theorem blockJacobi_eq {p : ℕ} (π : Fin n → Fin p) (A : Matrix (Fin n) (Fin n) ℝ)
    (h : IsUnit (Matrix.blockDiagPart π A)) (b x y : Fin n → ℝ) :
    (∀ r, ∑ c ∈ univ.filter (fun c => π c = π r), A r c * y c =
        b r - ∑ c ∈ univ.filter (fun c => π c ≠ π r), A r c * x c) ↔
      y = (Matrix.blockJacobiSplitting π A h).mulVecStep b x := by
  rw [eq_mulVecStep_iff, funext_iff]
  refine forall_congr' fun r => ?_
  have hn : (Matrix.blockJacobiSplitting π A h).n = Matrix.blockDiagPart π A - A := rfl
  have hne := Finset.sum_filter_add_sum_filter_not univ (fun c => π c = π r)
    (fun c => A r c * x c)
  simp only [← ne_eq] at hne
  rw [hn, Matrix.sub_mulVec, Pi.add_apply, Pi.sub_apply]
  change _ ↔ (Matrix.blockDiagPart π A *ᵥ y) r = _
  rw [blockDiagPart_mulVec_apply, blockDiagPart_mulVec_apply]
  simp only [Matrix.mulVec, dotProduct]
  constructor <;> intro h' <;> linarith [hne]

/-- **Block Gauss–Seidel (§11.2.2).** As `blockJacobi_eq`, with the blocks before the row's block
carrying the new values: `A_ii x⁺_i = b_i − ∑_{j < i} A_ij x⁺_j − ∑_{j > i} A_ij x_j` exactly when
`x⁺` is the step of the block Gauss–Seidel splitting. -/
theorem blockGaussSeidel_eq {p : ℕ} (π : Fin n → Fin p) (A : Matrix (Fin n) (Fin n) ℝ)
    (h : IsUnit (Matrix.blockDiagPart π A)) (b x y : Fin n → ℝ) :
    (∀ r, ∑ c ∈ univ.filter (fun c => π c = π r), A r c * y c =
        b r - ∑ c ∈ univ.filter (fun c => π c < π r), A r c * y c
          - ∑ c ∈ univ.filter (fun c => π r < π c), A r c * x c) ↔
      y = (Matrix.blockGaussSeidelSplitting π A h).mulVecStep b x := by
  rw [eq_mulVecStep_iff, funext_iff]
  refine forall_congr' fun r => ?_
  have hm : (Matrix.blockGaussSeidelSplitting π A h).m =
      Matrix.blockDiagPart π A + Matrix.blockStrictLower π A := rfl
  have hn : (Matrix.blockGaussSeidelSplitting π A h).n =
      Matrix.blockDiagPart π A + Matrix.blockStrictLower π A - A := rfl
  rw [hn, hm, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.add_mulVec]
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [blockDiagPart_mulVec_apply,
    blockDiagPart_mulVec_apply, blockStrictLower_mulVec_apply, blockStrictLower_mulVec_apply,
    mulVec_apply_eq_block π A x r]
  constructor <;> intro h' <;> linarith

/-! ### Splittings and convergence -/

/-- **(11.2.6)–(11.2.7).** For a splitting `A = M − N` with `M` nonsingular and `A x = b`, the
iterates `M x⁽ᵏ⁾ = N x⁽ᵏ⁻¹⁾ + b` have errors `e⁽ᵏ⁾ = G^k e⁽⁰⁾`, `G = M⁻¹N`. -/
theorem equation_11_2_7 {A : Matrix (Fin n) (Fin n) ℝ} (s : Stationary.Splitting A)
    {b x : Fin n → ℝ} (hx : A *ᵥ x = b) (x₀ : Fin n → ℝ) (k : ℕ) :
    (s.mulVecStep b)^[k] x₀ - x = s.iterationOperator ^ k *ᵥ (x₀ - x) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', mulVecStep_sub s hx, ih, Matrix.mulVec_mulVec, ← pow_succ']

/-- **(11.2.8).** `[λ α; 0 λ]^k = [λ^k  kαλ^{k−1}; 0  λ^k]` for `k ≥ 1`. The book prints the corner
as `αλ^{k−1}`, which is wrong for `k ≥ 2`; the corner is `k α λ^{k−1}`. -/
theorem equation_11_2_8 {R : Type*} [CommRing R] (l a : R) {k : ℕ} (hk : 1 ≤ k) :
    !![l, a; 0, l] ^ k = !![l ^ k, (k : R) * a * l ^ (k - 1); 0, l ^ k] := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [add_comm 1 j, Nat.add_sub_cancel]
  clear hk
  induction j with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ j ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **Theorem 11.2.1.** Let `A = M − N` be a splitting of a nonsingular `A ∈ ℝ^{n×n}` with `M`
nonsingular. The iteration (11.2.6) converges to `x = A⁻¹b` for all starting vectors `x⁽⁰⁾` if and
only if `ρ(G) < 1`, `G = M⁻¹N`. -/
theorem theorem_11_2_1 {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) (s : Stationary.Splitting A)
    (b : Fin n → ℝ) :
    (∀ x₀, Tendsto (fun k => (s.mulVecStep b)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b))) ↔
      s.iterationOperator.complexSpectralRadius < 1 := by
  have hx : A *ᵥ (A⁻¹ *ᵥ b) = b := Matrix.mulVec_nonsing_inv_mulVec hA b
  rw [← Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one,
    Matrix.tendsto_zero_iff_forall_mulVec_tendsto_zero]
  constructor
  · intro H v
    have := tendsto_sub_nhds_zero_iff.2 (H (A⁻¹ *ᵥ b + v))
    simpa only [equation_11_2_7 s hx, add_sub_cancel_left] using this
  · intro H x₀
    rw [← tendsto_sub_nhds_zero_iff]
    simpa only [equation_11_2_7 s hx] using H (x₀ - A⁻¹ *ᵥ b)

open scoped Matrix.Norms.Frobenius in
/-- **(11.2.9).** If `Qᴴ G Q = T = D + E` is a Schur decomposition of `G ∈ ℂ^{n×n}` (`D` diagonal,
`E` strictly upper triangular) and `ρ(G) = max_i |t_ii| < 1`, then
`‖G^k‖₂ ≤ (1 + 2‖E‖_F/(1 − ρ(G)))^{n−1} ((1 + ρ(G))/2)^k`. The book's proof writes `E = A − D` (it
is `T − D`) and `μ = 2‖E‖₂/(1 − ρ)`; with the 2-norm the display does not follow from (7.3.15),
which needs `‖E‖_F`, the norm stated here. -/
theorem equation_11_2_9 {G Q T : Matrix (Fin n) (Fin n) ℂ} (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hT : star Q * G * Q = T) (hTu : T.IsUpperTriangular) (hρ : (⨆ i, ‖T i i‖) < 1) (k : ℕ) :
    Matrix.lpOpNorm 2 (G ^ k) ≤
      (1 + 2 * ‖Matrix.strictUpper T‖ / (1 - ⨆ i, ‖T i i‖)) ^ (n - 1) *
        ((1 + ⨆ i, ‖T i i‖) / 2) ^ k := by
  set ρ := ⨆ i, ‖T i i‖ with hρdef
  set e := ‖Matrix.strictUpper T‖
  have hρ0 : 0 ≤ ρ := Real.iSup_nonneg fun _ => norm_nonneg _
  have he : 0 ≤ e := norm_nonneg _
  have h1ρ : 0 < 1 - ρ := by linarith
  have hμ : 0 ≤ 2 * e / (1 - ρ) := by positivity
  refine ((GolubVanLoan.Chapter07.lemma_7_3_2 hQ hT hTu hμ).1 k).trans ?_
  have h1μ : 0 < 1 + 2 * e / (1 - ρ) := by positivity
  have hle : e / (1 + 2 * e / (1 - ρ)) ≤ (1 - ρ) / 2 := by
    rw [div_le_iff₀ h1μ]
    have : (1 - ρ) / 2 * (1 + 2 * e / (1 - ρ)) = (1 - ρ) / 2 + e := by
      field_simp
    linarith
  have hb : 0 ≤ ρ + e / (1 + 2 * e / (1 - ρ)) := by positivity
  have := pow_le_pow_left₀ hb (show ρ + e / (1 + 2 * e / (1 - ρ)) ≤ (1 + ρ) / 2 by linarith) k
  exact mul_le_mul_of_nonneg_left this (by positivity)

/-! ### Diagonal dominance, positive definiteness -/

/-- **Theorem 11.2.2.** If `A ∈ ℝ^{n×n}` is strictly diagonally dominant, then the Jacobi iteration
(11.2.4) converges to `x = A⁻¹b`: the iterates of the exact run of (11.2.2) tend to `A⁻¹b` from
every start. -/
theorem theorem_11_2_2 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsStrictDiagDominant)
    (b x₀ : Fin n → ℝ) :
    Tendsto (fun k => (fun x => Id.run (jacobiSweep pure A b x))^[k] x₀) atTop
      (𝓝 (A⁻¹ *ᵥ b)) := by
  have h := hA.isUnit_diagPart
  have hf : (fun x => Id.run (jacobiSweep pure A b x)) =
      (Matrix.jacobiSplitting A h).mulVecStep b :=
    funext fun x => (equation_11_2_4 A h b x).1
  rw [hf]
  exact (theorem_11_2_1 hA.isUnit _ b).2 (Matrix.jacobi_complexSpectralRadius_lt_one hA h) x₀

open scoped Matrix.Norms.Operator in
/-- The display in the proof of Theorem 11.2.2: under strict diagonal dominance
`‖G_J‖_∞ = max_i ∑_{j ≠ i} |a_ij / a_ii| < 1`, so no eigenvalue of `G_J` exceeds `1` in modulus (the
book writes "no eigenvalue of `A`"; it means `G_J`). -/
theorem jacobi_linfty_opNorm_lt_one [NeZero n] {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsStrictDiagDominant) :
    ‖(Matrix.jacobiSplitting A hA.isUnit_diagPart).iterationOperator‖ = A.jacobiContraction ∧
      A.jacobiContraction < 1 :=
  ⟨Matrix.linfty_opNorm_jacobi_iterMatrix A _, hA.jacobiContraction_lt_one⟩

/-- **Theorem 11.2.3.** If `A ∈ ℝ^{n×n}` is symmetric positive definite, then the Gauss–Seidel
iteration (11.2.5) converges for any `x⁽⁰⁾`. -/
theorem theorem_11_2_3 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (b x₀ : Fin n → ℝ) :
    Tendsto (fun k => (fun x => Id.run (gaussSeidelSweep pure A b x))^[k] x₀) atTop
      (𝓝 (A⁻¹ *ᵥ b)) := by
  have h : IsUnit (Matrix.diagPart A) := (Matrix.isUnit_diagPart_iff A).2 fun i => hA.diag_pos.ne'
  have hf : (fun x => Id.run (gaussSeidelSweep pure A b x)) =
      (Matrix.gaussSeidelSplitting A h).mulVecStep b :=
    funext fun x => (equation_11_2_5 A h b x).1
  rw [hf]
  exact (theorem_11_2_1 hA.isUnit _ b).2
    (Matrix.gaussSeidelSplitting_complexSpectralRadius_lt_one_of_posDef hA h) x₀

/-! ### The model problem -/

/-- **(11.2.11).** `T_m = tridiag(−1, 2, −1) ∈ ℝ^{m×m}`. -/
abbrev modelT (m : ℕ) : Matrix (Fin m) (Fin m) ℝ := Matrix.symmTridiagonalToeplitz m (-1) 2

/-- The matrix `E_m = tridiag(1, 0, 1)` of §11.2.6, with `T_m = 2I − E_m`. -/
abbrev modelE (m : ℕ) : Matrix (Fin m) (Fin m) ℝ := Matrix.symmTridiagonalToeplitz m 1 0

/-- **(11.2.10).** The model matrix `I_{n₁} ⊗ T_{n₂} + T_{n₁} ⊗ I_{n₂}`, the Kronecker sum of the
two `T`'s on the grid `Fin n₁ × Fin n₂` (lexicographic order = the book's row-by-row order). -/
noncomputable abbrev poissonMatrix (n₁ n₂ : ℕ) : Matrix (Fin n₁ × Fin n₂) (Fin n₁ × Fin n₂) ℝ :=
  Matrix.kroneckerSum (modelT n₁) (modelT n₂)

/-- §11.2.6: the model system (11.2.10) is symmetric positive definite: chapter 4's
`Chapter04.poisson2D_posDef_bandwidth` (§4.8.3) for the same Kronecker sum. -/
theorem poissonMatrix_posDef (n₁ n₂ : ℕ) : (poissonMatrix n₁ n₂).PosDef := by
  have h := (Chapter04.poisson2D_posDef_bandwidth n₂ n₁).1
  rw [add_comm] at h
  exact h

/-- `T_m = 2I − E_m`. -/
private theorem modelT_eq (m : ℕ) : modelT m = (2 : ℝ) • 1 + (-1 : ℝ) • modelE m := by
  ext i j
  simp only [modelT, modelE, Matrix.symmTridiagonalToeplitz_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> norm_num

/-- The diagonal of the model matrix is `4`. -/
private theorem diagPart_poissonMatrix (n₁ n₂ : ℕ) :
    Matrix.diagPart (poissonMatrix n₁ n₂) = (4 : ℝ) • 1 := by
  ext p q
  rw [Matrix.diagPart_apply, Matrix.smul_apply, Matrix.one_apply]
  split_ifs with hpq
  · subst hpq
    obtain ⟨a, c⟩ := p
    rw [show poissonMatrix n₁ n₂ = Matrix.kroneckerSum (modelT n₁) (modelT n₂) from rfl,
      Matrix.kroneckerSum_apply]
    simp only [modelT, Matrix.symmTridiagonalToeplitz_apply_self, ite_true]
    norm_num
  · simp

/-- The diagonal of the model matrix is nonsingular. -/
theorem isUnit_diagPart_poissonMatrix (n₁ n₂ : ℕ) :
    IsUnit (Matrix.diagPart (poissonMatrix n₁ n₂)) := by
  rw [Matrix.isUnit_diagPart_iff]
  intro p
  have := congrFun (congrFun (diagPart_poissonMatrix n₁ n₂) p) p
  rw [Matrix.diagPart_apply, ite_eq_left rfl] at this
  rw [this]
  simp

/-- **(11.2.12).** `A = I ⊗ T_{n₂} + T_{n₁} ⊗ I = 4I − (I ⊗ E_{n₂}) − (E_{n₁} ⊗ I)`, so the Jacobi
splitting of the model problem has `M_J = 4I` and `N_J = (I ⊗ E_{n₂}) + (E_{n₁} ⊗ I)`. -/
theorem equation_11_2_12 (n₁ n₂ : ℕ) :
    poissonMatrix n₁ n₂ = (4 : ℝ) • 1 - (1 ⊗ₖ modelE n₂) - (modelE n₁ ⊗ₖ 1) ∧
      (Matrix.jacobiSplitting _ (isUnit_diagPart_poissonMatrix n₁ n₂)).m = (4 : ℝ) • 1 ∧
      (Matrix.jacobiSplitting _ (isUnit_diagPart_poissonMatrix n₁ n₂)).n =
        (1 ⊗ₖ modelE n₂) + (modelE n₁ ⊗ₖ 1) := by
  have hA : poissonMatrix n₁ n₂ = (4 : ℝ) • 1 - (1 ⊗ₖ modelE n₂) - (modelE n₁ ⊗ₖ 1) := by
    rw [poissonMatrix, Matrix.kroneckerSum_def, modelT_eq, modelT_eq, Matrix.add_kronecker,
      Matrix.kronecker_add, Matrix.smul_kronecker, Matrix.smul_kronecker, Matrix.kronecker_smul,
      Matrix.kronecker_smul, Matrix.one_kronecker_one]
    module
  have hm : (Matrix.jacobiSplitting _ (isUnit_diagPart_poissonMatrix n₁ n₂)).m = (4 : ℝ) • 1 :=
    diagPart_poissonMatrix n₁ n₂
  refine ⟨hA, hm, ?_⟩
  rw [Stationary.Splitting.n, hm, hA]
  abel

/-! ### The model problem as an array averaging -/

section Grid

variable {n₁ n₂ : ℕ}

/-- The grid point `(i, j)` (the book's 1-based interior index) of the interior unknown `p`
(0-based) in the array `U(0:n₁+1, 0:n₂+1)` of §11.2.6. -/
def gridPoint (p : Fin n₁ × Fin n₂) : Fin (n₁ + 2) × Fin (n₂ + 2) :=
  (⟨p.1 + 1, by omega⟩, ⟨p.2 + 1, by omega⟩)

/-- Distinct unknowns sit at distinct grid points. -/
private theorem gridPoint_injective : Function.Injective (gridPoint (n₁ := n₁) (n₂ := n₂)) := by
  intro p q h
  simp only [gridPoint, Prod.mk.injEq, Fin.mk.injEq, add_left_inj] at h
  exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)

/-- The sum of the four grid neighbours of the interior unknown `p` in the array `U`, in the
book's order `U(i−1, j) + U(i, j+1) + U(i+1, j) + U(i, j−1)`. -/
def gridNeighbourSum (U : Fin (n₁ + 2) × Fin (n₂ + 2) → ℝ) (p : Fin n₁ × Fin n₂) : ℝ :=
  U (⟨p.1, by omega⟩, ⟨p.2 + 1, by omega⟩) + U (⟨p.1 + 1, by omega⟩, ⟨p.2 + 2, by omega⟩) +
    U (⟨p.1 + 2, by omega⟩, ⟨p.2 + 1, by omega⟩) + U (⟨p.1 + 1, by omega⟩, ⟨p.2, by omega⟩)

/-- A grid point is interior when both its indices lie in `1:n`. -/
def IsGridInterior (q : Fin (n₁ + 2) × Fin (n₂ + 2)) : Prop :=
  1 ≤ (q.1 : ℕ) ∧ (q.1 : ℕ) ≤ n₁ ∧ 1 ≤ (q.2 : ℕ) ∧ (q.2 : ℕ) ≤ n₂

/-- Interiority of a grid point is decidable. -/
instance (q : Fin (n₁ + 2) × Fin (n₂ + 2)) : Decidable (IsGridInterior q) := by
  unfold IsGridInterior; infer_instance

/-- The interior unknowns `U(1:n₁, 1:n₂)` of an array, as the vector `u` of (11.2.10). -/
def gridInterior (U : Fin (n₁ + 2) × Fin (n₂ + 2) → ℝ) (p : Fin n₁ × Fin n₂) : ℝ :=
  U (gridPoint p)

/-- A vector of interior unknowns placed on the grid, with zero boundary values. -/
def gridPad (u : Fin n₁ × Fin n₂ → ℝ) (q : Fin (n₁ + 2) × Fin (n₂ + 2)) : ℝ :=
  if h : IsGridInterior q then
    u (⟨q.1 - 1, by simp only [IsGridInterior] at h; omega⟩,
      ⟨q.2 - 1, by simp only [IsGridInterior] at h; omega⟩)
  else 0

/-- The boundary values of an array: `U` on the boundary, zero at the interior points. -/
def gridBoundary (U : Fin (n₁ + 2) × Fin (n₂ + 2) → ℝ) (q : Fin (n₁ + 2) × Fin (n₂ + 2)) : ℝ :=
  if IsGridInterior q then 0 else U q

/-- The right-hand side `b` of (11.2.10) in the Laplace case: at each interior unknown, the sum of
its neighbours that are boundary points of the array. -/
def gridRhs (U : Fin (n₁ + 2) × Fin (n₂ + 2) → ℝ) (p : Fin n₁ × Fin n₂) : ℝ :=
  gridNeighbourSum (gridBoundary U) p

/-- An array is its padded interior plus its boundary values. -/
private theorem gridPad_gridInterior_add_gridBoundary (U : Fin (n₁ + 2) × Fin (n₂ + 2) → ℝ) (q) :
    gridPad (gridInterior U) q + gridBoundary U q = U q := by
  unfold gridPad gridBoundary
  split_ifs with h
  · rw [add_zero, gridInterior]
    simp only [IsGridInterior] at h
    congr 1
    simp only [gridPoint]
    ext <;> simp <;> omega
  · rw [zero_add]

/-- The neighbour sum is additive in the array. -/
private theorem gridNeighbourSum_add (U V : Fin (n₁ + 2) × Fin (n₂ + 2) → ℝ) (p) :
    gridNeighbourSum (fun q => U q + V q) p = gridNeighbourSum U p + gridNeighbourSum V p := by
  unfold gridNeighbourSum; ring

/-- The neighbour sum of an array splits into its interior and boundary parts. -/
private theorem gridNeighbourSum_eq (U : Fin (n₁ + 2) × Fin (n₂ + 2) → ℝ) (p : Fin n₁ × Fin n₂) :
    gridNeighbourSum U p = gridNeighbourSum (gridPad (gridInterior U)) p + gridRhs U p := by
  rw [gridRhs, ← gridNeighbourSum_add]
  simp only [gridPad_gridInterior_add_gridBoundary]

/-- One row of `T_m = tridiag(−1, 2, −1)`, the missing neighbours of the end rows read as zero. -/
private theorem modelT_mulVec_apply {m : ℕ} (v : Fin m → ℝ) (i : Fin m) :
    (modelT m *ᵥ v) i = 2 * v i - (if h : 0 < (i : ℕ) then v ⟨i - 1, by omega⟩ else 0) -
      (if h : (i : ℕ) + 1 < m then v ⟨i + 1, h⟩ else 0) := by
  obtain ⟨N, rfl⟩ : ∃ N, m = N + 1 := ⟨m - 1, by have := i.isLt; omega⟩
  rw [modelT, Matrix.symmTridiagonalToeplitz_mulVec_apply']
  have e : ((i : ℕ) + 1 < N + 1) ↔ (i : ℕ) < N := by omega
  by_cases h1 : 0 < (i : ℕ) <;> by_cases h2 : (i : ℕ) < N <;>
    simp only [h1, h2, e, dite_true, dite_false] <;> ring

private theorem gridPad_north (u : Fin n₁ × Fin n₂ → ℝ) (p : Fin n₁ × Fin n₂) :
    gridPad u (⟨p.1, by omega⟩, ⟨p.2 + 1, by omega⟩) =
      if h : 0 < (p.1 : ℕ) then u (⟨p.1 - 1, by omega⟩, p.2) else 0 := by
  unfold gridPad
  by_cases h : 0 < (p.1 : ℕ)
  · rw [dite_eq_left_of_eq_true (eq_true (by simp only [IsGridInterior]; omega)),
      dite_eq_left_of_eq_true (eq_true h)]
    congr 1
  · rw [dite_eq_right_of_eq_false (eq_false (by simp only [IsGridInterior]; omega)),
      dite_eq_right_of_eq_false (eq_false h)]

private theorem gridPad_south (u : Fin n₁ × Fin n₂ → ℝ) (p : Fin n₁ × Fin n₂) :
    gridPad u (⟨p.1 + 2, by omega⟩, ⟨p.2 + 1, by omega⟩) =
      if h : (p.1 : ℕ) + 1 < n₁ then u (⟨p.1 + 1, h⟩, p.2) else 0 := by
  unfold gridPad
  by_cases h : (p.1 : ℕ) + 1 < n₁
  · rw [dite_eq_left_of_eq_true (eq_true (by simp only [IsGridInterior]; omega)),
      dite_eq_left_of_eq_true (eq_true h)]
    congr 1
  · rw [dite_eq_right_of_eq_false (eq_false (by simp only [IsGridInterior]; omega)),
      dite_eq_right_of_eq_false (eq_false h)]

private theorem gridPad_west (u : Fin n₁ × Fin n₂ → ℝ) (p : Fin n₁ × Fin n₂) :
    gridPad u (⟨p.1 + 1, by omega⟩, ⟨p.2, by omega⟩) =
      if h : 0 < (p.2 : ℕ) then u (p.1, ⟨p.2 - 1, by omega⟩) else 0 := by
  unfold gridPad
  by_cases h : 0 < (p.2 : ℕ)
  · rw [dite_eq_left_of_eq_true (eq_true (by simp only [IsGridInterior]; omega)),
      dite_eq_left_of_eq_true (eq_true h)]
    congr 1
  · rw [dite_eq_right_of_eq_false (eq_false (by simp only [IsGridInterior]; omega)),
      dite_eq_right_of_eq_false (eq_false h)]

private theorem gridPad_east (u : Fin n₁ × Fin n₂ → ℝ) (p : Fin n₁ × Fin n₂) :
    gridPad u (⟨p.1 + 1, by omega⟩, ⟨p.2 + 2, by omega⟩) =
      if h : (p.2 : ℕ) + 1 < n₂ then u (p.1, ⟨p.2 + 1, h⟩) else 0 := by
  unfold gridPad
  by_cases h : (p.2 : ℕ) + 1 < n₂
  · rw [dite_eq_left_of_eq_true (eq_true (by simp only [IsGridInterior]; omega)),
      dite_eq_left_of_eq_true (eq_true h)]
    congr 1
  · rw [dite_eq_right_of_eq_false (eq_false (by simp only [IsGridInterior]; omega)),
      dite_eq_right_of_eq_false (eq_false h)]

/-- **The model matrix is the five-point stencil**: row `p` of `A u` is `4 u_p` minus the sum of the
neighbours of `p`, those outside the interior read as zero. -/
theorem poissonMatrix_mulVec_apply (u : Fin n₁ × Fin n₂ → ℝ) (p : Fin n₁ × Fin n₂) :
    (poissonMatrix n₁ n₂ *ᵥ u) p = 4 * u p - gridNeighbourSum (gridPad u) p := by
  have hsum : (poissonMatrix n₁ n₂ *ᵥ u) p =
      (modelT n₁ *ᵥ fun a => u (a, p.2)) p.1 + (modelT n₂ *ᵥ fun c => u (p.1, c)) p.2 := by
    obtain ⟨i, j⟩ := p
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, poissonMatrix,
      Matrix.kroneckerSum_apply, add_mul, ite_mul, zero_mul, Finset.sum_add_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_ite_eq]; simp
    · rw [Finset.sum_eq_single i (fun a _ ha => Finset.sum_eq_zero fun c _ => by
        simp [Ne.symm ha]) (by simp)]
      simp
  rw [hsum, modelT_mulVec_apply, modelT_mulVec_apply, gridNeighbourSum, gridPad_north,
    gridPad_south, gridPad_west, gridPad_east]
  ring

/-- The diagonal entries of the model matrix are `4`. -/
private theorem poissonMatrix_apply_self (p : Fin n₁ × Fin n₂) : poissonMatrix n₁ n₂ p p = 4 := by
  obtain ⟨i, j⟩ := p
  rw [poissonMatrix, Matrix.kroneckerSum_apply]
  simp only [modelT, Matrix.symmTridiagonalToeplitz_apply_self, ite_true]
  norm_num

/-- The interior unknowns in the order of the book's double loop `i = 1:n₁`, `j = 1:n₂`. -/
private def gridList (n₁ n₂ : ℕ) : List (Fin n₁ × Fin n₂) :=
  (List.finRange n₁).flatMap fun i => (List.finRange n₂).map (Prod.mk i)

private theorem mem_gridList (p : Fin n₁ × Fin n₂) : p ∈ gridList n₁ n₂ := by
  simp [gridList]

/-- The double loop visits the unknowns in lexicographic order. -/
private theorem pairwise_gridList :
    (gridList n₁ n₂).Pairwise fun p q => toLex p < toLex q := by
  rw [gridList, List.pairwise_flatMap]
  refine ⟨fun i _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    refine (List.pairwise_lt_finRange n₂).imp fun {a b} h => ?_
    exact Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨rfl, h⟩)
  · refine (List.pairwise_lt_finRange n₁).imp fun h x hx y hy => ?_
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hy
    exact Prod.Lex.toLex_lt_toLex.2 (Or.inl h)

/-- The book's double loop is one loop over `gridList`. -/
private theorem foldl_foldl_eq_foldl_gridList {σ : Type*} (F : Fin n₁ × Fin n₂ → σ → σ) (s : σ) :
    (List.finRange n₁).foldl (fun s i => (List.finRange n₂).foldl (fun s j => F (i, j) s) s) s =
      (gridList n₁ n₂).foldl (fun s p => F p s) s := by
  rw [gridList, List.foldl_flatMap]
  simp only [List.foldl_map]

/-- Grid points are interior. -/
private theorem isGridInterior_gridPoint (p : Fin n₁ × Fin n₂) :
    IsGridInterior (gridPoint p) := by
  simp only [IsGridInterior, gridPoint]; omega

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The average `(W(i−1, j) + W(i, j+1) + W(i+1, j) + W(i, j−1))/4` of the four grid neighbours of
the unknown `p` in the array `W`, summed in the book's order, every operation rounded. -/
noncomputable def gridAverage (W : Fin (n₁ + 2) × Fin (n₂ + 2) → ℝ) (p : Fin n₁ × Fin n₂) :
    M ℝ := do
  let s₁ ← rnd (W (⟨p.1, by omega⟩, ⟨p.2 + 1, by omega⟩) +
    W (⟨p.1 + 1, by omega⟩, ⟨p.2 + 2, by omega⟩))
  let s₂ ← rnd (s₁ + W (⟨p.1 + 2, by omega⟩, ⟨p.2 + 1, by omega⟩))
  let s₃ ← rnd (s₂ + W (⟨p.1 + 1, by omega⟩, ⟨p.2, by omega⟩))
  rnd (s₃ / 4)

/-- **The array form of Jacobi** (§11.2.6):
```
V = U
for i = 1:n₁
    for j = 1:n₂
        U(i,j) = (V(i−1,j) + V(i,j+1) + V(i+1,j) + V(i,j−1))/4
    end
end
```
on the array `U(0:n₁+1, 0:n₂+1)` (indexed by pairs), every average read from the copy `V`. -/
noncomputable def poissonJacobiArray (U : Fin (n₁ + 2) × Fin (n₂ + 2) → ℝ) :
    M (Fin (n₁ + 2) × Fin (n₂ + 2) → ℝ) :=
  let V := U
  (List.finRange n₁).foldlM (fun U i => (List.finRange n₂).foldlM (fun U j => do
    let u ← gridAverage rnd V (i, j)
    pure (Function.update U (gridPoint (i, j)) u)) U) U

/-- **The array form of Gauss–Seidel** (§11.2.6):
```
for i = 1:n₁
    for j = 1:n₂
        U(i,j) = (U(i−1,j) + U(i,j+1) + U(i+1,j) + U(i,j−1))/4
    end
end
```
in place, so that `U(i−1, j)` and `U(i, j−1)` are already the new values. -/
noncomputable def poissonGaussSeidelArray (U : Fin (n₁ + 2) × Fin (n₂ + 2) → ℝ) :
    M (Fin (n₁ + 2) × Fin (n₂ + 2) → ℝ) :=
  (List.finRange n₁).foldlM (fun U i => (List.finRange n₂).foldlM (fun U j => do
    let u ← gridAverage rnd U (i, j)
    pure (Function.update U (gridPoint (i, j)) u)) U) U

end Programs

private theorem poissonJacobiArray_run (U : Fin (n₁ + 2) × Fin (n₂ + 2) → ℝ) :
    Id.run (poissonJacobiArray pure U) = (gridList n₁ n₂).foldl
      (fun W p => Function.update W (gridPoint p) (gridNeighbourSum U p / 4)) U := by
  rw [← foldl_foldl_eq_foldl_gridList]
  simp only [poissonJacobiArray, List.idRun_foldlM]
  rfl

private theorem poissonGaussSeidelArray_run (U : Fin (n₁ + 2) × Fin (n₂ + 2) → ℝ) :
    Id.run (poissonGaussSeidelArray pure U) = (gridList n₁ n₂).foldl
      (fun W p => Function.update W (gridPoint p) (gridNeighbourSum W p / 4)) U := by
  rw [← foldl_foldl_eq_foldl_gridList]
  simp only [poissonGaussSeidelArray, List.idRun_foldlM]
  rfl

/-- The array loops leave the boundary of the array fixed. -/
private theorem foldl_grid_boundary
    (F : Fin n₁ × Fin n₂ → (Fin (n₁ + 2) × Fin (n₂ + 2) → ℝ) → ℝ)
    (U : Fin (n₁ + 2) × Fin (n₂ + 2) → ℝ) {q : Fin (n₁ + 2) × Fin (n₂ + 2)}
    (hq : ¬ IsGridInterior q) :
    (gridList n₁ n₂).foldl (fun W p => Function.update W (gridPoint p) (F p W)) U q = U q :=
  List.foldl_update_apply_of_forall_ne gridPoint F (k := q) (fun p _ h =>
    hq (h ▸ isGridInterior_gridPoint p)) U

/-- Row `p` of the off-diagonal part of the model matrix: minus the neighbour sum. -/
private theorem sum_erase_poissonMatrix (u : Fin n₁ × Fin n₂ → ℝ) (p : Fin n₁ × Fin n₂) :
    ∑ q ∈ univ.erase p, poissonMatrix n₁ n₂ p q * u q = -gridNeighbourSum (gridPad u) p := by
  have h := Finset.sum_erase_add univ (fun q => poissonMatrix n₁ n₂ p q * u q) (mem_univ p)
  have h' := poissonMatrix_mulVec_apply u p
  rw [Matrix.mulVec, dotProduct] at h'
  rw [poissonMatrix_apply_self] at h
  linarith

/-- **§11.2.6: the array update is Jacobi.** One pass of the array averaging, with the book's copy
`V = U`, is one Jacobi step (11.2.4) for the model system (11.2.10) `A u = b`: its interior is
`M_J⁻¹(N_J u + b)` for `u = U(1:n₁, 1:n₂)` and `b` the sum of the boundary neighbours of each
unknown (the Laplace case of the model problem: fixed boundary values, no source term), and the
boundary of the array is left fixed. -/
theorem poissonJacobiArray_eq (U : Fin (n₁ + 2) × Fin (n₂ + 2) → ℝ) :
    gridInterior (Id.run (poissonJacobiArray pure U)) =
        (Matrix.jacobiSplitting _ (isUnit_diagPart_poissonMatrix n₁ n₂)).mulVecStep (gridRhs U)
          (gridInterior U) ∧
      ∀ q, ¬ IsGridInterior q → Id.run (poissonJacobiArray pure U) q = U q := by
  rw [poissonJacobiArray_run]
  refine ⟨?_, fun q hq => foldl_grid_boundary _ U hq⟩
  rw [← Matrix.jorSweep_one_eq_mulVecStep]
  funext p
  obtain ⟨w, -, -, hw⟩ := List.exists_foldl_update_apply_of_pairwise_rel gridPoint
    (fun p q => toLex p < toLex q) (fun _ _ h h' => lt_asymm h h')
    (fun p _ => gridNeighbourSum U p / 4) gridPoint_injective.injOn pairwise_gridList U
    (mem_gridList p)
  rw [gridInterior, hw, Matrix.jorSweep, sum_erase_poissonMatrix, poissonMatrix_apply_self,
    gridNeighbourSum_eq]
  ring

/-- The model matrix with its unknowns in the book's (row-by-row, lexicographic) order, the index
type on which Gauss–Seidel is defined. -/
noncomputable abbrev poissonMatrixLex (n₁ n₂ : ℕ) :
    Matrix (Lex (Fin n₁ × Fin n₂)) (Lex (Fin n₁ × Fin n₂)) ℝ :=
  (poissonMatrix n₁ n₂).submatrix ofLex ofLex

/-- The diagonal of the reordered model matrix is nonsingular. -/
theorem isUnit_diagPart_poissonMatrixLex (n₁ n₂ : ℕ) :
    IsUnit (Matrix.diagPart (poissonMatrixLex n₁ n₂)) := by
  rw [Matrix.isUnit_diagPart_iff]
  intro p
  change poissonMatrix n₁ n₂ (ofLex p) (ofLex p) ≠ 0
  rw [poissonMatrix_apply_self]
  norm_num

/-- Row `p` of the reordered model matrix split at the diagonal. -/
private theorem sum_lt_add_sum_gt_poissonMatrixLex (u : Lex (Fin n₁ × Fin n₂) → ℝ)
    (p : Lex (Fin n₁ × Fin n₂)) :
    ∑ q ∈ univ.filter (· < p), poissonMatrixLex n₁ n₂ p q * u q +
        ∑ q ∈ univ.filter (p < ·), poissonMatrixLex n₁ n₂ p q * u q =
      -gridNeighbourSum (gridPad fun r => u (toLex r)) (ofLex p) := by
  rw [← sum_erase_poissonMatrix]
  rw [← Finset.sum_union (Finset.disjoint_filter.2 fun q _ h1 h2 => lt_asymm h1 h2),
    ← Finset.filter_or]
  refine Finset.sum_nbij' ofLex toLex (fun q hq => ?_) (fun q hq => ?_) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun q _ => rfl)
  · simp only [Finset.mem_filter, mem_univ, true_and] at hq
    refine Finset.mem_erase.2 ⟨fun h => ?_, mem_univ _⟩
    have hpq : q = p := h
    rcases hq with h' | h' <;> exact lt_irrefl p (hpq ▸ h')
  · have hq' := (Finset.mem_erase.1 hq).1
    simp only [Finset.mem_filter, mem_univ, true_and]
    exact lt_or_gt_of_ne fun h => hq' (congrArg ofLex h)

/-- **§11.2.6: the in-place array update is Gauss–Seidel.** One pass of the in-place averaging is
one Gauss–Seidel step (11.2.5) for the model system with the unknowns in the book's row-by-row
order (the lexicographic order of the pairs, in which the loop visits them and in which the
neighbours `(i−1, j)` and `(i, j−1)` precede `(i, j)`), for the same `b` as in
`poissonJacobiArray_eq`; the boundary of the array is left fixed. -/
theorem poissonGaussSeidelArray_eq (U : Fin (n₁ + 2) × Fin (n₂ + 2) → ℝ) :
    (fun q => gridInterior (Id.run (poissonGaussSeidelArray pure U)) (ofLex q)) =
        (Matrix.gaussSeidelSplitting _ (isUnit_diagPart_poissonMatrixLex n₁ n₂)).mulVecStep
          (fun q => gridRhs U (ofLex q)) (fun q => gridInterior U (ofLex q)) ∧
      ∀ q, ¬ IsGridInterior q → Id.run (poissonGaussSeidelArray pure U) q = U q := by
  rw [poissonGaussSeidelArray_run]
  refine ⟨?_, fun q hq => foldl_grid_boundary _ U hq⟩
  rw [← Matrix.sorSweep_one_eq_mulVecStep]
  set Z := (gridList n₁ n₂).foldl
    (fun W p => Function.update W (gridPoint p) (gridNeighbourSum W p / 4)) U
  set A' := poissonMatrixLex n₁ n₂
  set b' : Lex (Fin n₁ × Fin n₂) → ℝ := fun q => gridRhs U (ofLex q)
  set x' : Lex (Fin n₁ × Fin n₂) → ℝ := fun q => gridInterior U (ofLex q)
  refine eq_of_forall_eq_apply (· < ·) wellFounded_lt
    (fun q u => 1 / A' q q * (b' q - ∑ j ∈ univ.filter (· < q), A' q j * u j
      - ∑ j ∈ univ.filter (q < ·), A' q j * x' j) + (1 - 1) * x' q) ?_ (fun q => ?_)
    (fun q => Matrix.sorSweep_apply A' (isUnit_diagPart_poissonMatrixLex n₁ n₂) 1 b' x' q)
  · intro q u v huv
    rw [Finset.sum_congr rfl fun j hj => by rw [huv j (Finset.mem_filter.1 hj).2]]
  · obtain ⟨w, hw₁, hw₂, hw₃⟩ := List.exists_foldl_update_apply_of_pairwise_rel gridPoint
      (fun p q => toLex p < toLex q) (fun _ _ h h' => lt_asymm h h')
      (fun p W => gridNeighbourSum W p / 4) gridPoint_injective.injOn pairwise_gridList U
      (mem_gridList (ofLex q))
    set u'' : Fin n₁ × Fin n₂ → ℝ := fun r =>
      if toLex r < q then Z (gridPoint r) else U (gridPoint r) with hu''
    have hint : gridInterior w = u'' := by
      funext r
      simp only [gridInterior, hu'']
      split_ifs with hr
      · exact hw₁ r (mem_gridList r) hr
      · refine hw₂ _ fun r' _ hr' h => hr ?_
        rw [← gridPoint_injective h]
        exact hr'
    have hbd : gridBoundary w = gridBoundary U := by
      funext k
      unfold gridBoundary
      split_ifs with hk
      · rfl
      · exact hw₂ k fun r _ _ h => hk (h ▸ isGridInterior_gridPoint r)
    have hsplit := sum_lt_add_sum_gt_poissonMatrixLex (fun j => u'' (ofLex j)) q
    have hlt : ∑ j ∈ univ.filter (· < q), A' q j * gridInterior Z (ofLex j) =
        ∑ j ∈ univ.filter (· < q), A' q j * u'' (ofLex j) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : toLex (ofLex j) < q := (Finset.mem_filter.1 hj).2
      simp only [hu'', gridInterior, hj', ite_true]
    have hgt : ∑ j ∈ univ.filter (q < ·), A' q j * x' j =
        ∑ j ∈ univ.filter (q < ·), A' q j * u'' (ofLex j) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : ¬ toLex (ofLex j) < q := fun h =>
        lt_asymm h (Finset.mem_filter.1 hj).2
      simp only [x', hu'', gridInterior, hj', ite_false]
    have hq : A' q q = 4 := poissonMatrix_apply_self (ofLex q)
    rw [show gridInterior Z (ofLex q) = gridNeighbourSum w (ofLex q) / 4 from hw₃, hlt, hgt, hq,
      gridNeighbourSum_eq, hint, gridRhs, hbd]
    simp only [b', gridRhs]
    have hpad : (gridPad fun r => u'' (ofLex (toLex r))) = gridPad u'' := rfl
    rw [hpad] at hsplit
    linarith

end Grid

/-- **(11.2.14).** `μ_k^{(m)} = 2 cos(kπ/(m + 1))`, `k = 1:m` (0-based: `2 cos((k + 1)π/(m + 1))`),
the eigenvalues of `E_m`. -/
noncomputable def modelEEigenvalues (m : ℕ) : Fin m → ℝ :=
  fun k => 2 * Real.cos ((((k : ℕ) : ℝ) + 1) * Real.pi / ((m : ℝ) + 1))

/-- The sine transform matrix `S_m` is nonsingular (§4.8.6, `Chapter04.dd_eigen`). -/
private theorem isUnit_dst1 (m : ℕ) : IsUnit (Matrix.dst1 m) :=
  (GolubVanLoan.Chapter04.dd_eigen m).2.1

/-- `E_m S_m = S_m D_m`, column by column the eigenpairs of `E_m`. -/
private theorem modelE_mul_dst1 (m : ℕ) :
    modelE m * Matrix.dst1 m = Matrix.dst1 m * Matrix.diagonal (modelEEigenvalues m) := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  have := congrFun (Matrix.symmTridiagonalToeplitz_mulVec_sineVec (a := 1) (b := 0) j) i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
  simp only [Matrix.dst1_apply_eq_sineVec, modelEEigenvalues]
  rw [this]
  ring

/-- **(11.2.13).** `S_m⁻¹ E_m S_m = D_m = diag(μ_1^{(m)}, …, μ_m^{(m)})` with `S_m` the sine
transform matrix `[S_m]_kj = sin(kjπ/(m + 1))` (the book's P11.2.7). -/
theorem equation_11_2_13 (m : ℕ) :
    (Matrix.dst1 m)⁻¹ * modelE m * Matrix.dst1 m = Matrix.diagonal (modelEEigenvalues m) := by
  have hS := (Matrix.isUnit_iff_isUnit_det _).1 (isUnit_dst1 m)
  rw [Matrix.mul_assoc, modelE_mul_dst1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hS,
    Matrix.one_mul]

/-- Conjugating a Kronecker product by a Kronecker product of nonsingular matrices. -/
private theorem kronecker_conj {m₁ m₂ : ℕ} (S₁ X₁ : Matrix (Fin m₁) (Fin m₁) ℝ)
    (S₂ X₂ : Matrix (Fin m₂) (Fin m₂) ℝ) :
    (S₁ ⊗ₖ S₂)⁻¹ * (X₁ ⊗ₖ X₂) * (S₁ ⊗ₖ S₂) = (S₁⁻¹ * X₁ * S₁) ⊗ₖ (S₂⁻¹ * X₂ * S₂) := by
  rw [Matrix.inv_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]

/-- The sine basis diagonalizes `I ⊗ E_{n₂}`. -/
private theorem conj_one_kronecker_modelE (n₁ n₂ : ℕ) :
    (Matrix.dst1 n₁ ⊗ₖ Matrix.dst1 n₂)⁻¹ * (1 ⊗ₖ modelE n₂) * (Matrix.dst1 n₁ ⊗ₖ Matrix.dst1 n₂) =
      1 ⊗ₖ Matrix.diagonal (modelEEigenvalues n₂) := by
  rw [kronecker_conj, equation_11_2_13, Matrix.mul_one,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_dst1 n₁))]

/-- The sine basis diagonalizes `E_{n₁} ⊗ I`. -/
private theorem conj_modelE_kronecker_one (n₁ n₂ : ℕ) :
    (Matrix.dst1 n₁ ⊗ₖ Matrix.dst1 n₂)⁻¹ * (modelE n₁ ⊗ₖ 1) * (Matrix.dst1 n₁ ⊗ₖ Matrix.dst1 n₂) =
      Matrix.diagonal (modelEEigenvalues n₁) ⊗ₖ 1 := by
  rw [kronecker_conj, equation_11_2_13, Matrix.mul_one,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_dst1 n₂))]

/-- `(4I)⁻¹ = ¼ I`. -/
private theorem inv_four_smul_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ((4 : ℝ) • (1 : Matrix ι ι ℝ))⁻¹ = (1 / 4 : ℝ) • 1 := by
  refine Matrix.inv_eq_left_inv ?_
  rw [smul_mul_smul_comm, Matrix.one_mul]
  norm_num

/-- The Jacobi iteration matrix of the model problem is `¼ ((I ⊗ E_{n₂}) + (E_{n₁} ⊗ I))`. -/
private theorem jacobi_poisson_iterationOperator (n₁ n₂ : ℕ) :
    (Matrix.jacobiSplitting _ (isUnit_diagPart_poissonMatrix n₁ n₂)).iterationOperator =
      (1 / 4 : ℝ) • ((1 ⊗ₖ modelE n₂) + (modelE n₁ ⊗ₖ 1)) := by
  obtain ⟨-, hm, hn⟩ := equation_11_2_12 n₁ n₂
  rw [Stationary.Splitting.iterationOperator_eq, hm, hn, ← Matrix.nonsing_inv_eq_ringInverse,
    inv_four_smul_one, Matrix.smul_mul, Matrix.one_mul]

/-- **§11.2.6, the display after (11.2.14).** With `S = S_{n₁} ⊗ S_{n₂}`,
`S⁻¹ (M_J⁻¹ N_J) S = (I_{n₁} ⊗ D_{n₂} + D_{n₁} ⊗ I_{n₂}) / 4`. -/
theorem jacobi_poisson_diagonal (n₁ n₂ : ℕ) :
    (Matrix.dst1 n₁ ⊗ₖ Matrix.dst1 n₂)⁻¹ *
        (Matrix.jacobiSplitting _ (isUnit_diagPart_poissonMatrix n₁ n₂)).iterationOperator *
        (Matrix.dst1 n₁ ⊗ₖ Matrix.dst1 n₂) =
      (1 / 4 : ℝ) • (1 ⊗ₖ Matrix.diagonal (modelEEigenvalues n₂) +
        Matrix.diagonal (modelEEigenvalues n₁) ⊗ₖ 1) := by
  rw [jacobi_poisson_iterationOperator, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add,
    Matrix.add_mul, conj_one_kronecker_modelE, conj_modelE_kronecker_one]

/-- The sine basis of the grid is nonsingular. -/
private theorem isUnit_dst1_kronecker (n₁ n₂ : ℕ) :
    IsUnit (Matrix.dst1 n₁ ⊗ₖ Matrix.dst1 n₂) :=
  Matrix.IsUnit.kronecker (isUnit_dst1 n₁) (isUnit_dst1 n₂)

/-- **The spectral radius of a real diagonal matrix** as a real number: if `|d i| ≤ r` for all `i`,
with equality at some `i₀`, then `ρ(diag d) = r`. -/
private theorem complexSpectralRadius_diagonal_eq_ofReal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) {r : ℝ} (hle : ∀ i, |d i| ≤ r) {i₀ : ι} (h₀ : |d i₀| = r) :
    (Matrix.diagonal d).complexSpectralRadius = ENNReal.ofReal r := by
  rw [Matrix.complexSpectralRadius_diagonal]
  have e : ∀ x : ℝ, ((‖x‖₊ : NNReal) : ENNReal) = ENNReal.ofReal |x| := fun x => by
    rw [← enorm_eq_nnnorm]; exact Real.enorm_eq_ofReal_abs x
  refine le_antisymm (iSup_le fun i => ?_) (le_iSup_of_le i₀ ?_)
  · rw [e]; exact ENNReal.ofReal_le_ofReal (hle i)
  · rw [e, h₀]

/-- `|cos(kπ/(m + 1))| ≤ cos(π/(m + 1))` for `k = 1:m`. -/
private theorem abs_cos_le (m : ℕ) (k : Fin m) :
    |Real.cos ((((k : ℕ) : ℝ) + 1) * Real.pi / ((m : ℝ) + 1))| ≤
      Real.cos (Real.pi / ((m : ℝ) + 1)) := by
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hk : ((k : ℕ) : ℝ) + 1 ≤ m := by exact_mod_cast k.isLt
  set θ := Real.pi / ((m : ℝ) + 1)
  have hθ0 : 0 ≤ θ := by positivity
  have ht : (((k : ℕ) : ℝ) + 1) * Real.pi / ((m : ℝ) + 1) = (((k : ℕ) : ℝ) + 1) * θ := by
    rw [mul_div_assoc]
  rw [ht]
  have h1 : θ ≤ (((k : ℕ) : ℝ) + 1) * θ := le_mul_of_one_le_left hθ0 (by linarith)
  have h2 : (((k : ℕ) : ℝ) + 1) * θ ≤ Real.pi - θ := by
    have : (((k : ℕ) : ℝ) + 1) * θ + θ = (((k : ℕ) : ℝ) + 2) * θ := by ring
    have h3 : (((k : ℕ) : ℝ) + 2) * θ ≤ Real.pi := by
      rw [show θ = Real.pi / ((m : ℝ) + 1) from rfl, ← mul_div_assoc, div_le_iff₀ hm]
      nlinarith [Real.pi_pos]
    linarith
  have hθπ : θ ≤ Real.pi := by
    rw [show θ = Real.pi / ((m : ℝ) + 1) from rfl, div_le_iff₀ hm]
    nlinarith [Real.pi_pos]
  rw [abs_le]
  constructor
  · rw [neg_le, ← Real.cos_pi_sub]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hθ0 (by linarith) (by linarith)
  · exact Real.cos_le_cos_of_nonneg_of_le_pi hθ0 (by linarith) h1

/-- `cos(π/(m + 1)) ≥ 0` for `m ≥ 1`. -/
private theorem cos_pi_div_nonneg (m : ℕ) [NeZero m] : 0 ≤ Real.cos (Real.pi / ((m : ℝ) + 1)) := by
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne m)
  refine Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩
  · have : 0 ≤ Real.pi / ((m : ℝ) + 1) := by positivity
    linarith [Real.pi_pos]
  · exact div_le_div_of_nonneg_left Real.pi_pos.le two_pos (by linarith)

/-- `cos(π/(m + 1)) < 1`. -/
private theorem cos_pi_div_lt_one (m : ℕ) : Real.cos (Real.pi / ((m : ℝ) + 1)) < 1 := by
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0 : ℝ))
    (div_le_self Real.pi_pos.le (by linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]))
    (by positivity : (0 : ℝ) < Real.pi / ((m : ℝ) + 1))
  rwa [Real.cos_zero] at h

/-- **(11.2.15).** `ρ(M_J⁻¹ N_J) = (2 cos(π/(n₁ + 1)) + 2 cos(π/(n₂ + 1)))/4` for the model problem
(the book's P11.2.8). -/
theorem equation_11_2_15 (n₁ n₂ : ℕ) [NeZero n₁] [NeZero n₂] :
    Matrix.complexSpectralRadius
        (Matrix.jacobiSplitting _ (isUnit_diagPart_poissonMatrix n₁ n₂)).iterationOperator =
      ENNReal.ofReal ((2 * Real.cos (Real.pi / ((n₁ : ℝ) + 1)) +
        2 * Real.cos (Real.pi / ((n₂ : ℝ) + 1))) / 4) := by
  rw [← Matrix.complexSpectralRadius_conj (isUnit_dst1_kronecker n₁ n₂), jacobi_poisson_diagonal]
  have hd : (1 / 4 : ℝ) • (1 ⊗ₖ Matrix.diagonal (modelEEigenvalues n₂) +
      Matrix.diagonal (modelEEigenvalues n₁) ⊗ₖ 1) =
      Matrix.diagonal fun p : Fin n₁ × Fin n₂ =>
        (modelEEigenvalues n₁ p.1 + modelEEigenvalues n₂ p.2) / 4 := by
    have h₁ : (1 : Matrix (Fin n₁) (Fin n₁) ℝ) = Matrix.diagonal fun _ => 1 :=
      Matrix.diagonal_one.symm
    have h₂ : (1 : Matrix (Fin n₂) (Fin n₂) ℝ) = Matrix.diagonal fun _ => 1 :=
      Matrix.diagonal_one.symm
    rw [h₁, h₂, Matrix.diagonal_kronecker_diagonal,
      Matrix.diagonal_kronecker_diagonal, Matrix.diagonal_add, ← Matrix.diagonal_smul]
    congr 1
    funext p
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hd]
  refine complexSpectralRadius_diagonal_eq_ofReal _ (fun p => ?_) (i₀ := (0, 0)) ?_
  · have h1 := abs_cos_le n₁ p.1
    have h2 := abs_cos_le n₂ p.2
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    refine (abs_add_le _ _).trans ?_
    simp only [modelEEigenvalues, abs_mul, abs_two]
    linarith
  · simp only [modelEEigenvalues, Fin.val_zero, Nat.cast_zero, zero_add, one_mul]
    rw [abs_of_nonneg]
    have := cos_pi_div_nonneg n₁
    have := cos_pi_div_nonneg n₂
    positivity

/-! ### The alternating-direction iteration (11.2.16) -/

/-- `4I − E_m = tridiag(−1, 4, −1)` is nonsingular. -/
private theorem isUnit_four_sub_modelE (m : ℕ) :
    IsUnit ((4 : ℝ) • (1 : Matrix (Fin m) (Fin m) ℝ) - modelE m) := by
  have h : (4 : ℝ) • (1 : Matrix (Fin m) (Fin m) ℝ) - modelE m =
      Matrix.symmTridiagonalToeplitz m (-1) 4 := by
    ext i j
    simp only [modelE, Matrix.symmTridiagonalToeplitz_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul]
    split_ifs <;> norm_num
  rw [h]
  exact (Matrix.posDef_symmTridiagonalToeplitz m (by norm_num)).isUnit

/-- `4I − (I ⊗ Y) = I ⊗ (4I − Y)`. -/
private theorem four_smul_one_sub_one_kronecker {m₁ m₂ : ℕ} (Y : Matrix (Fin m₂) (Fin m₂) ℝ) :
    (4 : ℝ) • (1 : Matrix (Fin m₁ × Fin m₂) (Fin m₁ × Fin m₂) ℝ) -
        ((1 : Matrix (Fin m₁) (Fin m₁) ℝ) ⊗ₖ Y) = 1 ⊗ₖ ((4 : ℝ) • 1 - Y) := by
  rw [sub_eq_add_neg, sub_eq_add_neg, Matrix.kronecker_add, ← neg_one_smul ℝ Y,
    ← neg_one_smul ℝ ((1 : Matrix (Fin m₁) (Fin m₁) ℝ) ⊗ₖ Y), Matrix.kronecker_smul,
    Matrix.kronecker_smul, Matrix.one_kronecker_one]

/-- `4I − (X ⊗ I) = (4I − X) ⊗ I`. -/
private theorem four_smul_one_sub_kronecker_one {m₁ m₂ : ℕ} (X : Matrix (Fin m₁) (Fin m₁) ℝ) :
    (4 : ℝ) • (1 : Matrix (Fin m₁ × Fin m₂) (Fin m₁ × Fin m₂) ℝ) -
        (X ⊗ₖ (1 : Matrix (Fin m₂) (Fin m₂) ℝ)) = ((4 : ℝ) • 1 - X) ⊗ₖ 1 := by
  rw [sub_eq_add_neg, sub_eq_add_neg, Matrix.add_kronecker, ← neg_one_smul ℝ X,
    ← neg_one_smul ℝ (X ⊗ₖ (1 : Matrix (Fin m₂) (Fin m₂) ℝ)), Matrix.smul_kronecker,
    Matrix.smul_kronecker, Matrix.one_kronecker_one]

/-- `4I − (I ⊗ E_{n₂})` is nonsingular: it is `I ⊗ (4I − E_{n₂})`. -/
private theorem isUnit_adiX (n₁ n₂ : ℕ) :
    IsUnit ((4 : ℝ) • (1 : Matrix (Fin n₁ × Fin n₂) (Fin n₁ × Fin n₂) ℝ) - (1 ⊗ₖ modelE n₂)) := by
  rw [four_smul_one_sub_one_kronecker]
  exact Matrix.IsUnit.kronecker isUnit_one (isUnit_four_sub_modelE n₂)

/-- `4I − (E_{n₁} ⊗ I)` is nonsingular: it is `(4I − E_{n₁}) ⊗ I`. -/
private theorem isUnit_adiY (n₁ n₂ : ℕ) :
    IsUnit ((4 : ℝ) • (1 : Matrix (Fin n₁ × Fin n₂) (Fin n₁ × Fin n₂) ℝ) - (modelE n₁ ⊗ₖ 1)) := by
  rw [four_smul_one_sub_kronecker_one]
  exact Matrix.IsUnit.kronecker (isUnit_four_sub_modelE n₁) isUnit_one

/-- The splitting `A = M_x − N_x` of §11.2.6, `M_x = 4I − (I ⊗ E_{n₂})`, `N_x = E_{n₁} ⊗ I`. -/
noncomputable def adiSplittingX (n₁ n₂ : ℕ) : Stationary.Splitting (poissonMatrix n₁ n₂) :=
  ⟨(4 : ℝ) • 1 - (1 ⊗ₖ modelE n₂), isUnit_adiX n₁ n₂⟩

/-- The splitting `A = M_y − N_y` of §11.2.6, `M_y = 4I − (E_{n₁} ⊗ I)`, `N_y = I ⊗ E_{n₂}`. -/
noncomputable def adiSplittingY (n₁ n₂ : ℕ) : Stationary.Splitting (poissonMatrix n₁ n₂) :=
  ⟨(4 : ℝ) • 1 - (modelE n₁ ⊗ₖ 1), isUnit_adiY n₁ n₂⟩

/-- **(11.2.16).** The alternating-direction step for the model problem,
`M_x v⁽ᵏ⁾ = N_x u⁽ᵏ⁻¹⁾ + b`, `M_y u⁽ᵏ⁾ = N_y v⁽ᵏ⁾ + b`, as an exact map (the book solves two linear
systems and fixes no operation order). -/
noncomputable def adiStep (n₁ n₂ : ℕ) (b u : Fin n₁ × Fin n₂ → ℝ) : Fin n₁ × Fin n₂ → ℝ :=
  (adiSplittingY n₁ n₂).mulVecStep b ((adiSplittingX n₁ n₂).mulVecStep b u)

/-- The complementary parts of the two splittings: `N_x = E_{n₁} ⊗ I`, `N_y = I ⊗ E_{n₂}`. -/
theorem adiSplitting_n (n₁ n₂ : ℕ) :
    (adiSplittingX n₁ n₂).n = modelE n₁ ⊗ₖ 1 ∧ (adiSplittingY n₁ n₂).n = 1 ⊗ₖ modelE n₂ := by
  obtain ⟨hA, -, -⟩ := equation_11_2_12 n₁ n₂
  constructor
  · change (4 : ℝ) • 1 - (1 ⊗ₖ modelE n₂) - poissonMatrix n₁ n₂ = _
    rw [hA]; abel
  · change (4 : ℝ) • 1 - (modelE n₁ ⊗ₖ 1) - poissonMatrix n₁ n₂ = _
    rw [hA]; abel

/-- `M_x⁻¹ N_x = E_{n₁} ⊗ (4I − E_{n₂})⁻¹`. -/
private theorem adiX_iterationOperator (n₁ n₂ : ℕ) :
    (adiSplittingX n₁ n₂).iterationOperator = modelE n₁ ⊗ₖ ((4 : ℝ) • 1 - modelE n₂)⁻¹ := by
  have hm : (adiSplittingX n₁ n₂).m = 1 ⊗ₖ ((4 : ℝ) • 1 - modelE n₂) :=
    four_smul_one_sub_one_kronecker _
  rw [Stationary.Splitting.iterationOperator_eq, ← Matrix.nonsing_inv_eq_ringInverse, hm,
    (adiSplitting_n n₁ n₂).1, Matrix.inv_kronecker, inv_one, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one]

/-- `M_y⁻¹ N_y = (4I − E_{n₁})⁻¹ ⊗ E_{n₂}`. -/
private theorem adiY_iterationOperator (n₁ n₂ : ℕ) :
    (adiSplittingY n₁ n₂).iterationOperator = ((4 : ℝ) • 1 - modelE n₁)⁻¹ ⊗ₖ modelE n₂ := by
  have hm : (adiSplittingY n₁ n₂).m = ((4 : ℝ) • 1 - modelE n₁) ⊗ₖ 1 :=
    four_smul_one_sub_kronecker_one _
  rw [Stationary.Splitting.iterationOperator_eq, ← Matrix.nonsing_inv_eq_ringInverse, hm,
    (adiSplitting_n n₁ n₂).2, Matrix.inv_kronecker, inv_one, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one]

/-- Conjugation is multiplicative. -/
private theorem conj_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Matrix ι ι ℝ}
    (hS : IsUnit S.det) (X Y : Matrix ι ι ℝ) :
    S⁻¹ * (X * Y) * S = (S⁻¹ * X * S) * (S⁻¹ * Y * S) := by
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hS]

/-- Conjugation commutes with inversion. -/
private theorem conj_inv {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Matrix ι ι ℝ}
    (hS : IsUnit S.det) (X : Matrix ι ι ℝ) : S⁻¹ * X⁻¹ * S = (S⁻¹ * X * S)⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hS,
    Matrix.mul_assoc]

/-- `S_m⁻¹ (4I − E_m) S_m = 4I − D_m`. -/
private theorem conj_four_sub_modelE (m : ℕ) :
    (Matrix.dst1 m)⁻¹ * ((4 : ℝ) • 1 - modelE m) * Matrix.dst1 m =
      (4 : ℝ) • 1 - Matrix.diagonal (modelEEigenvalues m) := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_dst1 m)),
    equation_11_2_13]

/-- The ADI error operator in the sine basis, as a Kronecker product. -/
private theorem conj_adi (n₁ n₂ : ℕ) :
    (Matrix.dst1 n₁ ⊗ₖ Matrix.dst1 n₂)⁻¹ *
        ((adiSplittingY n₁ n₂).iterationOperator * (adiSplittingX n₁ n₂).iterationOperator) *
        (Matrix.dst1 n₁ ⊗ₖ Matrix.dst1 n₂) =
      (((4 : ℝ) • 1 - Matrix.diagonal (modelEEigenvalues n₁))⁻¹ *
          Matrix.diagonal (modelEEigenvalues n₁)) ⊗ₖ
        (Matrix.diagonal (modelEEigenvalues n₂) *
          ((4 : ℝ) • 1 - Matrix.diagonal (modelEEigenvalues n₂))⁻¹) := by
  have h₁ := (Matrix.isUnit_iff_isUnit_det _).1 (isUnit_dst1 n₁)
  have h₂ := (Matrix.isUnit_iff_isUnit_det _).1 (isUnit_dst1 n₂)
  rw [adiY_iterationOperator, adiX_iterationOperator, ← Matrix.mul_kronecker_mul, kronecker_conj,
    conj_mul h₁, conj_mul h₂, conj_inv h₁, conj_inv h₂, conj_four_sub_modelE,
    conj_four_sub_modelE, equation_11_2_13, equation_11_2_13]

/-- **§11.2.6: the error of the alternating-direction iteration.** If `A x = b` then the iterates of
(11.2.16) satisfy `u⁽ᵏ⁾ − x = G^k (u⁽⁰⁾ − x)` with `G = (M_y⁻¹N_y)(M_x⁻¹N_x)`, and
`(S_{n₁} ⊗ S_{n₂})⁻¹ G (S_{n₁} ⊗ S_{n₂}) =
(4I − D_{n₁} ⊗ I)⁻¹ (I ⊗ D_{n₂}) (4I − I ⊗ D_{n₂})⁻¹ (D_{n₁} ⊗ I)`. -/
theorem adi_error_eq (n₁ n₂ : ℕ) {b x : Fin n₁ × Fin n₂ → ℝ} (hx : poissonMatrix n₁ n₂ *ᵥ x = b)
    (u₀ : Fin n₁ × Fin n₂ → ℝ) (k : ℕ) :
    (adiStep n₁ n₂ b)^[k] u₀ - x =
        ((adiSplittingY n₁ n₂).iterationOperator * (adiSplittingX n₁ n₂).iterationOperator) ^ k *ᵥ
          (u₀ - x) ∧
      (Matrix.dst1 n₁ ⊗ₖ Matrix.dst1 n₂)⁻¹ *
          ((adiSplittingY n₁ n₂).iterationOperator * (adiSplittingX n₁ n₂).iterationOperator) *
          (Matrix.dst1 n₁ ⊗ₖ Matrix.dst1 n₂) =
        ((4 : ℝ) • 1 - Matrix.diagonal (modelEEigenvalues n₁) ⊗ₖ 1)⁻¹ *
          (1 ⊗ₖ Matrix.diagonal (modelEEigenvalues n₂)) *
          ((4 : ℝ) • 1 - 1 ⊗ₖ Matrix.diagonal (modelEEigenvalues n₂))⁻¹ *
          (Matrix.diagonal (modelEEigenvalues n₁) ⊗ₖ 1) := by
  constructor
  · have hstep : ∀ u, adiStep n₁ n₂ b u - x = ((adiSplittingY n₁ n₂).iterationOperator *
        (adiSplittingX n₁ n₂).iterationOperator) *ᵥ (u - x) := fun u => by
      rw [adiStep, mulVecStep_sub _ hx, mulVecStep_sub _ hx, Matrix.mulVec_mulVec]
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', hstep, ih, Matrix.mulVec_mulVec, ← pow_succ']
  · rw [conj_adi, four_smul_one_sub_kronecker_one, four_smul_one_sub_one_kronecker,
      Matrix.inv_kronecker, Matrix.inv_kronecker]
    simp only [inv_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

/-- `4I − diag(d) = diag(4 − d)`. -/
private theorem four_smul_one_sub_diagonal {m : ℕ} (d : Fin m → ℝ) :
    (4 : ℝ) • (1 : Matrix (Fin m) (Fin m) ℝ) - Matrix.diagonal d =
      Matrix.diagonal fun i => 4 - d i := by
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/-- The inverse of a diagonal matrix with nonzero entries. -/
private theorem inv_diagonal_of_ne_zero {m : ℕ} (d : Fin m → ℝ) (hd : ∀ i, d i ≠ 0) :
    (Matrix.diagonal d)⁻¹ = Matrix.diagonal fun i => (d i)⁻¹ := by
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.diagonal_mul_diagonal]
  have : (fun i => (d i)⁻¹ * d i) = fun _ => (1 : ℝ) := funext fun i => inv_mul_cancel₀ (hd i)
  rw [this, Matrix.diagonal_one]

/-- `|μ_k| < 4`: the eigenvalues of `E_m` lie in `[−2, 2]`. -/
private theorem four_sub_modelEEigenvalues_ne_zero (m : ℕ) (k : Fin m) :
    4 - modelEEigenvalues m k ≠ 0 := by
  have := Real.cos_le_one ((((k : ℕ) : ℝ) + 1) * Real.pi / ((m : ℝ) + 1))
  simp only [modelEEigenvalues]
  linarith

/-- The scalar bound behind (11.2.17): `|2c/(4 − 2c)| ≤ c₀/(2 − c₀)` for `|c| ≤ c₀ < 1`. -/
private theorem abs_adiFactor_le {c c₀ : ℝ} (hc : |c| ≤ c₀) (hc₀ : c₀ < 1) :
    |(4 - 2 * c)⁻¹ * (2 * c)| ≤ c₀ / (2 - c₀) := by
  have hc1 : c ≤ c₀ := (le_abs_self c).trans hc
  have h2c : 0 < 2 - c := by linarith
  have h2c₀ : 0 < 2 - c₀ := by linarith
  have e : (4 - 2 * c)⁻¹ * (2 * c) = c / (2 - c) := by
    rw [show 4 - 2 * c = 2 * (2 - c) by ring]
    field_simp
  rw [e, abs_div, abs_of_pos h2c, div_le_div_iff₀ h2c h2c₀]
  have hc₀0 : 0 ≤ c₀ := (abs_nonneg c).trans hc
  nlinarith [mul_nonneg hc₀0 (sub_nonneg.2 (le_abs_self c))]

/-- `2c/(4 − 2c) = c/(2 − c)`. -/
private theorem adiFactor_eq {c : ℝ} (h : c < 1) : (4 - 2 * c)⁻¹ * (2 * c) = c / (2 - c) := by
  rw [show 4 - 2 * c = 2 * (2 - c) by ring]
  have : 2 - c ≠ 0 := by linarith
  field_simp

/-- **(11.2.17).** The spectral radius of the alternating-direction iteration matrix,
`ρ(G) = cos(π/(n₁+1)) cos(π/(n₂+1)) / ((2 − cos(π/(n₁+1)))(2 − cos(π/(n₂+1)))) < 1` (the book's
P11.2.9; the printed "`ρ(G) = =`" is a typo). -/
theorem equation_11_2_17 (n₁ n₂ : ℕ) [NeZero n₁] [NeZero n₂] :
    Matrix.complexSpectralRadius
        ((adiSplittingY n₁ n₂).iterationOperator * (adiSplittingX n₁ n₂).iterationOperator) =
      ENNReal.ofReal (Real.cos (Real.pi / ((n₁ : ℝ) + 1)) * Real.cos (Real.pi / ((n₂ : ℝ) + 1)) /
        ((2 - Real.cos (Real.pi / ((n₁ : ℝ) + 1))) * (2 - Real.cos (Real.pi / ((n₂ : ℝ) + 1))))) ∧
      Real.cos (Real.pi / ((n₁ : ℝ) + 1)) * Real.cos (Real.pi / ((n₂ : ℝ) + 1)) /
        ((2 - Real.cos (Real.pi / ((n₁ : ℝ) + 1))) * (2 - Real.cos (Real.pi / ((n₂ : ℝ) + 1)))) <
        1 := by
  have hc₁0 := cos_pi_div_nonneg n₁
  have hc₂0 := cos_pi_div_nonneg n₂
  have hc₁1 := cos_pi_div_lt_one n₁
  have hc₂1 := cos_pi_div_lt_one n₂
  set c₁ := Real.cos (Real.pi / ((n₁ : ℝ) + 1))
  set c₂ := Real.cos (Real.pi / ((n₂ : ℝ) + 1))
  have hsplit : c₁ * c₂ / ((2 - c₁) * (2 - c₂)) = c₁ / (2 - c₁) * (c₂ / (2 - c₂)) :=
    (div_mul_div_comm _ _ _ _).symm
  have hf : ∀ c : ℝ, 0 ≤ c → c < 1 → 0 ≤ c / (2 - c) ∧ c / (2 - c) < 1 := fun c h0 h1 =>
    ⟨div_nonneg h0 (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩
  refine ⟨?_, ?_⟩
  · rw [← Matrix.complexSpectralRadius_conj (isUnit_dst1_kronecker n₁ n₂), conj_adi,
      four_smul_one_sub_diagonal, four_smul_one_sub_diagonal,
      inv_diagonal_of_ne_zero _ (four_sub_modelEEigenvalues_ne_zero n₁),
      inv_diagonal_of_ne_zero _ (four_sub_modelEEigenvalues_ne_zero n₂),
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_kronecker_diagonal, hsplit]
    refine complexSpectralRadius_diagonal_eq_ofReal _ (fun p => ?_) (i₀ := (0, 0)) ?_
    · rw [abs_mul, mul_comm (modelEEigenvalues n₂ p.2)]
      exact mul_le_mul (abs_adiFactor_le (abs_cos_le n₁ p.1) hc₁1)
        (abs_adiFactor_le (abs_cos_le n₂ p.2) hc₂1) (abs_nonneg _) (hf c₁ hc₁0 hc₁1).1
    · have e₁ : modelEEigenvalues n₁ 0 = 2 * c₁ := by
        simp only [modelEEigenvalues, Fin.val_zero, Nat.cast_zero, zero_add, one_mul]; rfl
      have e₂ : modelEEigenvalues n₂ 0 = 2 * c₂ := by
        simp only [modelEEigenvalues, Fin.val_zero, Nat.cast_zero, zero_add, one_mul]; rfl
      rw [e₁, e₂, mul_comm (2 * c₂), adiFactor_eq hc₁1, adiFactor_eq hc₂1,
        abs_of_nonneg (mul_nonneg (hf c₁ hc₁0 hc₁1).1 (hf c₂ hc₂0 hc₂1).1)]
  · rw [hsplit]
    exact (mul_le_of_le_one_right (hf c₁ hc₁0 hc₁1).1 (hf c₂ hc₂0 hc₂1).2.le).trans_lt
      (hf c₁ hc₁0 hc₁1).2

/-! ### SOR and SSOR -/

/-- **(11.2.18).** For `ω ≠ 0` and `a_ii ≠ 0`, the SOR splitting `A = M_ω − N_ω` has
`M_ω = ω⁻¹ D_A + L_A` and `N_ω = (ω⁻¹ − 1) D_A − U_A`. The book prints `N_ω = (ω⁻¹ − 1) D_A + U_A`
in (11.2.18) and (11.2.19), which is inconsistent with `A = M_ω − N_ω`; the sign of `U_A` is
corrected here (the book itself has `− L_Aᵀ` in (11.2.22)). -/
theorem equation_11_2_18 (A : Matrix (Fin n) (Fin n) ℝ) (h : IsUnit (Matrix.diagPart A)) {ω : ℝ}
    (hω : ω ≠ 0) :
    (Matrix.sorSplitting A h hω).m = ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A ∧
      (Matrix.sorSplitting A h hω).n =
        (ω⁻¹ - 1) • Matrix.diagPart A - Matrix.strictUpper A := by
  refine ⟨rfl, ?_⟩
  change ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A - A = _
  have e := Matrix.diagPart_add_strictLower_add_strictUpper A
  calc ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A - A
      = ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A -
          (Matrix.diagPart A + Matrix.strictLower A + Matrix.strictUpper A) := by rw [e]
    _ = _ := by module

/-- The mirror identity for the backward SOR splitting: `M = ω⁻¹ D_A + U_A`,
`N = (ω⁻¹ − 1) D_A − L_A`. -/
private theorem backwardSorSplitting_m_n (A : Matrix (Fin n) (Fin n) ℝ)
    (h : IsUnit (Matrix.diagPart A)) {ω : ℝ} (hω : ω ≠ 0) :
    (Matrix.backwardSorSplitting A h hω).m = ω⁻¹ • Matrix.diagPart A + Matrix.strictUpper A ∧
      (Matrix.backwardSorSplitting A h hω).n =
        (ω⁻¹ - 1) • Matrix.diagPart A - Matrix.strictLower A := by
  refine ⟨rfl, ?_⟩
  change ω⁻¹ • Matrix.diagPart A + Matrix.strictUpper A - A = _
  have e := Matrix.diagPart_add_strictLower_add_strictUpper A
  calc ω⁻¹ • Matrix.diagPart A + Matrix.strictUpper A - A
      = ω⁻¹ • Matrix.diagPart A + Matrix.strictUpper A -
          (Matrix.diagPart A + Matrix.strictLower A + Matrix.strictUpper A) := by rw [e]
    _ = _ := by module

/-- The step of a splitting solves `M x⁺ = N x + b`. -/
private theorem m_mulVec_mulVecStep {A : Matrix (Fin n) (Fin n) ℝ} (s : Stationary.Splitting A)
    (b x : Fin n → ℝ) : s.m *ᵥ s.mulVecStep b x = s.n *ᵥ x + b :=
  Matrix.mulVec_nonsing_inv_mulVec s.isUnit _

/-- **(11.2.19).** With `a_ii ≠ 0` and `ω ≠ 0`, the exact run of the componentwise SOR loop is the
step of the SOR splitting: `(ω⁻¹ D_A + L_A) x⁽ᵏ⁾ = ((ω⁻¹ − 1) D_A − U_A) x⁽ᵏ⁻¹⁾ + b`. -/
theorem equation_11_2_19 (A : Matrix (Fin n) (Fin n) ℝ) (h : IsUnit (Matrix.diagPart A)) {ω : ℝ}
    (hω : ω ≠ 0) (b x : Fin n → ℝ) :
    Id.run (sorSweep pure A ω b x) = (Matrix.sorSplitting A h hω).mulVecStep b x ∧
      (ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A) *ᵥ Id.run (sorSweep pure A ω b x) =
        ((ω⁻¹ - 1) • Matrix.diagPart A - Matrix.strictUpper A) *ᵥ x + b := by
  have h1 : Id.run (sorSweep pure A ω b x) = (Matrix.sorSplitting A h hω).mulVecStep b x := by
    rw [sorSweep_id A h, Matrix.sorSweep_eq_mulVecStep A h hω]
  refine ⟨h1, ?_⟩
  rw [h1, ← (equation_11_2_18 A h hω).1, ← (equation_11_2_18 A h hω).2]
  exact m_mulVec_mulVecStep _ b x

/-- **(11.2.21).** The exact backward SOR sweep is the step of the backward SOR splitting,
`(ω⁻¹ D_A + U_A) x⁽ᵏ⁾ = ((ω⁻¹ − 1) D_A − L_A) x⁽ᵏ⁻¹⁾ + b` (the book again prints `+ L_A`). -/
theorem equation_11_2_21 (A : Matrix (Fin n) (Fin n) ℝ) (h : IsUnit (Matrix.diagPart A)) {ω : ℝ}
    (hω : ω ≠ 0) (b x : Fin n → ℝ) :
    Id.run (backwardSorSweep pure A ω b x) = (Matrix.backwardSorSplitting A h hω).mulVecStep b x ∧
      (ω⁻¹ • Matrix.diagPart A + Matrix.strictUpper A) *ᵥ Id.run (backwardSorSweep pure A ω b x) =
        ((ω⁻¹ - 1) • Matrix.diagPart A - Matrix.strictLower A) *ᵥ x + b := by
  have h1 : Id.run (backwardSorSweep pure A ω b x) =
      (Matrix.backwardSorSplitting A h hω).mulVecStep b x := by
    rw [backwardSorSweep_id A h, Matrix.backwardSorSweep_eq_mulVecStep A h hω]
  refine ⟨h1, ?_⟩
  rw [h1, ← (backwardSorSplitting_m_n A h hω).1, ← (backwardSorSplitting_m_n A h hω).2]
  exact m_mulVec_mulVecStep _ b x

/-- For symmetric `A`, `U_A = L_Aᵀ`. -/
private theorem strictUpper_eq_transpose {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    Matrix.strictUpper A = (Matrix.strictLower A)ᵀ := by
  rw [Matrix.strictLower_transpose, hA.eq]

/-- **(11.2.22)–(11.2.23).** For symmetric `A` (`U_A = L_Aᵀ`), `a_ii ≠ 0` and `ω ≠ 0`, the half step
`y⁽ᵏ⁾` and the full step `x⁽ᵏ⁾` of the exact SSOR program satisfy
`(ω⁻¹D + L) y⁽ᵏ⁾ = ((ω⁻¹ − 1)D − Lᵀ) x⁽ᵏ⁻¹⁾ + b` and
`(ω⁻¹D + Lᵀ) x⁽ᵏ⁾ = ((ω⁻¹ − 1)D − L) y⁽ᵏ⁾ + b`. -/
theorem equation_11_2_22 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (h : IsUnit (Matrix.diagPart A)) {ω : ℝ} (hω : ω ≠ 0) (b x : Fin n → ℝ) :
    (ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A) *ᵥ Id.run (sorSweep pure A ω b x) =
        ((ω⁻¹ - 1) • Matrix.diagPart A - (Matrix.strictLower A)ᵀ) *ᵥ x + b ∧
      (ω⁻¹ • Matrix.diagPart A + (Matrix.strictLower A)ᵀ) *ᵥ Id.run (ssorSweep pure A ω b x) =
        ((ω⁻¹ - 1) • Matrix.diagPart A - Matrix.strictLower A) *ᵥ
          Id.run (sorSweep pure A ω b x) + b := by
  rw [← strictUpper_eq_transpose hA]
  exact ⟨(equation_11_2_19 A h hω b x).2,
    (equation_11_2_21 A h hω b (Id.run (sorSweep pure A ω b x))).2⟩

/-- **(11.2.24) and the claims after it.** For symmetric `A` with positive diagonal and `0 < ω < 2`,
`M_SSOR = (ω/(2 − ω)) (ω⁻¹D + L) D⁻¹ (ω⁻¹D + Lᵀ)` is the `M` of the SSOR splitting, is symmetric,
and is positive definite. -/
theorem equation_11_2_24 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (hd : ∀ i, 0 < A i i)
    {ω : ℝ} (hω0 : 0 < ω) (hω2 : ω < 2) :
    let h : IsUnit (Matrix.diagPart A) := (Matrix.isUnit_diagPart_iff A).2 fun i => (hd i).ne'
    (ω / (2 - ω)) • ((ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A) * (Matrix.diagPart A)⁻¹ *
        (ω⁻¹ • Matrix.diagPart A + (Matrix.strictLower A)ᵀ)) =
        (Matrix.ssorSplitting A h hω0.ne' hω2.ne).m ∧
      (Matrix.ssorSplitting A h hω0.ne' hω2.ne).m.IsSymm ∧
      (Matrix.ssorSplitting A h hω0.ne' hω2.ne).m.PosDef := by
  intro h
  refine ⟨?_, Matrix.ssorSplitting_m_isSymm hA h _ _,
    Matrix.ssorSplitting_m_posDef_of_diag_pos (Matrix.isHermitian_iff_isSymm.2 hA) hd h hω0 hω2⟩
  change _ = (ω * (2 - ω))⁻¹ • ((Matrix.diagPart A + ω • Matrix.strictLower A) *
    (Matrix.diagPart A)⁻¹ * (Matrix.diagPart A + ω • Matrix.strictUpper A))
  rw [strictUpper_eq_transpose hA]
  have h2 : (2 : ℝ) - ω ≠ 0 := by linarith
  have e1 : ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A =
      ω⁻¹ • (Matrix.diagPart A + ω • Matrix.strictLower A) := by
    rw [smul_add, smul_smul, inv_mul_cancel₀ hω0.ne', one_smul]
  have e2 : ω⁻¹ • Matrix.diagPart A + (Matrix.strictLower A)ᵀ =
      ω⁻¹ • (Matrix.diagPart A + ω • (Matrix.strictLower A)ᵀ) := by
    rw [smul_add, smul_smul, inv_mul_cancel₀ hω0.ne', one_smul]
  rw [e1, e2, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul]
  congr 1
  field_simp

/-- **(11.2.25).** For symmetric `A` with `a_ii ≠ 0` and `ω ≠ 0, 2`, the exact SSOR step is
`x⁽ᵏ⁾ = x⁽ᵏ⁻¹⁾ + M_SSOR⁻¹ (b − A x⁽ᵏ⁻¹⁾)` (the book's P11.2.10). -/
theorem equation_11_2_25 {A : Matrix (Fin n) (Fin n) ℝ} (h : IsUnit (Matrix.diagPart A)) {ω : ℝ}
    (hω : ω ≠ 0) (hω2 : ω ≠ 2) (b x : Fin n → ℝ) :
    Id.run (ssorSweep pure A ω b x) =
      x + (Matrix.ssorSplitting A h hω hω2).m⁻¹ *ᵥ (b - A *ᵥ x) := by
  change Id.run (backwardSorSweep pure A ω b (Id.run (sorSweep pure A ω b x))) = _
  rw [sorSweep_id A h, backwardSorSweep_id A h, Matrix.ssorSweep_eq_mulVecStep A h hω hω2,
    Stationary.Splitting.mulVecStep_eq_add_inv_mulVec]

/-- The iteration matrix of the SSOR splitting is the book's `G = M_ω⁻ᵀ N_ωᵀ M_ω⁻¹ N_ω`. -/
private theorem ssor_iterationOperator_eq {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (h : IsUnit (Matrix.diagPart A)) {ω : ℝ} (hω : ω ≠ 0) (hω2 : ω ≠ 2) :
    (Matrix.ssorSplitting A h hω hω2).iterationOperator =
      (ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A)ᵀ⁻¹ *
        ((ω⁻¹ - 1) • Matrix.diagPart A - (Matrix.strictLower A)ᵀ)ᵀ *
        (ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A)⁻¹ *
        ((ω⁻¹ - 1) • Matrix.diagPart A - (Matrix.strictLower A)ᵀ) := by
  rw [Matrix.ssorSplitting_iterationOperator_eq_mul, Stationary.Splitting.iterationOperator_eq,
    Stationary.Splitting.iterationOperator_eq, ← Matrix.nonsing_inv_eq_ringInverse,
    ← Matrix.nonsing_inv_eq_ringInverse, (backwardSorSplitting_m_n A h hω).1,
    (backwardSorSplitting_m_n A h hω).2, (equation_11_2_18 A h hω).1, (equation_11_2_18 A h hω).2,
    strictUpper_eq_transpose hA, Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.diagPart_transpose, hA.eq]
  simp only [Matrix.mul_assoc]

/-- **Theorem 11.2.4.** Suppose SSOR (11.2.22)–(11.2.23) is applied to a symmetric positive definite
`A x = b` and `0 < ω < 2`. With `M_ω = ω⁻¹D_A + L_A`, `N_ω = (ω⁻¹ − 1)D_A − L_Aᵀ` and
`G = M_ω⁻ᵀ N_ωᵀ M_ω⁻¹ N_ω`, `G` has real eigenvalues — they lie in `[0, 1)`, as the proof shows —
and `ρ(G) < 1`. -/
theorem theorem_11_2_4 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) {ω : ℝ} (hω0 : 0 < ω)
    (hω2 : ω < 2) :
    let G := (ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A)ᵀ⁻¹ *
      ((ω⁻¹ - 1) • Matrix.diagPart A - (Matrix.strictLower A)ᵀ)ᵀ *
      (ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A)⁻¹ *
      ((ω⁻¹ - 1) • Matrix.diagPart A - (Matrix.strictLower A)ᵀ)
    spectrum ℂ G.complexify ⊆ Complex.ofReal '' Set.Ico 0 1 ∧ G.complexSpectralRadius < 1 := by
  intro G
  have hsymm : A.IsSymm := Matrix.isHermitian_iff_isSymm.1 hA.isHermitian
  have hd : ∀ i, 0 < A i i := fun i => hA.diag_pos
  have h : IsUnit (Matrix.diagPart A) := (Matrix.isUnit_diagPart_iff A).2 fun i => (hd i).ne'
  have hG : G = (Matrix.ssorSplitting A h hω0.ne' hω2.ne).iterationOperator :=
    (ssor_iterationOperator_eq hsymm h hω0.ne' hω2.ne).symm
  rw [hG]
  exact ⟨Stationary.Splitting.spectrum_complexify_iterationOperator_subset _ hA
      (Matrix.ssorSplitting_m_sub_posSemidef hA.isHermitian hd h hω0 hω2),
    Matrix.ssorSplitting_complexSpectralRadius_lt_one hA h hω0 hω2⟩

/-- **(11.2.26).** Under the hypotheses of Theorem 11.2.4, with `A x = b`, the iterates of the exact
SSOR program satisfy `x⁽ᵏ⁾ − x = G^k (x⁽⁰⁾ − x)`. -/
theorem equation_11_2_26 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) {ω : ℝ} (hω0 : 0 < ω)
    (hω2 : ω < 2) {b x : Fin n → ℝ} (hx : A *ᵥ x = b) (x₀ : Fin n → ℝ) (k : ℕ) :
    (fun y => Id.run (ssorSweep pure A ω b y))^[k] x₀ - x =
      ((ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A)ᵀ⁻¹ *
        ((ω⁻¹ - 1) • Matrix.diagPart A - (Matrix.strictLower A)ᵀ)ᵀ *
        (ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A)⁻¹ *
        ((ω⁻¹ - 1) • Matrix.diagPart A - (Matrix.strictLower A)ᵀ)) ^ k *ᵥ (x₀ - x) := by
  have hsymm : A.IsSymm := Matrix.isHermitian_iff_isSymm.1 hA.isHermitian
  have h : IsUnit (Matrix.diagPart A) :=
    (Matrix.isUnit_diagPart_iff A).2 fun i => hA.diag_pos.ne'
  have hf : (fun y => Id.run (ssorSweep pure A ω b y)) =
      (Matrix.ssorSplitting A h hω0.ne' hω2.ne).mulVecStep b := by
    funext y
    rw [equation_11_2_25 h hω0.ne' hω2.ne, Stationary.Splitting.mulVecStep_eq_add_inv_mulVec]
  rw [hf, equation_11_2_7 _ hx, ssor_iterationOperator_eq hsymm h]

/-- `(c B)⁻¹ = c⁻¹ B⁻¹` for `c ≠ 0` and `B` nonsingular. -/
private theorem inv_smul_of_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι] {c : ℝ} (hc : c ≠ 0)
    {B : Matrix ι ι ℝ} (hB : IsUnit B) : (c • B)⁻¹ = c⁻¹ • B⁻¹ :=
  Matrix.inv_eq_left_inv (by
    rw [smul_mul_smul_comm, inv_mul_cancel₀ hc,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hB), one_smul])

/-- The scalars cancel in `G = M⁻ᵀ Nᵀ M⁻¹ N` for `M = ω⁻¹ P`, `N = ω⁻¹ Q`. -/
private theorem ssorG_scale {ι : Type*} [Fintype ι] [DecidableEq ι] {ω : ℝ} (hω : ω ≠ 0)
    {P : Matrix ι ι ℝ} (hP : IsUnit P) (Q : Matrix ι ι ℝ) :
    (ω⁻¹ • P)ᵀ⁻¹ * (ω⁻¹ • Q)ᵀ * (ω⁻¹ • P)⁻¹ * (ω⁻¹ • Q) = Pᵀ⁻¹ * Qᵀ * P⁻¹ * Q := by
  rw [Matrix.transpose_smul, Matrix.transpose_smul,
    inv_smul_of_isUnit (inv_ne_zero hω) ((Matrix.isUnit_transpose P).2 hP),
    inv_smul_of_isUnit (inv_ne_zero hω) hP, inv_inv]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [inv_mul_cancel₀ hω, mul_one, inv_mul_cancel₀ hω, one_smul]

/-- Conjugating `Pᵀ⁻¹ Qᵀ P⁻¹ Q` by a nonsingular `D₁` and regrouping. -/
private theorem conj_ssorG {ι : Type*} [Fintype ι] [DecidableEq ι] {D₁ : Matrix ι ι ℝ}
    (hD : IsUnit D₁.det) (P Q : Matrix ι ι ℝ) :
    D₁ * (Pᵀ⁻¹ * Qᵀ * P⁻¹ * Q) * D₁⁻¹ =
      (D₁⁻¹ * Pᵀ * D₁⁻¹)⁻¹ * (D₁⁻¹ * Qᵀ * D₁⁻¹) * (D₁⁻¹ * P * D₁⁻¹)⁻¹ * (D₁⁻¹ * Q * D₁⁻¹) := by
  simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hD, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv_cancel_left _ _ hD, Matrix.nonsing_inv_mul_cancel_left _ _ hD]

/-- `D₁⁻¹ (a D₁² + c K) D₁⁻¹ = a I + c D₁⁻¹ K D₁⁻¹`. -/
private theorem conj_diag {ι : Type*} [Fintype ι] [DecidableEq ι] {D₁ : Matrix ι ι ℝ}
    (hD : IsUnit D₁.det) (a c : ℝ) (K : Matrix ι ι ℝ) :
    D₁⁻¹ * (a • (D₁ * D₁) + c • K) * D₁⁻¹ = a • 1 + c • (D₁⁻¹ * K * D₁⁻¹) := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_mul, ← Matrix.mul_assoc D₁⁻¹ D₁ D₁, Matrix.nonsing_inv_mul _ hD, Matrix.one_mul,
    Matrix.mul_nonsing_inv _ hD]

/-- `v ⬝ (Y w) = (Yᵀ v) ⬝ w`. -/
private theorem dotProduct_mulVec_eq {ι : Type*} [Fintype ι] (Y : Matrix ι ι ℝ) (v w : ι → ℝ) :
    v ⬝ᵥ (Y *ᵥ w) = (Yᵀ *ᵥ v) ⬝ᵥ w := by
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

/-- **(11.2.27)**, from the proof of Theorem 11.2.4. Let `A` be symmetric with positive diagonal,
`D = D₁²`, `L₁ = D₁⁻¹ L D₁⁻¹` and `G₁ = D₁ G D₁⁻¹`. Then
`G₁ = (I + ωL₁ᵀ)⁻¹ (I + ωL₁)⁻¹ ((1 − ω)I − ωL₁)((1 − ω)I − ωL₁ᵀ)`, and for a real unit eigenvector
`G₁ v = λ v`,
`λ = ‖(1 − ω)v − ωL₁ᵀv‖₂² / ‖v + ωL₁ᵀv‖₂² = 1 − ω(2 − ω)(1 + 2vᵀL₁ᵀv) / ‖v + ωL₁ᵀv‖₂²`. -/
theorem equation_11_2_27 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (hd : ∀ i, 0 < A i i)
    {ω : ℝ} (hω : ω ≠ 0) :
    let D₁ := Matrix.diagonal fun i => Real.sqrt (A i i)
    let L₁ := D₁⁻¹ * Matrix.strictLower A * D₁⁻¹
    let G := (ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A)ᵀ⁻¹ *
      ((ω⁻¹ - 1) • Matrix.diagPart A - (Matrix.strictLower A)ᵀ)ᵀ *
      (ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A)⁻¹ *
      ((ω⁻¹ - 1) • Matrix.diagPart A - (Matrix.strictLower A)ᵀ)
    let G₁ := (1 + ω • L₁ᵀ)⁻¹ * (1 + ω • L₁)⁻¹ * ((1 - ω) • 1 - ω • L₁) * ((1 - ω) • 1 - ω • L₁ᵀ)
    D₁ * D₁ = Matrix.diagPart A ∧ D₁ * G * D₁⁻¹ = G₁ ∧
      ∀ (l : ℝ) (v : Fin n → ℝ), G₁ *ᵥ v = l • v → v ⬝ᵥ v = 1 →
        l = ((1 - ω) • v - ω • L₁ᵀ *ᵥ v) ⬝ᵥ ((1 - ω) • v - ω • L₁ᵀ *ᵥ v) /
            ((v + ω • L₁ᵀ *ᵥ v) ⬝ᵥ (v + ω • L₁ᵀ *ᵥ v)) ∧
          l = 1 - ω * (2 - ω) * (1 + 2 * (v ⬝ᵥ L₁ᵀ *ᵥ v)) /
            ((v + ω • L₁ᵀ *ᵥ v) ⬝ᵥ (v + ω • L₁ᵀ *ᵥ v)) := by
  intro D₁ L₁ G G₁
  have hD1 : D₁ * D₁ = Matrix.diagPart A := by
    change Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal A.diag
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact Real.mul_self_sqrt (hd i).le
  have hD1u : IsUnit D₁.det := by
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    exact fun i _ => (Real.sqrt_pos.2 (hd i)).ne'
  have hD1i : IsUnit D₁⁻¹ :=
    (Matrix.isUnit_nonsing_inv_iff).2 ((Matrix.isUnit_iff_isUnit_det _).2 hD1u)
  have hD1iT : (D₁⁻¹)ᵀ = D₁⁻¹ := by rw [Matrix.transpose_nonsing_inv, Matrix.diagonal_transpose]
  have hDT : (Matrix.diagPart A)ᵀ = Matrix.diagPart A := by
    rw [Matrix.diagPart_transpose, hA.eq]
  have h : IsUnit (Matrix.diagPart A) := (Matrix.isUnit_diagPart_iff A).2 fun i => (hd i).ne'
  have hPu : IsUnit (Matrix.diagPart A + ω • Matrix.strictLower A) :=
    Matrix.isUnit_diagPart_add_smul_strictLower h ω
  have hL1T : L₁ᵀ = D₁⁻¹ * (Matrix.strictLower A)ᵀ * D₁⁻¹ := by
    change (D₁⁻¹ * Matrix.strictLower A * D₁⁻¹)ᵀ = _
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hD1iT, Matrix.mul_assoc]
  -- the four conjugated factors
  have hX : D₁⁻¹ * (Matrix.diagPart A + ω • Matrix.strictLower A) * D₁⁻¹ = 1 + ω • L₁ := by
    rw [show Matrix.diagPart A + ω • Matrix.strictLower A =
      (1 : ℝ) • (D₁ * D₁) + ω • Matrix.strictLower A by rw [one_smul, hD1], conj_diag hD1u,
      one_smul]
  have hXT : D₁⁻¹ * (Matrix.diagPart A + ω • Matrix.strictLower A)ᵀ * D₁⁻¹ = 1 + ω • L₁ᵀ := by
    rw [Matrix.transpose_add, Matrix.transpose_smul, hDT,
      show Matrix.diagPart A + ω • (Matrix.strictLower A)ᵀ =
        (1 : ℝ) • (D₁ * D₁) + ω • (Matrix.strictLower A)ᵀ by rw [one_smul, hD1],
      conj_diag hD1u, one_smul, hL1T]
  have hY : D₁⁻¹ * ((1 - ω) • Matrix.diagPart A - ω • (Matrix.strictLower A)ᵀ)ᵀ * D₁⁻¹ =
      (1 - ω) • 1 - ω • L₁ := by
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_smul, hDT,
      Matrix.transpose_transpose, sub_eq_add_neg, ← neg_smul, ← hD1, conj_diag hD1u, neg_smul,
      ← sub_eq_add_neg]
  have hYT : D₁⁻¹ * ((1 - ω) • Matrix.diagPart A - ω • (Matrix.strictLower A)ᵀ) * D₁⁻¹ =
      (1 - ω) • 1 - ω • L₁ᵀ := by
    rw [sub_eq_add_neg, ← neg_smul, ← hD1, conj_diag hD1u, neg_smul, ← sub_eq_add_neg, hL1T]
  -- `G = P⁻ᵀ Qᵀ P⁻¹ Q`
  have hG : G = (Matrix.diagPart A + ω • Matrix.strictLower A)ᵀ⁻¹ *
      ((1 - ω) • Matrix.diagPart A - ω • (Matrix.strictLower A)ᵀ)ᵀ *
      (Matrix.diagPart A + ω • Matrix.strictLower A)⁻¹ *
      ((1 - ω) • Matrix.diagPart A - ω • (Matrix.strictLower A)ᵀ) := by
    have e1 : ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A =
        ω⁻¹ • (Matrix.diagPart A + ω • Matrix.strictLower A) := by
      rw [smul_add, smul_smul, inv_mul_cancel₀ hω, one_smul]
    have e2 : (ω⁻¹ - 1) • Matrix.diagPart A - (Matrix.strictLower A)ᵀ =
        ω⁻¹ • ((1 - ω) • Matrix.diagPart A - ω • (Matrix.strictLower A)ᵀ) := by
      rw [smul_sub, smul_smul, smul_smul, mul_sub, mul_one, inv_mul_cancel₀ hω, one_smul]
    change (ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A)ᵀ⁻¹ *
      ((ω⁻¹ - 1) • Matrix.diagPart A - (Matrix.strictLower A)ᵀ)ᵀ *
      (ω⁻¹ • Matrix.diagPart A + Matrix.strictLower A)⁻¹ *
      ((ω⁻¹ - 1) • Matrix.diagPart A - (Matrix.strictLower A)ᵀ) = _
    rw [e1, e2]
    exact ssorG_scale hω hPu _
  -- units and commutation
  have hXu : IsUnit (1 + ω • L₁) := by rw [← hX]; exact (hD1i.mul hPu).mul hD1i
  have hXTu : IsUnit (1 + ω • L₁ᵀ) := by
    rw [← hXT]; exact (hD1i.mul ((Matrix.isUnit_transpose _).2 hPu)).mul hD1i
  have hXd := (Matrix.isUnit_iff_isUnit_det _).1 hXu
  have hXTd := (Matrix.isUnit_iff_isUnit_det _).1 hXTu
  have hcomm : ((1 - ω) • 1 - ω • L₁) * (1 + ω • L₁)⁻¹ =
      (1 + ω • L₁)⁻¹ * ((1 - ω) • 1 - ω • L₁) := by
    have hYX : (1 - ω) • (1 : Matrix (Fin n) (Fin n) ℝ) - ω • L₁ = (2 - ω) • 1 - (1 + ω • L₁) := by
      module
    rw [hYX, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, Matrix.mul_nonsing_inv _ hXd, Matrix.nonsing_inv_mul _ hXd]
  have hG₁ : D₁ * G * D₁⁻¹ = G₁ := by
    rw [hG, conj_ssorG hD1u, hXT, hY, hX, hYT]
    change _ = (1 + ω • L₁ᵀ)⁻¹ * (1 + ω • L₁)⁻¹ * ((1 - ω) • 1 - ω • L₁) *
      ((1 - ω) • 1 - ω • L₁ᵀ)
    rw [Matrix.mul_assoc (1 + ω • L₁ᵀ)⁻¹, hcomm, ← Matrix.mul_assoc]
  refine ⟨hD1, hG₁, fun l v hv hv1 => ?_⟩
  -- the eigenvalue
  have hYT' : ((1 - ω) • (1 : Matrix (Fin n) (Fin n) ℝ) - ω • L₁)ᵀ = (1 - ω) • 1 - ω • L₁ᵀ := by
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_one]
  have hXT' : (1 + ω • L₁)ᵀ = 1 + ω • L₁ᵀ := by
    rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one]
  have key : ((1 - ω) • 1 - ω • L₁) *ᵥ (((1 - ω) • 1 - ω • L₁ᵀ) *ᵥ v) =
      l • ((1 + ω • L₁) *ᵥ ((1 + ω • L₁ᵀ) *ᵥ v)) := by
    have h1 : ((1 + ω • L₁) * (1 + ω • L₁ᵀ)) *ᵥ (G₁ *ᵥ v) =
        ((1 - ω) • 1 - ω • L₁) *ᵥ (((1 - ω) • 1 - ω • L₁ᵀ) *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      congr 1
      change (1 + ω • L₁) * (1 + ω • L₁ᵀ) * ((1 + ω • L₁ᵀ)⁻¹ * (1 + ω • L₁)⁻¹ *
        ((1 - ω) • 1 - ω • L₁) * ((1 - ω) • 1 - ω • L₁ᵀ)) = _
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hXTd,
        Matrix.mul_nonsing_inv_cancel_left _ _ hXd]
    rw [← h1, hv, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
  set a := ((1 - ω) • (1 : Matrix (Fin n) (Fin n) ℝ) - ω • L₁ᵀ) *ᵥ v with ha
  set c := (1 + ω • L₁ᵀ) *ᵥ v with hc
  have hdot := congrArg (v ⬝ᵥ ·) key
  simp only [dotProduct_smul, dotProduct_mulVec_eq, hYT', hXT', smul_eq_mul] at hdot
  have ha' : a = (1 - ω) • v - ω • L₁ᵀ *ᵥ v := by
    rw [ha, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hc' : c = v + ω • L₁ᵀ *ᵥ v := by
    rw [hc, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp at hv1
  have hc0 : c ≠ 0 := by
    intro h0
    apply hv0
    rw [← Matrix.nonsing_inv_mulVec_mulVec hXTu v, ← hc, h0, Matrix.mulVec_zero]
  have hcc : c ⬝ᵥ c ≠ 0 := fun h0 => hc0 (dotProduct_self_eq_zero.1 h0)
  have hl : l = a ⬝ᵥ a / (c ⬝ᵥ c) := (eq_div_iff hcc).2 hdot.symm
  rw [← ha', ← hc']
  refine ⟨hl, ?_⟩
  set w := L₁ᵀ *ᵥ v
  have hwv : w ⬝ᵥ v = v ⬝ᵥ w := dotProduct_comm _ _
  have haa : a ⬝ᵥ a = c ⬝ᵥ c - ω * (2 - ω) * (1 + 2 * (v ⬝ᵥ w)) := by
    rw [ha', hc']
    simp only [dotProduct_sub, sub_dotProduct, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, hwv, hv1]
    ring
  rw [hl, haa, sub_div, div_self hcc]

/-! ### The Chebyshev semi-iterative method -/

/-- **(11.2.28).** The semi-iterative combination `y⁽ᵏ⁾ = ∑_{j=0}^{k} ν_j(k) x⁽ʲ⁾` of the iterates
`x⁽ʲ⁾` of a splitting, for a coefficient array `ν : Fin (k + 1) → ℝ` (the polynomial
`p_k(z) = ∑_j ν_j(k) z^j`). -/
def semiIterativeCombination {k : ℕ} (ν : Fin (k + 1) → ℝ) (xs : ℕ → Fin n → ℝ) : Fin n → ℝ :=
  ∑ j : Fin (k + 1), ν j • xs j

/-- **§11.2.8.** If `p_k(1) = ∑_j ν_j(k) = 1`, then `y⁽ᵏ⁾ − x = p_k(G) e⁽⁰⁾` with `G = M⁻¹N`,
`e⁽⁰⁾ = x⁽⁰⁾ − x`, for the iterates `x⁽ʲ⁾` of the splitting from `x⁽⁰⁾` and `A x = b`. -/
theorem semiIterative_sub_eq {A : Matrix (Fin n) (Fin n) ℝ} (s : Stationary.Splitting A)
    {b x : Fin n → ℝ} (hx : A *ᵥ x = b) (x₀ : Fin n → ℝ) {k : ℕ} (ν : Fin (k + 1) → ℝ)
    (hν : ∑ j, ν j = 1) :
    semiIterativeCombination ν (fun j => (s.mulVecStep b)^[j] x₀) - x =
      Polynomial.aeval s.iterationOperator (∑ j : Fin (k + 1), C (ν j) * X ^ (j : ℕ)) *ᵥ
        (x₀ - x) := by
  have hx' : x = ∑ j : Fin (k + 1), ν j • x := by rw [← Finset.sum_smul, hν, one_smul]
  rw [semiIterativeCombination]
  conv_lhs => rw [hx', ← Finset.sum_sub_distrib]
  simp only [← smul_sub, equation_11_2_7 s hx, map_sum, map_mul, Polynomial.aeval_C,
    Polynomial.aeval_X_pow, Matrix.sum_mulVec, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
    Matrix.one_mul, Matrix.smul_mulVec]

open scoped Matrix.Norms.L2Operator in
/-- **(11.2.29).** `‖y⁽ᵏ⁾ − x‖₂ ≤ ‖p_k(G)‖₂ ‖e⁽⁰⁾‖₂`. -/
theorem equation_11_2_29 {A : Matrix (Fin n) (Fin n) ℝ} (s : Stationary.Splitting A)
    {b x : Fin n → ℝ} (hx : A *ᵥ x = b) (x₀ : Fin n → ℝ) {k : ℕ} (ν : Fin (k + 1) → ℝ)
    (hν : ∑ j, ν j = 1) :
    ‖WithLp.toLp 2 (semiIterativeCombination ν (fun j => (s.mulVecStep b)^[j] x₀) - x)‖ ≤
      ‖Polynomial.aeval s.iterationOperator (∑ j : Fin (k + 1), C (ν j) * X ^ (j : ℕ))‖ *
        ‖WithLp.toLp 2 (x₀ - x)‖ := by
  rw [semiIterative_sub_eq s hx x₀ ν hν]
  exact Matrix.l2_opNorm_mulVec _ (WithLp.toLp 2 (x₀ - x))

/-- The Chebyshev polynomial of §11.2.8, `p_k(z) = c_k(−1 + 2(z − α)/(β − α)) / c_k(μ)`,
`μ = −1 + 2(1 − α)/(β − α)`. -/
noncomputable def chebyshevSemiIterativePoly (α β : ℝ) (k : ℕ) : ℝ[X] :=
  C ((Chebyshev.T ℝ k).eval (-1 + 2 * (1 - α) / (β - α)))⁻¹ *
    (Chebyshev.T ℝ k).comp (C (2 / (β - α)) * X + C (-1 - 2 * α / (β - α)))

/-- The value of the Chebyshev polynomial of §11.2.8. -/
private theorem eval_chebyshevSemiIterativePoly {α β : ℝ} (hαβ : α < β) (k : ℕ) (t : ℝ) :
    (chebyshevSemiIterativePoly α β k).eval t =
      ((Chebyshev.T ℝ k).eval (-1 + 2 * (1 - α) / (β - α)))⁻¹ *
        (Chebyshev.T ℝ k).eval (-1 + 2 * (t - α) / (β - α)) := by
  have hba : β - α ≠ 0 := by linarith
  have hl : 2 / (β - α) * t + (-1 - 2 * α / (β - α)) = -1 + 2 * (t - α) / (β - α) := by
    field_simp
    ring
  simp only [chebyshevSemiIterativePoly, eval_mul, eval_C, eval_comp, eval_add, eval_X, hl]

/-- The Chebyshev polynomial of §11.2.8 has degree at most `k`. -/
private theorem natDegree_chebyshevSemiIterativePoly_lt (α β : ℝ) (k : ℕ) :
    (chebyshevSemiIterativePoly α β k).natDegree < k + 1 := by
  have hT : (Chebyshev.T ℝ k).natDegree = k := by rw [Chebyshev.natDegree_T]; simp
  refine Nat.lt_succ_of_le ((natDegree_C_mul_le _ _).trans (natDegree_comp_le.trans ?_))
  calc (Chebyshev.T ℝ k).natDegree * (C (2 / (β - α)) * X + C (-1 - 2 * α / (β - α))).natDegree
      ≤ k * 1 := Nat.mul_le_mul hT.le natDegree_linear_le
    _ = k := mul_one k

/-- **§11.2.8, the Chebyshev bound.** Let `G` be symmetric with eigenvalues in `[α, β]`,
`−1 < α < β < 1` ((11.2.30)), `μ = −1 + 2(1 − α)/(β − α) = 1 + 2(1 − β)/(β − α) > 1` and
`p_k(z) = c_k(−1 + 2(z − α)/(β − α)) / c_k(μ)`. Then `p_k(1) = 1`, `|p_k| ≤ 1/|c_k(μ)|` on `[α, β]`,
and the semi-iterative combination with the coefficients of `p_k` satisfies
`‖y⁽ᵏ⁾ − x‖₂ ≤ ‖x − x⁽⁰⁾‖₂ / |c_k(μ)|`. (The book writes `λ_i ∈ λ(A)` for `λ(G)`.) -/
theorem chebyshevSemiIterative_norm_le {A : Matrix (Fin n) (Fin n) ℝ} (s : Stationary.Splitting A)
    (hG : s.iterationOperator.IsHermitian) {α β : ℝ} (hα : -1 < α) (hαβ : α < β) (hβ : β < 1)
    (hGab : ∀ i, hG.eigenvalues i ∈ Set.Icc α β) {b x : Fin n → ℝ} (hx : A *ᵥ x = b)
    (x₀ : Fin n → ℝ) (k : ℕ) :
    (chebyshevSemiIterativePoly α β k).eval 1 = 1 ∧
      (∀ t ∈ Set.Icc α β, |(chebyshevSemiIterativePoly α β k).eval t| ≤
        1 / |(Chebyshev.T ℝ k).eval (-1 + 2 * (1 - α) / (β - α))|) ∧
      ‖WithLp.toLp 2 (semiIterativeCombination
          (fun j : Fin (k + 1) => (chebyshevSemiIterativePoly α β k).coeff j)
          (fun j => (s.mulVecStep b)^[j] x₀) - x)‖ ≤
        ‖WithLp.toLp 2 (x - x₀)‖ / |(Chebyshev.T ℝ k).eval (-1 + 2 * (1 - α) / (β - α))| := by
  have hba : 0 < β - α := by linarith
  have hμ : 1 ≤ -1 + 2 * (1 - α) / (β - α) := by
    have : 2 ≤ 2 * (1 - α) / (β - α) := by
      rw [le_div_iff₀ hba]
      linarith
    linarith
  have hT := Chebyshev.one_le_eval_T hμ k
  have hT0 : (Chebyshev.T ℝ k).eval (-1 + 2 * (1 - α) / (β - α)) ≠ 0 := by linarith
  set p := chebyshevSemiIterativePoly α β k with hp
  have h1 : p.eval 1 = 1 := by
    rw [hp, eval_chebyshevSemiIterativePoly hαβ]
    exact inv_mul_cancel₀ hT0
  have h2 : ∀ t ∈ Set.Icc α β, |p.eval t| ≤
      1 / |(Chebyshev.T ℝ k).eval (-1 + 2 * (1 - α) / (β - α))| := by
    intro t ht
    rw [hp, eval_chebyshevSemiIterativePoly hαβ, abs_mul, abs_inv, ← div_eq_inv_mul]
    refine div_le_div_of_nonneg_right (Chebyshev.abs_eval_T_real_le_one _ ?_) (abs_nonneg _)
    rw [abs_le]
    constructor
    · have : 0 ≤ 2 * (t - α) / (β - α) := div_nonneg (by linarith [ht.1]) hba.le
      linarith
    · have : 2 * (t - α) / (β - α) ≤ 2 := by
        rw [div_le_iff₀ hba]; linarith [ht.2]
      linarith
  refine ⟨h1, h2, ?_⟩
  have hdeg := natDegree_chebyshevSemiIterativePoly_lt α β k
  have hν : ∑ j : Fin (k + 1), p.coeff j = 1 := by
    rw [← h1, eval_eq_sum_range' hdeg, ← Fin.sum_univ_eq_sum_range (fun i => p.coeff i * 1 ^ i)]
    simp
  have hpoly : ∑ j : Fin (k + 1), C (p.coeff j) * X ^ (j : ℕ) = p := by
    rw [Fin.sum_univ_eq_sum_range (fun i => C (p.coeff i) * X ^ i)]
    conv_rhs => rw [p.as_sum_range' _ hdeg]
    simp only [C_mul_X_pow_eq_monomial]
  rw [semiIterative_sub_eq s hx x₀ _ hν, hpoly, ← Matrix.toEuclideanLin_toLp,
    Matrix.toEuclideanLin_aeval]
  have hB := Matrix.IsHermitian.isSymmetricBoundedBy_toEuclideanLin hG hGab
  have hle := hB.norm_aeval_map_apply_le p (WithLp.toLp 2 (x₀ - x))
  rw [show p.map (algebraMap ℝ ℝ) = p by rw [Algebra.algebraMap_self, Polynomial.map_id]] at hle
  refine hle.trans ?_
  have hS : sSup ((fun t => |p.eval t|) '' Set.Icc α β) ≤
      1 / |(Chebyshev.T ℝ k).eval (-1 + 2 * (1 - α) / (β - α))| :=
    csSup_le ((Set.nonempty_Icc.2 hαβ.le).image _) (Set.forall_mem_image.2 h2)
  have hn : ‖WithLp.toLp 2 (x₀ - x)‖ = ‖WithLp.toLp 2 (x - x₀)‖ := by
    rw [← norm_neg, ← WithLp.toLp_neg, neg_sub]
  calc sSup ((fun t => |p.eval t|) '' Set.Icc α β) * ‖WithLp.toLp 2 (x₀ - x)‖
      ≤ 1 / |(Chebyshev.T ℝ k).eval (-1 + 2 * (1 - α) / (β - α))| * ‖WithLp.toLp 2 (x₀ - x)‖ :=
        mul_le_mul_of_nonneg_right hS (norm_nonneg _)
    _ = _ := by rw [hn, one_div, inv_mul_eq_div]

/-- The update `y⁽ᵏ⁺¹⁾ = y⁽ᵏ⁻¹⁾ + ω (y⁽ᵏ⁾ + z⁽ᵏ⁾ − y⁽ᵏ⁻¹⁾)` of §11.2.8, entrywise. -/
def chebyshevCombine {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) (yp y z : Fin n → ℝ) (ω : ℝ) :
    M (Fin n → ℝ) :=
  (List.finRange n).foldlM (fun w i => do
    let s₁ ← rnd (y i + z i)
    let s₂ ← rnd (s₁ - yp i)
    let s₃ ← rnd (ω * s₂)
    pure (Function.update w i (← rnd (yp i + s₃)))) y

/-- One pass of the `while` loop of the Chebyshev semi-iterative method, on the state
`(k, c_{k−1}, c_k, y⁽ᵏ⁻¹⁾, y⁽ᵏ⁾, r⁽ᵏ⁾, done)`. -/
noncomputable def chebyshevSemiIterativeStep {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)
    (solveM : (Fin n → ℝ) → M (Fin n → ℝ)) (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (β tol : ℝ) (st : ℕ × ℝ × ℝ × (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) × Bool) :
    M (ℕ × ℝ × ℝ × (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) × Bool) := do
  let (k, cp, c, yp, y, r, done) := st
  if done then pure st else do
    let rr ← GolubVanLoan.Chapter01.algorithm_1_1_1 rnd r r
    let nr ← rnd (Real.sqrt rr)
    if nr ≤ tol then pure (k, cp, c, yp, y, r, true) else do
      let tb ← rnd (2 / β)
      let tc ← rnd (tb * c)
      let c' ← rnd (tc - cp)
      let q ← rnd (cp / c')
      let ω ← rnd (1 + q)
      let z ← solveM r
      let y' ← chebyshevCombine rnd yp y z ω
      let Ay' ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd A y' 0
      let r' ← Chapter01.vecSub rnd b Ay'
      pure (k + 1, c, c', y, y', r', false)

/-- **The Chebyshev semi-iterative method** of §11.2.8 (the case `α = −β`), a program with a
tolerance and fuel, accelerating `M x⁽ʲ⁺¹⁾ = N x⁽ʲ⁾ + b`:
```
c_0 = 1; c_1 = 1/β
y^(0) = x^(0), M y^(1) = N y^(0) + b, r^(1) = b − A y^(1), k = 1
while ‖r^(k)‖ > tol
    c_{k+1} = (2/β) c_k − c_{k−1}
    ω_{k+1} = 1 + c_{k−1}/c_{k+1}
    M z^(k) = r^(k)
    y^(k+1) = y^(k−1) + ω_{k+1} (y^(k) + z^(k) − y^(k−1))
    k = k + 1
    r^(k) = b − A y^(k)
end
```
The solves with `M` are a routine `solveM` (exact semantics `M⁻¹`); the products are ch01's gaxpy
(Algorithm 1.1.3) and dot product (Algorithm 1.1.1), the test compares the computed
`fl(√fl(rᵀr))` with `tol`. The state is `(k, c_{k−1}, c_k, y^(k−1), y^(k), r^(k), done)`. -/
noncomputable def chebyshevSemiIterative {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)
    (solveM : (Fin n → ℝ) → M (Fin n → ℝ)) (A N : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ)
    (β tol : ℝ) (fuel : ℕ) :
    M (ℕ × ℝ × ℝ × (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) × Bool) := do
  let rhs ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd N x₀ b
  let y₁ ← solveM rhs
  let Ay₁ ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd A y₁ 0
  let r₁ ← Chapter01.vecSub rnd b Ay₁
  let c₁ ← rnd (1 / β)
  (List.range fuel).foldlM (fun st _ => chebyshevSemiIterativeStep rnd solveM A b β tol st)
    (1, 1, c₁, x₀, y₁, r₁, false)

/-- The polynomial `c_k(z/β)/c_k(1/β)` of the case `α = −β`. -/
noncomputable def chebyshevSymmetricPoly (β : ℝ) (k : ℕ) : ℝ[X] :=
  C ((Chebyshev.T ℝ k).eval (1 / β))⁻¹ * (Chebyshev.T ℝ k).comp (C (1 / β) * X)

/-- The exact update of §11.2.8. -/
private theorem chebyshevCombine_id (yp y z : Fin n → ℝ) (ω : ℝ) :
    Id.run (chebyshevCombine pure yp y z ω) = yp + ω • (y + z - yp) := by
  have hrun : Id.run (chebyshevCombine pure yp y z ω) = (List.finRange n).foldl
      (fun w i => Function.update w i (yp i + ω * (y i + z i - yp i))) y := List.idRun_foldlM
  rw [hrun]
  funext i
  exact List.foldl_update_apply_of_pairwise_rel (· < ·) (fun _ _ h h' => lt_asymm h h')
    (fun i _ => yp i + ω * (y i + z i - yp i)) (List.pairwise_lt_finRange n) y
    (List.mem_finRange i)

/-- The exact step of the Chebyshev loop. -/
private theorem chebyshevSemiIterativeStep_id (Minv A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ) (β tol : ℝ) (k : ℕ) (cp c : ℝ) (yp y r : Fin n → ℝ) :
    Id.run (chebyshevSemiIterativeStep pure (fun r => pure (Minv *ᵥ r)) A b β tol
        (k, cp, c, yp, y, r, false)) =
      if Real.sqrt (r ⬝ᵥ r) ≤ tol then (k, cp, c, yp, y, r, true) else
        (k + 1, c, 2 / β * c - cp, y,
          yp + (1 + cp / (2 / β * c - cp)) • (y + Minv *ᵥ r - yp),
          b - A *ᵥ (yp + (1 + cp / (2 / β * c - cp)) • (y + Minv *ᵥ r - yp)), false) := by
  have h : Id.run (chebyshevSemiIterativeStep pure (fun r => pure (Minv *ᵥ r)) A b β tol
      (k, cp, c, yp, y, r, false)) =
      if Real.sqrt (Id.run (GolubVanLoan.Chapter01.algorithm_1_1_1 pure r r)) ≤ tol then
        (k, cp, c, yp, y, r, true) else
        (k + 1, c, 2 / β * c - cp, y,
          Id.run (chebyshevCombine pure yp y (Minv *ᵥ r) (1 + cp / (2 / β * c - cp))),
          Id.run (Chapter01.vecSub pure b (Id.run (GolubVanLoan.Chapter01.algorithm_1_1_3 pure A
            (Id.run (chebyshevCombine pure yp y (Minv *ᵥ r) (1 + cp / (2 / β * c - cp)))) 0))),
          false) := rfl
  rw [h, GolubVanLoan.Chapter01.algorithm_1_1_1_spec, chebyshevCombine_id,
    GolubVanLoan.Chapter01.algorithm_1_1_3_spec, Chapter01.vecSub_spec, zero_add]

/-- The values `c_j = T_j(1/β)` of §11.2.8. -/
private noncomputable def chebC (β : ℝ) (j : ℕ) : ℝ := (Chebyshev.T ℝ j).eval (1 / β)

/-- The three-term recurrence of the `c_j`. -/
private theorem chebC_add_two (β : ℝ) (j : ℕ) :
    chebC β (j + 2) = 2 / β * chebC β (j + 1) - chebC β j := by
  have h := Chebyshev.T_add_two ℝ (j : ℤ)
  simp only [chebC]
  push_cast
  rw [h, eval_sub, eval_mul, eval_mul, eval_X, eval_ofNat]
  ring

/-- The `c_j` are at least `1` when `0 < β < 1`. -/
private theorem one_le_chebC {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (j : ℕ) : 1 ≤ chebC β j :=
  Chebyshev.one_le_eval_T (by rw [le_div_iff₀ hβ0]; linarith) j

/-- The vectors `T_j(G/β) e`. -/
private noncomputable def chebV (G : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) (e : Fin n → ℝ) (j : ℕ) :
    Fin n → ℝ :=
  Polynomial.aeval G ((Chebyshev.T ℝ j).comp (C (1 / β) * X)) *ᵥ e

/-- The three-term recurrence of the vectors `T_j(G/β) e`. -/
private theorem chebV_add_two (G : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) (e : Fin n → ℝ) (j : ℕ) :
    chebV G β e (j + 2) = (2 / β) • (G *ᵥ chebV G β e (j + 1)) - chebV G β e j := by
  have h := Chebyshev.T_add_two ℝ (j : ℤ)
  simp only [chebV]
  push_cast
  rw [h]
  simp only [sub_comp, mul_comp, ofNat_comp, X_comp, map_sub, map_mul, aeval_C,
    aeval_X, Algebra.algebraMap_eq_smul_one, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [map_natCast, show ((2 : ℕ) : Matrix (Fin n) (Fin n) ℝ) = (2 : ℝ) • 1 by
    rw [Nat.cast_ofNat, two_smul, one_add_one_eq_two]]
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul]
  module

/-- `p_j(G) e = c_j⁻¹ T_j(G/β) e`. -/
private theorem aeval_chebyshevSymmetricPoly (G : Matrix (Fin n) (Fin n) ℝ) (β : ℝ)
    (e : Fin n → ℝ) (j : ℕ) :
    Polynomial.aeval G (chebyshevSymmetricPoly β j) *ᵥ e = (chebC β j)⁻¹ • chebV G β e j := by
  simp only [chebyshevSymmetricPoly, chebV, chebC, map_mul, aeval_C,
    Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mulVec]

/-- The scalar identity behind the three-term recurrence of §11.2.8. -/
private theorem cheb_combine {β a b c ω : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hrec : c = 2 / β * b - a) (hω : ω = 1 + a / c) (u w : Fin n → ℝ) :
    (1 - ω) • (a⁻¹ • u) + ω • (b⁻¹ • w) = c⁻¹ • ((2 / β) • w - u) := by
  have hca : c + a = 2 / β * b := by linarith
  have h1 : (1 - ω) * a⁻¹ = -c⁻¹ := by
    rw [hω, show (1 : ℝ) - (1 + a / c) = -(a / c) by ring, neg_mul, div_mul_eq_mul_div,
      mul_inv_cancel₀ ha, one_div]
  have h2 : ω * b⁻¹ = c⁻¹ * (2 / β) := by
    calc ω * b⁻¹ = (c + a) / c * b⁻¹ := by rw [hω, add_div, div_self hc]
      _ = 2 / β * b / c * b⁻¹ := by rw [hca]
      _ = c⁻¹ * (2 / β) := by
        rw [div_mul_eq_mul_div, mul_assoc, mul_inv_cancel₀ hb, mul_one, div_eq_inv_mul]
  rw [smul_smul, smul_smul, h1, h2]
  module

/-- **Exact semantics of the Chebyshev semi-iterative method.** For a splitting `A = M − N`,
`A x = b`, `0 < β < 1`, the exact run with `solveM = M⁻¹` (any tolerance and fuel) returns a state
`(k, …, y^(k), …)` with `y^(k) − x = p_k(G)(x^(0) − x)`, `p_k(z) = c_k(z/β)/c_k(1/β)` — the `α = −β`
case of the polynomial of `chebyshevSemiIterative_norm_le` (`chebyshevSymmetricPoly_eq`), so the
bound there applies (`chebyshevSemiIterative_norm_le'`). -/
theorem chebyshevSemiIterative_spec {A : Matrix (Fin n) (Fin n) ℝ} (s : Stationary.Splitting A)
    {b x : Fin n → ℝ} (hx : A *ᵥ x = b) (x₀ : Fin n → ℝ) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (tol : ℝ) (fuel : ℕ) :
    let st := Id.run (chebyshevSemiIterative pure (fun r => pure (s.m⁻¹ *ᵥ r)) A s.n b x₀ β tol
      fuel)
    st.2.2.2.2.1 - x =
      Polynomial.aeval s.iterationOperator (chebyshevSymmetricPoly β st.1) *ᵥ (x₀ - x) := by
  intro st
  set G := s.iterationOperator
  set e := x₀ - x
  have hCpos : ∀ j, chebC β j ≠ 0 := fun j => by linarith [one_le_chebC hβ0 hβ1 j]
  -- the invariant
  let Inv : ℕ × ℝ × ℝ × (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) × Bool → Prop := fun st =>
    ∃ j, st.1 = j + 1 ∧ st.2.1 = chebC β j ∧ st.2.2.1 = chebC β (j + 1) ∧
      st.2.2.2.1 - x = (chebC β j)⁻¹ • chebV G β e j ∧
      st.2.2.2.2.1 - x = (chebC β (j + 1))⁻¹ • chebV G β e (j + 1) ∧
      st.2.2.2.2.2.1 = b - A *ᵥ st.2.2.2.2.1
  have hstep : ∀ st, Inv st → Inv (Id.run
      (chebyshevSemiIterativeStep pure (fun r => pure (s.m⁻¹ *ᵥ r)) A b β tol st)) := by
    rintro ⟨k, cp, c, yp, y, r, d⟩ ⟨j, hk, hcp, hc, hyp, hy, hr⟩
    dsimp only at hk hcp hc hyp hy hr
    cases d with
    | true => exact ⟨j, hk, hcp, hc, hyp, hy, hr⟩
    | false =>
      rw [chebyshevSemiIterativeStep_id]
      split_ifs
      · exact ⟨j, hk, hcp, hc, hyp, hy, hr⟩
      · have hc' : 2 / β * c - cp = chebC β (j + 2) := by rw [hcp, hc, chebC_add_two]
        refine ⟨j + 1, by rw [hk], hc, hc', hy, ?_, rfl⟩
        dsimp only
        rw [hc']
        have hz : y + s.m⁻¹ *ᵥ r - x = G *ᵥ (y - x) := by
          rw [hr, ← Stationary.Splitting.mulVecStep_eq_add_inv_mulVec]
          exact mulVecStep_sub s hx y
        have e1 : yp + (1 + cp / chebC β (j + 2)) • (y + s.m⁻¹ *ᵥ r - yp) - x =
            (1 - (1 + cp / chebC β (j + 2))) • (yp - x) +
              (1 + cp / chebC β (j + 2)) • (y + s.m⁻¹ *ᵥ r - x) := by
          module
        rw [e1, hz, hyp, hy, Matrix.mulVec_smul, hcp, chebV_add_two]
        exact cheb_combine (hCpos j) (hCpos (j + 1)) (hCpos (j + 2))
          (chebC_add_two β j) rfl _ _
  have hinv : ∀ (l : List ℕ) st, Inv st → Inv (l.foldl (fun st _ => Id.run
      (chebyshevSemiIterativeStep pure (fun r => pure (s.m⁻¹ *ᵥ r)) A b β tol st)) st) := by
    intro l
    induction l with
    | nil => exact fun _ h => h
    | cons a l ih => exact fun st h => ih _ (hstep st h)
  have hinit : Inv (1, 1, 1 / β, x₀, s.m⁻¹ *ᵥ (b + s.n *ᵥ x₀),
      b - A *ᵥ (s.m⁻¹ *ᵥ (b + s.n *ᵥ x₀)), false) := by
    refine ⟨0, rfl, ?_, ?_, ?_, ?_, rfl⟩
    · simp [chebC]
    · simp [chebC]
    · simp [chebC, chebV, e]
    · have h1 : s.m⁻¹ *ᵥ (b + s.n *ᵥ x₀) = s.mulVecStep b x₀ := by
        change _ = s.m⁻¹ *ᵥ (s.n *ᵥ x₀ + b); rw [add_comm]
      dsimp only
      rw [h1, mulVecStep_sub s hx]
      simp only [chebV, chebC, zero_add, Nat.cast_one, Chebyshev.T_one, X_comp, eval_X,
        map_mul, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul,
        Matrix.one_mul, Matrix.smul_mulVec, smul_smul]
      rw [one_div, inv_inv, mul_inv_cancel₀ hβ0.ne', one_smul]
  have hst : st = (List.range fuel).foldl (fun st _ => Id.run
      (chebyshevSemiIterativeStep pure (fun r => pure (s.m⁻¹ *ᵥ r)) A b β tol st))
      (1, 1, 1 / β, x₀, s.m⁻¹ *ᵥ (b + s.n *ᵥ x₀),
        b - A *ᵥ (s.m⁻¹ *ᵥ (b + s.n *ᵥ x₀)), false) := by
    have h : st = (List.range fuel).foldl (fun st _ => Id.run
        (chebyshevSemiIterativeStep pure (fun r => pure (s.m⁻¹ *ᵥ r)) A b β tol st))
        (1, 1, 1 / β, x₀,
          s.m⁻¹ *ᵥ Id.run (GolubVanLoan.Chapter01.algorithm_1_1_3 pure s.n x₀ b),
          Id.run (Chapter01.vecSub pure b (Id.run (GolubVanLoan.Chapter01.algorithm_1_1_3 pure A
            (s.m⁻¹ *ᵥ Id.run (GolubVanLoan.Chapter01.algorithm_1_1_3 pure s.n x₀ b)) 0))),
          false) := List.idRun_foldlM
    rw [h, GolubVanLoan.Chapter01.algorithm_1_1_3_spec, GolubVanLoan.Chapter01.algorithm_1_1_3_spec,
      Chapter01.vecSub_spec, zero_add]
  have hfin := hinv (List.range fuel) _ hinit
  rw [← hst] at hfin
  obtain ⟨j, hk, -, -, -, hy, -⟩ := hfin
  rw [hk, aeval_chebyshevSymmetricPoly]
  exact hy

/-- The polynomial of the case `α = −β` is the §11.2.8 polynomial at `α = −β`:
`−1 + 2(z + β)/(2β) = z/β` and `μ = 1/β`. -/
theorem chebyshevSymmetricPoly_eq {β : ℝ} (hβ : β ≠ 0) (k : ℕ) :
    chebyshevSymmetricPoly β k = chebyshevSemiIterativePoly (-β) β k := by
  have hb2 : β - -β = 2 * β := by ring
  have h1 : -1 + 2 * (1 - -β) / (β - -β) = 1 / β := by
    rw [hb2]; field_simp; ring
  have h2 : 2 / (β - -β) = 1 / β := by
    rw [hb2]; field_simp
  have h3 : -1 - 2 * -β / (β - -β) = 0 := by
    rw [hb2]; field_simp; ring
  rw [chebyshevSemiIterativePoly, h1, h2, h3, C_0, add_zero, chebyshevSymmetricPoly]

/-- **§11.2.8, the Chebyshev bound for the program**: for `G` symmetric with eigenvalues in
`[−β, β]`, `0 < β < 1`, the exact run of `chebyshevSemiIterative` after `k` steps satisfies
`‖y⁽ᵏ⁾ − x‖₂ ≤ ‖x − x⁽⁰⁾‖₂ / |c_k(1/β)|` — `chebyshevSemiIterative_norm_le` at `α = −β`, through
`chebyshevSemiIterative_spec` and `chebyshevSymmetricPoly_eq`. -/
theorem chebyshevSemiIterative_norm_le' {A : Matrix (Fin n) (Fin n) ℝ}
    (s : Stationary.Splitting A) (hG : s.iterationOperator.IsHermitian) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hGab : ∀ i, hG.eigenvalues i ∈ Set.Icc (-β) β) {b x : Fin n → ℝ}
    (hx : A *ᵥ x = b) (x₀ : Fin n → ℝ) (tol : ℝ) (fuel : ℕ) :
    let st := Id.run (chebyshevSemiIterative pure (fun r => pure (s.m⁻¹ *ᵥ r)) A s.n b x₀ β tol
      fuel)
    ‖WithLp.toLp 2 (st.2.2.2.2.1 - x)‖ ≤
      ‖WithLp.toLp 2 (x - x₀)‖ / |(Chebyshev.T ℝ st.1).eval (1 / β)| := by
  intro st
  have hspec : st.2.2.2.2.1 - x =
      Polynomial.aeval s.iterationOperator (chebyshevSymmetricPoly β st.1) *ᵥ (x₀ - x) :=
    chebyshevSemiIterative_spec s hx x₀ hβ0 hβ1 tol fuel
  have hμ : -1 + 2 * (1 - -β) / (β - -β) = 1 / β := by
    rw [show β - -β = 2 * β by ring]; field_simp; ring
  have h2 := (chebyshevSemiIterative_norm_le s hG (by linarith) (by linarith) hβ1 hGab hx x₀
    st.1).2.1
  rw [hμ] at h2
  rw [hspec, chebyshevSymmetricPoly_eq hβ0.ne', ← Matrix.toEuclideanLin_toLp,
    Matrix.toEuclideanLin_aeval]
  set p := chebyshevSemiIterativePoly (-β) β st.1
  have hB := Matrix.IsHermitian.isSymmetricBoundedBy_toEuclideanLin hG hGab
  have hle := hB.norm_aeval_map_apply_le p (WithLp.toLp 2 (x₀ - x))
  rw [show p.map (algebraMap ℝ ℝ) = p by rw [Algebra.algebraMap_self, Polynomial.map_id]] at hle
  refine hle.trans ?_
  have hS : sSup ((fun t => |p.eval t|) '' Set.Icc (-β) β) ≤
      1 / |(Chebyshev.T ℝ st.1).eval (1 / β)| :=
    csSup_le ((Set.nonempty_Icc.2 (by linarith)).image _) (Set.forall_mem_image.2 h2)
  have hn : ‖WithLp.toLp 2 (x₀ - x)‖ = ‖WithLp.toLp 2 (x - x₀)‖ := by
    rw [← norm_neg, ← WithLp.toLp_neg, neg_sub]
  calc sSup ((fun t => |p.eval t|) '' Set.Icc (-β) β) * ‖WithLp.toLp 2 (x₀ - x)‖
      ≤ 1 / |(Chebyshev.T ℝ st.1).eval (1 / β)| * ‖WithLp.toLp 2 (x₀ - x)‖ :=
        mul_le_mul_of_nonneg_right hS (norm_nonneg _)
    _ = _ := by rw [hn, one_div, inv_mul_eq_div]

end GolubVanLoan.Chapter11

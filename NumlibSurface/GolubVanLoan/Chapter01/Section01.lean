import Mathlib.LinearAlgebra.Matrix.RowCol
import Numlib.FloatingPoint.Program

/-!
# Golub–Van Loan §1.1: basic algorithms and notation

Surface file for Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th edition, §1.1:
the dot product and the saxpy (Algorithms 1.1.1–1.1.2), the row- and column-oriented gaxpys
(Algorithms 1.1.3–1.1.4), the four formulations of the update `C = C + A B` — `ijk`, dot product,
saxpy and outer product (Algorithms 1.1.5–1.1.8) — and the outer-product expansion (1.1.4).

## Design

Every algorithm is written once, as a monadic program in the book's loop order, generic in a monad
`M` and a rounding hook `rnd : ℝ → M ℝ` through which every product and every sum passes
(`Numlib/FloatingPoint/Program`, conventions 1–14 of `NumlibSurface/GolubVanLoan`). Data come in
BLAS order (`a x y` for the saxpy, `A x y` for the gaxpys, `A B C` for the products) and the state
is overwritten as the book overwrites it: vectors by `Function.update`, matrices by
`Matrix.updateRow C i (Function.update (C i) j c)` or `Matrix.updateCol`. The colon-notation
algorithms call the scalar ones: Algorithm 1.1.6's `A(i,:)·B(:,j)` is `algorithm_1_1_1`,
Algorithm 1.1.7's `C(:,j) = C(:,j) + A(:,k) B(k,j)` is `algorithm_1_1_2`. Indices are 0-based.

Each algorithm carries three kinds of theorem (convention 12):

* `…_mem_run` characterizes the run set in the relational model (`M := SetM`,
  `rnd := fp.round`) entry by entry: every entry of every run of a gaxpy or of a product is a run
  of the backbone accumulation `FloatingPoint.dotAccum` onto the initial entry, *whatever the loop
  order* — the rigorous content of "the same result applies if a gaxpy or outer product based
  procedure is used" in the book's §2.7 ((2.7.19)).
* `…_rounds` (Algorithms 1.1.1 and 1.1.5–1.1.8) is the bridge to the backbone's relational
  inner product `FloatingPoint.RoundsDot` / product `FloatingPoint.RoundsMul`, from which
  chapter 2 reads the bounds `|fl(xᵀy) − xᵀy| ≤ γ_n |x|ᵀ|y|` and `|fl(AB) − AB| ≤ γ_r |A||B|`. The
  book's loops start the accumulation at `c = 0` and round `0 + fl(x₁y₁)`; the relation starts from
  the unrounded first term, so these bridges assume `fp.IsIdempotent` (convention 6).
* `…_spec` is the exact semantics (`M := Id`, `rnd := pure`), read off `…_mem_run` at the exact
  model `FloatingPoint.RoundingModel.exact ℝ` (convention 11): the `Id` run is one of the runs
  there (`…_mem_exact`, private), and there every accumulation is the exact running sum
  (`FloatingPoint.mem_run_dotAccum_exact_iff`).

The run characterizations rest on three loop facts. A loop whose every step reads and rewrites one
component of the state only — one entry, one row, one column — is one update of that component by
the loop run on it alone (`List.foldlM_lens` and its instances `List.foldlM_update_self`,
`Matrix.foldlM_updateRow`, `Matrix.foldlM_updateCol`, `Matrix.foldlM_updateRow_update`, in any
lawful monad). A loop over `List.finRange n` whose
step `i` rewrites entry `i` only has as run set the product of the per-entry run sets
(`SetM.mem_run_foldlM_update_of_nodup`). A loop whose every step acts on every entry independently
is, entry by entry, the loop run on that entry (`SetM.mem_run_foldlM_of_pi`, loop interchange in
the relational model).

## Main results

* `algorithm_1_1_1` … `algorithm_1_1_8` — Algorithms 1.1.1–1.1.8 as programs.
* `algorithm_1_1_1_eq_dotAccum` — the dot product is the backbone accumulation from `0`.
* `algorithm_1_1_N_spec` — the exact specifications `x ⬝ᵥ y`, `y + a • x`, `y + A *ᵥ x`,
  `C + A * B`.
* `algorithm_1_1_N_mem_run` — the run sets, entrywise.
* `algorithm_1_1_1_rounds`, `algorithm_1_1_{5,6,7,8}_rounds` — the bridges to `RoundsDot`,
  `RoundsMul`.
* `equation_1_1_4` — `A B = ∑ₖ aₖ bₖᵀ`.

## Not formalized here

The notation of §1.1.1–1.1.4 and §1.1.7–1.1.8 ((1.1.1)–(1.1.3) are partition notation), the
unnumbered `jki`/`kij` loops (Algorithms 1.1.7/1.1.8 are their colon forms), Table 1.1.1, flops,
big-Oh and the BLAS levels (§1.1.15–1.1.17, Table 1.1.2), §1.1.19's complex notation (Mathlib's
`ᴴ`), the numerical examples.
-/

open FloatingPoint Matrix

namespace GolubVanLoan.Chapter01

/-! ### Loop fusion: a loop acting on one row of its state -/

/-- A loop writing the entries of row `i` of a matrix, each from its current value, is one update of
the row by the loop run on the row vector: `Matrix.foldlM_updateRow` with an entrywise step. -/
theorem foldlM_updateRow_row {M : Type → Type} [Monad M] [LawfulMonad M] {m n : ℕ}
    (i : Fin m) (h : Fin n → ℝ → M ℝ) (l : List (Fin n)) (C₀ : Matrix (Fin m) (Fin n) ℝ) :
    l.foldlM (fun (C : Matrix (Fin m) (Fin n) ℝ) j => do
        let c ← h j (C i j); pure (C.updateRow i (Function.update (C i) j c))) C₀
      = (do
        let r ← l.foldlM (fun (r : Fin n → ℝ) j => do
          let c ← h j (r j); pure (Function.update r j c)) (C₀ i)
        pure (C₀.updateRow i r)) := by
  have := Matrix.foldlM_updateRow i
    (fun j (r : Fin n → ℝ) => do let c ← h j (r j); pure (Function.update r j c)) l C₀
  simpa only [bind_assoc, pure_bind] using this

/-! ### Run sets of loops writing one entry per step -/

/-- **One entry per step, over `List.finRange n`.** A loop whose step `i` rewrites entry `i` from
its current value has as run set the product of the per-entry run sets. -/
private theorem mem_run_foldlM_finRange_update {n : ℕ} {β : Type} (g : Fin n → β → SetM β)
    (y₀ y : Fin n → β) :
    y ∈ ((List.finRange n).foldlM (fun (y : Fin n → β) a => do
        let b ← g a (y a); pure (Function.update y a b)) y₀).run ↔
      ∀ i, y i ∈ (g i (y₀ i)).run := by
  have h := SetM.mem_run_foldlM_update_of_nodup (fun a b (_ : Fin n → β) => g a b)
    (List.finRange n) (List.nodup_finRange n) (fun _ _ _ _ _ _ => rfl) y₀ y
  exact h.trans (by simp [List.mem_finRange])

/-- The row form of `mem_run_foldlM_finRange_update`: a loop whose step `i` rewrites row `i`. -/
private theorem mem_run_foldlM_finRange_updateRow {m n : ℕ}
    (g : Fin m → (Fin n → ℝ) → SetM (Fin n → ℝ)) (C₀ C : Matrix (Fin m) (Fin n) ℝ) :
    C ∈ ((List.finRange m).foldlM (fun (C : Matrix (Fin m) (Fin n) ℝ) i => do
        let r ← g i (C i); pure (C.updateRow i r)) C₀).run ↔
      ∀ i, C i ∈ (g i (C₀ i)).run :=
  mem_run_foldlM_finRange_update (β := Fin n → ℝ) g C₀ C

/-- The column form of `mem_run_foldlM_finRange_update`: a loop whose step `j` rewrites column `j`
from its current value; by transposition. -/
private theorem mem_run_foldlM_finRange_updateCol {m n : ℕ}
    (g : Fin n → (Fin m → ℝ) → SetM (Fin m → ℝ)) (C₀ C : Matrix (Fin m) (Fin n) ℝ) :
    C ∈ ((List.finRange n).foldlM (fun (C : Matrix (Fin m) (Fin n) ℝ) j => do
        let c ← g j (fun i => C i j); pure (C.updateCol j c)) C₀).run ↔
      ∀ j, (fun i => C i j) ∈ (g j (fun i => C₀ i j)).run := by
  -- the loop is the transpose of the row loop on `C₀ᵀ`
  have key : ∀ (l : List (Fin n)) (D₀ : Matrix (Fin m) (Fin n) ℝ),
      l.foldlM (fun (C : Matrix (Fin m) (Fin n) ℝ) j => do
          let c ← g j (fun i => C i j); pure (C.updateCol j c)) D₀
        = transpose <$> l.foldlM (fun (D : Matrix (Fin n) (Fin m) ℝ) j => do
            let c ← g j (D j); pure (D.updateRow j c)) D₀ᵀ := by
    intro l
    induction l with
    | nil => intro D₀; simp
    | cons a l ih =>
      intro D₀
      simp only [List.foldlM_cons, bind_assoc, pure_bind, map_bind]
      refine congrArg _ (funext fun c => ?_)
      rw [ih, updateRow_transpose]
  rw [key, SetM.mem_run_map]
  constructor
  · rintro ⟨D, hD, rfl⟩ j
    exact (mem_run_foldlM_finRange_updateRow g C₀ᵀ D).1 hD j
  · intro h
    exact ⟨Cᵀ, (mem_run_foldlM_finRange_updateRow g C₀ᵀ Cᵀ).2 h, transpose_transpose C⟩

/-! ### Algorithm 1.1.1: the dot product -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 1.1.1 (Dot Product).** "If `x, y ∈ ℝⁿ`, then this algorithm computes their dot
product `c = xᵀy`":
```
c = 0
for i = 1:n
    c = c + x(i) y(i)
end
```
with the product and the sum each rounded. -/
def algorithm_1_1_1 {n : ℕ} (x y : Fin n → ℝ) : M ℝ :=
  (List.finRange n).foldlM (fun c k => do rnd (c + (← rnd (x k * y k)))) 0

/-- Algorithm 1.1.1 is the backbone's inner-product accumulation from `c = 0` in the natural order,
which is how chapters 2–3 reach `FloatingPoint.RoundsDot`. -/
theorem algorithm_1_1_1_eq_dotAccum {n : ℕ} (x y : Fin n → ℝ) :
    algorithm_1_1_1 rnd x y = dotAccum rnd (List.finRange n) x y 0 :=
  rfl

/-- **Algorithm 1.1.2 (Saxpy).** "If `x, y ∈ ℝⁿ` and `a ∈ ℝ`, then this algorithm overwrites `y`
with `y + ax`":
```
for i = 1:n
    y(i) = y(i) + a x(i)
end
```
-/
def algorithm_1_1_2 {n : ℕ} (a : ℝ) (x y : Fin n → ℝ) : M (Fin n → ℝ) :=
  (List.finRange n).foldlM (fun y i => do
    let p ← rnd (a * x i)
    let s ← rnd (y i + p)
    pure (Function.update y i s)) y

/-- **Algorithm 1.1.3 (Row-Oriented Gaxpy).** "If `A ∈ ℝ^{m×n}`, `x ∈ ℝⁿ`, and `y ∈ ℝᵐ`, then this
algorithm overwrites `y` with `Ax + y`":
```
for i = 1:m
    for j = 1:n
        y(i) = y(i) + A(i,j) x(j)
    end
end
```
-/
def algorithm_1_1_3 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) (y : Fin m → ℝ) :
    M (Fin m → ℝ) :=
  (List.finRange m).foldlM (fun y i =>
    (List.finRange n).foldlM (fun y j => do
      let p ← rnd (A i j * x j)
      let s ← rnd (y i + p)
      pure (Function.update y i s)) y) y

/-- **Algorithm 1.1.4 (Column-Oriented Gaxpy).** The loops of Algorithm 1.1.3 interchanged:
```
for j = 1:n
    for i = 1:m
        y(i) = y(i) + A(i,j) x(j)
    end
end
```
-/
def algorithm_1_1_4 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) (y : Fin m → ℝ) :
    M (Fin m → ℝ) :=
  (List.finRange n).foldlM (fun y j =>
    (List.finRange m).foldlM (fun y i => do
      let p ← rnd (A i j * x j)
      let s ← rnd (y i + p)
      pure (Function.update y i s)) y) y

/-- **Algorithm 1.1.5 (`ijk` Matrix Multiplication).** "If `A ∈ ℝ^{m×r}`, `B ∈ ℝ^{r×n}`, and
`C ∈ ℝ^{m×n}` are given, then this algorithm overwrites `C` with `C + AB`":
```
for i = 1:m
    for j = 1:n
        for k = 1:r
            C(i,j) = C(i,j) + A(i,k) B(k,j)
        end
    end
end
```
-/
def algorithm_1_1_5 {m r n : ℕ} (A : Matrix (Fin m) (Fin r) ℝ) (B : Matrix (Fin r) (Fin n) ℝ)
    (C : Matrix (Fin m) (Fin n) ℝ) : M (Matrix (Fin m) (Fin n) ℝ) :=
  (List.finRange m).foldlM (fun C i =>
    (List.finRange n).foldlM (fun C j =>
      (List.finRange r).foldlM (fun C k => do
        let p ← rnd (A i k * B k j)
        let c ← rnd (C i j + p)
        pure (C.updateRow i (Function.update (C i) j c))) C) C) C

/-- **Algorithm 1.1.6 (Dot Product Matrix Multiplication).**
```
for i = 1:m
    for j = 1:n
        C(i,j) = C(i,j) + A(i,:)·B(:,j)
    end
end
```
The dot product `A(i,:)·B(:,j)` is formed first, from `0`, by Algorithm 1.1.1, and then added to
`C(i,j)`: a different rounding structure from Algorithm 1.1.5. -/
def algorithm_1_1_6 {m r n : ℕ} (A : Matrix (Fin m) (Fin r) ℝ) (B : Matrix (Fin r) (Fin n) ℝ)
    (C : Matrix (Fin m) (Fin n) ℝ) : M (Matrix (Fin m) (Fin n) ℝ) :=
  (List.finRange m).foldlM (fun C i =>
    (List.finRange n).foldlM (fun C j => do
      let s ← algorithm_1_1_1 rnd (A i) (fun k => B k j)
      let c ← rnd (C i j + s)
      pure (C.updateRow i (Function.update (C i) j c))) C) C

/-- **Algorithm 1.1.7 (Saxpy Matrix Multiplication).**
```
for j = 1:n
    for k = 1:r
        C(:,j) = C(:,j) + A(:,k) B(k,j)
    end
end
```
Each update of column `j` is the saxpy, Algorithm 1.1.2, with `a = B(k,j)` and `x = A(:,k)`. -/
def algorithm_1_1_7 {m r n : ℕ} (A : Matrix (Fin m) (Fin r) ℝ) (B : Matrix (Fin r) (Fin n) ℝ)
    (C : Matrix (Fin m) (Fin n) ℝ) : M (Matrix (Fin m) (Fin n) ℝ) :=
  (List.finRange n).foldlM (fun C j =>
    (List.finRange r).foldlM (fun C k => do
      let c ← algorithm_1_1_2 rnd (B k j) (fun i => A i k) (fun i => C i j)
      pure (C.updateCol j c)) C) C

/-- **Algorithm 1.1.8 (Outer Product Matrix Multiplication).**
```
for k = 1:r
    C = C + A(:,k) B(k,:)
end
```
The outer-product update `C = C + A(:,k) B(k,:)` is written in the row form of §1.1.9: for
`i = 1:m`, for `j = 1:n`, `C(i,j) = C(i,j) + A(i,k) B(k,j)`. -/
def algorithm_1_1_8 {m r n : ℕ} (A : Matrix (Fin m) (Fin r) ℝ) (B : Matrix (Fin r) (Fin n) ℝ)
    (C : Matrix (Fin m) (Fin n) ℝ) : M (Matrix (Fin m) (Fin n) ℝ) :=
  (List.finRange r).foldlM (fun C k =>
    (List.finRange m).foldlM (fun C i =>
      (List.finRange n).foldlM (fun C j => do
        let p ← rnd (A i k * B k j)
        let c ← rnd (C i j + p)
        pure (C.updateRow i (Function.update (C i) j c))) C) C) C

end Programs

/-! ### Normal forms: the loops fused into per-entry accumulations -/

section NormalForms

variable {M : Type → Type} [Monad M] [LawfulMonad M] (rnd : ℝ → M ℝ)

/-- The inner loop of the row gaxpy accumulates into `y i`: Algorithm 1.1.3 is a loop of
accumulations. -/
private theorem algorithm_1_1_3_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ)
    (y : Fin m → ℝ) :
    algorithm_1_1_3 rnd A x y = (List.finRange m).foldlM (fun y i => do
      let s ← dotAccum rnd (List.finRange n) (A i) x (y i); pure (Function.update y i s)) y := by
  unfold algorithm_1_1_3
  congr 1
  funext y i
  have := List.foldlM_update_self i (fun j c => do let p ← rnd (A i j * x j); rnd (c + p))
    (List.finRange n) y
  simp only [bind_assoc] at this
  exact this

/-- Algorithm 1.1.5 as two loops writing one entry per step around the accumulations. -/
private theorem algorithm_1_1_5_eq {m r n : ℕ} (A : Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin r) (Fin n) ℝ) (C : Matrix (Fin m) (Fin n) ℝ) :
    algorithm_1_1_5 rnd A B C = (List.finRange m).foldlM (fun C i => do
      let row ← (List.finRange n).foldlM (fun row j => do
        let c ← dotAccum rnd (List.finRange r) (A i) (fun k => B k j) (row j)
        pure (Function.update row j c)) (C i)
      pure (C.updateRow i row)) C := by
  unfold algorithm_1_1_5
  congr 1
  funext C i
  rw [← foldlM_updateRow_row i
    (fun j c => dotAccum rnd (List.finRange r) (A i) (fun k => B k j) c)]
  congr 1
  funext C j
  have := Matrix.foldlM_updateRow_update i j
    (fun k c => do let p ← rnd (A i k * B k j); rnd (c + p)) (List.finRange r) C
  simp only [bind_assoc] at this
  exact this

/-- Algorithm 1.1.6 as two loops writing one entry per step. -/
private theorem algorithm_1_1_6_eq {m r n : ℕ} (A : Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin r) (Fin n) ℝ) (C : Matrix (Fin m) (Fin n) ℝ) :
    algorithm_1_1_6 rnd A B C = (List.finRange m).foldlM (fun C i => do
      let row ← (List.finRange n).foldlM (fun row j => do
        let c ← (do let s ← algorithm_1_1_1 rnd (A i) (fun k => B k j); rnd (row j + s))
        pure (Function.update row j c)) (C i)
      pure (C.updateRow i row)) C := by
  unfold algorithm_1_1_6
  congr 1
  funext C i
  have := foldlM_updateRow_row i
    (fun j c => do let s ← algorithm_1_1_1 rnd (A i) (fun k => B k j); rnd (c + s))
    (List.finRange n) C
  simpa only [bind_assoc] using this

/-- Algorithm 1.1.7 as a loop writing one column per step around a loop of saxpys. -/
private theorem algorithm_1_1_7_eq {m r n : ℕ} (A : Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin r) (Fin n) ℝ) (C : Matrix (Fin m) (Fin n) ℝ) :
    algorithm_1_1_7 rnd A B C = (List.finRange n).foldlM (fun C j => do
      let c ← (List.finRange r).foldlM (fun c k => algorithm_1_1_2 rnd (B k j) (fun i => A i k) c)
        (fun i => C i j)
      pure (C.updateCol j c)) C := by
  unfold algorithm_1_1_7
  congr 1
  funext C j
  exact Matrix.foldlM_updateCol j (fun k c => algorithm_1_1_2 rnd (B k j) (fun i => A i k) c)
    (List.finRange r) C

/-- Each outer-product update of Algorithm 1.1.8 as two loops writing one entry per step. -/
private theorem algorithm_1_1_8_eq {m r n : ℕ} (A : Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin r) (Fin n) ℝ) (C : Matrix (Fin m) (Fin n) ℝ) :
    algorithm_1_1_8 rnd A B C = (List.finRange r).foldlM (fun C k =>
      (List.finRange m).foldlM (fun C i => do
        let row ← (List.finRange n).foldlM (fun row j => do
          let c ← (do let p ← rnd (A i k * B k j); rnd (row j + p))
          pure (Function.update row j c)) (C i)
        pure (C.updateRow i row)) C) C := by
  unfold algorithm_1_1_8
  congr 1
  funext C k
  congr 1
  funext C i
  have := foldlM_updateRow_row i (fun j c => do let p ← rnd (A i k * B k j); rnd (c + p))
    (List.finRange n) C
  simpa only [bind_assoc] using this

end NormalForms

/-! ### The exact runs are runs of the exact model -/

section Exact

/-- In the exact model the run set of the dot product is the `Id` run. -/
private theorem algorithm_1_1_1_mem_exact {n : ℕ} (x y : Fin n → ℝ) :
    Id.run (algorithm_1_1_1 pure x y) ∈
      (algorithm_1_1_1 (RoundingModel.exact ℝ).round x y).run := by
  rw [RoundingModel.round_exact]
  simp only [algorithm_1_1_1, pure_bind, List.foldlM_pure, SetM.mem_run_pure]
  rfl

private theorem algorithm_1_1_2_mem_exact {n : ℕ} (a : ℝ) (x y : Fin n → ℝ) :
    Id.run (algorithm_1_1_2 pure a x y) ∈
      (algorithm_1_1_2 (RoundingModel.exact ℝ).round a x y).run := by
  rw [RoundingModel.round_exact]
  simp only [algorithm_1_1_2, pure_bind, List.foldlM_pure, SetM.mem_run_pure]
  rfl

private theorem algorithm_1_1_3_mem_exact {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ) (y : Fin m → ℝ) :
    Id.run (algorithm_1_1_3 pure A x y) ∈
      (algorithm_1_1_3 (RoundingModel.exact ℝ).round A x y).run := by
  rw [RoundingModel.round_exact]
  simp only [algorithm_1_1_3, pure_bind, List.foldlM_pure, SetM.mem_run_pure]
  rfl

private theorem algorithm_1_1_4_mem_exact {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ) (y : Fin m → ℝ) :
    Id.run (algorithm_1_1_4 pure A x y) ∈
      (algorithm_1_1_4 (RoundingModel.exact ℝ).round A x y).run := by
  rw [RoundingModel.round_exact]
  simp only [algorithm_1_1_4, pure_bind, List.foldlM_pure, SetM.mem_run_pure]
  rfl

variable {m r n : ℕ} (A : Matrix (Fin m) (Fin r) ℝ) (B : Matrix (Fin r) (Fin n) ℝ)
  (C : Matrix (Fin m) (Fin n) ℝ)

private theorem algorithm_1_1_5_mem_exact :
    Id.run (algorithm_1_1_5 pure A B C) ∈
      (algorithm_1_1_5 (RoundingModel.exact ℝ).round A B C).run := by
  rw [RoundingModel.round_exact]
  simp only [algorithm_1_1_5, pure_bind, List.foldlM_pure, SetM.mem_run_pure]
  rfl

private theorem algorithm_1_1_6_mem_exact :
    Id.run (algorithm_1_1_6 pure A B C) ∈
      (algorithm_1_1_6 (RoundingModel.exact ℝ).round A B C).run := by
  rw [RoundingModel.round_exact]
  simp only [algorithm_1_1_6, algorithm_1_1_1, pure_bind, List.foldlM_pure, SetM.mem_run_pure]
  rfl

private theorem algorithm_1_1_7_mem_exact :
    Id.run (algorithm_1_1_7 pure A B C) ∈
      (algorithm_1_1_7 (RoundingModel.exact ℝ).round A B C).run := by
  rw [RoundingModel.round_exact]
  simp only [algorithm_1_1_7, algorithm_1_1_2, pure_bind, List.foldlM_pure, SetM.mem_run_pure]
  rfl

private theorem algorithm_1_1_8_mem_exact :
    Id.run (algorithm_1_1_8 pure A B C) ∈
      (algorithm_1_1_8 (RoundingModel.exact ℝ).round A B C).run := by
  rw [RoundingModel.round_exact]
  simp only [algorithm_1_1_8, pure_bind, List.foldlM_pure, SetM.mem_run_pure]
  rfl

end Exact

/-! ### The run sets -/

section Runs

variable (fp : RoundingModel ℝ)

/-- **The run set of the saxpy**, entrywise: `ŷ` is a run of Algorithm 1.1.2 iff every entry is an
admissible rounding `fl(y(i) + fl(a x(i)))` — the relation of the book's (2.7.17). -/
theorem algorithm_1_1_2_mem_run {n : ℕ} (a : ℝ) (x y ŷ : Fin n → ℝ) :
    ŷ ∈ (algorithm_1_1_2 fp.round a x y).run ↔
      ∀ i, ∃ p, fp.Rounds (a * x i) p ∧ fp.Rounds (y i + p) (ŷ i) := by
  have h := mem_run_foldlM_finRange_update
    (fun i b => do let p ← fp.round (a * x i); fp.round (b + p)) y ŷ
  simp only [bind_assoc] at h
  exact h.trans (by simp)

/-- **The run set of the row gaxpy**, entry by entry an accumulation onto `y(i)`:
`ŷ(i) = fl(⋯fl(y(i) + fl(a_{i1} x_1))⋯ + fl(a_{in} x_n))`. -/
theorem algorithm_1_1_3_mem_run {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ)
    (y ŷ : Fin m → ℝ) :
    ŷ ∈ (algorithm_1_1_3 fp.round A x y).run ↔
      ∀ i, ŷ i ∈ (dotAccum fp.round (List.finRange n) (A i) x (y i)).run := by
  rw [algorithm_1_1_3_eq]
  exact mem_run_foldlM_finRange_update (fun i b => dotAccum fp.round (List.finRange n) (A i) x b)
    y ŷ

/-- **The column gaxpy rounds exactly as the row gaxpy does**: the run set of Algorithm 1.1.4 is
that of Algorithm 1.1.3 (the right side of `algorithm_1_1_3_mem_run`). Loop interchange in the
relational model: the inner loop writes one entry per step, so each outer step acts on every
entry independently. -/
theorem algorithm_1_1_4_mem_run {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ)
    (y ŷ : Fin m → ℝ) :
    ŷ ∈ (algorithm_1_1_4 fp.round A x y).run ↔
      ∀ i, ŷ i ∈ (dotAccum fp.round (List.finRange n) (A i) x (y i)).run := by
  refine SetM.mem_run_foldlM_of_pi _
    (fun j i b => do let p ← fp.round (A i j * x j); fp.round (b + p)) (fun y j y' => ?_) _ y ŷ
  have h := mem_run_foldlM_finRange_update
    (fun i b => do let p ← fp.round (A i j * x j); fp.round (b + p)) y y'
  simp only [bind_assoc] at h
  exact h

/-- **The run set of the `ijk` product**, entry by entry an accumulation onto `C(i,j)`:
`Ĉ(i,j) = fl(⋯fl(C(i,j) + fl(a_{i1} b_{1j}))⋯ + fl(a_{ir} b_{rj}))`. -/
theorem algorithm_1_1_5_mem_run {m r n : ℕ} (A : Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin r) (Fin n) ℝ) (C Ĉ : Matrix (Fin m) (Fin n) ℝ) :
    Ĉ ∈ (algorithm_1_1_5 fp.round A B C).run ↔
      ∀ i j, Ĉ i j ∈ (dotAccum fp.round (List.finRange r) (A i) (fun k => B k j) (C i j)).run := by
  rw [algorithm_1_1_5_eq]
  refine (mem_run_foldlM_finRange_updateRow (fun i row => (List.finRange n).foldlM (fun row j => do
      let c ← dotAccum fp.round (List.finRange r) (A i) (fun k => B k j) (row j)
      pure (Function.update row j c)) row) C Ĉ).trans (forall_congr' fun i => ?_)
  exact mem_run_foldlM_finRange_update
    (fun j b => dotAccum fp.round (List.finRange r) (A i) (fun k => B k j) b) (C i) (Ĉ i)

/-- **The run set of the dot-product matrix multiplication**: every entry is an admissible
`fl(C(i,j) + s)` with `s` a run of Algorithm 1.1.1 on `A(i,:)` and `B(:,j)`. -/
theorem algorithm_1_1_6_mem_run {m r n : ℕ} (A : Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin r) (Fin n) ℝ) (C Ĉ : Matrix (Fin m) (Fin n) ℝ) :
    Ĉ ∈ (algorithm_1_1_6 fp.round A B C).run ↔
      ∀ i j, ∃ s ∈ (algorithm_1_1_1 fp.round (A i) (fun k => B k j)).run,
        fp.Rounds (C i j + s) (Ĉ i j) := by
  rw [algorithm_1_1_6_eq]
  refine (mem_run_foldlM_finRange_updateRow (fun i row => (List.finRange n).foldlM (fun row j => do
      let c ← (do let s ← algorithm_1_1_1 fp.round (A i) (fun k => B k j); fp.round (row j + s))
      pure (Function.update row j c)) row) C Ĉ).trans (forall_congr' fun i => ?_)
  exact (mem_run_foldlM_finRange_update (fun j b => do
    let s ← algorithm_1_1_1 fp.round (A i) (fun k => B k j); fp.round (b + s)) (C i) (Ĉ i)).trans
    (by simp)

/-- **The saxpy product rounds entry by entry as the `ijk` product does**: the right side of
`algorithm_1_1_5_mem_run` characterizes the run set of Algorithm 1.1.7. The `j` loop writes
column `j` only; each `k` step is a saxpy on that column, which acts on every entry independently,
so the `k` loop is, entry by entry, the `k` accumulation. -/
theorem algorithm_1_1_7_mem_run {m r n : ℕ} (A : Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin r) (Fin n) ℝ) (C Ĉ : Matrix (Fin m) (Fin n) ℝ) :
    Ĉ ∈ (algorithm_1_1_7 fp.round A B C).run ↔
      ∀ i j, Ĉ i j ∈ (dotAccum fp.round (List.finRange r) (A i) (fun k => B k j) (C i j)).run := by
  rw [algorithm_1_1_7_eq, mem_run_foldlM_finRange_updateCol (fun j c =>
    (List.finRange r).foldlM (fun c k => algorithm_1_1_2 fp.round (B k j) (fun i => A i k) c) c)]
  refine (forall_congr' fun j => ?_).trans forall_comm
  refine SetM.mem_run_foldlM_of_pi _
    (fun k i b => do let p ← fp.round (A i k * B k j); fp.round (b + p)) (fun c k c' => ?_) _ _ _
  rw [algorithm_1_1_2_mem_run]
  simp [mul_comm]

/-- **The outer-product form rounds entry by entry as the `ijk` product does**: the right side of
`algorithm_1_1_5_mem_run` characterizes the run set of Algorithm 1.1.8. Each rank-one update acts on
every entry independently, so the `k` loop is, entry by entry, the `k` accumulation; with `r = 1`
this is the book's (2.7.18). -/
theorem algorithm_1_1_8_mem_run {m r n : ℕ} (A : Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin r) (Fin n) ℝ) (C Ĉ : Matrix (Fin m) (Fin n) ℝ) :
    Ĉ ∈ (algorithm_1_1_8 fp.round A B C).run ↔
      ∀ i j, Ĉ i j ∈ (dotAccum fp.round (List.finRange r) (A i) (fun k => B k j) (C i j)).run := by
  rw [algorithm_1_1_8_eq]
  -- the rank-one updates act on the rows independently …
  refine (SetM.mem_run_foldlM_of_pi _ (fun k i row => (List.finRange n).foldlM (fun row j => do
      let c ← (do let p ← fp.round (A i k * B k j); fp.round (row j + p))
      pure (Function.update row j c)) row) (fun C k C' => ?_) _ C Ĉ).trans
    (forall_congr' fun i => ?_)
  · exact mem_run_foldlM_finRange_updateRow (fun i row => (List.finRange n).foldlM (fun row j => do
      let c ← (do let p ← fp.round (A i k * B k j); fp.round (row j + p))
      pure (Function.update row j c)) row) C C'
  -- … and on the entries of a row independently
  · refine SetM.mem_run_foldlM_of_pi _
      (fun k j b => do let p ← fp.round (A i k * B k j); fp.round (b + p)) (fun row k row' => ?_)
      _ _ _
    exact mem_run_foldlM_finRange_update
      (fun j b => do let p ← fp.round (A i k * B k j); fp.round (b + p)) row row'

end Runs

/-! ### Exact specifications, read off the run sets at the exact model -/

/-- **Algorithm 1.1.1 computes `c = xᵀy`.** -/
theorem algorithm_1_1_1_spec {n : ℕ} (x y : Fin n → ℝ) :
    Id.run (algorithm_1_1_1 pure x y) = x ⬝ᵥ y := by
  have h := algorithm_1_1_1_mem_exact x y
  rw [algorithm_1_1_1_eq_dotAccum (RoundingModel.exact ℝ).round, mem_run_dotAccum_exact_iff] at h
  rw [h, zero_add, ← Fin.sum_univ_def]
  rfl

/-- **Algorithm 1.1.2 overwrites `y` with `y + ax`.** -/
theorem algorithm_1_1_2_spec {n : ℕ} (a : ℝ) (x y : Fin n → ℝ) :
    Id.run (algorithm_1_1_2 pure a x y) = y + a • x := by
  funext i
  obtain ⟨p, hp, hs⟩ := (algorithm_1_1_2_mem_run _ a x y _).1 (algorithm_1_1_2_mem_exact a x y) i
  rw [RoundingModel.exact_rounds_iff] at hp hs
  rw [hs, hp]
  rfl

/-- **Algorithm 1.1.3 overwrites `y` with `Ax + y`.** -/
theorem algorithm_1_1_3_spec {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ)
    (y : Fin m → ℝ) : Id.run (algorithm_1_1_3 pure A x y) = y + A *ᵥ x := by
  funext i
  have h := (algorithm_1_1_3_mem_run _ A x y _).1 (algorithm_1_1_3_mem_exact A x y) i
  rw [mem_run_dotAccum_exact_iff] at h
  rw [h, Pi.add_apply, ← Fin.sum_univ_def]
  rfl

/-- **Algorithm 1.1.4 overwrites `y` with `Ax + y`**, as Algorithm 1.1.3 does. -/
theorem algorithm_1_1_4_spec {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ)
    (y : Fin m → ℝ) : Id.run (algorithm_1_1_4 pure A x y) = y + A *ᵥ x := by
  funext i
  have h := (algorithm_1_1_4_mem_run _ A x y _).1 (algorithm_1_1_4_mem_exact A x y) i
  rw [mem_run_dotAccum_exact_iff] at h
  rw [h, Pi.add_apply, ← Fin.sum_univ_def]
  rfl

/-- An entry that is the exact accumulation of a row of `A` against a column of `B` onto `C(i,j)`
is the entry of `C + AB`. -/
private theorem eq_add_mul_of_forall_mem_run_exact {m r n : ℕ} {A : Matrix (Fin m) (Fin r) ℝ}
    {B : Matrix (Fin r) (Fin n) ℝ} {C Ĉ : Matrix (Fin m) (Fin n) ℝ}
    (h : ∀ i j, Ĉ i j ∈
      (dotAccum (RoundingModel.exact ℝ).round (List.finRange r) (A i) (fun k => B k j)
        (C i j)).run) :
    Ĉ = C + A * B := by
  ext i j
  rw [mem_run_dotAccum_exact_iff.1 (h i j), add_apply, ← Fin.sum_univ_def]
  rfl

/-- **Algorithm 1.1.5 overwrites `C` with `C + AB`.** -/
theorem algorithm_1_1_5_spec {m r n : ℕ} (A : Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin r) (Fin n) ℝ) (C : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (algorithm_1_1_5 pure A B C) = C + A * B :=
  eq_add_mul_of_forall_mem_run_exact
    ((algorithm_1_1_5_mem_run _ A B C _).1 (algorithm_1_1_5_mem_exact A B C))

/-- **Algorithm 1.1.6 overwrites `C` with `C + AB`.** -/
theorem algorithm_1_1_6_spec {m r n : ℕ} (A : Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin r) (Fin n) ℝ) (C : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (algorithm_1_1_6 pure A B C) = C + A * B := by
  ext i j
  obtain ⟨s, hs, hc⟩ := (algorithm_1_1_6_mem_run _ A B C _).1 (algorithm_1_1_6_mem_exact A B C) i j
  rw [RoundingModel.exact_rounds_iff] at hc
  rw [algorithm_1_1_1_eq_dotAccum, mem_run_dotAccum_exact_iff, zero_add] at hs
  rw [hc, hs, add_apply, ← Fin.sum_univ_def]
  rfl

/-- **Algorithm 1.1.7 overwrites `C` with `C + AB`.** -/
theorem algorithm_1_1_7_spec {m r n : ℕ} (A : Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin r) (Fin n) ℝ) (C : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (algorithm_1_1_7 pure A B C) = C + A * B :=
  eq_add_mul_of_forall_mem_run_exact
    ((algorithm_1_1_7_mem_run _ A B C _).1 (algorithm_1_1_7_mem_exact A B C))

/-- **Algorithm 1.1.8 overwrites `C` with `C + AB`**; (1.1.4) (`equation_1_1_4`) is the book's
reading of the same identity. -/
theorem algorithm_1_1_8_spec {m r n : ℕ} (A : Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin r) (Fin n) ℝ) (C : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (algorithm_1_1_8 pure A B C) = C + A * B :=
  eq_add_mul_of_forall_mem_run_exact
    ((algorithm_1_1_8_mem_run _ A B C _).1 (algorithm_1_1_8_mem_exact A B C))

/-! ### Bridges to the backbone's relational inner and matrix products -/

section Bridges

variable {fp : RoundingModel ℝ}

/-- **Every run of Algorithm 1.1.1 is a recursive inner product** in the relational model when
rounding fixes its outputs: the first addition `0 + fl(x₁y₁)` is then exact — the book's (2.7.9)
`s₁ = x₁y₁(1 + δ₁)`. Without the hypothesis, `FloatingPoint.abs_sub_le_of_mem_run_dotAccum`
bounds a run by `γ_{n+1} |x|ᵀ|y|`. -/
theorem algorithm_1_1_1_rounds (hfp : fp.IsIdempotent) {n : ℕ} (x y : Fin n → ℝ) :
    ∀ s ∈ (algorithm_1_1_1 fp.round x y).run, RoundsDot fp x y s := fun _ hs =>
  roundsDot_of_mem_run_dotAccum hfp (List.nodup_finRange n) List.mem_finRange hs

/-- For a total model the run set of Algorithm 1.1.1 is nonempty, so the statements about every
run are not vacuous. -/
theorem algorithm_1_1_1_run_nonempty (hfp : fp.IsTotal) {n : ℕ} (x y : Fin n → ℝ) :
    (algorithm_1_1_1 fp.round x y).run.Nonempty :=
  dotAccum_run_nonempty hfp (List.finRange n) x y 0

/-- An accumulation from `0` over a full duplicate-free order is a `RoundsDot`, entrywise. -/
private theorem roundsMul_of_forall_mem_run (hfp : fp.IsIdempotent) {m r n : ℕ}
    {A : Matrix (Fin m) (Fin r) ℝ} {B : Matrix (Fin r) (Fin n) ℝ} {Ĉ : Matrix (Fin m) (Fin n) ℝ}
    (h : ∀ i j, Ĉ i j ∈
      (dotAccum fp.round (List.finRange r) (A i) (fun k => B k j) ((0 : Matrix _ _ ℝ) i j)).run) :
    RoundsMul fp A B Ĉ := fun i j =>
  roundsDot_of_mem_run_dotAccum hfp (List.nodup_finRange r) List.mem_finRange (h i j)

/-- **Every run of Algorithm 1.1.5 with `C = 0` is a relational matrix product**, hence
`|Ĉ − AB| ≤ γ_r |A||B|` (`FloatingPoint.abs_sub_entrywiseLE_of_roundsMul`, the book's (2.7.19)). -/
theorem algorithm_1_1_5_rounds (hfp : fp.IsIdempotent) {m r n : ℕ} (A : Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin r) (Fin n) ℝ) :
    ∀ Ĉ ∈ (algorithm_1_1_5 fp.round A B 0).run, RoundsMul fp A B Ĉ := fun _ h =>
  roundsMul_of_forall_mem_run hfp ((algorithm_1_1_5_mem_run _ A B 0 _).1 h)

/-- **Every run of Algorithm 1.1.6 with `C = 0` is a relational matrix product**: each entry is
`fl(0 + s)` with `s` a run of Algorithm 1.1.1, `= s` by idempotence, and `s` is a `RoundsDot` by
`algorithm_1_1_1_rounds`. -/
theorem algorithm_1_1_6_rounds (hfp : fp.IsIdempotent) {m r n : ℕ} (A : Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin r) (Fin n) ℝ) :
    ∀ Ĉ ∈ (algorithm_1_1_6 fp.round A B 0).run, RoundsMul fp A B Ĉ := by
  intro Ĉ h i j
  obtain ⟨s, hs, hc⟩ := (algorithm_1_1_6_mem_run _ A B 0 _).1 h i j
  rw [zero_apply, zero_add] at hc
  have hsc : Ĉ i j = s := by
    rcases FloatingPoint.eq_or_rounds_of_mem_run_dotAccum (o := List.finRange r) (x := A i)
        (y := fun k => B k j) (c := 0) hs with
      rfl | ⟨z, hz⟩
    · exact hc.eq_zero_of_zero
    · exact hfp hz hc
  rw [hsc]
  exact algorithm_1_1_1_rounds hfp _ _ s hs

/-- **Every run of Algorithm 1.1.7 with `C = 0` is a relational matrix product** (the book's
(2.7.19) "for a gaxpy based procedure"). -/
theorem algorithm_1_1_7_rounds (hfp : fp.IsIdempotent) {m r n : ℕ} (A : Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin r) (Fin n) ℝ) :
    ∀ Ĉ ∈ (algorithm_1_1_7 fp.round A B 0).run, RoundsMul fp A B Ĉ := fun _ h =>
  roundsMul_of_forall_mem_run hfp ((algorithm_1_1_7_mem_run _ A B 0 _).1 h)

/-- **Every run of Algorithm 1.1.8 with `C = 0` is a relational matrix product** (the book's
(2.7.19) "or outer product based"). -/
theorem algorithm_1_1_8_rounds (hfp : fp.IsIdempotent) {m r n : ℕ} (A : Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin r) (Fin n) ℝ) :
    ∀ Ĉ ∈ (algorithm_1_1_8 fp.round A B 0).run, RoundsMul fp A B Ĉ := fun _ h =>
  roundsMul_of_forall_mem_run hfp ((algorithm_1_1_8_mem_run _ A B 0 _).1 h)

end Bridges

/-! ### (1.1.4): matrix multiplication is a sum of outer products -/

/-- **(1.1.4)**: `AB = ∑_{k=1}^r a_k b_kᵀ`, where `a_k` is the `k`-th column of `A` and `b_kᵀ` the
`k`-th row of `B` (the partitionings (1.1.3)). -/
theorem equation_1_1_4 {m r n : ℕ} (A : Matrix (Fin m) (Fin r) ℝ) (B : Matrix (Fin r) (Fin n) ℝ) :
    A * B = ∑ k, vecMulVec (fun i => A i k) (B k) := by
  ext i j
  simp [mul_apply, vecMulVec_apply, Matrix.sum_apply]

end GolubVanLoan.Chapter01

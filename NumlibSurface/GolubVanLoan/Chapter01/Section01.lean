/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.RowCol
import Numlib.FloatingPoint.Program

/-!
# Golub and Van Loan, Section 1.1: Basic algorithms and notation

This module formalizes §1.1 of [golub2013matrix]: the dot product and the saxpy (Algorithms
1.1.1–1.1.2), the row-oriented and column-oriented gaxpy (Algorithms 1.1.3–1.1.4), the four
formulations of the update $C = C + AB$ of a matrix product (the `ijk`, dot product, saxpy and outer
product forms, Algorithms 1.1.5–1.1.8), and the outer product expansion (1.1.4)
$AB = \sum_k a_k b_k^T$. For each algorithm it proves that in exact arithmetic the algorithm
computes what the source says. It also describes, entry by entry, the set of all results that the
algorithm can produce in a rounding model: each entry of a gaxpy or of a matrix product is an
accumulation of the rounded products onto the initial entry, in whatever loop order the algorithm
uses. This is the precise content of the remark in §2.7 of the source, at (2.7.19), that the same
error result applies if a gaxpy or outer product based procedure is used.

The programs and their run sets use `Numlib.FloatingPoint.Program`. The rounding bridges connect the
dot product and the matrix products to the relational inner product `FloatingPoint.RoundsDot` and
matrix product `FloatingPoint.RoundsMul` of `Numlib.FloatingPoint.InnerProduct`, from which Chapter
2 reads the bounds $|\mathrm{fl}(x^T y) - x^T y| \le \gamma_n |x|^T |y|$ and
$|\mathrm{fl}(AB) - AB| \le \gamma_r |A| |B|$.

## Main definitions

* Algorithm 1.1.1, `GolubVanLoan.Chapter01.algorithm_1_1_1`: the dot product $c = x^T y$.
* Algorithm 1.1.2, `GolubVanLoan.Chapter01.algorithm_1_1_2`: the saxpy $y \leftarrow y + ax$.
* Algorithm 1.1.3, `GolubVanLoan.Chapter01.algorithm_1_1_3`: the row-oriented gaxpy
  $y \leftarrow Ax + y$.
* Algorithm 1.1.4, `GolubVanLoan.Chapter01.algorithm_1_1_4`: the column-oriented gaxpy
  $y \leftarrow Ax + y$.
* Algorithm 1.1.5, `GolubVanLoan.Chapter01.algorithm_1_1_5`: the `ijk` matrix multiplication
  $C \leftarrow C + AB$.
* Algorithm 1.1.6, `GolubVanLoan.Chapter01.algorithm_1_1_6`: the dot product matrix multiplication.
* Algorithm 1.1.7, `GolubVanLoan.Chapter01.algorithm_1_1_7`: the saxpy matrix multiplication.
* Algorithm 1.1.8, `GolubVanLoan.Chapter01.algorithm_1_1_8`: the outer product matrix
  multiplication.

## Main results

* Algorithm 1.1.1, `GolubVanLoan.Chapter01.algorithm_1_1_1_eq_dotAccum`: the dot product is the
  backbone accumulation `FloatingPoint.dotAccum` from $c = 0$.
* Algorithms 1.1.1–1.1.8, `GolubVanLoan.Chapter01.algorithm_1_1_1_spec` to
  `GolubVanLoan.Chapter01.algorithm_1_1_8_spec`: in exact arithmetic the algorithms compute $x^T y$,
  $y + ax$, $y + Ax$ and $C + AB$.
* Algorithms 1.1.2–1.1.8, `GolubVanLoan.Chapter01.algorithm_1_1_2_mem_run` to
  `GolubVanLoan.Chapter01.algorithm_1_1_8_mem_run`: the results in a rounding model, entry by entry;
  every gaxpy and every matrix product has, entry by entry, the run set of an accumulation of
  rounded products onto the initial entry.
* Algorithm 1.1.1, `GolubVanLoan.Chapter01.algorithm_1_1_1_rounds`: over an idempotent rounding
  model, every result of the dot product is a recursive inner product in the sense of
  `FloatingPoint.RoundsDot`.
* Algorithm 1.1.1, `GolubVanLoan.Chapter01.algorithm_1_1_1_run_nonempty`: over a total rounding
  model, the dot product has a result.
* Algorithms 1.1.5–1.1.8, `GolubVanLoan.Chapter01.algorithm_1_1_5_rounds` to
  `GolubVanLoan.Chapter01.algorithm_1_1_8_rounds`: over an idempotent rounding model, every result
  started from $C = 0$ is a computed matrix product in the sense of `FloatingPoint.RoundsMul`.
* Equation (1.1.4), `GolubVanLoan.Chapter01.equation_1_1_4`: $AB = \sum_{k=1}^r a_k b_k^T$, with
  $a_k$ the columns of $A$ and $b_k^T$ the rows of $B$.

## Conventions

* Indices are 0-based. The source's $x(i)$ is `x (i - 1)`, and its $A(i, j)$ is `A (i - 1) (j - 1)`.
* The arguments come in BLAS order: `a x y` for the saxpy, `A x y` for the gaxpys, and `A B C` for
  the matrix products.

## Implementation notes

* Every algorithm is written once, as a monadic program in the loop order of the source. It is
  generic in a monad `M` and a rounding hook `rnd : ℝ → M ℝ`, and every product and every sum passes
  through `rnd`, as in the algorithm conventions of `NumlibSurface.GolubVanLoan` and
  `Numlib.FloatingPoint.Program`. With `M := Id` and `rnd := pure` the program computes in exact
  arithmetic. With `M := SetM` and `rnd := fp.round` its run set contains every result that
  floating-point evaluation in the rounding model `fp` can produce.
* The state is overwritten as the source overwrites it: vectors by `Function.update`, and matrices
  by `Matrix.updateRow C i (Function.update (C i) j c)` or `Matrix.updateCol`. The colon-notation
  algorithms call the scalar ones. The update $C(i,j) + A(i,:) \cdot B(:,j)$ of Algorithm 1.1.6 is
  the loop of Algorithm 1.1.1 accumulating onto $C(i,j)$ (`FloatingPoint.dotAccum`), and the update
  $C(:,j) = C(:,j) + A(:,k) B(k,j)$ of Algorithm 1.1.7 is `GolubVanLoan.Chapter01.algorithm_1_1_2`.
* Each algorithm has up to three kinds of theorem. A theorem `…_mem_run` describes the run set in
  the relational model entry by entry. A theorem `…_rounds` (Algorithms 1.1.1 and 1.1.5–1.1.8) is
  the bridge to `FloatingPoint.RoundsDot` or `FloatingPoint.RoundsMul`. A theorem `…_spec` is the
  exact semantics. It is read off the run set at the exact model
  `FloatingPoint.RoundingModel.exact`: the exact run is one of the runs there, and there every
  accumulation is the exact running sum (`FloatingPoint.mem_run_dotAccum_exact_iff`).
* The loops of the source start the accumulation at $c = 0$ and round $0 + \mathrm{fl}(x_1 y_1)$,
  but `FloatingPoint.RoundsDot` starts from the unrounded first term. The bridges therefore assume
  `FloatingPoint.RoundingModel.IsIdempotent`, under which this first addition is exact.
* The run sets rest on three facts about loops. First, a loop whose every step reads and rewrites
  one component of the state only (one entry, one row or one column) is one update of that component
  by the loop run on that component alone (`List.foldlM_lens` and its instances
  `List.foldlM_update_self`, `Matrix.foldlM_updateRow`, `Matrix.foldlM_updateCol` and
  `Matrix.foldlM_updateRow_update`, in any lawful monad). Second, a loop over `List.finRange n`
  whose step $i$ rewrites entry $i$ only has as run set the product of the run sets of the entries
  (`SetM.mem_run_foldlM_update_of_nodup`). Third, a loop whose every step acts on every entry
  independently is, entry by entry, the loop run on that entry (`SetM.mem_run_foldlM_of_pi`); this
  is loop interchange in the relational model.

## Deviations from the source

* **Algorithm 1.1.6** (reading). The source presents the dot-product display as a rewrite of
  Algorithm 1.1.5. The program retains the rounding order of 1.1.5 by accumulating onto $C(i,j)$.
  See `GolubVanLoan.Chapter01.algorithm_1_1_6`.

## Not formalized

* **The notation of §1.1.1–1.1.4 and §1.1.7–1.1.8.** The displays (1.1.1)–(1.1.3) are partition
  notation.
* **The unnumbered `jki` and `kij` loops.** Algorithms 1.1.7 and 1.1.8 are their colon forms.
* **Table 1.1.1.**
* **The flop counts, the big-Oh notation and the BLAS levels of §1.1.15–1.1.17, with Table 1.1.2.**
  Operation counts are out of scope for the library.
* **The complex notation of §1.1.19.** Mathlib supplies the conjugate transpose `ᴴ`.
* **The numerical examples.** Numerical examples are out of scope for the library.
-/

open FloatingPoint Matrix

namespace GolubVanLoan.Chapter01

/-! ### Run sets of loops writing one entry per step -/

/-- A loop over `List.finRange n` whose step $i$ rewrites entry $i$ from its current value has as
run set the product of the run sets of the single entries. -/
private theorem mem_run_foldlM_finRange_update {n : ℕ} {β : Type} (g : Fin n → β → SetM β)
    (y₀ y : Fin n → β) :
    y ∈ ((List.finRange n).foldlM (fun (y : Fin n → β) a => do
        let b ← g a (y a); pure (Function.update y a b)) y₀).run ↔
      ∀ i, y i ∈ (g i (y₀ i)).run := by
  have h := SetM.mem_run_foldlM_update_of_nodup (fun a b (_ : Fin n → β) => g a b)
    (List.finRange n) (List.nodup_finRange n) (fun _ _ _ _ _ _ => rfl) y₀ y
  exact h.trans (by simp [List.mem_finRange])

/-- The row form of the previous lemma: a loop whose step $i$ rewrites row $i$ from its current
value. -/
private theorem mem_run_foldlM_finRange_updateRow {m n : ℕ}
    (g : Fin m → (Fin n → ℝ) → SetM (Fin n → ℝ)) (C₀ C : Matrix (Fin m) (Fin n) ℝ) :
    C ∈ ((List.finRange m).foldlM (fun (C : Matrix (Fin m) (Fin n) ℝ) i => do
        let r ← g i (C i); pure (C.updateRow i r)) C₀).run ↔
      ∀ i, C i ∈ (g i (C₀ i)).run :=
  mem_run_foldlM_finRange_update (β := Fin n → ℝ) g C₀ C

/-- The column form of the previous lemmas: a loop whose step $j$ rewrites column $j$ from its
current value; the proof is by transposition. -/
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

/-! ### Algorithms 1.1.1–1.1.8 -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 1.1.1** of [golub2013matrix] (dot product). "If $x, y \in \mathbb{R}^n$, then this
algorithm computes their dot product $c = x^T y$":
```
c = 0
for i = 1:n
    c = c + x(i) y(i)
end
```
The program starts from $c = 0$ and computes $c \leftarrow \mathrm{fl}(c + \mathrm{fl}(x_i
y_i))$ for $i = 1, \dots, n$, so the product and the sum are each rounded.

The program is generic in the monad `M` and the rounding hook `rnd`. Indices are 0-based. -/
def algorithm_1_1_1 {n : ℕ} (x y : Fin n → ℝ) : M ℝ :=
  (List.finRange n).foldlM (fun c k => do rnd (c + (← rnd (x k * y k)))) 0

/-- **Algorithm 1.1.1** of [golub2013matrix], as an accumulation. For $x, y \in \mathbb{R}^n$, in
every monad and for every rounding hook, Algorithm 1.1.1 is the accumulation
`FloatingPoint.dotAccum` of the rounded products $\mathrm{fl}(x_i y_i)$ onto $c = 0$ in the
order $i = 1, \dots, n$.

Chapters 2 and 3 reach `FloatingPoint.RoundsDot` through this identity. -/
theorem algorithm_1_1_1_eq_dotAccum {n : ℕ} (x y : Fin n → ℝ) :
    algorithm_1_1_1 rnd x y = dotAccum rnd (List.finRange n) x y 0 :=
  rfl

/-- **Algorithm 1.1.2** of [golub2013matrix] (saxpy). "If $x, y \in \mathbb{R}^n$ and
$a \in \mathbb{R}$, then this algorithm overwrites $y$ with $y + ax$":
```
for i = 1:n
    y(i) = y(i) + a x(i)
end
```
The program computes $y_i \leftarrow \mathrm{fl}(y_i + \mathrm{fl}(a x_i))$ for
$i = 1, \dots, n$. -/
def algorithm_1_1_2 {n : ℕ} (a : ℝ) (x y : Fin n → ℝ) : M (Fin n → ℝ) :=
  (List.finRange n).foldlM (fun y i => do
    let p ← rnd (a * x i)
    let s ← rnd (y i + p)
    pure (Function.update y i s)) y

/-- **Algorithm 1.1.3** of [golub2013matrix] (row-oriented gaxpy). "If
$A \in \mathbb{R}^{m \times n}$, $x \in \mathbb{R}^n$, and $y \in \mathbb{R}^m$, then this
algorithm overwrites $y$ with $Ax + y$":
```
for i = 1:m
    for j = 1:n
        y(i) = y(i) + A(i,j) x(j)
    end
end
```
The program computes $y_i \leftarrow \mathrm{fl}(y_i + \mathrm{fl}(a_{ij} x_j))$ in this loop
order. -/
def algorithm_1_1_3 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) (y : Fin m → ℝ) :
    M (Fin m → ℝ) :=
  (List.finRange m).foldlM (fun y i =>
    (List.finRange n).foldlM (fun y j => do
      let p ← rnd (A i j * x j)
      let s ← rnd (y i + p)
      pure (Function.update y i s)) y) y

/-- **Algorithm 1.1.4** of [golub2013matrix] (column-oriented gaxpy). Let
$A \in \mathbb{R}^{m \times n}$, $x \in \mathbb{R}^n$ and $y \in \mathbb{R}^m$. The algorithm
overwrites $y$ with $Ax + y$ by the loops of Algorithm 1.1.3 interchanged:
```
for j = 1:n
    for i = 1:m
        y(i) = y(i) + A(i,j) x(j)
    end
end
```
The program computes $y_i \leftarrow \mathrm{fl}(y_i + \mathrm{fl}(a_{ij} x_j))$ in this loop
order. -/
def algorithm_1_1_4 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) (y : Fin m → ℝ) :
    M (Fin m → ℝ) :=
  (List.finRange n).foldlM (fun y j =>
    (List.finRange m).foldlM (fun y i => do
      let p ← rnd (A i j * x j)
      let s ← rnd (y i + p)
      pure (Function.update y i s)) y) y

/-- **Algorithm 1.1.5** of [golub2013matrix] (`ijk` matrix multiplication). "If
$A \in \mathbb{R}^{m \times r}$, $B \in \mathbb{R}^{r \times n}$, and
$C \in \mathbb{R}^{m \times n}$ are given, then this algorithm overwrites $C$ with $C + AB$":
```
for i = 1:m
    for j = 1:n
        for k = 1:r
            C(i,j) = C(i,j) + A(i,k) B(k,j)
        end
    end
end
```
The program computes $c_{ij} \leftarrow \mathrm{fl}(c_{ij} + \mathrm{fl}(a_{ik} b_{kj}))$ in
this loop order. -/
def algorithm_1_1_5 {m r n : ℕ} (A : Matrix (Fin m) (Fin r) ℝ) (B : Matrix (Fin r) (Fin n) ℝ)
    (C : Matrix (Fin m) (Fin n) ℝ) : M (Matrix (Fin m) (Fin n) ℝ) :=
  (List.finRange m).foldlM (fun C i =>
    (List.finRange n).foldlM (fun C j =>
      (List.finRange r).foldlM (fun C k => do
        let p ← rnd (A i k * B k j)
        let c ← rnd (C i j + p)
        pure (C.updateRow i (Function.update (C i) j c))) C) C) C

/-- **Algorithm 1.1.6** of [golub2013matrix] (dot product matrix multiplication). Let
$A \in \mathbb{R}^{m \times r}$, $B \in \mathbb{R}^{r \times n}$ and
$C \in \mathbb{R}^{m \times n}$. The algorithm overwrites $C$ with $C + AB$:
```
for i = 1:m
    for j = 1:n
        C(i,j) = C(i,j) + A(i,:)·B(:,j)
    end
end
```

**Reading.** The dot-product notation leaves the rounding order implicit. The source introduces
the display as a rewrite of Algorithm 1.1.5, so the program interprets it as a single accumulation
starting at $C(i,j)$. Evaluating the dot product first and adding $C(i,j)$ afterward gives the same
exact result and may round differently.

The update is `FloatingPoint.dotAccum` started at $C(i,j)$. -/
def algorithm_1_1_6 {m r n : ℕ} (A : Matrix (Fin m) (Fin r) ℝ) (B : Matrix (Fin r) (Fin n) ℝ)
    (C : Matrix (Fin m) (Fin n) ℝ) : M (Matrix (Fin m) (Fin n) ℝ) :=
  (List.finRange m).foldlM (fun C i =>
    (List.finRange n).foldlM (fun C j => do
      let c ← dotAccum rnd (List.finRange r) (A i) (fun k => B k j) (C i j)
      pure (C.updateRow i (Function.update (C i) j c))) C) C

/-- **Algorithm 1.1.7** of [golub2013matrix] (saxpy matrix multiplication). Let
$A \in \mathbb{R}^{m \times r}$, $B \in \mathbb{R}^{r \times n}$ and
$C \in \mathbb{R}^{m \times n}$. The algorithm overwrites $C$ with $C + AB$:
```
for j = 1:n
    for k = 1:r
        C(:,j) = C(:,j) + A(:,k) B(k,j)
    end
end
```
Each update of column $j$ is the saxpy, Algorithm 1.1.2, with $a = B(k,j)$ and $x = A(:,k)$. -/
def algorithm_1_1_7 {m r n : ℕ} (A : Matrix (Fin m) (Fin r) ℝ) (B : Matrix (Fin r) (Fin n) ℝ)
    (C : Matrix (Fin m) (Fin n) ℝ) : M (Matrix (Fin m) (Fin n) ℝ) :=
  (List.finRange n).foldlM (fun C j =>
    (List.finRange r).foldlM (fun C k => do
      let c ← algorithm_1_1_2 rnd (B k j) (fun i => A i k) (fun i => C i j)
      pure (C.updateCol j c)) C) C

/-- **Algorithm 1.1.8** of [golub2013matrix] (outer product matrix multiplication). Let
$A \in \mathbb{R}^{m \times r}$, $B \in \mathbb{R}^{r \times n}$ and
$C \in \mathbb{R}^{m \times n}$. The algorithm overwrites $C$ with $C + AB$:
```
for k = 1:r
    C = C + A(:,k) B(k,:)
end
```
The outer product update $C = C + A(:,k) B(k,:)$ is written in the row form of §1.1.9: for
$i = 1, \dots, m$ and $j = 1, \dots, n$, $c_{ij} \leftarrow \mathrm{fl}(c_{ij} +
\mathrm{fl}(a_{ik} b_{kj}))$. -/
def algorithm_1_1_8 {m r n : ℕ} (A : Matrix (Fin m) (Fin r) ℝ) (B : Matrix (Fin r) (Fin n) ℝ)
    (C : Matrix (Fin m) (Fin n) ℝ) : M (Matrix (Fin m) (Fin n) ℝ) :=
  (List.finRange r).foldlM (fun C k =>
    (List.finRange m).foldlM (fun C i =>
      (List.finRange n).foldlM (fun C j => do
        let p ← rnd (A i k * B k j)
        let c ← rnd (C i j + p)
        pure (C.updateRow i (Function.update (C i) j c))) C) C) C

end Programs

/-! ### Normal forms: the loops fused into accumulations of single entries -/

section NormalForms

variable {M : Type → Type} [Monad M] [LawfulMonad M] (rnd : ℝ → M ℝ)

/-- The inner loop of the row-oriented gaxpy accumulates into $y_i$, so Algorithm 1.1.3 is a loop of
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

/-- Algorithm 1.1.5 is two loops that write one entry per step around the accumulations. -/
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
  rw [← Matrix.foldlM_updateRow_entrywise i
    (fun j c => dotAccum rnd (List.finRange r) (A i) (fun k => B k j) c)]
  congr 1
  funext C j
  have := Matrix.foldlM_updateRow_update i j
    (fun k c => do let p ← rnd (A i k * B k j); rnd (c + p)) (List.finRange r) C
  simp only [bind_assoc] at this
  exact this

/-- Algorithm 1.1.6 is Algorithm 1.1.5 with the innermost loop named. -/
private theorem algorithm_1_1_6_eq_algorithm_1_1_5 {m r n : ℕ} (A : Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin r) (Fin n) ℝ) (C : Matrix (Fin m) (Fin n) ℝ) :
    algorithm_1_1_6 rnd A B C = algorithm_1_1_5 rnd A B C := by
  rw [algorithm_1_1_5_eq]
  unfold algorithm_1_1_6
  congr 1
  funext C i
  exact Matrix.foldlM_updateRow_entrywise i
    (fun j c => dotAccum rnd (List.finRange r) (A i) (fun k => B k j) c) (List.finRange n) C

/-- Algorithm 1.1.7 is a loop that writes one column per step around a loop of saxpys. -/
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

/-- Each outer product update of Algorithm 1.1.8 is two loops that write one entry per step. -/
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
  have := Matrix.foldlM_updateRow_entrywise i
    (fun j c => do let p ← rnd (A i k * B k j); rnd (c + p))
    (List.finRange n) C
  simpa only [bind_assoc] using this

end NormalForms

/-! ### The exact runs are runs of the exact model -/

section Exact

/-- In the exact model, the run set of the dot product contains the result of the program in exact
arithmetic. -/
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

/-- **Algorithm 1.1.2** of [golub2013matrix], run set. Let `fp` be a rounding model, let
$a \in \mathbb{R}$, and let $x, y, \hat y \in \mathbb{R}^n$. Then $\hat y$ is a result of
Algorithm 1.1.2 in `fp` if and only if, for every $i$, there is an admissible rounding $p$ of
$a x_i$ such that $\hat y_i$ is an admissible rounding of $y_i + p$:
$$\hat y_i = \mathrm{fl}(y_i + \mathrm{fl}(a x_i)).$$

This is the relation of (2.7.17) of the source. The results are the run set of the program with
`M := SetM` and `rnd := fp.round`. -/
theorem algorithm_1_1_2_mem_run {n : ℕ} (a : ℝ) (x y ŷ : Fin n → ℝ) :
    ŷ ∈ (algorithm_1_1_2 fp.round a x y).run ↔
      ∀ i, ∃ p, fp.Rounds (a * x i) p ∧ fp.Rounds (y i + p) (ŷ i) := by
  have h := mem_run_foldlM_finRange_update
    (fun i b => do let p ← fp.round (a * x i); fp.round (b + p)) y ŷ
  simp only [bind_assoc] at h
  exact h.trans (by simp)

/-- **Algorithm 1.1.3** of [golub2013matrix], run set. Let `fp` be a rounding model, let
$A \in \mathbb{R}^{m \times n}$, $x \in \mathbb{R}^n$, and $y, \hat y \in \mathbb{R}^m$. Then
$\hat y$ is a result of Algorithm 1.1.3 in `fp` if and only if, for every $i$, $\hat y_i$ is a
result of the accumulation of the products $a_{ij} x_j$, $j = 1, \dots, n$, onto $y_i$:
$$\hat y_i = \mathrm{fl}(\cdots \mathrm{fl}(\mathrm{fl}(y_i + \mathrm{fl}(a_{i1} x_1)) +
  \mathrm{fl}(a_{i2} x_2)) \cdots + \mathrm{fl}(a_{in} x_n)).$$

The accumulation is `FloatingPoint.dotAccum fp.round (List.finRange n) (A i) x (y i)`. -/
theorem algorithm_1_1_3_mem_run {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ)
    (y ŷ : Fin m → ℝ) :
    ŷ ∈ (algorithm_1_1_3 fp.round A x y).run ↔
      ∀ i, ŷ i ∈ (dotAccum fp.round (List.finRange n) (A i) x (y i)).run := by
  rw [algorithm_1_1_3_eq]
  exact mem_run_foldlM_finRange_update (fun i b => dotAccum fp.round (List.finRange n) (A i) x b)
    y ŷ

/-- **Algorithm 1.1.4** of [golub2013matrix], run set. Let `fp` be a rounding model, let
$A \in \mathbb{R}^{m \times n}$, $x \in \mathbb{R}^n$, and $y, \hat y \in \mathbb{R}^m$. Then
$\hat y$ is a result of Algorithm 1.1.4 in `fp` if and only if, for every $i$, $\hat y_i$ is a
result of the accumulation of the products $a_{ij} x_j$, $j = 1, \dots, n$, onto $y_i$. So the
column-oriented gaxpy has the same results as the row-oriented gaxpy
(`GolubVanLoan.Chapter01.algorithm_1_1_3_mem_run`).

The proof is loop interchange in the relational model: the inner loop writes one entry per step,
so each step of the outer loop acts on every entry independently. -/
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

/-- **Algorithm 1.1.5** of [golub2013matrix], run set. Let `fp` be a rounding model, let
$A \in \mathbb{R}^{m \times r}$, $B \in \mathbb{R}^{r \times n}$, and
$C, \hat C \in \mathbb{R}^{m \times n}$. Then $\hat C$ is a result of Algorithm 1.1.5 in `fp` if
and only if, for all $i$ and $j$, $\hat c_{ij}$ is a result of the accumulation of the products
$a_{ik} b_{kj}$, $k = 1, \dots, r$, onto $c_{ij}$:
$$\hat c_{ij} = \mathrm{fl}(\cdots \mathrm{fl}(\mathrm{fl}(c_{ij} + \mathrm{fl}(a_{i1}
  b_{1j})) + \mathrm{fl}(a_{i2} b_{2j})) \cdots + \mathrm{fl}(a_{ir} b_{rj})).$$

The accumulation is `FloatingPoint.dotAccum fp.round (List.finRange r) (A i) (fun k => B k j) (C
i j)`. -/
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

/-- **Algorithm 1.1.6** of [golub2013matrix], run set. Let `fp` be a rounding model, let
$A \in \mathbb{R}^{m \times r}$, $B \in \mathbb{R}^{r \times n}$, and
$C, \hat C \in \mathbb{R}^{m \times n}$. Then $\hat C$ is a result of Algorithm 1.1.6 in `fp` if
and only if, for all $i$ and $j$, $\hat c_{ij}$ is a result of the accumulation of
$A(i,:) \cdot B(:,j)$ onto $c_{ij}$, as for Algorithm 1.1.5
(`GolubVanLoan.Chapter01.algorithm_1_1_5_mem_run`). -/
theorem algorithm_1_1_6_mem_run {m r n : ℕ} (A : Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin r) (Fin n) ℝ) (C Ĉ : Matrix (Fin m) (Fin n) ℝ) :
    Ĉ ∈ (algorithm_1_1_6 fp.round A B C).run ↔
      ∀ i j, Ĉ i j ∈ (dotAccum fp.round (List.finRange r) (A i) (fun k => B k j) (C i j)).run := by
  rw [algorithm_1_1_6_eq_algorithm_1_1_5]
  exact algorithm_1_1_5_mem_run fp A B C Ĉ

/-- **Algorithm 1.1.7** of [golub2013matrix], run set. Let `fp` be a rounding model, let
$A \in \mathbb{R}^{m \times r}$, $B \in \mathbb{R}^{r \times n}$, and
$C, \hat C \in \mathbb{R}^{m \times n}$. Then $\hat C$ is a result of Algorithm 1.1.7 in `fp` if
and only if, for all $i$ and $j$, $\hat c_{ij}$ is a result of the accumulation of the products
$a_{ik} b_{kj}$, $k = 1, \dots, r$, onto $c_{ij}$, as for Algorithm 1.1.5
(`GolubVanLoan.Chapter01.algorithm_1_1_5_mem_run`).

The loop over $j$ writes column $j$ only. Each step of the loop over $k$ is a saxpy on that
column, which acts on every entry independently, so the loop over $k$ is, entry by entry, the
accumulation over $k$. -/
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

/-- **Algorithm 1.1.8** of [golub2013matrix], run set. Let `fp` be a rounding model, let
$A \in \mathbb{R}^{m \times r}$, $B \in \mathbb{R}^{r \times n}$, and
$C, \hat C \in \mathbb{R}^{m \times n}$. Then $\hat C$ is a result of Algorithm 1.1.8 in `fp` if
and only if, for all $i$ and $j$, $\hat c_{ij}$ is a result of the accumulation of the products
$a_{ik} b_{kj}$, $k = 1, \dots, r$, onto $c_{ij}$, as for Algorithm 1.1.5
(`GolubVanLoan.Chapter01.algorithm_1_1_5_mem_run`). For $r = 1$ this is (2.7.18) of the source.

Each rank-one update acts on every entry independently, so the loop over $k$ is, entry by entry,
the accumulation over $k$. -/
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

/-- **Algorithm 1.1.1** of [golub2013matrix], exact correctness. For $x, y \in \mathbb{R}^n$, in
exact arithmetic Algorithm 1.1.1 returns $c = x^T y$.

Exact arithmetic is the program with `M := Id` and `rnd := pure`. -/
theorem algorithm_1_1_1_spec {n : ℕ} (x y : Fin n → ℝ) :
    Id.run (algorithm_1_1_1 pure x y) = x ⬝ᵥ y := by
  have h := algorithm_1_1_1_mem_exact x y
  rw [algorithm_1_1_1_eq_dotAccum (RoundingModel.exact ℝ).round, mem_run_dotAccum_exact_iff] at h
  rw [h, zero_add, ← Fin.sum_univ_def]
  rfl

/-- **Algorithm 1.1.2** of [golub2013matrix], exact correctness. For $a \in \mathbb{R}$ and
$x, y \in \mathbb{R}^n$, in exact arithmetic Algorithm 1.1.2 returns $y + ax$. -/
theorem algorithm_1_1_2_spec {n : ℕ} (a : ℝ) (x y : Fin n → ℝ) :
    Id.run (algorithm_1_1_2 pure a x y) = y + a • x := by
  funext i
  obtain ⟨p, hp, hs⟩ := (algorithm_1_1_2_mem_run _ a x y _).1 (algorithm_1_1_2_mem_exact a x y) i
  rw [RoundingModel.exact_rounds_iff] at hp hs
  rw [hs, hp]
  rfl

/-- **Algorithm 1.1.3** of [golub2013matrix], exact correctness. For
$A \in \mathbb{R}^{m \times n}$, $x \in \mathbb{R}^n$ and $y \in \mathbb{R}^m$, in exact
arithmetic Algorithm 1.1.3 returns $Ax + y$. -/
theorem algorithm_1_1_3_spec {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ)
    (y : Fin m → ℝ) : Id.run (algorithm_1_1_3 pure A x y) = y + A *ᵥ x := by
  funext i
  have h := (algorithm_1_1_3_mem_run _ A x y _).1 (algorithm_1_1_3_mem_exact A x y) i
  rw [mem_run_dotAccum_exact_iff] at h
  rw [h, Pi.add_apply, ← Fin.sum_univ_def]
  rfl

/-- **Algorithm 1.1.4** of [golub2013matrix], exact correctness. For
$A \in \mathbb{R}^{m \times n}$, $x \in \mathbb{R}^n$ and $y \in \mathbb{R}^m$, in exact
arithmetic Algorithm 1.1.4 returns $Ax + y$, as Algorithm 1.1.3 does. -/
theorem algorithm_1_1_4_spec {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ)
    (y : Fin m → ℝ) : Id.run (algorithm_1_1_4 pure A x y) = y + A *ᵥ x := by
  funext i
  have h := (algorithm_1_1_4_mem_run _ A x y _).1 (algorithm_1_1_4_mem_exact A x y) i
  rw [mem_run_dotAccum_exact_iff] at h
  rw [h, Pi.add_apply, ← Fin.sum_univ_def]
  rfl

/-- If every entry $\hat c_{ij}$ is the exact accumulation of row $i$ of $A$ against column $j$ of
$B$ onto $c_{ij}$, then $\hat C = C + AB$. -/
private theorem eq_add_mul_of_forall_mem_run_exact {m r n : ℕ} {A : Matrix (Fin m) (Fin r) ℝ}
    {B : Matrix (Fin r) (Fin n) ℝ} {C Ĉ : Matrix (Fin m) (Fin n) ℝ}
    (h : ∀ i j, Ĉ i j ∈
      (dotAccum (RoundingModel.exact ℝ).round (List.finRange r) (A i) (fun k => B k j)
        (C i j)).run) :
    Ĉ = C + A * B := by
  ext i j
  rw [mem_run_dotAccum_exact_iff.1 (h i j), Matrix.add_apply, ← Fin.sum_univ_def]
  rfl

/-- **Algorithm 1.1.5** of [golub2013matrix], exact correctness. For
$A \in \mathbb{R}^{m \times r}$, $B \in \mathbb{R}^{r \times n}$ and
$C \in \mathbb{R}^{m \times n}$, in exact arithmetic Algorithm 1.1.5 returns $C + AB$. -/
theorem algorithm_1_1_5_spec {m r n : ℕ} (A : Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin r) (Fin n) ℝ) (C : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (algorithm_1_1_5 pure A B C) = C + A * B :=
  eq_add_mul_of_forall_mem_run_exact
    ((algorithm_1_1_5_mem_run _ A B C _).1 (algorithm_1_1_5_mem_exact A B C))

/-- **Algorithm 1.1.6** of [golub2013matrix], exact correctness. For
$A \in \mathbb{R}^{m \times r}$, $B \in \mathbb{R}^{r \times n}$ and
$C \in \mathbb{R}^{m \times n}$, in exact arithmetic Algorithm 1.1.6 returns $C + AB$. -/
theorem algorithm_1_1_6_spec {m r n : ℕ} (A : Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin r) (Fin n) ℝ) (C : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (algorithm_1_1_6 pure A B C) = C + A * B := by
  rw [algorithm_1_1_6_eq_algorithm_1_1_5]
  exact algorithm_1_1_5_spec A B C

/-- **Algorithm 1.1.7** of [golub2013matrix], exact correctness. For
$A \in \mathbb{R}^{m \times r}$, $B \in \mathbb{R}^{r \times n}$ and
$C \in \mathbb{R}^{m \times n}$, in exact arithmetic Algorithm 1.1.7 returns $C + AB$. -/
theorem algorithm_1_1_7_spec {m r n : ℕ} (A : Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin r) (Fin n) ℝ) (C : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (algorithm_1_1_7 pure A B C) = C + A * B :=
  eq_add_mul_of_forall_mem_run_exact
    ((algorithm_1_1_7_mem_run _ A B C _).1 (algorithm_1_1_7_mem_exact A B C))

/-- **Algorithm 1.1.8** of [golub2013matrix], exact correctness. For
$A \in \mathbb{R}^{m \times r}$, $B \in \mathbb{R}^{r \times n}$ and
$C \in \mathbb{R}^{m \times n}$, in exact arithmetic Algorithm 1.1.8 returns $C + AB$.

The expansion (1.1.4) (`GolubVanLoan.Chapter01.equation_1_1_4`) is the reading of the same
identity in the source. -/
theorem algorithm_1_1_8_spec {m r n : ℕ} (A : Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin r) (Fin n) ℝ) (C : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (algorithm_1_1_8 pure A B C) = C + A * B :=
  eq_add_mul_of_forall_mem_run_exact
    ((algorithm_1_1_8_mem_run _ A B C _).1 (algorithm_1_1_8_mem_exact A B C))

/-! ### Bridges to the backbone's relational inner and matrix products -/

section Bridges

variable {fp : RoundingModel ℝ}

/-- **Algorithm 1.1.1** of [golub2013matrix], rounding bridge. Let `fp` be an idempotent rounding
model: if $y$ is an admissible rounding of some number and $z$ is an admissible rounding of $y$,
then $z = y$. Let $x, y \in \mathbb{R}^n$. Then every result $s$ of Algorithm 1.1.1 in `fp` is a
recursive inner product of $x$ and $y$: there are admissible roundings $p_i$ of the products
$x_i y_i$ and an order $i_1, \dots, i_n$ of the indices such that $s$ is a result of the
recursive summation $s_1 = p_{i_1}$, $s_k = \mathrm{fl}(s_{k-1} + p_{i_k})$.

The relation is `FloatingPoint.RoundsDot fp x y s`. Idempotence makes the first addition
$0 + \mathrm{fl}(x_1 y_1)$ exact, which is what (2.7.9) of the source assumes when it writes
$s_1 = x_1 y_1 (1 + \delta_1)$. Without this hypothesis,
`FloatingPoint.abs_sub_le_of_mem_run_dotAccum` bounds a result by $\gamma_{n+1} |x|^T |y|$. -/
theorem algorithm_1_1_1_rounds (hfp : fp.IsIdempotent) {n : ℕ} (x y : Fin n → ℝ) :
    ∀ s ∈ (algorithm_1_1_1 fp.round x y).run, RoundsDot fp x y s := fun _ hs =>
  roundsDot_of_mem_run_dotAccum hfp (List.nodup_finRange n) List.mem_finRange hs

/-- **Algorithm 1.1.1** of [golub2013matrix], existence of a result. Let `fp` be a total rounding
model, in which every real number has an admissible rounding, and let $x, y \in \mathbb{R}^n$.
Then Algorithm 1.1.1 has at least one result in `fp`.

So the statements about every result of the algorithm are not vacuous. -/
theorem algorithm_1_1_1_run_nonempty (hfp : fp.IsTotal) {n : ℕ} (x y : Fin n → ℝ) :
    (algorithm_1_1_1 fp.round x y).run.Nonempty :=
  dotAccum_run_nonempty hfp (List.finRange n) x y 0

/-- If every entry $\hat c_{ij}$ is a result of the accumulation of row $i$ of $A$ against column
$j$ of $B$ onto $0$ in an idempotent model, then $\hat C$ is a computed matrix product in the
sense of `FloatingPoint.RoundsMul`. -/
private theorem roundsMul_of_forall_mem_run (hfp : fp.IsIdempotent) {m r n : ℕ}
    {A : Matrix (Fin m) (Fin r) ℝ} {B : Matrix (Fin r) (Fin n) ℝ} {Ĉ : Matrix (Fin m) (Fin n) ℝ}
    (h : ∀ i j, Ĉ i j ∈
      (dotAccum fp.round (List.finRange r) (A i) (fun k => B k j) ((0 : Matrix _ _ ℝ) i j)).run) :
    RoundsMul fp A B Ĉ := fun i j =>
  roundsDot_of_mem_run_dotAccum hfp (List.nodup_finRange r) List.mem_finRange (h i j)

/-- **Algorithm 1.1.5** of [golub2013matrix], rounding bridge. Let `fp` be an idempotent rounding
model, and let $A \in \mathbb{R}^{m \times r}$ and $B \in \mathbb{R}^{r \times n}$. Then every
result $\hat C$ of Algorithm 1.1.5 in `fp`, started from $C = 0$, is a computed matrix product:
each entry $\hat c_{ij}$ is a recursive inner product of row $i$ of $A$ and column $j$ of $B$,
as in `GolubVanLoan.Chapter01.algorithm_1_1_1_rounds`.

The relation is `FloatingPoint.RoundsMul fp A B Ĉ`. With it,
`FloatingPoint.abs_sub_entrywiseLE_of_roundsMul` gives $|\hat C - AB| \le \gamma_r |A| |B|$
entrywise, the bound (2.7.19) of the source. -/
theorem algorithm_1_1_5_rounds (hfp : fp.IsIdempotent) {m r n : ℕ} (A : Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin r) (Fin n) ℝ) :
    ∀ Ĉ ∈ (algorithm_1_1_5 fp.round A B 0).run, RoundsMul fp A B Ĉ := fun _ h =>
  roundsMul_of_forall_mem_run hfp ((algorithm_1_1_5_mem_run _ A B 0 _).1 h)

/-- **Algorithm 1.1.6** of [golub2013matrix], rounding bridge. Let `fp` be an idempotent rounding
model, and let $A \in \mathbb{R}^{m \times r}$ and $B \in \mathbb{R}^{r \times n}$. Then every
result $\hat C$ of Algorithm 1.1.6 in `fp`, started from $C = 0$, is a computed matrix product
in the sense of `FloatingPoint.RoundsMul`.

From $c_{ij} = 0$, each entry is a result of Algorithm 1.1.1 on $A(i,:)$ and $B(:,j)$. -/
theorem algorithm_1_1_6_rounds (hfp : fp.IsIdempotent) {m r n : ℕ} (A : Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin r) (Fin n) ℝ) :
    ∀ Ĉ ∈ (algorithm_1_1_6 fp.round A B 0).run, RoundsMul fp A B Ĉ := fun _ h =>
  roundsMul_of_forall_mem_run hfp ((algorithm_1_1_6_mem_run _ A B 0 _).1 h)

/-- **Algorithm 1.1.7** of [golub2013matrix], rounding bridge. Let `fp` be an idempotent rounding
model, and let $A \in \mathbb{R}^{m \times r}$ and $B \in \mathbb{R}^{r \times n}$. Then every
result $\hat C$ of Algorithm 1.1.7 in `fp`, started from $C = 0$, is a computed matrix product
in the sense of `FloatingPoint.RoundsMul`.

This is the case "for a gaxpy based procedure" of (2.7.19) of the source. -/
theorem algorithm_1_1_7_rounds (hfp : fp.IsIdempotent) {m r n : ℕ} (A : Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin r) (Fin n) ℝ) :
    ∀ Ĉ ∈ (algorithm_1_1_7 fp.round A B 0).run, RoundsMul fp A B Ĉ := fun _ h =>
  roundsMul_of_forall_mem_run hfp ((algorithm_1_1_7_mem_run _ A B 0 _).1 h)

/-- **Algorithm 1.1.8** of [golub2013matrix], rounding bridge. Let `fp` be an idempotent rounding
model, and let $A \in \mathbb{R}^{m \times r}$ and $B \in \mathbb{R}^{r \times n}$. Then every
result $\hat C$ of Algorithm 1.1.8 in `fp`, started from $C = 0$, is a computed matrix product
in the sense of `FloatingPoint.RoundsMul`.

This is the case "or outer product based" of (2.7.19) of the source. -/
theorem algorithm_1_1_8_rounds (hfp : fp.IsIdempotent) {m r n : ℕ} (A : Matrix (Fin m) (Fin r) ℝ)
    (B : Matrix (Fin r) (Fin n) ℝ) :
    ∀ Ĉ ∈ (algorithm_1_1_8 fp.round A B 0).run, RoundsMul fp A B Ĉ := fun _ h =>
  roundsMul_of_forall_mem_run hfp ((algorithm_1_1_8_mem_run _ A B 0 _).1 h)

end Bridges

/-! ### Equation (1.1.4): the matrix product as a sum of outer products -/

/-- **Equation (1.1.4)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times r}$ and
$B \in \mathbb{R}^{r \times n}$, let $a_k$ be the $k$-th column of $A$, and let $b_k^T$ be the
$k$-th row of $B$, as in the partitionings (1.1.3). Then
$$AB = \sum_{k=1}^{r} a_k b_k^T.$$

The outer product $a_k b_k^T$ is `Matrix.vecMulVec`. -/
theorem equation_1_1_4 {m r n : ℕ} (A : Matrix (Fin m) (Fin r) ℝ) (B : Matrix (Fin r) (Fin n) ℝ) :
    A * B = ∑ k, vecMulVec (fun i => A i k) (B k) := by
  ext i j
  simp [Matrix.mul_apply, vecMulVec_apply, Matrix.sum_apply]

end GolubVanLoan.Chapter01

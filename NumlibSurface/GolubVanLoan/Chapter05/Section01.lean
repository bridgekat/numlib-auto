/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Basic.Real.Sign
import Numlib.FloatingPoint.Givens
import Numlib.FloatingPoint.Program
import Numlib.LinearAlgebra.Matrix.WY
import NumlibSurface.GolubVanLoan.Chapter01.Section01

/-!
# Golub and Van Loan, Section 5.1: Householder and Givens transformations

This module formalizes §5.1 of [golub2013matrix], the two orthogonal transformations that introduce
zeros into a vector. A Householder reflection $P = I - \beta v v^T$ with $\beta = 2 / v^T v$ maps
$x \in \mathbb{R}^m$ to a multiple of $e_1$ when $v = x \pm \|x\|_2 e_1$. A Givens rotation
$G(i, k, \theta)$ rotates the plane of the coordinates $i$ and $k$, and a suitable angle makes the
entry $k$ of a vector zero. The module defines the computation of a Householder vector (Algorithm
5.1.1), the updates $PA$ and $AP$ (§5.1.4), the factored form (5.1.3) of a product of reflections
and its accumulation (§5.1.6), the WY representation (§5.1.7 and Algorithm 5.1.2), the computation
of a Givens rotation (Algorithm 5.1.3), the Givens updates (§5.1.9), Stewart's encoding of a
rotation by one number (§5.1.11), and the complex case (§5.1.13). For each program it proves the
exact semantics and, where the source analyses the program, a bound on its rounding errors (§5.1.5,
§5.1.10, §5.1.12).

In the bounds, $\mathrm{fl}(\cdot)$ is a rounded result, $u$ is the unit roundoff and
$\gamma_K = Ku/(1 - Ku)$. A computed $\hat y$ is a relative perturbation of order $K$ of $y$ if
$\hat y = y(1 + \theta)$ with $|\theta| \le \gamma_K$. For a list $o$ of indices, $x|_o$ is the
restriction of $x$ to the listed indices. Computed data $(\hat v, \hat \beta)$ are reflector data of
order $K$ for $x$, with pivot $p$ and target $c$, if they are relative perturbations of order $K$ of
exact $(v, \beta)$ such that $I - \beta v v^T$ is orthogonal, $(I - \beta v v^T) x = c\, e_p$ and
$|\beta| v^T v \le 2$. The proofs specialize the backbone modules `Numlib.FloatingPoint.Householder`
and `Numlib.FloatingPoint.Givens`, which define the rounding relations of the Householder and Givens
computations and bound their errors, and `Numlib.LinearAlgebra.Matrix.WY`.

## Main definitions

* Equation (5.1.1), `GolubVanLoan.Chapter05.householderMatrix`: the Householder matrix
  $I - (2 / v^T v) v v^T$ of a vector $v$.
* Algorithm 5.1.1, `GolubVanLoan.Chapter05.algorithm_5_1_1`: the computation of a Householder vector
  $v$ and of $\beta$ for $x$ (the source's `house`).
* Algorithm 5.1.1, `GolubVanLoan.Chapter05.houseOn`: the same computation on the entries of a vector
  listed by an index list.
* §5.1.4, `GolubVanLoan.Chapter05.householderApplyLeft` and
  `GolubVanLoan.Chapter05.householderApplyRight`: the updates $A - (\beta v)(v^T A)$ and
  $A - (A v)(\beta v)^T$ of a block of $A$.
* Equation (5.1.3), `GolubVanLoan.Chapter05.householderProduct`,
  `GolubVanLoan.Chapter05.storedHouseholderVec`, `GolubVanLoan.Chapter05.storedReflectors` and
  `GolubVanLoan.Chapter05.factoredQ`: the factored form $Q = Q_1 \cdots Q_r$,
  $Q_j = I - \beta_j v_j v_j^T$, of a product of reflections, and its storage in an array.
* Equations (5.1.4) and (5.1.5), `GolubVanLoan.Chapter05.recomputedBeta`,
  `GolubVanLoan.Chapter05.factoredQTransposeMul` and `GolubVanLoan.Chapter05.factoredQFirstColumns`:
  the programs that compute $Q^T C$ and the first $k$ columns of $Q$ from the factored form, with
  $\beta_j$ recomputed from the stored vector.
* Equation (5.1.5), `GolubVanLoan.Chapter05.storedQFirstColumns`: the first $k$ columns of $Q$ with
  the $\beta_j$ that Algorithm 5.1.1 returned.
* §5.1.6, `GolubVanLoan.Chapter05.forwardAccumulation` and
  `GolubVanLoan.Chapter05.backwardAccumulation`: the two orders of accumulating
  $Q = Q_1 \cdots Q_r$.
* Algorithm 5.1.2, `GolubVanLoan.Chapter05.algorithm_5_1_2`: the WY representation of a product of
  reflections.
* Equation (5.1.7), `GolubVanLoan.Chapter05.givensRotation`: the Givens rotation $G(i, k, \theta)$.
* Algorithm 5.1.3, `GolubVanLoan.Chapter05.algorithm_5_1_3`: the computation of $c$ and $s$ (the
  source's `givens`).
* §5.1.9, `GolubVanLoan.Chapter05.givensApplyLeft` and `GolubVanLoan.Chapter05.givensApplyRight`:
  the updates $G^T A$ and $A G$ of two rows or two columns.
* Equations (5.1.9) and (5.1.10), `GolubVanLoan.Chapter05.rotationCode` and
  `GolubVanLoan.Chapter05.rotationDecode`: Stewart's encoding of a rotation by one number, and the
  reconstruction.
* §5.1.12, `GolubVanLoan.Chapter05.orthogonalToWorkingPrecision`: a matrix within distance
  $\varepsilon$ of an orthogonal matrix in the 2-norm.
* §6.5.4, `GolubVanLoan.Chapter05.hyperbolicApplyLeft`: a hyperbolic rotation applied to two rows.

## Main results

* §5.1.2, `GolubVanLoan.Chapter05.householderMatrix_isSymm` and
  `GolubVanLoan.Chapter05.householderMatrix_mem_orthogonalGroup`: Householder matrices are symmetric
  and orthogonal.
* Equation (5.1.2), `GolubVanLoan.Chapter05.equation_5_1_2`: if $v = x \pm \|x\|_2 e_1 \neq 0$, then
  $Px = \mp \|x\|_2 e_1$.
* §5.1.3, `GolubVanLoan.Chapter05.parlett_formula`: Parlett's formula $x_1 - \|x\|_2 = -(x_2^2 +
  \cdots + x_m^2)/(x_1 + \|x\|_2)$.
* Algorithm 5.1.1, `GolubVanLoan.Chapter05.houseOn_rounds`: every computed result satisfies the
  rounding relation `FloatingPoint.RoundsHouseholderVectorParlett` of the backbone.
* Algorithm 5.1.1, `GolubVanLoan.Chapter05.houseOn_spec` and
  `GolubVanLoan.Chapter05.algorithm_5_1_1_spec`: in exact arithmetic $v_1 = 1$, and
  $I - \beta v v^T$ is orthogonal and maps $x$ to $\|x\|_2 e_1$.
* §5.1.5, `GolubVanLoan.Chapter05.houseOn_rounding` and
  `GolubVanLoan.Chapter05.algorithm_5_1_1_rounding`: the computed $(\hat v, \hat \beta)$ are
  reflector data of order $18m + 31$.
* §5.1.4, `GolubVanLoan.Chapter05.householderApplyLeft_rounds`,
  `GolubVanLoan.Chapter05.householderApplyRight_rounds`,
  `GolubVanLoan.Chapter05.householderApplyLeft_spec` and
  `GolubVanLoan.Chapter05.householderApplyRight_spec`: the rounding bridges and the exact semantics
  of the Householder updates.
* §5.1.5, `GolubVanLoan.Chapter05.householderApplyLeft_rounding` and
  `GolubVanLoan.Chapter05.householderApplyRight_rounding`: the computed update differs from the
  exact update $PA$ or $AP$ by at most $3\gamma_{3K + \ell + 3}$ times the norm of the block, where
  $\ell$ is the length of the reflector.
* §5.1.5, `GolubVanLoan.Chapter05.householderMatrix_computed_sub_le`:
  $\|\hat P - P\|_2 \le 8\gamma_{18m + 31}$ for the Householder matrix $\hat P$ of a computed
  vector.
* Equations (5.1.4) and (5.1.5), `GolubVanLoan.Chapter05.equation_5_1_4` and
  `GolubVanLoan.Chapter05.equation_5_1_5`: the programs compute $Q^T C$ and $Q(:, 1{:}k)$ for the
  factored form with the recomputed $\beta_j$.
* Equation (5.1.5), `GolubVanLoan.Chapter05.storedQFirstColumns_spec`: the program with the returned
  $\beta_j$ computes $Q(:, 1{:}k)$.
* §5.1.6, `GolubVanLoan.Chapter05.forwardAccumulation_spec` and
  `GolubVanLoan.Chapter05.backwardAccumulation_spec`: both accumulations compute $Q_1 \cdots Q_r$.
* Equation (5.1.6), `GolubVanLoan.Chapter05.equation_5_1_6`: a product of $r$ reflections is
  $I - W Y^T$ with $W, Y \in \mathbb{R}^{m \times r}$.
* Lemma 5.1.1, `GolubVanLoan.Chapter05.lemma_5_1_1`: $(I - W Y^T)(I - \beta v v^T) = I - W_+ Y_+^T$
  with $W_+ = [W \mid z]$, $Y_+ = [Y \mid v]$, $z = \beta (I - W Y^T) v$.
* Algorithm 5.1.2, `GolubVanLoan.Chapter05.algorithm_5_1_2_spec`: the algorithm computes the WY
  representation.
* §5.1.7, `GolubVanLoan.Chapter05.blockReflector_mem_orthogonalGroup`: $I - 2 V V^T$ is orthogonal
  if $V^T V = I$.
* §5.1.8, `GolubVanLoan.Chapter05.givensRotation_mem_orthogonalGroup`: Givens rotations are
  orthogonal.
* Equation (5.1.8), `GolubVanLoan.Chapter05.equation_5_1_8`: the choice of $c$ and $s$ that makes
  the entry $k$ of $G^T x$ zero.
* Algorithm 5.1.3, `GolubVanLoan.Chapter05.algorithm_5_1_3_rounds` and
  `GolubVanLoan.Chapter05.algorithm_5_1_3_spec`: the rounding bridge, and in exact arithmetic
  $c^2 + s^2 = 1$ and $sa + cb = 0$.
* §5.1.10, `GolubVanLoan.Chapter05.algorithm_5_1_3_rounding`: the computed $\hat c$ and $\hat s$ are
  relative perturbations of order $13$ of an exact rotation.
* §5.1.9, `GolubVanLoan.Chapter05.givensApplyLeft_rounds`,
  `GolubVanLoan.Chapter05.givensApplyRight_rounds`, `GolubVanLoan.Chapter05.givensApplyLeft_spec`
  and `GolubVanLoan.Chapter05.givensApplyRight_spec`: the rounding bridges and the exact semantics
  of the Givens updates.
* §5.1.10, `GolubVanLoan.Chapter05.givensApplyLeft_rounding` and
  `GolubVanLoan.Chapter05.givensApplyRight_rounding`: the computed update differs from the exact
  update by at most $\sqrt 2\, \gamma_{K+2}$ times the norm of $A$.
* §5.1.11, `GolubVanLoan.Chapter05.rotationDecode_rotationCode`: decoding the code of $(c, s)$ gives
  $(c, s)$ or $(-c, -s)$.
* §5.1.12, `GolubVanLoan.Chapter05.orthogonalToWorkingPrecision_transpose_mul_self`: $\|\hat Q^T
  \hat Q - I\|_2 \le 2\varepsilon + \varepsilon^2$.
* §5.1.12, `GolubVanLoan.Chapter05.givensRotation_orthogonalToWorkingPrecision`,
  `GolubVanLoan.Chapter05.householderMatrix_orthogonalToWorkingPrecision`,
  `GolubVanLoan.Chapter05.one_sub_smul_vecMulVec_computed_sub_le` and
  `GolubVanLoan.Chapter05.one_sub_smul_vecMulVec_orthogonalToWorkingPrecision`: the matrices built
  from the outputs of Algorithms 5.1.3 and 5.1.1 are orthogonal to working precision.
* Equation (5.1.11), `GolubVanLoan.Chapter05.equation_5_1_11`: a sequence of computed two-sided
  orthogonal updates is an exact orthogonal update of a nearby matrix.
* §5.1.13, `GolubVanLoan.Chapter05.complexHouseholder` and
  `GolubVanLoan.Chapter05.complexGivens_mem_unitaryGroup`: complex Householder matrices and complex
  Givens rotations are unitary.
* Equation (5.1.12), `GolubVanLoan.Chapter05.equation_5_1_12`: a complex Givens rotation built from
  three real ones.
* §6.5.4, `GolubVanLoan.Chapter05.hyperbolicApplyLeft_spec`: the exact semantics of the hyperbolic
  row update.

## Conventions

* Vectors are `Fin m → ℝ`, and indices are 0-based: the source's $x(1)$ is `x 0`, and $e_1$ is
  `Pi.single 0 1`. A vector of type `Fin (k + 1) → ℝ` has length $m = k + 1 \ge 1$.
* The matrix $I - \beta v v^T$ is `1 - β • vecMulVec v v`. The source's Householder matrix
  $I - 2 v v^T / v^T v$ is `GolubVanLoan.Chapter05.householderMatrix v`, which is the backbone's
  `Matrix.reflector v`.
* The Givens rotation $G(i, k, \theta)$ of (5.1.7) is
  `GolubVanLoan.Chapter05.givensRotation i k c s`, which is `Matrix.planeRotation i k c (-s)`. The
  backbone's plane rotation has the sign convention of the Jacobi method; the rounding relations of
  `Numlib.FloatingPoint.Givens` are stated in the convention of the source.
* A block $A(j{:}m, k{:}n)$ is the full matrix together with the lists of its row and column
  indices, such as `GolubVanLoan.Chapter05.indexFrom m j`. A subvector is the full vector together
  with its list of active indices.
* The source's first-order bounds $O(u)$ are stated with explicit constants $\gamma_K$.

## Implementation notes

* Every program is written once, generic in a monad `M` and a rounding hook `rnd : ℝ → M ℝ`, as in
  the algorithm conventions of `NumlibSurface.GolubVanLoan` and `Numlib.FloatingPoint.Program`. A
  theorem `…_rounds` says that every run in the rounding model (`M := SetM`, `rnd := fp.round`)
  satisfies a rounding relation of the backbone. A theorem `…_spec` gives the exact semantics
  (`M := Id`, `rnd := pure`), read off the bridge at the exact model
  `FloatingPoint.RoundingModel.exact`. A theorem `…_rounding` gives the error bound of the source,
  where the source analyses the program.
* The Householder and Givens programs of this module are the shared helpers of the library, and
  later chapters call them instead of defining variants: `GolubVanLoan.Chapter05.houseOn`,
  `GolubVanLoan.Chapter05.householderApplyLeft`, `GolubVanLoan.Chapter05.householderApplyRight`,
  `GolubVanLoan.Chapter05.givensRotation`, `GolubVanLoan.Chapter05.givensRotateVec` (with exact
  semantics `GolubVanLoan.Chapter05.givensRotateVec_pure`),
  `GolubVanLoan.Chapter05.givensApplyLeft`, `GolubVanLoan.Chapter05.givensApplyRight`,
  `GolubVanLoan.Chapter05.householderProduct`, `GolubVanLoan.Chapter05.forwardAccumulation` and
  `GolubVanLoan.Chapter05.backwardAccumulation`. The update programs work in place on the full
  matrix over lists of row and column indices; a block is never copied into an array of type
  `Fin (m - j)`.
* Reflector data are lists `List ((Fin m → ℝ) × ℝ)` of pairs $(v, \beta)$ in order of application.
  Each $v$ has full length and is zero outside its active rows, and each $\beta$ is the value that
  Algorithm 5.1.1 returned. A reflector is never rebuilt as $\beta = 2 / v^T v$ from a stored $v$:
  when Algorithm 5.1.1 returns $\beta = 0$, the rebuilt matrix is a reflection and not the identity
  that was applied.
* The rounding theorems for Algorithm 5.1.1 and the Householder updates assume an idempotent
  rounding model (`FloatingPoint.RoundingModel.IsIdempotent`), because their inner products are
  accumulated from $0$.
* Later chapters also use the loop lemmas `GolubVanLoan.Chapter05.mem_run_foldlM_updateCol_of_nodup`
  and `GolubVanLoan.Chapter05.mem_run_foldlM_updateRow_of_nodup`, the entry formulas for
  $(I - \beta v v^T) M$ and $M (I - \beta v v^T)$ with $v$ supported on a set
  (`GolubVanLoan.Chapter05.one_sub_smul_vecMulVec_mul_apply` and its variants), the selection matrix
  `GolubVanLoan.Chapter05.selCols`, the index lists `GolubVanLoan.Chapter05.indexFrom` and
  `GolubVanLoan.Chapter05.indexTo`, and the hyperbolic row update
  `GolubVanLoan.Chapter05.hyperbolicApplyLeft` of §6.5.4.

## Deviations from the source

* **(5.1.1), (5.1.2) and §5.1.13** (domain). `GolubVanLoan.Chapter05.householderMatrix`
  assigns the identity to the zero vector, extending the source's nonzero domain.
  `GolubVanLoan.Chapter05.equation_5_1_2` and `GolubVanLoan.Chapter05.complexHouseholder` impose
  the nonzero normal explicitly for the selected sign. The complex theorem fixes the phase at
  $1$ when the first component is zero.
* **(5.1.8)** (reading). `GolubVanLoan.Chapter05.equation_5_1_8` requires a nonzero input pair
  to ensure a nonzero denominator and gives the first component as well as the zero second
  component.
* **§5.1.4, §5.1.9 and §6.5.4** (generalization).
  `GolubVanLoan.Chapter05.householderApplyLeft`, `GolubVanLoan.Chapter05.householderApplyRight`,
  `GolubVanLoan.Chapter05.givensApplyLeft`, `GolubVanLoan.Chapter05.givensApplyRight` and
  `GolubVanLoan.Chapter05.hyperbolicApplyLeft` work on selected index lists, including
  noncontiguous ones. The exact specifications use duplicate-free lists.
* **§5.1.5 and §5.1.10** (precision). The rounding theorems state explicit constants in the
  relative rounding model. The update bounds use row or column norms and the Frobenius norm of
  the selected block where the source gives a spectral-norm backward error.
  `GolubVanLoan.Chapter05.one_sub_smul_vecMulVec_computed_sub_le` also analyzes the applied
  reflector with the actual computed coefficient, including an identity step.
* **(5.1.3), (5.1.6) and Algorithm 5.1.2** (generalizations).
  `GolubVanLoan.Chapter05.householderProduct` and the accumulation programs accept arbitrary
  lists of rank-one update data. `GolubVanLoan.Chapter05.equation_5_1_6` and
  `GolubVanLoan.Chapter05.algorithm_5_1_2_spec` establish WY even for nonorthogonal factors and
  empty data.
* **§5.1.12** (precision). `GolubVanLoan.Chapter05.orthogonalToWorkingPrecision` takes an
  explicit tolerance in the spectral norm. The corollary bounds the orthogonality defect by
  $2\varepsilon+\varepsilon^2$. Equation (5.1.11) assumes a local Frobenius error bound at the
  computed iterates and gives explicit global Frobenius and spectral bounds.
* **(5.1.12)** (scope). `GolubVanLoan.Chapter05.equation_5_1_12` proves that the second
  component is zero using the three real rotations.
  `GolubVanLoan.Chapter05.complexGivens_mem_unitaryGroup` gives the separate unitary-matrix
  result.
* **Algorithm 5.1.1** (correction). The source sets $\beta = -2$ in the branch $\sigma = 0$,
  $x(1) < 0$, which makes $P$ not orthogonal. The program sets $\beta = 2$. See
  `GolubVanLoan.Chapter05.algorithm_5_1_1`.
* **Equations (5.1.4) and (5.1.5)** (correction). The source recovers
  $\beta_j = 2/(1 + \|A(j+1{:}m, j)\|_2^2)$ from the stored vector, which is wrong when Algorithm
  5.1.1 returned $\beta_j = 0$. The displays are stated for the recomputed $\beta_j$, and the first
  columns of $Q$ with the returned $\beta_j$ are a separate program. See
  `GolubVanLoan.Chapter05.equation_5_1_4`, `GolubVanLoan.Chapter05.equation_5_1_5` and
  `GolubVanLoan.Chapter05.storedQFirstColumns`.
* **Lemma 5.1.1** (generalization). The source assumes that $Q$ is orthogonal. The identity holds
  without this assumption. See `GolubVanLoan.Chapter05.lemma_5_1_1`.
* **Equation (5.1.11)** (reading). The source refers to the rotations or reflections that would
  be produced without roundoff. The theorem uses the exact transformations determined by the
  computed data at each step and assumes a local error bound for them. See
  `GolubVanLoan.Chapter05.equation_5_1_11`.

## Not formalized

* **The 2-by-2 preview of §5.1.1.** It is prose.
* **The flop counts of §5.1.** Operation counts are out of scope for the library.
* **The level-2 and level-3 discussion of §5.1.7.**
* **A rounding bound for Algorithm 5.1.2.** The source states none.
* **The Problems of §5.1.** Problems are out of scope for the library.
-/

open FloatingPoint Matrix WithLp

namespace GolubVanLoan.Chapter05

/-! ### Generic facts about index lists and the exact model -/

section Generic

/-- With unit roundoff $0$, a relative perturbation $y$ of $x$ of any order is equal to $x$. -/
theorem eq_of_isRelPert_zero {n : ℕ} {x y : ℝ} (h : IsRelPert 0 n x y) : y = x := by
  obtain ⟨θ, hθ, rfl⟩ := h
  have hθ0 : θ = 0 := abs_nonpos_iff.1 (by simpa [gamma] using hθ)
  simp [hθ0]

/-- The inner product of $x$ and $y$ accumulated along the image of a list $o$ under a map $f$ is
the inner product of $x \circ f$ and $y \circ f$ accumulated along $o$. -/
theorem dotAccum_map {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) {ι κ : Type} (f : κ → ι)
    (o : List κ) (x y : ι → ℝ) (c : ℝ) :
    dotAccum rnd (o.map f) x y c = dotAccum rnd o (x ∘ f) (y ∘ f) c := by
  simp only [dotAccum, List.foldlM_map, Function.comp_apply]

/-- Let the rounding model be idempotent, and let $l$ be a list of indices without duplicates. Every
result $s$ of the accumulation of $x^T y$ along $l$, started from $0$, is a computed inner
product (`FloatingPoint.RoundsDot`) of the restrictions $x|_l$ and $y|_l$, which are indexed by
the subtype `{i // i ∈ l}`. -/
theorem roundsDot_subtype_of_mem_run_dotAccum {fp : RoundingModel ℝ} (hfp : fp.IsIdempotent)
    {ι : Type} {l : List ι} (hl : l.Nodup) {x y : ι → ℝ} {s : ℝ}
    (h : s ∈ (dotAccum fp.round l x y 0).run) :
    RoundsDot fp (fun i : {i // i ∈ l} => x i) (fun i => y i) s := by
  have e : dotAccum fp.round l x y 0 =
      dotAccum fp.round l.attach (x ∘ Subtype.val) (y ∘ Subtype.val) 0 := by
    conv_lhs => rw [← List.attach_map_subtype_val l]
    exact dotAccum_map _ _ _ _ _ _
  rw [e] at h
  exact roundsDot_of_mem_run_dotAccum hfp (List.nodup_attach.2 hl) (List.mem_attach l) h

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ### The entries of $(I - \beta v v^T) M$ and $M (I - \beta v v^T)$ -/

variable {κ : Type*}

/-- Let $\beta \in \mathbb{R}$, let $v$ be a vector and let $M$ be a matrix whose rows have the
indices of $v$. The entries of $(I - \beta v v^T) M$ are
$$((I - \beta v v^T) M)_{iq} = M_{iq} - \beta v_i \, (v^T M(:, q)).$$
-/
theorem one_sub_smul_vecMulVec_mul_apply (β : ℝ) (v : ι → ℝ) (M : Matrix ι κ ℝ) (i : ι) (q : κ) :
    ((1 - β • vecMulVec v v : Matrix ι ι ℝ) * M) i q = M i q - β * v i * (v ⬝ᵥ fun r => M r q) := by
  change ((1 - β • vecMulVec v v) *ᵥ fun r => M r q) i = _
  rw [one_sub_smul_vecMulVec_mulVec_apply]

/-- Let $\beta \in \mathbb{R}$, let $v$ be a vector and let $M$ be a matrix whose columns have the
indices of $v$. The entries of $M (I - \beta v v^T)$ are
$$(M (I - \beta v v^T))_{rq} = M_{rq} - \beta \, (M(r, :) \, v) \, v_q.$$
-/
theorem mul_one_sub_smul_vecMulVec_apply (β : ℝ) (v : ι → ℝ) (M : Matrix κ ι ℝ) (r : κ) (q : ι) :
    (M * (1 - β • vecMulVec v v : Matrix ι ι ℝ)) r q = M r q - β * (M r ⬝ᵥ v) * v q := by
  change (M * (1 - β • vecMulVec v v : Matrix ι ι ℝ))ᵀ q r = _
  rw [transpose_mul, transpose_one_sub_smul_vecMulVec, one_sub_smul_vecMulVec_mul_apply,
    dotProduct_comm]
  change M r q - β * v q * (M r ⬝ᵥ v) = _
  ring

/-- Row $r$ of $M (I - \beta v v^T)$ is $(I - \beta v v^T)$ applied to row $r$ of $M$, because
$I - \beta v v^T$ is symmetric. -/
theorem mul_one_sub_smul_vecMulVec_apply_eq_mulVec (β : ℝ) (v : ι → ℝ) (M : Matrix κ ι ℝ)
    (r : κ) (q : ι) :
    (M * (1 - β • vecMulVec v v : Matrix ι ι ℝ)) r q = ((1 - β • vecMulVec v v) *ᵥ M r) q := by
  rw [mul_one_sub_smul_vecMulVec_apply, one_sub_smul_vecMulVec_mulVec_apply, dotProduct_comm]
  ring

/-- Let $v$ vanish outside a set $S$ of indices. Then $(I - \beta v v^T) M$ agrees with $M$ in every
row $i \notin S$.

**Generalization.** Extends untouched rows to arbitrary support.
-/
theorem one_sub_smul_vecMulVec_mul_apply_of_notMem {v : ι → ℝ} {S : ι → Prop}
    (hv : ∀ l, ¬ S l → v l = 0) (β : ℝ) (M : Matrix ι κ ℝ) {i : ι} (hi : ¬ S i) (q : κ) :
    ((1 - β • vecMulVec v v : Matrix ι ι ℝ) * M) i q = M i q := by
  rw [one_sub_smul_vecMulVec_mul_apply, hv i hi, mul_zero, zero_mul, sub_zero]

/-- Let $v$ vanish outside a set $S$ of indices. Then $M (I - \beta v v^T)$ agrees with $M$ in every
column $q \notin S$.

**Generalization.** Extends untouched columns to arbitrary support.
-/
theorem mul_one_sub_smul_vecMulVec_apply_of_notMem {v : ι → ℝ} {S : ι → Prop}
    (hv : ∀ l, ¬ S l → v l = 0) (β : ℝ) (M : Matrix κ ι ℝ) (r : κ) {q : ι} (hq : ¬ S q) :
    (M * (1 - β • vecMulVec v v : Matrix ι ι ℝ)) r q = M r q := by
  rw [mul_one_sub_smul_vecMulVec_apply, hv q hq, mul_zero, sub_zero]

/-- Let $v$ vanish outside a set $S$ of indices. If column $q$ of $M$ vanishes on $S$, then column
$q$ of $(I - \beta v v^T) M$ is column $q$ of $M$.

**Reading.** Preserves a column zero on an arbitrary support set.
-/
theorem one_sub_smul_vecMulVec_mul_apply_of_forall {v : ι → ℝ} {S : ι → Prop}
    (hv : ∀ l, ¬ S l → v l = 0) (β : ℝ) (M : Matrix ι κ ℝ) {q : κ} (hM : ∀ l, S l → M l q = 0)
    (i : ι) : ((1 - β • vecMulVec v v : Matrix ι ι ℝ) * M) i q = M i q := by
  have h0 : (v ⬝ᵥ fun r => M r q) = 0 := Finset.sum_eq_zero fun l _ => by
    by_cases hl : S l
    · simp [hM l hl]
    · simp [hv l hl]
  rw [one_sub_smul_vecMulVec_mul_apply, h0, mul_zero, sub_zero]

/-- Let $v$ vanish outside a set $S$ of indices. If row $r$ of $M$ vanishes on $S$, then row $r$ of
$M (I - \beta v v^T)$ is row $r$ of $M$.

**Reading.** Right-update analogue for a row zero on arbitrary support.
-/
theorem mul_one_sub_smul_vecMulVec_apply_of_forall {v : ι → ℝ} {S : ι → Prop}
    (hv : ∀ l, ¬ S l → v l = 0) (β : ℝ) (M : Matrix κ ι ℝ) {r : κ} (hM : ∀ l, S l → M r l = 0)
    (q : ι) : (M * (1 - β • vecMulVec v v : Matrix ι ι ℝ)) r q = M r q := by
  have h0 : M r ⬝ᵥ v = 0 := Finset.sum_eq_zero fun l _ => by
    by_cases hl : S l
    · simp [hM l hl]
    · simp [hv l hl]
  rw [mul_one_sub_smul_vecMulVec_apply, h0, mul_zero, zero_mul, sub_zero]

/-- Let $v$ vanish outside a set $S$ of indices, and let the vector $u$ agree with column $q$ of $M$
on $S$. Then $((I - \beta v v^T) M)_{iq} = ((I - \beta v v^T) u)_i$ for every $i \in S$: the
rows in $S$ of the product depend on column $q$ of $M$ only through its entries in $S$.

**Reading.** Equality with a vector agreeing on the arbitrary active row set.
-/
theorem one_sub_smul_vecMulVec_mul_apply_eq_mulVec {v : ι → ℝ} {S : ι → Prop}
    (hv : ∀ l, ¬ S l → v l = 0) (β : ℝ) (M : Matrix ι κ ℝ) (u : ι → ℝ) {q : κ}
    (hMu : ∀ l, S l → M l q = u l) {i : ι} (hi : S i) :
    ((1 - β • vecMulVec v v : Matrix ι ι ℝ) * M) i q = ((1 - β • vecMulVec v v) *ᵥ u) i := by
  have h : (v ⬝ᵥ fun r => M r q) = v ⬝ᵥ u := Finset.sum_congr rfl fun l _ => by
    by_cases hl : S l
    · simp [hMu l hl]
    · simp [hv l hl]
  rw [one_sub_smul_vecMulVec_mul_apply, one_sub_smul_vecMulVec_mulVec_apply, hMu i hi, h]

/-! ### Selecting columns of the identity -/

/-- For a list $l = [l_0, \dots, l_{k-1}]$ of indices, `selCols l` is the matrix
$E = [e_{l_0} \cdots e_{l_{k-1}}]$ whose column $a$ is the unit vector $e_{l_a}$. -/
def selCols (l : List ι) : Matrix ι (Fin l.length) ℝ :=
  of fun r a => if l.get a = r then 1 else 0

omit [Fintype ι] in
/-- If the list $l$ has no duplicates, row $l_a$ of $E N$ is row $a$ of $N$, where $E$ is
`GolubVanLoan.Chapter05.selCols l`. -/
theorem selCols_mul_apply_get {l : List ι} (hl : l.Nodup) (N : Matrix (Fin l.length) κ ℝ)
    (a : Fin l.length) (c : κ) : (selCols l * N) (l.get a) c = N a c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · simp [selCols]
  · intro a' _ ha'
    simp only [selCols, of_apply, ite_mul, one_mul, zero_mul, ite_eq_right_iff]
    exact fun h => absurd (List.nodup_iff_injective_get.1 hl h) ha'
  · simp

omit [Fintype ι] in
/-- Every row of $E N$ whose index is not in the list $l$ is zero, where $E$ is
`GolubVanLoan.Chapter05.selCols l`. -/
theorem selCols_mul_apply_of_notMem {l : List ι} (N : Matrix (Fin l.length) κ ℝ) {r : ι}
    (hr : r ∉ l) (c : κ) : (selCols l * N) r c = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  have : l.get a ≠ r := fun h => hr (h ▸ List.get_mem l a)
  simp only [selCols, of_apply, this, ite_false, zero_mul]

omit [Fintype ι] in
/-- If the list $l$ has no duplicates, column $l_e$ of $N E^T$ is column $e$ of $N$, where $E$ is
`GolubVanLoan.Chapter05.selCols l`. -/
theorem mul_selCols_transpose_apply_get {l : List ι} (hl : l.Nodup)
    (N : Matrix κ (Fin l.length) ℝ) (r : κ) (e : Fin l.length) :
    (N * (selCols l)ᵀ) r (l.get e) = N r e := by
  rw [Matrix.mul_apply, Finset.sum_eq_single e]
  · simp [selCols]
  · intro e' _ he'
    simp only [transpose_apply, selCols, of_apply, mul_ite, mul_one, mul_zero, ite_eq_right_iff]
    exact fun h => absurd (List.nodup_iff_injective_get.1 hl h) he'
  · simp

omit [Fintype ι] in
/-- Every column of $N E^T$ whose index is not in the list $l$ is zero, where $E$ is
`GolubVanLoan.Chapter05.selCols l`. -/
theorem mul_selCols_transpose_apply_of_notMem {l : List ι} (N : Matrix κ (Fin l.length) ℝ)
    (r : κ) {c : ι} (hc : c ∉ l) : (N * (selCols l)ᵀ) r c = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun e _ => ?_
  have : l.get e ≠ c := fun h => hc (h ▸ List.get_mem l e)
  simp only [transpose_apply, selCols, of_apply, this, ite_false, mul_zero]

/-- Row $a$ of $E^T A$ is row $l_a$ of $A$, where $E$ is `GolubVanLoan.Chapter05.selCols l`. -/
theorem selCols_transpose_mul_apply (l : List ι) (A : Matrix ι κ ℝ) (a : Fin l.length) (c : κ) :
    ((selCols l)ᵀ * A) a c = A (l.get a) c := by
  simp [Matrix.mul_apply, selCols]

/-- Column $a$ of $A E$ is column $l_a$ of $A$, where $E$ is `GolubVanLoan.Chapter05.selCols l`. -/
theorem mul_selCols_apply (l : List ι) (A : Matrix κ ι ℝ) (r : κ) (a : Fin l.length) :
    (A * selCols l) r a = A r (l.get a) := by
  simp [Matrix.mul_apply, selCols]

end Generic

/-! ### Loops that rewrite one column, or one row, per step -/

section Loops

variable {m n : ℕ}

/-- A loop that rewrites one column per step. For each column index $q$, let $g_q$ be a
nondeterministic program on vectors of $\mathbb{R}^m$, and let `cols` be a list of column
indices without duplicates. Consider the loop that starts from $A \in \mathbb{R}^{m \times n}$
and, for each $q$ in `cols` in turn, replaces column $q$ by a result of $g_q$ applied to its
current value. A matrix $B$ is a result of this loop if and only if $B$ agrees with $A$ in every
column that is not in `cols`, and for every $q$ in `cols` column $q$ of $B$ is a result of $g_q$
applied to column $q$ of $A$.

This is the column form of `SetM.mem_run_foldlM_update_of_nodup`. -/
theorem mem_run_foldlM_updateCol_of_nodup (g : Fin n → (Fin m → ℝ) → SetM (Fin m → ℝ))
    {cols : List (Fin n)} (hcols : cols.Nodup) (A B : Matrix (Fin m) (Fin n) ℝ) :
    B ∈ (cols.foldlM (fun (A : Matrix (Fin m) (Fin n) ℝ) q => do
        let c ← g q (fun i => A i q); pure (A.updateCol q c)) A).run ↔
      (∀ q, q ∉ cols → ∀ i, B i q = A i q) ∧
        ∀ q ∈ cols, (fun i => B i q) ∈ (g q (fun i => A i q)).run := by
  -- the loop is the transpose of the loop on the columns of `Aᵀ`, updated by `Function.update`
  have key : ∀ (l : List (Fin n)) (D₀ : Matrix (Fin m) (Fin n) ℝ),
      l.foldlM (fun (A : Matrix (Fin m) (Fin n) ℝ) q => do
          let c ← g q (fun i => A i q); pure (A.updateCol q c)) D₀
        = (fun D : Fin n → Fin m → ℝ => (Matrix.of D)ᵀ) <$>
          l.foldlM (fun (D : Fin n → Fin m → ℝ) q => do
            let c ← g q (D q); pure (Function.update D q c)) (fun q i => D₀ i q) := by
    intro l
    induction l with
    | nil => intro D₀; simp only [List.foldlM_nil, map_pure]; rfl
    | cons a l ih =>
      intro D₀
      simp only [List.foldlM_cons, bind_assoc, pure_bind, map_bind]
      refine congrArg _ (funext fun c => ?_)
      rw [ih]
      congr 2
      funext q i
      simp only [updateCol_apply, Function.update_apply]
      split_ifs <;> rfl
  rw [key, SetM.mem_run_map]
  have h := SetM.mem_run_foldlM_update_of_nodup (fun q b (_ : Fin n → Fin m → ℝ) => g q b) cols
    hcols (fun _ _ _ _ _ _ => rfl) (fun q i => A i q)
  constructor
  · rintro ⟨D, hD, rfl⟩
    obtain ⟨hout, hin⟩ := (h D).1 hD
    exact ⟨fun q hq i => congrFun (hout q hq) i, fun q hq => hin q hq⟩
  · rintro ⟨hout, hin⟩
    refine ⟨fun q i => B i q, (h _).2 ⟨fun q hq => funext fun i => hout q hq i, hin⟩, ?_⟩
    rfl

/-- A loop that rewrites one row per step. For each row index $r$, let $g_r$ be a nondeterministic
program on vectors of $\mathbb{R}^n$, and let `rows` be a list of row indices without
duplicates. A matrix $B$ is a result of the loop that starts from $A$ and, for each $r$ in
`rows` in turn, replaces row $r$ by a result of $g_r$ applied to its current value, if and only
if $B$ agrees with $A$ in every row that is not in `rows`, and for every $r$ in `rows` row $r$
of $B$ is a result of $g_r$ applied to row $r$ of $A$.

This is `SetM.mem_run_foldlM_update_of_nodup` applied to the rows. -/
theorem mem_run_foldlM_updateRow_of_nodup (g : Fin m → (Fin n → ℝ) → SetM (Fin n → ℝ))
    {rows : List (Fin m)} (hrows : rows.Nodup) (A B : Matrix (Fin m) (Fin n) ℝ) :
    B ∈ (rows.foldlM (fun (A : Matrix (Fin m) (Fin n) ℝ) r => do
        let x ← g r (A r); pure (A.updateRow r x)) A).run ↔
      (∀ r, r ∉ rows → B r = A r) ∧ ∀ r ∈ rows, B r ∈ (g r (A r)).run :=
  SetM.mem_run_foldlM_update_of_nodup (fun r b (_ : Fin m → Fin n → ℝ) => g r b) rows hrows
    (fun _ _ _ _ _ _ => rfl) A B

end Loops

/-! ### §5.1.2 Householder reflections -/

section Reflections

variable {m : ℕ}

/-- **Equation (5.1.1)** of [golub2013matrix] (Householder reflection). For $v \in \mathbb{R}^m$,
the **Householder matrix** of $v$ is
$$P = I - \beta v v^T, \qquad \beta = \frac{2}{v^T v},$$
and $v$ is its **Householder vector**. In the words of the source, if a vector $x$ is multiplied
by $P$, then it is reflected in the hyperplane $\operatorname{span}\{v\}^\perp$.

For $v = 0$ the definition gives $P = I$, because $2 / 0 = 0$ in Lean. The matrix is the
backbone's `Matrix.reflector v` (`GolubVanLoan.Chapter05.householderMatrix_eq_reflector`).

**Totalization.** The source assumes $v \ne 0$. Since division by zero is total in Lean,
`householderMatrix 0` is the identity.

**Generalization.** Extends formula to v=0 with identity result.
-/
noncomputable def householderMatrix (v : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  1 - (2 / (v ⬝ᵥ v)) • vecMulVec v v

/-- The Householder matrix of $v$ is the backbone's reflector `Matrix.reflector v`, which is
$I - (2 / v^T v) v v^T$.

**Reading.** Backbone equivalence includes the zero-vector identity.
-/
theorem householderMatrix_eq_reflector (v : Fin m → ℝ) : householderMatrix v = reflector v :=
  (reflector_eq_one_sub_smul_vecMulVec v).symm

/-- **Section 5.1.2** of [golub2013matrix], symmetry. For every $v \in \mathbb{R}^m$, the
Householder matrix $P = I - (2 / v^T v) v v^T$ is symmetric: $P^T = P$.

**Generalization.** Symmetry extends to the zero-vector identity.
-/
theorem householderMatrix_isSymm (v : Fin m → ℝ) : (householderMatrix v).IsSymm :=
  transpose_one_sub_smul_vecMulVec _ _

/-- **Section 5.1.2** of [golub2013matrix], orthogonality. For every $v \in \mathbb{R}^m$, the
Householder matrix $P = I - (2 / v^T v) v v^T$ is orthogonal. This includes $v = 0$, where
$P = I$.

**Generalization.** Orthogonality extends to the zero-vector identity.
-/
theorem householderMatrix_mem_orthogonalGroup (v : Fin m → ℝ) :
    householderMatrix v ∈ orthogonalGroup (Fin m) ℝ := by
  rw [householderMatrix_eq_reflector]
  exact reflector_mem_orthogonalGroup v

/-- **Equation (5.1.2)** of [golub2013matrix]. Let $m \ge 1$ and $x \in \mathbb{R}^m$, let
$\alpha = \|x\|_2$ or $\alpha = -\|x\|_2$, and let $v = x + \alpha e_1 \neq 0$. Then
$$P x = \Bigl(I - \frac{2 v v^T}{v^T v}\Bigr) x = -\alpha e_1.$$
In the notation of the source: $v = x \pm \|x\|_2 e_1$ implies $P x = \mp \|x\|_2 e_1$.

Here $m = k + 1$, $e_1$ is `Pi.single 0 1`, and $P$ is
`GolubVanLoan.Chapter05.householderMatrix v`.

**Reading.** The nonzero-vector hypothesis in the definition of a reflection is imposed on
$x+\alpha e_1$ for the selected sign. -/
theorem equation_5_1_2 {k : ℕ} (x : Fin (k + 1) → ℝ) {α : ℝ}
    (hα : α = ‖(toLp 2 x : EuclideanSpace ℝ (Fin (k + 1)))‖ ∨
      α = -‖(toLp 2 x : EuclideanSpace ℝ (Fin (k + 1)))‖)
    (hv : x + α • Pi.single 0 1 ≠ 0) :
    householderMatrix (x + α • Pi.single 0 1) *ᵥ x = -α • Pi.single 0 1 := by
  rw [householderMatrix_eq_reflector]
  refine reflector_mulVec_eq_of_sq ?_ (by simp) hv
  simp only [star_trivial, RCLike.ofReal_real_eq_id, id]
  rcases hα with rfl | rfl <;> ring

/-- **Section 5.1.3** of [golub2013matrix] (Parlett's formula). Let $m \ge 1$ and
$x \in \mathbb{R}^m$ with $x_1 + \|x\|_2 \neq 0$. Then
$$x_1 - \|x\|_2 = \frac{-(x_2^2 + \cdots + x_m^2)}{x_1 + \|x\|_2}.$$
For $x_1 > 0$, the right-hand side computes $v_1 = x_1 - \|x\|_2$ without cancellation.

Here $m = k + 1$, $x_1$ is `x 0`, and the sum runs over `Fin k` through `Fin.succ`. -/
theorem parlett_formula {k : ℕ} (x : Fin (k + 1) → ℝ)
    (h : x 0 + ‖(toLp 2 x : EuclideanSpace ℝ (Fin (k + 1)))‖ ≠ 0) :
    x 0 - ‖(toLp 2 x : EuclideanSpace ℝ (Fin (k + 1)))‖ =
      -(∑ i : Fin k, x i.succ ^ 2) / (x 0 + ‖(toLp 2 x : EuclideanSpace ℝ (Fin (k + 1)))‖) := by
  have hN : ‖(toLp 2 x : EuclideanSpace ℝ (Fin (k + 1)))‖ ^ 2 =
      x 0 ^ 2 + ∑ i : Fin k, x i.succ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
    simp
  rw [eq_div_iff h]
  linear_combination -hN

end Reflections

/-! ### §5.1.3 Computing the Householder vector -/

section House

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) {m : ℕ}

/-- The pivot entry $v_1$ of Algorithm 5.1.1, computed from $x_1$, $\mu$ and $\sigma$ with every
operation rounded: $\mathrm{fl}(x_1 - \mu)$ if $x_1 \le 0$, and Parlett's form
$\mathrm{fl}(-\sigma / \mathrm{fl}(x_1 + \mu))$ if $x_1 > 0$. -/
noncomputable def parlettPivot (x₁ μ σ : ℝ) : M ℝ :=
  if x₁ ≤ 0 then rnd (x₁ - μ) else do rnd (-σ / (← rnd (x₁ + μ)))

/-- **Algorithm 5.1.1** of [golub2013matrix] (`house`), on the entries of $x \in \mathbb{R}^m$
listed by an index list $o$. The first index $p$ of $o$ plays the role of the source's $x(1)$,
and the other indices $t$ of $o$ play the role of $x(2{:}m)$. The program computes
```
σ = x(2:m)ᵀ x(2:m),  v = [1; x(2:m)]
if σ = 0 and x(1) >= 0:      β = 0
elseif σ = 0 & x(1) < 0:     β = 2          (the source prints -2)
else
    μ = √(x(1)² + σ)
    if x(1) <= 0:  v(1) = x(1) - μ
    else           v(1) = -σ/(x(1) + μ)
    β = 2 v(1)² / (σ + v(1)²)
    v = v / v(1)
```
with every arithmetic result rounded. The sum $\sigma$ is accumulated from $0$ as in Algorithm
1.1.1, and $v(1)^2$ is computed once. The output $v$ is $1$ at $p$; at each index $i$ of $t$ it is
$\mathrm{fl}(x_i / v(1))$, or $x_i$ in the two branches with $\sigma = 0$; and it is $0$ at every
index that is not in $o$. For the empty list the output is $(0, 0)$.

**Correction.** In the branch $\sigma = 0$, $x(1) < 0$ the source sets $\beta = -2$. Then
$I - \beta v v^T = I + 2 e_1 e_1^T$ is not orthogonal. The program sets $\beta = 2$, for which
$I - \beta v v^T = I - 2 e_1 e_1^T$ is orthogonal and maps $x = x_1 e_1$ to $|x_1| e_1$.

This is the form in which later algorithms apply `house` to a block such as $A(j{:}m, j)$: the
full vector together with the list of the active indices. The sum $\sigma$ is
`FloatingPoint.dotAccum` over $t$. The program is generic in the monad `M` and the rounding hook
`rnd`. -/
noncomputable def houseOn (o : List (Fin m)) (x : Fin m → ℝ) : M ((Fin m → ℝ) × ℝ) :=
  match o with
  | [] => pure (0, 0)
  | p :: t => do
    let σ ← dotAccum rnd t x x 0
    let v : Fin m → ℝ := fun i => if i = p then 1 else if i ∈ t then x i else 0
    if σ = 0 ∧ 0 ≤ x p then pure (v, 0)
    else if σ = 0 ∧ x p < 0 then pure (v, 2)
    else do
      let μ ← rnd √(← rnd ((← rnd (x p * x p)) + σ))
      let v₁ ← parlettPivot rnd (x p) μ σ
      let q ← rnd (v₁ * v₁)
      let β ← rnd ((← rnd (2 * q)) / (← rnd (σ + q)))
      let w ← t.foldlM (fun (w : Fin m → ℝ) i => do
        let b ← rnd (x i / v₁)
        pure (Function.update w i b)) v
      pure (w, β)

/-- **Algorithm 5.1.1** of [golub2013matrix] (`house`). Given $x \in \mathbb{R}^m$ with $m \ge 1$,
the algorithm computes $v \in \mathbb{R}^m$ with $v(1) = 1$ and $\beta \in \mathbb{R}$ such that
$P = I_m - \beta v v^T$ is orthogonal and $P x = \|x\|_2 e_1$. It is
`GolubVanLoan.Chapter05.houseOn` on the full index list, which lists the program.

**Correction.** In the branch $\sigma = 0$, $x(1) < 0$ the source sets $\beta = -2$, which makes
$P = I + 2 e_1 e_1^T$ not orthogonal. The program sets $\beta = 2$.

Here $m = k + 1$, and the index list is `List.finRange (k + 1)`. -/
noncomputable def algorithm_5_1_1 {k : ℕ} (x : Fin (k + 1) → ℝ) :
    M ((Fin (k + 1) → ℝ) × ℝ) :=
  houseOn rnd (List.finRange (k + 1)) x

end House

/-! ### Algorithm 5.1.1: rounding bridge, exact semantics and rounding bound -/

section HouseRuns

variable {m : ℕ}

/-- For a list $l$ without duplicates, the subtype `{i // i ∈ l}` of the listed indices has $|l|$
elements. -/
theorem card_subtype_mem_of_nodup {ι : Type} [DecidableEq ι] {l : List ι} (hl : l.Nodup) :
    Fintype.card {i // i ∈ l} = l.length := by
  rw [Fintype.card_of_subtype l.toFinset (fun x => List.mem_toFinset),
    List.toFinset_card_of_nodup hl]

/-- For $p \notin t$, the indices of the list $p :: t$ other than $p$ correspond to the indices of
$t$. -/
private def consTailEquiv {p : Fin m} {t : List (Fin m)} (hp : p ∉ t) :
    {j : {i // i ∈ p :: t} // j ≠ ⟨p, List.mem_cons_self⟩} ≃ {i // i ∈ t} where
  toFun j := ⟨j.1.1, (List.mem_cons.1 j.1.2).resolve_left fun h => j.2 (Subtype.ext h)⟩
  invFun i := ⟨⟨i.1, List.mem_cons_of_mem _ i.2⟩, fun h => hp (by
    have h' : i.1 = p := congrArg Subtype.val h
    exact h' ▸ i.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Algorithm 5.1.1** of [golub2013matrix] on an index list, rounding bridge. Let the rounding
model be idempotent, and let $o$ be a nonempty list of indices of $\mathbb{R}^m$ without
duplicates, with first entry $p$. Every result $(\hat v, \hat\beta)$ of Algorithm 5.1.1 on the
entries of $x$ listed by $o$, in the rounding model, satisfies two conditions. First,
$\hat v_i = 0$ for every $i$ that is not in $o$. Second, $x|_o$, $\hat v|_o$ and $\hat\beta$
satisfy the relation of a computed Householder vector with Parlett's formula and pivot $p$: the
tail sum $\hat\sigma$ is a computed inner product, $\hat v_p = 1$, and the other quantities are
rounded results of the steps of the algorithm in the branch that $\hat\sigma$ and $x_p$ select.

The relation is `FloatingPoint.RoundsHouseholderVectorParlett` on the subtype `{i // i ∈ o}`.
The tail sum is a `FloatingPoint.RoundsDot` because the accumulation starts from $0$; this step
uses the idempotence of the model. -/
theorem houseOn_rounds {fp : RoundingModel ℝ} (hfp : fp.IsIdempotent) {o : List (Fin m)}
    (ho : o.Nodup) (hne : o ≠ []) (x : Fin m → ℝ) {vβ : (Fin m → ℝ) × ℝ}
    (h : vβ ∈ (houseOn fp.round o x).run) :
    (∀ i, i ∉ o → vβ.1 i = 0) ∧
      RoundsHouseholderVectorParlett fp (fun i : {i // i ∈ o} => x i)
        ⟨o.head hne, List.head_mem hne⟩ (fun i => vβ.1 i) vβ.2 := by
  obtain ⟨p, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hp : p ∉ t := (List.nodup_cons.1 ho).1
  have ht : t.Nodup := (List.nodup_cons.1 ho).2
  simp only [houseOn, SetM.mem_run_bind] at h
  obtain ⟨σ, hσ, h⟩ := h
  have hdot : RoundsDot fp
      (fun j : {j : {i // i ∈ p :: t} // j ≠ ⟨p, List.mem_cons_self⟩} => x j.1.1)
      (fun j => x j.1.1) σ :=
    (roundsDot_comp_equiv_iff (consTailEquiv hp)).2
      (roundsDot_subtype_of_mem_run_dotAccum hfp ht hσ)
  set v : Fin m → ℝ := fun i => if i = p then 1 else if i ∈ t then x i else 0 with hv
  have hvp : v p = 1 := by simp [hv]
  have hvt : ∀ i ∈ t, v i = x i := fun i hi => by
    have hip : i ≠ p := fun e => hp (e ▸ hi)
    simp [hv, hi, hip]
  have hvout : ∀ i, i ∉ p :: t → v i = 0 := fun i hi => by
    simp only [List.mem_cons, not_or] at hi
    simp [hv, hi.1, hi.2]
  -- the entries of the subtype other than the pivot are the tail
  have htail : ∀ j : {i // i ∈ p :: t}, j ≠ ⟨p, List.mem_cons_self⟩ → j.1 ∈ t := fun j hj =>
    (List.mem_cons.1 j.2).resolve_left fun e => hj (Subtype.ext e)
  split_ifs at h with h1 h2
  · rw [SetM.mem_run_pure] at h
    subst h
    exact ⟨hvout, σ, hdot, hvp, Or.inl ⟨h1.1, h1.2, rfl, fun j hj => hvt j (htail j hj)⟩⟩
  · rw [SetM.mem_run_pure] at h
    subst h
    exact ⟨hvout, σ, hdot, hvp, Or.inr (Or.inl ⟨h2.1, h2.2, rfl,
      fun j hj => hvt j (htail j hj)⟩)⟩
  · have hσ0 : σ ≠ 0 := fun e => by
      rcases le_or_gt 0 (x p) with hx | hx
      · exact h1 ⟨e, hx⟩
      · exact h2 ⟨e, hx⟩
    simp only [SetM.mem_run_bind, RoundingModel.mem_run_round, SetM.mem_run_pure] at h
    obtain ⟨a, ha, b, hb, μ, hμ, v₁, hv₁, q, hq, c, hc, d, hd, β, hβ, w, hw, rfl⟩ := h
    have hw' := (SetM.mem_run_foldlM_update_of_nodup
      (fun i _ (_ : Fin m → ℝ) => fp.round (x i / v₁)) t ht (fun _ _ _ _ _ _ => rfl) v w).1 hw
    obtain ⟨hwout, hwin⟩ := hw'
    have hwp : w p = 1 := by rw [hwout p hp, hvp]
    refine ⟨fun i hi => ?_, σ, hdot, hwp, Or.inr (Or.inr ⟨hσ0, a, b, μ, v₁, q, c, d, ha, hb, hμ,
      ?_, hq, hc, hd, hβ, fun j hj => hwin j (htail j hj)⟩)⟩
    · have hit : i ∉ t := fun h => hi (List.mem_cons_of_mem _ h)
      change w i = 0
      rw [hwout i hit, hvout i hi]
    · unfold parlettPivot at hv₁
      by_cases hxp : x p ≤ 0
      · simp only [hxp, ↓reduceIte] at hv₁
        exact Or.inl ⟨hxp, hv₁⟩
      · simp only [hxp, ↓reduceIte, SetM.mem_run_bind] at hv₁
        exact Or.inr ⟨lt_of_not_ge hxp, hv₁⟩

/-- The exact output of `GolubVanLoan.Chapter05.houseOn` is a result of the program in the exact
rounding model. -/
private theorem houseOn_mem_exact (o : List (Fin m)) (x : Fin m → ℝ) :
    Id.run (houseOn pure o x) ∈ (houseOn (RoundingModel.exact ℝ).round o x).run := by
  rw [RoundingModel.round_exact]
  cases o with
  | nil => rfl
  | cons p t =>
    simp only [houseOn, parlettPivot, dotAccum_pure, pure_bind, List.foldlM_pure]
    split_ifs <;> simp only [pure_bind, SetM.mem_run_pure] <;> rfl

/-- Reflector data are invariant under a change of index type. Let $e : \kappa \simeq \iota$ be a
bijection. If $(\hat v \circ e, \hat\beta)$ are reflector data of order $K$ for $x \circ e$ with
pivot $e^{-1}(i)$ and target $c$, then $(\hat v, \hat\beta)$ are reflector data of order $K$ for
$x$ with pivot $i$ and target $c$ (`FloatingPoint.IsReflectorPert`). -/
theorem IsReflectorPert.of_comp_equiv {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : κ ≃ ι) {u : ℝ} {K : ℕ} {x : ι → ℝ} {i : ι} {c : ℝ} {vhat : ι → ℝ}
    {βhat : ℝ} (h : IsReflectorPert u K (x ∘ e) (e.symm i) c (vhat ∘ e) βhat) :
    IsReflectorPert u K x i c vhat βhat := by
  obtain ⟨v, β, hO, hmul, hβv, hβ, hv⟩ := h
  have hdot : ∀ y : ι → ℝ, (v ∘ e.symm) ⬝ᵥ y = v ⬝ᵥ (y ∘ e) := fun y => by
    rw [dotProduct_comm, dotProduct_comp_equiv_symm, dotProduct_comm]
  have hvv : (v ∘ e.symm) ⬝ᵥ (v ∘ e.symm) = v ⬝ᵥ v := by
    rw [hdot]; congr 1; ext j; simp
  refine ⟨v ∘ e.symm, β, ?_, ?_, by rwa [hvv], hβ, fun j => by simpa using hv (e.symm j)⟩
  · -- orthogonality is `β (β vᵀv - 2) = 0` unless `v = 0`
    by_cases hv0 : v = 0
    · subst hv0
      have : (0 : κ → ℝ) ∘ e.symm = 0 := rfl
      rw [this, vecMulVec_zero, smul_zero, sub_zero]
      exact one_mem _
    · obtain ⟨p, hp⟩ := Function.ne_iff.1 hv0
      refine one_sub_smul_vecMulVec_mem_orthogonalGroup ?_
      rw [hvv]
      exact mul_mul_dotProduct_sub_two_eq_zero_of_mem_orthogonalGroup hp hO
  · funext j
    have hj := congrFun hmul (e.symm j)
    rw [one_sub_smul_vecMulVec_mulVec_apply] at hj ⊢
    rw [hdot]
    simp only [Function.comp_apply, Equiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul] at hj ⊢
    rw [hj]
    congr 1
    by_cases hji : j = i
    · subst hji; simp
    · rw [Pi.single_eq_of_ne hji, Pi.single_eq_of_ne (fun h => hji (e.symm.injective h))]

/-- **Algorithm 5.1.1** of [golub2013matrix] on an index list, exact semantics. Let $o$ be a
nonempty list of indices of $\mathbb{R}^m$ without duplicates, with first entry $p$, and let
$x \in \mathbb{R}^m$. In exact arithmetic, the output $(v, \beta)$ of Algorithm 5.1.1 on the
entries of $x$ listed by $o$ satisfies the following: $v_p = 1$; $v_i = 0$ for every $i$ that is
not in $o$; $\beta = 0$ or $\beta v^T v = 2$, so that $I - \beta v v^T$ is $I$ or the
Householder matrix of $v$; $I - \beta v v^T$ is orthogonal; and $(I - \beta v v^T) x = y$ with
$$y_i = \begin{cases} \|x|_o\|_2 & \text{if } i = p, \\ 0 & \text{if } i \in o,\ i \neq p, \\
  x_i & \text{if } i \notin o. \end{cases}$$
The reflection acts only on the coordinates listed by $o$.

The exact output is `Id.run (houseOn pure o x)`. The proof reads it off
`GolubVanLoan.Chapter05.houseOn_rounds` at the exact model.

**Correction.** Indexed and zero-padded exact semantics, with corrected coefficient and unchanged
inactive entries.
-/
theorem houseOn_spec {o : List (Fin m)} (ho : o.Nodup) (hne : o ≠ []) (x : Fin m → ℝ) :
    (Id.run (houseOn pure o x)).1 (o.head hne) = 1 ∧
      (∀ i, i ∉ o → (Id.run (houseOn pure o x)).1 i = 0) ∧
      ((Id.run (houseOn pure o x)).2 = 0 ∨
        (Id.run (houseOn pure o x)).2 *
          ((Id.run (houseOn pure o x)).1 ⬝ᵥ (Id.run (houseOn pure o x)).1) = 2) ∧
      (1 - (Id.run (houseOn pure o x)).2 •
        vecMulVec (Id.run (houseOn pure o x)).1 (Id.run (houseOn pure o x)).1) ∈
          orthogonalGroup (Fin m) ℝ ∧
      (1 - (Id.run (houseOn pure o x)).2 •
        vecMulVec (Id.run (houseOn pure o x)).1 (Id.run (houseOn pure o x)).1) *ᵥ x =
          fun i => if i = o.head hne then
              ‖(toLp 2 (fun j : {j // j ∈ o} => x j) : EuclideanSpace ℝ {j // j ∈ o})‖
            else if i ∈ o then 0 else x i := by
  obtain ⟨hout, hrel⟩ := houseOn_rounds RoundingModel.isIdempotent_exact ho hne x
    (houseOn_mem_exact o x)
  generalize Id.run (houseOn pure o x) = vβ at hout hrel ⊢
  obtain ⟨hvp, v, β, hO, hmul, -, hβ, hv⟩ := hrel.isReflectorPert (by simp)
  simp only [RoundingModel.exact_u] at hβ hv
  have hβ' : vβ.2 = β := eq_of_isRelPert_zero hβ
  have hv' : (fun i : {i // i ∈ o} => vβ.1 i) = v := funext fun j => eq_of_isRelPert_zero (hv j)
  subst hβ' hv'
  have hdot : vβ.1 ⬝ᵥ vβ.1 =
      (fun i : {i // i ∈ o} => vβ.1 i) ⬝ᵥ (fun i : {i // i ∈ o} => vβ.1 i) :=
    dotProduct_eq_dotProduct_subtype hout _
  have hc := mul_mul_dotProduct_sub_two_eq_zero_of_mem_orthogonalGroup
    (v := fun i : {i // i ∈ o} => vβ.1 i)
    (p := ⟨o.head hne, List.head_mem hne⟩) (by rw [hvp]; exact one_ne_zero) hO
  rw [← hdot] at hc
  refine ⟨hvp, hout, ?_, one_sub_smul_vecMulVec_mem_orthogonalGroup hc, ?_⟩
  · rcases mul_eq_zero.1 hc with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  · funext i
    rw [one_sub_smul_vecMulVec_mulVec_apply_subtype hout]
    by_cases hio : i ∈ o
    · simp only [hio, ↓reduceDIte]
      rw [hmul]
      by_cases hih : i = o.head hne
      · subst hih
        simp
      · simp [hih]
    · have hih : i ≠ o.head hne := fun e => hio (e ▸ List.head_mem hne)
      simp [hio, hih]

/-- **Section 5.1.5** of [golub2013matrix], accuracy of the computed Householder vector, on an index
list. Let the rounding model be idempotent, let $o$ be a nonempty list of indices of
$\mathbb{R}^m$ without duplicates, with first entry $p$ and length $n$, and let $K = 18 n + 31$
with $K u < 1$. Every result $(\hat v, \hat\beta)$ of Algorithm 5.1.1 on the entries of $x$
listed by $o$, in the rounding model, vanishes outside $o$, and on the indices of $o$ it is
reflector data of order $K$ for $x|_o$ with pivot $p$ and target $\|x|_o\|_2$. That is, there
are exact $v$ and $\beta$, indexed by the entries of $o$, such that $I - \beta v v^T$ is
orthogonal, $(I - \beta v v^T)\, x|_o = \|x|_o\|_2\, e_p$, $|\beta| v^T v \le 2$, and
$$\hat\beta = \beta (1 + \theta), \qquad \hat v_i = v_i (1 + \theta_i), \qquad |\theta|,
  |\theta_i| \le \gamma_K.$$

The source says that `house` produces a vector $\hat v$ that is very close to the exact $v$,
with a relative error of order $O(u)$. The formal statement gives the bound $\gamma_K$. The
relation is `FloatingPoint.IsReflectorPert` on the subtype `{i // i ∈ o}`.

**Reading.** Explicit relative bounds for list-restricted reflector data under model conditions.
-/
theorem houseOn_rounding {fp : RoundingModel ℝ} (hfp : fp.IsIdempotent) {o : List (Fin m)}
    (ho : o.Nodup) (hne : o ≠ []) (hu : ((18 * o.length + 31 : ℕ) : ℝ) * fp.u < 1)
    (x : Fin m → ℝ) {vβ : (Fin m → ℝ) × ℝ} (h : vβ ∈ (houseOn fp.round o x).run) :
    (∀ i, i ∉ o → vβ.1 i = 0) ∧
      IsReflectorPert fp.u (18 * o.length + 31) (fun i : {i // i ∈ o} => x i)
        ⟨o.head hne, List.head_mem hne⟩
        ‖(toLp 2 (fun j : {j // j ∈ o} => x j) : EuclideanSpace ℝ {j // j ∈ o})‖
        (fun i => vβ.1 i) vβ.2 := by
  obtain ⟨hout, hrel⟩ := houseOn_rounds hfp ho hne x h
  have hcard := card_subtype_mem_of_nodup ho
  refine ⟨hout, ?_⟩
  have := (hrel.isReflectorPert (by rwa [hcard])).2
  rwa [hcard] at this

end HouseRuns

/-! ### Algorithm 5.1.1 on a whole vector -/

section HouseVector

variable {k : ℕ}

/-- The subtype of the indices listed in `List.finRange (k + 1)` is all of `Fin (k + 1)`. -/
private def finRangeEquiv (k : ℕ) : {i // i ∈ List.finRange (k + 1)} ≃ Fin (k + 1) :=
  Equiv.subtypeUnivEquiv List.mem_finRange

/-- The Euclidean norm of the restriction of $x$ to the full index list is $\|x\|_2$. -/
private theorem norm_toLp_finRange (x : Fin (k + 1) → ℝ) :
    ‖(toLp 2 (fun j : {j // j ∈ List.finRange (k + 1)} => x j) :
        EuclideanSpace ℝ {j // j ∈ List.finRange (k + 1)})‖ =
      ‖(toLp 2 x : EuclideanSpace ℝ (Fin (k + 1)))‖ := by
  simp only [EuclideanSpace.norm_eq]
  congr 1
  exact Fintype.sum_equiv (finRangeEquiv k) _ _ fun _ => rfl

/-- The first entry of `List.finRange (k + 1)` is $0$. -/
private theorem head_finRange (h : List.finRange (k + 1) ≠ []) :
    (List.finRange (k + 1)).head h = 0 := by
  simp [List.finRange_succ]

/-- **Algorithm 5.1.1** of [golub2013matrix], exact semantics. Let $m \ge 1$ and
$x \in \mathbb{R}^m$. In exact arithmetic, the output $(v, \beta)$ of Algorithm 5.1.1 satisfies
$v_1 = 1$, the matrix $P = I - \beta v v^T$ is orthogonal,
$$P x = \|x\|_2 e_1,$$
and $\beta = 0$ or $\beta v^T v = 2$, so that $P$ is $I$ or the Householder matrix of $v$.

The algorithm has three cases. If $\sigma = 0$, then $x = x_1 e_1$; the output has $\beta = 0$
for $x_1 \ge 0$ and gives $P = I - 2 e_1 e_1^T$ for $x_1 < 0$. Otherwise
$v = (x - \|x\|_2 e_1) / (x_1 - \|x\|_2)$, with Parlett's formula for $x_1 - \|x\|_2$ when
$x_1 > 0$. Here $m = k + 1$, and $v_1$ is `v 0`. -/
theorem algorithm_5_1_1_spec (x : Fin (k + 1) → ℝ) :
    (Id.run (algorithm_5_1_1 pure x)).1 0 = 1 ∧
      (1 - (Id.run (algorithm_5_1_1 pure x)).2 •
        vecMulVec (Id.run (algorithm_5_1_1 pure x)).1 (Id.run (algorithm_5_1_1 pure x)).1) ∈
          orthogonalGroup (Fin (k + 1)) ℝ ∧
      (1 - (Id.run (algorithm_5_1_1 pure x)).2 •
        vecMulVec (Id.run (algorithm_5_1_1 pure x)).1 (Id.run (algorithm_5_1_1 pure x)).1) *ᵥ x =
          ‖(toLp 2 x : EuclideanSpace ℝ (Fin (k + 1)))‖ • Pi.single 0 1 ∧
      ((Id.run (algorithm_5_1_1 pure x)).2 = 0 ∨
        (Id.run (algorithm_5_1_1 pure x)).2 *
          ((Id.run (algorithm_5_1_1 pure x)).1 ⬝ᵥ (Id.run (algorithm_5_1_1 pure x)).1) = 2) := by
  have hne : List.finRange (k + 1) ≠ [] := by simp
  obtain ⟨h1, -, h3, h4, h5⟩ := houseOn_spec (List.nodup_finRange (k + 1)) hne x
  rw [head_finRange] at h1 h5
  refine ⟨h1, h4, ?_, h3⟩
  rw [algorithm_5_1_1, h5, norm_toLp_finRange]
  funext i
  by_cases hi : i = 0
  · subst hi; simp
  · simp [hi]

/-- **Section 5.1.5** of [golub2013matrix], accuracy of the computed Householder vector. Let the
rounding model be idempotent, let $m \ge 1$ and $x \in \mathbb{R}^m$, and let $K = 18 m + 31$
with $K u < 1$. Every result $(\hat v, \hat\beta)$ of Algorithm 5.1.1 in the rounding model is
reflector data of order $K$ for $x$ with pivot $1$ and target $\|x\|_2$. That is, there are
exact $v \in \mathbb{R}^m$ and $\beta \in \mathbb{R}$ such that $P = I - \beta v v^T$ is
orthogonal, $P x = \|x\|_2 e_1$, $|\beta| v^T v \le 2$, and
$$\hat\beta = \beta (1 + \theta), \qquad \hat v_i = v_i (1 + \theta_i), \qquad |\theta|,
  |\theta_i| \le \gamma_K.$$

The source states the relative error as $O(u)$; the formal statement gives the bound $\gamma_K$.
In the proof, $(v, \beta)$ is the exact output of the same branch of the algorithm. Here
$m = k + 1$, and the relation is `FloatingPoint.IsReflectorPert`.

**Reading.** Explicit gamma and coefficientwise perturbations under idempotence and smallness
assumptions.
-/
theorem algorithm_5_1_1_rounding {fp : RoundingModel ℝ} (hfp : fp.IsIdempotent)
    (hu : ((18 * (k + 1) + 31 : ℕ) : ℝ) * fp.u < 1) (x : Fin (k + 1) → ℝ)
    {vβ : (Fin (k + 1) → ℝ) × ℝ} (h : vβ ∈ (algorithm_5_1_1 fp.round x).run) :
    IsReflectorPert fp.u (18 * (k + 1) + 31) x 0 ‖(toLp 2 x : EuclideanSpace ℝ (Fin (k + 1)))‖
      vβ.1 vβ.2 := by
  have hne : List.finRange (k + 1) ≠ [] := by simp
  have hlen : (List.finRange (k + 1)).length = k + 1 := List.length_finRange
  obtain ⟨-, hr⟩ := houseOn_rounding hfp (List.nodup_finRange (k + 1)) hne (by rwa [hlen]) x h
  rw [hlen, norm_toLp_finRange] at hr
  refine IsReflectorPert.of_comp_equiv (finRangeEquiv k) ?_
  convert hr using 2
  all_goals first
    | rfl
    | exact (head_finRange hne).symm

end HouseVector

/-! ### §5.1.4 Applying Householder matrices -/

section Apply

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) {m n : ℕ}

/-- The scaled Householder vector $w = \mathrm{fl}(\beta v)$ on the indices of the list $l$, and $0$
at the other indices: the source's $\beta v$, formed once.

**Reading.** Formally scales only selected coordinates and zeroes others.
-/
def householderScaled (v : Fin m → ℝ) (β : ℝ) (l : List (Fin m)) : M (Fin m → ℝ) :=
  l.foldlM (fun (w : Fin m → ℝ) i => do
    let b ← rnd (β * v i)
    pure (Function.update w i b)) 0

/-- One column of the premultiplication $A - (\beta v)(v^T A)$. For a column $a$ and a given
$w = \mathrm{fl}(\beta v)$, the program computes $s = v^T a$ over the indices in `rows` by
Algorithm 1.1.1, and then sets $a_i \leftarrow \mathrm{fl}(a_i - \mathrm{fl}(w_i s))$ for each
$i$ in `rows`.

**Reading.** Follows the column formula on an arbitrary row list.
-/
def householderLeftColumn (w v : Fin m → ℝ) (rows : List (Fin m)) (a : Fin m → ℝ) :
    M (Fin m → ℝ) := do
  let s ← dotAccum rnd rows v a 0
  rows.foldlM (fun (a : Fin m → ℝ) i => do
    let b ← (do let t ← rnd (w i * s); rnd (a i - t))
    pure (Function.update a i b)) a

/-- **Section 5.1.4** of [golub2013matrix], premultiplication by a Householder matrix. Let
$v \in \mathbb{R}^m$, $\beta \in \mathbb{R}$, $A \in \mathbb{R}^{m \times n}$, and let `rows`
and `cols` be lists of row and column indices. The program overwrites the block
$A(\mathrm{rows}, \mathrm{cols})$ with $(I - \beta v v^T) A(\mathrm{rows}, \mathrm{cols})$ in
the form of the source,
$$P A = A - (\beta v)(v^T A),$$
a matrix-vector product and a rank-1 update. It forms $w = \mathrm{fl}(\beta v)$ on `rows` once.
Then for each $q$ in `cols` it computes $s = v^T A(\mathrm{rows}, q)$ by Algorithm 1.1.1 and
sets $A(i, q) \leftarrow \mathrm{fl}(A(i, q) - \mathrm{fl}(w_i s))$ for each $i$ in `rows`. The
entries outside the block are not changed.

The program works in place on the full matrix over the two index lists.

**Generalization.** Extends contiguous blocks to arbitrary index lists with explicit rounding.
-/
def householderApplyLeft (v : Fin m → ℝ) (β : ℝ) (rows : List (Fin m)) (cols : List (Fin n))
    (A : Matrix (Fin m) (Fin n) ℝ) : M (Matrix (Fin m) (Fin n) ℝ) := do
  let w ← householderScaled rnd v β rows
  cols.foldlM (fun (A : Matrix (Fin m) (Fin n) ℝ) q => do
    let c ← householderLeftColumn rnd w v rows (fun i => A i q)
    pure (A.updateCol q c)) A

/-- One row of the postmultiplication $A - (A v)(\beta v)^T$. For a row $a$ and a given
$w = \mathrm{fl}(\beta v)$, the program computes $s = a^T v$ over the indices in `cols` by
Algorithm 1.1.1, and then sets $a_j \leftarrow \mathrm{fl}(a_j - \mathrm{fl}(s w_j))$ for each
$j$ in `cols`.

**Reading.** Follows the row formula on an arbitrary column list.
-/
def householderRightRow (w v : Fin n → ℝ) (cols : List (Fin n)) (a : Fin n → ℝ) :
    M (Fin n → ℝ) := do
  let s ← dotAccum rnd cols a v 0
  cols.foldlM (fun (a : Fin n → ℝ) j => do
    let b ← (do let t ← rnd (s * w j); rnd (a j - t))
    pure (Function.update a j b)) a

/-- **Section 5.1.4** of [golub2013matrix], postmultiplication by a Householder matrix. Let
$v \in \mathbb{R}^n$, $\beta \in \mathbb{R}$, $A \in \mathbb{R}^{m \times n}$, and let `rows`
and `cols` be lists of row and column indices. The program overwrites the block
$A(\mathrm{rows}, \mathrm{cols})$ with $A(\mathrm{rows}, \mathrm{cols})(I - \beta v v^T)$ in the
form
$$A P = A - (A v)(\beta v)^T.$$
It forms $w = \mathrm{fl}(\beta v)$ on `cols` once. Then for each $r$ in `rows` it computes
$s = A(r, \mathrm{cols})\, v$ by Algorithm 1.1.1 and sets $A(r, j) \leftarrow \mathrm{fl}(A(r,
j) - \mathrm{fl}(s w_j))$ for each $j$ in `cols`. The entries outside the block are not changed.

This is the symmetric twin of `GolubVanLoan.Chapter05.householderApplyLeft`.

**Generalization.** Extends block interpretation to arbitrary index lists with explicit rounding.
-/
def householderApplyRight (v : Fin n → ℝ) (β : ℝ) (rows : List (Fin m)) (cols : List (Fin n))
    (A : Matrix (Fin m) (Fin n) ℝ) : M (Matrix (Fin m) (Fin n) ℝ) := do
  let w ← householderScaled rnd v β cols
  rows.foldlM (fun (A : Matrix (Fin m) (Fin n) ℝ) r => do
    let x ← householderRightRow rnd w v cols (A r)
    pure (A.updateRow r x)) A

end Apply

/-! ### The Householder updates: rounding bridges, exact semantics and rounding bounds -/

section ApplyRuns

variable {m n : ℕ} {fp : RoundingModel ℝ}

/-- In the exact rounding model, a computed inner product of $x$ and $y$ is the exact inner product
$x^T y$. -/
theorem eq_dotProduct_of_roundsDot_exact {ι : Type} [Fintype ι] {x y : ι → ℝ} {s : ℝ}
    (h : RoundsDot (RoundingModel.exact ℝ) x y s) : s = x ⬝ᵥ y := by
  have := abs_sub_le_of_roundsDot (by simp) (by simp) h
  simp only [RoundingModel.exact_u, gamma, mul_zero, zero_div, sub_zero, zero_mul] at this
  exact sub_eq_zero.1 (abs_nonpos_iff.1 this)

/-- For a list $l$ without duplicates, every result $w$ of
`GolubVanLoan.Chapter05.householderScaled` in the rounding model has $w_i$ a rounding of
$\beta v_i$ for every $i$ in $l$. -/
theorem householderScaled_rounds {l : List (Fin m)} (hl : l.Nodup) {v w : Fin m → ℝ} {β : ℝ}
    (h : w ∈ (householderScaled fp.round v β l).run) : ∀ i ∈ l, fp.Rounds (β * v i) (w i) :=
  ((SetM.mem_run_foldlM_update_of_nodup (fun i _ (_ : Fin m → ℝ) => fp.round (β * v i)) l hl
    (fun _ _ _ _ _ _ => rfl) 0 w).1 h).2

/-- Rounding bridge of one column of the premultiplication. Let the rounding model be idempotent,
let `rows` have no duplicates, and let $w_i$ be a rounding of $\beta v_i$ for every $i$ in
`rows`. Every result $b$ of `GolubVanLoan.Chapter05.householderLeftColumn` on a column $a$
agrees with $a$ outside `rows`, and on `rows` it is a computed update $a - (\beta v)(v^T a)$ for
$\beta$ and $v|_{\mathrm{rows}}$ (`FloatingPoint.RoundsHouseholderApplyScaled`). -/
theorem householderLeftColumn_rounds (hfp : fp.IsIdempotent) {rows : List (Fin m)}
    (hrows : rows.Nodup) {β : ℝ} {w v a b : Fin m → ℝ}
    (hw : ∀ i ∈ rows, fp.Rounds (β * v i) (w i))
    (h : b ∈ (householderLeftColumn fp.round w v rows a).run) :
    (∀ i, i ∉ rows → b i = a i) ∧
      RoundsHouseholderApplyScaled fp β (fun i : {i // i ∈ rows} => v i) (fun i => a i)
        (fun i => b i) := by
  rw [householderLeftColumn, SetM.mem_run_bind] at h
  obtain ⟨s, hs, hb⟩ := h
  obtain ⟨hout, hin⟩ := (SetM.mem_run_foldlM_update_of_nodup
    (fun i b' (_ : Fin m → ℝ) => do let t ← fp.round (w i * s); fp.round (b' - t)) rows hrows
    (fun _ _ _ _ _ _ => rfl) a b).1 hb
  refine ⟨hout, s, fun i => w i, roundsDot_subtype_of_mem_run_dotAccum hfp hrows hs,
    fun i => hw i i.2, fun i => ?_⟩
  have := hin i i.2
  simpa only [SetM.mem_run_bind, RoundingModel.mem_run_round] using this

/-- Rounding bridge of one row of the postmultiplication. Let the rounding model be idempotent, let
the list `cols` have no duplicates, and for every index $j$ of this list let $w_j$ be a rounding
of $\beta v_j$. Every result $b$ of `GolubVanLoan.Chapter05.householderRightRow` on a row $a$
agrees with $a$ outside `cols`, and on `cols` it is a computed update for $\beta$ and
$v|_{\mathrm{cols}}$ (`FloatingPoint.RoundsHouseholderApplyScaled`). The products
$\mathrm{fl}(s w_j)$ are the relation's $\mathrm{fl}(w_j s)$, and the inner product $a^T v$ is its
$v^T a$. -/
theorem householderRightRow_rounds (hfp : fp.IsIdempotent) {cols : List (Fin n)}
    (hcols : cols.Nodup) {β : ℝ} {w v a b : Fin n → ℝ}
    (hw : ∀ j ∈ cols, fp.Rounds (β * v j) (w j))
    (h : b ∈ (householderRightRow fp.round w v cols a).run) :
    (∀ j, j ∉ cols → b j = a j) ∧
      RoundsHouseholderApplyScaled fp β (fun j : {j // j ∈ cols} => v j) (fun j => a j)
        (fun j => b j) := by
  rw [householderRightRow, SetM.mem_run_bind] at h
  obtain ⟨s, hs, hb⟩ := h
  obtain ⟨hout, hin⟩ := (SetM.mem_run_foldlM_update_of_nodup
    (fun j b' (_ : Fin n → ℝ) => do let t ← fp.round (s * w j); fp.round (b' - t)) cols hcols
    (fun _ _ _ _ _ _ => rfl) a b).1 hb
  have hdot := roundsDot_subtype_of_mem_run_dotAccum hfp hcols hs
  refine ⟨hout, s, fun j => w j, ?_, fun j => hw j j.2, fun j => ?_⟩
  · obtain ⟨o, p, ho, hfull, hp, hsum⟩ := hdot
    exact ⟨o, p, ho, hfull, fun j => by rw [mul_comm]; exact hp j, hsum⟩
  · have := hin j j.2
    simp only [SetM.mem_run_bind, RoundingModel.mem_run_round] at this
    obtain ⟨t, ht, hb⟩ := this
    exact ⟨t, by rwa [mul_comm], hb⟩

/-- **Section 5.1.4** of [golub2013matrix], rounding bridge of the premultiplication. Let the
rounding model be idempotent, and let `rows` and `cols` be lists without duplicates. Every
result $B$ of `GolubVanLoan.Chapter05.householderApplyLeft` with $v$ and $\beta$ on $A$, in the
rounding model, agrees with $A$ outside $\mathrm{rows} \times \mathrm{cols}$. For every $q$ in
`cols`, the column $B(\mathrm{rows}, q)$ is a computed update of $A(\mathrm{rows}, q)$ for
$\beta$ and $v|_{\mathrm{rows}}$: there are a computed inner product $s$ of $v|_{\mathrm{rows}}$
and $A(\mathrm{rows}, q)$, roundings $w_i$ of $\beta v_i$ and roundings $t_i$ of $w_i s$ such
that $B(i, q)$ is a rounding of $A(i, q) - t_i$.

The relation is `FloatingPoint.RoundsHouseholderApplyScaled` on the subtype `{i // i ∈ rows}`. -/
theorem householderApplyLeft_rounds (hfp : fp.IsIdempotent) {rows : List (Fin m)}
    {cols : List (Fin n)} (hrows : rows.Nodup) (hcols : cols.Nodup) (v : Fin m → ℝ) (β : ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) {B : Matrix (Fin m) (Fin n) ℝ}
    (h : B ∈ (householderApplyLeft fp.round v β rows cols A).run) :
    (∀ i q, (i ∉ rows ∨ q ∉ cols) → B i q = A i q) ∧
      ∀ q ∈ cols, RoundsHouseholderApplyScaled fp β (fun i : {i // i ∈ rows} => v i)
        (fun i => A i q) (fun i => B i q) := by
  rw [householderApplyLeft, SetM.mem_run_bind] at h
  obtain ⟨w, hw, hB⟩ := h
  have hw' := householderScaled_rounds hrows hw
  obtain ⟨hout, hin⟩ := (mem_run_foldlM_updateCol_of_nodup
    (fun q a => householderLeftColumn fp.round w v rows a) hcols A B).1 hB
  refine ⟨fun i q hiq => ?_, fun q hq =>
    (householderLeftColumn_rounds hfp hrows hw' (hin q hq)).2⟩
  by_cases hq : q ∈ cols
  · have hi : i ∉ rows := hiq.resolve_right (not_not.2 hq)
    exact (householderLeftColumn_rounds hfp hrows hw' (hin q hq)).1 i hi
  · exact hout q hq i

/-- **Section 5.1.4** of [golub2013matrix], rounding bridge of the postmultiplication. Let the
rounding model be idempotent, and let `rows` and `cols` be lists without duplicates. Every
result $B$ of `GolubVanLoan.Chapter05.householderApplyRight` with $v$ and $\beta$ on $A$, in the
rounding model, agrees with $A$ outside $\mathrm{rows} \times \mathrm{cols}$. For every $r$ in
`rows`, the row $B(r, \mathrm{cols})$ is a computed update of $A(r, \mathrm{cols})$ for $\beta$
and $v|_{\mathrm{cols}}$, in the sense of `FloatingPoint.RoundsHouseholderApplyScaled` on the
subtype `{j // j ∈ cols}`. -/
theorem householderApplyRight_rounds (hfp : fp.IsIdempotent) {rows : List (Fin m)}
    {cols : List (Fin n)} (hrows : rows.Nodup) (hcols : cols.Nodup) (v : Fin n → ℝ) (β : ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) {B : Matrix (Fin m) (Fin n) ℝ}
    (h : B ∈ (householderApplyRight fp.round v β rows cols A).run) :
    (∀ r j, (r ∉ rows ∨ j ∉ cols) → B r j = A r j) ∧
      ∀ r ∈ rows, RoundsHouseholderApplyScaled fp β (fun j : {j // j ∈ cols} => v j)
        (fun j => A r j) (fun j => B r j) := by
  rw [householderApplyRight, SetM.mem_run_bind] at h
  obtain ⟨w, hw, hB⟩ := h
  have hw' := householderScaled_rounds hcols hw
  obtain ⟨hout, hin⟩ := (mem_run_foldlM_updateRow_of_nodup
    (fun r a => householderRightRow fp.round w v cols a) hrows A B).1 hB
  refine ⟨fun r j hrj => ?_, fun r hr =>
    (householderRightRow_rounds hfp hcols hw' (hin r hr)).2⟩
  by_cases hr : r ∈ rows
  · have hj : j ∉ cols := hrj.resolve_left (not_not.2 hr)
    exact (householderRightRow_rounds hfp hcols hw' (hin r hr)).1 j hj
  · exact congrFun (hout r hr) j

/-- In the exact rounding model, a computed update $y$ of $b$ for $\beta$ and $v$ is the exact
update $y_i = b_i - \beta v_i (v^T b)$. -/
theorem eq_of_roundsHouseholderApplyScaled_exact {ι : Type} [Fintype ι] {β : ℝ}
    {v b y : ι → ℝ} (h : RoundsHouseholderApplyScaled (RoundingModel.exact ℝ) β v b y) (i : ι) :
    y i = b i - β * v i * (v ⬝ᵥ b) := by
  obtain ⟨s, w, hs, hw, ht⟩ := h
  obtain ⟨t, ht, hy⟩ := ht i
  rw [RoundingModel.exact_rounds_iff] at ht hy
  rw [hy, ht, (RoundingModel.exact_rounds_iff).1 (hw i), eq_dotProduct_of_roundsDot_exact hs]

private theorem householderApplyLeft_mem_exact (v : Fin m → ℝ) (β : ℝ) (rows : List (Fin m))
    (cols : List (Fin n)) (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (householderApplyLeft pure v β rows cols A) ∈
      (householderApplyLeft (RoundingModel.exact ℝ).round v β rows cols A).run := by
  rw [RoundingModel.round_exact]
  simp only [householderApplyLeft, householderScaled, householderLeftColumn, dotAccum_pure,
    pure_bind, List.foldlM_pure, SetM.mem_run_pure]
  rfl

private theorem householderApplyRight_mem_exact (v : Fin n → ℝ) (β : ℝ) (rows : List (Fin m))
    (cols : List (Fin n)) (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (householderApplyRight pure v β rows cols A) ∈
      (householderApplyRight (RoundingModel.exact ℝ).round v β rows cols A).run := by
  rw [RoundingModel.round_exact]
  simp only [householderApplyRight, householderScaled, householderRightRow, dotAccum_pure,
    pure_bind, List.foldlM_pure, SetM.mem_run_pure]
  rfl

/-- **Section 5.1.4** of [golub2013matrix], exact semantics of the premultiplication. Let `rows` and
`cols` be lists without duplicates, and let the vector $v$ of length $m$ vanish outside `rows`. In
exact arithmetic, `GolubVanLoan.Chapter05.householderApplyLeft` with $v$ and $\beta$ on $A$ returns
the matrix whose column $q$ is column $q$ of $(I - \beta v v^T) A$ for $q$ in `cols`, and column
$q$ of $A$ otherwise.

The proof reads the result off `GolubVanLoan.Chapter05.householderApplyLeft_rounds` at the exact
model.

**Reading.** Arbitrary duplicate-free active index lists in place of contiguous block.
-/
theorem householderApplyLeft_spec {rows : List (Fin m)} {cols : List (Fin n)}
    (hrows : rows.Nodup) (hcols : cols.Nodup) {v : Fin m → ℝ} (hv : ∀ i, i ∉ rows → v i = 0)
    (β : ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (householderApplyLeft pure v β rows cols A) =
      of fun i q => if q ∈ cols then
        ((1 - β • vecMulVec v v : Matrix (Fin m) (Fin m) ℝ) * A) i q else A i q := by
  obtain ⟨hout, hin⟩ := householderApplyLeft_rounds RoundingModel.isIdempotent_exact hrows hcols
    v β A
    (householderApplyLeft_mem_exact v β rows cols A)
  ext i q
  rw [of_apply]
  split_ifs with hq
  · have hPA : ((1 - β • vecMulVec v v : Matrix (Fin m) (Fin m) ℝ) * A) i q =
        ((1 - β • vecMulVec v v) *ᵥ fun r => A r q) i :=
      rfl
    rw [hPA, one_sub_smul_vecMulVec_mulVec_apply_subtype hv]
    split_ifs with hi
    · rw [one_sub_smul_vecMulVec_mulVec_apply]
      exact eq_of_roundsHouseholderApplyScaled_exact (hin q hq) ⟨i, hi⟩
    · exact hout i q (Or.inl hi)
  · exact hout i q (Or.inr hq)

/-- Let `rows` and `cols` be lists without duplicates, let every column index be in `cols`, and let
$v$ vanish outside `rows`. In exact arithmetic, `GolubVanLoan.Chapter05.householderApplyLeft`
with $v$ and $\beta$ on $A$ returns $(I - \beta v v^T) A$. -/
theorem householderApplyLeft_spec_of_forall_mem {rows : List (Fin m)} {cols : List (Fin n)}
    (hrows : rows.Nodup) (hcols : cols.Nodup) (hall : ∀ q, q ∈ cols) {v : Fin m → ℝ}
    (hv : ∀ i, i ∉ rows → v i = 0) (β : ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (householderApplyLeft pure v β rows cols A) = (1 - β • vecMulVec v v) * A := by
  rw [householderApplyLeft_spec hrows hcols hv]
  ext i q
  simp [hall q]

/-- **Section 5.1.4** of [golub2013matrix], exact semantics of the postmultiplication. Let `rows`
and `cols` be lists without duplicates, and let the vector $v$ of length $n$ vanish outside `cols`.
In exact arithmetic, `GolubVanLoan.Chapter05.householderApplyRight` with $v$ and $\beta$ on $A$
returns the matrix whose row $r$ is row $r$ of $A (I - \beta v v^T)$ for $r$ in `rows`, and row
$r$ of $A$ otherwise.

**Reading.** Arbitrary duplicate-free active index lists in place of contiguous block.
-/
theorem householderApplyRight_spec {rows : List (Fin m)} {cols : List (Fin n)}
    (hrows : rows.Nodup) (hcols : cols.Nodup) {v : Fin n → ℝ} (hv : ∀ j, j ∉ cols → v j = 0)
    (β : ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (householderApplyRight pure v β rows cols A) =
      of fun r j => if r ∈ rows then
        (A * (1 - β • vecMulVec v v : Matrix (Fin n) (Fin n) ℝ)) r j else A r j := by
  obtain ⟨hout, hin⟩ := householderApplyRight_rounds RoundingModel.isIdempotent_exact hrows hcols
    v β A
    (householderApplyRight_mem_exact v β rows cols A)
  ext r j
  rw [of_apply]
  split_ifs with hr
  · have hAP : (A * (1 - β • vecMulVec v v : Matrix (Fin n) (Fin n) ℝ)) r j =
        ((1 - β • vecMulVec v v) *ᵥ A r) j := by
      conv_rhs => rw [← transpose_one_sub_smul_vecMulVec β v, mulVec_transpose]
      rfl
    rw [hAP, one_sub_smul_vecMulVec_mulVec_apply_subtype hv]
    split_ifs with hj
    · rw [one_sub_smul_vecMulVec_mulVec_apply]
      exact eq_of_roundsHouseholderApplyScaled_exact (hin r hr) ⟨j, hj⟩
    · exact hout r j (Or.inr hj)
  · exact hout r j (Or.inl hr)

/-- Let `rows` and `cols` be lists without duplicates, let every row index be in `rows`, and let $v$
vanish outside `cols`. In exact arithmetic, `GolubVanLoan.Chapter05.householderApplyRight` with
$v$ and $\beta$ on $A$ returns $A (I - \beta v v^T)$. -/
theorem householderApplyRight_spec_of_forall_mem {rows : List (Fin m)} {cols : List (Fin n)}
    (hrows : rows.Nodup) (hcols : cols.Nodup) (hall : ∀ r, r ∈ rows) {v : Fin n → ℝ}
    (hv : ∀ j, j ∉ cols → v j = 0) (β : ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (householderApplyRight pure v β rows cols A) = A * (1 - β • vecMulVec v v) := by
  rw [householderApplyRight_spec hrows hcols hv]
  ext r j
  simp [hall r]

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **Section 5.1.5** of [golub2013matrix], rounding error of the premultiplication. Let the
rounding model be idempotent, let `rows` and `cols` be lists without duplicates, and let
$K \in \mathbb{N}$ with $(3K + |\mathrm{rows}| + 3)\, u < 1$. Let $v \in \mathbb{R}^m$ vanish
outside `rows`, let $\beta \in \mathbb{R}$ with $|\beta|\, v^T v \le 2$, and let $\hat v_i$ and
$\hat\beta$ be relative perturbations of order $K$ of $v_i$ and $\beta$. Write
$P = I - \beta v v^T$ for the matrix on the indices of `rows`, and $\varepsilon = 3 \gamma_{3K +
|\mathrm{rows}| + 3}$. Every result $B$ of `GolubVanLoan.Chapter05.householderApplyLeft` with
$\hat v$ and $\hat\beta$ on $A$, in the rounding model, agrees with $A$ outside
$\mathrm{rows} \times \mathrm{cols}$, and
$$\|B(\mathrm{rows}, q) - P A(\mathrm{rows}, q)\|_2 \le \varepsilon \|A(\mathrm{rows}, q)\|_2$$
for every $q$ in `cols`, and
$$\|B(\mathrm{rows}, \mathrm{cols}) - P A(\mathrm{rows}, \mathrm{cols})\|_F \le \varepsilon
  \|A(\mathrm{rows}, \mathrm{cols})\|_F.$$

The source states $\mathrm{fl}(\hat P A) = P (A + E)$ with $\|E\|_2 = O(u) \|A\|_2$. For
orthogonal $P$ this is the bound above with $E = P^T \mathrm{fl}(\hat P A) - A$, because then
$\|E\| = \|\mathrm{fl}(\hat P A) - P A\|$. The theorem itself uses only $|\beta|\, v^T v \le 2$
and not the orthogonality of $P$. The blocks are `Matrix.submatrix` on the subtypes of the two
lists.

**Precision.** The source states a spectral-norm backward error of order $u$. This theorem
states an explicit error relative to the exact product using column norms and the Frobenius
norm of the selected block.

**Reading.** Explicit columnwise and block Frobenius error bounds with stated model assumptions
instead of spectral backward error.
-/
theorem householderApplyLeft_rounding (hfp : fp.IsIdempotent) {rows : List (Fin m)}
    {cols : List (Fin n)} (hrows : rows.Nodup) (hcols : cols.Nodup) {K : ℕ}
    (hu : ((3 * K + rows.length + 3 : ℕ) : ℝ) * fp.u < 1) {v vhat : Fin m → ℝ}
    {β βhat : ℝ} (hβ : IsRelPert fp.u K β βhat) (hvv : ∀ i, IsRelPert fp.u K (v i) (vhat i))
    (hv : ∀ i, i ∉ rows → v i = 0) (hP : |β| * (v ⬝ᵥ v) ≤ 2) (A : Matrix (Fin m) (Fin n) ℝ)
    {B : Matrix (Fin m) (Fin n) ℝ}
    (h : B ∈ (householderApplyLeft fp.round vhat βhat rows cols A).run) :
    (∀ i q, (i ∉ rows ∨ q ∉ cols) → B i q = A i q) ∧
      (∀ q : {q // q ∈ cols},
        ‖(toLp 2 ((B.submatrix (Subtype.val : {i // i ∈ rows} → Fin m) Subtype.val -
          (1 - β • vecMulVec (fun i : {i // i ∈ rows} => v i) (fun i : {i // i ∈ rows} => v i)) *
            A.submatrix (Subtype.val : {i // i ∈ rows} → Fin m) Subtype.val).col q) :
              EuclideanSpace ℝ {i // i ∈ rows})‖ ≤
          3 * gamma fp.u (3 * K + rows.length + 3) *
            ‖(toLp 2 ((A.submatrix (Subtype.val : {i // i ∈ rows} → Fin m)
              (Subtype.val : {q // q ∈ cols} → Fin n)).col q) :
                EuclideanSpace ℝ {i // i ∈ rows})‖) ∧
      ‖B.submatrix (Subtype.val : {i // i ∈ rows} → Fin m)
          (Subtype.val : {q // q ∈ cols} → Fin n) -
        (1 - β • vecMulVec (fun i : {i // i ∈ rows} => v i) (fun i : {i // i ∈ rows} => v i)) *
          A.submatrix (Subtype.val : {i // i ∈ rows} → Fin m)
            (Subtype.val : {q // q ∈ cols} → Fin n)‖ ≤
        3 * gamma fp.u (3 * K + rows.length + 3) *
          ‖A.submatrix (Subtype.val : {i // i ∈ rows} → Fin m)
            (Subtype.val : {q // q ∈ cols} → Fin n)‖ := by
  obtain ⟨hout, hin⟩ := householderApplyLeft_rounds hfp hrows hcols vhat βhat A h
  have hcard := card_subtype_mem_of_nodup hrows
  have hP' : |β| * ((fun i : {i // i ∈ rows} => v i) ⬝ᵥ (fun i => v i)) ≤ 2 := by
    rwa [← dotProduct_eq_dotProduct_subtype hv]
  have := frobenius_norm_sub_le_of_forall_roundsHouseholderApplyScaled_col
    (ι := {i // i ∈ rows}) (κ := {q // q ∈ cols}) (by rwa [hcard]) hβ (fun i => hvv i) hP'
    (A := A.submatrix Subtype.val Subtype.val) (B := B.submatrix Subtype.val Subtype.val)
    (fun q => hin q q.2)
  rw [hcard] at this
  exact ⟨hout, this⟩

/-- **Section 5.1.5** of [golub2013matrix], rounding error of the postmultiplication. Let the
rounding model be idempotent, let `rows` and `cols` be lists without duplicates, and let
$K \in \mathbb{N}$ with $(3K + |\mathrm{cols}| + 3)\, u < 1$. Let $v \in \mathbb{R}^n$ vanish
outside `cols`, let $\beta \in \mathbb{R}$ with $|\beta|\, v^T v \le 2$, and let $\hat v_j$ and
$\hat\beta$ be relative perturbations of order $K$ of $v_j$ and $\beta$. Write
$P = I - \beta v v^T$ for the matrix on the indices of `cols`, and $\varepsilon = 3 \gamma_{3K +
|\mathrm{cols}| + 3}$. Every result $B$ of `GolubVanLoan.Chapter05.householderApplyRight` with
$\hat v$ and $\hat\beta$ on $A$, in the rounding model, agrees with $A$ outside
$\mathrm{rows} \times \mathrm{cols}$, and
$$\|B(r, \mathrm{cols}) - A(r, \mathrm{cols}) P\|_2 \le \varepsilon \|A(r, \mathrm{cols})\|_2$$
for every $r$ in `rows`, and
$$\|B(\mathrm{rows}, \mathrm{cols}) - A(\mathrm{rows}, \mathrm{cols}) P\|_F \le \varepsilon
  \|A(\mathrm{rows}, \mathrm{cols})\|_F.$$

This is the postmultiplication form $\mathrm{fl}(A \hat P) = A P + F$ of the bound of
`GolubVanLoan.Chapter05.householderApplyLeft_rounding`.

**Precision.** The source states a spectral-norm backward error of order $u$. This theorem
states an explicit error relative to the exact product using row norms and the Frobenius norm
of the selected block.

**Reading.** Explicit rowwise and block Frobenius error bounds with stated model assumptions instead
of spectral backward error.
-/
theorem householderApplyRight_rounding (hfp : fp.IsIdempotent) {rows : List (Fin m)}
    {cols : List (Fin n)} (hrows : rows.Nodup) (hcols : cols.Nodup) {K : ℕ}
    (hu : ((3 * K + cols.length + 3 : ℕ) : ℝ) * fp.u < 1) {v vhat : Fin n → ℝ}
    {β βhat : ℝ} (hβ : IsRelPert fp.u K β βhat) (hvv : ∀ j, IsRelPert fp.u K (v j) (vhat j))
    (hv : ∀ j, j ∉ cols → v j = 0) (hP : |β| * (v ⬝ᵥ v) ≤ 2) (A : Matrix (Fin m) (Fin n) ℝ)
    {B : Matrix (Fin m) (Fin n) ℝ}
    (h : B ∈ (householderApplyRight fp.round vhat βhat rows cols A).run) :
    (∀ r j, (r ∉ rows ∨ j ∉ cols) → B r j = A r j) ∧
      (∀ r : {r // r ∈ rows},
        ‖(toLp 2 ((B.submatrix (Subtype.val : {r // r ∈ rows} → Fin m)
            (Subtype.val : {j // j ∈ cols} → Fin n) -
          A.submatrix (Subtype.val : {r // r ∈ rows} → Fin m)
              (Subtype.val : {j // j ∈ cols} → Fin n) *
            (1 - β • vecMulVec (fun j : {j // j ∈ cols} => v j)
              (fun j : {j // j ∈ cols} => v j))).row r) :
              EuclideanSpace ℝ {j // j ∈ cols})‖ ≤
          3 * gamma fp.u (3 * K + cols.length + 3) *
            ‖(toLp 2 ((A.submatrix (Subtype.val : {r // r ∈ rows} → Fin m)
              (Subtype.val : {j // j ∈ cols} → Fin n)).row r) :
                EuclideanSpace ℝ {j // j ∈ cols})‖) ∧
      ‖B.submatrix (Subtype.val : {r // r ∈ rows} → Fin m)
          (Subtype.val : {j // j ∈ cols} → Fin n) -
        A.submatrix (Subtype.val : {r // r ∈ rows} → Fin m)
            (Subtype.val : {j // j ∈ cols} → Fin n) *
          (1 - β • vecMulVec (fun j : {j // j ∈ cols} => v j) (fun j : {j // j ∈ cols} => v j))‖ ≤
        3 * gamma fp.u (3 * K + cols.length + 3) *
          ‖A.submatrix (Subtype.val : {r // r ∈ rows} → Fin m)
            (Subtype.val : {j // j ∈ cols} → Fin n)‖ := by
  obtain ⟨hout, hin⟩ := householderApplyRight_rounds hfp hrows hcols vhat βhat A h
  have hcard := card_subtype_mem_of_nodup hcols
  have hP' : |β| * ((fun j : {j // j ∈ cols} => v j) ⬝ᵥ (fun j => v j)) ≤ 2 := by
    rwa [← dotProduct_eq_dotProduct_subtype hv]
  have := frobenius_norm_sub_le_of_forall_roundsHouseholderApplyScaled_row
    (ι := {j // j ∈ cols}) (κ := {r // r ∈ rows}) (by rwa [hcard]) hβ (fun j => hvv j) hP'
    (A := A.submatrix Subtype.val Subtype.val) (B := B.submatrix Subtype.val Subtype.val)
    (fun r => hin r r.2)
  rw [hcard] at this
  exact ⟨hout, this⟩

/-- If $\hat\beta = \beta (1 + \theta)$ and $b_i = a_i (1 + \theta_i)$ with
$|\theta|, |\theta_i| \le \gamma_K$, then $\|(I - \hat\beta b b^T) - (I - \beta a a^T)\|_2 \le
((1 + \gamma_K)^3 - 1)\, |\beta|\, \|a\|_2^2$. -/
private theorem lpOpNorm_two_one_sub_smul_vecMulVec_sub_le {K : ℕ} {a b : Fin m → ℝ}
    {β β' : ℝ} (hg : 0 ≤ gamma fp.u K) (hβ : IsRelPert fp.u K β β')
    (hb : ∀ i, IsRelPert fp.u K (a i) (b i)) :
    lpOpNorm 2 ((1 - β' • vecMulVec b b) - (1 - β • vecMulVec a a)) ≤
      ((1 + gamma fp.u K) ^ 3 - 1) * |β| * ‖(toLp 2 a : EuclideanSpace ℝ (Fin m))‖ ^ 2 := by
  set g := gamma fp.u K
  obtain ⟨θ, hθ, rfl⟩ := hβ
  have hb' : ∀ i, ∃ θ, |θ| ≤ g ∧ b i = a i * (1 + θ) := hb
  choose t ht hbt using hb'
  have h3 : ∀ x y z : ℝ, |x| ≤ g → |y| ≤ g → |z| ≤ g →
      |(1 + x) * (1 + y) * (1 + z) - 1| ≤ (1 + g) ^ 3 - 1 := by
    intro x y z hx hy hz
    have h1 : |x| ≤ (1 + g) ^ 1 - 1 := by rw [pow_one, add_sub_cancel_left]; exact hx
    have h2 := abs_one_add_mul_one_add_sub_one_le_one_add_pow_sub_one h1 hy
    have h3 := abs_one_add_mul_one_add_sub_one_le_one_add_pow_sub_one h2 hz
    rwa [add_sub_cancel] at h3
  have hc : 0 ≤ (1 + g) ^ 3 - 1 := sub_nonneg.2 (one_le_pow₀ (by linarith))
  have e : (1 - (β * (1 + θ)) • vecMulVec b b) - (1 - β • vecMulVec a a) =
      -((β * (1 + θ)) • vecMulVec b b - β • vecMulVec a a) := by abel
  rw [e]
  refine (l2_opNorm_le_frobenius_norm _).trans ?_
  have hva : ‖vecMulVec a a‖ = ‖(toLp 2 a : EuclideanSpace ℝ (Fin m))‖ ^ 2 := by
    rw [frobenius_norm_vecMulVec, sq]
  rw [norm_neg, ← hva]
  refine frobenius_norm_le_of_forall_abs_le (by positivity) fun i j => ?_
  simp only [Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, hbt]
  have e2 : β * (1 + θ) * (a i * (1 + t i) * (a j * (1 + t j))) - β * (a i * a j) =
      β * (a i * a j) * ((1 + θ) * (1 + t i) * (1 + t j) - 1) := by ring
  rw [e2, abs_mul, abs_mul]
  calc |β| * |a i * a j| * |(1 + θ) * (1 + t i) * (1 + t j) - 1|
      ≤ |β| * |a i * a j| * ((1 + g) ^ 3 - 1) :=
        mul_le_mul_of_nonneg_left (h3 _ _ _ hθ (ht i) (ht j)) (by positivity)
    _ = ((1 + g) ^ 3 - 1) * |β| * |a i * a j| := by ring

end Frobenius

section L2

open scoped Matrix.Norms.L2Operator

/-- **Section 5.1.5** of [golub2013matrix], accuracy of the computed Householder matrix. Let the
rounding model be idempotent, let $m \ge 1$ and $x \in \mathbb{R}^m$, and let $K = 18 m + 31$
with $K u < 1$. For every result $(\hat v, \hat\beta)$ of Algorithm 5.1.1 in the rounding model,
there are $v \in \mathbb{R}^m$ and $\beta \in \mathbb{R}$ such that $I - \beta v v^T$ is
orthogonal, $(I - \beta v v^T) x = \|x\|_2 e_1$, $\hat v_i = v_i (1 + \theta_i)$ with
$|\theta_i| \le \gamma_K$ for every $i$, and the Householder matrices $\hat P = I - 2 \hat v
\hat v^T / \hat v^T \hat v$ and $P = I - 2 v v^T / v^T v$ satisfy
$$\|\hat P - P\|_2 \le 8 \gamma_K.$$

The source states $\|\hat P - P\|_2 = O(u)$. Here $\hat P$ is rebuilt from $\hat v$ alone, as in
the source. `GolubVanLoan.Chapter05.one_sub_smul_vecMulVec_computed_sub_le` bounds instead the
matrix $I - \hat\beta \hat v \hat v^T$ that the update programs apply. Here $m = k + 1$.

**Reading.** Bounds recomputed reflector difference by explicit 8 gamma and distinguishes it from
the exact update when beta is zero.
-/
theorem householderMatrix_computed_sub_le {k : ℕ} (hfp : fp.IsIdempotent)
    (hu : ((18 * (k + 1) + 31 : ℕ) : ℝ) * fp.u < 1) (x : Fin (k + 1) → ℝ)
    {vβ : (Fin (k + 1) → ℝ) × ℝ} (h : vβ ∈ (algorithm_5_1_1 fp.round x).run) :
    ∃ (v : Fin (k + 1) → ℝ) (β : ℝ), (1 - β • vecMulVec v v) ∈ orthogonalGroup (Fin (k + 1)) ℝ ∧
      (1 - β • vecMulVec v v) *ᵥ x = ‖(toLp 2 x : EuclideanSpace ℝ (Fin (k + 1)))‖ •
        Pi.single 0 1 ∧
      (∀ i, IsRelPert fp.u (18 * (k + 1) + 31) (v i) (vβ.1 i)) ∧
      ‖householderMatrix vβ.1 - householderMatrix v‖ ≤ 8 * gamma fp.u (18 * (k + 1) + 31) := by
  obtain ⟨v, β, hO, hmul, -, -, hv⟩ := algorithm_5_1_1_rounding hfp hu x h
  refine ⟨v, β, hO, hmul, hv, ?_⟩
  -- the computed vector has `v̂ 0 = 1`, so the exact one is nonzero
  have hne : List.finRange (k + 1) ≠ [] := by simp
  obtain ⟨σ, -, h1, -⟩ := (houseOn_rounds hfp (List.nodup_finRange (k + 1)) hne x h).2
  have h0 : vβ.1 0 = 1 := by
    have := h1; simp only [head_finRange] at this; exact this
  have hv0 : v ≠ 0 := by
    rintro rfl
    obtain ⟨θ, -, hθ⟩ := hv 0
    rw [h0, Pi.zero_apply, zero_mul] at hθ
    exact one_ne_zero hθ
  rw [householderMatrix_eq_reflector, householderMatrix_eq_reflector]
  exact l2_opNorm_reflector_sub_le hv0 hv

/-- **Section 5.1.12** of [golub2013matrix], the computed reflection that the update programs apply.
Let the rounding model be idempotent, let $m \ge 1$ and $x \in \mathbb{R}^m$, and let
$K = 18 m + 31$ with $K u < 1$. For every result $(\hat v, \hat\beta)$ of Algorithm 5.1.1 in the
rounding model, there are $v \in \mathbb{R}^m$ and $\beta \in \mathbb{R}$ such that
$P = I - \beta v v^T$ is orthogonal, $P x = \|x\|_2 e_1$, and
$$\|(I - \hat\beta \hat v \hat v^T) - P\|_2 \le 2 \bigl((1 + \gamma_K)^3 - 1\bigr).$$

The source says that the matrix defined by the floating point output of `house` is orthogonal to
working precision. `GolubVanLoan.Chapter05.householderMatrix_computed_sub_le` reads this matrix
literally as $I - 2 \hat v \hat v^T / \hat v^T \hat v$, rebuilt from $\hat v$ alone. This
theorem reads it as $I - \hat\beta \hat v \hat v^T$ with the computed $\hat\beta$, the matrix
that the update programs apply. It covers the branch $\sigma = 0$, $x_1 \ge 0$, where $P = I$
while the Householder matrix of $v$ is a reflection. Here $m = k + 1$.

**Reading.** Tracks the actual computed beta of the update and bounds the difference by a different
explicit constant.
-/
theorem one_sub_smul_vecMulVec_computed_sub_le {k : ℕ} (hfp : fp.IsIdempotent)
    (hu : ((18 * (k + 1) + 31 : ℕ) : ℝ) * fp.u < 1) (x : Fin (k + 1) → ℝ)
    {vβ : (Fin (k + 1) → ℝ) × ℝ} (h : vβ ∈ (algorithm_5_1_1 fp.round x).run) :
    ∃ (v : Fin (k + 1) → ℝ) (β : ℝ), (1 - β • vecMulVec v v) ∈ orthogonalGroup (Fin (k + 1)) ℝ ∧
      (1 - β • vecMulVec v v) *ᵥ x = ‖(toLp 2 x : EuclideanSpace ℝ (Fin (k + 1)))‖ •
        Pi.single 0 1 ∧
      ‖(1 - vβ.2 • vecMulVec vβ.1 vβ.1) - (1 - β • vecMulVec v v)‖ ≤
        2 * ((1 + gamma fp.u (18 * (k + 1) + 31)) ^ 3 - 1) := by
  obtain ⟨v, β, hO, hmul, hβv, hβ, hv⟩ := algorithm_5_1_1_rounding hfp hu x h
  refine ⟨v, β, hO, hmul, ?_⟩
  have hg : 0 ≤ gamma fp.u (18 * (k + 1) + 31) := gamma_nonneg fp.u_nonneg hu
  have hc : 0 ≤ (1 + gamma fp.u (18 * (k + 1) + 31)) ^ 3 - 1 :=
    sub_nonneg.2 (one_le_pow₀ (by linarith))
  have hvv : ‖(toLp 2 v : EuclideanSpace ℝ (Fin (k + 1)))‖ ^ 2 = v ⬝ᵥ v := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [dotProduct, sq]
  rw [← lpOpNorm_two]
  refine (lpOpNorm_two_one_sub_smul_vecMulVec_sub_le hg hβ hv).trans ?_
  rw [mul_assoc, hvv, mul_comm 2]
  exact mul_le_mul_of_nonneg_left hβv hc

end L2

end ApplyRuns

/-! ### §5.1.6 The factored-form representation -/

section FactoredForm

variable {m n : ℕ}

/-- The index list $[j, j+1, \dots, m-1]$ of `Fin m`, which is empty for $j \ge m$: the source's
rows $j{:}m$ (or columns $j{:}n$) of a block $A(j{:}m, j{:}n)$, in 0-based form. -/
def indexFrom (m j : ℕ) : List (Fin m) := (List.finRange m).filter fun i => j ≤ (i : ℕ)

/-- An index $i$ is in `GolubVanLoan.Chapter05.indexFrom m j` if and only if $j \le i$. -/
@[simp]
theorem mem_indexFrom {j : ℕ} {i : Fin m} : i ∈ indexFrom m j ↔ j ≤ (i : ℕ) := by
  simp [indexFrom]

/-- The list `GolubVanLoan.Chapter05.indexFrom m j` has no duplicates. -/
theorem nodup_indexFrom (m j : ℕ) : (indexFrom m j).Nodup :=
  (List.nodup_finRange m).filter _

/-- For $j < m$, the list `GolubVanLoan.Chapter05.indexFrom m j` is nonempty. -/
theorem indexFrom_ne_nil {j : ℕ} (hj : j < m) : indexFrom m j ≠ [] := by
  intro h
  have : (⟨j, hj⟩ : Fin m) ∈ indexFrom m j := by simp
  rw [h] at this
  exact List.not_mem_nil this

/-- The first entry of a strictly increasing list is at most each of its entries. -/
private theorem head_le_of_pairwise {α : Type*} [Preorder α] {l : List α}
    (hp : l.Pairwise (· < ·)) (h : l ≠ []) {b : α} (hb : b ∈ l) : l.head h ≤ b := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t =>
    rcases List.mem_cons.1 hb with rfl | hb
    · exact le_rfl
    · exact (List.rel_of_pairwise_cons hp hb).le

/-- For $j < m$, the first entry of `GolubVanLoan.Chapter05.indexFrom m j` is $j$: the rows $j{:}m$
start at row $j$. -/
theorem head_indexFrom {j : ℕ} (hj : j < m) (h : indexFrom m j ≠ []) :
    (indexFrom m j).head h = ⟨j, hj⟩ := by
  have hp : (indexFrom m j).Pairwise (· < ·) :=
    (List.sortedLT_finRange m).pairwise.filter _
  have hmem : (⟨j, hj⟩ : Fin m) ∈ indexFrom m j := by simp
  have h1 := head_le_of_pairwise hp h hmem
  have h2 : j ≤ ((indexFrom m j).head h : ℕ) := mem_indexFrom.1 (List.head_mem h)
  exact le_antisymm h1 (Fin.mk_le_of_le_val h2)

/-- The index list $[0, 1, \dots, j]$ of `Fin m`, which is all of `Fin m` for $j \ge m - 1$: the
source's rows $1{:}j+1$ in 0-based form. It is the twin of `GolubVanLoan.Chapter05.indexFrom`. -/
def indexTo (m j : ℕ) : List (Fin m) := (List.finRange m).filter fun i => (i : ℕ) ≤ j

/-- An index $i$ is in `GolubVanLoan.Chapter05.indexTo m j` if and only if $i \le j$. -/
@[simp]
theorem mem_indexTo {j : ℕ} {i : Fin m} : i ∈ indexTo m j ↔ (i : ℕ) ≤ j := by
  simp [indexTo]

/-- The list `GolubVanLoan.Chapter05.indexTo m j` has no duplicates. -/
theorem nodup_indexTo (m j : ℕ) : (indexTo m j).Nodup :=
  (List.nodup_finRange m).filter _

/-- If $f$ vanishes outside a list $l$ without duplicates, then $\sum_i f(i)$ is the sum of $f$
along $l$. -/
theorem sum_eq_sum_map_of_nodup {ι : Type} [Fintype ι] {l : List ι}
    (hl : l.Nodup) {f : ι → ℝ} (hf : ∀ i, i ∉ l → f i = 0) : ∑ i, f i = (l.map f).sum := by
  classical
  rw [← List.sum_toFinset f hl]
  exact (Finset.sum_subset (Finset.subset_univ _) fun i _ hi =>
    hf i (by simpa using hi)).symm

/-- **Section 5.1.6** of [golub2013matrix], the product of reflector data. For reflector data
$[(v_1, \beta_1), \dots, (v_r, \beta_r)]$, listed in order of application, the matrix is
$$Q = Q_1 Q_2 \cdots Q_r, \qquad Q_j = I - \beta_j v_j v_j^T.$$
For the empty list $Q = I$.

Reflector data are lists `List ((Fin m → ℝ) × ℝ)`. Each $\beta_j$ is the value that the program
which computed $v_j$ returned, and it is not recomputed from $v_j$.

**Reading.** Product of arbitrary vector and coefficient pairs without staggered pivots or
orthogonality enforced.
-/
noncomputable def householderProduct (data : List ((Fin m → ℝ) × ℝ)) :
    Matrix (Fin m) (Fin m) ℝ :=
  (data.map fun p => 1 - p.2 • vecMulVec p.1 p.1).prod

/-- The product of no reflectors is the identity.

**Generalization.** Extends to an empty product.
-/
@[simp]
theorem householderProduct_nil : householderProduct ([] : List ((Fin m → ℝ) × ℝ)) = 1 := rfl

/-- The product of reflector data $(v, \beta)$ followed by $D$ is $(I - \beta v v^T)$ times the
product of $D$. -/
@[simp]
theorem householderProduct_cons (p : (Fin m → ℝ) × ℝ) (data : List ((Fin m → ℝ) × ℝ)) :
    householderProduct (p :: data) = (1 - p.2 • vecMulVec p.1 p.1) * householderProduct data :=
  rfl

/-- The product of reflector data $D$ followed by $(v, \beta)$ is the product of $D$ times
$(I - \beta v v^T)$. -/
theorem householderProduct_concat (data : List ((Fin m → ℝ) × ℝ)) (p : (Fin m → ℝ) × ℝ) :
    householderProduct (data ++ [p]) = householderProduct data * (1 - p.2 • vecMulVec p.1 p.1) := by
  simp [householderProduct, List.prod_append]

/-- The product of reflector data $D$ followed by $E$ is the product of $D$ times the product of
$E$. -/
theorem householderProduct_append (D E : List ((Fin m → ℝ) × ℝ)) :
    householderProduct (D ++ E) = householderProduct D * householderProduct E := by
  simp [householderProduct, List.prod_append]

/-- The transpose of the product of the reversed reflector data is the product of the data, because
every factor $I - \beta v v^T$ is symmetric. -/
theorem householderProduct_reverse_transpose (data : List ((Fin m → ℝ) × ℝ)) :
    (householderProduct data.reverse)ᵀ = householderProduct data := by
  induction data with
  | nil => simp
  | cons p t ih =>
    rw [List.reverse_cons, householderProduct_concat, transpose_mul,
      transpose_one_sub_smul_vecMulVec, ih, householderProduct_cons]

/-- If every pair $(v, \beta)$ of the reflector data has $\beta = 0$ or $\beta v^T v = 2$, then the
product of the data is orthogonal, because each factor is then $I$ or a Householder matrix.

**Reading.** Explicit condition includes identities via beta=0 and arbitrary factor lists.
-/
theorem householderProduct_mem_orthogonalGroup {data : List ((Fin m → ℝ) × ℝ)}
    (h : ∀ p ∈ data, p.2 = 0 ∨ p.2 * (p.1 ⬝ᵥ p.1) = 2) :
    householderProduct data ∈ orthogonalGroup (Fin m) ℝ := by
  refine list_prod_mem fun Q hQ => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hQ
  refine one_sub_smul_vecMulVec_mem_orthogonalGroup ?_
  rcases h p hp with h0 | h2
  · rw [h0, zero_mul]
  · rw [h2, sub_self, mul_zero]

/-- If every vector of the reflector data vanishes at $p$, then the product of the data fixes $e_p$.

**Reading.** Any coordinate absent from the support of every reflector is fixed.
-/
theorem householderProduct_mulVec_single {data : List ((Fin m → ℝ) × ℝ)} {p : Fin m}
    (h : ∀ q ∈ data, q.1 p = 0) :
    householderProduct data *ᵥ Pi.single p 1 = Pi.single p 1 := by
  induction data with
  | nil => rw [householderProduct_nil, one_mulVec]
  | cons q data ih =>
    rw [householderProduct_cons, ← mulVec_mulVec,
      ih fun r hr => h r (List.mem_cons_of_mem _ hr),
      one_sub_smul_vecMulVec_mulVec_single (h q List.mem_cons_self)]

/-- **Equation (5.1.3)** of [golub2013matrix], the Householder vector stored in a factored-form
array. For $A \in \mathbb{R}^{m \times n}$ and a column $j$, the vector
$v^{(j)} \in \mathbb{R}^m$ has
$$v^{(j)}_i = 0 \ (i < j), \qquad v^{(j)}_j = 1, \qquad v^{(j)}_i = a_{ij} \ (i > j):$$
zeros above position $j$, $1$ at position $j$, and the essential part $A(j+1{:}m, j)$ below.

Indices are 0-based. For $j \ge m$ the vector is $0$.

**Reading.** Total array function including an empty active vector when pivot exceeds row count.
-/
def storedHouseholderVec (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) : Fin m → ℝ :=
  fun i => if (i : ℕ) < j then 0 else if (i : ℕ) = j then 1 else A i j

/-- The stored vector $v^{(j)}$ vanishes at every row $i$ that is not in
`GolubVanLoan.Chapter05.indexFrom m j`, that is, at every $i < j$. -/
theorem storedHouseholderVec_eq_zero (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) {i : Fin m}
    (hi : i ∉ indexFrom m j) : storedHouseholderVec A j i = 0 := by
  rw [mem_indexFrom, not_le] at hi
  simp [storedHouseholderVec, hi]

/-- **Equation (5.1.3)** of [golub2013matrix], the reflector data of a factored-form array. For
$A \in \mathbb{R}^{m \times n}$ and $\beta \in \mathbb{R}^n$, the data are
$$[(v^{(1)}, \beta_1), \dots, (v^{(n)}, \beta_n)],$$
with the vectors $v^{(j)}$ read from the array and the given $\beta_j$. In the source these are
the Householder vectors and the corresponding $\beta_j$.

The $\beta_j$ are the values that the factorization returned; they are not recomputed from the
stored vectors.

**Reading.** Allows every array shape and pairs data with explicitly stored coefficients.
-/
def storedReflectors (A : Matrix (Fin m) (Fin n) ℝ) (β : Fin n → ℝ) :
    List ((Fin m → ℝ) × ℝ) :=
  List.ofFn fun j => (storedHouseholderVec A j, β j)

/-- **Equation (5.1.3)** of [golub2013matrix], the factored form. For
$A \in \mathbb{R}^{m \times n}$ and $\beta \in \mathbb{R}^n$,
$$Q = Q_1 Q_2 \cdots Q_n, \qquad Q_j = I_m - \beta_j v^{(j)} v^{(j)T},$$
where $v^{(j)}$ is the Householder vector stored in column $j$ of $A$.

**Reading.** Defines the product on arbitrary dimensions and supplied coefficients.
-/
noncomputable def factoredQ (β : Fin n → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  householderProduct (storedReflectors A β)

/-- The factored form is the product of the matrices $I - \beta_j v^{(j)} v^{(j)T}$ over
$j = 0, \dots, n - 1$ in increasing order.

**Reading.** Product expansion also holds on totalized inputs.
-/
theorem factoredQ_eq_prod (β : Fin n → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    factoredQ β A = ((List.finRange n).map fun j =>
      1 - β j • vecMulVec (storedHouseholderVec A j) (storedHouseholderVec A j)).prod := by
  simp only [factoredQ, householderProduct, storedReflectors, List.ofFn_eq_map, List.map_map]
  rfl

/-- **Equations (5.1.4) and (5.1.5)** of [golub2013matrix], the recomputed $\beta_j$. For
$A \in \mathbb{R}^{m \times n}$ and a column $j$,
$$\beta_j = \frac{2}{v^{(j)T} v^{(j)}},$$
where $v^{(j)}$ is the stored Householder vector. For $j < m$ this is the source's
$2 / (1 + \|A(j+1{:}m, j)\|_2^2)$. Algorithm 5.3.2 uses the same value.

The value is the $\beta$ that Algorithm 5.1.1 returned when that $\beta$ was nonzero. When
Algorithm 5.1.1 returned $\beta = 0$, the value is $2$. For $j \ge m$ the stored vector is $0$
and the value is $2 / 0 = 0$.

**Reading.** Formula agrees on valid pivots and totalizes out-of-range pivots via division.
-/
noncomputable def recomputedBeta (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) : ℝ :=
  2 / (storedHouseholderVec A j ⬝ᵥ storedHouseholderVec A j)

/-- For $j < m$, the stored vector satisfies $v^{(j)T} v^{(j)} = 1 + \|A(j+1{:}m, j)\|_2^2$, with
the squared norm written as the sum of the squares of the stored entries along
`GolubVanLoan.Chapter05.indexFrom m (j + 1)`. -/
theorem storedHouseholderVec_dotProduct_self (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n)
    (hj : (j : ℕ) < m) :
    storedHouseholderVec A j ⬝ᵥ storedHouseholderVec A j =
      1 + ((indexFrom m (j + 1)).map fun i =>
        storedHouseholderVec A j i * storedHouseholderVec A j i).sum := by
  set v := storedHouseholderVec A j with hv
  have hsplit : ∀ i, v i * v i =
      (if i = ⟨j, hj⟩ then 1 else 0) + (if (j : ℕ) + 1 ≤ i then v i * v i else 0) := by
    intro i
    by_cases hij : (i : ℕ) = j
    · have hi : i = ⟨j, hj⟩ := Fin.ext hij
      subst hi
      simp [hv, storedHouseholderVec]
    · have hne : i ≠ ⟨j, hj⟩ := fun e => hij (by rw [e])
      by_cases hlt : (i : ℕ) < j
      · have h1 : ¬ ((j : ℕ) + 1 ≤ i) := by omega
        simp [hv, storedHouseholderVec, hlt, hne, h1]
      · have h1 : (j : ℕ) + 1 ≤ i := by omega
        simp [hne, h1]
  have htail : ∑ i : Fin m, (if (j : ℕ) + 1 ≤ (i : ℕ) then v i * v i else 0) =
      ((indexFrom m (j + 1)).map fun i => v i * v i).sum := by
    rw [sum_eq_sum_map_of_nodup (nodup_indexFrom m (j + 1)) (fun i hi => by
      rw [mem_indexFrom] at hi; simp [hi])]
    congr 1
    exact List.map_congr_left fun i hi => by rw [mem_indexFrom] at hi; simp [hi]
  change ∑ i, v i * v i = _
  rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib, Finset.sum_ite_eq', htail]
  simp only [Finset.mem_univ, ↓reduceIte]

/-- If every $Q_a$ is symmetric, the loop that premultiplies $C$ by $Q_{a_1}, \dots, Q_{a_k}$ in
turn computes $Q_{a_k} \cdots Q_{a_1} C = (Q_{a_1} \cdots Q_{a_k})^T C$.

**Reading.** Ordered fold identity for arbitrary symmetric factors, independent of factorization
shape.
-/
theorem foldl_mul_eq_transpose_prod_mul {α : Type} {p : ℕ} (Q : α → Matrix (Fin m) (Fin m) ℝ)
    (hQ : ∀ a, (Q a)ᵀ = Q a) (l : List α) (C : Matrix (Fin m) (Fin p) ℝ) :
    l.foldl (fun C a => Q a * C) C = ((l.map Q).prod)ᵀ * C := by
  induction l generalizing C with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.prod_cons, transpose_mul, hQ,
      Matrix.mul_assoc]

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Equation (5.1.4)** of [golub2013matrix], as a program. Given $A \in \mathbb{R}^{m \times n}$
that holds a factored form and $C \in \mathbb{R}^{m \times p}$, the program overwrites $C$ with
$Q^T C$:
```
for j = 1:n
    v(j:m) = [1; A(j+1:m, j)]
    β_j = 2/(1 + ‖A(j+1:m, j)‖₂²)
    C(j:m, :) = C(j:m, :) - (β_j v(j:m))(v(j:m)ᵀ C(j:m, :))
end
```
The recomputation of $\beta_j$ is rounded as in the source: a computed inner product, the
addition of $1$, and a division. The update is `GolubVanLoan.Chapter05.householderApplyLeft` on
the rows $j{:}m$ and all columns.

**Reading.** Exact source loop on tall inputs; definition totalizes wide inputs and uses
recomputation semantics.
-/
noncomputable def factoredQTransposeMul {p : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (C : Matrix (Fin m) (Fin p) ℝ) : M (Matrix (Fin m) (Fin p) ℝ) :=
  (List.finRange n).foldlM (fun (C : Matrix (Fin m) (Fin p) ℝ) j => do
    let v := storedHouseholderVec A j
    let s ← dotAccum rnd (indexFrom m (j + 1)) v v 0
    let β ← rnd (2 / (← rnd (1 + s)))
    householderApplyLeft rnd v β (indexFrom m j) (List.finRange p) C) C

/-- **Equation (5.1.5)** of [golub2013matrix], as a program: backward accumulation of the first $k$
columns $Q(:, 1{:}k)$ of the factored form stored in $A \in \mathbb{R}^{m \times n}$.
```
Q = I_m(:, 1:k)
for j = n:-1:1
    v(j:m) = [1; A(j+1:m, j)]
    β_j = 2/(1 + ‖A(j+1:m, j)‖₂²)
    Q(j:m, j:k) = Q(j:m, j:k) - (β_j v(j:m))(v(j:m)ᵀ Q(j:m, j:k))
end
```
The $\beta_j$ are recomputed as in `GolubVanLoan.Chapter05.factoredQTransposeMul`. The update
can be restricted to the columns $j{:}k$, because the columns $< j$ of the partial product are
still columns of the identity, which the reflector $Q_j$ fixes.

**Reading.** Definition totalizes k and shape, and uses recomputation semantics.
-/
noncomputable def factoredQFirstColumns (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    M (Matrix (Fin m) (Fin k) ℝ) :=
  (List.finRange n).reverse.foldlM (fun (Q : Matrix (Fin m) (Fin k) ℝ) j => do
    let v := storedHouseholderVec A j
    let s ← dotAccum rnd (indexFrom m (j + 1)) v v 0
    let β ← rnd (2 / (← rnd (1 + s)))
    householderApplyLeft rnd v β (indexFrom m j) (indexFrom k j) Q)
    (of fun i c => if (i : ℕ) = c then 1 else 0)

/-- **Equation (5.1.5)** of [golub2013matrix] with the returned $\beta$. Given
$A \in \mathbb{R}^{m \times n}$ that holds the stored Householder vectors and the
$\beta \in \mathbb{R}^n$ that Algorithm 5.1.1 returned, the program computes the first $k$
columns of $Q$ by backward accumulation: $Q = I_m(:, 1{:}k)$ and, for $j = n, n - 1, \dots, 1$,
$$Q(j{:}m, j{:}k) = Q(j{:}m, j{:}k) - (\beta_j v(j{:}m)) (v(j{:}m)^T Q(j{:}m, j{:}k)).$$

**Correction.** This is the loop of `GolubVanLoan.Chapter05.factoredQFirstColumns` without the
recomputation of $\beta_j$ from the stored vector, which is wrong when Algorithm 5.1.1 returned
$\beta_j = 0$ (see `GolubVanLoan.Chapter05.equation_5_1_5`).

Every later algorithm that needs the first columns of a factored $Q$ calls this program. -/
noncomputable def storedQFirstColumns (A : Matrix (Fin m) (Fin n) ℝ) (β : Fin n → ℝ) (k : ℕ) :
    M (Matrix (Fin m) (Fin k) ℝ) :=
  (List.finRange n).reverse.foldlM (fun (Q : Matrix (Fin m) (Fin k) ℝ) j =>
    householderApplyLeft rnd (storedHouseholderVec A j) (β j) (indexFrom m j) (indexFrom k j) Q)
    (of fun i c => if (i : ℕ) = c then 1 else 0)

/-- **Section 5.1.6** of [golub2013matrix], forward accumulation. For reflector data
$[(v_1, \beta_1), \dots, (v_r, \beta_r)]$, the program sets $Q = I$ and then, for
$j = 1, \dots, r$, $Q \leftarrow Q Q_j$ with $Q_j = I - \beta_j v_j v_j^T$. Each update is
`GolubVanLoan.Chapter05.householderApplyRight` on all rows and columns.

**Reading.** Implements right accumulation for any reflector data list.
-/
def forwardAccumulation (data : List ((Fin m → ℝ) × ℝ)) : M (Matrix (Fin m) (Fin m) ℝ) :=
  data.foldlM (fun (Q : Matrix (Fin m) (Fin m) ℝ) p =>
    householderApplyRight rnd p.1 p.2 (List.finRange m) (List.finRange m) Q) 1

/-- **Section 5.1.6** of [golub2013matrix], backward accumulation, which the source recommends. For
reflector data $[(v_1, \beta_1), \dots, (v_r, \beta_r)]$, the program sets $Q = I$ and then, for
$j = r, r - 1, \dots, 1$, $Q \leftarrow Q_j Q$ with $Q_j = I - \beta_j v_j v_j^T$. Each update
is `GolubVanLoan.Chapter05.householderApplyLeft` on all rows and columns.

This is the symmetric twin of `GolubVanLoan.Chapter05.forwardAccumulation`.

**Reading.** Implements reverse left accumulation for any list, with full updates rather than
exploiting leading identities.
-/
def backwardAccumulation (data : List ((Fin m → ℝ) × ℝ)) : M (Matrix (Fin m) (Fin m) ℝ) :=
  data.reverse.foldlM (fun (Q : Matrix (Fin m) (Fin m) ℝ) p =>
    householderApplyLeft rnd p.1 p.2 (List.finRange m) (List.finRange m) Q) 1

end Programs

/-- In exact arithmetic, the value of $\beta_j$ that the programs of (5.1.4) and (5.1.5) compute is
`GolubVanLoan.Chapter05.recomputedBeta A j`. -/
private theorem recomputed_beta_eq (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n)
    (hj : (j : ℕ) < m) :
    2 / (1 + (0 + ((indexFrom m (j + 1)).map fun i =>
      storedHouseholderVec A j i * storedHouseholderVec A j i).sum)) = recomputedBeta A j := by
  rw [zero_add, recomputedBeta, storedHouseholderVec_dotProduct_self A j hj]

/-- **Equation (5.1.4)** of [golub2013matrix]. Let $n \le m$, $A \in \mathbb{R}^{m \times n}$ and
$C \in \mathbb{R}^{m \times p}$. In exact arithmetic, the program of (5.1.4) returns $Q^T C$,
where $Q$ is the factored form (5.1.3) stored in $A$ with the recomputed values
$\beta_j = 2 / v^{(j)T} v^{(j)}$.

**Correction.** The source recovers $\beta_j = 2 / (1 + \|A(j+1{:}m, j)\|_2^2)$ from the stored
vector. This equals the $\beta_j$ that Algorithm 5.1.1 returned only when that value was
nonzero; when Algorithm 5.1.1 returned $\beta_j = 0$, the recovered value is $2$. The theorem
states the result for the recomputed values, with no condition. These are the reflectors of the
factorization exactly when no $\beta_j$ that Algorithm 5.1.1 returned was $0$.

The recomputed values are `GolubVanLoan.Chapter05.recomputedBeta A`. -/
theorem equation_5_1_4 {p : ℕ} (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ)
    (C : Matrix (Fin m) (Fin p) ℝ) :
    Id.run (factoredQTransposeMul pure A C) = (factoredQ (recomputedBeta A) A)ᵀ * C := by
  rw [factoredQ_eq_prod, ← foldl_mul_eq_transpose_prod_mul _
    (fun j => transpose_one_sub_smul_vecMulVec _ _), factoredQTransposeMul, List.idRun_foldlM]
  congr 1
  funext C j
  simp only [dotAccum_pure, pure_bind]
  rw [householderApplyLeft_spec_of_forall_mem (nodup_indexFrom m j) (List.nodup_finRange p)
    List.mem_finRange (fun i hi => storedHouseholderVec_eq_zero A j hi),
    recomputed_beta_eq A j (by omega)]

/-- If $v$ vanishes at the row $c$ and column $c$ of $X$ is the unit vector $e_c$, then column $c$
of $(I - \beta v v^T) X$ is column $c$ of $X$. -/
private theorem one_sub_smul_vecMulVec_mul_idCols_col {k : ℕ} {v : Fin m → ℝ} {β : ℝ}
    {X : Matrix (Fin m) (Fin k) ℝ} (c : Fin k)
    (hX : ∀ i, X i c = if (i : ℕ) = c then 1 else 0)
    (hv : ∀ i : Fin m, (i : ℕ) = c → v i = 0) (i : Fin m) :
    ((1 - β • vecMulVec v v : Matrix (Fin m) (Fin m) ℝ) * X) i c = X i c := by
  have hdot : v ⬝ᵥ (fun r => X r c) = 0 :=
    Finset.sum_eq_zero fun r _ => by
      change v r * X r c = 0
      rw [hX r]
      split_ifs with h
      · rw [hv r h, zero_mul]
      · rw [mul_zero]
  change ((1 - β • vecMulVec v v) *ᵥ fun r => X r c) i = X i c
  rw [one_sub_smul_vecMulVec_mulVec_apply, hdot, mul_zero, sub_zero]

/-- For any $\beta$ and $k \le m$, the exact loop of (5.1.5), with the update at step $j$ restricted
to the columns $j{:}k$, gives the first $k$ columns of the factored form, because the columns
$< j$ of the partial product $Q_{j+1} \cdots Q_n I_m(:, 1{:}k)$ are columns of the identity,
which $Q_j$ fixes. -/
private theorem foldr_firstColumns_eq {k : ℕ} (hk : k ≤ m) (A : Matrix (Fin m) (Fin n) ℝ)
    (β : Fin n → ℝ) :
    (List.finRange n).foldr (fun (j : Fin n) (X : Matrix (Fin m) (Fin k) ℝ) =>
      of fun i c => if c ∈ indexFrom k j then
        ((1 - β j • vecMulVec (storedHouseholderVec A j) (storedHouseholderVec A j) :
          Matrix (Fin m) (Fin m) ℝ) * X) i c else X i c)
      (of fun i c => if (i : ℕ) = c then 1 else 0) =
      (factoredQ β A).submatrix id (Fin.castLE hk) := by
  set Q : Fin n → Matrix (Fin m) (Fin m) ℝ := fun j =>
    1 - β j • vecMulVec (storedHouseholderVec A j) (storedHouseholderVec A j) with hQ
  set I : Matrix (Fin m) (Fin k) ℝ := of fun i c => if (i : ℕ) = c then 1 else 0 with hI
  have key : ∀ l : List (Fin n), l.Pairwise (· < ·) →
      l.foldr (fun (j : Fin n) (X : Matrix (Fin m) (Fin k) ℝ) =>
        of fun i c => if c ∈ indexFrom k j then (Q j * X) i c else X i c) I =
        (l.map Q).prod * I := by
    intro l hl
    induction l with
    | nil => simp
    | cons a l ih =>
      rw [List.pairwise_cons] at hl
      rw [List.foldr_cons, ih hl.2, List.map_cons, List.prod_cons, Matrix.mul_assoc]
      ext i c
      rw [of_apply]
      split_ifs with hc
      · rfl
      · -- column `c < a`: every reflector of the product fixes it
        rw [mem_indexFrom, not_le] at hc
        have hfix : ∀ l' : List (Fin n), (∀ b ∈ l', a < b) →
            ∀ i, ((l'.map Q).prod * I) i c = I i c := by
          intro l' hl'
          induction l' with
          | nil => intro i; simp
          | cons b l' ih' =>
            intro i
            rw [List.map_cons, List.prod_cons, Matrix.mul_assoc,
              one_sub_smul_vecMulVec_mul_idCols_col c
                (fun r => ih' (fun b' hb' => hl' b' (List.mem_cons_of_mem _ hb')) r)
                (fun r hr => storedHouseholderVec_eq_zero A b (by
                  rw [mem_indexFrom, not_le, hr]
                  exact lt_trans hc (hl' b List.mem_cons_self)))]
            exact ih' (fun b' hb' => hl' b' (List.mem_cons_of_mem _ hb')) i
        rw [one_sub_smul_vecMulVec_mul_idCols_col c (hfix l hl.1)
          (fun r hr => storedHouseholderVec_eq_zero A a (by
            rw [mem_indexFrom, not_le, hr]; exact hc))]
  rw [key (List.finRange n) (List.sortedLT_finRange n).pairwise, factoredQ_eq_prod]
  ext i c
  simp only [Matrix.mul_apply, hI, of_apply, submatrix_apply, id]
  rw [Finset.sum_eq_single (Fin.castLE hk c)]
  · simp only [Fin.val_castLE, ↓reduceIte, mul_one]
    rfl
  · intro r _ hr
    have : ¬ ((r : ℕ) = c) := fun h => hr (Fin.ext h)
    simp [this]
  · simp

/-- **Equation (5.1.5)** of [golub2013matrix]. Let $k \le m$, $n \le m$ and
$A \in \mathbb{R}^{m \times n}$. In exact arithmetic, the program of (5.1.5) returns the first
$k$ columns $Q(:, 1{:}k)$ of the factored form $Q$ stored in $A$, with the recomputed values
$\beta_j = 2 / v^{(j)T} v^{(j)}$.

**Correction.** As in (5.1.4), the source recovers $\beta_j = 2 / (1 + \|A(j+1{:}m, j)\|_2^2)$
from the stored vector, and this value is $2$ when Algorithm 5.1.1 returned $\beta_j = 0$. The
theorem states the result for the recomputed values. The first columns of $Q$ with the returned
values are `GolubVanLoan.Chapter05.storedQFirstColumns_spec`.

The first $k$ columns are `(factoredQ (recomputedBeta A) A).submatrix id (Fin.castLE hk)`. -/
theorem equation_5_1_5 {k : ℕ} (hk : k ≤ m) (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (factoredQFirstColumns pure A k) =
      (factoredQ (recomputedBeta A) A).submatrix id (Fin.castLE hk) := by
  have hstep : ∀ (j : Fin n) (X : Matrix (Fin m) (Fin k) ℝ),
      Id.run (do
        let s ← dotAccum pure (indexFrom m (j + 1)) (storedHouseholderVec A j)
          (storedHouseholderVec A j) 0
        let β ← pure (2 / (← pure (1 + s)))
        householderApplyLeft pure (storedHouseholderVec A j) β (indexFrom m j) (indexFrom k j) X) =
        of fun i c => if c ∈ indexFrom k j then
          ((1 - recomputedBeta A j • vecMulVec (storedHouseholderVec A j)
            (storedHouseholderVec A j) : Matrix (Fin m) (Fin m) ℝ) * X) i c else X i c := by
    intro j X
    simp only [dotAccum_pure, pure_bind]
    rw [householderApplyLeft_spec (nodup_indexFrom m j) (nodup_indexFrom k j)
      (fun i hi => storedHouseholderVec_eq_zero A j hi), recomputed_beta_eq A j (by omega)]
  rw [factoredQFirstColumns, List.foldlM_reverse, List.idRun_foldrM]
  simp only [hstep]
  exact foldr_firstColumns_eq hk A _

/-- **Equation (5.1.5)** of [golub2013matrix] with the returned $\beta$. Let $k \le m$,
$A \in \mathbb{R}^{m \times n}$ and $\beta \in \mathbb{R}^n$. In exact arithmetic,
`GolubVanLoan.Chapter05.storedQFirstColumns` returns the first $k$ columns of the factored form
$Q = Q_1 \cdots Q_n$, $Q_j = I - \beta_j v^{(j)} v^{(j)T}$, stored in $A$. There is no condition
on $\beta$.

**Reading.** Exact first columns of product with supplied rather than recomputed beta.
-/
theorem storedQFirstColumns_spec {k : ℕ} (hk : k ≤ m) (A : Matrix (Fin m) (Fin n) ℝ)
    (β : Fin n → ℝ) :
    Id.run (storedQFirstColumns pure A β k) = (factoredQ β A).submatrix id (Fin.castLE hk) := by
  have hstep : ∀ (j : Fin n) (X : Matrix (Fin m) (Fin k) ℝ),
      Id.run (householderApplyLeft pure (storedHouseholderVec A j) (β j) (indexFrom m j)
        (indexFrom k j) X) =
        of fun i c => if c ∈ indexFrom k j then
          ((1 - β j • vecMulVec (storedHouseholderVec A j)
            (storedHouseholderVec A j) : Matrix (Fin m) (Fin m) ℝ) * X) i c else X i c :=
    fun j X => householderApplyLeft_spec (nodup_indexFrom m j) (nodup_indexFrom k j)
      (fun i hi => storedHouseholderVec_eq_zero A j hi) _ X
  rw [storedQFirstColumns, List.foldlM_reverse, List.idRun_foldrM]
  simp only [hstep]
  exact foldr_firstColumns_eq hk A β

/-- **Section 5.1.6** of [golub2013matrix], forward accumulation, exact semantics. For reflector
data $[(v_1, \beta_1), \dots, (v_r, \beta_r)]$, forward accumulation in exact arithmetic returns
$Q = Q_1 \cdots Q_r$, $Q_j = I - \beta_j v_j v_j^T$.

**Reading.** Right accumulation for any list of rank-one update data.
-/
theorem forwardAccumulation_spec (data : List ((Fin m → ℝ) × ℝ)) :
    Id.run (forwardAccumulation pure data) = householderProduct data := by
  have key : ∀ Q₀ : Matrix (Fin m) (Fin m) ℝ,
      Id.run (data.foldlM (fun (Q : Matrix (Fin m) (Fin m) ℝ) p =>
        householderApplyRight pure p.1 p.2 (List.finRange m) (List.finRange m) Q) Q₀) =
        Q₀ * householderProduct data := by
    induction data with
    | nil => intro Q₀; simp
    | cons p data ih =>
      intro Q₀
      rw [List.foldlM_cons]
      change Id.run (data.foldlM _ (Id.run (householderApplyRight pure p.1 p.2
        (List.finRange m) (List.finRange m) Q₀))) = _
      rw [ih, householderApplyRight_spec_of_forall_mem (List.nodup_finRange m)
        (List.nodup_finRange m) List.mem_finRange (fun j hj => absurd (List.mem_finRange j) hj),
        householderProduct_cons, Matrix.mul_assoc]
  rw [forwardAccumulation, key, Matrix.one_mul]

/-- **Section 5.1.6** of [golub2013matrix], backward accumulation, exact semantics. For reflector
data $[(v_1, \beta_1), \dots, (v_r, \beta_r)]$, backward accumulation in exact arithmetic
returns $Q = Q_1 \cdots Q_r$, $Q_j = I - \beta_j v_j v_j^T$.

**Reading.** Reverse left accumulation for any list of rank-one update data.
-/
theorem backwardAccumulation_spec (data : List ((Fin m → ℝ) × ℝ)) :
    Id.run (backwardAccumulation pure data) = householderProduct data := by
  have key : ∀ Q₀ : Matrix (Fin m) (Fin m) ℝ,
      Id.run (data.reverse.foldlM (fun (Q : Matrix (Fin m) (Fin m) ℝ) p =>
        householderApplyLeft pure p.1 p.2 (List.finRange m) (List.finRange m) Q) Q₀) =
        householderProduct data * Q₀ := by
    intro Q₀
    rw [List.idRun_foldlM, List.foldl_reverse]
    induction data with
    | nil => simp
    | cons p data ih =>
      rw [List.foldr_cons, ih, householderApplyLeft_spec_of_forall_mem (List.nodup_finRange m)
        (List.nodup_finRange m) List.mem_finRange (fun j hj => absurd (List.mem_finRange j) hj),
        householderProduct_cons, Matrix.mul_assoc]
  rw [backwardAccumulation, key, Matrix.mul_one]

end FactoredForm


/-! ### §5.1.7 The WY representation -/

section WY

variable {m : ℕ}

/-- The product of reflector data indexed by `Fin r` is the backbone's product
$\prod_j (I - \beta_j v_j v_j^*)$ over $\mathbb{R}$, in which the transpose is written with
`star`. -/
theorem householderProduct_ofFn {r : ℕ} (β : Fin r → ℝ) (v : Fin r → Fin m → ℝ) :
    householderProduct (List.ofFn fun j => (v j, β j)) =
      (List.ofFn fun j => 1 - β j • vecMulVec (v j) (star (v j))).prod := by
  simp [householderProduct, List.map_ofFn, Function.comp_def]

/-- **Equation (5.1.6)** of [golub2013matrix]. Let $v_1, \dots, v_r \in \mathbb{R}^m$ and
$\beta_1, \dots, \beta_r \in \mathbb{R}$. The product $Q = Q_1 \cdots Q_r$ with
$Q_j = I - \beta_j v_j v_j^T$ has the form
$$Q = I_m - W Y^T$$
for some $W, Y \in \mathbb{R}^{m \times r}$. In particular, a product of $r$ Householder
matrices is a rank-$r$ modification of the identity.

The statement holds for any rank-one modifications $Q_j$ of the identity, not only for
Householder matrices.

**Generalization.** The WY representation holds for any product of rank-one updates of the
displayed shape, including nonorthogonal factors and an empty product. -/
theorem equation_5_1_6 {r : ℕ} (β : Fin r → ℝ) (v : Fin r → Fin m → ℝ) :
    ∃ W Y : Matrix (Fin m) (Fin r) ℝ,
      householderProduct (List.ofFn fun j => (v j, β j)) = 1 - W * Yᵀ := by
  refine ⟨wyW β v, of fun i j => v j i, ?_⟩
  rw [householderProduct_ofFn, ← conjTranspose_eq_transpose_of_trivial]
  exact isWY_prod β v

/-- **Lemma 5.1.1** of [golub2013matrix]. Let $Q = I_m - W Y^T$ with
$W, Y \in \mathbb{R}^{m \times j}$, let $P = I_m - \beta v v^T$ with $v \in \mathbb{R}^m$ and
$\beta \in \mathbb{R}$, and let $z = \beta Q v$. Then
$$Q_+ = Q P = I_m - W_+ Y_+^T, \qquad W_+ = [\, W \mid z \,], \quad Y_+ = [\, Y \mid v \,].$$

**Generalization.** The source assumes that $Q$ is orthogonal. The identity holds without this
assumption.

The new last columns are appended with `Fin.snoc`. -/
theorem lemma_5_1_1 {j : ℕ} {Q : Matrix (Fin m) (Fin m) ℝ} {W Y : Matrix (Fin m) (Fin j) ℝ}
    (hQ : Q = 1 - W * Yᵀ) (β : ℝ) (v : Fin m → ℝ) :
    Q * (1 - β • vecMulVec v v) =
      1 - (of fun i => Fin.snoc (W i) ((β • (Q *ᵥ v)) i) : Matrix (Fin m) (Fin (j + 1)) ℝ) *
        (of fun i => Fin.snoc (Y i) (v i) : Matrix (Fin m) (Fin (j + 1)) ℝ)ᵀ := by
  have h : IsWY Q W Y := by rw [IsWY, conjTranspose_eq_transpose_of_trivial]; exact hQ
  have := h.mul_one_sub_smul_vecMulVec β v
  rw [IsWY, conjTranspose_eq_transpose_of_trivial, star_trivial] at this
  exact this

/-- One step of Algorithm 5.1.2, which fills column $j$ of $W$ and $Y$. With $v = v^{(j)}$,
$\beta = \beta_j$ and the previous columns $k < j$, the step computes $t = Y(:, 1{:}j-1)^T v$ by
Algorithm 1.1.1 for each column, then $z_i = \mathrm{fl}(\beta\, \mathrm{fl}(v_i - W(i,
1{:}j-1)\, t))$ with the inner product accumulated and rounded, and sets $W(:, j) = z$ and
$Y(:, j) = v$. At the first step there are no previous columns, and
$z_i = \mathrm{fl}(\beta v_i)$: the source's $W = \beta_1 v^{(1)}$, with one rounding per entry
and no subtraction. -/
noncomputable def wyStep {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)
    (data : List ((Fin m → ℝ) × ℝ))
    (st : Matrix (Fin m) (Fin data.length) ℝ × Matrix (Fin m) (Fin data.length) ℝ)
    (j : Fin data.length) :
    M (Matrix (Fin m) (Fin data.length) ℝ × Matrix (Fin m) (Fin data.length) ℝ) := do
  let v := (data.get j).1
  let β := (data.get j).2
  let prev := (List.finRange data.length).filter (· < j)
  let t ← prev.foldlM (fun (t : Fin data.length → ℝ) k => do
    let d ← Chapter01.algorithm_1_1_1 rnd (fun i => st.2 i k) v
    pure (Function.update t k d)) 0
  let z ← (List.finRange m).foldlM (fun (z : Fin m → ℝ) i => do
    let wt ← dotAccum rnd prev (st.1 i) t 0
    let d ← if prev = [] then pure (v i) else rnd (v i - wt)
    let b ← rnd (β * d)
    pure (Function.update z i b)) 0
  pure (st.1.updateCol j z, st.2.updateCol j v)

/-- **Algorithm 5.1.2** of [golub2013matrix] (the WY representation from the factored form). For
reflector data $[(v^{(1)}, \beta_1), \dots, (v^{(r)}, \beta_r)]$ the algorithm computes
$W, Y \in \mathbb{R}^{m \times r}$:
```
Y = v⁽¹⁾; W = β₁ v⁽¹⁾
for j = 2:r
    z = β_j (I_m - W Yᵀ) v⁽ʲ⁾
    W = [W | z];  Y = [Y | v⁽ʲ⁾]
end
```
The arrays $W$ and $Y$ have size $m \times r$ from the start, and the columns that are not yet
filled are zero. Step $j$ writes column $j$ (`GolubVanLoan.Chapter05.wyStep`), and the first
step forms $\beta_1 v^{(1)}$ directly. The product $(I - W Y^T) v$ is formed as $v - W (Y^T v)$
over the previous columns.

**Generalization.** The first step uses the same recurrence as the later steps, starting with
empty prefixes. This also defines the result when the input contains no reflectors. -/
noncomputable def algorithm_5_1_2 {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)
    (data : List ((Fin m → ℝ) × ℝ)) :
    M (Matrix (Fin m) (Fin data.length) ℝ × Matrix (Fin m) (Fin data.length) ℝ) :=
  (List.finRange data.length).foldlM (wyStep rnd data) (0, 0)

/-- If the columns $\ge j$ of $W$ are zero, the exact step $j$ of Algorithm 5.1.2 sets
$W(:, j) = \beta_j (I - W Y^T) v^{(j)}$ and $Y(:, j) = v^{(j)}$. -/
private theorem wyStep_pure (data : List ((Fin m → ℝ) × ℝ))
    (W Y : Matrix (Fin m) (Fin data.length) ℝ) (j : Fin data.length)
    (hW : ∀ i (k : Fin data.length), j ≤ k → W i k = 0) :
    Id.run (wyStep pure data (W, Y) j) =
      (W.updateCol j ((data.get j).2 • ((1 - W * Yᵀ) *ᵥ (data.get j).1)),
        Y.updateCol j (data.get j).1) := by
  set v := (data.get j).1
  set β := (data.get j).2
  set prev := (List.finRange data.length).filter (· < j) with hprev
  by_cases hp : prev = []
  · -- the first step: no previous columns, and `W = 0`
    have hj : ∀ k : Fin data.length, j ≤ k := fun k => by
      by_contra h
      have hk : k ∈ prev := by rw [hprev]; simpa using not_le.1 h
      rw [hp] at hk
      exact List.not_mem_nil hk
    have hW0 : W = 0 := by ext i k; exact hW i k (hj k)
    subst hW0
    simp only [wyStep, Id.run_bind, Id.run_pure, List.idRun_foldlM, ← hprev, hp, ↓reduceIte]
    rw [List.foldl_update_eq_ite]
    congr 2
    funext i
    simp
    rfl
  simp only [wyStep, Id.run_bind, Id.run_pure, List.idRun_foldlM,
    Chapter01.algorithm_1_1_1_spec, dotAccum_id, ← hprev, hp, ↓reduceIte]
  rw [List.foldl_update_eq_ite, List.foldl_update_eq_ite]
  congr 2
  funext i
  simp only [List.mem_finRange, ↓reduceIte, zero_add, Pi.smul_apply, smul_eq_mul, sub_mulVec,
    one_mulVec, Pi.sub_apply, ← mulVec_mulVec]
  congr 2
  refine (sum_eq_sum_map_of_nodup ((List.nodup_finRange _).filter _)
    (f := fun k => W i k * (if k ∈ prev then (fun r => Y r k) ⬝ᵥ v
      else (0 : Fin data.length → ℝ) k)) fun k hk => ?_).symm.trans ?_
  · have hk' : k ∉ prev := hk
    simp only [hk', ↓reduceIte, Pi.zero_apply, mul_zero]
  · change _ = ∑ k, W i k * (Yᵀ *ᵥ v) k
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k ∈ prev
    · simp only [hk, ↓reduceIte]; rfl
    · simp only [hk, ↓reduceIte, Pi.zero_apply, mul_zero]
      rw [hW i k (by simpa [hprev] using hk), zero_mul]

/-- **Algorithm 5.1.2** of [golub2013matrix], exact semantics. For reflector data $[(v^{(1)},
\beta_1), \dots, (v^{(r)}, \beta_r)]$ in $\mathbb{R}^m$, the output $(W, Y)$ of Algorithm 5.1.2
in exact arithmetic satisfies
$$Q_1 \cdots Q_r = I_m - W Y^T, \qquad Q_j = I - \beta_j v^{(j)} v^{(j)T},$$
and column $k$ of $Y$ is $v^{(k)}$ for every $k$.

In the words of the source, $Y$ is merely the matrix of Householder vectors; for vectors of the
shape (5.1.3) it is unit lower triangular.

**Reading.** Proves WY and Y-column identities for general data, including no reflectors.
-/
theorem algorithm_5_1_2_spec (data : List ((Fin m → ℝ) × ℝ)) :
    householderProduct data =
        1 - (Id.run (algorithm_5_1_2 pure data)).1 * (Id.run (algorithm_5_1_2 pure data)).2ᵀ ∧
      ∀ i k, (Id.run (algorithm_5_1_2 pure data)).2 i k = (data.get k).1 i := by
  set R := data.length with hR
  set f := fun st j => Id.run (wyStep pure data st j) with hf
  -- the invariant after the first `j` steps
  set I : ℕ → Matrix (Fin m) (Fin R) ℝ × Matrix (Fin m) (Fin R) ℝ → Prop := fun j st =>
    (∀ i (k : Fin R), j ≤ k → st.1 i k = 0 ∧ st.2 i k = 0) ∧
      (∀ i (k : Fin R), (k : ℕ) < j → st.2 i k = (data.get k).1 i) ∧
      1 - st.1 * st.2ᵀ = householderProduct (data.take j) with hI
  have hstep : ∀ st (j : Fin R), I j st → I (j + 1) (f st j) := by
    rintro ⟨W, Y⟩ j ⟨hz, hY, hQ⟩
    simp only [hf]
    rw [wyStep_pure data W Y j fun i k hk => (hz i k hk).1]
    refine ⟨fun i k hk => ?_, fun i k hk => ?_, ?_⟩
    · have hkj : k ≠ j := fun e => by rw [e] at hk; omega
      simp only [updateCol_ne hkj]
      exact hz i k (by omega)
    · by_cases hkj : k = j
      · subst hkj; simp
      · simp only [updateCol_ne hkj]
        exact hY i k (by
          rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
          · exact h
          · exact absurd (Fin.ext h) hkj)
    · have htake : data.take (j + 1) = data.take j ++ [data.get j] := by
        rw [List.take_succ_eq_append_getElem j.isLt]
        rfl
      rw [htake, householderProduct_concat, ← hQ]
      set v := (data.get j).1
      set β := (data.get j).2
      -- `W' Y'ᵀ = W Yᵀ + z vᵀ`, since column `j` of `W` and of `Y` is zero
      have hWY : (W.updateCol j (β • ((1 - W * Yᵀ) *ᵥ v))) * (Y.updateCol j v)ᵀ =
          W * Yᵀ + vecMulVec (β • ((1 - W * Yᵀ) *ᵥ v)) v := by
        ext a b
        simp only [Matrix.mul_apply, Matrix.add_apply, transpose_apply, updateCol_apply,
          vecMulVec_apply]
        have hpt : ∀ k, (if k = j then (β • ((1 - W * Yᵀ) *ᵥ v)) a else W a k) *
            (if k = j then v b else Y b k) =
              W a k * Y b k + if k = j then (β • ((1 - W * Yᵀ) *ᵥ v)) a * v b else 0 := by
          intro k
          by_cases hk : k = j
          · subst hk
            have h0 : W a k = 0 := (hz a k le_rfl).1
            simp [h0]
          · simp [hk]
        simp only [hpt, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
          ↓reduceIte]
      rw [hWY, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, mul_vecMulVec, ← sub_sub,
        smul_vecMulVec]
  have hinit : I 0 (0, 0) := ⟨fun i k _ => ⟨rfl, rfl⟩, fun i k hk => absurd hk (Nat.not_lt_zero _),
    by simp⟩
  have hall : ∀ j ≤ R, I j (((List.finRange R).take j).foldl f (0, 0)) := by
    intro j
    induction j with
    | zero => intro _; simpa using hinit
    | succ j ih =>
      intro hj
      rw [List.take_succ_eq_append_getElem (by simpa using hj), List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      have h := hstep _ ⟨j, by omega⟩ (ih (by omega))
      simpa using h
  obtain ⟨-, hY, hQ⟩ := hall R le_rfl
  rw [List.take_of_length_le (by simp)] at hY hQ
  have hprog : Id.run (algorithm_5_1_2 pure data) = (List.finRange R).foldl f (0, 0) := by
    rw [algorithm_5_1_2, List.idRun_foldlM]
  rw [hprog]
  rw [List.take_of_length_le (le_of_eq hR.symm)] at hQ
  exact ⟨hQ.symm, fun i k => hY i k k.2⟩

/-- **Section 5.1.7** of [golub2013matrix], block reflectors. Let $V \in \mathbb{R}^{m \times r}$
with $V^T V = I_r$. Then $Q = I - 2 V V^T$ is orthogonal. The source calls such matrices true
block reflectors. -/
theorem blockReflector_mem_orthogonalGroup {r : ℕ} {V : Matrix (Fin m) (Fin r) ℝ}
    (hV : Vᵀ * V = 1) : 1 - (2 : ℝ) • (V * Vᵀ) ∈ orthogonalGroup (Fin m) ℝ := by
  have := one_sub_two_mul_conjTranspose_mem_unitaryGroup (R := ℝ)
    (V := V) (by rwa [conjTranspose_eq_transpose_of_trivial])
  rwa [conjTranspose_eq_transpose_of_trivial] at this

end WY

/-! ### §5.1.8–5.1.10 Givens rotations -/

section Givens

variable {m n : ℕ}

/-- **Equation (5.1.7)** of [golub2013matrix], the Givens rotation. For indices $i$, $k$ and
$c, s \in \mathbb{R}$, the matrix $G(i, k, \theta)$ is the identity except for the entries
$$g_{ii} = g_{kk} = c, \qquad g_{ik} = s, \qquad g_{ki} = -s,$$
where $c = \cos\theta$ and $s = \sin\theta$.

The backbone's `Matrix.planeRotation i k c s` has the rows $(c, -s)$ and $(s, c)$ in the plane
of the coordinates $i$ and $k$, so $G(i, k, \theta)$ is `Matrix.planeRotation i k c (-s)`. The
definition takes $c$ and $s$ directly and does not assume $c^2 + s^2 = 1$. The results below
assume $i \neq k$.

**Reading.** Definition accepts arbitrary c,s and coincident indices; orthogonality theorem imposes
distinct indices and unit pair.
-/
def givensRotation (i k : Fin m) (c s : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  planeRotation i k c (-s)

/-- **Section 5.1.8** of [golub2013matrix], orthogonality. Let $i \neq k$ and $c^2 + s^2 = 1$. Then
the Givens rotation $G(i, k, \theta)$ is orthogonal. The source says that Givens rotations are
clearly orthogonal. -/
theorem givensRotation_mem_orthogonalGroup {i k : Fin m} (hik : i ≠ k) {c s : ℝ}
    (hcs : c ^ 2 + s ^ 2 = 1) : givensRotation i k c s ∈ orthogonalGroup (Fin m) ℝ :=
  planeRotation_mem_orthogonalGroup hik (by rwa [neg_sq])

/-- **Section 5.1.8** of [golub2013matrix], the action of $G(i, k, \theta)^T$. Let $i \neq k$. The
vector $y = G(i, k, \theta)^T x$ has $y_i = c x_i - s x_k$, $y_k = s x_i + c x_k$, and
$y_j = x_j$ for every other $j$. -/
theorem givensRotation_transpose_mulVec_apply {i k : Fin m} (hik : i ≠ k) (c s : ℝ)
    (x : Fin m → ℝ) (p : Fin m) :
    ((givensRotation i k c s)ᵀ *ᵥ x) p =
      if p = i then c * x i - s * x k else if p = k then s * x i + c * x k else x p := by
  rw [givensRotation, transpose_planeRotation_mulVec_apply hik]
  split_ifs <;> ring

/-- **Equation (5.1.8)** of [golub2013matrix]. Let $i \neq k$ and $x \in \mathbb{R}^m$ with
$x_i \neq 0$ or $x_k \neq 0$, and let
$$c = \frac{x_i}{\sqrt{x_i^2 + x_k^2}}, \qquad s = \frac{-x_k}{\sqrt{x_i^2 + x_k^2}}.$$
Then $y = G(i, k, \theta)^T x$ has $y_k = 0$ and $y_i = \sqrt{x_i^2 + x_k^2}$.

**Reading.** The denominator is nonzero when at least one of the two selected components is
nonzero. The theorem also states the resulting first component. -/
theorem equation_5_1_8 {i k : Fin m} (hik : i ≠ k) (x : Fin m → ℝ) (hx : x i ≠ 0 ∨ x k ≠ 0) :
    ((givensRotation i k (x i / √(x i ^ 2 + x k ^ 2)) (-x k / √(x i ^ 2 + x k ^ 2)))ᵀ *ᵥ x) k
        = 0 ∧
      ((givensRotation i k (x i / √(x i ^ 2 + x k ^ 2)) (-x k / √(x i ^ 2 + x k ^ 2)))ᵀ *ᵥ x) i
        = √(x i ^ 2 + x k ^ 2) := by
  have hpos : 0 < x i ^ 2 + x k ^ 2 := by
    rcases hx with h | h
    · have := pow_pos (abs_pos.2 h) 2; rw [sq_abs] at this; positivity
    · have := pow_pos (abs_pos.2 h) 2; rw [sq_abs] at this; positivity
  have hr : √(x i ^ 2 + x k ^ 2) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  have hsq := Real.sq_sqrt hpos.le
  rw [givensRotation_transpose_mulVec_apply hik, givensRotation_transpose_mulVec_apply hik,
    ite_eq_right hik.symm, ite_eq_left rfl, ite_eq_left rfl]
  constructor
  · field_simp
    ring
  · field_simp
    nlinarith [hsq, Real.sqrt_nonneg (x i ^ 2 + x k ^ 2)]

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 5.1.3** of [golub2013matrix] (`givens`). Given scalars $a$ and $b$, the algorithm
computes $c = \cos\theta$ and $s = \sin\theta$ such that
$$\begin{bmatrix} c & s \\ -s & c \end{bmatrix}^T \begin{bmatrix} a \\ b \end{bmatrix} =
  \begin{bmatrix} r \\ 0 \end{bmatrix}:$$
```
if b = 0:           c = 1; s = 0
elseif |b| > |a|:   τ = -a/b; s = 1/√(1 + τ²); c = s τ
else                τ = -b/a; c = 1/√(1 + τ²); s = c τ
```
The comparisons act on the inputs and are exact; every arithmetic result is rounded. -/
noncomputable def algorithm_5_1_3 (a b : ℝ) : M (ℝ × ℝ) :=
  if b = 0 then pure (1, 0)
  else if |b| > |a| then do
    let τ ← rnd (-a / b)
    let s ← rnd (1 / (← rnd √(← rnd (1 + (← rnd (τ * τ))))))
    let c ← rnd (s * τ)
    pure (c, s)
  else do
    let τ ← rnd (-b / a)
    let c ← rnd (1 / (← rnd √(← rnd (1 + (← rnd (τ * τ))))))
    let s ← rnd (c * τ)
    pure (c, s)

/-- One computed rotation of the entries $i$ and $k$ of a vector $x$, the loop body of §5.1.9: from
the old values, $x_i \leftarrow \mathrm{fl}(\mathrm{fl}(c x_i) - \mathrm{fl}(s x_k))$ and $x_k
\leftarrow \mathrm{fl}(\mathrm{fl}(s x_i) + \mathrm{fl}(c x_k))$. -/
def givensRotateVec {p : ℕ} (i k : Fin p) (c s : ℝ) (x : Fin p → ℝ) : M (Fin p → ℝ) := do
  let y₁ ← rnd ((← rnd (c * x i)) - (← rnd (s * x k)))
  let y₂ ← rnd ((← rnd (s * x i)) + (← rnd (c * x k)))
  pure (Function.update (Function.update x i y₁) k y₂)

/-- **Section 5.1.9** of [golub2013matrix], the row update $A([i, k], \mathrm{cols}) = G(i, k,
\theta)^T A([i, k], \mathrm{cols})$, in place on the full matrix. For each $j$ in the list
`cols`, with $\tau_1 = a_{ij}$ and $\tau_2 = a_{kj}$, the program sets
$$a_{ij} = c \tau_1 - s \tau_2, \qquad a_{kj} = s \tau_1 + c \tau_2,$$
with each product and each sum rounded.

**Reading.** Updates selected columns instead of all columns.
-/
def givensApplyLeft (i k : Fin m) (c s : ℝ) (cols : List (Fin n))
    (A : Matrix (Fin m) (Fin n) ℝ) : M (Matrix (Fin m) (Fin n) ℝ) :=
  cols.foldlM (fun (A : Matrix (Fin m) (Fin n) ℝ) q => do
    let y ← givensRotateVec rnd i k c s (fun r => A r q)
    pure (A.updateCol q y)) A

/-- **Section 5.1.9** of [golub2013matrix], the column update $A(\mathrm{rows}, [i, k]) =
A(\mathrm{rows}, [i, k])\, G(i, k, \theta)$, in place on the full matrix. For each $r$ in the
list `rows`, with $\tau_1 = a_{ri}$ and $\tau_2 = a_{rk}$, the program sets
$$a_{ri} = c \tau_1 - s \tau_2, \qquad a_{rk} = s \tau_1 + c \tau_2,$$
with each product and each sum rounded.

This is the symmetric twin of `GolubVanLoan.Chapter05.givensApplyLeft`.

**Reading.** Updates selected rows instead of all rows.
-/
def givensApplyRight (i k : Fin n) (c s : ℝ) (rows : List (Fin m))
    (A : Matrix (Fin m) (Fin n) ℝ) : M (Matrix (Fin m) (Fin n) ℝ) :=
  rows.foldlM (fun (A : Matrix (Fin m) (Fin n) ℝ) r => do
    let y ← givensRotateVec rnd i k c s (A r)
    pure (A.updateRow r y)) A

/-- **Section 6.5.4** of [golub2013matrix], a hyperbolic rotation applied to two rows. For rows $i$
and $k$ of a matrix $S$, scalars $c$ and $s$, and a list `cols` of columns, the program applies
$\begin{bmatrix} c & -s \\ -s & c \end{bmatrix}$ to the rows $i$ and $k$ in the listed columns,
in place. For each $j$ in `cols`, from the old values,
$$S(i, j) \leftarrow c\, S(i, j) - s\, S(k, j), \qquad S(k, j) \leftarrow c\, S(k, j) - s\, S(i,
  j),$$
with every product and every difference rounded.

This is the hyperbolic counterpart of the Givens row update
`GolubVanLoan.Chapter05.givensApplyLeft`. Its exact semantics is
`GolubVanLoan.Chapter05.hyperbolicApplyLeft_spec`.

**Reading.** General row type and selected columns, with both off-diagonal signs negative.
-/
def hyperbolicApplyLeft {ι : Type} [DecidableEq ι] {n : ℕ} (i k : ι) (c s : ℝ)
    (cols : List (Fin n)) (S : Matrix ι (Fin n) ℝ) : M (Matrix ι (Fin n) ℝ) :=
  cols.foldlM (fun (S : Matrix ι (Fin n) ℝ) (j : Fin n) => do
    let x ← rnd ((← rnd (c * S i j)) - (← rnd (s * S k j)))
    let y ← rnd ((← rnd (c * S k j)) - (← rnd (s * S i j)))
    pure ((S.updateRow i (Function.update (S i) j x)).updateRow k
      (Function.update (S k) j y))) S

end Programs

/-- For $i \neq i'$, the exact rotation of the entries $i$ and $i'$ of $x$ is
$G(i, i', \theta)^T x$. -/
theorem givensRotateVec_pure {N : ℕ} {i i' : Fin N} (hii' : i ≠ i') (c s : ℝ) (x : Fin N → ℝ) :
    Id.run (givensRotateVec pure i i' c s x) = (givensRotation i i' c s)ᵀ *ᵥ x := by
  ext t
  rw [givensRotation_transpose_mulVec_apply hii']
  simp only [givensRotateVec, Id.run_bind, Id.run_pure]
  by_cases hti' : t = i'
  · subst hti'
    rw [Function.update_self, ite_eq_right (Ne.symm hii'), ite_eq_left rfl]
  · rw [Function.update_of_ne hti']
    by_cases hti : t = i
    · subst hti
      rw [Function.update_self, ite_eq_left rfl]
    · rw [Function.update_of_ne hti, ite_eq_right hti, ite_eq_right hti']

variable {fp : RoundingModel ℝ}

/-- **Algorithm 5.1.3** of [golub2013matrix], rounding bridge. Let $a, b \in \mathbb{R}$. Every
result $(\hat c, \hat s)$ of Algorithm 5.1.3 in the rounding model is a computed pair of the
$\tau$-formula: $(\hat c, \hat s) = (1, 0)$ if $b = 0$; if $|a| < |b|$, then $\hat\tau$ is a
rounding of $-a/b$, $\hat s$ comes from $\hat\tau$ by rounding $\hat\tau^2$, $1 + \hat\tau^2$,
the square root and the reciprocal in turn, and $\hat c$ is a rounding of $\hat s \hat\tau$;
otherwise the same holds with $a, b$ and $c, s$ exchanged.

The relation is `FloatingPoint.RoundsGivensPair`. It needs no hypothesis on the rounding model. -/
theorem algorithm_5_1_3_rounds (a b : ℝ) {cs : ℝ × ℝ}
    (h : cs ∈ (algorithm_5_1_3 fp.round a b).run) : RoundsGivensPair fp a b cs.1 cs.2 := by
  unfold algorithm_5_1_3 at h
  split_ifs at h with hb hab
  · rw [SetM.mem_run_pure] at h
    subst h
    exact Or.inl ⟨hb, rfl, rfl⟩
  · simp only [SetM.mem_run_bind, RoundingModel.mem_run_round, SetM.mem_run_pure] at h
    obtain ⟨τ, hτ, t₁, h₁, t₂, h₂, r, hr, s, hs, c, hc, rfl⟩ := h
    exact Or.inr (Or.inl ⟨hab, τ, t₁, t₂, r, hτ, h₁, h₂, hr, hs, hc⟩)
  · simp only [SetM.mem_run_bind, RoundingModel.mem_run_round, SetM.mem_run_pure] at h
    obtain ⟨τ, hτ, t₁, h₁, t₂, h₂, r, hr, c, hc, s, hs, rfl⟩ := h
    exact Or.inr (Or.inr ⟨hb, not_lt.1 hab, τ, t₁, t₂, r, hτ, h₁, h₂, hr, hc, hs⟩)

private theorem algorithm_5_1_3_mem_exact (a b : ℝ) :
    Id.run (algorithm_5_1_3 pure a b) ∈
      (algorithm_5_1_3 (RoundingModel.exact ℝ).round a b).run := by
  rw [RoundingModel.round_exact]
  unfold algorithm_5_1_3
  split_ifs <;> simp only [pure_bind, SetM.mem_run_pure] <;> rfl

/-- **Algorithm 5.1.3** of [golub2013matrix], exact semantics. Let $a, b \in \mathbb{R}$. In exact
arithmetic, the output $(c, s)$ of Algorithm 5.1.3 satisfies $c^2 + s^2 = 1$ and
$$\begin{bmatrix} c & s \\ -s & c \end{bmatrix}^T \begin{bmatrix} a \\ b \end{bmatrix} =
  \begin{bmatrix} r \\ 0 \end{bmatrix}, \qquad |r| = \sqrt{a^2 + b^2},$$
that is, $s a + c b = 0$ and $r = c a - s b$.

The sign of $r$ is not controlled; the source treats it in Problem P5.1.11. -/
theorem algorithm_5_1_3_spec (a b : ℝ) :
    (Id.run (algorithm_5_1_3 pure a b)).1 ^ 2 + (Id.run (algorithm_5_1_3 pure a b)).2 ^ 2 = 1 ∧
      (Id.run (algorithm_5_1_3 pure a b)).2 * a + (Id.run (algorithm_5_1_3 pure a b)).1 * b = 0 ∧
      |(Id.run (algorithm_5_1_3 pure a b)).1 * a - (Id.run (algorithm_5_1_3 pure a b)).2 * b| =
        √(a ^ 2 + b ^ 2) := by
  have h := algorithm_5_1_3_rounds a b (algorithm_5_1_3_mem_exact a b)
  obtain ⟨c, s, hcs, hz, hc, hs⟩ := h.exists_isRelPert (by simp)
  rw [RoundingModel.exact_u] at hc hs
  rw [eq_of_isRelPert_zero hc, eq_of_isRelPert_zero hs]
  refine ⟨hcs, hz, ?_⟩
  rw [← Real.sqrt_sq_eq_abs]
  congr 1
  linear_combination (a ^ 2 + b ^ 2) * hcs - (s * a + c * b) * hz

/-- **Section 5.1.10** of [golub2013matrix], accuracy of the computed rotation. Let $13 u < 1$ and
$a, b \in \mathbb{R}$. For every result $(\hat c, \hat s)$ of Algorithm 5.1.3 in the rounding
model, there are $c, s \in \mathbb{R}$ with $c^2 + s^2 = 1$ and $s a + c b = 0$ such that
$$\hat c = c (1 + \varepsilon_c), \qquad \hat s = s (1 + \varepsilon_s), \qquad |\varepsilon_c|,
  |\varepsilon_s| \le \gamma_{13}.$$

The source states $\varepsilon_c, \varepsilon_s = O(u)$; the formal statement gives the bound
$\gamma_{13}$.

**Reading.** Relative errors bounded by gamma13 under 13u<1.
-/
theorem algorithm_5_1_3_rounding (hu : ((13 : ℕ) : ℝ) * fp.u < 1) (a b : ℝ) {cs : ℝ × ℝ}
    (h : cs ∈ (algorithm_5_1_3 fp.round a b).run) :
    ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧ s * a + c * b = 0 ∧ IsRelPert fp.u 13 c cs.1 ∧
      IsRelPert fp.u 13 s cs.2 :=
  (algorithm_5_1_3_rounds a b h).exists_isRelPert hu

/-- For $i \neq k$, every result $y$ of `GolubVanLoan.Chapter05.givensRotateVec` in the rounding
model is a computed rotation of the entries $i$ and $k$ of $x$
(`FloatingPoint.RoundsGivensApply`). -/
theorem givensRotateVec_rounds {p : ℕ} {i k : Fin p} (hik : i ≠ k) {c s : ℝ} {x y : Fin p → ℝ}
    (h : y ∈ (givensRotateVec fp.round i k c s x).run) : RoundsGivensApply fp c s i k x y := by
  simp only [givensRotateVec, SetM.mem_run_bind, RoundingModel.mem_run_round,
    SetM.mem_run_pure] at h
  obtain ⟨p₁, hp₁, q₁, hq₁, y₁, hy₁, p₂, hp₂, q₂, hq₂, y₂, hy₂, rfl⟩ := h
  refine ⟨⟨p₁, q₁, hp₁, hq₁, ?_⟩, ⟨p₂, q₂, hp₂, hq₂, ?_⟩, fun l hli hlk => ?_⟩
  · rwa [Function.update_of_ne hik, Function.update_self]
  · rwa [Function.update_self]
  · rw [Function.update_of_ne hlk, Function.update_of_ne hli]

/-- In the exact rounding model, a computed rotation $y$ of the entries $i$ and $k$ of $x$ is the
exact one: $y_i = c x_i - s x_k$, $y_k = s x_i + c x_k$, and $y_l = x_l$ for every
$l \neq i, k$. -/
theorem eq_of_roundsGivensApply_exact {p : ℕ} {i k : Fin p} {c s : ℝ} {x y : Fin p → ℝ}
    (h : RoundsGivensApply (RoundingModel.exact ℝ) c s i k x y) :
    y i = c * x i - s * x k ∧ y k = s * x i + c * x k ∧ ∀ l, l ≠ i → l ≠ k → y l = x l := by
  obtain ⟨⟨p₁, q₁, hp₁, hq₁, h₁⟩, ⟨p₂, q₂, hp₂, hq₂, h₂⟩, h₃⟩ := h
  simp only [RoundingModel.exact_rounds_iff] at hp₁ hq₁ h₁ hp₂ hq₂ h₂
  exact ⟨by rw [h₁, hp₁, hq₁], by rw [h₂, hp₂, hq₂], h₃⟩

/-- **Section 5.1.9** of [golub2013matrix], rounding bridge of the row update. Let $i \neq k$, let
$c, s \in \mathbb{R}$, and let the list `cols` have no duplicates. Every result $B$ of
`GolubVanLoan.Chapter05.givensApplyLeft` on $A$ in the rounding model agrees with $A$ in the
columns that are not in `cols` and in the rows other than $i$ and $k$. On the columns of `cols`,
$B$ is a computed row update of $A$: each listed column of $B$ is a computed rotation of the
entries $i$ and $k$ of the same column of $A$.

The relation is `FloatingPoint.RoundsGivensRowUpdate` on the columns of the subtype
`{q // q ∈ cols}`. -/
theorem givensApplyLeft_rounds {i k : Fin m} (hik : i ≠ k) (c s : ℝ) {cols : List (Fin n)}
    (hcols : cols.Nodup) (A : Matrix (Fin m) (Fin n) ℝ) {B : Matrix (Fin m) (Fin n) ℝ}
    (h : B ∈ (givensApplyLeft fp.round i k c s cols A).run) :
    (∀ r q, q ∉ cols → B r q = A r q) ∧ (∀ r q, r ≠ i → r ≠ k → B r q = A r q) ∧
      RoundsGivensRowUpdate fp c s i k (A.submatrix id (Subtype.val : {q // q ∈ cols} → Fin n))
        (B.submatrix id (Subtype.val : {q // q ∈ cols} → Fin n)) := by
  obtain ⟨hout, hin⟩ := (mem_run_foldlM_updateCol_of_nodup
    (fun _ a => givensRotateVec fp.round i k c s a) hcols A B).1 h
  refine ⟨fun r q hq => hout q hq r, fun r q hri hrk => ?_, fun q =>
    givensRotateVec_rounds hik (hin q q.2)⟩
  by_cases hq : q ∈ cols
  · exact (givensRotateVec_rounds hik (hin q hq)).2.2 r hri hrk
  · exact hout q hq r

/-- **Section 5.1.9** of [golub2013matrix], rounding bridge of the column update. Let $i \neq k$,
let $c, s \in \mathbb{R}$, and let the list `rows` have no duplicates. Every result $B$ of
`GolubVanLoan.Chapter05.givensApplyRight` on $A$ in the rounding model agrees with $A$ in the
rows that are not in `rows` and in the columns other than $i$ and $k$. On the rows of `rows`,
$B$ is a computed column update of $A$: each listed row of $B$ is a computed rotation of the
entries $i$ and $k$ of the same row of $A$.

The relation is `FloatingPoint.RoundsGivensColUpdate` on the rows of the subtype
`{r // r ∈ rows}`. -/
theorem givensApplyRight_rounds {i k : Fin n} (hik : i ≠ k) (c s : ℝ) {rows : List (Fin m)}
    (hrows : rows.Nodup) (A : Matrix (Fin m) (Fin n) ℝ) {B : Matrix (Fin m) (Fin n) ℝ}
    (h : B ∈ (givensApplyRight fp.round i k c s rows A).run) :
    (∀ r q, r ∉ rows → B r q = A r q) ∧ (∀ r q, q ≠ i → q ≠ k → B r q = A r q) ∧
      RoundsGivensColUpdate fp c s i k (A.submatrix (Subtype.val : {r // r ∈ rows} → Fin m) id)
        (B.submatrix (Subtype.val : {r // r ∈ rows} → Fin m) id) := by
  obtain ⟨hout, hin⟩ := (mem_run_foldlM_updateRow_of_nodup
    (fun _ a => givensRotateVec fp.round i k c s a) hrows A B).1 h
  refine ⟨fun r q hr => congrFun (hout r hr) q, fun r q hqi hqk => ?_, fun r =>
    givensRotateVec_rounds hik (hin r r.2)⟩
  by_cases hr : r ∈ rows
  · exact (givensRotateVec_rounds hik (hin r hr)).2.2 q hqi hqk
  · exact congrFun (hout r hr) q

private theorem givensApplyLeft_mem_exact (i k : Fin m) (c s : ℝ) (cols : List (Fin n))
    (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (givensApplyLeft pure i k c s cols A) ∈
      (givensApplyLeft (RoundingModel.exact ℝ).round i k c s cols A).run := by
  rw [RoundingModel.round_exact]
  simp only [givensApplyLeft, givensRotateVec, pure_bind, List.foldlM_pure, SetM.mem_run_pure]
  rfl

private theorem givensApplyRight_mem_exact (i k : Fin n) (c s : ℝ) (rows : List (Fin m))
    (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (givensApplyRight pure i k c s rows A) ∈
      (givensApplyRight (RoundingModel.exact ℝ).round i k c s rows A).run := by
  rw [RoundingModel.round_exact]
  simp only [givensApplyRight, givensRotateVec, pure_bind, List.foldlM_pure, SetM.mem_run_pure]
  rfl

/-- **Section 5.1.9** of [golub2013matrix], exact semantics of the row update. Let $i \neq k$ and
let the list `cols` have no duplicates. In exact arithmetic,
`GolubVanLoan.Chapter05.givensApplyLeft` on $A$ returns the matrix whose column $q$ is column
$q$ of $G(i, k, \theta)^T A$ for $q$ in `cols`, and column $q$ of $A$ otherwise.

The proof reads the result off `GolubVanLoan.Chapter05.givensApplyLeft_rounds` at the exact
model.

**Reading.** Exact Gᵀ multiplication on arbitrary listed columns.
-/
theorem givensApplyLeft_spec {i k : Fin m} (hik : i ≠ k) (c s : ℝ) {cols : List (Fin n)}
    (hcols : cols.Nodup) (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (givensApplyLeft pure i k c s cols A) =
      of fun r q => if q ∈ cols then ((givensRotation i k c s)ᵀ * A) r q else A r q := by
  obtain ⟨hout, -, hin⟩ := givensApplyLeft_rounds hik c s hcols A
    (givensApplyLeft_mem_exact i k c s cols A)
  ext r q
  rw [of_apply]
  split_ifs with hq
  · obtain ⟨h1, h2, h3⟩ := eq_of_roundsGivensApply_exact (hin ⟨q, hq⟩)
    have hG : ((givensRotation i k c s)ᵀ * A) r q =
        ((givensRotation i k c s)ᵀ *ᵥ fun p => A p q) r := rfl
    rw [hG, givensRotation_transpose_mulVec_apply hik]
    simp only [submatrix_apply, id] at h1 h2 h3
    split_ifs with hri hrk
    · subst hri; exact h1
    · subst hrk; exact h2
    · exact h3 r hri hrk
  · exact hout r q hq

/-- Let $i \neq k$, let the list `cols` have no duplicates, and let every column index be in `cols`.
In exact arithmetic, `GolubVanLoan.Chapter05.givensApplyLeft` on $A$ returns
$G(i, k, \theta)^T A$. -/
theorem givensApplyLeft_spec_of_forall_mem {i k : Fin m} (hik : i ≠ k) (c s : ℝ)
    {cols : List (Fin n)} (hcols : cols.Nodup) (hall : ∀ q, q ∈ cols)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (givensApplyLeft pure i k c s cols A) = (givensRotation i k c s)ᵀ * A := by
  rw [givensApplyLeft_spec hik c s hcols]
  ext r q
  simp [hall q]

/-- **Section 5.1.9** of [golub2013matrix], exact semantics of the column update. Let $i \neq k$ and
let the list `rows` have no duplicates. In exact arithmetic,
`GolubVanLoan.Chapter05.givensApplyRight` on $A$ returns the matrix whose row $r$ is row $r$ of
$A\, G(i, k, \theta)$ for $r$ in `rows`, and row $r$ of $A$ otherwise.

**Reading.** Exact G multiplication on arbitrary listed rows.
-/
theorem givensApplyRight_spec {i k : Fin n} (hik : i ≠ k) (c s : ℝ) {rows : List (Fin m)}
    (hrows : rows.Nodup) (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (givensApplyRight pure i k c s rows A) =
      of fun r q => if r ∈ rows then (A * givensRotation i k c s) r q else A r q := by
  obtain ⟨hout, -, hin⟩ := givensApplyRight_rounds hik c s hrows A
    (givensApplyRight_mem_exact i k c s rows A)
  ext r q
  rw [of_apply]
  split_ifs with hr
  · obtain ⟨h1, h2, h3⟩ := eq_of_roundsGivensApply_exact (hin ⟨r, hr⟩)
    have hG : (A * givensRotation i k c s) r q = ((givensRotation i k c s)ᵀ *ᵥ A r) q := by
      rw [mulVec_transpose]; rfl
    rw [hG, givensRotation_transpose_mulVec_apply hik]
    simp only [submatrix_apply, id] at h1 h2 h3
    split_ifs with hqi hqk
    · subst hqi; exact h1
    · subst hqk; exact h2
    · exact h3 q hqi hqk
  · exact hout r q hr

/-- Let $i \neq k$, let the list `rows` have no duplicates, and let every row index be in `rows`. In
exact arithmetic, `GolubVanLoan.Chapter05.givensApplyRight` on $A$ returns
$A\, G(i, k, \theta)$. -/
theorem givensApplyRight_spec_of_forall_mem {i k : Fin n} (hik : i ≠ k) (c s : ℝ)
    {rows : List (Fin m)} (hrows : rows.Nodup) (hall : ∀ r, r ∈ rows)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (givensApplyRight pure i k c s rows A) = A * givensRotation i k c s := by
  rw [givensApplyRight_spec hik c s hrows]
  ext r q
  simp [hall r]

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **Section 5.1.10** of [golub2013matrix], rounding error of the row update. Let $i \neq k$, let
$c, s \in \mathbb{R}$ with $c^2 + s^2 = 1$, let $K \in \mathbb{N}$ with $(K + 2)\, u < 1$, let
$\hat c$ and $\hat s$ be relative perturbations of order $K$ of $c$ and $s$, and let the list
`cols` have no duplicates. Write $G = G(i, k, \theta)$ for the exact rotation. Every result $B$
of `GolubVanLoan.Chapter05.givensApplyLeft` with $\hat c$ and $\hat s$ on $A$, in the rounding
model, agrees with $A$ in the columns that are not in `cols`, and
$$\|B(:, q) - G^T A(:, q)\|_2 \le \sqrt 2\, \gamma_{K+2}\, \|A(:, q)\|_2$$
for every $q$ in `cols`, and
$$\|B(:, \mathrm{cols}) - G^T A(:, \mathrm{cols})\|_F \le \sqrt 2\, \gamma_{K+2}\, \|A(:,
  \mathrm{cols})\|_F.$$

The source states $\mathrm{fl}[\hat G^T A] = G^T (A + E)$ with $\|E\|_2 \approx u \|A\|_2$.
Because $G$ is orthogonal, $E = G B - A$ satisfies the same bounds. With the data of
`GolubVanLoan.Chapter05.algorithm_5_1_3_rounding`, $K = 13$ and the constant is
$\sqrt 2\, \gamma_{15}$. The rounding model need not be idempotent.

**Precision.** The source gives an approximate spectral-norm backward error. This statement
uses explicit columnwise and Frobenius bounds for the difference from the exact product on the
selected block.

**Reading.** Replaces approximate spectral backward error by explicit column and block Frobenius
bounds on difference from exact result.
-/
theorem givensApplyLeft_rounding {K : ℕ} (hu : ((K + 2 : ℕ) : ℝ) * fp.u < 1) {i k : Fin m}
    (hik : i ≠ k) {c s chat shat : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (hc : IsRelPert fp.u K c chat)
    (hs : IsRelPert fp.u K s shat) {cols : List (Fin n)} (hcols : cols.Nodup)
    (A : Matrix (Fin m) (Fin n) ℝ) {B : Matrix (Fin m) (Fin n) ℝ}
    (h : B ∈ (givensApplyLeft fp.round i k chat shat cols A).run) :
    (∀ r q, q ∉ cols → B r q = A r q) ∧
      (∀ q, ‖(toLp 2 ((B.submatrix id (Subtype.val : {q // q ∈ cols} → Fin n) -
          (givensRotation i k c s)ᵀ * A.submatrix id Subtype.val).col q) :
            EuclideanSpace ℝ (Fin m))‖ ≤
        √2 * gamma fp.u (K + 2) *
          ‖(toLp 2 ((A.submatrix id (Subtype.val : {q // q ∈ cols} → Fin n)).col q) :
            EuclideanSpace ℝ (Fin m))‖) ∧
      ‖B.submatrix id (Subtype.val : {q // q ∈ cols} → Fin n) -
          (givensRotation i k c s)ᵀ * A.submatrix id Subtype.val‖ ≤
        √2 * gamma fp.u (K + 2) * ‖A.submatrix id (Subtype.val : {q // q ∈ cols} → Fin n)‖ := by
  obtain ⟨hout, -, hrel⟩ := givensApplyLeft_rounds hik chat shat hcols A h
  exact ⟨hout, hrel.col_norm_sub_le hu hik hcs hc hs, hrel.frobenius_norm_sub_le hu hik hcs hc hs⟩

/-- **Section 5.1.10** of [golub2013matrix], rounding error of the column update. Let $i \neq k$,
let $c, s \in \mathbb{R}$ with $c^2 + s^2 = 1$, let $K \in \mathbb{N}$ with $(K + 2)\, u < 1$,
let $\hat c$ and $\hat s$ be relative perturbations of order $K$ of $c$ and $s$, and let the
list `rows` have no duplicates. Write $G = G(i, k, \theta)$ for the exact rotation. Every result
$B$ of `GolubVanLoan.Chapter05.givensApplyRight` with $\hat c$ and $\hat s$ on $A$, in the
rounding model, agrees with $A$ in the rows that are not in `rows`, and
$$\|B(r, :) - A(r, :)\, G\|_2 \le \sqrt 2\, \gamma_{K+2}\, \|A(r, :)\|_2$$
for every $r$ in `rows`, and
$$\|B(\mathrm{rows}, :) - A(\mathrm{rows}, :)\, G\|_F \le \sqrt 2\, \gamma_{K+2}\,
  \|A(\mathrm{rows}, :)\|_F.$$

This is the column form $\mathrm{fl}[A \hat G] = (A + E)\, G$ of the source.

**Precision.** The source gives an approximate spectral-norm backward error. This statement
uses explicit rowwise and Frobenius bounds for the difference from the exact product on the
selected block.

**Reading.** Replaces approximate spectral backward error by explicit row and block Frobenius bounds
on difference from exact result.
-/
theorem givensApplyRight_rounding {K : ℕ} (hu : ((K + 2 : ℕ) : ℝ) * fp.u < 1) {i k : Fin n}
    (hik : i ≠ k) {c s chat shat : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (hc : IsRelPert fp.u K c chat)
    (hs : IsRelPert fp.u K s shat) {rows : List (Fin m)} (hrows : rows.Nodup)
    (A : Matrix (Fin m) (Fin n) ℝ) {B : Matrix (Fin m) (Fin n) ℝ}
    (h : B ∈ (givensApplyRight fp.round i k chat shat rows A).run) :
    (∀ r q, r ∉ rows → B r q = A r q) ∧
      (∀ r, ‖(toLp 2 ((B.submatrix (Subtype.val : {r // r ∈ rows} → Fin m) id -
          A.submatrix Subtype.val id * givensRotation i k c s).row r) :
            EuclideanSpace ℝ (Fin n))‖ ≤
        √2 * gamma fp.u (K + 2) *
          ‖(toLp 2 ((A.submatrix (Subtype.val : {r // r ∈ rows} → Fin m) id).row r) :
            EuclideanSpace ℝ (Fin n))‖) ∧
      ‖B.submatrix (Subtype.val : {r // r ∈ rows} → Fin m) id -
          A.submatrix Subtype.val id * givensRotation i k c s‖ ≤
        √2 * gamma fp.u (K + 2) * ‖A.submatrix (Subtype.val : {r // r ∈ rows} → Fin m) id‖ := by
  obtain ⟨hout, -, hrel⟩ := givensApplyRight_rounds hik chat shat hrows A h
  exact ⟨hout, hrel.row_norm_sub_le hu hik hcs hc hs, hrel.frobenius_norm_sub_le hu hik hcs hc hs⟩

end Frobenius

/-- For $i \neq k$, row $i$ of $H S$ is $c\, S(i, :) - s\, S(k, :)$, row $k$ is
$c\, S(k, :) - s\, S(i, :)$, and the other rows are those of $S$, where $H$ is the hyperbolic
rotation `Matrix.hyperbolicRotation i k c s`. -/
private theorem hyperbolicRotation_mul_apply {ι κ : Type*} [Fintype ι] [DecidableEq ι] {i k : ι}
    (hik : i ≠ k) (c s : ℝ) (S : Matrix ι κ ℝ) (p : ι) (q : κ) :
    (hyperbolicRotation i k c s * S) p q =
      if p = i then c * S i q - s * S k q else if p = k then c * S k q - s * S i q
      else S p q := by
  change (planeEmbed i k !![c, -s; -s, c] *ᵥ fun r => S r q) p = _
  rw [planeEmbed_mulVec_apply _ hik]
  split_ifs <;> simp <;> ring

/-- **Section 6.5.4** of [golub2013matrix], exact semantics of the hyperbolic row update. Let
$i \neq k$ and let the list `cols` have no duplicates. In exact arithmetic,
`GolubVanLoan.Chapter05.hyperbolicApplyLeft` on $S$ returns the matrix whose column $j$ is
column $j$ of $H S$ for $j$ in `cols`, and column $j$ of $S$ otherwise. Here $H$ is the identity
except for the block $\begin{bmatrix} c & -s \\ -s & c \end{bmatrix}$ in the rows and columns
$i$ and $k$.

The matrix $H$ is `Matrix.hyperbolicRotation i k c s`.

**Reading.** Updates selected columns of a matrix with arbitrary finite row type.
-/
theorem hyperbolicApplyLeft_spec {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} {i k : ι}
    (hik : i ≠ k) (c s : ℝ) {cols : List (Fin n)} (hcols : cols.Nodup) (S : Matrix ι (Fin n) ℝ) :
    Id.run (hyperbolicApplyLeft pure i k c s cols S) =
      of fun p j => if j ∈ cols then (hyperbolicRotation i k c s * S) p j else S p j := by
  induction cols generalizing S with
  | nil =>
    ext p j
    simp [hyperbolicApplyLeft]
  | cons j l ih =>
    obtain ⟨hjl, hl⟩ := List.nodup_cons.1 hcols
    set S' := (S.updateRow i (Function.update (S i) j (c * S i j - s * S k j))).updateRow k
      (Function.update (S k) j (c * S k j - s * S i j)) with hS'
    have hstep : Id.run (hyperbolicApplyLeft pure i k c s (j :: l) S) =
        Id.run (hyperbolicApplyLeft pure i k c s l S') := rfl
    have hS'e : ∀ p q, S' p q =
        if q = j then (hyperbolicRotation i k c s * S) p q else S p q := fun p q => by
      rw [hyperbolicRotation_mul_apply hik]
      simp only [hS', updateRow_apply, Function.update_apply]
      by_cases hq : q = j
      · subst hq
        by_cases hpk : p = k
        · subst hpk
          simp [Ne.symm hik]
        · by_cases hpi : p = i
          · subst hpi
            simp [hpk]
          · simp [hpk, hpi]
      · simp only [hq, ite_false]
        split_ifs <;> subst_vars <;> rfl
    have hcol : ∀ q, q ≠ j → ∀ p, (hyperbolicRotation i k c s * S') p q =
        (hyperbolicRotation i k c s * S) p q := fun q hq p => by
      rw [hyperbolicRotation_mul_apply hik, hyperbolicRotation_mul_apply hik, hS'e, hS'e, hS'e,
        ite_eq_right hq, ite_eq_right hq, ite_eq_right hq]
    rw [hstep, ih hl]
    ext p q
    simp only [of_apply, List.mem_cons]
    by_cases hq : q = j
    · subst hq
      rw [ite_eq_right hjl, ite_eq_left (Or.inl rfl), hS'e, ite_eq_left rfl]
    · by_cases hql : q ∈ l
      · rw [ite_eq_left hql, ite_eq_left (Or.inr hql), hcol q hq]
      · rw [ite_eq_right hql, ite_eq_right (by tauto), hS'e, ite_eq_right hq]

end Givens

/-! ### §5.1.11 Representing products of Givens rotations -/

section Encoding

/-- **Equation (5.1.9)** of [golub2013matrix] (Stewart's encoding). The rotation $Z =
\begin{bmatrix} c & s \\ -s & c \end{bmatrix}$ is encoded by the single number
$$\rho = \begin{cases} 1 & \text{if } c = 0, \\ \operatorname{sign}(c)\, s / 2 & \text{if } |s|
  < |c|, \\ 2 \operatorname{sign}(s) / c & \text{otherwise.} \end{cases}$$

The sign function is `Real.sign`, with $\operatorname{sign}(0) = 0$. -/
noncomputable def rotationCode (c s : ℝ) : ℝ :=
  if c = 0 then 1 else if |s| < |c| then Real.sign c * s / 2 else 2 * Real.sign s / c

/-- **Equation (5.1.10)** of [golub2013matrix], the reconstruction of a rotation from its code
$\rho$:
$$(c, s) = \begin{cases} (0, 1) & \text{if } \rho = 1, \\ (\sqrt{1 - s^2},\ s) \text{ with } s =
  2\rho & \text{if } |\rho| < 1, \\ (c,\ \sqrt{1 - c^2}) \text{ with } c = 2/\rho &
  \text{otherwise.} \end{cases}$$
-/
noncomputable def rotationDecode (ρ : ℝ) : ℝ × ℝ :=
  if ρ = 1 then (0, 1)
  else if |ρ| < 1 then (√(1 - (2 * ρ) ^ 2), 2 * ρ) else (2 / ρ, √(1 - (2 / ρ) ^ 2))

/-- **Section 5.1.11** of [golub2013matrix], reconstruction of a rotation. Let $c^2 + s^2 = 1$.
Decoding the code $\rho$ of $(c, s)$ by (5.1.10) gives $(c, s)$ or $(-c, -s)$. In the words of
the source, it is possible to reconstruct $Z$ or $-Z$. -/
theorem rotationDecode_rotationCode {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    rotationDecode (rotationCode c s) = (c, s) ∨ rotationDecode (rotationCode c s) = (-c, -s) := by
  have hs1 : |s| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]; nlinarith [sq_nonneg c]
  unfold rotationCode
  by_cases hc : c = 0
  · subst hc
    have : s = 1 ∨ s = -1 := by
      have h : (s - 1) * (s + 1) = 0 := by nlinarith
      rcases mul_eq_zero.1 h with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rw [ite_eq_left rfl, rotationDecode, ite_eq_left rfl]
    rcases this with rfl | rfl
    · left; rfl
    · right; simp
  rw [ite_eq_right hc]
  by_cases hsc : |s| < |c|
  · rw [ite_eq_left hsc]
    have hρ : |Real.sign c * s / 2| < 1 := by
      rw [abs_div, abs_mul, abs_two]
      rcases Real.sign_apply_eq_of_ne_zero c hc with h | h <;> rw [h] <;> simp <;> linarith
    have hρ1 : Real.sign c * s / 2 ≠ 1 := fun e => by rw [e] at hρ; simp at hρ
    rw [rotationDecode, ite_eq_right hρ1, ite_eq_left hρ]
    have hsq : 1 - (2 * (Real.sign c * s / 2)) ^ 2 = c ^ 2 := by
      rcases Real.sign_apply_eq_of_ne_zero c hc with h | h <;> rw [h] <;> linarith
    rw [hsq, Real.sqrt_sq_eq_abs]
    rcases lt_or_gt_of_ne hc with h | h
    · right; rw [Real.sign_of_neg h, abs_of_neg h]; ext <;> simp; ring
    · left; rw [Real.sign_of_pos h, abs_of_pos h]; ext <;> simp; ring
  · rw [ite_eq_right hsc]
    have hs0 : s ≠ 0 := fun e => by
      rw [e, abs_zero] at hsc; exact hsc (abs_pos.2 hc)
    have hcle : c ^ 2 ≤ 1 / 2 := by
      have := not_lt.1 hsc
      have h2 : c ^ 2 ≤ s ^ 2 := by rw [← sq_abs c, ← sq_abs s]; gcongr
      linarith
    have hc1 : |c| < 1 := by
      rw [← sq_lt_one_iff_abs_lt_one]; linarith
    have hρabs : |2 * Real.sign s / c| = 2 / |c| := by
      rw [abs_div, abs_mul, abs_two]
      rcases Real.sign_apply_eq_of_ne_zero s hs0 with h | h <;> rw [h] <;> simp
    have hcpos : 0 < |c| := abs_pos.2 hc
    have hρ : ¬ |2 * Real.sign s / c| < 1 := by
      rw [hρabs, div_lt_one hcpos]; linarith
    have hρ1 : 2 * Real.sign s / c ≠ 1 := fun e => by
      have h := hρabs
      rw [e, abs_one, eq_div_iff hcpos.ne'] at h
      linarith
    rw [rotationDecode, ite_eq_right hρ1, ite_eq_right hρ]
    have hinv : 2 / (2 * Real.sign s / c) = Real.sign s * c := by
      rcases Real.sign_apply_eq_of_ne_zero s hs0 with h | h <;> rw [h] <;> field_simp
    rw [hinv]
    have hsq : 1 - (Real.sign s * c) ^ 2 = s ^ 2 := by
      rcases Real.sign_apply_eq_of_ne_zero s hs0 with h | h <;> rw [h] <;> linarith
    rw [hsq, Real.sqrt_sq_eq_abs]
    rcases lt_or_gt_of_ne hs0 with h | h
    · right; rw [Real.sign_of_neg h, abs_of_neg h]; ext <;> simp
    · left; rw [Real.sign_of_pos h, abs_of_pos h]; ext <;> simp

end Encoding

/-! ### §5.1.12 Error propagation -/

section ErrorPropagation

open scoped Matrix.Norms.L2Operator

variable {m n : ℕ}

/-- **Section 5.1.12** of [golub2013matrix], definition. A matrix
$\hat Q \in \mathbb{R}^{m \times m}$ is **orthogonal to working precision** $\varepsilon$ if
there is an orthogonal $Q \in \mathbb{R}^{m \times m}$ with
$$\|\hat Q - Q\|_2 \le \varepsilon.$$

The source writes $\|\hat Q - Q\|_2 = O(u)$; the definition makes the $O(u)$ an explicit
parameter $\varepsilon$.

**Reading.** Uses explicit tolerance epsilon and spectral norm in place of O(u).
-/
def orthogonalToWorkingPrecision (ε : ℝ) (Qhat : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  ∃ Q ∈ orthogonalGroup (Fin m) ℝ, ‖Qhat - Q‖ ≤ ε

/-- **Section 5.1.12** of [golub2013matrix], corollary. If $\hat Q$ is orthogonal to working
precision $\varepsilon$, then
$$\|\hat Q^T \hat Q - I\|_2 \le 2 \varepsilon + \varepsilon^2.$$
The source states this as $\|\hat Q^T \hat Q - I_m\| = O(u)$.

**Reading.** Includes exact bound 2epsilon+epsilon² for the chosen tolerance.
-/
theorem orthogonalToWorkingPrecision_transpose_mul_self {ε : ℝ}
    {Qhat : Matrix (Fin m) (Fin m) ℝ} (h : orthogonalToWorkingPrecision ε Qhat) :
    ‖Qhatᵀ * Qhat - 1‖ ≤ 2 * ε + ε ^ 2 := by
  obtain ⟨Q, hQ, hε⟩ := h
  exact l2_opNorm_transpose_mul_self_sub_one_le hQ hε

/-- **Section 5.1.12** of [golub2013matrix], the Givens case. Let $13 u < 1$, $i \neq k$ and
$a, b \in \mathbb{R}$. If $(\hat c, \hat s)$ is a result of Algorithm 5.1.3 in the rounding
model, then the rotation $G(i, k)$ built from $\hat c$ and $\hat s$ is orthogonal to working
precision $\gamma_{13}$. The source says that the matrices defined by the floating point output
of `givens` are orthogonal to working precision.

**Reading.** Quantifies closeness of computed Givens matrix using gamma13.
-/
theorem givensRotation_orthogonalToWorkingPrecision {fp : RoundingModel ℝ}
    (hu : ((13 : ℕ) : ℝ) * fp.u < 1) {i k : Fin m} (hik : i ≠ k) (a b : ℝ) {cs : ℝ × ℝ}
    (h : cs ∈ (algorithm_5_1_3 fp.round a b).run) :
    orthogonalToWorkingPrecision (gamma fp.u 13) (givensRotation i k cs.1 cs.2) := by
  obtain ⟨c, s, hcs, -, hc, hs⟩ := algorithm_5_1_3_rounding hu a b h
  exact ⟨givensRotation i k c s, givensRotation_mem_orthogonalGroup hik hcs,
    l2_opNorm_planeRotation_sub_le (gamma_nonneg fp.u_nonneg hu) hik hcs hc hs⟩

/-- **Section 5.1.12** of [golub2013matrix], the Householder case. Let the rounding model be
idempotent, let $m \ge 1$ and $x \in \mathbb{R}^m$, and let $K = 18 m + 31$ with $K u < 1$. For
every result $(\hat v, \hat\beta)$ of Algorithm 5.1.1 in the rounding model, the Householder
matrix $I - 2 \hat v \hat v^T / \hat v^T \hat v$ is orthogonal to working precision
$8 \gamma_K$. Here $m = k + 1$.

**Reading.** Quantifies closeness when reconstructing beta from vector, including an explicit gamma
bound.
-/
theorem householderMatrix_orthogonalToWorkingPrecision {fp : RoundingModel ℝ} {k : ℕ}
    (hfp : fp.IsIdempotent) (hu : ((18 * (k + 1) + 31 : ℕ) : ℝ) * fp.u < 1)
    (x : Fin (k + 1) → ℝ) {vβ : (Fin (k + 1) → ℝ) × ℝ}
    (h : vβ ∈ (algorithm_5_1_1 fp.round x).run) :
    orthogonalToWorkingPrecision (8 * gamma fp.u (18 * (k + 1) + 31))
      (householderMatrix vβ.1) := by
  obtain ⟨v, -, -, -, -, hle⟩ := householderMatrix_computed_sub_le hfp hu x h
  exact ⟨householderMatrix v, householderMatrix_mem_orthogonalGroup v, hle⟩

/-- **Section 5.1.12** of [golub2013matrix], the Householder case for the matrix that the update
programs apply. Let the rounding model be idempotent, let $m \ge 1$ and $x \in \mathbb{R}^m$,
and let $K = 18 m + 31$ with $K u < 1$. For every result $(\hat v, \hat\beta)$ of Algorithm
5.1.1 in the rounding model, the matrix $I - \hat\beta \hat v \hat v^T$ is orthogonal to working
precision $2((1 + \gamma_K)^3 - 1)$.

The proof uses `GolubVanLoan.Chapter05.one_sub_smul_vecMulVec_computed_sub_le`. Here
$m = k + 1$.

**Reading.** Uses actual computed beta and explicit gamma perturbation bound.
-/
theorem one_sub_smul_vecMulVec_orthogonalToWorkingPrecision {fp : RoundingModel ℝ} {k : ℕ}
    (hfp : fp.IsIdempotent) (hu : ((18 * (k + 1) + 31 : ℕ) : ℝ) * fp.u < 1)
    (x : Fin (k + 1) → ℝ) {vβ : (Fin (k + 1) → ℝ) × ℝ}
    (h : vβ ∈ (algorithm_5_1_1 fp.round x).run) :
    orthogonalToWorkingPrecision (2 * ((1 + gamma fp.u (18 * (k + 1) + 31)) ^ 3 - 1))
      (1 - vβ.2 • vecMulVec vβ.1 vβ.1) := by
  obtain ⟨v, β, hO, -, hle⟩ := one_sub_smul_vecMulVec_computed_sub_le hfp hu x h
  exact ⟨_, hO, hle⟩

end ErrorPropagation

section Accumulation

open scoped Matrix.Norms.Frobenius

variable {m n : ℕ}

/-- **Equation (5.1.11)** of [golub2013matrix]. Let $A_0, A_1, \dots, A_p \in \mathbb{R}^{m \times
n}$, let $Q_0, Q_1, \dots \in \mathbb{R}^{m \times m}$ and
$Z_0, Z_1, \dots \in \mathbb{R}^{n \times n}$ be orthogonal, and let $\varepsilon \ge 0$ with
$p \varepsilon < 1$. Assume that the matrices are generated by computed two-sided orthogonal
updates:
$$\|A_{k+1} - Q_k A_k Z_k\|_F \le \varepsilon \|A_k\|_F, \qquad k = 0, \dots, p - 1.$$
Then there is $E \in \mathbb{R}^{m \times n}$ with
$$A_p = (Q_{p-1} \cdots Q_0)(A_0 + E)(Z_0 \cdots Z_{p-1}),$$
$$\|E\|_F \le \gamma_p(\varepsilon)\, \|A_0\|_F, \qquad \|E\|_2 \le \sqrt{\min(m, n)}\,
  \gamma_p(\varepsilon)\, \|A_0\|_2,$$
where $\gamma_p(\varepsilon) = p \varepsilon / (1 - p \varepsilon)$. This is the source's bound
$\|E\|_2 \le c\, u\, \|A\|_2$, with $c$ depending mildly on $m$, $n$ and $p$.

**Reading.** The source describes $Q_k$ and $Z_k$ as the orthogonal matrices that would be
produced in the absence of roundoff. The formal statement assumes the local error bound for
the exact transformations determined by the computed data at each step.

For full-width updates (a left update on all columns, or a right update on all rows), the
hypothesis at each step is the bound of `GolubVanLoan.Chapter05.householderApplyLeft_rounding`,
`GolubVanLoan.Chapter05.householderApplyRight_rounding`,
`GolubVanLoan.Chapter05.givensApplyLeft_rounding` or
`GolubVanLoan.Chapter05.givensApplyRight_rounding`, with $Z_k = I$ or $Q_k = I$. Those theorems
bound only the updated block. An in-place factorization that stores its vectors in the columns
that a reflector skips, such as Algorithm 5.2.1, therefore needs its own accumulation
(`GolubVanLoan.Chapter05.algorithm_5_2_1_rounding`). The products are `prodRev Q p` and
`prodFwd Z p`, the sequences are 0-based, and $\gamma_p(\varepsilon)$ is
`FloatingPoint.gamma ε p`. -/
theorem equation_5_1_11 {Q : ℕ → Matrix (Fin m) (Fin m) ℝ} {Z : ℕ → Matrix (Fin n) (Fin n) ℝ}
    (hQ : ∀ k, Q k ∈ orthogonalGroup (Fin m) ℝ) (hZ : ∀ k, Z k ∈ orthogonalGroup (Fin n) ℝ)
    {A : ℕ → Matrix (Fin m) (Fin n) ℝ} {ε : ℝ} (hε : 0 ≤ ε) {p : ℕ} (hp : (p : ℝ) * ε < 1)
    (hA : ∀ k, k < p → ‖A (k + 1) - Q k * A k * Z k‖ ≤ ε * ‖A k‖) :
    ∃ E : Matrix (Fin m) (Fin n) ℝ, A p = prodRev Q p * (A 0 + E) * prodFwd Z p ∧
      ‖E‖ ≤ gamma ε p * ‖A 0‖ ∧
      lpOpNorm 2 E ≤ √(min m n : ℕ) * gamma ε p * lpOpNorm 2 (A 0) := by
  obtain ⟨E, h1, h2⟩ := exists_eq_prodRev_mul_add_mul_prodFwd_rect hQ hZ hε p hA
  have hg := one_add_pow_sub_one_le_gamma hε hp
  have hg0 := gamma_nonneg hε hp
  have hF : ‖E‖ ≤ gamma ε p * ‖A 0‖ := h2.trans (mul_le_mul_of_nonneg_right hg (norm_nonneg _))
  refine ⟨E, h1, hF, ?_⟩
  have hrank : √((A 0).rank : ℝ) ≤ √(min m n : ℕ) :=
    Real.sqrt_le_sqrt (Nat.cast_le.2 (le_min (rank_le_height _) (rank_le_width _)))
  calc lpOpNorm 2 E ≤ ‖E‖ := l2_opNorm_le_frobenius_norm E
    _ ≤ gamma ε p * ‖A 0‖ := hF
    _ ≤ gamma ε p * (√((A 0).rank : ℝ) * lpOpNorm 2 (A 0)) :=
        mul_le_mul_of_nonneg_left (frobenius_norm_le_sqrt_rank_mul_l2_opNorm _) hg0
    _ ≤ gamma ε p * (√(min m n : ℕ) * lpOpNorm 2 (A 0)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrank (lpOpNorm_nonneg 2 _)) hg0
    _ = √(min m n : ℕ) * gamma ε p * lpOpNorm 2 (A 0) := by ring

end Accumulation

/-! ### §5.1.13 The complex case -/

section Complex

open Complex

variable {m : ℕ}

/-- **Section 5.1.13** of [golub2013matrix], the complex Householder transformation. Let
$x \in \mathbb{C}^{m+1}$ with $x_1 = r e^{i\theta}$, let $\sigma \in \{1, -1\}$, and let
$v = x + \sigma e^{i\theta} \|x\|_2 e_1 \neq 0$. Then $P = I - (2 / v^H v)\, v v^H$ is unitary
and
$$P x = -\sigma e^{i\theta} \|x\|_2 e_1.$$
In the notation of the source, $v = x \pm e^{i\theta} \|x\|_2 e_1$ gives
$P x = \mp e^{i\theta} \|x\|_2 e_1$.

The factor $e^{i\theta}$ is `Matrix.phase (x 0)`, which is $x_1 / |x_1|$ for $x_1 \neq 0$ and
$1$ for $x_1 = 0$. The matrix $P$ is `Matrix.reflector v`.

**Reading.** The phase is fixed to $1$ at a zero first component. The reflector must be nonzero
for the chosen sign, as required by the source's reflector formula. -/
theorem complexHouseholder (x : Fin (m + 1) → ℂ) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hv : x + ((σ : ℂ) * phase (x 0) * (‖(toLp 2 x : EuclideanSpace ℂ (Fin (m + 1)))‖ : ℂ)) •
      Pi.single 0 1 ≠ 0) :
    reflector (x + ((σ : ℂ) * phase (x 0) *
        (‖(toLp 2 x : EuclideanSpace ℂ (Fin (m + 1)))‖ : ℂ)) • Pi.single 0 1) ∈
        unitaryGroup (Fin (m + 1)) ℂ ∧
      reflector (x + ((σ : ℂ) * phase (x 0) *
          (‖(toLp 2 x : EuclideanSpace ℂ (Fin (m + 1)))‖ : ℂ)) • Pi.single 0 1) *ᵥ x =
        -((σ : ℂ) * phase (x 0) * (‖(toLp 2 x : EuclideanSpace ℂ (Fin (m + 1)))‖ : ℂ)) •
          Pi.single 0 1 := by
  refine ⟨reflector_mem_unitaryGroup _, reflector_mulVec_eq_of_sq ?_ ?_ hv⟩
  · set N : ℝ := ‖(toLp 2 x : EuclideanSpace ℂ (Fin (m + 1)))‖
    have hph : starRingEnd ℂ (phase (x 0)) * phase (x 0) = 1 := by
      rw [RCLike.conj_mul, norm_phase]; simp
    have hσ2 : (σ : ℂ) ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
    calc star ((σ : ℂ) * phase (x 0) * (N : ℂ)) * ((σ : ℂ) * phase (x 0) * (N : ℂ))
        = (σ : ℂ) ^ 2 * (starRingEnd ℂ (phase (x 0)) * phase (x 0)) * (N : ℂ) ^ 2 := by
          simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
          ring
      _ = (N : ℂ) ^ 2 := by rw [hph, hσ2]; ring
  · have h : star ((σ : ℂ) * phase (x 0) *
        (‖(toLp 2 x : EuclideanSpace ℂ (Fin (m + 1)))‖ : ℂ)) * x 0 =
        ((σ * ‖(toLp 2 x : EuclideanSpace ℂ (Fin (m + 1)))‖ * ‖x 0‖ : ℝ) : ℂ) := by
      have := conj_phase_mul_self (x 0)
      simp only [star_mul', Complex.star_def, Complex.conj_ofReal] at this ⊢
      push_cast
      linear_combination ((σ : ℂ) * (‖(toLp 2 x : EuclideanSpace ℂ (Fin (m + 1)))‖ : ℂ)) * this
    rw [h, Complex.star_def, Complex.conj_ofReal]

/-- **Section 5.1.13** of [golub2013matrix], complex Givens rotations. Let $c \in \mathbb{R}$ and
$s \in \mathbb{C}$ with $c^2 + |s|^2 = 1$. Then
$$Q = \begin{bmatrix} c & s \\ -\bar s & c \end{bmatrix}$$
is unitary, and for all indices $i \neq k$ so is its embedding in the plane of the coordinates
$i$ and $k$ of $\mathbb{C}^{m \times m}$. The source writes $Q = \begin{bmatrix} \cos\theta &
\sin\theta\, e^{i\phi} \\ -\sin\theta\, e^{-i\phi} & \cos\theta \end{bmatrix}$ and says that it
is easy to verify that $Q$ is unitary.

The embedding is `Matrix.planeEmbed i k Q`. -/
theorem complexGivens_mem_unitaryGroup {c : ℝ} {s : ℂ} (h : c ^ 2 + ‖s‖ ^ 2 = 1) :
    !![(c : ℂ), s; -starRingEnd ℂ s, (c : ℂ)] ∈ unitaryGroup (Fin 2) ℂ ∧
      ∀ {i k : Fin m}, i ≠ k →
        planeEmbed i k !![(c : ℂ), s; -starRingEnd ℂ s, (c : ℂ)] ∈ unitaryGroup (Fin m) ℂ := by
  have hs : s * starRingEnd ℂ s = ((‖s‖ ^ 2 : ℝ) : ℂ) := by
    rw [RCLike.mul_conj]; push_cast; rfl
  have hG : !![(c : ℂ), s; -starRingEnd ℂ s, (c : ℂ)] ∈ unitaryGroup (Fin 2) ℂ := by
    rw [mem_unitaryGroup_iff]
    have hc : (c : ℂ) ^ 2 + ((‖s‖ ^ 2 : ℝ) : ℂ) = 1 := by exact_mod_cast h
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, star_apply, of_apply, cons_val',
        cons_val_zero, cons_val_one, cons_val_fin_one, Fin.isValue, Fin.zero_eta, Fin.mk_one,
        one_apply_eq, one_apply_ne, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true,
        RCLike.star_def, Complex.conj_ofReal, map_neg, Complex.conj_conj] <;>
      first | ring1 | linear_combination hc + hs
  exact ⟨hG, fun hik => (planeEmbed_mem_unitaryGroup_iff _ hik).2 hG⟩

/-- **Equation (5.1.12)** of [golub2013matrix], a complex Givens rotation from three real ones. Let
$u = u_1 + i u_2$ and $v = v_1 + i v_2$ be complex numbers. Let Algorithm 5.1.3 in exact
arithmetic give $(c_\alpha, s_\alpha)$ for $(u_1, u_2)$, $(c_\beta, s_\beta)$ for $(v_1, v_2)$,
and $(c_\theta, s_\theta)$ for $(r_u, r_v)$, where $r_u = c_\alpha u_1 - s_\alpha u_2$ and
$r_v = c_\beta v_1 - s_\beta v_2$. Set
$$e^{i\phi} = (c_\alpha c_\beta + s_\alpha s_\beta) + i\, (c_\alpha s_\beta - c_\beta s_\alpha),
  \qquad c = c_\theta, \qquad s = s_\theta e^{i\phi}.$$
Then $\bar s u + c v = 0$, which is the second row of
$$\begin{bmatrix} c & s \\ -\bar s & c \end{bmatrix}^H \begin{bmatrix} u \\ v \end{bmatrix} =
  \begin{bmatrix} r \\ 0 \end{bmatrix}.$$

**Reading.** States second-component annihilation only and encodes all three real rotations by exact
program results.
-/
theorem equation_5_1_12 (u v : ℂ) {cα sα cβ sβ cθ sθ : ℝ}
    (hgα : Id.run (algorithm_5_1_3 pure u.re u.im) = (cα, sα))
    (hgβ : Id.run (algorithm_5_1_3 pure v.re v.im) = (cβ, sβ))
    (hgθ : Id.run (algorithm_5_1_3 pure (cα * u.re - sα * u.im) (cβ * v.re - sβ * v.im)) =
      (cθ, sθ)) :
    starRingEnd ℂ ((sθ : ℂ) * ⟨cα * cβ + sα * sβ, cα * sβ - cβ * sα⟩) * u + (cθ : ℂ) * v = 0 := by
  have hα' := algorithm_5_1_3_spec u.re u.im
  have hβ' := algorithm_5_1_3_spec v.re v.im
  rw [hgα] at hα'
  rw [hgβ] at hβ'
  obtain ⟨hα, hαz, -⟩ := hα'
  obtain ⟨hβ, hβz, -⟩ := hβ'
  simp only at hα hαz hβ hβz
  set ru := cα * u.re - sα * u.im
  set rv := cβ * v.re - sβ * v.im
  have hθ' := algorithm_5_1_3_spec ru rv
  rw [hgθ] at hθ'
  obtain ⟨-, hθ, -⟩ := hθ'
  simp only at hθ
  -- `u = r_u e^{-iα}`, `v = r_v e^{-iβ}`
  have hu : u = (ru : ℂ) * ⟨cα, -sα⟩ := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, ru]
      linear_combination (-u.re) * hα + sα * hαz
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, ru]
      linear_combination (-u.im) * hα + cα * hαz
  have hv : v = (rv : ℂ) * ⟨cβ, -sβ⟩ := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, rv]
      linear_combination (-v.re) * hβ + sβ * hβz
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, rv]
      linear_combination (-v.im) * hβ + cβ * hβz
  -- `e^{-iφ} e^{-iα} = e^{-iβ}`
  have hconj : starRingEnd ℂ (⟨cα * cβ + sα * sβ, cα * sβ - cβ * sα⟩ : ℂ) * ⟨cα, -sα⟩ =
      ⟨cβ, -sβ⟩ := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
      linear_combination cβ * hα
    · simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
      linear_combination (-sβ) * hα
  have hθc : (sθ : ℂ) * (ru : ℂ) + (cθ : ℂ) * (rv : ℂ) = 0 := by exact_mod_cast hθ
  rw [hu, hv, map_mul, Complex.conj_ofReal]
  linear_combination ((sθ : ℂ) * (ru : ℂ)) * hconj + (⟨cβ, -sβ⟩ : ℂ) * hθc

end Complex

end GolubVanLoan.Chapter05

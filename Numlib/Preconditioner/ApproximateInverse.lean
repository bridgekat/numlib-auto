/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.Analysis.Normed.Ring.Inverse

/-!
# Approximate inverse preconditioners

An approximate inverse preconditioner for a matrix $A$ does not factor $A$. It minimizes the
residual norm $\|1 - AM\|$ over sparse matrices $M$ and uses $M$ itself as the preconditioner
([saad2003iterative], §10.5). The algorithms of §10.5 are dropping strategies without theorems. This
module proves the facts behind them: the Frobenius objective decouples into one least-squares
problem per column of $M$, and a column with a prescribed support needs only the rows that this
support reaches; the derivative of the least-squares objective; nonsingularity of $AM$ when
$\|1 - AM\| < 1$; a lower bound on the entries of $M$ in terms of the entries of $A^{-1}$; and the
quadratic convergence of the self-preconditioned minimal-residual iteration.

The column decoupling is how [saad2003iterative], §10.5.2, and [golub2013matrix], §11.5.5, compute
sparse approximate inverses column by column. The sparsity estimate shows that an accurate
approximate inverse has a nonzero pattern that contains the large entries of $A^{-1}$, so when these
entries are all of comparable size, $M$ is as dense as $A^{-1}$. The quadratic convergence is a
statement about a normed ring: if the next residual has norm at most $\|(1 - t) R + t R^2\|$ for
every real $t$, then it has norm at most $\|R^2\| \le \|R\|^2$. With the residual recurrence
$R' = (1 - \alpha) R + \alpha R^2$, this is the content of Propositions 10.13 and 10.14 of
[saad2003iterative], and it uses neither matrices, nor the Frobenius norm, nor sparsity.

## Main results

* `Preconditioner.hasFDerivAt_normSq_sub_apply`: the map $z \mapsto \|c - Tz\|^2$ has the derivative
  $e \mapsto -2 \langle c - Tm, Te \rangle$ at $m$.
* `Preconditioner.isUnit_of_norm_one_sub_mul_lt_one`: in a normed ring, $\|1 - am\| < 1$ implies
  that $am$ is a unit.
* `Preconditioner.norm_le_norm_sq_of_isMinOn`: if $\|r'\| \le \|(1 - t) r + t r^2\|$ for every real
  $t$, then $\|r'\| \le \|r\|^2$.
* `Preconditioner.residual_selfPreconditionedStep`: the step $M' = M + \alpha M R$ has the residual
  $R' = (1 - \alpha) R + \alpha R^2$.
* `Preconditioner.abs_sub_inv_apply_le`: if $BA = 1$, then $|B_{ij}| - \max_k |B_{ik}| \sum_k |(1 -
  AM)_{kj}| \le |M_{ij}|$.
* `Preconditioner.frobenius_sq_mul_sub_one_eq_sum`: $\|AM - 1\|_F^2 = \sum_k \|A m_k - e_k\|_2^2$.
* `Preconditioner.isMinOn_submatrix_iff`: the reduced least-squares problem on the rows $I$ and the
  columns $J$ has the same minimizers as the full problem over the vectors supported in $J$.

## Implementation notes

* The derivative is stated for a continuous linear map $T$ into a real inner product space.
  Proposition 10.9 of [saad2003iterative] is the case where $T$ is $M \mapsto AM$ on matrices with
  the Frobenius inner product. The proof needs nothing about matrices, and Mathlib does not provide
  the Frobenius inner product as an inner product space structure.
* The other half of Proposition 10.13 of [saad2003iterative] says that one self-preconditioned
  minimal-residual step reduces the residual by the sine of the angle between $r$ and $Cr$. This is
  the one-dimensional minimal-residual step of `Numlib.Projection.OneDimensional`, and it is not
  stated again here.
-/

namespace Preconditioner

/-! ### The least-squares objective -/

/-- Let $F$ be a real normed space, let $G$ be a real inner product space, let $T \colon F \to G$ be
a continuous linear map, and let $c \in G$. Then at every $m \in F$, the map
$z \mapsto \|c - Tz\|^2$ has the Fréchet derivative
$$e \mapsto -2 \langle c - Tm, Te \rangle,$$
that is, the gradient $-2 T^*(c - Tm)$.

Proposition 10.9 of [saad2003iterative] is the case where $F$ and $G$ are spaces of matrices
with the Frobenius inner product, $T$ is $M \mapsto AM$ and $c = 1$. Its gradient is
$-2 A^T (1 - AM)$. -/
theorem hasFDerivAt_normSq_sub_apply {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] (T : F →L[ℝ] G) (c : G) (m : F) :
    HasFDerivAt (fun z => ‖c - T z‖ ^ 2)
      ((-2 : ℝ) • (innerSL ℝ (c - T m)).comp T) m := by
  have hf : HasFDerivAt (fun z => c - T z) (-T) m := by
    have h := (hasFDerivAt_const c m).sub T.hasFDerivAt
    rwa [zero_sub] at h
  refine hf.norm_sq.congr_fderiv ?_
  ext e
  simp [two_smul]

/-! ### Nonsingularity from a small residual -/

variable {R : Type*} [NormedRing R] [HasSummableGeomSeries R]

/-- Let $R$ be a normed ring in which geometric series of elements of norm less than $1$ are
summable, and let $a, m \in R$. If $\|1 - am\| < 1$, then $am$ is a unit. This is Proposition
10.10 of [saad2003iterative].

The proof is the Neumann series. The result applies to matrices with any submultiplicative norm,
including the Frobenius norm. For square matrices it gives that $m$ is invertible. -/
theorem isUnit_of_norm_one_sub_mul_lt_one {a m : R} (h : ‖1 - a * m‖ < 1) : IsUnit (a * m) := by
  have h' := isUnit_one_sub_of_norm_lt_one h
  rwa [sub_sub_cancel] at h'

/-- Let $R$ be a normed ring in which geometric series of elements of norm less than $1$ are
summable, let $a, m \in R$, and let $d_1$ and $d_2$ be units of $R$. If
$\|1 - d_1 a m d_2\| < 1$, then $am$ is a unit. This is the variant of (10.54) of
[saad2003iterative] with a scaling on both sides: a small scaled residual also gives
nonsingularity. -/
theorem isUnit_of_norm_one_sub_units_mul_lt_one {a m : R} {d₁ d₂ : Rˣ}
    (h : ‖1 - (d₁ : R) * (a * m) * (d₂ : R)‖ < 1) : IsUnit (a * m) :=
  (Units.isUnit_units_mul d₁ _).mp ((Units.isUnit_mul_units _ d₂).mp
    (isUnit_of_norm_one_sub_mul_lt_one h))

/-! ### Quadratic convergence of the self-preconditioned iteration -/

/-- Let $S$ be a normed ring that is also a real normed space, and let $r, r' \in S$. If
$$\|r'\| \le \|(1 - t) r + t r^2\| \quad \text{for every } t \in \mathbb{R},$$
then $\|r'\| \le \|r\|^2$. This is the quadratic convergence of the self-preconditioned
minimal-residual iteration in Propositions 10.13, (10.60), and 10.14 of [saad2003iterative].

A minimal-residual step in the direction $MR$ gives the hypothesis, because $(1 - t) R + t R^2$
is the residual after a step of length $t$ (`Preconditioner.residual_selfPreconditionedStep`).
The proof takes $t = 1$ and uses $\|r^2\| \le \|r\|^2$. The result covers the global and the
column-oriented form of the iteration. It says how fast the iteration converges when it
converges, but not whether it converges. -/
theorem norm_le_norm_sq_of_isMinOn {S : Type*} [NormedRing S] [NormedSpace ℝ S] {r r' : S}
    (h : ∀ t : ℝ, ‖r'‖ ≤ ‖(1 - t) • r + t • r ^ 2‖) : ‖r'‖ ≤ ‖r‖ ^ 2 := by
  have h1 := h 1
  rw [sub_self, zero_smul, zero_add, one_smul] at h1
  refine h1.trans ?_
  rw [pow_two, pow_two]
  exact norm_mul_le r r

/-- Let $T$ be an algebra over a commutative ring $S$, let $A, M \in T$ and $\alpha \in S$. Then the
matrix $B = AM$ of the self-preconditioned step $M' = M + \alpha M(1 - AM)$ satisfies
$$A M' = AM + \alpha \, AM (1 - AM),$$
that is, $B' = B + \alpha B(1 - B)$. This is (10.63) of [saad2003iterative].

Thus every $B_k$ is a polynomial in $B_0$. In particular, if $B_0$ is symmetric, as for
$M_0 = \alpha_0 A^T$, then every $B_k$ is symmetric. -/
theorem mul_selfPreconditionedStep {S T : Type*} [CommRing S] [Ring T] [Algebra S T]
    (A M : T) (α : S) :
    A * (M + α • (M * (1 - A * M))) = A * M + α • (A * M * (1 - A * M)) := by
  rw [mul_add, mul_smul_comm, ← mul_assoc]

/-- Let $T$ be an algebra over a commutative ring $S$, let $A, M \in T$ and $\alpha \in S$, and let
$R = 1 - AM$. Then the self-preconditioned global minimal-residual step $M' = M + \alpha M R$
has the residual
$$1 - A M' = (1 - \alpha) R + \alpha R^2.$$
This is (10.61)–(10.62) of [saad2003iterative].

By induction, the residual $R_k$ after $k$ steps is a polynomial of degree $2^k$ in $R_0$. -/
theorem residual_selfPreconditionedStep {S T : Type*} [CommRing S] [Ring T] [Algebra S T]
    (A M : T) (α : S) :
    1 - A * (M + α • (M * (1 - A * M))) =
      (1 - α) • (1 - A * M) + α • (1 - A * M) ^ 2 := by
  have h2 : A * M * (1 - A * M) = (1 - A * M) - (1 - A * M) * (1 - A * M) := by noncomm_ring
  rw [mul_selfPreconditionedStep, pow_two, h2, smul_sub, sub_smul, one_smul]
  abel

/-! ### The sparsity estimate -/

open scoped Matrix

/-- Let $A, B, M$ be real square matrices with $BA = 1$, and let $R = 1 - AM$. Then for all indices
$i$ and $j$,
$$|B_{ij}| - \Bigl(\max_k |B_{ik}|\Bigr) \sum_k |R_{kj}| \le |M_{ij}|.$$
This is the estimate behind Proposition 10.11 of [saad2003iterative].

The proof uses $M = B - BR$, which follows from $BA = 1$. The maximum over $k$ is written as an
indexed supremum. -/
theorem abs_sub_inv_apply_le {n : Type*} [Fintype n] [DecidableEq n] {A B M : Matrix n n ℝ}
    (hBA : B * A = 1) (i j : n) :
    |B i j| - (⨆ k, |B i k|) * ∑ k, |(1 - A * M) k j| ≤ |M i j| := by
  have hBR : B * (1 - A * M) = B - M := by
    rw [mul_sub, mul_one, ← mul_assoc, hBA, one_mul]
  have hM : M i j = B i j - (B * (1 - A * M)) i j := by
    rw [hBR, Matrix.sub_apply, sub_sub_cancel]
  have hbdd : BddAbove (Set.range fun k => |B i k|) := Set.Finite.bddAbove (Set.finite_range _)
  have h1 : |(B * (1 - A * M)) i j| ≤ (⨆ k, |B i k|) * ∑ k, |(1 - A * M) k j| := by
    rw [Matrix.mul_apply]
    calc |∑ k, B i k * (1 - A * M) k j| ≤ ∑ k, |B i k * (1 - A * M) k j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k, |B i k| * |(1 - A * M) k j| := by simp [abs_mul]
      _ ≤ ∑ k, (⨆ l, |B i l|) * |(1 - A * M) k j| :=
          Finset.sum_le_sum fun k _ => by gcongr; exact le_ciSup hbdd k
      _ = (⨆ l, |B i l|) * ∑ k, |(1 - A * M) k j| := by rw [Finset.mul_sum]
  calc |B i j| - (⨆ k, |B i k|) * ∑ k, |(1 - A * M) k j|
      ≤ |B i j| - |(B * (1 - A * M)) i j| := by linarith
    _ ≤ |B i j - (B * (1 - A * M)) i j| := abs_sub_abs_le_abs_sub _ _
    _ = |M i j| := by rw [← hM]

/-- Let $A, B, M$ be real square matrices with $BA = 1$, let $R = 1 - AM$, and let $\tau$ be a real
number with $\sum_k |R_{kj}| \le \tau$. If $\tau \max_k |B_{ik}| < |B_{ij}|$, then
$M_{ij} \neq 0$. This is Corollary 10.12 of [saad2003iterative].

Thus, if column $j$ of the residual is small in the $\ell^1$ norm and the entry $B_{ij}$ of the
inverse is large compared with its row, then $M_{ij}$ is not zero. An accurate approximate
inverse therefore has a nonzero pattern that contains the large entries of $A^{-1}$. When these
entries are all of comparable size, as for many matrices, $M$ is as dense as $A^{-1}$. -/
theorem apply_ne_zero_of_abs_lt {n : Type*} [Fintype n] [DecidableEq n] {A B M : Matrix n n ℝ}
    (hBA : B * A = 1) {τ : ℝ} {i j : n} (hτ : ∑ k, |(1 - A * M) k j| ≤ τ)
    (hlt : τ * (⨆ k, |B i k|) < |B i j|) : M i j ≠ 0 := by
  have hbdd : BddAbove (Set.range fun k => |B i k|) := Set.Finite.bddAbove (Set.finite_range _)
  have hnonneg : 0 ≤ ⨆ k, |B i k| := le_trans (abs_nonneg (B i i)) (le_ciSup hbdd i)
  have hmono : (⨆ k, |B i k|) * ∑ k, |(1 - A * M) k j| ≤ (⨆ k, |B i k|) * τ :=
    mul_le_mul_of_nonneg_left hτ hnonneg
  have h := abs_sub_inv_apply_le (M := M) hBA i j
  have hpos : 0 < |M i j| := by
    rw [mul_comm] at hlt
    linarith
  exact fun h0 => absurd h0 (abs_pos.mp hpos)

/-! ### Column decoupling and reduced least squares -/

section Columns

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.Frobenius in
/-- The Frobenius objective decouples into columns. Let $A, M \in \mathbb{K}^{n \times n}$ with
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let $m_k$ be column $k$ of $M$. Then
$$\|AM - 1\|_F^2 = \sum_k \|A m_k - e_k\|_2^2.$$
This is the decoupling of [golub2013matrix], §11.5.5, and [saad2003iterative], §10.5.2.

Thus the minimization of $\|AM - 1\|_F$ over the matrices with a prescribed pattern is $n$
independent least-squares problems, one for each column. The norm on the left is the Frobenius
norm `Matrix.Norms.Frobenius`, and the vectors on the right are in `EuclideanSpace` through
`WithLp.toLp 2`. -/
theorem frobenius_sq_mul_sub_one_eq_sum (A M : Matrix n n 𝕜) :
    ‖A * M - 1‖ ^ 2 = ∑ k, ‖WithLp.toLp 2 (A *ᵥ (fun i => M i k) - Pi.single k 1)‖ ^ 2 := by
  rw [Matrix.frobenius_norm_sq_eq_sum_norm_sq_col]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 3
  funext i
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply, Pi.single_apply]

/-- Let $J$ be a set of columns, and let $I$ be a set of rows that contains every row $i$ with
$A_{ij} \neq 0$ for some $j \in J$. For a vector $x$ supported in $J$,
$$\|Ax - c\|_2^2 = \|A(I, J) x_J - c_I\|_2^2 + \sum_{i \notin I} |c_i|^2.$$
-/
private theorem norm_sq_mulVec_sub_eq {A : Matrix n n 𝕜} {c : n → 𝕜} {I J : Finset n}
    (hI : ∀ i, ∀ j ∈ J, A i j ≠ 0 → i ∈ I) {x : n → 𝕜} (hx : ∀ j ∉ J, x j = 0) :
    ‖WithLp.toLp 2 (A *ᵥ x - c)‖ ^ 2 =
      ‖WithLp.toLp 2 (A.submatrix ((↑) : I → n) ((↑) : J → n) *ᵥ (fun j : J => x j) -
        fun i : I => c i)‖ ^ 2 + ∑ i ∈ Iᶜ, ‖c i‖ ^ 2 := by
  have hAx : ∀ i, (A *ᵥ x) i = ∑ j : J, A i j * x j := by
    intro i
    rw [Matrix.mulVec, dotProduct, Finset.sum_coe_sort J (fun j => A i j * x j)]
    exact (Finset.sum_subset (Finset.subset_univ J) fun j _ hj => by rw [hx j hj, mul_zero]).symm
  have hout : ∀ i ∉ I, (A *ᵥ x) i = 0 := by
    intro i hi
    rw [hAx]
    exact Finset.sum_eq_zero fun j _ => by
      rw [show A i j = 0 by by_contra h; exact hi (hI i j j.2 h), zero_mul]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, ← Finset.sum_add_sum_compl I]
  congr 1
  · rw [← Finset.sum_coe_sort I]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi := hAx i
    simp only [Matrix.mulVec, dotProduct] at hi
    simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.submatrix_apply, hi]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [PiLp.toLp_apply, Pi.sub_apply, hout i (Finset.mem_compl.mp hi), zero_sub, norm_neg]

omit [DecidableEq n] in
/-- Reduced least squares. Let $A \in \mathbb{K}^{n \times n}$ and $c \in \mathbb{K}^n$ with
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. Let $J$ be a set of columns, and let $I$ be a set of
rows that contains every row $i$ with $A_{ij} \neq 0$ for some $j \in J$. Then a vector
$\tau \in \mathbb{K}^J$ minimizes $\|A(I, J) \tau - c_I\|_2$ if and only if its extension by
zero minimizes $\|Ax - c\|_2$ over the vectors $x \in \mathbb{K}^n$ with $x_j = 0$ for
$j \notin J$. This is the reduction of [golub2013matrix], §11.5.5, and [saad2003iterative],
§10.5.2.

The two objectives differ by the constant $\|c_{I^c}\|_2^2$. The submatrix $A(I, J)$ is
`A.submatrix` along the inclusions of `I` and `J`, and the extension by zero is
`Function.extend Subtype.val τ 0`. -/
theorem isMinOn_submatrix_iff {A : Matrix n n 𝕜} {c : n → 𝕜} {I J : Finset n}
    (hI : ∀ i, ∀ j ∈ J, A i j ≠ 0 → i ∈ I) {τ : J → 𝕜} :
    IsMinOn (fun σ : J → 𝕜 => ‖WithLp.toLp 2 (A.submatrix ((↑) : I → n) ((↑) : J → n) *ᵥ σ -
        fun i : I => c i)‖) Set.univ τ ↔
      IsMinOn (fun x : n → 𝕜 => ‖WithLp.toLp 2 (A *ᵥ x - c)‖) {x | ∀ j ∉ J, x j = 0}
        (Function.extend Subtype.val τ 0) := by
  classical
  set ext : (J → 𝕜) → n → 𝕜 := fun σ => Function.extend Subtype.val σ 0 with hext
  have hsupp : ∀ σ, ∀ j ∉ J, ext σ j = 0 := fun σ j hj => by
    simp only [hext, Function.extend_val_apply' (p := (· ∈ J)) hj, Pi.zero_apply]
  have hres : ∀ σ, (fun j : J => ext σ j) = σ := fun σ => funext fun j => by
    simp only [hext, Function.extend_val_apply (p := (· ∈ J)) j.2]
  simp only [isMinOn_iff, Set.mem_univ, Set.mem_ofPred_eq, forall_const]
  constructor
  · intro h x hx
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_mulVec_sub_eq hI (hsupp τ),
      norm_sq_mulVec_sub_eq hI hx, hres]
    gcongr
    exact h _
  · intro h σ
    have h' := h (ext σ) (hsupp σ)
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_mulVec_sub_eq hI (hsupp τ),
      norm_sq_mulVec_sub_eq hI (hsupp σ), hres, hres] at h'
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
    linarith

end Columns

end Preconditioner

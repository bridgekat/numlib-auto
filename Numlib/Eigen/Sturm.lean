/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Numlib.Eigen.MinMax
import Numlib.LinearAlgebra.Matrix.UnreducedHessenberg
import Numlib.Topology.Algebra.Polynomial

/-!
# Sturm sequences and Givens' bisection method

Let $T_n$ be the real symmetric tridiagonal matrix of order $n$ with diagonal $d_0, \dots, d_{n-1}$
and off-diagonal $b_0, \dots, b_{n-2}$, and let $T_i$ be its leading principal submatrix of order
$i$. The polynomials $p_i(x) = \det(T_i - x I)$ satisfy the three-term recurrence
$$p_0 = 1, \qquad p_1 = d_0 - x, \qquad p_{i+2} = (d_{i+1} - x) \, p_{i+1} - b_i^2 \, p_i,$$
and they form a **Sturm sequence**: if no $b_i$ vanishes, the number of sign changes in
$p_0(\mu), \dots, p_n(\mu)$ is the number of eigenvalues of $T_n$ that are at most $\mu$. So the
eigenvalues can be located one at a time by bisection (Givens' method). The presentation follows
[quarteroni2000numerical], §5.10.2, with (5.65) for the recurrence and Property 5.11 for interlacing
and the count; the same material is in Wilkinson, *The Algebraic Eigenvalue Problem*, Chapter 5,
§§36–39, in Golub and Van Loan, *Matrix Computations* (1989), §8.5.2, and in [kress1998numerical],
§7.4.

The module also proves that strict interlacing holds for an unreduced matrix: the eigenvalues of
$T_i$ strictly separate those of $T_{i+1}$, so all eigenvalues of $T_n$ are simple. It locates the
spectrum in a Gershgorin interval, which gives a starting interval for the bisection.

## Main definitions

* `Matrix.symmTridiagonalOf`: the symmetric tridiagonal matrix $T_n$ of order $n$ built from
  sequences $d$ and $b$ indexed by $\mathbb{N}$.
* `Sturm.IsUnreduced`: the off-diagonal entries $b_0, \dots, b_{n-2}$ of $T_n$ are nonzero.
* `Sturm.seq`: the Sturm sequence $p_0, p_1, \dots$ of (5.65) of [quarteroni2000numerical].
* `Sturm.eigenvalues`: the eigenvalues $\lambda_0(T_n) \ge \dots \ge \lambda_{n-1}(T_n)$ of $T_n$,
  sorted decreasingly.
* `Sturm.count`: the number $N_n(\mu)$ of eigenvalues of $T_n$ that are at most $\mu$.
* `Sturm.sign` and `Sturm.signChanges`: the signs attached to $p_0(\mu), \dots, p_n(\mu)$, where a
  vanishing $p_i(\mu)$ takes the sign opposite to that of $p_{i-1}(\mu)$, and the number $s_n(\mu)$
  of sign changes among them.
* `Sturm.bisectionStep` and `Sturm.bisectionIterate`: Givens' bisection for the $j$-th largest
  eigenvalue, driven by $s_n$.

## Main results

* `Sturm.seq_eq_det`: $p_i = \det(T_i - x I)$.
* `Sturm.eval_ne_zero_or_eval_ne_zero`: for an unreduced matrix, consecutive members of the Sturm
  sequence have no common root.
* `Sturm.eigenvalues_strictInterlace`: strict interlacing, $\lambda_{k+1}(T_{i+1}) < \lambda_k(T_i)
  < \lambda_k(T_{i+1})$, for an unreduced matrix.
* `Sturm.eigenvalues_simple`: the eigenvalues of an unreduced $T_n$ are simple.
* `Sturm.signChanges_eq_count` and `Sturm.signChanges_eq_countRootsIn`: the Sturm count
  $s_n(\mu) = N_n(\mu)$ for an unreduced $T_n$.
* `Sturm.spectrum_subset_Icc`: the spectrum of $T_n$ lies in its Gershgorin interval.
* `Sturm.eigenvalues_mem_bisectionIterate`: Givens' bisection keeps the $j$-th largest eigenvalue in
  an interval that halves at each step.
* `Matrix.IsHermitian.eigenvalues_injective_of_isUnreducedUpperHessenberg`: a Hermitian unreduced
  upper Hessenberg matrix has simple eigenvalues.
* `Matrix.IsUnreducedUpperHessenberg.apply_zero_ne_zero_of_isSymm`: an eigenvector of a real
  symmetric unreduced tridiagonal matrix has a nonzero first component.

## Proof outline

Strict interlacing is Cauchy's weak interlacing for a principal submatrix
(`Matrix.IsHermitian.eigenvalues₀_submatrix_interlace`), sharpened by the absence of common roots of
$p_i$ and $p_{i+1}$. The Sturm count rests on the invariant that the sign attached to $p_i(\mu)$ is
$(-1)^{N_i(\mu)}$. Off the roots of $p_i$ this holds because
$p_i(\mu) = \prod_k (\lambda_k(T_i) - \mu)$. At a root of $p_{i+1}$, strict interlacing puts exactly
one more eigenvalue of $T_{i+1}$ than of $T_i$ at or below $\mu$.

## Implementation notes

* The indices start at $0$, both for the entries $d_i$, $b_i$ and for the sorted eigenvalues
  $\lambda_k$. The bisection index $j$ of the $j$-th largest eigenvalue starts at $1$, as in Program
  42 of [quarteroni2000numerical].
* *Unreduced* is the hypothesis `Sturm.IsUnreduced b n`, that is, $b_j \neq 0$ for $j + 1 < n$, on
  the off-diagonal entries that occur in $T_n$. A statement about $T_i$ and $T_{i+1}$ takes it at
  order $i + 1$. Nothing is assumed about the entries $b_j$ with $j + 1 \ge n$, which $T_n$ does not
  use. The hypothesis says exactly that $T_n$ is an unreduced upper Hessenberg matrix
  (`Matrix.isUnreducedUpperHessenberg_symmTridiagonalOf_iff`).
* Mathlib's sorted eigenvalues `Matrix.IsHermitian.eigenvalues₀` are indexed by
  `Fin (Fintype.card (Fin i))`. `Sturm.eigenvalues d b i` is `Matrix.IsHermitian.sortedEigenvalues`
  of `Numlib.Eigen.MinMax`, which reindexes them along `Fintype.card_fin`, so that the interlacing
  and counting statements use `Fin i` and `Fin (i + 1)` with `Fin.succ` and `Fin.castSucc`.
* All counting is done with `Finset.card` of index sets of the sorted eigenvalues.
  `Polynomial.countRootsIn` is reached through
  `Matrix.IsHermitian.roots_charpoly_eq_sortedEigenvalues`.
* [quarteroni2000numerical] states the Sturm count for the eigenvalues strictly less than $\mu$.
  This agrees with the count here off the spectrum. At an eigenvalue $\mu$, the sign convention of
  the source counts $\mu$ itself: for $n = 1$ and $\mu = d_0$ the sequence $1, 0$ has one sign
  change. So the formal statement counts the eigenvalues at most $\mu$.
* The nonzero first component of an eigenvector of an unreduced tridiagonal matrix is what makes the
  Gauss weights of `Numlib.Krylov.Quadrature` positive.
-/

open Polynomial Finset

namespace Matrix

/-! ### The symmetric tridiagonal matrix of a diagonal and an off-diagonal -/

/-- The **symmetric tridiagonal matrix** $T_n$ of order $n$ built from sequences
$d, b : \mathbb{N} \to R$: its entries are
$$(T_n)_{ij} = \begin{cases} d_i & \text{if } i = j, \\ b_i & \text{if } j = i + 1, \\ b_j &
  \text{if } i = j + 1, \\ 0 & \text{otherwise}, \end{cases}$$
for $0 \le i, j < n$. Its leading principal submatrix of order $i$ is $T_i$
(`Matrix.symmTridiagonalOf_submatrix_castSucc`). -/
def symmTridiagonalOf {R : Type*} [Zero R] (d b : ℕ → R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j =>
    if (i : ℕ) = j then d i
    else if (i : ℕ) + 1 = j then b i
    else if (j : ℕ) + 1 = i then b j
    else 0

variable {R : Type*} [Zero R] (d b : ℕ → R)

/-- The entries of $T_n$: $d_i$ on the diagonal, $b_i$ at the positions $(i, i + 1)$ and
$(i + 1, i)$, and $0$ elsewhere. -/
theorem symmTridiagonalOf_apply {n : ℕ} (i j : Fin n) :
    symmTridiagonalOf d b n i j =
      if (i : ℕ) = j then d i
      else if (i : ℕ) + 1 = j then b i
      else if (j : ℕ) + 1 = i then b j
      else 0 := rfl

/-- The leading principal submatrix of order $n$ of $T_{n+1}$ is $T_n$. -/
theorem symmTridiagonalOf_submatrix_castSucc (n : ℕ) :
    (symmTridiagonalOf d b (n + 1)).submatrix Fin.castSucc Fin.castSucc
      = symmTridiagonalOf d b n := by
  ext i j
  simp [symmTridiagonalOf_apply]

/-- The matrix $T_n$ is tridiagonal. -/
theorem isTridiagonal_symmTridiagonalOf (n : ℕ) : (symmTridiagonalOf d b n).IsTridiagonal := by
  intro i j hij
  rw [symmTridiagonalOf_apply]
  have hij' : (∃ k : ℕ, j < k ∧ k < i) ∨ (∃ k : ℕ, i < k ∧ k < j) := by
    rcases hij with ⟨k, h1, h2⟩ | ⟨k, h1, h2⟩
    · exact Or.inl ⟨k, h1, h2⟩
    · exact Or.inr ⟨k, h1, h2⟩
  have h1 : (i : ℕ) ≠ j := by omega
  have h2 : (i : ℕ) + 1 ≠ j := by omega
  have h3 : (j : ℕ) + 1 ≠ i := by omega
  simp [h1, h2, h3]

/-- The matrix $T_n$ is symmetric. -/
theorem isSymm_symmTridiagonalOf (n : ℕ) : (symmTridiagonalOf d b n).IsSymm := by
  ext i j
  simp only [transpose_apply, symmTridiagonalOf_apply]
  by_cases h1 : (i : ℕ) = j
  · simp [h1]
  · have h1' : (j : ℕ) ≠ i := fun h => h1 h.symm
    simp only [h1, h1', ite_false]
    by_cases h2 : (i : ℕ) + 1 = j
    · have h3 : ¬ (j : ℕ) + 1 = i := by omega
      simp [h2, h3]
    · simp [h2]

/-- For real sequences $d$ and $b$, the matrix $T_n$ is Hermitian. -/
theorem isHermitian_symmTridiagonalOf (d b : ℕ → ℝ) (n : ℕ) :
    (symmTridiagonalOf d b n).IsHermitian :=
  isHermitian_iff_isSymm.mpr (isSymm_symmTridiagonalOf d b n)

/-- The off-diagonal $b$ is **unreduced** at order $n$ if $b_j \neq 0$ for every $j$ with
$j + 1 < n$. These are the off-diagonal entries of $T_n$, and the condition is the hypothesis of
the Sturm theorems.

The condition says that $T_n$ is an unreduced upper Hessenberg matrix
(`Matrix.isUnreducedUpperHessenberg_symmTridiagonalOf_iff`). -/
def _root_.Sturm.IsUnreduced {R : Type*} [Zero R] (b : ℕ → R) (n : ℕ) : Prop :=
  ∀ j, j + 1 < n → b j ≠ 0

/-- If $b$ is unreduced at order $n$ and $m \le n$, then $b$ is unreduced at order $m$. -/
theorem _root_.Sturm.IsUnreduced.mono {R : Type*} [Zero R] {b : ℕ → R} {m n : ℕ}
    (h : Sturm.IsUnreduced b n) (hmn : m ≤ n) : Sturm.IsUnreduced b m :=
  fun j hj => h j (by omega)

/-- The matrix $T_n$ is an unreduced upper Hessenberg matrix if and only if $b$ is unreduced at
order $n$, that is, $b_j \neq 0$ for $j + 1 < n$.

$T_n$ is tridiagonal, hence upper Hessenberg, and its subdiagonal entry at $(i + 1, i)$ is
$b_i$. So the hypothesis of the Sturm theorems is `Matrix.IsUnreducedUpperHessenberg`, to which
the implicit Q theorem and the geometric simplicity of the eigenvalues of an unreduced
Hessenberg matrix apply. -/
theorem isUnreducedUpperHessenberg_symmTridiagonalOf_iff (n : ℕ) :
    (symmTridiagonalOf d b n).IsUnreducedUpperHessenberg ↔ Sturm.IsUnreduced b n := by
  rw [isUnreducedUpperHessenberg_iff_fin]
  refine ⟨fun h i hi => ?_, fun h =>
    ⟨(isTridiagonal_symmTridiagonalOf d b n).isUpperHessenberg, fun k hk => ?_⟩⟩
  · simpa [symmTridiagonalOf_apply, show i + 1 + 1 ≠ i by omega] using h.2 i hi
  · simpa [symmTridiagonalOf_apply, show k + 1 + 1 ≠ k by omega] using h k hk

/-! ### Unreduced symmetric tridiagonal matrices -/

section Unreduced

/-- A symmetric unreduced upper Hessenberg matrix is tridiagonal. -/
theorem IsUnreducedUpperHessenberg.isTridiagonal_of_isSymm {ι R : Type*} [LinearOrder ι] [Zero R]
    {M : Matrix ι ι R} (hM : M.IsUnreducedUpperHessenberg) (hS : M.IsSymm) : M.IsTridiagonal :=
  fun i j h => h.elim (hM.1 i j) fun hk => by rw [← hS.apply i j]; exact hM.1 j i hk

/-- Let $R$ be a commutative ring without zero divisors, and let $M \in R^{n \times n}$ be
tridiagonal with nonzero superdiagonal entries $M_{i,i+1} \neq 0$ for $i + 1 < n$. If $s \neq 0$
satisfies $Ms = \theta s$ and $n \ge 1$, then the first component $s_0$ is nonzero.

Row $k$ of $Ms = \theta s$ determines $s_{k+1}$ from the earlier components, so $s_0 = 0$ would
give $s = 0$. -/
theorem IsTridiagonal.apply_zero_ne_zero_of_superdiag_ne_zero {R : Type*}
    [CommRing R] [NoZeroDivisors R] {n : ℕ} {M : Matrix (Fin n) (Fin n) R}
    (hT : M.IsTridiagonal)
    (hsup : ∀ (i : ℕ) (hi : i + 1 < n), M ⟨i, by omega⟩ ⟨i + 1, hi⟩ ≠ 0)
    {θ : R} {s : Fin n → R} (hs : M *ᵥ s = θ • s) (hs0 : s ≠ 0) (h0 : 0 < n) :
    s ⟨0, h0⟩ ≠ 0 := by
  intro hz
  apply hs0
  have key : ∀ k (hk : k < n), s ⟨k, hk⟩ = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      cases k with
      | zero => exact hz
      | succ k =>
        have hrow := congrFun hs ⟨k, by omega⟩
        change ∑ l, M ⟨k, by omega⟩ l * s l = θ * s ⟨k, by omega⟩ at hrow
        rw [ih k (by omega) (by omega), mul_zero, Finset.sum_eq_single ⟨k + 1, hk⟩] at hrow
        · exact (mul_eq_zero.1 hrow).resolve_left (hsup k hk)
        · intro l _ hl
          by_cases hlk : (l : ℕ) ≤ k
          · have := ih l (by omega) l.isLt
            rw [Fin.eta] at this
            rw [this, mul_zero]
          · have hl' : k + 1 < (l : ℕ) := by
              have : (l : ℕ) ≠ k + 1 := fun h => hl (Fin.ext h)
              omega
            rw [hT ⟨k, by omega⟩ l (Or.inr ⟨⟨k + 1, hk⟩, Fin.lt_def.2 (by simp),
              Fin.lt_def.2 (by simpa using hl')⟩), zero_mul]
        · simp
  funext i
  exact key i i.isLt

/-- Let $M \in \mathbb{R}^{n \times n}$ be a symmetric unreduced upper Hessenberg matrix (hence
tridiagonal). If $s \neq 0$ satisfies $Ms = \theta s$ and $n \ge 1$, then the first component
$s_0$ is nonzero.

Symmetry turns the nonzero subdiagonal into a nonzero superdiagonal, and
`Matrix.IsTridiagonal.apply_zero_ne_zero_of_superdiag_ne_zero` applies. -/
theorem IsUnreducedUpperHessenberg.apply_zero_ne_zero_of_isSymm {n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsUnreducedUpperHessenberg) (hS : M.IsSymm) {θ : ℝ}
    {s : Fin n → ℝ} (hs : M *ᵥ s = θ • s) (hs0 : s ≠ 0) (h0 : 0 < n) : s ⟨0, h0⟩ ≠ 0 := by
  apply (hM.isTridiagonal_of_isSymm hS).apply_zero_ne_zero_of_superdiag_ne_zero _ hs hs0 h0
  intro i hi
  rw [← hS.apply]
  exact (isUnreducedUpperHessenberg_iff_fin.1 hM).2 i hi

/-- Let $M \in \mathbb{K}^{N \times N}$, over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, be
Hermitian and unreduced upper Hessenberg (such a matrix is tridiagonal). Then the eigenvalues of
$M$ are **simple**: the map `Matrix.IsHermitian.eigenvalues` from indices to eigenvalues is
injective.

Two orthonormal eigenvectors for one eigenvalue would span a plane in an eigenspace, but the
eigenspaces of an unreduced Hessenberg matrix have dimension at most $1$
(`Matrix.IsUnreducedUpperHessenberg.finrank_eigenspace_le_one`, Theorem 7.4.4 of
[golub2013matrix]). -/
theorem IsHermitian.eigenvalues_injective_of_isUnreducedUpperHessenberg {𝕜 : Type*} [RCLike 𝕜]
    {N : ℕ} {M : Matrix (Fin N) (Fin N) 𝕜} (hT : M.IsHermitian)
    (hM : M.IsUnreducedUpperHessenberg) : Function.Injective hT.eigenvalues := by
  cases N with
  | zero => exact fun i => i.elim0
  | succ N =>
  intro i j hij
  by_contra hne
  set e := hT.eigenvectorBasis
  set μ : 𝕜 := (hT.eigenvalues i : 𝕜)
  have hmem : ∀ k, hT.eigenvalues k = hT.eigenvalues i →
      (WithLp.ofLp (e k) : Fin (N + 1) → 𝕜) ∈ Module.End.eigenspace (toLin' M) μ := fun k hk => by
    rw [Module.End.mem_eigenspace_iff, toLin'_apply, hT.mulVec_eigenvectorBasis, hk,
      RCLike.real_smul_eq_coe_smul (K := 𝕜)]
  have hinj : Function.Injective ![i, j] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm]
  have h1 : LinearIndependent 𝕜 fun t : Fin 2 => (WithLp.ofLp (e (![i, j] t)) : Fin (N + 1) → 𝕜) :=
    (e.orthonormal.linearIndependent.comp _ hinj).map' (WithLp.linearEquiv 2 𝕜 _).toLinearMap
      (LinearEquiv.ker _)
  have hli : LinearIndependent 𝕜 fun t : Fin 2 =>
      (⟨WithLp.ofLp (e (![i, j] t)), hmem _ (by fin_cases t <;> simp [hij])⟩ :
        Module.End.eigenspace (toLin' M) μ) :=
    LinearIndependent.of_comp (Submodule.subtype _) h1
  have h2 := hli.fintype_card_le_finrank
  have h3 := hM.finrank_eigenspace_le_one μ
  simp only [Fintype.card_fin] at h2
  omega

end Unreduced

end Matrix

namespace Sturm

variable (d b : ℕ → ℝ)

/-! ### The Sturm sequence -/

/-- **The Sturm sequence** of $T_n$, (5.65) of [quarteroni2000numerical]: the real polynomials
$$p_0 = 1, \qquad p_1 = d_0 - x, \qquad p_{i+2} = (d_{i+1} - x) \, p_{i+1} - b_i^2 \, p_i.$$

The indices start at $0$. By `Sturm.seq_eq_det`, $p_i = \det(T_i - x I)$. -/
noncomputable def seq : ℕ → ℝ[X]
  | 0 => 1
  | 1 => C (d 0) - X
  | (i + 2) => (C (d (i + 1)) - X) * seq (i + 1) - C (b i) ^ 2 * seq i

/-- The first member of the Sturm sequence is $p_0 = 1$. -/
@[simp] theorem seq_zero : seq d b 0 = 1 := rfl

/-- The second member of the Sturm sequence is $p_1 = d_0 - x$. -/
@[simp] theorem seq_one : seq d b 1 = C (d 0) - X := rfl

/-- The three-term recurrence of the Sturm sequence: $p_{i+2} = (d_{i+1} - x) \, p_{i+1} - b_i^2 \,
p_i$. -/
theorem seq_add_two (i : ℕ) :
    seq d b (i + 2) = (C (d (i + 1)) - X) * seq d b (i + 1) - C (b i) ^ 2 * seq d b i := rfl

/-- The matrix $T_n - x I$ with polynomial entries, with the sign convention of the Sturm sequence.
-/
private noncomputable def charMat (n : ℕ) : Matrix (Fin n) (Fin n) ℝ[X] :=
  (Matrix.symmTridiagonalOf d b n).map C - (X : ℝ[X]) • 1

private theorem charMat_apply {n : ℕ} (i j : Fin n) :
    charMat d b n i j = C (Matrix.symmTridiagonalOf d b n i j) - if i = j then X else 0 := by
  simp [charMat, Matrix.one_apply]

private theorem charMat_submatrix_castSucc (n : ℕ) :
    (charMat d b (n + 1)).submatrix Fin.castSucc Fin.castSucc = charMat d b n := by
  ext i j
  simp [charMat_apply, Matrix.symmTridiagonalOf_apply]

private theorem seq_eq_det_charMat (i : ℕ) : seq d b i = (charMat d b i).det := by
  induction i using Nat.twoStepInduction with
  | zero => simp [charMat]
  | one =>
    rw [seq_one, Matrix.det_fin_one, charMat_apply]
    simp [Matrix.symmTridiagonalOf_apply]
  | more i ih1 ih2 =>
    rw [seq_add_two, ih1, ih2, Matrix.det_succ_row _ (Fin.last (i + 1)), Fin.sum_univ_castSucc,
      Fin.sum_univ_castSucc]
    have hzero : ∀ j : Fin i, charMat d b (i + 2) (Fin.last (i + 1)) j.castSucc.castSucc = 0 := by
      intro j
      rw [charMat_apply, Matrix.symmTridiagonalOf_apply]
      have hj := j.isLt
      simp only [Fin.val_last, Fin.val_castSucc]
      have h1 : ¬ (i + 1 = (j : ℕ)) := by omega
      have h2 : ¬ (i + 1 + 1 = (j : ℕ)) := by omega
      have h3 : (j : ℕ) ≠ i := by omega
      have h4 : ¬ (Fin.last (i + 1) = j.castSucc.castSucc) := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      simp [h1, h2, h3, h4]
    rw [Finset.sum_eq_zero fun j _ => by rw [hzero j]; ring, zero_add]
    -- the two surviving terms
    have hdiag : charMat d b (i + 2) (Fin.last (i + 1)) (Fin.last (i + 1)) = C (d (i + 1)) - X := by
      rw [charMat_apply, Matrix.symmTridiagonalOf_apply]
      simp
    have hoff : charMat d b (i + 2) (Fin.last (i + 1)) (Fin.last i).castSucc = C (b i) := by
      rw [charMat_apply, Matrix.symmTridiagonalOf_apply]
      have h1 : ¬ (i + 1 + 1 = i) := by omega
      have h2 : ¬ (Fin.last (i + 1) = (Fin.last i).castSucc) := by
        intro h; have := congrArg Fin.val h; simp at this
      simp [h1, h2]
    have hsub1 : (charMat d b (i + 2)).submatrix (Fin.last (i + 1)).succAbove
        (Fin.last (i + 1)).succAbove = charMat d b (i + 1) := by
      rw [Fin.succAbove_last, charMat_submatrix_castSucc]
    -- the minor at `(last, last - 1)`: expand along its last column
    have hsub2 : ((charMat d b (i + 2)).submatrix (Fin.last (i + 1)).succAbove
        (Fin.last i).castSucc.succAbove).det = C (b i) * (charMat d b i).det := by
      rw [Matrix.det_succ_column _ (Fin.last i), Fin.sum_univ_castSucc]
      have hz : ∀ r : Fin i, (charMat d b (i + 2)).submatrix (Fin.last (i + 1)).succAbove
          (Fin.last i).castSucc.succAbove r.castSucc (Fin.last i) = 0 := by
        intro r
        rw [Matrix.submatrix_apply, Fin.succAbove_last, Fin.succAbove_castSucc_self, charMat_apply,
          Matrix.symmTridiagonalOf_apply]
        have hr := r.isLt
        have h4 : ¬ (r.castSucc.castSucc = (Fin.last i).succ) := by
          intro h; have := congrArg Fin.val h; simp at this; omega
        simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_last, h4, ite_false, sub_zero]
        have h1 : ¬ ((r : ℕ) = i + 1) := by omega
        have h2 : (r : ℕ) ≠ i := by omega
        have h3 : ¬ (i + 1 + 1 = (r : ℕ)) := by omega
        simp [h1, h2, h3]
      rw [Finset.sum_eq_zero fun r _ => by rw [hz r]; ring, zero_add]
      have hlast : (charMat d b (i + 2)).submatrix (Fin.last (i + 1)).succAbove
          (Fin.last i).castSucc.succAbove (Fin.last i) (Fin.last i) = C (b i) := by
        rw [Matrix.submatrix_apply, Fin.succAbove_last, Fin.succAbove_castSucc_self, charMat_apply,
          Matrix.symmTridiagonalOf_apply]
        have h4 : ¬ ((Fin.last i).castSucc = (Fin.last i).succ) := by
          intro h; have := congrArg Fin.val h; simp at this
        simp
      have hmin : ((charMat d b (i + 2)).submatrix (Fin.last (i + 1)).succAbove
          (Fin.last i).castSucc.succAbove).submatrix (Fin.last i).succAbove (Fin.last i).succAbove
          = charMat d b i := by
        rw [Matrix.submatrix_submatrix, Fin.succAbove_last, Fin.succAbove_last]
        ext r c
        rw [Matrix.submatrix_apply, Function.comp_apply, Function.comp_apply,
          Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def]), charMat_apply, charMat_apply,
          Matrix.symmTridiagonalOf_apply, Matrix.symmTridiagonalOf_apply]
        simp [Fin.ext_iff]
      rw [hlast, hmin]
      simp
    rw [hdiag, hoff, hsub1, hsub2]
    simp only [Fin.val_last, Fin.val_castSucc]
    have hs1 : ((-1 : ℝ[X]) ^ (i + 1 + (i + 1))) = 1 := Even.neg_one_pow ⟨i + 1, rfl⟩
    have hs2 : ((-1 : ℝ[X]) ^ (i + 1 + i)) = -1 := Odd.neg_one_pow ⟨i, by ring⟩
    rw [hs1, hs2]
    ring

/-- For every $i$, the Sturm polynomial $p_i$ is the determinant
$$p_i = \det(T_i - x I).$$

The proof expands the tridiagonal determinant along its last row, and then the remaining minor
along its last column. -/
theorem seq_eq_det (i : ℕ) :
    seq d b i = ((Matrix.symmTridiagonalOf d b i).map C - (X : ℝ[X]) • 1).det :=
  seq_eq_det_charMat d b i

/-- For every $i$, $p_i = (-1)^i \chi_{T_i}$, where $\chi_{T_i} = \det(x I - T_i)$ is the
characteristic polynomial of $T_i$. -/
theorem seq_eq_charpoly (i : ℕ) :
    seq d b i = (-1) ^ i * (Matrix.symmTridiagonalOf d b i).charpoly := by
  have h : charMat d b i = -(Matrix.symmTridiagonalOf d b i).charmatrix := by
    ext r c
    simp [charMat_apply, Matrix.charmatrix_apply, Matrix.diagonal_apply]
  rw [seq_eq_det_charMat, h, Matrix.det_neg, Fintype.card_fin, Matrix.charpoly]

/-- The Sturm polynomial $p_i$ has degree $i$. -/
theorem natDegree_seq (i : ℕ) : (seq d b i).natDegree = i := by
  rw [seq_eq_charpoly, natDegree_mul (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (Matrix.charpoly_monic _).ne_zero, natDegree_pow, natDegree_neg, natDegree_one, mul_zero,
    zero_add, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

/-- The Sturm polynomial $p_i$ has leading coefficient $(-1)^i$. -/
theorem leadingCoeff_seq (i : ℕ) : (seq d b i).leadingCoeff = (-1) ^ i := by
  rw [seq_eq_charpoly, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_neg, leadingCoeff_one,
    (Matrix.charpoly_monic _).leadingCoeff, mul_one]

/-- No Sturm polynomial $p_i$ is the zero polynomial. -/
theorem seq_ne_zero (i : ℕ) : seq d b i ≠ 0 := by
  intro h
  have := leadingCoeff_seq d b i
  rw [h, leadingCoeff_zero] at this
  exact pow_ne_zero i (neg_ne_zero.mpr one_ne_zero) this.symm

/-- **Consecutive members of the Sturm sequence have no common root.** If $b$ is unreduced at order
$i + 1$, then for every $\mu \in \mathbb{R}$, $p_i(\mu) \neq 0$ or $p_{i+1}(\mu) \neq 0$.

By the recurrence, a common root of $p_{j+1}$ and $p_{j+2}$ is a root of $p_j$, because
$b_j \neq 0$. Descending gives a root of $p_0 = 1$, which is impossible. -/
theorem eval_ne_zero_or_eval_ne_zero (i : ℕ) (hb : IsUnreduced b (i + 1)) (μ : ℝ) :
    (seq d b i).eval μ ≠ 0 ∨ (seq d b (i + 1)).eval μ ≠ 0 := by
  induction i with
  | zero => exact Or.inl (by simp)
  | succ i ih =>
    by_contra h
    push Not at h
    obtain ⟨h1, h2⟩ := h
    have h3 : (seq d b i).eval μ = 0 := by
      rw [seq_add_two, eval_sub, eval_mul, eval_mul, eval_pow, eval_C, h1, mul_zero, zero_sub,
        neg_eq_zero, mul_eq_zero, pow_eq_zero_iff two_ne_zero] at h2
      exact h2.resolve_left (hb i (by omega))
    rcases ih (hb.mono (by omega)) with h | h
    · exact h h3
    · exact h h1

/-- Let $b$ be unreduced at order $i + 2$. If $p_{i+1}(\mu) = 0$, then $p_i(\mu)$ and $p_{i+2}(\mu)$
have opposite signs:
$$p_{i+2}(\mu) \, p_i(\mu) < 0.$$

The recurrence gives $p_{i+2}(\mu) = -b_i^2 \, p_i(\mu)$, and $p_i(\mu) \neq 0$ by
`Sturm.eval_ne_zero_or_eval_ne_zero`. This lemma justifies the sign convention for a vanishing
member. -/
theorem eval_seq_add_two_mul_eval_seq_neg (i : ℕ) (hb : IsUnreduced b (i + 2)) {μ : ℝ}
    (h : (seq d b (i + 1)).eval μ = 0) :
    (seq d b (i + 2)).eval μ * (seq d b i).eval μ < 0 := by
  have hne : (seq d b i).eval μ ≠ 0 :=
    (eval_ne_zero_or_eval_ne_zero d b i (hb.mono (by omega)) μ).resolve_right
      (by simpa using h)
  rw [seq_add_two, eval_sub, eval_mul, eval_mul, eval_pow, eval_C, h, mul_zero, zero_sub,
    neg_mul, neg_lt_zero, mul_assoc]
  exact mul_pos ((even_two).pow_pos (hb i (by omega))) (mul_self_pos.mpr hne)

/-! ### The sorted eigenvalues -/

/-- The eigenvalues $\lambda_0(T_n) \ge \dots \ge \lambda_{n-1}(T_n)$ of $T_n$, sorted decreasingly
and indexed from $0$. This is `Matrix.IsHermitian.sortedEigenvalues` of `Numlib.Eigen.MinMax`. -/
noncomputable def eigenvalues (n : ℕ) : Fin n → ℝ :=
  (Matrix.isHermitian_symmTridiagonalOf d b n).sortedEigenvalues

/-- `Sturm.eigenvalues d b n` is `Matrix.IsHermitian.sortedEigenvalues` for any proof that $T_n$ is
Hermitian. -/
theorem eigenvalues_eq_sortedEigenvalues {n : ℕ}
    (hT : (Matrix.symmTridiagonalOf d b n).IsHermitian) :
    eigenvalues d b n = hT.sortedEigenvalues :=
  rfl

/-- The $k$-th sorted eigenvalue $\lambda_k(T_n)$ is the $k$-th entry of Mathlib's sorted
eigenvalues `Matrix.IsHermitian.eigenvalues₀`, for any proof that $T_n$ is Hermitian. -/
theorem eigenvalues_eq_eigenvalues₀ {n : ℕ} (hT : (Matrix.symmTridiagonalOf d b n).IsHermitian)
    (k : Fin n) : eigenvalues d b n k = hT.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm k) :=
  rfl

/-- The sorted eigenvalues decrease: $k \le k'$ implies $\lambda_{k'}(T_n) \le \lambda_k(T_n)$. -/
theorem antitone_eigenvalues (n : ℕ) : Antitone (eigenvalues d b n) :=
  (Matrix.isHermitian_symmTridiagonalOf d b n).sortedEigenvalues_antitone

/-- The roots of the characteristic polynomial of $T_n$, with multiplicity, are the sorted
eigenvalues $\lambda_0(T_n), \dots, \lambda_{n-1}(T_n)$. -/
theorem roots_charpoly_eq (n : ℕ) :
    (Matrix.symmTridiagonalOf d b n).charpoly.roots
      = Multiset.map (eigenvalues d b n) univ.val :=
  (Matrix.isHermitian_symmTridiagonalOf d b n).roots_charpoly_eq_sortedEigenvalues

/-- The characteristic polynomial of $T_n$ is $\prod_{k < n} (x - \lambda_k(T_n))$. -/
theorem charpoly_eq_prod (n : ℕ) :
    (Matrix.symmTridiagonalOf d b n).charpoly = ∏ k, (X - C (eigenvalues d b n k)) := by
  rw [Finset.prod_eq_multiset_prod,
    show (Multiset.map (fun k => X - C (eigenvalues d b n k)) univ.val)
      = Multiset.map (fun a => X - C a) (Multiset.map (eigenvalues d b n) univ.val) by
        rw [Multiset.map_map]; rfl, ← roots_charpoly_eq]
  exact (prod_multiset_X_sub_C_of_monic_of_roots_card_eq (Matrix.charpoly_monic _)
    (Matrix.isHermitian_symmTridiagonalOf d b n).splits_charpoly.natDegree_eq_card_roots.symm).symm

/-- For every $\mu \in \mathbb{R}$,
$$p_n(\mu) = \prod_{k < n} (\lambda_k(T_n) - \mu).$$
-/
theorem eval_seq_eq_prod (n : ℕ) (μ : ℝ) :
    (seq d b n).eval μ = ∏ k, (eigenvalues d b n k - μ) := by
  rw [seq_eq_charpoly, charpoly_eq_prod, eval_mul, eval_pow, eval_neg, eval_one, eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  rw [show ∏ k, (eigenvalues d b n k - μ) = ∏ k, -(μ - eigenvalues d b n k) by
    simp only [neg_sub], Finset.prod_neg, Finset.card_univ, Fintype.card_fin]

/-- Every sorted eigenvalue $\lambda_k(T_n)$ is a root of $p_n$. -/
theorem eval_seq_eigenvalues (n : ℕ) (k : Fin n) : (seq d b n).eval (eigenvalues d b n k) = 0 := by
  rw [eval_seq_eq_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ k) (sub_self _)

/-- Every root $\mu$ of $p_n$ is a sorted eigenvalue: $\mu = \lambda_k(T_n)$ for some $k$. -/
theorem exists_eigenvalues_eq_of_eval_eq_zero {n : ℕ} {μ : ℝ} (h : (seq d b n).eval μ = 0) :
    ∃ k, eigenvalues d b n k = μ := by
  rw [eval_seq_eq_prod, Finset.prod_eq_zero_iff] at h
  obtain ⟨k, -, hk⟩ := h
  exact ⟨k, sub_eq_zero.mp hk⟩

/-! ### Interlacing -/

/-- **Weak (Cauchy) interlacing** for the leading principal submatrix. For every $i$ and
$0 \le k < i$,
$$\lambda_{k+1}(T_{i+1}) \le \lambda_k(T_i) \le \lambda_k(T_{i+1}).$$
-/
theorem eigenvalues_interlace (i : ℕ) (k : Fin i) :
    eigenvalues d b (i + 1) k.succ ≤ eigenvalues d b i k ∧
      eigenvalues d b i k ≤ eigenvalues d b (i + 1) k.castSucc := by
  have hsub := Matrix.symmTridiagonalOf_submatrix_castSucc d b i
  have hB : ((Matrix.symmTridiagonalOf d b (i + 1)).submatrix Fin.castSucc
      Fin.castSucc).IsHermitian :=
    hsub ▸ Matrix.isHermitian_symmTridiagonalOf d b i
  have h := Matrix.IsHermitian.sortedEigenvalues_submatrix_castSucc_interlace
    (Matrix.isHermitian_symmTridiagonalOf d b (i + 1)) hB k
  rw [Matrix.IsHermitian.sortedEigenvalues_congr hsub hB
    (Matrix.isHermitian_symmTridiagonalOf d b i)] at h
  exact h

/-- **Strict interlacing**, lower half (Property 5.11 of [quarteroni2000numerical]). If $b$ is
unreduced at order $i + 1$, then for $0 \le k < i$,
$$\lambda_{k+1}(T_{i+1}) < \lambda_k(T_i).$$

Equality would make $\lambda_k(T_i)$ a common root of $p_i$ and $p_{i+1}$, which
`Sturm.eval_ne_zero_or_eval_ne_zero` excludes. -/
theorem eigenvalues_succ_lt (i : ℕ) (hb : IsUnreduced b (i + 1)) (k : Fin i) :
    eigenvalues d b (i + 1) k.succ < eigenvalues d b i k := by
  refine lt_of_le_of_ne (eigenvalues_interlace d b i k).1 fun h => ?_
  have h1 := eval_seq_eigenvalues d b (i + 1) k.succ
  have h2 := eval_seq_eigenvalues d b i k
  rw [h] at h1
  rcases eval_ne_zero_or_eval_ne_zero d b i hb (eigenvalues d b i k) with h' | h'
  · exact h' h2
  · exact h' h1

/-- **Strict interlacing**, upper half (Property 5.11 of [quarteroni2000numerical]). If $b$ is
unreduced at order $i + 1$, then for $0 \le k < i$,
$$\lambda_k(T_i) < \lambda_k(T_{i+1}).$$
-/
theorem eigenvalues_lt_castSucc (i : ℕ) (hb : IsUnreduced b (i + 1)) (k : Fin i) :
    eigenvalues d b i k < eigenvalues d b (i + 1) k.castSucc := by
  refine lt_of_le_of_ne (eigenvalues_interlace d b i k).2 fun h => ?_
  have h1 := eval_seq_eigenvalues d b (i + 1) k.castSucc
  have h2 := eval_seq_eigenvalues d b i k
  rw [← h] at h1
  rcases eval_ne_zero_or_eval_ne_zero d b i hb (eigenvalues d b i k) with h' | h'
  · exact h' h2
  · exact h' h1

/-- **Strict interlacing** (Property 5.11 of [quarteroni2000numerical]). If $b$ is unreduced at
order $i + 1$, then the eigenvalues of $T_i$ strictly separate those of $T_{i+1}$: for
$0 \le k < i$,
$$\lambda_{k+1}(T_{i+1}) < \lambda_k(T_i) < \lambda_k(T_{i+1}).$$

This form uses Mathlib's sorted eigenvalues `Matrix.IsHermitian.eigenvalues₀`, for any proofs
that $T_i$ and $T_{i+1}$ are Hermitian. -/
theorem eigenvalues_strictInterlace (i : ℕ) (hb : IsUnreduced b (i + 1))
    (hT : (Matrix.symmTridiagonalOf d b (i + 1)).IsHermitian)
    (hT' : (Matrix.symmTridiagonalOf d b i).IsHermitian) (k : Fin i) :
    hT.eigenvalues₀ ⟨k + 1, by simp⟩ < hT'.eigenvalues₀ ⟨k, by simp⟩ ∧
      hT'.eigenvalues₀ ⟨k, by simp⟩ < hT.eigenvalues₀ ⟨k, by simp⟩ := by
  have h1 := eigenvalues_succ_lt d b i hb k
  have h2 := eigenvalues_lt_castSucc d b i hb k
  rw [eigenvalues_eq_eigenvalues₀ d b hT, eigenvalues_eq_eigenvalues₀ d b hT'] at h1 h2
  exact ⟨h1, h2⟩

/-- If $b$ is unreduced at order $n$, then the sorted eigenvalues of $T_n$ strictly decrease:
$\lambda_0(T_n) > \dots > \lambda_{n-1}(T_n)$. So the eigenvalues are simple. -/
theorem strictAnti_eigenvalues (n : ℕ) (hb : IsUnreduced b n) :
    StrictAnti (eigenvalues d b n) := by
  cases n with
  | zero => exact fun i => i.elim0
  | succ n =>
    rw [Fin.strictAnti_iff_succ_lt]
    intro k
    exact (eigenvalues_succ_lt d b n hb k).trans (eigenvalues_lt_castSucc d b n hb k)

/-- **The eigenvalues of an unreduced symmetric tridiagonal matrix are simple** (Property 5.11 of
[quarteroni2000numerical]). If $b$ is unreduced at order $n$, then the roots of the
characteristic polynomial of $T_n$ have no repetition. -/
theorem eigenvalues_simple (n : ℕ) (hb : IsUnreduced b n) :
    (Matrix.symmTridiagonalOf d b n).charpoly.roots.Nodup := by
  rw [roots_charpoly_eq]
  exact (Finset.univ.nodup).map_on fun x _ y _ h => (strictAnti_eigenvalues d b n hb).injective h

/-! ### The Sturm count -/

/-- The number $N_n(\mu)$ of eigenvalues of $T_n$ that are at most $\mu$, counted with multiplicity:
the number of indices $k < n$ with $\lambda_k(T_n) \le \mu$. -/
noncomputable def count (n : ℕ) (μ : ℝ) : ℕ :=
  (univ.filter fun k => eigenvalues d b n k ≤ μ).card

/-- $N_n(\mu)$ is the number of roots of the characteristic polynomial of $T_n$ in $(-\infty, \mu]$,
counted with multiplicity. -/
theorem countRootsIn_Iic_eq_count (n : ℕ) (μ : ℝ) :
    (Matrix.symmTridiagonalOf d b n).charpoly.countRootsIn (Set.Iic μ) = count d b n μ := by
  classical
  rw [countRootsIn, roots_charpoly_eq, Multiset.filter_map, Multiset.card_map, count]
  congr 1

/-- $N_n(\mu) = \sum_{k < n} [\lambda_k(T_n) \le \mu]$, where $[\cdot]$ is $1$ for a true condition
and $0$ otherwise. -/
theorem count_eq_sum (n : ℕ) (μ : ℝ) :
    count d b n μ = ∑ k, if eigenvalues d b n k ≤ μ then 1 else 0 :=
  Finset.card_filter _ _

/-- For the empty matrix, $N_0(\mu) = 0$. -/
@[simp] theorem count_zero (μ : ℝ) : count d b 0 μ = 0 := by simp [count]

/-- $N_n(\mu) \le n$. -/
theorem count_le (n : ℕ) (μ : ℝ) : count d b n μ ≤ n :=
  (Finset.card_filter_le _ _).trans (by simp)

/-- $N_n(\mu)$ is monotone in $\mu$. -/
theorem count_mono (n : ℕ) : Monotone (count d b n) := fun μ ν hμν =>
  Finset.card_le_card fun k hk => by
    simp only [mem_filter, mem_univ, true_and] at hk ⊢
    exact hk.trans hμν

/-- If $b$ is unreduced at order $n$, then $N_n(\lambda_k(T_n)) = n - k$ for $0 \le k < n$: the
eigenvalues at most $\lambda_k(T_n)$ are $\lambda_k(T_n), \dots, \lambda_{n-1}(T_n)$. -/
theorem count_eigenvalues {n : ℕ} (hb : IsUnreduced b n) (k : Fin n) :
    count d b n (eigenvalues d b n k) = n - k := by
  have : (univ.filter fun j => eigenvalues d b n j ≤ eigenvalues d b n k) = Finset.Ici k := by
    ext j
    simp [(strictAnti_eigenvalues d b n hb).le_iff_ge]
  rw [count, this, Fin.card_Ici]

/-- If $b$ is unreduced at order $i + 1$, then $N_i(\lambda_k(T_{i+1})) = i - k$ for
$0 \le k \le i$. By strict interlacing, the eigenvalues of $T_i$ at most $\lambda_k(T_{i+1})$
are $\lambda_k(T_i), \dots, \lambda_{i-1}(T_i)$. -/
theorem count_eigenvalues_succ {i : ℕ} (hb : IsUnreduced b (i + 1)) (k : Fin (i + 1)) :
    count d b i (eigenvalues d b (i + 1) k) = i - k := by
  have hset : (univ.filter fun j : Fin i => eigenvalues d b i j ≤ eigenvalues d b (i + 1) k)
      = univ.filter fun j : Fin i => (k : ℕ) ≤ j := by
    ext j
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro h
      by_contra hlt
      push Not at hlt
      have h1 := eigenvalues_succ_lt d b i hb j
      have h2 := antitone_eigenvalues d b (i + 1)
        (show j.succ ≤ k by rw [Fin.le_def, Fin.val_succ]; omega)
      linarith
    · intro h
      have h1 := (eigenvalues_lt_castSucc d b i hb j).le
      have h2 := antitone_eigenvalues d b (i + 1)
        (show k ≤ j.castSucc by rw [Fin.le_def, Fin.val_castSucc]; exact h)
      linarith
  rw [count, hset]
  rcases lt_or_ge (k : ℕ) i with hk | hk
  · have : (univ.filter fun j : Fin i => (k : ℕ) ≤ j) = Finset.Ici (⟨k, hk⟩ : Fin i) := by
      ext j
      simp [Fin.le_def]
    rw [this, Fin.card_Ici]
  · have : (univ.filter fun j : Fin i => (k : ℕ) ≤ j) = ∅ := by
      ext j
      simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false, not_le]
      exact lt_of_lt_of_le j.isLt hk
    rw [this, Finset.card_empty]
    omega

/-- $N_i(\mu) \le N_{i+1}(\mu)$: passing from $T_i$ to $T_{i+1}$ loses no eigenvalue at or below
$\mu$. This follows from weak interlacing. -/
theorem count_le_count_succ (i : ℕ) (μ : ℝ) : count d b i μ ≤ count d b (i + 1) μ := by
  rw [count_eq_sum, count_eq_sum, Fin.sum_univ_succ]
  refine le_add_of_nonneg_of_le (by positivity) (Finset.sum_le_sum fun k _ => ?_)
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd ((eigenvalues_interlace d b i k).1.trans h1) h2
  · exact zero_le_one
  · exact le_rfl

/-- $N_{i+1}(\mu) \le N_i(\mu) + 1$: passing from $T_i$ to $T_{i+1}$ adds at most one eigenvalue at
or below $\mu$. This follows from weak interlacing. -/
theorem count_succ_le (i : ℕ) (μ : ℝ) : count d b (i + 1) μ ≤ count d b i μ + 1 := by
  rw [count_eq_sum, count_eq_sum, Fin.sum_univ_castSucc]
  refine add_le_add (Finset.sum_le_sum fun k _ => ?_) (by split_ifs <;> simp)
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd ((eigenvalues_interlace d b i k).2.trans h1) h2
  · exact zero_le_one
  · exact le_rfl

/-! ### The sign convention and the sign changes -/

/-- The sign $\sigma_i(\mu) \in \{1, -1\}$ attached to $p_i(\mu)$ by the convention of Property 5.11
of [quarteroni2000numerical]: $\sigma_0(\mu) = 1$, and for $i \ge 1$, $\sigma_i(\mu)$ is the
sign of $p_i(\mu)$ when $p_i(\mu) \neq 0$, and $-\sigma_{i-1}(\mu)$ when $p_i(\mu) = 0$. -/
noncomputable def sign (μ : ℝ) : ℕ → ℝ
  | 0 => 1
  | (i + 1) =>
    if (seq d b (i + 1)).eval μ = 0 then -sign μ i
    else if 0 < (seq d b (i + 1)).eval μ then 1 else -1

/-- The sign attached to $p_0(\mu) = 1$ is $\sigma_0(\mu) = 1$. -/
@[simp] theorem sign_zero (μ : ℝ) : sign d b μ 0 = 1 := rfl

/-- The sign convention for $i \ge 1$: $\sigma_i(\mu) = -\sigma_{i-1}(\mu)$ if $p_i(\mu) = 0$,
$\sigma_i(\mu) = 1$ if $p_i(\mu) > 0$, and $\sigma_i(\mu) = -1$ if $p_i(\mu) < 0$. -/
theorem sign_succ (μ : ℝ) (i : ℕ) :
    sign d b μ (i + 1) =
      if (seq d b (i + 1)).eval μ = 0 then -sign d b μ i
      else if 0 < (seq d b (i + 1)).eval μ then 1 else -1 := rfl

/-- The number $s_n(\mu)$ of sign changes in $p_0(\mu), \dots, p_n(\mu)$: the number of $i < n$ with
$\sigma_{i+1}(\mu) \neq \sigma_i(\mu)$, where the signs $\sigma_i$ follow the convention of
`Sturm.sign` for vanishing members. -/
noncomputable def signChanges (n : ℕ) (μ : ℝ) : ℕ :=
  ((range n).filter fun i => sign d b μ (i + 1) ≠ sign d b μ i).card

/-- For the empty matrix, $s_0(\mu) = 0$. -/
@[simp] theorem signChanges_zero (μ : ℝ) : signChanges d b 0 μ = 0 := by simp [signChanges]

/-- $s_{n+1}(\mu) = s_n(\mu) + 1$ if $\sigma_{n+1}(\mu) \neq \sigma_n(\mu)$, and
$s_{n+1}(\mu) = s_n(\mu)$ otherwise. -/
theorem signChanges_succ (n : ℕ) (μ : ℝ) :
    signChanges d b (n + 1) μ =
      signChanges d b n μ + if sign d b μ (n + 1) ≠ sign d b μ n then 1 else 0 := by
  rw [signChanges, signChanges, Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

/-- If $\mu$ is not an eigenvalue of $T_n$, then $p_n(\mu) > 0$ if and only if $N_n(\mu)$ is even.

The product $p_n(\mu) = \prod_k (\lambda_k(T_n) - \mu)$ has one negative factor for each
eigenvalue below $\mu$. -/
theorem eval_seq_pos_iff {n : ℕ} {μ : ℝ} (hμ : ∀ k, eigenvalues d b n k ≠ μ) :
    0 < (seq d b n).eval μ ↔ Even (count d b n μ) := by
  have hfac : ∀ k, eigenvalues d b n k - μ
      = (if eigenvalues d b n k ≤ μ then (-1 : ℝ) else 1) * |eigenvalues d b n k - μ| := by
    intro k
    split_ifs with h
    · rw [abs_of_neg (sub_neg.mpr (lt_of_le_of_ne h (hμ k)))]
      ring
    · rw [abs_of_pos (sub_pos.mpr (lt_of_not_ge h)), one_mul]
  have hpos : 0 < ∏ k, |eigenvalues d b n k - μ| :=
    Finset.prod_pos fun k _ => abs_pos.mpr (sub_ne_zero.mpr (hμ k))
  rw [eval_seq_eq_prod, Finset.prod_congr rfl fun k _ => hfac k, Finset.prod_mul_distrib,
    Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const, ← count]
  rcases Nat.even_or_odd (count d b n μ) with h | h
  · rw [h.neg_one_pow, one_mul]
    exact ⟨fun _ => h, fun _ => hpos⟩
  · rw [h.neg_one_pow, neg_one_mul, neg_pos]
    exact ⟨fun h' => absurd (h'.trans hpos) (lt_irrefl _),
      fun h' => absurd h' (Nat.not_even_iff_odd.mpr h)⟩

/-- **The sign invariant.** If $b$ is unreduced at order $i$, then the sign attached to $p_i(\mu)$
is
$$\sigma_i(\mu) = (-1)^{N_i(\mu)}.$$

Off the roots of $p_i$ this is `Sturm.eval_seq_pos_iff`. At a root of $p_{i+1}$, strict
interlacing puts exactly one more eigenvalue of $T_{i+1}$ than of $T_i$ at or below $\mu$. -/
theorem sign_eq_neg_one_pow (μ : ℝ) (i : ℕ) (hb : IsUnreduced b i) :
    sign d b μ i = (-1) ^ count d b i μ := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [sign_succ]
    by_cases h0 : (seq d b (i + 1)).eval μ = 0
    · rw [ite_eq_left h0, ih (hb.mono (by omega))]
      obtain ⟨k, hk⟩ := exists_eigenvalues_eq_of_eval_eq_zero d b h0
      rw [← hk, count_eigenvalues d b hb k, count_eigenvalues_succ d b hb k,
        show i + 1 - (k : ℕ) = (i - k) + 1 by have := k.isLt; omega, pow_succ]
      ring
    · rw [ite_eq_right h0]
      have hμ : ∀ k, eigenvalues d b (i + 1) k ≠ μ := fun k hk =>
        h0 (hk ▸ eval_seq_eigenvalues d b (i + 1) k)
      rcases Nat.even_or_odd (count d b (i + 1) μ) with h | h
      · rw [ite_eq_left ((eval_seq_pos_iff d b hμ).mpr h), h.neg_one_pow]
      · rw [ite_eq_right fun h' => Nat.not_even_iff_odd.mpr h ((eval_seq_pos_iff d b hμ).mp h'),
          h.neg_one_pow]

/-- **The Sturm count** (Property 5.11 of [quarteroni2000numerical]). If $b$ is unreduced at order
$n$, then for every $\mu \in \mathbb{R}$ the number of sign changes in
$p_0(\mu), \dots, p_n(\mu)$, where a vanishing member takes the sign opposite to that of its
predecessor, is the number of eigenvalues of $T_n$ that are at most $\mu$:
$$s_n(\mu) = N_n(\mu).$$
The same theorem is in Wilkinson, *The Algebraic Eigenvalue Problem*, Chapter 5, §37, and in
Golub and Van Loan, *Matrix Computations* (1989), Theorem 8.5.1.

The source counts the eigenvalues strictly less than $\mu$. The two counts agree off the
spectrum. At an eigenvalue, the sign convention of the source counts $\mu$ itself: for $n = 1$
and $\mu = d_0$, the sequence $1, 0$ has one sign change. -/
theorem signChanges_eq_count (n : ℕ) (hb : IsUnreduced b n) (μ : ℝ) :
    signChanges d b n μ = count d b n μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [signChanges_succ, ih (hb.mono (by omega)), sign_eq_neg_one_pow d b μ (n + 1) hb,
      sign_eq_neg_one_pow d b μ n (hb.mono (by omega))]
    have h1 := count_le_count_succ d b n μ
    have h2 := count_succ_le d b n μ
    rcases Nat.lt_or_ge (count d b n μ) (count d b (n + 1) μ) with h | h
    · have heq : count d b (n + 1) μ = count d b n μ + 1 := by omega
      rw [heq, pow_succ, ite_eq_left]
      intro h'
      have : (-1 : ℝ) ^ count d b n μ ≠ 0 := pow_ne_zero _ (by norm_num)
      rw [mul_neg_one] at h'
      exact this (by linarith)
    · have heq : count d b (n + 1) μ = count d b n μ := le_antisymm h h1
      rw [heq, ite_eq_right (by simp), add_zero]

/-- **The Sturm count** with `Polynomial.countRootsIn`. If $b$ is unreduced at order $n$, then
$s_n(\mu)$ is the number of roots of the characteristic polynomial of $T_n$ in $(-\infty, \mu]$,
counted with multiplicity. All these roots are simple, by `Sturm.eigenvalues_simple`. -/
theorem signChanges_eq_countRootsIn (n : ℕ) (hb : IsUnreduced b n) (μ : ℝ) :
    signChanges d b n μ =
      (Matrix.symmTridiagonalOf d b n).charpoly.countRootsIn (Set.Iic μ) := by
  rw [signChanges_eq_count d b n hb, countRootsIn_Iic_eq_count]

/-- If $b$ is unreduced at order $n$, then $s_n(\mu)$ is monotone in $\mu$. -/
theorem signChanges_monotone (n : ℕ) (hb : IsUnreduced b n) :
    Monotone (signChanges d b n) := by
  intro μ ν h
  rw [signChanges_eq_count d b n hb, signChanges_eq_count d b n hb]
  exact count_mono d b n h

/-! ### The Gershgorin interval -/

/-- The Gershgorin radius $r_i$ of row $i$ of $T_n$: $r_i = |b_{i-1}| + |b_i|$, where the term
$|b_{i-1}|$ is omitted in the first row and the term $|b_i|$ is omitted in the last row. -/
noncomputable def gershgorinRadius (n : ℕ) (i : Fin n) : ℝ :=
  (if 0 < (i : ℕ) then |b (i - 1)| else 0) + if (i : ℕ) + 1 < n then |b i| else 0

/-- The sum of the absolute values of the off-diagonal entries in row $i$ of $T_n$ is the Gershgorin
radius $r_i$. -/
theorem sum_erase_abs_eq_gershgorinRadius (n : ℕ) (i : Fin n) :
    ∑ j ∈ univ.erase i, |Matrix.symmTridiagonalOf d b n i j| = gershgorinRadius b n i := by
  have hsplit : ∀ j ∈ univ.erase i, |Matrix.symmTridiagonalOf d b n i j|
      = (if (j : ℕ) + 1 = i then |b j| else 0) + if (i : ℕ) + 1 = j then |b i| else 0 := by
    intro j hj
    have hji : (j : ℕ) ≠ i := fun h => (Finset.mem_erase.mp hj).1 (Fin.ext h)
    rw [Matrix.symmTridiagonalOf_apply, ite_eq_right (Ne.symm hji)]
    by_cases h1 : (i : ℕ) + 1 = j
    · have h2 : ¬ ((j : ℕ) + 1 = i) := by omega
      simp [h1, h2]
    · by_cases h2 : (j : ℕ) + 1 = i
      · simp [h1, h2]
      · simp [h1, h2]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, gershgorinRadius]
  congr 1
  · by_cases hi : 0 < (i : ℕ)
    · rw [ite_eq_left hi]
      have hmem : (⟨(i : ℕ) - 1, by omega⟩ : Fin n) ∈ univ.erase i := by
        simp [Fin.ext_iff]
        omega
      rw [Finset.sum_eq_single_of_mem _ hmem]
      · have : ((i : ℕ) - 1) + 1 = i := by omega
        simp [this]
      · intro j _ hj
        have : ¬ ((j : ℕ) + 1 = i) := fun h => hj (Fin.ext (by simp; omega))
        simp [this]
    · rw [ite_eq_right hi]
      refine Finset.sum_eq_zero fun j _ => ?_
      have : ¬ ((j : ℕ) + 1 = i) := by omega
      simp [this]
  · by_cases hi : (i : ℕ) + 1 < n
    · rw [ite_eq_left hi]
      have hmem : (⟨(i : ℕ) + 1, hi⟩ : Fin n) ∈ univ.erase i := by
        simp [Fin.ext_iff]
      rw [Finset.sum_eq_single_of_mem _ hmem]
      · simp
      · intro j _ hj
        have : ¬ ((i : ℕ) + 1 = j) := fun h => hj (Fin.ext h.symm)
        simp [this]
    · rw [ite_eq_right hi]
      refine Finset.sum_eq_zero fun j _ => ?_
      have : ¬ ((i : ℕ) + 1 = j) := fun h => hi (h ▸ j.isLt)
      simp [this]

/-- **Gershgorin's theorem for $T_n$.** Every real eigenvalue $\mu$ of $T_n$ satisfies
$|\mu - d_i| \le r_i$ for some $i < n$.

This gives the interval of Program 44 in §5.10.2 of [quarteroni2000numerical]. -/
theorem exists_abs_sub_le_of_mem_spectrum {n : ℕ} {μ : ℝ}
    (hμ : μ ∈ spectrum ℝ (Matrix.symmTridiagonalOf d b n)) :
    ∃ i : Fin n, |μ - d i| ≤ gershgorinRadius b n i := by
  rw [← Matrix.spectrum_toLin', ← Module.End.hasEigenvalue_iff_mem_spectrum] at hμ
  obtain ⟨i, hi⟩ := eigenvalue_mem_ball hμ
  refine ⟨i, ?_⟩
  rw [Metric.mem_closedBall, Real.dist_eq] at hi
  simp only [Real.norm_eq_abs] at hi
  rw [sum_erase_abs_eq_gershgorinRadius] at hi
  have hd : Matrix.symmTridiagonalOf d b n i i = d i := by simp [Matrix.symmTridiagonalOf_apply]
  rwa [hd] at hi

/-- For every $\mu \in \mathbb{R}$, $p_n(\mu) = 0$ if and only if $\mu$ is a root of the
characteristic polynomial of $T_n$. -/
theorem eval_seq_eq_zero_iff (n : ℕ) (μ : ℝ) :
    (seq d b n).eval μ = 0 ↔ (Matrix.symmTridiagonalOf d b n).charpoly.eval μ = 0 := by
  rw [seq_eq_charpoly, eval_mul, eval_pow, eval_neg, eval_one, mul_eq_zero,
    or_iff_right (pow_ne_zero _ (by norm_num))]

/-- Every sorted eigenvalue $\lambda_k(T_n)$ is in the real spectrum of $T_n$. -/
theorem eigenvalues_mem_spectrum (n : ℕ) (k : Fin n) :
    eigenvalues d b n k ∈ spectrum ℝ (Matrix.symmTridiagonalOf d b n) := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, IsRoot.def, ← eval_seq_eq_zero_iff]
  exact eval_seq_eigenvalues d b n k

/-- **The Gershgorin interval encloses the spectrum.** Every real eigenvalue of $T_n$ lies in the
interval
$$\left[ \min_{i < n} (d_i - r_i), \ \max_{i < n} (d_i + r_i) \right],$$
where $r_i$ are the Gershgorin radii. This is the interval $[\alpha, \beta]$ of Givens' method
in §5.10.2 of [quarteroni2000numerical].

The minimum and the maximum are `iInf` and `iSup` over `Fin n`. For $n = 0$ they take the junk
value $0$, but the spectrum is then empty. -/
theorem spectrum_subset_Icc (n : ℕ) :
    spectrum ℝ (Matrix.symmTridiagonalOf d b n) ⊆
      Set.Icc (⨅ i : Fin n, (d i - gershgorinRadius b n i))
        (⨆ i : Fin n, (d i + gershgorinRadius b n i)) := by
  intro μ hμ
  obtain ⟨i, hi⟩ := exists_abs_sub_le_of_mem_spectrum d b hμ
  rw [abs_le] at hi
  have h1 : (⨅ j : Fin n, (d j - gershgorinRadius b n j)) ≤ d i - gershgorinRadius b n i :=
    ciInf_le (f := fun j : Fin n => d j - gershgorinRadius b n j) (Set.finite_range _).bddBelow i
  have h2 : d i + gershgorinRadius b n i ≤ ⨆ j : Fin n, (d j + gershgorinRadius b n j) :=
    le_ciSup (f := fun j : Fin n => d j + gershgorinRadius b n j) (Set.finite_range _).bddAbove i
  constructor <;> linarith [hi.1, hi.2]

/-- Every sorted eigenvalue $\lambda_k(T_n)$ lies in the Gershgorin interval
$[\min_i (d_i - r_i), \max_i (d_i + r_i)]$. -/
theorem eigenvalues_mem_Icc (n : ℕ) (k : Fin n) :
    eigenvalues d b n k ∈ Set.Icc (⨅ i : Fin n, (d i - gershgorinRadius b n i))
      (⨆ i : Fin n, (d i + gershgorinRadius b n i)) :=
  spectrum_subset_Icc d b n (eigenvalues_mem_spectrum d b n k)

/-- If $a < \min_i (d_i - r_i)$, then $N_n(a) = 0$: no eigenvalue lies at or below a point below the
Gershgorin interval. -/
theorem count_eq_zero_of_lt {n : ℕ} {a : ℝ}
    (ha : a < ⨅ i : Fin n, (d i - gershgorinRadius b n i)) : count d b n a = 0 := by
  rw [count, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro k _
  exact not_le.mpr (lt_of_lt_of_le ha (eigenvalues_mem_Icc d b n k).1)

/-- If $\max_i (d_i + r_i) \le b'$, then $N_n(b') = n$: every eigenvalue lies at or below a point at
or above the Gershgorin interval. -/
theorem count_eq_of_le {n : ℕ} {b' : ℝ}
    (hb' : (⨆ i : Fin n, (d i + gershgorinRadius b n i)) ≤ b') : count d b n b' = n := by
  rw [count, Finset.filter_true_of_mem fun k _ => (eigenvalues_mem_Icc d b n k).2.trans hb',
    Finset.card_univ, Fintype.card_fin]

/-! ### Givens' bisection -/

/-- One step of **Givens' bisection** for the $j$-th largest eigenvalue of $T_n$, with $j$ counted
from $1$ as in Program 42 of [quarteroni2000numerical]. Let $c = (a + b') / 2$ be the midpoint
of the interval $(a, b')$. The step keeps $(a, c)$ if $n - j < s_n(c)$, and $(c, b')$ otherwise.

For an unreduced matrix, $s_n(c)$ is the number of eigenvalues at most $c$
(`Sturm.signChanges_eq_count`). So the step keeps $(a, c)$ when more than $n - j$ eigenvalues
are at most $c$. -/
noncomputable def bisectionStep (n idx : ℕ) (ab : ℝ × ℝ) : ℝ × ℝ :=
  if n - idx < signChanges d b n ((ab.1 + ab.2) / 2) then (ab.1, (ab.1 + ab.2) / 2)
  else ((ab.1 + ab.2) / 2, ab.2)

/-- The interval after $r$ steps of Givens' bisection from the interval $(a, b')$. -/
noncomputable def bisectionIterate (n idx : ℕ) (ab : ℝ × ℝ) : ℕ → ℝ × ℝ
  | 0 => ab
  | (r + 1) => bisectionStep d b n idx (bisectionIterate n idx ab r)

/-- After $0$ steps, Givens' bisection gives the starting interval. -/
@[simp] theorem bisectionIterate_zero (n idx : ℕ) (ab : ℝ × ℝ) :
    bisectionIterate d b n idx ab 0 = ab := rfl

/-- Step $r + 1$ of Givens' bisection is one bisection step applied to the interval after $r$ steps.
-/
theorem bisectionIterate_succ (n idx : ℕ) (ab : ℝ × ℝ) (r : ℕ) :
    bisectionIterate d b n idx ab (r + 1)
      = bisectionStep d b n idx (bisectionIterate d b n idx ab r) :=
  rfl

/-- A bisection step halves the length of the interval: from $(a, b')$ to an interval of length
$(b' - a) / 2$. -/
theorem bisectionStep_length (n idx : ℕ) (ab : ℝ × ℝ) :
    (bisectionStep d b n idx ab).2 - (bisectionStep d b n idx ab).1 = (ab.2 - ab.1) / 2 := by
  rw [bisectionStep]
  split_ifs <;> simp only <;> ring

/-- After $r$ bisection steps from $(a, b')$, the interval has length $(b' - a) / 2^r$. -/
theorem bisectionIterate_length (n idx : ℕ) (ab : ℝ × ℝ) (r : ℕ) :
    (bisectionIterate d b n idx ab r).2 - (bisectionIterate d b n idx ab r).1
      = (ab.2 - ab.1) / 2 ^ r := by
  induction r with
  | zero => simp
  | succ r ih => rw [bisectionIterate_succ, bisectionStep_length, ih, pow_succ, div_div]

/-- A bisection step preserves the bracketing condition $s_n(a) \le n - j < s_n(b')$ on the end
points $a$ and $b'$ of the interval. -/
theorem bisectionStep_invariant (n idx : ℕ) {ab : ℝ × ℝ}
    (h : signChanges d b n ab.1 ≤ n - idx ∧ n - idx < signChanges d b n ab.2) :
    signChanges d b n (bisectionStep d b n idx ab).1 ≤ n - idx ∧
      n - idx < signChanges d b n (bisectionStep d b n idx ab).2 := by
  rw [bisectionStep]
  split_ifs with hc
  · exact ⟨h.1, hc⟩
  · exact ⟨not_lt.mp hc, h.2⟩

/-- If the starting interval $(a, b')$ satisfies $s_n(a) \le n - j < s_n(b')$, then the interval
after $r$ bisection steps satisfies the same condition, for every $r$. -/
theorem bisectionIterate_invariant (n idx : ℕ) {ab : ℝ × ℝ}
    (h : signChanges d b n ab.1 ≤ n - idx ∧ n - idx < signChanges d b n ab.2) (r : ℕ) :
    signChanges d b n (bisectionIterate d b n idx ab r).1 ≤ n - idx ∧
      n - idx < signChanges d b n (bisectionIterate d b n idx ab r).2 := by
  induction r with
  | zero => exact h
  | succ r ih => exact bisectionStep_invariant d b n idx ih

/-- Let $b$ be unreduced at order $n$, let $1 \le j \le n$, and let $a, b' \in \mathbb{R}$. If at
most $n - j$ eigenvalues of $T_n$ are at most $a$, and more than $n - j$ eigenvalues are at most
$b'$, that is, $N_n(a) \le n - j < N_n(b')$, then the $j$-th largest eigenvalue lies in
$(a, b']$:
$$a < \lambda_{j-1}(T_n) \le b'.$$
-/
theorem eigenvalues_mem_Ioc_of_count {n idx : ℕ} (hb : IsUnreduced b n) (hidx : 1 ≤ idx)
    (hidxn : idx ≤ n) {a b' : ℝ} (ha : count d b n a ≤ n - idx) (hb' : n - idx < count d b n b') :
    eigenvalues d b n ⟨idx - 1, by omega⟩ ∈ Set.Ioc a b' := by
  set k : Fin n := ⟨idx - 1, by omega⟩ with hk
  constructor
  · by_contra hle
    push Not at hle
    have : count d b n (eigenvalues d b n k) ≤ count d b n a := count_mono d b n hle
    rw [count_eigenvalues d b hb k] at this
    simp only [hk] at this
    omega
  · by_contra hlt
    push Not at hlt
    -- every eigenvalue at most `b'` has index above `k`
    have hsub : (univ.filter fun j => eigenvalues d b n j ≤ b') ⊆ Finset.Ioi k := by
      intro j hj
      simp only [mem_filter, mem_univ, true_and] at hj
      rw [Finset.mem_Ioi]
      by_contra hjk
      push Not at hjk
      have := antitone_eigenvalues d b n hjk
      linarith
    have := Finset.card_le_card hsub
    rw [Fin.card_Ioi] at this
    simp only [hk] at this
    rw [count] at hb'
    omega

/-- **Givens' bisection converges** (§5.10.2 of [quarteroni2000numerical]). Let $b$ be unreduced at
order $n$, let $1 \le j \le n$, and let the starting interval $(a, b')$ satisfy
$s_n(a) \le n - j < s_n(b')$. Then for every $r$, the $j$-th largest eigenvalue
$\lambda_{j-1}(T_n)$ lies in the half-open interval $(a_r, b'_r]$ given by $r$ bisection steps.

The interval has length $(b' - a) / 2^r$ (`Sturm.bisectionIterate_length`), so its midpoint is
within $(b' - a) / 2^{r+1}$ of the eigenvalue. The Gershgorin interval gives a starting interval
(`Sturm.signChanges_gershgorin`). -/
theorem eigenvalues_mem_bisectionIterate {n idx : ℕ} (hb : IsUnreduced b n)
    (hidx : 1 ≤ idx)
    (hidxn : idx ≤ n) {ab : ℝ × ℝ}
    (h : signChanges d b n ab.1 ≤ n - idx ∧ n - idx < signChanges d b n ab.2) (r : ℕ) :
    eigenvalues d b n ⟨idx - 1, by omega⟩ ∈
      Set.Ioc (bisectionIterate d b n idx ab r).1 (bisectionIterate d b n idx ab r).2 := by
  have hinv := bisectionIterate_invariant d b n idx h r
  rw [signChanges_eq_count d b n hb, signChanges_eq_count d b n hb] at hinv
  exact eigenvalues_mem_Ioc_of_count d b hb hidx hidxn hinv.1 hinv.2

/-- **Givens' bisection converges**, for Mathlib's sorted eigenvalues. Under the hypotheses of
`Sturm.eigenvalues_mem_bisectionIterate`, the $j$-th largest eigenvalue, the entry $j - 1$ of
`Matrix.IsHermitian.eigenvalues₀`, lies in the interval $(a_r, b'_r]$ given by $r$ bisection
steps, for every $r$. -/
theorem eigenvalues₀_mem_bisectionIterate {n idx : ℕ} (hb : IsUnreduced b n)
    (hidx : 1 ≤ idx)
    (hidxn : idx ≤ n) (hT : (Matrix.symmTridiagonalOf d b n).IsHermitian) {ab : ℝ × ℝ}
    (h : signChanges d b n ab.1 ≤ n - idx ∧ n - idx < signChanges d b n ab.2) (r : ℕ) :
    hT.eigenvalues₀ ⟨idx - 1, by simp; omega⟩ ∈
      Set.Ioc (bisectionIterate d b n idx ab r).1 (bisectionIterate d b n idx ab r).2 :=
  eigenvalues_mem_bisectionIterate d b hb hidx hidxn h r

/-- **Givens' bisection from a lower bound of the spectrum** (§5.10.2 of [quarteroni2000numerical]).
Let $b$ be unreduced at order $n$, let $1 \le j \le n$, and let the starting interval $(a, b')$
satisfy $a \le \lambda_k(T_n)$ for every $k$ and $n - j < s_n(b')$. Then for every $r$, the
$j$-th largest eigenvalue $\lambda_{j-1}(T_n)$ lies in the closed interval $[a_r, b'_r]$ given
by $r$ bisection steps.

When $s_n(a) \le n - j$ this is `Sturm.eigenvalues_mem_bisectionIterate`. Otherwise $a$ is the
smallest eigenvalue, $j = n$, and the left end point never moves. In this case the half-open
interval of `Sturm.eigenvalues_mem_bisectionIterate` does not contain the eigenvalue; this
happens for the Gershgorin interval when its left end is an eigenvalue. -/
theorem eigenvalues_mem_Icc_bisectionIterate {n idx : ℕ} (hb : IsUnreduced b n) (hidx : 1 ≤ idx)
    (hidxn : idx ≤ n) {ab : ℝ × ℝ} (ha : ∀ k, ab.1 ≤ eigenvalues d b n k)
    (hb' : n - idx < signChanges d b n ab.2) (r : ℕ) :
    eigenvalues d b n ⟨idx - 1, by omega⟩ ∈
      Set.Icc (bisectionIterate d b n idx ab r).1 (bisectionIterate d b n idx ab r).2 := by
  have hn : 0 < n := by omega
  by_cases has : signChanges d b n ab.1 ≤ n - idx
  · exact Set.Ioc_subset_Icc_self (eigenvalues_mem_bisectionIterate d b hb hidx hidxn ⟨has, hb'⟩ r)
  push Not at has
  -- `a` is an eigenvalue, hence the smallest one, and `idx = n`
  have hpos : 0 < count d b n ab.1 := by
    rw [← signChanges_eq_count d b n hb]; omega
  obtain ⟨k, hk⟩ : ∃ k, eigenvalues d b n k ≤ ab.1 := by
    rw [count, Finset.card_pos] at hpos
    obtain ⟨k, hk⟩ := hpos
    exact ⟨k, (Finset.mem_filter.mp hk).2⟩
  have hlast : eigenvalues d b n ⟨n - 1, by omega⟩ = ab.1 :=
    le_antisymm ((antitone_eigenvalues d b n
      (Fin.le_iff_val_le_val.mpr (by simp; omega))).trans hk) (ha _)
  have hcount : count d b n ab.1 = 1 := by
    have h := count_eigenvalues d b (n := n) hb ⟨n - 1, by omega⟩
    rw [hlast] at h
    rw [h]
    simp only
    omega
  have hidx' : idx = n := by
    rw [signChanges_eq_count d b n hb, hcount] at has
    omega
  subst hidx'
  -- the right end lies above some eigenvalue, hence above `a`
  have hab : ab.1 ≤ ab.2 := by
    have hpos' : 0 < count d b idx ab.2 := by
      rw [← signChanges_eq_count d b idx hb]; omega
    rw [count, Finset.card_pos] at hpos'
    obtain ⟨k', hk'⟩ := hpos'
    exact (ha k').trans (Finset.mem_filter.mp hk').2
  -- the left endpoint never moves
  have hleft : ∀ r, (bisectionIterate d b idx idx ab r).1 = ab.1 ∧
      ab.1 ≤ (bisectionIterate d b idx idx ab r).2 := by
    intro r
    induction r with
    | zero => exact ⟨rfl, hab⟩
    | succ r ih =>
      have hc : ab.1 ≤ ((bisectionIterate d b idx idx ab r).1 +
          (bisectionIterate d b idx idx ab r).2) / 2 := by
        rw [ih.1]; linarith [ih.2]
      have hs : idx - idx < signChanges d b idx
          (((bisectionIterate d b idx idx ab r).1 + (bisectionIterate d b idx idx ab r).2) / 2) :=
        lt_of_lt_of_le has (signChanges_monotone d b idx hb hc)
      rw [bisectionIterate_succ, bisectionStep, ite_eq_left hs]
      exact ⟨ih.1, hc⟩
  rw [hlast, (hleft r).1]
  exact ⟨le_rfl, (hleft r).2⟩

/-- Let $b$ be unreduced at order $n$ and let $1 \le j \le n$. If $a$ is below the Gershgorin
interval and $b'$ is at or above it, that is, $a < \min_i (d_i - r_i)$ and
$\max_i (d_i + r_i) \le b'$, then
$$s_n(a) \le n - j < s_n(b').$$
In fact $s_n(a) = 0$ and $s_n(b') = n$. So these end points give a starting interval for Givens'
bisection. -/
theorem signChanges_gershgorin {n idx : ℕ} (hb : IsUnreduced b n) (hidx : 1 ≤ idx)
    (hidxn : idx ≤ n)
    {a b' : ℝ} (ha : a < ⨅ i : Fin n, (d i - gershgorinRadius b n i))
    (hb' : (⨆ i : Fin n, (d i + gershgorinRadius b n i)) ≤ b') :
    signChanges d b n a ≤ n - idx ∧ n - idx < signChanges d b n b' := by
  rw [signChanges_eq_count d b n hb, signChanges_eq_count d b n hb, count_eq_zero_of_lt d b ha,
    count_eq_of_le d b hb']
  omega

end Sturm

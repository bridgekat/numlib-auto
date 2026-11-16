/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: a file beside `Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Symmetric spectra and the half-sum of two involutions

This file reads characteristic polynomials off the traces of matrix powers, and applies this to the
spectrum of the half-sum of two symmetric involutions of trace zero. A Hermitian matrix $A$ whose
odd powers have trace zero has a spectrum that is symmetric about $0$: the eigenvalues $\lambda_i$
have vanishing odd power sums $\sum_i \lambda_i^{2j+1} = \operatorname{tr} A^{2j+1}$, so the
multiset of the $-\lambda_i$ equals the multiset of the $\lambda_i$, and
$\det(zI + A) = \det(zI - A)$.

Let $A$ and $B$ be real symmetric matrices with $A^2 = B^2 = I$ and
$\operatorname{tr} A = \operatorname{tr} B = 0$. Then every odd power of $A + B$ has trace zero. If
the eigenvalues of $AB$ are the $m$ pairs $e^{\pm i \theta_k}$, then the eigenvalues of $(A + B)/2$
are the $m$ pairs $\pm \cos(\theta_k / 2)$. This is a result of Ammar, Gragg and Reichel, and it is
the spectral half of Fact 2 in §12.2.10 of [golub2013matrix].

## Main results

* `Matrix.roots_charpoly_diagonal`: the roots of the characteristic polynomial of a diagonal matrix
  are its diagonal entries.
* `Matrix.charpoly_unitary_conj`: a unitary conjugation $M \mapsto U M U^H$ keeps the characteristic
  polynomial.
* `Matrix.IsHermitian.star_eigenvectorUnitary_mul_mul`: $U^H A U = \operatorname{diag}(\lambda)$ for
  the eigenvector unitary $U$ of a Hermitian matrix $A$.
* `Matrix.IsHermitian.eq_conj_diagonal`: $A = U \operatorname{diag}(\lambda) U^H$ for the same $U$.
* `Matrix.IsHermitian.transpose_eigenvectorUnitary_mul_mul`: the real form
  $Q^T A Q = \operatorname{diag}(\lambda)$.
* `Matrix.trace_add_pow_odd_eq_zero`: if $A^2 = B^2 = I$ and
  $\operatorname{tr} A = \operatorname{tr} B = 0$, then $\operatorname{tr} (A + B)^{2j+1} = 0$.
* `Fintype.map_neg_eq_of_sum_pow_odd`: over a field of characteristic zero, a finite family whose
  odd power sums vanish is symmetric about $0$, as a multiset.
* `Matrix.IsHermitian.trace_pow_eq_sum`: $\operatorname{tr} A^k = \sum_i \lambda_i^k$ for a
  Hermitian matrix $A$.
* `Matrix.IsHermitian.charpoly_neg_of_trace_pow_odd`: a Hermitian matrix whose odd powers have trace
  zero satisfies $p_{-A} = p_A$.
* `Matrix.card_eq_of_charpoly_eq_prod`: a matrix whose characteristic polynomial is a product of $m$
  monic quadratics has order $2m$.
* `Matrix.charpoly_half_add_of_involutive`: the eigenvalues of $(A + B)/2$ are
  $\pm \cos(\theta_k / 2)$ when those of $AB$ are $e^{\pm i \theta_k}$.

## Notation

* $p_M$: the characteristic polynomial $\det(XI - M)$ of a square matrix $M$, `Matrix.charpoly M`.
-/

open Finset Polynomial

namespace Matrix

/-! ### Diagonal matrices and unitary conjugates -/

/-- Let $R$ be a commutative ring without zero divisors, and let $d \in R^n$. The roots of the
characteristic polynomial of the diagonal matrix $\operatorname{diag}(d)$, counted with
multiplicity, are the entries $d_i$: the multiset of roots is the multiset of the $d_i$. -/
theorem roots_charpoly_diagonal {R n : Type*} [CommRing R] [IsDomain R] [Fintype n]
    [DecidableEq n] (d : n → R) :
    (diagonal d).charpoly.roots = Multiset.map d Finset.univ.val := by
  rw [charpoly_diagonal, Polynomial.roots_prod]
  · simp
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

/-- Let $R$ be a commutative ring with a star operation, let $U \in R^{n \times n}$ be unitary, and
let $M \in R^{n \times n}$. Then $U M U^H$ has the same characteristic polynomial as $M$. -/
theorem charpoly_unitary_conj {R n : Type*} [CommRing R] [StarRing R] [Fintype n]
    [DecidableEq n] {U : Matrix n n R} (hU : U ∈ unitaryGroup n R) (M : Matrix n n R) :
    (U * M * star U).charpoly = M.charpoly := by
  rw [charpoly_mul_comm, ← Matrix.mul_assoc, mem_unitaryGroup_iff'.1 hU, Matrix.one_mul]

/-! ### The Hermitian spectral decomposition, unfolded -/

section Spectral

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The **spectral decomposition of a Hermitian matrix**, in the form
$U^H A U = \operatorname{diag}(\lambda)$. Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, and
let $A \in \mathbb{K}^{n \times n}$ be Hermitian, with the eigenvalues $\lambda_i$ and the
eigenvector unitary $U$ of Mathlib. Then
$$U^H A U = \operatorname{diag}(\lambda_1, \dots, \lambda_n).$$

This is Mathlib's `Matrix.IsHermitian.conjStarAlgAut_star_eigenvectorUnitary` without the
algebra automorphism. The matrix $U$ is `Matrix.IsHermitian.eigenvectorUnitary`, and $\lambda$
is `Matrix.IsHermitian.eigenvalues`. -/
theorem IsHermitian.star_eigenvectorUnitary_mul_mul {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    star (hA.eigenvectorUnitary : Matrix n n 𝕜) * A * (hA.eigenvectorUnitary : Matrix n n 𝕜) =
      diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
  simpa [Unitary.conjStarAlgAut_apply] using hA.conjStarAlgAut_star_eigenvectorUnitary

/-- The **spectral decomposition of a Hermitian matrix**, in the form
$A = U \operatorname{diag}(\lambda) U^H$. Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, and
let $A \in \mathbb{K}^{n \times n}$ be Hermitian, with the eigenvalues $\lambda_i$ and the
eigenvector unitary $U$ of Mathlib. Then
$$A = U \operatorname{diag}(\lambda_1, \dots, \lambda_n) U^H.$$

This is Mathlib's `Matrix.IsHermitian.spectral_theorem` without the algebra automorphism. -/
theorem IsHermitian.eq_conj_diagonal {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n 𝕜) * diagonal (fun i => ((hA.eigenvalues i : ℝ) : 𝕜))
      * (hA.eigenvectorUnitary : Matrix n n 𝕜)ᴴ := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]
  rfl

/-- Let $A \in \mathbb{R}^{n \times n}$ be symmetric, with the eigenvalues $\lambda_i$ and the
orthogonal eigenvector matrix $Q$ of Mathlib (`Matrix.IsHermitian.eigenvectorUnitary`). Then
$Q^T A Q = \operatorname{diag}(\lambda_1, \dots, \lambda_n)$. This is the real form of
`Matrix.IsHermitian.star_eigenvectorUnitary_mul_mul`. -/
theorem IsHermitian.transpose_eigenvectorUnitary_mul_mul {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix n n ℝ)ᵀ * A * (hA.eigenvectorUnitary : Matrix n n ℝ) =
      diagonal hA.eigenvalues := by
  have h := hA.star_eigenvectorUnitary_mul_mul
  rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id,
    Function.id_comp] at h

end Spectral

/-! ### Two involutions of trace zero -/

section Involution

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n R}

/-- Let $R$ be a commutative ring of characteristic zero without zero divisors, and let
$A, B \in R^{n \times n}$ with $A^2 = B^2 = I$ and
$\operatorname{tr} A = \operatorname{tr} B = 0$. Then $\operatorname{tr}\bigl(A \, ((A +
B)^2)^j\bigr) = 0$ for every $j \ge 0$; this is the main step for
`Matrix.trace_add_pow_odd_eq_zero`. -/
private theorem trace_mul_sq_pow_eq_zero [NoZeroDivisors R] [CharZero R] (hA : A * A = 1)
    (hB : B * B = 1) (htA : trace A = 0) (htB : trace B = 0) (j : ℕ) :
    trace (A * ((A + B) * (A + B)) ^ j) = 0 := by
  have hA' : ∀ M, A * (A * M) = M := fun M => by rw [← Matrix.mul_assoc, hA, Matrix.one_mul]
  have hB' : ∀ M, B * (B * M) = M := fun M => by rw [← Matrix.mul_assoc, hB, Matrix.one_mul]
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = (A + B) * (A + B) := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = A * B - B * A := ⟨_, rfl⟩
  rw [← hZ]
  have hZA : Commute Z A := by
    rw [Commute, SemiconjBy, hZ]
    simp only [add_mul, mul_add, Matrix.mul_assoc, hA, hB, hA', Matrix.mul_one, Matrix.one_mul]
    abel
  have hZB : Commute Z B := by
    rw [Commute, SemiconjBy, hZ]
    simp only [add_mul, mul_add, Matrix.mul_assoc, hA, hB, hB', Matrix.mul_one, Matrix.one_mul]
    abel
  have hDZ : Commute D Z := hD ▸ (hZA.symm.mul_left hZB.symm).sub_left
    (hZB.symm.mul_left hZA.symm)
  have hDA : D * A = -(A * D) := by
    rw [hD]
    simp only [sub_mul, mul_sub, Matrix.mul_assoc, hA, hA', Matrix.mul_one]
    abel
  have hDD : D * D = Z * Z - 4 • Z := by
    rw [hD, hZ]
    simp only [sub_mul, mul_sub, add_mul, mul_add, Matrix.mul_assoc, hA, hB, hA', hB',
      Matrix.mul_one, Matrix.one_mul]
    abel
  have hrec : ∀ j, trace (A * Z ^ (j + 2)) = 4 • trace (A * Z ^ (j + 1)) := fun j => by
    have h0 : trace (A * Z ^ j * (D * D)) = 0 := by
      have e : D * (A * Z ^ j * D) = -(A * Z ^ j * (D * D)) := by
        calc D * (A * Z ^ j * D) = D * A * Z ^ j * D := by simp only [Matrix.mul_assoc]
          _ = -(A * (D * Z ^ j) * D) := by
            rw [hDA]
            simp only [Matrix.neg_mul, Matrix.mul_assoc]
          _ = -(A * Z ^ j * (D * D)) := by
            rw [(hDZ.pow_right j).eq]
            simp only [Matrix.mul_assoc]
      have e' : trace (A * Z ^ j * (D * D)) = -trace (A * Z ^ j * (D * D)) := by
        rw [← trace_neg, ← e, ← Matrix.mul_assoc, trace_mul_comm]
      exact self_eq_neg.mp e'
    rw [hDD, Matrix.mul_sub, trace_sub, Matrix.mul_smul, trace_smul, sub_eq_zero] at h0
    rw [pow_succ, pow_succ, show A * (Z ^ j * Z * Z) = A * Z ^ j * (Z * Z) by
      simp only [Matrix.mul_assoc], h0, Matrix.mul_assoc]
  have hAZ : trace (A * Z) = 0 := by
    rw [hZ]
    simp only [add_mul, mul_add, hA, hB, hA', Matrix.mul_one, trace_add]
    rw [trace_mul_comm A (B * A), Matrix.mul_assoc, hA, Matrix.mul_one, htA, htB]
    simp
  have h2 : ∀ j, trace (A * Z ^ j) = 0 ∧ trace (A * Z ^ (j + 1)) = 0 := fun j => by
    induction j with
    | zero => exact ⟨by rw [pow_zero, Matrix.mul_one, htA], by rw [zero_add, pow_one, hAZ]⟩
    | succ j ih => exact ⟨ih.2, by rw [hrec, ih.2, smul_zero]⟩
  exact (h2 j).1

/-- Let $R$ be a commutative ring of characteristic zero without zero divisors, and let
$A, B \in R^{n \times n}$ satisfy $A^2 = B^2 = I$ and
$\operatorname{tr} A = \operatorname{tr} B = 0$. Then every odd power of $A + B$ has trace zero:
$$\operatorname{tr} (A + B)^{2j+1} = 0 \quad \text{for every } j \ge 0.$$

After expansion, every odd word in $A$ and $B$ reduces cyclically to a single letter. The proof
uses instead $Z = (A + B)^2$, which commutes with $A$ and $B$, and the commutator $D = AB - BA$,
which anticommutes with $A$ and commutes with $Z$. From $\operatorname{tr}(A Z^j D^2) =
-\operatorname{tr}(A Z^j D^2)$ and $D^2 = Z^2 - 4Z$, the traces $t_j = \operatorname{tr}(A Z^j)$
satisfy $t_{j+2} = 4 t_{j+1}$, and $t_0 = t_1 = 0$. -/
theorem trace_add_pow_odd_eq_zero [NoZeroDivisors R] [CharZero R] (hA : A * A = 1)
    (hB : B * B = 1) (htA : trace A = 0) (htB : trace B = 0) (j : ℕ) :
    trace ((A + B) ^ (2 * j + 1)) = 0 := by
  rw [pow_succ', pow_mul, sq, add_mul, trace_add, trace_mul_sq_pow_eq_zero hA hB htA htB,
    add_comm A B, trace_mul_sq_pow_eq_zero hB hA htB htA, add_zero]

end Involution

end Matrix

/-! ### Symmetric spectra from odd power sums -/

section PowerSum

variable {ι K : Type*} [Fintype ι] [Field K]

namespace Fintype

/-- Let $K$ be a field, and let $\mu_1, \dots, \mu_N \in K$ be a finite family with
$\sum_i \mu_i^{2j+1} = 0$ for every $j \ge 0$. Then every polynomial $p \in K[X]$ has the same
sum over the $-\mu_i$ as over the $\mu_i$:
$$\sum_i p(-\mu_i) = \sum_i p(\mu_i).$$

The odd part of $p$ sums to zero over both families. -/
theorem sum_eval_neg_eq_of_sum_pow_odd {μ : ι → K} (h : ∀ j, ∑ i, μ i ^ (2 * j + 1) = 0)
    (p : K[X]) : ∑ i, p.eval (-μ i) = ∑ i, p.eval (μ i) := by
  simp only [eval_eq_sum_range]
  refine Finset.sum_comm.trans ((Finset.sum_congr rfl fun k _ => ?_).trans Finset.sum_comm)
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  congr 1
  rcases Nat.even_or_odd k with hk | ⟨j, rfl⟩
  · simp only [hk.neg_pow]
  · simp only [Odd.neg_pow ⟨j, rfl⟩, Finset.sum_neg_distrib, h j, neg_zero]

/-- For a finite set $T \subseteq K$, a value $v$ and a family $\nu$ with values in $T$, the sum
$\sum_i \prod_{w \in T \setminus \{v\}} (\nu_i - w)$ equals the number of indices $i$ with
$\nu_i = v$, times $\prod_{w \in T \setminus \{v\}} (v - w)$. -/
private theorem sum_eval_prod_erase [DecidableEq K] {T : Finset K} (v : K) {ν : ι → K}
    (hν : ∀ i, ν i ∈ T) :
    ∑ i, (∏ w ∈ T.erase v, (X - C w)).eval (ν i) =
      #(univ.filter fun i => v = ν i) • ∏ w ∈ T.erase v, (v - w) := by
  have h : ∀ i, (∏ w ∈ T.erase v, (X - C w)).eval (ν i) =
      if v = ν i then ∏ w ∈ T.erase v, (v - w) else 0 := fun i => by
    rw [eval_prod]
    split_ifs with hv
    · simp [hv]
    · exact Finset.prod_eq_zero (mem_erase.2 ⟨Ne.symm hv, hν i⟩) (by simp)
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero,
    add_zero]

/-- A **family whose odd power sums vanish is symmetric**. Let $K$ be a field of characteristic
zero, and let $\mu_1, \dots, \mu_N \in K$ be a finite family with $\sum_i \mu_i^{2j+1} = 0$ for
every $j \ge 0$. Then the multiset of the $-\mu_i$ equals the multiset of the $\mu_i$.

The proof reads off each multiplicity: it sums a polynomial that vanishes at every other value
of $\pm\mu$, and uses `Fintype.sum_eval_neg_eq_of_sum_pow_odd`. -/
theorem map_neg_eq_of_sum_pow_odd [CharZero K] {μ : ι → K}
    (h : ∀ j, ∑ i, μ i ^ (2 * j + 1) = 0) :
    univ.val.map (fun i => -μ i) = univ.val.map μ := by
  classical
  refine Multiset.ext' fun v => ?_
  obtain ⟨T, hT⟩ : ∃ T : Finset K, T = univ.image μ ∪ univ.image fun i => -μ i := ⟨_, rfl⟩
  have hne : ∏ w ∈ T.erase v, (v - w) ≠ 0 :=
    prod_ne_zero_iff.2 fun w hw => sub_ne_zero.2 (Ne.symm (ne_of_mem_erase hw))
  have key := sum_eval_neg_eq_of_sum_pow_odd h (∏ w ∈ T.erase v, (X - C w))
  rw [sum_eval_prod_erase v (ν := fun i => -μ i) fun i => hT ▸ mem_union_right _
      (mem_image_of_mem _ (mem_univ i)),
    sum_eval_prod_erase v (ν := μ) fun i => hT ▸ mem_union_left _
      (mem_image_of_mem _ (mem_univ i)), nsmul_eq_mul, nsmul_eq_mul] at key
  rw [Multiset.count_map, Multiset.count_map]
  exact_mod_cast mul_right_cancel₀ hne key

end Fintype

end PowerSum

namespace Matrix

namespace IsHermitian

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}

/-- Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, and let $A \in \mathbb{K}^{n \times n}$ be
Hermitian with the eigenvalues $\lambda_1, \dots, \lambda_n$. Then for every $k \ge 0$,
$$\operatorname{tr} A^k = \sum_i \lambda_i^k.$$

The eigenvalues are `Matrix.IsHermitian.eigenvalues`, cast from $\mathbb{R}$ to $\mathbb{K}$. -/
theorem trace_pow_eq_sum (hA : A.IsHermitian) (k : ℕ) :
    trace (A ^ k) = ∑ i, (hA.eigenvalues i : 𝕜) ^ k := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [← map_pow, Unitary.conjStarAlgAut_apply, trace_mul_comm, ← Matrix.mul_assoc,
    Unitary.coe_star_mul_self, Matrix.one_mul, diagonal_pow, trace_diagonal]
  simp

/-- A **Hermitian matrix whose odd powers have trace zero has a spectrum symmetric about $0$**. Let
$\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, and let $A \in \mathbb{K}^{n \times n}$ be
Hermitian with $\operatorname{tr} A^{2j+1} = 0$ for every $j \ge 0$. Then $-A$ and $A$ have the
same characteristic polynomial.

The odd power sums of the eigenvalues vanish by `Matrix.IsHermitian.trace_pow_eq_sum`, so the
multiset of eigenvalues is symmetric by `Fintype.map_neg_eq_of_sum_pow_odd`. -/
theorem charpoly_neg_of_trace_pow_odd (hA : A.IsHermitian)
    (h : ∀ j, trace (A ^ (2 * j + 1)) = 0) : (-A).charpoly = A.charpoly := by
  have hs : univ.val.map (fun i => -hA.eigenvalues i) = univ.val.map hA.eigenvalues :=
    Fintype.map_neg_eq_of_sum_pow_odd fun j => by
      have := h j
      rw [hA.trace_pow_eq_sum] at this
      exact_mod_cast this
  conv_lhs => rw [hA.spectral_theorem]
  rw [← map_neg, Unitary.conjStarAlgAut_apply, charpoly_mul_comm, ← Matrix.mul_assoc,
    Unitary.coe_star_mul_self, Matrix.one_mul, diagonal_neg, charpoly_diagonal, hA.charpoly_eq,
    Finset.prod_eq_multiset_prod, Finset.prod_eq_multiset_prod]
  have := congrArg (Multiset.map fun x : ℝ => (X - C (x : 𝕜))) hs
  simp only [Multiset.map_map, Function.comp_def] at this
  simpa using congrArg Multiset.prod this

end IsHermitian

end Matrix

namespace Matrix

/-! ### The half-sum of two symmetric involutions -/

section HalfSum

open Complex in
/-- Let $\theta \in \mathbb{R}$ and $z, r_1, r_2 \in \mathbb{C}$ with $r_1 r_2 = 1$ and
$r_1 + r_2 = 4z^2 - 2$. Then, with $a = e^{i\theta}$ and $b = e^{-i\theta}$,
$$(r_1 - a)(r_1 - b)(r_2 - a)(r_2 - b) = 16 \bigl((z - \cos(\theta/2))(z +
  \cos(\theta/2))\bigr)^2;$$
this factor identity is used for `Matrix.charpoly_half_add_of_involutive`. -/
private theorem prod_sub_exp_mul_prod_sub_exp (θ : ℝ) {z r₁ r₂ : ℂ} (h12 : r₁ * r₂ = 1)
    (hs : r₁ + r₂ = 4 * z ^ 2 - 2) :
    (r₁ - exp (θ * I)) * (r₁ - exp (-θ * I)) * ((r₂ - exp (θ * I)) * (r₂ - exp (-θ * I))) =
      16 * ((z - (Real.cos (θ / 2) : ℂ)) * (z + (Real.cos (θ / 2) : ℂ))) ^ 2 := by
  obtain ⟨a, ha⟩ : ∃ a, a = exp (θ * I) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = exp (-θ * I) := ⟨_, rfl⟩
  rw [← ha, ← hb]
  have hab : a * b = 1 := by
    rw [ha, hb, ← Complex.exp_add, neg_mul, add_neg_cancel, Complex.exp_zero]
  have hc : a + b = 4 * (Real.cos (θ / 2) : ℂ) ^ 2 - 2 := by
    have h2 : (θ : ℂ) = 2 * ((θ / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [ha, hb, ← Complex.two_cos, h2, Complex.cos_two_mul, Complex.ofReal_cos]
    ring
  have hP : (r₁ - a) * (r₂ - a) = 1 - a * (4 * z ^ 2 - 2) + a ^ 2 := by
    linear_combination h12 - a * hs
  have hQ : (r₁ - b) * (r₂ - b) = 1 - b * (4 * z ^ 2 - 2) + b ^ 2 := by
    linear_combination h12 - b * hs
  calc (r₁ - a) * (r₁ - b) * ((r₂ - a) * (r₂ - b))
      = ((r₁ - a) * (r₂ - a)) * ((r₁ - b) * (r₂ - b)) := by ring
    _ = (1 - a * (4 * z ^ 2 - 2) + a ^ 2) * (1 - b * (4 * z ^ 2 - 2) + b ^ 2) := by rw [hP, hQ]
    _ = (a + b - (4 * z ^ 2 - 2)) ^ 2 := by
      linear_combination ((4 * z ^ 2 - 2) ^ 2 - (a + b) * (4 * z ^ 2 - 2) + (a * b - 1)) * hab
    _ = _ := by rw [hc]; ring

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Let $K$ be a field, let $M \in K^{n \times n}$, and let $a, b \in K^m$. If the characteristic
polynomial of $M$ is
$$p_M = \prod_{k=1}^{m} (X - a_k)(X - b_k),$$
then $M$ has order $n = 2m$. -/
theorem card_eq_of_charpoly_eq_prod {K : Type*} [Field K] {M : Matrix n n K} {m : ℕ}
    {a b : Fin m → K} (h : M.charpoly = ∏ k, (X - C (a k)) * (X - C (b k))) :
    Fintype.card n = 2 * m := by
  have h' := congrArg natDegree h
  rw [charpoly_natDegree_eq_dim, natDegree_prod_of_monic _ _ fun k _ =>
    (monic_X_sub_C _).mul (monic_X_sub_C _)] at h'
  simp only [natDegree_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _), natDegree_X_sub_C,
    sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h'
  omega

open Complex in
/-- The **spectrum of the half-sum of two symmetric involutions of trace zero**, a result of Ammar,
Gragg and Reichel. Let $A, B \in \mathbb{R}^{n \times n}$ be symmetric with $A^2 = B^2 = I$ and
$\operatorname{tr} A = \operatorname{tr} B = 0$. Let $\theta_1, \dots, \theta_m \in \mathbb{R}$,
and assume that the characteristic polynomial of $AB$, as a complex matrix, is
$$p_{AB} = \prod_{k=1}^{m} (X - e^{i\theta_k})(X - e^{-i\theta_k}).$$
Then the characteristic polynomial of $C = \tfrac{1}{2}(A + B)$ is
$$p_C = \prod_{k=1}^{m} \bigl(X - \cos(\theta_k/2)\bigr)\bigl(X + \cos(\theta_k/2)\bigr).$$
That is, if the eigenvalues of $AB$ are the $m$ pairs $e^{\pm i\theta_k}$, then the eigenvalues
of $C$ are the $m$ pairs $\pm\cos(\theta_k/2)$. This is the spectral half of Fact 2 in §12.2.10
of [golub2013matrix].

The spectrum of $C$ is symmetric about $0$, because its odd powers have trace zero
(`Matrix.trace_add_pow_odd_eq_zero`, `Matrix.IsHermitian.charpoly_neg_of_trace_pow_odd`). Hence
$p_C(z)^2 = p_C(z) p_{-C}(z) = \det(z^2 I - C^2)$. For $r_1 r_2 = 1$ and $r_1 + r_2 = 4z^2 - 2$,
the identity $4 (z^2 I - C^2) AB = -(r_1 I - AB)(r_2 I - AB)$ and $\det AB = 1$ give
$\det(z^2 I - C^2)$ from $p_{AB}(r_1)$ and $p_{AB}(r_2)$. This gives
$p_C^2 = \prod_k (X^2 - \cos^2(\theta_k/2))^2$, and since both polynomials are monic,
$p_C = \prod_k (X^2 - \cos^2(\theta_k/2))$. The complex matrix $AB$ is
`(A * B).map (algebraMap ℝ ℂ)`. -/
theorem charpoly_half_add_of_involutive {A B : Matrix n n ℝ} (hAs : A.IsSymm) (hBs : B.IsSymm)
    (hA : A * A = 1) (hB : B * B = 1) (htA : trace A = 0) (htB : trace B = 0) {m : ℕ}
    (θ : Fin m → ℝ)
    (hθ : ((A * B).map (algebraMap ℝ ℂ)).charpoly =
      ∏ k, (X - C (exp (θ k * I))) * (X - C (exp (-θ k * I)))) :
    ((1 / 2 : ℝ) • (A + B)).charpoly =
      ∏ k, (X - C (Real.cos (θ k / 2))) * (X + C (Real.cos (θ k / 2))) := by
  have hn := card_eq_of_charpoly_eq_prod hθ
  have hneg1 : ∀ M : Matrix n n ℂ, det (-M) = det M := fun M => by
    rw [det_neg, hn, pow_mul, neg_one_sq, one_pow, one_mul]
  have hsc : ∀ w : ℂ, scalar n w = w • (1 : Matrix n n ℂ) := fun w => by
    rw [scalar_apply, smul_one_eq_diagonal]
  obtain ⟨Cm, hCm⟩ : ∃ Cm : Matrix n n ℝ, Cm = (1 / 2 : ℝ) • (A + B) := ⟨_, rfl⟩
  rw [← hCm]
  have hCh : Cm.IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, hCm, transpose_smul, transpose_add,
      hAs.eq, hBs.eq]
  have hsym : (-Cm).charpoly = Cm.charpoly := hCh.charpoly_neg_of_trace_pow_odd fun j => by
    rw [hCm, smul_pow, trace_smul, trace_add_pow_odd_eq_zero hA hB htA htB, smul_zero]
  obtain ⟨p, hp⟩ : ∃ p, p = Cm.charpoly := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ[X],
      r = ∏ k, (X - C (Real.cos (θ k / 2))) * (X + C (Real.cos (θ k / 2))) := ⟨_, rfl⟩
  rw [← hp, ← hr]
  -- the complexified matrices
  obtain ⟨Ac, hAc⟩ : ∃ Ac, Ac = A.map (algebraMap ℝ ℂ) := ⟨_, rfl⟩
  obtain ⟨Bc, hBc⟩ : ∃ Bc, Bc = B.map (algebraMap ℝ ℂ) := ⟨_, rfl⟩
  have hMc : (A * B).map (algebraMap ℝ ℂ) = Ac * Bc := by rw [hAc, hBc, Matrix.map_mul]
  have hAA : Ac * Ac = 1 := by
    rw [hAc, ← Matrix.map_mul, hA, Matrix.map_one _ (map_zero _) (map_one _)]
  have hBB : Bc * Bc = 1 := by
    rw [hBc, ← Matrix.map_mul, hB, Matrix.map_one _ (map_zero _) (map_one _)]
  have hAA' : ∀ M, Ac * (Ac * M) = M := fun M => by rw [← Matrix.mul_assoc, hAA, Matrix.one_mul]
  have hCc : Cm.map (algebraMap ℝ ℂ) = (1 / 2 : ℂ) • (Ac + Bc) := by
    ext i j
    simp [hCm, hAc, hBc]
    ring
  have hCneg : (-Cm).map (algebraMap ℝ ℂ) = -((1 / 2 : ℂ) • (Ac + Bc)) := by
    rw [← hCc]
    ext i j
    simp
  have hev : ∀ w : ℂ, det (w • 1 - Ac * Bc) =
      ∏ k, (w - exp (θ k * I)) * (w - exp (-θ k * I)) := fun w => by
    have h := congrArg (eval w) hθ
    rw [eval_charpoly, eval_prod, hsc, hMc] at h
    simpa using h
  have hdet : det (Ac * Bc) = 1 := by
    have h := hev 0
    rw [zero_smul, zero_sub, hneg1] at h
    rw [h]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [zero_sub, zero_sub, neg_mul_neg, ← Complex.exp_add, neg_mul, add_neg_cancel,
      Complex.exp_zero]
  have hpt : ∀ z : ℂ, (p.map (algebraMap ℝ ℂ)).eval z ^ 2 =
      (r.map (algebraMap ℝ ℂ)).eval z ^ 2 := fun z => by
    obtain ⟨d, hd⟩ := IsAlgClosed.isSquare ((4 * z ^ 2 - 2) ^ 2 - 4)
    have h12 : (4 * z ^ 2 - 2 + d) / 2 * ((4 * z ^ 2 - 2 - d) / 2) = 1 := by
      linear_combination (1 / 4 : ℂ) * hd
    have hs : (4 * z ^ 2 - 2 + d) / 2 + (4 * z ^ 2 - 2 - d) / 2 = 4 * z ^ 2 - 2 := by ring
    generalize (4 * z ^ 2 - 2 + d) / 2 = r₁ at h12 hs
    generalize (4 * z ^ 2 - 2 - d) / 2 = r₂ at h12 hs
    -- `p_C(z)² = det (z² − C²)`
    have e1 : (p.map (algebraMap ℝ ℂ)).eval z = det (z • 1 - (1 / 2 : ℂ) • (Ac + Bc)) := by
      rw [hp, ← charpoly_map, eval_charpoly, hsc, hCc]
    have e2 : (p.map (algebraMap ℝ ℂ)).eval z = det (z • 1 + (1 / 2 : ℂ) • (Ac + Bc)) := by
      rw [hp, ← hsym, ← charpoly_map, eval_charpoly, hsc, hCneg, sub_neg_eq_add]
    have eX : (z • 1 - (1 / 2 : ℂ) • (Ac + Bc)) * (z • 1 + (1 / 2 : ℂ) • (Ac + Bc)) =
        (4 : ℂ)⁻¹ • ((4 * z ^ 2 - 2) • 1 - (Ac * Bc + Bc * Ac)) := by
      simp only [sub_mul, mul_add, add_mul, smul_mul_assoc, mul_smul_comm,
        Matrix.one_mul, Matrix.mul_one, smul_add, hAA, hBB]
      module
    -- `4 (z² − C²) AB = −(r₁ − AB)(r₂ − AB)`
    have eY : ((4 * z ^ 2 - 2) • 1 - (Ac * Bc + Bc * Ac)) * (Ac * Bc) =
        -((r₁ • 1 - Ac * Bc) * (r₂ • 1 - Ac * Bc)) := by
      have e : (r₁ • 1 - Ac * Bc) * (r₂ • 1 - Ac * Bc) =
          (r₁ * r₂) • 1 - (r₁ + r₂) • (Ac * Bc) + Ac * Bc * (Ac * Bc) := by
        simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, Matrix.one_mul,
          Matrix.mul_one, add_smul]
        module
      rw [e, h12, hs]
      simp only [sub_mul, add_mul, smul_mul_assoc, Matrix.one_mul, Matrix.mul_assoc, hAA', hBB]
      module
    have key : (4 : ℂ)⁻¹ ^ Fintype.card n * ((∏ k, (r₁ - exp (θ k * I)) * (r₁ - exp (-θ k * I))) *
        ∏ k, (r₂ - exp (θ k * I)) * (r₂ - exp (-θ k * I))) =
        (p.map (algebraMap ℝ ℂ)).eval z ^ 2 := by
      rw [← hev, ← hev, ← det_mul, ← hneg1, ← eY, det_mul, hdet, mul_one, ← det_smul, ← eX,
        det_mul, ← e1, ← e2, sq]
    rw [← key, ← prod_mul_distrib,
      Finset.prod_congr rfl fun k _ => prod_sub_exp_mul_prod_sub_exp (θ k) h12 hs, prod_mul_distrib,
      prod_const, card_univ, Fintype.card_fin, prod_pow, hr, Polynomial.map_prod, eval_prod, hn,
      pow_mul, ← mul_assoc, ← mul_pow]
    norm_num
  have hsq : p ^ 2 = r ^ 2 :=
    Polynomial.map_injective _ (RingHom.injective (algebraMap ℝ ℂ)) <| Polynomial.funext fun z => by
      simp only [Polynomial.map_pow, eval_pow, hpt]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
  · exact h
  · have h1 : p.leadingCoeff = 1 := hp ▸ charpoly_monic Cm
    have h2 : r.Monic := hr ▸ monic_prod_of_monic _ _ fun k _ =>
      (monic_X_sub_C _).mul (monic_X_add_C _)
    rw [h, leadingCoeff_neg, h2.leadingCoeff] at h1
    norm_num at h1

end HalfSum

end Matrix

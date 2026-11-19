/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Krylov.Arnoldi
import Numlib.Krylov.Hessenberg
import Numlib.Krylov.Subspace
import Numlib.Projection.Basic
import NumlibSurface.SaadSparse.Chapter06.Common

/-!
# Saad, Section 6.3: Arnoldi's method

This module formalizes Section 6.3 of [saad2003iterative]. Arnoldi's method builds, from a unit
vector $v_1$, an orthonormal basis $v_1, \dots, v_m$ of the Krylov subspace $\mathcal{K}_m(A, v_1)$,
together with the coefficients $h_{ij} = (Av_j, v_i)$ of the upper Hessenberg matrices
$\bar H_m \in \mathbb{K}^{(m+1) \times m}$ and $H_m \in \mathbb{K}^{m \times m}$. With
$V_m = [v_1, \dots, v_m]$, the basic relations are
$$A V_m = V_m H_m + w_m e_m^T = V_{m+1} \bar H_m, \qquad V_m^T A V_m = H_m.$$
The module defines Algorithm 6.1 (classical Gram–Schmidt), Algorithm 6.2 (modified Gram–Schmidt) and
Algorithm 6.3 (Householder Arnoldi), and proves Propositions 6.4–6.6, the relations (6.6)–(6.13),
the equivalence of Algorithms 6.1 and 6.2 in exact arithmetic, and the parts of Exercise P-6.1 on
Householder Arnoldi.

The proofs identify Algorithm 6.1 with the backbone Arnoldi process `Arnoldi.vec` of
`Numlib.Krylov.Arnoldi`, the Gram–Schmidt orthonormalization of the Krylov sequence
$v_1, Av_1, A^2 v_1, \dots$, and use the Hessenberg relation interface `Krylov.HessenbergRelation`
of `Numlib.Krylov.Hessenberg`. The last section translates these results to the starting vector
$v_1 = r_0 / \beta$ of `NumlibSurface.SaadSparse.Chapter06.Common`, for use by every algorithm from
Section 6.4 on.

## Main definitions

* Algorithm 6.1, `SaadSparse.Chapter06.arnoldiCGS`: the Arnoldi vectors, computed with classical
  Gram–Schmidt.
* Algorithm 6.1, `SaadSparse.Chapter06.arnoldiCoeff`: the coefficients $h_{ij} = (Av_j, v_i)$.
* Algorithm 6.1, `SaadSparse.Chapter06.arnoldiW`: the unnormalized vectors $w_j$.
* Section 6.3.1, `SaadSparse.Chapter06.NoBreakdownBefore`: Algorithm 6.1 does not stop before the
  $m$-th step.
* Section 6.3.1, `SaadSparse.Chapter06.V`, `SaadSparse.Chapter06.Hbar`, `SaadSparse.Chapter06.H`:
  the matrices $V_m$, $\bar H_m$ and $H_m$.
* Algorithm 6.2, `SaadSparse.Chapter06.arnoldiMGS` and `SaadSparse.Chapter06.arnoldiMGSCoeff`:
  Arnoldi with modified Gram–Schmidt, and its coefficients.
* Algorithm 6.3, `SaadSparse.Chapter06.householderVec` and `SaadSparse.Chapter06.householder`: the
  Householder vector (1.24) and reflector (1.23).
* Equation (6.10), `SaadSparse.Chapter06.Qhh`: the product $Q_j = P_j \cdots P_1$ of the Householder
  reflectors.
* Exercise P-6.1, `SaadSparse.Chapter06.HbarHH`: the Hessenberg matrix of Householder Arnoldi.

## Main results

* Proposition 6.4, `SaadSparse.Chapter06.proposition_6_4`: if Algorithm 6.1 does not stop before
  step $m$, then $v_1, \dots, v_m$ is an orthonormal basis of $\mathcal{K}_m$.
* Equation (6.6) and Proposition 6.5, `SaadSparse.Chapter06.equation_6_6`:
  $A V_m = V_m H_m + w_m e_m^T$.
* Equation (6.7) and Proposition 6.5, `SaadSparse.Chapter06.equation_6_7`:
  $A V_m = V_{m+1} \bar H_m$.
* Equation (6.8) and Proposition 6.5, `SaadSparse.Chapter06.equation_6_8`: $V_m^T A V_m = H_m$.
* Equation (6.9), `SaadSparse.Chapter06.equation_6_9`: $A v_j = \sum_{i=1}^{j+1} h_{ij} v_i$.
* Proposition 6.6, `SaadSparse.Chapter06.proposition_6_6`: Arnoldi's method breaks down at step $j$
  if and only if the minimal polynomial of $v_1$ has degree $j$.
* Proposition 6.6, `SaadSparse.Chapter06.proposition_6_6'`: at a breakdown at step $j$,
  $\mathcal{K}_j$ is invariant under $A$.
* Section 6.3.2, `SaadSparse.Chapter06.algorithm_6_2_eq_alg_6_1`: Algorithms 6.1 and 6.2 compute the
  same vectors and coefficients in exact arithmetic.
* Equation (6.11), `SaadSparse.Chapter06.equation_6_11`: $h_j = Q_{j+1} A v_j$.
* Equation (6.12), `SaadSparse.Chapter06.equation_6_12_zero` and
  `SaadSparse.Chapter06.equation_6_12`: $Q_{m+1} [v, Av_1, \dots, Av_m] = [h_0, h_1, \dots, h_m]$.
* Equation (6.13), `SaadSparse.Chapter06.equation_6_13`: $Q_{j}^T e_i = v_i$ for $i \le j$.
* Exercise P-6.1(d), `SaadSparse.Chapter06.hh_arnoldi_relation`: Householder Arnoldi satisfies
  $A V_m = V_{m+1} \bar H_m$.
* Exercise P-6.1(e), `SaadSparse.Chapter06.hh_orthonormal`: the Householder Arnoldi vectors are
  orthonormal.
* Exercise P-6.1(f), `SaadSparse.Chapter06.hh_eq_arnoldi_up_to_sign`: the Householder Arnoldi
  vectors are the Gram–Schmidt Arnoldi vectors up to sign.

## Implementation notes

* Indices are $0$-based, and a Lean index $j$ stands for the book's index $j + 1$. Thus
  `arnoldiCGS A v₁ j`, `arnoldiW A v₁ j`, `hhV A v j`, `hhZ A v j`, `hhW A v j`, `Qhh A v j` and
  `stdVec j` are the book's objects with index $j + 1$.
* The coefficient `arnoldiCoeff A v₁ i j` is the book's $h_{i+1,j+1}$.
* The column `hhH A v j` of (6.12) is the book's $h_j$, because the book numbers these columns from
  $0$.
* The matrices keep the book's dimensions: $V_m$ is `Matrix (Fin n) (Fin m) 𝕜`.
* Division by a vanishing norm is $0$ in Lean. This gives the book's "if $h_{j+1,j} = 0$ then Stop":
  every later vector is $0$, and the relations stay true after the breakdown.
* The definitions are polymorphic in the scalar field `𝕜` with `[RCLike 𝕜]`. The numbered results
  are stated over $\mathbb{R}$, the generality of Section 6.3 of the book, as specializations of
  lemmas for any `𝕜`. Householder Arnoldi is real throughout, as in the book.
* Algorithm 6.2 is identified with `Arnoldi.vec` through the backbone modified Gram–Schmidt
  recurrence `Arnoldi.eq_vec_of_modifiedGramSchmidt`, which Algorithm 10.5.1 of [golub2013matrix]
  also uses.

## Deviations from the source

* **Reading.** The Gram–Schmidt Arnoldi definitions pad exact breakdown with zeros and allow complex
  scalars. See `SaadSparse.Chapter06.arnoldiCGS`, `SaadSparse.Chapter06.arnoldiCGS_succ`,
  `SaadSparse.Chapter06.arnoldiMGS`, `SaadSparse.Chapter06.arnoldiMGS_succ`.
* **Reading.** The Arnoldi coefficient and residual formulas use the complex inner product when
  needed. See `SaadSparse.Chapter06.arnoldiCoeff`, `SaadSparse.Chapter06.arnoldiW`,
  `SaadSparse.Chapter06.arnoldiMGSW`, `SaadSparse.Chapter06.arnoldiMGSCoeff`,
  `SaadSparse.Chapter06.mgsW`, `SaadSparse.Chapter06.mgsW_succ`.
* **Reading.** The zero tests on the padded sequence identify indices at or past breakdown. See
  `SaadSparse.Chapter06.arnoldiCGS_eq_zero_iff`,
  `SaadSparse.Chapter06.arnoldiCoeff_succ_self_eq_zero_iff`.
* **Generalization.** The orthogonality and span formulas include complex scalars and describe the
  stabilized span. See `SaadSparse.Chapter06.inner_arnoldiCGS_eq_zero`,
  `SaadSparse.Chapter06.norm_arnoldiCGS`, `SaadSparse.Chapter06.orthonormal_arnoldiCGS`,
  `SaadSparse.Chapter06.span_arnoldiCGS`.
* **Generalization.** The Arnoldi recurrence and matrix relations hold for the totalized real or
  complex sequence. See `SaadSparse.Chapter06.arnoldiCoeff_succ_self`,
  `SaadSparse.Chapter06.arnoldiW_eq_smul`, `SaadSparse.Chapter06.arnoldiCoeff_eq_zero_of_lt`,
  `SaadSparse.Chapter06.hessenbergRelation`, `SaadSparse.Chapter06.apply_arnoldiCGS`,
  `SaadSparse.Chapter06.mul_V_eq`, `SaadSparse.Chapter06.mul_V_eq_add_vecMulVec`.
* **Generalization.** The stopping, grade and invariance conditions are available for both scalar
  fields. See `SaadSparse.Chapter06.NoBreakdownBefore`,
  `SaadSparse.Chapter06.noBreakdownBefore_iff`, `SaadSparse.Chapter06.breakdown_iff_grade_eq`,
  `SaadSparse.Chapter06.krylov_mem_invtSubmodule_of_breakdown`.
* **Reading.** The matrices $V_m$, $H_m$ and the extended Hessenberg matrix also allow padded
  prefixes. See `SaadSparse.Chapter06.V`, `SaadSparse.Chapter06.Hbar`, `SaadSparse.Chapter06.H`.
* **Generalization.** The compression identity holds entrywise even for nonunit starts and after
  breakdown. See `SaadSparse.Chapter06.conjTranspose_V_mul_mul_V`,
  `SaadSparse.Chapter06.equation_6_8`.
* **Generalization.** The real Arnoldi identities include the padded sequence after breakdown. See
  `SaadSparse.Chapter06.equation_6_9`, `SaadSparse.Chapter06.equation_6_7`,
  `SaadSparse.Chapter06.equation_6_6`.
* **Reading.** The exact equivalence of CGS and MGS includes the padded tails. See
  `SaadSparse.Chapter06.arnoldiMGS_eq_arnoldiCGS`,
  `SaadSparse.Chapter06.arnoldiMGSCoeff_eq_arnoldiCoeff`,
  `SaadSparse.Chapter06.algorithm_6_2_eq_alg_6_1`.
* **Reading.** The Householder sign is chosen positive at a zero leading coordinate. See
  `SaadSparse.Chapter06.householderBeta`.
* **Correction.** The Householder direction uses the corrected pivot-coordinate entry. See
  `SaadSparse.Chapter06.householderDir_coord`, `SaadSparse.Chapter06.householderDir_eq`.
* **Reading.** Householder normalization and the reflector identities cover zero tails. See
  `SaadSparse.Chapter06.householderVec`, `SaadSparse.Chapter06.norm_householderVec`,
  `SaadSparse.Chapter06.householder_householder`, `SaadSparse.Chapter06.norm_householder_apply`,
  `SaadSparse.Chapter06.householder_householderVec_apply`,
  `SaadSparse.Chapter06.householder_householderVec_coord`.
* **Generalization.** The elementary Householder map is defined even when its input direction is
  zero. See `SaadSparse.Chapter06.householder`.
* **Reading.** The Householder process uses identity reflectors on zero tails and can complete the
  basis. See `SaadSparse.Chapter06.hhZ`, `SaadSparse.Chapter06.hhW`, `SaadSparse.Chapter06.Qhh`,
  `SaadSparse.Chapter06.QhhT`, `SaadSparse.Chapter06.hhV`, `SaadSparse.Chapter06.hhH`,
  `SaadSparse.Chapter06.hhZ_succ`, `SaadSparse.Chapter06.norm_hhW`.
* **Correction.** The Householder factorization uses $Q_{m+1}$ for all $m+1$ columns. See
  `SaadSparse.Chapter06.equation_6_12_zero`, `SaadSparse.Chapter06.equation_6_12`.
* **Correction.** The Householder matrix relation uses consistent coordinate spaces in the reading
  of P-6.1(d). See `SaadSparse.Chapter06.hh_hessenbergRelation`,
  `SaadSparse.Chapter06.hh_arnoldi_relation`.
* **Reading.** The Householder and Gram–Schmidt basis comparison is restricted to the prefix within
  the grade. See `SaadSparse.Chapter06.span_hhV_eq`,
  `SaadSparse.Chapter06.hh_eq_arnoldi_up_to_sign`.
* **Reading.** Lucky-breakdown exactness explicitly needs the test space to separate trial vectors.
  See `SaadSparse.Chapter06.lucky_breakdown`.
* **Equation (1.25)** (typo). The source prints the $k$-th entry of the Householder direction as
  $\beta + x_{ii}$. It is $\beta + x_{kk}$, as Algorithm 1.3 needs. See
  `SaadSparse.Chapter06.householderDir`.
-/

open scoped Matrix

namespace SaadSparse.Chapter06

section General

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-! ### Coordinate helpers -/

private theorem sum_coord {ι : Type*} (s : Finset ι) (f : ι → 𝔼) (i : Fin n) :
    (∑ k ∈ s, f k) i = ∑ k ∈ s, f k i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, PiLp.add_apply, ih]

private theorem op_coord (B : Matrix (Fin n) (Fin n) 𝕜) (x : 𝔼) (i : Fin n) :
    op B x i = ∑ k, B i k * x k := rfl

private theorem range_fin_eq_image_Iio {α : Type*} (f : ℕ → α) (m : ℕ) :
    Set.range (fun i : Fin m => f (i : ℕ)) = f '' Set.Iio m := by
  ext x
  simp only [Set.mem_range, Set.mem_image, Set.mem_Iio, Fin.exists_iff]
  tauto

/-! ### Algorithm 6.1: Arnoldi with classical Gram–Schmidt -/

/-- **Algorithm 6.1** of [saad2003iterative] (Arnoldi, classical Gram–Schmidt). Start from $v_1$.
For $j = 1, 2, \dots$, compute $h_{ij} = (Av_j, v_i)$ for $i = 1, \dots, j$, then
$$w_j = A v_j - \sum_{i=1}^{j} h_{ij} v_i, \qquad v_{j+1} = w_j / \|w_j\|_2.$$

The index is $0$-based: `arnoldiCGS A v₁ j` is $v_{j+1}$. The book's "if $h_{j+1,j} = 0$ then
Stop" is Lean's convention $w / 0 = 0$: all later vectors are $0$.

**Reading.** Lean gives exact infinite sequences. Division by zero returns the zero vector, so the
sequence is padded with zeros after the point where the printed algorithm stops. The definitions
also allow complex scalars and a nonunit input; the Arnoldi properties use a unit starting vector.
-/
noncomputable def arnoldiCGS (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ : 𝔼) : ℕ → 𝔼
  | 0 => v₁
  | j + 1 =>
    let v : Fin (j + 1) → 𝔼 := fun i => arnoldiCGS A v₁ (i : ℕ)
    let Av := op A (v (Fin.last j))
    let w := Av - ∑ i : Fin (j + 1), inner 𝕜 (v i) Av • v i
    ((‖w‖ : 𝕜)⁻¹) • w
  termination_by j => j
  decreasing_by exact i.isLt

/-- **Algorithm 6.1** of [saad2003iterative], line 3. The **Arnoldi coefficients**
$h_{ij} = (Av_j, v_i)$.

The indices are $0$-based: `arnoldiCoeff A v₁ i j` is $h_{i+1,j+1}$. The definition gives a
value for all $i$, $j$; it is the inner product also for $i > j + 1$.

**Reading.** The recurrences also act over complex scalars, with conjugate-linear first argument in
Lean's inner-product convention. In the unit-start case they give the source's coefficients through
breakdown, with the totalized extension thereafter.
-/
noncomputable def arnoldiCoeff (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ : 𝔼) (i j : ℕ) : 𝕜 :=
  inner 𝕜 (arnoldiCGS A v₁ i) (op A (arnoldiCGS A v₁ j))

/-- **Algorithm 6.1** of [saad2003iterative], line 4. The **unnormalized vector**
$w_j = Av_j - \sum_{i=1}^{j} h_{ij} v_i$.

The index is $0$-based: `arnoldiW A v₁ j` is $w_{j+1}$.

**Reading.** The recurrences also act over complex scalars, with conjugate-linear first argument in
Lean's inner-product convention. In the unit-start case they give the source's coefficients through
breakdown, with the totalized extension thereafter.
-/
noncomputable def arnoldiW (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ : 𝔼) (j : ℕ) : 𝔼 :=
  op A (arnoldiCGS A v₁ j) -
    ∑ i ∈ Finset.range (j + 1), arnoldiCoeff A v₁ i j • arnoldiCGS A v₁ i

variable (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ : EuclideanSpace 𝕜 (Fin n))

/-- The first Arnoldi vector is the starting vector $v_1$. -/
@[simp]
theorem arnoldiCGS_zero : arnoldiCGS A v₁ 0 = v₁ := by rw [arnoldiCGS]

/-- **Algorithm 6.1** of [saad2003iterative], line 7. Each next Arnoldi vector is the normalized
vector $v_{j+1} = w_j / \|w_j\|$, which is $0$ when $w_j = 0$.

**Reading.** Lean gives exact infinite sequences. Division by zero returns the zero vector, so the
sequence is padded with zeros after the point where the printed algorithm stops. The definitions
also allow complex scalars and a nonunit input; the Arnoldi properties use a unit starting vector.
-/
theorem arnoldiCGS_succ (j : ℕ) :
    arnoldiCGS A v₁ (j + 1) = ((‖arnoldiW A v₁ j‖ : 𝕜)⁻¹) • arnoldiW A v₁ j := by
  rw [arnoldiCGS, arnoldiW]
  simp only [arnoldiCoeff, Fin.val_last]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => inner 𝕜 (arnoldiCGS A v₁ i) (op A (arnoldiCGS A v₁ j)) • arnoldiCGS A v₁ i) (j + 1)]

/-! ### Identification with the backbone Arnoldi process -/

private theorem arnoldiW_eq_of_forall {r : EuclideanSpace 𝕜 (Fin n)} {j : ℕ}
    (ih : ∀ i ≤ j, arnoldiCGS A v₁ i = Arnoldi.vec (op A) r i) :
    arnoldiW A v₁ j = Arnoldi.w (op A) r j := by
  have hsum : ∑ i ∈ Finset.range (j + 1), arnoldiCoeff A v₁ i j • arnoldiCGS A v₁ i
      = ∑ i ∈ Finset.range (j + 1),
        Arnoldi.coeff (op A) r i j • Arnoldi.vec (op A) r i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [arnoldiCoeff, ih i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)), ih j le_rfl]
    rfl
  rw [arnoldiW, Arnoldi.w, hsum, ih j le_rfl]

/-- The **bridge to the backbone**. Let $r$ be a vector whose first backbone Arnoldi vector
`Arnoldi.vec (op A) r 0` is $v_1$. Then Algorithm 6.1 started at $v_1$ computes the backbone
Arnoldi vectors of $r$: `arnoldiCGS A v₁ j = Arnoldi.vec (op A) r j` for every $j$.

The two instances are $r = v_1$ for a unit starting vector
(`SaadSparse.Chapter06.arnoldiCGS_eq_vec`), and $r = r_0$ with $v_1 = r_0 / \|r_0\|$ for the
residual start of FOM and GMRES (`SaadSparse.Chapter06.arnoldiCGS_normalize`). -/
theorem arnoldiCGS_eq_vec_of_vec_zero {r : EuclideanSpace 𝕜 (Fin n)}
    (h0 : Arnoldi.vec (op A) r 0 = v₁) (j : ℕ) : arnoldiCGS A v₁ j = Arnoldi.vec (op A) r j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [arnoldiCGS_zero, h0]
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      rw [arnoldiCGS_succ, Arnoldi.vec_succ_eq,
        arnoldiW_eq_of_forall A v₁ fun i hi => ih i (Nat.lt_succ_of_le hi)]

/-- If $\|v_1\| = 1$, then Algorithm 6.1 computes the backbone Arnoldi vectors `Arnoldi.vec` of
$v_1$: the Gram–Schmidt orthonormalization of the Krylov sequence $v_1, Av_1, A^2 v_1, \dots$. -/
theorem arnoldiCGS_eq_vec (hv : ‖v₁‖ = 1) (j : ℕ) :
    arnoldiCGS A v₁ j = Arnoldi.vec (op A) v₁ j := by
  refine arnoldiCGS_eq_vec_of_vec_zero A v₁ ?_ j
  have hv0 : v₁ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hv
    exact zero_ne_one hv
  rw [Arnoldi.vec_zero (op A) v₁ hv0, hv]
  simp

/-- If $\|v_1\| = 1$, then the coefficients $h_{ij}$ of Algorithm 6.1 are the backbone Arnoldi
coefficients `Arnoldi.coeff` of $v_1$. -/
theorem arnoldiCoeff_eq (hv : ‖v₁‖ = 1) (i j : ℕ) :
    arnoldiCoeff A v₁ i j = Arnoldi.coeff (op A) v₁ i j := by
  rw [arnoldiCoeff, arnoldiCGS_eq_vec A v₁ hv, arnoldiCGS_eq_vec A v₁ hv]
  rfl

/-- If $\|v_1\| = 1$, then the vectors $w_j$ of Algorithm 6.1 are the backbone vectors `Arnoldi.w`
of $v_1$. -/
theorem arnoldiW_eq (hv : ‖v₁‖ = 1) (j : ℕ) : arnoldiW A v₁ j = Arnoldi.w (op A) v₁ j :=
  arnoldiW_eq_of_forall A v₁ fun i _ => arnoldiCGS_eq_vec A v₁ hv i

/-- If $\|v_1\| = 1$, then the Arnoldi vectors are pairwise orthogonal: $(v_j, v_i) = 0$ for
$i \neq j$. This holds also after the breakdown, where the vectors are $0$.

**Generalization.** The orthogonality and span formulas also allow complex scalars. Norm one is
asserted before breakdown. The span remains the stabilized Krylov space even after zero padding.
-/
theorem inner_arnoldiCGS_eq_zero (hv : ‖v₁‖ = 1) {i j : ℕ} (h : i ≠ j) :
    inner 𝕜 (arnoldiCGS A v₁ i) (arnoldiCGS A v₁ j) = 0 := by
  rw [arnoldiCGS_eq_vec A v₁ hv, arnoldiCGS_eq_vec A v₁ hv]
  exact Arnoldi.inner_vec_eq_zero _ _ h

/-- **Breakdown.** Let $\|v_1\| = 1$ and let $\mu$ be the grade of $v_1$. Then the Arnoldi vector
$v_k$ is $0$ if and only if $k > \mu$. In Lean, `arnoldiCGS A v₁ j = 0` if and only if
$\mu \le j$.

**Reading.** The padded recurrence has zeros at and after the first breakdown. The source stops at
the first zero subdiagonal; an equality to zero at an arbitrary index of the continued sequence only
bounds the grade above.
-/
theorem arnoldiCGS_eq_zero_iff (hv : ‖v₁‖ = 1) (j : ℕ) :
    arnoldiCGS A v₁ j = 0 ↔ grade A v₁ ≤ j := by
  rw [arnoldiCGS_eq_vec A v₁ hv, Arnoldi.vec_eq_zero_iff, grade_eq]

/-- Let $\|v_1\| = 1$ and let $\mu$ be the grade of $v_1$. Then $\|v_k\| = 1$ for $k \le \mu$.

**Generalization.** The orthogonality and span formulas also allow complex scalars. Norm one is
asserted before breakdown. The span remains the stabilized Krylov space even after zero padding.
-/
theorem norm_arnoldiCGS (hv : ‖v₁‖ = 1) {j : ℕ} (h : j < grade A v₁) :
    ‖arnoldiCGS A v₁ j‖ = 1 := by
  rw [arnoldiCGS_eq_vec A v₁ hv]
  exact Arnoldi.norm_vec_eq_one_of_lt_grade _ _ (by rwa [← grade_eq])

/-- **Algorithm 6.1** of [saad2003iterative], line 5. If $\|v_1\| = 1$, then $h_{j+1,j} = \|w_j\|_2$
for every $j$.

**Generalization.** The recurrence and matrix equations hold for the real or complex totalized
sequence. They remain valid when a zero vector is used for the unavailable next basis vector.
-/
theorem arnoldiCoeff_succ_self (hv : ‖v₁‖ = 1) (j : ℕ) :
    arnoldiCoeff A v₁ (j + 1) j = (‖arnoldiW A v₁ j‖ : 𝕜) := by
  rw [arnoldiCoeff_eq A v₁ hv, arnoldiW_eq A v₁ hv, Arnoldi.coeff_succ_self]

/-- If $\|v_1\| = 1$, then $w_j = h_{j+1,j} v_{j+1}$ for every $j$.

**Generalization.** The recurrence and matrix equations hold for the real or complex totalized
sequence. They remain valid when a zero vector is used for the unavailable next basis vector.
-/
theorem arnoldiW_eq_smul (hv : ‖v₁‖ = 1) (j : ℕ) :
    arnoldiW A v₁ j = arnoldiCoeff A v₁ (j + 1) j • arnoldiCGS A v₁ (j + 1) := by
  rw [arnoldiCoeff_succ_self A v₁ hv, arnoldiCGS_succ, smul_smul]
  rcases eq_or_ne (arnoldiW A v₁ j) 0 with h | h
  · rw [h, smul_zero]
  · rw [mul_inv_cancel₀ (by simpa using norm_ne_zero_iff.2 h), one_smul]

/-- **Hessenberg structure.** If $\|v_1\| = 1$, then $h_{ij} = 0$ for $i > j + 1$.

**Generalization.** The recurrence and matrix equations hold for the real or complex totalized
sequence. They remain valid when a zero vector is used for the unavailable next basis vector.
-/
theorem arnoldiCoeff_eq_zero_of_lt (hv : ‖v₁‖ = 1) {i j : ℕ} (h : j + 1 < i) :
    arnoldiCoeff A v₁ i j = 0 := by
  rw [arnoldiCoeff_eq A v₁ hv]
  exact Arnoldi.coeff_eq_zero_of_lt (op A) v₁ h

/-- If $\|v_1\| = 1$, then the Arnoldi vectors and coefficients satisfy the backbone Hessenberg
relation `Krylov.HessenbergRelation`: $A v_j = \sum_{i=1}^{j+1} h_{ij} v_i$ for every $j$, and
$h_{ij} = 0$ for $i > j + 1$. This is the interface that the FOM, GMRES and Givens rotation
results use.

**Generalization.** The recurrence and matrix equations hold for the real or complex totalized
sequence. They remain valid when a zero vector is used for the unavailable next basis vector.
-/
theorem hessenbergRelation (hv : ‖v₁‖ = 1) :
    Krylov.HessenbergRelation (op A) (arnoldiCGS A v₁) (arnoldiCoeff A v₁) := by
  have hvec : arnoldiCGS A v₁ = Arnoldi.vec (op A) v₁ := funext (arnoldiCGS_eq_vec A v₁ hv)
  have hc : arnoldiCoeff A v₁ = Arnoldi.coeff (op A) v₁ := by
    funext i j
    exact arnoldiCoeff_eq A v₁ hv i j
  rw [hvec, hc]
  exact Arnoldi.hessenbergRelation (op A) v₁

/-! ### Breakdown -/

/-- **Section 6.3.1** of [saad2003iterative]. Algorithm 6.1 **does not stop before the $m$-th step**
if $h_{j+1,j} \neq 0$ for $j = 1, \dots, m - 1$.

In $0$-based indices the condition is `arnoldiCoeff A v₁ (j + 1) j ≠ 0` for $j + 1 < m$.

**Generalization.** Lean formulates the stopping test and grade criterion over real or complex
scalars. The invariance theorem also permits every index at or above the grade.
-/
def NoBreakdownBefore (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ : 𝔼) (m : ℕ) : Prop :=
  ∀ j, j + 1 < m → arnoldiCoeff A v₁ (j + 1) j ≠ 0

/-- Let $\|v_1\| = 1$ and let $\mu$ be the grade of $v_1$. Then Algorithm 6.1 stops at step $j$,
that is $h_{j+1,j} = 0$, if and only if $\mu \le j$. In Lean, `arnoldiCoeff A v₁ (j + 1) j = 0`
if and only if $\mu \le j + 1$.

**Reading.** The padded recurrence has zeros at and after the first breakdown. The source stops at
the first zero subdiagonal; an equality to zero at an arbitrary index of the continued sequence only
bounds the grade above.
-/
theorem arnoldiCoeff_succ_self_eq_zero_iff (hv : ‖v₁‖ = 1) (j : ℕ) :
    arnoldiCoeff A v₁ (j + 1) j = 0 ↔ grade A v₁ ≤ j + 1 := by
  rw [arnoldiCoeff_eq A v₁ hv, Arnoldi.coeff_succ_self_eq_zero_iff, grade_eq]

/-- A unit vector $v_1$ has positive grade, so Algorithm 6.1 takes at least one step. -/
theorem grade_pos (hv : ‖v₁‖ = 1) : 0 < grade A v₁ := by
  rw [grade_eq]
  exact Krylov.grade_pos_of_ne_zero _ _ (by rintro rfl; simp at hv)

/-- Let $\|v_1\| = 1$ and let $\mu$ be the grade of $v_1$. Then Algorithm 6.1 does not stop before
the $m$-th step if and only if $m \le \mu$.

**Generalization.** Lean formulates the stopping test and grade criterion over real or complex
scalars. The invariance theorem also permits every index at or above the grade.
-/
theorem noBreakdownBefore_iff (hv : ‖v₁‖ = 1) (m : ℕ) :
    NoBreakdownBefore A v₁ m ↔ m ≤ grade A v₁ := by
  constructor
  · intro h
    by_contra hc
    have hpos := grade_pos A v₁ hv
    obtain ⟨k, hk⟩ : ∃ k, grade A v₁ = k + 1 := ⟨grade A v₁ - 1, by omega⟩
    exact h k (by omega) ((arnoldiCoeff_succ_self_eq_zero_iff A v₁ hv k).2 (by omega))
  · intro h j hj hz
    exact absurd ((arnoldiCoeff_succ_self_eq_zero_iff A v₁ hv j).1 hz) (by omega)

/-! ### The matrices $V_m$, $\bar H_m$ and $H_m$ of Section 6.3.1 -/

/-- The $n \times m$ matrix whose $j$-th column is $u_j$, for a $0$-based sequence $u_0, u_1, \dots$
of vectors. This is the shape of the book's $V_m$ for the Arnoldi, incomplete orthogonalization
and Householder Arnoldi vectors. -/
noncomputable def colMatrix (u : ℕ → 𝔼) (m : ℕ) : Matrix (Fin n) (Fin m) 𝕜 :=
  Matrix.of fun i j => u (j : ℕ) i

/-- **Section 6.3.1** of [saad2003iterative]. The $n \times m$ matrix $V_m = [v_1, \dots, v_m]$
whose columns are the Arnoldi vectors.

**Reading.** The matrices can be formed at any requested size for the real or complex recurrence. At
sizes beyond breakdown they use the padded vectors and coefficients. The source forms these matrices
from the basis that was actually generated.
-/
noncomputable def V (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ : 𝔼) (m : ℕ) : Matrix (Fin n) (Fin m) 𝕜 :=
  colMatrix (arnoldiCGS A v₁) m

/-- **Section 6.3.1** of [saad2003iterative]. The $(m+1) \times m$ upper Hessenberg matrix
$\bar H_m$ whose $(i, j)$ entry is the Arnoldi coefficient $h_{ij}$.

All entries are the inner products $h_{ij} = (Av_j, v_i)$; those with $i > j + 1$ vanish for a
unit $v_1$ (`SaadSparse.Chapter06.arnoldiCoeff_eq_zero_of_lt`).

**Reading.** The matrices can be formed at any requested size for the real or complex recurrence. At
sizes beyond breakdown they use the padded vectors and coefficients. The source forms these matrices
from the basis that was actually generated.
-/
noncomputable def Hbar (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ : 𝔼) (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin m) 𝕜 :=
  Matrix.of fun i j => arnoldiCoeff A v₁ i j

/-- **Section 6.3.1** of [saad2003iterative]. The $m \times m$ matrix $H_m$ obtained from $\bar H_m$
by deleting its last row.

**Reading.** The matrices can be formed at any requested size for the real or complex recurrence. At
sizes beyond breakdown they use the padded vectors and coefficients. The source forms these matrices
from the basis that was actually generated.
-/
noncomputable def H (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ : 𝔼) (m : ℕ) : Matrix (Fin m) (Fin m) 𝕜 :=
  Matrix.of fun i j => arnoldiCoeff A v₁ i j

/-- The $(i, j)$ entry of $V_m$ is the $i$-th entry of the Arnoldi vector $v_j$. -/
@[simp]
theorem V_apply {m : ℕ} (i : Fin n) (j : Fin m) : V A v₁ m i j = arnoldiCGS A v₁ (j : ℕ) i := rfl

/-- The $(i, j)$ entry of $\bar H_m$ is $h_{ij}$. -/
@[simp]
theorem Hbar_apply {m : ℕ} (i : Fin (m + 1)) (j : Fin m) :
    Hbar A v₁ m i j = arnoldiCoeff A v₁ i j := rfl

/-- The $(i, j)$ entry of $H_m$ is $h_{ij}$. -/
@[simp]
theorem H_apply {m : ℕ} (i j : Fin m) : H A v₁ m i j = arnoldiCoeff A v₁ i j := rfl

/-- The matrix $\bar H_m$ is the backbone Hessenberg matrix `Krylov.hessenbergOf` of the Arnoldi
coefficients. -/
theorem Hbar_eq_hessenbergOf (m : ℕ) :
    Hbar A v₁ m = Krylov.hessenbergOf (arnoldiCoeff A v₁) m := rfl

/-- The matrix $H_m$ is the backbone square Hessenberg matrix `Krylov.hessenbergSqOf` of the Arnoldi
coefficients. -/
theorem H_eq_hessenbergSqOf (m : ℕ) :
    H A v₁ m = Krylov.hessenbergSqOf (arnoldiCoeff A v₁) m := rfl

/-- If $\|v_1\| = 1$, then $\bar H_m$ is the backbone Arnoldi Hessenberg matrix `Arnoldi.hessenberg`
of $v_1$. -/
theorem Hbar_eq (hv : ‖v₁‖ = 1) (m : ℕ) : Hbar A v₁ m = Arnoldi.hessenberg (op A) v₁ m := by
  ext i j
  rw [Hbar_apply, arnoldiCoeff_eq A v₁ hv]
  rfl

/-- If $\|v_1\| = 1$, then $H_m$ is the backbone square Arnoldi Hessenberg matrix
`Arnoldi.hessenbergSq` of $v_1$. -/
theorem H_eq (hv : ‖v₁‖ = 1) (m : ℕ) : H A v₁ m = Arnoldi.hessenbergSq (op A) v₁ m := by
  ext i j
  rw [H_apply, arnoldiCoeff_eq A v₁ hv]
  rfl

/-- For a $0$-based sequence $u_0, u_1, \dots$ and $y \in \mathbb{K}^m$, the matrix with columns
$u_0, \dots, u_{m-1}$ maps $y$ to $\sum_{j} y_j u_j$. -/
theorem toEuclideanLin_colMatrix_apply (u : ℕ → 𝔼) {m : ℕ} (y : Fin m → 𝕜) :
    Matrix.toEuclideanLin (colMatrix u m) (WithLp.toLp 2 y) = ∑ j, y j • u (j : ℕ) := by
  rw [Matrix.toEuclideanLin_apply_eq_sum]
  exact Finset.sum_congr rfl fun j _ => rfl

/-- For $y \in \mathbb{K}^m$, $V_m y = \sum_{j=1}^{m} y_j v_j$. This is the book's $V_m y$ in the
expansion form that the backbone uses. -/
theorem toEuclideanLin_V_apply {m : ℕ} (y : Fin m → 𝕜) :
    Matrix.toEuclideanLin (V A v₁ m) (WithLp.toLp 2 y) = ∑ j, y j • arnoldiCGS A v₁ (j : ℕ) :=
  toEuclideanLin_colMatrix_apply _ y

/-!
### Starting from an unnormalized vector

FOM and GMRES run Algorithm 6.1 on $v_1 = r_0 / \|r_0\|$, while the backbone indexes the Arnoldi
data by the residual $r_0$ itself. These lemmas translate between the two.
-/

/-- For a nonzero vector $r$, Algorithm 6.1 started at $r / \|r\|$ computes the backbone Arnoldi
vectors `Arnoldi.vec` of $r$. -/
theorem arnoldiCGS_normalize {r : EuclideanSpace 𝕜 (Fin n)} (hr : r ≠ 0) (j : ℕ) :
    arnoldiCGS A ((‖r‖⁻¹ : 𝕜) • r) j = Arnoldi.vec (op A) r j :=
  arnoldiCGS_eq_vec_of_vec_zero A _ (Arnoldi.vec_zero (op A) r hr) j

/-- For a nonzero vector $r$, the coefficients $h_{ij}$ of Algorithm 6.1 started at $r / \|r\|$ are
the backbone Arnoldi coefficients `Arnoldi.coeff` of $r$. -/
theorem arnoldiCoeff_normalize {r : EuclideanSpace 𝕜 (Fin n)} (hr : r ≠ 0) (i j : ℕ) :
    arnoldiCoeff A ((‖r‖⁻¹ : 𝕜) • r) i j = Arnoldi.coeff (op A) r i j := by
  rw [arnoldiCoeff, arnoldiCGS_normalize A hr, arnoldiCGS_normalize A hr]
  rfl

/-- For a nonzero vector $r$, the matrix $H_m$ of Algorithm 6.1 started at $r / \|r\|$ is the
backbone matrix `Arnoldi.hessenbergSq` of $r$. -/
theorem H_normalize {r : EuclideanSpace 𝕜 (Fin n)} (hr : r ≠ 0) (m : ℕ) :
    H A ((‖r‖⁻¹ : 𝕜) • r) m = Arnoldi.hessenbergSq (op A) r m := by
  ext i j
  rw [H_apply, arnoldiCoeff_normalize A hr]
  rfl

/-- For a nonzero vector $r$, the matrix $\bar H_m$ of Algorithm 6.1 started at $r / \|r\|$ is the
backbone matrix `Arnoldi.hessenberg` of $r$. -/
theorem Hbar_normalize {r : EuclideanSpace 𝕜 (Fin n)} (hr : r ≠ 0) (m : ℕ) :
    Hbar A ((‖r‖⁻¹ : 𝕜) • r) m = Arnoldi.hessenberg (op A) r m := by
  ext i j
  rw [Hbar_apply, arnoldiCoeff_normalize A hr]
  rfl

/-! ### Proposition 6.4 -/

/-- Let $\|v_1\| = 1$, let $\mu$ be the grade of $v_1$, and let $m \le \mu$. Then the Arnoldi
vectors $v_1, \dots, v_m$ are orthonormal. This is the first half of Proposition 6.4 of
[saad2003iterative].

**Generalization.** The orthogonality and span formulas also allow complex scalars. Norm one is
asserted before breakdown. The span remains the stabilized Krylov space even after zero padding.
-/
theorem orthonormal_arnoldiCGS (hv : ‖v₁‖ = 1) {m : ℕ} (hm : m ≤ grade A v₁) :
    Orthonormal 𝕜 (fun i : Fin m => arnoldiCGS A v₁ (i : ℕ)) := by
  have hg : m ≤ Krylov.grade (op A) v₁ := by rwa [← grade_eq]
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · dsimp only
    rw [arnoldiCGS_eq_vec A v₁ hv]
    exact Arnoldi.norm_vec_eq_one_of_lt_grade _ _ (lt_of_lt_of_le i.2 hg)
  · exact inner_arnoldiCGS_eq_zero A v₁ hv fun h => hij (Fin.val_injective h)

/-- Let $\|v_1\| = 1$. Then for every $m$ the Arnoldi vectors $v_1, \dots, v_m$ span the Krylov
subspace $\mathcal{K}_m(A, v_1)$. This is the second half of Proposition 6.4 of
[saad2003iterative].

No bound on $m$ is needed: after the grade of $v_1$, the later vectors are $0$ and the Krylov
subspaces stop growing.

**Generalization.** The orthogonality and span formulas also allow complex scalars. Norm one is
asserted before breakdown. The span remains the stabilized Krylov space even after zero padding.
-/
theorem span_arnoldiCGS (hv : ‖v₁‖ = 1) (m : ℕ) :
    Submodule.span 𝕜 (Set.range fun i : Fin m => arnoldiCGS A v₁ (i : ℕ)) = krylov A v₁ m := by
  have hfun : (fun i : Fin m => arnoldiCGS A v₁ (i : ℕ))
      = fun i : Fin m => Arnoldi.vec (op A) v₁ (i : ℕ) :=
    funext fun i => arnoldiCGS_eq_vec A v₁ hv i
  rw [krylov_eq, hfun, range_fin_eq_image_Iio, Arnoldi.span_vec]

/-! ### (6.6)–(6.9) and Proposition 6.5 -/

/-- **Equation (6.9)** of [saad2003iterative], over $\mathbb{R}$ or $\mathbb{C}$. If $\|v_1\| = 1$,
then for every $j$,
$$A v_j = \sum_{i=1}^{j+1} h_{ij} v_i.$$

**Generalization.** The recurrence and matrix equations hold for the real or complex totalized
sequence. They remain valid when a zero vector is used for the unavailable next basis vector.
-/
theorem apply_arnoldiCGS (hv : ‖v₁‖ = 1) (j : ℕ) :
    op A (arnoldiCGS A v₁ j)
      = ∑ i ∈ Finset.range (j + 2), arnoldiCoeff A v₁ i j • arnoldiCGS A v₁ i :=
  (hessenbergRelation A v₁ hv).apply_eq j

private theorem equation_6_9_range (hv : ‖v₁‖ = 1) {j N : ℕ} (h : j + 2 ≤ N) :
    op A (arnoldiCGS A v₁ j)
      = ∑ i ∈ Finset.range N, arnoldiCoeff A v₁ i j • arnoldiCGS A v₁ i := by
  simp only [arnoldiCGS_eq_vec A v₁ hv, arnoldiCoeff_eq A v₁ hv]
  exact Arnoldi.apply_vec_of_le (op A) v₁ h

/-- For a matrix $B$ and a $0$-based sequence $u_0, u_1, \dots$, the $(i, j)$ entry of $B U_m$ is
the $i$-th entry of $B u_j$, where $U_m$ is the matrix with columns $u_0, \dots, u_{m-1}$. -/
theorem mul_colMatrix_apply (B : Matrix (Fin n) (Fin n) 𝕜) (u : ℕ → 𝔼) {m : ℕ} (i : Fin n)
    (j : Fin m) : (B * colMatrix u m) i j = op B (u (j : ℕ)) i := by
  rw [Matrix.mul_apply, op_coord]
  rfl

private theorem mul_V_apply {m : ℕ} (i : Fin n) (j : Fin m) :
    (A * V A v₁ m) i j = op A (arnoldiCGS A v₁ (j : ℕ)) i :=
  mul_colMatrix_apply A _ i j

/-- The Hessenberg relation in matrix form. Let $u_0, u_1, \dots$ and coefficients $h_{ij}$ satisfy
the Hessenberg relation `Krylov.HessenbergRelation` for $A$. Then $A U_m = U_{m+1} \bar H_m$,
where $U_m$ is the matrix with columns $u_0, \dots, u_{m-1}$ and $\bar H_m$ is the
$(m+1) \times m$ matrix of the $h_{ij}$.

This gives (6.7) for Arnoldi, for incomplete orthogonalization and for Householder Arnoldi. -/
theorem mul_colMatrix_eq {u : ℕ → 𝔼} {h : ℕ → ℕ → 𝕜}
    (hr : Krylov.HessenbergRelation (op A) u h) (m : ℕ) :
    A * colMatrix u m = colMatrix u (m + 1) * Krylov.hessenbergOf h m := by
  have hrange : ∀ j : ℕ, j + 2 ≤ m + 1 →
      op A (u j) = ∑ i ∈ Finset.range (m + 1), h i j • u i := by
    intro j hN
    rw [hr.apply_eq j]
    refine Finset.sum_subset (by simpa using hN) fun i _ hi => ?_
    rw [Finset.mem_range, not_lt] at hi
    rw [hr.eq_zero_of_lt i j (by omega), zero_smul]
  ext i j
  rw [mul_colMatrix_apply, hrange (j : ℕ) (by omega), sum_coord, Matrix.mul_apply,
    ← Fin.sum_univ_eq_sum_range (fun l => (h l (j : ℕ) • u l) i) (m + 1)]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

/-- **Equation (6.7)** of [saad2003iterative], over $\mathbb{R}$ or $\mathbb{C}$. If $\|v_1\| = 1$,
then $A V_m = V_{m+1} \bar H_m$ for every $m$.

**Generalization.** The recurrence and matrix equations hold for the real or complex totalized
sequence. They remain valid when a zero vector is used for the unavailable next basis vector.
-/
theorem mul_V_eq (hv : ‖v₁‖ = 1) (m : ℕ) : A * V A v₁ m = V A v₁ (m + 1) * Hbar A v₁ m :=
  mul_colMatrix_eq A (hessenbergRelation A v₁ hv) m

/-- **Equation (6.6)** of [saad2003iterative], over $\mathbb{R}$ or $\mathbb{C}$. If $\|v_1\| = 1$,
then for every $m \ge 1$,
$$A V_m = V_m H_m + w_m e_m^T.$$

The Lean statement is for $m + 1$ steps, so that $w_{m+1}$ is `arnoldiW A v₁ m`, the last vector
computed; $e_m^T$ is the row vector `Pi.single (Fin.last m) 1`.

**Generalization.** The recurrence and matrix equations hold for the real or complex totalized
sequence. They remain valid when a zero vector is used for the unavailable next basis vector.
-/
theorem mul_V_eq_add_vecMulVec (hv : ‖v₁‖ = 1) (m : ℕ) :
    A * V A v₁ (m + 1) = V A v₁ (m + 1) * H A v₁ (m + 1) +
      Matrix.vecMulVec (WithLp.ofLp (arnoldiW A v₁ m)) (Pi.single (Fin.last m) 1) := by
  have hlast : ∀ j : Fin (m + 1),
      arnoldiCoeff A v₁ (m + 1) (j : ℕ) • arnoldiCGS A v₁ (m + 1)
        = (Pi.single (M := fun _ : Fin (m + 1) => 𝕜) (Fin.last m) 1 j) • arnoldiW A v₁ m := by
    intro j
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 j.2) with hj | hj
    · have hjl : j = Fin.last m := Fin.ext (by simpa using hj)
      rw [hjl, Fin.val_last, Pi.single_eq_same, one_smul, arnoldiW_eq_smul A v₁ hv]
    · have hne : (j : ℕ) ≠ m := by omega
      rw [arnoldiCoeff_eq_zero_of_lt A v₁ hv (by omega), zero_smul]
      simp [Fin.ext_iff, hne]
  ext i j
  rw [mul_V_apply, equation_6_9_range A v₁ hv (N := m + 2) (by omega), Finset.sum_range_succ,
    hlast j,
    PiLp.add_apply, sum_coord, Matrix.add_apply, Matrix.mul_apply, Matrix.vecMulVec_apply,
    ← Fin.sum_univ_eq_sum_range
      (fun l => (arnoldiCoeff A v₁ l (j : ℕ) • arnoldiCGS A v₁ l) i) (m + 1)]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun l _ => mul_comm _ _) ?_
  rw [PiLp.smul_apply, smul_eq_mul, mul_comm]

/-- **Equation (6.8)** of [saad2003iterative], over $\mathbb{R}$ or $\mathbb{C}$. For every $v_1$
and every $m$, $V_m^H A V_m = H_m$. This is the book's $V_m^T A V_m = H_m$ for real matrices.

Neither a unit starting vector nor a bound on the number of Arnoldi steps is needed: both sides
are the same inner products by definition, and both vanish after the breakdown.

**Generalization.** Lean defines the projected matrix entrywise by inner products, so the
compression identity does not need an orthonormal basis or a successful full run.
-/
theorem conjTranspose_V_mul_mul_V (m : ℕ) : (V A v₁ m)ᴴ * A * V A v₁ m = H A v₁ m := by
  ext i j
  rw [Matrix.mul_assoc, Matrix.mul_apply, H_apply, arnoldiCoeff, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.conjTranspose_apply, V_apply, mul_V_apply, RCLike.inner_apply, mul_comm]
  rfl

/-! ### Proposition 6.6 and the lucky breakdown -/

/-- Let $\|v_1\| = 1$ and $j \ge 1$. Arnoldi's method breaks down at step $j$, that is, it does not
stop before step $j$ and $h_{j+1,j} = 0$, if and only if the grade of $v_1$ is $j$. This is the
first part of Proposition 6.6 of [saad2003iterative], over $\mathbb{R}$ or $\mathbb{C}$.

**Generalization.** Lean formulates the stopping test and grade criterion over real or complex
scalars. The invariance theorem also permits every index at or above the grade.
-/
theorem breakdown_iff_grade_eq (hv : ‖v₁‖ = 1) {j : ℕ} (hj : 0 < j) :
    (NoBreakdownBefore A v₁ j ∧ arnoldiCoeff A v₁ j (j - 1) = 0) ↔ grade A v₁ = j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [Nat.add_sub_cancel, noBreakdownBefore_iff A v₁ hv,
    arnoldiCoeff_succ_self_eq_zero_iff A v₁ hv]
  omega

/-- If the grade of $v_1$ is at most $j$, in particular after a breakdown of Arnoldi's method at
step $j$, then $\mathcal{K}_j(A, v_1)$ is invariant under $A$. This is the second part of
Proposition 6.6 of [saad2003iterative], over $\mathbb{R}$ or $\mathbb{C}$.

**Generalization.** Lean formulates the stopping test and grade criterion over real or complex
scalars. The invariance theorem also permits every index at or above the grade.
-/
theorem krylov_mem_invtSubmodule_of_breakdown {j : ℕ} (h : grade A v₁ ≤ j) :
    krylov A v₁ j ∈ Module.End.invtSubmodule (op A) := by
  rw [krylov_eq_of_grade_le A v₁ h]
  exact krylov_grade_mem_invtSubmodule A v₁

/-! ### Algorithm 6.2: Arnoldi with modified Gram–Schmidt -/

/-- The inner loop of **Algorithm 6.2** of [saad2003iterative]. For a $0$-based sequence
$u_0, u_1, \dots$ and a vector $w^{(0)}$, the vector $w^{(k)}$ is obtained by subtracting the
projections on $u_0, \dots, u_{k-1}$ one at a time.

It is the backbone modified Gram–Schmidt sweep `InnerProductSpace.modifiedGramSchmidtSweep`.

**Reading.** The recurrences also act over complex scalars, with conjugate-linear first argument in
Lean's inner-product convention. In the unit-start case they give the source's coefficients through
breakdown, with the totalized extension thereafter.
-/
noncomputable abbrev mgsW (v : ℕ → 𝔼) (w₀ : 𝔼) : ℕ → 𝔼 :=
  InnerProductSpace.modifiedGramSchmidtSweep 𝕜 v w₀

/-- One step of the inner loop of Algorithm 6.2: $w^{(k+1)} = w^{(k)} - (w^{(k)}, u_k) u_k$.

**Reading.** The recurrences also act over complex scalars, with conjugate-linear first argument in
Lean's inner-product convention. In the unit-start case they give the source's coefficients through
breakdown, with the totalized extension thereafter.
-/
theorem mgsW_succ (v : ℕ → 𝔼) (w₀ : 𝔼) (k : ℕ) :
    mgsW v w₀ (k + 1) = mgsW v w₀ k - inner 𝕜 (v k) (mgsW v w₀ k) • v k :=
  InnerProductSpace.modifiedGramSchmidtSweep_succ 𝕜 v w₀ k

private theorem mgsW_congr {v v' : ℕ → 𝔼} (w₀ : 𝔼) {k : ℕ} (h : ∀ i < k, v i = v' i) :
    mgsW v w₀ k = mgsW v' w₀ k :=
  InnerProductSpace.modifiedGramSchmidtSweep_congr 𝕜 w₀ h

/-- If $u_0, u_1, \dots$ are pairwise orthogonal, then the inner loop of modified Gram–Schmidt
subtracts the same total as classical Gram–Schmidt:
$$w^{(k)} = w^{(0)} - \sum_{i < k} (w^{(0)}, u_i) u_i.$$
-/
theorem mgsW_eq_sub_sum {v : ℕ → 𝔼} (ho : ∀ i j, i ≠ j → inner 𝕜 (v i) (v j) = 0)
    (w₀ : 𝔼) (k : ℕ) :
    mgsW v w₀ k = w₀ - ∑ i ∈ Finset.range k, inner 𝕜 (v i) w₀ • v i :=
  InnerProductSpace.modifiedGramSchmidtSweep_eq_sub_sum 𝕜 (fun i j h => ho i j h) w₀ k

/-- If $u_0, u_1, \dots$ are pairwise orthogonal, then the loop does not change the coefficient that
it computes next: $(w^{(k)}, u_k) = (w^{(0)}, u_k)$. -/
theorem inner_mgsW_self {v : ℕ → 𝔼} (ho : ∀ i j, i ≠ j → inner 𝕜 (v i) (v j) = 0)
    (w₀ : 𝔼) (k : ℕ) : inner 𝕜 (v k) (mgsW v w₀ k) = inner 𝕜 (v k) w₀ :=
  InnerProductSpace.inner_modifiedGramSchmidtSweep_self 𝕜 (fun i j h => ho i j h) w₀ k

/-- **Algorithm 6.2** of [saad2003iterative] (Arnoldi, modified Gram–Schmidt). Start from $v_1$. For
$j = 1, 2, \dots$, set $w := Av_j$; for $i = 1, \dots, j$, set $h_{ij} := (w, v_i)$ and
$w := w - h_{ij} v_i$; then $v_{j+1} = w / \|w\|_2$.

The index is $0$-based: `arnoldiMGS A v₁ j` is $v_{j+1}$. The definition reads the earlier
vectors through the clamp `min i j`; this does not matter, because the inner loop reads only
$v_1, \dots, v_j$ (`SaadSparse.Chapter06.mgsW_congr`).

**Reading.** Lean gives exact infinite sequences. Division by zero returns the zero vector, so the
sequence is padded with zeros after the point where the printed algorithm stops. The definitions
also allow complex scalars and a nonunit input; the Arnoldi properties use a unit starting vector.
-/
noncomputable def arnoldiMGS (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ : 𝔼) : ℕ → 𝔼
  | 0 => v₁
  | j + 1 =>
    let v : ℕ → 𝔼 := fun i => arnoldiMGS A v₁ (min i j)
    let w := mgsW v (op A (v j)) (j + 1)
    ((‖w‖ : 𝕜)⁻¹) • w
  termination_by j => j
  decreasing_by exact Nat.lt_succ_of_le (Nat.min_le_right _ _)

/-- The vector $w_j$ of Algorithm 6.2: what remains of $A v_j$ after the whole inner loop.

**Reading.** The recurrences also act over complex scalars, with conjugate-linear first argument in
Lean's inner-product convention. In the unit-start case they give the source's coefficients through
breakdown, with the totalized extension thereafter.
-/
noncomputable def arnoldiMGSW (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ : 𝔼) (j : ℕ) : 𝔼 :=
  mgsW (arnoldiMGS A v₁) (op A (arnoldiMGS A v₁ j)) (j + 1)

/-- **Algorithm 6.2** of [saad2003iterative], the coefficients. For $i \le j$, $h_{ij}$ is the inner
product $(w, v_i)$ with the current $w$ of the inner loop; $h_{j+1,j} = \|w_j\|_2$; and
$h_{ij} = 0$ for $i > j + 1$.

The indices are $0$-based, as for `SaadSparse.Chapter06.arnoldiCoeff`.

**Reading.** The recurrences also act over complex scalars, with conjugate-linear first argument in
Lean's inner-product convention. In the unit-start case they give the source's coefficients through
breakdown, with the totalized extension thereafter.
-/
noncomputable def arnoldiMGSCoeff (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ : 𝔼) (i j : ℕ) : 𝕜 :=
  if i ≤ j then inner 𝕜 (arnoldiMGS A v₁ i) (mgsW (arnoldiMGS A v₁) (op A (arnoldiMGS A v₁ j)) i)
  else if i = j + 1 then (‖arnoldiMGSW A v₁ j‖ : 𝕜) else 0

/-- The first vector of Algorithm 6.2 is the starting vector $v_1$. -/
@[simp]
theorem arnoldiMGS_zero : arnoldiMGS A v₁ 0 = v₁ := by rw [arnoldiMGS]

/-- Each next vector of Algorithm 6.2 is the normalized vector $v_{j+1} = w_j / \|w_j\|$, which is
$0$ when $w_j = 0$.

**Reading.** Lean gives exact infinite sequences. Division by zero returns the zero vector, so the
sequence is padded with zeros after the point where the printed algorithm stops. The definitions
also allow complex scalars and a nonunit input; the Arnoldi properties use a unit starting vector.
-/
theorem arnoldiMGS_succ (j : ℕ) :
    arnoldiMGS A v₁ (j + 1) = ((‖arnoldiMGSW A v₁ j‖ : 𝕜)⁻¹) • arnoldiMGSW A v₁ j := by
  rw [arnoldiMGS, arnoldiMGSW]
  simp only [Nat.min_self]
  rw [mgsW_congr (v := fun i => arnoldiMGS A v₁ (min i j)) (v' := arnoldiMGS A v₁)
    (op A (arnoldiMGS A v₁ j)) fun i hi => by rw [Nat.min_eq_left (Nat.lt_succ_iff.1 hi)]]

/-- If $\|v_1\| = 1$, then Algorithm 6.2 computes the backbone Arnoldi vectors `Arnoldi.vec` of
$v_1$, the Gram–Schmidt orthonormalization of the Krylov sequence. The proof checks the
recurrence that `Arnoldi.eq_vec_of_modifiedGramSchmidt` characterizes. -/
theorem arnoldiMGS_eq_vec (hv : ‖v₁‖ = 1) : arnoldiMGS A v₁ = Arnoldi.vec (op A) v₁ := by
  refine Arnoldi.eq_vec_of_modifiedGramSchmidt (op A) v₁ (by simp [hv]) fun j => ?_
  rw [arnoldiMGS_succ, arnoldiMGSW]

/-- **Section 6.3.2** of [saad2003iterative]. If $\|v_1\| = 1$, then in exact arithmetic Algorithm
6.2 computes the same vectors as Algorithm 6.1.

**Reading.** The equality compares the exact sequences for all indices, including the zeros after
the stopping point. The general statements also admit complex scalars.
-/
theorem arnoldiMGS_eq_arnoldiCGS (hv : ‖v₁‖ = 1) (j : ℕ) :
    arnoldiMGS A v₁ j = arnoldiCGS A v₁ j := by
  rw [arnoldiMGS_eq_vec A v₁ hv, arnoldiCGS_eq_vec A v₁ hv]

/-- **Section 6.3.2** of [saad2003iterative]. If $\|v_1\| = 1$, then in exact arithmetic Algorithm
6.2 computes the same coefficients $h_{ij}$ as Algorithm 6.1.

**Reading.** The equality compares the exact sequences for all indices, including the zeros after
the stopping point. The general statements also admit complex scalars.
-/
theorem arnoldiMGSCoeff_eq_arnoldiCoeff (hv : ‖v₁‖ = 1) (i j : ℕ) :
    arnoldiMGSCoeff A v₁ i j = arnoldiCoeff A v₁ i j := by
  have hvec : arnoldiMGS A v₁ = arnoldiCGS A v₁ := funext (arnoldiMGS_eq_arnoldiCGS A v₁ hv)
  have hw : arnoldiMGSW A v₁ j = arnoldiW A v₁ j := by
    rw [arnoldiMGSW, hvec, mgsW_eq_sub_sum (fun a b hab => inner_arnoldiCGS_eq_zero A v₁ hv hab),
      arnoldiW]
    rfl
  rw [arnoldiMGSCoeff, hvec, hw]
  split_ifs with h1 h2
  · rw [inner_mgsW_self (fun a b hab => inner_arnoldiCGS_eq_zero A v₁ hv hab), arnoldiCoeff]
  · rw [h2, arnoldiCoeff_succ_self A v₁ hv]
  · exact (arnoldiCoeff_eq_zero_of_lt A v₁ hv (by omega)).symm

end General

/-!
### Algorithm 6.3: Householder Arnoldi

The book presents Algorithm 6.3 for real matrices, with the real Householder reflectors
(1.23)–(1.26) of Section 1.7, and this section does the same. Indices are $0$-based, with the
correspondence given in the module doc comment: a Lean index $j$ stands for the book's index
$j + 1$, except for the columns $h_j$ of (6.12).
-/

section Householder

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin n)

/-- The $k$-th entry $z_k$ of a vector $z \in \mathbb{R}^n$, $0$-based, and $0$ for $k \ge n$. -/
noncomputable def coordAt (z : 𝔼) (k : ℕ) : ℝ := if h : k < n then z ⟨k, h⟩ else 0

/-- The $k$-th standard basis vector of $\mathbb{R}^n$, $0$-based, and the zero vector for
$k \ge n$. -/
noncomputable def stdVec (k : ℕ) : 𝔼 := WithLp.toLp 2 fun i => if (i : ℕ) = k then 1 else 0

/-- The tail $(0, \dots, 0, z_k, \dots, z_{n-1})$ of $z$, $0$-based. Its norm is the book's
$\big(\sum_{i \ge k} z_i^2\big)^{1/2}$. -/
noncomputable def householderTail (z : 𝔼) (k : ℕ) : 𝔼 :=
  WithLp.toLp 2 fun i => if k ≤ (i : ℕ) then z i else 0

/-- **Equation (1.26)** of [saad2003iterative]. The scalar $\beta = \operatorname{sign}(z_k)
\big(\sum_{i \ge k} z_i^2\big)^{1/2}$, with the convention $\operatorname{sign}(0) = 1$.

**Reading.** The source does not specify the sign at zero. Lean takes positive sign there, so a zero
leading coordinate with a nonzero tail still yields the stated reflector.
-/
noncomputable def householderBeta (z : 𝔼) (k : ℕ) : ℝ :=
  (if 0 ≤ coordAt z k then 1 else -1) * ‖householderTail z k‖

/-- **Equation (1.25)** of [saad2003iterative]. The unnormalized Householder direction $z'$ at
position $k$: its entries are $0$ for $i < k$, $\beta + z_k$ for $i = k$, and $z_i$ for $i > k$.

**Typo.** The source prints the $k$-th entry as $\beta + x_{ii}$. The intended entry is
$\beta + x_{kk}$, which is what Algorithm 1.3 needs and what is defined here. -/
noncomputable def householderDir (z : 𝔼) (k : ℕ) : 𝔼 :=
  WithLp.toLp 2 fun i =>
    if (i : ℕ) < k then 0 else if (i : ℕ) = k then householderBeta z k + z i else z i

/-- **Equation (1.24)** of [saad2003iterative]. The **Householder vector** $w = z' / \|z'\|_2$ at
position $k$.

It is $0$ when $z' = 0$, which happens exactly when $z_i = 0$ for all $i \ge k$.

**Reading.** The normalized direction is zero when the tail is zero, and the reflection formula then
acts as the identity. The source formula divides by the norm of the direction.
-/
noncomputable def householderVec (z : 𝔼) (k : ℕ) : 𝔼 :=
  (‖householderDir z k‖⁻¹ : ℝ) • householderDir z k

/-- **Equation (1.23)** of [saad2003iterative]. The **Householder reflector** $P = I - 2 w w^T$ of a
vector $w$, as a linear map of $\mathbb{R}^n$. It is the identity when $w = 0$.

**Generalization.** The map formula is defined for any vector, including zero. Its orthogonality is
proved separately under the unit-or-zero condition used by the Lean process.
-/
noncomputable def householder (w : 𝔼) : 𝔼 →ₗ[ℝ] 𝔼 :=
  LinearMap.id - (innerSL ℝ w).toLinearMap.smulRight ((2 : ℝ) • w)

/-- The $i$-th entry of the $k$-th standard basis vector is $1$ if $i = k$ and $0$ otherwise. -/
@[simp]
theorem stdVec_coord (k : ℕ) (i : Fin n) : stdVec k i = if (i : ℕ) = k then 1 else 0 := rfl

/-- The $i$-th entry of the tail of $z$ at position $k$ is $z_i$ if $i \ge k$ and $0$ otherwise. -/
@[simp]
theorem householderTail_coord (z : 𝔼) (k : ℕ) (i : Fin n) :
    householderTail z k i = if k ≤ (i : ℕ) then z i else 0 := rfl

/-- The $i$-th entry of the Householder direction $z'$ at position $k$ is $0$ for $i < k$,
$\beta + z_k$ for $i = k$, and $z_i$ for $i > k$.

**Correction.** Like the direction definition, these formulas use the entry at the pivot coordinate
where (1.25) prints the diagonal subscript $x_{ii}$.
-/
@[simp]
theorem householderDir_coord (z : 𝔼) (k : ℕ) (i : Fin n) :
    householderDir z k i =
      if (i : ℕ) < k then 0 else if (i : ℕ) = k then householderBeta z k + z i else z i := rfl

private theorem inner_coord (x y : 𝔼) : (inner ℝ x y : ℝ) = ∑ i, x i * y i := by
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- The Householder direction is the tail plus a multiple of the standard basis vector: $z' = (0,
\dots, 0, z_k, \dots, z_{n-1}) + \beta e_k$.

**Correction.** Like the direction definition, these formulas use the entry at the pivot coordinate
where (1.25) prints the diagonal subscript $x_{ii}$.
-/
theorem householderDir_eq (z : 𝔼) (k : ℕ) :
    householderDir z k = householderTail z k + householderBeta z k • stdVec k := by
  ext i
  rcases lt_trichotomy (i : ℕ) k with h | h | h
  · have h1 : ¬ k ≤ (i : ℕ) := by omega
    have h2 : (i : ℕ) ≠ k := by omega
    simp [h, h1, h2]
  · simp [h, add_comm]
  · have h1 : ¬ (i : ℕ) < k := by omega
    have h2 : (i : ℕ) ≠ k := by omega
    have h3 : k ≤ (i : ℕ) := by omega
    simp [h1, h2, h3]

/-- The inner product of the $k$-th standard basis vector with $x$ is the $k$-th entry of $x$, which
is $0$ for $k \ge n$. -/
theorem inner_stdVec_left (x : 𝔼) (k : ℕ) : (inner ℝ (stdVec k) x : ℝ) = coordAt x k := by
  rw [inner_coord]
  by_cases h : k < n
  · rw [Finset.sum_eq_single (⟨k, h⟩ : Fin n)]
    · simp [coordAt, h]
    · intro b _ hb
      have hbk : (b : ℕ) ≠ k := fun hc => hb (Fin.ext hc)
      simp [hbk]
    · simp
  · refine (Finset.sum_eq_zero fun i _ => ?_).trans (by simp [coordAt, h])
    have hik : (i : ℕ) ≠ k := by omega
    simp [hik]

/-- The squared norm of the tail of $z$ at position $k$ is its inner product with $z$. -/
theorem norm_householderTail_sq (z : 𝔼) (k : ℕ) :
    ‖householderTail z k‖ ^ 2 = (inner ℝ (householderTail z k) z : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, inner_coord, inner_coord]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : k ≤ (i : ℕ) <;> simp [h]

/-- The inner product of the tail of $z$ at position $k$ with $e_k$ is $z_k$. -/
theorem inner_householderTail_stdVec (z : 𝔼) (k : ℕ) :
    (inner ℝ (householderTail z k) (stdVec k) : ℝ) = coordAt z k := by
  rw [real_inner_comm, inner_stdVec_left, coordAt, coordAt]
  by_cases h : k < n <;> simp [h]

/-- For $k < n$, the $k$-th standard basis vector has squared norm $1$. -/
theorem norm_stdVec_sq_of_lt {k : ℕ} (h : k < n) : ‖(stdVec k : 𝔼)‖ ^ 2 = 1 := by
  rw [← real_inner_self_eq_norm_sq, inner_stdVec_left, coordAt]
  simp [h]

/-- For $k < n$, the $k$-th standard basis vector has norm $1$. -/
theorem norm_stdVec_of_lt {k : ℕ} (h : k < n) : ‖(stdVec k : 𝔼)‖ = 1 := by
  have h1 := norm_stdVec_sq_of_lt (n := n) h
  nlinarith [norm_nonneg (stdVec (n := n) k)]

/-- The scalar $\beta$ of (1.26) satisfies $\beta^2 = \sum_{i \ge k} z_i^2$. -/
theorem householderBeta_sq (z : 𝔼) (k : ℕ) :
    householderBeta z k ^ 2 = ‖householderTail z k‖ ^ 2 := by
  rw [householderBeta, mul_pow]
  split_ifs <;> norm_num

/-- The identity behind (1.24) of [saad2003iterative]: $2 (z', z) = \|z'\|_2^2$. -/
theorem two_inner_householderDir (z : 𝔼) (k : ℕ) :
    2 * (inner ℝ (householderDir z k) z : ℝ) = ‖householderDir z k‖ ^ 2 := by
  by_cases hk : k < n
  · have hS : (inner ℝ (householderTail z k) (householderTail z k) : ℝ)
        = ‖householderTail z k‖ ^ 2 := real_inner_self_eq_norm_sq _
    have hT : (inner ℝ (householderTail z k) (stdVec k) : ℝ) = coordAt z k :=
      inner_householderTail_stdVec z k
    have hT' : (inner ℝ (stdVec k) (householderTail z k) : ℝ) = coordAt z k := by
      rw [real_inner_comm]; exact hT
    have hE : (inner ℝ (stdVec (n := n) k) (stdVec k) : ℝ) = 1 := by
      rw [real_inner_self_eq_norm_sq]; exact norm_stdVec_sq_of_lt hk
    have hZ : (inner ℝ (stdVec k) z : ℝ) = coordAt z k := inner_stdVec_left z k
    have hb : householderBeta z k ^ 2 = ‖householderTail z k‖ ^ 2 := householderBeta_sq z k
    rw [← real_inner_self_eq_norm_sq, householderDir_eq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
    rw [hS, hT, hT', hE, hZ, ← norm_householderTail_sq]
    linear_combination -hb
  · have h0 : householderDir z k = 0 := by
      ext i
      have hi : (i : ℕ) < k := by omega
      simp [hi]
    rw [h0]
    simp

/-- The Householder reflector acts by $Px = x - 2 (x, w) w$. -/
theorem householder_apply (w x : 𝔼) : householder w x = x - (2 * inner ℝ w x) • w := by
  simp [householder, smul_smul, mul_comm]

/-- A vector supported on the coordinates $\ge k$ is orthogonal to a vector supported on the
coordinates $< k$. -/
theorem inner_eq_zero_of_supported {x y : 𝔼} {k : ℕ}
    (hx : ∀ i : Fin n, (i : ℕ) < k → x i = 0) (hy : ∀ i : Fin n, k ≤ (i : ℕ) → y i = 0) :
    (inner ℝ x y : ℝ) = 0 := by
  rw [inner_coord]
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases lt_or_ge (i : ℕ) k with h | h
  · rw [hx i h, zero_mul]
  · rw [hy i h, mul_zero]

/-- If $(x, w) = 0$, then the Householder reflector of $w$ fixes $x$. -/
theorem householder_apply_of_inner_eq_zero {w x : 𝔼} (h : (inner ℝ w x : ℝ) = 0) :
    householder w x = x := by
  rw [householder_apply, h]
  simp

/-- The Householder vector at position $k$ has norm $1$ or is $0$.

**Reading.** The normalized direction is zero when the tail is zero, and the reflection formula then
acts as the identity. The source formula divides by the norm of the direction.
-/
theorem norm_householderVec (z : 𝔼) (k : ℕ) :
    ‖householderVec z k‖ = 1 ∨ householderVec z k = 0 := by
  rcases eq_or_ne (householderDir z k) 0 with h | h
  · right
    rw [householderVec, h, smul_zero]
  · left
    rw [householderVec, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.2 h)]

/-- If $\|w\| = 1$ or $w = 0$, then the Householder reflector of $w$ is an involution: $P(Px) = x$.

**Reading.** The normalized direction is zero when the tail is zero, and the reflection formula then
acts as the identity. The source formula divides by the norm of the direction.
-/
theorem householder_householder {w : 𝔼} (hw : ‖w‖ = 1 ∨ w = 0) (x : 𝔼) :
    householder w (householder w x) = x := by
  rcases hw with hw | rfl
  · have hww : (inner ℝ w w : ℝ) = 1 := by
      rw [real_inner_self_eq_norm_sq, hw]; norm_num
    rw [householder_apply, householder_apply, inner_sub_right, real_inner_smul_right, hww]
    module
  · simp [householder_apply]

/-- The Householder reflector is symmetric: $(Px, y) = (x, Py)$. -/
theorem inner_householder (w x y : 𝔼) :
    (inner ℝ (householder w x) y : ℝ) = inner ℝ x (householder w y) := by
  rw [householder_apply, householder_apply, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_comm w x, real_inner_comm y w]
  ring

/-- If $\|w\| = 1$ or $w = 0$, then the Householder reflector of $w$ preserves the norm:
$\|Px\| = \|x\|$.

**Reading.** The normalized direction is zero when the tail is zero, and the reflection formula then
acts as the identity. The source formula divides by the norm of the direction.
-/
theorem norm_householder_apply {w : 𝔼} (hw : ‖w‖ = 1 ∨ w = 0) (x : 𝔼) :
    ‖householder w x‖ = ‖x‖ := by
  have h : (inner ℝ (householder w x) (householder w x) : ℝ) = inner ℝ x x := by
    rw [inner_householder, householder_householder hw]
  have h2 := congrArg Real.sqrt h
  rwa [real_inner_self_eq_norm_mul_norm, real_inner_self_eq_norm_mul_norm,
    Real.sqrt_mul_self (norm_nonneg _), Real.sqrt_mul_self (norm_nonneg _)] at h2

/-- The Householder vector at position $k$ has zero entries before position $k$. -/
theorem householderVec_coord_of_lt {z : 𝔼} {k : ℕ} {i : Fin n} (h : (i : ℕ) < k) :
    householderVec z k i = 0 := by
  simp [householderVec, h]

/-- **Equations (1.23)–(1.26)** of [saad2003iterative]. The Householder reflector at position $k$
maps $z$ to $z - z'$. It keeps the entries of $z$ before position $k$, puts $-\beta$ at position
$k$, and zeros after it.

**Reading.** The normalized direction is zero when the tail is zero, and the reflection formula then
acts as the identity. The source formula divides by the norm of the direction.
-/
theorem householder_householderVec_apply (z : 𝔼) (k : ℕ) :
    householder (householderVec z k) z = z - householderDir z k := by
  rcases eq_or_ne (householderDir z k) 0 with h | h
  · rw [householderVec, h, smul_zero, householder_apply]
    simp
  · have hn : ‖householderDir z k‖ ≠ 0 := norm_ne_zero_iff.2 h
    have hkey := two_inner_householderDir z k
    have hone : 2 * (‖householderDir z k‖⁻¹ * (inner ℝ (householderDir z k) z : ℝ)) *
        ‖householderDir z k‖⁻¹ = 1 := by
      field_simp
      linarith [hkey]
    rw [householder_apply, householderVec, real_inner_smul_left, smul_smul, hone, one_smul]

/-- The $i$-th entry of $Pz$, for the Householder reflector $P$ of $z$ at position $k$, is $z_i$ for
$i < k$, $-\beta$ for $i = k$, and $0$ for $i > k$.

**Reading.** The normalized direction is zero when the tail is zero, and the reflection formula then
acts as the identity. The source formula divides by the norm of the direction.
-/
theorem householder_householderVec_coord (z : 𝔼) (k : ℕ) (i : Fin n) :
    householder (householderVec z k) z i =
      if (i : ℕ) < k then z i else if (i : ℕ) = k then -householderBeta z k else 0 := by
  rw [householder_householderVec_apply, PiLp.sub_apply, householderDir_coord]
  rcases lt_trichotomy (i : ℕ) k with hi | hi | hi
  · simp [hi]
  · simp [hi]
  · have h1 : ¬ (i : ℕ) < k := by omega
    have h2 : (i : ℕ) ≠ k := by omega
    simp [h1, h2]

/-- A vector whose entries vanish from position $N$ on is the sum $\sum_{i < N} x_i e_i$. -/
theorem eq_sum_coordAt_smul_stdVec {x : 𝔼} {N : ℕ} (h : ∀ i : Fin n, N ≤ (i : ℕ) → x i = 0) :
    x = ∑ i ∈ Finset.range N, coordAt x i • stdVec i := by
  ext i'
  rw [sum_coord]
  by_cases hlt : (i' : ℕ) < N
  · rw [Finset.sum_eq_single (i' : ℕ)]
    · simp [coordAt, i'.isLt]
    · intro b _ hb
      simp [Ne.symm hb]
    · intro hb
      exact absurd (Finset.mem_range.2 hlt) hb
  · rw [h i' (by omega)]
    refine (Finset.sum_eq_zero fun b hb => ?_).symm
    have hne : (i' : ℕ) ≠ b := by
      have := Finset.mem_range.1 hb
      omega
    simp [hne]

/-- The composition $P_j \circ \dots \circ P_0$ of the Householder reflectors of a $0$-based family
of vectors $w_0, w_1, \dots$. -/
noncomputable def hhQAux (w : ℕ → 𝔼) : ℕ → (𝔼 →ₗ[ℝ] 𝔼)
  | 0 => householder (w 0)
  | j + 1 => householder (w (j + 1)) ∘ₗ hhQAux w j

/-- The composition $P_0 \circ \dots \circ P_j$ of the Householder reflectors of a $0$-based family
of vectors, the transpose of `SaadSparse.Chapter06.hhQAux`. -/
noncomputable def hhQTAux (w : ℕ → 𝔼) : ℕ → (𝔼 →ₗ[ℝ] 𝔼)
  | 0 => householder (w 0)
  | j + 1 => hhQTAux w j ∘ₗ householder (w (j + 1))

private theorem hhQAux_congr {w w' : ℕ → 𝔼} {j : ℕ} (h : ∀ i ≤ j, w i = w' i) :
    hhQAux w j = hhQAux w' j := by
  induction j with
  | zero => rw [hhQAux, hhQAux, h 0 le_rfl]
  | succ j ih => rw [hhQAux, hhQAux, ih fun i hi => h i (hi.trans j.le_succ), h (j + 1) le_rfl]

private theorem hhQTAux_congr {w w' : ℕ → 𝔼} {j : ℕ} (h : ∀ i ≤ j, w i = w' i) :
    hhQTAux w j = hhQTAux w' j := by
  induction j with
  | zero => rw [hhQTAux, hhQTAux, h 0 le_rfl]
  | succ j ih => rw [hhQTAux, hhQTAux, ih fun i hi => h i (hi.trans j.le_succ), h (j + 1) le_rfl]

/-- **Algorithm 6.3** of [saad2003iterative] (Householder Arnoldi), the auxiliary vectors. Start
from $z_1 = v$, and set $z_{j+1} = P_j P_{j-1} \cdots P_1 A v_j$, where $P_i$ is the Householder
reflector at position $i$ for $z_i$.

As in Algorithm 6.2, the clamp `min i j` does not matter, because only the first $j$ reflectors
are used. The index is $0$-based: `hhZ A v j` is $z_{j+1}$.

**Reading.** Lean gives an exact recurrence without fixed iteration limit, permits a zero start, and
uses the identity reflector for a zero tail. Where dependent Krylov vectors occur the reflectors can
supply orthogonal completion vectors, and out-of-range coordinate vectors are zero. The source
specifies a nonzero start and unit reflectors.
-/
noncomputable def hhZ (A : Matrix (Fin n) (Fin n) ℝ) (v : 𝔼) : ℕ → 𝔼
  | 0 => v
  | j + 1 =>
    let w : ℕ → 𝔼 := fun i => householderVec (hhZ A v (min i j)) (min i j)
    hhQAux w j (op A (hhQTAux w j (stdVec j)))
  termination_by j => j
  decreasing_by exact Nat.lt_succ_of_le (Nat.min_le_right _ _)

variable (A : Matrix (Fin n) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n))

/-- **Algorithm 6.3** of [saad2003iterative], lines 3–5. The Householder unit vector $w_j$, computed
from $z_j$ at position $j$.

The index is $0$-based: `hhW A v j` is $w_{j+1}$.

**Reading.** Lean gives an exact recurrence without fixed iteration limit, permits a zero start, and
uses the identity reflector for a zero tail. Where dependent Krylov vectors occur the reflectors can
supply orthogonal completion vectors, and out-of-range coordinate vectors are zero. The source
specifies a nonzero start and unit reflectors.
-/
noncomputable def hhW (j : ℕ) : 𝔼 := householderVec (hhZ A v j) j

/-- **Equation (6.10)** of [saad2003iterative]. The product of Householder reflectors
$Q_j = P_j P_{j-1} \cdots P_1$.

The index is $0$-based: `Qhh A v j` is $Q_{j+1}$.

**Reading.** Lean gives an exact recurrence without fixed iteration limit, permits a zero start, and
uses the identity reflector for a zero tail. Where dependent Krylov vectors occur the reflectors can
supply orthogonal completion vectors, and out-of-range coordinate vectors are zero. The source
specifies a nonzero start and unit reflectors.
-/
noncomputable def Qhh (j : ℕ) : 𝔼 →ₗ[ℝ] 𝔼 := hhQAux (hhW A v) j

/-- The transpose $Q_j^T = P_1 P_2 \cdots P_j$ of $Q_j$, which is its inverse (Exercise P-6.1(a),(b)
of [saad2003iterative]). The index is $0$-based: `QhhT A v j` is $Q_{j+1}^T$.

**Reading.** Lean gives an exact recurrence without fixed iteration limit, permits a zero start, and
uses the identity reflector for a zero tail. Where dependent Krylov vectors occur the reflectors can
supply orthogonal completion vectors, and out-of-range coordinate vectors are zero. The source
specifies a nonzero start and unit reflectors.
-/
noncomputable def QhhT (j : ℕ) : 𝔼 →ₗ[ℝ] 𝔼 := hhQTAux (hhW A v) j

/-- **Algorithm 6.3** of [saad2003iterative], line 7. The Householder Arnoldi vector
$v_j = P_1 P_2 \cdots P_j e_j$. The index is $0$-based: `hhV A v j` is $v_{j+1}$.

**Reading.** Lean gives an exact recurrence without fixed iteration limit, permits a zero start, and
uses the identity reflector for a zero tail. Where dependent Krylov vectors occur the reflectors can
supply orthogonal completion vectors, and out-of-range coordinate vectors are zero. The source
specifies a nonzero start and unit reflectors.
-/
noncomputable def hhV (j : ℕ) : 𝔼 := QhhT A v j (stdVec j)

/-- **Algorithm 6.3** of [saad2003iterative], line 6. The vector $h_{j-1} = P_j z_j$, the $j$-th
column of the factorization (6.12). The index is shifted: `hhH A v j` is
$h_j = P_{j+1} z_{j+1}$.

**Reading.** Lean gives an exact recurrence without fixed iteration limit, permits a zero start, and
uses the identity reflector for a zero tail. Where dependent Krylov vectors occur the reflectors can
supply orthogonal completion vectors, and out-of-range coordinate vectors are zero. The source
specifies a nonzero start and unit reflectors.
-/
noncomputable def hhH (j : ℕ) : 𝔼 := householder (hhW A v j) (hhZ A v j)

/-- The first product of reflectors is $Q_1 = P_1$. -/
theorem Qhh_zero : Qhh A v 0 = householder (hhW A v 0) := rfl

/-- The products of reflectors satisfy $Q_{j+1} = P_{j+1} Q_j$. -/
theorem Qhh_succ (j : ℕ) : Qhh A v (j + 1) = householder (hhW A v (j + 1)) ∘ₗ Qhh A v j := rfl

/-- The first transposed product is $Q_1^T = P_1$. -/
theorem QhhT_zero : QhhT A v 0 = householder (hhW A v 0) := rfl

/-- The transposed products satisfy $Q_{j+1}^T = Q_j^T P_{j+1}$. -/
theorem QhhT_succ (j : ℕ) : QhhT A v (j + 1) = QhhT A v j ∘ₗ householder (hhW A v (j + 1)) := rfl

/-- The first auxiliary vector of Algorithm 6.3 is $z_1 = v$. -/
@[simp]
theorem hhZ_zero : hhZ A v 0 = v := by rw [hhZ]

/-- The auxiliary vectors of Algorithm 6.3 satisfy $z_{j+1} = Q_j A v_j$.

**Reading.** Lean gives an exact recurrence without fixed iteration limit, permits a zero start, and
uses the identity reflector for a zero tail. Where dependent Krylov vectors occur the reflectors can
supply orthogonal completion vectors, and out-of-range coordinate vectors are zero. The source
specifies a nonzero start and unit reflectors.
-/
theorem hhZ_succ (j : ℕ) : hhZ A v (j + 1) = Qhh A v j (op A (hhV A v j)) := by
  rw [hhZ]
  have hw : ∀ i ≤ j, householderVec (hhZ A v (min i j)) (min i j) = hhW A v i := by
    intro i hi
    rw [Nat.min_eq_left hi, hhW]
  rw [hhQAux_congr (w' := hhW A v) hw, hhQTAux_congr (w' := hhW A v) hw]
  rfl

/-- Each Householder vector $w_j$ of Algorithm 6.3 has norm $1$ or is $0$.

**Reading.** Lean gives an exact recurrence without fixed iteration limit, permits a zero start, and
uses the identity reflector for a zero tail. Where dependent Krylov vectors occur the reflectors can
supply orthogonal completion vectors, and out-of-range coordinate vectors are zero. The source
specifies a nonzero start and unit reflectors.
-/
theorem norm_hhW (j : ℕ) : ‖hhW A v j‖ = 1 ∨ hhW A v j = 0 := norm_householderVec _ _

/-- The Householder vector $w_j$ of Algorithm 6.3 has zero entries before position $j$. -/
theorem hhW_coord_of_lt {j : ℕ} {i : Fin n} (h : (i : ℕ) < j) : hhW A v j i = 0 :=
  householderVec_coord_of_lt h

/-- Each reflector $P_j$ of Algorithm 6.3 fixes every vector supported on the coordinates before
position $j$. -/
theorem householder_hhW_apply_of_supported {j : ℕ} {x : 𝔼}
    (hx : ∀ i : Fin n, j ≤ (i : ℕ) → x i = 0) : householder (hhW A v j) x = x :=
  householder_apply_of_inner_eq_zero
    (inner_eq_zero_of_supported (fun _ hi => hhW_coord_of_lt A v hi) hx)

/-- Each reflector $P_j$ of Algorithm 6.3 fixes the standard basis vectors $e_i$ with $i < j$. -/
theorem householder_hhW_stdVec {i j : ℕ} (h : i < j) :
    householder (hhW A v j) (stdVec i) = stdVec i := by
  refine householder_hhW_apply_of_supported A v fun i' hi' => ?_
  have hne : (i' : ℕ) ≠ i := by omega
  simp [hne]

/-- **Exercise P-6.1(a),(b)** of [saad2003iterative]. The product $Q_j$ is orthogonal with inverse
$Q_j^T = P_1 \cdots P_j$: $Q_j^T Q_j x = x$ for every $x$. -/
theorem QhhT_Qhh (j : ℕ) (x : 𝔼) : QhhT A v j (Qhh A v j x) = x := by
  induction j with
  | zero => exact householder_householder (norm_hhW A v 0) x
  | succ j ih =>
    rw [QhhT_succ, Qhh_succ, LinearMap.comp_apply, LinearMap.comp_apply,
      householder_householder (norm_hhW A v (j + 1))]
    exact ih

/-- The product $Q_j^T$ is a right inverse of $Q_j$: $Q_j Q_j^T x = x$ for every $x$. -/
theorem Qhh_QhhT (j : ℕ) (x : 𝔼) : Qhh A v j (QhhT A v j x) = x := by
  induction j generalizing x with
  | zero => exact householder_householder (norm_hhW A v 0) x
  | succ j ih =>
    rw [QhhT_succ, Qhh_succ, LinearMap.comp_apply, LinearMap.comp_apply, ih,
      householder_householder (norm_hhW A v (j + 1))]

/-- The product $Q_j$ preserves the norm: $\|Q_j x\| = \|x\|$. -/
theorem norm_Qhh_apply (j : ℕ) (x : 𝔼) : ‖Qhh A v j x‖ = ‖x‖ := by
  induction j with
  | zero => exact norm_householder_apply (norm_hhW A v 0) x
  | succ j ih =>
    rw [Qhh_succ, LinearMap.comp_apply, norm_householder_apply (norm_hhW A v (j + 1)), ih]

/-- The transposed product $Q_j^T$ preserves the norm: $\|Q_j^T x\| = \|x\|$. -/
theorem norm_QhhT_apply (j : ℕ) (x : 𝔼) : ‖QhhT A v j x‖ = ‖x‖ := by
  induction j generalizing x with
  | zero => exact norm_householder_apply (norm_hhW A v 0) x
  | succ j ih =>
    rw [QhhT_succ, LinearMap.comp_apply, ih, norm_householder_apply (norm_hhW A v (j + 1))]

/-- The transposed product $Q_j^T$ preserves inner products: $(Q_j^T x, Q_j^T y) = (x, y)$. -/
theorem inner_QhhT (j : ℕ) (x y : 𝔼) :
    (inner ℝ (QhhT A v j x) (QhhT A v j y) : ℝ) = inner ℝ x y := by
  induction j generalizing x y with
  | zero => rw [QhhT_zero, inner_householder, householder_householder (norm_hhW A v 0)]
  | succ j ih =>
    rw [QhhT_succ, LinearMap.comp_apply, LinearMap.comp_apply, ih, inner_householder,
      householder_householder (norm_hhW A v (j + 1))]

/-- **Equation (6.13)** of [saad2003iterative], Exercise P-6.1(c). For all $i \le j$, the
Householder Arnoldi vectors satisfy
$$Q_j^T e_i = v_i.$$

In Lean, `QhhT A v j (stdVec i) = hhV A v i` for $i \le j$, $0$-based; this is
$Q_{j+1}^T e_{i+1} = v_{i+1}$. -/
theorem equation_6_13 {i j : ℕ} (h : i ≤ j) : QhhT A v j (stdVec i) = hhV A v i := by
  induction j with
  | zero =>
    obtain rfl : i = 0 := Nat.le_zero.1 h
    rfl
  | succ j ih =>
    rcases eq_or_lt_of_le h with rfl | h'
    · rfl
    · rw [QhhT_succ, LinearMap.comp_apply, householder_hhW_stdVec A v h']
      exact ih (Nat.lt_succ_iff.1 h')

/-- The vector $h_j$ of (6.12) has zero entries after position $j + 1$. In Lean, `hhH A v j` has
zero entries at the $0$-based positions $i > j$. -/
theorem hhH_coord_of_lt (j : ℕ) {i : Fin n} (h : j < (i : ℕ)) : hhH A v j i = 0 := by
  rw [hhH, hhW, householder_householderVec_coord]
  have h1 : ¬ (i : ℕ) < j := by omega
  have h2 : (i : ℕ) ≠ j := by omega
  simp [h1, h2]

/-- For $j < i$ ($0$-based), the reflector `householder (hhW A v i)` fixes `hhH A v j`: a later
reflector fixes an earlier column $h$ of (6.12). -/
theorem householder_hhW_hhH {i j : ℕ} (h : j < i) :
    householder (hhW A v i) (hhH A v j) = hhH A v j :=
  householder_hhW_apply_of_supported A v fun _ hi => hhH_coord_of_lt A v j (by omega)

/-- **Equation (6.11)** of [saad2003iterative]. For every $j \ge 1$, the Householder Arnoldi vectors
satisfy
$$h_j = Q_{j+1} A v_j.$$
-/
theorem equation_6_11 (j : ℕ) : hhH A v (j + 1) = Qhh A v (j + 1) (op A (hhV A v j)) := by
  rw [hhH, hhZ_succ, Qhh_succ, LinearMap.comp_apply]

/-- **Equation (6.12)** of [saad2003iterative], first column. For every $m$, $Q_{m+1} v = h_0$, that
is, $Q_{m+1}$ maps the starting vector to the first column of the factorization.

In Lean, `Qhh A v m` is $Q_{m+1}$.

**Correction.** The source prints $Q_m$ even though the final column $h_m$ includes the $(m+1)$-st
reflector. Lean uses enough reflectors to include that column, or any later product because later
reflectors fix it.
-/
theorem equation_6_12_zero (m : ℕ) : Qhh A v m v = hhH A v 0 := by
  induction m with
  | zero => rw [Qhh_zero, hhH, hhZ_zero]
  | succ m ih => rw [Qhh_succ, LinearMap.comp_apply, ih, householder_hhW_hhH A v (by omega)]

/-- **Equation (6.12)** of [saad2003iterative], the later columns. For $1 \le j \le m$,
$Q_{m+1} A v_j = h_j$. Together with `SaadSparse.Chapter06.equation_6_12_zero` this gives
$$Q_{m+1} [v, Av_1, \dots, Av_m] = [h_0, h_1, \dots, h_m],$$
and with `SaadSparse.Chapter06.hhH_coord_of_lt` it says that the right-hand side is upper
triangular.

In Lean, `Qhh A v m` is the book's $Q_{m+1}$.

**Correction.** The source prints $Q_m$ even though the final column $h_m$ includes the $(m+1)$-st
reflector. Lean uses enough reflectors to include that column, or any later product because later
reflectors fix it.
-/
theorem equation_6_12 {j m : ℕ} (h : j + 1 ≤ m) :
    Qhh A v m (op A (hhV A v j)) = hhH A v (j + 1) := by
  induction m, h using Nat.le_induction with
  | base => exact (equation_6_11 A v j).symm
  | succ m hm ih =>
    rw [Qhh_succ, LinearMap.comp_apply, ih, householder_hhW_hhH A v (by omega)]

/-- The Hessenberg coefficients of the Householder Arnoldi basis: in $0$-based indices, the $(i, j)$
coefficient is the $i$-th entry of `hhH A v (j + 1)`, the book's $h_{j+1}$. -/
noncomputable def hhCoeff (i j : ℕ) : ℝ := coordAt (hhH A v (j + 1)) i

/-- The Householder Hessenberg coefficients vanish more than one place below the diagonal: the
$(i, j)$ coefficient is $0$ for $i > j + 1$. -/
theorem hhCoeff_eq_zero_of_lt {i j : ℕ} (h : j + 1 < i) : hhCoeff A v i j = 0 := by
  rw [hhCoeff, coordAt]
  split_ifs with hi
  · exact hhH_coord_of_lt A v (j + 1) (by simpa using h)
  · rfl

/-- **Exercise P-6.1(d)** of [saad2003iterative]. The Householder Arnoldi vectors and coefficients
satisfy the Hessenberg relation `Krylov.HessenbergRelation`: $A v_j$ is a combination of
$v_1, \dots, v_{j+1}$ with the coefficients of $\bar H_m$. Hence $A V_m = V_{m+1} \bar H_m$.

**Correction.** Lean proves the Arnoldi relation $AV_m=V_{m+1}\bar H_m$ from §6.3.2. The literal
exercise display mixes the transformed left side with the Arnoldi basis and an extra coordinate
matrix on the right. With $Q_{m+1}$ on the left, the right side uses the first $m+1$ coordinate
vectors in place of $V_{m+1}$.
-/
theorem hh_hessenbergRelation :
    Krylov.HessenbergRelation (op A) (hhV A v) (hhCoeff A v) := by
  refine ⟨fun j => ?_, fun i j hij => hhCoeff_eq_zero_of_lt A v hij⟩
  have hzero : ∀ i : Fin n, j + 2 ≤ (i : ℕ) → hhH A v (j + 1) i = 0 :=
    fun i hi => hhH_coord_of_lt A v (j + 1) (by omega)
  have hAv : op A (hhV A v j) = QhhT A v (j + 1) (hhH A v (j + 1)) := by
    rw [equation_6_11, QhhT_Qhh]
  rw [hAv, eq_sum_coordAt_smul_stdVec hzero, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [map_smul, equation_6_13 A v (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]
  rfl

/-- The $n \times m$ matrix $V_m$ of the first $m$ Householder Arnoldi vectors. -/
noncomputable def VHH (m : ℕ) : Matrix (Fin n) (Fin m) ℝ := colMatrix (hhV A v) m

/-- **Exercise P-6.1** of [saad2003iterative]. The $(m+1) \times m$ Hessenberg matrix $\bar H_m$ of
the Householder Arnoldi coefficients: in the book's indices, its $(i, j)$ entry is the $i$-th
entry of $h_j$. -/
noncomputable def HbarHH (m : ℕ) : Matrix (Fin (m + 1)) (Fin m) ℝ :=
  Krylov.hessenbergOf (hhCoeff A v) m

/-- **Exercise P-6.1(d)** of [saad2003iterative]. For every $m$, the Householder Arnoldi basis
satisfies
$$A V_m = V_{m+1} \bar H_m.$$

No hypothesis on $v$ or $m$ is needed. The matrices are `SaadSparse.Chapter06.VHH` and
`SaadSparse.Chapter06.HbarHH`.

**Correction.** Lean proves the Arnoldi relation $AV_m=V_{m+1}\bar H_m$ from §6.3.2. The literal
exercise display mixes the transformed left side with the Arnoldi basis and an extra coordinate
matrix on the right. With $Q_{m+1}$ on the left, the right side uses the first $m+1$ coordinate
vectors in place of $V_{m+1}$.
-/
theorem hh_arnoldi_relation (m : ℕ) : A * VHH A v m = VHH A v (m + 1) * HbarHH A v m :=
  mul_colMatrix_eq A (hh_hessenbergRelation A v) m

/-- **Exercise P-6.1(e)** of [saad2003iterative]. For $i < n$ ($0$-based), the Householder Arnoldi
vectors satisfy $(v_{j+1}, v_{i+1}) = 1$ if $i = j$ and $0$ otherwise. -/
theorem inner_hhV {i j : ℕ} (hi : i < n) :
    (inner ℝ (hhV A v i) (hhV A v j) : ℝ) = if i = j then 1 else 0 := by
  have h := inner_QhhT A v (max i j) (stdVec i) (stdVec j)
  rw [equation_6_13 A v (le_max_left i j), equation_6_13 A v (le_max_right i j)] at h
  rw [h, inner_stdVec_left]
  simp [coordAt, hi]

/-- For $i < n$ ($0$-based), the Householder Arnoldi vector `hhV A v i` has norm $1$. -/
theorem norm_hhV {i : ℕ} (h : i < n) : ‖hhV A v i‖ = 1 := by
  rw [hhV, norm_QhhT_apply, norm_stdVec_of_lt h]

/-- **Exercise P-6.1(e)** of [saad2003iterative]. If $m \le n$, then the Householder Arnoldi vectors
$v_1, \dots, v_m$ are orthonormal. -/
theorem hh_orthonormal {m : ℕ} (hm : m ≤ n) :
    Orthonormal ℝ (fun i : Fin m => hhV A v (i : ℕ)) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · dsimp only
    exact norm_hhV A v (lt_of_lt_of_le i.2 hm)
  · have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.val_injective h)
    dsimp only
    rw [inner_hhV A v (lt_of_lt_of_le i.2 hm)]
    simp [hne]

/-- The first column of the factorization (6.12) is $h_0 = -\beta e_1$, where $\beta$ is the scalar
(1.26) of $v$ at the first position, so that $|\beta| = \|v\|$. This is the
$\beta = \pm \|r_0\|$ of Householder GMRES (Algorithm 6.10). -/
theorem hhH_zero : hhH A v 0 = (-householderBeta v 0) • stdVec 0 := by
  ext i
  rw [hhH, hhZ_zero, hhW, hhZ_zero, householder_householderVec_coord, PiLp.smul_apply,
    stdVec_coord]
  simp

/-- The scalar $\beta$ of (1.26) of $v$ at the first position satisfies $|\beta| = \|v\|$. -/
theorem abs_householderBeta_zero : |householderBeta v 0| = ‖v‖ := by
  have htail : householderTail v 0 = v := by
    ext i
    simp
  rw [householderBeta, htail, abs_mul, abs_of_nonneg (norm_nonneg _)]
  split_ifs <;> simp

/-- The starting vector is $v = -\beta v_1$: the first Householder Arnoldi vector is
$\pm v / \|v\|$. -/
theorem smul_hhV_zero : (-householderBeta v 0) • hhV A v 0 = v := by
  have h : householder (hhW A v 0) (hhH A v 0) = v := by
    rw [hhH, householder_householder (norm_hhW A v 0), hhZ_zero]
  rw [hhH_zero, map_smul] at h
  exact h

/-! ### The Householder flag and comparison with Gram–Schmidt Arnoldi -/

private theorem span_hhV_mono {i j : ℕ} (h : i ≤ j) :
    Submodule.span ℝ (hhV A v '' Set.Iio i) ≤ Submodule.span ℝ (hhV A v '' Set.Iio j) :=
  Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio h))

private theorem map_span_hhV_le (i : ℕ) :
    Submodule.map (op A) (Submodule.span ℝ (hhV A v '' Set.Iio (i + 1)))
      ≤ Submodule.span ℝ (hhV A v '' Set.Iio (i + 2)) := by
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
  have hl' : l < i + 1 := hl
  rw [SetLike.mem_coe, (hh_hessenbergRelation A v).apply_eq l]
  refine Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ ?_
  rw [Finset.mem_range] at hk
  exact Submodule.subset_span ⟨k, show k < i + 2 by omega, rfl⟩

private theorem pow_apply_mem_span_hhV (i : ℕ) :
    (op A ^ i) v ∈ Submodule.span ℝ (hhV A v '' Set.Iio (i + 1)) := by
  induction i with
  | zero =>
    have h0 : hhV A v 0 ∈ Submodule.span ℝ (hhV A v '' Set.Iio 1) :=
      Submodule.subset_span ⟨0, by simp, rfl⟩
    have h1 := Submodule.smul_mem _ (-householderBeta v 0) h0
    rw [smul_hhV_zero A v] at h1
    simpa using h1
  | succ i ih =>
    have hstep : (op A ^ (i + 1)) v = op A ((op A ^ i) v) := by
      rw [pow_succ']
      rfl
    rw [hstep]
    exact map_span_hhV_le A v i ⟨_, ih, rfl⟩

/-- For every $m$, the Krylov subspace $\mathcal{K}_m(A, v)$ is contained in the span of the first
$m$ Householder Arnoldi vectors. This half of the flag identity needs no hypothesis. -/
theorem krylov_le_span_hhV (m : ℕ) :
    krylov A v m ≤ Submodule.span ℝ (hhV A v '' Set.Iio m) := by
  rw [krylov_eq, Krylov.subspace, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact span_hhV_mono A v (by omega) (pow_apply_mem_span_hhV A v (i : ℕ))

/-- **Equation (6.12)** of [saad2003iterative], span form. If $m \le n$ and the grade of $v$ is at
least $m$, then the first $m$ Householder Arnoldi vectors span $\mathcal{K}_m(A, v)$.

**Reading.** Lean restricts the Krylov-basis and sign comparisons to the prefix within the grade.
The source's comparison is stated for Arnoldi vectors that actually exist. After breakdown the
Householder vectors can complete the basis.
-/
theorem span_hhV_eq {m : ℕ} (hmn : m ≤ n) (hmg : m ≤ grade A v) :
    Submodule.span ℝ (hhV A v '' Set.Iio m) = krylov A v m := by
  have hfin : Module.finrank ℝ (Submodule.span ℝ (hhV A v '' Set.Iio m)) = m := by
    rw [← range_fin_eq_image_Iio]
    simpa using finrank_span_eq_card (hh_orthonormal A v hmn).linearIndependent
  have hk : Module.finrank ℝ (krylov A v m) = m := by rw [finrank_krylov, min_eq_left hmg]
  exact (Submodule.eq_of_le_of_finrank_le (krylov_le_span_hhV A v m) (by rw [hfin, hk])).symm

/-- **Exercise P-6.1(f)** of [saad2003iterative]. Let $v \neq 0$, and let $m + 1 \le n$ and
$m + 1 \le \mu$, where $\mu$ is the grade of $v$. Then there are signs
$\varepsilon_j \in \{1, -1\}$ such that, for $j = 1, \dots, m + 1$, the Householder Arnoldi
vector $v_j$ is $\varepsilon_j$ times the $j$-th vector of Algorithm 6.1 started at $v / \|v\|$.

In Lean, the conclusion is `hhV A v j = ε j • arnoldiCGS A (‖v‖⁻¹ • v) j` for $j \le m$,
$0$-based.

**Reading.** Lean restricts the Krylov-basis and sign comparisons to the prefix within the grade.
The source's comparison is stated for Arnoldi vectors that actually exist. After breakdown the
Householder vectors can complete the basis.
-/
theorem hh_eq_arnoldi_up_to_sign (hv : v ≠ 0) {m : ℕ} (hmn : m + 1 ≤ n)
    (hmg : m + 1 ≤ grade A v) :
    ∃ ε : ℕ → ℝ, (∀ j, ε j = 1 ∨ ε j = -1) ∧
      ∀ j ≤ m, hhV A v j = ε j • arnoldiCGS A (‖v‖⁻¹ • v) j := by
  classical
  have hnorm : ∀ i, arnoldiCGS A (‖v‖⁻¹ • v) i = Arnoldi.vec (op A) v i :=
    arnoldiCGS_normalize A hv
  refine ⟨fun j => if (inner ℝ (Arnoldi.vec (op A) v j) (hhV A v j) : ℝ) < 0 then -1 else 1,
    fun j => ?_, ?_⟩
  · dsimp only
    split_ifs with h
    · exact Or.inr rfl
    · exact Or.inl rfl
  intro j hj
  dsimp only
  have hmem : hhV A v j ∈ Krylov.subspace (op A) v (j + 1) := by
    rw [← krylov_eq, ← span_hhV_eq A v (by omega) (by omega)]
    exact Submodule.subset_span ⟨j, Nat.lt_succ_self j, rfl⟩
  have hperp : hhV A v j ∈ (Krylov.subspace (op A) v j)ᗮ := by
    rw [← krylov_eq, ← span_hhV_eq A v (by omega) (by omega), Submodule.mem_orthogonal_span]
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k < j := hk
    rw [inner_hhV A v (show k < n by omega)]
    simp [Nat.ne_of_lt hk']
  have hzero : ∀ i ∈ Finset.range (j + 1), i ≠ j →
      (inner ℝ (Arnoldi.vec (op A) v i) (hhV A v j) : ℝ) • Arnoldi.vec (op A) v i = 0 := by
    intro i hi hij
    have hlt : i < j := by
      rw [Finset.mem_range] at hi
      omega
    rw [(Submodule.mem_orthogonal _ _).1 hperp _ (Arnoldi.vec_mem_subspace_of_lt (op A) v hlt),
      zero_smul]
  have hsum : ∑ i ∈ Finset.range (j + 1),
      (inner ℝ (Arnoldi.vec (op A) v i) (hhV A v j) : ℝ) • Arnoldi.vec (op A) v i
      = (inner ℝ (Arnoldi.vec (op A) v j) (hhV A v j) : ℝ) • Arnoldi.vec (op A) v j :=
    Finset.sum_eq_single j hzero fun hb =>
      absurd (Finset.mem_range.2 (Nat.lt_succ_self j)) hb
  have hsingle : hhV A v j
      = (inner ℝ (Arnoldi.vec (op A) v j) (hhV A v j) : ℝ) • Arnoldi.vec (op A) v j :=
    (Arnoldi.eq_sum_inner_smul_vec (op A) v hmem).trans hsum
  have hnu : ‖Arnoldi.vec (op A) v j‖ = 1 :=
    Arnoldi.norm_vec_eq_one_of_lt_grade (op A) v (by rw [← grade_eq]; omega)
  have hnv : ‖hhV A v j‖ = 1 := norm_hhV A v (by omega)
  have habs : |(inner ℝ (Arnoldi.vec (op A) v j) (hhV A v j) : ℝ)| = 1 := by
    have hc := congrArg norm hsingle
    rwa [hnv, norm_smul, hnu, mul_one, Real.norm_eq_abs, eq_comm] at hc
  have hif : (if (inner ℝ (Arnoldi.vec (op A) v j) (hhV A v j) : ℝ) < 0 then (-1 : ℝ) else 1)
      = (inner ℝ (Arnoldi.vec (op A) v j) (hhV A v j) : ℝ) := by
    rcases (abs_eq (le_of_lt one_pos)).1 habs with h1 | h1 <;> rw [h1] <;> norm_num
  rw [hif, hnorm j]
  exact hsingle

end Householder

/-! ### The numbered results of Section 6.3, over the real numbers -/

section BookResults

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v₁ : EuclideanSpace ℝ (Fin n))

/-- **Proposition 6.4** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ and let
$v_1 \in \mathbb{R}^n$ have norm $1$. If Algorithm 6.1 does not stop before the $m$-th step,
then the vectors $v_1, \dots, v_m$ form an orthonormal basis of the Krylov subspace
$$\mathcal{K}_m = \operatorname{span}\{v_1, Av_1, \dots, A^{m-1} v_1\}.$$

The conclusion is stated as two parts: the vectors are orthonormal, and they span
$\mathcal{K}_m$. -/
theorem proposition_6_4 (hv : ‖v₁‖ = 1) {m : ℕ} (h : NoBreakdownBefore A v₁ m) :
    Orthonormal ℝ (fun i : Fin m => arnoldiCGS A v₁ (i : ℕ)) ∧
      Submodule.span ℝ (Set.range fun i : Fin m => arnoldiCGS A v₁ (i : ℕ)) = krylov A v₁ m :=
  ⟨orthonormal_arnoldiCGS A v₁ hv ((noBreakdownBefore_iff A v₁ hv m).1 h),
    span_arnoldiCGS A v₁ hv m⟩

/-- **Equation (6.9)** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ and let
$v_1 \in \mathbb{R}^n$ have norm $1$. Then for every $j$,
$$A v_j = \sum_{i=1}^{j+1} h_{ij} v_i.$$

**Generalization.** The identities use the totalized exact sequence for every applicable order,
including zeros after the point at which Algorithm 6.1 stops.
-/
theorem equation_6_9 (hv : ‖v₁‖ = 1) (j : ℕ) :
    op A (arnoldiCGS A v₁ j)
      = ∑ i ∈ Finset.range (j + 2), arnoldiCoeff A v₁ i j • arnoldiCGS A v₁ i :=
  apply_arnoldiCGS A v₁ hv j

/-- **Equation (6.7)** of [saad2003iterative], part of Proposition 6.5. Let
$A \in \mathbb{R}^{n \times n}$ and let $v_1 \in \mathbb{R}^n$ have norm $1$. Then for every
$m$,
$$A V_m = V_{m+1} \bar H_m.$$

**Generalization.** The identities use the totalized exact sequence for every applicable order,
including zeros after the point at which Algorithm 6.1 stops.
-/
theorem equation_6_7 (hv : ‖v₁‖ = 1) (m : ℕ) : A * V A v₁ m = V A v₁ (m + 1) * Hbar A v₁ m :=
  mul_V_eq A v₁ hv m

/-- **Equation (6.6)** of [saad2003iterative], part of Proposition 6.5. Let
$A \in \mathbb{R}^{n \times n}$ and let $v_1 \in \mathbb{R}^n$ have norm $1$. Then for every
$m \ge 1$,
$$A V_m = V_m H_m + w_m e_m^T.$$

The Lean statement is for $m + 1$ steps: the last term is the outer product of
`arnoldiW A v₁ m`, the book's $w_{m+1}$, with the last coordinate vector of $\mathbb{R}^{m+1}$.

**Generalization.** The identities use the totalized exact sequence for every applicable order,
including zeros after the point at which Algorithm 6.1 stops.
-/
theorem equation_6_6 (hv : ‖v₁‖ = 1) (m : ℕ) :
    A * V A v₁ (m + 1) = V A v₁ (m + 1) * H A v₁ (m + 1) +
      Matrix.vecMulVec (WithLp.ofLp (arnoldiW A v₁ m)) (Pi.single (Fin.last m) 1) :=
  mul_V_eq_add_vecMulVec A v₁ hv m

/-- **Equation (6.8)** of [saad2003iterative], part of Proposition 6.5. Let
$A \in \mathbb{R}^{n \times n}$ and $v_1 \in \mathbb{R}^n$. Then for every $m$,
$$V_m^T A V_m = H_m.$$

The identity holds for every $v_1$ and every $m$, also after a breakdown, because both sides are
the same inner products.

**Generalization.** Lean defines the projected matrix entrywise by inner products, so the
compression identity does not need an orthonormal basis or a successful full run.
-/
theorem equation_6_8 (m : ℕ) : (V A v₁ m)ᵀ * A * V A v₁ m = H A v₁ m := by
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact conjTranspose_V_mul_mul_V A v₁ m

/-- **Proposition 6.6** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$, let
$v_1 \in \mathbb{R}^n$ have norm $1$, and let $j \ge 1$. Arnoldi's method breaks down at step
$j$, that is, $h_{j+1,j} = 0$ and no earlier step broke down, if and only if the minimal
polynomial of $v_1$ has degree $j$.

In Lean, the breakdown is `NoBreakdownBefore A v₁ j ∧ arnoldiCoeff A v₁ j (j - 1) = 0`, and the
degree of the minimal polynomial is the grade `SaadSparse.Chapter06.grade`. -/
theorem proposition_6_6 (hv : ‖v₁‖ = 1) {j : ℕ} (hj : 0 < j) :
    (NoBreakdownBefore A v₁ j ∧ arnoldiCoeff A v₁ j (j - 1) = 0) ↔ grade A v₁ = j :=
  breakdown_iff_grade_eq A v₁ hv hj

/-- **Proposition 6.6** of [saad2003iterative], second part. Let $A \in \mathbb{R}^{n \times n}$,
let $v_1 \in \mathbb{R}^n$ have norm $1$, and let $j \ge 1$. If Arnoldi's method breaks down at
step $j$, then the subspace $\mathcal{K}_j$ is invariant under $A$. -/
theorem proposition_6_6' (hv : ‖v₁‖ = 1) {j : ℕ} (hj : 0 < j)
    (h : NoBreakdownBefore A v₁ j ∧ arnoldiCoeff A v₁ j (j - 1) = 0) :
    krylov A v₁ j ∈ Module.End.invtSubmodule (op A) :=
  krylov_mem_invtSubmodule_of_breakdown A v₁ ((proposition_6_6 A v₁ hv hj).1 h).le

variable {A}

/-- **Section 6.3.1** of [saad2003iterative], the consequence of Proposition 6.6 stated in the text.
Let $A \in \mathbb{R}^{n \times n}$, $b, x_0 \in \mathbb{R}^n$, $r_0 = b - Ax_0$ and $j \ge 1$,
and let the grade of $r_0$ be at most $j$. Let $L$ be a subspace such that no nonzero vector of
$\mathcal{K}_j(A, r_0)$ is orthogonal to $L$. If $x$ is the approximation of a projection method
onto $\mathcal{K}_j(A, r_0)$ orthogonally to $L$, that is, $x - x_0 \in \mathcal{K}_j(A, r_0)$
and $b - Ax \perp L$, then $Ax = b$.

This is Proposition 5.6 of [saad2003iterative] applied to the invariant subspace
$\mathcal{K}_j$. The approximation is `IsPetrovGalerkin`.

**Reading.** Exactness for a Petrov–Galerkin approximation needs $K_j\cap L^\perp=\{0\}$, the same
transversality condition used in the Lean reading of Proposition 5.6. The grade inequality also
allows using an already stabilized Krylov subspace.
-/
theorem lucky_breakdown {j : ℕ} (hj : 0 < j) {b x₀ x : EuclideanSpace ℝ (Fin n)}
    {L : Submodule ℝ (EuclideanSpace ℝ (Fin n))} (hbreak : grade A (b - op A x₀) ≤ j)
    (hKL : ∀ z ∈ krylov A (b - op A x₀) j, z ∈ Lᗮ → z = 0)
    (hx : IsPetrovGalerkin (op A) b x₀ (krylov A (b - op A x₀) j) L x) :
    op A x = b :=
  hx.eq_of_invt (krylov_mem_invtSubmodule_of_breakdown A _ hbreak)
    (self_mem_krylov A _ hj) hKL

variable (A)

/-- **Section 6.3.2** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ and let
$v_1 \in \mathbb{R}^n$ have norm $1$. Then **Algorithm 6.2 is mathematically equivalent to
Algorithm 6.1**: in exact arithmetic the two produce the same vectors $v_j$ and the same
coefficients $h_{ij}$.

**Reading.** The equality compares the exact sequences for all indices, including the zeros after
the stopping point. The general statements also admit complex scalars.
-/
theorem algorithm_6_2_eq_alg_6_1 (hv : ‖v₁‖ = 1) :
    arnoldiMGS A v₁ = arnoldiCGS A v₁ ∧ arnoldiMGSCoeff A v₁ = arnoldiCoeff A v₁ :=
  ⟨funext (arnoldiMGS_eq_arnoldiCGS A v₁ hv),
    funext fun i => funext fun j => arnoldiMGSCoeff_eq_arnoldiCoeff A v₁ hv i j⟩

end BookResults

section ResidualStart

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜] (A : Matrix (Fin n) (Fin n) 𝕜)
  (b x₀ : EuclideanSpace 𝕜 (Fin n))

/-!
### The bridge to the backbone Arnoldi data of $r_0$

The book runs Algorithm 6.1 on the unit vector $v_1 = r_0 / \beta$, and the backbone indexes the
Arnoldi process by the residual $r_0$ itself. These lemmas translate between the two. They need no
hypothesis: when $r_0 = 0$, both sides vanish.
-/

private theorem vec_zero_eq_v₁ : Arnoldi.vec (op A) (r₀ A b x₀) 0 = v₁ A b x₀ := by
  rcases eq_or_ne (r₀ A b x₀) 0 with h | h
  · rw [v₁, h, smul_zero]
    exact (Arnoldi.vec_eq_zero_iff_pow_apply_mem (op A) 0 0).2 (by simp)
  · exact Arnoldi.vec_zero (op A) _ h

/-- Algorithm 6.1 started at $v_1 = r_0 / \beta$ computes the backbone Arnoldi vectors `Arnoldi.vec`
of $r_0$: the $j$-th vectors agree for every $j$. -/
theorem arnoldiCGS_v₁_apply (j : ℕ) :
    arnoldiCGS A (v₁ A b x₀) j = Arnoldi.vec (op A) (r₀ A b x₀) j :=
  arnoldiCGS_eq_vec_of_vec_zero A _ (vec_zero_eq_v₁ A b x₀) j

/-- Algorithm 6.1 started at $v_1 = r_0 / \beta$ computes the backbone Arnoldi vectors of $r_0$, as
an equality of sequences. -/
theorem arnoldiCGS_v₁ : arnoldiCGS A (v₁ A b x₀) = Arnoldi.vec (op A) (r₀ A b x₀) :=
  funext (arnoldiCGS_v₁_apply A b x₀)

/-- The coefficients $h_{ij}$ of Algorithm 6.1 started at $v_1 = r_0 / \beta$ are the backbone
Arnoldi coefficients `Arnoldi.coeff` of $r_0$, for all $i$, $j$. -/
theorem arnoldiCoeff_v₁_apply (i j : ℕ) :
    arnoldiCoeff A (v₁ A b x₀) i j = Arnoldi.coeff (op A) (r₀ A b x₀) i j := by
  rw [arnoldiCoeff, arnoldiCGS_v₁_apply, arnoldiCGS_v₁_apply]
  rfl

/-- The coefficients of Algorithm 6.1 started at $v_1 = r_0 / \beta$ are the backbone Arnoldi
coefficients of $r_0$, as an equality of functions. -/
theorem arnoldiCoeff_v₁ : arnoldiCoeff A (v₁ A b x₀) = Arnoldi.coeff (op A) (r₀ A b x₀) :=
  funext fun i => funext fun j => arnoldiCoeff_v₁_apply A b x₀ i j

/-- The matrix $\bar H_m$ of Algorithm 6.1 started at $v_1 = r_0 / \beta$ is the backbone matrix
`Arnoldi.hessenberg` of $r_0$. -/
theorem Hbar_v₁ (m : ℕ) : Hbar A (v₁ A b x₀) m = Arnoldi.hessenberg (op A) (r₀ A b x₀) m := by
  ext i j
  rw [Hbar_apply, arnoldiCoeff_v₁]
  rfl

/-- The matrix $H_m$ of Algorithm 6.1 started at $v_1 = r_0 / \beta$ is the backbone matrix
`Arnoldi.hessenbergSq` of $r_0$. -/
theorem H_v₁ (m : ℕ) : H A (v₁ A b x₀) m = Arnoldi.hessenbergSq (op A) (r₀ A b x₀) m := by
  ext i j
  rw [H_apply, arnoldiCoeff_v₁]
  rfl

/-- The coefficients of Algorithm 6.1 started at $v_1 = r_0 / \beta$ are upper Hessenberg, with no
hypothesis on $v_1$: $h_{ij} = 0$ for $i > j + 1$. This is the standing hypothesis of the Givens
rotation results of Section 6.5. -/
theorem arnoldiCoeff_v₁_eq_zero_of_lt (i j : ℕ) (hij : j + 1 < i) :
    arnoldiCoeff A (v₁ A b x₀) i j = 0 := by
  rw [arnoldiCoeff_v₁]
  exact Arnoldi.coeff_eq_zero_of_lt (op A) _ hij

end ResidualStart

end SaadSparse.Chapter06

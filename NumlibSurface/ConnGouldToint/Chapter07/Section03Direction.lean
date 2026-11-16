/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Direct.Substitution
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Sequences
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Conn, Gould and Toint, Section 7.3.7: The LINPACK hard-case direction

This module formalizes the LINPACK direction of Section 7.3.7 of [conn2000trust], which the
Moré–Sorensen algorithm uses in the hard case. Let $A = L L^T$ be a Cholesky factorization with $L$
lower triangular and positive diagonal. The LINPACK method solves $L w = v$ by forward substitution,
choosing each entry $v_i \in \{1, -1\}$ greedily: with $b_i = \sum_{j < i} L_{ij} w_j$, it takes the
sign for which $|v_i - b_i|$ is larger, so that $|v_i - b_i| \ge 1$. It then solves $L^T y = w$. The
Rayleigh quotient $y^T A y / y^T y$ is at most $n \det(A)^{1/n}$, so it tends to zero when $A$ tends
to a singular matrix, and the normalized directions approach the kernel of the limit (7.3.16).

At a failed pivot of the Cholesky factorization, a back solve gives a vector $v$ with last entry $1$
that is a kernel vector of the leading principal block after a rank-one correction $\delta e e^T$ of
its last pivot (7.3.17). The Rayleigh quotient of the zero extension of $v$ then gives a lower bound
on the pole $-\lambda_1$ of the full matrix.

## Main definitions

* Section 7.3.7, `ConnGouldToint.Chapter07.linpackSign`: the sign with the larger magnitude
  $|v - b|$.
* Section 7.3.7, `ConnGouldToint.Chapter07.linpackForwardSubst`: the greedy forward substitution.
* Section 7.3.7, `ConnGouldToint.Chapter07.linpackCurvature`: the Rayleigh quotient
  $y^T A y / y^T y$.
* Equation (7.3.17), `ConnGouldToint.Chapter07.failedCholeskyBackSubst`: the back solve at a failed
  pivot, with pivot entry $1$.

## Main results

* Section 7.3.7, `ConnGouldToint.Chapter07.abs_linpackSign` and
  `ConnGouldToint.Chapter07.one_le_abs_linpackSign_sub`: the chosen sign has magnitude $1$ and gives
  a residual of magnitude at least $1$.
* Section 7.3.7, `ConnGouldToint.Chapter07.linpackForwardSubst_apply` and
  `ConnGouldToint.Chapter07.linpack_triangular_solves`: the greedy row recurrence and the triangular
  solves of the certificate.
* Section 7.3.7, `ConnGouldToint.Chapter07.linpackCurvature_bound`: the curvature satisfies
  $0 \le c$ and $c^n \le n^n \det(L L^T)$.
* Equation (7.3.16), `ConnGouldToint.Chapter07.linpackCurvature_tendsto_zero` and
  `ConnGouldToint.Chapter07.linpackCurvature_tendsto_zero_of_eventually`: the curvature tends to
  zero when the determinants do.
* Section 7.3.7, `ConnGouldToint.Chapter07.linpackCurvature_eq_of_normalization`: the curvature is
  the quadratic form at a unit multiple of the direction.
* Equation (7.3.16), `ConnGouldToint.Chapter07.linpackDirection_limit`: at a singular positive
  semidefinite limit, the normalized directions have vanishing curvature and approach the kernel.
* Equation (7.3.17), `ConnGouldToint.Chapter07.failedCholeskyBackSubst_spec`,
  `ConnGouldToint.Chapter07.failedCholeskyPivotDirection` and
  `ConnGouldToint.Chapter07.failedCholeskyPivot_correction`: the kernel equation of the corrected
  leading principal block.
* Equation (7.3.17), `ConnGouldToint.Chapter07.failedCholeskyPivot_full_residual_counterexample`:
  the kernel equation can fail for the full matrix.
* Section 7.3.7 and Algorithm 7.3.4, Steps 3c–d,
  `ConnGouldToint.Chapter07.failedCholeskyPivot_lower_bound`: the Rayleigh lower bound on the pole
  from the failed pivot.

## Implementation notes

* Matrices are indexed by `Fin n`, and a leading principal block followed by the pivot row is
  indexed by `ι ⊕ Unit`, with the pivot as `Sum.inr ()`.

## Deviations from the source

* **Section 7.3.7, sign rule** (correction). The source compares the signed candidates $1 - b$ and
  $-1 - b$, which always selects $+1$; this choice misses the kernel of the $2 \times 2$ all-ones
  matrix. The rule compares magnitudes. See `ConnGouldToint.Chapter07.linpackSign`.
* **Equation (7.3.17)** (correction). The kernel equation holds on the leading principal block, not
  on the full matrix. See
  `ConnGouldToint.Chapter07.failedCholeskyPivot_full_residual_counterexample`.
-/

namespace ConnGouldToint.Chapter07

open Matrix Filter
open scoped Topology

/-- **Section 7.3.7** of [conn2000trust], the corrected sign choice. For $b \in \mathbb{R}$, the
**LINPACK sign** is $1$ if $|1 - b| \ge |-1 - b|$ and $-1$ otherwise: the right-hand side in
$\{1, -1\}$ farther from $b$, with ties going to $1$.

**Correction.** The source compares the signed values $1 - b$ and $-1 - b$, which always selects
$1$. This choice misses the kernel of the $2 \times 2$ all-ones matrix. Comparing magnitudes
gives a bound on every Cholesky pivot and makes the normalized curvature vanish at a singular
limit. -/
noncomputable def linpackSign (b : ℝ) : ℝ :=
  if |1 - b| ≥ |-1 - b| then 1 else -1

/-- **Section 7.3.7** of [conn2000trust], sign choice. The LINPACK sign has magnitude $1$:
$|\sigma(b)| = 1$ for every $b \in \mathbb{R}$. -/
theorem abs_linpackSign (b : ℝ) : |linpackSign b| = 1 := by
  unfold linpackSign
  split <;> norm_num

/-- **Section 7.3.7** of [conn2000trust], greedy row bound. For every $b \in \mathbb{R}$, the
LINPACK sign satisfies $|\sigma(b) - b| \ge 1$. -/
theorem one_le_abs_linpackSign_sub (b : ℝ) : 1 ≤ |linpackSign b - b| := by
  have ht := abs_sub_le (1 - b) 0 (-1 - b)
  have htwo : (1 : ℝ) - b - (-1 - b) = 2 := by ring
  rw [htwo, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), sub_zero,
    zero_sub, abs_neg] at ht
  unfold linpackSign
  split <;> linarith

/-- **Section 7.3.7** of [conn2000trust], greedy forward substitution. For a square matrix $L$ of
order $n$, the vector $w$ is defined row by row: with $b_i = \sum_{j < i} L_{ij} w_j$,
$$w_i = \frac{\sigma(b_i) - b_i}{L_{ii}},$$
where $\sigma$ is the LINPACK sign. The sign is chosen after the contribution of the earlier
rows is known.

The quotient is $0$ when $L_{ii} = 0$. -/
noncomputable def linpackForwardSubst {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) : Fin n → ℝ
  | i =>
    let b := ∑ j ∈ (Finset.univ.filter (· < i)).attach, L i j * linpackForwardSubst L j
    (linpackSign b - b) / L i i
termination_by i => i.val
decreasing_by exact (Finset.mem_filter.mp j.property).2

/-- **Section 7.3.7** of [conn2000trust], greedy row recurrence. For every row $i$, with
$b_i = \sum_{j < i} L_{ij} w_j$, the greedy forward substitution satisfies
$w_i = (\sigma(b_i) - b_i) / L_{ii}$. -/
theorem linpackForwardSubst_apply {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    let b := ∑ j ∈ Finset.univ.filter (· < i), L i j * linpackForwardSubst L j
    linpackForwardSubst L i = (linpackSign b - b) / L i i := by
  rw [linpackForwardSubst, Finset.sum_attach (Finset.univ.filter (· < i))
    (fun j => L i j * linpackForwardSubst L j)]

/-- **Section 7.3.7** of [conn2000trust], the triangular solves. Let $L$ be lower triangular with
nonzero diagonal. Let $w$ be the greedy forward substitution,
$v_i = \sigma(\sum_{j < i} L_{ij} w_j)$, and let $y$ be the back substitution solution of
$L^T y = w$. Then
$$L w = v, \qquad L^T y = w, \qquad v_i = \sigma(v_i - L_{ii} w_i) \text{ for all } i.$$

These three facts form the certificate of the LINPACK direction. -/
theorem linpack_triangular_solves {n : ℕ} {L : Matrix (Fin n) (Fin n) ℝ}
    (hL : L.IsLowerTriangular) (hd : ∀ i, L i i ≠ 0) :
    let w := linpackForwardSubst L
    let v := fun i => linpackSign (∑ j ∈ Finset.univ.filter (· < i), L i j * w j)
    let y := Lᵀ.backSubst w
    L *ᵥ w = v ∧ Lᵀ *ᵥ y = w ∧
      ∀ i, v i = linpackSign (v i - L i i * w i) := by
  dsimp only
  have hrow (i : Fin n) :
      L i i * linpackForwardSubst L i =
        linpackSign (∑ j ∈ Finset.univ.filter (· < i), L i j * linpackForwardSubst L j) -
          ∑ j ∈ Finset.univ.filter (· < i), L i j * linpackForwardSubst L j := by
    rw [linpackForwardSubst_apply L i, mul_div_cancel₀ _ (hd i)]
  refine ⟨?_, Matrix.mulVec_backSubst _ (fun _ _ hij => hL hij) hd, ?_⟩
  · ext i
    rw [Matrix.mulVec_apply_of_isLowerTriangular hL, hrow, add_sub_cancel]
  · intro i
    rw [hrow, sub_sub_cancel]

/-- **Section 7.3.7** of [conn2000trust]. For a square matrix $A$ and a vector $y$, the **Rayleigh
quotient** of the back solve is
$$\frac{y^T A y}{y^T y}.$$

Its value is $0$ when $y = 0$. -/
noncomputable def linpackCurvature {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (y : Fin n → ℝ) : ℝ :=
  (y ⬝ᵥ A *ᵥ y) / (y ⬝ᵥ y)

/-- **Section 7.3.7** of [conn2000trust], curvature bound from the corrected direction. Let
$n \ge 1$, let $L$ be lower triangular of order $n$ with positive diagonal, and let $v, w, y$
satisfy $L w = v$, $L^T y = w$ and $v_i = \sigma(v_i - L_{ii} w_i)$ for all $i$. Then the
Rayleigh quotient $c = y^T L L^T y / y^T y$ satisfies
$$0 \le c \quad \text{and} \quad c^n \le n^n \det(L L^T).$$
-/
theorem linpackCurvature_bound {n : ℕ} (hn : 0 < n)
    {L : Matrix (Fin n) (Fin n) ℝ} (hL : L.IsLowerTriangular)
    (hd : ∀ i, 0 < L i i) {v w y : Fin n → ℝ}
    (hw : L *ᵥ w = v) (hy : Lᵀ *ᵥ y = w)
    (hv : ∀ i, v i = linpackSign (v i - L i i * w i)) :
    0 ≤ linpackCurvature (L * Lᵀ) y ∧
      linpackCurvature (L * Lᵀ) y ^ n ≤ (n : ℝ) ^ n * (L * Lᵀ).det := by
  let q := linpackCurvature (L * Lᵀ) y
  have hs (i : Fin n) : 1 ≤ L i i * |w i| := by
    have hr := one_le_abs_linpackSign_sub (v i - L i i * w i)
    rw [← hv i, show v i - (v i - L i i * w i) = L i i * w i by ring,
      abs_mul, abs_of_pos (hd i)] at hr
    exact hr
  have hdprod (z : Fin n → ℝ) : z ⬝ᵥ z = ∑ i, z i ^ 2 := by
    simp [dotProduct, pow_two]
  have hnn (z : Fin n → ℝ) : 0 ≤ z ⬝ᵥ z := by
    rw [hdprod]
    exact Finset.sum_nonneg fun i _ => sq_nonneg (z i)
  have hnorm (z : Fin n → ℝ) (i : Fin n) : z i ^ 2 ≤ z ⬝ᵥ z := by
    rw [hdprod]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (z j)) (Finset.mem_univ i)
  have hyy : 0 < y ⬝ᵥ y := by
    let i : Fin n := ⟨0, hn⟩
    have hne : y ≠ 0 := by
      intro h
      have hzero : w = 0 := by simpa [h] using hy.symm
      have := hs i
      simp [hzero] at this
      exact (not_le_of_gt zero_lt_one) this
    obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
      by_contra! hall
      exact hne (funext hall)
    exact (sq_pos_of_ne_zero hj).trans_le (hnorm y j)
  have hww : w ⬝ᵥ w = y ⬝ᵥ v := by
    rw [← hw, ← Matrix.dotProduct_transpose_mulVec, hy]
  have hq : q = (w ⬝ᵥ w) / (y ⬝ᵥ y) := by
    unfold q linpackCurvature
    rw [← Matrix.mulVec_mulVec, hy, hw, hww]
  have hq0 : 0 ≤ q := hq ▸ div_nonneg (hnn w) hyy.le
  have hvv : v ⬝ᵥ v = (n : ℝ) := by
    rw [hdprod]
    have hi (i : Fin n) : v i ^ 2 = 1 := by
      rw [← sq_abs (v i), hv i, abs_linpackSign, one_pow]
    simp [hi]
  have hcs : (w ⬝ᵥ w) ^ 2 ≤ (y ⬝ᵥ y) * (n : ℝ) := by
    rw [hww, ← hvv, hdprod y, hdprod v]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ y v
  have hmul : q * (w ⬝ᵥ w) ≤ (n : ℝ) := by
    rw [hq, div_mul_eq_mul_div, div_le_iff₀ hyy]
    simpa [pow_two, mul_comm] using hcs
  have hpiv (i : Fin n) : q ≤ (n : ℝ) * (L i i)^2 := by
    have hrow := pow_le_pow_left₀ zero_le_one (hs i) 2
    rw [one_pow, mul_pow, sq_abs] at hrow
    have hi : 1 ≤ (L i i)^2 * (w ⬝ᵥ w) :=
      hrow.trans (mul_le_mul_of_nonneg_left (hnorm w i) (sq_nonneg _))
    calc
      q = q * 1 := (mul_one q).symm
      _ ≤ q * ((L i i)^2 * (w ⬝ᵥ w)) := mul_le_mul_of_nonneg_left hi hq0
      _ = (q * (w ⬝ᵥ w)) * (L i i)^2 := by ring
      _ ≤ (n : ℝ) * (L i i)^2 := mul_le_mul_of_nonneg_right hmul (sq_nonneg _)
  refine ⟨hq0, ?_⟩
  calc
    q ^ n = ∏ _i : Fin n, q := by simp
    _ ≤ ∏ i : Fin n, (n : ℝ) * (L i i)^2 :=
      Finset.prod_le_prod₀ (fun _ _ => hq0) (fun i _ => hpiv i)
    _ = (n : ℝ) ^ n * (L * Lᵀ).det := by
      have hprod : (∏ i : Fin n, (L i i)^2) = (∏ i : Fin n, L i i)^2 :=
        Finset.prod_pow Finset.univ 2 (fun i : Fin n => L i i)
      rw [Finset.prod_mul_distrib, hprod, Matrix.det_mul,
        Matrix.det_transpose, Matrix.det_of_isLowerTriangular L hL]
      simp [pow_two]

/-- **Equation (7.3.16)** of [conn2000trust], along a filter. Let $n \ge 1$, and let $L_k$, $v_k$,
$w_k$, $y_k$ be indexed by a filter $f$. Suppose that, eventually along $f$, $L_k$ is lower
triangular with positive diagonal, $L_k w_k = v_k$, $L_k^T y_k = w_k$ and
$v_{k,i} = \sigma(v_{k,i} - (L_k)_{ii} w_{k,i})$ for all $i$. If $\det(L_k L_k^T) \to 0$ along
$f$, then the Rayleigh quotients $y_k^T L_k L_k^T y_k / y_k^T y_k$ tend to $0$ along $f$.

For example, $f$ can be the filter of successful factorizations of a run. -/
theorem linpackCurvature_tendsto_zero_of_eventually {n : ℕ} (hn : 0 < n)
    {ι : Type*} {f : Filter ι} {L : ι → Matrix (Fin n) (Fin n) ℝ} {v w y : ι → Fin n → ℝ}
    (hcert : ∀ᶠ k in f, (L k).IsLowerTriangular ∧ (∀ i, 0 < L k i i) ∧
      L k *ᵥ w k = v k ∧ (L k)ᵀ *ᵥ y k = w k ∧
      ∀ i, v k i = linpackSign (v k i - L k i i * w k i))
    (hlim : Tendsto (fun k => (L k * (L k)ᵀ).det) f (𝓝 0)) :
    Tendsto (fun k => linpackCurvature (L k * (L k)ᵀ) (y k)) f (𝓝 0) := by
  have ht : Tendsto (fun k => (n : ℝ)^n * (L k * (L k)ᵀ).det) f (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hlim (a := (n : ℝ)^n)
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hcert, ht.eventually (eventually_lt_nhds (pow_pos hε n))]
    with k ⟨hL, hd, hw, hy, hv⟩ hk
  have hb := linpackCurvature_bound hn hL hd hw hy hv
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hb.1]
  by_contra! hc
  exact (not_lt_of_ge (pow_le_pow_left₀ hε.le hc n)) (hb.2.trans_lt hk)

/-- **Equation (7.3.16)** of [conn2000trust], with the corrected sign choice. Let $n \ge 1$, and for
every $k$ let $L_k$ be lower triangular with positive diagonal, with $L_k w_k = v_k$,
$L_k^T y_k = w_k$ and $v_{k,i} = \sigma(v_{k,i} - (L_k)_{ii} w_{k,i})$ for all $i$. If
$\det(L_k L_k^T) \to 0$, then
$$\frac{y_k^T L_k L_k^T y_k}{y_k^T y_k} \to 0.$$
-/
theorem linpackCurvature_tendsto_zero {n : ℕ} (hn : 0 < n)
    {L : ℕ → Matrix (Fin n) (Fin n) ℝ} {v w y : ℕ → Fin n → ℝ}
    (hL : ∀ k, (L k).IsLowerTriangular) (hd : ∀ k i, 0 < L k i i)
    (hw : ∀ k, L k *ᵥ w k = v k) (hy : ∀ k, (L k)ᵀ *ᵥ y k = w k)
    (hv : ∀ k i, v k i = linpackSign (v k i - L k i i * w k i))
    (hlim : Tendsto (fun k => (L k * (L k)ᵀ).det) atTop (𝓝 0)) :
    Tendsto (fun k => linpackCurvature (L k * (L k)ᵀ) (y k)) atTop (𝓝 0) :=
  linpackCurvature_tendsto_zero_of_eventually hn
    (Eventually.of_forall fun k => ⟨hL k, hd k, hw k, hy k, hv k⟩) hlim

/-- **Section 7.3.7** of [conn2000trust], unit normalization. Let $A$ be a square matrix and
$u = c y$ with $u^T u = 1$. Then the Rayleigh quotient of $y$ is $u^T A u$. -/
theorem linpackCurvature_eq_of_normalization {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) {u y : Fin n → ℝ} {c : ℝ}
    (hu : u = c • y) (hunit : u ⬝ᵥ u = 1) :
    linpackCurvature A y = u ⬝ᵥ A *ᵥ u := by
  rw [hu, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  rw [hu, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at hunit
  have hyy : y ⬝ᵥ y ≠ 0 := by
    intro hz
    simp [hz] at hunit
  unfold linpackCurvature
  apply (div_eq_iff hyy).2
  calc
    _ = 1 * (y ⬝ᵥ A *ᵥ y) := by ring
    _ = _ := by rw [← hunit]; ring

/-- **Equation (7.3.16)** of [conn2000trust], the limit of the directions. Let $n \ge 1$, and for
every $k$ let $L_k$ be lower triangular with positive diagonal, with $L_k w_k = v_k$,
$L_k^T y_k = w_k$ and $v_{k,i} = \sigma(v_{k,i} - (L_k)_{ii} w_{k,i})$ for all $i$. Let $u_k$ be
unit multiples of $y_k$. Let $A$ be positive semidefinite with $\det A = 0$, and suppose that
$L_k L_k^T \to A$. Then
$$u_k^T L_k L_k^T u_k \to 0 \quad \text{and} \quad \operatorname{dist}(u_k, \ker A) \to 0.$$

When $L_k L_k^T = H + \lambda_k I$ with $\lambda_k \to -\lambda_1$, the kernel of $A$ is the
eigenspace of $H$ for its least eigenvalue $\lambda_1$. -/
theorem linpackDirection_limit {n : ℕ} (hn : 0 < n)
    {L : ℕ → Matrix (Fin n) (Fin n) ℝ} {v w y u : ℕ → Fin n → ℝ}
    (hL : ∀ k, (L k).IsLowerTriangular) (hd : ∀ k i, 0 < L k i i)
    (hw : ∀ k, L k *ᵥ w k = v k) (hy : ∀ k, (L k)ᵀ *ᵥ y k = w k)
    (hv : ∀ k i, v k i = linpackSign (v k i - L k i i * w k i))
    (hu : ∀ k, ∃ c : ℝ, u k = c • y k) (hunit : ∀ k, u k ⬝ᵥ u k = 1)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) (hdet : A.det = 0)
    (hlim : Tendsto (fun k => L k * (L k)ᵀ) atTop (𝓝 A)) :
    Tendsto (fun k => u k ⬝ᵥ (L k * (L k)ᵀ) *ᵥ u k) atTop (𝓝 0) ∧
      Tendsto (fun k => Metric.infDist (u k) {z | A *ᵥ z = 0}) atTop (𝓝 0) := by
  have hdetlim : Tendsto (fun k => (L k * (L k)ᵀ).det) atTop (𝓝 0) := by
    rw [← hdet]
    exact continuous_id.matrix_det.continuousAt.tendsto.comp hlim
  have h := linpackCurvature_tendsto_zero hn hL hd hw hy hv hdetlim
  have heq (k : ℕ) :
      linpackCurvature (L k * (L k)ᵀ) (y k) = u k ⬝ᵥ (L k * (L k)ᵀ) *ᵥ u k := by
    obtain ⟨c, hc⟩ := hu k
    exact linpackCurvature_eq_of_normalization _ hc (hunit k)
  simp only [heq] at h
  have hkernel (j : ℕ → ℕ) (z : Fin n → ℝ) (hj : Tendsto j atTop atTop)
      (hz : Tendsto (u ∘ j) atTop (𝓝 z)) : A *ᵥ z = 0 := by
    have hcont : Continuous (fun p : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ) =>
        p.2 ⬝ᵥ p.1 *ᵥ p.2) := by
      unfold dotProduct
      fun_prop
    have hq := hcont.continuousAt.tendsto.comp ((hlim.comp hj).prodMk_nhds hz)
    have hzero : z ⬝ᵥ A *ᵥ z = 0 := tendsto_nhds_unique hq (h.comp hj)
    exact hA.dotProduct_mulVec_zero_iff.mp (by simpa using hzero)
  let K : Set (Fin n → ℝ) := {z | A *ᵥ z = 0}
  let B : Set (Fin n → ℝ) := Set.univ.pi (fun _ => Set.Icc (-1 : ℝ) 1)
  have hB : IsCompact B := isCompact_univ_pi fun _ => isCompact_Icc
  have huB (k : ℕ) : u k ∈ B := by
    intro i _
    have hs : (u k i)^2 ≤ u k ⬝ᵥ u k := by
      simp only [dotProduct, ← pow_two]
      exact Finset.single_le_sum (fun j _ => sq_nonneg (u k j)) (Finset.mem_univ i)
    rw [hunit k] at hs
    exact ⟨by nlinarith, by nlinarith⟩
  refine ⟨h, ?_⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  by_contra hE
  have hf : ∃ᶠ k in atTop, ε ≤ Metric.infDist (u k) K := by
    simpa only [Filter.Frequently, not_le, Real.dist_eq, sub_zero,
      abs_of_nonneg Metric.infDist_nonneg] using hE
  obtain ⟨j, hj, hjε⟩ := exists_seq_forall_of_frequently hf
  obtain ⟨z, _, l, hl, hz⟩ := hB.tendsto_subseq (x := u ∘ j) (fun k => huB (j k))
  have hzK : z ∈ K := hkernel (j ∘ l) z (hj.comp hl.tendsto_atTop) hz
  have hdist : Tendsto (fun k => Metric.infDist (u (j (l k))) K) atTop (𝓝 0) := by
    rw [← Metric.infDist_zero_of_mem hzK]
    exact (Metric.continuous_infDist_pt K).continuousAt.tendsto.comp hz
  have hε' := hdist.eventually (eventually_lt_nhds hε)
  exact (hε'.and (Eventually.of_forall fun k => hjε (l k))).exists.elim
    (fun _ hk => (not_lt_of_ge hk.2) hk.1)

/-- **Equation (7.3.17)** of [conn2000trust], the back solve at a failed pivot. For a square matrix
$L$ indexed by $\iota$ and a row $c$ indexed by $\iota$, the vector indexed by $\iota$ and the
pivot is
$$v = \begin{bmatrix} -L^{-T} c^T \\ 1 \end{bmatrix},$$
where $L^{-T} c^T$ is computed by back substitution. -/
noncomputable def failedCholeskyBackSubst {ι : Type*} [Fintype ι] [LinearOrder ι]
    (L : Matrix ι ι ℝ) (C : Matrix Unit ι ℝ) : ι ⊕ Unit → ℝ :=
  Sum.elim (Lᵀ.backSubst (-(Cᵀ *ᵥ (fun _ => 1)))) (fun _ => 1)

/-- **Equation (7.3.17)** of [conn2000trust], the computed kernel witness. Let $L$ be lower
triangular with positive diagonal, $c$ a row, $\delta \in \mathbb{R}$, $e$ the unit vector of
the pivot, and $B$ a matrix of the leading principal block with
$$B + \delta e e^T = \begin{bmatrix} L \\ c \end{bmatrix} \begin{bmatrix} L \\ c
  \end{bmatrix}^T.$$
Then the back solve $v$ at the failed pivot satisfies
$$v_{\mathrm{pivot}} = 1, \qquad (B + \delta e e^T) v = 0, \qquad v^T B v = -\delta.$$

**Correction.** The source states the kernel equation for the full matrix with $v$ extended by
zero. If the pivot fails before the last row, the zero extension can have a nonzero residual in
the later rows, so the equation is stated on the leading principal block; see
`ConnGouldToint.Chapter07.failedCholeskyPivot_full_residual_counterexample`. -/
theorem failedCholeskyBackSubst_spec {ι : Type*} [Fintype ι] [LinearOrder ι]
    {L : Matrix ι ι ℝ}
    (hL : L.IsLowerTriangular) (hd : ∀ i, 0 < L i i)
    (C : Matrix Unit ι ℝ) (δ : ℝ)
    (B : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ)
    (e : ι ⊕ Unit → ℝ) (he : e = Sum.elim (0 : ι → ℝ) (fun _ : Unit => 1))
    (hB : B + δ • vecMulVec e e = fromRows L C * (fromRows L C)ᵀ) :
    let v := failedCholeskyBackSubst L C
    v (Sum.inr ()) = 1 ∧ (B + δ • vecMulVec e e) *ᵥ v = 0 ∧ v ⬝ᵥ B *ᵥ v = -δ := by
  let y := Lᵀ.backSubst (-(Cᵀ *ᵥ (fun _ => 1)))
  have hy : Lᵀ *ᵥ y = -(Cᵀ *ᵥ (fun _ => 1)) :=
    Matrix.mulVec_backSubst _ (fun _ _ hij => hL hij) (fun i => (hd i).ne')
  let v := failedCholeskyBackSubst L C
  have hzero : (fromRows L C)ᵀ *ᵥ v = 0 := by
    rw [Matrix.transpose_fromRows]
    change fromCols Lᵀ Cᵀ *ᵥ Sum.elim y (fun _ => 1) = 0
    rw [Matrix.fromCols_mulVec_sumElim, hy, neg_add_cancel]
  have hker : (B + δ • vecMulVec e e) *ᵥ v = 0 := by
    rw [hB, ← Matrix.mulVec_mulVec, hzero, Matrix.mulVec_zero]
  have hev : e ⬝ᵥ v = 1 := by
    rw [he]
    change Sum.elim 0 (fun _ : Unit => (1 : ℝ)) ⬝ᵥ Sum.elim y (fun _ => 1) = 1
    rw [sumElim_dotProduct_sumElim]
    simp [dotProduct]
  have hve : v ⬝ᵥ e = 1 := (dotProduct_comm _ _).trans hev
  have houter : vecMulVec e e *ᵥ v = e := by
    rw [Matrix.vecMulVec_mulVec, hev, MulOpposite.op_one, one_smul]
  have hquadratic := congrArg (fun z => v ⬝ᵥ z) hker
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, houter, dotProduct_add,
    dotProduct_smul, hve, smul_eq_mul, mul_one, dotProduct_zero] at hquadratic
  exact ⟨rfl, hker, by linarith⟩

/-- **Equation (7.3.17)** of [conn2000trust], kernel equation on the leading principal block. Let
$L$ be lower triangular of order $n$ with positive diagonal, $c$ a row, $\delta \in \mathbb{R}$,
$e$ the unit vector of the pivot, and $B$ a matrix of order $n + 1$ with
$B + \delta e e^T = [L; c][L; c]^T$. Then there is $v$ with
$$v_{\mathrm{pivot}} = 1, \qquad (B + \delta e e^T) v = 0, \qquad v^T B v = -\delta.$$
-/
theorem failedCholeskyPivotDirection {n : ℕ} {L : Matrix (Fin n) (Fin n) ℝ}
    (hL : L.IsLowerTriangular) (hd : ∀ i, 0 < L i i)
    (C : Matrix Unit (Fin n) ℝ) (δ : ℝ)
    (B : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ)
    (e : Fin n ⊕ Unit → ℝ) (he : e = Sum.elim (0 : Fin n → ℝ) (fun _ : Unit => 1))
    (hB : B + δ • vecMulVec e e = fromRows L C * (fromRows L C)ᵀ) :
    ∃ v : Fin n ⊕ Unit → ℝ, v (Sum.inr ()) = 1 ∧
      (B + δ • vecMulVec e e) *ᵥ v = 0 ∧ v ⬝ᵥ B *ᵥ v = -δ :=
  ⟨failedCholeskyBackSubst L C, failedCholeskyBackSubst_spec hL hd C δ B e he hB⟩

/-- **Section 7.3.7** of [conn2000trust], the correction from the failed pivot. Let $L$ be lower
triangular of order $n$ with positive diagonal, $c$ a row of length $n$, and $d \le c c^T$. Let
$$B = \begin{bmatrix} L L^T & L c^T \\ c L^T & d \end{bmatrix}, \qquad \delta = c c^T - d,$$
and let $e$ be the unit vector of the last coordinate. Then $\delta \ge 0$, and there is $v$
with $v_{\mathrm{last}} = 1$, $(B + \delta e e^T) v = 0$ and $v^T B v = -\delta$.

So the correction is the deficit between the accumulated row square $c c^T$ and the uncorrected
pivot entry $d$. -/
theorem failedCholeskyPivot_correction {n : ℕ} {L : Matrix (Fin n) (Fin n) ℝ}
    (hL : L.IsLowerTriangular) (hd : ∀ i, 0 < L i i)
    (C : Matrix Unit (Fin n) ℝ) (d : ℝ) (hpivot : d ≤ (C * Cᵀ) () ()) :
    let B := fromBlocks (L * Lᵀ) (L * Cᵀ) (C * Lᵀ) (Matrix.of fun _ _ : Unit => d)
    let δ := (C * Cᵀ) () () - d
    let e : Fin n ⊕ Unit → ℝ := Sum.elim (0 : Fin n → ℝ) (fun _ : Unit => 1)
    0 ≤ δ ∧ ∃ v : Fin n ⊕ Unit → ℝ, v (Sum.inr ()) = 1 ∧
      (B + δ • vecMulVec e e) *ᵥ v = 0 ∧ v ⬝ᵥ B *ᵥ v = -δ := by
  dsimp only
  refine ⟨sub_nonneg.mpr hpivot, failedCholeskyPivotDirection hL hd C _ _ _ rfl ?_⟩
  rw [Matrix.transpose_fromRows, Matrix.fromRows_mul_fromCols]
  ext (i | i) (j | j)
  · simp [vecMulVec]
  · cases j
    simp [vecMulVec]
  · cases i
    simp [vecMulVec]
  · cases i
    cases j
    simp [vecMulVec]

/-- **Counterexample** to the full-matrix kernel equation (7.3.17) of [conn2000trust] as printed.
Let
$$B = \begin{bmatrix} -1 & 1 \\ 1 & 1 \end{bmatrix}, \qquad e = \begin{bmatrix} 1 \\ 0
  \end{bmatrix}.$$
Then $(B + e e^T) e = (0, 1)^T$. The correction of the first pivot removes the leading residual,
but the second coordinate of the residual is $1$. -/
theorem failedCholeskyPivot_full_residual_counterexample :
    let B : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 1; 1, 1]
    let e : Fin 2 → ℝ := ![1, 0]
    (B + vecMulVec e e) *ᵥ e = ![0, 1] := by
  dsimp only
  ext i
  fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two, vecMulVec]

/-- **Section 7.3.7** of [conn2000trust] and Algorithm 7.3.4, Steps 3c–d, the Rayleigh lower bound
on the pole. Let $A = \begin{bmatrix} B & C \\ D & F \end{bmatrix}$, where $B$ is the leading
principal block indexed by the first $n$ coordinates and the pivot. Let
$\lambda, \lambda_{\min}, \delta \in \mathbb{R}$, and let $v$ have pivot entry $1$ with
$v^T B v = -\delta$. If
$$(\lambda + \lambda_{\min}) z^T z \le z^T A z \quad \text{for all } z,$$
then
$$\lambda + \frac{\delta}{v^T v} \le -\lambda_{\min}.$$

Here $A = H + \lambda I$, and $\lambda_{\min}$ is a lower bound on the eigenvalues of $H$. The
proof uses the zero extension of $v$, whose Rayleigh quotient for $A$ equals that for $B$, so
the bound holds even when the full residual is nonzero. -/
theorem failedCholeskyPivot_lower_bound {n : ℕ} {ι : Type*} [Fintype ι]
    {B : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ}
    (C : Matrix (Fin n ⊕ Unit) ι ℝ) (D : Matrix ι (Fin n ⊕ Unit) ℝ)
    (F : Matrix ι ι ℝ) {lam lamMin δ : ℝ} {v : Fin n ⊕ Unit → ℝ}
    (hv : v (Sum.inr ()) = 1) (hq : v ⬝ᵥ B *ᵥ v = -δ)
    (hRayleigh : ∀ z, (lam + lamMin) * (z ⬝ᵥ z) ≤
      z ⬝ᵥ fromBlocks B C D F *ᵥ z) :
    lam + δ / (v ⬝ᵥ v) ≤ -lamMin := by
  have hnorm : 0 < v ⬝ᵥ v := by
    have hs : v (Sum.inr ()) ^ 2 ≤ ∑ i, v i ^ 2 :=
      Finset.single_le_sum (fun i _ => sq_nonneg (v i)) (Finset.mem_univ _)
    rw [hv, one_pow] at hs
    have hd : v ⬝ᵥ v = ∑ i, v i ^ 2 := by simp [dotProduct, pow_two]
    rw [hd]
    exact zero_lt_one.trans_le hs
  have hr := hRayleigh (Sum.elim v 0)
  rw [Matrix.fromBlocks_mulVec] at hr
  have hl : Sum.elim v (0 : ι → ℝ) ∘ Sum.inl = v := rfl
  have ht : Sum.elim v (0 : ι → ℝ) ∘ Sum.inr = 0 := rfl
  simp only [hl, ht, Matrix.mulVec_zero, add_zero, sumElim_dotProduct_sumElim,
    zero_dotProduct, hq] at hr
  have hdiv : δ / (v ⬝ᵥ v) ≤ -(lam + lamMin) := by
    apply (div_le_iff₀ hnorm).2
    nlinarith only [hr]
  linarith

end ConnGouldToint.Chapter07

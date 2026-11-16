/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.LeastSquares.Total`.
The exception is `Numlib/Analysis/Matrix/SingularValues` (the Frobenius Eckart–Young–Mirsky
theorem and the interlacing bounds), which is not a candidate and would have to go upstream
first; keep it free of any other dependency on the rest of `Numlib` than other upstreaming
candidates.
-/
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Numlib.Analysis.Matrix.SingularValues

/-!
# Total least squares

Let $A \in \mathbb{K}^{m \times n}$ and $B \in \mathbb{K}^{m \times k}$, with $\mathbb{K}$ either
$\mathbb{R}$ or $\mathbb{C}$, and let $D = \operatorname{diag}(d_1, \dots, d_m)$ and
$T = \operatorname{diag}(t_1, \dots, t_{n+k})$ be nonsingular real diagonal weights. **Total least
squares** (TLS) perturbs both the data matrix and the right-hand sides: it minimizes
$\|D [E \mid R] T\|_F$ subject to $\operatorname{ran}(B + R) \subseteq \operatorname{ran}(A + E)$,
and a TLS solution is an $X$ with $(A + E) X = B + R$ for a minimizing pair $(E, R)$. The
presentation follows [golub2013matrix], §6.3, whose formulation goes back to Golub and Van Loan
(1980).

With $C = D [A \mid B] T$, every feasible perturbation makes $C + D [E \mid R] T$ rank-deficient, so
the small singular values of $C$ bound its size from below. For one right-hand side, a unit vector
$w = [z; \alpha]$ with $\|Cw\| = \sigma_{\min}(C)$ and $\alpha \ne 0$ gives the TLS solution
$x = -T_1 z / (t_{n+1} \alpha)$, where $T_1 = \operatorname{diag}(t_1, \dots, t_n)$; if every such
$w$ has $\alpha = 0$, there is no TLS solution. For $k$ right-hand sides, Theorem 6.3.1 of
[golub2013matrix] states that under the generic condition $\sigma_n(C_1) > \sigma_{n+1}(C)$, with
$C_1$ the first $n$ columns of $C$, the TLS perturbation is unique and the TLS solution is
$X_{TLS} = -T_1 V_{12} V_{22}^{-1} T_2^{-1}$. Finally, the TLS solution minimizes the
orthogonal-regression objective $\psi$ of (6.3.6).

## Main definitions

* `Matrix.tlsWeighted`: the weighted matrix $D [E \mid R] T$.
* `Matrix.IsTLSPerturbation`: $(E, R)$ is a feasible perturbation of least weighted Frobenius norm,
  (6.3.2)–(6.3.3) of [golub2013matrix].
* `Matrix.IsTLSSolution`: $X$ solves $(A + E) X = B + R$ for a TLS perturbation $(E, R)$.
* `Matrix.tlsObjective`: the orthogonal-regression objective $\psi$ of (6.3.6) of [golub2013matrix].

## Main results

* `Matrix.iInf_sq_norm_diagonal_mulVec_sub_hyperplane`: the weighted squared distance from a point
  to a hyperplane.
* `Matrix.isTLSSolution_of_mem_smallest`: with one right-hand side, a unit minimizer
  $w = [z; \alpha]$ of $\|Cw\|$ with $\alpha \ne 0$ gives the TLS solution
  $x = -T_1 z / (t_{n+1} \alpha)$ and the perturbation $-C w w^H$.
* `Matrix.not_isTLSSolution_of_forall_last_eq_zero`: if every unit minimizer has $\alpha = 0$, there
  is no TLS solution.
* `Matrix.tls_single_rhs`: both cases, read off an orthonormal basis of the minimizers, as in
  Algorithm 6.3.1 of [golub2013matrix].
* `Matrix.isUnit_lowerRightBlock_of_lt`: the generic condition $\sigma_n(C_1) > \sigma_{n+1}(C)$
  makes $V_{22}$ invertible.
* `Matrix.isTLSPerturbation_iff`: under the generic condition, $(E, R)$ is a TLS perturbation if and
  only if $C + D [E \mid R] T$ is the rank-$n$ truncation of the SVD of $C$.
* `Matrix.existsUnique_isTLSPerturbation`: under the generic condition, the TLS perturbation is
  unique, Theorem 6.3.1 of [golub2013matrix].
* `Matrix.isTLSSolution_iff_eq`: under the generic condition, the unique TLS solution is
  $X_{TLS} = -T_1 V_{12} V_{22}^{-1} T_2^{-1}$, Theorem 6.3.1 of [golub2013matrix].
* `Matrix.isMinOn_tlsObjective`: the TLS solution minimizes $\psi$.

## Implementation notes

* The single right-hand side needs no singular-value theory beyond the least stretch
  $\sigma_{\min}(C) \|w\| \le \|Cw\|$ (`Matrix.iInf_colSingularValues_mul_norm_le`), which is
  attained (`Matrix.exists_norm_eq_iInf_colSingularValues`). A feasible perturbation $\Delta C$ has
  a unit null vector $w'$ of $C + \Delta C$ with nonzero last entry, and $\|\Delta C\|_F \ge
  \|\Delta C w'\| = \|C w'\| \ge \sigma_{\min}(C)$. Conversely, $\Delta C = -C w w^H$ is feasible
  for every unit vector $w$ with nonzero last entry, and $\|\Delta C\|_F = \|Cw\|$.
* The case of several right-hand sides rests on the Frobenius-norm Eckart–Young–Mirsky theorem of
  `Numlib.Analysis.Matrix.SingularValues`.
* Several right-hand sides are stated on `Fin` indices, with the columns `Fin n ⊕ Fin k` of $C$
  reindexed to `Fin (n + k)` for the SVD. Singular values are indexed from $0$, so the generic
  condition $\sigma_{n+1}(C) < \sigma_n(C_1)$ is `σ n < C₁.sortedSingularValues (n - 1)`. One
  right-hand side is the column type `Unit`, and its entry is `Sum.inr ()`.
-/

open scoped Matrix

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### The weighted problem -/

section Defs

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k] [DecidableEq m] [DecidableEq n]
  [DecidableEq k]

/-- Let $d \in \mathbb{R}^m$ and $t \in \mathbb{R}^{n + k}$ be weights, $D = \operatorname{diag}(d)$
and $T = \operatorname{diag}(t)$. For $E \in \mathbb{K}^{m \times n}$ and
$R \in \mathbb{K}^{m \times k}$, the **weighted matrix** of the total least-squares problem is
$$D [E \mid R] T \in \mathbb{K}^{m \times (n + k)}.$$

The columns are indexed by `n ⊕ k`. -/
noncomputable def tlsWeighted (d : m → ℝ) (t : n ⊕ k → ℝ) (E : Matrix m n 𝕜)
    (R : Matrix m k 𝕜) : Matrix m (n ⊕ k) 𝕜 :=
  diagonal (fun i => (d i : 𝕜)) * fromCols E R * diagonal (fun j => (t j : 𝕜))

open scoped Matrix.Norms.Frobenius in
/-- Let $A \in \mathbb{K}^{m \times n}$, $B \in \mathbb{K}^{m \times k}$, and let $d$, $t$ be real
weights. A pair $(E, R)$ with $E \in \mathbb{K}^{m \times n}$ and
$R \in \mathbb{K}^{m \times k}$ is a **total-least-squares perturbation** if it is feasible,
$\operatorname{ran}(B + R) \subseteq \operatorname{ran}(A + E)$, and
$$\|D [E \mid R] T\|_F \le \|D [E' \mid R'] T\|_F$$
for every feasible pair $(E', R')$. This is (6.3.2)–(6.3.3) of [golub2013matrix]; the problem
(6.3.2) is the case $d = 1$, $t = 1$, $k = 1$. -/
structure IsTLSPerturbation (d : m → ℝ) (t : n ⊕ k → ℝ) (A : Matrix m n 𝕜) (B : Matrix m k 𝕜)
    (E : Matrix m n 𝕜) (R : Matrix m k 𝕜) : Prop where
  /-- The perturbation is feasible: $\operatorname{ran}(B + R) \subseteq \operatorname{ran}(A + E)$.
  -/
  range_le : LinearMap.range (B + R).mulVecLin ≤ LinearMap.range (A + E).mulVecLin
  /-- No feasible perturbation has a smaller weighted Frobenius norm. -/
  norm_le : ∀ (E' : Matrix m n 𝕜) (R' : Matrix m k 𝕜),
    LinearMap.range (B + R').mulVecLin ≤ LinearMap.range (A + E').mulVecLin →
      ‖tlsWeighted d t E R‖ ≤ ‖tlsWeighted d t E' R'‖

/-- Let $A \in \mathbb{K}^{m \times n}$, $B \in \mathbb{K}^{m \times k}$, and let $d$, $t$ be real
weights. A matrix $X \in \mathbb{K}^{n \times k}$ is a **total-least-squares solution** if
$(A + E) X = B + R$ for some TLS perturbation $(E, R)$. This is the definition after (6.3.3) of
[golub2013matrix]. -/
def IsTLSSolution (d : m → ℝ) (t : n ⊕ k → ℝ) (A : Matrix m n 𝕜) (B : Matrix m k 𝕜)
    (X : Matrix n k 𝕜) : Prop :=
  ∃ E R, IsTLSPerturbation d t A B E R ∧ (A + E) * X = B + R

/-- The weighted matrix is additive: $D [A + E \mid B + R] T = D [A \mid B] T + D [E \mid R] T$. -/
theorem tlsWeighted_add (d : m → ℝ) (t : n ⊕ k → ℝ) (A E : Matrix m n 𝕜) (B R : Matrix m k 𝕜) :
    tlsWeighted d t (A + E) (B + R) = tlsWeighted d t A B + tlsWeighted d t E R := by
  have : fromCols (A + E) (B + R) = fromCols A B + fromCols E R := by
    ext i (j | j) <;> simp
  rw [tlsWeighted, this, Matrix.mul_add, Matrix.add_mul]
  rfl

/-- The weighted matrix acts on a vector $v$ by $D [E \mid R] T v = D ([E \mid R] (T v))$, written
entrywise. -/
theorem tlsWeighted_mulVec (d : m → ℝ) (t : n ⊕ k → ℝ) (E : Matrix m n 𝕜) (R : Matrix m k 𝕜)
    (v : n ⊕ k → 𝕜) (i : m) :
    (tlsWeighted d t E R *ᵥ v) i =
      d i * ((E *ᵥ fun j => t (Sum.inl j) * v (Sum.inl j)) i +
        (R *ᵥ fun j => t (Sum.inr j) * v (Sum.inr j)) i) := by
  rw [tlsWeighted, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_diagonal, fromCols_mulVec]
  have e1 : ((diagonal fun j => (t j : 𝕜)) *ᵥ v) ∘ Sum.inl =
      fun j => (t (Sum.inl j) : 𝕜) * v (Sum.inl j) := funext fun j => mulVec_diagonal _ _ _
  have e2 : ((diagonal fun j => (t j : 𝕜)) *ᵥ v) ∘ Sum.inr =
      fun j => (t (Sum.inr j) : 𝕜) * v (Sum.inr j) := funext fun j => mulVec_diagonal _ _ _
  rw [Pi.add_apply, e1, e2]

/-- For nonzero weights, every matrix $M \in \mathbb{K}^{m \times (n + k)}$ is $D [E \mid R] T$ for
some $E$ and $R$, namely the column blocks of $D^{-1} M T^{-1}$. -/
theorem exists_tlsWeighted_eq {d : m → ℝ} {t : n ⊕ k → ℝ} (hd : ∀ i, d i ≠ 0)
    (ht : ∀ j, t j ≠ 0) (M : Matrix m (n ⊕ k) 𝕜) : ∃ E R, tlsWeighted d t E R = M := by
  have hd' : ∀ i, (d i : 𝕜) ≠ 0 := fun i => RCLike.ofReal_ne_zero.2 (hd i)
  have ht' : ∀ j, (t j : 𝕜) ≠ 0 := fun j => RCLike.ofReal_ne_zero.2 (ht j)
  set ER : Matrix m (n ⊕ k) 𝕜 :=
    diagonal (fun i => (d i : 𝕜)⁻¹) * M * diagonal (fun j => (t j : 𝕜)⁻¹)
  refine ⟨ER.toCols₁, ER.toCols₂, ?_⟩
  rw [tlsWeighted, fromCols_toCols]
  simp only [ER, ← Matrix.mul_assoc, diagonal_mul_diagonal]
  rw [Matrix.mul_assoc, diagonal_mul_diagonal]
  simp [mul_inv_cancel₀ (hd' _), inv_mul_cancel₀ (ht' _)]

/-- For nonzero weights, $D [E \mid R] T$ determines $E$ and $R$. -/
theorem tlsWeighted_injective {d : m → ℝ} {t : n ⊕ k → ℝ} (hd : ∀ i, d i ≠ 0)
    (ht : ∀ j, t j ≠ 0) {E E' : Matrix m n 𝕜} {R R' : Matrix m k 𝕜}
    (h : tlsWeighted d t E R = tlsWeighted d t E' R') : E = E' ∧ R = R' := by
  have hd' : ∀ i, (d i : 𝕜) ≠ 0 := fun i => RCLike.ofReal_ne_zero.2 (hd i)
  have ht' : ∀ j, (t j : 𝕜) ≠ 0 := fun j => RCLike.ofReal_ne_zero.2 (ht j)
  refine fromCols_inj ?_
  ext i j
  have := congrFun (congrFun h i) j
  simp only [tlsWeighted, mul_diagonal, diagonal_mul] at this
  exact mul_left_cancel₀ (hd' i) (mul_right_cancel₀ (ht' j) this)

end Defs

/-! ### The weighted distance to a hyperplane -/

section Hyperplane

/-- Let $t \in \mathbb{R}^\iota$ have nonzero entries, $T = \operatorname{diag}(t)$, let
$\nu \in \mathbb{R}^\iota$ be nonzero, and let $q \in \mathbb{R}^\iota$. Then the weighted
squared distance from $q$ to the hyperplane $\nu^T w = 0$ is
$$\inf_{\nu^T w = 0} \|T (q - w)\|_2^2 = \frac{(\nu^T q)^2}{\sum_j (\nu_j / t_j)^2},$$
and the infimum is attained. This is the distance $\delta_i$ of §6.3.3 of [golub2013matrix],
measured in the norm $\|z\| = \|Tz\|_2$.

The infimum is attained at $w = q - \lambda T^{-2} \nu$ with
$\lambda = (\nu^T q) / \sum_j (\nu_j / t_j)^2$. The lower bound is the Cauchy–Schwarz inequality
for $\nu^T q = \sum_j (\nu_j / t_j) (t_j (q_j - w_j))$. With $\nu = [x; -1]$ and
$q = [a_i; b_i]$, it gives $\delta_i = |a_i^T x - b_i|^2 / (x^T T_1^{-2} x + t_{n+1}^{-2})$. -/
theorem iInf_sq_norm_diagonal_mulVec_sub_hyperplane {ι : Type*} [Fintype ι] [DecidableEq ι]
    {t : ι → ℝ} (ht : ∀ j, t j ≠ 0) {ν : ι → ℝ} (hν : ν ≠ 0) (q : ι → ℝ) :
    (⨅ w : {w : ι → ℝ // ν ⬝ᵥ w = 0},
        ‖(WithLp.toLp 2 (diagonal t *ᵥ (q - w.1)) : EuclideanSpace ℝ ι)‖ ^ 2) =
      (ν ⬝ᵥ q) ^ 2 / ∑ j, (ν j / t j) ^ 2 ∧
    ∃ w : ι → ℝ, ν ⬝ᵥ w = 0 ∧
      ‖(WithLp.toLp 2 (diagonal t *ᵥ (q - w)) : EuclideanSpace ℝ ι)‖ ^ 2 =
        (ν ⬝ᵥ q) ^ 2 / ∑ j, (ν j / t j) ^ 2 := by
  have hnorm : ∀ w : ι → ℝ, ‖(WithLp.toLp 2 (diagonal t *ᵥ (q - w)) : EuclideanSpace ℝ ι)‖ ^ 2 =
      ∑ j, (t j * (q j - w j)) ^ 2 := fun w => by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.sum_congr rfl fun j _ => by
      rw [Real.norm_eq_abs, sq_abs]
      simp [mulVec_diagonal]
  set s := ∑ j, (ν j / t j) ^ 2 with hs
  have hs0 : 0 < s := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hν
    exact lt_of_lt_of_le (by have := div_ne_zero hj (ht j); positivity)
      (Finset.single_le_sum (fun i _ => sq_nonneg (ν i / t i)) (Finset.mem_univ j))
  -- the lower bound
  have hlow : ∀ w : ι → ℝ, ν ⬝ᵥ w = 0 → (ν ⬝ᵥ q) ^ 2 / s ≤ ∑ j, (t j * (q j - w j)) ^ 2 :=
    fun w hw => by
    have e : ν ⬝ᵥ q = ∑ j, ν j / t j * (t j * (q j - w j)) := by
      have : ν ⬝ᵥ q = ν ⬝ᵥ (q - w) := by rw [dotProduct_sub, hw, sub_zero]
      rw [this, dotProduct]
      exact Finset.sum_congr rfl fun j _ => by
        rw [Pi.sub_apply]
        field_simp [ht j]
    rw [div_le_iff₀ hs0, e, mul_comm]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  -- the minimizer
  set lam := (ν ⬝ᵥ q) / s
  set w₀ : ι → ℝ := fun j => q j - lam * ν j / t j ^ 2
  have hw₀ : ν ⬝ᵥ w₀ = 0 := by
    have : ν ⬝ᵥ w₀ = ν ⬝ᵥ q - lam * s := by
      simp only [w₀, dotProduct, mul_sub, Finset.sum_sub_distrib, hs, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by field_simp [ht j]
    rw [this, div_mul_cancel₀ _ hs0.ne', sub_self]
  have hval : ∑ j, (t j * (q j - w₀ j)) ^ 2 = (ν ⬝ᵥ q) ^ 2 / s := by
    have : ∑ j, (t j * (q j - w₀ j)) ^ 2 = lam ^ 2 * s := by
      rw [hs, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by
        simp only [w₀]
        field_simp [ht j]
        ring
    rw [this, div_pow, sq s]
    field_simp
  refine ⟨le_antisymm ?_ ?_, w₀, hw₀, by rw [hnorm, hval]⟩
  · refine (ciInf_le ⟨0, fun _ ⟨w, hw⟩ => hw ▸ sq_nonneg _⟩ ⟨w₀, hw₀⟩).trans_eq ?_
    rw [hnorm, hval]
  · have : Nonempty {w : ι → ℝ // ν ⬝ᵥ w = 0} := ⟨⟨0, by simp⟩⟩
    exact le_ciInf fun w => by rw [hnorm]; exact hlow w.1 w.2

end Hyperplane

/-! ### One right-hand side -/

section SingleRHS

open scoped Matrix.Norms.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  {d : m → ℝ} {t : n ⊕ Unit → ℝ} {A : Matrix m n 𝕜} {b : m → 𝕜}

/-- If $\operatorname{ran}(b + r) \subseteq \operatorname{ran}(A + E)$, then $C + D [E \mid r] T$
annihilates a unit vector with nonzero last entry, namely $T^{-1} [x; -1]$ normalized, for
$(A + E) x = b + r$, as in (6.3.5) of [golub2013matrix]. -/
private theorem exists_null_of_range_le (ht : ∀ j, t j ≠ 0)
    {E : Matrix m n 𝕜} {R : Matrix m Unit 𝕜}
    (h : LinearMap.range (replicateCol Unit b + R).mulVecLin ≤ LinearMap.range (A + E).mulVecLin) :
    ∃ w : n ⊕ Unit → 𝕜, ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (n ⊕ Unit))‖ = 1 ∧
      w (Sum.inr ()) ≠ 0 ∧
      (tlsWeighted d t A (replicateCol Unit b) + tlsWeighted d t E R) *ᵥ w = 0 := by
  have ht' : ∀ j, (t j : 𝕜) ≠ 0 := fun j => RCLike.ofReal_ne_zero.2 (ht j)
  obtain ⟨x', hx'⟩ := h ⟨fun _ => 1, rfl⟩
  simp only [mulVecLin_apply] at hx'
  set v : n ⊕ Unit → 𝕜 := Sum.elim (fun j => x' j / (t (Sum.inl j) : 𝕜))
    (fun _ => -1 / (t (Sum.inr ()) : 𝕜)) with hv
  have hv0 : v (Sum.inr ()) ≠ 0 := by
    simp [hv, ht' (Sum.inr ())]
  have hnull : (tlsWeighted d t A (replicateCol Unit b) + tlsWeighted d t E R) *ᵥ v = 0 := by
    rw [← tlsWeighted_add]
    funext i
    rw [tlsWeighted_mulVec]
    have e1 : (fun j => (t (Sum.inl j) : 𝕜) * v (Sum.inl j)) = x' := funext fun j => by
      simp [hv, mul_div_cancel₀ _ (ht' (Sum.inl j))]
    have e2 : (fun j : Unit => (t (Sum.inr j) : 𝕜) * v (Sum.inr j)) = -fun _ => 1 :=
      funext fun j => by simp [hv, mul_div_cancel₀ _ (ht' (Sum.inr ()))]
    rw [e1, e2, hx', mulVec_neg, Pi.neg_apply, add_neg_cancel, mul_zero]
    rfl
  have hvn : ‖(WithLp.toLp 2 v : EuclideanSpace 𝕜 (n ⊕ Unit))‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro h0
    apply hv0
    have := congrArg (fun z : EuclideanSpace 𝕜 (n ⊕ Unit) => z (Sum.inr ())) h0
    simpa using this
  refine ⟨(‖(WithLp.toLp 2 v : EuclideanSpace 𝕜 (n ⊕ Unit))‖⁻¹ : 𝕜) • v, ?_, ?_, ?_⟩
  · rw [WithLp.toLp_smul, norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm,
      inv_mul_cancel₀ hvn]
  · simp [hv0, hvn]
  · rw [mulVec_smul, hnull, smul_zero]

/-- A feasible perturbation $\Delta C = D [E \mid r] T$ has a unit vector $w$ with nonzero last
entry and $\|Cw\| \le \|\Delta C\|_F$, because $Cw = -\Delta C w$. -/
private theorem exists_norm_mulVec_le_of_range_le (ht : ∀ j, t j ≠ 0)
    {E : Matrix m n 𝕜} {R : Matrix m Unit 𝕜}
    (h : LinearMap.range (replicateCol Unit b + R).mulVecLin ≤ LinearMap.range (A + E).mulVecLin) :
    ∃ w : n ⊕ Unit → 𝕜, ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (n ⊕ Unit))‖ = 1 ∧
      w (Sum.inr ()) ≠ 0 ∧
      ‖(WithLp.toLp 2 (tlsWeighted d t A (replicateCol Unit b) *ᵥ w) : EuclideanSpace 𝕜 m)‖ ≤
        ‖tlsWeighted d t E R‖ := by
  obtain ⟨w, hw, hα, hnull⟩ := exists_null_of_range_le (A := A) ht h
  refine ⟨w, hw, hα, ?_⟩
  rw [add_mulVec, add_eq_zero_iff_eq_neg] at hnull
  rw [hnull, WithLp.toLp_neg, norm_neg]
  exact (frobenius_norm_mulVec_le _ w).trans_eq (by rw [hw, mul_one])

/-- The least singular value $\sigma_{\min}(C)$ is at most the Frobenius norm of every feasible
perturbation. -/
private theorem iInf_colSingularValues_le_of_range_le (ht : ∀ j, t j ≠ 0)
    {E : Matrix m n 𝕜} {R : Matrix m Unit 𝕜}
    (h : LinearMap.range (replicateCol Unit b + R).mulVecLin ≤ LinearMap.range (A + E).mulVecLin) :
    ⨅ j, (tlsWeighted d t A (replicateCol Unit b)).colSingularValues j ≤ ‖tlsWeighted d t E R‖ := by
  obtain ⟨w, hw, -, hle⟩ := exists_norm_mulVec_le_of_range_le (A := A) ht h
  have := iInf_colSingularValues_mul_norm_le (tlsWeighted d t A (replicateCol Unit b))
    (WithLp.toLp 2 w)
  rw [hw, mul_one, toEuclideanLin_toLp] at this
  exact this.trans hle

/-- For a unit vector $w = [z; \alpha]$ with $\alpha \ne 0$, the pair $(E, r)$ with
$D [E \mid r] T = -C w w^H$ satisfies $(A + E) x = b + r$ for $x = -T_1 z / (t_{n+1} \alpha)$. -/
private theorem exists_rankOne_perturbation (hd : ∀ i, d i ≠ 0) (ht : ∀ j, t j ≠ 0)
    {w : n ⊕ Unit → 𝕜} (hw : ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (n ⊕ Unit))‖ = 1)
    (hα : w (Sum.inr ()) ≠ 0) :
    ∃ (E : Matrix m n 𝕜) (R : Matrix m Unit 𝕜),
      tlsWeighted d t E R = -vecMulVec (tlsWeighted d t A (replicateCol Unit b) *ᵥ w) (star w) ∧
      (A + E) * replicateCol Unit (fun j => -((t (Sum.inl j) : 𝕜) * w (Sum.inl j)) /
        ((t (Sum.inr ()) : 𝕜) * w (Sum.inr ()))) = replicateCol Unit b + R := by
  have hd' : ∀ i, (d i : 𝕜) ≠ 0 := fun i => RCLike.ofReal_ne_zero.2 (hd i)
  have ht' : ∀ j, (t j : 𝕜) ≠ 0 := fun j => RCLike.ofReal_ne_zero.2 (ht j)
  set C := tlsWeighted d t A (replicateCol Unit b)
  set ΔC := -vecMulVec (C *ᵥ w) (star w)
  obtain ⟨E, R, hER⟩ := exists_tlsWeighted_eq hd ht ΔC
  refine ⟨E, R, hER, ?_⟩
  -- `C + ΔC` annihilates `w`
  have hww : star w ⬝ᵥ w = 1 := by rw [star_dotProduct_self, hw]; simp
  have hnull : tlsWeighted d t (A + E) (replicateCol Unit b + R) *ᵥ w = 0 := by
    rw [tlsWeighted_add, hER, add_mulVec]
    funext i
    simp only [ΔC, neg_mulVec, Pi.add_apply, Pi.neg_apply, vecMulVec_mulVec, Pi.smul_apply,
      op_smul_eq_mul, hww, mul_one, Pi.zero_apply]
    exact add_neg_cancel _
  set c : 𝕜 := (t (Sum.inr ()) : 𝕜) * w (Sum.inr ())
  have hc : c ≠ 0 := mul_ne_zero (ht' _) hα
  ext i u
  have hi := congrFun hnull i
  rw [tlsWeighted_mulVec, Pi.zero_apply, mul_eq_zero, or_iff_right (hd' i)] at hi
  have hB : ((replicateCol Unit b + R) *ᵥ fun j => (t (Sum.inr j) : 𝕜) * w (Sum.inr j)) i
      = (replicateCol Unit b + R) i () * c := by
    simp [mulVec, dotProduct, c]
  rw [hB] at hi
  have hA : ((A + E) * replicateCol Unit (fun j => -((t (Sum.inl j) : 𝕜) *
      w (Sum.inl j)) / c)) i u = -(((A + E) *ᵥ fun j => (t (Sum.inl j) : 𝕜) *
        w (Sum.inl j)) i) / c := by
    simp only [Matrix.mul_apply, replicateCol_apply, mulVec, dotProduct, neg_div, Finset.sum_div,
      ← Finset.sum_neg_distrib, mul_div_assoc, mul_neg]
  rw [hA, eq_neg_of_add_eq_zero_left hi, neg_neg, mul_div_cancel_right₀ _ hc]

/-- Let $A \in \mathbb{K}^{m \times n}$, $b \in \mathbb{K}^m$, and let the weights $d$, $t$ be
nonzero, with $C = D [A \mid b] T$ and $T_1 = \operatorname{diag}(t_1, \dots, t_n)$. Let
$w = [z; \alpha] \in \mathbb{K}^{n + 1}$ be a unit vector with $\|Cw\| = \sigma_{\min}(C)$ and
$\alpha \ne 0$. Then there is a TLS perturbation $(E_0, r_0)$ with
$$D [E_0 \mid r_0] T = -C w w^H \quad \text{and} \quad (A + E_0) x = b + r_0, \qquad x =
  -\frac{T_1 z}{t_{n+1} \alpha}.$$
So $x$ is a TLS solution. This is §6.3.2 of [golub2013matrix], which allows repeated smallest
singular values.

An example of $w$ is the last column of $V(:, n+1-p : n+1) \tilde Q$ in the source. The
perturbation is feasible, because $(C - C w w^H) w = 0$, and $\|C w w^H\|_F = \sigma_{\min}(C)$.
Every feasible perturbation $\Delta C$ has a unit null vector $w'$ of $C + \Delta C$, and
$\|\Delta C\|_F \ge \|\Delta C w'\| = \|C w'\| \ge \sigma_{\min}(C)$. The number
$\sigma_{\min}(C)$ is the infimum of `Matrix.colSingularValues`, and the right-hand side is the
column `replicateCol Unit b`. -/
theorem isTLSSolution_of_mem_smallest (hd : ∀ i, d i ≠ 0) (ht : ∀ j, t j ≠ 0)
    {w : n ⊕ Unit → 𝕜} (hw : ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (n ⊕ Unit))‖ = 1)
    (hmin : ‖(WithLp.toLp 2 (tlsWeighted d t A (replicateCol Unit b) *ᵥ w) :
      EuclideanSpace 𝕜 m)‖ = ⨅ j, (tlsWeighted d t A (replicateCol Unit b)).colSingularValues j)
    (hα : w (Sum.inr ()) ≠ 0) :
    ∃ E R, IsTLSPerturbation d t A (replicateCol Unit b) E R ∧
      (A + E) * replicateCol Unit (fun j => -((t (Sum.inl j) : 𝕜) * w (Sum.inl j)) /
        ((t (Sum.inr ()) : 𝕜) * w (Sum.inr ()))) = replicateCol Unit b + R ∧
      tlsWeighted d t E R = -vecMulVec (tlsWeighted d t A (replicateCol Unit b) *ᵥ w) (star w) := by
  obtain ⟨E, R, hER, hsol⟩ := exists_rankOne_perturbation (A := A) (b := b) hd ht hw hα
  refine ⟨E, R, ⟨?_, fun E' R' h' => ?_⟩, hsol, hER⟩
  · rw [← hsol, mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  · rw [hER, norm_neg, frobenius_norm_vecMulVec_star, hw, mul_one, hmin]
    exact iInf_colSingularValues_le_of_range_le ht h'

/-- Under the hypotheses of `Matrix.isTLSSolution_of_mem_smallest`, the one-column matrix $X = [x]$
with $x = -T_1 z / (t_{n+1} \alpha)$ is a TLS solution. -/
theorem isTLSSolution_of_mem_smallest' (hd : ∀ i, d i ≠ 0) (ht : ∀ j, t j ≠ 0)
    {w : n ⊕ Unit → 𝕜} (hw : ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (n ⊕ Unit))‖ = 1)
    (hmin : ‖(WithLp.toLp 2 (tlsWeighted d t A (replicateCol Unit b) *ᵥ w) :
      EuclideanSpace 𝕜 m)‖ = ⨅ j, (tlsWeighted d t A (replicateCol Unit b)).colSingularValues j)
    (hα : w (Sum.inr ()) ≠ 0) :
    IsTLSSolution d t A (replicateCol Unit b) (replicateCol Unit fun j =>
      -((t (Sum.inl j) : 𝕜) * w (Sum.inl j)) / ((t (Sum.inr ()) : 𝕜) * w (Sum.inr ()))) :=
  let ⟨E, R, h₁, h₂, _⟩ := isTLSSolution_of_mem_smallest hd ht hw hmin hα
  ⟨E, R, h₁, h₂⟩

/-- Let $A \in \mathbb{K}^{m \times n}$, $b \in \mathbb{K}^m$, let the weights $d$, $t$ be nonzero,
and let $C = D [A \mid b] T$. If every unit vector $w$ with $\|Cw\| = \sigma_{\min}(C)$ has last
entry $0$, then the TLS problem has no solution. This is the statement of §6.3.2 of
[golub2013matrix] that the TLS problem has no solution if $\alpha = 0$.

A TLS perturbation $\Delta C$ would satisfy $\|\Delta C\|_F \le \|Cw\|$ for every unit vector
$w$ with nonzero last entry, because the rank-one perturbations are feasible. Tilting a
minimizer $w^*$, whose last entry is $0$, towards the last unit vector gives
$\|\Delta C\|_F \le \sigma_{\min}(C)$. Its null vector $w'$ has nonzero last entry and
$\sigma_{\min}(C) \le \|C w'\| \le \|\Delta C\|_F$, which forces $\|C w'\| = \sigma_{\min}(C)$,
a contradiction. -/
theorem not_isTLSSolution_of_forall_last_eq_zero (hd : ∀ i, d i ≠ 0) (ht : ∀ j, t j ≠ 0)
    (h : ∀ w : n ⊕ Unit → 𝕜, ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (n ⊕ Unit))‖ = 1 →
      ‖(WithLp.toLp 2 (tlsWeighted d t A (replicateCol Unit b) *ᵥ w) : EuclideanSpace 𝕜 m)‖ =
        ⨅ j, (tlsWeighted d t A (replicateCol Unit b)).colSingularValues j → w (Sum.inr ()) = 0) :
    ¬ ∃ X, IsTLSSolution d t A (replicateCol Unit b) X := by
  rintro ⟨X, E, R, hP, -⟩
  set C := tlsWeighted d t A (replicateCol Unit b)
  set σmin := ⨅ j, C.colSingularValues j
  have hnrm : ∀ w : n ⊕ Unit → 𝕜, ‖(WithLp.toLp 2 (C *ᵥ w) : EuclideanSpace 𝕜 m)‖ =
      ‖toEuclideanLin C (WithLp.toLp 2 w)‖ := fun w => by rw [toEuclideanLin_toLp]
  -- the upper bound `‖ΔC‖_F ≤ σ_min`
  have hup : ‖tlsWeighted d t E R‖ ≤ σmin := by
    obtain ⟨x, hx, hCx⟩ := exists_norm_eq_iInf_colSingularValues C
    set w₀ : n ⊕ Unit → 𝕜 := WithLp.ofLp x
    have hw₀ : ‖(WithLp.toLp 2 w₀ : EuclideanSpace 𝕜 (n ⊕ Unit))‖ = 1 := hx
    have hCw₀ : ‖(WithLp.toLp 2 (C *ᵥ w₀) : EuclideanSpace 𝕜 m)‖ = σmin := by
      rw [hnrm]; exact hCx
    have hlast : w₀ (Sum.inr ()) = 0 := h w₀ hw₀ hCw₀
    set e : n ⊕ Unit → 𝕜 := Pi.single (Sum.inr ()) 1
    set c := ‖(WithLp.toLp 2 (C *ᵥ e) : EuclideanSpace 𝕜 m)‖
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    set ε : ℝ := δ / (c + 1) with hε
    have hε0 : 0 < ε := div_pos hδ (by positivity)
    set u : n ⊕ Unit → 𝕜 := w₀ + (ε : 𝕜) • e
    have hu_inl : ∀ j, u (Sum.inl j) = w₀ (Sum.inl j) := fun j => by simp [u, e]
    have hu_inr : u (Sum.inr ()) = (ε : 𝕜) := by
      change w₀ (Sum.inr ()) + (ε : 𝕜) • (Pi.single (Sum.inr ()) (1 : 𝕜) : n ⊕ Unit → 𝕜)
        (Sum.inr ()) = ε
      rw [hlast, zero_add, Pi.single_eq_same, smul_eq_mul, mul_one]
    have hsplit : ∀ z : n ⊕ Unit → 𝕜, ‖(WithLp.toLp 2 z : EuclideanSpace 𝕜 (n ⊕ Unit))‖ ^ 2 =
        ∑ j : n, ‖z (Sum.inl j)‖ ^ 2 + ‖z (Sum.inr ())‖ ^ 2 := fun z => by
      rw [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]
      simp
    have hu2 : ‖(WithLp.toLp 2 u : EuclideanSpace 𝕜 (n ⊕ Unit))‖ ^ 2 = 1 + ε ^ 2 := by
      have h0 : ‖(WithLp.toLp 2 w₀ : EuclideanSpace 𝕜 (n ⊕ Unit))‖ ^ 2 = 1 := by
        rw [hw₀, one_pow]
      rw [hsplit] at h0 ⊢
      rw [hlast, norm_zero, zero_pow two_ne_zero, add_zero] at h0
      rw [hu_inr, RCLike.norm_ofReal, sq_abs, Finset.sum_congr rfl fun j _ => by rw [hu_inl j],
        h0]
    have hu1 : 1 ≤ ‖(WithLp.toLp 2 u : EuclideanSpace 𝕜 (n ⊕ Unit))‖ := by
      refine (one_le_sq_iff_one_le_abs _).1 ?_ |>.trans_eq (abs_of_nonneg (norm_nonneg _))
      rw [hu2]; nlinarith
    have hun : ‖(WithLp.toLp 2 u : EuclideanSpace 𝕜 (n ⊕ Unit))‖ ≠ 0 := by linarith
    set w := (‖(WithLp.toLp 2 u : EuclideanSpace 𝕜 (n ⊕ Unit))‖⁻¹ : 𝕜) • u
    have hw : ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (n ⊕ Unit))‖ = 1 := by
      rw [WithLp.toLp_smul, norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm,
        inv_mul_cancel₀ hun]
    have hα : w (Sum.inr ()) ≠ 0 := by
      have e1 : w (Sum.inr ()) =
          (‖(WithLp.toLp 2 u : EuclideanSpace 𝕜 (n ⊕ Unit))‖⁻¹ : 𝕜) * (ε : 𝕜) := by
        rw [← hu_inr]
        rfl
      rw [e1]
      exact mul_ne_zero (inv_ne_zero (RCLike.ofReal_ne_zero.2 hun))
        (RCLike.ofReal_ne_zero.2 hε0.ne')
    obtain ⟨E', R', hE', hsol'⟩ := exists_rankOne_perturbation (A := A) (b := b) hd ht hw hα
    have hfeas : LinearMap.range (replicateCol Unit b + R').mulVecLin ≤
        LinearMap.range (A + E').mulVecLin := by
      rw [← hsol', mulVecLin_mul]
      exact LinearMap.range_comp_le_range _ _
    calc ‖tlsWeighted d t E R‖ ≤ ‖tlsWeighted d t E' R'‖ := hP.norm_le E' R' hfeas
      _ = ‖(WithLp.toLp 2 (C *ᵥ w) : EuclideanSpace 𝕜 m)‖ := by
          rw [hE', norm_neg, frobenius_norm_vecMulVec_star, hw, mul_one]
      _ ≤ ‖(WithLp.toLp 2 (C *ᵥ u) : EuclideanSpace 𝕜 m)‖ := by
          rw [show w = (‖(WithLp.toLp 2 u : EuclideanSpace 𝕜 (n ⊕ Unit))‖⁻¹ : 𝕜) • u from rfl,
            mulVec_smul, WithLp.toLp_smul, norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm]
          exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ hu1)
      _ ≤ σmin + ε * c := by
          rw [show u = w₀ + (ε : 𝕜) • e from rfl, mulVec_add, mulVec_smul, WithLp.toLp_add,
            WithLp.toLp_smul, ← hCw₀]
          refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
          rw [norm_smul, RCLike.norm_ofReal, abs_of_pos hε0]
      _ ≤ σmin + δ := by
          have : ε * c ≤ δ := by
            rw [hε, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
            nlinarith
          linarith
  -- the lower bound, with a null vector whose last entry does not vanish
  obtain ⟨w', hw', hα', hle'⟩ := exists_norm_mulVec_le_of_range_le (A := A) ht hP.range_le
  have hge : σmin ≤ ‖(WithLp.toLp 2 (C *ᵥ w') : EuclideanSpace 𝕜 m)‖ := by
    have := iInf_colSingularValues_mul_norm_le C (WithLp.toLp 2 w')
    rwa [hw', mul_one, ← hnrm] at this
  exact hα' (h w' hw' (le_antisymm (hle'.trans hup) hge))

/-- Let $A \in \mathbb{K}^{m \times n}$, $b \in \mathbb{K}^m$, let the weights $d$, $t$ be nonzero,
and let $C = D [A \mid b] T$. Let $W \in \mathbb{K}^{(n + 1) \times p}$ have orthonormal
columns, $W^H W = I$, whose span is exactly the set of $w$ with
$\|Cw\| = \sigma_{\min}(C) \|w\|$. Let $Q \in \mathbb{K}^{p \times p}$ be unitary such that the
last row of $WQ$ is zero outside the column $l$, so that
$$WQ = \begin{bmatrix} W' & z \\ 0 & \alpha \end{bmatrix}.$$
Then (a) $|\alpha|$ is the largest absolute value of the last entry of a unit vector of the
span: $|(Wy)_{n+1}| \le |\alpha|$ for every unit vector $y \in \mathbb{K}^p$; (b) if
$\alpha = 0$, the TLS problem has no solution; (c) if $\alpha \ne 0$, there is a TLS
perturbation $(E_0, r_0)$ with $D [E_0 \mid r_0] T = -C w w^H$ for the unit vector
$w = (WQ)(:, l)$, and $x = -T_1 z / (t_{n+1} \alpha)$ satisfies $(A + E_0) x = b + r_0$. This is
Algorithm 6.3.1 of [golub2013matrix], §6.3.2.

An example of $W$ is the trailing right singular vectors $V(:, n+1-p : n+1)$ of an SVD of $C$
(`Matrix.IsSVD.norm_toEuclideanLin_eq_iff_mem_span`), and a Householder matrix gives $Q$. -/
theorem tls_single_rhs {p : Type*} [Fintype p] [DecidableEq p] (hd : ∀ i, d i ≠ 0)
    (ht : ∀ j, t j ≠ 0) {W : Matrix (n ⊕ Unit) p 𝕜} (hW : Wᴴ * W = 1)
    (hmin : ∀ w : EuclideanSpace 𝕜 (n ⊕ Unit),
      ‖toEuclideanLin (tlsWeighted d t A (replicateCol Unit b)) w‖ =
          (⨅ j, (tlsWeighted d t A (replicateCol Unit b)).colSingularValues j) * ‖w‖ ↔
        w ∈ LinearMap.range (toEuclideanLin W))
    {Q : Matrix p p 𝕜} (hQ : Q ∈ unitaryGroup p 𝕜) {l : p}
    (hz : ∀ j, j ≠ l → (W * Q) (Sum.inr ()) j = 0) :
    (∀ y : EuclideanSpace 𝕜 p, ‖y‖ = 1 →
      ‖(W *ᵥ WithLp.ofLp y) (Sum.inr ())‖ ≤ ‖(W * Q) (Sum.inr ()) l‖) ∧
    ((W * Q) (Sum.inr ()) l = 0 → ¬ ∃ X, IsTLSSolution d t A (replicateCol Unit b) X) ∧
    ((W * Q) (Sum.inr ()) l ≠ 0 → ∃ E R, IsTLSPerturbation d t A (replicateCol Unit b) E R ∧
      (A + E) * replicateCol Unit (fun j => -((t (Sum.inl j) : 𝕜) * (W * Q) (Sum.inl j) l) /
        ((t (Sum.inr ()) : 𝕜) * (W * Q) (Sum.inr ()) l)) = replicateCol Unit b + R ∧
      tlsWeighted d t E R =
        -vecMulVec (tlsWeighted d t A (replicateCol Unit b) *ᵥ (W * Q).col l)
          (star ((W * Q).col l))) := by
  set M := W * Q with hMdef
  have hQQ : Q * star Q = 1 := mem_unitaryGroup_iff.1 hQ
  have hM : Mᴴ * M = 1 := by
    rw [hMdef, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Wᴴ, hW, Matrix.one_mul,
      ← star_eq_conjTranspose, mem_unitaryGroup_iff'.1 hQ]
  -- the last entry of `W y` only sees the `l`-th coordinate of `Qᴴ y`
  have hlast : ∀ y : p → 𝕜, (W *ᵥ y) (Sum.inr ()) = M (Sum.inr ()) l * (star Q *ᵥ y) l := by
    intro y
    have e : W *ᵥ y = M *ᵥ (star Q *ᵥ y) := by
      rw [mulVec_mulVec, hMdef, Matrix.mul_assoc, hQQ, Matrix.mul_one]
    rw [e, mulVec, dotProduct, Finset.sum_eq_single l (fun j _ hj => by rw [hz j hj, zero_mul])
      (fun h => absurd (Finset.mem_univ l) h)]
  have ha : ∀ y : EuclideanSpace 𝕜 p, ‖y‖ = 1 →
      ‖(W *ᵥ WithLp.ofLp y) (Sum.inr ())‖ ≤ ‖M (Sum.inr ()) l‖ := by
    intro y hy
    rw [hlast, norm_mul]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    have h1 : ‖(WithLp.toLp 2 (star Q *ᵥ WithLp.ofLp y) : EuclideanSpace 𝕜 p)‖ = 1 := by
      rw [norm_toLp_mulVec_of_mem_unitaryGroup (Unitary.star_mem hQ), WithLp.toLp_ofLp, hy]
    exact (PiLp.norm_apply_le (WithLp.toLp 2 (star Q *ᵥ WithLp.ofLp y) : EuclideanSpace 𝕜 p)
      l).trans h1.le
  refine ⟨ha, fun hα => ?_, fun hα => ?_⟩
  · -- (b): every unit minimizer lies in the span, so its last entry is at most `|α| = 0`
    refine not_isTLSSolution_of_forall_last_eq_zero hd ht fun w hw hmw => ?_
    obtain ⟨y, hy⟩ : WithLp.toLp 2 w ∈ LinearMap.range (toEuclideanLin W) := by
      rw [← hmin, toEuclideanLin_toLp, hmw, hw, mul_one]
    have hy1 : ‖y‖ = 1 := by
      rw [← norm_toEuclideanLin_apply_of_conjTranspose_mul_self_eq_one hW, hy, hw]
    have hwy : W *ᵥ WithLp.ofLp y = w := congrArg WithLp.ofLp hy
    have := ha y hy1
    rwa [hwy, hα, norm_zero, norm_le_zero_iff] at this
  · -- (c): the column `l` of `W Q` is a unit minimizer with nonzero last entry
    have hcol : M.col l = W *ᵥ Q.col l := by
      rw [← mulVec_single_one, ← mulVec_single_one, hMdef, ← mulVec_mulVec]
    have hw : ‖(WithLp.toLp 2 (M.col l) : EuclideanSpace 𝕜 (n ⊕ Unit))‖ = 1 := by
      rw [← mulVec_single_one, ← toEuclideanLin_toLp,
        norm_toEuclideanLin_apply_of_conjTranspose_mul_self_eq_one hM]
      rw [show (WithLp.toLp 2 (Pi.single l (1 : 𝕜)) : EuclideanSpace 𝕜 p) =
        PiLp.single 2 l (1 : 𝕜) from rfl]
      simp
    have hmw := (hmin (WithLp.toLp 2 (M.col l))).2
      ⟨WithLp.toLp 2 (Q.col l), by rw [toEuclideanLin_toLp, hcol]⟩
    rw [hw, mul_one, toEuclideanLin_toLp] at hmw
    exact isTLSSolution_of_mem_smallest hd ht hw hmw hα

end SingleRHS

/-! ### The generic condition of Theorem 6.3.1 -/

section Generic

variable {m n k : ℕ}

/-- On $\mathbb{K}^{a + b}$, the squared norm of a vector is the sum of the squared norms of its two
blocks. -/
private theorem norm_sq_toLp_eq_add {a b : ℕ} (v : Fin (a + b) → 𝕜) :
    ‖(WithLp.toLp 2 v : EuclideanSpace 𝕜 (Fin (a + b)))‖ ^ 2 =
      ‖(WithLp.toLp 2 fun i => v (Fin.castAdd b i) : EuclideanSpace 𝕜 (Fin a))‖ ^ 2 +
        ‖(WithLp.toLp 2 fun j => v (Fin.natAdd a j) : EuclideanSpace 𝕜 (Fin b))‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    Fin.sum_univ_add]

open scoped Matrix.Norms.L2Operator in
/-- Let $C_1 \in \mathbb{K}^{m \times n}$ and $C_2 \in \mathbb{K}^{m \times k}$, and let
$C = [C_1 \mid C_2]$ have the SVD $U^H C V = \Sigma$ with singular values
$\sigma_1 \ge \sigma_2 \ge \dots$. Let $V_{22}$ be the trailing $k \times k$ block of $V$. If
$$\sigma_{n+1}(C) < \sigma_n(C_1),$$
then $V_{22}$ is invertible. This is the first part of the proof of Theorem 6.3.1 of
[golub2013matrix].

If $V_{22} x = 0$ with $x \ne 0$, then $v = V [0; x] = [V_{12} x; 0]$ and
$\|V_{12} x\| = \|x\|$, so $\sigma_n(C_1) \|V_{12} x\| \le \|C_1 V_{12} x\| = \|Cv\| = \|\Sigma
[0; x]\| \le \sigma_{n+1}(C) \|x\|$, by the least stretch of $C_1$ and the ordering of the
$\sigma_i$. The columns of $C$ are reindexed to `Fin (n + k)`. Indices start at $0$, so the
hypothesis is `σ n < C₁.sortedSingularValues (n - 1)`. -/
theorem isUnit_lowerRightBlock_of_lt {C₁ : Matrix (Fin m) (Fin n) 𝕜}
    {C₂ : Matrix (Fin m) (Fin k) 𝕜} {U : Matrix (Fin m) (Fin m) 𝕜} {σ : ℕ → ℝ}
    {V : Matrix (Fin (n + k)) (Fin (n + k)) 𝕜}
    (hC : IsSVD ((fromCols C₁ C₂).submatrix id finSumFinEquiv.symm) U σ V)
    (hσ : σ n < C₁.sortedSingularValues (n - 1)) :
    IsUnit (V.submatrix (Fin.natAdd n) (Fin.natAdd n)) := by
  set C := (fromCols C₁ C₂).submatrix id finSumFinEquiv.symm with hCdef
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- no leading columns: `σ_n(C₁) = 0`
    subst hn
    have h0 : C₁.sortedSingularValues 0 = 0 :=
      (C₁.sortedSingularValues_eq_zero_iff_rank_le 0).2 (by simpa using C₁.rank_le_card_width)
    rw [Nat.zero_sub, h0] at hσ
    exact absurd hσ (not_lt.2 (hC.nonneg 0))
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [← mulVec_injective_iff_isUnit]
  suffices hker : ∀ x, V.submatrix (Fin.natAdd n) (Fin.natAdd n) *ᵥ x = 0 → x = 0 from
    fun x y hxy => sub_eq_zero.1 (hker _ (by rw [mulVec_sub, hxy, sub_self]))
  intro x hx
  by_contra hx0
  have hxpos : 0 < ‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 (Fin k))‖ := by
    refine norm_pos_iff.2 fun h => hx0 ?_
    exact congrArg WithLp.ofLp h
  set e : Fin (n + k) → 𝕜 := Fin.append (0 : Fin n → 𝕜) x with he
  set v : Fin (n + k) → 𝕜 := V *ᵥ e with hv
  have hv_right : ∀ j, v (Fin.natAdd n j) = 0 := fun j => by
    have := congrFun hx j
    simp only [mulVec, dotProduct, submatrix_apply, Pi.zero_apply] at this
    simp only [hv, he, mulVec, dotProduct, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add]
    exact this
  set y : Fin n → 𝕜 := fun i => v (Fin.castAdd k i) with hy
  -- the norms of `x`, `e`, `v` and `y` agree
  have hne : ‖(WithLp.toLp 2 e : EuclideanSpace 𝕜 (Fin (n + k)))‖ =
      ‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 (Fin k))‖ := by
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    rw [norm_sq_toLp_eq_add]
    have h1 : (fun i => e (Fin.castAdd k i)) = 0 := funext fun i => by simp [he]
    have h2 : (fun j => e (Fin.natAdd n j)) = x := funext fun j => by simp [he]
    rw [h1, h2, show (WithLp.toLp 2 (0 : Fin n → 𝕜) : EuclideanSpace 𝕜 (Fin n)) = 0 from rfl,
      norm_zero, zero_pow two_ne_zero, zero_add]
  have hnv : ‖(WithLp.toLp 2 v : EuclideanSpace 𝕜 (Fin (n + k)))‖ =
      ‖(WithLp.toLp 2 e : EuclideanSpace 𝕜 (Fin (n + k)))‖ :=
    norm_toLp_mulVec_of_mem_unitaryGroup hC.mem_unitaryGroup_right e
  have hny : ‖(WithLp.toLp 2 y : EuclideanSpace 𝕜 (Fin n))‖ =
      ‖(WithLp.toLp 2 v : EuclideanSpace 𝕜 (Fin (n + k)))‖ := by
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    rw [norm_sq_toLp_eq_add]
    have h3 : (fun j => v (Fin.natAdd n j)) = 0 := funext hv_right
    rw [h3, show (WithLp.toLp 2 (0 : Fin k → 𝕜) : EuclideanSpace 𝕜 (Fin k)) = 0 from rfl,
      norm_zero, zero_pow two_ne_zero, add_zero]
  -- `C v = C₁ y`
  have hCv : C *ᵥ v = C₁ *ᵥ y := by
    funext r
    simp only [hCdef, mulVec, dotProduct, Fin.sum_univ_add, submatrix_apply, id_eq,
      finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, fromCols_apply_inl,
      fromCols_apply_inr, hv_right, mul_zero, Finset.sum_const_zero, add_zero, hy]
  -- `C v = U Σ e`
  have hCV : C * V = U * rectDiagonal fun i => ((σ i : ℝ) : 𝕜) := by
    rw [← hC.star_mul_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Unitary.mul_star_self_of_mem hC.mem_unitaryGroup_left, Matrix.one_mul]
  -- `Σ e` only sees the entries from `n` on
  set τ : ℕ → 𝕜 := fun i => if n ≤ i then ((σ i : ℝ) : 𝕜) else 0 with hτ
  have hSe : (rectDiagonal fun i => ((σ i : ℝ) : 𝕜) : Matrix (Fin m) (Fin (n + k)) 𝕜) *ᵥ e =
      (rectDiagonal τ : Matrix (Fin m) (Fin (n + k)) 𝕜) *ᵥ e := by
    funext r
    by_cases hr : (r : ℕ) < n + k
    · rw [rectDiagonal_mulVec _ _ _ hr, rectDiagonal_mulVec _ _ _ hr]
      by_cases hrn : n ≤ (r : ℕ)
      · simp [hτ, hrn]
      · have : e ⟨r, hr⟩ = 0 := by
          have := Fin.append_left (0 : Fin n → 𝕜) x ⟨r, by omega⟩
          simpa [he, Fin.castAdd] using this
        rw [this, mul_zero, mul_zero]
    · rw [rectDiagonal_mulVec_of_le _ _ _ (by omega), rectDiagonal_mulVec_of_le _ _ _ (by omega)]
  have hτle : ‖(rectDiagonal τ : Matrix (Fin m) (Fin (n + k)) 𝕜)‖ ≤ σ n := by
    rw [l2_opNorm_rectDiagonal]
    refine Real.iSup_le (fun i => ?_) (hC.nonneg n)
    simp only [hτ]
    split_ifs with hi
    · rw [RCLike.norm_ofReal, abs_of_nonneg (hC.nonneg _)]
      exact hC.antitone hi
    · rw [norm_zero]
      exact hC.nonneg n
  have hupper : ‖(WithLp.toLp 2 (C₁ *ᵥ y) : EuclideanSpace 𝕜 (Fin m))‖ ≤
      σ n * ‖(WithLp.toLp 2 y : EuclideanSpace 𝕜 (Fin n))‖ := by
    rw [← hCv, hv, mulVec_mulVec, hCV, ← mulVec_mulVec,
      norm_toLp_mulVec_of_mem_unitaryGroup hC.mem_unitaryGroup_left, hSe, hny, hnv,
      ← toEuclideanLin_toLp]
    exact (norm_toEuclideanLin_apply_le _ _).trans
      (mul_le_mul_of_nonneg_right hτle (norm_nonneg _))
  have hlower := iInf_colSingularValues_mul_norm_le C₁ (WithLp.toLp 2 y)
  rw [← sortedSingularValues_eq_iInf_colSingularValues, Fintype.card_fin, toEuclideanLin_toLp]
    at hlower
  have hypos : 0 < ‖(WithLp.toLp 2 y : EuclideanSpace 𝕜 (Fin n))‖ := by
    rw [hny, hnv, hne]
    exact hxpos
  have := (mul_le_mul_iff_left₀ hypos).1 (hlower.trans hupper)
  linarith

end Generic

/-! ### Several right-hand sides -/

section Feasible

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k] [DecidableEq m] [DecidableEq n]
  [DecidableEq k]

/-- If $MX = N$, then $D [M \mid N] T$ has rank at most $n$, because $[M \mid MX] = M [I \mid X]$.
-/
private theorem rank_tlsWeighted_le_of_mul_eq {d : m → ℝ} {t : n ⊕ k → ℝ} {M : Matrix m n 𝕜}
    {N : Matrix m k 𝕜} {X : Matrix n k 𝕜} (h : M * X = N) :
    (tlsWeighted d t M N).rank ≤ Fintype.card n := by
  have hMX : fromCols M N = M * fromCols 1 X := by rw [mul_fromCols, Matrix.mul_one, h]
  rw [tlsWeighted, hMX]
  calc _ ≤ (diagonal (fun i => (d i : 𝕜)) * (M * fromCols 1 X)).rank := rank_mul_le_left _ _
    _ ≤ (M * fromCols 1 X).rank := rank_mul_le_right _ _
    _ ≤ M.rank := rank_mul_le_left _ _
    _ ≤ Fintype.card n := rank_le_card_width M

/-- The matrix $T^{-1} \begin{bmatrix} X \\ -I \end{bmatrix}$ of (6.3.5) of [golub2013matrix]. -/
private noncomputable def tlsNull (t : n ⊕ k → ℝ) (X : Matrix n k 𝕜) : Matrix (n ⊕ k) k 𝕜 :=
  fromRows (diagonal (fun j => (t (Sum.inl j) : 𝕜)⁻¹) * X)
    (-diagonal fun j => (t (Sum.inr j) : 𝕜)⁻¹)

/-- $D [E \mid R] T \cdot T^{-1} [X; -I] = D (EX - R)$. -/
private theorem tlsWeighted_mul_tlsNull {d : m → ℝ} {t : n ⊕ k → ℝ} (ht : ∀ j, t j ≠ 0)
    (E : Matrix m n 𝕜) (R : Matrix m k 𝕜) (X : Matrix n k 𝕜) :
    tlsWeighted d t E R * tlsNull t X = diagonal (fun i => (d i : 𝕜)) * (E * X - R) := by
  have ht' : ∀ j, (t j : 𝕜) ≠ 0 := fun j => RCLike.ofReal_ne_zero.2 (ht j)
  have hT : diagonal (fun j => (t j : 𝕜)) * tlsNull t X = fromRows X (-1) := by
    ext (i | i) j
    · simp [tlsNull, mul_inv_cancel_left₀ (ht' _)]
    · by_cases hij : i = j
      · subst hij
        simp [tlsNull, ht' (Sum.inr i)]
      · simp [tlsNull, hij]
  rw [tlsWeighted, Matrix.mul_assoc, hT, Matrix.mul_assoc, fromCols_mul_fromRows, Matrix.mul_neg,
    Matrix.mul_one, ← sub_eq_add_neg]

/-- For nonzero weights, $EX = R$ if and only if $D [E \mid R] T$ annihilates $T^{-1} [X; -I]$; this
is (6.3.5) of [golub2013matrix]. -/
private theorem mul_eq_iff_tlsWeighted_mul_tlsNull_eq_zero {d : m → ℝ} {t : n ⊕ k → ℝ}
    (hd : ∀ i, d i ≠ 0) (ht : ∀ j, t j ≠ 0) {E : Matrix m n 𝕜} {R : Matrix m k 𝕜}
    {X : Matrix n k 𝕜} : E * X = R ↔ tlsWeighted d t E R * tlsNull t X = 0 := by
  rw [tlsWeighted_mul_tlsNull ht]
  constructor
  · intro h
    rw [h, sub_self, Matrix.mul_zero]
  · intro h
    rw [← sub_eq_zero]
    ext i j
    have := congrFun (congrFun h i) j
    rw [diagonal_mul, Matrix.zero_apply] at this
    exact (mul_eq_zero.1 this).resolve_left (RCLike.ofReal_ne_zero.2 (hd i))

end Feasible

section Theorem631

open scoped Matrix.Norms.Frobenius

variable {m n k : ℕ} {d : Fin m → ℝ} {t : Fin n ⊕ Fin k → ℝ} {A : Matrix (Fin m) (Fin n) 𝕜}
  {B : Matrix (Fin m) (Fin k) 𝕜} {U : Matrix (Fin m) (Fin m) 𝕜} {σ : ℕ → ℝ}
  {V : Matrix (Fin (n + k)) (Fin (n + k)) 𝕜}

/-- The generic condition $\sigma_{n+1}(C) < \sigma_n(C_1)$ of Theorem 6.3.1 of [golub2013matrix]
implies $1 \le n \le m$, the gap $\sigma_{n+1}(C) < \sigma_n(C)$ (by column interlacing,
`Matrix.sortedSingularValues_fromCols_left_le`) and the invertibility of $V_{22}$. -/
private theorem generic_facts
    (hC : IsSVD ((tlsWeighted d t A B).submatrix id finSumFinEquiv.symm) U σ V)
    (hσ : σ n < (tlsWeighted d t A B).toCols₁.sortedSingularValues (n - 1)) :
    0 < n ∧ n ≤ m ∧ σ n < σ (n - 1) ∧ IsUnit (V.submatrix (Fin.natAdd n) (Fin.natAdd n)) := by
  have hlt : n - 1 < min m n := by
    by_contra hle
    rw [(tlsWeighted d t A B).toCols₁.sortedSingularValues_eq_zero_of_min_le
      (by simpa using not_lt.1 hle)] at hσ
    exact absurd hσ (not_lt.2 (hC.nonneg n))
  have hC' : IsSVD ((fromCols (tlsWeighted d t A B).toCols₁
      (tlsWeighted d t A B).toCols₂).submatrix id finSumFinEquiv.symm) U σ V := by
    rwa [fromCols_toCols]
  refine ⟨by omega, by omega, ?_, isUnit_lowerRightBlock_of_lt hC' hσ⟩
  have h1 : σ (n - 1) = (tlsWeighted d t A B).sortedSingularValues (n - 1) := by
    rw [hC.singularValues_eq (by omega) (by omega)]
    exact congrFun (sortedSingularValues_submatrix_equiv (tlsWeighted d t A B) (Equiv.refl _)
      finSumFinEquiv.symm) _
  have h2 := sortedSingularValues_fromCols_left_le (tlsWeighted d t A B).toCols₁
    (tlsWeighted d t A B).toCols₂ (n - 1)
  rw [fromCols_toCols] at h2
  linarith

/-- If $\sigma_1, \dots, \sigma_n$ are nonzero and $n \le m$, then the rank-$n$ truncation satisfies
$C_n Y = 0$ if and only if $Y = V_2 V_2^H Y$, where $V_2$ is the last $k$ columns of $V$; this
is the null space of $C_n$ in the proof of Theorem 6.3.1 of [golub2013matrix]. -/
private theorem svdTruncation_mul_eq_zero_iff {M : Matrix (Fin m) (Fin (n + k)) 𝕜}
    (hC : IsSVD M U σ V) (hnm : n ≤ m) (hpos : ∀ i < n, σ i ≠ 0) {p : Type*}
    (Y : Matrix (Fin (n + k)) p 𝕜) :
    svdTruncation U σ V n * Y = 0 ↔
      Y = V.submatrix id (Fin.natAdd n) * ((V.submatrix id (Fin.natAdd n))ᴴ * Y) := by
  have hVV : star V * V = 1 := mem_unitaryGroup_iff'.1 hC.mem_unitaryGroup_right
  have hVV' : V * star V = 1 := mem_unitaryGroup_iff.1 hC.mem_unitaryGroup_right
  have hUU : star U * U = 1 := mem_unitaryGroup_iff'.1 hC.mem_unitaryGroup_left
  have hCV : svdTruncation U σ V n * V =
      U * (rectDiagonal fun i => if i < n then ((σ i : ℝ) : 𝕜) else 0) := by
    rw [svdTruncation, Matrix.mul_assoc, hVV, Matrix.mul_one]
  -- `C_n V₂ = 0`
  have hSig : ((rectDiagonal fun i => if i < n then ((σ i : ℝ) : 𝕜) else 0 :
      Matrix (Fin m) (Fin (n + k)) 𝕜)).submatrix id (Fin.natAdd n) = 0 := by
    ext i j
    simp only [submatrix_apply, id_eq, rectDiagonal_apply, Fin.val_natAdd, Matrix.zero_apply]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hCV₂ : svdTruncation U σ V n * V.submatrix id (Fin.natAdd n) = 0 := by
    change (svdTruncation U σ V n * V).submatrix id (Fin.natAdd n) = 0
    rw [hCV]
    change U * ((rectDiagonal fun i => if i < n then ((σ i : ℝ) : 𝕜) else 0 :
      Matrix (Fin m) (Fin (n + k)) 𝕜)).submatrix id (Fin.natAdd n) = 0
    rw [hSig, Matrix.mul_zero]
  constructor
  · intro h
    have hZ : (rectDiagonal fun i => if i < n then ((σ i : ℝ) : 𝕜) else 0 :
        Matrix (Fin m) (Fin (n + k)) 𝕜) * (star V * Y) = 0 := by
      have := congrArg (star U * ·) h
      rw [svdTruncation] at this
      simpa only [← Matrix.mul_assoc, hUU, Matrix.one_mul, Matrix.mul_zero] using this
    have hlead : ∀ (i : Fin n) (j : p), (star V * Y) (Fin.castAdd k i) j = 0 := by
      intro i j
      have := congrFun (congrFun hZ ⟨i, lt_of_lt_of_le i.isLt hnm⟩) j
      rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.castAdd k i) (fun b _ hb => by
          rw [rectDiagonal_apply, ite_eq_right (fun h => hb (Fin.ext h.symm)), zero_mul])
          (fun h => absurd (Finset.mem_univ _) h), rectDiagonal_apply,
        ite_eq_left (show ((⟨i, lt_of_lt_of_le i.isLt hnm⟩ : Fin m) : ℕ) = Fin.castAdd k i
          from rfl), ite_eq_left i.isLt, Matrix.zero_apply] at this
      exact (mul_eq_zero.1 this).resolve_left (RCLike.ofReal_ne_zero.2 (hpos i i.isLt))
    have hY : Y = V * (star V * Y) := by rw [← Matrix.mul_assoc, hVV', Matrix.one_mul]
    conv_lhs => rw [hY]
    ext r j
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_add]
    simp only [hlead, mul_zero, Finset.sum_const_zero, zero_add]
    rfl
  · intro h
    rw [h, ← Matrix.mul_assoc, hCV₂, Matrix.zero_mul]

/-- If $V_{22}$ is invertible, then $T^{-1} [X; -I] = V_2 S$ for some $S$ if and only if
$X = -T_1 V_{12} V_{22}^{-1} T_2^{-1}$, and then $S = -V_{22}^{-1} T_2^{-1}$. -/
private theorem exists_eq_mul_iff (ht : ∀ j, t j ≠ 0)
    (hV : IsUnit (V.submatrix (Fin.natAdd n) (Fin.natAdd n))) (X : Matrix (Fin n) (Fin k) 𝕜) :
    (∃ S, (tlsNull t X).submatrix finSumFinEquiv.symm id = V.submatrix id (Fin.natAdd n) * S) ↔
      X = -(diagonal (fun j => (t (Sum.inl j) : 𝕜)) * V.submatrix (Fin.castAdd k) (Fin.natAdd n) *
        (V.submatrix (Fin.natAdd n) (Fin.natAdd n))⁻¹ *
          (diagonal fun j => (t (Sum.inr j) : 𝕜))⁻¹) := by
  have ht' : ∀ j, (t j : 𝕜) ≠ 0 := fun j => RCLike.ofReal_ne_zero.2 (ht j)
  have hVd := (isUnit_iff_isUnit_det _).1 hV
  have h11 : diagonal (fun j => (t (Sum.inl j) : 𝕜)) *
      diagonal (fun j => (t (Sum.inl j) : 𝕜)⁻¹) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg diagonal (funext fun j => mul_inv_cancel₀ (ht' _))
  have h11' : diagonal (fun j => (t (Sum.inl j) : 𝕜)⁻¹) *
      diagonal (fun j => (t (Sum.inl j) : 𝕜)) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg diagonal (funext fun j => inv_mul_cancel₀ (ht' _))
  have h22 : (diagonal fun j => (t (Sum.inr j) : 𝕜))⁻¹ =
      diagonal fun j => (t (Sum.inr j) : 𝕜)⁻¹ := inv_eq_left_inv (by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg diagonal (funext fun j => inv_mul_cancel₀ (ht' _)))
  -- the two block rows
  have hrows : ∀ Y Z : Matrix (Fin (n + k)) (Fin k) 𝕜, Y = Z ↔
      Y.submatrix (Fin.castAdd k) id = Z.submatrix (Fin.castAdd k) id ∧
        Y.submatrix (Fin.natAdd n) id = Z.submatrix (Fin.natAdd n) id := by
    intro Y Z
    refine ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨h1, h2⟩ => ?_⟩
    ext r j
    induction r using Fin.addCases with
    | left i => exact congrFun (congrFun h1 i) j
    | right i => exact congrFun (congrFun h2 i) j
  have hW1 : ((tlsNull t X).submatrix finSumFinEquiv.symm id).submatrix (Fin.castAdd k) id =
      diagonal (fun j => (t (Sum.inl j) : 𝕜)⁻¹) * X := by
    ext i j
    simp [tlsNull]
  have hW2 : ((tlsNull t X).submatrix finSumFinEquiv.symm id).submatrix (Fin.natAdd n) id =
      -diagonal (fun j => (t (Sum.inr j) : 𝕜)⁻¹) := by
    ext i j
    by_cases hij : i = j <;> simp [tlsNull, hij]
  have hsplit : ∀ S : Matrix (Fin k) (Fin k) 𝕜,
      (tlsNull t X).submatrix finSumFinEquiv.symm id = V.submatrix id (Fin.natAdd n) * S ↔
        diagonal (fun j => (t (Sum.inl j) : 𝕜)⁻¹) * X =
            V.submatrix (Fin.castAdd k) (Fin.natAdd n) * S ∧
          -diagonal (fun j => (t (Sum.inr j) : 𝕜)⁻¹) =
            V.submatrix (Fin.natAdd n) (Fin.natAdd n) * S := fun S => by
    rw [hrows, hW1, hW2]
    rfl
  rw [exists_congr hsplit]
  constructor
  · rintro ⟨S, h1, h2⟩
    have hS : S = -((V.submatrix (Fin.natAdd n) (Fin.natAdd n))⁻¹ *
        (diagonal fun j => (t (Sum.inr j) : 𝕜))⁻¹) := by
      rw [h22]
      calc S = (V.submatrix (Fin.natAdd n) (Fin.natAdd n))⁻¹ *
            (V.submatrix (Fin.natAdd n) (Fin.natAdd n) * S) := by
            rw [← Matrix.mul_assoc, nonsing_inv_mul _ hVd, Matrix.one_mul]
        _ = _ := by rw [← h2, Matrix.mul_neg]
    calc X = diagonal (fun j => (t (Sum.inl j) : 𝕜)) *
          (diagonal (fun j => (t (Sum.inl j) : 𝕜)⁻¹) * X) := by
          rw [← Matrix.mul_assoc, h11, Matrix.one_mul]
      _ = _ := by rw [h1, hS]; simp only [Matrix.mul_neg, Matrix.mul_assoc]
  · intro hX
    refine ⟨-((V.submatrix (Fin.natAdd n) (Fin.natAdd n))⁻¹ *
        (diagonal fun j => (t (Sum.inr j) : 𝕜))⁻¹), ?_, ?_⟩
    · rw [hX]
      simp only [Matrix.mul_neg, ← Matrix.mul_assoc, h11', Matrix.one_mul]
    · rw [Matrix.mul_neg, ← Matrix.mul_assoc, mul_nonsing_inv _ hVd, Matrix.one_mul, h22]

/-- Under the generic condition, the first $n$ singular values of $C$ are nonzero. -/
private theorem pos_of_generic
    (hC : IsSVD ((tlsWeighted d t A B).submatrix id finSumFinEquiv.symm) U σ V)
    (hσ : σ n < (tlsWeighted d t A B).toCols₁.sortedSingularValues (n - 1)) :
    ∀ i < n, σ i ≠ 0 := fun i hi => by
  obtain ⟨-, -, hgap, -⟩ := generic_facts hC hσ
  exact (lt_of_le_of_lt (hC.nonneg n) (lt_of_lt_of_le hgap (hC.antitone (by omega)))).ne'

/-- If $C + D [E \mid R] T$ is the rank-$n$ truncation $C_n$, then $(A + E) X = B + R$ if and only
if $X = -T_1 V_{12} V_{22}^{-1} T_2^{-1}$. -/
private theorem add_mul_eq_iff (hd : ∀ i, d i ≠ 0) (ht : ∀ j, t j ≠ 0)
    (hC : IsSVD ((tlsWeighted d t A B).submatrix id finSumFinEquiv.symm) U σ V)
    (hσ : σ n < (tlsWeighted d t A B).toCols₁.sortedSingularValues (n - 1))
    {E : Matrix (Fin m) (Fin n) 𝕜} {R : Matrix (Fin m) (Fin k) 𝕜}
    (h : tlsWeighted d t (A + E) (B + R) =
      (svdTruncation U σ V n).submatrix id finSumFinEquiv) (X : Matrix (Fin n) (Fin k) 𝕜) :
    (A + E) * X = B + R ↔
      X = -(diagonal (fun j => (t (Sum.inl j) : 𝕜)) * V.submatrix (Fin.castAdd k) (Fin.natAdd n) *
        (V.submatrix (Fin.natAdd n) (Fin.natAdd n))⁻¹ *
          (diagonal fun j => (t (Sum.inr j) : 𝕜))⁻¹) := by
  obtain ⟨-, hnm, -, hV⟩ := generic_facts hC hσ
  have h22 : (V.submatrix id (Fin.natAdd n))ᴴ * V.submatrix id (Fin.natAdd n) = 1 := by
    rw [conjTranspose_submatrix, ← star_eq_conjTranspose,
      ← submatrix_mul _ _ _ id _ Function.bijective_id,
      mem_unitaryGroup_iff'.1 hC.mem_unitaryGroup_right,
      submatrix_one _ fun a b hab => Fin.ext (by simpa [Fin.ext_iff] using hab)]
  rw [mul_eq_iff_tlsWeighted_mul_tlsNull_eq_zero hd ht, h, ← submatrix_id_id (tlsNull t X),
    submatrix_id_mul_right,
    svdTruncation_mul_eq_zero_iff hC hnm (pos_of_generic hC hσ), ← exists_eq_mul_iff ht hV]
  constructor
  · intro hY
    exact ⟨_, hY⟩
  · rintro ⟨S, hS⟩
    conv_rhs => rw [hS, ← Matrix.mul_assoc (V.submatrix id (Fin.natAdd n))ᴴ, h22, Matrix.one_mul]
    exact hS

/-- $\|C - C_n\|_F^2 = \sum_{i = n+1}^{\min(m, n + k)} \sigma_i^2$. -/
private theorem frobenius_norm_sub_svdTruncation_sq
    (hC : IsSVD ((tlsWeighted d t A B).submatrix id finSumFinEquiv.symm) U σ V) :
    ‖(tlsWeighted d t A B).submatrix id finSumFinEquiv.symm - svdTruncation U σ V n‖ ^ 2 =
      ∑ i ∈ Finset.Ico n (min m (n + k)), σ i ^ 2 := by
  rw [frobenius_norm_sub_svdTruncation hC,
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨-, hi⟩ := Finset.mem_Ico.1 hi
  rw [hC.singularValues_eq (lt_of_lt_of_le hi (min_le_left _ _))
    (lt_of_lt_of_le hi (min_le_right _ _))]

/-- Reindexing the columns does not change the Frobenius norm of a weighted matrix. -/
private theorem frobenius_norm_submatrix_finSumFinEquiv (M : Matrix (Fin m) (Fin n ⊕ Fin k) 𝕜) :
    ‖M.submatrix id finSumFinEquiv.symm‖ = ‖M‖ :=
  frobenius_norm_submatrix_equiv M (Equiv.refl _) finSumFinEquiv.symm

/-- $C - (C + \Delta C) = -\Delta C$, with the columns reindexed. -/
private theorem submatrix_sub_tlsWeighted_add (E : Matrix (Fin m) (Fin n) 𝕜)
    (R : Matrix (Fin m) (Fin k) 𝕜) :
    (tlsWeighted d t A B).submatrix id finSumFinEquiv.symm -
        (tlsWeighted d t (A + E) (B + R)).submatrix id finSumFinEquiv.symm =
      (-tlsWeighted d t E R).submatrix id finSumFinEquiv.symm := by
  rw [tlsWeighted_add]
  ext i j
  simp

/-- If $\operatorname{ran}(B + R) \subseteq \operatorname{ran}(A + E)$, then $C + D [E \mid R] T$
has rank at most $n$. -/
private theorem rank_submatrix_tlsWeighted_le {E : Matrix (Fin m) (Fin n) 𝕜}
    {R : Matrix (Fin m) (Fin k) 𝕜}
    (h : LinearMap.range (B + R).mulVecLin ≤ LinearMap.range (A + E).mulVecLin) :
    ((tlsWeighted d t (A + E) (B + R)).submatrix id finSumFinEquiv.symm).rank ≤ n := by
  obtain ⟨X, hX⟩ := exists_mul_eq_of_range_mulVecLin_le h
  rw [show ((tlsWeighted d t (A + E) (B + R)).submatrix id finSumFinEquiv.symm).rank =
    (tlsWeighted d t (A + E) (B + R)).rank from
      rank_submatrix _ (Equiv.refl _) finSumFinEquiv.symm]
  simpa using rank_tlsWeighted_le_of_mul_eq (d := d) (t := t) hX

/-- If $\operatorname{ran}(B + R) \subseteq \operatorname{ran}(A + E)$, then $\sum_{i =
n+1}^{\min(m, n + k)} \sigma_i^2 \le \|D [E \mid R] T\|_F^2$, by the Eckart–Young–Mirsky
theorem. -/
private theorem sum_sq_le_of_range_le
    (hC : IsSVD ((tlsWeighted d t A B).submatrix id finSumFinEquiv.symm) U σ V)
    {E : Matrix (Fin m) (Fin n) 𝕜} {R : Matrix (Fin m) (Fin k) 𝕜}
    (h : LinearMap.range (B + R).mulVecLin ≤ LinearMap.range (A + E).mulVecLin) :
    ∑ i ∈ Finset.Ico n (min m (n + k)), σ i ^ 2 ≤ ‖tlsWeighted d t E R‖ ^ 2 := by
  have hEY := sum_sq_sortedSingularValues_le_frobenius_norm_sub_sq_of_rank_le
    (C := (tlsWeighted d t A B).submatrix id finSumFinEquiv.symm)
    (rank_submatrix_tlsWeighted_le (d := d) (t := t) h)
  rw [submatrix_sub_tlsWeighted_add, frobenius_norm_submatrix_finSumFinEquiv, norm_neg] at hEY
  refine le_trans (le_of_eq ?_) hEY
  simp only [Fintype.card_fin]
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨-, hi⟩ := Finset.mem_Ico.1 hi
  rw [hC.singularValues_eq (lt_of_lt_of_le hi (min_le_left _ _))
    (lt_of_lt_of_le hi (min_le_right _ _))]

/-- If $C + D [E \mid R] T = C_n$, then $\|D [E \mid R] T\|_F^2 = \sum_{i = n+1}^{\min(m, n + k)}
\sigma_i^2$. -/
private theorem frobenius_norm_sq_of_tlsWeighted_add_eq
    (hC : IsSVD ((tlsWeighted d t A B).submatrix id finSumFinEquiv.symm) U σ V)
    {E : Matrix (Fin m) (Fin n) 𝕜} {R : Matrix (Fin m) (Fin k) 𝕜}
    (h : tlsWeighted d t (A + E) (B + R) = (svdTruncation U σ V n).submatrix id finSumFinEquiv) :
    ‖tlsWeighted d t E R‖ ^ 2 = ∑ i ∈ Finset.Ico n (min m (n + k)), σ i ^ 2 := by
  have hER : tlsWeighted d t E R =
      (svdTruncation U σ V n).submatrix id finSumFinEquiv - tlsWeighted d t A B := by
    rw [← h, tlsWeighted_add, add_sub_cancel_left]
  have : svdTruncation U σ V n - (tlsWeighted d t A B).submatrix id finSumFinEquiv.symm =
      (tlsWeighted d t E R).submatrix id finSumFinEquiv.symm := by
    rw [hER]
    ext i j
    simp
  rw [← frobenius_norm_sub_svdTruncation_sq hC, norm_sub_rev, this,
    frobenius_norm_submatrix_finSumFinEquiv]

/-- Let $A \in \mathbb{K}^{m \times n}$, $B \in \mathbb{K}^{m \times k}$, let the weights $d$, $t$
be nonzero, and let $C = D [A \mid B] T$ have the SVD $U^H C V = \Sigma$ with singular values
$\sigma_1 \ge \sigma_2 \ge \dots$. Let $C_1$ be the first $n$ columns of $C$, and assume the
generic condition $\sigma_{n+1}(C) < \sigma_n(C_1)$. Then $(E, R)$ is a TLS perturbation if and
only if
$$C + D [E \mid R] T = C_n = U \Sigma_n V^H,$$
the rank-$n$ truncation of the SVD of $C$; that is, $D [E \mid R] T = -U_2 \Sigma_2 [V_{12}^H
\mid V_{22}^H]$. This is the characterization (6.3.4) in Theorem 6.3.1 of [golub2013matrix].

Every feasible perturbation makes $C + D [E \mid R] T$ of rank at most $n$, by (6.3.5), so its
size is at least $\|C - C_n\|_F$ by the Eckart–Young–Mirsky theorem. The truncation is feasible,
because its null space is the range of $[V_{12}; V_{22}]$ with $V_{22}$ invertible
(`Matrix.isUnit_lowerRightBlock_of_lt`). It is the only minimizer, because the generic condition
separates $\sigma_n(C) \ge \sigma_n(C_1) > \sigma_{n+1}(C)$
(`Matrix.eq_svdTruncation_of_frobenius_norm_sub_sq_le`). The hypothesis $m \ge n + k$ of the
source is not needed. The columns of $C$ are reindexed to `Fin (n + k)`, indices start at $0$,
and the truncation is `Matrix.svdTruncation U σ V n`. -/
theorem isTLSPerturbation_iff (hd : ∀ i, d i ≠ 0) (ht : ∀ j, t j ≠ 0)
    (hC : IsSVD ((tlsWeighted d t A B).submatrix id finSumFinEquiv.symm) U σ V)
    (hσ : σ n < (tlsWeighted d t A B).toCols₁.sortedSingularValues (n - 1))
    {E : Matrix (Fin m) (Fin n) 𝕜} {R : Matrix (Fin m) (Fin k) 𝕜} :
    IsTLSPerturbation d t A B E R ↔
      tlsWeighted d t (A + E) (B + R) = (svdTruncation U σ V n).submatrix id finSumFinEquiv := by
  obtain ⟨-, -, hgap, -⟩ := generic_facts hC hσ
  -- the truncation is feasible
  have hfeas : ∀ {E' : Matrix (Fin m) (Fin n) 𝕜} {R' : Matrix (Fin m) (Fin k) 𝕜},
      tlsWeighted d t (A + E') (B + R') = (svdTruncation U σ V n).submatrix id finSumFinEquiv →
        LinearMap.range (B + R').mulVecLin ≤ LinearMap.range (A + E').mulVecLin := by
    intro E' R' h
    rw [← (add_mul_eq_iff hd ht hC hσ h _).2 rfl, mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  obtain ⟨E₀, R₀, h₀⟩ := exists_tlsWeighted_eq hd ht
    ((svdTruncation U σ V n).submatrix id finSumFinEquiv - tlsWeighted d t A B)
  have h₀' : tlsWeighted d t (A + E₀) (B + R₀) =
      (svdTruncation U σ V n).submatrix id finSumFinEquiv := by
    rw [tlsWeighted_add, h₀, add_sub_cancel]
  constructor
  · intro h
    have hle : ‖(tlsWeighted d t A B).submatrix id finSumFinEquiv.symm -
        (tlsWeighted d t (A + E) (B + R)).submatrix id finSumFinEquiv.symm‖ ^ 2 ≤
          ∑ i ∈ Finset.Ico n (min m (n + k)), σ i ^ 2 := by
      rw [submatrix_sub_tlsWeighted_add, frobenius_norm_submatrix_finSumFinEquiv, norm_neg,
        ← frobenius_norm_sq_of_tlsWeighted_add_eq hC h₀']
      exact pow_le_pow_left₀ (norm_nonneg _) (h.norm_le E₀ R₀ (hfeas h₀')) 2
    have hĈ := eq_svdTruncation_of_frobenius_norm_sub_sq_le hC hgap
      (rank_submatrix_tlsWeighted_le h.range_le) hle
    rw [← hĈ]
    ext i j
    simp
  · intro h
    refine ⟨hfeas h, fun E' R' h' => ?_⟩
    have := sum_sq_le_of_range_le hC h'
    rw [← frobenius_norm_sq_of_tlsWeighted_add_eq hC h] at this
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

/-- Under the hypotheses of `Matrix.isTLSPerturbation_iff`, there is exactly one TLS perturbation
$(E_0, R_0)$. It is the one with $D [E_0 \mid R_0] T = -U_2 \Sigma_2 [V_{12}^H \mid V_{22}^H]$
of (6.3.4). This is the uniqueness of the perturbation in Theorem 6.3.1 of [golub2013matrix].

The size of the perturbation is given by `Matrix.IsTLSPerturbation.frobenius_norm_sq_eq`. -/
theorem existsUnique_isTLSPerturbation (hd : ∀ i, d i ≠ 0) (ht : ∀ j, t j ≠ 0)
    (hC : IsSVD ((tlsWeighted d t A B).submatrix id finSumFinEquiv.symm) U σ V)
    (hσ : σ n < (tlsWeighted d t A B).toCols₁.sortedSingularValues (n - 1)) :
    ∃! ER : Matrix (Fin m) (Fin n) 𝕜 × Matrix (Fin m) (Fin k) 𝕜,
      IsTLSPerturbation d t A B ER.1 ER.2 := by
  obtain ⟨E₀, R₀, h₀⟩ := exists_tlsWeighted_eq hd ht
    ((svdTruncation U σ V n).submatrix id finSumFinEquiv - tlsWeighted d t A B)
  refine ⟨(E₀, R₀), (isTLSPerturbation_iff hd ht hC hσ).2 (by rw [tlsWeighted_add, h₀,
    add_sub_cancel]), fun ER h => ?_⟩
  have h' := (isTLSPerturbation_iff hd ht hC hσ).1 h
  rw [tlsWeighted_add] at h'
  obtain ⟨h1, h2⟩ := tlsWeighted_injective hd ht ((eq_sub_of_add_eq' h').trans h₀.symm)
  exact Prod.ext h1 h2

/-- Under the hypotheses of `Matrix.isTLSPerturbation_iff`, the TLS perturbation $(E_0, R_0)$ has
the size
$$\|D [E_0 \mid R_0] T\|_F^2 = \sum_{i = n+1}^{\min(m, n + k)} \sigma_i^2.$$
This is the value in the proof of Theorem 6.3.1 of [golub2013matrix], where it reads
$\sigma_{n+1}^2 + \dots + \sigma_{n+k}^2$ for $m \ge n + k$.

Lean indices start at $0$, so the sum is over `Finset.Ico n (min m (n + k))`. -/
theorem IsTLSPerturbation.frobenius_norm_sq_eq (hd : ∀ i, d i ≠ 0) (ht : ∀ j, t j ≠ 0)
    (hC : IsSVD ((tlsWeighted d t A B).submatrix id finSumFinEquiv.symm) U σ V)
    (hσ : σ n < (tlsWeighted d t A B).toCols₁.sortedSingularValues (n - 1))
    {E : Matrix (Fin m) (Fin n) 𝕜} {R : Matrix (Fin m) (Fin k) 𝕜}
    (h : IsTLSPerturbation d t A B E R) :
    ‖tlsWeighted d t E R‖ ^ 2 = ∑ i ∈ Finset.Ico n (min m (n + k)), σ i ^ 2 :=
  frobenius_norm_sq_of_tlsWeighted_add_eq hC ((isTLSPerturbation_iff hd ht hC hσ).1 h)

/-- Under the hypotheses of `Matrix.isTLSPerturbation_iff`, let
$T_1 = \operatorname{diag}(t_1, \dots, t_n)$ and $T_2 = \operatorname{diag}(t_{n+1}, \dots,
t_{n+k})$, and let $V_{12}$ and $V_{22}$ be the blocks of the last $k$ columns of $V$. Then $X$
is a TLS solution if and only if
$$X = X_{TLS} = -T_1 V_{12} V_{22}^{-1} T_2^{-1}.$$
This is the solution formula of Theorem 6.3.1 of [golub2013matrix].

The null space of $C + D [E_0 \mid R_0] T = C_n$ is the range of $[V_{12}; V_{22}]$, so
$T^{-1} [X; -I] = [V_{12}; V_{22}] S$ and $S = -V_{22}^{-1} T_2^{-1}$. -/
theorem isTLSSolution_iff_eq (hd : ∀ i, d i ≠ 0) (ht : ∀ j, t j ≠ 0)
    (hC : IsSVD ((tlsWeighted d t A B).submatrix id finSumFinEquiv.symm) U σ V)
    (hσ : σ n < (tlsWeighted d t A B).toCols₁.sortedSingularValues (n - 1))
    (X : Matrix (Fin n) (Fin k) 𝕜) :
    IsTLSSolution d t A B X ↔
      X = -(diagonal (fun j => (t (Sum.inl j) : 𝕜)) * V.submatrix (Fin.castAdd k) (Fin.natAdd n) *
        (V.submatrix (Fin.natAdd n) (Fin.natAdd n))⁻¹ *
          (diagonal fun j => (t (Sum.inr j) : 𝕜))⁻¹) := by
  constructor
  · rintro ⟨E, R, h, hX⟩
    exact (add_mul_eq_iff hd ht hC hσ ((isTLSPerturbation_iff hd ht hC hσ).1 h) X).1 hX
  · intro hX
    obtain ⟨⟨E₀, R₀⟩, h₀, -⟩ := existsUnique_isTLSPerturbation hd ht hC hσ
    exact ⟨E₀, R₀, h₀,
      (add_mul_eq_iff hd ht hC hσ ((isTLSPerturbation_iff hd ht hC hσ).1 h₀) X).2 hX⟩

end Theorem631

/-! ### Orthogonal regression -/

section Regression

variable {m n : ℕ}

/-- Let $A \in \mathbb{R}^{m \times n}$ with rows $a_i^T$, $b \in \mathbb{R}^m$, row weights
$d \in \mathbb{R}^m$ and column weights $t \in \mathbb{R}^{n + 1}$, with
$T_1 = \operatorname{diag}(t_1, \dots, t_n)$. The **orthogonal-regression objective** is
$$\psi(x) = \sum_{i = 1}^{m} \frac{d_i^2 (a_i^T x - b_i)^2}{x^T T_1^{-2} x + t_{n+1}^{-2}},
  \qquad x \in \mathbb{R}^n.$$
This is (6.3.6) of [golub2013matrix]: $\psi$ is the weighted sum of the squared distances
$\delta_i$ of the points $[a_i; b_i]$ to the hyperplane $\{[a; \beta] : \beta = x^T a\}$
(`Matrix.iInf_sq_norm_diagonal_mulVec_sub_hyperplane`). -/
noncomputable def tlsObjective (d : Fin m → ℝ) (t : Fin (n + 1) → ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, d i ^ 2 * (A i ⬝ᵥ x - b i) ^ 2 /
    (∑ j : Fin n, x j ^ 2 / t (Fin.castSucc j) ^ 2 + 1 / t (Fin.last n) ^ 2)

/-- $\psi(x) = \|Cw\|^2 / \|w\|^2$ for $C = D [A \mid b] T$, with the columns reindexed to
`Fin (n + 1)`, and $w = T^{-1} [x; -1]$. -/
private theorem tlsObjective_eq (d : Fin m → ℝ) {t : Fin (n + 1) → ℝ} (ht : ∀ j, t j ≠ 0)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    tlsObjective d t A b x =
      ‖(WithLp.toLp 2 (((fromCols (diagonal d * A * diagonal fun j => t (Fin.castSucc j))
          (replicateCol (Fin 1) fun i => d i * b i * t (Fin.last n))).submatrix id
            finSumFinEquiv.symm) *ᵥ Fin.snoc (fun j => x j / t (Fin.castSucc j))
              (-1 / t (Fin.last n))) : EuclideanSpace ℝ (Fin m))‖ ^ 2 /
        ‖(WithLp.toLp 2 (Fin.snoc (fun j => x j / t (Fin.castSucc j)) (-1 / t (Fin.last n)) :
          Fin (n + 1) → ℝ) : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2 := by
  rw [tlsObjective, ← Finset.sum_div, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    Fin.sum_univ_castSucc (fun j => ‖(WithLp.toLp 2 (Fin.snoc _ _ : Fin (n + 1) → ℝ) :
      EuclideanSpace ℝ (Fin (n + 1))) j‖ ^ 2)]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
    simp only [mulVec, dotProduct]
    rw [Fin.sum_univ_castSucc]
    simp only [submatrix_apply, id_eq, Fin.snoc_castSucc, Fin.snoc_last]
    have h1 : ∀ j : Fin n, finSumFinEquiv.symm (Fin.castSucc j) = Sum.inl j := fun j =>
      finSumFinEquiv_symm_apply_castAdd j
    have h2 : finSumFinEquiv.symm (Fin.last n) = Sum.inr (0 : Fin 1) :=
      finSumFinEquiv_symm_apply_natAdd 0
    simp only [h1, h2, fromCols_apply_inl, fromCols_apply_inr, replicateCol_apply,
      diagonal_mul, mul_diagonal]
    rw [show ∑ j : Fin n, d i * A i j * t (Fin.castSucc j) * (x j / t (Fin.castSucc j)) =
      d i * ∑ j, A i j * x j from by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by field_simp [ht (Fin.castSucc j)]]
    field_simp [ht (Fin.last n)]
    ring
  · simp only [Fin.snoc_castSucc, Fin.snoc_last, Real.norm_eq_abs, sq_abs,
      div_pow, neg_div, neg_sq, one_pow]

/-- Let $A \in \mathbb{R}^{m \times n}$ and $b \in \mathbb{R}^m$ with $m > n$, let
$d \in \mathbb{R}^m$, and let $t \in \mathbb{R}^{n + 1}$ have nonzero entries. Let
$C = D [A \mid b] T$ have the SVD $U^T C V = \Sigma$, with singular values
$\sigma_1 \ge \sigma_2 \ge \dots$, and assume the generic condition
$\sigma_{n+1}(C) < \sigma_n(D A T_1)$. Then the vector
$$x_{TLS} = -\frac{T_1 v_{12}}{t_{n+1} v_{22}}$$
of Theorem 6.3.1 minimizes $\psi$, where $[v_{12}; v_{22}]$ is the last column of $V$. This is
the statement after (6.3.6) of [golub2013matrix] that the TLS solution minimizes $\psi$, and
Problem P6.3.5.

For $w = T^{-1} [x; -1]$, $\psi(x) = \|Cw\|^2 / \|w\|^2 \ge \sigma_{\min}(C)^2$, and
$T^{-1} [x_{TLS}; -1]$ is a multiple of the last column of $V$, on which
$\|Cv\| = \sigma_{n+1}(C) = \sigma_{\min}(C)$. The entry $v_{22}$ is nonzero by
`Matrix.isUnit_lowerRightBlock_of_lt`. The columns of $C$ are reindexed to `Fin (n + 1)`, and
singular values are indexed from $0$, as in `Matrix.isUnit_lowerRightBlock_of_lt`. -/
theorem isMinOn_tlsObjective (hmn : n < m) (d : Fin m → ℝ) {t : Fin (n + 1) → ℝ}
    (ht : ∀ j, t j ≠ 0) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ} {V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hC : IsSVD ((fromCols (diagonal d * A * diagonal fun j => t (Fin.castSucc j))
      (replicateCol (Fin 1) fun i => d i * b i * t (Fin.last n))).submatrix id
        finSumFinEquiv.symm) U σ V)
    (hsep : σ n < (diagonal d * A * diagonal fun j => t (Fin.castSucc j)).sortedSingularValues
      (n - 1)) :
    IsMinOn (tlsObjective d t A b) Set.univ fun j =>
      -(t (Fin.castSucc j) * V (Fin.castSucc j) (Fin.last n)) /
        (t (Fin.last n) * V (Fin.last n) (Fin.last n)) := by
  set C := (fromCols (diagonal d * A * diagonal fun j => t (Fin.castSucc j))
    (replicateCol (Fin 1) fun i => d i * b i * t (Fin.last n))).submatrix id
      finSumFinEquiv.symm with hCdef
  -- `v₂₂ ≠ 0`
  have hV : V (Fin.last n) (Fin.last n) ≠ 0 := by
    have hu := isUnit_lowerRightBlock_of_lt hC hsep
    rw [isUnit_iff_isUnit_det, det_unique, isUnit_iff_ne_zero] at hu
    exact hu
  set x₀ : Fin n → ℝ := fun j => -(t (Fin.castSucc j) * V (Fin.castSucc j) (Fin.last n)) /
    (t (Fin.last n) * V (Fin.last n) (Fin.last n))
  -- `σ_min(C) = σ n`
  have hmin : ⨅ j, C.colSingularValues j = σ n := by
    rw [← sortedSingularValues_eq_iInf_colSingularValues, Fintype.card_fin, Nat.add_sub_cancel,
      hC.singularValues_eq hmn (Nat.lt_succ_self n)]
  -- the vector of `x₀` is a multiple of the last column of `V`
  set s : ℝ := -1 / (t (Fin.last n) * V (Fin.last n) (Fin.last n))
  have hw₀ : (Fin.snoc (fun j => x₀ j / t (Fin.castSucc j)) (-1 / t (Fin.last n)) :
      Fin (n + 1) → ℝ) = s • fun p => V p (Fin.last n) := by
    funext p
    induction p using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last, Pi.smul_apply, smul_eq_mul, s]
      field_simp [ht (Fin.last n), hV]
    | cast j =>
      simp only [Fin.snoc_castSucc, Pi.smul_apply, smul_eq_mul, s, x₀]
      field_simp [ht (Fin.castSucc j), ht (Fin.last n), hV]
  -- on the last column of `V`, `‖C v‖ = σ n` and `‖v‖ = 1`
  have hCV : C * V = U * (star U * C * V) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Unitary.mul_star_self_of_mem hC.mem_unitaryGroup_left, Matrix.one_mul]
  rw [hC.star_mul_mul] at hCV
  have hVcol : (fun p => V p (Fin.last n)) = V *ᵥ Pi.single (Fin.last n) 1 := by
    funext p
    simp [mulVec, dotProduct, Pi.single_apply]
  have hnormv : ‖(WithLp.toLp 2 (fun p => V p (Fin.last n)) : EuclideanSpace ℝ (Fin (n + 1)))‖
      = 1 := by
    rw [hVcol, norm_toLp_mulVec_of_mem_unitaryGroup hC.mem_unitaryGroup_right]
    simp
  have hnormCv : ‖(WithLp.toLp 2 (C *ᵥ fun p => V p (Fin.last n)) : EuclideanSpace ℝ (Fin m))‖
      = σ n := by
    rw [hVcol, mulVec_mulVec, hCV, ← mulVec_mulVec,
      norm_toLp_mulVec_of_mem_unitaryGroup hC.mem_unitaryGroup_left, EuclideanSpace.norm_eq]
    rw [Finset.sum_eq_single (⟨n, hmn⟩ : Fin m)]
    · rw [PiLp.toLp_apply, rectDiagonal_mulVec _ _ _ (by simp)]
      simp [Pi.single_apply, Fin.ext_iff, Real.sqrt_sq_eq_abs, abs_of_nonneg (hC.nonneg n)]
    · intro r _ hr
      rw [PiLp.toLp_apply]
      have hrn' : (r : ℕ) ≠ n := fun h => hr (Fin.ext h)
      by_cases hrn : (r : ℕ) < n + 1
      · rw [rectDiagonal_mulVec _ _ _ hrn]
        simp [Fin.ext_iff, hrn']
      · rw [rectDiagonal_mulVec_of_le _ _ _ (by omega), norm_zero, zero_pow two_ne_zero]
    · simp
  have hs : s ≠ 0 := div_ne_zero (by norm_num) (mul_ne_zero (ht _) hV)
  have hψ₀ : tlsObjective d t A b x₀ = σ n ^ 2 := by
    rw [tlsObjective_eq d ht, hw₀, mulVec_smul, WithLp.toLp_smul, WithLp.toLp_smul, norm_smul,
      norm_smul, hnormCv, hnormv, mul_one, mul_pow,
      mul_div_cancel_left₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.2 hs))]
  intro x _
  rw [Set.mem_ofPred_eq, hψ₀, tlsObjective_eq d ht]
  set w : Fin (n + 1) → ℝ := Fin.snoc (fun j => x j / t (Fin.castSucc j)) (-1 / t (Fin.last n))
  have hw : 0 < ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin (n + 1)))‖ := by
    refine norm_pos_iff.2 fun h => ?_
    have := congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) => z (Fin.last n)) h
    simp [w, ht (Fin.last n)] at this
  have hlow := iInf_colSingularValues_mul_norm_le C (WithLp.toLp 2 w)
  rw [hmin, toEuclideanLin_toLp] at hlow
  rw [le_div_iff₀ (pow_pos hw 2), ← mul_pow]
  exact pow_le_pow_left₀ (mul_nonneg (hC.nonneg n) (norm_nonneg _)) hlow 2

end Regression

end Matrix

/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Matrix.SingularValues
import Numlib.Eigen.InvariantSubspace
import Numlib.Eigen.PowerMethod
import Numlib.Eigen.QRAlgorithm
import Numlib.LinearAlgebra.Matrix.LU
import NumlibSurface.GolubVanLoan.Chapter07.Section02

/-!
# Golub and Van Loan, Section 7.3: Power Iterations

This module formalizes §7.3 of [golub2013matrix], on iterations that multiply repeatedly by a matrix
$A \in \mathbb{C}^{n \times n}$. It covers the QR iteration (7.3.1)–(7.3.2) as a sequence of unitary
similarities; the power method (7.3.3) with its convergence rate (7.3.5) and its backward error;
orthogonal iteration (7.3.6) and the dominant invariant subspace $D_r(A)$; the QR iteration as
orthogonal iteration and the convergence (7.3.11) of $T_k = Q_k^H A Q_k$ to triangular form
(§7.3.3); the LR iteration as treppeniteration (§7.3.4); and the appendix of the section, which
proves Lemma 7.3.2 and Theorem 7.3.1 with the displays (7.3.18)–(7.3.26).

Theorem 7.3.1, the convergence bound of orthogonal iteration, is false as printed.
`GolubVanLoan.Chapter07.theorem_7_3_1_counterexample` gives a counterexample, and
`GolubVanLoan.Chapter07.theorem_7_3_1` states a corrected version. The proofs specialize the
backbone modules `Numlib.Eigen.PowerMethod` (the iterates `Krylov.powerIterate` and their rates),
`Numlib.Eigen.QRAlgorithm` (the predicates `Matrix.IsShiftedQrStep` and
`Matrix.IsOrthogonalIterationStep`), `Numlib.Eigen.InvariantSubspace` (Lemma 7.3.2 and the dominant
invariant subspace) and `Numlib.LinearAlgebra.Matrix.Sylvester` (the separation `Matrix.sep`).

## Main definitions

* (7.3.3), `GolubVanLoan.Chapter07.powerMethod`: the power method,
  $q^{(k)} = A q^{(k-1)} / \|A q^{(k-1)}\|_2$ and $\lambda^{(k)} = [q^{(k)}]^H A q^{(k)}$.
* (7.3.6), `GolubVanLoan.Chapter07.orthogonalIteration`: a sequence $Q_k$ with $A Q_{k-1} = Q_k R_k$
  a thin QR factorization at every step.
* (7.3.8), `GolubVanLoan.Chapter07.schurSplit`: the partition of the indices into the first $r$ and
  the last $n - r$.

## Main results

* (7.3.1)–(7.3.2), `GolubVanLoan.Chapter07.equation_7_3_2`: the iterates of the QR iteration satisfy
  $T_k = (U_0 \cdots U_k)^H A (U_0 \cdots U_k)$.
* (7.3.5), `GolubVanLoan.Chapter07.equation_7_3_5`: the eigenvalue estimates of the power method
  converge at the rate $(|\lambda_2| / |\lambda_1|)^k$.
* §7.3.1, `GolubVanLoan.Chapter07.powerMethod_dist`: the vectors of the power method converge to the
  dominant eigenvector at the same rate.
* §7.3.1, `GolubVanLoan.Chapter07.powerMethod_backwardError`: $\lambda^{(k)}$ is an exact eigenvalue
  of $A + E$ with $\|E\|_2 = \|r^{(k)}\|_2$, and no smaller $E$ does this.
* §7.3.2, `GolubVanLoan.Chapter07.orthogonalIteration_range`: $\operatorname{ran}(Q_k) = A^k
  \operatorname{ran}(Q_0)$, and the first columns of the $Q_k$ are the vectors of the power method.
* §7.3.2, `GolubVanLoan.Chapter07.dominantInvariantSubspace_unique`: $D_r(A)$ is the unique
  invariant subspace for the $r$ dominant eigenvalues.
* §7.3.3, `GolubVanLoan.Chapter07.orthogonalIteration_qr_step`: for $r = n$, consecutive matrices
  $Q_k^H A Q_k$ are related by a QR step.
* (7.3.11), `GolubVanLoan.Chapter07.equation_7_3_11`: under the corrected hypothesis of Theorem
  7.3.1, the matrices $Q_k^H A Q_k$ converge to upper triangular form.
* (7.3.12)–(7.3.14), `GolubVanLoan.Chapter07.equation_7_3_14`: the LR iteration is treppeniteration
  started from a unit lower triangular matrix.
* Lemma 7.3.2, `GolubVanLoan.Chapter07.lemma_7_3_2`: the bounds (7.3.15) and (7.3.16) on $\|A^k\|_2$
  and $\|A^{-k}\|_2$ through a Schur form.
* Theorem 7.3.1, `GolubVanLoan.Chapter07.theorem_7_3_1`: the corrected convergence bound for
  $\operatorname{dist}(D_r(A), \operatorname{ran}(Q_k))$.
* Theorem 7.3.1, `GolubVanLoan.Chapter07.theorem_7_3_1_counterexample`: a $2 \times 2$ example in
  which the printed theorem fails.
* (7.3.18), `GolubVanLoan.Chapter07.equation_7_3_18`: $\operatorname{dist}(D_r(A),
  \operatorname{ran}(Q_k)) = \|Q_\beta^H Q_k\|_2$.
* (7.3.19), `GolubVanLoan.Chapter07.equation_7_3_19`: $1 = d_k^2 + \sigma_{\min}(Q_\alpha^H Q_k)^2$.
* (7.3.20), `GolubVanLoan.Chapter07.equation_7_3_20`: the Sylvester equation
  $T_{11} X - X T_{22} = -T_{12}$ has a solution with $\|X\|_F \le \|T_{12}\|_F /
  \operatorname{sep}(T_{11}, T_{22})$.
* (7.3.23)–(7.3.24), `GolubVanLoan.Chapter07.equation_7_3_24`: if $G G^H = I + X X^H$, then
  $\sigma_{\min}(G) \ge 1$.
* (7.3.25), `GolubVanLoan.Chapter07.equation_7_3_25`: the columns of $Q_\alpha X + Q_\beta$ span an
  invariant subspace of $A$, and those of $Q_\alpha - Q_\beta X^H$ span an invariant subspace of
  $A^H$.
* (7.3.26), `GolubVanLoan.Chapter07.equation_7_3_26`: the corrected bound $\|(V_0 - X W_0)^{-1}\|_2
  \le 1/\sqrt{1 - \tilde d_0^2}$.

## Conventions

* Matrices are complex, `Matrix (Fin n) (Fin n) ℂ`, as in §7.1. The power method (7.3.3), orthogonal
  iteration (7.3.6) and the results about them are stated over a field $\mathbb{K}$ that is
  $\mathbb{R}$ or $\mathbb{C}$ (`RCLike 𝕜`), so that (8.2.3) and (8.2.8) of Chapter 8 are their
  instances at $\mathbb{K} = \mathbb{R}$.
* $D_r(A)$ is the dominant invariant subspace of $A$, spanned by the first $r$ columns $Q_\alpha$ of
  the unitary factor $Q = [Q_\alpha\ Q_\beta]$ of a Schur decomposition (7.3.7)–(7.3.8). The
  distance $\operatorname{dist}$ of two subspaces is the gap `Submodule.gap`.
* $\|\cdot\|_2$ is the scoped norm `Matrix.Norms.L2Operator` or `Matrix.lpOpNorm 2`, and
  $\|\cdot\|_F$ is the scoped norm `Matrix.Norms.Frobenius`. For a matrix $B$, $\sigma_{\min}(B)$ is
  the least column singular value `⨅ i, B.colSingularValues i`.

## Implementation notes

* Vectors are in `EuclideanSpace 𝕜 (Fin n)` where norms matter, and a matrix acts on them by
  `Matrix.toEuclideanLin`.
* "Some QR factorization" is recorded as data (the factors $U_k$ and $R_k$) or by the predicates
  `Matrix.IsShiftedQrStep` and `Matrix.IsOrthogonalIterationStep`. Every statement therefore holds
  for every choice of the factorizations, as in the source.

## Deviations from the source

* **§7.3.2, dominant invariant subspace** (generalization). The diagonal blocks may be arbitrary
  matrices with strictly separated spectral moduli. Disjoint spectra alone suffice to identify
  the leading span with a sum of generalized eigenspaces. See
  `GolubVanLoan.Chapter07.dominantInvariantSubspace_unique` and
  `GolubVanLoan.Chapter07.span_leading_schurVectors_eq`.
* **Equations (7.3.1)–(7.3.2)** (generalization). The similarity identity allows arbitrary
  second factors $R_k$. See `GolubVanLoan.Chapter07.equation_7_3_2`.
* **Equations (7.3.3), (7.3.5) and §7.3.1** (generalization). The power method also accepts real
  matrices and defines a zero iterate when normalization encounters zero. The rate assumes an
  eigenvector expansion of the initial vector and allows any bound on the nondominant moduli.
  The backward error gives a minimum over perturbations. See
  `GolubVanLoan.Chapter07.powerMethod`, `GolubVanLoan.Chapter07.equation_7_3_5`,
  `GolubVanLoan.Chapter07.powerMethod_dist` and
  `GolubVanLoan.Chapter07.powerMethod_backwardError`.
* **Equation (7.3.6) and §7.3.2** (reading). The iterate predicate records the QR sequence,
  including the empty-width case. The range theorem assumes full column rank of $A^kQ_0$ and
  gives first-column agreement with power iteration up to a unit-modulus phase. See
  `GolubVanLoan.Chapter07.orthogonalIteration` and
  `GolubVanLoan.Chapter07.orthogonalIteration_range`.
* **Equations (7.3.23)–(7.3.25)** (generalization). The factor bound accepts any square factor
  with $GG^H=I+XX^H$. The invariant-subspace theorem also gives the complementary right
  identity. See `GolubVanLoan.Chapter07.equation_7_3_24` and
  `GolubVanLoan.Chapter07.equation_7_3_25`.
* **Equation (7.3.26)** (typo). The displayed definition of $Z$ has $r$ columns. The source
  labels it as $n$ by $n-r$. See `GolubVanLoan.Chapter07.equation_7_3_26`.
* **Theorem 7.3.1** (correction). The printed bound is false. The theorem assumes
  $\operatorname{dist}(D_r(A^H), \operatorname{ran}(Q_0)) < 1$ in place of (7.3.9) and has this
  distance in the denominator. See `GolubVanLoan.Chapter07.theorem_7_3_1` and
  `GolubVanLoan.Chapter07.theorem_7_3_1_counterexample`.
* **Theorem 7.3.1** (generalization). Any bounds $a \le |\lambda_r|$, $b \ge |\lambda_{r+1}|$ with
  $b < a$, and $\nu \ge \|N\|_F$ can replace the source's $|\lambda_r|$, $|\lambda_{r+1}|$ and
  $\|N\|_F$. See `GolubVanLoan.Chapter07.theorem_7_3_1`.
* **Equation (7.3.26)** (correction). The source ends the chain of inequalities with $d_0 =
  \operatorname{dist}(D_r(A), \operatorname{ran}(Q_0))$ through the false claim
  $\operatorname{ran}(Q_\beta) = D_r(A^H)^\perp$. The statement ends it with
  $\operatorname{dist}(D_r(A^H), \operatorname{ran}(Q_0))$. See
  `GolubVanLoan.Chapter07.equation_7_3_26`.
* **Lemma 7.3.2** (typo). The last display of the source writes $|\mu|$ for $|\lambda_{\min}|$. See
  `GolubVanLoan.Chapter07.lemma_7_3_2`.
* **Equations (7.3.12)–(7.3.14)** (reading). The source starts treppeniteration from
  $G_0 \in \mathbb{C}^{n \times r}$ of rank $r$. The statement takes $r = n$ and $G_0 = L_0$ unit
  lower triangular. See `GolubVanLoan.Chapter07.equation_7_3_14`.

## Not formalized

* **Stewart's accelerated orthogonal iteration.** The source gives only approximate rates and no
  algorithm.
* **The estimates $|\lambda^{(k)} - \lambda_1| \approx \|r^{(k)}\|_2 / s(\lambda_1)$ and
  $s(\lambda_1) \approx |w^{(k)H} q^{(k)}|$.** They are heuristics.
* **The remark that "under reasonable assumptions" the matrices $T_k$ of the LR iteration converge
  to upper triangular form.**
* **Equations (7.3.17), (7.3.21) and (7.3.22).** They are identities inside the proof of Theorem
  7.3.1, whose content is the theorem.
* **The flop count.**
-/

open Matrix Filter Topology

namespace GolubVanLoan.Chapter07

variable {n : ℕ}

/-! ### The QR iteration (7.3.1) -/

/-- **Equations (7.3.1)–(7.3.2)** of [golub2013matrix]. Let $A \in \mathbb{C}^{n \times n}$ and let
$U_0, U_1, \dots \in \mathbb{C}^{n \times n}$ be unitary, with $T_0 = U_0^H A U_0$. Suppose that
$T_{k-1} = U_k R_k$ and $T_k = R_k U_k$ for every $k \ge 1$. Then for every $k \ge 0$
$$T_k = (U_0 U_1 \cdots U_k)^H A (U_0 U_1 \cdots U_k),$$
so every $T_k$ is unitarily similar to $A$.

In the source $T_{k-1} = U_k R_k$ is a QR factorization; the statement does not use that $R_k$
is upper triangular. The product $U_0 U_1 \cdots U_k$ is `((List.range (k + 1)).map U).prod`.

**Reading.** Reversed product yields unitary similarity without triangularity assumptions.
-/
theorem equation_7_3_2 {A : Matrix (Fin n) (Fin n) ℂ} {T U R : ℕ → Matrix (Fin n) (Fin n) ℂ}
    (hU : ∀ k, U k ∈ unitaryGroup (Fin n) ℂ) (hT0 : T 0 = star (U 0) * A * U 0)
    (hQR : ∀ k, T k = U (k + 1) * R (k + 1)) (hRQ : ∀ k, T (k + 1) = R (k + 1) * U (k + 1))
    (k : ℕ) :
    T k = star ((List.range (k + 1)).map U).prod * A * ((List.range (k + 1)).map U).prod := by
  induction k with
  | zero => simpa using hT0
  | succ k ih =>
    have hUU : star (U (k + 1)) * U (k + 1) = 1 := mem_unitaryGroup_iff'.1 (hU (k + 1))
    have hstep : T (k + 1) = star (U (k + 1)) * T k * U (k + 1) := by
      rw [hRQ, hQR k, ← Matrix.mul_assoc (star (U (k + 1))), hUU, Matrix.one_mul]
    rw [hstep, ih, List.range_succ (n := k + 1), List.map_append, List.prod_append,
      List.map_singleton, List.prod_singleton, star_mul]
    simp only [Matrix.mul_assoc]

/-! ### §7.3.1 The power method -/

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Equation (7.3.3)** of [golub2013matrix] (the power method). Let $\mathbb{K}$ be $\mathbb{R}$
or $\mathbb{C}$, $A \in \mathbb{K}^{n \times n}$ and $q_0 \in \mathbb{K}^n$. The power method
computes
$$q^{(0)} = q_0, \qquad z^{(k)} = A q^{(k-1)}, \qquad q^{(k)} = z^{(k)} / \|z^{(k)}\|_2, \qquad
  \lambda^{(k)} = [q^{(k)}]^H A q^{(k)},$$
and `powerMethod A q₀ k` is the pair $(q^{(k)}, \lambda^{(k)})$, with
$\lambda^{(0)} = q_0^H A q_0$.

The source states the method over $\mathbb{C}$, and (8.2.3) of Chapter 8 is the instance
$\mathbb{K} = \mathbb{R}$. If $z^{(k)} = 0$, then $q^{(k)} = 0$, because the inverse of $0$ is
$0$ in Lean. For a unit $q_0$ the vectors are the backbone's `Krylov.powerIterate`; see
`GolubVanLoan.Chapter07.powerMethod_fst`.

**Reading.** RCLike field, arbitrary input, explicit estimate at k=0 and total zero normalization.
-/
noncomputable def powerMethod (A : Matrix (Fin n) (Fin n) 𝕜) (q₀ : EuclideanSpace 𝕜 (Fin n)) :
    ℕ → EuclideanSpace 𝕜 (Fin n) × 𝕜
  | 0 => (q₀, inner 𝕜 q₀ (toEuclideanLin A q₀))
  | k + 1 =>
    let z := toEuclideanLin A (powerMethod A q₀ k).1
    let q := (‖z‖ : 𝕜)⁻¹ • z
    (q, inner 𝕜 q (toEuclideanLin A q))

/-- The eigenvalue estimate $\lambda^{(k)}$ of the power method is the Rayleigh quotient
$[q^{(k)}]^H A q^{(k)}$ of its vector $q^{(k)}$. -/
theorem powerMethod_snd (A : Matrix (Fin n) (Fin n) 𝕜) (q₀ : EuclideanSpace 𝕜 (Fin n)) (k : ℕ) :
    (powerMethod A q₀ k).2 =
      inner 𝕜 (powerMethod A q₀ k).1 (toEuclideanLin A (powerMethod A q₀ k).1) := by
  cases k <;> rfl

/-- If $\|q_0\|_2 = 1$, the vector $q^{(k)}$ of the power method (7.3.3) is
$A^k q_0 / \|A^k q_0\|_2$, which is the backbone's `Krylov.powerIterate`. -/
theorem powerMethod_fst (A : Matrix (Fin n) (Fin n) 𝕜) {q₀ : EuclideanSpace 𝕜 (Fin n)}
    (hq₀ : ‖q₀‖ = 1) (k : ℕ) :
    (powerMethod A q₀ k).1 = Krylov.powerIterate (toEuclideanLin A) q₀ k :=
  Krylov.eq_powerIterate_of_recurrence (toEuclideanLin A) q₀
    (y := fun j => (powerMethod A q₀ j).1) (by
    change q₀ = _
    rw [hq₀, RCLike.ofReal_one, inv_one, one_smul]) (fun _ => rfl) k

/-- **Equation (7.3.5)** of [golub2013matrix]. Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let
$A \in \mathbb{K}^{n \times n}$, and let $x_1, \dots, x_n$ be unit vectors with
$A x_i = \lambda_i x_i$. Let $i_0$ be an index and $\rho \ge 0$ a number with
$|\lambda_i| \le \rho < |\lambda_{i_0}|$ for all $i \neq i_0$. Let $q^{(0)}$ be a unit vector
with $q^{(0)} = \sum_i a_i x_i$ and $a_{i_0} \neq 0$, as in (7.3.4). Then there is a constant
$C$ such that the eigenvalue estimates of the power method satisfy
$$|\lambda_{i_0} - \lambda^{(k)}| \le C \left( \frac{\rho}{|\lambda_{i_0}|} \right)^k \qquad
  \text{for all } k \ge 0.$$

The source states $|\lambda_1 - \lambda^{(k)}| = O(|\lambda_2 / \lambda_1|^k)$ for a dominant
$\lambda_1$; here the dominant index is $i_0$ and $\rho$ plays the role of $|\lambda_2|$.

**Reading.** Initial eigenvector expansion suffices without global diagonalizability, and
nondominant moduli can be bounded by arbitrary rho.
-/
theorem equation_7_3_5 {A : Matrix (Fin n) (Fin n) 𝕜} {x : Fin n → EuclideanSpace 𝕜 (Fin n)}
    {l : Fin n → 𝕜} (hx : ∀ i, toEuclideanLin A (x i) = l i • x i) (hx1 : ∀ i, ‖x i‖ = 1)
    {i₀ : Fin n} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ∀ i, i ≠ i₀ → ‖l i‖ ≤ ρ) (hdom : ρ < ‖l i₀‖)
    {a : Fin n → 𝕜}
    (ha : a i₀ ≠ 0) {q₀ : EuclideanSpace 𝕜 (Fin n)} (hq₀ : ‖q₀‖ = 1)
    (hq : q₀ = ∑ i, a i • x i) :
    ∃ C : ℝ, ∀ k, ‖l i₀ - (powerMethod A q₀ k).2‖ ≤ C * (ρ / ‖l i₀‖) ^ k := by
  have hl₀ : l i₀ ≠ 0 := norm_pos_iff.1 (hρ0.trans_lt hdom)
  obtain ⟨C, hC⟩ := Krylov.exists_norm_inner_powerIterate_sub_le_of_eigenbasis
    (LinearMap.continuous_of_finiteDimensional _) hx hx1 hl₀ hρ ha hq
  refine ⟨C, fun k => ?_⟩
  rw [powerMethod_snd, powerMethod_fst A hq₀, norm_sub_rev]
  exact hC k

section L2

open scoped Matrix.Norms.L2Operator

/-- **Section 7.3.1** of [golub2013matrix], the backward error of the power method. Let $\mathbb{K}$
be $\mathbb{R}$ or $\mathbb{C}$, let $A \in \mathbb{K}^{n \times n}$, let $q^{(k)}$ and
$\lambda^{(k)}$ be the iterates of the power method from $q_0$, and assume $\|q^{(k)}\|_2 = 1$.
Let $r^{(k)} = A q^{(k)} - \lambda^{(k)} q^{(k)}$. Then $\|r^{(k)}\|_2$ is the least value of
$\|E\|_2$ over all $E \in \mathbb{K}^{n \times n}$ with
$$(A + E) q^{(k)} = \lambda^{(k)} q^{(k)},$$
and the least value is attained.

The source's perturbation is $E^{(k)} = -r^{(k)} [q^{(k)}]^H$. The norm is the scoped 2-norm
`Matrix.Norms.L2Operator`.

**Generalization.** The source constructs a perturbation with norm equal to the residual. The
theorem also proves minimality among all perturbations that realize the fixed eigenpair. -/
theorem powerMethod_backwardError (A : Matrix (Fin n) (Fin n) 𝕜) (q₀ : EuclideanSpace 𝕜 (Fin n))
    (k : ℕ) (hq : ‖(powerMethod A q₀ k).1‖ = 1) :
    IsLeast {ε : ℝ | ∃ E : Matrix (Fin n) (Fin n) 𝕜,
        toEuclideanLin (A + E) (powerMethod A q₀ k).1 =
          (powerMethod A q₀ k).2 • (powerMethod A q₀ k).1 ∧ ‖E‖ = ε}
      ‖toEuclideanLin A (powerMethod A q₀ k).1 -
        (powerMethod A q₀ k).2 • (powerMethod A q₀ k).1‖ := by
  set q := (powerMethod A q₀ k).1
  set θ := (powerMethod A q₀ k).2
  have h := isLeast_eigen_backwardError (toEuclideanCLM (n := Fin n) (𝕜 := 𝕜) A) hq θ
  refine ⟨?_, fun ε ⟨E, hE, hεE⟩ => h.2 ⟨-toEuclideanCLM (n := Fin n) (𝕜 := 𝕜) E, ?_, ?_⟩⟩
  · obtain ⟨ΔA, hΔ, hn⟩ := h.1
    refine ⟨(toEuclideanCLM (n := Fin n) (𝕜 := 𝕜)).symm (-ΔA), ?_, ?_⟩
    · rw [map_add, LinearMap.add_apply, ← coe_toEuclideanCLM_eq_toEuclideanLin,
        ← coe_toEuclideanCLM_eq_toEuclideanLin, StarAlgEquiv.apply_symm_apply]
      simpa [sub_eq_add_neg] using hΔ
    · rw [← l2_opNorm_toEuclideanCLM, StarAlgEquiv.apply_symm_apply, norm_neg, hn]
      rfl
  · rw [sub_neg_eq_add]
    rw [map_add, LinearMap.add_apply, ← coe_toEuclideanCLM_eq_toEuclideanLin,
      ← coe_toEuclideanCLM_eq_toEuclideanLin] at hE
    simpa using hE
  · rw [norm_neg, l2_opNorm_toEuclideanCLM, hεE]

end L2

/-! ### §7.3.2 Orthogonal iteration -/

/-- **Equation (7.3.6)** of [golub2013matrix] (orthogonal iteration). Let $\mathbb{K}$ be
$\mathbb{R}$ or $\mathbb{C}$ and $A \in \mathbb{K}^{n \times n}$. A sequence
$Q_0, Q_1, \dots \in \mathbb{K}^{n \times r}$ is an **orthogonal iteration** for $A$ if
$Q_0^H Q_0 = I$ and, for every $k \ge 1$, $Q_k$ is the orthonormal factor of some thin QR
factorization
$$Z_k = A Q_{k-1} = Q_k R_k,$$
with $Q_k^H Q_k = I$ and $R_k$ upper triangular. The eigenvalue estimates are the eigenvalues of
$Q_k^H A Q_k$.

The source states the method over $\mathbb{C}$, and (8.2.8) of Chapter 8 is the instance
$\mathbb{K} = \mathbb{R}$. A step is `Matrix.IsOrthogonalIterationStep`. Every $Q_0$ with
orthonormal columns and $r \le n$ starts an orthogonal iteration; see
`GolubVanLoan.Chapter07.orthogonalIteration_exists`.

**Reading.** This predicate records the thin QR sequence. The source's eigenvalue estimates,
computed from the projected matrices $Q_k^H A Q_k$, are described separately. The predicate
also allows $r=0$. -/
def orthogonalIteration {r : ℕ} (A : Matrix (Fin n) (Fin n) 𝕜)
    (Q : ℕ → Matrix (Fin n) (Fin r) 𝕜) : Prop :=
  (Q 0)ᴴ * Q 0 = 1 ∧ ∀ k, IsOrthogonalIterationStep A (Q k) (Q (k + 1))

/-- Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, $A \in \mathbb{K}^{n \times n}$, and let
$Q_0 \in \mathbb{K}^{n \times r}$ have orthonormal columns, with $r \le n$. Then there is an
orthogonal iteration (7.3.6) for $A$ that starts at $Q_0$. No rank hypothesis is needed, because
every step has a thin QR factorization.

**Reading.** Existence for arbitrary initial orthonormal columns, including zero width and real
scalars.
-/
theorem orthogonalIteration_exists {r : ℕ} (A : Matrix (Fin n) (Fin n) 𝕜)
    {Q₀ : Matrix (Fin n) (Fin r) 𝕜} (hQ₀ : Q₀ᴴ * Q₀ = 1) (hr : r ≤ n) :
    ∃ Q : ℕ → Matrix (Fin n) (Fin r) 𝕜, Q 0 = Q₀ ∧ orthogonalIteration A Q := by
  choose next hnext using fun Q : Matrix (Fin n) (Fin r) 𝕜 =>
    exists_isOrthogonalIterationStep A Q hr
  let Q : ℕ → Matrix (Fin n) (Fin r) 𝕜 := fun k => Nat.rec Q₀ (fun _ P => next P) k
  exact ⟨Q, rfl, hQ₀, fun k => hnext (Q k)⟩

/-- **Section 7.3.3** of [golub2013matrix], the QR iteration as orthogonal iteration. Let
$\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, $A \in \mathbb{K}^{n \times n}$, let
$Q_0, Q_1, \dots \in \mathbb{K}^{n \times n}$ be an orthogonal iteration (7.3.6) with $r = n$,
and let $T_k = Q_k^H A Q_k$. For every $k$ there is an upper triangular $R$ such that
$Q_k^H Q_{k+1}$ is unitary and
$$T_k = (Q_k^H Q_{k+1}) R, \qquad T_{k+1} = R (Q_k^H Q_{k+1}).$$
So "$T_k$ is determined by computing the QR factorization of $T_{k-1}$ and then multiplying the
factors together in reverse order".

The last conclusion is also stated as a QR step with shift $0$, `Matrix.IsShiftedQrStep`. The
section §8.2.5 of Chapter 8 is the instance $\mathbb{K} = \mathbb{R}$.

**Reading.** QR factors and reversed-product equalities also over real scalars.
-/
theorem orthogonalIteration_qr_step {A : Matrix (Fin n) (Fin n) 𝕜}
    {Q : ℕ → Matrix (Fin n) (Fin n) 𝕜} (hQ : orthogonalIteration A Q) (k : ℕ) :
    ∃ R : Matrix (Fin n) (Fin n) 𝕜, R.IsUpperTriangular ∧
      (Q k)ᴴ * Q (k + 1) ∈ unitaryGroup (Fin n) 𝕜 ∧
      (Q k)ᴴ * A * Q k = ((Q k)ᴴ * Q (k + 1)) * R ∧
      (Q (k + 1))ᴴ * A * Q (k + 1) = R * ((Q k)ᴴ * Q (k + 1)) ∧
      IsShiftedQrStep 0 ((Q k)ᴴ * A * Q k) ((Q (k + 1))ᴴ * A * Q (k + 1)) := by
  have hunit : ∀ j, Q j ∈ unitaryGroup (Fin n) 𝕜 := by
    intro j
    rw [mem_unitaryGroup_iff', star_eq_conjTranspose]
    cases j with
    | zero => exact hQ.1
    | succ j => exact (hQ.2 j).choose_spec.conjTranspose_mul_self
  obtain ⟨R, hR⟩ := hQ.2 k
  have hQQ : Q k * (Q k)ᴴ = 1 := by
    rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff.1 (hunit k)
  have hQQ' : (Q (k + 1))ᴴ * Q (k + 1) = 1 := hR.conjTranspose_mul_self
  have hA : A * Q k = Q (k + 1) * R := hR.mul_eq.symm
  have hmem : (Q k)ᴴ * Q (k + 1) ∈ unitaryGroup (Fin n) 𝕜 := by
    rw [← star_eq_conjTranspose]
    exact Submonoid.mul_mem _ (Unitary.star_mem (hunit k)) (hunit (k + 1))
  have h1 : (Q k)ᴴ * A * Q k = ((Q k)ᴴ * Q (k + 1)) * R := by
    rw [Matrix.mul_assoc, hA, Matrix.mul_assoc]
  have h2 : (Q (k + 1))ᴴ * A * Q (k + 1) = R * ((Q k)ᴴ * Q (k + 1)) := by
    have hA' : A = Q (k + 1) * R * (Q k)ᴴ := by
      rw [← hA, Matrix.mul_assoc, hQQ, Matrix.mul_one]
    rw [hA', ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQQ', Matrix.one_mul, Matrix.mul_assoc]
  refine ⟨R, hR.isUpperTriangular, hmem, h1, h2, (Q k)ᴴ * Q (k + 1), hmem, R,
    hR.isUpperTriangular, ?_, ?_⟩
  · rw [zero_smul, sub_zero, h1]
  · rw [zero_smul, add_zero, h2]

/-- **Section 7.3.2** of [golub2013matrix], orthogonal iteration iterates subspaces and contains the
power method. Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, $A \in \mathbb{K}^{n \times n}$,
let $Q_0, Q_1, \dots \in \mathbb{K}^{n \times r}$ be an orthogonal iteration (7.3.6), and let
$k \ge 0$ be such that $A^k Q_0$ has full column rank. Then $\operatorname{ran}(Q_k) = A^k
\operatorname{ran}(Q_0)$, and $A^k Q_0 = Q_k S$ for a nonsingular upper triangular
$S \in \mathbb{K}^{r \times r}$. Moreover, if $r \ge 1$, the first column of $Q_k$ is
$c\, q^{(k)}$ for some $c$ with $|c| = 1$, where $q^{(k)}$ is the vector of the power method
(7.3.3) started from the first column of $Q_0$.

The last part is the source's remark that "the sequence $\{Q_k e_1\}$ is precisely the sequence
produced by the power iteration". The factor $c$ accounts for the freedom of sign or phase in
the QR factorizations. The matrix $S$ is the product $R_k \cdots R_1$ of the triangular factors,
as in the first display of the proof in the appendix. Full column rank is linear independence of
the rows of the transpose, and the subspace on the right is `Krylov.subspaceIterate`.

**Reading.** The source identifies the first columns with the power iterates exactly. An
arbitrary thin QR factorization can introduce a unit-modulus phase. The theorem records that
phase and assumes full column rank of $A^kQ_0$ to identify its range with the iterated
subspace. -/
theorem orthogonalIteration_range {r : ℕ} {A : Matrix (Fin n) (Fin n) 𝕜}
    {Q : ℕ → Matrix (Fin n) (Fin r) 𝕜} (hQ : orthogonalIteration A Q) {k : ℕ}
    (hk : LinearIndependent 𝕜 (A ^ k * Q 0)ᵀ) :
    LinearMap.range (toEuclideanLin (Q k)) =
        Krylov.subspaceIterate (toEuclideanLin A) (LinearMap.range (toEuclideanLin (Q 0))) k ∧
      (∃ S : Matrix (Fin r) (Fin r) 𝕜, IsUnit S ∧ S.IsUpperTriangular ∧ A ^ k * Q 0 = Q k * S) ∧
      ∀ h0 : 0 < r, ∃ c : 𝕜, ‖c‖ = 1 ∧
        (WithLp.toLp 2 ((Q k)ᵀ ⟨0, h0⟩) : EuclideanSpace 𝕜 (Fin n)) =
          c • (powerMethod A (WithLp.toLp 2 ((Q 0)ᵀ ⟨0, h0⟩)) k).1 := by
  obtain ⟨S, hS, hSt, hSeq⟩ := exists_pow_mul_eq_mul_of_isOrthogonalIterationStep hQ.2 hk
  refine ⟨range_eq_subspaceIterate_of_isOrthogonalIterationStep hQ.2 hk, ⟨S, hS, hSt, hSeq⟩,
    fun h0 => ?_⟩
  set j : Fin r := ⟨0, h0⟩
  have hortho : ∀ m, (Q m)ᴴ * Q m = 1 := fun m => by
    cases m with
    | zero => exact hQ.1
    | succ m => exact (hQ.2 m).choose_spec.conjTranspose_mul_self
  have hnorm : ∀ m, ‖(WithLp.toLp 2 ((Q m)ᵀ j) : EuclideanSpace 𝕜 (Fin n))‖ = 1 := fun m => by
    have h := norm_toEuclideanLin_apply_of_conjTranspose_mul_self_eq_one (hortho m)
      (WithLp.toLp 2 (Pi.single j 1))
    rwa [toEuclideanLin_toLp, mulVec_single_one, PiLp.toLp_single, PiLp.norm_single,
      norm_one] at h
  have hcol : A ^ k *ᵥ (Q 0)ᵀ j = S j j • (Q k)ᵀ j := by
    ext i
    have h2 : (Q k * S) i j = Q k i j * S j j := by
      rw [Matrix.mul_apply, Finset.sum_eq_single j]
      · intro l _ hl
        rw [hSt (show j < l by
          rw [Fin.lt_def]
          exact Nat.pos_of_ne_zero fun h => hl (Fin.ext h)), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
    change (A ^ k * Q 0) i j = _
    rw [hSeq, h2, Pi.smul_apply, transpose_apply, smul_eq_mul, mul_comm]
  have hSjj : S j j ≠ 0 := by
    intro h
    apply hk.ne_zero j
    ext i
    have h' := congrFun hcol i
    rw [h, zero_smul] at h'
    exact h'
  have hn : (‖S j j‖ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hSjj)
  refine ⟨(S j j)⁻¹ * ‖S j j‖, ?_, ?_⟩
  · rw [norm_mul, norm_inv, RCLike.norm_ofReal, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hSjj)]
  · rw [powerMethod_fst A (hnorm 0) k, Krylov.powerIterate_eq_smul, ← toEuclideanLin_pow,
      toEuclideanLin_toLp, hcol, WithLp.toLp_smul, norm_smul, hnorm k, mul_one, smul_smul,
      smul_smul, show (S j j)⁻¹ * (‖S j j‖ : 𝕜) * (‖S j j‖ : 𝕜)⁻¹ * S j j = 1 by
        field_simp, one_smul]

end RCLike

/-! ### §7.3.4 LR iterations -/

/-- **Equations (7.3.12)–(7.3.14)** of [golub2013matrix], the LR iteration as treppeniteration. Let
$A \in \mathbb{C}^{n \times n}$, let $L_0$ be unit lower triangular, and let
$T_0 = L_0^{-1} A L_0$. For $k \ge 1$ let $T_{k-1} = L_k R_k$ be an LU factorization, with $L_k$
unit lower triangular and $R_k$ upper triangular, and let $T_k = R_k L_k$. Let
$G_k = L_0 L_1 \cdots L_k$. Then for every $k \ge 0$, $G_k$ is unit lower triangular,
$$T_k = G_k^{-1} A G_k, \qquad A G_k = G_{k+1} R_{k+1}.$$
The first identity is (7.3.13). The second says that $A G_k = G_{k+1} R_{k+1}$ is an LU-type
factorization, so the $G_k$ are the iterates of treppeniteration (7.3.12) started from
$G_0 = L_0$.

**Reading.** The source starts treppeniteration from a matrix $G_0 \in \mathbb{C}^{n \times r}$
of rank $r$. The statement takes $r = n$ and $G_0 = L_0$, and it needs $G_0$ to be unit lower
triangular for the identification with the LR iteration.

An LU factorization is `Matrix.IsLU`, and the product $G_k$ is
`((List.range (k + 1)).map L).prod`. -/
theorem equation_7_3_14 {A : Matrix (Fin n) (Fin n) ℂ} {L R T : ℕ → Matrix (Fin n) (Fin n) ℂ}
    (hL0 : (L 0).IsUnitLowerTriangular) (hT0 : T 0 = (L 0)⁻¹ * A * L 0)
    (hLU : ∀ k, IsLU (T k) (L (k + 1)) (R (k + 1)))
    (hRL : ∀ k, T (k + 1) = R (k + 1) * L (k + 1)) (k : ℕ) :
    ((List.range (k + 1)).map L).prod.IsUnitLowerTriangular ∧
      T k = ((List.range (k + 1)).map L).prod⁻¹ * A * ((List.range (k + 1)).map L).prod ∧
      A * ((List.range (k + 1)).map L).prod = ((List.range (k + 2)).map L).prod * R (k + 1) := by
  set G : ℕ → Matrix (Fin n) (Fin n) ℂ := fun j => ((List.range (j + 1)).map L).prod with hGdef
  have hG : ∀ j, G (j + 1) = G j * L (j + 1) := fun j => by
    simp only [G, List.range_succ (n := j + 1), List.map_append, List.prod_append,
      List.map_singleton, List.prod_singleton]
  have hG0 : G 0 = L 0 := by simp [G]
  have hGu : ∀ j, (G j).IsUnitLowerTriangular := by
    intro j
    induction j with
    | zero => rw [hG0]; exact hL0
    | succ j ih => rw [hG j]; exact ih.mul (hLU j).isUnitLowerTriangular
  have hdet : ∀ M : Matrix (Fin n) (Fin n) ℂ, M.IsUnitLowerTriangular → IsUnit M.det :=
    fun M hM => (isUnit_iff_isUnit_det M).1 hM.isUnit
  have hT : ∀ j, T j = (G j)⁻¹ * A * G j := by
    intro j
    induction j with
    | zero => rw [hG0, hT0]
    | succ j ih =>
      have hR : R (j + 1) = (L (j + 1))⁻¹ * T j := by
        rw [← (hLU j).mul_eq, ← Matrix.mul_assoc,
          nonsing_inv_mul _ (hdet _ (hLU j).isUnitLowerTriangular), Matrix.one_mul]
      rw [hRL j, hR, ih, hG j, Matrix.mul_inv_rev]
      simp only [Matrix.mul_assoc]
  refine ⟨hGu k, hT k, ?_⟩
  change A * G k = G (k + 1) * R (k + 1)
  have hAG : A * G k = G k * T k := by
    rw [hT k, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ (hdet _ (hGu k)),
      Matrix.one_mul]
  rw [hAG, ← (hLU k).mul_eq, hG k, Matrix.mul_assoc]

/-! ### The dominant invariant subspace -/

/-- Let $A, Q \in \mathbb{C}^{(p+q) \times (p+q)}$ with $Q$ unitary and $Q^H A Q = \begin{bmatrix}
T_{11} & T_{12} \\ 0 & T_{22} \end{bmatrix}$, where $T_{11} \in \mathbb{C}^{p \times p}$, and
assume $\lambda(T_{11}) \cap \lambda(T_{22}) = \emptyset$. Then the first $p$ columns of $Q$
span $\sum_{\mu \in \lambda(T_{11})} \operatorname{null}((A - \mu I)^{p+q})$, the sum of the
generalized eigenspaces of $A$ for the eigenvalues of $T_{11}$. Every $A$-invariant subspace $S$
of dimension $p$ that contains no eigenvector of $A$ for an eigenvalue outside $\lambda(T_{11})$
equals this span.

The block form is stated after reindexing by `finSumFinEquiv`. The result is used in §7.3.2 and
§7.6.2.

**Generalization.** Uses disjoint spectra rather than dominance and identifies generalized
eigenspace sum.
-/
theorem span_leading_schurVectors_eq {p q : ℕ} {A Q : Matrix (Fin (p + q)) (Fin (p + q)) ℂ}
    (hQ : Q ∈ unitaryGroup (Fin (p + q)) ℂ) {T₁₁ : Matrix (Fin p) (Fin p) ℂ}
    {T₁₂ : Matrix (Fin p) (Fin q) ℂ} {T₂₂ : Matrix (Fin q) (Fin q) ℂ}
    (hT : (star Q * A * Q).reindex finSumFinEquiv.symm finSumFinEquiv.symm =
      fromBlocks T₁₁ T₁₂ 0 T₂₂)
    (hdisj : Disjoint (spectrum ℂ T₁₁) (spectrum ℂ T₂₂)) :
    Submodule.span ℂ (Set.range fun i : Fin p => Q.col (Fin.castAdd q i)) =
        ⨆ μ ∈ spectrum ℂ T₁₁, Module.End.maxGenEigenspace (toLin' A) μ ∧
      ∀ S ∈ Module.End.invtSubmodule (toLin' A), Module.finrank ℂ S = p →
        (∀ μ ∉ spectrum ℂ T₁₁, ∀ x ∈ S, A *ᵥ x = μ • x → x = 0) →
        S = Submodule.span ℂ (Set.range fun i : Fin p => Q.col (Fin.castAdd q i)) := by
  have hQu : IsUnit Q := (isUnit_iff_isUnit_det Q).2
    (isUnit_det_of_right_inverse (mem_unitaryGroup_iff.1 hQ))
  have hinv : Q⁻¹ = star Q := Matrix.inv_eq_left_inv (mem_unitaryGroup_iff'.1 hQ)
  have hspan := span_cols_eq_spectralSubspace_of_conj hQu finSumFinEquiv.symm
    (by rwa [hinv]) hdisj
  simp only [Equiv.symm_symm, finSumFinEquiv_apply_left] at hspan
  refine ⟨hspan, fun S hS hdim hΛ => ?_⟩
  have hli : LinearIndependent ℂ (fun i : Fin p => Q.col (Fin.castAdd q i)) :=
    (linearIndependent_col_iff_isUnit.2 hQu).comp _ (Fin.castAdd_injective p q)
  have hfin : Module.finrank ℂ
      (Submodule.span ℂ (Set.range fun i : Fin p => Q.col (Fin.castAdd q i))) = p := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  rw [hspan]
  refine Module.End.invtSubmodule_eq_spectralSubspace hS
    (fun μ hμ x hx hAx => hΛ μ hμ x hx (by rwa [toLin'_apply] at hAx)) ?_
  rw [← hspan, hfin, hdim]

/-- **Section 7.3.2** of [golub2013matrix], the dominant invariant subspace. Let
$A, Q \in \mathbb{C}^{n \times n}$ with $n = r + s$ and $Q$ unitary, and let
$$Q^H A Q = \begin{bmatrix} T_{11} & T_{12} \\ 0 & T_{22} \end{bmatrix}, \qquad T_{11} \in
  \mathbb{C}^{r \times r},$$
be a block Schur form as in (7.3.7)–(7.3.8). Assume $|\mu| > |\nu|$ for every eigenvalue $\mu$
of $T_{11}$ and every eigenvalue $\nu$ of $T_{22}$; this is the source's
$|\lambda_r| > |\lambda_{r+1}|$. Then the dominant invariant subspace $D_r(A)$, spanned by the
first $r$ columns of $Q$, "is the unique invariant subspace associated with the eigenvalues
$\lambda_1, \dots, \lambda_r$": it equals $\sum_{\mu \in \lambda(T_{11})}
\operatorname{null}((A - \mu I)^n)$, and every $A$-invariant subspace $S$ of dimension $r$ that
contains no eigenvector of $A$ for an eigenvalue outside $\lambda(T_{11})$ equals it.

The diagonal blocks need not be triangular. The block form is stated after reindexing by
`finSumFinEquiv`. The proof applies `GolubVanLoan.Chapter07.span_leading_schurVectors_eq`.

**Reading.** Requires spectral dominance for upper block triangular form with arbitrary diagonal
blocks.
-/
theorem dominantInvariantSubspace_unique {r s : ℕ} {A Q : Matrix (Fin (r + s)) (Fin (r + s)) ℂ}
    (hQ : Q ∈ unitaryGroup (Fin (r + s)) ℂ) {T₁₁ : Matrix (Fin r) (Fin r) ℂ}
    {T₁₂ : Matrix (Fin r) (Fin s) ℂ} {T₂₂ : Matrix (Fin s) (Fin s) ℂ}
    (hT : (star Q * A * Q).reindex finSumFinEquiv.symm finSumFinEquiv.symm =
      fromBlocks T₁₁ T₁₂ 0 T₂₂)
    (hdom : ∀ μ ∈ spectrum ℂ T₁₁, ∀ ν ∈ spectrum ℂ T₂₂, ‖ν‖ < ‖μ‖) :
    Submodule.span ℂ (Set.range fun i : Fin r => Q.col (Fin.castAdd s i)) =
        ⨆ μ ∈ spectrum ℂ T₁₁, Module.End.maxGenEigenspace (toLin' A) μ ∧
      ∀ S ∈ Module.End.invtSubmodule (toLin' A), Module.finrank ℂ S = r →
        (∀ μ ∉ spectrum ℂ T₁₁, ∀ x ∈ S, A *ᵥ x = μ • x → x = 0) →
        S = Submodule.span ℂ (Set.range fun i : Fin r => Q.col (Fin.castAdd s i)) :=
  span_leading_schurVectors_eq hQ hT
    (Set.disjoint_left.2 fun μ h₁ h₂ => lt_irrefl _ (hdom μ h₁ μ h₂))

/-! ### The appendix: Lemma 7.3.2 and the displays of the proof of Theorem 7.3.1 -/

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **Lemma 7.3.2** of [golub2013matrix]. Let $A, Q \in \mathbb{C}^{n \times n}$ with $Q$ unitary
and $Q^H A Q = T = D + N$ upper triangular, where $D$ is the diagonal and $N$ the strictly upper
triangular part of $T$. Let $|\lambda_{\max}| = \max_i |t_{ii}|$ and
$|\lambda_{\min}| = \min_i |t_{ii}|$, and let $\mu \ge 0$. Then for every $k \ge 0$ the bound
(7.3.15) holds:
$$\|A^k\|_2 \le (1 + \mu)^{n-1} \left( |\lambda_{\max}| + \frac{\|N\|_F}{1 + \mu} \right)^k.$$
If moreover $(1 + \mu) |\lambda_{\min}| > \|N\|_F$, then for every $k \ge 0$ the bound (7.3.16)
holds:
$$\|A^{-k}\|_2 \le (1 + \mu)^{n-1} \left( \frac{1}{|\lambda_{\min}| - \|N\|_F / (1 + \mu)}
  \right)^k.$$

**Typo.** The last display of the source writes $|\mu|$ where $|\lambda_{\min}|$ is meant.

The matrix $N$ is `Matrix.strictUpper T`, and the 2-norm is `Matrix.lpOpNorm 2`. The power
$A^{-k}$ is `A⁻¹ ^ k`. For $n = 0$ the maximum and the minimum are $0$. -/
theorem lemma_7_3_2 {A Q T : Matrix (Fin n) (Fin n) ℂ} (hQ : Q ∈ unitaryGroup (Fin n) ℂ)
    (hT : star Q * A * Q = T) (hTu : T.IsUpperTriangular) {μ : ℝ} (hμ : 0 ≤ μ) :
    (∀ k : ℕ, lpOpNorm 2 (A ^ k) ≤
      (1 + μ) ^ (n - 1) * ((⨆ i, ‖T i i‖) + ‖strictUpper T‖ / (1 + μ)) ^ k) ∧
    (‖strictUpper T‖ < (1 + μ) * (⨅ i, ‖T i i‖) → ∀ k : ℕ, lpOpNorm 2 (A⁻¹ ^ k) ≤
      (1 + μ) ^ (n - 1) * (1 / ((⨅ i, ‖T i i‖) - ‖strictUpper T‖ / (1 + μ))) ^ k) :=
  ⟨l2_opNorm_pow_le_of_schur hQ hT hTu hμ, fun hm => l2_opNorm_inv_pow_le_of_schur hQ hT hTu hμ hm⟩

/-- **Equation (7.3.20)** of [golub2013matrix]. Let $p, q \ge 1$,
$T_{11} \in \mathbb{C}^{p \times p}$, $T_{22} \in \mathbb{C}^{q \times q}$ and
$T_{12} \in \mathbb{C}^{p \times q}$. If $\lambda(T_{11}) \cap \lambda(T_{22}) = \emptyset$, the
Sylvester equation $T_{11} X - X T_{22} = -T_{12}$ has a solution
$X \in \mathbb{C}^{p \times q}$ with
$$\|X\|_F \le \frac{\|T_{12}\|_F}{\operatorname{sep}(T_{11}, T_{22})}.$$

The existence of the solution is Lemma 7.1.5. -/
theorem equation_7_3_20 {p q : ℕ} [NeZero p] [NeZero q] {T₁₁ : Matrix (Fin p) (Fin p) ℂ}
    {T₂₂ : Matrix (Fin q) (Fin q) ℂ} (T₁₂ : Matrix (Fin p) (Fin q) ℂ)
    (h : spectrum ℂ T₁₁ ∩ spectrum ℂ T₂₂ = ∅) :
    ∃ X : Matrix (Fin p) (Fin q) ℂ, T₁₁ * X - X * T₂₂ = -T₁₂ ∧ ‖X‖ ≤ ‖T₁₂‖ / sep T₁₁ T₂₂ := by
  have hdisj : Disjoint (spectrum ℂ T₁₁) (spectrum ℂ T₂₂) := Set.disjoint_iff_inter_eq_empty.2 h
  obtain ⟨X, hX, -⟩ := existsUnique_sylvesterMap_eq hdisj (-T₁₂)
  refine ⟨X, hX, ?_⟩
  have hsep : 0 < sep T₁₁ T₂₂ := (sep_pos_iff_disjoint_spectrum).2 hdisj
  have h1 := frobenius_norm_le_div_sep hsep X
  rwa [hX, norm_neg] at h1

end Frobenius

/-- **Equation (7.3.25)** of [golub2013matrix], with the complementary invariant subspace. Let
$A, Q \in \mathbb{C}^{n \times n}$ with $n = p + q$, $Q = [Q_\alpha\ Q_\beta]$ unitary, and
$$Q^H A Q = T = \begin{bmatrix} T_{11} & T_{12} \\ 0 & T_{22} \end{bmatrix}, \qquad T_{11} \in
  \mathbb{C}^{p \times p}.$$
Let $X \in \mathbb{C}^{p \times q}$ solve $T_{11} X - X T_{22} = -T_{12}$. Then
$$T \begin{bmatrix} X \\ I \end{bmatrix} = \begin{bmatrix} X \\ I \end{bmatrix} T_{22}, \qquad
  T^H \begin{bmatrix} I \\ -X^H \end{bmatrix} = \begin{bmatrix} I \\ -X^H \end{bmatrix}
  T_{11}^H,$$
and therefore
$$A (Q_\alpha X + Q_\beta) = (Q_\alpha X + Q_\beta) T_{22}, \qquad A^H (Q_\alpha - Q_\beta
  X^H) = (Q_\alpha - Q_\beta X^H) T_{11}^H.$$
So the columns of $Q_\alpha X + Q_\beta$ span an invariant subspace of $A$ that is complementary
to $\operatorname{ran}(Q_\alpha)$, and the columns of $Q_\alpha - Q_\beta X^H$ span an invariant
subspace of $A^H$. In the setting of Theorem 7.3.1 the latter is the dominant invariant subspace
$D_p(A^H)$.

The source orthonormalizes the columns of $Q_\alpha - Q_\beta X^H$ by $G^{-H}$. The index type
is `Fin p ⊕ Fin q`, so the two matrices are `Q * fromRows X 1` and `Q * fromRows 1 (-Xᴴ)`.

**Generalization.** The statement also gives the complementary right invariant subspace
identity for $Q_\alpha X+Q_\beta$. The numbered source display states the adjoint identity. -/
theorem equation_7_3_25 {p q : ℕ} {A : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ}
    {Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (hQ : Q ∈ unitaryGroup (Fin p ⊕ Fin q) ℂ)
    {T₁₁ : Matrix (Fin p) (Fin p) ℂ} {T₁₂ : Matrix (Fin p) (Fin q) ℂ}
    {T₂₂ : Matrix (Fin q) (Fin q) ℂ} (hT : star Q * A * Q = fromBlocks T₁₁ T₁₂ 0 T₂₂)
    {X : Matrix (Fin p) (Fin q) ℂ} (hX : T₁₁ * X - X * T₂₂ = -T₁₂) :
    fromBlocks T₁₁ T₁₂ 0 T₂₂ * fromRows X 1 = fromRows X 1 * T₂₂ ∧
      (fromBlocks T₁₁ T₁₂ 0 T₂₂)ᴴ * fromRows 1 (-Xᴴ) = fromRows 1 (-Xᴴ) * T₁₁ᴴ ∧
      (A * (Q * fromRows X 1) : Matrix (Fin p ⊕ Fin q) (Fin q) ℂ) =
        (Q * fromRows X 1 * T₂₂ : Matrix (Fin p ⊕ Fin q) (Fin q) ℂ) ∧
      (Aᴴ * (Q * fromRows 1 (-Xᴴ)) : Matrix (Fin p ⊕ Fin q) (Fin p) ℂ) =
        (Q * fromRows 1 (-Xᴴ) * T₁₁ᴴ : Matrix (Fin p ⊕ Fin q) (Fin p) ℂ) := by
  have h1 : fromBlocks T₁₁ T₁₂ 0 T₂₂ * fromRows X 1 = fromRows X 1 * T₂₂ := by
    simp only [fromBlocks_mul_fromRows, fromRows_mul, Matrix.zero_mul, zero_add, Matrix.mul_one,
      Matrix.one_mul]
    refine congrArg₂ fromRows ?_ rfl
    have e : T₁₂ = -(T₁₁ * X - X * T₂₂) := by rw [hX, neg_neg]
    rw [e]
    abel
  have h2 : (fromBlocks T₁₁ T₁₂ 0 T₂₂)ᴴ * fromRows 1 (-Xᴴ) = fromRows 1 (-Xᴴ) * T₁₁ᴴ := by
    have hXh := congrArg conjTranspose hX
    rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, conjTranspose_neg] at hXh
    simp only [fromBlocks_conjTranspose, fromBlocks_mul_fromRows, fromRows_mul, conjTranspose_zero,
      Matrix.zero_mul, neg_zero, add_zero, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg,
      Matrix.neg_mul]
    refine congrArg₂ fromRows rfl ?_
    have e : T₁₂ᴴ = -(Xᴴ * T₁₁ᴴ - T₂₂ᴴ * Xᴴ) := by rw [hXh, neg_neg]
    rw [e]
    abel
  have hQQ' : star Q * Q = 1 := mem_unitaryGroup_iff'.1 hQ
  have hQQ : Q * star Q = 1 := mem_unitaryGroup_iff.1 hQ
  have hA : A = Q * fromBlocks T₁₁ T₁₂ 0 T₂₂ * star Q := by
    rw [← hT, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQQ, Matrix.one_mul, Matrix.mul_assoc,
      hQQ, Matrix.mul_one]
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [hA]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star Q) Q, hQQ', Matrix.one_mul, h1]
  · have hQh : Qᴴ * Q = 1 := by rw [← star_eq_conjTranspose]; exact hQQ'
    rw [hA, star_eq_conjTranspose, conjTranspose_mul, conjTranspose_mul,
      conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Qᴴ Q, hQh, Matrix.one_mul, h2]

open scoped ComplexOrder in
/-- **Equations (7.3.23)–(7.3.24)** of [golub2013matrix]. Let $n \ge 1$ and
$X \in \mathbb{C}^{n \times m}$, and let $G \in \mathbb{C}^{n \times n}$ satisfy
$G G^H = I + X X^H$, as in (7.3.23); the Cholesky factor of $I + X X^H$ is one such $G$. Then
$I + X X^H$ is Hermitian positive definite, and $\sigma_{\min}(G) \ge 1$.

The proof uses $\|G^H v\|^2 = \|v\|^2 + \|X^H v\|^2$, which bounds $G^H$ from below and hence
$(G^H)^{-1}$ from above, and $\|x\|^2 = \langle (G^H)^{-1} x, G x \rangle \le \|x\| \|G x\|$.
Here $\sigma_{\min}(G)$ is the least column singular value.

**Generalization.** The singular-value bound holds for any supplied square factor with
$GG^H=I+XX^H$. The source uses a Cholesky factor. -/
theorem equation_7_3_24 [NeZero n] {m : ℕ} (X : Matrix (Fin n) (Fin m) ℂ)
    {G : Matrix (Fin n) (Fin n) ℂ} (hG : G * Gᴴ = 1 + X * Xᴴ) :
    (1 + X * Xᴴ).PosDef ∧ 1 ≤ ⨅ i, G.colSingularValues i := by
  refine ⟨Matrix.PosDef.one.add_posSemidef (posSemidef_self_mul_conjTranspose X), ?_⟩
  -- `Gᴴ` is bounded below: `‖Gᴴ v‖² = ‖v‖² + ‖Xᴴ v‖²`
  have hlow : ∀ v : EuclideanSpace ℂ (Fin n), ‖v‖ ≤ ‖toEuclideanLin Gᴴ v‖ := by
    intro v
    have h1 : ‖toEuclideanLin Gᴴ v‖ ^ 2 = ‖v‖ ^ 2 + ‖toEuclideanLin Xᴴ v‖ ^ 2 := by
      have e1 : (inner ℂ (toEuclideanLin Gᴴ v) (toEuclideanLin Gᴴ v) : ℂ) =
          inner ℂ v (toEuclideanLin (G * Gᴴ) v) := by
        rw [toEuclideanLin_mul_apply, toEuclideanLin_conjTranspose_eq_adjoint G,
          LinearMap.adjoint_inner_left]
      have e2 : (inner ℂ v (toEuclideanLin (X * Xᴴ) v) : ℂ) =
          inner ℂ (toEuclideanLin Xᴴ v) (toEuclideanLin Xᴴ v) := by
        rw [toEuclideanLin_mul_apply, toEuclideanLin_conjTranspose_eq_adjoint X,
          LinearMap.adjoint_inner_left]
      rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, e1, hG,
        map_add, LinearMap.add_apply, toLpLin_one, LinearMap.id_apply, inner_add_right, e2,
        map_add]
    have h2 : ‖v‖ ^ 2 ≤ ‖toEuclideanLin Gᴴ v‖ ^ 2 := by
      rw [h1]; exact le_add_of_nonneg_right (sq_nonneg _)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2
  -- hence `Gᴴ` is invertible
  have hGu : IsUnit Gᴴ := by
    rw [← mulVec_injective_iff_isUnit]
    intro a b hab
    have h := hlow (WithLp.toLp 2 (a - b))
    rw [toLpLin_toLp, toLin'_apply, mulVec_sub, hab, sub_self, WithLp.toLp_zero, norm_zero,
      norm_le_zero_iff, WithLp.toLp_eq_zero] at h
    exact sub_eq_zero.1 h
  -- and `G` is bounded below: `‖x‖² = ⟪(Gᴴ)⁻¹ x, G x⟫`
  have hGx : ∀ x : EuclideanSpace ℂ (Fin n), ‖x‖ ≤ ‖toEuclideanLin G x‖ := by
    intro x
    set y := toEuclideanLin (Gᴴ)⁻¹ x
    have hy : toEuclideanLin Gᴴ y = x := by
      rw [← toEuclideanLin_mul_apply, Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hGu),
        toLpLin_one, LinearMap.id_apply]
    have hyx : ‖y‖ ≤ ‖x‖ := hy ▸ hlow y
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
    have h3 : ‖x‖ ^ 2 ≤ ‖x‖ * ‖toEuclideanLin G x‖ := by
      calc ‖x‖ ^ 2 = RCLike.re (inner ℂ (toEuclideanLin Gᴴ y) x) := by
            rw [hy, @norm_sq_eq_re_inner ℂ]
        _ = RCLike.re (inner ℂ y (toEuclideanLin G x)) := by
            rw [toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left]
        _ ≤ ‖y‖ * ‖toEuclideanLin G x‖ := (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
        _ ≤ ‖x‖ * ‖toEuclideanLin G x‖ := by gcongr
    nlinarith
  rw [iInf_colSingularValues_eq_iInf_norm]
  have : Nonempty {x : EuclideanSpace ℂ (Fin n) // ‖x‖ = 1} :=
    ⟨⟨EuclideanSpace.single 0 1, by simp⟩⟩
  refine le_ciInf fun x => ?_
  have h := hGx x
  rwa [x.2] at h


/-! ### The rates of §7.3.1–7.3.2 and the appendix displays (7.3.18), (7.3.19), (7.3.26) -/

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Section 7.3.1** of [golub2013matrix], the convergence of the vectors of the power method. Let
$\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ and $A \in \mathbb{K}^{n \times n}$. Let
$x_1, \dots, x_n$ be unit vectors with $A x_i = \lambda_i x_i$, let $\rho \ge 0$ with
$|\lambda_i| \le \rho < |\lambda_{i_0}|$ for all $i \neq i_0$, and let
$q^{(0)} = \sum_i a_i x_i$ be a unit vector with $a_{i_0} \neq 0$, as in (7.3.4). Then there is
a constant $C$ with
$$\operatorname{dist}(\operatorname{span}\{q^{(k)}\}, \operatorname{span}\{x_{i_0}\}) \le C
  \left( \frac{\rho}{|\lambda_{i_0}|} \right)^k \qquad \text{for all } k \ge 0.$$

The source states $\operatorname{dist}(\operatorname{span}\{q^{(k)}\},
\operatorname{span}\{x_1\}) = O(|\lambda_2 / \lambda_1|^k)$. The distance is the gap of
subspaces; for two lines it is the sine of the angle between them, which the backbone bounds.

**Reading.** Subspace gap bound for any initial eigenvector expansion and bound on nondominant
moduli.
-/
theorem powerMethod_dist {A : Matrix (Fin n) (Fin n) 𝕜} {x : Fin n → EuclideanSpace 𝕜 (Fin n)}
    {l : Fin n → 𝕜} (hx : ∀ i, toEuclideanLin A (x i) = l i • x i) (hx1 : ∀ i, ‖x i‖ = 1)
    {i₀ : Fin n} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ∀ i, i ≠ i₀ → ‖l i‖ ≤ ρ) (hdom : ρ < ‖l i₀‖)
    {a : Fin n → 𝕜} (ha : a i₀ ≠ 0) {q₀ : EuclideanSpace 𝕜 (Fin n)} (hq₀ : ‖q₀‖ = 1)
    (hq : q₀ = ∑ i, a i • x i) :
    ∃ C : ℝ, ∀ k, (𝕜 ∙ (powerMethod A q₀ k).1).gap (𝕜 ∙ x i₀) ≤ C * (ρ / ‖l i₀‖) ^ k := by
  have hl₀ : l i₀ ≠ 0 := norm_pos_iff.1 (hρ0.trans_lt hdom)
  obtain ⟨C, hC⟩ := Krylov.exists_norm_sub_smul_powerIterate_le_of_eigenbasis hx hx1 hl₀ hρ ha hq
  refine ⟨C, fun k => ?_⟩
  rw [powerMethod_fst A hq₀ k]
  rcases eq_or_ne ((toEuclideanLin A ^ k) q₀) 0 with h0 | h0
  · have hz := (Krylov.powerIterate_eq_zero_iff (toEuclideanLin A) q₀ k).2 h0
    have h := (hC k).1
    rw [hz, smul_zero, zero_sub, norm_neg, hx1] at h
    have hne : (𝕜 ∙ x i₀) ≠ ⊥ := fun h' =>
      (norm_ne_zero_iff.1 (by rw [hx1]; exact one_ne_zero)) ((Submodule.span_singleton_eq_bot).1 h')
    rw [hz, Submodule.gap_comm, Submodule.gap_congr _ _ (Submodule.span_zero_singleton 𝕜),
      Submodule.gap_comm, Submodule.gap_bot_eq_one _ hne]
    exact h
  · rw [Submodule.gap_span_singleton_eq_sinAngle
      (Krylov.norm_powerIterate_of_ne_zero (toEuclideanLin A) q₀ k h0) (hx1 i₀)]
    exact (hC k).2

end RCLike

section Blocks

variable {r s : ℕ}

/-- If $[Q_\alpha\ Q_\beta]$ has orthonormal columns, then $Q_\alpha^H Q_\alpha = I$,
$Q_\beta^H Q_\beta = I$ and $Q_\alpha^H Q_\beta = 0$. -/
private theorem conjTranspose_mul_fromCols_eq {Qα : Matrix (Fin n) (Fin r) ℂ}
    {Qβ : Matrix (Fin n) (Fin s) ℂ} (hQ : (fromCols Qα Qβ)ᴴ * fromCols Qα Qβ = 1) :
    Qαᴴ * Qα = 1 ∧ Qβᴴ * Qβ = 1 ∧ Qαᴴ * Qβ = 0 := by
  rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols,
    ← fromBlocks_one] at hQ
  obtain ⟨h1, h2, -, h4⟩ := fromBlocks_inj.1 hQ
  exact ⟨h1, h4, h2⟩

open scoped Matrix.Norms.L2Operator

/-- **Equation (7.3.18)** of [golub2013matrix]. Let $Q = [Q_\alpha\ Q_\beta]$ be unitary, with
$Q_\alpha \in \mathbb{C}^{n \times r}$ and $Q_\beta \in \mathbb{C}^{n \times s}$, and let
$Q_k \in \mathbb{C}^{n \times r}$ have orthonormal columns. Then
$$\operatorname{dist}(\operatorname{ran}(Q_\alpha), \operatorname{ran}(Q_k)) = \|W_k\|_2, \qquad
  W_k = Q_\beta^H Q_k.$$

In the source $Q$ is the matrix of Schur vectors, so that
$\operatorname{ran}(Q_\alpha) = D_r(A)$. The identity is the characterization in Theorem 2.5.1
of the distance between two subspaces of equal dimension. Unitarity is stated as $Q^H Q = I$
together with $Q Q^H = I$, and the norm is the scoped 2-norm `Matrix.Norms.L2Operator`. -/
theorem equation_7_3_18 {Qα : Matrix (Fin n) (Fin r) ℂ} {Qβ : Matrix (Fin n) (Fin s) ℂ}
    (hQ : (fromCols Qα Qβ)ᴴ * fromCols Qα Qβ = 1) (hQ' : fromCols Qα Qβ * (fromCols Qα Qβ)ᴴ = 1)
    {Qk : Matrix (Fin n) (Fin r) ℂ} (hQk : Qkᴴ * Qk = 1) :
    (LinearMap.range (toEuclideanLin Qα)).gap (LinearMap.range (toEuclideanLin Qk)) =
      ‖Qβᴴ * Qk‖ := by
  obtain ⟨hα, hβ, -⟩ := conjTranspose_mul_fromCols_eq hQ
  rw [Submodule.gap_comm, gap_range_eq_l2_opNorm_conjTranspose_mul hQk hα hβ
    (range_eq_orthogonal_of_fromCols hQ hQ'), ← l2_opNorm_conjTranspose, conjTranspose_mul,
    conjTranspose_conjTranspose]

/-- **Equation (7.3.19)** of [golub2013matrix]. Let $r \ge 1$ and let
$Q_\alpha, Q_k \in \mathbb{C}^{n \times r}$ have orthonormal columns. With
$V_k = Q_\alpha^H Q_k$ and $d_k = \operatorname{dist}(\operatorname{ran}(Q_\alpha),
\operatorname{ran}(Q_k))$,
$$1 = d_k^2 + \sigma_{\min}(V_k)^2.$$

This is the thin CS decomposition read for two subspaces. Here $\sigma_{\min}(V_k)$ is the least
column singular value of $V_k$. -/
theorem equation_7_3_19 [NeZero r] {Qα Qk : Matrix (Fin n) (Fin r) ℂ} (hα : Qαᴴ * Qα = 1)
    (hQk : Qkᴴ * Qk = 1) :
    1 = (LinearMap.range (toEuclideanLin Qα)).gap (LinearMap.range (toEuclideanLin Qk)) ^ 2 +
      (⨅ i, (Qαᴴ * Qk).colSingularValues i) ^ 2 := by
  have : Nonempty (Fin r) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne r)⟩⟩
  rw [← sortedSingularValues_eq_iInf_colSingularValues, Fintype.card_fin]
  have h := gap_range_sq_add_sortedSingularValues_sq hα hQk
  rw [Fintype.card_fin] at h
  exact h.symm


open scoped ComplexOrder in
/-- **Equation (7.3.26)** of [golub2013matrix], corrected. Let
$Q_\alpha \in \mathbb{C}^{n \times r}$ and $Q_\beta \in \mathbb{C}^{n \times s}$ with $r \ge 1$
be such that $[Q_\alpha\ Q_\beta]$ has orthonormal columns. Let $X \in \mathbb{C}^{r \times s}$,
let $G \in \mathbb{C}^{r \times r}$ satisfy $G G^H = I + X X^H$ as in (7.3.23), and let
$Z = (Q_\alpha - Q_\beta X^H) G^{-H}$. Let $Q_0 \in \mathbb{C}^{n \times r}$ have orthonormal
columns, and let $V_0 = Q_\alpha^H Q_0$, $W_0 = Q_\beta^H Q_0$ and $\tilde d_0 =
\operatorname{dist}(\operatorname{ran}(Z), \operatorname{ran}(Q_0))$. If $\tilde d_0 < 1$, then
$Z^H Z = I$, $V_0 - X W_0 = G (Z^H Q_0)$, the matrix $V_0 - X W_0$ is nonsingular, and
$$\|(V_0 - X W_0)^{-1}\|_2 \le \|G^{-1}\|_2 \|(Z^H Q_0)^{-1}\|_2 \le \frac{1}{\sqrt{1 - \tilde
  d_0^2}}.$$

**Correction.** The source ends this chain with $d_0 = \operatorname{dist}(D_r(A),
\operatorname{ran}(Q_0))$ in place of $\tilde d_0$, through the claim
$\operatorname{ran}(Q_\beta) = D_r(A^H)^\perp$. That claim is false unless $T_{12} = 0$, and it
is the source of the error in Theorem 7.3.1; see
`GolubVanLoan.Chapter07.theorem_7_3_1_counterexample`.

The columns of $Z$ are an orthonormal basis of $\operatorname{ran}(Q_\alpha - Q_\beta X^H)$.
When $X$ solves the Sylvester equation (7.3.20), this is the dominant invariant subspace
$D_r(A^H)$, by (7.3.25). The distance is the gap of subspaces, and the norm is the scoped
2-norm.

**Typo.** The source gives $Z$ as $n$ by $n-r$. Its displayed definition has $r$ columns. The
inverse estimate uses $Z^H Q_0$. -/
theorem equation_7_3_26 [NeZero r] {Qα : Matrix (Fin n) (Fin r) ℂ} {Qβ : Matrix (Fin n) (Fin s) ℂ}
    (hQ : (fromCols Qα Qβ)ᴴ * fromCols Qα Qβ = 1) {X : Matrix (Fin r) (Fin s) ℂ}
    {G : Matrix (Fin r) (Fin r) ℂ} (hG : G * Gᴴ = 1 + X * Xᴴ) {Z : Matrix (Fin n) (Fin r) ℂ}
    (hZ : Z = (Qα - Qβ * Xᴴ) * (Gᴴ)⁻¹) {Q₀ : Matrix (Fin n) (Fin r) ℂ} (hQ₀ : Q₀ᴴ * Q₀ = 1)
    (hd : (LinearMap.range (toEuclideanLin Z)).gap (LinearMap.range (toEuclideanLin Q₀)) < 1) :
    Zᴴ * Z = 1 ∧ Qαᴴ * Q₀ - X * (Qβᴴ * Q₀) = G * (Zᴴ * Q₀) ∧
      IsUnit (Qαᴴ * Q₀ - X * (Qβᴴ * Q₀)) ∧
      ‖(Qαᴴ * Q₀ - X * (Qβᴴ * Q₀))⁻¹‖ ≤ ‖G⁻¹‖ * ‖(Zᴴ * Q₀)⁻¹‖ ∧
      ‖G⁻¹‖ * ‖(Zᴴ * Q₀)⁻¹‖ ≤ 1 / Real.sqrt (1 -
        (LinearMap.range (toEuclideanLin Z)).gap (LinearMap.range (toEuclideanLin Q₀)) ^ 2) := by
  obtain ⟨hα, hβ, hαβ⟩ := conjTranspose_mul_fromCols_eq hQ
  have hβα : Qβᴴ * Qα = 0 := by
    rw [← conjTranspose_conjTranspose Qα, ← conjTranspose_mul, hαβ, conjTranspose_zero]
  obtain ⟨hpd, hσG⟩ := equation_7_3_24 X hG
  have hGu : IsUnit G.det := by
    have h := hpd.isUnit
    rw [← hG, isUnit_iff_isUnit_det, det_mul, det_conjTranspose] at h
    exact isUnit_of_mul_isUnit_left h
  have hGhu : IsUnit Gᴴ.det := by rw [det_conjTranspose]; exact hGu.star
  set Y := Qα - Qβ * Xᴴ with hY
  have hYY : Yᴴ * Y = 1 + X * Xᴴ := by
    rw [hY, conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.mul_sub, hα, Matrix.mul_assoc X, hβα, Matrix.mul_zero,
      ← Matrix.mul_assoc, hαβ, Matrix.zero_mul, Matrix.mul_assoc X, ← Matrix.mul_assoc Qβᴴ, hβ,
      Matrix.one_mul]
    abel
  have hZG : Z * Gᴴ = Y := by
    rw [hZ, Matrix.mul_assoc, nonsing_inv_mul _ hGhu, Matrix.mul_one]
  have hZZ : Zᴴ * Z = 1 := by
    have hGi : ((Gᴴ)⁻¹)ᴴ = G⁻¹ := by rw [conjTranspose_nonsing_inv, conjTranspose_conjTranspose]
    rw [hZ, conjTranspose_mul, hGi, Matrix.mul_assoc, ← Matrix.mul_assoc Yᴴ, hYY, ← hG,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul _ hGu, Matrix.one_mul,
      mul_nonsing_inv _ hGhu]
  have hV : Qαᴴ * Q₀ - X * (Qβᴴ * Q₀) = G * (Zᴴ * Q₀) := by
    have h1 : G * Zᴴ = Yᴴ := by
      rw [← hZG, conjTranspose_mul, conjTranspose_conjTranspose]
    calc Qαᴴ * Q₀ - X * (Qβᴴ * Q₀) = Yᴴ * Q₀ := by
          rw [hY, conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose,
            Matrix.sub_mul, Matrix.mul_assoc]
      _ = G * (Zᴴ * Q₀) := by rw [← h1, Matrix.mul_assoc]
  -- the least singular value of `Zᴴ Q₀`
  set d := (LinearMap.range (toEuclideanLin Z)).gap (LinearMap.range (toEuclideanLin Q₀))
  have hd0 : 0 ≤ d := Submodule.gap_nonneg _ _
  have hσ := equation_7_3_19 hZZ hQ₀
  have hσ0 : 0 ≤ ⨅ i, (Zᴴ * Q₀).colSingularValues i :=
    le_ciInf fun i => colSingularValues_nonneg _ i
  have hσeq : ⨅ i, (Zᴴ * Q₀).colSingularValues i = Real.sqrt (1 - d ^ 2) := by
    rw [← Real.sqrt_sq hσ0]
    congr 1
    linarith
  have hσpos : 0 < ⨅ i, (Zᴴ * Q₀).colSingularValues i := by
    rw [hσeq]
    exact Real.sqrt_pos.2 (by nlinarith)
  have hZQu : IsUnit (Zᴴ * Q₀) := Matrix.isUnit_of_iInf_colSingularValues_pos _ hσpos
  have hZQd : IsUnit (Zᴴ * Q₀).det := (isUnit_iff_isUnit_det _).1 hZQu
  have hunit : IsUnit (Qαᴴ * Q₀ - X * (Qβᴴ * Q₀)) := by
    rw [hV]; exact ((isUnit_iff_isUnit_det G).2 hGu).mul hZQu
  refine ⟨hZZ, hV, hunit, ?_, ?_⟩
  · rw [hV, Matrix.mul_inv_rev]
    refine (norm_mul_le _ _).trans (le_of_eq (mul_comm _ _))
  · have hG1 : ‖G⁻¹‖ ≤ 1 := by
      rw [l2_opNorm_inv_eq_inv_iInf_colSingularValues _ hGu]
      exact inv_le_one_of_one_le₀ hσG
    rw [l2_opNorm_inv_eq_inv_iInf_colSingularValues _ hZQd, hσeq, one_div]
    calc ‖G⁻¹‖ * (Real.sqrt (1 - d ^ 2))⁻¹ ≤ 1 * (Real.sqrt (1 - d ^ 2))⁻¹ :=
          mul_le_mul_of_nonneg_right hG1 (inv_nonneg.2 (Real.sqrt_nonneg _))
      _ = (Real.sqrt (1 - d ^ 2))⁻¹ := one_mul _

end Blocks

/-- The norm of a vector $v \in \mathbb{C}^2$ is $\sqrt{|v_0|^2 + |v_1|^2}$. -/
private theorem norm_euclidean_two (v : EuclideanSpace ℂ (Fin 2)) :
    ‖v‖ = Real.sqrt (‖v 0‖ ^ 2 + ‖v 1‖ ^ 2) := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]

/-- The identity $(\sqrt 2)^{-1} (\sqrt 2)^{-1} = 1/2$. -/
private theorem inv_sqrt_two_mul_self : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2), one_div]

/-- The column space of a one-column matrix is the line spanned by its column. -/
private theorem range_toEuclideanLin_col {m : ℕ} (M : Matrix (Fin m) (Fin 1) ℂ) :
    LinearMap.range (toEuclideanLin M) = ℂ ∙ WithLp.toLp 2 (fun i => M i 0) := by
  have happ : ∀ y : EuclideanSpace ℂ (Fin 1),
      toEuclideanLin M y = y 0 • WithLp.toLp 2 (fun i => M i 0) := by
    intro y
    ext i
    simp [toEuclideanLin_apply, mulVec, dotProduct, mul_comm]
  ext x
  rw [LinearMap.mem_range, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y 0, (happ y).symm⟩
  · rintro ⟨a, rfl⟩
    refine ⟨EuclideanSpace.single 0 a, ?_⟩
    rw [happ]
    simp

open scoped Matrix.Norms.Frobenius in
/-- **Theorem 7.3.1** of [golub2013matrix], a counterexample to the printed statement. Let
$$A = \begin{bmatrix} 2 & 1 \\ 0 & 1 \end{bmatrix}, \qquad Q_0 = \frac{1}{\sqrt 2}
  \begin{bmatrix} 1 \\ -1 \end{bmatrix},$$
and let $Q_0, Q_1, \dots \in \mathbb{C}^{2 \times 1}$ be any orthogonal iteration (7.3.6) for
$A$ that starts at $Q_0$. Let $N$ be the strictly upper triangular part of $A$ and $d_k =
\operatorname{dist}(\operatorname{span}\{e_1\}, \operatorname{ran}(Q_k))$. Then $\|N\|_F = 1$,
$d_k = 1/\sqrt 2$ for every $k$, and the printed right-hand side of (7.3.10) with $\mu = 3$,
$$\left( 1 + \frac{1}{1} \right) \left( \frac{1 + 1/4}{2 - 1/4} \right)^k \frac{d_0}{\sqrt{1 -
  d_0^2}},$$
tends to $0$ as $k \to \infty$. Moreover $A^H (1, 1)^T = 2 (1, 1)^T$, and
$\operatorname{dist}(\operatorname{span}\{(1, 1)^T\}, \operatorname{ran}(Q_0)) = 1$.

Here $A$ is its own Schur form, with $Q = I$, $r = 1$, $D_1(A) = \operatorname{span}\{e_1\}$,
$T_{11} = 2$, $T_{12} = 1$, $T_{22} = 1$ and $\operatorname{sep}(2, 1) = 1$. With $\mu = 3$ the
hypothesis $(1 + \mu) |\lambda_1| = 8 > \|N\|_F$ of the theorem holds, and the printed
hypothesis (7.3.9) holds because $d_0 = 1/\sqrt 2 < 1$. Yet $d_k$ does not tend to $0$, because
$A Q_0 = Q_0$ gives $\operatorname{ran}(Q_k) = \operatorname{ran}(Q_0)$ for every $k$. The
hypothesis that the proof really uses fails: $D_1(A^H) = \operatorname{span}\{(1, 1)^T\}$ is
orthogonal to $\operatorname{ran}(Q_0)$, so $\operatorname{dist}(D_1(A^H),
\operatorname{ran}(Q_0)) = 1$.

**Reading.** Specific nonnormal 2×2 input has constant positive gap while printed bound tends to
zero.
-/
theorem theorem_7_3_1_counterexample {Q : ℕ → Matrix (Fin 2) (Fin 1) ℂ}
    (hQ : orthogonalIteration !![(2 : ℂ), 1; 0, 1] Q)
    (h0 : Q 0 = !![(((Real.sqrt 2)⁻¹ : ℝ) : ℂ); -(((Real.sqrt 2)⁻¹ : ℝ) : ℂ)]) :
    ‖strictUpper !![(2 : ℂ), 1; 0, 1]‖ = 1 ∧
      (∀ k, (ℂ ∙ EuclideanSpace.single (0 : Fin 2) (1 : ℂ)).gap
        (LinearMap.range (toEuclideanLin (Q k))) = (Real.sqrt 2)⁻¹) ∧
      Tendsto (fun k : ℕ => (1 + 3 : ℝ) ^ (2 - 2) *
          (1 + ‖!![(1 : ℂ)]‖ / sep !![(2 : ℂ)] !![(1 : ℂ)]) *
          ((‖(1 : ℂ)‖ + ‖strictUpper !![(2 : ℂ), 1; 0, 1]‖ / (1 + 3)) /
            (‖(2 : ℂ)‖ - ‖strictUpper !![(2 : ℂ), 1; 0, 1]‖ / (1 + 3))) ^ k *
          ((ℂ ∙ EuclideanSpace.single (0 : Fin 2) (1 : ℂ)).gap
              (LinearMap.range (toEuclideanLin (Q 0))) /
            Real.sqrt (1 - (ℂ ∙ EuclideanSpace.single (0 : Fin 2) (1 : ℂ)).gap
              (LinearMap.range (toEuclideanLin (Q 0))) ^ 2))) atTop (𝓝 0) ∧
      (!![(2 : ℂ), 1; 0, 1])ᴴ *ᵥ ![1, 1] = (2 : ℂ) • ![1, 1] ∧
      (ℂ ∙ WithLp.toLp 2 ![(((Real.sqrt 2)⁻¹ : ℝ) : ℂ), (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)]).gap
        (LinearMap.range (toEuclideanLin (Q 0))) = 1 := by
  set A : Matrix (Fin 2) (Fin 2) ℂ := !![(2 : ℂ), 1; 0, 1] with hA
  set t : ℝ := (Real.sqrt 2)⁻¹ with ht
  have ht2 : t * t = 1 / 2 := inv_sqrt_two_mul_self
  have ht0 : 0 < t := inv_pos.2 (Real.sqrt_pos.2 (by norm_num))
  set Q₀ : Matrix (Fin 2) (Fin 1) ℂ := !![((t : ℝ) : ℂ); -((t : ℝ) : ℂ)] with hQ₀
  set q₀ : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![((t : ℝ) : ℂ), -((t : ℝ) : ℂ)] with hq₀
  -- `A Q₀ = Q₀`, hence `A^k Q₀ = Q₀`
  have hAQ : A * Q₀ = Q₀ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A, Q₀, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have hpow : ∀ k, A ^ k * Q₀ = Q₀ := by
    intro k
    induction k with
    | zero => rw [pow_zero, Matrix.one_mul]
    | succ k ih => rw [pow_succ', Matrix.mul_assoc, ih, hAQ]
  -- `ran Q_k = ran Q₀ = span{q₀}`
  have hrange0 : LinearMap.range (toEuclideanLin Q₀) = ℂ ∙ q₀ := by
    rw [range_toEuclideanLin_col]
    congr 2
    ext i
    fin_cases i <;> rfl
  have hrange : ∀ k, LinearMap.range (toEuclideanLin (Q k)) = ℂ ∙ q₀ := by
    intro k
    have hli : LinearIndependent ℂ (A ^ k * Q 0)ᵀ := by
      rw [h0, hpow]
      refine linearIndependent_unique_iff.2 fun h => ?_
      have := congrFun h 0
      simp [Q₀, ht0.ne'] at this
    rw [(orthogonalIteration_range hQ hli).1, h0, ← hrange0]
    ext x
    rw [Krylov.mem_subspaceIterate]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, rfl⟩ := hy
      refine ⟨z, ?_⟩
      rw [← toEuclideanLin_pow, ← toEuclideanLin_mul_apply, hpow]
    · intro hx
      obtain ⟨z, rfl⟩ := hx
      refine ⟨toEuclideanLin Q₀ z, ⟨z, rfl⟩, ?_⟩
      rw [← toEuclideanLin_pow, ← toEuclideanLin_mul_apply, hpow]
  have hq₀1 : ‖q₀‖ = 1 := by
    rw [norm_euclidean_two]
    simp [q₀, Complex.norm_real, abs_of_pos ht0, sq, ht2]
    norm_num
  have he1 : ‖EuclideanSpace.single (0 : Fin 2) (1 : ℂ)‖ = 1 := by simp
  have hc : ((t : ℝ) : ℂ) * ((t : ℝ) : ℂ) = 1 / 2 := by
    rw [← Complex.ofReal_mul, ht2]
    push_cast
    ring
  have hin : (inner ℂ q₀ (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) : ℂ) = ((t : ℝ) : ℂ) := by
    simp [q₀, EuclideanSpace.inner_single_right]
  -- `d_k = 1/√2`
  have hd : ∀ k, (ℂ ∙ EuclideanSpace.single (0 : Fin 2) (1 : ℂ)).gap
      (LinearMap.range (toEuclideanLin (Q k))) = t := by
    intro k
    have hv : EuclideanSpace.single (0 : Fin 2) (1 : ℂ) -
        (inner ℂ q₀ (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) / ((‖q₀‖ ^ 2 : ℝ) : ℂ)) • q₀ =
        WithLp.toLp 2 ![((1 / 2 : ℝ) : ℂ), ((1 / 2 : ℝ) : ℂ)] := by
      rw [hq₀1, hin]
      ext i
      fin_cases i
      · simp [q₀]
        linear_combination -hc
      · simp [q₀]
        linear_combination hc
    rw [Submodule.gap_congr _ _ (hrange k), Submodule.gap_span_singleton_eq_sinAngle he1 hq₀1,
      Submodule.sinAngle, he1, div_one, Submodule.starProjection_singleton]
    refine (congrArg norm hv).trans ?_
    rw [norm_euclidean_two]
    have e0 : ‖(WithLp.toLp 2 ![((1 / 2 : ℝ) : ℂ), ((1 / 2 : ℝ) : ℂ)] :
        EuclideanSpace ℂ (Fin 2)) 0‖ = 1 / 2 := by
      simp
    have e1 : ‖(WithLp.toLp 2 ![((1 / 2 : ℝ) : ℂ), ((1 / 2 : ℝ) : ℂ)] :
        EuclideanSpace ℂ (Fin 2)) 1‖ = 1 / 2 := by
      simp
    rw [e0, e1, ht, ← Real.sqrt_inv]
    congr 1
    norm_num
  -- `‖N‖_F = 1`
  have hN : ‖strictUpper A‖ = 1 := by
    have e : strictUpper A = !![0, 1; 0, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [A, strictUpper_apply]
    rw [e, frobenius_norm_def]
    simp [Fin.sum_univ_two]
  refine ⟨hN, fun k => (hd k).trans rfl, ?_, ?_, ?_⟩
  · rw [hN]
    have hr : (‖(1 : ℂ)‖ + 1 / (1 + 3)) / (‖(2 : ℂ)‖ - 1 / (1 + 3)) = (5 / 7 : ℝ) := by
      norm_num
    rw [hr]
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 5 / 7)
      (by norm_num)).const_mul ((1 + 3 : ℝ) ^ (2 - 2) *
        (1 + ‖!![(1 : ℂ)]‖ / sep !![(2 : ℂ)] !![(1 : ℂ)]))
    rw [mul_zero] at h
    simpa using h.mul_const ((ℂ ∙ EuclideanSpace.single (0 : Fin 2) (1 : ℂ)).gap
      (LinearMap.range (toEuclideanLin (Q 0))) / Real.sqrt (1 - (ℂ ∙ EuclideanSpace.single
        (0 : Fin 2) (1 : ℂ)).gap (LinearMap.range (toEuclideanLin (Q 0))) ^ 2))
  · ext i
    fin_cases i <;> simp [A, mulVec, dotProduct, Fin.sum_univ_two, map_ofNat]
    norm_num
  · set w : EuclideanSpace ℂ (Fin 2) :=
      WithLp.toLp 2 ![((t : ℝ) : ℂ), ((t : ℝ) : ℂ)] with hw
    have hw1 : ‖w‖ = 1 := by
      rw [norm_euclidean_two]
      simp [w, Complex.norm_real, abs_of_pos ht0, sq, ht2]
      norm_num
    rw [Submodule.gap_congr _ _ (hrange 0), Submodule.gap_span_singleton_eq_sinAngle hw1 hq₀1,
      Submodule.sinAngle, hw1, div_one, Submodule.starProjection_singleton]
    have hinner : (inner ℂ q₀ w : ℂ) = 0 := by
      simp [q₀, w, PiLp.inner_apply, Fin.sum_univ_two]
    rw [hinner, zero_div, zero_smul, sub_zero, hw1]

/-- If $Q$ is unitary, $Q^H A Q$ reindexed along $e$ is $\begin{bmatrix} T_{11} & T_{12} \\ 0 &
T_{22} \end{bmatrix}$, $T_{11} X - X T_{22} = -T_{12}$ and
$P = Q \begin{bmatrix} I \\ -X^H \end{bmatrix}$, then $(A^H)^k P = P (T_{11}^H)^k$ for every
$k$. -/
private theorem conjTranspose_pow_mul_eq {r : ℕ} {A Q : Matrix (Fin n) (Fin n) ℂ}
    (hQ : Q ∈ unitaryGroup (Fin n) ℂ) (e : Fin n ≃ Fin r ⊕ Fin (n - r))
    {T₁₁ : Matrix (Fin r) (Fin r) ℂ} {T₁₂ : Matrix (Fin r) (Fin (n - r)) ℂ}
    {T₂₂ : Matrix (Fin (n - r)) (Fin (n - r)) ℂ}
    (hT : (star Q * A * Q).reindex e e = fromBlocks T₁₁ T₁₂ 0 T₂₂)
    {X : Matrix (Fin r) (Fin (n - r)) ℂ} (hX : T₁₁ * X - X * T₂₂ = -T₁₂) (k : ℕ) :
    Aᴴ ^ k * (Q * (fromRows (1 : Matrix (Fin r) (Fin r) ℂ) (-Xᴴ)).submatrix e id) =
      Q * (fromRows (1 : Matrix (Fin r) (Fin r) ℂ) (-Xᴴ)).submatrix e id * T₁₁ᴴ ^ k := by
  set B := fromBlocks T₁₁ T₁₂ 0 T₂₂ with hBdef
  set M := fromRows (1 : Matrix (Fin r) (Fin r) ℂ) (-Xᴴ) with hM
  have hBM : Bᴴ * M = M * T₁₁ᴴ :=
    (equation_7_3_25 (A := B) (Q := 1) (one_mem _) (by simp [hBdef]) hX).2.1
  have hQQ : Q * star Q = 1 := mem_unitaryGroup_iff.1 hQ
  have hQQ' : star Q * Q = 1 := mem_unitaryGroup_iff'.1 hQ
  have hB : star Q * A * Q = B.submatrix e e := by
    rw [← hT, reindex_apply, submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id]
  have hA : A = Q * B.submatrix e e * star Q := by
    rw [← hB, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQQ, Matrix.one_mul, Matrix.mul_assoc,
      hQQ, Matrix.mul_one]
  have h1 : Aᴴ * (Q * M.submatrix e id) = Q * M.submatrix e id * T₁₁ᴴ := by
    have hAh : Aᴴ = Q * Bᴴ.submatrix e e * star Q := by
      rw [hA, conjTranspose_mul, conjTranspose_mul, ← star_eq_conjTranspose (star Q), star_star,
        conjTranspose_submatrix, star_eq_conjTranspose, Matrix.mul_assoc]
    rw [hAh, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (star Q), hQQ',
      Matrix.one_mul, submatrix_mul_equiv, hBM,
      submatrix_mul _ _ _ _ _ Function.bijective_id, submatrix_id_id, Matrix.mul_assoc]
  induction k with
  | zero => rw [pow_zero, pow_zero, Matrix.one_mul, Matrix.mul_one]
  | succ k ih =>
    rw [pow_succ, Matrix.mul_assoc, h1, ← Matrix.mul_assoc, ih, pow_succ, Matrix.mul_assoc]

/-- The partition (7.3.8) of the indices: for $r \le n$, the bijection of `Fin n` with
`Fin r ⊕ Fin (n - r)` that sends the first $r$ indices to the left summand and the last $n - r$
indices to the right summand. After reindexing along it, a block Schur form $Q^H A Q$ is
$\begin{bmatrix} T_{11} & T_{12} \\ 0 & T_{22} \end{bmatrix}$ with $T_{11}$ of size $r$. -/
def schurSplit {r : ℕ} (h : r ≤ n) : Fin n ≃ Fin r ⊕ Fin (n - r) :=
  (finCongr (by omega : n = r + (n - r))).trans finSumFinEquiv.symm

/-- Under the partition (7.3.8), the index $i < r$ of the first block is the index $i$ of `Fin n`.
-/
theorem schurSplit_symm_inl {r : ℕ} (h : r ≤ n) (i : Fin r) :
    (schurSplit h).symm (Sum.inl i) = Fin.castLE h i := by
  ext
  simp [schurSplit]

/-- Under the partition (7.3.8), the index $j$ of the second block is the index $r + j$ of `Fin n`.
-/
theorem schurSplit_symm_inr {r : ℕ} (h : r ≤ n) (j : Fin (n - r)) :
    ((schurSplit h).symm (Sum.inr j) : ℕ) = r + j := by
  simp [schurSplit]

section Split

variable {r : ℕ} (h : r ≤ n)

/-- If $R$ is upper triangular, the first $r$ columns of $P R$ are the first $r$ columns of $P$
times the leading $r \times r$ block of $R$. -/
private theorem mul_submatrix_castLE {m : ℕ} (P : Matrix (Fin m) (Fin n) ℂ)
    {R : Matrix (Fin n) (Fin n) ℂ} (hR : R.IsUpperTriangular) :
    (P * R).submatrix id (Fin.castLE h) =
      P.submatrix id (Fin.castLE h) * R.submatrix (Fin.castLE h) (Fin.castLE h) := by
  ext p l
  simp only [submatrix_apply, id, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ ?_ fun _ => rfl
  intro j hj
  have hjl : Fin.castLE h l < j := by
    rw [Fin.lt_def, Fin.val_castLE]
    by_contra hc
    exact hj ⟨⟨j, by omega⟩, Fin.ext (by simp)⟩
  exact mul_eq_zero_of_right _ (hR hjl)

/-- The first $r$ columns of an orthogonal iteration with square iterates form an orthogonal
iteration. -/
private theorem orthogonalIteration_castLE {A : Matrix (Fin n) (Fin n) ℂ}
    {Qk : ℕ → Matrix (Fin n) (Fin n) ℂ} (hQk : orthogonalIteration A Qk) :
    orthogonalIteration A fun k => (Qk k).submatrix id (Fin.castLE h) := by
  have hsub : ∀ M : Matrix (Fin n) (Fin n) ℂ, Mᴴ * M = 1 →
      (M.submatrix id (Fin.castLE h))ᴴ * M.submatrix id (Fin.castLE h) = 1 := by
    intro M hM
    rw [conjTranspose_submatrix, ← submatrix_mul _ _ _ _ _ Function.bijective_id, hM]
    ext i j
    simp [Matrix.one_apply, Fin.ext_iff]
  refine ⟨hsub _ hQk.1, fun k => ?_⟩
  obtain ⟨R, hR⟩ := hQk.2 k
  refine ⟨R.submatrix (Fin.castLE h) (Fin.castLE h), ⟨?_, hsub _ hR.conjTranspose_mul_self, ?_⟩⟩
  · rw [← mul_submatrix_castLE h _ hR.isUpperTriangular, hR.mul_eq,
      submatrix_mul _ _ _ _ _ Function.bijective_id, submatrix_id_id]
  · intro i j hij
    exact hR.isUpperTriangular (show Fin.castLE h j < Fin.castLE h i from hij)

/-- Under the partition (7.3.8), $Q \begin{bmatrix} I \\ 0 \end{bmatrix}$ is $Q_\alpha$, the matrix
of the first $r$ columns of $Q$. -/
private theorem mul_fromRows_one_zero_submatrix (Q : Matrix (Fin n) (Fin n) ℂ) :
    Q * (fromRows (1 : Matrix (Fin r) (Fin r) ℂ)
      (0 : Matrix (Fin (n - r)) (Fin r) ℂ)).submatrix (schurSplit h) id =
      Q.submatrix id (Fin.castLE h) := by
  have e1 : (fromRows (1 : Matrix (Fin r) (Fin r) ℂ)
      (0 : Matrix (Fin (n - r)) (Fin r) ℂ)).submatrix (schurSplit h) id =
      (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id (Fin.castLE h) := by
    ext j l
    simp only [submatrix_apply, id]
    rcases hj : schurSplit h j with a | b
    · have hja : j = Fin.castLE h a := by
        rw [← schurSplit_symm_inl h a, ← hj, Equiv.symm_apply_apply]
      subst hja
      simp [Matrix.one_apply, Fin.ext_iff]
    · have hjb : (j : ℕ) = r + b := by
        rw [← schurSplit_symm_inr h b, ← hj, Equiv.symm_apply_apply]
      have hne : j ≠ Fin.castLE h l := fun h' => by
        rw [h', Fin.val_castLE] at hjb
        omega
      simp [hne]
  rw [e1]
  exact mul_submatrix_one (Equiv.refl _) (Fin.castLE h) Q

end Split

open scoped Matrix.Norms.L2Operator in
/-- Every matrix $A$ acts on `EuclideanSpace ℂ (Fin n)` as a bounded operator: there is $M \ge 0$
with $\|A y\| \le M \|y\|$ for every $y$. -/
private theorem exists_norm_toEuclideanLin_le (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y, ‖toEuclideanLin A y‖ ≤ M * ‖y‖ :=
  ⟨‖A‖, norm_nonneg _, norm_toEuclideanLin_apply_le A⟩

open scoped Matrix.Norms.Frobenius

/-- **Theorem 7.3.1** of [golub2013matrix], corrected. Let $A, Q \in \mathbb{C}^{n \times n}$ with
$Q$ unitary, let $0 < r < n$, and let
$$Q^H A Q = \begin{bmatrix} T_{11} & T_{12} \\ 0 & T_{22} \end{bmatrix}$$
be a block Schur form as in (7.3.7)–(7.3.8), with $T_{11} \in \mathbb{C}^{r \times r}$, and with
$T_{11}$ and $T_{22}$ upper triangular. Let $N_{11}$ and $N_{22}$ be the strictly upper
triangular parts of $T_{11}$ and $T_{22}$. Let $a$, $b$, $\nu$ and $\mu$ be real numbers with
$|t_{ii}| \ge a$ on the diagonal of $T_{11}$, $|t_{jj}| \le b$ on the diagonal of $T_{22}$,
$b < a$, $\|N_{11}\|_F \le \nu$, $\|N_{22}\|_F \le \nu$, $\mu \ge 0$ and $\nu < (1 + \mu) a$.
Let $X$ solve $T_{11} X - X T_{22} = -T_{12}$, as in (7.3.20). Let
$Q_0, Q_1, \dots \in \mathbb{C}^{n \times r}$ be an orthogonal iteration (7.3.6) for $A$, and
let
$$d_k = \operatorname{dist}(D_r(A), \operatorname{ran}(Q_k)), \qquad \tilde d_0 =
  \operatorname{dist}(D_r(A^H), \operatorname{ran}(Q_0)),$$
where $D_r(A) = \operatorname{ran}(Q \begin{bmatrix} I \\ 0 \end{bmatrix})$, and $D_r(A^H) =
\operatorname{ran}(Q \begin{bmatrix} I \\ -X^H \end{bmatrix})$ is the dominant invariant
subspace of $A^H$ by (7.3.25). If $\tilde d_0 < 1$, then for every $k \ge 0$
$$d_k \le (1 + \mu)^{n-2} \left( 1 + \frac{\|T_{12}\|_F}{\operatorname{sep}(T_{11}, T_{22})}
  \right) \left( \frac{b + \nu / (1 + \mu)}{a - \nu / (1 + \mu)} \right)^k \frac{d_0}{\sqrt{1 -
  \tilde d_0^2}}.$$

**Correction.** The printed theorem assumes (7.3.9) and has $\sqrt{1 - d_0^2}$ in the
denominator of (7.3.10). That statement is false: the example of
`GolubVanLoan.Chapter07.theorem_7_3_1_counterexample` satisfies (7.3.9), and its printed bound
tends to $0$ while $d_k = 1/\sqrt 2$ for every $k$. The proof in the source needs
$\tilde d_0 < 1$, and it replaces $\tilde d_0$ by $d_0$ through a false claim (see
`GolubVanLoan.Chapter07.equation_7_3_26`). The statement here assumes $\tilde d_0 < 1$ in place
of (7.3.9).

**Generalization.** The source has $a = |\lambda_r|$, $b = |\lambda_{r+1}|$ and $\nu = \|N\|_F$
for the strictly upper triangular part $N$ of the Schur form. Here any bounds $a$, $b$ and $\nu$
with the stated properties suffice.

Because no vector of $\operatorname{ran}(Q_0)$ is orthogonal to $D_r(A^H)$ and $A^H$ is
invertible on $D_r(A^H)$, the matrix $A^k Q_0$ has full column rank. So
$\operatorname{ran}(Q_k) = A^k \operatorname{ran}(Q_0)$, and the backbone's bound for subspace
iteration applies. The block form is stated after reindexing along any bijection
`e : Fin n ≃ Fin r ⊕ Fin (n - r)`; the partition (7.3.8) is `GolubVanLoan.Chapter07.schurSplit`.
The distance is the gap `Submodule.gap`. -/
theorem theorem_7_3_1 {r : ℕ} {A Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q ∈ unitaryGroup (Fin n) ℂ)
    (e : Fin n ≃ Fin r ⊕ Fin (n - r)) {T₁₁ : Matrix (Fin r) (Fin r) ℂ}
    {T₁₂ : Matrix (Fin r) (Fin (n - r)) ℂ} {T₂₂ : Matrix (Fin (n - r)) (Fin (n - r)) ℂ}
    (hT : (star Q * A * Q).reindex e e = fromBlocks T₁₁ T₁₂ 0 T₂₂)
    (hT₁₁ : T₁₁.IsUpperTriangular) (hT₂₂ : T₂₂.IsUpperTriangular) (hr : 0 < r) (hrn : r < n)
    {a b ν μ : ℝ} (hμ : 0 ≤ μ) (ha : ∀ i, a ≤ ‖T₁₁ i i‖) (hb : ∀ j, ‖T₂₂ j j‖ ≤ b)
    (hab : b < a) (hν₁ : ‖strictUpper T₁₁‖ ≤ ν) (hν₂ : ‖strictUpper T₂₂‖ ≤ ν)
    (hνa : ν < (1 + μ) * a) {X : Matrix (Fin r) (Fin (n - r)) ℂ}
    (hX : T₁₁ * X - X * T₂₂ = -T₁₂) {Qk : ℕ → Matrix (Fin n) (Fin r) ℂ}
    (hQk : orthogonalIteration A Qk)
    (h0 : (LinearMap.range (toEuclideanLin
      (Q * (fromRows (1 : Matrix (Fin r) (Fin r) ℂ) (-Xᴴ)).submatrix e id))).gap
        (LinearMap.range (toEuclideanLin (Qk 0))) < 1)
    (k : ℕ) :
    (LinearMap.range (toEuclideanLin (Q * (fromRows (1 : Matrix (Fin r) (Fin r) ℂ)
        (0 : Matrix (Fin (n - r)) (Fin r) ℂ)).submatrix e id))).gap
        (LinearMap.range (toEuclideanLin (Qk k))) ≤
      (1 + μ) ^ (n - 2) * (1 + ‖T₁₂‖ / sep T₁₁ T₂₂) *
        ((b + ν / (1 + μ)) / (a - ν / (1 + μ))) ^ k *
        ((LinearMap.range (toEuclideanLin (Q * (fromRows (1 : Matrix (Fin r) (Fin r) ℂ)
          (0 : Matrix (Fin (n - r)) (Fin r) ℂ)).submatrix e id))).gap
            (LinearMap.range (toEuclideanLin (Qk 0))) /
          Real.sqrt (1 - (LinearMap.range (toEuclideanLin
            (Q * (fromRows (1 : Matrix (Fin r) (Fin r) ℂ) (-Xᴴ)).submatrix e id))).gap
              (LinearMap.range (toEuclideanLin (Qk 0))) ^ 2)) := by
  have hconj := conjTranspose_pow_mul_eq hQ e hT hX k
  have h0' := h0
  generalize hPdef : Q * (fromRows (1 : Matrix (Fin r) (Fin r) ℂ) (-Xᴴ)).submatrix e id = P
    at h0' hconj
  set S₀ := LinearMap.range (toEuclideanLin (Qk 0)) with hS₀
  have hQ0 : (Qk 0)ᴴ * Qk 0 = 1 := hQk.1
  -- `T₁₁` is invertible
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb ⟨0, by omega⟩)
  have hT₁₁u : IsUnit T₁₁.det := by
    rw [det_of_isUpperTriangular hT₁₁, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro i _ h
    have := ha i
    rw [h, norm_zero] at this
    linarith
  have hTk : IsUnit (T₁₁ᴴ ^ k).det := by
    rw [det_pow, det_conjTranspose]
    exact (hT₁₁u.star).pow k
  -- `A^k` is injective on `ran Q₀`: a killed vector is orthogonal to `D_r(Aᴴ)`
  have hker : ∀ v ∈ S₀, (toEuclideanLin A ^ k) v = 0 → v = 0 := by
    intro v hv hAv
    refine Submodule.eq_zero_of_starProjection_eq_zero_of_gap_lt_one _ S₀ h0' hv ?_
    refine (Submodule.starProjection_apply_eq_zero_iff _).2 ((Submodule.mem_orthogonal _ _).2 ?_)
    rintro _ ⟨y, rfl⟩
    set y' := toEuclideanLin (T₁₁ᴴ ^ k)⁻¹ y
    have hy : toEuclideanLin P y = toEuclideanLin (Aᴴ ^ k) (toEuclideanLin P y') := by
      rw [← toEuclideanLin_mul_apply (Aᴴ ^ k), hconj, toEuclideanLin_mul_apply P,
        ← toEuclideanLin_mul_apply (T₁₁ᴴ ^ k), mul_nonsing_inv _ hTk, toLpLin_one,
        LinearMap.id_apply]
    rw [hy, ← conjTranspose_pow, toEuclideanLin_conjTranspose_eq_adjoint,
      LinearMap.adjoint_inner_left, toEuclideanLin_pow, hAv, inner_zero_right]
  -- hence `A^k Q₀` has full column rank
  have hli : LinearIndependent ℂ (A ^ k * Qk 0)ᵀ := by
    refine mulVec_injective_iff.1 fun c c' hcc => ?_
    have hd : (A ^ k * Qk 0) *ᵥ (c - c') = 0 := by rw [mulVec_sub, hcc, sub_self]
    set v := toEuclideanLin (Qk 0) (WithLp.toLp 2 (c - c'))
    have hv0 : v = 0 := by
      refine hker v ⟨_, rfl⟩ ?_
      rw [← toEuclideanLin_pow, ← toEuclideanLin_mul_apply, toEuclideanLin_toLp, hd,
        WithLp.toLp_zero]
    have hn : ‖v‖ = ‖(WithLp.toLp 2 (c - c') : EuclideanSpace ℂ (Fin r))‖ :=
      norm_toEuclideanLin_apply_of_conjTranspose_mul_self_eq_one hQ0 _
    rw [hv0, norm_zero, eq_comm, norm_eq_zero, WithLp.toLp_eq_zero] at hn
    exact sub_eq_zero.1 hn
  -- `dim ran Q₀ = r`
  have hdim : Module.finrank ℂ S₀ = r := by
    have hinj : Function.Injective (toEuclideanLin (Qk 0)) := by
      refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
      have hn := norm_toEuclideanLin_apply_of_conjTranspose_mul_self_eq_one hQ0 y
      rw [hy, norm_zero, eq_comm, norm_eq_zero] at hn
      exact hn
    rw [hS₀, LinearMap.finrank_range_of_inj hinj, finrank_euclideanSpace, Fintype.card_fin]
  subst hPdef
  have key := gap_subspaceIterate_le_of_schur hQ e hT hT₁₁ hT₂₂ hr hrn hμ ha hb hab hν₁ hν₂ hνa
    hX hdim h0 k
  exact (le_of_eq (Submodule.gap_congr _ _ (orthogonalIteration_range hQk hli).1)).trans key

/-- **Equation (7.3.11)** of [golub2013matrix], and the conclusion of §7.3.3 drawn from it. Let
$A, Q \in \mathbb{C}^{n \times n}$ with $Q = [q_1 \mid \cdots \mid q_n]$ unitary and
$T = Q^H A Q$ upper triangular with $|t_{11}| > |t_{22}| > \cdots > |t_{nn}|$. Let
$Q_0, Q_1, \dots \in \mathbb{C}^{n \times n}$ be an orthogonal iteration (7.3.6) with $r = n$,
and let $q_1^{(k)}, \dots, q_n^{(k)}$ be the columns of $Q_k$. For $1 \le i \le n - 1$ let
$T_{11}$, $T_{12}$, $T_{22}$ be the blocks of $T$ for the partition (7.3.8) with $r = i$. Assume
that for every such $i$ there is a solution $X_i$ of $T_{11} X_i - X_i T_{22} = -T_{12}$ with
$$\operatorname{dist}(D_i(A^H), \operatorname{span}\{q_1^{(0)}, \dots, q_i^{(0)}\}) < 1, \qquad
  D_i(A^H) = \operatorname{ran}\left( Q \begin{bmatrix} I \\ -X_i^H \end{bmatrix} \right).$$
Then for every $i$ with $1 \le i \le n - 1$
$$\operatorname{dist}(\operatorname{span}\{q_1, \dots, q_i\}, \operatorname{span}\{q_1^{(k)},
  \dots, q_i^{(k)}\}) \to 0 \qquad (k \to \infty),$$
and the matrices $T_k = Q_k^H A Q_k$ converge to upper triangular form: every entry of $T_k$
below the diagonal tends to $0$.

The hypothesis on $Q_0$ is the one of the corrected Theorem 7.3.1,
`GolubVanLoan.Chapter07.theorem_7_3_1`. The proof applies that theorem with $r = i$ to the first
$i$ columns of $Q_k$, which again form an orthogonal iteration. It bounds the entry
$(T_k)_{jl} = \langle q_j^{(k)}, A q_l^{(k)} \rangle$ by the gap with
`Krylov.norm_inner_le_of_gap`. The case $i = n$ is trivial, because both spans are the whole
space. -/
theorem equation_7_3_11 {A Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q ∈ unitaryGroup (Fin n) ℂ)
    (hT : (star Q * A * Q).IsUpperTriangular)
    (hdiag : StrictAnti fun i => ‖(star Q * A * Q) i i‖)
    {Qk : ℕ → Matrix (Fin n) (Fin n) ℂ} (hQk : orthogonalIteration A Qk)
    (h0 : ∀ i, 0 < i → ∀ hin : i < n, ∃ X : Matrix (Fin i) (Fin (n - i)) ℂ,
      ((star Q * A * Q).reindex (schurSplit hin.le) (schurSplit hin.le)).toBlocks₁₁ * X -
          X * ((star Q * A * Q).reindex (schurSplit hin.le) (schurSplit hin.le)).toBlocks₂₂ =
        -((star Q * A * Q).reindex (schurSplit hin.le) (schurSplit hin.le)).toBlocks₁₂ ∧
      (LinearMap.range (toEuclideanLin (Q * (fromRows (1 : Matrix (Fin i) (Fin i) ℂ)
        (-Xᴴ)).submatrix (schurSplit hin.le) id))).gap
        (LinearMap.range (toEuclideanLin ((Qk 0).submatrix id (Fin.castLE hin.le)))) < 1) :
    (∀ i, 0 < i → ∀ hin : i < n, Tendsto (fun k =>
        (LinearMap.range (toEuclideanLin (Q.submatrix id (Fin.castLE hin.le)))).gap
          (LinearMap.range (toEuclideanLin ((Qk k).submatrix id (Fin.castLE hin.le)))))
        atTop (𝓝 0)) ∧
      ∀ j l : Fin n, l < j → Tendsto (fun k => ((Qk k)ᴴ * A * Qk k) j l) atTop (𝓝 0) := by
  set T := star Q * A * Q with hTdef
  have hconv : ∀ i, 0 < i → ∀ hin : i < n, Tendsto (fun k =>
      (LinearMap.range (toEuclideanLin (Q.submatrix id (Fin.castLE hin.le)))).gap
        (LinearMap.range (toEuclideanLin ((Qk k).submatrix id (Fin.castLE hin.le)))))
      atTop (𝓝 0) := by
    intro i hi hin
    obtain ⟨X, hX, hgap⟩ := h0 i hi hin
    set e := schurSplit hin.le with he
    set B := T.reindex e e with hB
    -- the blocks
    have he1 : ∀ a : Fin i, e.symm (Sum.inl a) = Fin.castLE hin.le a :=
      schurSplit_symm_inl hin.le
    have he2 : ∀ b : Fin (n - i), ((e.symm (Sum.inr b) : Fin n) : ℕ) = i + b :=
      schurSplit_symm_inr hin.le
    have hblk : B = fromBlocks B.toBlocks₁₁ B.toBlocks₁₂ 0 B.toBlocks₂₂ := by
      conv_lhs => rw [← fromBlocks_toBlocks B]
      congr 1
      ext b a
      simp only [toBlocks₂₁, of_apply, Matrix.zero_apply, hB, reindex_apply, submatrix_apply]
      refine hT ?_
      simp only [id_eq, Fin.lt_def, he1, Fin.val_castLE, he2]
      omega
    have hT₁₁ : B.toBlocks₁₁.IsUpperTriangular := by
      intro a a' haa
      simp only [toBlocks₁₁, of_apply, hB, reindex_apply, submatrix_apply, he1]
      exact hT (show Fin.castLE hin.le a' < Fin.castLE hin.le a from haa)
    have hT₂₂ : B.toBlocks₂₂.IsUpperTriangular := by
      intro b b' hbb
      simp only [toBlocks₂₂, of_apply, hB, reindex_apply, submatrix_apply]
      refine hT ?_
      simp only [id_eq, Fin.lt_def, he2] at hbb ⊢
      omega
    -- the constants
    set a := ‖T ⟨i - 1, by omega⟩ ⟨i - 1, by omega⟩‖ with ha_def
    set b := ‖T ⟨i, hin⟩ ⟨i, hin⟩‖ with hb_def
    set ν := ‖strictUpper T‖ with hν_def
    have ha : ∀ a' : Fin i, a ≤ ‖B.toBlocks₁₁ a' a'‖ := by
      intro a'
      simp only [toBlocks₁₁, of_apply, hB, reindex_apply, submatrix_apply, he1]
      refine hdiag.antitone ?_
      rw [Fin.le_def, Fin.val_castLE]
      change (a' : ℕ) ≤ i - 1
      omega
    have hb : ∀ b' : Fin (n - i), ‖B.toBlocks₂₂ b' b'‖ ≤ b := by
      intro b'
      simp only [toBlocks₂₂, of_apply, hB, reindex_apply, submatrix_apply]
      refine hdiag.antitone ?_
      rw [Fin.le_def, he2]
      change i ≤ i + (b' : ℕ)
      omega
    have hab : b < a := hdiag (show (⟨i - 1, by omega⟩ : Fin n) < ⟨i, hin⟩ by
      rw [Fin.lt_def]; simp only; omega)
    have hb0 : 0 ≤ b := norm_nonneg _
    have ha0 : 0 < a := hb0.trans_lt hab
    have hν0 : 0 ≤ ν := norm_nonneg _
    have hν₁ : ‖strictUpper B.toBlocks₁₁‖ ≤ ν := by
      have e1 : strictUpper B.toBlocks₁₁ =
          (strictUpper T).submatrix (Fin.castLE hin.le) (Fin.castLE hin.le) := by
        ext a' a''
        simp only [strictUpper_apply, submatrix_apply, toBlocks₁₁, of_apply, hB, reindex_apply,
          he1]
        congr 1
      rw [e1]
      exact frobenius_norm_submatrix_le _ (Fin.castLE_injective _) (Fin.castLE_injective _)
    have hν₂ : ‖strictUpper B.toBlocks₂₂‖ ≤ ν := by
      have hinj : Function.Injective fun b' : Fin (n - i) => e.symm (Sum.inr b') :=
        e.symm.injective.comp Sum.inr_injective
      have e1 : strictUpper B.toBlocks₂₂ =
          (strictUpper T).submatrix (fun b' => e.symm (Sum.inr b'))
            (fun b' => e.symm (Sum.inr b')) := by
        ext b' b''
        simp only [strictUpper_apply, submatrix_apply, toBlocks₂₂, of_apply, hB, reindex_apply]
        congr 1
        refine propext ⟨fun hlt => ?_, fun hlt => ?_⟩
        · rw [Fin.lt_def, he2, he2]; have := Fin.lt_def.1 hlt; omega
        · rw [Fin.lt_def, he2, he2] at hlt; rw [Fin.lt_def]; omega
      rw [e1]
      exact frobenius_norm_submatrix_le _ hinj hinj
    set μ := 4 * ν / (a - b) with hμ_def
    have hμ : 0 ≤ μ := div_nonneg (by positivity) (by linarith)
    have h1μ : 0 < 1 + μ := by linarith
    have hc : ν / (1 + μ) ≤ (a - b) / 4 := by
      rw [div_le_iff₀ h1μ, hμ_def]
      have hab' : 0 < a - b := by linarith
      field_simp
      nlinarith
    have hνa : ν < (1 + μ) * a := by
      have h' : ν / (1 + μ) < a := hc.trans_lt (by linarith)
      rw [div_lt_iff₀ h1μ] at h'
      linarith [mul_comm a (1 + μ)]
    set ρ := (b + ν / (1 + μ)) / (a - ν / (1 + μ)) with hρ_def
    have hden : 0 < a - ν / (1 + μ) := by linarith
    have hρ0 : 0 ≤ ρ := div_nonneg (by positivity) hden.le
    have hρ1 : ρ < 1 := by
      rw [div_lt_one hden]
      linarith
    have hbound := fun k => theorem_7_3_1 hQ e hblk hT₁₁ hT₂₂ hi hin hμ ha hb hab
      hν₁ hν₂ hνa hX (orthogonalIteration_castLE hin.le hQk) hgap k
    have hQα : Q * (fromRows (1 : Matrix (Fin i) (Fin i) ℂ)
        (0 : Matrix (Fin (n - i)) (Fin i) ℂ)).submatrix e id = Q.submatrix id (Fin.castLE hin.le) :=
      mul_fromRows_one_zero_submatrix hin.le Q
    simp only [hQα] at hbound
    refine squeeze_zero (fun _ => Submodule.gap_nonneg _ _) hbound ?_
    have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul
      ((1 + μ) ^ (n - 2) * (1 + ‖B.toBlocks₁₂‖ / sep B.toBlocks₁₁ B.toBlocks₂₂))).mul_const
      ((LinearMap.range (toEuclideanLin (Q.submatrix id (Fin.castLE hin.le)))).gap
          (LinearMap.range (toEuclideanLin ((Qk 0).submatrix id (Fin.castLE hin.le)))) /
        Real.sqrt (1 - (LinearMap.range (toEuclideanLin
          (Q * (fromRows (1 : Matrix (Fin i) (Fin i) ℂ) (-Xᴴ)).submatrix e id))).gap
          (LinearMap.range (toEuclideanLin ((Qk 0).submatrix id (Fin.castLE hin.le)))) ^ 2))
    simpa [mul_assoc] using h
  refine ⟨hconv, fun j l hlj => ?_⟩
  have hl : (l : ℕ) + 1 < n := by have := Fin.lt_def.1 hlj; omega
  have hlt := hconv ((l : ℕ) + 1) (Nat.succ_pos _) hl
  set f := Fin.castLE hl.le with hf
  obtain ⟨M, hM0, hM⟩ := exists_norm_toEuclideanLin_le A
  -- `span{q₁, …, q_{l+1}}` is `A`-invariant
  have hAQ : A * Q = Q * T := by
    rw [hTdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mem_unitaryGroup_iff.1 hQ, Matrix.one_mul]
  have hinvM : A * Q.submatrix id f = Q.submatrix id f * T.submatrix f f := by
    rw [← mul_submatrix_castLE hl.le Q hT, ← hAQ, submatrix_mul _ _ _ _ _ Function.bijective_id,
      submatrix_id_id]
  have hinv : ∀ y ∈ LinearMap.range (toEuclideanLin (Q.submatrix id f)),
      toEuclideanLin A y ∈ LinearMap.range (toEuclideanLin (Q.submatrix id f)) := by
    rintro _ ⟨z, rfl⟩
    exact ⟨toEuclideanLin (T.submatrix f f) z, by
      rw [← toEuclideanLin_mul_apply, ← hinvM, toEuclideanLin_mul_apply]⟩
  -- the iterates have orthonormal columns
  have hunit : ∀ k, (Qk k)ᴴ * Qk k = 1 := fun k => by
    cases k with
    | zero => exact hQk.1
    | succ k => exact (hQk.2 k).choose_spec.conjTranspose_mul_self
  have happ : ∀ (P : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n),
      (toEuclideanLin P (EuclideanSpace.single q 1)) p = P p q := by
    intro P p q
    simp [toEuclideanLin_apply]
  have hbound : ∀ k, ‖((Qk k)ᴴ * A * Qk k) j l‖ ≤ 2 * M *
      (LinearMap.range (toEuclideanLin (Q.submatrix id f))).gap
        (LinearMap.range (toEuclideanLin ((Qk k).submatrix id f))) := by
    intro k
    set v := toEuclideanLin (Qk k) (EuclideanSpace.single l 1) with hv
    set w := toEuclideanLin (Qk k) (EuclideanSpace.single j 1) with hw
    have hvS : v ∈ LinearMap.range (toEuclideanLin ((Qk k).submatrix id f)) := by
      refine ⟨EuclideanSpace.single ⟨l, by omega⟩ 1, ?_⟩
      ext p
      rw [hv, happ]
      simp [toEuclideanLin_apply, hf]
    have hwS : w ∈ (LinearMap.range (toEuclideanLin ((Qk k).submatrix id f)))ᗮ := by
      refine (Submodule.mem_orthogonal _ _).2 ?_
      rintro _ ⟨z, rfl⟩
      rw [hw, ← LinearMap.adjoint_inner_right, ← toEuclideanLin_conjTranspose_eq_adjoint,
        ← toEuclideanLin_mul_apply, conjTranspose_submatrix,
        show (Qk k)ᴴ.submatrix f id * Qk k = ((Qk k)ᴴ * Qk k).submatrix f id from rfl, hunit]
      have h0' : toEuclideanLin ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix f id)
          (EuclideanSpace.single j 1) = 0 := by
        ext a
        have hne : f a ≠ j := fun h' => by
          have := Fin.val_eq_of_eq h'
          rw [hf, Fin.val_castLE] at this
          have := Fin.lt_def.1 hlj
          omega
        simp [toEuclideanLin_apply, hne]
      rw [h0', inner_zero_right]
    have hnv : ‖v‖ ≤ 1 := by
      rw [hv, norm_toEuclideanLin_apply_of_conjTranspose_mul_self_eq_one (hunit k)]
      simp
    have hnw : ‖w‖ ≤ 1 := by
      rw [hw, norm_toEuclideanLin_apply_of_conjTranspose_mul_self_eq_one (hunit k)]
      simp
    have hentry : ((Qk k)ᴴ * A * Qk k) j l = inner ℂ w (toEuclideanLin A v) := by
      rw [hw, hv, ← LinearMap.adjoint_inner_right, ← toEuclideanLin_conjTranspose_eq_adjoint,
        ← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply,
        EuclideanSpace.inner_single_left, map_one, one_mul, happ, Matrix.mul_assoc]
    rw [hentry]
    exact Krylov.norm_inner_le_of_gap hM0 hM hinv hvS hnv hwS hnw
  refine squeeze_zero_norm hbound ?_
  simpa using hlt.const_mul (2 * M)

end GolubVanLoan.Chapter07

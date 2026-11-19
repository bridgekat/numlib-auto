/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Krylov.Arnoldi
import Numlib.Krylov.Hessenberg
import Numlib.Krylov.Iterate
import Numlib.Krylov.QuasiMinRes
import Numlib.Krylov.Relations
import Numlib.Krylov.Subspace
import Numlib.Projection.Basic
import NumlibSurface.SaadSparse.Chapter06.Common
import NumlibSurface.SaadSparse.Chapter06.Section03
import NumlibSurface.SaadSparse.Chapter06.Section04

/-!
# Saad, Section 6.5: GMRES

This module formalizes Section 6.5 of [saad2003iterative], the generalized minimal residual method
(GMRES), together with the problems P-6.5, P-6.9, P-6.13, P-6.14, P-6.25 and P-6.26. Let
$\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let $A \in \mathbb{K}^{n \times n}$,
$b, x_0 \in \mathbb{K}^n$, $r_0 = b - Ax_0$, $\beta = \|r_0\|_2$ and $v_1 = r_0 / \beta$. After $m$
steps of the Arnoldi process, with basis $V_m = [v_1, \dots, v_m]$ and Hessenberg matrix
$\bar H_m \in \mathbb{K}^{(m+1) \times m}$, GMRES takes the approximation $x_m = x_0 + V_m y_m$,
where $y_m$ minimizes $J(y) = \|\beta e_1 - \bar H_m y\|_2$. This is the vector of
$x_0 + \mathcal{K}_m(A, r_0)$ with the smallest residual norm. Givens rotations
$\Omega_1, \dots, \Omega_m$ with product $Q_m$ reduce $\bar H_m$ to the triangular factor
$\bar R_m = Q_m \bar H_m$ and $\beta e_1$ to $\bar g_m = Q_m(\beta e_1)$, whose last entry is
$\gamma_{m+1}$. Then $y_m = R_m^{-1} g_m$, where $R_m$ and $g_m$ drop the last row and entry, and
the residual norm is $|\gamma_{m+1}|$.

The module also covers Householder GMRES (Algorithm 6.10), restarted GMRES (Algorithm 6.11), the
quasi-minimal-residual methods QGMRES and DQGMRES on a non-orthogonal basis with the bound of Freund
and Nachtigal (Theorem 6.11), the relations between the residual norms of FOM and GMRES
(Propositions 6.12–6.17), residual smoothing (Algorithm 6.14 and Lemma 6.18), and complex GMRES
(Section 6.5.9). The proofs specialize the Givens rotations of `Numlib.Krylov.Hessenberg`, the
minimal-residual and Galerkin specifications of `Numlib.Krylov.Iterate`, the relations of
`Numlib.Krylov.Relations` and the quasi-minimal-residual theory of `Numlib.Krylov.QuasiMinRes`.

## Main definitions

* Equation (6.25), `SaadSparse.Chapter06.krylovIterate`: the vector $x_0 + V_m y$.
* Equations (6.26) and (6.28), `SaadSparse.Chapter06.J`: the least-squares function
  $J(y) = \|\beta e_1 - \bar H_m y\|_2$.
* Algorithm 6.9, `SaadSparse.Chapter06.IsGMRESIterate`: $x = x_0 + V_m y_m$ with $y_m$ a minimizer
  of $J$.
* Algorithm 6.9, `SaadSparse.Chapter06.gmresFixed` and `SaadSparse.Chapter06.gmres`: GMRES for
  exactly $m$ steps, and with the stopping rule "if $h_{j+1,j} = 0$ set $m := j$".
* Equations (6.31)–(6.33), `SaadSparse.Chapter06.hornerAccumulate`: the accumulation
  $z := P_j(\eta_j e_j + z)$ of Algorithm 6.10.
* Algorithm 6.10, `SaadSparse.Chapter06.gmresHH`: Householder GMRES.
* Equations (6.34) and (6.80), `SaadSparse.Chapter06.Ω`: the Givens rotation $\Omega_{i+1}$.
* Equations (6.37) and (6.81), `SaadSparse.Chapter06.c` and `SaadSparse.Chapter06.s`: the rotation
  parameters $c_{i+1}$ and $s_{i+1}$.
* Equation (6.38), `SaadSparse.Chapter06.Qrot`: the product $Q_m = \Omega_m \cdots \Omega_1$.
* Equation (6.39), `SaadSparse.Chapter06.Rbar` and `SaadSparse.Chapter06.R`: the triangular factor
  $\bar R_m = Q_m \bar H_m$ and its square part $R_m$.
* Equation (6.40), `SaadSparse.Chapter06.gbar` and `SaadSparse.Chapter06.g`: the rotated right-hand
  side $\bar g_m = Q_m(\beta e_1)$ and its first $m$ entries $g_m$.
* Equation (6.47), `SaadSparse.Chapter06.γ`: the last entries $\gamma_1 = \beta$,
  $\gamma_{i+2} = -s_{i+1}\gamma_{i+1}$.
* Proposition 6.9(2), `SaadSparse.Chapter06.gmresY`: the coordinates $y_m = R_m^{-1} g_m$.
* Algorithm 6.11, `SaadSparse.Chapter06.gmresCycle` and `SaadSparse.Chapter06.gmresRestarted`:
  restarted GMRES, GMRES(m).
* Algorithm 6.12, `SaadSparse.Chapter06.qgmres`: QGMRES on an arbitrary basis.
* Equation (6.48) and Algorithm 6.13, `SaadSparse.Chapter06.dqgmresP` and
  `SaadSparse.Chapter06.dqgmres`: the direction vectors and the approximations of DQGMRES.
* Equation (6.52), `SaadSparse.Chapter06.Z`, `SaadSparse.Chapter06.z` and `SaadSparse.Chapter06.ζ`:
  $Z_{m+1} = V_{m+1} Q_m^H$, its last column $z_{m+1}$ and $\zeta_{m+1} = \|z_{m+1}\|_2$.
* Section 6.5.6, `SaadSparse.Chapter06.quasiResidualNorm`: the quasi-residual norm $|\gamma_{m+1}|$.
* Section 6.5.6, `SaadSparse.Chapter06.iomOfBasis`: the Galerkin approximation on an arbitrary basis
  (IOM, DIOM or FOM).
* Section 6.5.7, `SaadSparse.Chapter06.ρG` and `SaadSparse.Chapter06.ρF`: the residual norms
  $\rho^G_m$ of GMRES and $\rho^F_m$ of FOM.
* Proposition 6.12, `SaadSparse.Chapter06.ξ`: the diagonal entry $\xi_m$ of $Q_{m-1} \bar H_m$.
* Proposition 6.15, `SaadSparse.Chapter06.ρFmin`: the smallest FOM residual norm $\rho^F_{m*}$ of
  the first $m$ steps.
* Lemma 6.16, `SaadSparse.Chapter06.Rtilde`, `SaadSparse.Chapter06.gtilde` and
  `SaadSparse.Chapter06.ytilde`: the Givens data $\tilde R_m$, $\tilde g_m$, $\tilde y_m$ one
  rotation short.
* Algorithm 6.14, `SaadSparse.Chapter06.mrs` and `SaadSparse.Chapter06.mrsEta`: minimal residual
  smoothing and its coefficient $\eta_m$.
* Section 6.5.8, `SaadSparse.Chapter06.qmrs`: quasi-minimal residual smoothing (QMRS) with scale
  factors `SaadSparse.Chapter06.qmrsTau`.

## Main results

* Equation (6.27), `SaadSparse.Chapter06.equation_6_27`: $b - A(x_0 + V_m y) = V_{m+1}(\beta e_1 -
  \bar H_m y)$.
* Equation (6.28), `SaadSparse.Chapter06.equation_6_28`: $\|b - A(x_0 + V_m y)\|_2 = J(y)$.
* Equations (6.29)–(6.30), `SaadSparse.Chapter06.isGMRESIterate_iff`: the GMRES approximation is the
  minimal-residual iterate on $\mathcal{K}_m(A, r_0)$.
* Equations (6.29)–(6.30), `SaadSparse.Chapter06.gmres_unique`: for nonsingular $A$ the GMRES
  approximation is unique.
* Algorithm 6.10, `SaadSparse.Chapter06.gmresHH_eq` and `SaadSparse.Chapter06.algorithm_6_10`:
  Householder GMRES computes the approximation of Algorithm 6.9.
* Equation (6.35), `SaadSparse.Chapter06.equation_6_35`: $c_i^2 + s_i^2 = 1$.
* Equations (6.36) and (6.38), `SaadSparse.Chapter06.equation_6_38`: the rotations and their product
  are orthogonal.
* Equation (6.39), `SaadSparse.Chapter06.equation_6_39`: $\bar R_m$ is upper triangular with a zero
  last row.
* Equation (6.41), `SaadSparse.Chapter06.equation_6_41`:
  $b - Ax_m = V_{m+1} Q_m^H(\gamma_{m+1} e_{m+1})$.
* Equation (6.42), `SaadSparse.Chapter06.equation_6_42`: $\|b - Ax_m\|_2 = |\gamma_{m+1}|$.
* Equation (6.43), `SaadSparse.Chapter06.equation_6_43`: $\|\beta e_1 - \bar H_m y\|_2^2 =
  |\gamma_{m+1}|^2 + \|g_m - R_m y\|_2^2$.
* Equations (6.44)–(6.46), `SaadSparse.Chapter06.equation_6_44` and
  `SaadSparse.Chapter06.Rbar_succ_submatrix`: a new column changes neither the earlier columns of
  $\bar R$ nor the earlier entries of $\bar g$.
* Equation (6.47), `SaadSparse.Chapter06.equation_6_47`: $\gamma_{j+2} = -s_{j+1}\gamma_{j+1}$.
* Proposition 6.9, `SaadSparse.Chapter06.proposition_6_9` and
  `SaadSparse.Chapter06.proposition_6_9_2`: $R_m$ is nonsingular, $y_m = R_m^{-1} g_m$ is the unique
  minimizer of $J$, and the residual norm is $|\gamma_{m+1}|$.
* Proposition 6.10, `SaadSparse.Chapter06.proposition_6_10` and
  `SaadSparse.Chapter06.proposition_6_10_book`: for nonsingular $A$, GMRES breaks down at step $j$
  if and only if $x_j$ is exact.
* Section 6.5.5, `SaadSparse.Chapter06.gmres_exact_of_card_le`: full GMRES is exact after $n$ steps.
* Equation (6.50), `SaadSparse.Chapter06.equation_6_50`: the QGMRES residual is
  $\gamma_{m+1} z_{m+1}$.
* Equation (6.51), `SaadSparse.Chapter06.equation_6_51`: $\|b - Ax_m\|_2 \le \sqrt{m - k +
  1}\,|\gamma_{m+1}|$.
* Equation (6.53), `SaadSparse.Chapter06.equation_6_53`: $z_{m+2} = -\bar s_{m+1} z_{m+1} + \bar
  c_{m+1} v_{m+2}$.
* Equation (6.54), `SaadSparse.Chapter06.equation_6_54`: $\zeta_{m+2} \le |s_{m+1}| \zeta_{m+1} +
  |c_{m+1}| \|v_{m+2}\|_2$.
* Equation (6.55), `SaadSparse.Chapter06.equation_6_55`: the recurrence between two successive
  QGMRES residuals.
* Equation (6.56), `SaadSparse.Chapter06.equation_6_56`: $\gamma_{m+1} v_{m+1} = c_m r^I_m$.
* Equation (6.57), `SaadSparse.Chapter06.equation_6_57`: $\rho^Q_m = |c_m| \rho^I_m$.
* Equation (6.58), `SaadSparse.Chapter06.equation_6_58`: $r^Q_m = s_m^2 r^Q_{m-1} + c_m^2 r^I_m$.
* Theorem 6.11, `SaadSparse.Chapter06.theorem_6_11`: the QGMRES residual norm is at most
  $\kappa_2(V_{m+1})$ times the GMRES residual norm.
* Algorithm 6.13, `SaadSparse.Chapter06.dqgmres_eq_qgmres`: without truncation DQGMRES computes the
  QGMRES approximation.
* Equation (6.62), `SaadSparse.Chapter06.equation_6_62` and `SaadSparse.Chapter06.ρG_succ`:
  $\rho^G_m = |s_1 \cdots s_m| \beta$.
* Proposition 6.12, `SaadSparse.Chapter06.proposition_6_12`: $\rho^F_m = \rho^G_m / |c_m|$.
* Equation (6.63), `SaadSparse.Chapter06.equation_6_63`: $\rho^F_{m+1} = \rho^G_{m+1} \sqrt{1 +
  h_{m+2,m+1}^2 / \xi_{m+1}^2}$.
* Proposition 6.13, `SaadSparse.Chapter06.proposition_6_13`: the relation (6.64) of Cullum and
  Greenbaum between $\rho^F_{m+1}$, $\rho^G_{m+1}$ and $\rho^G_m$.
* Equation (6.65), `SaadSparse.Chapter06.equation_6_65`: $1/(\rho^F_{m+1})^2 + 1/(\rho^G_m)^2 =
  1/(\rho^G_{m+1})^2$.
* Equation (6.66), `SaadSparse.Chapter06.equation_6_66`:
  $\sum_{i=0}^m 1/(\rho^F_i)^2 = 1/(\rho^G_m)^2$.
* Corollary 6.14, `SaadSparse.Chapter06.corollary_6_14`: $\rho^G_m = 1 / \sqrt{\sum_{i=0}^m
  (\rho^F_i)^{-2}}$.
* Proposition 6.15, `SaadSparse.Chapter06.proposition_6_15`: $\rho^G_m \le \rho^F_{m*} \le
  \sqrt{m+1}\,\rho^G_m$.
* Lemma 6.16, `SaadSparse.Chapter06.lemma_6_16`: the relation (6.69) between the coordinates of
  GMRES and FOM, with (6.70) and (6.71) in `SaadSparse.Chapter06.equation_6_70` and
  `SaadSparse.Chapter06.equation_6_71`.
* Proposition 6.17, `SaadSparse.Chapter06.proposition_6_17`: GMRES stagnates at a step if and only
  if FOM breaks down there.
* Equations (6.74) and (6.75), `SaadSparse.Chapter06.equation_6_74` and
  `SaadSparse.Chapter06.equation_6_75`: $x^G_{m+1} = s_{m+1}^2 x^G_m + c_{m+1}^2 x^F_{m+1}$, and the
  same for the residuals.
* Lemma 6.18, `SaadSparse.Chapter06.lemma_6_18`, with (6.76) and (6.77) in
  `SaadSparse.Chapter06.equation_6_76` and `SaadSparse.Chapter06.equation_6_77`: under an
  orthogonality condition, the smoothed residual norms satisfy $1/\|r^S_{m+1}\|^2 = 1/\|r^S_m\|^2 +
  1/\|r^O_{m+1}\|^2$.
* Equation (6.78), `SaadSparse.Chapter06.equation_6_78` and `SaadSparse.Chapter06.qmrs_eq_6_78`: the
  smoothed residual is a convex combination of $r^S_m$ and $r^O_{m+1}$.
* Equation (6.79), `SaadSparse.Chapter06.equation_6_79` and `SaadSparse.Chapter06.qmrs_eq_6_79`: the
  smoothed residual is a weighted average of the original residuals.
* Section 6.5.8, `SaadSparse.Chapter06.qmrs_iomOfBasis_eq_qgmres`: QMRS applied to IOM gives QGMRES.
* Section 6.5.8, `SaadSparse.Chapter06.mrs_fom_eq_gmres`: minimal residual smoothing applied to FOM
  gives GMRES.
* Equation (6.80), `SaadSparse.Chapter06.equation_6_80` and
  `SaadSparse.Chapter06.equation_6_80_unitary`: the entries of the complex rotations, which are
  unitary.
* Equation (6.81), `SaadSparse.Chapter06.equation_6_81`: for Arnoldi coefficients, the $s_i$, the
  diagonal of $R_m$ and the $\gamma_i$ are real.
* Problem P-6.5, `SaadSparse.Chapter06.problem_6_5` and `SaadSparse.Chapter06.problem_6_5_book`:
  $y_m = (\bar H_m^H \bar H_m)^{-1} \bar H_m^H (\beta e_1)$.
* Problem P-6.9, `SaadSparse.Chapter06.proposition_6_17`: the same statement as Proposition 6.17.
* Problem P-6.13, `SaadSparse.Chapter06.problem_6_13`: if $x^G_m = x^F_m$, then both are exact.
* Problem P-6.14, `SaadSparse.Chapter06.problem_6_14`: the two residuals in (6.75) are orthogonal.
* Problem P-6.25, `SaadSparse.Chapter06.problem_6_25` and `SaadSparse.Chapter06.problem_6_25_le`:
  $\zeta_{m+1} \le \sqrt{m - k + 1}$.
* Problem P-6.26, `SaadSparse.Chapter06.problem_6_26`: the directions of minimal residual smoothing
  of a Galerkin sequence are $A^T A$-orthogonal.

## Proof outline

The central result is `SaadSparse.Chapter06.isGMRESIterate_iff`, equations (6.29)–(6.30): the GMRES
approximation, defined by the least-squares problem in Hessenberg coordinates, is the
minimal-residual iterate `Krylov.IsMinResidualIterate` of the backbone. Proposition 6.9(2), (6.41),
(6.42), Proposition 6.10 and the bound of $n$ steps follow from backbone theorems through this
equivalence and the relation between the Givens data here and `Krylov.rotated`. Most results of
Section 6.5.7 specialize the relations of `Numlib.Krylov.Relations`. Lemma 6.16 is about
coordinates, not approximations, and is proved by the computation (6.72)–(6.73) of the book:
$\tilde R_m$ and $R_m$ differ in the single entry $(m, m)$. For QMRS applied to IOM, the scale
factor $\tau_m$ is the quasi-residual norm $|\gamma_{m+1}|$ by (6.57) and (6.47), the coefficient of
step $m+1$ is $c_{m+1}^2$, and (6.58) is then the QMRS residual recurrence.

## Conventions

* Indices are `0`-based in Lean, and the book's are `1`-based. A rotation quantity with the Lean
  index $i$ is the book's quantity with the index $i + 1$. Thus the Lean terms `c h i`, `s h i`,
  `γ h β i` and `Krylov.givensRho h i` are the book's $c_{i+1}$, $s_{i+1}$, $\gamma_{i+1}$ and
  $\rho_{i+1}$. Step counts $m$ are the book's.
* For a basis `u : ℕ → 𝔼` and a matrix, the Lean terms `u i` and `(i, j)` are the book's $v_{i+1}$
  and entry $(i+1, j+1)$.
* A coefficient function `h : ℕ → ℕ → 𝕜` is upper Hessenberg if `h i j = 0` for $i > j + 1$. The
  Lean terms `h i j` and `Krylov.rotated h k i j` are the book's $h_{i+1,j+1}$ and
  $h^{(k)}_{i+1,j+1}$, the coefficient after the first $k$ rotations.
* The rotation parameters are $\rho_{i+1} = \sqrt{|h^{(i)}_{i+1,i+1}|^2 + |h_{i+2,i+1}|^2}$,
  $c_{i+1} = h^{(i)}_{i+1,i+1} / \rho_{i+1}$ and $s_{i+1} = h_{i+2,i+1} / \rho_{i+1}$. At a
  breakdown $\rho_{i+1} = 0$, and then $c_{i+1} = s_{i+1} = 0$ by the convention $x / 0 = 0$.
* The book's inner product $(x, y) = \sum_i x_i \bar y_i$ is Mathlib's `inner 𝕜 y x`.
* $A x$ is `op A x`, that is `Matrix.toEuclideanLin A x`. Coordinate vectors are functions
  `Fin m → 𝕜`, and their Euclidean norms are taken through `WithLp.toLp 2`.

## Implementation notes

* The Givens data of Section 6.5.3, from `SaadSparse.Chapter06.c` to `SaadSparse.Chapter06.g`, are
  functions of the coefficient function $h$, not of the step count $m$. This is the content of the
  book's remark that the earlier rotations need not be computed again when a column is added, and it
  makes (6.44)–(6.46) hold by definition. They specialize `Krylov.givensC`, `Krylov.givensS`,
  `Krylov.givensMatrix`, `Krylov.givensQ` and `Krylov.gamma`. The lemmas
  `SaadSparse.Chapter06.Rbar_eq` and `SaadSparse.Chapter06.gbar_eq` relate the triangular factor and
  the rotated right-hand side to `Krylov.rotated`.
* Definitions are polymorphic over `[RCLike 𝕜]`, so complex GMRES (Section 6.5.9) is the same code
  as real GMRES. The results collected in the sections over $\mathbb{R}$ are stated in the book's
  real setting. Many other results, among them (6.27), (6.28), (6.41), (6.42), Proposition 6.9(2),
  Proposition 6.10, (6.50)–(6.58), Theorem 6.11 and P-6.25, are stated over any `RCLike` field and
  so cover both settings.
* The data of the system, $r_0$, $\beta$, $v_1$, $e_1$ and `SaadSparse.Chapter06.mEff`, are shared
  with Section 6.4 and are defined in `NumlibSurface.SaadSparse.Chapter06.Common`. The backbone
  indexes the Arnoldi data by $r_0$ and the book by $v_1$; the lemmas
  `SaadSparse.Chapter06.arnoldiCGS_v₁`, `SaadSparse.Chapter06.arnoldiCoeff_v₁`,
  `SaadSparse.Chapter06.Hbar_v₁` and `SaadSparse.Chapter06.grade_v₁` translate between the two.
* The module follows the order of the book's subsections with one exception: the Givens rotations of
  Section 6.5.3 come first, because the GMRES approximation of Algorithm 6.9 is defined through
  $R_m$ and $g_m$ (Proposition 6.9(2)). Propositions 6.9 and 6.10 are stated with GMRES, not with
  the rotations, because they are statements about GMRES.
* The stopping rule "if $h_{j+1,j} = 0$ set $m := j$" is `SaadSparse.Chapter06.mEff`, which is
  $\min(m, \operatorname{grade}(v_1))$.
* QGMRES and DQGMRES are stated for an arbitrary basis `u` with coefficients `h` that satisfy
  `Krylov.HessenbergRelation (op A) u h`, because their properties do not use orthogonality. With
  `u := SaadSparse.Chapter06.iop A v₁ k` and `h := SaadSparse.Chapter06.iopCoeff A v₁ k` (through
  `SaadSparse.Chapter06.iop_hessenbergRelation`) the statements become the book's statements about
  QGMRES and DQGMRES. With the Arnoldi basis they become statements about GMRES
  (`SaadSparse.Chapter06.qgmres_eq_gmresFixed`).
* The Galerkin approximation on the same basis is `SaadSparse.Chapter06.iomOfBasis`. It is IOM on
  the incomplete orthogonalization basis (`SaadSparse.Chapter06.iomOfBasis_eq_iomFixed`) and FOM on
  the Arnoldi basis (`SaadSparse.Chapter06.iomOfBasis_eq_fomFixed`).
* The lemmas about the sizes of the partial products `Krylov.givensQAux` that (6.53) needs are
  private in this module.
* Section 6.5.8 is real in the book, and this part is stated over $\mathbb{R}$.

## Deviations from the source

* **Reading.** The residual-smoothing update leaves the state fixed when its direction vanishes. See
  `SaadSparse.Chapter06.smoothEta`, `SaadSparse.Chapter06.smoothEta_eq`, `SaadSparse.Chapter06.mrs`,
  `SaadSparse.Chapter06.mrsX`, `SaadSparse.Chapter06.mrsR`, `SaadSparse.Chapter06.mrsEta`,
  `SaadSparse.Chapter06.mrsX_succ`, `SaadSparse.Chapter06.mrsR_succ`.
* **Reading.** The quasi-minimal smoothing recurrence totalizes reciprocal norms. See
  `SaadSparse.Chapter06.qmrsTau`, `SaadSparse.Chapter06.qmrsEta`, `SaadSparse.Chapter06.qmrs`,
  `SaadSparse.Chapter06.qmrs_succ`.
* **Reading.** The one-step reciprocal identity states the nonzero residual assumptions explicitly.
  See `SaadSparse.Chapter06.equation_6_76`, `SaadSparse.Chapter06.equation_6_77`,
  `SaadSparse.Chapter06.lemma_6_18`.
* **Correction.** The accumulated reciprocal formula uses the summation index in each denominator.
  See `SaadSparse.Chapter06.inv_qmrsTau_sq`, `SaadSparse.Chapter06.qmrsTau_sq`,
  `SaadSparse.Chapter06.inv_sq_norm_mrsR`.
* **Correction.** The weighted MRS and QMRS residual formulas include the initial residual. See
  `SaadSparse.Chapter06.qmrs_eq_6_79`, `SaadSparse.Chapter06.residual_mrs_eq`.
* **Reading.** The weighted update and agreement of the two smoothing procedures state their nonzero
  conditions. See `SaadSparse.Chapter06.qmrs_eq_6_78`, `SaadSparse.Chapter06.equation_6_78`,
  `SaadSparse.Chapter06.norm_mrsR_eq_qmrsTau`, `SaadSparse.Chapter06.mrs_eq_qmrs`.
* **Reading.** The smoothing comparison is with fixed IOM and QGMRES and uses the cosine ratio from
  (6.57). See `SaadSparse.Chapter06.qmrs_iomOfBasis_eq_qgmres`.
* **Reading.** The GMRES equality uses uniqueness and explicit hypotheses for the FOM prefix. See
  `SaadSparse.Chapter06.mrs_isMinResidualIterate`, `SaadSparse.Chapter06.mrs_fom_eq_gmres`.
* **Reading.** The smoothing exercise gives orthogonality for Krylov Galerkin iterates. See
  `SaadSparse.Chapter06.problem_6_26`.
* **Reading.** The residual norms use the fixed-size, totalized iterates. See
  `SaadSparse.Chapter06.ρG`, `SaadSparse.Chapter06.ρF`.
* **Generalization.** The data before the last rotation support complex scalars and totalized
  inversion. See `SaadSparse.Chapter06.Rtilde`, `SaadSparse.Chapter06.gtilde`,
  `SaadSparse.Chapter06.ξ`, `SaadSparse.Chapter06.ytilde`, `SaadSparse.Chapter06.Rtilde_apply`,
  `SaadSparse.Chapter06.gtilde_last`, `SaadSparse.Chapter06.gtilde_castSucc`.
* **Reading.** The best FOM residual includes the initial residual at index zero. See
  `SaadSparse.Chapter06.ρFmin`, `SaadSparse.Chapter06.ρFmin_le`, `SaadSparse.Chapter06.le_ρFmin`.
* **Reading.** The product formula is certified strictly before the grade without assuming
  nonsingularity of the system. See `SaadSparse.Chapter06.ρG_succ`,
  `SaadSparse.Chapter06.equation_6_62`.
* **Reading.** The residual ratio has a complex-modulus version. See
  `SaadSparse.Chapter06.ρF_eq_div_norm_c`, `SaadSparse.Chapter06.equation_6_63`.
* **Reading.** The consecutive-residual identities make the nonzero denominator hypotheses explicit.
  See `SaadSparse.Chapter06.equation_6_65`, `SaadSparse.Chapter06.proposition_6_13`.
* **Reading.** The accumulated reciprocal identities require defined FOM iterates throughout the
  prefix. See `SaadSparse.Chapter06.equation_6_66`, `SaadSparse.Chapter06.corollary_6_14`.
* **Reading.** The FOM–GMRES combination formulas require a nonsingular system and nonzero later
  residual. See `SaadSparse.Chapter06.equation_6_74`, `SaadSparse.Chapter06.equation_6_75`,
  `SaadSparse.Chapter06.problem_6_14`.
* **Reading.** The triangular-coordinate relation makes the reached step and nonsingularity
  explicit. See `SaadSparse.Chapter06.lemma_6_16`.
* **Reading.** QGMRES uses a fixed reduced solve under an abstract Hessenberg relation. See
  `SaadSparse.Chapter06.qgmresY`, `SaadSparse.Chapter06.qgmres`,
  `SaadSparse.Chapter06.qgmresY_isMinOn`, `SaadSparse.Chapter06.qgmres_isQuasiMinResidualIterate`.
* **Generalization.** The QGMRES residual-direction recurrence uses the adjoint in the complex case.
  See `SaadSparse.Chapter06.Z`, `SaadSparse.Chapter06.z`, `SaadSparse.Chapter06.z_eq`,
  `SaadSparse.Chapter06.z_eq_sum`, `SaadSparse.Chapter06.equation_6_53`.
* **Generalization.** The QGMRES and IOM residual identities extend to an abstract real or complex
  Hessenberg relation. See `SaadSparse.Chapter06.equation_6_50`,
  `SaadSparse.Chapter06.equation_6_55`, `SaadSparse.Chapter06.equation_6_56`,
  `SaadSparse.Chapter06.equation_6_58`.
* **Generalization.** The residual-direction norm estimate retains the norm of an arbitrary next
  vector. See `SaadSparse.Chapter06.equation_6_54`.
* **Generalization.** The IOM comparison formulas use an arbitrary basis and make nonsingularity
  explicit for the residual. See `SaadSparse.Chapter06.iomOfBasisY`,
  `SaadSparse.Chapter06.iomOfBasis`, `SaadSparse.Chapter06.residual_iomOfBasis`.
* **Reading.** The quasi-residual and IOM norm comparison explicitly assumes a unit next vector. See
  `SaadSparse.Chapter06.equation_6_57`.
* **Reading.** The quasi-residual estimate uses an explicit base bound and nonzero radii. See
  `SaadSparse.Chapter06.problem_6_25`, `SaadSparse.Chapter06.problem_6_25_le`,
  `SaadSparse.Chapter06.equation_6_51`.
* **Reading.** The QGMRES residual bound uses explicit upper and lower basis constants. See
  `SaadSparse.Chapter06.theorem_6_11`.
* **Reading.** The fixed-length DQGMRES recurrence uses rotated coefficients and totalized division.
  See `SaadSparse.Chapter06.dqgmresP`, `SaadSparse.Chapter06.dqgmresP_eq`,
  `SaadSparse.Chapter06.dqgmres`, `SaadSparse.Chapter06.dqgmres_eq_sum`.
* **Reading.** The certified DQGMRES–QGMRES equivalence requires a full window. See
  `SaadSparse.Chapter06.sum_R_smul_dqgmresP`, `SaadSparse.Chapter06.dqgmres_eq_qgmres`.
* **Reading.** The Givens data extend the rotation formulas to zero radii by totalized division. See
  `SaadSparse.Chapter06.c`, `SaadSparse.Chapter06.s`, `SaadSparse.Chapter06.Ω`,
  `SaadSparse.Chapter06.Qrot`.
* **Reading.** Givens unitarity and norm preservation explicitly require nonzero active radii. See
  `SaadSparse.Chapter06.norm_c_sq_add_norm_s_sq`, `SaadSparse.Chapter06.Ω_mem_unitaryGroup`,
  `SaadSparse.Chapter06.Qrot_mem_unitaryGroup`, `SaadSparse.Chapter06.norm_toLp_Qrot_mulVec`,
  `SaadSparse.Chapter06.equation_6_35`, `SaadSparse.Chapter06.equation_6_38`,
  `SaadSparse.Chapter06.equation_6_80_unitary`.
* **Generalization.** The triangular pattern of the rotated matrix also holds at a degenerate
  rotation. See `SaadSparse.Chapter06.Rbar_eq_zero_of_lt`, `SaadSparse.Chapter06.Rbar_last_row`,
  `SaadSparse.Chapter06.R_isUpperTriangular`, `SaadSparse.Chapter06.R_diag`,
  `SaadSparse.Chapter06.equation_6_39`.
* **Reading.** The rotated least-squares norm identities explicitly require nonzero radii. See
  `SaadSparse.Chapter06.norm_firstVec_sub_mulVec_eq_norm_gbar_sub`,
  `SaadSparse.Chapter06.norm_sq_firstVec_sub_mulVec`, `SaadSparse.Chapter06.equation_6_43`,
  `SaadSparse.Chapter06.sq_J_eq`.
* **Reading.** The triangular least-squares minimizer is certified when its triangular factor is
  nonsingular. See `SaadSparse.Chapter06.isMinOn_lsq`, `SaadSparse.Chapter06.proposition_6_9_2`,
  `SaadSparse.Chapter06.gmresFixed_isGMRESIterate`,
  `SaadSparse.Chapter06.gmresFixed_isMinResidualIterate`, `SaadSparse.Chapter06.lsq_eq_norm_gamma`.
* **Reading.** The complex rotation matrix is defined entrywise, including out-of-range row indices.
  See `SaadSparse.Chapter06.equation_6_80`.
* **Reading.** The evolving last component is real. Earlier entries of the rotated right-hand side
  can be complex. See `SaadSparse.Chapter06.exists_real_gamma_arnoldiCoeff`,
  `SaadSparse.Chapter06.equation_6_81`.
* **Reading.** The objective named $J$ is defined in the projected coordinates. See
  `SaadSparse.Chapter06.J`, `SaadSparse.Chapter06.J_eq`, `SaadSparse.Chapter06.J_eq_lsq`.
* **Generalization.** The Arnoldi residual vector identity includes the padded sequence. See
  `SaadSparse.Chapter06.equation_6_27`, `SaadSparse.Chapter06.residual_eq_6_27`.
* **Reading.** The residual norm equality includes the first breakdown step. See
  `SaadSparse.Chapter06.equation_6_28`, `SaadSparse.Chapter06.residual_eq_6_28`.
* **Reading.** The GMRES specification separates existence and uniqueness of least-squares
  minimizers. See `SaadSparse.Chapter06.IsGMRESIterate`, `SaadSparse.Chapter06.isGMRESIterate_iff`,
  `SaadSparse.Chapter06.gmres_isMinResidualIterate_iff`,
  `SaadSparse.Chapter06.exists_isGMRESIterate`.
* **Reading.** The uniqueness theorem makes matrix nonsingularity and the grade bound explicit. See
  `SaadSparse.Chapter06.existsUnique_isGMRESIterate`, `SaadSparse.Chapter06.gmres_unique`.
* **Reading.** The concrete GMRES algorithm uses a triangular inverse whose singular value is
  totalized. See `SaadSparse.Chapter06.gmresY`, `SaadSparse.Chapter06.gmresFixed`,
  `SaadSparse.Chapter06.gmres`.
* **Reading.** Restarted GMRES takes the cycle count as an input. See
  `SaadSparse.Chapter06.gmresCycle`, `SaadSparse.Chapter06.gmresRestarted`.
* **Reading.** The GMRES residual formulas state the nonsingularity and valid-prefix hypotheses
  explicitly. See `SaadSparse.Chapter06.equation_6_41`, `SaadSparse.Chapter06.equation_6_42`.
* **Generalization.** The reached-step characterization of GMRES breakdown also covers complex
  scalars. See `SaadSparse.Chapter06.proposition_6_10`.
* **Reading.** Householder GMRES uses the signed first reflected entry as its right-hand side. See
  `SaadSparse.Chapter06.βHH`, `SaadSparse.Chapter06.βHH_eq`, `SaadSparse.Chapter06.abs_βHH`,
  `SaadSparse.Chapter06.βHH_smul_hhV_zero`.
* **Reading.** Householder GMRES uses a totalized triangular inverse for the least-squares solve.
  See `SaadSparse.Chapter06.gmresHHY`, `SaadSparse.Chapter06.gmresHH`.
* **Reading.** The Householder GMRES correctness results require the extended basis to fit and the
  reduced factor to be nonsingular. See `SaadSparse.Chapter06.gmresHH_isMinResidualIterate`,
  `SaadSparse.Chapter06.gmresHH_eq`, `SaadSparse.Chapter06.algorithm_6_10`.
* **Proposition 6.9** (reading). The statement assumes a nonsingular $A$ and replaces the
  printed $m \le n$ with $m \le \operatorname{grade}(v_1)$. It proves the nonsingularity
  consequence of part (1). See `SaadSparse.Chapter06.proposition_6_9`.
* **Proposition 6.10** (reading). The implicit hypothesis that the first $j$ steps were taken is
  explicit: $r_0 \neq 0$ and no breakdown before step $j$. See
  `SaadSparse.Chapter06.proposition_6_10_book`.
* **Proposition 6.17** (reading). The stagnation equivalence assumes a reached prefix, a
  nonzero GMRES residual and nonsingularity of $A$ for both directions. See
  `SaadSparse.Chapter06.proposition_6_17`.
* **Proposition 6.15** (correction). The book prints the upper bound $\sqrt{m}\,\rho^G_m$ in (6.68).
  The bound is $\sqrt{m+1}\,\rho^G_m$ because the minimum includes the initial residual.
  Lean assumes every FOM reduced system is nonsingular, while the source permits skipping
  undefined iterates. See `SaadSparse.Chapter06.proposition_6_15`.
* **Equation (6.79)** (correction). The book prints both sums from $j = 1$. They run from $j = 0$.
  See `SaadSparse.Chapter06.equation_6_79`.
-/

open scoped Matrix

namespace SaadSparse.Chapter06

/-!
### Sections 6.5.3 and 6.5.9: Givens rotations and the factorization $Q_m \bar H_m = \bar R_m$
-/

section Givens

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### The rotation parameters (6.37) and (6.81) -/

/-- **Equations (6.37) and (6.81)** of [saad2003iterative]. Let $h$ be a coefficient function and
$i \ge 0$. The **cosine** of the rotation $\Omega_{i+1}$ is
$$c_{i+1} = \frac{h^{(i)}_{i+1,i+1}}{\rho_{i+1}}, \qquad
  \rho_{i+1} = \sqrt{|h^{(i)}_{i+1,i+1}|^2 + |h^{(i)}_{i+2,i+1}|^2},$$
where $h^{(i)}$ are the coefficients after the first $i$ rotations. If $\rho_{i+1} = 0$, then
$c_{i+1} = 0$.

The definition is `Krylov.givensC`. The Lean index $i$ is the book's $i + 1$. The Lean terms
`Krylov.rotated h i i i` and `Krylov.givensRho h i` are $h^{(i)}_{i+1,i+1}$ and $\rho_{i+1}$.
The first $i$ rotations do not change row $i + 2$, so $h^{(i)}_{i+2,i+1} = h_{i+2,i+1}$. The
value $0$ at $\rho_{i+1} = 0$ comes from the convention $x / 0 = 0$.

**Reading.** Lean assigns both parameters zero when the rotation radius is zero. The displayed
source formulas divide by that radius, and an active block is unitary only for nonzero radius. The
real and complex cases use a single conjugate-transpose convention.
-/
noncomputable abbrev c (h : ℕ → ℕ → 𝕜) (i : ℕ) : 𝕜 := Krylov.givensC h i

/-- **Equations (6.37) and (6.81)** of [saad2003iterative]. The **sine** of the rotation
$\Omega_{i+1}$ is $s_{i+1} = h_{i+2,i+1} / \rho_{i+1}$, with $\rho_{i+1}$ as for
`SaadSparse.Chapter06.c`. If $\rho_{i+1} = 0$, then $s_{i+1} = 0$.

The definition is `Krylov.givensS`. Its numerator is the entry `Krylov.rotated h i (i + 1) i`,
which the first $i$ rotations leave equal to $h_{i+2,i+1}$ (`SaadSparse.Chapter06.s_eq_div`).

**Reading.** Lean assigns both parameters zero when the rotation radius is zero. The displayed
source formulas divide by that radius, and an active block is unitary only for nonzero radius. The
real and complex cases use a single conjugate-transpose convention.
-/
noncomputable abbrev s (h : ℕ → ℕ → 𝕜) (i : ℕ) : 𝕜 := Krylov.givensS h i

/-- **Equations (6.34) and (6.80)** of [saad2003iterative]. The **Givens rotation** $\Omega_{i+1}$
is the $(m+1) \times (m+1)$ matrix that equals the identity except in rows and columns $i + 1$
and $i + 2$, where it is
$$\begin{bmatrix} \bar c_{i+1} & \bar s_{i+1} \\ -s_{i+1} & c_{i+1} \end{bmatrix}.$$

Over $\mathbb{R}$ the conjugates have no effect and this is (6.34); over $\mathbb{C}$ it is
(6.80). The rows and columns are `0`-based in Lean, so the block is in rows `i` and `i + 1`. The
definition is `Krylov.givensMatrix`.

**Reading.** Lean assigns both parameters zero when the rotation radius is zero. The displayed
source formulas divide by that radius, and an active block is unitary only for nonzero radius. The
real and complex cases use a single conjugate-transpose convention.
-/
noncomputable abbrev Ω (h : ℕ → ℕ → 𝕜) (i m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜 :=
  Krylov.givensMatrix h i m

/-- **Equation (6.38)** of [saad2003iterative]. The product
$Q_m = \Omega_m \Omega_{m-1} \cdots \Omega_1$ of the first $m$ rotations, an
$(m+1) \times (m+1)$ matrix.

The definition is `Krylov.givensQ`. The matrix $Q_0$ is the identity.

**Reading.** Lean assigns both parameters zero when the rotation radius is zero. The displayed
source formulas divide by that radius, and an active block is unitary only for nonzero radius. The
real and complex cases use a single conjugate-transpose convention.
-/
noncomputable abbrev Qrot (h : ℕ → ℕ → 𝕜) (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜 :=
  Krylov.givensQ h m

/-- **Equation (6.47)** of [saad2003iterative]. The last entry $\gamma_{i+1}$ of the rotated
right-hand side $\bar g_i$, defined by
$$\gamma_1 = \beta, \qquad \gamma_{i+2} = -s_{i+1} \gamma_{i+1}.$$

The definition is `Krylov.gamma`. The Lean value `γ h β i` is the book's $\gamma_{i+1}$. -/
noncomputable abbrev γ (h : ℕ → ℕ → 𝕜) (β : 𝕜) (i : ℕ) : 𝕜 := Krylov.gamma h β i

/-- **Equation (6.39)** of [saad2003iterative]. The **triangular factor** $\bar R_m = Q_m \bar H_m
\in \mathbb{K}^{(m+1) \times m}$, where $\bar H_m$ is the $(m+1) \times m$ Hessenberg matrix of
the coefficient function $h$.

The matrix $\bar H_m$ is `Krylov.hessenbergOf h m`. That $\bar R_m$ is upper triangular with a
zero last row is `SaadSparse.Chapter06.equation_6_39`. -/
noncomputable def Rbar (h : ℕ → ℕ → 𝕜) (m : ℕ) : Matrix (Fin (m + 1)) (Fin m) 𝕜 :=
  Qrot h m * Krylov.hessenbergOf h m

/-- **Equation (6.40)** of [saad2003iterative]. The **rotated right-hand side** $\bar g_m = Q_m
(\beta e_1) \in \mathbb{K}^{m+1}$, where $e_1$ is the first coordinate vector of
$\mathbb{K}^{m+1}$.

`SaadSparse.Chapter06.gbar_eq` gives its entries: the first $m$ are $\bar c_{i+1} \gamma_{i+1}$,
and the last is $\gamma_{m+1}$. -/
noncomputable def gbar (h : ℕ → ℕ → 𝕜) (β : 𝕜) (m : ℕ) : Fin (m + 1) → 𝕜 :=
  (Qrot h m).mulVec (Krylov.firstVec β (m + 1))

/-- **Section 6.5.3** of [saad2003iterative]. The $m \times m$ matrix $R_m$ obtained from $\bar R_m$
by deleting its last row.

For an upper Hessenberg $h$ the deleted row is zero (`SaadSparse.Chapter06.Rbar_last_row`). -/
noncomputable def R (h : ℕ → ℕ → 𝕜) (m : ℕ) : Matrix (Fin m) (Fin m) 𝕜 :=
  (Rbar h m).submatrix Fin.castSucc id

/-- **Section 6.5.3** of [saad2003iterative]. The vector $g_m \in \mathbb{K}^m$ obtained from
$\bar g_m$ by deleting its last entry $\gamma_{m+1}$. -/
noncomputable def g (h : ℕ → ℕ → 𝕜) (β : 𝕜) (m : ℕ) : Fin m → 𝕜 :=
  fun i => gbar h β m i.castSucc

variable (h : ℕ → ℕ → 𝕜) (β : 𝕜)

/-! ### The relation to the backbone: $\bar R_m$ is $\bar H^{(m)}_m$ -/

/-- The matrix $\bar R_m = Q_m \bar H_m$ is the $(m+1) \times m$ Hessenberg matrix of the
coefficients after $m$ rotations, `Krylov.hessenbergOf (Krylov.rotated h m) m`. -/
theorem Rbar_eq (m : ℕ) : Rbar h m = Krylov.hessenbergOf (Krylov.rotated h m) m :=
  Krylov.givensQ_mul_hessenbergOf h m

/-- The entry $(i, j)$ of $\bar R_m$ is `Krylov.rotated h m i j`, the coefficient
$h^{(m)}_{i+1,j+1}$ after $m$ rotations. -/
theorem Rbar_apply {m : ℕ} (i : Fin (m + 1)) (j : Fin m) :
    Rbar h m i j = Krylov.rotated h m i j := by
  rw [Rbar_eq]
  rfl

/-- The entries of $\bar g_m = Q_m(\beta e_1)$: the entry with `0`-based index $i < m$ is
$\bar c_{i+1} \gamma_{i+1}$, which is `Krylov.gvec h β i`, and the last entry is $\gamma_{m+1}$. -/
theorem gbar_eq (m : ℕ) :
    gbar h β m =
      fun i : Fin (m + 1) => if (i : ℕ) < m then Krylov.gvec h β i else Krylov.gamma h β m :=
  Krylov.givensQ_mulVec_firstVec h β m

/-- For a `0`-based index $i < m$, the entry $i$ of $\bar g_m$ is $\bar c_{i+1} \gamma_{i+1}$, which
is `Krylov.gvec h β i`. -/
theorem gbar_apply_of_lt {m : ℕ} {i : Fin (m + 1)} (hi : (i : ℕ) < m) :
    gbar h β m i = Krylov.gvec h β i := by
  rw [gbar_eq]
  exact ite_eq_left hi

/-- The last entry of $\bar g_m$ is $\gamma_{m+1}$. -/
theorem gbar_last (m : ℕ) : gbar h β m (Fin.last m) = γ h β m := by
  rw [gbar_eq]
  exact ite_eq_right (by simp)

/-- The entry $(i, j)$ of $R_m$ is `Krylov.rotated h m i j`, the coefficient $h^{(m)}_{i+1,j+1}$
after $m$ rotations. -/
theorem R_apply {m : ℕ} (i j : Fin m) : R h m i j = Krylov.rotated h m i j := by
  rw [R, Matrix.submatrix_apply, Rbar_apply, Fin.val_castSucc]
  rfl

/-- The matrix $R_m$ is the square Hessenberg matrix `Krylov.hessenbergSqOf (Krylov.rotated h m) m`
of the coefficients after $m$ rotations. -/
theorem R_eq (m : ℕ) : R h m = Krylov.hessenbergSqOf (Krylov.rotated h m) m := by
  ext i j
  rw [R_apply]
  rfl

/-- The entry with `0`-based index $i$ of $g_m$ is $\bar c_{i+1} \gamma_{i+1}$, and so it does not
depend on $m$: adding a column to $\bar H_m$ and rotating it leaves the earlier entries of the
right-hand side unchanged. This is the part of (6.44)–(6.46) of [saad2003iterative] about the
right-hand side. -/
theorem g_apply {m : ℕ} (i : Fin m) : g h β m i = Krylov.gvec h β (i : ℕ) := by
  rw [g, gbar_apply_of_lt h β (by simp)]
  rfl

/-- The vector $g_m$ is $(\bar c_1 \gamma_1, \dots, \bar c_m \gamma_m)$, with entries
`Krylov.gvec h β i`. -/
theorem g_eq (m : ℕ) : g h β m = fun i : Fin m => Krylov.gvec h β (i : ℕ) :=
  funext fun i => g_apply h β i

/-! ### The least-squares function (6.26) and (6.28) for a coefficient function -/

/-- The least-squares function $y \mapsto \|\beta e_1 - \bar H_m y\|_2$ of (6.26) and (6.28), for
$y \in \mathbb{K}^m$, as a function of the coefficient function $h$ alone. The function
`SaadSparse.Chapter06.J` is its value at the Arnoldi coefficients of $v_1$. -/
noncomputable def lsq (h : ℕ → ℕ → 𝕜) (β : 𝕜) (m : ℕ) (y : Fin m → 𝕜) : ℝ :=
  ‖(WithLp.toLp 2 (Krylov.firstVec β (m + 1) - Krylov.hessenbergOf h m *ᵥ y) :
    EuclideanSpace 𝕜 (Fin (m + 1)))‖

/-- The least-squares function is nonnegative. -/
theorem lsq_nonneg {m : ℕ} (y : Fin m → 𝕜) : 0 ≤ lsq h β m y := norm_nonneg _

/-- If $R_m$ is nonsingular, then $y = R_m^{-1} g_m$ solves the triangular system $R_m y = g_m$ of
Proposition 6.9(2). -/
theorem mulVec_R_inv_mulVec_g {m : ℕ} (hR : IsUnit (R h m)) :
    R h m *ᵥ ((R h m)⁻¹ *ᵥ g h β m) = g h β m :=
  Matrix.mulVec_nonsing_inv_mulVec hR _

/-! ### Equations (6.35), (6.36) and (6.80): the rotations are unitary -/

/-- If $\rho_{i+1} \neq 0$, then $|c_{i+1}|^2 + |s_{i+1}|^2 = 1$. This is (6.35) and (6.80) of
[saad2003iterative]; at a breakdown $\rho_{i+1} = 0$, and then $c_{i+1} = s_{i+1} = 0$.

**Reading.** The normalizing radius must be nonzero for every active rotation. This is explicit in
Lean because the definitions also allow a degenerate zero-radius block.
-/
theorem norm_c_sq_add_norm_s_sq {i : ℕ} (hρ : Krylov.givensRho h i ≠ 0) :
    ‖c h i‖ ^ 2 + ‖s h i‖ ^ 2 = 1 :=
  Krylov.norm_givensC_sq_add_norm_givensS_sq h i hρ

/-- If $i < m$ and $\rho_{i+1} \neq 0$, then the rotation $\Omega_{i+1}$ of size $m + 1$ is unitary.
This is (6.34) and (6.80) of [saad2003iterative].

**Reading.** The normalizing radius must be nonzero for every active rotation. This is explicit in
Lean because the definitions also allow a degenerate zero-radius block.
-/
theorem Ω_mem_unitaryGroup {i m : ℕ} (hi : i < m) (hρ : Krylov.givensRho h i ≠ 0) :
    Ω h i m ∈ Matrix.unitaryGroup (Fin (m + 1)) 𝕜 :=
  Krylov.givensMatrix_mem_unitaryGroup h i m hi hρ

/-- If $\rho_1, \dots, \rho_m$ are all nonzero, then $Q_m = \Omega_m \cdots \Omega_1$ is unitary.
This is (6.38) of [saad2003iterative].

**Reading.** The normalizing radius must be nonzero for every active rotation. This is explicit in
Lean because the definitions also allow a degenerate zero-radius block.
-/
theorem Qrot_mem_unitaryGroup (m : ℕ) (hρ : ∀ i < m, Krylov.givensRho h i ≠ 0) :
    Qrot h m ∈ Matrix.unitaryGroup (Fin (m + 1)) 𝕜 :=
  Krylov.givensQ_mem_unitaryGroup h m hρ

/-- If $\rho_1, \dots, \rho_m$ are all nonzero, then $\|Q_m z\|_2 = \|z\|_2$ for every
$z \in \mathbb{K}^{m+1}$. This is the only property of the rotations that (6.43) uses.

**Reading.** The normalizing radius must be nonzero for every active rotation. This is explicit in
Lean because the definitions also allow a degenerate zero-radius block.
-/
theorem norm_toLp_Qrot_mulVec {m : ℕ} (hρ : ∀ i < m, Krylov.givensRho h i ≠ 0)
    (z : Fin (m + 1) → 𝕜) :
    ‖(WithLp.toLp 2 (Qrot h m *ᵥ z) : EuclideanSpace 𝕜 (Fin (m + 1)))‖ =
      ‖(WithLp.toLp 2 z : EuclideanSpace 𝕜 (Fin (m + 1)))‖ :=
  Matrix.norm_toLp_mulVec_of_mem_unitaryGroup (Qrot_mem_unitaryGroup h m hρ) z

/-! ### Equation (6.39): $\bar R_m$ is upper triangular with a zero last row -/

variable (hh : ∀ i j : ℕ, j + 1 < i → h i j = 0)
include hh

/-- Let $h$ be upper Hessenberg. Then $\bar R_m$ is upper triangular: its entry $(i, j)$ is $0$ for
$j < i$. This is part of (6.39) of [saad2003iterative].

**Generalization.** The zero pattern of the rotated Hessenberg matrix and the diagonal computation
are valid even if a radius vanishes. The source describes the pattern after genuine unitary
rotations.
-/
theorem Rbar_eq_zero_of_lt {m : ℕ} {i : Fin (m + 1)} {j : Fin m} (hij : (j : ℕ) < (i : ℕ)) :
    Rbar h m i j = 0 := by
  rw [Rbar_apply]
  exact Krylov.rotated_eq_zero_of_lt h (Matrix.isUpperHessenberg_iff_nat.2 hh) m i j j.isLt hij

/-- Let $h$ be upper Hessenberg. Then the last row of $\bar R_m$ is zero. This is part of (6.39) of
[saad2003iterative].

**Generalization.** The zero pattern of the rotated Hessenberg matrix and the diagonal computation
are valid even if a radius vanishes. The source describes the pattern after genuine unitary
rotations.
-/
theorem Rbar_last_row {m : ℕ} (j : Fin m) : Rbar h m (Fin.last m) j = 0 :=
  Rbar_eq_zero_of_lt h hh (by simp)

/-- Let $h$ be upper Hessenberg. Then $R_m$ is upper triangular.

**Generalization.** The zero pattern of the rotated Hessenberg matrix and the diagonal computation
are valid even if a radius vanishes. The source describes the pattern after genuine unitary
rotations.
-/
theorem R_isUpperTriangular (m : ℕ) : (R h m).IsUpperTriangular := by
  rw [R_eq]
  exact Krylov.hessenbergSqOf_rotated_isUpperTriangular h (Matrix.isUpperHessenberg_iff_nat.2 hh)
      (by omega)

/-- Let $h$ be upper Hessenberg. Then the diagonal entry $r_{i+1,i+1}$ of $R_m$ is the nonnegative
real number $\rho_{i+1}$, as in (6.37) of [saad2003iterative]. Over $\mathbb{C}$ this is the
statement of Section 6.5.9 that the diagonal of $R_m$ is real and nonnegative.

**Generalization.** The zero pattern of the rotated Hessenberg matrix and the diagonal computation
are valid even if a radius vanishes. The source describes the pattern after genuine unitary
rotations.
-/
theorem R_diag {m : ℕ} (i : Fin m) : R h m i i = ((Krylov.givensRho h i : ℝ) : 𝕜) := by
  rw [R_apply]
  exact Krylov.rotated_diag h (Matrix.isUpperHessenberg_iff_nat.2 hh) i.isLt

/-- Let $h$ be upper Hessenberg. If $\rho_1, \dots, \rho_m$ are all nonzero, then $R_m$ is
nonsingular. -/
theorem isUnit_R {m : ℕ} (hρ : ∀ k < m, Krylov.givensRho h k ≠ 0) : IsUnit (R h m) := by
  rw [R_eq]
  exact Krylov.isUnit_hessenbergSqOf_rotated_self h (Matrix.isUpperHessenberg_iff_nat.2 hh) hρ

/-- Let $h$ be upper Hessenberg. Then $R_m$ is nonsingular if and only if $\rho_1, \dots, \rho_m$
are all nonzero, because the diagonal of the triangular matrix $R_m$ is
$(\rho_1, \dots, \rho_m)$. -/
theorem isUnit_R_iff {m : ℕ} : IsUnit (R h m) ↔ ∀ k < m, Krylov.givensRho h k ≠ 0 := by
  refine ⟨fun hR k hk => ?_, isUnit_R h hh⟩
  have hdet : (R h m).det = ∏ i : Fin m, ((Krylov.givensRho h (i : ℕ) : ℝ) : 𝕜) := by
    rw [Matrix.det_of_isUpperTriangular (R_isUpperTriangular h hh m)]
    exact Finset.prod_congr rfl fun i _ => R_diag h hh i
  have hne : (R h m).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 hR).ne_zero
  rw [hdet, Finset.prod_ne_zero_iff] at hne
  simpa using hne ⟨k, hk⟩ (Finset.mem_univ _)

/-! ### Equation (6.43): the least-squares residual after the rotations -/

omit hh in
/-- For every $y \in \mathbb{K}^m$, $Q_m (\beta e_1 - \bar H_m y) = \bar g_m - \bar R_m y$. -/
theorem Qrot_mulVec_firstVec_sub {m : ℕ} (y : Fin m → 𝕜) :
    Qrot h m *ᵥ (Krylov.firstVec β (m + 1) - Krylov.hessenbergOf h m *ᵥ y)
      = gbar h β m - Rbar h m *ᵥ y := by
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec]
  rfl

/-- Let $h$ be upper Hessenberg, and let $y \in \mathbb{K}^m$ satisfy $R_m y = g_m$. Then
$\bar g_m - \bar R_m y = \gamma_{m+1} e_{m+1}$, because the last row of $\bar R_m$ is zero and
the last entry of $\bar g_m$ is $\gamma_{m+1}$. This is the core of (6.41) of
[saad2003iterative]. -/
theorem gbar_sub_Rbar_mulVec {m : ℕ} {y : Fin m → 𝕜} (hy : R h m *ᵥ y = g h β m) :
    gbar h β m - Rbar h m *ᵥ y = Pi.single (Fin.last m) (γ h β m) := by
  funext i
  rcases eq_or_ne i (Fin.last m) with rfl | hi
  · have hz : (Rbar h m *ᵥ y) (Fin.last m) = 0 := by
      simp only [Matrix.mulVec, dotProduct]
      exact Finset.sum_eq_zero fun j _ => by rw [Rbar_last_row h hh j, zero_mul]
    rw [Pi.sub_apply, gbar_last, hz, sub_zero, Pi.single_eq_same]
  · obtain ⟨i', rfl⟩ := Fin.exists_castSucc_eq.2 hi
    have hz : (Rbar h m *ᵥ y) i'.castSucc = g h β m i' := by
      rw [← hy]
      rfl
    rw [Pi.sub_apply, hz, Pi.single_eq_of_ne hi]
    exact sub_eq_zero.2 rfl

omit hh in
/-- If $\rho_1, \dots, \rho_m$ are all nonzero, then $\|\beta e_1 - \bar H_m y\|_2 = \|\bar g_m -
\bar R_m y\|_2$ for every $y \in \mathbb{K}^m$, because $Q_m$ is unitary. This is the first
equality of (6.43) of [saad2003iterative].

**Reading.** The norm decomposition requires the active rotations to be unitary. Lean states nonzero
radii explicitly, and the general versions also allow complex coefficients.
-/
theorem norm_firstVec_sub_mulVec_eq_norm_gbar_sub {m : ℕ}
    (hρ : ∀ k < m, Krylov.givensRho h k ≠ 0) (y : Fin m → 𝕜) :
    ‖(WithLp.toLp 2 (Krylov.firstVec β (m + 1) - Krylov.hessenbergOf h m *ᵥ y) :
        EuclideanSpace 𝕜 (Fin (m + 1)))‖ =
      ‖(WithLp.toLp 2 (gbar h β m - Rbar h m *ᵥ y) : EuclideanSpace 𝕜 (Fin (m + 1)))‖ := by
  have hmul : Qrot h m *ᵥ (Krylov.firstVec β (m + 1) - Krylov.hessenbergOf h m *ᵥ y) =
      gbar h β m - Rbar h m *ᵥ y := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec]
    rfl
  rw [← norm_toLp_Qrot_mulVec h hρ, hmul]

/-- Let $h$ be upper Hessenberg with $\rho_1, \dots, \rho_m$ all nonzero. Then for every
$y \in \mathbb{K}^m$,
$$\|\beta e_1 - \bar H_m y\|_2^2 = |\gamma_{m+1}|^2 + \|g_m - R_m y\|_2^2.$$
This is (6.43) of [saad2003iterative]: the rotations split the least-squares problem into a part
that the triangular system $R_m y = g_m$ can make zero and a fixed remainder.

**Reading.** The norm decomposition requires the active rotations to be unitary. Lean states nonzero
radii explicitly, and the general versions also allow complex coefficients.
-/
theorem norm_sq_firstVec_sub_mulVec {m : ℕ} (hρ : ∀ k < m, Krylov.givensRho h k ≠ 0)
    (y : Fin m → 𝕜) :
    ‖(WithLp.toLp 2 (Krylov.firstVec β (m + 1) - Krylov.hessenbergOf h m *ᵥ y) :
        EuclideanSpace 𝕜 (Fin (m + 1)))‖ ^ 2 =
      ‖γ h β m‖ ^ 2 +
        ‖(WithLp.toLp 2 (g h β m - R h m *ᵥ y) : EuclideanSpace 𝕜 (Fin m))‖ ^ 2 := by
  rw [Krylov.norm_sq_firstVec_sub_mulVec_eq h (Matrix.isUpperHessenberg_iff_nat.2 hh)
      hρ β y, R_eq, g_eq, add_comm]

/-- Proposition 6.9(2) of [saad2003iterative] for a coefficient function. Let $h$ be upper
Hessenberg and let $R_m$ be nonsingular. Then $y = R_m^{-1} g_m$ minimizes
$\|\beta e_1 - \bar H_m y\|_2$ over $y \in \mathbb{K}^m$, and every minimizer equals
$R_m^{-1} g_m$. The proof uses (6.43): the second term of
$|\gamma_{m+1}|^2 + \|g_m - R_m y\|_2^2$ is zero exactly at $y = R_m^{-1} g_m$.

**Reading.** The inverse formula gives the unique minimizer when the triangular factor is
nonsingular. Lean makes that assumption explicit, as used in the source proof. The same argument
also applies to complex least squares.
-/
theorem isMinOn_lsq {m : ℕ} (hR : IsUnit (R h m)) :
    IsMinOn (lsq h β m) Set.univ ((R h m)⁻¹ *ᵥ g h β m) ∧
      ∀ y, IsMinOn (lsq h β m) Set.univ y → y = (R h m)⁻¹ *ᵥ g h β m := by
  have hρ := (isUnit_R_iff h hh).1 hR
  have hsq : ∀ y : Fin m → 𝕜, lsq h β m y ^ 2 = ‖γ h β m‖ ^ 2 +
      ‖(WithLp.toLp 2 (g h β m - R h m *ᵥ y) : EuclideanSpace 𝕜 (Fin m))‖ ^ 2 :=
    fun y => norm_sq_firstVec_sub_mulVec h β hh hρ y
  have hzero : lsq h β m ((R h m)⁻¹ *ᵥ g h β m) ^ 2 = ‖γ h β m‖ ^ 2 := by
    rw [hsq, mulVec_R_inv_mulVec_g h β hR, sub_self]
    simp
  have hle : ∀ y : Fin m → 𝕜, lsq h β m ((R h m)⁻¹ *ᵥ g h β m) ≤ lsq h β m y := by
    intro y
    nlinarith [hsq y, lsq_nonneg h β ((R h m)⁻¹ *ᵥ g h β m), lsq_nonneg h β y,
      sq_nonneg ‖(WithLp.toLp 2 (g h β m - R h m *ᵥ y) : EuclideanSpace 𝕜 (Fin m))‖]
  refine ⟨isMinOn_iff.2 fun y _ => hle y, fun y hy => ?_⟩
  have h3 : ‖(WithLp.toLp 2 (g h β m - R h m *ᵥ y) : EuclideanSpace 𝕜 (Fin m))‖ = 0 := by
    nlinarith [hsq y, hle y, isMinOn_iff.1 hy _ (Set.mem_univ ((R h m)⁻¹ *ᵥ g h β m)),
      lsq_nonneg h β y, lsq_nonneg h β ((R h m)⁻¹ *ᵥ g h β m),
      norm_nonneg (WithLp.toLp 2 (g h β m - R h m *ᵥ y) : EuclideanSpace 𝕜 (Fin m))]
  rw [norm_eq_zero, WithLp.toLp_eq_zero, sub_eq_zero] at h3
  exact Matrix.mulVec_injective_iff_isUnit.2 hR (by rw [← h3, mulVec_R_inv_mulVec_g h β hR])

/-- **Equations (6.44)–(6.46)** of [saad2003iterative], for the triangular factor. Let $h$ be upper
Hessenberg. Then the leading $(m+1) \times m$ block of $\bar R_{m+1}$ is $\bar R_m$:
$$(\bar R_{m+1})_{ij} = (\bar R_m)_{ij}, \qquad 1 \le i \le m + 1, \ 1 \le j \le m.$$
So adding a column to $\bar H_m$ and rotating it does not change the earlier columns of the
triangular factor in their first $m + 1$ rows.

The Givens data are functions of $h$ alone, so the rotations $\Omega_1, \dots, \Omega_m$ used
for $\bar R_{m+1}$ are those used for $\bar R_m$. -/
theorem Rbar_succ_submatrix {m : ℕ} :
    (Rbar h (m + 1)).submatrix Fin.castSucc Fin.castSucc = Rbar h m := by
  ext i j
  rw [Matrix.submatrix_apply, Rbar_apply, Rbar_apply, Fin.val_castSucc, Fin.val_castSucc,
    Krylov.rotated_succ_eq_of_lt h (Matrix.isUpperHessenberg_iff_nat.2 hh) m (j : ℕ) j.isLt (i : ℕ)]

/-- Let $h$ be upper Hessenberg with $\rho_1, \dots, \rho_m$ all nonzero, and let
$y \in \mathbb{K}^m$ satisfy $R_m y = g_m$. Then $\beta e_1 - \bar H_m y = Q_m^H (\gamma_{m+1}
e_{m+1})$. This is (6.41) of [saad2003iterative] for a coefficient function. -/
theorem firstVec_sub_mulVec_eq {m : ℕ} (hρ : ∀ k < m, Krylov.givensRho h k ≠ 0)
    {y : Fin m → 𝕜} (hy : R h m *ᵥ y = g h β m) :
    Krylov.firstVec β (m + 1) - Krylov.hessenbergOf h m *ᵥ y
      = (Qrot h m)ᴴ *ᵥ Pi.single (Fin.last m) (γ h β m) := by
  have h1 : (Qrot h m)ᴴ * Qrot h m = 1 := by
    have hq := (Matrix.mem_unitaryGroup_iff' (A := Qrot h m)).1 (Qrot_mem_unitaryGroup h m hρ)
    rwa [Matrix.star_eq_conjTranspose] at hq
  conv_lhs => rw [← Matrix.one_mulVec (Krylov.firstVec β (m + 1) -
    Krylov.hessenbergOf h m *ᵥ y), ← h1]
  rw [← Matrix.mulVec_mulVec, Qrot_mulVec_firstVec_sub, gbar_sub_Rbar_mulVec h β hh hy]

/-- Let $h$ be upper Hessenberg and let $R_m$ be nonsingular. Then
$\|\beta e_1 - \bar H_m y\|_2 = |\gamma_{m+1}|$ at $y = R_m^{-1} g_m$, so the minimum of the
least-squares function is $|\gamma_{m+1}|$. This is (6.42) of [saad2003iterative] for a
coefficient function.

**Reading.** The inverse formula gives the unique minimizer when the triangular factor is
nonsingular. Lean makes that assumption explicit, as used in the source proof. The same argument
also applies to complex least squares.
-/
theorem lsq_eq_norm_gamma {m : ℕ} (hR : IsUnit (R h m)) :
    lsq h β m ((R h m)⁻¹ *ᵥ g h β m) = ‖γ h β m‖ := by
  have hρ := (isUnit_R_iff h hh).1 hR
  have hsq := norm_sq_firstVec_sub_mulVec h β hh hρ ((R h m)⁻¹ *ᵥ g h β m)
  rw [mulVec_R_inv_mulVec_g h β hR, sub_self] at hsq
  simp only [WithLp.toLp_zero, norm_zero] at hsq
  rw [lsq]
  nlinarith [norm_nonneg (WithLp.toLp 2 (Krylov.firstVec β (m + 1) -
      Krylov.hessenbergOf h m *ᵥ ((R h m)⁻¹ *ᵥ g h β m)) : EuclideanSpace 𝕜 (Fin (m + 1))),
    norm_nonneg (γ h β m), hsq]

/-! ### Problem P-6.5: the normal equations of the least-squares problem -/

/-- Let $h$ be upper Hessenberg. Then $\bar R_m^H \bar R_m = R_m^H R_m$, because the last row of
$\bar R_m$ is zero. -/
theorem conjTranspose_mul_self_Rbar {m : ℕ} : (Rbar h m)ᴴ * Rbar h m = (R h m)ᴴ * R h m := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Fin.sum_univ_castSucc, Rbar_last_row h hh i, star_zero, zero_mul, add_zero]
  rfl

/-- Let $h$ be upper Hessenberg. Then $\bar R_m^H \bar g_m = R_m^H g_m$, because the last row of
$\bar R_m$ is zero. -/
theorem conjTranspose_mulVec_gbar {m : ℕ} :
    (Rbar h m)ᴴ *ᵥ gbar h β m = (R h m)ᴴ *ᵥ g h β m := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]
  rw [Fin.sum_univ_castSucc, Rbar_last_row h hh i, star_zero, zero_mul, add_zero]
  rfl

/-- Let $h$ be upper Hessenberg with $\rho_1, \dots, \rho_m$ all nonzero. Then
$\bar H_m^H \bar H_m = R_m^H R_m$: the rotations are unitary, so they cancel in the normal
equations. -/
theorem conjTranspose_mul_self_hessenbergOf {m : ℕ}
    (hρ : ∀ k < m, Krylov.givensRho h k ≠ 0) :
    (Krylov.hessenbergOf h m)ᴴ * Krylov.hessenbergOf h m = (R h m)ᴴ * R h m := by
  have h1 : (Qrot h m)ᴴ * Qrot h m = 1 := by
    have hq := (Matrix.mem_unitaryGroup_iff' (A := Qrot h m)).1 (Qrot_mem_unitaryGroup h m hρ)
    rwa [Matrix.star_eq_conjTranspose] at hq
  have h2 : (Rbar h m)ᴴ * Rbar h m
      = (Krylov.hessenbergOf h m)ᴴ * ((Qrot h m)ᴴ * Qrot h m) * Krylov.hessenbergOf h m := by
    rw [Rbar, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [← conjTranspose_mul_self_Rbar h hh, h2, h1, Matrix.mul_one]

/-- Let $h$ be upper Hessenberg with $\rho_1, \dots, \rho_m$ all nonzero. Then
$\bar H_m^H (\beta e_1) = R_m^H g_m$. -/
theorem conjTranspose_hessenbergOf_mulVec_firstVec {m : ℕ}
    (hρ : ∀ k < m, Krylov.givensRho h k ≠ 0) :
    (Krylov.hessenbergOf h m)ᴴ *ᵥ Krylov.firstVec β (m + 1) = (R h m)ᴴ *ᵥ g h β m := by
  have h1 : (Qrot h m)ᴴ * Qrot h m = 1 := by
    have hq := (Matrix.mem_unitaryGroup_iff' (A := Qrot h m)).1 (Qrot_mem_unitaryGroup h m hρ)
    rwa [Matrix.star_eq_conjTranspose] at hq
  rw [← conjTranspose_mulVec_gbar h β hh, gbar, Rbar, Matrix.conjTranspose_mul,
    Matrix.mulVec_mulVec, Matrix.mul_assoc, h1, Matrix.mul_one]

/-- Let $h$ be upper Hessenberg with $\rho_1, \dots, \rho_m$ all nonzero. If $R_m$ is nonsingular,
then the matrix $\bar H_m^H \bar H_m$ of the normal equations is nonsingular. -/
theorem isUnit_conjTranspose_mul_self_hessenbergOf {m : ℕ}
    (hρ : ∀ k < m, Krylov.givensRho h k ≠ 0) (hR : IsUnit (R h m)) :
    IsUnit ((Krylov.hessenbergOf h m)ᴴ * Krylov.hessenbergOf h m) := by
  have hRH : IsUnit ((R h m)ᴴ) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_conjTranspose]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 hR).star
  rw [conjTranspose_mul_self_hessenbergOf h hh hρ]
  exact hRH.mul hR

/-- Problem P-6.5 of [saad2003iterative] for a coefficient function. Let $h$ be upper Hessenberg
with $\rho_1, \dots, \rho_m$ all nonzero, and let $y \in \mathbb{K}^m$ satisfy $R_m y = g_m$.
Then $y$ satisfies the normal equations $\bar H_m^H \bar H_m y = \bar H_m^H (\beta e_1)$ of the
least-squares problem (6.29), so GMRES is the projection formula (5.7) with $V = V_m$ and
$W = A V_m$. -/
theorem normal_equations {m : ℕ} (hρ : ∀ k < m, Krylov.givensRho h k ≠ 0) {y : Fin m → 𝕜}
    (hy : R h m *ᵥ y = g h β m) :
    ((Krylov.hessenbergOf h m)ᴴ * Krylov.hessenbergOf h m) *ᵥ y
      = (Krylov.hessenbergOf h m)ᴴ *ᵥ Krylov.firstVec β (m + 1) := by
  rw [conjTranspose_mul_self_hessenbergOf h hh hρ,
    conjTranspose_hessenbergOf_mulVec_firstVec h β hh hρ, ← Matrix.mulVec_mulVec, hy]

/-! ### Equations (6.44)–(6.47): the progressive form of the right-hand side -/

omit hh

/-- The recurrence (6.47) of [saad2003iterative]: $\gamma_{j+2} = -s_{j+1} \gamma_{j+1}$. -/
theorem gamma_succ (j : ℕ) : γ h β (j + 1) = -(s h j) * γ h β j :=
  Krylov.gamma_succ h β j

/-- The entry $m + 1$ of $\bar g_{m+1}$, at the position of the last entry of $\bar g_m$, is
$\bar c_{m+1} \gamma_{m+1}$. This is part of (6.44)–(6.46) of [saad2003iterative], where the
book writes $c_{m+1} \gamma_{m+1}$; the conjugate is the complex convention of (6.80). -/
theorem gbar_succ_castSucc (m : ℕ) :
    gbar h β (m + 1) (Fin.last m).castSucc = starRingEnd 𝕜 (c h m) * γ h β m :=
  gbar_apply_of_lt h β (by simp)

/-- The last entry of $\bar g_{m+1}$ is $-s_{m+1} \gamma_{m+1}$. This is part of (6.44)–(6.46) of
[saad2003iterative]. -/
theorem gbar_succ_last (m : ℕ) : gbar h β (m + 1) (Fin.last (m + 1)) = -(s h m) * γ h β m := by
  rw [gbar_last]
  exact Krylov.gamma_succ h β m

/-- $|\gamma_{m+1}| = |s_1 \cdots s_m| \, |\beta|$, the product form of (6.47). -/
theorem norm_gamma_eq_prod (m : ℕ) :
    ‖γ h β m‖ = (∏ k ∈ Finset.range m, ‖s h k‖) * ‖β‖ :=
  Krylov.norm_gamma_eq_prod h β m

/-! ### Section 6.5.9: $s_i$ and $\gamma_i$ are real for Arnoldi coefficients -/

section Arnoldi

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ : EuclideanSpace 𝕜 (Fin n))

/-- $s_{i+1} = h_{i+2,i+1} / \rho_{i+1}$, the second half of (6.37) and (6.81) of
[saad2003iterative]. -/
theorem s_eq_div (i : ℕ) : s h i = h (i + 1) i / ((Krylov.givensRho h i : ℝ) : 𝕜) := by
  change Krylov.givensS h i = _
  rw [Krylov.givensS, Krylov.rotated_eq_of_le h i (i + 1) i le_rfl]

/-- Let $v_1 \in \mathbb{K}^n$ be a unit vector and let $h$ be the Arnoldi coefficients of $A$ and
$v_1$. Then $s_{i+1} = \|w_{i+1}\|_2 / \rho_{i+1}$, where $w_{i+1}$ is the vector of the Arnoldi
process before normalization (`SaadSparse.Chapter06.arnoldiW`). So $s_{i+1}$ is real and
nonnegative also over $\mathbb{C}$, as Section 6.5.9 states. -/
theorem s_arnoldiCoeff_eq (hv : ‖v₁‖ = 1) (i : ℕ) :
    s (arnoldiCoeff A v₁) i =
      ((‖arnoldiW A v₁ i‖ / Krylov.givensRho (arnoldiCoeff A v₁) i : ℝ) : 𝕜) := by
  rw [s_eq_div, arnoldiCoeff_succ_self A v₁ hv, RCLike.ofReal_div]

/-- Let $v_1$ be a unit vector. For the Arnoldi coefficients of $A$ and $v_1$, each $s_{i+1}$ is a
nonnegative real number (Section 6.5.9). -/
theorem s_arnoldiCoeff_nonneg (hv : ‖v₁‖ = 1) (i : ℕ) :
    ∃ t : ℝ, 0 ≤ t ∧ s (arnoldiCoeff A v₁) i = (t : 𝕜) :=
  ⟨_, div_nonneg (norm_nonneg _) (Krylov.givensRho_nonneg _ i), s_arnoldiCoeff_eq A v₁ hv i⟩

/-- Let $v_1$ be a unit vector and let $\beta = t$ be real. Then for the Arnoldi coefficients of $A$
and $v_1$ every $\gamma_{i+1}$ is real, because every $s_{i+1}$ is real
(`SaadSparse.Chapter06.s_arnoldiCoeff_nonneg`).

**Reading.** The real-valued $\gamma_i$ is the evolving last component before the next rotation. An
earlier component stored in the final rotated right-hand side is $\overline c_i\gamma_i$ and can be
complex. The sine coefficient and the diagonal are nonnegative real values.
-/
theorem exists_real_gamma_arnoldiCoeff (hv : ‖v₁‖ = 1) (t : ℝ) (i : ℕ) :
    ∃ u : ℝ, γ (arnoldiCoeff A v₁) ((t : ℝ) : 𝕜) i = (u : 𝕜) := by
  induction i with
  | zero => exact ⟨t, rfl⟩
  | succ i ih =>
    obtain ⟨u, hu⟩ := ih
    obtain ⟨w, -, hw⟩ := s_arnoldiCoeff_nonneg A v₁ hv i
    refine ⟨-(w * u), ?_⟩
    rw [gamma_succ, hu, hw]
    push_cast
    ring

end Arnoldi

end Givens

/-! ### The numbered results of Section 6.5.3 over $\mathbb{R}$ -/

section BookResultsReal

variable (h : ℕ → ℕ → ℝ) (β : ℝ) (hh : ∀ i j : ℕ, j + 1 < i → h i j = 0)

/-- **Equation (6.35)** of [saad2003iterative]. Let $h$ be a real coefficient function and let
$i \ge 0$ with $\rho_{i+1} \neq 0$. Then
$$c_{i+1}^2 + s_{i+1}^2 = 1.$$

The hypothesis $\rho_{i+1} \neq 0$ excludes a breakdown, where $c_{i+1} = s_{i+1} = 0$. The
proof specializes `SaadSparse.Chapter06.norm_c_sq_add_norm_s_sq`.

**Reading.** The normalizing radius must be nonzero for every active rotation. This is explicit in
Lean because the definitions also allow a degenerate zero-radius block.
-/
theorem equation_6_35 {i : ℕ} (hρ : Krylov.givensRho h i ≠ 0) : c h i ^ 2 + s h i ^ 2 = 1 := by
  have := norm_c_sq_add_norm_s_sq h hρ
  rwa [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs] at this

/-- **Equations (6.36) and (6.38)** of [saad2003iterative]. Let $h$ be a real coefficient function,
let $m \ge 0$, and let $\rho_1, \dots, \rho_m$ be nonzero. Then each rotation $\Omega_{i+1}$
with $i < m$ is an orthogonal $(m+1) \times (m+1)$ matrix, and so is the product
$Q_m = \Omega_m \cdots \Omega_1$.

Orthogonality is membership in `Matrix.unitaryGroup (Fin (m + 1)) ℝ`.

**Reading.** The normalizing radius must be nonzero for every active rotation. This is explicit in
Lean because the definitions also allow a degenerate zero-radius block.
-/
theorem equation_6_38 (m : ℕ) (hρ : ∀ i < m, Krylov.givensRho h i ≠ 0) :
    (∀ i < m, Ω h i m ∈ Matrix.unitaryGroup (Fin (m + 1)) ℝ) ∧
      Qrot h m ∈ Matrix.unitaryGroup (Fin (m + 1)) ℝ :=
  ⟨fun i hi => Ω_mem_unitaryGroup h hi (hρ i hi), Qrot_mem_unitaryGroup h m hρ⟩

include hh

/-- **Equation (6.39)** of [saad2003iterative]. Let $h$ be a real upper Hessenberg coefficient
function. Then $\bar R_m = Q_m \bar H_m$ is upper triangular, $(\bar R_m)_{ij} = 0$ for $i > j$,
and the last row of $\bar R_m$ is zero.

**Generalization.** The zero pattern of the rotated Hessenberg matrix and the diagonal computation
are valid even if a radius vanishes. The source describes the pattern after genuine unitary
rotations.
-/
theorem equation_6_39 (m : ℕ) :
    (∀ (i : Fin (m + 1)) (j : Fin m), (j : ℕ) < (i : ℕ) → Rbar h m i j = 0) ∧
      ∀ j : Fin m, Rbar h m (Fin.last m) j = 0 :=
  ⟨fun _ _ hij => Rbar_eq_zero_of_lt h hh hij, fun j => Rbar_last_row h hh j⟩

/-- **Equation (6.43)** of [saad2003iterative]. Let $h$ be a real upper Hessenberg coefficient
function with $\rho_1, \dots, \rho_m$ nonzero, and let $\beta \in \mathbb{R}$. Then for every
$y \in \mathbb{R}^m$,
$$\|\beta e_1 - \bar H_m y\|_2^2 = |\gamma_{m+1}|^2 + \|g_m - R_m y\|_2^2.$$

**Reading.** The norm decomposition requires the active rotations to be unitary. Lean states nonzero
radii explicitly, and the general versions also allow complex coefficients.
-/
theorem equation_6_43 {m : ℕ} (hρ : ∀ k < m, Krylov.givensRho h k ≠ 0) (y : Fin m → ℝ) :
    ‖(WithLp.toLp 2 (Krylov.firstVec β (m + 1) - Krylov.hessenbergOf h m *ᵥ y) :
        EuclideanSpace ℝ (Fin (m + 1)))‖ ^ 2 =
      ‖γ h β m‖ ^ 2 +
        ‖(WithLp.toLp 2 (g h β m - R h m *ᵥ y) : EuclideanSpace ℝ (Fin m))‖ ^ 2 :=
  norm_sq_firstVec_sub_mulVec h β hh hρ y

/-- **Equations (6.44)–(6.46)** of [saad2003iterative]. Let $h$ be a real upper Hessenberg
coefficient function and $\beta \in \mathbb{R}$. When column $m + 1$ is added, the earlier
columns of the triangular factor and the earlier entries of the right-hand side do not change:
the leading $(m+1) \times m$ block of $\bar R_{m+1}$ is $\bar R_m$, and the first $m$ entries of
$g_{m+1}$ are those of $g_m$. The two new entries of $\bar g_{m+1}$, in positions $m + 1$ and
$m + 2$, are
$$c_{m+1} \gamma_{m+1} \quad \text{and} \quad -s_{m+1} \gamma_{m+1}.$$
-/
theorem equation_6_44 {m : ℕ} :
    (Rbar h (m + 1)).submatrix Fin.castSucc Fin.castSucc = Rbar h m ∧
      (∀ i : Fin m, g h β (m + 1) i.castSucc = g h β m i) ∧
        gbar h β (m + 1) (Fin.last m).castSucc = c h m * γ h β m ∧
          gbar h β (m + 1) (Fin.last (m + 1)) = -(s h m) * γ h β m := by
  refine ⟨Rbar_succ_submatrix h hh, fun i => ?_, ?_, gbar_succ_last h β m⟩
  · rw [g_apply, g_apply, Fin.val_castSucc]
  · rw [gbar_succ_castSucc]
    rfl

omit hh

/-- **Equation (6.47)** of [saad2003iterative]. Let $h$ be a real coefficient function,
$\beta \in \mathbb{R}$ and $j \ge 0$. Then
$$\gamma_{j+2} = -s_{j+1} \gamma_{j+1}.$$

With $\gamma_1 = \beta$, this is the definition of `SaadSparse.Chapter06.γ`. -/
theorem equation_6_47 (j : ℕ) : γ h β (j + 1) = -(s h j) * γ h β j :=
  gamma_succ h β j

end BookResultsReal

/-! ### Section 6.5.9: the complex rotations (6.80) and (6.81) -/

section BookResultsComplex

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (v₁ : EuclideanSpace ℂ (Fin n))

/-- **Equation (6.80)** of [saad2003iterative]. Let $h$ be a complex coefficient function and
$i, m \ge 0$. The complex rotation $\Omega_{i+1}$ of size $m + 1$ has the entries
$$(\Omega_{i+1})_{pq} = \begin{cases}
  \bar c_{i+1} & p = q = i + 1, \\
  \bar s_{i+1} & p = i + 1, \ q = i + 2, \\
  -s_{i+1} & p = i + 2, \ q = i + 1, \\
  c_{i+1} & p = q = i + 2, \\
  \delta_{pq} & \text{otherwise}.
\end{cases}$$

The indices $p$ and $q$ are `0`-based in Lean, so the cases read `p = i`, `q = i + 1` and so on.

**Reading.** The formula acts on the intended two-row block for an in-range rotation. Lean defines
the matrix entrywise for any natural index, including when the complete two-row block is outside its
dimensions.
-/
theorem equation_6_80 (h : ℕ → ℕ → ℂ) (i m : ℕ) (p q : Fin (m + 1)) :
    Ω h i m p q =
      if (p : ℕ) = i ∧ (q : ℕ) = i then starRingEnd ℂ (c h i)
      else if (p : ℕ) = i ∧ (q : ℕ) = i + 1 then starRingEnd ℂ (s h i)
      else if (p : ℕ) = i + 1 ∧ (q : ℕ) = i then -s h i
      else if (p : ℕ) = i + 1 ∧ (q : ℕ) = i + 1 then c h i
      else if p = q then 1 else 0 := rfl

/-- **Equation (6.80)** of [saad2003iterative], unitarity. Let $h$ be a complex coefficient
function, let $i < m$ and let $\rho_{i+1} \neq 0$. Then $|c_{i+1}|^2 + |s_{i+1}|^2 = 1$, and the
rotation $\Omega_{i+1}$ of size $m + 1$ is unitary.

**Reading.** The normalizing radius must be nonzero for every active rotation. This is explicit in
Lean because the definitions also allow a degenerate zero-radius block.
-/
theorem equation_6_80_unitary (h : ℕ → ℕ → ℂ) {i m : ℕ} (hi : i < m)
    (hρ : Krylov.givensRho h i ≠ 0) :
    ‖c h i‖ ^ 2 + ‖s h i‖ ^ 2 = 1 ∧ Ω h i m ∈ Matrix.unitaryGroup (Fin (m + 1)) ℂ :=
  ⟨norm_c_sq_add_norm_s_sq h hρ, Ω_mem_unitaryGroup h hi hρ⟩

/-- **Equation (6.81)** of [saad2003iterative] and Section 6.5.9. Let
$A \in \mathbb{C}^{n \times n}$, let $v_1 \in \mathbb{C}^n$ with $\|v_1\|_2 = 1$, let $h$ be the
Arnoldi coefficients of $A$ and $v_1$, and let $t \in \mathbb{R}$ and $m \ge 0$. Then every
$s_{i+1}$ is a nonnegative real number, the diagonal entries of $R_m$ are the real numbers
$\rho_1, \dots, \rho_m$, and for $\beta = t$ every $\gamma_{i+1}$ is real.

The Arnoldi coefficients are `SaadSparse.Chapter06.arnoldiCoeff A v₁`.

**Reading.** The real-valued $\gamma_i$ is the evolving last component before the next rotation. An
earlier component stored in the final rotated right-hand side is $\overline c_i\gamma_i$ and can be
complex. The sine coefficient and the diagonal are nonnegative real values.
-/
theorem equation_6_81 (hv : ‖v₁‖ = 1) (t : ℝ) (m : ℕ) :
    (∀ i, ∃ u : ℝ, 0 ≤ u ∧ s (arnoldiCoeff A v₁) i = (u : ℂ)) ∧
      (∀ i : Fin m, R (arnoldiCoeff A v₁) m i i =
        ((Krylov.givensRho (arnoldiCoeff A v₁) i : ℝ) : ℂ)) ∧
        ∀ i, ∃ u : ℝ, γ (arnoldiCoeff A v₁) ((t : ℝ) : ℂ) i = (u : ℂ) :=
  ⟨fun i => s_arnoldiCoeff_nonneg A v₁ hv i,
    fun i => R_diag _ (fun _ _ hij => arnoldiCoeff_eq_zero_of_lt A v₁ hv hij) i,
    fun i => exists_real_gamma_arnoldiCoeff A v₁ hv t i⟩

end BookResultsComplex

/-!
### Sections 6.5.1–6.5.5: GMRES

In this part $A \in \mathbb{K}^{n \times n}$, $b, x_0 \in \mathbb{K}^n$, $r_0 = b - Ax_0$,
$\beta = \|r_0\|_2$ and $v_1 = r_0 / \beta$. The matrices $V_m$ and $\bar H_m$ are the Arnoldi basis
and the Hessenberg matrix of $v_1$, and the Givens data are those of the Arnoldi coefficients of
$v_1$.
-/

section GMRES

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

variable (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : EuclideanSpace 𝕜 (Fin n))

/-! ### Equations (6.25)–(6.28) -/

/-- The vector $x_0 + V_m y$ of (6.25) of [saad2003iterative], for $y \in \mathbb{K}^m$, where
$V_m = [v_1, \dots, v_m]$ is the matrix of the first $m$ Arnoldi vectors of $v_1$. -/
noncomputable def krylovIterate (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (m : ℕ)
    (y : Fin m → 𝕜) : 𝔼 :=
  x₀ + Matrix.toEuclideanLin (V A (v₁ A b x₀) m) (WithLp.toLp 2 y)

/-- $x_0 + V_m y = x_0 + \sum_{j=1}^m y_j v_j$, where the Arnoldi vectors $v_j$ are written as the
backbone vectors `Arnoldi.vec (op A) r₀` of the Arnoldi process started at $r_0$. -/
theorem krylovIterate_eq_sum {m : ℕ} (y : Fin m → 𝕜) :
    krylovIterate A b x₀ m y = x₀ + ∑ j, y j • Arnoldi.vec (op A) (r₀ A b x₀) (j : ℕ) := by
  rw [krylovIterate, toEuclideanLin_V_apply]
  exact congrArg _ (Finset.sum_congr rfl fun j _ => by rw [arnoldiCGS_v₁_apply])

/-- **Equations (6.26) and (6.28)** of [saad2003iterative]. The function
$$J(y) = \|\beta e_1 - \bar H_m y\|_2, \qquad y \in \mathbb{K}^m,$$
where $\beta = \|r_0\|_2$, $e_1$ is the first coordinate vector of $\mathbb{K}^{m+1}$ and
$\bar H_m$ is the $(m+1) \times m$ Hessenberg matrix of the Arnoldi process started at $v_1$.
GMRES minimizes $J$.

The book defines $J$ by the residual norm $\|b - A(x_0 + V_m y)\|_2$. The Lean definition uses
the Hessenberg form, and `SaadSparse.Chapter06.equation_6_28` shows that the two agree when $m$
is at most the grade of $v_1$.

**Reading.** The source introduces $J$ as the original-space residual norm. Lean defines it as the
Hessenberg least-squares objective and proves equality with the original norm for prefixes at most
the grade.
-/
noncomputable def J (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (m : ℕ) (y : Fin m → 𝕜) : ℝ :=
  ‖(WithLp.toLp 2 ((β A b x₀ : 𝕜) • e₁ (m + 1) - Hbar A (v₁ A b x₀) m *ᵥ y) :
    EuclideanSpace 𝕜 (Fin (m + 1)))‖

/-- The function $J$ in the terms of the backbone: $J(y) = \| \, \|r_0\|_2 e_1 - \bar H_m y \|_2$,
where $\bar H_m$ is `Arnoldi.hessenberg (op A) r₀ m`, the Hessenberg matrix of the Arnoldi
process started at $r_0$.

**Reading.** The source introduces $J$ as the original-space residual norm. Lean defines it as the
Hessenberg least-squares objective and proves equality with the original norm for prefixes at most
the grade.
-/
theorem J_eq (m : ℕ) :
    J A b x₀ m = fun y : Fin m → 𝕜 =>
      ‖(WithLp.toLp 2 (Krylov.firstVec (‖r₀ A b x₀‖ : 𝕜) (m + 1) -
        Arnoldi.hessenberg (op A) (r₀ A b x₀) m *ᵥ y) : EuclideanSpace 𝕜 (Fin (m + 1)))‖ := by
  funext y
  rw [J, smul_e₁_eq_firstVec, Hbar_v₁, β_eq_norm_r₀]

/-- **Equation (6.27)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$,
$b, x_0 \in \mathbb{K}^n$ and $m \ge 0$. For every $y \in \mathbb{K}^m$,
$$b - A(x_0 + V_m y) = V_{m+1} (\beta e_1 - \bar H_m y).$$

The identity needs no hypothesis on $m$: after a breakdown the Arnoldi vectors and coefficients
are $0$, and the identity stays true. It holds over $\mathbb{R}$ and over $\mathbb{C}$.

**Generalization.** The identity also holds with the zero-padded sequence, including zero initial
residual. The general version applies to complex scalars.
-/
theorem equation_6_27 {m : ℕ} (y : Fin m → 𝕜) :
    b - op A (krylovIterate A b x₀ m y) =
      Matrix.toEuclideanLin (V A (v₁ A b x₀) (m + 1))
        (WithLp.toLp 2 ((β A b x₀ : 𝕜) • e₁ (m + 1) - Hbar A (v₁ A b x₀) m *ᵥ y)) := by
  rw [krylovIterate_eq_sum, toEuclideanLin_V_apply, smul_e₁_eq_firstVec, Hbar_v₁, β_eq_norm_r₀,
    Arnoldi.hessenberg_eq,
    (Arnoldi.hessenbergRelation (op A) (r₀ A b x₀)).residual_eq
      (Arnoldi.smul_vec_zero (op A) (r₀ A b x₀)).symm m y]
  exact Finset.sum_congr rfl fun j _ => by rw [arnoldiCGS_v₁_apply]

/-- **Equation (6.28)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$,
$b, x_0 \in \mathbb{K}^n$, and let $m$ be at most the grade of $v_1$ with respect to $A$. For
every $y \in \mathbb{K}^m$,
$$\|b - A(x_0 + V_m y)\|_2 = J(y).$$

The hypothesis $m \le \operatorname{grade}(v_1)$ says that the Arnoldi process has completed $m$
steps.

**Reading.** Lean permits the step at the grade, where the next basis vector is zero. Its
coefficient in the residual vanishes, so the norm equality still holds even though the source's
proof describes all the columns of the extended basis as orthonormal.
-/
theorem equation_6_28 {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀)) (y : Fin m → 𝕜) :
    ‖b - op A (krylovIterate A b x₀ m y)‖ = J A b x₀ m y := by
  rw [krylovIterate_eq_sum, J_eq]
  exact Krylov.norm_residual_eq_norm_firstVec_sub_mulVec (by rwa [← grade_v₁]) y

/-! ### Equations (6.29)–(6.30): Algorithm 6.9 and the minimal-residual specification -/

/-- **Algorithm 6.9** of [saad2003iterative] (GMRES), line 12. A vector $x \in \mathbb{K}^n$ is a
**GMRES approximation** at step $m$ if $x = x_0 + V_m y_m$ for a vector $y_m \in \mathbb{K}^m$
that minimizes $J$ over $\mathbb{K}^m$, as in (6.29)–(6.30).

The definition does not require the minimizer to be unique. For nonsingular $A$ the
approximation is unique (`SaadSparse.Chapter06.existsUnique_isGMRESIterate`).

**Reading.** The minimizer predicate describes all minimizers. Lean separates existence from
uniqueness and makes the valid-prefix hypothesis explicit in its equivalence with minimization of
the original residual.
-/
def IsGMRESIterate (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (m : ℕ) (x : 𝔼) : Prop :=
  ∃ y : Fin m → 𝕜, IsMinOn (J A b x₀ m) Set.univ y ∧ x = krylovIterate A b x₀ m y

/-- Let $m$ be at most the grade of $v_1$. Then $x$ is a GMRES approximation at step $m$ if and only
if $x$ is the minimal-residual iterate on $\mathcal{K}_m(A, r_0)$
(`Krylov.IsMinResidualIterate`): $x - x_0 \in \mathcal{K}_m(A, r_0)$, and
$\|b - Ax\|_2 \le \|b - Ax'\|_2$ for every $x' \in x_0 + \mathcal{K}_m(A, r_0)$. This is
(6.29)–(6.30) of [saad2003iterative], and most other results about GMRES in this module follow
from it.

**Reading.** The minimizer predicate describes all minimizers. Lean separates existence from
uniqueness and makes the valid-prefix hypothesis explicit in its equivalence with minimization of
the original residual.
-/
theorem isGMRESIterate_iff {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀)) {x : 𝔼} :
    IsGMRESIterate A b x₀ m x ↔ Krylov.IsMinResidualIterate (op A) b x₀ m x := by
  have hm' : m ≤ Krylov.grade (op A) (r₀ A b x₀) := by rwa [← grade_v₁]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [krylovIterate_eq_sum]
    exact (Krylov.isMinResidualIterate_iff_isMinOn hm' y).2 (by rwa [J_eq] at hy)
  · intro hx
    obtain ⟨y, -, hxe⟩ := hx.exists_mulVec_rotated_eq hm'
    refine ⟨y, ?_, by rw [krylovIterate_eq_sum]; exact hxe⟩
    rw [J_eq]
    exact (Krylov.isMinResidualIterate_iff_isMinOn hm' y).1 (by rwa [← hxe])

/-- Let $m$ be at most the grade of $v_1$. Then a GMRES approximation at step $m$ exists.

**Reading.** The minimizer predicate describes all minimizers. Lean separates existence from
uniqueness and makes the valid-prefix hypothesis explicit in its equivalence with minimization of
the original residual.
-/
theorem exists_isGMRESIterate {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀)) :
    ∃ x, IsGMRESIterate A b x₀ m x := by
  obtain ⟨x, hx⟩ := Krylov.exists_isMinResidualIterate (op A) b x₀ m
  exact ⟨x, (isGMRESIterate_iff A b x₀ hm).2 hx⟩

/-- If $A$ is nonsingular, then the map $x \mapsto Ax$ is injective. -/
theorem injective_op_of_isUnit {A : Matrix (Fin n) (Fin n) 𝕜} (hA : IsUnit A) :
    Function.Injective (op A) := by
  obtain ⟨u, hu⟩ := hA
  have h1 : op (↑u⁻¹ : Matrix (Fin n) (Fin n) 𝕜) ∘ₗ op A = LinearMap.id := by
    rw [← Matrix.toEuclideanLin_mul, ← hu, ← Units.val_mul]
    simp
  exact Function.LeftInverse.injective (g := op (↑u⁻¹ : Matrix (Fin n) (Fin n) 𝕜))
    fun y => by rw [← LinearMap.comp_apply, h1, LinearMap.id_apply]

/-- Let $m$ be at most the grade of $v_1$ and let $A$ be nonsingular. Then there is exactly one
GMRES approximation at step $m$: the unique vector of $x_0 + \mathcal{K}_m(A, r_0)$ that
minimizes $\|b - Ax\|_2$, as in (6.29)–(6.30) of [saad2003iterative].

**Reading.** The source calls the minimizer unique. Lean requires a nonsingular system matrix and
the grade bound, ensuring injectivity of the system operator on the search space.
-/
theorem existsUnique_isGMRESIterate {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀)) (hA : IsUnit A) :
    ∃! x, IsGMRESIterate A b x₀ m x := by
  obtain ⟨x, hx, huniq⟩ :=
    Krylov.existsUnique_isMinResidualIterate_of_injective (injective_op_of_isUnit hA) b x₀ m
  exact ⟨x, (isGMRESIterate_iff A b x₀ hm).2 hx,
    fun z hz => huniq z ((isGMRESIterate_iff A b x₀ hm).1 hz)⟩

/-! ### Section 6.5.3: the minimizer $y_m = R_m^{-1} g_m$ and Algorithm 6.9 -/

/-- **Proposition 6.9(2)** of [saad2003iterative], and line 12 of Algorithm 6.9 in its practical
form. The coordinate vector
$$y_m = R_m^{-1} g_m \in \mathbb{K}^m,$$
where $R_m$ and $g_m$ are the Givens data of the Arnoldi coefficients of $v_1$, with
$\beta = \|r_0\|_2$.

If $R_m$ is singular, the Lean inverse is $0$, and then $y_m = 0$.

**Reading.** Lean uses the triangular inverse implementation from §6.5.3 and totalizes it at a
singular triangular factor. The source defines the update by an arbitrary least-squares minimizer.
In Lean's singular case the inverse can return zero coefficients even when zero does not minimize
the residual.
-/
noncomputable def gmresY (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (m : ℕ) : Fin m → 𝕜 :=
  (R (arnoldiCoeff A (v₁ A b x₀)) m)⁻¹ *ᵥ g (arnoldiCoeff A (v₁ A b x₀)) (β A b x₀ : 𝕜) m

/-- **Algorithm 6.9** of [saad2003iterative] (GMRES), run for exactly $m$ Arnoldi steps. The
approximation
$$x_m = x_0 + V_m y_m, \qquad y_m = R_m^{-1} g_m.$$

This definition does not test for a breakdown. `SaadSparse.Chapter06.gmres` adds the stopping
rule.

**Reading.** Lean uses the triangular inverse implementation from §6.5.3 and totalizes it at a
singular triangular factor. The source defines the update by an arbitrary least-squares minimizer.
In Lean's singular case the inverse can return zero coefficients even when zero does not minimize
the residual.
-/
noncomputable def gmresFixed (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (m : ℕ) : 𝔼 :=
  krylovIterate A b x₀ m (gmresY A b x₀ m)

/-- **Algorithm 6.9** of [saad2003iterative] (GMRES), with the book's rule "if $h_{j+1,j} = 0$ set
$m := j$". It is the approximation $x_{m'}$ of `SaadSparse.Chapter06.gmresFixed` with
$m' = \min(m, \operatorname{grade}(v_1))$.

The number $m'$ is `SaadSparse.Chapter06.mEff`: the Arnoldi process stops exactly at the grade
of $v_1$.

**Reading.** Lean uses the triangular inverse implementation from §6.5.3 and totalizes it at a
singular triangular factor. The source defines the update by an arbitrary least-squares minimizer.
In Lean's singular case the inverse can return zero coefficients even when zero does not minimize
the residual.
-/
noncomputable def gmres (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (m : ℕ) : 𝔼 :=
  gmresFixed A b x₀ (mEff A b x₀ m)

/-- **Algorithm 6.11** of [saad2003iterative] (GMRES(m)), one cycle. From the initial guess $x_0$ it
returns the approximation of Algorithm 6.9 after at most $m$ steps, which is the initial guess
of the next cycle.

**Reading.** Lean takes a fixed restart size and a specified number of cycles, using the exact
totalized GMRES step each time. The printed loop stops according to satisfaction of the convergence
check.
-/
noncomputable def gmresCycle (A : Matrix (Fin n) (Fin n) 𝕜) (b : 𝔼) (m : ℕ) (x₀ : 𝔼) : 𝔼 :=
  gmres A b x₀ m

/-- **Algorithm 6.11** of [saad2003iterative] (GMRES(m)). The approximation after $k$ restart cycles
of length $m$ started from $x_0$, that is the $k$-th iterate of the map
`SaadSparse.Chapter06.gmresCycle A b m` applied to $x_0$.

The algorithm has no convergence test here; for $k = 0$ the value is $x_0$.

**Reading.** Lean takes a fixed restart size and a specified number of cycles, using the exact
totalized GMRES step each time. The printed loop stops according to satisfaction of the convergence
check.
-/
noncomputable def gmresRestarted (A : Matrix (Fin n) (Fin n) 𝕜) (b : 𝔼) (m : ℕ) (x₀ : 𝔼)
    (k : ℕ) : 𝔼 :=
  (gmresCycle A b m)^[k] x₀

/-- $J(y) \ge 0$ for every $y$. -/
theorem J_nonneg {m : ℕ} (y : Fin m → 𝕜) : 0 ≤ J A b x₀ m y := norm_nonneg _

/-- If $\rho_1, \dots, \rho_m$ of the Arnoldi coefficients of $v_1$ are nonzero, then $J(y)^2 =
|\gamma_{m+1}|^2 + \|g_m - R_m y\|_2^2$ for every $y \in \mathbb{K}^m$. This is (6.43) of
[saad2003iterative] for GMRES.

**Reading.** The norm decomposition requires the active rotations to be unitary. Lean states nonzero
radii explicitly, and the general versions also allow complex coefficients.
-/
theorem sq_J_eq {m : ℕ}
    (hρ : ∀ k < m, Krylov.givensRho (arnoldiCoeff A (v₁ A b x₀)) k ≠ 0) (y : Fin m → 𝕜) :
    J A b x₀ m y ^ 2 = ‖γ (arnoldiCoeff A (v₁ A b x₀)) (β A b x₀ : 𝕜) m‖ ^ 2 +
      ‖(WithLp.toLp 2 (g (arnoldiCoeff A (v₁ A b x₀)) (β A b x₀ : 𝕜) m -
        R (arnoldiCoeff A (v₁ A b x₀)) m *ᵥ y) : EuclideanSpace 𝕜 (Fin m))‖ ^ 2 := by
  rw [J, smul_e₁_eq_firstVec, Hbar_eq_hessenbergOf]
  exact norm_sq_firstVec_sub_mulVec _ _ (arnoldiCoeff_v₁_eq_zero_of_lt A b x₀) hρ y

/-- The function $J$ is the least-squares function `SaadSparse.Chapter06.lsq` of the Arnoldi
coefficients of $v_1$, with $\beta = \|r_0\|_2$.

**Reading.** The source introduces $J$ as the original-space residual norm. Lean defines it as the
Hessenberg least-squares objective and proves equality with the original norm for prefixes at most
the grade.
-/
theorem J_eq_lsq (m : ℕ) : J A b x₀ m = lsq (arnoldiCoeff A (v₁ A b x₀)) (β A b x₀ : 𝕜) m := by
  funext y
  rw [J, smul_e₁_eq_firstVec, Hbar_eq_hessenbergOf, lsq]

/-- If $R_m$ is nonsingular, then the GMRES coordinates satisfy $R_m y_m = g_m$. -/
theorem mulVec_R_gmresY {m : ℕ} (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) :
    R (arnoldiCoeff A (v₁ A b x₀)) m *ᵥ gmresY A b x₀ m =
      g (arnoldiCoeff A (v₁ A b x₀)) (β A b x₀ : 𝕜) m :=
  mulVec_R_inv_mulVec_g _ _ hR

/-- **Proposition 6.9(2)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$,
$b, x_0 \in \mathbb{K}^n$ and $m \ge 0$, and let $R_m$ of the Arnoldi coefficients of $v_1$ be
nonsingular. Then $y_m = R_m^{-1} g_m$ minimizes $J$ over $\mathbb{K}^m$, and every minimizer of
$J$ equals $y_m$.

The proof specializes `SaadSparse.Chapter06.isMinOn_lsq` through
`SaadSparse.Chapter06.J_eq_lsq`.

**Reading.** The inverse formula gives the unique minimizer when the triangular factor is
nonsingular. Lean makes that assumption explicit, as used in the source proof. The same argument
also applies to complex least squares.
-/
theorem proposition_6_9_2 {m : ℕ} (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) :
    IsMinOn (J A b x₀ m) Set.univ (gmresY A b x₀ m) ∧
      ∀ y, IsMinOn (J A b x₀ m) Set.univ y → y = gmresY A b x₀ m := by
  rw [J_eq_lsq]
  exact isMinOn_lsq _ _ (arnoldiCoeff_v₁_eq_zero_of_lt A b x₀) hR

/-- If $R_m$ is nonsingular, then the vector $x_m$ of Algorithm 6.9 is a GMRES approximation at step
$m$.

**Reading.** The inverse formula gives the unique minimizer when the triangular factor is
nonsingular. Lean makes that assumption explicit, as used in the source proof. The same argument
also applies to complex least squares.
-/
theorem gmresFixed_isGMRESIterate {m : ℕ} (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) :
    IsGMRESIterate A b x₀ m (gmresFixed A b x₀ m) :=
  ⟨gmresY A b x₀ m, (proposition_6_9_2 A b x₀ hR).1, rfl⟩

/-- If $m$ is at most the grade of $v_1$ and $R_m$ is nonsingular, then the vector $x_m$ of
Algorithm 6.9 is the minimal-residual iterate on $\mathcal{K}_m(A, r_0)$.

**Reading.** The inverse formula gives the unique minimizer when the triangular factor is
nonsingular. Lean makes that assumption explicit, as used in the source proof. The same argument
also applies to complex least squares.
-/
theorem gmresFixed_isMinResidualIterate {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀))
    (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) :
    Krylov.IsMinResidualIterate (op A) b x₀ m (gmresFixed A b x₀ m) :=
  (isGMRESIterate_iff A b x₀ hm).1 (gmresFixed_isGMRESIterate A b x₀ hR)

/-! ### Proposition 6.9(1), (6.41) and (6.42) -/

/-- Proposition 6.9(1) of [saad2003iterative], in the direction that the book uses. Let $A$ be
nonsingular and let $m$ be at most the grade of $v_1$. Then $R_m$ is nonsingular. Equivalently,
if a diagonal entry of $R_m$ is zero, then $A$ is singular.

Below the grade this is `Krylov.givensRho_arnoldi_ne_zero`. At the grade $\mu$ the proof is the
book's: a nonsingular $A$ maps the invariant subspace $\mathcal{K}_\mu$ bijectively onto itself,
so the Galerkin approximation at step $\mu$ exists and is unique, $H_\mu$ is nonsingular, and
$c_\mu \neq 0$. -/
theorem isUnit_R_of_isUnit {m : ℕ} (hA : IsUnit A) (hm : m ≤ grade A (v₁ A b x₀)) :
    IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m) := by
  have hinj : Function.Injective (op A) := injective_op_of_isUnit hA
  have hm' : m ≤ Krylov.grade (op A) (r₀ A b x₀) := by rwa [← grade_v₁]
  refine (isUnit_R_iff _ (arnoldiCoeff_v₁_eq_zero_of_lt A b x₀)).2 fun k hk => ?_
  rw [arnoldiCoeff_v₁]
  rcases lt_or_ge (k + 1) (Krylov.grade (op A) (r₀ A b x₀)) with h1 | h1
  · exact Krylov.givensRho_arnoldi_ne_zero h1
  · have hgal : ∃! x, Krylov.IsGalerkinIterate (op A) b x₀ (k + 1) x := by
      obtain ⟨x, hx⟩ := Krylov.exists_isMinResidualIterate (op A) b x₀ (k + 1)
      have hAx : op A x = b := hx.apply_eq_of_grade_le h1 hinj.injOn
      refine ⟨x, ⟨hx.mem, ?_⟩, fun z hz => hinj ?_⟩
      · rw [hAx, sub_self]
        exact Submodule.zero_mem _
      · rw [hAx, hz.apply_eq_of_grade_le h1]
    have hU : IsUnit (Arnoldi.hessenbergSq (op A) (r₀ A b x₀) (k + 1)) :=
      (Krylov.existsUnique_isGalerkinIterate_iff_isUnit (le_trans hk hm')).1 hgal
    have hc := (Krylov.isUnit_hessenbergSq_iff_givensC_ne_zero (le_trans hk hm')).1 hU
    exact Krylov.givensRho_ne_zero_of_rotated_ne_zero _
      fun h0 => hc ((Krylov.givensC_eq_zero_iff _ k).2 h0)

/-- **Equation (6.41)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$,
$b, x_0 \in \mathbb{K}^n$ and $m \ge 0$, and let $R_m$ be nonsingular. Then the residual of the
approximation $x_m$ of Algorithm 6.9 is
$$b - Ax_m = V_{m+1} Q_m^H (\gamma_{m+1} e_{m+1}),$$
where $e_{m+1}$ is the last coordinate vector of $\mathbb{K}^{m+1}$.

Over $\mathbb{R}$, $Q_m^H = Q_m^T$ as in the book. The identity needs no hypothesis on the grade
of $v_1$.

**Reading.** The residual formulas require a nonsingular triangular factor, and the original
residual norm formula also requires the valid-prefix bound. For complex scalars the inverse rotation
is the conjugate transpose.
-/
theorem equation_6_41 {m : ℕ} (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) :
    b - op A (gmresFixed A b x₀ m) =
      Matrix.toEuclideanLin (V A (v₁ A b x₀) (m + 1))
        (WithLp.toLp 2 ((Qrot (arnoldiCoeff A (v₁ A b x₀)) m)ᴴ *ᵥ
          Pi.single (Fin.last m) (γ (arnoldiCoeff A (v₁ A b x₀)) (β A b x₀ : 𝕜) m))) := by
  have hρ := (isUnit_R_iff _ (arnoldiCoeff_v₁_eq_zero_of_lt A b x₀)).1 hR
  have hQ := Qrot_mem_unitaryGroup (arnoldiCoeff A (v₁ A b x₀)) m hρ
  have h1 : (Qrot (arnoldiCoeff A (v₁ A b x₀)) m)ᴴ * Qrot (arnoldiCoeff A (v₁ A b x₀)) m = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff' (A := Qrot (arnoldiCoeff A (v₁ A b x₀)) m)).1 hQ
    rwa [Matrix.star_eq_conjTranspose] at h
  rw [gmresFixed, equation_6_27, smul_e₁_eq_firstVec, Hbar_eq_hessenbergOf]
  congr 2
  conv_lhs => rw [← Matrix.one_mulVec (Krylov.firstVec (β A b x₀ : 𝕜) (m + 1) -
    Krylov.hessenbergOf (arnoldiCoeff A (v₁ A b x₀)) m *ᵥ gmresY A b x₀ m), ← h1]
  rw [← Matrix.mulVec_mulVec, Qrot_mulVec_firstVec_sub,
    gbar_sub_Rbar_mulVec _ _ (arnoldiCoeff_v₁_eq_zero_of_lt A b x₀) (mulVec_R_gmresY A b x₀ hR)]

/-- **Equation (6.42)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$ and
$b, x_0 \in \mathbb{K}^n$, let $m$ be at most the grade of $v_1$, and let $R_m$ be nonsingular.
Then the approximation $x_m$ of Algorithm 6.9 satisfies
$$\|b - Ax_m\|_2 = |\gamma_{m+1}|.$$

So the residual norm can be read off the rotated right-hand side.

**Reading.** The residual formulas require a nonsingular triangular factor, and the original
residual norm formula also requires the valid-prefix bound. For complex scalars the inverse rotation
is the conjugate transpose.
-/
theorem equation_6_42 {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀))
    (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) :
    ‖b - op A (gmresFixed A b x₀ m)‖ =
      ‖γ (arnoldiCoeff A (v₁ A b x₀)) (β A b x₀ : 𝕜) m‖ := by
  have hρ := (isUnit_R_iff _ (arnoldiCoeff_v₁_eq_zero_of_lt A b x₀)).1 hR
  rw [arnoldiCoeff_v₁] at hρ ⊢
  exact Krylov.IsMinResidualIterate.norm_residual_eq_norm_gamma_of_givensRho_ne_zero
    (by rwa [← grade_v₁]) hρ (gmresFixed_isMinResidualIterate A b x₀ hm hR)

/-- Let $m + 1$ be at most the grade of $v_1$, let $R_{m+1}$ be nonsingular, and let $s_{m+1} = 0$.
Then the approximation of Algorithm 6.9 at step $m + 1$ is exact: $A x_{m+1} = b$. This follows
from (6.47) and (6.42) of [saad2003iterative]. -/
theorem apply_eq_of_s_eq_zero {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀))
    (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) (m + 1)))
    (hs : s (arnoldiCoeff A (v₁ A b x₀)) m = 0) : op A (gmresFixed A b x₀ (m + 1)) = b := by
  have h1 := equation_6_42 A b x₀ hm hR
  rw [gamma_succ, hs, neg_zero, zero_mul, norm_zero] at h1
  exact (sub_eq_zero.1 (norm_le_zero_iff.1 h1.le)).symm

/-! ### Problem P-6.5: GMRES from the projection formula (5.7) -/

/-- Problem P-6.5 of [saad2003iterative]. If $R_m$ is nonsingular, then the GMRES coordinates
satisfy the normal equations $\bar H_m^H \bar H_m y_m = \bar H_m^H (\beta e_1)$ of the
least-squares problem (6.29). This is the projection formula (5.7) with $V = V_m$ and
$W = A V_m$. -/
theorem normal_equations_gmresY {m : ℕ} (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) :
    ((Hbar A (v₁ A b x₀) m)ᴴ * Hbar A (v₁ A b x₀) m) *ᵥ gmresY A b x₀ m
      = (Hbar A (v₁ A b x₀) m)ᴴ *ᵥ ((β A b x₀ : 𝕜) • e₁ (m + 1)) := by
  have hρ := (isUnit_R_iff _ (arnoldiCoeff_v₁_eq_zero_of_lt A b x₀)).1 hR
  rw [Hbar_eq_hessenbergOf, smul_e₁_eq_firstVec]
  exact normal_equations _ _ (arnoldiCoeff_v₁_eq_zero_of_lt A b x₀) hρ (mulVec_R_gmresY A b x₀ hR)

/-- **Problem P-6.5** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$,
$b, x_0 \in \mathbb{K}^n$ and $m \ge 0$, and let $R_m$ be nonsingular. Then
$$y_m = (\bar H_m^H \bar H_m)^{-1} \bar H_m^H (\beta e_1).$$
So GMRES is the projection formula (5.7) with $V = V_m$ and $W = A V_m$.

The real statement with transposes is `SaadSparse.Chapter06.problem_6_5_book`. -/
theorem problem_6_5 {m : ℕ} (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) :
    gmresY A b x₀ m = ((Hbar A (v₁ A b x₀) m)ᴴ * Hbar A (v₁ A b x₀) m)⁻¹ *ᵥ
      ((Hbar A (v₁ A b x₀) m)ᴴ *ᵥ ((β A b x₀ : 𝕜) • e₁ (m + 1))) := by
  have hρ := (isUnit_R_iff _ (arnoldiCoeff_v₁_eq_zero_of_lt A b x₀)).1 hR
  have hN : IsUnit ((Hbar A (v₁ A b x₀) m)ᴴ * Hbar A (v₁ A b x₀) m) := by
    rw [Hbar_eq_hessenbergOf]
    exact isUnit_conjTranspose_mul_self_hessenbergOf _ (arnoldiCoeff_v₁_eq_zero_of_lt A b x₀) hρ hR
  rw [← normal_equations_gmresY A b x₀ hR, Matrix.nonsing_inv_mulVec_mulVec hN]

/-! ### Proposition 6.10 and the bound of $n$ steps -/

/-- **Proposition 6.10** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$ be nonsingular,
$b, x_0 \in \mathbb{K}^n$, and let $1 \le j \le \operatorname{grade}(v_1)$. Then GMRES breaks
down at step $j$, that is $h_{j+1,j} = 0$, if and only if the approximation $x_j$ of Algorithm
6.9 is exact:
$$h_{j+1,j} = 0 \iff A x_j = b.$$

The coefficient $h_{j+1,j}$ is `arnoldiCoeff A (v₁ A b x₀) j (j - 1)`. The hypothesis
$j \le \operatorname{grade}(v_1)$ stands for the book's assumption that the first $j$ steps were
taken; `SaadSparse.Chapter06.proposition_6_10_book` states the result in the book's form.

**Generalization.** The exactness and breakdown equivalence is stated for a step within the grade
and also applies over the complex scalars. The source implicitly uses a step that the algorithm
reaches.
-/
theorem proposition_6_10 (hA : IsUnit A) {j : ℕ} (hj : 0 < j) (hjg : j ≤ grade A (v₁ A b x₀)) :
    arnoldiCoeff A (v₁ A b x₀) j (j - 1) = 0 ↔ op A (gmresFixed A b x₀ j) = b := by
  have hj1 : j - 1 + 1 = j := by omega
  have hbd : arnoldiCoeff A (v₁ A b x₀) j (j - 1) = 0 ↔
      Krylov.grade (op A) (r₀ A b x₀) ≤ j := by
    rw [arnoldiCoeff_v₁, ← hj1]
    exact Arnoldi.coeff_succ_self_eq_zero_iff (op A) (r₀ A b x₀) (j - 1)
  have hx := gmresFixed_isMinResidualIterate A b x₀ hjg (isUnit_R_of_isUnit A b x₀ hA hjg)
  rw [hbd]
  refine ⟨fun hg => hx.apply_eq_of_grade_le hg (injective_op_of_isUnit hA).injOn, fun hex => ?_⟩
  exact Krylov.grade_le_of_apply_eq hx.mem hex

/-- Section 6.5.5 of [saad2003iterative]. Let $A$ be nonsingular and $m \ge n$. Then full GMRES,
Algorithm 6.9 with the stopping rule, is exact after $m$ steps: $A x_m = b$. -/
theorem gmres_apply_eq (hA : IsUnit A) {m : ℕ} (hmn : n ≤ m) : op A (gmres A b x₀ m) = b := by
  have hg : grade A (v₁ A b x₀) ≤ n := grade_le_card A _
  have hmEff : mEff A b x₀ m = grade A (v₁ A b x₀) := min_eq_right (le_trans hg hmn)
  rw [gmres, hmEff]
  exact (gmresFixed_isMinResidualIterate A b x₀ le_rfl
    (isUnit_R_of_isUnit A b x₀ hA le_rfl)).apply_eq_of_grade_le (by rw [← grade_v₁])
    (injective_op_of_isUnit hA).injOn

/-- Let $A$ be nonsingular. Then full GMRES is exact at some step $m \le n$. -/
theorem exists_gmres_apply_eq (hA : IsUnit A) : ∃ m ≤ n, op A (gmres A b x₀ m) = b :=
  ⟨n, le_rfl, gmres_apply_eq A b x₀ hA le_rfl⟩

end GMRES

/-!
### Section 6.5.2: Algorithm 6.10, Householder GMRES

In this part $A \in \mathbb{R}^{n \times n}$, and the Arnoldi basis is the Householder basis of
Algorithm 6.3 (`SaadSparse.Chapter06.hhV`).
-/

section Householder

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin n)

/-- **Equations (6.31)–(6.33)** of [saad2003iterative], the accumulation in Algorithm 6.10. For
linear maps $P_i$ of $\mathbb{R}^n$ and scalars $\eta_i$, the vector $z_{j,l}$ is the result of
the loop $z := P_i(\eta_i e_i + z)$ for $i = j + l - 1, \dots, j + 1, j$, started from $z = 0$:
$$z_{j,0} = 0, \qquad z_{j,l+1} = P_j(\eta_j e_j + z_{j+1,l}).$$

Indices are `0`-based, and the book's loop over $j = m, m - 1, \dots, 1$ is
`hornerAccumulate P η 0 m`. The vector $e_j$ is `SaadSparse.Chapter06.stdVec j`, which is $0$
for $j \ge n$. -/
noncomputable def hornerAccumulate (P : ℕ → (𝔼 →ₗ[ℝ] 𝔼)) (η : ℕ → ℝ) : ℕ → ℕ → 𝔼
  | _, 0 => 0
  | j, l + 1 => P j (η j • stdVec j + hornerAccumulate P η (j + 1) l)

variable (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : EuclideanSpace ℝ (Fin n))

/-- The inner loop of (6.31)–(6.33) started at index $j + 1$ and followed by $Q_j^T$ is the partial
sum $\sum_{i < l} \eta_{j+1+i} v_{j+1+i}$ over the Householder Arnoldi vectors. -/
private theorem QhhT_hornerAccumulate (v : 𝔼) (η : ℕ → ℝ) :
    ∀ (l j : ℕ), QhhT A v j (hornerAccumulate (fun i => householder (hhW A v i)) η (j + 1) l)
      = ∑ i ∈ Finset.range l, η (j + 1 + i) • hhV A v (j + 1 + i) := by
  intro l
  induction l with
  | zero => intro j; simp [hornerAccumulate]
  | succ l ih =>
    intro j
    rw [hornerAccumulate, ← LinearMap.comp_apply, ← QhhT_succ, map_add, map_smul, ih (j + 1),
      Finset.sum_range_succ']
    have hs : ∑ i ∈ Finset.range l, η (j + 1 + (i + 1)) • hhV A v (j + 1 + (i + 1))
        = ∑ i ∈ Finset.range l, η (j + 1 + 1 + i) • hhV A v (j + 1 + 1 + i) :=
      Finset.sum_congr rfl fun i _ => by rw [show j + 1 + (i + 1) = j + 1 + 1 + i by omega]
    rw [hs]
    exact add_comm _ _

/-- Let $P_j$ be the Householder reflectors of Algorithm 6.3 for the starting vector $v$. Then the
accumulation (6.31)–(6.33) of Algorithm 6.10 over $m$ steps computes $\sum_{j < m} \eta_j v_j$,
where the $v_j$ are the Householder Arnoldi vectors with `0`-based indices. -/
theorem hornerAccumulate_eq_sum (v : 𝔼) (η : ℕ → ℝ) (m : ℕ) :
    hornerAccumulate (fun i => householder (hhW A v i)) η 0 m
      = ∑ i ∈ Finset.range m, η i • hhV A v i := by
  cases m with
  | zero => simp [hornerAccumulate]
  | succ l =>
    rw [hornerAccumulate]
    have h0 : (householder (hhW A v 0) : 𝔼 →ₗ[ℝ] 𝔼) = QhhT A v 0 := (QhhT_zero A v).symm
    rw [h0, map_add, map_smul, QhhT_hornerAccumulate A v η l 0, Finset.sum_range_succ']
    have hs : ∑ i ∈ Finset.range l, η (0 + 1 + i) • hhV A v (0 + 1 + i)
        = ∑ i ∈ Finset.range l, η (i + 1) • hhV A v (i + 1) :=
      Finset.sum_congr rfl fun i _ => by rw [show 0 + 1 + i = i + 1 by omega]
    rw [hs]
    exact add_comm _ _

/-- Algorithm 6.10 of [saad2003iterative], line 1: the scalar $\beta = e_1^T h_0$, the first
coordinate of the first Householder column $h_0$ for the starting vector $r_0$.

**Reading.** Lean uses the signed first reflected entry. It is $-\beta$ for the separate Householder
convention in (1.26); its absolute value is the initial residual norm. The coordinate function
returns zero for a missing first coordinate.
-/
noncomputable def βHH (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : 𝔼) : ℝ :=
  coordAt (hhH A (r₀ A b x₀) 0) 0

/-- If $n \ge 1$, the Householder scalar $\beta$ of Algorithm 6.10 is the negative of the scalar
$\beta$ of (1.25) of [saad2003iterative] for $r_0$ at the first position
(`SaadSparse.Chapter06.householderBeta`).

**Reading.** Lean uses the signed first reflected entry. It is $-\beta$ for the separate Householder
convention in (1.26); its absolute value is the initial residual norm. The coordinate function
returns zero for a missing first coordinate.
-/
theorem βHH_eq (hn : 0 < n) : βHH A b x₀ = -householderBeta (r₀ A b x₀) 0 := by
  rw [βHH, hhH_zero, coordAt, dite_eq_left hn]
  simp [stdVec_coord]

/-- If $n \ge 1$, the Householder scalar $\beta$ of Algorithm 6.10 satisfies $|\beta| = \|r_0\|_2$.

**Reading.** Lean uses the signed first reflected entry. It is $-\beta$ for the separate Householder
convention in (1.26); its absolute value is the initial residual norm. The coordinate function
returns zero for a missing first coordinate.
-/
theorem abs_βHH (hn : 0 < n) : |βHH A b x₀| = ‖r₀ A b x₀‖ := by
  rw [βHH_eq A b x₀ hn, abs_neg, abs_householderBeta_zero]

/-- If $n \ge 1$, then $r_0 = \beta v_1$ for the Householder scalar $\beta$ and the first
Householder Arnoldi vector $v_1$. This is the hypothesis of the residual formula for a
Hessenberg relation.

**Reading.** Lean uses the signed first reflected entry. It is $-\beta$ for the separate Householder
convention in (1.26); its absolute value is the initial residual norm. The coordinate function
returns zero for a missing first coordinate.
-/
theorem βHH_smul_hhV_zero (hn : 0 < n) :
    b - op A x₀ = βHH A b x₀ • hhV A (r₀ A b x₀) 0 := by
  rw [βHH_eq A b x₀ hn]
  exact (smul_hhV_zero A (r₀ A b x₀)).symm

/-- For an orthonormal family $e_1, \dots, e_N$, $\|\sum_i c_i e_i\| = \|c\|_2$. -/
private theorem norm_sum_smul_of_orthonormal {N : ℕ} {e : Fin N → 𝔼} (he : Orthonormal ℝ e)
    (cc : Fin N → ℝ) :
    ‖∑ i, cc i • e i‖ = ‖(WithLp.toLp 2 cc : EuclideanSpace ℝ (Fin N))‖ := by
  have h1 : ‖∑ i, cc i • e i‖ ^ 2 = ∑ i, ‖cc i‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, he.inner_sum cc cc Finset.univ]
    exact Finset.sum_congr rfl fun i _ => by
      simp [Real.norm_eq_abs, sq]
  have h2 : ‖(WithLp.toLp 2 cc : EuclideanSpace ℝ (Fin N))‖ ^ 2 = ∑ i, ‖cc i‖ ^ 2 :=
    EuclideanSpace.norm_sq_eq _
  nlinarith [norm_nonneg (∑ i, cc i • e i),
    norm_nonneg (WithLp.toLp 2 cc : EuclideanSpace ℝ (Fin N)), h1, h2]

/-- Let $m + 1 \le n$. For every $y \in \mathbb{R}^m$, the residual norm of
$x_0 + \sum_{j=1}^m y_j v^{HH}_j$, with the Householder Arnoldi vectors $v^{HH}_j$, is
$\|\beta e_1 - \bar H^{HH}_m y\|_2$, with the Householder scalar $\beta$ and the Householder
Hessenberg coefficients (`SaadSparse.Chapter06.hhCoeff`). This is the least-squares problem of
(6.28) with the Householder data. -/
theorem norm_residual_hh {m : ℕ} (hn : m + 1 ≤ n) (y : Fin m → ℝ) :
    ‖b - op A (x₀ + ∑ j : Fin m, y j • hhV A (r₀ A b x₀) (j : ℕ))‖
      = lsq (hhCoeff A (r₀ A b x₀)) (βHH A b x₀) m y := by
  have hn0 : 0 < n := by omega
  rw [(hh_hessenbergRelation A (r₀ A b x₀)).residual_eq (βHH_smul_hhV_zero A b x₀ hn0) m y,
    norm_sum_smul_of_orthonormal (hh_orthonormal A (r₀ A b x₀) hn), lsq]

/-- Algorithm 6.10 of [saad2003iterative], line 12: the coordinates $y_m = R_m^{-1} g_m$ for the
Givens data of the Householder Hessenberg coefficients, with the Householder scalar $\beta$.

**Reading.** The fixed-size Householder program uses the triangular least-squares inverse, which is
zero at a singular reduced factor, instead of the abstract minimization in line 11. The underlying
reflector recurrence uses identity reflectors for zero tails.
-/
noncomputable def gmresHHY (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : 𝔼) (m : ℕ) : Fin m → ℝ :=
  (R (hhCoeff A (r₀ A b x₀)) m)⁻¹ *ᵥ g (hhCoeff A (r₀ A b x₀)) (βHH A b x₀) m

/-- **Algorithm 6.10** of [saad2003iterative] (Householder GMRES). The approximation
$$x_m = x_0 + z,$$
where $z$ is accumulated by (6.31)–(6.33) from the Householder reflectors of $r_0$ and the
coefficients $\eta_j$, the entries of $y_m$ (`SaadSparse.Chapter06.gmresHHY`).

The coefficients $\eta_j$ with $j \ge m$ are $0$. `SaadSparse.Chapter06.gmresHH_eq` proves that
the result is the approximation of Algorithm 6.9.

**Reading.** The fixed-size Householder program uses the triangular least-squares inverse, which is
zero at a singular reduced factor, instead of the abstract minimization in line 11. The underlying
reflector recurrence uses identity reflectors for zero tails.
-/
noncomputable def gmresHH (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : 𝔼) (m : ℕ) : 𝔼 :=
  x₀ + hornerAccumulate (fun i => householder (hhW A (r₀ A b x₀) i))
    (fun i => if h : i < m then gmresHHY A b x₀ m ⟨i, h⟩ else 0) 0 m

/-- The approximation of Algorithm 6.10 is $x_0 + \sum_{j=1}^m (y_m)_j v^{HH}_j$, with the
Householder Arnoldi vectors $v^{HH}_j$. -/
theorem gmresHH_eq_add_sum (m : ℕ) :
    gmresHH A b x₀ m = x₀ + ∑ j : Fin m, gmresHHY A b x₀ m j • hhV A (r₀ A b x₀) (j : ℕ) := by
  rw [gmresHH, hornerAccumulate_eq_sum,
    ← Fin.sum_univ_eq_sum_range
      (fun i => (if h : i < m then gmresHHY A b x₀ m ⟨i, h⟩ else 0) •
        hhV A (r₀ A b x₀) i) m]
  refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
  rw [dite_eq_left j.isLt]

/-- Let $m + 1 \le n$, let $m$ be at most the grade of $r_0$, and let $R_m$ of the Householder
Hessenberg coefficients be nonsingular. Then Algorithm 6.10 computes the minimal-residual
iterate on $\mathcal{K}_m(A, r_0)$. The Householder basis is orthonormal and spans the same
Krylov subspaces, so the least-squares problem is the same problem in another orthonormal basis.

**Reading.** The specification uses an extended basis fitting in the ambient dimension, a prefix
within the grade, and a nonsingular triangular factor. The comparison with Gram–Schmidt GMRES uses
nonsingularity of the system for uniqueness.
-/
theorem gmresHH_isMinResidualIterate {m : ℕ} (hn : m + 1 ≤ n) (hm : m ≤ grade A (r₀ A b x₀))
    (hR : IsUnit (R (hhCoeff A (r₀ A b x₀)) m)) :
    Krylov.IsMinResidualIterate (op A) b x₀ m (gmresHH A b x₀ m) := by
  have hrange : (Set.range fun i : Fin m => hhV A (r₀ A b x₀) (i : ℕ))
      = hhV A (r₀ A b x₀) '' Set.Iio m := by
    ext w
    simp only [Set.mem_range, Set.mem_image, Set.mem_Iio, Fin.exists_iff]
    tauto
  have hspan : Submodule.span ℝ (Set.range fun i : Fin m => hhV A (r₀ A b x₀) (i : ℕ))
      = Krylov.subspace (op A) (r₀ A b x₀) m := by
    rw [hrange, span_hhV_eq A _ (by omega) hm, krylov_eq]
  have hmin := (isMinOn_lsq (hhCoeff A (r₀ A b x₀)) (βHH A b x₀)
    (fun i j hij => hhCoeff_eq_zero_of_lt A _ hij) hR).1
  refine ⟨?_, fun w hw => ?_⟩
  · rw [gmresHH_eq_add_sum, add_sub_cancel_left, ← hspan]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rw [← hspan] at hw
    obtain ⟨zz, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hw
    have hwe : w = x₀ + ∑ j : Fin m, zz j • hhV A (r₀ A b x₀) (j : ℕ) := by
      rw [hz]
      abel
    rw [gmresHH_eq_add_sum, hwe, norm_residual_hh A b x₀ hn, norm_residual_hh A b x₀ hn]
    exact isMinOn_iff.1 hmin zz (Set.mem_univ zz)

/-- **Algorithm 6.10** of [saad2003iterative], Section 6.5.2. Let $A \in \mathbb{R}^{n \times n}$ be
nonsingular, $b, x_0 \in \mathbb{R}^n$, $m + 1 \le n$ and $m \le \operatorname{grade}(v_1)$, and
let $R_m$ of the Householder Hessenberg coefficients be nonsingular. Then Algorithm 6.10
computes the GMRES approximation of Algorithm 6.9:
$$x^{HH}_m = x_m.$$

The proof combines `SaadSparse.Chapter06.gmresHH_isMinResidualIterate` with the uniqueness of
the minimal-residual iterate for nonsingular $A$.

**Reading.** The specification uses an extended basis fitting in the ambient dimension, a prefix
within the grade, and a nonsingular triangular factor. The comparison with Gram–Schmidt GMRES uses
nonsingularity of the system for uniqueness.
-/
theorem gmresHH_eq {m : ℕ} (hn : m + 1 ≤ n) (hm : m ≤ grade A (v₁ A b x₀)) (hA : IsUnit A)
    (hR : IsUnit (R (hhCoeff A (r₀ A b x₀)) m)) :
    gmresHH A b x₀ m = gmresFixed A b x₀ m := by
  obtain ⟨xx, -, huniq⟩ := Krylov.existsUnique_isMinResidualIterate_of_injective
    (injective_op_of_isUnit hA) b x₀ m
  have hmr : m ≤ grade A (r₀ A b x₀) := by
    rw [grade_eq, ← grade_v₁]
    exact hm
  rw [huniq _ (gmresHH_isMinResidualIterate A b x₀ hn hmr hR),
    huniq _ (gmresFixed_isMinResidualIterate A b x₀ hm (isUnit_R_of_isUnit A b x₀ hA hm))]

end Householder

/-! ### The numbered results of Sections 6.5.1–6.5.5 over $\mathbb{R}$ -/

section BookResultsGMRES

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : EuclideanSpace ℝ (Fin n))

/-- Equation (6.27) of [saad2003iterative] over $\mathbb{R}$: for $A \in \mathbb{R}^{n \times n}$
and every $y \in \mathbb{R}^m$, $b - A(x_0 + V_m y) = V_{m+1}(\beta e_1 - \bar H_m y)$.

**Generalization.** The identity also holds with the zero-padded sequence, including zero initial
residual. The general version applies to complex scalars.
-/
theorem residual_eq_6_27 {m : ℕ} (y : Fin m → ℝ) :
    b - op A (krylovIterate A b x₀ m y) =
      Matrix.toEuclideanLin (V A (v₁ A b x₀) (m + 1))
        (WithLp.toLp 2 ((β A b x₀ : ℝ) • e₁ (m + 1) - Hbar A (v₁ A b x₀) m *ᵥ y)) :=
  equation_6_27 A b x₀ y

/-- Equation (6.28) of [saad2003iterative] over $\mathbb{R}$: if $m$ is at most the grade of $v_1$,
then $\|b - A(x_0 + V_m y)\|_2 = J(y) = \|\beta e_1 - \bar H_m y\|_2$ for every
$y \in \mathbb{R}^m$.

**Reading.** Lean permits the step at the grade, where the next basis vector is zero. Its
coefficient in the residual vanishes, so the norm equality still holds even though the source's
proof describes all the columns of the extended basis as orthonormal.
-/
theorem residual_eq_6_28 {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀)) (y : Fin m → ℝ) :
    ‖b - op A (krylovIterate A b x₀ m y)‖ = J A b x₀ m y :=
  equation_6_28 A b x₀ hm y

/-- Equations (6.29)–(6.30) of [saad2003iterative] over $\mathbb{R}$: if $m$ is at most the grade of
$v_1$, then $x$ is a GMRES approximation at step $m$ if and only if $x$ is the minimal-residual
iterate on $\mathcal{K}_m(A, r_0)$.

**Reading.** The minimizer predicate describes all minimizers. Lean separates existence from
uniqueness and makes the valid-prefix hypothesis explicit in its equivalence with minimization of
the original residual.
-/
theorem gmres_isMinResidualIterate_iff {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀))
    {x : EuclideanSpace ℝ (Fin n)} :
    IsGMRESIterate A b x₀ m x ↔ Krylov.IsMinResidualIterate (op A) b x₀ m x :=
  isGMRESIterate_iff A b x₀ hm

/-- **Equations (6.29)–(6.30)** of [saad2003iterative], uniqueness. Let
$A \in \mathbb{R}^{n \times n}$ be nonsingular, $b, x_0 \in \mathbb{R}^n$, and let $m$ be at
most the grade of $v_1$. Then there is exactly one GMRES approximation at step $m$.

So "the" GMRES approximation is well defined. `SaadSparse.Chapter06.gmresFixed_isGMRESIterate`
identifies it with the vector that Algorithm 6.9 computes.

**Reading.** The source calls the minimizer unique. Lean requires a nonsingular system matrix and
the grade bound, ensuring injectivity of the system operator on the search space.
-/
theorem gmres_unique {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀)) (hA : IsUnit A) :
    ∃! x, IsGMRESIterate A b x₀ m x :=
  existsUnique_isGMRESIterate A b x₀ hm hA

/-- **Proposition 6.9** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ be nonsingular,
$b, x_0 \in \mathbb{R}^n$, and let $m$ be at most the grade of $v_1$. Then $R_m$ is nonsingular,
$y_m = R_m^{-1} g_m$ is the unique minimizer of $J$ over $\mathbb{R}^m$, and the approximation
$x_m$ of Algorithm 6.9 satisfies
$$\|b - Ax_m\|_2 = |\gamma_{m+1}|.$$

The residual vector (6.41) is `SaadSparse.Chapter06.equation_6_41`.

**Reading.** The source prints $m \le n$. Lean requires $m \le \operatorname{grade}(v_1)$ so the
first $m$ basis vectors are available. Part (1) is represented by the implication that $R_m$ is
nonsingular when $A$ is nonsingular. The source states a general rank equality for $AV_m$ and $R_m$.
-/
theorem proposition_6_9 {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀)) (hA : IsUnit A) :
    IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m) ∧
      (IsMinOn (J A b x₀ m) Set.univ (gmresY A b x₀ m) ∧
        ∀ y, IsMinOn (J A b x₀ m) Set.univ y → y = gmresY A b x₀ m) ∧
      ‖b - op A (gmresFixed A b x₀ m)‖ =
        ‖γ (arnoldiCoeff A (v₁ A b x₀)) (β A b x₀ : ℝ) m‖ :=
  ⟨isUnit_R_of_isUnit A b x₀ hA hm, proposition_6_9_2 A b x₀ (isUnit_R_of_isUnit A b x₀ hA hm),
    equation_6_42 A b x₀ hm (isUnit_R_of_isUnit A b x₀ hA hm)⟩

/-- **Proposition 6.10** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ be nonsingular
and $b, x_0 \in \mathbb{R}^n$ with $r_0 \neq 0$. Let $j \ge 1$, and assume that the Arnoldi
process has no breakdown before step $j$: $h_{i+1,i} \neq 0$ for $1 \le i < j$. Then
$$h_{j+1,j} = 0 \iff A x_j = b,$$
where $x_j$ is the approximation of Algorithm 6.9.

**Reading.** The book leaves implicit the hypothesis that the first $j$ steps were taken. Here
it is the condition $h_{i+1,i} \neq 0$ for $i < j$ (`SaadSparse.Chapter06.NoBreakdownBefore`),
together with $r_0 \neq 0$, which makes $v_1$ a unit vector. -/
theorem proposition_6_10_book (hA : IsUnit A) (hr : r₀ A b x₀ ≠ 0) {j : ℕ} (hj : 0 < j)
    (hnb : NoBreakdownBefore A (v₁ A b x₀) j) :
    arnoldiCoeff A (v₁ A b x₀) j (j - 1) = 0 ↔ op A (gmresFixed A b x₀ j) = b :=
  proposition_6_10 A b x₀ hA hj ((noBreakdownBefore_iff A _ (norm_v₁ A b x₀ hr) j).1 hnb)

/-- **Problem P-6.5** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$,
$b, x_0 \in \mathbb{R}^n$ and $m \ge 0$, and let $R_m$ be nonsingular. Then the GMRES
coordinates solve the normal equations:
$$y_m = (\bar H_m^T \bar H_m)^{-1} \bar H_m^T (\beta e_1).$$
So GMRES is the projection formula (5.7) with $V = V_m$ and $W = A V_m$. -/
theorem problem_6_5_book {m : ℕ} (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) :
    gmresY A b x₀ m = ((Hbar A (v₁ A b x₀) m)ᵀ * Hbar A (v₁ A b x₀) m)⁻¹ *ᵥ
      ((Hbar A (v₁ A b x₀) m)ᵀ *ᵥ ((β A b x₀ : ℝ) • e₁ (m + 1))) := by
  have hT : (Hbar A (v₁ A b x₀) m)ᴴ = (Hbar A (v₁ A b x₀) m)ᵀ := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  rw [← hT]
  exact problem_6_5 A b x₀ hR

/-- **Algorithm 6.10** of [saad2003iterative] (Householder GMRES), Section 6.5.2. Let
$A \in \mathbb{R}^{n \times n}$ be nonsingular, $b, x_0 \in \mathbb{R}^n$, $m + 1 \le n$ and
$m \le \operatorname{grade}(v_1)$, and let $R_m$ of the Householder Hessenberg coefficients be
nonsingular. Then the scalar $\beta$ of line 1 satisfies $|\beta| = \|r_0\|_2$, the accumulation
(6.31)–(6.33) gives
$$x^{HH}_m = x_0 + \sum_{j=1}^m (y_m)_j v^{HH}_j$$
with the Householder Arnoldi vectors $v^{HH}_j$, and $x^{HH}_m$ is the approximation $x_m$ of
Algorithm 6.9.

**Reading.** The specification uses an extended basis fitting in the ambient dimension, a prefix
within the grade, and a nonsingular triangular factor. The comparison with Gram–Schmidt GMRES uses
nonsingularity of the system for uniqueness.
-/
theorem algorithm_6_10 {m : ℕ} (hn : m + 1 ≤ n) (hm : m ≤ grade A (v₁ A b x₀)) (hA : IsUnit A)
    (hR : IsUnit (R (hhCoeff A (r₀ A b x₀)) m)) :
    |βHH A b x₀| = ‖r₀ A b x₀‖ ∧
      gmresHH A b x₀ m = x₀ + ∑ j : Fin m, gmresHHY A b x₀ m j • hhV A (r₀ A b x₀) (j : ℕ) ∧
        gmresHH A b x₀ m = gmresFixed A b x₀ m :=
  ⟨abs_βHH A b x₀ (by omega), gmresHH_eq_add_sum A b x₀ m, gmresHH_eq A b x₀ hn hm hA hR⟩

/-- **Section 6.5.5** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ be nonsingular,
$b, x_0 \in \mathbb{R}^n$ and $m \ge n$. Then full GMRES, Algorithm 6.9 with the stopping rule,
is exact after $m$ steps: $A x_m = b$.

The stopping rule stops the Arnoldi process at the grade of $v_1$, which is at most $n$. -/
theorem gmres_exact_of_card_le (hA : IsUnit A) {m : ℕ} (hmn : n ≤ m) :
    op A (gmres A b x₀ m) = b :=
  gmres_apply_eq A b x₀ hA hmn

end BookResultsGMRES

/-!
### Section 6.5.6: QGMRES and DQGMRES

In this part the basis is an arbitrary sequence $v_1, v_2, \dots$ of vectors of $\mathbb{K}^n$ (`u`)
with a coefficient function $h$. Most results assume the Hessenberg relation
$A v_j = \sum_{i=1}^{j+1} h_{ij} v_i$ with $h$ upper Hessenberg
(`Krylov.HessenbergRelation (op A) u h`) and $b - Ax_0 = \beta v_1$. The incomplete
orthogonalization process of Algorithm 6.6 gives such a basis
(`SaadSparse.Chapter06.iop_hessenbergRelation`), and so does the Arnoldi process.
-/

section QGMRES

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-! ### Algorithm 6.12 (QGMRES) and the quantities of (6.52) -/

/-- The coordinates $y_m = R_m^{-1} g_m$ of Algorithm 6.12 (QGMRES) for a coefficient function $h$
and a scalar $\beta$: the formula of Proposition 6.9(2) applied to the coefficients of the
basis.

**Reading.** The definitions allow an arbitrary Hessenberg relation and real or complex
coefficients, and evaluate a fixed prefix. The source uses incomplete orthogonalization and a
least-squares minimizer. The Lean inverse is zero at singular R; the minimizer specifications
require nonsingular R.
-/
noncomputable def qgmresY (h : ℕ → ℕ → 𝕜) (β : 𝕜) (m : ℕ) : Fin m → 𝕜 :=
  (R h m)⁻¹ *ᵥ g h β m

/-- **Algorithm 6.12** of [saad2003iterative] (QGMRES). For vectors $v_1, v_2, \dots$ of
$\mathbb{K}^n$, a coefficient function $h$ and $\beta \in \mathbb{K}$, the approximation
$$x_m = x_0 + V_m y_m, \qquad y_m = R_m^{-1} g_m,$$
where $V_m = [v_1, \dots, v_m]$ and $R_m$, $g_m$ are the Givens data of $h$ and $\beta$.

The book's QGMRES uses the basis and the coefficients of Algorithm 6.6, that is
`u := SaadSparse.Chapter06.iop A v₁ k` and `h := SaadSparse.Chapter06.iopCoeff A v₁ k`. If $R_m$
is singular, then $y_m = 0$.

**Reading.** The definitions allow an arbitrary Hessenberg relation and real or complex
coefficients, and evaluate a fixed prefix. The source uses incomplete orthogonalization and a
least-squares minimizer. The Lean inverse is zero at singular R; the minimizer specifications
require nonsingular R.
-/
noncomputable def qgmres (x₀ : 𝔼) (u : ℕ → 𝔼) (h : ℕ → ℕ → 𝕜) (β : 𝕜) (m : ℕ) : 𝔼 :=
  x₀ + Matrix.toEuclideanLin (colMatrix u m) (WithLp.toLp 2 (qgmresY h β m))

/-- **Equation (6.52)** of [saad2003iterative]. The $n \times (m+1)$ matrix
$Z_{m+1} = V_{m+1} Q_m^H$.

**Generalization.** Lean uses the adjoint and the conjugates of the real update coefficients, so the
last-column formulas also hold for complex coefficients and arbitrary vector sequences.
-/
noncomputable def Z (u : ℕ → 𝔼) (h : ℕ → ℕ → 𝕜) (m : ℕ) : Matrix (Fin n) (Fin (m + 1)) 𝕜 :=
  colMatrix u (m + 1) * (Qrot h m)ᴴ

/-- **Equation (6.52)** of [saad2003iterative]. The vector $z_{m+1} = Z_{m+1} e_{m+1}$, the last
column of $Z_{m+1}$.

**Generalization.** Lean uses the adjoint and the conjugates of the real update coefficients, so the
last-column formulas also hold for complex coefficients and arbitrary vector sequences.
-/
noncomputable def z (u : ℕ → 𝔼) (h : ℕ → ℕ → 𝕜) (m : ℕ) : 𝔼 :=
  Matrix.toEuclideanLin (Z u h m) (WithLp.toLp 2 (Pi.single (Fin.last m) 1))

/-- The number $\zeta_{m+1} = \|z_{m+1}\|_2$ of (6.52) of [saad2003iterative]. -/
noncomputable def ζ (u : ℕ → 𝔼) (h : ℕ → ℕ → 𝕜) (m : ℕ) : ℝ := ‖z u h m‖

/-- **Section 6.5.6** of [saad2003iterative]. The **quasi-residual norm** $|\gamma_{m+1}|$ that
QGMRES and DQGMRES monitor, for a coefficient function $h$ and a scalar $\beta$. -/
noncomputable def quasiResidualNorm (h : ℕ → ℕ → 𝕜) (β : 𝕜) (m : ℕ) : ℝ := ‖γ h β m‖

/-- $z_{m+1} = V_{m+1} (Q_m^H e_{m+1})$.

**Generalization.** Lean uses the adjoint and the conjugates of the real update coefficients, so the
last-column formulas also hold for complex coefficients and arbitrary vector sequences.
-/
theorem z_eq (u : ℕ → 𝔼) (h : ℕ → ℕ → 𝕜) (m : ℕ) :
    z u h m = Matrix.toEuclideanLin (colMatrix u (m + 1))
      (WithLp.toLp 2 ((Qrot h m)ᴴ *ᵥ Pi.single (Fin.last m) 1)) := by
  rw [z, Z, Matrix.toEuclideanLin_toLp, Matrix.toEuclideanLin_toLp, Matrix.mulVec_mulVec]

/-- Let $h$ be upper Hessenberg and let $R_m$ be nonsingular. Then $y_m = R_m^{-1} g_m$ minimizes
the quasi-residual norm $\|\beta e_1 - \bar H_m y\|_2$ over $y \in \mathbb{K}^m$, and the
minimum is $|\gamma_{m+1}|$, as in (6.49) of [saad2003iterative]. If the basis is not
orthogonal, this is not the residual norm.

**Reading.** The definitions allow an arbitrary Hessenberg relation and real or complex
coefficients, and evaluate a fixed prefix. The source uses incomplete orthogonalization and a
least-squares minimizer. The Lean inverse is zero at singular R; the minimizer specifications
require nonsingular R.
-/
theorem qgmresY_isMinOn (h : ℕ → ℕ → 𝕜) (β : 𝕜) (hh : ∀ i j : ℕ, j + 1 < i → h i j = 0) {m : ℕ}
    (hR : IsUnit (R h m)) :
    IsMinOn (lsq h β m) Set.univ (qgmresY h β m) ∧
      lsq h β m (qgmresY h β m) = quasiResidualNorm h β m :=
  ⟨(isMinOn_lsq h β hh hR).1, lsq_eq_norm_gamma h β hh hR⟩

/-- **Equation (6.50)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$,
$b, x_0 \in \mathbb{K}^n$ and $\beta \in \mathbb{K}$. Let $v_1, v_2, \dots \in \mathbb{K}^n$ and
the upper Hessenberg coefficient function $h$ satisfy $A v_j = \sum_{i=1}^{j+1} h_{ij} v_i$, and
let $b - Ax_0 = \beta v_1$. If $R_m$ is nonsingular, then the QGMRES approximation $x_m$
satisfies
$$b - Ax_m = \gamma_{m+1} z_{m+1}.$$

Equation (6.41) stays true without orthogonality, because its proof uses only the Hessenberg
relation and the unitarity of the rotations.

**Generalization.** These identities use an abstract Hessenberg relation over real or complex
scalars. The relevant reduced matrices must be nonsingular. In the complex residual combination,
squared moduli replace the real coefficient squares.
-/
theorem equation_6_50 {A : Matrix (Fin n) (Fin n) 𝕜} {b x₀ : 𝔼} {u : ℕ → 𝔼} {h : ℕ → ℕ → 𝕜} {β : 𝕜}
    (hu : Krylov.HessenbergRelation (op A) u h) (hr : b - op A x₀ = β • u 0) {m : ℕ}
    (hR : IsUnit (R h m)) :
    b - op A (qgmres x₀ u h β m) = γ h β m • z u h m := by
  have hh := hu.eq_zero_of_lt
  have hρ := (isUnit_R_iff h hh).1 hR
  have hsingle : (Pi.single (Fin.last m) (γ h β m) : Fin (m + 1) → 𝕜)
      = γ h β m • Pi.single (Fin.last m) 1 := by
    funext j
    rcases eq_or_ne j (Fin.last m) with rfl | hj
    · simp
    · simp [Pi.single_eq_of_ne hj]
  rw [qgmres, toEuclideanLin_colMatrix_apply,
    hu.residual_eq hr m (qgmresY h β m), ← toEuclideanLin_colMatrix_apply u, qgmresY,
    firstVec_sub_mulVec_eq h β hh hρ (mulVec_R_inv_mulVec_g h β hR), hsingle, z_eq,
    Matrix.toEuclideanLin_toLp, Matrix.toEuclideanLin_toLp, Matrix.mulVec_smul, Matrix.mulVec_smul]
  rfl

/-- On the Arnoldi basis of $v_1$, with the Arnoldi coefficients and $\beta = \|r_0\|_2$, Algorithm
6.12 computes the approximation $x_m$ of Algorithm 6.9. This is the book's remark that QGMRES
coincides with GMRES when $k \ge m$, where the incomplete orthogonalization is the complete one. -/
theorem qgmres_eq_gmresFixed (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (m : ℕ) :
    qgmres x₀ (arnoldiCGS A (v₁ A b x₀)) (arnoldiCoeff A (v₁ A b x₀)) (β A b x₀ : 𝕜) m
      = gmresFixed A b x₀ m := rfl

/-!
### Equations (6.53)–(6.55): the progressive form of $z_{m+1}$

The rotations are indexed by $\mathbb{N}$, but their products are matrices of a fixed size, so
(6.53) compares $Q_m$ at two sizes. Write $Q^{(k)}_m$ for the product of the first $k$ rotations as
an $(m+1) \times (m+1)$ matrix (`Krylov.givensQAux`). The private lemmas below give facts that the
backbone does not have: the last row of a rotation, the rows of $Q^{(k)}_m$ beyond $k$ are rows of
the identity, and the leading block of $Q^{(k)}_{m+1}$ is $Q^{(k)}_m$.
-/

/-- $z_{m+1} = \sum_{k=1}^{m+1} \overline{(Q_m)_{m+1,k}} \, v_k$.

**Generalization.** Lean uses the adjoint and the conjugates of the real update coefficients, so the
last-column formulas also hold for complex coefficients and arbitrary vector sequences.
-/
theorem z_eq_sum (u : ℕ → 𝔼) (h : ℕ → ℕ → 𝕜) (m : ℕ) :
    z u h m = ∑ k : Fin (m + 1), starRingEnd 𝕜 (Qrot h m (Fin.last m) k) • u (k : ℕ) := by
  rw [z_eq, toEuclideanLin_colMatrix_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Pi.single_apply, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact (starRingEnd_apply _).symm

private theorem givensQ_succ_last_castSucc (h : ℕ → ℕ → 𝕜) (m : ℕ) (k : Fin (m + 1)) :
    Qrot h (m + 1) (Fin.last (m + 1)) k.castSucc = -(s h m) * Qrot h m (Fin.last m) k := by
  change Krylov.givensQAux h (m + 1) (m + 1) (Fin.last (m + 1)) k.castSucc
      = -Krylov.givensS h m * Krylov.givensQAux h m m (Fin.last m) k
  rw [Krylov.givensQAux_succ, Matrix.mul_apply, Fin.sum_univ_castSucc]
  have hne : (Fin.last (m + 1) : Fin (m + 2)) ≠ k.castSucc := by
    have := k.isLt
    simp only [Ne, Fin.ext_iff, Fin.val_last, Fin.val_castSucc]
    omega
  have hlast : Krylov.givensMatrix h m (m + 1) (Fin.last (m + 1)) (Fin.last (m + 1)) *
      Krylov.givensQAux h m (m + 1) (Fin.last (m + 1)) k.castSucc = 0 := by
    rw [Krylov.givensQAux_apply_of_row_lt h (m + 1) k.castSucc m (Fin.last (m + 1))
      (by rw [Fin.val_last]; omega), ite_eq_right hne, mul_zero]
  rw [hlast, add_zero]
  have hterm : ∀ p : Fin (m + 1),
      Krylov.givensMatrix h m (m + 1) (Fin.last (m + 1)) p.castSucc *
        Krylov.givensQAux h m (m + 1) p.castSucc k.castSucc
      = (if (p : ℕ) = m then -Krylov.givensS h m else 0) *
        Krylov.givensQAux h m m p k := fun p => by
    have hp : (p : ℕ) ≠ m + 1 := by
      have := p.isLt
      omega
    rw [Krylov.givensMatrix_last_row, Krylov.givensQAux_castSucc h m m le_rfl p k, Fin.val_castSucc,
      ite_eq_right hp]
  rw [Finset.sum_congr rfl fun p _ => hterm p, Finset.sum_eq_single (Fin.last m)]
  · rw [Fin.val_last, ite_eq_left rfl]
  · intro p _ hp
    have hpm : (p : ℕ) ≠ m := fun hc => hp (Fin.ext (by rw [hc, Fin.val_last]))
    rw [ite_eq_right hpm, zero_mul]
  · intro hc
    exact absurd (Finset.mem_univ _) hc

private theorem givensQ_succ_last_last (h : ℕ → ℕ → 𝕜) (m : ℕ) :
    Qrot h (m + 1) (Fin.last (m + 1)) (Fin.last (m + 1)) = c h m := by
  change Krylov.givensQAux h (m + 1) (m + 1) (Fin.last (m + 1)) (Fin.last (m + 1))
      = Krylov.givensC h m
  rw [Krylov.givensQAux_succ, Matrix.mul_apply, Fin.sum_univ_castSucc]
  have hz : ∀ p : Fin (m + 1),
      Krylov.givensMatrix h m (m + 1) (Fin.last (m + 1)) p.castSucc *
        Krylov.givensQAux h m (m + 1) p.castSucc (Fin.last (m + 1)) = 0 := fun p => by
    have hne : (p.castSucc : Fin (m + 2)) ≠ (Fin.last (m + 1) : Fin (m + 2)) := by
      have := p.isLt
      simp only [Ne, Fin.ext_iff, Fin.val_last, Fin.val_castSucc]
      omega
    rw [Krylov.givensQAux_apply_of_lt h m (m + 1) p.castSucc (Fin.last (m + 1))
      (by rw [Fin.val_last]; omega), ite_eq_right hne, mul_zero]
  rw [Finset.sum_congr rfl fun p _ => hz p, Finset.sum_const_zero, zero_add,
    Krylov.givensQAux_apply_of_row_lt h (m + 1) (Fin.last (m + 1)) m (Fin.last (m + 1))
      (by rw [Fin.val_last]; omega), ite_eq_left rfl, mul_one, Krylov.givensMatrix_last_row]
  simp

/-- **Equation (6.53)** of [saad2003iterative]. For any vectors $v_1, v_2, \dots \in \mathbb{K}^n$
and any coefficient function $h$,
$$z_{m+2} = -\bar s_{m+1} z_{m+1} + \bar c_{m+1} v_{m+2}.$$

Over $\mathbb{R}$ this is the book's $z_{m+1} = -s_m z_m + c_m v_{m+1}$, with the index shifted
by one. No hypothesis on the basis is needed.

**Generalization.** Lean uses the adjoint and the conjugates of the real update coefficients, so the
last-column formulas also hold for complex coefficients and arbitrary vector sequences.
-/
theorem equation_6_53 (u : ℕ → 𝔼) (h : ℕ → ℕ → 𝕜) (m : ℕ) :
    z u h (m + 1) = starRingEnd 𝕜 (-(s h m)) • z u h m
      + starRingEnd 𝕜 (c h m) • u (m + 1) := by
  rw [z_eq_sum, z_eq_sum, Fin.sum_univ_castSucc, Finset.smul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun k _ => by
      rw [givensQ_succ_last_castSucc, map_mul, smul_smul, Fin.val_castSucc]
  · rw [givensQ_succ_last_last, Fin.val_last]

/-- **Equation (6.54)** of [saad2003iterative]. For any vectors $v_1, v_2, \dots \in \mathbb{K}^n$
and any coefficient function $h$,
$$\zeta_{m+2} \le |s_{m+1}| \, \zeta_{m+1} + |c_{m+1}| \, \|v_{m+2}\|_2.$$

For unit vectors $v_i$ this is the book's $\zeta_{m+1} \le |s_m| \zeta_m + |c_m|$, with the
index shifted by one.

**Generalization.** Lean retains the factor giving the norm of the next basis vector in the triangle
inequality. The source assumes a unit next vector and drops that factor.
-/
theorem equation_6_54 (u : ℕ → 𝔼) (h : ℕ → ℕ → 𝕜) (m : ℕ) :
    ζ u h (m + 1) ≤ ‖s h m‖ * ζ u h m + ‖c h m‖ * ‖u (m + 1)‖ := by
  rw [ζ, ζ, equation_6_53]
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  · rw [norm_smul, RCLike.norm_conj, norm_neg]
  · rw [norm_smul, RCLike.norm_conj]

/-- **Equation (6.55)** of [saad2003iterative]. Let $A$, $b$, $x_0$, $\beta$, the vectors $v_i$ and
the coefficient function $h$ be as in `SaadSparse.Chapter06.equation_6_50`, and let $R_m$ and
$R_{m+1}$ be nonsingular. Then the residuals $r_m = b - Ax_m$ of two successive QGMRES
approximations satisfy
$$r_{m+1} = |s_{m+1}|^2 r_m + \bar c_{m+1} \gamma_{m+2} v_{m+2}.$$

Over $\mathbb{R}$ this is the book's $r_m = s_m^2 r_{m-1} + c_m \gamma_{m+1} v_{m+1}$, with the
index shifted by one.

**Generalization.** These identities use an abstract Hessenberg relation over real or complex
scalars. The relevant reduced matrices must be nonsingular. In the complex residual combination,
squared moduli replace the real coefficient squares.
-/
theorem equation_6_55 {A : Matrix (Fin n) (Fin n) 𝕜} {b x₀ : 𝔼} {u : ℕ → 𝔼} {h : ℕ → ℕ → 𝕜} {β : 𝕜}
    (hu : Krylov.HessenbergRelation (op A) u h) (hr : b - op A x₀ = β • u 0) {m : ℕ}
    (hR : IsUnit (R h m)) (hR' : IsUnit (R h (m + 1))) :
    b - op A (qgmres x₀ u h β (m + 1))
      = ((‖s h m‖ : 𝕜) ^ 2) • (b - op A (qgmres x₀ u h β m))
        + (starRingEnd 𝕜 (c h m) * γ h β (m + 1)) • u (m + 1) := by
  have h1 : γ h β (m + 1) * starRingEnd 𝕜 (-(s h m)) = (‖s h m‖ : 𝕜) ^ 2 * γ h β m := by
    rw [gamma_succ, map_neg, ← RCLike.mul_conj (s h m)]
    ring
  have h2 : γ h β (m + 1) * starRingEnd 𝕜 (c h m)
      = starRingEnd 𝕜 (c h m) * γ h β (m + 1) := mul_comm _ _
  rw [equation_6_50 hu hr hR', equation_6_50 hu hr hR, equation_6_53, smul_add,
    smul_smul, smul_smul, smul_smul,
    h1, h2]

/-!
### Equations (6.56)–(6.58): DQGMRES and IOM

These results compare the quasi-minimal-residual approximation with the Galerkin approximation on
the same, possibly non-orthogonal, basis. That is IOM or DIOM when the basis comes from the
incomplete orthogonalization of Algorithm 6.6 (the book writes $x^I_m$ and $r^I_m$), and FOM when it
is the Arnoldi basis. This approximation is `SaadSparse.Chapter06.iomOfBasis`.
-/

/-- The coordinates $y^I_m = H_m^{-1} (\beta e_1)$ of the Galerkin approximation in the basis, where
$H_m$ is the $m \times m$ Hessenberg matrix of $h$. If $H_m$ is singular, then $y^I_m = 0$.

**Generalization.** The IOM expressions use an arbitrary Hessenberg relation rather than the
incomplete Arnoldi basis. Their definitions totalize matrix inversion. The residual formula requires
nonsingularity of the reduced system.
-/
noncomputable def iomOfBasisY (h : ℕ → ℕ → 𝕜) (β : 𝕜) (m : ℕ) : Fin m → 𝕜 :=
  (Krylov.hessenbergSqOf h m)⁻¹ *ᵥ Krylov.firstVec β m

/-- **Algorithm 6.7** of [saad2003iterative] (IOM), for an arbitrary basis. For vectors
$v_1, v_2, \dots \in \mathbb{K}^n$, a coefficient function $h$ and $\beta \in \mathbb{K}$, the
Galerkin approximation
$$x^I_m = x_0 + V_m y^I_m, \qquad y^I_m = H_m^{-1} (\beta e_1),$$
where $H_m$ is the $m \times m$ Hessenberg matrix of $h$.

On the incomplete orthogonalization basis this is Algorithm 6.7
(`SaadSparse.Chapter06.iomOfBasis_eq_iomFixed`), and on the Arnoldi basis it is Algorithm 6.4,
FOM (`SaadSparse.Chapter06.iomOfBasis_eq_fomFixed`). If $H_m$ is singular, then $x^I_m = x_0$.

**Generalization.** The IOM expressions use an arbitrary Hessenberg relation rather than the
incomplete Arnoldi basis. Their definitions totalize matrix inversion. The residual formula requires
nonsingularity of the reduced system.
-/
noncomputable def iomOfBasis (x₀ : 𝔼) (u : ℕ → 𝔼) (h : ℕ → ℕ → 𝕜) (β : 𝕜) (m : ℕ) : 𝔼 :=
  x₀ + Matrix.toEuclideanLin (colMatrix u m) (WithLp.toLp 2 (iomOfBasisY h β m))

/-- On the incomplete orthogonalization basis `SaadSparse.Chapter06.iop A v₁ k`, with the
coefficients `SaadSparse.Chapter06.iopCoeff A v₁ k` and $\beta = \|r_0\|_2$, the Galerkin
approximation is Algorithm 6.7 (IOM) with parameter $k$, `SaadSparse.Chapter06.iomFixed`. So
(6.56)–(6.58) below are the book's statements about $x^I_m$. -/
theorem iomOfBasis_eq_iomFixed (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (k m : ℕ) :
    iomOfBasis x₀ (iop A (v₁ A b x₀) k) (iopCoeff A (v₁ A b x₀) k) (β A b x₀ : 𝕜) m
      = iomFixed A b x₀ k m := by
  rw [iomOfBasis, iomFixed, iomOfBasisY, iomY, VI, HI, smul_e₁_eq_firstVec]

/-- On the Arnoldi basis of $v_1$, with the Arnoldi coefficients and $\beta = \|r_0\|_2$, the
Galerkin approximation is Algorithm 6.4 (FOM), `SaadSparse.Chapter06.fomFixed`. -/
theorem iomOfBasis_eq_fomFixed (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (m : ℕ) :
    iomOfBasis x₀ (arnoldiCGS A (v₁ A b x₀)) (arnoldiCoeff A (v₁ A b x₀)) (β A b x₀ : 𝕜) m
      = fomFixed A b x₀ m := by
  rw [iomOfBasis, fomFixed, iomOfBasisY, fomY, V, H_eq_hessenbergSqOf, smul_e₁_eq_firstVec]

/-- If $H_m$ is nonsingular, then $H_m y^I_m = \beta e_1$. This makes $x^I_m$ the Galerkin
approximation. -/
theorem hessenbergSqOf_mulVec_iomOfBasisY {h : ℕ → ℕ → 𝕜} {β : 𝕜} {m : ℕ}
    (hH : IsUnit (Krylov.hessenbergSqOf h m)) :
    Krylov.hessenbergSqOf h m *ᵥ iomOfBasisY h β m = Krylov.firstVec β m := by
  rw [iomOfBasisY, Matrix.mulVec_nonsing_inv_mulVec hH]

/-- **Proposition 6.7** of [saad2003iterative], for an arbitrary basis. Let $A$, $b$, $x_0$,
$\beta$, the vectors $v_i$ and the coefficient function $h$ be as in
`SaadSparse.Chapter06.equation_6_50`, and let $H_{m+1}$ be nonsingular. Then
$$b - Ax^I_{m+1} = -h_{m+2,m+1} \, (e_{m+1}^T y^I_{m+1}) \, v_{m+2}.$$

Like (6.50), this uses only the Hessenberg relation, so the loss of orthogonality does not
matter. This is the remark of Section 6.4.2 that the result of Proposition 6.7 stays valid.

**Generalization.** The IOM expressions use an arbitrary Hessenberg relation rather than the
incomplete Arnoldi basis. Their definitions totalize matrix inversion. The residual formula requires
nonsingularity of the reduced system.
-/
theorem residual_iomOfBasis {A : Matrix (Fin n) (Fin n) 𝕜} {b x₀ : 𝔼} {u : ℕ → 𝔼} {h : ℕ → ℕ → 𝕜}
    {β : 𝕜} (hu : Krylov.HessenbergRelation (op A) u h) (hr : b - op A x₀ = β • u 0) {m : ℕ}
    (hH : IsUnit (Krylov.hessenbergSqOf h (m + 1))) :
    b - op A (iomOfBasis x₀ u h β (m + 1))
      = -(h (m + 1) m * iomOfBasisY h β (m + 1) (Fin.last m)) • u (m + 1) := by
  rw [iomOfBasis, toEuclideanLin_colMatrix_apply]
  exact hu.residual_eq_of_mulVec_eq hr (Nat.succ_pos m) _
    (hessenbergSqOf_mulVec_iomOfBasisY hH)

/-- **Equation (6.56)** of [saad2003iterative]. Let $A$, $b$, $x_0$, $\beta$, the vectors $v_i$ and
the coefficient function $h$ be as in `SaadSparse.Chapter06.equation_6_50`, and let $H_{m+1}$ be
nonsingular. Then
$$\gamma_{m+2} v_{m+2} = c_{m+1} r^I_{m+1}, \qquad r^I_{m+1} = b - Ax^I_{m+1},$$
which in the book's indexing is $\gamma_{m+1} v_{m+1} = c_m r^I_m$.

In the book's indexing, both sides are the scalar $-r^{(m-1)}_{mm} h_{m+1,m} (e_m^T y^I_m) /
\rho_m$ times $v_{m+1}$, because $c_m = r^{(m-1)}_{mm} / \rho_m$ and $s_m = h_{m+1,m} / \rho_m$
have the same denominator. The book reads the relation off
$h_{m+1,m} / h^{(m)}_{mm} = \tan \theta_m$, which divides by $h^{(m)}_{mm}$. The identity here
needs no hypothesis $h^{(m)}_{mm} \neq 0$, and at a breakdown both sides are $0$.

**Generalization.** These identities use an abstract Hessenberg relation over real or complex
scalars. The relevant reduced matrices must be nonsingular. In the complex residual combination,
squared moduli replace the real coefficient squares.
-/
theorem equation_6_56 {A : Matrix (Fin n) (Fin n) 𝕜} {b x₀ : 𝔼} {u : ℕ → 𝔼} {h : ℕ → ℕ → 𝕜}
    {β : 𝕜} (hu : Krylov.HessenbergRelation (op A) u h) (hr : b - op A x₀ = β • u 0) {m : ℕ}
    (hH : IsUnit (Krylov.hessenbergSqOf h (m + 1))) :
    γ h β (m + 1) • u (m + 1) = c h m • (b - op A (iomOfBasis x₀ u h β (m + 1))) := by
  have hg : Krylov.rotated h m m m * iomOfBasisY h β (m + 1) (Fin.last m) = γ h β m :=
    Krylov.rotated_self_mul_eq_gamma h hu.isUpperHessenberg β (hessenbergSqOf_mulVec_iomOfBasisY hH)
  have hsub : Krylov.rotated h m (m + 1) m = h (m + 1) m :=
    Krylov.rotated_eq_of_le h m (m + 1) m le_rfl
  have key : γ h β (m + 1)
      = c h m * -(h (m + 1) m * iomOfBasisY h β (m + 1) (Fin.last m)) := by
    rw [gamma_succ, ← hg, show c h m = Krylov.givensC h m from rfl,
      show s h m = Krylov.givensS h m from rfl, Krylov.givensC, Krylov.givensS, hsub]
    ring
  rw [residual_iomOfBasis hu hr hH, smul_smul, ← key]

/-- **Equation (6.57)** of [saad2003iterative]. Let $A$, $b$, $x_0$, $\beta$, the vectors $v_i$ and
the coefficient function $h$ be as in `SaadSparse.Chapter06.equation_6_50`, let
$\|v_{m+2}\|_2 = 1$, and let $H_{m+1}$ be nonsingular. Then
$$|\gamma_{m+2}| = |c_{m+1}| \, \|b - Ax^I_{m+1}\|_2.$$
In the book's indexing this is $\rho^Q_m = |c_m| \rho_m$: the quasi-residual norm of QGMRES
against the residual norm of IOM.

This is (6.56) in norms, so it needs only that $v_{m+2}$ is a unit vector, which the incomplete
orthogonalization gives.

**Reading.** The identity explicitly requires the next basis vector to be a unit vector and the IOM
reduced system to be nonsingular. Lean also allows complex scalars.
-/
theorem equation_6_57 {A : Matrix (Fin n) (Fin n) 𝕜} {b x₀ : 𝔼} {u : ℕ → 𝔼} {h : ℕ → ℕ → 𝕜}
    {β : 𝕜} (hu : Krylov.HessenbergRelation (op A) u h) (hr : b - op A x₀ = β • u 0) {m : ℕ}
    (hnorm : ‖u (m + 1)‖ = 1) (hH : IsUnit (Krylov.hessenbergSqOf h (m + 1))) :
    quasiResidualNorm h β (m + 1)
      = ‖c h m‖ * ‖b - op A (iomOfBasis x₀ u h β (m + 1))‖ := by
  have h56 := congrArg norm (equation_6_56 hu hr hH)
  rwa [norm_smul, norm_smul, hnorm, mul_one] at h56

/-- **Equation (6.58)** of [saad2003iterative]. Let $A$, $b$, $x_0$, $\beta$, the vectors $v_i$ and
the coefficient function $h$ be as in `SaadSparse.Chapter06.equation_6_50`, and let $R_m$,
$R_{m+1}$ and $H_{m+1}$ be nonsingular. Then the residual $r^Q_m = b - Ax_m$ of the QGMRES
approximation and the residual $r^I_{m+1} = b - Ax^I_{m+1}$ of the Galerkin approximation
satisfy
$$r^Q_{m+1} = |s_{m+1}|^2 r^Q_m + |c_{m+1}|^2 r^I_{m+1}.$$
In the book's indexing this is $r^Q_m = s_m^2 r^Q_{m-1} + c_m^2 r^I_m$, the residual recurrence
of QGMRES and DQGMRES.

This is (6.55) with (6.56) substituted for $\gamma_{m+2} v_{m+2}$.

**Generalization.** These identities use an abstract Hessenberg relation over real or complex
scalars. The relevant reduced matrices must be nonsingular. In the complex residual combination,
squared moduli replace the real coefficient squares.
-/
theorem equation_6_58 {A : Matrix (Fin n) (Fin n) 𝕜} {b x₀ : 𝔼} {u : ℕ → 𝔼} {h : ℕ → ℕ → 𝕜}
    {β : 𝕜} (hu : Krylov.HessenbergRelation (op A) u h) (hr : b - op A x₀ = β • u 0) {m : ℕ}
    (hR : IsUnit (R h m)) (hR' : IsUnit (R h (m + 1)))
    (hH : IsUnit (Krylov.hessenbergSqOf h (m + 1))) :
    b - op A (qgmres x₀ u h β (m + 1))
      = ((‖s h m‖ : 𝕜) ^ 2) • (b - op A (qgmres x₀ u h β m))
        + ((‖c h m‖ : 𝕜) ^ 2) • (b - op A (iomOfBasis x₀ u h β (m + 1))) := by
  rw [equation_6_55 hu hr hR hR', ← smul_smul, equation_6_56 hu hr hH, smul_smul,
    ← RCLike.mul_conj (c h m)]
  ring_nf

/-- **Problem P-6.25** of [saad2003iterative]. Let $v_1, v_2, \dots \in \mathbb{K}^n$ satisfy
$\|v_i\|_2 \le 1$ for all $i$, let $h$ be a coefficient function with $\rho_i \neq 0$ for all
$i \ge 1$, and let $k \ge 0$ with $\zeta_{k+1} \le 1$. Then for every $j \ge 0$,
$$\zeta_{k+j+1} \le \sqrt{j + 1}.$$

By (6.54), $\zeta$ grows by at most one square root per step. The hypothesis $\zeta_{k+1} \le 1$
is what the truncation gives: the first $k + 1$ vectors of the incomplete orthogonalization are
orthonormal, so $z_{k+1}$, their combination with the coefficients of a unit vector, has norm
$1$. This bound is sharper than (6.51).

**Reading.** The source derives the bound from local orthogonality and the unit Arnoldi vectors, and
uses the full-prefix case when the window covers all steps. Lean proves the bound for an abstract
sequence using the base bound, norms at most one and nonzero rotation radii at every index. The
order in the bound is at or above the base index.
-/
theorem problem_6_25 (u : ℕ → 𝔼) (h : ℕ → ℕ → 𝕜) (hu : ∀ i, ‖u i‖ ≤ 1)
    (hρ : ∀ i, Krylov.givensRho h i ≠ 0) {k : ℕ} (hbase : ζ u h k ≤ 1) (j : ℕ) :
    ζ u h (k + j) ≤ Real.sqrt ((j : ℝ) + 1) := by
  induction j with
  | zero => simpa using hbase
  | succ j ih =>
    set a := ‖s h (k + j)‖ with ha
    set bb := ‖c h (k + j)‖ with hb
    set zz := ζ u h (k + j) with hzz
    set w := ‖u (k + j + 1)‖ with hw
    have hz0 : 0 ≤ zz := norm_nonneg _
    have ha0 : 0 ≤ a := norm_nonneg _
    have hb0 : 0 ≤ bb := norm_nonneg _
    have hw0 : 0 ≤ w := norm_nonneg _
    have hw1 : w ≤ 1 := hu _
    have hw2 : w ^ 2 ≤ 1 := by nlinarith
    have hab : a ^ 2 + bb ^ 2 = 1 := by
      have := norm_c_sq_add_norm_s_sq h (hρ (k + j))
      linarith
    have hsq : zz ^ 2 ≤ (j : ℝ) + 1 := by
      have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (j : ℝ) + 1)
      nlinarith [ih, hz0]
    have hC : (a * zz + bb * w) ^ 2 ≤ (a ^ 2 + bb ^ 2) * (zz ^ 2 + w ^ 2) := by
      nlinarith [sq_nonneg (a * w - bb * zz)]
    rw [hab, one_mul] at hC
    have hnn : 0 ≤ a * zz + bb * w := by positivity
    have hkey : (a * zz + bb * w) ^ 2 ≤ ((j : ℝ) + 1) + 1 := by linarith
    calc ζ u h (k + (j + 1)) ≤ a * zz + bb * w := equation_6_54 u h (k + j)
      _ = Real.sqrt ((a * zz + bb * w) ^ 2) := (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt (((j : ℝ) + 1) + 1) := Real.sqrt_le_sqrt hkey
      _ = Real.sqrt (((j + 1 : ℕ) : ℝ) + 1) := by push_cast; ring_nf

/-- **Problem P-6.25** of [saad2003iterative], in the book's indexing. Let
$v_1, v_2, \dots \in \mathbb{K}^n$ satisfy $\|v_i\|_2 \le 1$ for all $i$, let $h$ be a
coefficient function with $\rho_i \neq 0$ for all $i \ge 1$, and let $k \le m$ with
$\zeta_{k+1} \le 1$. Then
$$\zeta_{m+1} \le \sqrt{m - k + 1}.$$

**Reading.** The source derives the bound from local orthogonality and the unit Arnoldi vectors, and
uses the full-prefix case when the window covers all steps. Lean proves the bound for an abstract
sequence using the base bound, norms at most one and nonzero rotation radii at every index. The
order in the bound is at or above the base index.
-/
theorem problem_6_25_le (u : ℕ → 𝔼) (h : ℕ → ℕ → 𝕜) (hu : ∀ i, ‖u i‖ ≤ 1)
    (hρ : ∀ i, Krylov.givensRho h i ≠ 0) {k m : ℕ} (hbase : ζ u h k ≤ 1) (hkm : k ≤ m) :
    ζ u h m ≤ Real.sqrt (((m - k : ℕ) : ℝ) + 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkm
  simpa using problem_6_25 u h hu hρ hbase j

/-- **Equation (6.51)** of [saad2003iterative]. Let $A$, $b$, $x_0$, $\beta$, the vectors $v_i$ and
the coefficient function $h$ be as in `SaadSparse.Chapter06.equation_6_50`. Assume that
$\|v_i\|_2 \le 1$ and $\rho_i \neq 0$ for all $i \ge 1$, that $k \le m$ with
$\zeta_{k+1} \le 1$, and that $R_m$ is nonsingular. Then the QGMRES approximation $x_m$
satisfies
$$\|b - Ax_m\|_2 \le \sqrt{m - k + 1} \, |\gamma_{m+1}|.$$
So the quasi-residual norm $|\gamma_{m+1}|$ underestimates the residual norm by at most the
factor $\sqrt{m - k + 1}$.

The proof derives the bound from the sharper P-6.25 and (6.50), not from the book's direct
splitting of $Q_m^T e_{m+1}$.

**Reading.** The source derives the bound from local orthogonality and the unit Arnoldi vectors, and
uses the full-prefix case when the window covers all steps. Lean proves the bound for an abstract
sequence using the base bound, norms at most one and nonzero rotation radii at every index. The
order in the bound is at or above the base index.
-/
theorem equation_6_51 {A : Matrix (Fin n) (Fin n) 𝕜} {b x₀ : 𝔼} {u : ℕ → 𝔼} {h : ℕ → ℕ → 𝕜} {β : 𝕜}
    (hA : Krylov.HessenbergRelation (op A) u h) (hr : b - op A x₀ = β • u 0)
    (hu : ∀ i, ‖u i‖ ≤ 1) (hρ : ∀ i, Krylov.givensRho h i ≠ 0) {k m : ℕ}
    (hbase : ζ u h k ≤ 1) (hkm : k ≤ m) (hR : IsUnit (R h m)) :
    ‖b - op A (qgmres x₀ u h β m)‖
      ≤ Real.sqrt (((m - k : ℕ) : ℝ) + 1) * quasiResidualNorm h β m := by
  have hzz : ζ u h m ≤ Real.sqrt (((m - k : ℕ) : ℝ) + 1) := problem_6_25_le u h hu hρ hbase hkm
  rw [equation_6_50 hA hr hR, norm_smul, quasiResidualNorm]
  calc ‖γ h β m‖ * ‖z u h m‖
      ≤ ‖γ h β m‖ * Real.sqrt (((m - k : ℕ) : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hzz (norm_nonneg _)
    _ = Real.sqrt (((m - k : ℕ) : ℝ) + 1) * ‖γ h β m‖ := mul_comm _ _

/-! ### Theorem 6.11: the bound of Freund and Nachtigal -/

/-- Supporting result for Theorem 6.11 of [saad2003iterative]. Let $h$ be upper Hessenberg and let
$R_m$ be nonsingular. Then the QGMRES approximation of Algorithm 6.12 is a
quasi-minimal-residual iterate (`Krylov.IsQuasiMinResidualIterate`):
$x_m = x_0 + \sum_{j=1}^m (y_m)_j v_j$, where $y_m$ minimizes the quasi-residual
$\|\beta e_1 - \bar H_m y\|_2$.

This brings the quasi-minimal-residual theory of `Numlib.Krylov.QuasiMinRes`, which QMR, TFQMR
and FGMRES also use, to Algorithms 6.12 and 6.13.

**Reading.** The definitions allow an arbitrary Hessenberg relation and real or complex
coefficients, and evaluate a fixed prefix. The source uses incomplete orthogonalization and a
least-squares minimizer. The Lean inverse is zero at singular R; the minimizer specifications
require nonsingular R.
-/
theorem qgmres_isQuasiMinResidualIterate (x₀ : 𝔼) (u : ℕ → 𝔼) (h : ℕ → ℕ → 𝕜) (β : 𝕜)
    (hh : ∀ i j : ℕ, j + 1 < i → h i j = 0) {m : ℕ} (hR : IsUnit (R h m)) :
    Krylov.IsQuasiMinResidualIterate u h β x₀ m (qgmres x₀ u h β m) :=
  ⟨qgmresY h β m, (isMinOn_lsq h β hh hR).1, by rw [qgmres, toEuclideanLin_colMatrix_apply]⟩

/-- **Theorem 6.11** of [saad2003iterative] (Freund and Nachtigal). Let
$A \in \mathbb{K}^{n \times n}$, $b, x_0 \in \mathbb{K}^n$ and $\beta \in \mathbb{K}$. Let
$v_1, v_2, \dots \in \mathbb{K}^n$ and the upper Hessenberg coefficient function $h$ satisfy
$A v_j = \sum_{i=1}^{j+1} h_{ij} v_i$, with $b - Ax_0 = \beta v_1$, and let $R_m$ be
nonsingular. Let $m \le \operatorname{grade}(v_1)$, and let $R_m$ of the Arnoldi coefficients of
$v_1$ be nonsingular. Assume that $v_1, \dots, v_m$ span $\mathcal{K}_m(A, r_0)$, and that there
are constants $c > 0$ and $C$ with
$$c \|w\|_2 \le \|V_{m+1} w\|_2 \le C \|w\|_2 \qquad \text{for all } w \in \mathbb{K}^{m+1}.$$
Then the QGMRES approximation $x_m$ and the GMRES approximation $x^G_m$ of Algorithm 6.9 satisfy
$$\|b - Ax_m\|_2 \le \frac{C}{c} \, \|b - Ax^G_m\|_2.$$

With the best constants, $C / c$ is the condition number $\kappa_2(V_{m+1})$, the ratio of the
extreme singular values, and the bound is the book's (6.59),
$\|r^Q_m\|_2 \le \kappa_2(V_{m+1}) \|r^G_m\|_2$. The book states the theorem for DQGMRES; the
Lean statement is about the QGMRES approximation, which DQGMRES computes in exact arithmetic
(`SaadSparse.Chapter06.dqgmres_eq_qgmres` proves this when no truncation occurs). The book
factors $V_{m+1} = WS$ with $W$ orthonormal, which needs $V_{m+1}$ to have full rank. The
backbone result `Krylov.IsQuasiMinResidualIterate.norm_residual_le_mul` needs only the two-sided
bound, and gives the same estimate against every point of
$x_0 + \operatorname{span}\{v_1, \dots, v_m\}$; the GMRES approximation is the point that makes
it sharpest.

**Reading.** Lean takes two-sided basis bounds with positive lower constant and gives their ratio in
place of the source's spectral condition number. It works directly with QGMRES, requires both
reduced factors nonsingular, and makes the common search span explicit.
-/
theorem theorem_6_11 {A : Matrix (Fin n) (Fin n) 𝕜} (b x₀ : 𝔼) {u : ℕ → 𝔼} {h : ℕ → ℕ → 𝕜}
    {β : 𝕜} (hu : Krylov.HessenbergRelation (op A) u h) (hr : b - op A x₀ = β • u 0) {m : ℕ}
    (hR : IsUnit (R h m)) (hm : m ≤ grade A (v₁ A b x₀))
    (hRA : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m))
    (hspan : Submodule.span 𝕜 (Set.range fun i : Fin m => u (i : ℕ))
      = krylov A (r₀ A b x₀) m)
    {c C : ℝ} (hc0 : 0 < c)
    (hc : ∀ w : Fin (m + 1) → 𝕜,
      c * ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (Fin (m + 1)))‖ ≤ ‖∑ i, w i • u (i : ℕ)‖)
    (hC : ∀ w : Fin (m + 1) → 𝕜,
      ‖∑ i, w i • u (i : ℕ)‖ ≤ C * ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (Fin (m + 1)))‖) :
    ‖b - op A (qgmres x₀ u h β m)‖ ≤ C / c * ‖b - op A (gmresFixed A b x₀ m)‖ := by
  have hmem : gmresFixed A b x₀ m - x₀ ∈
      Submodule.span 𝕜 (Set.range fun i : Fin m => u (i : ℕ)) := by
    rw [hspan, krylov_eq]
    exact (gmresFixed_isMinResidualIterate A b x₀ hm hRA).mem
  obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).1 hmem
  have hxG : gmresFixed A b x₀ m = x₀ + ∑ j, w j • u (j : ℕ) := by
    rw [hw]
    abel
  rw [hxG]
  exact Krylov.IsQuasiMinResidualIterate.norm_residual_le_mul hu hr hc0 hc hC
    (qgmres_isQuasiMinResidualIterate x₀ u h β hu.eq_zero_of_lt hR) w

/-! ### Algorithm 6.13 (DQGMRES) -/

/-- Algorithm 6.13 of [saad2003iterative] (DQGMRES), line 8: the direction vectors of (6.48). With
`0`-based indices and truncation parameter $k$,
$$p_m = \frac{1}{r_{mm}} \Big( v_m - \sum_{i = m-k}^{m-1} r_{im} \, p_i \Big),$$
where the Lean terms `u m` and `Krylov.rotated h (m + 1) i m` are $v_m$ and $r_{im}$, an entry
of column $m$ of the triangular factor after the rotations with indices $0, \dots, m$. The
rotation with index $m$ changes only rows $m$ and $m + 1$, so for $i < m$ the entry $r_{im}$ is
the entry after the earlier rotations, and $r_{mm}$ is the updated diagonal entry, the norm
`Krylov.givensRho h m`. Division by $0$ gives $0$, the book's convention at a breakdown.

**Reading.** The recurrence uses the full rotated Hessenberg coefficients restricted to the
specified window, with an arbitrary basis and real or complex coefficients. It is evaluated for a
fixed number of steps and totalizes division by a zero diagonal. The source gives an incremental
band rotation and stops using a quasi-residual test.
-/
noncomputable def dqgmresP (u : ℕ → 𝔼) (h : ℕ → ℕ → 𝕜) (k : ℕ) : ℕ → 𝔼
  | m =>
    let p : Fin m → 𝔼 := fun i => dqgmresP u h k (i : ℕ)
    ((Krylov.rotated h (m + 1) m m)⁻¹) •
      (u m - ∑ i : Fin m,
        (if m ≤ (i : ℕ) + k then Krylov.rotated h (m + 1) (i : ℕ) m else 0) • p i)
  termination_by m => m
  decreasing_by exact i.isLt

/-- The recurrence of `SaadSparse.Chapter06.dqgmresP`, with the sum over $i < m$ written over
`Finset.range m`.

**Reading.** The recurrence uses the full rotated Hessenberg coefficients restricted to the
specified window, with an arbitrary basis and real or complex coefficients. It is evaluated for a
fixed number of steps and totalizes division by a zero diagonal. The source gives an incremental
band rotation and stops using a quasi-residual test.
-/
theorem dqgmresP_eq (u : ℕ → 𝔼) (h : ℕ → ℕ → 𝕜) (k m : ℕ) :
    dqgmresP u h k m = ((Krylov.rotated h (m + 1) m m)⁻¹) •
      (u m - ∑ i ∈ Finset.range m,
        (if m ≤ i + k then Krylov.rotated h (m + 1) i m else 0) • dqgmresP u h k i) := by
  rw [dqgmresP]
  simp only []
  rw [Fin.sum_univ_eq_sum_range
    (fun i => (if m ≤ i + k then Krylov.rotated h (m + 1) i m else 0) • dqgmresP u h k i) m]

/-- **Algorithm 6.13** of [saad2003iterative] (DQGMRES), line 9. For vectors
$v_1, v_2, \dots \in \mathbb{K}^n$, a coefficient function $h$, $\beta \in \mathbb{K}$ and a
truncation parameter $k$, the approximations are $x_0$ and
$$x_m = x_{m-1} + \bar c_m \gamma_m \, p_m, \qquad m \ge 1,$$
where $p_m$ are the direction vectors of `SaadSparse.Chapter06.dqgmresP` and $\bar c_m \gamma_m$
is the entry $g_m$ of the rotated right-hand side. The book writes this product as the updated
$\gamma_m$.

The Lean terms `dqgmresP u h k m` and `Krylov.gvec h β m` are the book's $p_{m+1}$ and
$\bar c_{m+1} \gamma_{m+1}$.

**Reading.** The recurrence uses the full rotated Hessenberg coefficients restricted to the
specified window, with an arbitrary basis and real or complex coefficients. It is evaluated for a
fixed number of steps and totalizes division by a zero diagonal. The source gives an incremental
band rotation and stops using a quasi-residual test.
-/
noncomputable def dqgmres (x₀ : 𝔼) (u : ℕ → 𝔼) (h : ℕ → ℕ → 𝕜) (β : 𝕜) (k : ℕ) : ℕ → 𝔼
  | 0 => x₀
  | m + 1 => dqgmres x₀ u h β k m + Krylov.gvec h β m • dqgmresP u h k m

/-- The DQGMRES approximation is $x_m = x_0 + \sum_{j=1}^m \bar c_j \gamma_j \, p_j$, in the book's
indexing.

**Reading.** The recurrence uses the full rotated Hessenberg coefficients restricted to the
specified window, with an arbitrary basis and real or complex coefficients. It is evaluated for a
fixed number of steps and totalizes division by a zero diagonal. The source gives an incremental
band rotation and stops using a quasi-residual test.
-/
theorem dqgmres_eq_sum (x₀ : 𝔼) (u : ℕ → 𝔼) (h : ℕ → ℕ → 𝕜) (β : 𝕜) (k m : ℕ) :
    dqgmres x₀ u h β k m
      = x₀ + ∑ j : Fin m, Krylov.gvec h β (j : ℕ) • dqgmresP u h k (j : ℕ) := by
  induction m with
  | zero => simp [dqgmres]
  | succ m ih =>
    rw [dqgmres, ih, Fin.sum_univ_castSucc, add_assoc]
    rfl

/-! ### DQGMRES computes QGMRES -/

/-- Let $h$ be upper Hessenberg. Then column $j$ of the triangular factor does not change after the
rotation with index $j$ has been applied. -/
private theorem rotated_of_col_lt {h : ℕ → ℕ → 𝕜} (hh : ∀ i j : ℕ, j + 1 < i → h i j = 0)
    {j : ℕ} : ∀ M, j + 1 ≤ M → ∀ i, Krylov.rotated h M i j = Krylov.rotated h (j + 1) i j := by
  intro M
  induction M with
  | zero => intro hM; omega
  | succ M ih =>
    intro hM i
    rcases Nat.lt_or_ge j M with hjM | hjM
    · rw [Krylov.rotated_succ_eq_of_lt h (Matrix.isUpperHessenberg_iff_nat.2 hh) M j hjM i]
      exact ih (by omega) i
    · have hMj : M = j := by omega
      subst hMj
      rfl

/-- Let $h$ be upper Hessenberg. Then the entry $(i, j)$ of $R_m$ is the entry
`Krylov.rotated h (j + 1) i j` that the DQGMRES recurrence uses. -/
private theorem R_apply_eq_rotated_succ {h : ℕ → ℕ → 𝕜} (hh : ∀ i j : ℕ, j + 1 < i → h i j = 0)
    {m : ℕ} (i j : Fin m) : R h m i j = Krylov.rotated h ((j : ℕ) + 1) i j := by
  rw [R_apply]
  exact rotated_of_col_lt hh m j.isLt (i : ℕ)

/-- Let $h$ be upper Hessenberg, let $m \le k$ (no truncation), and let the entries
`Krylov.rotated h (j + 1) j j` be nonzero for $j < m$. Then the DQGMRES directions satisfy
$P_m R_m = V_m$: $\sum_i (R_m)_{ij} \, p_i = v_j$ for each column $j$. So the recurrence without
truncation is back substitution for the triangular system.

**Reading.** The factor relation and equality with QGMRES require a window covering the whole
prefix. The source derives the same equivalence with a short window from bandedness of the rotated
triangular factor.
-/
theorem sum_R_smul_dqgmresP {u : ℕ → 𝔼} {h : ℕ → ℕ → 𝕜} {k m : ℕ}
    (hh : ∀ i j : ℕ, j + 1 < i → h i j = 0) (hk : m ≤ k)
    (hd : ∀ j < m, Krylov.rotated h (j + 1) j j ≠ 0) (j : Fin m) :
    ∑ i : Fin m, R h m i j • dqgmresP u h k (i : ℕ) = u (j : ℕ) := by
  have hjm : (j : ℕ) < m := j.isLt
  have hzero : ∀ i ∈ Finset.range m, i ∉ Finset.range ((j : ℕ) + 1) →
      Krylov.rotated h ((j : ℕ) + 1) i (j : ℕ) • dqgmresP u h k i = 0 := by
    intro i _ hi
    rw [Finset.mem_range, not_lt] at hi
    rw [Krylov.rotated_eq_zero_of_lt h (Matrix.isUpperHessenberg_iff_nat.2 hh)
        ((j : ℕ) + 1) i (j : ℕ) (Nat.lt_succ_self _)
      (by omega), zero_smul]
  have hsub : Finset.range ((j : ℕ) + 1) ⊆ Finset.range m := by
    intro i hi
    rw [Finset.mem_range] at hi ⊢
    omega
  have hpj := dqgmresP_eq u h k (j : ℕ)
  have hcond : ∀ i ∈ Finset.range (j : ℕ),
      (if (j : ℕ) ≤ i + k then Krylov.rotated h ((j : ℕ) + 1) i (j : ℕ) else 0) •
          dqgmresP u h k i
        = Krylov.rotated h ((j : ℕ) + 1) i (j : ℕ) • dqgmresP u h k i := by
    intro i _
    rw [ite_eq_left (by omega)]
  rw [Finset.sum_congr rfl fun i _ => by rw [R_apply_eq_rotated_succ hh i j],
    Fin.sum_univ_eq_sum_range
      (fun i => Krylov.rotated h ((j : ℕ) + 1) i (j : ℕ) • dqgmresP u h k i) m,
    ← Finset.sum_subset hsub hzero,
    Finset.sum_range_succ, hpj, Finset.sum_congr rfl hcond, smul_smul,
    mul_inv_cancel₀ (hd (j : ℕ) hjm), one_smul]
  abel

/-- Algorithm 6.13 computes Algorithm 6.12. Let $h$ be upper Hessenberg, let $m \le k$ (no
truncation), and let $R_m$ be nonsingular. Then the DQGMRES approximation with parameter $k$ and
the QGMRES approximation at step $m$ are equal.

**Reading.** The factor relation and equality with QGMRES require a window covering the whole
prefix. The source derives the same equivalence with a short window from bandedness of the rotated
triangular factor.
-/
theorem dqgmres_eq_qgmres {x₀ : 𝔼} {u : ℕ → 𝔼} {h : ℕ → ℕ → 𝕜} {β : 𝕜} {k m : ℕ}
    (hh : ∀ i j : ℕ, j + 1 < i → h i j = 0) (hk : m ≤ k) (hR : IsUnit (R h m)) :
    dqgmres x₀ u h β k m = qgmres x₀ u h β m := by
  have hρ := (isUnit_R_iff h hh).1 hR
  have hd : ∀ j < m, Krylov.rotated h (j + 1) j j ≠ 0 := by
    intro j hj
    rw [Krylov.rotated_succ_self]
    simpa using hρ j hj
  have key := sum_R_smul_dqgmresP (u := u) (k := k) hh hk hd
  rw [dqgmres_eq_sum, qgmres, toEuclideanLin_colMatrix_apply]
  refine congrArg _ ?_
  have hg : ∀ i : Fin m, Krylov.gvec h β (i : ℕ) = (R h m *ᵥ qgmresY h β m) i := by
    intro i
    rw [qgmresY, mulVec_R_inv_mulVec_g h β hR, g_apply]
  calc ∑ i : Fin m, Krylov.gvec h β (i : ℕ) • dqgmresP u h k (i : ℕ)
      = ∑ i : Fin m, ∑ j : Fin m,
          (R h m i j * qgmresY h β m j) • dqgmresP u h k (i : ℕ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hg i, Matrix.mulVec, dotProduct, Finset.sum_smul]
    _ = ∑ j : Fin m, qgmresY h β m j • ∑ i : Fin m, R h m i j • dqgmresP u h k (i : ℕ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, mul_comm]
    _ = ∑ j : Fin m, qgmresY h β m j • u (j : ℕ) :=
        Finset.sum_congr rfl fun j _ => by rw [key j]

/-! ### Nondegeneracy from a nonzero $\gamma$ -/

/-- If $\gamma_{l+2} \neq 0$, then $\rho_{l+1} \neq 0$: at a breakdown $s_{l+1} = 0$, and (6.47)
gives $\gamma_{l+2} = 0$. -/
theorem givensRho_ne_zero_of_gamma_ne_zero {h : ℕ → ℕ → 𝕜} {β : 𝕜} {l : ℕ}
    (hγ : γ h β (l + 1) ≠ 0) : Krylov.givensRho h l ≠ 0 := fun h0 => hγ (by
  rw [gamma_succ, show s h l = Krylov.givensS h l from rfl, Krylov.givensS, h0]
  simp)

/-- Let $h$ be upper Hessenberg. If $\gamma_1, \dots, \gamma_{k+1}$ are all nonzero, then $R_k$ is
nonsingular. -/
theorem isUnit_R_of_gamma_ne_zero {h : ℕ → ℕ → 𝕜} {β : 𝕜}
    (hh : ∀ i j : ℕ, j + 1 < i → h i j = 0) {k : ℕ} (hγ : ∀ j ≤ k, γ h β j ≠ 0) :
    IsUnit (R h k) :=
  (isUnit_R_iff h hh).2 fun l hl => givensRho_ne_zero_of_gamma_ne_zero (hγ (l + 1) (by omega))

/-- Step $0$ of Algorithm 6.12 returns $x_0$. -/
theorem qgmres_zero (x₀ : 𝔼) (u : ℕ → 𝔼) (h : ℕ → ℕ → 𝕜) (β : 𝕜) :
    qgmres x₀ u h β 0 = x₀ := by
  rw [qgmres, toEuclideanLin_colMatrix_apply]
  simp

/-- Step $0$ of the Galerkin approximation (Algorithm 6.7) returns $x_0$. -/
theorem iomOfBasis_zero (x₀ : 𝔼) (u : ℕ → 𝔼) (h : ℕ → ℕ → 𝕜) (β : 𝕜) :
    iomOfBasis x₀ u h β 0 = x₀ := by
  rw [iomOfBasis, toEuclideanLin_colMatrix_apply]
  simp

end QGMRES

/-!
### Section 6.5.7: relations between FOM and GMRES

In this part $x^G_m$ is the approximation of Algorithm 6.9 (GMRES) and $x^F_m$ is the approximation
of Algorithm 6.4 (FOM, `SaadSparse.Chapter06.fomFixed`), on the same Arnoldi basis of $v_1$. FOM is
defined at step $m$ when $H_m$ is nonsingular (`SaadSparse.Chapter06.FOMDefined`).
-/

section Relations

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-! ### The two residual norms and the data of Freund -/

/-- **Section 6.5.7** of [saad2003iterative]. The GMRES residual norm $\rho^G_m = \|b - Ax^G_m\|_2$
after $m$ steps, where $x^G_m$ is the approximation of Algorithm 6.9.

**Reading.** Lean takes exact fixed-size formulas over real or complex scalars. The definitions
therefore have values at a singular reduced system by totalized inversion. In the source an iterate
requiring a nonexistent reduced inverse is undefined.
-/
noncomputable abbrev ρG (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (m : ℕ) : ℝ :=
  ‖b - op A (gmresFixed A b x₀ m)‖

/-- **Section 6.5.7** of [saad2003iterative]. The FOM residual norm $\rho^F_m = \|b - Ax^F_m\|_2$
after $m$ steps, where $x^F_m$ is the approximation of Algorithm 6.4.

The book's $\rho^F_m$ has a meaning exactly when $H_m$ is nonsingular
(`SaadSparse.Chapter06.FOMDefined`). The Lean definition gives a value in all cases.

**Reading.** Lean takes exact fixed-size formulas over real or complex scalars. The definitions
therefore have values at a singular reduced system by totalized inversion. In the source an iterate
requiring a nonexistent reduced inverse is undefined.
-/
noncomputable abbrev ρF (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (m : ℕ) : ℝ :=
  ‖b - op A (fomFixed A b x₀ m)‖

/-- **Proposition 6.12** of [saad2003iterative]. For $m \ge 1$, the scalar $\xi_m = h^{(m-1)}_{mm}$:
the diagonal entry $(m, m)$ of $Q_{m-1} \bar H_m$, which the first $m - 1$ rotations leave.

The definition is `Krylov.rotated h (m - 1) (m - 1) (m - 1)`. At $m = 0$ the natural subtraction
gives $h_{11}$.

**Generalization.** The preceding-rotation data are defined over real or complex scalars, using the
totalized matrix inverse for the coefficient solve. The source uses the real triangular system with
the last rotation omitted.
-/
noncomputable def ξ (h : ℕ → ℕ → 𝕜) (m : ℕ) : 𝕜 := Krylov.rotated h (m - 1) (m - 1) (m - 1)

/-- **Lemma 6.16** of [saad2003iterative]. The $m \times m$ matrix $\tilde R_m$, the leading block
of $Q_{m-1} \bar H_m$. It is the triangular factor one rotation short of $R_m$.

The definition is `Krylov.hessenbergSqOf (Krylov.rotated h (m - 1)) m`.

**Generalization.** The preceding-rotation data are defined over real or complex scalars, using the
totalized matrix inverse for the coefficient solve. The source uses the real triangular system with
the last rotation omitted.
-/
noncomputable def Rtilde (h : ℕ → ℕ → 𝕜) (m : ℕ) : Matrix (Fin m) (Fin m) 𝕜 :=
  Krylov.hessenbergSqOf (Krylov.rotated h (m - 1)) m

/-- **Lemma 6.16** of [saad2003iterative]. The vector $\tilde g_m \in \mathbb{K}^m$ of the first $m$
entries of $Q_{m-1} (\beta e_1)$:
$$\tilde g_m = (\bar c_1 \gamma_1, \dots, \bar c_{m-1} \gamma_{m-1}, \gamma_m).$$

The scalar $\beta$ is the argument `c` of the definition.

**Generalization.** The preceding-rotation data are defined over real or complex scalars, using the
totalized matrix inverse for the coefficient solve. The source uses the real triangular system with
the last rotation omitted.
-/
noncomputable def gtilde (h : ℕ → ℕ → 𝕜) (c : 𝕜) (m : ℕ) : Fin m → 𝕜 :=
  fun i => if (i : ℕ) < m - 1 then Krylov.gvec h c (i : ℕ) else Krylov.gamma h c (m - 1)

/-- **Lemma 6.16** of [saad2003iterative]. The vector $\tilde y_m = \tilde R_m^{-1} \tilde g_m$, the
coordinates of the FOM approximation in the Givens description of Section 6.5.3.

If $\tilde R_m$ is singular, then $\tilde y_m = 0$.

**Generalization.** The preceding-rotation data are defined over real or complex scalars, using the
totalized matrix inverse for the coefficient solve. The source uses the real triangular system with
the last rotation omitted.
-/
noncomputable def ytilde (h : ℕ → ℕ → 𝕜) (c : 𝕜) (m : ℕ) : Fin m → 𝕜 :=
  (Rtilde h m)⁻¹ *ᵥ gtilde h c m

/-- The entry $(i, j)$ of $\tilde R_m$ is `Krylov.rotated h (m - 1) i j`.

**Generalization.** The preceding-rotation data are defined over real or complex scalars, using the
totalized matrix inverse for the coefficient solve. The source uses the real triangular system with
the last rotation omitted.
-/
theorem Rtilde_apply (h : ℕ → ℕ → 𝕜) {m : ℕ} (i j : Fin m) :
    Rtilde h m i j = Krylov.rotated h (m - 1) (i : ℕ) (j : ℕ) := rfl

/-- The last entry of $\tilde g_{m+1}$ is $\gamma_{m+1}$.

**Generalization.** The preceding-rotation data are defined over real or complex scalars, using the
totalized matrix inverse for the coefficient solve. The source uses the real triangular system with
the last rotation omitted.
-/
theorem gtilde_last (h : ℕ → ℕ → 𝕜) (c : 𝕜) (m : ℕ) :
    gtilde h c (m + 1) (Fin.last m) = Krylov.gamma h c m := by
  rw [gtilde, Nat.add_sub_cancel]
  exact ite_eq_right (by simp)

/-- For a `0`-based index $i < m$, the entry $i$ of $\tilde g_{m+1}$ is $\bar c_{i+1} \gamma_{i+1}$.

**Generalization.** The preceding-rotation data are defined over real or complex scalars, using the
totalized matrix inverse for the coefficient solve. The source uses the real triangular system with
the last rotation omitted.
-/
theorem gtilde_castSucc (h : ℕ → ℕ → 𝕜) (c : 𝕜) {m : ℕ} (i : Fin m) :
    gtilde h c (m + 1) i.castSucc = Krylov.gvec h c (i : ℕ) := by
  rw [gtilde, Nat.add_sub_cancel]
  exact ite_eq_left i.isLt

/-!
### The matrices $\tilde R_m$ and $R_m$

The two triangular factors differ in a single entry. This is the content of the book's block
computation (6.72)–(6.73). The lemma `Krylov.rotated_succ_apply` holds by definition.
-/

/-- The rotation with `0`-based index $k$ changes only the rows $k$ and $k + 1$. -/
private theorem rotated_succ_of_ne (h : ℕ → ℕ → 𝕜) {k i : ℕ} (h1 : i ≠ k) (h2 : i ≠ k + 1)
    (j : ℕ) : Krylov.rotated h (k + 1) i j = Krylov.rotated h k i j := by
  rw [Krylov.rotated_succ_apply, ite_eq_right h1, ite_eq_right h2]

/-- Let $h$ be upper Hessenberg. For every $w \in \mathbb{K}^{m+1}$,
$$R_{m+1} w = \tilde R_{m+1} w + (\rho_{m+1} - \xi_{m+1}) \, w_{m+1} \, e_{m+1}.$$
So $R_{m+1}$ and $\tilde R_{m+1}$ agree except in the entry $(m+1, m+1)$, where the former has
$\rho_{m+1}$ and the latter $\xi_{m+1}$. This is (6.72)–(6.73) of [saad2003iterative]. -/
theorem R_mulVec_eq_Rtilde_mulVec_add (h : ℕ → ℕ → 𝕜)
    (hh : ∀ i j : ℕ, j + 1 < i → h i j = 0) (m : ℕ) (v : Fin (m + 1) → 𝕜) :
    R h (m + 1) *ᵥ v = Rtilde h (m + 1) *ᵥ v +
      Pi.single (Fin.last m)
        ((((Krylov.givensRho h m : ℝ) : 𝕜) - Krylov.rotated h m m m) * v (Fin.last m)) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply]
  rcases eq_or_ne i (Fin.last m) with rfl | hi
  · rw [Pi.single_eq_same, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    have h1 : ∀ j : Fin m, R h (m + 1) (Fin.last m) j.castSucc * v j.castSucc = 0 := by
      intro j
      rw [R_apply, Fin.val_last, Fin.val_castSucc,
        Krylov.rotated_eq_zero_of_lt h (Matrix.isUpperHessenberg_iff_nat.2 hh)
            (m + 1) m (j : ℕ) (by omega) j.isLt, zero_mul]
    have h2 : ∀ j : Fin m, Rtilde h (m + 1) (Fin.last m) j.castSucc * v j.castSucc = 0 := by
      intro j
      rw [Rtilde_apply, Nat.add_sub_cancel, Fin.val_last, Fin.val_castSucc,
        Krylov.rotated_eq_zero_of_lt h (Matrix.isUpperHessenberg_iff_nat.2 hh)
            m m (j : ℕ) j.isLt j.isLt, zero_mul]
    rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_congr rfl (fun j _ => h2 j)]
    rw [R_apply, Rtilde_apply, Nat.add_sub_cancel, Fin.val_last,
      Krylov.rotated_succ_self h m]
    ring
  · have hlt : (i : ℕ) < m := by
      have := i.isLt
      have : (i : ℕ) ≠ m := fun hc => hi (Fin.ext (by simpa using hc))
      omega
    rw [Pi.single_eq_of_ne hi, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [R_apply, Rtilde_apply, Nat.add_sub_cancel,
      rotated_succ_of_ne h (by omega) (by omega) (j : ℕ)]

variable (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : EuclideanSpace 𝕜 (Fin n))

/-- The empty matrix $H_0$ is nonsingular, so FOM is defined at step $0$. -/
theorem fomDefined_zero : FOMDefined A b x₀ 0 := by
  rw [FOMDefined, Matrix.isUnit_iff_isUnit_det, Matrix.det_isEmpty]
  exact isUnit_one

open scoped Classical in
/-- **Proposition 6.15** of [saad2003iterative]. The smallest FOM residual norm of the first $m$
steps,
$$\rho^F_{m*} = \min \{ \rho^F_i : 0 \le i \le m, \ H_i \text{ nonsingular} \}.$$
The steps where $H_i$ is singular are left out.

The minimum runs over the $m + 1$ indices $0, \dots, m$, as the sum of (6.66) does. Step $0$ is
always included and gives the initial residual norm, which the book writes
$\rho^F_0 = \rho^G_0$.

**Reading.** The minimum is taken over the initial residual and the defined FOM iterates through
step $m$. The source refers to the first $m$ steps, while its preceding sum also includes index
zero.
-/
noncomputable def ρFmin (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (m : ℕ) : ℝ :=
  ((Finset.range (m + 1)).filter (FOMDefined A b x₀)).inf'
    ⟨0, Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.succ_pos m), fomDefined_zero A b x₀⟩⟩
    (ρF A b x₀)

/-! ### Nonsingularity of $R_m$ and $\tilde R_m$ -/

/-- If $m$ is less than the grade of $v_1$, then $R_m$ is nonsingular, with no hypothesis on $A$:
below the grade no rotation degenerates. -/
theorem isUnit_R_of_lt_grade {m : ℕ} (hm : m < grade A (v₁ A b x₀)) :
    IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m) := by
  refine (isUnit_R_iff _ (arnoldiCoeff_v₁_eq_zero_of_lt A b x₀)).2 fun k hk => ?_
  rw [arnoldiCoeff_v₁]
  exact Krylov.givensRho_arnoldi_ne_zero (by rw [← grade_v₁]; omega)

/-- If $m + 1 \le \operatorname{grade}(v_1)$ and $H_{m+1}$ is nonsingular, then $c_{m+1} \neq 0$.
The proof uses `Krylov.isUnit_hessenbergSq_iff_givensC_ne_zero`. -/
theorem givensC_ne_zero_of_fomDefined {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀))
    (hH : FOMDefined A b x₀ (m + 1)) : c (arnoldiCoeff A (v₁ A b x₀)) m ≠ 0 := by
  rw [arnoldiCoeff_v₁]
  refine (Krylov.isUnit_hessenbergSq_iff_givensC_ne_zero (by rw [← grade_v₁]; exact hm)).1 ?_
  rw [← H_v₁ A b x₀]
  exact hH

/-- If $m + 1 \le \operatorname{grade}(v_1)$ and $H_{m+1}$ is nonsingular, then $\xi_{m+1} \neq 0$.
-/
theorem ξ_ne_zero_of_fomDefined {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀))
    (hH : FOMDefined A b x₀ (m + 1)) : ξ (arnoldiCoeff A (v₁ A b x₀)) (m + 1) ≠ 0 := by
  rw [ξ, Nat.add_sub_cancel]
  intro h0
  exact givensC_ne_zero_of_fomDefined A b x₀ hm hH
    ((Krylov.givensC_eq_zero_iff (arnoldiCoeff A (v₁ A b x₀)) m).2 h0)

/-- If $m + 1 \le \operatorname{grade}(v_1)$ and $H_{m+1}$ is nonsingular, then $\rho_{m+1} \neq 0$.
-/
theorem givensRho_ne_zero_of_fomDefined {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀))
    (hH : FOMDefined A b x₀ (m + 1)) :
    Krylov.givensRho (arnoldiCoeff A (v₁ A b x₀)) m ≠ 0 := by
  refine Krylov.givensRho_ne_zero_of_rotated_ne_zero _ ?_
  have := ξ_ne_zero_of_fomDefined A b x₀ hm hH
  rwa [ξ, Nat.add_sub_cancel] at this

/-- If $m \le \operatorname{grade}(v_1)$ and $H_m$ is nonsingular, then $R_m$ is nonsingular. The
earlier rotations do not degenerate below the grade, and the last one does not degenerate
because its pivot $\xi_m$ is nonzero. -/
theorem isUnit_R_of_fomDefined {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀))
    (hH : FOMDefined A b x₀ m) : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m) := by
  refine (isUnit_R_iff _ (arnoldiCoeff_v₁_eq_zero_of_lt A b x₀)).2 fun k hk => ?_
  rcases Nat.lt_or_ge (k + 1) m with h1 | h1
  · rw [arnoldiCoeff_v₁]
    exact Krylov.givensRho_arnoldi_ne_zero (by rw [← grade_v₁]; omega)
  · have hkm : m = k + 1 := by omega
    subst hkm
    exact givensRho_ne_zero_of_fomDefined A b x₀ hm hH

/-- If $m + 1 \le \operatorname{grade}(v_1)$ and $H_{m+1}$ is nonsingular, then $\tilde R_{m+1}$ is
nonsingular: its diagonal is $(\rho_1, \dots, \rho_m, \xi_{m+1})$. -/
theorem isUnit_Rtilde_of_fomDefined {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀))
    (hH : FOMDefined A b x₀ (m + 1)) :
    IsUnit (Rtilde (arnoldiCoeff A (v₁ A b x₀)) (m + 1)) := by
  rw [Rtilde, Nat.add_sub_cancel]
  refine Krylov.isUnit_hessenbergSqOf_rotated _
    (Matrix.isUpperHessenberg_iff_nat.2 (arnoldiCoeff_v₁_eq_zero_of_lt A b x₀))
    (le_refl (m + 1)) fun j hj => ?_
  rcases Nat.lt_or_ge j m with h1 | h1
  · rw [Krylov.rotated_diag _
      (Matrix.isUpperHessenberg_iff_nat.2 (arnoldiCoeff_v₁_eq_zero_of_lt A b x₀)) h1]
    have hρ : Krylov.givensRho (arnoldiCoeff A (v₁ A b x₀)) j ≠ 0 := by
      rw [arnoldiCoeff_v₁]
      exact Krylov.givensRho_arnoldi_ne_zero (by rw [← grade_v₁]; omega)
    simpa using hρ
  · have hjm : j = m := by omega
    subst hjm
    have := ξ_ne_zero_of_fomDefined A b x₀ hm hH
    rwa [ξ, Nat.add_sub_cancel] at this

/-! ### The two approximations as backbone specifications -/

/-- If $m \le \operatorname{grade}(v_1)$ and $R_m$ is nonsingular, then $\rho^G_m = |\gamma_{m+1}|$.
This is (6.42) of [saad2003iterative], in the form that Section 6.5.7 uses. -/
theorem ρG_eq_norm_gamma {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀))
    (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) :
    ρG A b x₀ m = ‖γ (arnoldiCoeff A (v₁ A b x₀)) (β A b x₀ : 𝕜) m‖ :=
  equation_6_42 A b x₀ hm hR

/-- If $m < \operatorname{grade}(v_1)$, then $x^G_m$ is the minimal-residual iterate on
$\mathcal{K}_m(A, r_0)$. -/
theorem gmresFixed_isMinResidualIterate_of_lt {m : ℕ} (hm : m < grade A (v₁ A b x₀)) :
    Krylov.IsMinResidualIterate (op A) b x₀ m (gmresFixed A b x₀ m) :=
  gmresFixed_isMinResidualIterate A b x₀ hm.le (isUnit_R_of_lt_grade A b x₀ hm)

/-- If $m \le \operatorname{grade}(v_1)$ and $H_m$ is nonsingular, then $x^F_m$ is the Galerkin
iterate on $\mathcal{K}_m(A, r_0)$ (`Krylov.IsGalerkinIterate`). -/
theorem fomFixed_isGalerkin {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀))
    (hH : FOMDefined A b x₀ m) :
    Krylov.IsGalerkinIterate (op A) b x₀ m (fomFixed A b x₀ m) :=
  fomFixed_isGalerkinIterate A b x₀ hH hm

/-- If $m \le \operatorname{grade}(v_1)$ and $H_m$ and $R_m$ are nonsingular, then
$\rho^G_m \le \rho^F_m$: both approximations lie in $x_0 + \mathcal{K}_m(A, r_0)$, and GMRES
minimizes the residual norm there. -/
theorem ρG_le_ρF {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀)) (hH : FOMDefined A b x₀ m)
    (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) : ρG A b x₀ m ≤ ρF A b x₀ m :=
  Krylov.norm_residual_minRes_le_galerkin (gmresFixed_isMinResidualIterate A b x₀ hm hR)
    (fomFixed_isGalerkin A b x₀ hm hH)

/-- If $m + 1 \le \operatorname{grade}(v_1)$ and $R_{m+1}$ is nonsingular, then
$\rho^G_{m+1} \le \rho^G_m$, because $\mathcal{K}_m \subseteq \mathcal{K}_{m+1}$. -/
theorem ρG_succ_le {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀))
    (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) (m + 1))) :
    ρG A b x₀ (m + 1) ≤ ρG A b x₀ m :=
  IsMinResidual.norm_residual_le (gmresFixed_isMinResidualIterate_of_lt A b x₀ (by omega))
    (gmresFixed_isMinResidualIterate A b x₀ hm hR)
    (Krylov.subspace_mono (op A) (b - op A x₀) (Nat.le_succ m))

/-- Let $h$ be upper Hessenberg, $t \in \mathbb{K}$, and let $y \in \mathbb{K}^m$ satisfy
$R_m y = g_m$ for $\beta = t$. Then the vector $(y; 0)$ satisfies $R_{m+1} (y; 0) = g_{m+1} -
\bar c_{m+1} \gamma_{m+1} e_{m+1}$: it solves the system of step $m + 1$ except in the last
entry, where the left side is $0$. This is the book's remark that $R_{m+1}$ gets one new row and
one new column. -/
theorem R_mulVec_snoc (h : ℕ → ℕ → 𝕜) (hh : ∀ i j : ℕ, j + 1 < i → h i j = 0) (t : 𝕜) {m : ℕ}
    (yp : Fin m → 𝕜) (hyp : R h m *ᵥ yp = g h t m) :
    R h (m + 1) *ᵥ (Fin.snoc yp (0 : 𝕜) : Fin (m + 1) → 𝕜)
      = g h t (m + 1) - Pi.single (Fin.last m) (Krylov.gvec h t m) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.sub_apply]
  rw [Fin.sum_univ_castSucc, Fin.snoc_last, mul_zero, add_zero]
  rcases eq_or_ne i (Fin.last m) with rfl | hi
  · rw [Pi.single_eq_same, g_apply, Fin.val_last, sub_self]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [R_apply, Fin.val_last, Fin.val_castSucc,
      Krylov.rotated_eq_zero_of_lt h (Matrix.isUpperHessenberg_iff_nat.2 hh)
          (m + 1) m (j : ℕ) (by omega) j.isLt, zero_mul]
  · have hlt : (i : ℕ) < m := by
      have := i.isLt
      have : (i : ℕ) ≠ m := fun hc => hi (Fin.ext (by simpa using hc))
      omega
    rw [Pi.single_eq_of_ne hi, sub_zero]
    have hrow : ∀ j : Fin m, R h (m + 1) i j.castSucc *
        (Fin.snoc yp (0 : 𝕜) : Fin (m + 1) → 𝕜) j.castSucc
        = R h m ⟨(i : ℕ), hlt⟩ j * yp j := by
      intro j
      rw [Fin.snoc_castSucc, R_apply, R_apply, Fin.val_castSucc,
        Krylov.rotated_succ_eq_of_lt h (Matrix.isUpperHessenberg_iff_nat.2 hh)
            m (j : ℕ) j.isLt (i : ℕ)]
    rw [Finset.sum_congr rfl fun j _ => hrow j]
    have hval := congrFun hyp ⟨(i : ℕ), hlt⟩
    simp only [Matrix.mulVec, dotProduct] at hval
    rw [hval, g_apply, g_apply]

open scoped Classical in
/-- If $i \le m$ and $H_i$ is nonsingular, then $\rho^F_{m*} \le \rho^F_i$.

**Reading.** The minimum is taken over the initial residual and the defined FOM iterates through
step $m$. The source refers to the first $m$ steps, while its preceding sum also includes index
zero.
-/
theorem ρFmin_le {m i : ℕ} (hi : i ≤ m) (hH : FOMDefined A b x₀ i) :
    ρFmin A b x₀ m ≤ ρF A b x₀ i := by
  rw [ρFmin]
  exact Finset.inf'_le _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hH⟩)

open scoped Classical in
/-- If $r \le \rho^F_i$ for every $i \le m$ with $H_i$ nonsingular, then $r \le \rho^F_{m*}$.

**Reading.** The minimum is taken over the initial residual and the defined FOM iterates through
step $m$. The source refers to the first $m$ steps, while its preceding sum also includes index
zero.
-/
theorem le_ρFmin {m : ℕ} {r : ℝ} (h : ∀ i ≤ m, FOMDefined A b x₀ i → r ≤ ρF A b x₀ i) :
    r ≤ ρFmin A b x₀ m := by
  rw [ρFmin]
  refine Finset.le_inf' _ _ fun i hi => ?_
  obtain ⟨hi1, hi2⟩ := Finset.mem_filter.1 hi
  exact h i (by have := Finset.mem_range.1 hi1; omega) hi2

end Relations

/-!
### The numbered results of Section 6.5.7 over $\mathbb{R}$

In this part $A \in \mathbb{R}^{n \times n}$ and $b, x_0 \in \mathbb{R}^n$, and $c_i$, $s_i$ and
$\xi_m$ are the Givens data of the Arnoldi coefficients of $v_1$.
-/

section BookResultsRelations

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : EuclideanSpace ℝ (Fin n))

/-! ### Equation (6.62) -/

/-- **Equation (6.62)** of [saad2003iterative], one step. Let $m + 1 < \operatorname{grade}(v_1)$.
Then
$$\rho^G_{m+1} = |s_{m+1}| \, \rho^G_m.$$

**Reading.** Lean uses a prefix strictly below grade so the triangular factors are nonsingular
without a hypothesis on the system matrix. This excludes the final breakdown step of a nonsingular
problem, where the source product formula still holds. The Lean formulas allow complex scalars.
-/
theorem ρG_succ {m : ℕ} (hm : m + 1 < grade A (v₁ A b x₀)) :
    ρG A b x₀ (m + 1) = ‖s (arnoldiCoeff A (v₁ A b x₀)) m‖ * ρG A b x₀ m := by
  rw [arnoldiCoeff_v₁]
  exact Krylov.IsMinResidualIterate.norm_residual_succ_eq (by rw [← grade_v₁]; exact hm)
    (gmresFixed_isMinResidualIterate_of_lt A b x₀ (by omega))
    (gmresFixed_isMinResidualIterate_of_lt A b x₀ hm)

/-- **Equation (6.62)** of [saad2003iterative]. Let $m < \operatorname{grade}(v_1)$. Then
$$\rho^G_m = |s_1 s_2 \cdots s_m| \, \beta.$$

**Reading.** Lean uses a prefix strictly below grade so the triangular factors are nonsingular
without a hypothesis on the system matrix. This excludes the final breakdown step of a nonsingular
problem, where the source product formula still holds. The Lean formulas allow complex scalars.
-/
theorem equation_6_62 {m : ℕ} (hm : m < grade A (v₁ A b x₀)) :
    ρG A b x₀ m
      = (∏ i ∈ Finset.range m, ‖s (arnoldiCoeff A (v₁ A b x₀)) i‖) * β A b x₀ := by
  rw [ρG_eq_norm_gamma A b x₀ hm.le (isUnit_R_of_lt_grade A b x₀ hm), norm_gamma_eq_prod,
    RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]

/-! ### Proposition 6.12 (Brown) and (6.63) -/

/-- Proposition 6.12 of [saad2003iterative], first form: if $m + 1 \le \operatorname{grade}(v_1)$
and $H_{m+1}$ is nonsingular, then $\rho^F_{m+1} = \rho^G_{m+1} / |c_{m+1}|$.

**Reading.** The two clauses give the source ratio and its square-root form. The first also works
over complex scalars, using the modulus of the rotation coefficient. The valid-prefix hypothesis
specifies that the Arnoldi steps were reached.
-/
theorem ρF_eq_div_norm_c {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀))
    (hH : FOMDefined A b x₀ (m + 1)) :
    ρF A b x₀ (m + 1) = ρG A b x₀ (m + 1) / ‖c (arnoldiCoeff A (v₁ A b x₀)) m‖ := by
  rw [arnoldiCoeff_v₁]
  exact Krylov.IsGalerkinIterate.norm_residual_eq_div_norm_givensC
    (by rw [← grade_v₁]; exact hm) (fomFixed_isGalerkin A b x₀ hm hH)
    (gmresFixed_isMinResidualIterate A b x₀ hm (isUnit_R_of_fomDefined A b x₀ hm hH))

/-- The first $m$ rotations leave the subdiagonal entry $h_{m+2,m+1}$ unchanged. -/
private theorem rotated_succ_row (h : ℕ → ℕ → ℝ) (m : ℕ) :
    Krylov.rotated h m (m + 1) m = h (m + 1) m :=
  Krylov.rotated_eq_of_le h m (m + 1) m le_rfl

/-- **Equation (6.63)** of [saad2003iterative]. Let $m + 1 \le \operatorname{grade}(v_1)$ and let
$H_{m+1}$ be nonsingular. Then
$$\rho^F_{m+1} = \rho^G_{m+1} \sqrt{1 + \frac{h_{m+2,m+1}^2}{\xi_{m+1}^2}}.$$

**Reading.** The two clauses give the source ratio and its square-root form. The first also works
over complex scalars, using the modulus of the rotation coefficient. The valid-prefix hypothesis
specifies that the Arnoldi steps were reached.
-/
theorem equation_6_63 {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀))
    (hH : FOMDefined A b x₀ (m + 1)) :
    ρF A b x₀ (m + 1) = ρG A b x₀ (m + 1) *
      Real.sqrt (1 + arnoldiCoeff A (v₁ A b x₀) (m + 1) m ^ 2 /
        ξ (arnoldiCoeff A (v₁ A b x₀)) (m + 1) ^ 2) := by
  set h := arnoldiCoeff A (v₁ A b x₀) with hdef
  have hξ : ξ h (m + 1) = Krylov.rotated h m m m := by rw [ξ, Nat.add_sub_cancel]
  have hξ0 : Krylov.rotated h m m m ≠ 0 := by
    have := ξ_ne_zero_of_fomDefined A b x₀ hm hH
    rwa [hξ] at this
  have hρ0 : Krylov.givensRho h m ≠ 0 := givensRho_ne_zero_of_fomDefined A b x₀ hm hH
  have hρpos : 0 < Krylov.givensRho h m :=
    lt_of_le_of_ne (Krylov.givensRho_nonneg h m) (Ne.symm hρ0)
  have hsq : Krylov.givensRho h m ^ 2 = Krylov.rotated h m m m ^ 2 + h (m + 1) m ^ 2 := by
    rw [Krylov.givensRho_sq, rotated_succ_row, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
      sq_abs]
  have hc : ‖c h m‖ = |Krylov.rotated h m m m| / Krylov.givensRho h m := by
    rw [show c h m = Krylov.givensC h m from rfl, Krylov.givensC, norm_div,
      RCLike.norm_ofReal, abs_of_nonneg (Krylov.givensRho_nonneg h m), Real.norm_eq_abs]
  have hcne : ‖c h m‖ ≠ 0 := by
    rw [hc]
    exact div_ne_zero (abs_ne_zero.2 hξ0) hρ0
  have habs : (0 : ℝ) < |Krylov.rotated h m m m| := abs_pos.2 hξ0
  have hkey : Real.sqrt (1 + h (m + 1) m ^ 2 / ξ h (m + 1) ^ 2) = 1 / ‖c h m‖ := by
    rw [hξ, hc, one_div_div]
    rw [show (1 : ℝ) + h (m + 1) m ^ 2 / Krylov.rotated h m m m ^ 2
        = (Krylov.givensRho h m / |Krylov.rotated h m m m|) ^ 2 by
      rw [div_pow, sq_abs, hsq]
      field_simp]
    exact Real.sqrt_sq (by positivity)
  rw [ρF_eq_div_norm_c A b x₀ hm hH, hkey, ← hdef, div_eq_mul_one_div]

/-- **Proposition 6.12** of [saad2003iterative] (Brown). Let $1 \le m \le \operatorname{grade}(v_1)$
and let $H_m$ be nonsingular. Then $c_m \neq 0$ and
$$\rho^F_m = \frac{\rho^G_m}{|c_m|} = \rho^G_m \sqrt{1 + \frac{h_{m+1,m}^2}{\xi_m^2}}.$$

**Reading.** The hypotheses that $m$ Arnoldi steps have been taken and that $H_m$ is nonsingular
are explicit, because the proof needs them. -/
theorem proposition_6_12 {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀)) (hm0 : 0 < m)
    (hH : FOMDefined A b x₀ m) :
    c (arnoldiCoeff A (v₁ A b x₀)) (m - 1) ≠ 0 ∧
      ρF A b x₀ m = ρG A b x₀ m / ‖c (arnoldiCoeff A (v₁ A b x₀)) (m - 1)‖ ∧
        ρF A b x₀ m = ρG A b x₀ m *
          Real.sqrt (1 + arnoldiCoeff A (v₁ A b x₀) m (m - 1) ^ 2 /
            ξ (arnoldiCoeff A (v₁ A b x₀)) m ^ 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  exact ⟨givensC_ne_zero_of_fomDefined A b x₀ hm hH, ρF_eq_div_norm_c A b x₀ hm hH,
    equation_6_63 A b x₀ hm hH⟩

/-! ### Proposition 6.13 (Cullum and Greenbaum) and (6.64)–(6.65) -/

/-- **Equation (6.65)** of [saad2003iterative]. Let $m + 1 \le \operatorname{grade}(v_1)$, let
$H_{m+1}$ be nonsingular, and let $\rho^G_{m+1} \neq 0$. Then
$$\frac{1}{(\rho^F_{m+1})^2} + \frac{1}{(\rho^G_m)^2} = \frac{1}{(\rho^G_{m+1})^2}.$$

**Reading.** The formula assumes the later GMRES residual norm is nonzero. Nonsingularity of the FOM
projected matrix and the reached-prefix hypothesis are also stated, as in the printed proposition.
The reciprocal identity uses norms over either scalar field.
-/
theorem equation_6_65 {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀)) (hH : FOMDefined A b x₀ (m + 1))
    (h0 : ρG A b x₀ (m + 1) ≠ 0) :
    1 / ρF A b x₀ (m + 1) ^ 2 + 1 / ρG A b x₀ m ^ 2 = 1 / ρG A b x₀ (m + 1) ^ 2 := by
  have hkey := Krylov.inv_sq_norm_residual_minRes
    (gmresFixed_isMinResidualIterate_of_lt A b x₀ (by omega))
    (gmresFixed_isMinResidualIterate A b x₀ hm (isUnit_R_of_fomDefined A b x₀ hm hH))
    (fomFixed_isGalerkin A b x₀ hm hH) (norm_ne_zero_iff.1 h0)
  linarith

/-- **Proposition 6.13** of [saad2003iterative] (Cullum and Greenbaum), equation (6.64). Let
$m + 1 \le \operatorname{grade}(v_1)$, let $H_{m+1}$ be nonsingular, and let
$\rho^G_{m+1} \neq 0$. Then
$$\rho^F_{m+1} = \frac{\rho^G_{m+1}}{\sqrt{1 - (\rho^G_{m+1} / \rho^G_m)^2}}.$$

**Reading.** The hypotheses that $H_{m+1}$ is nonsingular and that $\rho^G_{m+1} \neq 0$ are
explicit, because the proof needs them.

**Reading.** The formula assumes the later GMRES residual norm is nonzero. Nonsingularity of the FOM
projected matrix and the reached-prefix hypothesis are also stated, as in the printed proposition.
The reciprocal identity uses norms over either scalar field.
-/
theorem proposition_6_13 {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀)) (hH : FOMDefined A b x₀ (m + 1))
    (h0 : ρG A b x₀ (m + 1) ≠ 0) :
    ρF A b x₀ (m + 1)
      = ρG A b x₀ (m + 1) /
        Real.sqrt (1 - (ρG A b x₀ (m + 1) / ρG A b x₀ m) ^ 2) := by
  have h65 := equation_6_65 A b x₀ hm hH h0
  have hRm1 := isUnit_R_of_fomDefined A b x₀ hm hH
  have hGF := ρG_le_ρF A b x₀ hm hH hRm1
  have hGG := ρG_succ_le A b x₀ hm hRm1
  have ha : 0 < ρG A b x₀ (m + 1) := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
  have hf : 0 < ρF A b x₀ (m + 1) := lt_of_lt_of_le ha hGF
  have hp : 0 < ρG A b x₀ m := lt_of_lt_of_le ha hGG
  have hmul : ρF A b x₀ (m + 1) ^ 2 * (ρG A b x₀ m ^ 2 - ρG A b x₀ (m + 1) ^ 2)
      = ρG A b x₀ m ^ 2 * ρG A b x₀ (m + 1) ^ 2 := by
    field_simp at h65
    nlinarith [h65]
  have hgap : 0 < ρG A b x₀ m ^ 2 - ρG A b x₀ (m + 1) ^ 2 := by
    have hprod : (0 : ℝ) <
        ρF A b x₀ (m + 1) ^ 2 * (ρG A b x₀ m ^ 2 - ρG A b x₀ (m + 1) ^ 2) := by
      rw [hmul]; positivity
    rcases mul_pos_iff.1 hprod with ⟨-, hgt⟩ | ⟨hlt', -⟩
    · exact hgt
    · nlinarith
  have hnn : (0 : ℝ) ≤ 1 - (ρG A b x₀ (m + 1) / ρG A b x₀ m) ^ 2 := by
    rw [div_pow]
    rw [sub_nonneg, div_le_one (by positivity)]
    nlinarith
  have hs2 : Real.sqrt (1 - (ρG A b x₀ (m + 1) / ρG A b x₀ m) ^ 2) ^ 2
      = 1 - (ρG A b x₀ (m + 1) / ρG A b x₀ m) ^ 2 := Real.sq_sqrt hnn
  have hspos : 0 < Real.sqrt (1 - (ρG A b x₀ (m + 1) / ρG A b x₀ m) ^ 2) := by
    refine Real.sqrt_pos.2 ?_
    rw [div_pow, sub_pos, div_lt_one (by positivity)]
    nlinarith
  rw [eq_div_iff (ne_of_gt hspos)]
  have hsq : (ρF A b x₀ (m + 1) *
      Real.sqrt (1 - (ρG A b x₀ (m + 1) / ρG A b x₀ m) ^ 2)) ^ 2
      = ρG A b x₀ (m + 1) ^ 2 := by
    rw [mul_pow, hs2, div_pow]
    field_simp
    nlinarith [hmul]
  nlinarith [hsq, ha.le, mul_pos hf hspos]

/-! ### Equation (6.66) and Corollary 6.14, equation (6.67) -/

/-- **Equation (6.66)** of [saad2003iterative]. Let $m \le \operatorname{grade}(v_1)$, let $H_i$ be
nonsingular for every $i \le m$, and let $\rho^G_m \neq 0$. Then
$$\sum_{i=0}^m \frac{1}{(\rho^F_i)^2} = \frac{1}{(\rho^G_m)^2}.$$

The term $i = 0$ is the initial residual norm $\rho^F_0 = \|r_0\|_2$.

**Reading.** Lean assumes every FOM reduced system in the prefix is nonsingular and the final GMRES
residual is nonzero. This is the regime in which the proof uses the reciprocals of actual residual
norms. The identities are also available for complex systems.
-/
theorem equation_6_66 {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀)) (hH : ∀ i ≤ m, FOMDefined A b x₀ i)
    (h0 : ρG A b x₀ m ≠ 0) :
    ∑ i ∈ Finset.range (m + 1), 1 / ρF A b x₀ i ^ 2 = 1 / ρG A b x₀ m ^ 2 :=
  (Krylov.inv_sq_norm_residual_minRes_eq_sum (xF := fun i => fomFixed A b x₀ i)
    (gmresFixed_isMinResidualIterate A b x₀ hm (isUnit_R_of_fomDefined A b x₀ hm (hH m le_rfl)))
    (fun i hi => fomFixed_isGalerkin A b x₀ (hi.trans hm) (hH i hi))
    (norm_ne_zero_iff.1 h0)).symm

/-- **Corollary 6.14** of [saad2003iterative], equation (6.67). Let
$m \le \operatorname{grade}(v_1)$, let $H_i$ be nonsingular for every $i \le m$, and let
$\rho^G_m \neq 0$. Then
$$\rho^G_m = \frac{1}{\sqrt{\sum_{i=0}^m (\rho^F_i)^{-2}}}.$$

**Reading.** Lean assumes every FOM reduced system in the prefix is nonsingular and the final GMRES
residual is nonzero. This is the regime in which the proof uses the reciprocals of actual residual
norms. The identities are also available for complex systems.
-/
theorem corollary_6_14 {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀)) (hH : ∀ i ≤ m, FOMDefined A b x₀ i)
    (h0 : ρG A b x₀ m ≠ 0) :
    ρG A b x₀ m = 1 / Real.sqrt (∑ i ∈ Finset.range (m + 1), 1 / ρF A b x₀ i ^ 2) := by
  have ha : 0 < ρG A b x₀ m := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
  rw [equation_6_66 A b x₀ hm hH h0,
    show (1 : ℝ) / ρG A b x₀ m ^ 2 = (1 / ρG A b x₀ m) ^ 2 by rw [div_pow, one_pow],
    Real.sqrt_sq (by positivity), one_div_one_div]

/-! ### Proposition 6.15 and (6.68) -/

/-- **Proposition 6.15** of [saad2003iterative], equation (6.68). Let
$m \le \operatorname{grade}(v_1)$ and let $H_i$ be nonsingular for every $i \le m$. Then
$$\rho^G_m \le \rho^F_{m*} \le \sqrt{m + 1} \, \rho^G_m.$$

**Correction.** The book prints $\sqrt{m}$ in (6.68). The inequality displayed two lines above
it, $1/(\rho^G_m)^2 = \sum_{i=0}^m 1/(\rho^F_i)^2 \le (m+1)/(\rho^F_{m*})^2$, which is what
(6.66) gives, yields $\sqrt{m+1}$, and the sum runs over the $m + 1$ indices $0, \dots, m$, with
$\rho^F_0$ the initial residual norm. The printed constant fails already at $m = 1$: if
$|c_1| = |s_1| = 1/\sqrt{2}$, then (6.62) and Proposition 6.12 give
$\rho^F_0 = \rho^F_1 = \beta$ and $\rho^G_1 = \beta / \sqrt{2}$, so
$\rho^F_{1*} = \sqrt{2} \, \rho^G_1$.

**Reading.** Lean assumes that all FOM reduced systems in the prefix are nonsingular. The source
permits skipping an undefined FOM step.
-/
theorem proposition_6_15 {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀))
    (hH : ∀ i ≤ m, FOMDefined A b x₀ i) :
    ρG A b x₀ m ≤ ρFmin A b x₀ m ∧
      ρFmin A b x₀ m ≤ Real.sqrt (m + 1) * ρG A b x₀ m := by
  have hG := gmresFixed_isMinResidualIterate A b x₀ hm
    (isUnit_R_of_fomDefined A b x₀ hm (hH m le_rfl))
  constructor
  · refine le_ρFmin A b x₀ fun i hi' _ => ?_
    exact hG.min (fomFixed A b x₀ i)
      (Krylov.subspace_mono (op A) (b - op A x₀) hi'
        (fomFixed_isGalerkin A b x₀ (hi'.trans hm) (hH i hi')).mem)
  · obtain ⟨i, hi, hle⟩ := Krylov.exists_norm_residual_galerkin_le
      (xF := fun i => fomFixed A b x₀ i) hG
      (fun i hi => fomFixed_isGalerkin A b x₀ (hi.trans hm) (hH i hi))
    exact le_trans (ρFmin_le A b x₀ hi (hH i hi)) hle

/-! ### Equations (6.74) and (6.75) -/

/-- **Equation (6.74)** of [saad2003iterative]. Let $A$ be nonsingular,
$m + 1 \le \operatorname{grade}(v_1)$, let $H_{m+1}$ be nonsingular, and let
$\rho^G_{m+1} \neq 0$. Then
$$x^G_{m+1} = s_{m+1}^2 \, x^G_m + c_{m+1}^2 \, x^F_{m+1}.$$

**Reading.** Lean assumes a nonsingular system and FOM reduced matrix, a reached prefix and a
nonzero later GMRES residual. The source derives these identities after its triangular systems
without listing all these hypotheses.
-/
theorem equation_6_74 {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀)) (hA : IsUnit A)
    (hH : FOMDefined A b x₀ (m + 1)) (h0 : ρG A b x₀ (m + 1) ≠ 0) :
    gmresFixed A b x₀ (m + 1)
      = s (arnoldiCoeff A (v₁ A b x₀)) m ^ 2 • gmresFixed A b x₀ m +
        c (arnoldiCoeff A (v₁ A b x₀)) m ^ 2 • fomFixed A b x₀ (m + 1) := by
  set h := arnoldiCoeff A (v₁ A b x₀) with hdef
  have hRm1 := isUnit_R_of_fomDefined A b x₀ hm hH
  have hGF := ρG_le_ρF A b x₀ hm hH hRm1
  have ha : 0 < ρG A b x₀ (m + 1) := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
  have hf : 0 < ρF A b x₀ (m + 1) := lt_of_lt_of_le ha hGF
  have hF0 : b - op A (fomFixed A b x₀ (m + 1)) ≠ 0 := norm_ne_zero_iff.1 (ne_of_gt hf)
  have hcne : ‖c h m‖ ≠ 0 := norm_ne_zero_iff.2 (givensC_ne_zero_of_fomDefined A b x₀ hm hH)
  have hratio : ρG A b x₀ (m + 1) ^ 2 / ρF A b x₀ (m + 1) ^ 2 = c h m ^ 2 := by
    rw [ρF_eq_div_norm_c A b x₀ hm hH, div_pow, div_div_eq_mul_div, ← hdef]
    rw [show ‖c h m‖ ^ 2 = c h m ^ 2 by rw [Real.norm_eq_abs, sq_abs]]
    field_simp
  have hcs : 1 - c h m ^ 2 = s h m ^ 2 := by
    have := equation_6_35 h (givensRho_ne_zero_of_fomDefined A b x₀ hm hH)
    linarith
  have hcomb := Krylov.minRes_eq_combination
    (gmresFixed_isMinResidualIterate_of_lt A b x₀ (by omega))
    (gmresFixed_isMinResidualIterate A b x₀ hm hRm1) (fomFixed_isGalerkin A b x₀ hm hH)
    (injective_op_of_isUnit hA) hF0
  rw [hcomb, hratio, hcs]
  norm_num

/-- For $p + q = 1$, $u - A(pv + qw) = p(u - Av) + q(u - Aw)$; this identity gives (6.75) from
(6.74). -/
private theorem residual_combination {N : ℕ}
    (Aop : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N))
    (u v w : EuclideanSpace ℝ (Fin N)) {p q : ℝ} (hpq : p + q = 1) :
    u - Aop (p • v + q • w) = p • (u - Aop v) + q • (u - Aop w) := by
  rw [map_add, map_smul, map_smul]
  match_scalars <;> linarith

/-- **Equation (6.75)** of [saad2003iterative]. Let $A$ be nonsingular,
$m + 1 \le \operatorname{grade}(v_1)$, let $H_{m+1}$ be nonsingular, and let
$\rho^G_{m+1} \neq 0$. Then the residuals $r^G_m = b - Ax^G_m$ and $r^F_m = b - Ax^F_m$ satisfy
$$r^G_{m+1} = s_{m+1}^2 \, r^G_m + c_{m+1}^2 \, r^F_{m+1}.$$

**Reading.** Lean assumes a nonsingular system and FOM reduced matrix, a reached prefix and a
nonzero later GMRES residual. The source derives these identities after its triangular systems
without listing all these hypotheses.
-/
theorem equation_6_75 {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀)) (hA : IsUnit A)
    (hH : FOMDefined A b x₀ (m + 1)) (h0 : ρG A b x₀ (m + 1) ≠ 0) :
    b - op A (gmresFixed A b x₀ (m + 1))
      = s (arnoldiCoeff A (v₁ A b x₀)) m ^ 2 • (b - op A (gmresFixed A b x₀ m)) +
        c (arnoldiCoeff A (v₁ A b x₀)) m ^ 2 • (b - op A (fomFixed A b x₀ (m + 1))) := by
  have hcs := equation_6_35 (arnoldiCoeff A (v₁ A b x₀))
    (givensRho_ne_zero_of_fomDefined A b x₀ hm hH)
  rw [equation_6_74 A b x₀ hm hA hH h0]
  exact residual_combination (op A) b _ _ (by linarith)

/-! ### Problem P-6.14: Proposition 6.12 from (6.75) -/

/-- **Problem P-6.14** of [saad2003iterative]. Let $A$ be nonsingular,
$m + 1 \le \operatorname{grade}(v_1)$, let $H_{m+1}$ be nonsingular, and let
$\rho^G_{m+1} \neq 0$. Then the two residuals on the right of (6.75) are orthogonal,
$(r^G_m, r^F_{m+1}) = 0$, and so
$$(\rho^G_{m+1})^2 = s_{m+1}^4 (\rho^G_m)^2 + c_{m+1}^4 (\rho^F_{m+1})^2.$$

**Reading.** Lean assumes a nonsingular system and FOM reduced matrix, a reached prefix and a
nonzero later GMRES residual. The source derives these identities after its triangular systems
without listing all these hypotheses.
-/
theorem problem_6_14 {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀)) (hA : IsUnit A)
    (hH : FOMDefined A b x₀ (m + 1)) (h0 : ρG A b x₀ (m + 1) ≠ 0) :
    inner ℝ (b - op A (gmresFixed A b x₀ m)) (b - op A (fomFixed A b x₀ (m + 1))) = 0 ∧
      ρG A b x₀ (m + 1) ^ 2
        = s (arnoldiCoeff A (v₁ A b x₀)) m ^ 4 * ρG A b x₀ m ^ 2 +
          c (arnoldiCoeff A (v₁ A b x₀)) m ^ 4 * ρF A b x₀ (m + 1) ^ 2 := by
  have hG := gmresFixed_isMinResidualIterate_of_lt A b x₀ (show m < grade A (v₁ A b x₀) by omega)
  have hF := fomFixed_isGalerkin A b x₀ hm hH
  have horth : inner ℝ (b - op A (gmresFixed A b x₀ m))
      (b - op A (fomFixed A b x₀ (m + 1))) = 0 :=
    IsPetrovGalerkin.inner_residual_eq_zero hF (Krylov.residual_mem_subspace_succ hG.mem)
  refine ⟨horth, ?_⟩
  have horth' : inner ℝ (s (arnoldiCoeff A (v₁ A b x₀)) m ^ 2 •
      (b - op A (gmresFixed A b x₀ m)))
      (c (arnoldiCoeff A (v₁ A b x₀)) m ^ 2 • (b - op A (fomFixed A b x₀ (m + 1))))
      = (0 : ℝ) := by
    rw [real_inner_smul_left, real_inner_smul_right, horth, mul_zero, mul_zero]
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth'
  rw [← equation_6_75 A b x₀ hm hA hH h0, norm_smul, norm_smul,
    Real.norm_of_nonneg (sq_nonneg (s (arnoldiCoeff A (v₁ A b x₀)) m)),
    Real.norm_of_nonneg (sq_nonneg (c (arnoldiCoeff A (v₁ A b x₀)) m))] at hpy
  nlinarith [hpy]

/-! ### Problem P-6.13: $x^G_m = x^F_m$ forces both to be exact -/

/-- **Problem P-6.13** of [saad2003iterative]. Let $m + 1 \le \operatorname{grade}(v_1)$, let
$H_{m+1}$ be nonsingular, and let $x^G_{m+1} = x^F_{m+1}$. Then both approximations are exact:
$$b - Ax^G_{m+1} = 0 \quad \text{and} \quad b - Ax^F_{m+1} = 0.$$

The statement does not need $A$ to be nonsingular. -/
theorem problem_6_13 {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀)) (hH : FOMDefined A b x₀ (m + 1))
    (heq : gmresFixed A b x₀ (m + 1) = fomFixed A b x₀ (m + 1)) :
    b - op A (gmresFixed A b x₀ (m + 1)) = 0 ∧ b - op A (fomFixed A b x₀ (m + 1)) = 0 := by
  have hRm1 := isUnit_R_of_fomDefined A b x₀ hm hH
  have hcne : ‖c (arnoldiCoeff A (v₁ A b x₀)) m‖ ≠ 0 :=
    norm_ne_zero_iff.2 (givensC_ne_zero_of_fomDefined A b x₀ hm hH)
  have hdiv := ρF_eq_div_norm_c A b x₀ hm hH
  have hG0 : ρG A b x₀ (m + 1) = 0 := by
    by_contra h0
    have hFG : ρF A b x₀ (m + 1) = ρG A b x₀ (m + 1) :=
      congrArg (fun x => ‖b - op A x‖) heq.symm
    rw [hFG, eq_div_iff hcne] at hdiv
    have hc1 : ‖c (arnoldiCoeff A (v₁ A b x₀)) m‖ = 1 :=
      mul_left_cancel₀ h0 (by rw [mul_one]; exact hdiv)
    have hs0 : s (arnoldiCoeff A (v₁ A b x₀)) m = 0 := by
      have hcs := equation_6_35 (arnoldiCoeff A (v₁ A b x₀))
        (givensRho_ne_zero_of_fomDefined A b x₀ hm hH)
      have hc2 : c (arnoldiCoeff A (v₁ A b x₀)) m ^ 2 = 1 := by
        rw [show c (arnoldiCoeff A (v₁ A b x₀)) m ^ 2
            = ‖c (arnoldiCoeff A (v₁ A b x₀)) m‖ ^ 2 by rw [Real.norm_eq_abs, sq_abs], hc1]
        norm_num
      nlinarith
    have : ρG A b x₀ (m + 1) = 0 := by
      rw [ρG_eq_norm_gamma A b x₀ hm hRm1, gamma_succ, hs0, neg_zero, zero_mul, norm_zero]
    exact h0 this
  have hF0 : ρF A b x₀ (m + 1) = 0 := by rw [hdiv, hG0, zero_div]
  exact ⟨norm_eq_zero.1 hG0, norm_eq_zero.1 hF0⟩

/-! ### Proposition 6.17 (Brown) and Problem P-6.9 -/

/-- Let $A$ be nonsingular, $m + 1 \le \operatorname{grade}(v_1)$ and $\rho^G_{m+1} \neq 0$. Then a
Galerkin iterate at step $m + 1$ exists if and only if $H_{m+1}$ is nonsingular. -/
private theorem exists_galerkin_iff {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀)) (hA : IsUnit A)
    (h0 : ρG A b x₀ (m + 1) ≠ 0) :
    (∃ x, Krylov.IsGalerkinIterate (op A) b x₀ (m + 1) x) ↔ FOMDefined A b x₀ (m + 1) := by
  refine ⟨fun ⟨xF, hF⟩ => ?_, fun hH => ⟨_, fomFixed_isGalerkin A b x₀ hm hH⟩⟩
  have hG := gmresFixed_isMinResidualIterate A b x₀ hm (isUnit_R_of_isUnit A b x₀ hA hm)
  have hkey := Krylov.IsGalerkinIterate.norm_residual_eq_div_norm_givensC
    (by rw [← grade_v₁]; exact hm) hF hG
  have hcne : Krylov.givensC (Arnoldi.coeff (op A) (r₀ A b x₀)) m ≠ 0 := by
    intro hc
    rw [hc, norm_zero, div_zero] at hkey
    exact h0 (le_antisymm (by rw [← hkey]; exact hG.min xF hF.mem) (norm_nonneg _))
  rw [FOMDefined, H_v₁]
  exact (Krylov.isUnit_hessenbergSq_iff_givensC_ne_zero (by rw [← grade_v₁]; exact hm)).2 hcne

/-- **Proposition 6.17** of [saad2003iterative] (Brown) and **Problem P-6.9** of
[saad2003iterative]. Let $A$ be nonsingular, $m + 1 \le \operatorname{grade}(v_1)$ and
$\rho^G_{m+1} \neq 0$. Then GMRES makes no progress at step $m + 1$ if and only if FOM breaks
down there:
$$x^G_{m+1} = x^G_m \iff H_{m+1} \text{ is singular}.$$

**Reading.** The hypothesis $\rho^G_{m+1} \neq 0$ is explicit, because the proof needs it. -/
theorem proposition_6_17 {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀)) (hA : IsUnit A)
    (h0 : ρG A b x₀ (m + 1) ≠ 0) :
    gmresFixed A b x₀ (m + 1) = gmresFixed A b x₀ m ↔ ¬ FOMDefined A b x₀ (m + 1) := by
  have hG := gmresFixed_isMinResidualIterate_of_lt A b x₀ (show m < grade A (v₁ A b x₀) by omega)
  have hG' := gmresFixed_isMinResidualIterate A b x₀ hm (isUnit_R_of_isUnit A b x₀ hA hm)
  have hbb := Krylov.norm_residual_minRes_eq_iff_not_exists_galerkin hG hG'
    (norm_ne_zero_iff.1 h0) (by rw [← grade_v₁]; exact hm)
  rw [← exists_galerkin_iff A b x₀ hm hA h0, ← hbb]
  constructor
  · intro heq
    rw [heq]
  · intro heq
    obtain ⟨z, -, huniq⟩ :=
      Krylov.existsUnique_isMinResidualIterate_of_injective (injective_op_of_isUnit hA) b x₀ (m + 1)
    have hGm : Krylov.IsMinResidualIterate (op A) b x₀ (m + 1) (gmresFixed A b x₀ m) := by
      refine ⟨Krylov.subspace_mono (op A) (b - op A x₀) (Nat.le_succ m) hG.mem, fun y hy => ?_⟩
      rw [← heq]
      exact hG'.min y hy
    rw [huniq _ hG', huniq _ hGm]

/-! ### Lemma 6.16 (Freund) and (6.69)–(6.73) -/

/-- **Equation (6.70)** of [saad2003iterative]. Let $h$ be a real coefficient function,
$t \in \mathbb{R}$ and $m \ge 0$. Then the last entry of $g_{m+1}$, for $\beta = t$, is
$$c_{m+1} \gamma_{m+1}.$$
-/
theorem equation_6_70 (h : ℕ → ℕ → ℝ) (t : ℝ) (m : ℕ) :
    g h t (m + 1) (Fin.last m) = c h m * γ h t m := by
  rw [g_apply, Fin.val_last, Krylov.gvec]
  simp

/-- **Equation (6.71)** of [saad2003iterative]. Let $m + 1 \le \operatorname{grade}(v_1)$ and let
$H_{m+1}$ be nonsingular. Then the last diagonal entry of $R_{m+1}$ is
$$r_{m+1,m+1} = \frac{\xi_{m+1}}{c_{m+1}}.$$
-/
theorem equation_6_71 {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀)) (hH : FOMDefined A b x₀ (m + 1)) :
    R (arnoldiCoeff A (v₁ A b x₀)) (m + 1) (Fin.last m) (Fin.last m)
      = ξ (arnoldiCoeff A (v₁ A b x₀)) (m + 1) / c (arnoldiCoeff A (v₁ A b x₀)) m := by
  have hξ : ξ (arnoldiCoeff A (v₁ A b x₀)) (m + 1)
      = Krylov.rotated (arnoldiCoeff A (v₁ A b x₀)) m m m := by rw [ξ, Nat.add_sub_cancel]
  have hξ0 : Krylov.rotated (arnoldiCoeff A (v₁ A b x₀)) m m m ≠ 0 := by
    have := ξ_ne_zero_of_fomDefined A b x₀ hm hH
    rwa [hξ] at this
  rw [R_apply, Fin.val_last, Krylov.rotated_succ_self, hξ,
    show c (arnoldiCoeff A (v₁ A b x₀)) m = Krylov.givensC (arnoldiCoeff A (v₁ A b x₀)) m from
      rfl,
    Krylov.givensC, div_div_eq_mul_div, eq_div_iff hξ0]
  ring

/-- The core of Lemma 6.16 for the Givens data: if $R_{m+1} y = g_{m+1}$ and $R_m y' = g_m$, then
$y - (y'; 0) = c_{m+1}^2 (\tilde y_{m+1} - (y'; 0))$. -/
private theorem sub_snoc_eq_smul (h : ℕ → ℕ → ℝ) (hh : ∀ i j : ℕ, j + 1 < i → h i j = 0)
    (t : ℝ) {m : ℕ} (hρ : Krylov.givensRho h m ≠ 0)
    (hRt : IsUnit (Rtilde h (m + 1))) (y : Fin (m + 1) → ℝ) (yp : Fin m → ℝ)
    (hy : R h (m + 1) *ᵥ y = g h t (m + 1)) (hyp : R h m *ᵥ yp = g h t m) :
    y - (Fin.snoc yp (0 : ℝ) : Fin (m + 1) → ℝ)
      = Krylov.givensC h m ^ 2 •
        (ytilde h t (m + 1) - (Fin.snoc yp (0 : ℝ) : Fin (m + 1) → ℝ)) := by
  have hzlast : (Fin.snoc yp (0 : ℝ) : Fin (m + 1) → ℝ) (Fin.last m) = 0 := Fin.snoc_last _ _
  have hRz := R_mulVec_snoc h hh t yp hyp
  have hρ' : Krylov.rotated h (m + 1) m m ≠ 0 := by
    rw [Krylov.rotated_succ_self]
    simpa using hρ
  have hcdef : Krylov.givensC h m =
      Krylov.rotated h m m m / Krylov.rotated h (m + 1) m m := by
    rw [Krylov.rotated_succ_self, Krylov.givensC]
  have hgv : Krylov.gvec h t m = Krylov.givensC h m * Krylov.gamma h t m := by
    rw [Krylov.gvec]
    simp
  have hRtz : Rtilde h (m + 1) *ᵥ (Fin.snoc yp (0 : ℝ) : Fin (m + 1) → ℝ)
      = R h (m + 1) *ᵥ (Fin.snoc yp (0 : ℝ) : Fin (m + 1) → ℝ) := by
    rw [R_mulVec_eq_Rtilde_mulVec_add h hh m _, hzlast, mul_zero, Pi.single_zero, add_zero]
  have hu : R h (m + 1) *ᵥ (y - (Fin.snoc yp (0 : ℝ) : Fin (m + 1) → ℝ))
      = Pi.single (Fin.last m) (Krylov.gvec h t m) := by
    rw [Matrix.mulVec_sub, hy, hRz]
    abel
  have hw : Rtilde h (m + 1) *ᵥ
      (ytilde h t (m + 1) - (Fin.snoc yp (0 : ℝ) : Fin (m + 1) → ℝ))
      = Pi.single (Fin.last m) (Krylov.gamma h t m) := by
    rw [Matrix.mulVec_sub, ytilde, Matrix.mulVec_nonsing_inv_mulVec hRt, hRtz, hRz]
    funext i
    rcases eq_or_ne i (Fin.last m) with rfl | hi
    · rw [Pi.sub_apply, Pi.sub_apply, gtilde_last, g_apply, Fin.val_last, Pi.single_eq_same,
        Pi.single_eq_same]
      ring
    · obtain ⟨i', rfl⟩ := Fin.exists_castSucc_eq.2 hi
      rw [Pi.sub_apply, Pi.sub_apply, gtilde_castSucc, g_apply, Fin.val_castSucc,
        Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hi]
      ring
  have hulast : Krylov.rotated h (m + 1) m m *
      (y - (Fin.snoc yp (0 : ℝ) : Fin (m + 1) → ℝ)) (Fin.last m)
      = Krylov.givensC h m * Krylov.gamma h t m := by
    have hlast := congrFun hu (Fin.last m)
    simp only [Matrix.mulVec, dotProduct, Pi.single_eq_same] at hlast
    rw [Fin.sum_univ_castSucc] at hlast
    have hz : ∀ j : Fin m, R h (m + 1) (Fin.last m) j.castSucc *
        (y - (Fin.snoc yp (0 : ℝ) : Fin (m + 1) → ℝ)) j.castSucc = 0 := by
      intro j
      rw [R_apply, Fin.val_last, Fin.val_castSucc,
        Krylov.rotated_eq_zero_of_lt h (Matrix.isUpperHessenberg_iff_nat.2 hh)
            (m + 1) m (j : ℕ) (by omega) j.isLt, zero_mul]
    rw [Finset.sum_congr rfl fun j _ => hz j, Finset.sum_const_zero, zero_add, R_apply,
      Fin.val_last] at hlast
    rw [hlast, hgv]
  have hentry : Krylov.gvec h t m -
      (Krylov.rotated h (m + 1) m m - Krylov.rotated h m m m) *
        (y - (Fin.snoc yp (0 : ℝ) : Fin (m + 1) → ℝ)) (Fin.last m)
      = Krylov.givensC h m ^ 2 * Krylov.gamma h t m := by
    have hxi : Krylov.rotated h m m m
        = Krylov.givensC h m * Krylov.rotated h (m + 1) m m := by
      rw [hcdef]
      field_simp
    rw [hgv, hxi]
    linear_combination (Krylov.givensC h m - 1) * hulast
  have hRtu : Rtilde h (m + 1) *ᵥ (y - (Fin.snoc yp (0 : ℝ) : Fin (m + 1) → ℝ))
      = Pi.single (Fin.last m) (Krylov.givensC h m ^ 2 * Krylov.gamma h t m) := by
    have hsplit := R_mulVec_eq_Rtilde_mulVec_add h hh m
      (y - (Fin.snoc yp (0 : ℝ) : Fin (m + 1) → ℝ))
    rw [hu, ← Krylov.rotated_succ_self h m] at hsplit
    funext i
    rcases eq_or_ne i (Fin.last m) with rfl | hi
    · have hval := congrFun hsplit (Fin.last m)
      rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_same] at hval
      rw [Pi.single_eq_same, ← hentry]
      linarith [hval]
    · have hval := congrFun hsplit i
      rw [Pi.add_apply, Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hi, add_zero] at hval
      rw [Pi.single_eq_of_ne hi, ← hval]
  refine Matrix.mulVec_injective_iff_isUnit.2 hRt ?_
  rw [hRtu, Matrix.mulVec_smul, hw]
  funext i
  rcases eq_or_ne i (Fin.last m) with rfl | hi
  · rw [Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same, smul_eq_mul]
  · rw [Pi.smul_apply, Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hi, smul_eq_mul, mul_zero]

/-- **Lemma 6.16** of [saad2003iterative] (Freund), equation (6.69). Let
$m + 1 \le \operatorname{grade}(v_1)$ and let $H_{m+1}$ be nonsingular. Then the GMRES
coordinates $y_m = R_m^{-1} g_m$ and the vector $\tilde y_{m+1} = \tilde R_{m+1}^{-1} \tilde
g_{m+1}$ satisfy
$$y_{m+1} - \begin{bmatrix} y_m \\ 0 \end{bmatrix}
  = c_{m+1}^2 \left( \tilde y_{m+1} - \begin{bmatrix} y_m \\ 0 \end{bmatrix} \right).$$

**Reading.** The hypothesis that $H_{m+1}$ is nonsingular is explicit, because the proof needs
it.

The lemma is about coordinates, not approximations, so it is proved here by the book's
computation (6.72)–(6.73): $\tilde R_{m+1}$ and $R_{m+1}$ differ only in the entry $(m+1, m+1)$,
where the former has $\xi_{m+1}$ and the latter $\rho_{m+1} = \xi_{m+1} / c_{m+1}$.

**Reading.** Lean explicitly assumes the prefix is reached and the FOM reduced matrix is
nonsingular. The source uses these conditions in the triangular solves without listing them in the
statement.
-/
theorem lemma_6_16 {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀))
    (hH : FOMDefined A b x₀ (m + 1)) :
    gmresY A b x₀ (m + 1) - (Fin.snoc (gmresY A b x₀ m) (0 : ℝ) : Fin (m + 1) → ℝ)
      = c (arnoldiCoeff A (v₁ A b x₀)) m ^ 2 •
        (ytilde (arnoldiCoeff A (v₁ A b x₀)) (β A b x₀) (m + 1) -
          (Fin.snoc (gmresY A b x₀ m) (0 : ℝ) : Fin (m + 1) → ℝ)) := by
  have hy := mulVec_R_gmresY A b x₀ (isUnit_R_of_fomDefined A b x₀ hm hH)
  have hyp := mulVec_R_gmresY A b x₀
    (isUnit_R_of_lt_grade A b x₀ (show m < grade A (v₁ A b x₀) by omega))
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hy hyp
  exact sub_snoc_eq_smul (arnoldiCoeff A (v₁ A b x₀)) (arnoldiCoeff_v₁_eq_zero_of_lt A b x₀)
    (β A b x₀) (givensRho_ne_zero_of_fomDefined A b x₀ hm hH)
    (isUnit_Rtilde_of_fomDefined A b x₀ hm hH) _ _ hy hyp

end BookResultsRelations

/-!
### Section 6.5.8: residual smoothing

Residual smoothing turns a sequence of approximations $x^O_m$ with residuals $r^O_m$ into a sequence
$(x^S_m, r^S_m)$ whose residual norms do not increase. This part is over $\mathbb{R}$, as in the
book.
-/

section Smoothing

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin n)

/-! ### Algorithm 6.14 and QMRS -/

/-- Algorithm 6.14 of [saad2003iterative], line 3: for the previous smoothed residual
$s = r^S_{m-1}$ and the new residual $r = r^O_m$,
$$\eta_m = -\frac{(r^S_{m-1}, r^O_m - r^S_{m-1})}{\|r^O_m - r^S_{m-1}\|_2^2},$$
which is $0$ when $r^O_m = r^S_{m-1}$. The book's inner product $(x, y)$ is `inner ℝ y x`.

**Reading.** The original approximations and residuals are independent inputs to the recurrence; the
residual-consistency theorem separately ties them to a system. At equal residuals Lean uses zero for
the undefined quotient, leaving the smoothed state fixed.
-/
noncomputable def smoothEta (s r : 𝔼) : ℝ := -inner ℝ (r - s) s / ‖r - s‖ ^ 2

/-- The coefficient $\eta_m$ of Algorithm 6.14 is the residual-minimizing smoothing coefficient
`Krylov.smoothingCoeff` of the backbone.

**Reading.** The original approximations and residuals are independent inputs to the recurrence; the
residual-consistency theorem separately ties them to a system. At equal residuals Lean uses zero for
the undefined quotient, leaving the smoothed state fixed.
-/
theorem smoothEta_eq (s r : 𝔼) : smoothEta s r = Krylov.smoothingCoeff s r := by
  rw [smoothEta, Krylov.smoothingCoeff, inner_neg_right]
  simp [RCLike.ofReal_real_eq_id]

/-- **Algorithm 6.14** of [saad2003iterative] (minimal residual smoothing, Weiss). From sequences
$x^O_m$ and $r^O_m$ of vectors of $\mathbb{R}^n$, it computes the pairs $(x^S_m, r^S_m)$ with
$x^S_0 = x^O_0$, $r^S_0 = r^O_0$ and
$$x^S_m = x^S_{m-1} + \eta_m (x^O_m - x^S_{m-1}), \qquad
  r^S_m = r^S_{m-1} + \eta_m (r^O_m - r^S_{m-1}),$$
where $\eta_m$ is the coefficient of line 3 (`SaadSparse.Chapter06.smoothEta`) for $r^S_{m-1}$
and $r^O_m$.

The two input sequences are independent arguments. If $r^O_m = b - Ax^O_m$ for all $m$, then
$r^S_m = b - Ax^S_m$ (`SaadSparse.Chapter06.mrs_eq`).

**Reading.** The original approximations and residuals are independent inputs to the recurrence; the
residual-consistency theorem separately ties them to a system. At equal residuals Lean uses zero for
the undefined quotient, leaving the smoothed state fixed.
-/
noncomputable def mrs (xO rO : ℕ → 𝔼) : ℕ → 𝔼 × 𝔼
  | 0 => (xO 0, rO 0)
  | m + 1 =>
    let p := mrs xO rO m
    let η := smoothEta p.2 (rO (m + 1))
    (p.1 + η • (xO (m + 1) - p.1), p.2 + η • (rO (m + 1) - p.2))

/-- The smoothed approximations $x^S_m$ of Algorithm 6.14.

**Reading.** The original approximations and residuals are independent inputs to the recurrence; the
residual-consistency theorem separately ties them to a system. At equal residuals Lean uses zero for
the undefined quotient, leaving the smoothed state fixed.
-/
noncomputable abbrev mrsX (xO rO : ℕ → 𝔼) (m : ℕ) : 𝔼 := (mrs xO rO m).1

/-- The smoothed residuals $r^S_m$ of Algorithm 6.14.

**Reading.** The original approximations and residuals are independent inputs to the recurrence; the
residual-consistency theorem separately ties them to a system. At equal residuals Lean uses zero for
the undefined quotient, leaving the smoothed state fixed.
-/
noncomputable abbrev mrsR (xO rO : ℕ → 𝔼) (m : ℕ) : 𝔼 := (mrs xO rO m).2

/-- **Algorithm 6.14** of [saad2003iterative], line 3. The coefficient $\eta_{m+1}$ of step $m + 1$,
computed from $r^S_m$ and $r^O_{m+1}$.

The Lean value `mrsEta xO rO m` is the book's $\eta_{m+1}$.

**Reading.** The original approximations and residuals are independent inputs to the recurrence; the
residual-consistency theorem separately ties them to a system. At equal residuals Lean uses zero for
the undefined quotient, leaving the smoothed state fixed.
-/
noncomputable abbrev mrsEta (xO rO : ℕ → 𝔼) (m : ℕ) : ℝ :=
  smoothEta (mrsR xO rO m) (rO (m + 1))

/-- $x^S_0 = x^O_0$. -/
theorem mrsX_zero (xO rO : ℕ → 𝔼) : mrsX xO rO 0 = xO 0 := rfl

/-- $r^S_0 = r^O_0$. -/
theorem mrsR_zero (xO rO : ℕ → 𝔼) : mrsR xO rO 0 = rO 0 := rfl

/-- $x^S_{m+1} = x^S_m + \eta_{m+1} (x^O_{m+1} - x^S_m)$.

**Reading.** The original approximations and residuals are independent inputs to the recurrence; the
residual-consistency theorem separately ties them to a system. At equal residuals Lean uses zero for
the undefined quotient, leaving the smoothed state fixed.
-/
theorem mrsX_succ (xO rO : ℕ → 𝔼) (m : ℕ) :
    mrsX xO rO (m + 1) = mrsX xO rO m + mrsEta xO rO m • (xO (m + 1) - mrsX xO rO m) := rfl

/-- $r^S_{m+1} = r^S_m + \eta_{m+1} (r^O_{m+1} - r^S_m)$.

**Reading.** The original approximations and residuals are independent inputs to the recurrence; the
residual-consistency theorem separately ties them to a system. At equal residuals Lean uses zero for
the undefined quotient, leaving the smoothed state fixed.
-/
theorem mrsR_succ (xO rO : ℕ → 𝔼) (m : ℕ) :
    mrsR xO rO (m + 1) = mrsR xO rO m + mrsEta xO rO m • (rO (m + 1) - mrsR xO rO m) := rfl

/-- The scale factors of QMRS (Section 6.5.8): $\tau_0 = \rho_0$ and
$$\frac{1}{\tau_m^2} = \frac{1}{\tau_{m-1}^2} + \frac{1}{\rho_m^2}, \qquad \rho_j =
  \|r^O_j\|_2,$$
where $\tau_m \ge 0$ and $1/0 = 0$.

**Reading.** Lean extends the reciprocal and normalization formulas to zero denominators by
totalized division. The source recurrences for the scale are interpreted with nonzero norms. The
consistency between an input approximation and residual is separate.
-/
noncomputable def qmrsTau (rO : ℕ → 𝔼) : ℕ → ℝ
  | 0 => ‖rO 0‖
  | m + 1 => Real.sqrt (1 / (1 / qmrsTau rO m ^ 2 + 1 / ‖rO (m + 1)‖ ^ 2))

/-- The coefficient of QMRS in step $m + 1$: $\eta_{m+1} = \tau_m^2 / (\tau_m^2 + \rho_{m+1}^2)$.

**Reading.** Lean extends the reciprocal and normalization formulas to zero denominators by
totalized division. The source recurrences for the scale are interpreted with nonzero norms. The
consistency between an input approximation and residual is separate.
-/
noncomputable def qmrsEta (rO : ℕ → 𝔼) (m : ℕ) : ℝ :=
  qmrsTau rO m ^ 2 / (qmrsTau rO m ^ 2 + ‖rO (m + 1)‖ ^ 2)

/-- **Section 6.5.8** of [saad2003iterative], **QMRS** (quasi-minimal residual smoothing). Algorithm
6.14 with the coefficient $\eta_m$ replaced by $\tau_{m-1}^2 / (\tau_{m-1}^2 + \rho_m^2)$, where
$\rho_m = \|r^O_m\|_2$ and $\tau_m$ are the scale factors of `SaadSparse.Chapter06.qmrsTau`. It
starts from $(x^O_0, r^O_0)$.

**Reading.** Lean extends the reciprocal and normalization formulas to zero denominators by
totalized division. The source recurrences for the scale are interpreted with nonzero norms. The
consistency between an input approximation and residual is separate.
-/
noncomputable def qmrs (xO rO : ℕ → 𝔼) : ℕ → 𝔼 × 𝔼
  | 0 => (xO 0, rO 0)
  | m + 1 =>
    let p := qmrs xO rO m
    (p.1 + qmrsEta rO m • (xO (m + 1) - p.1), p.2 + qmrsEta rO m • (rO (m + 1) - p.2))

/-- QMRS starts from $(x^O_0, r^O_0)$. -/
theorem qmrs_zero (xO rO : ℕ → 𝔼) : qmrs xO rO 0 = (xO 0, rO 0) := rfl

/-- Step $m + 1$ of QMRS: $x_{m+1} = x_m + \eta_{m+1} (x^O_{m+1} - x_m)$ and
$r_{m+1} = r_m + \eta_{m+1} (r^O_{m+1} - r_m)$, with $\eta_{m+1} = \tau_m^2 / (\tau_m^2 +
\rho_{m+1}^2)$.

**Reading.** Lean extends the reciprocal and normalization formulas to zero denominators by
totalized division. The source recurrences for the scale are interpreted with nonzero norms. The
consistency between an input approximation and residual is separate.
-/
theorem qmrs_succ (xO rO : ℕ → 𝔼) (m : ℕ) :
    qmrs xO rO (m + 1) =
      ((qmrs xO rO m).1 + qmrsEta rO m • (xO (m + 1) - (qmrs xO rO m).1),
        (qmrs xO rO m).2 + qmrsEta rO m • (rO (m + 1) - (qmrs xO rO m).2)) := rfl

/-! ### The relation to `Krylov.mrs` -/

/-- Let $A \in \mathbb{R}^{n \times n}$ and $b \in \mathbb{R}^n$, and let $r^O_j = b - Ax^O_j$ for
all $j$. Then Algorithm 6.14 computes the minimal residual smoothing `Krylov.mrs` of the
backbone, $x^S_m$ = `Krylov.mrs (op A) b xO m`, and $r^S_m = b - Ax^S_m$. -/
theorem mrs_eq (A : Matrix (Fin n) (Fin n) ℝ) (b : 𝔼) (xO rO : ℕ → 𝔼)
    (hr : ∀ j, rO j = b - op A (xO j)) (m : ℕ) :
    mrsX xO rO m = Krylov.mrs (op A) b xO m ∧
      mrsR xO rO m = b - op A (Krylov.mrs (op A) b xO m) := by
  induction m with
  | zero => exact ⟨rfl, by rw [mrsR_zero, hr 0, Krylov.mrs]⟩
  | succ m ih =>
    obtain ⟨ihx, ihr⟩ := ih
    have hη : mrsEta xO rO m =
        Krylov.smoothingCoeff (b - op A (Krylov.mrs (op A) b xO m)) (b - op A (xO (m + 1))) := by
      rw [mrsEta, ihr, hr (m + 1), smoothEta_eq]
    have hx : mrsX xO rO (m + 1) = Krylov.mrs (op A) b xO (m + 1) := by
      rw [mrsX_succ, ihx, hη, Krylov.mrs]
    refine ⟨hx, ?_⟩
    rw [mrsR_succ, ihr, hη, hr (m + 1), Krylov.mrs]
    simp only [map_add, map_smul, map_sub]
    module

/-! ### Lemma 6.18 (Weiss) and (6.76)–(6.77) -/

/-- If $w$ is orthogonal to $r^O_0, \dots, r^O_m$, then $w$ is orthogonal to $r^S_m$, because the
smoothed residual is a linear combination of the original ones. -/
theorem inner_mrsR_eq_zero (xO rO : ℕ → 𝔼) (w : 𝔼) :
    ∀ m : ℕ, (∀ i ≤ m, inner ℝ w (rO i) = 0) → inner ℝ w (mrsR xO rO m) = 0 := by
  intro m
  induction m with
  | zero => intro h; rw [mrsR_zero]; exact h 0 le_rfl
  | succ m ih =>
    intro h
    rw [mrsR_succ, inner_add_right, real_inner_smul_right, inner_sub_right,
      ih fun i hi => h i (by omega), h (m + 1) le_rfl]
    ring

/-- **Equation (6.76)** of [saad2003iterative] (Lemma 6.18, Weiss). Let $r^S_m \neq 0$ and
$r^O_{m+1} \neq 0$ with $(r^O_{m+1}, r^S_m) = 0$. Then
$$\frac{1}{\|r^S_{m+1}\|_2^2} = \frac{1}{\|r^S_m\|_2^2} + \frac{1}{\|r^O_{m+1}\|_2^2}.$$

The proof specializes `Krylov.inv_sq_norm_smoothing`.

**Reading.** Lean states a one-step orthogonality condition. The reciprocal norm identity requires
both residuals used in the step to be nonzero. The coefficient formula alone also holds for zero
residuals under totalized division.
-/
theorem equation_6_76 (xO rO : ℕ → 𝔼) {m : ℕ} (h0 : mrsR xO rO m ≠ 0) (h1 : rO (m + 1) ≠ 0)
    (horth : inner ℝ (rO (m + 1)) (mrsR xO rO m) = 0) :
    1 / ‖mrsR xO rO (m + 1)‖ ^ 2 = 1 / ‖mrsR xO rO m‖ ^ 2 + 1 / ‖rO (m + 1)‖ ^ 2 := by
  have hkey := Krylov.inv_sq_norm_smoothing (𝕜 := ℝ) h0 h1 horth
  rw [mrsR_succ, mrsEta, smoothEta_eq]
  exact hkey

/-- **Equation (6.77)** of [saad2003iterative] (Lemma 6.18, Weiss). If $(r^O_{m+1}, r^S_m) = 0$,
then
$$\eta_{m+1} = \frac{\|r^S_m\|_2^2}{\|r^S_m\|_2^2 + \|r^O_{m+1}\|_2^2}.$$

No vector needs to be nonzero: if $r^S_m = r^O_{m+1} = 0$, then both sides are $0$.

**Reading.** Lean states a one-step orthogonality condition. The reciprocal norm identity requires
both residuals used in the step to be nonzero. The coefficient formula alone also holds for zero
residuals under totalized division.
-/
theorem equation_6_77 (xO rO : ℕ → 𝔼) {m : ℕ}
    (horth : inner ℝ (rO (m + 1)) (mrsR xO rO m) = 0) :
    mrsEta xO rO m
      = ‖mrsR xO rO m‖ ^ 2 / (‖mrsR xO rO m‖ ^ 2 + ‖rO (m + 1)‖ ^ 2) := by
  have hnum : inner ℝ (rO (m + 1) - mrsR xO rO m) (mrsR xO rO m) = -‖mrsR xO rO m‖ ^ 2 := by
    rw [inner_sub_left, horth, real_inner_self_eq_norm_sq]
    ring
  have hden : ‖rO (m + 1) - mrsR xO rO m‖ ^ 2
      = ‖mrsR xO rO m‖ ^ 2 + ‖rO (m + 1)‖ ^ 2 := by
    rw [norm_sub_sq_real, horth]
    ring
  rw [mrsEta, smoothEta, hnum, hden, neg_neg]

/-!
### Equations (6.78)–(6.79) and the QMRS identities

The smoothed residual and the QMRS residual satisfy the same recurrence once the weight is written
with the partial sums $\sum_{i \le j} 1/\rho_i^2$. One induction gives (6.79) and its QMRS analogue.
-/

/-- The scalar identity behind (6.79), for $S > 0$ and $\rho > 0$. -/
private theorem smul_combination_eq {S rho : ℝ} (hS : 0 < S) (hr : 0 < rho) (u v : 𝔼) :
    (1 - S⁻¹ / (S⁻¹ + rho)) • (S⁻¹ • u) + (S⁻¹ / (S⁻¹ + rho)) • v
      = (S + 1 / rho)⁻¹ • (u + (1 / rho) • v) := by
  have hS0 : S ≠ 0 := ne_of_gt hS
  have hr0 : rho ≠ 0 := ne_of_gt hr
  have hd : S⁻¹ + rho ≠ 0 := ne_of_gt (by have := inv_pos.2 hS; linarith)
  have hd2 : S + 1 / rho ≠ 0 := ne_of_gt (by have := one_div_pos.2 hr; linarith)
  have e1 : (1 - S⁻¹ / (S⁻¹ + rho)) * S⁻¹ = (S + 1 / rho)⁻¹ := by
    field_simp
    ring
  have e2 : S⁻¹ / (S⁻¹ + rho) = (S + 1 / rho)⁻¹ * (1 / rho) := by
    field_simp
    ring
  rw [smul_smul, e1, smul_add, smul_smul, e2]

private theorem sum_inv_sq_pos {rO : ℕ → 𝔼} {m : ℕ} (hr : ∀ j ≤ m, rO j ≠ 0) :
    (0 : ℝ) < ∑ j ∈ Finset.range (m + 1), 1 / ‖rO j‖ ^ 2 :=
  Finset.sum_pos (fun j hj => one_div_pos.2 (pow_pos
    (norm_pos_iff.2 (hr j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)))) 2)) ⟨0, by simp⟩

/-- The induction behind (6.79): a sequence that starts at $r^O_0$ and follows the smoothing
recurrence with the weights of Lemma 6.18 is the weighted average of the original residuals. -/
private theorem residual_eq_weighted (rO S : ℕ → 𝔼) (hS0 : S 0 = rO 0) {m : ℕ}
    (hr : ∀ j ≤ m, rO j ≠ 0)
    (hstep : ∀ j < m, S (j + 1) = S j +
      ((∑ i ∈ Finset.range (j + 1), 1 / ‖rO i‖ ^ 2)⁻¹ /
        ((∑ i ∈ Finset.range (j + 1), 1 / ‖rO i‖ ^ 2)⁻¹ + ‖rO (j + 1)‖ ^ 2)) •
        (rO (j + 1) - S j)) :
    S m = (∑ j ∈ Finset.range (m + 1), 1 / ‖rO j‖ ^ 2)⁻¹ •
      ∑ j ∈ Finset.range (m + 1), (1 / ‖rO j‖ ^ 2) • rO j := by
  induction m with
  | zero =>
    have hne : ‖rO 0‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 (hr 0 le_rfl))
    simp only [zero_add, Finset.range_one, Finset.sum_singleton]
    rw [hS0, smul_smul, inv_mul_cancel₀ (one_div_ne_zero hne), one_smul]
  | succ k ih =>
    have hrk : ∀ j ≤ k, rO j ≠ 0 := fun j hj => hr j (by omega)
    have hSpos := sum_inv_sq_pos hrk
    have hrpos : (0 : ℝ) < ‖rO (k + 1)‖ ^ 2 :=
      pow_pos (norm_pos_iff.2 (hr (k + 1) le_rfl)) 2
    have hcomb : ∀ (t : ℝ) (a v : 𝔼), a + t • (v - a) = (1 - t) • a + t • v := by
      intro t a v
      module
    rw [hstep k (by omega), ih hrk (fun j hj => hstep j (by omega)), hcomb,
      Finset.sum_range_succ (fun j => 1 / ‖rO j‖ ^ 2) (k + 1),
      Finset.sum_range_succ (fun j => (1 / ‖rO j‖ ^ 2) • rO j) (k + 1)]
    exact smul_combination_eq hSpos hrpos _ _

/-! ### The QMRS scale factors -/

/-- If $r^O_0, \dots, r^O_m$ are nonzero, then $\tau_m > 0$. -/
theorem qmrsTau_pos (rO : ℕ → 𝔼) {m : ℕ} (hr : ∀ j ≤ m, rO j ≠ 0) : 0 < qmrsTau rO m := by
  induction m with
  | zero => rw [qmrsTau]; exact norm_pos_iff.2 (hr 0 le_rfl)
  | succ k ih =>
    have hk := ih fun j hj => hr j (by omega)
    have hrpos : (0 : ℝ) < ‖rO (k + 1)‖ ^ 2 :=
      pow_pos (norm_pos_iff.2 (hr (k + 1) le_rfl)) 2
    rw [qmrsTau]
    refine Real.sqrt_pos.2 (one_div_pos.2 ?_)
    have : (0 : ℝ) < 1 / qmrsTau rO k ^ 2 := by positivity
    have : (0 : ℝ) < 1 / ‖rO (k + 1)‖ ^ 2 := by positivity
    linarith

/-- If $r^O_0, \dots, r^O_m$ are nonzero, then $1/\tau_m^2 = \sum_{j=0}^m 1/\rho_j^2$, the defining
relation of QMRS.

**Correction.** The summation index in the displayed recurrence is $i$, but the source prints
$1/\rho_j^2$ in each summand. Lean uses $1/\rho_i^2$ for the successive original residual norms and
requires them to be nonzero.
-/
theorem inv_qmrsTau_sq (rO : ℕ → 𝔼) {m : ℕ} (hr : ∀ j ≤ m, rO j ≠ 0) :
    1 / qmrsTau rO m ^ 2 = ∑ j ∈ Finset.range (m + 1), 1 / ‖rO j‖ ^ 2 := by
  induction m with
  | zero => rw [qmrsTau]; simp
  | succ k ih =>
    have hk := ih fun j hj => hr j (by omega)
    have hkpos := qmrsTau_pos rO fun j hj => hr j (Nat.le_succ_of_le hj)
    have hrpos : (0 : ℝ) < ‖rO (k + 1)‖ ^ 2 :=
      pow_pos (norm_pos_iff.2 (hr (k + 1) le_rfl)) 2
    have hsum : (0 : ℝ) < 1 / qmrsTau rO k ^ 2 + 1 / ‖rO (k + 1)‖ ^ 2 := by positivity
    rw [qmrsTau, Real.sq_sqrt (le_of_lt (one_div_pos.2 hsum)), one_div_one_div,
      Finset.sum_range_succ, ← hk]

/-- If $r^O_0, \dots, r^O_m$ are nonzero, then $\tau_m^2 = \big(\sum_{j=0}^m 1/\rho_j^2\big)^{-1}$.

**Correction.** The summation index in the displayed recurrence is $i$, but the source prints
$1/\rho_j^2$ in each summand. Lean uses $1/\rho_i^2$ for the successive original residual norms and
requires them to be nonzero.
-/
theorem qmrsTau_sq (rO : ℕ → 𝔼) {m : ℕ} (hr : ∀ j ≤ m, rO j ≠ 0) :
    qmrsTau rO m ^ 2 = (∑ j ∈ Finset.range (m + 1), 1 / ‖rO j‖ ^ 2)⁻¹ := by
  rw [← inv_qmrsTau_sq rO hr, one_div, inv_inv]

/-- **Equation (6.79)** of [saad2003iterative], for QMRS. If $r^O_0, \dots, r^O_m$ are nonzero, then
the QMRS residual is the weighted average of the original residuals:
$$r_m = \Big( \sum_{j=0}^m \frac{1}{\rho_j^2} \Big)^{-1} \sum_{j=0}^m \frac{1}{\rho_j^2} \,
  r^O_j, \qquad \rho_j = \|r^O_j\|_2.$$

The sums run from $j = 0$; see `SaadSparse.Chapter06.equation_6_79`.

**Correction.** The weighted sum includes the initial residual at index zero. The source prints both
sums starting at one. The Lean formulas assume nonzero original residuals.
-/
theorem qmrs_eq_6_79 (xO rO : ℕ → 𝔼) {m : ℕ} (hr : ∀ j ≤ m, rO j ≠ 0) :
    (qmrs xO rO m).2 = (∑ j ∈ Finset.range (m + 1), 1 / ‖rO j‖ ^ 2)⁻¹ •
      ∑ j ∈ Finset.range (m + 1), (1 / ‖rO j‖ ^ 2) • rO j := by
  refine residual_eq_weighted rO (fun j => (qmrs xO rO j).2) rfl hr fun j hj => ?_
  rw [qmrs_succ, qmrsEta, qmrsTau_sq rO fun i hi => hr i (by omega)]

/-- **Equation (6.78)** of [saad2003iterative], for QMRS. If $r^O_{m+1} \neq 0$, then with
$\rho = \|r^O_{m+1}\|_2$ the QMRS residual satisfies
$$r_{m+1} = \frac{\rho^2}{\rho^2 + \tau_m^2} \, r_m + \frac{\tau_m^2}{\rho^2 + \tau_m^2} \,
  r^O_{m+1}.$$

**Reading.** Lean makes the nonzero assumptions needed for the exact coefficient comparison
explicit. The QMRS weighted update uses its scalar from the reciprocal-norm recursion, while
agreement with MRS assumes the indicated orthogonality.
-/
theorem qmrs_eq_6_78 (xO rO : ℕ → 𝔼) {m : ℕ} (hr : rO (m + 1) ≠ 0) :
    (qmrs xO rO (m + 1)).2
      = (‖rO (m + 1)‖ ^ 2 / (‖rO (m + 1)‖ ^ 2 + qmrsTau rO m ^ 2)) • (qmrs xO rO m).2 +
        (qmrsTau rO m ^ 2 / (‖rO (m + 1)‖ ^ 2 + qmrsTau rO m ^ 2)) • rO (m + 1) := by
  have hrpos : (0 : ℝ) < ‖rO (m + 1)‖ ^ 2 := pow_pos (norm_pos_iff.2 hr) 2
  have hden : ‖rO (m + 1)‖ ^ 2 + qmrsTau rO m ^ 2 ≠ 0 := by positivity
  have he : qmrsEta rO m = qmrsTau rO m ^ 2 / (‖rO (m + 1)‖ ^ 2 + qmrsTau rO m ^ 2) := by
    rw [qmrsEta, add_comm (qmrsTau rO m ^ 2)]
  have he' : 1 - qmrsEta rO m
      = ‖rO (m + 1)‖ ^ 2 / (‖rO (m + 1)‖ ^ 2 + qmrsTau rO m ^ 2) := by
    rw [he]
    field_simp
    ring
  rw [qmrs_succ]
  simp only
  rw [show (qmrs xO rO m).2 + qmrsEta rO m • (rO (m + 1) - (qmrs xO rO m).2)
      = (1 - qmrsEta rO m) • (qmrs xO rO m).2 + qmrsEta rO m • rO (m + 1) by module, he', he]

/-! ### Algorithm 6.14 under the orthogonality hypothesis of Lemma 6.18 -/

/-- Let $r^O_0, \dots, r^O_m$ be nonzero, and let $(r^O_{j+1}, r^S_j) = 0$ for every $j < m$. Then
$1/\|r^S_m\|_2^2 = \sum_{j=0}^m 1/\rho_j^2$.

**Correction.** The summation index in the displayed recurrence is $i$, but the source prints
$1/\rho_j^2$ in each summand. Lean uses $1/\rho_i^2$ for the successive original residual norms and
requires them to be nonzero.
-/
theorem inv_sq_norm_mrsR (xO rO : ℕ → 𝔼) {m : ℕ} (hr : ∀ j ≤ m, rO j ≠ 0)
    (horth : ∀ j < m, inner ℝ (rO (j + 1)) (mrsR xO rO j) = 0) :
    1 / ‖mrsR xO rO m‖ ^ 2 = ∑ j ∈ Finset.range (m + 1), 1 / ‖rO j‖ ^ 2 := by
  induction m with
  | zero => rw [mrsR_zero]; simp
  | succ k ih =>
    have hrk : ∀ j ≤ k, rO j ≠ 0 := fun j hj => hr j (by omega)
    have hk := ih hrk fun j hj => horth j (by omega)
    have hne : mrsR xO rO k ≠ 0 := by
      intro h0
      have hpos : (0 : ℝ) < 1 / ‖mrsR xO rO k‖ ^ 2 := hk ▸ sum_inv_sq_pos hrk
      rw [h0, norm_zero] at hpos
      norm_num at hpos
    rw [equation_6_76 xO rO hne (hr (k + 1) le_rfl) (horth k (by omega)), hk,
      Finset.sum_range_succ (fun j => 1 / ‖rO j‖ ^ 2) (k + 1)]

/-- Let $r^O_0, \dots, r^O_m$ be nonzero, and let $(r^O_{j+1}, r^S_j) = 0$ for every $j < m$. Then
$\|r^S_m\|_2 = \tau_m$: the smoothed residual norms are the QMRS scale factors.

**Reading.** Lean makes the nonzero assumptions needed for the exact coefficient comparison
explicit. The QMRS weighted update uses its scalar from the reciprocal-norm recursion, while
agreement with MRS assumes the indicated orthogonality.
-/
theorem norm_mrsR_eq_qmrsTau (xO rO : ℕ → 𝔼) {m : ℕ} (hr : ∀ j ≤ m, rO j ≠ 0)
    (horth : ∀ j < m, inner ℝ (rO (j + 1)) (mrsR xO rO j) = 0) :
    ‖mrsR xO rO m‖ = qmrsTau rO m := by
  have h1 := inv_sq_norm_mrsR xO rO hr horth
  have h2 := inv_qmrsTau_sq rO hr
  have hne : ‖mrsR xO rO m‖ ≠ 0 := by
    intro h0
    have hpos : (0 : ℝ) < 1 / ‖mrsR xO rO m‖ ^ 2 := h1 ▸ sum_inv_sq_pos hr
    rw [h0] at hpos
    norm_num at hpos
  have hsq : ‖mrsR xO rO m‖ ^ 2 = qmrsTau rO m ^ 2 := by
    have h3 : (‖mrsR xO rO m‖ ^ 2)⁻¹ = (qmrsTau rO m ^ 2)⁻¹ := by
      rw [← one_div, ← one_div]
      exact h1.trans h2.symm
    exact inv_injective h3
  have hpos := qmrsTau_pos rO hr
  nlinarith [norm_nonneg (mrsR xO rO m), hpos, hsq]

/-- Section 6.5.8 of [saad2003iterative]. Let $r^O_0, \dots, r^O_m$ be nonzero, and let
$(r^O_{j+1}, r^S_j) = 0$ for every $j < m$. Then Algorithm 6.14 and QMRS give the same pair at
step $m$.

**Reading.** Lean makes the nonzero assumptions needed for the exact coefficient comparison
explicit. The QMRS weighted update uses its scalar from the reciprocal-norm recursion, while
agreement with MRS assumes the indicated orthogonality.
-/
theorem mrs_eq_qmrs (xO rO : ℕ → 𝔼) {m : ℕ} (hr : ∀ j ≤ m, rO j ≠ 0)
    (horth : ∀ j < m, inner ℝ (rO (j + 1)) (mrsR xO rO j) = 0) :
    mrs xO rO m = qmrs xO rO m := by
  induction m with
  | zero => rfl
  | succ k ih =>
    have hrk : ∀ j ≤ k, rO j ≠ 0 := fun j hj => hr j (by omega)
    have hk := ih hrk fun j hj => horth j (by omega)
    have hη : mrsEta xO rO k = qmrsEta rO k := by
      rw [equation_6_77 xO rO (horth k (by omega)), qmrsEta,
        norm_mrsR_eq_qmrsTau xO rO hrk fun j hj => horth j (by omega)]
    rw [qmrs_succ, ← hk]
    have hx : mrs xO rO (k + 1) =
        (mrsX xO rO k + mrsEta xO rO k • (xO (k + 1) - mrsX xO rO k),
          mrsR xO rO k + mrsEta xO rO k • (rO (k + 1) - mrsR xO rO k)) := rfl
    rw [hx, hη]

/-- **Equation (6.78)** of [saad2003iterative]. Let $r^O_0, \dots, r^O_{m+1}$ be nonzero, and let
$(r^O_{j+1}, r^S_j) = 0$ for every $j \le m$. Then with $\rho = \|r^O_{m+1}\|_2$ and
$\tau_m = \|r^S_m\|_2$,
$$r^S_{m+1} = \frac{\rho^2}{\rho^2 + \tau_m^2} \, r^S_m + \frac{\tau_m^2}{\rho^2 + \tau_m^2} \,
  r^O_{m+1}.$$

**Reading.** Lean makes the nonzero assumptions needed for the exact coefficient comparison
explicit. The QMRS weighted update uses its scalar from the reciprocal-norm recursion, while
agreement with MRS assumes the indicated orthogonality.
-/
theorem equation_6_78 (xO rO : ℕ → 𝔼) {m : ℕ} (hr : ∀ j ≤ m + 1, rO j ≠ 0)
    (horth : ∀ j < m + 1, inner ℝ (rO (j + 1)) (mrsR xO rO j) = 0) :
    mrsR xO rO (m + 1)
      = (‖rO (m + 1)‖ ^ 2 / (‖rO (m + 1)‖ ^ 2 + ‖mrsR xO rO m‖ ^ 2)) • mrsR xO rO m +
        (‖mrsR xO rO m‖ ^ 2 / (‖rO (m + 1)‖ ^ 2 + ‖mrsR xO rO m‖ ^ 2)) • rO (m + 1) := by
  have hrk : ∀ j ≤ m, rO j ≠ 0 := fun j hj => hr j (by omega)
  have hτ := norm_mrsR_eq_qmrsTau xO rO hrk fun j hj => horth j (by omega)
  have hq := qmrs_eq_6_78 xO rO (hr (m + 1) le_rfl)
  have h1 : mrsR xO rO (m + 1) = (qmrs xO rO (m + 1)).2 :=
    congrArg Prod.snd (mrs_eq_qmrs xO rO hr horth)
  have h2 : mrsR xO rO m = (qmrs xO rO m).2 :=
    congrArg Prod.snd (mrs_eq_qmrs xO rO hrk fun j hj => horth j (by omega))
  rw [h1, hq, ← h2, hτ]

/-- **Equation (6.79)** of [saad2003iterative]. Let $r^O_0, \dots, r^O_m$ be nonzero, and let
$(r^O_{j+1}, r^S_j) = 0$ for every $j < m$. Then the smoothed residual is the weighted average
$$r^S_m = \Big( \sum_{j=0}^m \frac{1}{\rho_j^2} \Big)^{-1} \sum_{j=0}^m \frac{r^O_j}{\rho_j^2},
  \qquad \rho_j = \|r^O_j\|_2.$$

**Correction.** The book prints both sums of (6.79) from $j = 1$. The identity that it combines
with (6.78), displayed just above as $1/\tau_j^2 = \sum_{i=0}^j 1/\rho_i^2$, starts at $0$, and
so does Algorithm 6.14, whose line 1 sets $r^S_0 = r^O_0$. At $m = 1$ the printed range would
give $r^S_1 = r^O_1$. The sums here run over $0, \dots, m$. -/
theorem equation_6_79 (xO rO : ℕ → 𝔼) {m : ℕ} (hr : ∀ j ≤ m, rO j ≠ 0)
    (horth : ∀ j < m, inner ℝ (rO (j + 1)) (mrsR xO rO j) = 0) :
    mrsR xO rO m = (∑ j ∈ Finset.range (m + 1), 1 / ‖rO j‖ ^ 2)⁻¹ •
      ∑ j ∈ Finset.range (m + 1), (1 / ‖rO j‖ ^ 2) • rO j := by
  rw [show mrsR xO rO m = (qmrs xO rO m).2 from
    congrArg Prod.snd (mrs_eq_qmrs xO rO hr horth)]
  exact qmrs_eq_6_79 xO rO hr

/-- **Lemma 6.18** of [saad2003iterative] (Weiss). Let $r^S_m \neq 0$ and $r^O_{m+1} \neq 0$ with
$(r^O_{m+1}, r^S_m) = 0$. Then the smoothed residual norms satisfy (6.76) and the coefficient
satisfies (6.77):
$$\frac{1}{\|r^S_{m+1}\|_2^2} = \frac{1}{\|r^S_m\|_2^2} + \frac{1}{\|r^O_{m+1}\|_2^2}, \qquad
  \eta_{m+1} = \frac{\|r^S_m\|_2^2}{\|r^S_m\|_2^2 + \|r^O_{m+1}\|_2^2}.$$

**Reading.** Lean states a one-step orthogonality condition. The reciprocal norm identity requires
both residuals used in the step to be nonzero. The coefficient formula alone also holds for zero
residuals under totalized division.
-/
theorem lemma_6_18 (xO rO : ℕ → 𝔼) {m : ℕ} (h0 : mrsR xO rO m ≠ 0)
    (h1 : rO (m + 1) ≠ 0)
    (horth : inner ℝ (rO (m + 1)) (mrsR xO rO m) = 0) :
    1 / ‖mrsR xO rO (m + 1)‖ ^ 2 = 1 / ‖mrsR xO rO m‖ ^ 2 + 1 / ‖rO (m + 1)‖ ^ 2 ∧
      mrsEta xO rO m
        = ‖mrsR xO rO m‖ ^ 2 / (‖mrsR xO rO m‖ ^ 2 + ‖rO (m + 1)‖ ^ 2) :=
  ⟨equation_6_76 xO rO h0 h1 horth, equation_6_77 xO rO horth⟩

/-!
### Section 6.5.8: QMRS applied to IOM or DIOM gives QGMRES or DQGMRES

The book says that this can easily be shown. Here it is proved from (6.47), (6.57) and (6.58). The
QMRS scale factor $\tau_m$ is the quasi-residual norm $|\gamma_{m+1}|$, the coefficient of step
$m + 1$ is $c_{m+1}^2$, and (6.58) is then the QMRS residual recurrence.
-/

section QMRSIOM

variable {A : Matrix (Fin n) (Fin n) ℝ} {b x₀ : EuclideanSpace ℝ (Fin n)}
  {u : ℕ → EuclideanSpace ℝ (Fin n)} {h : ℕ → ℕ → ℝ} {β : ℝ}

/-- **Section 6.5.8** of [saad2003iterative], QMRS applied to IOM. Let
$A \in \mathbb{R}^{n \times n}$ be nonsingular, $b, x_0 \in \mathbb{R}^n$ and
$\beta \in \mathbb{R}$. Let $v_1, v_2, \dots$ be unit vectors of $\mathbb{R}^n$ that satisfy
$A v_j = \sum_{i=1}^{j+1} h_{ij} v_i$ with an upper Hessenberg coefficient function $h$, and let
$b - Ax_0 = \beta v_1$. Let $\gamma_1, \dots, \gamma_{m+1}$ be nonzero, and let
$H_0, \dots, H_m$ be nonsingular. Then QMRS applied to the Galerkin approximations $x^I_j$ and
their residuals gives at step $m$ the QGMRES approximation $x_m$ and its residual $b - Ax_m$,
and its scale factor is $\tau_m = |\gamma_{m+1}|$.

On the incomplete orthogonalization basis the Galerkin approximation is IOM, so this is the
book's statement that QMRS applied to IOM or DIOM gives, in exact arithmetic, the same sequence
as QGMRES or DQGMRES. The hypothesis $\gamma_j \neq 0$ is the algorithm's own termination test;
it gives $c_j \neq 0$ and $s_j \neq 0$ through (6.57) and (6.47), and so makes $\tau_m$ and the
coefficients well defined. It is stated for $j \le m + 1$ and not for all $j$, which would be
impossible in finite dimension. The hypothesis on $H_j$ says that IOM is defined at every step.

**Reading.** Lean proves the identity for fixed IOM and QGMRES on a common Hessenberg relation, with
unit vectors, nonzero rotated residual components and nonsingular reduced systems. The source also
names the direct variants. It prints the cosine ratio with $\rho_m^2$ in the denominator. The
argument uses $\rho_m$ as in (6.57).
-/
theorem qmrs_iomOfBasis_eq_qgmres (hA : IsUnit A)
    (hu : Krylov.HessenbergRelation (op A) u h) (hr : b - op A x₀ = β • u 0)
    (hnorm : ∀ i, ‖u i‖ = 1) {m : ℕ} (hγ : ∀ j ≤ m, γ h β j ≠ 0)
    (hH : ∀ j ≤ m, IsUnit (Krylov.hessenbergSqOf h j)) :
    qmrs (fun j => iomOfBasis x₀ u h β j) (fun j => b - op A (iomOfBasis x₀ u h β j)) m
        = (qgmres x₀ u h β m, b - op A (qgmres x₀ u h β m)) ∧
      qmrsTau (fun j => b - op A (iomOfBasis x₀ u h β j)) m = ‖γ h β m‖ := by
  induction m with
  | zero =>
    have h0 : iomOfBasis x₀ u h β 0 = x₀ := iomOfBasis_zero x₀ u h β
    refine ⟨by rw [qmrs_zero, h0, qgmres_zero], ?_⟩
    rw [qmrsTau, h0, hr, norm_smul, hnorm 0, mul_one]
    rfl
  | succ m ih =>
    obtain ⟨ihq, ihτ⟩ := ih (fun j hj => hγ j (by omega)) (fun j hj => hH j (by omega))
    have hhh := hu.eq_zero_of_lt
    -- the four quantities of the book's computation
    have h57 : ‖γ h β (m + 1)‖
        = ‖c h m‖ * ‖b - op A (iomOfBasis x₀ u h β (m + 1))‖ := by
      have h := equation_6_57 hu hr (hnorm (m + 1)) (hH (m + 1) le_rfl)
      rwa [quasiResidualNorm] at h
    have h47 : ‖γ h β (m + 1)‖ = ‖s h m‖ * ‖γ h β m‖ := by
      rw [gamma_succ, norm_mul, norm_neg]
    have hγ1 : ‖γ h β (m + 1)‖ ≠ 0 := norm_ne_zero_iff.2 (hγ (m + 1) le_rfl)
    have hcc : ‖c h m‖ ≠ 0 := fun hc => hγ1 (by rw [h57, hc, zero_mul])
    have hss : ‖s h m‖ ≠ 0 := fun hc => hγ1 (by rw [h47, hc, zero_mul])
    have hgm : ‖γ h β m‖ ≠ 0 := fun hc => hγ1 (by rw [h47, hc, mul_zero])
    have hp : ‖b - op A (iomOfBasis x₀ u h β (m + 1))‖ ≠ 0 :=
      fun hc => hγ1 (by rw [h57, hc, mul_zero])
    have hcs : ‖c h m‖ ^ 2 + ‖s h m‖ ^ 2 = 1 :=
      norm_c_sq_add_norm_s_sq h (givensRho_ne_zero_of_gamma_ne_zero (hγ (m + 1) le_rfl))
    have e1 : ‖γ h β (m + 1)‖ ^ 2 = ‖s h m‖ ^ 2 * ‖γ h β m‖ ^ 2 := by rw [h47]; ring
    have e2 : ‖γ h β (m + 1)‖ ^ 2
        = ‖c h m‖ ^ 2 * ‖b - op A (iomOfBasis x₀ u h β (m + 1))‖ ^ 2 := by rw [h57]; ring
    -- `τ_{m+1} = |γ_{m+2}|`
    have hτ : qmrsTau (fun j => b - op A (iomOfBasis x₀ u h β j)) (m + 1)
        = ‖γ h β (m + 1)‖ := by
      have hsum : 1 / ‖γ h β m‖ ^ 2
            + 1 / ‖b - op A (iomOfBasis x₀ u h β (m + 1))‖ ^ 2
          = 1 / ‖γ h β (m + 1)‖ ^ 2 := by
        rw [div_add_div _ _ (pow_ne_zero 2 hgm) (pow_ne_zero 2 hp),
          div_eq_div_iff (by positivity) (by positivity)]
        linear_combination (‖b - op A (iomOfBasis x₀ u h β (m + 1))‖ ^ 2) * e1
          + (‖γ h β m‖ ^ 2) * e2
          + (‖γ h β m‖ ^ 2 * ‖b - op A (iomOfBasis x₀ u h β (m + 1))‖ ^ 2) * hcs
      rw [qmrsTau, ihτ, hsum, one_div_one_div, Real.sqrt_sq (norm_nonneg _)]
    -- `η_{m+1} = c_m²`
    have hη : qmrsEta (fun j => b - op A (iomOfBasis x₀ u h β j)) m = ‖c h m‖ ^ 2 := by
      have hden : (0 : ℝ) < ‖γ h β m‖ ^ 2
          + ‖b - op A (iomOfBasis x₀ u h β (m + 1))‖ ^ 2 :=
        add_pos_of_pos_of_nonneg (pow_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hgm)) 2)
          (sq_nonneg _)
      rw [qmrsEta, ihτ, div_eq_iff hden.ne']
      linear_combination (-1 : ℝ) * e1 + e2 - (‖γ h β m‖ ^ 2) * hcs
    -- the residual recurrence (6.58) with `‖s_m‖² = 1 - ‖c_m‖²`
    have hs2 : ‖s h m‖ ^ 2 = 1 - ‖c h m‖ ^ 2 := by linarith
    have hRm : IsUnit (R h m) := isUnit_R_of_gamma_ne_zero hhh fun j hj => hγ j (by omega)
    have hRm1 : IsUnit (R h (m + 1)) := isUnit_R_of_gamma_ne_zero hhh fun j hj => hγ j hj
    have hres : b - op A (qgmres x₀ u h β (m + 1))
        = b - op A (qgmres x₀ u h β m + ‖c h m‖ ^ 2 •
            (iomOfBasis x₀ u h β (m + 1) - qgmres x₀ u h β m)) := by
      rw [equation_6_58 hu hr hRm hRm1 (hH (m + 1) le_rfl)]
      simp only [RCLike.ofReal_real_eq_id, id_eq, map_add, map_smul, map_sub]
      rw [hs2]
      module
    have hstep : qgmres x₀ u h β (m + 1)
        = qgmres x₀ u h β m + ‖c h m‖ ^ 2 •
            (iomOfBasis x₀ u h β (m + 1) - qgmres x₀ u h β m) :=
      injective_op_of_isUnit hA (sub_right_injective hres)
    refine ⟨?_, hτ⟩
    rw [qmrs_succ, ihq, hη, hstep]
    simp only [Prod.mk.injEq, true_and]
    rw [map_add, map_smul, map_sub]
    module

end QMRSIOM

end Smoothing

/-! ### Section 6.5.8: minimal residual smoothing of FOM gives GMRES -/

section FOM

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : EuclideanSpace ℝ (Fin n))

local notation "𝔼" => EuclideanSpace ℝ (Fin n)

/-- If $x^O_i - x_0 \in \mathcal{K}_i(A, r_0)$ for every $i \le m$, then
$x^S_m - x_0 \in \mathcal{K}_m(A, r_0)$. -/
theorem mrsX_sub_mem (xO rO : ℕ → 𝔼) {m : ℕ}
    (hO : ∀ i ≤ m, xO i - x₀ ∈ Krylov.subspace (op A) (b - op A x₀) i) :
    mrsX xO rO m - x₀ ∈ Krylov.subspace (op A) (b - op A x₀) m := by
  induction m with
  | zero => rw [mrsX_zero]; exact hO 0 le_rfl
  | succ k ih =>
    have hmono := Krylov.subspace_mono (op A) (b - op A x₀) (Nat.le_succ k)
    have ihk := ih fun i hi => hO i (by omega)
    rw [mrsX_succ, show mrsX xO rO k + mrsEta xO rO k • (xO (k + 1) - mrsX xO rO k) - x₀
        = (mrsX xO rO k - x₀) + mrsEta xO rO k • ((xO (k + 1) - x₀) - (mrsX xO rO k - x₀)) by
      module]
    exact Submodule.add_mem _ (hmono ihk)
      (Submodule.smul_mem _ _ (Submodule.sub_mem _ (hO (k + 1) le_rfl) (hmono ihk)))

/-- Section 6.5.8 of [saad2003iterative]. Let $r^O_j = b - Ax^O_j$ for all $j$, and let $x^O_i$ be
the Galerkin iterate on $\mathcal{K}_i(A, r_0)$ for every $i \le m$. Then $x^S_m$ is the
minimal-residual iterate on $\mathcal{K}_m(A, r_0)$. The book assumes $A$ nonsingular in all of
Chapter 6; this statement does not need it.

**Reading.** The minimizing property works for any sequence of exact Galerkin iterates. The specific
equality with computed GMRES assumes a nonsingular system, defined FOM iterates, a reached prefix
and nonzero GMRES residual.
-/
theorem mrs_isMinResidualIterate (xO rO : ℕ → 𝔼)
    (hr : ∀ j, rO j = b - op A (xO j)) (m : ℕ)
    (hO : ∀ i ≤ m, Krylov.IsGalerkinIterate (op A) b x₀ i (xO i)) :
    Krylov.IsMinResidualIterate (op A) b x₀ m (mrsX xO rO m) := by
  rw [(mrs_eq A b xO rO hr m).1]
  exact Krylov.IsGalerkinIterate.mrs_isMinResidualIterate m hO

/-- Section 6.5.8 of [saad2003iterative]. Let $A$ be nonsingular, $r^O_j = b - Ax^F_j$ for all $j$,
$m \le \operatorname{grade}(v_1)$, let $H_i$ be nonsingular for every $i \le m$, and let
$\rho^G_m \neq 0$. Then minimal residual smoothing of the FOM approximations gives the GMRES
approximation: $x^S_m = x^G_m$. The FOM residuals are mutually orthogonal, so Lemma 6.18 applies
at every step and the smoothed residual norms satisfy (6.66)–(6.67); GMRES minimizes over the
same subspace, so the two sequences agree.

**Reading.** The minimizing property works for any sequence of exact Galerkin iterates. The specific
equality with computed GMRES assumes a nonsingular system, defined FOM iterates, a reached prefix
and nonzero GMRES residual.
-/
theorem mrs_fom_eq_gmres (hA : IsUnit A) (rO : ℕ → 𝔼)
    (hr : ∀ j, rO j = b - op A (fomFixed A b x₀ j)) {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀))
    (hH : ∀ i ≤ m, FOMDefined A b x₀ i) (h0 : ρG A b x₀ m ≠ 0) :
    mrsX (fomFixed A b x₀) rO m = gmresFixed A b x₀ m := by
  have hgal : ∀ i ≤ m, Krylov.IsGalerkinIterate (op A) b x₀ i (fomFixed A b x₀ i) :=
    fun i hi => fomFixed_isGalerkin A b x₀ (hi.trans hm) (hH i hi)
  have hG := gmresFixed_isMinResidualIterate A b x₀ hm
    (isUnit_R_of_fomDefined A b x₀ hm (hH m le_rfl))
  have hrne : ∀ j ≤ m, rO j ≠ 0 := by
    intro j hj hz
    rw [hr j] at hz
    have hAy : op A (fomFixed A b x₀ j) = b := (sub_eq_zero.1 hz).symm
    have hex := hG.apply_eq_of_exists
      (Krylov.subspace_mono (op A) (b - op A x₀) hj (hgal j hj).mem) hAy
    exact h0 (norm_eq_zero.2 (by rw [hex, sub_self]))
  have hpair : ∀ i ≤ m, ∀ j ≤ m, i ≠ j → inner ℝ (rO i) (rO j) = 0 := by
    intro i hi j hj hij
    rw [hr i, hr j]
    exact Krylov.IsGalerkinIterate.inner_residual_eq_zero (hgal i hi) (hgal j hj) hij
  have horth : ∀ j < m, inner ℝ (rO (j + 1)) (mrsR (fomFixed A b x₀) rO j) = 0 := fun j hj =>
    inner_mrsR_eq_zero (fomFixed A b x₀) rO _ j fun i hi =>
      hpair (j + 1) (by omega) i (by omega) (by omega)
  have hsum := inv_sq_norm_mrsR (fomFixed A b x₀) rO hrne horth
  have h66 := equation_6_66 A b x₀ hm hH h0
  have heq := mrs_eq A b (fomFixed A b x₀) rO hr m
  have hres : mrsR (fomFixed A b x₀) rO m
      = b - op A (mrsX (fomFixed A b x₀) rO m) := by rw [heq.1]; exact heq.2
  have hGpos : 0 < ρG A b x₀ m := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
  have hnorm : ‖b - op A (mrsX (fomFixed A b x₀) rO m)‖ = ρG A b x₀ m := by
    rw [← hres]
    have hsum' : 1 / ‖mrsR (fomFixed A b x₀) rO m‖ ^ 2 = 1 / ρG A b x₀ m ^ 2 := by
      rw [hsum, ← h66]
      exact Finset.sum_congr rfl fun j _ => by rw [hr j]
    have hne : ‖mrsR (fomFixed A b x₀) rO m‖ ≠ 0 := by
      intro hz
      rw [hz] at hsum'
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero] at hsum'
      exact (one_div_pos.2 (pow_pos hGpos 2)).ne hsum'
    have hsq : ‖mrsR (fomFixed A b x₀) rO m‖ ^ 2 = ρG A b x₀ m ^ 2 := by
      field_simp at hsum'
      linarith
    nlinarith [norm_nonneg (mrsR (fomFixed A b x₀) rO m), hGpos, hsq]
  have hmres : Krylov.IsMinResidualIterate (op A) b x₀ m (mrsX (fomFixed A b x₀) rO m) := by
    refine ⟨mrsX_sub_mem A b x₀ _ rO fun i hi => (hgal i hi).mem, fun y hy => ?_⟩
    rw [hnorm]
    exact hG.min y hy
  obtain ⟨z, -, huniq⟩ :=
    Krylov.existsUnique_isMinResidualIterate_of_injective (injective_op_of_isUnit hA) b x₀ m
  rw [huniq _ hmres, huniq _ hG]

/-- Equation (6.79) of [saad2003iterative] for Galerkin iterates. Let $r^O_j = b - Ax^O_j$ for all
$j$, let $x^O_i$ be the Galerkin iterate on $\mathcal{K}_i(A, r_0)$ for every $i \le m$, and let
$r^O_0, \dots, r^O_m$ be nonzero. Then $r^S_m = \big(\sum_{j=0}^m \rho_j^{-2}\big)^{-1}
\sum_{j=0}^m \rho_j^{-2} r^O_j$. The book assumes $A$ nonsingular in all of Chapter 6; this
statement does not need it.

**Correction.** The weighted sum includes the initial residual at index zero. The source prints both
sums starting at one. The Lean formulas assume nonzero original residuals.
-/
theorem residual_mrs_eq (xO rO : ℕ → 𝔼) (hr : ∀ j, rO j = b - op A (xO j))
    {m : ℕ} (hO : ∀ i ≤ m, Krylov.IsGalerkinIterate (op A) b x₀ i (xO i))
    (h0 : ∀ j ≤ m, rO j ≠ 0) :
    mrsR xO rO m = (∑ j ∈ Finset.range (m + 1), 1 / ‖rO j‖ ^ 2)⁻¹ •
      ∑ j ∈ Finset.range (m + 1), (1 / ‖rO j‖ ^ 2) • rO j := by
  have hkey := Krylov.residual_mrs_eq m hO
    (fun j hj => by rw [← hr j]; exact h0 j hj)
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hkey
  rw [(mrs_eq A b xO rO hr m).2, hkey]
  simp only [← hr]

/-- **Problem P-6.26** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ and
$b, x_0 \in \mathbb{R}^n$, let $r^O_j = b - Ax^O_j$ for all $j$, and let $x^O_m$ be the Galerkin
iterate on $\mathcal{K}_m(A, r_0)$ for every $m$. Then for $i \neq j$,
$$\big( A(x^O_{i+1} - x^S_i), \ A(x^O_{j+1} - x^S_j) \big) = 0.$$
So the directions $x^O_{j+1} - x^S_j$ of Algorithm 6.14 are $A^T A$-orthogonal, which is the
hypothesis of Lemma 6.21 (`SaadSparse.Chapter06.lemma_6_21`), the lemma behind GCR and ORTHOMIN.

The book assumes $A$ nonsingular in all of Chapter 6; this statement does not need it.

**Reading.** Lean obtains the requested orthogonality of the directions from the stronger hypothesis
of Galerkin iterates on the Krylov sequence, rather than from pairwise orthogonality of arbitrary
original residuals. Equality with GMRES is treated separately. The exercise's reference to Algorithm
7.5 means Algorithm 6.14.
-/
theorem problem_6_26 (xO rO : ℕ → 𝔼) (hr : ∀ j, rO j = b - op A (xO j))
    (hO : ∀ m, Krylov.IsGalerkinIterate (op A) b x₀ m (xO m)) {i j : ℕ} (hij : i ≠ j) :
    inner ℝ (op A (xO (i + 1) - mrsX xO rO i)) (op A (xO (j + 1) - mrsX xO rO j)) = 0 := by
  have hmemS : ∀ k, mrsX xO rO k - x₀ ∈ Krylov.subspace (op A) (b - op A x₀) k :=
    fun k => mrsX_sub_mem A b x₀ xO rO fun i _ => (hO i).mem
  have hres : ∀ k, mrsR xO rO k = b - op A (mrsX xO rO k) := fun k => by
    have h := mrs_eq A b xO rO hr k
    rw [h.1]
    exact h.2
  have hminres : ∀ k, Krylov.IsMinResidualIterate (op A) b x₀ k (mrsX xO rO k) :=
    fun k => mrs_isMinResidualIterate A b x₀ xO rO hr k fun i _ => hO i
  have key : ∀ p q : ℕ, p < q →
      inner ℝ (op A (xO (p + 1) - mrsX xO rO p)) (op A (xO (q + 1) - mrsX xO rO q)) = 0 := by
    intro p q hpq
    have hmem : op A (xO (p + 1) - mrsX xO rO p)
        ∈ (Krylov.subspace (op A) (b - op A x₀) q).map (op A) := by
      refine Submodule.mem_map_of_mem ?_
      rw [show xO (p + 1) - mrsX xO rO p = (xO (p + 1) - x₀) - (mrsX xO rO p - x₀) by abel]
      exact Submodule.sub_mem _
        (Krylov.subspace_mono (op A) (b - op A x₀) (by omega) (hO (p + 1)).mem)
        (Krylov.subspace_mono (op A) (b - op A x₀) (by omega) (hmemS p))
    have h1 : inner ℝ (op A (xO (p + 1) - mrsX xO rO p)) (mrsR xO rO q) = 0 := by
      rw [hres q]
      exact (Submodule.mem_orthogonal _ _).1
        (Krylov.IsMinResidualIterate.residual_mem_orthogonal (hminres q)) _ hmem
    have h2 : inner ℝ (op A (xO (p + 1) - mrsX xO rO p)) (rO (q + 1)) = 0 := by
      rw [hr (q + 1)]
      exact IsPetrovGalerkin.inner_residual_eq_zero (hO (q + 1))
        (Krylov.map_subspace_le (op A) (b - op A x₀) q hmem)
    have hd : op A (xO (q + 1) - mrsX xO rO q) = mrsR xO rO q - rO (q + 1) := by
      rw [hres q, hr (q + 1), map_sub]
      abel
    rw [hd, inner_sub_right, h1, h2, sub_zero]
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · rw [real_inner_comm]
    exact key j i h

end FOM

end SaadSparse.Chapter06

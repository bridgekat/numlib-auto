/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.TransposeFree
import NumlibSurface.SaadSparse.Chapter07.Section03

/-!
# Saad, Section 7.4: Transpose-free variants

This module formalizes Section 7.4 of [saad2003iterative], which presents three methods derived from
BCG that need no products with $A^H$: CGS (Algorithm 7.6, Sonneveld), BICGSTAB (Algorithm 7.7, van
der Vorst) and TFQMR (Algorithm 7.8, Freund). The section proves no numbered result about them. What
gives each method its meaning is a polynomial identity, and these identities are what the module
states. Let $\varphi_j$ and $\pi_j$ be the BCG residual and direction polynomials of (7.32)–(7.33),
so that BCG has $r_j = \varphi_j(A) r_0$ and $p_j = \pi_j(A) r_0$. Then CGS computes
$r_j = \varphi_j^2(A) r_0$ (equations (7.40)–(7.45)), and BICGSTAB computes
$r_j = \psi_j(A) \varphi_j(A) r_0$ with $\psi_{j+1}(t) = (1 - \omega_j t) \psi_j(t)$ (equations
(7.46)–(7.52)). The BCG coefficients can be computed from the BICGSTAB vectors (equations
(7.53)–(7.54)).

TFQMR runs on the CGS vectors with doubled indices (equations (7.56)–(7.65)). They satisfy
$Au_j = (w_j - w_{j+1})/\alpha_j$, a Hessenberg relation with two families of vectors and a
bidiagonal coefficient matrix $\bar H_m$ (equations (7.68)–(7.73)). The module shows that Algorithm
7.8 computes the quasi-minimal residual iterate of this relation, and it proves the bound (7.83),
$\|b - Ax_m\|_2 \le \sqrt{m+1} \, \tau_m$. The proofs specialize `Numlib.Krylov.TransposeFree`,
`Numlib.Krylov.BiLanczos` and `Numlib.Krylov.QuasiMinRes`.

## Main definitions

* Equations (7.32)–(7.36), `SaadSparse.Chapter07.bcgResidualPoly` and
  `SaadSparse.Chapter07.bcgDirectionPoly`: the BCG residual polynomial $\varphi_j$ and direction
  polynomial $\pi_j$.
* Algorithm 7.6, `SaadSparse.Chapter07.cgs`: the conjugate gradient squared method (CGS), with the
  state `SaadSparse.Chapter07.CGSState` and the auxiliary vector `SaadSparse.Chapter07.cgsQ`.
* Algorithm 7.7, `SaadSparse.Chapter07.bicgstab`: BICGSTAB, with the state
  `SaadSparse.Chapter07.BICGSTABState`, the half-step residual `SaadSparse.Chapter07.bicgstabS` and
  the step length `SaadSparse.Chapter07.bicgstabOmega`.
* Equation (7.47), `SaadSparse.Chapter07.bicgstabPoly`: the stabilizing polynomial $\psi_j$.
* Algorithm 7.8, `SaadSparse.Chapter07.tfqmr`: the transpose-free QMR method (TFQMR), with the state
  `SaadSparse.Chapter07.TFQMRState`.
* Equations (7.66)–(7.67), `SaadSparse.Chapter07.cgsHalfIterate`: the CGS iterates extended to
  half-steps.
* Equations (7.72) and (7.81), `SaadSparse.Chapter07.tfqmrCoeff`: the bidiagonal coefficient array
  $\bar H_m = \Delta_{m+1} \bar B_m$.
* Equation (7.73), `SaadSparse.Chapter07.tfqmrDelta`: the column scaling $\delta_i = \|w_i\|_2$.
* `SaadSparse.Chapter07.TFQMRNoSeriousBreakdown` and `SaadSparse.Chapter07.TFQMRNoBreakdown`: the
  two no-breakdown hypotheses of TFQMR.

## Main results

* Equations (7.32)–(7.33), `SaadSparse.Chapter07.bcg_residual_eq_aeval`: $r_j = \varphi_j(A) r_0$,
  $p_j = \pi_j(A) r_0$, and the conjugate polynomials at $A^H$ give $r^*_j$ and $p^*_j$.
* `SaadSparse.Chapter07.inner_aeval_conjTranspose_aeval`:
  $(p(A) v, \bar q(A^H) w) = (q(A) p(A) v, w)$, the step that removes the transpose.
* Equations (7.40)–(7.45), `SaadSparse.Chapter07.cgs_residual_eq`: the CGS vectors are the squared
  BCG polynomials applied to $r_0$, and the CGS coefficients are the BCG coefficients.
* Equations (7.46) and (7.52), `SaadSparse.Chapter07.bicgstab_residual_eq`:
  $r_j = \psi_j(A) \varphi_j(A) r_0$ and $p_j = \psi_j(A) \pi_j(A) r_0$.
* Equations (7.53)–(7.54), `SaadSparse.Chapter07.equation_7_53`: the BCG coefficients in terms of
  the BICGSTAB vectors.
* Equation (7.55), `SaadSparse.Chapter07.equation_7_55`: $\omega_j$ minimizes
  $\|(I - \omega A) s_j\|_2$.
* Equations (7.56)–(7.62), `SaadSparse.Chapter07.tfqmr_eq_cgs`: the even half-steps of Algorithm 7.8
  carry the CGS state.
* Equations (7.63)–(7.64), `SaadSparse.Chapter07.cgsHalfIterate_two_mul`: the even half-step
  iterates are the CGS iterates.
* Equations (7.68)–(7.73), `SaadSparse.Chapter07.equation_7_70`: $Au_i = (w_i - w_{i+1})/\alpha_i$
  is a two-family Hessenberg relation with the bidiagonal $\bar H_m$.
* Equations (7.74)–(7.76) and exercise P-7.9, `SaadSparse.Chapter07.equation_7_76`: the FOM formula
  for the extended CGS iterates, for every column scaling.
* `SaadSparse.Chapter07.tfqmr_eq_dqgmres`, `SaadSparse.Chapter07.tfqmr_eq_qgmres` and
  `SaadSparse.Chapter07.tfqmr_isQuasiMinResidualIterate`: Algorithm 7.8 is Algorithm 6.13 with
  $k = 1$, hence Algorithm 6.12, hence the quasi-minimal residual iterate.
* Equation (7.83), `SaadSparse.Chapter07.equation_7_83`: $\|b - Ax_m\|_2 \le \sqrt{m+1} \, \tau_m$.
* Section 7.4.3, `SaadSparse.Chapter07.norm_gamma_eq_tfqmrTau`: the quasi-residual scalar has
  modulus $\tau_m$.

## Proof outline

Every scalar of the section is computed by moving a polynomial across the inner product,
`BiLanczos.inner_aeval_map_eq`. For (7.53)–(7.54), the proof replaces $\psi_j(A^H) r^*_0$ and
$\varphi_j(A^H) r^*_0$ by their leading terms and compares the leading coefficients
$\eta_1^{(j+1)} = -\omega_j \eta_1^{(j)}$ of $\psi$ and
$\gamma_1^{(j+1)} = -\alpha_j \gamma_1^{(j)}$ of $\varphi$. For TFQMR, the scaling
$\delta_i = \|w_i\|_2$ of (7.73) gives the residual basis unit columns. The $\theta$, $c$, $\tau$,
$\eta$, $d$ recurrence of Algorithm 7.8 is Algorithm 6.13 (DQGMRES) with $k = 1$, which loses
nothing because $\bar H_m$ is bidiagonal, so it computes the quasi-minimal residual iterate of
Algorithm 6.12. The bound (7.83) then follows as Proposition 7.3 does.

## Conventions

* Indices are $0$-based as in the rest of the chapter: `cgs A b x₀ rs₀ j` is the state of the book
  after $j$ steps, `tfqmr A b x₀ rs₀ m` is its state after $m$ half-steps, and
  `bcgResidualPoly A b x₀ rs₀ j` is its $\varphi_j$.
* The polynomials $\varphi_j$ and $\pi_j$ are defined from the coefficients
  `SaadSparse.Chapter07.bcgAlpha` and `SaadSparse.Chapter07.bcgBeta` of the run of Algorithm 7.3 for
  the same $A$, $b$, $x_0$ and $r^*_0$.
* Over $\mathbb{C}$, the starred BCG vectors carry the conjugate polynomials:
  $r^*_j = \bar\varphi_j(A^H) r^*_0$. Over $\mathbb{R}$ this is the book's
  $r^*_j = \varphi_j(A^T) r^*_0$.

## Implementation notes

* CGS needs no hypothesis: the squared polynomials are computed without any product with $A^H$,
  which is the purpose of the method. BICGSTAB needs the two hypotheses of the leading-coefficient
  argument of the book: Algorithm 7.3 has not broken down, so that $\gamma_1^{(j)} \neq 0$, and no
  $\omega_i$ has vanished, so that $\eta_1^{(j)} \neq 0$.
* The TFQMR hypotheses are bounded or conditional, because $\alpha_m \neq 0$ for all $m$ cannot hold
  in finite dimension: Algorithm 7.3 terminates, and $\rho_j = 0$ from the grade on, so a theorem
  with that hypothesis would say nothing. `SaadSparse.Chapter07.TFQMRNoBreakdown` asks that no
  $\alpha_i$ and no $w_i$ vanish through step $m$, which is what the first $m$ rotations need.
  `SaadSparse.Chapter07.TFQMRNoSeriousBreakdown` asks that $\alpha_m = 0$ imply $Au_m = 0$, which is
  what (7.70) needs and what a regular termination gives. It is the analogue of
  `SaadSparse.Chapter07.NoSeriousBreakdown` for Algorithm 7.1.
* Over $\mathbb{C}$ the real recurrence of the book for $\theta_m$, $c_m$ and $\tau_m$ still
  computes the right quantities. The value $\tau_m$ is the modulus of the backbone scalar
  `Krylov.gamma`, and $\eta_{m+1} = c_{m+1}^2 \alpha_m$ is exactly the DQGMRES step length
  $g_m/\rho_m$, so the phase of $\alpha_m$ enters only through $\eta$.
* `SaadSparse.Chapter07.equation_7_70` and `SaadSparse.Chapter07.equation_7_76` hold for an
  arbitrary column scaling $\Delta_{m+1}$, which is what exercise P-7.9 asks about.

## Deviations from the source

* **Representation.** TFQMR stores the quantities that carry over between half-steps. See
  `SaadSparse.Chapter07.TFQMRState`.
* **Generalization.** TFQMR accepts arbitrary shadows and complex input and initializes an extra
  alpha field. See `SaadSparse.Chapter07.tfqmr`, `SaadSparse.Chapter07.tfqmr_zero`.
* **Totalization.** TFQMR extends the real updates to complex scalars and totalizes their quotients.
  See `SaadSparse.Chapter07.tfqmrStepAlpha`, `SaadSparse.Chapter07.tfqmrStepBeta`,
  `SaadSparse.Chapter07.tfqmr_alpha_even`, `SaadSparse.Chapter07.tfqmr_succ_theta`,
  `SaadSparse.Chapter07.tfqmr_succ_d`, `SaadSparse.Chapter07.tfqmr_succ_rho_odd`,
  `SaadSparse.Chapter07.tfqmr_succ_u_odd`, `SaadSparse.Chapter07.tfqmr_succ_v_odd`.
* **Scope.** TFQMR defines all half-steps independently of a stopping rule. See
  `SaadSparse.Chapter07.tfqmrStep`, `SaadSparse.Chapter07.tfqmr_succ`.
* **Correction.** The TFQMR coefficient array uses the terminal row indices implied by the product
  in (7.81). See `SaadSparse.Chapter07.tfqmrCoeff`, `SaadSparse.Chapter07.tfqmrH`.
* **Correction.** The TFQMR entry lemmas use the corrected zero-based scaling factors in (7.81). See
  `SaadSparse.Chapter07.tfqmrCoeff_self`, `SaadSparse.Chapter07.tfqmrCoeff_succ_self`,
  `SaadSparse.Chapter07.tfqmrH_self`, `SaadSparse.Chapter07.tfqmrH_succ_self`.
* **Scope.** The continuation condition for (7.69) is phrased through the image direction. See
  `SaadSparse.Chapter07.TFQMRNoSeriousBreakdown`.
* **Generalization.** The TFQMR Hessenberg identity permits zero step lengths and zero scales under
  explicit conditions. See `SaadSparse.Chapter07.equation_7_70`.
* **Generalization.** The reduced TFQMR least-squares formulation permits any nonzero finite
  scaling. See `SaadSparse.Chapter07.equation_7_76`.
* **Scope.** The TFQMR equivalences use a nonzero prefix that includes index $m$. See
  `SaadSparse.Chapter07.TFQMRNoBreakdown`.
* **Totalization.** Norm-based scaling is defined for zero residuals, whose normalized columns are
  then zero. See `SaadSparse.Chapter07.tfqmrDelta`.
* **Convention.** The TFQMR residual recurrence identifies tau with the magnitude of the rotated
  residual. See `SaadSparse.Chapter07.norm_gamma_eq_tfqmrTau`.
* **Scope.** The proofs of equivalence with DQGMRES and the projected minimizer assume the nonzero
  prefix. See `SaadSparse.Chapter07.tfqmr_eq_dqgmres`, `SaadSparse.Chapter07.tfqmr_eq_qgmres`,
  `SaadSparse.Chapter07.tfqmr_isQuasiMinResidualIterate`.
* **Scope.** The residual bound (7.83) has explicit finite and global no-breakdown hypotheses. See
  `SaadSparse.Chapter07.equation_7_83`.
* **Generalization.** The BCG residual and direction polynomial recurrences extend to totalized
  complex coefficients. See `SaadSparse.Chapter07.bcgResidualPoly`,
  `SaadSparse.Chapter07.bcgDirectionPoly`, `SaadSparse.Chapter07.bcgResidualPoly_succ`,
  `SaadSparse.Chapter07.bcgDirectionPoly_succ`.
* **Reading.** The BCG polynomial degree bounds allow vanishing leading coefficients. See
  `SaadSparse.Chapter07.bcgResidualPoly_natDegree_le`,
  `SaadSparse.Chapter07.bcgDirectionPoly_natDegree_le`.
* **Generalization.** The BCG leading-term identities are valid even when those coefficients vanish.
  See `SaadSparse.Chapter07.bcgDirectionPoly_coeff_self`,
  `SaadSparse.Chapter07.bcgResidualPoly_coeff_succ`.
* **Generalization.** The dual BCG polynomial formulas use conjugate coefficients with the adjoint.
  See `SaadSparse.Chapter07.bcg_succ`, `SaadSparse.Chapter07.bcg_residual_eq_aeval`,
  `SaadSparse.Chapter07.inner_aeval_conjTranspose_aeval`.
* **Reading.** The CGS recurrence is defined for complex input and all indices with totalized
  quotients. See `SaadSparse.Chapter07.cgsStep`, `SaadSparse.Chapter07.cgs`,
  `SaadSparse.Chapter07.cgs_succ`, `SaadSparse.Chapter07.cgsAlpha`, `SaadSparse.Chapter07.cgsBeta`,
  `SaadSparse.Chapter07.cgsQ`, `SaadSparse.Chapter07.cgs_succ_x`, `SaadSparse.Chapter07.cgs_succ_r`,
  `SaadSparse.Chapter07.cgs_succ_u`, `SaadSparse.Chapter07.cgs_succ_p`.
* **Generalization.** The squared polynomial identity holds for the totalized CGS and BCG
  recurrences. See `SaadSparse.Chapter07.cgs_residual_eq`.
* **Reading.** The BICGSTAB recurrence totalizes the quotients and uses the complex minimum-residual
  coefficient. See `SaadSparse.Chapter07.bicgstabStep`, `SaadSparse.Chapter07.bicgstab`,
  `SaadSparse.Chapter07.bicgstab_succ`, `SaadSparse.Chapter07.bicgstabAlpha`,
  `SaadSparse.Chapter07.bicgstabS`, `SaadSparse.Chapter07.bicgstabOmega`,
  `SaadSparse.Chapter07.bicgstabBeta`.
* **Generalization.** The BICGSTAB update identities include the complex totalized recurrence. See
  `SaadSparse.Chapter07.bicgstab_succ_x`, `SaadSparse.Chapter07.bicgstab_succ_r`,
  `SaadSparse.Chapter07.bicgstab_succ_p`.
* **Reading.** The BICGSTAB comparison makes the leading-coefficient nonvanishing conditions
  explicit. See `SaadSparse.Chapter07.bicgstab_residual_eq`, `SaadSparse.Chapter07.equation_7_53`.
* **Generalization.** The BICGSTAB minimum-residual half-step includes the case of zero matrix
  image. See `SaadSparse.Chapter07.equation_7_55`.
-/

open Matrix Polynomial

open scoped Matrix SaadSparse

namespace SaadSparse.Chapter07

open Chapter06 (op)

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-! ### §7.4.1: the BCG residual and direction polynomials -/

section BCGPolynomials

variable (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ rs₀ : EuclideanSpace 𝕜 (Fin n))

/-- **Equations (7.32) and (7.35)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$ and
$b, x_0, r^*_0 \in \mathbb{K}^n$. The **BCG residual polynomial** $\varphi_j$ is defined from
the coefficients $\alpha_j$ of Algorithm 7.3 by $$\varphi_0 = 1, \qquad \varphi_{j+1}(t) =
\varphi_j(t) - \alpha_j t \, \pi_j(t),$$ where $\pi_j$ is the BCG direction polynomial. It has
degree at most $j$, it satisfies $\varphi_j(0) = 1$, and the BCG residual is
$r_j = \varphi_j(A) r_0$ (`SaadSparse.Chapter07.bcg_residual_eq_aeval`). Its degree is exactly
$j$ while no $\alpha_i$ vanishes.

The definition is the backbone `BCG.residualPoly` for the operators $A$ and $A^H$.

**Generalization.** The revised polynomials use totalized BCG coefficients over the real or complex
field. They are defined after breakdown as well as during the source's active real recurrence.
-/
noncomputable def bcgResidualPoly (j : ℕ) : 𝕜[X] := BCG.residualPoly (op A) (op Aᴴ) b x₀ rs₀ j

/-- **Equations (7.33) and (7.36)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$ and
$b, x_0, r^*_0 \in \mathbb{K}^n$. The **BCG direction polynomial** $\pi_j$ is defined from the
coefficients $\beta_j$ of Algorithm 7.3 by $$\pi_0 = 1, \qquad \pi_{j+1} = \varphi_{j+1} +
\beta_j \pi_j.$$ It has degree at most $j$, and the BCG direction is $p_j = \pi_j(A) r_0$.

The definition is the backbone `BCG.directionPoly` for the operators $A$ and $A^H$.

**Generalization.** The revised polynomials use totalized BCG coefficients over the real or complex
field. They are defined after breakdown as well as during the source's active real recurrence.
-/
noncomputable def bcgDirectionPoly (j : ℕ) : 𝕜[X] := BCG.directionPoly (op A) (op Aᴴ) b x₀ rs₀ j

/-- The BCG residual polynomial starts with $\varphi_0 = 1$. -/
@[simp] theorem bcgResidualPoly_zero : bcgResidualPoly A b x₀ rs₀ 0 = 1 := rfl

/-- The BCG direction polynomial starts with $\pi_0 = 1$. -/
@[simp] theorem bcgDirectionPoly_zero : bcgDirectionPoly A b x₀ rs₀ 0 = 1 := rfl

/-- Equation (7.35): $\varphi_{j+1}(t) = \varphi_j(t) - \alpha_j t \, \pi_j(t)$.

**Generalization.** The revised polynomials use totalized BCG coefficients over the real or complex
field. They are defined after breakdown as well as during the source's active real recurrence.
-/
theorem bcgResidualPoly_succ (j : ℕ) : bcgResidualPoly A b x₀ rs₀ (j + 1) =
    bcgResidualPoly A b x₀ rs₀ j
      - C (bcgAlpha A b x₀ rs₀ j) * (X * bcgDirectionPoly A b x₀ rs₀ j) :=
  BCG.residualPoly_succ _ _ _ _ _ j

/-- Equation (7.36): $\pi_{j+1} = \varphi_{j+1} + \beta_j \pi_j$.

**Generalization.** The revised polynomials use totalized BCG coefficients over the real or complex
field. They are defined after breakdown as well as during the source's active real recurrence.
-/
theorem bcgDirectionPoly_succ (j : ℕ) : bcgDirectionPoly A b x₀ rs₀ (j + 1) =
    bcgResidualPoly A b x₀ rs₀ (j + 1)
      + C (bcgBeta A b x₀ rs₀ j) * bcgDirectionPoly A b x₀ rs₀ j :=
  BCG.directionPoly_succ _ _ _ _ _ j

/-- The residual polynomials are consistent: $\varphi_j(0) = 1$ for every $j$, which makes
$\varphi_j(A) r_0$ a residual. -/
@[simp] theorem bcgResidualPoly_eval_zero (j : ℕ) :
    (bcgResidualPoly A b x₀ rs₀ j).eval 0 = 1 :=
  BCG.residualPoly_eval_zero _ _ _ _ _ j

/-- The BCG residual polynomial $\varphi_j$ has degree at most $j$.

**Reading.** The book calls these degree-$j$ polynomials. Lean gives upper degree bounds without
assuming that the leading coefficients of the totalized recurrences are nonzero.
-/
theorem bcgResidualPoly_natDegree_le (j : ℕ) : (bcgResidualPoly A b x₀ rs₀ j).natDegree ≤ j :=
  BCG.residualPoly_natDegree_le _ _ _ _ _ j

/-- The BCG direction polynomial $\pi_j$ has degree at most $j$.

**Reading.** The book calls these degree-$j$ polynomials. Lean gives upper degree bounds without
assuming that the leading coefficients of the totalized recurrences are nonzero.
-/
theorem bcgDirectionPoly_natDegree_le (j : ℕ) : (bcgDirectionPoly A b x₀ rs₀ j).natDegree ≤ j :=
  BCG.directionPoly_natDegree_le _ _ _ _ _ j

/-- The coefficients of $t^j$ in $\pi_j$ and in $\varphi_j$ are equal, because $\pi_j$ differs from
$\varphi_j$ only by a multiple of $\pi_{j-1}$, which has lower degree. This is the statement, in
the derivation of (7.54), that the leading coefficients of $\varphi_j(A^H) r^*_0$ and
$\pi_j(A^H) r^*_0$ are identical.

**Generalization.** The identities concern the coefficients of the prescribed powers and hold even
when those coefficients vanish. The source uses them as leading coefficients of nonbroken
recurrences.
-/
theorem bcgDirectionPoly_coeff_self (j : ℕ) :
    (bcgDirectionPoly A b x₀ rs₀ j).coeff j = (bcgResidualPoly A b x₀ rs₀ j).coeff j :=
  BCG.directionPoly_coeff_self _ _ _ _ _ j

/-- The coefficients $\gamma_1^{(j)}$ of $t^j$ in $\varphi_j$ satisfy
$\gamma_1^{(j+1)} = -\alpha_j \gamma_1^{(j)}$. This is the first of the two relations that the
derivation of (7.53) compares.

**Generalization.** The identities concern the coefficients of the prescribed powers and hold even
when those coefficients vanish. The source uses them as leading coefficients of nonbroken
recurrences.
-/
theorem bcgResidualPoly_coeff_succ (j : ℕ) :
    (bcgResidualPoly A b x₀ rs₀ (j + 1)).coeff (j + 1) =
      -bcgAlpha A b x₀ rs₀ j * (bcgResidualPoly A b x₀ rs₀ j).coeff j :=
  BCG.residualPoly_coeff_succ _ _ _ _ _ j

/-- Lines 6, 7, 9 and 10 of Algorithm 7.3, in the notation of the book:
$r_{j+1} = r_j - \alpha_j A p_j$, $r^*_{j+1} = r^*_j - \bar\alpha_j A^H p^*_j$,
$p_{j+1} = r_{j+1} + \beta_j p_j$ and $p^*_{j+1} = r^*_{j+1} + \bar\beta_j p^*_j$.

**Generalization.** Lean conjugates the coefficients on the dual side so polynomial evaluation can
be moved across the complex inner product using the adjoint. The real restriction gives the source's
transpose relation.
-/
theorem bcg_succ (j : ℕ) :
    (bcg A b x₀ rs₀ (j + 1)).r
        = (bcg A b x₀ rs₀ j).r - bcgAlpha A b x₀ rs₀ j • op A (bcg A b x₀ rs₀ j).p ∧
      (bcg A b x₀ rs₀ (j + 1)).rs
        = (bcg A b x₀ rs₀ j).rs
          - starRingEnd 𝕜 (bcgAlpha A b x₀ rs₀ j) • op Aᴴ (bcg A b x₀ rs₀ j).ps ∧
      (bcg A b x₀ rs₀ (j + 1)).p
        = (bcg A b x₀ rs₀ (j + 1)).r + bcgBeta A b x₀ rs₀ j • (bcg A b x₀ rs₀ j).p ∧
      (bcg A b x₀ rs₀ (j + 1)).ps
        = (bcg A b x₀ rs₀ (j + 1)).rs
          + starRingEnd 𝕜 (bcgBeta A b x₀ rs₀ j) • (bcg A b x₀ rs₀ j).ps := by
  simp only [bcg_eq]
  exact ⟨BCG.residual_succ _ _ _ _ _ j, BCG.dualResidual_succ _ _ _ _ _ j,
    BCG.direction_succ _ _ _ _ _ j, BCG.dualDirection_succ _ _ _ _ _ j⟩

/-- **Equations (7.32)–(7.33)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$ and
$b, x_0, r^*_0 \in \mathbb{K}^n$, and let $r_0 = b - Ax_0$. For every $j$, the vectors of
Algorithm 7.3 are $$r_j = \varphi_j(A) r_0, \quad p_j = \pi_j(A) r_0, \quad r^*_j =
\bar\varphi_j(A^H) r^*_0, \quad p^*_j = \bar\pi_j(A^H) r^*_0,$$ where $\bar\varphi_j$ and
$\bar\pi_j$ are $\varphi_j$ and $\pi_j$ with conjugated coefficients. Over $\mathbb{R}$, where
the book works, $\bar\varphi_j = \varphi_j$, and the third identity is the book's
$r^*_j = \varphi_j(A^T) r^*_0$.

The starred recurrences are the unstarred ones with $A$ replaced by $A^H$ and every coefficient
conjugated, and this gives the conjugate polynomials. No hypothesis is needed. The proof
specializes `BCG.residual_eq_aeval`.

**Generalization.** Lean conjugates the coefficients on the dual side so polynomial evaluation can
be moved across the complex inner product using the adjoint. The real restriction gives the source's
transpose relation.
-/
theorem bcg_residual_eq_aeval (j : ℕ) :
    (bcg A b x₀ rs₀ j).r = aeval (op A) (bcgResidualPoly A b x₀ rs₀ j) (b - op A x₀) ∧
      (bcg A b x₀ rs₀ j).p = aeval (op A) (bcgDirectionPoly A b x₀ rs₀ j) (b - op A x₀) ∧
      (bcg A b x₀ rs₀ j).rs
        = aeval (op Aᴴ) ((bcgResidualPoly A b x₀ rs₀ j).map (starRingEnd 𝕜)) rs₀ ∧
      (bcg A b x₀ rs₀ j).ps
        = aeval (op Aᴴ) ((bcgDirectionPoly A b x₀ rs₀ j).map (starRingEnd 𝕜)) rs₀ := by
  rw [bcg_eq]
  exact BCG.residual_eq_aeval (op A) (op Aᴴ) b x₀ rs₀ j

end BCGPolynomials

/-! ### §7.4.1: Algorithm 7.6, the conjugate gradient squared algorithm -/

section CGS

/-- **Algorithm 7.6** of [saad2003iterative], the state of CGS: the vectors $(x_j, r_j, u_j, p_j)$.
The auxiliary vector $q_j$ of line 5 is computed from the state by `SaadSparse.Chapter07.cgsQ`.

This is the backbone record `CGS.State`. -/
abbrev CGSState (E : Type*) := CGS.State E

/-- One pass through lines 4–10 of Algorithm 7.6 (CGS). From the state $(x_j, r_j, u_j, p_j)$ it
computes $\alpha_j = (r_j, r^*_0)/(Ap_j, r^*_0)$, $q_j = u_j - \alpha_j A p_j$,
$x_{j+1} = x_j + \alpha_j (u_j + q_j)$, $r_{j+1} = r_j - \alpha_j A (u_j + q_j)$,
$\beta_j = (r_{j+1}, r^*_0)/(r_j, r^*_0)$, $u_{j+1} = r_{j+1} + \beta_j q_j$ and $p_{j+1} =
u_{j+1} + \beta_j (q_j + \beta_j p_j)$. A division by zero gives $0$.

**Reading.** The recurrence also applies over the complex field. Lean defines it at every index
without a convergence test and returns zero for a quotient with zero denominator.
-/
noncomputable def cgsStep (A : Matrix (Fin n) (Fin n) 𝕜) (rs₀ : EuclideanSpace 𝕜 (Fin n))
    (s : CGSState (EuclideanSpace 𝕜 (Fin n))) : CGSState (EuclideanSpace 𝕜 (Fin n)) :=
  let α : 𝕜 := inner 𝕜 rs₀ s.r / inner 𝕜 rs₀ (op A s.p)
  let q : EuclideanSpace 𝕜 (Fin n) := s.u - α • op A s.p
  let r : EuclideanSpace 𝕜 (Fin n) := s.r - α • op A (s.u + q)
  let β : 𝕜 := inner 𝕜 rs₀ r / inner 𝕜 rs₀ s.r
  let u : EuclideanSpace 𝕜 (Fin n) := r + β • q
  { x := s.x + α • (s.u + q), r := r, u := u, p := u + β • (q + β • s.p) }

/-- **Algorithm 7.6** of [saad2003iterative] (CGS, Sonneveld). Let $A \in \mathbb{K}^{n \times n}$
and $b, x_0, r^*_0 \in \mathbb{K}^n$, with $r^*_0$ arbitrary. The state after $0$ steps is
$(x_0, r_0, r_0, r_0)$ with $r_0 = b - Ax_0$, which is $p_0 = u_0 = r_0$ of lines 1 and 2. The
state after $k + 1$ steps is `SaadSparse.Chapter07.cgsStep` applied to the state after $k$
steps.

**Reading.** The recurrence also applies over the complex field. Lean defines it at every index
without a convergence test and returns zero for a quotient with zero denominator.
-/
noncomputable def cgs (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ rs₀ : EuclideanSpace 𝕜 (Fin n)) :
    ℕ → CGSState (EuclideanSpace 𝕜 (Fin n))
  | 0 => { x := x₀, r := b - op A x₀, u := b - op A x₀, p := b - op A x₀ }
  | k + 1 => cgsStep A rs₀ (cgs A b x₀ rs₀ k)

variable (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ rs₀ : EuclideanSpace 𝕜 (Fin n))

/-- Lines 1 and 2 of Algorithm 7.6: the initial state of CGS is $(x_0, r_0, r_0, r_0)$ with
$r_0 = b - Ax_0$. -/
@[simp] theorem cgs_zero :
    cgs A b x₀ rs₀ 0 = { x := x₀, r := b - op A x₀, u := b - op A x₀, p := b - op A x₀ } := rfl

/-- Each step of Algorithm 7.6 is one application of `SaadSparse.Chapter07.cgsStep`.

**Reading.** The recurrence also applies over the complex field. Lean defines it at every index
without a convergence test and returns zero for a quotient with zero denominator.
-/
theorem cgs_succ (k : ℕ) : cgs A b x₀ rs₀ (k + 1) = cgsStep A rs₀ (cgs A b x₀ rs₀ k) := rfl

/-- Algorithm 7.6 is the backbone CGS iteration: for every $k$, the state
`SaadSparse.Chapter07.cgs A b x₀ rs₀ k` equals `CGS.iterate (op A) b x₀ rs₀ k`. -/
theorem cgs_eq (k : ℕ) : cgs A b x₀ rs₀ k = CGS.iterate (op A) b x₀ rs₀ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [cgs_succ, ih, CGS.iterate_succ]; rfl

/-- Line 4 of Algorithm 7.6: the step length $\alpha_j = (r_j, r^*_0)/(Ap_j, r^*_0)$, computed from
the state of CGS after $j$ steps.

**Reading.** The recurrence also applies over the complex field. Lean defines it at every index
without a convergence test and returns zero for a quotient with zero denominator.
-/
noncomputable def cgsAlpha (j : ℕ) : 𝕜 :=
  inner 𝕜 rs₀ (cgs A b x₀ rs₀ j).r / inner 𝕜 rs₀ (op A (cgs A b x₀ rs₀ j).p)

/-- Line 8 of Algorithm 7.6: the coefficient $\beta_j = (r_{j+1}, r^*_0)/(r_j, r^*_0)$, computed
from the states of CGS after $j$ and $j + 1$ steps.

**Reading.** The recurrence also applies over the complex field. Lean defines it at every index
without a convergence test and returns zero for a quotient with zero denominator.
-/
noncomputable def cgsBeta (j : ℕ) : 𝕜 :=
  inner 𝕜 rs₀ (cgs A b x₀ rs₀ (j + 1)).r / inner 𝕜 rs₀ (cgs A b x₀ rs₀ j).r

/-- **Algorithm 7.6** of [saad2003iterative], line 5: the auxiliary vector $$q_j = u_j - \alpha_j A
p_j.$$

**Reading.** The recurrence also applies over the complex field. Lean defines it at every index
without a convergence test and returns zero for a quotient with zero denominator.
-/
noncomputable def cgsQ (j : ℕ) : EuclideanSpace 𝕜 (Fin n) :=
  (cgs A b x₀ rs₀ j).u - cgsAlpha A b x₀ rs₀ j • op A (cgs A b x₀ rs₀ j).p

/-- The step length $\alpha_j$ of Algorithm 7.6 is the backbone `CGS.alpha`. -/
theorem cgsAlpha_eq (j : ℕ) : cgsAlpha A b x₀ rs₀ j = CGS.alpha (op A) b x₀ rs₀ j := by
  rw [cgsAlpha, CGS.alpha, cgs_eq]

/-- The coefficient $\beta_j$ of Algorithm 7.6 is the backbone `CGS.beta`. -/
theorem cgsBeta_eq (j : ℕ) : cgsBeta A b x₀ rs₀ j = CGS.beta (op A) b x₀ rs₀ j := by
  rw [cgsBeta, CGS.beta, cgs_eq, cgs_eq]

/-- The auxiliary vector $q_j$ of Algorithm 7.6 is the backbone `CGS.q`. -/
theorem cgsQ_eq (j : ℕ) : cgsQ A b x₀ rs₀ j = CGS.q (op A) b x₀ rs₀ j := by
  rw [cgsQ, CGS.q, cgsAlpha_eq, cgs_eq]

/-- Line 6 of Algorithm 7.6: $x_{j+1} = x_j + \alpha_j (u_j + q_j)$.

**Reading.** The recurrence also applies over the complex field. Lean defines it at every index
without a convergence test and returns zero for a quotient with zero denominator.
-/
theorem cgs_succ_x (j : ℕ) : (cgs A b x₀ rs₀ (j + 1)).x =
    (cgs A b x₀ rs₀ j).x
      + cgsAlpha A b x₀ rs₀ j • ((cgs A b x₀ rs₀ j).u + cgsQ A b x₀ rs₀ j) := rfl

/-- Line 7 of Algorithm 7.6: $r_{j+1} = r_j - \alpha_j A (u_j + q_j)$.

**Reading.** The recurrence also applies over the complex field. Lean defines it at every index
without a convergence test and returns zero for a quotient with zero denominator.
-/
theorem cgs_succ_r (j : ℕ) : (cgs A b x₀ rs₀ (j + 1)).r =
    (cgs A b x₀ rs₀ j).r
      - cgsAlpha A b x₀ rs₀ j • op A ((cgs A b x₀ rs₀ j).u + cgsQ A b x₀ rs₀ j) := rfl

/-- Line 9 of Algorithm 7.6: $u_{j+1} = r_{j+1} + \beta_j q_j$.

**Reading.** The recurrence also applies over the complex field. Lean defines it at every index
without a convergence test and returns zero for a quotient with zero denominator.
-/
theorem cgs_succ_u (j : ℕ) : (cgs A b x₀ rs₀ (j + 1)).u =
    (cgs A b x₀ rs₀ (j + 1)).r + cgsBeta A b x₀ rs₀ j • cgsQ A b x₀ rs₀ j := rfl

/-- Line 10 of Algorithm 7.6: $p_{j+1} = u_{j+1} + \beta_j (q_j + \beta_j p_j)$.

**Reading.** The recurrence also applies over the complex field. Lean defines it at every index
without a convergence test and returns zero for a quotient with zero denominator.
-/
theorem cgs_succ_p (j : ℕ) : (cgs A b x₀ rs₀ (j + 1)).p =
    (cgs A b x₀ rs₀ (j + 1)).u
      + cgsBeta A b x₀ rs₀ j • (cgsQ A b x₀ rs₀ j + cgsBeta A b x₀ rs₀ j • (cgs A b x₀ rs₀ j).p) :=
  rfl

/-- The vector $r_j$ of Algorithm 7.6 is the true residual $b - Ax_j$ of its iterate $x_j$. -/
theorem cgs_residual (j : ℕ) : (cgs A b x₀ rs₀ j).r = b - op A (cgs A b x₀ rs₀ j).x := by
  rw [cgs_eq]
  exact CGS.r_eq_sub_apply_x (op A) b x₀ rs₀ j

/-- Let $A \in \mathbb{K}^{n \times n}$, let $p$ and $q$ be polynomials, and let
$v, w \in \mathbb{K}^n$. Then $$(p(A) v, \bar q(A^H) w) = ((qp)(A) v, w),$$ where $\bar q$ is
$q$ with conjugated coefficients. This is the step that removes the transpose from the BCG
coefficients: it turns $\alpha_j = (\varphi_j(A) r_0, \varphi_j(A^H) r^*_0)/(A \pi_j(A) r_0,
\pi_j(A^H) r^*_0)$ into $(\varphi_j^2(A) r_0, r^*_0)/(A \pi_j^2(A) r_0, r^*_0)$.

The proof specializes `BiLanczos.inner_aeval_map_eq` for the operators $A$ and $A^H$.

**Generalization.** Lean conjugates the coefficients on the dual side so polynomial evaluation can
be moved across the complex inner product using the adjoint. The real restriction gives the source's
transpose relation.
-/
theorem inner_aeval_conjTranspose_aeval (p q : 𝕜[X]) (v w : EuclideanSpace 𝕜 (Fin n)) :
    inner 𝕜 (aeval (op Aᴴ) (q.map (starRingEnd 𝕜)) w) (aeval (op A) p v)
      = inner 𝕜 w (aeval (op A) (q * p) v) := by
  rw [BiLanczos.inner_aeval_map_eq (LinearMap.isAdjointPair_inner_iff'.2 (inner_op_conjTranspose A))
    q, map_mul, Module.End.mul_apply]

/-- **Equations (7.40)–(7.45)** of [saad2003iterative]: Algorithm 7.6 computes the squared BCG
polynomials. Let $A \in \mathbb{K}^{n \times n}$ and $b, x_0, r^*_0 \in \mathbb{K}^n$, and let
$\varphi_j$, $\pi_j$, $\alpha_j$ and $\beta_j$ be the BCG polynomials and coefficients for the
same data. Then for every $j$ the vectors of Algorithm 7.6 are $$r_j = \varphi_j^2(A) r_0, \quad
p_j = \pi_j^2(A) r_0, \quad u_j = \varphi_j(A) \pi_j(A) r_0, \quad q_j = \varphi_{j+1}(A)
\pi_j(A) r_0,$$ and the coefficients $\alpha_j$ and $\beta_j$ of Algorithm 7.6 are the BCG
coefficients. Thus Algorithm 7.6 gives the residual $\varphi_j^2(A) r_0$ of (7.34) without any
product with $A^H$.

No hypothesis is needed: the coefficients agree also where both are $0/0$, which Lean evaluates
to $0$. The proof specializes `CGS.residual_eq_aeval_sq`.

**Generalization.** The polynomial and coefficient identities relate both totalized recurrences,
including steps whose projected quotient is zero by totalization. The text derives them for active
real iterations.
-/
theorem cgs_residual_eq (j : ℕ) :
    (cgs A b x₀ rs₀ j).r = aeval (op A) (bcgResidualPoly A b x₀ rs₀ j ^ 2) (b - op A x₀) ∧
      (cgs A b x₀ rs₀ j).p = aeval (op A) (bcgDirectionPoly A b x₀ rs₀ j ^ 2) (b - op A x₀) ∧
      (cgs A b x₀ rs₀ j).u
          = aeval (op A) (bcgResidualPoly A b x₀ rs₀ j * bcgDirectionPoly A b x₀ rs₀ j)
            (b - op A x₀) ∧
        cgsQ A b x₀ rs₀ j
          = aeval (op A) (bcgResidualPoly A b x₀ rs₀ (j + 1) * bcgDirectionPoly A b x₀ rs₀ j)
            (b - op A x₀) ∧
        cgsAlpha A b x₀ rs₀ j = bcgAlpha A b x₀ rs₀ j ∧
        cgsBeta A b x₀ rs₀ j = bcgBeta A b x₀ rs₀ j := by
  rw [cgsQ_eq, cgsAlpha_eq, cgsBeta_eq, cgs_eq]
  exact CGS.residual_eq_aeval_sq (LinearMap.isAdjointPair_inner_iff'.2 (inner_op_conjTranspose A)) j

end CGS

/-! ### §7.4.2: Algorithm 7.7, BICGSTAB -/

section BICGSTAB

/-- **Algorithm 7.7** of [saad2003iterative], the state of BICGSTAB: the vectors $(x_j, r_j, p_j)$.
The half-step residual $s_j$ of line 5 is computed from the state by
`SaadSparse.Chapter07.bicgstabS`.

This is the backbone record `BiCGSTAB.State`. -/
abbrev BICGSTABState (E : Type*) := BiCGSTAB.State E

/-- One pass through lines 4–10 of Algorithm 7.7 (BICGSTAB). From the state $(x_j, r_j, p_j)$ it
computes $\alpha_j = (r_j, r^*_0)/(Ap_j, r^*_0)$, $s_j = r_j - \alpha_j A p_j$,
$\omega_j = (s_j, As_j)/(As_j, As_j)$, $x_{j+1} = x_j + \alpha_j p_j + \omega_j s_j$,
$r_{j+1} = s_j - \omega_j A s_j$, $\beta_j = ((r_{j+1}, r^*_0)/(r_j, r^*_0))
(\alpha_j/\omega_j)$ and $p_{j+1} = r_{j+1} + \beta_j (p_j - \omega_j A p_j)$. A division by
zero gives $0$.

**Reading.** The recurrence is defined at all indices with totalized divisions, including a
vanishing stabilization step. For a complex half-step the numerator of omega uses the inner product
linear in the residual to preserve the minimization formula. Over real scalars the printed order of
the arguments is equivalent.
-/
noncomputable def bicgstabStep (A : Matrix (Fin n) (Fin n) 𝕜) (rs₀ : EuclideanSpace 𝕜 (Fin n))
    (s : BICGSTABState (EuclideanSpace 𝕜 (Fin n))) : BICGSTABState (EuclideanSpace 𝕜 (Fin n)) :=
  let α : 𝕜 := inner 𝕜 rs₀ s.r / inner 𝕜 rs₀ (op A s.p)
  let sv : EuclideanSpace 𝕜 (Fin n) := s.r - α • op A s.p
  let ω : 𝕜 := inner 𝕜 (op A sv) sv / inner 𝕜 (op A sv) (op A sv)
  let r : EuclideanSpace 𝕜 (Fin n) := sv - ω • op A sv
  let β : 𝕜 := inner 𝕜 rs₀ r / inner 𝕜 rs₀ s.r * (α / ω)
  { x := s.x + α • s.p + ω • sv, r := r, p := r + β • (s.p - ω • op A s.p) }

/-- **Algorithm 7.7** of [saad2003iterative] (BICGSTAB, van der Vorst). Let
$A \in \mathbb{K}^{n \times n}$ and $b, x_0, r^*_0 \in \mathbb{K}^n$, with $r^*_0$ arbitrary.
The state after $0$ steps is $(x_0, r_0, r_0)$ with $r_0 = b - Ax_0$, which is $p_0 = r_0$ of
lines 1 and 2. The state after $k + 1$ steps is `SaadSparse.Chapter07.bicgstabStep` applied to
the state after $k$ steps.

**Reading.** The recurrence is defined at all indices with totalized divisions, including a
vanishing stabilization step. For a complex half-step the numerator of omega uses the inner product
linear in the residual to preserve the minimization formula. Over real scalars the printed order of
the arguments is equivalent.
-/
noncomputable def bicgstab (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ rs₀ : EuclideanSpace 𝕜 (Fin n)) :
    ℕ → BICGSTABState (EuclideanSpace 𝕜 (Fin n))
  | 0 => { x := x₀, r := b - op A x₀, p := b - op A x₀ }
  | k + 1 => bicgstabStep A rs₀ (bicgstab A b x₀ rs₀ k)

variable (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ rs₀ : EuclideanSpace 𝕜 (Fin n))

/-- Lines 1 and 2 of Algorithm 7.7: the initial state of BICGSTAB is $(x_0, r_0, r_0)$ with
$r_0 = b - Ax_0$. -/
@[simp] theorem bicgstab_zero :
    bicgstab A b x₀ rs₀ 0 = { x := x₀, r := b - op A x₀, p := b - op A x₀ } := rfl

/-- Each step of Algorithm 7.7 is one application of `SaadSparse.Chapter07.bicgstabStep`.

**Reading.** The recurrence is defined at all indices with totalized divisions, including a
vanishing stabilization step. For a complex half-step the numerator of omega uses the inner product
linear in the residual to preserve the minimization formula. Over real scalars the printed order of
the arguments is equivalent.
-/
theorem bicgstab_succ (k : ℕ) :
    bicgstab A b x₀ rs₀ (k + 1) = bicgstabStep A rs₀ (bicgstab A b x₀ rs₀ k) := rfl

/-- Algorithm 7.7 is the backbone BICGSTAB iteration: for every $k$, the state
`SaadSparse.Chapter07.bicgstab A b x₀ rs₀ k` equals `BiCGSTAB.iterate (op A) b x₀ rs₀ k`. -/
theorem bicgstab_eq (k : ℕ) : bicgstab A b x₀ rs₀ k = BiCGSTAB.iterate (op A) b x₀ rs₀ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [bicgstab_succ, ih, BiCGSTAB.iterate_succ]; rfl

/-- Line 4 of Algorithm 7.7: the step length $\alpha_j = (r_j, r^*_0)/(Ap_j, r^*_0)$, computed from
the state of BICGSTAB after $j$ steps.

**Reading.** The recurrence is defined at all indices with totalized divisions, including a
vanishing stabilization step. For a complex half-step the numerator of omega uses the inner product
linear in the residual to preserve the minimization formula. Over real scalars the printed order of
the arguments is equivalent.
-/
noncomputable def bicgstabAlpha (j : ℕ) : 𝕜 :=
  inner 𝕜 rs₀ (bicgstab A b x₀ rs₀ j).r / inner 𝕜 rs₀ (op A (bicgstab A b x₀ rs₀ j).p)

/-- **Algorithm 7.7** of [saad2003iterative], line 5: the half-step residual $$s_j = r_j - \alpha_j
A p_j.$$

**Reading.** The recurrence is defined at all indices with totalized divisions, including a
vanishing stabilization step. For a complex half-step the numerator of omega uses the inner product
linear in the residual to preserve the minimization formula. Over real scalars the printed order of
the arguments is equivalent.
-/
noncomputable def bicgstabS (j : ℕ) : EuclideanSpace 𝕜 (Fin n) :=
  (bicgstab A b x₀ rs₀ j).r - bicgstabAlpha A b x₀ rs₀ j • op A (bicgstab A b x₀ rs₀ j).p

/-- **Algorithm 7.7** of [saad2003iterative], line 6: the stabilizing step length $$\omega_j =
\frac{(s_j, As_j)}{(As_j, As_j)}.$$ Over $\mathbb{R}$ this is the formula
$(As_j, s_j)/(As_j, As_j)$ of the book. Over $\mathbb{C}$ the order of the numerator is the one
for which $\omega_j$ minimizes $\|s_j - \omega A s_j\|_2$
(`SaadSparse.Chapter07.equation_7_55`).

The numerator is `inner 𝕜 (A s) s`, which in the inner product $(x, y) = \sum_i x_i \bar y_i$ of
the book is $(s_j, As_j)$. When $As_j = 0$, Lean's division by zero gives $\omega_j = 0$.

**Reading.** The recurrence is defined at all indices with totalized divisions, including a
vanishing stabilization step. For a complex half-step the numerator of omega uses the inner product
linear in the residual to preserve the minimization formula. Over real scalars the printed order of
the arguments is equivalent.
-/
noncomputable def bicgstabOmega (j : ℕ) : 𝕜 :=
  inner 𝕜 (op A (bicgstabS A b x₀ rs₀ j)) (bicgstabS A b x₀ rs₀ j) /
    inner 𝕜 (op A (bicgstabS A b x₀ rs₀ j)) (op A (bicgstabS A b x₀ rs₀ j))

/-- Line 9 of Algorithm 7.7: the coefficient $\beta_j = ((r_{j+1}, r^*_0)/(r_j, r^*_0))
(\alpha_j/\omega_j)$.

**Reading.** The recurrence is defined at all indices with totalized divisions, including a
vanishing stabilization step. For a complex half-step the numerator of omega uses the inner product
linear in the residual to preserve the minimization formula. Over real scalars the printed order of
the arguments is equivalent.
-/
noncomputable def bicgstabBeta (j : ℕ) : 𝕜 :=
  inner 𝕜 rs₀ (bicgstab A b x₀ rs₀ (j + 1)).r / inner 𝕜 rs₀ (bicgstab A b x₀ rs₀ j).r
    * (bicgstabAlpha A b x₀ rs₀ j / bicgstabOmega A b x₀ rs₀ j)

/-- The step length $\alpha_j$ of Algorithm 7.7 is the backbone `BiCGSTAB.alpha`. -/
theorem bicgstabAlpha_eq (j : ℕ) :
    bicgstabAlpha A b x₀ rs₀ j = BiCGSTAB.alpha (op A) b x₀ rs₀ j := by
  rw [bicgstabAlpha, BiCGSTAB.alpha, bicgstab_eq]

/-- The half-step residual $s_j$ of Algorithm 7.7 is the backbone `BiCGSTAB.s`. -/
theorem bicgstabS_eq (j : ℕ) : bicgstabS A b x₀ rs₀ j = BiCGSTAB.s (op A) b x₀ rs₀ j := by
  rw [bicgstabS, BiCGSTAB.s, bicgstabAlpha_eq, bicgstab_eq]

/-- The step length $\omega_j$ of Algorithm 7.7 is the backbone `BiCGSTAB.omega`. -/
theorem bicgstabOmega_eq (j : ℕ) :
    bicgstabOmega A b x₀ rs₀ j = BiCGSTAB.omega (op A) b x₀ rs₀ j := by
  rw [bicgstabOmega, BiCGSTAB.omega, bicgstabS_eq]

/-- Line 7 of Algorithm 7.7: $x_{j+1} = x_j + \alpha_j p_j + \omega_j s_j$.

**Generalization.** The forms hold over the complex field at every index of the totalized
recurrence. The source describes the executed real iteration.
-/
theorem bicgstab_succ_x (j : ℕ) : (bicgstab A b x₀ rs₀ (j + 1)).x =
    (bicgstab A b x₀ rs₀ j).x + bicgstabAlpha A b x₀ rs₀ j • (bicgstab A b x₀ rs₀ j).p
      + bicgstabOmega A b x₀ rs₀ j • bicgstabS A b x₀ rs₀ j := rfl

/-- Line 8 of Algorithm 7.7: $r_{j+1} = s_j - \omega_j A s_j$.

**Generalization.** The forms hold over the complex field at every index of the totalized
recurrence. The source describes the executed real iteration.
-/
theorem bicgstab_succ_r (j : ℕ) : (bicgstab A b x₀ rs₀ (j + 1)).r =
    bicgstabS A b x₀ rs₀ j - bicgstabOmega A b x₀ rs₀ j • op A (bicgstabS A b x₀ rs₀ j) := rfl

/-- Line 10 of Algorithm 7.7: $p_{j+1} = r_{j+1} + \beta_j (p_j - \omega_j A p_j)$.

**Generalization.** The forms hold over the complex field at every index of the totalized
recurrence. The source describes the executed real iteration.
-/
theorem bicgstab_succ_p (j : ℕ) : (bicgstab A b x₀ rs₀ (j + 1)).p =
    (bicgstab A b x₀ rs₀ (j + 1)).r + bicgstabBeta A b x₀ rs₀ j •
      ((bicgstab A b x₀ rs₀ j).p
        - bicgstabOmega A b x₀ rs₀ j • op A (bicgstab A b x₀ rs₀ j).p) := rfl

/-- The vector $r_j$ of Algorithm 7.7 is the true residual $b - Ax_j$ of its iterate $x_j$. -/
theorem bicgstab_residual (j : ℕ) :
    (bicgstab A b x₀ rs₀ j).r = b - op A (bicgstab A b x₀ rs₀ j).x := by
  rw [bicgstab_eq]
  exact BiCGSTAB.r_eq_sub_apply_x (op A) b x₀ rs₀ j

/-- **Equation (7.47)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$ and
$b, x_0, r^*_0 \in \mathbb{K}^n$. The **stabilizing polynomial** $\psi_j$ of BICGSTAB is defined
by $$\psi_0 = 1, \qquad \psi_{j+1}(t) = (1 - \omega_j t) \, \psi_j(t),$$ where $\omega_j$ are
the step lengths that Algorithm 7.7 computes.

The definition is the backbone `BiCGSTAB.stabPoly`. -/
noncomputable def bicgstabPoly (j : ℕ) : 𝕜[X] := BiCGSTAB.stabPoly (op A) b x₀ rs₀ j

/-- The stabilizing polynomial starts with $\psi_0 = 1$. -/
@[simp] theorem bicgstabPoly_zero : bicgstabPoly A b x₀ rs₀ 0 = 1 := rfl

/-- Equation (7.47): $\psi_{j+1}(t) = (1 - \omega_j t) \, \psi_j(t)$. -/
theorem bicgstabPoly_succ (j : ℕ) : bicgstabPoly A b x₀ rs₀ (j + 1) =
    (1 - C (bicgstabOmega A b x₀ rs₀ j) * X) * bicgstabPoly A b x₀ rs₀ j := by
  rw [bicgstabPoly, bicgstabPoly, BiCGSTAB.stabPoly_succ, bicgstabOmega_eq]

/-- The stabilizing polynomial $\psi_j$ has degree at most $j$. -/
theorem bicgstabPoly_natDegree_le (j : ℕ) : (bicgstabPoly A b x₀ rs₀ j).natDegree ≤ j :=
  BiCGSTAB.stabPoly_natDegree_le _ _ _ _ j

/-- The coefficients $\eta_1^{(j)}$ of $t^j$ in $\psi_j$ satisfy
$\eta_1^{(j+1)} = -\omega_j \eta_1^{(j)}$. This is the second of the two relations that the
derivation of (7.53) compares. -/
theorem bicgstabPoly_coeff_succ (j : ℕ) :
    (bicgstabPoly A b x₀ rs₀ (j + 1)).coeff (j + 1) =
      -bicgstabOmega A b x₀ rs₀ j * (bicgstabPoly A b x₀ rs₀ j).coeff j := by
  rw [bicgstabOmega_eq]
  exact BiCGSTAB.stabPoly_coeff_succ _ _ _ _ j

/-- If $\omega_i \neq 0$ for every $i < j$, then the coefficient
$\eta_1^{(j)} = \prod_{i<j} (-\omega_i)$ of $t^j$ in $\psi_j$ is nonzero. -/
theorem bicgstabPoly_coeff_ne_zero {j : ℕ}
    (hω : ∀ i < j, bicgstabOmega A b x₀ rs₀ i ≠ 0) :
    (bicgstabPoly A b x₀ rs₀ j).coeff j ≠ 0 :=
  BiCGSTAB.stabPoly_coeff_ne_zero _ _ _ _ fun i hi => bicgstabOmega_eq A b x₀ rs₀ i ▸ hω i hi

variable {A b x₀ rs₀}

/-- **Equations (7.46) and (7.52)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$ and
$b, x_0, r^*_0 \in \mathbb{K}^n$. Assume that Algorithm 7.3 does not break down before step $m$
and that $\omega_i \neq 0$ for every $i < m$. Then for every $j \le m$ the vectors of Algorithm
7.7 are $$r_j = \psi_j(A) \varphi_j(A) r_0 \quad\text{and}\quad p_j = \psi_j(A) \pi_j(A) r_0,$$
where $\varphi_j$ and $\pi_j$ are the BCG polynomials for the same data.

The proof is an induction that carries the identities of the coefficients
(`SaadSparse.Chapter07.equation_7_53`) with it, because $\varphi_{j+1}$ and $\pi_{j+1}$ are
built from the BCG coefficients while Algorithm 7.7 computes its own. It specializes
`BiCGSTAB.residual_eq`.

**Reading.** The comparison specifies successful BCG steps and nonzero stabilization coefficients
throughout the relevant prefix. These conditions make the leading coefficients and quotients used in
the source's calculation nonzero. The comparison extends to complex scalars.
-/
theorem bicgstab_residual_eq {m : ℕ} (h : BCGNoBreakdown A b x₀ rs₀ m)
    (hω : ∀ i < m, bicgstabOmega A b x₀ rs₀ i ≠ 0) :
    ∀ j ≤ m, (bicgstab A b x₀ rs₀ j).r
        = aeval (op A) (bicgstabPoly A b x₀ rs₀ j * bcgResidualPoly A b x₀ rs₀ j) (b - op A x₀) ∧
      (bicgstab A b x₀ rs₀ j).p
        = aeval (op A) (bicgstabPoly A b x₀ rs₀ j * bcgDirectionPoly A b x₀ rs₀ j)
            (b - op A x₀) := by
  intro j hj
  rw [bicgstab_eq]
  exact BiCGSTAB.residual_eq h.toBCG
    (fun i hi => bicgstabOmega_eq A b x₀ rs₀ i ▸ hω i hi) hj

/-- **Equations (7.53)–(7.54)** of [saad2003iterative]: the BCG coefficients can be computed from
the BICGSTAB vectors. Let $A \in \mathbb{K}^{n \times n}$ and $b, x_0, r^*_0 \in \mathbb{K}^n$.
Assume that Algorithm 7.3 does not break down before step $m$ and that $\omega_i \neq 0$ for
every $i < m$, and let $j < m$. Let $\tilde\rho_j = (r_j, r^*_0)$, where $r_j$ and $p_j$ are the
vectors of Algorithm 7.7. Then the BCG coefficients are $$\alpha_j = \frac{\tilde\rho_j}{(Ap_j,
r^*_0)} \quad\text{and}\quad \beta_j = \frac{\tilde\rho_{j+1}}{\tilde\rho_j} \cdot
\frac{\alpha_j}{\omega_j}.$$

The proof replaces $\psi_j(A^H) r^*_0$ and $\varphi_j(A^H) r^*_0$ by their leading terms. This
is correct because the BCG vectors $r_j$ and $Ap_j$ are orthogonal to $(A^H)^k r^*_0$ for
$k < j$. It then compares the two leading coefficients,
$\eta_1^{(j+1)} = -\omega_j \eta_1^{(j)}$ and $\gamma_1^{(j+1)} = -\alpha_j \gamma_1^{(j)}$. The
proof specializes `BiCGSTAB.alpha_eq` and `BiCGSTAB.beta_eq`.

**Reading.** The comparison specifies successful BCG steps and nonzero stabilization coefficients
throughout the relevant prefix. These conditions make the leading coefficients and quotients used in
the source's calculation nonzero. The comparison extends to complex scalars.
-/
theorem equation_7_53 {m : ℕ} (h : BCGNoBreakdown A b x₀ rs₀ m)
    (hω : ∀ i < m, bicgstabOmega A b x₀ rs₀ i ≠ 0) {j : ℕ} (hj : j < m) :
    bcgAlpha A b x₀ rs₀ j
        = inner 𝕜 rs₀ (bicgstab A b x₀ rs₀ j).r
          / inner 𝕜 rs₀ (op A (bicgstab A b x₀ rs₀ j).p) ∧
      bcgBeta A b x₀ rs₀ j
        = inner 𝕜 rs₀ (bicgstab A b x₀ rs₀ (j + 1)).r / inner 𝕜 rs₀ (bicgstab A b x₀ rs₀ j).r
          * (bcgAlpha A b x₀ rs₀ j / bicgstabOmega A b x₀ rs₀ j) := by
  have hω' : ∀ i < m, BiCGSTAB.omega (op A) b x₀ rs₀ i ≠ 0 :=
    fun i hi => bicgstabOmega_eq A b x₀ rs₀ i ▸ hω i hi
  have hα := BiCGSTAB.alpha_eq h.toBCG hω' hj
  have hβ := BiCGSTAB.beta_eq h.toBCG hω' hj
  rw [BiCGSTAB.beta, hα] at hβ
  rw [BiCGSTAB.alpha] at hα
  simp only [bicgstabOmega_eq, bicgstab_eq]
  exact ⟨hα.symm, hβ.symm⟩

variable (A b x₀ rs₀)

/-- **Equation (7.55)** of [saad2003iterative]: $\omega_j$ is a steepest-descent step along the
residual. Let $A \in \mathbb{K}^{n \times n}$ and $b, x_0, r^*_0 \in \mathbb{K}^n$, and let
$x_{j+1/2} = x_j + \alpha_j p_j$ be the half-step iterate of Algorithm 7.7, whose residual is
$s_j$. Then for every $j$, $x_{j+1}$ is the minimal residual step from $x_{j+1/2}$, and
$x_{j+1}$ minimizes $\|b - Ax\|_2$ over $x \in x_{j+1/2} + \operatorname{span}\{s_j\}$.
Equivalently, $\omega_j$ minimizes $\|(I - \omega A) s_j\|_2$ over $\omega \in \mathbb{K}$.

The minimal residual step is `Projection.minResStep`, the one-dimensional projection step along
the residual $r = b - Ax$ orthogonally to $Ar$. The minimization is `IsMinResidual`.

**Generalization.** The exact result minimizes over complex scalar multiples as well as real ones.
When $As_j=0$, the residual norm is constant along the trial line and Lean's totalized choice of
zero is one minimizer.
-/
theorem equation_7_55 (j : ℕ) :
    (bicgstab A b x₀ rs₀ (j + 1)).x
        = Projection.minResStep (op A) b
            ((bicgstab A b x₀ rs₀ j).x + bicgstabAlpha A b x₀ rs₀ j • (bicgstab A b x₀ rs₀ j).p) ∧
      IsMinResidual (op A) b
        ((bicgstab A b x₀ rs₀ j).x + bicgstabAlpha A b x₀ rs₀ j • (bicgstab A b x₀ rs₀ j).p)
        (𝕜 ∙ bicgstabS A b x₀ rs₀ j) (bicgstab A b x₀ rs₀ (j + 1)).x := by
  have hres : b - op A ((bicgstab A b x₀ rs₀ j).x
      + bicgstabAlpha A b x₀ rs₀ j • (bicgstab A b x₀ rs₀ j).p) = bicgstabS A b x₀ rs₀ j := by
    rw [bicgstabS, bicgstab_residual, map_add, map_smul]
    abel
  have hstep : (bicgstab A b x₀ rs₀ (j + 1)).x
      = Projection.minResStep (op A) b
        ((bicgstab A b x₀ rs₀ j).x + bicgstabAlpha A b x₀ rs₀ j • (bicgstab A b x₀ rs₀ j).p) := by
    simp only [bicgstabAlpha_eq, bicgstab_eq]
    exact BiCGSTAB.iterate_succ_x_eq_minResStep _ _ _ _ j
  refine ⟨hstep, ?_⟩
  have := Projection.minResStep_isMinResidual (A := op A) (b := b)
    ((bicgstab A b x₀ rs₀ j).x + bicgstabAlpha A b x₀ rs₀ j • (bicgstab A b x₀ rs₀ j).p)
  rwa [hres, ← hstep] at this

end BICGSTAB

/-! ### §7.4.3: Algorithm 7.8, TFQMR -/

section TFQMR

/-- **Algorithm 7.8** of [saad2003iterative], the state of TFQMR after $m$ half-steps. It consists
of the vectors $x_m$, $w_m$, $u_m$, $v$ and $d_m$ and the scalars $\tau_m$, $\theta_m$,
$\eta_m$, $\rho$ and $\alpha$. The book defines $v_m$, $\rho_m$ and $\beta_m$ only at even $m$,
so the fields `v` and `ρ` carry the value from the last even index. The field `α` carries
$\alpha_{m-1}$, which by (7.65) is $\alpha_m$ when $m$ is odd.

**Reading.** Lean stores the last even rho and v, and the last computed alpha, at every half-step.
The printed algorithm gives new names to these quantities only at the steps that compute them.
-/
structure TFQMRState (𝕜 E : Type*) where
  /-- The iterate $x_m$. -/
  x : E
  /-- The auxiliary residual $w_m$, which is the CGS residual $r_m$ in the doubled-index notation.
  -/
  w : E
  /-- The direction $u_m$ of (7.65). -/
  u : E
  /-- The vector $v_{2j} = Ap_{2j}$ at the last even index $2j \le m$; the odd steps leave it
  unchanged. -/
  v : E
  /-- The search direction $d_m$ of (7.78). -/
  d : E
  /-- The quasi-residual norm $\tau_m$ of (7.82). -/
  τ : ℝ
  /-- The tangent $\theta_m$ of the rotation angle. -/
  θ : ℝ
  /-- The scalar $\eta_m = c_m^2 \alpha_{m-1}$ of (7.78). -/
  η : 𝕜
  /-- The scalar $\rho_{2j} = (w_{2j}, r^*_0)$ at the last even index $2j \le m$; the odd steps
  leave it unchanged. -/
  ρ : 𝕜
  /-- The step length $\alpha_{m-1}$. -/
  α : 𝕜

/-- Lines 5–8 of Algorithm 7.8 and (7.65): the step length $\alpha_m = \rho_m/(v_m, r^*_0)$ at even
$m$, and $\alpha_m = \alpha_{m-1}$ at odd $m$.

**Reading.** The recurrence is a total identity, with division by zero returning zero where a
quotient is used. Pairings involving the shadow vector are extended to complex scalars with
conjugation on the shadow vector.
-/
noncomputable def tfqmrStepAlpha (rs₀ : EuclideanSpace 𝕜 (Fin n)) (m : ℕ)
    (s : TFQMRState 𝕜 (EuclideanSpace 𝕜 (Fin n))) : 𝕜 :=
  if Even m then s.ρ / inner 𝕜 rs₀ s.v else s.α

/-- Line 9 of Algorithm 7.8: $w_{m+1} = w_m - \alpha_m A u_m$. -/
noncomputable def tfqmrStepW (A : Matrix (Fin n) (Fin n) 𝕜) (rs₀ : EuclideanSpace 𝕜 (Fin n))
    (m : ℕ) (s : TFQMRState 𝕜 (EuclideanSpace 𝕜 (Fin n))) : EuclideanSpace 𝕜 (Fin n) :=
  s.w - tfqmrStepAlpha rs₀ m s • op A s.u

/-- Line 15 of Algorithm 7.8: $\beta_{m-1} = \rho_{m+1}/\rho_{m-1}$ with
$\rho_{m+1} = (w_{m+1}, r^*_0)$, used at odd $m$ only.

**Reading.** The recurrence is a total identity, with division by zero returning zero where a
quotient is used. Pairings involving the shadow vector are extended to complex scalars with
conjugation on the shadow vector.
-/
noncomputable def tfqmrStepBeta (A : Matrix (Fin n) (Fin n) 𝕜) (rs₀ : EuclideanSpace 𝕜 (Fin n))
    (m : ℕ) (s : TFQMRState 𝕜 (EuclideanSpace 𝕜 (Fin n))) : 𝕜 :=
  inner 𝕜 rs₀ (tfqmrStepW A rs₀ m s) / s.ρ

/-- One pass through the loop of Algorithm 7.8 at step $m$. It computes $\alpha_m$,
$w_{m+1} = w_m - \alpha_m A u_m$, $d_{m+1} = u_m + (\theta_m^2/\alpha_m) \eta_m d_m$,
$\theta_{m+1} = \|w_{m+1}\|_2/\tau_m$, $c_{m+1} = (1 + \theta_{m+1}^2)^{-1/2}$,
$\tau_{m+1} = \tau_m \theta_{m+1} c_{m+1}$, $\eta_{m+1} = c_{m+1}^2 \alpha_m$ and
$x_{m+1} = x_m + \eta_{m+1} d_{m+1}$. At even $m$ it sets $u_{m+1} = u_m - \alpha_m v_m$. At odd
$m$ it sets $\rho_{m+1} = (w_{m+1}, r^*_0)$, $\beta_{m-1} = \rho_{m+1}/\rho_{m-1}$,
$u_{m+1} = w_{m+1} + \beta_{m-1} u_m$ and $v_{m+1} = Au_{m+1} + \beta_{m-1}(Au_m + \beta_{m-1}
v_{m-1})$. A division by zero gives $0$.

**Reading.** Each call executes one half-step without a convergence test. The book repeats the
half-steps until convergence. Lean also uses totalized division and complex shadow pairings.
-/
noncomputable def tfqmrStep (A : Matrix (Fin n) (Fin n) 𝕜) (rs₀ : EuclideanSpace 𝕜 (Fin n))
    (m : ℕ) (s : TFQMRState 𝕜 (EuclideanSpace 𝕜 (Fin n))) :
    TFQMRState 𝕜 (EuclideanSpace 𝕜 (Fin n)) :=
  let α : 𝕜 := tfqmrStepAlpha rs₀ m s
  let w : EuclideanSpace 𝕜 (Fin n) := tfqmrStepW A rs₀ m s
  let β : 𝕜 := tfqmrStepBeta A rs₀ m s
  let d : EuclideanSpace 𝕜 (Fin n) := s.u + (((s.θ ^ 2 : ℝ) : 𝕜) / α * s.η) • s.d
  let θ : ℝ := ‖w‖ / s.τ
  let c : ℝ := (Real.sqrt (1 + θ ^ 2))⁻¹
  { x := s.x + (((c ^ 2 : ℝ) : 𝕜) * α) • d
    w := w
    u := if Even m then s.u - α • s.v else w + β • s.u
    v := if Even m then s.v else op A (w + β • s.u) + β • (op A s.u + β • s.v)
    d := d
    τ := s.τ * θ * c
    θ := θ
    η := ((c ^ 2 : ℝ) : 𝕜) * α
    ρ := if Even m then s.ρ else inner 𝕜 rs₀ w
    α := α }

/-- **Algorithm 7.8** of [saad2003iterative] (TFQMR, Freund), the state after $m$ half-steps. Let
$A \in \mathbb{K}^{n \times n}$ and $b, x_0, r^*_0 \in \mathbb{K}^n$, with $r^*_0$ arbitrary.
Lines 1–3 set $w_0 = u_0 = r_0 = b - Ax_0$, $v_0 = Au_0$, $d_0 = 0$, $\tau_0 = \|r_0\|_2$,
$\theta_0 = \eta_0 = 0$ and $\rho_0 = (r_0, r^*_0)$. Each half-step is one application of
`SaadSparse.Chapter07.tfqmrStep`.

The field `α` of the initial state is $0$.

**Generalization.** The printed real initialization requires a nonzero shadow pairing. Lean accepts
every shadow vector and extends the pairing to complex scalars, consistently using the shadow vector
in the conjugate-linear slot. The extra initial alpha field is zero.
-/
noncomputable def tfqmr (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ rs₀ : EuclideanSpace 𝕜 (Fin n)) :
    ℕ → TFQMRState 𝕜 (EuclideanSpace 𝕜 (Fin n))
  | 0 =>
      { x := x₀, w := b - op A x₀, u := b - op A x₀, v := op A (b - op A x₀), d := 0,
        τ := ‖b - op A x₀‖, θ := 0, η := 0, ρ := inner 𝕜 rs₀ (b - op A x₀), α := 0 }
  | m + 1 => tfqmrStep A rs₀ m (tfqmr A b x₀ rs₀ m)

variable (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ rs₀ : EuclideanSpace 𝕜 (Fin n))

/-- Lines 1–3 of Algorithm 7.8: the initial state of TFQMR.

**Generalization.** The printed real initialization requires a nonzero shadow pairing. Lean accepts
every shadow vector and extends the pairing to complex scalars, consistently using the shadow vector
in the conjugate-linear slot. The extra initial alpha field is zero.
-/
@[simp] theorem tfqmr_zero :
    tfqmr A b x₀ rs₀ 0 =
      { x := x₀, w := b - op A x₀, u := b - op A x₀, v := op A (b - op A x₀), d := 0,
        τ := ‖b - op A x₀‖, θ := 0, η := 0, ρ := inner 𝕜 rs₀ (b - op A x₀), α := 0 } := rfl

/-- Each half-step of Algorithm 7.8 is one application of `SaadSparse.Chapter07.tfqmrStep`.

**Reading.** Each call executes one half-step without a convergence test. The book repeats the
half-steps until convergence. Lean also uses totalized division and complex shadow pairings.
-/
theorem tfqmr_succ (m : ℕ) :
    tfqmr A b x₀ rs₀ (m + 1) = tfqmrStep A rs₀ m (tfqmr A b x₀ rs₀ m) := rfl

/-- The vector $u_m$ of (7.65), from the state of Algorithm 7.8 after $m$ half-steps. -/
noncomputable abbrev tfqmrU (m : ℕ) : EuclideanSpace 𝕜 (Fin n) := (tfqmr A b x₀ rs₀ m).u

/-- The vector $w_m$ of Algorithm 7.8, which is the CGS residual $r_m$ in the doubled-index
notation. -/
noncomputable abbrev tfqmrW (m : ℕ) : EuclideanSpace 𝕜 (Fin n) := (tfqmr A b x₀ rs₀ m).w

/-- The step length $\alpha_m$ of (7.65), stored in the state of Algorithm 7.8 after $m + 1$
half-steps. -/
noncomputable abbrev tfqmrAlpha (m : ℕ) : 𝕜 := (tfqmr A b x₀ rs₀ (m + 1)).α

/-- The scalar $\tau_m$ of (7.82), the running estimate of the quasi-residual norm. -/
noncomputable abbrev tfqmrTau (m : ℕ) : ℝ := (tfqmr A b x₀ rs₀ m).τ

/-- The scalar $\theta_m$ of (7.82). -/
noncomputable abbrev tfqmrTheta (m : ℕ) : ℝ := (tfqmr A b x₀ rs₀ m).θ

/-- The scalar $c_m = (1 + \theta_m^2)^{-1/2}$ of (7.82). -/
noncomputable abbrev tfqmrC (m : ℕ) : ℝ :=
  (Real.sqrt (1 + tfqmrTheta A b x₀ rs₀ m ^ 2))⁻¹

/-- The scalar $\eta_m = c_m^2 \alpha_{m-1}$ of (7.78). -/
noncomputable abbrev tfqmrEta (m : ℕ) : 𝕜 := (tfqmr A b x₀ rs₀ m).η

/-- The direction $d_m$ of (7.78). -/
noncomputable abbrev tfqmrD (m : ℕ) : EuclideanSpace 𝕜 (Fin n) := (tfqmr A b x₀ rs₀ m).d

/-- Line 9 of Algorithm 7.8: $w_{m+1} = w_m - \alpha_m A u_m$. -/
theorem tfqmr_succ_w (m : ℕ) : tfqmrW A b x₀ rs₀ (m + 1) =
    tfqmrW A b x₀ rs₀ m - tfqmrAlpha A b x₀ rs₀ m • op A (tfqmrU A b x₀ rs₀ m) := rfl

/-- Line 9 of Algorithm 7.8: $d_{m+1} = u_m + (\theta_m^2/\alpha_m) \eta_m d_m$.

**Reading.** The recurrence is a total identity, with division by zero returning zero where a
quotient is used. Pairings involving the shadow vector are extended to complex scalars with
conjugation on the shadow vector.
-/
theorem tfqmr_succ_d (m : ℕ) : tfqmrD A b x₀ rs₀ (m + 1) =
    tfqmrU A b x₀ rs₀ m
      + (((tfqmrTheta A b x₀ rs₀ m ^ 2 : ℝ) : 𝕜) / tfqmrAlpha A b x₀ rs₀ m
        * tfqmrEta A b x₀ rs₀ m) • tfqmrD A b x₀ rs₀ m := rfl

/-- Line 10 of Algorithm 7.8: $\theta_{m+1} = \|w_{m+1}\|_2/\tau_m$.

**Reading.** The recurrence is a total identity, with division by zero returning zero where a
quotient is used. Pairings involving the shadow vector are extended to complex scalars with
conjugation on the shadow vector.
-/
theorem tfqmr_succ_theta (m : ℕ) : tfqmrTheta A b x₀ rs₀ (m + 1) =
    ‖tfqmrW A b x₀ rs₀ (m + 1)‖ / tfqmrTau A b x₀ rs₀ m := rfl

/-- Line 11 of Algorithm 7.8: $\tau_{m+1} = \tau_m \theta_{m+1} c_{m+1}$. -/
theorem tfqmr_succ_tau (m : ℕ) : tfqmrTau A b x₀ rs₀ (m + 1) =
    tfqmrTau A b x₀ rs₀ m * tfqmrTheta A b x₀ rs₀ (m + 1) * tfqmrC A b x₀ rs₀ (m + 1) := rfl

/-- Line 11 of Algorithm 7.8: $\eta_{m+1} = c_{m+1}^2 \alpha_m$. -/
theorem tfqmr_succ_eta (m : ℕ) : tfqmrEta A b x₀ rs₀ (m + 1) =
    ((tfqmrC A b x₀ rs₀ (m + 1) ^ 2 : ℝ) : 𝕜) * tfqmrAlpha A b x₀ rs₀ m := rfl

/-- Line 12 of Algorithm 7.8: $x_{m+1} = x_m + \eta_{m+1} d_{m+1}$. -/
theorem tfqmr_succ_x (m : ℕ) : (tfqmr A b x₀ rs₀ (m + 1)).x =
    (tfqmr A b x₀ rs₀ m).x + tfqmrEta A b x₀ rs₀ (m + 1) • tfqmrD A b x₀ rs₀ (m + 1) := rfl

/-- Line 6 of Algorithm 7.8 at even $m$: $\alpha_m = \rho_m/(v_m, r^*_0)$.

**Reading.** The recurrence is a total identity, with division by zero returning zero where a
quotient is used. Pairings involving the shadow vector are extended to complex scalars with
conjugation on the shadow vector.
-/
theorem tfqmr_alpha_even {m : ℕ} (hm : Even m) : tfqmrAlpha A b x₀ rs₀ m =
    (tfqmr A b x₀ rs₀ m).ρ / inner 𝕜 rs₀ (tfqmr A b x₀ rs₀ m).v := ite_eq_left hm

/-- Equation (7.65) at odd $m$: $\alpha_m = \alpha_{m-1}$. -/
theorem tfqmr_alpha_odd {m : ℕ} (hm : ¬ Even m) :
    tfqmrAlpha A b x₀ rs₀ m = (tfqmr A b x₀ rs₀ m).α := ite_eq_right hm

/-- Line 6 of Algorithm 7.8 at even $m$: $u_{m+1} = u_m - \alpha_m v_m$. -/
theorem tfqmr_succ_u_even {m : ℕ} (hm : Even m) : tfqmrU A b x₀ rs₀ (m + 1) =
    tfqmrU A b x₀ rs₀ m - tfqmrAlpha A b x₀ rs₀ m • (tfqmr A b x₀ rs₀ m).v := ite_eq_left hm

/-- At even $m$, a step of Algorithm 7.8 leaves the vector $v$ unchanged. -/
theorem tfqmr_succ_v_even {m : ℕ} (hm : Even m) :
    (tfqmr A b x₀ rs₀ (m + 1)).v = (tfqmr A b x₀ rs₀ m).v := ite_eq_left hm

/-- At even $m$, a step of Algorithm 7.8 leaves the scalar $\rho$ unchanged. -/
theorem tfqmr_succ_rho_even {m : ℕ} (hm : Even m) :
    (tfqmr A b x₀ rs₀ (m + 1)).ρ = (tfqmr A b x₀ rs₀ m).ρ := ite_eq_left hm

/-- Line 14 of Algorithm 7.8 at odd $m$: $\rho_{m+1} = (w_{m+1}, r^*_0)$.

**Reading.** The recurrence is a total identity, with division by zero returning zero where a
quotient is used. Pairings involving the shadow vector are extended to complex scalars with
conjugation on the shadow vector.
-/
theorem tfqmr_succ_rho_odd {m : ℕ} (hm : ¬ Even m) :
    (tfqmr A b x₀ rs₀ (m + 1)).ρ = inner 𝕜 rs₀ (tfqmrW A b x₀ rs₀ (m + 1)) := ite_eq_right hm

/-- Line 16 of Algorithm 7.8 at odd $m$: $u_{m+1} = w_{m+1} + \beta_{m-1} u_m$, with
$\beta_{m-1} = \rho_{m+1}/\rho_{m-1}$.

**Reading.** The recurrence is a total identity, with division by zero returning zero where a
quotient is used. Pairings involving the shadow vector are extended to complex scalars with
conjugation on the shadow vector.
-/
theorem tfqmr_succ_u_odd {m : ℕ} (hm : ¬ Even m) : tfqmrU A b x₀ rs₀ (m + 1) =
    tfqmrW A b x₀ rs₀ (m + 1)
      + (inner 𝕜 rs₀ (tfqmrW A b x₀ rs₀ (m + 1)) / (tfqmr A b x₀ rs₀ m).ρ)
        • tfqmrU A b x₀ rs₀ m := ite_eq_right hm

/-- Line 17 of Algorithm 7.8 at odd $m$: $v_{m+1} = Au_{m+1} + \beta_{m-1}(Au_m + \beta_{m-1}
v_{m-1})$, with $\beta_{m-1} = \rho_{m+1}/\rho_{m-1}$.

**Reading.** The recurrence is a total identity, with division by zero returning zero where a
quotient is used. Pairings involving the shadow vector are extended to complex scalars with
conjugation on the shadow vector.
-/
theorem tfqmr_succ_v_odd {m : ℕ} (hm : ¬ Even m) : (tfqmr A b x₀ rs₀ (m + 1)).v =
    op A (tfqmrU A b x₀ rs₀ (m + 1))
      + (inner 𝕜 rs₀ (tfqmrW A b x₀ rs₀ (m + 1)) / (tfqmr A b x₀ rs₀ m).ρ)
        • (op A (tfqmrU A b x₀ rs₀ m)
          + (inner 𝕜 rs₀ (tfqmrW A b x₀ rs₀ (m + 1)) / (tfqmr A b x₀ rs₀ m).ρ)
            • (tfqmr A b x₀ rs₀ m).v) := by
  rw [tfqmr_succ_u_odd A b x₀ rs₀ hm]
  exact ite_eq_right hm

/-- The even half-steps of Algorithm 7.8 carry the state of Algorithm 7.6: $w_{2j} = r_j$,
$u_{2j} = u_j$, $v_{2j} = Ap_j$ and $\rho_{2j} = (r_j, r^*_0)$. -/
private theorem tfqmr_even_state (j : ℕ) :
    tfqmrW A b x₀ rs₀ (2 * j) = (cgs A b x₀ rs₀ j).r ∧
      tfqmrU A b x₀ rs₀ (2 * j) = (cgs A b x₀ rs₀ j).u ∧
      (tfqmr A b x₀ rs₀ (2 * j)).v = op A (cgs A b x₀ rs₀ j).p ∧
      (tfqmr A b x₀ rs₀ (2 * j)).ρ = inner 𝕜 rs₀ (cgs A b x₀ rs₀ j).r := by
  induction j with
  | zero => exact ⟨rfl, rfl, rfl, rfl⟩
  | succ j ih =>
    obtain ⟨hw, hu, hv, hρ⟩ := ih
    have hev : Even (2 * j) := ⟨j, by ring⟩
    have hod : ¬ Even (2 * j + 1) := by rw [Nat.even_add_one, not_not]; exact hev
    have hidx : 2 * (j + 1) = 2 * j + 1 + 1 := by ring
    have hα : tfqmrAlpha A b x₀ rs₀ (2 * j) = cgsAlpha A b x₀ rs₀ j := by
      rw [tfqmr_alpha_even A b x₀ rs₀ hev, hρ, hv, cgsAlpha]
    have hα1 : tfqmrAlpha A b x₀ rs₀ (2 * j + 1) = cgsAlpha A b x₀ rs₀ j := by
      rw [tfqmr_alpha_odd A b x₀ rs₀ hod]; exact hα
    have hu1 : tfqmrU A b x₀ rs₀ (2 * j + 1) = cgsQ A b x₀ rs₀ j := by
      rw [tfqmr_succ_u_even A b x₀ rs₀ hev, hu, hv, hα, cgsQ]
    have hw1 : tfqmrW A b x₀ rs₀ (2 * j + 1)
        = (cgs A b x₀ rs₀ j).r - cgsAlpha A b x₀ rs₀ j • op A (cgs A b x₀ rs₀ j).u := by
      rw [tfqmr_succ_w A b x₀ rs₀ (2 * j), hw, hu, hα]
    have hw2 : tfqmrW A b x₀ rs₀ (2 * j + 1 + 1) = (cgs A b x₀ rs₀ (j + 1)).r := by
      rw [tfqmr_succ_w A b x₀ rs₀ (2 * j + 1), hw1, hu1, hα1, cgs_succ_r, map_add, smul_add]
      abel
    have hρ1 : (tfqmr A b x₀ rs₀ (2 * j + 1)).ρ = inner 𝕜 rs₀ (cgs A b x₀ rs₀ j).r := by
      rw [tfqmr_succ_rho_even A b x₀ rs₀ hev]; exact hρ
    have hβ : inner 𝕜 rs₀ (tfqmrW A b x₀ rs₀ (2 * j + 1 + 1)) / (tfqmr A b x₀ rs₀ (2 * j + 1)).ρ
        = cgsBeta A b x₀ rs₀ j := by
      rw [hw2, hρ1, cgsBeta]
    have hu2 : tfqmrU A b x₀ rs₀ (2 * j + 1 + 1) = (cgs A b x₀ rs₀ (j + 1)).u := by
      rw [tfqmr_succ_u_odd A b x₀ rs₀ hod, hβ, hw2, hu1, cgs_succ_u]
    refine ⟨by rw [hidx]; exact hw2, by rw [hidx]; exact hu2, ?_, ?_⟩
    · rw [hidx, tfqmr_succ_v_odd A b x₀ rs₀ hod, hβ, hu2, hu1,
        tfqmr_succ_v_even A b x₀ rs₀ hev, hv]
      simp only [cgs_succ_p, map_add, map_smul]
    · rw [hidx, tfqmr_succ_rho_odd A b x₀ rs₀ hod, hw2]

/-- **Equations (7.56)–(7.62)** of [saad2003iterative]: doubling the indices of Algorithm 7.6 gives
Algorithm 7.8. Let $A \in \mathbb{K}^{n \times n}$ and $b, x_0, r^*_0 \in \mathbb{K}^n$. For
every $j$, the state of Algorithm 7.8 after $2j$ half-steps carries the state of Algorithm 7.6
after $j$ steps, $$w_{2j} = r_j, \quad u_{2j} = u_j, \quad v_{2j} = Ap_j, \quad \rho_{2j} =
(r_j, r^*_0).$$ The odd half-step carries $u_{2j+1} = q_j$ of (7.57), and the step lengths
agree, $\alpha_{2j} = \alpha_{2j+1} = \alpha_j$, which is (7.65). On the right-hand sides,
$r_j$, $u_j$, $p_j$, $q_j$ and $\alpha_j$ are the quantities of Algorithm 7.6. -/
theorem tfqmr_eq_cgs (j : ℕ) :
    tfqmrW A b x₀ rs₀ (2 * j) = (cgs A b x₀ rs₀ j).r ∧
      tfqmrU A b x₀ rs₀ (2 * j) = (cgs A b x₀ rs₀ j).u ∧
      (tfqmr A b x₀ rs₀ (2 * j)).v = op A (cgs A b x₀ rs₀ j).p ∧
      (tfqmr A b x₀ rs₀ (2 * j)).ρ = inner 𝕜 rs₀ (cgs A b x₀ rs₀ j).r ∧
      tfqmrAlpha A b x₀ rs₀ (2 * j) = cgsAlpha A b x₀ rs₀ j ∧
      tfqmrAlpha A b x₀ rs₀ (2 * j + 1) = cgsAlpha A b x₀ rs₀ j ∧
      tfqmrU A b x₀ rs₀ (2 * j + 1) = cgsQ A b x₀ rs₀ j := by
  obtain ⟨hw, hu, hv, hρ⟩ := tfqmr_even_state A b x₀ rs₀ j
  have hev : Even (2 * j) := ⟨j, by ring⟩
  have hod : ¬ Even (2 * j + 1) := by rw [Nat.even_add_one, not_not]; exact hev
  have hα : tfqmrAlpha A b x₀ rs₀ (2 * j) = cgsAlpha A b x₀ rs₀ j := by
    rw [tfqmr_alpha_even A b x₀ rs₀ hev, hρ, hv, cgsAlpha]
  refine ⟨hw, hu, hv, hρ, hα, ?_, ?_⟩
  · rw [tfqmr_alpha_odd A b x₀ rs₀ hod]; exact hα
  · rw [tfqmr_succ_u_even A b x₀ rs₀ hev, hu, hv, hα, cgsQ]

/-- **Equations (7.66)–(7.67)** of [saad2003iterative]: the CGS iterates extended to half-steps. Let
$A \in \mathbb{K}^{n \times n}$ and $b, x_0, r^*_0 \in \mathbb{K}^n$. With the vectors $u_i$ and
the step lengths $\alpha_i$ of Algorithm 7.8, $$\tilde x_m = x_0 + U_m z_m = x_0 +
\sum_{i=0}^{m-1} \alpha_i u_i, \qquad z_m = (\alpha_0, \dots, \alpha_{m-1})^T.$$ For even $m$
these are the iterates of Algorithm 7.6 (`SaadSparse.Chapter07.cgsHalfIterate_two_mul`). The odd
ones are the intermediate iterates $x_{j+1/2} = x_j + \alpha_j u_j$, which Algorithm 7.6 does
not name. -/
noncomputable def cgsHalfIterate (m : ℕ) : EuclideanSpace 𝕜 (Fin n) :=
  x₀ + ∑ i ∈ Finset.range m, tfqmrAlpha A b x₀ rs₀ i • tfqmrU A b x₀ rs₀ i

/-- Equation (7.67): $\tilde x_{m+1} = \tilde x_m + \alpha_m u_m$. -/
theorem cgsHalfIterate_succ (m : ℕ) : cgsHalfIterate A b x₀ rs₀ (m + 1) =
    cgsHalfIterate A b x₀ rs₀ m + tfqmrAlpha A b x₀ rs₀ m • tfqmrU A b x₀ rs₀ m := by
  rw [cgsHalfIterate, cgsHalfIterate, Finset.sum_range_succ, add_assoc]

/-- **Equations (7.63)–(7.64)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$ and
$b, x_0, r^*_0 \in \mathbb{K}^n$. For every $j$, $$\tilde x_{2j} = x_j,$$ the iterate of
Algorithm 7.6 after $j$ steps: the two half-steps from $\tilde x_{2j}$ to $\tilde x_{2j+2}$
compose to one step of CGS. -/
theorem cgsHalfIterate_two_mul (j : ℕ) :
    cgsHalfIterate A b x₀ rs₀ (2 * j) = (cgs A b x₀ rs₀ j).x := by
  induction j with
  | zero => simp [cgsHalfIterate]
  | succ j ih =>
    obtain ⟨-, hu, -, -, hα, hα1, hu1⟩ := tfqmr_eq_cgs A b x₀ rs₀ j
    have hidx : 2 * (j + 1) = 2 * j + 1 + 1 := by ring
    rw [hidx, cgsHalfIterate_succ, cgsHalfIterate_succ, ih, hu, hu1, hα, hα1, cgs_succ_x,
      smul_add, add_assoc]

/-! ### (7.68)–(7.76): the two-family Hessenberg relation -/

/-- **Equations (7.72) and (7.81)** of [saad2003iterative]. For a sequence of step lengths
$\alpha_j$ and a column scaling $\delta_j$, this is the bidiagonal coefficient array
$\bar H_m = \Delta_{m+1} \bar B_m$. In $0$-based indices its entry $(i, j)$ is
$\delta_j/\alpha_j$ if $i = j$, $-\delta_{j+1}/\alpha_j$ if $i = j + 1$, and $0$ otherwise. A
division by zero gives $0$.

**Correction.** With the zero-based indexing used in the derivation, the diagonal in column $j$ is
$\delta_j/\alpha_j$ and the subdiagonal is $-\delta_{j+1}/\alpha_j$. The printed last column of
(7.81) labels the two scaling factors $\delta_m$ and $\delta_{m+1}$, one too high for the displayed
$(m+1)\times m$ block. Lean also totalizes undefined quotients.
-/
noncomputable def tfqmrCoeff (α δ : ℕ → 𝕜) : ℕ → ℕ → 𝕜 := fun i j =>
  if i = j then δ j / α j else if i = j + 1 then -(δ i / α j) else 0

variable (α δ : ℕ → 𝕜)

/-- The diagonal entry $(j, j)$ of $\bar H_m$ is $\delta_j/\alpha_j$.

**Correction.** The entry formula uses zero-based row scaling as given by the matrix product. The
last column in the source display labels the scaling factors one index too high. The formula uses
Lean's total division.
-/
@[simp] theorem tfqmrCoeff_self (j : ℕ) : tfqmrCoeff α δ j j = δ j / α j := ite_eq_left rfl

/-- The subdiagonal entry $(j + 1, j)$ of $\bar H_m$ is $-\delta_{j+1}/\alpha_j$.

**Correction.** The entry formula uses zero-based row scaling as given by the matrix product. The
last column in the source display labels the scaling factors one index too high. The formula uses
Lean's total division.
-/
@[simp] theorem tfqmrCoeff_succ_self (j : ℕ) :
    tfqmrCoeff α δ (j + 1) j = -(δ (j + 1) / α j) := by
  rw [tfqmrCoeff, ite_eq_right (Nat.succ_ne_self j), ite_eq_left rfl]

/-- The entries of $\bar H_m$ off the diagonal and the subdiagonal are zero. -/
theorem tfqmrCoeff_eq_zero {i j : ℕ} (h₁ : i ≠ j) (h₂ : i ≠ j + 1) : tfqmrCoeff α δ i j = 0 := by
  rw [tfqmrCoeff, ite_eq_right h₁, ite_eq_right h₂]

variable {α δ}

variable {A b x₀ rs₀}

/-- Equation (7.69): $\alpha_m A u_m = w_m - w_{m+1}$, the only relation between the two families of
vectors that Algorithm 7.8 needs. -/
theorem tfqmr_smul_apply_u (m : ℕ) :
    tfqmrAlpha A b x₀ rs₀ m • op A (tfqmrU A b x₀ rs₀ m)
      = tfqmrW A b x₀ rs₀ m - tfqmrW A b x₀ rs₀ (m + 1) := by
  rw [tfqmr_succ_w]
  abel

/-- Algorithm 7.8 of [saad2003iterative] has **no serious breakdown**: for every $m$, if
$\alpha_m = 0$ then $Au_m = 0$. This is what (7.69) needs at a regular termination: once
$w_M = 0$, the algorithm produces $u_m = 0$ and $\alpha_m = 0$ for every $m \ge M$, and
$Au_m = (w_m - w_{m+1})/\alpha_m$ holds with both sides $0$. The condition excludes a genuine
breakdown, where $\rho_{2j}$ vanishes with $w_{2j} \neq 0$.

This is the analogue of `SaadSparse.Chapter07.NoSeriousBreakdown` for Algorithm 7.1. Like that
structure, it is a conditional hypothesis, because $\alpha_m \neq 0$ for all $m$ cannot hold in
finite dimension: Algorithm 7.3 terminates.

**Reading.** Lean defines a sufficient continuation condition for the divided identity: any zero
step length must have zero image direction. It neither excludes every vanishing denominator nor
asserts that a numerical run can continue through one.
-/
structure TFQMRNoSeriousBreakdown (A : Matrix (Fin n) (Fin n) 𝕜)
    (b x₀ rs₀ : EuclideanSpace 𝕜 (Fin n)) : Prop where
  /-- If the step length $\alpha_m$ is zero, then $Au_m = 0$. -/
  apply_u_eq_zero : ∀ m, tfqmrAlpha A b x₀ rs₀ m = 0 → op A (tfqmrU A b x₀ rs₀ m) = 0

/-- **Equations (7.68)–(7.73)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$ and
$b, x_0, r^*_0 \in \mathbb{K}^n$, and assume that Algorithm 7.8 has no serious breakdown. Let
$\delta_0, \delta_1, \dots$ be a column scaling such that $w_i = 0$ whenever $\delta_i = 0$.
Then $$Au_i = \frac{1}{\alpha_i} (w_i - w_{i+1}) \quad\text{for every } i,$$ and the vectors
$u_j$ and the scaled vectors $\delta_i^{-1} w_i$ satisfy the two-family Hessenberg relation
$$Au_j = \sum_{i=0}^{j+1} h_{ij} \, \delta_i^{-1} w_i \quad\text{for every } j,$$ with the
bidiagonal coefficients $h_{ij}$ of $\bar H_m = \Delta_{m+1} \bar B_m$. In matrix form the first
identity is $AU_m = R_{m+1} \bar B_m$ of (7.70), and the second is that identity after the
column scaling $R_{m+1} \Delta_{m+1}^{-1}$ of (7.73).

The iterates expand in the vectors $u_j$ and the residuals in the vectors $w_i$, so the relation
has two families of vectors: it is `Krylov.HessenbergRelation₂`, with the coefficients
`SaadSparse.Chapter07.tfqmrCoeff`. The scaling is arbitrary, which is what exercise P-7.9 asks
about. The condition on $\delta$ holds for every nonzero scaling and for the normalization
$\delta_i = \|w_i\|_2$ of (7.73). Lean's inverse gives $0^{-1} = 0$.

**Generalization.** The identity is extended to all steps under the explicit condition that a zero
step length implies a zero image direction. The scaling can be any sequence whose zero entries occur
only at zero residual vectors. The book first divides by step lengths and then uses the inverse of
the norm-scaling diagonal.
-/
theorem equation_7_70 {δ : ℕ → 𝕜} (h : TFQMRNoSeriousBreakdown A b x₀ rs₀)
    (hδ : ∀ i, δ i = 0 → tfqmrW A b x₀ rs₀ i = 0) :
    (∀ i, op A (tfqmrU A b x₀ rs₀ i)
        = (tfqmrAlpha A b x₀ rs₀ i)⁻¹ • (tfqmrW A b x₀ rs₀ i - tfqmrW A b x₀ rs₀ (i + 1))) ∧
      Krylov.HessenbergRelation₂ (op A) (tfqmrU A b x₀ rs₀)
        (fun i => (δ i)⁻¹ • tfqmrW A b x₀ rs₀ i) (tfqmrCoeff (tfqmrAlpha A b x₀ rs₀) δ) := by
  have hAu : ∀ i, op A (tfqmrU A b x₀ rs₀ i)
      = (tfqmrAlpha A b x₀ rs₀ i)⁻¹ • (tfqmrW A b x₀ rs₀ i - tfqmrW A b x₀ rs₀ (i + 1)) := by
    intro i
    rcases eq_or_ne (tfqmrAlpha A b x₀ rs₀ i) 0 with h0 | h0
    · rw [h.apply_u_eq_zero i h0, ← tfqmr_smul_apply_u i, h0, zero_smul, smul_zero]
    · rw [← tfqmr_smul_apply_u i, smul_smul, inv_mul_cancel₀ h0, one_smul]
  have key : ∀ (i : ℕ) (c : 𝕜),
      (δ i / c) • ((δ i)⁻¹ • tfqmrW A b x₀ rs₀ i) = c⁻¹ • tfqmrW A b x₀ rs₀ i := by
    intro i c
    rcases eq_or_ne (δ i) 0 with h0 | h0
    · rw [hδ i h0, smul_zero, smul_zero, smul_zero]
    · rw [smul_smul, div_eq_mul_inv, mul_right_comm, mul_inv_cancel₀ h0, one_mul]
  refine ⟨hAu, ⟨fun j => ?_, fun i j hij => tfqmrCoeff_eq_zero _ _ (by omega) (by omega)⟩⟩
  have hzero : ∑ i ∈ Finset.range j,
      tfqmrCoeff (tfqmrAlpha A b x₀ rs₀) δ i j • ((δ i)⁻¹ • tfqmrW A b x₀ rs₀ i) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [tfqmrCoeff_eq_zero _ _ (by omega) (by omega), zero_smul]
  rw [show j + 2 = j + 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_succ, hzero,
    zero_add, tfqmrCoeff_self, tfqmrCoeff_succ_self, key, neg_smul, key, hAu j, smul_sub,
    sub_eq_add_neg]

/-- If no $\alpha_i$ and no $\delta_i$ with $i < m$ vanishes, then the bidiagonal $H_m$ is lower
triangular with nonzero diagonal, hence nonsingular. -/
private theorem isUnit_hessenbergSqOf_tfqmrCoeff {α δ : ℕ → 𝕜} (m : ℕ) (hα : ∀ i < m, α i ≠ 0)
    (hδ : ∀ i < m, δ i ≠ 0) : IsUnit (Krylov.hessenbergSqOf (tfqmrCoeff α δ) m) := by
  have hlow : (Krylov.hessenbergSqOf (tfqmrCoeff α δ) m).IsLowerTriangular := by
    intro i j hij
    have hlt : (i : ℕ) < (j : ℕ) := hij
    exact tfqmrCoeff_eq_zero _ _ (by omega) (by omega)
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_isLowerTriangular _ hlow, isUnit_iff_ne_zero,
    Finset.prod_ne_zero_iff]
  intro i _
  change tfqmrCoeff α δ (i : ℕ) (i : ℕ) ≠ 0
  rw [tfqmrCoeff_self]
  exact div_ne_zero (hδ _ i.isLt) (hα _ i.isLt)

/-- **Equations (7.74)–(7.76)** and **exercise P-7.9** of [saad2003iterative]. Let
$A \in \mathbb{K}^{n \times n}$ and $b, x_0, r^*_0 \in \mathbb{K}^n$, let
$\delta_0, \delta_1, \dots$ be a column scaling, and assume $\alpha_i \neq 0$ and
$\delta_i \neq 0$ for every $i < m$. Let $H_m$ be the leading $m \times m$ block of
$\bar H_m = \Delta_{m+1} \bar B_m$. Then the vector of step lengths
$z_m = (\alpha_0, \dots, \alpha_{m-1})^T$ solves $$H_m z_m = \delta_0 e_1,$$ the matrix $H_m$ is
nonsingular, and the extended CGS iterate is given by the FOM formula for the relation (7.70),
$$\tilde x_m = x_0 + U_m H_m^{-1} (\delta_0 e_1).$$ The identity holds for every scaling
$\Delta_{m+1}$, which answers exercise P-7.9.

In each row $i \ge 1$ of $H_m z_m$, the two products $h_{i,i-1} \alpha_{i-1} = -\delta_i$ and
$h_{ii} \alpha_i = \delta_i$ cancel. The matrix $H_m$ is `Krylov.hessenbergSqOf` of
`SaadSparse.Chapter07.tfqmrCoeff`.

**Generalization.** The theorem permits arbitrary nonzero scalars on the finite residual prefix and
assumes nonzero step lengths for the preceding updates. The displayed derivation uses residual norms
for the column scalings.
-/
theorem equation_7_76 {δ : ℕ → 𝕜} (m : ℕ) (hα : ∀ i < m, tfqmrAlpha A b x₀ rs₀ i ≠ 0)
    (hδ : ∀ i < m, δ i ≠ 0) :
    Krylov.hessenbergSqOf (tfqmrCoeff (tfqmrAlpha A b x₀ rs₀) δ) m
          *ᵥ (fun j : Fin m => tfqmrAlpha A b x₀ rs₀ (j : ℕ)) = Krylov.firstVec (δ 0) m ∧
      IsUnit (Krylov.hessenbergSqOf (tfqmrCoeff (tfqmrAlpha A b x₀ rs₀) δ) m) ∧
      cgsHalfIterate A b x₀ rs₀ m
        = x₀ + ∑ j : Fin m,
            ((Krylov.hessenbergSqOf (tfqmrCoeff (tfqmrAlpha A b x₀ rs₀) δ) m)⁻¹
              *ᵥ Krylov.firstVec (δ 0) m) j • tfqmrU A b x₀ rs₀ (j : ℕ) := by
  have happ : ∀ i j : Fin m,
      Krylov.hessenbergSqOf (tfqmrCoeff (tfqmrAlpha A b x₀ rs₀) δ) m i j
        = tfqmrCoeff (tfqmrAlpha A b x₀ rs₀) δ (i : ℕ) (j : ℕ) := fun _ _ => rfl
  have hfv : ∀ i : Fin m,
      Krylov.firstVec (δ 0) m i = if (i : ℕ) = 0 then δ 0 else 0 := fun _ => rfl
  have hunit := isUnit_hessenbergSqOf_tfqmrCoeff (α := tfqmrAlpha A b x₀ rs₀) m hα hδ
  have hmul : Krylov.hessenbergSqOf (tfqmrCoeff (tfqmrAlpha A b x₀ rs₀) δ) m
      *ᵥ (fun j : Fin m => tfqmrAlpha A b x₀ rs₀ (j : ℕ)) = Krylov.firstVec (δ 0) m := by
    funext i
    have him : (i : ℕ) < m := i.isLt
    rw [Matrix.mulVec, dotProduct, hfv]
    rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | hpos
    · rw [Finset.sum_eq_single i]
      · rw [happ, tfqmrCoeff_self, div_mul_cancel₀ _ (hα _ him), ite_eq_left h0, h0]
      · intro j _ hj
        have hjne : (j : ℕ) ≠ (i : ℕ) := fun hc => hj (Fin.ext hc)
        rw [happ, tfqmrCoeff_eq_zero _ _ (by omega) (by omega), zero_mul]
      · intro hc; exact absurd (Finset.mem_univ _) hc
    · obtain ⟨k, hk⟩ : ∃ k, (i : ℕ) = k + 1 := ⟨(i : ℕ) - 1, by omega⟩
      have hkm : k < m := by omega
      have hne : (⟨k, hkm⟩ : Fin m) ≠ i := by
        intro hc
        have hik : (i : ℕ) = k := by rw [← hc]
        omega
      have hzr : ∀ j ∈ Finset.univ, j ∉ ({(⟨k, hkm⟩ : Fin m), i} : Finset (Fin m)) →
          Krylov.hessenbergSqOf (tfqmrCoeff (tfqmrAlpha A b x₀ rs₀) δ) m i j
            * tfqmrAlpha A b x₀ rs₀ (j : ℕ) = 0 := by
        intro j _ hj
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
        have h1 : (j : ℕ) ≠ k := fun hc => hj.1 (Fin.ext hc)
        have h2 : (j : ℕ) ≠ (i : ℕ) := fun hc => hj.2 (Fin.ext hc)
        rw [happ, tfqmrCoeff_eq_zero _ _ (by omega) (by omega), zero_mul]
      rw [← Finset.sum_subset (Finset.subset_univ ({(⟨k, hkm⟩ : Fin m), i} : Finset (Fin m))) hzr,
        Finset.sum_pair hne, happ, happ, ite_eq_right (by omega : ¬ (i : ℕ) = 0)]
      rw [show ((⟨k, hkm⟩ : Fin m) : ℕ) = k from rfl, hk, tfqmrCoeff_succ_self, tfqmrCoeff_self,
        neg_mul, div_mul_cancel₀ _ (hα k hkm), div_mul_cancel₀ _ (hα (k + 1) (by omega)),
        neg_add_cancel]
  refine ⟨hmul, hunit, ?_⟩
  have hinv : (Krylov.hessenbergSqOf (tfqmrCoeff (tfqmrAlpha A b x₀ rs₀) δ) m)⁻¹
      *ᵥ Krylov.firstVec (δ 0) m = fun j : Fin m => tfqmrAlpha A b x₀ rs₀ (j : ℕ) := by
    rw [← hmul, Matrix.nonsing_inv_mulVec_mulVec hunit]
  rw [hinv, cgsHalfIterate, Fin.sum_univ_eq_sum_range
    (fun i => tfqmrAlpha A b x₀ rs₀ i • tfqmrU A b x₀ rs₀ i) m]

/-! ### (7.77)–(7.83): the rotations and the quasi-minimal residual property -/

/-- Algorithm 7.8 of [saad2003iterative] does not break down through step $m$: for every $i \le m$,
$\alpha_i \neq 0$ and $w_i \neq 0$. Since $\alpha_{2j} = \alpha_{2j+1} = \rho_{2j}/(v_{2j},
r^*_0)$, and Lean's division by zero gives $0$, the first condition says that no $\rho_{2j}$ and
no denominator $(v_{2j}, r^*_0)$ of line 5 vanishes; the condition $\rho_{2j} \neq 0$ is the
condition of the book on $r^*_0$ carried along the iteration. The second condition makes it
possible to normalize the columns of $R_{m+1}$.

The bound $m$ is necessary: $\alpha_i \neq 0$ for all $i$ cannot hold in finite dimension,
because Algorithm 7.3 terminates with $\rho_j = 0$ from the grade on.

**Reading.** The predicate requires nonzero residual vectors and step lengths through index $m$,
inclusive. This can exclude a successful termination at $m$ and includes the length of the next
update when applied to the iterate after $m$ half-steps.
-/
structure TFQMRNoBreakdown (A : Matrix (Fin n) (Fin n) 𝕜)
    (b x₀ rs₀ : EuclideanSpace 𝕜 (Fin n)) (m : ℕ) : Prop where
  /-- For every $i \le m$, the step length $\alpha_i$ is nonzero. -/
  alpha_ne_zero : ∀ i ≤ m, tfqmrAlpha A b x₀ rs₀ i ≠ 0
  /-- For every $i \le m$, $w_i \neq 0$, so that $\delta_i = \|w_i\|_2 \neq 0$. -/
  w_ne_zero : ∀ i ≤ m, tfqmrW A b x₀ rs₀ i ≠ 0

/-- If Algorithm 7.8 does not break down through step $m$, then it does not break down through step
$k$ for every $k \le m$. -/
theorem TFQMRNoBreakdown.mono {A : Matrix (Fin n) (Fin n) 𝕜}
    {b x₀ rs₀ : EuclideanSpace 𝕜 (Fin n)} {m k : ℕ}
    (h : TFQMRNoBreakdown A b x₀ rs₀ m) (hk : k ≤ m) : TFQMRNoBreakdown A b x₀ rs₀ k :=
  ⟨fun i hi => h.alpha_ne_zero i (hi.trans hk), fun i hi => h.w_ne_zero i (hi.trans hk)⟩

variable (A b x₀ rs₀)

/-- **Equation (7.73)** of [saad2003iterative]: the column scaling $\delta_i = \|w_i\|_2$, seen as a
scalar. It gives the residual basis $R_{m+1} \Delta_{m+1}^{-1}$ unit columns.

**Reading.** The norm is a scalar defined even when the residual is zero. The normalized column is a
unit vector only for a nonzero residual; the book writes the inverse diagonal and uses unit columns.
-/
noncomputable def tfqmrDelta (i : ℕ) : 𝕜 := ((‖tfqmrW A b x₀ rs₀ i‖ : ℝ) : 𝕜)

/-- Equation (7.81): the bidiagonal coefficient array $\bar H_m = \Delta_{m+1} \bar B_m$ for the
step lengths of Algorithm 7.8 and the scaling $\delta_i = \|w_i\|_2$.

**Correction.** With the zero-based indexing used in the derivation, the diagonal in column $j$ is
$\delta_j/\alpha_j$ and the subdiagonal is $-\delta_{j+1}/\alpha_j$. The printed last column of
(7.81) labels the two scaling factors $\delta_m$ and $\delta_{m+1}$, one too high for the displayed
$(m+1)\times m$ block. Lean also totalizes undefined quotients.
-/
noncomputable abbrev tfqmrH : ℕ → ℕ → 𝕜 :=
  tfqmrCoeff (tfqmrAlpha A b x₀ rs₀) (tfqmrDelta A b x₀ rs₀)

/-- The scaling satisfies $|\delta_i| = \|w_i\|_2$. -/
theorem norm_tfqmrDelta (i : ℕ) : ‖tfqmrDelta A b x₀ rs₀ i‖ = ‖tfqmrW A b x₀ rs₀ i‖ := by
  rw [tfqmrDelta, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]

/-- The entries of $\bar H_m$ above the diagonal are zero. -/
theorem tfqmrH_eq_zero_of_lt {i j : ℕ} (hij : i < j) : tfqmrH A b x₀ rs₀ i j = 0 :=
  tfqmrCoeff_eq_zero _ _ (by omega) (by omega)

/-- The diagonal entry $(j, j)$ of $\bar H_m$ is $\delta_j/\alpha_j$.

**Correction.** The entry formula uses zero-based row scaling as given by the matrix product. The
last column in the source display labels the scaling factors one index too high. The formula uses
Lean's total division.
-/
theorem tfqmrH_self (j : ℕ) :
    tfqmrH A b x₀ rs₀ j j = tfqmrDelta A b x₀ rs₀ j / tfqmrAlpha A b x₀ rs₀ j :=
  tfqmrCoeff_self _ _ j

/-- The subdiagonal entry $(j + 1, j)$ of $\bar H_m$ is $-\delta_{j+1}/\alpha_j$.

**Correction.** The entry formula uses zero-based row scaling as given by the matrix product. The
last column in the source display labels the scaling factors one index too high. The formula uses
Lean's total division.
-/
theorem tfqmrH_succ_self (j : ℕ) :
    tfqmrH A b x₀ rs₀ (j + 1) j = -(tfqmrDelta A b x₀ rs₀ (j + 1) / tfqmrAlpha A b x₀ rs₀ j) :=
  tfqmrCoeff_succ_self _ _ j

/-- The entries of $\bar H_m$ below the subdiagonal are zero, so $\bar H_m$ is upper Hessenberg. -/
theorem tfqmrH_eq_zero_of_succ_lt {i j : ℕ} (hij : j + 1 < i) : tfqmrH A b x₀ rs₀ i j = 0 :=
  tfqmrCoeff_eq_zero _ _ (by omega) (by omega)

variable {A b x₀ rs₀}

/-- If Algorithm 7.8 does not break down through step $m$, then $\delta_i \neq 0$ for every
$i \le m$. -/
theorem TFQMRNoBreakdown.delta_ne_zero {m : ℕ} (h : TFQMRNoBreakdown A b x₀ rs₀ m) {i : ℕ}
    (hi : i ≤ m) : tfqmrDelta A b x₀ rs₀ i ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_tfqmrDelta]
  exact norm_ne_zero_iff.2 (h.w_ne_zero i hi)

/-- The cosine $c_m$ of Algorithm 7.8 is a positive real number. -/
private theorem tfqmrC_pos (m : ℕ) : 0 < tfqmrC A b x₀ rs₀ m :=
  inv_pos.2 (Real.sqrt_pos.2 (by positivity))

/-- If Algorithm 7.8 does not break down through step $m$, then $\tau_m > 0$. -/
private theorem tfqmrTau_pos : ∀ (m : ℕ), TFQMRNoBreakdown A b x₀ rs₀ m →
    0 < tfqmrTau A b x₀ rs₀ m := by
  intro m
  induction m with
  | zero => intro h; exact norm_pos_iff.2 (h.w_ne_zero 0 le_rfl)
  | succ m ih =>
    intro h
    have ihm := ih (h.mono (Nat.le_succ m))
    rw [tfqmr_succ_tau, tfqmr_succ_theta]
    exact mul_pos (mul_pos ihm (div_pos (norm_pos_iff.2 (h.w_ne_zero (m + 1) le_rfl)) ihm))
      (tfqmrC_pos (m + 1))

/-- For $t > 0$, $\sqrt{1 + (d/t)^2} = \sqrt{t^2 + d^2}/t$, which gives $c_{m+1} =
\tau_m/\sqrt{\tau_m^2 + \delta_{m+1}^2}$. -/
private theorem sqrt_one_add_div_sq {t d : ℝ} (ht : 0 < t) :
    Real.sqrt (1 + (d / t) ^ 2) = Real.sqrt (t ^ 2 + d ^ 2) / t := by
  rw [eq_div_iff ht.ne']
  have hmul : Real.sqrt (1 + (d / t) ^ 2) * Real.sqrt (t ^ 2)
      = Real.sqrt ((1 + (d / t) ^ 2) * t ^ 2) := (Real.sqrt_mul (by positivity) _).symm
  rw [Real.sqrt_sq ht.le] at hmul
  rw [hmul]
  congr 1
  field_simp

/-- Equation (7.82): if Algorithm 7.8 does not break down through step $m$, then $c_{m+1} =
\tau_m/\sqrt{\tau_m^2 + \delta_{m+1}^2}$. -/
private theorem tfqmrC_succ_eq (m : ℕ) (h : TFQMRNoBreakdown A b x₀ rs₀ m) :
    tfqmrC A b x₀ rs₀ (m + 1) = tfqmrTau A b x₀ rs₀ m
      / Real.sqrt (tfqmrTau A b x₀ rs₀ m ^ 2 + ‖tfqmrW A b x₀ rs₀ (m + 1)‖ ^ 2) := by
  rw [tfqmrC, tfqmr_succ_theta, sqrt_one_add_div_sq (tfqmrTau_pos m h), inv_div]

/-- Equation (7.82): if Algorithm 7.8 does not break down through step $m$, then $\tau_{m+1} =
\tau_m \delta_{m+1}/\sqrt{\tau_m^2 + \delta_{m+1}^2}$. -/
private theorem tfqmrTau_succ_eq (m : ℕ) (h : TFQMRNoBreakdown A b x₀ rs₀ m) :
    tfqmrTau A b x₀ rs₀ (m + 1) = tfqmrTau A b x₀ rs₀ m * ‖tfqmrW A b x₀ rs₀ (m + 1)‖
      / Real.sqrt (tfqmrTau A b x₀ rs₀ m ^ 2 + ‖tfqmrW A b x₀ rs₀ (m + 1)‖ ^ 2) := by
  have ht := tfqmrTau_pos m h
  rw [tfqmr_succ_tau, tfqmr_succ_theta, tfqmrC_succ_eq m h]
  field_simp

/-- The first $m$ rotations leave the subdiagonal entry $-\delta_{m+1}/\alpha_m$ of column $m$
unchanged. -/
private theorem rotated_succ_col (m : ℕ) :
    Krylov.rotated (tfqmrH A b x₀ rs₀) m (m + 1) m
      = -(tfqmrDelta A b x₀ rs₀ (m + 1) / tfqmrAlpha A b x₀ rs₀ m) := by
  rw [Krylov.rotated_eq_of_le _ m (m + 1) m le_rfl]
  exact tfqmrCoeff_succ_self _ _ m

/-- After rotation $m$, the diagonal entry of column $m + 1$ is $c \, \delta_{m+1}/\alpha_{m+1}$,
where $c$ is the cosine of rotation $m$. -/
private theorem rotated_succ_diag (m : ℕ) :
    Krylov.rotated (tfqmrH A b x₀ rs₀) (m + 1) (m + 1) (m + 1)
      = Krylov.givensC (tfqmrH A b x₀ rs₀) m
        * (tfqmrDelta A b x₀ rs₀ (m + 1) / tfqmrAlpha A b x₀ rs₀ (m + 1)) := by
  rw [Krylov.rotated_succ_apply, ite_eq_right (by omega), ite_eq_left rfl,
    Krylov.rotated_eq_zero_of_lt_of_lt_col _ (fun i j hij => tfqmrH_eq_zero_of_lt A b x₀ rs₀ hij)
      m m (m + 1) (by omega) (by omega),
    Krylov.rotated_eq_of_le _ m (m + 1) (m + 1) le_rfl, tfqmrH_self A b x₀ rs₀ (m + 1),
    mul_zero, zero_add]

/-- Rotation $m$ puts the entry $\bar s \, \delta_{m+1}/\alpha_{m+1}$ one row above the diagonal of
column $m + 1$, where $s$ is the sine of rotation $m$. -/
private theorem rotated_above_diag (m : ℕ) :
    Krylov.rotated (tfqmrH A b x₀ rs₀) (m + 1 + 1) m (m + 1)
      = starRingEnd 𝕜 (Krylov.givensS (tfqmrH A b x₀ rs₀) m)
        * (tfqmrDelta A b x₀ rs₀ (m + 1) / tfqmrAlpha A b x₀ rs₀ (m + 1)) := by
  rw [Krylov.rotated_succ_apply, ite_eq_right (by omega), ite_eq_right (by omega),
    Krylov.rotated_succ_apply, ite_eq_left rfl,
    Krylov.rotated_eq_zero_of_lt_of_lt_col _ (fun i j hij => tfqmrH_eq_zero_of_lt A b x₀ rs₀ hij)
      m m (m + 1) (by omega) (by omega),
    Krylov.rotated_eq_of_le _ m (m + 1) (m + 1) le_rfl, tfqmrH_self A b x₀ rs₀ (m + 1),
    mul_zero, zero_add]

/-- For $x \ge 0$ and $a > 0$, $\sqrt{x/a^2} = \sqrt{x}/a$. -/
private theorem sqrt_div_sq {x a : ℝ} (hx : 0 ≤ x) (ha : 0 < a) :
    Real.sqrt (x / a ^ 2) = Real.sqrt x / a := by
  rw [eq_div_iff ha.ne']
  have hmul : Real.sqrt (x / a ^ 2) * Real.sqrt (a ^ 2) = Real.sqrt (x / a ^ 2 * a ^ 2) :=
    (Real.sqrt_mul (by positivity) _).symm
  rw [Real.sqrt_sq ha.le] at hmul
  rw [hmul, div_mul_cancel₀ _ (by positivity : (a : ℝ) ^ 2 ≠ 0)]

variable (A b x₀ rs₀)

/-- The unimodular factor $\sigma_m = \prod_{i<m} |\alpha_i|/\alpha_i$, which the real recurrence of
the book for $\tau_m$ does not see; over $\mathbb{R}$ it is $\pm 1$. -/
private noncomputable def tfqmrPhase (m : ℕ) : 𝕜 :=
  ∏ i ∈ Finset.range m, ((‖tfqmrAlpha A b x₀ rs₀ i‖ : ℝ) : 𝕜) / tfqmrAlpha A b x₀ rs₀ i

private theorem tfqmrPhase_zero : tfqmrPhase A b x₀ rs₀ 0 = 1 := by
  rw [tfqmrPhase, Finset.range_zero, Finset.prod_empty]

private theorem tfqmrPhase_succ (m : ℕ) : tfqmrPhase A b x₀ rs₀ (m + 1)
    = tfqmrPhase A b x₀ rs₀ m
      * (((‖tfqmrAlpha A b x₀ rs₀ m‖ : ℝ) : 𝕜) / tfqmrAlpha A b x₀ rs₀ m) := by
  rw [tfqmrPhase, tfqmrPhase, Finset.prod_range_succ]

variable {A b x₀ rs₀}

private theorem norm_tfqmrPhase (m : ℕ) (h : TFQMRNoBreakdown A b x₀ rs₀ m) :
    ‖tfqmrPhase A b x₀ rs₀ m‖ = 1 := by
  rw [tfqmrPhase, norm_prod]
  refine Finset.prod_eq_one fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [norm_div, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.2 (h.alpha_ne_zero i (by omega)))]

/-- If the diagonal entry left by the first $m$ rotations is $\tau_m \sigma_m/\alpha_m$, then the
denominator of rotation $m$ is $\sqrt{\tau_m^2 + \delta_{m+1}^2}/|\alpha_m|$. -/
private theorem givensRho_eq_aux (m : ℕ) (h : TFQMRNoBreakdown A b x₀ rs₀ m)
    (hrot : Krylov.rotated (tfqmrH A b x₀ rs₀) m m m
      = ((tfqmrTau A b x₀ rs₀ m : ℝ) : 𝕜) * tfqmrPhase A b x₀ rs₀ m
        / tfqmrAlpha A b x₀ rs₀ m) :
    Krylov.givensRho (tfqmrH A b x₀ rs₀) m
      = Real.sqrt (tfqmrTau A b x₀ rs₀ m ^ 2 + ‖tfqmrW A b x₀ rs₀ (m + 1)‖ ^ 2)
        / ‖tfqmrAlpha A b x₀ rs₀ m‖ := by
  have hna : (0 : ℝ) < ‖tfqmrAlpha A b x₀ rs₀ m‖ := norm_pos_iff.2 (h.alpha_ne_zero m le_rfl)
  have hnaz : ‖tfqmrAlpha A b x₀ rs₀ m‖ ≠ 0 := hna.ne'
  rw [Krylov.givensRho, hrot, rotated_succ_col, norm_neg, norm_div, norm_div, norm_mul,
    RCLike.norm_ofReal, abs_of_pos (tfqmrTau_pos m h), norm_tfqmrPhase m h, mul_one,
    norm_tfqmrDelta,
    show (tfqmrTau A b x₀ rs₀ m / ‖tfqmrAlpha A b x₀ rs₀ m‖) ^ 2
        + (‖tfqmrW A b x₀ rs₀ (m + 1)‖ / ‖tfqmrAlpha A b x₀ rs₀ m‖) ^ 2
        = (tfqmrTau A b x₀ rs₀ m ^ 2 + ‖tfqmrW A b x₀ rs₀ (m + 1)‖ ^ 2)
          / ‖tfqmrAlpha A b x₀ rs₀ m‖ ^ 2 from by field_simp,
    sqrt_div_sq (by positivity) hna]

/-- If Algorithm 7.8 does not break down through step $m$, then the Givens rotations of Algorithm
6.12 on the bidiagonal $\bar H_m$ give the quasi-residual scalar $\gamma_m = \tau_m \sigma_m$,
and the diagonal entry left by rotation $m$ is $\tau_m \sigma_m/\alpha_m$, so that
$|\gamma_m| = \tau_m$ as in the text after (7.83). -/
private theorem tfqmr_rotation : ∀ (m : ℕ), TFQMRNoBreakdown A b x₀ rs₀ m →
    Krylov.gamma (tfqmrH A b x₀ rs₀) (tfqmrDelta A b x₀ rs₀ 0) m
        = ((tfqmrTau A b x₀ rs₀ m : ℝ) : 𝕜) * tfqmrPhase A b x₀ rs₀ m ∧
      Krylov.rotated (tfqmrH A b x₀ rs₀) m m m
        = ((tfqmrTau A b x₀ rs₀ m : ℝ) : 𝕜) * tfqmrPhase A b x₀ rs₀ m
          / tfqmrAlpha A b x₀ rs₀ m := by
  intro m
  induction m with
  | zero =>
    intro _
    have hg : Krylov.gamma (tfqmrH A b x₀ rs₀) (tfqmrDelta A b x₀ rs₀ 0) 0
        = tfqmrDelta A b x₀ rs₀ 0 := rfl
    have hr : Krylov.rotated (tfqmrH A b x₀ rs₀) 0 0 0
        = tfqmrDelta A b x₀ rs₀ 0 / tfqmrAlpha A b x₀ rs₀ 0 := tfqmrH_self A b x₀ rs₀ 0
    have ht : tfqmrTau A b x₀ rs₀ 0 = ‖tfqmrW A b x₀ rs₀ 0‖ := rfl
    refine ⟨?_, ?_⟩
    · rw [hg, tfqmrPhase_zero, mul_one, tfqmrDelta, ht]
    · rw [hr, tfqmrPhase_zero, mul_one, tfqmrDelta, ht]
  | succ m ih =>
    intro h
    obtain ⟨hgam, hrot⟩ := ih (h.mono (Nat.le_succ m))
    have hαm := h.alpha_ne_zero m (by omega)
    have hαm' := h.alpha_ne_zero (m + 1) le_rfl
    have ht : 0 < tfqmrTau A b x₀ rs₀ m := tfqmrTau_pos m (h.mono (Nat.le_succ m))
    have hd : 0 < ‖tfqmrW A b x₀ rs₀ (m + 1)‖ := norm_pos_iff.2 (h.w_ne_zero (m + 1) le_rfl)
    have hna : (0 : ℝ) < ‖tfqmrAlpha A b x₀ rs₀ m‖ := norm_pos_iff.2 hαm
    have hS : (0 : ℝ) < Real.sqrt (tfqmrTau A b x₀ rs₀ m ^ 2 + ‖tfqmrW A b x₀ rs₀ (m + 1)‖ ^ 2) :=
      Real.sqrt_pos.2 (by positivity)
    have hSK : ((Real.sqrt (tfqmrTau A b x₀ rs₀ m ^ 2 + ‖tfqmrW A b x₀ rs₀ (m + 1)‖ ^ 2) : ℝ) : 𝕜)
        ≠ 0 := RCLike.ofReal_ne_zero.2 hS.ne'
    have hnaK : ((‖tfqmrAlpha A b x₀ rs₀ m‖ : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 hna.ne'
    have hrho := givensRho_eq_aux m (h.mono (Nat.le_succ m)) hrot
    constructor
    · rw [Krylov.gamma_succ, Krylov.givensS, rotated_succ_col, hgam, hrho,
        tfqmrTau_succ_eq m (h.mono (Nat.le_succ m)), tfqmrPhase_succ, tfqmrDelta]
      push_cast
      field_simp
    · rw [rotated_succ_diag, Krylov.givensC, hrot, hrho,
        tfqmrTau_succ_eq m (h.mono (Nat.le_succ m)), tfqmrPhase_succ, tfqmrDelta]
      push_cast
      field_simp

/-- If Algorithm 7.8 does not break down through step $m$, then the denominator of rotation $m$ is
$\sqrt{\tau_m^2 + \delta_{m+1}^2}/|\alpha_m|$, in particular positive. -/
private theorem givensRho_eq (m : ℕ) (h : TFQMRNoBreakdown A b x₀ rs₀ m) :
    Krylov.givensRho (tfqmrH A b x₀ rs₀) m
      = Real.sqrt (tfqmrTau A b x₀ rs₀ m ^ 2 + ‖tfqmrW A b x₀ rs₀ (m + 1)‖ ^ 2)
        / ‖tfqmrAlpha A b x₀ rs₀ m‖ :=
  givensRho_eq_aux m h (tfqmr_rotation m h).2

private theorem givensRho_pos (m : ℕ) (h : TFQMRNoBreakdown A b x₀ rs₀ m) :
    0 < Krylov.givensRho (tfqmrH A b x₀ rs₀) m := by
  have hna : (0 : ℝ) < ‖tfqmrAlpha A b x₀ rs₀ m‖ := norm_pos_iff.2 (h.alpha_ne_zero m le_rfl)
  have ht := tfqmrTau_pos m h
  rw [givensRho_eq m h]
  have : (0 : ℝ) < Real.sqrt (tfqmrTau A b x₀ rs₀ m ^ 2 + ‖tfqmrW A b x₀ rs₀ (m + 1)‖ ^ 2) :=
    Real.sqrt_pos.2 (by positivity)
  positivity

/-- **Section 7.4.3** of [saad2003iterative], the identity after (7.83). Let
$A \in \mathbb{K}^{n \times n}$ and $b, x_0, r^*_0 \in \mathbb{K}^n$, and assume that Algorithm
7.8 does not break down through step $m$. Then the quasi-residual scalar $\gamma_{m+1}$ of the
Givens rotations of $\bar H_m$ of (7.81), with the right-hand side $\delta_0 e_1$, has the
modulus $$|\gamma_{m+1}| = \tau_m.$$

The identity holds in modulus: the backbone rotations differ from those of Algorithm 7.8 by the
unimodular factor $\prod_{i<m} |\alpha_i|/\alpha_i$. The scalar $\gamma_{m+1}$ is `Krylov.gamma`
at index `m`.

**Reading.** The source identifies gamma with the nonnegative tau. In Lean's complex-capable Givens
convention, gamma can carry a unit phase, even a sign over the reals, so Lean identifies its norm
with tau.
-/
theorem norm_gamma_eq_tfqmrTau (m : ℕ) (h : TFQMRNoBreakdown A b x₀ rs₀ m) :
    ‖Krylov.gamma (tfqmrH A b x₀ rs₀) (tfqmrDelta A b x₀ rs₀ 0) m‖ = tfqmrTau A b x₀ rs₀ m := by
  rw [(tfqmr_rotation m h).1, norm_mul, RCLike.norm_ofReal, abs_of_pos (tfqmrTau_pos m h),
    norm_tfqmrPhase m h, mul_one]

/-- The entry $g_m$ of the rotated right-hand side is $\tau_m^2/(\bar\alpha_m \rho_m)$, where
$\rho_m$ is the denominator of rotation $m$, because the unimodular factor cancels against its
conjugate. -/
private theorem gvec_eq (m : ℕ) (h : TFQMRNoBreakdown A b x₀ rs₀ m) :
    Krylov.gvec (tfqmrH A b x₀ rs₀) (tfqmrDelta A b x₀ rs₀ 0) m
      = ((tfqmrTau A b x₀ rs₀ m : ℝ) : 𝕜) ^ 2
        / (starRingEnd 𝕜 (tfqmrAlpha A b x₀ rs₀ m)
          * ((Krylov.givensRho (tfqmrH A b x₀ rs₀) m : ℝ) : 𝕜)) := by
  obtain ⟨hgam, hrot⟩ := tfqmr_rotation m h
  have hαm := h.alpha_ne_zero m le_rfl
  have hcαm : starRingEnd 𝕜 (tfqmrAlpha A b x₀ rs₀ m) ≠ 0 := by simpa using hαm
  have hρK : ((Krylov.givensRho (tfqmrH A b x₀ rs₀) m : ℝ) : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.2 (givensRho_pos m h).ne'
  have hσne : tfqmrPhase A b x₀ rs₀ m ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_tfqmrPhase m h]
    norm_num
  have hσinv : starRingEnd 𝕜 (tfqmrPhase A b x₀ rs₀ m) = (tfqmrPhase A b x₀ rs₀ m)⁻¹ := by
    field_simp
    rw [RCLike.conj_mul, norm_tfqmrPhase m h]
    norm_num
  rw [Krylov.gvec, Krylov.givensC, hrot, hgam]
  simp only [map_div₀, map_mul, RCLike.conj_ofReal, hσinv]
  field_simp

/-- Equation (7.78): $g_m = \rho_m \eta_{m+1}$, so that $\eta_{m+1} = c_{m+1}^2 \alpha_m$ is the
DQGMRES step length $g_m/\rho_m$. -/
private theorem gvec_eq_givensRho_mul_eta (m : ℕ) (h : TFQMRNoBreakdown A b x₀ rs₀ m) :
    Krylov.gvec (tfqmrH A b x₀ rs₀) (tfqmrDelta A b x₀ rs₀ 0) m
      = ((Krylov.givensRho (tfqmrH A b x₀ rs₀) m : ℝ) : 𝕜) * tfqmrEta A b x₀ rs₀ (m + 1) := by
  have hαm := h.alpha_ne_zero m le_rfl
  have ht : 0 < tfqmrTau A b x₀ rs₀ m := tfqmrTau_pos m h
  have hna : (0 : ℝ) < ‖tfqmrAlpha A b x₀ rs₀ m‖ := norm_pos_iff.2 hαm
  have hS : (0 : ℝ) < Real.sqrt (tfqmrTau A b x₀ rs₀ m ^ 2 + ‖tfqmrW A b x₀ rs₀ (m + 1)‖ ^ 2) :=
    Real.sqrt_pos.2 (by positivity)
  have hSK : ((Real.sqrt (tfqmrTau A b x₀ rs₀ m ^ 2 + ‖tfqmrW A b x₀ rs₀ (m + 1)‖ ^ 2) : ℝ) : 𝕜)
      ≠ 0 := RCLike.ofReal_ne_zero.2 hS.ne'
  have hnaK : ((‖tfqmrAlpha A b x₀ rs₀ m‖ : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 hna.ne'
  have hcα : starRingEnd 𝕜 (tfqmrAlpha A b x₀ rs₀ m)
      = ((‖tfqmrAlpha A b x₀ rs₀ m‖ : ℝ) : 𝕜) ^ 2 / tfqmrAlpha A b x₀ rs₀ m := by
    rw [eq_div_iff hαm, ← RCLike.mul_conj]
    ring
  rw [gvec_eq m h, tfqmr_succ_eta, tfqmrC_succ_eq m h, givensRho_eq m h, hcα]
  push_cast
  field_simp

/-- Equation (7.79): if Algorithm 7.8 does not break down through step $m + 1$, then the entry that
rotation $m$ puts above the diagonal of column $m + 1$ is $-(\theta_{m+1}^2/\alpha_{m+1}) g_m$,
which makes the recurrence for $d$ of Algorithm 7.8 the back-substitution of Algorithm 6.13. -/
private theorem rotated_above_diag_eq (m : ℕ) (h : TFQMRNoBreakdown A b x₀ rs₀ (m + 1)) :
    Krylov.rotated (tfqmrH A b x₀ rs₀) (m + 1 + 1) m (m + 1)
      = -(((tfqmrTheta A b x₀ rs₀ (m + 1) ^ 2 : ℝ) : 𝕜) / tfqmrAlpha A b x₀ rs₀ (m + 1))
        * Krylov.gvec (tfqmrH A b x₀ rs₀) (tfqmrDelta A b x₀ rs₀ 0) m := by
  have hαm := h.alpha_ne_zero m (by omega)
  have hαm' := h.alpha_ne_zero (m + 1) le_rfl
  have hcαm : starRingEnd 𝕜 (tfqmrAlpha A b x₀ rs₀ m) ≠ 0 := by simpa using hαm
  have ht : 0 < tfqmrTau A b x₀ rs₀ m := tfqmrTau_pos m (h.mono (Nat.le_succ m))
  have htK : ((tfqmrTau A b x₀ rs₀ m : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 ht.ne'
  have hρK : ((Krylov.givensRho (tfqmrH A b x₀ rs₀) m : ℝ) : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.2 (givensRho_pos m (h.mono (Nat.le_succ m))).ne'
  rw [rotated_above_diag, Krylov.givensS, rotated_succ_col,
    gvec_eq m (h.mono (Nat.le_succ m)), tfqmr_succ_theta,
    tfqmrDelta]
  simp only [map_div₀, map_neg, RCLike.conj_ofReal]
  push_cast
  field_simp

/-- The first direction of Algorithm 6.13 with $k = 1$ on $\bar H_m$ is $u_0$ divided by the rotated
diagonal entry; nothing is truncated, because each column of the triangular factor has only its
diagonal entry and the entry above it. -/
private theorem dqgmresP_zero_eq :
    Chapter06.dqgmresP (tfqmrU A b x₀ rs₀) (tfqmrH A b x₀ rs₀) 1 0
      = (Krylov.rotated (tfqmrH A b x₀ rs₀) 1 0 0)⁻¹ • tfqmrU A b x₀ rs₀ 0 := by
  rw [Chapter06.dqgmresP_eq]
  simp

private theorem dqgmresP_succ_eq (m : ℕ) :
    Chapter06.dqgmresP (tfqmrU A b x₀ rs₀) (tfqmrH A b x₀ rs₀) 1 (m + 1)
      = (Krylov.rotated (tfqmrH A b x₀ rs₀) (m + 1 + 1) (m + 1) (m + 1))⁻¹ •
        (tfqmrU A b x₀ rs₀ (m + 1)
          - Krylov.rotated (tfqmrH A b x₀ rs₀) (m + 1 + 1) m (m + 1)
            • Chapter06.dqgmresP (tfqmrU A b x₀ rs₀) (tfqmrH A b x₀ rs₀) 1 m) := by
  have hz : ∑ i ∈ Finset.range m,
      (if m + 1 ≤ i + 1 then Krylov.rotated (tfqmrH A b x₀ rs₀) (m + 1 + 1) i (m + 1) else 0)
        • Chapter06.dqgmresP (tfqmrU A b x₀ rs₀) (tfqmrH A b x₀ rs₀) 1 i = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [Finset.mem_range] at hi
      rw [ite_eq_right (by omega), zero_smul]
  rw [Chapter06.dqgmresP_eq, Finset.sum_range_succ, hz, zero_add, ite_eq_left (by omega)]

/-- If Algorithm 7.8 does not break down through step $m$, then its update $\eta_{m+1} d_{m+1}$ is
the update $g_m p_m$ of Algorithm 6.13 with $k = 1$. -/
private theorem tfqmr_eta_smul_d : ∀ (m : ℕ), TFQMRNoBreakdown A b x₀ rs₀ m →
    tfqmrEta A b x₀ rs₀ (m + 1) • tfqmrD A b x₀ rs₀ (m + 1)
      = Krylov.gvec (tfqmrH A b x₀ rs₀) (tfqmrDelta A b x₀ rs₀ 0) m
        • Chapter06.dqgmresP (tfqmrU A b x₀ rs₀) (tfqmrH A b x₀ rs₀) 1 m := by
  intro m
  induction m with
  | zero =>
    intro h
    have hρK : ((Krylov.givensRho (tfqmrH A b x₀ rs₀) 0 : ℝ) : 𝕜) ≠ 0 :=
      RCLike.ofReal_ne_zero.2 (givensRho_pos 0 h).ne'
    have hd1 : tfqmrD A b x₀ rs₀ 1 = tfqmrU A b x₀ rs₀ 0 := by
      rw [tfqmr_succ_d, show tfqmrEta A b x₀ rs₀ 0 = 0 from rfl, mul_zero, zero_smul, add_zero]
    have hsc : Krylov.gvec (tfqmrH A b x₀ rs₀) (tfqmrDelta A b x₀ rs₀ 0) 0
        * ((Krylov.givensRho (tfqmrH A b x₀ rs₀) 0 : ℝ) : 𝕜)⁻¹ = tfqmrEta A b x₀ rs₀ 1 := by
      rw [gvec_eq_givensRho_mul_eta 0 h]
      field_simp
    rw [hd1, dqgmresP_zero_eq, Krylov.rotated_succ_self, smul_smul, hsc]
  | succ m ih =>
    intro h
    have ihm := ih (h.mono (Nat.le_succ m))
    have hρK : ((Krylov.givensRho (tfqmrH A b x₀ rs₀) (m + 1) : ℝ) : 𝕜) ≠ 0 :=
      RCLike.ofReal_ne_zero.2 (givensRho_pos (m + 1) h).ne'
    have hsc : Krylov.gvec (tfqmrH A b x₀ rs₀) (tfqmrDelta A b x₀ rs₀ 0) (m + 1)
        * ((Krylov.givensRho (tfqmrH A b x₀ rs₀) (m + 1) : ℝ) : 𝕜)⁻¹
          = tfqmrEta A b x₀ rs₀ (m + 1 + 1) := by
      rw [gvec_eq_givensRho_mul_eta (m + 1) h]
      field_simp
    have hassoc : tfqmrEta A b x₀ rs₀ (m + 1 + 1)
        * (((tfqmrTheta A b x₀ rs₀ (m + 1) ^ 2 : ℝ) : 𝕜) / tfqmrAlpha A b x₀ rs₀ (m + 1)
          * tfqmrEta A b x₀ rs₀ (m + 1))
        = tfqmrEta A b x₀ rs₀ (m + 1 + 1)
            * (((tfqmrTheta A b x₀ rs₀ (m + 1) ^ 2 : ℝ) : 𝕜) / tfqmrAlpha A b x₀ rs₀ (m + 1))
          * tfqmrEta A b x₀ rs₀ (m + 1) := by
      ring
    have hkey : (tfqmrEta A b x₀ rs₀ (m + 1 + 1)
          * (((tfqmrTheta A b x₀ rs₀ (m + 1) ^ 2 : ℝ) : 𝕜) / tfqmrAlpha A b x₀ rs₀ (m + 1)
            * tfqmrEta A b x₀ rs₀ (m + 1))) • tfqmrD A b x₀ rs₀ (m + 1)
        = -(tfqmrEta A b x₀ rs₀ (m + 1 + 1)
            * Krylov.rotated (tfqmrH A b x₀ rs₀) (m + 1 + 1) m (m + 1))
          • Chapter06.dqgmresP (tfqmrU A b x₀ rs₀) (tfqmrH A b x₀ rs₀) 1 m := by
      rw [hassoc, ← smul_smul, ihm, smul_smul, rotated_above_diag_eq m h]
      congr 1
      ring
    rw [tfqmr_succ_d, dqgmresP_succ_eq, Krylov.rotated_succ_self, smul_smul, hsc, smul_add,
      smul_sub, smul_smul, smul_smul, hkey, neg_smul, sub_eq_add_neg]

/-- Algorithm 7.8 of [saad2003iterative] is Algorithm 6.13 (DQGMRES) with $k = 1$. Let
$A \in \mathbb{K}^{n \times n}$ and $b, x_0, r^*_0 \in \mathbb{K}^n$, and assume that Algorithm
7.8 does not break down through step $m$. Then its iterate $x_m$ is the iterate of Algorithm
6.13 with $k = 1$ for the vectors $u_j$, the bidiagonal coefficients $\bar H_m$ of (7.81) and
the right-hand side $\delta_0 e_1$, where $\delta_0 = \|r_0\|_2$. That is, the $\theta$, $c$,
$\tau$, $\eta$, $d$ recurrence of Algorithm 7.8 is the back-substitution of DQGMRES.

The proof uses $\eta_{m+1} = g_m/\rho_m$ and the identification of the entry above the diagonal
with $-(\theta_m^2/\alpha_m) g_{m-1}$. DQGMRES is `SaadSparse.Chapter06.dqgmres`.

**Reading.** The equivalence with the reduced solution is asserted only under the explicit nonzero
prefix through index $m$, including the next step length. DQGMRES uses memory one because the
rotated bidiagonal array has only one superdiagonal.
-/
theorem tfqmr_eq_dqgmres : ∀ (m : ℕ), TFQMRNoBreakdown A b x₀ rs₀ m →
    (tfqmr A b x₀ rs₀ m).x
      = Chapter06.dqgmres x₀ (tfqmrU A b x₀ rs₀) (tfqmrH A b x₀ rs₀)
          (tfqmrDelta A b x₀ rs₀ 0) 1 m := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro h
    rw [tfqmr_succ_x, ih (h.mono (Nat.le_succ m)), Chapter06.dqgmres,
      tfqmr_eta_smul_d m (h.mono (Nat.le_succ m))]

/-- Column $j$ of the triangular factor does not change after rotation $j$. -/
private theorem rotated_of_col_lt {j : ℕ} : ∀ M, j + 1 ≤ M → ∀ i,
    Krylov.rotated (tfqmrH A b x₀ rs₀) M i j
      = Krylov.rotated (tfqmrH A b x₀ rs₀) (j + 1) i j := by
  intro M
  induction M with
  | zero => intro hM; omega
  | succ M ih =>
    intro hM i
    rcases Nat.lt_or_ge j M with hjM | hjM
    · rw [Krylov.rotated_succ_eq_of_lt _
        (Matrix.isUpperHessenberg_iff_nat.2 fun i j hij => tfqmrH_eq_zero_of_succ_lt A b x₀ rs₀ hij)
        M j hjM i]
      exact ih (by omega) i
    · have hMj : M = j := by omega
      subst hMj
      rfl

/-- If Algorithm 7.8 does not break down through step $m$, then $P_m R_m = U_m$: with $k = 1$ the
truncated recurrence is the full back-substitution for the bidiagonal triangular factor. -/
private theorem sum_R_smul_dqgmresP {m : ℕ} (h : TFQMRNoBreakdown A b x₀ rs₀ m) (j : Fin m) :
    ∑ i : Fin m, Chapter06.R (tfqmrH A b x₀ rs₀) m i j
        • Chapter06.dqgmresP (tfqmrU A b x₀ rs₀) (tfqmrH A b x₀ rs₀) 1 (i : ℕ)
      = tfqmrU A b x₀ rs₀ (j : ℕ) := by
  have hhess : Matrix.IsUpperHessenberg (n := ℕ) (tfqmrH A b x₀ rs₀) :=
    Matrix.isUpperHessenberg_iff_nat.2 fun i j hij => tfqmrH_eq_zero_of_succ_lt A b x₀ rs₀ hij
  have hlow : ∀ i j : ℕ, i < j → tfqmrH A b x₀ rs₀ i j = 0 :=
    fun i j hij => tfqmrH_eq_zero_of_lt A b x₀ rs₀ hij
  have hjm : (j : ℕ) < m := j.isLt
  have hd : Krylov.rotated (tfqmrH A b x₀ rs₀) ((j : ℕ) + 1) (j : ℕ) (j : ℕ) ≠ 0 := by
    rw [Krylov.rotated_succ_self]
    exact RCLike.ofReal_ne_zero.2 (givensRho_pos (j : ℕ) (h.mono (le_of_lt j.isLt))).ne'
  have hzero : ∀ i ∈ Finset.range m, i ∉ Finset.range ((j : ℕ) + 1) →
      Krylov.rotated (tfqmrH A b x₀ rs₀) ((j : ℕ) + 1) i (j : ℕ)
        • Chapter06.dqgmresP (tfqmrU A b x₀ rs₀) (tfqmrH A b x₀ rs₀) 1 i = 0 := by
    intro i _ hi
    rw [Finset.mem_range, not_lt] at hi
    rw [Krylov.rotated_eq_zero_of_lt _ hhess ((j : ℕ) + 1) i (j : ℕ) (Nat.lt_succ_self _)
      (by omega), zero_smul]
  have hsub : Finset.range ((j : ℕ) + 1) ⊆ Finset.range m := by
    intro i hi
    rw [Finset.mem_range] at hi ⊢
    omega
  have hpj := Chapter06.dqgmresP_eq (tfqmrU A b x₀ rs₀) (tfqmrH A b x₀ rs₀) 1 (j : ℕ)
  have hcond : ∀ i ∈ Finset.range (j : ℕ),
      (if (j : ℕ) ≤ i + 1 then Krylov.rotated (tfqmrH A b x₀ rs₀) ((j : ℕ) + 1) i (j : ℕ) else 0)
          • Chapter06.dqgmresP (tfqmrU A b x₀ rs₀) (tfqmrH A b x₀ rs₀) 1 i
        = Krylov.rotated (tfqmrH A b x₀ rs₀) ((j : ℕ) + 1) i (j : ℕ)
          • Chapter06.dqgmresP (tfqmrU A b x₀ rs₀) (tfqmrH A b x₀ rs₀) 1 i := by
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases hc : (j : ℕ) ≤ i + 1
    · rw [ite_eq_left hc]
    · rw [ite_eq_right hc, Krylov.rotated_eq_zero_of_succ_lt_col _ hlow ((j : ℕ) + 1) i (j : ℕ)
        (by omega), zero_smul]
  rw [Finset.sum_congr rfl fun i _ => by
      rw [Chapter06.R_apply, rotated_of_col_lt (j := (j : ℕ)) m (by omega) (i : ℕ)],
    Fin.sum_univ_eq_sum_range
      (fun i => Krylov.rotated (tfqmrH A b x₀ rs₀) ((j : ℕ) + 1) i (j : ℕ)
        • Chapter06.dqgmresP (tfqmrU A b x₀ rs₀) (tfqmrH A b x₀ rs₀) 1 i) m,
    ← Finset.sum_subset hsub hzero, Finset.sum_range_succ, hpj, Finset.sum_congr rfl hcond,
    smul_smul, mul_inv_cancel₀ hd, one_smul]
  abel

/-- Let $A \in \mathbb{K}^{n \times n}$ and $b, x_0, r^*_0 \in \mathbb{K}^n$, and assume that
Algorithm 7.8 of [saad2003iterative] does not break down through step $m$. Then its iterate
$x_m$ is the iterate $x_0 + U_m R_m^{-1} g_m$ of Algorithm 6.12 (QGMRES) for the relation
(7.70), with the vectors $u_j$, the bidiagonal coefficients $\bar H_m$ of (7.81) and the
right-hand side $\delta_0 e_1$. Because $\bar H_m$ is bidiagonal, the truncated Algorithm 6.13
loses nothing.

QGMRES is `SaadSparse.Chapter06.qgmres`.

**Reading.** The equivalence with the reduced solution is asserted only under the explicit nonzero
prefix through index $m$, including the next step length. DQGMRES uses memory one because the
rotated bidiagonal array has only one superdiagonal.
-/
theorem tfqmr_eq_qgmres (m : ℕ) (h : TFQMRNoBreakdown A b x₀ rs₀ m) :
    (tfqmr A b x₀ rs₀ m).x
      = Chapter06.qgmres x₀ (tfqmrU A b x₀ rs₀) (tfqmrH A b x₀ rs₀)
          (tfqmrDelta A b x₀ rs₀ 0) m := by
  have hR : IsUnit (Chapter06.R (tfqmrH A b x₀ rs₀) m) :=
    Chapter06.isUnit_R _ (fun i j hij => tfqmrH_eq_zero_of_succ_lt A b x₀ rs₀ hij)
      fun k hk => (givensRho_pos k (h.mono (le_of_lt hk))).ne'
  rw [tfqmr_eq_dqgmres m h, Chapter06.dqgmres_eq_sum, Chapter06.qgmres,
    Chapter06.toEuclideanLin_colMatrix_apply]
  refine congrArg _ ?_
  have hg : ∀ i : Fin m, Krylov.gvec (tfqmrH A b x₀ rs₀) (tfqmrDelta A b x₀ rs₀ 0) (i : ℕ)
      = (Chapter06.R (tfqmrH A b x₀ rs₀) m
        *ᵥ Chapter06.qgmresY (tfqmrH A b x₀ rs₀) (tfqmrDelta A b x₀ rs₀ 0) m) i := by
    intro i
    rw [Chapter06.qgmresY, Chapter06.mulVec_R_inv_mulVec_g _ _ hR, Chapter06.g_apply]
  calc ∑ i : Fin m, Krylov.gvec (tfqmrH A b x₀ rs₀) (tfqmrDelta A b x₀ rs₀ 0) (i : ℕ)
        • Chapter06.dqgmresP (tfqmrU A b x₀ rs₀) (tfqmrH A b x₀ rs₀) 1 (i : ℕ)
      = ∑ i : Fin m, ∑ j : Fin m,
          (Chapter06.R (tfqmrH A b x₀ rs₀) m i j
            * Chapter06.qgmresY (tfqmrH A b x₀ rs₀) (tfqmrDelta A b x₀ rs₀ 0) m j)
            • Chapter06.dqgmresP (tfqmrU A b x₀ rs₀) (tfqmrH A b x₀ rs₀) 1 (i : ℕ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hg i, Matrix.mulVec, dotProduct, Finset.sum_smul]
    _ = ∑ j : Fin m, Chapter06.qgmresY (tfqmrH A b x₀ rs₀) (tfqmrDelta A b x₀ rs₀ 0) m j
          • ∑ i : Fin m, Chapter06.R (tfqmrH A b x₀ rs₀) m i j
            • Chapter06.dqgmresP (tfqmrU A b x₀ rs₀) (tfqmrH A b x₀ rs₀) 1 (i : ℕ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, mul_comm]
    _ = ∑ j : Fin m, Chapter06.qgmresY (tfqmrH A b x₀ rs₀) (tfqmrDelta A b x₀ rs₀ 0) m j
          • tfqmrU A b x₀ rs₀ (j : ℕ) :=
        Finset.sum_congr rfl fun j _ => by rw [sum_R_smul_dqgmresP h j]

/-- **Section 7.4.3** of [saad2003iterative], the quasi-minimal residual property of TFQMR. Let
$A \in \mathbb{K}^{n \times n}$ and $b, x_0, r^*_0 \in \mathbb{K}^n$, and assume that Algorithm
7.8 does not break down through step $m$. Then its iterate is $$x_m = x_0 + U_m y$$ for a vector
$y \in \mathbb{K}^m$ that minimizes the quasi-residual norm $\|\delta_0 e_1 - \bar H_m y\|_2$
over all of $\mathbb{K}^m$, with $\bar H_m$ of (7.81).

This is Algorithm 6.12 on the two-family data of `SaadSparse.Chapter07.equation_7_70`, reached
through Algorithm 6.13 with $k = 1$. The conclusion is `Krylov.IsQuasiMinResidualIterate`.

**Reading.** The equivalence with the reduced solution is asserted only under the explicit nonzero
prefix through index $m$, including the next step length. DQGMRES uses memory one because the
rotated bidiagonal array has only one superdiagonal.
-/
theorem tfqmr_isQuasiMinResidualIterate (m : ℕ) (h : TFQMRNoBreakdown A b x₀ rs₀ m) :
    Krylov.IsQuasiMinResidualIterate (tfqmrU A b x₀ rs₀) (tfqmrH A b x₀ rs₀)
      (tfqmrDelta A b x₀ rs₀ 0) x₀ m (tfqmr A b x₀ rs₀ m).x := by
  rw [tfqmr_eq_qgmres m h]
  exact Chapter06.qgmres_isQuasiMinResidualIterate x₀ _ _ _
    (fun i j hij => tfqmrH_eq_zero_of_succ_lt A b x₀ rs₀ hij)
    (Chapter06.isUnit_R _ (fun i j hij => tfqmrH_eq_zero_of_succ_lt A b x₀ rs₀ hij)
      fun k hk => (givensRho_pos k (h.mono (le_of_lt hk))).ne')

/-- **Equation (7.83)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$ and
$b, x_0, r^*_0 \in \mathbb{K}^n$, and assume that Algorithm 7.8 does not break down through step
$m$ and has no serious breakdown. Then its iterate satisfies $$\|b - Ax_m\|_2 \le \sqrt{m+1} \,
\tau_m.$$

The residual basis $R_{m+1} \Delta_{m+1}^{-1}$ has unit columns, so the constant of
`Krylov.IsQuasiMinResidualIterate.norm_residual_le` is $\sqrt{m+1}$, and the quasi-residual norm
is $|\gamma_{m+1}| = \tau_m$.

**Reading.** Lean states the bound under both the nonzero prefix through index $m$ and the global
condition that zero step lengths have zero image directions. The printed estimate uses the
norm-scaled basis and its quasi-minimality at the indicated step.
-/
theorem equation_7_83 (m : ℕ) (h : TFQMRNoBreakdown A b x₀ rs₀ m)
    (hs : TFQMRNoSeriousBreakdown A b x₀ rs₀) :
    ‖b - op A (tfqmr A b x₀ rs₀ m).x‖
      ≤ Real.sqrt (m + 1) * tfqmrTau A b x₀ rs₀ m := by
  have hδ0 : ∀ i, tfqmrDelta A b x₀ rs₀ i = 0 → tfqmrW A b x₀ rs₀ i = 0 := by
    intro i hi
    rw [← norm_eq_zero, ← norm_tfqmrDelta, hi, norm_zero]
  have hrel := (equation_7_70 (δ := tfqmrDelta A b x₀ rs₀) hs hδ0).2
  have hunit : ∀ i, ‖(tfqmrDelta A b x₀ rs₀ i)⁻¹ • tfqmrW A b x₀ rs₀ i‖ ≤ 1 := by
    intro i
    rcases eq_or_ne (tfqmrW A b x₀ rs₀ i) 0 with h0 | h0
    · rw [h0, smul_zero, norm_zero]
      norm_num
    · rw [norm_smul, norm_inv, norm_tfqmrDelta, inv_mul_cancel₀ (norm_ne_zero_iff.2 h0)]
  have hr : b - op A x₀
      = tfqmrDelta A b x₀ rs₀ 0 • (tfqmrDelta A b x₀ rs₀ 0)⁻¹ • tfqmrW A b x₀ rs₀ 0 := by
    rw [smul_smul, mul_inv_cancel₀ (h.delta_ne_zero (Nat.zero_le m)), one_smul]
    rfl
  have hle := Krylov.IsQuasiMinResidualIterate.norm_residual_le hrel hr
    (fun k hk => (givensRho_pos k (h.mono (le_of_lt hk))).ne')
    (fun w => Krylov.norm_sum_smul_le_sqrt_mul hunit w) (tfqmr_isQuasiMinResidualIterate m h)
  rw [norm_gamma_eq_tfqmrTau m h] at hle
  refine hle.trans_eq ?_
  norm_num

end TFQMR

end SaadSparse.Chapter07

/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Eigen.KrylovEigen
import Numlib.Eigen.NumericalRange
import Numlib.Eigen.Pseudospectrum
import Numlib.Eigen.RayleighRitz
import Numlib.Krylov.Iterate
import Numlib.Krylov.Convergence.GMRES
import Numlib.Krylov.Convergence.GMRES.HessenbergPencil

/-!
# Liesen and Strakoš, §5.7: GMRES in exact arithmetic

The GMRES residual is the evaluation of a normalized polynomial on the initial residual.
For a unitarily diagonalizable operator, a polynomial's maximum over the spectrum gives
a bound on the relative residual. The field of values, closed pseudospectrum, and polynomial
numerical hull are larger sets used in the study of nonnormal operators.

## Main definitions

* Definition 5.7.2, `LiesenStrakos.Chapter05.IsRitzPair`: an eigenvector residual
  in the orthogonal complement of the trial space.
* `LiesenStrakos.Chapter05.IsHarmonicRitzPair`: an eigenvector residual orthogonal to the image
  of the trial space.
* `LiesenStrakos.Chapter05.gmresIterationPolynomial`: a normalized polynomial for the GMRES
  residual.

## Main results

* Theorem 5.7.1, `LiesenStrakos.Chapter05.theorem_5_7_1`: the normalized determinant of the
  Arnoldi pencil is the GMRES iteration polynomial.
* Corollary 5.7.3, `LiesenStrakos.Chapter05.corollary_5_7_3`: its roots are reciprocals of the
  nonzero Ritz values of the inverse on the image Krylov space.

## Deviations from the source

* **Asymptotic convergence factor** (reading). An upper limit defines the expression for an
  arbitrary set. On sets where the limit exists it agrees with the definition in the source.

-/

open Krylov Polynomial
open scoped Matrix

namespace LiesenStrakos.Chapter05

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Equation (5.7.3)** of [liesen2013krylov]. A **GMRES iteration polynomial** at step $n$ has
degree at most $n$, value $1$ at $0$, and maps the initial residual to the $n$-th GMRES residual.
The definition chooses a witness for the specified iterate. -/
noncomputable def gmresIterationPolynomial {A : E →ₗ[𝕜] E} {b x₀ xₙ : E} {n : ℕ}
    (hx : IsMinResidualIterate A b x₀ n xₙ) : 𝕜[X] :=
  Classical.choose (exists_residual_poly hx.mem)

/-- The chosen GMRES iteration polynomial has degree at most $n$ and value $1$ at $0$ and gives
$b-Ax_n$ when evaluated at $A$ and applied to $b-Ax_0$. -/
theorem gmresIterationPolynomial_spec {A : E →ₗ[𝕜] E} {b x₀ xₙ : E} {n : ℕ}
    (hx : IsMinResidualIterate A b x₀ n xₙ) :
    (gmresIterationPolynomial hx).degree ≤ n ∧ (gmresIterationPolynomial hx).eval 0 = 1 ∧
      b - A xₙ = aeval A (gmresIterationPolynomial hx) (b - A x₀) :=
  Classical.choose_spec (exists_residual_poly hx.mem)

/-- **Definition 5.7.2** of [liesen2013krylov]. A **Ritz value** $\theta$ and corresponding
**Ritz vector** $y$ of $A$ on $\mathcal{W}$ satisfy
$y\ne0$, $y\in\mathcal{W}$, and $Ay-\theta y\perp\mathcal{W}$. -/
abbrev IsRitzPair (A : E →ₗ[𝕜] E) (W : Submodule 𝕜 E) (θ : 𝕜) (y : E) : Prop :=
  Krylov.IsRitzPair A W θ y

/-- **Section 5.7.1** of [liesen2013krylov]. A **harmonic Ritz pair** $(\theta,y)$ for $A$ on
$\mathcal{W}$ has $y\ne0$, $y\in\mathcal{W}$, and $Ay-\theta y\perp A\mathcal{W}$. -/
abbrev IsHarmonicRitzPair (A : E →ₗ[𝕜] E) (W : Submodule 𝕜 E) (θ : 𝕜) (y : E) : Prop :=
  Krylov.IsObliqueRitzPair A W (W.map A) θ y


section Invertible

variable [FiniteDimensional 𝕜 E] {A : E ≃ₗ[𝕜] E} {b x₀ xₙ : E} {n : ℕ}
variable (hx : IsMinResidualIterate (A : E →ₗ[𝕜] E) b x₀ n xₙ)
variable (hn : n ≤ grade (A : E →ₗ[𝕜] E) (b - A x₀))

include hn in
/-- Through the grade of the initial residual, the GMRES iteration polynomial is the
reverse of the characteristic polynomial of the inverse compressed to the image Krylov space. -/
theorem gmresIterationPolynomial_eq_inverseCompressionResidualPoly :
    gmresIterationPolynomial hx = inverseCompressionResidualPoly A (b - A x₀) n := by
  obtain ⟨hdeg, h0, hr⟩ := gmresIterationPolynomial_spec hx
  exact hx.residualPoly_eq_inverseCompressionResidualPoly hn _ hdeg h0 hr

include hn in
/-- **Theorem 5.7.1** of [liesen2013krylov]. Let $A$ be invertible in finite dimension,
$r_0=b-Ax_0$, and $x_n$ the GMRES iterate at a step at most the grade of $r_0$.
Write $H_n$ and $\underline H_n$ for the square and rectangular Arnoldi matrices.
Then $G=\underline H_n^*\underline H_n$ is nonsingular and the iterate is
$x_n=x_0+V_nG^{-1}H_n^*(\|r_0\|e_1)$ with Arnoldi basis $V_n$. For all $\mu$,
$$\varphi_n^{MR}(\mu)=\frac{\det(\mu H_n^*-G)}{(-1)^n\det G}.$$
Thus $\mu$ is a root precisely when $Gz=\mu H_n^*z$ for some nonzero $z$. -/
theorem theorem_5_7_1 :
    let r := b - A x₀
    let H := Arnoldi.hessenberg (A : E →ₗ[𝕜] E) r n
    let H₀ := Arnoldi.hessenbergSq (A : E →ₗ[𝕜] E) r n
    let G := H.conjTranspose * H
    let t := G⁻¹ *ᵥ (H₀.conjTranspose *ᵥ firstVec (‖r‖ : 𝕜) n)
    IsUnit G ∧
      xₙ = x₀ + ∑ j : Fin n, t j • Arnoldi.vec (A : E →ₗ[𝕜] E) r j.val ∧
      (∀ μ : 𝕜, (gmresIterationPolynomial hx).eval μ =
        (μ • H₀.conjTranspose - G).det / ((-1 : 𝕜) ^ n * G.det)) ∧
      ∀ μ : 𝕜, (gmresIterationPolynomial hx).IsRoot μ ↔
        ∃ z, Matrix.HasPencilEigenvector G H₀.conjTranspose μ z := by
  let r := b - A x₀
  let H := Arnoldi.hessenberg (A : E →ₗ[𝕜] E) r n
  let H₀ := Arnoldi.hessenbergSq (A : E →ₗ[𝕜] E) r n
  let G := H.conjTranspose * H
  have hG : IsUnit G := Arnoldi.isUnit_hessenberg_gram A r hn
  have hD : G.det ≠ 0 := isUnit_iff_ne_zero.1 ((Matrix.isUnit_iff_isUnit_det G).1 hG)
  have hp := (gmresIterationPolynomial_eq_inverseCompressionResidualPoly hx hn).trans
    (inverseCompressionResidualPoly_eq_normalized_hessenbergPencil A r hn)
  change gmresIterationPolynomial hx = C G.det⁻¹ * Matrix.pencilPoly G H₀.conjTranspose at hp
  refine ⟨hG, Arnoldi.eq_arnoldi_normal_equations hn hx, ?_, ?_⟩
  · intro μ
    change (gmresIterationPolynomial hx).eval μ =
      (μ • H₀.conjTranspose - G).det / ((-1 : 𝕜) ^ n * G.det)
    have hsign : (μ • H₀.conjTranspose - G).det =
        (-1 : 𝕜) ^ n * (G - μ • H₀.conjTranspose).det := by
      rw [← neg_sub, Matrix.det_neg, Fintype.card_fin]
    rw [hp, eval_mul, eval_C, Matrix.pencilPoly_eval, hsign,
      mul_div_mul_left _ _ (pow_ne_zero n (neg_ne_zero.mpr one_ne_zero)), div_eq_inv_mul]
  · intro μ
    change (gmresIterationPolynomial hx).IsRoot μ ↔
      ∃ z, Matrix.HasPencilEigenvector G H₀.conjTranspose μ z
    rw [hp, IsRoot.def, eval_mul, eval_C, mul_eq_zero, inv_eq_zero, or_iff_right hD,
      ← IsRoot.def, ← Matrix.mem_pencilSpectrum_iff_isRoot, Matrix.mem_pencilSpectrum_iff_exists]

include hn in
/-- **Corollary 5.7.3** of [liesen2013krylov]. For invertible $A$ and a GMRES step $n$ through
the grade, the roots of the GMRES iteration polynomial are the reciprocals of the nonzero
Ritz values of $A^{-1}$ with respect to $A\mathcal K_n(A,r_0)$. -/
theorem corollary_5_7_3 (μ : 𝕜) :
    (gmresIterationPolynomial hx).IsRoot μ ↔
      μ ≠ 0 ∧ ∃ y, IsRitzPair (A.symm : E →ₗ[𝕜] E)
        ((subspace (A : E →ₗ[𝕜] E) (b - A x₀) n).map (A : E →ₗ[𝕜] E)) μ⁻¹ y := by
  rw [gmresIterationPolynomial_eq_inverseCompressionResidualPoly hx hn]
  exact isRoot_inverseCompressionResidualPoly_iff A (b - A x₀) n μ

end Invertible

/-- **Theorem 5.7.4** of [liesen2013krylov], normal-matrix bound. Let $A$ admit a nonempty
finite orthonormal eigenbasis with eigenvalues $\lambda_i$, let $r_0=b-Ax_0\ne0$, and let
$x_n$ be the GMRES iterate. Then
$$\frac{\|b-Ax_n\|}{\|r_0\|}\le
 \inf_{\deg p\le n,\ p(0)=1}\max_i|p(\lambda_i)|.$$
The finite orthonormal eigenbasis expresses the unitary diagonalisation assumed in the source. -/
theorem theorem_5_7_4_normal {ι : Type*} [Fintype ι] [Nonempty ι]
    {A : E →ₗ[𝕜] E} {b x₀ xₙ : E} {n : ℕ}
    (basis : OrthonormalBasis ι 𝕜 E) (μ : ι → 𝕜)
    (hμ : ∀ i, A (basis i) = μ i • basis i)
    (hr : b - A x₀ ≠ 0) (hx : IsMinResidualIterate A b x₀ n xₙ) :
    ‖b - A xₙ‖ / ‖b - A x₀‖ ≤
      ⨅ p : {p : 𝕜[X] // p.degree ≤ n ∧ p.eval 0 = 1}, ⨆ i, ‖p.1.eval (μ i)‖ := by
  have : Nonempty {p : 𝕜[X] // p.degree ≤ (n : WithBot ℕ) ∧ p.eval 0 = 1} :=
    ⟨⟨1, by simp, by simp⟩⟩
  refine le_ciInf fun p => (div_le_iff₀ (norm_pos_iff.mpr hr)).2 ?_
  have hval : ∀ i, ‖p.1.eval (μ i)‖ ≤ ⨆ i, ‖p.1.eval (μ i)‖ :=
    fun i => le_ciSup (f := fun j => ‖p.1.eval (μ j)‖) (Finite.bddAbove_range _) i
  have hnn : 0 ≤ ⨆ i, ‖p.1.eval (μ i)‖ :=
    (norm_nonneg _).trans (hval (Classical.choice ‹Nonempty ι›))
  exact (hx.norm_residual_le_norm_aeval p.1 p.2.1 p.2.2).trans
    (basis.norm_aeval_apply_le_of_forall_repr hμ p.1 hnn (fun i _ => hval i))

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- **Section 5.7.3** of [liesen2013krylov]. The **closed $\varepsilon$-pseudospectrum** consists
of $z$ for which some unit vector $w$ satisfies $\|Aw-zw\|\le\varepsilon$. In finite nonzero
dimension and for $\varepsilon>0$, this is the spectrum together with the points where the
resolvent has norm at least $1/\varepsilon$. -/
noncomputable abbrev closedPseudospectrum (A : F →L[ℂ] F) (ε : ℝ) : Set ℂ :=
  A.closedPseudospectrum ε

/-- **Section 5.7.3** of [liesen2013krylov]. The **field of values** of $A$ is the set of all
$\langle v,Av\rangle$ for unit vectors $v$. -/
abbrev fieldOfValues (A : F →ₗ[ℂ] F) : Set ℂ := A.numericalRange

/-- **Section 5.7.3** of [liesen2013krylov]. The **order-$n$ polynomial numerical hull** consists
of $z$ for which $|p(z)|\le\|p(A)\|$ for all polynomials $p$ of degree at most $n$. -/
def polynomialNumericalHull (A : F →L[ℂ] F) (n : ℕ) : Set ℂ :=
  {z | ∀ p : ℂ[X], p.degree ≤ n → ‖p.eval z‖ ≤ ‖aeval A p‖}

/-- **Section 5.7.6** of [liesen2013krylov]. The **asymptotic convergence factor** of the set
$\Omega$ is the upper limit as $n\to\infty$ of the $n$-th root of
$\inf_{\deg p\le n,\,p(0)=1}\sup_{z\in\Omega}|p(z)|$.

**Reading.** The source considers sets for which the limit exists. The upper limit defines an
expression on arbitrary sets and gives the same value under the existence of the limit. -/
noncomputable def asymptoticSetConvergenceFactor (Ω : Set ℂ) : ℝ :=
  Filter.limsup (fun n : ℕ =>
    (⨅ p : {p : ℂ[X] // p.degree ≤ n ∧ p.eval 0 = 1}, ⨆ z : Ω, ‖p.1.eval z.1‖) ^
      (1 / (n : ℝ))) Filter.atTop


/-- **Lemma 5.7.6** of [liesen2013krylov]. Suppose $A$ is injective, $d$ is the finite grade
of $r_0=b-Ax_0$, and the orthonormal family $(w_i)_{i<d}$ has prefixes spanning
$A\mathcal K_n(A,r_0)$ for all $n\le d$. Let $r_n=b-Ax_n$ be the GMRES residuals. Then
$$r_n=r_0-\sum_{i<n}\langle w_i,r_0\rangle w_i
     =r_0-\sum_{i<n}\langle w_i,r_i\rangle w_i
     =\sum_{i\ge n}\langle w_i,r_0\rangle w_i.$$
The basis uses zero-based indexing. -/
theorem lemma_5_7_6 {A : E →ₗ[𝕜] E} {b x₀ : E}
    [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]
    (hA : Function.Injective A) {w : Fin (grade A (b - A x₀)) → E} (hw : Orthonormal 𝕜 w)
    (hspan : ∀ n ≤ grade A (b - A x₀),
      Submodule.span 𝕜 (w '' {i | i.val < n}) = (subspace A (b - A x₀) n).map A)
    {x : ℕ → E} (hx : ∀ n, IsMinResidualIterate A b x₀ n (x n))
    {n : ℕ} (hn : n ≤ grade A (b - A x₀)) :
    let r (k : ℕ) := b - A (x k)
    r n = (b - A x₀) - ∑ i : Fin (grade A (b - A x₀)) with i.val < n,
      inner 𝕜 (w i) (b - A x₀) • w i ∧
    r n = (b - A x₀) - ∑ i : Fin (grade A (b - A x₀)) with i.val < n,
      inner 𝕜 (w i) (r i.val) • w i ∧
    r n = ∑ i : Fin (grade A (b - A x₀)) with n ≤ i.val, inner 𝕜 (w i) (b - A x₀) • w i := by
  have h1 := (hx n).residual_eq_sub_sum_prefix hw (hspan n hn)
  refine ⟨h1, ?_, IsMinResidualIterate.residual_eq_sum_tail hA hw hspan hx hn⟩
  refine h1.trans ?_
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  change inner 𝕜 (w i) (b - A x₀) • w i = inner 𝕜 (w i) (b - A (x i.val)) • w i
  rw [(IsMinResidualIterate.residual_succ_decomposition hw hspan hx i).2.1]

/-- **Lemma 5.7.6** of [liesen2013krylov], one step. For an orthonormal family with prefixes
spanning the mapped Krylov spaces, the decomposition
$r_i=\langle w_i,r_0\rangle w_i+r_{i+1}$ is orthogonal, with
$\langle w_i,r_i\rangle=\langle w_i,r_0\rangle$. Consequently
$\|r_i\|^2-\|r_{i+1}\|^2=|\langle w_i,r_0\rangle|^2$. The index $i$ starts at zero. -/
theorem lemma_5_7_6_step {A : E →ₗ[𝕜] E} {b x₀ : E}
    {w : Fin (grade A (b - A x₀)) → E} (hw : Orthonormal 𝕜 w)
    (hspan : ∀ n ≤ grade A (b - A x₀),
      Submodule.span 𝕜 (w '' {i | i.val < n}) = (subspace A (b - A x₀) n).map A)
    {x : ℕ → E} (hx : ∀ n, IsMinResidualIterate A b x₀ n (x n))
    (i : Fin (grade A (b - A x₀))) :
    let r (k : ℕ) := b - A (x k)
    r i.val = inner 𝕜 (w i) (b - A x₀) • w i + r (i.val + 1) ∧
    inner 𝕜 (w i) (r i.val) = inner 𝕜 (w i) (b - A x₀) ∧
    ‖r i.val‖ ^ 2 - ‖r (i.val + 1)‖ ^ 2 = ‖inner 𝕜 (w i) (b - A x₀)‖ ^ 2 :=
  IsMinResidualIterate.residual_succ_decomposition hw hspan hx i

end LiesenStrakos.Chapter05

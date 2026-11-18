/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Matrix.ToEuclideanLin
import NumlibSurface.ConnGouldToint.Chapter07.Section03
import NumlibSurface.ConnGouldToint.Chapter07.Section03Direction

/-!
# Conn, Gould and Toint, Section 7.3: Hard-case convergence with LINPACK matrix certificates

This module specializes the hard-case analysis of the Moré–Sorensen iteration in Section 7.3 of
[conn2000trust] to a real symmetric matrix $M \in \mathbb{R}^{n \times n}$ with $n \ge 1$ and least
eigenvalue $\lambda_1$. At a multiplier $x > -\lambda_1$ the matrix $M + xI$ has a Cholesky factor
$L$. The LINPACK technique of Section 7.3.7 solves $Lw = v$ by forward substitution, with entries
$v_i \in \{1, -1\}$ chosen row by row, then solves $L^T y = w$, and uses $u = y / \|y\|$ as an
approximate leftmost eigenvector. Call the triple $(v, w, y)$ a **certified back solve** for $L$ if
$Lw = v$, $L^T y = w$ and $v_i = \sigma(v_i - L_{ii} w_i)$ for every $i$, where $\sigma(b) = 1$ if
$|1 - b| \ge |-1 - b|$ and $\sigma(b) = -1$ otherwise.

The module proves that $u$ is a unit vector whose curvature $u^T (M + xI) u$ is the Rayleigh
quotient $y^T L L^T y / y^T y$, that this curvature tends to zero as $x \to -\lambda_1$, that
$x - y^T L L^T y / y^T y$ is a lower bound for $-\lambda_1$, and that these certificates give the
hard-case conclusions of Theorem 7.3.4 for the safeguarded multiplier recurrence. The proofs use the
operator results `ConnGouldToint.Chapter07.moreSorensen_hard_safeguarded_run` and
`ConnGouldToint.Chapter07.moreSorensen_hard_safeguarded_corrections` of
`NumlibSurface.ConnGouldToint.Chapter07.Section03` and the direction bounds of
`NumlibSurface.ConnGouldToint.Chapter07.Section03Direction`.

## Main definitions

* Section 7.3.7, `ConnGouldToint.Chapter07.linpackEuclideanDirection`: the back-solve vector $y$
  normalized to Euclidean length one.

## Main results

* Section 7.3.7, `ConnGouldToint.Chapter07.linpackEuclideanDirection_spec`: for a certified back
  solve, $u$ is a unit vector and $u^T L L^T u = y^T L L^T y / y^T y$.
* Equation (7.3.16), `ConnGouldToint.Chapter07.linpackEuclideanCurvature_tendsto`: along certified
  Cholesky factorizations of $M + x_k I$ with $x_k \to -\lambda_1$, the curvature
  $u_k^T (M + x_k I) u_k$ tends to zero.
* Algorithm 7.3.4, Step 3b(ii), `ConnGouldToint.Chapter07.linpackEuclidean_lower_bound`: a certified
  back solve for a factor of $M + xI$ gives the lower bound
  $x - y^T L L^T y / y^T y \le -\lambda_1$.
* Theorem 7.3.4, `ConnGouldToint.Chapter07.moreSorensen_hard_matrix_run`: in the hard case, the
  safeguarded recurrence with certified factorizations converges to $-\lambda_1$, and the
  boundary-corrected steps converge in model value and have only minimizers as cluster points.

## Implementation notes

* The matrix $M$ acts on `EuclideanSpace ℝ (Fin n)` through `Matrix.toEuclideanCLM`. Its least
  eigenvalue $\lambda_1$ is `Subproblem.leftmost hM`, so the pole of the secular equation is
  `-leftmost hM`.
* The sign $\sigma$ is `ConnGouldToint.Chapter07.linpackSign`, and the Rayleigh quotient
  $y^T A y / y^T y$ is `ConnGouldToint.Chapter07.linpackCurvature A y`.

## Deviations from the source

* **Section 7.3.7, LINPACK sign rule** (correction). The certificates use the rule $\sigma$, which
  compares the magnitudes $|1 - b|$ and $|-1 - b|$. The printed comparison of the signed candidates
  always selects $v_i = 1$. See `ConnGouldToint.Chapter07.linpackSign`.
-/

namespace ConnGouldToint.Chapter07

open Matrix Subproblem Filter Set WithLp
open scoped RealInnerProductSpace Topology

/-- **Section 7.3.7** of [conn2000trust], unit back-solve direction. For $y \in \mathbb{R}^n$, the
**LINPACK direction** is the vector $u = \|y\|^{-1} y$ of the Euclidean space $\mathbb{R}^n$.

For $y = 0$ the definition gives $u = 0$, because `‖0‖⁻¹ = 0`. -/
noncomputable def linpackEuclideanDirection {n : ℕ} (y : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  ‖(toLp 2 y : EuclideanSpace ℝ (Fin n))‖⁻¹ • toLp 2 y

/-- **Section 7.3.7** of [conn2000trust], normalization and curvature. Let $n \ge 1$, let
$L \in \mathbb{R}^{n \times n}$, and let $v, w, y \in \mathbb{R}^n$ satisfy $Lw = v$,
$L^T y = w$ and $v_i = \sigma(v_i - L_{ii} w_i)$ for every $i$, where $\sigma(b) = 1$ if
$|1 - b| \ge |-1 - b|$ and $\sigma(b) = -1$ otherwise. Then the LINPACK direction
$u = y / \|y\|$ satisfies $\|u\| = 1$ and
$$u^T (L L^T) u = \frac{y^T L L^T y}{y^T y}.$$

The hypotheses force $v \neq 0$, and hence $y \neq 0$. The sign $\sigma$ is
`ConnGouldToint.Chapter07.linpackSign`, the direction is
`ConnGouldToint.Chapter07.linpackEuclideanDirection y`, and the right side is
`ConnGouldToint.Chapter07.linpackCurvature (L * Lᵀ) y`. -/
theorem linpackEuclideanDirection_spec {n : ℕ} (hn : 0 < n)
    {L : Matrix (Fin n) (Fin n) ℝ} {v w y : Fin n → ℝ}
    (hw : L *ᵥ w = v) (hy : Lᵀ *ᵥ y = w)
    (hv : ∀ i, v i = linpackSign (v i - L i i * w i)) :
    ‖linpackEuclideanDirection y‖ = 1 ∧
      ⟪linpackEuclideanDirection y,
        toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (L * Lᵀ) (linpackEuclideanDirection y)⟫ =
        linpackCurvature (L * Lᵀ) y := by
  have hyne : y ≠ 0 := by
    intro h
    have hz : w = 0 := by simpa [h] using hy.symm
    have hvz : v = 0 := by simpa [hz] using hw.symm
    let i : Fin n := ⟨0, hn⟩
    have h := abs_linpackSign (v i - L i i * w i)
    rw [← hv i, hvz] at h
    norm_num at h
  have hpos : 0 < ‖(toLp 2 y : EuclideanSpace ℝ (Fin n))‖ := by
    apply norm_pos_iff.mpr
    intro h
    exact hyne (congrArg ofLp h)
  let c := ‖(toLp 2 y : EuclideanSpace ℝ (Fin n))‖⁻¹
  have hdir : linpackEuclideanDirection y = toLp 2 (c • y) := by
    rw [WithLp.toLp_smul]
    rfl
  have hnorm : ‖linpackEuclideanDirection y‖ = 1 := by
    unfold linpackEuclideanDirection
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hpos.le),
      inv_mul_cancel₀ hpos.ne']
  have hunit : (c • y) ⬝ᵥ (c • y) = 1 := by
    rw [← EuclideanSpace.inner_toLp_toLp_real, ← hdir, real_inner_self_eq_norm_sq, hnorm, one_pow]
  refine ⟨hnorm, ?_⟩
  rw [hdir, Matrix.toEuclideanCLM_toLp, EuclideanSpace.inner_toLp_toLp_real]
  exact (linpackCurvature_eq_of_normalization _ rfl hunit).symm

private theorem det_shift_leftmost_eq_zero {n : ℕ} (hn : 0 < n)
    {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric) :
    (M + (-leftmost hM) • 1).det = 0 := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨i, hi⟩ := exists_eigenvalues_eq_leftmost (hH := hM)
  let z : EuclideanSpace ℝ (Fin n) := hM.eigenvectorBasis rfl i
  have hnorm : ‖z‖ = 1 := (hM.eigenvectorBasis rfl).orthonormal.norm_eq_one i
  have hz : (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M + (-leftmost hM) • 1) z = 0 := by
    change toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M z + (-leftmost hM) • z = 0
    have he : toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M z = leftmost hM • z := by
      rw [← hi]
      exact apply_eigenvectorBasis' (hH := hM) i
    simp [he, neg_smul]
  by_contra hdet
  have hunit : IsUnit (M + (-leftmost hM) • 1) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hvec : (M + (-leftmost hM) • 1) *ᵥ ofLp z = 0 := by
    rw [← Matrix.toEuclideanCLM_add_smul_one, ← WithLp.toLp_ofLp 2 z,
      Matrix.toEuclideanCLM_toLp] at hz
    exact congrArg ofLp hz
  have hzero : ofLp z = 0 :=
    Matrix.mulVec_injective_iff_isUnit.mpr hunit (hvec.trans (Matrix.mulVec_zero _).symm)
  have hz0 : z = 0 := by
    simpa using congrArg (toLp 2) hzero
  simp [hz0] at hnorm

/-- **Equation (7.3.16)** of [conn2000trust], Euclidean form. Let $n \ge 1$ and let
$M \in \mathbb{R}^{n \times n}$ be symmetric with least eigenvalue $\lambda_1$. Let $f$ be a
filter on an index set, and let $x_k \to -\lambda_1$ along $f$. Suppose that, eventually along
$f$, $L_k$ is lower triangular with positive diagonal, $L_k L_k^T = M + x_k I$, and
$(v_k, w_k, y_k)$ satisfies $L_k w_k = v_k$, $L_k^T y_k = w_k$ and
$(v_k)_i = \sigma((v_k)_i - (L_k)_{ii} (w_k)_i)$ for every $i$, with the sign $\sigma$ of
`ConnGouldToint.Chapter07.linpackSign`. Then the LINPACK directions $u_k = y_k / \|y_k\|$
satisfy
$$u_k^T (M + x_k I) u_k \to 0$$
along $f$.

The directions are `ConnGouldToint.Chapter07.linpackEuclideanDirection (y k)`, and $M$ acts
through `Matrix.toEuclideanCLM`. -/
theorem linpackEuclideanCurvature_tendsto {n : ℕ} (hn : 0 < n)
    {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric)
    {ι : Type*} {f : Filter ι} {x : ι → ℝ} {L : ι → Matrix (Fin n) (Fin n) ℝ}
    {v w y : ι → Fin n → ℝ} (hx : Tendsto x f (𝓝 (-leftmost hM)))
    (hcert : ∀ᶠ k in f, L k * (L k)ᵀ = M + x k • 1 ∧
      (L k).IsLowerTriangular ∧ (∀ i, 0 < L k i i) ∧
      L k *ᵥ w k = v k ∧ (L k)ᵀ *ᵥ y k = w k ∧
      ∀ i, v k i = linpackSign (v k i - L k i i * w k i)) :
    Tendsto (fun k => ⟪linpackEuclideanDirection (y k),
      (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M + x k • 1) (linpackEuclideanDirection (y k))⟫) f
        (𝓝 0) := by
  have hcont : Continuous (fun t : ℝ => (M + t • (1 : Matrix (Fin n) (Fin n) ℝ)).det) := by
    fun_prop
  have hlim := hcont.continuousAt.tendsto.comp hx
  rw [det_shift_leftmost_eq_zero hn hM] at hlim
  have hdet : Tendsto (fun k => (L k * (L k)ᵀ).det) f (𝓝 0) :=
    hlim.congr' (hcert.mono fun _ hk => congrArg Matrix.det hk.1.symm)
  have ht := linpackCurvature_tendsto_zero_of_eventually hn
    (hcert.mono fun _ hk => hk.2) hdet
  apply ht.congr'
  filter_upwards [hcert] with k ⟨hfact, _, _, hw, hy, hv⟩
  rw [← Matrix.toEuclideanCLM_add_smul_one, ← hfact]
  exact (linpackEuclideanDirection_spec hn hw hy hv).2.symm

/-- **Algorithm 7.3.4** of [conn2000trust], Step 3b(ii). Let $n \ge 1$, let
$M \in \mathbb{R}^{n \times n}$ be symmetric with least eigenvalue $\lambda_1$, let
$x \in \mathbb{R}$, and let $L \in \mathbb{R}^{n \times n}$ satisfy $L L^T = M + xI$. If
$Lw = v$, $L^T y = w$ and $v_i = \sigma(v_i - L_{ii} w_i)$ for every $i$, with the sign $\sigma$
of `ConnGouldToint.Chapter07.linpackSign`, then
$$x - \frac{y^T L L^T y}{y^T y} \le -\lambda_1.$$

The quotient is `ConnGouldToint.Chapter07.linpackCurvature (L * Lᵀ) y`, and $\lambda_1$ is
`Subproblem.leftmost hM`. The factor $L$ need not be triangular. -/
theorem linpackEuclidean_lower_bound {n : ℕ} (hn : 0 < n)
    {M L : Matrix (Fin n) (Fin n) ℝ}
    (hM : (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric)
    {x : ℝ} {v w y : Fin n → ℝ} (hfact : L * Lᵀ = M + x • 1)
    (hw : L *ᵥ w = v) (hy : Lᵀ *ᵥ y = w)
    (hv : ∀ i, v i = linpackSign (v i - L i i * w i)) :
    x - linpackCurvature (L * Lᵀ) y ≤ -leftmost hM := by
  obtain ⟨hnorm, hcurv⟩ := linpackEuclideanDirection_spec hn hw hy hv
  have h := add_leftmost_mul_norm_sq_le (hH := hM) x (linpackEuclideanDirection y)
  rw [hnorm, one_pow, mul_one, real_inner_comm, ← Matrix.toEuclideanCLM_add_smul_one, ← hfact,
    hcurv] at h
  linarith

/-- **Theorem 7.3.4** of [conn2000trust], hard case with matrix certificates. Let $n \ge 1$, let
$M \in \mathbb{R}^{n \times n}$ be symmetric with least eigenvalue $\lambda_1$, let
$g \in \mathbb{R}^n$ be nonzero, and let $\Delta > 0$ and $\theta \in (0, 1)$. Write
$m(s) = g^T s + \frac{1}{2} s^T M s$ and $s(x) = -(M + xI)^{-1} g$. Assume the hard case: a step
$s^M$ with $\|s^M\| \le \Delta$ has the trust-region multiplier $-\lambda_1$, that is,
$-\lambda_1 \ge 0$, $(M - \lambda_1 I) s^M = -g$, $M - \lambda_1 I$ is positive semidefinite and
$\lambda_1 (\|s^M\| - \Delta) = 0$. Let $\ell_k, h_k, x_k, b_k, \alpha_k \in \mathbb{R}$,
$L_k \in \mathbb{R}^{n \times n}$ and $v_k, w_k, y_k \in \mathbb{R}^n$ satisfy the following
conditions for every $k$, where $u_k = y_k / \|y_k\|$.

* $0 \le \ell_0 \le -\lambda_1 < h_0$ and $\ell_0 \le x_0 \le h_0$.
* If $x_k \le -\lambda_1$, then $b_k \le -\lambda_1$.
* If $x_k > -\lambda_1$, then $L_k$ is lower triangular with positive diagonal,
  $L_k L_k^T = M + x_k I$, $L_k w_k = v_k$, $L_k^T y_k = w_k$,
  $(v_k)_i = \sigma((v_k)_i - (L_k)_{ii} (w_k)_i)$ for every $i$,
  $b_k = x_k - y_k^T L_k L_k^T y_k / y_k^T y_k$, and $\|s(x_k) + \alpha_k u_k\| = \Delta$.
* $(\ell_{k+1}, h_{k+1}, x_{k+1})$ is the safeguarded Moré–Sorensen update of
  $(\ell_k, h_k, x_k)$ with the estimate $b_k$, the pole $-\lambda_1$, the radius $\Delta$ and
  the parameter $\theta$.

Then $x_k \to -\lambda_1$, and $x_k > -\lambda_1$ for infinitely many $k$. Let $j(k) \to \infty$
be any index sequence with $x_{j(k)} > -\lambda_1$ for all $k$, and let
$s_k = s(x_{j(k)}) + \alpha_{j(k)} u_{j(k)}$. Then $m(s_k) \to m(s^M)$. Every limit $z$ of
$(s_{l(k)})$, for an index sequence $l(k) \to \infty$, satisfies $\|z\| \le \Delta$ and
minimizes $m$ on the ball $\|s\| \le \Delta$. If $s^M$ is the only minimizer of $m$ on this
ball, then $s_k \to s^M$.

The scalar $\alpha_k$ can be either root of the boundary equation
$\|s(x_k) + \alpha u_k\| = \Delta$, including the root that minimizes the model. The sign
$\sigma$ is `ConnGouldToint.Chapter07.linpackSign`, the multiplier condition is
`Subproblem.IsTrustRegionMultiplier`, the step $s(x)$ is `ConnGouldToint.Chapter07.shiftedStep`,
the model is `Subproblem.quadModel`, and the update is
`ConnGouldToint.Chapter07.moreSorensenSafeguardedStep`. The proof feeds the three preceding
results into `ConnGouldToint.Chapter07.moreSorensen_hard_safeguarded_run` and
`ConnGouldToint.Chapter07.moreSorensen_hard_safeguarded_corrections`. -/
theorem moreSorensen_hard_matrix_run {n : ℕ} (hn : 0 < n)
    {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric)
    {g sM : EuclideanSpace ℝ (Fin n)} (hg : g ≠ 0)
    {Δ θ : ℝ} {lo hi x b α : ℕ → ℝ} {L : ℕ → Matrix (Fin n) (Fin n) ℝ}
    {v w y : ℕ → Fin n → ℝ} (hΔ : 0 < Δ) (hθ : θ ∈ Ioo 0 1)
    (hsM : ‖sM‖ ≤ Δ)
    (hmul : IsTrustRegionMultiplier g (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M) Δ sM
      (-leftmost hM))
    (hlo : 0 ≤ lo 0) (hlr : lo 0 ≤ -leftmost hM) (hhi : -leftmost hM < hi 0)
    (hx0 : x 0 ∈ Icc (lo 0) (hi 0))
    (hbFailure : ∀ k, x k ≤ -leftmost hM → b k ≤ -leftmost hM)
    (hbSuccess : ∀ k, -leftmost hM < x k →
      b k = x k - linpackCurvature (L k * (L k)ᵀ) (y k))
    (hrec : ∀ k, (lo (k + 1), hi (k + 1), x (k + 1)) =
      moreSorensenSafeguardedStep g (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M) (-leftmost hM) Δ θ
        (lo k) (hi k) (x k) (b k))
    (hcert : ∀ k, -leftmost hM < x k → L k * (L k)ᵀ = M + x k • 1 ∧
      (L k).IsLowerTriangular ∧ (∀ i, 0 < L k i i) ∧
      L k *ᵥ w k = v k ∧ (L k)ᵀ *ᵥ y k = w k ∧
      ∀ i, v k i = linpackSign (v k i - L k i i * w k i))
    (hboundary : ∀ k, -leftmost hM < x k →
      ‖shiftedStep g (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M) (x k) +
        α k • linpackEuclideanDirection (y k)‖ = Δ) :
    Tendsto x atTop (𝓝 (-leftmost hM)) ∧
      (∃ j : ℕ → ℕ, Tendsto j atTop atTop ∧ ∀ k, -leftmost hM < x (j k)) ∧
      ∀ (j : ℕ → ℕ), Tendsto j atTop atTop → (∀ k, -leftmost hM < x (j k)) →
        let s := fun k => shiftedStep g (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M) (x (j k)) +
          α (j k) • linpackEuclideanDirection (y (j k))
        Tendsto (fun k => quadModel g (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M) (s k)) atTop
          (𝓝 (quadModel g (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M) sM)) ∧
          (∀ (l : ℕ → ℕ) (z : EuclideanSpace ℝ (Fin n)), Tendsto l atTop atTop →
            Tendsto (s ∘ l) atTop (𝓝 z) →
            z ∈ Metric.closedBall 0 Δ ∧
              IsMinOn (quadModel g (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M))
                (Metric.closedBall 0 Δ) z) ∧
          ((∀ z ∈ Metric.closedBall 0 Δ,
            IsMinOn (quadModel g (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M))
              (Metric.closedBall 0 Δ) z → z = sM) →
            Tendsto s atTop (𝓝 sM)) := by
  have hb (k : ℕ) : b k ≤ -leftmost hM := by
    rcases le_or_gt (x k) (-leftmost hM) with hk | hk
    · exact hbFailure k hk
    · obtain ⟨hfact, _, _, hw, hy, hv⟩ := hcert k hk
      rw [hbSuccess k hk]
      exact linpackEuclidean_lower_bound hn hM hfact hw hy hv
  have hxlim : Tendsto x atTop (𝓝 (-leftmost hM)) :=
    (moreSorensen_hard_safeguarded_run (H := toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M)
      (hH := hM) hg hΔ hθ hsM hmul hlo hlr hhi.le hx0 hb hrec).2
  let f := (atTop : Filter ℕ) ⊓ 𝓟 {k | -leftmost hM < x k}
  have hsuc : ∀ᶠ k in f, -leftmost hM < x k :=
    mem_inf_of_right (mem_principal_self _)
  have hcurv := linpackEuclideanCurvature_tendsto hn hM (f := f) (hxlim.mono_left inf_le_left)
    (hsuc.mono hcert)
  have hunit (k : ℕ) (hk : -leftmost hM < x k) : ‖linpackEuclideanDirection (y k)‖ = 1 := by
    obtain ⟨_, _, _, hw, hy, hv⟩ := hcert k hk
    exact (linpackEuclideanDirection_spec hn hw hy hv).1
  have hresult := moreSorensen_hard_safeguarded_corrections
    (H := toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M) (hH := hM)
    (α := α) (u := fun k => linpackEuclideanDirection (y k))
    hg hΔ hθ hsM hmul hlo hlr hhi hx0 hb hrec hunit hboundary hcurv
  exact hresult

end ConnGouldToint.Chapter07

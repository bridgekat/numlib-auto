/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Numlib.Eigen.Perturbation
import Numlib.Eigen.QRAlgorithm

/-!
# Rayleigh quotient iteration: local quadratic convergence, and the last row of a shifted QR step

Let $E$ be an inner product space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$ and let $M$ be a
linear operator on $E$. **Rayleigh quotient iteration** is inverse iteration whose shift is
refreshed at every step to the Rayleigh quotient $\rho = \langle v, Mv \rangle$ of the current unit
vector $v$: the next vector is $u / \|u\|$, where $(M - \rho) u = v$. This module proves that the
iteration converges locally quadratically to a simple eigenvalue of a general, nonsymmetric
operator, in the quantitative form of Demmel, *Applied Numerical Linear Algebra* (1997),
§4.4.4–4.4.5, pp. 161–163. Demmel also identifies Rayleigh quotient iteration with the shifted QR
step, and [quarteroni2000numerical] cites him for the quadratic convergence. The module applies the
result to the QR iteration with the Rayleigh-quotient shift $\mu = t_{nn}$ of
[quarteroni2000numerical] (5.53), whose last row is one step of Rayleigh quotient iteration on the
transpose. Related material is in [quarteroni2000numerical] §5.3.2 (inverse iteration) and §5.7.1
(the single-shift QR iteration (5.52)–(5.53)), in §7.5 of the 1989 edition of Golub and Van Loan,
*Matrix Computations*, and in [saad2011numerical] §4.1.

Let $Mx = lx$, and let $y$ be a left eigenvector, $\langle y, Mz \rangle = l \langle y, z \rangle$
for all $z$ (that is, $M^* y = \bar l y$), normalized by $\langle y, x \rangle = 1$. The spectral
projector of $l$ is $Pv = \langle y, v \rangle x$, and $E = \mathbb{K} x \oplus y^\perp$ is an
$M$-invariant splitting. All statements are written in terms of the **complementary component**
$v - \langle y, v \rangle x = (1 - P) v$ of a vector $v$. Two constants describe the eigenvalue: $C$
with $\|(M - l) z\| \le C \|z\|$ for all $z$, and $K$ with $\|w\| \le K \|(M - l) w\|$ for all
$w \perp y$.

## Main definitions

* `Krylov.rqiStep`: one step of Rayleigh quotient iteration.
* `Krylov.rayleighQuotientIterate`: the iteration, started from the normalized starting vector.

## Main results

* `Krylov.norm_inner_map_sub_le`: the Rayleigh quotient of a unit vector is first-order accurate,
  $|\langle v, Mv \rangle - l| \le C \|v - \langle y, v \rangle x\|$, from the identity $\langle v,
  Mv \rangle - l = \langle v, (M - l)(1 - P) v \rangle$ (`Krylov.inner_map_sub_mul_inner_self`).
* `Krylov.norm_sub_inner_smul_le_norm_map_sub_smul`: a small residual $\|Mv - \rho v\|$ at a shift
  $\rho$ near $l$ forces a small complementary component, $\|v - \langle y, v \rangle x\| \le 2K
  (1 + \|x\| \|y\|) \|Mv - \rho v\|$.
* `Krylov.exists_norm_le_mul_norm_map_sub`: in finite dimension the constant $K$ exists when every
  eigenvector of $l$ is a multiple of $x$.
* `Krylov.norm_sub_inner_smul_le_sq_mul_norm`: the step: for a unit vector $v$ with complementary
  component $\eta$ in the basin $4\eta \le 1$, $2KC\eta \le 1$, the solution $u$ of
  $(M - \rho) u = v$ at the Rayleigh shift has $\|u - \langle y, u \rangle x\| \le 4KC\eta^2 \|u\|$.
* `Krylov.isUnit_sub_smul_one`: in the basin the shifted operator is invertible whenever the shift
  is not exactly $l$.
* `Krylov.norm_rayleighQuotientIterate_sub_le`: local quadratic convergence, $4KC \|v_k - \langle y,
  v_k \rangle x\| \le (4KC\eta_0)^{2^k}$ for a start in the basin $4\eta_0 \le 1$,
  $4KC\eta_0 \le 1$, as long as no shift is exactly an eigenvalue.
* `Matrix.toEuclideanLin_transpose_euclideanCol_qrQ_last`: for a real QR decomposition $A = QR$, the
  last column $q_n$ of $Q$ satisfies $A^T q_n = r_{nn} e_n$.
* `Matrix.abs_shiftedQrStep_last_le`: for an upper Hessenberg $T$ with $T - t_{nn} I$ nonsingular,
  the canonical QR step $T'$ with shift $t_{nn}$ has $|t'_{nj}| \le 4KC^2\alpha^2 t_{n,n-1}^2$ for
  $j \neq n$ and $|t'_{nn} - l| \le 4KC^2\alpha^2 t_{n,n-1}^2$, with $\alpha = 2K(1 + \|x\| \|y\|)$,
  once $|t_{n,n-1}|$ and $|t_{nn} - l|$ are small.
* `Matrix.abs_shiftedQrStep_last_le_of_conj`: the same bound with the eigenvector data of a matrix
  $A$ and the step taken on a Hessenberg orthogonal conjugate $T = Q^T A Q$, the form that the
  iteration (5.53) uses.
* `Matrix.exists_eigenvector_data_of_rootMultiplicity_eq_one`: an algebraically simple real
  eigenvalue supplies $x$, $y$ and $K$.
* `Matrix.exists_abs_isShiftedQrStep_last_le_sq`: the three combined, for a single-shift step with
  any QR factorization (`Matrix.IsShiftedQrStep`), with constants that depend only on $A$ and $l$.
* `Matrix.isUpperHessenberg_shiftedQrStep`, `Matrix.isUpperHessenberg_rayleighShiftQrIterate`:
  Hessenberg form is preserved as long as no shift is exactly an eigenvalue.

## Proof outline

The complementary component is orthogonal to $y$ (`Krylov.inner_sub_inner_smul`), it commutes with
$M$ and with the shifted operators (`Krylov.map_sub_inner_smul`,
`Krylov.map_sub_inner_smul_sub_smul`), and it is comparable with the distance from $v$ to the
eigenline: $\sin\theta(v, \mathbb{K} x) \|v\| \le \|v - \langle y, v \rangle x\| \le (1 + \|x\|
\|y\|) \sin\theta(v, \mathbb{K} x) \|v\|$ (`Krylov.sinAngle_span_singleton_le`,
`Krylov.norm_sub_inner_smul_le_sinAngle_mul`). The bilinear form of the projector makes the
nonsymmetric case work without any orthogonality: no eigenbasis, no Jordan form and no gap between
eigenvalues is used. The constant $K$ exists in finite dimension because $M - l$ is injective on
$y^\perp$: the eigenspace of $l$ is the line through $x$, which meets $y^\perp$ only in $0$. It
persists near $l$: $\|w\| \le 2K \|(M - \rho) w\|$ on $y^\perp$ for $2K |\rho - l| \le 1$
(`Krylov.norm_le_two_mul_norm_map_sub_smul`, a Neumann-series step written as a lower bound). In one
step, the shifted operator preserves the splitting, contracts the complementary component by at most
$2K$, and divides the eigencomponent by $l - \rho = O(\eta)$, so the ratio is $O(\eta^2)$. For a
symmetric operator the Rayleigh quotient is second-order accurate, which is why Rayleigh quotient
iteration converges cubically there; the general case is only quadratic.

For a real matrix $T$ with $T - \mu I = QR$, the identity $(T - \mu I)^T Q = R^T$ gives
$(T - \mu I)^T q_n = r_{nn} e_n$ for the last column $q_n$ of $Q$: it is one step of inverse
iteration on $T^T$ from $e_n$ with shift $\mu$. With the shift
$\mu = t_{nn} = \langle e_n, T^T e_n \rangle$ this is one step of Rayleigh quotient iteration on
$T^T$, and for a Hessenberg $T$ the residual of $e_n$ is the single entry $|t_{n,n-1}|$
(`Matrix.toEuclideanLin_transpose_single_last_sub_of_isUpperHessenberg`). The last row of
$T' = RQ + \mu I = Q^T T Q$ is $\langle T^T q_n, q_j \rangle$ (`Matrix.transpose_mul_mul_apply`), so
its off-diagonal entries are bounded by $C$ times the complementary component of $q_n$.

## Implementation notes

* The inverse in the iteration is `Ring.inverse`, so that the iteration is total. Statements about a
  step assume that the shifted operator is invertible.
* In the matrix part the operator of the abstract theorems is $M = T^T$. So the vector $x$ with
  $T^T x = lx$ is a left eigenvector of $T$, and the vector $y$ with $Ty = ly$ is a right
  eigenvector of $T$.
* Matrix indices are $0$-based in Lean. The prose writes the last index as $n$; it is
  `Fin.last (N + 1)` for a matrix of order $N + 2$, and $n - 1$ is `Fin.castSucc (Fin.last N)`.
* The surface statement is `QuarteroniSaccoSaleri.Chapter05.equation_5_53_quadratic`. Two of its
  hypotheses are the reading of the book's "$O(\eta_k^2)$": the closeness of $t^{(k)}_{nn}$ to the
  eigenvalue, which says which eigenvalue the last row converges to, and the nonsingularity of every
  shifted matrix, which is the generic case in which the book's QR factorization is unique and
  Hessenberg form is preserved. The book's hypothesis that the matrix is unreduced is not needed.
-/

open Filter Topology

namespace Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-! ### The spectral projector of a simple eigenvalue -/

section Projector

variable {M : E →ₗ[𝕜] E} {l : 𝕜} {x y : E}

/-- If $\langle y, x \rangle = 1$, then the complementary component $v - \langle y, v \rangle x$ of
every vector $v$ is orthogonal to $y$. -/
theorem inner_sub_inner_smul (hyx : inner 𝕜 y x = 1) (v : E) :
    inner 𝕜 y (v - inner 𝕜 y v • x) = 0 := by
  rw [inner_sub_right, inner_smul_right, hyx, mul_one, sub_self]

/-- Let $Mx = lx$ and let $y$ be a left eigenvector of $M$ for $l$. Then the complementary component
commutes with $M$: for every $v$,
$$M(v - \langle y, v \rangle x) = Mv - \langle y, Mv \rangle x.$$
-/
theorem map_sub_inner_smul (hx : M x = l • x)
    (hy : Module.End.IsLeftEigenvector M l y) (v : E) :
    M (v - inner 𝕜 y v • x) = M v - inner 𝕜 y (M v) • x := by
  rw [map_sub, map_smul, hx, hy.inner_apply, smul_smul, mul_comm]

/-- Let $Mx = lx$ and let $y$ be a left eigenvector of $M$ for $l$. Then for every
$\rho \in \mathbb{K}$ and every $v$, the complementary component of $(M - \rho) v$ is $M - \rho$
applied to the complementary component of $v$:
$$(M - \rho)(v - \langle y, v \rangle x) = (M - \rho) v - \langle y, (M - \rho) v \rangle x.$$
-/
theorem map_sub_inner_smul_sub_smul (hx : M x = l • x)
    (hy : Module.End.IsLeftEigenvector M l y) (ρ : 𝕜) (v : E) :
    M (v - inner 𝕜 y v • x) - ρ • (v - inner 𝕜 y v • x) =
      (M v - ρ • v) - inner 𝕜 y (M v - ρ • v) • x := by
  rw [map_sub_inner_smul hx hy, inner_sub_right, inner_smul_right, sub_smul, smul_sub,
    mul_smul]
  abel

/-- Let $Mx = lx$. Then for all $y$ and $v$, with $w = v - \langle y, v \rangle x$,
$$\langle v, Mv \rangle - l \langle v, v \rangle = \langle v, (M - l) w \rangle.$$
So the Rayleigh quotient minus the eigenvalue is controlled by the complementary component. -/
theorem inner_map_sub_mul_inner_self (hx : M x = l • x) (v : E) :
    inner 𝕜 v (M v) - l * inner 𝕜 v v =
      inner 𝕜 v (M (v - inner 𝕜 y v • x) - l • (v - inner 𝕜 y v • x)) := by
  have h : M (v - inner 𝕜 y v • x) - l • (v - inner 𝕜 y v • x) = M v - l • v := by
    rw [map_sub, map_smul, hx, smul_sub, smul_smul, smul_smul, mul_comm (inner 𝕜 y v) l,
      sub_sub_sub_cancel_right]
  rw [h, inner_sub_right, inner_smul_right]

/-- Let $Mx = lx$, and let $\|(M - l) z\| \le C \|z\|$ for all $z$. Then for every $y$ and every
unit vector $v$,
$$|\langle v, Mv \rangle - l| \le C \|v - \langle y, v \rangle x\|.$$
The Rayleigh quotient of a unit vector is first-order accurate in the complementary component. -/
theorem norm_inner_map_sub_le (hx : M x = l • x) {C : ℝ}
    (hC : ∀ z, ‖M z - l • z‖ ≤ C * ‖z‖) {v : E} (hv : ‖v‖ = 1) :
    ‖inner 𝕜 v (M v) - l‖ ≤ C * ‖v - inner 𝕜 y v • x‖ := by
  have h := inner_map_sub_mul_inner_self (y := y) hx v
  rw [inner_self_eq_norm_sq_to_K, hv] at h
  push_cast at h
  rw [one_pow, mul_one] at h
  rw [h]
  calc ‖inner 𝕜 v (M (v - inner 𝕜 y v • x) - l • (v - inner 𝕜 y v • x))‖
      ≤ ‖v‖ * ‖M (v - inner 𝕜 y v • x) - l • (v - inner 𝕜 y v • x)‖ := norm_inner_le_norm _ _
    _ ≤ 1 * (C * ‖v - inner 𝕜 y v • x‖) := by
      rw [hv]
      exact mul_le_mul_of_nonneg_left (hC _) zero_le_one
    _ = C * ‖v - inner 𝕜 y v • x‖ := one_mul _

/-- For all vectors $x$, $y$ and $v$, the complementary component is bounded by the vector: $\|v -
\langle y, v \rangle x\| \le (1 + \|x\| \|y\|) \|v\|$. -/
theorem norm_sub_inner_smul_le (x y v : E) :
    ‖v - inner 𝕜 y v • x‖ ≤ (1 + ‖x‖ * ‖y‖) * ‖v‖ := by
  calc ‖v - inner 𝕜 y v • x‖ ≤ ‖v‖ + ‖inner 𝕜 y v • x‖ := norm_sub_le _ _
    _ = ‖v‖ + ‖inner 𝕜 y v‖ * ‖x‖ := by rw [norm_smul]
    _ ≤ ‖v‖ + ‖y‖ * ‖v‖ * ‖x‖ := by
      gcongr
      exact norm_inner_le_norm _ _
    _ = (1 + ‖x‖ * ‖y‖) * ‖v‖ := by ring

/-- **The resolvent bound on the complementary subspace persists near the eigenvalue.** Let
$K \ge 0$ satisfy $\|w\| \le K \|(M - l) w\|$ for every $w$ with $\langle y, w \rangle = 0$, and
let $2K |\rho - l| \le 1$. Then $\|w\| \le 2K \|(M - \rho) w\|$ for every $w$ with
$\langle y, w \rangle = 0$.

The proof is a Neumann-series step written as a lower bound. -/
theorem norm_le_two_mul_norm_map_sub_smul {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ w, inner 𝕜 y w = 0 → ‖w‖ ≤ K * ‖M w - l • w‖) {ρ : 𝕜}
    (hρ : 2 * K * ‖ρ - l‖ ≤ 1) {w : E} (hw : inner 𝕜 y w = 0) :
    ‖w‖ ≤ 2 * K * ‖M w - ρ • w‖ := by
  have h1 := hK w hw
  have h2 : ‖M w - l • w‖ ≤ ‖M w - ρ • w‖ + ‖ρ - l‖ * ‖w‖ := by
    calc ‖M w - l • w‖ = ‖(M w - ρ • w) + (ρ - l) • w‖ := by
          congr 1
          rw [sub_smul]
          abel
      _ ≤ ‖M w - ρ • w‖ + ‖(ρ - l) • w‖ := norm_add_le _ _
      _ = ‖M w - ρ • w‖ + ‖ρ - l‖ * ‖w‖ := by rw [norm_smul]
  have h3 := mul_le_mul_of_nonneg_left h2 hK0
  have h4 := mul_le_mul_of_nonneg_right hρ (norm_nonneg w)
  nlinarith [norm_nonneg w, norm_nonneg (M w - ρ • w)]

/-- **A small residual forces a small complementary component.** Let $Mx = lx$, let $y$ be a left
eigenvector of $M$ for $l$ with $\langle y, x \rangle = 1$, let $K \ge 0$ satisfy
$\|w\| \le K \|(M - l) w\|$ for every $w \perp y$, and let $2K |\rho - l| \le 1$. Then for every
$v$
$$\|v - \langle y, v \rangle x\| \le 2K (1 + \|x\| \|y\|) \|Mv - \rho v\|.$$
-/
theorem norm_sub_inner_smul_le_norm_map_sub_smul (hx : M x = l • x)
    (hy : Module.End.IsLeftEigenvector M l y) (hyx : inner 𝕜 y x = 1) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ w, inner 𝕜 y w = 0 → ‖w‖ ≤ K * ‖M w - l • w‖) {ρ : 𝕜}
    (hρ : 2 * K * ‖ρ - l‖ ≤ 1) (v : E) :
    ‖v - inner 𝕜 y v • x‖ ≤ 2 * K * (1 + ‖x‖ * ‖y‖) * ‖M v - ρ • v‖ := by
  have h1 := norm_le_two_mul_norm_map_sub_smul hK0 hK hρ (inner_sub_inner_smul hyx v)
  rw [map_sub_inner_smul_sub_smul hx hy] at h1
  calc ‖v - inner 𝕜 y v • x‖
      ≤ 2 * K * ‖(M v - ρ • v) - inner 𝕜 y (M v - ρ • v) • x‖ := h1
    _ ≤ 2 * K * ((1 + ‖x‖ * ‖y‖) * ‖M v - ρ • v‖) := by
      gcongr
      exact norm_sub_inner_smul_le x y _
    _ = 2 * K * (1 + ‖x‖ * ‖y‖) * ‖M v - ρ • v‖ := by ring

/-- **The resolvent bound on the complementary subspace exists** in finite dimension. Let $E$ be
finite-dimensional, let $\langle y, x \rangle = 1$, and suppose that every solution $z$ of
$Mz = lz$ is a multiple of $x$. Then there is $K > 0$ with $\|w\| \le K \|(M - l) w\|$ for every
$w$ with $\langle y, w \rangle = 0$.

The eigenspace of $l$ lies in the line through $x$, which meets the hyperplane $y^\perp$ only in
$0$. So $M - l$ is injective on $y^\perp$, hence bounded below there. -/
theorem exists_norm_le_mul_norm_map_sub [FiniteDimensional 𝕜 E] (hyx : inner 𝕜 y x = 1)
    (hsimple : ∀ z, M z = l • z → ∃ c : 𝕜, z = c • x) :
    ∃ K : ℝ, 0 < K ∧ ∀ w, inner 𝕜 y w = 0 → ‖w‖ ≤ K * ‖M w - l • w‖ := by
  set W : Submodule 𝕜 E := (𝕜 ∙ y)ᗮ with hW
  set f : W →ₗ[𝕜] E := (M - l • LinearMap.id).domRestrict W with hf
  have hfapply : ∀ w : W, f w = M w - l • (w : E) := fun w => rfl
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    rw [hfapply, sub_eq_zero] at hw
    obtain ⟨c, hc⟩ := hsimple w hw
    have hyw : inner 𝕜 y (w : E) = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.2
    rw [hc, inner_smul_right, hyx, mul_one] at hyw
    ext
    rw [hc, hyw, zero_smul]
    rfl
  obtain ⟨K, hK, hfK⟩ := f.exists_antilipschitzWith hker
  refine ⟨K, hK, fun w hw => ?_⟩
  have hwW : w ∈ W := Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hw
  have h := hfK.le_mul_dist ⟨w, hwW⟩ 0
  rw [dist_zero_right, map_zero, dist_zero_right, hfapply] at h
  exact h

/-- **One step of Rayleigh quotient iteration is quadratically convergent at a simple eigenvalue.**
Let $Mx = lx$, let $y$ be a left eigenvector of $M$ for $l$ with $\langle y, x \rangle = 1$, let
$K \ge 0$ satisfy $\|w\| \le K \|(M - l) w\|$ for every $w \perp y$, and let
$\|(M - l) z\| \le C \|z\|$ for all $z$. Let $v$ be a unit vector whose complementary component
$\eta = \|v - \langle y, v \rangle x\|$ satisfies $4\eta \le 1$ and $2KC\eta \le 1$, and let $u$
solve $(M - \rho) u = v$ with the Rayleigh shift $\rho = \langle v, Mv \rangle$. Then
$$\|u - \langle y, u \rangle x\| \le 4KC\eta^2 \|u\|.$$
So the next iterate $u / \|u\|$ has complementary component at most $4KC\eta^2$.

The proof is the perturbation argument of Demmel, *Applied Numerical Linear Algebra*,
§4.4.4–4.4.5, made quantitative. The operator $M - \rho$ preserves the splitting
$E = \mathbb{K} x \oplus y^\perp$. It is bounded below by $1/(2K)$ on $y^\perp$ because
$|\rho - l| \le C\eta$ (`Krylov.norm_le_two_mul_norm_map_sub_smul`), and it divides the
eigencomponent by $l - \rho$, which is of order $\eta$. So the component of $u$ along $x$ is of
order $1/\eta$, while its complementary component is of order $\eta$. -/
theorem norm_sub_inner_smul_le_sq_mul_norm (hx : M x = l • x)
    (hy : Module.End.IsLeftEigenvector M l y) (hyx : inner 𝕜 y x = 1) {K C : ℝ}
    (hK0 : 0 ≤ K) (hK : ∀ w, inner 𝕜 y w = 0 → ‖w‖ ≤ K * ‖M w - l • w‖)
    (hC : ∀ z, ‖M z - l • z‖ ≤ C * ‖z‖) {v : E} (hv : ‖v‖ = 1)
    (hη : 4 * ‖v - inner 𝕜 y v • x‖ ≤ 1) (hη' : 2 * K * C * ‖v - inner 𝕜 y v • x‖ ≤ 1)
    {u : E} (hu : M u - inner 𝕜 v (M v) • u = v) :
    ‖u - inner 𝕜 y u • x‖ ≤ 4 * K * C * ‖v - inner 𝕜 y v • x‖ ^ 2 * ‖u‖ := by
  set ρ := inner 𝕜 v (M v) with hρ
  set η := ‖v - inner 𝕜 y v • x‖ with hηdef
  have hη0 : 0 ≤ η := norm_nonneg _
  have hC0 : 0 ≤ C := by
    have h := hC v
    rw [hv, mul_one] at h
    exact le_trans (norm_nonneg _) h
  have hρl : ‖ρ - l‖ ≤ C * η := norm_inner_map_sub_le hx hC hv
  have hres : 2 * K * ‖ρ - l‖ ≤ 1 := by
    calc 2 * K * ‖ρ - l‖ ≤ 2 * K * (C * η) := by gcongr
      _ = 2 * K * C * η := by ring
      _ ≤ 1 := hη'
  -- the complementary component of `u` solves `(M - ρ) w' = w`
  have hw' : M (u - inner 𝕜 y u • x) - ρ • (u - inner 𝕜 y u • x) = v - inner 𝕜 y v • x := by
    rw [map_sub_inner_smul_sub_smul hx hy, hu]
  have h1 : ‖u - inner 𝕜 y u • x‖ ≤ 2 * K * η := by
    have h := norm_le_two_mul_norm_map_sub_smul hK0 hK hres (inner_sub_inner_smul hyx u)
    rwa [hw'] at h
  -- the eigen-component of `u` is that of `v` divided by `l - ρ`
  have hPu : inner 𝕜 y v = (l - ρ) * inner 𝕜 y u := by
    rw [← hu, inner_sub_right, inner_smul_right, hy.inner_apply, sub_mul]
  have hPv : 1 - η ≤ ‖inner 𝕜 y v‖ * ‖x‖ := by
    have h := norm_le_norm_add_norm_sub' v (inner 𝕜 y v • x)
    rw [norm_smul, hv] at h
    linarith [hηdef]
  have hd : ‖ρ - l‖ = ‖l - ρ‖ := norm_sub_rev _ _
  have hw'd : ‖u - inner 𝕜 y u • x‖ * ‖l - ρ‖ ≤ 2 * K * C * η ^ 2 := by
    calc ‖u - inner 𝕜 y u • x‖ * ‖l - ρ‖ ≤ (2 * K * η) * (C * η) := by
          rw [← hd]
          exact mul_le_mul h1 hρl (norm_nonneg _) (by positivity)
      _ = 2 * K * C * η ^ 2 := by ring
  have hlow : 1 - η - 2 * K * C * η ^ 2 ≤ ‖u‖ * ‖l - ρ‖ := by
    have h := norm_le_norm_add_norm_sub' (inner 𝕜 y u • x) u
    rw [norm_smul, norm_sub_rev] at h
    have h' := mul_le_mul_of_nonneg_right h (norm_nonneg (l - ρ))
    have hyv : ‖inner 𝕜 y v‖ * ‖x‖ = ‖inner 𝕜 y u‖ * ‖x‖ * ‖l - ρ‖ := by
      rw [hPu, norm_mul]
      ring
    rw [hyv] at hPv
    rw [add_mul] at h'
    linarith
  have hhalf : 1 / 2 ≤ ‖u‖ * ‖l - ρ‖ := by
    have h : 2 * K * C * η ^ 2 ≤ η := by
      calc 2 * K * C * η ^ 2 = (2 * K * C * η) * η := by ring
        _ ≤ 1 * η := mul_le_mul_of_nonneg_right hη' hη0
        _ = η := one_mul _
    linarith
  have hdpos : 0 < ‖l - ρ‖ := by
    rcases (norm_nonneg (l - ρ)).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hhalf
      linarith
  refine le_of_mul_le_mul_right ?_ hdpos
  calc ‖u - inner 𝕜 y u • x‖ * ‖l - ρ‖ ≤ 2 * K * C * η ^ 2 := hw'd
    _ = (4 * K * C * η ^ 2) * (1 / 2) := by ring
    _ ≤ (4 * K * C * η ^ 2) * (‖u‖ * ‖l - ρ‖) := by gcongr
    _ = 4 * K * C * η ^ 2 * ‖u‖ * ‖l - ρ‖ := by ring

end Projector

/-! ### The angle to the eigenvector -/

section Angle

variable {x y : E}

/-- For all vectors $x$, $y$ and $v$,
$$\sin\theta(v, \mathbb{K} x) \le \frac{\|v - \langle y, v \rangle x\|}{\|v\|},$$
where $\sin\theta(v, \mathbb{K} x) = \|v - P_{\mathbb{K} x} v\| / \|v\|$ is
`Submodule.sinAngle`. The complementary component dominates the distance to the eigenline,
because the orthogonal projection onto the line is the best approximation from it. Both sides
are $0$ at $v = 0$. -/
theorem sinAngle_span_singleton_le (x y v : E) :
    (𝕜 ∙ x).sinAngle v ≤ ‖v - inner 𝕜 y v • x‖ / ‖v‖ := by
  rw [Submodule.sinAngle]
  refine div_le_div_of_nonneg_right ?_ (norm_nonneg v)
  rw [Submodule.norm_sub_starProjection_eq_infDist]
  have hmem : inner 𝕜 y v • x ∈ ((𝕜 ∙ x : Submodule 𝕜 E) : Set E) :=
    Submodule.mem_span_singleton.mpr ⟨inner 𝕜 y v, rfl⟩
  calc Metric.infDist v ((𝕜 ∙ x : Submodule 𝕜 E) : Set E) ≤ dist v (inner 𝕜 y v • x) :=
        Metric.infDist_le_dist_of_mem hmem
    _ = ‖v - inner 𝕜 y v • x‖ := dist_eq_norm _ _

/-- If $\langle y, x \rangle = 1$, then for every $v$
$$\|v - \langle y, v \rangle x\| \le (1 + \|x\| \|y\|) \sin\theta(v, \mathbb{K} x) \|v\|.$$
So the complementary component is at most $1 + \|x\| \|y\|$ times the distance to the eigenline.
The reason is that $v - \langle y, v \rangle x = (1 - P)(v - cx)$ for every $c$, in particular
when $cx$ is the orthogonal projection of $v$ onto the line. -/
theorem norm_sub_inner_smul_le_sinAngle_mul (hyx : inner 𝕜 y x = 1) (v : E) :
    ‖v - inner 𝕜 y v • x‖ ≤ (1 + ‖x‖ * ‖y‖) * ((𝕜 ∙ x).sinAngle v * ‖v‖) := by
  rw [Submodule.sinAngle_mul_norm]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ((𝕜 ∙ x).starProjection_apply_mem v)
  have h : v - inner 𝕜 y v • x =
      (v - (𝕜 ∙ x).starProjection v) -
        inner 𝕜 y (v - (𝕜 ∙ x).starProjection v) • x := by
    rw [← hc, inner_sub_right, inner_smul_right, hyx, mul_one, sub_smul]
    abel
  rw [h]
  exact norm_sub_inner_smul_le x y _

end Angle

/-! ### Rayleigh quotient iteration -/

section Iteration

/-- **One step of Rayleigh quotient iteration.** For a vector $v$, let
$\rho = \langle v, Mv \rangle$ be its Rayleigh quotient and $u = (M - \rho)^{-1} v$. The step
returns $u / \|u\|$.

The inverse is `Ring.inverse`, so the step is total: it returns $0$ when $M - \rho$ is not
invertible or $u = 0$. Every statement about the step assumes that $M - \rho$ is invertible. -/
noncomputable def rqiStep (M : Module.End 𝕜 E) (v : E) : E :=
  (‖Ring.inverse (M - inner 𝕜 v (M v) • (1 : Module.End 𝕜 E)) v‖ : 𝕜)⁻¹ •
    Ring.inverse (M - inner 𝕜 v (M v) • (1 : Module.End 𝕜 E)) v

/-- **Rayleigh quotient iteration.** For a starting vector $w$, the iterates are $v_0 = w / \|w\|$
and $v_{k+1}$ = one step `Krylov.rqiStep` of Rayleigh quotient iteration from $v_k$. It is
inverse iteration whose shift is updated at every step to the Rayleigh quotient of the current
vector (Demmel, *Applied Numerical Linear Algebra*, §4.4.4–4.4.5; [saad2011numerical] §4.1,
beside the fixed-shift iteration `Krylov.inverseIterate`).

For $w = 0$ the iteration starts at $v_0 = 0$. -/
noncomputable def rayleighQuotientIterate (M : Module.End 𝕜 E) (v₀ : E) : ℕ → E
  | 0 => (‖v₀‖ : 𝕜)⁻¹ • v₀
  | k + 1 => rqiStep M (rayleighQuotientIterate M v₀ k)

/-- The iteration starts at the normalized starting vector, $v_0 = w / \|w\|$. -/
@[simp]
theorem rayleighQuotientIterate_zero (M : Module.End 𝕜 E) (v₀ : E) :
    rayleighQuotientIterate M v₀ 0 = (‖v₀‖ : 𝕜)⁻¹ • v₀ := rfl

/-- The iterate $v_{k+1}$ is one step of Rayleigh quotient iteration from $v_k$. -/
theorem rayleighQuotientIterate_succ (M : Module.End 𝕜 E) (v₀ : E) (k : ℕ) :
    rayleighQuotientIterate M v₀ (k + 1) = rqiStep M (rayleighQuotientIterate M v₀ k) := rfl

variable {M : E →ₗ[𝕜] E} {l : 𝕜} {x y : E}

/-- **In the basin, the shifted operator is injective unless the shift is the eigenvalue.** Let
$Mx = lx$, let $y$ be a left eigenvector of $M$ for $l$ with $\langle y, x \rangle = 1$, let
$K \ge 0$ satisfy $\|w\| \le K \|(M - l) w\|$ for every $w \perp y$, and let $\rho \neq l$
satisfy $2K |\rho - l| \le 1$. If $(M - \rho) z = 0$, then $z = 0$.

The complementary component of $z$ vanishes by the resolvent bound, and the eigencomponent
vanishes because $\rho \neq l$. -/
theorem eq_zero_of_map_sub_smul_eq_zero (hx : M x = l • x)
    (hy : Module.End.IsLeftEigenvector M l y) (hyx : inner 𝕜 y x = 1) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ w, inner 𝕜 y w = 0 → ‖w‖ ≤ K * ‖M w - l • w‖) {ρ : 𝕜}
    (hρ : 2 * K * ‖ρ - l‖ ≤ 1) (hρl : ρ ≠ l) {z : E} (hz : M z - ρ • z = 0) : z = 0 := by
  have hw : z - inner 𝕜 y z • x = 0 := by
    have h := norm_le_two_mul_norm_map_sub_smul hK0 hK hρ (inner_sub_inner_smul hyx z)
    rw [map_sub_inner_smul_sub_smul hx hy, hz, inner_zero_right, zero_smul, sub_zero,
      norm_zero, mul_zero] at h
    exact norm_le_zero_iff.mp h
  have hz' : z = inner 𝕜 y z • x := sub_eq_zero.mp hw
  have hx0 : x ≠ 0 := fun h => by simp [h] at hyx
  rw [hz', map_smul, hx, smul_smul, smul_smul, ← sub_smul, smul_eq_zero] at hz
  rcases hz with h | h
  · have h' : inner 𝕜 y z * (l - ρ) = 0 := by rw [← h]; ring
    rcases mul_eq_zero.mp h' with h'' | h''
    · rw [hz', h'', zero_smul]
    · exact absurd (sub_eq_zero.mp h'').symm hρl
  · exact absurd h hx0

/-- **In the basin, the shifted operator is invertible unless the shift is the eigenvalue.** Let $E$
be finite-dimensional. Let $Mx = lx$, let $y$ be a left eigenvector of $M$ for $l$ with
$\langle y, x \rangle = 1$, let $K \ge 0$ satisfy $\|w\| \le K \|(M - l) w\|$ for every
$w \perp y$, and let $\rho \neq l$ satisfy $2K |\rho - l| \le 1$. Then $M - \rho$ is invertible. -/
theorem isUnit_sub_smul_one [FiniteDimensional 𝕜 E] (hx : M x = l • x)
    (hy : Module.End.IsLeftEigenvector M l y) (hyx : inner 𝕜 y x = 1) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ w, inner 𝕜 y w = 0 → ‖w‖ ≤ K * ‖M w - l • w‖) {ρ : 𝕜}
    (hρ : 2 * K * ‖ρ - l‖ ≤ 1) (hρl : ρ ≠ l) : IsUnit (M - ρ • (1 : Module.End 𝕜 E)) := by
  rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  exact eq_zero_of_map_sub_smul_eq_zero hx hy hyx hK0 hK hρ hρl hz

/-- **One step of Rayleigh quotient iteration, in the basin.** Let $Mx = lx$, let $y$ be a left
eigenvector of $M$ for $l$ with $\langle y, x \rangle = 1$, let $K \ge 0$ satisfy
$\|w\| \le K \|(M - l) w\|$ for every $w \perp y$, and let $\|(M - l) z\| \le C \|z\|$ for all
$z$. Let $v$ be a unit vector whose complementary component
$\eta = \|v - \langle y, v \rangle x\|$ satisfies $4\eta \le 1$ and $2KC\eta \le 1$, and let
$M - \rho$ be invertible at the Rayleigh shift $\rho = \langle v, Mv \rangle$. Then the next
iterate $v'$ = `Krylov.rqiStep M v` is a unit vector with
$$\|v' - \langle y, v' \rangle x\| \le 4KC\eta^2.$$
-/
theorem rqiStep_spec (hx : M x = l • x)
    (hy : Module.End.IsLeftEigenvector M l y) (hyx : inner 𝕜 y x = 1) {K C : ℝ}
    (hK0 : 0 ≤ K) (hK : ∀ w, inner 𝕜 y w = 0 → ‖w‖ ≤ K * ‖M w - l • w‖)
    (hC : ∀ z, ‖M z - l • z‖ ≤ C * ‖z‖) {v : E} (hv : ‖v‖ = 1)
    (hη : 4 * ‖v - inner 𝕜 y v • x‖ ≤ 1) (hη' : 2 * K * C * ‖v - inner 𝕜 y v • x‖ ≤ 1)
    (hunit : IsUnit (M - inner 𝕜 v (M v) • (1 : Module.End 𝕜 E))) :
    ‖rqiStep M v‖ = 1 ∧
      ‖rqiStep M v - inner 𝕜 y (rqiStep M v) • x‖ ≤ 4 * K * C * ‖v - inner 𝕜 y v • x‖ ^ 2 := by
  set u : E := Ring.inverse (M - inner 𝕜 v (M v) • (1 : Module.End 𝕜 E)) v with hudef
  have hu : M u - inner 𝕜 v (M v) • u = v := by
    have h := congrArg (fun f : Module.End 𝕜 E => f v) (Ring.mul_inverse_cancel _ hunit)
    simpa [Module.End.mul_apply, hudef] using h
  have hu0 : u ≠ 0 := fun h => by
    rw [h, map_zero, smul_zero, sub_zero] at hu
    rw [← hu, norm_zero] at hv
    exact zero_ne_one hv
  have hun : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu0
  have hstep := norm_sub_inner_smul_le_sq_mul_norm hx hy hyx hK0 hK hC hv hη hη' hu
  have hrq : rqiStep M v = (‖u‖ : 𝕜)⁻¹ • u := rfl
  refine ⟨?_, ?_⟩
  · rw [hrq, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ hun]
  · have h : rqiStep M v - inner 𝕜 y (rqiStep M v) • x =
        (‖u‖ : 𝕜)⁻¹ • (u - inner 𝕜 y u • x) := by
      rw [hrq, inner_smul_right, smul_sub, mul_smul]
    rw [h, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
    calc ‖u‖⁻¹ * ‖u - inner 𝕜 y u • x‖
        ≤ ‖u‖⁻¹ * (4 * K * C * ‖v - inner 𝕜 y v • x‖ ^ 2 * ‖u‖) := by gcongr
      _ = 4 * K * C * ‖v - inner 𝕜 y v • x‖ ^ 2 := by
        field_simp

/-- **Rayleigh quotient iteration converges locally quadratically at a simple eigenvalue.** Let
$Mx = lx$, let $y$ be a left eigenvector of $M$ for $l$ with $\langle y, x \rangle = 1$, let
$K > 0$ satisfy $\|w\| \le K \|(M - l) w\|$ for every $w \perp y$, and let $C > 0$ satisfy
$\|(M - l) z\| \le C \|z\|$ for all $z$. Let the starting vector $v_0$ be a unit vector whose
complementary component $\eta_0 = \|v_0 - \langle y, v_0 \rangle x\|$ satisfies $4\eta_0 \le 1$
and $4KC\eta_0 \le 1$. Suppose that no Rayleigh shift is exactly an eigenvalue: $M - \rho_k$ is
invertible for every $k$, where $\rho_k = \langle v_k, M v_k \rangle$. Then every iterate $v_k$
is a unit vector with
$$4KC \|v_k - \langle y, v_k \rangle x\| \le (4KC\eta_0)^{2^k}.$$
This is the local statement behind the quadratic convergence of the single-shift QR iteration in
[quarteroni2000numerical] §5.7.1; see Demmel, *Applied Numerical Linear Algebra*, §4.4.4–4.4.5.

The complementary component, and with it the angle to the eigenvector
(`Krylov.sinAngle_span_singleton_le`), is squared at every step. For a symmetric $M$ the
convergence is in fact cubic. The quadratic rate is what the nonsymmetric perturbation argument
gives, because the Rayleigh quotient is only first-order accurate
(`Krylov.norm_inner_map_sub_le`). -/
theorem norm_rayleighQuotientIterate_sub_le (hx : M x = l • x)
    (hy : Module.End.IsLeftEigenvector M l y) (hyx : inner 𝕜 y x = 1) {K C : ℝ}
    (hK0 : 0 < K) (hK : ∀ w, inner 𝕜 y w = 0 → ‖w‖ ≤ K * ‖M w - l • w‖) (hC0 : 0 < C)
    (hC : ∀ z, ‖M z - l • z‖ ≤ C * ‖z‖) {v₀ : E} (hv₀ : ‖v₀‖ = 1)
    (hη : 4 * ‖v₀ - inner 𝕜 y v₀ • x‖ ≤ 1) (hη' : 4 * K * C * ‖v₀ - inner 𝕜 y v₀ • x‖ ≤ 1)
    (hunit : ∀ k, IsUnit (M - inner 𝕜 (rayleighQuotientIterate M v₀ k)
      (M (rayleighQuotientIterate M v₀ k)) • (1 : Module.End 𝕜 E))) (k : ℕ) :
    ‖rayleighQuotientIterate M v₀ k‖ = 1 ∧
      4 * K * C * ‖rayleighQuotientIterate M v₀ k -
          inner 𝕜 y (rayleighQuotientIterate M v₀ k) • x‖ ≤
        (4 * K * C * ‖v₀ - inner 𝕜 y v₀ • x‖) ^ (2 ^ k) := by
  have hKC : 0 < 4 * K * C := by positivity
  induction k with
  | zero =>
    rw [rayleighQuotientIterate_zero, hv₀, RCLike.ofReal_one, inv_one, one_smul, pow_zero,
      pow_one]
    exact ⟨hv₀, le_rfl⟩
  | succ k ih =>
    obtain ⟨hvk, hwk⟩ := ih
    set v := rayleighQuotientIterate M v₀ k with hvdef
    have hpow : (4 * K * C * ‖v₀ - inner 𝕜 y v₀ • x‖) ^ (2 ^ k) ≤
        4 * K * C * ‖v₀ - inner 𝕜 y v₀ • x‖ :=
      pow_le_of_le_one (by positivity) hη' (pow_ne_zero _ two_ne_zero)
    -- the basin is preserved
    have hηk : 4 * ‖v - inner 𝕜 y v • x‖ ≤ 1 := by
      have h1 : 4 * K * C * ‖v - inner 𝕜 y v • x‖ ≤ 4 * K * C * ‖v₀ - inner 𝕜 y v₀ • x‖ :=
        hwk.trans hpow
      have h2 : ‖v - inner 𝕜 y v • x‖ ≤ ‖v₀ - inner 𝕜 y v₀ • x‖ :=
        le_of_mul_le_mul_left h1 hKC
      linarith
    have hηk' : 2 * K * C * ‖v - inner 𝕜 y v • x‖ ≤ 1 := by
      linarith
    obtain ⟨hnorm, hstep⟩ := rqiStep_spec hx hy hyx hK0.le hK hC hvk hηk hηk' (hunit k)
    rw [rayleighQuotientIterate_succ, ← hvdef]
    refine ⟨hnorm, ?_⟩
    calc 4 * K * C * ‖rqiStep M v - inner 𝕜 y (rqiStep M v) • x‖
        ≤ 4 * K * C * (4 * K * C * ‖v - inner 𝕜 y v • x‖ ^ 2) := by gcongr
      _ = (4 * K * C * ‖v - inner 𝕜 y v • x‖) ^ 2 := by ring
      _ ≤ ((4 * K * C * ‖v₀ - inner 𝕜 y v₀ • x‖) ^ (2 ^ k)) ^ 2 := by gcongr
      _ = (4 * K * C * ‖v₀ - inner 𝕜 y v₀ • x‖) ^ (2 ^ (k + 1)) := by
        rw [← pow_mul, pow_succ]

end Iteration

end Krylov


namespace Matrix

/-! ### The last column of the unitary factor and the last row of a shifted QR step -/

section Column

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- For square matrices $M$ and $U$, $M u_j = (MU)_{\cdot j}$, where $u_j$ is the $j$-th column of
$U$. -/
theorem toEuclideanLin_euclideanCol (M U : Matrix n n 𝕜) (j : n) :
    toEuclideanLin M (euclideanCol U j) = euclideanCol (M * U) j := by
  ext i
  simp [euclideanCol, toLpLin_apply, mulVec, dotProduct, Matrix.mul_apply, mul_comm]

/-- For real square matrices $U$ and $T$,
$$(U^T T U)_{ij} = \langle T^T u_i, u_j \rangle,$$
where $u_i$ is the $i$-th column of $U$. So the $i$-th row of the conjugate is $T^T u_i$ tested
against the columns of $U$. -/
theorem transpose_mul_mul_apply (U T : Matrix n n ℝ) (i j : n) :
    (Uᵀ * T * U) i j =
      inner ℝ (toEuclideanLin Tᵀ (euclideanCol U i)) (euclideanCol U j) := by
  rw [← conjTranspose_eq_transpose_of_trivial U, conjTranspose_mul_mul_apply,
    ← conjTranspose_eq_transpose_of_trivial T, toEuclideanLin_conjTranspose_inner_left]

end Column

section Last

variable {N : ℕ}

/-- **The last column of the orthogonal factor.** Let $A \in \mathbb{R}^{n \times n}$, $n = N + 1$,
have the QR decomposition $A = QR$ by `Matrix.qrQ` and `Matrix.qrR`, and let $q_n$ be the last
column of $Q$. Then
$$A^T q_n = r_{nn} e_n.$$

This follows from $A^T Q = R^T Q^T Q = R^T$ and the upper triangularity of $R$. It identifies
the last column of $Q$ with one step of inverse iteration on $A^T$ from $e_n$, as in Demmel,
*Applied Numerical Linear Algebra*, §4.4.5: $q_n$ is proportional to $A^{-T} e_n$ whenever
$r_{nn} \neq 0$. The index $n$ is `Fin.last N`. -/
theorem toEuclideanLin_transpose_euclideanCol_qrQ_last (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    toEuclideanLin Aᵀ (euclideanCol (qrQ A) (Fin.last N)) =
      qrR A (Fin.last N) (Fin.last N) • EuclideanSpace.single (Fin.last N) (1 : ℝ) := by
  have hQ : (qrQ A)ᵀ * qrQ A = 1 := by
    have h := conjTranspose_qrQ_mul_self A
    rwa [conjTranspose_eq_transpose_of_trivial] at h
  have hAQ : Aᵀ * qrQ A = (qrR A)ᵀ := by
    calc Aᵀ * qrQ A = (qrQ A * qrR A)ᵀ * qrQ A := by rw [qrQ_mul_qrR]
      _ = (qrR A)ᵀ := by rw [transpose_mul, Matrix.mul_assoc, hQ, Matrix.mul_one]
  rw [toEuclideanLin_euclideanCol, hAQ]
  ext i
  rw [euclideanCol_apply, transpose_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]
  by_cases hi : i = Fin.last N
  · rw [ite_eq_left hi, hi, mul_one]
  · rw [ite_eq_right hi, mul_zero]
    exact isUpperTriangular_qrR A (lt_of_le_of_ne (Fin.le_last i) hi)

/-- Let $T \in \mathbb{R}^{n \times n}$, $n = N + 2$, be upper Hessenberg. Then the last row of $T$
has at most two nonzero entries; as a vector,
$$T^T e_n - t_{nn} e_n = t_{n,n-1} e_{n-1}.$$
The index $n$ is `Fin.last (N + 1)` and $n - 1$ is `Fin.castSucc (Fin.last N)`. -/
theorem toEuclideanLin_transpose_single_last_sub_of_isUpperHessenberg
    {T : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ} (hT : T.IsUpperHessenberg) :
    toEuclideanLin Tᵀ (EuclideanSpace.single (Fin.last (N + 1)) (1 : ℝ)) -
        T (Fin.last (N + 1)) (Fin.last (N + 1)) • EuclideanSpace.single (Fin.last (N + 1)) (1 : ℝ) =
      T (Fin.last (N + 1)) (Fin.castSucc (Fin.last N)) •
        EuclideanSpace.single (Fin.castSucc (Fin.last N)) (1 : ℝ) := by
  rw [isUpperHessenberg_iff_fin] at hT
  ext i
  rw [PiLp.sub_apply, PiLp.smul_apply, PiLp.smul_apply, PiLp.single_apply, PiLp.single_apply,
    smul_eq_mul, smul_eq_mul, toEuclideanLin_apply, WithLp.ofLp_toLp,
    PiLp.ofLp_single, mulVec_single_one, col_apply, transpose_apply]
  by_cases hi : i = Fin.last (N + 1)
  · have hi' : i ≠ Fin.castSucc (Fin.last N) := by
      rw [hi]; exact fun h => by simpa using congrArg Fin.val h
    rw [ite_eq_left hi, ite_eq_right hi', hi, mul_one, mul_zero, sub_self]
  · rw [ite_eq_right hi, mul_zero, sub_zero]
    by_cases hi' : i = Fin.castSucc (Fin.last N)
    · rw [ite_eq_left hi', hi', mul_one]
    · rw [ite_eq_right hi', mul_zero]
      refine hT _ _ ?_
      have h1 : (i : ℕ) ≠ N + 1 := fun h => hi (Fin.ext (by simpa using h))
      have h2 : (i : ℕ) ≠ N := fun h => hi' (Fin.ext (by simpa using h))
      have h3 := i.isLt
      simp only [Fin.val_last]
      omega

end Last

section Step

variable {N : ℕ}

/-- **One Rayleigh-shift QR step is quadratically convergent in the last row.** Let
$T \in \mathbb{R}^{n \times n}$, $n = N + 2$, be upper Hessenberg. Let $l \in \mathbb{R}$ and
$x, y \in \mathbb{R}^n$ satisfy $T^T x = lx$, $Ty = ly$ and $\langle y, x \rangle = 1$. Let
$K \ge 0$ satisfy $\|w\| \le K \|(T^T - l) w\|$ for every $w \perp y$, and let
$\|(T^T - l) z\| \le C \|z\|$ for all $z$. Write $\alpha = 2K(1 + \|x\| \|y\|)$, $\mu = t_{nn}$
and $t = |t_{n,n-1}|$. Suppose that $T - \mu I$ is nonsingular and
$$4\alpha t \le 1, \qquad 2KC\alpha t \le 1, \qquad 2K |\mu - l| \le 1.$$
Then the canonical QR step $T' = RQ + \mu I$, where $QR = T - \mu I$, satisfies
$$|t'_{nj}| \le 4KC^2\alpha^2 t^2 \quad (j \neq n), \qquad |t'_{nn} - l| \le 4KC^2\alpha^2
  t^2.$$
This follows Demmel, *Applied Numerical Linear Algebra*, §4.4.4–4.4.5.

The last row of $T'$ is $q_n^T T Q$, where the last column $q_n$ of $Q$ is
$(T - \mu I)^{-T} e_n$ normalized (`Matrix.toEuclideanLin_transpose_euclideanCol_qrQ_last`).
This is one step of Rayleigh quotient iteration on $T^T$ from $e_n$: its Rayleigh quotient is
$\mu = t_{nn}$, and its residual is $\|T^T e_n - \mu e_n\| = t$ because $T$ is Hessenberg
(`Matrix.toEuclideanLin_transpose_single_last_sub_of_isUpperHessenberg`). The residual controls
the complementary component $\eta \le \alpha t$ of $e_n$
(`Krylov.norm_sub_inner_smul_le_norm_map_sub_smul`), the step squares it
(`Krylov.norm_sub_inner_smul_le_sq_mul_norm`), and the off-diagonal entries of the last row are
$\langle (T^T - l) q_n, q_j \rangle$, of size $C$ times the complementary component of $q_n$.
The step is `Matrix.shiftedQrStep`; the index $n$ is `Fin.last (N + 1)` and $n - 1$ is
`Fin.castSucc (Fin.last N)`. -/
theorem abs_shiftedQrStep_last_le {T : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ}
    (hT : T.IsUpperHessenberg) {l : ℝ} {x y : EuclideanSpace ℝ (Fin (N + 2))}
    (hx : toEuclideanLin Tᵀ x = l • x) (hy : toEuclideanLin T y = l • y)
    (hyx : inner ℝ y x = 1) {K C : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ w, inner ℝ y w = 0 → ‖w‖ ≤ K * ‖toEuclideanLin Tᵀ w - l • w‖)
    (hC : ∀ z, ‖toEuclideanLin Tᵀ z - l • z‖ ≤ C * ‖z‖)
    (hunit : IsUnit (T - T (Fin.last (N + 1)) (Fin.last (N + 1)) •
      (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ)))
    (hsub1 : 4 * (2 * K * (1 + ‖x‖ * ‖y‖)) *
      |T (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ≤ 1)
    (hsub2 : 2 * K * C * (2 * K * (1 + ‖x‖ * ‖y‖)) *
      |T (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ≤ 1)
    (hdiag : 2 * K * |T (Fin.last (N + 1)) (Fin.last (N + 1)) - l| ≤ 1) :
    (∀ j, j ≠ Fin.last (N + 1) →
      |shiftedQrStep (T (Fin.last (N + 1)) (Fin.last (N + 1))) T (Fin.last (N + 1)) j| ≤
        4 * K * C ^ 2 * (2 * K * (1 + ‖x‖ * ‖y‖)) ^ 2 *
          |T (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ^ 2) ∧
      |shiftedQrStep (T (Fin.last (N + 1)) (Fin.last (N + 1))) T (Fin.last (N + 1))
          (Fin.last (N + 1)) - l| ≤
        4 * K * C ^ 2 * (2 * K * (1 + ‖x‖ * ‖y‖)) ^ 2 *
          |T (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ^ 2 := by
  set n : Fin (N + 2) := Fin.last (N + 1) with hn
  set m : Fin (N + 2) := Fin.castSucc (Fin.last N) with hm
  set μ : ℝ := T n n with hμ
  set M : EuclideanSpace ℝ (Fin (N + 2)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (N + 2)) :=
    toEuclideanLin Tᵀ with hM
  set e : EuclideanSpace ℝ (Fin (N + 2)) := EuclideanSpace.single n (1 : ℝ) with he
  set H : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ := T - μ • 1 with hH
  set A' : ℝ := 2 * K * (1 + ‖x‖ * ‖y‖) with hA'
  set t : ℝ := |T n m| with ht
  -- the left eigenvector condition in operator form
  have hy' : ∀ z, inner ℝ y (M z) = l * inner ℝ y z := fun z => by
    rw [hM, ← conjTranspose_eq_transpose_of_trivial T, toEuclideanLin_conjTranspose_inner_right,
      hy, real_inner_smul_left]
  -- the residual of `e_n` and its Rayleigh quotient
  have he1 : ‖e‖ = 1 := by rw [he, PiLp.norm_single, norm_one]
  have hres : M e - μ • e = T n m • EuclideanSpace.single m (1 : ℝ) :=
    toEuclideanLin_transpose_single_last_sub_of_isUpperHessenberg hT
  have hresn : ‖M e - μ • e‖ = t := by
    rw [hres, norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]
  have hρ : inner ℝ e (M e) = μ := by
    have h : inner ℝ e (M e) - μ * inner ℝ e e = inner ℝ e (M e - μ • e) := by
      rw [inner_sub_right, real_inner_smul_right]
    have hee : inner ℝ e e = 1 := by
      rw [real_inner_self_eq_norm_sq, he1, one_pow]
    have hem : inner ℝ e (EuclideanSpace.single m (1 : ℝ)) = 0 := by
      have hnm : n ≠ m := by
        rw [hn, hm]
        exact fun h => by simpa using congrArg Fin.val h
      rw [he, EuclideanSpace.inner_single_left, PiLp.single_apply, ite_eq_right hnm, mul_zero]
    rw [hres, real_inner_smul_right, hem, mul_zero, hee, mul_one, sub_eq_zero] at h
    exact h
  -- the complementary component of `e_n` is controlled by the residual
  have hC0 : 0 ≤ C := by
    have h := hC e
    rw [he1, mul_one] at h
    exact le_trans (norm_nonneg _) h
  have hη : ‖e - inner ℝ y e • x‖ ≤ A' * t := by
    have h := Krylov.norm_sub_inner_smul_le_norm_map_sub_smul hx hy' hyx hK0 hK (ρ := μ)
      (by rwa [Real.norm_eq_abs]) e
    rwa [hresn] at h
  have hη4 : 4 * ‖e - inner ℝ y e • x‖ ≤ 1 := by
    calc 4 * ‖e - inner ℝ y e • x‖ ≤ 4 * (A' * t) := by gcongr
      _ = 4 * A' * t := by ring
      _ ≤ 1 := hsub1
  have hη2 : 2 * K * C * ‖e - inner ℝ y e • x‖ ≤ 1 := by
    calc 2 * K * C * ‖e - inner ℝ y e • x‖ ≤ 2 * K * C * (A' * t) := by gcongr
      _ = 2 * K * C * A' * t := by ring
      _ ≤ 1 := hsub2
  -- the QR factorization of the shifted matrix and its last column
  have hHunit : IsUnit H.det := (isUnit_iff_isUnit_det H).mp hunit
  have hQQ : (qrQ H)ᴴ * qrQ H = 1 := conjTranspose_qrQ_mul_self H
  have hon : Orthonormal ℝ (euclideanCol (qrQ H)) := orthonormal_euclideanCol hQQ
  have hqn1 : ‖euclideanCol (qrQ H) n‖ = 1 := hon.1 n
  have hqij : ∀ j, j ≠ n → inner ℝ (euclideanCol (qrQ H) n) (euclideanCol (qrQ H) j) = 0 :=
    fun j hj => hon.2 (Ne.symm hj)
  have hrpos : 0 < qrR H n n := qrR_diag_pos hHunit n
  have hHq : M (euclideanCol (qrQ H) n) - μ • euclideanCol (qrQ H) n = qrR H n n • e := by
    have h := toEuclideanLin_transpose_euclideanCol_qrQ_last H
    rwa [hH, transpose_sub, transpose_smul, transpose_one, toEuclideanLin_sub_apply,
      toEuclideanLin_smul_apply, toEuclideanLin_one_apply] at h
  -- the inverse-iteration vector `u = q_n / r_{nn}` solves `(Tᵀ - μ) u = e_n`
  set u : EuclideanSpace ℝ (Fin (N + 2)) := (qrR H n n)⁻¹ • euclideanCol (qrQ H) n with hu
  have hu' : M u - inner ℝ e (M e) • u = e := by
    rw [hρ, hu, map_smul, smul_comm μ, ← smul_sub, hHq, smul_smul, inv_mul_cancel₀ hrpos.ne',
      one_smul]
  have hstep := Krylov.norm_sub_inner_smul_le_sq_mul_norm hx hy' hyx hK0 hK hC he1 hη4 hη2 hu'
  have hqu : euclideanCol (qrQ H) n = qrR H n n • u := by
    rw [hu, smul_smul, mul_inv_cancel₀ hrpos.ne', one_smul]
  -- the complementary component of `q_n` is `O(η²)`
  have hw : ‖euclideanCol (qrQ H) n - inner ℝ y (euclideanCol (qrQ H) n) • x‖ ≤
      4 * K * C * ‖e - inner ℝ y e • x‖ ^ 2 := by
    have h : euclideanCol (qrQ H) n - inner ℝ y (euclideanCol (qrQ H) n) • x =
        qrR H n n • (u - inner ℝ y u • x) := by
      rw [hqu, real_inner_smul_right, smul_sub, mul_smul]
    rw [h, norm_smul, Real.norm_eq_abs, abs_of_pos hrpos]
    calc qrR H n n * ‖u - inner ℝ y u • x‖
        ≤ qrR H n n * (4 * K * C * ‖e - inner ℝ y e • x‖ ^ 2 * ‖u‖) := by gcongr
      _ = 4 * K * C * ‖e - inner ℝ y e • x‖ ^ 2 * (qrR H n n * ‖u‖) := by ring
      _ = 4 * K * C * ‖e - inner ℝ y e • x‖ ^ 2 := by
        rw [← abs_of_pos hrpos, ← Real.norm_eq_abs, ← norm_smul, ← hqu, hqn1, mul_one]
  have hw' : ‖euclideanCol (qrQ H) n - inner ℝ y (euclideanCol (qrQ H) n) • x‖ ≤
      4 * K * C * A' ^ 2 * t ^ 2 := by
    calc ‖euclideanCol (qrQ H) n - inner ℝ y (euclideanCol (qrQ H) n) • x‖
        ≤ 4 * K * C * ‖e - inner ℝ y e • x‖ ^ 2 := hw
      _ ≤ 4 * K * C * (A' * t) ^ 2 := by gcongr
      _ = 4 * K * C * A' ^ 2 * t ^ 2 := by ring
  -- the last row of the step
  have hstep_eq : shiftedQrStep μ T = (qrQ H)ᵀ * T * qrQ H := by
    rw [shiftedQrStep_eq_conj, conjTranspose_eq_transpose_of_trivial]
  have hentry : ∀ j, shiftedQrStep μ T n j =
      inner ℝ (M (euclideanCol (qrQ H) n)) (euclideanCol (qrQ H) j) := fun j => by
    rw [hstep_eq, transpose_mul_mul_apply]
  have hMw : ‖M (euclideanCol (qrQ H) n) - l • euclideanCol (qrQ H) n‖ ≤
      C * ‖euclideanCol (qrQ H) n - inner ℝ y (euclideanCol (qrQ H) n) • x‖ := by
    have h : M (euclideanCol (qrQ H) n) - l • euclideanCol (qrQ H) n =
        M (euclideanCol (qrQ H) n - inner ℝ y (euclideanCol (qrQ H) n) • x) -
          l • (euclideanCol (qrQ H) n - inner ℝ y (euclideanCol (qrQ H) n) • x) := by
      rw [map_sub, map_smul, hx, smul_sub, smul_smul, smul_smul,
        mul_comm (inner ℝ y (euclideanCol (qrQ H) n)) l, sub_sub_sub_cancel_right]
    rw [h]
    exact hC _
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [hentry]
    have h : inner ℝ (M (euclideanCol (qrQ H) n)) (euclideanCol (qrQ H) j) =
        inner ℝ (M (euclideanCol (qrQ H) n) - l • euclideanCol (qrQ H) n)
          (euclideanCol (qrQ H) j) := by
      rw [inner_sub_left, real_inner_smul_left, hqij j hj, mul_zero, sub_zero]
    rw [h, ← Real.norm_eq_abs]
    calc ‖inner ℝ (M (euclideanCol (qrQ H) n) - l • euclideanCol (qrQ H) n)
          (euclideanCol (qrQ H) j)‖
        ≤ ‖M (euclideanCol (qrQ H) n) - l • euclideanCol (qrQ H) n‖ *
            ‖euclideanCol (qrQ H) j‖ := norm_inner_le_norm _ _
      _ = ‖M (euclideanCol (qrQ H) n) - l • euclideanCol (qrQ H) n‖ := by
        rw [hon.1 j, mul_one]
      _ ≤ C * ‖euclideanCol (qrQ H) n - inner ℝ y (euclideanCol (qrQ H) n) • x‖ := hMw
      _ ≤ C * (4 * K * C * A' ^ 2 * t ^ 2) := by gcongr
      _ = 4 * K * C ^ 2 * A' ^ 2 * t ^ 2 := by ring
  · rw [hentry, real_inner_comm, ← Real.norm_eq_abs]
    calc ‖inner ℝ (euclideanCol (qrQ H) n) (M (euclideanCol (qrQ H) n)) - l‖
        ≤ C * ‖euclideanCol (qrQ H) n - inner ℝ y (euclideanCol (qrQ H) n) • x‖ :=
          Krylov.norm_inner_map_sub_le hx hC hqn1
      _ ≤ C * (4 * K * C * A' ^ 2 * t ^ 2) := by gcongr
      _ = 4 * K * C ^ 2 * A' ^ 2 * t ^ 2 := by ring

end Step

/-! ### Transport along an orthogonal similarity -/

section Orthogonal

variable {n : Type*} [Fintype n] [DecidableEq n] {Q : Matrix n n ℝ}

/-- A real orthogonal matrix $Q$ satisfies $Q Q^T = I$. -/
theorem mul_transpose_of_mem_orthogonalGroup (hQ : Q ∈ Matrix.orthogonalGroup n ℝ) :
    Q * Qᵀ = 1 :=
  (Matrix.mem_orthogonalGroup_iff n ℝ).mp hQ

/-- A real orthogonal matrix $Q$ satisfies $Q^T Q = I$. -/
theorem transpose_mul_of_mem_orthogonalGroup (hQ : Q ∈ Matrix.orthogonalGroup n ℝ) :
    Qᵀ * Q = 1 :=
  (Matrix.mem_orthogonalGroup_iff' n ℝ).mp hQ

/-- For a real orthogonal matrix $Q$ and every vector $v$, $Q (Q^T v) = v$. -/
theorem toEuclideanLin_toEuclideanLin_transpose_apply (hQ : Q ∈ Matrix.orthogonalGroup n ℝ)
    (v : EuclideanSpace ℝ n) : toEuclideanLin Q (toEuclideanLin Qᵀ v) = v := by
  rw [← toEuclideanLin_mul_apply, mul_transpose_of_mem_orthogonalGroup hQ,
    toEuclideanLin_one_apply]

/-- For a real orthogonal matrix $Q$ and every vector $v$, $Q^T (Q v) = v$. -/
theorem toEuclideanLin_transpose_toEuclideanLin_apply (hQ : Q ∈ Matrix.orthogonalGroup n ℝ)
    (v : EuclideanSpace ℝ n) : toEuclideanLin Qᵀ (toEuclideanLin Q v) = v := by
  rw [← toEuclideanLin_mul_apply, transpose_mul_of_mem_orthogonalGroup hQ,
    toEuclideanLin_one_apply]

/-- For every real square matrix $Q$ and all vectors $y$, $w$, $\langle Q^T y, w \rangle = \langle
y, Q w \rangle$. This is `Matrix.toEuclideanLin_transpose_inner_left` for a square real matrix. -/
theorem inner_toEuclideanLin_transpose_left (Q : Matrix n n ℝ) (y w : EuclideanSpace ℝ n) :
    inner ℝ (toEuclideanLin Qᵀ y) w = inner ℝ y (toEuclideanLin Q w) :=
  toEuclideanLin_transpose_inner_left Q w y

/-- For a real orthogonal matrix $Q$, every real square matrix $B$ and every vector $v$,
$(Q^T B Q)(Q^T v) = Q^T (B v)$. -/
theorem toEuclideanLin_transpose_mul_mul_apply_transpose (hQ : Q ∈ Matrix.orthogonalGroup n ℝ)
    (B : Matrix n n ℝ) (v : EuclideanSpace ℝ n) :
    toEuclideanLin (Qᵀ * B * Q) (toEuclideanLin Qᵀ v) = toEuclideanLin Qᵀ (toEuclideanLin B v) := by
  rw [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply,
    toEuclideanLin_toEuclideanLin_transpose_apply hQ]

end Orthogonal

section Conj

variable {N : ℕ}

/-- **The one-step bound `Matrix.abs_shiftedQrStep_last_le`, transported along an orthogonal
similarity.** Let $A, T, Q \in \mathbb{R}^{n \times n}$, $n = N + 2$, with $Q$ orthogonal,
$T = Q^T A Q$ and $T$ upper Hessenberg. Let $l \in \mathbb{R}$ and $x, y \in \mathbb{R}^n$
satisfy $A^T x = lx$, $Ay = ly$ and $\langle y, x \rangle = 1$. Let $K \ge 0$ satisfy
$\|w\| \le K \|(A^T - l) w\|$ for every $w \perp y$, and let $\|(A^T - l) z\| \le C \|z\|$ for
all $z$. Write $\alpha = 2K(1 + \|x\| \|y\|)$, $\mu = t_{nn}$ and $t = |t_{n,n-1}|$. Suppose
that $T - \mu I$ is nonsingular and
$$4\alpha t \le 1, \qquad 2KC\alpha t \le 1, \qquad 2K |\mu - l| \le 1.$$
Then the canonical QR step $T'$ from $T$ with shift $\mu$ satisfies
$$|t'_{nj}| \le 4KC^2\alpha^2 t^2 \quad (j \neq n), \qquad |t'_{nn} - l| \le 4KC^2\alpha^2
  t^2.$$

This is the form that the iteration (5.53) of [quarteroni2000numerical] uses, every iterate
being an orthogonal conjugate of the starting matrix. The eigenvectors of $T^T$ and $T$ are
$Q^T x$ and $Q^T y$, with the same norms and inner product, and both bounds with $K$ and $C$ are
invariant because $Q$ is an isometry. -/
theorem abs_shiftedQrStep_last_le_of_conj {A T Q : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ}
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin (N + 2)) ℝ) (hTQ : T = Qᵀ * A * Q)
    (hT : T.IsUpperHessenberg) {l : ℝ} {x y : EuclideanSpace ℝ (Fin (N + 2))}
    (hx : toEuclideanLin Aᵀ x = l • x) (hy : toEuclideanLin A y = l • y)
    (hyx : inner ℝ y x = 1) {K C : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ w, inner ℝ y w = 0 → ‖w‖ ≤ K * ‖toEuclideanLin Aᵀ w - l • w‖)
    (hC : ∀ z, ‖toEuclideanLin Aᵀ z - l • z‖ ≤ C * ‖z‖)
    (hunit : IsUnit (T - T (Fin.last (N + 1)) (Fin.last (N + 1)) •
      (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ)))
    (hsub1 : 4 * (2 * K * (1 + ‖x‖ * ‖y‖)) *
      |T (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ≤ 1)
    (hsub2 : 2 * K * C * (2 * K * (1 + ‖x‖ * ‖y‖)) *
      |T (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ≤ 1)
    (hdiag : 2 * K * |T (Fin.last (N + 1)) (Fin.last (N + 1)) - l| ≤ 1) :
    (∀ j, j ≠ Fin.last (N + 1) →
      |shiftedQrStep (T (Fin.last (N + 1)) (Fin.last (N + 1))) T (Fin.last (N + 1)) j| ≤
        4 * K * C ^ 2 * (2 * K * (1 + ‖x‖ * ‖y‖)) ^ 2 *
          |T (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ^ 2) ∧
      |shiftedQrStep (T (Fin.last (N + 1)) (Fin.last (N + 1))) T (Fin.last (N + 1))
          (Fin.last (N + 1)) - l| ≤
        4 * K * C ^ 2 * (2 * K * (1 + ‖x‖ * ‖y‖)) ^ 2 *
          |T (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ^ 2 := by
  have hQT : Qᵀ ∈ orthogonalGroup (Fin (N + 2)) ℝ := transpose_mem_unitaryGroup_iff.2 hQ
  have hTt : Tᵀ = Qᵀ * Aᵀ * Q := by
    rw [hTQ, transpose_mul, transpose_mul, transpose_transpose, Matrix.mul_assoc]
  have hnormQ : ∀ v : EuclideanSpace ℝ (Fin (N + 2)), ‖toEuclideanLin Q v‖ = ‖v‖ :=
    norm_toEuclideanLin_apply_of_mem_unitaryGroup hQ
  have hnormQT : ∀ v : EuclideanSpace ℝ (Fin (N + 2)), ‖toEuclideanLin Qᵀ v‖ = ‖v‖ :=
    norm_toEuclideanLin_apply_of_mem_unitaryGroup hQT
  -- the transported eigenvectors
  have hx' : toEuclideanLin Tᵀ (toEuclideanLin Qᵀ x) = l • toEuclideanLin Qᵀ x := by
    rw [hTt, toEuclideanLin_transpose_mul_mul_apply_transpose hQ, hx, map_smul]
  have hy' : toEuclideanLin T (toEuclideanLin Qᵀ y) = l • toEuclideanLin Qᵀ y := by
    rw [hTQ, toEuclideanLin_transpose_mul_mul_apply_transpose hQ, hy, map_smul]
  have hyx' : inner ℝ (toEuclideanLin Qᵀ y) (toEuclideanLin Qᵀ x) = 1 := by
    rw [inner_toEuclideanLin_transpose_left, toEuclideanLin_toEuclideanLin_transpose_apply hQ, hyx]
  -- the transported resolvent bounds
  have hres : ∀ w : EuclideanSpace ℝ (Fin (N + 2)),
      toEuclideanLin Tᵀ w - l • w = toEuclideanLin Qᵀ
        (toEuclideanLin Aᵀ (toEuclideanLin Q w) - l • toEuclideanLin Q w) := by
    intro w
    rw [map_sub, map_smul, toEuclideanLin_transpose_toEuclideanLin_apply hQ, hTt,
      toEuclideanLin_mul_apply, toEuclideanLin_mul_apply]
  have hK' : ∀ w, inner ℝ (toEuclideanLin Qᵀ y) w = 0 →
      ‖w‖ ≤ K * ‖toEuclideanLin Tᵀ w - l • w‖ := by
    intro w hw
    rw [inner_toEuclideanLin_transpose_left] at hw
    rw [hres, hnormQT, ← hnormQ w]
    exact hK _ hw
  have hC' : ∀ z, ‖toEuclideanLin Tᵀ z - l • z‖ ≤ C * ‖z‖ := by
    intro z
    rw [hres, hnormQT, ← hnormQ z]
    exact hC _
  have h := abs_shiftedQrStep_last_le hT hx' hy' hyx' hK0 hK' hC' hunit
    (by rwa [hnormQT, hnormQT]) (by rwa [hnormQT, hnormQT]) hdiag
  rwa [hnormQT, hnormQT] at h

end Conj

/-! ### The data of an algebraically simple real eigenvalue -/

section Data

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **An algebraically simple real eigenvalue supplies the eigenvector data of the local convergence
theorem.** Let $A \in \mathbb{R}^{n \times n}$ and let $l$ be a simple root of the
characteristic polynomial of $A$. Then there are $x, y \in \mathbb{R}^n$ and $K > 0$ with
$$A^T x = lx, \qquad Ay = ly, \qquad \langle y, x \rangle = 1,$$
and $\|w\| \le K \|(A^T - l) w\|$ for every $w$ with $\langle y, w \rangle = 0$.

The left and right eigenvectors are not orthogonal at an algebraically simple eigenvalue
(`Module.End.inner_ne_zero_of_finrank_maxGenEigenspace_eq_one`), so they can be normalized. The
constant $K$ exists because the eigenspace of $A^T$ at $l$ is the line through $x$, which meets
$y^\perp$ only in $0$ (`Krylov.exists_norm_le_mul_norm_map_sub`). -/
theorem exists_eigenvector_data_of_rootMultiplicity_eq_one {A : Matrix n n ℝ} {l : ℝ}
    (hl : A.charpoly.rootMultiplicity l = 1) :
    ∃ (x y : EuclideanSpace ℝ n) (K : ℝ), toEuclideanLin Aᵀ x = l • x ∧
      toEuclideanLin A y = l • y ∧ inner ℝ y x = 1 ∧ 0 < K ∧
      ∀ w, inner ℝ y w = 0 → ‖w‖ ≤ K * ‖toEuclideanLin Aᵀ w - l • w‖ := by
  have hroot : A.charpoly.IsRoot l :=
    (Polynomial.rootMultiplicity_pos (A.charpoly_monic.ne_zero)).mp (by rw [hl]; exact one_pos)
  have hrootT : Aᵀ.charpoly.IsRoot l := by rwa [charpoly_transpose]
  -- a right eigenvector of `A` and one of `Aᵀ`
  obtain ⟨y₀, hy₀⟩ := ((hasEigenvalue_toEuclideanLin_iff A l).mpr
    (mem_spectrum_iff_isRoot_charpoly.mpr hroot)).exists_hasEigenvector
  obtain ⟨x, hx⟩ := ((hasEigenvalue_toEuclideanLin_iff Aᵀ l).mpr
    (mem_spectrum_iff_isRoot_charpoly.mpr hrootT)).exists_hasEigenvector
  have hy₀' : toEuclideanLin A y₀ = l • y₀ := hy₀.apply_eq_smul
  have hx' : toEuclideanLin Aᵀ x = l • x := hx.apply_eq_smul
  have hxleft : ∀ z, inner ℝ x (toEuclideanLin A z) = l * inner ℝ x z := fun z => by
    rw [← toEuclideanLin_conjTranspose_inner_left, conjTranspose_eq_transpose_of_trivial, hx',
      real_inner_smul_left]
  have hsimpleA : Module.finrank ℝ (Module.End.maxGenEigenspace (toEuclideanLin A) l) = 1 := by
    rw [finrank_maxGenEigenspace_toEuclideanLin]; exact hl
  have hsimpleT : Module.finrank ℝ (Module.End.maxGenEigenspace (toEuclideanLin Aᵀ) l) = 1 := by
    rw [finrank_maxGenEigenspace_toEuclideanLin, charpoly_transpose]; exact hl
  -- the two eigenvectors are not orthogonal
  have hne : inner ℝ x y₀ ≠ 0 :=
    Module.End.inner_ne_zero_of_finrank_maxGenEigenspace_eq_one hy₀' hy₀.right hxleft hx.right
      hsimpleA
  have hne' : inner ℝ y₀ x ≠ 0 := by rwa [real_inner_comm]
  -- normalize the right eigenvector
  refine ⟨x, (inner ℝ y₀ x)⁻¹ • y₀, ?_⟩
  have hyx : inner ℝ ((inner ℝ y₀ x)⁻¹ • y₀) x = 1 := by
    rw [real_inner_smul_left, inv_mul_cancel₀ hne']
  have hsimple : ∀ z, toEuclideanLin Aᵀ z = l • z → ∃ c : ℝ, z = c • x := by
    intro z hz
    have hmem : z ∈ Module.End.maxGenEigenspace (toEuclideanLin Aᵀ) l :=
      Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hz)
    rw [Module.End.maxGenEigenspace_eq_span_singleton_of_finrank_eq_one hx' hx.right hsimpleT,
      Submodule.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    exact ⟨c, hc.symm⟩
  obtain ⟨K, hK, hKw⟩ := Krylov.exists_norm_le_mul_norm_map_sub hyx hsimple
  exact ⟨K, hx', by rw [map_smul, hy₀', smul_comm], hyx, hK, hKw⟩

end Data

/-! ### Hessenberg form along the shifted iteration -/

section ShiftedStep

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]
  [LocallyFiniteOrderBot n]

/-- **A shifted QR step preserves upper Hessenberg form when the shifted matrix is nonsingular.**
Let $T$ be upper Hessenberg and let $T - \mu I$ be invertible. Then the canonical QR step from
$T$ with shift $\mu$ is upper Hessenberg ([quarteroni2000numerical] §5.6.4 for the unshifted
step).

The step is $RQ + \mu I$ with $R$ upper triangular and $Q$ = `Matrix.qrQ (T - μ • 1)` upper
Hessenberg (`Matrix.isUpperHessenberg_qrQ`). The nonsingularity makes the factor $Q$ unique. At
a singular shift the Gram–Schmidt completion in `Matrix.qrQ` is arbitrary and need not be
Hessenberg. -/
theorem isUpperHessenberg_shiftedQrStep {T : Matrix n n 𝕜} (hT : T.IsUpperHessenberg) {μ : 𝕜}
    (hunit : IsUnit (T - μ • 1)) : (shiftedQrStep μ T).IsUpperHessenberg := by
  have hdet : IsUnit (T - μ • 1).det := (isUnit_iff_isUnit_det _).mp hunit
  exact ((isUpperTriangular_qrR _).mul_isUpperHessenberg
    (isUpperHessenberg_qrQ hdet (hT.sub_smul_one μ))).add_smul_one μ

end ShiftedStep

section RayleighShift

variable {𝕜 : Type*} [RCLike 𝕜] {N : ℕ}

/-- **The Rayleigh-shift QR iteration preserves upper Hessenberg form** as long as no shift is an
eigenvalue. Let $A$ of order $n = N + 1$ be upper Hessenberg, let $T_k$ be the Rayleigh-shift
iterates `Matrix.rayleighShiftQrIterate A k`, and suppose that every shifted matrix
$T_k - (T_k)_{nn} I$ is invertible. Then every $T_k$ is upper Hessenberg. -/
theorem isUpperHessenberg_rayleighShiftQrIterate {A : Matrix (Fin (N + 1)) (Fin (N + 1)) 𝕜}
    (hA : A.IsUpperHessenberg)
    (hreg : ∀ k, IsUnit (rayleighShiftQrIterate A k -
      rayleighShiftQrIterate A k (Fin.last N) (Fin.last N) • 1)) (k : ℕ) :
    (rayleighShiftQrIterate A k).IsUpperHessenberg := by
  induction k with
  | zero => exact hA
  | succ k ih =>
    rw [rayleighShiftQrIterate_succ]
    exact isUpperHessenberg_shiftedQrStep ih (hreg k)

end RayleighShift

/-! ### Local quadratic convergence of the single-shift step, for any factorization -/

section Quadratic

variable {N : ℕ}

/-- **Local quadratic convergence of the single-shift QR step at a simple eigenvalue, for any QR
factorization.** Let $A \in \mathbb{R}^{n \times n}$, $n = N + 2$, and let $l$ be a simple root
of the characteristic polynomial of $A$. Then there are $C$ and $\delta > 0$ with the following
property. Let $Q$ be orthogonal, and let $T = Q^T A Q$ be upper Hessenberg with $T - t_{nn} I$
nonsingular, $|t_{n,n-1}| \le \delta$ and $|t_{nn} - l| \le \delta$. Then every QR step $T'$
from $T$ with shift $t_{nn}$, for any QR factorization, satisfies
$$|t'_{n,n-1}| \le C t_{n,n-1}^2, \qquad |t'_{nn} - l| \le C t_{n,n-1}^2.$$
This is [golub2013matrix] §7.5.3 and [quarteroni2000numerical] (5.53).

The canonical step is bounded by `Matrix.abs_shiftedQrStep_last_le_of_conj` with the data of
`Matrix.exists_eigenvector_data_of_rootMultiplicity_eq_one`. Any other step is a unimodular
diagonal similarity of it (`Matrix.IsShiftedQrStep.unique_of_isUnit`), which keeps the moduli of
the entries and the diagonal. A step for any factorization is `Matrix.IsShiftedQrStep`; the
index $n$ is `Fin.last (N + 1)` and $n - 1$ is `Fin.castSucc (Fin.last N)`. -/
theorem exists_abs_isShiftedQrStep_last_le_sq {A : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ} {l : ℝ}
    (hl : A.charpoly.rootMultiplicity l = 1) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ Q T T' : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ,
      Q ∈ orthogonalGroup (Fin (N + 2)) ℝ → T = Qᵀ * A * Q → T.IsUpperHessenberg →
      IsUnit (T - T (Fin.last (N + 1)) (Fin.last (N + 1)) • 1) →
      |T (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ≤ δ →
      |T (Fin.last (N + 1)) (Fin.last (N + 1)) - l| ≤ δ →
      IsShiftedQrStep (T (Fin.last (N + 1)) (Fin.last (N + 1))) T T' →
      |T' (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ≤
          C * |T (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ^ 2 ∧
        |T' (Fin.last (N + 1)) (Fin.last (N + 1)) - l| ≤
          C * |T (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ^ 2 := by
  obtain ⟨x, y, K, hx, hy, hyx, hK, hKw⟩ := exists_eigenvector_data_of_rootMultiplicity_eq_one hl
  set C₀ : ℝ := ‖LinearMap.toContinuousLinearMap (toEuclideanLin Aᵀ)‖ + |l| with hC₀def
  have hC₀ : 0 ≤ C₀ := by positivity
  have hCz : ∀ z : EuclideanSpace ℝ (Fin (N + 2)), ‖toEuclideanLin Aᵀ z - l • z‖ ≤ C₀ * ‖z‖ :=
    fun z => by
      calc ‖toEuclideanLin Aᵀ z - l • z‖ ≤ ‖toEuclideanLin Aᵀ z‖ + ‖l • z‖ := norm_sub_le _ _
        _ ≤ ‖LinearMap.toContinuousLinearMap (toEuclideanLin Aᵀ)‖ * ‖z‖ + |l| * ‖z‖ := by
          gcongr
          · exact (LinearMap.toContinuousLinearMap (toEuclideanLin Aᵀ)).le_opNorm z
          · rw [norm_smul, Real.norm_eq_abs]
        _ = C₀ * ‖z‖ := by ring
  set A' : ℝ := 2 * K * (1 + ‖x‖ * ‖y‖) with hA'def
  have hA'0 : 0 < A' := by positivity
  set D : ℝ := 4 * A' + 2 * K * C₀ * A' + 2 * K with hDdef
  have hD : 0 < D := by positivity
  refine ⟨4 * K * C₀ ^ 2 * A' ^ 2, 1 / D, by positivity,
    fun Q T T' hQ hTQ hT hunit ht hd hstep => ?_⟩
  set t := |T (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| with htdef
  have hsub1 : 4 * A' * t ≤ 1 := by
    calc 4 * A' * t ≤ 4 * A' * (1 / D) := by gcongr
      _ ≤ 1 := by
        rw [mul_one_div, div_le_one hD]
        nlinarith [mul_nonneg (mul_nonneg hK.le hC₀) hA'0.le]
  have hsub2 : 2 * K * C₀ * A' * t ≤ 1 := by
    calc 2 * K * C₀ * A' * t ≤ 2 * K * C₀ * A' * (1 / D) := by
          gcongr
      _ ≤ 1 := by
        rw [mul_one_div, div_le_one hD]
        nlinarith [hA'0, hK]
  have hdiag : 2 * K * |T (Fin.last (N + 1)) (Fin.last (N + 1)) - l| ≤ 1 := by
    calc 2 * K * |T (Fin.last (N + 1)) (Fin.last (N + 1)) - l| ≤ 2 * K * (1 / D) := by gcongr
      _ ≤ 1 := by
        rw [mul_one_div, div_le_one hD]
        nlinarith [mul_nonneg (mul_nonneg hK.le hC₀) hA'0.le, hA'0]
  obtain ⟨h₁, h₂⟩ := abs_shiftedQrStep_last_le_of_conj hQ hTQ hT hx hy hyx hK.le hKw hCz hunit
    hsub1 hsub2 hdiag
  obtain ⟨d, hd, hT'⟩ := (isShiftedQrStep_shiftedQrStep _ T).unique_of_isUnit hstep
    ((isUnit_iff_isUnit_det _).1 hunit)
  have hne : Fin.castSucc (Fin.last N) ≠ Fin.last (N + 1) := Fin.castSucc_lt_last _ |>.ne
  refine ⟨?_, ?_⟩
  · rw [hT', ← Real.norm_eq_abs, norm_diagonal_conj_apply hd, Real.norm_eq_abs]
    exact h₁ _ hne
  · rw [hT', diagonal_conj_apply_self hd]
    exact h₂

end Quadratic

end Matrix

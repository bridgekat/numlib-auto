/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.Convergence.Polynomial
import Numlib.Krylov.Convergence.CGIterationLimit
import Numlib.Krylov.OrthogonalPolynomials
import Numlib.Krylov.Quadrature
import Mathlib.Topology.Order.IntermediateValue

/-!
# Spectral identities for conjugate gradients

The characteristic polynomial of the Lanczos compression, normalized at zero, is the
conjugate-gradient residual polynomial. Orthogonal eigenvector coordinates give spectral
formulas for the Euclidean and energy norms of the error.
-/

open Polynomial Krylov Finset

namespace Lanczos

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The characteristic polynomial of the Lanczos tridiagonal after $n$ steps, divided by its
value at $0$. The result is the zero polynomial when the denominator is zero. -/
noncomputable def normalizedCharpoly (A : E →ₗ[𝕜] E) (r : E) (n : ℕ) : ℝ[X] :=
  let p := (tridiag A r n).charpoly
  C (p.eval 0)⁻¹ * p

variable {A : E →ₗ[𝕜] E} {b x₀ : E}

private theorem charpoly_eval_zero_ne (hA : A.IsSymmetricCoercive)
    [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))] {n : ℕ}
    (hn : n ≤ grade A (b - A x₀)) :
    (tridiag A (b - A x₀) n).charpoly.eval 0 ≠ 0 := by
  have hu := isUnit_tridiag (b := b) (x₀ := x₀) hA hn
  have hnd := isUnit_iff_ne_zero.1 ((Matrix.isUnit_iff_isUnit_det _).1 hu)
  simp [Matrix.eval_charpoly, Matrix.det_neg, hnd]

/-- With symmetric coercive $A$, before or at the grade of $r_0=b-Ax_0$, the normalized
Lanczos characteristic polynomial is the product $\prod_j(1-t/\theta_j)$ at each $t$,
where the $\theta_j$ are the eigenvalues of the Lanczos tridiagonal. -/
theorem eval_normalizedCharpoly_eq_prod (hA : A.IsSymmetricCoercive)
    [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))] {n : ℕ}
    (hn : n ≤ grade A (b - A x₀)) (t : ℝ) :
    (normalizedCharpoly A (b - A x₀) n).eval t =
      ∏ j : Fin n, (1 - t / (tridiag_isHermitian A (b - A x₀) n).eigenvalues j) := by
  let T := tridiag A (b - A x₀) n
  let hT := tridiag_isHermitian A (b - A x₀) n
  let θ := hT.eigenvalues
  have hpoly := hT.charpoly_eq
  have heval (x : ℝ) : T.charpoly.eval x = ∏ j, (x - θ j) := by
    rw [hpoly, eval_prod]
    refine prod_congr rfl fun j _ => ?_
    rw [eval_sub, eval_X, eval_C]
    rfl
  have hnz : T.charpoly.eval 0 ≠ 0 := charpoly_eval_zero_ne hA hn
  have hθ (j : Fin n) : θ j ≠ 0 := by
    intro hj
    apply hnz
    rw [heval]
    exact prod_eq_zero (mem_univ j) (by simp [hj])
  change (C (T.charpoly.eval 0)⁻¹ * T.charpoly).eval t = _
  rw [eval_mul, eval_C, heval 0, heval t, ← prod_inv_distrib, ← prod_mul_distrib]
  refine prod_congr rfl fun j _ => ?_
  change (0 - θ j)⁻¹ * (t - θ j) = 1 - t / θ j
  rw [zero_sub, inv_neg]
  field_simp [hθ j]
  ring

end Lanczos

namespace Krylov.IsGalerkinIterate

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {A : E →ₗ[𝕜] E} {b x₀ y : E} {n : ℕ}

/-- If $A$ is symmetric coercive, $y$ is a Galerkin iterate of step $n$, and $n$ is at most the
finite grade of $r_0=b-Ax_0$, then its residual equals $p_n(A)r_0$, where $p_n$ is the normalized
characteristic polynomial of the Lanczos tridiagonal at that step. -/
theorem residual_eq_aeval_normalized_charpoly (hA : A.IsSymmetricCoercive)
    [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]
    (hy : IsGalerkinIterate A b x₀ n y) (hn : n ≤ grade A (b - A x₀)) :
    b - A y = aeval A ((Lanczos.normalizedCharpoly A (b - A x₀) n).map
      (algebraMap ℝ 𝕜)) (b - A x₀) := by
  let r := b - A x₀
  let q := (Lanczos.tridiag A r n).charpoly
  let p := (Lanczos.normalizedCharpoly A r n).map (algebraMap ℝ 𝕜)
  have hq0 : q.eval 0 ≠ 0 := Lanczos.charpoly_eval_zero_ne hA hn
  have hp : p.degree ≤ n := by
    refine degree_map_le.trans (degree_le_natDegree.trans ?_)
    have hq : q.natDegree = n := by
      dsimp only [q]
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    exact_mod_cast (natDegree_C_mul_le (q.eval 0)⁻¹ q).trans hq.le
  have hp0 : p.eval 0 = 1 := by
    change ((C (q.eval 0)⁻¹ * q).map (algebraMap ℝ 𝕜)).eval 0 = 1
    rw [eval_zero_map, eval_mul, eval_C, inv_mul_cancel₀ hq0, map_one]
  obtain ⟨z, hz, hres⟩ := exists_mem_of_residual_poly (A := A) (b := b) (x₀ := x₀) p hp hp0
  have horth : b - A z ∈ (subspace A r n)ᗮ := by
    rw [hres]
    change aeval A ((C (q.eval 0)⁻¹ * q).map (algebraMap ℝ 𝕜)) r ∈ _
    rw [Polynomial.map_mul, Polynomial.map_C, map_mul, Module.End.mul_apply, aeval_C,
      Module.algebraMap_end_apply]
    apply Submodule.smul_mem
    change aeval A ((Lanczos.tridiag A r n).charpoly.map (algebraMap ℝ 𝕜)) r ∈ _
    rw [Lanczos.charpoly_tridiag_map hA.isSymmetric r hn]
    exact Arnoldi.aeval_charpoly_mem_orthogonal A r hn
  obtain ⟨u, _, hu⟩ := existsUnique_isGalerkinIterate_of_isCoercive hA.isCoercive b x₀ n
  rw [(hu y hy).trans (hu z ⟨hz, horth⟩).symm]
  exact hres

variable [FiniteDimensional 𝕜 E]

/-- For a symmetric coercive operator with eigenvalues $\mu_i$ and orthonormal eigenvectors
$u_i$, set $w_i=|\langle u_i,r_0\rangle|^2$ for $r_0=b-Ax_0$. At a Galerkin iterate $y$
of step $n$ up to the grade of $r_0$, write $q_i=\prod_j(1-\mu_i/\theta_j)$ using the
eigenvalues of the Lanczos tridiagonal. Then, for $Ax=b$, the squared residual norm, Euclidean
error norm and energy error norm are respectively $\sum_i q_i^2 w_i$,
$\sum_i (q_i/\mu_i)^2 w_i$, and $\sum_i \mu_i(q_i/\mu_i)^2 w_i$. -/
theorem squared_norms_eq_sum_eigenvalues (hA : A.IsSymmetricCoercive)
    {N : ℕ} (hN : Module.finrank 𝕜 E = N) {x : E} (hx : A x = b)
    (hy : IsGalerkinIterate A b x₀ n y) (hn : n ≤ grade A (b - A x₀)) :
    let r := b - A x₀
    let μ := hA.isSymmetric.eigenvalues hN
    let θ := (Lanczos.tridiag_isHermitian A r n).eigenvalues
    let q (i : Fin N) := ∏ j, (1 - μ i / θ j)
    let w (i : Fin N) := ‖(hA.isSymmetric.eigenvectorBasis hN).repr r i‖ ^ 2
    ‖b - A y‖ ^ 2 = ∑ i, q i ^ 2 * w i ∧
    ‖x - y‖ ^ 2 = ∑ i, (q i / μ i) ^ 2 * w i ∧
    energyNorm A (x - y) ^ 2 = ∑ i, μ i * (q i / μ i) ^ 2 * w i := by
  set r := b - A x₀
  set μ := hA.isSymmetric.eigenvalues hN
  set θ := (Lanczos.tridiag_isHermitian A r n).eigenvalues
  let q (i : Fin N) := ∏ j, (1 - μ i / θ j)
  let ψ := hA.isSymmetric.eigenvectorBasis hN
  let p := Lanczos.normalizedCharpoly A r n
  have hμ (i : Fin N) : 0 < μ i := by
    have hh := hA.re_pos_of_hasEigenvalue (hA.isSymmetric.hasEigenvalue_eigenvalues hN i)
    simpa only [RCLike.ofReal_re] using hh
  have hrepr (i : Fin N) : ψ.repr (b - A y) i = (q i : 𝕜) * ψ.repr r i := by
    have hr := hy.residual_eq_aeval_normalized_charpoly hA hn
    rw [hr, hA.isSymmetric.repr_aeval_apply hN]
    have he : (p.map (algebraMap ℝ 𝕜)).eval (μ i : 𝕜) = (q i : 𝕜) := by
      rw [← RCLike.algebraMap_eq_ofReal, eval_map, eval₂_at_apply]
      congr 1
      exact Lanczos.eval_normalizedCharpoly_eq_prod hA hn _
    rw [show hA.isSymmetric.eigenvalues hN i = μ i from rfl, he]
  have herr (i : Fin N) : ψ.repr (x - y) i = ((q i / μ i : ℝ) : 𝕜) * ψ.repr r i := by
    have hs := ψ.repr_apply_of_apply_eq_smul (hA.isSymmetric.apply_eigenvectorBasis hN) (x - y) i
    rw [map_sub, hx, hrepr i] at hs
    have hne : (μ i : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 (hμ i).ne'
    rw [RCLike.ofReal_div, div_mul_eq_mul_div, eq_div_iff hne, mul_comm]
    exact hs.symm
  change ‖b - A y‖ ^ 2 = ∑ i, q i ^ 2 * ‖ψ.repr r i‖ ^ 2 ∧
    ‖x - y‖ ^ 2 = ∑ i, (q i / μ i) ^ 2 * ‖ψ.repr r i‖ ^ 2 ∧
    energyNorm A (x - y) ^ 2 = ∑ i, μ i * (q i / μ i) ^ 2 * ‖ψ.repr r i‖ ^ 2
  refine ⟨?_, ?_, ?_⟩
  · rw [hA.isSymmetric.norm_sq_eq_sum_norm_repr_sq hN]
    refine sum_congr rfl fun i _ => ?_
    rw [hrepr i, norm_mul, mul_pow, RCLike.norm_ofReal, sq_abs]
  · rw [hA.isSymmetric.norm_sq_eq_sum_norm_repr_sq hN]
    refine sum_congr rfl fun i _ => ?_
    rw [herr i, norm_mul, mul_pow, RCLike.norm_ofReal, sq_abs]
  · rw [hA.energyNorm_sq, hA.isSymmetric.re_inner_apply_self_eq_sum hN]
    refine sum_congr rfl fun i _ => ?_
    rw [herr i, norm_mul, mul_pow, RCLike.norm_ofReal, sq_abs]
    ring

end Krylov.IsGalerkinIterate

namespace CG

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E} {b x x₀ : E}

/-- Let $A$ be symmetric coercive of positive dimension with eigenvalues $\mu_i$, and $Ax=b$.
The relative CG energy error at step $n$ does not exceed
$\inf_{\deg p\le n,\,p(0)=1}\max_i|p(\mu_i)|$. If the initial error vanishes, its relative
error in Lean is zero. -/
theorem energyNorm_error_le_spectralMinimax {N : ℕ} [NeZero N]
    (hN : Module.finrank 𝕜 E = N) (hA : A.IsSymmetricCoercive) (hx : A x = b) (n : ℕ) :
    energyNorm A (x - (iterate A b x₀ n).x) / energyNorm A (x - x₀) ≤
      ⨅ p : {p : 𝕜[X] // p.degree ≤ n ∧ p.eval 0 = 1},
        ⨆ i, ‖p.1.eval (hA.isSymmetric.eigenvalues hN i : 𝕜)‖ := by
  have : Nonempty {p : 𝕜[X] // p.degree ≤ (n : WithBot ℕ) ∧ p.eval 0 = 1} :=
    ⟨⟨1, by simp, by simp⟩⟩
  refine le_ciInf fun p => ?_
  let M := ⨆ i, ‖p.1.eval (hA.isSymmetric.eigenvalues hN i : 𝕜)‖
  have hval : ∀ i, ‖p.1.eval (hA.isSymmetric.eigenvalues hN i : 𝕜)‖ ≤ M :=
    fun i => le_ciSup (f := fun j => ‖p.1.eval (hA.isSymmetric.eigenvalues hN j : 𝕜)‖)
      (Finite.bddAbove_range _) i
  change _ ≤ M
  rcases eq_or_ne (energyNorm A (x - x₀)) 0 with hz | hz
  · rw [hz, div_zero]
    exact (norm_nonneg _).trans (hval 0)
  rw [div_le_iff₀ (lt_of_le_of_ne (energyNorm_nonneg _ _) hz.symm)]
  refine (IsGalerkinIterate.energyNorm_error_le_energyNorm_aeval hA
    (isGalerkinIterate b x₀ hA n) hx p.1 p.2.1 p.2.2).trans
    (hA.isSymmetric.energyNorm_aeval_apply_le hA p.1 ?_ _)
  intro u hu
  obtain ⟨i, hi⟩ := hA.isSymmetric.exists_eigenvalues_eq hN hu
  rw [← hi]
  exact hval i


/-- For $Ax=b$ and symmetric $A$ in finite dimension with spectrum in $[a,c]\subset(0,\infty)$,
the squared energy error after $n$ steps of CG, up to the grade, is
$$\xi^{-(2n+1)}\sum_i |\langle u_i,r_0\rangle|^2
  \prod_j(\mu_i-\theta_j)^2$$
for some $\xi\in[a,c]$, where $(\mu_i,u_i)$ are the eigenpairs of $A$ and $\theta_j$ are the
eigenvalues of the $n$-th Lanczos tridiagonal. -/
theorem exists_energyNorm_error_eq_monicRitzProduct {a c : ℝ}
    (ha : 0 < a) (hac : a ≤ c) (hA : A.IsSymmetricBoundedBy a c)
    {N : ℕ} (hN : Module.finrank 𝕜 E = N) (hx : A x = b)
    {n : ℕ} (hn : n ≤ grade A (b - A x₀)) :
    let r := b - A x₀
    let μ := (hA.isSymmetricCoercive ha).isSymmetric.eigenvalues hN
    let θ := (Lanczos.tridiag_isHermitian A r n).eigenvalues
    let w (i : Fin N) := ‖((hA.isSymmetricCoercive ha).isSymmetric.eigenvectorBasis hN).repr r i‖ ^ 2
    ∃ ξ ∈ Set.Icc a c,
      energyNorm A (x - (iterate A b x₀ n).x) ^ 2 =
        (∑ i, (∏ j, (μ i - θ j) ^ 2) * w i) / ξ ^ (2 * n + 1) := by
  let r := b - A x₀
  let hP := hA.isSymmetricCoercive ha
  let μ := hP.isSymmetric.eigenvalues hN
  let T := Lanczos.tridiag A r n
  let hT := Lanczos.tridiag_isHermitian A r n
  let θ := hT.eigenvalues
  let w (i : Fin N) := ‖(hP.isSymmetric.eigenvectorBasis hN).repr r i‖ ^ 2
  let q (i : Fin N) := ∏ j, (1 - μ i / θ j)
  let u (i : Fin N) := (∏ j, (μ i - θ j) ^ 2) * w i
  let total := ∑ i, u i
  let P := ∏ j, θ j
  let d (i : Fin N) := μ i * P ^ 2
  let en := energyNorm A (x - (iterate A b x₀ n).x) ^ 2
  have hμ (i : Fin N) : μ i ∈ Set.Icc a c := by
    simpa only [RCLike.ofReal_re] using
      ((hP.isSymmetric.isSymmetricBoundedBy_iff_forall_hasEigenvalue a c).1 hA _
        (hP.isSymmetric.hasEigenvalue_eigenvalues hN i))
  have hθ (j : Fin n) : θ j ∈ Set.Icc a c := by
    have hm : θ j ∈ spectrum ℝ T := by
      rw [Matrix.mem_spectrum_iff_isRoot_charpoly, hT.charpoly_eq, IsRoot.def, eval_prod]
      exact prod_eq_zero (mem_univ j) (by simp [θ])
    have he := (Lanczos.hasEigenvalue_compression_iff_mem_spectrum_tridiag hP.isSymmetric r hn
      (θ j)).2 hm
    have hC := compression.isSymmetricBoundedBy A (subspace A r n) hA
    simpa only [RCLike.ofReal_re] using
      ((hC.isSymmetric.isSymmetricBoundedBy_iff_forall_hasEigenvalue a c).1 hC _ he)
  have hP0 : 0 < P := prod_pos fun j _ => ha.trans_le (hθ j).1
  have hP_a : a ^ n ≤ P := by
    simpa [P] using prod_le_prod₀ (s := (univ : Finset (Fin n)))
      (f := fun _ => a) (g := θ) (fun _ _ => ha.le) (fun j _ => (hθ j).1)
  have hP_c : P ≤ c ^ n := by
    simpa [P] using prod_le_prod₀ (s := (univ : Finset (Fin n)))
      (f := θ) (g := fun _ => c) (fun j _ => ha.le.trans (hθ j).1) (fun j _ => (hθ j).2)
  have hpow (t : ℝ) : t ^ (2 * n + 1) = t * (t ^ n) ^ 2 := by
    rw [pow_succ', ← pow_mul, Nat.mul_comm n 2]
  have hdlo (i : Fin N) : a ^ (2 * n + 1) ≤ d i := by
    rw [hpow]
    dsimp only [d]
    exact mul_le_mul (hμ i).1 (pow_le_pow_left₀ (pow_nonneg ha.le n) hP_a 2)
      (sq_nonneg _) (ha.le.trans (hμ i).1)
  have hdhi (i : Fin N) : d i ≤ c ^ (2 * n + 1) := by
    rw [hpow]
    dsimp only [d]
    exact mul_le_mul (hμ i).2 (pow_le_pow_left₀ hP0.le hP_c 2)
      (sq_nonneg _) (ha.le.trans hac)
  have hd0 (i : Fin N) : 0 < d i := mul_pos (ha.trans_le (hμ i).1) (pow_pos hP0 2)
  have hq (i : Fin N) : q i ^ 2 = (∏ j, (μ i - θ j) ^ 2) / P ^ 2 := by
    change (∏ j, (1 - μ i / θ j)) ^ 2 = _
    rw [← prod_pow]
    have he (j : Fin n) : (1 - μ i / θ j) ^ 2 = (μ i - θ j) ^ 2 / θ j ^ 2 := by
      field_simp [(ha.trans_le (hθ j).1).ne']
      ring
    dsimp only [P]
    simp_rw [he]
    rw [prod_div_distrib]
    simp_rw [prod_pow]
  have hen : en = ∑ i, u i / d i := by
    have he := ((isGalerkinIterate b x₀ hP n).squared_norms_eq_sum_eigenvalues hP hN hx hn).2.2
    change en = ∑ i, μ i * (q i / μ i) ^ 2 * w i at he
    rw [he]
    refine sum_congr rfl fun i _ => ?_
    dsimp only [u, d]
    rw [div_pow, hq]
    field_simp [hP0.ne', (ha.trans_le (hμ i).1).ne']
  let f (t : ℝ) := total / t ^ (2 * n + 1)
  have hf : ContinuousOn f (Set.Icc a c) :=
    continuousOn_const.div (continuous_id.pow _).continuousOn fun t ht =>
      pow_ne_zero _ (ha.trans_le ht.1).ne'
  have hflo : f c ≤ en := by
    rw [hen]
    change (∑ i, u i) / c ^ (2 * n + 1) ≤ _
    rw [sum_div]
    exact sum_le_sum fun i _ =>
      div_le_div_of_nonneg_left (by
        dsimp [u, w]
        positivity) (hd0 i) (hdhi i)
  have hfhi : en ≤ f a := by
    rw [hen]
    change _ ≤ (∑ i, u i) / a ^ (2 * n + 1)
    rw [sum_div]
    exact sum_le_sum fun i _ =>
      div_le_div_of_nonneg_left (by
        dsimp [u, w]
        positivity) (pow_pos ha _) (hdlo i)
  obtain ⟨ξ, hξ, he⟩ := intermediate_value_Icc' hac hf ⟨hflo, hfhi⟩
  exact ⟨ξ, hξ, he.symm⟩


private theorem energyNorm_le_of_repr_norm_le {N : ℕ} (hN : Module.finrank 𝕜 E = N)
    (hA : A.IsSymmetricCoercive) {v w : E}
    (h : ∀ i, ‖(hA.isSymmetric.eigenvectorBasis hN).repr v i‖ ≤
      ‖(hA.isSymmetric.eigenvectorBasis hN).repr w i‖) :
    energyNorm A v ≤ energyNorm A w := by
  unfold energyNorm
  apply Real.sqrt_le_sqrt
  rw [hA.isSymmetric.re_inner_apply_self_eq_sum hN,
    hA.isSymmetric.re_inner_apply_self_eq_sum hN]
  refine sum_le_sum fun i _ => ?_
  have hμ : 0 ≤ hA.isSymmetric.eigenvalues hN i := by
    have hh := hA.re_pos_of_hasEigenvalue (hA.isSymmetric.hasEigenvalue_eigenvalues hN i)
    exact (by simpa only [RCLike.ofReal_re] using hh.le)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (h i) _) hμ

/-- Let $A$ be symmetric coercive with orthonormal eigenvectors $u_i$, and let $Ax=b$.
Fix two starting points $x_0$ and $\tilde x_0$ so that the latter's initial error agrees
with the former's outside a set $D$ of indices of largest eigenvalues and has zero
coordinates in $D$. The CG energy error from $\tilde x_0$ at step $n$ is bounded by that
from $x_0$ at the same step. The CG energy error from $x_0$ at step $n+|D|$ is bounded by the
error from $\tilde x_0$ at step $n$. -/
theorem energyNorm_error_le_truncated {N : ℕ} (hN : Module.finrank 𝕜 E = N)
    (hA : A.IsSymmetricCoercive) (hx : A x = b) {y₀ : E} (D : Finset (Fin N))
    (hD : ∀ i ∉ D, ∀ j ∈ D, hA.isSymmetric.eigenvalues hN i ≤ hA.isSymmetric.eigenvalues hN j)
    (hy₀ : ∀ i, (hA.isSymmetric.eigenvectorBasis hN).repr (x - y₀) i =
      if i ∈ D then 0 else (hA.isSymmetric.eigenvectorBasis hN).repr (x - x₀) i)
    (n : ℕ) :
    energyNorm A (x - (iterate A b y₀ n).x) ≤ energyNorm A (x - (iterate A b x₀ n).x) ∧
    energyNorm A (x - (iterate A b x₀ (n + D.card)).x) ≤
      energyNorm A (x - (iterate A b y₀ n).x) := by
  let μ := hA.isSymmetric.eigenvalues hN
  let B := hA.isSymmetric.eigenvectorBasis hN
  have hrepr (p : 𝕜[X]) (v : E) (i : Fin N) :
      B.repr (aeval A p v) i = p.eval (μ i : 𝕜) * B.repr v i :=
    hA.isSymmetric.repr_aeval_apply hN p v i
  have hxg := isGalerkinIterate b x₀ hA n
  have hyg := isGalerkinIterate b y₀ hA n
  refine ⟨?_, ?_⟩
  · obtain ⟨p, hdeg, hp0, hp⟩ := exists_residual_poly hxg.mem
    have he := error_eq_aeval_of_injective hA.isCoercive.injective hx hp
    rw [he]
    refine (hyg.energyNorm_error_le_energyNorm_aeval hA hx p hdeg hp0).trans
      (energyNorm_le_of_repr_norm_le hN hA fun i => ?_)
    rw [hrepr, hrepr, hy₀ i]
    by_cases hi : i ∈ D
    · rw [ite_eq_left hi, mul_zero, norm_zero]
      exact norm_nonneg _
    · rw [ite_eq_right hi]
  · obtain ⟨p, hdeg, hp0, hp⟩ := exists_residual_poly hyg.mem
    have he := error_eq_aeval_of_injective hA.isCoercive.injective hx hp
    have hpos (i : Fin N) : 0 < μ i := by
      simpa only [RCLike.ofReal_re] using
        hA.re_pos_of_hasEigenvalue (hA.isSymmetric.hasEigenvalue_eigenvalues hN i)
    obtain ⟨q, hq, hq0, hqD, hqL⟩ := exists_deflationPolynomial μ D hpos hD
    let qK := q.map (algebraMap ℝ 𝕜)
    have hqK : qK.natDegree ≤ D.card := natDegree_map_le.trans hq
    have hpq : (p * qK).degree ≤ (n + D.card : ℕ) :=
      degree_le_of_natDegree_le (natDegree_mul_le.trans
        (add_le_add (natDegree_le_of_degree_le hdeg) hqK))
    have hpq0 : (p * qK).eval 0 = 1 := by
      dsimp only [qK]
      rw [eval_mul, eval_zero_map, hq0, hp0, map_one, mul_one]
    have hv (i : Fin N) : qK.eval (μ i : 𝕜) = ((q.eval (μ i) : ℝ) : 𝕜) := by
      dsimp only [qK]
      rw [← RCLike.algebraMap_eq_ofReal, eval_map, eval₂_at_apply]
    rw [he]
    refine ((isGalerkinIterate b x₀ hA _).energyNorm_error_le_energyNorm_aeval
      hA hx (p * qK) hpq hpq0).trans (energyNorm_le_of_repr_norm_le hN hA fun i => ?_)
    rw [hrepr, hrepr, eval_mul, hv, hy₀ i]
    by_cases hi : i ∈ D
    · rw [hqD i hi, RCLike.ofReal_zero, mul_zero, zero_mul, norm_zero]
      exact norm_nonneg _
    · rw [ite_eq_right hi, mul_right_comm, norm_mul, RCLike.norm_ofReal]
      exact mul_le_of_le_one_right (norm_nonneg _) (hqL i hi)

end CG

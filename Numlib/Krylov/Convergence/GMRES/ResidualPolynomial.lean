/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.OrthogonalPolynomials
import Numlib.Eigen.RayleighRitz

/-!
# GMRES residual polynomials and the inverse compression

Let $A$ be invertible, $r$ the initial residual, and $W=A\mathcal K_n(A,r)$ the GMRES test
space. The characteristic polynomial of the compression of $A^{-1}$ to $W$, with its
coefficients reversed, is the normalized GMRES residual polynomial. Its roots are the
reciprocals of the nonzero Ritz values of $A^{-1}$ on $W$.
-/

open Finset Polynomial

namespace Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "ℒ(" A ")" => (LinearEquiv.toLinearMap A)

private theorem inverse_pow_apply_pow (A : E ≃ₗ[𝕜] E) {i n : ℕ} (hi : i ≤ n) (r : E) :
    (ℒ(A.symm) ^ i) ((ℒ(A) ^ n) r) = (ℒ(A) ^ (n - i)) r := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', Module.End.mul_apply, ih (Nat.le_of_succ_le hi)]
    have h : n - i = (n - (i + 1)) + 1 := by omega
    rw [h, pow_succ', Module.End.mul_apply]
    exact A.symm_apply_apply _

private theorem reverse_aeval_apply (A : E ≃ₗ[𝕜] E) (p : 𝕜[X]) (r : E) :
    aeval (ℒ(A)) p.reverse r =
      aeval (ℒ(A.symm)) p ((ℒ(A) ^ p.natDegree) r) := by
  let n := p.natDegree
  rw [aeval_eq_sum_range' (Nat.lt_succ_of_le p.reverse_natDegree_le), aeval_eq_sum_range]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  rw [← sum_range_reflect (fun i => p.coeff i • (ℒ(A.symm) ^ i) ((ℒ(A) ^ n) r)) (n + 1)]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := Nat.le_of_lt_succ (mem_range.mp hi)
  rw [coeff_reverse, revAt_le hi', show n + 1 - 1 - i = n - i by omega,
    inverse_pow_apply_pow A (Nat.sub_le _ _) r, Nat.sub_sub_self hi']

variable [FiniteDimensional 𝕜 E]

/-- The **GMRES residual polynomial from the inverse compression** is the reverse of the
characteristic polynomial of $P_W A^{-1}|_W$ for $W=A\mathcal K_n(A,r)$. Reversal gives value
$1$ at zero even when the inverse compression has a zero eigenvalue. -/
noncomputable def inverseCompressionResidualPoly (A : E ≃ₗ[𝕜] E) (r : E) (n : ℕ) : 𝕜[X] :=
  (LinearMap.charpoly (compression (ℒ(A.symm)) ((subspace (ℒ(A)) r n).map (ℒ(A))))).reverse

omit [FiniteDimensional 𝕜 E] in
/-- The GMRES polynomial from the inverse compression takes value $1$ at zero. -/
@[simp] theorem inverseCompressionResidualPoly_eval_zero (A : E ≃ₗ[𝕜] E) (r : E) (n : ℕ) :
    (inverseCompressionResidualPoly A r n).eval 0 = 1 := by
  rw [← coeff_zero_eq_eval_zero, inverseCompressionResidualPoly, coeff_zero_reverse]
  exact (LinearMap.charpoly_monic _).leadingCoeff

/-- The degree of the GMRES polynomial from the inverse compression is at most the step
number $n$, provided $n$ is at most the grade of the initial residual. -/
theorem inverseCompressionResidualPoly_degree_le (A : E ≃ₗ[𝕜] E) (r : E) {n : ℕ}
    (hn : n ≤ grade (ℒ(A)) r) :
    (inverseCompressionResidualPoly A r n).degree ≤ n := by
  have hdim : Module.finrank 𝕜 ((subspace (ℒ(A)) r n).map (ℒ(A))) = n := by
    rw [LinearEquiv.finrank_map_eq, finrank_subspace, min_eq_left hn]
  refine degree_le_of_natDegree_le ((reverse_natDegree_le _).trans ?_)
  rw [LinearMap.charpoly_natDegree, hdim]

private theorem inverseCompressionResidualPoly_orthogonal (A : E ≃ₗ[𝕜] E) (r : E) {n : ℕ}
    (hn : n ≤ grade (ℒ(A)) r) :
    aeval (ℒ(A)) (inverseCompressionResidualPoly A r n) r ∈
      ((subspace (ℒ(A)) r n).map (ℒ(A)))ᗮ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp
  let W := (subspace (ℒ(A)) r n).map (ℒ(A))
  let D := compression (ℒ(A.symm)) W
  let p := LinearMap.charpoly D
  have hdeg : p.natDegree = n := by
    dsimp only [p]
    rw [LinearMap.charpoly_natDegree, show Module.finrank 𝕜 W = n by
      dsimp only [W]
      rw [LinearEquiv.finrank_map_eq, finrank_subspace, min_eq_left hn]]
  have hmem : ∀ j < n, (ℒ(A) ^ (n - j)) r ∈ W := by
    intro j hj
    have h : n - j = (n - (j + 1)) + 1 := by omega
    rw [h, pow_succ', Module.End.mul_apply]
    exact Submodule.mem_map_of_mem (pow_apply_mem_subspace (ℒ(A)) r (by omega))
  have hv : (ℒ(A) ^ n) r ∈ W := by simpa using hmem 0 hn0
  let w : W := ⟨_, hv⟩
  have h := compressionBy.apply_aeval_of_forall_pow_lt_mem
    (W.orthogonalProjectionOnto : E →ₗ[𝕜] W) W.orthogonalProjectionOnto_mem_subspace_eq_self
    (ℒ(A.symm)) p (x := w) (fun i hi => by
      change (ℒ(A.symm) ^ i) ((ℒ(A) ^ n) r) ∈ W
      rw [inverse_pow_apply_pow A (le_of_lt (hdeg ▸ hi))]
      exact hmem i (hdeg ▸ hi))
  rw [← compression.eq_compressionBy, LinearMap.aeval_self_charpoly, LinearMap.zero_apply] at h
  rw [← Submodule.orthogonalProjectionOnto_eq_zero_iff]
  change W.orthogonalProjectionOnto (aeval (ℒ(A)) p.reverse r) = 0
  rw [reverse_aeval_apply, hdeg]
  exact h

/-- Let $A$ be invertible and let $n$ be at most the grade of $b-Ax_0$. If $x_n$ is the $n$-th
GMRES iterate, its residual is the reverse characteristic polynomial of the compression of
$A^{-1}$ to $A\mathcal K_n(A,b-Ax_0)$, evaluated at $A$ and applied to $b-Ax_0$. -/
theorem IsMinResidualIterate.residual_eq_aeval_inverseCompressionResidualPoly
    {A : E ≃ₗ[𝕜] E} {b x₀ x : E} {n : ℕ} (hx : IsMinResidualIterate (ℒ(A)) b x₀ n x)
    (hn : n ≤ grade (ℒ(A)) (b - A x₀)) :
    b - A x = aeval (ℒ(A)) (inverseCompressionResidualPoly A (b - A x₀) n) (b - A x₀) := by
  let r := b - A x₀
  let p := inverseCompressionResidualPoly A r n
  obtain ⟨z, hz, hzres⟩ := exists_mem_of_residual_poly (A := ℒ(A)) (b := b) (x₀ := x₀) p
    (inverseCompressionResidualPoly_degree_le A r hn)
    (inverseCompressionResidualPoly_eval_zero A r n)
  have hzmin : IsMinResidualIterate (ℒ(A)) b x₀ n z := by
    apply IsMinResidual.iff_isPetrovGalerkin.2
    exact ⟨hz, hzres ▸ inverseCompressionResidualPoly_orthogonal A r hn⟩
  obtain ⟨y, _, hu⟩ := existsUnique_isMinResidualIterate_of_injective (A := ℒ(A)) A.injective b x₀ n
  rw [(hu x hx).trans (hu z hzmin).symm]
  exact hzres

/-- Up to the grade of the initial residual, the polynomial of degree at most $n$ and value $1$
at zero that produces the GMRES residual is uniquely the reverse characteristic polynomial of
the compression of the inverse to the test space. -/
theorem IsMinResidualIterate.residualPoly_eq_inverseCompressionResidualPoly
    {A : E ≃ₗ[𝕜] E} {b x₀ x : E} {n : ℕ} (hx : IsMinResidualIterate (ℒ(A)) b x₀ n x)
    (hn : n ≤ grade (ℒ(A)) (b - A x₀)) (p : 𝕜[X]) (hdeg : p.degree ≤ n) (hp0 : p.eval 0 = 1)
    (hp : b - A x = aeval (ℒ(A)) p (b - A x₀)) :
    p = inverseCompressionResidualPoly A (b - A x₀) n := by
  let r := b - A x₀
  let q := inverseCompressionResidualPoly A r n
  have hq0 : q.eval 0 = 1 := inverseCompressionResidualPoly_eval_zero A r n
  have hqdeg : q.degree ≤ n := inverseCompressionResidualPoly_degree_le A r hn
  have hql := hx.residual_eq_aeval_inverseCompressionResidualPoly hn
  obtain ⟨g, hg⟩ : X ∣ p - q := by
    rw [X_dvd_iff, coeff_sub, coeff_zero_eq_eval_zero, coeff_zero_eq_eval_zero, hp0, hq0, sub_self]
  change b - A x = aeval (ℒ(A)) p r at hp
  change b - A x = aeval (ℒ(A)) q r at hql
  have hgp : aeval (ℒ(A)) g r = 0 := by
    apply A.injective
    have hzero : aeval (ℒ(A)) (p - q) r = 0 := by
      simp only [map_sub, LinearMap.sub_apply, ← hp, ← hql, sub_self]
    simpa only [hg, map_mul, aeval_X, Module.End.mul_apply, LinearEquiv.coe_coe,
      LinearEquiv.map_zero] using hzero
  have hg0 : g = 0 := by
    by_contra hgz
    have hgdeg : (X * g).degree ≤ (n : WithBot ℕ) := by
      rw [← hg]
      exact (degree_sub_le _ _).trans (max_le hdeg hqdeg)
    rw [degree_mul, degree_X, degree_eq_natDegree hgz] at hgdeg
    have hnat : 1 + g.natDegree ≤ n := by exact_mod_cast hgdeg
    have hlt : g.degree < grade (ℒ(A)) r := by
      rw [degree_eq_natDegree hgz, Nat.cast_lt]
      exact (by omega : g.natDegree < n).trans_le hn
    exact hgz ((aeval_eq_zero_iff_of_degree_lt_grade (ℒ(A)) r hlt).1 hgp)
  exact sub_eq_zero.mp (by simpa only [hg0, mul_zero] using hg)

omit [FiniteDimensional 𝕜 E] in
/-- A scalar is a root of the GMRES polynomial from the inverse compression exactly when it
is nonzero and its reciprocal is a Ritz value of $A^{-1}$ on the image Krylov subspace. -/
theorem isRoot_inverseCompressionResidualPoly_iff (A : E ≃ₗ[𝕜] E) (r : E) (n : ℕ) (μ : 𝕜) :
    (inverseCompressionResidualPoly A r n).IsRoot μ ↔
      μ ≠ 0 ∧ ∃ u : E, IsRitzPair (ℒ(A.symm)) ((subspace (ℒ(A)) r n).map (ℒ(A))) μ⁻¹ u := by
  by_cases hμ : μ = 0
  · subst μ
    simp [IsRoot.def]
  rw [and_iff_right hμ]
  let W := (subspace (ℒ(A)) r n).map (ℒ(A))
  let D := compression (ℒ(A.symm)) W
  have : Invertible μ⁻¹ := invertibleOfNonzero (inv_ne_zero hμ)
  have hr := eval₂_reverse_eq_zero_iff (RingHom.id 𝕜) μ⁻¹ (LinearMap.charpoly D)
  simp only [eval₂_id, invOf_eq_inv, inv_inv] at hr
  change D.charpoly.reverse.eval μ = 0 ↔ ∃ u : E, IsRitzPair (ℒ(A.symm)) W μ⁻¹ u
  rw [hr, ← IsRoot.def, ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
  constructor
  · intro h
    obtain ⟨u, hu⟩ := h.exists_hasEigenvector
    exact ⟨u, isRitzPair_of_hasEigenvector (ℒ(A.symm)) W _ hu⟩
  · rintro ⟨u, hu⟩
    exact hu.hasEigenvalue

end Krylov

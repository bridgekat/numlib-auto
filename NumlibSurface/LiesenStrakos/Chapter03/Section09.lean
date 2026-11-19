/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Ring.Units
import Numlib.Krylov.OrthogonalPolynomials

/-!
# Model reduction of large-scale dynamical systems

The transfer function of a finite-dimensional system is expressed through a matrix resolvent.
Expansion at infinity produces moments in nonnegative powers of the matrix. A partial
realization reproduces a specified initial segment of those moments. See §3.9 of
[liesen2013krylov].

## Main definitions

* `LiesenStrakos.Chapter03.transferFunction` evaluates the transfer function
  $d+c^*(\lambda E-A)^{-1}b$.
* `LiesenStrakos.Chapter03.IsPartialRealization` is moment matching through a given order.
* `LiesenStrakos.Chapter03.IsMinimalPartialRealization` is partial realization at the least
  possible state dimension.

## Main results

* `transferFunction_hasSum_at_infinity` and `remark_3_9_1` give the convergent expansions at
  infinity and at zero, respectively.
* `cg_scatteringAmplitude_eq` identifies the scattering amplitude at the CG initial residual
  with the squared initial energy error and gives its reduced approximation.

## Deviations from the source

* **Section 3.9** (generalization). The transfer formulas allow complex data and use total
  inverses, with explicit norm bounds for the expansion domains.
-/

open Matrix

namespace LiesenStrakos.Chapter03

/-- The transfer function of the descriptor system with state matrices $A,E$, input $b$, output
$c^*$ and direct feedthrough $d$ is $d+c^*(\lambda E-A)^{-1}b$ at every $\lambda$ for which the
pencil matrix is invertible. This is (3.9.2) of [liesen2013krylov].

**Generalization.** Complex system data are allowed. At a singular pencil argument the total
inverse assigns the feedthrough value $d$. -/
noncomputable def transferFunction {n : ℕ} (A E : Matrix (Fin n) (Fin n) ℂ)
    (b c : Fin n → ℂ) (d z : ℂ) : ℂ :=
  d + (star c) ⬝ᵥ ((z • E - A)⁻¹ *ᵥ b)

/-- The $k$th Markov parameter for the ordinary system $E=I$, $d=0$ is $c^*A^k b$. This is
(3.9.6) of [liesen2013krylov], indexed from zero.

**Generalization.** Complex system data are allowed and the index begins at zero. -/
noncomputable def markovParameter {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (b c : Fin n → ℂ) (k : ℕ) : ℂ :=
  (star c) ⬝ᵥ (A ^ k *ᵥ b)

/-- The $k$th coefficient of the expansion of $-c^*(\lambda I-A)^{-1}b$ at $\lambda=0$ is
$c^*(A^{-1})^{k+1}b$ for invertible $A$. This is (3.9.7) of [liesen2013krylov], indexed from
zero.

**Generalization.** Complex system data are allowed and the total inverse defines a value even
for singular $A$. -/
noncomputable def inverseMoment {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (b c : Fin n → ℂ) (k : ℕ) : ℂ :=
  (star c) ⬝ᵥ ((A⁻¹) ^ (k + 1) *ᵥ b)

/-- A triple $(\widehat A,\widehat b,\widehat c)$ is a partial realization of $(A,b,c)$ of length
$m$ if their Markov parameters agree at every index below $m$.

**Generalization.** The prefix length is arbitrary and the ordinary system data may be complex. -/
def IsPartialRealization {n r : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b c : Fin n → ℂ)
    (B : Matrix (Fin r) (Fin r) ℂ) (d e : Fin r → ℂ) (m : ℕ) : Prop :=
  ∀ k < m, markovParameter B d e k = markovParameter A b c k

/-- A partial realization of length $m$ and dimension $r$ is minimal if every realization of
length $m$ has dimension at least $r$.

**Generalization.** The minimum dimension criterion uses arbitrary prefix lengths and complex
system data. -/
def IsMinimalPartialRealization {n r : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b c : Fin n → ℂ)
    (B : Matrix (Fin r) (Fin r) ℂ) (d e : Fin r → ℂ) (m : ℕ) : Prop :=
  IsPartialRealization A b c B d e m ∧
    ∀ (s : ℕ) (C : Matrix (Fin s) (Fin s) ℂ) (f g : Fin s → ℂ),
      IsPartialRealization A b c C f g m → r ≤ s

section Expansion

open scoped Matrix.Norms.Operator

private noncomputable def inputOutput {n : ℕ} (b c : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => star c ⬝ᵥ (M *ᵥ b)
      map_add' := fun M N => by rw [Matrix.add_mulVec, dotProduct_add]
      map_smul' := fun z M => by rw [Matrix.smul_mulVec, dotProduct_smul, RingHom.id_apply] }

private theorem hasSum_geometric_matrix {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : ‖T‖ < 1) : HasSum (fun k : ℕ => T ^ k) ((1 - T)⁻¹) := by
  rw [Matrix.nonsing_inv_eq_ringInverse, NormedRing.inverse_one_sub T hT]
  exact (summable_geometric_of_norm_lt_one hT).hasSum

private theorem isUnit_det_one_sub {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) (hT : ‖T‖ < 1) :
    IsUnit (1 - T).det := by
  apply (Matrix.isUnit_iff_isUnit_det _).1
  rw [← Units.val_oneSub T hT]
  exact (Units.oneSub T hT).isUnit

/-- **Equation (3.9.4)** of [liesen2013krylov].
The ordinary transfer function has a convergent Laurent expansion in the Markov parameters
where the maximum absolute row-sum norm satisfies $\|z^{-1} A\| < 1$.

**Generalization.** The expansion uses complex system data and a sufficient region specified by
$\|z^{-1}A\|<1$. -/
theorem transferFunction_hasSum_at_infinity {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (b c : Fin n → ℂ) {z : ℂ} (hz : z ≠ 0) (h : ‖z⁻¹ • A‖ < 1) :
    HasSum (fun k => z⁻¹ ^ (k + 1) * markovParameter A b c k)
      (transferFunction A 1 b c 0 z) := by
  let T := z⁻¹ • A
  have hfactor : z • (1 - T) = z • 1 - A := by
    rw [smul_sub, show z • T = A by simp [T, smul_smul, hz]]
  have hinv : (z • 1 - A)⁻¹ = z⁻¹ • (1 - T)⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [← hfactor, smul_mul_smul_comm, inv_mul_cancel₀ hz, one_smul,
      Matrix.nonsing_inv_mul _ (isUnit_det_one_sub T h)]
  let L := inputOutput b c
  have hsum := (L.hasSum (hasSum_geometric_matrix T h)).mul_left z⁻¹
  rw [transferFunction, zero_add, hinv, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  convert hsum using 1 <;> try rfl
  funext k
  change _ = z⁻¹ * (star c ⬝ᵥ ((T ^ k) *ᵥ b))
  rw [show T ^ k = z⁻¹ ^ k • A ^ k by exact smul_pow _ _ _, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, markovParameter, pow_succ']
  exact mul_assoc _ _ _

/-- **Equation (3.9.8) and Remark 3.9.1** of [liesen2013krylov].
The expansion at zero for invertible $A$ uses inverse moments. The sum has the opposite sign
from the transfer function, because the resolvent is written as $(zI-A)^{-1}$.

**Generalization.** The expansion uses complex system data and a sufficient region specified by
$\|z A^{-1}\|<1$. -/
theorem remark_3_9_1 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b c : Fin n → ℂ)
    (hA : IsUnit A.det) {z : ℂ} (h : ‖z • A⁻¹‖ < 1) :
    HasSum (fun k => z ^ k * inverseMoment A b c k) (-transferFunction A 1 b c 0 z) := by
  let T := z • A⁻¹
  have hfactor : -(A * (1 - T)) = z • 1 - A := by
    rw [Matrix.mul_sub, mul_one, neg_sub, show A * T = z • 1 by
      change A * (z • A⁻¹) = z • 1
      rw [Matrix.mul_smul, Matrix.mul_nonsing_inv _ hA]]
  have hinv : (z • 1 - A)⁻¹ = -((1 - T)⁻¹ * A⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [← hfactor, neg_mul_neg, Matrix.mul_assoc, ← Matrix.mul_assoc A⁻¹,
      Matrix.nonsing_inv_mul _ hA, one_mul,
      Matrix.nonsing_inv_mul _ (isUnit_det_one_sub T h)]
  let L := inputOutput b c
  have hsum := L.hasSum ((hasSum_geometric_matrix T h).mul_right A⁻¹)
  rw [transferFunction, zero_add, hinv, Matrix.neg_mulVec, dotProduct_neg, neg_neg]
  convert hsum using 1 <;> try rfl
  funext k
  change _ = star c ⬝ᵥ ((T ^ k * A⁻¹) *ᵥ b)
  rw [show T ^ k = z ^ k • (A⁻¹) ^ k by exact smul_pow _ _ _, Matrix.smul_mul, ← pow_succ,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, inverseMoment]

end Expansion

open scoped InnerProductSpace

/-- **Equation (3.9.10)** of [liesen2013krylov].
At the CG initial residual $r_0$, the scattering amplitude $r_0^* A^{-1}r_0$ equals the
squared initial energy error. It is the sum of the reduced inverse moment multiplied
by $\|r_0\|^2$ and the squared CG energy error at step $n$.

**Generalization.** The identity also covers step zero and a zero initial residual. -/
theorem cg_scatteringAmplitude_eq {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E}
    (hA : A.IsSymmetricCoercive) (b x₀ xstar : E) (hstar : A xstar = b) {n : ℕ}
    (hn : n ≤ Krylov.grade A (b - A x₀)) :
    let Ainv := (LinearEquiv.ofBijective A ⟨hA.isCoercive.injective,
      LinearMap.surjective_of_injective hA.isCoercive.injective⟩).symm
    let r₀ := b - A x₀
    RCLike.re (inner 𝕜 r₀ (Ainv r₀)) = energyNorm A (xstar - x₀) ^ 2 ∧
    energyNorm A (xstar - x₀) ^ 2 = ‖r₀‖ ^ 2 * Lanczos.tridiagInvFirst A r₀ n +
      energyNorm A (xstar - (CG.iterate A b x₀ n).x) ^ 2 := by
  dsimp only
  constructor
  · have herr : A (xstar - x₀) = b - A x₀ := by rw [map_sub, hstar]
    rw [hA.energyNorm_sq, ← herr]
    let e := LinearEquiv.ofBijective A ⟨hA.isCoercive.injective,
      LinearMap.surjective_of_injective hA.isCoercive.injective⟩
    change RCLike.re (inner 𝕜 (A (xstar - x₀)) (e.symm (e (xstar - x₀)))) = _
    rw [e.symm_apply_apply]
  · have h₀ := CG.energyNorm_error_sq_eq_sub_inner_inv (x₀ := x₀) hA hstar (Nat.zero_le _)
    simp only [CG.iterate_zero, CG.init_x, Lanczos.tridiagInvFirst_zero, sub_zero] at h₀
    rw [h₀, CG.energyNorm_error_sq_eq_sub_inner_inv hA hstar hn, mul_sub]
    ring

end LiesenStrakos.Chapter03

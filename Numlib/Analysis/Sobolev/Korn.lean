/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.PDE.Elliptic.Dirichlet

/-!
# Korn's first inequality on $[H^1_0(\Omega)]^N$

Let $\Omega \subseteq \mathbb{R}^N$ be open. For a vector field $v = (v_1, \dots, v_N)$ with
components in $H^1_0(\Omega)$, the **linearized strain** is the symmetric matrix of $L^2(\Omega)$
functions $\varepsilon(v)_{ij} = \frac12 (\partial_j v_i + \partial_i v_j)$. **Korn's first
inequality** is the bound $\int_\Omega |\nabla v|^2 \le 2 \int_\Omega |\varepsilon(v)|^2$. Together
with Poincaré's inequality it makes $\int_\Omega |\varepsilon(v)|^2$ an equivalent squared norm on
$[H^1_0(\Omega)]^N$ for a bounded $\Omega$. This is the $V$-ellipticity behind the linearized
elasticity problem of [han2009theoretical], §8.5, in the pure displacement case
$\Gamma_D = \partial\Omega$; the source quotes Korn's inequality after Theorem 8.5.1. The bounded
case uses Poincaré's inequality in the form of Corollary 9.19 of [brezis2011functional].

## Main definitions

* `SobolevEuclideanZeroVec`: the Hilbert space $[H^1_0(\Omega)]^N$, the $\ell^2$ product of $N$
  copies of $H^1_0(\Omega)$.
* `SobolevEuclideanZeroVec.partialL`: the partial derivative $v \mapsto \partial_j v_i$, as a
  continuous linear map into $L^2(\Omega)$.
* `SobolevEuclideanZeroVec.strainL`: the strain $v \mapsto \varepsilon(v)_{ij}$, as a continuous
  linear map into $L^2(\Omega)$.

## Main results

* `SobolevEuclideanZero.inner_weakDeriv_single_comm`: for $u, v \in H^1_0(\Omega)$, $(\partial_j u,
  \partial_i v)_{L^2} = (\partial_i u, \partial_j v)_{L^2}$.
* `SobolevEuclideanZeroVec.sum_norm_strainL_sq_eq`: Korn's identity $\int_\Omega
  |\varepsilon(v)|^2 = \frac12 \int_\Omega |\nabla v|^2 + \frac12 \int_\Omega (\operatorname{div}
  v)^2$.
* `SobolevEuclideanZeroVec.korn_first`: Korn's first inequality $\frac12 \int_\Omega |\nabla v|^2
  \le \int_\Omega |\varepsilon(v)|^2$.
* `SobolevEuclideanZeroVec.norm_sq_le_sum_norm_strainL_sq`: for $\Omega \subseteq B(0, R) \subseteq
  \mathbb{R}^{d+1}$, $\|v\|^2 \le 2 (1 + (2R)^2) \int_\Omega |\varepsilon(v)|^2$.

## Proof outline

Korn's identity follows from the commutation
$$\int_\Omega \partial_j u \, \partial_i v = \int_\Omega \partial_i u \, \partial_j v, \qquad u, v
  \in H^1_0(\Omega).$$
For test functions $\varphi, \psi$ this is two integrations by parts, $\int \partial_j \varphi \,
\partial_i \psi = -\int \varphi \, \partial_j \partial_i \psi = -\int \varphi \, \partial_i
\partial_j \psi = \int \partial_i \varphi \, \partial_j \psi$. Both sides are continuous bilinear
forms on $H^1(\Omega)$, so the identity extends to $H^1_0(\Omega)$ by density.

## Implementation notes

* The commutation fails on $H^1(\Omega)$, because the boundary terms of the integrations by parts do
  not vanish. Korn's second inequality on $H^1(\Omega)$, with the $L^2$ norm on the right, needs the
  regularity of the boundary and a compactness argument; it is not formalized here.
* The number of components of a vector field is the dimension $N$ of the space. The results on a
  bounded domain are stated in dimension $N = d + 1$, the setting of the Poincaré inequality
  `SobolevEuclideanZero.norm_le_gradNorm`.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology InnerProductSpace

noncomputable section

/-! ### The commutation $\int \partial_j u \, \partial_i v = \int \partial_i u \, \partial_j v$ -/

section Comm

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **Two integrations by parts on test functions.** Let $\varphi, \psi \in C_0^\infty(\Omega)$ and
let $v, w \in \mathbb{R}^N$ be two directions. Then
$$\int_\Omega D\varphi(x)[v] \, D\psi(x)[w] \, dx = \int_\Omega D\varphi(x)[w] \, D\psi(x)[v] \,
  dx.$$

Both sides equal $-\int_\Omega \varphi \, D^2\psi[v, w]$, by the symmetry of the second
derivative of $\psi$. -/
theorem TestFunction.setIntegral_fderiv_mul_fderiv_comm (φ ψ : 𝓓(Ω, ℝ))
    (v w : EuclideanSpace ℝ (Fin N)) :
    ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), fderiv ℝ φ x v * fderiv ℝ ψ x w
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), fderiv ℝ φ x w * fderiv ℝ ψ x v := by
  have h1 := TestFunction.setIntegral_mul_fderiv_eq_neg
    ((ψ.fderivApply w).contDiff.of_le (by simp)) φ v
  have h2 := TestFunction.setIntegral_mul_fderiv_eq_neg
    ((ψ.fderivApply v).contDiff.of_le (by simp)) φ w
  simp only [TestFunction.fderivApply_coe] at h1 h2
  have hcomm := ψ.contDiff.fderiv_fderiv_comm w v
  have hL : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        φ x * fderiv ℝ (fun y ↦ fderiv ℝ ψ y w) x v
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        φ x * fderiv ℝ (fun y ↦ fderiv ℝ ψ y v) x w :=
    integral_congr_ae (Eventually.of_forall fun x ↦ by dsimp only; rw [congrFun hcomm x])
  have := (h1.symm.trans hL).trans h2
  exact neg_inj.1 this

namespace SobolevEuclideanZero

/-- Let $w, w' \in H^1(\Omega)$ be elements whose functions agree almost everywhere on $\Omega$ with
test functions $\varphi$ and $\psi$. Then for all $i, j$,
$$(\partial_j w, \partial_i w')_{L^2(\Omega)} = (\partial_i w, \partial_j w')_{L^2(\Omega)}.$$

The weak partial derivatives of $w$ and $w'$ are the classical ones
(`SobolevMultiIndexZero.weakDeriv_single_ae_eq_testFunction`), and
`TestFunction.setIntegral_fderiv_mul_fderiv_comm` applies. -/
theorem inner_weakDeriv_single_comm_of_testFunction {w w' : SobolevEuclidean N 1 2 Ω}
    {φ ψ : 𝓓(Ω, ℝ)}
    (hφ : SobolevMultiIndex.fn w =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] φ)
    (hψ : SobolevMultiIndex.fn w' =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ψ)
    (i j : Fin N) :
    ⟪SobolevMultiIndex.weakDeriv w (MultiIndexLE.single j),
        SobolevMultiIndex.weakDeriv w' (MultiIndexLE.single i)⟫_ℝ
      = ⟪SobolevMultiIndex.weakDeriv w (MultiIndexLE.single i),
        SobolevMultiIndex.weakDeriv w' (MultiIndexLE.single j)⟫_ℝ := by
  have e : ∀ (a b : Fin N), ⟪SobolevMultiIndex.weakDeriv w (MultiIndexLE.single a),
      SobolevMultiIndex.weakDeriv w' (MultiIndexLE.single b)⟫_ℝ
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        fderiv ℝ φ x (EuclideanSpace.single a 1) * fderiv ℝ ψ x (EuclideanSpace.single b 1) := by
    intro a b
    rw [L2.inner_eq_integral_mul]
    refine integral_congr_ae ?_
    filter_upwards [SobolevMultiIndexZero.weakDeriv_single_ae_eq_testFunction hφ a,
      SobolevMultiIndexZero.weakDeriv_single_ae_eq_testFunction hψ b] with x hx hx'
    rw [hx, hx', EuclideanSpace.basisFun_toBasis_apply, EuclideanSpace.basisFun_toBasis_apply]
  rw [e, e]
  exact TestFunction.setIntegral_fderiv_mul_fderiv_comm φ ψ _ _

/-- **The commutation of partial derivatives on $H^1_0(\Omega)$.** Let $u, v \in H^1_0(\Omega)$ and
$i, j \in \{1, \dots, N\}$. Then
$$(\partial_j u, \partial_i v)_{L^2(\Omega)} = (\partial_i u, \partial_j v)_{L^2(\Omega)},
  \quad\text{that is,}\quad \int_\Omega \partial_j u \, \partial_i v = \int_\Omega \partial_i u
  \, \partial_j v.$$

The identity holds for test functions by two integrations by parts
(`TestFunction.setIntegral_fderiv_mul_fderiv_comm`). Both sides are continuous bilinear forms on
$H^1(\Omega)$ (sums of `Elliptic.pairing` forms), so the identity extends to the closure
$H^1_0(\Omega)$ of the test functions. On $H^1(\Omega)$ the identity fails, because the boundary
terms do not vanish. -/
theorem inner_weakDeriv_single_comm {u v : SobolevEuclidean N 1 2 Ω}
    (hu : u ∈ SobolevEuclideanZero N 1 2 Ω) (hv : v ∈ SobolevEuclideanZero N 1 2 Ω)
    (i j : Fin N) :
    ⟪SobolevMultiIndex.weakDeriv u (MultiIndexLE.single j),
        SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i)⟫_ℝ
      = ⟪SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i),
        SobolevMultiIndex.weakDeriv v (MultiIndexLE.single j)⟫_ℝ := by
  obtain ⟨B, hB⟩ : ∃ B : SesqForm ℝ (SobolevEuclidean N 1 2 Ω), B
      = Elliptic.pairing Ω (ContinuousLinearMap.id ℝ _) (MultiIndexLE.single j)
          (MultiIndexLE.single i)
        - Elliptic.pairing Ω (ContinuousLinearMap.id ℝ _) (MultiIndexLE.single i)
          (MultiIndexLE.single j) := ⟨_, rfl⟩
  have hBapply : ∀ u v : SobolevEuclidean N 1 2 Ω, B u v
      = ⟪SobolevMultiIndex.weakDeriv u (MultiIndexLE.single j),
          SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i)⟫_ℝ
        - ⟪SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i),
          SobolevMultiIndex.weakDeriv v (MultiIndexLE.single j)⟫_ℝ := fun u v ↦ by
    rw [hB, sub_apply, sub_apply, Elliptic.pairing_apply, Elliptic.pairing_apply]
    rfl
  obtain ⟨w, φ, hφ, hw⟩ := SobolevMultiIndexZero.exists_seq_testFunction_tendsto hu
  obtain ⟨w', ψ, hψ, hw'⟩ := SobolevMultiIndexZero.exists_seq_testFunction_tendsto hv
  have h0 : ∀ n m, B (w n) (w' m) = 0 := fun n m ↦ by
    rw [hBapply, inner_weakDeriv_single_comm_of_testFunction (hφ n) (hψ m), sub_self]
  have h1 : ∀ n, B (w n) v = 0 := fun n ↦ by
    refine tendsto_nhds_unique (((B (w n)).continuous.tendsto v).comp hw') ?_
    have : (B (w n) ∘ w') = fun _ ↦ (0 : ℝ) := funext fun m ↦ h0 n m
    rw [this]
    exact tendsto_const_nhds
  have h2 : B u v = 0 := by
    refine tendsto_nhds_unique (((B.flip v).continuous.tendsto u).comp hw) ?_
    have : (B.flip v ∘ w) = fun _ ↦ (0 : ℝ) := funext fun n ↦ h1 n
    rw [this]
    exact tendsto_const_nhds
  rw [hBapply] at h2
  exact sub_eq_zero.1 h2

end SobolevEuclideanZero

end Comm

/-! ### Vector fields with components in $H^1_0(\Omega)$, and the linearized strain -/

variable (N : ℕ) (Ω : Opens (EuclideanSpace ℝ (Fin N))) in
/-- **The space $[H^1_0(\Omega)]^N$** of vector fields $v = (v_1, \dots, v_N)$ with components
$v_i \in H^1_0(\Omega)$. It is a Hilbert space with the norm
$\|v\|^2 = \sum_i \|v_i\|^2_{H^1(\Omega)}$.

The space is the $\ell^2$ product `PiLp 2` of $N$ copies of $H^1_0(\Omega)$, which is
`SobolevEuclideanZero N 1 2 Ω`. -/
abbrev SobolevEuclideanZeroVec : Type :=
  PiLp 2 fun _ : Fin N ↦ SobolevEuclideanZero N 1 2 Ω

namespace SobolevEuclideanZeroVec

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **The partial derivative** $v \mapsto \partial_j v_i$ on $[H^1_0(\Omega)]^N$, as a continuous
linear map into $L^2(\Omega)$. -/
def partialL (i j : Fin N) :
    SobolevEuclideanZeroVec N Ω →L[ℝ]
      Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  (SobolevMultiIndex.weakDerivL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
    (MultiIndexLE.single j)).comp
    ((SobolevEuclideanZero N 1 2 Ω).subtypeL.comp
      (PiLp.proj 2 (fun _ : Fin N ↦ SobolevEuclideanZero N 1 2 Ω) i))

/-- The value of `SobolevEuclideanZeroVec.partialL i j` at $v$ is the weak partial derivative
$\partial_j v_i$ of the component $v_i$. -/
@[simp]
theorem partialL_apply (i j : Fin N) (v : SobolevEuclideanZeroVec N Ω) :
    partialL i j v
      = SobolevMultiIndex.weakDeriv (v i : SobolevEuclidean N 1 2 Ω) (MultiIndexLE.single j) :=
  rfl

/-- For $v \in [H^1_0(\Omega)]^N$, $\|\partial_j v_i\|_{L^2(\Omega)} \le \|v\|$. -/
theorem norm_partialL_apply_le (i j : Fin N) (v : SobolevEuclideanZeroVec N Ω) :
    ‖partialL i j v‖ ≤ ‖v‖ := by
  rw [partialL_apply]
  refine (SobolevMultiIndex.norm_weakDeriv_le _ _).trans ?_
  rw [Submodule.norm_coe]
  exact PiLp.norm_apply_le v i

/-- **The linearized strain** $\varepsilon(v)_{ij} = \frac12 (\partial_j v_i + \partial_i v_j)$ of a
vector field $v \in [H^1_0(\Omega)]^N$, as a continuous linear map into $L^2(\Omega)$. This is
(8.5.2) of [han2009theoretical]. -/
def strainL (i j : Fin N) :
    SobolevEuclideanZeroVec N Ω →L[ℝ]
      Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  (1 / 2 : ℝ) • (partialL i j + partialL j i)

/-- The strain is $\varepsilon(v)_{ij} = \frac12 (\partial_j v_i + \partial_i v_j)$. -/
theorem strainL_apply (i j : Fin N) (v : SobolevEuclideanZeroVec N Ω) :
    strainL i j v = (1 / 2 : ℝ) • (partialL i j v + partialL j i v) :=
  rfl

/-- The strain is symmetric: $\varepsilon(v)_{ij} = \varepsilon(v)_{ji}$, as an identity of
continuous linear maps. -/
theorem strainL_symm (i j : Fin N) : (strainL i j : SobolevEuclideanZeroVec N Ω →L[ℝ] _)
      = strainL j i := by
  rw [strainL, strainL, add_comm]

/-- For $v \in [H^1_0(\Omega)]^N$, $\|\varepsilon(v)_{ij}\|_{L^2(\Omega)} \le \|v\|$. -/
theorem norm_strainL_apply_le (i j : Fin N) (v : SobolevEuclideanZeroVec N Ω) :
    ‖strainL i j v‖ ≤ ‖v‖ := by
  rw [strainL_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc 1 / 2 * ‖partialL i j v + partialL j i v‖
      ≤ 1 / 2 * (‖partialL i j v‖ + ‖partialL j i v‖) := by gcongr; exact norm_add_le _ _
    _ ≤ 1 / 2 * (‖v‖ + ‖v‖) := by
        gcongr
        · exact norm_partialL_apply_le i j v
        · exact norm_partialL_apply_le j i v
    _ = ‖v‖ := by ring

/-- The operator norm of the strain $v \mapsto \varepsilon(v)_{ij}$ is at most $1$. -/
theorem norm_strainL_le (i j : Fin N) : ‖(strainL i j : SobolevEuclideanZeroVec N Ω →L[ℝ] _)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v ↦ by
    rw [one_mul]
    exact norm_strainL_apply_le i j v

/-! ### Korn's identity and Korn's first inequality -/

/-- **Korn's identity on $[H^1_0(\Omega)]^N$.** For $v \in [H^1_0(\Omega)]^N$,
$$\int_\Omega |\varepsilon(v)|^2 = \frac12 \int_\Omega |\nabla v|^2 + \frac12 \int_\Omega
  (\operatorname{div} v)^2,$$
that is, $\sum_{i,j} \|\varepsilon(v)_{ij}\|^2 = \frac12 \sum_{i,j} \|\partial_j v_i\|^2 +
\frac12 \|\sum_i \partial_i v_i\|^2$, with norms in $L^2(\Omega)$.

Expanding $\|\frac12 (\partial_j v_i + \partial_i v_j)\|^2$ gives $\frac14 (\|\partial_j
v_i\|^2 + \|\partial_i v_j\|^2) + \frac12 (\partial_j v_i, \partial_i v_j)$. On $H^1_0(\Omega)$,
$(\partial_j v_i, \partial_i v_j) = (\partial_i v_i, \partial_j v_j)$
(`SobolevEuclideanZero.inner_weakDeriv_single_comm`), and the double sum of these terms is
$\|\sum_i \partial_i v_i\|^2$. -/
theorem sum_norm_strainL_sq_eq (v : SobolevEuclideanZeroVec N Ω) :
    ∑ i, ∑ j, ‖strainL i j v‖ ^ 2
      = (1 / 2 : ℝ) * ∑ i, ∑ j, ‖partialL i j v‖ ^ 2
        + (1 / 2 : ℝ) * ‖∑ i, partialL i i v‖ ^ 2 := by
  obtain ⟨P, hP⟩ : ∃ P : Fin N → Fin N →
      Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      P = fun i j ↦ partialL i j v := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : Fin N → Fin N →
      Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      S = fun i j ↦ strainL i j v := ⟨_, rfl⟩
  have hSP : ∀ i j, S i j = (1 / 2 : ℝ) • (P i j + P j i) := fun i j ↦ by
    rw [hS, hP]
    exact strainL_apply i j v
  have e1 : ∀ i j, ‖S i j‖ ^ 2
      = (1 / 4 : ℝ) * (‖P i j‖ ^ 2 + ‖P j i‖ ^ 2) + (1 / 2 : ℝ) * ⟪P i j, P j i⟫_ℝ := fun i j ↦ by
    rw [hSP, norm_smul, mul_pow, norm_add_sq_real, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    ring
  have e2 : ∀ i j, ⟪P i j, P j i⟫_ℝ = ⟪P i i, P j j⟫_ℝ := fun i j ↦ by
    rw [hP]
    simp only [partialL_apply]
    exact SobolevEuclideanZero.inner_weakDeriv_single_comm (v i).2 (v j).2 i j
  have e3 : ∑ i, ∑ j, ⟪P i i, P j j⟫_ℝ = ‖∑ i, P i i‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    exact Finset.sum_congr rfl fun i _ ↦ (inner_sum _ _ _).symm
  have e4 : ∑ i, ∑ j, ‖P j i‖ ^ 2 = ∑ i, ∑ j, ‖P i j‖ ^ 2 := Finset.sum_comm
  have key : ∑ i, ∑ j, ‖S i j‖ ^ 2
      = (1 / 2 : ℝ) * ∑ i, ∑ j, ‖P i j‖ ^ 2 + (1 / 2 : ℝ) * ‖∑ i, P i i‖ ^ 2 := by
    calc ∑ i, ∑ j, ‖S i j‖ ^ 2
        = ∑ i, ∑ j, ((1 / 4 : ℝ) * (‖P i j‖ ^ 2 + ‖P j i‖ ^ 2)
            + (1 / 2 : ℝ) * ⟪P i i, P j j⟫_ℝ) :=
          Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by rw [e1, e2]
      _ = (1 / 4 : ℝ) * (∑ i, ∑ j, ‖P i j‖ ^ 2 + ∑ i, ∑ j, ‖P j i‖ ^ 2)
            + (1 / 2 : ℝ) * ∑ i, ∑ j, ⟪P i i, P j j⟫_ℝ := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = (1 / 2 : ℝ) * ∑ i, ∑ j, ‖P i j‖ ^ 2 + (1 / 2 : ℝ) * ‖∑ i, P i i‖ ^ 2 := by
          rw [e3, e4]
          ring
  rw [hS, hP] at key
  exact key

/-- **Korn's first inequality on $[H^1_0(\Omega)]^N$.** For $v \in [H^1_0(\Omega)]^N$,
$$\frac12 \int_\Omega |\nabla v|^2 \le \int_\Omega |\varepsilon(v)|^2,$$
that is, $\frac12 \sum_{i,j} \|\partial_j v_i\|^2 \le \sum_{i,j} \|\varepsilon(v)_{ij}\|^2$,
with norms in $L^2(\Omega)$.

The inequality follows from Korn's identity `SobolevEuclideanZeroVec.sum_norm_strainL_sq_eq`,
because the term $\frac12 \|\operatorname{div} v\|^2$ is nonnegative. -/
theorem korn_first (v : SobolevEuclideanZeroVec N Ω) :
    (1 / 2 : ℝ) * ∑ i, ∑ j, ‖partialL i j v‖ ^ 2 ≤ ∑ i, ∑ j, ‖strainL i j v‖ ^ 2 := by
  rw [sum_norm_strainL_sq_eq]
  have : 0 ≤ (1 / 2 : ℝ) * ‖∑ i, partialL i i v‖ ^ 2 := by positivity
  linarith

/-- The squared norm of $v \in [H^1_0(\Omega)]^N$ is the sum of the squared $H^1(\Omega)$ norms of
its components: $\|v\|^2 = \sum_i \|v_i\|^2_{H^1(\Omega)}$. -/
theorem norm_sq_eq (v : SobolevEuclideanZeroVec N Ω) :
    ‖v‖ ^ 2 = ∑ i, ‖(v i : SobolevEuclidean N 1 2 Ω)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [Submodule.norm_coe]

end SobolevEuclideanZeroVec

/-! ### Korn plus Poincaré on a bounded domain -/

namespace SobolevEuclideanZeroVec

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **Poincaré's inequality on $[H^1_0(\Omega)]^N$.** Let $\Omega \subseteq \mathbb{R}^{d+1}$ be
open, let $R \ge 0$ and $\Omega \subseteq B(0, R)$. Then for $v \in [H^1_0(\Omega)]^{d+1}$,
$$\|v\|^2 \le (1 + (2R)^2) \sum_{i,j} \|\partial_j v_i\|^2_{L^2(\Omega)}.$$

The proof applies `SobolevEuclideanZero.norm_le_gradNorm` at $p = 2$ to each component. -/
theorem norm_sq_le_sum_norm_partialL_sq {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (v : SobolevEuclideanZeroVec (d + 1) Ω) :
    ‖v‖ ^ 2 ≤ (1 + (2 * R) ^ 2) * ∑ i, ∑ j, ‖partialL i j v‖ ^ 2 := by
  rw [norm_sq_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  obtain ⟨u, hu⟩ : ∃ u : SobolevEuclideanZero (d + 1) 1 2 Ω, u = v i := ⟨_, rfl⟩
  have hPj : ∀ j, partialL i j v = SobolevMultiIndex.weakDeriv
      (u : SobolevEuclidean (d + 1) 1 2 Ω) (MultiIndexLE.single j) := fun j ↦ by
    rw [partialL_apply, hu]
  have hsum : ∑ j, ‖partialL i j v‖ ^ 2 = ∑ j, ‖SobolevMultiIndex.weakDeriv
      (u : SobolevEuclidean (d + 1) 1 2 Ω) (MultiIndexLE.single j)‖ ^ 2 :=
    Finset.sum_congr rfl fun j _ ↦ by rw [hPj]
  rw [← hu, hsum]
  exact SobolevEuclideanZero.norm_sq_le_sum_norm_weakDeriv_single_sq hR hΩ u

/-- **Korn's first inequality with Poincaré's constant.** Let $\Omega \subseteq \mathbb{R}^{d+1}$ be
open, let $R \ge 0$ and $\Omega \subseteq B(0, R)$. Then for $v \in [H^1_0(\Omega)]^{d+1}$,
$$\|v\|^2 \le 2 (1 + (2R)^2) \sum_{i,j} \|\varepsilon(v)_{ij}\|^2_{L^2(\Omega)}.$$

So $\int_\Omega |\varepsilon(v)|^2$ is an equivalent squared norm on $[H^1_0(\Omega)]^{d+1}$. A
bilinear form bounded below by $\alpha \int_\Omega |\varepsilon(v)|^2$ is therefore $V$-elliptic
on this space, with constant $\alpha / (2 (1 + (2R)^2))$. -/
theorem norm_sq_le_sum_norm_strainL_sq {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (v : SobolevEuclideanZeroVec (d + 1) Ω) :
    ‖v‖ ^ 2 ≤ 2 * (1 + (2 * R) ^ 2) * ∑ i, ∑ j, ‖strainL i j v‖ ^ 2 := by
  have h1 := norm_sq_le_sum_norm_partialL_sq hR hΩ v
  have h2 := korn_first v
  nlinarith

end SobolevEuclideanZeroVec

end

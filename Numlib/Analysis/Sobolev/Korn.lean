import Numlib.Analysis.PDE.Elliptic.Dirichlet

/-!
# Korn's first inequality on `[H¹₀(Ω)]^N`

For a vector field `v = (v₁, …, v_N)` with components in `H¹₀(Ω)`, the *linearized strain* is the
symmetric matrix of `L²(Ω)` functions `ε(v)_{ij} = ½ (∂_j v_i + ∂_i v_j)`. **Korn's first
inequality** is the bound `∫_Ω |∇v|² ≤ 2 ∫_Ω |ε(v)|²`, which together with Poincaré's inequality
makes `∫_Ω |ε(v)|²` an equivalent squared norm on `[H¹₀(Ω)]^N`; it is the `V`-ellipticity behind
the linearized elasticity problem of [han2009theoretical] §8.5 (Theorem 8.5.1) in the pure
displacement case `Γ_D = ∂Ω`.

The proof is the identity `∫_Ω |ε(v)|² = ½ ∫_Ω |∇v|² + ½ ∫_Ω (div v)²`, itself a consequence of

`∫_Ω ∂_j u ∂_i v = ∫_Ω ∂_i u ∂_j v`  for `u, v ∈ H¹₀(Ω)`,

two integrations by parts against test functions (`∫ ∂_j φ ∂_i ψ = -∫ φ ∂_j ∂_i ψ = -∫ φ ∂_i ∂_j ψ
= ∫ ∂_i φ ∂_j ψ`) extended to `H¹₀(Ω)` by density, both sides being continuous bilinear forms.
This is what fails on `H¹(Ω)`: the boundary terms of the integrations by parts do not vanish, and
Korn's *second* inequality on `H¹(Ω)` (with the `L²` norm on the right) needs the regularity of
the boundary and a compactness argument that are not here.

## Main definitions and results

* `SobolevEuclideanZero.inner_weakDeriv_single_comm`: `⟪∂_j u, ∂_i v⟫_{L²} = ⟪∂_i u, ∂_j v⟫_{L²}`
  for `u, v ∈ H¹₀(Ω)`;
* `SobolevEuclideanZeroVec N Ω`, the Hilbert space `[H¹₀(Ω)]^N` as the `ℓ²` product of `N` copies
  of `H¹₀(Ω)`, with `SobolevEuclideanZeroVec.partialL i j` (`∂_j v_i`) and
  `SobolevEuclideanZeroVec.strainL i j` (`ε(v)_{ij}`) as continuous linear maps into `L²(Ω)`;
* `SobolevEuclideanZeroVec.sum_norm_strainL_sq_eq`, the identity
  `∫_Ω |ε(v)|² = ½ ∫_Ω |∇v|² + ½ ∫_Ω (div v)²`, and `SobolevEuclideanZeroVec.korn_first`,
  `½ ∫_Ω |∇v|² ≤ ∫_Ω |ε(v)|²`;
* `SobolevEuclideanZeroVec.norm_sq_le_sum_norm_strainL_sq`: on a bounded `Ω ⊆ B(0, R) ⊆ ℝ^{d+1}`,
  `‖v‖²_{[H¹]^N} ≤ 2 (1 + (2R)²) ∫_Ω |ε(v)|²` (Korn plus Poincaré, Corollary 9.19 of
  [brezis2011functional]).

## References

[han2009theoretical] §8.5 (Korn's inequality is quoted after Theorem 8.5.1);
[brezis2011functional] Corollary 9.19 for Poincaré's inequality.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology InnerProductSpace

noncomputable section

/-! ### The commutation `∫ ∂_j u ∂_i v = ∫ ∂_i u ∂_j v` on `H¹₀(Ω)` -/

section Comm

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **Two integrations by parts on test functions**: `∫_Ω ∂_v φ ∂_w ψ = ∫_Ω ∂_w φ ∂_v ψ` for
`φ, ψ ∈ C_0^∞(Ω)` and directions `v, w`, since both sides are `-∫_Ω φ ∂_v ∂_w ψ` by the symmetry
of the second derivative of `ψ`. -/
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

/-- The commutation `⟪∂_j w, ∂_i w'⟫ = ⟪∂_i w, ∂_j w'⟫` for elements of `H¹(Ω)` whose functions
are test functions on `Ω`: their partial derivatives are the classical ones
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

/-- **The commutation `∫_Ω ∂_j u ∂_i v = ∫_Ω ∂_i u ∂_j v` on `H¹₀(Ω)`**: for `u, v ∈ H¹₀(Ω)` and
`i, j`, `⟪∂_j u, ∂_i v⟫_{L²(Ω)} = ⟪∂_i u, ∂_j v⟫_{L²(Ω)}`. Two integrations by parts on test
functions (`TestFunction.setIntegral_fderiv_mul_fderiv_comm`), extended by density: both sides
are continuous bilinear forms on `H¹(Ω)` (sums of `Elliptic.pairing`s) and agree on the dense
subspace of test functions. On `H¹(Ω)` the identity fails, the boundary terms not vanishing. -/
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

/-! ### Vector fields with components in `H¹₀(Ω)`, and the linearized strain -/

variable (N : ℕ) (Ω : Opens (EuclideanSpace ℝ (Fin N))) in
/-- **The space `[H¹₀(Ω)]^N` of vector fields with components in `H¹₀(Ω)`**, as the `ℓ²` product
of `N` copies of `H¹₀(Ω) = SobolevEuclideanZero N 1 2 Ω`: a Hilbert space with
`‖v‖² = ∑ᵢ ‖vᵢ‖²_{H¹(Ω)}`. -/
abbrev SobolevEuclideanZeroVec : Type :=
  PiLp 2 fun _ : Fin N ↦ SobolevEuclideanZero N 1 2 Ω

namespace SobolevEuclideanZeroVec

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **The partial derivative `∂_j v_i`** of a vector field `v ∈ [H¹₀(Ω)]^N`, as a continuous
linear map into `L²(Ω)`. -/
def partialL (i j : Fin N) :
    SobolevEuclideanZeroVec N Ω →L[ℝ]
      Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  (SobolevMultiIndex.weakDerivL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
    (MultiIndexLE.single j)).comp
    ((SobolevEuclideanZero N 1 2 Ω).subtypeL.comp
      (PiLp.proj 2 (fun _ : Fin N ↦ SobolevEuclideanZero N 1 2 Ω) i))

/-- `partialL i j v = ∂_j v_i`. -/
@[simp]
theorem partialL_apply (i j : Fin N) (v : SobolevEuclideanZeroVec N Ω) :
    partialL i j v
      = SobolevMultiIndex.weakDeriv (v i : SobolevEuclidean N 1 2 Ω) (MultiIndexLE.single j) :=
  rfl

/-- `‖∂_j v_i‖_{L²} ≤ ‖v_i‖_{H¹} ≤ ‖v‖`. -/
theorem norm_partialL_apply_le (i j : Fin N) (v : SobolevEuclideanZeroVec N Ω) :
    ‖partialL i j v‖ ≤ ‖v‖ := by
  rw [partialL_apply]
  refine (SobolevMultiIndex.norm_weakDeriv_le _ _).trans ?_
  rw [Submodule.norm_coe]
  exact PiLp.norm_apply_le v i

/-- **The linearized strain `ε(v)_{ij} = ½ (∂_j v_i + ∂_i v_j)`** of a vector field
`v ∈ [H¹₀(Ω)]^N` ([han2009theoretical] (8.5.2)), as a continuous linear map into `L²(Ω)`. -/
def strainL (i j : Fin N) :
    SobolevEuclideanZeroVec N Ω →L[ℝ]
      Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  (1 / 2 : ℝ) • (partialL i j + partialL j i)

/-- `strainL i j v = ½ (∂_j v_i + ∂_i v_j)`. -/
theorem strainL_apply (i j : Fin N) (v : SobolevEuclideanZeroVec N Ω) :
    strainL i j v = (1 / 2 : ℝ) • (partialL i j v + partialL j i v) :=
  rfl

/-- The strain is symmetric: `ε(v)_{ij} = ε(v)_{ji}`. -/
theorem strainL_symm (i j : Fin N) : (strainL i j : SobolevEuclideanZeroVec N Ω →L[ℝ] _)
      = strainL j i := by
  rw [strainL, strainL, add_comm]

/-- `‖ε(v)_{ij}‖_{L²} ≤ ‖v‖`. -/
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

/-- The operator norm of the strain is at most one. -/
theorem norm_strainL_le (i j : Fin N) : ‖(strainL i j : SobolevEuclideanZeroVec N Ω →L[ℝ] _)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v ↦ by
    rw [one_mul]
    exact norm_strainL_apply_le i j v

/-! ### Korn's identity and Korn's first inequality -/

/-- **Korn's identity on `[H¹₀(Ω)]^N`**: `∫_Ω |ε(v)|² = ½ ∫_Ω |∇v|² + ½ ∫_Ω (div v)²`, that is
`∑ᵢⱼ ‖ε(v)_{ij}‖² = ½ ∑ᵢⱼ ‖∂_j v_i‖² + ½ ‖∑ᵢ ∂_i v_i‖²` in `L²(Ω)`. Expanding
`‖½ (∂_j v_i + ∂_i v_j)‖²` gives `¼ (‖∂_j v_i‖² + ‖∂_i v_j‖²) + ½ ⟪∂_j v_i, ∂_i v_j⟫`, and
`⟪∂_j v_i, ∂_i v_j⟫ = ⟪∂_i v_i, ∂_j v_j⟫` on `H¹₀(Ω)`
(`SobolevEuclideanZero.inner_weakDeriv_single_comm`), whose double sum is `‖∑ᵢ ∂_i v_i‖²`. -/
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

/-- **Korn's first inequality on `[H¹₀(Ω)]^N`**: `½ ∫_Ω |∇v|² ≤ ∫_Ω |ε(v)|²`, that is
`½ ∑ᵢⱼ ‖∂_j v_i‖² ≤ ∑ᵢⱼ ‖ε(v)_{ij}‖²`, the term `½ ‖div v‖²` of Korn's identity being
nonnegative. -/
theorem korn_first (v : SobolevEuclideanZeroVec N Ω) :
    (1 / 2 : ℝ) * ∑ i, ∑ j, ‖partialL i j v‖ ^ 2 ≤ ∑ i, ∑ j, ‖strainL i j v‖ ^ 2 := by
  rw [sum_norm_strainL_sq_eq]
  have : 0 ≤ (1 / 2 : ℝ) * ‖∑ i, partialL i i v‖ ^ 2 := by positivity
  linarith

/-- The squared norm of `[H¹₀(Ω)]^N` is the sum of the squared `H¹` norms of the components. -/
theorem norm_sq_eq (v : SobolevEuclideanZeroVec N Ω) :
    ‖v‖ ^ 2 = ∑ i, ‖(v i : SobolevEuclidean N 1 2 Ω)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [Submodule.norm_coe]

end SobolevEuclideanZeroVec

/-! ### Korn plus Poincaré on a bounded domain -/

namespace SobolevEuclideanZeroVec

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **Poincaré's inequality on `[H¹₀(Ω)]^N`**: for `Ω ⊆ B(0, R)`,
`‖v‖² ≤ (1 + (2R)²) ∑ᵢⱼ ‖∂_j v_i‖²`, from `SobolevEuclideanZero.norm_le_gradNorm` on each
component. -/
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

/-- **Korn's first inequality with Poincaré's constant**: for `Ω ⊆ B(0, R) ⊆ ℝ^{d+1}` and
`v ∈ [H¹₀(Ω)]^{d+1}`, `‖v‖² ≤ 2 (1 + (2R)²) ∑ᵢⱼ ‖ε(v)_{ij}‖²`; so `∫_Ω |ε(v)|²` is an equivalent
squared norm on `[H¹₀(Ω)]^{d+1}`, and any bilinear form bounded below by `α ∫_Ω |ε(v)|²` is
`V`-elliptic there with constant `α / (2 (1 + (2R)²))`. -/
theorem norm_sq_le_sum_norm_strainL_sq {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (v : SobolevEuclideanZeroVec (d + 1) Ω) :
    ‖v‖ ^ 2 ≤ 2 * (1 + (2 * R) ^ 2) * ∑ i, ∑ j, ‖strainL i j v‖ ^ 2 := by
  have h1 := norm_sq_le_sum_norm_partialL_sq hR hΩ v
  have h2 := korn_first v
  have h3 : 0 ≤ 1 + (2 * R) ^ 2 := by positivity
  nlinarith

end SobolevEuclideanZeroVec

end

import Numlib.Analysis.Normed.Operator.Scaling
import Numlib.Analysis.Sobolev.Affine
import Numlib.Analysis.Sobolev.SeminormCompare
import Numlib.Analysis.Sobolev.Simplex
import Numlib.Analysis.Sobolev.Triangulation
import Numlib.FiniteElement.LagrangeElement

/-!
# Finite element interpolation error on affine families and triangulations

The interpolation error estimates of the finite element method, by the reference element
technique: the error of nodal interpolation is estimated on a fixed reference element `K̂` by the
Bramble–Hilbert lemma, transported to every affine image `K = F_K(K̂)`, `F_K x̂ = T_K x̂ + b_K`,
made uniform over a *regular* family of elements, and summed over the elements of a
triangulation. The one-dimensional counterpart is `Numlib/Approximation/SobolevInterpolation.lean`.

The interpolation operator of a reference element with nodes `x̂ᵢ` and shape functions `φ̂ᵢ` is
`Approximation.nodalInterp xhat φhat`, `Π̂ v̂ = ∑ᵢ v̂(x̂ᵢ) φ̂ᵢ`; on `K` it is
`Approximation.nodalInterp`
at the nodes `F_K(x̂ᵢ)` with the shape functions `φ̂ᵢ ∘ F_K⁻¹`, and nodal interpolation commutes
with the affine pullback (`Approximation.nodalInterp_comp`). Spaces and seminorms are the tensor
ones, `MemSobolev v m 2 K volume`, `sobolevSeminorm`, `sobolevNorm`.

## Design

* **The reference element is a Sobolev extension domain**, as a hypothesis
  (`IsSobolevExtensionDomainAll`): that is what the embedding `H^{k+1}(K̂) ↪ C(K̂̄)` and the
  Bramble–Hilbert estimate of the backbone need (`Numlib/Analysis/Sobolev/{Compactness,
  DenyLions}.lean`). The reference triangle is one (`isSobolevExtensionDomainAll_referenceTriangle`)
  and so is the unit square.
* **Functions are read on a representative continuous up to the boundary**
  (`ContinuousOn v (closure K)`), so that the nodal values are meaningful at nodes on `∂K`; every
  element of `H^{k+1}(K)`, `k + 1 > d/2`, has one.
* **Regularity of a family** (`FiniteElement.IsRegularFamily`) asks for *some* inscribed ball of
  radius `r` with `h_K ≤ σ (2 r)`, rather than for the largest inscribed ball, which Mathlib has no
  name for; the mesh parameter is the supremum of the diameters, written inline so as not to
  clash with `FiniteElement.meshSize` of `Numlib/Variational/FiniteElementInterval.lean`.
* The local estimate on an affine image is proved directly from the affine change of variables
  in `H^m` (`sobolevSeminorm_comp_affine_le`) and the operator-norm bound by inscribed balls
  (`ContinuousLinearMap.opNorm_le_diam_div`).

## Main results

* `FiniteElement.sobolevSeminorm_sub_nodalInterp_le` — `|v̂ − Π̂ v̂|_{m,K̂} ≤ c |v̂|_{k+1,K̂}` on
  the reference element, under the polynomial invariance `ℙ_k(K̂) ⊆ X̂`.
* `FiniteElement.sobolevSeminorm_sub_nodalInterp_comp_affine_le` —
  `|v − Π_K v|_{m,K} ≤ c h_K^{k+1} ρ_K^{−m} |v|_{k+1,K}` on every affine image.
* `FiniteElement.IsRegularFamily` and `FiniteElement.sobolevNorm_sub_nodalInterp_comp_affine_le` —
  `‖v − Π_K v‖_{m,K} ≤ c h_K^{k+1−m} |v|_{k+1,K}` on a regular family.
* `Triangulation.sobolevNorm_sub_globalInterp_le` — the global estimate
  `‖v − Π_h v‖_{m,Ω} ≤ c h^{k+1−m} |v|_{k+1,Ω}`, `m = 0, 1`, for a conforming element on a regular
  family of triangulations, and `LagrangeElement.sobolevNorm_sub_globalInterp_le` its instance for
  the `ℙ_k` Lagrange element.

## References

* [han2009theoretical] §10.3: Theorem 10.3.3, Theorem 10.3.4, Theorem 10.3.5, Definition 10.3.6,
  Corollary 10.3.7, Theorem 10.3.9.
-/

open Filter Metric Topology MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

namespace FiniteElement

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- The polynomial function `x ↦ q(x)` on `ℝ^d` is continuous. -/
private theorem continuous_eval_coords (q : MvPolynomial (Fin d) ℝ) :
    Continuous fun x : 𝔼 ↦ MvPolynomial.eval (fun i ↦ x i) q :=
  (MvPolynomial.continuous_eval q).comp (PiLp.continuous_ofLp 2 _)

/-! ### Nodal interpolation in Sobolev spaces -/

variable {Ω : Opens (EuclideanSpace ℝ (Fin d))}

/-- The nodal interpolant of any function lies in `W^{m,p}(Ω)` when the shape functions do. -/
theorem memSobolev_nodalInterp {I : ℕ} {x : Fin I → EuclideanSpace ℝ (Fin d)}
    {φ : Fin I → EuclideanSpace ℝ (Fin d) → ℝ} {m : ℕ} {p : ℝ≥0∞}
    (hφ : ∀ i, MemSobolev (φ i) m p Ω volume) (v : EuclideanSpace ℝ (Fin d) → ℝ) :
    MemSobolev (Approximation.nodalInterp x φ v) m p Ω volume := by
  rw [Approximation.nodalInterp_eq_sum_smul]
  exact MemSobolev.finsetSum fun i _ ↦ (hφ i).const_smul _

/-- The Sobolev seminorm of a nodal interpolant is bounded by the nodal values times the
seminorms of the shape functions: `|Π̂ v̂|_{m,K̂} ≤ ∑ᵢ |v̂(x̂ᵢ)| |φ̂ᵢ|_{m,K̂}`. -/
theorem sobolevSeminorm_nodalInterp_le {I : ℕ} {x : Fin I → EuclideanSpace ℝ (Fin d)}
    {φ : Fin I → EuclideanSpace ℝ (Fin d) → ℝ} {m : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hφ : ∀ i, MemSobolev (φ i) m p Ω volume) (v : EuclideanSpace ℝ (Fin d) → ℝ) :
    sobolevSeminorm (Approximation.nodalInterp x φ v) m p Ω volume
      ≤ ∑ i, ‖v (x i)‖ₑ * sobolevSeminorm (φ i) m p Ω volume := by
  rw [Approximation.nodalInterp_eq_sum_smul]
  exact sobolevSeminorm_sum_smul_le hp (fun i _ ↦ hφ i) _

/-- **The interpolation operator is bounded** (the first display of the proof of
[han2009theoretical] Theorem 10.3.3): for a bounded linear `ι : V → C(K)` and nodes `yᵢ ∈ K`,
`|∑ᵢ (ι w)(yᵢ) φᵢ|_{m,Ω} ≤ ‖ι‖ ‖w‖ ∑ᵢ |φᵢ|_{m,Ω}`. -/
theorem sobolevSeminorm_sum_apply_smul_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {K : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace K] (ι : V →L[ℝ] C(K, ℝ)) {I : ℕ}
    (y : Fin I → K) {φ : Fin I → EuclideanSpace ℝ (Fin d) → ℝ} {m : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hφ : ∀ i, MemSobolev (φ i) m p Ω volume) (w : V) :
    sobolevSeminorm (∑ i, (ι w (y i)) • φ i) m p Ω volume
      ≤ ENNReal.ofReal (‖ι‖ * ‖w‖ * ∑ i, (sobolevSeminorm (φ i) m p Ω volume).toReal) := by
  refine (sobolevSeminorm_sum_smul_le hp (fun i _ ↦ hφ i) _).trans ?_
  calc ∑ i, ‖ι w (y i)‖ₑ * sobolevSeminorm (φ i) m p Ω volume
      ≤ ∑ i, ENNReal.ofReal (‖ι‖ * ‖w‖) * sobolevSeminorm (φ i) m p Ω volume := by
        gcongr with i
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal
          ((ContinuousMap.norm_coe_le_norm _ _).trans (ι.le_opNorm w))
    _ = ENNReal.ofReal (‖ι‖ * ‖w‖) * ∑ i, sobolevSeminorm (φ i) m p Ω volume := by
        rw [Finset.mul_sum]
    _ = _ := by
        rw [ENNReal.ofReal_mul (p := ‖ι‖ * ‖w‖) (by positivity),
          ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ ENNReal.toReal_nonneg]
        congr 1
        exact Finset.sum_congr rfl fun i _ ↦
          (ENNReal.ofReal_toReal (hφ i).sobolevSeminorm_ne_top).symm

local notation "𝟚" => ((2 : ℝ≥0) : ℝ≥0∞)

/-! ### The estimate on the reference element -/

/-- **The polynomial invariance on `ℙ_k(K̂) ⊆ H^{k+1}(K̂)`** ([han2009theoretical] (10.3.4)): if
the nodal interpolation
`Π̂` reproduces every polynomial of degree at most `k` on `K̂`, and `ι : H^{k+1}(K̂) → C(K)` sends
each element to (the restriction to `K ⊇ K̂` of) a continuous representative, then for
`q ∈ ℙ_k(K̂)` the interpolant `∑ᵢ (ι q)(x̂ᵢ) φ̂ᵢ` of that representative is `q` almost everywhere
on `K̂`. The nodes may lie on the boundary of `K̂`, which is why the representative is read on
`K ⊇ closure K̂`. -/
theorem sum_apply_smul_ae_eq_fn_of_mem_polynomialSubmodule
    {Khat : Opens (EuclideanSpace ℝ (Fin d))}
    (hb : Bornology.IsBounded (Khat : Set (EuclideanSpace ℝ (Fin d)))) {k : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace K]
    (ι : SobolevEuclidean d (k + 1) 𝟚 Khat →L[ℝ] C(K, ℝ))
    (hι : ∀ u, ∃ ut : EuclideanSpace ℝ (Fin d) → ℝ, Continuous ut ∧
      SobolevMultiIndex.fn u =ᵐ[volume.restrict (Khat : Set (EuclideanSpace ℝ (Fin d)))] ut ∧
      ∀ x : K, ι u x = ut x)
    {I : ℕ} (xhat : Fin I → EuclideanSpace ℝ (Fin d))
    (φhat : Fin I → EuclideanSpace ℝ (Fin d) → ℝ) (hx : ∀ i, xhat i ∈ K)
    (hxc : ∀ i, xhat i ∈ closure (Khat : Set (EuclideanSpace ℝ (Fin d))))
    (hP : ∀ q : MvPolynomial (Fin d) ℝ, q.totalDegree ≤ k →
      ∀ x ∈ Khat, Approximation.nodalInterp xhat φhat
        (fun y ↦ MvPolynomial.eval (fun i ↦ y i) q) x = MvPolynomial.eval (fun i ↦ x i) q)
    {q : SobolevEuclidean d (k + 1) 𝟚 Khat}
    (hq : q ∈ SobolevEuclidean.polynomialSubmodule (k := k) (p := 𝟚) hb) :
    (∑ i, (ι q ⟨xhat i, hx i⟩) • φhat i)
      =ᵐ[volume.restrict (Khat : Set (EuclideanSpace ℝ (Fin d)))] SobolevMultiIndex.fn q := by
  obtain ⟨r, hr, hqr⟩ := (SobolevEuclidean.mem_polynomialSubmodule_iff hb).1 hq
  have hrep := hι q
  obtain ⟨qt, hqtc, hqtae, hqtι⟩ := hrep
  have hpq : EqOn (fun x : EuclideanSpace ℝ (Fin d) ↦ MvPolynomial.eval (fun i ↦ x i) r) qt
      (closure (Khat : Set (EuclideanSpace ℝ (Fin d)))) :=
    (continuous_eval_coords r).continuousOn.eqOn_closure_of_ae_eq Khat.isOpen hqtc.continuousOn
      (hqr.symm.trans hqtae)
  have hIq : (∑ i, (ι q ⟨xhat i, hx i⟩) • φhat i) = Approximation.nodalInterp xhat φhat
      (fun x : EuclideanSpace ℝ (Fin d) ↦ MvPolynomial.eval (fun i ↦ x i) r) := by
    rw [Approximation.nodalInterp_eq_sum_smul]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hqtι, ← hpq (hxc i)]
  rw [hIq]
  refine Filter.EventuallyEq.trans ?_ hqr.symm
  exact ae_restrict_of_forall_mem Khat.isOpen.measurableSet fun x hx' ↦
    hP r ((MvPolynomial.mem_restrictTotalDegree _ _ _).1 hr) x hx'

/-- **The interpolation error on the reference element** ([han2009theoretical] Theorem 10.3.3).
Let `K̂ ⊆ ℝ^d` be a bounded connected open reference element which is a Sobolev extension domain
for every exponent, let `m ≤ k + 1` and `k + 1 > d/2`, let `x̂ᵢ ∈ K̂̄` be the nodes and
`φ̂ᵢ ∈ H^m(K̂)` the shape functions of the interpolation operator `Π̂`, and assume the polynomial
invariance `Π̂ q = q` on `K̂` for every polynomial `q` of total degree at most `k`. Then there is a
constant `c` with `|v̂ − Π̂ v̂|_{m,K̂} ≤ c |v̂|_{k+1,K̂}` for every `v̂ ∈ H^{k+1}(K̂)`.

`v̂` is read on its continuous representative up to the boundary (`ContinuousOn v (closure K̂)`),
which every element has by the embedding `H^{k+1}(K̂) ↪ C(K̂̄)`
(`SobolevEuclidean.exists_isCompactEmbedding_toContinuousMap_of_order`), so that the nodal values
are meaningful at nodes on the boundary. The proof: `Π̂` is bounded from `H^{k+1}(K̂)` to `H^m(K̂)`
through the embedding (`sobolevSeminorm_sum_apply_smul_le`), it fixes `ℙ_k(K̂)`
(`sum_apply_smul_ae_eq_fn_of_mem_polynomialSubmodule`), so
`|v̂ − Π̂ v̂|_{m,K̂} ≤ c inf_{q ∈ ℙ_k} ‖v̂ + q‖_{k+1,K̂}`, and the Bramble–Hilbert estimate
(`SobolevEuclidean.exists_ciInf_norm_add_le_mul_topSeminorm`) bounds the infimum by
`|v̂|_{k+1,K̂}`; the passage between the tensor seminorm and the multi-index seminorm is
`SobolevMultiIndex.sobolevSeminorm_fn_le` and
`SobolevMultiIndex.topSeminorm_le_mul_toReal_sobolevSeminorm`. -/
theorem sobolevSeminorm_sub_nodalInterp_le {Khat : Opens (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsSobolevExtensionDomainAll d Khat)
    (hb : Bornology.IsBounded (Khat : Set (EuclideanSpace ℝ (Fin d))))
    (hc : IsPreconnected (Khat : Set (EuclideanSpace ℝ (Fin d))))
    {k m : ℕ} (hm : m ≤ k + 1) (hkd : (d : ℝ) / 2 < k + 1)
    {I : ℕ} (xhat : Fin I → EuclideanSpace ℝ (Fin d))
    (φhat : Fin I → EuclideanSpace ℝ (Fin d) → ℝ)
    (hx : ∀ i, xhat i ∈ closure (Khat : Set (EuclideanSpace ℝ (Fin d))))
    (hφ : ∀ i, MemSobolev (φhat i) m 2 Khat volume)
    (hP : ∀ q : MvPolynomial (Fin d) ℝ, q.totalDegree ≤ k →
      ∀ x ∈ Khat, Approximation.nodalInterp xhat φhat
        (fun y ↦ MvPolynomial.eval (fun i ↦ y i) q) x = MvPolynomial.eval (fun i ↦ x i) q) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ v : EuclideanSpace ℝ (Fin d) → ℝ, MemSobolev v (k + 1) 2 Khat volume →
      ContinuousOn v (closure (Khat : Set (EuclideanSpace ℝ (Fin d)))) →
      sobolevSeminorm (v - Approximation.nodalInterp xhat φhat v) m 2 Khat volume
        ≤ ENNReal.ofReal c * sobolevSeminorm v (k + 1) 2 Khat volume := by
  classical
  -- the exponent in the backbone's form, `2 = ((2 : ℝ≥0) : ℝ≥0∞)` definitionally
  replace hφ : ∀ i, MemSobolev (φhat i) m 𝟚 Khat volume := hφ
  have : CompactSpace (closure (Khat : Set (EuclideanSpace ℝ (Fin d)))) :=
    isCompact_iff_compactSpace.1 hb.isCompact_closure
  -- the embedding `H^{k+1}(K̂) ↪ C(K̂̄)`
  have hkd' : (d : ℝ) / ((2 : ℝ≥0) : ℝ) < ((k + 1 : ℕ) : ℝ) := by
    rw [NNReal.coe_ofNat]
    push_cast
    exact hkd
  have hemb := SobolevEuclidean.exists_isCompactEmbedding_toContinuousMap_of_order (N := d) k hΩ
    (Or.inr (by norm_num)) hkd' (K := closure (Khat : Set (EuclideanSpace ℝ (Fin d))))
    subset_closure
  obtain ⟨ι, hι, -⟩ := hemb
  -- Bramble–Hilbert: the quotient norm is bounded by the top seminorm
  have hBH := SobolevEuclidean.exists_ciInf_norm_add_le_mul_topSeminorm (N := d) (k := k)
    (p := 2) (hΩ _) hb hc
  obtain ⟨C₁, hC₁, hBH⟩ := hBH
  -- the constants
  obtain ⟨Cm, hCm⟩ : ∃ Cm : ℝ, Cm = ∑ m' : Fin m → Fin d,
      ‖basisCoordProd (EuclideanSpace.basisFun (Fin d) ℝ).toBasis m'‖ := ⟨_, rfl⟩
  obtain ⟨Ck, hCk⟩ : ∃ Ck : ℝ, Ck = ∑ α : MultiIndexEq (Fin d) (k + 1), ∏ j,
      ‖multiIndexTuple ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis :
        Fin d → EuclideanSpace ℝ (Fin d)) α.1.1 j‖ := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ i, (sobolevSeminorm (φhat i) m 𝟚 Khat volume).toReal :=
    ⟨_, rfl⟩
  have hCm0 : 0 ≤ Cm := by rw [hCm]; positivity
  have hCk0 : 0 ≤ Ck := by rw [hCk]; positivity
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hA0 : 0 ≤ Cm + ‖ι‖ * S := add_nonneg hCm0 (mul_nonneg (norm_nonneg _) hS0)
  have hc0 : 0 ≤ (Cm + ‖ι‖ * S) * C₁ * Ck := mul_nonneg (mul_nonneg hA0 hC₁.le) hCk0
  refine ⟨(Cm + ‖ι‖ * S) * C₁ * Ck, hc0, fun v hv hvc ↦ ?_⟩
  replace hv : MemSobolev v (k + 1) 𝟚 Khat volume := hv
  suffices key : sobolevSeminorm (v - Approximation.nodalInterp xhat φhat v) m 𝟚 Khat volume
      ≤ ENNReal.ofReal ((Cm + ‖ι‖ * S) * C₁ * Ck) * sobolevSeminorm v (k + 1) 𝟚 Khat volume from
    key
  -- the typed element of `H^{k+1}(K̂)` carrying `v`
  have hv' : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin d) ℝ).toBasis v (k + 1) 𝟚 Khat
      volume := hv.memSobolevMultiIndex
  have hu := hv'.exists_sobolevMultiIndex
  obtain ⟨u, hu⟩ := hu
  -- its continuous representative is `v` on the closure
  have hrep := hι u
  obtain ⟨ut, hutc, hutae, hutι⟩ := hrep
  have hvut : EqOn v ut (closure (Khat : Set (EuclideanSpace ℝ (Fin d)))) :=
    hvc.eqOn_closure_of_ae_eq Khat.isOpen hutc.continuousOn (hu.symm.trans hutae)
  have hnode : ∀ i, v (xhat i) = ι u ⟨xhat i, hx i⟩ := fun i ↦ by rw [hvut (hx i), hutι]
  -- the interpolation operator on the typed space
  obtain ⟨Ip, hIp⟩ : ∃ Ip : SobolevEuclidean d (k + 1) 𝟚 Khat → EuclideanSpace ℝ (Fin d) → ℝ,
      ∀ w, Ip w = ∑ i, (ι w ⟨xhat i, hx i⟩) • φhat i := ⟨_, fun _ ↦ rfl⟩
  have hIpu : Approximation.nodalInterp xhat φhat v = Ip u := by
    rw [Approximation.nodalInterp_eq_sum_smul, hIp]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hnode i]
  have hIpadd : ∀ w₁ w₂, Ip (w₁ + w₂) = Ip w₁ + Ip w₂ := fun w₁ w₂ ↦ by
    rw [hIp, hIp, hIp, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [map_add, ContinuousMap.add_apply, add_smul]
  have hIpmem : ∀ w, MemSobolev (Ip w) m 𝟚 Khat volume := fun w ↦ by
    rw [hIp]
    exact MemSobolev.finsetSum fun i _ ↦ (hφ i).const_smul _
  have hIpbound : ∀ w, sobolevSeminorm (Ip w) m 𝟚 Khat volume
      ≤ ENNReal.ofReal (‖ι‖ * ‖w‖ * S) := fun w ↦ by
    rw [hIp, hS]
    exact sobolevSeminorm_sum_apply_smul_le ι (fun i ↦ ⟨xhat i, hx i⟩) (by norm_num) hφ w
  -- the estimate against `‖u + q‖` for every `q ∈ ℙ_k(K̂)`
  have hvm : MemSobolev v m 𝟚 Khat volume := hv.mono_order (by exact_mod_cast hm)
  have hmain : ∀ q : SobolevEuclidean.polynomialSubmodule (k := k) (p := 𝟚) hb,
      (sobolevSeminorm (v - Approximation.nodalInterp xhat φhat v) m 𝟚 Khat volume).toReal
        ≤ (Cm + ‖ι‖ * S) * ‖u + q.1‖ := by
    intro q
    have hfnq : MemSobolev (SobolevMultiIndex.fn q.1) (k + 1) 𝟚 Khat volume :=
      SobolevMultiIndex.memSobolev_fn q.1
    have hpoly := sum_apply_smul_ae_eq_fn_of_mem_polynomialSubmodule hb ι hι xhat φhat hx hx hP
      q.2
    rw [← hIp] at hpoly
    have hae : v - Approximation.nodalInterp xhat φhat v
        =ᵐ[volume.restrict (Khat : Set (EuclideanSpace ℝ (Fin d)))]
          (v + SobolevMultiIndex.fn q.1) - Ip (u + q.1) := by
      rw [hIpu, hIpadd]
      filter_upwards [hpoly] with x hx'
      simp only [Pi.sub_apply, Pi.add_apply, hx']
      ring
    rw [sobolevSeminorm_congr_ae hae]
    have h1 : sobolevSeminorm ((v + SobolevMultiIndex.fn q.1) - Ip (u + q.1)) m 𝟚 Khat volume
        ≤ sobolevSeminorm (v + SobolevMultiIndex.fn q.1) m 𝟚 Khat volume
          + sobolevSeminorm (Ip (u + q.1)) m 𝟚 Khat volume :=
      sobolevSeminorm_sub_le (by norm_num) (hvm.add (hfnq.mono_order (by exact_mod_cast hm)))
        (hIpmem _)
    have h2 : sobolevSeminorm (v + SobolevMultiIndex.fn q.1) m 𝟚 Khat volume
        ≤ ENNReal.ofReal (Cm * ‖u + q.1‖) := by
      have hae2 : v + SobolevMultiIndex.fn q.1
          =ᵐ[volume.restrict (Khat : Set (EuclideanSpace ℝ (Fin d)))]
            SobolevMultiIndex.fn (u + q.1) := by
        filter_upwards [hu, SobolevMultiIndex.fn_add u q.1] with x h1 h2
        rw [h2]
        change v x + _ = SobolevMultiIndex.fn u x + _
        rw [h1]
      rw [sobolevSeminorm_congr_ae hae2, ENNReal.ofReal_mul hCm0, hCm]
      exact SobolevMultiIndex.sobolevSeminorm_fn_le (u + q.1) hm
    have h3 := hIpbound (u + q.1)
    have htot : sobolevSeminorm ((v + SobolevMultiIndex.fn q.1) - Ip (u + q.1)) m 𝟚 Khat volume
        ≤ ENNReal.ofReal ((Cm + ‖ι‖ * S) * ‖u + q.1‖) := by
      refine h1.trans ((add_le_add h2 h3).trans (le_of_eq ?_))
      rw [← ENNReal.ofReal_add (mul_nonneg hCm0 (norm_nonneg _))
        (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hS0)]
      congr 1
      ring
    exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hA0 (norm_nonneg _)) htot
  -- pass to the infimum, apply Bramble–Hilbert and compare the seminorms
  have hinf : (sobolevSeminorm (v - Approximation.nodalInterp xhat φhat v) m 𝟚 Khat volume).toReal
      ≤ (Cm + ‖ι‖ * S) * ⨅ q : SobolevEuclidean.polynomialSubmodule (k := k) (p := 𝟚) hb,
        ‖u + q‖ := by
    rw [Real.mul_iInf_of_nonneg hA0]
    exact le_ciInf hmain
  have hBHu := hBH u
  have hcmp := SobolevMultiIndex.topSeminorm_le_mul_toReal_sobolevSeminorm u
  rw [← hCk] at hcmp
  have hsv : sobolevSeminorm v (k + 1) 𝟚 Khat volume
      = sobolevSeminorm (SobolevMultiIndex.fn u) (k + 1) 𝟚 Khat volume :=
    sobolevSeminorm_congr_ae hu.symm
  have hfinal : (sobolevSeminorm (v - Approximation.nodalInterp xhat φhat v) m 𝟚 Khat
      volume).toReal
        ≤ (Cm + ‖ι‖ * S) * C₁ * Ck * (sobolevSeminorm v (k + 1) 𝟚 Khat volume).toReal := by
    rw [hsv]
    refine hinf.trans ?_
    refine (mul_le_mul_of_nonneg_left hBHu hA0).trans ?_
    refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcmp hC₁.le) hA0).trans
      (le_of_eq ?_)
    ring
  have hlhs : sobolevSeminorm (v - Approximation.nodalInterp xhat φhat v) m 𝟚 Khat volume ≠ ⊤ :=
    (hvm.sub (memSobolev_nodalInterp hφ v)).sobolevSeminorm_ne_top
  calc sobolevSeminorm (v - Approximation.nodalInterp xhat φhat v) m 𝟚 Khat volume
      = ENNReal.ofReal (sobolevSeminorm (v - Approximation.nodalInterp xhat φhat v) m 𝟚 Khat
          volume).toReal := (ENNReal.ofReal_toReal hlhs).symm
    _ ≤ ENNReal.ofReal ((Cm + ‖ι‖ * S) * C₁ * Ck
          * (sobolevSeminorm v (k + 1) 𝟚 Khat volume).toReal) := ENNReal.ofReal_le_ofReal hfinal
    _ = ENNReal.ofReal ((Cm + ‖ι‖ * S) * C₁ * Ck) * sobolevSeminorm v (k + 1) 𝟚 Khat volume := by
          rw [ENNReal.ofReal_mul hc0, ENNReal.ofReal_toReal hv.sobolevSeminorm_ne_top]

/-! ### Affine maps between elements -/

/-- **The operator norms of an affine map between elements** ([han2009theoretical] Lemma 10.2.2):
if `F x̂ = T x̂ + b` carries `K̂` onto `K`, both bounded, and balls of diameters `ρ̂` and `ρ_K` lie
in `K̂` and `K`, then `‖T‖ ≤ h_K / ρ̂` and `‖T⁻¹‖ ≤ ĥ / ρ_K`:
`ContinuousLinearMap.opNorm_le_diam_div` for `F` and for `F⁻¹ y = T⁻¹ y − T⁻¹ b`. -/
theorem opNorm_le_diam_div_of_image {Khat K : Set 𝔼} {T : 𝔼 ≃L[ℝ] 𝔼} {b chat c : 𝔼}
    {ρhat ρK : ℝ} (hρhat : 0 < ρhat) (hρK : 0 < ρK) (hKhatb : Bornology.IsBounded Khat)
    (hKb : Bornology.IsBounded K) (hballhat : closedBall chat (ρhat / 2) ⊆ Khat)
    (hballK : closedBall c (ρK / 2) ⊆ K) (hF : (fun x ↦ T x + b) '' Khat = K) :
    ‖(T : 𝔼 →L[ℝ] 𝔼)‖ ≤ diam K / ρhat ∧ ‖(T.symm : 𝔼 →L[ℝ] 𝔼)‖ ≤ diam Khat / ρK := by
  constructor
  · have h := ContinuousLinearMap.opNorm_le_diam_div (T : 𝔼 →L[ℝ] 𝔼) (b := b) (S := Khat)
      (D := K) (by positivity) hKb hballhat (fun x hx ↦ hF ▸ Set.mem_image_of_mem _ hx)
    rwa [show 2 * (ρhat / 2) = ρhat by ring] at h
  · have hmaps : ∀ y ∈ K, (T.symm : 𝔼 →L[ℝ] 𝔼) y + (-T.symm b) ∈ Khat := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ : ∃ x ∈ Khat, T x + b = y := by
        rw [← hF] at hy
        obtain ⟨x, hx, hxy⟩ := hy
        exact ⟨x, hx, hxy⟩
      have : (T.symm : 𝔼 →L[ℝ] 𝔼) (T x + b) + (-T.symm b) = x := by
        simp [ContinuousLinearEquiv.coe_coe, map_add]
      rw [this]
      exact hx
    have h := ContinuousLinearMap.opNorm_le_diam_div (T.symm : 𝔼 →L[ℝ] 𝔼) (b := -T.symm b)
      (S := K) (D := Khat) (by positivity) hKhatb hballK hmaps
    rwa [show 2 * (ρK / 2) = ρK by ring] at h


/-- The inverse of the affine map `F x = T x + b` is a left inverse. -/
theorem affine_leftInverse (T : 𝔼 ≃L[ℝ] 𝔼) (b : 𝔼) :
    Function.LeftInverse (fun y ↦ T.symm (y - b)) (fun x ↦ T x + b) := fun x ↦ by simp

/-! ### The local estimate on an affine image -/

/-- **The local interpolation error** ([han2009theoretical] Theorem 10.3.5, (10.3.7)). Under the
hypotheses of `sobolevSeminorm_sub_nodalInterp_le` on the reference element `K̂`, which also
contains a ball of diameter `ρ̂`, there is a constant `c`, depending only on `K̂` and `Π̂`, such
that for every element `K = F_K(K̂)`, `F_K x̂ = T_K x̂ + b_K`, containing a ball of diameter `ρ_K`,
the interpolation operator `Π_K` — nodes `F_K(x̂ᵢ)`, shape functions `φ̂ᵢ ∘ F_K⁻¹` — satisfies

  `|v − Π_K v|_{m,K} ≤ c h_K^{k+1} ρ_K^{−m} |v|_{k+1,K}`  for every `v ∈ H^{k+1}(K)`,

with `h_K = diam K`. Nodal interpolation commutes with `F_K` (`Approximation.nodalInterp_comp`),
so `(v − Π_K v) ∘ F_K = v̂ − Π̂ v̂`; the affine change of variables
(`sobolevSeminorm_le_comp_affine_of_image`) transports the left-hand side to `K̂`, the reference
estimate bounds it there by `|v̂|_{k+1,K̂}`, `sobolevSeminorm_comp_affine_le_of_image` brings that
back to `K`, and `opNorm_le_diam_div_of_image` bounds `‖T_K‖ ≤ h_K/ρ̂` and `‖T_K⁻¹‖ ≤ ĥ/ρ_K`; the
constant is `c = c₀ ĥ^m / ρ̂^{k+1}`. -/
theorem sobolevSeminorm_sub_nodalInterp_comp_affine_le {Khat : Opens 𝔼}
    (hΩ : IsSobolevExtensionDomainAll d Khat)
    (hb : Bornology.IsBounded (Khat : Set 𝔼)) (hc : IsPreconnected (Khat : Set 𝔼))
    {chat : 𝔼} {ρhat : ℝ} (hρhat : 0 < ρhat)
    (hballhat : Metric.closedBall chat (ρhat / 2) ⊆ Khat)
    {k m : ℕ} (hm : m ≤ k + 1) (hkd : (d : ℝ) / 2 < k + 1)
    {I : ℕ} (xhat : Fin I → 𝔼) (φhat : Fin I → 𝔼 → ℝ)
    (hx : ∀ i, xhat i ∈ closure (Khat : Set 𝔼))
    (hφ : ∀ i, MemSobolev (φhat i) m 2 Khat volume)
    (hP : ∀ q : MvPolynomial (Fin d) ℝ, q.totalDegree ≤ k →
      ∀ x ∈ Khat, Approximation.nodalInterp xhat φhat
        (fun y ↦ MvPolynomial.eval (fun i ↦ y i) q) x = MvPolynomial.eval (fun i ↦ x i) q) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (T : 𝔼 ≃L[ℝ] 𝔼) (b : 𝔼) (K : Opens 𝔼),
      (fun x ↦ T x + b) '' Khat = K →
      ∀ {cK : 𝔼} {ρK : ℝ}, 0 < ρK → Metric.closedBall cK (ρK / 2) ⊆ K →
      ∀ v : 𝔼 → ℝ, MemSobolev v (k + 1) 2 K volume → ContinuousOn v (closure (K : Set 𝔼)) →
      sobolevSeminorm (v - Approximation.nodalInterp ((fun x ↦ T x + b) ∘ xhat)
          (fun i ↦ φhat i ∘ fun y ↦ T.symm (y - b)) v) m 2 K volume
        ≤ ENNReal.ofReal (c * Metric.diam (K : Set 𝔼) ^ (k + 1) / ρK ^ m)
          * sobolevSeminorm v (k + 1) 2 K volume := by
  obtain ⟨c₀, hc₀0, hc₀⟩ := sobolevSeminorm_sub_nodalInterp_le hΩ hb hc hm hkd xhat φhat hx hφ hP
  refine ⟨c₀ * Metric.diam (Khat : Set 𝔼) ^ m / ρhat ^ (k + 1), by positivity, ?_⟩
  intro T b K hK cK ρK hρK hballK v hv hvc
  have hKb : Bornology.IsBounded (K : Set 𝔼) := hK ▸ isBounded_image_affine T b hb
  -- the operator norms of `T` and `T⁻¹`
  obtain ⟨hT, hT'⟩ := opNorm_le_diam_div_of_image hρhat hρK hb hKb hballhat hballK hK
  -- the change of variables `F_K`
  have hKhat : Khat = affinePreimage T b K := (affinePreimage_eq_of_image_eq T b hK).symm
  have hG : Function.LeftInverse (fun y ↦ T.symm (y - b)) (fun x ↦ T x + b) :=
    affine_leftInverse T b
  -- the transported shape functions lie in `H^m(K)`
  have hφK : ∀ i, MemSobolev (φhat i ∘ fun y ↦ T.symm (y - b)) m 2 K volume := fun i ↦
    memSobolev_comp_affine_inv T b hK (hφ i)
  -- `w = v − Π_K v` and its transport `w ∘ F_K = v̂ − Π̂ v̂`
  obtain ⟨w, hw⟩ : ∃ w : 𝔼 → ℝ, w = v - Approximation.nodalInterp ((fun x ↦ T x + b) ∘ xhat)
      (fun i ↦ φhat i ∘ fun y ↦ T.symm (y - b)) v := ⟨_, rfl⟩
  have hwmem : MemSobolev w m 2 K volume := by
    rw [hw]
    exact (hv.mono_order (by exact_mod_cast hm)).sub (memSobolev_nodalInterp hφK v)
  have hwF : (fun x ↦ w (T x + b))
      = (fun x ↦ v (T x + b)) - Approximation.nodalInterp xhat φhat (fun x ↦ v (T x + b)) := by
    funext x
    have h := congrFun (Approximation.nodalInterp_comp xhat φhat v hG) x
    change w (T x + b)
      = v (T x + b) - Approximation.nodalInterp xhat φhat (v ∘ fun x ↦ T x + b) x
    rw [← h, hw]
    rfl
  rw [← hw]
  -- back to `K̂`, the estimate there, and forth to `K` at order `k + 1`
  have h6 := sobolevSeminorm_le_comp_affine_of_image T b hK hwmem
  have hvF : MemSobolev (fun x ↦ v (T x + b)) (k + 1) 2 Khat volume := by
    rw [hKhat]
    exact memSobolev_comp_affine T b hv
  have hvFc : ContinuousOn (fun x ↦ v (T x + b)) (closure (Khat : Set 𝔼)) := by
    rw [hKhat]
    exact hvc.comp_affine_closure T b
  have h3 := hc₀ _ hvF hvFc
  rw [← hwF] at h3
  have h5 := sobolevSeminorm_comp_affine_le_of_image T b hK hv
  -- assemble the constants
  have hdet : |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (1 / 2 : ℝ)
      * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (-(1 / 2 : ℝ)) = 1 :=
    abs_det_rpow_half_mul_rpow_neg_half T
  have hA0 : 0 ≤ ‖(T.symm : 𝔼 →L[ℝ] 𝔼)‖ ^ m * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (1 / 2 : ℝ) := by
    positivity
  have hB0 : 0 ≤ ‖(T : 𝔼 →L[ℝ] 𝔼)‖ ^ (k + 1)
      * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (-(1 / 2 : ℝ)) := by
    positivity
  have hreal : ‖(T.symm : 𝔼 →L[ℝ] 𝔼)‖ ^ m * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (1 / 2 : ℝ)
      * (c₀ * (‖(T : 𝔼 →L[ℝ] 𝔼)‖ ^ (k + 1) * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (-(1 / 2 : ℝ))))
      ≤ c₀ * Metric.diam (Khat : Set 𝔼) ^ m / ρhat ^ (k + 1) * Metric.diam (K : Set 𝔼) ^ (k + 1)
        / ρK ^ m := by
    have e : ‖(T.symm : 𝔼 →L[ℝ] 𝔼)‖ ^ m * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (1 / 2 : ℝ)
        * (c₀ * (‖(T : 𝔼 →L[ℝ] 𝔼)‖ ^ (k + 1) * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (-(1 / 2 : ℝ))))
        = c₀ * ‖(T.symm : 𝔼 →L[ℝ] 𝔼)‖ ^ m * ‖(T : 𝔼 →L[ℝ] 𝔼)‖ ^ (k + 1)
          * (|LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (1 / 2 : ℝ)
            * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (-(1 / 2 : ℝ))) := by ring
    rw [e, hdet, mul_one]
    have h1 : ‖(T.symm : 𝔼 →L[ℝ] 𝔼)‖ ^ m ≤ (Metric.diam (Khat : Set 𝔼) / ρK) ^ m :=
      pow_le_pow_left₀ (norm_nonneg _) hT' m
    have h2 : ‖(T : 𝔼 →L[ℝ] 𝔼)‖ ^ (k + 1) ≤ (Metric.diam (K : Set 𝔼) / ρhat) ^ (k + 1) :=
      pow_le_pow_left₀ (norm_nonneg _) hT (k + 1)
    calc c₀ * ‖(T.symm : 𝔼 →L[ℝ] 𝔼)‖ ^ m * ‖(T : 𝔼 →L[ℝ] 𝔼)‖ ^ (k + 1)
        ≤ c₀ * (Metric.diam (Khat : Set 𝔼) / ρK) ^ m
            * (Metric.diam (K : Set 𝔼) / ρhat) ^ (k + 1) := by
          gcongr
      _ = c₀ * Metric.diam (Khat : Set 𝔼) ^ m / ρhat ^ (k + 1) * Metric.diam (K : Set 𝔼) ^ (k + 1)
            / ρK ^ m := by
          rw [div_pow, div_pow]
          field_simp
  calc sobolevSeminorm w m 2 K volume
      ≤ ENNReal.ofReal (‖(T.symm : 𝔼 →L[ℝ] 𝔼)‖ ^ m * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (1 / 2 : ℝ))
          * (ENNReal.ofReal c₀ * (ENNReal.ofReal (‖(T : 𝔼 →L[ℝ] 𝔼)‖ ^ (k + 1)
            * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (-(1 / 2 : ℝ)))
            * sobolevSeminorm v (k + 1) 2 K volume)) := by
        refine h6.trans ?_
        gcongr
        exact h3.trans (by gcongr)
    _ = ENNReal.ofReal (‖(T.symm : 𝔼 →L[ℝ] 𝔼)‖ ^ m * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (1 / 2 : ℝ)
          * (c₀ * (‖(T : 𝔼 →L[ℝ] 𝔼)‖ ^ (k + 1) * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (-(1 / 2 : ℝ)))))
          * sobolevSeminorm v (k + 1) 2 K volume := by
        rw [ENNReal.ofReal_mul hA0, ENNReal.ofReal_mul hc₀0, mul_assoc, mul_assoc]
    _ ≤ _ := by gcongr

/-- The arithmetic of the estimate on a regular family: for `0 ≤ h ≤ σ ρ`, `ρ > 0` and `h ≤ H`,
and orders
`j ≤ m ≤ k + 1`, `h^{k+1} / ρ^j ≤ σ^j H^{m−j} h^{k+1−m}`. -/
theorem pow_div_pow_le_of_le_mul {h ρ σ H : ℝ} (hh : 0 ≤ h) (hρ : 0 < ρ) (hσ : 0 ≤ σ)
    (hhσ : h ≤ σ * ρ) (hhH : h ≤ H) {j m k : ℕ} (hjm : j ≤ m) (hmk : m ≤ k + 1) :
    h ^ (k + 1) / ρ ^ j ≤ σ ^ j * H ^ (m - j) * h ^ (k + 1 - m) := by
  obtain ⟨a, rfl⟩ : ∃ a, m = j + a := ⟨m - j, by omega⟩
  obtain ⟨e, he⟩ : ∃ e, k + 1 = j + a + e := ⟨k + 1 - (j + a), by omega⟩
  rw [he, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left, pow_add, pow_add,
    div_le_iff₀ (by positivity)]
  have h1 : h ^ j ≤ (σ * ρ) ^ j := pow_le_pow_left₀ hh hhσ j
  have h2 : h ^ a ≤ H ^ a := pow_le_pow_left₀ hh hhH a
  calc h ^ j * h ^ a * h ^ e ≤ (σ * ρ) ^ j * H ^ a * h ^ e := by gcongr
    _ = σ ^ j * H ^ a * h ^ e * ρ ^ j := by ring

/-! ### Regular families -/

/-- **A regular family of partitions** ([han2009theoretical] Definition 10.3.6): a family `T i` of
collections of elements, indexed along a filter `l`, such that

* (a) there is a `σ` with `h_K / ρ_K ≤ σ` for every element `K` of every member of the family, and
* (b) the mesh parameter `h = sup_{K ∈ T i} h_K` tends to `0` along `l`.

Here `h_K = diam K` and `ρ_K` is the diameter of a ball inscribed in `K`: condition (a) is written
as the existence of an inscribed ball of radius `r` with `h_K ≤ σ (2 r)`, which is the inequality
`h_K ≤ σ ρ_K` for the largest inscribed ball whenever that exists. Regularity is what turns the
element-wise estimate `sobolevSeminorm_sub_nodalInterp_comp_affine_le`, whose right-hand side
carries both `h_K` and `ρ_K`, into a bound in `h_K` alone
(`sobolevNorm_sub_nodalInterp_comp_affine_le`). -/
def IsRegularFamily {E ι : Type*} [PseudoMetricSpace E] (l : Filter ι) (T : ι → Set (Set E)) :
    Prop :=
  (∃ σ : ℝ, ∀ i, ∀ K ∈ T i, ∃ (c : E) (r : ℝ),
      0 < r ∧ closedBall c r ⊆ K ∧ diam K ≤ σ * (2 * r)) ∧
    Tendsto (fun i ↦ sSup (diam '' T i)) l (𝓝 0)

/-- **The interpolation error on a regular family** ([han2009theoretical] Corollary 10.3.7,
(10.3.10)). Under the hypotheses of `sobolevSeminorm_sub_nodalInterp_comp_affine_le` on the
reference element `K̂`, let `{𝒯_h}` be a regular family of partitions (`IsRegularFamily`) whose
elements have diameter at most `H`. Then there is a constant `c` such that for every element `K`
of every `𝒯_h`, read as the open set `K` which is the affine image `F_K(K̂)` of the reference
element,

  `‖v − Π_K v‖_{m,K} ≤ c h_K^{k+1−m} |v|_{k+1,K}`  for every `v ∈ H^{k+1}(K)`.

Regularity gives `ρ_K ≥ h_K/σ`, which turns the `h_K^{k+1} ρ_K^{−m}` of the local estimate into
`σ^m h_K^{k+1−m}`; the norm `‖·‖_{m,K}` is at most the sum of the seminorms of orders `j ≤ m`
(`MemSobolev.sobolevNorm_le_sum_sobolevSeminorm`), each bounded by the local estimate at order `j`
with `h_K^{k+1−j} = h_K^{m−j} h_K^{k+1−m} ≤ H^{m−j} h_K^{k+1−m}`. The bound `h_K ≤ H`, which the
book leaves implicit, enters the constant through the lower-order seminorms. -/
theorem sobolevNorm_sub_nodalInterp_comp_affine_le {Khat : Opens 𝔼}
    (hΩ : IsSobolevExtensionDomainAll d Khat)
    (hb : Bornology.IsBounded (Khat : Set 𝔼)) (hc : IsPreconnected (Khat : Set 𝔼))
    {chat : 𝔼} {ρhat : ℝ} (hρhat : 0 < ρhat)
    (hballhat : Metric.closedBall chat (ρhat / 2) ⊆ Khat)
    {k m : ℕ} (hm : m ≤ k + 1) (hkd : (d : ℝ) / 2 < k + 1)
    {I : ℕ} (xhat : Fin I → 𝔼) (φhat : Fin I → 𝔼 → ℝ)
    (hx : ∀ i, xhat i ∈ closure (Khat : Set 𝔼))
    (hφ : ∀ i, MemSobolev (φhat i) m 2 Khat volume)
    (hP : ∀ q : MvPolynomial (Fin d) ℝ, q.totalDegree ≤ k →
      ∀ x ∈ Khat, Approximation.nodalInterp xhat φhat
        (fun y ↦ MvPolynomial.eval (fun i ↦ y i) q) x = MvPolynomial.eval (fun i ↦ x i) q)
    {ι : Type*} {l : Filter ι} {𝒯 : ι → Set (Set 𝔼)} (hreg : IsRegularFamily l 𝒯)
    {H : ℝ} (hH : ∀ i, ∀ K ∈ 𝒯 i, Metric.diam K ≤ H) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ i, ∀ K ∈ 𝒯 i, ∀ Kop : Opens 𝔼, (Kop : Set 𝔼) = K →
      ∀ (T : 𝔼 ≃L[ℝ] 𝔼) (b : 𝔼), (fun x ↦ T x + b) '' Khat = Kop →
      ∀ v : 𝔼 → ℝ, MemSobolev v (k + 1) 2 Kop volume → ContinuousOn v (closure (Kop : Set 𝔼)) →
      sobolevNorm (v - Approximation.nodalInterp ((fun x ↦ T x + b) ∘ xhat)
          (fun i ↦ φhat i ∘ fun y ↦ T.symm (y - b)) v) m 2 Kop volume
        ≤ ENNReal.ofReal (c * Metric.diam K ^ (k + 1 - m))
          * sobolevSeminorm v (k + 1) 2 Kop volume := by
  obtain ⟨σ, hσ⟩ := hreg.1
  -- the local estimate at every order `j ≤ m`
  have h5 : ∀ j : Fin (m + 1), ∃ c : ℝ, 0 ≤ c ∧ ∀ (T : 𝔼 ≃L[ℝ] 𝔼) (b : 𝔼) (K : Opens 𝔼),
      (fun x ↦ T x + b) '' Khat = K →
      ∀ {cK : 𝔼} {ρK : ℝ}, 0 < ρK → Metric.closedBall cK (ρK / 2) ⊆ K →
      ∀ v : 𝔼 → ℝ, MemSobolev v (k + 1) 2 K volume → ContinuousOn v (closure (K : Set 𝔼)) →
      sobolevSeminorm (v - Approximation.nodalInterp ((fun x ↦ T x + b) ∘ xhat)
          (fun i ↦ φhat i ∘ fun y ↦ T.symm (y - b)) v) j 2 K volume
        ≤ ENNReal.ofReal (c * Metric.diam (K : Set 𝔼) ^ (k + 1) / ρK ^ (j : ℕ))
          * sobolevSeminorm v (k + 1) 2 K volume := fun j ↦
    sobolevSeminorm_sub_nodalInterp_comp_affine_le hΩ hb hc hρhat hballhat
      ((Nat.lt_succ_iff.1 j.2).trans hm) hkd xhat φhat hx
      (fun i ↦ (hφ i).mono_order (by exact_mod_cast Nat.lt_succ_iff.1 j.2)) hP
  choose cj hcj0 hcj using h5
  obtain ⟨σ', hσ'⟩ : ∃ σ' : ℝ, σ' = max σ 0 := ⟨_, rfl⟩
  obtain ⟨H', hH'⟩ : ∃ H' : ℝ, H' = max H 0 := ⟨_, rfl⟩
  have hσ'0 : 0 ≤ σ' := hσ' ▸ le_max_right _ _
  have hH'0 : 0 ≤ H' := hH' ▸ le_max_right _ _
  refine ⟨∑ j : Fin (m + 1), cj j * σ' ^ (j : ℕ) * H' ^ (m - j),
    Finset.sum_nonneg fun j _ ↦ mul_nonneg (mul_nonneg (hcj0 j) (by positivity)) (by positivity),
    ?_⟩
  intro i K hK Kop hKop T b hF v hv hvc
  obtain ⟨cK, r, hr, hball, hdiam⟩ := hσ i K hK
  have hball' : Metric.closedBall cK (2 * r / 2) ⊆ Kop := by
    rw [hKop, mul_div_cancel_left₀ _ (two_ne_zero' ℝ)]
    exact hball
  have hdiamK : Metric.diam (Kop : Set 𝔼) = Metric.diam K := by rw [hKop]
  have hw : MemSobolev (v - Approximation.nodalInterp ((fun x ↦ T x + b) ∘ xhat)
      (fun i ↦ φhat i ∘ fun y ↦ T.symm (y - b)) v) m 2 Kop volume :=
    (hv.mono_order (by exact_mod_cast hm)).sub
      (memSobolev_nodalInterp (fun i ↦ memSobolev_comp_affine_inv T b hF (hφ i)) v)
  refine (hw.sobolevNorm_le_sum_sobolevSeminorm (by norm_num)).trans ?_
  -- the real inequality of each order
  have hreal : ∀ j : Fin (m + 1), cj j * Metric.diam (Kop : Set 𝔼) ^ (k + 1) / (2 * r) ^ (j : ℕ)
      ≤ cj j * σ' ^ (j : ℕ) * H' ^ (m - j) * Metric.diam K ^ (k + 1 - m) := by
    intro j
    rw [hdiamK, mul_div_assoc, mul_assoc, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (hcj0 j)
    rw [← mul_assoc]
    refine pow_div_pow_le_of_le_mul Metric.diam_nonneg (by positivity) hσ'0 ?_ ?_
      (Nat.lt_succ_iff.1 j.2) hm
    · exact hdiam.trans (mul_le_mul_of_nonneg_right (hσ' ▸ le_max_left _ _) (by positivity))
    · exact (hH i K hK).trans (hH' ▸ le_max_left _ _)
  calc ∑ j : Fin (m + 1), sobolevSeminorm (v - Approximation.nodalInterp ((fun x ↦ T x + b) ∘ xhat)
        (fun i ↦ φhat i ∘ fun y ↦ T.symm (y - b)) v) j 2 Kop volume
      ≤ ∑ j : Fin (m + 1), ENNReal.ofReal (cj j * σ' ^ (j : ℕ) * H' ^ (m - j)
          * Metric.diam K ^ (k + 1 - m)) * sobolevSeminorm v (k + 1) 2 Kop volume := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        refine (hcj j T b Kop hF (by positivity) hball' v hv hvc).trans ?_
        gcongr
        exact hreal j
    _ = ENNReal.ofReal (∑ j : Fin (m + 1), cj j * σ' ^ (j : ℕ) * H' ^ (m - j)
          * Metric.diam K ^ (k + 1 - m)) * sobolevSeminorm v (k + 1) 2 Kop volume := by
        rw [← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun j _ ↦
          mul_nonneg (mul_nonneg (mul_nonneg (hcj0 j) (by positivity)) (by positivity))
            (by positivity)]
    _ = _ := by rw [Finset.sum_mul]

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

/-- **Regularity of a family of triangulations** ([han2009theoretical] Definition 10.3.6): the
family of element collections `Set.range (𝒯 i).K` is regular exactly when (a) every element of
every triangulation contains a ball of radius `r` with `h_K ≤ σ (2 r)` for one `σ`, and (b) the
mesh parameters `Triangulation.meshSize` tend to `0`. -/
theorem isRegularFamily_range_K_iff {Ω : Opens 𝔼₂} {ι : Type*} (l : Filter ι)
    (𝒯 : ι → Triangulation Ω) :
    IsRegularFamily l (fun i ↦ Set.range (𝒯 i).K) ↔
      (∃ σ : ℝ, ∀ i, ∀ T : (𝒯 i).elems, ∃ (c : 𝔼₂) (r : ℝ), 0 < r ∧
        closedBall c r ⊆ (𝒯 i).K T ∧ diam ((𝒯 i).K T) ≤ σ * (2 * r)) ∧
      Tendsto (fun i ↦ (𝒯 i).meshSize) l (𝓝 0) := by
  simp only [IsRegularFamily, ← Triangulation.meshSize_eq_sSup_image, Set.forall_mem_range]

end FiniteElement

/-! ### The global estimate on a triangulation -/

namespace Triangulation

open EuclideanSpace

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

/-- **The global interpolation error on a regular family of triangulations**
([han2009theoretical] Theorem 10.3.9, (10.3.13)). Let `{𝒯_h}` be a family of triangulations of a
plane domain `Ω`, regular (`FiniteElement.IsRegularFamily`) with mesh parameters at most `H`, and
let the reference element be the reference triangle with nodes `x̂ᵢ ∈ K̂̄`, `C¹` shape functions
`φ̂ᵢ` and the polynomial invariance `ℙ_k(K̂) ⊆ X̂`, `k ≥ 1`, conforming on every triangulation of
the family. Then there is a constant `c`, independent of `h`, such that for every
`v ∈ H^{k+1}(Ω)`, read on its continuous representative up to the boundary, and `m = 0, 1`,

  `‖v − Π_h v‖_{m,Ω} ≤ c h^{k+1−m} |v|_{k+1,Ω}`.

`‖v − Π_h v‖²_{m,Ω} = ∑_K ‖v − Π_K v‖²_{m,K}` (`Triangulation.sobolevNorm_rpow_eq_sum`, which needs
`v − Π_h v ∈ H^m(Ω)`, for `m = 1` the conformity), each term is bounded by
`FiniteElement.sobolevNorm_sub_nodalInterp_comp_affine_le` with `h_K ≤ h`, and
`∑_K |v|²_{k+1,K} = |v|²_{k+1,Ω}`. -/
theorem sobolevNorm_sub_globalInterp_le {k m : ℕ} (hm : m ≤ 1) (hk : 1 ≤ k)
    {I : ℕ} (xhat : Fin I → 𝔼₂) (φhat : Fin I → 𝔼₂ → ℝ)
    (hx : ∀ i, xhat i ∈ closure (referenceTriangle : Set 𝔼₂))
    (hφ : ∀ i, ContDiff ℝ 1 (φhat i))
    (hP : ∀ q : MvPolynomial (Fin 2) ℝ, q.totalDegree ≤ k →
      ∀ x ∈ referenceTriangle, Approximation.nodalInterp xhat φhat
        (fun y ↦ MvPolynomial.eval (fun i ↦ y i) q) x = MvPolynomial.eval (fun i ↦ x i) q)
    {Ω : Opens 𝔼₂} {ι : Type*} {l : Filter ι} {𝒯 : ι → Triangulation Ω}
    (hreg : FiniteElement.IsRegularFamily l fun i ↦ Set.range (𝒯 i).K)
    {H : ℝ} (hH : ∀ i, (𝒯 i).meshSize ≤ H)
    (hconf : ∀ i, (𝒯 i).IsConformingElement xhat φhat) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ i, ∀ v : 𝔼₂ → ℝ, MemSobolev v (k + 1) 2 Ω volume →
      ContinuousOn v (closure (Ω : Set 𝔼₂)) →
      sobolevNorm (v - (𝒯 i).globalInterp xhat φhat v) m 2 Ω volume
        ≤ ENNReal.ofReal (c * (𝒯 i).meshSize ^ (k + 1 - m))
          * sobolevSeminorm v (k + 1) 2 Ω volume := by
  -- the elementwise estimate on the reference triangle
  have hφ1 : ∀ i, MemSobolev (φhat i) m 2 referenceTriangle volume := fun i ↦
    ((hφ i).memSobolev_of_isBounded isBounded_referenceTriangle 2).mono_order
      (by exact_mod_cast hm)
  have hkd : (2 : ℝ) / 2 < k + 1 := by
    norm_num
    exact_mod_cast hk
  have hH' : ∀ i, ∀ K ∈ Set.range (𝒯 i).K, Metric.diam K ≤ H := by
    rintro i _ ⟨T, rfl⟩
    exact ((𝒯 i).diam_le_meshSize T).trans (hH i)
  obtain ⟨c, hc0, hc⟩ := FiniteElement.sobolevNorm_sub_nodalInterp_comp_affine_le (k := k) (m := m)
    isSobolevExtensionDomainAll_referenceTriangle isBounded_referenceTriangle
    convex_referenceTriangle.isPreconnected (by norm_num : (0 : ℝ) < 1 / 4)
    closedBall_subset_referenceTriangle (hm.trans (by omega)) hkd xhat φhat hx hφ1 hP hreg hH'
  refine ⟨c, hc0, fun i v hv hvc ↦ ?_⟩
  -- `v − Π_h v ∈ H^m(Ω)`: the conformity of the element
  have hw : MemSobolev (v - (𝒯 i).globalInterp xhat φhat v) m 2 Ω volume :=
    (hv.mono_order (by exact_mod_cast (show m ≤ k + 1 by omega))).sub
      (((𝒯 i).memSobolev_globalInterp xhat φhat (hconf i) hφ v 2).mono_order
        (by exact_mod_cast hm))
  -- the bound on each element, with `h_K ≤ h`
  have helem : ∀ T : (𝒯 i).elems,
      sobolevNorm (v - (𝒯 i).globalInterp xhat φhat v) m 2 ((𝒯 i).Kopens T) volume
        ≤ ENNReal.ofReal (c * (𝒯 i).meshSize ^ (k + 1 - m))
          * sobolevSeminorm v (k + 1) 2 ((𝒯 i).Kopens T) volume := by
    intro T
    rw [(𝒯 i).sobolevNorm_sub_globalInterp xhat φhat (hconf i) T v m]
    refine (hc i _ ⟨T, rfl⟩ ((𝒯 i).Kopens T) rfl ((𝒯 i).linearPart T) (T.1 0)
      ((𝒯 i).image_referenceTriangle T) v (hv.mono_set ((𝒯 i).Kopens_le T))
      (hvc.mono (closure_mono ((𝒯 i).K_subset T)))).trans ?_
    gcongr
    exact (𝒯 i).diam_le_meshSize T
  -- sum the squares over the elements
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by simp
  have hsum := (𝒯 i).sobolevNorm_rpow_eq_sum (p := 2) (by simp) hw
  have hsum' := (𝒯 i).sobolevSeminorm_rpow_eq_sum (p := 2) (by simp) hv
  rw [h2] at hsum hsum'
  have key : sobolevNorm (v - (𝒯 i).globalInterp xhat φhat v) m 2 Ω volume ^ (2 : ℝ)
      ≤ (ENNReal.ofReal (c * (𝒯 i).meshSize ^ (k + 1 - m))
          * sobolevSeminorm v (k + 1) 2 Ω volume) ^ (2 : ℝ) := by
    rw [hsum, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hsum', Finset.mul_sum]
    refine Finset.sum_le_sum fun T _ ↦ ?_
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    exact ENNReal.rpow_le_rpow (helem T) (by norm_num)
  exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).1 key

end Triangulation

/-! ### The `ℙ_k` Lagrange element -/

namespace LagrangeElement

open EuclideanSpace

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

/-- **The interpolation error of the `ℙ_k` Lagrange element on a regular family of
triangulations** ([han2009theoretical] Theorem 10.3.9, for the affine-equivalent spaces of
piecewise polynomials of degree at most `k`): with mesh parameters at most `H`, the continuous
piecewise-`ℙ_k` interpolant `Π_h v` at the lattice nodes satisfies
`‖v − Π_h v‖_{m,Ω} ≤ c h^{k+1−m} |v|_{k+1,Ω}` for every `v ∈ H^{k+1}(Ω)`, `k ≥ 1`, `m = 0, 1`.
The element is conforming (`isConformingElement`) and reproduces `ℙ_k` (`nodalInterp_eval`). -/
theorem sobolevNorm_sub_globalInterp_le {k m : ℕ} (hm : m ≤ 1) (hk : 1 ≤ k) {Ω : Opens 𝔼₂}
    {ι : Type*} {l : Filter ι} {𝒯 : ι → Triangulation Ω}
    (hreg : FiniteElement.IsRegularFamily l fun i ↦ Set.range (𝒯 i).K)
    {H : ℝ} (hH : ∀ i, (𝒯 i).meshSize ≤ H) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ i, ∀ v : 𝔼₂ → ℝ, MemSobolev v (k + 1) 2 Ω volume →
      ContinuousOn v (closure (Ω : Set 𝔼₂)) →
      sobolevNorm (v - (𝒯 i).globalInterp (node k) (shape k) v) m 2 Ω volume
        ≤ ENNReal.ofReal (c * (𝒯 i).meshSize ^ (k + 1 - m))
          * sobolevSeminorm v (k + 1) 2 Ω volume :=
  Triangulation.sobolevNorm_sub_globalInterp_le hm hk (node k) (shape k) (node_mem_closure hk)
    (fun i ↦ (contDiff_shape k i).of_le (by simp))
    (fun q hq x _ ↦ nodalInterp_eval hk q hq x) hreg hH
    fun i ↦ isConformingElement hk (𝒯 i)

/-- **The `ℙ_k` interpolant of a boundary-vanishing function lies in `V_h`**
(`Triangulation.polySpaceZero`), on a triangulation whose boundary is a union of edges, `k ≥ 1`,
`1 ≤ p < ∞`: the element is conforming, edge unisolvent and polynomial
(`Triangulation.exists_mem_polySpaceZero_globalInterp`). -/
theorem exists_mem_polySpaceZero_globalInterp {k : ℕ} (hk : 0 < k) {Ω : Opens 𝔼₂}
    (𝒯 : Triangulation Ω) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hedge : 𝒯.FrontierSubsetEdges)
    {v : 𝔼₂ → ℝ} (hv0 : EqOn v 0 (frontier (Ω : Set 𝔼₂))) :
    ∃ w ∈ 𝒯.polySpaceZero p k, SobolevMultiIndex.fn (w : SobolevEuclidean 2 1 p Ω)
      =ᵐ[volume.restrict (Ω : Set 𝔼₂)] 𝒯.globalInterp (node k) (shape k) v :=
  𝒯.exists_mem_polySpaceZero_globalInterp p hp (isConformingElement hk 𝒯)
    (fun i ↦ (contDiff_shape k i).continuous) (isEdgeUnisolvent hk) (shape_eq_eval k) hedge hv0

/-- **The space `V_h` of continuous piecewise-`ℙ_k` functions vanishing on `∂Ω` is
finite-dimensional**, `k ≥ 1`: its elements are determined by their values at the nodes of the
`ℙ_k` Lagrange element (`Triangulation.finiteDimensional_polySpaceZero`). -/
theorem finiteDimensional_polySpaceZero {k : ℕ} (hk : 0 < k) {Ω : Opens 𝔼₂}
    (𝒯 : Triangulation Ω) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    FiniteDimensional ℝ (𝒯.polySpaceZero p k) :=
  𝒯.finiteDimensional_polySpaceZero p (isConformingElement hk 𝒯) (node_mem_closure hk)
    (nodalInterp_eval hk)

end LagrangeElement

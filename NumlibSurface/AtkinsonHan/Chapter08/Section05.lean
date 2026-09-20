import Numlib.Analysis.Sobolev.Korn
import NumlibSurface.AtkinsonHan.Chapter08.Section03

/-!
# Atkinson–Han §8.5: a boundary value problem of linearized elasticity

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §8.5.

The section sets up the linearized elasticity problem `−div σ = f` in `Ω`, `σ = C ε(u)`,
`ε(u) = ½ (∇u + (∇u)ᵀ)` (8.5.1)–(8.5.5), with the displacement `u = 0` on `Γ_D` and the traction
`σ ν = g` on `Γ_N`, and proves (Theorem 8.5.1, left to Exercise 8.5.3) that its weak formulation
(8.5.15) on `V = {v ∈ [H¹(Ω)]^d : v = 0 on Γ_D}` has a unique solution, which is the minimizer
of the energy (8.5.17), the `V`-ellipticity of the form coming from Korn's inequality.

## What is formalized

**The pure displacement case `Γ_D = Γ`**, `g` absent, on a bounded open `Ω ⊆ B(0, R) ⊆ ℝ^{d+1}`
(the book writes `ℝ^d`; the dimension is `d + 1` because the backbone's Poincaré inequality is).
Then `V = [H¹₀(Ω)]^{d+1}` is the backbone's `SobolevEuclideanZeroVec (d + 1) Ω`
(`Numlib/Analysis/Sobolev/Korn.lean`), the strain `ε(v)_{ij}` is
`SobolevEuclideanZeroVec.strainL i j v ∈ L²(Ω)`, and Korn's inequality is the *first* Korn
inequality `∫_Ω |∇v|² ≤ 2 ∫_Ω |ε(v)|²` on `[H¹₀(Ω)]^{d+1}` (`SobolevEuclideanZeroVec.korn_first`,
the identity `∫ |ε(v)|² = ½ ∫ |∇v|² + ½ ∫ (div v)²` by two integrations by parts and density),
which needs no regularity of `Ω` at all. The elasticity tensor `C_ijkl ∈ L^∞(Ω)` (8.5.6) enters
as `L^∞` classes, its symmetry (8.5.7) and pointwise stability (8.5.8) as `IsElasticityTensor`.

* `elasticityForm Ω C` is the bilinear form `a(u, v) = ∫_Ω [C ε(u)] : ε(v)` on `V`, bounded
  (`elasticityForm_isBoundedWith`), symmetric (`elasticityForm_isHermitian`, from
  `C_ijkl = C_klij`) and `V`-elliptic (`elasticityForm_isCoerciveWith`, from (8.5.8), Korn's
  inequality and Poincaré's inequality);
* `elasticityLoad Ω f` is `ℓ(v) = ∫_Ω f · v` for `f ∈ [L²(Ω)]^{d+1}` (8.5.14);
* `theorem_8_5_1_dirichlet` is **Theorem 8.5.1 in the pure displacement case**: the weak
  problem (8.5.15) with `Γ_N = ∅` has exactly one solution, and a displacement solves it if and
  only if it minimizes the energy (8.5.17) over `V` — Lax–Milgram (`theorem_8_3_4`) and
  Theorem 8.3.3.

**Not formalized**: the mixed case `meas(Γ_D) > 0`, `Γ_N ≠ ∅` of `theorem_8_5_1`, which needs the
trace on `Γ_D`, the surface measure on `Γ_N` and Korn's *second* inequality on `H¹(Ω)` of a
Lipschitz domain (blocker 2 of `notes/frontier.md`); the group's plan file records the state.
-/

open Filter MeasureTheory Metric Set TopologicalSpace Topology
open scoped ENNReal InnerProductSpace

namespace AtkinsonHan.Chapter08

/-! ### Sums and integrals: bookkeeping -/

/-- Four nested finite sums may be permuted pairwise: `∑ᵢⱼₖₗ f = ∑ₖₗᵢⱼ f`. -/
theorem Finset.sum_sum_sum_sum_comm {ι M : Type*} [Fintype ι] [AddCommMonoid M]
    (f : ι → ι → ι → ι → M) :
    ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l :=
  calc ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ i, ∑ k, ∑ j, ∑ l, f i j k l :=
        Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, ∑ l, f i j k l := Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ l, ∑ j, f i j k l :=
        Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm

/-- Four nested sums of integrals of integrable functions are the integral of the sums. -/
theorem sum_sum_sum_sum_integral_eq {X ι : Type*} [MeasurableSpace X] {μ : Measure X}
    [Fintype ι] {F : ι → ι → ι → ι → X → ℝ} (hF : ∀ i j k l, Integrable (F i j k l) μ) :
    ∑ i, ∑ j, ∑ k, ∑ l, ∫ x, F i j k l x ∂μ = ∫ x, ∑ i, ∑ j, ∑ k, ∑ l, F i j k l x ∂μ := by
  symm
  rw [integral_finsetSum (f := fun i x ↦ ∑ j, ∑ k, ∑ l, F i j k l x) _ fun i _ ↦
    integrable_finsetSum _ fun j _ ↦ integrable_finsetSum _ fun k _ ↦
      integrable_finsetSum _ fun l _ ↦ hF i j k l]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_finsetSum (f := fun j x ↦ ∑ k, ∑ l, F i j k l x) _ fun j _ ↦
    integrable_finsetSum _ fun k _ ↦ integrable_finsetSum _ fun l _ ↦ hF i j k l]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [integral_finsetSum (f := fun k x ↦ ∑ l, F i j k l x) _ fun k _ ↦
    integrable_finsetSum _ fun l _ ↦ hF i j k l]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [integral_finsetSum (f := fun l x ↦ F i j k l x) _ fun l _ ↦ hF i j k l]

/-- The absolute value of four nested sums is at most the four nested sums of absolute values. -/
theorem abs_sum_sum_sum_sum_le {ι : Type*} [Fintype ι] (f : ι → ι → ι → ι → ℝ) :
    |∑ i, ∑ j, ∑ k, ∑ l, f i j k l| ≤ ∑ i, ∑ j, ∑ k, ∑ l, |f i j k l| :=
  (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun _ _ ↦
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun _ _ ↦
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun _ _ ↦
        Finset.abs_sum_le_sum_abs _ _)))

/-- On a Hilbert space, the minimizers of the energy `E(v) = ½ a(v,v) − ℓ(v)` of a bounded,
symmetric, `V`-elliptic form over the whole space are the solutions of `a(u, v) = ℓ(v)` for all
`v`: Theorem 8.3.3 on the subspace `K = V`. -/
theorem isMinOn_energy_univ_iff {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] {a : BilinForm V} {M α : ℝ} (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) (hs : LinearMap.BilinForm.IsSymm a) (ℓ : StrongDual ℝ V) (u : V) :
    IsMinOn (a.energy ℓ) univ u ↔ ∀ v, a u v = ℓ v := by
  have h := theorem_8_3_3_subspace hM hα ha hs ℓ ⊤ (Submodule.mem_top (x := u))
  rw [Submodule.top_coe] at h
  simpa using h

/-- **The Lax–Milgram lemma with the energy characterization**, for a bounded, Hermitian,
coercive form `a` on a Hilbert space and `ℓ ∈ V'`: the problem `a(u, v) = ℓ(v)` for all `v` has
exactly one solution, and `u` solves it if and only if it minimizes `½ a(v, v) − ℓ(v)` over `V`
(`theorem_8_3_4` and Theorem 8.3.3, on the abstract space, so that a concrete instance is one
application). -/
theorem existsUnique_and_isMinOn_iff {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] {a : SesqForm ℝ V} {M c : ℝ}
    (hM : a.IsBoundedWith M) (hc : 0 < c) (hcoer : a.IsCoerciveWith c) (hherm : a.IsHermitian)
    (ℓ : StrongDual ℝ V) :
    (∃! u : V, ∀ v, a u v = ℓ v)
      ∧ ∀ u : V, (∀ v, a u v = ℓ v)
        ↔ IsMinOn (fun v ↦ (1 / 2 : ℝ) * a v v - ℓ v) univ u := by
  have hM' : (BilinForm.ofCLM a).IsBoundedWith M := fun u v ↦ by
    rw [BilinForm.ofCLM_apply, ← Real.norm_eq_abs]
    exact hM u v
  have hα : (BilinForm.ofCLM a).IsEllipticWith c := fun v ↦ by
    rw [BilinForm.ofCLM_apply]
    exact hcoer v
  have hs : LinearMap.BilinForm.IsSymm (BilinForm.ofCLM a) :=
    (BilinForm.isSymm_ofCLM_iff _).2 fun u v ↦ by
      have h := hherm u v
      rwa [conj_trivial] at h
  exact ⟨theorem_8_3_4 hM' hc hα ℓ, fun u ↦ (isMinOn_energy_univ_iff hM' hc hα hs ℓ u).symm⟩

/-! ### The elasticity form `a(u, v) = ∫_Ω [C ε(u)] : ε(v)` -/

section Elasticity

variable {N : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin N)))

/-- The pairing `(u, v) ↦ ⟪T ε(u)_{kl}, ε(v)_{ij}⟫_{L²(Ω)}` of two strain components through a
bounded operator `T` on `L²(Ω)`, as a bounded bilinear form on `[H¹₀(Ω)]^N`; the elasticity form
is a finite sum of these (compare `Elliptic.pairing`). -/
noncomputable def strainPairing
    (T : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) →L[ℝ]
      Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (k l i j : Fin N) : SesqForm ℝ (SobolevEuclideanZeroVec N Ω) :=
  (((innerSL ℝ).comp (T.comp (SobolevEuclideanZeroVec.strainL k l))).flip.comp
    (SobolevEuclideanZeroVec.strainL i j)).flip

/-- `strainPairing T k l i j u v = ⟪T ε(u)_{kl}, ε(v)_{ij}⟫_{L²(Ω)}`. -/
theorem strainPairing_apply
    (T : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) →L[ℝ]
      Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (k l i j : Fin N) (u v : SobolevEuclideanZeroVec N Ω) :
    strainPairing Ω T k l i j u v
      = ⟪T (SobolevEuclideanZeroVec.strainL k l u), SobolevEuclideanZeroVec.strainL i j v⟫_ℝ :=
  rfl

/-- **The elasticity form** `a(u, v) = ∫_Ω [C ε(u)] : ε(v) = ∑ᵢⱼₖₗ ∫_Ω C_ijkl ε_kl(u) ε_ij(v)`
of §8.5 on `[H¹₀(Ω)]^N`, for an elasticity tensor with `L^∞(Ω)` components (8.5.6). -/
noncomputable def elasticityForm
    (C : Fin N → Fin N → Fin N → Fin N →
      Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    SesqForm ℝ (SobolevEuclideanZeroVec N Ω) :=
  ∑ i, ∑ j, ∑ k, ∑ l, strainPairing Ω (Elliptic.mulL Ω (C i j k l)) k l i j

/-- **The elasticity tensor hypotheses (8.5.6)–(8.5.8)**: components `C_ijkl ∈ L^∞(Ω)` (the type),
the symmetries `C_ijkl = C_jikl = C_klij`, and the pointwise stability
`ε : C ε ≥ α |ε|²` for every symmetric `ε ∈ 𝕊^N`, almost everywhere on `Ω`, with `α > 0`. -/
structure IsElasticityTensor
    (C : Fin N → Fin N → Fin N → Fin N →
      Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (α : ℝ) : Prop where
  /-- `C_ijkl = C_jikl` (8.5.7). -/
  symm_left : ∀ i j k l, C i j k l = C j i k l
  /-- `C_ijkl = C_klij` (8.5.7). -/
  symm_pair : ∀ i j k l, C i j k l = C k l i j
  /-- The stability constant is positive. -/
  pos : 0 < α
  /-- Pointwise stability (8.5.8), almost everywhere on `Ω`, for symmetric `ε`. -/
  stable : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
    ∀ ε : Fin N → Fin N → ℝ, (∀ i j, ε i j = ε j i) →
      α * ∑ i, ∑ j, ε i j ^ 2 ≤ ∑ i, ∑ j, ∑ k, ∑ l, C i j k l x * ε k l * ε i j

variable (C : Fin N → Fin N → Fin N → Fin N →
  Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))

/-- The elasticity form as a sum of `L²` inner products of strain components. -/
theorem elasticityForm_apply_inner (u v : SobolevEuclideanZeroVec N Ω) :
    elasticityForm Ω C u v = ∑ i, ∑ j, ∑ k, ∑ l,
      ⟪Elliptic.mulL Ω (C i j k l) (SobolevEuclideanZeroVec.strainL k l u),
        SobolevEuclideanZeroVec.strainL i j v⟫_ℝ := by
  simp only [elasticityForm, sum_apply, strainPairing_apply]

/-- **The elasticity form is the integral `∫_Ω [C ε(u)] : ε(v)`**:
`a(u, v) = ∫_Ω ∑ᵢⱼₖₗ C_ijkl ε_kl(u) ε_ij(v)`. -/
theorem elasticityForm_apply (u v : SobolevEuclideanZeroVec N Ω) :
    elasticityForm Ω C u v = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      ∑ i, ∑ j, ∑ k, ∑ l, C i j k l x * SobolevEuclideanZeroVec.strainL k l u x
        * SobolevEuclideanZeroVec.strainL i j v x := by
  rw [elasticityForm_apply_inner]
  simp only [Elliptic.inner_mulL_eq_integral]
  exact sum_sum_sum_sum_integral_eq fun i j k l ↦ Elliptic.integrable_mul_mul Ω _ _ _

/-- **The elasticity form is bounded**, with constant `∑ᵢⱼₖₗ ‖C_ijkl‖_∞`: each term is at most
`‖C_ijkl‖_∞ ‖ε_kl(u)‖₂ ‖ε_ij(v)‖₂`, and `‖ε_ij(v)‖₂ ≤ ‖v‖`
(`SobolevEuclideanZeroVec.norm_strainL_apply_le`). -/
theorem elasticityForm_isBoundedWith :
    (elasticityForm Ω C).IsBoundedWith (∑ i, ∑ j, ∑ k, ∑ l, ‖C i j k l‖) := by
  intro u v
  rw [Real.norm_eq_abs, elasticityForm_apply_inner]
  have key : ∀ i j k l, |⟪Elliptic.mulL Ω (C i j k l) (SobolevEuclideanZeroVec.strainL k l u),
      SobolevEuclideanZeroVec.strainL i j v⟫_ℝ| ≤ ‖C i j k l‖ * ‖u‖ * ‖v‖ := fun i j k l ↦ by
    refine (abs_real_inner_le_norm _ _).trans ?_
    calc ‖Elliptic.mulL Ω (C i j k l) (SobolevEuclideanZeroVec.strainL k l u)‖
          * ‖SobolevEuclideanZeroVec.strainL i j v‖
        ≤ ‖C i j k l‖ * ‖SobolevEuclideanZeroVec.strainL k l u‖
          * ‖SobolevEuclideanZeroVec.strainL i j v‖ := by
          gcongr
          exact Elliptic.norm_mulL_apply_le Ω _ _
      _ ≤ ‖C i j k l‖ * ‖u‖ * ‖v‖ := by
          gcongr
          · exact SobolevEuclideanZeroVec.norm_strainL_apply_le k l u
          · exact SobolevEuclideanZeroVec.norm_strainL_apply_le i j v
  refine (abs_sum_sum_sum_sum_le _).trans ?_
  calc ∑ i, ∑ j, ∑ k, ∑ l, |⟪Elliptic.mulL Ω (C i j k l)
          (SobolevEuclideanZeroVec.strainL k l u), SobolevEuclideanZeroVec.strainL i j v⟫_ℝ|
      ≤ ∑ i, ∑ j, ∑ k, ∑ l, ‖C i j k l‖ * ‖u‖ * ‖v‖ :=
        Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ Finset.sum_le_sum fun k _ ↦
          Finset.sum_le_sum fun l _ ↦ key i j k l
    _ = (∑ i, ∑ j, ∑ k, ∑ l, ‖C i j k l‖) * ‖u‖ * ‖v‖ := by
        simp only [Finset.sum_mul]

/-- The quadruple sum `∑ᵢⱼₖₗ ⟪C_ijkl S_kl, S'_ij⟫` is symmetric in `(S, S')` under
`C_ijkl = C_klij`, by exchanging the index pairs `(i, j)` and `(k, l)`. -/
theorem sum_inner_mulL_comm {α : ℝ} (hC : IsElasticityTensor Ω C α)
    (S S' : Fin N → Fin N → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ∑ i, ∑ j, ∑ k, ∑ l, ⟪Elliptic.mulL Ω (C i j k l) (S k l), S' i j⟫_ℝ
      = ∑ i, ∑ j, ∑ k, ∑ l, ⟪Elliptic.mulL Ω (C i j k l) (S' k l), S i j⟫_ℝ := by
  simp only [Elliptic.inner_mulL_eq_integral]
  rw [Finset.sum_sum_sum_sum_comm (fun i j k l ↦ ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
    C i j k l x * S k l x * S' i j x)]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
    Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
  rw [hC.symm_pair k l i j]
  exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)

/-- **The elasticity form is symmetric** under `C_ijkl = C_klij`: `a(u, v) = a(v, u)`, by
exchanging the index pairs `(i, j)` and `(k, l)` in the quadruple sum. -/
theorem elasticityForm_comm {α : ℝ} (hC : IsElasticityTensor Ω C α)
    (u v : SobolevEuclideanZeroVec N Ω) :
    elasticityForm Ω C u v = elasticityForm Ω C v u := by
  rw [elasticityForm_apply_inner, elasticityForm_apply_inner]
  exact sum_inner_mulL_comm Ω C hC (fun i j ↦ SobolevEuclideanZeroVec.strainL i j u)
    (fun i j ↦ SobolevEuclideanZeroVec.strainL i j v)

/-- The elasticity form is Hermitian (over `ℝ`: symmetric) under `C_ijkl = C_klij`. -/
theorem elasticityForm_isHermitian {α : ℝ} (hC : IsElasticityTensor Ω C α) :
    (elasticityForm Ω C).IsHermitian := fun u v ↦ by
  rw [conj_trivial]
  exact elasticityForm_comm Ω C hC u v

/-- **The elasticity form dominates `α ∫_Ω |ε(v)|²`** under the stability condition (8.5.8):
`a(v, v) ≥ α ∑ᵢⱼ ‖ε_ij(v)‖²₂`, the pointwise inequality applied to the symmetric matrix `ε(v)(x)`
under the integral. -/
theorem elasticityForm_self_ge {α : ℝ} (hC : IsElasticityTensor Ω C α)
    (v : SobolevEuclideanZeroVec N Ω) :
    α * ∑ i, ∑ j, ‖SobolevEuclideanZeroVec.strainL i j v‖ ^ 2 ≤ elasticityForm Ω C v v := by
  rw [elasticityForm_apply_inner]
  obtain ⟨S, hS⟩ : ∃ S : Fin N → Fin N →
      Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      S = fun i j ↦ SobolevEuclideanZeroVec.strainL i j v := ⟨_, rfl⟩
  have hSsymm : ∀ i j, S i j = S j i := fun i j ↦ by
    rw [hS]
    exact congrFun (congrArg DFunLike.coe (SobolevEuclideanZeroVec.strainL_symm i j)) v
  have hsum : ∑ i, ∑ j, ‖SobolevEuclideanZeroVec.strainL i j v‖ ^ 2 = ∑ i, ∑ j, ‖S i j‖ ^ 2 := by
    rw [hS]
  have hinner : ∀ i j k l, ⟪Elliptic.mulL Ω (C i j k l) (SobolevEuclideanZeroVec.strainL k l v),
      SobolevEuclideanZeroVec.strainL i j v⟫_ℝ = ⟪Elliptic.mulL Ω (C i j k l) (S k l), S i j⟫_ℝ :=
    fun i j k l ↦ by rw [hS]
  simp only [hsum, hinner, Elliptic.inner_mulL_eq_integral]
  have hint : ∀ i j k l, Integrable (fun x ↦ C i j k l x * S k l x * S i j x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := fun i j k l ↦
    Elliptic.integrable_mul_mul Ω _ _ _
  have hsq : ∀ i j, Integrable (fun x ↦ S i j x * S i j x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := fun i j ↦
    (L2.integrable_inner (𝕜 := ℝ) (S i j) (S i j)).congr
      (Eventually.of_forall fun x ↦ by simp [sq])
  have e : ∑ i, ∑ j, ‖S i j‖ ^ 2 = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      ∑ i, ∑ j, S i j x * S i j x := by
    rw [integral_finsetSum (f := fun i x ↦ ∑ j, S i j x * S i j x) _ fun i _ ↦
      integrable_finsetSum _ fun j _ ↦ hsq i j]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_finsetSum (f := fun j x ↦ S i j x * S i j x) _ fun j _ ↦ hsq i j]
    exact Finset.sum_congr rfl fun j _ ↦ by
      rw [← real_inner_self_eq_norm_sq, L2.inner_eq_integral_mul]
  rw [e, ← integral_const_mul, sum_sum_sum_sum_integral_eq hint]
  refine integral_mono_ae ((integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
    hsq i j).const_mul α) (integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      integrable_finsetSum _ fun k _ ↦ integrable_finsetSum _ fun l _ ↦ hint i j k l) ?_
  filter_upwards [hC.stable] with x hx
  have h := hx (fun i j ↦ S i j x) fun i j ↦ by rw [hSsymm]
  simpa [sq] using h

end Elasticity

/-! ### Coercivity on a bounded domain, the load, and Theorem 8.5.1 -/

section Dirichlet

variable {d : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1))))
  (C : Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) →
    Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))

/-- **`V`-ellipticity of the elasticity form on `[H¹₀(Ω)]^{d+1}`** for a bounded
`Ω ⊆ B(0, R)`: `a(v, v) ≥ α / (2 (1 + (2R)²)) ‖v‖²`, from the stability condition (8.5.8)
(`elasticityForm_self_ge`), Korn's first inequality and Poincaré's inequality
(`SobolevEuclideanZeroVec.norm_sq_le_sum_norm_strainL_sq`). This is the step of Exercise 8.5.3
that needs Korn's inequality; on `[H¹₀(Ω)]^{d+1}` the first Korn inequality suffices and no
regularity of the boundary enters. -/
theorem elasticityForm_isCoerciveWith {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R) {α : ℝ}
    (hC : IsElasticityTensor Ω C α) :
    (elasticityForm Ω C).IsCoerciveWith (α / (2 * (1 + (2 * R) ^ 2))) := by
  intro v
  rw [RCLike.re_to_real]
  have h1 := elasticityForm_self_ge Ω C hC v
  have h2 := SobolevEuclideanZeroVec.norm_sq_le_sum_norm_strainL_sq hR hΩ v
  have hpos : 0 < 2 * (1 + (2 * R) ^ 2) := by positivity
  have hα : 0 < α := hC.pos
  calc α / (2 * (1 + (2 * R) ^ 2)) * ‖v‖ ^ 2
      ≤ α / (2 * (1 + (2 * R) ^ 2))
        * (2 * (1 + (2 * R) ^ 2) * ∑ i, ∑ j, ‖SobolevEuclideanZeroVec.strainL i j v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = α * ∑ i, ∑ j, ‖SobolevEuclideanZeroVec.strainL i j v‖ ^ 2 := by
        field_simp
    _ ≤ elasticityForm Ω C v v := h1

/-- **The load `ℓ(v) = ∫_Ω f · v = ∑ᵢ ∫_Ω fᵢ vᵢ`** for a body force `f ∈ [L²(Ω)]^{d+1}` (8.5.14),
as a continuous linear functional on `[H¹₀(Ω)]^{d+1}`; the traction term `∫_{Γ_N} g · v` is
absent in the pure displacement case. -/
noncomputable def elasticityLoad
    (f : Fin (d + 1) → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    StrongDual ℝ (SobolevEuclideanZeroVec (d + 1) Ω) :=
  ∑ i, (Elliptic.load Ω (f i)).comp ((SobolevEuclideanZero (d + 1) 1 2 Ω).subtypeL.comp
    (PiLp.proj 2 (fun _ : Fin (d + 1) ↦ SobolevEuclideanZero (d + 1) 1 2 Ω) i))

/-- `ℓ(v) = ∑ᵢ ∫_Ω fᵢ vᵢ`. -/
theorem elasticityLoad_apply
    (f : Fin (d + 1) → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (v : SobolevEuclideanZeroVec (d + 1) Ω) :
    elasticityLoad Ω f v = ∑ i, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      f i x * SobolevMultiIndex.fn (v i : SobolevEuclidean (d + 1) 1 2 Ω) x := by
  simp only [elasticityLoad, sum_apply, ContinuousLinearMap.comp_apply, Elliptic.load_apply]
  rfl

variable {Ω C}

/-- **Theorem 8.5.1 in the pure displacement case `Γ_D = Γ`**, on a bounded open
`Ω ⊆ B(0, R) ⊆ ℝ^{d+1}`: for an elasticity tensor satisfying (8.5.6)–(8.5.8) and a body force
`f ∈ [L²(Ω)]^{d+1}`, the weak problem (8.5.15) with no traction term,

`u ∈ [H¹₀(Ω)]^{d+1}`, `∫_Ω [C ε(u)] : ε(v) = ∫_Ω f · v` for all `v ∈ [H¹₀(Ω)]^{d+1}`,

has exactly one solution, and a displacement `u` solves it if and only if it minimizes the
energy (8.5.17) `E(v) = ½ ∫_Ω [C ε(v)] : ε(v) − ∫_Ω f · v` over `[H¹₀(Ω)]^{d+1}` (8.5.16). The
form is `elasticityForm Ω C` (`elasticityForm_apply`) and the load `elasticityLoad Ω f`
(`elasticityLoad_apply`); the proof is the Lax–Milgram lemma `theorem_8_3_4` and Theorem 8.3.3,
the `V`-ellipticity being `elasticityForm_isCoerciveWith` (Korn's first inequality on
`[H¹₀(Ω)]^{d+1}`, Poincaré's inequality and (8.5.8)). The mixed boundary conditions of the book's
statement, `meas(Γ_D) > 0` with a traction `g` on `Γ_N`, are `theorem_8_5_1`, which stays open. -/
theorem theorem_8_5_1_dirichlet {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R) {α : ℝ}
    (hC : IsElasticityTensor Ω C α)
    (f : Fin (d + 1) → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    (∃! u : SobolevEuclideanZeroVec (d + 1) Ω,
        ∀ v, elasticityForm Ω C u v = elasticityLoad Ω f v)
      ∧ ∀ u : SobolevEuclideanZeroVec (d + 1) Ω,
        (∀ v, elasticityForm Ω C u v = elasticityLoad Ω f v)
          ↔ IsMinOn (fun v ↦ (1 / 2 : ℝ) * elasticityForm Ω C v v - elasticityLoad Ω f v)
              univ u := by
  have hcoer := elasticityForm_isCoerciveWith Ω C hR hΩ hC
  have hpos : 0 < α / (2 * (1 + (2 * R) ^ 2)) := div_pos hC.pos (by positivity)
  exact existsUnique_and_isMinOn_iff (elasticityForm_isBoundedWith Ω C) hpos hcoer
    (elasticityForm_isHermitian Ω C hC) (elasticityLoad Ω f)

end Dirichlet

end AtkinsonHan.Chapter08

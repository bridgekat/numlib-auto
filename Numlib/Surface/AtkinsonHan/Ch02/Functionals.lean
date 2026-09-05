import Numlib.Backbone
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Atkinson–Han §2.5: linear functionals

Statements from Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework* (3rd ed.), §2.5. The book's dual space `V'` of bounded linear functionals is
Mathlib's `StrongDual 𝕜 V`.

The book's inner product `(u, v)` is linear in its *first* argument while Mathlib's `⟪u, v⟫` is
linear in its second, so the book's `ℓ(v) = (v, u)` is written `ℓ v = inner 𝕜 u v` below.

## Main results

* `IsSublinear`, `isSublinear_iff` — Definition 2.5.4 and its bridge to Mathlib's hypotheses.
* `theorem_2_5_2`, `theorem_2_5_5` — the Hahn–Banach theorem and its generalized (sublinear) form.
* `corollary_2_5_6`, `corollary_2_5_7` — norming functionals and the dual description (2.5.4) of the norm.
* `theorem_2_5_8` — the Riesz representation theorem, (2.5.5) and (2.5.6).

## Not formalized here

Example 2.5.1 (`(Lᵖ)' = Lᵖ'`), Example 2.5.3 (point evaluation on `L^∞`) and Example 2.5.9
(`H¹(a,b)`) are out of scope: they need `Lᵖ` duality and Sobolev spaces.
-/

open Filter Topology

namespace AtkinsonHan.Ch02

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-! ### Theorem 2.5.2: the Hahn–Banach theorem -/

/-- **Hahn–Banach theorem** (Theorem 2.5.2). A bounded linear functional on a subspace `V₀` of a
normed space extends to a bounded linear functional on the whole space with the same norm. -/
theorem theorem_2_5_2 (V₀ : Submodule 𝕜 V) (ℓ : StrongDual 𝕜 V₀) :
    ∃ ℓhat : StrongDual 𝕜 V, (∀ v : V₀, ℓhat v = ℓ v) ∧ ‖ℓhat‖ = ‖ℓ‖ :=
  exists_extension_norm_eq V₀ ℓ

/-! ### Definition 2.5.4 and Theorem 2.5.5: the generalized Hahn–Banach theorem -/

/-- **Sublinear functional** (Definition 2.5.4): `p` is subadditive and positively homogeneous.
The book states positive homogeneity for all `α ≥ 0`; `isSublinear_iff` shows this is the same as
Mathlib's `α > 0` form. -/
def IsSublinear {E : Type*} [AddCommGroup E] [Module ℝ E] (p : E → ℝ) : Prop :=
  (∀ u v, p (u + v) ≤ p u + p v) ∧ ∀ (α : ℝ) (v : E), 0 ≤ α → p (α • v) = α * p v

/-- Bridge from Definition 2.5.4 to the hypotheses `N_add` and `N_hom` of Mathlib's
`exists_extension_of_le_sublinear`: positive homogeneity for `α > 0` already implies it for
`α = 0`, because `p 0 = p (2 • 0) = 2 p 0`. -/
theorem isSublinear_iff {E : Type*} [AddCommGroup E] [Module ℝ E] (p : E → ℝ) :
    IsSublinear p ↔
      (∀ u v, p (u + v) ≤ p u + p v) ∧ ∀ c : ℝ, 0 < c → ∀ v : E, p (c • v) = c * p v := by
  refine ⟨fun h => ⟨h.1, fun c hc v => h.2 c v hc.le⟩, fun h => ⟨h.1, fun α v hα => ?_⟩⟩
  rcases hα.lt_or_eq with hα' | hα'
  · exact h.2 α hα' v
  · have hzero : p 0 = 0 := by
      have := h.2 2 (by norm_num) (0 : E)
      rw [smul_zero] at this
      linarith
    rw [← hα', zero_smul, hzero, zero_mul]

/-- **Generalized Hahn–Banach theorem** (Theorem 2.5.5). On a real vector space, a linear
functional on a subspace dominated by a sublinear functional `p` extends to the whole space,
still dominated by `p`. -/
theorem theorem_2_5_5 {E : Type*} [AddCommGroup E] [Module ℝ E] (V₀ : Submodule ℝ E) (p : E → ℝ)
    (hp : IsSublinear p) (ℓ : V₀ →ₗ[ℝ] ℝ) (hℓ : ∀ v : V₀, ℓ v ≤ p v) :
    ∃ ℓhat : E →ₗ[ℝ] ℝ, (∀ v : V₀, ℓhat v = ℓ v) ∧ ∀ v, ℓhat v ≤ p v := by
  obtain ⟨hadd, hhom⟩ := (isSublinear_iff p).1 hp
  exact exists_extension_of_le_sublinear ⟨V₀, ℓ⟩ p (fun c hc x => hhom c hc x) hadd hℓ

/-! ### Corollaries 2.5.6 and 2.5.7 -/

/-- **Norming functional** (Corollary 2.5.6). For every nonzero `v` there is a functional of norm
one attaining `‖v‖` at `v`. -/
theorem corollary_2_5_6 (v : V) (hv : v ≠ 0) : ∃ ℓ : StrongDual 𝕜 V, ‖ℓ‖ = 1 ∧ ℓ v = ‖v‖ :=
  exists_dual_vector 𝕜 v (norm_ne_zero_iff.mpr hv)

/-- **(2.5.4)** (Corollary 2.5.7): the norm of `v` is the supremum of `|ℓ(v)|` over the unit
sphere of the dual space. -/
theorem corollary_2_5_7 (v : V) : ‖v‖ = sSup {r : ℝ | ∃ ℓ : StrongDual 𝕜 V, ‖ℓ‖ = 1 ∧ r = ‖ℓ v‖} := by
  have hbdd : ∀ r ∈ {r : ℝ | ∃ ℓ : StrongDual 𝕜 V, ‖ℓ‖ = 1 ∧ r = ‖ℓ v‖}, r ≤ ‖v‖ := by
    rintro r ⟨ℓ, hℓ, rfl⟩
    simpa [hℓ] using ℓ.le_opNorm v
  refine le_antisymm ?_ (Real.sSup_le hbdd (norm_nonneg v))
  rcases eq_or_ne v 0 with rfl | hv
  · rw [norm_zero]
    exact Real.sSup_nonneg (by rintro r ⟨ℓ, -, rfl⟩; exact norm_nonneg _)
  · obtain ⟨ℓ, hℓ, hval⟩ := corollary_2_5_6 (𝕜 := 𝕜) v hv
    refine le_csSup ⟨‖v‖, fun r hr => hbdd r hr⟩ ⟨ℓ, hℓ, ?_⟩
    rw [hval, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg v)]

/-! ### Theorem 2.5.8: the Riesz representation theorem -/

/-- **Riesz representation theorem** (Theorem 2.5.8). Every bounded linear functional `ℓ` on a
Hilbert space is `ℓ(v) = (v, u)` for a unique `u` (2.5.5), and `‖ℓ‖ = ‖u‖` (2.5.6). In Mathlib's
convention the book's `(v, u)` is `inner 𝕜 u v`, and the representer `u` is
`(InnerProductSpace.toDual 𝕜 H).symm ℓ`. -/
theorem theorem_2_5_8 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (ℓ : StrongDual 𝕜 H) :
    (∃! u : H, ∀ v, ℓ v = inner 𝕜 u v) ∧ ‖ℓ‖ = ‖(InnerProductSpace.toDual 𝕜 H).symm ℓ‖ := by
  constructor
  · refine ⟨(InnerProductSpace.toDual 𝕜 H).symm ℓ, fun v => ?_, ?_⟩
    · exact (InnerProductSpace.toDual_symm_apply).symm
    · change ∀ u : H, (∀ v, ℓ v = inner 𝕜 u v) → u = (InnerProductSpace.toDual 𝕜 H).symm ℓ
      intro u hu
      have : InnerProductSpace.toDual 𝕜 H u = ℓ := by
        ext v
        exact (hu v).symm
      rw [← this, LinearIsometryEquiv.symm_apply_apply]
  · exact ((InnerProductSpace.toDual 𝕜 H).symm.norm_map ℓ).symm

end AtkinsonHan.Ch02

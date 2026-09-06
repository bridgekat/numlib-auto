import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Numlib.IntegralEquations.L2Kernel

/-!
# Atkinson–Han §2.6: adjoint operators

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §2.6: the adjoint of a bounded operator between
Hilbert spaces, self-adjoint operators, and the characterisation `‖L‖ = sup_{‖v‖ = 1} |(L v, v)|` of
the norm of a self-adjoint operator.

The book restricts §2.6 to real scalars; the statements below are over `RCLike 𝕜`, because
Mathlib's `ContinuousLinearMap.adjoint` is, and the real case is the instantiation. The book's
inner product `(u, v)` is linear in its *first* argument and Mathlib's `⟪u, v⟫` in its second, so
the book's `(u, v)` is written `inner 𝕜 v u`; that is why the defining relation (2.6.1) reads with
its arguments reversed below.

## Main results

* `equation_2_6_1` — the adjoint exists and is unique, characterised by `(L v, w) = (v, L* w)`.
* `equation_2_6_3` — `(L*)* = L`, `(α₁ L₁ + α₂ L₂)* = conj α₁ L₁* + conj α₂ L₂*`,
  `(L₁ L₂)* = L₂* L₁*`.
* `equation_2_6_4` — `‖L*‖ = ‖L‖`.
* `proposition_2_6_2`, `proposition_2_6_3`, `corollary_2_6_4`, `corollary_2_6_4_polynomial` — the
  self-adjoint operators form a real subspace, a product of self-adjoint operators is self-adjoint
  exactly when they commute, and every real polynomial in a self-adjoint operator is self-adjoint.
* `theorem_2_6_5`, `exercise_2_6_3` — `‖L‖ = sup_{‖v‖ = 1} |(L v, v)|` for self-adjoint `L`, and
  the bound `|(L u, v)| ≤ ‖L‖ ‖u‖ ‖v‖` that goes with it.
* `example_2_6_1`, `example_2_6_1_apply`, `example_2_6_1_adjoint`,
  `example_2_6_1_isSelfAdjoint` — the integral operator of a square-integrable kernel on
  `L²(a, b)`: `‖K‖ ≤ B`, the defining formula, the transposed-kernel adjoint, and
  self-adjointness exactly for a symmetric kernel.

## Conventions

Theorem 2.6.5 carries a `[Nontrivial V]` hypothesis: on the zero space the unit sphere is empty and
the supremum the book writes has no meaning. The quantity `(L v, v)` of the book is real for a
self-adjoint `L`, and is written `RCLike.re (inner 𝕜 v (L v))` below.

## Conventions, continued

`equation_2_6_1` above is the *displayed relation* (2.6.1), `(L v, w) = (v, L* w)`, which defines
the adjoint in general — it is not Example 2.6.1, and neither it nor `equation_2_6_3` and
`equation_2_6_4` says anything about integral operators. Example 2.6.1 is the group of
`example_2_6_1` declarations below, over the backbone module `Numlib/IntegralEquations/L2Kernel`;
§2.8.3's bound (2.8.16)–(2.8.17) is the same statement under a second number, and
`example_2_6_1` carries both.

-/

open Metric RCLike Set
open scoped InnerProduct

namespace AtkinsonHan.Chapter02

variable {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [CompleteSpace V] [CompleteSpace W]

/-! ### (2.6.1)–(2.6.4): the adjoint and its algebra -/

/-- **(2.6.1).** For Hilbert spaces `V`, `W` and `L ∈ 𝓛(V, W)` there is a unique `L* ∈ 𝓛(W, V)`
with `(L v, w)_W = (v, L* w)_V` for all `v` and `w`. It is Mathlib's
`ContinuousLinearMap.adjoint`, constructed from the Riesz representation theorem exactly as the
book constructs it from its Theorem 2.5.5. -/
theorem equation_2_6_1 (L : V →L[𝕜] W) :
    ∃! M : W →L[𝕜] V, ∀ (v : V) (w : W), inner 𝕜 w (L v) = inner 𝕜 (M w) v := by
  refine ⟨ContinuousLinearMap.adjoint L, fun v w => ?_, fun M hM => ?_⟩
  · exact (ContinuousLinearMap.adjoint_inner_left L v w).symm
  · exact (ContinuousLinearMap.eq_adjoint_iff M L).mpr fun w v => (hM v w).symm

/-- **(2.6.3)** and Exercise 2.6.1, the algebra of adjoints: the adjoint is an involutive,
conjugate-linear map, and it reverses composition. -/
theorem equation_2_6_3 {U : Type*} [NormedAddCommGroup U] [InnerProductSpace 𝕜 U] [CompleteSpace U]
    (L : V →L[𝕜] W) (α₁ α₂ : 𝕜) (L₁ L₂ : V →L[𝕜] W) (M : W →L[𝕜] U) :
    ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint L) = L ∧
      ContinuousLinearMap.adjoint (α₁ • L₁ + α₂ • L₂) =
        starRingEnd 𝕜 α₁ • ContinuousLinearMap.adjoint L₁ +
          starRingEnd 𝕜 α₂ • ContinuousLinearMap.adjoint L₂ ∧
      ContinuousLinearMap.adjoint (M ∘L L) =
        ContinuousLinearMap.adjoint L ∘L ContinuousLinearMap.adjoint M :=
  ⟨ContinuousLinearMap.adjoint_adjoint L, by rw [map_add, map_smulₛₗ, map_smulₛₗ],
    ContinuousLinearMap.adjoint_comp M L⟩

/-- **(2.6.2)** and **(2.6.4).** The adjoint preserves the operator norm, `‖L*‖ = ‖L‖`; the book
proves `‖L*‖ ≤ ‖L‖` and then applies it to `L*` using `(L*)* = L`. -/
theorem equation_2_6_4 (L : V →L[𝕜] W) : ‖ContinuousLinearMap.adjoint L‖ = ‖L‖ :=
  ContinuousLinearMap.adjoint.norm_map L

/-! ### Self-adjoint operators -/

private theorem isSelfAdjoint_ofReal (α : ℝ) : IsSelfAdjoint (α : 𝕜) := by
  simp [isSelfAdjoint_iff, RCLike.star_def]

/-- **Proposition 2.6.2.** A real linear combination of self-adjoint operators is self-adjoint. -/
theorem proposition_2_6_2 {L₁ L₂ : V →L[𝕜] V} (h₁ : IsSelfAdjoint L₁) (h₂ : IsSelfAdjoint L₂)
    (α₁ α₂ : ℝ) : IsSelfAdjoint ((α₁ : 𝕜) • L₁ + (α₂ : 𝕜) • L₂) :=
  ((isSelfAdjoint_ofReal α₁).smul h₁).add ((isSelfAdjoint_ofReal α₂).smul h₂)

/-- **Proposition 2.6.3.** For self-adjoint `L₁` and `L₂` the product `L₁ L₂` is self-adjoint if
and only if `L₁` and `L₂` commute, because `(L₁ L₂)* = L₂ L₁`. -/
theorem proposition_2_6_3 {L₁ L₂ : V →L[𝕜] V} (h₁ : IsSelfAdjoint L₁) (h₂ : IsSelfAdjoint L₂) :
    IsSelfAdjoint (L₁ ∘L L₂) ↔ L₁ ∘L L₂ = L₂ ∘L L₁ := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff', ContinuousLinearMap.adjoint_comp, h₁.adjoint_eq,
    h₂.adjoint_eq]
  exact eq_comm

/-- **Corollary 2.6.4.** Every power of a self-adjoint operator is self-adjoint. -/
theorem corollary_2_6_4 {L : V →L[𝕜] V} (hL : IsSelfAdjoint L) (n : ℕ) : IsSelfAdjoint (L ^ n) :=
  hL.pow n

/-- **Corollary 2.6.4**, second half: `p(L)` is self-adjoint for every real polynomial `p`, written
here as the finite sum `∑ cᵢ Lⁱ` with real coefficients. -/
theorem corollary_2_6_4_polynomial {L : V →L[𝕜] V} (hL : IsSelfAdjoint L) (n : ℕ) (c : ℕ → ℝ) :
    IsSelfAdjoint (∑ i ∈ Finset.range n, (c i : 𝕜) • L ^ i) := by
  refine Finset.sum_induction _ _ (fun a b ha hb => ha.add hb) (IsSelfAdjoint.zero _) ?_
  exact fun i _ => (isSelfAdjoint_ofReal (c i)).smul (hL.pow i)

/-! ### Theorem 2.6.5 -/

omit [CompleteSpace V] in
private theorem abs_re_inner_eq_abs_rayleigh (T : V →L[𝕜] V) {v : V} (hv : ‖v‖ = 1) :
    |re (inner 𝕜 v (T v))| = |T.rayleighQuotient v| := by
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
    ← inner_conj_symm (T v) v, RCLike.conj_re, hv]
  norm_num

omit [CompleteSpace V] in
private theorem bddAbove_sphere (T : V →L[𝕜] V) :
    BddAbove (Set.range fun v : sphere (0 : V) 1 => |re (inner 𝕜 (v : V) (T v))|) := by
  refine ⟨‖T‖, ?_⟩
  rintro _ ⟨v, rfl⟩
  dsimp only
  rw [abs_re_inner_eq_abs_rayleigh T (mem_sphere_zero_iff_norm.mp v.2)]
  exact T.rayleighQuotient_le_norm (v : V)

section Norm

variable [Nontrivial V] {L : V →L[𝕜] V}

/-- **Theorem 2.6.5** with **(2.6.5)**. For a self-adjoint `L ∈ 𝓛(V)` the operator norm is the
supremum of `|(L v, v)|` over the unit sphere. -/
theorem theorem_2_6_5 (hL : IsSelfAdjoint L) :
    ‖L‖ = ⨆ v : sphere (0 : V) 1, |re (inner 𝕜 (v : V) (L v))| := by
  have hne : Nonempty (sphere (0 : V) 1) := NormedSpace.sphere_nonempty_rclike 𝕜 zero_le_one
  refine le_antisymm ?_ ?_
  · rw [L.norm_eq_iSup_rayleighQuotient hL.isSymmetric]
    refine ciSup_le fun x => ?_
    rcases eq_or_ne x 0 with rfl | hx
    · obtain ⟨v⟩ := hne
      exact le_trans (by simp) (le_ciSup (bddAbove_sphere L) v)
    · have hv : ‖(‖x‖⁻¹ : 𝕜) • x‖ = 1 := by
        rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm,
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
      have hne' : (‖x‖⁻¹ : 𝕜) ≠ 0 :=
        inv_ne_zero (RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx))
      have hmem : (‖x‖⁻¹ : 𝕜) • x ∈ sphere (0 : V) 1 := mem_sphere_zero_iff_norm.mpr hv
      have hle := le_ciSup (bddAbove_sphere L) (⟨_, hmem⟩ : sphere (0 : V) 1)
      rwa [abs_re_inner_eq_abs_rayleigh L hv, L.rayleigh_smul x hne'] at hle
  · refine ciSup_le fun v => ?_
    rw [abs_re_inner_eq_abs_rayleigh L (mem_sphere_zero_iff_norm.mp v.2)]
    exact L.rayleighQuotient_le_norm (v : V)

/-- **Exercise 2.6.3.** The quantity of Theorem 2.6.5 bounds the whole sesquilinear form:
`|(L u, v)| ≤ (sup_{‖w‖ = 1} |(L w, w)|) ‖u‖ ‖v‖` for a self-adjoint `L`. -/
theorem exercise_2_6_3 (hL : IsSelfAdjoint L) (u v : V) :
    ‖inner 𝕜 v (L u)‖ ≤ (⨆ w : sphere (0 : V) 1, |re (inner 𝕜 (w : V) (L w))|) * ‖u‖ * ‖v‖ := by
  rw [← theorem_2_6_5 hL]
  calc ‖inner 𝕜 v (L u)‖ ≤ ‖v‖ * ‖L u‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖L‖ * ‖u‖) := by gcongr; exact L.le_opNorm u
    _ = ‖L‖ * ‖u‖ * ‖v‖ := by ring

end Norm

/-! ### Example 2.6.1: the integral operator of a square-integrable kernel -/

section L2Kernel

open MeasureTheory Real

variable {a b : ℝ} {k : ℝ × ℝ → ℝ}
  (hk : MemLp k 2 ((volume.restrict (Icc a b)).prod (volume.restrict (Icc a b))))

include hk

/-- **Example 2.6.1.** For a kernel with
`B = (∫∫ |k (x, y)|² dx dy)^{1/2} < ∞` the integral operator `K v (x) = ∫ k (x, y) v (y) dy` is
bounded on `L²(a, b)`, with `‖K‖ ≤ B`. This is also (2.8.16)–(2.8.17) of §2.8.3, where `B` is
called the Hilbert–Schmidt norm of `K`. -/
theorem example_2_6_1 : ‖IntegralOperator.l2KernelCLM hk‖ ≤
    √(∫ p, k p ^ 2 ∂((volume.restrict (Icc a b)).prod (volume.restrict (Icc a b)))) :=
  IntegralOperator.norm_l2KernelCLM_le hk

/-- **Example 2.6.1**, the defining formula: `K v (x) = ∫ k (x, y) v (y) dy` for almost every `x`,
an element of `L²(a, b)` being an almost-everywhere class. -/
theorem example_2_6_1_apply (v : Lp ℝ 2 (volume.restrict (Icc a b))) :
    IntegralOperator.l2KernelCLM hk v =ᵐ[volume.restrict (Icc a b)]
      fun x => ∫ y, k (x, y) * v y ∂(volume.restrict (Icc a b)) :=
  IntegralOperator.l2KernelCLM_apply_ae hk v

/-- **Example 2.6.1**, the adjoint: `K* v (y) = ∫ k (x, y) v (x) dx`, the integral operator of the
transposed kernel. -/
theorem example_2_6_1_adjoint (v : Lp ℝ 2 (volume.restrict (Icc a b))) :
    ContinuousLinearMap.adjoint (IntegralOperator.l2KernelCLM hk) v
        =ᵐ[volume.restrict (Icc a b)]
      fun y => ∫ x, k (x, y) * v x ∂(volume.restrict (Icc a b)) := by
  rw [IntegralOperator.adjoint_l2KernelCLM hk]
  exact IntegralOperator.l2KernelCLM_apply_ae _ v

/-- **Example 2.6.1**, self-adjointness: `K` is self-adjoint exactly when `k (x, y) = k (y, x)`.
Almost everywhere, since an element of `L²` is an almost-everywhere class and the kernel of the
zero operator is null only up to a null set. -/
theorem example_2_6_1_isSelfAdjoint :
    IsSelfAdjoint (IntegralOperator.l2KernelCLM hk) ↔
      ∀ᵐ p ∂((volume.restrict (Icc a b)).prod (volume.restrict (Icc a b))),
        k p = k (p.2, p.1) :=
  IntegralOperator.isSelfAdjoint_l2KernelCLM_iff hk

end L2Kernel

end AtkinsonHan.Chapter02

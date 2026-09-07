/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.l2Space`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Series against an orthonormal family

Let `v : ι → E` be an orthonormal family in a real Hilbert space. This module collects the
arithmetic of the series `∑ i, a i • v i`: when it converges, what its coefficients and inner
products are, and the two membership criteria for the closed span of the family.

## Main statements

* `Orthonormal.summable_smul_iff`: the series converges exactly when `∑ i, (a i) ^ 2` does.
* `Orthonormal.inner_eq_of_hasSum`: the coefficients are recovered by pairing with the family.
* `Orthonormal.hasSum_mul_of_hasSum`: Parseval's identity for two such series.
* `Orthonormal.hilbertBasisTopologicalClosure`: an orthonormal family is a Hilbert basis of the
  closure of its span, and `Orthonormal.hasSum_inner_smul_starProjection` expands the orthogonal
  projection onto that closure.
* `Orthonormal.mem_topologicalClosure_span_of_hasSum_inner_sq`: the **completeness criterion**, that
  a vector whose coefficients against the family already carry its whole norm lies in the closed
  span. It is the converse of Bessel's inequality, and it is what turns a computation with the
  coefficients into a statement that a family is complete.
-/

noncomputable section

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {v : ι → E}

/-- A vector in the closure of the span of a family is the limit of finite linear combinations; in
particular the sum of a convergent series in the family lies there. -/
theorem mem_topologicalClosure_span_of_hasSum {a : ι → ℝ} {y : E}
    (h : HasSum (fun i => a i • v i) y) :
    y ∈ (Submodule.span ℝ (Set.range v)).topologicalClosure := by
  have hmem : ∀ s : Finset ι, (∑ i ∈ s, a i • v i) ∈ Submodule.span ℝ (Set.range v) := fun s =>
    Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  have hy : y ∈ closure (Submodule.span ℝ (Set.range v) : Set E) :=
    mem_closure_of_tendsto h (Filter.Eventually.of_forall hmem)
  rwa [← Submodule.topologicalClosure_coe] at hy

/-- A vector orthogonal to every member of a family is orthogonal to the span of the family. -/
theorem Submodule.mem_orthogonal_span_range {x : E} (h : ∀ i, inner ℝ (v i) x = 0) :
    x ∈ (Submodule.span ℝ (Set.range v))ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
  · rintro y ⟨i, rfl⟩
    exact h i
  · simp
  · intro a b _ _ ha hb
    rw [inner_add_left, ha, hb, add_zero]
  · intro r a _ ha
    rw [real_inner_smul_left, ha, mul_zero]

namespace Orthonormal

/-- **The coefficients of a convergent orthonormal series** are its inner products with the
family. -/
theorem inner_eq_of_hasSum (hv : Orthonormal ℝ v) {a : ι → ℝ} {y : E}
    (h : HasSum (fun i => a i • v i) y) (i : ι) : inner ℝ (v i) y = a i := by
  have h1 := h.mapL (innerSL ℝ (v i))
  simp only [innerSL_apply_apply ℝ, real_inner_smul_right] at h1
  have hdiag : (inner ℝ (v i) (v i) : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hv.1 i, one_pow]
  have h2 : HasSum (fun j : ι => a j * inner ℝ (v i) (v j)) (a i * inner ℝ (v i) (v i)) :=
    hasSum_single (f := fun j : ι => a j * inner ℝ (v i) (v j)) i fun j hj => by
      rw [hv.2 (Ne.symm hj), mul_zero]
  rw [hdiag, mul_one] at h2
  exact h1.unique h2

/-- **Parseval's identity for two orthonormal series**: the inner product of two convergent series
in the same orthonormal family is the sum of the products of their coefficients. -/
theorem hasSum_mul_of_hasSum (hv : Orthonormal ℝ v) {a b : ι → ℝ} {x y : E}
    (hx : HasSum (fun i => a i • v i) x) (hy : HasSum (fun i => b i • v i) y) :
    HasSum (fun i => a i * b i) (inner ℝ x y) := by
  have h1 := hx.mapL (innerSL ℝ y)
  simp only [innerSL_apply_apply ℝ, real_inner_smul_right] at h1
  rw [real_inner_comm y x]
  refine h1.congr_fun fun i => ?_
  rw [real_inner_comm (v i) y, hv.inner_eq_of_hasSum hy i]

section CompleteSpace

variable [CompleteSpace E]

/-- A series of scalar multiples of an orthonormal family converges exactly when the squares of the
coefficients are summable. -/
theorem summable_smul_iff (hv : Orthonormal ℝ v) (a : ι → ℝ) :
    (Summable fun i => a i • v i) ↔ Summable fun i => a i ^ 2 := by
  simpa [LinearIsometry.toSpanSingleton_apply, Real.norm_eq_abs, sq_abs] using
    hv.orthogonalFamily.summable_iff_norm_sq_summable a

/-- An orthonormal family is a Hilbert basis of the closure of its span. -/
def hilbertBasisTopologicalClosure (hv : Orthonormal ℝ v) :
    HilbertBasis ι ℝ ((Submodule.span ℝ (Set.range v)).topologicalClosure) :=
  haveI : CompleteSpace ((Submodule.span ℝ (Set.range v)).topologicalClosure) :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  HilbertBasis.mkOfOrthogonalEqBot
    (hv.codRestrict _ fun i =>
      Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self i)))
    (by
      rw [Submodule.eq_bot_iff]
      intro x hx
      have hgen : ∀ i, inner ℝ (v i) (x : E) = 0 := fun i =>
        (Submodule.mem_orthogonal _ _).1 hx _ (Submodule.subset_span (Set.mem_range_self i))
      have hmem : (x : E) ∈ (Submodule.span ℝ (Set.range v))ᗮ :=
        Submodule.mem_orthogonal_span_range hgen
      have hmem2 : (x : E) ∈ (Submodule.span ℝ (Set.range v))ᗮᗮ :=
        Submodule.topologicalClosure_minimal _ (Submodule.le_orthogonal_orthogonal _)
          (Submodule.isClosed_orthogonal _) x.2
      have hzero : inner ℝ (x : E) (x : E) = 0 := (Submodule.mem_orthogonal _ _).1 hmem2 _ hmem
      exact Submodule.coe_eq_zero.mp (inner_self_eq_zero.mp hzero))

/-- **The expansion of an orthogonal projection in an orthonormal family.** The projection onto
the closed span of an orthonormal family is the sum of the family against the coefficients of the
projected vector; for a vector already in that closed span it is the expansion of the vector
itself. -/
theorem hasSum_inner_smul_starProjection (hv : Orthonormal ℝ v) (x : E) :
    HasSum (fun i : ι => (inner ℝ (v i) x) • v i)
      ((Submodule.span ℝ (Set.range v)).topologicalClosure.starProjection x) := by
  have : CompleteSpace ((Submodule.span ℝ (Set.range v)).topologicalClosure) :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hmem : ∀ i : ι, v i ∈ (Submodule.span ℝ (Set.range v)).topologicalClosure := fun i =>
    Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self i))
  have hbcoe : ∀ i : ι, ((hv.hilbertBasisTopologicalClosure i :
      (Submodule.span ℝ (Set.range v)).topologicalClosure) : E) = v i := by
    intro i
    simp only [hilbertBasisTopologicalClosure]
    rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
    rfl
  have hsum := (hv.hilbertBasisTopologicalClosure.hasSum_repr
      ⟨_, (Submodule.span ℝ (Set.range v)).topologicalClosure.starProjection_apply_mem x⟩).mapL
    (Submodule.span ℝ (Set.range v)).topologicalClosure.subtypeL
  refine hsum.congr_fun fun i => ?_
  rw [ContinuousLinearMap.map_smul, Submodule.subtypeL_apply, hbcoe i,
    HilbertBasis.repr_apply_apply, Submodule.coe_inner, hbcoe i,
    ← Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr (hmem i)]

/-- **The expansion of a vector in the closed span of an orthonormal family.** -/
theorem hasSum_inner_smul_of_mem (hv : Orthonormal ℝ v) {x : E}
    (hx : x ∈ (Submodule.span ℝ (Set.range v)).topologicalClosure) :
    HasSum (fun i : ι => (inner ℝ (v i) x) • v i) x := by
  have : CompleteSpace ((Submodule.span ℝ (Set.range v)).topologicalClosure) :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  simpa [Submodule.starProjection_eq_self_iff.mpr hx] using hv.hasSum_inner_smul_starProjection x

/-- **The completeness criterion for an orthonormal family.** If the squares of the coefficients of
`x` against an orthonormal family already sum to `‖x‖ ^ 2` — that is, if Bessel's inequality is an
equality at `x` — then `x` lies in the closed span of the family. -/
theorem mem_topologicalClosure_span_of_hasSum_inner_sq (hv : Orthonormal ℝ v) {x : E}
    (h : HasSum (fun i : ι => (inner ℝ (v i) x : ℝ) ^ 2) (‖x‖ ^ 2)) :
    x ∈ (Submodule.span ℝ (Set.range v)).topologicalClosure := by
  obtain ⟨y, hy⟩ := (hv.summable_smul_iff fun i => (inner ℝ (v i) x : ℝ)).2 h.summable
  have hyy : (inner ℝ y y : ℝ) = ‖x‖ ^ 2 :=
    (hv.hasSum_mul_of_hasSum hy hy).unique (h.congr_fun fun i => (pow_two _).symm)
  have hxy : (inner ℝ x y : ℝ) = ‖x‖ ^ 2 := by
    have h1 := hy.mapL (innerSL ℝ x)
    simp only [innerSL_apply_apply ℝ, real_inner_smul_right] at h1
    refine h1.unique (h.congr_fun fun i => ?_)
    rw [real_inner_comm (v i) x, pow_two]
  have hzero : ‖x - y‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, hxy, ← real_inner_self_eq_norm_sq y, hyy]
    ring
  have : x = y := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hzero
    rwa [norm_eq_zero, sub_eq_zero] at this
  rw [this]
  exact mem_topologicalClosure_span_of_hasSum hy

/-- **Splitting an orthonormal family in two.** For an orthonormal family indexed by a sum type, the
closed span of the second half is the part of the closed span of the whole family orthogonal to the
closed span of the first half.

Applied to a two-channel filter bank, this is what identifies the wavelet space `W = V₁ ⊖ V₀` with
the closed span of the high-pass channel. -/
theorem topologicalClosure_span_comp_inr {ι κ : Type*} {u : ι ⊕ κ → E} (hu : Orthonormal ℝ u) :
    (Submodule.span ℝ (Set.range (u ∘ Sum.inr))).topologicalClosure
      = (Submodule.span ℝ (Set.range (u ∘ Sum.inl))).topologicalClosureᗮ
        ⊓ (Submodule.span ℝ (Set.range u)).topologicalClosure := by
  have hperp : ∀ j : κ, (u ∘ Sum.inr) j ∈ (Submodule.span ℝ (Set.range (u ∘ Sum.inl)))ᗮ := fun j =>
    Submodule.mem_orthogonal_span_range fun i => hu.2 (by simp)
  refine le_antisymm (le_inf ?_ ?_) ?_
  · rw [Submodule.orthogonal_closure]
    exact Submodule.topologicalClosure_minimal _
      (Submodule.span_le.2 (Set.range_subset_iff.2 hperp)) (Submodule.isClosed_orthogonal _)
  · exact Submodule.topologicalClosure_mono
      (Submodule.span_mono (Set.range_comp_subset_range _ _))
  · rintro x ⟨hx1, hx2⟩
    have hsum := hu.hasSum_inner_smul_of_mem hx2
    have hzero : ∀ i : ι ⊕ κ, i ∉ Set.range (Sum.inr : κ → ι ⊕ κ) →
        (inner ℝ (u i) x : ℝ) • u i = 0 := by
      rintro (a | a) ha
      · rw [(Submodule.mem_orthogonal _ _).1 hx1 (u (Sum.inl a))
          (Submodule.le_topologicalClosure _
            (Submodule.subset_span (Set.mem_range_self (f := u ∘ Sum.inl) a))), zero_smul]
      · exact absurd (Set.mem_range_self a) ha
    exact mem_topologicalClosure_span_of_hasSum
      ((Sum.inr_injective.hasSum_iff hzero).mpr hsum)

end CompleteSpace

end Orthonormal

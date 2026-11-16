/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.l2Space`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Series against an orthonormal family

Let $(v_i)_{i \in \iota}$ be an orthonormal family in a real inner product space $E$, and let
$\overline{V}$ be the closure of its span. This module studies the series $\sum_i a_i v_i$ with real
coefficients $a_i$. The coefficients of a convergent series are recovered as
$a_i = \langle v_i, y \rangle$, and the inner product of two convergent series is $\sum_i a_i b_i$.
When $E$ is complete, the series converges exactly when $\sum_i a_i^2$ converges, the family is a
Hilbert basis of $\overline{V}$, and the orthogonal projection onto $\overline{V}$ is
$x \mapsto \sum_i \langle v_i, x \rangle v_i$. The module also gives a criterion for membership in
$\overline{V}$: if $\sum_i \langle v_i, x \rangle^2 = \|x\|^2$, then $x \in \overline{V}$. This
criterion is the converse of Bessel's inequality. It turns a computation with the coefficients into
a proof that a family is complete.

## Main results

* `Orthonormal.inner_eq_of_hasSum`: if $\sum_i a_i v_i = y$, then $\langle v_i, y \rangle = a_i$ for
  every $i$.
* `Orthonormal.hasSum_mul_of_hasSum`: Parseval's identity $\langle x, y \rangle = \sum_i a_i b_i$
  for two series $x = \sum_i a_i v_i$ and $y = \sum_i b_i v_i$.
* `Orthonormal.summable_smul_iff`: in a complete space, $\sum_i a_i v_i$ converges if and only if
  $\sum_i a_i^2$ converges.
* `Orthonormal.hilbertBasisTopologicalClosure`: in a complete space, the family is a Hilbert basis
  of $\overline{V}$.
* `Orthonormal.hasSum_inner_smul_starProjection`: in a complete space, the orthogonal projection of
  $x$ onto $\overline{V}$ is $\sum_i \langle v_i, x \rangle v_i$.
* `Orthonormal.mem_topologicalClosure_span_of_hasSum_inner_sq`: the completeness criterion, that
  $\sum_i \langle v_i, x \rangle^2 = \|x\|^2$ implies $x \in \overline{V}$.
* `Orthonormal.topologicalClosure_span_comp_inr`: for an orthonormal family indexed by a disjoint
  union $\iota \sqcup \kappa$, the closed span of the second part is the orthogonal complement of
  the closed span of the first part inside the closed span of the whole family.

## Implementation notes

* Convergence of a series means unconditional convergence, Mathlib's `HasSum` and `Summable`. The
  index type $\iota$ is arbitrary.
* The closed span $\overline{V}$ is `(Submodule.span ℝ (Set.range v)).topologicalClosure`.
-/

noncomputable section

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {v : ι → E}

/-- Let $(v_i)_{i \in \iota}$ be any family in a real inner product space $E$, let
$a \colon \iota \to \mathbb{R}$, and let $y \in E$. If the series $\sum_i a_i v_i$ converges
unconditionally to $y$, then $y$ lies in the closure of the span of the family.

The family need not be orthonormal: the partial sums lie in the span, and their limit lies in
its closure. -/
theorem mem_topologicalClosure_span_of_hasSum {a : ι → ℝ} {y : E}
    (h : HasSum (fun i => a i • v i) y) :
    y ∈ (Submodule.span ℝ (Set.range v)).topologicalClosure := by
  have hmem : ∀ s : Finset ι, (∑ i ∈ s, a i • v i) ∈ Submodule.span ℝ (Set.range v) := fun s =>
    Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  have hy : y ∈ closure (Submodule.span ℝ (Set.range v) : Set E) :=
    mem_closure_of_tendsto h (Filter.Eventually.of_forall hmem)
  rwa [← Submodule.topologicalClosure_coe] at hy

/-- Let $(v_i)_{i \in \iota}$ be any family in a real inner product space $E$, and let $x \in E$. If
$\langle v_i, x \rangle = 0$ for every $i$, then $x$ is orthogonal to the span of the family. -/
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

/-- **The coefficients of a convergent orthonormal series.** Let $(v_i)_{i \in \iota}$ be an
orthonormal family in a real inner product space $E$, let $a \colon \iota \to \mathbb{R}$, and
let $y \in E$. If the series $\sum_i a_i v_i$ converges unconditionally to $y$, then
$$\langle v_i, y \rangle = a_i \quad \text{for every } i \in \iota.$$
-/
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

/-- **Parseval's identity for two orthonormal series.** Let $(v_i)_{i \in \iota}$ be an orthonormal
family in a real inner product space $E$, let $a, b \colon \iota \to \mathbb{R}$, and let
$x, y \in E$. If $\sum_i a_i v_i$ converges unconditionally to $x$ and $\sum_i b_i v_i$
converges unconditionally to $y$, then the series $\sum_i a_i b_i$ converges unconditionally,
and
$$\sum_i a_i b_i = \langle x, y \rangle.$$
-/
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

/-- Let $(v_i)_{i \in \iota}$ be an orthonormal family in a real Hilbert space $E$, and let
$a \colon \iota \to \mathbb{R}$. Then the series $\sum_i a_i v_i$ converges unconditionally if
and only if the series $\sum_i a_i^2$ converges. -/
theorem summable_smul_iff (hv : Orthonormal ℝ v) (a : ι → ℝ) :
    (Summable fun i => a i • v i) ↔ Summable fun i => a i ^ 2 := by
  simpa [LinearIsometry.toSpanSingleton_apply, Real.norm_eq_abs, sq_abs] using
    hv.orthogonalFamily.summable_iff_norm_sq_summable a

/-- Let $(v_i)_{i \in \iota}$ be an orthonormal family in a real Hilbert space $E$. Then the family
is a **Hilbert basis** of the closure $\overline{V}$ of its span: it is orthonormal in
$\overline{V}$, and every vector of $\overline{V}$ is the sum of its expansion in the family.

The definition builds the Hilbert basis with `HilbertBasis.mkOfOrthogonalEqBot`. The closure
$\overline{V}$ is complete because $E$ is complete and $\overline{V}$ is closed. -/
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

/-- **The expansion of an orthogonal projection in an orthonormal family.** Let
$(v_i)_{i \in \iota}$ be an orthonormal family in a real Hilbert space $E$, and let $P$ be the
orthogonal projection onto the closure $\overline{V}$ of its span. Then for every $x \in E$, the
series $\sum_i \langle v_i, x \rangle v_i$ converges unconditionally, and
$$\sum_i \langle v_i, x \rangle \, v_i = P x.$$

The projection $P$ is `Submodule.starProjection` of $\overline{V}$. For $x \in \overline{V}$
this gives the expansion of $x$ itself, `Orthonormal.hasSum_inner_smul_of_mem`. -/
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

/-- **The expansion of a vector in the closed span of an orthonormal family.** Let
$(v_i)_{i \in \iota}$ be an orthonormal family in a real Hilbert space $E$, and let $x$ lie in
the closure of the span of the family. Then the series $\sum_i \langle v_i, x \rangle v_i$
converges unconditionally to $x$. -/
theorem hasSum_inner_smul_of_mem (hv : Orthonormal ℝ v) {x : E}
    (hx : x ∈ (Submodule.span ℝ (Set.range v)).topologicalClosure) :
    HasSum (fun i : ι => (inner ℝ (v i) x) • v i) x := by
  have : CompleteSpace ((Submodule.span ℝ (Set.range v)).topologicalClosure) :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  simpa [Submodule.starProjection_eq_self_iff.mpr hx] using hv.hasSum_inner_smul_starProjection x

/-- **The completeness criterion for an orthonormal family.** Let $(v_i)_{i \in \iota}$ be an
orthonormal family in a real Hilbert space $E$, and let $x \in E$. If the series
$\sum_i \langle v_i, x \rangle^2$ converges unconditionally to $\|x\|^2$, then $x$ lies in the
closure of the span of the family.

The hypothesis says that Bessel's inequality $\sum_i \langle v_i, x \rangle^2 \le \|x\|^2$ is an
equality at $x$, so the theorem is the converse of Bessel's inequality. -/
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

/-- **Splitting an orthonormal family in two.** Let $(u_k)_{k \in \iota \sqcup \kappa}$ be an
orthonormal family in a real Hilbert space $E$, indexed by the disjoint union of two types. Let
$U_1$, $U_2$ and $U$ be the closures of the spans of the families $(u_i)_{i \in \iota}$,
$(u_j)_{j \in \kappa}$ and $(u_k)_{k \in \iota \sqcup \kappa}$. Then
$$U_2 = U_1^\perp \cap U.$$

The two parts of the family are `u ∘ Sum.inl` and `u ∘ Sum.inr`. For a two-channel filter bank,
this result identifies the wavelet space $W = V_1 \ominus V_0$ with the closed span of the
high-pass channel. -/
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

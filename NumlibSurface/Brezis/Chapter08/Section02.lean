import Numlib.Analysis.Sobolev.Interval.DifferenceQuotient
import NumlibSurface.Brezis.Chapter04.Section03

/-!
# Brezis §8.2: the Sobolev space `W^{1,p}(I)`

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §8.2, including the closing paragraph on the spaces
`W^{m,p}`. Throughout, `I` is an open interval of `ℝ`, possibly unbounded — an `I : Opens ℝ`
with the hypothesis `(hI : (I : Set ℝ).OrdConnected)` wherever the book says "interval" — and
`1 ≤ p ≤ ∞` is `p : ℝ≥0∞` with `[Fact (1 ≤ p)]`. Everything delegates to the backbone modules
`Numlib/Analysis/Sobolev/Interval/{Basic, Extension, Density, Embedding, Higher, Zero,
DifferenceQuotient}`.

## Correspondence

* The book's `W^{1,p}(I)` is `sobolevSpace p I = SobolevIntervalLp 1 p I` and `H¹(I)` is
  `H1 I = sobolevSpace 2 I`; the book's set-theoretic definition is the predicate
  `MemSobolevSpace p I u` on functions, identified with the backbone's `MemSobolevIntervalLp`
  by `memSobolevSpace_iff_memSobolevIntervalLp`. The test class is `𝓓(I, ℝ) = C_c^∞(I)`;
  Remark 1 (`remark_8_1`) says that `C_c^1(I)`, Mathlib's `𝓓^{1}(I, ℝ)`, gives the same space.
* For `u : SobolevIntervalLp 1 p I`, the book's `u'` is `u.deriv 1`, its function is `u.fn`
  (`u.deriv 0`), and its continuous representative `ũ` of Theorem 8.2 is `u.rep`, so that
  "`u(x)` for `x ∈ Ī`" is `u.rep x`.
* The book's norm `‖u‖_{W^{1,p}} = ‖u‖_{L^p} + ‖u'‖_{L^p}` is `sobolevNorm u`; the norm of the
  type is the "equivalent norm" `(‖u‖_p^p + ‖u'‖_p^p)^{1/p}` (`sobolevNorm_equiv`), and at
  `p = 2` it is the book's `H¹` norm (`norm_H1_sq`, `inner_H1`).
* `W^{m,p}(I)` is `sobolevSpaceHigher m p I = SobolevIntervalLp m p I`, the book's inductive
  definition being the predicate `MemSobolevSpaceHigher` (`memSobolevSpaceHigher_iff`).

## Main results

* `proposition_8_1` — `W^{1,p}` is a Banach space, reflexive for `1 < p < ∞`, separable for
  `1 ≤ p < ∞`; `H¹` is a separable Hilbert space.
* `theorem_8_2` — the continuous representative, with `remark_8_5`, `remark_8_6`, and the
  lemmas `lemma_8_1` (du Bois-Reymond) and `lemma_8_2` (the primitive) of its proof.
* `proposition_8_3`, `proposition_8_4`, `proposition_8_5` — the characterizations of `W^{1,p}`
  by the bound `|∫ u φ'| ≤ C ‖φ‖_{p'}`, of `W^{1,∞}` by the Lipschitz condition, and of
  `W^{1,p}(ℝ)` by translations.
* `theorem_8_6` — the extension operator, with `lemma_8_3` and the constants of footnote 6.
* `theorem_8_7` — density of `C_c^∞(ℝ)`, with `lemma_8_4` and `remark_8_9`.
* `theorem_8_8` — the embedding `W^{1,p}(I) ⊆ L^∞(I)` and the two compactness statements,
  with Remarks 10–12 and Corollaries 8.9–8.11.
* `sobolevSpaceHigher`, `memSobolevSpaceHigher_iff_forall_integral`, `sobolevNormHigher`,
  `interpolationInequality`, `sobolevSpaceHigher_subset_contDiff` — the paragraph on `W^{m,p}`.

Remark 3 (distributions) and the bounded-variation clauses of Remark 8 are not formalized
(chapter plan). The book's proofs of Theorem 8.8 (5), Corollaries 8.9–8.11 go through the
density theorem; the backbone proves them from the absolutely continuous representative, so the
surface proofs are one-line specializations either way.
-/

open Filter MeasureTheory Set TopologicalSpace
open scoped Convolution Distributions ENNReal InnerProductSpace Topology

noncomputable section

namespace Brezis.Chapter08

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {I : Opens ℝ}

/-! ### The definition -/

/-- **Definition (§8.2).** The Sobolev space `W^{1,p}(I)`, for an open interval `I` and
`1 ≤ p ≤ ∞`: the backbone's `SobolevIntervalLp 1 p I`, a Banach space whose elements are the
pairs `(u, u')` in `L^p(I) × L^p(I)`. -/
abbrev sobolevSpace (p : ℝ≥0∞) (I : Opens ℝ) : Type := SobolevIntervalLp 1 p I

/-- **Notation (§8.2).** `H¹(I) = W^{1,2}(I)`. -/
abbrev H1 (I : Opens ℝ) : Type := sobolevSpace 2 I

/-- **Definition (§8.2), as a predicate on functions.** `u ∈ W^{1,p}(I)` means: `u ∈ L^p(I)`
and there is `g ∈ L^p(I)` with `∫_I u φ' = -∫_I g φ` for every test function `φ ∈ C_c^∞(I)`
(the book's `C_c^1(I)`; both classes give the same space, `remark_8_1`). The function `g` is
the weak derivative `u'`, well defined almost everywhere (`memSobolevSpace_deriv_unique`). -/
def MemSobolevSpace (p : ℝ≥0∞) (I : Opens ℝ) (u : ℝ → ℝ) : Prop :=
  MemLp u p (volume.restrict I) ∧ ∃ g : ℝ → ℝ, MemLp g p (volume.restrict I) ∧
    ∀ φ : 𝓓(I, ℝ), ∫ x in (I : Set ℝ), u x * deriv φ x = -∫ x in (I : Set ℝ), g x * φ x

/-- The book's definition of `W^{1,p}(I)` is the backbone's `MemSobolevIntervalLp u 1 p I`: an
`L^p` function is locally integrable, so the identity against test functions is the weak
derivative `HasWeakDerivOn u g I`. -/
theorem memSobolevSpace_iff_memSobolevIntervalLp {u : ℝ → ℝ} :
    MemSobolevSpace p I u ↔ MemSobolevIntervalLp u 1 p I := by
  rw [MemSobolevSpace, memSobolevIntervalLp_one_iff]
  refine and_congr_right fun hu ↦ ⟨fun ⟨g, hg, h⟩ ↦ ⟨g, hasWeakDerivOn_iff.2
    ⟨hu.locallyIntegrableOn Fact.out, hg.locallyIntegrableOn Fact.out, fun φ ↦ ?_⟩, hg⟩,
    fun ⟨g, hg, hgp⟩ ↦ ⟨g, hgp, fun φ ↦ ?_⟩⟩
  · have := h φ
    simp only [mul_comm] at this ⊢
    exact this
  · have := hg.integral_deriv_mul φ
    simp only [mul_comm] at this ⊢
    exact this

/-- **Footnote 2 of §8.2.** The weak derivative is well defined almost everywhere on `I`: two
functions `g₁, g₂ ∈ L^p(I)` with `∫_I u φ' = -∫_I gᵢ φ` for every test function agree a.e. on
`I` (the book's Corollary 4.24, here the uniqueness `HasWeakIteratedLineDerivOn.ae_eq`). -/
theorem memSobolevSpace_deriv_unique {u g₁ g₂ : ℝ → ℝ} (hu : MemLp u p (volume.restrict I))
    (hg₁ : MemLp g₁ p (volume.restrict I)) (hg₂ : MemLp g₂ p (volume.restrict I))
    (h₁ : ∀ φ : 𝓓(I, ℝ), ∫ x in (I : Set ℝ), u x * deriv φ x = -∫ x in (I : Set ℝ), g₁ x * φ x)
    (h₂ : ∀ φ : 𝓓(I, ℝ), ∫ x in (I : Set ℝ), u x * deriv φ x = -∫ x in (I : Set ℝ), g₂ x * φ x) :
    g₁ =ᵐ[volume.restrict I] g₂ := by
  have hw : ∀ {g : ℝ → ℝ}, MemLp g p (volume.restrict I) →
      (∀ φ : 𝓓(I, ℝ), ∫ x in (I : Set ℝ), u x * deriv φ x = -∫ x in (I : Set ℝ), g x * φ x) →
      HasWeakDerivOn u g I := fun hg h ↦
    hasWeakDerivOn_iff.2 ⟨hu.locallyIntegrableOn Fact.out, hg.locallyIntegrableOn Fact.out,
      fun φ ↦ by
        have := h φ
        simp only [mul_comm] at this ⊢
        exact this⟩
  exact (ae_restrict_iff' I.isOpen.measurableSet).2 ((hw hg₁ h₁).ae_eq (hw hg₂ h₂))

/-- **Remark 2.** If `u ∈ C¹(I) ∩ L^p(I)` and its usual derivative `u' ∈ L^p(I)`, then
`u ∈ W^{1,p}(I)`; the weak derivative is the usual one (`remark_8_2_deriv`). The backbone's
`memSobolevIntervalLp_of_contDiffOn`. -/
theorem remark_8_2 {u : ℝ → ℝ} (hu : ContDiffOn ℝ 1 u I) (hup : MemLp u p (volume.restrict I))
    (hup' : MemLp (deriv u) p (volume.restrict I)) : MemSobolevSpace p I u :=
  memSobolevSpace_iff_memSobolevIntervalLp.2 (memSobolevIntervalLp_of_contDiffOn hu hup hup').1

/-- **Remark 2, "so that notation is consistent".** For `u ∈ C¹(I)` the usual derivative
`deriv u` satisfies the defining identity of the weak derivative:
`∫_I u φ' = -∫_I (deriv u) φ` for every test function `φ`. -/
theorem remark_8_2_deriv {u : ℝ → ℝ} (hu : ContDiffOn ℝ 1 u I) (φ : 𝓓(I, ℝ)) :
    ∫ x in (I : Set ℝ), u x * deriv φ x = -∫ x in (I : Set ℝ), deriv u x * φ x := by
  have := (hasWeakDerivOn_of_contDiffOn hu).integral_deriv_mul φ
  simp only [mul_comm] at this ⊢
  exact this

/-- **Remark 2, last sentence.** If `I` is bounded, `C¹(Ī) ⊆ W^{1,p}(I)` for all `1 ≤ p ≤ ∞`.
The backbone's `memSobolevIntervalLp_of_contDiffOn_Icc`. -/
theorem remark_8_2_Icc {a b : ℝ} (hab : a < b) {u : ℝ → ℝ} (hu : ContDiffOn ℝ 1 u (Icc a b)) :
    MemSobolevSpace p (Opens.Ioo a b) u :=
  memSobolevSpace_iff_memSobolevIntervalLp.2 (memSobolevIntervalLp_of_contDiffOn_Icc hab hu).1

/-! ### Remark 1: the test class -/

/-- The support of a compactly supported function on `I` lies in a compact subinterval
`[lo, hi]` with `lo < hi` both in `I`, and the function vanishes at `lo` and `hi`; a point of `I`
serves when the support is empty. (The pattern of `TestFunction.exists_mem_tsupport_subset_Ioo`,
for an arbitrary function.) -/
private theorem exists_mem_tsupport_subset_Ioo_of_hasCompactSupport {f : ℝ → ℝ}
    (hf : HasCompactSupport f) (hfI : tsupport f ⊆ I) {y₀ : ℝ} (hy₀ : y₀ ∈ I) :
    ∃ lo hi : ℝ, lo ∈ I ∧ hi ∈ I ∧ lo ≤ hi ∧ tsupport f ⊆ Ioo lo hi := by
  obtain ⟨lo, hi, hlo, hhi, hlohi, hsupp⟩ : ∃ lo hi : ℝ, lo ∈ I ∧ hi ∈ I ∧ lo ≤ hi ∧
      tsupport f ⊆ Icc lo hi := by
    by_cases hne : (tsupport f).Nonempty
    · obtain ⟨lo, hlo⟩ := hf.exists_isLeast hne
      obtain ⟨hi, hhi⟩ := hf.exists_isGreatest hne
      exact ⟨lo, hi, hfI hlo.1, hfI hhi.1, hlo.2 hhi.1, fun t ht ↦ ⟨hlo.2 ht, hhi.2 ht⟩⟩
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      exact ⟨y₀, y₀, hy₀, hy₀, le_rfl, hne ▸ empty_subset _⟩
  obtain ⟨εl, hεl, hl⟩ := Metric.isOpen_iff.1 I.isOpen lo hlo
  obtain ⟨εh, hεh, hh⟩ := Metric.isOpen_iff.1 I.isOpen hi hhi
  refine ⟨lo - εl / 2, hi + εh / 2, hl ?_, hh ?_, by linarith, hsupp.trans ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
  · rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
  · exact Icc_subset_Ioo (by linarith) (by linarith)

/-- **Remark 1.** In the definition of `W^{1,p}` we could equally well have used `C_c^1(I)`
(Mathlib's `𝓓^{1}(I, ℝ)`) as the class of test functions: for `u, g ∈ L^p(I)`, the identity
`∫_I u φ' = -∫_I g φ` holds for all `φ ∈ C_c^∞(I)` iff it holds for all `φ ∈ C_c^1(I)`. The
book mollifies `φ ∈ C_c^1(I)`; here the identity for smooth test functions makes `u` the
function of an element of `W^{1,p}(I)` with derivative `g`, and the integration by parts
formula against a `C¹` factor (`SobolevIntervalLp.integral_deriv_mul_contDiffOn`, Corollary
8.10) on a compact subinterval containing the support of `φ` gives the identity for `φ`. -/
theorem remark_8_1 (hI : (I : Set ℝ).OrdConnected) {u g : ℝ → ℝ}
    (hu : MemLp u p (volume.restrict I)) (hg : MemLp g p (volume.restrict I)) :
    (∀ φ : 𝓓(I, ℝ), ∫ x in (I : Set ℝ), u x * deriv φ x = -∫ x in (I : Set ℝ), g x * φ x) ↔
      ∀ φ : 𝓓^{1}(I, ℝ), ∫ x in (I : Set ℝ), u x * deriv φ x = -∫ x in (I : Set ℝ), g x * φ x := by
  refine ⟨fun h φ ↦ ?_, fun h φ ↦
    h ⟨φ, φ.contDiff.of_le (mod_cast le_top), φ.hasCompactSupport, φ.tsupport_subset⟩⟩
  -- the element of `W^{1,p}(I)` carried by `u`, with derivative `g`
  have hweak : HasWeakDerivOn u g I :=
    hasWeakDerivOn_iff.2 ⟨hu.locallyIntegrableOn Fact.out, hg.locallyIntegrableOn Fact.out,
      fun ψ ↦ by
        have := h ψ
        simp only [mul_comm] at this ⊢
        exact this⟩
  obtain ⟨v, hv⟩ := (memSobolevIntervalLp_one_iff.2 ⟨hu, g, hweak, hg⟩).exists_sobolevIntervalLp
  have hv1 : ⇑(v.deriv 1) =ᵐ[volume.restrict I] g :=
    (ae_restrict_iff' I.isOpen.measurableSet).2
      ((v.hasWeakDerivOn_fn.congr_ae hv (EventuallyEq.refl _ _)).ae_eq hweak)
  have hurep : u =ᵐ[volume.restrict I] v.rep :=
    hv.symm.trans (SobolevIntervalLp.fn_ae_eq_rep hI v)
  -- a compact subinterval of `I` containing the support of `φ`
  by_cases hne : (tsupport φ).Nonempty
  · obtain ⟨y₀, hy₀⟩ : (I : Set ℝ).Nonempty := ⟨_, φ.tsupport_subset hne.some_mem⟩
    obtain ⟨lo, hi, hlo, hhi, -, hsupp⟩ :=
      exists_mem_tsupport_subset_Ioo_of_hasCompactSupport φ.hasCompactSupport
        φ.tsupport_subset hy₀
    have hIcc : Icc lo hi ⊆ I := hI.out hlo hhi
    have hφlo : φ lo = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ (hsupp h).1.ne rfl
    have hφhi : φ hi = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ (hsupp h).2.ne rfl
    have hφ' : ∀ x, x ∉ Ioc lo hi → deriv φ x = 0 := fun x hx ↦ by
      by_contra hd
      exact hx (Ioo_subset_Ioc_self (hsupp (support_deriv_subset hd)))
    have hφ0 : ∀ x, x ∉ Ioc lo hi → φ x = 0 := fun x hx ↦
      image_eq_zero_of_notMem_tsupport fun h ↦ hx (Ioo_subset_Ioc_self (hsupp h))
    have hlohi : lo ≤ hi := (hsupp hne.some_mem).1.le.trans (hsupp hne.some_mem).2.le
    -- both integrals live on `[lo, hi]`
    have e1' : (fun x ↦ u x * deriv φ x) =ᵐ[volume.restrict I] fun x ↦ v.rep x * deriv φ x :=
      hurep.mono fun x hx ↦ by simp only [hx]
    have e2' : (fun x ↦ g x * φ x) =ᵐ[volume.restrict I] fun x ↦ v.deriv 1 x * φ x :=
      hv1.mono fun x hx ↦ by simp only [hx]
    have e1 : ∫ x in (I : Set ℝ), u x * deriv φ x = ∫ x in lo..hi, v.rep x * deriv φ x := by
      rw [integral_congr_ae e1',
        setIntegral_eq_of_subset_of_forall_sdiff_eq_zero I.isOpen.measurableSet
          (Ioc_subset_Icc_self.trans hIcc) (fun x hx ↦ by rw [hφ' x hx.2, mul_zero]),
        intervalIntegral.integral_of_le hlohi]
    have e2 : ∫ x in (I : Set ℝ), g x * φ x = ∫ x in lo..hi, v.deriv 1 x * φ x := by
      rw [integral_congr_ae e2',
        setIntegral_eq_of_subset_of_forall_sdiff_eq_zero I.isOpen.measurableSet
          (Ioc_subset_Icc_self.trans hIcc) (fun x hx ↦ by rw [hφ0 x hx.2, mul_zero]),
        intervalIntegral.integral_of_le hlohi]
    rw [e1, e2, SobolevIntervalLp.integral_deriv_mul_contDiffOn hI v
      (subset_closure (hIcc (right_mem_Icc.2 hlohi)))
      (subset_closure (hIcc (left_mem_Icc.2 hlohi)))
      ((φ.contDiff.of_le (mod_cast le_rfl)).contDiffOn), hφlo, hφhi]
    ring
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have hφ0 : ∀ x, φ x = 0 := fun x ↦
      image_eq_zero_of_notMem_tsupport (by rw [hne]; exact notMem_empty x)
    have hφ' : ∀ x, deriv φ x = 0 := fun x ↦ by
      by_contra hd
      exact absurd (support_deriv_subset hd) (by rw [hne]; exact notMem_empty x)
    simp only [hφ0, hφ', mul_zero, integral_zero, neg_zero]

/-! ### The Examples -/

/-- **Examples (i).** On `I = (-1, 1)`, the function `u(x) = |x|` belongs to `W^{1,p}(I)` for
every `1 ≤ p ≤ ∞`. The backbone's `memSobolevIntervalLp_abs`. -/
theorem example_abs : MemSobolevSpace p (Opens.Ioo (-1) 1) fun x ↦ |x| :=
  memSobolevSpace_iff_memSobolevIntervalLp.2 memSobolevIntervalLp_abs.1

/-- **Examples (i), the derivative.** The weak derivative of `|x|` on `(-1, 1)` is the sign
function `g(x) = 1` for `0 < x < 1`, `g(x) = -1` for `-1 < x < 0`: `∫ |x| φ' = -∫ g φ` for every
test function `φ` on `(-1, 1)`. -/
theorem example_abs_deriv (φ : 𝓓(Opens.Ioo (-1) 1, ℝ)) :
    ∫ x in Ioo (-1 : ℝ) 1, |x| * deriv φ x
      = -∫ x in Ioo (-1 : ℝ) 1, (if 0 < x then 1 else -1) * φ x := by
  have := (memSobolevIntervalLp_abs (p := 1)).2.integral_deriv_mul φ
  simp only [mul_comm, Opens.coe_Ioo] at this ⊢
  exact this

/-- **Examples (i), "more generally".** A function continuous on `[a, b]` and piecewise `C¹`
there — `C¹` on the open panels of a partition `a = x₀ < x₁ < ⋯ < x_{N+1} = b`, with panel
derivatives bounded by a common constant — belongs to `W^{1,p}(a, b)` for all `1 ≤ p ≤ ∞`. The
backbone's `memSobolevIntervalLp_of_piecewise_contDiffOn`. -/
theorem example_piecewise_contDiff {a b : ℝ} {N : ℕ} {x : Fin (N + 2) → ℝ} (hx : StrictMono x)
    (hxa : x 0 = a) (hxb : x (Fin.last (N + 1)) = b) {g : ℝ → ℝ} (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ j : Fin (N + 1), ContDiffOn ℝ 1 g (Ioo (x j.castSucc) (x j.succ)))
    (hbdd : ∃ C, ∀ j : Fin (N + 1), ∀ t ∈ Ioo (x j.castSucc) (x j.succ), |deriv g t| ≤ C) :
    MemSobolevSpace p (Opens.Ioo a b) g :=
  memSobolevSpace_iff_memSobolevIntervalLp.2
    (memSobolevIntervalLp_of_piecewise_contDiffOn hx hxa hxb hg hg' hbdd).1

/-- **Examples (ii).** The sign function `g` of (i) does not belong to `W^{1,p}(-1, 1)` for any
`1 ≤ p ≤ ∞`. The backbone's `not_memSobolevIntervalLp_sign`. -/
theorem example_sign_not_mem :
    ¬ MemSobolevSpace p (Opens.Ioo (-1) 1) fun x ↦ if 0 < x then (1 : ℝ) else -1 := fun h ↦
  not_memSobolevIntervalLp_sign (memSobolevSpace_iff_memSobolevIntervalLp.1 h)

/-! ### The norm -/

/-- **Notation (§8.2), the norm.** `‖u‖_{W^{1,p}} = ‖u‖_{L^p} + ‖u'‖_{L^p}`. -/
def sobolevNorm (u : SobolevIntervalLp 1 p I) : ℝ := ‖u.deriv 0‖ + ‖u.deriv 1‖

/-- The book's norm is nonnegative. -/
theorem sobolevNorm_nonneg (u : SobolevIntervalLp 1 p I) : 0 ≤ sobolevNorm u :=
  add_nonneg (norm_nonneg _) (norm_nonneg _)

/-- **Notation (§8.2), "the equivalent norm".** The norm of the type,
`(‖u‖_p^p + ‖u'‖_p^p)^{1/p}` (`SobolevIntervalLp.norm_eq_sum`; `max (‖u‖_∞, ‖u'‖_∞)` at
`p = ∞`), is equivalent to the book's: `‖u‖ ≤ ‖u‖_{W^{1,p}} ≤ 2 ‖u‖`, for every `1 ≤ p ≤ ∞`. -/
theorem sobolevNorm_equiv (u : SobolevIntervalLp 1 p I) :
    ‖u‖ ≤ sobolevNorm u ∧ sobolevNorm u ≤ 2 * ‖u‖ := by
  refine ⟨(SobolevIntervalLp.norm_le_sum_norm_deriv u).trans_eq ?_, ?_⟩
  · rw [Fin.sum_univ_two]; rfl
  · have h0 := SobolevIntervalLp.norm_deriv_le u 0
    have h1 := SobolevIntervalLp.norm_deriv_le u 1
    unfold sobolevNorm
    linarith

/-- At `p = 1` the two norms coincide: `‖u‖ = ‖u‖_{L¹} + ‖u'‖_{L¹}`. -/
theorem sobolevNorm_eq_norm_of_one (u : SobolevIntervalLp 1 1 I) : sobolevNorm u = ‖u‖ := by
  rw [SobolevIntervalLp.norm_eq_sum ENNReal.one_ne_top, Fin.sum_univ_two]
  simp only [ENNReal.toReal_one, Real.rpow_one, div_one]
  rfl

/-- **Notation (§8.2), the scalar product of `H¹`.**
`(u, v)_{H¹} = (u, v)_{L²} + (u', v')_{L²} = ∫_I (u v + u' v')`. The backbone's
`SobolevIntervalLp.inner_eq_integral`. -/
theorem inner_H1 (u v : SobolevIntervalLp 1 2 I) :
    ⟪u, v⟫_ℝ = ∫ x in (I : Set ℝ), (u.fn x * v.fn x + u.deriv 1 x * v.deriv 1 x) :=
  SobolevIntervalLp.inner_eq_integral u v

/-- **Notation (§8.2), the norm of `H¹`.** `‖u‖_{H¹} = (‖u‖_{L²}^2 + ‖u'‖_{L²}^2)^{1/2}`: the
norm of the type is the one associated with the scalar product. -/
theorem norm_H1_sq (u : SobolevIntervalLp 1 2 I) :
    ‖u‖ ^ 2 = ‖u.deriv 0‖ ^ 2 + ‖u.deriv 1‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, SobolevIntervalLp.inner_eq, Fin.sum_univ_two,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

/-! ### Proposition 8.1 -/

/-- **Proposition 8.1, first clause.** `W^{1,p}(I)` is a Banach space for `1 ≤ p ≤ ∞` (the
instance `SobolevMultiIndex.instCompleteSpace`; the book's proof is Remark 4's closedness of
the weak derivative under `L^p` limits). -/
theorem proposition_8_1_banach : CompleteSpace (SobolevIntervalLp 1 p I) := inferInstance

/-- **Proposition 8.1, second clause.** `W^{1,p}(I)` is reflexive for `1 < p < ∞`: the map
`u ↦ (u, u')` embeds it isometrically as a closed subspace of the reflexive product
`L^p(I) × L^p(I)` (chapter 4's `theorem_4_10` for the factors, the backbone's
`SobolevMultiIndex.instIsReflexive` for the closed subspace). -/
theorem proposition_8_1_reflexive (hp1 : 1 < p) (hp : p ≠ ∞) :
    NormedSpace.IsReflexive ℝ (SobolevIntervalLp 1 p I) :=
  have : NormedSpace.IsReflexive ℝ (Lp ℝ p (volume.restrict (I : Set ℝ))) :=
    Brezis.Chapter04.theorem_4_10 hp1 hp
  inferInstance

/-- **Proposition 8.1, third clause.** `W^{1,p}(I)` is separable for `1 ≤ p < ∞` (the factors
`L^p(I)` are, chapter 4's `theorem_4_13`; the backbone's
`SobolevMultiIndex.instSecondCountableTopology`). -/
theorem proposition_8_1_separable (hp : p ≠ ∞) :
    TopologicalSpace.SeparableSpace (SobolevIntervalLp 1 p I) :=
  have : Fact (p ≠ ∞) := ⟨hp⟩
  have : SecondCountableTopology (SobolevIntervalLp 1 p I) :=
    SobolevMultiIndex.instSecondCountableTopology
  TopologicalSpace.SecondCountableTopology.to_separableSpace

/-- **Proposition 8.1, last clause.** `H¹(I)` is a separable Hilbert space: its norm is the one
of its scalar product (`inner_H1`, `norm_H1_sq`), it is complete and separable. (Mathlib bundles
no `HilbertSpace`; the pair `[InnerProductSpace ℝ H] [CompleteSpace H]` is what the surface
carries, as in chapter 5.) -/
theorem proposition_8_1_hilbert :
    (∀ u : SobolevIntervalLp 1 2 I, ‖u‖ = √⟪u, u⟫_ℝ) ∧ CompleteSpace (SobolevIntervalLp 1 2 I) ∧
      TopologicalSpace.SeparableSpace (SobolevIntervalLp 1 2 I) :=
  ⟨fun u ↦ norm_eq_sqrt_real_inner u, inferInstance, proposition_8_1_separable ENNReal.ofNat_ne_top⟩

/-- **Proposition 8.1.** The space `W^{1,p}(I)` is a Banach space for `1 ≤ p ≤ ∞`; it is
reflexive for `1 < p < ∞` and separable for `1 ≤ p < ∞`. The space `H¹(I)` is a separable
Hilbert space. -/
theorem proposition_8_1 :
    CompleteSpace (SobolevIntervalLp 1 p I) ∧
      (1 < p → p ≠ ∞ → NormedSpace.IsReflexive ℝ (SobolevIntervalLp 1 p I)) ∧
      (p ≠ ∞ → TopologicalSpace.SeparableSpace (SobolevIntervalLp 1 p I)) ∧
      ((∀ u : SobolevIntervalLp 1 2 I, ‖u‖ = √⟪u, u⟫_ℝ) ∧
        CompleteSpace (SobolevIntervalLp 1 2 I) ∧
        TopologicalSpace.SeparableSpace (SobolevIntervalLp 1 2 I)) :=
  ⟨proposition_8_1_banach, proposition_8_1_reflexive, proposition_8_1_separable,
    proposition_8_1_hilbert⟩

/-! ### Remark 4 -/

/-- **Remark 4, first clause.** Let `(u_n)` be a sequence in `W^{1,p}(I)` such that `u_n → v`
in `L^p(I)` and `(u_n')` converges to some `w` in `L^p(I)`; then `v ∈ W^{1,p}(I)`, and the
element `v'` of `W^{1,p}(I)` carried by `v` (with derivative `w`) is the limit of `u_n` in
`W^{1,p}(I)`: `‖u_n − v'‖_{W^{1,p}} → 0`. The backbone's `hasWeakDerivOn_of_tendsto_eLpNorm`
and `SobolevIntervalLp.tendsto_of_tendsto_deriv`. -/
theorem remark_8_4_a {u : ℕ → SobolevIntervalLp 1 p I} {v w : ℝ → ℝ}
    (hv : MemLp v p (volume.restrict I)) (hw : MemLp w p (volume.restrict I))
    (hlv : Tendsto (fun n ↦ eLpNorm ((u n).fn - v) p (volume.restrict I)) atTop (𝓝 0))
    (hlw : Tendsto (fun n ↦ eLpNorm (⇑((u n).deriv 1) - w) p (volume.restrict I)) atTop (𝓝 0)) :
    MemSobolevSpace p I v ∧ ∃ v' : SobolevIntervalLp 1 p I,
      v'.fn =ᵐ[volume.restrict I] v ∧ ⇑(v'.deriv 1) =ᵐ[volume.restrict I] w ∧
        Tendsto u atTop (𝓝 v') := by
  have hweak : HasWeakDerivOn v w I :=
    hasWeakDerivOn_of_tendsto_eLpNorm (fun n ↦ (u n).hasWeakDerivOn_fn) hv hw hlv hlw
  refine ⟨memSobolevSpace_iff_memSobolevIntervalLp.2
    (memSobolevIntervalLp_one_iff.2 ⟨hv, w, hweak, hw⟩), ?_⟩
  let v' : SobolevIntervalLp 1 p I := SobolevIntervalLp.mk ![hv.toLp v, hw.toLp w] fun j ↦ by
    fin_cases j
    · exact HasWeakIteratedLineDerivOn.of_length_eq_zero rfl _
        ((Lp.memLp _).locallyIntegrableOn (Ω := I) Fact.out)
    · exact hweak.congr_ae hv.coeFn_toLp.symm hw.coeFn_toLp.symm
  refine ⟨v', hv.coeFn_toLp, hw.coeFn_toLp, SobolevIntervalLp.tendsto_of_tendsto_deriv fun j ↦ ?_⟩
  fin_cases j
  · exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm (fun n ↦ (u n).deriv 0) v hv).2 hlv
  · exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm (fun n ↦ (u n).deriv 1) w hw).2 hlw

/-- **Remark 4, second clause** ("see Exercise 8.2"). When `1 < p ≤ ∞` it suffices to know
that `u_n → v` in `L^p(I)` and that `‖u_n'‖_{L^p}` stays bounded to conclude that
`v ∈ W^{1,p}(I)`. The backbone's
`SobolevIntervalLp.memSobolevIntervalLp_of_tendsto_of_bounded_deriv` (the bound of Proposition
8.3 (ii) passes to the limit). -/
theorem remark_8_4_b (hp : 1 < p) {u : ℕ → SobolevIntervalLp 1 p I} {M : ℝ}
    (hM : ∀ n, ‖(u n).deriv 1‖ ≤ M) {v : ℝ → ℝ} (hv : MemLp v p (volume.restrict I))
    (hlv : Tendsto (fun n ↦ eLpNorm ((u n).fn - v) p (volume.restrict I)) atTop (𝓝 0)) :
    MemSobolevSpace p I v :=
  have := ENNReal.holderConjugate_sub_inv_inv (p := p)
  memSobolevSpace_iff_memSobolevIntervalLp.2
    (SobolevIntervalLp.memSobolevIntervalLp_of_tendsto_of_bounded_deriv
      ((ENNReal.HolderConjugate.lt_top_iff_one_lt (1 - p⁻¹)⁻¹ p).2 hp).ne hM hv hlv)

/-- **Remark 4.** Both clauses: a sequence of `W^{1,p}(I)` converging in `L^p(I)` whose
derivatives converge in `L^p(I)` converges in `W^{1,p}(I)` to an element of `W^{1,p}(I)`; and
for `1 < p ≤ ∞` a bounded sequence of derivatives already forces the `L^p` limit into
`W^{1,p}(I)`. -/
theorem remark_8_4 {u : ℕ → SobolevIntervalLp 1 p I} {v : ℝ → ℝ}
    (hv : MemLp v p (volume.restrict I))
    (hlv : Tendsto (fun n ↦ eLpNorm ((u n).fn - v) p (volume.restrict I)) atTop (𝓝 0)) :
    (∀ w : ℝ → ℝ, MemLp w p (volume.restrict I) →
      Tendsto (fun n ↦ eLpNorm (⇑((u n).deriv 1) - w) p (volume.restrict I)) atTop (𝓝 0) →
      MemSobolevSpace p I v ∧ ∃ v' : SobolevIntervalLp 1 p I,
        v'.fn =ᵐ[volume.restrict I] v ∧ Tendsto u atTop (𝓝 v')) ∧
    (1 < p → ∀ M : ℝ, (∀ n, ‖(u n).deriv 1‖ ≤ M) → MemSobolevSpace p I v) :=
  ⟨fun _ hw hlw ↦
    let ⟨h₁, v', hv', _, hlim⟩ := remark_8_4_a hv hw hlv hlw
    ⟨h₁, v', hv', hlim⟩,
    fun hp _ hM ↦ remark_8_4_b hp hM hv hlv⟩

/-! ### Theorem 8.2 and its lemmas -/

/-- **Theorem 8.2.** Let `u ∈ W^{1,p}(I)` with `1 ≤ p ≤ ∞`, `I` bounded or unbounded; then
there is a function `ũ ∈ C(Ī)` with `u = ũ` a.e. on `I` and
`ũ(x) − ũ(y) = ∫_y^x u'(t) dt` for all `x, y ∈ Ī`. The backbone's
`SobolevIntervalLp.exists_continuousOn_closure_ae_eq`; the canonical choice, used as "`u(x)`"
from now on, is `SobolevIntervalLp.rep u`. -/
theorem theorem_8_2 (hI : (I : Set ℝ).OrdConnected) (u : SobolevIntervalLp 1 p I) :
    ∃ ũ : ℝ → ℝ, ContinuousOn ũ (closure (I : Set ℝ)) ∧ u.fn =ᵐ[volume.restrict I] ũ ∧
      ∀ x ∈ closure (I : Set ℝ), ∀ y ∈ closure (I : Set ℝ),
        ũ x - ũ y = ∫ t in y..x, u.deriv 1 t :=
  let ⟨g, hg, hu, h⟩ := SobolevIntervalLp.exists_continuousOn_closure_ae_eq hI u
  ⟨g, hg, hu, fun x hx y hy ↦ h y hy x hx⟩

/-- **Remark 5, first sentence.** If `u ∈ W^{1,p}(I)` then all functions `v` with `v = u`
a.e. on `I` also belong to `W^{1,p}(I)` (directly from the definition). -/
theorem remark_8_5_congr {u v : ℝ → ℝ} (hu : MemSobolevSpace p I u)
    (hvu : v =ᵐ[volume.restrict I] u) : MemSobolevSpace p I v :=
  memSobolevSpace_iff_memSobolevIntervalLp.2
    ((memSobolevSpace_iff_memSobolevIntervalLp.1 hu).congr_ae hvu.symm)

/-- **Remark 5, second sentence.** Every `u ∈ W^{1,p}(I)` admits one (Theorem 8.2) and only one
continuous representative on `Ī`: two functions continuous on `Ī` both equal to `u` a.e. on `I`
agree on `Ī`. The backbone's `SobolevIntervalLp.rep_eq_of_continuousOn`. -/
theorem remark_8_5_unique (hI : (I : Set ℝ).OrdConnected) (u : SobolevIntervalLp 1 p I)
    {g₁ g₂ : ℝ → ℝ} (hg₁ : ContinuousOn g₁ (closure (I : Set ℝ)))
    (hg₂ : ContinuousOn g₂ (closure (I : Set ℝ))) (hu₁ : u.fn =ᵐ[volume.restrict I] g₁)
    (hu₂ : u.fn =ᵐ[volume.restrict I] g₂) : EqOn g₁ g₂ (closure (I : Set ℝ)) := fun _ hx ↦
  (SobolevIntervalLp.rep_eq_of_continuousOn hI u hg₁ hu₁ hx).symm.trans
    (SobolevIntervalLp.rep_eq_of_continuousOn hI u hg₂ hu₂ hx)

/-- **Remark 5.** Membership of `W^{1,p}(I)` only depends on the a.e. class, and the continuous
representative of Theorem 8.2 is unique. -/
theorem remark_8_5 (hI : (I : Set ℝ).OrdConnected) :
    (∀ u v : ℝ → ℝ, MemSobolevSpace p I u → v =ᵐ[volume.restrict I] u → MemSobolevSpace p I v) ∧
    ∀ (u : SobolevIntervalLp 1 p I) (g₁ g₂ : ℝ → ℝ), ContinuousOn g₁ (closure (I : Set ℝ)) →
      ContinuousOn g₂ (closure (I : Set ℝ)) → u.fn =ᵐ[volume.restrict I] g₁ →
      u.fn =ᵐ[volume.restrict I] g₂ → EqOn g₁ g₂ (closure (I : Set ℝ)) :=
  ⟨fun _ _ hu hvu ↦ remark_8_5_congr hu hvu,
    fun u _ _ hg₁ hg₂ hu₁ hu₂ ↦ remark_8_5_unique hI u hg₁ hg₂ hu₁ hu₂⟩

omit [Fact (1 ≤ p)] in
/-- **Remark 6.** If `u ∈ W^{1,p}(I)` and `u'` admits a continuous representative `g` on `Ī`,
then `ũ ∈ C¹(Ī)`, with derivative `g`. The backbone's
`SobolevIntervalLp.contDiffOn_rep_of_continuousOn_deriv`. -/
theorem remark_8_6 (hI : (I : Set ℝ).OrdConnected) (u : SobolevIntervalLp 1 p I) {g : ℝ → ℝ}
    (hg : ContinuousOn g (closure (I : Set ℝ))) (hu : ⇑(u.deriv 1) =ᵐ[volume.restrict I] g) :
    ContDiffOn ℝ 1 u.rep (closure (I : Set ℝ)) ∧
      ∀ x ∈ closure (I : Set ℝ), HasDerivWithinAt u.rep (g x) (closure (I : Set ℝ)) x :=
  SobolevIntervalLp.contDiffOn_rep_of_continuousOn_deriv hI u hg hu

/-- **Lemma 8.1** (du Bois-Reymond). Let `f ∈ L¹_loc(I)` be such that `∫_I f φ' = 0` for all
test functions `φ`. Then there is a constant `C` with `f = C` a.e. on `I`. The backbone's
`HasWeakDerivOn.exists_ae_eq_const`. -/
theorem lemma_8_1 (hI : (I : Set ℝ).OrdConnected) {f : ℝ → ℝ} (hf : LocallyIntegrableOn f I)
    (h : ∀ φ : 𝓓(I, ℝ), ∫ x in (I : Set ℝ), f x * deriv φ x = 0) :
    ∃ C : ℝ, f =ᵐ[volume.restrict I] fun _ ↦ C := by
  refine HasWeakDerivOn.exists_ae_eq_const hI (hasWeakDerivOn_iff.2
    ⟨hf, (locallyIntegrable_const 0).locallyIntegrableOn _, fun φ ↦ ?_⟩)
  simp only [Pi.zero_apply, mul_zero, integral_zero, neg_zero]
  have := h φ
  simp only [mul_comm] at this ⊢
  exact this

/-- **Lemma 8.2.** Let `g ∈ L¹_loc(I)`; for `y₀` fixed in `I` set `v(x) = ∫_{y₀}^x g(t) dt`.
Then `v ∈ C(I)` and `∫_I v φ' = -∫_I g φ` for all test functions `φ`. The backbone's
`MeasureTheory.LocallyIntegrableOn.hasWeakDerivOn_integral` (by integration by parts for
absolutely continuous functions, not by the book's Fubini argument) and
`continuousOn_integral`. -/
theorem lemma_8_2 (hI : (I : Set ℝ).OrdConnected) {g : ℝ → ℝ} (hg : LocallyIntegrableOn g I)
    {y₀ : ℝ} (hy₀ : y₀ ∈ I) :
    ContinuousOn (fun x ↦ ∫ t in y₀..x, g t) I ∧ ∀ φ : 𝓓(I, ℝ),
      ∫ x in (I : Set ℝ), (∫ t in y₀..x, g t) * deriv φ x
        = -∫ x in (I : Set ℝ), g x * φ x := by
  have h1 := hg.continuousOn_integral hI hy₀ 0
  have h2 := hg.hasWeakDerivOn_integral hI hy₀ 0
  simp only [zero_add] at h1 h2
  refine ⟨h1, fun φ ↦ ?_⟩
  have := h2.integral_deriv_mul φ
  simp only [mul_comm] at this ⊢
  exact this

/-- **Remark 7.** The primitive `v = ∫_{y₀}^x g` of a function `g ∈ L^p(I)` belongs to
`W^{1,p}(I)` provided `v ∈ L^p(I)`. The backbone's `memSobolevIntervalLp_integral`. -/
theorem remark_8_7 (hI : (I : Set ℝ).OrdConnected) {g : ℝ → ℝ} (hg : MemLp g p (volume.restrict I))
    {y₀ : ℝ} (hy₀ : y₀ ∈ I) (hv : MemLp (fun x ↦ ∫ t in y₀..x, g t) p (volume.restrict I)) :
    MemSobolevSpace p I fun x ↦ ∫ t in y₀..x, g t := by
  have := (memSobolevIntervalLp_integral hI hg hy₀ (c := 0) (by simpa only [zero_add] using hv)).1
  simp only [zero_add] at this
  exact memSobolevSpace_iff_memSobolevIntervalLp.2 this

/-- **Remark 7, "which is always the case when `I` is bounded".** On a bounded interval the
primitive of `g ∈ L^p(a, b)` is continuous on `[a, b]`, hence in `L^p(a, b)`, hence in
`W^{1,p}(a, b)`. -/
theorem remark_8_7_of_bounded {a b : ℝ} (hab : a < b) {g : ℝ → ℝ}
    (hg : MemLp g p (volume.restrict (Ioo a b))) {y₀ : ℝ} (hy₀ : y₀ ∈ Ioo a b) :
    MemSobolevSpace p (Opens.Ioo a b) fun x ↦ ∫ t in y₀..x, g t := by
  have hI := SobolevIntervalLp.ordConnected_coe_Ioo a b
  have hcl := SobolevIntervalLp.closure_coe_Ioo hab
  refine remark_8_7 hI hg hy₀ ?_
  have hcont : ContinuousOn (fun x ↦ 0 + ∫ t in y₀..x, g t) (Icc a b) :=
    continuousOn_integral_of_intervalIntegrable (s := Icc a b) (Ioo_subset_Icc_self hy₀)
      (fun x hx y hy ↦ hg.intervalIntegrable_of_mem_closure hI (I := Opens.Ioo a b)
        (hcl ▸ hx) (hcl ▸ hy)) 0
  simp only [zero_add] at hcont
  exact hcont.memLp_top_restrict_Ioo.mono_exponent le_top

/-! ### Propositions 8.3–8.5 -/

/-- **Proposition 8.3, (i) ⇒ (ii) with the constant `C = ‖u'‖_{L^p(I)}`** (valid for every
`1 ≤ p ≤ ∞`, Remark 8): for `u ∈ W^{1,p}(I)` and `p'` the conjugate exponent,
`|∫_I u φ'| ≤ ‖u'‖_{L^p(I)} ‖φ‖_{L^{p'}(I)}` for every test function `φ`. The backbone's
`SobolevIntervalLp.abs_integral_mul_deriv_le`. -/
theorem proposition_8_3_const {q : ℝ≥0∞} [p.HolderConjugate q] (u : SobolevIntervalLp 1 p I)
    (φ : 𝓓(I, ℝ)) :
    |∫ x in (I : Set ℝ), u.fn x * deriv φ x|
      ≤ ‖u.deriv 1‖ * (eLpNorm φ q (volume.restrict I)).toReal :=
  SobolevIntervalLp.abs_integral_mul_deriv_le u φ

/-- **Proposition 8.3.** Let `u ∈ L^p(I)` with `1 < p ≤ ∞` and `p'` the conjugate exponent. Then
`u ∈ W^{1,p}(I)` if and only if there is a constant `C` with
`|∫_I u φ'| ≤ C ‖φ‖_{L^{p'}(I)}` for all test functions `φ`. The backbone's
`memSobolevIntervalLp_iff_forall_abs_integral_mul_deriv_le` (the converse through the Riesz
representation theorem, as in the book). -/
theorem proposition_8_3 {q : ℝ≥0∞} [p.HolderConjugate q] (hp : 1 < p) {u : ℝ → ℝ}
    (hu : MemLp u p (volume.restrict I)) :
    MemSobolevSpace p I u ↔ ∃ C : ℝ, ∀ φ : 𝓓(I, ℝ),
      |∫ x in (I : Set ℝ), u x * deriv φ x| ≤ C * (eLpNorm φ q (volume.restrict I)).toReal :=
  memSobolevSpace_iff_memSobolevIntervalLp.trans
    (memSobolevIntervalLp_iff_forall_abs_integral_mul_deriv_le
      ((ENNReal.HolderConjugate.lt_top_iff_one_lt q p).2 hp).ne hu)

/-- **Remark 8, first sentence.** When `p = 1` the implication (i) ⇒ (ii) of Proposition 8.3
remains true (with `p' = ∞`): `|∫_I u φ'| ≤ ‖u'‖_{L¹(I)} ‖φ‖_{L^∞(I)}` for `u ∈ W^{1,1}(I)`. -/
theorem remark_8_8_one (u : SobolevIntervalLp 1 1 I) (φ : 𝓓(I, ℝ)) :
    |∫ x in (I : Set ℝ), u.fn x * deriv φ x|
      ≤ ‖u.deriv 1‖ * (eLpNorm φ ∞ (volume.restrict I)).toReal :=
  SobolevIntervalLp.abs_integral_mul_deriv_le u φ

/-- **Remark 8, absolutely continuous functions.** On a bounded interval `I = (a, b)`, the
functions of `W^{1,1}(I)` are the absolutely continuous functions (property (AC)): `u` lies
in `W^{1,1}(a, b)` iff it agrees a.e. with a function absolutely continuous on `[a, b]`
(Mathlib's `AbsolutelyContinuousOnInterval`). The backbone's
`memSobolevIntervalLp_one_one_iff_absolutelyContinuousOnInterval`. -/
theorem remark_8_8_absolutelyContinuous {a b : ℝ} (hab : a < b) {u : ℝ → ℝ} :
    MemSobolevSpace 1 (Opens.Ioo a b) u ↔
      ∃ g : ℝ → ℝ, AbsolutelyContinuousOnInterval g a b ∧ u =ᵐ[volume.restrict (Ioo a b)] g :=
  memSobolevSpace_iff_memSobolevIntervalLp.trans
    (memSobolevIntervalLp_one_one_iff_absolutelyContinuousOnInterval hab)

/-- **Remark 8**, the two clauses that are formalized: (i) ⇒ (ii) of Proposition 8.3 at `p = 1`,
and `W^{1,1}(a, b)` as the space of absolutely continuous functions. (The failure of the
converse at `p = 1` and the characterizations (a)–(c) of the functions of bounded variation
are not formalized.) -/
theorem remark_8_8 :
    (∀ (u : SobolevIntervalLp 1 1 I) (φ : 𝓓(I, ℝ)), |∫ x in (I : Set ℝ), u.fn x * deriv φ x|
      ≤ ‖u.deriv 1‖ * (eLpNorm φ ∞ (volume.restrict I)).toReal) ∧
    ∀ a b : ℝ, a < b → ∀ u : ℝ → ℝ, MemSobolevSpace 1 (Opens.Ioo a b) u ↔
      ∃ g : ℝ → ℝ, AbsolutelyContinuousOnInterval g a b ∧ u =ᵐ[volume.restrict (Ioo a b)] g :=
  ⟨remark_8_8_one, fun _ _ hab _ ↦ remark_8_8_absolutelyContinuous hab⟩

/-- **Proposition 8.4.** A function `u ∈ L^∞(I)` belongs to `W^{1,∞}(I)` if and only if there
is a constant `C` with `|u(x) − u(y)| ≤ C |x − y|` for a.e. `x, y ∈ I`. The backbone's
`memSobolevIntervalLp_top_iff_lipschitz` (through the absolutely continuous calculus rather
than the book's Proposition 8.3). -/
theorem proposition_8_4 (hI : (I : Set ℝ).OrdConnected) {u : ℝ → ℝ}
    (hu : MemLp u ∞ (volume.restrict I)) :
    MemSobolevSpace ∞ I u ↔
      ∃ C : ℝ, ∀ᵐ x ∂(volume.restrict I), ∀ᵐ y ∂(volume.restrict I), |u x - u y| ≤ C * |x - y| :=
  memSobolevSpace_iff_memSobolevIntervalLp.trans (memSobolevIntervalLp_top_iff_lipschitz hI hu)

/-- **Proposition 8.5, (i) ⇒ (ii) with the constant `C = ‖u'‖_{L^p(ℝ)}`** (valid for `p = 1`
too): for `u ∈ W^{1,p}(ℝ)` and every `h ∈ ℝ`, `‖τ_h u − u‖_{L^p(ℝ)} ≤ |h| ‖u'‖_{L^p(ℝ)}`, where
`(τ_h u)(x) = u(x + h)` and `u` stands for its continuous representative. The backbone's
`SobolevIntervalLp.eLpNorm_translate_sub_le`. -/
theorem proposition_8_5_const (u : SobolevIntervalLp 1 p ⊤) (h : ℝ) :
    eLpNorm (fun x ↦ u.rep (x + h) - u.rep x) p volume
      ≤ ENNReal.ofReal |h| * eLpNorm (u.deriv 1) p volume :=
  SobolevIntervalLp.eLpNorm_translate_sub_le u h

/-- **Proposition 8.5.** Let `u ∈ L^p(ℝ)` with `1 < p < ∞`. Then `u ∈ W^{1,p}(ℝ)` if and only if
there is a constant `C` with `‖τ_h u − u‖_{L^p(ℝ)} ≤ C |h|` for all `h ∈ ℝ`, where
`(τ_h u)(x) = u(x + h)`. The backbone's `memSobolevIntervalLp_of_eLpNorm_translate_sub_le`
(the converse, by Proposition 8.3, which holds for `p = ∞` too — the hypothesis `p ≠ ∞` is the
book's and is not used) and `eLpNorm_translate_sub_le`. -/
theorem proposition_8_5 (hp1 : 1 < p) (_hp : p ≠ ∞) {u : ℝ → ℝ} (hu : MemLp u p volume) :
    MemSobolevSpace p ⊤ u ↔
      ∃ C : ℝ, ∀ h : ℝ, eLpNorm (fun x ↦ u (x + h) - u x) p volume ≤ ENNReal.ofReal (C * |h|) := by
  have := ENNReal.holderConjugate_sub_inv_inv (p := p)
  have hq : (1 - p⁻¹)⁻¹ ≠ ⊤ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt (1 - p⁻¹)⁻¹ p).2 hp1).ne
  have hu' : MemLp u p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) := by
    rwa [Opens.coe_top, Measure.restrict_univ]
  rw [memSobolevSpace_iff_memSobolevIntervalLp]
  constructor
  · intro h
    obtain ⟨v, hv⟩ := h.exists_sobolevIntervalLp
    have hne : eLpNorm (⇑(v.deriv 1)) p volume ≠ ⊤ :=
      (SobolevIntervalLp.memLp_restrict_top_iff.1 (Lp.memLp (v.deriv 1))).eLpNorm_ne_top
    refine ⟨(eLpNorm (⇑(v.deriv 1)) p volume).toReal, fun t ↦ ?_⟩
    have hv' : u =ᵐ[volume] v.rep :=
      (SobolevIntervalLp.eventuallyEq_restrict_top_iff.1 hv).symm.trans
        (SobolevIntervalLp.eventuallyEq_restrict_top_iff.1
          (SobolevIntervalLp.fn_ae_eq_rep Opens.ordConnected_top v))
    have h1 : (fun x ↦ u (x + t)) =ᵐ[volume] fun x ↦ v.rep (x + t) :=
      (measurePreserving_add_right volume t).quasiMeasurePreserving.ae_eq_comp hv'
    have h2 : (fun x ↦ u (x + t) - u x) =ᵐ[volume] fun x ↦ v.rep (x + t) - v.rep x :=
      h1.sub hv'
    rw [eLpNorm_congr_ae h2, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hne, mul_comm]
    exact proposition_8_5_const v t
  · rintro ⟨C, hC⟩
    exact (memSobolevIntervalLp_of_eLpNorm_translate_sub_le hq hu hC).1

/-! ### Theorem 8.6, the extension operator -/

/-- **Theorem 8.6** (extension operator), with the constants of footnote 6. Let `1 ≤ p ≤ ∞` and
`I` a nonempty open interval. There is a bounded linear operator `P : W^{1,p}(I) → W^{1,p}(ℝ)`
such that (i) `Pu|_I = u`, (ii) `‖Pu‖_{L^p(ℝ)} ≤ 4 ‖u‖_{L^p(I)}`, and (iii)
`‖Pu‖_{W^{1,p}(ℝ)} ≤ 4 (1 + 1/|I|) ‖u‖_{W^{1,p}(I)}` in the book's norm, where `1/|I| = 0` when
`|I| = ∞` (`|I| = (volume I).toReal`). The backbone's `SobolevIntervalLp.extensionCLM`. -/
theorem theorem_8_6_const (hI : (I : Set ℝ).OrdConnected) (hne : (I : Set ℝ).Nonempty) :
    ∃ P : SobolevIntervalLp 1 p I →L[ℝ] SobolevIntervalLp 1 p ⊤,
      (∀ u, (P u).fn =ᵐ[volume.restrict I] u.fn) ∧
      (∀ u, ‖(P u).deriv 0‖ ≤ 4 * ‖u.deriv 0‖) ∧
      ∀ u, sobolevNorm (P u) ≤ 4 * (1 + (volume (I : Set ℝ)).toReal⁻¹) * sobolevNorm u := by
  refine ⟨SobolevIntervalLp.extensionCLM hI hne, SobolevIntervalLp.fn_extensionCLM hI hne,
    SobolevIntervalLp.norm_deriv_extensionCLM_zero_le hI hne, fun u ↦ ?_⟩
  have h0 := SobolevIntervalLp.norm_deriv_extensionCLM_zero_le hI hne u
  have h1 := SobolevIntervalLp.norm_deriv_extensionCLM_one_le hI hne u
  have hk : 0 ≤ (volume (I : Set ℝ)).toReal⁻¹ := by positivity
  have hn0 := norm_nonneg (u.deriv 0)
  have hn1 := norm_nonneg (u.deriv 1)
  unfold sobolevNorm
  nlinarith

/-- **Theorem 8.6** (extension operator). Let `1 ≤ p ≤ ∞` and `I` a nonempty open interval.
There is a bounded linear operator `P : W^{1,p}(I) → W^{1,p}(ℝ)`, called an extension operator,
with (i) `Pu|_I = u`, (ii) `‖Pu‖_{L^p(ℝ)} ≤ C ‖u‖_{L^p(I)}`, (iii)
`‖Pu‖_{W^{1,p}(ℝ)} ≤ C ‖u‖_{W^{1,p}(I)}` for all `u ∈ W^{1,p}(I)`, where `C` depends only on
`|I| ≤ ∞` (`theorem_8_6_const` gives the value). -/
theorem theorem_8_6 (hI : (I : Set ℝ).OrdConnected) (hne : (I : Set ℝ).Nonempty) :
    ∃ (P : SobolevIntervalLp 1 p I →L[ℝ] SobolevIntervalLp 1 p ⊤) (C : ℝ),
      (∀ u, (P u).fn =ᵐ[volume.restrict I] u.fn) ∧
      (∀ u, ‖(P u).deriv 0‖ ≤ C * ‖u.deriv 0‖) ∧
      ∀ u, sobolevNorm (P u) ≤ C * sobolevNorm u := by
  obtain ⟨P, h1, h2, h3⟩ := theorem_8_6_const (p := p) hI hne
  have hk : 0 ≤ (volume (I : Set ℝ)).toReal⁻¹ := by positivity
  refine ⟨P, 4 * (1 + (volume (I : Set ℝ)).toReal⁻¹), h1, fun u ↦ (h2 u).trans ?_, h3⟩
  have := norm_nonneg (u.deriv 0)
  nlinarith

/-- **Lemma 8.3.** Let `u ∈ W^{1,p}(0, 1)`, and let `η ∈ C^∞(ℝ)` with `η(x) = 0` for
`x > 3/4` (the book's `η`, equal to `1` on `x < 1/4`, is not needed here). Then, `ũ` denoting
the extension of `u` by `0` to `(0, ∞)`, `η ũ ∈ W^{1,p}(0, ∞)` and
`(η ũ)' = η' ũ + η ũ'`. The backbone's
`HasWeakDerivOn.indicator_mul_of_tsupport_inter_subset`, the book's integration by parts
against `η φ ∈ C_c^1((0, 1))`. -/
theorem lemma_8_3 (u : SobolevIntervalLp 1 p (Opens.Ioo 0 1)) {η : ℝ → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη0 : ∀ x, 3 / 4 < x → η x = 0) :
    MemSobolevSpace p (Opens.Ioi 0) ((Ioo 0 1).indicator fun x ↦ η x * u.rep x) ∧
      ∀ φ : 𝓓(Opens.Ioi 0, ℝ),
        ∫ x in Ioi (0 : ℝ), (Ioo 0 1).indicator (fun x ↦ η x * u.rep x) x * deriv φ x
          = -∫ x in Ioi (0 : ℝ),
              (Ioo 0 1).indicator (fun x ↦ deriv η x * u.rep x + η x * u.deriv 1 x) x * φ x := by
  have hI := SobolevIntervalLp.ordConnected_coe_Ioo 0 1
  have hIJ : Opens.Ioo 0 1 ≤ Opens.Ioi 0 := fun x hx ↦ hx.1
  have hsupp : tsupport η ∩ ((Opens.Ioi 0 : Opens ℝ) : Set ℝ) ⊆ (Opens.Ioo 0 1 : Opens ℝ) := by
    rintro x ⟨hx, hx0⟩
    have hle : x ≤ 3 / 4 := by
      by_contra hlt
      push Not at hlt
      have : x ∈ (Function.support η)ᶜ := fun h ↦ h (hη0 x hlt)
      have hcl : tsupport η ⊆ Iic (3 / 4) := by
        refine closure_minimal (fun y hy ↦ ?_) isClosed_Iic
        by_contra hy'
        exact hy (hη0 y (not_le.1 hy'))
      exact absurd (hcl hx) (not_le.2 hlt)
    exact ⟨hx0, by linarith⟩
  have hweak := (SobolevIntervalLp.hasWeakDerivOn_rep hI u).indicator_mul_of_tsupport_inter_subset
    hIJ hη hsupp
  have hηb : MemLp η ⊤ (volume.restrict (Ioo (0 : ℝ) 1)) :=
    hη.continuous.continuousOn.memLp_top_restrict_Ioo
  have hηb' : MemLp (deriv η) ⊤ (volume.restrict (Ioo (0 : ℝ) 1)) :=
    (hη.continuous_deriv (by simp)).continuousOn.memLp_top_restrict_Ioo
  have hrest : (volume.restrict (Ioi (0 : ℝ))).restrict (Ioo 0 1) = volume.restrict (Ioo 0 1) := by
    rw [Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.2 fun x hx ↦ hx.1]
  have hmem : ∀ {f : ℝ → ℝ}, MemLp f p (volume.restrict (Ioo (0 : ℝ) 1)) →
      MemLp ((Ioo (0 : ℝ) 1).indicator f) p (volume.restrict (Ioi 0)) := fun hf ↦ by
    rw [memLp_iff, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioo, hrest]
    exact hf.eLpNorm_lt_top
  refine ⟨memSobolevSpace_iff_memSobolevIntervalLp.2 (memSobolevIntervalLp_one_iff.2
    ⟨hmem (hηb.fun_mul (SobolevIntervalLp.memLp_rep hI u)), _, hweak,
      hmem ((hηb'.fun_mul (SobolevIntervalLp.memLp_rep hI u)).add
        (hηb.fun_mul (SobolevIntervalLp.memLp_deriv u 1)))⟩), fun φ ↦ ?_⟩
  have := hweak.integral_deriv_mul φ
  simp only [mul_comm, Opens.coe_Ioi] at this ⊢
  exact this

/-! ### Theorem 8.7, density -/

/-- **Theorem 8.7** (density). Let `u ∈ W^{1,p}(I)` with `1 ≤ p < ∞`, `I` a nonempty open
interval. Then there is a sequence `(u_n)` in `C_c^∞(ℝ)` such that `u_n|_I → u` in
`W^{1,p}(I)`: the elements `v_n ∈ W^{1,p}(I)` carried by the restrictions converge to `u`. The
backbone's `SobolevIntervalLp.exists_seq_contDiff_hasCompactSupport_tendsto` (through the
extension operator and the whole-space density theorem). -/
theorem theorem_8_7 (hI : (I : Set ℝ).OrdConnected) (hne : (I : Set ℝ).Nonempty) (hp : p ≠ ∞)
    (u : SobolevIntervalLp 1 p I) :
    ∃ g : ℕ → ℝ → ℝ, (∀ n, ContDiff ℝ (⊤ : ℕ∞) (g n)) ∧ (∀ n, HasCompactSupport (g n)) ∧
      ∃ v : ℕ → SobolevIntervalLp 1 p I,
        (∀ n, (v n).fn =ᵐ[volume.restrict I] g n) ∧ Tendsto v atTop (𝓝 u) :=
  SobolevIntervalLp.exists_seq_contDiff_hasCompactSupport_tendsto hI hne hp u

/-- **Remark 9.** In general there is no sequence `(u_n)` in `C_c^∞(I)` with `u_n → u` in
`W^{1,p}(I)`: on a bounded interval `(a, b)` the constant `1` is the limit of no such sequence
(its element lies outside `W_0^{1,p}(a, b)`, §8.3). The backbone's
`SobolevIntervalLp.exists_not_mem_closure_testFunctions`. -/
theorem remark_8_9 {a b : ℝ} (hab : a < b) :
    ∃ u : SobolevIntervalLp 1 p (Opens.Ioo a b), (u.fn =ᵐ[volume.restrict (Ioo a b)] fun _ ↦ 1) ∧
      ¬ ∃ v : ℕ → SobolevIntervalLp 1 p (Opens.Ioo a b),
        (∀ n, ∃ φ : 𝓓(Opens.Ioo a b, ℝ), (v n).fn =ᵐ[volume.restrict (Ioo a b)] φ) ∧
          Tendsto v atTop (𝓝 u) := by
  obtain ⟨u, hu, hu0⟩ := SobolevIntervalLp.exists_not_mem_closure_testFunctions (p := p) hab
  refine ⟨u, hu, fun ⟨v, hv, hlim⟩ ↦ hu0 ?_⟩
  refine SobolevMultiIndexZero.isClosed.mem_of_tendsto hlim (Eventually.of_forall fun n ↦ ?_)
  obtain ⟨φ, hφ⟩ := hv n
  exact SobolevIntervalLpZero.mem_of_fn_ae_eq φ hφ

/-- **Lemma 8.4.** Let `ρ ∈ L¹(ℝ)` and `v ∈ W^{1,p}(ℝ)` with `1 ≤ p ≤ ∞`. Then
`ρ ⋆ v ∈ W^{1,p}(ℝ)` and `(ρ ⋆ v)' = ρ ⋆ v'`. The backbone's
`SobolevIntervalLp.hasWeakDerivOn_convolution` and `memSobolevIntervalLp_convolution`. -/
theorem lemma_8_4 (v : SobolevIntervalLp 1 p ⊤) {ρ : ℝ → ℝ} (hρ : Integrable ρ) :
    MemSobolevSpace p ⊤ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] v.fn) ∧
      ∀ φ : 𝓓((⊤ : Opens ℝ), ℝ),
        ∫ x in ((⊤ : Opens ℝ) : Set ℝ), (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] v.fn) x * deriv φ x
          = -∫ x in ((⊤ : Opens ℝ) : Set ℝ),
              (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] ⇑(v.deriv 1)) x * φ x := by
  refine ⟨memSobolevSpace_iff_memSobolevIntervalLp.2
    (SobolevIntervalLp.memSobolevIntervalLp_convolution v hρ), fun φ ↦ ?_⟩
  have := (SobolevIntervalLp.hasWeakDerivOn_convolution v hρ).integral_deriv_mul φ
  simp only [mul_comm] at this ⊢
  exact this

/-! ### Theorem 8.8, the Sobolev embedding -/

/-- The constant of Theorem 8.8 (5) can be chosen independently of `p` (footnote 7): the
backbone's `SobolevIntervalLp.embeddingConst p I = max 2 (|I|^{-1/p} + |I|^{1-1/p})` is at most
`max 2 (max 1 |I|⁻¹ + max 1 |I|)`, a function of `|I|` alone. -/
private theorem embeddingConst_le (p : ℝ≥0∞) [Fact (1 ≤ p)] (I : Opens ℝ) :
    SobolevIntervalLp.embeddingConst p I
      ≤ max 2 (max 1 (volume (I : Set ℝ)).toReal⁻¹ + max 1 (volume (I : Set ℝ)).toReal) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have he0 : 0 ≤ p.toReal⁻¹ := by positivity
  have he1 : p.toReal⁻¹ ≤ 1 := by
    have := one_sub_toReal_inv_nonneg hp1
    linarith
  refine max_le_max_left 2 (add_le_add ?_ ?_)
  · rcases (ENNReal.toReal_nonneg (a := volume (I : Set ℝ))).eq_or_lt with h0 | hpos
    · rw [← h0]; exact (Real.zero_rpow_le_one _).trans (le_max_left _ _)
    rcases le_or_gt 1 (volume (I : Set ℝ)).toReal with h1 | h1
    · exact (Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)).trans (le_max_left _ _)
    · refine le_trans ?_ (le_max_right _ _)
      have h := Real.rpow_le_rpow_of_exponent_ge hpos h1.le
        (show (-1 : ℝ) ≤ -p.toReal⁻¹ by linarith)
      rwa [Real.rpow_neg_one] at h
  · rcases (ENNReal.toReal_nonneg (a := volume (I : Set ℝ))).eq_or_lt with h0 | hpos
    · rw [← h0]; exact (Real.zero_rpow_le_one _).trans (le_max_left _ _)
    rcases le_or_gt 1 (volume (I : Set ℝ)).toReal with h1 | h1
    · refine le_trans ?_ (le_max_right _ _)
      conv_rhs => rw [← Real.rpow_one (volume (I : Set ℝ)).toReal]
      exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    · exact (Real.rpow_le_one hpos.le h1.le (by linarith)).trans (le_max_left _ _)

/-- **Theorem 8.8, (5).** There is a constant `C`, depending only on `|I| ≤ ∞`, such that
`‖u‖_{L^∞(I)} ≤ C ‖u‖_{W^{1,p}(I)}` for all `u ∈ W^{1,p}(I)` and all `1 ≤ p ≤ ∞` — in other
words, `W^{1,p}(I) ⊆ L^∞(I)` with continuous injection for all `1 ≤ p ≤ ∞`. The backbone's
`SobolevIntervalLp.eLpNorm_top_le`, whose constant `embeddingConst p I` is bounded uniformly
in `p` (footnote 7) by `embeddingConst_le`. -/
theorem theorem_8_8_a (hI : (I : Set ℝ).OrdConnected) :
    ∃ C : ℝ, ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : SobolevIntervalLp 1 p I),
      eLpNorm u.fn ∞ (volume.restrict I) ≤ ENNReal.ofReal (C * sobolevNorm u) := by
  refine ⟨max 2 (max 1 (volume (I : Set ℝ)).toReal⁻¹ + max 1 (volume (I : Set ℝ)).toReal),
    fun p _ u ↦ (SobolevIntervalLp.eLpNorm_top_le hI u).trans (ENNReal.ofReal_le_ofReal ?_)⟩
  exact mul_le_mul (embeddingConst_le p I) (sobolevNorm_equiv u).1 (norm_nonneg _)
    (le_trans zero_le_two (le_max_left _ _))

/-- **Theorem 8.8, (6).** If `I` is bounded, the injection `W^{1,p}(I) ⊆ C(Ī)`, `u ↦ ũ`, is
compact for all `1 < p ≤ ∞` (Ascoli–Arzelà, the unit ball being uniformly Hölder continuous).
The backbone's `SobolevIntervalLp.isCompactOperator_toContinuousMap`. -/
theorem theorem_8_8_b {a b : ℝ} (hab : a < b) (hp : 1 < p) :
    IsCompactOperator (SobolevIntervalLp.toContinuousMap (p := p) hab) :=
  SobolevIntervalLp.isCompactOperator_toContinuousMap hab hp

/-- **Theorem 8.8, (7).** If `I` is bounded, the injection `W^{1,1}(I) ⊆ L^q(I)` is compact
for all `1 ≤ q < ∞` (through the extension operator and the Kolmogorov–M. Riesz–Fréchet
theorem). The backbone's `SobolevIntervalLp.isCompactOperator_toLp_one`. -/
theorem theorem_8_8_c {a b : ℝ} (hab : a < b) {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : q ≠ ∞) :
    IsCompactOperator (SobolevIntervalLp.toLpOfBounded 1 hab q) :=
  SobolevIntervalLp.isCompactOperator_toLp_one hab hq

/-- **Theorem 8.8.** There is a constant `C` depending only on `|I| ≤ ∞` with
`‖u‖_{L^∞(I)} ≤ C ‖u‖_{W^{1,p}(I)}` for all `u ∈ W^{1,p}(I)` and all `1 ≤ p ≤ ∞` (5); further,
if `I` is bounded, the injection `W^{1,p}(I) ⊆ C(Ī)` is compact for all `1 < p ≤ ∞` (6), and
the injection `W^{1,1}(I) ⊆ L^q(I)` is compact for all `1 ≤ q < ∞` (7). -/
theorem theorem_8_8 (hI : (I : Set ℝ).OrdConnected) :
    (∃ C : ℝ, ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : SobolevIntervalLp 1 p I),
      eLpNorm u.fn ∞ (volume.restrict I) ≤ ENNReal.ofReal (C * sobolevNorm u)) ∧
    (∀ (a b : ℝ) (hab : a < b) (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p →
      IsCompactOperator (SobolevIntervalLp.toContinuousMap (p := p) hab)) ∧
    ∀ (a b : ℝ) (hab : a < b) (q : ℝ≥0∞) [Fact (1 ≤ q)], q ≠ ∞ →
      IsCompactOperator (SobolevIntervalLp.toLpOfBounded 1 hab q) :=
  ⟨theorem_8_8_a hI, fun _ _ hab _ _ hp ↦ theorem_8_8_b hab hp,
    fun _ _ hab _ _ hq ↦ theorem_8_8_c hab hq⟩

/-! ### Remark 10: the two non-compactness claims -/

/-- The functions `x ↦ x ^ n` on `(0, 1)`, as elements of `W^{1,1}(0, 1)`: their `W^{1,1}` norms
are at most `2` (`‖x^n‖_1 ≤ 1`, `‖n x^{n-1}‖_1 = 1 - 0^n ≤ 1`) and their representatives are
`x ↦ x ^ n` on `[0, 1]`. -/
private theorem exists_pow_sobolevIntervalLp (n : ℕ) :
    ∃ u : SobolevIntervalLp 1 1 (Opens.Ioo 0 1), ‖u‖ ≤ 2 ∧
      ∀ x ∈ Icc (0 : ℝ) 1, u.rep x = x ^ n := by
  have hI := SobolevIntervalLp.ordConnected_coe_Ioo (0 : ℝ) 1
  have hmem : MemSobolevIntervalLp (fun y : ℝ ↦ y ^ n) 1 1 (Opens.Ioo 0 1) ∧
      HasWeakDerivOn (fun y : ℝ ↦ y ^ n) (deriv fun y : ℝ ↦ y ^ n) (Opens.Ioo 0 1) :=
    memSobolevIntervalLp_of_contDiffOn_Icc (p := 1) (zero_lt_one' ℝ) (contDiff_id.pow n).contDiffOn
  obtain ⟨u, hu⟩ := hmem.1.exists_sobolevIntervalLp
  have hderiv : ∀ x : ℝ, deriv (fun y : ℝ ↦ y ^ n) x = n * x ^ (n - 1) := fun x ↦
    (hasDerivAt_pow n x).deriv
  have hu1 : ⇑(u.deriv 1) =ᵐ[volume.restrict ((Opens.Ioo (0 : ℝ) 1 : Opens ℝ) : Set ℝ)]
      fun x ↦ (n : ℝ) * x ^ (n - 1) := by
    filter_upwards [(ae_restrict_iff' measurableSet_Ioo).2
      ((u.hasWeakDerivOn_fn.congr_ae hu (EventuallyEq.refl _ _)).ae_eq hmem.2)] with x hx
    rw [hx, hderiv]
  have hrep : ∀ x ∈ Icc (0 : ℝ) 1, u.rep x = x ^ n := fun x hx ↦
    SobolevIntervalLp.rep_eq_of_continuousOn hI u (continuous_pow n).continuousOn hu
      (by rw [SobolevIntervalLp.closure_coe_Ioo (zero_lt_one' ℝ)]; exact hx)
  refine ⟨u, ?_, hrep⟩
  rw [← sobolevNorm_eq_norm_of_one, sobolevNorm]
  have hfin : IsFiniteMeasure (volume.restrict ((Opens.Ioo (0 : ℝ) 1 : Opens ℝ) : Set ℝ)) := ⟨by
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Opens.coe_Ioo, Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top⟩
  have hvol : measureUnivNNReal (volume.restrict ((Opens.Ioo (0 : ℝ) 1 : Opens ℝ) : Set ℝ))
      = 1 := by
    simp [measureUnivNNReal, Real.volume_Ioo]
  -- `‖x^n‖_{L¹(0, 1)} ≤ 1`
  have h0 : ‖u.deriv 0‖ ≤ 1 := by
    have := Lp.norm_le_of_ae_bound (f := u.deriv 0) (C := 1) zero_le_one ?_
    · rwa [hvol, NNReal.coe_one, Real.one_rpow, one_mul] at this
    · filter_upwards [hu, ae_restrict_mem measurableSet_Ioo] with x hx hxI
      rw [SobolevIntervalLp.deriv_zero, hx, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hxI.1.le _)]
      exact pow_le_one₀ hxI.1.le hxI.2.le
  -- `‖n x^{n-1}‖_{L¹(0, 1)} = 1 - 0^n ≤ 1`
  have h1 : ‖u.deriv 1‖ ≤ 1 := by
    have e0 : (fun x ↦ ‖u.deriv 1 x‖) =ᵐ[volume.restrict ((Opens.Ioo (0 : ℝ) 1 : Opens ℝ) : Set ℝ)]
        fun x ↦ ‖(n : ℝ) * x ^ (n - 1)‖ := hu1.mono fun x hx ↦ by simp only [hx]
    rw [L1.norm_eq_integral_norm, integral_congr_ae e0]
    have e : ∫ x in ((Opens.Ioo (0 : ℝ) 1 : Opens ℝ) : Set ℝ), ‖(n : ℝ) * x ^ (n - 1)‖
        = ∫ x in (0 : ℝ)..1, (n : ℝ) * x ^ (n - 1) := by
      rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo, Opens.coe_Ioo]
      refine setIntegral_congr_fun measurableSet_Ioo fun x hx ↦ ?_
      exact Real.norm_of_nonneg (by have := hx.1.le; positivity)
    rw [e, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hasDerivAt_pow n x)
      ((continuous_const.mul (continuous_pow _)).intervalIntegrable _ _), one_pow]
    linarith [pow_nonneg (le_refl (0 : ℝ)) n]
  linarith

/-- **Remark 10 (a).** The injection `W^{1,1}(I) ⊆ C(Ī)` is continuous but never compact, even
if `I` is a bounded interval; on `I = (0, 1)`: the functions `u_n(x) = x^n` are bounded in
`W^{1,1}(0, 1)` and converge pointwise on `[0, 1]` to the discontinuous function `1_{{1}}`, so no
subsequence converges in `C([0, 1])`. (The book: "the reader should find an argument or see
Exercise 8.2".) -/
theorem remark_8_10_a :
    ¬ IsCompactOperator (SobolevIntervalLp.toContinuousMap (p := 1) (zero_lt_one' ℝ)) := by
  intro hT
  choose u hu hrep using exists_pow_sobolevIntervalLp
  obtain ⟨T, hT'⟩ : ∃ T : SobolevIntervalLp 1 1 (Opens.Ioo 0 1) →L[ℝ] C(Icc (0 : ℝ) 1, ℝ),
      T = SobolevIntervalLp.toContinuousMap (p := 1) (zero_lt_one' ℝ) := ⟨_, rfl⟩
  rw [← hT'] at hT
  have hT2 : IsCompactOperator
      (T : SobolevIntervalLp 1 1 (Opens.Ioo 0 1) →ₗ[ℝ] C(Icc (0 : ℝ) 1, ℝ)) := by
    rwa [ContinuousLinearMap.coe_coe]
  have hK := hT2.isCompact_closure_image_closedBall 2
  obtain ⟨g, -, ρ, hρ, hlim⟩ := hK.tendsto_subseq (x := fun n ↦ T (u n)) fun n ↦
    subset_closure ⟨u n, mem_closedBall_zero_iff.2 (hu n), rfl⟩
  -- the pointwise values of the limit
  have hval : ∀ (x : Icc (0 : ℝ) 1) (k : ℕ), (T (u (ρ k))) x = (x : ℝ) ^ ρ k := fun x k ↦ by
    rw [hT', SobolevIntervalLp.toContinuousMap_apply, hrep _ _ x.2]
  have hev : ∀ x : Icc (0 : ℝ) 1, Tendsto (fun k ↦ (x : ℝ) ^ ρ k) atTop (𝓝 (g x)) := fun x ↦
    (((continuous_eval_const x : Continuous fun f : C(Icc (0 : ℝ) 1, ℝ) ↦ f x).tendsto g).comp
      hlim).congr fun k ↦ hval x k
  have hg1 : g ⟨1, right_mem_Icc.2 zero_le_one⟩ = 1 := by
    refine tendsto_nhds_unique (hev ⟨1, right_mem_Icc.2 zero_le_one⟩) ?_
    simp only [one_pow]
    exact tendsto_const_nhds
  have hg0 : ∀ x : Icc (0 : ℝ) 1, (x : ℝ) < 1 → g x = 0 := fun x hx ↦
    tendsto_nhds_unique (hev x)
      ((tendsto_pow_atTop_nhds_zero_of_lt_one x.2.1 hx).comp hρ.tendsto_atTop)
  -- the limit is continuous at `1`, but its values left of `1` vanish
  have hxk : ∀ k : ℕ, 1 - 1 / ((k : ℝ) + 1) ∈ Icc (0 : ℝ) 1 := fun k ↦ by
    have h1 : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have h2 : (0 : ℝ) ≤ 1 / ((k : ℝ) + 1) := by positivity
    constructor <;> linarith
  have hlt : ∀ k : ℕ, 1 - 1 / ((k : ℝ) + 1) < 1 := fun k ↦ by
    have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    linarith
  have hseq : Tendsto (fun k : ℕ ↦ (⟨1 - 1 / ((k : ℝ) + 1), hxk k⟩ : Icc (0 : ℝ) 1)) atTop
      (𝓝 ⟨1, right_mem_Icc.2 zero_le_one⟩) := by
    rw [tendsto_subtype_rng]
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_one_div_add_atTop_nhds_zero_nat
  have hcont := (g.continuous.tendsto _).comp hseq
  have hzero : Tendsto (fun k : ℕ ↦ g ⟨1 - 1 / ((k : ℝ) + 1), hxk k⟩) atTop (𝓝 0) :=
    tendsto_const_nhds.congr fun k ↦ (hg0 _ (hlt k)).symm
  have := tendsto_nhds_unique hcont hzero
  rw [hg1] at this
  exact one_ne_zero this

/-- Two distinct natural numbers are at distance at least one, in `ℝ`. -/
private theorem one_le_abs_sub_of_ne {m n : ℕ} (h : m ≠ n) : 1 ≤ |(m : ℝ) - n| := by
  have e : (m : ℝ) - n = ((m : ℤ) - n : ℤ) := by push_cast; ring
  rw [e, ← Int.cast_abs, ← Int.cast_one, Int.cast_le]
  exact Int.one_le_abs (sub_ne_zero.2 (by exact_mod_cast h))

/-- The essential supremum of a function over an open set dominates its value at any point of
the set where it is continuous. -/
private theorem enorm_le_eLpNormEssSup_restrict {f : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s) {x : ℝ}
    (hx : x ∈ s) (hf : ContinuousAt f x) : ‖f x‖ₑ ≤ eLpNormEssSup f (volume.restrict s) := by
  by_contra hlt
  push Not at hlt
  have hev : ∀ᶠ y in 𝓝 x, eLpNormEssSup f (volume.restrict s) < ‖f y‖ₑ :=
    continuousAt_const.eventually_lt (continuous_enorm.continuousAt.comp hf) hlt
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.1 hev
  have h0 : volume.restrict s {y | eLpNormEssSup f (volume.restrict s) < ‖f y‖ₑ} = 0 :=
    meas_eLpNormEssSup_lt
  have hpos : 0 < volume.restrict s U := by
    rw [Measure.restrict_apply hU.measurableSet]
    exact (hU.inter hs).measure_pos volume ⟨x, hxU, hx⟩
  exact hpos.ne' (measure_mono_null hUsub h0)

/-- **Remark 10 (c).** When `I` is unbounded, the injection `W^{1,p}(I) ⊆ L^∞(I)` (continuous
by Theorem 8.8 (5), the book's context being `1 < p ≤ ∞`; the hypothesis is not needed) is
never compact: the translates `u_n = φ(· − c_n)` of a fixed bump `φ ∈ C_c^∞(ℝ)` along a
half-line contained in `I`, with the `c_n` at mutual distance at least one, are bounded in
`W^{1,p}(I)` and pairwise at `L^∞` distance at least `‖φ‖_∞ = 1`, so no subsequence is Cauchy in
`L^∞(I)`. (The book: "again give an argument or see Exercise 8.4".) -/
theorem remark_8_10_c (hI : (I : Set ℝ).OrdConnected) (hunb : ¬ Bornology.IsBounded (I : Set ℝ)) :
    ¬ IsCompactOperator (SobolevIntervalLp.toLp p hI (le_top : p ≤ ⊤)) := by
  intro hT
  -- centres of the translates, at mutual distance at least one, with `[c n - 1, c n + 1] ⊆ I`
  obtain ⟨c, hcI, hsep⟩ : ∃ c : ℕ → ℝ, (∀ n, Icc (c n - 1) (c n + 1) ⊆ I) ∧
      ∀ m n, m ≠ n → 1 ≤ |c m - c n| := by
    obtain ⟨x₀, hx₀⟩ : (I : Set ℝ).Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty] at h
      exact hunb (h ▸ Bornology.isBounded_empty)
    rw [isBounded_iff_bddBelow_bddAbove, not_and_or] at hunb
    rcases hunb with h | h
    · refine ⟨fun n ↦ x₀ - ((n : ℝ) + 2), fun n ↦ ?_, fun m n hmn ↦ ?_⟩
      · obtain ⟨y, hy, hyx⟩ : ∃ y ∈ (I : Set ℝ), y < x₀ - ((n : ℝ) + 2) - 1 := by
          by_contra hcon
          push Not at hcon
          exact h ⟨_, fun y hy ↦ hcon y hy⟩
        exact (Icc_subset_Icc hyx.le (by linarith)).trans (hI.out hy hx₀)
      · rw [show x₀ - ((m : ℝ) + 2) - (x₀ - ((n : ℝ) + 2)) = -((m : ℝ) - n) by ring, abs_neg]
        exact one_le_abs_sub_of_ne hmn
    · refine ⟨fun n ↦ x₀ + ((n : ℝ) + 2), fun n ↦ ?_, fun m n hmn ↦ ?_⟩
      · obtain ⟨y, hy, hyx⟩ : ∃ y ∈ (I : Set ℝ), x₀ + ((n : ℝ) + 2) + 1 < y := by
          by_contra hcon
          push Not at hcon
          exact h ⟨_, fun y hy ↦ hcon y hy⟩
        exact (Icc_subset_Icc (by linarith) hyx.le).trans (hI.out hx₀ hy)
      · rw [show x₀ + ((m : ℝ) + 2) - (x₀ + ((n : ℝ) + 2)) = (m : ℝ) - n by ring]
        exact one_le_abs_sub_of_ne hmn
  -- the bump and its translates, as test functions on `I`
  obtain ⟨φ, hφin, hφout⟩ : ∃ φ : ContDiffBump (0 : ℝ), φ.rIn = 1 / 4 ∧ φ.rOut = 1 / 2 :=
    ⟨⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩, rfl, rfl⟩
  have hφc : ∀ n, tsupport (fun x ↦ φ (x - c n)) ⊆ I := fun n ↦ by
    refine (closure_minimal ?_ isClosed_Icc).trans (hcI n)
    intro x hx
    have hx' : x - c n ∈ Function.support φ := Function.mem_support.2 (Function.mem_support.1 hx)
    rw [φ.support_eq, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_lt, hφout] at hx'
    constructor <;> linarith [hx'.1, hx'.2]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℕ → 𝓓(I, ℝ), ∀ n, ⇑(ψ n) = fun x ↦ φ (x - c n) :=
    ⟨fun n ↦ ⟨fun x ↦ φ (x - c n), (φ.contDiff (n := ⊤)).comp (contDiff_id.sub contDiff_const),
      φ.hasCompactSupport.comp_homeomorph (Homeomorph.subRight (c n)), hφc n⟩, fun n ↦ rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℕ → SobolevIntervalLp 1 p I,
      ∀ n, u n = TestFunction.toSobolevIntervalLp p (ψ n) := ⟨_, fun n ↦ rfl⟩
  -- the translates are bounded in `W^{1,p}(I)`
  have hφp : MemLp (⇑φ) p volume := φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
  have hφ'p : MemLp (deriv φ) p volume :=
    ((φ.contDiff (n := 1)).continuous_deriv le_rfl).memLp_of_hasCompactSupport
      φ.hasCompactSupport.deriv
  have hM : ∀ n, ‖u n‖ ≤ (eLpNorm φ p volume).toReal + (eLpNorm (deriv φ) p volume).toReal :=
    fun n ↦ by
    refine (sobolevNorm_equiv (u n)).1.trans (add_le_add ?_ ?_)
    · rw [Lp.norm_def]
      refine ENNReal.toReal_mono hφp.eLpNorm_ne_top ?_
      calc eLpNorm (⇑((u n).deriv 0)) p (volume.restrict I)
          = eLpNorm (ψ n) p (volume.restrict I) := by
            rw [hu]
            exact eLpNorm_congr_ae (TestFunction.fn_toSobolevIntervalLp_ae_eq (ψ n))
        _ ≤ eLpNorm (ψ n) p volume := eLpNorm_mono_measure _ Measure.restrict_le_self
        _ = eLpNorm φ p volume := by
            rw [hψ]
            exact eLpNorm_comp_measurePreserving φ.continuous.aestronglyMeasurable
              (measurePreserving_sub_right volume (c n))
    · rw [Lp.norm_def]
      refine ENNReal.toReal_mono hφ'p.eLpNorm_ne_top ?_
      have hd : deriv (ψ n) = fun x ↦ deriv φ (x - c n) := by
        rw [hψ]
        exact funext fun x ↦ deriv_comp_sub_const _ _ _
      calc eLpNorm (⇑((u n).deriv 1)) p (volume.restrict I)
          = eLpNorm (deriv (ψ n)) p (volume.restrict I) := by
            rw [hu]
            exact eLpNorm_congr_ae (TestFunction.coeFn_deriv_toSobolevIntervalLp_one (ψ n))
        _ ≤ eLpNorm (deriv (ψ n)) p volume := eLpNorm_mono_measure _ Measure.restrict_le_self
        _ = eLpNorm (deriv φ) p volume := by
            rw [hd]
            exact eLpNorm_comp_measurePreserving
              ((φ.contDiff (n := 1)).continuous_deriv le_rfl).aestronglyMeasurable
              (measurePreserving_sub_right volume (c n))
  -- two translates are at `L^∞` distance at least one
  obtain ⟨T, hT'⟩ : ∃ T : SobolevIntervalLp 1 p I →L[ℝ] Lp ℝ ⊤ (volume.restrict (I : Set ℝ)),
      T = SobolevIntervalLp.toLp p hI (le_top : p ≤ ⊤) := ⟨_, rfl⟩
  rw [← hT'] at hT
  have hge : ∀ a b, a ≠ b → 1 ≤ dist (T (u a)) (T (u b)) := fun a b hab ↦ by
    rw [dist_eq_norm, ← map_sub, hT', Lp.norm_def]
    have hae : ⇑(SobolevIntervalLp.toLp p hI (le_top : p ≤ ⊤) (u a - u b))
        =ᵐ[volume.restrict I] fun x ↦ φ (x - c a) - φ (x - c b) := by
      refine (SobolevIntervalLp.coeFn_toLp (p := p) (q := ⊤) hI le_top (u a - u b)).trans
        ((SobolevMultiIndex.fn_sub (u a) (u b)).trans ?_)
      rw [hu, hu]
      filter_upwards [TestFunction.fn_toSobolevIntervalLp_ae_eq (p := p) (ψ a),
        TestFunction.fn_toSobolevIntervalLp_ae_eq (p := p) (ψ b)] with x hxa hxb
      have hxa' : SobolevMultiIndex.fn (TestFunction.toSobolevIntervalLp p (ψ a)) x
          = φ (x - c a) := by
        have := congrFun (hψ a) x
        exact hxa.trans this
      have hxb' : SobolevMultiIndex.fn (TestFunction.toSobolevIntervalLp p (ψ b)) x
          = φ (x - c b) := by
        have := congrFun (hψ b) x
        exact hxb.trans this
      rw [Pi.sub_apply, hxa', hxb']
    have hcont : Continuous fun x ↦ φ (x - c a) - φ (x - c b) :=
      (φ.continuous.comp (continuous_sub_right (c a))).sub
        (φ.continuous.comp (continuous_sub_right (c b)))
    have hne : eLpNormEssSup (fun x ↦ φ (x - c a) - φ (x - c b)) (volume.restrict I) ≠ ⊤ := by
      rw [← eLpNorm_exponent_top hcont.aestronglyMeasurable, ← eLpNorm_congr_ae hae]
      exact Lp.eLpNorm_ne_top _
    rw [eLpNorm_congr_ae hae, eLpNorm_exponent_top hcont.aestronglyMeasurable]
    have hlow : ‖φ (c a - c a) - φ (c a - c b)‖ₑ
        ≤ eLpNormEssSup (fun x ↦ φ (x - c a) - φ (x - c b)) (volume.restrict I) :=
      enorm_le_eLpNormEssSup_restrict (f := fun x ↦ φ (x - c a) - φ (x - c b)) I.isOpen
        (hcI a ⟨by linarith, by linarith⟩) hcont.continuousAt
    rw [sub_self, φ.one_of_mem_closedBall (Metric.mem_closedBall_self (by rw [hφin]; norm_num)),
      φ.zero_of_le_dist (by rw [hφout, Real.dist_eq, sub_zero]; linarith [hsep a b hab]),
      sub_zero, enorm_one] at hlow
    have := ENNReal.toReal_mono hne hlow
    rwa [ENNReal.toReal_one] at this
  -- no subsequence of the translates is Cauchy in `L^∞(I)`
  have hT2 : IsCompactOperator
      (T : SobolevIntervalLp 1 p I →ₗ[ℝ] Lp ℝ ⊤ (volume.restrict (I : Set ℝ))) := by
    rwa [ContinuousLinearMap.coe_coe]
  have hK := hT2.isCompact_closure_image_closedBall
    ((eLpNorm φ p volume).toReal + (eLpNorm (deriv φ) p volume).toReal)
  obtain ⟨g, -, ρ, hρ, hlim⟩ := hK.tendsto_subseq (x := fun n ↦ T (u n)) fun n ↦
    subset_closure ⟨u n, mem_closedBall_zero_iff.2 (hM n), rfl⟩
  have hcauchy := hlim.cauchySeq
  rw [Metric.cauchySeq_iff'] at hcauchy
  obtain ⟨N, hN⟩ := hcauchy 1 one_pos
  have hlt := hN (N + 1) (Nat.le_succ N)
  simp only [Function.comp_apply] at hlt
  exact absurd hlt (not_lt.2 (hge _ _ (hρ.injective.ne (Nat.succ_ne_self N))))

/-- **Remark 10 (b), Helly's selection theorem.** If `(u_n)` is a bounded sequence in
`W^{1,1}(I)`, `I = (a, b)` bounded, there is a subsequence `(u_{n_k})` such that `u_{n_k}(x)`
converges for all `x ∈ Ī`. The backbone's
`SobolevIntervalLp.exists_subseq_tendsto_of_bounded_one`. (The book allows `I` unbounded; the
unbounded case follows by a diagonal argument on `I ∩ [−R, R]` and is not formalized.) -/
theorem remark_8_10_b {a b : ℝ} (hab : a < b) {u : ℕ → SobolevIntervalLp 1 1 (Opens.Ioo a b)}
    {M : ℝ} (hM : ∀ n, ‖u n‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ x ∈ Icc a b, ∃ l : ℝ, Tendsto (fun n ↦ (u (φ n)).rep x) atTop (𝓝 l) :=
  SobolevIntervalLp.exists_subseq_tendsto_of_bounded_one hab hM

/-- **Remark 10 (d).** If `(u_n)` is bounded in `W^{1,p}(I)` with `1 < p ≤ ∞` there are a
subsequence `(u_{n_k})` and some `u ∈ W^{1,p}(I)` such that `u_{n_k} → u` in `L^∞(J)` for every
bounded subset `J` of `I`: the representatives converge uniformly on `Ī ∩ [−R, R]` for every
`R`. The backbone's `SobolevIntervalLp.exists_subseq_tendsto_rep_of_bounded`. -/
theorem remark_8_10_d (hI : (I : Set ℝ).OrdConnected) (hp : 1 < p)
    {u : ℕ → SobolevIntervalLp 1 p I} {M : ℝ} (hM : ∀ n, ‖u n‖ ≤ M) :
    ∃ (v : SobolevIntervalLp 1 p I) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ R : ℝ, TendstoUniformlyOn (fun n ↦ (u (φ n)).rep) v.rep atTop
        (closure (I : Set ℝ) ∩ Icc (-R) R) :=
  have := ENNReal.holderConjugate_sub_inv_inv (p := p)
  let ⟨v, φ, hφ, hlim, _⟩ := SobolevIntervalLp.exists_subseq_tendsto_rep_of_bounded hI
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt (1 - p⁻¹)⁻¹ p).2 hp).ne hM
  ⟨v, φ, hφ, hlim⟩

/-- **Remark 11.** Let `I = (a, b)` be bounded, `1 ≤ p ≤ ∞` and `1 ≤ q ≤ ∞`. The norm
`‖u'‖_{L^p} + ‖u‖_{L^q}` is equivalent to the norm of `W^{1,p}(I)`. The backbone's
`SobolevIntervalLp.norm_equiv_of_bounded` (`u ↦ u` in `L^q(a, b)` is
`SobolevIntervalLp.toLpOfBounded p hab q`). -/
theorem remark_8_11 {a b : ℝ} (hab : a < b) (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ u : SobolevIntervalLp 1 p (Opens.Ioo a b),
      ‖u‖ ≤ C₁ * (‖u.deriv 1‖ + ‖SobolevIntervalLp.toLpOfBounded p hab q u‖) ∧
      ‖u.deriv 1‖ + ‖SobolevIntervalLp.toLpOfBounded p hab q u‖ ≤ C₂ * ‖u‖ :=
  SobolevIntervalLp.norm_equiv_of_bounded hab q

/-- **Remark 12.** Let `I` be an unbounded interval. If `u ∈ W^{1,p}(I)` then `u ∈ L^q(I)` for
all `q ∈ [p, ∞]` (the interpolation `∫_I |u|^q ≤ ‖u‖_∞^{q−p} ‖u‖_p^p` behind the backbone's
`SobolevIntervalLp.memLp_of_le`; the hypothesis that `I` is unbounded is not needed). The
claim "in general `u ∉ L^q(I)` for `q ∈ [1, p)`" (Exercise 8.1) is not formalized. -/
theorem remark_8_12 (hI : (I : Set ℝ).OrdConnected) (_hunb : ¬ Bornology.IsBounded (I : Set ℝ))
    (u : SobolevIntervalLp 1 p I) {q : ℝ≥0∞} (hpq : p ≤ q) : MemLp u.fn q (volume.restrict I) :=
  SobolevIntervalLp.memLp_of_le hI hpq u

/-! ### Corollaries 8.9–8.11 -/

/-- **Corollary 8.9.** Suppose that `I` is an unbounded interval and `u ∈ W^{1,p}(I)` with
`1 ≤ p < ∞`. Then `lim_{x ∈ I, |x| → ∞} u(x) = 0`. The backbone's
`SobolevIntervalLp.tendsto_rep_cocompact` (which needs no unboundedness: the filter is trivial
otherwise). -/
theorem corollary_8_9 (hI : (I : Set ℝ).OrdConnected) (_hunb : ¬ Bornology.IsBounded (I : Set ℝ))
    (hp : p ≠ ∞) (u : SobolevIntervalLp 1 p I) :
    Tendsto u.rep (cocompact ℝ ⊓ 𝓟 (I : Set ℝ)) (𝓝 0) :=
  SobolevIntervalLp.tendsto_rep_cocompact hI hp u

/-- **Corollary 8.10** (differentiation of a product). Let `u, v ∈ W^{1,p}(I)` with
`1 ≤ p ≤ ∞`. Then `u v ∈ W^{1,p}(I)` (the product of the continuous representatives). The
backbone's `SobolevIntervalLp.memSobolevIntervalLp_mul` (from the absolutely continuous
calculus, not the book's density argument). -/
theorem corollary_8_10 (hI : (I : Set ℝ).OrdConnected) (u v : SobolevIntervalLp 1 p I) :
    MemSobolevSpace p I fun t ↦ u.rep t * v.rep t :=
  memSobolevSpace_iff_memSobolevIntervalLp.2 (SobolevIntervalLp.memSobolevIntervalLp_mul hI u v)

/-- **Corollary 8.10, formula (10).** `(u v)' = u' v + u v'`: the function `u' ṽ + ũ v'` is the
weak derivative of `ũ ṽ` on `I`. The backbone's `SobolevIntervalLp.hasWeakDerivOn_rep_mul`. -/
theorem corollary_8_10_deriv (hI : (I : Set ℝ).OrdConnected) (u v : SobolevIntervalLp 1 p I)
    (φ : 𝓓(I, ℝ)) :
    ∫ x in (I : Set ℝ), (u.rep x * v.rep x) * deriv φ x
      = -∫ x in (I : Set ℝ), (u.deriv 1 x * v.rep x + u.rep x * v.deriv 1 x) * φ x := by
  have := (SobolevIntervalLp.hasWeakDerivOn_rep_mul hI u v).integral_deriv_mul φ
  simp only [mul_comm] at this ⊢
  exact this

/-- **Corollary 8.10, formula (11)** (integration by parts).
`∫_y^x u' v = u(x) v(x) − u(y) v(y) − ∫_y^x u v'` for all `x, y ∈ Ī`. The backbone's
`SobolevIntervalLp.integral_deriv_mul_eq_sub_integral_mul_deriv`. -/
theorem corollary_8_10_parts (hI : (I : Set ℝ).OrdConnected) (u v : SobolevIntervalLp 1 p I)
    {x y : ℝ} (hx : x ∈ closure (I : Set ℝ)) (hy : y ∈ closure (I : Set ℝ)) :
    ∫ t in y..x, u.deriv 1 t * v.rep t
      = u.rep x * v.rep x - u.rep y * v.rep y - ∫ t in y..x, u.rep t * v.deriv 1 t :=
  SobolevIntervalLp.integral_deriv_mul_eq_sub_integral_mul_deriv hI u v hx hy

/-- **Corollary 8.11** (differentiation of a composition). Let `G ∈ C¹(ℝ)` with `G(0) = 0`
and `u ∈ W^{1,p}(I)` with `1 ≤ p ≤ ∞`. Then `G ∘ u ∈ W^{1,p}(I)`. The backbone's
`SobolevIntervalLp.memSobolevIntervalLp_comp`. -/
theorem corollary_8_11 (hI : (I : Set ℝ).OrdConnected) (u : SobolevIntervalLp 1 p I) {G : ℝ → ℝ}
    (hG : ContDiff ℝ 1 G) (hG0 : G 0 = 0) : MemSobolevSpace p I fun t ↦ G (u.rep t) :=
  memSobolevSpace_iff_memSobolevIntervalLp.2
    (SobolevIntervalLp.memSobolevIntervalLp_comp hI u hG hG0).1

/-- **Corollary 8.11, the derivative.** `(G ∘ u)' = (G' ∘ u) u'`: the function
`(G' ∘ ũ) u'` is the weak derivative of `G ∘ ũ` on `I` (no `G(0) = 0` is needed for the
identity alone). -/
theorem corollary_8_11_deriv (hI : (I : Set ℝ).OrdConnected) (u : SobolevIntervalLp 1 p I)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) (φ : 𝓓(I, ℝ)) :
    ∫ x in (I : Set ℝ), G (u.rep x) * deriv φ x
      = -∫ x in (I : Set ℝ), (deriv G (u.rep x) * u.deriv 1 x) * φ x := by
  have := (SobolevIntervalLp.hasWeakDerivOn_comp hI u hG).integral_deriv_mul φ
  simp only [mul_comm] at this ⊢
  exact this

/-- **Corollary 8.11, footnote 9.** The restriction `G(0) = 0` is unnecessary when `I` is
bounded: for `G ∈ C¹(ℝ)` and `u ∈ W^{1,p}(a, b)`, `G ∘ u ∈ W^{1,p}(a, b)`. The backbone's
`SobolevIntervalLp.memSobolevIntervalLp_comp_of_bounded`. -/
theorem corollary_8_11_of_bounded {a b : ℝ} (hab : a < b)
    (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) :
    MemSobolevSpace p (Opens.Ioo a b) fun t ↦ G (u.rep t) :=
  memSobolevSpace_iff_memSobolevIntervalLp.2
    (SobolevIntervalLp.memSobolevIntervalLp_comp_of_bounded hab u hG).1

/-! ### The Sobolev spaces `W^{m,p}` -/

/-- **Definition (§8.2, "The Sobolev spaces `W^{m,p}`"), the inductive definition** as a
predicate on functions: `W^{0,p}(I) = L^p(I)`, and `u ∈ W^{m+1,p}(I)` iff `u ∈ W^{m,p}(I)` and
`u` has a weak derivative `g` (`∫_I u φ' = -∫_I g φ` for all test functions) with
`g ∈ W^{m,p}(I)`. At `m = 1` this is `MemSobolevSpace` (definitionally); for `m ≥ 2` it is the
book's `W^{m,p}(I) = {u ∈ W^{m−1,p}(I) : u' ∈ W^{m−1,p}(I)}`. -/
def MemSobolevSpaceHigher (p : ℝ≥0∞) (I : Opens ℝ) : ℕ → (ℝ → ℝ) → Prop
  | 0, u => MemLp u p (volume.restrict I)
  | m + 1, u => MemSobolevSpaceHigher p I m u ∧ ∃ g : ℝ → ℝ, MemSobolevSpaceHigher p I m g ∧
      ∀ φ : 𝓓(I, ℝ), ∫ x in (I : Set ℝ), u x * deriv φ x = -∫ x in (I : Set ℝ), g x * φ x

omit [Fact (1 ≤ p)] in
/-- At `m = 1` the inductive definition is the definition of `W^{1,p}(I)`. -/
theorem memSobolevSpaceHigher_one {u : ℝ → ℝ} :
    MemSobolevSpaceHigher p I 1 u ↔ MemSobolevSpace p I u := Iff.rfl

/-- **The two definitions of `W^{m,p}(I)` agree**: the inductive one is the backbone's
`MemSobolevIntervalLp u m p I` (`m` weak derivatives in `L^p(I)`), by induction on `m` through
`memSobolevIntervalLp_succ_iff`. -/
theorem memSobolevSpaceHigher_iff {m : ℕ} {u : ℝ → ℝ} :
    MemSobolevSpaceHigher p I m u ↔ MemSobolevIntervalLp u m p I := by
  induction m generalizing u with
  | zero => exact memSobolevIntervalLp_zero_iff.symm
  | succ m ih =>
    rw [MemSobolevSpaceHigher, ih, memSobolevIntervalLp_succ_iff]
    constructor
    · rintro ⟨hu, g, hg, h⟩
      have hu' := (memSobolevIntervalLp_iff.1 hu).1
      have hg' := (memSobolevIntervalLp_iff.1 (ih.1 hg)).1
      refine ⟨hu', g, hasWeakDerivOn_iff.2 ⟨hu'.locallyIntegrableOn Fact.out,
        hg'.locallyIntegrableOn Fact.out, fun φ ↦ ?_⟩, ih.1 hg⟩
      have := h φ
      simp only [mul_comm] at this ⊢
      exact this
    · rintro ⟨hu, w, hw, hwm⟩
      refine ⟨?_, w, ih.2 hwm, fun φ ↦ ?_⟩
      · rw [memSobolevIntervalLp_iff] at hwm ⊢
        refine ⟨hu, fun j hj ↦ ?_⟩
        cases j with
        | zero => exact ⟨u, HasWeakIteratedLineDerivOn.of_length_eq_zero rfl _
            hw.locallyIntegrableOn, hu⟩
        | succ j =>
          obtain ⟨w', hw', hwp'⟩ := hwm.2 j (by omega)
          exact ⟨w', hw.hasWeakIteratedDerivOn_succ hw', hwp'⟩
      · have := hw.integral_deriv_mul φ
        simp only [mul_comm] at this ⊢
        exact this

/-- **Definition (§8.2, "The Sobolev spaces `W^{m,p}`").** The space `W^{m,p}(I)`: the
backbone's `SobolevIntervalLp m p I`, whose elements are the tuples `(u, Du, …, D^m u)` in
`L^p(I)`. -/
abbrev sobolevSpaceHigher (m : ℕ) (p : ℝ≥0∞) (I : Opens ℝ) : Type := SobolevIntervalLp m p I

/-- **Notation.** `H^m(I) = W^{m,2}(I)`. -/
abbrev Hm (m : ℕ) (I : Opens ℝ) : Type := sobolevSpaceHigher m 2 I

/-- **The "easily shown" characterization of `W^{m,p}(I)`.** `u ∈ W^{m,p}(I)` iff `u ∈ L^p(I)`
and there are `m` functions `g₁, …, g_m ∈ L^p(I)` with `∫_I u D^j φ = (−1)^j ∫_I g_j φ` for all
test functions `φ` and all `j = 1, …, m`. The backbone's
`SobolevIntervalLp.memSobolevIntervalLp_iff_forall_integral`. -/
theorem memSobolevSpaceHigher_iff_forall_integral {m : ℕ} {u : ℝ → ℝ} :
    MemSobolevSpaceHigher p I m u ↔ MemLp u p (volume.restrict I) ∧ ∀ j ∈ Icc 1 m,
      ∃ g : ℝ → ℝ, MemLp g p (volume.restrict I) ∧ ∀ φ : 𝓓(I, ℝ),
        ∫ x in (I : Set ℝ), u x * iteratedDeriv j φ x
          = (-1) ^ j * ∫ x in (I : Set ℝ), g x * φ x :=
  memSobolevSpaceHigher_iff.trans SobolevIntervalLp.memSobolevIntervalLp_iff_forall_integral

omit [Fact (1 ≤ p)] in
/-- **The successive derivatives `Du, D²u, …, D^m u`.** For `u ∈ W^{m,p}(I)` the `j`-th
function `g_j` of the characterization is the component `u.deriv j` of the element:
`∫_I u D^j φ = (−1)^j ∫_I (D^j u) φ` for every test function `φ` (`u' = g₁`,
`(u')' = g₂`, …, `SobolevIntervalLp.hasWeakDerivOn_deriv_succ`). -/
theorem memSobolevSpaceHigher_deriv {m : ℕ} (u : SobolevIntervalLp m p I) (j : Fin (m + 1))
    (φ : 𝓓(I, ℝ)) :
    ∫ x in (I : Set ℝ), u.fn x * iteratedDeriv j φ x
      = (-1) ^ (j : ℕ) * ∫ x in (I : Set ℝ), u.deriv j x * φ x := by
  have := (SobolevIntervalLp.hasWeakIteratedDerivOn_deriv u j).integral_iteratedDeriv_mul φ
  simp only [mul_comm] at this ⊢
  exact this

/-- **The norm of `W^{m,p}(I)`.** `‖u‖_{W^{m,p}} = ‖u‖_p + ∑_{α=1}^m ‖D^α u‖_p`. -/
def sobolevNormHigher {m : ℕ} (u : SobolevIntervalLp m p I) : ℝ :=
  ‖u.deriv 0‖ + ∑ j : Fin m, ‖u.deriv j.succ‖

/-- The book's `W^{m,p}` norm is equivalent to the norm of the type (the `ℓ^p` sum of the
`‖D^α u‖_p`): `‖u‖ ≤ ‖u‖_{W^{m,p}} ≤ (m + 1) ‖u‖`. The backbone's
`SobolevIntervalLp.norm_le_sum_norm_deriv` and `sum_norm_deriv_le_mul_norm`. -/
theorem sobolevNormHigher_equiv {m : ℕ} (u : SobolevIntervalLp m p I) :
    ‖u‖ ≤ sobolevNormHigher u ∧ sobolevNormHigher u ≤ (m + 1) * ‖u‖ := by
  have e : sobolevNormHigher u = ∑ j : Fin (m + 1), ‖u.deriv j‖ := by
    rw [sobolevNormHigher, Fin.sum_univ_succ]
  rw [e]
  exact ⟨SobolevIntervalLp.norm_le_sum_norm_deriv u, SobolevIntervalLp.sum_norm_deriv_le_mul_norm u⟩

/-- **The scalar product of `H^m(I)`.**
`(u, v)_{H^m} = (u, v)_{L²} + ∑_{α=1}^m (D^α u, D^α v)_{L²}`. The backbone's
`SobolevIntervalLp.inner_eq`. -/
theorem inner_Hm {m : ℕ} (u v : SobolevIntervalLp m 2 I) :
    ⟪u, v⟫_ℝ = ⟪u.deriv 0, v.deriv 0⟫_ℝ + ∑ j : Fin m, ⟪u.deriv j.succ, v.deriv j.succ⟫_ℝ := by
  rw [SobolevIntervalLp.inner_eq, Fin.sum_univ_succ]

/-- **The interpolation inequality.** For every integer `j` with `1 ≤ j ≤ m − 1` and every
`ε > 0` there is a constant `C` (depending on `ε` and `|I| ≤ ∞`) such that
`‖D^j u‖_p ≤ ε ‖D^m u‖_p + C ‖u‖_p` for all `u ∈ W^{m,p}(I)`. The backbone's
`SobolevIntervalLp.eLpNorm_deriv_le_mul_add` (by a direct window estimate, not the book's
reference to Adams or Exercise 8.6). -/
theorem interpolationInequality (hI : (I : Set ℝ).OrdConnected) {m : ℕ} (j : ℕ) (hj1 : 1 ≤ j)
    (hjm : j < m) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ u : SobolevIntervalLp m p I,
      ‖u.deriv ⟨j, by omega⟩‖ ≤ ε * ‖u.deriv (Fin.last m)‖ + C * ‖u.deriv 0‖ := by
  obtain ⟨C, -, hC⟩ := SobolevIntervalLp.eLpNorm_deriv_le_mul_add (p := p) hI
    (⟨j, by omega⟩ : Fin (m + 1)) (by rw [Ne, Fin.ext_iff]; simp; omega)
    (by rw [Ne, Fin.ext_iff]; simp; omega) hε
  exact ⟨C, hC⟩

/-- **The norm `‖u‖_p + ‖D^m u‖_p` is equivalent to `‖u‖_{W^{m,p}}`** (the consequence of the
interpolation inequality the book states first), for `m ≥ 1`. The backbone's
`SobolevIntervalLp.exists_norm_le_mul_norm_deriv_add`. -/
theorem interpolationInequality_norm_equiv (hI : (I : Set ℝ).OrdConnected) (m : ℕ) :
    ∃ C : ℝ, ∀ u : SobolevIntervalLp (m + 1) p I,
      ‖u.deriv 0‖ + ‖u.deriv (Fin.last (m + 1))‖ ≤ sobolevNormHigher u ∧
      sobolevNormHigher u ≤ C * (‖u.deriv 0‖ + ‖u.deriv (Fin.last (m + 1))‖) := by
  obtain ⟨C, hC0, hC⟩ := SobolevIntervalLp.exists_norm_le_mul_norm_deriv_add (p := p) hI (m + 1)
  refine ⟨(m + 1 + 1) * C, fun u ↦ ⟨?_, ?_⟩⟩
  · unfold sobolevNormHigher
    have : ‖u.deriv (Fin.last (m + 1))‖ ≤ ∑ j : Fin (m + 1), ‖u.deriv j.succ‖ := by
      rw [← Fin.succ_last]
      exact Finset.single_le_sum (f := fun j : Fin (m + 1) ↦ ‖u.deriv j.succ‖)
        (fun j _ ↦ norm_nonneg _) (Finset.mem_univ (Fin.last m))
    linarith
  · calc sobolevNormHigher u ≤ (m + 1 + 1) * ‖u‖ := by
          have := (sobolevNormHigher_equiv u).2
          push_cast at this
          exact this
      _ ≤ (m + 1 + 1) * (C * (‖u.deriv 0‖ + ‖u.deriv (Fin.last (m + 1))‖)) := by
          gcongr
          exact hC u
      _ = (m + 1 + 1) * C * (‖u.deriv 0‖ + ‖u.deriv (Fin.last (m + 1))‖) := by ring

/-- **The closing sentence: `W^{m,p}(I) ⊆ C^{m−1}(Ī)` with continuous injection** for a bounded
`I = (a, b)`: the backbone's bounded linear map
`SobolevIntervalLp.toContDiffMapIcc hab : W^{k+1,p}(a, b) → C^k[a, b]` is injective and sends
`u` to a `C^k` function on `[a, b]` equal to `u` a.e. -/
theorem sobolevSpaceHigher_subset_contDiff {a b : ℝ} (hab : a < b) {m : ℕ} :
    Function.Injective (SobolevIntervalLp.toContDiffMapIcc (p := p) (m := m) hab) ∧
      ∀ u : SobolevIntervalLp (m + 1) p (Opens.Ioo a b),
        u.fn =ᵐ[volume.restrict (Ioo a b)] (SobolevIntervalLp.toContDiffMapIcc hab u).extend := by
  refine ⟨SobolevIntervalLp.toContDiffMapIcc_injective hab, fun u ↦ ?_⟩
  have h1 := SobolevIntervalLp.fn_ae_eq_rep (SobolevIntervalLp.ordConnected_coe_Ioo a b)
    (SobolevIntervalLp.derivOne u 0)
  rw [SobolevIntervalLp.fn_derivOne_zero] at h1
  refine h1.trans ((ae_restrict_mem measurableSet_Ioo).mono fun x hx ↦ ?_)
  rw [ContDiffMapIcc.extend_of_mem _ (Ioo_subset_Icc_self hx),
    SobolevIntervalLp.toContDiffMapIcc_apply]

/-- **The closing sentence, compactness**: for a bounded `I = (a, b)` and `1 < p ≤ ∞` the
injection `W^{m,p}(I) ⊆ C^{m−1}(Ī)` is compact. The backbone's
`SobolevIntervalLp.isCompactOperator_toContDiffMapIcc`. -/
theorem sobolevSpaceHigher_subset_contDiff_compact {a b : ℝ} (hab : a < b) {m : ℕ} (hp : 1 < p) :
    IsCompactOperator (SobolevIntervalLp.toContDiffMapIcc (p := p) (m := m) hab) :=
  SobolevIntervalLp.isCompactOperator_toContDiffMapIcc hab hp

end Brezis.Chapter08

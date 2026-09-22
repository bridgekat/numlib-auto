import Numlib.Analysis.Calculus.ContDiffConstOffCompact
import Numlib.Analysis.Distributions.TestFunctionOps
import Numlib.Analysis.PDE.Elliptic.Dirichlet
import Numlib.Analysis.Sobolev.Translate

/-!
# Regularity of weak solutions of elliptic equations

Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, §9.6:
L. Nirenberg's method of translations (difference quotients) for the weak solutions of the
Dirichlet problem for `-Δu + u = f`, and of second-order elliptic equations with `C¹`
coefficients, on an open `Ω ⊆ ℝ^N`.

## Contents

* **Difference quotients.** For an open set `Ω` invariant under the translation by `h`
  (`IsTranslationInvariant Ω h`), the translation `u ↦ u(· + h)` acts isometrically on `L^p(Ω)`
  (`MeasureTheory.Lp.translate`) and on `W^{k,p}(Ω)` (`SobolevMultiIndex.translateL`) and
  commutes with the weak derivatives (`Numlib/Analysis/Sobolev/Translate.lean`); the difference
  quotient `D_h u = (u(· + h) − u)/|h|` (`Elliptic.diffQuot`) is `Elliptic.diffQuotLp` on
  `L^p(Ω)` and `Elliptic.diffQuotL` on `W^{k,p}(Ω)`, with the adjointness
  `⟪D_h u, v⟫ = ⟪u, D_{−h} v⟫`.
* **Weak derivatives from bounded difference quotients**
  (`Elliptic.exists_hasWeakIteratedLineDerivOn_of_diffQuot_bounded`): if the difference quotients
  `D_{t y} u`, `t → 0`, are bounded in a Hilbert space `H` mapped continuously into `L²(Ω)`, then
  `∂_y u` exists, lies in `H`, and has norm at most the bound — the weak compactness that replaces
  both uses of Proposition 9.3 in the book's proof and the "delicate point" of Lemma 9.7.
* **Theorem 9.25.** The `H²` clause: case A (`Elliptic.regularity_top`), case B
  (`Elliptic.regularity_upperHalfSpace`, with Lemmas 9.6 and 9.7), case C₁ = Remark 25
  (`Elliptic.regularity_interior`, `regularity_interior_higher`), case C₂ through the charts
  (`Elliptic.transfer_chart`, Lemma 9.8), assembled in `Elliptic.regularity_dirichlet_mem` and,
  with the constant from the closed graph theorem, `Elliptic.regularity_dirichlet`. The
  `H^{m+2}` clause (`Elliptic.regularity_dirichlet_higher`, membership
  `regularity_dirichlet_higher_mem`) is the same induction on the order one level up: the
  multipliers `IsContDiffConstOffCompact` (smooth functions constant off a compact set,
  closed under derivatives, products and inversion,
  `Numlib/Analysis/Calculus/ContDiffConstOffCompact.lean`) keep `H^k` stable
  (`MemSobolevMultiIndex.mul_of_isContDiffConstOffCompact`), the differentiated
  variable-coefficient equation (`Elliptic.forall_testFunction_deriv_general`) drives the
  induction on the half space (`Elliptic.memSobolevMultiIndex_of_tangential_of_order`), and the
  chart transfers hold at every order (`Elliptic.memSobolevMultiIndex_comp_chart_of_order`). The
  `C²(Ω̄)` and `C^∞(Ω̄)` clauses (`Elliptic.regularity_dirichlet_contDiffOn`,
  `regularity_dirichlet_smooth`) follow from Corollary 9.15.

## References

[brezis2011functional], §9.6: Theorem 9.25 and its proof (cases A, B, C₁, C₂), Lemmas 9.6–9.8,
Remark 25.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology InnerProductSpace

noncomputable section

/-! ### The half space is invariant under the tangential translations -/

section InvariantHalfSpace

/-- The half space is invariant under the tangential translations `t • y`, `y_N = 0`. -/
theorem EuclideanSpace.isTranslationInvariant_upperHalfSpace {d : ℕ}
    {y : EuclideanSpace ℝ (Fin (d + 1))} (hy : y (Fin.last d) = 0) (t : ℝ) :
    IsTranslationInvariant (EuclideanSpace.upperHalfSpace d) (t • y) := fun x ↦ by
  simp [EuclideanSpace.mem_upperHalfSpace, hy]

end InvariantHalfSpace


/-! ### From second partial derivatives to `W^{2,p}(Ω)` -/

section MultiIndexTwo

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Ω : Opens E} {μ : Measure E} [IsLocallyFiniteMeasure μ]

/-- **`W^{1,p}(Ω)` by the basis directions**: `f ∈ W^{1,p}(Ω)` exactly when `f ∈ L^p(Ω)` and,
for every basis vector `b i`, `f` has a weak derivative along `b i` in `L^p(Ω)`. -/
theorem memSobolevMultiIndex_one_iff {f : E → F} :
    MemSobolevMultiIndex b f 1 p Ω μ ↔ MemLp f p (μ.restrict (Ω : Set E)) ∧ ∀ i,
      ∃ w : E → F, HasWeakIteratedLineDerivOn ![b i] f w Ω μ ∧
        MemLp w p (μ.restrict (Ω : Set E)) := by
  constructor
  · intro h
    refine ⟨h.memLp, fun i ↦ ?_⟩
    obtain ⟨w, hw, hwp⟩ := h.2 (Pi.single i 1) (by simp)
    exact ⟨w, hw.of_perm (multiIndexTuple_single_perm (b : ι → E) i), hwp⟩
  · rintro ⟨hf, hw⟩
    refine ⟨hf, fun α hα ↦ ?_⟩
    rcases MultiIndexLE.eq_zero_or_exists_eq_single (⟨α, hα⟩ : MultiIndexLE ι 1) with h0 | ⟨i, hi⟩
    · obtain rfl : α = 0 := congrArg Subtype.val h0
      exact ⟨f, HasWeakIteratedLineDerivOn.of_length_eq_zero (by simp) _
        (hf.locallyIntegrableOn Fact.out), hf⟩
    · obtain rfl : α = Pi.single i 1 := congrArg Subtype.val hi
      obtain ⟨w, hw, hwp⟩ := hw i
      exact ⟨w, hw.of_perm (multiIndexTuple_single_perm (b : ι → E) i).symm, hwp⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fact (1 ≤ p)] [IsLocallyFiniteMeasure μ] in
/-- A multi-index of order two is `e_j + e_i` for some `i`, `j`. -/
theorem exists_eq_single_add_single_of_sum_eq_two {α : ι → ℕ} (hα : ∑ i, α i = 2) :
    ∃ i j, α = Pi.single j 1 + Pi.single i 1 := by
  obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ, α i ≠ 0 :=
    Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := α) (by omega)
  obtain ⟨β, rfl⟩ : ∃ β : ι → ℕ, α = β + Pi.single i 1 := by
    refine ⟨α - Pi.single i 1, funext fun j ↦ ?_⟩
    by_cases hj : j = i
    · subst hj
      simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same]
      omega
    · simp [Pi.single_eq_of_ne hj]
  have hβ : ∑ j, β j = 1 := by
    simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
      ite_true] at hα
    omega
  rcases MultiIndexLE.eq_zero_or_exists_eq_single (⟨β, hβ.le⟩ : MultiIndexLE ι 1) with h0 | ⟨j, hj⟩
  · obtain rfl : β = 0 := congrArg Subtype.val h0
    simp at hβ
  · obtain rfl : β = Pi.single j 1 := congrArg Subtype.val hj
    exact ⟨i, j, rfl⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fact (1 ≤ p)] [IsLocallyFiniteMeasure μ] in
/-- The tuple naming `e_j + e_i` is a rearrangement of `![b i, b j]`. -/
theorem multiIndexTuple_single_add_single_perm (b : ι → E) (i j : ι) :
    (List.ofFn (multiIndexTuple b (Pi.single j 1 + Pi.single i 1))).Perm
      (List.ofFn ![b i, b j]) := by
  refine (multiIndexTuple_add_single_perm b (Pi.single j 1) i).symm.trans ?_
  rw [List.ofFn_cons]
  have := (multiIndexTuple_single_perm b j).cons (b i)
  simpa using this

namespace SobolevMultiIndex

variable [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F]

omit [Fact (1 ≤ p)] [IsLocallyFiniteMeasure μ] in
/-- The weak derivative `∂^α U` of an element is any `L^p(Ω)` element that is a weak derivative
of its function along the tuple naming `α`, by the uniqueness of weak derivatives. -/
theorem weakDeriv_eq_of_hasWeakIteratedLineDerivOn {k : ℕ} (U : SobolevMultiIndex F b k p Ω μ)
    {f : E → F} (hU : fn U =ᵐ[μ.restrict (Ω : Set E)] f) (α : MultiIndexLE ι k)
    {w : Lp F p (μ.restrict (Ω : Set E))}
    (hw : HasWeakIteratedLineDerivOn (multiIndexTuple (b : ι → E) α.1) f w Ω μ) :
    weakDeriv U α = w := by
  refine Lp.ext ?_
  have h := ((hasWeakIteratedLineDerivOn U α).congr_ae hU (EventuallyEq.refl _ _)).ae_eq hw
  exact (ae_restrict_iff' Ω.isOpen.measurableSet).2 h

omit [IsLocallyFiniteMeasure μ] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
/-- **The norm of `W^{k,2}(Ω)` from a uniform bound on the derivatives**: if `‖∂^α U‖₂ ≤ C` for
every `α` then `‖U‖ ≤ √(#{α}) C`. -/
theorem norm_le_sqrt_card_mul_of_forall_norm_weakDeriv_le {k : ℕ}
    (U : SobolevMultiIndex F b k 2 Ω μ) {C : ℝ} (hC : ∀ α, ‖weakDeriv U α‖ ≤ C) :
    ‖U‖ ≤ √(Fintype.card (MultiIndexLE ι k)) * C := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  rw [norm_eq_sum (p := 2) (by norm_num), ENNReal.toReal_ofNat, ← Real.sqrt_eq_rpow,
    ← Real.sqrt_sq hC0, ← Real.sqrt_mul (Nat.cast_nonneg _)]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ α : MultiIndexLE ι k, ‖weakDeriv U α‖ ^ (2 : ℝ)
      ≤ ∑ _α : MultiIndexLE ι k, C ^ 2 := by
        refine Finset.sum_le_sum fun α _ ↦ ?_
        rw [Real.rpow_two]
        exact pow_le_pow_left₀ (norm_nonneg _) (hC α) 2
    _ = Fintype.card (MultiIndexLE ι k) * C ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ]

/-- **`W^{2,p}(Ω)` from the second partial derivatives, with bounds**: if `u ∈ W^{1,p}(Ω)` and
each `∂ⱼu` has a weak derivative `w_{ij}` along every `b i`, an element of `L^p(Ω)` with
`‖w_{ij}‖_p ≤ C`, then `u` is the function of an element `U ∈ W^{2,p}(Ω)`, whose second
derivatives `∂^α U`, `|α| = 2`, are bounded by `C` and whose first derivatives are those of `u`.
The bookkeeping of the multi-indices: `α = e_j + e_i` names a rearrangement of `![b i, b j]`
(`multiIndexTuple_single_add_single_perm`), along which `w_{ij}` is a weak derivative of `u` by
`HasWeakIteratedLineDerivOn.cons`. -/
theorem exists_two_of_forall_exists (u : SobolevMultiIndex F b 1 p Ω μ) {C : ℝ}
    (h : ∀ i j, ∃ w : Lp F p (μ.restrict (Ω : Set E)), ‖w‖ ≤ C ∧
      HasWeakIteratedLineDerivOn ![b i] (weakDeriv u (MultiIndexLE.single j)) w Ω μ) :
    ∃ U : SobolevMultiIndex F b 2 p Ω μ, fn U =ᵐ[μ.restrict (Ω : Set E)] fn u ∧
      (∀ α : MultiIndexLE ι 2, ∑ i, α.1 i = 2 → ‖weakDeriv U α‖ ≤ C) ∧
      ∀ α : MultiIndexLE ι 2, ∑ i, α.1 i ≤ 1 → ‖weakDeriv U α‖ ≤ ‖u‖ := by
  choose w hwC hw using h
  have hd : ∀ j, HasWeakIteratedLineDerivOn ![b j] (fn u) (weakDeriv u (MultiIndexLE.single j))
      Ω μ := fun j ↦
    (hasWeakIteratedLineDerivOn u (MultiIndexLE.single j)).of_perm
      (multiIndexTuple_single_perm (b : ι → E) j)
  -- membership in `W^{2,p}(Ω)`
  have hmem : MemSobolevMultiIndex b (fn u) 2 p Ω μ := by
    refine memSobolevMultiIndex_succ_iff.2 ⟨memSobolevMultiIndex u, fun j ↦ ?_⟩
    refine ⟨weakDeriv u (MultiIndexLE.single j), hd j, memSobolevMultiIndex_one_iff.2
      ⟨Lp.memLp _, fun i ↦ ⟨w i j, hw i j, Lp.memLp _⟩⟩⟩
  obtain ⟨U, hU⟩ := hmem.exists_sobolevMultiIndex
  refine ⟨U, hU, fun α hα ↦ ?_, fun α hα ↦ ?_⟩
  · obtain ⟨i, j, hij⟩ := exists_eq_single_add_single_of_sum_eq_two hα
    have h2 : HasWeakIteratedLineDerivOn (multiIndexTuple (b : ι → E) α.1) (fn u) (w i j) Ω μ := by
      have := (hd j).cons (hw i j)
      refine this.of_perm ?_
      rw [hij]
      exact (multiIndexTuple_single_add_single_perm (b : ι → E) i j).symm
    rw [weakDeriv_eq_of_hasWeakIteratedLineDerivOn U hU α h2]
    exact hwC i j
  · have h1 : HasWeakIteratedLineDerivOn (multiIndexTuple (b : ι → E) α.1) (fn u)
        (weakDeriv u ⟨α.1, hα⟩) Ω μ := hasWeakIteratedLineDerivOn u ⟨α.1, hα⟩
    rw [weakDeriv_eq_of_hasWeakIteratedLineDerivOn U hU α h1]
    exact norm_weakDeriv_le u _

end SobolevMultiIndex

end MultiIndexTwo


/-! ### Difference quotients -/

namespace Elliptic

section DiffQuot

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F] {h : E}

/-- **The difference quotient** `D_h u = (τ_h u − u)/|h|`, `D_h u (x) = (u(x + h) − u(x))/|h|`,
of [brezis2011functional] §9.6, case A (the method of translations of L. Nirenberg). -/
def diffQuot (h : E) (u : E → F) : E → F := fun x ↦ ‖h‖⁻¹ • (u (x + h) - u x)

theorem diffQuot_apply (h : E) (u : E → F) (x : E) :
    diffQuot h u x = ‖h‖⁻¹ • (u (x + h) - u x) :=
  rfl

/-- The difference quotient as a scalar multiple of the difference of a translate and the
function, in the `Pi` operations. -/
theorem diffQuot_eq (h : E) (u : E → F) :
    diffQuot h u = ‖h‖⁻¹ • ((fun x ↦ u (x + h)) - u) :=
  rfl

/-- **The difference quotient commutes with the weak derivative** on an invariant open set:
`∂^y (D_h u) = D_h (∂^y u)`. -/
theorem _root_.HasWeakIteratedLineDerivOn.diffQuot [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [ProperSpace E] {μ : Measure E} [μ.IsAddRightInvariant] {Ω : Opens E}
    {n : ℕ} {y : Fin n → E} {u w : E → F}
    (hu : HasWeakIteratedLineDerivOn y u w Ω μ) (hΩ : IsTranslationInvariant (Ω : Set E) h) :
    HasWeakIteratedLineDerivOn y (diffQuot h u) (diffQuot h w) Ω μ :=
  ((hu.comp_add_right hΩ).sub hu).const_smul _

/-- The difference quotient of an `L^p(Ω)` function on an invariant open set is in `L^p(Ω)`. -/
theorem _root_.MeasureTheory.MemLp.diffQuot [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [μ.IsAddRightInvariant] {Ω : Opens E} {u : E → F} {p : ℝ≥0∞}
    (hu : MemLp u p (μ.restrict (Ω : Set E))) (hΩ : IsTranslationInvariant (Ω : Set E) h) :
    MemLp (diffQuot h u) p (μ.restrict (Ω : Set E)) :=
  ((hu.comp_add_right hΩ).sub hu).const_smul _

end DiffQuot

/-! ### Difference quotients on `L^p(Ω)` -/

section DiffQuotLp

variable {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure E} [μ.IsAddRightInvariant]
  {Ω : Opens E} {h : E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (F p) in
/-- **The difference quotient `D_h = (τ_h − 1)/|h|` on `L^p(Ω)`**, as a bounded linear map, for an
open set `Ω` invariant under the translation by `h`. -/
def diffQuotLp (hΩ : IsTranslationInvariant (Ω : Set E) h) :
    Lp F p (μ.restrict (Ω : Set E)) →L[ℝ] Lp F p (μ.restrict (Ω : Set E)) :=
  ‖h‖⁻¹ • ((Lp.translate F p hΩ).toContinuousLinearMap - ContinuousLinearMap.id ℝ _)

theorem diffQuotLp_apply (hΩ : IsTranslationInvariant (Ω : Set E) h)
    (u : Lp F p (μ.restrict (Ω : Set E))) :
    diffQuotLp F p hΩ u = ‖h‖⁻¹ • (Lp.translate F p hΩ u - u) :=
  rfl

/-- `diffQuotLp hΩ u` is the difference quotient `D_h u` almost everywhere on `Ω`. -/
theorem coeFn_diffQuotLp (hΩ : IsTranslationInvariant (Ω : Set E) h)
    (u : Lp F p (μ.restrict (Ω : Set E))) :
    diffQuotLp F p hΩ u =ᵐ[μ.restrict (Ω : Set E)] diffQuot h u := by
  rw [diffQuotLp_apply]
  filter_upwards [Lp.coeFn_smul (‖h‖⁻¹) (Lp.translate F p hΩ u - u),
    Lp.coeFn_sub (Lp.translate F p hΩ u) u, Lp.coeFn_translate hΩ u] with x h1 h2 h3
  rw [h1, Pi.smul_apply, h2, Pi.sub_apply, h3, diffQuot_apply]

/-- `‖D_h u‖_p ≤ 2 ‖h‖⁻¹ ‖u‖_p`. -/
theorem norm_diffQuotLp_apply_le (hΩ : IsTranslationInvariant (Ω : Set E) h)
    (u : Lp F p (μ.restrict (Ω : Set E))) :
    ‖diffQuotLp F p hΩ u‖ ≤ 2 * ‖h‖⁻¹ * ‖u‖ := by
  rw [diffQuotLp_apply, norm_smul, norm_inv, norm_norm]
  calc ‖h‖⁻¹ * ‖Lp.translate F p hΩ u - u‖ ≤ ‖h‖⁻¹ * (‖Lp.translate F p hΩ u‖ + ‖u‖) := by
        gcongr; exact norm_sub_le _ _
    _ = 2 * ‖h‖⁻¹ * ‖u‖ := by rw [LinearIsometry.norm_map]; ring

/-- **Adjointness of the difference quotients in `L²(Ω)`**: `⟪D_h u, v⟫ = ⟪u, D_{−h} v⟫`
([brezis2011functional] §9.6, proof of Theorem 9.25, case B: "`∫ D_h u φ = −∫ u D_{−h} φ`" up to
the sign convention of `D_{−h}`). -/
theorem inner_diffQuotLp (hΩ : IsTranslationInvariant (Ω : Set E) h)
    (u v : Lp ℝ 2 (μ.restrict (Ω : Set E))) :
    ⟪diffQuotLp ℝ 2 hΩ u, v⟫_ℝ = ⟪u, diffQuotLp ℝ 2 hΩ.neg v⟫_ℝ := by
  rw [diffQuotLp_apply, diffQuotLp_apply, inner_smul_left, inner_smul_right, inner_sub_left,
    inner_sub_right, Lp.inner_translate hΩ u v, norm_neg]
  simp

end DiffQuotLp

/-! ### Difference quotients on `W^{k,p}(Ω)` -/

section DiffQuotSobolev

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [ProperSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Ω : Opens E} {μ : Measure E} [μ.IsAddRightInvariant] {h : E}

open SobolevMultiIndex

variable (F b k p μ) in
/-- **The difference quotient `D_h = (τ_h − 1)/|h|` on `W^{k,p}(Ω)`**, as a bounded linear map,
for an open set `Ω` invariant under the translation by `h`: the proof of
[brezis2011functional] Theorem 9.25 tests the equation with `D_{−h}(D_h u)`, so `D_h u` must be
an element of the space and not merely a function. -/
def diffQuotL (hΩ : IsTranslationInvariant (Ω : Set E) h) :
    SobolevMultiIndex F b k p Ω μ →L[ℝ] SobolevMultiIndex F b k p Ω μ :=
  ‖h‖⁻¹ • ((translateL F b k p μ hΩ).toContinuousLinearMap - ContinuousLinearMap.id ℝ _)

theorem diffQuotL_apply (hΩ : IsTranslationInvariant (Ω : Set E) h)
    (u : SobolevMultiIndex F b k p Ω μ) :
    diffQuotL F b k p μ hΩ u = ‖h‖⁻¹ • (translateL F b k p μ hΩ u - u) :=
  rfl

/-- The weak derivatives of `D_h u` are the difference quotients `D_h (∂^α u)` of the weak
derivatives, as elements of `L^p(Ω)`. -/
theorem weakDeriv_diffQuotL (hΩ : IsTranslationInvariant (Ω : Set E) h)
    (u : SobolevMultiIndex F b k p Ω μ) (α : MultiIndexLE ι k) :
    weakDeriv (diffQuotL F b k p μ hΩ u) α = diffQuotLp F p hΩ (weakDeriv u α) :=
  rfl

/-- The function of `D_h u` is the difference quotient `D_h (fn u)`, almost everywhere on `Ω`. -/
theorem fn_diffQuotL (hΩ : IsTranslationInvariant (Ω : Set E) h)
    (u : SobolevMultiIndex F b k p Ω μ) :
    fn (diffQuotL F b k p μ hΩ u) =ᵐ[μ.restrict (Ω : Set E)] diffQuot h (fn u) :=
  coeFn_diffQuotLp hΩ (weakDeriv u 0)

/-- `D_h u ∈ W_0^{k,p}(Ω)` for `u ∈ W_0^{k,p}(Ω)` and an invariant `Ω`. -/
theorem diffQuotL_mem_zero (hΩ : IsTranslationInvariant (Ω : Set E) h)
    {u : SobolevMultiIndex F b k p Ω μ} (hu : u ∈ SobolevMultiIndexZero F b k p Ω μ) :
    diffQuotL F b k p μ hΩ u ∈ SobolevMultiIndexZero F b k p Ω μ := by
  rw [diffQuotL_apply]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (translateL_mem_zero hΩ hu) hu)

/-- `‖D_h u‖ ≤ 2 ‖h‖⁻¹ ‖u‖` in `W^{k,p}(Ω)`. -/
theorem norm_diffQuotL_apply_le (hΩ : IsTranslationInvariant (Ω : Set E) h)
    (u : SobolevMultiIndex F b k p Ω μ) :
    ‖diffQuotL F b k p μ hΩ u‖ ≤ 2 * ‖h‖⁻¹ * ‖u‖ := by
  rw [diffQuotL_apply, norm_smul, norm_inv, norm_norm]
  calc ‖h‖⁻¹ * ‖translateL F b k p μ hΩ u - u‖
      ≤ ‖h‖⁻¹ * (‖translateL F b k p μ hΩ u‖ + ‖u‖) := by gcongr; exact norm_sub_le _ _
    _ = 2 * ‖h‖⁻¹ * ‖u‖ := by rw [LinearIsometry.norm_map]; ring

end DiffQuotSobolev


/-! ### Weak derivatives from bounded difference quotients -/

section WeakLimit

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [ProperSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure E}
  [μ.IsAddRightInvariant] {Ω : Opens E} {h : E}

/-- **Adjointness of the difference quotient against a test function**:
`∫_Ω φ D_h u = ∫_Ω (D_{−h} φ) u` for a locally integrable `u` on an invariant open set — the
change of variables `x ↦ x − h`. -/
theorem integral_smul_diffQuot_eq {u : E → F} (hu : LocallyIntegrableOn u Ω μ)
    (hΩ : IsTranslationInvariant (Ω : Set E) h) (φ : 𝓓(Ω, ℝ)) :
    ∫ x in (Ω : Set E), φ x • diffQuot h u x ∂μ
      = ∫ x in (Ω : Set E), diffQuot (-h) (φ : E → ℝ) x • u x ∂μ := by
  have h1 : Integrable (fun x ↦ φ x • u (x + h)) μ :=
    LocallyIntegrableOn.integrable_smul_left_of_tsupport_subset
      (LocallyIntegrableOn.comp_add_right hu hΩ) φ.continuous φ.hasCompactSupport
      φ.tsupport_subset
  have h2 : Integrable (fun x ↦ φ x • u x) μ :=
    LocallyIntegrableOn.integrable_smul_left_of_tsupport_subset hu φ.continuous
      φ.hasCompactSupport φ.tsupport_subset
  have h3 : Integrable (fun x ↦ φ (x - h) • u x) μ := by
    have := LocallyIntegrableOn.integrable_smul_left_of_tsupport_subset hu
      (φ.compAddRightOn hΩ.neg).continuous (φ.compAddRightOn hΩ.neg).hasCompactSupport
      (φ.compAddRightOn hΩ.neg).tsupport_subset
    simpa [sub_eq_add_neg] using this
  have e : ∀ x, φ x • diffQuot h u x = ‖h‖⁻¹ • (φ x • u (x + h) - φ x • u x) := fun x ↦ by
    rw [diffQuot_apply, smul_comm, smul_sub]
  simp_rw [e]
  rw [integral_smul, integral_sub h1.integrableOn h2.integrableOn,
    integral_smul_comp_add_right (μ := μ) u hΩ φ, ← integral_sub h3.integrableOn h2.integrableOn,
    ← integral_smul]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [diffQuot_apply, norm_neg, ← sub_eq_add_neg, smul_sub, smul_smul, smul_eq_mul,
    mul_sub, sub_smul]

omit [μ.IsAddRightInvariant] in
/-- **The difference quotients of a test function converge**: for `u` locally integrable on an
open set `Ω` invariant under the translations `t • y`, `‖y‖ = 1`, and `t_n → 0⁺`,
`∫_Ω (D_{−t_n y} φ) u → −∫_Ω (∂_y φ) u`, by dominated convergence — the pointwise limit is the
derivative of `s ↦ φ(x − s y)` at `0` and the quotients are dominated by `‖∇φ‖_∞` on a fixed
compact subset of `Ω`. -/
theorem tendsto_integral_diffQuot_neg_smul {u : E → F} (hu : LocallyIntegrableOn u Ω μ)
    {y : E} (hy : ‖y‖ = 1) (hΩ : ∀ t : ℝ, IsTranslationInvariant (Ω : Set E) (t • y))
    {t : ℕ → ℝ} (htpos : ∀ n, 0 < t n) (ht1 : ∀ n, t n ≤ 1) (ht0 : Tendsto t atTop (𝓝 0))
    (φ : 𝓓(Ω, ℝ)) :
    Tendsto (fun n ↦ ∫ x in (Ω : Set E), diffQuot (-(t n • y)) (φ : E → ℝ) x • u x ∂μ) atTop
      (𝓝 (∫ x in (Ω : Set E), (-(fderiv ℝ φ x y)) • u x ∂μ)) := by
  -- the compact set carrying all the translated supports
  obtain ⟨K, hKc, hKΩ, hK⟩ : ∃ K : Set E, IsCompact K ∧ K ⊆ (Ω : Set E) ∧
      ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → ∀ x, x - s • y ∈ tsupport φ → x ∈ K := by
    refine ⟨(fun q : E × ℝ ↦ q.1 + q.2 • y) '' (tsupport φ ×ˢ Icc (0 : ℝ) 1),
      (φ.hasCompactSupport.prod isCompact_Icc).image (by fun_prop), ?_, ?_⟩
    · rintro _ ⟨⟨x, s⟩, ⟨hx, -⟩, rfl⟩
      exact (hΩ s).mem (φ.tsupport_subset hx)
    · intro s hs x hx
      exact ⟨(x - s • y, s), ⟨hx, hs⟩, by simp⟩
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  -- a bound on the gradient of `φ`
  obtain ⟨M, hM⟩ := (φ.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (φ.contDiff.continuous_fderiv (by simp))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hlip : ∀ x z : E, ‖(φ : E → ℝ) z - φ x‖ ≤ M * ‖z - x‖ := fun x z ↦
    Convex.norm_image_sub_le_of_norm_fderiv_le (fun _ _ ↦ (φ.contDiff.differentiable
      (by simp)).differentiableAt) (fun x _ ↦ hM x) convex_univ (mem_univ x) (mem_univ z)
  have hQ : ∀ n x, diffQuot (-(t n • y)) (φ : E → ℝ) x
      = (t n)⁻¹ * ((φ : E → ℝ) (x - t n • y) - φ x) := fun n x ↦ by
    rw [diffQuot_apply, norm_neg, norm_smul, hy, mul_one, Real.norm_eq_abs,
      abs_of_pos (htpos n), smul_eq_mul, ← sub_eq_add_neg]
  have ht0' : Tendsto t atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨ht0, Eventually.of_forall fun n ↦ (htpos n).ne'⟩
  have hQcont : ∀ n, Continuous (diffQuot (-(t n • y)) (φ : E → ℝ)) := fun n ↦ by
    change Continuous fun x ↦ ‖-(t n • y)‖⁻¹ • ((φ : E → ℝ) (x + -(t n • y)) - φ x)
    fun_prop
  refine tendsto_integral_of_dominated_convergence (fun x ↦ M * ‖K.indicator u x‖)
    (fun n ↦ (hQcont n).aestronglyMeasurable.smul
      (hu.aestronglyMeasurable.mono_measure le_rfl)) ?_
    (fun n ↦ Eventually.of_forall fun x ↦ ?_) (Eventually.of_forall fun x ↦ ?_)
  · exact (((integrable_indicator_iff hKm).2 (hu.integrableOn_compact_subset hKΩ hKc)).norm
      |>.const_mul _).mono_measure Measure.restrict_le_self
  · -- the domination
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx, norm_smul, hQ]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos (htpos n)]
      calc (t n)⁻¹ * |(φ : E → ℝ) (x - t n • y) - φ x|
          ≤ (t n)⁻¹ * (M * ‖x - t n • y - x‖) :=
            mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hlip x (x - t n • y))
              (inv_nonneg.2 (htpos n).le)
        _ = M := by
            rw [sub_sub_cancel_left, norm_neg, norm_smul, hy, mul_one, Real.norm_eq_abs,
              abs_of_pos (htpos n), mul_comm M, ← mul_assoc, inv_mul_cancel₀ (htpos n).ne',
              one_mul]
    · have hφ0 : (φ : E → ℝ) (x - t n • y) = 0 := by
        by_contra hne
        exact hx (hK (t n) ⟨(htpos n).le, ht1 n⟩ x (subset_tsupport _ hne))
      have hφ0' : (φ : E → ℝ) x = 0 := by
        by_contra hne
        refine hx (hK 0 ⟨le_rfl, zero_le_one⟩ x ?_)
        simpa using subset_tsupport _ hne
      rw [hQ, hφ0, hφ0', sub_zero, mul_zero, zero_smul, norm_zero, Set.indicator_of_notMem hx,
        norm_zero, mul_zero]
  · -- the pointwise limit
    refine Tendsto.smul_const ?_ (u x)
    have hd : HasDerivAt (fun s : ℝ ↦ (φ : E → ℝ) (x - s • y)) (fderiv ℝ φ x (-y)) 0 := by
      have := ((φ.contDiff.differentiable (by simp)) (x - (0 : ℝ) • y)).hasFDerivAt
        |>.comp_hasDerivAt (0 : ℝ) (((hasDerivAt_id (0 : ℝ)).smul_const y).const_sub x)
      simpa [Function.comp_def] using this
    have := (hasDerivAt_iff_tendsto_slope.1 hd).comp ht0'
    rw [map_neg] at this
    refine this.congr fun n ↦ ?_
    simp [slope_def_module, hQ]

end WeakLimit

section WeakLimit'

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [ProperSpace E] {μ : Measure E} [μ.IsAddRightInvariant]
  [IsFiniteMeasureOnCompacts μ] {Ω : Opens E}

/-- A weak limit in a Hilbert space has norm at most the bound of the sequence:
if `‖v n‖ ≤ M` and `⟪v n, w⟫ → ⟪w, w⟫` then `‖w‖ ≤ M`. -/
theorem norm_le_of_tendsto_inner {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {v : ℕ → H} {w : H} {M : ℝ} (hM : 0 ≤ M) (hv : ∀ n, ‖v n‖ ≤ M)
    (hlim : Tendsto (fun n ↦ ⟪w, v n⟫_ℝ) atTop (𝓝 ⟪w, w⟫_ℝ)) : ‖w‖ ≤ M := by
  have hle : ⟪w, w⟫_ℝ ≤ ‖w‖ * M := by
    refine le_of_tendsto' hlim fun n ↦ ?_
    calc ⟪w, v n⟫_ℝ ≤ ‖w‖ * ‖v n‖ := real_inner_le_norm _ _
      _ ≤ ‖w‖ * M := by gcongr; exact hv n
  rw [real_inner_self_eq_norm_sq] at hle
  rcases (norm_nonneg w).eq_or_lt with hw | hw
  · rw [← hw]; exact hM
  · nlinarith

/-- **Weak derivatives from bounded difference quotients.** Let `H` be a real Hilbert space with
a bounded linear map `ι : H → L²(Ω)`, let `u` be locally integrable on an open set `Ω` invariant
under the translations `t • y`, `‖y‖ = 1`, and let `t_n → 0⁺`. If the difference quotients
`D_{t_n y} u` are the images of a bounded sequence `v_n` of `H`, `‖v_n‖ ≤ M`, then `u` has a weak
derivative along `y` on `Ω` of the form `ι w` with `w ∈ H` and `‖w‖ ≤ M`.

This is the weak compactness step of the method of translations: a subsequence of `v_n`
converges weakly in the reflexive space `H` (`NormedSpace.exists_subseq_forall_dual_tendsto`),
the pairings `∫_Ω (D_{t_n y} u) φ = ∫_Ω u D_{−t_n y} φ` against a test function converge to
`−∫_Ω u ∂_y φ` (`tendsto_integral_diffQuot_neg_smul`), which identifies the weak limit as the
weak derivative, and the norm bound is the weak lower semicontinuity of the norm. In
[brezis2011functional] §9.6 it appears as "applying Proposition 9.3 once more" in case A, as the
limit `h → 0` in (56) in case B, and as the "delicate point" of Lemma 9.7 (with `H = H^1_0`). -/
theorem exists_hasWeakIteratedLineDerivOn_of_diffQuot_bounded {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (ι : H →L[ℝ] Lp ℝ 2 (μ.restrict (Ω : Set E))) {u : E → ℝ} (hu : LocallyIntegrableOn u Ω μ)
    {y : E} (hy : ‖y‖ = 1) (hΩ : ∀ t : ℝ, IsTranslationInvariant (Ω : Set E) (t • y))
    {t : ℕ → ℝ} (htpos : ∀ n, 0 < t n) (ht1 : ∀ n, t n ≤ 1) (ht0 : Tendsto t atTop (𝓝 0))
    {v : ℕ → H} {M : ℝ} (hv : ∀ n, ‖v n‖ ≤ M)
    (hιv : ∀ n, ι (v n) =ᵐ[μ.restrict (Ω : Set E)] diffQuot (t n • y) u) :
    ∃ w : H, ‖w‖ ≤ M ∧ HasWeakIteratedLineDerivOn ![y] u (ι w) Ω μ := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hv 0)
  obtain ⟨w, σ, hσ, hw⟩ := NormedSpace.exists_subseq_forall_dual_tendsto (𝕜 := ℝ) hv
  refine ⟨w, norm_le_of_tendsto_inner hM (fun k ↦ hv (σ k)) (hw (innerSL ℝ w)), ?_⟩
  have hιw : LocallyIntegrableOn (ι w) Ω μ :=
    (Lp.memLp (ι w)).locallyIntegrableOn one_le_two
  refine ⟨hu, hιw, fun φ ↦ ?_⟩
  -- the pairing with `φ` as a continuous linear functional on `H`
  have hφ2 : MemLp (φ : E → ℝ) 2 (μ.restrict (Ω : Set E)) := (φ.memLp 2 μ).restrict _
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Lp ℝ 2 (μ.restrict (Ω : Set E)), Φ = hφ2.toLp φ := ⟨_, rfl⟩
  have hΦφ : ⇑Φ =ᵐ[μ.restrict (Ω : Set E)] φ := by rw [hΦ]; exact hφ2.coeFn_toLp
  have hpair : ∀ z : H, ⟪Φ, ι z⟫_ℝ = ∫ x in (Ω : Set E), φ x • (ι z) x ∂μ := fun z ↦ by
    rw [L2.inner_def]
    refine integral_congr_ae (hΦφ.mono fun x hx ↦ ?_)
    simp [hx, mul_comm]
  have hlim₁ := hw ((innerSL ℝ Φ).comp ι)
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, hpair] at hlim₁
  -- the pairings of the difference quotients converge to the derivative
  have hlim₂ : Tendsto (fun k ↦ ∫ x in (Ω : Set E), φ x • (ι (v (σ k))) x ∂μ) atTop
      (𝓝 (∫ x in (Ω : Set E), (-(fderiv ℝ φ x y)) • u x ∂μ)) := by
    have := (tendsto_integral_diffQuot_neg_smul hu hy hΩ htpos ht1 ht0 φ).comp hσ.tendsto_atTop
    refine this.congr fun k ↦ ?_
    simp only [Function.comp_def]
    rw [← integral_smul_diffQuot_eq hu (hΩ (t (σ k))) φ]
    refine integral_congr_ae ((hιv (σ k)).mono fun x hx ↦ ?_)
    dsimp only
    rw [hx]
  have key := tendsto_nhds_unique hlim₁ hlim₂
  simp only [iteratedFDeriv_one_apply, Matrix.cons_val_zero, pow_one, neg_one_smul]
  rw [key, ← integral_neg]
  exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp)

end WeakLimit'


/-! ### Lemma 9.6: the difference quotient is bounded by the gradient -/

section TranslateNorm

variable {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure E} [μ.IsAddRightInvariant]
  {Ω : Opens E} {h : E}

/-- An `eLpNorm` translation estimate `‖f(· + h) − f‖_{L²(Ω)} ≤ ‖h‖ C` for the function of an
`L²(Ω)` element is a bound `‖τ_h f − f‖ ≤ ‖h‖ C` on the norm of the element. -/
theorem norm_translateLp_sub_le_of_eLpNorm_le (hΩ : IsTranslationInvariant (Ω : Set E) h)
    (f : Lp F 2 (μ.restrict (Ω : Set E))) {C : ℝ} (hC : 0 ≤ C)
    (hf : eLpNorm (fun x ↦ f (x + h) - f x) 2 (μ.restrict (Ω : Set E))
      ≤ ‖h‖ₑ * ENNReal.ofReal C) :
    ‖Lp.translate F 2 hΩ f - f‖ ≤ ‖h‖ * C := by
  rw [Lp.norm_def, ← ENNReal.toReal_ofReal (mul_nonneg (norm_nonneg h) hC)]
  refine ENNReal.toReal_mono ENNReal.ofReal_ne_top ?_
  rw [ENNReal.ofReal_mul (norm_nonneg h), ofReal_norm]
  refine le_trans (le_of_eq (eLpNorm_congr_ae ?_)) hf
  filter_upwards [Lp.coeFn_sub (Lp.translate F 2 hΩ f) f, Lp.coeFn_translate hΩ f] with x h1 h2
  rw [h1, Pi.sub_apply, h2]

/-- `‖D_h f‖ ≤ C` for `f ∈ L²(Ω)` with the translation estimate `‖f(· + h) − f‖₂ ≤ ‖h‖ C`. -/
theorem norm_diffQuotLp_le_of_eLpNorm_le (hΩ : IsTranslationInvariant (Ω : Set E) h)
    (f : Lp F 2 (μ.restrict (Ω : Set E))) {C : ℝ} (hC : 0 ≤ C)
    (hf : eLpNorm (fun x ↦ f (x + h) - f x) 2 (μ.restrict (Ω : Set E))
      ≤ ‖h‖ₑ * ENNReal.ofReal C) :
    ‖diffQuotLp F 2 hΩ f‖ ≤ C := by
  rcases eq_or_ne h 0 with rfl | hh
  · rw [diffQuotLp_apply, norm_zero, inv_zero, zero_smul, norm_zero]
    exact hC
  rw [diffQuotLp_apply, norm_smul, norm_inv, norm_norm]
  calc ‖h‖⁻¹ * ‖Lp.translate F 2 hΩ f - f‖ ≤ ‖h‖⁻¹ * (‖h‖ * C) := by
        gcongr
        exact norm_translateLp_sub_le_of_eLpNorm_le hΩ f hC hf
    _ = C := by rw [← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.2 hh), one_mul]

end TranslateNorm

section Euclidean

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

open SobolevMultiIndex

/-- The operator norm of a linear functional on `ℝ^N` is the Euclidean norm of its values on the
standard basis: `‖L‖ = √(∑ᵢ (L eᵢ)²)`, by the Riesz representation `L = ⟪v, ·⟫`, `vᵢ = L eᵢ`. -/
theorem _root_.ContinuousLinearMap.norm_eq_sqrt_sum_sq_single
    (L : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ) :
    ‖L‖ = √(∑ i, (L (EuclideanSpace.single i 1)) ^ 2) := by
  obtain ⟨v, hv⟩ : ∃ v, v = (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin N))).symm L :=
    ⟨_, rfl⟩
  have hLv : ∀ z, L z = ⟪v, z⟫_ℝ := fun z ↦ by
    rw [hv, InnerProductSpace.toDual_symm_apply]
  have hnorm : ‖L‖ = ‖v‖ := by
    rw [hv, LinearIsometryEquiv.norm_map]
  rw [hnorm, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hLv, EuclideanSpace.inner_single_right, Real.norm_eq_abs, sq_abs]
  simp

/-- `∫ ‖f‖ₑ² = ‖f‖₂²` in `ℝ≥0∞`. -/
theorem _root_.MeasureTheory.lintegral_enorm_rpow_two_eq {X G : Type*} [MeasurableSpace X]
    [NormedAddCommGroup G] {ν : Measure X} {f : X → G} (hf : AEStronglyMeasurable f ν) :
    ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂ν = eLpNorm f 2 ν ^ (2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hf,
    ENNReal.toReal_ofNat, ← ENNReal.rpow_mul]
  norm_num

/-- **The `L²` norm of the tensor weak derivative is the gradient norm**: for
`v ∈ H^1(Ω)` and `w : ℝ^N → (ℝ^N →L ℝ)` with `w x eᵢ = ∂ᵢv x` almost everywhere,
`‖w‖_{L²(Ω)} = ‖∇v‖_{L²(Ω)} = (∑ᵢ ‖∂ᵢv‖₂²)^{1/2}`. -/
theorem _root_.SobolevEuclidean.eLpNorm_eq_gradNorm_of_forall_ae_eq (v : SobolevEuclidean N 1 2 Ω)
    {w : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ}
    (hwm : AEStronglyMeasurable w (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (hw : ∀ i, (fun x ↦ w x (EuclideanSpace.single i 1))
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        weakDeriv v (MultiIndexLE.single i)) :
    eLpNorm w 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
      = ENNReal.ofReal (gradNorm v) := by
  have hall : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      ∀ i, w x (EuclideanSpace.single i 1) = weakDeriv v (MultiIndexLE.single i) x :=
    ae_all_iff.2 hw
  have hpt : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      ‖w x‖ₑ ^ (2 : ℝ) = ∑ i, ‖weakDeriv v (MultiIndexLE.single i) x‖ₑ ^ (2 : ℝ) := by
    filter_upwards [hall] with x hx
    rw [← ofReal_norm (w x), ContinuousLinearMap.norm_eq_sqrt_sum_sq_single,
      ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num), Real.rpow_two,
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _),
      ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ sq_nonneg _)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hx i, ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
      Real.norm_eq_abs, Real.rpow_two, sq_abs]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hwm,
    ENNReal.toReal_ofNat, lintegral_congr_ae hpt, lintegral_finsetSum' _
    fun i _ ↦ (Lp.aestronglyMeasurable _).enorm.pow_const _]
  have hi : ∀ i, ∫⁻ x, ‖weakDeriv v (MultiIndexLE.single i) x‖ₑ ^ (2 : ℝ)
      ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
      = ENNReal.ofReal (‖weakDeriv v (MultiIndexLE.single i)‖ ^ 2) := fun i ↦ by
    rw [lintegral_enorm_rpow_two_eq (Lp.aestronglyMeasurable _), Lp.norm_def,
      ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _),
      ← ENNReal.rpow_natCast, Nat.cast_ofNat]
  simp only [hi]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ sq_nonneg _),
    ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (by norm_num),
    gradNorm_eq_sqrt, Real.sqrt_eq_rpow]

/-- **The translation estimate for `H^1(Ω)` with the gradient norm**: for `v ∈ H^1(Ω)` and `h`
with the segments `[x, x + h]`, `x ∈ Ω`, inside `Ω`,
`‖v(· + h) − v‖_{L²(Ω)} ≤ ‖h‖ ‖∇v‖_{L²(Ω)}` — Proposition 9.3, (i) ⇒ (iii), on `V = Ω`
(`HasWeakFDerivOn.eLpNorm_sub_translate_le`), with the tensor weak derivative measured by
`SobolevEuclidean.eLpNorm_eq_gradNorm_of_forall_ae_eq`. -/
theorem _root_.SobolevEuclidean.eLpNorm_fn_sub_translate_le_gradNorm_of_segments
    (v : SobolevEuclidean N 1 2 Ω) (h : EuclideanSpace ℝ (Fin N))
    (hseg : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin N))), ∀ t ∈ Icc (0 : ℝ) 1, x + t • h ∈ Ω) :
    eLpNorm (fun x ↦ fn v (x + h) - fn v x) 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
      ≤ ‖h‖ₑ * ENNReal.ofReal (gradNorm v) := by
  obtain ⟨w, hw, hwp, hwi, -⟩ := exists_hasWeakFDerivOn_fn v
  have hwn := SobolevEuclidean.eLpNorm_eq_gradNorm_of_forall_ae_eq v hwp.aestronglyMeasurable
    (fun i ↦ by simpa using hwi i)
  have key := hw.eLpNorm_sub_translate_le (memLp v) hwp one_le_two ENNReal.ofNat_ne_top
    Ω.isOpen h hseg
  rwa [hwn] at key

/-- **Lemma 9.6, on `L²(Ω)`**: for `v ∈ H^1(Ω)`, an open set `Ω` invariant under the translation
by `h` and containing the segments `[x, x + h]`, `x ∈ Ω`, the difference quotient satisfies
`‖D_h v‖_{L²(Ω)} ≤ ‖∇v‖_{L²(Ω)}` ([brezis2011functional] §9.6, Lemma 9.6, and the inequality
`‖D_{−h} v‖₂ ≤ ‖∇v‖₂` of case A). -/
theorem norm_diffQuotLp_fnL_le {h : EuclideanSpace ℝ (Fin N)}
    (hΩ : IsTranslationInvariant (Ω : Set (EuclideanSpace ℝ (Fin N))) h)
    (hseg : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin N))), ∀ t ∈ Icc (0 : ℝ) 1, x + t • h ∈ Ω)
    (v : SobolevEuclidean N 1 2 Ω) :
    ‖diffQuotLp ℝ 2 hΩ (fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v)‖
      ≤ gradNorm v :=
  norm_diffQuotLp_le_of_eLpNorm_le hΩ _ (gradNorm_nonneg v)
    (SobolevEuclidean.eLpNorm_fn_sub_translate_le_gradNorm_of_segments v h hseg)

end Euclidean


/-! ### The tangential estimate for a variable-coefficient form -/

section Coefficients

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))} {h : EuclideanSpace ℝ (Fin N)}

open SobolevMultiIndex

/-- The norm of an `L^∞` element is bounded by an almost everywhere bound on its function. -/
theorem _root_.MeasureTheory.Lp.norm_top_le_of_ae_bound {X G : Type*} [MeasurableSpace X]
    [NormedAddCommGroup G] {ν : Measure X} {f : Lp G ⊤ ν} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ᵐ x ∂ν, ‖f x‖ ≤ C) : ‖f‖ ≤ C := by
  rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable f)]
  exact ENNReal.toReal_le_of_le_ofReal hC (eLpNormEssSup_le_of_ae_bound hf)

/-- **The product formula for difference quotients**:
`D_h (a f) = a(· + h) D_h f + (D_h a) f` in `L²(Ω)`, for `a ∈ L^∞(Ω)` and `f ∈ L²(Ω)`
([brezis2011functional] §9.6, the displayed identity before (65)). -/
theorem diffQuotLp_mulL (hΩ : IsTranslationInvariant (Ω : Set (EuclideanSpace ℝ (Fin N))) h)
    (a : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    diffQuotLp ℝ 2 hΩ (mulL Ω a f)
      = mulL Ω (Lp.translate ℝ ⊤ hΩ a) (diffQuotLp ℝ 2 hΩ f) + mulL Ω (diffQuotLp ℝ ⊤ hΩ a) f := by
  refine Lp.ext ?_
  have h1 := hΩ.measurePreserving.quasiMeasurePreserving.ae_eq_comp (coeFn_mulL Ω a f)
  filter_upwards [coeFn_diffQuotLp hΩ (mulL Ω a f), h1, coeFn_mulL Ω a f,
    Lp.coeFn_add (mulL Ω (Lp.translate ℝ ⊤ hΩ a) (diffQuotLp ℝ 2 hΩ f))
      (mulL Ω (diffQuotLp ℝ ⊤ hΩ a) f),
    coeFn_mulL Ω (Lp.translate ℝ ⊤ hΩ a) (diffQuotLp ℝ 2 hΩ f),
    coeFn_mulL Ω (diffQuotLp ℝ ⊤ hΩ a) f, Lp.coeFn_translate hΩ a, coeFn_diffQuotLp hΩ f,
    coeFn_diffQuotLp hΩ a] with x e1 e2 e3 e4 e5 e6 e7 e8 e9
  rw [e1, e4, Pi.add_apply, e5, e6, e7, e8, e9, diffQuot_apply, diffQuot_apply, diffQuot_apply,
    e3]
  simp only [Function.comp_def] at e2
  rw [e2]
  simp only [smul_eq_mul]
  ring

/-- **The difference quotient of a `C¹` coefficient is bounded by its Lipschitz constant**: if
`a ∈ L^∞(Ω)` agrees almost everywhere with a function `a'` that is `C¹` on `Ω` with
`‖∇a'‖ ≤ M` on `Ω`, and the segments `[x, x + h]`, `x ∈ Ω`, lie in `Ω`, then `‖D_h a‖_∞ ≤ M` —
the mean value theorem along the segment ([brezis2011functional] §9.6, "`|D_h a_{kℓ}| ≤ C`"). -/
theorem norm_diffQuotLp_top_le (hΩ : IsTranslationInvariant (Ω : Set (EuclideanSpace ℝ (Fin N))) h)
    (hseg : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin N))), ∀ t ∈ Icc (0 : ℝ) 1, x + t • h ∈ Ω)
    {a : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    {a' : EuclideanSpace ℝ (Fin N) → ℝ}
    (haa' : ⇑a =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] a')
    (ha' : ContDiffOn ℝ 1 a' Ω) {M : ℝ} (hM : 0 ≤ M)
    (haM : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin N))), ‖fderiv ℝ a' x‖ ≤ M) :
    ‖diffQuotLp ℝ ⊤ hΩ a‖ ≤ M := by
  refine Lp.norm_top_le_of_ae_bound hM ?_
  have h1 := hΩ.measurePreserving.quasiMeasurePreserving.ae_eq_comp haa'
  simp only [Function.comp_def] at h1
  filter_upwards [coeFn_diffQuotLp hΩ a, haa', h1,
    self_mem_ae_restrict Ω.isOpen.measurableSet] with x e1 e2 e3 hx
  rw [e1, diffQuot_apply, e2, e3]
  rcases eq_or_ne h 0 with rfl | hh
  · simp [hM]
  -- the mean value theorem on the segment `[x, x + h] ⊆ Ω`
  have hsegΩ : segment ℝ x (x + h) ⊆ (Ω : Set (EuclideanSpace ℝ (Fin N))) := by
    rw [segment_eq_image']
    rintro _ ⟨t, ht, rfl⟩
    rw [add_sub_cancel_left]
    exact hseg x hx t ht
  have hmvt : ‖a' (x + h) - a' x‖ ≤ M * ‖x + h - x‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z hz ↦ (ha'.differentiableOn one_ne_zero).differentiableAt
        (Ω.isOpen.mem_nhds (hsegΩ hz)))
      (fun z hz ↦ haM z (hsegΩ hz)) (convex_segment _ _) (left_mem_segment _ _ _)
      (right_mem_segment _ _ _)
  rw [add_sub_cancel_left] at hmvt
  rw [norm_smul, norm_inv, norm_norm]
  calc ‖h‖⁻¹ * ‖a' (x + h) - a' x‖ ≤ ‖h‖⁻¹ * (M * ‖h‖) := by gcongr
    _ = M := by rw [mul_comm M, ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.2 hh), one_mul]

/-- The ellipticity condition is invariant under a translation leaving `Ω` invariant. -/
theorem isUniformlyElliptic_translateLp
    (hΩ : IsTranslationInvariant (Ω : Set (EuclideanSpace ℝ (Fin N))) h)
    {A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))} {α : ℝ}
    (hA : IsUniformlyElliptic Ω A α) :
    IsUniformlyElliptic Ω (fun k l ↦ Lp.translate ℝ ⊤ hΩ (A k l)) α := by
  refine ⟨hA.1, ?_⟩
  have h1 := hΩ.measurePreserving.quasiMeasurePreserving.ae hA.2
  have h2 : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      ∀ k l, Lp.translate ℝ ⊤ hΩ (A k l) x = A k l (x + h) :=
    ae_all_iff.2 fun k ↦ ae_all_iff.2 fun l ↦ Lp.coeFn_translate hΩ (A k l)
  filter_upwards [h1, h2] with x hx hx' ξ
  simp only [hx']
  exact hx ξ

/-- **The lower-order term of the tangential estimate**: for coefficients `B_{kℓ} ∈ L^∞(Ω)` with
`‖B_{kℓ}‖_∞ ≤ M`, `|∑_{kℓ} ⟪B_{kℓ} ∂_k u, ∂_ℓ v⟫| ≤ N² M ‖∇u‖₂ ‖∇v‖₂`. -/
theorem abs_sum_inner_mulL_le
    {B : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))} {M : ℝ}
    (hM : 0 ≤ M) (hB : ∀ k l, ‖B k l‖ ≤ M) (u v : SobolevEuclidean N 1 2 Ω) :
    |∑ k, ∑ l, ⟪mulL Ω (B k l) (weakDeriv u (MultiIndexLE.single k)),
      weakDeriv v (MultiIndexLE.single l)⟫_ℝ| ≤ N ^ 2 * M * gradNorm u * gradNorm v := by
  calc |∑ k, ∑ l, ⟪mulL Ω (B k l) (weakDeriv u (MultiIndexLE.single k)),
        weakDeriv v (MultiIndexLE.single l)⟫_ℝ|
      ≤ ∑ k, ∑ l, |⟪mulL Ω (B k l) (weakDeriv u (MultiIndexLE.single k)),
        weakDeriv v (MultiIndexLE.single l)⟫_ℝ| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun k _ ↦ Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _k : Fin N, ∑ _l : Fin N, M * gradNorm u * gradNorm v := by
        refine Finset.sum_le_sum fun k _ ↦ Finset.sum_le_sum fun l _ ↦ ?_
        refine (abs_real_inner_le_norm _ _).trans ?_
        calc ‖mulL Ω (B k l) (weakDeriv u (MultiIndexLE.single k))‖
              * ‖weakDeriv v (MultiIndexLE.single l)‖
            ≤ (‖B k l‖ * ‖weakDeriv u (MultiIndexLE.single k)‖)
              * ‖weakDeriv v (MultiIndexLE.single l)‖ := by
              gcongr; exact norm_mulL_apply_le Ω _ _
          _ ≤ (M * gradNorm u) * gradNorm v :=
              mul_le_mul (mul_le_mul (hB k l) (norm_weakDeriv_single_le_gradNorm u k)
                (norm_nonneg _) hM) (norm_weakDeriv_single_le_gradNorm v l) (norm_nonneg _)
                (mul_nonneg hM (gradNorm_nonneg u))
    _ = N ^ 2 * M * gradNorm u * gradNorm v := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end Coefficients

section Estimate

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))} {h : EuclideanSpace ℝ (Fin N)}

open SobolevMultiIndex

/-- The principal part of the general form (41), with the lower-order coefficients zero, as a
double sum of pairings. -/
theorem generalForm_zero_zero_apply
    (A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (u v : SobolevEuclidean N 1 2 Ω) :
    generalForm Ω A 0 0 u v = ∑ k, ∑ l, ⟪mulL Ω (A k l) (weakDeriv u (MultiIndexLE.single k)),
      weakDeriv v (MultiIndexLE.single l)⟫_ℝ := by
  rw [generalForm_apply_inner]
  simp [mulL_zero]

/-- **The equation tested with `D_{−h}(D_h u)`**, [brezis2011functional] §9.6, (63): the
principal part of the form evaluated at `u` and `D_{−h}(D_h u)` is
`∑_{kℓ} ⟪D_h (a_{kℓ} ∂_k u), D_h ∂_ℓ u⟫`, by the adjointness of the difference quotients. -/
theorem generalForm_apply_diffQuotL_diffQuotL
    (hΩ : IsTranslationInvariant (Ω : Set (EuclideanSpace ℝ (Fin N))) h)
    (A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (u : SobolevEuclidean N 1 2 Ω) :
    generalForm Ω A 0 0 u (diffQuotL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 volume
      hΩ.neg (diffQuotL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 volume hΩ u))
      = ∑ k, ∑ l, ⟪diffQuotLp ℝ 2 hΩ (mulL Ω (A k l) (weakDeriv u (MultiIndexLE.single k))),
        diffQuotLp ℝ 2 hΩ (weakDeriv u (MultiIndexLE.single l))⟫_ℝ := by
  rw [generalForm_zero_zero_apply]
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
  rw [weakDeriv_diffQuotL, weakDeriv_diffQuotL, inner_diffQuotLp hΩ]

/-- **The equation tested with `D_{−h}(D_h u)`, split by the product formula**: the principal
part of the form at `u` and `D_{−h}(D_h u)` is
`∑ ⟪(τ_h A) ∂_k D_h u, ∂_ℓ D_h u⟫ + ∑ ⟪(D_h A) ∂_k u, ∂_ℓ D_h u⟫` ([brezis2011functional] §9.6,
(63) and the identity before (65)). -/
theorem generalForm_apply_diffQuotL_diffQuotL_split
    (hΩ : IsTranslationInvariant (Ω : Set (EuclideanSpace ℝ (Fin N))) h)
    (A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (u : SobolevEuclidean N 1 2 Ω) :
    generalForm Ω A 0 0 u (diffQuotL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 volume
      hΩ.neg (diffQuotL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 volume hΩ u))
      = (∑ k, ∑ l, ⟪mulL Ω (Lp.translate ℝ ⊤ hΩ (A k l))
          (diffQuotLp ℝ 2 hΩ (weakDeriv u (MultiIndexLE.single k))),
          diffQuotLp ℝ 2 hΩ (weakDeriv u (MultiIndexLE.single l))⟫_ℝ)
        + ∑ k, ∑ l, ⟪mulL Ω (diffQuotLp ℝ ⊤ hΩ (A k l)) (weakDeriv u (MultiIndexLE.single k)),
          diffQuotLp ℝ 2 hΩ (weakDeriv u (MultiIndexLE.single l))⟫_ℝ := by
  rw [generalForm_apply_diffQuotL_diffQuotL, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [diffQuotLp_mulL, inner_add_left]

/-- The arithmetic of the tangential estimate: from `α G² ≤ S₁`, `|S₂| ≤ N² M G_u G`,
`S₁ + S₂ = L` and `L ≤ g G` follows `G ≤ α⁻¹ (g + N² M G_u)`. -/
theorem le_inv_mul_of_estimates {α M S₁ S₂ L G Gu g : ℝ} (hα : 0 < α) (hM : 0 ≤ M) (hG : 0 ≤ G)
    (hGu : 0 ≤ Gu) (hg : 0 ≤ g) (h1 : α * G ^ 2 ≤ S₁) (h2 : |S₂| ≤ N ^ 2 * M * Gu * G)
    (h3 : S₁ + S₂ = L) (h4 : L ≤ g * G) : G ≤ α⁻¹ * (g + N ^ 2 * M * Gu) := by
  have hkey : α * G ^ 2 ≤ (g + N ^ 2 * M * Gu) * G := by
    have := neg_abs_le S₂
    nlinarith
  rcases hG.eq_or_lt with hG0 | hG0
  · rw [← hG0]
    exact mul_nonneg (inv_nonneg.2 hα.le) (add_nonneg hg (mul_nonneg (mul_nonneg (by positivity) hM)
      hGu))
  · rw [le_inv_mul_iff₀ hα]
    exact le_of_mul_le_mul_right (by rw [sq, ← mul_assoc] at hkey; exact hkey) hG0

/-- Lemma 9.6 for the function of `D_h w`: `‖fn (D_h w)‖₂ ≤ ‖∇w‖₂`. -/
theorem norm_weakDeriv_zero_diffQuotL_le
    (hΩ : IsTranslationInvariant (Ω : Set (EuclideanSpace ℝ (Fin N))) h)
    (hseg : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin N))), ∀ t ∈ Icc (0 : ℝ) 1, x + t • h ∈ Ω)
    (w : SobolevEuclidean N 1 2 Ω) :
    ‖weakDeriv (diffQuotL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 volume hΩ w) 0‖
      ≤ gradNorm w :=
  norm_diffQuotLp_fnL_le hΩ hseg w

/-- The load tested with `D_{−h} v` is at most `‖g‖₂ ‖∇v‖₂` (Lemma 9.6). -/
theorem load_apply_diffQuotL_le
    (hΩ : IsTranslationInvariant (Ω : Set (EuclideanSpace ℝ (Fin N))) h)
    (hseg : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin N))), ∀ t ∈ Icc (0 : ℝ) 1, x + t • h ∈ Ω)
    (g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (v : SobolevEuclidean N 1 2 Ω) :
    load Ω g (diffQuotL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 volume hΩ v)
      ≤ ‖g‖ * gradNorm v := by
  refine (le_abs_self _).trans ((abs_load_le Ω g _).trans ?_)
  exact mul_le_mul_of_nonneg_left (norm_weakDeriv_zero_diffQuotL_le hΩ hseg v) (norm_nonneg g)

/-- The squared gradient norm of `D_h u` is `∑ᵢ ‖D_h ∂ᵢu‖₂²`. -/
theorem gradNorm_diffQuotL_sq
    (hΩ : IsTranslationInvariant (Ω : Set (EuclideanSpace ℝ (Fin N))) h)
    (u : SobolevEuclidean N 1 2 Ω) :
    gradNorm (diffQuotL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 volume hΩ u) ^ 2
      = ∑ i, ‖diffQuotLp ℝ 2 hΩ (weakDeriv u (MultiIndexLE.single i))‖ ^ 2 := by
  rw [← dirichletForm_self_eq_gradNorm_sq, dirichletForm_self_eq]
  simp only [weakDeriv_diffQuotL]

/-- **The tangential estimate (66)** of [brezis2011functional] §9.6, for a variable-coefficient
elliptic form on an open set invariant under the translation by `h` (and containing the segments
`[x, x − h]`, `x ∈ Ω`): if `u ∈ H^1(Ω)` satisfies `a(u, ψ) = ∫ g ψ` for `ψ = D_{−h}(D_h u)`,
where `a` is the principal part of the form (41) with coefficients `A_{kℓ} ∈ L^∞(Ω)` that are
elliptic after translation (`IsUniformlyElliptic Ω (τ_h A) α`) and have difference quotients
bounded in `L^∞(Ω)` by `M` (`‖D_h A_{kℓ}‖_∞ ≤ M`), then

`‖∇ D_h u‖₂ ≤ α⁻¹ (‖g‖₂ + N² M ‖∇u‖₂)`.

For the Laplacian (`A = δ`, `M = 0`, `α = 1`) this is the estimate (55) `‖∇ D_h u‖₂ ≤ ‖g‖₂` of
cases A and B. The proof is the book's: the left side of the tested equation is
`∑ ⟪(τ_h A) ∂_k D_h u, ∂_ℓ D_h u⟫ + ∑ ⟪(D_h A) ∂_k u, ∂_ℓ D_h u⟫`
(`Elliptic.generalForm_apply_diffQuotL_diffQuotL_split`), bounded below by
`α ‖∇ D_h u‖² − N² M ‖∇u‖ ‖∇ D_h u‖` (`Elliptic.sum_inner_mulL_ge`,
`Elliptic.abs_sum_inner_mulL_le`), and the right side is at most
`‖g‖ ‖D_{−h} D_h u‖₂ ≤ ‖g‖ ‖∇ D_h u‖₂` by Lemma 9.6 (`Elliptic.load_apply_diffQuotL_le`). -/
theorem gradNorm_diffQuotL_le
    (hΩ : IsTranslationInvariant (Ω : Set (EuclideanSpace ℝ (Fin N))) h)
    (hseg' : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin N))), ∀ t ∈ Icc (0 : ℝ) 1, x + t • (-h) ∈ Ω)
    {A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))} {α : ℝ}
    (hA : IsUniformlyElliptic Ω (fun k l ↦ Lp.translate ℝ ⊤ hΩ (A k l)) α) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ k l, ‖diffQuotLp ℝ ⊤ hΩ (A k l)‖ ≤ M)
    {u : SobolevEuclidean N 1 2 Ω}
    {g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : generalForm Ω A 0 0 u (diffQuotL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2
      volume hΩ.neg (diffQuotL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 volume hΩ u))
      = load Ω g (diffQuotL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 volume hΩ.neg
        (diffQuotL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 volume hΩ u))) :
    gradNorm (diffQuotL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 volume hΩ u)
      ≤ α⁻¹ * (‖g‖ + N ^ 2 * M * gradNorm u) := by
  have hell := sum_inner_mulL_ge Ω hA
    (diffQuotL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 volume hΩ u)
  simp only [weakDeriv_diffQuotL] at hell
  rw [← gradNorm_diffQuotL_sq hΩ u] at hell
  have hlow := abs_sum_inner_mulL_le hM0 hM u
    (diffQuotL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 volume hΩ u)
  simp only [weakDeriv_diffQuotL] at hlow
  exact le_inv_mul_of_estimates hA.1 hM0 (gradNorm_nonneg _) (gradNorm_nonneg _) (norm_nonneg _)
    hell hlow ((generalForm_apply_diffQuotL_diffQuotL_split hΩ A u).symm.trans heq)
    (load_apply_diffQuotL_le hΩ.neg hseg' g _)

end Estimate


/-! ### Second derivatives along an invariant direction -/

section SecondDeriv

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

open SobolevMultiIndex

/-- `D_h u ∈ K` for a submodule `K` of `W^{k,p}(Ω)` invariant under the translation by `h`. -/
theorem diffQuotL_mem {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [ProperSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {Ω : Opens E} {μ : Measure E} [μ.IsAddRightInvariant] {h : E}
    (hΩ : IsTranslationInvariant (Ω : Set E) h) {K : Submodule ℝ (SobolevMultiIndex F b k p Ω μ)}
    (hK : ∀ u ∈ K, translateL F b k p μ hΩ u ∈ K) {u : SobolevMultiIndex F b k p Ω μ}
    (hu : u ∈ K) : diffQuotL F b k p μ hΩ u ∈ K := by
  rw [diffQuotL_apply]
  exact K.smul_mem _ (K.sub_mem (hK u hu) hu)

/-- The segments `[x, x + s • (t • y)]`, `x ∈ Ω`, lie in an open set invariant under all the
translations along `y`. -/
theorem forall_add_smul_smul_mem {y : EuclideanSpace ℝ (Fin N)}
    (hΩ : ∀ t : ℝ, IsTranslationInvariant (Ω : Set (EuclideanSpace ℝ (Fin N))) (t • y)) (t : ℝ) :
    ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin N))), ∀ s ∈ Icc (0 : ℝ) 1, x + s • (t • y) ∈ Ω :=
  fun x hx s _ ↦ by rw [smul_smul]; exact (hΩ (s * t)).mem hx

/-- The segments `[x, x − s • (t • y)]`, `x ∈ Ω`, lie in an open set invariant under all the
translations along `y`. -/
theorem forall_add_smul_neg_smul_mem {y : EuclideanSpace ℝ (Fin N)}
    (hΩ : ∀ t : ℝ, IsTranslationInvariant (Ω : Set (EuclideanSpace ℝ (Fin N))) (t • y)) (t : ℝ) :
    ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin N))), ∀ s ∈ Icc (0 : ℝ) 1, x + s • (-(t • y)) ∈ Ω :=
  fun x hx s _ ↦ by rw [smul_neg, smul_smul, ← neg_smul]; exact (hΩ (-(s * t))).mem hx

/-- **The tangential estimate along an invariant direction**: for `Ω` invariant under all the
translations along `y`, a subspace `K` of `H^1(Ω)` invariant under those translations,
coefficients `A_{kℓ} ∈ L^∞(Ω)` with `C¹` representatives `a_{kℓ}` on `Ω` whose gradients are
bounded by `M`, elliptic with constant `α`, and `u ∈ K` solving `a(u, ψ) = ∫ g ψ` for all
`ψ ∈ K`: `‖∇ D_{t y} u‖₂ ≤ α⁻¹ (‖g‖₂ + N² M ‖∇u‖₂)` for every `t`. -/
theorem gradNorm_diffQuotL_le_of_invariant {y : EuclideanSpace ℝ (Fin N)}
    (hΩ : ∀ t : ℝ, IsTranslationInvariant (Ω : Set (EuclideanSpace ℝ (Fin N))) (t • y))
    {K : Submodule ℝ (SobolevEuclidean N 1 2 Ω)}
    (hK : ∀ ⦃h : EuclideanSpace ℝ (Fin N)⦄
      (hh : IsTranslationInvariant (Ω : Set (EuclideanSpace ℝ (Fin N))) h), ∀ u ∈ K,
        translateL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 volume hh u ∈ K)
    {A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    {a : Fin N → Fin N → EuclideanSpace ℝ (Fin N) → ℝ}
    (hAa : ∀ k l, ⇑(A k l) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] a k l)
    (ha : ∀ k l, ContDiffOn ℝ 1 (a k l) Ω) {M : ℝ} (hM0 : 0 ≤ M)
    (haM : ∀ k l, ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin N))), ‖fderiv ℝ (a k l) x‖ ≤ M)
    {α : ℝ} (hA : IsUniformlyElliptic Ω A α) {u : SobolevEuclidean N 1 2 Ω} (hu : u ∈ K)
    {g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ ψ ∈ K, generalForm Ω A 0 0 u ψ = load Ω g ψ) (t : ℝ) :
    gradNorm (diffQuotL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 volume (hΩ t) u)
      ≤ α⁻¹ * (‖g‖ + N ^ 2 * M * gradNorm u) := by
  refine gradNorm_diffQuotL_le (hΩ t) (forall_add_smul_neg_smul_mem hΩ t)
    (isUniformlyElliptic_translateLp (hΩ t) hA) hM0 (fun k l ↦ norm_diffQuotLp_top_le (hΩ t)
      (forall_add_smul_smul_mem hΩ t) (hAa k l) (ha k l) hM0 (haM k l)) ?_
  exact heq _ (diffQuotL_mem (hΩ t).neg (hK (hΩ t).neg) (diffQuotL_mem (hΩ t) (hK (hΩ t)) hu))

/-- **Second derivatives along an invariant direction** ([brezis2011functional] §9.6, (55)–(56)
and (66)–(67)): under the hypotheses of `Elliptic.gradNorm_diffQuotL_le_of_invariant`, with
`‖y‖ = 1`, every partial derivative `∂ᵢu` has a weak derivative along `y` in `L²(Ω)`, bounded by
`α⁻¹ (‖g‖₂ + N² M ‖∇u‖₂)`. The difference quotients `D_{t y} ∂ᵢu = ∂ᵢ D_{t y} u`, `t → 0`, are
bounded in `L²(Ω)` by the tangential estimate, and
`Elliptic.exists_hasWeakIteratedLineDerivOn_of_diffQuot_bounded` extracts the weak derivative. -/
theorem exists_hasWeakIteratedLineDerivOn_weakDeriv_of_invariant {y : EuclideanSpace ℝ (Fin N)}
    (hy : ‖y‖ = 1)
    (hΩ : ∀ t : ℝ, IsTranslationInvariant (Ω : Set (EuclideanSpace ℝ (Fin N))) (t • y))
    {K : Submodule ℝ (SobolevEuclidean N 1 2 Ω)}
    (hK : ∀ ⦃h : EuclideanSpace ℝ (Fin N)⦄
      (hh : IsTranslationInvariant (Ω : Set (EuclideanSpace ℝ (Fin N))) h), ∀ u ∈ K,
        translateL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 volume hh u ∈ K)
    {A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    {a : Fin N → Fin N → EuclideanSpace ℝ (Fin N) → ℝ}
    (hAa : ∀ k l, ⇑(A k l) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] a k l)
    (ha : ∀ k l, ContDiffOn ℝ 1 (a k l) Ω) {M : ℝ} (hM0 : 0 ≤ M)
    (haM : ∀ k l, ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin N))), ‖fderiv ℝ (a k l) x‖ ≤ M)
    {α : ℝ} (hA : IsUniformlyElliptic Ω A α) {u : SobolevEuclidean N 1 2 Ω} (hu : u ∈ K)
    {g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ ψ ∈ K, generalForm Ω A 0 0 u ψ = load Ω g ψ) (i : Fin N) :
    ∃ w : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      ‖w‖ ≤ α⁻¹ * (‖g‖ + N ^ 2 * M * gradNorm u) ∧
        HasWeakIteratedLineDerivOn ![y] (weakDeriv u (MultiIndexLE.single i)) w Ω volume := by
  obtain ⟨t, ht⟩ : ∃ t : ℕ → ℝ, t = fun n : ℕ ↦ 1 / ((n : ℝ) + 1) := ⟨_, rfl⟩
  have htpos : ∀ n, 0 < t n := fun n ↦ by rw [ht]; positivity
  have ht1 : ∀ n, t n ≤ 1 := fun n ↦ by
    rw [ht]
    exact div_le_one_of_le₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (by positivity)
  have ht0 : Tendsto t atTop (𝓝 0) := by
    rw [ht]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨v, hv⟩ : ∃ v : ℕ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      v = fun n ↦ diffQuotLp ℝ 2 (hΩ (t n)) (weakDeriv u (MultiIndexLE.single i)) := ⟨_, rfl⟩
  have hvle : ∀ n, ‖v n‖ ≤ α⁻¹ * (‖g‖ + N ^ 2 * M * gradNorm u) := fun n ↦ by
    rw [hv]
    refine le_trans ?_ (gradNorm_diffQuotL_le_of_invariant hΩ hK hAa ha hM0 haM hA hu heq (t n))
    exact norm_weakDeriv_single_le_gradNorm
      (diffQuotL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 volume (hΩ (t n)) u) i
  have hvae : ∀ n, ⇑(ContinuousLinearMap.id ℝ _ (v n))
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        diffQuot (t n • y) (weakDeriv u (MultiIndexLE.single i)) := fun n ↦ by
    rw [hv]
    exact coeFn_diffQuotLp (hΩ (t n)) _
  obtain ⟨w, hw, hwd⟩ := exists_hasWeakIteratedLineDerivOn_of_diffQuot_bounded
    (ContinuousLinearMap.id ℝ _)
    ((Lp.memLp (weakDeriv u (MultiIndexLE.single i))).locallyIntegrableOn
      one_le_two) hy hΩ htpos ht1 ht0 hvle hvae
  exact ⟨w, hw, hwd⟩

end SecondDeriv


/-! ### The Laplacian as the general form with the identity coefficients -/

section Kronecker

variable {N : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin N)))

open SobolevMultiIndex

/-- The identity matrix `δ_{kℓ}` as `L^∞(Ω)` coefficients, so that the principal part of the
general form (41) with these coefficients is the Dirichlet form `∫_Ω ∇u · ∇v`. -/
def kroneckerCoeff :
    Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  fun k l ↦ if k = l then (memLp_top_const (1 : ℝ)).toLp _ else 0

/-- The diagonal coefficients are `1`. -/
theorem kroneckerCoeff_diag (k : Fin N) :
    kroneckerCoeff Ω k k = (memLp_top_const (1 : ℝ)).toLp _ := by
  simp [kroneckerCoeff]

/-- The off-diagonal coefficients are `0`. -/
theorem kroneckerCoeff_of_ne {k l : Fin N} (hkl : k ≠ l) : kroneckerCoeff Ω k l = 0 := by
  simp [kroneckerCoeff, hkl]

/-- The coefficients `δ_{kℓ}` are the constant functions `if k = ℓ then 1 else 0`, almost
everywhere. -/
theorem coeFn_kroneckerCoeff (k l : Fin N) :
    ⇑(kroneckerCoeff Ω k l) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      fun _ ↦ if k = l then (1 : ℝ) else 0 := by
  by_cases hkl : k = l
  · subst hkl
    rw [kroneckerCoeff_diag]
    simpa using (memLp_top_const (1 : ℝ)).coeFn_toLp
  · rw [kroneckerCoeff_of_ne Ω hkl]
    refine (Lp.coeFn_zero ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).trans
      (Eventually.of_forall fun x ↦ ?_)
    simp [hkl]

/-- Multiplication by the diagonal coefficient `1` is the identity. -/
theorem mulL_kroneckerCoeff_diag (k : Fin N)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    mulL Ω (kroneckerCoeff Ω k k) f = f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_mulL Ω (kroneckerCoeff Ω k k) f, coeFn_kroneckerCoeff Ω k k] with x h1 h2
  rw [h1, h2]
  simp

/-- **The principal part of the general form with the identity coefficients is the Dirichlet
form** `∫_Ω ∇u · ∇v`. -/
theorem generalForm_kroneckerCoeff : generalForm Ω (kroneckerCoeff Ω) 0 0 = dirichletForm Ω := by
  ext u v
  rw [generalForm_zero_zero_apply, dirichletForm_apply_inner]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Finset.sum_eq_single k]
  · rw [mulL_kroneckerCoeff_diag]
  · intro l _ hlk
    rw [kroneckerCoeff_of_ne Ω (Ne.symm hlk), mulL_zero]
    simp
  · simp

/-- The identity coefficients are elliptic with constant `1`. -/
theorem isUniformlyElliptic_kroneckerCoeff : IsUniformlyElliptic Ω (kroneckerCoeff Ω) 1 := by
  refine ⟨one_pos, ?_⟩
  have h : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      ∀ k l, kroneckerCoeff Ω k l x = if k = l then (1 : ℝ) else 0 :=
    ae_all_iff.2 fun k ↦ ae_all_iff.2 fun l ↦ coeFn_kroneckerCoeff Ω k l
  filter_upwards [h] with x hx ξ
  simp only [hx, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    one_mul, EuclideanSpace.real_norm_sq_eq]
  exact le_of_eq (Finset.sum_congr rfl fun i _ ↦ by ring)

/-- The constant representatives of the identity coefficients are `C¹` with zero derivative. -/
theorem contDiffOn_kroneckerRep (k l : Fin N) :
    ContDiffOn ℝ 1 (fun _ : EuclideanSpace ℝ (Fin N) ↦ if k = l then (1 : ℝ) else 0) Ω :=
  contDiffOn_const

omit Ω in
theorem norm_fderiv_kroneckerRep_le (k l : Fin N) (x : EuclideanSpace ℝ (Fin N)) :
    ‖fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin N) ↦ if k = l then (1 : ℝ) else 0) x‖ ≤ 0 := by
  simp

end Kronecker

/-! ### Case A: the whole space -/

section WholeSpace

variable {N : ℕ}

open SobolevMultiIndex

/-- Every subspace of `H^1(Ω)` is invariant under a translation if it is `⊤`. -/
theorem translateL_mem_top {Ω : Opens (EuclideanSpace ℝ (Fin N))} {h : EuclideanSpace ℝ (Fin N)}
    (hh : IsTranslationInvariant (Ω : Set (EuclideanSpace ℝ (Fin N))) h)
    (u : SobolevEuclidean N 1 2 Ω) (_ : u ∈ (⊤ : Submodule ℝ (SobolevEuclidean N 1 2 Ω))) :
    translateL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 volume hh u ∈
      (⊤ : Submodule ℝ (SobolevEuclidean N 1 2 Ω)) :=
  trivial

/-- **`H²` regularity on an open set invariant under all translations, with bounds**: if `Ω` is
invariant under every translation along the coordinate directions (the whole space), `u ∈ H^1(Ω)`
and `∫_Ω ∇u · ∇φ = ∫_Ω g φ` for all `φ ∈ H^1(Ω)`, then `u` is the function of an element
`U ∈ H²(Ω)` with `‖∂_j ∂_k U‖₂ ≤ ‖g‖₂` for all `j, k` and
`‖U‖_{H²} ≤ √(#{|α| ≤ 2}) (‖u‖_{H¹} + ‖g‖₂)`.
This is [brezis2011functional] Theorem 9.25, case A, for the Dirichlet form, on any such `Ω`. -/
theorem exists_sobolevEuclidean_two_of_forall_invariant {Ω : Opens (EuclideanSpace ℝ (Fin N))}
    (hΩ : ∀ (i : Fin N) (t : ℝ),
      IsTranslationInvariant (Ω : Set (EuclideanSpace ℝ (Fin N))) (t • EuclideanSpace.single i 1))
    {u : SobolevEuclidean N 1 2 Ω}
    {g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ, dirichletForm Ω u φ = load Ω g φ) :
    ∃ U : SobolevEuclidean N 2 2 Ω,
      fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn u ∧
      (∀ α : MultiIndexLE (Fin N) 2, ∑ i, α.1 i = 2 → ‖weakDeriv U α‖ ≤ ‖g‖) ∧
      ‖U‖ ≤ √(Fintype.card (MultiIndexLE (Fin N) 2)) * (‖u‖ + ‖g‖) := by
  have heq' : ∀ ψ ∈ (⊤ : Submodule ℝ (SobolevEuclidean N 1 2 Ω)),
      generalForm Ω (kroneckerCoeff Ω) 0 0 u ψ = load Ω g ψ := fun ψ _ ↦ by
    rw [generalForm_kroneckerCoeff]
    exact heq ψ
  have hsecond : ∀ i j, ∃ w : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      ‖w‖ ≤ ‖g‖ ∧ HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1]
        (weakDeriv u (MultiIndexLE.single j)) w Ω volume := fun i j ↦ by
    obtain ⟨w, hw, hwd⟩ := exists_hasWeakIteratedLineDerivOn_weakDeriv_of_invariant
      (y := EuclideanSpace.single i 1) (by simp) (hΩ i) (K := ⊤) (fun h hh u _ ↦ trivial)
      (coeFn_kroneckerCoeff Ω) (contDiffOn_kroneckerRep Ω) (M := 0) le_rfl
      (fun k l x _ ↦ norm_fderiv_kroneckerRep_le k l x) (isUniformlyElliptic_kroneckerCoeff Ω)
      (u := u) trivial heq' j
    refine ⟨w, ?_, hwd⟩
    simpa using hw
  obtain ⟨U, hU, hU2, hU1⟩ := exists_two_of_forall_exists u (fun i j ↦ by
    obtain ⟨w, hw, hwd⟩ := hsecond i j
    exact ⟨w, hw, by simpa [EuclideanSpace.basisFun_toBasis_apply] using hwd⟩)
  refine ⟨U, hU, hU2, norm_le_sqrt_card_mul_of_forall_norm_weakDeriv_le U fun α ↦ ?_⟩
  rcases Nat.lt_or_ge (∑ i, α.1 i) 2 with hlt | hge
  · exact (hU1 α (Nat.lt_succ_iff.1 hlt)).trans (le_add_of_nonneg_right (norm_nonneg _))
  · exact (hU2 α (le_antisymm α.2 hge)).trans (le_add_of_nonneg_left (norm_nonneg _))

/-- **Theorem 9.25, case A (`Ω = ℝ^N`), `H²` regularity, with the book's constants**
([brezis2011functional] §9.6, case A): let `u ∈ H^1(ℝ^N)`, `g ∈ L²(ℝ^N)`, and
`∫ ∇u · ∇φ = ∫ g φ` for every `φ ∈ H^1(ℝ^N)`. Then `u` is the function of an element
`U ∈ H²(ℝ^N)`, with `‖∂_j ∂_k U‖₂ ≤ ‖g‖₂` for all `j, k` and
`‖U‖_{H²} ≤ √(#{|α| ≤ 2}) (‖u‖_{H¹} + ‖g‖₂)`. The book's equation `−Δu + u = f` is the case
`g = f − u`, and its `‖u‖_{H¹} ≤ ‖f‖₂` gives `‖U‖_{H²} ≤ C ‖f‖₂`.

The proof is the method of translations: testing with `D_{−h}(D_h u)` and Lemma 9.6 give
`‖∇ D_h u‖₂ ≤ ‖g‖₂` (`Elliptic.gradNorm_diffQuotL_le`), and the weak compactness of bounded
difference quotients (`Elliptic.exists_hasWeakIteratedLineDerivOn_of_diffQuot_bounded`) produces
every second derivative with the same bound. The whole space is invariant under every
translation, so every direction is available
(`Elliptic.exists_sobolevEuclidean_two_of_forall_invariant`). -/
theorem regularity_top {u : SobolevEuclidean N 1 2 ⊤}
    {g : Lp ℝ 2 (volume.restrict
      ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ, dirichletForm (⊤ : Opens (EuclideanSpace ℝ (Fin N))) u φ
      = load (⊤ : Opens (EuclideanSpace ℝ (Fin N))) g φ) :
    ∃ U : SobolevEuclidean N 2 2 ⊤,
      fn U =ᵐ[volume.restrict
        ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) : Set (EuclideanSpace ℝ (Fin N)))] fn u ∧
      (∀ α : MultiIndexLE (Fin N) 2, ∑ i, α.1 i = 2 → ‖weakDeriv U α‖ ≤ ‖g‖) ∧
      ‖U‖ ≤ √(Fintype.card (MultiIndexLE (Fin N) 2)) * (‖u‖ + ‖g‖) :=
  exists_sobolevEuclidean_two_of_forall_invariant (fun _ _ ↦ IsTranslationInvariant.univ _) heq

/-- **Theorem 9.25, case A, as a membership**: the function of the weak solution lies in
`H²(ℝ^N)` (`MemSobolevMultiIndex` for the standard basis). -/
theorem regularity_top_memSobolevMultiIndex {u : SobolevEuclidean N 1 2 ⊤}
    {g : Lp ℝ 2 (volume.restrict
      ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ, dirichletForm (⊤ : Opens (EuclideanSpace ℝ (Fin N))) u φ
      = load (⊤ : Opens (EuclideanSpace ℝ (Fin N))) g φ) :
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (fn u) 2 2 ⊤ volume := by
  obtain ⟨U, hU, -, -⟩ := regularity_top heq
  exact (memSobolevMultiIndex U).congr_ae hU


end WholeSpace


/-! ### Cutting off a weak solution -/

section Cutoff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}

omit [MeasurableSpace E] [BorelSpace E] in
/-- A smooth function `α` whose support misses the frontier of `Ω`, times a smooth compactly
supported `φ`, agrees on `Ω` with a test function on `Ω`:
`IsSobolevCutoff.exists_testFunction_mul_eqOn` without the bound on `α` and its derivative, which
that proof does not use. -/
theorem exists_testFunction_mul_eqOn_of_disjoint_frontier {α : E → ℝ} (hα : ContDiff ℝ ∞ α)
    (hαΩ : Disjoint (tsupport α) (frontier (Ω : Set E))) {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) :
    ∃ ψ : 𝓓(Ω, ℝ), ∀ x ∈ (Ω : Set E), ψ x = α x * φ x := by
  have hsub : tsupport α ∩ closure (Ω : Set E) ⊆ Ω := by
    rintro x ⟨hxα, hxc⟩
    by_contra hxΩ
    exact hαΩ.notMem_of_mem_left hxα ⟨hxc, fun h ↦ hxΩ (Ω.isOpen.interior_eq ▸ h)⟩
  obtain ⟨K, hK⟩ : ∃ K : Set E, K = tsupport (fun x ↦ α x * φ x) ∩ closure (Ω : Set E) := ⟨_, rfl⟩
  have hKc : IsCompact K := by
    rw [hK]
    exact (hφc.mul_left.of_isClosed_subset isClosed_closure le_rfl).inter_right isClosed_closure
  have hKΩ : K ⊆ Ω := fun x hx ↦ by
    rw [hK] at hx
    exact hsub ⟨tsupport_mul_subset_left hx.1, hx.2⟩
  obtain ⟨χ, hχ, hχ1, hχΩ, -⟩ := hKc.exists_contDiff_eqOn_one Ω.isOpen hKΩ
  refine ⟨⟨fun x ↦ χ x * (α x * φ x), hχ.mul (hα.mul hφ), hφc.mul_left.mul_left,
    tsupport_mul_subset_left.trans hχΩ⟩, fun x hx ↦ ?_⟩
  change χ x * (α x * φ x) = α x * φ x
  by_cases hxK : x ∈ K
  · rw [hχ1 hxK, Pi.one_apply, one_mul]
  · have : α x * φ x = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun x ↦ α x * φ x) fun h ↦
        hxK (hK ▸ ⟨h, subset_closure hx⟩)
    rw [this, mul_zero]

omit [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
/-- The defining identity of a weak derivative along one direction, for a function `χ` agreeing
on `Ω` with a test function: `∫_Ω (∂_y χ) u = −∫_Ω χ w`. -/
theorem _root_.HasWeakIteratedLineDerivOn.integral_fderiv_mul_eq_of_eqOn {y : E} {u w : E → ℝ}
    (hu : HasWeakIteratedLineDerivOn ![y] u w Ω μ) {χ : E → ℝ} (ψ : 𝓓(Ω, ℝ))
    (hχ : ∀ x ∈ (Ω : Set E), ψ x = χ x) :
    ∫ x in (Ω : Set E), fderiv ℝ χ x y * u x ∂μ = -∫ x in (Ω : Set E), χ x * w x ∂μ := by
  have key := hu.integral_smul_eq ψ
  simp only [iteratedFDeriv_one_apply, Matrix.cons_val_zero, pow_one, smul_eq_mul,
    neg_one_mul] at key
  have e1 : ∫ x in (Ω : Set E), fderiv ℝ χ x y * u x ∂μ
      = ∫ x in (Ω : Set E), fderiv ℝ ψ x y * u x ∂μ := by
    refine setIntegral_congr_fun Ω.isOpen.measurableSet fun x hx ↦ ?_
    have : (ψ : E → ℝ) =ᶠ[𝓝 x] χ := Filter.eventually_of_mem (Ω.isOpen.mem_nhds hx) hχ
    rw [this.fderiv_eq]
  have e2 : ∫ x in (Ω : Set E), χ x * w x ∂μ = ∫ x in (Ω : Set E), ψ x * w x ∂μ :=
    setIntegral_congr_fun Ω.isOpen.measurableSet fun x hx ↦ by rw [hχ x hx]
  rw [e1, e2, key]

omit [μ.IsAddHaarMeasure] in
/-- **Cutting off a weak solution of `−div(∇u) = f`** ([brezis2011functional] §9.6, proof of
Theorem 9.25, case C₁, "it is easy to verify that `θ₀ u` is a weak solution in `ℝ^N` of
`−Δ(θ₀u) + θ₀u = θ₀f − 2∇θ₀·∇u − (Δθ₀)u`"): let `u` have the weak partial derivatives `w i` along
the vectors `b i` on `Ω`, all locally integrable, let `f` be locally integrable on `Ω`, and let
`∑ᵢ ∫_Ω wᵢ ∂ᵢφ = ∫_Ω f φ` for every test function `φ` on `Ω`. For a cut-off `θ` of `Ω` and every
test function `ψ` on the whole space,

`∑ᵢ ∫ 1_Ω (θ wᵢ + (∂ᵢθ) u) ∂ᵢψ = ∫ 1_Ω (θ f − 2 ∑ᵢ (∂ᵢθ) wᵢ − (∑ᵢ ∂ᵢ∂ᵢθ) u) ψ`,

with `∂ᵢθ = ∇θ · bᵢ`. The equation is tested with `θψ`, and the weak derivatives with
`(∂ᵢθ) ψ`, both of which agree on `Ω` with test functions on `Ω`. -/
theorem sum_integral_indicator_cutoff_eq {ι : Type*} [Fintype ι] (b : ι → E) {u f : E → ℝ}
    {w : ι → E → ℝ} (hu : LocallyIntegrableOn u Ω μ) (hf : LocallyIntegrableOn f Ω μ)
    (hw : ∀ i, HasWeakIteratedLineDerivOn ![b i] u (w i) Ω μ)
    (heq : ∀ φ : 𝓓(Ω, ℝ), ∫ x in (Ω : Set E), ∑ i, w i x * fderiv ℝ φ x (b i) ∂μ
      = ∫ x in (Ω : Set E), f x * φ x ∂μ)
    {θ : E → ℝ} (hθ : IsSobolevCutoff Ω θ) (ψ : 𝓓((⊤ : Opens E), ℝ)) :
    ∑ i, ∫ x, (Ω : Set E).indicator (fun x ↦ θ x * w i x + fderiv ℝ θ x (b i) * u x) x
        * fderiv ℝ ψ x (b i) ∂μ
      = ∫ x, (Ω : Set E).indicator (fun x ↦ θ x * f x - 2 * ∑ i, fderiv ℝ θ x (b i) * w i x
          - (∑ i, fderiv ℝ (fun z ↦ fderiv ℝ θ z (b i)) x (b i)) * u x) x * ψ x ∂μ := by
  have hΩm : MeasurableSet (Ω : Set E) := Ω.isOpen.measurableSet
  have hwl : ∀ i, LocallyIntegrableOn (w i) Ω μ := fun i ↦ (hw i).locallyIntegrableOn_weakDeriv
  have hθc : ContDiff ℝ ∞ θ := hθ.contDiff
  have hψc : ContDiff ℝ ∞ (ψ : E → ℝ) := ψ.contDiff
  have hψs : HasCompactSupport (ψ : E → ℝ) := ψ.hasCompactSupport
  have hdθ : ∀ i, ContDiff ℝ ∞ fun x ↦ fderiv ℝ θ x (b i) := fun i ↦ hθ.contDiff_fderiv_apply _
  have hdψ : ∀ i, ContDiff ℝ ∞ fun x ↦ fderiv ℝ ψ x (b i) := fun i ↦
    (hψc.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
  have hddθ : ∀ i, ContDiff ℝ ∞ fun x ↦ fderiv ℝ (fun z ↦ fderiv ℝ θ z (b i)) x (b i) := fun i ↦
    contDiff_fderiv_fderiv_apply hθc _
  have hsθ : ∀ i, tsupport (fun x ↦ fderiv ℝ θ x (b i)) ⊆ tsupport θ := fun i ↦
    tsupport_fderiv_apply_subset ℝ (b i)
  have hssθ : ∀ i, tsupport (fun x ↦ fderiv ℝ (fun z ↦ fderiv ℝ θ z (b i)) x (b i))
      ⊆ tsupport θ := fun i ↦ (tsupport_fderiv_apply_subset ℝ (b i)).trans (hsθ i)
  -- the test functions on `Ω` agreeing with `θ ψ` and with `(∂ᵢθ) ψ`
  obtain ⟨χ, hχ⟩ :=
    exists_testFunction_mul_eqOn_of_disjoint_frontier hθc hθ.disjoint_frontier hψc hψs
  have hχi : ∀ i, ∃ χ' : 𝓓(Ω, ℝ), ∀ x ∈ (Ω : Set E), χ' x = fderiv ℝ θ x (b i) * ψ x := fun i ↦
    exists_testFunction_mul_eqOn_of_disjoint_frontier (hdθ i)
      (Disjoint.mono_left (hsθ i) hθ.disjoint_frontier) hψc hψs
  choose χ' hχ' using hχi
  -- integrability of the pieces
  have I : ∀ (v : E → ℝ), LocallyIntegrableOn v Ω μ → ∀ (g : E → ℝ), Continuous g →
      HasCompactSupport g → tsupport g ⊆ tsupport θ → IntegrableOn (fun x ↦ g x * v x) Ω μ :=
    fun v hv g hg hgc hgθ ↦ hθ.integrableOn_mul_of_locallyIntegrableOn hv hg hgc hgθ
  have hθψ : HasCompactSupport fun x ↦ θ x * ψ x := hψs.mul_left
  -- the identity for one direction
  have key : ∀ i, ∫ x in (Ω : Set E), (θ x * w i x + fderiv ℝ θ x (b i) * u x)
        * fderiv ℝ ψ x (b i) ∂μ
      = ∫ x in (Ω : Set E), w i x * fderiv ℝ χ x (b i) ∂μ
        - 2 * ∫ x in (Ω : Set E), fderiv ℝ θ x (b i) * w i x * ψ x ∂μ
        - ∫ x in (Ω : Set E), fderiv ℝ (fun z ↦ fderiv ℝ θ z (b i)) x (b i) * u x * ψ x ∂μ := by
    intro i
    -- `∂ᵢ(θψ) = (∂ᵢθ) ψ + θ ∂ᵢψ` and `∂ᵢ((∂ᵢθ) ψ) = (∂ᵢ∂ᵢθ) ψ + (∂ᵢθ) ∂ᵢψ`
    have hd1 : ∀ x, fderiv ℝ (fun z ↦ θ z * ψ z) x (b i)
        = fderiv ℝ θ x (b i) * ψ x + θ x * fderiv ℝ ψ x (b i) := fun x ↦ by
      rw [fderiv_fun_mul (hθc.differentiable (by simp) x) (hψc.differentiable (by simp) x)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      ring
    have hd2 : ∀ x, fderiv ℝ (fun z ↦ fderiv ℝ θ z (b i) * ψ z) x (b i)
        = fderiv ℝ (fun z ↦ fderiv ℝ θ z (b i)) x (b i) * ψ x
          + fderiv ℝ θ x (b i) * fderiv ℝ ψ x (b i) := fun x ↦ by
      rw [fderiv_fun_mul ((hdθ i).differentiable (by simp) x) (hψc.differentiable (by simp) x)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      ring
    -- the two integrations by parts
    have hA : ∫ x in (Ω : Set E), fderiv ℝ (fun z ↦ θ z * ψ z) x (b i) * w i x ∂μ
        = ∫ x in (Ω : Set E), fderiv ℝ χ x (b i) * w i x ∂μ := by
      refine setIntegral_congr_fun hΩm fun x hx ↦ ?_
      have : (χ : E → ℝ) =ᶠ[𝓝 x] fun z ↦ θ z * ψ z :=
        Filter.eventually_of_mem (Ω.isOpen.mem_nhds hx) hχ
      rw [this.fderiv_eq]
    have hB := (hw i).integral_fderiv_mul_eq_of_eqOn (χ' i) (hχ' i)
    -- integrability
    have I1 := I (w i) (hwl i) (fun x ↦ fderiv ℝ θ x (b i) * ψ x)
      ((hdθ i).continuous.mul ψ.continuous) hψs.mul_left (tsupport_mul_subset_left.trans (hsθ i))
    have I2 := I (w i) (hwl i) (fun x ↦ θ x * fderiv ℝ ψ x (b i))
      (hθc.continuous.mul (hdψ i).continuous) (hψs.fderiv_apply ℝ (b i)).mul_left
      tsupport_mul_subset_left
    have I3 := I u hu (fun x ↦ fderiv ℝ (fun z ↦ fderiv ℝ θ z (b i)) x (b i) * ψ x)
      ((hddθ i).continuous.mul ψ.continuous) hψs.mul_left
      (tsupport_mul_subset_left.trans (hssθ i))
    have I4 := I u hu (fun x ↦ fderiv ℝ θ x (b i) * fderiv ℝ ψ x (b i))
      ((hdθ i).continuous.mul (hdψ i).continuous) (hψs.fderiv_apply ℝ (b i)).mul_left
      (tsupport_mul_subset_left.trans (hsθ i))
    have e1 : ∫ x in (Ω : Set E), (θ x * w i x + fderiv ℝ θ x (b i) * u x)
          * fderiv ℝ ψ x (b i) ∂μ
        = (∫ x in (Ω : Set E), θ x * fderiv ℝ ψ x (b i) * w i x ∂μ)
          + ∫ x in (Ω : Set E), fderiv ℝ θ x (b i) * fderiv ℝ ψ x (b i) * u x ∂μ := by
      rw [← integral_add I2 I4]
      exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
    have e2 : ∫ x in (Ω : Set E), θ x * fderiv ℝ ψ x (b i) * w i x ∂μ
        = (∫ x in (Ω : Set E), fderiv ℝ (fun z ↦ θ z * ψ z) x (b i) * w i x ∂μ)
          - ∫ x in (Ω : Set E), fderiv ℝ θ x (b i) * ψ x * w i x ∂μ := by
      simp_rw [hd1]
      rw [← integral_sub ((I1.add I2).congr_fun (fun x _ ↦ by simp only [Pi.add_apply]; ring) hΩm)
        I1]
      exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
    have e3 : ∫ x in (Ω : Set E), fderiv ℝ θ x (b i) * fderiv ℝ ψ x (b i) * u x ∂μ
        = (∫ x in (Ω : Set E), fderiv ℝ (fun z ↦ fderiv ℝ θ z (b i) * ψ z) x (b i) * u x ∂μ)
          - ∫ x in (Ω : Set E), fderiv ℝ (fun z ↦ fderiv ℝ θ z (b i)) x (b i) * ψ x * u x ∂μ := by
      simp_rw [hd2]
      rw [← integral_sub ((I3.add I4).congr_fun (fun x _ ↦ by simp only [Pi.add_apply]; ring) hΩm)
        I3]
      exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
    rw [e1, e2, e3, hA, hB]
    have e4 : ∫ x in (Ω : Set E), fderiv ℝ χ x (b i) * w i x ∂μ
        = ∫ x in (Ω : Set E), w i x * fderiv ℝ χ x (b i) ∂μ :=
      integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
    have e5 : ∫ x in (Ω : Set E), fderiv ℝ θ x (b i) * ψ x * w i x ∂μ
        = ∫ x in (Ω : Set E), fderiv ℝ θ x (b i) * w i x * ψ x ∂μ :=
      integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
    have e7 : ∫ x in (Ω : Set E), fderiv ℝ (fun z ↦ fderiv ℝ θ z (b i)) x (b i) * ψ x * u x ∂μ
        = ∫ x in (Ω : Set E), fderiv ℝ (fun z ↦ fderiv ℝ θ z (b i)) x (b i) * u x * ψ x ∂μ :=
      integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
    rw [e4, e5, e7]
    ring
  -- sum over the directions, use the equation, and pass to the indicator integrals
  have hL : ∀ i, ∫ x, (Ω : Set E).indicator (fun x ↦ θ x * w i x + fderiv ℝ θ x (b i) * u x) x
        * fderiv ℝ ψ x (b i) ∂μ
      = ∫ x in (Ω : Set E), (θ x * w i x + fderiv ℝ θ x (b i) * u x)
        * fderiv ℝ ψ x (b i) ∂μ := fun i ↦ by
    rw [← integral_indicator hΩm]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [Set.indicator_mul_left])
  have hR : ∫ x, (Ω : Set E).indicator (fun x ↦ θ x * f x - 2 * ∑ i, fderiv ℝ θ x (b i) * w i x
        - (∑ i, fderiv ℝ (fun z ↦ fderiv ℝ θ z (b i)) x (b i)) * u x) x * ψ x ∂μ
      = ∫ x in (Ω : Set E), (θ x * f x - 2 * ∑ i, fderiv ℝ θ x (b i) * w i x
        - (∑ i, fderiv ℝ (fun z ↦ fderiv ℝ θ z (b i)) x (b i)) * u x) * ψ x ∂μ := by
    rw [← integral_indicator hΩm]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [Set.indicator_mul_left])
  simp_rw [hL, key]
  rw [hR, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have IB : ∀ i, IntegrableOn (fun x ↦ fderiv ℝ θ x (b i) * w i x * ψ x) Ω μ := fun i ↦
    (I (w i) (hwl i) (fun x ↦ fderiv ℝ θ x (b i) * ψ x) ((hdθ i).continuous.mul ψ.continuous)
      hψs.mul_left (tsupport_mul_subset_left.trans (hsθ i))).congr_fun (fun x _ ↦ by ring) hΩm
  have IC : ∀ i, IntegrableOn
      (fun x ↦ fderiv ℝ (fun z ↦ fderiv ℝ θ z (b i)) x (b i) * u x * ψ x) Ω μ := fun i ↦
    (I u hu (fun x ↦ fderiv ℝ (fun z ↦ fderiv ℝ θ z (b i)) x (b i) * ψ x)
      ((hddθ i).continuous.mul ψ.continuous) hψs.mul_left
      (tsupport_mul_subset_left.trans (hssθ i))).congr_fun (fun x _ ↦ by ring) hΩm
  have IF : IntegrableOn (fun x ↦ θ x * f x * ψ x) Ω μ :=
    (I f hf (fun x ↦ θ x * ψ x) (hθc.continuous.mul ψ.continuous) hθψ
      tsupport_mul_subset_left).congr_fun (fun x _ ↦ by ring) hΩm
  -- the sum of the first terms is the equation tested with `χ`
  have hA : ∑ i, ∫ x in (Ω : Set E), w i x * fderiv ℝ χ x (b i) ∂μ
      = ∫ x in (Ω : Set E), θ x * f x * ψ x ∂μ := by
    rw [← integral_finsetSum _ fun i _ ↦ ((hw i).integrable_smul_weakDeriv
      (χ.fderivApply (b i))).integrableOn.congr_fun
        (fun x _ ↦ by simp [TestFunction.fderivApply_apply, mul_comm]) hΩm, heq χ]
    exact setIntegral_congr_fun hΩm fun x hx ↦ by rw [hχ x hx]; ring
  -- the right side splits into its three pieces
  have hR' : ∫ x in (Ω : Set E), (θ x * f x - 2 * ∑ i, fderiv ℝ θ x (b i) * w i x
        - (∑ i, fderiv ℝ (fun z ↦ fderiv ℝ θ z (b i)) x (b i)) * u x) * ψ x ∂μ
      = (∫ x in (Ω : Set E), θ x * f x * ψ x ∂μ)
        - 2 * ∑ i, ∫ x in (Ω : Set E), fderiv ℝ θ x (b i) * w i x * ψ x ∂μ
        - ∑ i, ∫ x in (Ω : Set E),
            fderiv ℝ (fun z ↦ fderiv ℝ θ z (b i)) x (b i) * u x * ψ x ∂μ := by
    have hB2 : IntegrableOn (fun x ↦ 2 * ∑ i, fderiv ℝ θ x (b i) * w i x * ψ x) Ω μ :=
      (integrable_finsetSum _ fun i _ ↦ IB i).const_mul 2
    have hCs : IntegrableOn
        (fun x ↦ ∑ i, fderiv ℝ (fun z ↦ fderiv ℝ θ z (b i)) x (b i) * u x * ψ x) Ω μ :=
      integrable_finsetSum _ fun i _ ↦ IC i
    have h12 : IntegrableOn
        (fun x ↦ θ x * f x * ψ x - 2 * ∑ i, fderiv ℝ θ x (b i) * w i x * ψ x) Ω μ :=
      IF.sub hB2
    rw [← integral_finsetSum _ fun i _ ↦ IB i, ← integral_finsetSum _ fun i _ ↦ IC i,
      ← integral_const_mul, ← integral_sub IF hB2, ← integral_sub h12 hCs]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only [sub_mul, Finset.sum_mul, mul_assoc]
  rw [hA, hR']

end Cutoff


/-! ### Weak solutions: the typed and the predicate forms -/

section Bridge

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

open SobolevMultiIndex

/-- **A weak solution against the test functions is one against `H^1_0(Ω)`**: if
`∫_Ω ∇V · ∇φ = ∫_Ω G φ` for every element `φ` of `H^1(Ω)` whose function is a test function, then
it holds for every `φ ∈ H^1_0(Ω)`, both sides being continuous in `φ`. On `Ω = ℝ^N`, where
`H^1_0 = H^1` (`SobolevEuclideanZero.eq_top`), this is the density argument "this implies (53),
since `C_c^∞(ℝ^N)` is dense in `H^1(ℝ^N)`" of [brezis2011functional] §9.6. -/
theorem dirichletForm_eq_load_of_forall_testFunctions {V : SobolevEuclidean N 1 2 Ω}
    {G : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (h : ∀ φ ∈ testFunctions ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume,
      dirichletForm Ω V φ = load Ω G φ)
    {φ : SobolevEuclidean N 1 2 Ω} (hφ : φ ∈ SobolevEuclideanZero N 1 2 Ω) :
    dirichletForm Ω V φ = load Ω G φ := by
  have hker : testFunctions ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
      ≤ LinearMap.ker ((dirichletForm Ω V - load Ω G : SobolevEuclidean N 1 2 Ω →L[ℝ] ℝ) :
        SobolevEuclidean N 1 2 Ω →ₗ[ℝ] ℝ) := fun ψ hψ ↦ by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, sub_apply, h ψ hψ,
      sub_self]
  have hclosed := Submodule.topologicalClosure_minimal _ hker
    (ContinuousLinearMap.isClosed_ker (dirichletForm Ω V - load Ω G))
  have := hclosed hφ
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, sub_apply,
    sub_eq_zero] at this
  exact this

/-- **The Dirichlet form of an element against a test-function element, in terms of
functions**: if the partial derivatives of `V` are the functions `wv i` and the function of `Φ`
is the test function `ψ`, then `∫_Ω ∇V · ∇Φ = ∑ᵢ ∫_Ω wvᵢ ∂ᵢψ`. -/
theorem dirichletForm_apply_eq_of_ae_eq {V : SobolevEuclidean N 1 2 Ω}
    {wv : Fin N → EuclideanSpace ℝ (Fin N) → ℝ}
    (hV : ∀ i, ⇑(weakDeriv V (MultiIndexLE.single i))
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] wv i)
    {Φ : SobolevEuclidean N 1 2 Ω} {ψ : 𝓓(Ω, ℝ)}
    (hΦ : fn Φ =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ψ) :
    dirichletForm Ω V Φ = ∑ i, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      wv i x * fderiv ℝ ψ x (EuclideanSpace.single i 1) := by
  rw [dirichletForm_apply_inner]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [L2.inner_eq_integral_mul]
  have hΦi := weakDeriv_single_ae_eq_fderiv_of_contDiffOn Ω
    (ψ.contDiff.contDiffOn.of_le (by simp)) hΦ i
  refine integral_congr_ae ?_
  filter_upwards [hV i, hΦi] with x h1 h2
  rw [h1, h2]

/-- The load of `G` against a test-function element, in terms of functions. -/
theorem load_apply_eq_of_ae_eq {G : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    {g : EuclideanSpace ℝ (Fin N) → ℝ}
    (hG : ⇑G =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] g)
    {Φ : SobolevEuclidean N 1 2 Ω} {ψ : 𝓓(Ω, ℝ)}
    (hΦ : fn Φ =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ψ) :
    load Ω G Φ = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), g x * ψ x := by
  rw [load_apply]
  refine integral_congr_ae ?_
  filter_upwards [hG, hΦ] with x h1 h2
  rw [h1, h2]

/-- **From the predicate form to the typed form of a weak solution**: functions `v`, `wv i`, `g`
in `L²(Ω)` with `wv i` the weak derivative of `v` along `eᵢ` and
`∑ᵢ ∫_Ω wvᵢ ∂ᵢψ = ∫_Ω g ψ` for every test function `ψ` on `Ω` are the function, the partial
derivatives and the load of elements `V ∈ H^1(Ω)`, `G ∈ L²(Ω)` with `∫_Ω ∇V · ∇Φ = ∫_Ω G Φ` for
every test-function element `Φ`. -/
theorem exists_sobolevEuclidean_of_forall_testFunction {v g : EuclideanSpace ℝ (Fin N) → ℝ}
    {wv : Fin N → EuclideanSpace ℝ (Fin N) → ℝ}
    (hv : MemLp v 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (hwv : ∀ i, HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1] v (wv i) Ω volume)
    (hwvp : ∀ i, MemLp (wv i) 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (hg : MemLp g 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (heq : ∀ ψ : 𝓓(Ω, ℝ), ∑ i, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      wv i x * fderiv ℝ ψ x (EuclideanSpace.single i 1)
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), g x * ψ x) :
    ∃ (V : SobolevEuclidean N 1 2 Ω)
      (G : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))),
      fn V =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] v ∧
      (∀ i, ⇑(weakDeriv V (MultiIndexLE.single i))
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] wv i) ∧
      ⇑G =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] g ∧
      ∀ Φ ∈ testFunctions ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume,
        dirichletForm Ω V Φ = load Ω G Φ := by
  have hmem : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis v 1 2 Ω volume :=
    memSobolevMultiIndex_one_iff.2 ⟨hv, fun i ↦ ⟨wv i, by
      simpa [EuclideanSpace.basisFun_toBasis_apply] using hwv i, hwvp i⟩⟩
  obtain ⟨V, hV⟩ := hmem.exists_sobolevMultiIndex
  have hVd : ∀ i, ⇑(weakDeriv V (MultiIndexLE.single i))
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] wv i := fun i ↦ by
    have h1 := ((hasWeakIteratedLineDerivOn V (MultiIndexLE.single i)).of_perm
      (multiIndexTuple_single_perm ((EuclideanSpace.basisFun (Fin N) ℝ).toBasis :
        Fin N → EuclideanSpace ℝ (Fin N)) i)).congr_ae hV (EventuallyEq.refl _ _)
    rw [EuclideanSpace.basisFun_toBasis_apply] at h1
    exact (ae_restrict_iff' Ω.isOpen.measurableSet).2 (h1.ae_eq (hwv i))
  refine ⟨V, hg.toLp g, hV, hVd, hg.coeFn_toLp, ?_⟩
  rintro Φ ⟨ψ, hψ⟩
  rw [dirichletForm_apply_eq_of_ae_eq hVd hψ, load_apply_eq_of_ae_eq hg.coeFn_toLp hψ]
  exact heq ψ

/-- **From the typed form to the predicate form of a weak solution**: if
`∫_Ω ∇U · ∇Φ = ∫_Ω F Φ` for every test-function element `Φ`, then
`∑ᵢ ∫_Ω ∂ᵢU ∂ᵢψ = ∫_Ω F ψ` for every test function `ψ` on `Ω`. -/
theorem forall_testFunction_of_forall_testFunctions {U : SobolevEuclidean N 1 2 Ω}
    {F : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (h : ∀ Φ ∈ testFunctions ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume,
      dirichletForm Ω U Φ = load Ω F Φ) (ψ : 𝓓(Ω, ℝ)) :
    ∑ i, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      weakDeriv U (MultiIndexLE.single i) x * fderiv ℝ ψ x (EuclideanSpace.single i 1)
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), F x * ψ x := by
  obtain ⟨Φ, hΦ, hΦψ⟩ := ψ.exists_mem_sobolevMultiIndex_testFunctions
    (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis) (k := 1) (p := 2) (μ := volume)
  rw [← dirichletForm_apply_eq_of_ae_eq (fun i ↦ EventuallyEq.refl _ _) hΦψ,
    ← load_apply_eq_of_ae_eq (EventuallyEq.refl _ _) hΦψ]
  exact h Φ hΦ

end Bridge

/-! ### Case C₁: interior regularity -/

section Interior

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
/-- A continuous function with compact support in `Ω` times a function locally in `L^p` on `Ω`
lies in `L^p(Ω)`, `p < ∞`. -/
theorem _root_.MeasureTheory.LocallyMemLpOn.memLp_mul_of_tsupport_subset {p : ℝ≥0∞}
    (hp : p ≠ ⊤) {u : E → ℝ} (hu : LocallyMemLpOn u p Ω μ) {θ : E → ℝ} (hθ : Continuous θ)
    (hθc : HasCompactSupport θ) (hθΩ : tsupport θ ⊆ Ω) :
    MemLp (fun x ↦ θ x * u x) p (μ.restrict (Ω : Set E)) := by
  obtain ⟨C, hC⟩ := hθc.exists_bound_of_continuous hθ
  have hK : MemLp u p (μ.restrict (tsupport θ)) := hu.memLp_restrict_of_compact_subset hp hθΩ hθc
  have h1 : MemLp (fun x ↦ θ x * u x) p (μ.restrict (tsupport θ)) := by
    refine (hK.const_mul C).of_le (hθ.aestronglyMeasurable.mul hK.aestronglyMeasurable)
      (Eventually.of_forall fun x ↦ ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg
      ((norm_nonneg _).trans (hC 0))]
    exact mul_le_mul_of_nonneg_right ((Real.norm_eq_abs _).symm.trans_le (hC x)) (abs_nonneg _)
  have h2 : MemLp ((tsupport θ).indicator fun x ↦ θ x * u x) p μ :=
    (memLp_indicator_iff_restrict (isClosed_tsupport θ).measurableSet).2 h1
  have h3 : (tsupport θ).indicator (fun x ↦ θ x * u x) = fun x ↦ θ x * u x := by
    funext x
    by_cases hx : x ∈ tsupport θ
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx, zero_mul]
  rw [h3] at h2
  exact h2.restrict _

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
/-- The zero extension of a continuous compactly supported function in `Ω` times a function
locally in `L^p` on `Ω` lies in `L^p` of the whole space. -/
theorem _root_.MeasureTheory.LocallyMemLpOn.memLp_indicator_mul_of_tsupport_subset {p : ℝ≥0∞}
    (hp : p ≠ ⊤) {u : E → ℝ} (hu : LocallyMemLpOn u p Ω μ) {θ : E → ℝ} (hθ : Continuous θ)
    (hθc : HasCompactSupport θ) (hθΩ : tsupport θ ⊆ Ω) :
    MemLp ((Ω : Set E).indicator fun x ↦ θ x * u x) p μ :=
  (memLp_indicator_iff_restrict Ω.isOpen.measurableSet).2
    (hu.memLp_mul_of_tsupport_subset hp hθ hθc hθΩ)

omit [BorelSpace E] in
/-- A function locally in `L^p` on an open set, `1 ≤ p < ∞`, is locally integrable there. -/
theorem _root_.MeasureTheory.LocallyMemLpOn.locallyIntegrableOn_of_le {p : ℝ≥0∞} {u : E → ℝ}
    (hu : LocallyMemLpOn u p Ω μ) (hp : 1 ≤ p) (hp' : p ≠ ⊤) : LocallyIntegrableOn u Ω μ := by
  rw [locallyIntegrableOn_iff Ω.isOpen.isLocallyClosed]
  intro k hk hkc
  have : IsFiniteMeasure (μ.restrict k) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hkc.measure_lt_top⟩
  exact (hu.memLp_restrict_of_compact_subset hp' hk hkc).integrable hp

omit [MeasurableSpace E] [BorelSpace E] in
/-- A smooth function equal to `1` on a compact subset `K` of `Ω`, with compact support in `Ω`. -/
theorem exists_contDiff_eqOn_one_hasCompactSupport {K : Set E} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) :
    ∃ θ : E → ℝ, ContDiff ℝ ∞ θ ∧ EqOn θ 1 K ∧ HasCompactSupport θ ∧ tsupport θ ⊆ Ω := by
  obtain ⟨L, hLc, hKL, hLΩ⟩ := exists_compact_between hK Ω.isOpen hKΩ
  obtain ⟨θ, hθ, hθ1, hθL, -⟩ := hK.exists_contDiff_eqOn_one isOpen_interior hKL
  exact ⟨θ, hθ, hθ1, hLc.of_isClosed_subset (isClosed_tsupport θ) (hθL.trans interior_subset),
    hθL.trans (interior_subset.trans hLΩ)⟩

end Interior

section InteriorEuclidean

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

open SobolevMultiIndex

/-- **Theorem 9.25, case C₁ = Remark 25 at `m = 0`: interior `H²` regularity on an arbitrary open
set** ([brezis2011functional] §9.6). Let `Ω ⊆ ℝ^N` be open, let `u ∈ H^1_loc(Ω)` with the weak
partial derivatives `w i ∈ L²_loc(Ω)`, let `f ∈ L²_loc(Ω)`, and let
`∑ᵢ ∫_Ω wᵢ ∂ᵢφ = ∫_Ω f φ` for every test function `φ` on `Ω`. Then `u ∈ H²_loc(Ω)`: `u ∈ H²(ω)`
for every open `ω` with compact closure in `Ω`.

The proof is the book's: for such an `ω`, a smooth `θ` equal to `1` on `closure ω` with compact
support in `Ω` (`Elliptic.exists_contDiff_eqOn_one_hasCompactSupport`); `θu` extended by zero
lies in `H^1(ℝ^N)` (`HasWeakIteratedLineDerivOn.indicator_mul`) and solves
`−Δ(θu) = θf − 2∇θ·∇u − (Δθ)u ∈ L²(ℝ^N)` against the test functions
(`Elliptic.sum_integral_indicator_cutoff_eq`), hence against all of `H^1(ℝ^N)` by density
(`Elliptic.dirichletForm_eq_load_of_forall_testFunctions`, `SobolevEuclideanZero.eq_top`); case A
(`Elliptic.regularity_top_memSobolevMultiIndex`) gives `θu ∈ H²(ℝ^N)`, and `θu = u` on `ω`. -/
theorem regularity_interior {u f : EuclideanSpace ℝ (Fin N) → ℝ}
    {w : Fin N → EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : LocallyMemLpOn u 2 Ω volume)
    (hw : ∀ i, HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1] u (w i) Ω volume)
    (hwp : ∀ i, LocallyMemLpOn (w i) 2 Ω volume) (hf : LocallyMemLpOn f 2 Ω volume)
    (heq : ∀ φ : 𝓓(Ω, ℝ), ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      ∑ i, w i x * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), f x * φ x) :
    MemSobolevMultiIndexLoc (EuclideanSpace.basisFun (Fin N) ℝ).toBasis u 2 2 Ω volume := by
  intro V hVc hVΩ
  have h2 : (2 : ℝ≥0∞) ≠ ⊤ := ENNReal.ofNat_ne_top
  have hul : LocallyIntegrableOn u Ω volume := hu.locallyIntegrableOn_of_le one_le_two h2
  have hfl : LocallyIntegrableOn f Ω volume := hf.locallyIntegrableOn_of_le one_le_two h2
  -- the cut-off and its derivatives
  obtain ⟨θ, hθ, hθ1, hθc, hθΩ⟩ := exists_contDiff_eqOn_one_hasCompactSupport hVc hVΩ
  have hθ' : IsSobolevCutoff Ω θ := IsSobolevCutoff.of_hasCompactSupport hθ hθc hθΩ
  have hdθ : ∀ i, ContDiff ℝ ∞ fun x ↦ fderiv ℝ θ x (EuclideanSpace.single i 1) := fun i ↦
    hθ'.contDiff_fderiv_apply _
  have hdθc : ∀ i, HasCompactSupport fun x ↦ fderiv ℝ θ x (EuclideanSpace.single i 1) :=
    fun i ↦ hθc.fderiv_apply ℝ _
  have hdθΩ : ∀ i, tsupport (fun x ↦ fderiv ℝ θ x (EuclideanSpace.single i 1)) ⊆ Ω := fun i ↦
    (tsupport_fderiv_apply_subset ℝ _).trans hθΩ
  have hddθ : ∀ i, ContDiff ℝ ∞ fun x ↦
      fderiv ℝ (fun z ↦ fderiv ℝ θ z (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1) :=
    fun i ↦ contDiff_fderiv_fderiv_apply hθ _
  have hddθc : ∀ i, HasCompactSupport fun x ↦
      fderiv ℝ (fun z ↦ fderiv ℝ θ z (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1) :=
    fun i ↦ (hdθc i).fderiv_apply ℝ _
  have hddθΩ : ∀ i, tsupport (fun x ↦
      fderiv ℝ (fun z ↦ fderiv ℝ θ z (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1))
      ⊆ Ω := fun i ↦ (tsupport_fderiv_apply_subset ℝ _).trans (hdθΩ i)
  -- the pieces, as functions on `ℝ^N`
  obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin N) → ℝ,
      v = (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator fun x ↦ θ x * u x := ⟨_, rfl⟩
  obtain ⟨wv, hwv⟩ : ∃ wv : Fin N → EuclideanSpace ℝ (Fin N) → ℝ,
      wv = fun i ↦ (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator
        fun x ↦ θ x * w i x + fderiv ℝ θ x (EuclideanSpace.single i 1) * u x := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : EuclideanSpace ℝ (Fin N) → ℝ,
      g = (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator fun x ↦
        θ x * f x - 2 * ∑ i, fderiv ℝ θ x (EuclideanSpace.single i 1) * w i x
        - (∑ i, fderiv ℝ (fun z ↦ fderiv ℝ θ z (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1)) * u x := ⟨_, rfl⟩
  -- their `L²` memberships
  have hvp : MemLp v 2 (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) : Set _)) := by
    rw [Measure.restrict_coe_top, hv]
    exact hu.memLp_indicator_mul_of_tsupport_subset h2 hθ.continuous hθc hθΩ
  have hwvp : ∀ i, MemLp (wv i) 2
      (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) : Set _)) := fun i ↦ by
    rw [Measure.restrict_coe_top, hwv]
    have h1 := (hwp i).memLp_indicator_mul_of_tsupport_subset h2 hθ.continuous hθc hθΩ
    have h2' := hu.memLp_indicator_mul_of_tsupport_subset h2 (hdθ i).continuous (hdθc i) (hdθΩ i)
    refine (h1.add h2').ae_eq (Eventually.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ (Ω : Set (EuclideanSpace ℝ (Fin N)))
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hgp : MemLp g 2 (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) : Set _)) := by
    rw [Measure.restrict_coe_top, hg]
    have h1 := hf.memLp_indicator_mul_of_tsupport_subset h2 hθ.continuous hθc hθΩ
    have h2' : ∀ i, MemLp ((Ω : Set (EuclideanSpace ℝ (Fin N))).indicator
        fun x ↦ fderiv ℝ θ x (EuclideanSpace.single i 1) * w i x) 2 volume := fun i ↦
      (hwp i).memLp_indicator_mul_of_tsupport_subset h2 (hdθ i).continuous (hdθc i) (hdθΩ i)
    have h3 : ∀ i, MemLp ((Ω : Set (EuclideanSpace ℝ (Fin N))).indicator
        fun x ↦ fderiv ℝ (fun z ↦ fderiv ℝ θ z (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1) * u x) 2 volume := fun i ↦
      hu.memLp_indicator_mul_of_tsupport_subset h2 (hddθ i).continuous (hddθc i) (hddθΩ i)
    have hS2 := memLp_finsetSum (μ := volume) (p := 2) Finset.univ
      (f := fun i ↦ (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator
        fun x ↦ fderiv ℝ θ x (EuclideanSpace.single i 1) * w i x) (fun i _ ↦ h2' i)
    have hS3 := memLp_finsetSum (μ := volume) (p := 2) Finset.univ
      (f := fun i ↦ (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator
        fun x ↦ fderiv ℝ (fun z ↦ fderiv ℝ θ z (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1) * u x) (fun i _ ↦ h3 i)
    refine ((h1.sub (hS2.const_mul 2)).sub hS3).ae_eq (Eventually.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ (Ω : Set (EuclideanSpace ℝ (Fin N)))
    · simp only [Pi.sub_apply, Set.indicator_of_mem hx, Finset.sum_mul]
    · simp [Set.indicator_of_notMem hx]
  -- the weak derivatives of `v` on `ℝ^N`
  have hwvd : ∀ i, HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1] v (wv i) ⊤ volume :=
    fun i ↦ by
      rw [hv, hwv]
      exact (hw i).indicator_mul hθ'
  -- the equation on `ℝ^N`, against the test functions
  have heqv : ∀ ψ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin N))), ℝ),
      ∑ i, ∫ x in ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) : Set _),
        wv i x * fderiv ℝ ψ x (EuclideanSpace.single i 1)
      = ∫ x in ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) : Set _), g x * ψ x := fun ψ ↦ by
    simp only [Measure.restrict_coe_top]
    rw [hwv, hg]
    exact sum_integral_indicator_cutoff_eq (fun i ↦ EuclideanSpace.single i 1) hul hfl hw heq hθ' ψ
  obtain ⟨V₁, G, hV₁, -, -, hVG⟩ :=
    exists_sobolevEuclidean_of_forall_testFunction hvp hwvd hwvp hgp heqv
  have hall : ∀ φ, dirichletForm (⊤ : Opens (EuclideanSpace ℝ (Fin N))) V₁ φ
      = load (⊤ : Opens (EuclideanSpace ℝ (Fin N))) G φ := fun φ ↦
    dirichletForm_eq_load_of_forall_testFunctions hVG
      (by rw [SobolevEuclideanZero.eq_top h2]; exact Submodule.mem_top)
  have hmem := (regularity_top_memSobolevMultiIndex hall).congr_ae hV₁
  refine (hmem.mono_set le_top).congr_ae ?_
  refine (ae_restrict_iff' V.isOpen.measurableSet).2 (Eventually.of_forall fun x hx ↦ ?_)
  rw [hv, Set.indicator_of_mem (hVΩ (subset_closure hx)), hθ1 (subset_closure hx), Pi.one_apply,
    one_mul]

end InteriorEuclidean


/-! ### The normal derivative from the equation -/

/-- A double sum with the `(i₀, i₀)` term separated off. -/
theorem sum_sum_eq_add_sum_sum_ite {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid M]
    (F : ι → ι → M) (i₀ : ι) :
    ∑ k, ∑ l, F k l = F i₀ i₀ + ∑ k, ∑ l, if k = i₀ ∧ l = i₀ then 0 else F k l := by
  have h : ∀ k l, F k l = (if k = i₀ ∧ l = i₀ then F k l else 0)
      + if k = i₀ ∧ l = i₀ then 0 else F k l := fun k l ↦ by
    split_ifs <;> simp
  conv_lhs => rw [Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ h k l]
  simp only [Finset.sum_add_distrib]
  congr 1
  simp [ite_and, Finset.sum_ite_eq']

section Normal

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **The equation gives the normal derivative of `a_{NN} w_N`** ([brezis2011functional] §9.6,
(57) and (69)): let `w i ∈ L²(Ω)` (the weak partial derivatives of a solution), let the
coefficients `a_{kℓ}` be `C¹` on `Ω` with `|a_{kℓ}| ≤ M₀` and `‖∇a_{kℓ}‖ ≤ M` there, let
`∑_{kℓ} ∫_Ω a_{kℓ} w_k ∂_ℓ φ = ∫_Ω f φ` for every test function `φ`, and suppose every `w_k` has a
weak derivative `v_{kℓ} ∈ L²(Ω)` along `e_ℓ` for `(k, ℓ) ≠ (N, N)`. Then `a_{NN} w_N` has the weak
derivative `−(f + ∑_{(k,ℓ) ≠ (N,N)} ((∂_ℓ a_{kℓ}) w_k + a_{kℓ} v_{kℓ}))` along `e_N`, which lies in
`L²(Ω)`: the equation, with the other terms integrated by parts through the product rule
`HasWeakIteratedLineDerivOn.mul`. -/
theorem hasWeakIteratedLineDerivOn_last_mul_of_forall {f : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    {w : Fin (d + 1) → EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    {a v : Fin (d + 1) → Fin (d + 1) → EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (ha : ∀ k l, ContDiffOn ℝ 1 (a k l) Ω) {M₀ M : ℝ}
    (haM₀ : ∀ k l, ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), |a k l x| ≤ M₀)
    (haM : ∀ k l, ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), ‖fderiv ℝ (a k l) x‖ ≤ M)
    (hwp : ∀ i, MemLp (w i) 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (hf : MemLp f 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (hv : ∀ k l, (k ≠ Fin.last d ∨ l ≠ Fin.last d) →
      HasWeakIteratedLineDerivOn ![EuclideanSpace.single l 1] (w k) (v k l) Ω volume)
    (hvp : ∀ k l, MemLp (v k l) 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (heq : ∀ φ : 𝓓(Ω, ℝ), ∑ k, ∑ l, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      a k l x * w k x * fderiv ℝ φ x (EuclideanSpace.single l 1)
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), f x * φ x) :
    HasWeakIteratedLineDerivOn ![EuclideanSpace.single (Fin.last d) 1]
      (fun x ↦ a (Fin.last d) (Fin.last d) x * w (Fin.last d) x)
      (fun x ↦ -(f x + ∑ k, ∑ l, if k = Fin.last d ∧ l = Fin.last d then 0 else
        fderiv ℝ (a k l) x (EuclideanSpace.single l 1) * w k x + a k l x * v k l x)) Ω volume ∧
    MemLp (fun x ↦ -(f x + ∑ k, ∑ l, if k = Fin.last d ∧ l = Fin.last d then 0 else
        fderiv ℝ (a k l) x (EuclideanSpace.single l 1) * w k x + a k l x * v k l x)) 2
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) := by
  have h2 : (2 : ℝ≥0∞) ≠ ⊤ := ENNReal.ofNat_ne_top
  have hΩm : MeasurableSet (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) := Ω.isOpen.measurableSet
  -- the coefficients and their derivatives, measurable and locally `L²`
  have hac : ∀ k l, ContinuousOn (a k l) Ω := fun k l ↦ (ha k l).continuousOn
  have hdac : ∀ k l, ContinuousOn (fun x ↦ fderiv ℝ (a k l) x (EuclideanSpace.single l 1)) Ω :=
    fun k l ↦ (((ha k l).fderiv_of_isOpen Ω.isOpen (m := 0) le_rfl).continuousOn).clm_apply
      continuousOn_const
  have hdaM : ∀ k l, ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      |fderiv ℝ (a k l) x (EuclideanSpace.single l 1)| ≤ M := fun k l x hx ↦ by
    rw [← Real.norm_eq_abs]
    refine ((fderiv ℝ (a k l) x).le_opNorm _).trans ?_
    rw [PiLp.norm_single, norm_one, mul_one]
    exact haM k l x hx
  -- the terms of the sum are in `L²(Ω)`
  have hterm : ∀ k l, MemLp (fun x ↦ if k = Fin.last d ∧ l = Fin.last d then 0 else
      fderiv ℝ (a k l) x (EuclideanSpace.single l 1) * w k x + a k l x * v k l x) 2
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) := fun k l ↦ by
    split_ifs
    · exact MemLp.zero
    · exact ((hwp k).mul_of_forall_abs_le ((hdac k l).aestronglyMeasurable hΩm) (hdaM k l)).add
        ((hvp k l).mul_of_forall_abs_le ((hac k l).aestronglyMeasurable hΩm) (haM₀ k l))
  have hG : MemLp (fun x ↦ -(f x + ∑ k, ∑ l, if k = Fin.last d ∧ l = Fin.last d then 0 else
      fderiv ℝ (a k l) x (EuclideanSpace.single l 1) * w k x + a k l x * v k l x)) 2
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    (hf.add (memLp_finsetSum _ fun k _ ↦ memLp_finsetSum _ fun l _ ↦ hterm k l)).neg
  -- the product rule for `a_{kℓ} w_k`, `(k, ℓ) ≠ (N, N)`
  have hprod : ∀ k l, (k ≠ Fin.last d ∨ l ≠ Fin.last d) →
      HasWeakIteratedLineDerivOn ![EuclideanSpace.single l 1] (fun x ↦ a k l x * w k x)
        (fun x ↦ fderiv ℝ (a k l) x (EuclideanSpace.single l 1) * w k x + a k l x * v k l x)
        Ω volume := fun k l hkl ↦
    ((ha k l).hasWeakIteratedLineDerivOn_single Ω l).mul rfl (hv k l hkl) one_le_two h2 h2
      ((hac k l).locallyMemLpOn 2) ((hdac k l).locallyMemLpOn 2) (hwp k).locallyMemLpOn
      (hvp k l).locallyMemLpOn
  refine ⟨⟨((hac _ _).locallyMemLpOn 2).locallyIntegrableOn_mul (hwp _).locallyMemLpOn,
    hG.locallyIntegrableOn one_le_two, fun φ ↦ ?_⟩, hG⟩
  -- the defining identity: the equation, split at `(N, N)`
  have hsplit := sum_sum_eq_add_sum_sum_ite
    (fun k l ↦ ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
    a k l x * w k x * fderiv ℝ φ x (EuclideanSpace.single l 1)) (Fin.last d)
  rw [heq φ] at hsplit
  have hib : ∀ k l, (if k = Fin.last d ∧ l = Fin.last d then 0 else
      ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
        a k l x * w k x * fderiv ℝ φ x (EuclideanSpace.single l 1))
      = -∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
          φ x * (if k = Fin.last d ∧ l = Fin.last d
          then 0 else fderiv ℝ (a k l) x (EuclideanSpace.single l 1) * w k x + a k l x * v k l x) :=
    fun k l ↦ by
      split_ifs with hkl
      · simp
      · have hkl' : k ≠ Fin.last d ∨ l ≠ Fin.last d := by
          rcases not_and_or.1 hkl with h | h
          · exact Or.inl h
          · exact Or.inr h
        have := (hprod k l hkl').integral_fderiv_mul_eq_of_eqOn φ (fun _ _ ↦ rfl)
        rw [← this]
        exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
  simp only [hib, Finset.sum_neg_distrib] at hsplit
  simp only [iteratedFDeriv_one_apply, Matrix.cons_val_zero, pow_one, smul_eq_mul, neg_one_mul]
  have hI : ∀ k l, Integrable (fun x ↦ φ x * (if k = Fin.last d ∧ l = Fin.last d then 0 else
      fderiv ℝ (a k l) x (EuclideanSpace.single l 1) * w k x + a k l x * v k l x))
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) := fun k l ↦
    ((hterm k l).locallyIntegrableOn one_le_two).integrable_smul_left_of_tsupport_subset
      φ.continuous φ.hasCompactSupport φ.tsupport_subset |>.integrableOn
  have hIf : Integrable (fun x ↦ φ x * f x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    ((hf.locallyIntegrableOn one_le_two).integrable_smul_left_of_tsupport_subset φ.continuous
      φ.hasCompactSupport φ.tsupport_subset).integrableOn
  have hS : ∀ k, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      ∑ l, φ x * (if k = Fin.last d ∧ l = Fin.last d then 0 else
        fderiv ℝ (a k l) x (EuclideanSpace.single l 1) * w k x + a k l x * v k l x)
      = ∑ l, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
        φ x * (if k = Fin.last d ∧ l = Fin.last d then 0 else
          fderiv ℝ (a k l) x (EuclideanSpace.single l 1) * w k x + a k l x * v k l x) :=
    fun k ↦ integral_finsetSum _ fun l _ ↦ hI k l
  have hR : -∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
        φ x * -(f x + ∑ k, ∑ l, if k = Fin.last d ∧ l = Fin.last d then 0 else
          fderiv ℝ (a k l) x (EuclideanSpace.single l 1) * w k x + a k l x * v k l x)
      = (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), f x * φ x)
        + ∑ k, ∑ l, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
          φ x * (if k = Fin.last d ∧ l = Fin.last d then 0 else
            fderiv ℝ (a k l) x (EuclideanSpace.single l 1) * w k x + a k l x * v k l x) := by
    have e : (fun x ↦ φ x * -(f x + ∑ k, ∑ l, if k = Fin.last d ∧ l = Fin.last d then 0 else
          fderiv ℝ (a k l) x (EuclideanSpace.single l 1) * w k x + a k l x * v k l x))
        = fun x ↦ -(φ x * f x + ∑ k, ∑ l, φ x * (if k = Fin.last d ∧ l = Fin.last d then 0 else
          fderiv ℝ (a k l) x (EuclideanSpace.single l 1) * w k x + a k l x * v k l x)) := by
      funext x
      simp only [mul_neg, mul_add, Finset.mul_sum]
    rw [e, integral_neg, neg_neg, integral_add hIf (integrable_finsetSum _ fun k _ ↦
      integrable_finsetSum _ fun l _ ↦ hI k l), integral_finsetSum _ fun k _ ↦
      integrable_finsetSum _ fun l _ ↦ hI k l]
    simp only [hS]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
  have e1 : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      fderiv ℝ φ x (EuclideanSpace.single (Fin.last d) 1)
        * (a (Fin.last d) (Fin.last d) x * w (Fin.last d) x)
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), a (Fin.last d) (Fin.last d) x
          * w (Fin.last d) x * fderiv ℝ φ x (EuclideanSpace.single (Fin.last d) 1) :=
    integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
  rw [e1, hR]
  linarith [hsplit]


/-- **The normal-normal derivative of a weak solution, from the equation** ([brezis2011functional]
§9.6, (57) and (68)–(69)): under the hypotheses of
`Elliptic.hasWeakIteratedLineDerivOn_last_mul_of_forall`, with `a_{NN} ≥ α > 0` on `Ω`, the
derivative `w_N` has a weak derivative `v_{NN}` along `e_N` in `L²(Ω)`, dominated pointwise by
`α⁻¹ (M |w_N| + |f| + ∑_{kℓ} (M |w_k| + M₀ |v_{kℓ}|))`: divide the equation
`∂_N(a_{NN} w_N) = −(f + …)` by `a_{NN}` with the product rule for the `C¹` factor `1/a_{NN}`. -/
theorem exists_hasWeakIteratedLineDerivOn_last_of_forall {f : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    {w : Fin (d + 1) → EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    {a v : Fin (d + 1) → Fin (d + 1) → EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (ha : ∀ k l, ContDiffOn ℝ 1 (a k l) Ω) {M₀ M α : ℝ}
    (haM₀ : ∀ k l, ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), |a k l x| ≤ M₀)
    (haM : ∀ k l, ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), ‖fderiv ℝ (a k l) x‖ ≤ M)
    (hα0 : 0 < α)
    (hα : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), α ≤ a (Fin.last d) (Fin.last d) x)
    (hwp : ∀ i, MemLp (w i) 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (hf : MemLp f 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (hv : ∀ k l, (k ≠ Fin.last d ∨ l ≠ Fin.last d) →
      HasWeakIteratedLineDerivOn ![EuclideanSpace.single l 1] (w k) (v k l) Ω volume)
    (hvp : ∀ k l, MemLp (v k l) 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (heq : ∀ φ : 𝓓(Ω, ℝ), ∑ k, ∑ l, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      a k l x * w k x * fderiv ℝ φ x (EuclideanSpace.single l 1)
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), f x * φ x) :
    ∃ vNN : EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
      HasWeakIteratedLineDerivOn ![EuclideanSpace.single (Fin.last d) 1] (w (Fin.last d)) vNN
        Ω volume ∧
      MemLp vNN 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) ∧
      ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), |vNN x| ≤ α⁻¹ * (M * |w (Fin.last d) x|
        + |f x| + ∑ k, ∑ l, (M * |w k x| + M₀ * |v k l x|)) := by
  have h2 : (2 : ℝ≥0∞) ≠ ⊤ := ENNReal.ofNat_ne_top
  have hΩm : MeasurableSet (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) := Ω.isOpen.measurableSet
  obtain ⟨hGd, hGp⟩ := hasWeakIteratedLineDerivOn_last_mul_of_forall ha haM₀ haM hwp hf hv hvp heq
  obtain ⟨G, hG⟩ : ∃ G : EuclideanSpace ℝ (Fin (d + 1)) → ℝ, G = fun x ↦
      -(f x + ∑ k, ∑ l, if k = Fin.last d ∧ l = Fin.last d then 0 else
        fderiv ℝ (a k l) x (EuclideanSpace.single l 1) * w k x + a k l x * v k l x) := ⟨_, rfl⟩
  rw [← hG] at hGd hGp
  obtain ⟨aN, haN⟩ : ∃ aN : EuclideanSpace ℝ (Fin (d + 1)) → ℝ, aN = a (Fin.last d) (Fin.last d) :=
    ⟨_, rfl⟩
  have haNc : ContDiffOn ℝ 1 aN Ω := haN ▸ ha _ _
  have haNpos : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), 0 < aN x := fun x hx ↦
    haN ▸ hα0.trans_le (hα x hx)
  have haNne : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), aN x ≠ 0 := fun x hx ↦
    (haNpos x hx).ne'
  have haNM₀ : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), |aN x| ≤ M₀ := fun x hx ↦
    haN ▸ haM₀ _ _ x hx
  have haNM : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      |fderiv ℝ aN x (EuclideanSpace.single (Fin.last d) 1)| ≤ M := fun x hx ↦ by
    rw [← Real.norm_eq_abs]
    refine ((fderiv ℝ aN x).le_opNorm _).trans ?_
    rw [PiLp.norm_single, norm_one, mul_one, haN]
    exact haM _ _ x hx
  rw [← haN] at hGd
  -- the inverse coefficient and its derivative
  have hinv : ContDiffOn ℝ 1 (fun x ↦ (aN x)⁻¹) Ω := haNc.inv haNne
  have hinvd : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      fderiv ℝ (fun z ↦ (aN z)⁻¹) x (EuclideanSpace.single (Fin.last d) 1)
        = -(aN x ^ 2)⁻¹ * fderiv ℝ aN x (EuclideanSpace.single (Fin.last d) 1) := fun x hx ↦ by
    have hd : HasFDerivAt aN (fderiv ℝ aN x) x :=
      ((haNc.differentiableOn one_ne_zero).differentiableAt (Ω.isOpen.mem_nhds hx)).hasFDerivAt
    have this : HasFDerivAt (fun z ↦ (aN z)⁻¹)
        ((ContinuousLinearMap.toSpanSingleton ℝ (-(aN x ^ 2)⁻¹)).comp (fderiv ℝ aN x)) x :=
      (hasFDerivAt_inv (haNne x hx)).comp x hd
    rw [this.fderiv]
    simp [ContinuousLinearMap.toSpanSingleton_apply, mul_comm]
  have hinvw : HasWeakIteratedLineDerivOn ![EuclideanSpace.single (Fin.last d) 1]
      (fun x ↦ (aN x)⁻¹) (fun x ↦ fderiv ℝ (fun z ↦ (aN z)⁻¹) x
        (EuclideanSpace.single (Fin.last d) 1)) Ω volume :=
    hinv.hasWeakIteratedLineDerivOn_single Ω _
  have hinvc : ContinuousOn (fun x ↦ (aN x)⁻¹) Ω := hinv.continuousOn
  have hinvdc : ContinuousOn (fun x ↦ fderiv ℝ (fun z ↦ (aN z)⁻¹) x
      (EuclideanSpace.single (Fin.last d) 1)) Ω :=
    ((hinv.fderiv_of_isOpen Ω.isOpen (m := 0) le_rfl).continuousOn).clm_apply continuousOn_const
  have haNw : MemLp (fun x ↦ aN x * w (Fin.last d) x) 2
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    (hwp _).mul_of_forall_abs_le (haNc.continuousOn.aestronglyMeasurable hΩm) haNM₀
  -- the product rule for `(1/a_{NN}) (a_{NN} w_N)`
  have hprod := hinvw.mul rfl hGd one_le_two h2 h2 (hinvc.locallyMemLpOn 2)
    (hinvdc.locallyMemLpOn 2) haNw.locallyMemLpOn hGp.locallyMemLpOn
  obtain ⟨vNN, hvNN⟩ : ∃ vNN : EuclideanSpace ℝ (Fin (d + 1)) → ℝ, vNN = fun x ↦
      fderiv ℝ (fun z ↦ (aN z)⁻¹) x (EuclideanSpace.single (Fin.last d) 1)
        * (aN x * w (Fin.last d) x) + (aN x)⁻¹ * G x := ⟨_, rfl⟩
  rw [← hvNN] at hprod
  -- the pointwise bound on `Ω`
  have hGb : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      |G x| ≤ |f x| + ∑ k, ∑ l, (M * |w k x| + M₀ * |v k l x|) := fun x hx ↦ by
    rw [hG, abs_neg]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ ↦ ?_)
    split_ifs
    · rw [abs_zero]
      exact add_nonneg (mul_nonneg ((norm_nonneg _).trans (haM k l x hx)) (abs_nonneg _))
        (mul_nonneg ((abs_nonneg _).trans (haM₀ k l x hx)) (abs_nonneg _))
    · refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        rw [← Real.norm_eq_abs]
        refine ((fderiv ℝ (a k l) x).le_opNorm _).trans ?_
        rw [PiLp.norm_single, norm_one, mul_one]
        exact haM k l x hx
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (haM₀ k l x hx) (abs_nonneg _)
  have hbound : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), |vNN x| ≤ α⁻¹
      * (M * |w (Fin.last d) x| + |f x| + ∑ k, ∑ l, (M * |w k x| + M₀ * |v k l x|)) := by
    intro x hx
    have hαx : α ≤ aN x := haN ▸ hα x hx
    have hax : 0 < aN x := haNpos x hx
    rw [hvNN]
    simp only
    rw [hinvd x hx]
    have e : -(aN x ^ 2)⁻¹ * fderiv ℝ aN x (EuclideanSpace.single (Fin.last d) 1)
        * (aN x * w (Fin.last d) x)
        = -(fderiv ℝ aN x (EuclideanSpace.single (Fin.last d) 1) / aN x) * w (Fin.last d) x := by
      field_simp
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_neg, abs_div, abs_inv, abs_of_pos hax, mul_add, mul_add]
    have h1 : |fderiv ℝ aN x (EuclideanSpace.single (Fin.last d) 1)| / aN x * |w (Fin.last d) x|
        ≤ α⁻¹ * (M * |w (Fin.last d) x|) := by
      rw [div_eq_mul_inv, mul_comm |fderiv ℝ aN x (EuclideanSpace.single (Fin.last d) 1)| (aN x)⁻¹,
        mul_assoc]
      exact mul_le_mul (inv_anti₀ hα0 hαx) (mul_le_mul_of_nonneg_right (haNM x hx) (abs_nonneg _))
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (inv_nonneg.2 hα0.le)
    have h2 : (aN x)⁻¹ * |G x| ≤ α⁻¹ * (|f x| + ∑ k, ∑ l, (M * |w k x| + M₀ * |v k l x|)) :=
      mul_le_mul (inv_anti₀ hα0 hαx) (hGb x hx) (abs_nonneg _) (inv_nonneg.2 hα0.le)
    linarith
  refine ⟨vNN, hprod.congr_ae ?_ (EventuallyEq.refl _ _), ?_, hbound⟩
  · refine (ae_restrict_iff' hΩm).2 (Eventually.of_forall fun x hx ↦ ?_)
    simp only
    rw [inv_mul_cancel_left₀ (haNne x hx)]
  · -- `L²` membership from the domination
    have hD : MemLp (fun x ↦ α⁻¹ * (M * |w (Fin.last d) x| + |f x|
        + ∑ k, ∑ l, (M * |w k x| + M₀ * |v k l x|))) 2
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) := by
      refine MemLp.const_mul ?_ _
      refine ((((hwp _).abs).const_mul M).add hf.abs).add (memLp_finsetSum _ fun k _ ↦
        memLp_finsetSum _ fun l _ ↦ (((hwp k).abs).const_mul M).add (((hvp k l).abs).const_mul M₀))
    refine hD.of_ae_norm_le_mul (c := 1) ?_ ((ae_restrict_mem hΩm).mono fun x hx ↦ ?_)
    · rw [hvNN]
      exact ((hinvdc.aestronglyMeasurable hΩm).mul haNw.aestronglyMeasurable).add
        ((hinvc.aestronglyMeasurable hΩm).mul hGp.aestronglyMeasurable)
    · rw [one_mul]
      exact (hbound x hx).trans (le_abs_self _)


end Normal


/-! ### From a pointwise domination to a norm bound -/

section Domination

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-- `‖M |w|‖₂ = M ‖W‖` for `W ∈ L²` the class of `w` and `M ≥ 0`. -/
theorem eLpNorm_const_mul_abs_eq {M : ℝ} (hM : 0 ≤ M) (W : Lp ℝ 2 ν) {w : X → ℝ}
    (hw : ⇑W =ᵐ[ν] w) : eLpNorm (fun x ↦ M * |w x|) 2 ν = ENNReal.ofReal (M * ‖W‖) := by
  have e1 : (fun x ↦ M * |w x|) = M • fun x ↦ ‖w x‖ := by
    funext x
    simp [Real.norm_eq_abs]
  rw [e1, eLpNorm_const_smul, eLpNorm_norm _ ((Lp.aestronglyMeasurable W).congr hw),
    ← eLpNorm_congr_ae hw, ← Lp.enorm_def, Real.enorm_of_nonneg hM, ← ofReal_norm,
    ← ENNReal.ofReal_mul hM]

/-- **From a pointwise domination to a norm bound**: if
`|φ| ≤ c (M |w₀| + |f| + ∑_{kℓ} (M |w_k| + M₀ |v_{kℓ}|))`
almost everywhere, then `‖φ‖₂ ≤ c (M ‖W₀‖ + ‖F‖ + ∑_{kℓ} (M ‖W_k‖ + M₀ ‖V_{kℓ}‖))` for the `L²`
classes `W₀, F, W_k, V_{kℓ}` of the dominating functions. -/
theorem norm_toLp_le_of_ae_abs_le {ι : Type*} [Fintype ι] {φ f : X → ℝ} {w : ι → X → ℝ}
    {v : ι → ι → X → ℝ} {c M M₀ : ℝ} (hc : 0 ≤ c) (hM : 0 ≤ M) (hM₀ : 0 ≤ M₀) (i₀ : ι)
    (hφ : MemLp φ 2 ν) (F : Lp ℝ 2 ν) (hF : ⇑F =ᵐ[ν] f) (W : ι → Lp ℝ 2 ν)
    (hW : ∀ i, ⇑(W i) =ᵐ[ν] w i) (V : ι → ι → Lp ℝ 2 ν) (hV : ∀ k l, ⇑(V k l) =ᵐ[ν] v k l)
    (h : ∀ᵐ x ∂ν, |φ x| ≤ c * (M * |w i₀ x| + |f x| + ∑ k, ∑ l, (M * |w k x| + M₀ * |v k l x|))) :
    ‖hφ.toLp φ‖ ≤ c * (M * ‖W i₀‖ + ‖F‖ + ∑ k, ∑ l, (M * ‖W k‖ + M₀ * ‖V k l‖)) := by
  have hD : eLpNorm φ 2 ν ≤ eLpNorm (fun x ↦ c * (M * |w i₀ x| + |f x|
      + ∑ k, ∑ l, (M * |w k x| + M₀ * |v k l x|))) 2 ν :=
    eLpNorm_mono_ae hφ.aestronglyMeasurable (h.mono fun x hx ↦ by
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      exact hx.trans (le_abs_self _))
  have e2 : (fun x ↦ c * (M * |w i₀ x| + |f x| + ∑ k, ∑ l, (M * |w k x| + M₀ * |v k l x|)))
      = c • (((fun x ↦ M * |w i₀ x|) + fun x ↦ |f x|)
        + ∑ k, ∑ l, ((fun x ↦ M * |w k x|) + fun x ↦ M₀ * |v k l x|)) := by
    funext x
    simp [Finset.sum_apply]
  have hf1 : eLpNorm (fun x ↦ |f x|) 2 ν = ENNReal.ofReal ‖F‖ := by
    have := eLpNorm_const_mul_abs_eq zero_le_one F hF
    simpa using this
  rw [Lp.norm_toLp]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) (hD.trans ?_)
  rw [e2, eLpNorm_const_smul, Real.enorm_of_nonneg hc]
  have hsum : eLpNorm (∑ k, ∑ l, ((fun x ↦ M * |w k x|) + fun x ↦ M₀ * |v k l x|)) 2 ν
      ≤ ∑ k, ∑ l, (ENNReal.ofReal (M * ‖W k‖) + ENNReal.ofReal (M₀ * ‖V k l‖)) := by
    refine (eLpNorm_sum_le one_le_two).trans (Finset.sum_le_sum fun k _ ↦ ?_)
    refine (eLpNorm_sum_le one_le_two).trans (Finset.sum_le_sum fun l _ ↦ ?_)
    refine (eLpNorm_add_le one_le_two).trans ?_
    rw [eLpNorm_const_mul_abs_eq hM (W k) (hW k), eLpNorm_const_mul_abs_eq hM₀ (V k l) (hV k l)]
  calc ENNReal.ofReal c * eLpNorm (((fun x ↦ M * |w i₀ x|) + fun x ↦ |f x|)
        + ∑ k, ∑ l, ((fun x ↦ M * |w k x|) + fun x ↦ M₀ * |v k l x|)) 2 ν
      ≤ ENNReal.ofReal c * ((ENNReal.ofReal (M * ‖W i₀‖) + ENNReal.ofReal ‖F‖)
        + ∑ k, ∑ l, (ENNReal.ofReal (M * ‖W k‖) + ENNReal.ofReal (M₀ * ‖V k l‖))) := by
        refine mul_le_mul' le_rfl ((eLpNorm_add_le one_le_two).trans (add_le_add ?_ hsum))
        refine (eLpNorm_add_le one_le_two).trans ?_
        rw [eLpNorm_const_mul_abs_eq hM (W i₀) (hW i₀), hf1]
    _ = ENNReal.ofReal (c * (M * ‖W i₀‖ + ‖F‖ + ∑ k, ∑ l, (M * ‖W k‖ + M₀ * ‖V k l‖))) := by
        rw [ENNReal.ofReal_mul hc]
        congr 1
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (norm_nonneg _),
          ENNReal.ofReal_sum_of_nonneg fun k _ ↦ Finset.sum_nonneg fun l _ ↦ by positivity]
        congr 1
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [ENNReal.ofReal_sum_of_nonneg fun l _ ↦ by positivity]
        refine Finset.sum_congr rfl fun l _ ↦ ?_
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]

end Domination


/-! ### Case B: the half space, for a variable-coefficient elliptic form -/

section HalfSpace

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

open SobolevMultiIndex

/-- **The principal part of the general form against a test-function element, in terms of
functions**: for coefficients `A_{kℓ}` with representatives `a_{kℓ}` and an element `Φ` whose
function is the test function `ψ`, `a(U, Φ) = ∑_{kℓ} ∫_Ω a_{kℓ} ∂_k U ∂_ℓ ψ`. -/
theorem generalForm_zero_zero_apply_eq_of_ae_eq
    {A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    {a : Fin N → Fin N → EuclideanSpace ℝ (Fin N) → ℝ}
    (hAa : ∀ k l, ⇑(A k l) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] a k l)
    (U : SobolevEuclidean N 1 2 Ω) {Φ : SobolevEuclidean N 1 2 Ω} {ψ : 𝓓(Ω, ℝ)}
    (hΦ : fn Φ =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ψ) :
    generalForm Ω A 0 0 U Φ = ∑ k, ∑ l, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      a k l x * weakDeriv U (MultiIndexLE.single k) x
        * fderiv ℝ ψ x (EuclideanSpace.single l 1) := by
  rw [generalForm_zero_zero_apply]
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
  rw [inner_mulL_eq_integral]
  have hΦl := weakDeriv_single_ae_eq_fderiv_of_contDiffOn Ω
    (ψ.contDiff.contDiffOn.of_le (by simp)) hΦ l
  refine integral_congr_ae ?_
  filter_upwards [hAa k l, hΦl] with x h1 h2
  rw [h1, h2]

/-- **From the typed form to the predicate form of a weak solution of the general equation**: if
`a(U, Φ) = ∫_Ω g Φ` for every `Φ` of a subspace containing the test-function elements, then
`∑_{kℓ} ∫_Ω a_{kℓ} ∂_k U ∂_ℓ ψ = ∫_Ω g ψ` for every test function `ψ`. -/
theorem forall_testFunction_of_forall_mem_general
    {A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    {a : Fin N → Fin N → EuclideanSpace ℝ (Fin N) → ℝ}
    (hAa : ∀ k l, ⇑(A k l) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] a k l)
    {K : Submodule ℝ (SobolevEuclidean N 1 2 Ω)}
    (hK : testFunctions ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume ≤ K)
    {U : SobolevEuclidean N 1 2 Ω}
    {g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ Φ ∈ K, generalForm Ω A 0 0 U Φ = load Ω g Φ) (ψ : 𝓓(Ω, ℝ)) :
    ∑ k, ∑ l, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      a k l x * weakDeriv U (MultiIndexLE.single k) x * fderiv ℝ ψ x (EuclideanSpace.single l 1)
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), g x * ψ x := by
  obtain ⟨Φ, hΦ, hΦψ⟩ := ψ.exists_mem_sobolevMultiIndex_testFunctions
    (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis) (k := 1) (p := 2) (μ := volume)
  rw [← generalForm_zero_zero_apply_eq_of_ae_eq hAa U hΦψ,
    ← load_apply_eq_of_ae_eq (EventuallyEq.refl _ _) hΦψ]
  exact heq Φ (hK hΦ)

end HalfSpace

section HalfSpaceTangential

variable {d : ℕ}

open SobolevMultiIndex EuclideanSpace

/-- The tangential coordinate vectors of the half space: `e_k` for `k ≠ N`. -/
theorem single_apply_last_eq_zero {k : Fin (d + 1)} (hk : k ≠ Fin.last d) :
    (EuclideanSpace.single k (1 : ℝ)) (Fin.last d) = 0 := by
  simp [hk.symm]

/-- **Second derivatives of a weak solution, all but `∂_N∂_N`, on an open set invariant under
the tangential translations** ([brezis2011functional] §9.6, (55)–(56) and (66)–(67), the half
space being the case in point): for `u ∈ H^1_0(Ω)` solving `a(u, ψ) = ∫ g ψ` for all
`ψ ∈ H^1_0(Ω)`, with `C¹` elliptic coefficients, every partial derivative `∂_k u` has a weak
derivative along `e_ℓ` in `L²(Ω)` for `(k, ℓ) ≠ (N, N)`, bounded by `α⁻¹ (‖g‖ + N² M ‖∇u‖)`. For
tangential `ℓ` this is the tangential estimate along `e_ℓ`; for `ℓ = N` and tangential `k` it is
the derivative `∂_k ∂_N u`, which is `∂_N ∂_k u` by the symmetry of weak derivatives
(`HasWeakIteratedLineDerivOn.of_perm`). -/
theorem exists_hasWeakIteratedLineDerivOn_weakDeriv_of_tangential
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : ∀ j : Fin (d + 1), j ≠ Fin.last d → ∀ t : ℝ,
      IsTranslationInvariant (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))
        (t • EuclideanSpace.single j 1))
    {A : Fin (d + 1) → Fin (d + 1) →
      Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    {a : Fin (d + 1) → Fin (d + 1) → EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hAa : ∀ k l, ⇑(A k l) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] a k l)
    (ha : ∀ k l, ContDiffOn ℝ 1 (a k l) Ω) {M : ℝ} (hM0 : 0 ≤ M)
    (haM : ∀ k l, ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), ‖fderiv ℝ (a k l) x‖ ≤ M)
    {α : ℝ} (hA : IsUniformlyElliptic Ω A α) {u : SobolevEuclidean (d + 1) 1 2 Ω}
    (hu : u ∈ SobolevEuclideanZero (d + 1) 1 2 Ω)
    {g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    (heq : ∀ ψ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω, generalForm Ω A 0 0 u ψ = load Ω g ψ)
    (k l : Fin (d + 1)) (hkl : k ≠ Fin.last d ∨ l ≠ Fin.last d) :
    ∃ w : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      ‖w‖ ≤ α⁻¹ * (‖g‖ + (d + 1) ^ 2 * M * gradNorm u) ∧
        HasWeakIteratedLineDerivOn ![EuclideanSpace.single l 1]
          (weakDeriv u (MultiIndexLE.single k)) w Ω volume := by
  have hK : ∀ ⦃h : EuclideanSpace ℝ (Fin (d + 1))⦄
      (hh : IsTranslationInvariant (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) h),
      ∀ v ∈ SobolevEuclideanZero (d + 1) 1 2 Ω,
        translateL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 volume hh v
          ∈ SobolevEuclideanZero (d + 1) 1 2 Ω :=
    fun _ hh _ hv ↦ translateL_mem_zero hh hv
  have hsec : ∀ (j : Fin (d + 1)), j ≠ Fin.last d → ∀ i,
      ∃ w : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
        ‖w‖ ≤ α⁻¹ * (‖g‖ + (d + 1) ^ 2 * M * gradNorm u) ∧
          HasWeakIteratedLineDerivOn ![EuclideanSpace.single j 1]
            (weakDeriv u (MultiIndexLE.single i)) w Ω volume := by
    intro j hj i
    obtain ⟨w, hw, hwd⟩ := exists_hasWeakIteratedLineDerivOn_weakDeriv_of_invariant
      (y := EuclideanSpace.single j 1) (by simp) (hΩ j hj) hK hAa ha hM0 haM hA hu heq i
    refine ⟨w, ?_, hwd⟩
    simpa using hw
  rcases eq_or_ne l (Fin.last d) with rfl | hl
  · -- `ℓ = N`, so `k ≠ N`: the derivative `∂_k ∂_N u` is `∂_N ∂_k u`
    have hk : k ≠ Fin.last d := hkl.resolve_right (fun h ↦ h rfl)
    obtain ⟨w, hw, hwd⟩ := hsec k hk (Fin.last d)
    refine ⟨w, hw, ?_⟩
    have h1 : HasWeakIteratedLineDerivOn ![EuclideanSpace.single k 1] (fn u)
        (weakDeriv u (MultiIndexLE.single k)) Ω volume := by
      have := (hasWeakIteratedLineDerivOn u (MultiIndexLE.single k)).of_perm
        (multiIndexTuple_single_perm ((EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis :
          Fin (d + 1) → EuclideanSpace ℝ (Fin (d + 1))) k)
      rwa [EuclideanSpace.basisFun_toBasis_apply] at this
    have h2 : HasWeakIteratedLineDerivOn ![EuclideanSpace.single (Fin.last d) 1] (fn u)
        (weakDeriv u (MultiIndexLE.single (Fin.last d))) Ω volume := by
      have := (hasWeakIteratedLineDerivOn u (MultiIndexLE.single (Fin.last d))).of_perm
        (multiIndexTuple_single_perm ((EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis :
          Fin (d + 1) → EuclideanSpace ℝ (Fin (d + 1))) (Fin.last d))
      rwa [EuclideanSpace.basisFun_toBasis_apply] at this
    have h3 := h2.cons hwd
    have h4 : HasWeakIteratedLineDerivOn
        (Fin.cons (EuclideanSpace.single (Fin.last d) 1) ![EuclideanSpace.single k 1]) (fn u) w
        Ω volume := by
      refine h3.of_perm ?_
      simp only [List.ofFn_cons]
      exact List.Perm.swap _ _ _
    exact h1.of_cons h4
  · obtain ⟨w, hw, hwd⟩ := hsec l hl k
    exact ⟨w, hw, hwd⟩

end HalfSpaceTangential


/-! ### Case B: `H²` regularity on a tangentially invariant open set -/

section TangentialRegularity

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

open SobolevMultiIndex

/-- The pointwise ellipticity condition on continuous representatives gives the almost
everywhere condition `IsUniformlyElliptic` on the `L^∞` classes. -/
theorem isUniformlyElliptic_of_forall
    {A : Fin (d + 1) → Fin (d + 1) →
      Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    {a : Fin (d + 1) → Fin (d + 1) → EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hAa : ∀ k l, ⇑(A k l) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] a k l)
    {α : ℝ} (hα0 : 0 < α)
    (hell : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), ∀ ξ : EuclideanSpace ℝ (Fin (d + 1)),
      α * ‖ξ‖ ^ 2 ≤ ∑ k, ∑ l, a k l x * ξ k * ξ l) :
    IsUniformlyElliptic Ω A α := by
  refine ⟨hα0, ?_⟩
  have h : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      ∀ k l, A k l x = a k l x := ae_all_iff.2 fun k ↦ ae_all_iff.2 fun l ↦ hAa k l
  filter_upwards [h, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ ξ
  simp only [hx]
  exact hell x hxΩ ξ

/-- The diagonal coefficient `a_{NN}` of an elliptic matrix is at least `α`. -/
theorem le_diag_of_forall_elliptic
    {a : Fin (d + 1) → Fin (d + 1) → EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    {α : ℝ} (hell : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      ∀ ξ : EuclideanSpace ℝ (Fin (d + 1)), α * ‖ξ‖ ^ 2 ≤ ∑ k, ∑ l, a k l x * ξ k * ξ l)
    {x : EuclideanSpace ℝ (Fin (d + 1))} (hx : x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (i : Fin (d + 1)) : α ≤ a i i x := by
  have := hell x hx (EuclideanSpace.single i 1)
  simpa [PiLp.norm_single, Finset.sum_ite_eq'] using this

/-- The constant of the `H²` estimate on a tangentially invariant open set, in terms of the
dimension `d + 1`, the ellipticity constant `α`, the bound `M₀` on the coefficients and the bound
`M` on their gradients. -/
def regularityConst (d : ℕ) (α M₀ M : ℝ) : ℝ :=
  √(Fintype.card (MultiIndexLE (Fin (d + 1)) 2)) * (1 + max (α⁻¹ * (1 + (d + 1) ^ 2 * M))
    (α⁻¹ * (1 + M + (d + 1) ^ 2 * (M + M₀ * (α⁻¹ * (1 + (d + 1) ^ 2 * M))))))

/-- The arithmetic of the normal-normal bound: with `C₁ = α⁻¹ (1 + N² M)`,
`α⁻¹ (M a₀ + b + ∑_{kℓ} (M a_k + M₀ c_{kℓ})) ≤ α⁻¹ (1 + M + N² (M + M₀ C₁)) (‖u‖ + ‖g‖)` when
`a_k ≤ ‖u‖`, `b = ‖g‖` and `c_{kℓ} ≤ C₁ (‖u‖ + ‖g‖)`. -/
theorem normal_bound_le {α M₀ M nu ng : ℝ} (hα : 0 < α) (hM₀ : 0 ≤ M₀) (hM : 0 ≤ M) (hnu : 0 ≤ nu)
    (hng : 0 ≤ ng) {a : Fin (d + 1) → ℝ} {c : Fin (d + 1) → Fin (d + 1) → ℝ} (i₀ : Fin (d + 1))
    (ha : ∀ k, a k ≤ nu) (hc : ∀ k l, c k l ≤ α⁻¹ * (1 + (d + 1) ^ 2 * M) * (nu + ng)) :
    α⁻¹ * (M * a i₀ + ng + ∑ k, ∑ l, (M * a k + M₀ * c k l))
      ≤ α⁻¹ * (1 + M + (d + 1) ^ 2 * (M + M₀ * (α⁻¹ * (1 + (d + 1) ^ 2 * M)))) * (nu + ng) := by
  have hsum : ∑ k, ∑ l, (M * a k + M₀ * c k l)
      ≤ (d + 1) ^ 2 * (M * nu + M₀ * (α⁻¹ * (1 + (d + 1) ^ 2 * M) * (nu + ng))) := by
    calc ∑ k, ∑ l, (M * a k + M₀ * c k l)
        ≤ ∑ _k : Fin (d + 1), ∑ _l : Fin (d + 1),
          (M * nu + M₀ * (α⁻¹ * (1 + (d + 1) ^ 2 * M) * (nu + ng))) := by
          refine Finset.sum_le_sum fun k _ ↦ Finset.sum_le_sum fun l _ ↦ ?_
          exact add_le_add (mul_le_mul_of_nonneg_left (ha k) hM)
            (mul_le_mul_of_nonneg_left (hc k l) hM₀)
      _ = (d + 1) ^ 2 * (M * nu + M₀ * (α⁻¹ * (1 + (d + 1) ^ 2 * M) * (nu + ng))) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  have h1 : M * a i₀ ≤ M * nu := mul_le_mul_of_nonneg_left (ha i₀) hM
  have hαi : 0 ≤ α⁻¹ := inv_nonneg.2 hα.le
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hαi
  have hC₁ : 0 ≤ α⁻¹ * (1 + (d + 1) ^ 2 * M) := by positivity
  nlinarith [hsum, h1, mul_nonneg hM hng, mul_nonneg (mul_nonneg hM₀ hC₁) hnu,
    mul_nonneg (mul_nonneg hM₀ hC₁) hng, mul_nonneg hM hnu, sq_nonneg ((d : ℝ) + 1)]

/-- **`H²` regularity on an open set invariant under the tangential translations, for a
variable-coefficient elliptic form** — [brezis2011functional] Theorem 9.25, case B
(`Ω = ℝ^N_+`), in the generality of the estimates (63)–(69) of case C₂. Let `Ω ⊆ ℝ^N` be open
and invariant under the translations `t e_j`, `j ≠ N`, let the coefficients `A_{kℓ} ∈ L^∞(Ω)`
have `C¹` representatives `a_{kℓ}` on `Ω` with `|a_{kℓ}| ≤ M₀`, `‖∇a_{kℓ}‖ ≤ M`, elliptic with
constant `α > 0` at every point of `Ω`, and let `u ∈ H^1_0(Ω)` satisfy
`∑_{kℓ} ∫_Ω a_{kℓ} ∂_k u ∂_ℓ ψ = ∫_Ω g ψ` for all `ψ ∈ H^1_0(Ω)`. Then `u` is the function of an
element `U ∈ H²(Ω)` with `‖U‖_{H²} ≤ C (‖u‖_{H¹} + ‖g‖₂)`, `C = regularityConst d α M₀ M`.

The tangential second derivatives come from the method of translations
(`Elliptic.exists_hasWeakIteratedLineDerivOn_weakDeriv_of_tangential`), the normal-normal one
from the equation (`Elliptic.exists_hasWeakIteratedLineDerivOn_last_of_forall`), and
`SobolevMultiIndex.exists_two_of_forall_exists` assembles them. -/
theorem exists_sobolevEuclidean_two_of_tangential
    (hΩ : ∀ j : Fin (d + 1), j ≠ Fin.last d → ∀ t : ℝ,
      IsTranslationInvariant (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))
        (t • EuclideanSpace.single j 1))
    {A : Fin (d + 1) → Fin (d + 1) →
      Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    {a : Fin (d + 1) → Fin (d + 1) → EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hAa : ∀ k l, ⇑(A k l) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] a k l)
    (ha : ∀ k l, ContDiffOn ℝ 1 (a k l) Ω) {M₀ M α : ℝ} (hM₀0 : 0 ≤ M₀) (hM0 : 0 ≤ M)
    (haM₀ : ∀ k l, ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), |a k l x| ≤ M₀)
    (haM : ∀ k l, ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), ‖fderiv ℝ (a k l) x‖ ≤ M)
    (hα0 : 0 < α)
    (hell : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), ∀ ξ : EuclideanSpace ℝ (Fin (d + 1)),
      α * ‖ξ‖ ^ 2 ≤ ∑ k, ∑ l, a k l x * ξ k * ξ l)
    {u : SobolevEuclidean (d + 1) 1 2 Ω} (hu : u ∈ SobolevEuclideanZero (d + 1) 1 2 Ω)
    {g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    (heq : ∀ ψ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω, generalForm Ω A 0 0 u ψ = load Ω g ψ) :
    ∃ U : SobolevEuclidean (d + 1) 2 2 Ω,
      fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] fn u ∧
      ‖U‖ ≤ regularityConst d α M₀ M * (‖u‖ + ‖g‖) := by
  have hΩm : MeasurableSet (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) := Ω.isOpen.measurableSet
  have hA : IsUniformlyElliptic Ω A α := isUniformlyElliptic_of_forall hAa hα0 hell
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = α⁻¹ * (1 + (d + 1) ^ 2 * M) := ⟨_, rfl⟩
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  -- the tangential bound in terms of `‖u‖ + ‖g‖`
  have hbnd : α⁻¹ * (‖g‖ + (d + 1) ^ 2 * M * gradNorm u) ≤ C₁ * (‖u‖ + ‖g‖) := by
    rw [hC₁]
    have := gradNorm_le_norm u
    have h1 : 0 ≤ (d + 1 : ℝ) ^ 2 * M := by positivity
    have h2 : (d + 1 : ℝ) ^ 2 * M * gradNorm u ≤ (d + 1) ^ 2 * M * ‖u‖ :=
      mul_le_mul_of_nonneg_left this h1
    have h3 : 0 ≤ α⁻¹ := inv_nonneg.2 hα0.le
    nlinarith [norm_nonneg g, norm_nonneg u, mul_nonneg h1 (norm_nonneg g)]
  -- the second derivatives other than `∂_N ∂_N`
  have hsec := exists_hasWeakIteratedLineDerivOn_weakDeriv_of_tangential hΩ hAa ha hM0 haM hA hu heq
  choose V hVb hVd using hsec
  classical
  obtain ⟨V', hV'⟩ : ∃ V' : Fin (d + 1) → Fin (d + 1) →
      Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      V' = fun k l ↦ if h : k ≠ Fin.last d ∨ l ≠ Fin.last d then V k l h else 0 := ⟨_, rfl⟩
  have hV'b : ∀ k l, ‖V' k l‖ ≤ C₁ * (‖u‖ + ‖g‖) := fun k l ↦ by
    rw [hV']
    dsimp only
    split_ifs with h
    · exact (hVb k l h).trans hbnd
    · rw [norm_zero]; positivity
  have hV'd : ∀ k l, (k ≠ Fin.last d ∨ l ≠ Fin.last d) →
      HasWeakIteratedLineDerivOn ![EuclideanSpace.single l 1] (weakDeriv u (MultiIndexLE.single k))
        (V' k l) Ω volume := fun k l h ↦ by
    rw [hV']
    dsimp only
    rw [dite_eq_left h]
    exact hVd k l h
  -- the predicate form of the equation, and the normal-normal derivative
  have hpred := forall_testFunction_of_forall_mem_general hAa
    (SobolevMultiIndexZero.testFunctions_le) heq
  obtain ⟨vNN, hvNN, hvNNp, hvNNb⟩ := exists_hasWeakIteratedLineDerivOn_last_of_forall ha haM₀ haM
    hα0 (fun x hx ↦ le_diag_of_forall_elliptic hell hx _)
    (w := fun k ↦ ⇑(weakDeriv u (MultiIndexLE.single k))) (fun k ↦ Lp.memLp _) (Lp.memLp g)
    (v := fun k l ↦ ⇑(V' k l)) hV'd (fun k l ↦ Lp.memLp _) hpred
  have hWNN : ‖hvNNp.toLp vNN‖ ≤ α⁻¹ * (1 + M + (d + 1) ^ 2 * (M + M₀ * C₁)) * (‖u‖ + ‖g‖) := by
    refine (norm_toLp_le_of_ae_abs_le (inv_nonneg.2 hα0.le) hM0 hM₀0 (Fin.last d) hvNNp g
      (EventuallyEq.refl _ _) (fun k ↦ weakDeriv u (MultiIndexLE.single k))
      (fun k ↦ EventuallyEq.refl _ _) V' (fun k l ↦ EventuallyEq.refl _ _)
      ((ae_restrict_mem hΩm).mono fun x hx ↦ hvNNb x hx)).trans ?_
    rw [hC₁]
    exact normal_bound_le hα0 hM₀0 hM0 (norm_nonneg u) (norm_nonneg g) (Fin.last d)
      (fun k ↦ norm_weakDeriv_le u _) (fun k l ↦ hC₁ ▸ hV'b k l)
  -- assembly
  obtain ⟨C₂, hC₂⟩ : ∃ C₂ : ℝ, C₂ = α⁻¹ * (1 + M + (d + 1) ^ 2 * (M + M₀ * C₁)) := ⟨_, rfl⟩
  rw [← hC₂] at hWNN
  obtain ⟨U, hU, hU2, hU1⟩ := exists_two_of_forall_exists u (C := max C₁ C₂ * (‖u‖ + ‖g‖))
    fun i j ↦ by
      by_cases hij : j ≠ Fin.last d ∨ i ≠ Fin.last d
      · refine ⟨V' j i, (hV'b j i).trans ?_, ?_⟩
        · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        · rw [EuclideanSpace.basisFun_toBasis_apply]
          exact hV'd j i hij
      · push Not at hij
        obtain ⟨rfl, rfl⟩ := hij
        refine ⟨hvNNp.toLp vNN, hWNN.trans ?_, ?_⟩
        · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
        · rw [EuclideanSpace.basisFun_toBasis_apply]
          exact hvNN.congr_ae (EventuallyEq.refl _ _) hvNNp.coeFn_toLp.symm
  refine ⟨U, hU, ?_⟩
  have hnorm : ‖U‖ ≤ √(Fintype.card (MultiIndexLE (Fin (d + 1)) 2))
      * (‖u‖ + max C₁ C₂ * (‖u‖ + ‖g‖)) := by
    refine norm_le_sqrt_card_mul_of_forall_norm_weakDeriv_le U fun β ↦ ?_
    rcases Nat.lt_or_ge (∑ i, β.1 i) 2 with hlt | hge
    · exact (hU1 β (Nat.lt_succ_iff.1 hlt)).trans (le_add_of_nonneg_right (by positivity))
    · exact (hU2 β (le_antisymm β.2 hge)).trans (le_add_of_nonneg_left (norm_nonneg _))
  refine hnorm.trans ?_
  rw [regularityConst, ← hC₁, ← hC₂, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  nlinarith [norm_nonneg u, norm_nonneg g, le_max_left C₁ C₂, hC₁0]

end TangentialRegularity


/-! ### Case B: the half space -/

section UpperHalfSpace

variable {d : ℕ}

open SobolevMultiIndex EuclideanSpace

/-- The half space is invariant under the tangential coordinate translations. -/
theorem upperHalfSpaceOpens_isTranslationInvariant (j : Fin (d + 1)) (hj : j ≠ Fin.last d)
    (t : ℝ) :
    IsTranslationInvariant ((upperHalfSpaceOpens d : Opens (EuclideanSpace ℝ (Fin (d + 1)))) :
        Set (EuclideanSpace ℝ (Fin (d + 1))))
      (t • EuclideanSpace.single j (1 : ℝ)) :=
  isTranslationInvariant_upperHalfSpace (single_apply_last_eq_zero hj) t

/-- **Theorem 9.25, case B (`Ω = ℝ^N_+`), for a variable-coefficient elliptic form**
([brezis2011functional] §9.6, case B, in the generality of case C₂'s estimates): let the
coefficients `A_{kℓ} ∈ L^∞(ℝ^N_+)` have `C¹` representatives `a_{kℓ}` with `|a_{kℓ}| ≤ M₀`,
`‖∇a_{kℓ}‖ ≤ M`, elliptic with constant `α > 0`, and let `u ∈ H^1_0(ℝ^N_+)` satisfy
`∑_{kℓ} ∫ a_{kℓ} ∂_k u ∂_ℓ ψ = ∫ g ψ` for all `ψ ∈ H^1_0(ℝ^N_+)`. Then `u` is the function of an
element `U ∈ H²(ℝ^N_+)` with `‖U‖_{H²} ≤ C (‖u‖_{H¹} + ‖g‖₂)`, `C = regularityConst d α M₀ M`. -/
theorem regularity_upperHalfSpace_general
    {A : Fin (d + 1) → Fin (d + 1) → Lp ℝ ⊤ (volume.restrict
      ((upperHalfSpaceOpens d : Opens (EuclideanSpace ℝ (Fin (d + 1)))) :
        Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    {a : Fin (d + 1) → Fin (d + 1) → EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hAa : ∀ k l, ⇑(A k l) =ᵐ[volume.restrict
      ((upperHalfSpaceOpens d : Opens (EuclideanSpace ℝ (Fin (d + 1)))) :
        Set (EuclideanSpace ℝ (Fin (d + 1))))] a k l)
    (ha : ∀ k l, ContDiffOn ℝ 1 (a k l) (upperHalfSpaceOpens d)) {M₀ M α : ℝ} (hM₀0 : 0 ≤ M₀)
    (hM0 : 0 ≤ M)
    (haM₀ : ∀ k l, ∀ x ∈ ((upperHalfSpaceOpens d : Opens (EuclideanSpace ℝ (Fin (d + 1)))) :
        Set (EuclideanSpace ℝ (Fin (d + 1)))),
      |a k l x| ≤ M₀)
    (haM : ∀ k l, ∀ x ∈ ((upperHalfSpaceOpens d : Opens (EuclideanSpace ℝ (Fin (d + 1)))) :
        Set (EuclideanSpace ℝ (Fin (d + 1)))),
      ‖fderiv ℝ (a k l) x‖ ≤ M)
    (hα0 : 0 < α)
    (hell : ∀ x ∈ ((upperHalfSpaceOpens d : Opens (EuclideanSpace ℝ (Fin (d + 1)))) :
        Set (EuclideanSpace ℝ (Fin (d + 1)))),
      ∀ ξ : EuclideanSpace ℝ (Fin (d + 1)), α * ‖ξ‖ ^ 2 ≤ ∑ k, ∑ l, a k l x * ξ k * ξ l)
    {u : SobolevEuclidean (d + 1) 1 2 (upperHalfSpaceOpens d)}
    (hu : u ∈ SobolevEuclideanZero (d + 1) 1 2 (upperHalfSpaceOpens d))
    {g : Lp ℝ 2 (volume.restrict
      ((upperHalfSpaceOpens d : Opens (EuclideanSpace ℝ (Fin (d + 1)))) :
        Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    (heq : ∀ ψ ∈ SobolevEuclideanZero (d + 1) 1 2 (upperHalfSpaceOpens d),
      generalForm (upperHalfSpaceOpens d) A 0 0 u ψ = load (upperHalfSpaceOpens d) g ψ) :
    ∃ U : SobolevEuclidean (d + 1) 2 2 (upperHalfSpaceOpens d),
      fn U =ᵐ[volume.restrict
        ((upperHalfSpaceOpens d : Opens (EuclideanSpace ℝ (Fin (d + 1)))) :
        Set (EuclideanSpace ℝ (Fin (d + 1))))] fn u ∧
      ‖U‖ ≤ regularityConst d α M₀ M * (‖u‖ + ‖g‖) :=
  exists_sobolevEuclidean_two_of_tangential upperHalfSpaceOpens_isTranslationInvariant hAa ha hM₀0
    hM0 haM₀ haM hα0 hell hu heq

/-- The constant representatives `δ_{kℓ}` of the identity coefficients are bounded by `1`. -/
theorem abs_kroneckerRep_le_one (k l : Fin (d + 1)) (x : EuclideanSpace ℝ (Fin (d + 1))) :
    |(fun _ : EuclideanSpace ℝ (Fin (d + 1)) ↦ if k = l then (1 : ℝ) else 0) x| ≤ 1 := by
  split_ifs <;> simp

/-- The identity coefficients are elliptic with constant `1`, pointwise. -/
theorem one_mul_norm_sq_le_sum_kroneckerRep (x ξ : EuclideanSpace ℝ (Fin (d + 1))) :
    (1 : ℝ) * ‖ξ‖ ^ 2 ≤ ∑ k, ∑ l,
      (fun _ : EuclideanSpace ℝ (Fin (d + 1)) ↦ if k = l then (1 : ℝ) else 0) x * ξ k * ξ l := by
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    EuclideanSpace.real_norm_sq_eq]
  exact le_of_eq (Finset.sum_congr rfl fun i _ ↦ by ring)

/-- **Theorem 9.25, case B (`Ω = ℝ^N_+`), `H²` regularity** ([brezis2011functional] §9.6,
case B): let `u ∈ H^1_0(ℝ^N_+)`, `g ∈ L²(ℝ^N_+)`, and `∫ ∇u · ∇ψ = ∫ g ψ` for every
`ψ ∈ H^1_0(ℝ^N_+)`. Then `u` is the function of an element `U ∈ H²(ℝ^N_+)`, with
`‖U‖_{H²} ≤ C_N (‖u‖_{H¹} + ‖g‖₂)`, `C_N = regularityConst d 1 1 0`. The book's equation
`−Δu + u = f` is the case `g = f − u`. The Dirichlet form is the general form with the identity
coefficients (`Elliptic.generalForm_kroneckerCoeff`), so this is
`Elliptic.regularity_upperHalfSpace_general` with `α = 1`, `M₀ = 1`, `M = 0`. -/
theorem regularity_upperHalfSpace {u : SobolevEuclidean (d + 1) 1 2 (upperHalfSpaceOpens d)}
    {g : Lp ℝ 2 (volume.restrict
      ((upperHalfSpaceOpens d : Opens (EuclideanSpace ℝ (Fin (d + 1)))) :
        Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    (hu : IsGalerkinSolution (dirichletForm (upperHalfSpaceOpens d))
      (load (upperHalfSpaceOpens d) g)
      (SobolevEuclideanZero (d + 1) 1 2 (upperHalfSpaceOpens d)) u) :
    ∃ U : SobolevEuclidean (d + 1) 2 2 (upperHalfSpaceOpens d),
      fn U =ᵐ[volume.restrict
        ((upperHalfSpaceOpens d : Opens (EuclideanSpace ℝ (Fin (d + 1)))) :
        Set (EuclideanSpace ℝ (Fin (d + 1))))] fn u ∧
      ‖U‖ ≤ regularityConst d 1 1 0 * (‖u‖ + ‖g‖) := by
  refine regularity_upperHalfSpace_general (A := kroneckerCoeff (upperHalfSpaceOpens d))
    (a := fun k l _ ↦ if k = l then (1 : ℝ) else 0) (coeFn_kroneckerCoeff _)
    (fun k l ↦ contDiffOn_const)
    zero_le_one le_rfl (fun k l x _ ↦ abs_kroneckerRep_le_one k l x)
    (fun k l x _ ↦ by simp) one_pos (fun x _ ξ ↦ one_mul_norm_sq_le_sum_kroneckerRep x ξ) hu.1
    fun ψ hψ ↦ ?_
  rw [generalForm_kroneckerCoeff]
  exact hu.2 ψ hψ

end UpperHalfSpace


/-! ### Differentiating the equation -/

section Differentiate

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **Differentiating the weak equation** ([brezis2011functional] §9.6, "if `φ ∈ C_c^∞` we may
replace `φ` by `Dφ` in (48)"): let `w i` be weak derivatives of `u` along `eᵢ` on `Ω`, `v i j`
weak derivatives of `w j` along `eᵢ`, `g j` a weak derivative of `f` along `e_j`, and
`∑ᵢ ∫_Ω wᵢ ∂ᵢφ = ∫_Ω f φ` for every test function `φ`. Then `∂_j u = w j` solves the equation
with datum `∂_j f = g j`: `∑ᵢ ∫_Ω v i j ∂ᵢφ = ∫_Ω g j φ` for every test function `φ`. The
derivatives `∂ᵢ∂_j u` and `∂_j∂ᵢu` agree (`HasWeakIteratedLineDerivOn.of_perm`), and the equation
is tested with `∂_jφ`. -/
theorem forall_testFunction_deriv {u f : EuclideanSpace ℝ (Fin N) → ℝ}
    {w g : Fin N → EuclideanSpace ℝ (Fin N) → ℝ} {v : Fin N → Fin N → EuclideanSpace ℝ (Fin N) → ℝ}
    (hw : ∀ i, HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1] u (w i) Ω volume)
    (hv : ∀ i j, HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1] (w j) (v i j) Ω volume)
    (hg : ∀ j, HasWeakIteratedLineDerivOn ![EuclideanSpace.single j 1] f (g j) Ω volume)
    (heq : ∀ φ : 𝓓(Ω, ℝ), ∑ i, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      w i x * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), f x * φ x)
    (j : Fin N) (φ : 𝓓(Ω, ℝ)) :
    ∑ i, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      v i j x * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), g j x * φ x := by
  have hΩm : MeasurableSet (Ω : Set (EuclideanSpace ℝ (Fin N))) := Ω.isOpen.measurableSet
  -- `v i j` is a weak derivative of `w i` along `e_j`
  have hvij : ∀ i,
      HasWeakIteratedLineDerivOn ![EuclideanSpace.single j 1] (w i) (v i j) Ω volume := by
    intro i
    have h1 := (hw j).cons (hv i j)
    have h2 : HasWeakIteratedLineDerivOn
        (Fin.cons (EuclideanSpace.single j 1) ![EuclideanSpace.single i 1]) u (v i j) Ω volume := by
      refine h1.of_perm ?_
      simp only [List.ofFn_cons]
      exact List.Perm.swap _ _ _
    exact (hw i).of_cons h2
  -- each term, integrated by parts against `∂ᵢφ`, then the symmetry of `∂_j∂ᵢφ`
  have hterm : ∀ i, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      v i j x * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = -∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        w i x * fderiv ℝ (φ.fderivApply (EuclideanSpace.single j 1)) x
          (EuclideanSpace.single i 1) := by
    intro i
    have key := (hvij i).integral_fderiv_mul_eq_of_eqOn (φ.fderivApply (EuclideanSpace.single i 1))
      (fun _ _ ↦ rfl)
    have hsym : ∀ x, fderiv ℝ (fun z ↦ fderiv ℝ φ z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single j 1)
        = fderiv ℝ (fun z ↦ fderiv ℝ φ z (EuclideanSpace.single j 1)) x
          (EuclideanSpace.single i 1) := fun x ↦
      congrFun (φ.contDiff.fderiv_fderiv_comm (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1)) x
    simp only [TestFunction.fderivApply_coe] at key ⊢
    have e1 : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        fderiv ℝ (fun z ↦ fderiv ℝ φ z (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1)
          * w i x
        = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          w i x * fderiv ℝ (fun z ↦ fderiv ℝ φ z (EuclideanSpace.single j 1)) x
            (EuclideanSpace.single i 1) :=
      integral_congr_ae (Eventually.of_forall fun x ↦ by dsimp only; rw [hsym x, mul_comm])
    have e2 : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        fderiv ℝ φ x (EuclideanSpace.single i 1) * v i j x
        = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          v i j x * fderiv ℝ φ x (EuclideanSpace.single i 1) :=
      integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
    rw [e1, e2] at key
    linarith
  simp_rw [hterm]
  rw [Finset.sum_neg_distrib, heq (φ.fderivApply (EuclideanSpace.single j 1))]
  have key := (hg j).integral_fderiv_mul_eq_of_eqOn φ (fun _ _ ↦ rfl)
  simp only [TestFunction.fderivApply_coe]
  have e3 : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      fderiv ℝ φ x (EuclideanSpace.single j 1) * f x
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          f x * fderiv ℝ φ x (EuclideanSpace.single j 1) :=
    integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
  have e4 : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), φ x * g j x
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), g j x * φ x :=
    integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
  rw [e3, e4] at key
  linarith

end Differentiate

/-! ### Case A, higher order -/

section WholeSpaceHigher

variable {N : ℕ}

open SobolevMultiIndex

/-- **Theorem 9.25, case A, higher order, as a membership** ([brezis2011functional] §9.6, case A:
"`f ∈ H^m ⇒ u ∈ H^{m+2}`, by induction on `m`"): let `u ∈ H^1(ℝ^N)`, `G ∈ L²(ℝ^N)` with
`G ∈ H^m(ℝ^N)`, and `∫ ∇u · ∇φ = ∫ G φ` for every `φ ∈ H^1(ℝ^N)`. Then `u ∈ H^{m+2}(ℝ^N)`.

The induction differentiates the equation (`Elliptic.forall_testFunction_deriv`): each `∂_j u`,
an element of `H^1(ℝ^N)` by the case `m = 0`, solves it with datum `∂_j G ∈ H^m(ℝ^N)` against the
test functions, hence against all of `H^1(ℝ^N)` by density
(`Elliptic.dirichletForm_eq_load_of_forall_testFunctions` with `SobolevEuclideanZero.eq_top`), so
`∂_j u ∈ H^{m+2}(ℝ^N)` by the inductive hypothesis, and `memSobolevMultiIndex_succ_iff` assembles
`u ∈ H^{m+3}(ℝ^N)`. -/
theorem regularity_top_higher (m : ℕ) : ∀ (u : SobolevEuclidean N 1 2 ⊤)
    (G : Lp ℝ 2 (volume.restrict
      ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) : Set (EuclideanSpace ℝ (Fin N))))),
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (⇑G) m 2 ⊤ volume →
    (∀ φ, dirichletForm (⊤ : Opens (EuclideanSpace ℝ (Fin N))) u φ
      = load (⊤ : Opens (EuclideanSpace ℝ (Fin N))) G φ) →
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (fn u) (m + 2) 2 ⊤ volume := by
  induction m with
  | zero => exact fun u G _ heq ↦ regularity_top_memSobolevMultiIndex heq
  | succ m ih =>
    intro u G hG heq
    have h2 : (2 : ℝ≥0∞) ≠ ⊤ := ENNReal.ofNat_ne_top
    -- `u ∈ H²`, with its first derivatives `w j ∈ H¹` and second derivatives `v i j`
    have hu2 := regularity_top_memSobolevMultiIndex heq
    obtain ⟨-, hw⟩ := memSobolevMultiIndex_succ_iff.1 hu2
    choose w hw hw1 using hw
    simp only [EuclideanSpace.basisFun_toBasis_apply] at hw
    have hv : ∀ j, ∀ i, ∃ v, HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1] (w j) v ⊤
        volume ∧ MemLp v 2 (volume.restrict
          ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) : Set (EuclideanSpace ℝ (Fin N)))) := by
      intro j i
      obtain ⟨v, hv, hvp⟩ := (memSobolevMultiIndex_one_iff.1 (hw1 j)).2 i
      rw [EuclideanSpace.basisFun_toBasis_apply] at hv
      exact ⟨v, hv, hvp⟩
    choose v hv hvp using hv
    -- the derivatives of `G`
    obtain ⟨hGm, hg⟩ := memSobolevMultiIndex_succ_iff.1 hG
    choose g hg hgm using hg
    simp only [EuclideanSpace.basisFun_toBasis_apply] at hg
    -- the equation against test functions, in the predicate form, and its derivatives
    have hpred := forall_testFunction_of_forall_testFunctions (fun Φ _ ↦ heq Φ)
    have hpred' : ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin N))), ℝ),
        ∑ i, ∫ x in ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) : Set (EuclideanSpace ℝ (Fin N))),
          w i x * fderiv ℝ φ x (EuclideanSpace.single i 1)
        = ∫ x in ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) : Set (EuclideanSpace ℝ (Fin N))),
          G x * φ x := fun φ ↦ by
      rw [← hpred φ]
      refine Finset.sum_congr rfl fun i _ ↦ integral_congr_ae ?_
      have h1 := ((hasWeakIteratedLineDerivOn u (MultiIndexLE.single i)).of_perm
        (multiIndexTuple_single_perm ((EuclideanSpace.basisFun (Fin N) ℝ).toBasis :
          Fin N → EuclideanSpace ℝ (Fin N)) i))
      rw [EuclideanSpace.basisFun_toBasis_apply] at h1
      filter_upwards
        [(ae_restrict_iff' (⊤ : Opens (EuclideanSpace ℝ (Fin N))).isOpen.measurableSet).2
        (h1.ae_eq (hw i))] with x hx
      rw [hx]
    have hderiv := forall_testFunction_deriv hw (fun i j ↦ hv j i) hg hpred'
    -- `∂_j u ∈ H^{m+2}` for every `j`
    have hwj : ∀ j, MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (w j) (m + 2) 2
        ⊤ volume := by
      intro j
      obtain ⟨Wj, Gj, hWj, -, hGj, hWG⟩ := exists_sobolevEuclidean_of_forall_testFunction
        (hw1 j).memLp (fun i ↦ hv j i) (fun i ↦ hvp j i) (hgm j).memLp (hderiv j)
      have hall : ∀ φ, dirichletForm (⊤ : Opens (EuclideanSpace ℝ (Fin N))) Wj φ
          = load (⊤ : Opens (EuclideanSpace ℝ (Fin N))) Gj φ := fun φ ↦
        dirichletForm_eq_load_of_forall_testFunctions hWG
          (by rw [SobolevEuclideanZero.eq_top h2]; exact Submodule.mem_top)
      exact (ih Wj Gj ((hgm j).congr_ae hGj.symm) hall).congr_ae hWj
    -- assembly
    refine memSobolevMultiIndex_succ_iff.2 ⟨ih u G hGm heq, fun j ↦ ⟨w j, ?_, hwj j⟩⟩
    rw [EuclideanSpace.basisFun_toBasis_apply]
    exact hw j

end WholeSpaceHigher


/-! ### Algebra of `MemSobolevMultiIndex`, and the local spaces -/

section Algebra

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ} {p : ℝ≥0∞}
  {Ω : Opens E} {μ : Measure E}


variable [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] [IsLocallyFiniteMeasure μ]

omit [OpensMeasurableSpace E] [BorelSpace E] [CompleteSpace F] [IsLocallyFiniteMeasure μ] in
/-- A function in `W^{0,p}_loc(Ω)` is locally in `L^p` on `Ω`. -/
theorem _root_.MemSobolevMultiIndexLoc.locallyMemLpOn {f : E → F}
    (hf : MemSobolevMultiIndexLoc b f 0 p Ω μ) : LocallyMemLpOn f p Ω μ := by
  intro x hx
  obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 Ω.isOpen x hx
  have hball : closure (ball x (ε / 2)) ⊆ Ω :=
    closure_ball_subset_closedBall.trans ((closedBall_subset_ball (half_lt_self hε)).trans hεΩ)
  refine ⟨ball x (ε / 2), mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (half_pos hε)), ?_⟩
  exact (hf ⟨ball x (ε / 2), isOpen_ball⟩ ((isCompact_closedBall x (ε / 2)).of_isClosed_subset
    isClosed_closure closure_ball_subset_closedBall) hball).memLp

omit [IsLocallyFiniteMeasure μ] in
/-- The weak derivative on `Ω` along a basis vector of a function in `W^{1,p}_loc(Ω)` is locally in
`L^p` on `Ω`: on every `V ⋐ Ω` it agrees almost everywhere with the derivative that the
membership provides. -/
theorem _root_.MemSobolevMultiIndexLoc.memSobolevMultiIndexLoc_weakDeriv {f w : E → F} {k : ℕ}
    (hf : MemSobolevMultiIndexLoc b f (k + 1) p Ω μ) {i : ι}
    (hw : HasWeakIteratedLineDerivOn ![b i] f w Ω μ) : MemSobolevMultiIndexLoc b w k p Ω μ := by
  intro V hVc hVΩ
  obtain ⟨-, hg⟩ := memSobolevMultiIndex_succ_iff.1 (hf V hVc hVΩ)
  obtain ⟨g, hg, hgm⟩ := hg i
  refine hgm.congr_ae ?_
  exact (ae_restrict_iff' V.isOpen.measurableSet).2
    (hg.ae_eq (hw.mono (subset_closure.trans hVΩ)))

end Algebra

/-! ### Case C₁, higher order: Remark 25 -/

section InteriorHigher

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

open SobolevMultiIndex

/-- **Chapter 9, Remark 25: interior `H^{m+2}` regularity** ([brezis2011functional] §9.6). Let
`Ω ⊆ ℝ^N` be open, `u ∈ H^1_loc(Ω)` with weak partial derivatives `w i` on `Ω`,
`f ∈ H^m_loc(Ω)`, and `∑ᵢ ∫_Ω wᵢ ∂ᵢφ = ∫_Ω f φ` for every test function `φ` on `Ω`. Then
`u ∈ H^{m+2}_loc(Ω)`.

By induction on `m`, following case C₁: for `ω ⋐ Ω` and a smooth `θ` equal to `1` near
`closure ω` with compact support in `Ω`, the zero extension of `θu` solves
`−Δ(θu) = θf − 2∇θ·∇u − (Δθ)u` on `ℝ^N` (`Elliptic.sum_integral_indicator_cutoff_eq`); by the
inductive hypothesis `u ∈ H^{m+2}_loc(Ω)`, so the right side lies in `H^{m+1}(ℝ^N)`
(`MemSobolevMultiIndex.indicator_smul_of_tsupport_subset` for each piece), and case A at order
`m + 1` (`Elliptic.regularity_top_higher`) gives `θu ∈ H^{m+3}(ℝ^N)`, hence `u ∈ H^{m+3}(ω)`.
The hypoellipticity of the last paragraph of Remark 25 is the local nature of the hypotheses:
apply the theorem on `ω` in place of `Ω`. -/
theorem regularity_interior_higher (m : ℕ) : ∀ {u f : EuclideanSpace ℝ (Fin N) → ℝ}
    {w : Fin N → EuclideanSpace ℝ (Fin N) → ℝ},
    MemSobolevMultiIndexLoc (EuclideanSpace.basisFun (Fin N) ℝ).toBasis u 1 2 Ω volume →
    (∀ i, HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1] u (w i) Ω volume) →
    MemSobolevMultiIndexLoc (EuclideanSpace.basisFun (Fin N) ℝ).toBasis f m 2 Ω volume →
    (∀ φ : 𝓓(Ω, ℝ), ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      ∑ i, w i x * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), f x * φ x) →
    MemSobolevMultiIndexLoc (EuclideanSpace.basisFun (Fin N) ℝ).toBasis u (m + 2) 2 Ω volume := by
  induction m with
  | zero =>
    intro u f w hu hw hf heq
    have hw' : ∀ i, LocallyMemLpOn (w i) 2 Ω volume := fun i ↦
      (hu.memSobolevMultiIndexLoc_weakDeriv (i := i) (by
        rw [EuclideanSpace.basisFun_toBasis_apply]; exact hw i)).locallyMemLpOn
    exact regularity_interior (hu.mono_order zero_le_one).locallyMemLpOn hw hw'
      hf.locallyMemLpOn heq
  | succ m ih =>
    intro u f w hu hw hf heq
    have h2 : (2 : ℝ≥0∞) ≠ ⊤ := ENNReal.ofNat_ne_top
    have hΩm : MeasurableSet (Ω : Set (EuclideanSpace ℝ (Fin N))) := Ω.isOpen.measurableSet
    -- the inductive hypothesis: `u ∈ H^{m+2}_loc`
    have hu2 := ih hu hw (hf.mono_order (Nat.le_succ m)) heq
    have hul : LocallyIntegrableOn u Ω volume :=
      (hu.mono_order zero_le_one).locallyMemLpOn.locallyIntegrableOn_of_le one_le_two h2
    have hfl : LocallyIntegrableOn f Ω volume :=
      (hf.mono_order (Nat.zero_le _)).locallyMemLpOn.locallyIntegrableOn_of_le one_le_two h2
    intro V hVc hVΩ
    -- the cut-off, supported in `V' ⋐ Ω`
    obtain ⟨V', -, hV'o, hVV', -, hV'c, hV'Ω, -⟩ :=
      hVc.exists_pos_forall_closedBall_subset Ω.isOpen hVΩ
    obtain ⟨θ, hθ, hθ1, hθc, hθV'⟩ := exists_contDiff_eqOn_one_hasCompactSupport (Ω := ⟨V', hV'o⟩)
      hVc hVV'
    have hθΩ : tsupport θ ⊆ Ω := hθV'.trans (subset_closure.trans hV'Ω)
    have hθ' : IsSobolevCutoff Ω θ := IsSobolevCutoff.of_hasCompactSupport hθ hθc hθΩ
    have hV'Ω' : (⟨V', hV'o⟩ : Opens (EuclideanSpace ℝ (Fin N))) ≤ Ω := subset_closure.trans hV'Ω
    -- the memberships on `V'`
    have huV' := hu2 ⟨V', hV'o⟩ hV'c hV'Ω
    have hfV' := hf ⟨V', hV'o⟩ hV'c hV'Ω
    have hwV' : ∀ i,
        MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (w i) (m + 1) 2
        ⟨V', hV'o⟩ volume := fun i ↦
      (hu2.memSobolevMultiIndexLoc_weakDeriv (i := i) (by
        rw [EuclideanSpace.basisFun_toBasis_apply]; exact hw i)) ⟨V', hV'o⟩ hV'c hV'Ω
    -- the pieces of the datum, as functions on `ℝ^N` in `H^{m+1}(ℝ^N)`
    have hext : ∀ (α : EuclideanSpace ℝ (Fin N) → ℝ), ContDiff ℝ ∞ α → HasCompactSupport α →
        tsupport α ⊆ tsupport θ → ∀ {v : EuclideanSpace ℝ (Fin N) → ℝ},
        MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis v (m + 1) 2 ⟨V', hV'o⟩
          volume →
        MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
          ((Ω : Set (EuclideanSpace ℝ (Fin N))).indicator fun x ↦ α x * v x) (m + 1) 2 ⊤
          volume := by
      intro α hα hαc hαθ v hv
      have hmem := MemSobolevMultiIndex.indicator_smul_of_tsupport_subset (Ω := ⊤)
        (Ω' := ⟨V', hV'o⟩) one_le_two le_top hα hαc (fun x hx ↦ hθV' (hαθ hx.1)) hv
      refine hmem.congr_ae (Eventually.of_forall fun x ↦ ?_)
      change V'.indicator (fun x ↦ α x • v x) x = (Ω : Set _).indicator (fun x ↦ α x * v x) x
      by_cases hxV : x ∈ V'
      · rw [Set.indicator_of_mem hxV, Set.indicator_of_mem (hV'Ω' hxV)]; rfl
      · rw [Set.indicator_of_notMem hxV]
        by_cases hxΩ : x ∈ (Ω : Set (EuclideanSpace ℝ (Fin N)))
        · rw [Set.indicator_of_mem hxΩ, image_eq_zero_of_notMem_tsupport fun h ↦ hxV (hθV' (hαθ h)),
            zero_mul]
        · rw [Set.indicator_of_notMem hxΩ]
    obtain ⟨hΔ, hΔc, hΔθ⟩ := laplacianRep_props hθ hθc
    have hg1 := hext θ hθ hθc le_rfl hfV'
    have hg2 : ∀ i, MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
        ((Ω : Set (EuclideanSpace ℝ (Fin N))).indicator fun x ↦
          fderiv ℝ θ x (EuclideanSpace.single i 1) * w i x) (m + 1) 2 ⊤ volume := fun i ↦
      hext _ (hθ'.contDiff_fderiv_apply _) (hθc.fderiv_apply ℝ _) (tsupport_fderiv_apply_subset ℝ _)
        (hwV' i)
    have hg3 := hext _ hΔ hΔc hΔθ (huV'.mono_order (by omega))
    obtain ⟨g, hg⟩ : ∃ g : EuclideanSpace ℝ (Fin N) → ℝ,
        g = (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator fun x ↦
          θ x * f x - 2 * ∑ i, fderiv ℝ θ x (EuclideanSpace.single i 1) * w i x
          - (∑ i, fderiv ℝ (fun z ↦ fderiv ℝ θ z (EuclideanSpace.single i 1)) x
            (EuclideanSpace.single i 1)) * u x := ⟨_, rfl⟩
    have hgm : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis g (m + 1) 2 ⊤
        volume := by
      have := (hg1.sub ((MemSobolevMultiIndex.finset_sum Finset.univ fun i _ ↦ hg2 i).const_smul
        2)).sub hg3
      refine this.congr_ae (Eventually.of_forall fun x ↦ ?_)
      rw [hg]
      by_cases hx : x ∈ (Ω : Set (EuclideanSpace ℝ (Fin N)))
      · simp only [Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, Set.indicator_of_mem hx,
          smul_eq_mul]
      · simp [Set.indicator_of_notMem hx]
    -- `θu` on `ℝ^N`, its derivatives, and the equation
    obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin N) → ℝ,
        v = (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator fun x ↦ θ x * u x := ⟨_, rfl⟩
    obtain ⟨wv, hwv⟩ : ∃ wv : Fin N → EuclideanSpace ℝ (Fin N) → ℝ,
        wv = fun i ↦ (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator
          fun x ↦ θ x * w i x + fderiv ℝ θ x (EuclideanSpace.single i 1) * u x := ⟨_, rfl⟩
    have huloc : LocallyMemLpOn u 2 Ω volume := (hu.mono_order zero_le_one).locallyMemLpOn
    have hwloc : ∀ i, LocallyMemLpOn (w i) 2 Ω volume := fun i ↦
      (hu.memSobolevMultiIndexLoc_weakDeriv (i := i) (by
        rw [EuclideanSpace.basisFun_toBasis_apply]; exact hw i)).locallyMemLpOn
    have hvp : MemLp v 2 (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) : Set _)) := by
      rw [Measure.restrict_coe_top, hv]
      exact huloc.memLp_indicator_mul_of_tsupport_subset h2 hθ.continuous hθc hθΩ
    have hwvp : ∀ i, MemLp (wv i) 2
        (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) : Set _)) := fun i ↦ by
      rw [Measure.restrict_coe_top, hwv]
      have h1 := (hwloc i).memLp_indicator_mul_of_tsupport_subset h2 hθ.continuous hθc hθΩ
      have h2' := huloc.memLp_indicator_mul_of_tsupport_subset h2
        (hθ'.contDiff_fderiv_apply (EuclideanSpace.single i 1)).continuous
        (hθc.fderiv_apply ℝ (EuclideanSpace.single i 1))
        ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hθΩ)
      refine (h1.add h2').ae_eq (Eventually.of_forall fun x ↦ ?_)
      by_cases hx : x ∈ (Ω : Set (EuclideanSpace ℝ (Fin N)))
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    have hwvd : ∀ i, HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1] v (wv i) ⊤ volume :=
      fun i ↦ by
        rw [hv, hwv]
        exact (hw i).indicator_mul hθ'
    have heqv : ∀ ψ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin N))), ℝ),
        ∑ i, ∫ x in ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) : Set _),
          wv i x * fderiv ℝ ψ x (EuclideanSpace.single i 1)
        = ∫ x in ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) : Set _), g x * ψ x := fun ψ ↦ by
      simp only [Measure.restrict_coe_top]
      rw [hwv, hg]
      exact sum_integral_indicator_cutoff_eq (fun i ↦ EuclideanSpace.single i 1) hul hfl hw heq
        hθ' ψ
    obtain ⟨V₁, G, hV₁, -, hG, hVG⟩ :=
      exists_sobolevEuclidean_of_forall_testFunction hvp hwvd hwvp hgm.memLp heqv
    have hall : ∀ φ, dirichletForm (⊤ : Opens (EuclideanSpace ℝ (Fin N))) V₁ φ
        = load (⊤ : Opens (EuclideanSpace ℝ (Fin N))) G φ := fun φ ↦
      dirichletForm_eq_load_of_forall_testFunctions hVG
        (by rw [SobolevEuclideanZero.eq_top h2]; exact Submodule.mem_top)
    have hmem := (regularity_top_higher (m + 1) V₁ G (hgm.congr_ae hG.symm) hall).congr_ae hV₁
    refine (hmem.mono_set le_top).congr_ae ?_
    refine (ae_restrict_iff' V.isOpen.measurableSet).2 (Eventually.of_forall fun x hx ↦ ?_)
    rw [hv, Set.indicator_of_mem (hVΩ (subset_closure hx)), hθ1 (subset_closure hx), Pi.one_apply,
      one_mul]

/-- **The bootstrap of [brezis2011functional] Chapter 9, Remark 25** ("the same method applies …
and argue by induction on `m`") for a datum that depends on the solution: let `u ∈ H^1_loc(Ω)`
with weak partial derivatives `w i`, and let `∫_Ω ∇u · ∇φ = ∫_Ω (f + c u) φ` for every test
function `φ` on `Ω`, with `f ∈ H^m_loc(Ω)`. Then `u ∈ H^{m+2}_loc(Ω)`: the datum `f + c u` gains
regularity with `u`, and interior regularity (`regularity_interior_higher`) raises the order by
two at each step. The datum `f − u` of the Dirichlet problem for `−Δ + 1` is the case `c = −1`,
the eigenvalue equation `−Δu = λu` the case `f = 0`, `c = λ`. -/
theorem memSobolevMultiIndexLoc_of_forall_testFunction_add_mul (m : ℕ)
    {u f : EuclideanSpace ℝ (Fin N) → ℝ} {w : Fin N → EuclideanSpace ℝ (Fin N) → ℝ} {c : ℝ}
    (hu : MemSobolevMultiIndexLoc (EuclideanSpace.basisFun (Fin N) ℝ).toBasis u 1 2 Ω volume)
    (hw : ∀ i, HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1] u (w i) Ω volume)
    (hf : MemSobolevMultiIndexLoc (EuclideanSpace.basisFun (Fin N) ℝ).toBasis f m 2 Ω volume)
    (heq : ∀ φ : 𝓓(Ω, ℝ), ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      ∑ i, w i x * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), (f x + c * u x) * φ x) :
    MemSobolevMultiIndexLoc (EuclideanSpace.basisFun (Fin N) ℝ).toBasis u (m + 2) 2 Ω volume := by
  have key : ∀ k : ℕ, k ≤ m + 1 →
      MemSobolevMultiIndexLoc (EuclideanSpace.basisFun (Fin N) ℝ).toBasis u (k + 1) 2 Ω volume := by
    intro k
    induction k with
    | zero => exact fun _ ↦ hu
    | succ k ih =>
      intro hk
      have hu' := ih (by omega)
      have hfu : MemSobolevMultiIndexLoc (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
          (fun x ↦ f x + c * u x) k 2 Ω volume :=
        fun V hVc hVΩ ↦ (((hf V hVc hVΩ).mono_order (by omega)).add
          (((hu' V hVc hVΩ).mono_order (by omega)).const_smul c)).congr_ae
            (Eventually.of_forall fun x ↦ by simp)
      exact regularity_interior_higher k hu hw hfu heq
  exact key (m + 1) le_rfl

/-- **The weak equation against the test functions of `Ω` restricts to any open `Ω' ⊆ Ω`**: both
integrands vanish off `Ω'`, the test function on `Ω'` being a test function on `Ω`. -/
theorem forall_testFunction_of_le {f : EuclideanSpace ℝ (Fin N) → ℝ}
    {w : Fin N → EuclideanSpace ℝ (Fin N) → ℝ} {Ω' : Opens (EuclideanSpace ℝ (Fin N))}
    (hω : Ω' ≤ Ω)
    (heq : ∀ φ : 𝓓(Ω, ℝ), ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      ∑ i, w i x * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), f x * φ x) (φ : 𝓓(Ω', ℝ)) :
    ∫ x in (Ω' : Set (EuclideanSpace ℝ (Fin N))),
      ∑ i, w i x * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = ∫ x in (Ω' : Set (EuclideanSpace ℝ (Fin N))), f x * φ x := by
  have h := heq (φ.ofLE hω)
  rw [TestFunction.ofLE_coe] at h
  have h1 : ∀ x, x ∉ (Ω' : Set (EuclideanSpace ℝ (Fin N))) →
      ∑ i, w i x * fderiv ℝ φ x (EuclideanSpace.single i 1) = 0 := by
    intro x hx
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    have := (φ.fderivApply (EuclideanSpace.single i 1)).eq_zero_of_notMem hx
    rw [TestFunction.fderivApply_apply] at this
    rw [this, mul_zero]
  have h2 : ∀ x, x ∉ (Ω' : Set (EuclideanSpace ℝ (Fin N))) → f x * φ x = 0 := fun x hx ↦ by
    rw [φ.eq_zero_of_notMem hx, mul_zero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ h1 x fun h' ↦ hx (hω h'),
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ h2 x fun h' ↦ hx (hω h')] at h
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero h1,
    setIntegral_eq_integral_of_forall_compl_eq_zero h2]
  exact h

end InteriorHigher


/-! ### Cutting off a weak solution, against the test functions of the same set -/

section CutoffInside

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] {μ : Measure E} {Ω : Opens E}

omit [MeasurableSpace E] [BorelSpace E] in
/-- A smooth function times a test function on `Ω` is a test function on `Ω`. -/
def _root_.TestFunction.contDiffMul (ψ : 𝓓(Ω, ℝ)) {θ : E → ℝ} (hθ : ContDiff ℝ ∞ θ) : 𝓓(Ω, ℝ) where
  toFun x := θ x * ψ x
  contDiff' := hθ.mul ψ.contDiff
  hasCompactSupport' := ψ.hasCompactSupport.mul_left
  tsupport_subset' := tsupport_mul_subset_right.trans ψ.tsupport_subset

omit [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem _root_.TestFunction.contDiffMul_coe (ψ : 𝓓(Ω, ℝ)) {θ : E → ℝ} (hθ : ContDiff ℝ ∞ θ) :
    (ψ.contDiffMul hθ : E → ℝ) = fun x ↦ θ x * ψ x :=
  rfl

/-- **Cutting off a weak solution of `−div(∇u) = f`, against the test functions of `Ω`**: let
`u` have the weak partial derivatives `w i` along the vectors `b i` on `Ω`, all locally
integrable, let `f` be locally integrable on `Ω`, and let `∑ᵢ ∫_Ω wᵢ ∂ᵢφ = ∫_Ω f φ` for every test
function `φ` on `Ω`. For a smooth `θ` (no support condition) and every test function `ψ` on `Ω`,

`∑ᵢ ∫_Ω (θ wᵢ + (∂ᵢθ) u) ∂ᵢψ = ∫_Ω (θ f − 2 ∑ᵢ (∂ᵢθ) wᵢ − (∑ᵢ ∂ᵢ∂ᵢθ) u) ψ`.

The equation is tested with `θψ` and the weak derivatives with `(∂ᵢθ) ψ`, both test functions
on `Ω`. This is the computation of [brezis2011functional] §9.6, case C₂ ("it is easy to verify
that `v = θᵢ u` is a weak solution in `Ω ∩ Uᵢ` of `−Δv = θᵢ f − θᵢ u − 2∇θᵢ·∇u − (Δθᵢ)u`"). -/
theorem sum_integral_cutoff_eq {ι : Type*} [Fintype ι] (b : ι → E) {u f : E → ℝ}
    {w : ι → E → ℝ} (hu : LocallyIntegrableOn u Ω μ) (hf : LocallyIntegrableOn f Ω μ)
    (hw : ∀ i, HasWeakIteratedLineDerivOn ![b i] u (w i) Ω μ)
    (heq : ∀ φ : 𝓓(Ω, ℝ), ∫ x in (Ω : Set E), ∑ i, w i x * fderiv ℝ φ x (b i) ∂μ
      = ∫ x in (Ω : Set E), f x * φ x ∂μ)
    {θ : E → ℝ} (hθ : ContDiff ℝ ∞ θ) (ψ : 𝓓(Ω, ℝ)) :
    ∑ i, ∫ x in (Ω : Set E), (θ x * w i x + fderiv ℝ θ x (b i) * u x) * fderiv ℝ ψ x (b i) ∂μ
      = ∫ x in (Ω : Set E), (θ x * f x - 2 * ∑ i, fderiv ℝ θ x (b i) * w i x
          - (∑ i, fderiv ℝ (fun z ↦ fderiv ℝ θ z (b i)) x (b i)) * u x) * ψ x ∂μ := by
  have hΩm : MeasurableSet (Ω : Set E) := Ω.isOpen.measurableSet
  have hwl : ∀ i, LocallyIntegrableOn (w i) Ω μ := fun i ↦ (hw i).locallyIntegrableOn_weakDeriv
  have hψc : ContDiff ℝ ∞ (ψ : E → ℝ) := ψ.contDiff
  have hdθ : ∀ i, ContDiff ℝ ∞ fun x ↦ fderiv ℝ θ x (b i) := fun i ↦
    (hθ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
  have hdψ : ∀ i, ContDiff ℝ ∞ fun x ↦ fderiv ℝ ψ x (b i) := fun i ↦
    (hψc.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
  have hddθ : ∀ i, ContDiff ℝ ∞ fun x ↦ fderiv ℝ (fun z ↦ fderiv ℝ θ z (b i)) x (b i) := fun i ↦
    contDiff_fderiv_fderiv_apply hθ _
  have hsψ : ∀ i, tsupport (fun x ↦ fderiv ℝ ψ x (b i)) ⊆ Ω := fun i ↦
    (tsupport_fderiv_apply_subset ℝ (b i)).trans ψ.tsupport_subset
  -- integrability: a continuous function with compact support in `Ω` times a locally integrable
  -- function is integrable on `Ω`
  have I : ∀ (v : E → ℝ), LocallyIntegrableOn v Ω μ → ∀ (g : E → ℝ), Continuous g →
      HasCompactSupport g → tsupport g ⊆ Ω → IntegrableOn (fun x ↦ g x * v x) Ω μ :=
    fun v hv g hg hgc hgΩ ↦
      (LocallyIntegrableOn.integrable_smul_left_of_tsupport_subset hv hg hgc hgΩ).integrableOn
  -- the identity for one direction
  have key : ∀ i, ∫ x in (Ω : Set E), (θ x * w i x + fderiv ℝ θ x (b i) * u x)
        * fderiv ℝ ψ x (b i) ∂μ
      = ∫ x in (Ω : Set E), w i x * fderiv ℝ (fun z ↦ θ z * ψ z) x (b i) ∂μ
        - 2 * ∫ x in (Ω : Set E), fderiv ℝ θ x (b i) * w i x * ψ x ∂μ
        - ∫ x in (Ω : Set E), fderiv ℝ (fun z ↦ fderiv ℝ θ z (b i)) x (b i) * u x * ψ x ∂μ := by
    intro i
    have hd1 : ∀ x, fderiv ℝ (fun z ↦ θ z * ψ z) x (b i)
        = fderiv ℝ θ x (b i) * ψ x + θ x * fderiv ℝ ψ x (b i) := fun x ↦ by
      rw [fderiv_fun_mul (hθ.differentiable (by simp) x) (hψc.differentiable (by simp) x)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      ring
    have hd2 : ∀ x, fderiv ℝ (fun z ↦ fderiv ℝ θ z (b i) * ψ z) x (b i)
        = fderiv ℝ (fun z ↦ fderiv ℝ θ z (b i)) x (b i) * ψ x
          + fderiv ℝ θ x (b i) * fderiv ℝ ψ x (b i) := fun x ↦ by
      rw [fderiv_fun_mul ((hdθ i).differentiable (by simp) x) (hψc.differentiable (by simp) x)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      ring
    have hB := (hw i).integral_fderiv_mul_eq_of_eqOn (ψ.contDiffMul (hdθ i)) (fun _ _ ↦ rfl)
    simp only [TestFunction.contDiffMul_coe] at hB
    have I1 : IntegrableOn (fun x ↦ fderiv ℝ θ x (b i) * ψ x * w i x) Ω μ :=
      I (w i) (hwl i) _ ((hdθ i).continuous.mul ψ.continuous) ψ.hasCompactSupport.mul_left
        (tsupport_mul_subset_right.trans ψ.tsupport_subset)
    have I2 : IntegrableOn (fun x ↦ θ x * fderiv ℝ ψ x (b i) * w i x) Ω μ :=
      I (w i) (hwl i) _ (hθ.continuous.mul (hdψ i).continuous)
        (ψ.hasCompactSupport.fderiv_apply ℝ (b i)).mul_left
        (tsupport_mul_subset_right.trans (hsψ i))
    have I3 : IntegrableOn (fun x ↦ fderiv ℝ (fun z ↦ fderiv ℝ θ z (b i)) x (b i) * ψ x * u x)
        Ω μ :=
      I u hu _ ((hddθ i).continuous.mul ψ.continuous) ψ.hasCompactSupport.mul_left
        (tsupport_mul_subset_right.trans ψ.tsupport_subset)
    have I4 : IntegrableOn (fun x ↦ fderiv ℝ θ x (b i) * fderiv ℝ ψ x (b i) * u x) Ω μ :=
      I u hu _ ((hdθ i).continuous.mul (hdψ i).continuous)
        (ψ.hasCompactSupport.fderiv_apply ℝ (b i)).mul_left
        (tsupport_mul_subset_right.trans (hsψ i))
    have e1 : ∫ x in (Ω : Set E), (θ x * w i x + fderiv ℝ θ x (b i) * u x)
          * fderiv ℝ ψ x (b i) ∂μ
        = (∫ x in (Ω : Set E), θ x * fderiv ℝ ψ x (b i) * w i x ∂μ)
          + ∫ x in (Ω : Set E), fderiv ℝ θ x (b i) * fderiv ℝ ψ x (b i) * u x ∂μ := by
      rw [← integral_add I2 I4]
      exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
    have e2 : ∫ x in (Ω : Set E), w i x * fderiv ℝ (fun z ↦ θ z * ψ z) x (b i) ∂μ
        = (∫ x in (Ω : Set E), fderiv ℝ θ x (b i) * ψ x * w i x ∂μ)
          + ∫ x in (Ω : Set E), θ x * fderiv ℝ ψ x (b i) * w i x ∂μ := by
      simp_rw [hd1]
      rw [← integral_add I1 I2]
      exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
    have e3 : ∫ x in (Ω : Set E), fderiv ℝ (fun z ↦ fderiv ℝ θ z (b i) * ψ z) x (b i) * u x ∂μ
        = (∫ x in (Ω : Set E), fderiv ℝ (fun z ↦ fderiv ℝ θ z (b i)) x (b i) * ψ x * u x ∂μ)
          + ∫ x in (Ω : Set E), fderiv ℝ θ x (b i) * fderiv ℝ ψ x (b i) * u x ∂μ := by
      simp_rw [hd2]
      rw [← integral_add I3 I4]
      exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
    have e5 : ∫ x in (Ω : Set E), fderiv ℝ θ x (b i) * ψ x * w i x ∂μ
        = ∫ x in (Ω : Set E), fderiv ℝ θ x (b i) * w i x * ψ x ∂μ :=
      integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
    have e7 : ∫ x in (Ω : Set E), fderiv ℝ (fun z ↦ fderiv ℝ θ z (b i)) x (b i) * ψ x * u x ∂μ
        = ∫ x in (Ω : Set E), fderiv ℝ (fun z ↦ fderiv ℝ θ z (b i)) x (b i) * u x * ψ x ∂μ :=
      integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
    rw [e3, e5, e7] at hB
    rw [e1, e2, e5]
    linarith
  simp_rw [key]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have IB : ∀ i, IntegrableOn (fun x ↦ fderiv ℝ θ x (b i) * w i x * ψ x) Ω μ := fun i ↦
    (I (w i) (hwl i) (fun x ↦ fderiv ℝ θ x (b i) * ψ x) ((hdθ i).continuous.mul ψ.continuous)
      ψ.hasCompactSupport.mul_left (tsupport_mul_subset_right.trans ψ.tsupport_subset)).congr_fun
      (fun x _ ↦ by ring) hΩm
  have IC : ∀ i, IntegrableOn (fun x ↦ fderiv ℝ (fun z ↦ fderiv ℝ θ z (b i)) x (b i) * u x * ψ x)
      Ω μ := fun i ↦
    (I u hu (fun x ↦ fderiv ℝ (fun z ↦ fderiv ℝ θ z (b i)) x (b i) * ψ x)
      ((hddθ i).continuous.mul ψ.continuous) ψ.hasCompactSupport.mul_left
      (tsupport_mul_subset_right.trans ψ.tsupport_subset)).congr_fun (fun x _ ↦ by ring) hΩm
  have IF : IntegrableOn (fun x ↦ θ x * f x * ψ x) Ω μ :=
    (I f hf (fun x ↦ θ x * ψ x) (hθ.continuous.mul ψ.continuous) ψ.hasCompactSupport.mul_left
      (tsupport_mul_subset_right.trans ψ.tsupport_subset)).congr_fun (fun x _ ↦ by ring) hΩm
  -- the sum of the first terms is the equation tested with `θψ`
  have hA : ∑ i, ∫ x in (Ω : Set E), w i x * fderiv ℝ (fun z ↦ θ z * ψ z) x (b i) ∂μ
      = ∫ x in (Ω : Set E), θ x * f x * ψ x ∂μ := by
    have := heq (ψ.contDiffMul hθ)
    simp only [TestFunction.contDiffMul_coe] at this
    rw [← integral_finsetSum _ fun i _ ↦ ((hw i).integrable_smul_weakDeriv
      ((ψ.contDiffMul hθ).fderivApply (b i))).integrableOn.congr_fun
        (fun x _ ↦ by simp [TestFunction.fderivApply_apply, mul_comm]) hΩm, this]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
  have hB2 : IntegrableOn (fun x ↦ 2 * ∑ i, fderiv ℝ θ x (b i) * w i x * ψ x) Ω μ :=
    (integrable_finsetSum _ fun i _ ↦ IB i).const_mul 2
  have hCs : IntegrableOn (fun x ↦ ∑ i, fderiv ℝ (fun z ↦ fderiv ℝ θ z (b i)) x (b i) * u x * ψ x)
      Ω μ := integrable_finsetSum _ fun i _ ↦ IC i
  have h12 : IntegrableOn (fun x ↦ θ x * f x * ψ x - 2 * ∑ i, fderiv ℝ θ x (b i) * w i x * ψ x)
      Ω μ := IF.sub hB2
  rw [hA, ← integral_finsetSum _ fun i _ ↦ IB i, ← integral_finsetSum _ fun i _ ↦ IC i,
    ← integral_const_mul, ← integral_sub IF hB2, ← integral_sub h12 hCs]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [sub_mul, Finset.sum_mul, mul_assoc]

end CutoffInside


/-! ### The boundary pieces `θᵢ u` on `Ω ∩ Uᵢ` -/

section BoundaryPiece

variable {N : ℕ} {Ω Ω' : Opens (EuclideanSpace ℝ (Fin N))}

open SobolevMultiIndex

/-- The partial derivative `∂ᵢu` of an element of `H^1(Ω)` is a weak derivative of its function
along `eᵢ` (the case `p = 2` of `SobolevEuclidean.hasWeakIteratedLineDerivOn_fn_single`). -/
theorem weakDeriv_hasWeakIteratedLineDerivOn_single (u : SobolevEuclidean N 1 2 Ω) (i : Fin N) :
    HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1] (fn u)
      (weakDeriv u (MultiIndexLE.single i)) Ω volume :=
  SobolevEuclidean.hasWeakIteratedLineDerivOn_fn_single u i

/-- A smooth function `θ` with `tsupport θ ∩ Ω ⊆ Ω'` times a test function on `Ω` is a test
function on `Ω'`. -/
def _root_.TestFunction.contDiffMulOfSubset (φ : 𝓓(Ω, ℝ)) {θ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hθΩ' : tsupport θ ∩ Ω ⊆ Ω') : 𝓓(Ω', ℝ) where
  toFun x := θ x * φ x
  contDiff' := hθ.mul φ.contDiff
  hasCompactSupport' := φ.hasCompactSupport.mul_left
  tsupport_subset' := fun _ hx ↦
    hθΩ' ⟨tsupport_mul_subset_left hx, φ.tsupport_subset (tsupport_mul_subset_right hx)⟩

/-- The function of `(θ ū)|_{Ω'}` is `θ u` on `Ω' ≤ Ω`, for the zero extension `ū` of
`u ∈ H^1_0(Ω)`: the operator is a variable with its defining equation, as the lessons of this
project prescribe for composites of typed operators. -/
theorem fn_boundaryPiece_of_ops (hΩ' : Ω' ≤ Ω) {θ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hθtop : IsSobolevCutoff (⊤ : Opens (EuclideanSpace ℝ (Fin N))) θ)
    {P : SobolevEuclideanZero N 1 2 Ω →L[ℝ] SobolevEuclidean N 1 2 Ω'}
    (hP : ∀ z, P z = restrictL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 volume
      (le_top (a := Ω')) (extendZeroMulL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 volume
        hθtop (SobolevEuclideanZero.extendZeroL N 2 Ω z)))
    (z : SobolevEuclideanZero N 1 2 Ω) :
    fn (P z) =ᵐ[volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N)))]
      fun x ↦ θ x * fn (z : SobolevEuclidean N 1 2 Ω) x := by
  rw [hP]
  refine (fn_restrictL _ _).trans ?_
  have h1 := fn_extendZeroMulL hθtop (SobolevEuclideanZero.extendZeroL N 2 Ω z)
  have h2 := SobolevEuclideanZero.fn_extendZeroL z
  filter_upwards [ae_restrict_of_ae h1, ae_restrict_of_ae h2,
    self_mem_ae_restrict Ω'.isOpen.measurableSet] with x hx1 hx2 hxΩ'
  rw [hx1, Set.indicator_of_mem (show x ∈ ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) : Set _) from
    trivial), hx2, Set.indicator_of_mem (hΩ' hxΩ'), smul_eq_mul]

/-- The partial derivatives of `(θ ū)|_{Ω'}` are `θ ∂ᵢu + (∂ᵢθ) u` on `Ω' ≤ Ω`. -/
theorem weakDeriv_boundaryPiece_of_ops (hΩ' : Ω' ≤ Ω) {θ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hθtop : IsSobolevCutoff (⊤ : Opens (EuclideanSpace ℝ (Fin N))) θ)
    {P : SobolevEuclideanZero N 1 2 Ω →L[ℝ] SobolevEuclidean N 1 2 Ω'}
    (hP : ∀ z, P z = restrictL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 volume
      (le_top (a := Ω')) (extendZeroMulL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 volume
        hθtop (SobolevEuclideanZero.extendZeroL N 2 Ω z)))
    (z : SobolevEuclideanZero N 1 2 Ω) (i : Fin N) :
    ⇑(weakDeriv (P z) (MultiIndexLE.single i))
      =ᵐ[volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N)))]
      fun x ↦ θ x * weakDeriv (z : SobolevEuclidean N 1 2 Ω) (MultiIndexLE.single i) x
        + fderiv ℝ θ x (EuclideanSpace.single i 1) * fn (z : SobolevEuclidean N 1 2 Ω) x := by
  rw [hP]
  refine (weakDeriv_restrictL _ _ _).trans ?_
  have h1 := weakDeriv_extendZeroMulL_single hθtop (SobolevEuclideanZero.extendZeroL N 2 Ω z) i
  have h2 := SobolevEuclideanZero.fn_extendZeroL z
  have h3 := SobolevEuclideanZero.weakDeriv_extendZeroL_single z i
  filter_upwards [ae_restrict_of_ae h1, ae_restrict_of_ae h2, ae_restrict_of_ae h3,
    self_mem_ae_restrict Ω'.isOpen.measurableSet] with x hx1 hx2 hx3 hxΩ'
  rw [hx1, Set.indicator_of_mem (show x ∈ ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) : Set _) from
    trivial), hx2, hx3, Set.indicator_of_mem (hΩ' hxΩ'), Set.indicator_of_mem (hΩ' hxΩ'),
    EuclideanSpace.basisFun_toBasis_apply]
  simp only [smul_eq_mul]

/-- **A continuous map `H^1_0(Ω) → H^1(Ω')` whose functions are `θ u` takes values in
`H^1_0(Ω')`**, when `θ` is smooth with `tsupport θ ∩ Ω ⊆ Ω'`: it sends the test-function
elements of `H^1_0(Ω)` to test-function elements of `H^1(Ω')`, and `H^1_0(Ω')` is closed. -/
theorem mem_zero_of_fn_ae_eq_contDiff_mul (hΩ' : Ω' ≤ Ω) {θ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hθΩ' : tsupport θ ∩ Ω ⊆ Ω')
    {P : SobolevEuclideanZero N 1 2 Ω →L[ℝ] SobolevEuclidean N 1 2 Ω'}
    (hPfn : ∀ z : SobolevEuclideanZero N 1 2 Ω,
      fn (P z) =ᵐ[volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N)))]
        fun x ↦ θ x * fn (z : SobolevEuclidean N 1 2 Ω) x)
    (z : SobolevEuclideanZero N 1 2 Ω) : P z ∈ SobolevEuclideanZero N 1 2 Ω' := by
  obtain ⟨w, φ, hwφ, hw⟩ := SobolevMultiIndexZero.exists_seq_testFunction_tendsto z.2
  have hwz : Tendsto (fun n ↦ (⟨w n, SobolevMultiIndexZero.testFunctions_le ⟨φ n, hwφ n⟩⟩ :
      SobolevEuclideanZero N 1 2 Ω)) atTop (𝓝 z) := tendsto_subtype_rng.2 hw
  have hlim := (P.continuous.tendsto z).comp hwz
  refine SobolevMultiIndexZero.isClosed.mem_of_tendsto hlim (Eventually.of_forall fun n ↦ ?_)
  refine SobolevMultiIndexZero.testFunctions_le ⟨(φ n).contDiffMulOfSubset hθ hθΩ', ?_⟩
  refine (hPfn _).trans ?_
  have hwφ' := (ae_restrict_iff' Ω.isOpen.measurableSet).1 (hwφ n)
  filter_upwards [ae_restrict_of_ae hwφ', self_mem_ae_restrict Ω'.isOpen.measurableSet]
    with x hx hxΩ'
  change θ x * fn (w n) x = θ x * φ n x
  rw [hx (hΩ' hxΩ')]

/-- The predicate form of the equation `∫_Ω ∇u · ∇Φ = ∫_Ω F Φ` for the test-function elements,
with the partial derivatives of `u` as functions. -/
theorem forall_testFunction_weakDeriv_of_forall_testFunctions {u : SobolevEuclidean N 1 2 Ω}
    {F : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ Φ ∈ testFunctions ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume,
      dirichletForm Ω u Φ = load Ω F Φ) (φ : 𝓓(Ω, ℝ)) :
    ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      ∑ i, weakDeriv u (MultiIndexLE.single i) x * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), F x * φ x := by
  rw [integral_finsetSum _ fun i _ ↦ ((weakDeriv_hasWeakIteratedLineDerivOn_single u i)
    |>.integrable_smul_weakDeriv (φ.fderivApply (EuclideanSpace.single i 1))).integrableOn.congr_fun
      (fun x _ ↦ by simp [TestFunction.fderivApply_apply, mul_comm]) Ω.isOpen.measurableSet]
  exact forall_testFunction_of_forall_testFunctions heq φ

/-- The datum `θ F − 2∇θ·∇u − (Δθ) u` of the boundary piece lies in `L²(Ω')`. -/
theorem memLp_boundaryDatum (hΩ' : Ω' ≤ Ω) {θ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ) (u : SobolevEuclidean N 1 2 Ω)
    (F : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    MemLp (fun x ↦ θ x * F x
      - 2 * ∑ i, fderiv ℝ θ x (EuclideanSpace.single i 1) * weakDeriv u (MultiIndexLE.single i) x
      - (∑ i, fderiv ℝ (fun z ↦ fderiv ℝ θ z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1)) * fn u x) 2
      (volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N)))) := by
  have hb : ∀ (α : EuclideanSpace ℝ (Fin N) → ℝ), Continuous α → HasCompactSupport α →
      ∀ {f : EuclideanSpace ℝ (Fin N) → ℝ},
      MemLp f 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) →
      MemLp (fun x ↦ α x * f x) 2 (volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N)))) := by
    intro α hα hαc f hf
    obtain ⟨C, hC⟩ := hαc.exists_bound_of_continuous hα
    exact (hf.mono_measure (Measure.restrict_mono hΩ' le_rfl)).mul_of_forall_abs_le
      hα.aestronglyMeasurable (C := C) (fun x _ ↦ (Real.norm_eq_abs _).symm.trans_le (hC x))
  have hθtop : IsSobolevCutoff (⊤ : Opens (EuclideanSpace ℝ (Fin N))) θ :=
    IsSobolevCutoff.of_hasCompactSupport hθ hθc (subset_univ _)
  obtain ⟨hΔ, hΔc, -⟩ := laplacianRep_props hθ hθc
  have h1 : MemLp (fun x ↦ θ x * F x) 2 (volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N)))) :=
    hb θ hθ.continuous hθc (Lp.memLp F)
  have h2 : ∀ i, MemLp (fun x ↦ fderiv ℝ θ x (EuclideanSpace.single i 1)
      * weakDeriv u (MultiIndexLE.single i) x) 2
      (volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N)))) := fun i ↦
    hb _ (hθtop.contDiff_fderiv_apply (EuclideanSpace.single i 1)).continuous
      (hθc.fderiv_apply ℝ (EuclideanSpace.single i 1)) (Lp.memLp _)
  have h2' : MemLp (fun x ↦ ∑ i, fderiv ℝ θ x (EuclideanSpace.single i 1)
      * weakDeriv u (MultiIndexLE.single i) x) 2
      (volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N)))) :=
    memLp_finsetSum Finset.univ (f := fun i x ↦ fderiv ℝ θ x (EuclideanSpace.single i 1)
      * weakDeriv u (MultiIndexLE.single i) x) fun i _ ↦ h2 i
  have h3 : MemLp (fun x ↦ (∑ i, fderiv ℝ (fun z ↦ fderiv ℝ θ z (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single i 1)) * fn u x) 2
      (volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N)))) :=
    hb _ hΔ.continuous hΔc (memLp u)
  exact (h1.sub (h2'.const_mul 2)).sub h3

/-- **The boundary piece `v = θ u` of a weak solution** ([brezis2011functional] §9.6, case C₂:
"`v = θᵢ u ∈ H^1_0(Ω ∩ Uᵢ)` is a weak solution in `Ω ∩ Uᵢ` of `−Δv = g`"): let `Ω' ≤ Ω`, let
`θ` be smooth with compact support and `tsupport θ ∩ Ω ⊆ Ω'`, let `u ∈ H^1_0(Ω)` satisfy
`∫_Ω ∇u · ∇Φ = ∫_Ω F Φ` for the test-function elements `Φ`. Then there are `v ∈ H^1_0(Ω')` with
function `θ u` and `G ∈ L²(Ω')` with `∫_{Ω'} ∇v · ∇Ψ = ∫_{Ω'} G Ψ` for all `Ψ ∈ H^1_0(Ω')`.

`v` is `θ ū` restricted to `Ω'`, for the zero extension `ū ∈ H^1(ℝ^N)` of `u`
(`Elliptic.mem_zero_of_fn_ae_eq_contDiff_mul`); the datum is `G = θ F − 2∇θ·∇u − (Δθ)u`
(`Elliptic.sum_integral_cutoff_eq`). -/
theorem exists_boundary_piece (hΩ' : Ω' ≤ Ω) {θ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ)
    (hθΩ' : tsupport θ ∩ Ω ⊆ Ω') {u : SobolevEuclidean N 1 2 Ω}
    (hu : u ∈ SobolevEuclideanZero N 1 2 Ω)
    {F : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ Φ ∈ testFunctions ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume,
      dirichletForm Ω u Φ = load Ω F Φ) :
    ∃ (v : SobolevEuclidean N 1 2 Ω')
      (G : Lp ℝ 2 (volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N))))),
      v ∈ SobolevEuclideanZero N 1 2 Ω' ∧
      fn v =ᵐ[volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N)))] (fun x ↦ θ x * fn u x) ∧
      ∀ Ψ ∈ SobolevEuclideanZero N 1 2 Ω', dirichletForm Ω' v Ψ = load Ω' G Ψ := by
  have hΩm : MeasurableSet (Ω : Set (EuclideanSpace ℝ (Fin N))) := Ω.isOpen.measurableSet
  have hθtop : IsSobolevCutoff (⊤ : Opens (EuclideanSpace ℝ (Fin N))) θ :=
    IsSobolevCutoff.of_hasCompactSupport hθ hθc (subset_univ _)
  obtain ⟨P, hP⟩ : ∃ P : SobolevEuclideanZero N 1 2 Ω →L[ℝ] SobolevEuclidean N 1 2 Ω',
      ∀ z, P z = restrictL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 volume
        (le_top (a := Ω')) (extendZeroMulL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 volume
          hθtop (SobolevEuclideanZero.extendZeroL N 2 Ω z)) :=
    ⟨(restrictL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 volume (le_top (a := Ω'))) ∘L
      (extendZeroMulL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 volume hθtop) ∘L
      (SobolevEuclideanZero.extendZeroL N 2 Ω), fun _ ↦ rfl⟩
  have hPfn := fn_boundaryPiece_of_ops hΩ' hθtop hP
  have hPd := weakDeriv_boundaryPiece_of_ops hΩ' hθtop hP
  have hgp := memLp_boundaryDatum hΩ' hθ hθc u F
  refine ⟨P ⟨u, hu⟩, hgp.toLp _, mem_zero_of_fn_ae_eq_contDiff_mul hΩ' hθ hθΩ' hPfn ⟨u, hu⟩,
    hPfn ⟨u, hu⟩, fun Ψ hΨ ↦ ?_⟩
  refine dirichletForm_eq_load_of_forall_testFunctions (fun Φ hΦ ↦ ?_) hΨ
  obtain ⟨ψ, hψ⟩ := hΦ
  rw [dirichletForm_apply_eq_of_ae_eq (hPd ⟨u, hu⟩) hψ, load_apply_eq_of_ae_eq hgp.coeFn_toLp hψ]
  have hwd : ∀ i, HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1] (fn u)
      (weakDeriv u (MultiIndexLE.single i)) Ω volume := fun i ↦
    weakDeriv_hasWeakIteratedLineDerivOn_single u i
  have hcut := sum_integral_cutoff_eq (fun i ↦ EuclideanSpace.single i 1)
    ((memLp u).locallyIntegrableOn one_le_two) ((Lp.memLp F).locallyIntegrableOn one_le_two) hwd
    (forall_testFunction_weakDeriv_of_forall_testFunctions heq) hθ (ψ.ofLE hΩ')
  simp only [TestFunction.ofLE_coe] at hcut
  -- the integrals over `Ω` are integrals over `Ω'`
  have hsub : ∀ (F' : EuclideanSpace ℝ (Fin N) → ℝ),
      ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), F' x * ψ x
        = ∫ x in (Ω' : Set (EuclideanSpace ℝ (Fin N))), F' x * ψ x := fun F' ↦
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hΩm hΩ' fun x hx ↦ by
      rw [ψ.eq_zero_of_notMem hx.2, mul_zero]
  have hsub' : ∀ (F' : EuclideanSpace ℝ (Fin N) → ℝ) (i : Fin N),
      ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), F' x * fderiv ℝ ψ x (EuclideanSpace.single i 1)
        = ∫ x in (Ω' : Set (EuclideanSpace ℝ (Fin N))),
          F' x * fderiv ℝ ψ x (EuclideanSpace.single i 1) := fun F' i ↦
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hΩm hΩ' fun x hx ↦ by
      have := (ψ.fderivApply (EuclideanSpace.single i 1)).eq_zero_of_notMem hx.2
      rw [TestFunction.fderivApply_apply] at this
      rw [this, mul_zero]
  simp only [hsub, hsub'] at hcut
  exact hcut

end BoundaryPiece


/-! ### The determinant is smooth -/

section Det

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open scoped Matrix.Norms.Elementwise in
/-- **The determinant of a matrix is a smooth function of its entries**: a polynomial, by the
Leibniz formula `Matrix.det_apply'`. -/
theorem _root_.Matrix.contDiff_det {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ContDiff ℝ ∞ fun M : Matrix ι ι ℝ ↦ M.det := by
  simp_rw [Matrix.det_apply']
  refine ContDiff.sum fun σ _ ↦ ContDiff.mul contDiff_const (contDiff_prod fun i _ ↦ ?_)
  exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ι → ℝ) (σ i))).contDiff

open scoped Matrix.Norms.Elementwise in
/-- **The determinant of a continuous linear map on a finite-dimensional space is a smooth function
of the map**: `ContinuousLinearMap.det` is the determinant of the matrix of the map in a basis,
and the map to that matrix is linear. -/
theorem _root_.ContinuousLinearMap.contDiff_det :
    ContDiff ℝ ∞ fun f : E →L[ℝ] E ↦ f.det := by
  classical
  obtain ⟨b, -⟩ : ∃ b : Basis (Fin (Module.finrank ℝ E)) ℝ E, b = Module.finBasis ℝ E := ⟨_, rfl⟩
  have h : ∀ f : E →L[ℝ] E, f.det = Matrix.det (LinearMap.toMatrix b b (f : E →ₗ[ℝ] E)) :=
    fun f ↦ (LinearMap.det_toMatrix b _).symm
  simp_rw [h]
  refine Matrix.contDiff_det.comp ?_
  exact (LinearMap.toContinuousLinearMap ((LinearMap.toMatrix b b).toLinearMap.comp
    (ContinuousLinearMap.coeLM ℝ))).contDiff (n := ∞)

end Det

/-! ### Lemma 9.8: the coefficients of the transferred equation -/

section ChartCoeff

variable {N : ℕ}

/-- **The coefficients `a_{kℓ} = (∑_j ∂_jJ_k ∂_jJ_ℓ) ∘ H · |det Jac H|`** of the equation
satisfied by `w = v ∘ H` when `v` solves `−Δv = g` ([brezis2011functional] §9.6, Lemma 9.8),
for a diffeomorphism `H` with inverse `J`; `∂_jJ_k(x)` is the `k`-th coordinate of
`fderiv ℝ J x e_j`. -/
def chartCoeff (H J : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)) (k l : Fin N)
    (y : EuclideanSpace ℝ (Fin N)) : ℝ :=
  (∑ j, fderiv ℝ J (H y) (EuclideanSpace.single j 1) k
    * fderiv ℝ J (H y) (EuclideanSpace.single j 1) l) * |(fderiv ℝ H y).det|

/-- **The transferred datum `g̃ = (g ∘ H) |det Jac H|`** of [brezis2011functional] §9.6,
Lemma 9.8. -/
def chartDatum (H : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (g : EuclideanSpace ℝ (Fin N) → ℝ) (y : EuclideanSpace ℝ (Fin N)) : ℝ :=
  g (H y) * |(fderiv ℝ H y).det|

/-- The Jacobian determinant of a `C²` local diffeomorphism is `C¹` where it does not vanish. -/
theorem contDiffOn_abs_det_fderiv {H : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)}
    {s : Set (EuclideanSpace ℝ (Fin N))} (hs : IsOpen s) (hH : ContDiffOn ℝ 2 H s)
    (hdet : ∀ y ∈ s, (fderiv ℝ H y).det ≠ 0) :
    ContDiffOn ℝ 1 (fun y ↦ |(fderiv ℝ H y).det|) s := by
  have hdH : ContDiffOn ℝ 1 (fderiv ℝ H) s := hH.fderiv_of_isOpen hs (m := 1) (by norm_num)
  have h1 : ContDiffOn ℝ 1 (fun y ↦ (fderiv ℝ H y).det) s :=
    (ContinuousLinearMap.contDiff_det.of_le (by simp)).comp_contDiffOn hdH
  intro y hy
  refine (contDiffAt_abs (hdet y hy)).comp_contDiffWithinAt y (h1 y hy)

/-- The coefficients are `C¹` where `H` is `C²` with nonvanishing Jacobian and maps into a set on
which `J` is `C²`. -/
theorem contDiffOn_chartCoeff {H J : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)}
    {s t : Set (EuclideanSpace ℝ (Fin N))} (hs : IsOpen s) (ht : IsOpen t)
    (hH : ContDiffOn ℝ 2 H s) (hJ : ContDiffOn ℝ 2 J t) (hHs : MapsTo H s t)
    (hdet : ∀ y ∈ s, (fderiv ℝ H y).det ≠ 0) (k l : Fin N) :
    ContDiffOn ℝ 1 (chartCoeff H J k l) s := by
  have hdJ : ContDiffOn ℝ 1 (fderiv ℝ J) t := hJ.fderiv_of_isOpen ht (m := 1) (by norm_num)
  have hJH : ∀ j i, ContDiffOn ℝ 1 (fun y ↦ fderiv ℝ J (H y) (EuclideanSpace.single j 1) i) s := by
    intro j i
    have h1 : ContDiffOn ℝ 1 (fun y ↦ fderiv ℝ J (H y)) s :=
      hdJ.comp (hH.of_le (by norm_num)) hHs
    have h2 : ContDiffOn ℝ 1 (fun y ↦ fderiv ℝ J (H y) (EuclideanSpace.single j 1)) s :=
      h1.clm_apply contDiffOn_const
    exact (EuclideanSpace.proj i).contDiff.comp_contDiffOn h2
  exact (ContDiffOn.sum fun j _ ↦ (hJH j k).mul (hJH j l)).mul
    (contDiffOn_abs_det_fderiv hs hH hdet)

end ChartCoeff


/-! ### Lemma 9.8: ellipticity and boundedness of the coefficients -/

section ChartElliptic

variable {N : ℕ}

/-- A vector of `ℝ^N` is the sum of its coordinates times the basis vectors. -/
theorem _root_.EuclideanSpace.eq_sum_single_smul (z : EuclideanSpace ℝ (Fin N)) :
    z = ∑ k, z k • EuclideanSpace.single k (1 : ℝ) := by
  have := (EuclideanSpace.basisFun (Fin N) ℝ).sum_repr z
  simpa [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using this.symm

/-- The real inner product on `ℝ^N` is the sum of the products of the coordinates. -/
theorem _root_.EuclideanSpace.real_inner_eq_sum (x y : EuclideanSpace ℝ (Fin N)) :
    ⟪x, y⟫_ℝ = ∑ k, x k * y k := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun k _ ↦ by simp [RCLike.inner_apply, mul_comm]

/-- The chain rule for the inverse: `fderiv J (H y) ∘ fderiv H y = id` at a point of the source
of a `C¹` diffeomorphism. -/
theorem _root_.IsDiffeoOnWithBoundedJacobian.fderiv_invFun_comp_fderiv
    {H J : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)}
    {s t : Set (EuclideanSpace ℝ (Fin N))} {M : ℝ} (h : IsDiffeoOnWithBoundedJacobian H J s t M)
    {y : EuclideanSpace ℝ (Fin N)} (hy : y ∈ s) :
    (fderiv ℝ J (H y)).comp (fderiv ℝ H y) = ContinuousLinearMap.id ℝ _ := by
  have hH : HasFDerivAt H (fderiv ℝ H y) y :=
    ((h.contDiffOn.differentiableOn one_ne_zero).differentiableAt
      (h.isOpen_source.mem_nhds hy)).hasFDerivAt
  have hJ : HasFDerivAt J (fderiv ℝ J (H y)) (H y) :=
    ((h.contDiffOn_invFun.differentiableOn one_ne_zero).differentiableAt
      (h.isOpen_target.mem_nhds (h.bijOn.mapsTo hy))).hasFDerivAt
  have hcomp := hJ.comp y hH
  have hid : HasFDerivAt (J ∘ H) (ContinuousLinearMap.id ℝ _) y := by
    refine (hasFDerivAt_id y).congr_of_eventuallyEq ?_
    filter_upwards [h.isOpen_source.mem_nhds hy] with z hz
    exact h.invOn.1 hz
  exact hcomp.unique hid

/-- `det DJ(H y) · det DH(y) = 1` on the source of a diffeomorphism. -/
theorem _root_.IsDiffeoOnWithBoundedJacobian.det_fderiv_invFun_mul_det_fderiv
    {H J : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)}
    {s t : Set (EuclideanSpace ℝ (Fin N))} {M : ℝ} (h : IsDiffeoOnWithBoundedJacobian H J s t M)
    {y : EuclideanSpace ℝ (Fin N)} (hy : y ∈ s) :
    (fderiv ℝ J (H y)).det * (fderiv ℝ H y).det = 1 := by
  have := congrArg ContinuousLinearMap.det (h.fderiv_invFun_comp_fderiv hy)
  simpa [ContinuousLinearMap.det, LinearMap.det_comp] using this

/-- The Jacobian determinant of a diffeomorphism does not vanish on the source. -/
theorem _root_.IsDiffeoOnWithBoundedJacobian.det_fderiv_ne_zero
    {H J : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)}
    {s t : Set (EuclideanSpace ℝ (Fin N))} {M : ℝ} (h : IsDiffeoOnWithBoundedJacobian H J s t M)
    {y : EuclideanSpace ℝ (Fin N)} (hy : y ∈ s) : (fderiv ℝ H y).det ≠ 0 :=
  right_ne_zero_of_mul_eq_one (h.det_fderiv_invFun_mul_det_fderiv hy)

/-- **The quadratic form of the transferred coefficients**:
`∑_{kℓ} a_{kℓ}(y) ξ_k ξ_ℓ = |det DH(y)| ∑_j ⟪DJ(Hy) e_j, ξ⟫²`. -/
theorem sum_chartCoeff_mul_eq (H J : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (y ξ : EuclideanSpace ℝ (Fin N)) :
    ∑ k, ∑ l, chartCoeff H J k l y * ξ k * ξ l
      = |(fderiv ℝ H y).det| * ∑ j, ⟪fderiv ℝ J (H y) (EuclideanSpace.single j 1), ξ⟫_ℝ ^ 2 := by
  have e1 : ∀ k l, chartCoeff H J k l y * ξ k * ξ l = ∑ j, |(fderiv ℝ H y).det|
      * (fderiv ℝ J (H y) (EuclideanSpace.single j 1) k * ξ k)
      * (fderiv ℝ J (H y) (EuclideanSpace.single j 1) l * ξ l) := fun k l ↦ by
    simp only [chartCoeff, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  have e2 : ∀ j, ⟪fderiv ℝ J (H y) (EuclideanSpace.single j 1), ξ⟫_ℝ ^ 2
      = ∑ k, ∑ l, (fderiv ℝ J (H y) (EuclideanSpace.single j 1) k * ξ k)
        * (fderiv ℝ J (H y) (EuclideanSpace.single j 1) l * ξ l) := fun j ↦ by
    rw [EuclideanSpace.real_inner_eq_sum, sq, Finset.sum_mul_sum]
  simp only [e1, e2, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun k _ ↦ Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦
    Finset.sum_congr rfl fun l _ ↦ ?_
  ring

/-- **The transferred coefficients are elliptic** ([brezis2011functional] §9.6, Lemma 9.8:
"`∑ a_{kℓ} ξ_k ξ_ℓ = |det Jac H| ∑_j |∑_k ∂_jJ_k ξ_k|² ≥ α |ξ|²`"): for a `C¹` diffeomorphism
`H : s → t` with inverse `J` and Jacobians bounded by `M`, there is `α > 0` with
`α ‖ξ‖² ≤ ∑_{kℓ} a_{kℓ}(y) ξ_k ξ_ℓ` for all `y ∈ s` and `ξ`. Since `DJ(Hy) ∘ DH(y) = id`, every
coordinate `ξ_k = ∑_j (DH e_k)_j ⟪DJ e_j, ξ⟫`, so `‖ξ‖² ≤ N M² ∑_j ⟪DJ e_j, ξ⟫²` by
Cauchy–Schwarz, and `|det DH(y)| ≥ 1/(D+1)` for a bound `D` on `|det DJ|`. -/
theorem chartCoeff_elliptic {H J : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)}
    {s t : Set (EuclideanSpace ℝ (Fin N))} {M : ℝ} (h : IsDiffeoOnWithBoundedJacobian H J s t M) :
    ∃ α : ℝ, 0 < α ∧ ∀ y ∈ s, ∀ ξ : EuclideanSpace ℝ (Fin N),
      α * ‖ξ‖ ^ 2 ≤ ∑ k, ∑ l, chartCoeff H J k l y * ξ k * ξ l := by
  obtain ⟨D, hD0, hD⟩ := h.exists_abs_det_fderiv_invFun_le
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = N * max M 0 ^ 2 + 1 := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hK]; positivity
  refine ⟨1 / ((D + 1) * K), by positivity, fun y hy ξ ↦ ?_⟩
  rw [sum_chartCoeff_mul_eq]
  obtain ⟨A, hA⟩ : ∃ A, A = fderiv ℝ H y := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = fderiv ℝ J (H y) := ⟨_, rfl⟩
  rw [← hA, ← hB]
  have hBA : ∀ z, B (A z) = z := fun z ↦ by
    have := congrArg (fun L : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) ↦ L z)
      (h.fderiv_invFun_comp_fderiv hy)
    simpa [hA, hB] using this
  -- the coordinates of `ξ` through `B ∘ A = id`
  have hcoord : ∀ k, ξ k = ∑ j, A (EuclideanSpace.single k 1) j
      * ⟪B (EuclideanSpace.single j 1), ξ⟫_ℝ := by
    intro k
    have e1 : ξ k = ⟪B (A (EuclideanSpace.single k 1)), ξ⟫_ℝ := by
      rw [hBA, EuclideanSpace.inner_single_left]
      simp
    obtain ⟨c, hc⟩ : ∃ c : EuclideanSpace ℝ (Fin N), c = A (EuclideanSpace.single k 1) := ⟨_, rfl⟩
    rw [e1, ← hc]
    conv_lhs => rw [EuclideanSpace.eq_sum_single_smul c, map_sum, sum_inner]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_smul, real_inner_smul_left]
  -- Cauchy–Schwarz
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ j, ⟪B (EuclideanSpace.single j 1), ξ⟫_ℝ ^ 2 := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hAk : ∀ k, ∑ j, A (EuclideanSpace.single k 1) j ^ 2 ≤ max M 0 ^ 2 := fun k ↦ by
    rw [← EuclideanSpace.real_norm_sq_eq]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    refine (A.le_opNorm _).trans ?_
    rw [PiLp.norm_single, norm_one, mul_one, hA]
    exact (h.norm_fderiv_le y hy).trans (le_max_left _ _)
  have hξ : ‖ξ‖ ^ 2 ≤ K * S := by
    rw [EuclideanSpace.real_norm_sq_eq, hK]
    calc ∑ k, ξ k ^ 2
        = ∑ k, (∑ j, A (EuclideanSpace.single k 1) j
          * ⟪B (EuclideanSpace.single j 1), ξ⟫_ℝ) ^ 2 := by
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          rw [← hcoord k]
      _ ≤ ∑ k, (∑ j, A (EuclideanSpace.single k 1) j ^ 2)
          * ∑ j, ⟪B (EuclideanSpace.single j 1), ξ⟫_ℝ ^ 2 :=
          Finset.sum_le_sum fun k _ ↦ Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ ∑ _k : Fin N, max M 0 ^ 2 * S := by
          refine Finset.sum_le_sum fun k _ ↦ ?_
          rw [← hS]
          exact mul_le_mul_of_nonneg_right (hAk k) hS0
      _ ≤ (N * max M 0 ^ 2 + 1) * S := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          nlinarith [hS0]
  -- the determinant
  have hdet : 1 / (D + 1) ≤ |A.det| := by
    have h1 := h.det_fderiv_invFun_mul_det_fderiv hy
    rw [← hA, ← hB] at h1
    have hB' : |B.det| ≤ D := hB ▸ hD _ (h.bijOn.mapsTo hy)
    have hBpos : 0 < |B.det| := abs_pos.2 (left_ne_zero_of_mul_eq_one h1)
    have hAB : |B.det| * |A.det| = 1 := by rw [← abs_mul, h1, abs_one]
    rw [div_le_iff₀ (by positivity)]
    calc (1 : ℝ) = |B.det| * |A.det| := hAB.symm
      _ ≤ (D + 1) * |A.det| := by gcongr; linarith
      _ = |A.det| * (D + 1) := mul_comm _ _
  rw [← hS]
  calc 1 / ((D + 1) * K) * ‖ξ‖ ^ 2 ≤ 1 / ((D + 1) * K) * (K * S) := by gcongr
    _ = 1 / (D + 1) * S := by field_simp
    _ ≤ |A.det| * S := mul_le_mul_of_nonneg_right hdet hS0

/-- **The transferred coefficients are bounded on the source**: `|a_{kℓ}(y)| ≤ M₀` for `y ∈ s`,
by the Jacobian bounds and `ContinuousLinearMap.exists_abs_det_le_mul_norm_pow`. -/
theorem chartCoeff_bounded {H J : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)}
    {s t : Set (EuclideanSpace ℝ (Fin N))} {M : ℝ} (h : IsDiffeoOnWithBoundedJacobian H J s t M) :
    ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ k l, ∀ y ∈ s, |chartCoeff H J k l y| ≤ M₀ := by
  obtain ⟨D, hD0, hD⟩ := h.symm.exists_abs_det_fderiv_invFun_le
  refine ⟨N * max M 0 ^ 2 * D, by positivity, fun k l y hy ↦ ?_⟩
  have hJb : ∀ j i, |fderiv ℝ J (H y) (EuclideanSpace.single j 1) i| ≤ max M 0 := fun j i ↦ by
    rw [← Real.norm_eq_abs]
    refine (PiLp.norm_apply_le _ _).trans ?_
    refine ((fderiv ℝ J (H y)).le_opNorm _).trans ?_
    rw [PiLp.norm_single, norm_one, mul_one]
    exact (h.norm_fderiv_invFun_le _ (h.bijOn.mapsTo hy)).trans (le_max_left _ _)
  have hdet : |(fderiv ℝ H y).det| ≤ D := hD y hy
  rw [chartCoeff, abs_mul, abs_abs]
  calc |∑ j, fderiv ℝ J (H y) (EuclideanSpace.single j 1) k
        * fderiv ℝ J (H y) (EuclideanSpace.single j 1) l| * |(fderiv ℝ H y).det|
      ≤ (∑ _j : Fin N, max M 0 * max M 0) * D := by
        refine mul_le_mul ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum
          fun j _ ↦ ?_)) hdet (abs_nonneg _) (by positivity)
        rw [abs_mul]
        exact mul_le_mul (hJb j k) (hJb j l) (abs_nonneg _) (le_max_right _ _)
    _ = N * max M 0 ^ 2 * D := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end ChartElliptic


/-! ### Lemma 9.8: the transfer of the equation -/

section ChartTransfer

variable {N : ℕ} {Ω' Ω : Opens (EuclideanSpace ℝ (Fin N))}
  {H J : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)} {M : ℝ}

open SobolevMultiIndex

/-- A test function has its classical derivative as weak derivative. -/
theorem _root_.TestFunction.hasWeakFDerivOn (ψ : 𝓓(Ω', ℝ)) :
    HasWeakFDerivOn (ψ : EuclideanSpace ℝ (Fin N) → ℝ) (fderiv ℝ ψ) Ω' volume := by
  have := ContDiffOn.hasWeakIteratedFDerivOn (μ := volume) (ψ.contDiff.contDiffOn (s := Ω'))
    (m := 1) (by simp)
  unfold HasWeakFDerivOn
  refine this.congr_ae (EventuallyEq.refl _ _) (Eventually.of_forall fun x ↦ ?_)
  rw [iteratedFDeriv_one_eq_symm_fderiv]

/-- **The change of variables `x = H y` for integrals over the target of a diffeomorphism**:
`∫_Ω F = ∫_{Ω'} |det DH| F ∘ H` (Mathlib's
`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`). -/
theorem _root_.IsDiffeoOnWithBoundedJacobian.integral_eq_integral_abs_det_mul
    (h : IsDiffeoOnWithBoundedJacobian H J Ω' Ω M) (F : EuclideanSpace ℝ (Fin N) → ℝ) :
    ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), F x
      = ∫ y in (Ω' : Set (EuclideanSpace ℝ (Fin N))), |(fderiv ℝ H y).det| * F (H y) := by
  have hd : ∀ y ∈ (Ω' : Set (EuclideanSpace ℝ (Fin N))),
      HasFDerivWithinAt H (fderiv ℝ H y) Ω' y := fun y hy ↦
    ((h.contDiffOn.differentiableOn one_ne_zero).differentiableAt
      (h.isOpen_source.mem_nhds hy)).hasFDerivAt.hasFDerivWithinAt
  rw [← h.bijOn.image_eq, integral_image_eq_integral_abs_det_fderiv_smul volume
    Ω'.isOpen.measurableSet hd h.bijOn.injOn F]
  simp only [smul_eq_mul]

/-- **The pullback `ψ ∘ J` of a test function on `Ω'` is an element of `H^1_0(Ω)`** with the
derivatives `∂_j(ψ ∘ J) = ∇ψ(J x) (DJ(x) e_j)`: the transfer `φ(x) = ψ(J x)` of
[brezis2011functional] §9.6, proof of Lemma 9.8, which lies in `H^1_0(Ω ∩ Uᵢ)` because it
vanishes outside the compact `H(supp ψ)` (Lemma 9.5). -/
theorem exists_pullback_testFunction (h : IsDiffeoOnWithBoundedJacobian H J Ω' Ω M)
    (ψ : 𝓓(Ω', ℝ)) :
    ∃ Ψ : SobolevEuclidean N 1 2 Ω, Ψ ∈ SobolevEuclideanZero N 1 2 Ω ∧
      fn Ψ =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] (fun x ↦ ψ (J x)) ∧
      ∀ j, ⇑(weakDeriv Ψ (MultiIndexLE.single j))
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
          fun x ↦ fderiv ℝ ψ (J x) (fderiv ℝ J x (EuclideanSpace.single j 1)) := by
  obtain ⟨Φ, -, hΦ⟩ := ψ.exists_mem_sobolevMultiIndex_testFunctions
    (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis) (k := 1) (p := 2) (μ := volume)
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : SobolevEuclidean N 1 2 Ω,
      Ψ = SobolevEuclidean.compDiffeoL h.symm Φ := ⟨_, rfl⟩
  have hΨfn : fn Ψ =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fun x ↦ ψ (J x) := by
    rw [hΨ]
    refine (fn_compDiffeoL h.symm Φ).trans ?_
    filter_upwards [h.symm.ae_comp_restrict hΦ] with x hx
    exact hx
  have hΨd : ∀ j, ⇑(weakDeriv Ψ (MultiIndexLE.single j))
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        fun x ↦ fderiv ℝ ψ (J x) (fderiv ℝ J x (EuclideanSpace.single j 1)) := by
    intro j
    rw [hΨ]
    have hw : HasWeakFDerivOn (fn Φ) (fderiv ℝ ψ) Ω' volume :=
      ψ.hasWeakFDerivOn.congr_ae hΦ.symm (EventuallyEq.refl _ _)
    have := weakDeriv_compDiffeo_single h.symm Φ hw j
    rw [EuclideanSpace.basisFun_toBasis_apply] at this
    exact this
  refine ⟨Ψ, ?_, hΨfn, hΨd⟩
  -- `Ψ` vanishes outside the compact `H '' tsupport ψ ⊆ Ω`
  refine SobolevMultiIndex.mem_zero_of_ae_eq_zero_compl_isCompact ENNReal.ofNat_ne_top Ψ
    (K := H '' tsupport ψ) (ψ.hasCompactSupport.image_of_continuousOn
      (h.contDiffOn.continuousOn.mono ψ.tsupport_subset)) (h.image_subset ψ.tsupport_subset) ?_
  filter_upwards [hΨfn, self_mem_ae_restrict Ω.isOpen.measurableSet] with x hx hxΩ hxK
  rw [hx]
  by_contra hne
  have hmem : J x ∈ tsupport ψ := subset_tsupport _ hne
  exact hxK ⟨J x, hmem, h.invOn.2 hxΩ⟩

/-- **The partial derivatives of `v` through the transferred function**: for `w = v ∘ H` with a
tensor weak derivative `W` on `Ω'`, `∂_j v (x) = W(J x)(DJ(x) e_j)` almost everywhere on `Ω`
([brezis2011functional] §9.6, Lemma 9.8: "`∂v/∂x_j = ∑_k (∂w/∂y_k)(∂J_k/∂x_j)`"). -/
theorem weakDeriv_eq_of_compDiffeo (h : IsDiffeoOnWithBoundedJacobian H J Ω' Ω M)
    (v : SobolevEuclidean N 1 2 Ω)
    {W : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ}
    (hW : HasWeakFDerivOn (fn (SobolevEuclidean.compDiffeoL h v)) W Ω' volume) (j : Fin N) :
    ⇑(weakDeriv v (MultiIndexLE.single j))
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        fun x ↦ W (J x) (fderiv ℝ J x (EuclideanSpace.single j 1)) := by
  have hfn : (fun x ↦ fn (SobolevEuclidean.compDiffeoL h v) (J x))
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn v := by
    filter_upwards [h.symm.ae_comp_restrict (fn_compDiffeoL h v),
      self_mem_ae_restrict Ω.isOpen.measurableSet] with x hx hxΩ
    rw [hx, h.invOn.2 hxΩ]
  have h1 := (hW.comp_diffeoOn h.symm).congr_ae hfn (EventuallyEq.refl _ _)
  have h2 : HasWeakIteratedLineDerivOn ![EuclideanSpace.single j 1] (fn v)
      (fun x ↦ W (J x) (fderiv ℝ J x (EuclideanSpace.single j 1))) Ω volume := by
    have := (h1 : HasWeakIteratedFDerivOn 1 _ _ Ω volume).lineDeriv ![EuclideanSpace.single j 1]
    simpa using this
  exact (ae_restrict_iff' Ω.isOpen.measurableSet).2
    ((weakDeriv_hasWeakIteratedLineDerivOn_single v j).ae_eq h2)

end ChartTransfer


/-! ### Lemma 9.8: the transferred equation -/

section ChartEquation

variable {N : ℕ} {Ω' Ω : Opens (EuclideanSpace ℝ (Fin N))}
  {H J : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)} {M : ℝ}

open SobolevMultiIndex

/-- The product of two `L²` functions is integrable. -/
theorem _root_.MeasureTheory.MemLp.integrable_mul_two {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {f g : X → ℝ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    Integrable (fun x ↦ f x * g x) ν := by
  have : ENNReal.HolderTriple 2 2 1 := ⟨by rw [inv_one]; exact ENNReal.inv_two_add_inv_two⟩
  exact memLp_one_iff_integrable.1 (hf.fun_mul hg)

/-- A linear functional on `ℝ^N` evaluated at `z` is the sum of `z_k` times its values on the
basis vectors. -/
theorem _root_.ContinuousLinearMap.apply_eq_sum_single (L : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
    (z : EuclideanSpace ℝ (Fin N)) : L z = ∑ k, z k * L (EuclideanSpace.single k 1) := by
  conv_lhs => rw [EuclideanSpace.eq_sum_single_smul z, map_sum]
  simp only [map_smul, smul_eq_mul]

/-- The bounded factor `|det DH(y)| (DJ(Hy) e_j)_k (DJ(Hy) e_j)_l` of the transferred integrand is
continuous on the source and bounded there. -/
theorem exists_bound_chart_factor (h : IsDiffeoOnWithBoundedJacobian H J Ω' Ω M) (j k l : Fin N) :
    ContinuousOn (fun y ↦ |(fderiv ℝ H y).det| * fderiv ℝ J (H y) (EuclideanSpace.single j 1) k
      * fderiv ℝ J (H y) (EuclideanSpace.single j 1) l) Ω' ∧
    ∃ C : ℝ, ∀ y ∈ (Ω' : Set (EuclideanSpace ℝ (Fin N))),
      |(|(fderiv ℝ H y).det| * fderiv ℝ J (H y) (EuclideanSpace.single j 1) k
        * fderiv ℝ J (H y) (EuclideanSpace.single j 1) l)| ≤ C := by
  obtain ⟨D, -, hD⟩ := h.symm.exists_abs_det_fderiv_invFun_le
  have hdH : ContinuousOn (fun y ↦ |(fderiv ℝ H y).det|) Ω' :=
    (ContinuousLinearMap.continuous_det.comp_continuousOn
      (h.contDiffOn.continuousOn_fderiv_of_isOpen h.isOpen_source le_rfl)).abs
  have hdJ : ∀ i, ContinuousOn (fun y ↦ fderiv ℝ J (H y) (EuclideanSpace.single j 1) i) Ω' := by
    intro i
    have h1 : ContinuousOn (fun y ↦ fderiv ℝ J (H y)) Ω' :=
      (h.contDiffOn_invFun.continuousOn_fderiv_of_isOpen h.isOpen_target le_rfl).comp
        h.contDiffOn.continuousOn h.bijOn.mapsTo
    exact (EuclideanSpace.proj i).continuous.comp_continuousOn (h1.clm_apply continuousOn_const)
  refine ⟨(hdH.mul (hdJ k)).mul (hdJ l), D * max M 0 ^ 2, fun y hy ↦ ?_⟩
  have hJb : ∀ i, |fderiv ℝ J (H y) (EuclideanSpace.single j 1) i| ≤ max M 0 := fun i ↦ by
    rw [← Real.norm_eq_abs]
    refine (PiLp.norm_apply_le _ _).trans (((fderiv ℝ J (H y)).le_opNorm _).trans ?_)
    rw [PiLp.norm_single, norm_one, mul_one]
    exact (h.norm_fderiv_invFun_le _ (h.bijOn.mapsTo hy)).trans (le_max_left _ _)
  rw [abs_mul, abs_mul, abs_abs]
  calc |(fderiv ℝ H y).det| * |fderiv ℝ J (H y) (EuclideanSpace.single j 1) k|
        * |fderiv ℝ J (H y) (EuclideanSpace.single j 1) l|
      ≤ D * max M 0 * max M 0 :=
        mul_le_mul (mul_le_mul (hD y hy) (hJb k) (abs_nonneg _) ((abs_nonneg _).trans (hD y hy)))
          (hJb l) (abs_nonneg _) (mul_nonneg ((abs_nonneg _).trans (hD y hy)) (le_max_right _ _))
    _ = D * max M 0 ^ 2 := by ring

/-- **Lemma 9.8, the transferred equation** ([brezis2011functional] §9.6): let `v ∈ H^1(Ω)` satisfy
`∫_Ω ∇v · ∇Ψ = ∫_Ω G Ψ` for all `Ψ ∈ H^1_0(Ω)`, and let `w = v ∘ H ∈ H^1(Ω')` be its transfer
along the diffeomorphism `H : Ω' → Ω`. Then for every test function `ψ` on `Ω'`,

`∑_{kℓ} ∫_{Ω'} a_{kℓ} ∂_k w ∂_ℓ ψ = ∫_{Ω'} g̃ ψ`,

with `a_{kℓ} = chartCoeff H J k l` and `g̃ = chartDatum H G`. The equation is tested with the
pullback `ψ ∘ J ∈ H^1_0(Ω)` (`Elliptic.exists_pullback_testFunction`), the derivatives of `v` are
read through `w` (`Elliptic.weakDeriv_eq_of_compDiffeo`), and the integrals are transported by
the change of variables `x = H y`
(`IsDiffeoOnWithBoundedJacobian.integral_eq_integral_abs_det_mul`). -/
theorem sum_integral_chartCoeff_eq (h : IsDiffeoOnWithBoundedJacobian H J Ω' Ω M)
    {v : SobolevEuclidean N 1 2 Ω}
    {G : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ Ψ ∈ SobolevEuclideanZero N 1 2 Ω, dirichletForm Ω v Ψ = load Ω G Ψ)
    {w : SobolevEuclidean N 1 2 Ω'} (hw : w = SobolevEuclidean.compDiffeoL h v) (ψ : 𝓓(Ω', ℝ)) :
    ∑ k, ∑ l, ∫ y in (Ω' : Set (EuclideanSpace ℝ (Fin N))),
      chartCoeff H J k l y * weakDeriv w (MultiIndexLE.single k) y
        * fderiv ℝ ψ y (EuclideanSpace.single l 1)
      = ∫ y in (Ω' : Set (EuclideanSpace ℝ (Fin N))), chartDatum H G y * ψ y := by
  have hΩ'm : MeasurableSet (Ω' : Set (EuclideanSpace ℝ (Fin N))) := Ω'.isOpen.measurableSet
  obtain ⟨Ψ, hΨ0, hΨfn, hΨd⟩ := exists_pullback_testFunction h ψ
  have hΨeq := heq Ψ hΨ0
  rw [dirichletForm_apply_inner, load_apply_inner, L2.inner_eq_integral_mul] at hΨeq
  simp only [L2.inner_eq_integral_mul] at hΨeq
  obtain ⟨W, hW, -, hWi, -⟩ := exists_hasWeakFDerivOn_fn w
  simp only [EuclideanSpace.basisFun_toBasis_apply] at hWi
  have hvd := weakDeriv_eq_of_compDiffeo h v (hw ▸ hW)
  -- the derivatives of `ψ`, as functions
  obtain ⟨dψ, hdψ⟩ : ∃ dψ : Fin N → EuclideanSpace ℝ (Fin N) → ℝ,
      dψ = fun l y ↦ fderiv ℝ ψ y (EuclideanSpace.single l 1) := ⟨_, rfl⟩
  have hdψc : ∀ l, Continuous (dψ l) := fun l ↦ by
    rw [hdψ]; exact ((ψ.contDiff.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const).continuous
  have hdψs : ∀ l, HasCompactSupport (dψ l) := fun l ↦ by
    rw [hdψ]; exact ψ.hasCompactSupport.fderiv_apply ℝ _
  have hdψ2 : ∀ l, MemLp (dψ l) 2 (volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N)))) :=
    fun l ↦ ((hdψc l).memLp_of_hasCompactSupport (hdψs l)).restrict _
  -- integrability of the transferred terms
  have hint : ∀ j k l, Integrable (fun y ↦ (|(fderiv ℝ H y).det|
      * fderiv ℝ J (H y) (EuclideanSpace.single j 1) k
      * fderiv ℝ J (H y) (EuclideanSpace.single j 1) l) * weakDeriv w (MultiIndexLE.single k) y
      * dψ l y) (volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N)))) := by
    intro j k l
    obtain ⟨hc, C, hC⟩ := exists_bound_chart_factor h j k l
    have h1 := (hdψ2 l).mul_of_forall_abs_le (hc.aestronglyMeasurable hΩ'm) hC
    have h2 := h1.integrable_mul_two (Lp.memLp (weakDeriv w (MultiIndexLE.single k)))
    exact h2.congr (Eventually.of_forall fun y ↦ by ring)
  have hintW : ∀ j k l, Integrable (fun y ↦ (|(fderiv ℝ H y).det|
      * fderiv ℝ J (H y) (EuclideanSpace.single j 1) k
      * fderiv ℝ J (H y) (EuclideanSpace.single j 1) l) * W y (EuclideanSpace.single k 1)
      * dψ l y) (volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N)))) := fun j k l ↦
    (hint j k l).congr (by
      filter_upwards [hWi k] with y hy
      rw [hy])
  -- the left side, term by term
  have hL : ∀ j, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      weakDeriv v (MultiIndexLE.single j) x * weakDeriv Ψ (MultiIndexLE.single j) x
      = ∑ k, ∑ l, ∫ y in (Ω' : Set (EuclideanSpace ℝ (Fin N))),
        (|(fderiv ℝ H y).det| * fderiv ℝ J (H y) (EuclideanSpace.single j 1) k
          * fderiv ℝ J (H y) (EuclideanSpace.single j 1) l)
          * weakDeriv w (MultiIndexLE.single k) y * dψ l y := by
    intro j
    have e1 : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        weakDeriv v (MultiIndexLE.single j) x * weakDeriv Ψ (MultiIndexLE.single j) x
        = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          W (J x) (fderiv ℝ J x (EuclideanSpace.single j 1))
            * fderiv ℝ ψ (J x) (fderiv ℝ J x (EuclideanSpace.single j 1)) :=
      integral_congr_ae (by filter_upwards [hvd j, hΨd j] with x h1 h2; rw [h1, h2])
    rw [e1, h.integral_eq_integral_abs_det_mul]
    have e2 : ∀ y ∈ (Ω' : Set (EuclideanSpace ℝ (Fin N))),
        |(fderiv ℝ H y).det| * (W (J (H y)) (fderiv ℝ J (H y) (EuclideanSpace.single j 1))
          * fderiv ℝ ψ (J (H y)) (fderiv ℝ J (H y) (EuclideanSpace.single j 1)))
        = ∑ k, ∑ l, (|(fderiv ℝ H y).det| * fderiv ℝ J (H y) (EuclideanSpace.single j 1) k
          * fderiv ℝ J (H y) (EuclideanSpace.single j 1) l) * W y (EuclideanSpace.single k 1)
          * dψ l y := by
      intro y hy
      rw [h.invOn.1 hy, ContinuousLinearMap.apply_eq_sum_single (W y),
        ContinuousLinearMap.apply_eq_sum_single (fderiv ℝ ψ y), Finset.sum_mul_sum, Finset.mul_sum,
        hdψ]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      ring
    rw [setIntegral_congr_fun hΩ'm e2,
      integral_finsetSum _ fun k _ ↦ integrable_finsetSum _ fun l _ ↦ hintW j k l]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [integral_finsetSum _ fun l _ ↦ hintW j k l]
    refine Finset.sum_congr rfl fun l _ ↦ integral_congr_ae ?_
    filter_upwards [hWi k] with y hy
    rw [hy]
  -- the right side
  have hR : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), G x * weakDeriv Ψ 0 x
      = ∫ y in (Ω' : Set (EuclideanSpace ℝ (Fin N))), chartDatum H G y * ψ y := by
    have e1 : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), G x * weakDeriv Ψ 0 x
        = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), G x * ψ (J x) :=
      integral_congr_ae (by
        filter_upwards [hΨfn] with x hx
        rw [weakDeriv_zero, hx])
    rw [e1, h.integral_eq_integral_abs_det_mul]
    refine setIntegral_congr_fun hΩ'm fun y hy ↦ ?_
    rw [h.invOn.1 hy, chartDatum]
    ring
  rw [hR] at hΨeq
  simp only [hL] at hΨeq
  have hswap : ∑ j, ∑ k, ∑ l, ∫ y in (Ω' : Set (EuclideanSpace ℝ (Fin N))),
        (|(fderiv ℝ H y).det| * fderiv ℝ J (H y) (EuclideanSpace.single j 1) k
          * fderiv ℝ J (H y) (EuclideanSpace.single j 1) l)
          * weakDeriv w (MultiIndexLE.single k) y * dψ l y
      = ∑ k, ∑ l, ∑ j, ∫ y in (Ω' : Set (EuclideanSpace ℝ (Fin N))),
        (|(fderiv ℝ H y).det| * fderiv ℝ J (H y) (EuclideanSpace.single j 1) k
          * fderiv ℝ J (H y) (EuclideanSpace.single j 1) l)
          * weakDeriv w (MultiIndexLE.single k) y * dψ l y := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_comm
  rw [← hΨeq, hswap]
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
  rw [← integral_finsetSum _ fun j _ ↦ hint j k l]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  simp only [chartCoeff, hdψ, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  ring

end ChartEquation


/-! ### Lemma 9.8, typed: the transfer `H^1_0(Ω) → H^1_0(Q₊)` and the transferred problem -/

section ChartTyped

variable {N : ℕ} {Ω' Ω : Opens (EuclideanSpace ℝ (Fin N))}
  {H J : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)} {M : ℝ}

open SobolevMultiIndex

/-- **A continuous linear functional on `H^1(Ω)` vanishing on the test-function elements vanishes
on `H^1_0(Ω)`**, the closure of the test functions. -/
theorem apply_eq_zero_of_forall_testFunctions {L : SobolevEuclidean N 1 2 Ω →L[ℝ] ℝ}
    (h : ∀ φ ∈ testFunctions ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume, L φ = 0)
    {φ : SobolevEuclidean N 1 2 Ω} (hφ : φ ∈ SobolevEuclideanZero N 1 2 Ω) : L φ = 0 := by
  have hker : testFunctions ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
      ≤ LinearMap.ker (L : SobolevEuclidean N 1 2 Ω →ₗ[ℝ] ℝ) := fun ψ hψ ↦ by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    exact h ψ hψ
  have := Submodule.topologicalClosure_minimal _ hker L.isClosed_ker hφ
  rwa [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at this

/-- The equation `a(u, Ψ) = ∫ G Ψ` for the general form extends from the test-function elements
to `H^1_0(Ω)`. -/
theorem generalForm_eq_load_of_forall_testFunctions
    {A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    {u : SobolevEuclidean N 1 2 Ω}
    {G : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (h : ∀ φ ∈ testFunctions ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume,
      generalForm Ω A 0 0 u φ = load Ω G φ)
    {φ : SobolevEuclidean N 1 2 Ω} (hφ : φ ∈ SobolevEuclideanZero N 1 2 Ω) :
    generalForm Ω A 0 0 u φ = load Ω G φ := by
  have := apply_eq_zero_of_forall_testFunctions (L := generalForm Ω A 0 0 u - load Ω G)
    (fun ψ hψ ↦ by rw [sub_apply, h ψ hψ, sub_self]) hφ
  rwa [sub_apply, sub_eq_zero] at this

/-- **The transfer `v ↦ v ∘ H` maps `H^1_0(Ω)` into `H^1_0(Ω')`**: a test function on `Ω`
transfers to a `C¹` function vanishing outside the compact `J(supp φ) ⊆ Ω'`, which lies in
`H^1_0(Ω')` by Lemma 9.5, and the transfer is continuous. ([brezis2011functional] §9.6,
Lemma 9.8: "`w` belongs to `H^1_0(Q₊)`".) -/
theorem compDiffeoL_mem_zero (h : IsDiffeoOnWithBoundedJacobian H J Ω' Ω M)
    {v : SobolevEuclidean N 1 2 Ω} (hv : v ∈ SobolevEuclideanZero N 1 2 Ω) :
    SobolevEuclidean.compDiffeoL h v ∈ SobolevEuclideanZero N 1 2 Ω' := by
  obtain ⟨u, φ, huφ, hu⟩ := SobolevMultiIndexZero.exists_seq_testFunction_tendsto hv
  have hlim := ((SobolevEuclidean.compDiffeoL h).continuous.tendsto v).comp hu
  refine SobolevMultiIndexZero.isClosed.mem_of_tendsto hlim (Eventually.of_forall fun n ↦ ?_)
  -- `u n ∘ H` vanishes outside the compact `J '' tsupport (φ n) ⊆ Ω'`
  refine SobolevMultiIndex.mem_zero_of_ae_eq_zero_compl_isCompact ENNReal.ofNat_ne_top _
    (K := J '' tsupport (φ n)) ((φ n).hasCompactSupport.image_of_continuousOn
      (h.contDiffOn_invFun.continuousOn.mono (φ n).tsupport_subset))
    (h.symm.image_subset (φ n).tsupport_subset) ?_
  filter_upwards [fn_compDiffeoL h (u n), h.ae_comp_restrict (huφ n),
    self_mem_ae_restrict Ω'.isOpen.measurableSet] with y hy1 hy2 hyΩ' hyK
  refine (hy1.trans hy2).trans ?_
  by_contra hne
  exact hyK ⟨H y, subset_tsupport _ hne, h.invOn.1 hyΩ'⟩

/-- The transferred coefficients are continuous on the source. -/
theorem continuousOn_chartCoeff (h : IsDiffeoOnWithBoundedJacobian H J Ω' Ω M) (k l : Fin N) :
    ContinuousOn (chartCoeff H J k l) Ω' := by
  have : chartCoeff H J k l = fun y ↦ ∑ j, |(fderiv ℝ H y).det|
      * fderiv ℝ J (H y) (EuclideanSpace.single j 1) k
      * fderiv ℝ J (H y) (EuclideanSpace.single j 1) l := by
    funext y
    simp only [chartCoeff, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [this]
  exact continuousOn_finsetSum _ fun j _ ↦ (exists_bound_chart_factor h j k l).1

/-- The transferred coefficients are `L^∞` classes on the source. -/
theorem memLp_top_chartCoeff (h : IsDiffeoOnWithBoundedJacobian H J Ω' Ω M) (k l : Fin N) :
    MemLp (chartCoeff H J k l) ⊤ (volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N)))) := by
  obtain ⟨M₀, -, hM₀⟩ := chartCoeff_bounded h
  refine memLp_top_of_bound ((continuousOn_chartCoeff h k l).aestronglyMeasurable
    Ω'.isOpen.measurableSet) M₀ ?_
  filter_upwards [self_mem_ae_restrict Ω'.isOpen.measurableSet] with y hy
  rw [Real.norm_eq_abs]
  exact hM₀ k l y hy

/-- The transferred datum `g̃ = (G ∘ H) |det DH|` lies in `L²(Ω')`: `G ∘ H ∈ L²(Ω')` by the
transport of `L^p` norms (`IsDiffeoOnWithBoundedJacobian.memLp_comp`), and the Jacobian
determinant is bounded on the source. -/
theorem memLp_chartDatum (h : IsDiffeoOnWithBoundedJacobian H J Ω' Ω M)
    (G : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    MemLp (chartDatum H G) 2 (volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N)))) := by
  obtain ⟨D, -, hD⟩ := h.symm.exists_abs_det_fderiv_invFun_le
  have h1 : MemLp (fun y ↦ (G (H y) : ℝ)) 2
      (volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N)))) := by
    obtain ⟨D', -, hD'⟩ := h.exists_abs_det_fderiv_invFun_le
    have hG : MemLp G 2 (volume.restrict (H '' (Ω' : Set (EuclideanSpace ℝ (Fin N))))) := by
      rw [h.bijOn.image_eq]
      exact Lp.memLp G
    exact h.memLp_comp hD' h.isOpen_source subset_rfl hG
  have hdet : ContinuousOn (fun y ↦ |(fderiv ℝ H y).det|) Ω' :=
    (ContinuousLinearMap.continuous_det.comp_continuousOn
      (h.contDiffOn.continuousOn_fderiv_of_isOpen h.isOpen_source le_rfl)).abs
  have := MemLp.mul_of_forall_abs_le (hdet.aestronglyMeasurable Ω'.isOpen.measurableSet) (C := D)
    (fun y hy ↦ by rw [abs_abs]; exact hD y hy) h1
  exact this.ae_eq (Eventually.of_forall fun y ↦ by simp only [chartDatum]; ring)

/-- **Lemma 9.8, typed** ([brezis2011functional] §9.6): let `H : Ω' → Ω` be a `C¹`
diffeomorphism with bounded Jacobians and inverse `J`, and let `v ∈ H^1_0(Ω)` satisfy
`∫_Ω ∇v · ∇Ψ = ∫_Ω G Ψ` for all `Ψ ∈ H^1_0(Ω)`. Then `w = v ∘ H ∈ H^1_0(Ω')` and
`∑_{kℓ} ∫_{Ω'} a_{kℓ} ∂_k w ∂_ℓ Ψ = ∫_{Ω'} g̃ Ψ` for all `Ψ ∈ H^1_0(Ω')`, with the coefficients
`A_{kℓ}` the `L^∞(Ω')` classes of `chartCoeff H J k l` and `G̃` the `L²(Ω')` class of
`chartDatum H G`; the coefficients are elliptic (`Elliptic.chartCoeff_elliptic`). -/
theorem transfer_chart (h : IsDiffeoOnWithBoundedJacobian H J Ω' Ω M)
    {v : SobolevEuclidean N 1 2 Ω} (hv : v ∈ SobolevEuclideanZero N 1 2 Ω)
    {G : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ Ψ ∈ SobolevEuclideanZero N 1 2 Ω, dirichletForm Ω v Ψ = load Ω G Ψ) :
    ∃ (w : SobolevEuclidean N 1 2 Ω')
      (A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N)))))
      (G' : Lp ℝ 2 (volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N))))),
      w ∈ SobolevEuclideanZero N 1 2 Ω' ∧
      fn w =ᵐ[volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N)))] (fun y ↦ fn v (H y)) ∧
      (∀ k l, ⇑(A k l) =ᵐ[volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N)))]
        chartCoeff H J k l) ∧
      ∀ Ψ ∈ SobolevEuclideanZero N 1 2 Ω', generalForm Ω' A 0 0 w Ψ = load Ω' G' Ψ := by
  obtain ⟨w, hw⟩ : ∃ w, w = SobolevEuclidean.compDiffeoL h v := ⟨_, rfl⟩
  refine ⟨w, fun k l ↦ (memLp_top_chartCoeff h k l).toLp _, (memLp_chartDatum h G).toLp _,
    hw ▸ compDiffeoL_mem_zero h hv, hw ▸ fn_compDiffeoL h v,
    fun k l ↦ (memLp_top_chartCoeff h k l).coeFn_toLp, fun Ψ hΨ ↦ ?_⟩
  refine generalForm_eq_load_of_forall_testFunctions (fun Φ hΦ ↦ ?_) hΨ
  obtain ⟨ψ, hψ⟩ := hΦ
  rw [generalForm_zero_zero_apply_eq_of_ae_eq (fun k l ↦ (memLp_top_chartCoeff h k l).coeFn_toLp)
    w hψ, load_apply_eq_of_ae_eq (memLp_chartDatum h G).coeFn_toLp hψ]
  exact sum_integral_chartCoeff_eq h heq hw ψ

end ChartTyped


/-! ### Case C₂ on the model cylinder: extending the transferred problem to the half space

The transferred solution `w ∈ H^1_0(Q₊)` vanishes outside a compact subset `K` of the cylinder `Q`
(the support of the cut-off `θᵢ` is compact in `Uᵢ`, footnote 31 of [brezis2011functional]
§9.6). Its extension by zero `W` to the half space `ℝ^N_+` solves the equation with coefficients
`χ a_{kℓ} + (1 − χ) δ_{kℓ}`, for a cut-off `χ ∈ C_c^∞(Q)` equal to `1` near `K`: these are `C¹`,
bounded with bounded derivatives, elliptic, and the half space is invariant under the tangential
translations, so the case B theorem `Elliptic.exists_sobolevEuclidean_two_of_tangential` applies
and gives `W ∈ H²(ℝ^N_+)`, hence `w ∈ H²(Q₊)`. -/

section ExtendCoeff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {N : ℕ}

/-- **The coefficients `χ a_{kℓ} + (1 − χ) δ_{kℓ}`** extending an elliptic family from the support
of a cut-off `χ` to the whole space by the identity: the coefficients of the equation satisfied by
the zero extension of a solution supported where `χ = 1`. -/
def extendCoeff (χ : E → ℝ) (a : Fin N → Fin N → E → ℝ) (k l : Fin N) (y : E) : ℝ :=
  χ y * a k l y + (1 - χ y) * if k = l then 1 else 0

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem extendCoeff_of_eq_one {χ : E → ℝ} {a : Fin N → Fin N → E → ℝ} {k l : Fin N} {y : E}
    (hy : χ y = 1) : extendCoeff χ a k l y = a k l y := by
  simp [extendCoeff, hy]

omit [NormedSpace ℝ E] in
theorem extendCoeff_of_notMem_tsupport {χ : E → ℝ} {a : Fin N → Fin N → E → ℝ} {k l : Fin N}
    {y : E} (hy : y ∉ tsupport χ) : extendCoeff χ a k l y = if k = l then 1 else 0 := by
  simp [extendCoeff, image_eq_zero_of_notMem_tsupport hy]

/-- A `C^n` function with support in an open set `Q` times a `C^n` function on `Q` is `C^n`
everywhere. -/
theorem _root_.ContDiff.mul_contDiffOn_of_tsupport_subset {n : WithTop ℕ∞} {χ f : E → ℝ}
    (hχ : ContDiff ℝ n χ) {Q : Set E} (hQ : IsOpen Q) (hf : ContDiffOn ℝ n f Q)
    (hχQ : tsupport χ ⊆ Q) : ContDiff ℝ n fun y ↦ χ y * f y := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ Q
  · exact hχ.contDiffAt.mul ((hf y hy).contDiffAt (hQ.mem_nhds hy))
  · have hy' : y ∉ tsupport χ := fun h ↦ hy (hχQ h)
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hy'] with z hz
    rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]

theorem contDiff_extendCoeff {χ : E → ℝ} (hχ : ContDiff ℝ 1 χ) {Q : Set E} (hQ : IsOpen Q)
    {a : Fin N → Fin N → E → ℝ} (ha : ∀ k l, ContDiffOn ℝ 1 (a k l) Q) (hχQ : tsupport χ ⊆ Q)
    (k l : Fin N) : ContDiff ℝ 1 (extendCoeff χ a k l) :=
  (hχ.mul_contDiffOn_of_tsupport_subset hQ (ha k l) hχQ).add
    ((contDiff_const.sub hχ).mul contDiff_const)

/-- A finite family of reals has a common nonnegative bound. -/
theorem exists_forall_le_of_fin {n : ℕ} (C : Fin n → Fin n → ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ k l, C k l ≤ M :=
  ⟨∑ k, ∑ l, |C k l|, by positivity, fun k l ↦ (le_abs_self _).trans
    ((Finset.single_le_sum (f := fun l ↦ |C k l|) (fun l _ ↦ abs_nonneg (C k l))
      (Finset.mem_univ l)).trans
      (Finset.single_le_sum (f := fun k ↦ ∑ l, |C k l|)
        (fun k _ ↦ Finset.sum_nonneg fun l _ ↦ abs_nonneg (C k l)) (Finset.mem_univ k)))⟩

omit [NormedSpace ℝ E] in
/-- A continuous function equal to a constant off the compact support of `χ` is bounded. -/
theorem exists_forall_norm_le_of_continuous {G : Type*} [NormedAddCommGroup G] {χ : E → ℝ}
    {f : E → G} (hχc : HasCompactSupport χ) (hf : Continuous f) {c : G}
    (hfc : ∀ y, y ∉ tsupport χ → f y = c) : ∃ C, 0 ≤ C ∧ ∀ y, ‖f y‖ ≤ C := by
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn hχc hf.continuousOn
  refine ⟨max C ‖c‖, le_max_of_le_right (norm_nonneg c), fun y ↦ ?_⟩
  by_cases hy : y ∈ tsupport χ
  · exact (hC y hy).trans (le_max_left _ _)
  · rw [hfc y hy]
    exact le_max_right _ _

theorem exists_bound_extendCoeff {χ : E → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    {Q : Set E} (hQ : IsOpen Q) {a : Fin N → Fin N → E → ℝ}
    (ha : ∀ k l, ContDiffOn ℝ 1 (a k l) Q) (hχQ : tsupport χ ⊆ Q) :
    ∃ M₀, 0 ≤ M₀ ∧ ∀ k l y, |extendCoeff χ a k l y| ≤ M₀ := by
  have h : ∀ k l, ∃ C, 0 ≤ C ∧ ∀ y, ‖extendCoeff χ a k l y‖ ≤ C := fun k l ↦
    exists_forall_norm_le_of_continuous hχc (contDiff_extendCoeff hχ hQ ha hχQ k l).continuous
      (c := if k = l then 1 else 0) fun y hy ↦ extendCoeff_of_notMem_tsupport hy
  choose C hC0 hC using h
  obtain ⟨M₀, hM₀0, hM₀⟩ := exists_forall_le_of_fin C
  refine ⟨M₀, hM₀0, fun k l y ↦ ?_⟩
  have := hC k l y
  rw [Real.norm_eq_abs] at this
  exact this.trans (hM₀ k l)

theorem exists_bound_fderiv_extendCoeff {χ : E → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hχc : HasCompactSupport χ) {Q : Set E} (hQ : IsOpen Q) {a : Fin N → Fin N → E → ℝ}
    (ha : ∀ k l, ContDiffOn ℝ 1 (a k l) Q) (hχQ : tsupport χ ⊆ Q) :
    ∃ M, 0 ≤ M ∧ ∀ k l y, ‖fderiv ℝ (extendCoeff χ a k l) y‖ ≤ M := by
  have h : ∀ k l, ∃ C, 0 ≤ C ∧ ∀ y, ‖fderiv ℝ (extendCoeff χ a k l) y‖ ≤ C := fun k l ↦
    exists_forall_norm_le_of_continuous hχc
      ((contDiff_extendCoeff hχ hQ ha hχQ k l).continuous_fderiv one_ne_zero) (c := 0) fun y hy ↦ by
        have : extendCoeff χ a k l =ᶠ[𝓝 y] fun _ ↦ if k = l then (1 : ℝ) else 0 := by
          filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hy] with z hz
          exact extendCoeff_of_notMem_tsupport hz
        rw [this.fderiv_eq, fderiv_const_apply]
  choose C hC0 hC using h
  obtain ⟨M, hM0, hM⟩ := exists_forall_le_of_fin C
  exact ⟨M, hM0, fun k l y ↦ (hC k l y).trans (hM k l)⟩

/-- `∑_{kℓ} δ_{kℓ} ξ_k ξ_ℓ = ‖ξ‖²`. -/
theorem sum_ite_mul_eq_norm_sq (ξ : EuclideanSpace ℝ (Fin N)) :
    ∑ k, ∑ l, (if k = l then (1 : ℝ) else 0) * ξ k * ξ l = ‖ξ‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp [ite_mul, Real.norm_eq_abs, sq]

/-- **The extended coefficients are elliptic with constant `min α 1`** where `0 ≤ χ ≤ 1` and
`a` is elliptic with constant `α` on the part of the support of `χ` under consideration. -/
theorem extendCoeff_elliptic {χ : EuclideanSpace ℝ (Fin N) → ℝ} (hχ01 : ∀ y, χ y ∈ Icc (0 : ℝ) 1)
    {a : Fin N → Fin N → EuclideanSpace ℝ (Fin N) → ℝ} {T s : Set (EuclideanSpace ℝ (Fin N))}
    (hT : tsupport χ ∩ T ⊆ s) {α : ℝ}
    (hell : ∀ y ∈ s, ∀ ξ : EuclideanSpace ℝ (Fin N), α * ‖ξ‖ ^ 2 ≤ ∑ k, ∑ l, a k l y * ξ k * ξ l)
    {y : EuclideanSpace ℝ (Fin N)} (hy : y ∈ T) (ξ : EuclideanSpace ℝ (Fin N)) :
    min α 1 * ‖ξ‖ ^ 2 ≤ ∑ k, ∑ l, extendCoeff χ a k l y * ξ k * ξ l := by
  have hsum : ∑ k, ∑ l, extendCoeff χ a k l y * ξ k * ξ l
      = χ y * ∑ k, ∑ l, a k l y * ξ k * ξ l + (1 - χ y) * ‖ξ‖ ^ 2 := by
    rw [← sum_ite_mul_eq_norm_sq ξ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    simp only [extendCoeff]
    ring
  rw [hsum]
  obtain ⟨h0, h1⟩ := hχ01 y
  have h1' : 0 ≤ 1 - χ y := by linarith
  have hξ : 0 ≤ ‖ξ‖ ^ 2 := by positivity
  have e2 : min α 1 * ‖ξ‖ ^ 2 ≤ 1 * ‖ξ‖ ^ 2 := mul_le_mul_of_nonneg_right (min_le_right _ _) hξ
  by_cases hyχ : y ∈ tsupport χ
  · have e1 : min α 1 * ‖ξ‖ ^ 2 ≤ ∑ k, ∑ l, a k l y * ξ k * ξ l :=
      (mul_le_mul_of_nonneg_right (min_le_left _ _) hξ).trans (hell y (hT ⟨hyχ, hy⟩) ξ)
    nlinarith [mul_le_mul_of_nonneg_left e1 h0, mul_le_mul_of_nonneg_left e2 h1']
  · rw [image_eq_zero_of_notMem_tsupport hyχ]
    nlinarith

end ExtendCoeff

section ZeroExtension

variable {N : ℕ} {Ω' Ω : Opens (EuclideanSpace ℝ (Fin N))}

open SobolevMultiIndex

/-- **The extension by zero `H^1_0(Ω') → H^1_0(Ω)`, `Ω' ≤ Ω`**: for `w ∈ H^1_0(Ω')` there is
`W ∈ H^1_0(Ω)` with `W = 1_{Ω'} w` and `∂ᵢW = 1_{Ω'} ∂ᵢw` on `Ω` — the restriction to `Ω` of the
zero extension `SobolevEuclideanZero.extendZeroL` of Proposition 9.18; membership of `H^1_0(Ω)`
is by closure from the test functions of `Ω'`, which are test functions of `Ω`. -/
theorem exists_extendZero_mem_zero (hΩ' : Ω' ≤ Ω) {w : SobolevEuclidean N 1 2 Ω'}
    (hw : w ∈ SobolevEuclideanZero N 1 2 Ω') :
    ∃ W : SobolevEuclidean N 1 2 Ω, W ∈ SobolevEuclideanZero N 1 2 Ω ∧
      fn W =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        (Ω' : Set (EuclideanSpace ℝ (Fin N))).indicator (fn w) ∧
      ∀ i, ⇑(weakDeriv W (MultiIndexLE.single i))
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        (Ω' : Set (EuclideanSpace ℝ (Fin N))).indicator (weakDeriv w (MultiIndexLE.single i)) := by
  obtain ⟨P, hP⟩ : ∃ P : SobolevEuclideanZero N 1 2 Ω' →L[ℝ] SobolevEuclidean N 1 2 Ω,
      P = (restrictL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 volume
        (le_top (a := Ω))).comp (SobolevEuclideanZero.extendZeroL N 2 Ω') := ⟨_, rfl⟩
  have hPfn : ∀ z : SobolevEuclideanZero N 1 2 Ω',
      fn (P z) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        (Ω' : Set (EuclideanSpace ℝ (Fin N))).indicator
          (fn (z : SobolevEuclidean N 1 2 Ω')) := fun z ↦ by
    rw [hP, ContinuousLinearMap.comp_apply]
    exact (fn_restrictL _ _).trans (ae_restrict_of_ae (SobolevEuclideanZero.fn_extendZeroL z))
  have hPd : ∀ (z : SobolevEuclideanZero N 1 2 Ω') (i : Fin N),
      ⇑(weakDeriv (P z) (MultiIndexLE.single i))
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        (Ω' : Set (EuclideanSpace ℝ (Fin N))).indicator
          (weakDeriv (z : SobolevEuclidean N 1 2 Ω') (MultiIndexLE.single i)) := fun z i ↦ by
    rw [hP, ContinuousLinearMap.comp_apply]
    exact (weakDeriv_restrictL _ _ _).trans
      (ae_restrict_of_ae (SobolevEuclideanZero.weakDeriv_extendZeroL_single z i))
  refine ⟨P ⟨w, hw⟩, ?_, hPfn ⟨w, hw⟩, hPd ⟨w, hw⟩⟩
  obtain ⟨u, φ, huφ, hu⟩ := SobolevMultiIndexZero.exists_seq_testFunction_tendsto hw
  have huw : Tendsto (fun n ↦ (⟨u n, SobolevMultiIndexZero.testFunctions_le ⟨φ n, huφ n⟩⟩ :
      SobolevEuclideanZero N 1 2 Ω')) atTop (𝓝 ⟨w, hw⟩) := tendsto_subtype_rng.2 hu
  have hlim := (P.continuous.tendsto _).comp huw
  refine SobolevMultiIndexZero.isClosed.mem_of_tendsto hlim (Eventually.of_forall fun n ↦ ?_)
  refine SobolevMultiIndexZero.testFunctions_le ⟨(φ n).ofLE hΩ', ?_⟩
  refine (hPfn _).trans ?_
  have huφ' := (ae_restrict_iff' Ω'.isOpen.measurableSet).1 (huφ n)
  filter_upwards [ae_restrict_of_ae huφ'] with x hx
  by_cases hxΩ' : x ∈ (Ω' : Set (EuclideanSpace ℝ (Fin N)))
  · rw [Set.indicator_of_mem hxΩ', hx hxΩ']
    rfl
  · rw [Set.indicator_of_notMem hxΩ']
    exact ((φ n).eq_zero_of_notMem hxΩ').symm

/-- The partial derivatives of `w ∈ H^1(Ω')` vanish almost everywhere off a closed set off which
`w` vanishes: on the open set `Ω' ∖ K` the function is zero, and weak derivatives are unique. -/
theorem weakDeriv_ae_eq_zero_of_fn_ae_eq_zero {w : SobolevEuclidean N 1 2 Ω'}
    {K : Set (EuclideanSpace ℝ (Fin N))} (hK : IsClosed K)
    (hw : ∀ᵐ y ∂volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N))), y ∉ K → fn w y = 0)
    (i : Fin N) :
    ∀ᵐ y ∂volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N))),
      y ∉ K → weakDeriv w (MultiIndexLE.single i) y = 0 := by
  obtain ⟨V, hV⟩ : ∃ V : Opens (EuclideanSpace ℝ (Fin N)),
    V = ⟨(Ω' : Set (EuclideanSpace ℝ (Fin N))) \ K, Ω'.isOpen.sdiff hK⟩ := ⟨_, rfl⟩
  have hVΩ' : V ≤ Ω' := by
    rw [hV]
    exact sdiff_subset
  have hVm : MeasurableSet (V : Set (EuclideanSpace ℝ (Fin N))) := V.isOpen.measurableSet
  have h0 : fn w =ᵐ[volume.restrict (V : Set (EuclideanSpace ℝ (Fin N)))] 0 := by
    have := (ae_restrict_iff' Ω'.isOpen.measurableSet).1 hw
    rw [Filter.EventuallyEq, ae_restrict_iff' hVm]
    filter_upwards [this] with y hy hyV
    rw [hV] at hyV
    exact hy hyV.1 hyV.2
  have h1 := ((weakDeriv_hasWeakIteratedLineDerivOn_single w i).mono hVΩ').congr_ae h0
    (EventuallyEq.refl _ _)
  have h2 := h1.ae_eq HasWeakIteratedLineDerivOn.zero
  rw [ae_restrict_iff' Ω'.isOpen.measurableSet]
  filter_upwards [h2] with y hy hyΩ' hyK
  exact hy (by rw [hV]; exact ⟨hyΩ', hyK⟩)

/-- **The equation for the zero extension** on `Ω ≥ Ω'`: for `w ∈ H^1_0(Ω')` vanishing off the
compact `K ⊆ Q`, `Q ∩ Ω ⊆ Ω'`, solving `∑_{kℓ} ∫_{Ω'} a_{kℓ} ∂_k w ∂_ℓ ψ = ∫_{Ω'} g ψ` on
`H^1_0(Ω')`, and `W ∈ H^1(Ω)` with `∂ᵢW = 1_{Ω'} ∂ᵢw`, the extension `W` solves
`∑_{kℓ} ∫_Ω ã_{kℓ} ∂_k W ∂_ℓ ψ = ∫_Ω 1_{Ω'} χ g ψ` against the test functions of `Ω`, where
`ã = χ a + (1 − χ) δ` for a smooth `χ` supported in `Q` and equal to `1` on a neighbourhood of
`K`: the equation on `Ω'` is tested with `χ ψ`, and `∂_k w = 0` off `K`. -/
theorem sum_integral_extendCoeff_eq (hΩ' : Ω' ≤ Ω) {Q : Set (EuclideanSpace ℝ (Fin N))}
    (hQΩ' : Q ∩ Ω ⊆ Ω') {χ : EuclideanSpace ℝ (Fin N) → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχQ : tsupport χ ⊆ Q) {L : Set (EuclideanSpace ℝ (Fin N))} (hχ1 : EqOn χ 1 L)
    {K : Set (EuclideanSpace ℝ (Fin N))} (hK : IsClosed K) (hKL : K ⊆ interior L)
    {A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N))))}
    {a : Fin N → Fin N → EuclideanSpace ℝ (Fin N) → ℝ}
    (hAa : ∀ k l, ⇑(A k l) =ᵐ[volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N)))] a k l)
    {w : SobolevEuclidean N 1 2 Ω'}
    (hwK : ∀ᵐ y ∂volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N))), y ∉ K → fn w y = 0)
    {g : Lp ℝ 2 (volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ ψ ∈ SobolevEuclideanZero N 1 2 Ω', generalForm Ω' A 0 0 w ψ = load Ω' g ψ)
    {W : SobolevEuclidean N 1 2 Ω}
    (hWd : ∀ i, ⇑(weakDeriv W (MultiIndexLE.single i))
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      (Ω' : Set (EuclideanSpace ℝ (Fin N))).indicator (weakDeriv w (MultiIndexLE.single i)))
    (ψ : 𝓓(Ω, ℝ)) :
    ∑ k, ∑ l, ∫ y in (Ω : Set (EuclideanSpace ℝ (Fin N))), extendCoeff χ a k l y
        * weakDeriv W (MultiIndexLE.single k) y * fderiv ℝ ψ y (EuclideanSpace.single l 1)
      = ∫ y in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        (Ω' : Set (EuclideanSpace ℝ (Fin N))).indicator (fun y ↦ χ y * g y) y * ψ y := by
  have hΩ'm : MeasurableSet (Ω' : Set (EuclideanSpace ℝ (Fin N))) := Ω'.isOpen.measurableSet
  have hχΩ' : tsupport χ ∩ Ω ⊆ Ω' := fun y hy ↦ hQΩ' ⟨hχQ hy.1, hy.2⟩
  obtain ⟨ψ', hψ'⟩ : ∃ ψ' : 𝓓(Ω', ℝ), ψ' = ψ.contDiffMulOfSubset hχ hχΩ' := ⟨_, rfl⟩
  have hψ'c : ∀ y, ψ' y = χ y * ψ y := fun y ↦ by
    rw [hψ']
    rfl
  have hψ'd : ∀ y l, fderiv ℝ ψ' y (EuclideanSpace.single l 1)
      = χ y * fderiv ℝ ψ y (EuclideanSpace.single l 1)
        + ψ y * fderiv ℝ χ y (EuclideanSpace.single l 1) := by
    intro y l
    have : (ψ' : EuclideanSpace ℝ (Fin N) → ℝ) = fun y ↦ χ y * ψ y := funext hψ'c
    rw [this, fderiv_fun_mul (hχ.differentiable (by simp) y)
      (ψ.contDiff.differentiable (by simp) y)]
    simp only [add_apply, smul_apply, smul_eq_mul]
  have hK1 : ∀ y ∈ K, χ y = 1 ∧ fderiv ℝ χ y = 0 := fun y hy ↦ by
    have hnhds : χ =ᶠ[𝓝 y] fun _ ↦ 1 := Filter.eventuallyEq_of_mem
      (isOpen_interior.mem_nhds (hKL hy)) fun z hz ↦ hχ1 (interior_subset hz)
    exact ⟨hχ1 (interior_subset (hKL hy)), by rw [hnhds.fderiv_eq, fderiv_const_apply]⟩
  have hKw := fun i ↦ weakDeriv_ae_eq_zero_of_fn_ae_eq_zero hK hwK i
  have hkey := forall_testFunction_of_forall_mem_general hAa
    SobolevMultiIndexZero.testFunctions_le heq ψ'
  have hterm : ∀ k l, ∫ y in (Ω : Set (EuclideanSpace ℝ (Fin N))), extendCoeff χ a k l y
        * weakDeriv W (MultiIndexLE.single k) y * fderiv ℝ ψ y (EuclideanSpace.single l 1)
      = ∫ y in (Ω' : Set (EuclideanSpace ℝ (Fin N))), a k l y
        * weakDeriv w (MultiIndexLE.single k) y * fderiv ℝ ψ' y (EuclideanSpace.single l 1) := by
    intro k l
    have e1 : ∫ y in (Ω : Set (EuclideanSpace ℝ (Fin N))), extendCoeff χ a k l y
          * weakDeriv W (MultiIndexLE.single k) y * fderiv ℝ ψ y (EuclideanSpace.single l 1)
        = ∫ y in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          (Ω' : Set (EuclideanSpace ℝ (Fin N))).indicator (fun y ↦ extendCoeff χ a k l y
            * weakDeriv w (MultiIndexLE.single k) y
            * fderiv ℝ ψ y (EuclideanSpace.single l 1)) y := by
      refine integral_congr_ae ?_
      filter_upwards [hWd k] with y hy
      rw [hy]
      by_cases hyΩ' : y ∈ (Ω' : Set (EuclideanSpace ℝ (Fin N)))
      · rw [Set.indicator_of_mem hyΩ', Set.indicator_of_mem hyΩ']
      · rw [Set.indicator_of_notMem hyΩ', Set.indicator_of_notMem hyΩ', mul_zero, zero_mul]
    rw [e1, setIntegral_indicator hΩ'm, inter_eq_right.2 hΩ']
    refine integral_congr_ae ?_
    filter_upwards [hKw k] with y hy
    by_cases hyK : y ∈ K
    · obtain ⟨h1, h2⟩ := hK1 y hyK
      rw [extendCoeff_of_eq_one h1, hψ'd, h1, h2, one_mul, zero_apply,
        mul_zero, add_zero]
    · rw [hy hyK, mul_zero, zero_mul, mul_zero, zero_mul]
  rw [Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ hterm k l, hkey]
  have e2 : ∫ y in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        (Ω' : Set (EuclideanSpace ℝ (Fin N))).indicator (fun y ↦ χ y * g y) y * ψ y
      = ∫ y in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        (Ω' : Set (EuclideanSpace ℝ (Fin N))).indicator (fun y ↦ χ y * g y * ψ y) y := by
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    dsimp only
    by_cases hy : y ∈ (Ω' : Set (EuclideanSpace ℝ (Fin N)))
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, zero_mul]
  rw [e2, setIntegral_indicator hΩ'm, inter_eq_right.2 hΩ']
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  dsimp only
  rw [hψ'c]
  ring

end ZeroExtension

section CylinderRegularity

variable {d : ℕ} {Ω' Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

open SobolevMultiIndex

/-- **`H²` regularity of a compactly supported solution on a subset of a tangentially invariant
open set** — [brezis2011functional] Theorem 9.25, case C₂ on the model cylinder (67)–(69), in the
form used in the proof of the theorem: let `Ω` be invariant under the tangential translations
(the half space), `Ω' ≤ Ω` with `Q ∩ Ω ⊆ Ω'` for an open `Q` (the cylinder, `Ω' = Q₊`), let the
coefficients `A_{kℓ} ∈ L^∞(Ω')` have representatives `a_{kℓ}` of class `C¹` on `Q` and elliptic
on `Ω'`, and let `w ∈ H^1_0(Ω')` vanish off a compact `K ⊆ Q` and solve
`∑_{kℓ} ∫_{Ω'} a_{kℓ} ∂_k w ∂_ℓ ψ = ∫_{Ω'} g ψ` for all `ψ ∈ H^1_0(Ω')`. Then `w ∈ H²(Ω')`.

The extension by zero `W ∈ H^1_0(Ω)` solves the equation with the coefficients
`Elliptic.extendCoeff χ a` and the datum `1_{Ω'} χ g` (`Elliptic.sum_integral_extendCoeff_eq`),
which satisfy the hypotheses of the case B theorem
`Elliptic.exists_sobolevEuclidean_two_of_tangential`; the `H²` element on `Ω` restricts to
`Ω'`. -/
theorem memSobolevMultiIndex_two_of_tangential_of_compact
    (hΩ : ∀ j : Fin (d + 1), j ≠ Fin.last d → ∀ t : ℝ,
      IsTranslationInvariant (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))
        (t • EuclideanSpace.single j 1))
    (hΩ' : Ω' ≤ Ω) {Q : Set (EuclideanSpace ℝ (Fin (d + 1)))} (hQ : IsOpen Q)
    (hQΩ' : Q ∩ Ω ⊆ Ω')
    {A : Fin (d + 1) → Fin (d + 1) →
      Lp ℝ ⊤ (volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    {a : Fin (d + 1) → Fin (d + 1) → EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hAa : ∀ k l, ⇑(A k l) =ᵐ[volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin (d + 1))))] a k l)
    (ha : ∀ k l, ContDiffOn ℝ 1 (a k l) Q) {α : ℝ} (hα0 : 0 < α)
    (hell : ∀ y ∈ (Ω' : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      ∀ ξ : EuclideanSpace ℝ (Fin (d + 1)), α * ‖ξ‖ ^ 2 ≤ ∑ k, ∑ l, a k l y * ξ k * ξ l)
    {K : Set (EuclideanSpace ℝ (Fin (d + 1)))} (hK : IsCompact K) (hKQ : K ⊆ Q)
    {w : SobolevEuclidean (d + 1) 1 2 Ω'} (hw : w ∈ SobolevEuclideanZero (d + 1) 1 2 Ω')
    (hwK : ∀ᵐ y ∂volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      y ∉ K → fn w y = 0)
    {g : Lp ℝ 2 (volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    (heq : ∀ ψ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω', generalForm Ω' A 0 0 w ψ = load Ω' g ψ) :
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (fn w) 2 2 Ω'
      volume := by
  have hΩ'm : MeasurableSet (Ω' : Set (EuclideanSpace ℝ (Fin (d + 1)))) :=
    Ω'.isOpen.measurableSet
  -- the cut-off `χ`, equal to `1` on the compact `L ⊇ K`, supported in the compact `L' ⊆ Q`
  obtain ⟨L, hL, hKL, hLQ⟩ := exists_compact_between hK hQ hKQ
  obtain ⟨L', hL', hLL', hL'Q⟩ := exists_compact_between hL hQ hLQ
  obtain ⟨χ, hχ, hχ1, hχL', hχ01⟩ := hL.exists_contDiff_eqOn_one isOpen_interior hLL'
  have hχQ : tsupport χ ⊆ Q := hχL'.trans (interior_subset.trans hL'Q)
  have hχc : HasCompactSupport χ :=
    hL'.of_isClosed_subset (isClosed_tsupport χ) (hχL'.trans interior_subset)
  have hχ1' : ContDiff ℝ 1 χ := hχ.of_le (by simp)
  have hχΩ' : tsupport χ ∩ Ω ⊆ Ω' := fun y hy ↦ hQΩ' ⟨hχQ hy.1, hy.2⟩
  -- the extended coefficients
  obtain ⟨M₀, hM₀0, hM₀⟩ := exists_bound_extendCoeff hχ1' hχc hQ ha hχQ
  obtain ⟨M, hM0, hM⟩ := exists_bound_fderiv_extendCoeff hχ1' hχc hQ ha hχQ
  have hmem : ∀ k l, MemLp (extendCoeff χ a k l) ⊤
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) := fun k l ↦
    memLp_top_of_bound (contDiff_extendCoeff hχ1' hQ ha hχQ k l).continuous.aestronglyMeasurable
      M₀ (Eventually.of_forall fun y ↦ by
        rw [Real.norm_eq_abs]
        exact hM₀ k l y)
  -- the zero extension `W ∈ H^1_0(Ω)`
  obtain ⟨W, hW, hWfn, hWd⟩ := exists_extendZero_mem_zero hΩ' hw
  -- the extended datum
  have hgmem : MemLp ((Ω' : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator fun y ↦ χ y * g y) 2
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) := by
    rw [memLp_indicator_iff_restrict hΩ'm, Measure.restrict_restrict hΩ'm, inter_eq_left.2 hΩ']
    refine MemLp.mul_of_forall_abs_le hχ.continuous.aestronglyMeasurable (C := 1)
      (fun y _ ↦ ?_) (Lp.memLp g)
    rw [abs_le]
    exact ⟨by linarith [(hχ01 y).1], (hχ01 y).2⟩
  -- the equation on `Ω`
  have heq' : ∀ Ψ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω,
      generalForm Ω (fun k l ↦ (hmem k l).toLp _) 0 0 W Ψ = load Ω (hgmem.toLp _) Ψ := by
    intro Ψ hΨ
    refine generalForm_eq_load_of_forall_testFunctions (fun Φ hΦ ↦ ?_) hΨ
    obtain ⟨ψ, hψ⟩ := hΦ
    rw [generalForm_zero_zero_apply_eq_of_ae_eq (fun k l ↦ (hmem k l).coeFn_toLp) W hψ,
      load_apply_eq_of_ae_eq hgmem.coeFn_toLp hψ]
    exact sum_integral_extendCoeff_eq hΩ' hQΩ' hχ hχQ hχ1 hK.isClosed hKL hAa hwK heq hWd ψ
  -- `H²` regularity on `Ω`
  obtain ⟨U, hU, -⟩ := exists_sobolevEuclidean_two_of_tangential hΩ
    (fun k l ↦ (hmem k l).coeFn_toLp)
    (fun k l ↦ (contDiff_extendCoeff hχ1' hQ ha hχQ k l).contDiffOn)
    hM₀0 hM0 (fun k l x _ ↦ hM₀ k l x) (fun k l x _ ↦ hM k l x) (lt_min hα0 one_pos)
    (fun y hy ξ ↦ extendCoeff_elliptic hχ01 hχΩ' hell hy ξ) hW heq'
  -- restriction to `Ω'`
  have hU' := fn_restrictL hΩ' U
  refine (memSobolevMultiIndex (restrictL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
    2 2 volume hΩ' U)).congr_ae (hU'.trans ?_)
  have h1 := ae_restrict_of_ae_restrict_of_subset hΩ' hU
  have h2 := ae_restrict_of_ae_restrict_of_subset hΩ' hWfn
  filter_upwards [h1, h2, self_mem_ae_restrict hΩ'm] with y hy1 hy2 hyΩ'
  rw [hy1, hy2, Set.indicator_of_mem hyΩ']

end CylinderRegularity


/-! ### Transfer back: `H²` is preserved by the inverse chart -/

section Retransfer

variable {N : ℕ} {Ω' Ω : Opens (EuclideanSpace ℝ (Fin N))}
  {H J : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)} {M : ℝ}

open SobolevMultiIndex

/-- **A diffeomorphism with bounded Jacobians restricts to an open subset of its target.** -/
theorem _root_.IsDiffeoOnWithBoundedJacobian.restrict_target {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {H Hinv : E → E} {s t : Set E} {M : ℝ}
    (h : IsDiffeoOnWithBoundedJacobian H Hinv s t M) {t' : Set E} (ht' : IsOpen t')
    (ht't : t' ⊆ t) : IsDiffeoOnWithBoundedJacobian H Hinv (Hinv '' t') t' M where
  isOpen_source := h.symm.isOpen_image ht' ht't
  isOpen_target := ht'
  bijOn := by
    refine ⟨fun y hy ↦ ?_, h.bijOn.injOn.mono (h.symm.image_subset ht't), fun x hx ↦ ?_⟩
    · obtain ⟨x, hx, rfl⟩ := hy
      rw [h.invOn.2 (ht't hx)]
      exact hx
    · exact ⟨Hinv x, mem_image_of_mem _ hx, h.invOn.2 (ht't hx)⟩
  invOn := ⟨h.invOn.1.mono (h.symm.image_subset ht't), h.invOn.2.mono ht't⟩
  contDiffOn := h.contDiffOn.mono (h.symm.image_subset ht't)
  contDiffOn_invFun := h.contDiffOn_invFun.mono ht't
  norm_fderiv_le := fun y hy ↦ h.norm_fderiv_le y (h.symm.image_subset ht't hy)
  norm_fderiv_invFun_le := fun x hx ↦ h.norm_fderiv_invFun_le x (ht't hx)

/-- **`H¹(Ω)` is stable under multiplication by a `C¹` function bounded with bounded derivative
on `Ω`**: the product rule `HasWeakIteratedLineDerivOn.mul` at `p = q = 2`. -/
theorem _root_.MemSobolevMultiIndex.contDiffOn_mul {c f : EuclideanSpace ℝ (Fin N) → ℝ}
    (hc : ContDiffOn ℝ 1 c Ω) {C : ℝ}
    (hcC : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin N))), |c x| ≤ C)
    (hdc : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin N))), ‖fderiv ℝ c x‖ ≤ C)
    (hf : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis f 1 2 Ω volume) :
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (fun x ↦ c x * f x) 1 2 Ω
      volume := by
  have hΩm : MeasurableSet (Ω : Set (EuclideanSpace ℝ (Fin N))) := Ω.isOpen.measurableSet
  rw [memSobolevMultiIndex_one_iff] at hf ⊢
  obtain ⟨hfp, hfd⟩ := hf
  have hcm : AEStronglyMeasurable c (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    hc.continuousOn.aestronglyMeasurable hΩm
  refine ⟨MemLp.mul_of_forall_abs_le hcm hcC hfp, fun i ↦ ?_⟩
  obtain ⟨g, hg, hgp⟩ := hfd i
  rw [EuclideanSpace.basisFun_toBasis_apply] at hg ⊢
  have hdci : ContinuousOn (fun x ↦ fderiv ℝ c x (EuclideanSpace.single i 1)) Ω :=
    (hc.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl).clm_apply continuousOn_const
  have hdciC : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin N))),
      |fderiv ℝ c x (EuclideanSpace.single i 1)| ≤ C := fun x hx ↦ by
    rw [← Real.norm_eq_abs]
    refine ((fderiv ℝ c x).le_opNorm _).trans ?_
    rw [PiLp.norm_single, norm_one, mul_one]
    exact hdc x hx
  have h2 : (2 : ℝ≥0∞) ≠ ⊤ := ENNReal.ofNat_ne_top
  refine ⟨_, (hc.hasWeakIteratedLineDerivOn_single Ω i).mul rfl hg one_le_two h2 h2
    (hc.continuousOn.locallyMemLpOn 2) (hdci.locallyMemLpOn 2) hfp.locallyMemLpOn
    hgp.locallyMemLpOn, ?_⟩
  exact (MemLp.mul_of_forall_abs_le (hdci.aestronglyMeasurable hΩm) hdciC hfp).add
    (MemLp.mul_of_forall_abs_le hcm hcC hgp)

/-- **Transfer back: `H²` is preserved by the inverse chart** ([brezis2011functional] §9.6,
proof of Theorem 9.25: "by returning to `Ω ∩ Uᵢ`, `θᵢ u` belongs to `H²(Ω ∩ Uᵢ)`"). For a `C¹`
diffeomorphism `H : Ω' → Ω` with bounded Jacobians and inverse `J`, with `J` of class `C²` on an
open set `V` containing a compact `K ⊇ Ω`, and `w ∈ H²(Ω')`, the composite `w ∘ J ∈ H²(Ω)`.

Proposition 9.6 (`MemSobolev.comp_diffeoOn`) gives `w ∘ J ∈ H¹(Ω)` with
`∂ᵢ(w ∘ J) = ∑_k (∂_i J)_k · (∂_k w ∘ J)` (`HasWeakFDerivOn.comp_diffeoOn`); each `∂_k w ∘ J` is
in `H¹(Ω)` by Proposition 9.6 again, and each `(∂_i J)_k` is `C¹` on `V`, bounded with bounded
derivative on the compact `K`, so the products are in `H¹(Ω)`
(`MemSobolevMultiIndex.contDiffOn_mul`). -/
theorem memSobolevMultiIndex_two_comp_chart (h : IsDiffeoOnWithBoundedJacobian H J Ω' Ω M)
    {V : Set (EuclideanSpace ℝ (Fin N))} (hV : IsOpen V) (hJ : ContDiffOn ℝ 2 J V)
    {K : Set (EuclideanSpace ℝ (Fin N))} (hK : IsCompact K)
    (hΩK : (Ω : Set (EuclideanSpace ℝ (Fin N))) ⊆ K) (hKV : K ⊆ V)
    {w : EuclideanSpace ℝ (Fin N) → ℝ}
    (hw : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis w 2 2 Ω' volume) :
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (fun x ↦ w (J x)) 2 2 Ω
      volume := by
  have hΩV : (Ω : Set (EuclideanSpace ℝ (Fin N))) ⊆ V := hΩK.trans hKV
  -- the coefficients `c i k = (∂ᵢJ)_k`: `C¹` on `V`, bounded with bounded derivative on `K`
  obtain ⟨c, hc⟩ : ∃ c : Fin N → Fin N → EuclideanSpace ℝ (Fin N) → ℝ,
    c = fun i k x ↦ fderiv ℝ J x (EuclideanSpace.single i 1) k := ⟨_, rfl⟩
  have hdJ : ContDiffOn ℝ 1 (fderiv ℝ J) V := hJ.fderiv_of_isOpen hV (m := 1) (by norm_num)
  have hcV : ∀ i k, ContDiffOn ℝ 1 (c i k) V := fun i k ↦ by
    rw [hc]
    exact (EuclideanSpace.proj k).contDiff.comp_contDiffOn (hdJ.clm_apply contDiffOn_const)
  have hbound : ∀ i k, ∃ C, ∀ x ∈ K, |c i k x| ≤ C ∧ ‖fderiv ℝ (c i k) x‖ ≤ C := by
    intro i k
    obtain ⟨C₁, hC₁⟩ := hK.exists_bound_of_continuousOn ((hcV i k).continuousOn.mono hKV)
    obtain ⟨C₂, hC₂⟩ := hK.exists_bound_of_continuousOn
      (((hcV i k).continuousOn_fderiv_of_isOpen hV le_rfl).mono hKV)
    refine ⟨max C₁ C₂, fun x hx ↦ ⟨?_, (hC₂ x hx).trans (le_max_right _ _)⟩⟩
    have := hC₁ x hx
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  choose C hC using hbound
  -- `w ∈ H¹(Ω')`, its partial derivatives `g k ∈ H¹(Ω')`, and a tensor weak derivative `Dw`
  obtain ⟨hw1, hwd⟩ := memSobolevMultiIndex_succ_iff.1 hw
  choose g hg hgp using hwd
  simp only [EuclideanSpace.basisFun_toBasis_apply] at hg
  obtain ⟨u, hu⟩ : ∃ u : SobolevEuclidean N 1 2 Ω',
    fn u =ᵐ[volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N)))] w :=
    hw1.exists_sobolevMultiIndex
  obtain ⟨Dw, hDw, -, hDwi, -⟩ := exists_hasWeakFDerivOn_fn u
  have hDw' : HasWeakFDerivOn w Dw Ω' volume :=
    HasWeakIteratedFDerivOn.congr_ae hDw hu (EventuallyEq.refl _ _)
  have hDwg : ∀ k, (fun y ↦ Dw y (EuclideanSpace.single k 1))
      =ᵐ[volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N)))] g k := by
    intro k
    have h1 := (weakDeriv_hasWeakIteratedLineDerivOn_single u k).congr_ae hu
      (EventuallyEq.refl _ _)
    have h2 := (ae_restrict_iff' Ω'.isOpen.measurableSet).2 (h1.ae_eq (hg k))
    have h3 := hDwi k
    rw [EuclideanSpace.basisFun_toBasis_apply] at h3
    exact h3.trans h2
  -- the composite: `H¹` and the derivatives
  have hcomp := hDw'.comp_diffeoOn h.symm
  refine memSobolevMultiIndex_succ_iff.2
    ⟨(MemSobolev.comp_diffeoOn h.symm hw1.memSobolev).memSobolevMultiIndex, fun i ↦ ?_⟩
  rw [EuclideanSpace.basisFun_toBasis_apply]
  refine ⟨fun x ↦ ∑ k, c i k x * g k (J x), ?_, ?_⟩
  · have h1 := (hcomp : HasWeakIteratedFDerivOn 1 _ _ Ω volume).lineDeriv
      ![EuclideanSpace.single i 1]
    refine h1.congr_ae (EventuallyEq.refl _ _) ?_
    have hae : ∀ k, ∀ᵐ x ∂volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))),
        Dw (J x) (EuclideanSpace.single k 1) = g k (J x) := fun k ↦
      h.symm.ae_comp_restrict (hDwg k)
    filter_upwards [ae_all_iff.2 hae] with x hx
    simp only [continuousMultilinearCurryFin1_symm_apply, Matrix.cons_val_zero,
      ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.apply_eq_sum_single (Dw (J x))
      (fderiv ℝ J x (EuclideanSpace.single i 1))]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hx k, hc]
  · have hsum : (fun x ↦ ∑ k, c i k x * g k (J x)) = ∑ k, fun x ↦ c i k x * g k (J x) := by
      funext x
      simp only [Finset.sum_apply]
    rw [hsum]
    refine MemSobolevMultiIndex.finset_sum Finset.univ fun k _ ↦ ?_
    have hgJ : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
        (fun x ↦ g k (J x)) 1 2 Ω volume :=
      (MemSobolev.comp_diffeoOn h.symm (hgp k).memSobolev).memSobolevMultiIndex
    exact hgJ.contDiffOn_mul ((hcV i k).mono hΩV) (fun x hx ↦ (hC i k x (hΩK hx)).1)
      (fun x hx ↦ (hC i k x (hΩK hx)).2)

end Retransfer


/-! ### Case C₂: a boundary piece `θᵢ u` is in `H²(Ω)` -/

section BoundaryPieceTwo

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

open SobolevMultiIndex EuclideanSpace

/-- **A boundary piece of a weak solution is in `H²(Ω)`** — [brezis2011functional] §9.6, proof of
Theorem 9.25, case C₂: for a `C²` chart `H : Q → U` of `Ω`, a smooth `θ` with compact support in
`U`, and `u ∈ H^1_0(Ω)` with `∫_Ω ∇u · ∇Φ = ∫_Ω F Φ` for the test-function elements `Φ`, the
function `θ u` lies in `H²(Ω)`.

The steps of the book: `v = θ u ∈ H^1_0(Ω ∩ U)` solves `−Δv = g` there
(`Elliptic.exists_boundary_piece`); `w = v ∘ H ∈ H^1_0(Q₊)` solves the transferred elliptic
equation (`Elliptic.transfer_chart`, Lemma 9.8) and vanishes off the compact `H⁻¹(supp θ) ⊆ Q`;
the method of translations on the half space gives `w ∈ H²(Q₊)`
(`Elliptic.memSobolevMultiIndex_two_of_tangential_of_compact`); returning to `Ω ∩ U'` for an open
`U'` with `supp θ ⊆ U' ⋐ U` gives `θ u ∈ H²(Ω ∩ U')`
(`Elliptic.memSobolevMultiIndex_two_comp_chart`), and the zero extension across the edge of the
chart (`MemSobolevMultiIndex.indicator_smul_of_tsupport_subset`) gives `θ u ∈ H²(Ω)`. -/
theorem memSobolevMultiIndex_two_boundary_piece (c : ContDiffChart 2 (Ω : Set _))
    {θ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ)
    (hθU : tsupport θ ⊆ c.U) {u : SobolevEuclidean (d + 1) 1 2 Ω}
    (hu : u ∈ SobolevEuclideanZero (d + 1) 1 2 Ω)
    {F : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    (heq : ∀ Φ ∈ testFunctions ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume,
      dirichletForm Ω u Φ = load Ω F Φ) :
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (fun x ↦ θ x * fn u x) 2 2 Ω volume := by
  -- the open sets: `Ω ∩ U`, a smaller `Ω ∩ U'` with `supp θ ⊆ U' ⋐ U`, `Q₊`, and the half space
  obtain ⟨L, hL, hθL, hLU⟩ := exists_compact_between hθc c.isOpen_U hθU
  obtain ⟨Ω₁, hΩ₁⟩ : ∃ Ω₁ : Opens (EuclideanSpace ℝ (Fin (d + 1))),
    Ω₁ = ⟨c.U ∩ Ω, c.isOpen_U.inter Ω.isOpen⟩ := ⟨_, rfl⟩
  obtain ⟨Ω₂, hΩ₂⟩ : ∃ Ω₂ : Opens (EuclideanSpace ℝ (Fin (d + 1))),
    Ω₂ = ⟨interior L ∩ Ω, isOpen_interior.inter Ω.isOpen⟩ := ⟨_, rfl⟩
  obtain ⟨Qp, hQp⟩ : ∃ Qp : Opens (EuclideanSpace ℝ (Fin (d + 1))),
    Qp = ⟨unitChartCubePos d, isOpen_unitChartCubePos⟩ := ⟨_, rfl⟩
  have hΩ₁s : (Ω₁ : Set (EuclideanSpace ℝ (Fin (d + 1)))) = c.U ∩ Ω := by rw [hΩ₁]; rfl
  have hΩ₂s : (Ω₂ : Set (EuclideanSpace ℝ (Fin (d + 1)))) = interior L ∩ Ω := by rw [hΩ₂]; rfl
  have hQps : (Qp : Set (EuclideanSpace ℝ (Fin (d + 1)))) = unitChartCubePos d := by rw [hQp]; rfl
  have hΩ₁Ω : Ω₁ ≤ Ω := by rw [hΩ₁]; exact inter_subset_right
  have hΩ₂Ω₁ : Ω₂ ≤ Ω₁ := by
    rw [hΩ₁, hΩ₂]
    exact inter_subset_inter_left _ (interior_subset.trans hLU)
  have hΩ₂Ω : Ω₂ ≤ Ω := hΩ₂Ω₁.trans hΩ₁Ω
  have hLc : IsCompact (closure (interior L)) :=
    hL.of_isClosed_subset isClosed_closure (closure_minimal interior_subset hL.isClosed)
  -- the boundary piece `v = θ u ∈ H^1_0(Ω ∩ U)` and its equation
  have hθΩ₁ : tsupport θ ∩ Ω ⊆ Ω₁ := by
    rw [hΩ₁s]
    exact inter_subset_inter_left _ hθU
  obtain ⟨v, G, hv, hvfn, hveq⟩ := exists_boundary_piece hΩ₁Ω hθ hθc hθΩ₁ hu heq
  -- the chart as a diffeomorphism `Q₊ → Ω ∩ U`, and the transfer
  obtain ⟨M, h⟩ := c.isDiffeoOnWithBoundedJacobian_pos (by norm_num) Ω.isOpen
  have h' : IsDiffeoOnWithBoundedJacobian c.toFun c.invFun (Qp : Set _) (Ω₁ : Set _) M := by
    rw [hQps, hΩ₁s]; exact h
  obtain ⟨w, A, G', hw, hwfn, hAa, hweq⟩ := transfer_chart h' hv hveq
  -- `w` vanishes off the compact `K = H⁻¹(supp θ) ⊆ Q`
  obtain ⟨K, hK⟩ : ∃ K : Set (EuclideanSpace ℝ (Fin (d + 1))), K = c.invFun '' tsupport θ :=
    ⟨_, rfl⟩
  have hKc : IsCompact K := by
    rw [hK]
    exact hθc.image_of_continuousOn (c.contDiffOn_invFun.continuousOn.mono
      (hθU.trans subset_closure))
  have hKQ : K ⊆ unitChartCube d := by
    rw [hK]
    exact (c.mapsTo_invFun.mono_left hθU).image_subset
  have hwK : ∀ᵐ y ∂volume.restrict (Qp : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      y ∉ K → fn w y = 0 := by
    filter_upwards [hwfn, h'.ae_comp_restrict hvfn, self_mem_ae_restrict Qp.isOpen.measurableSet]
      with y hy1 hy2 hyQ hyK
    rw [hy1]
    rw [hy2]
    have hθy : θ (c.toFun y) = 0 := by
      by_contra hne
      refine hyK ?_
      rw [hK]
      refine ⟨c.toFun y, subset_tsupport _ hne, ?_⟩
      rw [hQps] at hyQ
      exact c.invFun_toFun (unitChartCubePos_subset hyQ)
    rw [hθy, zero_mul]
  -- `H²` on `Q₊` by the method of translations on the half space
  obtain ⟨M₀, hM₀⟩ := c.isDiffeoOnWithBoundedJacobian (by norm_num)
  have hH2 : ContDiffOn ℝ 2 c.toFun (unitChartCube d) := c.contDiffOn.mono subset_closure
  have hJ2 : ContDiffOn ℝ 2 c.invFun c.U := c.contDiffOn_invFun.mono subset_closure
  have ha : ∀ k l, ContDiffOn ℝ 1 (chartCoeff c.toFun c.invFun k l) (unitChartCube d) :=
    contDiffOn_chartCoeff isOpen_unitChartCube c.isOpen_U hH2 hJ2 c.mapsTo
      (fun y hy ↦ hM₀.det_fderiv_ne_zero hy)
  obtain ⟨α, hα0, hell⟩ := chartCoeff_elliptic h'
  have hQphalf : Qp ≤ upperHalfSpaceOpens d := by
    rw [hQp]
    exact fun y hy ↦ hy.2
  have hQΩ' : unitChartCube d ∩ (upperHalfSpaceOpens d : Set _) ⊆ Qp := by
    rw [hQps]
    exact fun y hy ↦ hy
  have hw2 := memSobolevMultiIndex_two_of_tangential_of_compact
    (fun j hj t ↦ upperHalfSpaceOpens_isTranslationInvariant j hj t) hQphalf isOpen_unitChartCube
    hQΩ' hAa ha hα0 hell hKc hKQ hw hwK hweq
  -- back to `Ω ∩ U'` through the restricted chart
  have hΩ₂Ω₁' : (Ω₂ : Set (EuclideanSpace ℝ (Fin (d + 1))))
      ⊆ (Ω₁ : Set (EuclideanSpace ℝ (Fin (d + 1)))) := hΩ₂Ω₁
  have hres := h'.restrict_target Ω₂.isOpen hΩ₂Ω₁'
  obtain ⟨Ω₃, hΩ₃⟩ : ∃ Ω₃ : Opens (EuclideanSpace ℝ (Fin (d + 1))),
    Ω₃ = ⟨c.invFun '' Ω₂, hres.isOpen_source⟩ := ⟨_, rfl⟩
  have hΩ₃s : (Ω₃ : Set _) = c.invFun '' Ω₂ := by rw [hΩ₃]; rfl
  have hres' : IsDiffeoOnWithBoundedJacobian c.toFun c.invFun (Ω₃ : Set _) (Ω₂ : Set _) M := by
    rw [hΩ₃s]; exact hres
  have hΩ₃Qp : Ω₃ ≤ Qp := by
    change (Ω₃ : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ (Qp : Set (EuclideanSpace ℝ (Fin (d + 1))))
    rw [hΩ₃s]
    exact h'.symm.image_subset hΩ₂Ω₁'
  have hΩ₂K : (Ω₂ : Set _) ⊆ closure (interior L) := by
    rw [hΩ₂s]
    exact inter_subset_left.trans subset_closure
  have hKU : closure (interior L) ⊆ c.U :=
    (closure_minimal interior_subset hL.isClosed).trans hLU
  have hback := memSobolevMultiIndex_two_comp_chart hres' c.isOpen_U hJ2 hLc hΩ₂K hKU
    (hw2.mono_set hΩ₃Qp)
  -- `fn w ∘ J = θ u` on `Ω ∩ U'`
  have hθu : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (fun x ↦ θ x * fn u x) 2 2 Ω₂ volume := by
    refine hback.congr_ae ?_
    have h1 := h'.symm.ae_comp_restrict hwfn
    have h2 := hvfn
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hΩ₂Ω₁' h1,
      ae_restrict_of_ae_restrict_of_subset hΩ₂Ω₁' h2,
      self_mem_ae_restrict Ω₂.isOpen.measurableSet] with x hx1 hx2 hxΩ₂
    rw [hx1]
    rw [h'.invOn.2 (hΩ₂Ω₁' hxΩ₂), hx2]
  -- zero extension across the edge of the chart
  obtain ⟨η, hη, hη1, hηc, hηL⟩ := exists_contDiff_eqOn_one_hasCompactSupport (Ω := ⟨interior L,
    isOpen_interior⟩) (hθc : IsCompact (tsupport θ)) hθL
  have hηΩ₂ : tsupport η ∩ Ω ⊆ Ω₂ := by
    rw [hΩ₂s]
    exact inter_subset_inter_left _ hηL
  have hext := MemSobolevMultiIndex.indicator_smul_of_tsupport_subset one_le_two hΩ₂Ω hη hηc hηΩ₂
    hθu
  refine hext.congr_ae ?_
  filter_upwards [self_mem_ae_restrict Ω.isOpen.measurableSet] with x hxΩ
  by_cases hx : x ∈ (Ω₂ : Set (EuclideanSpace ℝ (Fin (d + 1))))
  · rw [Set.indicator_of_mem hx, smul_eq_mul]
    by_cases hxθ : x ∈ tsupport θ
    · rw [hη1 hxθ, Pi.one_apply, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hxθ, zero_mul, mul_zero]
  · rw [Set.indicator_of_notMem hx]
    have hxθ : x ∉ tsupport θ := fun hxθ ↦ hx (by rw [hΩ₂s]; exact ⟨hθL hxθ, hxΩ⟩)
    rw [image_eq_zero_of_notMem_tsupport hxθ, zero_mul]

end BoundaryPieceTwo


/-! ### The interior piece `θ₀ u`, and the assembly of Theorem 9.25 -/

section InteriorPiece

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

open SobolevMultiIndex

/-- The datum `θ F − 2∇θ·∇u − (Δθ) u` lies in `L²(Ω)` for a smooth `θ` bounded with bounded first
and second derivatives. -/
theorem memLp_boundaryDatum_of_bounds {θ : EuclideanSpace ℝ (Fin N) → ℝ} (hθ : ContDiff ℝ ∞ θ)
    {C : ℝ} (hθb : ∀ x, |θ x| ≤ C) (hdθb : ∀ x, ‖fderiv ℝ θ x‖ ≤ C)
    (hΔb : ∀ x, |∑ i, fderiv ℝ (fun z ↦ fderiv ℝ θ z (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single i 1)| ≤ C)
    (u : SobolevEuclidean N 1 2 Ω)
    (F : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    MemLp (fun x ↦ θ x * F x
      - 2 * ∑ i, fderiv ℝ θ x (EuclideanSpace.single i 1) * weakDeriv u (MultiIndexLE.single i) x
      - (∑ i, fderiv ℝ (fun z ↦ fderiv ℝ θ z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1)) * fn u x) 2
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
  have hb : ∀ (α : EuclideanSpace ℝ (Fin N) → ℝ), Continuous α → (∀ x, |α x| ≤ C) →
      ∀ {f : EuclideanSpace ℝ (Fin N) → ℝ},
      MemLp f 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) →
      MemLp (fun x ↦ α x * f x) 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    fun α hα hαC f hf ↦ MemLp.mul_of_forall_abs_le hα.aestronglyMeasurable (fun x _ ↦ hαC x) hf
  have h1 := hb θ hθ.continuous hθb (Lp.memLp F)
  have h2 : ∀ i, MemLp (fun x ↦ fderiv ℝ θ x (EuclideanSpace.single i 1)
      * weakDeriv u (MultiIndexLE.single i) x) 2
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := fun i ↦
    hb _ ((hθ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const).continuous (fun x ↦ by
      rw [← Real.norm_eq_abs]
      refine ((fderiv ℝ θ x).le_opNorm _).trans ?_
      rw [PiLp.norm_single, norm_one, mul_one]
      exact hdθb x) (Lp.memLp _)
  have h2' : MemLp (fun x ↦ ∑ i, fderiv ℝ θ x (EuclideanSpace.single i 1)
      * weakDeriv u (MultiIndexLE.single i) x) 2
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    memLp_finsetSum Finset.univ (f := fun i x ↦ fderiv ℝ θ x (EuclideanSpace.single i 1)
      * weakDeriv u (MultiIndexLE.single i) x) fun i _ ↦ h2 i
  have h3 := hb _ (ContDiff.sum fun i _ ↦ contDiff_fderiv_fderiv_apply hθ
    (EuclideanSpace.single i 1)).continuous hΔb (memLp u)
  exact (h1.sub (h2'.const_mul 2)).sub h3

/-- **The interior piece `θ₀ u` is in `H²(Ω)`** — [brezis2011functional] §9.6, proof of
Theorem 9.25, case C₁: for a cut-off `θ₀` of `Ω` (smooth, bounded with bounded derivative,
supported off `∂Ω`) with bounded Laplacian, and `u ∈ H¹(Ω)` with `∫_Ω ∇u · ∇Φ = ∫_Ω F Φ` for the
test-function elements `Φ`, the function `θ₀ u` lies in `H²(Ω)`: its zero extension
`\overline{θ₀ u} ∈ H¹(ℝ^N)` solves `−Δ(θ₀u) = θ₀F − 2∇θ₀·∇u − (Δθ₀)u` on `ℝ^N`
(`Elliptic.sum_integral_indicator_cutoff_eq`), and case A applies. -/
theorem memSobolevMultiIndex_two_interior_piece {θ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hθ : IsSobolevCutoff Ω θ) {C : ℝ}
    (hΔb : ∀ x, |∑ i, fderiv ℝ (fun z ↦ fderiv ℝ θ z (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single i 1)| ≤ C)
    (u : SobolevEuclidean N 1 2 Ω)
    {F : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ Φ ∈ testFunctions ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume,
      dirichletForm Ω u Φ = load Ω F Φ) :
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
      (fun x ↦ θ x * fn u x) 2 2 Ω volume := by
  have hΩm : MeasurableSet (Ω : Set (EuclideanSpace ℝ (Fin N))) := Ω.isOpen.measurableSet
  obtain ⟨M, hM⟩ := hθ.exists_bound
  -- the zero extension `V = \overline{θ u} ∈ H¹(ℝ^N)`
  obtain ⟨V, hV⟩ : ∃ V : SobolevEuclidean N 1 2 ⊤,
    V = extendZeroMulL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 volume hθ u := ⟨_, rfl⟩
  have hVfn : fn V =ᵐ[volume]
      (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator fun x ↦ θ x * fn u x := by
    rw [hV]
    exact fn_extendZeroMulL hθ u
  have hVd : ∀ i, ⇑(weakDeriv V (MultiIndexLE.single i)) =ᵐ[volume]
      (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator fun x ↦
        θ x * weakDeriv u (MultiIndexLE.single i) x
          + fderiv ℝ θ x (EuclideanSpace.single i 1) * fn u x := fun i ↦ by
    rw [hV]
    have := weakDeriv_extendZeroMulL_single hθ u i
    rw [EuclideanSpace.basisFun_toBasis_apply] at this
    exact this
  -- the datum `1_Ω (θ F − 2∇θ·∇u − (Δθ) u) ∈ L²(ℝ^N)`
  have hG := memLp_boundaryDatum_of_bounds hθ.contDiff (C := max M C)
    (fun x ↦ (hM x).1.trans (le_max_left _ _)) (fun x ↦ (hM x).2.trans (le_max_left _ _))
    (fun x ↦ (hΔb x).trans (le_max_right _ _)) u F
  have hG' : MemLp ((Ω : Set (EuclideanSpace ℝ (Fin N))).indicator fun x ↦ θ x * F x
      - 2 * ∑ i, fderiv ℝ θ x (EuclideanSpace.single i 1) * weakDeriv u (MultiIndexLE.single i) x
      - (∑ i, fderiv ℝ (fun z ↦ fderiv ℝ θ z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1)) * fn u x) 2
      (volume.restrict
        ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) : Set (EuclideanSpace ℝ (Fin N)))) := by
    rw [Opens.coe_top, Measure.restrict_univ, memLp_indicator_iff_restrict hΩm]
    exact hG
  -- the equation on `ℝ^N`
  have heqV : ∀ Φ ∈ testFunctions ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2
      (⊤ : Opens (EuclideanSpace ℝ (Fin N))) volume,
      dirichletForm ⊤ V Φ = load ⊤ (hG'.toLp _) Φ := by
    intro Φ hΦ
    obtain ⟨ψ, hψ⟩ := hΦ
    rw [dirichletForm_apply_eq_of_ae_eq (fun i ↦ ae_restrict_of_ae (hVd i)) hψ,
      load_apply_eq_of_ae_eq hG'.coeFn_toLp hψ]
    simp only [Opens.coe_top, Measure.restrict_univ]
    exact sum_integral_indicator_cutoff_eq (fun i ↦ EuclideanSpace.single i (1 : ℝ))
      ((memLp u).locallyIntegrableOn one_le_two) ((Lp.memLp F).locallyIntegrableOn one_le_two)
      (fun i ↦ weakDeriv_hasWeakIteratedLineDerivOn_single u i)
      (forall_testFunction_weakDeriv_of_forall_testFunctions heq) hθ ψ
  have heqV' : ∀ Φ, dirichletForm ⊤ V Φ = load ⊤ (hG'.toLp _) Φ := fun Φ ↦
    dirichletForm_eq_load_of_forall_testFunctions heqV (by
      rw [SobolevEuclideanZero.eq_top (p := 2) ENNReal.ofNat_ne_top]
      exact Submodule.mem_top)
  have hV2 := regularity_top_memSobolevMultiIndex heqV'
  refine (hV2.mono_set le_top).congr_ae ?_
  filter_upwards [ae_restrict_of_ae hVfn, self_mem_ae_restrict hΩm] with x hx hxΩ
  rw [hx, Set.indicator_of_mem hxΩ]

end InteriorPiece

section Assembly

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

open SobolevMultiIndex

/-- **[brezis2011functional] Theorem 9.25 (regularity for the Dirichlet problem), the `H²`
membership**: let `Ω ⊆ ℝ^N` be open of class `C²` with bounded boundary, and let `u ∈ H^1_0(Ω)`
satisfy `∫_Ω ∇u · ∇Φ = ∫_Ω g Φ` for all `Φ ∈ H^1_0(Ω)` with `g ∈ L²(Ω)`. Then `u ∈ H²(Ω)`. (For
the book's `−Δu + u = f`, take `g = f − u`.)

The proof of the book: a finite atlas of charts `Hᵢ : Q → Uᵢ` covering the compact `Γ = ∂Ω`
(`IsContDiffChartDomain.exists_finite_atlas`), a partition of unity `θ₀, θᵢ` subordinate to it
(Lemma 9.3, `IsCompact.exists_contDiff_partitionOfUnity`), and `u = θ₀ u + ∑ᵢ θᵢ u` with the
interior piece `θ₀ u ∈ H²(Ω)` by case A (`Elliptic.memSobolevMultiIndex_two_interior_piece`) and
each boundary piece `θᵢ u ∈ H²(Ω)` by cases B and C₂
(`Elliptic.memSobolevMultiIndex_two_boundary_piece`). -/
theorem regularity_dirichlet_mem
    (hΩ : IsContDiffChartDomain 2 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    {u : SobolevEuclidean (d + 1) 1 2 Ω} (hu : u ∈ SobolevEuclideanZero (d + 1) 1 2 Ω)
    {g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    (heq : ∀ Φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω, dirichletForm Ω u Φ = load Ω g Φ) :
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (fn u) 2 2 Ω volume := by
  have heq' : ∀ Φ ∈ testFunctions ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume,
      dirichletForm Ω u Φ = load Ω g Φ := fun Φ hΦ ↦
    heq Φ (SobolevMultiIndexZero.testFunctions_le hΦ)
  -- the finite atlas and the partition of unity
  have hΓc : IsCompact (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_frontier hΓ
  obtain ⟨k, c, hcov⟩ := hΩ.exists_finite_atlas hΓ
  obtain ⟨θ₀, θ, hθ₀, hθ, hθ₀01, -, hsum, hθc, hθU, hθ₀Γ⟩ :=
    hΓc.exists_contDiff_partitionOfUnity (fun i ↦ (c i).isOpen_U) hcov
  -- the boundary pieces
  have hbdry : ∀ i, MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (fun x ↦ θ i x * fn u x) 2 2 Ω volume := fun i ↦
    memSobolevMultiIndex_two_boundary_piece (c i) (hθ i) (hθc i) (hθU i) hu heq'
  -- the interior piece: `θ₀ = 1 − G` with `G = ∑ᵢ θᵢ` smooth and compactly supported
  obtain ⟨G, hG⟩ : ∃ G : EuclideanSpace ℝ (Fin (d + 1)) → ℝ, G = fun x ↦ ∑ i, θ i x := ⟨_, rfl⟩
  have hGs : ContDiff ℝ ∞ G := by
    rw [hG]
    exact ContDiff.sum fun i _ ↦ hθ i
  have hGc : HasCompactSupport G := by
    refine (isCompact_iUnion fun i ↦ hθc i).of_isClosed_subset (isClosed_tsupport G) ?_
    refine closure_minimal ?_ (isClosed_iUnion_of_finite fun i ↦ isClosed_tsupport (θ i))
    rw [hG]
    exact (Finset.support_sum _ _).trans (Set.iUnion₂_subset fun i _ ↦
      subset_closure.trans (Set.subset_iUnion (fun i ↦ tsupport (θ i)) i))
  have hθ₀eq : θ₀ = fun x ↦ 1 - G x := funext fun x ↦ by
    rw [hG]
    linarith [hsum x]
  have hdθ₀ : ∀ x, fderiv ℝ θ₀ x = -fderiv ℝ G x := fun x ↦ by
    rw [hθ₀eq, fderiv_const_sub]
  obtain ⟨M₁, hM₁⟩ := (hGc.fderiv ℝ).exists_bound_of_continuous (hGs.continuous_fderiv (by simp))
  have hθ₀cut : IsSobolevCutoff Ω θ₀ :=
    ⟨hθ₀, ⟨max 1 M₁, fun x ↦ ⟨(abs_le.2 ⟨by linarith [(hθ₀01 x).1], (hθ₀01 x).2⟩).trans
      (le_max_left _ _), by
        rw [hdθ₀ x, norm_neg]
        exact (hM₁ x).trans (le_max_right _ _)⟩⟩, hθ₀Γ⟩
  obtain ⟨hΔc, hΔs, -⟩ := laplacianRep_props hGs hGc
  obtain ⟨M₂, hM₂⟩ := hΔs.exists_bound_of_continuous hΔc.continuous
  have hΔθ₀ : ∀ x, ∑ i, fderiv ℝ (fun z ↦ fderiv ℝ θ₀ z (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single i 1)
      = -∑ i, fderiv ℝ (fun z ↦ fderiv ℝ G z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1) := fun x ↦ by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have : (fun z ↦ fderiv ℝ θ₀ z (EuclideanSpace.single i 1))
        = fun z ↦ -(fderiv ℝ G z (EuclideanSpace.single i 1)) := funext fun z ↦ by
      rw [hdθ₀ z, neg_apply]
    rw [this, fderiv_fun_neg, neg_apply]
  have hΔb : ∀ x, |∑ i, fderiv ℝ (fun z ↦ fderiv ℝ θ₀ z (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single i 1)| ≤ M₂ := fun x ↦ by
    rw [hΔθ₀ x, abs_neg, ← Real.norm_eq_abs]
    exact hM₂ x
  have hint := memSobolevMultiIndex_two_interior_piece hθ₀cut hΔb u heq'
  -- the sum `u = θ₀ u + ∑ᵢ θᵢ u`
  have htot := hint.add (MemSobolevMultiIndex.finset_sum Finset.univ
    (f := fun i x ↦ θ i x * fn u x) fun i _ ↦ hbdry i)
  refine htot.congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [Pi.add_apply, Finset.sum_apply]
  rw [← Finset.sum_mul, ← add_mul, hsum x, one_mul]

end Assembly


/-! ### The estimate `‖u‖_{H²} ≤ C ‖f‖₂`, by the closed graph theorem -/

section ClosedGraph

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

open SobolevMultiIndex

/-- **The `H²` bound from the membership, by the closed graph theorem**: if a continuous linear
solution map `S : L²(Ω) → H¹(Ω)` takes every `f` to the function of some element of `H²(Ω)`, then
the `H²` element is bounded by `C ‖f‖₂`. The map `f ↦ U_f ∈ H²(Ω)` is linear (elements of `H²(Ω)`
are determined by their functions) and its graph is closed (`H² → L²` and `S` are continuous), so
it is bounded. This is the standard route to the constant of [brezis2011functional] Theorem 9.25,
whose proof tracks the constants through the pieces instead. -/
theorem exists_norm_le_of_forall_exists_sobolev_two
    {S : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) →L[ℝ]
      SobolevEuclidean N 1 2 Ω}
    (hS : ∀ f, ∃ U : SobolevEuclidean N 2 2 Ω,
      fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn (S f)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
      (U : SobolevEuclidean N 2 2 Ω),
      fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn (S f) → ‖U‖ ≤ C * ‖f‖ := by
  choose T hT using hS
  -- `T` is linear
  obtain ⟨Tₗ, hTₗ⟩ : ∃ Tₗ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) →ₗ[ℝ]
      SobolevEuclidean N 2 2 Ω, ∀ f, Tₗ f = T f := by
    refine ⟨{ toFun := T, map_add' := fun f g ↦ ?_, map_smul' := fun c f ↦ ?_ }, fun _ ↦ rfl⟩
    · refine SobolevMultiIndex.ext_of_fn_ae_eq ?_
      filter_upwards [hT (f + g), hT f, hT g, fn_add (S f) (S g), fn_add (T f) (T g)]
        with x h1 h2 h3 h4 h5
      rw [h1, map_add, h4, h5, Pi.add_apply, Pi.add_apply, h2, h3]
    · refine SobolevMultiIndex.ext_of_fn_ae_eq ?_
      simp only [RingHom.id_apply]
      filter_upwards [hT (c • f), hT f, fn_smul c (S f), fn_smul c (T f)] with x h1 h2 h3 h4
      rw [h1, map_smul, h3, h4, Pi.smul_apply, Pi.smul_apply, h2]
  -- its graph is closed
  have hcont : Continuous Tₗ := by
    refine Tₗ.continuous_of_seq_closed_graph fun u x y hux hTy ↦ ?_
    have h1 : Tendsto (fun n ↦ fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 2 Ω volume
        (Tₗ (u n))) atTop (𝓝 (fnL ℝ _ 2 2 Ω volume y)) :=
      ((fnL ℝ _ 2 2 Ω volume).continuous.tendsto y).comp hTy
    have h2 : Tendsto (fun n ↦ fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
        (S (u n))) atTop (𝓝 (fnL ℝ _ 1 2 Ω volume (S x))) :=
      ((fnL ℝ _ 1 2 Ω volume).continuous.tendsto _).comp ((S.continuous.tendsto x).comp hux)
    have h12 : (fun n ↦ fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 2 Ω volume (Tₗ (u n)))
        = fun n ↦ fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume (S (u n)) := by
      funext n
      refine Lp.ext ?_
      rw [hTₗ]
      exact hT (u n)
    rw [h12] at h1
    have h3 := tendsto_nhds_unique h1 h2
    refine (SobolevMultiIndex.ext_of_fn_ae_eq ?_).symm
    rw [hTₗ]
    refine (hT x).trans ?_
    have := congrArg (fun w : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) ↦
      (w : EuclideanSpace ℝ (Fin N) → ℝ)) h3
    exact Filter.EventuallyEq.of_eq this.symm
  obtain ⟨Tc, hTc⟩ : ∃ Tc : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) →L[ℝ]
      SobolevEuclidean N 2 2 Ω, Tc = ⟨Tₗ, hcont⟩ := ⟨_, rfl⟩
  refine ⟨‖Tc‖, norm_nonneg _, fun f U hU ↦ ?_⟩
  have hUT : U = Tc f := by
    refine SobolevMultiIndex.ext_of_fn_ae_eq (hU.trans ?_)
    have h1 : Tc f = T f := by
      rw [hTc]
      exact hTₗ f
    rw [h1]
    exact (hT f).symm
  rw [hUT]
  exact Tc.le_opNorm f

/-- The form of `−Δ + 1` is coercive on `H^1_0(Ω)`. -/
theorem laplaceForm_restrict_isCoercive :
    ((laplaceForm Ω).restrict (SobolevEuclideanZero N 1 2 Ω)).IsCoercive :=
  ⟨1, one_pos, fun v ↦ laplaceForm_isCoerciveWith_one Ω (v : SobolevEuclidean N 1 2 Ω)⟩

/-- A weak solution of `−Δu + u = f` on `H^1_0(Ω)` solves `∫_Ω ∇u · ∇Φ = ∫_Ω (f − u) Φ` on
`H^1_0(Ω)`. -/
theorem dirichletForm_eq_load_sub_of_isGalerkinSolution_laplace
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    {u : SobolevEuclidean N 1 2 Ω}
    (hu : IsGalerkinSolution (laplaceForm Ω) (load Ω f) (SobolevEuclideanZero N 1 2 Ω) u) :
    ∀ Φ ∈ SobolevEuclideanZero N 1 2 Ω,
      dirichletForm Ω u Φ = load Ω (f - weakDeriv u 0) Φ := by
  intro Φ hΦ
  have h := hu.2 Φ hΦ
  rw [laplaceForm_apply_inner, ← dirichletForm_apply_inner, load_apply_inner] at h
  rw [load_apply_inner, inner_sub_left]
  linarith

end ClosedGraph

section Main

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

open SobolevMultiIndex

/-- **[brezis2011functional] Theorem 9.25 (regularity for the Dirichlet problem), the `H²`
clause.** Let `Ω ⊆ ℝ^N` be open of class `C²` with bounded boundary. There is a constant `C`
such that for every `f ∈ L²(Ω)`, the weak solution `u ∈ H^1_0(Ω)` of `−Δu + u = f`
(`∫_Ω ∇u · ∇φ + ∫_Ω u φ = ∫_Ω f φ` for all `φ ∈ H^1_0(Ω)`) lies in `H²(Ω)`, and every
`U ∈ H²(Ω)` with function `u` has `‖U‖_{H²(Ω)} ≤ C ‖f‖_{L²(Ω)}`.

The membership is `Elliptic.regularity_dirichlet_mem` (the localisation of the book's proof:
case A for the interior piece, cases B and C₂ through the charts for the boundary pieces), and the
constant comes from the closed graph theorem applied to the map `f ↦ U ∈ H²(Ω)`
(`Elliptic.exists_norm_le_of_forall_exists_sobolev_two`). -/
theorem regularity_dirichlet
    (hΩ : IsContDiffChartDomain 2 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
        (u : SobolevEuclidean (d + 1) 1 2 Ω),
        IsGalerkinSolution (laplaceForm Ω) (load Ω f) (SobolevEuclideanZero (d + 1) 1 2 Ω) u →
        MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (fn u) 2 2 Ω
          volume ∧
        ∀ U : SobolevEuclidean (d + 1) 2 2 Ω,
          fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] fn u →
          ‖U‖ ≤ C * ‖f‖ := by
  have hmem : ∀ (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
      (u : SobolevEuclidean (d + 1) 1 2 Ω),
      IsGalerkinSolution (laplaceForm Ω) (load Ω f) (SobolevEuclideanZero (d + 1) 1 2 Ω) u →
      MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (fn u) 2 2 Ω
        volume := fun f u hu ↦
    regularity_dirichlet_mem hΩ hΓ hu.1 (dirichletForm_eq_load_sub_of_isGalerkinSolution_laplace hu)
  obtain ⟨S, hS⟩ : ∃ S : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) →L[ℝ]
      SobolevEuclidean (d + 1) 1 2 Ω, S = (SobolevEuclideanZero (d + 1) 1 2 Ω).subtypeL ∘L
        solutionMap Ω (laplaceForm Ω) laplaceForm_restrict_isCoercive := ⟨_, rfl⟩
  have hSf : ∀ f, IsGalerkinSolution (laplaceForm Ω) (load Ω f) (SobolevEuclideanZero (d + 1) 1 2 Ω)
      (S f) := fun f ↦ by
    rw [hS]
    exact isGalerkinSolution_solutionMap Ω (laplaceForm Ω) laplaceForm_restrict_isCoercive f
  obtain ⟨C, hC0, hC⟩ := exists_norm_le_of_forall_exists_sobolev_two (S := S) fun f ↦
    (hmem f (S f) (hSf f)).exists_sobolevMultiIndex
  refine ⟨C, hC0, fun f u hu ↦ ⟨hmem f u hu, fun U hU ↦ hC f U (hU.trans ?_)⟩⟩
  have : u = S f := by
    rw [hS]
    exact eq_solutionMap_of_isGalerkinSolution Ω (laplaceForm Ω) laplaceForm_restrict_isCoercive hu
  rw [this]

end Main


/-! ### Lemma 9.7: tangential derivatives of an `H² ∩ H^1_0` function are in `H^1_0` -/

section TangentialDeriv

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

open SobolevMultiIndex

/-- **The partial derivatives of an `H²` function are functions of `H¹` elements**: for
`U ∈ H²(Ω)` and `u ∈ H¹(Ω)` with the same function, each `∂ₖu` is the function of some
`V ∈ H¹(Ω)`. -/
theorem exists_sobolevEuclidean_one_fn_ae_eq_weakDeriv {U : SobolevEuclidean N 2 2 Ω}
    {u : SobolevEuclidean N 1 2 Ω}
    (hU : fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn u) (k : Fin N) :
    ∃ V : SobolevEuclidean N 1 2 Ω, fn V =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      weakDeriv u (MultiIndexLE.single k) := by
  obtain ⟨-, hd⟩ := memSobolevMultiIndex_succ_iff.1 (memSobolevMultiIndex U)
  obtain ⟨g, hg, hgm⟩ := hd k
  rw [EuclideanSpace.basisFun_toBasis_apply] at hg
  have h1 := (hg.congr_ae hU (EventuallyEq.refl _ _)).ae_eq
    (weakDeriv_hasWeakIteratedLineDerivOn_single u k)
  obtain ⟨V, hV⟩ := hgm.exists_sobolevMultiIndex
  exact ⟨V, hV.trans ((ae_restrict_iff' Ω.isOpen.measurableSet).2 h1)⟩

/-- **Lemma 9.7** ([brezis2011functional] §9.6): on an open set invariant under the translations
along a unit vector `y`, if `u ∈ H^1_0(Ω)` is the function of an element of `H²(Ω)`, then
`∂u/∂y` is the function of an element of `H^1_0(Ω)`. The difference quotients `D_{ty} u`,
`t → 0`, lie in `H^1_0(Ω)` and are bounded there (Lemma 9.6 applied to `u` and to its partial
derivatives), so a subsequence converges weakly in `H^1_0(Ω)`, and the limit is `∂u/∂y`
(`Elliptic.exists_hasWeakIteratedLineDerivOn_of_diffQuot_bounded`, the "delicate point" of the
book's proof). On the half space, `y = e_j` for `j ≠ N`. -/
theorem tangentialDeriv_mem_zero_of_sobolev_two {y : EuclideanSpace ℝ (Fin N)} (hy : ‖y‖ = 1)
    (hΩ : ∀ t : ℝ, IsTranslationInvariant (Ω : Set (EuclideanSpace ℝ (Fin N))) (t • y))
    {u : SobolevEuclidean N 1 2 Ω} (hu : u ∈ SobolevEuclideanZero N 1 2 Ω)
    {U : SobolevEuclidean N 2 2 Ω}
    (hU : fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn u) :
    ∃ w : SobolevEuclidean N 1 2 Ω, w ∈ SobolevEuclideanZero N 1 2 Ω ∧
      HasWeakIteratedLineDerivOn ![y] (fn u) (fn w) Ω volume := by
  -- the partial derivatives of `u` as elements of `H¹(Ω)`
  choose V hV using exists_sobolevEuclidean_one_fn_ae_eq_weakDeriv hU
  -- the sequence of difference quotients in `H^1_0(Ω)`
  obtain ⟨t, ht⟩ : ∃ t : ℕ → ℝ, t = fun n : ℕ ↦ 1 / ((n : ℝ) + 1) := ⟨_, rfl⟩
  have htpos : ∀ n, 0 < t n := fun n ↦ by
    rw [ht]
    positivity
  have ht1 : ∀ n, t n ≤ 1 := fun n ↦ by
    rw [ht]
    exact div_le_one_of_le₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (by positivity)
  have ht0 : Tendsto t atTop (𝓝 0) := by
    rw [ht]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨v, hv⟩ : ∃ v : ℕ → SobolevEuclideanZero N 1 2 Ω, ∀ n, (v n : SobolevEuclidean N 1 2 Ω)
      = diffQuotL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 volume (hΩ (t n)) u :=
    ⟨fun n ↦ ⟨_, diffQuotL_mem_zero (hΩ (t n)) hu⟩, fun n ↦ rfl⟩
  -- the bound, Lemma 9.6 componentwise
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = ‖u‖ + ∑ k, ‖V k‖ := ⟨_, rfl⟩
  have hbound : ∀ n, ‖v n‖ ≤ √(Fintype.card (MultiIndexLE (Fin N) 1)) * C := by
    intro n
    rw [← Submodule.norm_coe, hv n]
    refine norm_le_sqrt_card_mul_of_forall_norm_weakDeriv_le _ fun α ↦ ?_
    rw [weakDeriv_diffQuotL]
    have hseg := forall_add_smul_smul_mem hΩ (t n)
    rcases MultiIndexLE.eq_zero_or_exists_eq_single α with rfl | ⟨k, rfl⟩
    · have h1 := norm_diffQuotLp_fnL_le (hΩ (t n)) hseg u
      rw [fnL_eq_weakDeriv_zero] at h1
      rw [hC]
      exact h1.trans ((gradNorm_le_norm u).trans
        (le_add_of_nonneg_right (Finset.sum_nonneg fun k _ ↦ norm_nonneg _)))
    · have hVk : weakDeriv u (MultiIndexLE.single k)
          = fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume (V k) :=
        Lp.ext (hV k).symm
      rw [hVk]
      refine (norm_diffQuotLp_fnL_le (hΩ (t n)) hseg (V k)).trans ((gradNorm_le_norm _).trans ?_)
      rw [hC]
      calc ‖V k‖ ≤ ∑ k, ‖V k‖ :=
            Finset.single_le_sum (f := fun k ↦ ‖V k‖) (fun _ _ ↦ norm_nonneg _)
              (Finset.mem_univ k)
        _ ≤ ‖u‖ + ∑ k, ‖V k‖ := le_add_of_nonneg_left (norm_nonneg _)
  -- weak compactness in `H^1_0(Ω)`
  obtain ⟨w, -, hw⟩ := exists_hasWeakIteratedLineDerivOn_of_diffQuot_bounded
    (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume)
    ((memLp u).locallyIntegrableOn one_le_two) hy hΩ htpos ht1 ht0 hbound fun n ↦ by
      rw [SobolevMultiIndexZero.fnL_apply, hv n]
      exact fn_diffQuotL (hΩ (t n)) u
  exact ⟨w, w.2, hw⟩

end TangentialDeriv


/-! ### Lemmas 9.6 and 9.7 on the half space, in the book's form -/

section HalfSpaceLemmas

variable {d : ℕ}

open SobolevMultiIndex EuclideanSpace

/-- **Lemma 9.6** ([brezis2011functional] §9.6), on the half space: for `v ∈ H¹(ℝ^N_+)` and `h`
parallel to the boundary, `‖D_h v‖_{L²(ℝ^N_+)} ≤ ‖∇v‖_{L²(ℝ^N_+)}`. The typed form, on any open
set invariant under the translations along `h`, is `Elliptic.norm_diffQuotLp_fnL_le`. -/
theorem eLpNorm_diffQuot_le_of_tangential {h : EuclideanSpace ℝ (Fin (d + 1))}
    (hh : h (Fin.last d) = 0) (v : SobolevEuclidean (d + 1) 1 2 (upperHalfSpaceOpens d)) :
    eLpNorm (diffQuot h (fn v)) 2
        (volume.restrict (upperHalfSpaceOpens d : Set (EuclideanSpace ℝ (Fin (d + 1)))))
      ≤ ENNReal.ofReal (gradNorm v) := by
  have hΩ' : ∀ t : ℝ, IsTranslationInvariant
      (upperHalfSpaceOpens d : Set (EuclideanSpace ℝ (Fin (d + 1)))) (t • h) :=
    isTranslationInvariant_upperHalfSpace hh
  have hΩ : IsTranslationInvariant
      (upperHalfSpaceOpens d : Set (EuclideanSpace ℝ (Fin (d + 1)))) h := by
    have := hΩ' 1
    rwa [one_smul] at this
  have hseg : ∀ x ∈ (upperHalfSpaceOpens d : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      ∀ t ∈ Icc (0 : ℝ) 1, x + t • h ∈ upperHalfSpaceOpens d := fun x hx t ht ↦ by
    have := forall_add_smul_smul_mem hΩ' 1 x hx t ht
    rwa [one_smul] at this
  have h1 := norm_diffQuotLp_fnL_le hΩ hseg v
  have hae := coeFn_diffQuotLp hΩ (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2
    (upperHalfSpaceOpens d) volume v)
  rw [fnL_apply] at hae
  rw [Lp.norm_def, eLpNorm_congr_ae hae] at h1
  have hne : eLpNorm (diffQuot h (fn v)) 2
      (volume.restrict (upperHalfSpaceOpens d : Set (EuclideanSpace ℝ (Fin (d + 1))))) ≠ ⊤ :=
    ((Lp.memLp _).ae_eq hae).eLpNorm_ne_top
  calc eLpNorm (diffQuot h (fn v)) 2
        (volume.restrict (upperHalfSpaceOpens d : Set (EuclideanSpace ℝ (Fin (d + 1)))))
      = ENNReal.ofReal (eLpNorm (diffQuot h (fn v)) 2
          (volume.restrict
            (upperHalfSpaceOpens d : Set (EuclideanSpace ℝ (Fin (d + 1)))))).toReal :=
        (ENNReal.ofReal_toReal hne).symm
    _ ≤ ENNReal.ofReal (gradNorm v) := ENNReal.ofReal_le_ofReal h1

/-- **Lemma 9.7** ([brezis2011functional] §9.6), on the half space: if `u ∈ H^1_0(ℝ^N_+)` is
the weak solution of `−Δu = g`, `g ∈ L²(ℝ^N_+)`, then every tangential derivative `∂_j u`,
`j ≠ N`, is the function of an element of `H^1_0(ℝ^N_+)`. Case B
(`Elliptic.regularity_upperHalfSpace`) gives `u ∈ H²(ℝ^N_+)`, and
`Elliptic.tangentialDeriv_mem_zero_of_sobolev_two` is the "delicate point" of the book's
proof. (Equation (58), the equation satisfied by `∂_j u` when `g ∈ H¹`, is not included.) -/
theorem tangentialDeriv_mem_zero_of_isGalerkinSolution
    {u : SobolevEuclidean (d + 1) 1 2 (upperHalfSpaceOpens d)}
    {g : Lp ℝ 2 (volume.restrict (upperHalfSpaceOpens d : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    (hu : IsGalerkinSolution (dirichletForm (upperHalfSpaceOpens d))
      (load (upperHalfSpaceOpens d) g) (SobolevEuclideanZero (d + 1) 1 2 (upperHalfSpaceOpens d)) u)
    {j : Fin (d + 1)} (hj : j ≠ Fin.last d) :
    ∃ w : SobolevEuclidean (d + 1) 1 2 (upperHalfSpaceOpens d),
      w ∈ SobolevEuclideanZero (d + 1) 1 2 (upperHalfSpaceOpens d) ∧
      HasWeakIteratedLineDerivOn ![EuclideanSpace.single j 1] (fn u) (fn w) (upperHalfSpaceOpens d)
        volume := by
  obtain ⟨U, hU, -⟩ := regularity_upperHalfSpace hu
  exact tangentialDeriv_mem_zero_of_sobolev_two (by rw [PiLp.norm_single, norm_one])
    (upperHalfSpaceOpens_isTranslationInvariant j hj) hu.1 hU

end HalfSpaceLemmas





/-! ### Transfer back at every order: `H^k` is preserved by a `C^k` chart -/

section RetransferHigher

variable {N : ℕ}

open SobolevMultiIndex

/-- **`H^k` is preserved by the inverse chart, at every order** ([brezis2011functional] §9.6,
proof of Theorem 9.25, "by returning to `Ω ∩ Uᵢ`"): for a `C¹` diffeomorphism `H : Ω' → Ω` with
bounded Jacobians and inverse `J`, with `J` of class `C^k` on an open set `V` containing a
compact `K ⊇ Ω`, and `w ∈ H^k(Ω')`, the composite `w ∘ J ∈ H^k(Ω)`. Induction on `k`: the chain
rule `∂ᵢ(w ∘ J) = ∑_l (∂_i J)_l · (∂_l w ∘ J)` (`HasWeakFDerivOn.comp_diffeoOn`), the inductive
hypothesis for `∂_l w ∘ J`, and the multiplier `(∂_i J)_l`, `C^{k-1}` on `V` and equal on `Ω` to
a compactly supported one (`MemSobolevMultiIndex.mul_of_isContDiffConstOffCompact`). The case
`k = 2` is `Elliptic.memSobolevMultiIndex_two_comp_chart`. -/
theorem memSobolevMultiIndex_comp_chart_of_order (k : ℕ) :
    ∀ {H J : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)} {M : ℝ}
    {Ω' Ω : Opens (EuclideanSpace ℝ (Fin N))}, IsDiffeoOnWithBoundedJacobian H J Ω' Ω M →
    ∀ {V : Set (EuclideanSpace ℝ (Fin N))}, IsOpen V → ContDiffOn ℝ k J V →
    ∀ {K : Set (EuclideanSpace ℝ (Fin N))}, IsCompact K →
    (Ω : Set (EuclideanSpace ℝ (Fin N))) ⊆ K → K ⊆ V →
    ∀ {w : EuclideanSpace ℝ (Fin N) → ℝ},
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis w k 2 Ω' volume →
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (fun x ↦ w (J x)) k 2 Ω
      volume := by
  induction k with
  | zero =>
    intro H J M Ω' Ω h V hV hJ K hK hΩK hKV w hw
    rw [memSobolevMultiIndex_zero_iff] at hw ⊢
    obtain ⟨D, -, hD⟩ := h.symm.exists_abs_det_fderiv_invFun_le
    refine h.symm.memLp_comp hD Ω.isOpen subset_rfl ?_
    rw [h.symm.bijOn.image_eq]
    exact hw
  | succ k ih =>
    intro H J M Ω' Ω h V hV hJ K hK hΩK hKV w hw
    have hΩV : (Ω : Set (EuclideanSpace ℝ (Fin N))) ⊆ V := hΩK.trans hKV
    -- the cut-off equal to `1` on `K` with support in `V`
    obtain ⟨χ, hχ, hχ1, hχc, hχV⟩ :=
      exists_contDiff_eqOn_one_hasCompactSupport (Ω := ⟨V, hV⟩) hK hKV
    -- the coefficients `c i l = (∂ᵢJ)_l`, `C^k` on `V`, and their compactly supported versions
    obtain ⟨c, hc⟩ : ∃ c : Fin N → Fin N → EuclideanSpace ℝ (Fin N) → ℝ,
      c = fun i l x ↦ fderiv ℝ J x (EuclideanSpace.single i 1) l := ⟨_, rfl⟩
    have hdJ : ContDiffOn ℝ k (fderiv ℝ J) V := hJ.fderiv_of_isOpen hV (m := k) (by norm_cast)
    have hcV : ∀ i l, ContDiffOn ℝ k (c i l) V := fun i l ↦ by
      rw [hc]
      exact (EuclideanSpace.proj l).contDiff.comp_contDiffOn (hdJ.clm_apply contDiffOn_const)
    have hmult : ∀ i l, IsContDiffConstOffCompact k fun x ↦ χ x * c i l x := fun i l ↦
      IsContDiffConstOffCompact.of_hasCompactSupport
        ((hχ.of_le (by simp)).mul_contDiffOn_of_tsupport_subset hV (hcV i l) hχV) hχc.mul_right
    -- `w ∈ H^k(Ω')`, its partial derivatives `g l ∈ H^k(Ω')`, and a tensor weak derivative `Dw`
    obtain ⟨hw1, hwd⟩ := memSobolevMultiIndex_succ_iff.1 hw
    choose g hg hgp using hwd
    simp only [EuclideanSpace.basisFun_toBasis_apply] at hg
    have hw1' : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis w 1 2 Ω' volume :=
      hw.mono_order (by omega)
    obtain ⟨u, hu⟩ : ∃ u : SobolevEuclidean N 1 2 Ω',
      fn u =ᵐ[volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N)))] w :=
      hw1'.exists_sobolevMultiIndex
    obtain ⟨Dw, hDw, -, hDwi, -⟩ := exists_hasWeakFDerivOn_fn u
    have hDw' : HasWeakFDerivOn w Dw Ω' volume :=
      HasWeakIteratedFDerivOn.congr_ae hDw hu (EventuallyEq.refl _ _)
    have hDwg : ∀ l, (fun y ↦ Dw y (EuclideanSpace.single l 1))
        =ᵐ[volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N)))] g l := by
      intro l
      have h1 := (weakDeriv_hasWeakIteratedLineDerivOn_single u l).congr_ae hu
        (EventuallyEq.refl _ _)
      have h2 := (ae_restrict_iff' Ω'.isOpen.measurableSet).2 (h1.ae_eq (hg l))
      have h3 := hDwi l
      rw [EuclideanSpace.basisFun_toBasis_apply] at h3
      exact h3.trans h2
    -- the composite: `H^k` by the inductive hypothesis, and the derivatives
    have hcomp := hDw'.comp_diffeoOn h.symm
    have hJk : ContDiffOn ℝ k J V := hJ.of_le (by exact_mod_cast Nat.le_succ k)
    refine memSobolevMultiIndex_succ_iff.2 ⟨ih h hV hJk hK hΩK hKV hw1, fun i ↦ ?_⟩
    rw [EuclideanSpace.basisFun_toBasis_apply]
    refine ⟨fun x ↦ ∑ l, χ x * c i l x * g l (J x), ?_, ?_⟩
    · have h1 := (hcomp : HasWeakIteratedFDerivOn 1 _ _ Ω volume).lineDeriv
        ![EuclideanSpace.single i 1]
      refine h1.congr_ae (EventuallyEq.refl _ _) ?_
      have hae : ∀ l, ∀ᵐ x ∂volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))),
          Dw (J x) (EuclideanSpace.single l 1) = g l (J x) := fun l ↦
        h.symm.ae_comp_restrict (hDwg l)
      filter_upwards [ae_all_iff.2 hae, self_mem_ae_restrict Ω.isOpen.measurableSet] with x hx hxΩ
      simp only [continuousMultilinearCurryFin1_symm_apply, Matrix.cons_val_zero,
        ContinuousLinearMap.comp_apply]
      rw [ContinuousLinearMap.apply_eq_sum_single (Dw (J x))
        (fderiv ℝ J x (EuclideanSpace.single i 1))]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [hx l, hc, hχ1 (hΩK hxΩ), Pi.one_apply, one_mul]
    · refine MemSobolevMultiIndex.sum_mul_of_isContDiffConstOffCompact Finset.univ
        (c := fun l x ↦ χ x * c i l x) (f := fun l x ↦ g l (J x)) (fun l _ ↦ hmult i l)
        fun l _ ↦ ?_
      exact ih h hV hJk hK hΩK hKV (hgp l)

end RetransferHigher



/-! ### Differentiating the variable-coefficient equation -/

section DifferentiateGeneral

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **Differentiating the weak equation with variable coefficients** ([brezis2011functional]
§9.6, the induction "`f ∈ H^m ⇒ u ∈ H^{m+2}`" in case B and case C₂): let `w k ∈ L²(Ω)` (the
weak derivatives of a solution `u` along `e_k`), `v k` weak derivatives of `w k` along `e_j`,
`gj` a weak derivative of `g` along `e_j`, `q k l` a weak derivative of `(∂_j a_{kℓ}) w_k`
along `e_ℓ`, with `C¹` coefficients `a_{kℓ}`, and let `∑_{kℓ} ∫_Ω a_{kℓ} w_k ∂_ℓ φ = ∫_Ω g φ`
for every test function `φ`. Then `∂_j u = w_j`, whose derivatives are the `v k`, solves the
equation with the datum `∂_j g + ∑_{kℓ} ∂_ℓ((∂_j a_{kℓ}) ∂_k u)`:
`∑_{kℓ} ∫_Ω a_{kℓ} v_k ∂_ℓ φ = ∫_Ω (gj + ∑_{kℓ} q_{kℓ}) φ`. The equation is tested with `∂_j φ`
and the derivative moved onto `a_{kℓ} w_k` by the product rule. -/
theorem forall_testFunction_deriv_general {g gj : EuclideanSpace ℝ (Fin N) → ℝ}
    {w v : Fin N → EuclideanSpace ℝ (Fin N) → ℝ}
    {a q : Fin N → Fin N → EuclideanSpace ℝ (Fin N) → ℝ} (j : Fin N)
    (ha : ∀ k l, ContDiffOn ℝ 1 (a k l) Ω)
    (hwp : ∀ k, MemLp (w k) 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (hv : ∀ k, HasWeakIteratedLineDerivOn ![EuclideanSpace.single j 1] (w k) (v k) Ω volume)
    (hvp : ∀ k, MemLp (v k) 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (hg : HasWeakIteratedLineDerivOn ![EuclideanSpace.single j 1] g gj Ω volume)
    (hq : ∀ k l, HasWeakIteratedLineDerivOn ![EuclideanSpace.single l 1]
      (fun x ↦ fderiv ℝ (a k l) x (EuclideanSpace.single j 1) * w k x) (q k l) Ω volume)
    (heq : ∀ φ : 𝓓(Ω, ℝ), ∑ k, ∑ l, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      a k l x * w k x * fderiv ℝ φ x (EuclideanSpace.single l 1)
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), g x * φ x)
    (φ : 𝓓(Ω, ℝ)) :
    ∑ k, ∑ l, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      a k l x * v k x * fderiv ℝ φ x (EuclideanSpace.single l 1)
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), (gj x + ∑ k, ∑ l, q k l x) * φ x := by
  have h2 : (2 : ℝ≥0∞) ≠ ⊤ := ENNReal.ofNat_ne_top
  have hΩm : MeasurableSet (Ω : Set (EuclideanSpace ℝ (Fin N))) := Ω.isOpen.measurableSet
  -- the product rule: `∂_j (a_{kℓ} w_k) = (∂_j a_{kℓ}) w_k + a_{kℓ} v_k`
  have hprod : ∀ k l, HasWeakIteratedLineDerivOn ![EuclideanSpace.single j 1]
      (fun x ↦ a k l x * w k x)
      (fun x ↦ fderiv ℝ (a k l) x (EuclideanSpace.single j 1) * w k x + a k l x * v k x)
      Ω volume := fun k l ↦
    ((ha k l).hasWeakIteratedLineDerivOn_single Ω j).mul rfl (hv k) one_le_two h2 h2
      ((ha k l).continuousOn.locallyMemLpOn 2)
      ((((ha k l).fderiv_of_isOpen Ω.isOpen (m := 0) le_rfl).continuousOn.clm_apply
        continuousOn_const).locallyMemLpOn 2)
      (hwp k).locallyMemLpOn (hvp k).locallyMemLpOn
  -- each term of the equation tested with `∂_j φ`
  have hterm : ∀ k l, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      a k l x * w k x * fderiv ℝ (φ.fderivApply (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single l 1)
      = (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), q k l x * φ x)
        - ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          a k l x * v k x * fderiv ℝ φ x (EuclideanSpace.single l 1) := by
    intro k l
    have key1 := (hprod k l).integral_fderiv_mul_eq_of_eqOn
      (φ.fderivApply (EuclideanSpace.single l 1)) (fun _ _ ↦ rfl)
    have key2 := (hq k l).integral_fderiv_mul_eq_of_eqOn φ (fun _ _ ↦ rfl)
    have hsym : ∀ x, fderiv ℝ (fun z ↦ fderiv ℝ φ z (EuclideanSpace.single l 1)) x
        (EuclideanSpace.single j 1)
        = fderiv ℝ (fun z ↦ fderiv ℝ φ z (EuclideanSpace.single j 1)) x
          (EuclideanSpace.single l 1) := fun x ↦
      congrFun (φ.contDiff.fderiv_fderiv_comm (EuclideanSpace.single l 1)
        (EuclideanSpace.single j 1)) x
    simp only [TestFunction.fderivApply_coe] at key1 key2 ⊢
    -- integrability of the two pieces of the right side of `key1`
    have I1 : Integrable (fun x ↦ fderiv ℝ φ x (EuclideanSpace.single l 1)
        * (fderiv ℝ (a k l) x (EuclideanSpace.single j 1) * w k x))
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
      have := ((hq k l).integrable_smul (φ.fderivApply (EuclideanSpace.single l 1))).integrableOn
        (s := (Ω : Set (EuclideanSpace ℝ (Fin N))))
      simp only [TestFunction.fderivApply_coe, smul_eq_mul] at this
      exact this
    have I12 : Integrable (fun x ↦ fderiv ℝ φ x (EuclideanSpace.single l 1)
        * (fderiv ℝ (a k l) x (EuclideanSpace.single j 1) * w k x + a k l x * v k x))
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
      have := ((hprod k l).integrable_smul_weakDeriv
        (φ.fderivApply (EuclideanSpace.single l 1))).integrableOn
        (s := (Ω : Set (EuclideanSpace ℝ (Fin N))))
      simp only [TestFunction.fderivApply_coe, smul_eq_mul] at this
      exact this
    have I2 : Integrable (fun x ↦ fderiv ℝ φ x (EuclideanSpace.single l 1) * (a k l x * v k x))
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
      (I12.sub I1).congr (Eventually.of_forall fun x ↦ by simp only [Pi.sub_apply]; ring)
    have e1 : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        fderiv ℝ φ x (EuclideanSpace.single l 1)
          * (fderiv ℝ (a k l) x (EuclideanSpace.single j 1) * w k x + a k l x * v k x)
        = (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), fderiv ℝ φ x (EuclideanSpace.single l 1)
            * (fderiv ℝ (a k l) x (EuclideanSpace.single j 1) * w k x))
          + ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
            fderiv ℝ φ x (EuclideanSpace.single l 1) * (a k l x * v k x) := by
      rw [← integral_add I1 I2]
      exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
    have e2 : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        a k l x * w k x * fderiv ℝ (fun z ↦ fderiv ℝ φ z (EuclideanSpace.single j 1)) x
          (EuclideanSpace.single l 1)
        = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          fderiv ℝ (fun z ↦ fderiv ℝ φ z (EuclideanSpace.single l 1)) x
            (EuclideanSpace.single j 1) * (a k l x * w k x) :=
      integral_congr_ae (Eventually.of_forall fun x ↦ by dsimp only; rw [← hsym x, mul_comm])
    have e3 : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        fderiv ℝ φ x (EuclideanSpace.single l 1)
          * (fderiv ℝ (a k l) x (EuclideanSpace.single j 1) * w k x)
        = -∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), q k l x * φ x := by
      rw [key2]
      congr 1
      exact integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
    have e4 : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        fderiv ℝ φ x (EuclideanSpace.single l 1) * (a k l x * v k x)
        = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          a k l x * v k x * fderiv ℝ φ x (EuclideanSpace.single l 1) :=
      integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
    rw [e2, key1, e1, e3, e4]
    ring
  -- the right side tested with `∂_j φ`
  have key3 := hg.integral_fderiv_mul_eq_of_eqOn φ (fun _ _ ↦ rfl)
  have e5 : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      g x * (φ.fderivApply (EuclideanSpace.single j 1)) x
      = -∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), gj x * φ x := by
    simp only [TestFunction.fderivApply_coe]
    calc ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          g x * fderiv ℝ φ x (EuclideanSpace.single j 1)
        = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          fderiv ℝ φ x (EuclideanSpace.single j 1) * g x :=
          integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
      _ = -∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), φ x * gj x := key3
      _ = -∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), gj x * φ x := by
          congr 1
          exact integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
  have hsum := heq (φ.fderivApply (EuclideanSpace.single j 1))
  simp only [hterm] at hsum
  rw [e5] at hsum
  simp only [Finset.sum_sub_distrib] at hsum
  -- integrability for the final rearrangement
  have Iq : ∀ k l, Integrable (fun x ↦ q k l x * φ x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := fun k l ↦ by
    have := ((hq k l).integrable_smul_weakDeriv φ).integrableOn
      (s := (Ω : Set (EuclideanSpace ℝ (Fin N))))
    exact this.congr (Eventually.of_forall fun x ↦ by simp only [smul_eq_mul]; ring)
  have Ig : Integrable (fun x ↦ gj x * φ x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
    have := (hg.integrable_smul_weakDeriv φ).integrableOn
      (s := (Ω : Set (EuclideanSpace ℝ (Fin N))))
    exact this.congr (Eventually.of_forall fun x ↦ by simp only [smul_eq_mul]; ring)
  have e7 : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), (∑ k, ∑ l, q k l x) * φ x
      = ∑ k, ∑ l, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), q k l x * φ x := by
    have : (fun x ↦ (∑ k, ∑ l, q k l x) * φ x) = fun x ↦ ∑ k, ∑ l, q k l x * φ x := by
      funext x
      simp only [Finset.sum_mul]
    rw [this, integral_finsetSum _ fun k _ ↦ integrable_finsetSum _ fun l _ ↦ Iq k l]
    exact Finset.sum_congr rfl fun k _ ↦ integral_finsetSum _ fun l _ ↦ Iq k l
  have IS : Integrable (fun x ↦ (∑ k, ∑ l, q k l x) * φ x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
    have : (fun x ↦ (∑ k, ∑ l, q k l x) * φ x) = fun x ↦ ∑ k, ∑ l, q k l x * φ x := by
      funext x
      simp only [Finset.sum_mul]
    rw [this]
    exact integrable_finsetSum _ fun k _ ↦ integrable_finsetSum _ fun l _ ↦ Iq k l
  have e6 : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), (gj x + ∑ k, ∑ l, q k l x) * φ x
      = (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), gj x * φ x)
        + ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), (∑ k, ∑ l, q k l x) * φ x := by
    rw [← integral_add Ig IS]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
  rw [e6, e7]
  linarith

end DifferentiateGeneral



section ConstOffCompactBounds

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite family of multipliers has a common bound. -/
theorem exists_forall_abs_le_of_isContDiffConstOffCompact {n : ℕ} {N : ℕ}
    {a : Fin N → Fin N → E → ℝ} (ha : ∀ k l, IsContDiffConstOffCompact n (a k l)) :
    ∃ M₀, 0 ≤ M₀ ∧ ∀ k l x, |a k l x| ≤ M₀ := by
  choose C hC using fun k l ↦ (ha k l).exists_bound
  obtain ⟨M₀, hM₀0, hM₀⟩ := exists_forall_le_of_fin C
  exact ⟨M₀, hM₀0, fun k l x ↦ (hC k l x).trans (hM₀ k l)⟩

/-- A finite family of multipliers of class `C^{n+1}` has a common bound on the derivatives. -/
theorem exists_forall_norm_fderiv_le_of_isContDiffConstOffCompact {n : ℕ} {N : ℕ}
    {a : Fin N → Fin N → E → ℝ} (ha : ∀ k l, IsContDiffConstOffCompact (n + 1) (a k l)) :
    ∃ M, 0 ≤ M ∧ ∀ k l x, ‖fderiv ℝ (a k l) x‖ ≤ M := by
  choose C hC using fun k l ↦ (ha k l).exists_bound_fderiv
  obtain ⟨M, hM0, hM⟩ := exists_forall_le_of_fin C
  exact ⟨M, hM0, fun k l x ↦ (hC k l x).trans (hM k l)⟩

end ConstOffCompactBounds


/-! ### Case B, higher order: `H^{m+2}` regularity on a tangentially invariant open set -/

section TangentialHigher

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

open SobolevMultiIndex

/-- **Higher-order regularity on an open set invariant under the tangential translations, for a
variable-coefficient elliptic form** — [brezis2011functional] Theorem 9.25, case B, the
induction "`f ∈ H^m ⇒ u ∈ H^{m+2}`", in the generality of case C₂. Let `Ω ⊆ ℝ^N` be open and
invariant under the translations `t e_j`, `j ≠ N`, let the coefficients `A_{kℓ} ∈ L^∞(Ω)` have
representatives `a_{kℓ}` of class `C^{m+1}` on `ℝ^N` and constant off a compact set
(`IsContDiffConstOffCompact`), elliptic with constant `α > 0` at every point, and let
`u ∈ H^1_0(Ω)` satisfy `∑_{kℓ} ∫_Ω a_{kℓ} ∂_k u ∂_ℓ ψ = ∫_Ω g ψ` for all `ψ ∈ H^1_0(Ω)` with
`g ∈ H^m(Ω)`. Then `u ∈ H^{m+2}(Ω)`.

Induction on `m`, the case `m = 0` being `Elliptic.exists_sobolevEuclidean_two_of_tangential`.
For `m + 1`: `u ∈ H^{m+2}(Ω)` by the inductive hypothesis; for a tangential direction `e_j` the
derivative `∂_j u` lies in `H^1_0(Ω)` (Lemma 9.7,
`Elliptic.tangentialDeriv_mem_zero_of_sobolev_two`) and solves the equation with the datum
`∂_j g + ∑_{kℓ} ∂_ℓ((∂_j a_{kℓ}) ∂_k u) ∈ H^m(Ω)` (`Elliptic.forall_testFunction_deriv_general`),
so `∂_j u ∈ H^{m+2}(Ω)` by the inductive hypothesis; the normal derivative `∂_N ∂_N u` is read
off the equation (`Elliptic.hasWeakIteratedLineDerivOn_last_mul_of_forall`) as `a_{NN}⁻¹` times
a function of `H^{m+1}(Ω)`, and `memSobolevMultiIndex_succ_iff` assembles `u ∈ H^{m+3}(Ω)`. -/
theorem memSobolevMultiIndex_of_tangential_of_order (m : ℕ)
    (hΩ : ∀ j : Fin (d + 1), j ≠ Fin.last d → ∀ t : ℝ,
      IsTranslationInvariant (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))
        (t • EuclideanSpace.single j 1))
    {A : Fin (d + 1) → Fin (d + 1) →
      Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    {a : Fin (d + 1) → Fin (d + 1) → EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hAa : ∀ k l, ⇑(A k l) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] a k l)
    {α : ℝ} (hα0 : 0 < α)
    (hell : ∀ (x ξ : EuclideanSpace ℝ (Fin (d + 1))),
      α * ‖ξ‖ ^ 2 ≤ ∑ k, ∑ l, a k l x * ξ k * ξ l) :
    (∀ k l, IsContDiffConstOffCompact (m + 1) (a k l)) →
    ∀ {u : SobolevEuclidean (d + 1) 1 2 Ω}, u ∈ SobolevEuclideanZero (d + 1) 1 2 Ω →
    ∀ {g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))},
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (⇑g) m 2 Ω volume →
    (∀ ψ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω, generalForm Ω A 0 0 u ψ = load Ω g ψ) →
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (fn u) (m + 2) 2 Ω
      volume := by
  have hΩm : MeasurableSet (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) := Ω.isOpen.measurableSet
  have hell' : ∀ x ∈ ((⊤ : Opens (EuclideanSpace ℝ (Fin (d + 1)))) :
      Set (EuclideanSpace ℝ (Fin (d + 1)))), ∀ ξ : EuclideanSpace ℝ (Fin (d + 1)),
      α * ‖ξ‖ ^ 2 ≤ ∑ k, ∑ l, a k l x * ξ k * ξ l := fun x _ ξ ↦ hell x ξ
  have hdiag : ∀ x, α ≤ a (Fin.last d) (Fin.last d) x := fun x ↦
    le_diag_of_forall_elliptic (Ω := ⊤) hell' (Set.mem_univ x) (Fin.last d)
  induction m with
  | zero =>
    intro ha u hu g hg heq
    obtain ⟨M₀, hM₀0, hM₀⟩ := exists_forall_abs_le_of_isContDiffConstOffCompact ha
    obtain ⟨M, hM0, hM⟩ := exists_forall_norm_fderiv_le_of_isContDiffConstOffCompact ha
    obtain ⟨U, hU, -⟩ := exists_sobolevEuclidean_two_of_tangential hΩ hAa
      (fun k l ↦ ((ha k l).contDiff.of_le (by simp)).contDiffOn) hM₀0 hM0
      (fun k l x _ ↦ hM₀ k l x) (fun k l x _ ↦ hM k l x) hα0 (fun x _ ξ ↦ hell x ξ) hu heq
    exact (memSobolevMultiIndex U).congr_ae hU
  | succ m ih =>
    intro ha u hu g hg heq
    have ha' : ∀ k l, IsContDiffConstOffCompact (m + 1) (a k l) := fun k l ↦
      (ha k l).of_le (Nat.le_succ _)
    have ha1 : ∀ k l, ContDiffOn ℝ 1 (a k l) Ω := fun k l ↦
      ((ha k l).contDiff.of_le (by exact_mod_cast Nat.le_add_left 1 (m + 1))).contDiffOn
    obtain ⟨M₀, hM₀0, hM₀⟩ := exists_forall_abs_le_of_isContDiffConstOffCompact ha
    obtain ⟨M, hM0, hM⟩ := exists_forall_norm_fderiv_le_of_isContDiffConstOffCompact ha
    -- (1) `u ∈ H^{m+2}(Ω)` by the inductive hypothesis, and a typed `H²` element
    have hu2 := ih ha' hu (hg.mono_order (Nat.le_succ m)) heq
    obtain ⟨U, hU⟩ : ∃ U : SobolevEuclidean (d + 1) 2 2 Ω,
        fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] fn u :=
      (hu2.mono_order (by omega)).exists_sobolevMultiIndex
    -- (2) the first derivatives of `u` lie in `H^{m+1}(Ω)`
    have hw : ∀ k, MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
        (weakDeriv u (MultiIndexLE.single k)) (m + 1) 2 Ω volume := by
      intro k
      obtain ⟨-, hd⟩ := memSobolevMultiIndex_succ_iff.1 hu2
      obtain ⟨w, hw, hwm⟩ := hd k
      rw [EuclideanSpace.basisFun_toBasis_apply] at hw
      refine hwm.congr_ae ?_
      exact (ae_restrict_iff' hΩm).2 (hw.ae_eq (weakDeriv_hasWeakIteratedLineDerivOn_single u k))
    -- (3) the derivatives of `g`
    obtain ⟨-, hgd⟩ := memSobolevMultiIndex_succ_iff.1 hg
    choose gj hgj hgjm using hgd
    simp only [EuclideanSpace.basisFun_toBasis_apply] at hgj
    -- (4) the products `(∂_j a_{kℓ}) ∂_k u ∈ H^{m+1}(Ω)` and their derivatives along `e_ℓ`
    have hp : ∀ j k l, MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
        (fun x ↦ fderiv ℝ (a k l) x (EuclideanSpace.single j 1)
          * weakDeriv u (MultiIndexLE.single k) x) (m + 1) 2 Ω volume := fun j k l ↦
      MemSobolevMultiIndex.mul_of_isContDiffConstOffCompact (m + 1) ((ha k l).fderiv_apply _)
        (hw k)
    have hq : ∀ j k l, ∃ q : EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
        HasWeakIteratedLineDerivOn ![EuclideanSpace.single l 1]
          (fun x ↦ fderiv ℝ (a k l) x (EuclideanSpace.single j 1)
            * weakDeriv u (MultiIndexLE.single k) x) q Ω volume ∧
        MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis q m 2 Ω volume := by
      intro j k l
      obtain ⟨-, hd⟩ := memSobolevMultiIndex_succ_iff.1 (hp j k l)
      obtain ⟨q, hq, hqm⟩ := hd l
      rw [EuclideanSpace.basisFun_toBasis_apply] at hq
      exact ⟨q, hq, hqm⟩
    choose q hq hqm using hq
    -- (5) the second derivatives `v k l = ∂_ℓ ∂_k u`, in `H^m(Ω)`
    have hv : ∀ k l, ∃ v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
        HasWeakIteratedLineDerivOn ![EuclideanSpace.single l 1]
          (weakDeriv u (MultiIndexLE.single k)) v Ω volume ∧
        MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis v m 2 Ω volume := by
      intro k l
      obtain ⟨-, hd⟩ := memSobolevMultiIndex_succ_iff.1 (hw k)
      obtain ⟨v, hv, hvm⟩ := hd l
      rw [EuclideanSpace.basisFun_toBasis_apply] at hv
      exact ⟨v, hv, hvm⟩
    choose v hv hvm using hv
    -- the predicate form of the equation
    have hpred := forall_testFunction_of_forall_mem_general hAa
      SobolevMultiIndexZero.testFunctions_le heq
    -- (6) for a tangential `j`, `∂_j u ∈ H^{m+2}(Ω)`
    have htan : ∀ j, j ≠ Fin.last d →
        MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
          (weakDeriv u (MultiIndexLE.single j)) (m + 2) 2 Ω volume := by
      intro j hj
      obtain ⟨W, hW, hWd⟩ := tangentialDeriv_mem_zero_of_sobolev_two
        (y := EuclideanSpace.single j 1) (by rw [PiLp.norm_single, norm_one]) (hΩ j hj) hu hU
      have hWfn : fn W =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
          weakDeriv u (MultiIndexLE.single j) :=
        (ae_restrict_iff' hΩm).2 (hWd.ae_eq (weakDeriv_hasWeakIteratedLineDerivOn_single u j))
      -- the datum `∂_j g + ∑ q`, in `H^m(Ω)`
      have hG'm : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
          (fun x ↦ gj j x + ∑ k, ∑ l, q j k l x) m 2 Ω volume := by
        have hS := MemSobolevMultiIndex.finset_sum Finset.univ
          (f := fun k ↦ ∑ l, fun x ↦ q j k l x) fun k _ ↦
            MemSobolevMultiIndex.finset_sum Finset.univ (f := fun l x ↦ q j k l x)
              fun l _ ↦ hqm j k l
        have := (hgjm j).add hS
        refine this.congr_ae (Eventually.of_forall fun x ↦ ?_)
        simp only [Pi.add_apply, Finset.sum_apply]
      have hG'p : MemLp (fun x ↦ gj j x + ∑ k, ∑ l, q j k l x) 2
          (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) := hG'm.memLp
      -- the differentiated equation
      have hderiv := forall_testFunction_deriv_general j ha1 (fun k ↦ Lp.memLp _)
        (fun k ↦ hv k j) (fun k ↦ (hvm k j).memLp) (hgj j) (hq j) hpred
      -- `v k j = ∂_k (fn W)` almost everywhere
      have hvW : ∀ k, v k j =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
          weakDeriv W (MultiIndexLE.single k) := by
        intro k
        have h1 := (weakDeriv_hasWeakIteratedLineDerivOn_single u k).cons (hv k j)
        have h2 := hWd.cons (weakDeriv_hasWeakIteratedLineDerivOn_single W k)
        have h3 : HasWeakIteratedLineDerivOn
            (Fin.cons (EuclideanSpace.single j 1) ![EuclideanSpace.single k 1]) (fn u)
            (weakDeriv W (MultiIndexLE.single k)) Ω volume := by
          refine h2.of_perm ?_
          simp only [List.ofFn_cons]
          exact List.Perm.swap _ _ _
        exact (ae_restrict_iff' hΩm).2 (h1.ae_eq h3)
      -- the typed equation for `W`
      have heqW : ∀ ψ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω,
          generalForm Ω A 0 0 W ψ = load Ω (hG'p.toLp _) ψ := by
        intro ψ hψ
        refine generalForm_eq_load_of_forall_testFunctions (fun Φ hΦ ↦ ?_) hψ
        obtain ⟨φ, hφ⟩ := hΦ
        rw [generalForm_zero_zero_apply_eq_of_ae_eq hAa W hφ,
          load_apply_eq_of_ae_eq hG'p.coeFn_toLp hφ, ← hderiv φ]
        refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ integral_congr_ae ?_
        filter_upwards [hvW k] with x hx
        rw [hx]
      exact (ih ha' hW (hG'm.congr_ae hG'p.coeFn_toLp.symm) heqW).congr_ae hWfn
    -- (7) the second derivatives other than `∂_N ∂_N u` lie in `H^{m+1}(Ω)`
    have hv1 : ∀ k l, (k ≠ Fin.last d ∨ l ≠ Fin.last d) →
        MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (v k l) (m + 1) 2
          Ω volume := by
      intro k l hkl
      rcases eq_or_ne l (Fin.last d) with rfl | hl
      · -- `ℓ = N`, `k ≠ N`: `v k N = ∂_N (∂_k u)` with `∂_k u ∈ H^{m+2}`
        have hk : k ≠ Fin.last d := hkl.resolve_right (fun h ↦ h rfl)
        obtain ⟨-, hd⟩ := memSobolevMultiIndex_succ_iff.1 (htan k hk)
        obtain ⟨r, hr, hrm⟩ := hd (Fin.last d)
        rw [EuclideanSpace.basisFun_toBasis_apply] at hr
        exact hrm.congr_ae ((ae_restrict_iff' hΩm).2 (hr.ae_eq (hv k (Fin.last d))))
      · -- `ℓ ≠ N`: `v k ℓ = ∂_ℓ ∂_k u = ∂_k ∂_ℓ u` with `∂_ℓ u ∈ H^{m+2}`
        obtain ⟨-, hd⟩ := memSobolevMultiIndex_succ_iff.1 (htan l hl)
        obtain ⟨r, hr, hrm⟩ := hd k
        rw [EuclideanSpace.basisFun_toBasis_apply] at hr
        have h1 := (weakDeriv_hasWeakIteratedLineDerivOn_single u k).cons (hv k l)
        have h2 := (weakDeriv_hasWeakIteratedLineDerivOn_single u l).cons hr
        have h3 : HasWeakIteratedLineDerivOn
            (Fin.cons (EuclideanSpace.single l 1) ![EuclideanSpace.single k 1]) (fn u) r Ω
            volume := by
          refine h2.of_perm ?_
          simp only [List.ofFn_cons]
          exact List.Perm.swap _ _ _
        exact hrm.congr_ae ((ae_restrict_iff' hΩm).2 (h3.ae_eq h1))
    -- (8) the normal-normal derivative from the equation
    have hNN : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
        (v (Fin.last d) (Fin.last d)) (m + 1) 2 Ω volume := by
      obtain ⟨hGd, -⟩ := hasWeakIteratedLineDerivOn_last_mul_of_forall ha1
        (fun k l x _ ↦ hM₀ k l x) (fun k l x _ ↦ hM k l x)
        (w := fun k ↦ ⇑(weakDeriv u (MultiIndexLE.single k))) (fun k ↦ Lp.memLp _) (Lp.memLp g)
        (v := v) (fun k l _ ↦ hv k l) (fun k l ↦ (hvm k l).memLp) hpred
      -- the product rule for `a_{NN} w_N`
      have haN := ha1 (Fin.last d) (Fin.last d)
      have hprod := (haN.hasWeakIteratedLineDerivOn_single Ω (Fin.last d)).mul rfl
        (hv (Fin.last d) (Fin.last d)) one_le_two ENNReal.ofNat_ne_top ENNReal.ofNat_ne_top
        (haN.continuousOn.locallyMemLpOn 2)
        (((haN.fderiv_of_isOpen Ω.isOpen (m := 0) le_rfl).continuousOn.clm_apply
          continuousOn_const).locallyMemLpOn 2) (Lp.memLp _).locallyMemLpOn
        (hvm (Fin.last d) (Fin.last d)).memLp.locallyMemLpOn
      have hae := (ae_restrict_iff' hΩm).2 (hprod.ae_eq hGd)
      -- the right side lies in `H^{m+1}(Ω)`
      obtain ⟨R, hR⟩ : ∃ R : EuclideanSpace ℝ (Fin (d + 1)) → ℝ, R = fun x ↦
        -(g x + ∑ k, ∑ l, if k = Fin.last d ∧ l = Fin.last d then 0 else
          fderiv ℝ (a k l) x (EuclideanSpace.single l 1) * weakDeriv u (MultiIndexLE.single k) x
            + a k l x * v k l x) := ⟨_, rfl⟩
      have hRm : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis R (m + 1)
          2 Ω volume := by
        have hterm : ∀ k l, MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
            (fun x ↦ if k = Fin.last d ∧ l = Fin.last d then 0 else
              fderiv ℝ (a k l) x (EuclideanSpace.single l 1)
                * weakDeriv u (MultiIndexLE.single k) x + a k l x * v k l x) (m + 1) 2 Ω
              volume := by
          intro k l
          by_cases hkl : k = Fin.last d ∧ l = Fin.last d
          · simp only [hkl, and_self, ite_true]
            exact MemSobolevMultiIndex.zero
          · simp only [hkl, ite_false]
            have hkl' : k ≠ Fin.last d ∨ l ≠ Fin.last d := by
              rw [← not_and_or]
              exact hkl
            exact (MemSobolevMultiIndex.mul_of_isContDiffConstOffCompact (m + 1)
              ((ha k l).fderiv_apply _) (hw k)).add
              (MemSobolevMultiIndex.mul_of_isContDiffConstOffCompact (m + 1) (ha' k l)
                (hv1 k l hkl'))
        have hsum := MemSobolevMultiIndex.finset_sum Finset.univ
          (f := fun k ↦ ∑ l, fun x ↦ if k = Fin.last d ∧ l = Fin.last d then (0 : ℝ) else
            fderiv ℝ (a k l) x (EuclideanSpace.single l 1)
              * weakDeriv u (MultiIndexLE.single k) x + a k l x * v k l x) fun k _ ↦
          MemSobolevMultiIndex.finset_sum Finset.univ fun l _ ↦ hterm k l
        have := (hg.add hsum).neg
        refine this.congr_ae (Eventually.of_forall fun x ↦ ?_)
        rw [hR]
        simp only [Pi.neg_apply, Pi.add_apply, Finset.sum_apply]
      -- divide by `a_{NN}`
      have hinv : IsContDiffConstOffCompact (m + 1) fun x ↦ (a (Fin.last d) (Fin.last d) x)⁻¹ :=
        (ha' _ _).inv hα0 hdiag
      have hRm' : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
          (fun x ↦ (a (Fin.last d) (Fin.last d) x)⁻¹ * (R x
            - fderiv ℝ (a (Fin.last d) (Fin.last d)) x (EuclideanSpace.single (Fin.last d) 1)
              * weakDeriv u (MultiIndexLE.single (Fin.last d)) x)) (m + 1) 2 Ω volume :=
        MemSobolevMultiIndex.mul_of_isContDiffConstOffCompact (m + 1) hinv
          (hRm.sub (MemSobolevMultiIndex.mul_of_isContDiffConstOffCompact (m + 1)
            ((ha (Fin.last d) (Fin.last d)).fderiv_apply (EuclideanSpace.single (Fin.last d) 1))
            (hw (Fin.last d))))
      refine hRm'.congr_ae ?_
      filter_upwards [hae] with x hx
      have hRx := congrFun hR x
      rw [hRx, ← hx]
      have hne : a (Fin.last d) (Fin.last d) x ≠ 0 := (hα0.trans_le (hdiag x)).ne'
      field_simp
      ring
    -- (9) `∂_N u ∈ H^{m+2}(Ω)`
    have hlast : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
        (weakDeriv u (MultiIndexLE.single (Fin.last d))) (m + 2) 2 Ω volume := by
      refine memSobolevMultiIndex_succ_iff.2 ⟨hw _, fun i ↦ ?_⟩
      rw [EuclideanSpace.basisFun_toBasis_apply]
      rcases eq_or_ne i (Fin.last d) with rfl | hi
      · exact ⟨v _ _, hv _ _, hNN⟩
      · -- `∂_i ∂_N u = ∂_N ∂_i u` with `∂_i u ∈ H^{m+2}`
        obtain ⟨-, hd⟩ := memSobolevMultiIndex_succ_iff.1 (htan i hi)
        obtain ⟨r, hr, hrm⟩ := hd (Fin.last d)
        rw [EuclideanSpace.basisFun_toBasis_apply] at hr
        refine ⟨r, ?_, hrm⟩
        have h2 := (weakDeriv_hasWeakIteratedLineDerivOn_single u i).cons hr
        have h3 : HasWeakIteratedLineDerivOn
            (Fin.cons (EuclideanSpace.single i 1) ![EuclideanSpace.single (Fin.last d) 1]) (fn u)
            r Ω volume := by
          refine h2.of_perm ?_
          simp only [List.ofFn_cons]
          exact List.Perm.swap _ _ _
        exact (weakDeriv_hasWeakIteratedLineDerivOn_single u (Fin.last d)).of_cons h3
    -- (10) assembly
    refine memSobolevMultiIndex_succ_iff.2 ⟨hu2, fun i ↦ ?_⟩
    rw [EuclideanSpace.basisFun_toBasis_apply]
    refine ⟨weakDeriv u (MultiIndexLE.single i), weakDeriv_hasWeakIteratedLineDerivOn_single u i,
      ?_⟩
    rcases eq_or_ne i (Fin.last d) with rfl | hi
    · exact hlast
    · exact htan i hi

end TangentialHigher



/-! ### Case B, higher order: the half space -/

section UpperHalfSpaceHigher

variable {d : ℕ}

open SobolevMultiIndex EuclideanSpace

/-- **Theorem 9.25, case B (`Ω = ℝ^N_+`), higher order** ([brezis2011functional] §9.6, case B:
"`f ∈ H^m ⇒ u ∈ H^{m+2}`, by induction on `m`"): let `u ∈ H^1_0(ℝ^N_+)` and `g ∈ L²(ℝ^N_+)` with
`∫ ∇u · ∇ψ = ∫ g ψ` for every `ψ ∈ H^1_0(ℝ^N_+)`. If `g ∈ H^m(ℝ^N_+)` then
`u ∈ H^{m+2}(ℝ^N_+)`. The book's equation `−Δu + u = f` is the case `g = f − u`. This is
`Elliptic.memSobolevMultiIndex_of_tangential_of_order` for the identity coefficients
(`Elliptic.generalForm_kroneckerCoeff`): the tangential derivatives `∂_j u ∈ H^1_0` (Lemma 9.7)
solve the equation with datum `∂_j g` and the normal one is read off the equation. -/
theorem regularity_upperHalfSpace_higher (m : ℕ)
    {u : SobolevEuclidean (d + 1) 1 2 (upperHalfSpaceOpens d)}
    {g : Lp ℝ 2 (volume.restrict
      ((upperHalfSpaceOpens d : Opens (EuclideanSpace ℝ (Fin (d + 1)))) :
        Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    (hu : IsGalerkinSolution (dirichletForm (upperHalfSpaceOpens d))
      (load (upperHalfSpaceOpens d) g)
      (SobolevEuclideanZero (d + 1) 1 2 (upperHalfSpaceOpens d)) u)
    (hg : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (⇑g) m 2
      (upperHalfSpaceOpens d) volume) :
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (fn u) (m + 2) 2
      (upperHalfSpaceOpens d) volume := by
  refine memSobolevMultiIndex_of_tangential_of_order m upperHalfSpaceOpens_isTranslationInvariant
    (A := kroneckerCoeff (upperHalfSpaceOpens d))
    (a := fun k l _ ↦ if k = l then (1 : ℝ) else 0) (coeFn_kroneckerCoeff _) one_pos
    (fun x ξ ↦ one_mul_norm_sq_le_sum_kroneckerRep x ξ)
    (fun k l ↦ IsContDiffConstOffCompact.const _) hu.1 hg fun ψ hψ ↦ ?_
  rw [generalForm_kroneckerCoeff]
  exact hu.2 ψ hψ

end UpperHalfSpaceHigher

/-! ### Case C₂ on the model cylinder, higher order -/

section CylinderRegularityHigher

variable {d : ℕ} {Ω' Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

open SobolevMultiIndex

/-- The extended coefficients `χ a + (1 − χ) δ` are of class `C^n` when `χ` and `a` are. -/
theorem contDiff_extendCoeff_of_order {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} {n : WithTop ℕ∞} {χ : E → ℝ} (hχ : ContDiff ℝ n χ) {Q : Set E} (hQ : IsOpen Q)
    {a : Fin N → Fin N → E → ℝ} (ha : ∀ k l, ContDiffOn ℝ n (a k l) Q) (hχQ : tsupport χ ⊆ Q)
    (k l : Fin N) : ContDiff ℝ n (extendCoeff χ a k l) :=
  (hχ.mul_contDiffOn_of_tsupport_subset hQ (ha k l) hχQ).add
    ((contDiff_const.sub hχ).mul contDiff_const)

/-- **The extended coefficients are multipliers**: for a smooth compactly supported `χ` with
support in `Q` and coefficients `a` of class `C^n` on `Q`, `χ a + (1 − χ) δ` is `C^n` on the
whole space and equal to `δ` off the support of `χ`. -/
theorem isContDiffConstOffCompact_extendCoeff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {N : ℕ} {n : ℕ} {χ : E → ℝ} (hχ : ContDiff ℝ n χ)
    (hχc : HasCompactSupport χ) {Q : Set E} (hQ : IsOpen Q) {a : Fin N → Fin N → E → ℝ}
    (ha : ∀ k l, ContDiffOn ℝ n (a k l) Q) (hχQ : tsupport χ ⊆ Q) (k l : Fin N) :
    IsContDiffConstOffCompact n (extendCoeff χ a k l) := by
  refine ⟨contDiff_extendCoeff_of_order hχ hQ ha hχQ k l, if k = l then 1 else 0, ?_⟩
  have e : (fun y ↦ extendCoeff χ a k l y - if k = l then 1 else 0)
      = fun y ↦ χ y * (a k l y - if k = l then 1 else 0) := by
    funext y
    simp only [extendCoeff]
    ring
  rw [e]
  exact hχc.mul_right

/-- **Higher-order regularity of a compactly supported solution on a subset of a tangentially
invariant open set** — [brezis2011functional] Theorem 9.25, case C₂ on the model cylinder, the
induction "`f ∈ H^m ⇒ u ∈ H^{m+2}`": under the hypotheses of
`Elliptic.memSobolevMultiIndex_two_of_tangential_of_compact`, with the coefficients of class
`C^{m+1}` and elliptic on `Q` and the datum `g ∈ H^m(Ω')`, the solution `w` lies in
`H^{m+2}(Ω')`. The zero extension `W ∈ H^1_0(Ω)` solves the equation with the coefficients
`Elliptic.extendCoeff χ a`, which are multipliers of class `C^{m+1}` elliptic everywhere, and the
datum `1_{Ω'} χ g ∈ H^m(Ω)`, so `Elliptic.memSobolevMultiIndex_of_tangential_of_order` applies. -/
theorem memSobolevMultiIndex_of_tangential_of_compact_of_order (m : ℕ)
    (hΩ : ∀ j : Fin (d + 1), j ≠ Fin.last d → ∀ t : ℝ,
      IsTranslationInvariant (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))
        (t • EuclideanSpace.single j 1))
    (hΩ' : Ω' ≤ Ω) {Q : Set (EuclideanSpace ℝ (Fin (d + 1)))} (hQ : IsOpen Q)
    (hQΩ' : Q ∩ Ω ⊆ Ω')
    {A : Fin (d + 1) → Fin (d + 1) →
      Lp ℝ ⊤ (volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    {a : Fin (d + 1) → Fin (d + 1) → EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hAa : ∀ k l, ⇑(A k l) =ᵐ[volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin (d + 1))))] a k l)
    (ha : ∀ k l, ContDiffOn ℝ (m + 1) (a k l) Q) {α : ℝ} (hα0 : 0 < α)
    (hell : ∀ y ∈ Q, ∀ ξ : EuclideanSpace ℝ (Fin (d + 1)),
      α * ‖ξ‖ ^ 2 ≤ ∑ k, ∑ l, a k l y * ξ k * ξ l)
    {K : Set (EuclideanSpace ℝ (Fin (d + 1)))} (hK : IsCompact K) (hKQ : K ⊆ Q)
    {w : SobolevEuclidean (d + 1) 1 2 Ω'} (hw : w ∈ SobolevEuclideanZero (d + 1) 1 2 Ω')
    (hwK : ∀ᵐ y ∂volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      y ∉ K → fn w y = 0)
    {g : Lp ℝ 2 (volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    (hg : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (⇑g) m 2 Ω'
      volume)
    (heq : ∀ ψ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω', generalForm Ω' A 0 0 w ψ = load Ω' g ψ) :
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (fn w) (m + 2) 2 Ω'
      volume := by
  have hΩ'm : MeasurableSet (Ω' : Set (EuclideanSpace ℝ (Fin (d + 1)))) :=
    Ω'.isOpen.measurableSet
  -- the cut-off `χ`, equal to `1` on the compact `L ⊇ K`, supported in the compact `L' ⊆ Q`
  obtain ⟨L, hL, hKL, hLQ⟩ := exists_compact_between hK hQ hKQ
  obtain ⟨L', hL', hLL', hL'Q⟩ := exists_compact_between hL hQ hLQ
  obtain ⟨χ, hχ, hχ1, hχL', hχ01⟩ := hL.exists_contDiff_eqOn_one isOpen_interior hLL'
  have hχQ : tsupport χ ⊆ Q := hχL'.trans (interior_subset.trans hL'Q)
  have hχc : HasCompactSupport χ :=
    hL'.of_isClosed_subset (isClosed_tsupport χ) (hχL'.trans interior_subset)
  have hχ' : ContDiff ℝ (m + 1) χ := hχ.of_le (by simp)
  have hχΩ' : tsupport χ ∩ Ω ⊆ Ω' := fun y hy ↦ hQΩ' ⟨hχQ hy.1, hy.2⟩
  -- the extended coefficients: multipliers, elliptic everywhere
  have hmult : ∀ k l, IsContDiffConstOffCompact (m + 1) (extendCoeff χ a k l) := fun k l ↦
    isContDiffConstOffCompact_extendCoeff hχ' hχc hQ ha hχQ k l
  have hell' : ∀ (y ξ : EuclideanSpace ℝ (Fin (d + 1))),
      min α 1 * ‖ξ‖ ^ 2 ≤ ∑ k, ∑ l, extendCoeff χ a k l y * ξ k * ξ l := fun y ξ ↦
    extendCoeff_elliptic hχ01 (T := univ) (s := Q) (fun y hy ↦ hχQ hy.1) hell (Set.mem_univ y) ξ
  obtain ⟨M₀, -, hM₀⟩ := exists_forall_abs_le_of_isContDiffConstOffCompact hmult
  have hmem : ∀ k l, MemLp (extendCoeff χ a k l) ⊤
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) := fun k l ↦
    memLp_top_of_bound (hmult k l).continuous.aestronglyMeasurable M₀
      (Eventually.of_forall fun y ↦ by
        rw [Real.norm_eq_abs]
        exact hM₀ k l y)
  -- the zero extension `W ∈ H^1_0(Ω)`
  obtain ⟨W, hW, hWfn, hWd⟩ := exists_extendZero_mem_zero hΩ' hw
  -- the extended datum, in `H^m(Ω)`
  have hgm : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      ((Ω' : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator fun y ↦ χ y * g y) m 2 Ω volume := by
    have := MemSobolevMultiIndex.indicator_smul_of_tsupport_subset one_le_two hΩ' hχ hχc hχΩ' hg
    refine this.congr_ae (Eventually.of_forall fun y ↦ ?_)
    simp only [smul_eq_mul]
  have hgmem := hgm.memLp
  -- the equation on `Ω`
  have heq' : ∀ Ψ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω,
      generalForm Ω (fun k l ↦ (hmem k l).toLp _) 0 0 W Ψ = load Ω (hgmem.toLp _) Ψ := by
    intro Ψ hΨ
    refine generalForm_eq_load_of_forall_testFunctions (fun Φ hΦ ↦ ?_) hΨ
    obtain ⟨ψ, hψ⟩ := hΦ
    rw [generalForm_zero_zero_apply_eq_of_ae_eq (fun k l ↦ (hmem k l).coeFn_toLp) W hψ,
      load_apply_eq_of_ae_eq hgmem.coeFn_toLp hψ]
    exact sum_integral_extendCoeff_eq hΩ' hQΩ' hχ hχQ hχ1 hK.isClosed hKL hAa hwK heq hWd ψ
  -- higher-order regularity on `Ω`
  have hW2 := memSobolevMultiIndex_of_tangential_of_order m hΩ (fun k l ↦ (hmem k l).coeFn_toLp)
    (lt_min hα0 one_pos) hell' hmult hW (hgm.congr_ae hgmem.coeFn_toLp.symm) heq'
  -- restriction to `Ω'`
  refine (hW2.mono_set hΩ').congr_ae ?_
  have h2 := ae_restrict_of_ae_restrict_of_subset hΩ' hWfn
  filter_upwards [h2, self_mem_ae_restrict hΩ'm] with y hy2 hyΩ'
  rw [hy2, Set.indicator_of_mem hyΩ']

end CylinderRegularityHigher



/-! ### Lemma 9.8 at higher order: the coefficients are `C^n` for a `C^{n+1}` chart -/

section ChartCoeffHigher

variable {N : ℕ}

/-- The Jacobian determinant of a `C^{n+1}` local diffeomorphism is `C^n` where it does not
vanish. -/
theorem contDiffOn_abs_det_fderiv_of_order (n : ℕ)
    {H : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)}
    {s : Set (EuclideanSpace ℝ (Fin N))} (hs : IsOpen s) (hH : ContDiffOn ℝ (n + 1) H s)
    (hdet : ∀ y ∈ s, (fderiv ℝ H y).det ≠ 0) :
    ContDiffOn ℝ n (fun y ↦ |(fderiv ℝ H y).det|) s := by
  have hdH : ContDiffOn ℝ n (fderiv ℝ H) s := hH.fderiv_of_isOpen hs (m := n) (by norm_cast)
  have h1 : ContDiffOn ℝ n (fun y ↦ (fderiv ℝ H y).det) s :=
    (ContinuousLinearMap.contDiff_det.of_le (by simp)).comp_contDiffOn hdH
  intro y hy
  exact (contDiffAt_abs (hdet y hy)).comp_contDiffWithinAt y (h1 y hy)

/-- The coefficients of the transferred equation are `C^n` where `H` is `C^{n+1}` with
nonvanishing Jacobian and maps into a set on which `J` is `C^{n+1}`. -/
theorem contDiffOn_chartCoeff_of_order (n : ℕ)
    {H J : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)}
    {s t : Set (EuclideanSpace ℝ (Fin N))} (hs : IsOpen s) (ht : IsOpen t)
    (hH : ContDiffOn ℝ (n + 1) H s) (hJ : ContDiffOn ℝ (n + 1) J t) (hHs : MapsTo H s t)
    (hdet : ∀ y ∈ s, (fderiv ℝ H y).det ≠ 0) (k l : Fin N) :
    ContDiffOn ℝ n (chartCoeff H J k l) s := by
  have hdJ : ContDiffOn ℝ n (fderiv ℝ J) t := hJ.fderiv_of_isOpen ht (m := n) (by norm_cast)
  have hJH : ∀ j i, ContDiffOn ℝ n (fun y ↦ fderiv ℝ J (H y) (EuclideanSpace.single j 1) i) s := by
    intro j i
    have h1 : ContDiffOn ℝ n (fun y ↦ fderiv ℝ J (H y)) s :=
      hdJ.comp (hH.of_le (by exact_mod_cast Nat.le_succ n)) hHs
    have h2 : ContDiffOn ℝ n (fun y ↦ fderiv ℝ J (H y) (EuclideanSpace.single j 1)) s :=
      h1.clm_apply contDiffOn_const
    exact (EuclideanSpace.proj i).contDiff.comp_contDiffOn h2
  exact (ContDiffOn.sum fun j _ ↦ (hJH j k).mul (hJH j l)).mul
    (contDiffOn_abs_det_fderiv_of_order n hs hH hdet)

end ChartCoeffHigher

/-! ### The boundary piece and the transfer, with their data made explicit -/

section BoundaryPieceData

variable {N : ℕ} {Ω' Ω : Opens (EuclideanSpace ℝ (Fin N))}
  {H J : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)} {M : ℝ}

open SobolevMultiIndex

/-- **The boundary piece `v = θ u` of a weak solution, with its datum**
(`Elliptic.exists_boundary_piece` with the datum `G = θ F − 2∇θ·∇u − (Δθ)u` made explicit). -/
theorem exists_boundary_piece_ae_eq (hΩ' : Ω' ≤ Ω) {θ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ)
    (hθΩ' : tsupport θ ∩ Ω ⊆ Ω') {u : SobolevEuclidean N 1 2 Ω}
    (hu : u ∈ SobolevEuclideanZero N 1 2 Ω)
    {F : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ Φ ∈ testFunctions ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume,
      dirichletForm Ω u Φ = load Ω F Φ) :
    ∃ (v : SobolevEuclidean N 1 2 Ω')
      (G : Lp ℝ 2 (volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N))))),
      v ∈ SobolevEuclideanZero N 1 2 Ω' ∧
      fn v =ᵐ[volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N)))] (fun x ↦ θ x * fn u x) ∧
      ⇑G =ᵐ[volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N)))] (fun x ↦ θ x * F x
        - 2 * ∑ i, fderiv ℝ θ x (EuclideanSpace.single i 1) * weakDeriv u (MultiIndexLE.single i) x
        - (∑ i, fderiv ℝ (fun z ↦ fderiv ℝ θ z (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1)) * fn u x) ∧
      ∀ Ψ ∈ SobolevEuclideanZero N 1 2 Ω', dirichletForm Ω' v Ψ = load Ω' G Ψ := by
  have hΩm : MeasurableSet (Ω : Set (EuclideanSpace ℝ (Fin N))) := Ω.isOpen.measurableSet
  have hθtop : IsSobolevCutoff (⊤ : Opens (EuclideanSpace ℝ (Fin N))) θ :=
    IsSobolevCutoff.of_hasCompactSupport hθ hθc (subset_univ _)
  obtain ⟨P, hP⟩ : ∃ P : SobolevEuclideanZero N 1 2 Ω →L[ℝ] SobolevEuclidean N 1 2 Ω',
      ∀ z, P z = restrictL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 volume
        (le_top (a := Ω')) (extendZeroMulL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 volume
          hθtop (SobolevEuclideanZero.extendZeroL N 2 Ω z)) :=
    ⟨(restrictL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 volume (le_top (a := Ω'))) ∘L
      (extendZeroMulL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 volume hθtop) ∘L
      (SobolevEuclideanZero.extendZeroL N 2 Ω), fun _ ↦ rfl⟩
  have hPfn := fn_boundaryPiece_of_ops hΩ' hθtop hP
  have hPd := weakDeriv_boundaryPiece_of_ops hΩ' hθtop hP
  have hgp := memLp_boundaryDatum hΩ' hθ hθc u F
  refine ⟨P ⟨u, hu⟩, hgp.toLp _, mem_zero_of_fn_ae_eq_contDiff_mul hΩ' hθ hθΩ' hPfn ⟨u, hu⟩,
    hPfn ⟨u, hu⟩, hgp.coeFn_toLp, fun Ψ hΨ ↦ ?_⟩
  refine dirichletForm_eq_load_of_forall_testFunctions (fun Φ hΦ ↦ ?_) hΨ
  obtain ⟨ψ, hψ⟩ := hΦ
  rw [dirichletForm_apply_eq_of_ae_eq (hPd ⟨u, hu⟩) hψ, load_apply_eq_of_ae_eq hgp.coeFn_toLp hψ]
  have hwd : ∀ i, HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1] (fn u)
      (weakDeriv u (MultiIndexLE.single i)) Ω volume := fun i ↦
    weakDeriv_hasWeakIteratedLineDerivOn_single u i
  have hcut := sum_integral_cutoff_eq (fun i ↦ EuclideanSpace.single i 1)
    ((memLp u).locallyIntegrableOn one_le_two) ((Lp.memLp F).locallyIntegrableOn one_le_two) hwd
    (forall_testFunction_weakDeriv_of_forall_testFunctions heq) hθ (ψ.ofLE hΩ')
  simp only [TestFunction.ofLE_coe] at hcut
  -- the integrals over `Ω` are integrals over `Ω'`
  have hsub : ∀ (F' : EuclideanSpace ℝ (Fin N) → ℝ),
      ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), F' x * ψ x
        = ∫ x in (Ω' : Set (EuclideanSpace ℝ (Fin N))), F' x * ψ x := fun F' ↦
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hΩm hΩ' fun x hx ↦ by
      rw [ψ.eq_zero_of_notMem hx.2, mul_zero]
  have hsub' : ∀ (F' : EuclideanSpace ℝ (Fin N) → ℝ) (i : Fin N),
      ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), F' x * fderiv ℝ ψ x (EuclideanSpace.single i 1)
        = ∫ x in (Ω' : Set (EuclideanSpace ℝ (Fin N))),
          F' x * fderiv ℝ ψ x (EuclideanSpace.single i 1) := fun F' i ↦
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hΩm hΩ' fun x hx ↦ by
      have := (ψ.fderivApply (EuclideanSpace.single i 1)).eq_zero_of_notMem hx.2
      rw [TestFunction.fderivApply_apply] at this
      rw [this, mul_zero]
  simp only [hsub, hsub'] at hcut
  exact hcut

/-- **Lemma 9.8, typed, with the transferred datum made explicit**: `Elliptic.transfer_chart`
together with `G̃ = (G ∘ H) |det DH|` almost everywhere (`Elliptic.chartDatum`). -/
theorem transfer_chart_ae_eq (h : IsDiffeoOnWithBoundedJacobian H J Ω' Ω M)
    {v : SobolevEuclidean N 1 2 Ω} (hv : v ∈ SobolevEuclideanZero N 1 2 Ω)
    {G : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ Ψ ∈ SobolevEuclideanZero N 1 2 Ω, dirichletForm Ω v Ψ = load Ω G Ψ) :
    ∃ (w : SobolevEuclidean N 1 2 Ω')
      (A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N)))))
      (G' : Lp ℝ 2 (volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N))))),
      w ∈ SobolevEuclideanZero N 1 2 Ω' ∧
      fn w =ᵐ[volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N)))] (fun y ↦ fn v (H y)) ∧
      (∀ k l, ⇑(A k l) =ᵐ[volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N)))]
        chartCoeff H J k l) ∧
      ⇑G' =ᵐ[volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N)))] chartDatum H G ∧
      ∀ Ψ ∈ SobolevEuclideanZero N 1 2 Ω', generalForm Ω' A 0 0 w Ψ = load Ω' G' Ψ := by
  obtain ⟨w, hw⟩ : ∃ w, w = SobolevEuclidean.compDiffeoL h v := ⟨_, rfl⟩
  refine ⟨w, fun k l ↦ (memLp_top_chartCoeff h k l).toLp _, (memLp_chartDatum h G).toLp _,
    hw ▸ compDiffeoL_mem_zero h hv, hw ▸ fn_compDiffeoL h v,
    fun k l ↦ (memLp_top_chartCoeff h k l).coeFn_toLp, (memLp_chartDatum h G).coeFn_toLp,
    fun Ψ hΨ ↦ ?_⟩
  refine generalForm_eq_load_of_forall_testFunctions (fun Φ hΦ ↦ ?_) hΨ
  obtain ⟨ψ, hψ⟩ := hΦ
  rw [generalForm_zero_zero_apply_eq_of_ae_eq (fun k l ↦ (memLp_top_chartCoeff h k l).coeFn_toLp)
    w hψ, load_apply_eq_of_ae_eq (memLp_chartDatum h G).coeFn_toLp hψ]
  exact sum_integral_chartCoeff_eq h heq hw ψ

end BoundaryPieceData



/-! ### Case C₂, higher order: a boundary piece `θᵢ u` is in `H^{m+2}(Ω)` -/

section BoundaryPieceHigher

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

open SobolevMultiIndex EuclideanSpace

/-- The datum `θ F − 2∇θ·∇u − (Δθ)u` of a boundary piece vanishes off the support of `θ`. -/
theorem boundaryDatum_eq_zero_of_notMem_tsupport {θ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    {u : SobolevEuclidean (d + 1) 1 2 Ω}
    {F : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    {x : EuclideanSpace ℝ (Fin (d + 1))} (hx : x ∉ tsupport θ) :
    θ x * F x - 2 * ∑ i, fderiv ℝ θ x (EuclideanSpace.single i 1)
      * weakDeriv u (MultiIndexLE.single i) x
      - (∑ i, fderiv ℝ (fun z ↦ fderiv ℝ θ z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1)) * fn u x = 0 := by
  have h0 : θ x = 0 := image_eq_zero_of_notMem_tsupport hx
  have h1 : ∀ i, fderiv ℝ θ x (EuclideanSpace.single i 1) = 0 := fun i ↦
    image_eq_zero_of_notMem_tsupport (f := fun x ↦ fderiv ℝ θ x (EuclideanSpace.single i 1))
      fun h ↦ hx (tsupport_fderiv_apply_subset ℝ _ h)
  have h2 : ∀ i, fderiv ℝ (fun z ↦ fderiv ℝ θ z (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single i 1) = 0 := fun i ↦
    image_eq_zero_of_notMem_tsupport
      (f := fun x ↦ fderiv ℝ (fun z ↦ fderiv ℝ θ z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1)) fun h ↦
      hx (tsupport_fderiv_apply_subset ℝ _ (tsupport_fderiv_apply_subset ℝ _ h))
  simp only [h0, h1, h2, zero_mul, mul_zero, Finset.sum_const_zero, sub_zero]

/-- **A boundary piece of a weak solution is in `H^{m+2}(Ω)`** — [brezis2011functional] §9.6,
proof of Theorem 9.25, case C₂ at higher order: for a `C^{m+2}` chart `H : Q → U` of `Ω`, a
smooth `θ` with compact support in `U`, and `u ∈ H^1_0(Ω) ∩ H^{m+1}(Ω)` with
`∫_Ω ∇u · ∇Φ = ∫_Ω F Φ` for the test-function elements `Φ` and `F ∈ H^m(Ω)`, the function
`θ u` lies in `H^{m+2}(Ω)`.

The steps of the `H²` case (`Elliptic.memSobolevMultiIndex_two_boundary_piece`) one order up:
the datum `G = θ F − 2∇θ·∇u − (Δθ) u` of `v = θ u` lies in `H^m(Ω ∩ U)`; its transfer
`(G ∘ H) |det DH|` lies in `H^m(Q₊)` (`Elliptic.memSobolevMultiIndex_comp_chart_of_order` on a
smaller half cylinder containing the support, and a cut-off); the higher-order theorem on the
cylinder (`Elliptic.memSobolevMultiIndex_of_tangential_of_compact_of_order`) gives
`w = v ∘ H ∈ H^{m+2}(Q₊)`, and the return through the `C^{m+2}` inverse chart at order `m + 2`
gives `θ u ∈ H^{m+2}(Ω)`. -/
theorem memSobolevMultiIndex_boundary_piece_of_order (m : ℕ) (c : ContDiffChart (m + 2) (Ω : Set _))
    {θ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ)
    (hθU : tsupport θ ⊆ c.U) {u : SobolevEuclidean (d + 1) 1 2 Ω}
    (hu : u ∈ SobolevEuclideanZero (d + 1) 1 2 Ω)
    (hum : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (fn u) (m + 1) 2
      Ω volume)
    {F : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    (hF : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (⇑F) m 2 Ω
      volume)
    (heq : ∀ Φ ∈ testFunctions ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume,
      dirichletForm Ω u Φ = load Ω F Φ) :
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (fun x ↦ θ x * fn u x) (m + 2) 2 Ω volume := by
  have hΩm : MeasurableSet (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) := Ω.isOpen.measurableSet
  -- the open sets: `Ω ∩ U`, a smaller `Ω ∩ U'` with `supp θ ⊆ U' ⋐ U`, `Q₊`, and the half space
  obtain ⟨L, hL, hθL, hLU⟩ := exists_compact_between hθc c.isOpen_U hθU
  obtain ⟨Ω₁, hΩ₁⟩ : ∃ Ω₁ : Opens (EuclideanSpace ℝ (Fin (d + 1))),
    Ω₁ = ⟨c.U ∩ Ω, c.isOpen_U.inter Ω.isOpen⟩ := ⟨_, rfl⟩
  obtain ⟨Ω₂, hΩ₂⟩ : ∃ Ω₂ : Opens (EuclideanSpace ℝ (Fin (d + 1))),
    Ω₂ = ⟨interior L ∩ Ω, isOpen_interior.inter Ω.isOpen⟩ := ⟨_, rfl⟩
  obtain ⟨Qp, hQp⟩ : ∃ Qp : Opens (EuclideanSpace ℝ (Fin (d + 1))),
    Qp = ⟨unitChartCubePos d, isOpen_unitChartCubePos⟩ := ⟨_, rfl⟩
  have hΩ₁s : (Ω₁ : Set (EuclideanSpace ℝ (Fin (d + 1)))) = c.U ∩ Ω := by rw [hΩ₁]; rfl
  have hΩ₂s : (Ω₂ : Set (EuclideanSpace ℝ (Fin (d + 1)))) = interior L ∩ Ω := by rw [hΩ₂]; rfl
  have hQps : (Qp : Set (EuclideanSpace ℝ (Fin (d + 1)))) = unitChartCubePos d := by rw [hQp]; rfl
  have hΩ₁Ω : Ω₁ ≤ Ω := by rw [hΩ₁]; exact inter_subset_right
  have hΩ₂Ω₁ : Ω₂ ≤ Ω₁ := by
    rw [hΩ₁, hΩ₂]
    exact inter_subset_inter_left _ (interior_subset.trans hLU)
  have hΩ₂Ω : Ω₂ ≤ Ω := hΩ₂Ω₁.trans hΩ₁Ω
  have hLc : IsCompact (closure (interior L)) :=
    hL.of_isClosed_subset isClosed_closure (closure_minimal interior_subset hL.isClosed)
  have hn1 : (1 : WithTop ℕ∞) ≤ ((m + 2 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast Nat.le_add_left 1 (m + 1)
  -- the boundary piece `v = θ u ∈ H^1_0(Ω ∩ U)`, its datum and its equation
  have hθΩ₁ : tsupport θ ∩ Ω ⊆ Ω₁ := by
    rw [hΩ₁s]
    exact inter_subset_inter_left _ hθU
  obtain ⟨v, G, hv, hvfn, hGae, hveq⟩ := exists_boundary_piece_ae_eq hΩ₁Ω hθ hθc hθΩ₁ hu heq
  -- the datum lies in `H^m(Ω ∩ U)`
  have hθmult : IsContDiffConstOffCompact (m + 1) θ :=
    IsContDiffConstOffCompact.of_hasCompactSupport (hθ.of_le (by simp)) hθc
  have hGm : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (⇑G) m 2 Ω₁
      volume := by
    have hw : ∀ i, MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
        (weakDeriv u (MultiIndexLE.single i)) m 2 Ω volume := by
      intro i
      obtain ⟨-, hd⟩ := memSobolevMultiIndex_succ_iff.1 hum
      obtain ⟨w, hw, hwm⟩ := hd i
      rw [EuclideanSpace.basisFun_toBasis_apply] at hw
      exact hwm.congr_ae ((ae_restrict_iff' hΩm).2
        (hw.ae_eq (weakDeriv_hasWeakIteratedLineDerivOn_single u i)))
    have h1 := MemSobolevMultiIndex.mul_of_isContDiffConstOffCompact m
      (hθmult.of_le (Nat.le_succ m)) hF
    have h2 := MemSobolevMultiIndex.finset_sum Finset.univ
      (f := fun i x ↦ fderiv ℝ θ x (EuclideanSpace.single i 1)
        * weakDeriv u (MultiIndexLE.single i) x) fun i _ ↦
      MemSobolevMultiIndex.mul_of_isContDiffConstOffCompact m (hθmult.fderiv_apply _) (hw i)
    obtain ⟨hΔ, hΔc, -⟩ := laplacianRep_props hθ hθc
    have h3 := MemSobolevMultiIndex.mul_of_isContDiffConstOffCompact m
      (IsContDiffConstOffCompact.of_hasCompactSupport (hΔ.of_le (by simp)) hΔc)
      (hum.mono_order (Nat.le_succ m))
    have := ((h1.sub (h2.const_smul 2)).sub h3).mono_set hΩ₁Ω
    refine this.congr_ae (EventuallyEq.trans (Eventually.of_forall fun x ↦ ?_) hGae.symm)
    simp only [Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  -- the chart as a diffeomorphism `Q₊ → Ω ∩ U`, and the transfer
  obtain ⟨M, h⟩ := c.isDiffeoOnWithBoundedJacobian_pos hn1 Ω.isOpen
  have h' : IsDiffeoOnWithBoundedJacobian c.toFun c.invFun (Qp : Set _) (Ω₁ : Set _) M := by
    rw [hQps, hΩ₁s]; exact h
  obtain ⟨w, A, G', hw, hwfn, hAa, hG'ae, hweq⟩ := transfer_chart_ae_eq h' hv hveq
  -- `w` vanishes off the compact `K = H⁻¹(supp θ) ⊆ Q`
  obtain ⟨K, hK⟩ : ∃ K : Set (EuclideanSpace ℝ (Fin (d + 1))), K = c.invFun '' tsupport θ :=
    ⟨_, rfl⟩
  have hKc : IsCompact K := by
    rw [hK]
    exact hθc.image_of_continuousOn (c.contDiffOn_invFun.continuousOn.mono
      (hθU.trans subset_closure))
  have hKQ : K ⊆ unitChartCube d := by
    rw [hK]
    exact (c.mapsTo_invFun.mono_left hθU).image_subset
  have hHK : ∀ y ∈ (Qp : Set (EuclideanSpace ℝ (Fin (d + 1)))), y ∉ K →
      c.toFun y ∉ tsupport θ := by
    intro y hyQ hyK hθy
    refine hyK ?_
    rw [hK]
    refine ⟨c.toFun y, hθy, ?_⟩
    rw [hQps] at hyQ
    exact c.invFun_toFun (unitChartCubePos_subset hyQ)
  have hwK : ∀ᵐ y ∂volume.restrict (Qp : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      y ∉ K → fn w y = 0 := by
    filter_upwards [hwfn, h'.ae_comp_restrict hvfn, self_mem_ae_restrict Qp.isOpen.measurableSet]
      with y hy1 hy2 hyQ hyK
    rw [hy1, hy2, image_eq_zero_of_notMem_tsupport (hHK y hyQ hyK), zero_mul]
  -- the chart on the whole cylinder, its coefficients and their ellipticity
  obtain ⟨M₀, hM₀⟩ := c.isDiffeoOnWithBoundedJacobian hn1
  have hH2 : ContDiffOn ℝ (m + 1 + 1) c.toFun (unitChartCube d) := c.contDiffOn.mono subset_closure
  have hJ2 : ContDiffOn ℝ (m + 1 + 1) c.invFun c.U := c.contDiffOn_invFun.mono subset_closure
  have hdet : ∀ y ∈ unitChartCube d, (fderiv ℝ c.toFun y).det ≠ 0 := fun y hy ↦
    hM₀.det_fderiv_ne_zero hy
  have ha : ∀ k l, ContDiffOn ℝ (m + 1) (chartCoeff c.toFun c.invFun k l) (unitChartCube d) :=
    contDiffOn_chartCoeff_of_order (m + 1) isOpen_unitChartCube c.isOpen_U hH2 hJ2 c.mapsTo hdet
  obtain ⟨α, hα0, hell⟩ := chartCoeff_elliptic hM₀
  have hQphalf : Qp ≤ upperHalfSpaceOpens d := by
    rw [hQp]
    exact fun y hy ↦ hy.2
  have hQΩ' : unitChartCube d ∩ (upperHalfSpaceOpens d : Set _) ⊆ Qp := by
    rw [hQps]
    exact fun y hy ↦ hy
  -- the transferred datum lies in `H^m(Q₊)`
  have hG'm : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (⇑G') m 2 Qp
      volume := by
    obtain ⟨L₂, hL₂, hKL₂, hL₂Q⟩ := exists_compact_between hKc isOpen_unitChartCube hKQ
    obtain ⟨Q', hQ'⟩ : ∃ Q' : Opens (EuclideanSpace ℝ (Fin (d + 1))),
      Q' = ⟨interior L₂ ∩ upperHalfSpace d, isOpen_interior.inter isOpen_upperHalfSpace⟩ :=
      ⟨_, rfl⟩
    have hQ's : (Q' : Set (EuclideanSpace ℝ (Fin (d + 1)))) = interior L₂ ∩ upperHalfSpace d := by
      rw [hQ']; rfl
    have hQ'Qp : Q' ≤ Qp := by
      rw [hQ', hQp]
      exact inter_subset_inter_left _ (interior_subset.trans hL₂Q)
    have hQ'Qp' : (Q' : Set (EuclideanSpace ℝ (Fin (d + 1))))
        ⊆ (Qp : Set (EuclideanSpace ℝ (Fin (d + 1)))) := hQ'Qp
    have hQ'L₂ : (Q' : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ L₂ := by
      rw [hQ's]
      exact inter_subset_left.trans interior_subset
    -- the chart restricted to `H(Q'₊) → Q'₊`, and `G ∘ H ∈ H^m(Q'₊)`
    have hres := h'.symm.restrict_target Q'.isOpen hQ'Qp'
    obtain ⟨Ω₃, hΩ₃⟩ : ∃ Ω₃ : Opens (EuclideanSpace ℝ (Fin (d + 1))),
      Ω₃ = ⟨c.toFun '' Q', hres.isOpen_source⟩ := ⟨_, rfl⟩
    have hΩ₃s : (Ω₃ : Set _) = c.toFun '' Q' := by rw [hΩ₃]; rfl
    have hres' : IsDiffeoOnWithBoundedJacobian c.invFun c.toFun (Ω₃ : Set _) (Q' : Set _) M := by
      rw [hΩ₃s]; exact hres
    have hΩ₃Ω₁ : Ω₃ ≤ Ω₁ := by
      change (Ω₃ : Set (EuclideanSpace ℝ (Fin (d + 1))))
        ⊆ (Ω₁ : Set (EuclideanSpace ℝ (Fin (d + 1))))
      rw [hΩ₃s]
      exact h'.image_subset hQ'Qp'
    have hHm : ContDiffOn ℝ m c.toFun (unitChartCube d) :=
      hH2.of_le (by exact_mod_cast Nat.le_add_right m 2)
    have hGH := memSobolevMultiIndex_comp_chart_of_order m hres' isOpen_unitChartCube hHm hL₂
      hQ'L₂ hL₂Q (hGm.mono_set hΩ₃Ω₁)
    -- the cut-offs `χ₂ = 1` on `K` with support in `interior L₂`, `χ₃ = 1` on `L₂` with support
    -- in `Q`
    obtain ⟨χ₂, hχ₂, hχ₂1, hχ₂c, hχ₂L⟩ := exists_contDiff_eqOn_one_hasCompactSupport
      (Ω := ⟨interior L₂, isOpen_interior⟩) hKc hKL₂
    obtain ⟨χ₃, hχ₃, hχ₃1, hχ₃c, hχ₃Q⟩ := exists_contDiff_eqOn_one_hasCompactSupport
      (Ω := ⟨unitChartCube d, isOpen_unitChartCube⟩) hL₂ hL₂Q
    have hχ₂Qp : tsupport χ₂ ∩ Qp ⊆ Q' := by
      rw [hQ's]
      rintro y ⟨hy1, hy2⟩
      exact ⟨hχ₂L hy1, (hQphalf hy2 : y ∈ upperHalfSpace d)⟩
    have hind := MemSobolevMultiIndex.indicator_smul_of_tsupport_subset one_le_two hQ'Qp hχ₂ hχ₂c
      hχ₂Qp hGH
    -- the multiplier `χ₃ |det DH|`
    have hdetm : IsContDiffConstOffCompact m fun y ↦ χ₃ y * |(fderiv ℝ c.toFun y).det| :=
      IsContDiffConstOffCompact.of_hasCompactSupport
        ((hχ₃.of_le (by simp)).mul_contDiffOn_of_tsupport_subset isOpen_unitChartCube
          (contDiffOn_abs_det_fderiv_of_order m isOpen_unitChartCube
            (hH2.of_le (by exact_mod_cast Nat.le_succ (m + 1))) hdet) hχ₃Q) hχ₃c.mul_right
    have hprod := MemSobolevMultiIndex.mul_of_isContDiffConstOffCompact m hdetm hind
    refine hprod.congr_ae ?_
    filter_upwards [hG'ae, h'.ae_comp_restrict hGae, self_mem_ae_restrict Qp.isOpen.measurableSet]
      with y hy1 hy2 hyQp
    rw [hy1]
    simp only [chartDatum]
    by_cases hyK : y ∈ K
    · have hyQ' : y ∈ (Q' : Set (EuclideanSpace ℝ (Fin (d + 1)))) := by
        rw [hQ's]
        exact ⟨hKL₂ hyK, hQphalf hyQp⟩
      rw [Set.indicator_of_mem hyQ', hχ₂1 hyK, hχ₃1 (interior_subset (hKL₂ hyK)), Pi.one_apply,
        smul_eq_mul]
      ring
    · have hG0 : G (c.toFun y) = 0 := by
        rw [hy2]
        exact boundaryDatum_eq_zero_of_notMem_tsupport (hHK y hyQp hyK)
      rw [hG0, zero_mul]
      by_cases hyQ' : y ∈ (Q' : Set (EuclideanSpace ℝ (Fin (d + 1))))
      · rw [Set.indicator_of_mem hyQ', hG0, smul_zero, mul_zero]
      · rw [Set.indicator_of_notMem hyQ', mul_zero]
  -- `H^{m+2}` on `Q₊` by the higher-order theorem on the cylinder
  have hw2 := memSobolevMultiIndex_of_tangential_of_compact_of_order m
    (fun j hj t ↦ upperHalfSpaceOpens_isTranslationInvariant j hj t) hQphalf isOpen_unitChartCube
    hQΩ' hAa ha hα0 hell hKc hKQ hw hwK hG'm hweq
  -- back to `Ω ∩ U'` through the restricted chart
  have hΩ₂Ω₁' : (Ω₂ : Set (EuclideanSpace ℝ (Fin (d + 1))))
      ⊆ (Ω₁ : Set (EuclideanSpace ℝ (Fin (d + 1)))) := hΩ₂Ω₁
  have hres := h'.restrict_target Ω₂.isOpen hΩ₂Ω₁'
  obtain ⟨Ω₃, hΩ₃⟩ : ∃ Ω₃ : Opens (EuclideanSpace ℝ (Fin (d + 1))),
    Ω₃ = ⟨c.invFun '' Ω₂, hres.isOpen_source⟩ := ⟨_, rfl⟩
  have hΩ₃s : (Ω₃ : Set _) = c.invFun '' Ω₂ := by rw [hΩ₃]; rfl
  have hres' : IsDiffeoOnWithBoundedJacobian c.toFun c.invFun (Ω₃ : Set _) (Ω₂ : Set _) M := by
    rw [hΩ₃s]; exact hres
  have hΩ₃Qp : Ω₃ ≤ Qp := by
    change (Ω₃ : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ (Qp : Set (EuclideanSpace ℝ (Fin (d + 1))))
    rw [hΩ₃s]
    exact h'.symm.image_subset hΩ₂Ω₁'
  have hΩ₂K : (Ω₂ : Set _) ⊆ closure (interior L) := by
    rw [hΩ₂s]
    exact inter_subset_left.trans subset_closure
  have hKU : closure (interior L) ⊆ c.U :=
    (closure_minimal interior_subset hL.isClosed).trans hLU
  have hback := memSobolevMultiIndex_comp_chart_of_order (m + 2) hres' c.isOpen_U hJ2 hLc hΩ₂K
    hKU (hw2.mono_set hΩ₃Qp)
  -- `fn w ∘ J = θ u` on `Ω ∩ U'`
  have hθu : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (fun x ↦ θ x * fn u x) (m + 2) 2 Ω₂ volume := by
    refine hback.congr_ae ?_
    have h1 := h'.symm.ae_comp_restrict hwfn
    have h2 := hvfn
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hΩ₂Ω₁' h1,
      ae_restrict_of_ae_restrict_of_subset hΩ₂Ω₁' h2,
      self_mem_ae_restrict Ω₂.isOpen.measurableSet] with x hx1 hx2 hxΩ₂
    rw [hx1, h'.invOn.2 (hΩ₂Ω₁' hxΩ₂), hx2]
  -- zero extension across the edge of the chart
  obtain ⟨η, hη, hη1, hηc, hηL⟩ := exists_contDiff_eqOn_one_hasCompactSupport (Ω := ⟨interior L,
    isOpen_interior⟩) (hθc : IsCompact (tsupport θ)) hθL
  have hηΩ₂ : tsupport η ∩ Ω ⊆ Ω₂ := by
    rw [hΩ₂s]
    exact inter_subset_inter_left _ hηL
  have hext := MemSobolevMultiIndex.indicator_smul_of_tsupport_subset one_le_two hΩ₂Ω hη hηc hηΩ₂
    hθu
  refine hext.congr_ae ?_
  filter_upwards [self_mem_ae_restrict Ω.isOpen.measurableSet] with x hxΩ
  by_cases hx : x ∈ (Ω₂ : Set (EuclideanSpace ℝ (Fin (d + 1))))
  · rw [Set.indicator_of_mem hx, smul_eq_mul]
    by_cases hxθ : x ∈ tsupport θ
    · rw [hη1 hxθ, Pi.one_apply, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hxθ, zero_mul, mul_zero]
  · rw [Set.indicator_of_notMem hx]
    have hxθ : x ∉ tsupport θ := fun hxθ ↦ hx (by rw [hΩ₂s]; exact ⟨hθL hxθ, hxΩ⟩)
    rw [image_eq_zero_of_notMem_tsupport hxθ, zero_mul]

end BoundaryPieceHigher



/-! ### The interior piece `θ₀ u` at higher order -/

section InteriorPieceHigher

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

open SobolevMultiIndex

/-- The support of the Laplacian `∑ᵢ ∂ᵢ∂ᵢθ` of a smooth `θ` lies in the support of `θ`. -/
theorem tsupport_laplacianRep_subset {θ : EuclideanSpace ℝ (Fin N) → ℝ} :
    tsupport (fun x ↦ ∑ i, fderiv ℝ (fun z ↦ fderiv ℝ θ z (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single i 1)) ⊆ tsupport θ := by
  refine closure_minimal ((Finset.support_sum _ _).trans ?_) (isClosed_tsupport θ)
  refine Set.iUnion₂_subset fun i _ ↦ subset_closure.trans ?_
  exact (tsupport_fderiv_apply_subset ℝ _).trans (tsupport_fderiv_apply_subset ℝ _)

/-- The Laplacian of a smooth function constant off a compact set has compact support. -/
theorem hasCompactSupport_laplacianRep {θ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hθ : ContDiff ℝ ∞ θ) {κ : ℝ} (hθκ : HasCompactSupport fun x ↦ θ x - κ) :
    HasCompactSupport (fun x ↦ ∑ i, fderiv ℝ (fun z ↦ fderiv ℝ θ z (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single i 1)) := by
  obtain ⟨-, hc, -⟩ := laplacianRep_props (hθ.sub contDiff_const) hθκ
  have e : (fun x ↦ ∑ i, fderiv ℝ (fun z ↦ fderiv ℝ θ z (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single i 1))
      = fun x ↦ ∑ i, fderiv ℝ (fun z ↦ fderiv ℝ (fun x ↦ θ x - κ) z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1) := by
    funext x
    simp only [fderiv_sub_const]
  rw [e]
  exact hc

/-- **The interior piece `θ₀ u` is in `H^{m+2}(Ω)`** — [brezis2011functional] §9.6, proof of
Theorem 9.25, case C₁ at higher order: for a smooth `θ₀` constant off a compact set with support
off `∂Ω`, and `u ∈ H¹(Ω) ∩ H^{m+1}(Ω)` with `∫_Ω ∇u · ∇Φ = ∫_Ω F Φ` for the test-function elements
`Φ` and `F ∈ H^m(Ω)`, the function `θ₀ u` lies in `H^{m+2}(Ω)`: its zero extension solves
`−Δ(θ₀u) = θ₀F − 2∇θ₀·∇u − (Δθ₀)u` on `ℝ^N`, whose right side lies in `H^m(ℝ^N)` by
`MemSobolevMultiIndex.indicator_mul_of_hasCompactSupport_sub`, and case A at higher order
applies (`Elliptic.regularity_top_higher`). -/
theorem memSobolevMultiIndex_interior_piece_of_order (m : ℕ)
    {θ : EuclideanSpace ℝ (Fin N) → ℝ} (hθ : ContDiff ℝ ∞ θ) {κ : ℝ}
    (hθκ : HasCompactSupport fun x ↦ θ x - κ)
    (hθΓ : Disjoint (tsupport θ) (frontier (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    {u : SobolevEuclidean N 1 2 Ω}
    (hum : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (fn u) (m + 1) 2 Ω
      volume)
    {F : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hF : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (⇑F) m 2 Ω volume)
    (heq : ∀ Φ ∈ testFunctions ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume,
      dirichletForm Ω u Φ = load Ω F Φ) :
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
      (fun x ↦ θ x * fn u x) (m + 2) 2 Ω volume := by
  have hΩm : MeasurableSet (Ω : Set (EuclideanSpace ℝ (Fin N))) := Ω.isOpen.measurableSet
  have hcut : IsSobolevCutoff Ω θ := IsSobolevCutoff.of_hasCompactSupport_sub hθ hθκ hθΓ
  obtain ⟨M, hM⟩ := hcut.exists_bound
  -- the zero extension `V = \overline{θ u} ∈ H¹(ℝ^N)`
  obtain ⟨V, hV⟩ : ∃ V : SobolevEuclidean N 1 2 ⊤,
    V = extendZeroMulL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 volume hcut u := ⟨_, rfl⟩
  have hVfn : fn V =ᵐ[volume]
      (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator fun x ↦ θ x * fn u x := by
    rw [hV]
    exact fn_extendZeroMulL hcut u
  have hVd : ∀ i, ⇑(weakDeriv V (MultiIndexLE.single i)) =ᵐ[volume]
      (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator fun x ↦
        θ x * weakDeriv u (MultiIndexLE.single i) x
          + fderiv ℝ θ x (EuclideanSpace.single i 1) * fn u x := fun i ↦ by
    rw [hV]
    have := weakDeriv_extendZeroMulL_single hcut u i
    rw [EuclideanSpace.basisFun_toBasis_apply] at this
    exact this
  -- the first derivatives of `u` lie in `H^m(Ω)`
  have hw : ∀ i, MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
      (weakDeriv u (MultiIndexLE.single i)) m 2 Ω volume := by
    intro i
    obtain ⟨-, hd⟩ := memSobolevMultiIndex_succ_iff.1 hum
    obtain ⟨w, hw, hwm⟩ := hd i
    rw [EuclideanSpace.basisFun_toBasis_apply] at hw
    exact hwm.congr_ae ((ae_restrict_iff' hΩm).2
      (hw.ae_eq (weakDeriv_hasWeakIteratedLineDerivOn_single u i)))
  -- the datum `1_Ω (θ F − 2∇θ·∇u − (Δθ) u)`, in `H^m(ℝ^N)`
  obtain ⟨G, hG⟩ : ∃ G : EuclideanSpace ℝ (Fin N) → ℝ,
    G = (Ω : Set (EuclideanSpace ℝ (Fin N))).indicator fun x ↦ θ x * F x
      - 2 * ∑ i, fderiv ℝ θ x (EuclideanSpace.single i 1) * weakDeriv u (MultiIndexLE.single i) x
      - (∑ i, fderiv ℝ (fun z ↦ fderiv ℝ θ z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1)) * fn u x := ⟨_, rfl⟩
  have hGm : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis G m 2 ⊤ volume := by
    have h1 := MemSobolevMultiIndex.indicator_mul_of_hasCompactSupport_sub m hθ ⟨κ, hθκ⟩ hθΓ hF
    have h2 : ∀ i, MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
        ((Ω : Set (EuclideanSpace ℝ (Fin N))).indicator fun x ↦
          fderiv ℝ θ x (EuclideanSpace.single i 1) * weakDeriv u (MultiIndexLE.single i) x) m 2 ⊤
        volume := fun i ↦ by
      refine MemSobolevMultiIndex.indicator_mul_of_hasCompactSupport_sub m
        (hcut.contDiff_fderiv_apply _) ⟨0, ?_⟩ (tsupport_fderiv_apply_disjoint_frontier hθΓ _)
        (hw i)
      have := hθκ.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
      have e : (fun x ↦ fderiv ℝ θ x (EuclideanSpace.single i 1) - 0)
          = fun x ↦ fderiv ℝ (fun x ↦ θ x - κ) x (EuclideanSpace.single i 1) := by
        funext x
        simp only [fderiv_sub_const, sub_zero]
      rw [e]
      exact this
    have h3 := MemSobolevMultiIndex.indicator_mul_of_hasCompactSupport_sub m
      (ContDiff.sum fun i _ ↦ contDiff_fderiv_fderiv_apply hθ (EuclideanSpace.single i 1))
      ⟨0, by simpa using hasCompactSupport_laplacianRep hθ hθκ⟩
      (hθΓ.mono_left tsupport_laplacianRep_subset) (hum.mono_order (Nat.le_succ m))
    have := (h1.sub ((MemSobolevMultiIndex.finset_sum Finset.univ fun i _ ↦ h2 i).const_smul
      2)).sub h3
    refine this.congr_ae (Eventually.of_forall fun x ↦ ?_)
    rw [hG]
    by_cases hx : x ∈ (Ω : Set (EuclideanSpace ℝ (Fin N)))
    · simp only [Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, Set.indicator_of_mem hx,
        smul_eq_mul, Finset.mul_sum]
    · simp [Set.indicator_of_notMem hx]
  have hG' : MemLp G 2
      (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) : Set (EuclideanSpace ℝ (Fin N)))) :=
    hGm.memLp
  -- the equation on `ℝ^N`
  have heqV : ∀ Φ ∈ testFunctions ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2
      (⊤ : Opens (EuclideanSpace ℝ (Fin N))) volume,
      dirichletForm ⊤ V Φ = load ⊤ (hG'.toLp _) Φ := by
    intro Φ hΦ
    obtain ⟨ψ, hψ⟩ := hΦ
    rw [dirichletForm_apply_eq_of_ae_eq (fun i ↦ ae_restrict_of_ae (hVd i)) hψ,
      load_apply_eq_of_ae_eq hG'.coeFn_toLp hψ, hG]
    simp only [Opens.coe_top, Measure.restrict_univ]
    exact sum_integral_indicator_cutoff_eq (fun i ↦ EuclideanSpace.single i (1 : ℝ))
      ((memLp u).locallyIntegrableOn one_le_two) ((Lp.memLp F).locallyIntegrableOn one_le_two)
      (fun i ↦ weakDeriv_hasWeakIteratedLineDerivOn_single u i)
      (forall_testFunction_weakDeriv_of_forall_testFunctions heq) hcut ψ
  have heqV' : ∀ Φ, dirichletForm ⊤ V Φ = load ⊤ (hG'.toLp _) Φ := fun Φ ↦
    dirichletForm_eq_load_of_forall_testFunctions heqV (by
      rw [SobolevEuclideanZero.eq_top (p := 2) ENNReal.ofNat_ne_top]
      exact Submodule.mem_top)
  have hV2 := regularity_top_higher m V _ (hGm.congr_ae hG'.coeFn_toLp.symm) heqV'
  refine (hV2.mono_set le_top).congr_ae ?_
  filter_upwards [ae_restrict_of_ae hVfn, self_mem_ae_restrict hΩm] with x hx hxΩ
  rw [hx, Set.indicator_of_mem hxΩ]

end InteriorPieceHigher

/-! ### Theorem 9.25, the `H^{m+2}` clause: the assembly -/

section AssemblyHigher

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

open SobolevMultiIndex

/-- **[brezis2011functional] Theorem 9.25, the `H^{m+2}` membership**: let `Ω ⊆ ℝ^N` be open
of class `C^{m+2}` with bounded boundary, and let `u ∈ H^1_0(Ω)` satisfy
`∫_Ω ∇u · ∇Φ = ∫_Ω g Φ` for all `Φ ∈ H^1_0(Ω)` with `g ∈ H^m(Ω)`. Then `u ∈ H^{m+2}(Ω)`. (For
the book's `−Δu + u = f`, take `g = f − u`; `Elliptic.regularity_dirichlet_higher` does so.)

Induction on `m` ("the implication `f ∈ H^m ⇒ u ∈ H^{m+2}` is done by induction on `m` as in
cases A and B"): the inductive hypothesis gives `u ∈ H^{m+1}(Ω)`, and `u = θ₀ u + ∑ᵢ θᵢ u` for
a partition of unity subordinate to a finite atlas of `C^{m+2}` charts, with the interior piece
in `H^{m+2}(Ω)` by case A (`Elliptic.memSobolevMultiIndex_interior_piece_of_order`) and each
boundary piece by cases B and C₂ (`Elliptic.memSobolevMultiIndex_boundary_piece_of_order`). -/
theorem regularity_dirichlet_higher_mem (m : ℕ) :
    IsContDiffChartDomain (m + 2) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) →
    Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) →
    ∀ {u : SobolevEuclidean (d + 1) 1 2 Ω}, u ∈ SobolevEuclideanZero (d + 1) 1 2 Ω →
    ∀ {g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))},
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (⇑g) m 2 Ω volume →
    (∀ Φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω, dirichletForm Ω u Φ = load Ω g Φ) →
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (fn u) (m + 2) 2 Ω
      volume := by
  induction m with
  | zero =>
    intro hΩ hΓ u hu g _ heq
    exact regularity_dirichlet_mem (hΩ.of_le (by simp)) hΓ hu heq
  | succ m ih =>
    intro hΩ hΓ u hu g hg heq
    have heq' : ∀ Φ ∈ testFunctions ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
        volume, dirichletForm Ω u Φ = load Ω g Φ := fun Φ hΦ ↦
      heq Φ (SobolevMultiIndexZero.testFunctions_le hΦ)
    -- the inductive hypothesis: `u ∈ H^{m+2}(Ω)`
    have hum := ih (hΩ.of_le (by exact_mod_cast Nat.le_succ (m + 2))) hΓ hu
      (hg.mono_order (Nat.le_succ m)) heq
    -- the finite atlas and the partition of unity
    have hΓc : IsCompact (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
      Metric.isCompact_of_isClosed_isBounded isClosed_frontier hΓ
    obtain ⟨k, c, hcov⟩ := hΩ.exists_finite_atlas hΓ
    obtain ⟨θ₀, θ, hθ₀, hθ, -, -, hsum, hθc, hθU, hθ₀Γ⟩ :=
      hΓc.exists_contDiff_partitionOfUnity (fun i ↦ (c i).isOpen_U) hcov
    -- the boundary pieces
    have hbdry : ∀ i, MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
        (fun x ↦ θ i x * fn u x) (m + 1 + 2) 2 Ω volume := fun i ↦
      memSobolevMultiIndex_boundary_piece_of_order (m + 1) (c i) (hθ i) (hθc i) (hθU i) hu hum hg
        heq'
    -- the interior piece: `θ₀ = 1 − G` with `G = ∑ᵢ θᵢ` smooth and compactly supported
    obtain ⟨G, hG⟩ : ∃ G : EuclideanSpace ℝ (Fin (d + 1)) → ℝ, G = fun x ↦ ∑ i, θ i x := ⟨_, rfl⟩
    have hGc : HasCompactSupport G := by
      refine (isCompact_iUnion fun i ↦ hθc i).of_isClosed_subset (isClosed_tsupport G) ?_
      refine closure_minimal ?_ (isClosed_iUnion_of_finite fun i ↦ isClosed_tsupport (θ i))
      rw [hG]
      exact (Finset.support_sum _ _).trans (Set.iUnion₂_subset fun i _ ↦
        subset_closure.trans (Set.subset_iUnion (fun i ↦ tsupport (θ i)) i))
    have hθ₀κ : HasCompactSupport fun x ↦ θ₀ x - 1 := by
      have e : (fun x ↦ θ₀ x - 1) = fun x ↦ -G x := by
        funext x
        rw [hG]
        linarith [hsum x]
      rw [e]
      exact hGc.neg
    have hint := memSobolevMultiIndex_interior_piece_of_order (m + 1) hθ₀ hθ₀κ hθ₀Γ hum hg heq'
    -- the sum `u = θ₀ u + ∑ᵢ θᵢ u`
    have htot := hint.add (MemSobolevMultiIndex.finset_sum Finset.univ
      (f := fun i x ↦ θ i x * fn u x) fun i _ ↦ hbdry i)
    refine htot.congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.add_apply, Finset.sum_apply]
    rw [← Finset.sum_mul, ← add_mul, hsum x, one_mul]

end AssemblyHigher

/-! ### The estimate `‖u‖_{H^{m+2}} ≤ C ‖f‖_{H^m}`, by the closed graph theorem -/

section MainHigher

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

open SobolevMultiIndex

/-- **[brezis2011functional] Theorem 9.25, the `H^{m+2}` clause, membership for the book's
equation**: for `Ω` of class `C^{m+2}` with bounded boundary, the weak solution `u ∈ H^1_0(Ω)`
of `−Δu + u = f` with `f ∈ H^m(Ω)` lies in `H^{m+2}(Ω)`. Induction on the order through
`Elliptic.regularity_dirichlet_higher_mem` with the datum `g = f − u`: `u ∈ H^j` and `f ∈ H^j`
give `g ∈ H^j`, hence `u ∈ H^{j+2}`. -/
theorem regularity_dirichlet_higher_mem_laplace (m : ℕ)
    (hΩ : IsContDiffChartDomain (m + 2) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    (hf : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (⇑f) m 2 Ω
      volume)
    {u : SobolevEuclidean (d + 1) 1 2 Ω}
    (hu : IsGalerkinSolution (laplaceForm Ω) (load Ω f) (SobolevEuclideanZero (d + 1) 1 2 Ω) u) :
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (fn u) (m + 2) 2 Ω
      volume := by
  have heq := dirichletForm_eq_load_sub_of_isGalerkinSolution_laplace hu
  have hg : ∀ j, MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (fn u) j 2
      Ω volume → j ≤ m →
      MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
        (⇑(f - weakDeriv u 0)) j 2 Ω volume := fun j huj hjm ↦ by
    refine ((hf.mono_order hjm).sub huj).congr_ae ?_
    filter_upwards [Lp.coeFn_sub f (weakDeriv u 0)] with x hx
    rw [hx]
    rfl
  have key : ∀ j, j ≤ m → MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (fn u) (j + 2) 2 Ω volume := by
    intro j
    induction j with
    | zero =>
      intro _
      exact regularity_dirichlet_mem (hΩ.of_le (by exact_mod_cast Nat.le_add_left 2 m)) hΓ hu.1 heq
    | succ j ih =>
      intro hjm
      have huj : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (fn u)
          (j + 1) 2 Ω volume :=
        (ih (Nat.le_of_succ_le hjm)).mono_order (Nat.le_succ (j + 1))
      exact regularity_dirichlet_higher_mem (j + 1)
        (hΩ.of_le (by exact_mod_cast Nat.add_le_add_right hjm 2)) hΓ hu.1 (hg (j + 1) huj hjm) heq
  exact key m le_rfl

/-- **[brezis2011functional] Theorem 9.25, the `H^{m+2}` clause.** Let `Ω ⊆ ℝ^N` be open of
class `C^{m+2}` with bounded boundary. There is a constant `C` such that for every
`F ∈ H^m(Ω)`, the weak solution `u ∈ H^1_0(Ω)` of `−Δu + u = F` lies in `H^{m+2}(Ω)`, and every
`U ∈ H^{m+2}(Ω)` with function `u` has `‖U‖_{H^{m+2}(Ω)} ≤ C ‖F‖_{H^m(Ω)}`.

The membership is `Elliptic.regularity_dirichlet_higher_mem_laplace` (induction on `m` through
the interior and boundary pieces), and the constant comes from the closed graph theorem applied
to the solution map `H^m(Ω) → H¹(Ω)`
(`SobolevEuclidean.exists_norm_le_of_forall_exists_sobolev`). -/
theorem regularity_dirichlet_higher (m : ℕ)
    (hΩ : IsContDiffChartDomain (m + 2) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (F : SobolevEuclidean (d + 1) m 2 Ω) (u : SobolevEuclidean (d + 1) 1 2 Ω),
        IsGalerkinSolution (laplaceForm Ω)
          (load Ω (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis m 2 Ω volume F))
          (SobolevEuclideanZero (d + 1) 1 2 Ω) u →
        MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (fn u) (m + 2) 2 Ω
          volume ∧
        ∀ U : SobolevEuclidean (d + 1) (m + 2) 2 Ω,
          fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] fn u →
          ‖U‖ ≤ C * ‖F‖ := by
  have hmem : ∀ (F : SobolevEuclidean (d + 1) m 2 Ω) (u : SobolevEuclidean (d + 1) 1 2 Ω),
      IsGalerkinSolution (laplaceForm Ω)
        (load Ω (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis m 2 Ω volume F))
        (SobolevEuclideanZero (d + 1) 1 2 Ω) u →
      MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (fn u) (m + 2) 2 Ω
        volume := fun F u hu ↦ by
    refine regularity_dirichlet_higher_mem_laplace m hΩ hΓ ?_ hu
    rw [fnL_apply]
    exact memSobolevMultiIndex F
  obtain ⟨S, hS⟩ : ∃ S : SobolevEuclidean (d + 1) m 2 Ω →L[ℝ] SobolevEuclidean (d + 1) 1 2 Ω,
      S = ((SobolevEuclideanZero (d + 1) 1 2 Ω).subtypeL ∘L
        solutionMap Ω (laplaceForm Ω) laplaceForm_restrict_isCoercive) ∘L
        fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis m 2 Ω volume := ⟨_, rfl⟩
  have hSf : ∀ F, IsGalerkinSolution (laplaceForm Ω)
      (load Ω (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis m 2 Ω volume F))
      (SobolevEuclideanZero (d + 1) 1 2 Ω) (S F) := fun F ↦ by
    rw [hS]
    exact isGalerkinSolution_solutionMap Ω (laplaceForm Ω) laplaceForm_restrict_isCoercive _
  obtain ⟨C, hC0, hC⟩ := SobolevEuclidean.exists_norm_le_of_forall_exists_sobolev (S := S)
    fun F ↦
    (hmem F (S F) (hSf F)).exists_sobolevMultiIndex
  refine ⟨C, hC0, fun F u hu ↦ ⟨hmem F u hu, fun U hU ↦ hC F U (hU.trans ?_)⟩⟩
  have : u = S F := by
    rw [hS]
    exact eq_solutionMap_of_isGalerkinSolution Ω (laplaceForm Ω) laplaceForm_restrict_isCoercive hu
  rw [this]

end MainHigher



/-! ### Theorem 9.25, the `C²(Ω̄)` and `C^∞(Ω̄)` clauses -/

section Smooth

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

open SobolevMultiIndex

/-- **A `C^k(Ω̄)` representative of an `H^{m+2}(Ω)` weak solution**, for `k + N/2 < m + 2`: the
function `u` agrees almost everywhere on `Ω` with a `ũ` continuous on `ℝ^N`, of class `C^k` on
`Ω`, each of whose derivatives of order `≤ k` extends continuously to `ℝ^N` from `Ω` — the sense
of `C^k(Ω̄)` of [brezis2011functional] Chapter 9, footnote 16, as in Corollary 9.15
(`SobolevEuclidean.exists_contDiffOn_closure_ae_eq_of_lt`). -/
theorem exists_contDiffOn_of_memSobolevMultiIndex (k : ℕ) {m : ℕ}
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (hm : (k : ℝ) + (d + 1) / 2 < m) {u : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hu : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis u m 2 Ω volume) :
    ∃ ũ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ, Continuous ũ ∧ ContDiffOn ℝ k ũ Ω ∧
      u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] ũ ∧
      ∀ j ≤ k, ∃ G : EuclideanSpace ℝ (Fin (d + 1)) →
        (EuclideanSpace ℝ (Fin (d + 1)) [×j]→L[ℝ] ℝ), Continuous G ∧
        EqOn (iteratedFDeriv ℝ j ũ) G Ω := by
  have hext : IsSobolevExtensionDomainAll (d + 1) Ω :=
    IsSobolevExtensionDomainAll.of_isContDiffChartDomain hΩ hΓ
  have hf2 : Fact (1 ≤ ((2 : NNReal) : ℝ≥0∞)) := ⟨one_le_two⟩
  obtain ⟨C, θ, -, -, -, hC⟩ := SobolevEuclidean.exists_contDiffOn_closure_ae_eq_of_lt
    (N := d + 1) (Ω := Ω) (m := m) (k := k) (p := 2) hext (Or.inr one_lt_two) (by
      push_cast
      exact hm)
  obtain ⟨U, hU⟩ : ∃ U : SobolevEuclidean (d + 1) m ((2 : NNReal) : ℝ≥0∞) Ω,
      fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] u :=
    hu.exists_sobolevMultiIndex
  obtain ⟨ũ, hc, hk, hae, hG, -⟩ := hC U
  refine ⟨ũ, hc, hk, hU.symm.trans hae, fun j hj ↦ ?_⟩
  obtain ⟨G, hGc, hGeq, -⟩ := hG j hj
  exact ⟨G, hGc, hGeq⟩

/-- **A function in `H^m(Ω)` for every `m` is `C^∞(Ω̄)`** on a `C¹` domain with bounded
boundary: it agrees almost everywhere on `Ω` with a function `ũ` continuous on `ℝ^N`, of class
`C^∞` on `Ω`, all of whose derivatives extend continuously from `Ω` to `ℝ^N` — the book's
`C^∞(Ω̄)` ([brezis2011functional] Chapter 9, footnote 16). Corollary 9.15 at every order
(`exists_contDiffOn_of_memSobolevMultiIndex`) gives a `C^k(Ω̄)` representative for each `k`; two
continuous representatives agree on the open set `Ω` (`Measure.eqOn_open_of_ae_eq`), so the
representative at order `0` is of class `C^k` on `Ω` for every `k`, with the derivative
extensions of the representative at order `k`. -/
theorem exists_contDiffOn_infty_of_forall_memSobolevMultiIndex
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    {u : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hu : ∀ m : ℕ, MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis u m 2 Ω
      volume) :
    ∃ ũ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ, Continuous ũ ∧ ContDiffOn ℝ ∞ ũ Ω ∧
      u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] ũ ∧
      ∀ j : ℕ, ∃ G : EuclideanSpace ℝ (Fin (d + 1)) →
        (EuclideanSpace ℝ (Fin (d + 1)) [×j]→L[ℝ] ℝ), Continuous G ∧
        EqOn (iteratedFDeriv ℝ j ũ) G Ω := by
  -- a `C^k(Ω̄)` representative for every `k`
  have hrep : ∀ k : ℕ, ∃ ũ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ, Continuous ũ ∧
      ContDiffOn ℝ k ũ Ω ∧ u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] ũ ∧
      ∀ j ≤ k, ∃ G : EuclideanSpace ℝ (Fin (d + 1)) →
        (EuclideanSpace ℝ (Fin (d + 1)) [×j]→L[ℝ] ℝ), Continuous G ∧
        EqOn (iteratedFDeriv ℝ j ũ) G Ω := fun k ↦ by
    refine exists_contDiffOn_of_memSobolevMultiIndex k hΩ hΓ (m := k + (d + 1)) ?_ (hu _)
    push_cast
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  choose v hvc hvk hvae hvG using hrep
  -- the representatives agree on `Ω`
  have hagree : ∀ k, EqOn (v 0) (v k) Ω := fun k ↦
    Measure.eqOn_open_of_ae_eq ((hvae 0).symm.trans (hvae k)) Ω.isOpen
      (hvc 0).continuousOn (hvc k).continuousOn
  refine ⟨v 0, hvc 0, ?_, hvae 0, fun j ↦ ?_⟩
  · rw [contDiffOn_infty]
    intro k
    exact (hvk k).congr fun x hx ↦ hagree k hx
  · obtain ⟨G, hGc, hGeq⟩ := hvG j j le_rfl
    refine ⟨G, hGc, fun x hx ↦ ?_⟩
    rw [← hGeq hx]
    have h : v 0 =ᶠ[𝓝 x] v j :=
      Filter.eventually_of_mem (Ω.isOpen.mem_nhds hx) fun y hy ↦ hagree j hy
    exact (h.iteratedFDeriv ℝ j).eq_of_nhds

/-- **A function in `H^m(Ω)` for every `m` is `C^∞(Ω̄)`**, in the `ContDiffOnClosure` reading of
the class `C^∞(Ω̄)`: on a `C¹` domain with bounded boundary it agrees almost everywhere on `Ω`
with a function of class `C^∞(Ω̄)` (`ContDiffOnClosure ℝ ∞ ũ Ω`), continuous on `Ω̄`
(`exists_contDiffOn_infty_of_forall_memSobolevMultiIndex`, the extensions restricted to the
closure). -/
theorem exists_contDiffOnClosure_infty_of_forall_memSobolevMultiIndex
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    {u : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hu : ∀ m : ℕ, MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis u m 2 Ω
      volume) :
    ∃ ũ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ, ContDiffOnClosure ℝ ∞ ũ Ω ∧
      ContinuousOn ũ (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) ∧
      u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] ũ := by
  obtain ⟨ũ, hc, hk, hae, hG⟩ := exists_contDiffOn_infty_of_forall_memSobolevMultiIndex hΩ hΓ hu
  refine ⟨ũ, ⟨hk, fun j _ ↦ ?_⟩, hc.continuousOn, hae⟩
  obtain ⟨G, hGc, hGeq⟩ := hG j
  exact ⟨G, hGc.continuousOn, fun x hx ↦ (hGeq hx).symm⟩

/-- **[brezis2011functional] Theorem 9.25, the `C²(Ω̄)` clause**: for `Ω` of class `C^{m+2}`
with bounded boundary, `f ∈ H^m(Ω)` and `m > N/2`, the weak solution `u ∈ H^1_0(Ω)` of
`−Δu + u = f` agrees almost everywhere with a function `ũ` continuous on `ℝ^N` and of class
`C²` on `Ω` whose derivatives up to order `2` extend continuously from `Ω` to `ℝ^N` — the
book's `C²(Ω̄)` in the sense of Chapter 9, footnote 16. From `u ∈ H^{m+2}(Ω)`
(`Elliptic.regularity_dirichlet_higher_mem_laplace`) and Corollary 9.15 on the `C¹` domain `Ω`
(`SobolevEuclidean.exists_contDiffOn_closure_ae_eq_of_lt`, `2 + N/2 < m + 2`). -/
theorem regularity_dirichlet_contDiffOn (m : ℕ)
    (hΩ : IsContDiffChartDomain (m + 2) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (hm : ((d + 1 : ℕ) : ℝ) / 2 < m)
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    (hf : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (⇑f) m 2 Ω
      volume)
    {u : SobolevEuclidean (d + 1) 1 2 Ω}
    (hu : IsGalerkinSolution (laplaceForm Ω) (load Ω f) (SobolevEuclideanZero (d + 1) 1 2 Ω) u) :
    ∃ ũ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ, Continuous ũ ∧ ContDiffOn ℝ 2 ũ Ω ∧
      fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] ũ ∧
      ∀ j ≤ 2, ∃ G : EuclideanSpace ℝ (Fin (d + 1)) →
        (EuclideanSpace ℝ (Fin (d + 1)) [×j]→L[ℝ] ℝ), Continuous G ∧
        EqOn (iteratedFDeriv ℝ j ũ) G Ω := by
  have hmem := regularity_dirichlet_higher_mem_laplace m hΩ hΓ hf hu
  have hΩ1 : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) :=
    hΩ.of_le (by exact_mod_cast Nat.le_add_left 1 (m + 1))
  refine exists_contDiffOn_of_memSobolevMultiIndex 2 hΩ1 hΓ ?_ hmem
  push_cast at hm ⊢
  linarith

/-- **[brezis2011functional] Theorem 9.25, the `C^∞(Ω̄)` clause**: for `Ω` of class `C^∞` with
bounded boundary and `f ∈ H^m(Ω)` for every `m` (which holds for every `f ∈ C^∞(Ω̄)` with
bounded derivatives on a bounded `Ω`), the weak solution `u ∈ H^1_0(Ω)` of `−Δu + u = f` agrees
almost everywhere with a function `ũ` continuous on `ℝ^N`, of class `C^∞` on `Ω`, all of whose
derivatives extend continuously from `Ω` to `ℝ^N` — the book's `C^∞(Ω̄)`. The solution lies in
`H^{m+2}(Ω)` for every `m` (`regularity_dirichlet_higher_mem_laplace`), and a function in every
`H^m(Ω)` is `C^∞(Ω̄)` (`exists_contDiffOn_infty_of_forall_memSobolevMultiIndex`). -/
theorem regularity_dirichlet_smooth
    (hΩ : IsContDiffChartDomain ∞ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    (hf : ∀ m : ℕ, MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (⇑f) m 2
      Ω volume)
    {u : SobolevEuclidean (d + 1) 1 2 Ω}
    (hu : IsGalerkinSolution (laplaceForm Ω) (load Ω f) (SobolevEuclideanZero (d + 1) 1 2 Ω) u) :
    ∃ ũ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ, Continuous ũ ∧ ContDiffOn ℝ ∞ ũ Ω ∧
      fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] ũ ∧
      ∀ j : ℕ, ∃ G : EuclideanSpace ℝ (Fin (d + 1)) →
        (EuclideanSpace ℝ (Fin (d + 1)) [×j]→L[ℝ] ℝ), Continuous G ∧
        EqOn (iteratedFDeriv ℝ j ũ) G Ω :=
  exists_contDiffOn_infty_of_forall_memSobolevMultiIndex (hΩ.of_le (by simp)) hΓ fun m ↦
    (regularity_dirichlet_higher_mem_laplace m (hΩ.of_le (by simp)) hΓ (hf m) hu).mono_order
      (Nat.le_add_right m 2)

end Smooth

end Elliptic

import Numlib.Analysis.InnerProductSpace.MaximalMonotone

/-!
# Brezis §7.1: definition and elementary properties of maximal monotone operators

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §7.1, over a real Hilbert space `H`. An unbounded
operator `A : D(A) ⊂ H → H` is Mathlib's `LinearPMap`, `A : H →ₗ.[ℝ] H`, with `A.domain` the
book's `D(A)`. Everything delegates to the backbone module
`Numlib/Analysis/InnerProductSpace/MaximalMonotone` (`LinearPMap.IsMonotone`,
`LinearPMap.IsMaximalMonotone`, `LinearPMap.resolvent`, `LinearPMap.yosida`, stated there over
`RCLike 𝕜` with the real part `re ⟪A v, v⟫`, which is the identity over `ℝ`).

## Main definitions

* `IsMonotone`, `IsMaximalMonotone` — the book's definitions in the book's words, `(A v, v) ≥ 0`
  and `R(I + A) = H`, with `isMonotone_iff` and `isMaximalMonotone_iff` to the backbone
  predicates and `isMaximalMonotone_iff_range` for the range spelling `R(I + A) = H`.
* `resolvent hA hl` — the resolvent `J_λ = (I + λA)⁻¹ : H → H`, defined as the book does: the
  inverse of the bijection `I + λA : D(A) → H` of Proposition 7.1 (c). `resolvent_eq` identifies
  it with the backbone's bounded operator `A.resolvent λ`.
* `yosidaApprox hA hl` — the Yosida approximation `A_λ = λ⁻¹ (I − J_λ)`, with `yosidaApprox_eq`
  to `A.yosida λ`.

## Main results

* `proposition_7_1_a`, `proposition_7_1_b`, `proposition_7_1_c`, `proposition_7_1` —
  Proposition 7.1: `D(A)` is dense, `A` is closed, and for every `λ > 0` the operator `I + λA`
  is a bijection of `D(A)` onto `H` whose inverse is a bounded operator of norm at most `1`.
* `remark_7_1` — Remark 1, first sentence: `λA` is maximal monotone for `λ > 0`.
* `norm_resolvent_le` — "keep in mind that `‖J_λ‖ ≤ 1`".
* `proposition_7_2_a1`, `proposition_7_2_a2`, `proposition_7_2_b`, …, `proposition_7_2_f`,
  `proposition_7_2` — the six properties of the Yosida approximation, Proposition 7.2, and the
  inequality (3) of its proof (in `proposition_7_2_e`).

Remark 2 is discussion; Remark 1's second sentence (`A + B` on `D(A) ∩ D(B)` need not be maximal
monotone) is a counterexample claim and is not formalized. The limits of Proposition 7.2 (c), (d)
as `λ → 0` range over `λ > 0`, so they are stated through the backbone's total `A.resolvent` and
`A.yosida` (which agree with `resolvent hA hl` and `yosidaApprox hA hl` at every `λ > 0`).
-/

open Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace Brezis.Chapter07

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ### The definitions -/

/-- **Definition (§7.1), monotone.** An unbounded operator `A : D(A) ⊂ H → H` is *monotone* if
`(A v, v) ≥ 0` for all `v ∈ D(A)`. Some authors say that `A` is accretive or that `−A` is
dissipative (footnote 1). -/
def IsMonotone (A : H →ₗ.[ℝ] H) : Prop :=
  ∀ v : A.domain, 0 ≤ ⟪A v, (v : H)⟫_ℝ

/-- The book's monotonicity is the backbone's `LinearPMap.IsMonotone` (which reads
`0 ≤ re ⟪A v, v⟫`, `re` being the identity over `ℝ`). -/
theorem isMonotone_iff (A : H →ₗ.[ℝ] H) : IsMonotone A ↔ A.IsMonotone := by
  simp only [IsMonotone, LinearPMap.IsMonotone, RCLike.re_to_real]

/-- **Definition (§7.1), maximal monotone.** `A` is *maximal monotone* if it is monotone and, in
addition, `R(I + A) = H`, i.e. for every `f ∈ H` there is `u ∈ D(A)` with `u + A u = f`. -/
def IsMaximalMonotone (A : H →ₗ.[ℝ] H) : Prop :=
  IsMonotone A ∧ ∀ f : H, ∃ u : A.domain, (u : H) + A u = f

/-- The book's maximal monotonicity is the backbone's `LinearPMap.IsMaximalMonotone`. -/
theorem isMaximalMonotone_iff (A : H →ₗ.[ℝ] H) : IsMaximalMonotone A ↔ A.IsMaximalMonotone :=
  ⟨fun h => ⟨(isMonotone_iff A).1 h.1, h.2⟩,
    fun h => ⟨(isMonotone_iff A).2 h.isMonotone, h.exists_add_apply_eq⟩⟩

/-- A maximal monotone operator in the book's sense is one in the backbone's sense. -/
theorem IsMaximalMonotone.isMaximalMonotone {A : H →ₗ.[ℝ] H} (hA : IsMaximalMonotone A) :
    A.IsMaximalMonotone :=
  (isMaximalMonotone_iff A).1 hA

/-- The range spelling of the definition: `A` is maximal monotone iff it is monotone and the
operator `I + A` (Mathlib's `LinearMap.id +ᵥ A`, defined on `D(A)`) has range `H`. -/
theorem isMaximalMonotone_iff_range (A : H →ₗ.[ℝ] H) :
    IsMaximalMonotone A ↔
      IsMonotone A ∧ LinearMap.range ((LinearMap.id : H →ₗ[ℝ] H) +ᵥ A).toFun = ⊤ := by
  rw [isMaximalMonotone_iff]
  refine ⟨fun h => ⟨(isMonotone_iff A).2 h.isMonotone, h.range_id_vadd_eq_top⟩, fun h => ?_⟩
  exact LinearPMap.IsMaximalMonotone.of_range_id_vadd_eq_top ((isMonotone_iff A).1 h.1) h.2

/-! ### Proposition 7.1 -/

variable [CompleteSpace H] {A : H →ₗ.[ℝ] H}

/-- **Proposition 7.1 (a).** If `A` is maximal monotone then `D(A)` is dense in `H`. -/
theorem proposition_7_1_a (hA : IsMaximalMonotone A) : Dense (A.domain : Set H) :=
  hA.isMaximalMonotone.dense_domain

/-- **Proposition 7.1 (b).** A maximal monotone operator is closed (its graph is closed in
`H × H`; the book's sequential reading is `Brezis.Chapter02.remark_2_11`). -/
theorem proposition_7_1_b (hA : IsMaximalMonotone A) : A.IsClosed :=
  hA.isMaximalMonotone.isClosed

/-- **Proposition 7.1 (c).** For every `λ > 0`, `I + λA` is bijective from `D(A)` onto `H`,
its inverse `(I + λA)⁻¹` is a bounded operator — a `J : H →L[ℝ] H` with `J f ∈ D(A)` and
`J f + λ A (J f) = f` for every `f` — and `‖(I + λA)⁻¹‖ ≤ 1`. The witness is the backbone's
`A.resolvent λ`. -/
theorem proposition_7_1_c (hA : IsMaximalMonotone A) {l : ℝ} (hl : 0 < l) :
    Function.Bijective (fun u : A.domain => (u : H) + l • A u) ∧
      ∃ J : H →L[ℝ] H, (∀ f : H, ∃ hf : J f ∈ A.domain, J f + l • A ⟨J f, hf⟩ = f) ∧ ‖J‖ ≤ 1 :=
  ⟨⟨hA.isMaximalMonotone.isMonotone.injective_add_smul hl.le, fun f => by
      obtain ⟨u, hu⟩ := hA.isMaximalMonotone.exists_add_smul_eq hl f
      exact ⟨u, hu⟩⟩,
    A.resolvent l, hA.isMaximalMonotone.resolvent_spec hl,
    hA.isMaximalMonotone.norm_resolvent_le_one hl⟩

/-- **Proposition 7.1.** For a maximal monotone `A`: (a) `D(A)` is dense in `H`; (b) `A` is
closed; (c) for every `λ > 0`, `I + λA` is a bijection of `D(A)` onto `H` whose inverse is a
bounded operator of norm at most `1`. -/
theorem proposition_7_1 (hA : IsMaximalMonotone A) :
    Dense (A.domain : Set H) ∧ A.IsClosed ∧ ∀ l : ℝ, 0 < l →
      Function.Bijective (fun u : A.domain => (u : H) + l • A u) ∧
        ∃ J : H →L[ℝ] H, (∀ f : H, ∃ hf : J f ∈ A.domain, J f + l • A ⟨J f, hf⟩ = f) ∧
          ‖J‖ ≤ 1 :=
  ⟨proposition_7_1_a hA, proposition_7_1_b hA, fun _ hl => proposition_7_1_c hA hl⟩

/-- **Remark 1, first sentence.** If `A` is maximal monotone then so is `λA` for every `λ > 0`.
(The second sentence — `A + B` on `D(A) ∩ D(B)` need not be maximal monotone — is a
counterexample claim and is not formalized.) -/
theorem remark_7_1 (hA : IsMaximalMonotone A) {l : ℝ} (hl : 0 < l) :
    IsMaximalMonotone (l • A) :=
  (isMaximalMonotone_iff _).2 (hA.isMaximalMonotone.smul hl)

/-! ### The resolvent and the Yosida approximation -/

/-- **Definition (§7.1), the resolvent.** For a maximal monotone `A` and `λ > 0`, the
*resolvent* `J_λ = (I + λA)⁻¹ : H → H` is the inverse of the bijection `I + λA : D(A) → H` of
Proposition 7.1 (c), followed by the inclusion `D(A) ⊆ H`. -/
def resolvent (hA : IsMaximalMonotone A) {l : ℝ} (hl : 0 < l) : H → H :=
  fun f => ((Equiv.ofBijective _ (proposition_7_1_c hA hl).1).symm f : H)

/-- `J_λ f ∈ D(A)`. -/
theorem resolvent_mem_domain (hA : IsMaximalMonotone A) {l : ℝ} (hl : 0 < l) (f : H) :
    resolvent hA hl f ∈ A.domain :=
  ((Equiv.ofBijective _ (proposition_7_1_c hA hl).1).symm f).2

/-- The defining property of the resolvent: `J_λ f + λ A (J_λ f) = f`. -/
theorem resolvent_add_smul_apply (hA : IsMaximalMonotone A) {l : ℝ} (hl : 0 < l) (f : H) :
    resolvent hA hl f + l • A ⟨resolvent hA hl f, resolvent_mem_domain hA hl f⟩ = f :=
  Equiv.ofBijective_apply_symm_apply _ (proposition_7_1_c hA hl).1 f

/-- The book's resolvent is the backbone's bounded operator `A.resolvent λ`. -/
theorem resolvent_eq (hA : IsMaximalMonotone A) {l : ℝ} (hl : 0 < l) (f : H) :
    resolvent hA hl f = A.resolvent l f :=
  ((hA.isMaximalMonotone.resolvent_eq_iff hl ⟨resolvent hA hl f, resolvent_mem_domain hA hl f⟩
    f).2 (resolvent_add_smul_apply hA hl f)).symm

/-- **"Keep in mind that `‖J_λ‖ ≤ 1`."** -/
theorem norm_resolvent_le (hA : IsMaximalMonotone A) {l : ℝ} (hl : 0 < l) (f : H) :
    ‖resolvent hA hl f‖ ≤ ‖f‖ := by
  rw [resolvent_eq]
  exact hA.isMaximalMonotone.norm_resolvent_apply_le hl f

/-- **Definition (§7.1), the Yosida approximation** (or regularization) of `A`:
`A_λ = λ⁻¹ (I − J_λ)`. -/
def yosidaApprox (hA : IsMaximalMonotone A) {l : ℝ} (hl : 0 < l) : H → H :=
  fun v => l⁻¹ • (v - resolvent hA hl v)

/-- The book's Yosida approximation is the backbone's bounded operator `A.yosida λ`. -/
theorem yosidaApprox_eq (hA : IsMaximalMonotone A) {l : ℝ} (hl : 0 < l) (v : H) :
    yosidaApprox hA hl v = A.yosida l v := by
  rw [yosidaApprox, LinearPMap.yosida_apply, resolvent_eq]
  rfl

/-! ### Proposition 7.2 -/

/-- **Proposition 7.2 (a₁).** `A_λ v = A (J_λ v)` for all `v ∈ H` and `λ > 0`. -/
theorem proposition_7_2_a1 (hA : IsMaximalMonotone A) {l : ℝ} (hl : 0 < l) (v : H) :
    yosidaApprox hA hl v = A ⟨resolvent hA hl v, resolvent_mem_domain hA hl v⟩ := by
  rw [yosidaApprox_eq, hA.isMaximalMonotone.yosida_apply_eq_apply_resolvent hl]
  congr 1
  exact Subtype.ext (resolvent_eq hA hl v).symm

/-- **Proposition 7.2 (a₂).** `A_λ v = J_λ (A v)` for all `v ∈ D(A)` and `λ > 0`. -/
theorem proposition_7_2_a2 (hA : IsMaximalMonotone A) {l : ℝ} (hl : 0 < l) (v : A.domain) :
    yosidaApprox hA hl v = resolvent hA hl (A v) := by
  rw [yosidaApprox_eq, resolvent_eq]
  exact hA.isMaximalMonotone.yosida_apply_eq_resolvent_apply hl v

/-- **Proposition 7.2 (b).** `|A_λ v| ≤ |A v|` for all `v ∈ D(A)` and `λ > 0`. -/
theorem proposition_7_2_b (hA : IsMaximalMonotone A) {l : ℝ} (hl : 0 < l) (v : A.domain) :
    ‖yosidaApprox hA hl v‖ ≤ ‖A v‖ := by
  rw [yosidaApprox_eq]
  exact hA.isMaximalMonotone.norm_yosida_apply_le_norm_apply hl v

/-- **Proposition 7.2 (c).** `lim_{λ → 0} J_λ v = v` for all `v ∈ H` (the limit along
`λ → 0⁺`, stated through the backbone's `A.resolvent`, which is `J_λ` for every `λ > 0` by
`resolvent_eq`). -/
theorem proposition_7_2_c (hA : IsMaximalMonotone A) (v : H) :
    Tendsto (fun l : ℝ => A.resolvent l v) (𝓝[>] 0) (𝓝 v) :=
  hA.isMaximalMonotone.tendsto_resolvent_apply v

/-- **Proposition 7.2 (d).** `lim_{λ → 0} A_λ v = A v` for all `v ∈ D(A)` (the limit along
`λ → 0⁺`, stated through the backbone's `A.yosida`, which is `A_λ` for every `λ > 0` by
`yosidaApprox_eq`). -/
theorem proposition_7_2_d (hA : IsMaximalMonotone A) (v : A.domain) :
    Tendsto (fun l : ℝ => A.yosida l v) (𝓝[>] 0) (𝓝 (A v)) :=
  hA.isMaximalMonotone.tendsto_yosida_apply v

/-- **Proposition 7.2 (e).** `(A_λ v, v) ≥ 0` for all `v ∈ H` and `λ > 0`, and the sharper
inequality (3) of the proof, `(A_λ v, v) ≥ λ |A_λ v|²`. -/
theorem proposition_7_2_e (hA : IsMaximalMonotone A) {l : ℝ} (hl : 0 < l) (v : H) :
    0 ≤ ⟪yosidaApprox hA hl v, v⟫_ℝ ∧
      l * ‖yosidaApprox hA hl v‖ ^ 2 ≤ ⟪yosidaApprox hA hl v, v⟫_ℝ := by
  rw [yosidaApprox_eq]
  exact ⟨by simpa using hA.isMaximalMonotone.re_inner_yosida_nonneg hl v,
    by simpa using hA.isMaximalMonotone.smul_norm_sq_yosida_le_re_inner hl v⟩

/-- **Proposition 7.2 (f).** `|A_λ v| ≤ (1/λ) |v|` for all `v ∈ H` and `λ > 0`. -/
theorem proposition_7_2_f (hA : IsMaximalMonotone A) {l : ℝ} (hl : 0 < l) (v : H) :
    ‖yosidaApprox hA hl v‖ ≤ (1 / l) * ‖v‖ := by
  rw [yosidaApprox_eq, one_div]
  exact hA.isMaximalMonotone.norm_yosida_apply_le hl v

/-- **Proposition 7.2.** For a maximal monotone `A`: (a₁) `A_λ v = A (J_λ v)` on `H`;
(a₂) `A_λ v = J_λ (A v)` on `D(A)`; (b) `|A_λ v| ≤ |A v|` on `D(A)`; (c) `J_λ v → v` as
`λ → 0` on `H`; (d) `A_λ v → A v` as `λ → 0` on `D(A)`; (e) `(A_λ v, v) ≥ 0` on `H`;
(f) `|A_λ v| ≤ (1/λ) |v|` on `H`; all for every `λ > 0`. -/
theorem proposition_7_2 (hA : IsMaximalMonotone A) :
    (∀ (l : ℝ) (hl : 0 < l) (v : H),
        yosidaApprox hA hl v = A ⟨resolvent hA hl v, resolvent_mem_domain hA hl v⟩) ∧
      (∀ (l : ℝ) (hl : 0 < l) (v : A.domain), yosidaApprox hA hl v = resolvent hA hl (A v)) ∧
      (∀ (l : ℝ) (hl : 0 < l) (v : A.domain), ‖yosidaApprox hA hl v‖ ≤ ‖A v‖) ∧
      (∀ v : H, Tendsto (fun l : ℝ => A.resolvent l v) (𝓝[>] 0) (𝓝 v)) ∧
      (∀ v : A.domain, Tendsto (fun l : ℝ => A.yosida l v) (𝓝[>] 0) (𝓝 (A v))) ∧
      (∀ (l : ℝ) (hl : 0 < l) (v : H), 0 ≤ ⟪yosidaApprox hA hl v, v⟫_ℝ) ∧
      ∀ (l : ℝ) (hl : 0 < l) (v : H), ‖yosidaApprox hA hl v‖ ≤ (1 / l) * ‖v‖ :=
  ⟨fun _ hl v => proposition_7_2_a1 hA hl v, fun _ hl v => proposition_7_2_a2 hA hl v,
    fun _ hl v => proposition_7_2_b hA hl v, proposition_7_2_c hA, proposition_7_2_d hA,
    fun _ hl v => (proposition_7_2_e hA hl v).1, fun _ hl v => proposition_7_2_f hA hl v⟩

end Brezis.Chapter07

end

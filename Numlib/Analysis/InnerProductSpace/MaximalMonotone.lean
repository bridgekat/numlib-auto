/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.LinearPMap`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Topology.MetricSpace.Contracting
import Numlib.Analysis.Normed.Operator.Unbounded.Basic

/-!
# Maximal monotone operators on a Hilbert space

Maximal monotone operators, their resolvents and Yosida approximations, the domains `D(A^k)` as
Hilbert spaces, and the self-adjointness of symmetric maximal monotone operators
([brezis2011functional] §7.1, §7.3, §7.4).

## Setting

`H` is a Hilbert space over `RCLike 𝕜` and `A : H →ₗ.[𝕜] H` is Mathlib's partially defined linear
map. Nothing here differentiates in time, so the whole module is over `RCLike 𝕜` with the real
part `re ⟪A v, v⟫`: the proofs are verbatim the real ones, Mathlib's `LinearPMap.adjoint` and
`IsSelfAdjoint` are over `RCLike`, and the skew-adjoint case (`re ⟪A v, v⟫ = 0`) comes for free.
The evolution equation `u' + A u = 0` is in `Numlib/Analysis/ODE/HilleYosida`, over `ℝ`.

## Main definitions

* `LinearPMap.IsMonotone A` — `0 ≤ re ⟪A v, v⟫` for all `v ∈ D(A)`.
* `LinearPMap.IsMaximalMonotone A` — monotone with `R(I + A) = H`, as a structure with fields
  `isMonotone` and `exists_add_apply_eq : ∀ f, ∃ u : A.domain, (u : H) + A u = f`. The book's
  operator `I + λ A` is `LinearMap.id +ᵥ ((λ : 𝕜) • A)`, whose domain is `A.domain` by `rfl`;
  `IsMaximalMonotone.range_id_vadd_eq_top` records the book's spelling.
* `LinearPMap.resolvent A c : H →L[𝕜] H` — the resolvent `J_c = (I + c A)⁻¹`, and
  `LinearPMap.yosida A c : H →L[𝕜] H` — the Yosida approximation `A_c = c⁻¹ (I - J_c)`. Both are
  total functions of `(A, c)` by the junk-value pattern of `LinearPMap.adjoint` (the bounded `J`
  with `J f ∈ D(A)` and `J f + c A (J f) = f` for all `f` if one exists, else `0`); their
  properties are stated under `hA : A.IsMaximalMonotone` and `0 < c`.
* `LinearPMap.powGraph A k` and `LinearPMap.PowDomain A k := ↥(A.powGraph k)` — the book's
  `D(A^k)` **as a Hilbert space with exactly the book's norm** `(∑_{j ≤ k} ‖A^j u‖²)^{1/2}`: the
  tuples `(u, A u, …, A^k u)` cut out of the `ℓ²`-product `PiLp 2 (Fin (k + 1) → H)` by
  "consecutive entries are related by `A`". The norm and inner product come from Mathlib's
  `PiLp` and `Submodule` instances, completeness is closedness of the submodule for a closed `A`
  (`IsClosed.completeSpace_powDomain`), and `A^j` on `D(A^k)` is the coordinate projection
  `PowDomain.applyL A k j`, a contraction. `A.PowDomain 1` is `D(A)` with the Hilbert graph norm.
  No operator `A ^ k : H →ₗ.[𝕜] H` is defined (Mathlib's `LinearPMap.comp` demands the whole
  range to land in the domain); only the domains with their norms are needed.
* `LinearPMap.powPart A k : A.PowDomain k →ₗ.[𝕜] A.PowDomain k` — the part of `A` in `D(A^k)`,
  the operator `D(A^{k+1}) ⊆ D(A^k) → D(A^k)`, `u ↦ A u`; it is again maximal monotone
  (`IsMaximalMonotone.powPart`) and symmetric when `A` is (`IsFormalAdjoint.powPart`), which
  is what makes the regularity theorems of the evolution equation inductions over one theorem.

Symmetric operators are Mathlib's `A.IsFormalAdjoint A`; self-adjoint ones are Mathlib's
`IsSelfAdjoint A` (`A† = A`).

## Main statements

* `IsMaximalMonotone.dense_domain`, `IsMaximalMonotone.isClosed`,
  `IsMaximalMonotone.exists_add_smul_eq`, `IsMaximalMonotone.norm_resolvent_le_one` — the three
  clauses of [brezis2011functional] Proposition 7.1: dense domain, closed graph, and
  `I + c A : D(A) → H` bijective with `‖(I + c A)⁻¹‖ ≤ 1` for every `c > 0`.
* `IsMaximalMonotone.yosida_apply_eq_apply_resolvent`, `yosida_apply_eq_resolvent_apply`,
  `norm_yosida_apply_le_norm_apply`, `tendsto_resolvent_apply`, `tendsto_yosida_apply`,
  `re_inner_yosida_nonneg`, `norm_yosida_apply_le` — the six properties of the Yosida
  approximation, [brezis2011functional] Proposition 7.2.
* `IsMaximalMonotone.dense_range_castL` — `D(A^{k+1})` is dense in `D(A^k)` for the norm of
  `D(A^k)` ([brezis2011functional] Lemma 7.2 at `k = 1`).
* `IsMaximalMonotone.isSelfAdjoint_of_isFormalAdjoint` — a symmetric maximal monotone operator
  is self-adjoint ([brezis2011functional] Proposition 7.6).

## References

[brezis2011functional], Chapter 7, §7.1, §7.3, §7.4.
-/

open RCLike Filter Topology Metric WithLp
open scoped InnerProductSpace

noncomputable section

namespace LinearPMap

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-! ### Monotone and maximal monotone operators -/

/-- An operator `A : D(A) ⊆ H → H` is **monotone** when `0 ≤ re ⟪A v, v⟫` for every `v ∈ D(A)`
([brezis2011functional] §7.1; "accretive" in other authors' words). Over `𝕜 = ℝ` the real part
is the identity. -/
def IsMonotone (A : H →ₗ.[𝕜] H) : Prop :=
  ∀ v : A.domain, 0 ≤ re ⟪A v, (v : H)⟫

/-- An operator `A : D(A) ⊆ H → H` is **maximal monotone** when it is monotone and `I + A` maps
`D(A)` onto `H`: for every `f` there is `u ∈ D(A)` with `u + A u = f` ([brezis2011functional]
§7.1). -/
structure IsMaximalMonotone (A : H →ₗ.[𝕜] H) : Prop where
  /-- A maximal monotone operator is monotone. -/
  isMonotone : A.IsMonotone
  /-- `R(I + A) = H`: every `f : H` is `u + A u` for some `u ∈ D(A)`. -/
  exists_add_apply_eq : ∀ f : H, ∃ u : A.domain, (u : H) + A u = f

variable {A : H →ₗ.[𝕜] H}

/-- The book's spelling of the range condition: for a maximal monotone `A`, the operator
`I + A` (Mathlib's `LinearMap.id +ᵥ A`, defined on `D(A)`) has range `H`. -/
theorem IsMaximalMonotone.range_id_vadd_eq_top (hA : A.IsMaximalMonotone) :
    LinearMap.range ((LinearMap.id : H →ₗ[𝕜] H) +ᵥ A).toFun = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro f
  obtain ⟨u, hu⟩ := hA.exists_add_apply_eq f
  exact ⟨u, hu⟩

/-- A monotone operator with `R(I + A) = H` (in the book's spelling) is maximal monotone. -/
theorem IsMaximalMonotone.of_range_id_vadd_eq_top (hA : A.IsMonotone)
    (h : LinearMap.range ((LinearMap.id : H →ₗ[𝕜] H) +ᵥ A).toFun = ⊤) : A.IsMaximalMonotone :=
  ⟨hA, fun f => by
    obtain ⟨u, hu⟩ := LinearMap.range_eq_top.1 h f
    exact ⟨u, hu⟩⟩

/-- `re ⟪u + c A u, u⟫ = ‖u‖² + c re ⟪A u, u⟫` for a real `c`. -/
theorem re_inner_add_smul_apply_self (A : H →ₗ.[𝕜] H) (c : ℝ) (u : A.domain) :
    re ⟪(u : H) + (c : 𝕜) • A u, (u : H)⟫ = ‖(u : H)‖ ^ 2 + c * re ⟪A u, (u : H)⟫ := by
  rw [inner_add_left, _root_.map_add, inner_self_eq_norm_sq, inner_smul_left, conj_ofReal,
    re_ofReal_mul]

/-- **The basic estimate for a monotone operator**: `‖u‖ ≤ ‖u + c A u‖` on `D(A)` for every
`c ≥ 0`, since `‖u‖² ≤ ‖u‖² + c re ⟪A u, u⟫ = re ⟪u + c A u, u⟫ ≤ ‖u + c A u‖ ‖u‖`
([brezis2011functional], proof of Proposition 7.1 (b)). -/
theorem IsMonotone.norm_le_norm_add_smul (hA : A.IsMonotone) {c : ℝ} (hc : 0 ≤ c)
    (u : A.domain) : ‖(u : H)‖ ≤ ‖(u : H) + (c : 𝕜) • A u‖ := by
  have h1 : ‖(u : H)‖ ^ 2 ≤ re ⟪(u : H) + (c : 𝕜) • A u, (u : H)⟫ := by
    rw [re_inner_add_smul_apply_self]
    exact le_add_of_nonneg_right (mul_nonneg hc (hA u))
  have h2 := re_inner_le_norm (𝕜 := 𝕜) ((u : H) + (c : 𝕜) • A u) (u : H)
  rcases (norm_nonneg (u : H)).eq_or_lt with h0 | h0
  · rw [← h0]
    exact norm_nonneg _
  · have : ‖(u : H)‖ * ‖(u : H)‖ ≤ ‖(u : H) + (c : 𝕜) • A u‖ * ‖(u : H)‖ := by
      rw [← sq]
      exact h1.trans h2
    exact le_of_mul_le_mul_right this h0

/-- For a monotone `A` and `c ≥ 0`, `u ↦ u + c A u` is injective on `D(A)`: the uniqueness
clause of [brezis2011functional] Proposition 7.1 (b), (c). -/
theorem IsMonotone.injective_add_smul (hA : A.IsMonotone) {c : ℝ} (hc : 0 ≤ c) :
    Function.Injective fun u : A.domain => (u : H) + (c : 𝕜) • A u := by
  intro u v huv
  have h := hA.norm_le_norm_add_smul hc (u - v)
  simp only at huv
  rw [map_sub, Submodule.coe_sub, smul_sub,
    show (u : H) - v + ((c : 𝕜) • A u - (c : 𝕜) • A v) =
      ((u : H) + (c : 𝕜) • A u) - ((v : H) + (c : 𝕜) • A v) by abel,
    huv, sub_self, norm_zero] at h
  exact Subtype.ext (sub_eq_zero.1 (norm_le_zero_iff.1 h))

/-- **Proposition 7.1 (a)**: the domain of a maximal monotone operator on a Hilbert space is
dense. If `f ⊥ D(A)`, solve `v₀ + A v₀ = f`; then `0 = re ⟪v₀, f⟫ = ‖v₀‖² + re ⟪A v₀, v₀⟫ ≥ ‖v₀‖²`,
so `v₀ = 0` and `f = 0` ([brezis2011functional], proof of Proposition 7.1 (a)). -/
theorem IsMaximalMonotone.dense_domain [CompleteSpace H] (hA : A.IsMaximalMonotone) :
    Dense (A.domain : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro f hf
  rw [Submodule.mem_orthogonal] at hf
  obtain ⟨v, hv⟩ := hA.exists_add_apply_eq f
  have h1 : ⟪(v : H), f⟫ = 0 := hf v v.2
  have h2 : ‖(v : H)‖ ^ 2 ≤ re ⟪(v : H), f⟫ := by
    rw [← hv, inner_add_right, _root_.map_add, inner_self_eq_norm_sq, inner_re_symm]
    exact le_add_of_nonneg_right (hA.isMonotone v)
  rw [h1, _root_.map_zero] at h2
  have hv0 : v = 0 :=
    Subtype.ext (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1
      (le_antisymm h2 (sq_nonneg _))))
  rw [← hv, hv0, map_zero, Submodule.coe_zero, add_zero]

/-- **The contraction step of Proposition 7.1 (c)**: if `A` is monotone and `I + c₀ A` maps
`D(A)` onto `H` for some `c₀ > 0`, then so does `I + c A` for every `c > c₀ / 2`. The equation
`u + c A u = f` is rewritten as the fixed-point equation
`u = J_{c₀} ((c₀/c) f + (1 - c₀/c) u)`, whose right-hand side is a contraction of `H` with
constant `|1 - c₀/c| < 1` because `J_{c₀} = (I + c₀ A)⁻¹` is nonexpansive
([brezis2011functional], proof of Proposition 7.1 (c)). -/
theorem IsMonotone.exists_add_smul_eq_of_exists_add_smul_eq [CompleteSpace H]
    (hA : A.IsMonotone) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (h : ∀ f : H, ∃ u : A.domain, (u : H) + (c₀ : 𝕜) • A u = f) {c : ℝ} (hc : c₀ / 2 < c)
    (f : H) : ∃ u : A.domain, (u : H) + (c : 𝕜) • A u = f := by
  choose J hJ using h
  have hc' : 0 < c := by linarith
  -- the inverse `J` of `I + c₀ A` is nonexpansive
  have hlip : ∀ x y : H, ‖(J x : H) - J y‖ ≤ ‖x - y‖ := fun x y => by
    have := hA.norm_le_norm_add_smul hc₀.le (J x - J y)
    rwa [map_sub, Submodule.coe_sub, smul_sub,
      show (J x : H) - J y + ((c₀ : 𝕜) • A (J x) - (c₀ : 𝕜) • A (J y)) =
        ((J x : H) + (c₀ : 𝕜) • A (J x)) - ((J y : H) + (c₀ : 𝕜) • A (J y)) by abel,
      hJ, hJ] at this
  set θ : ℝ := c₀ / c with hθ
  have hθ0 : 0 < θ := div_pos hc₀ hc'
  have hθ2 : θ < 2 := by
    rw [hθ, div_lt_iff₀ hc']
    linarith
  -- the contraction
  let Φ : H → H := fun u => J ((θ : 𝕜) • f + ((1 - θ : ℝ) : 𝕜) • u)
  have hΦ : LipschitzWith (Real.toNNReal |1 - θ|) Φ := by
    refine LipschitzWith.of_dist_le_mul fun u v => ?_
    simp only [Φ, dist_eq_norm, Real.coe_toNNReal _ (abs_nonneg _)]
    calc ‖(J ((θ : 𝕜) • f + ((1 - θ : ℝ) : 𝕜) • u) : H) -
          J ((θ : 𝕜) • f + ((1 - θ : ℝ) : 𝕜) • v)‖
        ≤ ‖((θ : 𝕜) • f + ((1 - θ : ℝ) : 𝕜) • u) - ((θ : 𝕜) • f + ((1 - θ : ℝ) : 𝕜) • v)‖ :=
          hlip _ _
      _ = |1 - θ| * ‖u - v‖ := by
          rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, norm_ofReal]
  have hcontr : ContractingWith (Real.toNNReal |1 - θ|) Φ := by
    refine ⟨Real.toNNReal_lt_one.2 ?_, hΦ⟩
    rw [abs_lt]
    constructor <;> linarith
  obtain ⟨u, hu⟩ : ∃ u : H, Φ u = u := ⟨_, hcontr.fixedPoint_isFixedPt⟩
  set w : H := (θ : 𝕜) • f + ((1 - θ : ℝ) : 𝕜) • u with hw
  have hJu : (J w : H) = u := hu
  have hspec : (J w : H) + (c₀ : 𝕜) • A (J w) = w := hJ w
  rw [hJu] at hspec
  refine ⟨J w, ?_⟩
  rw [hJu]
  have hθc : (c₀ : 𝕜) = (θ : 𝕜) * (c : 𝕜) := by
    rw [← ofReal_mul, hθ, div_mul_cancel₀ _ hc'.ne']
  have hθne : (θ : 𝕜) ≠ 0 := by exact_mod_cast hθ0.ne'
  apply smul_right_injective H hθne
  simp only
  rw [smul_add, smul_smul, ← hθc]
  have h1 : ((1 - θ : ℝ) : 𝕜) • u = u - (θ : 𝕜) • u := by
    rw [ofReal_sub, ofReal_one, sub_smul, one_smul]
  have hspec' : u + (c₀ : 𝕜) • A (J w) = (θ : 𝕜) • f + (u - (θ : 𝕜) • u) := by
    rw [hspec, hw, h1]
  calc (θ : 𝕜) • u + (c₀ : 𝕜) • A (J w) = (u + (c₀ : 𝕜) • A (J w)) - (u - (θ : 𝕜) • u) := by
        abel
    _ = (θ : 𝕜) • f := by rw [hspec']; abel

/-- **Proposition 7.1 (c), the surjectivity clause**: for a maximal monotone `A` and every
`c > 0`, `I + c A` maps `D(A)` onto `H`. By induction from `c₀ = 1`, the contraction step
`exists_add_smul_eq_of_exists_add_smul_eq` gives every `c > 2⁻ⁿ`
([brezis2011functional], proof of Proposition 7.1 (c)). -/
theorem IsMaximalMonotone.exists_add_smul_eq [CompleteSpace H] (hA : A.IsMaximalMonotone)
    {c : ℝ} (hc : 0 < c) (f : H) : ∃ u : A.domain, (u : H) + (c : 𝕜) • A u = f := by
  suffices h : ∀ n : ℕ, ∀ c : ℝ, (1 / 2 : ℝ) ^ n < c →
      ∀ f : H, ∃ u : A.domain, (u : H) + (c : 𝕜) • A u = f by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hc (by norm_num : (1 / 2 : ℝ) < 1)
    exact h n c hn f
  intro n
  induction n with
  | zero =>
    intro c hc f
    rw [pow_zero] at hc
    refine hA.isMonotone.exists_add_smul_eq_of_exists_add_smul_eq one_pos (fun f => ?_)
      (by linarith) f
    obtain ⟨u, hu⟩ := hA.exists_add_apply_eq f
    exact ⟨u, by rwa [ofReal_one, one_smul]⟩
  | succ n ih =>
    intro c hc f
    have h2 : (1 / 2 : ℝ) ^ n < 2 * c := by
      rw [pow_succ] at hc
      linarith
    exact hA.isMonotone.exists_add_smul_eq_of_exists_add_smul_eq
      (c₀ := ((1 / 2 : ℝ) ^ n + 2 * c) / 2)
      (by have := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n; linarith) (ih _ (by linarith))
      (by linarith) f

/-! ### The resolvent -/

variable (A) in
open scoped Classical in
/-- The **resolvent** `J_c = (I + c A)⁻¹` of `A` at `c : ℝ`, as a total function of `(A, c)`
([brezis2011functional] §7.1): some bounded operator `J` with `J f ∈ D(A)` and
`J f + c A (J f) = f` for every `f` when one exists (it is unique as soon as `I + c A` is
injective, in particular for a monotone `A` and `c ≥ 0`), and `0` otherwise. Its properties are
stated under `hA : A.IsMaximalMonotone` and `0 < c`. -/
def resolvent (c : ℝ) : H →L[𝕜] H :=
  if h : ∃ J : H →L[𝕜] H, ∀ f : H, ∃ hf : J f ∈ A.domain, J f + (c : 𝕜) • A ⟨J f, hf⟩ = f then
    h.choose
  else 0

/-- For a maximal monotone `A` and `c > 0`, the operator `I + c A` has a bounded inverse: the
resolvent exists. It is built from `exists_add_smul_eq`, made linear by `injective_add_smul` and
bounded by `norm_le_norm_add_smul`. -/
theorem IsMaximalMonotone.exists_resolvent [CompleteSpace H] (hA : A.IsMaximalMonotone) {c : ℝ}
    (hc : 0 < c) :
    ∃ J : H →L[𝕜] H, ∀ f : H, ∃ hf : J f ∈ A.domain, J f + (c : 𝕜) • A ⟨J f, hf⟩ = f := by
  choose g hg using hA.exists_add_smul_eq hc
  have hinj := hA.isMonotone.injective_add_smul hc.le
  let L : H →ₗ[𝕜] H :=
    { toFun := fun f => (g f : H)
      map_add' := fun x y => by
        have : g (x + y) = g x + g y := by
          apply hinj
          simp only
          calc (g (x + y) : H) + (c : 𝕜) • A (g (x + y)) = x + y := hg _
            _ = ((g x : H) + (c : 𝕜) • A (g x)) + ((g y : H) + (c : 𝕜) • A (g y)) := by
                rw [hg, hg]
            _ = (g x + g y : A.domain) + (c : 𝕜) • A (g x + g y) := by
                rw [Submodule.coe_add, map_add, smul_add]
                abel
        simp only [this, Submodule.coe_add]
      map_smul' := fun a x => by
        have : g (a • x) = a • g x := by
          apply hinj
          simp only
          calc (g (a • x) : H) + (c : 𝕜) • A (g (a • x)) = a • x := hg _
            _ = a • ((g x : H) + (c : 𝕜) • A (g x)) := by rw [hg]
            _ = (a • g x : A.domain) + (c : 𝕜) • A (a • g x) := by
                rw [Submodule.coe_smul, map_smul, smul_add, smul_comm]
        simp only [this, Submodule.coe_smul, RingHom.id_apply] }
  refine ⟨L.mkContinuous 1 fun f => ?_, fun f => ⟨(g f).2, hg f⟩⟩
  rw [one_mul]
  have := hA.isMonotone.norm_le_norm_add_smul hc.le (g f)
  rwa [hg f] at this

/-- The specification of the resolvent of a maximal monotone operator at `c > 0`:
`A.resolvent c f ∈ D(A)` and `A.resolvent c f + c A (A.resolvent c f) = f`. -/
theorem IsMaximalMonotone.resolvent_spec [CompleteSpace H] (hA : A.IsMaximalMonotone) {c : ℝ}
    (hc : 0 < c) (f : H) :
    ∃ hf : A.resolvent c f ∈ A.domain, A.resolvent c f + (c : 𝕜) • A ⟨A.resolvent c f, hf⟩ = f := by
  have h := hA.exists_resolvent hc
  unfold resolvent
  rw [dite_eq_left h]
  exact h.choose_spec f

/-- The resolvent takes its values in `D(A)`. -/
theorem IsMaximalMonotone.resolvent_apply_mem_domain [CompleteSpace H] (hA : A.IsMaximalMonotone)
    {c : ℝ} (hc : 0 < c) (f : H) : A.resolvent c f ∈ A.domain :=
  (hA.resolvent_spec hc f).fst

/-- `J_c f + c A (J_c f) = f`: the resolvent inverts `I + c A`. -/
theorem IsMaximalMonotone.resolvent_add_smul_apply [CompleteSpace H] (hA : A.IsMaximalMonotone)
    {c : ℝ} (hc : 0 < c) (f : H) :
    A.resolvent c f + (c : 𝕜) • A ⟨A.resolvent c f, hA.resolvent_apply_mem_domain hc f⟩ = f :=
  (hA.resolvent_spec hc f).snd

/-- **Uniqueness of the resolvent**: `J_c f = u` for `u ∈ D(A)` iff `u + c A u = f`. -/
theorem IsMaximalMonotone.resolvent_eq_iff [CompleteSpace H] (hA : A.IsMaximalMonotone) {c : ℝ}
    (hc : 0 < c) (u : A.domain) (f : H) :
    A.resolvent c f = u ↔ (u : H) + (c : 𝕜) • A u = f := by
  have h := hA.resolvent_add_smul_apply hc f
  constructor
  · intro hu
    have : (⟨A.resolvent c f, hA.resolvent_apply_mem_domain hc f⟩ : A.domain) = u :=
      Subtype.ext hu
    rw [← this]
    exact h
  · intro hu
    have := hA.isMonotone.injective_add_smul hc.le
      (a₁ := ⟨A.resolvent c f, hA.resolvent_apply_mem_domain hc f⟩) (a₂ := u) (h.trans hu.symm)
    exact congrArg Subtype.val this

/-- `J_c (u + c A u) = u` on `D(A)`: the resolvent is a left inverse of `I + c A`. -/
theorem IsMaximalMonotone.resolvent_apply_add_smul [CompleteSpace H] (hA : A.IsMaximalMonotone)
    {c : ℝ} (hc : 0 < c) (u : A.domain) :
    A.resolvent c ((u : H) + (c : 𝕜) • A u) = u :=
  (hA.resolvent_eq_iff hc u _).2 rfl

/-- **Proposition 7.1 (c), the bound, pointwise**: `‖J_c f‖ ≤ ‖f‖`. -/
theorem IsMaximalMonotone.norm_resolvent_apply_le [CompleteSpace H] (hA : A.IsMaximalMonotone)
    {c : ℝ} (hc : 0 < c) (f : H) : ‖A.resolvent c f‖ ≤ ‖f‖ := by
  have := hA.isMonotone.norm_le_norm_add_smul hc.le
    ⟨A.resolvent c f, hA.resolvent_apply_mem_domain hc f⟩
  rwa [hA.resolvent_add_smul_apply hc f] at this

/-- **Proposition 7.1 (c), the bound**: `‖J_c‖ ≤ 1` for every `c > 0`
([brezis2011functional] Proposition 7.1 (c)). -/
theorem IsMaximalMonotone.norm_resolvent_le_one [CompleteSpace H] (hA : A.IsMaximalMonotone)
    {c : ℝ} (hc : 0 < c) : ‖A.resolvent c‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    rw [one_mul]
    exact hA.norm_resolvent_apply_le hc f

/-- **Proposition 7.1 (b)**: a maximal monotone operator is closed. The graph of `A` is the
closed set `{(x, y) | x = J_1 (x + y)}`, a preimage of the diagonal under a continuous map
([brezis2011functional], proof of Proposition 7.1 (b)). -/
theorem IsMaximalMonotone.isClosed [CompleteSpace H] (hA : A.IsMaximalMonotone) : A.IsClosed := by
  have hgraph : (A.graph : Set (H × H)) = {p | p.1 = A.resolvent 1 (p.1 + p.2)} := by
    ext ⟨x, y⟩
    simp only [SetLike.mem_coe, mem_graph_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨u, rfl, rfl⟩
      have := hA.resolvent_apply_add_smul one_pos u
      rw [ofReal_one, one_smul] at this
      exact this.symm
    · intro hx
      set u : A.domain := ⟨A.resolvent 1 (x + y), hA.resolvent_apply_mem_domain one_pos (x + y)⟩
      have hu : (u : H) = x := hx.symm
      have h := hA.resolvent_add_smul_apply one_pos (x + y)
      rw [ofReal_one, one_smul] at h
      refine ⟨u, hu, ?_⟩
      calc A u = ((u : H) + A u) - (u : H) := by abel
        _ = y := by rw [h, hu]; abel
  change _root_.IsClosed (A.graph : Set (H × H))
  rw [hgraph]
  exact isClosed_eq continuous_fst
    ((A.resolvent 1).continuous.comp (continuous_fst.add continuous_snd))

/-- **Remark 1**: a positive multiple of a maximal monotone operator is maximal monotone
([brezis2011functional] Chapter 7, Remark 1). -/
theorem IsMaximalMonotone.smul [CompleteSpace H] (hA : A.IsMaximalMonotone) {c : ℝ}
    (hc : 0 < c) : ((c : 𝕜) • A).IsMaximalMonotone where
  isMonotone v := by
    change 0 ≤ re ⟪(c : 𝕜) • A v, (v : H)⟫
    rw [inner_smul_left, conj_ofReal, re_ofReal_mul]
    exact mul_nonneg hc.le (hA.isMonotone v)
  exists_add_apply_eq f := by
    obtain ⟨u, hu⟩ := hA.exists_add_smul_eq hc f
    exact ⟨u, hu⟩

/-! ### The Yosida approximation -/

variable (A) in
/-- The **Yosida approximation** `A_c = c⁻¹ (I - J_c)` of `A` at `c : ℝ`, a bounded operator
([brezis2011functional] §7.1); total in `(A, c)` like the resolvent. -/
def yosida (c : ℝ) : H →L[𝕜] H :=
  ((c⁻¹ : ℝ) : 𝕜) • (ContinuousLinearMap.id 𝕜 H - A.resolvent c)

variable (A) in
/-- `A_c v = c⁻¹ (v - J_c v)`. -/
theorem yosida_apply (c : ℝ) (v : H) :
    A.yosida c v = ((c⁻¹ : ℝ) : 𝕜) • (v - A.resolvent c v) :=
  rfl

variable (A) in
/-- `c A_c v = v - J_c v`. -/
theorem smul_yosida_apply {c : ℝ} (hc : c ≠ 0) (v : H) :
    (c : 𝕜) • A.yosida c v = v - A.resolvent c v := by
  rw [yosida_apply, smul_smul, ← ofReal_mul, mul_inv_cancel₀ hc, ofReal_one, one_smul]

/-- **Proposition 7.2 (a₁)**: `A_c v = A (J_c v)` for every `v ∈ H`, a rearrangement of
`J_c v + c A (J_c v) = v` ([brezis2011functional] Proposition 7.2 (a₁)). -/
theorem IsMaximalMonotone.yosida_apply_eq_apply_resolvent [CompleteSpace H]
    (hA : A.IsMaximalMonotone) {c : ℝ} (hc : 0 < c) (v : H) :
    A.yosida c v = A ⟨A.resolvent c v, hA.resolvent_apply_mem_domain hc v⟩ := by
  rw [yosida_apply, ← eq_sub_of_add_eq' (hA.resolvent_add_smul_apply hc v), smul_smul,
    ← ofReal_mul, inv_mul_cancel₀ hc.ne', ofReal_one, one_smul]

/-- **The resolvent commutes with `A` on `D(A)`**: `J_c (A u) = A (J_c u)` for `u ∈ D(A)`. Both
sides solve `w + c A w = A u`; for the right-hand side, `A (J_c u) = c⁻¹ (u - J_c u)` lies in
`D(A)` ([brezis2011functional], proof of Proposition 7.2 (a₂)). -/
theorem IsMaximalMonotone.resolvent_apply_comm [CompleteSpace H] (hA : A.IsMaximalMonotone)
    {c : ℝ} (hc : 0 < c) (u : A.domain) :
    A.resolvent c (A u) = A ⟨A.resolvent c u, hA.resolvent_apply_mem_domain hc u⟩ := by
  set j : A.domain := ⟨A.resolvent c u, hA.resolvent_apply_mem_domain hc u⟩ with hj
  have h : (j : H) + (c : 𝕜) • A j = u := hA.resolvent_add_smul_apply hc u
  set w : A.domain := ((c⁻¹ : ℝ) : 𝕜) • (u - j) with hw
  have hwH : (w : H) = A j := by
    rw [hw, Submodule.coe_smul, Submodule.coe_sub, ← eq_sub_of_add_eq' h, smul_smul,
      ← ofReal_mul, inv_mul_cancel₀ hc.ne', ofReal_one, one_smul]
  have hAw : A w = ((c⁻¹ : ℝ) : 𝕜) • (A u - A j) := by rw [hw, map_smul, map_sub]
  have key : (w : H) + (c : 𝕜) • A w = A u := by
    rw [hwH, hAw, smul_smul, ← ofReal_mul, mul_inv_cancel₀ hc.ne', ofReal_one, one_smul]
    abel
  rw [(hA.resolvent_eq_iff hc w (A u)).2 key, hwH]

/-- **Proposition 7.2 (a₂)**: `A_c v = J_c (A v)` for `v ∈ D(A)`
([brezis2011functional] Proposition 7.2 (a₂)). -/
theorem IsMaximalMonotone.yosida_apply_eq_resolvent_apply [CompleteSpace H]
    (hA : A.IsMaximalMonotone) {c : ℝ} (hc : 0 < c) (v : A.domain) :
    A.yosida c v = A.resolvent c (A v) := by
  rw [hA.yosida_apply_eq_apply_resolvent hc, hA.resolvent_apply_comm hc]

/-- **Proposition 7.2 (b)**: `‖A_c v‖ ≤ ‖A v‖` for `v ∈ D(A)`
([brezis2011functional] Proposition 7.2 (b)). -/
theorem IsMaximalMonotone.norm_yosida_apply_le_norm_apply [CompleteSpace H]
    (hA : A.IsMaximalMonotone) {c : ℝ} (hc : 0 < c) (v : A.domain) :
    ‖A.yosida c v‖ ≤ ‖A v‖ := by
  rw [hA.yosida_apply_eq_resolvent_apply hc]
  exact hA.norm_resolvent_apply_le hc _

/-- The rate of Proposition 7.2 (c) on the domain: `‖v - J_c v‖ ≤ c ‖A v‖` for `v ∈ D(A)`
([brezis2011functional], proof of Proposition 7.2 (c)). -/
theorem IsMaximalMonotone.norm_sub_resolvent_apply_le [CompleteSpace H]
    (hA : A.IsMaximalMonotone) {c : ℝ} (hc : 0 < c) (v : A.domain) :
    ‖(v : H) - A.resolvent c v‖ ≤ c * ‖A v‖ := by
  rw [← smul_yosida_apply A hc.ne', norm_smul, norm_ofReal, abs_of_pos hc]
  exact mul_le_mul_of_nonneg_left (hA.norm_yosida_apply_le_norm_apply hc v) hc.le

/-- **Proposition 7.2 (c)**: `J_c v → v` as `c → 0⁺`, for every `v ∈ H`. On `D(A)` by the rate
`‖v - J_c v‖ ≤ c ‖A v‖`; in general by density of `D(A)` and `‖J_c‖ ≤ 1`
([brezis2011functional] Proposition 7.2 (c)). -/
theorem IsMaximalMonotone.tendsto_resolvent_apply [CompleteSpace H] (hA : A.IsMaximalMonotone)
    (v : H) : Tendsto (fun c : ℝ => A.resolvent c v) (𝓝[>] 0) (𝓝 v) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨v₁, hv₁, hd⟩ := hA.dense_domain.exists_dist_lt v (by positivity : 0 < ε / 3)
  rw [dist_eq_norm] at hd
  refine ⟨ε / 3 / (‖A ⟨v₁, hv₁⟩‖ + 1), by positivity, fun c hc hcd => ?_⟩
  have hc' : 0 < c := hc
  rw [Real.dist_eq, sub_zero, abs_of_pos hc', lt_div_iff₀ (by positivity)] at hcd
  rw [dist_eq_norm]
  calc ‖A.resolvent c v - v‖
      = ‖A.resolvent c (v - v₁) + (A.resolvent c v₁ - v₁) + (v₁ - v)‖ := by
        rw [_root_.map_sub]
        congr 1
        abel
    _ ≤ ‖A.resolvent c (v - v₁)‖ + ‖A.resolvent c v₁ - v₁‖ + ‖v₁ - v‖ := norm_add₃_le
    _ ≤ ‖v - v₁‖ + c * ‖A ⟨v₁, hv₁⟩‖ + ‖v₁ - v‖ := by
        gcongr
        · exact hA.norm_resolvent_apply_le hc' _
        · rw [norm_sub_rev]
          exact hA.norm_sub_resolvent_apply_le hc' ⟨v₁, hv₁⟩
    _ < ε / 3 + ε / 3 + ε / 3 := by
        rw [norm_sub_rev v₁ v]
        have : c * ‖A ⟨v₁, hv₁⟩‖ ≤ c * (‖A ⟨v₁, hv₁⟩‖ + 1) := by
          gcongr
          linarith
        gcongr
        linarith
    _ = ε := by ring

/-- **Proposition 7.2 (d)**: `A_c v → A v` as `c → 0⁺`, for every `v ∈ D(A)`
([brezis2011functional] Proposition 7.2 (d)). -/
theorem IsMaximalMonotone.tendsto_yosida_apply [CompleteSpace H] (hA : A.IsMaximalMonotone)
    (v : A.domain) : Tendsto (fun c : ℝ => A.yosida c v) (𝓝[>] 0) (𝓝 (A v)) := by
  refine (hA.tendsto_resolvent_apply (A v)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  exact (hA.yosida_apply_eq_resolvent_apply hc v).symm

/-- **Inequality (3) of the proof of Proposition 7.2 (e)**: `c ‖A_c v‖² ≤ re ⟪A_c v, v⟫`, since
`re ⟪A_c v, v⟫ = re ⟪A_c v, v - J_c v⟫ + re ⟪A_c v, J_c v⟫ = c ‖A_c v‖² + re ⟪A (J_c v), J_c v⟫`
([brezis2011functional], proof of Proposition 7.2 (e)). -/
theorem IsMaximalMonotone.smul_norm_sq_yosida_le_re_inner [CompleteSpace H]
    (hA : A.IsMaximalMonotone) {c : ℝ} (hc : 0 < c) (v : H) :
    c * ‖A.yosida c v‖ ^ 2 ≤ re ⟪A.yosida c v, v⟫ := by
  have hv : (c : 𝕜) • A.yosida c v + A.resolvent c v = v := by
    rw [smul_yosida_apply A hc.ne']
    abel
  have : re ⟪A.yosida c v, v⟫ =
      re ⟪A.yosida c v, (c : 𝕜) • A.yosida c v + A.resolvent c v⟫ := by rw [hv]
  rw [this, inner_add_right, _root_.map_add, inner_smul_right, re_ofReal_mul,
    inner_self_eq_norm_sq]
  refine le_add_of_nonneg_right ?_
  have := hA.isMonotone ⟨A.resolvent c v, hA.resolvent_apply_mem_domain hc v⟩
  rwa [← hA.yosida_apply_eq_apply_resolvent hc] at this

/-- **Proposition 7.2 (e)**: the bounded operator `A_c` is monotone, `0 ≤ re ⟪A_c v, v⟫`
([brezis2011functional] Proposition 7.2 (e)). -/
theorem IsMaximalMonotone.re_inner_yosida_nonneg [CompleteSpace H] (hA : A.IsMaximalMonotone)
    {c : ℝ} (hc : 0 < c) (v : H) : 0 ≤ re ⟪A.yosida c v, v⟫ :=
  (mul_nonneg hc.le (sq_nonneg _)).trans (hA.smul_norm_sq_yosida_le_re_inner hc v)

/-- **Proposition 7.2 (f), pointwise**: `‖A_c v‖ ≤ c⁻¹ ‖v‖`, from (3) and Cauchy–Schwarz
([brezis2011functional] Proposition 7.2 (f)). -/
theorem IsMaximalMonotone.norm_yosida_apply_le [CompleteSpace H] (hA : A.IsMaximalMonotone)
    {c : ℝ} (hc : 0 < c) (v : H) : ‖A.yosida c v‖ ≤ c⁻¹ * ‖v‖ := by
  have h1 := hA.smul_norm_sq_yosida_le_re_inner hc v
  have h2 := re_inner_le_norm (𝕜 := 𝕜) (A.yosida c v) v
  rcases (norm_nonneg (A.yosida c v)).eq_or_lt with h0 | h0
  · rw [← h0]
    positivity
  · rw [le_inv_mul_iff₀ hc]
    have : c * ‖A.yosida c v‖ * ‖A.yosida c v‖ ≤ ‖v‖ * ‖A.yosida c v‖ :=
      calc c * ‖A.yosida c v‖ * ‖A.yosida c v‖ = c * ‖A.yosida c v‖ ^ 2 := by ring
        _ ≤ re ⟪A.yosida c v, v⟫ := h1
        _ ≤ ‖A.yosida c v‖ * ‖v‖ := h2
        _ = ‖v‖ * ‖A.yosida c v‖ := mul_comm _ _
    exact le_of_mul_le_mul_right this h0

/-- **Proposition 7.2 (f)**: `‖A_c‖ ≤ c⁻¹` ([brezis2011functional] Proposition 7.2 (f)). -/
theorem IsMaximalMonotone.norm_yosida_le [CompleteSpace H] (hA : A.IsMaximalMonotone) {c : ℝ}
    (hc : 0 < c) : ‖A.yosida c‖ ≤ c⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 hc.le) (hA.norm_yosida_apply_le hc)

/-- **The algebraic inequality (12) of the proof of the Hille–Yosida theorem**, for arbitrary
vectors: `re ⟪A_c x - A_d y, c A_c x - d A_d y⟫ ≤ re ⟪A_c x - A_d y, x - y⟫`, because
`x - y = (c A_c x - d A_d y) + (J_c x - J_d y)` and
`re ⟪A_c x - A_d y, J_c x - J_d y⟫ = re ⟪A (J_c x - J_d y), J_c x - J_d y⟫ ≥ 0`
([brezis2011functional], proof of Theorem 7.4, Step 3). -/
theorem IsMaximalMonotone.re_inner_yosida_sub_yosida_ge [CompleteSpace H]
    (hA : A.IsMaximalMonotone) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (x y : H) :
    re ⟪A.yosida c x - A.yosida d y, (c : 𝕜) • A.yosida c x - (d : 𝕜) • A.yosida d y⟫ ≤
      re ⟪A.yosida c x - A.yosida d y, x - y⟫ := by
  have hxy : x - y = ((c : 𝕜) • A.yosida c x - (d : 𝕜) • A.yosida d y) +
      (A.resolvent c x - A.resolvent d y) := by
    rw [smul_yosida_apply A hc.ne', smul_yosida_apply A hd.ne']
    abel
  rw [hxy, inner_add_right, _root_.map_add]
  refine le_add_of_nonneg_right ?_
  have := hA.isMonotone (⟨A.resolvent c x, hA.resolvent_apply_mem_domain hc x⟩ -
    ⟨A.resolvent d y, hA.resolvent_apply_mem_domain hd y⟩)
  rwa [map_sub, Submodule.coe_sub, ← hA.yosida_apply_eq_apply_resolvent hc,
    ← hA.yosida_apply_eq_apply_resolvent hd] at this

/-! ### The domains `D(A^k)` as Hilbert spaces -/

section PowDomain

variable (A) in
/-- The graph of the powers of `A`: the tuples `(u, A u, …, A^k u)` inside the `ℓ²`-product
`PiLp 2 (Fin (k + 1) → H)`, i.e. the tuples whose consecutive entries are related by `A`
([brezis2011functional] §7.3, the definition of `D(A^k)`). -/
def powGraph (k : ℕ) : Submodule 𝕜 (PiLp 2 fun _ : Fin (k + 1) => H) where
  carrier := {x | ∀ i : Fin k, ∃ h : x i.castSucc ∈ A.domain, A ⟨x i.castSucc, h⟩ = x i.succ}
  zero_mem' := fun i => ⟨by simp, by
    have h : (⟨(0 : PiLp 2 fun _ : Fin (k + 1) => H) i.castSucc, by simp⟩ : A.domain) = 0 :=
      Subtype.ext (by simp)
    rw [h, map_zero]
    simp⟩
  add_mem' := by
    rintro x y hx hy i
    obtain ⟨hx1, hx2⟩ := hx i
    obtain ⟨hy1, hy2⟩ := hy i
    refine ⟨by simpa using add_mem hx1 hy1, ?_⟩
    have : (⟨(x + y) i.castSucc, by simpa using add_mem hx1 hy1⟩ : A.domain) =
        ⟨x i.castSucc, hx1⟩ + ⟨y i.castSucc, hy1⟩ := by
      ext
      simp
    rw [this, map_add, hx2, hy2]
    simp
  smul_mem' := by
    rintro c x hx i
    obtain ⟨hx1, hx2⟩ := hx i
    refine ⟨by simpa using Submodule.smul_mem _ c hx1, ?_⟩
    have : (⟨(c • x) i.castSucc, by simpa using Submodule.smul_mem _ c hx1⟩ : A.domain) =
        c • ⟨x i.castSucc, hx1⟩ := by
      ext
      simp
    rw [this, map_smul, hx2]
    simp

variable (A) in
/-- Membership in `powGraph`: consecutive coordinates are related by `A`. -/
theorem mem_powGraph_iff {k : ℕ} {x : PiLp 2 fun _ : Fin (k + 1) => H} :
    x ∈ A.powGraph k ↔
      ∀ i : Fin k, ∃ h : x i.castSucc ∈ A.domain, A ⟨x i.castSucc, h⟩ = x i.succ :=
  Iff.rfl

variable (A) in
/-- The book's Hilbert space `D(A^k)` ([brezis2011functional] §7.3): the tuples
`(u, A u, …, A^k u)`, a submodule of the `ℓ²`-product `PiLp 2 (Fin (k + 1) → H)`, with the
inner product `∑_{j ≤ k} ⟪A^j u, A^j v⟫` and the norm `(∑_{j ≤ k} ‖A^j u‖²)^{1/2}` inherited
from it (`PowDomain.inner_def`, `PowDomain.norm_sq_eq`). `A.PowDomain 1` is `D(A)` with the
Hilbert graph norm, and `A.PowDomain 0` is `H`. -/
abbrev PowDomain (k : ℕ) : Type _ := ↥(A.powGraph k)

namespace PowDomain

variable (A) in
/-- `A^j` as a bounded operator on `D(A^k)`, for `j ≤ k`: the `j`-th coordinate of the tuple.
`applyL A k 0` is the inclusion `D(A^k) → H` and `applyL A 1 1` is `A` on `D(A)`. -/
def applyL (k : ℕ) (j : Fin (k + 1)) : A.PowDomain k →L[𝕜] H :=
  (PiLp.proj (𝕜 := 𝕜) (p := 2) (fun _ : Fin (k + 1) => H) j).comp (A.powGraph k).subtypeL

variable {k : ℕ}

/-- `applyL A k j x` is the `j`-th coordinate of the tuple `x`. -/
theorem applyL_apply (j : Fin (k + 1)) (x : A.PowDomain k) :
    applyL A k j x = (x : PiLp 2 fun _ : Fin (k + 1) => H) j :=
  rfl

/-- Two elements of `D(A^k)` with the same coordinates are equal. -/
theorem ext {x y : A.PowDomain k} (h : ∀ j, applyL A k j x = applyL A k j y) : x = y :=
  Subtype.ext (PiLp.ext h)

/-- The inner product of `D(A^k)` is `∑_{j ≤ k} ⟪A^j x, A^j y⟫`. -/
theorem inner_def (x y : A.PowDomain k) : ⟪x, y⟫ = ∑ j, ⟪applyL A k j x, applyL A k j y⟫ :=
  rfl

/-- The norm of `D(A^k)` is `(∑_{j ≤ k} ‖A^j x‖²)^{1/2}`. -/
theorem norm_sq_eq (x : A.PowDomain k) : ‖x‖ ^ 2 = ∑ j, ‖applyL A k j x‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 _ (x : PiLp 2 fun _ : Fin (k + 1) => H)

/-- Every coordinate map is a contraction: `‖A^j x‖ ≤ ‖x‖_{D(A^k)}`. -/
theorem norm_applyL_apply_le (j : Fin (k + 1)) (x : A.PowDomain k) : ‖applyL A k j x‖ ≤ ‖x‖ :=
  PiLp.norm_apply_le (x : PiLp 2 fun _ : Fin (k + 1) => H) j

/-- The coordinates `0, …, k - 1` of an element of `D(A^k)` lie in `D(A)`. -/
theorem applyL_mem_domain (x : A.PowDomain k) (i : Fin k) :
    applyL A k i.castSucc x ∈ A.domain :=
  (x.2 i).fst

/-- Consecutive coordinates are related by `A`: `A (A^i x) = A^{i+1} x`. -/
theorem apply_applyL (x : A.PowDomain k) (i : Fin k) :
    A ⟨applyL A k i.castSucc x, applyL_mem_domain x i⟩ = applyL A k i.succ x :=
  (x.2 i).snd

/-- The membership condition of `powGraph`, transported along equalities of the entries. -/
theorem exists_apply_eq_of_eq {a b : H} (ha : a ∈ A.domain) (hab : A ⟨a, ha⟩ = b) {a' b' : H}
    (h1 : a' = a) (h2 : b' = b) : ∃ h : a' ∈ A.domain, A ⟨a', h⟩ = b' := by
  subst h1
  subst h2
  exact ⟨ha, hab⟩

/-- An element of `D(A^k)` is determined by its `0`-th coordinate `u`: the others are
`A u, A² u, …`. -/
theorem applyL_zero_injective : Function.Injective (applyL A k 0) := by
  intro x y hxy
  refine ext fun j => ?_
  induction j using Fin.induction with
  | zero => exact hxy
  | succ i ih =>
    rw [← apply_applyL x i, ← apply_applyL y i]
    congr 1
    exact Subtype.ext ih

variable (A) in
/-- The element of `D(A^k)` with the coordinates `f`, for a tuple `f` whose consecutive entries
are related by `A`. -/
def mk (f : Fin (k + 1) → H)
    (hf : ∀ i : Fin k, ∃ h : f i.castSucc ∈ A.domain, A ⟨f i.castSucc, h⟩ = f i.succ) :
    A.PowDomain k :=
  ⟨toLp 2 f, hf⟩

/-- The coordinates of `mk A f hf` are `f`. -/
@[simp]
theorem applyL_mk (f : Fin (k + 1) → H) (hf) (j : Fin (k + 1)) : applyL A k j (mk A f hf) = f j :=
  rfl

/-- Reindexing the coordinates along an injection does not increase the norm. -/
theorem norm_mk_comp_le {l : ℕ} (e : Fin (l + 1) → Fin (k + 1)) (he : Function.Injective e)
    (x : A.PowDomain k) (hf) : ‖mk A (fun i => applyL A k (e i) x) hf‖ ≤ ‖x‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_eq, norm_sq_eq]
  simp only [applyL_mk]
  rw [← Finset.sum_image (f := fun i => ‖applyL A k i x‖ ^ 2) he.injOn]
  exact Finset.sum_le_univ_sum_of_nonneg fun i => sq_nonneg _

variable (A) in
/-- The inclusion `D(A^{k+1}) ⊆ D(A^k)`: drop the last coordinate. A contraction. -/
def castL (k : ℕ) : A.PowDomain (k + 1) →L[𝕜] A.PowDomain k :=
  LinearMap.mkContinuous
    { toFun := fun x => mk A (fun j => applyL A (k + 1) j.castSucc x) fun i =>
        exists_apply_eq_of_eq (applyL_mem_domain x i.castSucc) (apply_applyL x i.castSucc) rfl
          (by rw [Fin.succ_castSucc])
      map_add' := fun x y => ext fun j => by simp
      map_smul' := fun c x => ext fun j => by simp }
    1 fun x => by
      rw [one_mul]
      exact norm_mk_comp_le _ (Fin.castSucc_injective _) x _

/-- The coordinates of `castL x` are the first `k + 1` coordinates of `x`. -/
@[simp]
theorem applyL_castL (j : Fin (k + 1)) (x : A.PowDomain (k + 1)) :
    applyL A k j (castL A k x) = applyL A (k + 1) j.castSucc x :=
  rfl

/-- `castL` is a contraction. -/
theorem norm_castL_apply_le (x : A.PowDomain (k + 1)) : ‖castL A k x‖ ≤ ‖x‖ :=
  norm_mk_comp_le _ (Fin.castSucc_injective _) x _

variable (A) in
/-- The operator `A` from `D(A^{k+1})` to `D(A^k)`: drop the first coordinate. A contraction. -/
def shiftL (k : ℕ) : A.PowDomain (k + 1) →L[𝕜] A.PowDomain k :=
  LinearMap.mkContinuous
    { toFun := fun x => mk A (fun j => applyL A (k + 1) j.succ x) fun i =>
        exists_apply_eq_of_eq (applyL_mem_domain x i.succ) (apply_applyL x i.succ)
          (by rw [Fin.succ_castSucc]) rfl
      map_add' := fun x y => ext fun j => by simp
      map_smul' := fun c x => ext fun j => by simp }
    1 fun x => by
      rw [one_mul]
      exact norm_mk_comp_le _ (Fin.succ_injective _) x _

/-- The coordinates of `shiftL x` are the last `k + 1` coordinates of `x`. -/
@[simp]
theorem applyL_shiftL (j : Fin (k + 1)) (x : A.PowDomain (k + 1)) :
    applyL A k j (shiftL A k x) = applyL A (k + 1) j.succ x :=
  rfl

/-- `shiftL` is a contraction. -/
theorem norm_shiftL_apply_le (x : A.PowDomain (k + 1)) : ‖shiftL A k x‖ ≤ ‖x‖ :=
  norm_mk_comp_le _ (Fin.succ_injective _) x _

/-- The `0`-th coordinate of `shiftL x` is `A` applied to the `0`-th coordinate of `x`. -/
theorem applyL_zero_shiftL (x : A.PowDomain (k + 1)) :
    applyL A k 0 (shiftL A k x) = A ⟨applyL A (k + 1) 0 x, applyL_mem_domain x 0⟩ := by
  rw [applyL_shiftL]
  exact (apply_applyL x 0).symm

variable (A) in
/-- The inclusion `D(A^k) ⊆ D(A^j)` for `j ≤ k`: keep the first `j + 1` coordinates. A
contraction; `castL` is the case `j + 1 = k`. -/
def castLE {j : ℕ} (h : j ≤ k) : A.PowDomain k →L[𝕜] A.PowDomain j :=
  LinearMap.mkContinuous
    { toFun := fun x => mk A (fun i => applyL A k (Fin.castLE (by omega) i) x) fun i =>
        exists_apply_eq_of_eq (applyL_mem_domain x (Fin.castLE (by omega) i))
          (apply_applyL x (Fin.castLE (by omega) i)) (by simp) (by simp)
      map_add' := fun x y => ext fun i => by simp
      map_smul' := fun c x => ext fun i => by simp }
    1 fun x => by
      rw [one_mul]
      exact norm_mk_comp_le _ (Fin.castLE_injective _) x _

/-- The coordinates of `castLE h x` are the first `j + 1` coordinates of `x`. -/
@[simp]
theorem applyL_castLE {j : ℕ} (h : j ≤ k) (i : Fin (j + 1)) (x : A.PowDomain k) :
    applyL A j i (castLE A h x) = applyL A k (Fin.castLE (by omega) i) x :=
  rfl

/-- `castLE` is a contraction. -/
theorem norm_castLE_apply_le {j : ℕ} (h : j ≤ k) (x : A.PowDomain k) :
    ‖castLE A h x‖ ≤ ‖x‖ :=
  norm_mk_comp_le _ (Fin.castLE_injective _) x _

/-- `castLE` along `k ≤ k` is the identity. -/
@[simp]
theorem castLE_rfl (x : A.PowDomain k) : castLE A le_rfl x = x :=
  ext fun i => by simp

/-- `castLE` composes. -/
theorem castLE_castLE {j l : ℕ} (hjl : j ≤ l) (hlk : l ≤ k) (x : A.PowDomain k) :
    castLE A hjl (castLE A hlk x) = castLE A (hjl.trans hlk) x :=
  ext fun i => by simp

/-- `castL` after `castLE` is `castLE`. -/
theorem castL_castLE {j : ℕ} (h : j + 1 ≤ k) (x : A.PowDomain k) :
    castL A j (castLE A h x) = castLE A (by omega) x :=
  ext fun i => by simp

/-- `castLE` along `k ≤ k + 1` is `castL`. -/
theorem castLE_succ_eq_castL (x : A.PowDomain (k + 1)) :
    castLE A (Nat.le_succ k) x = castL A k x :=
  ext fun _ => rfl

/-- The **assembly constructor**: an element `x` of `D(A^k)` whose last coordinate `A^k u` lies
in `D(A)` extends to the element `(u, …, A^k u, A^{k+1} u)` of `D(A^{k+1})`. -/
def snoc (x : A.PowDomain k) (h : applyL A k (Fin.last k) x ∈ A.domain) :
    A.PowDomain (k + 1) :=
  mk A (Fin.snoc (fun i => applyL A k i x) (A ⟨applyL A k (Fin.last k) x, h⟩)) fun i => by
    induction i using Fin.lastCases with
    | last =>
      exact exists_apply_eq_of_eq h rfl (Fin.snoc_castSucc _ _ _)
        (by rw [Fin.succ_last, Fin.snoc_last])
    | cast i =>
      exact exists_apply_eq_of_eq (applyL_mem_domain x i) (apply_applyL x i)
        (Fin.snoc_castSucc _ _ _) (by rw [Fin.succ_castSucc, Fin.snoc_castSucc])

/-- The first `k + 1` coordinates of `snoc x h` are those of `x`. -/
@[simp]
theorem applyL_snoc_castSucc (x : A.PowDomain k) (h) (i : Fin (k + 1)) :
    applyL A (k + 1) i.castSucc (snoc x h) = applyL A k i x := by
  unfold snoc
  rw [applyL_mk, Fin.snoc_castSucc]

/-- The last coordinate of `snoc x h` is `A` of the last coordinate of `x`. -/
@[simp]
theorem applyL_snoc_last (x : A.PowDomain k) (h) :
    applyL A (k + 1) (Fin.last (k + 1)) (snoc x h) = A ⟨applyL A k (Fin.last k) x, h⟩ := by
  unfold snoc
  rw [applyL_mk, Fin.snoc_last]

/-- `castL` is a left inverse of `snoc`. -/
@[simp]
theorem castL_snoc (x : A.PowDomain k) (h) : castL A k (snoc x h) = x :=
  ext fun i => by simp

end PowDomain

open PowDomain

/-- **`D(A^k)` is a Hilbert space** when `A` is closed: its graph `powGraph` is closed in
`PiLp 2 (Fin (k + 1) → H)`, being the intersection of the preimages of the closed graph of `A`
under the continuous maps `x ↦ (x_i, x_{i+1})` ([brezis2011functional] §7.3). -/
theorem isClosed_powGraph (hA : A.IsClosed) (k : ℕ) :
    _root_.IsClosed (A.powGraph k : Set (PiLp 2 fun _ : Fin (k + 1) => H)) := by
  have hA' : _root_.IsClosed (A.graph : Set (H × H)) := hA
  have : (A.powGraph k : Set (PiLp 2 fun _ : Fin (k + 1) => H)) =
      ⋂ i : Fin k, (fun x : PiLp 2 fun _ : Fin (k + 1) => H => (x i.castSucc, x i.succ)) ⁻¹'
        (A.graph : Set (H × H)) := by
    ext x
    simp only [SetLike.mem_coe, mem_powGraph_iff, Set.mem_iInter, Set.mem_preimage, mem_graph_iff]
    refine forall_congr' fun i => ⟨fun ⟨h, hx⟩ => ⟨⟨_, h⟩, rfl, hx⟩, fun ⟨y, hy, hx⟩ => ?_⟩
    exact exists_apply_eq_of_eq y.2 hx hy.symm rfl
  rw [this]
  refine isClosed_iInter fun i => hA'.preimage ?_
  exact ((PiLp.proj (𝕜 := 𝕜) (p := 2) _ i.castSucc).continuous).prodMk
    ((PiLp.proj (𝕜 := 𝕜) (p := 2) _ i.succ).continuous)

/-- **`D(A^k)` is complete** when `A` is closed and `H` complete — the book's "it is easily
seen that `D(A^k)` is a Hilbert space" ([brezis2011functional] §7.3). Not an instance, the
hypothesis being a proof; consumers write `haveI := hA.completeSpace_powDomain k`. -/
theorem IsClosed.completeSpace_powDomain [CompleteSpace H] (hA : A.IsClosed) (k : ℕ) :
    CompleteSpace (A.PowDomain k) :=
  (isClosed_powGraph hA k).completeSpace_coe

/-! ### The part of `A` in `D(A^k)` -/

variable (A) in
/-- The domain of the part of `A` in `D(A^k)`: the elements whose last coordinate `A^k u` lies
in `D(A)`, i.e. `D(A^{k+1})` seen inside `D(A^k)` (the image of `castL`). -/
def powPartDomain (k : ℕ) : Submodule 𝕜 (A.PowDomain k) where
  carrier := {x | applyL A k (Fin.last k) x ∈ A.domain}
  zero_mem' := by simp
  add_mem' := fun hx hy => by simpa using add_mem hx hy
  smul_mem' := fun c x hx => by simpa using Submodule.smul_mem _ c hx

/-- Membership in the domain of the part: the last coordinate lies in `D(A)`. -/
theorem mem_powPartDomain_iff {k : ℕ} {x : A.PowDomain k} :
    x ∈ A.powPartDomain k ↔ applyL A k (Fin.last k) x ∈ A.domain :=
  Iff.rfl

/-- All coordinates of an element of `D(A^{k+1}) ⊆ D(A^k)` lie in `D(A)`. -/
theorem applyL_mem_domain_of_mem_powPartDomain {k : ℕ} {x : A.PowDomain k}
    (hx : x ∈ A.powPartDomain k) (i : Fin (k + 1)) : applyL A k i x ∈ A.domain := by
  induction i using Fin.lastCases with
  | last => exact hx
  | cast i => exact applyL_mem_domain x i

/-- `A` applied to a sum of elements of `D(A)`, with the membership proofs made explicit. -/
theorem apply_mk_add {a b : H} (h : a + b ∈ A.domain) (ha : a ∈ A.domain) (hb : b ∈ A.domain) :
    A ⟨a + b, h⟩ = A ⟨a, ha⟩ + A ⟨b, hb⟩ :=
  map_add A ⟨a, ha⟩ ⟨b, hb⟩

/-- `A` applied to a multiple of an element of `D(A)`, with the membership proof explicit. -/
theorem apply_mk_smul {c : 𝕜} {a : H} (h : c • a ∈ A.domain) (ha : a ∈ A.domain) :
    A ⟨c • a, h⟩ = c • A ⟨a, ha⟩ :=
  map_smul A c ⟨a, ha⟩

/-- The tuple `(A u, A² u, …, A^{k+1} u)` lies in `powGraph`, for `u ∈ D(A^{k+1})`. -/
theorem powPart_mem_aux {k : ℕ} {x : A.PowDomain k} (hx : x ∈ A.powPartDomain k) (i : Fin k) :
    ∃ h : A ⟨applyL A k i.castSucc x, applyL_mem_domain_of_mem_powPartDomain hx i.castSucc⟩ ∈
      A.domain, A ⟨_, h⟩ =
        A ⟨applyL A k i.succ x, applyL_mem_domain_of_mem_powPartDomain hx i.succ⟩ :=
  exists_apply_eq_of_eq (a := applyL A k i.succ x)
    (applyL_mem_domain_of_mem_powPartDomain hx i.succ) rfl (apply_applyL x i) rfl

variable (A) in
/-- **The part of `A` in `D(A^k)`**: the operator `D(A^{k+1}) ⊆ D(A^k) → D(A^k)`, `u ↦ A u`,
whose coordinates are `(A u, A² u, …, A^{k+1} u)`. This is the book's `A₁ : D(A²) ⊆ D(A) → D(A)`
(proof of Theorem 7.5) and `Ã : D(A^k) ⊆ D(A^{k-1}) → D(A^{k-1})` (proof of Theorem 7.7) in one
definition ([brezis2011functional] §7.3, §7.4). -/
def powPart (k : ℕ) : A.PowDomain k →ₗ.[𝕜] A.PowDomain k where
  domain := A.powPartDomain k
  toFun :=
    { toFun := fun x => PowDomain.mk A
        (fun i => A ⟨applyL A k i x, applyL_mem_domain_of_mem_powPartDomain x.2 i⟩)
        (powPart_mem_aux x.2)
      map_add' := fun x y => PowDomain.ext fun i => by
        simp only [applyL_mk, Submodule.coe_add, _root_.map_add]
        exact apply_mk_add _ _ _
      map_smul' := fun c x => PowDomain.ext fun i => by
        simp only [applyL_mk, Submodule.coe_smul, _root_.map_smul, RingHom.id_apply]
        exact apply_mk_smul _ _ }

/-- The domain of the part of `A` is `powPartDomain`. -/
theorem powPart_domain (k : ℕ) : (A.powPart k).domain = A.powPartDomain k :=
  rfl

/-- Membership in the domain of the part of `A`: the last coordinate lies in `D(A)`. -/
theorem mem_powPart_domain_iff {k : ℕ} {x : A.PowDomain k} :
    x ∈ (A.powPart k).domain ↔ applyL A k (Fin.last k) x ∈ A.domain :=
  Iff.rfl

/-- The coordinates of `A x` for `x ∈ D(A^{k+1}) ⊆ D(A^k)`: `(A x)_i = A (x_i)`. -/
@[simp]
theorem applyL_powPart_apply {k : ℕ} (x : (A.powPart k).domain) (i : Fin (k + 1)) :
    applyL A k i (A.powPart k x) =
      A ⟨applyL A k i x, applyL_mem_domain_of_mem_powPartDomain x.2 i⟩ :=
  rfl

/-- The `0`-th coordinate of `A x` is `A u`: the part of `A` is `A` ([brezis2011functional],
proof of Theorem 7.5, `A₁ u = A u`). -/
theorem applyL_zero_powPart_apply {k : ℕ} (x : (A.powPart k).domain) :
    applyL A k 0 (A.powPart k x) =
      A ⟨applyL A k 0 x, applyL_mem_domain_of_mem_powPartDomain x.2 0⟩ :=
  rfl

/-- The part of `A` in `D(A^k)` is the composite `shiftL ∘ snoc`: the tuple
`(A u, A² u, …, A^{k+1} u)`. -/
theorem powPart_apply_eq_shiftL_snoc {k : ℕ} (x : (A.powPart k).domain) :
    A.powPart k x = shiftL A k (snoc (x : A.PowDomain k) (mem_powPart_domain_iff.1 x.2)) := by
  refine PowDomain.ext fun i => ?_
  rw [applyL_powPart_apply, applyL_shiftL]
  induction i using Fin.lastCases with
  | last => exact (applyL_snoc_last _ _).symm
  | cast i => rw [Fin.succ_castSucc, applyL_snoc_castSucc, apply_applyL]

/-- `castL x ∈ D(A^{k+1}) ⊆ D(A^k)` for every `x ∈ D(A^{k+1})`: the domain of the part is the
range of `castL`. -/
theorem castL_mem_powPart_domain {k : ℕ} (x : A.PowDomain (k + 1)) :
    castL A k x ∈ (A.powPart k).domain := by
  rw [mem_powPart_domain_iff, applyL_castL]
  exact applyL_mem_domain x (Fin.last k)

/-- The range of `castL` is the domain of the part of `A`, as sets. -/
theorem range_castL {k : ℕ} :
    Set.range (castL A k) = ((A.powPart k).domain : Set (A.PowDomain k)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact castL_mem_powPart_domain y
  · intro hx
    exact ⟨snoc x (mem_powPart_domain_iff.1 hx), castL_snoc x _⟩

/-- The part of a monotone operator is monotone: `re ⟪A x, x⟫_{D(A^k)} = ∑_j re ⟪A x_j, x_j⟫`
([brezis2011functional], proof of Theorem 7.5). -/
theorem IsMonotone.powPart (hA : A.IsMonotone) (k : ℕ) : (A.powPart k).IsMonotone := by
  intro x
  rw [inner_def, _root_.map_sum]
  simp only [applyL_powPart_apply]
  exact Finset.sum_nonneg fun i _ => hA _

/-- The part of a symmetric operator is symmetric ([brezis2011functional], proof of Theorem
7.7, "`Ã` is symmetric in `H̃`"). -/
theorem IsFormalAdjoint.powPart (hs : A.IsFormalAdjoint A) (k : ℕ) :
    (A.powPart k).IsFormalAdjoint (A.powPart k) := by
  intro x y
  rw [inner_def, inner_def]
  simp only [applyL_powPart_apply]
  exact Finset.sum_congr rfl fun i _ => hs ⟨applyL A k i x, _⟩ ⟨applyL A k i y, _⟩

/-- **The part of a maximal monotone operator is maximal monotone** ([brezis2011functional],
proof of Theorem 7.5, "it is easy to check that `A₁` is maximal monotone in `H₁`"): the solution
of `x + A x = f` in `D(A^k)` is the tuple `(J_1 f_j)_j`, since `J_1` commutes with `A`. -/
theorem IsMaximalMonotone.powPart [CompleteSpace H] (hA : A.IsMaximalMonotone) (k : ℕ) :
    (A.powPart k).IsMaximalMonotone := by
  refine ⟨hA.isMonotone.powPart k, fun f => ?_⟩
  have hJ : ∀ v, A.resolvent 1 v ∈ A.domain := hA.resolvent_apply_mem_domain one_pos
  have hJ' : ∀ v, A.resolvent 1 v + A ⟨A.resolvent 1 v, hJ v⟩ = v := fun v => by
    have := hA.resolvent_add_smul_apply one_pos v
    rwa [ofReal_one, one_smul] at this
  let x : A.PowDomain k := PowDomain.mk A (fun i => A.resolvent 1 (applyL A k i f)) fun i =>
    ⟨hJ _, by rw [← apply_applyL f i, hA.resolvent_apply_comm one_pos]⟩
  refine ⟨⟨x, hJ _⟩, PowDomain.ext fun i => ?_⟩
  rw [_root_.map_add, applyL_powPart_apply]
  exact hJ' _

/-- **Lemma 7.2, at every level**: `D(A^{k+1})` is dense in `D(A^k)` for the norm of `D(A^k)`;
at `k = 1` this is the book's "`D(A²)` is dense in `D(A)` for the graph norm". The tuple
`(J_c x_j)_j` lies in the range of `castL` and converges to `x` as `c → 0⁺`
([brezis2011functional] Lemma 7.2). -/
theorem IsMaximalMonotone.dense_range_castL [CompleteSpace H] (hA : A.IsMaximalMonotone)
    (k : ℕ) : Dense (Set.range (castL A k)) := by
  intro x
  rw [Metric.mem_closure_iff]
  intro ε hε
  -- the tuples `(J_c x_j)_j` converge to `x` in the `ℓ²`-norm
  have hΦ : Tendsto (fun c : ℝ => (toLp 2 fun i => A.resolvent c (applyL A k i x) :
      PiLp 2 fun _ : Fin (k + 1) => H)) (𝓝[>] 0) (𝓝 (x : PiLp 2 fun _ : Fin (k + 1) => H)) := by
    have h1 : Tendsto (fun c : ℝ => fun i => A.resolvent c (applyL A k i x)) (𝓝[>] 0)
        (𝓝 fun i => applyL A k i x) :=
      tendsto_pi_nhds.2 fun i => hA.tendsto_resolvent_apply _
    exact ((PiLp.continuous_toLp (p := 2) (β := fun _ : Fin (k + 1) => H)).tendsto _).comp h1
  obtain ⟨c, hd, hc⟩ := ((hΦ.eventually (Metric.ball_mem_nhds _ hε)).and
    self_mem_nhdsWithin).exists
  have hc'' : (0 : ℝ) < c := hc
  -- the tuple `(J_c x_j)_j` lies in `D(A^k)`, and its last entry lies in `D(A)`
  let y : A.PowDomain k := PowDomain.mk A (fun i => A.resolvent c (applyL A k i x)) fun i =>
    ⟨hA.resolvent_apply_mem_domain hc'' _, by
      rw [← apply_applyL x i, hA.resolvent_apply_comm hc'']⟩
  refine ⟨y, ⟨snoc y (hA.resolvent_apply_mem_domain hc'' _), castL_snoc _ _⟩, ?_⟩
  rw [dist_comm] at hd
  exact hd

end PowDomain

/-! ### Symmetric and self-adjoint operators -/

section SelfAdjoint

variable [CompleteSpace H]

/-- **Remark 7, the easy direction**: a self-adjoint operator (`A† = A`) is symmetric,
`A.IsFormalAdjoint A` ([brezis2011functional] Chapter 7, Remark 7). -/
theorem _root_.IsSelfAdjoint.isFormalAdjoint_self (hA : IsSelfAdjoint A) :
    A.IsFormalAdjoint A := by
  have h := adjoint_isFormalAdjoint hA.dense_domain
  rwa [isSelfAdjoint_def.mp hA] at h

/-- **Remark 7**: a densely defined operator is symmetric iff `A ⊆ A†`, i.e. `D(A) ⊆ D(A†)` and
`A† = A` on `D(A)` ([brezis2011functional] Chapter 7, Remark 7). -/
theorem IsFormalAdjoint.le_adjoint_iff (hd : Dense (A.domain : Set H)) :
    A.IsFormalAdjoint A ↔ A ≤ A† := by
  refine ⟨fun h => h.le_adjoint hd, fun h x y => ?_⟩
  rw [apply_comp_inclusion h x]
  exact adjoint_isFormalAdjoint hd _ y

/-- **The resolvent of a symmetric maximal monotone operator is self-adjoint**: with
`u₁ = J_c u`, `v₁ = J_c v`, `⟪u₁, v⟫ = ⟪u₁, v₁ + c A v₁⟫ = ⟪u₁ + c A u₁, v₁⟫ = ⟪u, v₁⟫`
([brezis2011functional], proof of Proposition 7.6, and proof of Theorem 7.7, `J_λ^* = J_λ`). -/
theorem IsMaximalMonotone.isSelfAdjoint_resolvent (hA : A.IsMaximalMonotone)
    (hs : A.IsFormalAdjoint A) {c : ℝ} (hc : 0 < c) : IsSelfAdjoint (A.resolvent c) := by
  refine LinearMap.IsSymmetric.isSelfAdjoint fun u v => ?_
  simp only [ContinuousLinearMap.coe_coe]
  set u₁ : A.domain := ⟨A.resolvent c u, hA.resolvent_apply_mem_domain hc u⟩
  set v₁ : A.domain := ⟨A.resolvent c v, hA.resolvent_apply_mem_domain hc v⟩
  have hu : (u₁ : H) + (c : 𝕜) • A u₁ = u := hA.resolvent_add_smul_apply hc u
  have hv : (v₁ : H) + (c : 𝕜) • A v₁ = v := hA.resolvent_add_smul_apply hc v
  calc ⟪(u₁ : H), v⟫ = ⟪(u₁ : H), (v₁ : H) + (c : 𝕜) • A v₁⟫ := by rw [hv]
    _ = ⟪(u₁ : H), v₁⟫ + (c : 𝕜) * ⟪(u₁ : H), A v₁⟫ := by
        rw [inner_add_right, inner_smul_right]
    _ = ⟪(u₁ : H), v₁⟫ + (c : 𝕜) * ⟪A u₁, (v₁ : H)⟫ := by rw [hs u₁ v₁]
    _ = ⟪(u₁ : H) + (c : 𝕜) • A u₁, (v₁ : H)⟫ := by
        rw [inner_add_left, inner_smul_left, conj_ofReal]
    _ = ⟪u, v₁⟫ := by rw [hu]

/-- **The Yosida approximation of a symmetric maximal monotone operator is self-adjoint**
([brezis2011functional], proof of Theorem 7.7, `A_λ^* = A_λ`). -/
theorem IsMaximalMonotone.isSelfAdjoint_yosida (hA : A.IsMaximalMonotone)
    (hs : A.IsFormalAdjoint A) {c : ℝ} (hc : 0 < c) : IsSelfAdjoint (A.yosida c) := by
  have hJ : ∀ u v, ⟪A.resolvent c u, v⟫ = ⟪u, A.resolvent c v⟫ := fun u v =>
    (hA.isSelfAdjoint_resolvent hs hc).isSymmetric u v
  refine LinearMap.IsSymmetric.isSelfAdjoint fun u v => ?_
  simp only [ContinuousLinearMap.coe_coe, yosida_apply, inner_smul_left, inner_smul_right,
    inner_sub_left, inner_sub_right, conj_ofReal]
  rw [hJ u v]

/-- **Proposition 7.6**: a symmetric maximal monotone operator is self-adjoint. `A ⊆ A†` holds
for every symmetric operator; conversely for `u ∈ D(A†)` and `f = u + A† u`, one has
`⟪f, J_1 w⟫ = ⟪u, w⟫` for every `w`, so `u = J_1 f ∈ D(A)` by the self-adjointness of `J_1`
([brezis2011functional] Proposition 7.6). -/
theorem IsMaximalMonotone.isSelfAdjoint_of_isFormalAdjoint (hA : A.IsMaximalMonotone)
    (hs : A.IsFormalAdjoint A) : IsSelfAdjoint A := by
  have hd := hA.dense_domain
  have hle : A ≤ A† := hs.le_adjoint hd
  rw [isSelfAdjoint_def]
  refine (eq_of_le_of_domain_eq hle (le_antisymm hle.1 fun u hu => ?_)).symm
  set f : H := u + A† ⟨u, hu⟩ with hf
  have hJ : ∀ x y, ⟪A.resolvent 1 x, y⟫ = ⟪x, A.resolvent 1 y⟫ := fun x y =>
    (hA.isSelfAdjoint_resolvent hs one_pos).isSymmetric x y
  have key : A.resolvent 1 f = u := by
    refine ext_inner_right 𝕜 fun w => ?_
    rw [hJ]
    set w₁ : A.domain := ⟨A.resolvent 1 w, hA.resolvent_apply_mem_domain one_pos w⟩
    have hw : (w₁ : H) + A w₁ = w := by
      have := hA.resolvent_add_smul_apply one_pos w
      rwa [ofReal_one, one_smul] at this
    calc ⟪f, (w₁ : H)⟫ = ⟪u, (w₁ : H)⟫ + ⟪A† ⟨u, hu⟩, (w₁ : H)⟫ := by rw [hf, inner_add_left]
      _ = ⟪u, (w₁ : H)⟫ + ⟪u, A w₁⟫ := by rw [adjoint_isFormalAdjoint hd ⟨u, hu⟩ w₁]
      _ = ⟪u, (w₁ : H) + A w₁⟫ := by rw [inner_add_right]
      _ = ⟪u, w⟫ := by rw [hw]
  rw [← key]
  exact hA.resolvent_apply_mem_domain one_pos f

end SelfAdjoint

/-! ### Remark 8: maximal monotonicity and the adjoint -/

section Adjoint

variable [CompleteSpace H]

/-- **The adjoint of a maximal monotone operator is monotone** ([brezis2011functional]
Chapter 7, Remark 8): for `v ∈ D(A†)`, `re ⟪A† v, J_c v⟫ = re ⟪v, A (J_c v)⟫ = re ⟪A_c v, v⟫ ≥ 0`,
and `J_c v → v` as `c → 0⁺`. -/
theorem IsMaximalMonotone.isMonotone_adjoint (hA : A.IsMaximalMonotone) : A†.IsMonotone := by
  intro v
  have hd := hA.dense_domain
  have h1 : Tendsto (fun c : ℝ => re ⟪A† v, A.resolvent c v⟫) (𝓝[>] 0)
      (𝓝 (re ⟪A† v, (v : H)⟫)) :=
    (continuous_re.tendsto _).comp (tendsto_const_nhds.inner (hA.tendsto_resolvent_apply v))
  refine ge_of_tendsto h1 ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  rw [show ⟪A† v, A.resolvent c v⟫ =
      ⟪(v : H), A ⟨A.resolvent c v, hA.resolvent_apply_mem_domain hc v⟩⟫ from
      adjoint_isFormalAdjoint hd v ⟨_, _⟩, ← hA.yosida_apply_eq_apply_resolvent hc, inner_re_symm]
  exact hA.re_inner_yosida_nonneg hc v

/-- **The adjoint of `I + A` is `I + A†`**, for a densely defined `A`: both domains are the set of
`y` with `x ↦ ⟪y, A x⟫` continuous on `D(A)`, and `⟪y + A† y, x⟫ = ⟪y, x + A x⟫`
([brezis2011functional] Chapter 7, Remark 8). -/
theorem adjoint_id_vadd (hd : Dense (A.domain : Set H)) :
    ((LinearMap.id : H →ₗ[𝕜] H) +ᵥ A)† = (LinearMap.id : H →ₗ[𝕜] H) +ᵥ A† := by
  have hd' : Dense ((((LinearMap.id : H →ₗ[𝕜] H) +ᵥ A).domain : Submodule 𝕜 H) : Set H) := hd
  have hdom : ((LinearMap.id : H →ₗ[𝕜] H) +ᵥ A)†.domain = A†.domain := by
    ext y
    rw [mem_adjoint_domain_iff, mem_adjoint_domain_iff]
    have hc : Continuous ((innerₛₗ 𝕜 y).comp A.domain.subtype) :=
      ((innerSL 𝕜 y).comp A.domain.subtypeL).continuous
    have heq : ((innerₛₗ 𝕜 y).comp ((LinearMap.id : H →ₗ[𝕜] H) +ᵥ A).toFun :
        A.domain →ₗ[𝕜] 𝕜) = (innerₛₗ 𝕜 y).comp A.domain.subtype + (innerₛₗ 𝕜 y).comp A.toFun := by
      ext x
      simp [inner_add_right]
    rw [heq, LinearMap.coe_add]
    exact ⟨fun h => by simpa using h.sub hc, fun h => hc.add h⟩
  refine LinearPMap.ext hdom fun x hx hx' => ?_
  refine adjoint_apply_eq hd' ⟨x, hx⟩ fun z => ?_
  rw [vadd_apply, vadd_apply, LinearMap.id_apply, LinearMap.id_apply, inner_add_left,
    inner_add_right, adjoint_isFormalAdjoint hd ⟨x, hx'⟩ z]

/-- **Remark 8, `⇒`**: the adjoint of a maximal monotone operator is maximal monotone
([brezis2011functional] Chapter 7, Remark 8). For `f ∈ H`, `u = J_1^* f` satisfies
`⟪u, v + A v⟫ = ⟪f, J_1 (v + A v)⟫ = ⟪f, v⟫` for all `v ∈ D(A)`, so `u ∈ D(A†)` with
`A† u = f - u`. -/
theorem IsMaximalMonotone.adjoint (hA : A.IsMaximalMonotone) : A†.IsMaximalMonotone := by
  refine ⟨hA.isMonotone_adjoint, fun f => ?_⟩
  have hd := hA.dense_domain
  set u := ContinuousLinearMap.adjoint (A.resolvent 1) f with hu
  have key : ∀ v : A.domain, ⟪u, (v : H) + A v⟫ = ⟪f, v⟫ := fun v => by
    rw [hu, ContinuousLinearMap.adjoint_inner_left]
    congr 1
    have := hA.resolvent_apply_add_smul one_pos v
    rwa [ofReal_one, one_smul] at this
  have hsub : ∀ v : A.domain, ⟪f - u, (v : H)⟫ = ⟪u, A v⟫ := fun v => by
    rw [inner_sub_left, ← key v, inner_add_right]
    abel
  have hmem : u ∈ A†.domain := mem_adjoint_domain_of_exists u ⟨f - u, hsub⟩
  refine ⟨⟨u, hmem⟩, ?_⟩
  rw [adjoint_apply_eq hd ⟨u, hmem⟩ hsub]
  abel

/-- **Remark 8, second equivalence**: `A` is maximal monotone iff `A` is closed, densely defined,
and both `A` and `A†` are monotone ([brezis2011functional] Chapter 7, Remark 8; the Hilbert case
of the book's Problem 16). For `⇐`, `R(I + A)` is closed because `I + A` is closed and bounded
below (`‖u‖ ≤ ‖u + A u‖`), and `R(I + A)ᗮ = 0` because `w ⊥ R(I + A)` forces `w ∈ D(A†)` with
`A† w = -w`, whence `0 ≤ re ⟪A† w, w⟫ = -‖w‖²`. -/
theorem isMaximalMonotone_iff_isClosed_dense_isMonotone :
    A.IsMaximalMonotone ↔
      A.IsClosed ∧ Dense (A.domain : Set H) ∧ A.IsMonotone ∧ A†.IsMonotone := by
  refine ⟨fun hA => ⟨hA.isClosed, hA.dense_domain, hA.isMonotone, hA.isMonotone_adjoint⟩, ?_⟩
  rintro ⟨hcl, hd, hm, hm'⟩
  set B : H →ₗ.[𝕜] H := (LinearMap.id : H →ₗ[𝕜] H) +ᵥ A with hB
  -- `I + A` is closed
  have hBcl : B.IsClosed := by
    have hA' : _root_.IsClosed (A.graph : Set (H × H)) := hcl
    have : (B.graph : Set (H × H)) =
        (fun p : H × H => (p.1, p.2 - p.1)) ⁻¹' (A.graph : Set (H × H)) := by
      ext ⟨x, y⟩
      simp only [SetLike.mem_coe, mem_graph_iff, Set.mem_preimage]
      constructor
      · rintro ⟨u, rfl, rfl⟩
        exact ⟨u, rfl, by change A u = (u : H) + A u - u; abel⟩
      · rintro ⟨u, hu, hAu⟩
        exact ⟨u, hu, by change (u : H) + A u = y; rw [hAu, hu]; abel⟩
    change _root_.IsClosed (B.graph : Set (H × H))
    rw [this]
    exact hA'.preimage (continuous_fst.prodMk (continuous_snd.sub continuous_fst))
  -- `R(I + A)` is closed
  have hrange : _root_.IsClosed (LinearMap.range B.toFun : Set H) :=
    hBcl.isClosed_range_of_norm_le (C := 1) fun u => by
      rw [one_mul]
      have := hm.norm_le_norm_add_smul zero_le_one u
      rwa [ofReal_one, one_smul] at this
  -- `R(I + A)ᗮ = 0`
  have horth : (LinearMap.range B.toFun)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    rw [Submodule.mem_orthogonal] at hw
    have hw' : ∀ v : A.domain, ⟪(-w : H), (v : H)⟫ = ⟪w, A v⟫ := fun v => by
      have h1 : ⟪(v : H) + A v, w⟫ = 0 := hw (B v) ⟨v, rfl⟩
      have h2 : ⟪w, (v : H)⟫ + ⟪w, A v⟫ = 0 := by
        rw [← inner_conj_symm w (v : H), ← inner_conj_symm w (A v), ← _root_.map_add,
          ← inner_add_left, h1, _root_.map_zero]
      rw [inner_neg_left]
      exact neg_eq_of_add_eq_zero_right h2
    have hmem : w ∈ A†.domain := mem_adjoint_domain_of_exists w ⟨-w, hw'⟩
    have hval : A† ⟨w, hmem⟩ = -w := adjoint_apply_eq hd ⟨w, hmem⟩ hw'
    have := hm' ⟨w, hmem⟩
    rw [hval, inner_neg_left, _root_.map_neg, inner_self_eq_norm_sq] at this
    have h0 : ‖w‖ ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0)
  have htop : LinearMap.range B.toFun = ⊤ := by
    have : CompleteSpace (LinearMap.range B.toFun) := hrange.completeSpace_coe
    exact Submodule.orthogonal_eq_bot_iff.1 horth
  exact IsMaximalMonotone.of_range_id_vadd_eq_top hm htop

/-- **Remark 8, first equivalence**: for a closed, densely defined `A` whose adjoint is densely
defined, `A` is maximal monotone iff `A†` is ([brezis2011functional] Chapter 7, Remark 8). For
`⇐`, `A ⊆ A††` and `A††` is monotone, so `A` is monotone, and the second equivalence applies. -/
theorem isMaximalMonotone_iff_adjoint (hcl : A.IsClosed) (hd : Dense (A.domain : Set H))
    (hd' : Dense (A†.domain : Set H)) : A.IsMaximalMonotone ↔ A†.IsMaximalMonotone := by
  refine ⟨fun hA => hA.adjoint, fun hA => ?_⟩
  rw [isMaximalMonotone_iff_isClosed_dense_isMonotone]
  refine ⟨hcl, hd, ?_, hA.isMonotone⟩
  have hle : A ≤ A†† := (adjoint_isFormalAdjoint hd).le_adjoint hd'
  have hm := hA.isMonotone_adjoint
  intro v
  rw [apply_comp_inclusion hle v]
  exact hm (Submodule.inclusion hle.1 v)

/-- **The double adjoint of a closed operator**: for a closed, densely defined `A` whose adjoint is
densely defined, `A†† = A`. Through graphs: `A††.graph` is the "adjoint" of the adjoint of the
closed subspace `A.graph` of the Hilbert space `WithLp 2 (H × H)`, and a closed subspace is its
own double orthogonal ([brezis2011functional] Chapter 7, Remark 8, and the definition of the
adjoint in §2.6). -/
theorem adjoint_adjoint (hcl : A.IsClosed) (hd : Dense (A.domain : Set H))
    (hd' : Dense (A†.domain : Set H)) : A†† = A := by
  refine eq_of_eq_graph ?_
  rw [adjoint_graph_eq_graph_adjoint hd', adjoint_graph_eq_graph_adjoint hd]
  refine le_antisymm (fun p hp => ?_) (fun p hp => ?_)
  · rw [Submodule.mem_adjoint_iff] at hp
    by_contra hpg
    have hA' : _root_.IsClosed (A.graph : Set (H × H)) := hcl
    -- the graph, transported to the Hilbert space `WithLp 2 (H × H)`
    set K : Submodule 𝕜 (WithLp 2 (H × H)) :=
      A.graph.map (WithLp.linearEquiv 2 𝕜 (H × H)).symm.toLinearMap with hK
    have hKmem : ∀ x, x ∈ K ↔ ofLp x ∈ A.graph := fun x => by
      rw [hK, Submodule.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨ofLp x, hx, rfl⟩
    have hKcl : _root_.IsClosed (K : Set (WithLp 2 (H × H))) := by
      have : (K : Set (WithLp 2 (H × H))) = ofLp ⁻¹' (A.graph : Set (H × H)) := by
        ext x
        exact hKmem x
      rw [this]
      exact hA'.preimage (WithLp.prod_continuous_ofLp _ _ _)
    have : CompleteSpace K := hKcl.completeSpace_coe
    have hpK : toLp 2 p ∉ K := fun h => hpg ((hKmem _).1 h)
    rw [← Submodule.orthogonal_orthogonal K] at hpK
    have hne : ¬ ∀ u ∈ Kᗮ, ⟪u, toLp 2 p⟫ = 0 := fun h => hpK ((Submodule.mem_orthogonal _ _).2 h)
    simp only [not_forall, exists_prop] at hne
    obtain ⟨q, hqK, hq⟩ := hne
    -- `(q₂, -q₁)` lies in the adjoint of the graph
    have hq' : ((ofLp q).2, -(ofLp q).1) ∈ A.graph.adjoint := by
      rw [Submodule.mem_adjoint_iff]
      intro a b hab
      have h1 := (Submodule.mem_orthogonal _ _).1 hqK (toLp 2 (a, b)) ((hKmem _).2 hab)
      rw [WithLp.prod_inner_apply] at h1
      rw [inner_neg_right]
      linear_combination h1
    have h2 := hp _ _ hq'
    apply hq
    rw [WithLp.prod_inner_apply]
    rw [inner_neg_left] at h2
    linear_combination -h2
  · rw [Submodule.mem_adjoint_iff]
    intro a b hab
    rw [Submodule.mem_adjoint_iff] at hab
    have h1 := hab p.1 p.2 hp
    have h2 : ⟪p.1, b⟫ - ⟪p.2, a⟫ = 0 := by linear_combination -h1
    rw [← inner_conj_symm b, ← inner_conj_symm a, ← _root_.map_sub, h2, _root_.map_zero]

end Adjoint

end LinearPMap

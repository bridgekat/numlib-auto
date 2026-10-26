import Numlib.Analysis.Calculus.MultivariateTaylor.Peano
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Curve-based necessary optimality conditions of arbitrary order

Along a polynomial arc `α ↦ x + ∑_{i=1}^{q} α^i s_i (+ o(α^q))`, the Taylor expansion of a smooth
function `f` in powers of `α` has, for `j ≥ 1`, the coefficient
`c_j = ∑_{k=1}^{j} (1/k!) ∑_{(ℓ_1,…,ℓ_k) ∈ P(j,k)} ∇^k f(x)[s_{ℓ_1},…,s_{ℓ_k}]`
([cartis2022evaluation], (12.1.6)), where `P(j,k)` is the set of `k`-tuples of positive integers
summing to `j` ((12.1.5)). A local minimizer has `c_j ≥ 0` as soon as `c_1 = ⋯ = c_{j-1} = 0`
along every arc staying in the feasible set (Theorems 12.1.1 and 14.3.1).

## Main definitions

* `Optimization.curveIndexSet j k`: the index set `P(j,k)` of (12.1.5).
* `Optimization.curveCoeff D s j`: the coefficient `c_j` (12.1.6) for derivative data `D` (exact
  data being `ftaylorSeries ℝ f x`), with values in any normed space.
* `Optimization.IsCurveCritical D q`: the conclusion of Theorem 12.1.1 for all orders `j ≤ q`
  (the book's "`q`-th order minimizer").
* `Optimization.IsFeasibleArc K x j s`: some arc `x + ∑_{ℓ ≤ j} α^ℓ s_ℓ + o(α^j)` stays in `K` for
  small `α > 0` (the book's descriptor set `𝒟^j`).

## Main results

* `Optimization.taylorSum_polyCurve_eq`: the Taylor sum along a polynomial curve is a polynomial
  in `α` whose coefficients up to `α^q` are the `curveCoeff`.
* `Optimization.isLittleO_comp_curve_sub_curveCoeff`: the expansion
  `g(γ(α)) = g(x) + ∑_{i ≤ j} α^i c_i + o(α^j)` along an arc (Peano remainder plus algebra).
* `Optimization.nonneg_of_isLittleO_poly_of_le`, `Optimization.eq_zero_of_isLittleO_sum_pow`:
  one-dimensional sign and uniqueness tests for asymptotic expansions.
* `Optimization.IsLocalMin.isCurveCritical`: Theorem 12.1.1.
* `Optimization.curveCoeff_eq_zero_of_isFeasibleArc`: the constraint expansion (14.3.3).
* `Optimization.curveCoeff_lagrangian_nonneg_of_isLocalMinOn`: Theorem 14.3.1 (corrected).

## Implementation notes

`curveCoeff` is defined literally from `P(j,k)` (the tuples `ℓ : Fin k → ℕ` with entries in
`[1, j]` summing to `j`; these are the compositions of `j` into `k` parts). The book's restriction
to tuples of nonzero `s_i` is dropped: the conclusions hold for every tuple, which makes the
statements stronger (and tuples with zero entries give the classical ray conditions). No Faà di
Bruno formula is needed: the expansion along an arc follows from the Peano form of Taylor's
theorem and the algebra of `taylorSum_polyCurve_eq`.
-/

open Finset Filter Asymptotics
open scoped Nat Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

namespace Optimization

/-! ### The index sets `P(j,k)` -/

/-- The index set `P(j,k)` of [cartis2022evaluation], (12.1.5): the `k`-tuples
`(ℓ_1, …, ℓ_k)` of integers in `[1, j]` with `ℓ_1 + ⋯ + ℓ_k = j` (the compositions of `j` into
`k` positive parts). -/
def curveIndexSet (j k : ℕ) : Finset (Fin k → ℕ) :=
  {ℓ ∈ Fintype.piFinset fun _ => Icc 1 j | ∑ i, ℓ i = j}

theorem mem_curveIndexSet {j k : ℕ} {ℓ : Fin k → ℕ} :
    ℓ ∈ curveIndexSet j k ↔ (∀ i, ℓ i ∈ Icc 1 j) ∧ ∑ i, ℓ i = j := by
  simp [curveIndexSet, Fintype.mem_piFinset]

private theorem le_sum_of_fin {k : ℕ} (ℓ : Fin k → ℕ) (i : Fin k) : ℓ i ≤ ∑ i, ℓ i :=
  single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)

/-- A `k`-tuple of positive integers sums to at least `k`. -/
private theorem card_le_sum_of_one_le {k : ℕ} {ℓ : Fin k → ℕ} (h : ∀ i, 1 ≤ ℓ i) :
    k ≤ ∑ i, ℓ i := by
  simpa using sum_le_sum fun i (_ : i ∈ (univ : Finset (Fin k))) => h i

/-- `P(j,k)` is empty when `j < k`. -/
theorem curveIndexSet_eq_empty {j k : ℕ} (h : j < k) : curveIndexSet j k = ∅ := by
  refine eq_empty_of_forall_notMem fun ℓ hℓ => ?_
  rw [mem_curveIndexSet] at hℓ
  have := card_le_sum_of_one_le fun i => (mem_Icc.1 (hℓ.1 i)).1
  omega

/-- For `j ≤ q`, `P(j,k)` consists of the `k`-tuples with entries in `[1, q]` summing to `j`. -/
theorem curveIndexSet_eq_filter {j q k : ℕ} (hjq : j ≤ q) :
    curveIndexSet j k = {ℓ ∈ Fintype.piFinset fun _ : Fin k => Icc 1 q | ∑ i, ℓ i = j} := by
  ext ℓ
  simp only [mem_curveIndexSet, mem_filter, Fintype.mem_piFinset, mem_Icc]
  constructor
  · rintro ⟨h, hs⟩
    exact ⟨fun i => ⟨(h i).1, (h i).2.trans hjq⟩, hs⟩
  · rintro ⟨h, hs⟩
    exact ⟨fun i => ⟨(h i).1, hs ▸ le_sum_of_fin ℓ i⟩, hs⟩

/-! ### The curve coefficients -/

/-- The coefficient of `α^j` in the expansion of `f` along `x + ∑_i α^i s_i`
([cartis2022evaluation], (12.1.6)):
`curveCoeff D s j = ∑_{k=1}^{j} (1/k!) ∑_{ℓ ∈ P(j,k)} D_k[s_{ℓ_1}, …, s_{ℓ_k}]`, for derivative
data `D` (`D = ftaylorSeries ℝ f x` for exact derivatives). For `j = 0` it is `0`. -/
noncomputable def curveCoeff (D : FormalMultilinearSeries ℝ E F) (s : ℕ → E) (j : ℕ) : F :=
  ∑ k ∈ Icc 1 j, (k ! : ℝ)⁻¹ • ∑ ℓ ∈ curveIndexSet j k, D k fun i => s (ℓ i)

section CurveCoeff

variable (D D' : FormalMultilinearSeries ℝ E F) (s : ℕ → E)

theorem curveCoeff_def (j : ℕ) :
    curveCoeff D s j = ∑ k ∈ Icc 1 j, (k ! : ℝ)⁻¹ • ∑ ℓ ∈ curveIndexSet j k, D k fun i => s (ℓ i) :=
  rfl

@[simp]
theorem curveCoeff_zero : curveCoeff D s 0 = 0 := by
  simp [curveCoeff]

@[simp]
theorem curveCoeff_add (j : ℕ) :
    curveCoeff (D + D') s j = curveCoeff D s j + curveCoeff D' s j := by
  simp [curveCoeff, sum_add_distrib, smul_add]

@[simp]
theorem curveCoeff_smul (a : ℝ) (j : ℕ) : curveCoeff (a • D) s j = a • curveCoeff D s j := by
  simp [curveCoeff, smul_sum, smul_comm a]

@[simp]
theorem curveCoeff_neg (j : ℕ) : curveCoeff (-D) s j = -curveCoeff D s j := by
  simp [curveCoeff, sum_neg_distrib, smul_neg]

@[simp]
theorem curveCoeff_sub (j : ℕ) :
    curveCoeff (D - D') s j = curveCoeff D s j - curveCoeff D' s j := by
  simp [curveCoeff, sum_sub_distrib, smul_sub]

/-- The coefficients of data composed with a continuous linear map `L` are the images under `L`. -/
@[simp]
theorem curveCoeff_compFormalMultilinearSeries {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) (j : ℕ) :
    curveCoeff (L.compFormalMultilinearSeries D) s j = L (curveCoeff D s j) := by
  simp [curveCoeff, map_sum, map_smul]

/-- The first coefficient is `D_1[s_1]`. -/
theorem curveCoeff_one : curveCoeff D s 1 = D 1 fun _ => s 1 := by
  have : curveIndexSet 1 1 = {fun _ => 1} := by decide
  simp [curveCoeff, this]

/-- The second coefficient is `D_1[s_2] + ½ D_2[s_1, s_1]`. -/
theorem curveCoeff_two :
    curveCoeff D s 2 = (D 1 fun _ => s 2) + (2 : ℝ)⁻¹ • D 2 fun _ => s 1 := by
  have h1 : curveIndexSet 2 1 = {fun _ => 2} := by decide
  have h2 : curveIndexSet 2 2 = {fun _ => 1} := by decide
  have hI : Icc 1 2 = {1, 2} := by decide
  simp [curveCoeff, h1, h2, hI]

/-- Along a ray (`s_i = 0` for `i ≥ 2`) only the tuple `(1, …, 1)` contributes:
`c_j = (1/j!) D_j[s_1]^j` for `j ≥ 1`. -/
theorem curveCoeff_of_ray {j : ℕ} (hj : 1 ≤ j) (hs : ∀ i, 2 ≤ i → s i = 0) :
    curveCoeff D s j = (j ! : ℝ)⁻¹ • D j fun _ => s 1 := by
  -- every tuple other than `(1, …, 1)` has an entry `≥ 2`, hence a zero argument
  have hzero : ∀ k, ∀ ℓ ∈ curveIndexSet j k, ℓ ≠ (fun _ => 1) → (D k fun i => s (ℓ i)) = 0 := by
    intro k ℓ hℓ hne
    obtain ⟨i, hi⟩ : ∃ i, ℓ i ≠ 1 := by
      by_contra! h
      exact hne (funext h)
    have h1 := (mem_Icc.1 ((mem_curveIndexSet.1 hℓ).1 i)).1
    exact (D k).map_coord_zero i (hs _ (by omega))
  rw [curveCoeff, sum_eq_single_of_mem j (mem_Icc.2 ⟨hj, le_rfl⟩)]
  · rw [sum_eq_single_of_mem (fun _ => 1)]
    · rw [mem_curveIndexSet]
      exact ⟨fun _ => mem_Icc.2 ⟨le_rfl, hj⟩, by simp⟩
    · exact hzero j
  · intro k _ hkj
    rw [sum_eq_zero fun ℓ hℓ => hzero k ℓ hℓ ?_, smul_zero]
    rintro rfl
    exact hkj (by simpa using (mem_curveIndexSet.1 hℓ).2)

end CurveCoeff

/-! ### Expansion along a polynomial curve -/

section PolyCurve

variable (D : FormalMultilinearSeries ℝ E F) (s : ℕ → E)

/-- Multilinear expansion of `D_k[∑_{i=1}^q α^i s_i]^k` over all index tuples. -/
theorem apply_polyCurve_eq (q k : ℕ) (α : ℝ) :
    (D k fun _ => ∑ i ∈ Icc 1 q, α ^ i • s i) =
      ∑ ℓ ∈ Fintype.piFinset (fun _ : Fin k => Icc 1 q), α ^ (∑ i, ℓ i) • D k fun i => s (ℓ i) := by
  rw [(D k).map_sum_finset]
  refine sum_congr rfl fun ℓ _ => ?_
  rw [(D k).map_smul_univ (fun i => α ^ ℓ i), prod_pow_eq_pow_sum]

/-- **Expansion along a polynomial curve.** The Taylor sum `D.taylorSum q` evaluated at
`∑_{i=1}^q α^i s_i` is `D_0 + ∑_{j=1}^q α^j c_j + α^{q+1} R(α)` with `c_j = curveCoeff D s j`
and a continuous (polynomial) remainder `R`. -/
theorem taylorSum_polyCurve_eq (q : ℕ) :
    ∃ R : ℝ → F, Continuous R ∧ ∀ α : ℝ,
      D.taylorSum q (∑ i ∈ Icc 1 q, α ^ i • s i) =
        D 0 0 + ∑ j ∈ Icc 1 q, α ^ j • curveCoeff D s j + α ^ (q + 1) • R α := by
  classical
  let A : (k : ℕ) → Finset (Fin k → ℕ) := fun k => Fintype.piFinset fun _ : Fin k => Icc 1 q
  refine ⟨fun α => ∑ k ∈ Icc 1 q, (k ! : ℝ)⁻¹ • ∑ ℓ ∈ A k with q < ∑ i, ℓ i,
    α ^ (∑ i, ℓ i - (q + 1)) • D k fun i => s (ℓ i), ?_, fun α => ?_⟩
  · fun_prop
  rw [D.taylorSum_eq_add, add_assoc]
  congr 1
  -- split each inner sum into total degree `≤ q` and `> q`
  have hsplit : ∀ k, ∑ ℓ ∈ A k, α ^ (∑ i, ℓ i) • (D k fun i => s (ℓ i)) =
      ∑ ℓ ∈ A k with ∑ i, ℓ i ≤ q, α ^ (∑ i, ℓ i) • (D k fun i => s (ℓ i)) +
        ∑ ℓ ∈ A k with q < ∑ i, ℓ i, α ^ (∑ i, ℓ i) • (D k fun i => s (ℓ i)) := by
    intro k
    rw [← sum_filter_add_sum_filter_not (A k) (fun ℓ => ∑ i, ℓ i ≤ q)]
    simp only [not_le]
  -- the low-degree part, grouped by total degree
  have hlow : ∀ k ∈ Icc 1 q,
      ∑ ℓ ∈ A k with ∑ i, ℓ i ≤ q, α ^ (∑ i, ℓ i) • (D k fun i => s (ℓ i)) =
        ∑ j ∈ Icc 1 q, α ^ j • ∑ ℓ ∈ curveIndexSet j k, D k fun i => s (ℓ i) := by
    intro k hk
    rw [← sum_fiberwise_of_maps_to (g := fun ℓ : Fin k → ℕ => ∑ i, ℓ i) (t := Icc 1 q)]
    · refine sum_congr rfl fun j hj => ?_
      rw [curveIndexSet_eq_filter (mem_Icc.1 hj).2, filter_filter, smul_sum]
      refine sum_congr ?_ fun ℓ hℓ => ?_
      · ext ℓ
        simp only [mem_filter]
        constructor
        · rintro ⟨h1, -, h3⟩
          exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩
          exact ⟨h1, h3 ▸ (mem_Icc.1 hj).2, h3⟩
      · rw [(mem_filter.1 hℓ).2]
    · intro ℓ hℓ
      rw [mem_filter, Fintype.mem_piFinset] at hℓ
      refine mem_Icc.2 ⟨?_, hℓ.2⟩
      have := card_le_sum_of_one_le fun i => (mem_Icc.1 (hℓ.1 i)).1
      have := (mem_Icc.1 hk).1
      omega
  rw [sum_congr rfl fun k hk => by rw [apply_polyCurve_eq, hsplit, hlow k hk]]
  simp_rw [smul_add, sum_add_distrib]
  congr 1
  · rw [sum_congr rfl fun k _ => smul_sum, sum_comm]
    refine sum_congr rfl fun j hj => ?_
    rw [curveCoeff, smul_sum]
    symm
    rw [sum_congr rfl fun k _ => smul_comm _ _ _]
    refine sum_subset (Icc_subset_Icc_right (mem_Icc.1 hj).2) fun k hk hkj => ?_
    have : j < k := by
      simp only [mem_Icc, not_and, not_le] at hk hkj
      exact hkj hk.1
    simp [curveIndexSet_eq_empty this]
  · simp only [smul_sum, smul_smul]
    refine sum_congr rfl fun k _ => sum_congr rfl fun ℓ hℓ => ?_
    have h := (mem_filter.1 hℓ).2
    have : α ^ (∑ i, ℓ i) = α ^ (q + 1) * α ^ (∑ i, ℓ i - (q + 1)) := by
      rw [← pow_add]
      congr 1
      omega
    rw [this]
    congr 1
    ring

end PolyCurve

/-! ### Expansion along an arc -/

section Arc

/-- The polynomial part `∑_{ℓ=1}^j α^ℓ s_ℓ` of an arc tends to `0` as `α → 0`. -/
theorem tendsto_polyCurve_zero (s : ℕ → E) (j : ℕ) :
    Tendsto (fun α : ℝ => ∑ ℓ ∈ Icc 1 j, α ^ ℓ • s ℓ) (𝓝 0) (𝓝 0) := by
  have hc : Continuous fun α : ℝ => ∑ ℓ ∈ Icc 1 j, α ^ ℓ • s ℓ := by fun_prop
  have h0 : (∑ ℓ ∈ Icc 1 j, (0 : ℝ) ^ ℓ • s ℓ) = 0 :=
    sum_eq_zero fun ℓ hℓ => by rw [zero_pow (by have := (mem_Icc.1 hℓ).1; omega), zero_smul]
  simpa [h0] using hc.tendsto 0

/-- The polynomial part of an arc is `O(α)`. -/
theorem polyCurve_isBigO (s : ℕ → E) (j : ℕ) :
    (fun α : ℝ => ∑ ℓ ∈ Icc 1 j, α ^ ℓ • s ℓ) =O[𝓝 0] fun α => α := by
  have hd : Differentiable ℝ fun α : ℝ => ∑ ℓ ∈ Icc 1 j, α ^ ℓ • s ℓ := by fun_prop
  have h0 : (∑ ℓ ∈ Icc 1 j, (0 : ℝ) ^ ℓ • s ℓ) = 0 :=
    sum_eq_zero fun ℓ hℓ => by rw [zero_pow (by have := (mem_Icc.1 hℓ).1; omega), zero_smul]
  simpa [h0] using (hd 0).hasFDerivAt.isBigO_sub

/-- `α^j = O(α^i)` as `α → 0` for `i ≤ j`. -/
private theorem pow_isBigO_pow_of_le {i j : ℕ} (h : i ≤ j) :
    (fun α : ℝ => α ^ j) =O[𝓝 0] fun α => α ^ i := by
  rcases h.eq_or_lt with rfl | h
  · exact isBigO_refl _ _
  · exact (isLittleO_pow_pow h).isBigO

variable {s : ℕ → E} {x : E} {j : ℕ} {γ : ℝ → E}

/-- An arc `γ(α) = x + ∑_{ℓ=1}^j α^ℓ s_ℓ + o(α^j)` tends to `x` as `α → 0⁺`. -/
theorem tendsto_of_isLittleO_curve
    (hγ : (fun α => γ α - (x + ∑ ℓ ∈ Icc 1 j, α ^ ℓ • s ℓ)) =o[𝓝[>] 0] fun α => α ^ j) :
    Tendsto γ (𝓝[>] 0) (𝓝 x) := by
  have hpow : (fun α : ℝ => α ^ j) =O[𝓝[>] 0] fun _ => (1 : ℝ) :=
    (((continuous_pow j).tendsto 0).isBigO_one ℝ).mono nhdsWithin_le_nhds
  have he := isLittleO_one_iff ℝ |>.1 (hγ.trans_isBigO hpow)
  have hh := (tendsto_polyCurve_zero s j).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have := (he.add hh).const_add x
  simp only [add_zero] at this
  refine this.congr fun α => ?_
  abel

/-- An arc `γ(α) = x + ∑_{ℓ=1}^j α^ℓ s_ℓ + o(α^j)` with `j ≥ 1` satisfies `γ(α) - x = O(α)`. -/
theorem sub_isBigO_of_isLittleO_curve (hj : 1 ≤ j)
    (hγ : (fun α => γ α - (x + ∑ ℓ ∈ Icc 1 j, α ^ ℓ • s ℓ)) =o[𝓝[>] 0] fun α => α ^ j) :
    (fun α => γ α - x) =O[𝓝[>] 0] fun α => α := by
  have he : (fun α => γ α - (x + ∑ ℓ ∈ Icc 1 j, α ^ ℓ • s ℓ)) =O[𝓝[>] 0] fun α => α :=
    hγ.isBigO.trans (by simpa using (pow_isBigO_pow_of_le hj).mono nhdsWithin_le_nhds)
  refine (he.add ((polyCurve_isBigO s j).mono nhdsWithin_le_nhds)).congr_left fun α => ?_
  abel

/-- **Expansion along an arc.** If `g` is `C^j` at `x` and
`γ(α) = x + ∑_{ℓ=1}^j α^ℓ s_ℓ + o(α^j)` as `α → 0⁺`, then
`g(γ(α)) = g(x) + ∑_{i=1}^j α^i c_i + o(α^j)`, with `c_i = curveCoeff (ftaylorSeries ℝ g x) s i`
([cartis2022evaluation], Section 12.1.2 and (14.3.3), "collecting terms of equal degree in α"). -/
theorem isLittleO_comp_curve_sub_curveCoeff {g : E → F} (hg : ContDiffAt ℝ j g x)
    (hγ : (fun α => γ α - (x + ∑ ℓ ∈ Icc 1 j, α ^ ℓ • s ℓ)) =o[𝓝[>] 0] fun α => α ^ j) :
    (fun α => g (γ α) - g x - ∑ i ∈ Icc 1 j, α ^ i • curveCoeff (ftaylorSeries ℝ g x) s i)
      =o[𝓝[>] 0] fun α => α ^ j := by
  set h : ℝ → E := fun α => ∑ ℓ ∈ Icc 1 j, α ^ ℓ • s ℓ with hh_def
  set u : ℝ → E := fun α => γ α - x with hu_def
  set T := taylorPolynomial g j x with hT
  have hu : Tendsto u (𝓝[>] 0) (𝓝 0) := by
    have := (tendsto_of_isLittleO_curve hγ).sub_const x
    simpa [hu_def] using this
  have hh : Tendsto h (𝓝[>] 0) (𝓝 0) :=
    (tendsto_polyCurve_zero s j).mono_left nhdsWithin_le_nhds
  -- Peano remainder along the arc
  have h1 : (fun α => g (x + u α) - T (u α)) =o[𝓝[>] 0] fun α => α ^ j := by
    have hP := (sub_taylorPolynomial_isLittleO hg).comp_tendsto hu
    refine hP.trans_isBigO ?_
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp only [pow_zero]
      exact isBigO_refl _ _
    · change (fun α => ‖γ α - x‖ ^ j) =O[𝓝[>] 0] fun α => α ^ j
      exact ((sub_isBigO_of_isLittleO_curve hj hγ).norm_left).pow j
  -- the Taylor polynomial is locally Lipschitz, which absorbs the `o(α^j)` part of the arc
  have h2 : (fun α => T (u α) - T (h α)) =o[𝓝[>] 0] fun α => α ^ j := by
    have hS : HasStrictFDerivAt T (fderiv ℝ T 0) 0 :=
      ((contDiff_taylorPolynomial g j x (n := 1)).contDiffAt).hasStrictFDerivAt one_ne_zero
    have hO := hS.isBigO_sub.comp_tendsto (hu.prodMk_nhds hh)
    refine hO.trans_isLittleO ?_
    refine hγ.congr_left fun α => ?_
    simp only [Function.comp_apply, hu_def, hh_def]
    abel
  -- the algebraic expansion of the Taylor polynomial along the polynomial curve
  obtain ⟨R, hRc, hR⟩ := taylorSum_polyCurve_eq (ftaylorSeries ℝ g x) s j
  have h3 : (fun α => T (h α) - g x - ∑ i ∈ Icc 1 j, α ^ i • curveCoeff (ftaylorSeries ℝ g x) s i)
      =o[𝓝[>] 0] fun α => α ^ j := by
    have hR1 : R =O[𝓝 0] fun _ => (1 : ℝ) := (hRc.tendsto 0).isBigO_one ℝ
    have : (fun α : ℝ => α ^ (j + 1) • R α) =o[𝓝 0] fun α => α ^ j := by
      have := (isBigO_refl (fun α : ℝ => α ^ (j + 1)) (𝓝 0)).smul hR1
      simp only [smul_eq_mul, mul_one] at this
      exact this.trans_isLittleO (isLittleO_pow_pow (Nat.lt_succ_self j))
    refine (this.mono nhdsWithin_le_nhds).congr_left fun α => ?_
    rw [hT, taylorPolynomial_eq_taylorSum, hh_def, hR α]
    simp only [ftaylorSeries, iteratedFDeriv_zero_apply]
    abel
  refine ((h1.add h2).add h3).congr_left fun α => ?_
  simp only [hu_def]
  rw [add_sub_cancel]
  abel

end Arc

/-! ### One-dimensional tests -/

section OneDim

/-- If `α^n • w = o(α^n)` as `α → 0⁺`, then `w = 0`. -/
theorem eq_zero_of_isLittleO_pow_smul {n : ℕ} {w : F}
    (h : (fun α : ℝ => α ^ n • w) =o[𝓝[>] 0] fun α => α ^ n) : w = 0 := by
  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_)
  obtain ⟨α, hα, hαpos⟩ :=
    ((isLittleO_iff.1 h hε).and self_mem_nhdsWithin).exists
  have hpos : 0 < ‖α ^ n‖ := norm_pos_iff.2 (pow_ne_zero _ (ne_of_gt hαpos))
  rw [norm_smul, mul_comm ‖α ^ n‖] at hα
  simpa using le_of_mul_le_mul_right hα hpos

/-- **Uniqueness of asymptotic expansions.** If `∑_{i=1}^j α^i • v_i = o(α^j)` as `α → 0⁺`, then
`v_i = 0` for all `i ∈ [1, j]`. -/
theorem eq_zero_of_isLittleO_sum_pow {j : ℕ} {v : ℕ → F}
    (h : (fun α : ℝ => ∑ i ∈ Icc 1 j, α ^ i • v i) =o[𝓝[>] 0] fun α => α ^ j) :
    ∀ i ∈ Icc 1 j, v i = 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hsplit : ∀ α : ℝ, ∑ i ∈ Icc 1 (j + 1), α ^ i • v i =
        ∑ i ∈ Icc 1 j, α ^ i • v i + α ^ (j + 1) • v (j + 1) := fun α => by
      rw [sum_Icc_succ_top (by omega)]
    have hlo : (fun α : ℝ => α ^ (j + 1)) =o[𝓝[>] 0] fun α => α ^ j :=
      (isLittleO_pow_pow (Nat.lt_succ_self j)).mono nhdsWithin_le_nhds
    have hlast : (fun α : ℝ => α ^ (j + 1) • v (j + 1)) =O[𝓝[>] 0] fun α => α ^ (j + 1) :=
      isBigO_iff.2 ⟨‖v (j + 1)‖, Eventually.of_forall fun α => by rw [norm_smul, mul_comm]⟩
    have hlow : ∀ i ∈ Icc 1 j, v i = 0 := by
      refine ih ((h.trans hlo).sub (hlast.trans_isLittleO hlo) |>.congr_left fun α => ?_)
      rw [hsplit]
      abel
    intro i hi
    rcases (mem_Icc.1 hi).2.lt_or_eq with hij | rfl
    · exact hlow i (mem_Icc.2 ⟨(mem_Icc.1 hi).1, Nat.lt_succ_iff.1 hij⟩)
    · refine eq_zero_of_isLittleO_pow_smul (h.congr_left fun α => ?_)
      rw [hsplit, sum_eq_zero fun i hi => by rw [hlow i hi, smul_zero], zero_add]

/-- **First-nonvanishing-coefficient test.** Let `j ≥ 1` and
`ψ(α) = ψ₀ + ∑_{i=1}^j α^i a_i + o(α^j)` as `α → 0⁺` with `a_1 = ⋯ = a_{j-1} = 0`. If
`ψ₀ ≤ ψ(α)` for all small `α > 0`, then `0 ≤ a_j`. -/
theorem nonneg_of_isLittleO_poly_of_le {ψ : ℝ → ℝ} {ψ₀ : ℝ} {a : ℕ → ℝ} {j : ℕ} (hj : 1 ≤ j)
    (h : (fun α => ψ α - ψ₀ - ∑ i ∈ Icc 1 j, α ^ i • a i) =o[𝓝[>] 0] fun α => α ^ j)
    (hle : ∀ᶠ α in 𝓝[>] 0, ψ₀ ≤ ψ α) (hzero : ∀ i ∈ Ico 1 j, a i = 0) : 0 ≤ a j := by
  have hsum : ∀ α : ℝ, ∑ i ∈ Icc 1 j, α ^ i • a i = α ^ j • a j := fun α => by
    refine sum_eq_single_of_mem j (mem_Icc.2 ⟨hj, le_rfl⟩) fun i hi hij => ?_
    rw [hzero i (mem_Ico.2 ⟨(mem_Icc.1 hi).1, lt_of_le_of_ne (mem_Icc.1 hi).2 hij⟩), smul_zero]
  by_contra! hneg
  have hε : 0 < -a j / 2 := by linarith
  obtain ⟨α, ⟨hα, hle⟩, hαpos⟩ :=
    (((isLittleO_iff.1 h hε).and hle).and self_mem_nhdsWithin).exists
  have hαpos : 0 < α := hαpos
  have hpow : 0 < α ^ j := pow_pos hαpos j
  rw [hsum, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpow, smul_eq_mul] at hα
  have := (abs_le.1 hα).2
  nlinarith

end OneDim

/-! ### Feasible arcs and curve-based necessary conditions -/

section Necessary

/-- `IsFeasibleArc K x j s`: some arc `γ(α) = x + ∑_{ℓ=1}^j α^ℓ s_ℓ + o(α^j)` lies in `K` for all
small `α > 0` (the arcs (12.1.4), (14.3.2) of [cartis2022evaluation]; the tuple `(s_1, …, s_j)`
belongs to the book's descriptor set `𝒟^j` of `K`). -/
def IsFeasibleArc (K : Set E) (x : E) (j : ℕ) (s : ℕ → E) : Prop :=
  ∃ γ : ℝ → E, ((fun α => γ α - (x + ∑ ℓ ∈ Icc 1 j, α ^ ℓ • s ℓ)) =o[𝓝[>] 0] fun α => α ^ j) ∧
    ∀ᶠ α in 𝓝[>] 0, γ α ∈ K

variable {K K' : Set E} {x : E} {j : ℕ} {s : ℕ → E}

theorem IsFeasibleArc.mono (h : IsFeasibleArc K x j s) (hKK' : K ⊆ K') : IsFeasibleArc K' x j s :=
  let ⟨γ, hγ, hK⟩ := h
  ⟨γ, hγ, hK.mono fun _ hα => hKK' hα⟩

/-- In the whole space every tuple is feasible: take the polynomial arc itself. -/
theorem isFeasibleArc_univ (x : E) (j : ℕ) (s : ℕ → E) : IsFeasibleArc Set.univ x j s :=
  ⟨fun α => x + ∑ ℓ ∈ Icc 1 j, α ^ ℓ • s ℓ, by simp,
    Eventually.of_forall fun _ => Set.mem_univ _⟩

/-- For a convex set `X ∋ x`, a first-order direction `s_1` with `x + t s_1 ∈ X` for some `t > 0`
is feasible (the segment is an arc). -/
theorem isFeasibleArc_one_of_convex {X : Set E} (hX : Convex ℝ X) (hx : x ∈ X) {t : ℝ}
    (ht : 0 < t) (hxt : x + t • s 1 ∈ X) : IsFeasibleArc X x 1 s := by
  refine ⟨fun α => x + α • s 1, by simp, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT ht] with α hα
  have h := hX.add_smul_mem (x := x) (y := t • s 1) hx (by simpa using hxt)
    ⟨div_nonneg hα.1.le ht.le, (div_le_one ht).2 hα.2.le⟩
  rwa [smul_smul, div_mul_cancel₀ _ ht.ne'] at h

/-- **Curve-based necessary condition along one feasible arc.** If `f` is `C^j` at `x` (`j ≥ 1`),
`x` minimizes `f` locally on `K`, the tuple `s` is feasible for `K` at `x` up to order `j` and the
coefficients `c_1, …, c_{j-1}` vanish, then `c_j ≥ 0`. -/
theorem curveCoeff_nonneg_of_isLocalMinOn {f : E → ℝ} (hf : ContDiffAt ℝ j f x) (hj : 1 ≤ j)
    (hmin : IsLocalMinOn f K x) (harc : IsFeasibleArc K x j s)
    (hzero : ∀ i ∈ Ico 1 j, curveCoeff (ftaylorSeries ℝ f x) s i = 0) :
    0 ≤ curveCoeff (ftaylorSeries ℝ f x) s j := by
  obtain ⟨γ, hγ, hK⟩ := harc
  have hγK : Tendsto γ (𝓝[>] 0) (𝓝[K] x) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_of_isLittleO_curve hγ, hK⟩
  exact nonneg_of_isLittleO_poly_of_le hj (isLittleO_comp_curve_sub_curveCoeff hf hγ)
    (hγK.eventually hmin) hzero

/-- `IsCurveCritical D q`: the curve-based conditions of order `1, …, q` hold for the derivative
data `D`: for every `j ∈ [1, q]` and every `s`, if `c_1 = ⋯ = c_{j-1} = 0` then `c_j ≥ 0`, with
`c_i = curveCoeff D s i` ([cartis2022evaluation], (12.1.6)–(12.1.7)). For
`D = ftaylorSeries ℝ f x` this is the book's "`x` is a `q`-th order minimizer". -/
def IsCurveCritical (D : FormalMultilinearSeries ℝ E ℝ) (q : ℕ) : Prop :=
  ∀ j ∈ Icc 1 q, ∀ s : ℕ → E, (∀ i ∈ Ico 1 j, curveCoeff D s i = 0) → 0 ≤ curveCoeff D s j

namespace IsCurveCritical

variable {D : FormalMultilinearSeries ℝ E ℝ} {q : ℕ}

theorem mono {q' : ℕ} (h : IsCurveCritical D q) (hq : q' ≤ q) : IsCurveCritical D q' :=
  fun j hj => h j (Icc_subset_Icc_right hq hj)

/-- First-order condition: the first derivative vanishes. -/
theorem apply_one_eq_zero (h : IsCurveCritical D q) (hq : 1 ≤ q) : D 1 = 0 := by
  have key : ∀ d : E, 0 ≤ D 1 fun _ => d := fun d => by
    have := h 1 (mem_Icc.2 ⟨le_rfl, hq⟩) (fun _ => d) (by simp)
    rwa [curveCoeff_one] at this
  ext v
  have hv : v = fun _ => v 0 := funext fun i => by rw [Subsingleton.elim i 0]
  rw [hv]
  refine le_antisymm ?_ (key _)
  have h1 := key (-v 0)
  have h2 := (D 1).map_smul_univ (fun _ => (-1 : ℝ)) (fun _ => v 0)
  simp only [neg_one_smul, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one] at h2
  rw [h2] at h1
  simpa using h1

/-- Second-order condition: the second derivative is nonnegative on the diagonal. -/
theorem apply_two_nonneg (h : IsCurveCritical D q) (hq : 2 ≤ q) (d : E) :
    0 ≤ D 2 fun _ => d := by
  have h1 := h.apply_one_eq_zero (by omega)
  have := h 2 (mem_Icc.2 ⟨by norm_num, hq⟩) (fun i => if i = 1 then d else 0) (by
    intro i hi
    obtain rfl : i = 1 := by simp at hi; omega
    simp [curveCoeff_one, h1])
  rw [curveCoeff_two, h1] at this
  simpa using this

/-- Third-order condition: `D_3[d]^3 = 0` on the null directions `D_2[d]^2 = 0`
([cartis2022evaluation], discussion after Theorem 12.1.1, with `s_1 = ±d`). -/
theorem apply_three_eq_zero (h : IsCurveCritical D q) (hq : 3 ≤ q) {d : E}
    (hd : (D 2 fun _ => d) = 0) : (D 3 fun _ => d) = 0 := by
  have h1 := h.apply_one_eq_zero (by omega)
  -- along the ray `s_1 = e`, `s_i = 0` for `i ≥ 2`
  have key : ∀ e : E, (D 2 fun _ => e) = 0 → 0 ≤ D 3 fun _ => e := by
    intro e he
    set s : ℕ → E := fun i => if i = 1 then e else 0
    have hs : ∀ i, 2 ≤ i → s i = 0 := fun i hi => ite_eq_right_iff.2 fun h => by omega
    have := h 3 (mem_Icc.2 ⟨by norm_num, hq⟩) s (by
      intro i hi
      rw [curveCoeff_of_ray D s (mem_Ico.1 hi).1 hs]
      rcases (by simp at hi; omega : i = 1 ∨ i = 2) with rfl | rfl
      · simp [s, h1]
      · simp [s, he])
    rw [curveCoeff_of_ray D s (by norm_num) hs] at this
    simpa [s, Nat.factorial] using this
  have hneg : (D 3 fun _ => -d) = -D 3 fun _ => d := by
    have h2 := (D 3).map_smul_univ (fun _ => (-1 : ℝ)) (fun _ => d)
    simp only [neg_one_smul, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h2
    rw [h2]
    norm_num
  have hneg2 : (D 2 fun _ => -d) = 0 := by
    have h2 := (D 2).map_smul_univ (fun _ => (-1 : ℝ)) (fun _ => d)
    simp only [neg_one_smul, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h2
    rw [h2, hd, smul_zero]
  have := key (-d) hneg2
  rw [hneg] at this
  exact le_antisymm (by linarith) (key d hd)

end IsCurveCritical

/-- `IsCurveCritical D 1` holds exactly when the first derivative vanishes. -/
theorem isCurveCritical_one_iff {D : FormalMultilinearSeries ℝ E ℝ} :
    IsCurveCritical D 1 ↔ D 1 = 0 := by
  refine ⟨fun h => h.apply_one_eq_zero le_rfl, fun h j hj s _ => ?_⟩
  obtain rfl : j = 1 := by simp at hj; omega
  simp [curveCoeff_one, h]

/-- `IsCurveCritical D 2` holds exactly when the first derivative vanishes and the second one is
nonnegative on the diagonal (no symmetry of `D 2` needed). -/
theorem isCurveCritical_two_iff {D : FormalMultilinearSeries ℝ E ℝ} :
    IsCurveCritical D 2 ↔ D 1 = 0 ∧ ∀ d, 0 ≤ D 2 fun _ => d := by
  refine ⟨fun h => ⟨h.apply_one_eq_zero (by norm_num), h.apply_two_nonneg le_rfl⟩,
    fun ⟨h1, h2⟩ j hj s _ => ?_⟩
  rcases (by simp at hj; omega : j = 1 ∨ j = 2) with rfl | rfl
  · simp [curveCoeff_one, h1]
  · rw [curveCoeff_two, h1]
    simpa using h2 (s 1)

/-- **Curve-based necessary conditions for an unconstrained local minimum**
([cartis2022evaluation], Theorem 12.1.1). If `f` is `C^q` at a local minimizer `x`, then `x` is a
`q`-th order minimizer: for every `j ∈ [1, q]` and every `s_1, …, s_j` with
`c_1 = ⋯ = c_{j-1} = 0`, `c_j ≥ 0`, where `c_i` are the coefficients (12.1.6).

The book restricts (12.1.6)–(12.1.7) to tuples with all `s_i ≠ 0`; here every tuple `s` is
allowed, so the conclusion is asserted for more tuples and the statement is stronger. Tuples with
zero entries are what give the classical conditions, e.g. the ray `s_1 = d`, `s_i = 0` for
`i ≥ 2`. -/
theorem _root_.IsLocalMin.isCurveCritical {f : E → ℝ} {x : E} {q : ℕ} (hf : ContDiffAt ℝ q f x)
    (hmin : IsLocalMin f x) : IsCurveCritical (ftaylorSeries ℝ f x) q := fun j hj s hzero =>
  curveCoeff_nonneg_of_isLocalMinOn (hf.of_le (by exact_mod_cast (mem_Icc.1 hj).2))
    (mem_Icc.1 hj).1 (isLocalMinOn_univ_iff.2 hmin) (isFeasibleArc_univ x j s) hzero

/-- **Expansion of the constraints along a feasible arc** ([cartis2022evaluation], (14.3.3)). If
`c` is `C^j` at `x` and `s` is feasible up to order `j` for a set on which `c`
vanishes, then all coefficients `c_1, …, c_j` of `c` along `s` vanish. -/
theorem curveCoeff_eq_zero_of_isFeasibleArc {c : E → F} (hc : ContDiffAt ℝ j c x) {X : Set E}
    (harc : IsFeasibleArc (X ∩ {z | c z = 0}) x j s) :
    ∀ i ∈ Icc 1 j, curveCoeff (ftaylorSeries ℝ c x) s i = 0 := by
  obtain ⟨γ, hγ, hK⟩ := harc
  -- `c x = 0`: `c` is continuous at `x` and vanishes along the arc, which tends to `x`
  have hcx : c x = 0 := by
    have h1 : Tendsto (fun α => c (γ α)) (𝓝[>] 0) (𝓝 (c x)) :=
      hc.continuousAt.tendsto.comp (tendsto_of_isLittleO_curve hγ)
    have h2 : Tendsto (fun α => c (γ α)) (𝓝[>] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' (hK.mono fun α hα => (hα.2 : c (γ α) = 0).symm)
    exact tendsto_nhds_unique h1 h2
  refine eq_zero_of_isLittleO_sum_pow ((isLittleO_comp_curve_sub_curveCoeff hc hγ).neg_left
    |>.congr' ?_ EventuallyEq.rfl)
  filter_upwards [hK] with α hα
  have hα0 : c (γ α) = 0 := hα.2
  simp [hα0, hcx]

/-- **Curve-based necessary conditions for a constrained local minimum**
([cartis2022evaluation], Theorem 14.3.1, corrected). Let `f : E → ℝ` and `c : E → F` be `C^q` at
`x` with `c x = 0`, and let `x` be a local minimizer of `f` on `X ∩ {c = 0}`. For any multiplier
`y`, write `ℒ(z) = f(z) - ⟪y, c(z)⟫`. If `j ∈ [1, q]`, `s` is feasible for `X ∩ {c = 0}` up to
order `j`, and the coefficients `c_1, …, c_{j-1}` of `ℒ` along `s` vanish, then the coefficient
`c_j` of `ℒ` is nonnegative (14.3.4).

The book quantifies over tuples `s` admitting an arc that only stays in `X` and satisfies the
first-order feasibility conditions (14.3.3) for `c`. That version is false: for `X = ℝ²`,
`c(x) = x₁² + x₂²`, `f(x) = -x₁`, `x = 0` is the only feasible point, (14.3.3) holds for every
`s_1` and X.CQ holds for `q = 1`, yet (14.3.4) for `j = 1`, `s_1 = e_1` reads `-1 ≥ 0`. Here the
arc must stay in the whole feasible set, as the book's derivation (substituting the arc into
`c = 0`) intends; (14.3.3) then holds by `curveCoeff_eq_zero_of_isFeasibleArc`. -/
theorem curveCoeff_lagrangian_nonneg_of_isLocalMinOn {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {f : E → ℝ} {c : E → F} {X : Set E} {q : ℕ}
    (hf : ContDiffAt ℝ q f x) (hc : ContDiffAt ℝ q c x) (hcx : c x = 0)
    (hmin : IsLocalMinOn f (X ∩ {z | c z = 0}) x) (y : F) (hj : j ∈ Icc 1 q)
    (harc : IsFeasibleArc (X ∩ {z | c z = 0}) x j s)
    (hzero : ∀ i ∈ Ico 1 j,
      curveCoeff (ftaylorSeries ℝ (fun z => f z - inner ℝ y (c z)) x) s i = 0) :
    0 ≤ curveCoeff (ftaylorSeries ℝ (fun z => f z - inner ℝ y (c z)) x) s j := by
  have hjq : (j : WithTop ℕ∞) ≤ q := by exact_mod_cast (mem_Icc.1 hj).2
  have hL : ContDiffAt ℝ j (fun z => f z - inner ℝ y (c z)) x :=
    (hf.of_le hjq).sub (((innerSL ℝ y).contDiff.contDiffAt).comp x (hc.of_le hjq))
  refine curveCoeff_nonneg_of_isLocalMinOn hL (mem_Icc.1 hj).1 ?_ harc hzero
  filter_upwards [hmin, self_mem_nhdsWithin] with z hz hzK
  have hz0 : c z = 0 := hzK.2
  simpa [hcx, hz0] using hz

end Necessary

end Optimization

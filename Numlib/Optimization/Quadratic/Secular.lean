import Numlib.Analysis.InnerProductSpace.Energy
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import Mathlib.Tactic

/-!
# Secular equations of weighted quadratic subproblems

`PencilBasis` records a complete generalized eigenbasis of actual operators.
The shifted inverse is an actual continuous linear map inverse; its spectral
formula is derived by solving the linear system. No value at a singular endpoint
is used. A positive finite or infinite right-hand gap gives the unique interior
root against a continuous nonnegative nonzero nondecreasing comparison function.
-/

open scoped BigOperators
namespace QuadraticSecular
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [DecidableEq ι]

/-- Actual generalized eigenbasis of a symmetric matrix pencil in a positive metric. -/
structure PencilBasis (H M : E →L[ℝ] E) where
  basis : Module.Basis ι ℝ E
  eigenvalue : ι → ℝ
  orthonormal : ∀ i j, inner ℝ (M (basis i)) (basis j) = if i = j then 1 else 0
  eigenvector : ∀ i, H (basis i) = eigenvalue i • M (basis i)

/-- The actual shifted-operator solution used in the secular equation. -/
noncomputable def solution (H M : E →L[ℝ] E) (g : E) (z : ℝ) : E :=
  -((H + z • M).inverse g)

/-- The squared metric norm of the actual shifted-operator solution. -/
noncomputable def secular (H M : E →L[ℝ] E) (g : E) (z : ℝ) : ℝ :=
  inner ℝ (M (solution H M g z)) (solution H M g z)

namespace PencilBasis
variable {H M : E →L[ℝ] E} (B : PencilBasis (ι := ι) H M)

omit [Fintype ι] in
/-- Inner products against a complete basis separate vectors. -/
theorem eq_zero_of_inner_basis [Finite ι] {v : E}
    (hv : ∀ i, inner ℝ v (B.basis i) = 0) : v = 0 := by
  let := Fintype.ofFinite ι
  have hh : inner ℝ v v = 0 := by
    nth_rw 2 [← B.basis.sum_repr v]
    simp only [inner_sum, real_inner_smul_right, hv, mul_zero, Finset.sum_const_zero]
  exact inner_self_eq_zero.mp hh

/-- A metric orthonormal finite combination has its stated metric coordinates. -/
theorem inner_metric_sum (c : ι → ℝ) (i : ι) :
    inner ℝ (M (∑ j, c j • B.basis j)) (B.basis i) = c i := by
  simp only [map_sum, map_smul, sum_inner, real_inner_smul_left, B.orthonormal]
  simp

/-- Every vector is the dual metric-basis expansion of its original inner products. -/
theorem dual_expansion (g : E) :
    ∑ i, inner ℝ g (B.basis i) • M (B.basis i) = g := by
  apply sub_eq_zero.mp
  apply B.eq_zero_of_inner_basis
  intro j
  simp only [inner_sub_left, sum_inner, real_inner_smul_left, B.orthonormal]
  simp

/-- Applying the shifted pencil to a finite basis combination is diagonal. -/
theorem shifted_sum (z : ℝ) (c : ι → ℝ) :
    (H + z • M) (∑ i, c i • B.basis i) =
      ∑ i, (c i * (z + B.eigenvalue i)) • M (B.basis i) := by
  simp only [map_sum, map_smul, add_apply,
    smul_apply, B.eigenvector]
  apply Finset.sum_congr rfl
  intro i _
  module

/-- The explicit spectral vector solves the actual shifted linear system. -/
theorem shifted_inverse_sum (z : ℝ) (hz : ∀ i, z + B.eigenvalue i ≠ 0) (g : E) :
    (H + z • M) (∑ i, (inner ℝ g (B.basis i) / (z + B.eigenvalue i)) • B.basis i) = g := by
  rw [B.shifted_sum]
  simp only [div_mul_cancel₀ _ (hz _)]
  exact B.dual_expansion g

omit [Fintype ι] in
/-- The actual shifted operator acts diagonally on every metric-basis coordinate. -/
theorem shifted_apply_inner [Finite ι] (z : ℝ) (v : E) (i : ι) :
    inner ℝ ((H + z • M) v) (B.basis i) =
      B.basis.repr v i * (z + B.eigenvalue i) := by
  let := Fintype.ofFinite ι
  conv_lhs => arg 2; rw [← B.basis.sum_repr v]
  rw [B.shifted_sum]
  simp only [sum_inner, real_inner_smul_left, B.orthonormal]
  simp

omit [Fintype ι] in
/-- Nonzero shifted eigenvalues make the actual pencil injective. -/
theorem shifted_injective [Finite ι] (z : ℝ) (hz : ∀ i, z + B.eigenvalue i ≠ 0) :
    Function.Injective (H + z • M) := by
  let := Fintype.ofFinite ι
  intro u v huv
  apply sub_eq_zero.mp
  apply B.basis.repr.injective
  ext i
  have hh : B.basis.repr (u-v) i * (z + B.eigenvalue i) = 0 := by
    rw [← B.shifted_apply_inner, map_sub, huv, sub_self, inner_zero_left]
  simpa only [map_zero, Finsupp.zero_apply] using (mul_eq_zero.mp hh).resolve_right (hz i)

omit [Fintype ι] in
/-- The spectral construction gives an actual inverse at every nonsingular shift. -/
theorem shifted_invertible [Finite ι] [FiniteDimensional ℝ E] (z : ℝ)
    (hz : ∀ i, z + B.eigenvalue i ≠ 0) : (H + z • M).IsInvertible := by
  let := Fintype.ofFinite ι
  let e : E ≃ₗ[ℝ] E := LinearEquiv.ofBijective (H + z • M).toLinearMap
    ⟨B.shifted_injective z hz, fun g => ⟨_, B.shifted_inverse_sum z hz g⟩⟩
  exact ⟨e.toContinuousLinearEquiv, rfl⟩

/-- The matrix-defined resolvent has its spectral expression, proved from the linear system. -/
theorem solution_eq_sum [FiniteDimensional ℝ E] (z : ℝ)
    (hz : ∀ i, z + B.eigenvalue i ≠ 0) (g : E) :
    solution H M g z = ∑ i, (-inner ℝ g (B.basis i) / (z + B.eigenvalue i)) • B.basis i := by
  have hInv := B.shifted_invertible z hz
  apply hInv.injective
  unfold solution
  rw [map_neg, hInv.self_apply_inverse, B.shifted_sum]
  simp only [div_mul_cancel₀ _ (hz _)]
  simpa only [neg_smul, Finset.sum_neg_distrib] using
    (congrArg Neg.neg (B.dual_expansion g)).symm

/-- Metric orthonormality gives the true squared metric norm of a finite combination. -/
theorem metric_norm_sq_sum (c : ι → ℝ) :
    inner ℝ (M (∑ i, c i • B.basis i)) (∑ i, c i • B.basis i) = ∑ i, (c i)^2 := by
  simp only [inner_sum, real_inner_smul_right, B.inner_metric_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The actual squared metric resolvent norm is the finite spectral secular sum. -/
theorem secular_eq_sum [FiniteDimensional ℝ E] (z : ℝ)
    (hz : ∀ i, z + B.eigenvalue i ≠ 0) (g : E) :
    secular H M g z = ∑ i, (inner ℝ g (B.basis i))^2 / (z + B.eigenvalue i)^2 := by
  unfold secular
  rw [B.solution_eq_sum z hz g, B.metric_norm_sq_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [div_pow, neg_sq]

end PencilBasis
end QuadraticSecular

namespace QuadraticSecular
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [DecidableEq ι] [Nonempty ι]
namespace PencilBasis
variable {H M : E →L[ℝ] E} (B : PencilBasis (ι := ι) H M)

/-- The leftmost generalized eigenvalue of the actual pencil. -/
noncomputable def leftmost : ℝ := Finset.univ.inf' Finset.univ_nonempty B.eigenvalue

/-- The source lower endpoint of the positive-definite shifted pencil. -/
noncomputable def edge : ℝ := max 0 (-B.leftmost)

/-- Every shift above the source edge has positive spectral denominators. -/
theorem denominator_pos {z : ℝ} (hz : B.edge < z) (i : ι) : 0 < z + B.eigenvalue i := by
  have hμ : B.leftmost ≤ B.eigenvalue i := Finset.inf'_le _ (Finset.mem_univ i)
  have hh : -B.leftmost ≤ B.edge := le_max_right _ _
  linarith

/-- Spectral scalar coefficients are the original gradient's inner products. -/
noncomputable def spectralSum (g : E) (z : ℝ) : ℝ :=
  ∑ i, (inner ℝ g (B.basis i)) ^ 2 / (z + B.eigenvalue i) ^ 2

omit [Nonempty ι] in
/-- The scalar spectral sum is nonnegative. -/
theorem spectralSum_nonneg (g : E) (z : ℝ) : 0 ≤ B.spectralSum g z :=
  Finset.sum_nonneg (fun _ _ => div_nonneg (sq_nonneg _) (sq_nonneg _))

omit [Nonempty ι] [Fintype ι] in
/-- A nonzero gradient has a nonzero coefficient in every complete basis. -/
theorem exists_coefficient_ne_zero [Finite ι] {g : E} (hg : g ≠ 0) :
    ∃ i, inner ℝ g (B.basis i) ≠ 0 := by
  by_contra hh
  push Not at hh
  exact hg (B.eq_zero_of_inner_basis hh)

/-- The squared resolvent norm is strictly decreasing above the source spectral edge. -/
theorem strictAntiOn_spectralSum {g : E} (hg : g ≠ 0) :
    StrictAntiOn (B.spectralSum g) (Set.Ioi B.edge) := by
  intro u hu v hv huv
  obtain ⟨i, hi⟩ := B.exists_coefficient_ne_zero hg
  apply Finset.sum_lt_sum
  · intro j _
    exact div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos (B.denominator_pos hu j))
      (pow_le_pow_left₀ (B.denominator_pos hu j).le
        (by linarith : u+B.eigenvalue j ≤ v+B.eigenvalue j) 2)
  · refine ⟨i, Finset.mem_univ _, ?_⟩
    apply div_lt_div_of_pos_left (sq_pos_of_ne_zero hi)
      (sq_pos_of_pos (B.denominator_pos hu i))
    exact pow_lt_pow_left₀ (by linarith : u+B.eigenvalue i < v+B.eigenvalue i)
      (B.denominator_pos hu i).le (by norm_num)

end PencilBasis
end QuadraticSecular

namespace QuadraticSecular.PencilBasis
open Filter
open scoped Topology
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {H M : E →L[ℝ] E} (B : PencilBasis (ι := ι) H M)

/-- The scalar spectral sum is continuous above the positive-definite edge. -/
theorem continuousOn_spectralSum (g : E) :
    ContinuousOn (B.spectralSum g) (Set.Ioi B.edge) := by
  apply continuousOn_finsetSum
  intro i _
  exact continuousOn_const.div ((continuousOn_id.add continuousOn_const).pow 2)
    (fun z hz => ne_of_gt (sq_pos_of_pos (B.denominator_pos hz i)))

omit [Nonempty ι] in
/-- The squared resolvent norm tends to zero as the shift tends to infinity. -/
theorem tendsto_spectralSum_zero (g : E) :
    Tendsto (B.spectralSum g) atTop (𝓝 0) := by
  have hh (i : ι) : Tendsto (fun z : ℝ =>
      (inner ℝ g (B.basis i)) ^ 2 / (z + B.eigenvalue i) ^ 2) atTop (𝓝 0) := by
    have ht : Tendsto (fun z : ℝ => z + B.eigenvalue i) atTop atTop := by
      simpa only [add_comm] using
        (tendsto_const_nhds.add_atTop tendsto_id :
          Tendsto (fun z : ℝ => B.eigenvalue i + z) atTop atTop)
    have hi := (tendsto_inv_atTop_zero.comp ht).pow 2
    simpa only [Function.comp_def, inv_pow, div_eq_mul_inv,
      zero_pow (by norm_num : 2 ≠ 0), mul_zero] using
      hi.const_mul ((inner ℝ g (B.basis i)) ^ 2)
  change Tendsto (fun z => ∑ i, (inner ℝ g (B.basis i)) ^ 2 /
    (z + B.eigenvalue i) ^ 2) atTop (𝓝 0)
  convert tendsto_finsetSum Finset.univ (fun i _ => hh i) using 1
  simp

/-- A positive left-hand gap and a nonzero increasing comparison function give
an interior secular root, without assigning an inverse at a singular endpoint. -/
theorem existsUnique_root (g : E) (τ : ℝ → ℝ)
    (hτc : ContinuousOn τ (Set.Ioi B.edge))
    (hτm : MonotoneOn τ (Set.Ioi B.edge))
    (hτn : ∀ z ∈ Set.Ioi B.edge, 0 ≤ τ z)
    (hτp : ∃ z ∈ Set.Ioi B.edge, 0 < τ z)
    (hgap : ∃ z ∈ Set.Ioi B.edge, τ z < B.spectralSum g z) :
    ∃! z, z ∈ Set.Ioi B.edge ∧ B.spectralSum g z = τ z := by
  obtain ⟨a, ha, hga⟩ := hgap
  obtain ⟨c, hc, htc⟩ := hτp
  have hg : g ≠ 0 := by
    intro hg
    subst g
    have hzero : B.spectralSum 0 a = 0 := by simp [spectralSum]
    linarith [hτn a ha]
  have hev : ∀ᶠ z : ℝ in atTop, B.spectralSum g z < τ c :=
    (B.tendsto_spectralSum_zero g).eventually_lt_const htc
  obtain ⟨b, hb, hab, hcb⟩ := (hev.and
    ((eventually_gt_atTop a).and (eventually_gt_atTop c))).exists
  have hbedge : b ∈ Set.Ioi B.edge := lt_trans ha hab
  have hgb : B.spectralSum g b - τ b ≤ 0 := by
    have := hτm hc hbedge hcb.le
    linarith
  have hga' : 0 ≤ B.spectralSum g a - τ a := sub_nonneg.mpr hga.le
  have hI : Set.Icc a b ⊆ Set.Ioi B.edge := fun z hz => lt_of_lt_of_le ha hz.1
  have hcont : ContinuousOn (fun z => B.spectralSum g z - τ z) (Set.Icc a b) :=
    ((B.continuousOn_spectralSum g).sub hτc).mono hI
  obtain ⟨z, hz, heq⟩ := intermediate_value_Icc' hab.le hcont ⟨hgb, hga'⟩
  refine ⟨z, ⟨hI hz, sub_eq_zero.mp heq⟩, ?_⟩
  intro y hy
  have hs := B.strictAntiOn_spectralSum hg
  rcases lt_trichotomy y z with h | h | h
  · have := hs hy.1 (hI hz) h
    have := hτm hy.1 (hI hz) h.le
    rw [hy.2, sub_eq_zero.mp heq] at *
    linarith
  · exact h
  · have := hs (hI hz) hy.1 h
    have := hτm (hI hz) hy.1 h.le
    rw [hy.2, sub_eq_zero.mp heq] at *
    linarith

end QuadraticSecular.PencilBasis

namespace QuadraticSecular.PencilBasis
open Filter
open scoped Topology
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {H M : E →L[ℝ] E} (B : PencilBasis (ι := ι) H M)

/-- A strictly positive finite or infinite right limit yields an interior
positive gap. The shifted inverse is needed only in the open interval. -/
theorem exists_gap_of_right_limit (g : E) (τ : ℝ → ℝ)
    (hleft : Tendsto (fun z => B.spectralSum g z - τ z)
        (𝓝[Set.Ioi B.edge] B.edge) atTop ∨
      ∃ l : ℝ, 0 < l ∧ Tendsto (fun z => B.spectralSum g z - τ z)
        (𝓝[Set.Ioi B.edge] B.edge) (𝓝 l)) :
    ∃ z ∈ Set.Ioi B.edge, τ z < B.spectralSum g z := by
  have : (𝓝[Set.Ioi B.edge] B.edge).NeBot := nhdsWithin_Ioi_neBot le_rfl
  have hev : ∀ᶠ z in 𝓝[Set.Ioi B.edge] B.edge, 0 < B.spectralSum g z - τ z := by
    rcases hleft with ht | ⟨l, hl, ht⟩
    · exact ht.eventually_gt_atTop 0
    · exact ht.eventually (eventually_gt_nhds hl)
  have hmem : ∀ᶠ z in 𝓝[Set.Ioi B.edge] B.edge, z ∈ Set.Ioi B.edge :=
    self_mem_nhdsWithin
  obtain ⟨z, hz, hgap⟩ := (hmem.and hev).exists
  exact ⟨z, hz, sub_pos.mp hgap⟩

/-- Root existence and uniqueness for the actual matrix-defined secular function,
with a positive right-hand endpoint limit interpreted finitely or as infinity. -/
theorem existsUnique_secular_root [FiniteDimensional ℝ E] (g : E) (τ : ℝ → ℝ)
    (hτc : ContinuousOn τ (Set.Ioi B.edge))
    (hτm : MonotoneOn τ (Set.Ioi B.edge))
    (hτn : ∀ z ∈ Set.Ioi B.edge, 0 ≤ τ z)
    (hτp : ∃ z ∈ Set.Ioi B.edge, 0 < τ z)
    (hleft : Tendsto (fun z => secular H M g z - τ z)
        (𝓝[Set.Ioi B.edge] B.edge) atTop ∨
      ∃ l : ℝ, 0 < l ∧ Tendsto (fun z => secular H M g z - τ z)
        (𝓝[Set.Ioi B.edge] B.edge) (𝓝 l)) :
    ∃! z, z ∈ Set.Ioi B.edge ∧ secular H M g z = τ z := by
  have heq (z : ℝ) (hz : z ∈ Set.Ioi B.edge) :
      secular H M g z = B.spectralSum g z :=
    B.secular_eq_sum z (fun i => ne_of_gt (B.denominator_pos hz i)) g
  have hevent : (fun z => secular H M g z - τ z) =ᶠ[𝓝[Set.Ioi B.edge] B.edge]
      (fun z => B.spectralSum g z - τ z) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [heq z hz]
  have hleft' : Tendsto (fun z => B.spectralSum g z - τ z)
        (𝓝[Set.Ioi B.edge] B.edge) atTop ∨
      ∃ l : ℝ, 0 < l ∧ Tendsto (fun z => B.spectralSum g z - τ z)
        (𝓝[Set.Ioi B.edge] B.edge) (𝓝 l) := by
    rcases hleft with ht | ⟨l, hl, ht⟩
    · exact Or.inl (ht.congr' hevent)
    · exact Or.inr ⟨l, hl, ht.congr' hevent⟩
  obtain ⟨z, hz, hu⟩ := B.existsUnique_root g τ hτc hτm hτn hτp
    (B.exists_gap_of_right_limit g τ hleft')
  refine ⟨z, ⟨hz.1, (heq z hz.1).trans hz.2⟩, ?_⟩
  intro y hy
  exact hu y ⟨hy.1, (heq y hy.1).symm.trans hy.2⟩

end QuadraticSecular.PencilBasis

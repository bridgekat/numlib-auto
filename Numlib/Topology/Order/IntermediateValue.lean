import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The discrete mean value theorem

A convex combination of values of a continuous function on a compact interval is a value of that
function: for `u` continuous on `[a, b]`, points `x j ∈ [a, b]` and nonnegative weights `δ j`,
there is `η ∈ [a, b]` with `∑ j, δ j * u (x j) = u η * ∑ j, δ j`
(`ContinuousOn.exists_sum_mul_eq_mul_sum`; [quarteroni2000numerical] Theorem 9.1, the *discrete
mean value theorem*).

It is the intermediate value theorem applied to `u` between the points where `u` attains its
minimum and its maximum, and it is what turns a quadrature error written as a sum of panel errors
`∑ j, c * f^{(k)}(ξ_j)` into a single value `m * c * f^{(k)}(ξ)` — the step every composite error
formula takes (`Numlib/Approximation/NewtonCotes` and
`Numlib/Analysis/SpecialFunctions/EulerMaclaurin`).
It lives here, beside Mathlib's `intermediate_value_uIcc`, so that the analysis modules that use it
import no approximation theory.

The book states it for weights "all of the same sign"; that is the nonnegative case applied to
`-δ`, so only the nonnegative case is stated. The domain is any densely ordered conditionally
complete linear order with the order topology and the codomain any linearly ordered commutative
semiring with an order-closed topology and continuous multiplication (`ℝ`, in every use), since
that is all the two ingredients need.
-/

open Set

variable {α : Type*} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
  [DenselyOrdered α] {R : Type*} [CommSemiring R] [LinearOrder R] [IsOrderedRing R]
  [TopologicalSpace R] [OrderClosedTopology R] [ContinuousMul R]

/-- **The discrete mean value theorem, on an order-connected set.** For `u` continuous on an
order-connected set `S`, finitely many (at least one) points `x j ∈ S` and nonnegative weights
`δ j`, there is `η ∈ S` with `∑ j, δ j * u (x j) = u η * ∑ j, δ j`.

The sum lies between `u (x p) * ∑ δ` and `u (x q) * ∑ δ`, where `u ∘ x` attains its minimum at `p`
and its maximum at `q`, and the intermediate value theorem for `x ↦ u x * ∑ δ` on the interval
between `x p` and `x q`, which lies in `S`, supplies `η`. Taking `S` an open interval containing
the points puts `η` strictly inside it. -/
theorem ContinuousOn.exists_sum_mul_eq_mul_sum_of_ordConnected {S : Set α} (hS : S.OrdConnected)
    {u : α → R} (hu : ContinuousOn u S) {ι : Type*} [Fintype ι] [Nonempty ι] {x : ι → α}
    (hx : ∀ j, x j ∈ S) {δ : ι → R} (hδ : ∀ j, 0 ≤ δ j) :
    ∃ η ∈ S, ∑ j, δ j * u (x j) = u η * ∑ j, δ j := by
  obtain ⟨p, -, hmin⟩ := Finset.exists_min_image Finset.univ (fun j => u (x j))
    Finset.univ_nonempty
  obtain ⟨q, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun j => u (x j))
    Finset.univ_nonempty
  have hlow : u (x p) * ∑ j, δ j ≤ ∑ j, δ j * u (x j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (hmin j (Finset.mem_univ j)) (hδ j)
  have hhigh : ∑ j, δ j * u (x j) ≤ u (x q) * ∑ j, δ j := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => by
      rw [mul_comm (u (x q))]
      exact mul_le_mul_of_nonneg_left (hmax j (Finset.mem_univ j)) (hδ j)
  have hpq : uIcc (x p) (x q) ⊆ S := hS.uIcc_subset (hx p) (hx q)
  have hcont : ContinuousOn (fun t => u t * ∑ j, δ j) (uIcc (x p) (x q)) :=
    (hu.mono hpq).mul continuousOn_const
  obtain ⟨η, hη, hηval⟩ := intermediate_value_uIcc hcont (mem_uIcc_of_le hlow hhigh)
  exact ⟨η, hpq hη, hηval.symm⟩

/-- **The discrete mean value theorem.** For `u` continuous on `[a, b]`, finitely many points
`x j ∈ [a, b]` and nonnegative weights `δ j`, there is `η ∈ [a, b]` with
`∑ j, δ j * u (x j) = u η * ∑ j, δ j`: the case `S = Icc a b` of
`ContinuousOn.exists_sum_mul_eq_mul_sum_of_ordConnected`, with an empty family allowed.

Reference: [quarteroni2000numerical], Theorem 9.1. -/
theorem ContinuousOn.exists_sum_mul_eq_mul_sum {a b : α} (hab : a ≤ b) {u : α → R}
    (hu : ContinuousOn u (Icc a b)) {ι : Type*} [Fintype ι] {x : ι → α}
    (hx : ∀ j, x j ∈ Icc a b) {δ : ι → R} (hδ : ∀ j, 0 ≤ δ j) :
    ∃ η ∈ Icc a b, ∑ j, δ j * u (x j) = u η * ∑ j, δ j := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨a, left_mem_Icc.2 hab, by simp⟩
  · exact hu.exists_sum_mul_eq_mul_sum_of_ordConnected ordConnected_Icc hx hδ

/-! ### Roots between two points of opposite sign -/

section Root

/-- A continuous function changing sign on an interval has a root strictly inside it. -/
theorem Continuous.exists_mem_Ioo_eq_zero_of_mul_neg {F : ℝ → ℝ} (hF : Continuous F) {u v : ℝ}
    (huv : u < v) (h : F u * F v < 0) : ∃ z ∈ Set.Ioo u v, F z = 0 := by
  rcases mul_neg_iff.mp h with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · obtain ⟨z, hz, hz0⟩ :=
      intermediate_value_Ioo' huv.le hF.continuousOn (Set.mem_Ioo.mpr ⟨hv, hu⟩)
    exact ⟨z, hz, hz0⟩
  · obtain ⟨z, hz, hz0⟩ :=
      intermediate_value_Ioo huv.le hF.continuousOn (Set.mem_Ioo.mpr ⟨hu, hv⟩)
    exact ⟨z, hz, hz0⟩

/-- A continuous function on `[a, b]` taking values of opposite strict signs at `u < v` vanishes
somewhere strictly between `u` and `v`: the intermediate value theorem. -/
theorem ContinuousMap.exists_mem_Ioo_eq_zero_of_mul_neg {a b : ℝ} {g : C(Icc a b, ℝ)}
    {u v : Icc a b}
    (huv : (u : ℝ) < v) (h : g u * g v < 0) :
    ∃ z : Icc a b, (u : ℝ) < z ∧ (z : ℝ) < v ∧ g z = 0 := by
  have hab : a ≤ b := u.2.1.trans u.2.2
  set G : ℝ → ℝ := IccExtend hab g with hG
  have hGu : G u = g u := IccExtend_val hab g u
  have hGv : G v = g v := IccExtend_val hab g v
  have hcont : ContinuousOn G (Icc (u : ℝ) v) :=
    (g.continuous.Icc_extend' (h := hab)).continuousOn
  have key : ∃ z ∈ Ioo (u : ℝ) v, G z = 0 := by
    rcases mul_neg_iff.mp h with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · obtain ⟨z, hz, hz0⟩ := intermediate_value_Ioo' huv.le hcont
        (show (0 : ℝ) ∈ Ioo (G v) (G u) by rw [hGu, hGv]; exact ⟨hv, hu⟩)
      exact ⟨z, hz, hz0⟩
    · obtain ⟨z, hz, hz0⟩ := intermediate_value_Ioo huv.le hcont
        (show (0 : ℝ) ∈ Ioo (G u) (G v) by rw [hGu, hGv]; exact ⟨hu, hv⟩)
      exact ⟨z, hz, hz0⟩
  obtain ⟨z, hz, hz0⟩ := key
  have hzmem : z ∈ Icc a b := ⟨u.2.1.trans hz.1.le, hz.2.le.trans v.2.2⟩
  refine ⟨⟨z, hzmem⟩, hz.1, hz.2, ?_⟩
  rw [← hz0, hG, IccExtend_of_mem hab g hzmem]

end Root

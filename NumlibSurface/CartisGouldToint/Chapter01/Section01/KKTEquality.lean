import Numlib.Optimization.ConstrainedSecondOrder
import NumlibSurface.CartisGouldToint.Chapter01.Section01

/-!
# Equality-constrained optimality conditions

Theorem 1.1.3 is stated with equality LICQ as a precise sufficient choice for the source's
unspecified constraint qualification. Its first-order clause needs only local C1 smoothness;
its necessary and sufficient Hessian clauses use local C2 smoothness. The Lagrangian has the
source sign, `f - sum yᵢ cᵢ`, and every derivative is the actual derivative. Strict positivity
is tested only on nonzero directions, as required for any quadratic form.
-/

noncomputable section
open Filter Topology

namespace CartisGouldToint.Chapter01.Section01

/-- The source Lagrangian `f - sum yᵢ cᵢ`, obtained from the canonical plus-sign convention
by negating the multipliers. -/
def lagrangian {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (y : Fin m → ℝ) : ℝ := Constrained.lagrangian f c x (-y)

/-- The sign conversion gives precisely the source finite multiplier inner product. -/
theorem lagrangian_eq_sub_sum {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (y : Fin m → ℝ) : lagrangian f c x y = f x - ∑ i, y i * c i x := by
  simp [lagrangian, Constrained.lagrangian, Finset.sum_neg_distrib, sub_eq_add_neg]

/-- Theorem 1.1.3, with equality LICQ: first-order multipliers under C1 smoothness,
second-order necessity under C2 smoothness, and strict second-order sufficiency.
The qualification is required only for the necessary clauses. Smoothness is required only
on the open neighborhood `U` of the point, so no global extension is assumed. -/
theorem theorem_1_1_3 {n m : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : Fin m → EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hxU : x ∈ U)
    (hx : x ∈ Constrained.feasibleEq c) :
    (ContDiffOn ℝ 1 f U → (∀ i, ContDiffOn ℝ 1 (c i) U) →
      LinearIndependent ℝ (fun i => fderiv ℝ (c i) x) →
      IsLocalMinOn f (Constrained.feasibleEq c) x →
      ∃! y : Fin m → ℝ, fderiv ℝ (fun z => lagrangian f c z y) x = 0) ∧
    (ContDiffOn ℝ 2 f U → (∀ i, ContDiffOn ℝ 2 (c i) U) →
      LinearIndependent ℝ (fun i => fderiv ℝ (c i) x) →
      IsLocalMinOn f (Constrained.feasibleEq c) x →
      ∃! y : Fin m → ℝ, fderiv ℝ (fun z => lagrangian f c z y) x = 0 ∧
        ∀ d, (∀ i, fderiv ℝ (c i) x d = 0) →
          0 ≤ fderiv ℝ (fderiv ℝ (fun z => lagrangian f c z y)) x d d) ∧
    (ContDiffOn ℝ 2 f U → (∀ i, ContDiffOn ℝ 2 (c i) U) → ∀ y : Fin m → ℝ,
      fderiv ℝ (fun z => lagrangian f c z y) x = 0 →
      (∀ d, d ≠ 0 → (∀ i, fderiv ℝ (c i) x d = 0) →
        0 < fderiv ℝ (fderiv ℝ (fun z => lagrangian f c z y)) x d d) →
      ∃ δ > 0, ∀ z ∈ Constrained.feasibleEq c, dist z x < δ → z ≠ x → f x < f z) := by
  have hUn : U ∈ 𝓝 x := hU.mem_nhds hxU
  refine ⟨?_, ?_, ?_⟩
  · intro hf hc hlicq hmin
    have hfd := ((hf.contDiffAt hUn).hasStrictFDerivAt (by norm_num))
    have hcd := fun i => ((hc i).contDiffAt hUn).hasStrictFDerivAt (by norm_num)
    obtain ⟨l, hl, huniq⟩ := Constrained.existsUnique_multipliers_of_isLocalMinOn
      ⟨hx, hlicq⟩ hmin hfd hcd
    have heq (a : Fin m → ℝ) :
        fderiv ℝ (fun z => Constrained.lagrangian f c z a) x =
          fderiv ℝ f x + ∑ i, a i • fderiv ℝ (c i) x :=
      (Constrained.lagrangian_hasFDerivAt hfd.hasFDerivAt
        (fun i => (hcd i).hasFDerivAt) a).fderiv
    refine ⟨-l, ?_, ?_⟩
    · simpa only [lagrangian, neg_neg, heq] using hl
    · intro a ha
      have hm : -a = l := huniq (-a) (by simpa only [lagrangian, heq] using ha)
      simpa using congrArg Neg.neg hm
  · intro hf hc hlicq hmin
    obtain ⟨l, hl, huniq⟩ :=
      Constrained.existsUnique_stationary_lagrangian_second_of_isLocalMinOn
        hU hxU hf hc ⟨hx, hlicq⟩ hmin
    refine ⟨-l, ?_, ?_⟩
    · simpa only [lagrangian, neg_neg] using hl
    · intro a ha
      have hm : -a = l := huniq (-a) ha
      simpa using congrArg Neg.neg hm
  · intro hf hc y hstat hpos
    exact Constrained.isStrictLocalMinOn_of_contDiffOn_lagrangian_second_order
      hU hxU hf hc hx (-y) hstat hpos

end CartisGouldToint.Chapter01.Section01

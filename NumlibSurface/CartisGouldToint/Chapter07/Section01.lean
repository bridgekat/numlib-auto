import Numlib.Optimization.LagrangianMinimizer
import NumlibSurface.CartisGouldToint.Chapter01.Section01.KKTEquality
import NumlibSurface.CartisGouldToint.Chapter06.Section01

/-!
# General equality constraints and scaled Lagrangian criticality

The feasible set combines a simple set with actual vector equalities. The Lagrangian uses
the source minus sign and the earlier source definition, identified with the actual Euclidean
inner product. Scaled approximate KKT points need only approximate feasibility, and the
multiplier scale is the Euclidean norm of the augmented multiplier, rather than a product norm.
-/

noncomputable section
open Set
open scoped InnerProductSpace

namespace CartisGouldToint.Chapter07.Section01

variable {n m : ℕ}

/-- The actual feasible set `F(C,c)` of (7.1.1). -/
def generalFeasibleSet (C : Set (EuclideanSpace ℝ (Fin n)))
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) :
    Set (EuclideanSpace ℝ (Fin n)) := {x ∈ C | c x = 0}

/-- General feasibility means membership in the constraint set and vanishing constraints. -/
@[simp] theorem mem_generalFeasibleSet {C : Set (EuclideanSpace ℝ (Fin n))}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)} {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ generalFeasibleSet C c ↔ x ∈ C ∧ c x = 0 := Iff.rfl

/-- Vector feasibility is the intersection with the canonical component equality set. -/
theorem generalFeasibleSet_eq_inter (C : Set (EuclideanSpace ℝ (Fin n)))
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) :
    generalFeasibleSet C c = C ∩ Constrained.feasibleEq (fun i z => c z i) := by
  ext x
  constructor
  · rintro ⟨hx, hc⟩
    exact ⟨hx, fun i => by simp [hc]⟩
  · rintro ⟨hx, hc⟩
    refine ⟨hx, ?_⟩
    ext i
    exact hc i

/-- The vector-equality Lagrangian `f - inner y c`, reusing the earlier source convention. -/
def lagrangian (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) : ℝ :=
  Chapter01.Section01.lagrangian f (fun i z => c z i) x (fun i => y i)

/-- Identification with the source's actual Euclidean inner product. -/
theorem lagrangian_eq_sub_inner (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) :
    lagrangian f c x y = f x - inner ℝ y (c x) := by
  simp [lagrangian, Chapter01.Section01.lagrangian_eq_sub_sum, PiLp.inner_apply,
    RCLike.inner_apply, mul_comm]

/-- At a feasible point the actual source Lagrangian is the objective. -/
@[simp] theorem lagrangian_eq_of_feasible {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)} {x : EuclideanSpace ℝ (Fin n)}
    (hc : c x = 0) (y : EuclideanSpace ℝ (Fin m)) : lagrangian f c x y = f x := by
  simp [lagrangian_eq_sub_inner, hc]

/-- The actual derivative in the primal variable has the source minus sign. -/
theorem lagrangian_hasFDerivAt {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x : EuclideanSpace ℝ (Fin n)} {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    {c' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hf : HasFDerivAt f f' x) (hc : HasFDerivAt c c' x)
    (y : EuclideanSpace ℝ (Fin m)) :
    HasFDerivAt (fun z => lagrangian f c z y) (f' - (innerSL ℝ y).comp c') x := by
  have hd : HasFDerivAt (fun z => f z - inner ℝ y (c z))
      (f' - (innerSL ℝ y).comp c') x := by
    exact hf.sub ((innerSL ℝ y).hasFDerivAt.comp x hc)
  have heq : (fun z => lagrangian f c z y) = (fun z => f z - inner ℝ y (c z)) :=
    funext fun z => lagrangian_eq_sub_inner f c z y
  rw [heq]
  exact hd

/-- Theorem 7.1.1: a feasible Lagrangian minimizer on the closed subset `S` minimizes
`f` on `F(S,c)`. Closedness and containment retain the source statement; the canonical
restriction theorem needs neither. -/
theorem theorem_7_1_1 {C S : Set (EuclideanSpace ℝ (Fin n))}
    (_hS : IsClosed S) (_hSC : S ⊆ C) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x : EuclideanSpace ℝ (Fin n)} {y : EuclideanSpace ℝ (Fin m)} (hx : x ∈ S)
    (hc : c x = 0) (hmin : IsMinOn (fun z => lagrangian f c z y) S x) :
    x ∈ generalFeasibleSet S c ∧ IsMinOn f (generalFeasibleSet S c) x := by
  refine ⟨⟨hx, hc⟩, ?_⟩
  rw [generalFeasibleSet_eq_inter]
  exact Constrained.isMinOn_of_isMinOn_lagrangian
    (l := -(fun i => y i)) (by intro i; simp [hc]) hmin

/-- The Euclidean norm `||(y,1)||` in (7.1.4), with its precise scalar formula. -/
def multiplierScale (y : EuclideanSpace ℝ (Fin m)) : ℝ := Real.sqrt (‖y‖ ^ 2 + 1)

/-- Appending the last coordinate one gives exactly the stated Euclidean norm. -/
theorem multiplierScale_eq_norm_augmented (y : EuclideanSpace ℝ (Fin m)) :
    multiplierScale y = ‖(WithLp.toLp 2 (Fin.snoc (fun i => y i) (1 : ℝ)) :
      EuclideanSpace ℝ (Fin (m + 1)))‖ := by
  rw [EuclideanSpace.norm_eq, multiplierScale, EuclideanSpace.norm_sq_eq]
  congr 1
  rw [Fin.sum_univ_castSucc]
  simp

/-- Squaring the multiplier scale recovers the squared Euclidean norm plus one. -/
@[simp] theorem multiplierScale_sq (y : EuclideanSpace ℝ (Fin m)) :
    multiplierScale y ^ 2 = ‖y‖ ^ 2 + 1 := Real.sq_sqrt (by positivity)

/-- The appended coordinate one bounds the multiplier scale below by one. -/
theorem one_le_multiplierScale (y : EuclideanSpace ℝ (Fin m)) : 1 ≤ multiplierScale y :=
  Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg ‖y‖])

/-- The multiplier scale is strictly positive for every multiplier. -/
theorem multiplierScale_pos (y : EuclideanSpace ℝ (Fin m)) : 0 < multiplierScale y :=
  lt_of_lt_of_le zero_lt_one (one_le_multiplierScale y)

/-- The actual first-order Lagrangian measure from Chapter 6. -/
def lagrangianCriticality (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (C : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin m)) : ℝ :=
  Chapter06.Section01.constrainedCriticality (fun z => lagrangian f c z y) C x 0 0 0

/-- The source measure is precisely linear feasible-step criticality of the actual derivative. -/
theorem lagrangianCriticality_eq_feasibleCriticality (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (C : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin m)) : lagrangianCriticality f c C x y =
    Optimization.FeasibleCriticality.feasibleCriticality C x
      (fderiv ℝ (fun z => lagrangian f c z y) x) :=
  Chapter06.Section01.constrainedCriticality_first _ _ _ _ _

/-- The scaled approximate first-order conditions (7.1.4), including membership in `C`
and approximate feasibility. The explicit equality residual need not be zero. -/
structure IsScaledApproximateKKTPoint (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (C : Set (EuclideanSpace ℝ (Fin n))) (epsilon0 epsilon1 : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) : Prop where
  mem_constraint : x ∈ C
  residual_le : ‖c x‖ ≤ epsilon0
  criticality_le : lagrangianCriticality f c C x y ≤ epsilon1 * multiplierScale y

/-- Introduction and elimination of the complete scaled certificate. -/
theorem isScaledApproximateKKTPoint_iff {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {C : Set (EuclideanSpace ℝ (Fin n))} {epsilon0 epsilon1 : ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {y : EuclideanSpace ℝ (Fin m)} :
    IsScaledApproximateKKTPoint f c C epsilon0 epsilon1 x y ↔
      x ∈ C ∧ ‖c x‖ ≤ epsilon0 ∧
        lagrangianCriticality f c C x y ≤ epsilon1 * multiplierScale y :=
  ⟨fun h => ⟨h.mem_constraint, h.residual_le, h.criticality_le⟩,
    fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-- Enlarging the tolerances preserves a certificate. -/
theorem IsScaledApproximateKKTPoint.mono {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {C : Set (EuclideanSpace ℝ (Fin n))} {epsilon0 epsilon1 delta0 delta1 : ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {y : EuclideanSpace ℝ (Fin m)}
    (h : IsScaledApproximateKKTPoint f c C epsilon0 epsilon1 x y)
    (h0 : epsilon0 ≤ delta0) (h1 : epsilon1 ≤ delta1) :
    IsScaledApproximateKKTPoint f c C delta0 delta1 x y :=
  ⟨h.mem_constraint, h.residual_le.trans h0,
    h.criticality_le.trans (mul_le_mul_of_nonneg_right h1 (multiplierScale_pos y).le)⟩

/-- At zero tolerances this is exactly feasibility and zero Lagrangian criticality. -/
theorem isScaledApproximateKKTPoint_zero_iff {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {C : Set (EuclideanSpace ℝ (Fin n))} (hC : IsClosed C)
    {x : EuclideanSpace ℝ (Fin n)} {y : EuclideanSpace ℝ (Fin m)} :
    IsScaledApproximateKKTPoint f c C 0 0 x y ↔
      x ∈ C ∧ c x = 0 ∧ lagrangianCriticality f c C x y = 0 := by
  rw [isScaledApproximateKKTPoint_iff]
  simp only [zero_mul]
  constructor
  · rintro ⟨hx, hc, hw⟩
    refine ⟨hx, norm_le_zero_iff.mp hc, le_antisymm hw ?_⟩
    rw [lagrangianCriticality_eq_feasibleCriticality]
    exact Optimization.FeasibleCriticality.feasibleCriticality_nonneg hC hx _
  · rintro ⟨hx, hc, hw⟩
    simp [hx, hc, hw]

end CartisGouldToint.Chapter07.Section01

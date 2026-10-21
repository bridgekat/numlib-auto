import Numlib.Optimization.KKTSecondOrder
import NumlibSurface.CartisGouldToint.Chapter01.Section01.KKTEquality

/-!
# Inequality-constrained optimality conditions

The source convention is `c ≥ 0`, with Lagrangian `f - sum yᵢ cᵢ` and nonnegative
multipliers. Negating the inequality functions identifies it with canonical mixed KKT.
The source's unspecified constraint qualification is explicitly specialized to mixed LICQ.
Every derivative and feasible direction is actual; sufficiency does not require LICQ.
-/

noncomputable section
open Filter Topology Set

namespace CartisGouldToint.Chapter01.Section01

/-- Mixed LICQ for equalities `h = 0` and inequalities `c ≥ 0`, including feasibility.
The empty equality or inequality family specializes to the corresponding pure problem. -/
def constraintQualification {n me mi : ℕ}
    (h : Fin me → EuclideanSpace ℝ (Fin n) → ℝ)
    (c : Fin mi → EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  Constrained.IsRegularPointIneq h (fun i => fderiv ℝ (h i)) (fun j z => -c j z)
    (fun j => fderiv ℝ (fun z => -c j z)) x

/-- The actual feasible set for `c ≥ 0`; the canonical equality family is empty. -/
abbrev inequalityFeasible {n m : ℕ} (c : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  Constrained.feasible (fun _ : Fin 0 => fun _ => (0 : ℝ)) (fun j z => -c j z)

/-- Feasibility is exactly the source componentwise nonnegativity condition. -/
@[simp] theorem mem_inequalityFeasible {n m : ℕ}
    {c : Fin m → EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ inequalityFeasible c ↔ ∀ j, 0 ≤ c j x := by
  simp [inequalityFeasible, Constrained.feasible]

/-- The source KKT certificate, using actual canonical derivatives of `g = -c`. -/
abbrev InequalityKKTPoint {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (y : Fin m → ℝ) : Prop :=
  Constrained.IsKKTPoint (fderiv ℝ f) (fun _ : Fin 0 => fun _ => (0 : ℝ))
    (fun _ : Fin 0 => fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin n) => (0 : ℝ)))
    (fun j z => -c j z) (fun j => fderiv ℝ (fun z => -c j z)) x 0 y

/-- The source critical cone: active positive-multiplier constraints are linearized as
zero, while active zero-multiplier constraints have nonnegative first variation. -/
abbrev inequalityCriticalCone {n m : ℕ} (c : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (y : Fin m → ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  Constrained.kktCriticalCone
    (fun _ : Fin 0 => fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin n) => (0 : ℝ)))
    (fun j z => -c j z) (fun j => fderiv ℝ (fun z => -c j z)) x y

/-- The canonical empty-equality negative-constraint mixed Lagrangian has exactly the
source sign, as an equality of actual functions. -/
theorem mixedLagrangian_inequality_eq {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (l : Fin 0 → ℝ) (y : Fin m → ℝ) :
    Constrained.mixedLagrangian f (fun _ : Fin 0 => fun _ => (0 : ℝ))
      (fun j z => -c j z) l y = fun z => lagrangian f c z y := by
  funext z
  simp [Constrained.mixedLagrangian, Constrained.lagrangian, lagrangian, Finset.sum_neg_distrib]

/-- The critical cone is exactly the source's componentwise active-set condition. -/
@[simp] theorem mem_inequalityCriticalCone {n m : ℕ}
    {c : Fin m → EuclideanSpace ℝ (Fin n) → ℝ} {x d : EuclideanSpace ℝ (Fin n)}
    {y : Fin m → ℝ} : d ∈ inequalityCriticalCone c x y ↔
      ∀ j, c j x = 0 → (0 < y j → fderiv ℝ (c j) x d = 0) ∧
        (y j = 0 → 0 ≤ fderiv ℝ (c j) x d) := by
  simp [inequalityCriticalCone, Constrained.kktCriticalCone, Constrained.activeSet]

/-- The actual canonical certificate has precisely the source Lagrangian stationarity,
feasibility, nonnegative multipliers and source-sign complementarity. -/
theorem inequalityKKTPoint_iff {n m : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : Fin m → EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    {y : Fin m → ℝ} (hf : DifferentiableAt ℝ f x)
    (hc : ∀ j, DifferentiableAt ℝ (c j) x) :
    InequalityKKTPoint f c x y ↔ fderiv ℝ (fun z => lagrangian f c z y) x = 0 ∧
      (∀ j, 0 ≤ c j x) ∧ (∀ j, 0 ≤ y j) ∧ ∀ j, y j * c j x = 0 := by
  have hh : ∀ i : Fin 0, HasFDerivAt (fun _ : EuclideanSpace ℝ (Fin n) => (0 : ℝ))
      (fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin n) => (0 : ℝ)) x) x := fun i => Fin.elim0 i
  have hg := fun j => (hc j).neg.hasFDerivAt
  have hd := Constrained.mixedLagrangian_hasFDerivAt hf.hasFDerivAt hh hg (0 : Fin 0 → ℝ) y
  have hfun : Constrained.mixedLagrangian f
      (fun _ : Fin 0 => fun _ : EuclideanSpace ℝ (Fin n) => (0 : ℝ))
      (fun j => -c j) (0 : Fin 0 → ℝ) y = fun z => lagrangian f c z y := by
    funext z
    simp [Constrained.mixedLagrangian, Constrained.lagrangian, lagrangian,
      Finset.sum_neg_distrib]
  rw [hfun] at hd
  have heq := hd.fderiv
  constructor
  · intro hkkt
    refine ⟨heq.trans hkkt.stationary, ?_, hkkt.nonneg, fun j => ?_⟩
    · exact mem_inequalityFeasible.mp hkkt.mem_feasible
    · simpa only [mul_neg, neg_eq_zero] using hkkt.complementary j
  · rintro ⟨hstat, hfeas, hμ, hcompl⟩
    exact {
      feasible_eq := fun i => Fin.elim0 i
      feasible_ineq := fun j => neg_nonpos.mpr (hfeas j)
      stationary := heq.symm.trans hstat
      nonneg := hμ
      complementary := fun j => by simpa only [mul_neg, neg_eq_zero] using hcompl j }

/-- Componentwise complementarity gives the source's scalar multiplier inner product zero. -/
theorem InequalityKKTPoint.complementary_sum {n m : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : Fin m → EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    {y : Fin m → ℝ} (hkkt : InequalityKKTPoint f c x y) : ∑ j, y j * c j x = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  simpa only [mul_neg, neg_eq_zero] using hkkt.complementary j

/-- Mixed LICQ exposes exactly feasibility and independence of the actual active
constraint derivatives; it is a hypothesis, rather than a KKT conclusion. -/
theorem constraintQualification_iff {n me mi : ℕ}
    {h : Fin me → EuclideanSpace ℝ (Fin n) → ℝ}
    {c : Fin mi → EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)} :
    constraintQualification h c x ↔ (∀ i, h i x = 0) ∧ (∀ j, 0 ≤ c j x) ∧
      LinearIndependent ℝ (Sum.elim (fun i => fderiv ℝ (h i) x)
        (fun j : Constrained.activeSet (fun j z => -c j z) x =>
          fderiv ℝ (fun z => -c j z) x)) := by
  simp [constraintQualification, Constrained.IsRegularPointIneq]

/-- The C1 clause of Theorem 1.1.4, with the source's unspecified qualification
specialized explicitly to LICQ. Only a neighborhood of the minimizer is needed. -/
theorem exists_inequalityKKTPoint_of_isLocalMinOn {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {c : Fin m → EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hxU : x ∈ U) (hf : ContDiffOn ℝ 1 f U)
    (hc : ∀ j, ContDiffOn ℝ 1 (c j) U)
    (hqual : constraintQualification (fun _ : Fin 0 => fun _ => (0 : ℝ)) c x)
    (hmin : IsLocalMinOn f (inequalityFeasible c) x) :
    ∃ y, InequalityKKTPoint f c x y := by
  have hdf := (hf.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by norm_num)
  have hdc := fun j => ((hc j).neg.contDiffAt (hU.mem_nhds hxU)).hasStrictFDerivAt
    (by norm_num)
  obtain ⟨l, y, hkkt⟩ := Constrained.exists_kkt_of_isLocalMinOn hqual hmin hdf.hasFDerivAt
    (fun i : Fin 0 => Fin.elim0 i) hdc
  have hl : l = 0 := Subsingleton.elim _ _
  subst l
  exact ⟨y, hkkt⟩

/-- The C2 necessary clause of Theorem 1.1.4, on the exact source critical cone. -/
theorem exists_inequalityKKTPoint_second_of_isLocalMinOn {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {c : Fin m → EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hxU : x ∈ U) (hf : ContDiffOn ℝ 2 f U)
    (hc : ∀ j, ContDiffOn ℝ 2 (c j) U)
    (hqual : constraintQualification (fun _ : Fin 0 => fun _ => (0 : ℝ)) c x)
    (hmin : IsLocalMinOn f (inequalityFeasible c) x) :
    ∃ y, InequalityKKTPoint f c x y ∧ ∀ d ∈ inequalityCriticalCone c x y,
      0 ≤ fderiv ℝ (fderiv ℝ (fun z => lagrangian f c z y)) x d d := by
  obtain ⟨l, y, hkkt, hsecond⟩ := Constrained.exists_kkt_second_of_isLocalMinOn hU hxU hf
    (fun i : Fin 0 => Fin.elim0 i) (fun j => (hc j).neg) hqual hmin
  have hl : l = 0 := Subsingleton.elim _ _
  subst l
  refine ⟨y, hkkt, ?_⟩
  simpa only [mixedLagrangian_inequality_eq] using hsecond

/-- Strict second-order sufficiency in Theorem 1.1.4 needs no constraint qualification.
As usual, strict positivity is on nonzero critical directions. -/
theorem InequalityKKTPoint.isStrictLocalMinOn_of_posDef_second {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {c : Fin m → EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {U : Set (EuclideanSpace ℝ (Fin n))} {y : Fin m → ℝ}
    (hU : IsOpen U) (hxU : x ∈ U) (hf : ContDiffOn ℝ 2 f U)
    (hc : ∀ j, ContDiffOn ℝ 2 (c j) U) (hkkt : InequalityKKTPoint f c x y)
    (hpos : ∀ d ∈ inequalityCriticalCone c x y, d ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ (fun z => lagrangian f c z y)) x d d) :
    ∃ δ > 0, ∀ z ∈ inequalityFeasible c, dist z x < δ → z ≠ x → f x < f z := by
  apply hkkt.isStrictLocalMinOn_of_contDiffOn_posDef_second hU hxU hf
    (fun i : Fin 0 => Fin.elim0 i) (fun j => (hc j).neg)
  simpa only [mixedLagrangian_inequality_eq] using hpos

/-- Theorem 1.1.4: the C1 necessary KKT conditions, C2 necessity on the exact
critical cone, and C2 strict sufficiency. The qualification is explicit LICQ and is
used only for necessity. Smoothness on any open neighborhood suffices. -/
theorem theorem_1_1_4 {n m : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : Fin m → EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hxU : x ∈ U) :
    (ContDiffOn ℝ 1 f U → (∀ j, ContDiffOn ℝ 1 (c j) U) →
      constraintQualification (fun _ : Fin 0 => fun _ => (0 : ℝ)) c x →
      IsLocalMinOn f (inequalityFeasible c) x → ∃ y, InequalityKKTPoint f c x y) ∧
    (ContDiffOn ℝ 2 f U → (∀ j, ContDiffOn ℝ 2 (c j) U) →
      constraintQualification (fun _ : Fin 0 => fun _ => (0 : ℝ)) c x →
      IsLocalMinOn f (inequalityFeasible c) x →
      ∃ y, InequalityKKTPoint f c x y ∧ ∀ d ∈ inequalityCriticalCone c x y,
        0 ≤ fderiv ℝ (fderiv ℝ (fun z => lagrangian f c z y)) x d d) ∧
    (ContDiffOn ℝ 2 f U → (∀ j, ContDiffOn ℝ 2 (c j) U) → ∀ y,
      InequalityKKTPoint f c x y →
      (∀ d ∈ inequalityCriticalCone c x y, d ≠ 0 →
        0 < fderiv ℝ (fderiv ℝ (fun z => lagrangian f c z y)) x d d) →
      ∃ δ > 0, ∀ z ∈ inequalityFeasible c, dist z x < δ → z ≠ x → f x < f z) :=
  ⟨exists_inequalityKKTPoint_of_isLocalMinOn hU hxU,
    exists_inequalityKKTPoint_second_of_isLocalMinOn hU hxU,
    fun hf hc _ hkkt => hkkt.isStrictLocalMinOn_of_posDef_second hU hxU hf hc⟩

end CartisGouldToint.Chapter01.Section01

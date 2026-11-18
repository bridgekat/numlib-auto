/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.GeneralizedInverse
import Mathlib.Topology.Order.Compact

/-!
# Interval linear programming

Section 2.11 of [benIsrael2003generalized] reduces a bounded interval linear
program to an optimization over its attainable image coordinates. Full row
rank makes every point of the box attainable, and permits the coordinatewise
formula of Theorem 17.

## Deviations from the source

* In Exercises 103–104 the tests use the named vector `z₀`.
* Exercise 104 minimizes the objective. Its box selector therefore uses
  the negative of the projected objective vector.
-/

noncomputable section

namespace BenIsraelGreville.Chapter02

open Matrix Set

variable {m n : Type*} [Fintype m] [Fintype n]

/-- **Equations (137)–(138)** of [benIsrael2003generalized], Chapter 2.
The interval linear program has feasible points whose matrix images lie in the box. -/
def intervalProgram (a b : m → ℝ) (A : Matrix m n ℝ) : Set (n → ℝ) :=
  {x | A *ᵥ x ∈ Icc a b}

omit [Fintype m] in
/-- Feasibility is equivalent to satisfying both componentwise bounds. -/
theorem mem_intervalProgram_iff {a b : m → ℝ} {A : Matrix m n ℝ} {x : n → ℝ} :
    x ∈ intervalProgram a b A ↔ a ≤ A *ᵥ x ∧ A *ᵥ x ≤ b :=
  Iff.rfl

/-- The feasible images are the intersection of the box with the column space. -/
def intervalImageProgram (a b : m → ℝ) (A : Matrix m n ℝ) : Set (m → ℝ) :=
  Icc a b ∩ LinearMap.range A.mulVecLin

/-- A point is optimal when it is feasible and maximizes the objective over the feasible set. -/
def IsIntervalProgramOptimum (a b : m → ℝ) (c : n → ℝ) (A : Matrix m n ℝ)
    (x : n → ℝ) : Prop :=
  x ∈ intervalProgram a b A ∧ ∀ y ∈ intervalProgram a b A, c ⬝ᵥ y ≤ c ⬝ᵥ x

private theorem interval_apply_innerInverse {A : Matrix m n ℝ} {U : Matrix n m ℝ}
    (hU : A.IsInnerInverse U) (x : n → ℝ) :
    A *ᵥ (U *ᵥ (A *ᵥ x)) = A *ᵥ x := by
  rw [mulVec_mulVec, mulVec_mulVec, hU]

/-- The row space is exactly the set of objectives that vanish on null directions. -/
theorem interval_rowSpace_iff (A : Matrix m n ℝ) (c : n → ℝ) :
    c ∈ LinearMap.range Aᵀ.mulVecLin ↔ ∀ x, A *ᵥ x = 0 → c ⬝ᵥ x = 0 := by
  classical
  constructor
  · rintro ⟨d, rfl⟩ x hx
    change (Aᵀ *ᵥ d) ⬝ᵥ x = 0
    rw [dotProduct_comm, dotProduct_transpose_mulVec, hx, dotProduct_zero]
  · intro hc
    let U := A.pinv
    have hU : A.IsInnerInverse U := A.mul_pinv_mul_self
    refine ⟨Uᵀ *ᵥ c, ?_⟩
    change Aᵀ *ᵥ (Uᵀ *ᵥ c) = c
    have h (x : n → ℝ) : c ⬝ᵥ x = c ⬝ᵥ (U *ᵥ (A *ᵥ x)) := by
      have hz : A *ᵥ (x - U *ᵥ (A *ᵥ x)) = 0 := by
        rw [mulVec_sub, interval_apply_innerInverse hU, sub_self]
      exact sub_eq_zero.mp (by simpa only [dotProduct_sub] using hc _ hz)
    have ht (x : n → ℝ) : (Aᵀ *ᵥ (Uᵀ *ᵥ c)) ⬝ᵥ x = c ⬝ᵥ x := by
      rw [dotProduct_comm, dotProduct_transpose_mulVec, dotProduct_comm (Uᵀ *ᵥ c),
        dotProduct_transpose_mulVec]
      exact (h x).symm
    funext i
    simpa only [dotProduct_single_one] using ht (Pi.single i 1)

/-- On each fiber the objective of a bounded interval program can be evaluated
using any inner inverse, without changing its value. -/
theorem interval_objective_eq_innerInverse (A : Matrix m n ℝ) (c : n → ℝ)
    (hc : c ∈ LinearMap.range Aᵀ.mulVecLin) {U : Matrix n m ℝ} (hU : A.IsInnerInverse U)
    (x : n → ℝ) :
    c ⬝ᵥ x = c ⬝ᵥ (U *ᵥ (A *ᵥ x)) := by
  have hz : A *ᵥ (x - U *ᵥ (A *ᵥ x)) = 0 := by
    rw [mulVec_sub, interval_apply_innerInverse hU, sub_self]
  exact sub_eq_zero.mp (by simpa only [dotProduct_sub] using (interval_rowSpace_iff A c).mp hc _ hz)

private theorem continuous_interval_objective (c : n → ℝ) :
    Continuous (fun x => c ⬝ᵥ x) :=
  continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)

/-- **Lemma 5** of [benIsrael2003generalized], Chapter 2.
For a feasible interval program the objective is bounded above exactly
when its coefficient vector lies in the row space. -/
theorem lemma_5 (a b : m → ℝ) (c : n → ℝ) (A : Matrix m n ℝ)
    (hF : (intervalProgram a b A).Nonempty) :
    BddAbove ((fun x => c ⬝ᵥ x) '' intervalProgram a b A) ↔
      c ∈ LinearMap.range Aᵀ.mulVecLin := by
  constructor
  · intro hb
    obtain ⟨x, hx⟩ := hF
    obtain ⟨B, hB⟩ := hb
    apply (interval_rowSpace_iff A c).mpr
    intro v hv
    by_contra hcv
    let t := (B + 1 - c ⬝ᵥ x) / (c ⬝ᵥ v)
    have hF' : x + t • v ∈ intervalProgram a b A := by
      change A *ᵥ (x + t • v) ∈ Icc a b
      rw [mulVec_add, mulVec_smul, hv, smul_zero, add_zero]
      exact hx
    have hle := hB (mem_image_of_mem _ hF')
    have he : c ⬝ᵥ (x + t • v) = B + 1 := by
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
      dsimp [t]
      rw [div_mul_cancel₀ _ hcv]
      ring
    linarith
  · rintro ⟨d, rfl⟩
    obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image (continuous_interval_objective d).continuousOn
      (K := Icc a b)
    refine ⟨B, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    change (Aᵀ *ᵥ d) ⬝ᵥ x ≤ B
    rw [dotProduct_comm, dotProduct_transpose_mulVec]
    exact hB (mem_image_of_mem _ (show A *ᵥ x ∈ Icc a b from hx))

/-- The coordinate selector in **Equation (140)**. A zero weight permits
any point in the closed segment between the two endpoints. -/
def coordinateIntervalSelector (a b w : m → ℝ) : Set (m → ℝ) :=
  {u | ∀ i, (w i < 0 → u i = a i) ∧ (0 < w i → u i = b i) ∧
    (w i = 0 → u i ∈ uIcc (a i) (b i))}

/-- A point of the box maximizes its linear objective precisely by using the lower
endpoint at negative weights and the upper endpoint at positive weights. -/
def intervalSelector (a b w : m → ℝ) : Set (m → ℝ) :=
  {u | u ∈ Icc a b ∧ (∀ i, w i < 0 → u i = a i) ∧ (∀ i, 0 < w i → u i = b i)}

omit [Fintype m] in
/-- For ordered endpoints the coordinate selector lies in the box and
coincides with the box selector. -/
theorem intervalSelector_eq_coordinateIntervalSelector {a b w : m → ℝ} (hab : a ≤ b) :
    intervalSelector a b w = coordinateIntervalSelector a b w := by
  ext u
  constructor
  · rintro ⟨hu, ha, hb⟩ i
    refine ⟨ha i, hb i, fun _ => ?_⟩
    rw [uIcc_of_le (hab i)]
    exact ⟨hu.1 i, hu.2 i⟩
  · intro h
    have hs (i : m) : u i ∈ Icc (a i) (b i) := by
      rcases lt_trichotomy (w i) 0 with hn | hz | hp
      · rw [(h i).1 hn]
        exact left_mem_Icc.mpr (hab i)
      · simpa only [uIcc_of_le (hab i)] using (h i).2.2 hz
      · rw [(h i).2.1 hp]
        exact right_mem_Icc.mpr (hab i)
    exact ⟨⟨fun i => (hs i).1, fun i => (hs i).2⟩, fun i => (h i).1, fun i => (h i).2.1⟩

/-- **Equation (140)** of [benIsrael2003generalized], Chapter 2.
The selector is the entire set of maximizers of a linear objective over the box. -/
theorem mem_intervalSelector_iff {a b w u : m → ℝ} :
    u ∈ intervalSelector a b w ↔
      u ∈ Icc a b ∧ ∀ v ∈ Icc a b, w ⬝ᵥ v ≤ w ⬝ᵥ u := by
  classical
  constructor
  · rintro ⟨hu, hlo, hhi⟩
    refine ⟨hu, fun v hv => Finset.sum_le_sum fun i _ => ?_⟩
    rcases lt_trichotomy (w i) 0 with hi | hi | hi
    · rw [hlo i hi]
      exact mul_le_mul_of_nonpos_left (hv.1 i) hi.le
    · simp [hi]
    · rw [hhi i hi]
      exact mul_le_mul_of_nonneg_left (hv.2 i) hi.le
  · rintro ⟨hu, hmax⟩
    have hc (i : m) (s : ℝ) (hs : s ∈ Icc (a i) (b i)) : w i * s ≤ w i * u i := by
      let v := Function.update u i s
      have hv : v ∈ Icc a b := by
        constructor <;> intro j <;> by_cases hji : j = i
        · simpa [v, hji] using hs.1
        · simpa [v, Function.update_of_ne hji] using hu.1 j
        · simpa [v, hji] using hs.2
        · simpa [v, Function.update_of_ne hji] using hu.2 j
      have hv' : v = u + Pi.single i (s - u i) := by
        funext j
        by_cases hji : j = i
        · subst j
          simp [v]
        · simp [v, Function.update_of_ne hji, Pi.single_eq_of_ne hji]
      have h := hmax _ hv
      rw [hv', dotProduct_add, dotProduct_single] at h
      nlinarith
    refine ⟨hu, ?_, ?_⟩
    · intro i hi
      apply le_antisymm _ (hu.1 i)
      by_contra! hlt
      exact (not_lt_of_ge (hc i (a i) ⟨le_rfl, (hu.1 i).trans (hu.2 i)⟩))
        (mul_lt_mul_of_neg_left hlt hi)
    · intro i hi
      apply le_antisymm (hu.2 i)
      exact (mul_le_mul_iff_of_pos_left hi).mp (hc i (b i) ⟨(hu.1 i).trans (hu.2 i), le_rfl⟩)

/-- The feasible points over an attainable image are obtained by adding arbitrary null vectors. -/
theorem intervalProgram_fiber {A : Matrix m n ℝ} {U : Matrix n m ℝ}
    (hU : A.IsInnerInverse U) {u : m → ℝ} (hu : u ∈ LinearMap.range A.mulVecLin)
    (x : n → ℝ) :
    A *ᵥ x = u ↔ ∃ y, A *ᵥ y = 0 ∧ x = U *ᵥ u + y := by
  obtain ⟨w, hw⟩ := hu
  change A *ᵥ w = u at hw
  have h : A *ᵥ (U *ᵥ u) = u := by rw [← hw, interval_apply_innerInverse hU]
  constructor
  · intro hx
    refine ⟨x - U *ᵥ u, by rw [mulVec_sub, hx, h, sub_self], ?_⟩
    abel
  · rintro ⟨y, hy, rfl⟩
    rw [mulVec_add, h, hy, add_zero]

/-- For arbitrary rank, a feasible point is optimal precisely when its image
optimizes the induced objective on the box intersected with the column space. -/
theorem intervalProgram_optimum_image (a b : m → ℝ) (c : n → ℝ) (A : Matrix m n ℝ)
    (hc : c ∈ LinearMap.range Aᵀ.mulVecLin) {U : Matrix n m ℝ} (hU : A.IsInnerInverse U)
    (x : n → ℝ) :
    IsIntervalProgramOptimum a b c A x ↔ A *ᵥ x ∈ intervalImageProgram a b A ∧
      ∀ v ∈ intervalImageProgram a b A, (Uᵀ *ᵥ c) ⬝ᵥ v ≤ (Uᵀ *ᵥ c) ⬝ᵥ (A *ᵥ x) := by
  have he (z : n → ℝ) : (Uᵀ *ᵥ c) ⬝ᵥ (A *ᵥ z) = c ⬝ᵥ z := by
    rw [dotProduct_comm, dotProduct_transpose_mulVec]
    exact (interval_objective_eq_innerInverse A c hc hU z).symm
  constructor
  · rintro ⟨hx, hopt⟩
    refine ⟨⟨hx, ⟨x, rfl⟩⟩, ?_⟩
    rintro v ⟨hv, ⟨y, rfl⟩⟩
    change (Uᵀ *ᵥ c) ⬝ᵥ (A *ᵥ y) ≤ (Uᵀ *ᵥ c) ⬝ᵥ (A *ᵥ x)
    rw [he y, he x]
    exact hopt y hv
  · rintro ⟨hx, hopt⟩
    refine ⟨hx.1, fun y hy => ?_⟩
    rw [← he x, ← he y]
    exact hopt _ ⟨hy, y, rfl⟩

/-- **Theorem 17, Equation (141)** of [benIsrael2003generalized], Chapter 2.
When `A` has full row rank, the optimal solutions are all lifts of points
selected by the sign of the induced box objective. -/
theorem theorem_17 (a b : m → ℝ) (c : n → ℝ) (A : Matrix m n ℝ)
    (hF : (intervalProgram a b A).Nonempty)
    (hb : BddAbove ((fun x => c ⬝ᵥ x) '' intervalProgram a b A))
    (hA : Function.Surjective A.mulVecLin) {U : Matrix n m ℝ} (hU : A.IsInnerInverse U)
    (x : n → ℝ) :
    IsIntervalProgramOptimum a b c A x ↔
      ∃ u ∈ intervalSelector a b (Uᵀ *ᵥ c), ∃ y, A *ᵥ y = 0 ∧ x = U *ᵥ u + y := by
  have hc := (lemma_5 a b c A hF).mp hb
  have hr (u : m → ℝ) : u ∈ LinearMap.range A.mulVecLin := hA u
  have hi (u : m → ℝ) : u ∈ intervalImageProgram a b A ↔ u ∈ Icc a b :=
    and_iff_left (hr u)
  rw [intervalProgram_optimum_image a b c A hc hU]
  simp only [hi]
  rw [← mem_intervalSelector_iff]
  constructor
  · intro hx
    exact ⟨A *ᵥ x, hx, (intervalProgram_fiber hU (hr _) x).mp rfl⟩
  · rintro ⟨u, hu, hy⟩
    rw [(intervalProgram_fiber hU (hr u) x).mpr hy]
    exact hu

omit [Fintype m] in
/-- A feasible interval program with a bounded objective attains its maximum. -/
theorem exists_intervalProgramOptimum [Finite m] (a b : m → ℝ) (c : n → ℝ) (A : Matrix m n ℝ)
    (hF : (intervalProgram a b A).Nonempty)
    (hb : BddAbove ((fun x => c ⬝ᵥ x) '' intervalProgram a b A)) :
    ∃ x, IsIntervalProgramOptimum a b c A x := by
  classical
  let _ : Fintype m := Fintype.ofFinite m
  let U := A.pinv
  have hU : A.IsInnerInverse U := A.mul_pinv_mul_self
  have hc := (lemma_5 a b c A hF).mp hb
  have hK : IsCompact (intervalImageProgram a b A) :=
    isCompact_Icc.inter_right (LinearMap.range A.mulVecLin).closed_of_finiteDimensional
  obtain ⟨x₀, hx₀⟩ := hF
  have hx : A *ᵥ x₀ ∈ intervalImageProgram a b A := ⟨hx₀, x₀, rfl⟩
  obtain ⟨u, hu, hmax⟩ := hK.exists_isMaxOn ⟨_, hx⟩
    (continuous_interval_objective (Uᵀ *ᵥ c)).continuousOn
  obtain ⟨x, hAx⟩ := hu.2
  change A *ᵥ x = u at hAx
  refine ⟨x, (intervalProgram_optimum_image a b c A hc hU x).mpr ?_⟩
  exact hAx.symm ▸ ⟨hu, fun v hv => hmax hv⟩

variable [DecidableEq n]

/-- **Exercise 103** of [benIsrael2003generalized], Chapter 2.
The box selector with a left-null-space perturbation certifies optimality
whenever its proposed lift is feasible. -/
theorem exercise_103 (a b : m → ℝ) (c : n → ℝ) (A : Matrix m n ℝ)
    (hc : c ∈ LinearMap.range Aᵀ.mulVecLin) {U : Matrix n m ℝ} (hU : A.IsInnerInverse U)
    (z η : m → ℝ) (hz : Aᵀ *ᵥ z = 0)
    (hη : η ∈ intervalSelector a b (((U * (A * A.pinv))ᵀ *ᵥ c) + z))
    (hηz : z ⬝ᵥ η ≤ 0) (y : n → ℝ) (hy : A *ᵥ y = 0) :
    let x := U *ᵥ ((A * A.pinv) *ᵥ η) + y
    IsIntervalProgramOptimum a b c A x ↔ x ∈ intervalProgram a b A := by
  let P := A * A.pinv
  intro x
  constructor
  · exact And.left
  · intro hx
    refine ⟨hx, fun v hv => ?_⟩
    have hP : P *ᵥ (A *ᵥ v) = A *ᵥ v := by
      rw [mulVec_mulVec, show P * A = A from A.mul_pinv_mul_self]
    have hzv : z ⬝ᵥ (A *ᵥ v) = 0 := by
      rw [← dotProduct_transpose_mulVec, hz, dotProduct_zero]
    have h := (mem_intervalSelector_iff.mp hη).2 _ hv
    rw [add_dotProduct, add_dotProduct, hzv, add_zero] at h
    have he (u : m → ℝ) : ((U * P)ᵀ *ᵥ c) ⬝ᵥ u = c ⬝ᵥ (U *ᵥ (P *ᵥ u)) := by
      rw [dotProduct_comm, dotProduct_transpose_mulVec, mulVec_mulVec]
    rw [he, he, hP, ← interval_objective_eq_innerInverse A c hc hU] at h
    change c ⬝ᵥ v ≤ c ⬝ᵥ (U *ᵥ (P *ᵥ η) + y)
    rw [dotProduct_add, (interval_rowSpace_iff A c).mp hc y hy, add_zero]
    linarith

/-- **Exercise 104** of [benIsrael2003generalized], Chapter 2.
For the equality-constrained box problem, the sign selector with the
negative projected cost certifies a minimum whenever its lift is feasible. -/
theorem exercise_104 (A : Matrix m n ℝ) (b : m → ℝ) (c u : n → ℝ)
    (hF : ∃ v : n → ℝ, A *ᵥ v = b ∧ v ∈ Icc (0 : n → ℝ) u)
    (z η : n → ℝ) (hz : z ∈ LinearMap.range Aᵀ.mulVecLin)
    (hη : η ∈ intervalSelector 0 u (-((1 - A.pinv * A) *ᵥ c) + z))
    (hηz : z ⬝ᵥ η ≤ z ⬝ᵥ (A.pinv *ᵥ b)) :
    let x := A.pinv *ᵥ b + (1 - A.pinv * A) *ᵥ η
    ((A *ᵥ x = b ∧ x ∈ Icc 0 u) ∧
      ∀ v : n → ℝ, A *ᵥ v = b → v ∈ Icc (0 : n → ℝ) u → c ⬝ᵥ x ≤ c ⬝ᵥ v) ↔
      A *ᵥ x = b ∧ x ∈ Icc 0 u := by
  let P : Matrix n n ℝ := 1 - A.pinv * A
  let p := A.pinv *ᵥ b
  intro x
  constructor
  · exact And.left
  · intro hx
    refine ⟨hx, fun v hv hbox => ?_⟩
    have hAp : A *ᵥ p = b := by
      obtain ⟨v₀, hv₀, _⟩ := hF
      rw [show p = A.pinv *ᵥ b from rfl, ← hv₀]
      exact interval_apply_innerInverse A.mul_pinv_mul_self v₀
    have hzv : z ⬝ᵥ v = z ⬝ᵥ p := by
      have he : A *ᵥ (v - p) = 0 := by rw [mulVec_sub, hv, hAp, sub_self]
      exact sub_eq_zero.mp (by simpa only [dotProduct_sub] using
        (interval_rowSpace_iff A z).mp hz _ he)
    have hPT : Pᵀ = P := by
      change (1 - A.pinv * A)ᵀ = 1 - A.pinv * A
      rw [transpose_sub, transpose_one, A.isHermitian_pinv_mul.isSymm.eq]
    have hP (w : n → ℝ) : (P *ᵥ c) ⬝ᵥ w = c ⬝ᵥ (P *ᵥ w) := by
      rw [← hPT, dotProduct_comm, dotProduct_transpose_mulVec, hPT]
    have hPv : P *ᵥ v = v - p := by
      change (1 - A.pinv * A) *ᵥ v = _
      rw [sub_mulVec, one_mulVec, ← mulVec_mulVec, hv]
    have hi := (mem_intervalSelector_iff.mp hη).2 _ hbox
    change (- (P *ᵥ c) + z) ⬝ᵥ v ≤ (- (P *ᵥ c) + z) ⬝ᵥ η at hi
    rw [add_dotProduct, add_dotProduct, neg_dotProduct, neg_dotProduct, hP, hP, hzv, hPv,
      dotProduct_sub] at hi
    change c ⬝ᵥ (p + P *ᵥ η) ≤ c ⬝ᵥ v
    rw [dotProduct_add]
    exact by linarith

end BenIsraelGreville.Chapter02

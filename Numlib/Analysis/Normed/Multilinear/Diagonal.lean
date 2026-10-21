import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Diagonal evaluations of continuous multilinear maps

The diagonal of a continuous multilinear map is homogeneous. Its unit-sphere supremum is
bounded by the multilinear operator norm and is attained in finite-dimensional nontrivial
spaces. The diagonal zero set is a closed set stable under scalar multiplication; it need
not be a submodule. The supremum includes zero, giving value zero when the sphere is empty.
-/

noncomputable section

namespace ContinuousMultilinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℕ}

/-- Invariance under all permutations of the arguments. -/
def IsSymmetric (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) F) : Prop :=
  ∀ (σ : Equiv.Perm (Fin p)) (v : Fin p → E), T (v ∘ σ) = T v

/-- Symmetric continuous multilinear maps form a submodule of all continuous multilinear maps.
The inherited norm is the multilinear operator norm. -/
def symmetricSubmodule : Submodule ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin p => E) F) where
  carrier := {T | T.IsSymmetric}
  zero_mem' := by intro σ v; rfl
  add_mem' := by
    intro T S hT hS σ v
    change T (v ∘ σ) + S (v ∘ σ) = T v + S v
    rw [hT σ v, hS σ v]
  smul_mem' := by
    intro c T hT σ v
    change c • T (v ∘ σ) = c • T v
    rw [hT σ v]

/-- Membership in the symmetric submodule is permutation invariance. -/
@[simp] theorem mem_symmetricSubmodule
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) F) :
    T ∈ symmetricSubmodule ↔ T.IsSymmetric := Iff.rfl

/-- Evaluate a multilinear map on repeated copies of one vector. -/
def diagonal (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) F) (v : E) : F :=
  T (fun _ => v)

/-- The defining evaluation formula for the diagonal. -/
theorem diagonal_apply (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) F)
    (v : E) : T.diagonal v = T (fun _ => v) := rfl

/-- Evaluation on the diagonal respects addition of multilinear maps. -/
@[simp] theorem diagonal_add
    (T S : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) F) (v : E) :
    (T + S).diagonal v = T.diagonal v + S.diagonal v := rfl

/-- Evaluation on the diagonal respects subtraction of multilinear maps. -/
@[simp] theorem diagonal_sub
    (T S : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) F) (v : E) :
    (T - S).diagonal v = T.diagonal v - S.diagonal v := rfl

/-- Evaluation on the diagonal respects scalar multiplication of multilinear maps. -/
@[simp] theorem diagonal_smul_map
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) F) (c : ℝ) (v : E) :
    (c • T).diagonal v = c • T.diagonal v := rfl

/-- A diagonal evaluation is a continuous homogeneous polynomial. -/
theorem continuous_diagonal (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) F) :
    Continuous T.diagonal := T.cont.comp (continuous_pi fun _ => continuous_id)

/-- Homogeneity of the diagonal of an order-`p` multilinear map. -/
@[simp] theorem diagonal_smul (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) F)
    (c : ℝ) (v : E) : T.diagonal (c • v) = c ^ p • T.diagonal v := by
  simpa [diagonal] using T.map_smul_univ (fun _ => c) (fun _ => v)

/-- Positive-order diagonals vanish at zero. -/
@[simp] theorem diagonal_zero (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) F)
    (hp : 0 < p) : T.diagonal 0 = 0 := by
  exact T.map_coord_zero ⟨0, hp⟩ rfl

/-- Order-zero diagonals are constant, including on the zero-dimensional space. -/
theorem diagonal_order_zero (T : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) F)
    (v : E) : T.diagonal v = T.diagonal 0 := by
  change T (fun _ => v) = T (fun _ => 0)
  congr 1
  exact funext fun i => Fin.elim0 i

/-- The operator norm bounds a diagonal evaluation. -/
theorem norm_diagonal_le (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) F)
    (v : E) : ‖T.diagonal v‖ ≤ ‖T‖ * ‖v‖ ^ p := by
  simpa [diagonal] using T.le_opNorm (fun _ => v)

/-- The supremum of norms of unit-sphere diagonal values, with zero adjoined so the value
is zero when the unit sphere is empty. This does not assert equality with the operator norm. -/
def diagonalNorm (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) F) : ℝ :=
  sSup (insert 0 ((fun v => ‖T.diagonal v‖) '' Metric.sphere 0 1))

private theorem diagonalNorm_bddAbove
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) F) :
    BddAbove (insert 0 ((fun v => ‖T.diagonal v‖) '' Metric.sphere 0 1)) := by
  refine ⟨‖T‖, ?_⟩
  rintro x (rfl | ⟨v, hv, rfl⟩)
  · exact norm_nonneg _
  · have hv' : ‖v‖ = 1 := by simpa using hv
    simpa [hv'] using T.norm_diagonal_le v

/-- The diagonal supremum is nonnegative, even on a space with empty unit sphere. -/
theorem diagonalNorm_nonneg (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) F) :
    0 ≤ T.diagonalNorm := le_csSup T.diagonalNorm_bddAbove (Set.mem_insert _ _)

/-- A unit vector's diagonal value is bounded by the diagonal supremum. -/
theorem norm_diagonal_le_diagonalNorm
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) F) {v : E} (hv : ‖v‖ = 1) :
    ‖T.diagonal v‖ ≤ T.diagonalNorm := by
  apply le_csSup T.diagonalNorm_bddAbove
  exact Set.mem_insert_of_mem _ ⟨v, by simpa using hv, rfl⟩

/-- The diagonal supremum is bounded by the multilinear operator norm. -/
theorem diagonalNorm_le_norm (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) F) :
    T.diagonalNorm ≤ ‖T‖ := by
  apply csSup_le (Set.insert_nonempty _ _)
  rintro x (rfl | ⟨v, hv, rfl⟩)
  · exact norm_nonneg _
  · have hv' : ‖v‖ = 1 := by simpa using hv
    simpa [hv'] using T.norm_diagonal_le v

/-- Bounding all unit-sphere diagonal values bounds their supremum. -/
theorem diagonalNorm_le (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) F)
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ v : E, ‖v‖ = 1 → ‖T.diagonal v‖ ≤ C) :
    T.diagonalNorm ≤ C := by
  apply csSup_le (Set.insert_nonempty _ _)
  rintro x (rfl | ⟨v, hv, rfl⟩)
  · exact hC
  · exact h v (by simpa using hv)

/-- Diagonal suprema change by at most the operator norm of the difference. -/
theorem diagonalNorm_le_diagonalNorm_add_norm_sub
    (T S : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) F) :
    T.diagonalNorm ≤ S.diagonalNorm + ‖T - S‖ := by
  apply T.diagonalNorm_le (add_nonneg S.diagonalNorm_nonneg (norm_nonneg _))
  intro v hv
  have h := (T - S).norm_diagonal_le v
  simp only [diagonal_sub, hv, one_pow, mul_one] at h
  exact (norm_le_norm_add_norm_sub' (T.diagonal v) (S.diagonal v)).trans
    (add_le_add (S.norm_diagonal_le_diagonalNorm hv) h)

/-- The diagonal supremum is one-Lipschitz in the multilinear operator norm. -/
theorem lipschitzWith_diagonalNorm :
    LipschitzWith 1 (diagonalNorm : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) F → ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro T S
  simp only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul]
  apply abs_sub_le_iff.mpr
  constructor
  · linarith [T.diagonalNorm_le_diagonalNorm_add_norm_sub S]
  · have h := S.diagonalNorm_le_diagonalNorm_add_norm_sub T
    rw [norm_sub_rev] at h
    linarith

/-- Continuity of the unit-sphere diagonal supremum as a function of the tensor. -/
theorem continuous_diagonalNorm :
    Continuous (diagonalNorm : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) F → ℝ) :=
  lipschitzWith_diagonalNorm.continuous

/-- In finite dimensions, a nonempty unit sphere contains a maximizing diagonal vector. -/
theorem exists_norm_diagonal_eq_diagonalNorm [FiniteDimensional ℝ E] [Nontrivial E]
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) F) :
    ∃ v : E, ‖v‖ = 1 ∧ ‖T.diagonal v‖ = T.diagonalNorm := by
  obtain ⟨v, hv, hmax⟩ := (isCompact_sphere (0 : E) 1).exists_isMaxOn
    (NormedSpace.sphere_nonempty.mpr zero_le_one) T.continuous_diagonal.norm.continuousOn
  have hv' : ‖v‖ = 1 := by simpa using hv
  refine ⟨v, hv', le_antisymm (T.norm_diagonal_le_diagonalNorm hv') ?_⟩
  exact T.diagonalNorm_le (norm_nonneg _) fun w hw => hmax (by simpa using hw)

/-- On a subsingleton space the unit sphere is empty, and its diagonal supremum is zero. -/
@[simp] theorem diagonalNorm_of_subsingleton [Subsingleton E]
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) F) : T.diagonalNorm = 0 := by
  have hs : Metric.sphere (0 : E) 1 = ∅ := by
    ext v
    simp [Subsingleton.elim v 0]
  simp [diagonalNorm, hs]

/-- The sphere supremum controls every diagonal value by homogeneity. Positive order is
needed only to ensure the zero-vector value vanishes when the unit sphere is empty. -/
theorem norm_diagonal_le_diagonalNorm_mul
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) F) (hp : 0 < p) (v : E) :
    ‖T.diagonal v‖ ≤ T.diagonalNorm * ‖v‖ ^ p := by
  by_cases hv : v = 0
  · simp [hv, T.diagonal_zero hp, Nat.ne_of_gt hp]
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hu : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
    simp [norm_smul, hn]
  have he : v = ‖v‖ • ((‖v‖⁻¹ : ℝ) • v) := by simp [smul_smul, hn]
  calc
    ‖T.diagonal v‖ = ‖v‖ ^ p * ‖T.diagonal ((‖v‖⁻¹ : ℝ) • v)‖ := by
      conv_lhs => rw [he, T.diagonal_smul]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg v) p)]
    _ ≤ ‖v‖ ^ p * T.diagonalNorm :=
      mul_le_mul_of_nonneg_left (T.norm_diagonal_le_diagonalNorm hu) (pow_nonneg (norm_nonneg v) p)
    _ = T.diagonalNorm * ‖v‖ ^ p := mul_comm _ _

/-- A nonnegative constant bounds the diagonal supremum exactly when it gives a global
homogeneous diagonal bound. No symmetry or inner product assumption is needed. -/
theorem diagonalNorm_le_iff
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) F) (hp : 0 < p)
    {C : ℝ} (hC : 0 ≤ C) :
    T.diagonalNorm ≤ C ↔ ∀ v : E, ‖T.diagonal v‖ ≤ C * ‖v‖ ^ p := by
  constructor
  · intro h v
    exact (T.norm_diagonal_le_diagonalNorm_mul hp v).trans
      (mul_le_mul_of_nonneg_right h (pow_nonneg (norm_nonneg v) p))
  · intro h
    exact T.diagonalNorm_le hC fun v hv => by simpa [hv] using h v

/-- In order one the diagonal supremum always equals the operator norm, on any real normed
space, including the zero-dimensional space. -/
theorem diagonalNorm_order_one
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) F) : T.diagonalNorm = ‖T‖ := by
  apply le_antisymm T.diagonalNorm_le_norm
  apply opNorm_le_bound T.diagonalNorm_nonneg
  intro m
  have hm : m = fun _ => m 0 := funext fun i => congrArg m (Subsingleton.elim i 0)
  rw [hm]
  simpa [diagonal] using T.norm_diagonal_le_diagonalNorm_mul (by decide) (m 0)

/-- The operator norm of an order-zero multilinear map is the norm of its constant value. -/
theorem norm_order_zero (T : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) F) :
    ‖T‖ = ‖T.diagonal 0‖ := by
  apply le_antisymm
  · apply opNorm_le_bound (norm_nonneg _)
    intro m
    have hm : m = fun _ => 0 := funext fun i => Fin.elim0 i
    simp [hm, diagonal]
  · simpa using T.norm_diagonal_le (0 : E)

/-- On nontrivial spaces the order-zero sphere supremum is the norm of the constant value. -/
theorem diagonalNorm_order_zero [Nontrivial E]
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) F) :
    T.diagonalNorm = ‖T.diagonal 0‖ := by
  obtain ⟨v, hv⟩ := NormedSpace.sphere_nonempty (x := (0 : E)).mpr zero_le_one
  apply le_antisymm
  · exact T.diagonalNorm_le (norm_nonneg _) fun w _ => (congrArg norm (T.diagonal_order_zero w)).le
  · rw [← T.diagonal_order_zero v]
    exact T.norm_diagonal_le_diagonalNorm (by simpa using hv)

/-- The diagonal zero set of a multilinear map. -/
def diagonalZeroSet (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) F) : Set E :=
  {v | T.diagonal v = 0}

/-- Membership in the diagonal zero set is the vanishing of the diagonal value. -/
@[simp] theorem mem_diagonalZeroSet
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) F) (v : E) :
    v ∈ T.diagonalZeroSet ↔ T.diagonal v = 0 := Iff.rfl

/-- In order one the diagonal is a continuous linear map. -/
def diagonalLinearMap (T : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) F) :
    E →L[ℝ] F := (ofSubsingleton ℝ E F (0 : Fin 1)).symm T

/-- The order-one linear map evaluates to the diagonal. -/
@[simp] theorem diagonalLinearMap_apply
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) F) (v : E) :
    T.diagonalLinearMap v = T.diagonal v := rfl

/-- In order one the diagonal zero set is the kernel of a continuous linear map. -/
theorem diagonalZeroSet_order_one
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) F) :
    T.diagonalZeroSet = (T.diagonalLinearMap.ker : Set E) := rfl

/-- Positive-order diagonal zero sets contain the origin. -/
theorem zero_mem_diagonalZeroSet
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) F) (hp : 0 < p) :
    0 ∈ T.diagonalZeroSet := T.diagonal_zero hp

/-- Continuity makes the diagonal zero set closed. -/
theorem isClosed_diagonalZeroSet
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) F) :
    IsClosed T.diagonalZeroSet := isClosed_eq T.continuous_diagonal continuous_const

/-- Diagonal zero sets are stable under every scalar multiplication. -/
theorem smul_mem_diagonalZeroSet
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) F) {v : E}
    (hv : v ∈ T.diagonalZeroSet) (c : ℝ) : c • v ∈ T.diagonalZeroSet := by
  change T.diagonal v = 0 at hv
  change T.diagonal (c • v) = 0
  rw [diagonal_smul, hv, smul_zero]

end ContinuousMultilinearMap

namespace ContinuousMultilinearMap

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Pulling all arguments back by a contraction cannot increase the positive-order
unit-sphere diagonal supremum. -/
theorem diagonalNorm_compContinuousLinearMap_le {p : ℕ} (hp : 0 < p)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) G) (L : F →L[ℝ] E)
    (hL : ‖L‖ ≤ 1) :
    (T.compContinuousLinearMap (fun _ => L)).diagonalNorm ≤ T.diagonalNorm := by
  apply diagonalNorm_le _ T.diagonalNorm_nonneg
  intro v hv
  change ‖T.diagonal (L v)‖ ≤ T.diagonalNorm
  have hLv : ‖L v‖ ≤ 1 := (L.le_opNorm v).trans (by simpa [hv] using hL)
  calc
    ‖T.diagonal (L v)‖ ≤ T.diagonalNorm * ‖L v‖ ^ p :=
      T.norm_diagonal_le_diagonalNorm_mul hp (L v)
    _ ≤ T.diagonalNorm * 1 := mul_le_mul_of_nonneg_left
      (pow_le_one₀ (norm_nonneg _) hLv) T.diagonalNorm_nonneg
    _ = T.diagonalNorm := mul_one _

end ContinuousMultilinearMap

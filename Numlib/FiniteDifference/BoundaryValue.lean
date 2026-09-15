import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.Taylor
import Numlib.FiniteDifference.Derivative
import Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz

/-!
# Finite differences for the two-point boundary value problem

The centred finite difference discretization of `-u'' = f` on `(a, b)`, `u(a) = u(b) = 0`, and of
its variable-coefficient form `-(α u')' + γ u = f`: the uniform grid, the grid functions
vanishing at the ends, the discrete operator `L_h`, the trapezoidal discrete inner product with its
`L²` and `H¹` norms, the energy identities (summation by parts, symmetry and positivity of `L_h`,
the discrete Poincaré inequality), the consistency error by Taylor expansion, and the convergence
theorem `‖u - u_h‖_∞ ≤ ((b - a)²/96) h² ‖f''‖_∞`. The material is [quarteroni2000numerical] §12.2,
stated on a general interval `[a, b]` (the book has `[0, 1]`).

**Indexing.** `n` is the number of *interior* nodes, the nodes are `Fin (n + 2)`, the panels
`Fin (n + 1)`, `h = (b - a)/(n + 1)` (`FiniteDifference.gridStep`, `FiniteDifference.uniformGrid`);
the book's `n` subintervals with `n - 1` interior nodes is this with `n - 1`. A grid function is
`Fin (n + 2) → ℝ`, its supremum norm is the `‖·‖` of the `Pi` type, `FiniteDifference.gridZero n`
is the subspace `V_h^0` of those vanishing at both ends, and `FiniteDifference.interior` /
`FiniteDifference.ofInterior` pass between grid functions and their interior values. The operator
`L_h` (`FiniteDifference.discreteLaplacian`) maps grid functions to interior grid functions; on
`V_h^0` it is `h⁻² · tridiag(-1, 2, -1)` on the interior values
(`FiniteDifference.discreteLaplacian_eq_mulVec`, with `Matrix.symmTridiagonalToeplitz` of
`Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz`), and that is how every spectral or
inverse-positivity fact enters.

**Two stability estimates.** The energy method gives `‖u_h‖_h ≤ ((n + 1) h)²/2 ‖f_h‖_h` from the
energy identity `(L_h v, v)_h = ‖|v|‖_h²` and the discrete Poincaré inequality
`‖v‖_h ≤ ((n + 1) h/√2) ‖|v|‖_h` (`FiniteDifference.discreteL2Norm_le_of_discreteLaplacian_eq`); it
is the estimate that generalizes to variable coefficients. The maximum-norm estimate
`‖u_h‖_∞ ≤ ((b - a)²/8) ‖L_h u_h‖_∞` (`FiniteDifference.norm_le_of_discreteLaplacian_eq`) does not
use the book's explicit discrete Green's function: `tridiag(-1, 2, -1)` is an M-matrix and the
discrete parabola `w_j = (x_j - a)(b - x_j)/2` satisfies `L_h w = 1` exactly
(`FiniteDifference.discreteLaplacian_parabola`), so the comparison principle
`Matrix.IsMMatrix.norm_inv_mulVec_le` gives the bound with the same constant. Together with the
truncation error `‖τ_h‖_∞ ≤ (h²/12) ‖u⁗‖_∞` of the second centred difference this is the
convergence theorem `FiniteDifference.norm_sub_le_of_discreteLaplacian_eq`.

**Variable coefficients.** `FiniteDifference.variableCoeffOperator` is the flux form
`-(J_{j+1/2} - J_{j-1/2})/h + γ_j w_j` with midpoint fluxes; its matrix on `V_h^0`
(`FiniteDifference.variableCoeffMatrix`) is symmetric positive definite for `α > 0`, `γ ≥ 0`,
strictly diagonally dominant for `γ > 0` and an M-matrix — all through one energy identity
(`FiniteDifference.sum_variableCoeffOperator_mul_interior`), of which the Laplacian identity is the
case `α = 1`, `γ = 0`. The mirror-imaging rows for a Neumann or Robin condition at an endpoint are
definitions only (`FiniteDifference.IsNeumannSolution`, `FiniteDifference.IsRobinSolution`); the
book proves nothing about them.
-/

open Set Finset Matrix

namespace FiniteDifference

variable {n : ℕ} {a b : ℝ}

/-! ### The uniform grid -/

/-- The grid step `h = (b - a)/(n + 1)` of the uniform grid with `n` interior nodes. -/
noncomputable def gridStep (a b : ℝ) (n : ℕ) : ℝ := (b - a) / (n + 1)

/-- **The uniform grid** `x_j = a + j h`, `j = 0, …, n + 1`, with `h = (b - a)/(n + 1)`. -/
noncomputable def uniformGrid (a b : ℝ) (n : ℕ) (j : Fin (n + 2)) : ℝ := a + j * gridStep a b n

theorem gridStep_pos (hab : a < b) : 0 < gridStep a b n := by
  unfold gridStep; positivity

theorem gridStep_nonneg (hab : a ≤ b) : 0 ≤ gridStep a b n := by
  unfold gridStep; have := sub_nonneg.2 hab; positivity

/-- `(n + 1) h = b - a`. -/
theorem gridStep_mul_succ : ((n : ℝ) + 1) * gridStep a b n = b - a := by
  unfold gridStep; field_simp

theorem uniformGrid_apply (j : Fin (n + 2)) : uniformGrid a b n j = a + j * gridStep a b n := rfl

@[simp]
theorem uniformGrid_zero : uniformGrid a b n 0 = a := by simp [uniformGrid]

@[simp]
theorem uniformGrid_last : uniformGrid a b n (Fin.last (n + 1)) = b := by
  simp only [uniformGrid, Fin.val_last]
  push_cast
  rw [gridStep_mul_succ]
  ring

/-- Consecutive nodes are `h` apart. -/
theorem uniformGrid_succ_sub (j : Fin (n + 1)) :
    uniformGrid a b n j.succ - uniformGrid a b n j.castSucc = gridStep a b n := by
  simp only [uniformGrid, Fin.val_succ, Fin.val_castSucc]
  push_cast
  ring

/-- `x_{j+1} = x_j + h`. -/
theorem uniformGrid_succ (j : Fin (n + 1)) :
    uniformGrid a b n j.succ = uniformGrid a b n j.castSucc + gridStep a b n := by
  rw [← uniformGrid_succ_sub j]; ring

theorem uniformGrid_strictMono (hab : a < b) : StrictMono (uniformGrid a b n) := by
  intro i j hij
  simp only [uniformGrid]
  have := gridStep_pos (n := n) hab
  have : (i : ℝ) < j := by exact_mod_cast hij
  nlinarith

theorem uniformGrid_mem_Icc (hab : a ≤ b) (j : Fin (n + 2)) : uniformGrid a b n j ∈ Icc a b := by
  have h0 := gridStep_nonneg (n := n) hab
  have hj : (j : ℝ) ≤ n + 1 := by exact_mod_cast Nat.lt_succ_iff.1 j.isLt
  constructor
  · simp only [uniformGrid]; exact le_add_of_nonneg_right (by positivity)
  · simp only [uniformGrid]
    nlinarith [gridStep_mul_succ (a := a) (b := b) (n := n)]

/-- The interior nodes lie in the open interval. -/
theorem uniformGrid_interior_mem_Ioo (hab : a < b) (i : Fin n) :
    uniformGrid a b n i.succ.castSucc ∈ Ioo a b := by
  have hmono := uniformGrid_strictMono (n := n) hab
  constructor
  · simpa using hmono (show (0 : Fin (n + 2)) < i.succ.castSucc from by
      rw [Fin.lt_def]; simp)
  · simpa using hmono (show i.succ.castSucc < Fin.last (n + 1) from by
      rw [Fin.lt_def]; simp)

/-! ### Grid functions -/

/-- **The grid functions vanishing at both endpoints**, `V_h^0`. -/
def gridZero (n : ℕ) : Submodule ℝ (Fin (n + 2) → ℝ) where
  carrier := {v | v 0 = 0 ∧ v (Fin.last (n + 1)) = 0}
  zero_mem' := by simp
  add_mem' := by rintro v w ⟨hv0, hv1⟩ ⟨hw0, hw1⟩; simp [hv0, hv1, hw0, hw1]
  smul_mem' := by rintro c v ⟨hv0, hv1⟩; simp [hv0, hv1]

theorem mem_gridZero_iff {v : Fin (n + 2) → ℝ} :
    v ∈ gridZero n ↔ v 0 = 0 ∧ v (Fin.last (n + 1)) = 0 := Iff.rfl

/-- The interior values `(v_1, …, v_n)` of a grid function. -/
def interior (n : ℕ) : (Fin (n + 2) → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun v i := v i.succ.castSucc
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem interior_apply (v : Fin (n + 2) → ℝ) (i : Fin n) : interior n v i = v i.succ.castSucc := rfl

/-- **Every node is the first node, an interior node, or the last node**: the case analysis
behind every statement about grid functions of `V_h^0`. -/
theorem node_eq_zero_or_eq_last_or (j : Fin (n + 2)) :
    j = 0 ∨ j = Fin.last (n + 1) ∨ ∃ i : Fin n, j = i.succ.castSucc := by
  rcases Nat.eq_zero_or_pos (j : ℕ) with hj | hj
  · exact Or.inl (Fin.ext (by simpa using hj))
  by_cases hj2 : (j : ℕ) < n + 1
  · refine Or.inr (Or.inr ⟨⟨(j : ℕ) - 1, by omega⟩, Fin.ext ?_⟩)
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega
  · refine Or.inr (Or.inl (Fin.ext ?_))
    have := j.isLt
    simp only [Fin.val_last]
    omega

/-- Extension of interior values by zero at both endpoints. -/
def ofInterior (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] (Fin (n + 2) → ℝ) where
  toFun u j := if h : (j : ℕ) ≠ 0 ∧ (j : ℕ) < n + 1 then u ⟨(j : ℕ) - 1, by omega⟩ else 0
  map_add' u v := by
    ext j
    by_cases h : (j : ℕ) ≠ 0 ∧ (j : ℕ) < n + 1
    · simp only [Pi.add_apply, dite_eq_left h]
    · simp only [Pi.add_apply, dite_eq_right h, add_zero]
  map_smul' c u := by
    ext j
    by_cases h : (j : ℕ) ≠ 0 ∧ (j : ℕ) < n + 1
    · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, dite_eq_left h]
    · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, dite_eq_right h, mul_zero]

theorem ofInterior_apply (u : Fin n → ℝ) (j : Fin (n + 2)) :
    ofInterior n u j
      = if h : (j : ℕ) ≠ 0 ∧ (j : ℕ) < n + 1 then u ⟨(j : ℕ) - 1, by omega⟩ else 0 := rfl

@[simp]
theorem ofInterior_zero (u : Fin n → ℝ) : ofInterior n u 0 = 0 := by
  rw [ofInterior_apply, dite_eq_right (by simp)]

@[simp]
theorem ofInterior_last (u : Fin n → ℝ) : ofInterior n u (Fin.last (n + 1)) = 0 := by
  rw [ofInterior_apply, dite_eq_right (by simp)]

@[simp]
theorem ofInterior_succ_castSucc (u : Fin n → ℝ) (i : Fin n) :
    ofInterior n u i.succ.castSucc = u i := by
  rw [ofInterior_apply, dite_eq_left (by
    have := i.isLt
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega)]
  exact congrArg u (Fin.ext (by simp))

/-- `Fin.castSucc_succ` is a `simp` lemma, so the interior nodes are met in the form
`i.castSucc.succ` after any `simp`; this is `FiniteDifference.ofInterior_succ_castSucc` in that
form. -/
@[simp]
theorem ofInterior_castSucc_succ (u : Fin n → ℝ) (i : Fin n) :
    ofInterior n u i.castSucc.succ = u i := ofInterior_succ_castSucc u i

theorem interior_ofInterior (u : Fin n → ℝ) : interior n (ofInterior n u) = u := by
  ext i; simp

theorem ofInterior_mem_gridZero (u : Fin n → ℝ) : ofInterior n u ∈ gridZero n :=
  ⟨by simp, by simp⟩

/-- A grid function vanishing at the ends is the extension by zero of its interior values. -/
theorem ofInterior_interior_of_mem {v : Fin (n + 2) → ℝ} (hv : v ∈ gridZero n) :
    ofInterior n (interior n v) = v := by
  ext j
  rcases node_eq_zero_or_eq_last_or j with rfl | rfl | ⟨i, rfl⟩
  · simpa using hv.1.symm
  · simpa using hv.2.symm
  · simp

/-- The interior values determine a grid function of `V_h^0`. -/
theorem interior_injective_on_gridZero {v w : Fin (n + 2) → ℝ} (hv : v ∈ gridZero n)
    (hw : w ∈ gridZero n) (h : interior n v = interior n w) : v = w := by
  rw [← ofInterior_interior_of_mem hv, ← ofInterior_interior_of_mem hw, h]

/-- The supremum norm of a grid function of `V_h^0` is that of its interior values. -/
theorem norm_le_norm_interior_of_mem {v : Fin (n + 2) → ℝ} (hv : v ∈ gridZero n) :
    ‖v‖ ≤ ‖interior n v‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  rcases node_eq_zero_or_eq_last_or j with rfl | rfl | ⟨i, rfl⟩
  · rw [hv.1, norm_zero]; exact norm_nonneg _
  · rw [hv.2, norm_zero]; exact norm_nonneg _
  · exact norm_le_pi_norm (interior n v) i

/-- A grid function of `V_h^0` with vanishing interior values vanishes. -/
theorem eq_zero_of_interior_eq_zero {v : Fin (n + 2) → ℝ} (hv : v ∈ gridZero n)
    (h : interior n v = 0) : v = 0 :=
  interior_injective_on_gridZero hv (Submodule.zero_mem _) (by rw [h, map_zero])

/-- A grid function with all increments zero is constant, hence zero when it vanishes at `0`. -/
theorem eq_zero_of_forall_succ_eq {v : Fin (n + 2) → ℝ} (h0 : v 0 = 0)
    (h : ∀ j : Fin (n + 1), v j.succ = v j.castSucc) : v = 0 := by
  ext j
  induction j using Fin.induction with
  | zero => exact h0
  | succ j ih => rw [h j, ih]; rfl

/-! ### The discrete Laplacian -/

/-- **The discrete operator `L_h`** of [quarteroni2000numerical] (12.9):
`(L_h w)_j = -(w_{j+1} - 2 w_j + w_{j-1})/h²` at the interior nodes `j = 1, …, n`, as a linear map
from grid functions to interior grid functions. -/
noncomputable def discreteLaplacian (n : ℕ) (h : ℝ) : (Fin (n + 2) → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun w i := -(w i.succ.succ - 2 * w i.succ.castSucc + w i.castSucc.castSucc) / h ^ 2
  map_add' _ _ := by ext; simp only [Pi.add_apply]; ring
  map_smul' _ _ := by ext; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem discreteLaplacian_apply (h : ℝ) (w : Fin (n + 2) → ℝ) (i : Fin n) :
    discreteLaplacian n h w i
      = -(w i.succ.succ - 2 * w i.succ.castSucc + w i.castSucc.castSucc) / h ^ 2 := rfl

/-- The discrete Laplacian at an interior node is minus the second centred difference of the
grid function read as a function of the node position. -/
theorem discreteLaplacian_comp_uniformGrid (u : ℝ → ℝ) (i : Fin n) :
    discreteLaplacian n (gridStep a b n) (u ∘ uniformGrid a b n) i
      = -secondCentredDiff u (gridStep a b n) (uniformGrid a b n i.succ.castSucc) := by
  have h1 := uniformGrid_succ (a := a) (b := b) i.succ
  have h2 := uniformGrid_succ (a := a) (b := b) i.castSucc
  rw [Fin.succ_castSucc] at h2
  rw [discreteLaplacian_apply, secondCentredDiff_apply, Function.comp_apply, Function.comp_apply,
    Function.comp_apply, h1, show uniformGrid a b n i.castSucc.castSucc
      = uniformGrid a b n i.succ.castSucc - gridStep a b n by linarith]
  ring

/-! #### The neighbour sums of a tridiagonal row -/

/-- The sum picking the right neighbour of `i` from a family on `Fin n`, read on a grid function
vanishing at the last node. -/
private theorem sum_ite_succ_eq {w : Fin (n + 2) → ℝ} (hw : w (Fin.last (n + 1)) = 0) (i : Fin n)
    (c : ℝ) : ∑ j : Fin n, (if (i : ℕ) + 1 = j then c * interior n w j else 0)
      = c * w i.succ.succ := by
  by_cases hi : (i : ℕ) + 1 < n
  · have hfin : (⟨(i : ℕ) + 1, hi⟩ : Fin n).succ.castSucc = i.succ.succ := Fin.ext (by simp)
    rw [Finset.sum_eq_single ⟨(i : ℕ) + 1, hi⟩]
    · rw [ite_eq_left rfl, interior_apply, hfin]
    · intro j _ hj
      rw [ite_eq_right]
      intro h
      exact hj (Fin.ext h.symm)
    · intro h; exact absurd (Finset.mem_univ _) h
  · have hlast : i.succ.succ = Fin.last (n + 1) := by ext; simp; omega
    rw [hlast, hw, mul_zero]
    exact Finset.sum_eq_zero fun j _ => by rw [ite_eq_right]; intro h; omega

/-- The sum picking the left neighbour of `i` from a family on `Fin n`, read on a grid function
vanishing at the first node. -/
private theorem sum_ite_pred_eq {w : Fin (n + 2) → ℝ} (hw : w 0 = 0) (i : Fin n) (c : ℝ) :
    ∑ j : Fin n, (if (j : ℕ) + 1 = i then c * interior n w j else 0)
      = c * w i.castSucc.castSucc := by
  obtain ⟨i, hi⟩ := i
  cases i with
  | zero =>
    simp only [Fin.castSucc_mk, Fin.zero_eta]
    rw [Fin.castSucc_zero, hw, mul_zero]
    exact Finset.sum_eq_zero fun j _ => by rw [ite_eq_right]; omega
  | succ i =>
    have hfin : (⟨i, by omega⟩ : Fin n).succ.castSucc
        = (⟨i + 1, hi⟩ : Fin n).castSucc.castSucc := Fin.ext (by simp)
    rw [Finset.sum_eq_single ⟨i, by omega⟩]
    · rw [ite_eq_left rfl, interior_apply, hfin]
    · intro j _ hj
      rw [ite_eq_right]
      intro h
      exact hj (Fin.ext (by simpa using h))
    · intro h; exact absurd (Finset.mem_univ _) h

/-- The row of `tridiag(-1, 2, -1)` on the interior values of a grid function of `V_h^0`. -/
theorem symmTridiagonalToeplitz_mulVec_interior {w : Fin (n + 2) → ℝ} (hw : w ∈ gridZero n)
    (i : Fin n) : (symmTridiagonalToeplitz n (-1) 2 *ᵥ interior n w) i
      = 2 * w i.succ.castSucc - w i.succ.succ - w i.castSucc.castSucc := by
  have hsplit : ∀ j : Fin n, symmTridiagonalToeplitz n (-1) 2 i j * interior n w j
      = (if j = i then 2 * interior n w j else 0)
        - (if (i : ℕ) + 1 = j then 1 * interior n w j else 0)
        - (if (j : ℕ) + 1 = i then 1 * interior n w j else 0) := by
    intro j
    rw [symmTridiagonalToeplitz_apply']
    by_cases h1 : (i : ℕ) = j
    · have : j = i := Fin.ext h1.symm
      subst this
      simp
    · have hne : j ≠ i := fun h => h1 (by rw [h])
      rw [ite_eq_right h1, ite_eq_right hne]
      split_ifs <;> first | (exfalso; omega) | ring
  rw [mulVec, dotProduct]
  simp only [hsplit]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ i,
    sum_ite_succ_eq hw.2, sum_ite_pred_eq hw.1]
  simp only [Finset.mem_univ, ite_true, interior_apply, one_mul]

/-- **`L_h` on `V_h^0` is the finite difference matrix `h⁻² tridiag(-1, 2, -1)`** of
[quarteroni2000numerical] (12.8): for `w ∈ V_h^0`,
`L_h w = (h²)⁻¹ • (tridiag(-1, 2, -1) *ᵥ interior w)`. Symmetry, positive definiteness and the
M-matrix property of the matrix are `Matrix.symmTridiagonalToeplitz_isSymm`,
`Matrix.posDef_symmTridiagonalToeplitz_neg_one_two` and
`Matrix.isMMatrix_symmTridiagonalToeplitz_neg_one_two`. -/
theorem discreteLaplacian_eq_mulVec (h : ℝ) {w : Fin (n + 2) → ℝ} (hw : w ∈ gridZero n) :
    discreteLaplacian n h w = (h ^ 2)⁻¹ • (symmTridiagonalToeplitz n (-1) 2 *ᵥ interior n w) := by
  ext i
  rw [Pi.smul_apply, smul_eq_mul, symmTridiagonalToeplitz_mulVec_interior hw,
    discreteLaplacian_apply]
  ring

/-- `L_h` is injective on `V_h^0`: the finite difference problem has at most one solution. -/
theorem discreteLaplacian_injective_on_gridZero {h : ℝ} (hh : h ≠ 0) {w : Fin (n + 2) → ℝ}
    (hw : w ∈ gridZero n) (hL : discreteLaplacian n h w = 0) : w = 0 := by
  rw [discreteLaplacian_eq_mulVec h hw, smul_eq_zero, inv_eq_zero,
    pow_eq_zero_iff two_ne_zero] at hL
  refine eq_zero_of_interior_eq_zero hw (eq_zero_of_mulVec_eq_zero ?_ (hL.resolve_left hh))
  exact (isUnit_iff_ne_zero.1 ((isUnit_iff_isUnit_det _).1
    (isMMatrix_symmTridiagonalToeplitz_neg_one_two n).isUnit))

/-! ### The discrete inner product and norms -/

/-- The trapezoidal weights `c_0 = c_{n+1} = 1/2`, `c_k = 1` otherwise. -/
noncomputable def gridWeight (n : ℕ) (k : Fin (n + 2)) : ℝ :=
  if k = 0 ∨ k = Fin.last (n + 1) then 1 / 2 else 1

theorem gridWeight_nonneg (k : Fin (n + 2)) : 0 ≤ gridWeight n k := by
  unfold gridWeight; split_ifs <;> norm_num

theorem gridWeight_le_one (k : Fin (n + 2)) : gridWeight n k ≤ 1 := by
  unfold gridWeight; split_ifs <;> norm_num

@[simp]
theorem gridWeight_succ_castSucc (i : Fin n) : gridWeight n i.succ.castSucc = 1 := by
  unfold gridWeight
  rw [ite_eq_right]
  rintro (h | h)
  · exact absurd (congrArg Fin.val h) (by simp)
  · exact absurd (congrArg Fin.val h) (by simp; omega)

/-- **The trapezoidal discrete inner product** of [quarteroni2000numerical] §12.2.1:
`(w, v)_h = h ∑_k c_k w_k v_k` with `c_0 = c_{n+1} = 1/2` and `c_k = 1` otherwise, the composite
trapezoidal rule applied to `w v`. -/
noncomputable def discreteInner (n : ℕ) (h : ℝ) (w v : Fin (n + 2) → ℝ) : ℝ :=
  h * ∑ k, gridWeight n k * w k * v k

/-- **The discrete `L²` norm** `‖v‖_h = (v, v)_h^{1/2}`. -/
noncomputable def discreteL2Norm (n : ℕ) (h : ℝ) (v : Fin (n + 2) → ℝ) : ℝ :=
  √(discreteInner n h v v)

/-- The discrete derivative `(v_{j+1} - v_j)/h` on the panels ([quarteroni2000numerical] Remark
12.1). -/
noncomputable def discreteDeriv (n : ℕ) (h : ℝ) (v : Fin (n + 2) → ℝ) (j : Fin (n + 1)) : ℝ :=
  (v j.succ - v j.castSucc) / h

/-- **The discrete `H¹` seminorm** of [quarteroni2000numerical] (12.12):
`‖|v|‖_h = (h ∑_j ((v_{j+1} - v_j)/h)²)^{1/2}`. -/
noncomputable def discreteH1Seminorm (n : ℕ) (h : ℝ) (v : Fin (n + 2) → ℝ) : ℝ :=
  √(h * ∑ j, discreteDeriv n h v j ^ 2)

theorem discreteInner_comm (h : ℝ) (w v : Fin (n + 2) → ℝ) :
    discreteInner n h w v = discreteInner n h v w := by
  unfold discreteInner
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

theorem discreteInner_add_left (h : ℝ) (w v z : Fin (n + 2) → ℝ) :
    discreteInner n h (w + v) z = discreteInner n h w z + discreteInner n h v z := by
  unfold discreteInner
  rw [← mul_add, ← Finset.sum_add_distrib]
  exact congrArg _ (Finset.sum_congr rfl fun k _ => by simp only [Pi.add_apply]; ring)

theorem discreteInner_smul_left (h c : ℝ) (w v : Fin (n + 2) → ℝ) :
    discreteInner n h (c • w) v = c * discreteInner n h w v := by
  unfold discreteInner
  have hk : ∀ k, gridWeight n k * (c • w) k * v k = c * (gridWeight n k * w k * v k) :=
    fun k => by simp only [Pi.smul_apply, smul_eq_mul]; ring
  simp only [hk, ← Finset.mul_sum]
  ring

theorem discreteInner_self_nonneg {h : ℝ} (hh : 0 ≤ h) (v : Fin (n + 2) → ℝ) :
    0 ≤ discreteInner n h v v := by
  unfold discreteInner
  refine mul_nonneg hh (Finset.sum_nonneg fun k _ => ?_)
  rw [mul_assoc, ← sq]
  exact mul_nonneg (gridWeight_nonneg k) (sq_nonneg _)

theorem discreteInner_self_eq_zero_iff {h : ℝ} (hh : 0 < h) (v : Fin (n + 2) → ℝ) :
    discreteInner n h v v = 0 ↔ v = 0 := by
  unfold discreteInner
  rw [mul_eq_zero, or_iff_right hh.ne']
  have hterm : ∀ k, gridWeight n k * v k * v k = gridWeight n k * v k ^ 2 := fun k => by ring
  simp only [hterm]
  rw [Finset.sum_eq_zero_iff_of_nonneg fun k _ => mul_nonneg (gridWeight_nonneg k) (sq_nonneg _)]
  constructor
  · intro H
    ext k
    have hk := H k (Finset.mem_univ k)
    have hpos : 0 < gridWeight n k := by unfold gridWeight; split_ifs <;> norm_num
    exact pow_eq_zero_iff two_ne_zero |>.1 ((mul_eq_zero.1 hk).resolve_left hpos.ne')
  · rintro rfl k _
    simp

theorem discreteL2Norm_nonneg (h : ℝ) (v : Fin (n + 2) → ℝ) : 0 ≤ discreteL2Norm n h v :=
  Real.sqrt_nonneg _

theorem discreteL2Norm_sq {h : ℝ} (hh : 0 ≤ h) (v : Fin (n + 2) → ℝ) :
    discreteL2Norm n h v ^ 2 = discreteInner n h v v :=
  Real.sq_sqrt (discreteInner_self_nonneg hh v)

theorem discreteH1Seminorm_nonneg (h : ℝ) (v : Fin (n + 2) → ℝ) :
    0 ≤ discreteH1Seminorm n h v := Real.sqrt_nonneg _

theorem discreteH1Seminorm_sq {h : ℝ} (hh : 0 ≤ h) (v : Fin (n + 2) → ℝ) :
    discreteH1Seminorm n h v ^ 2 = h * ∑ j, discreteDeriv n h v j ^ 2 :=
  Real.sq_sqrt (mul_nonneg hh (Finset.sum_nonneg fun _ _ => sq_nonneg _))

/-- **The discrete `H¹` seminorm is the discrete `L²` norm of the difference quotient**
`v_h^{(1)}` on the `n + 1` panels ([quarteroni2000numerical] Remark 12.1): the panel sum carries
all weights `1`, against the trapezoidal weights of `FiniteDifference.discreteInner` on the
nodes. -/
theorem discreteH1Seminorm_eq_norm_discreteDeriv (h : ℝ) (v : Fin (n + 2) → ℝ) :
    discreteH1Seminorm n h v = √(h * ∑ j, discreteDeriv n h v j ^ 2) := rfl

/-- On `V_h^0` the endpoint terms of the discrete inner product vanish:
`(w, v)_h = h ∑_{i} w_{i+1} v_{i+1}`. -/
theorem discreteInner_eq_sum_interior (h : ℝ) (w : Fin (n + 2) → ℝ) {v : Fin (n + 2) → ℝ}
    (hv : v ∈ gridZero n) :
    discreteInner n h w v = h * ∑ i, w i.succ.castSucc * interior n v i := by
  unfold discreteInner
  congr 1
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc, hv.1, Fin.succ_last, hv.2]
  simp only [mul_zero, zero_add, add_zero]
  exact Finset.sum_congr rfl fun i _ => by rw [Fin.succ_castSucc, gridWeight_succ_castSucc, one_mul,
    interior_apply]

/-- The discrete inner product of an interior grid function extended by zero. -/
theorem discreteInner_ofInterior (h : ℝ) (g : Fin n → ℝ) {v : Fin (n + 2) → ℝ}
    (hv : v ∈ gridZero n) :
    discreteInner n h (ofInterior n g) v = h * ∑ i, g i * interior n v i := by
  rw [discreteInner_eq_sum_interior h _ hv]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [ofInterior_succ_castSucc]

/-- **Cauchy–Schwarz for the discrete inner product**: `(w, v)_h ≤ ‖w‖_h ‖v‖_h`. -/
theorem discreteInner_le_discreteL2Norm_mul {h : ℝ} (hh : 0 ≤ h) (w v : Fin (n + 2) → ℝ) :
    discreteInner n h w v ≤ discreteL2Norm n h w * discreteL2Norm n h v := by
  have hc : ∀ k, 0 ≤ h * gridWeight n k := fun k => mul_nonneg hh (gridWeight_nonneg k)
  have e1 : discreteInner n h w v
      = ∑ k, (√(h * gridWeight n k) * w k) * (√(h * gridWeight n k) * v k) := by
    unfold discreteInner
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := Real.mul_self_sqrt (hc k)
    linear_combination (-(w k * v k)) * this
  have e2 : ∀ u : Fin (n + 2) → ℝ, discreteL2Norm n h u
      = √(∑ k, (√(h * gridWeight n k) * u k) ^ 2) := fun u => by
    unfold discreteL2Norm discreteInner
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_pow, Real.sq_sqrt (hc k)]
    ring
  rw [e1, e2, e2]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/-! ### Summation by parts and the energy identities -/

/-- **Summation by parts** ([quarteroni2000numerical] §12.2.1):
`∑_{j=0}^{n} (w_{j+1} - w_j) v_j = w_{n+1} v_{n+1} - w_0 v_0
  - ∑_{j=0}^{n} (v_{j+1} - v_j) w_{j+1}`. -/
theorem sum_sub_mul_eq_sub_sum (w v : Fin (n + 2) → ℝ) :
    ∑ j : Fin (n + 1), (w j.succ - w j.castSucc) * v j.castSucc
      = w (Fin.last (n + 1)) * v (Fin.last (n + 1)) - w 0 * v 0
        - ∑ j : Fin (n + 1), (v j.succ - v j.castSucc) * w j.succ := by
  have htel : ∑ j : Fin (n + 1), (w j.succ * v j.succ - w j.castSucc * v j.castSucc)
      = w (Fin.last (n + 1)) * v (Fin.last (n + 1)) - w 0 * v 0 := by
    rw [Finset.sum_sub_distrib]
    have h1 := Fin.sum_univ_succ (fun k : Fin (n + 2) => w k * v k)
    have h2 := Fin.sum_univ_castSucc (fun k : Fin (n + 2) => w k * v k)
    linarith
  rw [← htel, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The shifted summation by parts behind the energy identities: for `v ∈ V_h^0`,
`∑_{i<n} (e_{i+1} - e_i) v_{i+1} = -∑_{j≤n} e_j (v_{j+1} - v_j)`. -/
theorem sum_succ_sub_castSucc_mul_eq_neg_sum (e : Fin (n + 1) → ℝ) {v : Fin (n + 2) → ℝ}
    (hv : v ∈ gridZero n) :
    ∑ i : Fin n, (e i.succ - e i.castSucc) * v i.succ.castSucc
      = -∑ j : Fin (n + 1), e j * (v j.succ - v j.castSucc) := by
  have h1 : ∑ i : Fin n, e i.succ * v i.succ.castSucc = ∑ j : Fin (n + 1), e j * v j.castSucc := by
    rw [Fin.sum_univ_succ (f := fun j => e j * v j.castSucc), Fin.castSucc_zero, hv.1, mul_zero,
      zero_add]
  have h2 : ∑ i : Fin n, e i.castSucc * v i.succ.castSucc = ∑ j : Fin (n + 1), e j * v j.succ := by
    rw [Fin.sum_univ_castSucc (f := fun j => e j * v j.succ), Fin.succ_last, hv.2, mul_zero,
      add_zero]
    exact Finset.sum_congr rfl fun i _ => by rw [Fin.succ_castSucc]
  calc ∑ i : Fin n, (e i.succ - e i.castSucc) * v i.succ.castSucc
      = ∑ i : Fin n, e i.succ * v i.succ.castSucc
          - ∑ i : Fin n, e i.castSucc * v i.succ.castSucc := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ j : Fin (n + 1), e j * v j.castSucc - ∑ j : Fin (n + 1), e j * v j.succ := by rw [h1, h2]
    _ = -∑ j : Fin (n + 1), e j * (v j.succ - v j.castSucc) := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring

/-- **The energy identity** behind [quarteroni2000numerical] Lemma 12.1: for `w, v ∈ V_h^0`,
`h ∑_i (L_h w)_i v_{i+1} = h⁻¹ ∑_j (w_{j+1} - w_j)(v_{j+1} - v_j)`. -/
theorem discreteInner_discreteLaplacian_eq {h : ℝ} (hh : h ≠ 0) {w v : Fin (n + 2) → ℝ}
    (hv : v ∈ gridZero n) :
    h * ∑ i, discreteLaplacian n h w i * interior n v i
      = h⁻¹ * ∑ j : Fin (n + 1), (w j.succ - w j.castSucc) * (v j.succ - v j.castSucc) := by
  have key := sum_succ_sub_castSucc_mul_eq_neg_sum (fun j => w j.succ - w j.castSucc) hv
  have e : ∀ i : Fin n, discreteLaplacian n h w i * interior n v i
      = -(h ^ 2)⁻¹ * (((w i.succ.succ - w i.succ.castSucc)
          - (w i.castSucc.succ - w i.castSucc.castSucc))
        * v i.succ.castSucc) := fun i => by
    rw [discreteLaplacian_apply, interior_apply, Fin.succ_castSucc]
    field_simp
    ring
  simp only [e]
  rw [← Finset.mul_sum, key]
  field_simp

/-- **`L_h` is symmetric** on `V_h^0` ([quarteroni2000numerical] Lemma 12.1):
`(L_h w, v)_h = (w, L_h v)_h`. -/
theorem discreteInner_discreteLaplacian_comm {h : ℝ} (hh : h ≠ 0) {w v : Fin (n + 2) → ℝ}
    (hw : w ∈ gridZero n) (hv : v ∈ gridZero n) :
    discreteInner n h (ofInterior n (discreteLaplacian n h w)) v
      = discreteInner n h w (ofInterior n (discreteLaplacian n h v)) := by
  rw [discreteInner_ofInterior h _ hv, discreteInner_comm, discreteInner_ofInterior h _ hw,
    discreteInner_discreteLaplacian_eq hh hv, discreteInner_discreteLaplacian_eq hh hw]
  congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- **`(L_h v, v)_h = ‖|v|‖_h²`** ([quarteroni2000numerical] (12.13)) on `V_h^0`. -/
theorem discreteInner_discreteLaplacian_self {h : ℝ} (hh : 0 < h) {v : Fin (n + 2) → ℝ}
    (hv : v ∈ gridZero n) :
    h * ∑ i, discreteLaplacian n h v i * interior n v i = discreteH1Seminorm n h v ^ 2 := by
  rw [discreteInner_discreteLaplacian_eq hh.ne' hv, discreteH1Seminorm_sq hh.le, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [discreteDeriv]
  field_simp

/-- **`L_h` is positive definite** on `V_h^0` ([quarteroni2000numerical] Lemma 12.1):
`(L_h v, v)_h > 0` for `v ≠ 0`. -/
theorem discreteInner_discreteLaplacian_self_pos {h : ℝ} (hh : 0 < h) {v : Fin (n + 2) → ℝ}
    (hv : v ∈ gridZero n) (hv0 : v ≠ 0) :
    0 < h * ∑ i, discreteLaplacian n h v i * interior n v i := by
  rw [discreteInner_discreteLaplacian_self hh hv, discreteH1Seminorm_sq hh.le]
  refine mul_pos hh (Finset.sum_pos' (fun j _ => sq_nonneg _) ?_)
  by_contra hcon
  push Not at hcon
  refine hv0 (eq_zero_of_forall_succ_eq hv.1 fun j => ?_)
  have := hcon j (Finset.mem_univ j)
  have h0 : discreteDeriv n h v j = 0 :=
    pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm this (sq_nonneg _))
  rw [discreteDeriv, div_eq_zero_iff, or_iff_left hh.ne', sub_eq_zero] at h0
  exact h0

/-- **`‖|v|‖_h` is a norm on `V_h^0`** (the positive definiteness clause of
[quarteroni2000numerical] Lemma 12.1): it vanishes only on `v = 0`. -/
theorem discreteH1Seminorm_eq_zero_iff {h : ℝ} (hh : 0 < h) {v : Fin (n + 2) → ℝ}
    (hv : v ∈ gridZero n) : discreteH1Seminorm n h v = 0 ↔ v = 0 := by
  constructor
  · intro h0
    by_contra hv0
    have := discreteInner_discreteLaplacian_self_pos hh hv hv0
    rw [discreteInner_discreteLaplacian_self hh hv, h0] at this
    simp at this
  · rintro rfl
    simp [discreteH1Seminorm, discreteDeriv]

/-! ### The discrete Poincaré inequality and the energy stability estimate -/

/-- **The discrete Poincaré inequality** ([quarteroni2000numerical] Lemma 12.2 on a general
interval), in squared form: for `v ∈ V_h^0`, `‖v‖_h² ≤ (((n + 1) h)²/2) ‖|v|‖_h²`. -/
theorem discreteInner_self_le_sq_mul {h : ℝ} (hh : 0 < h) {v : Fin (n + 2) → ℝ}
    (hv : v ∈ gridZero n) :
    discreteInner n h v v ≤ ((n + 1) * h) ^ 2 / 2 * (h * ∑ j, discreteDeriv n h v j ^ 2) := by
  -- the padded grid function and its increments, indexed by `ℕ`
  set V : ℕ → ℝ := fun m => if hm : m < n + 2 then v ⟨m, hm⟩ else 0 with hV
  set D : ℕ → ℝ := fun k => if hk : k < n + 1 then v ⟨k + 1, by omega⟩ - v ⟨k, by omega⟩ else 0
    with hD
  have hV0 : V 0 = 0 := by simp [hV, hv.1]
  have hVD : ∀ k, k < n + 1 → V (k + 1) - V k = D k := fun k hk => by
    simp only [hV, hD, dite_eq_left hk, dite_eq_left (show k + 1 < n + 2 by omega),
      dite_eq_left (show k < n + 2 by omega)]
  have hVsum : ∀ m, m ≤ n + 1 → V m = ∑ k ∈ Finset.range m, D k := fun m hm => by
    have htel := Finset.sum_range_sub V m
    rw [hV0, sub_zero] at htel
    rw [← htel]
    exact Finset.sum_congr rfl fun k hk => hVD k (by have := Finset.mem_range.1 hk; omega)
  set S := ∑ k ∈ Finset.range (n + 1), D k ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => sq_nonneg _
  -- `V m² ≤ m S` for `m ≤ n + 1`
  have hVsq : ∀ m, m ≤ n + 1 → V m ^ 2 ≤ m * S := fun m hm => by
    rw [hVsum m hm]
    refine (sq_sum_le_card_mul_sum_sq (s := Finset.range m) (f := D)).trans ?_
    rw [Finset.card_range]
    have hsub : Finset.range m ⊆ Finset.range (n + 1) := Finset.range_subset_range.2 hm
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
      hsub fun k _ _ => sq_nonneg _) (by positivity)
  -- the two norms in terms of `V` and `D`
  have hinner : discreteInner n h v v = h * ∑ m ∈ Finset.range n, V (m + 1) ^ 2 := by
    rw [discreteInner_eq_sum_interior h v hv, ← Fin.sum_univ_eq_sum_range]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have hfin : (⟨(i : ℕ) + 1, by omega⟩ : Fin (n + 2)) = i.succ.castSucc := Fin.ext (by simp)
    rw [interior_apply, hV]
    simp only [dite_eq_left (show (i : ℕ) + 1 < n + 2 by omega), hfin]
    ring
  have hseminorm : ∑ j, discreteDeriv n h v j ^ 2 = S / h ^ 2 := by
    rw [hS, ← Fin.sum_univ_eq_sum_range, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [discreteDeriv, div_pow, hD]
    simp only [dite_eq_left j.isLt]
    rfl
  -- the Gauss sum `∑_{m<n} (m + 1) ≤ (n + 1)²/2`
  have hgauss : ∑ m ∈ Finset.range n, ((m : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 2 / 2 := by
    have h1 : ∑ m ∈ Finset.range n, ((m : ℝ) + 1) = ((∑ m ∈ Finset.range (n + 1), m : ℕ) : ℝ) := by
      rw [Finset.sum_range_succ', Nat.cast_add, Nat.cast_sum, Nat.cast_zero, add_zero]
      push_cast
      rfl
    have h2 := Finset.sum_range_id_mul_two (n + 1)
    rw [Nat.add_sub_cancel] at h2
    have h3 : ((∑ m ∈ Finset.range (n + 1), m : ℕ) : ℝ) * 2 = ((n : ℝ) + 1) * n := by
      exact_mod_cast h2
    nlinarith
  rw [hinner, hseminorm]
  calc h * ∑ m ∈ Finset.range n, V (m + 1) ^ 2
      ≤ h * ∑ m ∈ Finset.range n, ((m : ℝ) + 1) * S := by
        gcongr with m hm
        have := hVsq (m + 1) (by have := Finset.mem_range.1 hm; omega)
        push_cast at this
        exact this
    _ = h * (∑ m ∈ Finset.range n, ((m : ℝ) + 1)) * S := by rw [← Finset.sum_mul]; ring
    _ ≤ h * (((n : ℝ) + 1) ^ 2 / 2) * S := by gcongr
    _ = ((n + 1) * h) ^ 2 / 2 * (h * (S / h ^ 2)) := by field_simp

/-- **The discrete Poincaré inequality** ([quarteroni2000numerical] Lemma 12.2 on a general
interval): for `v ∈ V_h^0`, `‖v‖_h ≤ ((n + 1) h/√2) ‖|v|‖_h`; with `(n + 1) h = b - a` this is
`‖v‖_h ≤ ((b - a)/√2) ‖|v|‖_h`, the book's `1/√2` on `[0, 1]`. -/
theorem discreteL2Norm_le_discreteH1Seminorm {h : ℝ} (hh : 0 < h) {v : Fin (n + 2) → ℝ}
    (hv : v ∈ gridZero n) :
    discreteL2Norm n h v ≤ ((n + 1) * h / √2) * discreteH1Seminorm n h v := by
  have hpos : 0 ≤ ((n : ℝ) + 1) * h / √2 := by positivity
  rw [← abs_of_nonneg (discreteL2Norm_nonneg h v),
    ← abs_of_nonneg (mul_nonneg hpos (discreteH1Seminorm_nonneg h v)), ← sq_le_sq, mul_pow,
    discreteL2Norm_sq hh.le, discreteH1Seminorm_sq hh.le, div_pow, Real.sq_sqrt zero_le_two]
  exact discreteInner_self_le_sq_mul hh hv

/-- **Stability by the energy method** ([quarteroni2000numerical] (12.17) on a general interval):
if `u ∈ V_h^0` and `L_h u = f` at the interior nodes, then `‖|u|‖_h ≤ ((n + 1) h/√2) ‖f‖_h` and
`‖u‖_h ≤ (((n + 1) h)²/2) ‖f‖_h`. On `[0, 1]`, `‖u_h‖_h ≤ ‖f_h‖_h / 2`. -/
theorem discreteL2Norm_le_of_discreteLaplacian_eq {h : ℝ} (hh : 0 < h) {u f : Fin (n + 2) → ℝ}
    (hu : u ∈ gridZero n) (hL : discreteLaplacian n h u = interior n f) :
    discreteH1Seminorm n h u ≤ ((n + 1) * h / √2) * discreteL2Norm n h f ∧
      discreteL2Norm n h u ≤ ((n + 1) * h) ^ 2 / 2 * discreteL2Norm n h f := by
  have hC : 0 ≤ ((n : ℝ) + 1) * h / √2 := by positivity
  have hP := discreteL2Norm_le_discreteH1Seminorm hh hu
  -- `‖|u|‖_h² = (f, u)_h ≤ ‖f‖_h ‖u‖_h`
  have h1 : discreteH1Seminorm n h u ^ 2 ≤ discreteL2Norm n h f * discreteL2Norm n h u := by
    have hfu := discreteInner_eq_sum_interior h f hu
    simp only [interior_apply] at hfu ⊢
    rw [← discreteInner_discreteLaplacian_self hh hu, hL]
    simp only [interior_apply]
    rw [← hfu]
    exact discreteInner_le_discreteL2Norm_mul hh.le f u
  have hA : discreteH1Seminorm n h u ≤ ((n + 1) * h / √2) * discreteL2Norm n h f := by
    rcases (discreteH1Seminorm_nonneg h u).eq_or_lt with h0 | h0
    · rw [← h0]; exact mul_nonneg hC (discreteL2Norm_nonneg h f)
    · have := h1.trans (mul_le_mul_of_nonneg_left hP (discreteL2Norm_nonneg h f))
      rw [sq] at this
      nlinarith
  refine ⟨hA, hP.trans ?_⟩
  calc ((n + 1) * h / √2) * discreteH1Seminorm n h u
      ≤ ((n + 1) * h / √2) * (((n + 1) * h / √2) * discreteL2Norm n h f) :=
        mul_le_mul_of_nonneg_left hA hC
    _ = ((n + 1) * h / √2 * ((n + 1) * h / √2)) * discreteL2Norm n h f := by ring
    _ = ((n + 1) * h) ^ 2 / 2 * discreteL2Norm n h f := by
        rw [div_mul_div_comm, Real.mul_self_sqrt zero_le_two]
        ring

/-! ### The truncation error -/

/-- **The local truncation error** of [quarteroni2000numerical] (12.18):
`τ_j = (L_h u)(x_j) - f(x_j)` at the interior nodes, for `u f : ℝ → ℝ` on the uniform grid. -/
noncomputable def truncationError (a b : ℝ) (n : ℕ) (u f : ℝ → ℝ) : Fin n → ℝ :=
  discreteLaplacian n (gridStep a b n) (u ∘ uniformGrid a b n)
    - fun i => f (uniformGrid a b n i.succ.castSucc)

theorem truncationError_apply (u f : ℝ → ℝ) (i : Fin n) :
    truncationError a b n u f i
      = discreteLaplacian n (gridStep a b n) (u ∘ uniformGrid a b n) i
        - f (uniformGrid a b n i.succ.castSucc) := rfl

/-- **The error equation** ([quarteroni2000numerical] Remark 12.3, (12.22)): if `u_h` solves the
finite difference problem, `L_h (u - u_h) = τ_h`. -/
theorem error_eq_of_discreteLaplacian_eq (u f : ℝ → ℝ) {uh : Fin (n + 2) → ℝ}
    (hL : discreteLaplacian n (gridStep a b n) uh
      = fun i => f (uniformGrid a b n i.succ.castSucc)) :
    discreteLaplacian n (gridStep a b n) (u ∘ uniformGrid a b n - uh)
      = truncationError a b n u f := by
  rw [map_sub, hL]
  rfl

/-! ### Consistency under a Lipschitz third derivative -/

/-- The order-two Taylor kernel integrates to `(y - x)³/6` over `x..y`, in either orientation. -/
private theorem integral_taylorKernel (x y : ℝ) :
    ∫ t in x..y, (y - t) ^ 2 / 2 = (y - x) ^ 3 / 6 := by
  have hF : ∀ t ∈ uIcc x y, HasDerivAt (fun s : ℝ => -((y - s) ^ 3 / 6)) ((y - t) ^ 2 / 2) t := by
    intro t _
    have h : HasDerivAt (fun s : ℝ => -((y - s) ^ 3 / 6)) (-(3 * (y - t) ^ 2 * (-1) / 6)) t :=
      ((((hasDerivAt_id t).const_sub y).pow 3).div_const 6).neg
    convert h using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  ring

/-- The first moment of the order-two Taylor kernel: `∫_x^y (y - t)²/2 · (t - x) dt =
(y - x)⁴/24`, in either orientation. -/
private theorem integral_taylorKernel_mul (x y : ℝ) :
    ∫ t in x..y, (y - t) ^ 2 / 2 * (t - x) = (y - x) ^ 4 / 24 := by
  have hF : ∀ t ∈ uIcc x y, HasDerivAt
      (fun s : ℝ => (y - x) ^ 2 * (s - x) ^ 2 / 4 - (y - x) * (s - x) ^ 3 / 3 + (s - x) ^ 4 / 8)
      ((y - t) ^ 2 / 2 * (t - x)) t := by
    intro t _
    have h : HasDerivAt
        (fun s : ℝ => (y - x) ^ 2 * (s - x) ^ 2 / 4 - (y - x) * (s - x) ^ 3 / 3 + (s - x) ^ 4 / 8)
        ((y - x) ^ 2 * (2 * (t - x) ^ 1 * 1) / 4 - (y - x) * (3 * (t - x) ^ 2 * 1) / 3
          + 4 * (t - x) ^ 3 * 1 / 8) t :=
      ((((((hasDerivAt_id t).sub_const x).pow 2).const_mul ((y - x) ^ 2)).div_const 4).sub
        (((((hasDerivAt_id t).sub_const x).pow 3).const_mul (y - x)).div_const 3)).add
        ((((hasDerivAt_id t).sub_const x).pow 4).div_const 8)
    convert h using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  ring

/-- **Taylor's theorem of order three with a Lipschitz third derivative**: for `u` of class `C³`
on the closed interval between `x` and `y`, whose third derivative there differs from its value at
`x` by at most `M |t - x|`, the order-three Taylor polynomial at `x` approximates `u y` to within
`M (y - x)⁴/24`. This is the integral remainder (12.21) of [quarteroni2000numerical] Remark 12.2,
bounded by `M ∫_0^{|y - x|} s (|y - x| - s)²/2 ds`. -/
private theorem abs_sub_taylor_three_le_of_lipschitz {u : ℝ → ℝ} {M x y : ℝ} (hne : x ≠ y)
    (hM : 0 ≤ M) (hu : ContDiffOn ℝ 3 u (uIcc x y)) (hx : ContDiffAt ℝ 3 u x)
    (hlip : ∀ t ∈ uIoo x y,
      |iteratedDerivWithin 3 u (uIcc x y) t - iteratedDeriv 3 u x| ≤ M * |t - x|) :
    |u y - (u x + (y - x) * iteratedDeriv 1 u x + (y - x) ^ 2 / 2 * iteratedDeriv 2 u x
        + (y - x) ^ 3 / 6 * iteratedDeriv 3 u x)| ≤ M * (y - x) ^ 4 / 24 := by
  have hud : UniqueDiffOn ℝ (uIcc x y) := uniqueDiffOn_uIcc hne
  have hu' : ContDiffOn ℝ ((2 : ℕ) + 1 : ℕ) u (uIcc x y) := by exact_mod_cast hu
  have hDcont : ContinuousOn (iteratedDerivWithin 3 u (uIcc x y)) (uIcc x y) :=
    hu.continuousOn_iteratedDerivWithin (by norm_num) hud
  have hD1 : IntervalIntegrable
      (fun t => (y - t) ^ 2 / 2 * iteratedDerivWithin 3 u (uIcc x y) t)
      MeasureTheory.volume x y :=
    (ContinuousOn.mul (by fun_prop) hDcont).intervalIntegrable
  have hD2 : IntervalIntegrable
      (fun t : ℝ => (y - t) ^ 2 / 2 * iteratedDeriv 3 u x) MeasureTheory.volume x y :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hT : u y - taylorWithinEval u 2 (uIcc x y) x y
      = ∫ t in x..y, (y - t) ^ 2 / 2 * iteratedDerivWithin 3 u (uIcc x y) t := by
    rw [taylor_integral_remainder hu']
    exact intervalIntegral.integral_congr fun t _ => by norm_num
  have hP : taylorWithinEval u 2 (uIcc x y) x y
      = u x + (y - x) * iteratedDeriv 1 u x + (y - x) ^ 2 / 2 * iteratedDeriv 2 u x := by
    rw [taylorWithinEval_eq_sum_of_contDiffAt hne (hx.of_le (by norm_num)),
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    norm_num [iteratedDeriv_zero]
  have hsplit : u y - (u x + (y - x) * iteratedDeriv 1 u x + (y - x) ^ 2 / 2 * iteratedDeriv 2 u x
        + (y - x) ^ 3 / 6 * iteratedDeriv 3 u x)
      = ∫ t in x..y, (y - t) ^ 2 / 2 * (iteratedDerivWithin 3 u (uIcc x y) t
          - iteratedDeriv 3 u x) := by
    have h2 : ∫ t in x..y, (y - t) ^ 2 / 2 * iteratedDeriv 3 u x
        = (y - x) ^ 3 / 6 * iteratedDeriv 3 u x := by
      rw [intervalIntegral.integral_mul_const, integral_taylorKernel]
    rw [show (fun t => (y - t) ^ 2 / 2 * (iteratedDerivWithin 3 u (uIcc x y) t
          - iteratedDeriv 3 u x))
        = (fun t => (y - t) ^ 2 / 2 * iteratedDerivWithin 3 u (uIcc x y) t
          - (y - t) ^ 2 / 2 * iteratedDeriv 3 u x) from funext fun t => by ring,
      intervalIntegral.integral_sub hD1 hD2, ← hT, h2, hP]
    ring
  rw [hsplit, ← Real.norm_eq_abs]
  have hae : ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.uIoc x y), ‖(y - t) ^ 2 / 2
      * (iteratedDerivWithin 3 u (uIcc x y) t - iteratedDeriv 3 u x)‖
      ≤ (y - t) ^ 2 / 2 * (M * |t - x|) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc,
      MeasureTheory.ae_restrict_of_ae (MeasureTheory.volume.ae_ne (x ⊔ y))] with t ht htne
    have ht' : t ∈ uIoo x y := ⟨ht.1, lt_of_le_of_ne ht.2 htne⟩
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (y - t) ^ 2 / 2)]
    exact mul_le_mul_of_nonneg_left (hlip t ht') (by positivity)
  have hgint : IntervalIntegrable (fun t => (y - t) ^ 2 / 2 * (M * |t - x|))
      MeasureTheory.volume x y :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  refine (intervalIntegral.norm_integral_le_abs_of_norm_le hae hgint).trans_eq ?_
  rcases lt_or_gt_of_ne hne with hxy | hxy
  · have he : EqOn (fun t : ℝ => (y - t) ^ 2 / 2 * (M * |t - x|))
        (fun t : ℝ => M * ((y - t) ^ 2 / 2 * (t - x))) (uIcc x y) := fun t ht => by
      rw [uIcc_of_le hxy.le] at ht
      simp only
      rw [abs_of_nonneg (by linarith [ht.1] : (0 : ℝ) ≤ t - x)]
      ring
    rw [intervalIntegral.integral_congr he, intervalIntegral.integral_const_mul,
      integral_taylorKernel_mul, abs_of_nonneg (mul_nonneg hM (by positivity))]
    ring
  · have he : EqOn (fun t : ℝ => (y - t) ^ 2 / 2 * (M * |t - x|))
        (fun t : ℝ => -M * ((y - t) ^ 2 / 2 * (t - x))) (uIcc x y) := fun t ht => by
      rw [uIcc_of_ge hxy.le] at ht
      simp only
      rw [abs_of_nonpos (by linarith [ht.2] : t - x ≤ (0 : ℝ))]
      ring
    rw [intervalIntegral.integral_congr he, intervalIntegral.integral_const_mul, abs_mul,
      integral_taylorKernel_mul, abs_neg, abs_of_nonneg hM,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (y - x) ^ 4 / 24)]
    ring

/-- **Consistency under a Lipschitz third derivative** ([quarteroni2000numerical] Remark 12.2): if
`u` is `C³` on `[a, b]`, its third derivative is Lipschitz with constant `M` on `(a, b)`, and
`u'' = -f` there, then the local truncation error satisfies `|τ_j| ≤ M h²/12` at every interior
node. The book states the weaker bound `M h²`; the proof is its integral remainder (12.21). -/
theorem abs_truncationError_le_of_lipschitzOnWith (hab : a < b) {u f : ℝ → ℝ} {M : NNReal}
    (hu : ContDiffOn ℝ 3 u (Icc a b)) (hM : LipschitzOnWith M (iteratedDeriv 3 u) (Ioo a b))
    (hu'' : ∀ x ∈ Ioo a b, iteratedDeriv 2 u x = -f x) (i : Fin n) :
    |truncationError a b n u f i| ≤ (M : ℝ) * gridStep a b n ^ 2 / 12 := by
  set h := gridStep a b n with hh
  set x := uniformGrid a b n i.succ.castSucc with hxdef
  have hpos : 0 < h := gridStep_pos hab
  have hne0 : h ≠ 0 := hpos.ne'
  have hx : x ∈ Ioo a b := uniformGrid_interior_mem_Ioo hab i
  have hxm : uniformGrid a b n i.castSucc.castSucc = x - h := by
    rw [hxdef, ← Fin.succ_castSucc, uniformGrid_succ]; ring
  have hxp : uniformGrid a b n i.succ.succ = x + h := by rw [hxdef, uniformGrid_succ]
  have hsub : Icc (x - h) (x + h) ⊆ Icc a b := by
    rw [← hxm, ← hxp]
    exact Icc_subset_Icc (uniformGrid_mem_Icc hab.le _).1 (uniformGrid_mem_Icc hab.le _).2
  have hcx : ContDiffAt ℝ 3 u x := hu.contDiffAt (Icc_mem_nhds hx.1 hx.2)
  -- the two Taylor expansions
  have key : ∀ y : ℝ, y ∈ Icc (x - h) (x + h) → x ≠ y →
      |u y - (u x + (y - x) * iteratedDeriv 1 u x + (y - x) ^ 2 / 2 * iteratedDeriv 2 u x
        + (y - x) ^ 3 / 6 * iteratedDeriv 3 u x)| ≤ (M : ℝ) * (y - x) ^ 4 / 24 := by
    intro y hy hne
    have hxmem : x ∈ Icc (x - h) (x + h) := ⟨by linarith, by linarith⟩
    have hIcc : Set.uIcc x y ⊆ Icc a b :=
      (Set.Icc_subset_Icc (le_inf hxmem.1 hy.1) (sup_le hxmem.2 hy.2)).trans hsub
    have hIoo : Set.uIoo x y ⊆ Ioo a b :=
      Set.Ioo_subset_Ioo (le_inf hx.1.le (hsub hy).1) (sup_le hx.2.le (hsub hy).2)
    refine abs_sub_taylor_three_le_of_lipschitz hne M.coe_nonneg (hu.mono hIcc) hcx ?_
    intro t ht
    have hEq : iteratedDerivWithin 3 u (uIcc x y) t = iteratedDeriv 3 u t :=
      iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hne)
        (hu.contDiffAt (Icc_mem_nhds (hIoo ht).1 (hIoo ht).2))
        (Set.uIoo_subset_uIcc_self ht)
    rw [hEq]
    simpa [Real.dist_eq] using hM.dist_le_mul t (hIoo ht) x hx
  have hplus := key (x + h) ⟨by linarith, le_rfl⟩ (by linarith)
  have hminus := key (x - h) ⟨le_rfl, by linarith⟩ (by linarith)
  have hxa : x + h - x = h := by ring
  have hxb : x - h - x = -h := by ring
  rw [hxa] at hplus
  rw [hxb] at hminus
  -- the truncation error is the sum of the two remainders, divided by `h²`
  have hfx : f x = -iteratedDeriv 2 u x := by
    rw [hu'' x hx, neg_neg]
  have hτ : truncationError a b n u f i
      = -((u (x + h) - (u x + h * iteratedDeriv 1 u x + h ^ 2 / 2 * iteratedDeriv 2 u x
            + h ^ 3 / 6 * iteratedDeriv 3 u x))
          + (u (x - h) - (u x + -h * iteratedDeriv 1 u x + (-h) ^ 2 / 2 * iteratedDeriv 2 u x
            + (-h) ^ 3 / 6 * iteratedDeriv 3 u x))) / h ^ 2 := by
    rw [truncationError_apply, discreteLaplacian_apply]
    simp only [Function.comp_apply]
    rw [← hh, hxm, hxp, ← hxdef, hfx]
    field_simp
    ring
  rw [hτ, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ h ^ 2), abs_neg]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < h ^ 2)]
  calc |u (x + h) - (u x + h * iteratedDeriv 1 u x + h ^ 2 / 2 * iteratedDeriv 2 u x
          + h ^ 3 / 6 * iteratedDeriv 3 u x)
        + (u (x - h) - (u x + -h * iteratedDeriv 1 u x + (-h) ^ 2 / 2 * iteratedDeriv 2 u x
          + (-h) ^ 3 / 6 * iteratedDeriv 3 u x))|
      ≤ (M : ℝ) * h ^ 4 / 24 + (M : ℝ) * (-h) ^ 4 / 24 := (abs_add_le _ _).trans
        (add_le_add hplus hminus)
    _ = (M : ℝ) * h ^ 2 / 12 * h ^ 2 := by ring

/-- **The truncation error in Lagrange form** ([quarteroni2000numerical] (12.19), with the sign
corrected): for `u` of class `C⁴` on `[a, b]` with `u'' = -f` inside, at each interior node
`τ_j = -(h²/24)(u⁗(ξ) + u⁗(η))` with `ξ ∈ (x_{j-1}, x_j)`, `η ∈ (x_j, x_{j+1})`. -/
theorem truncationError_eq_of_contDiffOn (hab : a < b) {u f : ℝ → ℝ}
    (hu : ContDiffOn ℝ 4 u (Icc a b)) (hu'' : ∀ x ∈ Ioo a b, iteratedDeriv 2 u x = -f x)
    (i : Fin n) :
    ∃ ξ ∈ Ioo (uniformGrid a b n i.castSucc.castSucc) (uniformGrid a b n i.succ.castSucc),
      ∃ η ∈ Ioo (uniformGrid a b n i.succ.castSucc) (uniformGrid a b n i.succ.succ),
        truncationError a b n u f i
          = -(gridStep a b n ^ 2 / 24) * (iteratedDeriv 4 u ξ + iteratedDeriv 4 u η) := by
  set h := gridStep a b n with hh
  set x := uniformGrid a b n i.succ.castSucc with hx
  have hpos : 0 < h := gridStep_pos hab
  have hxm : uniformGrid a b n i.castSucc.castSucc = x - h := by
    rw [hx, ← Fin.succ_castSucc, uniformGrid_succ]; ring
  have hxp : uniformGrid a b n i.succ.succ = x + h := by
    rw [hx, uniformGrid_succ]
  have hsub : Icc (x - h) (x + h) ⊆ Icc a b := by
    rw [← hxm, ← hxp]
    exact Icc_subset_Icc (uniformGrid_mem_Icc hab.le _).1 (uniformGrid_mem_Icc hab.le _).2
  obtain ⟨ξ, hξ, η, hη, hT⟩ :=
    iteratedDeriv_two_sub_secondCentredDiff_eq_two_points hpos (hu.mono hsub)
  refine ⟨ξ, by rw [hxm]; exact hξ, η, by rw [hxp]; exact hη, ?_⟩
  have hfx : f x = -iteratedDeriv 2 u x := by
    rw [hu'' x (uniformGrid_interior_mem_Ioo hab i), neg_neg]
  rw [truncationError_apply, discreteLaplacian_comp_uniformGrid, ← hh, ← hx, hfx, ← hT]
  ring

/-- **Consistency for `C⁴` solutions** ([quarteroni2000numerical] (12.20)): if `u` is `C⁴` on
`[a, b]`, `u'' = -f` inside, and `|u⁗| ≤ M` inside, then every interior node satisfies
`|τ_j| ≤ (h²/12) M`; in the supremum norm, `‖τ_h‖ ≤ (h²/12) M`. -/
theorem abs_truncationError_le_of_contDiffOn (hab : a < b) {u f : ℝ → ℝ} {M : ℝ}
    (hu : ContDiffOn ℝ 4 u (Icc a b)) (hu'' : ∀ x ∈ Ioo a b, iteratedDeriv 2 u x = -f x)
    (hM : ∀ x ∈ Ioo a b, |iteratedDeriv 4 u x| ≤ M) (i : Fin n) :
    |truncationError a b n u f i| ≤ gridStep a b n ^ 2 / 12 * M := by
  obtain ⟨ξ, hξ, η, hη, hT⟩ := truncationError_eq_of_contDiffOn hab hu hu'' i
  have hξ' : ξ ∈ Ioo a b := ⟨(uniformGrid_mem_Icc hab.le _).1.trans_lt hξ.1,
    hξ.2.trans_le (uniformGrid_mem_Icc hab.le _).2⟩
  have hη' : η ∈ Ioo a b := ⟨(uniformGrid_mem_Icc hab.le _).1.trans_lt hη.1,
    hη.2.trans_le (uniformGrid_mem_Icc hab.le _).2⟩
  have h1 := hM ξ hξ'
  have h2 := hM η hη'
  rw [hT, abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ gridStep a b n ^ 2 / 24)]
  calc gridStep a b n ^ 2 / 24 * |iteratedDeriv 4 u ξ + iteratedDeriv 4 u η|
      ≤ gridStep a b n ^ 2 / 24 * (M + M) :=
        mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add h1 h2)) (by positivity)
    _ = gridStep a b n ^ 2 / 12 * M := by ring

/-- The supremum-norm form of `abs_truncationError_le_of_contDiffOn`: `‖τ_h‖ ≤ (h²/12) M`. -/
theorem norm_truncationError_le_of_contDiffOn (hab : a < b) {u f : ℝ → ℝ} {M : ℝ}
    (hu : ContDiffOn ℝ 4 u (Icc a b)) (hu'' : ∀ x ∈ Ioo a b, iteratedDeriv 2 u x = -f x)
    (hM : ∀ x ∈ Ioo a b, |iteratedDeriv 4 u x| ≤ M) :
    ‖truncationError a b n u f‖ ≤ gridStep a b n ^ 2 / 12 * M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM _ (Set.nonempty_Ioo.2 hab).some_mem)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Subsingleton.elim (truncationError a b 0 u f) 0, norm_zero]
    exact mul_nonneg (by positivity) hM0
  refine (pi_norm_le_iff_of_nonneg ?_).2 fun i => ?_
  · have i0 : Fin n := ⟨0, hn⟩
    exact (abs_nonneg _).trans (abs_truncationError_le_of_contDiffOn hab hu hu'' hM i0)
  · rw [Real.norm_eq_abs]
    exact abs_truncationError_le_of_contDiffOn hab hu hu'' hM i

/-- If `u'' = -f` on an open interval then `u⁗ = -f''` there. -/
theorem iteratedDeriv_four_eq_neg_iteratedDeriv_two {u f : ℝ → ℝ}
    (hu'' : ∀ x ∈ Ioo a b, iteratedDeriv 2 u x = -f x) {x : ℝ} (hx : x ∈ Ioo a b) :
    iteratedDeriv 4 u x = -iteratedDeriv 2 f x := by
  have hev : iteratedDeriv 2 u =ᶠ[nhds x] -f :=
    Filter.eventually_of_mem (Ioo_mem_nhds hx.1 hx.2) fun y hy => by
      rw [Pi.neg_apply]; exact hu'' y hy
  have h4 : iteratedDeriv 4 u = iteratedDeriv 2 (iteratedDeriv 2 u) := by
    simp only [iteratedDeriv_eq_iterate]
    exact Function.iterate_add_apply deriv 2 2 u
  rw [h4, hev.iteratedDeriv_eq 2, iteratedDeriv_neg]

/-! ### Stability in the maximum norm and the convergence theorem -/

/-- **The comparison function**: the discrete parabola `w_j = (x_j - a)(b - x_j)/2` satisfies
`L_h w = 1` at every interior node (the grid function [quarteroni2000numerical] Exercise 12.7
obtains as `T_h 1`). -/
theorem discreteLaplacian_parabola (hab : a < b) :
    discreteLaplacian n (gridStep a b n)
      (fun j => (uniformGrid a b n j - a) * (b - uniformGrid a b n j) / 2) = 1 := by
  ext i
  have hpos := gridStep_pos (n := n) hab
  have h1 : uniformGrid a b n i.succ.succ
      = uniformGrid a b n i.succ.castSucc + gridStep a b n := uniformGrid_succ i.succ
  have h2 : uniformGrid a b n i.castSucc.castSucc
      = uniformGrid a b n i.succ.castSucc - gridStep a b n := by
    have h := uniformGrid_succ (a := a) (b := b) i.castSucc
    rw [Fin.succ_castSucc] at h
    linarith
  rw [discreteLaplacian_apply, Pi.one_apply]
  simp only [h1, h2]
  field_simp
  ring

/-- The discrete parabola vanishes at both endpoints. -/
theorem parabola_mem_gridZero :
    (fun j => (uniformGrid a b n j - a) * (b - uniformGrid a b n j) / 2) ∈ gridZero n := by
  constructor <;> simp

/-- The discrete parabola is bounded by `(b - a)²/8`. -/
theorem norm_parabola_le (hab : a ≤ b) :
    ‖fun j => (uniformGrid a b n j - a) * (b - uniformGrid a b n j) / 2‖ ≤ (b - a) ^ 2 / 8 := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  have hj := uniformGrid_mem_Icc (n := n) hab j
  rw [Real.norm_eq_abs, abs_of_nonneg (by nlinarith [hj.1, hj.2])]
  nlinarith [hj.1, hj.2, sq_nonneg (b + a - 2 * uniformGrid a b n j)]

/-- **Stability in the maximum norm** ([quarteroni2000numerical] (12.28) on `[a, b]`) by the
M-matrix comparison principle: for `u ∈ V_h^0`, `‖u‖_∞ ≤ ((b - a)²/8) ‖L_h u‖_∞`. -/
theorem norm_le_of_discreteLaplacian_eq (hab : a < b) {u : Fin (n + 2) → ℝ} (hu : u ∈ gridZero n)
    {g : Fin n → ℝ} (hL : discreteLaplacian n (gridStep a b n) u = g) :
    ‖u‖ ≤ (b - a) ^ 2 / 8 * ‖g‖ := by
  set h := gridStep a b n with hh
  have hpos : 0 < h := gridStep_pos hab
  set T := symmTridiagonalToeplitz n (-1) 2 with hT
  have hM := isMMatrix_symmTridiagonalToeplitz_neg_one_two n
  have hdet : IsUnit T.det := (isUnit_iff_isUnit_det _).1 hM.isUnit
  set w : Fin (n + 2) → ℝ := fun j => (uniformGrid a b n j - a) * (b - uniformGrid a b n j) / 2
    with hw
  -- the comparison vector `interior w / h²`
  have hcomp : T *ᵥ ((h ^ 2)⁻¹ • interior n w) = 1 := by
    rw [mulVec_smul, ← discreteLaplacian_eq_mulVec h parabola_mem_gridZero, hh,
      discreteLaplacian_parabola hab]
  -- `interior u = T⁻¹ (h² g)`
  have hint : interior n u = T⁻¹ *ᵥ (h ^ 2 • g) := by
    rw [← hL, discreteLaplacian_eq_mulVec h hu, smul_smul,
      mul_inv_cancel₀ (by positivity), one_smul,
      mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]
  calc ‖u‖ ≤ ‖interior n u‖ := norm_le_norm_interior_of_mem hu
    _ ≤ ‖(h ^ 2)⁻¹ • interior n w‖ * ‖h ^ 2 • g‖ := by
        rw [hint]; exact hM.norm_inv_mulVec_le hcomp _
    _ = ‖interior n w‖ * ‖g‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv,
          abs_of_pos (by positivity)]
        field_simp
    _ ≤ (b - a) ^ 2 / 8 * ‖g‖ := by
        gcongr
        exact ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => norm_le_pi_norm w _).trans
          (norm_parabola_le hab.le)

/-- **The discrete maximum principle** ([quarteroni2000numerical] §12.2): on `V_h^0`,
`L_h u ≥ 0` forces `u ≥ 0`. -/
theorem nonneg_of_discreteLaplacian_nonneg {h : ℝ} (hh : 0 < h) {u : Fin (n + 2) → ℝ}
    (hu : u ∈ gridZero n) (hL : 0 ≤ discreteLaplacian n h u) : 0 ≤ u := by
  have hM := isMMatrix_symmTridiagonalToeplitz_neg_one_two n
  have hint : 0 ≤ interior n u := by
    refine hM.nonneg_of_mulVec_nonneg fun i => ?_
    have := hL i
    rw [discreteLaplacian_eq_mulVec h hu, Pi.smul_apply, smul_eq_mul] at this
    exact nonneg_of_mul_nonneg_right this (by positivity)
  intro j
  rcases node_eq_zero_or_eq_last_or j with rfl | rfl | ⟨i, rfl⟩
  · simp [hu.1]
  · simp [hu.2]
  · simpa using hint i

/-- **Convergence of the centred scheme** ([quarteroni2000numerical] Theorem 12.1 on `[a, b]`), in
terms of a bound on `u⁗`: if `u` is `C⁴` on `[a, b]` with `u'' = -f` and `|u⁗| ≤ M` inside,
`u(a) = u(b) = 0`, and `u_h ∈ V_h^0` solves `L_h u_h = f` at the interior nodes, then
`‖u ∘ x - u_h‖_∞ ≤ ((b - a)²/96) h² M`. -/
theorem norm_sub_le_of_discreteLaplacian_eq_of_iteratedDeriv_four_le (hab : a < b) {u f : ℝ → ℝ}
    {M : ℝ} (hu : ContDiffOn ℝ 4 u (Icc a b)) (hu'' : ∀ x ∈ Ioo a b, iteratedDeriv 2 u x = -f x)
    (hM : ∀ x ∈ Ioo a b, |iteratedDeriv 4 u x| ≤ M) (hua : u a = 0) (hub : u b = 0)
    {uh : Fin (n + 2) → ℝ} (huh : uh ∈ gridZero n)
    (hL : discreteLaplacian n (gridStep a b n) uh
      = fun i => f (uniformGrid a b n i.succ.castSucc)) :
    ‖u ∘ uniformGrid a b n - uh‖ ≤ (b - a) ^ 2 / 96 * gridStep a b n ^ 2 * M := by
  have he : u ∘ uniformGrid a b n - uh ∈ gridZero n := by
    refine Submodule.sub_mem _ ⟨?_, ?_⟩ huh
    · simp [hua]
    · simp [hub]
  have hbound := norm_le_of_discreteLaplacian_eq hab he
    (error_eq_of_discreteLaplacian_eq u f hL)
  calc ‖u ∘ uniformGrid a b n - uh‖ ≤ (b - a) ^ 2 / 8 * ‖truncationError a b n u f‖ := hbound
    _ ≤ (b - a) ^ 2 / 8 * (gridStep a b n ^ 2 / 12 * M) := by
        gcongr
        exact norm_truncationError_le_of_contDiffOn hab hu hu'' hM
    _ = (b - a) ^ 2 / 96 * gridStep a b n ^ 2 * M := by ring

/-- **Convergence of the centred scheme** ([quarteroni2000numerical] Theorem 12.1 on `[a, b]`):
let `u` be `C⁴` on `[a, b]` with `u'' = -f` inside and `u(a) = u(b) = 0`, let `|f''| ≤ M` inside,
and let `u_h ∈ V_h^0` solve `L_h u_h = f` at the interior nodes. Then
`‖u ∘ x - u_h‖_∞ ≤ ((b - a)²/96) h² M`; on `[0, 1]` this is the book's (12.27),
`‖u - u_h‖_{h,∞} ≤ (h²/96) ‖f''‖_∞`. The solution `u` is a hypothesis rather than produced from
`f`: its existence and `C⁴` regularity for `f ∈ C²` is the Green's function representation of
[quarteroni2000numerical] §12.1. -/
theorem norm_sub_le_of_discreteLaplacian_eq (hab : a < b) {u f : ℝ → ℝ} {M : ℝ}
    (hu : ContDiffOn ℝ 4 u (Icc a b)) (hu'' : ∀ x ∈ Ioo a b, iteratedDeriv 2 u x = -f x)
    (hM : ∀ x ∈ Ioo a b, |iteratedDeriv 2 f x| ≤ M) (hua : u a = 0) (hub : u b = 0)
    {uh : Fin (n + 2) → ℝ} (huh : uh ∈ gridZero n)
    (hL : discreteLaplacian n (gridStep a b n) uh
      = fun i => f (uniformGrid a b n i.succ.castSucc)) :
    ‖u ∘ uniformGrid a b n - uh‖ ≤ (b - a) ^ 2 / 96 * gridStep a b n ^ 2 * M :=
  norm_sub_le_of_discreteLaplacian_eq_of_iteratedDeriv_four_le hab hu hu''
    (fun x hx => by
      rw [iteratedDeriv_four_eq_neg_iteratedDeriv_two hu'' hx, abs_neg]; exact hM x hx)
    hua hub huh hL

/-! ### Variable coefficients -/

/-- The midpoints `x_{j+1/2} = (x_j + x_{j+1})/2` of the panels. -/
noncomputable def midGrid (a b : ℝ) (n : ℕ) (j : Fin (n + 1)) : ℝ :=
  (uniformGrid a b n j.castSucc + uniformGrid a b n j.succ) / 2

/-- **The variable-coefficient operator** of [quarteroni2000numerical] (12.32)–(12.33):
`(L_h w)_j = -(J_{j+1/2}(w) - J_{j-1/2}(w))/h + γ(x_j) w_j` with the midpoint fluxes
`J_{j+1/2}(w) = α(x_{j+1/2}) (w_{j+1} - w_j)/h`. -/
noncomputable def variableCoeffOperator (a b : ℝ) (n : ℕ) (α γ : ℝ → ℝ) :
    (Fin (n + 2) → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun w i :=
    -(α (midGrid a b n i.succ) * (w i.succ.succ - w i.succ.castSucc) / gridStep a b n
        - α (midGrid a b n i.castSucc) * (w i.succ.castSucc - w i.castSucc.castSucc)
          / gridStep a b n)
      / gridStep a b n + γ (uniformGrid a b n i.succ.castSucc) * w i.succ.castSucc
  map_add' _ _ := by ext; simp only [Pi.add_apply]; ring
  map_smul' _ _ := by ext; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem variableCoeffOperator_apply (α γ : ℝ → ℝ) (w : Fin (n + 2) → ℝ) (i : Fin n) :
    variableCoeffOperator a b n α γ w i
      = -(α (midGrid a b n i.succ) * (w i.succ.succ - w i.succ.castSucc) / gridStep a b n
          - α (midGrid a b n i.castSucc) * (w i.succ.castSucc - w i.castSucc.castSucc)
            / gridStep a b n) / gridStep a b n
        + γ (uniformGrid a b n i.succ.castSucc) * w i.succ.castSucc := rfl

/-- With `α = 1` and `γ = 0` the variable-coefficient operator is the discrete Laplacian. -/
theorem variableCoeffOperator_one_zero :
    variableCoeffOperator a b n (fun _ => 1) (fun _ => 0)
      = discreteLaplacian n (gridStep a b n) := by
  refine LinearMap.ext fun w => funext fun i => ?_
  rw [variableCoeffOperator_apply, discreteLaplacian_apply]
  ring

/-- **The energy identity with variable coefficients**: for `w, v ∈ V_h^0`,
`∑_i (L_h w)_i v_{i+1} = h⁻² ∑_j α(x_{j+1/2}) (w_{j+1} - w_j)(v_{j+1} - v_j)
  + ∑_i γ(x_{i+1}) w_{i+1} v_{i+1}`.
-/
theorem sum_variableCoeffOperator_mul_interior (hab : a < b) (α γ : ℝ → ℝ)
    {w v : Fin (n + 2) → ℝ} (hv : v ∈ gridZero n) :
    ∑ i, variableCoeffOperator a b n α γ w i * interior n v i
      = (gridStep a b n ^ 2)⁻¹ * ∑ j : Fin (n + 1),
          α (midGrid a b n j) * (w j.succ - w j.castSucc) * (v j.succ - v j.castSucc)
        + ∑ i, γ (uniformGrid a b n i.succ.castSucc) * w i.succ.castSucc * interior n v i := by
  have hpos := gridStep_pos (n := n) hab
  have key := sum_succ_sub_castSucc_mul_eq_neg_sum
    (fun j => α (midGrid a b n j) * (w j.succ - w j.castSucc)) hv
  have e : ∀ i : Fin n, variableCoeffOperator a b n α γ w i * interior n v i
      = -(gridStep a b n ^ 2)⁻¹ * ((α (midGrid a b n i.succ) * (w i.succ.succ - w i.succ.castSucc)
          - α (midGrid a b n i.castSucc) * (w i.castSucc.succ - w i.castSucc.castSucc))
            * v i.succ.castSucc)
        + γ (uniformGrid a b n i.succ.castSucc) * w i.succ.castSucc * interior n v i := fun i => by
    rw [variableCoeffOperator_apply, interior_apply, Fin.succ_castSucc]
    field_simp
  simp only [e]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, key]
  ring

/-- **The matrix of the variable-coefficient operator** on `V_h^0` ([quarteroni2000numerical]
(12.34), with the sign of the off-diagonal entries restored):
`h⁻² tridiag(-α_{j+1/2}, α_{j-1/2} + α_{j+1/2}, -α_{j+1/2}) + diag(γ_j)`. -/
noncomputable def variableCoeffMatrix (a b : ℝ) (n : ℕ) (α γ : ℝ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    if i = j then
      (α (midGrid a b n i.castSucc) + α (midGrid a b n i.succ)) / gridStep a b n ^ 2
        + γ (uniformGrid a b n i.succ.castSucc)
    else if (i : ℕ) + 1 = j then -α (midGrid a b n i.succ) / gridStep a b n ^ 2
    else if (j : ℕ) + 1 = i then -α (midGrid a b n j.succ) / gridStep a b n ^ 2
    else 0

theorem variableCoeffMatrix_apply (α γ : ℝ → ℝ) (i j : Fin n) :
    variableCoeffMatrix a b n α γ i j
      = if i = j then
          (α (midGrid a b n i.castSucc) + α (midGrid a b n i.succ)) / gridStep a b n ^ 2
            + γ (uniformGrid a b n i.succ.castSucc)
        else if (i : ℕ) + 1 = j then -α (midGrid a b n i.succ) / gridStep a b n ^ 2
        else if (j : ℕ) + 1 = i then -α (midGrid a b n j.succ) / gridStep a b n ^ 2
        else 0 := rfl

/-- The variable-coefficient matrix is symmetric. -/
theorem variableCoeffMatrix_isSymm (α γ : ℝ → ℝ) : (variableCoeffMatrix a b n α γ).IsSymm := by
  ext i j
  rw [transpose_apply, variableCoeffMatrix_apply, variableCoeffMatrix_apply]
  rcases eq_or_ne i j with rfl | hij
  · rfl
  have hval : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
  rw [ite_eq_right hij.symm, ite_eq_right hij]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- The off-diagonal entries of the variable-coefficient matrix are nonpositive for `α ≥ 0` at
the midpoints. -/
theorem variableCoeffMatrix_offDiag_nonpos (α γ : ℝ → ℝ) (hα : ∀ j, 0 ≤ α (midGrid a b n j))
    {i j : Fin n} (hij : i ≠ j) : variableCoeffMatrix a b n α γ i j ≤ 0 := by
  rw [variableCoeffMatrix_apply, ite_eq_right hij]
  split_ifs
  · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (hα _)) (sq_nonneg _)
  · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (hα _)) (sq_nonneg _)
  · exact le_rfl

/-- **The variable-coefficient operator on `V_h^0` is its matrix on the interior values**. -/
theorem variableCoeffOperator_eq_mulVec (α γ : ℝ → ℝ) {w : Fin (n + 2) → ℝ} (hw : w ∈ gridZero n) :
    variableCoeffOperator a b n α γ w = variableCoeffMatrix a b n α γ *ᵥ interior n w := by
  ext i
  have hsplit : ∀ j : Fin n, variableCoeffMatrix a b n α γ i j * interior n w j
      = (if j = i then ((α (midGrid a b n i.castSucc) + α (midGrid a b n i.succ))
              / gridStep a b n ^ 2
            + γ (uniformGrid a b n i.succ.castSucc)) * interior n w j else 0)
        - (if (i : ℕ) + 1 = j then α (midGrid a b n i.succ) / gridStep a b n ^ 2 * interior n w j
            else 0)
        - (if (j : ℕ) + 1 = i then
            α (midGrid a b n i.castSucc) / gridStep a b n ^ 2 * interior n w j
            else 0) := by
    intro j
    rw [variableCoeffMatrix_apply]
    by_cases hij : i = j
    · subst hij; simp
    · have hne : j ≠ i := Ne.symm hij
      rw [ite_eq_right hij, ite_eq_right hne]
      by_cases h1 : (i : ℕ) + 1 = j
      · rw [ite_eq_left h1, ite_eq_left h1, ite_eq_right (by omega)]; ring
      · rw [ite_eq_right h1, ite_eq_right h1]
        by_cases h2 : (j : ℕ) + 1 = i
        · have hji : j.succ = i.castSucc := Fin.ext (by simp [h2])
          rw [ite_eq_left h2, ite_eq_left h2, hji]; ring
        · rw [ite_eq_right h2, ite_eq_right h2]; ring
  rw [mulVec, dotProduct]
  simp only [hsplit]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ i,
    sum_ite_succ_eq hw.2, sum_ite_pred_eq hw.1, variableCoeffOperator_apply]
  simp only [Finset.mem_univ, ite_true, interior_apply]
  have hpos : gridStep a b n ≠ 0 ∨ gridStep a b n = 0 := ne_or_eq _ _
  rcases hpos with hpos | hpos
  · field_simp
    ring
  · rw [hpos]; simp

/-- **The variable-coefficient matrix is positive definite** for `α > 0` at the midpoints and
`γ ≥ 0` at the nodes ([quarteroni2000numerical] §12.2.3): its quadratic form is
`h⁻² ∑_j α_{j+1/2} (x_{j+1} - x_j)² + ∑_j γ_j x_j²` with `x_0 = x_{n+1} = 0`. -/
theorem variableCoeffMatrix_posDef (hab : a < b) (α γ : ℝ → ℝ)
    (hα : ∀ j, 0 < α (midGrid a b n j))
    (hγ : ∀ i : Fin n, 0 ≤ γ (uniformGrid a b n i.succ.castSucc)) :
    (variableCoeffMatrix a b n α γ).PosDef := by
  have hpos := gridStep_pos (n := n) hab
  refine posDef_iff_dotProduct_mulVec.2 ⟨?_, fun x hx => ?_⟩
  · exact isHermitian_iff_isSymm.2 (variableCoeffMatrix_isSymm α γ)
  · have hw := ofInterior_mem_gridZero (n := n) x
    have hx' : interior n (ofInterior n x) = x := interior_ofInterior x
    rw [star_trivial, ← hx', ← variableCoeffOperator_eq_mulVec α γ hw, dotProduct_comm,
      dotProduct, sum_variableCoeffOperator_mul_interior hab α γ hw]
    have hterm : ∀ i : Fin n, 0 ≤ γ (uniformGrid a b n i.succ.castSucc)
        * ofInterior n x i.succ.castSucc
        * interior n (ofInterior n x) i := fun i => by
      rw [interior_apply, mul_assoc, ← sq]
      exact mul_nonneg (hγ i) (sq_nonneg _)
    refine add_pos_of_pos_of_nonneg (mul_pos (by positivity) (Finset.sum_pos' ?_ ?_))
      (Finset.sum_nonneg fun i _ => hterm i)
    · intro j _
      rw [mul_assoc, ← sq]
      exact mul_nonneg (hα j).le (sq_nonneg _)
    · by_contra hcon
      push Not at hcon
      refine hx (by
        rw [← hx']
        rw [eq_zero_of_forall_succ_eq hw.1 fun j => ?_]
        · simp
        have := hcon j (Finset.mem_univ j)
        rw [mul_assoc, ← sq] at this
        have h0 := le_antisymm this (mul_nonneg (hα j).le (sq_nonneg _))
        rw [mul_eq_zero, or_iff_right (hα j).ne', pow_eq_zero_iff two_ne_zero, sub_eq_zero] at h0
        exact h0)

/-- **The variable-coefficient matrix is an M-matrix** for `α > 0` at the midpoints and `γ ≥ 0` at
the nodes (Stieltjes: positive definite with nonpositive off-diagonal entries). -/
theorem variableCoeffMatrix_isMMatrix (hab : a < b) (α γ : ℝ → ℝ)
    (hα : ∀ j, 0 < α (midGrid a b n j))
    (hγ : ∀ i : Fin n, 0 ≤ γ (uniformGrid a b n i.succ.castSucc)) :
    (variableCoeffMatrix a b n α γ).IsMMatrix :=
  IsMMatrix.of_posDef_of_offDiag_nonpos (variableCoeffMatrix_posDef hab α γ hα hγ)
    fun _ _ hij => variableCoeffMatrix_offDiag_nonpos α γ (fun j => (hα j).le) hij

/-- The off-diagonal row sum of the variable-coefficient matrix is at most the flux part of the
diagonal, `(α_{j-1/2} + α_{j+1/2})/h²`. -/
theorem variableCoeffMatrix_sum_erase_le (α γ : ℝ → ℝ) (hα : ∀ j, 0 ≤ α (midGrid a b n j))
    (i : Fin n) : ∑ j ∈ Finset.univ.erase i, ‖variableCoeffMatrix a b n α γ i j‖
      ≤ (α (midGrid a b n i.castSucc) + α (midGrid a b n i.succ)) / gridStep a b n ^ 2 := by
  have hsplit : ∀ j : Fin n, j ≠ i → ‖variableCoeffMatrix a b n α γ i j‖
      = (if (i : ℕ) + 1 = j then α (midGrid a b n i.succ) / gridStep a b n ^ 2 else 0)
        + (if (j : ℕ) + 1 = i then α (midGrid a b n i.castSucc) / gridStep a b n ^ 2 else 0) := by
    intro j hj
    rw [variableCoeffMatrix_apply, ite_eq_right (Ne.symm hj), Real.norm_eq_abs]
    by_cases h1 : (i : ℕ) + 1 = j
    · rw [ite_eq_left h1, ite_eq_left h1, ite_eq_right (by omega), add_zero, abs_div, abs_neg,
        abs_of_nonneg (hα _), abs_of_nonneg (sq_nonneg _)]
    · rw [ite_eq_right h1, ite_eq_right h1, zero_add]
      by_cases h2 : (j : ℕ) + 1 = i
      · have hji : j.succ = i.castSucc := Fin.ext (by simp [h2])
        rw [ite_eq_left h2, ite_eq_left h2, hji, abs_div, abs_neg, abs_of_nonneg (hα _),
          abs_of_nonneg (sq_nonneg _)]
      · rw [ite_eq_right h2, ite_eq_right h2, abs_zero]
  rw [Finset.sum_congr rfl fun j hj => hsplit j (Finset.mem_erase.1 hj).1, Finset.sum_add_distrib]
  have h1 : ∑ j ∈ Finset.univ.erase i,
      (if (i : ℕ) + 1 = j then α (midGrid a b n i.succ) / gridStep a b n ^ 2 else 0)
      ≤ α (midGrid a b n i.succ) / gridStep a b n ^ 2 := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    refine mul_le_of_le_one_left (div_nonneg (hα _) (sq_nonneg _)) ?_
    have : ((Finset.univ.erase i).filter fun j : Fin n => (i : ℕ) + 1 = j).card ≤ 1 :=
      Finset.card_le_one.2 fun x hx y hy => Fin.ext (by
        have := (Finset.mem_filter.1 hx).2; have := (Finset.mem_filter.1 hy).2; omega)
    exact_mod_cast this
  have h2 : ∑ j ∈ Finset.univ.erase i,
      (if (j : ℕ) + 1 = i then α (midGrid a b n i.castSucc) / gridStep a b n ^ 2 else 0)
      ≤ α (midGrid a b n i.castSucc) / gridStep a b n ^ 2 := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    refine mul_le_of_le_one_left (div_nonneg (hα _) (sq_nonneg _)) ?_
    have : ((Finset.univ.erase i).filter fun j : Fin n => (j : ℕ) + 1 = i).card ≤ 1 :=
      Finset.card_le_one.2 fun x hx y hy => Fin.ext (by
        have := (Finset.mem_filter.1 hx).2; have := (Finset.mem_filter.1 hy).2; omega)
    exact_mod_cast this
  rw [add_div]
  linarith

/-- **The variable-coefficient matrix is strictly diagonally dominant** by rows when `γ > 0` at
the nodes and `α ≥ 0` at the midpoints ([quarteroni2000numerical] §12.2.3). -/
theorem variableCoeffMatrix_isStrictDiagDominant (hab : a < b) (α γ : ℝ → ℝ)
    (hα : ∀ j, 0 ≤ α (midGrid a b n j))
    (hγ : ∀ i : Fin n, 0 < γ (uniformGrid a b n i.succ.castSucc)) :
    (variableCoeffMatrix a b n α γ).IsStrictDiagDominant := by
  intro i
  have hpos := gridStep_pos (n := n) hab
  refine (variableCoeffMatrix_sum_erase_le α γ hα i).trans_lt ?_
  rw [variableCoeffMatrix_apply, ite_eq_left rfl, Real.norm_eq_abs, abs_of_pos]
  · linarith [hγ i]
  · have := hγ i; have := hα i.castSucc; have := hα i.succ; positivity

/-! ### Neumann and Robin boundary rows -/

/-- **The mirror-imaging discretization of a Neumann condition** `J(u)(b) = α u'(b) = g₁` at the
last node ([quarteroni2000numerical] (12.35) and the display after it): `u` satisfies the Dirichlet
condition `u_0 = d₀`, the interior equations of the variable-coefficient operator, and the modified
last row `-α_{n+1/2} u_n/h² + (α_{n+1/2}/h² + γ_{n+1}/2) u_{n+1} = g₁/h + f_{n+1}/2`. The book
proves
nothing about it (its second-order accuracy is asserted, not shown). -/
def IsNeumannSolution (a b : ℝ) (n : ℕ) (α γ f : ℝ → ℝ) (d₀ g₁ : ℝ) (u : Fin (n + 2) → ℝ) : Prop :=
  u 0 = d₀ ∧
  (∀ i : Fin n, variableCoeffOperator a b n α γ u i = f (uniformGrid a b n i.succ.castSucc)) ∧
  -α (midGrid a b n (Fin.last n)) * u (Fin.last n).castSucc / gridStep a b n ^ 2
    + (α (midGrid a b n (Fin.last n)) / gridStep a b n ^ 2 + γ b / 2) * u (Fin.last (n + 1))
    = g₁ / gridStep a b n + f b / 2

/-- **The mirror-imaging discretization of Robin conditions** `λ₀ u(a) + μ₀ u'(a) = g₀` and
`λ₁ u(b) + μ₁ u'(b) = g₁` at both ends ([quarteroni2000numerical] Exercise 12.10, with the missing
prime on `u'` restored): the interior equations of the variable-coefficient operator together with
the two end rows
`(α_{1/2}/h² + γ_0/2 + α_0 λ₀/(μ₀ h)) u_0 - α_{1/2} u_1/h² = α_0 g₀/(μ₀ h) + f_0/2` and
`(α_{n+1/2}/h² + γ_{n+1}/2 + α_{n+1} λ₁/(μ₁ h)) u_{n+1} - α_{n+1/2} u_n/h²
  = α_{n+1} g₁/(μ₁ h) + f_{n+1}/2`.
-/
def IsRobinSolution (a b : ℝ) (n : ℕ) (α γ f : ℝ → ℝ) (lam₀ mu₀ g₀ lam₁ mu₁ g₁ : ℝ)
    (u : Fin (n + 2) → ℝ) : Prop :=
  (∀ i : Fin n, variableCoeffOperator a b n α γ u i = f (uniformGrid a b n i.succ.castSucc)) ∧
  (α (midGrid a b n 0) / gridStep a b n ^ 2 + γ a / 2 + α a * lam₀ / (mu₀ * gridStep a b n)) * u 0
      - α (midGrid a b n 0) * u 1 / gridStep a b n ^ 2
    = α a * g₀ / (mu₀ * gridStep a b n) + f a / 2 ∧
  (α (midGrid a b n (Fin.last n)) / gridStep a b n ^ 2 + γ b / 2
      + α b * lam₁ / (mu₁ * gridStep a b n)) * u (Fin.last (n + 1))
      - α (midGrid a b n (Fin.last n)) * u (Fin.last n).castSucc / gridStep a b n ^ 2
    = α b * g₁ / (mu₁ * gridStep a b n) + f b / 2

end FiniteDifference

/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Numlib.LinearAlgebra.Matrix.BottDuffin
import Numlib.LinearAlgebra.Matrix.SVD
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Numlib.LinearAlgebra.Matrix.CauchyBinet
import Numlib.LinearAlgebra.Matrix.LeastSquares
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Electrical networks and the Bott–Duffin inverse

Section 2.13 of [benIsrael2003generalized] applies orthogonal constrained
inversion to branch voltages and currents. The application uses a real
node–branch incidence matrix and a positive diagonal conductance matrix.

## Deviations from the source

* The potential drop on a branch from node `i` to node `j` is `p i - p j`,
  as in (147).
* In (153b) the right-hand side is `A⁻¹ w + v`, as in (152).
-/

noncomputable section

namespace BenIsraelGreville.Chapter02

open Matrix
open scoped InnerProductSpace

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

section BottDuffin

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The matrix of orthogonal projection onto the chosen voltage or current space. -/
def networkProjection (L : Submodule 𝕜 (EuclideanSpace 𝕜 n)) : Matrix n n 𝕜 :=
  toEuclideanLin.symm (L.starProjection : EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 n)

/-- The projection matrix acts as orthogonal projection. -/
theorem networkProjection_toEuclideanLin (L : Submodule 𝕜 (EuclideanSpace 𝕜 n)) :
    toEuclideanLin (networkProjection L) =
      (L.starProjection : EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 n) :=
  toEuclideanLin.apply_symm_apply _

private theorem networkProjection_idempotent (L : Submodule 𝕜 (EuclideanSpace 𝕜 n)) :
    IsIdempotentElem (networkProjection L) := by
  change networkProjection L * networkProjection L = networkProjection L
  apply toEuclideanLin.injective
  ext1 x
  rw [toEuclideanLin_mul_apply, networkProjection_toEuclideanLin]
  exact L.starProjection_eq_self_iff.mpr (L.starProjection_apply_mem x)

/-- Projecting onto the orthogonal subspace gives the complementary matrix. -/
theorem networkProjection_orthogonal (L : Submodule 𝕜 (EuclideanSpace 𝕜 n)) :
    networkProjection Lᗮ = 1 - networkProjection L := by
  apply toEuclideanLin.injective
  ext1 x
  rw [toEuclideanLin_sub_apply, toEuclideanLin_one_apply, networkProjection_toEuclideanLin,
    networkProjection_toEuclideanLin]
  exact L.starProjection_orthogonal_val x

/-- **Exercise 107** of [benIsrael2003generalized], Chapter 2.
A nonzero quadratic form on every nonzero vector of the constraint
space guarantees existence of its Bott–Duffin inverse. -/
theorem exercise_107 (A : Matrix n n 𝕜) (L : Submodule 𝕜 (EuclideanSpace 𝕜 n))
    (hA : ∀ x ∈ L, x ≠ 0 → inner 𝕜 (toEuclideanLin A x) x ≠ 0) :
    IsUnit (A * networkProjection L + (1 - networkProjection L)) := by
  let P := networkProjection L
  let B := A * P + (1 - P)
  change IsUnit B
  apply Matrix.mulVec_injective_iff_isUnit.mp
  change Function.Injective B.mulVecLin
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro u hu
  change B *ᵥ u = 0 at hu
  let v : EuclideanSpace 𝕜 n := WithLp.toLp 2 u
  let x := L.starProjection v
  let y := v - x
  have hx : x ∈ L := L.starProjection_apply_mem v
  have hy : y ∈ Lᗮ := L.sub_starProjection_mem_orthogonal v
  have hv : toEuclideanLin A x + y = 0 := by
    have hB : toEuclideanLin B v = 0 := by
      simpa only [toEuclideanLin_apply, WithLp.ofLp_toLp, WithLp.toLp_eq_zero, v] using hu
    rw [show B = A * P + (1 - P) from rfl, map_add, LinearMap.add_apply,
      toEuclideanLin_mul_apply, toEuclideanLin_sub_apply, toEuclideanLin_one_apply,
      networkProjection_toEuclideanLin] at hB
    exact hB
  have hx₀ : x = 0 := by
    by_contra h
    have he := congrArg (fun w => inner 𝕜 w x) hv
    rw [inner_add_left, inner_zero_left, L.inner_left_of_mem_orthogonal hx hy, add_zero] at he
    exact (hA x hx h) he
  have hy₀ : y = 0 := by simpa only [hx₀, map_zero, zero_add] using hv
  have hzero : v = 0 := by
    change v - x = 0 at hy₀
    rwa [hx₀, sub_zero] at hy₀
  exact (WithLp.toLp_eq_zero 2).mp hzero

private theorem network_system_solution (A : Matrix n n 𝕜)
    (L : Submodule 𝕜 (EuclideanSpace 𝕜 n))
    (hA : IsUnit (A * networkProjection L + (1 - networkProjection L)))
    (b : EuclideanSpace 𝕜 n) (x y : EuclideanSpace 𝕜 n) :
    let B := A.bottDuffin (networkProjection L)
    (x ∈ L ∧ y ∈ Lᗮ ∧ toEuclideanLin A x + y = b) ↔
      x = toEuclideanLin B b ∧ y = toEuclideanLin (1 - A * B) b := by
  let P := networkProjection L
  intro B
  obtain ⟨hBAP, hPAB, hPB, hBP⟩ := bottDuffin_identities (networkProjection_idempotent L) hA
  change B * A * P = P at hBAP
  change P * A * B = P at hPAB
  change P * B = B at hPB
  change B * P = B at hBP
  have hPx (z : EuclideanSpace 𝕜 n) : toEuclideanLin P z = L.starProjection z :=
    DFunLike.congr_fun (networkProjection_toEuclideanLin L) z
  have hres : toEuclideanLin (1 - A * B) b = b - toEuclideanLin A (toEuclideanLin B b) := by
    rw [toEuclideanLin_sub_apply, toEuclideanLin_one_apply, toEuclideanLin_mul_apply]
  constructor
  · rintro ⟨hx, hy, h⟩
    have hX : toEuclideanLin P x = x := (hPx x).trans (L.starProjection_eq_self_iff.mpr hx)
    have hY : toEuclideanLin P y = 0 := (hPx y).trans (L.starProjection_apply_eq_zero_iff.mpr hy)
    have hBx : toEuclideanLin B b = x := by
      rw [← h, map_add, ← toEuclideanLin_mul_apply B A, ← hX,
        ← toEuclideanLin_mul_apply, hBAP, hX]
      have hy' : toEuclideanLin B y = 0 := by
        rw [← hBP, toEuclideanLin_mul_apply, hY, map_zero]
      rw [hy', add_zero]
    refine ⟨hBx.symm, ?_⟩
    rw [hres, hBx, ← h, add_sub_cancel_left]
  · rintro ⟨rfl, rfl⟩
    refine ⟨L.starProjection_eq_self_iff.mp ?_, L.starProjection_apply_eq_zero_iff.mp ?_, ?_⟩
    · rw [← hPx, ← toEuclideanLin_mul_apply, hPB]
    · rw [← hPx, hres, map_sub, ← toEuclideanLin_mul_apply A B b,
        ← toEuclideanLin_mul_apply P (A * B) b, ← Matrix.mul_assoc, hPAB, sub_self]
    · rw [hres, add_sub_cancel]

end BottDuffin

section DirectCurrent

/-- The real node–branch incidence matrix of a directed network. Each column
adds one at the tail and subtracts one at the head. A loop has zero column. -/
def incidenceMatrix (tail head : n → m) : Matrix m n ℝ :=
  Matrix.of fun i j => (if i = tail j then 1 else 0) - (if i = head j then 1 else 0)

omit [Fintype n] [DecidableEq n] in
/-- **Equation (147)** of [benIsrael2003generalized], Chapter 2.
Multiplication by the transpose takes node potentials to branch drops. -/
theorem incidenceMatrix_transpose_mulVec (tail head : n → m) (p : m → ℝ) (j : n) :
    ((incidenceMatrix tail head)ᵀ *ᵥ p) j = p (tail j) - p (head j) := by
  change (∑ i, ((if i = tail j then 1 else 0) - (if i = head j then 1 else 0)) * p i) = _
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
  simp

/-- Branch voltages arising from node potentials. -/
abbrev networkVoltageSpace (M : Matrix m n ℝ) : Submodule ℝ (EuclideanSpace ℝ n) :=
  LinearMap.range (toEuclideanLin Mᵀ)

/-- Branch currents satisfying Kirchhoff's current law. -/
abbrev networkCurrentSpace (M : Matrix m n ℝ) : Submodule ℝ (EuclideanSpace ℝ n) :=
  LinearMap.ker (toEuclideanLin M)

/-- **Equations (147)–(148)** of [benIsrael2003generalized], Chapter 2.
The current and voltage spaces are complementary and orthogonal. -/
theorem networkVoltageSpace_eq_orthogonal (M : Matrix m n ℝ) :
    networkVoltageSpace M = (networkCurrentSpace M)ᗮ := by
  rw [LinearMap.orthogonal_ker, ← toEuclideanLin_conjTranspose_eq_adjoint,
    conjTranspose_eq_transpose_of_trivial]

private theorem networkCurrentSpace_eq_orthogonal (M : Matrix m n ℝ) :
    networkCurrentSpace M = (networkVoltageSpace M)ᗮ := by
  rw [networkVoltageSpace_eq_orthogonal, Submodule.orthogonal_orthogonal]

/-- **Equation (149)** of [benIsrael2003generalized], Chapter 2.
In each branch, the conductance times the voltage difference balances
the difference in currents. -/
theorem network_ohm_iff (a : n → ℝ) (v w x y : EuclideanSpace ℝ n) :
    toEuclideanLin (diagonal a) x + y = toEuclideanLin (diagonal a) v + w ↔
      ∀ j, a j * (x j - v j) + (y j - w j) = 0 := by
  constructor
  · intro h j
    have hj := congrArg (fun z : EuclideanSpace ℝ n => z j) h
    simp only [PiLp.add_apply, toEuclideanLin_apply, mulVec_diagonal] at hj
    rw [mul_sub]
    linarith
  · intro h
    ext j
    simp only [PiLp.add_apply, toEuclideanLin_apply, mulVec_diagonal]
    have hj := h j
    rw [mul_sub] at hj
    linarith

/-- The transfer matrix sends a branch current source to its induced voltages. -/
def networkTransferMatrix (M : Matrix m n ℝ) (a : n → ℝ) : Matrix n n ℝ :=
  (diagonal a).bottDuffin (networkProjection (networkVoltageSpace M))

/-- The dual transfer matrix sends a branch voltage source to its induced currents. -/
def networkDualTransferMatrix (M : Matrix m n ℝ) (a : n → ℝ) : Matrix n n ℝ :=
  (diagonal fun j => (a j)⁻¹).bottDuffin (networkProjection (networkCurrentSpace M))

private theorem diag_quadratic_ne_zero (a : n → ℝ) (ha : ∀ j, 0 < a j)
    (x : EuclideanSpace ℝ n) (hx : x ≠ 0) :
    inner ℝ (toEuclideanLin (diagonal a) x) x ≠ 0 := by
  have hP : (diagonal a).PosDef := Matrix.posDef_diagonal_iff.mpr ha
  have h0 : WithLp.ofLp x ≠ 0 := by simpa using hx
  have h := hP.dotProduct_mulVec_pos h0
  rw [real_inner_comm, EuclideanSpace.inner_eq_star_dotProduct, ofLp_toEuclideanLin]
  rw [dotProduct_comm]
  exact ne_of_gt (by simpa using h)

/-- **Equations (149)–(151)** of [benIsrael2003generalized], Chapter 2.
The current and voltage laws together with the branch Ohm equations have
a unique solution, given by the transfer matrix and its residual. -/
theorem networkEquations (M : Matrix m n ℝ) (a : n → ℝ) (ha : ∀ j, 0 < a j)
    (v w x y : EuclideanSpace ℝ n) :
    let A := diagonal a
    let B := networkTransferMatrix M a
    let b := toEuclideanLin A v + w
    (x ∈ networkVoltageSpace M ∧ y ∈ networkCurrentSpace M ∧
      toEuclideanLin A x + y = b) ↔
      x = toEuclideanLin B b ∧ y = toEuclideanLin (1 - A * B) b := by
  rw [networkCurrentSpace_eq_orthogonal M]
  exact network_system_solution _ _ (exercise_107 _ _ fun z _ hz =>
    diag_quadratic_ne_zero a ha z hz) _ _ _

/-- **Equations (152)–(153)** of [benIsrael2003generalized], Chapter 2.
With reciprocal conductances the exchanged current and voltage problem is
solved by the dual transfer matrix. -/
theorem dualNetworkEquations (M : Matrix m n ℝ) (a : n → ℝ) (ha : ∀ j, 0 < a j)
    (v w x y : EuclideanSpace ℝ n) :
    let R := diagonal fun j => (a j)⁻¹
    let B := networkDualTransferMatrix M a
    let b := toEuclideanLin R w + v
    (y ∈ networkCurrentSpace M ∧ x ∈ networkVoltageSpace M ∧
      toEuclideanLin R y + x = b) ↔
      y = toEuclideanLin B b ∧ x = toEuclideanLin (1 - R * B) b := by
  rw [networkVoltageSpace_eq_orthogonal M]
  exact network_system_solution _ _ (exercise_107 _ _ fun z _ hz =>
    diag_quadratic_ne_zero _ (fun j => inv_pos.mpr (ha j)) z hz) _ _ _

private theorem mul_reciprocalConductance (a : n → ℝ) (ha : ∀ j, 0 < a j) :
    (diagonal fun j => (a j)⁻¹) * diagonal a = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext j
  exact inv_mul_cancel₀ (ha j).ne'

private theorem reciprocalConductance_mul (a : n → ℝ) (ha : ∀ j, 0 < a j) :
    diagonal a * (diagonal fun j => (a j)⁻¹) = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext j
  exact mul_inv_cancel₀ (ha j).ne'

/-- The primal and dual Ohm constraints are equivalent along with the
two Kirchhoff laws. -/
theorem network_equations_equivalent (M : Matrix m n ℝ) (a : n → ℝ) (ha : ∀ j, 0 < a j)
    (v w x y : EuclideanSpace ℝ n) :
    let A := diagonal a
    let R := diagonal fun j => (a j)⁻¹
    (x ∈ networkVoltageSpace M ∧ y ∈ networkCurrentSpace M ∧
      toEuclideanLin A x + y = toEuclideanLin A v + w) ↔
      y ∈ networkCurrentSpace M ∧ x ∈ networkVoltageSpace M ∧
        toEuclideanLin R y + x = toEuclideanLin R w + v := by
  intro A R
  have hRA : R * A = 1 := mul_reciprocalConductance a ha
  have hAR : A * R = 1 := reciprocalConductance_mul a ha
  constructor
  · rintro ⟨hx, hy, h⟩
    have he := congrArg (toEuclideanLin R) h
    rw [map_add, map_add, ← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply,
      hRA, toEuclideanLin_one_apply, toEuclideanLin_one_apply] at he
    exact ⟨hy, hx, by simpa only [add_comm] using he⟩
  · rintro ⟨hy, hx, h⟩
    have he := congrArg (toEuclideanLin A) h
    rw [map_add, map_add, ← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply,
      hAR, toEuclideanLin_one_apply, toEuclideanLin_one_apply] at he
    exact ⟨hx, hy, by simpa only [add_comm] using he⟩

/-- **Equation (154)** of [benIsrael2003generalized], Chapter 2.
The primal and dual transfer matrices give complementary response
operators for the two placements of the conductance factor. -/
theorem networkTransferMatrix_duality (M : Matrix m n ℝ) (a : n → ℝ) (ha : ∀ j, 0 < a j) :
    (diagonal fun j => (a j)⁻¹) * networkDualTransferMatrix M a +
      networkTransferMatrix M a * diagonal a = 1 := by
  let A := diagonal a
  let R := diagonal fun j => (a j)⁻¹
  let B := networkTransferMatrix M a
  let D := networkDualTransferMatrix M a
  apply toEuclideanLin.injective
  ext1 v
  let x := toEuclideanLin B (toEuclideanLin A v)
  let y := toEuclideanLin (1 - A * B) (toEuclideanLin A v)
  have hp := (networkEquations M a ha v 0 x y).mpr (by
    simp only [add_zero]
    exact ⟨rfl, rfl⟩)
  have hd := (dualNetworkEquations M a ha v 0 x y).mp
    ((network_equations_equivalent M a ha v 0 x y).mp hp)
  have he : x = toEuclideanLin (1 - R * D) v := by simpa only [map_zero, zero_add] using hd.2
  rw [map_add, LinearMap.add_apply, toEuclideanLin_mul_apply B A, toEuclideanLin_one_apply]
  change toEuclideanLin (R * D) v + x = v
  rw [he, toEuclideanLin_sub_apply, toEuclideanLin_one_apply, add_sub_cancel]

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- Every node is reachable from every other by unoriented branches. -/
def NetworkConnected (tail head : n → m) : Prop :=
  ∀ i j, Relation.ReflTransGen
    (fun a b => ∃ e, (tail e = a ∧ head e = b) ∨ (tail e = b ∧ head e = a)) i j

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
private theorem NetworkConnected.eq_of_edge_eq {tail head : n → m}
    (hc : NetworkConnected tail head) {V : Type*} (f : m → V)
    (h : ∀ e, f (tail e) = f (head e)) (i j : m) : f i = f j := by
  induction hc i j using Relation.ReflTransGen.trans_induction_on with
  | refl => rfl
  | single he =>
    obtain ⟨e, ⟨hi, hj⟩ | ⟨hj, hi⟩⟩ := he
    · simpa only [hi, hj] using h e
    · simpa only [hi, hj] using (h e).symm
  | trans _ _ hi hj => exact hi.trans hj

omit [Fintype n] [DecidableEq n] in
/-- The transpose of a connected incidence matrix has exactly the
constant vectors in its kernel. -/
theorem incidenceMatrix_transpose_ker [Nonempty m] (tail head : n → m)
    (hc : NetworkConnected tail head) :
    LinearMap.ker (incidenceMatrix tail head)ᵀ.mulVecLin =
      ℝ ∙ (fun _ : m => (1 : ℝ)) := by
  classical
  ext x
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  change (incidenceMatrix tail head)ᵀ *ᵥ x = 0 ↔ _
  constructor
  · intro hx
    let i₀ : m := Classical.choice inferInstance
    have h (e : n) : x (tail e) = x (head e) := by
      have h := congrFun hx e
      rw [incidenceMatrix_transpose_mulVec, Pi.zero_apply, sub_eq_zero] at h
      exact h
    refine ⟨x i₀, funext fun i => ?_⟩
    simpa only [Pi.smul_apply, smul_eq_mul, mul_one] using hc.eq_of_edge_eq x h i₀ i
  · rintro ⟨c, rfl⟩
    funext e
    rw [incidenceMatrix_transpose_mulVec]
    exact sub_self _

omit [DecidableEq n] in
/-- **Exercise 110** of [benIsrael2003generalized], Chapter 2.
A connected incidence matrix has rank one less than its node count. -/
theorem exercise_110 [Nonempty m] (tail head : n → m) (hc : NetworkConnected tail head) :
    (incidenceMatrix tail head).rank = Fintype.card m - 1 := by
  classical
  let M := incidenceMatrix tail head
  have hx : (fun _ : m => (1 : ℝ)) ≠ 0 := fun he =>
    one_ne_zero (congrFun he (Classical.choice inferInstance))
  have ht := LinearMap.finrank_range_add_finrank_ker Mᵀ.mulVecLin
  change Mᵀ.rank + Module.finrank ℝ Mᵀ.mulVecLin.ker = Module.finrank ℝ (m → ℝ) at ht
  rw [Matrix.rank_transpose, incidenceMatrix_transpose_ker tail head hc,
    finrank_span_singleton hx, Module.finrank_fintype_fun_eq_card] at ht
  change M.rank = Fintype.card m - 1
  omega

omit [DecidableEq n] in
/-- **Exercise 109** of [benIsrael2003generalized], Chapter 2.
For a connected incidence matrix, the complementary projector is the
matrix with every entry equal to the reciprocal node count. -/
theorem exercise_109 [Nonempty m] (tail head : n → m) (hc : NetworkConnected tail head)
    (U : Matrix n m ℝ) (hU : (incidenceMatrix tail head).IsInnerInverse U)
    (hH : (incidenceMatrix tail head * U).IsHermitian) :
    1 - incidenceMatrix tail head * U = Matrix.of (fun _ _ : m => (Fintype.card m : ℝ)⁻¹) := by
  let M := incidenceMatrix tail head
  let Q : Matrix m m ℝ := 1 - M * U
  have hQM : Q * M = 0 := by
    rw [show Q = 1 - M * U from rfl, Matrix.sub_mul, Matrix.one_mul, hU, sub_self]
  have hcol (i : m) (e : n) : Q i (tail e) = Q i (head e) := by
    have h := congrArg (fun B : Matrix m n ℝ => B i e) hQM
    change (∑ k, Q i k * ((if k = tail e then 1 else 0) -
      (if k = head e then 1 else 0))) = 0 at h
    simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero] at h
    simpa only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, sub_eq_zero] using h
  have hsame (i j k : m) : Q i j = Q i k := hc.eq_of_edge_eq (Q i) (hcol i) j k
  have hMt : Mᵀ *ᵥ (fun _ : m => (1 : ℝ)) = 0 := by
    funext e
    rw [incidenceMatrix_transpose_mulVec]
    exact sub_self _
  have hQ : Q *ᵥ (fun _ : m => (1 : ℝ)) = (fun _ => 1) := by
    have hs : (M * U)ᵀ = M * U := hH.isSymm.eq
    change (1 - M * U) *ᵥ _ = _
    rw [sub_mulVec, one_mulVec, ← hs, transpose_mul, ← mulVec_mulVec, hMt, mulVec_zero,
      sub_zero]
  ext i j
  have h := congrFun hQ i
  change (∑ k, Q i k * 1) = 1 at h
  simp only [mul_one, hsame i _ j, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  change Q i j = (Fintype.card m : ℝ)⁻¹
  have he : (Fintype.card m : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [← one_div, eq_div_iff he, mul_comm]
  exact h

omit [DecidableEq n] in
/-- **Exercise 108** of [benIsrael2003generalized], Chapter 2.
The complex admittance equations, including a symmetric coupling
matrix, can be written either in block form or branch by branch. -/
theorem exercise_108 (A : Matrix n n ℂ) (v w x y : n → ℂ) :
    A *ᵥ x + y = A *ᵥ v + w ↔
      ∀ j, (∑ k, A j k * (x k - v k)) + (y j - w j) = 0 := by
  have h : A *ᵥ (x - v) + (y - w) = A *ᵥ x + y - (A *ᵥ v + w) := by
    rw [mulVec_sub]
    abel
  rw [← sub_eq_zero, ← h]
  exact ⟨fun he j => congrFun he j, fun he => funext he⟩

/-- **Exercise 108**. The complexified incidence equations and
admittance equation define a state of the alternating-current network. -/
def IsACNetworkState (M : Matrix m n ℝ) (A : Matrix n n ℂ)
    (v w x y : n → ℂ) : Prop :=
  (M.map Complex.ofReal) *ᵥ y = 0 ∧
  (∃ p : m → ℂ, (M.map Complex.ofReal)ᵀ *ᵥ p = x) ∧
  A *ᵥ x + y = A *ᵥ v + w

omit [DecidableEq m] in
/-- In the absence of mutual coupling, the complex branch equations
of Exercise 108 use one admittance per branch. -/
theorem exercise_108_uncoupled (M : Matrix m n ℝ) (a : n → ℂ) (v w x y : n → ℂ) :
    IsACNetworkState M (diagonal a) v w x y ↔
      (M.map Complex.ofReal) *ᵥ y = 0 ∧
      (∃ p : m → ℂ, (M.map Complex.ofReal)ᵀ *ᵥ p = x) ∧
      ∀ j, a j * (x j - v j) + (y j - w j) = 0 := by
  unfold IsACNetworkState
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  rw [exercise_108]
  simp only [Matrix.diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]

omit [DecidableEq m] [DecidableEq n] in
/-- A symmetric admittance matrix represents mutual coupling through
its off-diagonal entries, with the same complex Kirchhoff equations. -/
theorem exercise_108_coupled (M : Matrix m n ℝ) (A : Matrix n n ℂ) (v w x y : n → ℂ) :
    (A.IsSymm ∧ IsACNetworkState M A v w x y) ↔
      (∀ j k, A j k = A k j) ∧ (M.map Complex.ofReal) *ᵥ y = 0 ∧
      (∃ p : m → ℂ, (M.map Complex.ofReal)ᵀ *ᵥ p = x) ∧
      ∀ j, (∑ k, A j k * (x k - v k)) + (y j - w j) = 0 := by
  rw [IsACNetworkState, exercise_108]
  exact and_congr_left' ⟨fun h j k => (congr_fun₂ h.eq j k).symm,
    fun h => Matrix.ext fun j k => h k j⟩

end DirectCurrent

section FigureResults

open Matrix

/-- The node–branch incidence matrix of **Figure 1** in Chapter 2 of
[benIsrael2003generalized], with the printed orientations and order
of the four nodes and the six branches. -/
theorem section13_figure1 :
    incidenceMatrix (![0, 1, 1, 2, 2, 3] : Fin 6 → Fin 4) ![1, 2, 3, 0, 3, 0] =
      !![1, 0, 0, -1, 0, -1;
        -1, 1, 1, 0, 0, 0;
        0, -1, 0, 1, 1, 0;
        0, 0, -1, 0, -1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [incidenceMatrix]

end FigureResults

section TreesResults

open Matrix
open scoped Sym2

variable {V E K : Type*}

/-- The unoriented graph of a node–branch network, with loops omitted
and multiple branches between the same endpoints represented by one edge. -/
def networkSimpleGraph (tail head : E → V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ∃ e, (tail e = x ∧ head e = y) ∨ (tail e = y ∧ head e = x)
  symm := ⟨fun _ _ ⟨hne, e, he⟩ => ⟨hne.symm, e, he.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Reachability disregards branch orientations, and loop branches do not change it. -/
theorem networkSimpleGraph_connected [Nonempty V] {tail head : E → V}
    (h : NetworkConnected tail head) : (networkSimpleGraph tail head).Connected := by
  refine ⟨fun u v => ?_⟩
  rw [SimpleGraph.reachable_iff_reflTransGen]
  induction h u v using Relation.ReflTransGen.trans_induction_on with
  | refl => exact .refl
  | @single x y he =>
      by_cases hxy : x = y
      · subst y
        exact .refl
      · exact Relation.ReflTransGen.single ⟨hxy, he⟩
  | trans _ _ h₁ h₂ => exact h₁.trans h₂

variable [Fintype V] [DecidableEq V] [Fintype E] [Fintype K]

omit [Fintype V] [Fintype E] in
private theorem incidence_col_eq_single_sub (tail head : E → V) (e : E) :
    (incidenceMatrix tail head).col e =
      Pi.single (tail e) (1 : ℝ) - Pi.single (head e) 1 := by
  funext v
  simp [incidenceMatrix, Matrix.col_apply, Pi.single_apply]

omit [Fintype V] in
/-- A list of independent incidence columns has no loops or repeated
unordered endpoint pairs, even when the original network has such branches. -/
theorem incidence_independent_distinct_edges [DecidableEq E] (tail head : E → V)
    (hI : Function.Injective (incidenceMatrix tail head).mulVecLin) :
    (∀ e, tail e ≠ head e) ∧ Function.Injective (fun e => s(tail e, head e)) := by
  let M := incidenceMatrix tail head
  constructor
  · intro e he
    have hz : M *ᵥ Pi.single e (1 : ℝ) = M *ᵥ 0 := by
      rw [mulVec_single_one, mulVec_zero, incidence_col_eq_single_sub, he, sub_self]
    have h := congrFun (hI hz) e
    simp at h
  · intro e f hef
    by_contra! hne
    have htail : (tail e, head e) = (tail f, head f) ∨
        (tail e, head e) = (head f, tail f) := Sym2.mk_eq_mk_iff.mp hef
    rcases htail with h | h
    · obtain ⟨ht, hh⟩ := Prod.mk.inj h
      have hs : M *ᵥ Pi.single e (1 : ℝ) = M *ᵥ Pi.single f 1 := by
        rw [mulVec_single_one, mulVec_single_one, incidence_col_eq_single_sub,
          incidence_col_eq_single_sub, ht, hh]
      have he := congrFun (hI hs) e
      simp [hne] at he
    · obtain ⟨ht, hh⟩ := Prod.mk.inj h
      have hs : M *ᵥ Pi.single e (1 : ℝ) = M *ᵥ (-Pi.single f 1) := by
        rw [mulVec_single_one, mulVec_neg, mulVec_single_one, incidence_col_eq_single_sub,
          incidence_col_eq_single_sub, ht, hh, neg_sub]
      have he := congrFun (hI hs) e
      simp [hne] at he

omit [Fintype V] [DecidableEq V] [Fintype K] in
private theorem networkSimpleGraph_edgeSet_eq (tail head : K → V)
    (hloop : ∀ e, tail e ≠ head e) :
    (networkSimpleGraph tail head).edgeSet = Set.range fun e => s(tail e, head e) := by
  ext q
  induction q using Sym2.inductionOn with
  | _ u v =>
    rw [SimpleGraph.mem_edgeSet]
    change (u ≠ v ∧ ∃ e, (tail e = u ∧ head e = v) ∨
      (tail e = v ∧ head e = u)) ↔ ∃ e, s(tail e, head e) = s(u, v)
    simp only [Sym2.eq_iff]
    constructor
    · exact And.right
    · rintro ⟨e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact ⟨hloop e, e, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨(hloop e).symm, e, Or.inr ⟨rfl, rfl⟩⟩

variable [Nonempty V] [DecidableEq K]

omit [DecidableEq K] in
/-- The independent $m-1$ selected branches have the same incidence
column space as the full connected network. -/
theorem spanningTree_incidence_range (tail head : E → V) (hconn : NetworkConnected tail head)
    (chooseBranch : K ↪ E) (hcard : Fintype.card K = Fintype.card V - 1)
    (hI : Function.Injective (incidenceMatrix (tail ∘ chooseBranch)
      (head ∘ chooseBranch)).mulVecLin) :
    LinearMap.range (incidenceMatrix (tail ∘ chooseBranch) (head ∘ chooseBranch)).mulVecLin =
      LinearMap.range (incidenceMatrix tail head).mulVecLin := by
  classical
  apply Submodule.eq_of_le_of_finrank_le
  · rw [Matrix.range_mulVecLin, Matrix.range_mulVecLin]
    apply Submodule.span_mono
    rintro v ⟨j, hj⟩
    exact ⟨chooseBranch j, hj⟩
  · rw [LinearMap.finrank_range_of_inj hI, Module.finrank_fintype_fun_eq_card, hcard]
    exact (exercise_110 tail head hconn).le

omit [DecidableEq K] in
private theorem spanningTree_networkConnected (tail head : E → V)
    (hconn : NetworkConnected tail head)
    (chooseBranch : K ↪ E) (hcard : Fintype.card K = Fintype.card V - 1)
    (hI : Function.Injective (incidenceMatrix (tail ∘ chooseBranch)
      (head ∘ chooseBranch)).mulVecLin) :
    NetworkConnected (tail ∘ chooseBranch) (head ∘ chooseBranch) := by
  classical
  let T := incidenceMatrix (tail ∘ chooseBranch) (head ∘ chooseBranch)
  let M := incidenceMatrix tail head
  have hr : LinearMap.range T.mulVecLin = LinearMap.range M.mulVecLin :=
    spanningTree_incidence_range tail head hconn chooseBranch hcard hI
  intro u v
  let r := Relation.ReflTransGen (fun x y => ∃ e : K,
    (tail (chooseBranch e) = x ∧ head (chooseBranch e) = y) ∨
      (tail (chooseBranch e) = y ∧ head (chooseBranch e) = x))
  by_contra h
  let p (x : V) : ℝ := if r u x then 1 else 0
  have hT : Tᵀ *ᵥ p = 0 := by
    funext e
    rw [incidenceMatrix_transpose_mulVec, Pi.zero_apply, sub_eq_zero]
    have he : r (tail (chooseBranch e)) (head (chooseBranch e)) :=
      Relation.ReflTransGen.single ⟨e, Or.inl ⟨rfl, rfl⟩⟩
    have he' : r (head (chooseBranch e)) (tail (chooseBranch e)) :=
      Relation.ReflTransGen.single ⟨e, Or.inr ⟨rfl, rfl⟩⟩
    simp only [p, Function.comp_apply]
    rw [show r u (tail (chooseBranch e)) ↔ r u (head (chooseBranch e)) from
      ⟨fun hp => hp.trans he, fun hp => hp.trans he'⟩]
  have hM : p ∈ LinearMap.ker Mᵀ.mulVecLin := by
    rw [LinearMap.mem_ker]
    funext e
    have hcol : M.col e ∈ LinearMap.range T.mulVecLin :=
      hr.symm ▸ ⟨Pi.single e 1, Matrix.mulVec_single_one M e⟩
    obtain ⟨f, hf⟩ := hcol
    change M.col e ⬝ᵥ p = 0
    have hvec : p ᵥ* T = 0 := by
      rw [← Matrix.vecMul_transpose Tᵀ, Matrix.transpose_transpose] at hT
      exact hT
    rw [← hf, Matrix.mulVecLin_apply, dotProduct_comm, dotProduct_mulVec,
      hvec, zero_dotProduct]
  rw [incidenceMatrix_transpose_ker tail head hconn, Submodule.mem_span_singleton] at hM
  obtain ⟨c, hc⟩ := hM
  have hp : p u = p v := by rw [← hc]; rfl
  change ¬r u v at h
  simp [p, h, show r u u from Relation.ReflTransGen.refl] at hp

/-- **Exercise 112(a)** of [benIsrael2003generalized], Chapter 2.
The $m-1$ independent incidence columns of a connected network select
a connected acyclic spanning graph. The selected branches have distinct
unordered endpoint pairs, so no loop or parallel pair is lost in this graph. -/
theorem exercise_112 (tail head : E → V) (hconn : NetworkConnected tail head)
    (chooseBranch : K ↪ E) (hcard : Fintype.card K = Fintype.card V - 1)
    (hI : Function.Injective (incidenceMatrix (tail ∘ chooseBranch)
      (head ∘ chooseBranch)).mulVecLin) :
    (networkSimpleGraph (tail ∘ chooseBranch) (head ∘ chooseBranch)).IsTree ∧
    (∀ e, tail (chooseBranch e) ≠ head (chooseBranch e)) ∧
    Function.Injective (fun e => s(tail (chooseBranch e), head (chooseBranch e))) := by
  obtain ⟨hloop, hdistinct⟩ := incidence_independent_distinct_edges
    (tail ∘ chooseBranch) (head ∘ chooseBranch) hI
  refine ⟨SimpleGraph.isTree_iff_connected_and_card.mpr ⟨?_, ?_⟩, hloop, hdistinct⟩
  · exact networkSimpleGraph_connected (spanningTree_networkConnected tail head hconn
      chooseBranch hcard hI)
  · change (networkSimpleGraph (tail ∘ chooseBranch) (head ∘ chooseBranch)).edgeSet.ncard + 1 = _
    rw [networkSimpleGraph_edgeSet_eq _ _ hloop, Set.ncard_range_of_injective hdistinct,
      Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hcard]
    exact Nat.sub_add_cancel (Fintype.card_pos_iff.mpr inferInstance)

end TreesResults

section PathsResults

open Matrix
open scoped Sym2

variable {V E K : Type*}

noncomputable section

private def traversedBranch {tail head : K → V} {u v : V}
    (h : (networkSimpleGraph tail head).Adj u v) : K :=
  Classical.choose h.2

private theorem traversedBranch_spec {tail head : K → V} {u v : V}
    (h : (networkSimpleGraph tail head).Adj u v) :
    (tail (traversedBranch h) = u ∧ head (traversedBranch h) = v) ∨
      (tail (traversedBranch h) = v ∧ head (traversedBranch h) = u) :=
  Classical.choose_spec h.2

private theorem traversedBranch_edge {tail head : K → V} {u v : V}
    (h : (networkSimpleGraph tail head).Adj u v) :
    s(tail (traversedBranch h), head (traversedBranch h)) = s(u, v) :=
  Sym2.eq_iff.mpr (traversedBranch_spec h)

variable [DecidableEq V] [DecidableEq K]

/-- A walk's coefficients add one along a branch's direction and subtract
one against it. When branch endpoint pairs are distinct, the branch at
each step is uniquely determined by the walk. -/
def networkWalkCoefficients (tail head : K → V) :
    {u v : V} → (networkSimpleGraph tail head).Walk u v → (K → ℝ)
  | _, _, .nil => 0
  | u, _, .cons h w =>
    Pi.single (traversedBranch h) (if tail (traversedBranch h) = u then 1 else -1) +
      networkWalkCoefficients tail head w

private theorem incidence_walkStep [Fintype K] {tail head : K → V} {u v : V}
    (h : (networkSimpleGraph tail head).Adj u v) :
    incidenceMatrix tail head *ᵥ
        Pi.single (traversedBranch h) (if tail (traversedBranch h) = u then 1 else -1) =
      Pi.single u (1 : ℝ) - Pi.single v 1 := by
  obtain ⟨ht, hh⟩ | ⟨ht, hh⟩ := traversedBranch_spec h
  · rw [ht, ite_eq_left rfl, mulVec_single_one]
    funext x
    simp [incidenceMatrix, Matrix.col_apply, Pi.single_apply, ht, hh]
  · have hne : v ≠ u := h.1.symm
    rw [ht, ite_eq_right hne]
    have hneg : Pi.single (M := fun _ => ℝ) (traversedBranch h) (-1) =
        -Pi.single (traversedBranch h) 1 := by
      funext e
      by_cases he : e = traversedBranch h <;> simp [he]
    rw [hneg, mulVec_neg, mulVec_single_one]
    funext x
    simp [incidenceMatrix, Matrix.col_apply, Pi.single_apply, ht, hh, neg_sub]

/-- Incidence multiplication telescopes the signed coefficients of any
walk to the difference of the unit vectors at its endpoints. -/
theorem incidenceMatrix_mulVec_walkCoefficients [Fintype K] (tail head : K → V)
    {u v : V} (w : (networkSimpleGraph tail head).Walk u v) :
    incidenceMatrix tail head *ᵥ networkWalkCoefficients tail head w =
      Pi.single u (1 : ℝ) - Pi.single v 1 := by
  induction w with
  | nil => simp [networkWalkCoefficients]
  | cons h w ih =>
    rw [networkWalkCoefficients, mulVec_add, incidence_walkStep h, ih]
    abel

private theorem walkCoefficients_eq_zero_of_notMem_edges {tail head : K → V}
    {u v : V} (w : (networkSimpleGraph tail head).Walk u v) (e : K)
    (he : s(tail e, head e) ∉ w.edges) : networkWalkCoefficients tail head w e = 0 := by
  induction w with
  | nil => rfl
  | cons h w ih =>
    rw [SimpleGraph.Walk.edges_cons, List.mem_cons, not_or] at he
    have hne : e ≠ traversedBranch h := fun hsame => he.1 (hsame ▸ traversedBranch_edge h)
    simp [networkWalkCoefficients, hne, ih he.2]

/-- Every coefficient of a branch-distinct walk is zero, plus one, or minus one. -/
theorem networkWalkCoefficients_unit {tail head : K → V} {u v : V}
    (w : (networkSimpleGraph tail head).Walk u v) (hw : w.IsTrail) (e : K) :
    networkWalkCoefficients tail head w e = 0 ∨ networkWalkCoefficients tail head w e = 1 ∨
      networkWalkCoefficients tail head w e = -1 := by
  induction w with
  | nil => exact Or.inl rfl
  | @cons x y z h w ih =>
    obtain ⟨hw', hn⟩ := SimpleGraph.Walk.isTrail_cons h w |>.mp hw
    by_cases he : e = traversedBranch h
    · subst e
      have hzero := walkCoefficients_eq_zero_of_notMem_edges w (traversedBranch h)
        (by rw [traversedBranch_edge h]; exact hn)
      by_cases hdir : tail (traversedBranch h) = x <;>
        simp [networkWalkCoefficients, hzero, hdir]
    · simpa [networkWalkCoefficients, Pi.single_apply, he] using ih hw'

variable [Fintype V] [Nonempty V] [Fintype E] [Fintype K]

/-- **Exercise 112(b)** of [benIsrael2003generalized], Chapter 2.
Every branch column is the signed sum along the simple path in the
chosen tree from the branch's tail to its head. These are its unique
tree coordinates. -/
theorem exercise_112_signed_tree_path (tail head : E → V) (hconn : NetworkConnected tail head)
    (chooseBranch : K ↪ E) (hcard : Fintype.card K = Fintype.card V - 1)
    (hI : Function.Injective (incidenceMatrix (tail ∘ chooseBranch)
      (head ∘ chooseBranch)).mulVecLin) (e : E) :
    ∃ w : (networkSimpleGraph (tail ∘ chooseBranch) (head ∘ chooseBranch)).Walk
        (tail e) (head e), w.IsPath ∧
      let x := networkWalkCoefficients (tail ∘ chooseBranch) (head ∘ chooseBranch) w
      incidenceMatrix (tail ∘ chooseBranch) (head ∘ chooseBranch) *ᵥ x =
        (incidenceMatrix tail head).col e ∧
      (∀ k, x k = 0 ∨ x k = 1 ∨ x k = -1) ∧
      ∀ y : K → ℝ, incidenceMatrix (tail ∘ chooseBranch) (head ∘ chooseBranch) *ᵥ y =
        (incidenceMatrix tail head).col e → y = x := by
  have hTree := (exercise_112 tail head hconn chooseBranch hcard hI).1
  obtain ⟨w, hw⟩ := hTree.connected.exists_isPath (tail e) (head e)
  refine ⟨w, hw, ?_⟩
  have hc := incidenceMatrix_mulVec_walkCoefficients (tail ∘ chooseBranch) (head ∘ chooseBranch) w
  have hcol : (incidenceMatrix tail head).col e =
      Pi.single (tail e) (1 : ℝ) - Pi.single (head e) 1 := by
    funext v
    simp [incidenceMatrix, Matrix.col_apply, Pi.single_apply]
  rw [← hcol] at hc
  exact ⟨hc, networkWalkCoefficients_unit w hw.isTrail, fun y hy => hI (hy.trans hc.symm)⟩

/-- A fundamental circuit is the added branch followed by the simple
tree path from its head back to its tail. Its branch set records the
circuit independently of the direction of traversal. -/
def IsFundamentalNetworkCircuit (tail head : E → V) (chooseBranch : K ↪ E)
    (e : E) (circuit : Set E) : Prop :=
  e ∉ Set.range chooseBranch ∧
  ∃ p : (networkSimpleGraph (tail ∘ chooseBranch) (head ∘ chooseBranch)).Path
      (head e) (tail e),
    circuit = insert e (chooseBranch '' {k | s(tail (chooseBranch k), head (chooseBranch k)) ∈
      p.val.edges})

/-- **Exercise 112(c)** of [benIsrael2003generalized], Chapter 2.
A branch outside the spanning tree belongs to exactly one fundamental
circuit. A loop outside the tree has the singleton circuit, and parallel
nontree branches retain their distinct labels. -/
theorem exercise_112_fundamentalCircuit (tail head : E → V) (hconn : NetworkConnected tail head)
    (chooseBranch : K ↪ E) (hcard : Fintype.card K = Fintype.card V - 1)
    (hI : Function.Injective (incidenceMatrix (tail ∘ chooseBranch)
      (head ∘ chooseBranch)).mulVecLin) (e : E) (he : e ∉ Set.range chooseBranch) :
    ∃! circuit : Set E, e ∈ circuit ∧
      circuit \ {e} ⊆ Set.range chooseBranch ∧
      IsFundamentalNetworkCircuit tail head chooseBranch e circuit := by
  have hTree := (exercise_112 tail head hconn chooseBranch hcard hI).1
  obtain ⟨w, hw⟩ := hTree.connected.exists_isPath (head e) (tail e)
  let p : (networkSimpleGraph (tail ∘ chooseBranch) (head ∘ chooseBranch)).Path
      (head e) (tail e) := ⟨w, hw⟩
  let s : Set K := {k | s(tail (chooseBranch k), head (chooseBranch k)) ∈ p.val.edges}
  let circuit : Set E := insert e (chooseBranch '' s)
  have hsub : circuit \ {e} ⊆ Set.range chooseBranch := by
    rintro j ⟨hj, hne⟩
    rcases hj with rfl | ⟨k, _, rfl⟩
    · exact (hne rfl).elim
    · exact ⟨k, rfl⟩
  refine ⟨circuit, ⟨Set.mem_insert e _, hsub, he, p, rfl⟩, ?_⟩
  rintro t ⟨_, _, _, q, rfl⟩
  rw [(hTree.isAcyclic.subsingleton_path (head e) (tail e)).elim q p]

end

end PathsResults

section IncidenceMinorsResults

open Matrix

variable {V E : Type*} [DecidableEq V]

private theorem sum_incidence_endpoint_indicator {r : ℕ} (f : Fin r ↪ V) (v : V) :
    (∑ i, if f i = v then (1 : ℝ) else 0) = if v ∈ Set.range f then 1 else 0 := by
  classical
  by_cases hv : v ∈ Set.range f
  · obtain ⟨j, rfl⟩ := hv
    simp [f.injective.eq_iff]
  · have h i : f i ≠ v := fun he => hv ⟨i, he⟩
    simp [h, hv]

/-- Every square minor of a node–branch incidence matrix has determinant
zero, one, or minus one. This also allows repeated column indices, which
give zero determinant. -/
theorem incidenceMinor_det_sign (tail head : E → V) {r : ℕ}
    (rows : Fin r ↪ V) (cols : Fin r → E) :
    let d := ((incidenceMatrix tail head).submatrix rows cols).det
    d = 0 ∨ d = 1 ∨ d = -1 := by
  classical
  induction r with
  | zero => exact Or.inr (Or.inl Matrix.det_fin_zero)
  | succ r ih =>
    let M := (incidenceMatrix tail head).submatrix rows cols
    change M.det = 0 ∨ M.det = 1 ∨ M.det = -1
    have hentry (i j : Fin (r + 1)) :
        M i j = (if rows i = tail (cols j) then (1 : ℝ) else 0) -
          (if rows i = head (cols j) then (1 : ℝ) else 0) := rfl
    by_cases hbalanced : ∀ j, tail (cols j) ∈ Set.range rows ↔ head (cols j) ∈ Set.range rows
    · left
      by_contra hdet
      have hinj : Function.Injective (fun x : Fin (r + 1) → ℝ => x ᵥ* M) :=
        Matrix.vecMul_injective_iff_isUnit.mpr
          ((Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hdet))
      have hsum : (fun _ : Fin (r + 1) => (1 : ℝ)) ᵥ* M = (0 : Fin (r + 1) → ℝ) ᵥ* M := by
        funext j
        rw [zero_vecMul]
        change (∑ i, 1 * M i j) = 0
        simp only [one_mul, hentry, Finset.sum_sub_distrib, sum_incidence_endpoint_indicator]
        by_cases ht : tail (cols j) ∈ Set.range rows
        · rw [ite_eq_left ht, ite_eq_left ((hbalanced j).mp ht), sub_self]
        · rw [ite_eq_right ht, ite_eq_right (fun hh => ht ((hbalanced j).mpr hh)), sub_self]
      have h := congrFun (hinj hsum) (0 : Fin (r + 1))
      norm_num at h
    · push Not at hbalanced
      obtain ⟨j, hj⟩ := hbalanced
      have hsingle : ∃ i : Fin (r + 1),
          (M i j = 1 ∨ M i j = -1) ∧ ∀ k, k ≠ i → M k j = 0 := by
        rcases hj with ⟨ht, hh⟩ | ⟨ht, hh⟩
        · obtain ⟨i, hi⟩ := ht
          have h (k : Fin (r + 1)) : rows k ≠ head (cols j) := fun he => hh ⟨k, he⟩
          refine ⟨i, Or.inl (by rw [hentry, ite_eq_left hi, ite_eq_right (h i), sub_zero]), ?_⟩
          intro k hk
          have he : rows k ≠ tail (cols j) := fun hc => hk (rows.injective (hc.trans hi.symm))
          simp [hentry, he, h k]
        · obtain ⟨i, hi⟩ := hh
          have h (k : Fin (r + 1)) : rows k ≠ tail (cols j) := fun he => ht ⟨k, he⟩
          refine ⟨i, Or.inr (by rw [hentry, ite_eq_right (h i), ite_eq_left hi, zero_sub]), ?_⟩
          intro k hk
          have he : rows k ≠ head (cols j) := fun hc => hk (rows.injective (hc.trans hi.symm))
          simp [hentry, he, h k]
      obtain ⟨i, hval, hzero⟩ := hsingle
      have he : M.det = (-1) ^ (i.val + j.val) * M i j *
          (M.submatrix i.succAbove j.succAbove).det := by
        rw [Matrix.det_succ_column M j]
        exact Fintype.sum_eq_single i (fun k hk => by simp [hzero k hk])
      have hsmall := ih (⟨rows ∘ i.succAbove, rows.injective.comp Fin.succAbove_right_injective⟩)
        (cols ∘ j.succAbove)
      change (M.submatrix i.succAbove j.succAbove).det = 0 ∨
        (M.submatrix i.succAbove j.succAbove).det = 1 ∨
        (M.submatrix i.succAbove j.succAbove).det = -1 at hsmall
      rcases hsmall with hd | hd | hd <;> rcases hval with h₁ | h₁ <;>
        rcases neg_one_pow_eq_or ℝ (i.val + j.val) with hs | hs <;>
        norm_num [he, hd, h₁, hs]

end IncidenceMinorsResults

section DeterminantResults

open Matrix

variable {m : ℕ} {E : Type*} [Fintype E] [DecidableEq E]

/-- The reduced incidence matrix deletes the reference node, indexed by zero. -/
def reducedNetworkIncidence (tail head : E → Fin (m + 1)) : Matrix (Fin m) E ℝ :=
  (incidenceMatrix tail head).submatrix Fin.succ id

omit [Fintype E] [DecidableEq E] in
private theorem transpose_reducedIncidence_mulVec (tail head : E → Fin (m + 1))
    (p : Fin m → ℝ) :
    (reducedNetworkIncidence tail head)ᵀ *ᵥ p =
      (incidenceMatrix tail head)ᵀ *ᵥ Fin.cons 0 p := by
  funext e
  simp [reducedNetworkIncidence, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

omit [Fintype E] [DecidableEq E] in
/-- Fixing the reference potential to zero removes the constant kernel
of the transpose incidence matrix in a connected network. -/
theorem reducedNetworkIncidence_transpose_injective (tail head : E → Fin (m + 1))
    (hc : NetworkConnected tail head) :
    Function.Injective (reducedNetworkIncidence tail head)ᵀ.mulVecLin := by
  apply LinearMap.ker_eq_bot.mp
  rw [Matrix.ker_mulVecLin_eq_bot_iff]
  intro p hp
  rw [transpose_reducedIncidence_mulVec] at hp
  have hp' : Fin.cons (0 : ℝ) p ∈ (incidenceMatrix tail head)ᵀ.mulVecLin.ker := hp
  rw [incidenceMatrix_transpose_ker tail head hc, Submodule.mem_span_singleton] at hp'
  obtain ⟨c, hc'⟩ := hp'
  have hc₀ : c = 0 := by
    have h := congrFun hc' 0
    simpa using h
  funext i
  have h := congrFun hc' i.succ
  simpa [hc₀] using h.symm

omit [Fintype E] [DecidableEq E] in
private theorem reducedNetworkIncidence_voltageSpace (tail head : E → Fin (m + 1)) :
    LinearMap.range (reducedNetworkIncidence tail head)ᵀ.toEuclideanLin =
      networkVoltageSpace (incidenceMatrix tail head) := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    refine ⟨WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp p)), ?_⟩
    apply WithLp.ofLp_injective 2
    exact (transpose_reducedIncidence_mulVec tail head (WithLp.ofLp p)).symm
  · rintro _ ⟨p, rfl⟩
    let q (i : Fin m) := WithLp.ofLp p i.succ - WithLp.ofLp p 0
    refine ⟨WithLp.toLp 2 q, ?_⟩
    apply WithLp.ofLp_injective 2
    change (reducedNetworkIncidence tail head)ᵀ *ᵥ q =
      (incidenceMatrix tail head)ᵀ *ᵥ WithLp.ofLp p
    rw [transpose_reducedIncidence_mulVec]
    have hq (i : Fin (m + 1)) :
        Fin.cons (α := fun _ => ℝ) 0 q i = WithLp.ofLp p i - WithLp.ofLp p 0 := by
      cases i using Fin.cases with
      | zero => simp
      | succ i => rfl
    funext e
    simp only [incidenceMatrix_transpose_mulVec, hq]
    abel

omit [DecidableEq E] in
private theorem reducedNetworkIncidence_gram_det_isUnit (tail head : E → Fin (m + 1))
    (hc : NetworkConnected tail head) :
    let B := reducedNetworkIncidence tail head
    IsUnit (B * Bᵀ).det := by
  intro B
  have hrows : LinearIndependent ℝ B := by
    change LinearIndependent ℝ B.row
    apply Matrix.vecMul_injective_iff.mp
    have hB := reducedNetworkIncidence_transpose_injective tail head hc
    change Function.Injective (fun x => Bᵀ *ᵥ x) at hB
    simpa only [← vecMul_transpose Bᵀ, transpose_transpose] using hB
  exact (Matrix.isUnit_iff_isUnit_det _).mp (by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      (Matrix.posDef_self_mul_conjTranspose_of_linearIndependent hrows).isUnit)

/-- The discriminant of Exercise 113 is the weighted reduced incidence
Gram determinant divided by the corresponding unweighted determinant. -/
theorem networkDiscriminant_eq_reducedGram_ratio
    (tail head : E → Fin (m + 1)) (hc : NetworkConnected tail head) (a : E → ℝ) :
    let M := incidenceMatrix tail head
    let B := reducedNetworkIncidence tail head
    (diagonal a * networkProjection (networkVoltageSpace M) +
      networkProjection (networkCurrentSpace M)).det =
      (B * diagonal a * Bᵀ).det / (B * Bᵀ).det := by
  intro M B
  let G := B * Bᵀ
  let A := diagonal a
  let P := networkProjection (networkVoltageSpace M)
  have hrows : LinearIndependent ℝ B := by
    change LinearIndependent ℝ B.row
    apply Matrix.vecMul_injective_iff.mp
    have hB := reducedNetworkIncidence_transpose_injective tail head hc
    change Function.Injective (fun x => Bᵀ *ᵥ x) at hB
    simpa only [← vecMul_transpose Bᵀ, transpose_transpose] using hB
  have hG : IsUnit G.det := reducedNetworkIncidence_gram_det_isUnit tail head hc
  have hP : P = Bᵀ * G⁻¹ * B := by
    have hInv : B.pinv = Bᵀ * G⁻¹ := by
      simpa only [conjTranspose_eq_transpose_of_trivial] using
        Matrix.pinv_eq_conjTranspose_mul_inv_self_mul_conjTranspose hrows
    rw [← hInv]
    apply Matrix.toEuclideanLin.injective
    change toEuclideanLin (networkProjection (networkVoltageSpace M)) =
      toEuclideanLin (B.pinv * B)
    rw [networkProjection_toEuclideanLin, Matrix.pinv_mul_eq_starProjection,
      conjTranspose_eq_transpose_of_trivial]
    exact congrArg (fun L : Submodule ℝ (EuclideanSpace ℝ E) =>
      (L.starProjection : EuclideanSpace ℝ E →ₗ[ℝ] EuclideanSpace ℝ E))
      (reducedNetworkIncidence_voltageSpace tail head).symm
  have hQ : networkProjection (networkCurrentSpace M) = 1 - P := by
    rw [← networkProjection_orthogonal, networkVoltageSpace_eq_orthogonal,
      Submodule.orthogonal_orthogonal]
  change (A * P + networkProjection (networkCurrentSpace M)).det = _
  rw [hQ, show A * P + (1 - P) = 1 + (A - 1) * P by rw [Matrix.sub_mul, Matrix.one_mul]; abel]
  rw [hP, show (A - 1) * (Bᵀ * G⁻¹ * B) =
    ((A - 1) * Bᵀ) * (G⁻¹ * B) by simp only [Matrix.mul_assoc],
    Matrix.det_one_add_mul_comm]
  have hprod : 1 + G⁻¹ * B * ((A - 1) * Bᵀ) = G⁻¹ * (B * A * Bᵀ) := by
    rw [show (G⁻¹ * B) * ((A - 1) * Bᵀ) = G⁻¹ * (B * (A - 1) * Bᵀ) by
      simp only [Matrix.mul_assoc], Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul,
      Matrix.mul_sub, show B * Bᵀ = G from rfl, Matrix.nonsing_inv_mul G hG]
    abel
  rw [hprod, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, div_eq_mul_inv, mul_comm]

/-- The finite sets of $m$ branches whose independent columns span a network
with $m+1$ nodes. These are the trees in the textbook definition. -/
noncomputable def networkSpanningTrees (tail head : E → Fin (m + 1)) : Finset (Finset E) := by
  classical
  exact Finset.univ.filter fun s => s.card = m ∧
    Function.Injective ((incidenceMatrix tail head).submatrix id
      (fun e : s => (e : E))).mulVecLin

omit [DecidableEq E] in
/-- A set of branches is enumerated as a tree exactly when it has the
specified size and its incidence columns are linearly independent. -/
theorem mem_networkSpanningTrees_iff (tail head : E → Fin (m + 1)) (s : Finset E) :
    s ∈ networkSpanningTrees tail head ↔ s.card = m ∧
      Function.Injective ((incidenceMatrix tail head).submatrix id
        (fun e : s => (e : E))).mulVecLin := by
  classical
  simp [networkSpanningTrees]

omit [Fintype E] [DecidableEq E] in
private theorem reducedNetworkIncidence_selection_injective_iff {K : Type*} [Fintype K]
    (tail head : E → Fin (m + 1)) (f : K → E) :
    Function.Injective ((reducedNetworkIncidence tail head).submatrix id f).mulVecLin ↔
      Function.Injective ((incidenceMatrix tail head).submatrix id f).mulVecLin := by
  let M := (incidenceMatrix tail head).submatrix id f
  let B := (reducedNetworkIncidence tail head).submatrix id f
  have hcol (j : K) : ∑ i, M i j = 0 := by
    simp [M, incidenceMatrix, Finset.sum_sub_distrib]
  have hsum (x : K → ℝ) : ∑ i, (M *ᵥ x) i = 0 := by
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hcol, zero_mul, Finset.sum_const_zero]
  have hrest (x : K → ℝ) (i : Fin m) : (M *ᵥ x) i.succ = (B *ᵥ x) i := rfl
  constructor
  · intro h x y hxy
    exact h (funext fun i => congrFun hxy i.succ)
  · intro h x y hxy
    apply h
    funext i
    cases i using Fin.cases with
    | zero =>
      have hx := hsum x
      have hy := hsum y
      rw [Fin.sum_univ_succ] at hx hy
      have hrest_eq : (∑ j : Fin m, (M *ᵥ x) j.succ) =
          ∑ j : Fin m, (M *ᵥ y) j.succ := by
        simp only [hrest, show B *ᵥ x = B *ᵥ y from hxy]
      rw [hrest_eq] at hx
      change (M *ᵥ x) 0 = (M *ᵥ y) 0
      linarith
    | succ j =>
      change (M *ᵥ x) j.succ = (M *ᵥ y) j.succ
      rw [hrest, hrest]
      exact congrFun hxy j

omit [Fintype E] [DecidableEq E] in
private theorem independent_incidenceColumns_comp_equiv {K J : Type*}
    [Fintype K] [Fintype J] (M : Matrix (Fin (m + 1)) E ℝ) (f : J → E) (e : K ≃ J) :
    Function.Injective (M.submatrix id (f ∘ e)).mulVecLin ↔
      Function.Injective (M.submatrix id f).mulVecLin := by
  change Function.Injective (M.submatrix id (f ∘ e)).mulVec ↔
    Function.Injective (M.submatrix id f).mulVec
  rw [Matrix.mulVec_injective_iff, Matrix.mulVec_injective_iff]
  change LinearIndependent ℝ ((M.submatrix id f).col ∘ e) ↔
    LinearIndependent ℝ (M.submatrix id f).col
  exact linearIndependent_equiv e

omit [Fintype E] [DecidableEq E] in
private theorem minor_ne_zero_iff_independent_incidenceColumns
    (tail head : E → Fin (m + 1)) (f : Fin m → E) :
    ((reducedNetworkIncidence tail head).submatrix id f).det ≠ 0 ↔
      Function.Injective ((incidenceMatrix tail head).submatrix id f).mulVecLin := by
  rw [← reducedNetworkIncidence_selection_injective_iff, ← isUnit_iff_ne_zero,
    ← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  rfl

omit [Fintype E] in
private theorem treeEnumeration_image (s : Finset E) (e : Fin m ≃ ↥s) :
    Finset.univ.image (fun i => (e i : E)) = s := by
  ext j
  constructor
  · rintro hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    exact (e i).property
  · intro hj
    exact Finset.mem_image.mpr ⟨e.symm ⟨j, hj⟩, Finset.mem_univ _,
      congrArg Subtype.val (e.apply_symm_apply ⟨j, hj⟩)⟩

private noncomputable def networkTreeEnumerationEquiv (tail head : E → Fin (m + 1)) :
    (Σ s : ↥(networkSpanningTrees tail head), Fin m ≃ ↥s.val) ≃
      {f : Fin m → E // ((reducedNetworkIncidence tail head).submatrix id f).det ≠ 0} := by
  classical
  let M := incidenceMatrix tail head
  let enumerate : (Σ s : ↥(networkSpanningTrees tail head), Fin m ≃ ↥s.val) →
      {f : Fin m → E // ((reducedNetworkIncidence tail head).submatrix id f).det ≠ 0} := fun x =>
    ⟨fun i => (x.2 i : E), (minor_ne_zero_iff_independent_incidenceColumns tail head _).mpr
      ((independent_incidenceColumns_comp_equiv M Subtype.val x.2).mpr
        ((mem_networkSpanningTrees_iff tail head x.1.val).mp x.1.property).2)⟩
  refine Equiv.ofBijective enumerate ⟨?_, ?_⟩
  · rintro ⟨s, es⟩ ⟨t, et⟩ h
    have h₀ : (fun i => (es i : E)) = fun i => (et i : E) := congrArg Subtype.val h
    have hst : s = t := by
      apply Subtype.ext
      rw [← treeEnumeration_image s.val es, ← treeEnumeration_image t.val et, h₀]
    subst t
    congr 1
    exact Equiv.ext fun i => Subtype.ext (congrFun h₀ i)
  · rintro ⟨f, hf⟩
    have hfinj : Function.Injective f := by
      intro i j hij
      by_contra! hne
      exact hf (Matrix.det_zero_of_column_eq hne fun k => by simp [hij])
    let s := Finset.univ.image f
    let eqv : Fin m ≃ ↥s :=
      (Equiv.ofInjective f hfinj).trans (Equiv.subtypeEquivRight
        (fun j => by simp [s, Finset.mem_image, Set.mem_range]))
    have heq : (fun i => (eqv i : E)) = f := rfl
    have hs : s ∈ networkSpanningTrees tail head := by
      rw [mem_networkSpanningTrees_iff]
      constructor
      · simpa only [Fintype.card_coe, Fintype.card_fin] using (Fintype.card_congr eqv).symm
      · apply (independent_incidenceColumns_comp_equiv M Subtype.val eqv).mp
        change Function.Injective (M.submatrix id (fun i => (eqv i : E))).mulVecLin
        rw [heq]
        exact (minor_ne_zero_iff_independent_incidenceColumns tail head f).mp hf
    refine ⟨⟨⟨s, hs⟩, eqv⟩, Subtype.ext heq⟩

private theorem weighted_reducedNetworkIncidence_det (tail head : E → Fin (m + 1)) (a : E → ℝ) :
    let B := reducedNetworkIncidence tail head
    (B * diagonal a * Bᵀ).det =
      ∑ s ∈ networkSpanningTrees tail head, ∏ e ∈ s, a e := by
  classical
  intro B
  have hsum := Matrix.factorial_mul_det_transpose_mul_diagonal_mul Bᵀ Bᵀ a
  rw [Matrix.transpose_transpose, Fintype.card_fin] at hsum
  have hminor (f : Fin m → E) : (Bᵀ.submatrix f id).det = (B.submatrix id f).det := by
    rw [← Matrix.det_transpose, Matrix.transpose_submatrix, Matrix.transpose_transpose]
  simp only [hminor] at hsum
  have hs : (m.factorial : ℝ) * (B * diagonal a * Bᵀ).det =
      ∑ f : {f : Fin m → E // (B.submatrix id f).det ≠ 0}, ∏ i, a (f.val i) := by
    rw [hsum, ← Finset.sum_subtype
      (Finset.univ.filter fun f : Fin m → E => (B.submatrix id f).det ≠ 0)
      (by simp) (fun f => ∏ i, a (f i)), Finset.sum_filter]
    refine Finset.sum_congr rfl fun f _ => ?_
    have hsign := incidenceMinor_det_sign tail head (⟨Fin.succ, Fin.succ_injective _⟩ :
      Fin m ↪ Fin (m + 1)) f
    change (B.submatrix id f).det = 0 ∨ (B.submatrix id f).det = 1 ∨
      (B.submatrix id f).det = -1 at hsign
    by_cases hz : (B.submatrix id f).det = 0
    · simp [hz]
    · rcases hsign with h | h | h <;> simp_all
  have hfac (s : ↥(networkSpanningTrees tail head)) :
      Fintype.card (Fin m ≃ ↥s.val) = m.factorial := by
    have hcard := ((mem_networkSpanningTrees_iff tail head s.val).mp s.property).1
    let e : Fin m ≃ ↥s.val := Fintype.equivOfCardEq (by simpa using hcard.symm)
    simpa only [Fintype.card_fin] using Fintype.card_equiv e
  have hprod (s : ↥(networkSpanningTrees tail head)) (e : Fin m ≃ ↥s.val) :
      (∏ i, a (e i)) = ∏ i ∈ s.val, a i := by
    rw [← s.val.prod_coe_sort]
    exact Fintype.prod_equiv e _ _ (fun _ => rfl)
  have hs' : (m.factorial : ℝ) * (B * diagonal a * Bᵀ).det =
      (m.factorial : ℝ) * ∑ s ∈ networkSpanningTrees tail head, ∏ e ∈ s, a e := by
    rw [hs, ← (networkTreeEnumerationEquiv tail head).sum_comp, Finset.mul_sum]
    rw [Fintype.sum_sigma, ← (networkSpanningTrees tail head).sum_coe_sort]
    refine Finset.sum_congr rfl fun s _ => ?_
    change (∑ e : Fin m ≃ ↥s.val, ∏ i, a (e i)) = _
    simp only [hprod, Finset.sum_const, Finset.card_univ, hfac, nsmul_eq_mul]
  exact mul_left_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero m) hs'

omit [DecidableEq E] in
/-- A connected network has at least one spanning tree, so the normalization
in Exercise 113 has a nonzero denominator. -/
theorem networkSpanningTrees_nonempty (tail head : E → Fin (m + 1))
    (hc : NetworkConnected tail head) : (networkSpanningTrees tail head).Nonempty := by
  classical
  rw [Finset.nonempty_iff_ne_empty]
  intro he
  have h := weighted_reducedNetworkIncidence_det tail head (fun _ => (1 : ℝ))
  simp only [Matrix.diagonal_one, Matrix.mul_one, he, Finset.sum_empty] at h
  exact isUnit_iff_ne_zero.mp (reducedNetworkIncidence_gram_det_isUnit tail head hc) h

/-- **Exercise 113** of [benIsrael2003generalized], Chapter 2. The
discriminant is the sum of the spanning-tree weight products divided
by the number of spanning trees. Each tree is counted once as an
unordered set of branches.

The printed formula omits the denominator. At unit weights, both
reduced Gram determinants coincide and the discriminant is one.
The unnormalized tree sum counts the trees. -/
theorem exercise_113 (tail head : E → Fin (m + 1)) (hc : NetworkConnected tail head) (a : E → ℝ) :
    let M := incidenceMatrix tail head
    (diagonal a * networkProjection (networkVoltageSpace M) +
      networkProjection (networkCurrentSpace M)).det =
      (∑ s ∈ networkSpanningTrees tail head, ∏ e ∈ s, a e) /
        (networkSpanningTrees tail head).card := by
  intro M
  rw [networkDiscriminant_eq_reducedGram_ratio tail head hc a,
    weighted_reducedNetworkIncidence_det]
  have h := weighted_reducedNetworkIncidence_det tail head (fun _ => (1 : ℝ))
  simp only [Matrix.diagonal_one, Matrix.mul_one, Finset.prod_const_one, Finset.sum_const,
    nsmul_eq_mul, mul_one] at h
  rw [h]

end DeterminantResults

end BenIsraelGreville.Chapter02

namespace BenIsraelGreville.Chapter02

open Matrix Finset

variable {U : Type*} [DecidableEq U] [Fintype U]

/-- The finite subsets of a given cardinality, indexing the rows or columns
of the set incidence matrices in Exercise 111. -/
abbrev FixedCardSubset (U : Type*) (k : ℕ) := {s : Finset U // s.card = k}

/-- The set inclusion incidence matrix of **Exercise 111** of
[benIsrael2003generalized]. Entry `(R,C)` is one when $R$ is contained in $C$. -/
def setInclusionMatrix (U : Type*) [DecidableEq U] (r c : ℕ) :
    Matrix (FixedCardSubset U r) (FixedCardSubset U c) ℝ :=
  Matrix.of fun R C => if R.val ⊆ C.val then 1 else 0

/-- The set intersection matrix of **Exercise 111** of [benIsrael2003generalized].
Entry `(R,C)` is one when $R$ and $C$ are disjoint. -/
def setIntersectionMatrix (U : Type*) [DecidableEq U] (r c : ℕ) :
    Matrix (FixedCardSubset U r) (FixedCardSubset U c) ℝ :=
  Matrix.of fun R C => if Disjoint R.val C.val then 1 else 0

omit [Fintype U] in
/-- The zero-cardinality row of both incidence matrices consists of ones. -/
theorem setIncidenceMatrix_zero_row (c : ℕ) (R : FixedCardSubset U 0) (C : FixedCardSubset U c) :
    setInclusionMatrix U 0 c R C = 1 ∧ setIntersectionMatrix U 0 c R C = 1 := by
  have hR := Finset.card_eq_zero.mp R.property
  simp [setInclusionMatrix, setIntersectionMatrix, hR]

omit [DecidableEq U] in
private theorem sum_fixedCardSubset {c : ℕ} (f : Finset U → ℝ) :
    (∑ C : FixedCardSubset U c, f C.val) = ∑ C ∈ (univ : Finset U).powersetCard c, f C := by
  symm
  apply Finset.sum_subtype
  simp [Finset.mem_powersetCard]

omit [Fintype U] in
private theorem filter_powersetCard_containing (domain S I : Finset U) {c : ℕ}
    (hS : S ⊆ domain) (hc : S.card ≤ c) (hSI : Disjoint S I) :
    (((domain.powersetCard c).filter fun C => S ⊆ C ∧ Disjoint I C).card) =
      (domain \ (S ∪ I)).card.choose (c - S.card) := by
  let available := domain \ (S ∪ I)
  let extra := available.powersetCard (c - S.card)
  let admissible := (domain.powersetCard c).filter fun C => S ⊆ C ∧ Disjoint I C
  have heq : extra.image (S ∪ ·) = admissible := by
    ext C
    constructor
    · intro h
      obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨hDa, hDc⟩ := Finset.mem_powersetCard.mp hD
      have hDS : Disjoint S D := by
        exact Finset.disjoint_left.mpr fun x hxS hxD =>
          (Finset.mem_sdiff.mp (hDa hxD)).2 (Finset.mem_union_left _ hxS)
      have hDI : Disjoint I D := by
        exact Finset.disjoint_left.mpr fun x hxI hxD =>
          (Finset.mem_sdiff.mp (hDa hxD)).2 (Finset.mem_union_right _ hxI)
      refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_, ?_⟩
      · exact union_subset hS fun x hx => (Finset.mem_sdiff.mp (hDa hx)).1
      · rw [Finset.card_union_of_disjoint hDS, hDc, Nat.add_sub_of_le hc]
      · exact Finset.subset_union_left
      · exact Finset.disjoint_union_right.mpr ⟨hSI.symm, hDI⟩
    · intro h
      obtain ⟨hC, hSC, hIC⟩ := Finset.mem_filter.mp h
      obtain ⟨hCd, hCc⟩ := Finset.mem_powersetCard.mp hC
      refine Finset.mem_image.mpr ⟨C \ S, Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
      · intro x hx
        obtain ⟨hxC, hxS⟩ := Finset.mem_sdiff.mp hx
        exact Finset.mem_sdiff.mpr ⟨hCd hxC, fun hx => (Finset.mem_union.mp hx).elim hxS
          (fun hxI => Finset.disjoint_left.mp hIC hxI hxC)⟩
      · rw [Finset.card_sdiff_of_subset hSC, hCc]
      · rw [Finset.union_sdiff_of_subset hSC]
  change admissible.card = available.card.choose (c - S.card)
  rw [← heq, Finset.card_image_of_injOn]
  · exact Finset.card_powersetCard _ _
  intro D hD D' hD' h
  have hdisj {D : Finset U} (hD : D ∈ extra) : Disjoint D S := by
    refine Finset.disjoint_left.mpr fun x hxD hxS => ?_
    have hx := (Finset.mem_powersetCard.mp hD).1 hxD
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_left _ hxS)
  have hd := congrArg (· \ S) h
  simpa only [Finset.union_sdiff_distrib, Finset.sdiff_self, Finset.empty_union,
    Finset.sdiff_eq_self_iff_disjoint.mpr (hdisj hD),
    Finset.sdiff_eq_self_iff_disjoint.mpr (hdisj hD')] using hd

omit [Fintype U] in
private theorem powerset_sdiff_eq_filter (s t : Finset U) :
    (s \ t).powerset = s.powerset.filter (fun I => Disjoint I t) := by
  ext I
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_sdiff]

private noncomputable def bapatWeight (n r c i : ℕ) : ℝ :=
  (-1 : ℝ) ^ i / ((n - i - r).choose (c - r) : ℝ)

private noncomputable def bapatCandidate (r c : ℕ) :
    Matrix (FixedCardSubset U c) (FixedCardSubset U r) ℝ :=
  Matrix.of fun C R =>
    ∑ I ∈ (R.val \ C.val).powerset, bapatWeight (Fintype.card U) r c I.card

private theorem bapatCandidate_formula (r c : ℕ) :
    bapatCandidate (U := U) r c =
      ∑ i ∈ Finset.range (r + 1), bapatWeight (Fintype.card U) r c i •
        ((setIntersectionMatrix U i c)ᵀ * setInclusionMatrix U i r) := by
  ext C R
  rw [Matrix.sum_apply]
  change (∑ I ∈ (R.val \ C.val).powerset, bapatWeight (Fintype.card U) r c I.card) = _
  have hb : (R.val \ C.val).card ≤ r :=
    (Finset.card_le_card Finset.sdiff_subset).trans_eq R.property
  have hsum :
      (∑ i ∈ Finset.range ((R.val \ C.val).card + 1),
        ∑ I ∈ (R.val \ C.val).powersetCard i, bapatWeight (Fintype.card U) r c I.card) =
      ∑ i ∈ Finset.range (r + 1),
        ∑ I ∈ (R.val \ C.val).powersetCard i, bapatWeight (Fintype.card U) r c I.card := by
    apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hb))
    intro i _ hi
    have hi' : (R.val \ C.val).card < i := by
      rw [Finset.mem_range] at hi
      omega
    simp [Finset.powersetCard_eq_empty.mpr hi']
  rw [Finset.sum_powerset, hsum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply,
    setIntersectionMatrix, setInclusionMatrix, Matrix.of_apply]
  rw [sum_fixedCardSubset (fun I => (if Disjoint I C.val then (1 : ℝ) else 0) *
    (if I ⊆ R.val then 1 else 0))]
  rw [Finset.mul_sum]
  have hfilter :
      (R.val \ C.val).powersetCard i =
        ((Finset.univ : Finset U).powersetCard i).filter
          (fun I => Disjoint I C.val ∧ I ⊆ R.val) := by
    ext I
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and, Finset.mem_filter,
      Finset.subset_sdiff]
    tauto
  calc
    _ = ∑ I ∈ (R.val \ C.val).powersetCard i, bapatWeight (Fintype.card U) r c i := by
      refine Finset.sum_congr rfl fun I hI => ?_
      rw [(Finset.mem_powersetCard.mp hI).2]
    _ = _ := by
      rw [hfilter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun I _ => ?_
      by_cases hD : Disjoint I C.val <;> by_cases hR : I ⊆ R.val <;> simp [hD, hR]

private theorem bapatCandidate_rightInverse {r c : ℕ} (hrc : r ≤ c)
    (hcn : c ≤ Fintype.card U - r) :
    setInclusionMatrix U r c * bapatCandidate (U := U) r c = 1 := by
  classical
  ext S R
  let w := bapatWeight (Fintype.card U) r c
  simp only [Matrix.mul_apply, setInclusionMatrix, Matrix.of_apply, bapatCandidate]
  change (∑ C : FixedCardSubset U c, (if S.val ⊆ C.val then (1 : ℝ) else 0) *
    ∑ I ∈ (R.val \ C.val).powerset, w I.card) = _
  rw [sum_fixedCardSubset (fun C =>
    (if S.val ⊆ C then (1 : ℝ) else 0) * ∑ I ∈ (R.val \ C).powerset, w I.card)]
  have hswap :
      (∑ C ∈ (Finset.univ : Finset U).powersetCard c, (if S.val ⊆ C then (1 : ℝ) else 0) *
        ∑ I ∈ (R.val \ C).powerset, w I.card) =
      ∑ I ∈ R.val.powerset,
        ((((Finset.univ : Finset U).powersetCard c).filter
          (fun C => S.val ⊆ C ∧ Disjoint I C)).card : ℝ) * w I.card := by
    calc
      _ = ∑ C ∈ (Finset.univ : Finset U).powersetCard c, ∑ I ∈ R.val.powerset,
          if S.val ⊆ C ∧ Disjoint I C then w I.card else 0 := by
        refine Finset.sum_congr rfl fun C _ => ?_
        rw [powerset_sdiff_eq_filter, Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun I _ => ?_
        by_cases hS : S.val ⊆ C <;> simp [hS]
      _ = _ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun I _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [hswap]
  have hreduce :
      (∑ I ∈ R.val.powerset, ((((Finset.univ : Finset U).powersetCard c).filter
        (fun C => S.val ⊆ C ∧ Disjoint I C)).card : ℝ) * w I.card) =
        ∑ I ∈ (R.val \ S.val).powerset, (-1 : ℝ) ^ I.card := by
    rw [powerset_sdiff_eq_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun I hI => ?_
    by_cases hIS : Disjoint I S.val
    · rw [ite_eq_left hIS, filter_powersetCard_containing _ _ _
        (Finset.subset_univ _) (S.property.symm ▸ hrc) hIS.symm]
      have hcard : ((Finset.univ : Finset U) \ (S.val ∪ I)).card =
          Fintype.card U - I.card - r := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
          Finset.card_univ, Finset.card_union_of_disjoint hIS.symm, S.property]
        omega
      rw [hcard, S.property]
      have hIr : I.card ≤ r :=
        (Finset.card_le_card (Finset.mem_powerset.mp hI)).trans_eq R.property
      have hne : (↑((Fintype.card U - I.card - r).choose (c - r)) : ℝ) ≠ 0 := by
        exact_mod_cast Nat.choose_ne_zero (by omega : c - r ≤ Fintype.card U - I.card - r)
      change (_ : ℝ) * ((-1 : ℝ) ^ I.card /
        ↑((Fintype.card U - I.card - r).choose (c - r))) = _
      field_simp
    · rw [ite_eq_right hIS]
      have hz : ((Finset.univ : Finset U).powersetCard c).filter
          (fun C => S.val ⊆ C ∧ Disjoint I C) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        exact fun C _ ⟨hS, hD⟩ => hIS (Finset.disjoint_of_subset_right hS hD)
      simp [hz]
  rw [hreduce, Matrix.one_apply]
  have hAlt : (∑ I ∈ (R.val \ S.val).powerset, (-1 : ℝ) ^ I.card) =
      if R.val \ S.val = ∅ then 1 else 0 := by
    exact_mod_cast (Finset.sum_powerset_neg_one_pow_card (x := R.val \ S.val))
  rw [hAlt]
  have heq : R.val \ S.val = ∅ ↔ S = R := by
    rw [Finset.sdiff_eq_empty_iff_subset]
    constructor
    · intro h
      exact Subtype.ext (Finset.eq_of_subset_of_card_le h
        (S.property.trans R.property.symm).le).symm
    · rintro rfl
      exact Finset.Subset.rfl
  by_cases h : S = R
  · simp [h]
  · simp [h, heq]

private theorem bapatCandidate_mulInclusion_apply {r c : ℕ}
    (C D : FixedCardSubset U c) :
    (bapatCandidate (U := U) r c * setInclusionMatrix U r c) C D =
      ∑ I ∈ (D.val \ C.val).powerset,
        (if I.card ≤ r then ((c - I.card).choose (r - I.card) : ℝ) else 0) *
          bapatWeight (Fintype.card U) r c I.card := by
  classical
  let w := bapatWeight (Fintype.card U) r c
  simp only [Matrix.mul_apply, bapatCandidate, setInclusionMatrix, Matrix.of_apply]
  change (∑ R : FixedCardSubset U r, (∑ I ∈ (R.val \ C.val).powerset, w I.card) *
    (if R.val ⊆ D.val then (1 : ℝ) else 0)) = _
  rw [sum_fixedCardSubset (fun R => (∑ I ∈ (R \ C.val).powerset, w I.card) *
    (if R ⊆ D.val then (1 : ℝ) else 0))]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have hf : ((Finset.univ : Finset U).powersetCard r).filter (· ⊆ D.val) =
      D.val.powersetCard r := by
    ext R
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and, and_comm]
  rw [hf]
  calc
    _ = ∑ R ∈ D.val.powersetCard r, ∑ I ∈ (D.val \ C.val).powerset,
        if I ⊆ R then w I.card else 0 := by
      refine Finset.sum_congr rfl fun R hR => ?_
      have hRD : R ⊆ D.val := (Finset.mem_powersetCard.mp hR).1
      have hS : (R \ C.val).powerset = ((D.val \ C.val).powerset).filter (· ⊆ R) := by
        ext I
        simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_sdiff]
        exact ⟨fun h => ⟨⟨h.1.trans hRD, h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩
      rw [hS, Finset.sum_filter]
    _ = _ := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun I hI => ?_
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      by_cases hIr : I.card ≤ r
      · rw [ite_eq_left hIr]
        have hID : I ⊆ D.val := (Finset.mem_powerset.mp hI).trans Finset.sdiff_subset
        have h := filter_powersetCard_containing D.val I ∅ hID hIr (by simp)
        simpa only [Finset.disjoint_empty_left, and_true, Finset.union_empty,
          Finset.card_sdiff_of_subset hID, D.property] using
            congrArg (fun k : ℕ => (k : ℝ) * w I.card) h
      · rw [ite_eq_right hIr]
        have hz' : (D.val.powersetCard r).filter (I ⊆ ·) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro R hR h
          exact hIr ((Finset.card_le_card h).trans_eq (Finset.mem_powersetCard.mp hR).2)
        simp [hz']

private theorem bapatCandidate_mulInclusion_isHermitian (r c : ℕ) :
    (bapatCandidate (U := U) r c * setInclusionMatrix U r c).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  ext C D
  rw [Matrix.transpose_apply, bapatCandidate_mulInclusion_apply, bapatCandidate_mulInclusion_apply]
  let f (j : ℕ) : ℝ := (if j ≤ r then ((c - j).choose (r - j) : ℝ) else 0) *
    bapatWeight (Fintype.card U) r c j
  change (∑ I ∈ (C.val \ D.val).powerset, f I.card) =
    ∑ I ∈ (D.val \ C.val).powerset, f I.card
  rw [Finset.sum_powerset_apply_card f, Finset.sum_powerset_apply_card f,
    Finset.card_sdiff_comm (C.property.trans D.property.symm)]

/-- **Exercise 111** of [benIsrael2003generalized], Chapter 2. For
$r le c le n-r$, the Moore–Penrose inverse of the inclusion matrix is
Bapat's alternating sum of transposed disjointness matrices multiplied by
inclusion matrices. The reciprocal binomial factors are well-defined in
this range. -/
theorem exercise_111 {r c : ℕ} (hrc : r ≤ c) (hcn : c ≤ Fintype.card U - r) :
    (setInclusionMatrix U r c).pinv =
      ∑ i ∈ Finset.range (r + 1),
        ((-1 : ℝ) ^ i / ((Fintype.card U - i - r).choose (c - r) : ℝ)) •
          ((setIntersectionMatrix U i c)ᵀ * setInclusionMatrix U i r) := by
  have h := bapatCandidate_rightInverse (U := U) hrc hcn
  refine (Matrix.pinv_unique (setInclusionMatrix U r c) ?_ ?_ ?_
    (bapatCandidate_mulInclusion_isHermitian r c)).symm.trans
      (bapatCandidate_formula r c)
  · rw [h, Matrix.one_mul]
  · rw [Matrix.mul_assoc, h, Matrix.mul_one]
  · rw [h]
    exact Matrix.isHermitian_one

end BenIsraelGreville.Chapter02

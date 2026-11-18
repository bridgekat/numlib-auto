/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.BottDuffin
import Numlib.LinearAlgebra.Matrix.SVD
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

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

end BenIsraelGreville.Chapter02

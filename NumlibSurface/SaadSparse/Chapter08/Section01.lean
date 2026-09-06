import Mathlib.Analysis.CStarAlgebra.Matrix
import Numlib.LinearSolve.Projection.Basic
import NumlibSurface.SaadSparse.Chapter01.Section13
import NumlibSurface.SaadSparse.Common

/-!
# Saad §8.1: the normal equations

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §8.1 , with P-8.1.

A rectangular `A : Matrix (Fin n) (Fin m) 𝕜` has two systems of normal equations. The system of
the *first* kind, `Aᴴ A x = Aᴴ b` (8.1), characterizes the least-squares solutions of (8.2),
`min ‖b - A x‖₂`: that is `equation_8_1`, and both of its directions are the statement that a
best approximation from `Ran A` is the point whose error is orthogonal to `Ran A`. The system of
the *second* kind, `A Aᴴ u = b` (8.3) with `x = Aᴴ u` (8.4), solves `A x = b` with the least
`‖·‖₂`: that is `equation_8_3`, whose last clause states the minimality as `IsMinError` over
`Ran Aᴴ`, the form §8.3 needs for CGNE. The augmented system (8.5) is `equation_8_5`, and
`equation_8_8` is `κ₂(Aᴴ A) = κ₂(A)²`, the chapter's reason for preferring methods that never
form the normal equations.

The eigenvalue claim of §8.1 — that the spectrum of `[[0, A], [Aᴴ, 0]]` is `±σ_i(A)` — and P-8.4
need a singular value decomposition, which Mathlib does not have; see `plans/saadsparse-ch7-9.md`
§4.

Vectors are `EuclideanSpace 𝕜 (Fin n)` and `A ⬝ x` is `Matrix.toEuclideanLin A x`, as everywhere
in this library; (8.5) alone is stated on the plain function types with `*ᵥ`, since its
coefficient matrix is indexed by `Fin n ⊕ Fin m`.
-/

open Matrix

open scoped SaadSparse ENNReal

namespace SaadSparse.Chapter08

variable {n m : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-! ### Moving `A` across the inner product -/

/-- `(Aᴴ u, v) = (u, A v)`: the conjugate transpose acts as the adjoint. -/
theorem inner_conjTranspose (A : Matrix (Fin n) (Fin m) 𝕜) (u : EuclideanSpace 𝕜 (Fin n))
    (v : EuclideanSpace 𝕜 (Fin m)) : inner 𝕜 (Aᴴ ⬝ u) v = inner 𝕜 u (A ⬝ v) := by
  rw [toEuclideanLin_conjTranspose_eq_adjoint]
  exact LinearMap.adjoint_inner_left _ _ _

/-- `(v, Aᴴ u) = (A v, u)`, the companion of `SaadSparse.Chapter08.inner_conjTranspose`. -/
theorem inner_conjTranspose' (A : Matrix (Fin n) (Fin m) 𝕜) (u : EuclideanSpace 𝕜 (Fin n))
    (v : EuclideanSpace 𝕜 (Fin m)) : inner 𝕜 v (Aᴴ ⬝ u) = inner 𝕜 (A ⬝ v) u := by
  rw [← inner_conj_symm, inner_conjTranspose, inner_conj_symm]

/-- A product of rectangular matrices acts as the composite of the two actions. -/
theorem toEuclideanLin_mul_apply {k : ℕ} (B : Matrix (Fin n) (Fin m) 𝕜)
    (C : Matrix (Fin m) (Fin k) 𝕜) (x : EuclideanSpace 𝕜 (Fin k)) :
    ((B * C) ⬝ x) = (B ⬝ (C ⬝ x)) := by
  rw [show (B * C).toEuclideanLin = B.toEuclideanLin ∘ₗ C.toEuclideanLin from
    Matrix.toLpLin_mul 2 2 2 B C]
  rfl

/-- The action of a rectangular matrix on a Euclidean vector is `Matrix.mulVec` under
`WithLp.ofLp`; the rectangular companion of `SaadSparse.ofLp_toEuclideanLin`. -/
private theorem ofLp_apply (B : Matrix (Fin n) (Fin m) 𝕜) (x : EuclideanSpace 𝕜 (Fin m)) :
    WithLp.ofLp (B ⬝ x) = B *ᵥ WithLp.ofLp x := rfl

/-- The range of `A`: the space over which `min ‖b - A x‖₂` searches. -/
private def ran (A : Matrix (Fin n) (Fin m) 𝕜) : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n)) :=
  LinearMap.range (toEuclideanLin A)

private theorem mem_ran (A : Matrix (Fin n) (Fin m) 𝕜) (z : EuclideanSpace 𝕜 (Fin m)) :
    (A ⬝ z) ∈ ran A := ⟨z, rfl⟩

/-! ### (8.1)–(8.2): the normal equations of the least-squares problem -/

/-- `Aᴴ w = 0` says exactly that `w` is orthogonal to the range of `A`. -/
private theorem conjTranspose_apply_eq_zero_iff (A : Matrix (Fin n) (Fin m) 𝕜)
    (w : EuclideanSpace 𝕜 (Fin n)) : (Aᴴ ⬝ w) = 0 ↔ ∀ z, inner 𝕜 w (A ⬝ z) = (0 : 𝕜) := by
  constructor
  · intro h z
    rw [← inner_conjTranspose, h, inner_zero_left]
  · intro h
    rw [← inner_self_eq_zero (𝕜 := 𝕜), ← inner_conj_symm, inner_conjTranspose, h, map_zero]

/-- **Saad (8.1)–(8.2)**: `x` solves the normal equations `Aᴴ A x = Aᴴ b` if and only if it
minimizes `‖b - A x‖₂`. Both directions are the characterization of a best approximation from
`Ran A` by orthogonality of its error, so no rank assumption on `A` is needed; when the columns
of `A` are independent, `Aᴴ A` is in addition symmetric positive definite
(`SaadSparse.Chapter08.isSymmetricCoercive_conjTranspose_mul_self`) and the minimizer is unique. -/
theorem equation_8_1 (A : Matrix (Fin n) (Fin m) 𝕜) (b : EuclideanSpace 𝕜 (Fin n))
    (x : EuclideanSpace 𝕜 (Fin m)) :
    ((Aᴴ * A) ⬝ x) = (Aᴴ ⬝ b) ↔ ∀ y, ‖b - (A ⬝ x)‖ ≤ ‖b - (A ⬝ y)‖ := by
  have hres : ((Aᴴ * A) ⬝ x) = (Aᴴ ⬝ b) ↔ (Aᴴ ⬝ (b - (A ⬝ x))) = 0 := by
    rw [toEuclideanLin_mul_apply, map_sub, sub_eq_zero]
    exact eq_comm
  rw [hres, conjTranspose_apply_eq_zero_iff]
  constructor
  · intro h y
    refine Submodule.norm_sub_le_of_forall_inner_eq_zero (K := ran A) (mem_ran A x) ?_
      (mem_ran A y)
    rintro _ ⟨z, rfl⟩
    exact h z
  · intro h z
    exact Submodule.inner_eq_zero_of_forall_norm_sub_le (K := ran A) (mem_ran A x)
      (by rintro _ ⟨y, rfl⟩; exact h y) (mem_ran A z)

/-- **Saad (8.1)**: `Aᴴ A` is symmetric positive definite as soon as the columns of `A` are
independent, so the normal equations then have a unique solution. This is the hypothesis under
which CGNR (§8.3) is well defined. -/
theorem isSymmetricCoercive_conjTranspose_mul_self (A : Matrix (Fin n) (Fin m) 𝕜)
    (hA : Function.Injective (toEuclideanLin A)) :
    (toEuclideanLin (Aᴴ * A)).IsSymmetricCoercive where
  isSymmetric x y := by
    rw [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply, inner_conjTranspose,
      inner_conjTranspose']
  isCoercive := (LinearMap.isCoercive_iff_forall_pos _).2 fun x hx => by
    rw [show (toEuclideanLin (Aᴴ * A)) x = (Aᴴ ⬝ (A ⬝ x)) from toEuclideanLin_mul_apply Aᴴ A x,
      inner_conjTranspose, inner_self_eq_norm_sq_to_K]
    have hAx : (A ⬝ x) ≠ 0 := fun h => hx (hA (by rw [h, map_zero]))
    simpa using by positivity

/-! ### (8.3)–(8.4): the normal equations of the second kind -/

/-- **Saad (8.3)–(8.4)**: if `A Aᴴ u = b` then `x = Aᴴ u` solves `A x = b`, and it is the
solution of least Euclidean norm. Equivalently — the form §8.3 uses for CGNE — `x` is the best
approximation to *any* solution `x_*` from `Ran Aᴴ`, so which solution is taken does not change
the minimizer. -/
theorem equation_8_3 (A : Matrix (Fin n) (Fin m) 𝕜) {b u : EuclideanSpace 𝕜 (Fin n)}
    (hu : ((A * Aᴴ) ⬝ u) = b) :
    (A ⬝ (Aᴴ ⬝ u)) = b ∧ (∀ y, (A ⬝ y) = b → ‖(Aᴴ ⬝ u)‖ ≤ ‖y‖) ∧
      ∀ xstar, (A ⬝ xstar) = b →
        IsMinError xstar 0 (LinearMap.range (toEuclideanLin Aᴴ)) (Aᴴ ⬝ u) := by
  have hsol : (A ⬝ (Aᴴ ⬝ u)) = b := by rw [← toEuclideanLin_mul_apply, hu]
  have horth : ∀ xstar : EuclideanSpace 𝕜 (Fin m), (A ⬝ xstar) = b →
      ∀ w ∈ LinearMap.range (toEuclideanLin Aᴴ),
        inner 𝕜 (xstar - (Aᴴ ⬝ u)) w = (0 : 𝕜) := by
    rintro xstar hx _ ⟨z, rfl⟩
    rw [show (toEuclideanLin Aᴴ) z = (Aᴴ ⬝ z) from rfl, inner_conjTranspose', map_sub, hx, hsol,
      sub_self, inner_zero_left]
  refine ⟨hsol, fun y hy => ?_, fun xstar hx => ⟨by rw [sub_zero]; exact ⟨u, rfl⟩, fun w hw => ?_⟩⟩
  · have h0 : inner 𝕜 (Aᴴ ⬝ u) (y - (Aᴴ ⬝ u)) = (0 : 𝕜) := by
      rw [inner_conjTranspose, map_sub, hy, hsol, sub_self, inner_zero_right]
    have hsum : ‖(Aᴴ ⬝ u) + (y - (Aᴴ ⬝ u))‖ * ‖(Aᴴ ⬝ u) + (y - (Aᴴ ⬝ u))‖
        = ‖(Aᴴ ⬝ u)‖ * ‖(Aᴴ ⬝ u)‖ + ‖y - (Aᴴ ⬝ u)‖ * ‖y - (Aᴴ ⬝ u)‖ :=
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0
    rw [show (Aᴴ ⬝ u) + (y - (Aᴴ ⬝ u)) = y from by abel] at hsum
    nlinarith [norm_nonneg y, norm_nonneg (Aᴴ ⬝ u), norm_nonneg (y - (Aᴴ ⬝ u))]
  · rw [sub_zero] at hw
    exact Submodule.norm_sub_le_of_forall_inner_eq_zero
      (K := LinearMap.range (toEuclideanLin Aᴴ)) ⟨u, rfl⟩ (horth xstar hx) hw

/-! ### (8.5)–(8.7): the augmented system -/

private theorem sum_elim_eq_iff {α β γ : Type*} {f f' : α → γ} {g g' : β → γ} :
    Sum.elim f g = Sum.elim f' g' ↔ f = f' ∧ g = g' :=
  ⟨fun h => ⟨funext fun i => congrFun h (Sum.inl i), funext fun i => congrFun h (Sum.inr i)⟩,
    fun h => by rw [h.1, h.2]⟩

/-- **Saad (8.5)–(8.7)** and **P-8.1**: the pair `(r, x)` solves the augmented system
`[[1, A], [Aᴴ, 0]] (r, x) = (b, 0)` exactly when `r` is the residual `b - A x` and `x` solves the
least-squares problem (8.2). The second block equation `Aᴴ r = 0` is the constraint of
"minimize `½‖r - b‖₂²` subject to `Aᴴ r = 0`", and `x` is its vector of Lagrange multipliers. -/
theorem equation_8_5 (A : Matrix (Fin n) (Fin m) 𝕜) (b r : EuclideanSpace 𝕜 (Fin n))
    (x : EuclideanSpace 𝕜 (Fin m)) :
    Matrix.fromBlocks 1 A Aᴴ 0 *ᵥ Sum.elim (WithLp.ofLp r) (WithLp.ofLp x)
        = Sum.elim (WithLp.ofLp b) 0 ↔
      r = b - (A ⬝ x) ∧ ∀ y, ‖b - (A ⬝ x)‖ ≤ ‖b - (A ⬝ y)‖ := by
  have hblk : Matrix.fromBlocks 1 A Aᴴ 0 *ᵥ Sum.elim (WithLp.ofLp r) (WithLp.ofLp x)
      = Sum.elim (WithLp.ofLp r + A *ᵥ WithLp.ofLp x) (Aᴴ *ᵥ WithLp.ofLp r) := by
    rw [Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.one_mulVec,
      Matrix.zero_mulVec, add_zero]
  have h1 : WithLp.ofLp r + A *ᵥ WithLp.ofLp x = WithLp.ofLp b ↔ r = b - (A ⬝ x) := by
    constructor
    · intro h
      refine WithLp.ofLp_injective 2 ?_
      rw [WithLp.ofLp_sub, ofLp_apply]
      exact eq_sub_of_add_eq h
    · intro h
      rw [h, WithLp.ofLp_sub, ofLp_apply, sub_add_cancel]
  rw [hblk, sum_elim_eq_iff, h1]
  refine and_congr_right fun hr => ?_
  have h2 : Aᴴ *ᵥ WithLp.ofLp r = WithLp.ofLp (Aᴴ ⬝ (b - (A ⬝ x))) := by rw [hr]; rfl
  rw [h2, ← WithLp.ofLp_zero (p := 2), (WithLp.ofLp_injective 2).eq_iff,
    ← equation_8_1, toEuclideanLin_mul_apply, map_sub, sub_eq_zero]
  exact eq_comm

/-! ### (8.8): the squared condition number -/

open scoped Matrix.Norms.L2Operator in
/-- `‖B Bᴴ‖₂ = ‖B‖₂²`, the companion of Mathlib's
`Matrix.l2_opNorm_conjTranspose_mul_self`. -/
private theorem l2_opNorm_self_mul_conjTranspose (B : Matrix (Fin n) (Fin m) 𝕜) :
    ‖B * Bᴴ‖ = ‖B‖ * ‖B‖ := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (Bᴴ)
  rwa [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose] at h

open scoped Matrix.Norms.L2Operator in
/-- **Saad (8.8)**: `κ₂(Aᴴ A) = κ₂(A)²`. Passing to the normal equations squares the condition
number, which is the chapter's reason for the row projection methods of §8.2 and for running CG
on `Aᴴ A` without ever forming it (§8.3). The book states it for nonsingular `A`; no hypothesis
is needed, because a singular `A` inverts to `0` and both sides vanish. -/
theorem equation_8_8 (A : Matrix (Fin n) (Fin n) 𝕜) :
    Matrix.condNumberLp 2 (Aᴴ * A) = Matrix.condNumberLp 2 A ^ 2 := by
  have hinv : (Aᴴ * A)⁻¹ = A⁻¹ * (A⁻¹)ᴴ := by
    rw [Matrix.mul_inv_rev, Matrix.conjTranspose_nonsing_inv]
  rw [Matrix.condNumberLp, Matrix.condNumberLp, Matrix.lpOpNorm_two, Matrix.lpOpNorm_two,
    Matrix.lpOpNorm_two, Matrix.lpOpNorm_two, hinv, Matrix.l2_opNorm_conjTranspose_mul_self,
    l2_opNorm_self_mul_conjTranspose]
  ring

end SaadSparse.Chapter08

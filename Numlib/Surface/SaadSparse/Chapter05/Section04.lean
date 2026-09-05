import Numlib.Surface.SaadSparse.Chapter05.Section01

/-!
# §5.4 Additive and multiplicative projection processes

Section 5.4 of Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
SIAM, 2003: the additive procedure (Algorithm 5.5) with relaxation parameters, its residual
identity (5.22)–(5.23), the projectors `P_i = A V_i (V_iᵀ A V_i)⁻¹ V_iᵀ`, and the multiplicative
procedure (Algorithm 5.6).

Saad's remark that each inner step of the block relaxations of §4.1.1 is an orthogonal
projection step over `K_i = span(V_i)` is `blockCorrection_eq_projStep`: (4.17) is literally
(5.7) with `W = V = V_i`.

Left open here (phase 2 of the backbone, `tracker/backbone.md` §2.4.4 and
`tracker/saadsparse-ch1-4-5.md` §3 item 6): the identification of `additiveStep` with the
abstract additive projection process, the statement that `P_i` is the projector onto `A K_i`
orthogonally to `K_i`, the least-squares variant with `L_i = A K_i`, and the exactness criterion
"mutually orthogonal `A V_i` of total rank `n`" (R-5.25).
-/

open Matrix Module Finset
open scoped SaadSparse

namespace SaadSparse.Ch05

variable {n : ℕ}

local notation "E" n => EuclideanSpace ℝ (Fin n)

/-- Saad §5.4: a family of `p` subspaces of `ℝⁿ`, each given by a matrix of basis columns. -/
structure ProjFamily (n : ℕ) where
  /-- The number of subspaces. -/
  p : ℕ
  /-- The dimension of the `i`-th subspace. -/
  size : Fin p → ℕ
  /-- The `i`-th matrix of basis columns. -/
  V : ∀ i, Matrix (Fin n) (Fin (size i)) ℝ

variable (𝒱 : ProjFamily n) (A : Matrix (Fin n) (Fin n) ℝ)

/-- Saad §5.4: the local correction matrix `V_i (V_iᵀ A V_i)⁻¹ V_iᵀ` of the `i`-th subspace. -/
noncomputable def corrector (i : Fin 𝒱.p) : Matrix (Fin n) (Fin n) ℝ :=
  𝒱.V i * ((𝒱.V i)ᵀ * A * 𝒱.V i)⁻¹ * (𝒱.V i)ᵀ

/-- Saad (5.22): the projector `P_i = A V_i (V_iᵀ A V_i)⁻¹ V_iᵀ` onto `A K_i` orthogonally to
`K_i`. -/
noncomputable def P_i (i : Fin 𝒱.p) : Matrix (Fin n) (Fin n) ℝ :=
  A * 𝒱.V i * ((𝒱.V i)ᵀ * A * 𝒱.V i)⁻¹ * (𝒱.V i)ᵀ

/-- Saad, Algorithm 5.5, with relaxation parameters `ω_i`. -/
noncomputable def additiveStep (ω : Fin 𝒱.p → ℝ) (b x : E n) : E n :=
  x + ∑ i, ω i • ((corrector 𝒱 A i) ⬝ (b - (A ⬝ x)))

/-- Saad, Algorithm 5.6: one multiplicative sweep, successive projection steps over
`K_1, …, K_p`. -/
noncomputable def multiplicativeSweep (b : E n) (x : E n) : E n :=
  (List.finRange 𝒱.p).foldl (fun y i => projStep A b (𝒱.V i) (𝒱.V i) y) x

variable {𝒱 A}

/-- `P_i` is Saad's (1.66) projector for the bases `A V_i` and `V_i`. -/
theorem P_i_eq_obliqueProj (i : Fin 𝒱.p) :
    P_i 𝒱 A i = Matrix.obliqueProj (A * 𝒱.V i) (𝒱.V i) := by
  rw [P_i, Matrix.obliqueProj, conjTranspose_eq_transpose, Matrix.mul_assoc (𝒱.V i)ᵀ A]

/-- `A` times the local corrector is the projector `P_i`. -/
theorem mul_corrector (i : Fin 𝒱.p) : A * corrector 𝒱 A i = P_i 𝒱 A i := by
  rw [corrector, P_i, ← Matrix.mul_assoc, ← Matrix.mul_assoc]

/-- Matrices act on `ℝⁿ` through `toEuclideanLin` multiplicatively. -/
theorem toEuclideanLin_mul_apply (M N : Matrix (Fin n) (Fin n) ℝ) (z : E n) :
    ((M * N) ⬝ z) = M ⬝ (N ⬝ z) := by
  have h : (M * N) *ᵥ WithLp.ofLp z = M *ᵥ (N *ᵥ WithLp.ofLp z) := (mulVec_mulVec _ _ _).symm
  exact congrArg (WithLp.toLp 2) h

/-- Saad (5.22)–(5.23): the residual of the additive procedure is
`r_{k+1} = (I - ∑ ω_i P_i) r_k`. -/
theorem residual_additiveStep (ω : Fin 𝒱.p → ℝ) (b x : E n) :
    b - (A ⬝ additiveStep 𝒱 A ω b x) =
      (b - (A ⬝ x)) - ∑ i, ω i • ((P_i 𝒱 A i) ⬝ (b - (A ⬝ x))) := by
  rw [additiveStep, map_add, map_sum]
  simp only [map_smul, ← toEuclideanLin_mul_apply, mul_corrector]
  abel

/-- Saad §5.4: (4.17), the block-relaxation correction, is the projection step (5.7) with
`W = V = V_i`. -/
theorem blockCorrection_eq_projStep {m : ℕ} (V : Matrix (Fin n) (Fin m) ℝ) (b x : E n) :
    x + ((V * (Vᵀ * A * V)⁻¹ * Vᵀ) ⬝ (b - (A ⬝ x))) = projStep A b V V x := rfl

end SaadSparse.Ch05

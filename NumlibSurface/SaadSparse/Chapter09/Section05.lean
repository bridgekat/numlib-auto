import Numlib.Krylov.NormalEquations
import Numlib.Krylov.Preconditioned
import NumlibSurface.SaadSparse.Chapter08.Section03
import NumlibSurface.SaadSparse.Chapter09.Section02

/-!
# Saad §9.5: preconditioned CG for the normal equations

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §9.5.

Both algorithms are Algorithm 9.1 (`pcg`) run on a normal-equations system and rearranged so
that only products with `A` and `Aᴴ` and solves with `M` occur, and neither `Aᴴ A` nor `A Aᴴ`
is ever formed. **Algorithm 9.7** (left-preconditioned CGNR) is `pcgnr` and **Algorithm 9.8**
(left-preconditioned CGNE) is `pcgne`; `pcgnr_eq` and `pcgne_eq` identify them with `pcg` for
`Aᴴ A x = Aᴴ b` and for `A Aᴴ u = b` read through `x = Aᴴ u`. They are §8.3's `cgnr` and
`cgne` (Algorithms 8.4 and 8.5) with `M⁻¹` inserted, and the two rearrangements — the residual
carried is the true residual `r_j = b - A x_j`, and the direction vectors of Algorithm 9.8
carry an extra `Aᴴ` — are the same ones.

The two optimality properties are `pcgnr_isMinRes` and `pcgne_isMinError`: Algorithm 9.1 is a
Galerkin method over the preconditioned Krylov space (`pcg_isGalerkinIterate`), and the two
readings of that condition through the adjoint are
`isGalerkin_adjoint_comp_iff_isMinRes` and `isMinError_of_isGalerkin_comp_adjoint`, the
general-subspace forms of what `Numlib/Krylov/NormalEquations` proves for the unpreconditioned
Krylov space. Unlike the unpreconditioned case, the two search spaces now *differ*: Algorithm
9.7 minimizes `‖b - A x‖₂` over `x₀ + 𝒦_m(M⁻¹ Aᴴ A, M⁻¹ Aᴴ r₀)` while Algorithm 9.8 minimizes
`‖x_* - x‖₂` over `x₀ + 𝒦_m(Aᴴ M⁻¹ A, Aᴴ M⁻¹ r₀)`; at `M = I` both are the single space
`x₀ + 𝒦_m(Aᴴ A, Aᴴ r₀)` of §8.3 (`Chapter08.subspace_adjoint_eq`).

The right, split and centred variants of P-9.4 and P-9.5 are the same derivation in other inner
products and are not formalized; see `plans/saadsparse-ch7-9.md` §4.

Indices are `0`-based, and division by a vanishing quantity is `0`, which reproduces the book's
breakdown behaviour.
-/

open Matrix

open scoped Matrix SaadSparse

namespace SaadSparse.Chapter09

open Chapter06 (op)

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-! ### Preliminaries: the two normal-equations operators -/

/-- `Aᴴ A` is a symmetric operator, whatever `A` is: it is the coefficient operator of the
system Algorithm 9.7 preconditions. -/
theorem isSymmetric_conjTranspose_mul (A : Matrix (Fin n) (Fin n) 𝕜) :
    (op (Aᴴ * A)).IsSymmetric := by
  intro x y
  simp only [op_mul_apply]
  rw [Chapter08.inner_op_conjTranspose, Chapter08.inner_op_self]

/-- `A Aᴴ` is a symmetric operator: the coefficient operator of the system Algorithm 9.8
preconditions. -/
theorem isSymmetric_mul_conjTranspose (A : Matrix (Fin n) (Fin n) 𝕜) :
    (op (A * Aᴴ)).IsSymmetric := by
  intro x y
  simp only [op_mul_apply]
  rw [Chapter08.inner_op_self, Chapter08.inner_op_conjTranspose]

/-- `(Aᴴ A p, p) = ‖A p‖₂²`: the denominator of Algorithm 9.7, line 4, is the one Algorithm 9.1
would form. -/
private theorem inner_conjTranspose_mul_self (A : Matrix (Fin n) (Fin n) 𝕜) (p : 𝔼) :
    inner 𝕜 p (op (Aᴴ * A) p) = (‖op A p‖ : 𝕜) ^ 2 := by
  rw [op_mul_apply, ← Chapter08.inner_op_self, inner_self_eq_norm_sq_to_K]

/-- `(A Aᴴ q, q) = (Aᴴ q, Aᴴ q)`: the denominator of Algorithm 9.8, line 4, is the one
Algorithm 9.1 would form, read through `p = Aᴴ q`. -/
private theorem inner_mul_conjTranspose_self (A : Matrix (Fin n) (Fin n) 𝕜) (q : 𝔼) :
    inner 𝕜 (op Aᴴ q) (op Aᴴ q) = inner 𝕜 q (op (A * Aᴴ) q) := by
  rw [op_mul_apply, Chapter08.inner_op_conjTranspose]

/-- `Aᴴ` carries the Krylov space of `M⁻¹ A Aᴴ` to the Krylov space of `Aᴴ M⁻¹ A`:
`Aᴴ 𝒦_m(M⁻¹ A Aᴴ, v) = 𝒦_m(Aᴴ M⁻¹ A, Aᴴ v)`. This is the change of variables `x = Aᴴ u` of
Algorithm 9.8, and it is what names the affine space that algorithm searches. -/
theorem map_krylov_conjTranspose (A M : Matrix (Fin n) (Fin n) 𝕜)
    (v : EuclideanSpace 𝕜 (Fin n)) (m : ℕ) :
    (Chapter06.krylov (M⁻¹ * (A * Aᴴ)) v m).map (op Aᴴ)
      = Chapter06.krylov (Aᴴ * (M⁻¹ * A)) (op Aᴴ v) m := by
  rw [Chapter06.krylov_eq, Chapter06.krylov_eq, ← Matrix.mul_assoc M⁻¹ A Aᴴ, op_mul (M⁻¹ * A) Aᴴ,
    op_mul Aᴴ (M⁻¹ * A), op_mul M⁻¹ A]
  exact Krylov.map_subspace_comp (op M⁻¹ ∘ₗ op A) (op Aᴴ) v m

/-! ### The two optimality readings, over an arbitrary subspace

`Numlib/Krylov/NormalEquations` states both readings for the *unpreconditioned* Krylov space
`𝒦_m(Aᴴ A, Aᴴ r₀)`, which is all §8.3 needs. Preconditioning replaces that space by another
one, and nothing in either argument uses the shape of the space, so both are restated here for
an arbitrary subspace `K`. -/

/-- **CGNR's optimality over an arbitrary subspace.** A Galerkin iterate for the normal
equations `Aᴴ A x = Aᴴ b` over `x₀ + K` is exactly a minimal-residual iterate for `A x = b`
over `x₀ + K`: both say that `b - A x ⟂ A K`. This is
`Krylov.isGalerkinIterate_adjoint_comp_iff_isMinRes` with the Krylov subspace it is stated for
replaced by an arbitrary `K`. -/
theorem isGalerkin_adjoint_comp_iff_isMinRes (A : Matrix (Fin n) (Fin n) 𝕜)
    (b x₀ : EuclideanSpace 𝕜 (Fin n)) (K : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n)))
    (x : EuclideanSpace 𝕜 (Fin n)) :
    IsGalerkin (op Aᴴ ∘ₗ op A) (op Aᴴ b) x₀ K x ↔ IsMinRes (op A) b x₀ K x := by
  rw [IsMinRes.iff_isPetrovGalerkin]
  constructor <;> rintro ⟨hmem, horth⟩
  · refine ⟨hmem, (Submodule.mem_orthogonal _ _).2 ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    have h := (Submodule.mem_orthogonal _ _).1 horth w hw
    rwa [LinearMap.comp_apply, ← map_sub,
      Krylov.inner_adjoint_right (Chapter08.inner_op_conjTranspose A)] at h
  · refine ⟨hmem, (Submodule.mem_orthogonal _ _).2 fun w hw => ?_⟩
    have h := (Submodule.mem_orthogonal _ _).1 horth (op A w) (Submodule.mem_map_of_mem hw)
    rwa [LinearMap.comp_apply, ← map_sub,
      Krylov.inner_adjoint_right (Chapter08.inner_op_conjTranspose A)]

/-- **CGNE's optimality over an arbitrary subspace.** If `u` is a Galerkin iterate for
`A Aᴴ u = b` over `u₀ + K` and `x = x₀ + Aᴴ (u - u₀)`, then `x` minimizes the *error*
`‖x_* - y‖` over `y ∈ x₀ + Aᴴ K`. This is
`Krylov.isMinError_of_isGalerkinIterate_comp_adjoint` with the Krylov subspace it is stated for
replaced by an arbitrary `K`. -/
theorem isMinError_of_isGalerkin_comp_adjoint (A : Matrix (Fin n) (Fin n) 𝕜)
    {b x₀ u₀ u xstar : EuclideanSpace 𝕜 (Fin n)}
    {K : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n))} (hx₀ : x₀ = op Aᴴ u₀)
    (hstar : op A xstar = b) (hu : IsGalerkin (op A ∘ₗ op Aᴴ) b u₀ K u) :
    IsMinError xstar x₀ (K.map (op Aᴴ)) (x₀ + op Aᴴ (u - u₀)) := by
  refine ⟨by rw [add_sub_cancel_left]; exact Submodule.mem_map_of_mem hu.mem, fun y hy => ?_⟩
  rw [show xstar - (x₀ + op Aᴴ (u - u₀)) = (xstar - x₀) - op Aᴴ (u - u₀) by abel,
    show xstar - y = (xstar - x₀) - (y - x₀) by abel]
  refine Submodule.norm_sub_le_of_forall_inner_eq_zero
    (Submodule.mem_map_of_mem hu.mem) ?_ hy
  rintro _ ⟨z, hz, rfl⟩
  have h1 : op A (op Aᴴ (u - u₀)) = (op A ∘ₗ op Aᴴ) u - (op A ∘ₗ op Aᴴ) u₀ := by
    rw [← LinearMap.comp_apply]
    exact map_sub _ _ _
  have h2 : op A x₀ = (op A ∘ₗ op Aᴴ) u₀ := by rw [hx₀, LinearMap.comp_apply]
  have hA : op A ((xstar - x₀) - op Aᴴ (u - u₀)) = b - (op A ∘ₗ op Aᴴ) u := by
    rw [map_sub, map_sub, hstar, h1, h2]; abel
  rw [Krylov.inner_adjoint_right (Chapter08.inner_op_conjTranspose A), hA, ← inner_conj_symm,
    (Submodule.mem_orthogonal _ _).1 hu.orth z hz, map_zero]

/-! ### Algorithm 9.7: left-preconditioned CGNR -/

section CGNR

variable (A M : Matrix (Fin n) (Fin n) 𝕜)

/-- **Algorithm 9.7**, line 4: `α_j = (z_j, r̃_j)/‖w_j‖₂²`, with `r̃_j = Aᴴ r_j`,
`z_j = M⁻¹ r̃_j` and `w_j = A p_j` recomputed rather than stored. -/
noncomputable def pcgnrStepAlpha (s : Krylov.CGNR.State 𝔼) : 𝕜 :=
  inner 𝕜 (op Aᴴ s.r) (op M⁻¹ (op Aᴴ s.r)) / (‖op A s.p‖ : 𝕜) ^ 2

/-- **Algorithm 9.7**, line 6: `r_{j+1} = r_j - α_j w_j`. -/
noncomputable def pcgnrStepR (s : Krylov.CGNR.State 𝔼) : 𝔼 :=
  s.r - pcgnrStepAlpha A M s • op A s.p

/-- **Algorithm 9.7**, line 9: `β_j = (z_{j+1}, r̃_{j+1})/(z_j, r̃_j)`. -/
noncomputable def pcgnrStepBeta (s : Krylov.CGNR.State 𝔼) : 𝕜 :=
  inner 𝕜 (op Aᴴ (pcgnrStepR A M s)) (op M⁻¹ (op Aᴴ (pcgnrStepR A M s))) /
    inner 𝕜 (op Aᴴ s.r) (op M⁻¹ (op Aᴴ s.r))

/-- One pass through lines 3–10 of **Algorithm 9.7**, on the triple `(x_j, r_j, p_j)`. -/
noncomputable def pcgnrStep (s : Krylov.CGNR.State 𝔼) : Krylov.CGNR.State 𝔼 :=
  { x := s.x + pcgnrStepAlpha A M s • s.p
    r := pcgnrStepR A M s
    p := op M⁻¹ (op Aᴴ (pcgnrStepR A M s)) + pcgnrStepBeta A M s • s.p }

/-- **Algorithm 9.7** (left-preconditioned CGNR) run for `j` steps, started from
`r_0 = b - A x_0` and `p_0 = z_0 = M⁻¹ Aᴴ r_0`. -/
noncomputable def pcgnr (b x₀ : EuclideanSpace 𝕜 (Fin n)) (j : ℕ) : Krylov.CGNR.State 𝔼 :=
  (pcgnrStep A M)^[j] { x := x₀, r := b - op A x₀, p := op M⁻¹ (op Aᴴ (b - op A x₀)) }

/-- Algorithm 9.7, line 5: `x_{j+1} = x_j + α_j p_j`. -/
theorem pcgnrStep_x (s : Krylov.CGNR.State 𝔼) :
    (pcgnrStep A M s).x = s.x + pcgnrStepAlpha A M s • s.p := rfl

/-- Algorithm 9.7, line 6: `r_{j+1} = r_j - α_j w_j`. -/
theorem pcgnrStep_r (s : Krylov.CGNR.State 𝔼) : (pcgnrStep A M s).r = pcgnrStepR A M s := rfl

/-- Algorithm 9.7, line 10: `p_{j+1} = z_{j+1} + β_j p_j`. -/
theorem pcgnrStep_p (s : Krylov.CGNR.State 𝔼) :
    (pcgnrStep A M s).p
      = op M⁻¹ (op Aᴴ (pcgnrStepR A M s)) + pcgnrStepBeta A M s • s.p := rfl

/-- The recurrence: state `j + 1` is one pass of Algorithm 9.7 applied to state `j`. -/
theorem pcgnr_succ (b x₀ : EuclideanSpace 𝕜 (Fin n)) (j : ℕ) :
    pcgnr A M b x₀ (j + 1) = pcgnrStep A M (pcgnr A M b x₀ j) :=
  Function.iterate_succ_apply' _ _ _

/-- Algorithm 9.7, line 1: the iteration starts at `x_0`. -/
@[simp] theorem pcgnr_zero_x (b x₀ : EuclideanSpace 𝕜 (Fin n)) : (pcgnr A M b x₀ 0).x = x₀ := rfl

/-- Algorithm 9.7, line 1: `r_0 = b - A x_0`. -/
@[simp] theorem pcgnr_zero_r (b x₀ : EuclideanSpace 𝕜 (Fin n)) :
    (pcgnr A M b x₀ 0).r = b - op A x₀ := rfl

/-- Algorithm 9.7, line 1: `p_0 = z_0 = M⁻¹ Aᴴ r_0`. -/
@[simp] theorem pcgnr_zero_p (b x₀ : EuclideanSpace 𝕜 (Fin n)) :
    (pcgnr A M b x₀ 0).p = op M⁻¹ (op Aᴴ (b - op A x₀)) := rfl

/-- The `r` field of Algorithm 9.7 is the true residual `b - A x_j`; the normal-equations
residual `r̃_j = Aᴴ r_j` is the one the preconditioner is applied to. -/
theorem pcgnr_residual_eq (b x₀ : EuclideanSpace 𝕜 (Fin n)) (j : ℕ) :
    (pcgnr A M b x₀ j).r = b - op A (pcgnr A M b x₀ j).x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pcgnr_succ, pcgnrStep_r, pcgnrStep_x, pcgnrStepR, ih, map_add, map_smul, sub_sub]

/-! #### The bridge to Algorithm 9.1 -/

variable {A M}

private theorem pcgnrStepAlpha_eq (hMinv : (op M⁻¹).IsSymmetric) (s : Krylov.CGNR.State 𝔼) :
    pcgnrStepAlpha A M s = pcgStepAlpha (Aᴴ * A) M (s.x, op Aᴴ s.r, s.p) := by
  rw [pcgnrStepAlpha, pcgStepAlpha_def, hMinv (op Aᴴ s.r) (op Aᴴ s.r),
    inner_conjTranspose_mul_self]

private theorem pcgnrStepR_eq (hMinv : (op M⁻¹).IsSymmetric) (s : Krylov.CGNR.State 𝔼) :
    op Aᴴ (pcgnrStepR A M s) = pcgStepR (Aᴴ * A) M (s.x, op Aᴴ s.r, s.p) := by
  rw [pcgnrStepR, pcgStepR_def, ← pcgnrStepAlpha_eq hMinv, map_sub, map_smul, op_mul_apply]

private theorem pcgnrStepBeta_eq (hMinv : (op M⁻¹).IsSymmetric) (s : Krylov.CGNR.State 𝔼) :
    pcgnrStepBeta A M s = pcgStepBeta (Aᴴ * A) M (s.x, op Aᴴ s.r, s.p) := by
  rw [pcgnrStepBeta, pcgStepBeta_def, ← pcgnrStepR_eq hMinv,
    hMinv (op Aᴴ (pcgnrStepR A M s)) (op Aᴴ (pcgnrStepR A M s)), hMinv (op Aᴴ s.r) (op Aᴴ s.r)]

private theorem pcgnrStep_eq (hMinv : (op M⁻¹).IsSymmetric) (s : Krylov.CGNR.State 𝔼) :
    ((pcgnrStep A M s).x, op Aᴴ (pcgnrStep A M s).r, (pcgnrStep A M s).p)
      = pcgStep (Aᴴ * A) M (s.x, op Aᴴ s.r, s.p) := by
  rw [pcgnrStep_x, pcgnrStep_r, pcgnrStep_p, pcgStep, pcgnrStepAlpha_eq hMinv,
    pcgnrStepBeta_eq hMinv, ← pcgnrStepR_eq hMinv]

/-- **Algorithm 9.7 is Algorithm 9.1 for the normal equations.** The triple
`(x_j, Aᴴ r_j, p_j)` of Algorithm 9.7 is the triple of Algorithm 9.1 applied to
`Aᴴ A x = Aᴴ b` with the preconditioner `M`: the residual Algorithm 9.1 would carry is the
normal-equations residual `r̃_j = Aᴴ r_j`, and its denominator `(Aᴴ A p_j, p_j)` is `‖w_j‖₂²`.
Only the symmetry of `M⁻¹` is needed, to move it across the inner products of lines 4 and 9. -/
theorem pcgnr_eq (hMinv : (op M⁻¹).IsSymmetric) (b x₀ : EuclideanSpace 𝕜 (Fin n)) (j : ℕ) :
    ((pcgnr A M b x₀ j).x, op Aᴴ (pcgnr A M b x₀ j).r, (pcgnr A M b x₀ j).p)
      = pcg (Aᴴ * A) M (op Aᴴ b) x₀ j := by
  have hinit : op Aᴴ b - op (Aᴴ * A) x₀ = op Aᴴ (b - op A x₀) := by
    rw [op_mul_apply, ← map_sub]
  induction j with
  | zero => exact (congrArg (fun z : 𝔼 => (x₀, z, op M⁻¹ z)) hinit).symm
  | succ j ih => rw [pcgnr_succ, pcg_succ, ← ih, pcgnrStep_eq hMinv]

/-- The iterate of Algorithm 9.7 is the iterate of Algorithm 9.1 on the normal equations. -/
theorem pcgnrX_eq (hMinv : (op M⁻¹).IsSymmetric) (b x₀ : EuclideanSpace 𝕜 (Fin n)) (j : ℕ) :
    (pcgnr A M b x₀ j).x = pcgX (Aᴴ * A) M (op Aᴴ b) x₀ j := by
  rw [pcgX, ← pcgnr_eq hMinv b x₀ j]

/-- **Saad §9.5, the optimality of Algorithm 9.7**: `x_m` minimizes the true residual
`‖b - A x‖₂` over the preconditioned affine space `x_0 + 𝒦_m(M⁻¹ Aᴴ A, M⁻¹ Aᴴ r_0)`.

The coercivity hypothesis is the generalized eigenvalue bound `c (M x, x) ≤ ‖A x‖₂²` that makes
`M⁻¹ Aᴴ A` symmetric coercive in the `M`-inner product; for a nonsingular `A` and a symmetric
positive definite `M` it holds with `c = σ_min(A)²/λ_max(M)`. -/
theorem pcgnr_isMinRes (hM : Krylov.IsPreconditioner (op M) (op M⁻¹)) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x : 𝔼, c * RCLike.re (inner 𝕜 (op M x) x) ≤ ‖op A x‖ ^ 2)
    (b x₀ : EuclideanSpace 𝕜 (Fin n)) (m : ℕ) :
    IsMinRes (op A) b x₀
        (Chapter06.krylov (M⁻¹ * (Aᴴ * A)) (op M⁻¹ (op Aᴴ (b - op A x₀))) m)
      (pcgnr A M b x₀ m).x := by
  have hinit : op Aᴴ b - op (Aᴴ * A) x₀ = op Aᴴ (b - op A x₀) := by
    rw [op_mul_apply, ← map_sub]
  have hcoer' : ∀ x : 𝔼, c * RCLike.re (inner 𝕜 (op M x) x)
      ≤ RCLike.re (inner 𝕜 (op (Aᴴ * A) x) x) := fun x => by
    rw [op_mul, Krylov.inner_adjoint_comp_self (Chapter08.inner_op_conjTranspose A) x,
      RCLike.ofReal_re]
    exact hcoer x
  have h := pcg_isGalerkinIterate (A := Aᴴ * A) (M := M) hM (isSymmetric_conjTranspose_mul A)
    hc hcoer' (op Aᴴ b) x₀ m
  rw [hinit, op_mul] at h
  rw [pcgnrX_eq hM.isSymmetric_inv]
  exact (isGalerkin_adjoint_comp_iff_isMinRes A b x₀ _ _).1 h

end CGNR

/-! ### Algorithm 9.8: left-preconditioned CGNE -/

section CGNE

variable (A M : Matrix (Fin n) (Fin n) 𝕜)

/-- **Algorithm 9.8**, line 4: `α_j = (z_j, r_j)/(p_j, p_j)`, with `z_j = M⁻¹ r_j` recomputed
rather than stored. The direction `p_j` is the direction `q_j` of Algorithm 9.1 for
`A Aᴴ u = b` premultiplied by `Aᴴ`, so `(p_j, p_j)` is that algorithm's `(A Aᴴ q_j, q_j)`. -/
noncomputable def pcgneStepAlpha (s : Krylov.CGNE.State 𝔼) : 𝕜 :=
  inner 𝕜 s.r (op M⁻¹ s.r) / inner 𝕜 s.p s.p

/-- **Algorithm 9.8**, line 6: `r_{j+1} = r_j - α_j w_j` with `w_j = A p_j`. -/
noncomputable def pcgneStepR (s : Krylov.CGNE.State 𝔼) : 𝔼 :=
  s.r - pcgneStepAlpha M s • op A s.p

/-- **Algorithm 9.8**, line 8: `β_j = (z_{j+1}, r_{j+1})/(z_j, r_j)`. -/
noncomputable def pcgneStepBeta (s : Krylov.CGNE.State 𝔼) : 𝕜 :=
  inner 𝕜 (pcgneStepR A M s) (op M⁻¹ (pcgneStepR A M s)) / inner 𝕜 s.r (op M⁻¹ s.r)

/-- One pass through lines 3–9 of **Algorithm 9.8**, on the triple `(x_j, r_j, p_j)`. -/
noncomputable def pcgneStep (s : Krylov.CGNE.State 𝔼) : Krylov.CGNE.State 𝔼 :=
  { x := s.x + pcgneStepAlpha M s • s.p
    r := pcgneStepR A M s
    p := op Aᴴ (op M⁻¹ (pcgneStepR A M s)) + pcgneStepBeta A M s • s.p }

/-- **Algorithm 9.8** (left-preconditioned CGNE) run for `j` steps, started from
`r_0 = b - A x_0` and `p_0 = Aᴴ z_0 = Aᴴ M⁻¹ r_0`. -/
noncomputable def pcgne (b x₀ : EuclideanSpace 𝕜 (Fin n)) (j : ℕ) : Krylov.CGNE.State 𝔼 :=
  (pcgneStep A M)^[j] { x := x₀, r := b - op A x₀, p := op Aᴴ (op M⁻¹ (b - op A x₀)) }

/-- Algorithm 9.8, line 5: `x_{j+1} = x_j + α_j p_j`. -/
theorem pcgneStep_x (s : Krylov.CGNE.State 𝔼) :
    (pcgneStep A M s).x = s.x + pcgneStepAlpha M s • s.p := rfl

/-- Algorithm 9.8, line 6: `r_{j+1} = r_j - α_j w_j`. -/
theorem pcgneStep_r (s : Krylov.CGNE.State 𝔼) : (pcgneStep A M s).r = pcgneStepR A M s := rfl

/-- Algorithm 9.8, line 9: `p_{j+1} = Aᴴ z_{j+1} + β_j p_j`. -/
theorem pcgneStep_p (s : Krylov.CGNE.State 𝔼) :
    (pcgneStep A M s).p
      = op Aᴴ (op M⁻¹ (pcgneStepR A M s)) + pcgneStepBeta A M s • s.p := rfl

/-- The recurrence: state `j + 1` is one pass of Algorithm 9.8 applied to state `j`. -/
theorem pcgne_succ (b x₀ : EuclideanSpace 𝕜 (Fin n)) (j : ℕ) :
    pcgne A M b x₀ (j + 1) = pcgneStep A M (pcgne A M b x₀ j) :=
  Function.iterate_succ_apply' _ _ _

/-- Algorithm 9.8, line 1: the iteration starts at `x_0`. -/
@[simp] theorem pcgne_zero_x (b x₀ : EuclideanSpace 𝕜 (Fin n)) : (pcgne A M b x₀ 0).x = x₀ := rfl

/-- Algorithm 9.8, line 1: `r_0 = b - A x_0`. -/
@[simp] theorem pcgne_zero_r (b x₀ : EuclideanSpace 𝕜 (Fin n)) :
    (pcgne A M b x₀ 0).r = b - op A x₀ := rfl

/-- Algorithm 9.8, line 1: `p_0 = Aᴴ z_0 = Aᴴ M⁻¹ r_0`. -/
@[simp] theorem pcgne_zero_p (b x₀ : EuclideanSpace 𝕜 (Fin n)) :
    (pcgne A M b x₀ 0).p = op Aᴴ (op M⁻¹ (b - op A x₀)) := rfl

/-- The `r` field of Algorithm 9.8 is the true residual `b - A x_j`. -/
theorem pcgne_residual_eq (b x₀ : EuclideanSpace 𝕜 (Fin n)) (j : ℕ) :
    (pcgne A M b x₀ j).r = b - op A (pcgne A M b x₀ j).x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pcgne_succ, pcgneStep_r, pcgneStep_x, pcgneStepR, ih, map_add, map_smul, sub_sub]

/-! #### The bridge to Algorithm 9.1 -/

variable {A M}

/-- **Algorithm 9.8 is Algorithm 9.1 for `A Aᴴ u = b`, read in `x = Aᴴ u`.** For any `u_0` with
`Aᴴ u_0 = x_0` the iterate is `x_j = x_0 + Aᴴ (u_j - u_0)`, the search direction is `Aᴴ` of the
direction of Algorithm 9.1, and the two residuals agree — so no vector of the `u`-iteration is
ever formed. Only the symmetry of `M⁻¹` is needed, to move it across the inner products of
lines 4 and 8. -/
theorem pcgne_eq (hMinv : (op M⁻¹).IsSymmetric) (b x₀ : EuclideanSpace 𝕜 (Fin n))
    {u₀ : EuclideanSpace 𝕜 (Fin n)} (hu₀ : op Aᴴ u₀ = x₀) (j : ℕ) :
    (pcgne A M b x₀ j).x = x₀ + op Aᴴ (pcgX (A * Aᴴ) M b u₀ j - u₀) ∧
      (pcgne A M b x₀ j).r = pcgR (A * Aᴴ) M b u₀ j ∧
      (pcgne A M b x₀ j).p = op Aᴴ (pcgP (A * Aᴴ) M b u₀ j) := by
  have hres : b - op (A * Aᴴ) u₀ = b - op A x₀ := by rw [op_mul_apply, hu₀]
  induction j with
  | zero =>
    refine ⟨?_, hres.symm, ?_⟩
    · change x₀ = x₀ + op Aᴴ (u₀ - u₀)
      rw [sub_self, map_zero, add_zero]
    · change op Aᴴ (op M⁻¹ (b - op A x₀)) = op Aᴴ (op M⁻¹ (b - op (A * Aᴴ) u₀))
      rw [hres]
  | succ j ih =>
    obtain ⟨hx, hr, hp⟩ := ih
    have halpha : pcgneStepAlpha M (pcgne A M b x₀ j) = pcgAlpha (A * Aᴴ) M b u₀ j := by
      rw [pcgneStepAlpha, pcgAlpha_eq, pcgZ, hr, hp, inner_mul_conjTranspose_self,
        hMinv (pcgR (A * Aᴴ) M b u₀ j) (pcgR (A * Aᴴ) M b u₀ j)]
    have hrstep : pcgneStepR A M (pcgne A M b x₀ j) = pcgR (A * Aᴴ) M b u₀ (j + 1) := by
      rw [pcgneStepR, pcgR_succ, halpha, hr, hp, op_mul_apply]
    have hbeta : pcgneStepBeta A M (pcgne A M b x₀ j) = pcgBeta (A * Aᴴ) M b u₀ j := by
      rw [pcgneStepBeta, hrstep, hr, pcgBeta_eq, pcgZ, pcgZ,
        hMinv (pcgR (A * Aᴴ) M b u₀ (j + 1)) (pcgR (A * Aᴴ) M b u₀ (j + 1)),
        hMinv (pcgR (A * Aᴴ) M b u₀ j) (pcgR (A * Aᴴ) M b u₀ j)]
    refine ⟨?_, ?_, ?_⟩
    · rw [pcgne_succ, pcgneStep_x, pcgX_succ, hx, hp, halpha]
      simp only [map_sub, map_add, map_smul]
      abel
    · rw [pcgne_succ, pcgneStep_r]
      exact hrstep
    · rw [pcgne_succ, pcgneStep_p, pcgP_succ, pcgZ, hrstep, hbeta, hp, map_add, map_smul]

/-- The iterate of Algorithm 9.8, written through the change of variables `x = Aᴴ u`. -/
theorem pcgneX_eq (hMinv : (op M⁻¹).IsSymmetric) (b x₀ : EuclideanSpace 𝕜 (Fin n))
    {u₀ : EuclideanSpace 𝕜 (Fin n)} (hu₀ : op Aᴴ u₀ = x₀) (j : ℕ) :
    (pcgne A M b x₀ j).x = x₀ + op Aᴴ (pcgX (A * Aᴴ) M b u₀ j - u₀) :=
  (pcgne_eq hMinv b x₀ hu₀ j).1

/-- **Saad §9.5, the optimality of Algorithm 9.8**: `x_m` minimizes the *error* `‖x_* - x‖₂`
over the affine space `x_0 + 𝒦_m(Aᴴ M⁻¹ A, Aᴴ M⁻¹ r_0)`.

That space is not the one Algorithm 9.7 searches: preconditioning separates the two normal
equations, and only at `M = I` do `𝒦_m(M⁻¹ Aᴴ A, M⁻¹ Aᴴ r_0)` and `𝒦_m(Aᴴ M⁻¹ A, Aᴴ M⁻¹ r_0)`
coincide (`Chapter08.subspace_adjoint_eq`). -/
theorem pcgne_isMinError (hM : Krylov.IsPreconditioner (op M) (op M⁻¹)) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x : 𝔼, c * RCLike.re (inner 𝕜 (op M x) x) ≤ ‖op Aᴴ x‖ ^ 2)
    (b x₀ : EuclideanSpace 𝕜 (Fin n)) {u₀ xstar : EuclideanSpace 𝕜 (Fin n)}
    (hu₀ : op Aᴴ u₀ = x₀) (hstar : op A xstar = b) (m : ℕ) :
    IsMinError xstar x₀
        (Chapter06.krylov (Aᴴ * (M⁻¹ * A)) (op Aᴴ (op M⁻¹ (b - op A x₀))) m)
      (pcgne A M b x₀ m).x := by
  have hres : b - op (A * Aᴴ) u₀ = b - op A x₀ := by rw [op_mul_apply, hu₀]
  have hcoer' : ∀ x : 𝔼, c * RCLike.re (inner 𝕜 (op M x) x)
      ≤ RCLike.re (inner 𝕜 (op (A * Aᴴ) x) x) := fun x => by
    rw [op_mul, Krylov.inner_adjoint_comp_self (Chapter08.inner_op_self A) x, RCLike.ofReal_re]
    exact hcoer x
  have h := pcg_isGalerkinIterate (A := A * Aᴴ) (M := M) hM (isSymmetric_mul_conjTranspose A)
    hc hcoer' b u₀ m
  rw [hres, op_mul] at h
  rw [pcgneX_eq hM.isSymmetric_inv b x₀ hu₀ m,
    ← map_krylov_conjTranspose A M (op M⁻¹ (b - op A x₀)) m]
  exact isMinError_of_isGalerkin_comp_adjoint A hu₀.symm hstar h

end CGNE

end SaadSparse.Chapter09

import Numlib.Krylov.NormalEquations
import NumlibSurface.SaadSparse.Chapter06.Section02
import NumlibSurface.SaadSparse.Chapter08.Section01

/-!
# Saad §8.3: conjugate gradient and the normal equations

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §8.3.

Both algorithms of the section are the conjugate gradient method on a normal-equations system,
rearranged so that only products with `A` and `Aᴴ` occur and neither `Aᴴ A` nor `A Aᴴ` is ever
formed. **Algorithm 8.4** (CGNR) is `cgnr` and **Algorithm 8.5** (CGNE, Craig's method) is
`cgne`; `cgnr_eq` and `cgne_eq` identify them with the conjugate gradient iterates of
`Aᴴ A x = Aᴴ b` and of `A Aᴴ u = b` read through `x = Aᴴ u`, which is what
`Numlib/Krylov/NormalEquations` proves in general.

The two optimality properties are `cgnr_isMinRes` and `cgne_isMinError`. Over the *same* affine
subspace `x_0 + 𝒦_m(Aᴴ A, Aᴴ r_0)` — that is `subspace_adjoint_eq`, the section's closing
observation, since `Aᴴ 𝒦_m(A Aᴴ, r_0)` is that space — CGNR minimizes the residual `‖b - A x‖₂`
and CGNE the error `‖x_* - x‖₂`. `cgnr_norm_residual_le` is the price the book warns about at
(8.8): the CG bound applies with the condition number of `Aᴴ A`, so the rate is governed by
`κ₂(A) = σ_max/σ_min` and not by its square root.

The section is stated for a square `A`, the coefficient matrix of the system `A x = b` the
chapter is about; the rectangular least-squares picture is §8.1.
-/

open Matrix

open scoped Matrix SaadSparse

namespace SaadSparse.Chapter08

open Chapter06 (op)

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-! ### Preliminaries -/

/-- `Aᴴ` acts as the adjoint of `A`, in the form the backbone normal-equations layer takes as a
hypothesis. -/
theorem inner_op_conjTranspose (A : Matrix (Fin n) (Fin n) 𝕜) (u v : 𝔼) :
    inner 𝕜 (op Aᴴ u) v = inner 𝕜 u (op A v) :=
  inner_conjTranspose A u v

/-- The same with the roles of `A` and `Aᴴ` exchanged: `A` acts as the adjoint of `Aᴴ`. -/
theorem inner_op_self (A : Matrix (Fin n) (Fin n) 𝕜) (u v : 𝔼) :
    inner 𝕜 (op A u) v = inner 𝕜 u (op Aᴴ v) := by
  have h := inner_conjTranspose Aᴴ u v
  rwa [Matrix.conjTranspose_conjTranspose] at h

/-- A matrix product acts as the composite of the two actions. -/
private theorem op_mul (B C : Matrix (Fin n) (Fin n) 𝕜) : op (B * C) = op B ∘ₗ op C :=
  Matrix.toEuclideanLin_mul B C

/-- The book's `𝒦_m(Aᴴ A, v)` is the backbone Krylov subspace of the composite operator. -/
theorem krylov_conjTranspose_mul (B C : Matrix (Fin n) (Fin n) 𝕜) (v : 𝔼) (m : ℕ) :
    Chapter06.krylov (B * C) v m = Krylov.subspace (op B ∘ₗ op C) v m := by
  rw [Chapter06.krylov_eq, op_mul]

/-- `Aᴴ A` is symmetric positive definite as soon as `A` is nonsingular, which is the hypothesis
under which CGNR is well defined. -/
theorem isSymmetricCoercive_normal {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : Function.Injective (op A)) : (op Aᴴ ∘ₗ op A).IsSymmetricCoercive :=
  Krylov.adjoint_comp_isSymmetricCoercive_of_injective (inner_op_conjTranspose A) hA

/-- `A Aᴴ` is symmetric positive definite as soon as `Aᴴ` is nonsingular, which is the
hypothesis under which CGNE is well defined. -/
theorem isSymmetricCoercive_normal' {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : Function.Injective (op Aᴴ)) : (op A ∘ₗ op Aᴴ).IsSymmetricCoercive :=
  Krylov.adjoint_comp_isSymmetricCoercive_of_injective (inner_op_self A) hA

/-! ### Algorithm 8.4: CGNR -/

section CGNR

variable (A : Matrix (Fin n) (Fin n) 𝕜)

/-- **Algorithm 8.4**, line 4: `α_i = ‖z_i‖₂²/‖w_i‖₂²` with `z_i = Aᴴ r_i` and `w_i = A p_i`. -/
noncomputable def cgnrStepAlpha (s : Krylov.CGNR.State 𝔼) : 𝕜 :=
  (‖op Aᴴ s.r‖ : 𝕜) ^ 2 / (‖op A s.p‖ : 𝕜) ^ 2

/-- **Algorithm 8.4**, line 6: `r_{i+1} = r_i - α_i w_i`. -/
noncomputable def cgnrStepR (s : Krylov.CGNR.State 𝔼) : 𝔼 :=
  s.r - cgnrStepAlpha A s • op A s.p

/-- **Algorithm 8.4**, line 8: `β_i = ‖z_{i+1}‖₂²/‖z_i‖₂²`. -/
noncomputable def cgnrStepBeta (s : Krylov.CGNR.State 𝔼) : 𝕜 :=
  (‖op Aᴴ (cgnrStepR A s)‖ : 𝕜) ^ 2 / (‖op Aᴴ s.r‖ : 𝕜) ^ 2

/-- One pass through lines 3–9 of **Algorithm 8.4**, on the triple `(x_i, r_i, p_i)`; the
normal-equations residual `z_i = Aᴴ r_i` and the product `w_i = A p_i` are recomputed rather
than stored. -/
noncomputable def cgnrStep (s : Krylov.CGNR.State 𝔼) : Krylov.CGNR.State 𝔼 :=
  { x := s.x + cgnrStepAlpha A s • s.p
    r := cgnrStepR A s
    p := op Aᴴ (cgnrStepR A s) + cgnrStepBeta A s • s.p }

/-- **Algorithm 8.4** (CGNR) run for `i` steps, started from `r_0 = b - A x_0` and
`p_0 = z_0 = Aᴴ r_0`. -/
noncomputable def cgnr (b x₀ : 𝔼) (i : ℕ) : Krylov.CGNR.State 𝔼 :=
  (cgnrStep A)^[i] { x := x₀, r := b - op A x₀, p := op Aᴴ (b - op A x₀) }

variable (b x₀ : EuclideanSpace 𝕜 (Fin n))

/-- The recurrence: state `i + 1` is one pass of Algorithm 8.4 applied to state `i`. -/
theorem cgnr_succ (i : ℕ) : cgnr A b x₀ (i + 1) = cgnrStep A (cgnr A b x₀ i) :=
  Function.iterate_succ_apply' _ _ _

/-- Algorithm 8.4, line 1: the iteration starts at `x_0`. -/
@[simp] theorem cgnr_zero_x : (cgnr A b x₀ 0).x = x₀ := rfl

/-- Algorithm 8.4, line 1: `r_0 = b - A x_0`. -/
@[simp] theorem cgnr_zero_r : (cgnr A b x₀ 0).r = b - op A x₀ := rfl

/-- Algorithm 8.4, line 1: `p_0 = z_0 = Aᴴ r_0`. -/
@[simp] theorem cgnr_zero_p : (cgnr A b x₀ 0).p = op Aᴴ (b - op A x₀) := rfl

/-! #### The bridge to the backbone CGNR recurrence -/

variable {A}

private theorem cgnrStepAlpha_eq (s : Krylov.CGNR.State 𝔼) :
    cgnrStepAlpha A s = Krylov.CGNR.alpha (op A) (op Aᴴ) s := by
  rw [cgnrStepAlpha, Krylov.CGNR.alpha, inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K]

private theorem cgnrStepR_eq (s : Krylov.CGNR.State 𝔼) :
    cgnrStepR A s = (Krylov.CGNR.step (op A) (op Aᴴ) s).r := by
  rw [cgnrStepR, cgnrStepAlpha_eq, Krylov.CGNR.step_r]

private theorem cgnrStepBeta_eq (s : Krylov.CGNR.State 𝔼) :
    cgnrStepBeta A s = Krylov.CGNR.beta (op A) (op Aᴴ) s := by
  rw [cgnrStepBeta, Krylov.CGNR.beta, cgnrStepR_eq, inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K]

private theorem cgnrStep_eq (s : Krylov.CGNR.State 𝔼) :
    cgnrStep A s = Krylov.CGNR.step (op A) (op Aᴴ) s := by
  have h : cgnrStep A s =
      { x := s.x + cgnrStepAlpha A s • s.p
        r := cgnrStepR A s
        p := op Aᴴ (cgnrStepR A s) + cgnrStepBeta A s • s.p } := rfl
  rw [h, cgnrStepAlpha_eq, cgnrStepR_eq, cgnrStepBeta_eq]
  rfl

/-- Algorithm 8.4 is the backbone CGNR recurrence for the pair `(A, Aᴴ)`. -/
theorem cgnr_eq_iterate (i : ℕ) :
    cgnr A b x₀ i = Krylov.CGNR.iterate (op A) (op Aᴴ) b x₀ i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [cgnr_succ, ih, cgnrStep_eq, Krylov.CGNR.iterate_succ]

/-- **Saad, Algorithm 8.4**: CGNR computes the conjugate gradient iterates of the normal
equations `Aᴴ A x = Aᴴ b`, without ever forming `Aᴴ A`. Everything the backbone proves of
`CG.iterate` — the orthogonality relations, finite termination, the Chebyshev bounds — therefore
holds of it. -/
theorem cgnr_eq (i : ℕ) :
    (cgnr A b x₀ i).x = (CG.iterate (op Aᴴ ∘ₗ op A) (op Aᴴ b) x₀ i).x := by
  rw [cgnr_eq_iterate]
  exact Krylov.CGNR.iterate_x_eq (op A) (op Aᴴ) b x₀ (inner_op_conjTranspose A) i

/-- The `r` field of Algorithm 8.4 is the true residual `b - A x_i`. -/
theorem cgnr_residual_eq (i : ℕ) : (cgnr A b x₀ i).r = b - op A (cgnr A b x₀ i).x := by
  rw [cgnr_eq_iterate]
  exact Krylov.CGNR.residual_eq (op A) (op Aᴴ) b x₀ (inner_op_conjTranspose A) i

end CGNR

/-! ### Algorithm 8.5: CGNE (Craig's method) -/

section CGNE

variable (A : Matrix (Fin n) (Fin n) 𝕜)

/-- **Algorithm 8.5**, line 3: `α_i = (r_i, r_i)/(p_i, p_i)`. -/
noncomputable def cgneStepAlpha (s : Krylov.CGNE.State 𝔼) : 𝕜 :=
  (‖s.r‖ : 𝕜) ^ 2 / (‖s.p‖ : 𝕜) ^ 2

/-- **Algorithm 8.5**, line 5: `r_{i+1} = r_i - α_i A p_i`. -/
noncomputable def cgneStepR (s : Krylov.CGNE.State 𝔼) : 𝔼 :=
  s.r - cgneStepAlpha s • op A s.p

/-- **Algorithm 8.5**, line 6: `β_i = (r_{i+1}, r_{i+1})/(r_i, r_i)`. -/
noncomputable def cgneStepBeta (s : Krylov.CGNE.State 𝔼) : 𝕜 :=
  (‖cgneStepR A s‖ : 𝕜) ^ 2 / (‖s.r‖ : 𝕜) ^ 2

/-- One pass through lines 3–7 of **Algorithm 8.5**, on the triple `(x_i, r_i, p_i)`. -/
noncomputable def cgneStep (s : Krylov.CGNE.State 𝔼) : Krylov.CGNE.State 𝔼 :=
  { x := s.x + cgneStepAlpha s • s.p
    r := cgneStepR A s
    p := op Aᴴ (cgneStepR A s) + cgneStepBeta A s • s.p }

/-- **Algorithm 8.5** (CGNE, Craig's method) run for `i` steps, started from `r_0 = b - A x_0`
and `p_0 = Aᴴ r_0`. -/
noncomputable def cgne (b x₀ : 𝔼) (i : ℕ) : Krylov.CGNE.State 𝔼 :=
  (cgneStep A)^[i] { x := x₀, r := b - op A x₀, p := op Aᴴ (b - op A x₀) }

variable (b x₀ : EuclideanSpace 𝕜 (Fin n))

/-- The recurrence: state `i + 1` is one pass of Algorithm 8.5 applied to state `i`. -/
theorem cgne_succ (i : ℕ) : cgne A b x₀ (i + 1) = cgneStep A (cgne A b x₀ i) :=
  Function.iterate_succ_apply' _ _ _

/-- Algorithm 8.5, line 1: the iteration starts at `x_0`. -/
@[simp] theorem cgne_zero_x : (cgne A b x₀ 0).x = x₀ := rfl

/-- Algorithm 8.5, line 1: `r_0 = b - A x_0`. -/
@[simp] theorem cgne_zero_r : (cgne A b x₀ 0).r = b - op A x₀ := rfl

/-- Algorithm 8.5, line 1: `p_0 = Aᴴ r_0`. -/
@[simp] theorem cgne_zero_p : (cgne A b x₀ 0).p = op Aᴴ (b - op A x₀) := rfl

/-! #### The bridge to the backbone CGNE recurrence -/

variable {A}

private theorem cgneStepAlpha_eq (s : Krylov.CGNE.State 𝔼) :
    cgneStepAlpha s = (Krylov.CGNE.alpha s : 𝕜) := by
  rw [cgneStepAlpha, Krylov.CGNE.alpha, inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K]

private theorem cgneStepR_eq (s : Krylov.CGNE.State 𝔼) :
    cgneStepR A s = (Krylov.CGNE.step (op A) (op Aᴴ) s).r := by
  rw [cgneStepR, cgneStepAlpha_eq, Krylov.CGNE.step_r]

private theorem cgneStepBeta_eq (s : Krylov.CGNE.State 𝔼) :
    cgneStepBeta A s = Krylov.CGNE.beta (op A) (op Aᴴ) s := by
  rw [cgneStepBeta, Krylov.CGNE.beta, cgneStepR_eq, inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K]

private theorem cgneStep_eq (s : Krylov.CGNE.State 𝔼) :
    cgneStep A s = Krylov.CGNE.step (op A) (op Aᴴ) s := by
  have h : cgneStep A s =
      { x := s.x + cgneStepAlpha s • s.p
        r := cgneStepR A s
        p := op Aᴴ (cgneStepR A s) + cgneStepBeta A s • s.p } := rfl
  rw [h, cgneStepAlpha_eq, cgneStepR_eq, cgneStepBeta_eq]
  rfl

/-- Algorithm 8.5 is the backbone CGNE recurrence for the pair `(A, Aᴴ)`. -/
theorem cgne_eq_iterate (i : ℕ) :
    cgne A b x₀ i = Krylov.CGNE.iterate (op A) (op Aᴴ) b x₀ i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [cgne_succ, ih, cgneStep_eq, Krylov.CGNE.iterate_succ]

/-- **Saad, Algorithm 8.5**: Craig's method is the conjugate gradient method for
`A Aᴴ u = b` read in the variable `x = Aᴴ u`. For any `u_0` with `Aᴴ u_0 = x_0` the iterate is
`x_i = x_0 + Aᴴ (u_i - u_0)`, the search direction is `Aᴴ` of the conjugate gradient direction,
and the two residuals agree — so no vector of the `u`-iteration is ever formed. -/
theorem cgne_eq {u₀ : EuclideanSpace 𝕜 (Fin n)} (hu₀ : op Aᴴ u₀ = x₀) (i : ℕ) :
    (cgne A b x₀ i).x = x₀ + op Aᴴ ((CG.iterate (op A ∘ₗ op Aᴴ) b u₀ i).x - u₀) ∧
      (cgne A b x₀ i).r = (CG.iterate (op A ∘ₗ op Aᴴ) b u₀ i).r ∧
      (cgne A b x₀ i).p = op Aᴴ (CG.iterate (op A ∘ₗ op Aᴴ) b u₀ i).p := by
  obtain ⟨hx, hr, hp⟩ :=
    Krylov.CGNE.iterate_eq (op A) (op Aᴴ) b x₀ (inner_op_conjTranspose A) hu₀ i
  rw [cgne_eq_iterate]
  refine ⟨?_, hr, hp⟩
  rw [hx, map_sub, hu₀]
  abel

end CGNE

/-! ### The two optimality properties -/

section Optimality

variable {A : Matrix (Fin n) (Fin n) 𝕜} (b x₀ : EuclideanSpace 𝕜 (Fin n))

/-- **Saad §8.3.1**, the optimality of CGNR: `x_m` minimizes `‖b - A x‖₂` over
`x_0 + 𝒦_m(Aᴴ A, Aᴴ r_0)`. It is the same minimization GMRES performs, over a different
subspace. -/
theorem cgnr_isMinRes (hA : Function.Injective (op A)) (m : ℕ) :
    IsMinRes (op A) b x₀ (Chapter06.krylov (Aᴴ * A) (op Aᴴ (b - op A x₀)) m) (cgnr A b x₀ m).x := by
  have hgal := CG.isGalerkinIterate (op Aᴴ b) x₀ (isSymmetricCoercive_normal hA) m
  rw [cgnr_eq, krylov_conjTranspose_mul]
  exact (Krylov.isGalerkinIterate_adjoint_comp_iff_isMinRes (inner_op_conjTranspose A) b x₀ m
    _).1 hgal

/-- **Saad §8.3.2**, the optimality of CGNE: `x_m` minimizes the *error* `‖x_* - x‖₂` over the
same affine subspace `x_0 + 𝒦_m(Aᴴ A, Aᴴ r_0)` that CGNR minimizes the residual over
(`subspace_adjoint_eq`). -/
theorem cgne_isMinError (hA : Function.Injective (op Aᴴ))
    {u₀ xstar : EuclideanSpace 𝕜 (Fin n)} (hu₀ : op Aᴴ u₀ = x₀) (hstar : op A xstar = b)
    (m : ℕ) :
    IsMinError xstar x₀ (Chapter06.krylov (Aᴴ * A) (op Aᴴ (b - op A x₀)) m) (cgne A b x₀ m).x := by
  have hgal := CG.isGalerkinIterate b u₀ (isSymmetricCoercive_normal' hA) m
  rw [(cgne_eq b x₀ hu₀ m).1, krylov_conjTranspose_mul]
  exact Krylov.isMinError_of_isGalerkinIterate_comp_adjoint (inner_op_conjTranspose A) b x₀
    hu₀.symm hstar hgal

/-- **Saad §8.3**, the section's closing observation: `Aᴴ 𝒦_m(A Aᴴ, r_0) = 𝒦_m(Aᴴ A, Aᴴ r_0)`.
CGNR and CGNE draw their approximations from the same affine subspace and differ only in what
they minimize over it. -/
theorem subspace_adjoint_eq (A : Matrix (Fin n) (Fin n) 𝕜) (r₀ : EuclideanSpace 𝕜 (Fin n))
    (m : ℕ) :
    (Chapter06.krylov (A * Aᴴ) r₀ m).map (op Aᴴ) = Chapter06.krylov (Aᴴ * A) (op Aᴴ r₀) m := by
  rw [krylov_conjTranspose_mul, krylov_conjTranspose_mul]
  exact Krylov.map_subspace_comp (op A) (op Aᴴ) r₀ m

/-- **Saad §8.3**, the quantitative form of the warning of (8.8): the conjugate gradient bound
transported to CGNR. With the singular values of `A` in `[σ_min, σ_max]`,
`‖b - A x_m‖₂ ≤ 2 ((κ - 1)/(κ + 1))^m ‖b - A x_0‖₂` for `κ = σ_max/σ_min = κ₂(A)`. The condition
number that appears is that of `Aᴴ A`, whose square root is `κ₂(A)`; that squaring is why the
chapter prefers methods which do not pass through the normal equations. -/
theorem cgnr_norm_residual_le {smin smax : ℝ} (hs : 0 < smin) (hss : smin ≤ smax)
    (hmin : ∀ x : EuclideanSpace 𝕜 (Fin n), smin * ‖x‖ ≤ ‖op A x‖)
    (hmax : ∀ x : EuclideanSpace 𝕜 (Fin n), ‖op A x‖ ≤ smax * ‖x‖)
    {xstar : EuclideanSpace 𝕜 (Fin n)} (hstar : op A xstar = b)
    (hA : Function.Injective (op A)) (m : ℕ) :
    ‖b - op A (cgnr A b x₀ m).x‖
      ≤ 2 * ((smax / smin - 1) / (smax / smin + 1)) ^ m * ‖b - op A x₀‖ := by
  have hB : (op Aᴴ ∘ₗ op A).IsSymmetricBoundedBy (smin ^ 2) (smax ^ 2) :=
    Krylov.adjoint_comp_isSymmetricBoundedBy (inner_op_conjTranspose A)
      (fun x => by
        nlinarith [hmin x, norm_nonneg (op A x), mul_nonneg hs.le (norm_nonneg x)])
      (fun x => by nlinarith [hmax x, norm_nonneg (op A x), norm_nonneg x])
  have hx := cgnr_isMinRes b x₀ hA m
  rw [krylov_conjTranspose_mul] at hx
  exact Krylov.IsMinRes.norm_residual_le_of_adjoint_comp (inner_op_conjTranspose A) hs hss hB
    hstar hx

end Optimality

end SaadSparse.Chapter08

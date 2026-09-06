import Numlib.Krylov.CGW
import NumlibSurface.SaadSparse.Chapter01.Section11
import NumlibSurface.SaadSparse.Chapter09.Section02

/-!
# Saad §9.6: the Concus–Golub–Widlund algorithm

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §9.6.

For a nearly symmetric `A`, precondition with its Hermitian part `M = (A + Aᴴ)/2` (`cgwM`) and
write `A = M - N` with `N = M - A = (Aᴴ - A)/2` (`cgwN`) skew-Hermitian.  Then
`M⁻¹ A = I - M⁻¹ N` where `M⁻¹ N` is *skew*-adjoint for the `M`-inner product
(`isSkewAdjoint_energy`), so the adjoint of `M⁻¹ A` in that inner product is `2 I - M⁻¹ A`
(`adjoint_energyEnd`).

Two consequences make the algorithm short-recurrence.  The Arnoldi process for `M⁻¹ A` in the
`M`-inner product has a *tridiagonal* Hessenberg matrix — that is
`Arnoldi.coeff_eq_zero_of_adjoint_mem` with `s = 2`, since `2 v - M⁻¹ A v` lies in
`span {v, M⁻¹ A v}` — and its entries satisfy `h_ij + conj h_ji = 2 (v_i, v_j)_M`, so the
diagonal is `1` and the two off-diagonals are `η_{j+1}` and `-conj η_{j+1}`.  That is (9.29),
`equation_9_29`.

`cgw` is the resulting algorithm: Algorithm 9.1 with the sign of `β_j` reversed
(`cgw_alpha`).

`cgw_isGalerkinIterate` is the only optimality property the algorithm has: the iterate is the
Galerkin (FOM) iterate of `M⁻¹ A x = M⁻¹ b` in the `M`-inner product.  It comes from the backbone
recurrence `Numlib/Krylov/CGW.lean` for an operator of the shape "identity plus skew-adjoint",
through the bridge `cgw_eq_CGW_iterate`; the hypothesis that backbone theory needs is exactly
`adjoint_energyEnd`, here `isShiftedSkewAdjoint_energyEnd`.  No minimization is claimed, because
`M⁻¹ A` is not `M`-self-adjoint.

## The real field

The Galerkin property is stated over `ℝ`, and over `ℂ` it is false: the step length `α_j` is then
genuinely complex — the quadratic form of a skew-adjoint operator is purely imaginary rather than
zero — and the cancellation that makes the search directions `M⁻¹A`-conjugate already fails at
`j = 1`.  The rest of the section, including (9.29), holds over any `RCLike` field.  See the module
documentation of `Numlib/Krylov/CGW.lean`.

## Not formalized here

The inner-outer variants of Golub and Overton mentioned in the notes of §9.6 carry no statement
in the book and are not formalized.
-/

open Matrix

open scoped ComplexOrder SaadSparse

namespace SaadSparse.Chapter09

open Chapter06 (op)

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-! ### §9.6: the splitting `A = M - N` -/

/-- §9.6: the preconditioner of the Concus–Golub–Widlund algorithm, the Hermitian part
`M = (A + Aᴴ)/2` of a nearly symmetric `A`. -/
noncomputable def cgwM (A : Matrix (Fin n) (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜 :=
  Matrix.hermitianPart A

/-- §9.6: the skew-Hermitian part `N = M - A = (Aᴴ - A)/2` of the splitting `A = M - N`. -/
noncomputable def cgwN (A : Matrix (Fin n) (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜 :=
  cgwM A - A

variable {A : Matrix (Fin n) (Fin n) 𝕜}

/-- §9.6: `A = M - N`. -/
theorem cgwM_sub_cgwN (A : Matrix (Fin n) (Fin n) 𝕜) : cgwM A - cgwN A = A := by
  rw [cgwN, sub_sub_cancel]

/-- The preconditioner of §9.6 is Hermitian. -/
theorem cgwM_isHermitian (A : Matrix (Fin n) (Fin n) 𝕜) : (cgwM A).IsHermitian :=
  Matrix.hermitianPart_isHermitian A

/-- `N = (Aᴴ - A)/2`. -/
theorem cgwN_eq (A : Matrix (Fin n) (Fin n) 𝕜) : cgwN A = (2⁻¹ : 𝕜) • (Aᴴ - A) := by
  have h : cgwM A = (2⁻¹ : 𝕜) • (A + Aᴴ) := rfl
  rw [cgwN, h]
  match_scalars <;> ring

/-- §9.6: `N` is skew-Hermitian, `Nᴴ = -N`. -/
theorem cgwN_conjTranspose (A : Matrix (Fin n) (Fin n) 𝕜) : (cgwN A)ᴴ = -cgwN A := by
  rw [cgwN_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_conjTranspose, ← neg_sub Aᴴ A, smul_neg,
    show star (2⁻¹ : 𝕜) = 2⁻¹ by simp]

/-! ### §9.6: skew-adjointness in the `M`-inner product -/

section Energy

variable {M : Matrix (Fin n) (Fin n) 𝕜}

/-- §9.6: for a skew-Hermitian `N`, `M⁻¹ N` is skew-adjoint for the `M`-inner product,
`(M⁻¹ N x, y)_M = -(x, M⁻¹ N y)_M`. -/
theorem isSkewAdjoint_energy {N : Matrix (Fin n) (Fin n) 𝕜} (hN : Nᴴ = -N)
    (hM : Krylov.IsPreconditioner (op M) (op M⁻¹)) (u v : hM.EnergySpace) :
    inner 𝕜 (hM.energyEnd (op M⁻¹ ∘ₗ op N) u) v
      = -inner 𝕜 u (hM.energyEnd (op M⁻¹ ∘ₗ op N) v) := by
  obtain ⟨x, rfl⟩ := hM.toEnergy.surjective u
  obtain ⟨y, rfl⟩ := hM.toEnergy.surjective v
  rw [hM.inner_energyEnd_left (op N), hM.inner_energyEnd_right (op N),
    inner_op_conjTranspose N x y, hN]
  have hneg : (op (-N) : 𝔼 →ₗ[𝕜] 𝔼) = -op N := map_neg Matrix.toEuclideanLin N
  rw [hneg, LinearMap.neg_apply, inner_neg_right]

/-- §9.6: `M⁻¹ A = I - M⁻¹ N`, read in the `M`-inner product. -/
theorem energyEnd_eq_one_sub (hM : Krylov.IsPreconditioner (op (cgwM A)) (op (cgwM A)⁻¹))
    (u : hM.EnergySpace) :
    hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A) u
      = u - hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op (cgwN A)) u := by
  obtain ⟨x, rfl⟩ := hM.toEnergy.surjective u
  have hA : (op A : 𝔼 →ₗ[𝕜] 𝔼) x = op (cgwM A) x - op (cgwN A) x := by
    rw [← LinearMap.sub_apply, ← map_sub, cgwM_sub_cgwN]
  rw [Krylov.IsPreconditioner.energyEnd_apply, Krylov.IsPreconditioner.energyEnd_apply,
    ← map_sub]
  congr 1
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hA, map_sub, hM.inv_apply]

/-- §9.6: the adjoint of `M⁻¹ A` in the `M`-inner product is `2 I - M⁻¹ A`.  This is the one
fact the whole section rests on: it is what makes the Hessenberg matrix of the `M`-orthogonal
Arnoldi process tridiagonal. -/
theorem adjoint_energyEnd (hM : Krylov.IsPreconditioner (op (cgwM A)) (op (cgwM A)⁻¹))
    (u v : hM.EnergySpace) :
    inner 𝕜 (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A) u) v
      = inner 𝕜 u ((2 : 𝕜) • v - hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A) v) := by
  have hskew := isSkewAdjoint_energy (cgwN_conjTranspose A) hM
  have hone := energyEnd_eq_one_sub (A := A) hM
  rw [hone u, inner_sub_left, hskew u v]
  have hv : hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op (cgwN A)) v
      = v - hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A) v := by
    rw [hone v]; abel
  rw [hv, inner_sub_right, inner_sub_right, two_smul, inner_add_right]
  ring

end Energy

/-! ### (9.29): the tridiagonal Hessenberg matrix of the `M`-orthogonal Arnoldi process -/

/-- **(9.29)**: the Hessenberg matrix of the Arnoldi process for `M⁻¹ A` in the `M`-inner
product is tridiagonal with unit diagonal.

* the first clause is tridiagonality — `h_ij = 0` whenever `j ≥ i + 2`, which with the
  Hessenberg structure leaves only the three central diagonals;
* the second is `h_ij + conj h_ji = 2 (v_i, v_j)_M`, so the superdiagonal entry is minus the
  conjugate of the subdiagonal one, `-conj η_{j+1}` against `η_{j+1}`;
* the third is the unit diagonal `re h_ii = 1` for the vectors the process actually
  produces — over `ℝ` that is Saad's `h_ii = 1`. -/
theorem equation_9_29 (hM : Krylov.IsPreconditioner (op (cgwM A)) (op (cgwM A)⁻¹))
    (b : hM.EnergySpace) :
    (∀ i j : ℕ, i + 2 ≤ j →
        Arnoldi.coeff (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) b i j = 0) ∧
      (∀ i j : ℕ,
        Arnoldi.coeff (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) b i j
            + starRingEnd 𝕜 (Arnoldi.coeff (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) b j i)
          = 2 * inner 𝕜 (Arnoldi.vec (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) b i)
              (Arnoldi.vec (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) b j)) ∧
      (∀ i : ℕ, i < Krylov.grade (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) b →
        RCLike.re (Arnoldi.coeff (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) b i i) = 1) := by
  have hadj := adjoint_energyEnd (A := A) hM
  have hband : ∀ i j : ℕ, i + 2 ≤ j →
      Arnoldi.coeff (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) b i j = 0 := by
    intro i j hij
    refine Arnoldi.coeff_eq_zero_of_adjoint_mem _ b
      (B := (2 : 𝕜) • (LinearMap.id : hM.EnergySpace →ₗ[𝕜] hM.EnergySpace)
        - hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) (fun x y => ?_) (s := 2) (fun v => ?_) hij
    · rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
      exact hadj x y
    · have h0 : v ∈ Krylov.subspace (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) v 2 :=
        Krylov.self_mem_subspace _ v (by omega)
      have h1 : hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A) v
          ∈ Krylov.subspace (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) v 2 := by
        have h := Krylov.pow_apply_mem_subspace
          (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) v (i := 1) (m := 2) (by omega)
        simpa using h
      rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ h0) h1
  have hsum : ∀ i j : ℕ,
      Arnoldi.coeff (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) b i j
          + starRingEnd 𝕜 (Arnoldi.coeff (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) b j i)
        = 2 * inner 𝕜 (Arnoldi.vec (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) b i)
            (Arnoldi.vec (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) b j) := by
    intro i j
    rw [Arnoldi.coeff, Arnoldi.coeff, inner_conj_symm, hadj, inner_sub_right,
      inner_smul_right]
    ring
  refine ⟨hband, hsum, fun i hi => ?_⟩
  have : FiniteDimensional 𝕜 hM.EnergySpace :=
    LinearEquiv.finiteDimensional (hM.toEnergy)
  have hnorm := Arnoldi.norm_vec_eq_one_of_lt_grade
    (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) b hi
  have h := hsum i i
  rw [inner_self_eq_norm_sq_to_K, hnorm] at h
  have h2 : (2 : 𝕜) * (RCLike.re (Arnoldi.coeff
      (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) b i i) : 𝕜) = 2 * 1 := by
    rw [← RCLike.add_conj]
    simpa using h
  have h3 : ((RCLike.re (Arnoldi.coeff (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) b i i) : ℝ) : 𝕜)
      = ((1 : ℝ) : 𝕜) := by
    have := mul_left_cancel₀ (a := (2 : 𝕜)) (by norm_num) h2
    simpa using this
  exact_mod_cast h3

/-! ### The algorithm -/

section Algorithm

variable (A M : Matrix (Fin n) (Fin n) 𝕜)

/-- One pass through the Concus–Golub–Widlund recurrence: **Algorithm 9.1** with the sign of
`β_j` reversed, `p_{j+1} = z_{j+1} - β_j p_j`. -/
noncomputable def cgwStep (s : 𝔼 × 𝔼 × 𝔼) : 𝔼 × 𝔼 × 𝔼 :=
  (s.1 + pcgStepAlpha A M s • s.2.2, pcgStepR A M s,
    op M⁻¹ (pcgStepR A M s) - pcgStepBeta A M s • s.2.2)

variable (b x₀ : EuclideanSpace 𝕜 (Fin n))

/-- **The Concus–Golub–Widlund algorithm** run for `j` steps, preconditioned by the Hermitian
part `M = (A + Aᴴ)/2` of `A`: the triple `(x_j, r_j, p_j)`, started from `r_0 = b - A x_0` and
`p_0 = z_0 = M⁻¹ r_0`. -/
noncomputable def cgw (j : ℕ) : 𝔼 × 𝔼 × 𝔼 :=
  (cgwStep A (cgwM A))^[j] (x₀, b - op A x₀, op (cgwM A)⁻¹ (b - op A x₀))

/-- The `j`-th CGW iterate `x_j`. -/
noncomputable def cgwX (j : ℕ) : 𝔼 := (cgw A b x₀ j).1

/-- The `j`-th CGW residual `r_j`. -/
noncomputable def cgwR (j : ℕ) : 𝔼 := (cgw A b x₀ j).2.1

/-- The `j`-th CGW search direction `p_j`. -/
noncomputable def cgwP (j : ℕ) : 𝔼 := (cgw A b x₀ j).2.2

/-- The `j`-th preconditioned CGW residual `z_j = M⁻¹ r_j`. -/
noncomputable def cgwZ (j : ℕ) : 𝔼 := op (cgwM A)⁻¹ (cgwR A b x₀ j)

/-- The CGW step length `α_j`. -/
noncomputable def cgwAlpha (j : ℕ) : 𝕜 := pcgStepAlpha A (cgwM A) (cgw A b x₀ j)

/-- The CGW direction coefficient `β_j`, the negative of Algorithm 9.1's. -/
noncomputable def cgwBeta (j : ℕ) : 𝕜 := -pcgStepBeta A (cgwM A) (cgw A b x₀ j)

/-- The recurrence: state `j + 1` is one pass of the CGW step applied to state `j`. -/
theorem cgw_succ (j : ℕ) : cgw A b x₀ (j + 1) = cgwStep A (cgwM A) (cgw A b x₀ j) :=
  Function.iterate_succ_apply' _ _ _

/-- The iteration starts at `x_0`. -/
@[simp] theorem cgwX_zero : cgwX A b x₀ 0 = x₀ := rfl

/-- `r_0 = b - A x_0`. -/
@[simp] theorem cgwR_zero : cgwR A b x₀ 0 = b - op A x₀ := rfl

/-- `p_0 = z_0 = M⁻¹ r_0`. -/
@[simp] theorem cgwP_zero : cgwP A b x₀ 0 = cgwZ A b x₀ 0 := rfl

/-- The CGW iterate update `x_{j+1} = x_j + α_j p_j`. -/
theorem cgwX_succ (j : ℕ) :
    cgwX A b x₀ (j + 1) = cgwX A b x₀ j + cgwAlpha A b x₀ j • cgwP A b x₀ j := by
  rw [cgwX, cgw_succ]; rfl

/-- The CGW residual update `r_{j+1} = r_j - α_j A p_j`. -/
theorem cgwR_succ (j : ℕ) :
    cgwR A b x₀ (j + 1) = cgwR A b x₀ j - cgwAlpha A b x₀ j • op A (cgwP A b x₀ j) := by
  rw [cgwR, cgw_succ]; rfl

private theorem cgwR_succ_eq (j : ℕ) :
    cgwR A b x₀ (j + 1) = pcgStepR A (cgwM A) (cgw A b x₀ j) := by
  rw [cgwR, cgw_succ]; rfl

/-- The CGW direction update `p_{j+1} = z_{j+1} + β_j p_j`, with `β_j` the *negative* of the
coefficient of Algorithm 9.1. -/
theorem cgwP_succ (j : ℕ) :
    cgwP A b x₀ (j + 1) = cgwZ A b x₀ (j + 1) + cgwBeta A b x₀ j • cgwP A b x₀ j := by
  rw [cgwBeta, neg_smul, ← sub_eq_add_neg, cgwZ, cgwR_succ_eq, cgwP, cgw_succ]
  rfl

/-- The CGW state's residual field is the true residual `b - A x_j`.  This is the first step of
the induction that would identify the CGW iterate with the Galerkin iterate. -/
theorem cgw_residual_eq (j : ℕ) : cgwR A b x₀ j = b - op A (cgwX A b x₀ j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [cgwR_succ, cgwX_succ, ih, map_add, map_smul]
      abel

/-- **§9.6**: the coefficients of the Concus–Golub–Widlund algorithm.  The step length is that
of Algorithm 9.1, `α_j = (r_j, z_j)/(A p_j, p_j)`, and the direction coefficient is its
negative, `β_j = -(z_{j+1}, r_{j+1})/(z_j, r_j)`; the sign is the one skew-adjointness of
`M⁻¹ N` forces, through `(M⁻¹ A z_{j+1}, p_j)_M = -(z_{j+1}, M⁻¹ A p_j)_M`. -/
theorem cgw_alpha (j : ℕ) :
    cgwAlpha A b x₀ j
        = inner 𝕜 (cgwZ A b x₀ j) (cgwR A b x₀ j)
            / inner 𝕜 (cgwP A b x₀ j) (op A (cgwP A b x₀ j))
      ∧ cgwBeta A b x₀ j
        = -(inner 𝕜 (cgwZ A b x₀ (j + 1)) (cgwR A b x₀ (j + 1))
            / inner 𝕜 (cgwZ A b x₀ j) (cgwR A b x₀ j)) := by
  refine ⟨rfl, ?_⟩
  rw [cgwBeta, pcgStepBeta_def, cgwZ, cgwZ, cgwR_succ_eq]
  rfl

end Algorithm

/-! ### The Galerkin property of the Concus–Golub–Widlund iterate (real case) -/

section Galerkin

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}

/-- **§9.6 read as the hypothesis of the backbone recurrence**: in the `M`-inner product `M⁻¹ A` is
*shifted skew-adjoint*, `B + B* = 2`.  This is `adjoint_energyEnd` over the reals. -/
theorem isShiftedSkewAdjoint_energyEnd
    (hM : Krylov.IsPreconditioner (op (cgwM A)) (op (cgwM A)⁻¹)) :
    (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)).IsShiftedSkewAdjoint := by
  intro u v
  have h := adjoint_energyEnd (A := A) hM u v
  rw [inner_sub_right, real_inner_smul_right] at h
  linarith

/-- **The Concus–Golub–Widlund recurrence is the backbone `CGW.iterate`** of `M⁻¹ A` in the
`M`-inner product: the iterate and the search direction transport unchanged, and what plays the
part of the backbone residual is the *preconditioned* residual `z_j = M⁻¹ r_j`. -/
theorem cgw_eq_CGW_iterate (hM : Krylov.IsPreconditioner (op (cgwM A)) (op (cgwM A)⁻¹))
    (b x₀ : EuclideanSpace ℝ (Fin n)) (j : ℕ) :
    hM.toEnergy (cgwX A b x₀ j)
        = (CGW.iterate (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A))
            (hM.toEnergy (op (cgwM A)⁻¹ b)) (hM.toEnergy x₀) j).x ∧
      hM.toEnergy (cgwZ A b x₀ j)
        = (CGW.iterate (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A))
            (hM.toEnergy (op (cgwM A)⁻¹ b)) (hM.toEnergy x₀) j).r ∧
      hM.toEnergy (cgwP A b x₀ j)
        = (CGW.iterate (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A))
            (hM.toEnergy (op (cgwM A)⁻¹ b)) (hM.toEnergy x₀) j).p := by
  have hnum : ∀ k : ℕ,
      inner ℝ (hM.toEnergy (cgwZ A b x₀ k)) (hM.toEnergy (cgwZ A b x₀ k))
        = inner ℝ (op (cgwM A)⁻¹ (cgwR A b x₀ k)) (cgwR A b x₀ k) := by
    intro k
    rw [WithEnergy.inner_equiv, _root_.energyInner]
    simp only [cgwZ]
    rw [hM.apply_inv]
    exact real_inner_comm _ _
  have hBapply : ∀ y : EuclideanSpace ℝ (Fin n),
      hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A) (hM.toEnergy y)
        = hM.toEnergy (op (cgwM A)⁻¹ (op A y)) := by
    intro y
    rw [Krylov.IsPreconditioner.energyEnd_apply, LinearMap.comp_apply]
  have hinit : hM.toEnergy (op (cgwM A)⁻¹ (b - op A x₀))
      = hM.toEnergy (op (cgwM A)⁻¹ b)
        - hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A) (hM.toEnergy x₀) := by
    rw [hBapply, ← map_sub, ← map_sub]
  induction j with
  | zero => exact ⟨rfl, hinit, hinit⟩
  | succ j ih =>
    obtain ⟨hx, hr, hp⟩ := ih
    have halpha : cgwAlpha A b x₀ j
        = CGW.alpha (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A))
          (CGW.iterate (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A))
            (hM.toEnergy (op (cgwM A)⁻¹ b)) (hM.toEnergy x₀) j) := by
      rw [CGW.alpha, ← hr, ← hp, hnum j, hM.inner_energyEnd_right (op A)]
      rfl
    have hr' : hM.toEnergy (cgwZ A b x₀ (j + 1))
        = (CGW.iterate (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A))
            (hM.toEnergy (op (cgwM A)⁻¹ b)) (hM.toEnergy x₀) (j + 1)).r := by
      rw [CGW.iterate_succ_r, ← hr, ← hp, ← halpha, hBapply]
      simp only [cgwZ, cgwR_succ, map_sub, map_smul]
    have hbeta : cgwBeta A b x₀ j
        = CGW.beta (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A))
          (CGW.iterate (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A))
            (hM.toEnergy (op (cgwM A)⁻¹ b)) (hM.toEnergy x₀) j) := by
      rw [CGW.beta_iterate, ← hr', ← hr, hnum (j + 1), hnum j, cgwBeta, pcgStepBeta_def,
        ← cgwR_succ_eq]
      rfl
    refine ⟨?_, hr', ?_⟩
    · rw [CGW.iterate_succ_x, ← hx, ← hp, ← halpha, cgwX_succ, map_add, map_smul]
    · rw [CGW.iterate_succ_p, ← hr', ← hp, ← hbeta, cgwP_succ, map_add, map_smul]

/-- **The Concus–Golub–Widlund iterate is a Galerkin iterate**: it lies in
`x₀ + 𝒦_j(M⁻¹ A, M⁻¹ r₀)` and its residual is `M`-orthogonal to that space, so §9.6 is a
projection method for the preconditioned system `M⁻¹ A x = M⁻¹ b` in the `M`-inner product.  This
is the only optimality the algorithm has: no minimization comes with it, because `M⁻¹ A` is not
`M`-self-adjoint.

Over the reals only.  Over `ℂ` the recurrence is not a projection method — see the module
documentation of `Numlib/Krylov/CGW.lean`: the step length `α_j` is then genuinely complex and the
cancellation that makes the directions `B`-conjugate fails already at `j = 1`. -/
theorem cgw_isGalerkinIterate (hM : Krylov.IsPreconditioner (op (cgwM A)) (op (cgwM A)⁻¹))
    (b x₀ : EuclideanSpace ℝ (Fin n)) (j : ℕ) :
    IsGalerkin (op A) b x₀
      (Chapter06.krylov ((cgwM A)⁻¹ * A) (op (cgwM A)⁻¹ (b - op A x₀)) j) (cgwX A b x₀ j) := by
  have hgal : IsGalerkin (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A))
      (hM.toEnergy (op (cgwM A)⁻¹ b)) (hM.toEnergy x₀)
      (Krylov.subspace (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A))
        (hM.toEnergy (op (cgwM A)⁻¹ b)
          - hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A) (hM.toEnergy x₀)) j)
      (CGW.iterate (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A))
        (hM.toEnergy (op (cgwM A)⁻¹ b)) (hM.toEnergy x₀) j).x :=
    CGW.isGalerkinIterate (hM.toEnergy (op (cgwM A)⁻¹ b)) (hM.toEnergy x₀)
      (isShiftedSkewAdjoint_energyEnd hM) j
  rw [show hM.toEnergy (op (cgwM A)⁻¹ b)
        - hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A) (hM.toEnergy x₀)
      = hM.toEnergy (op (cgwM A)⁻¹ (b - op A x₀)) by
      rw [Krylov.IsPreconditioner.energyEnd_apply, LinearMap.comp_apply, ← map_sub, ← map_sub],
    hM.subspace_energyEnd, ← (cgw_eq_CGW_iterate hM b x₀ j).1] at hgal
  rw [Chapter06.krylov_eq, op_mul]
  exact (hM.isGalerkin_energyEnd_iff (op A) b x₀ _ _).1 hgal

end Galerkin


end SaadSparse.Chapter09

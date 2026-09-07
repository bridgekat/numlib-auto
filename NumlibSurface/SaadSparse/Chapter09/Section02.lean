import Numlib.Krylov.CR
import Numlib.Krylov.Preconditioned
import NumlibSurface.SaadSparse.Chapter04.Section01
import NumlibSurface.SaadSparse.Chapter06.Common
import NumlibSurface.SaadSparse.Chapter09.Section01

/-!
# Saad §9.2: the preconditioned conjugate gradient method

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §9.2, with P-9.2, P-9.3 and P-9.6.

The section rests on one observation, `isSymmetric_energy`: for symmetric `A` and symmetric
positive definite `M`, the preconditioned matrix `M⁻¹ A` is self-adjoint for the `M`-inner
product `(x, y)_M = (M x, y)`, although it is not for the Euclidean one. CG may therefore be run
in that inner product, and — this is what makes Algorithm 9.1 practical — none of its `M`-inner
products has to be formed: `(z_j, z_j)_M = (r_j, z_j)` and `(M⁻¹ A p_j, p_j)_M = (A p_j, p_j)`
are Euclidean (`energyInner_inv`, `energyInner_leftPreconditioned`).

**Algorithm 9.1** is `pcg`, identified with the backbone `Krylov.PCG.iterate` by `pcg_eq`; from
that identification `pcg_isGalerkinIterate` gives the Galerkin property over
`x₀ + 𝒦_j(M⁻¹ A, M⁻¹ r₀)` and `problem_9_6` (**P-9.6**) the Chebyshev bound with the condition
number of the generalized eigenvalue problem `A x = λ M x`.

**Algorithm 9.2** (split preconditioning, `M = L Lᴴ`) is `splitPcg`, and `splitPcg_eq_pcg` is the
section's "surprisingly, the iterates are identical" claim, proved by the change of variables
`r̂_j = L⁻¹ r_j`; `splitPcg_eq_cg` adds the other half of the same paragraph, that both are the CG
iterates of `Â u = L⁻¹ b` with `Â = L⁻¹ A L⁻ᴴ` read through `u = Lᴴ x`. **P-9.3** is
`splitPcg_eq_pcg` in the other direction. `rightPcg_eq_pcg` is the closing paragraph of §9.2.1:
CG for the right-preconditioned system `A M⁻¹ u = b` in the `M⁻¹`-inner product, written in
`x = M⁻¹ u`, is Algorithm 9.1 verbatim.

**P-9.2** is `pcgEnergyA`, the analogue of Algorithm 9.1 in the `A`-inner product with one
matrix-vector product per step; `pcgEnergyA_isGalerkinIterate` identifies its iterates as the
minimal-`A M⁻¹ A`-error iterates over the same preconditioned Krylov space, so it is the
preconditioned conjugate residual method.

**P-9.12** is `pcr`, the analogue of Algorithm 9.1 for the conjugate residual method, and
`pcr_eq` is the same one-line reading as `pcg_eq`: it is `CR.iterate` for `M⁻¹ A` in the
`M`-inner product. `pcr_residual_eq` says its second component is `M⁻¹ r_j`.

Eisenstat's implementation (§9.2.2) is present as mathematics only:
`leftPreconditioned_apply_eq_add` is the opening observation `M⁻¹ A v = v + M⁻¹ R v` for
`M = A - R`, `equation_9_8` is the matrix identity behind the implementation and `eisenstat` is
**Algorithm 9.3**, with `eisenstat_eq` saying that it computes `Â v`. `problem_9_8c` is
**P-9.8 (c)**, the same identity conjugated by `D^{1/2}`: after that symmetric scaling the two
triangular factors are transposes of each other with a unit diagonal, and the matrix "to be
determined" is `D₂ = D^{-1/2} D₁ D^{-1/2}`, which for the SSOR choice `D = D₀` is `-I`
(`problem_9_8c_ssor`). The operation counts, P-9.7, P-9.9 and P-9.8 (a), (b) are not formalized,
as `plans/NumlibSurface/SaadSparse/Chapter09/Section02.toml` records.

Indices are `0`-based, and division by a vanishing quantity is `0`, which reproduces the book's
breakdown behaviour.
-/

open Matrix

open scoped ComplexOrder Matrix SaadSparse

namespace SaadSparse.Chapter09

open Chapter06 (op)

section General

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-! ### Preliminaries: adjoints, products and preconditioners -/

/-- `(B x, y) = (x, Bᴴ y)`: the conjugate transpose acts as the adjoint. -/
theorem inner_op_conjTranspose (B : Matrix (Fin n) (Fin n) 𝕜) (x y : 𝔼) :
    inner 𝕜 (op B x) y = inner 𝕜 x (op Bᴴ y) := by
  have hadj : (op Bᴴ) = LinearMap.adjoint (op B) := Matrix.toEuclideanLin_conjTranspose B
  rw [hadj, LinearMap.adjoint_inner_right]

/-- A matrix product acts as the composite of the two actions. -/
theorem op_mul (B C : Matrix (Fin n) (Fin n) 𝕜) : op (B * C) = op B ∘ₗ op C :=
  Matrix.toEuclideanLin_mul B C

/-- A matrix product acts on a vector as the composite of the two actions. -/
theorem op_mul_apply (B C : Matrix (Fin n) (Fin n) 𝕜) (x : 𝔼) : op (B * C) x = op B (op C x) := by
  rw [op_mul]; rfl

/-- A Hermitian matrix is a symmetric operator. -/
theorem isSymmetric_op {B : Matrix (Fin n) (Fin n) 𝕜} (hB : B.IsHermitian) :
    (op B).IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.2 hB

/-- The inverse of a symmetric positive definite matrix is symmetric positive definite, so it
too defines an inner product; this is the `M⁻¹`-inner product of §9.2.1. -/
theorem posDef_inv {M : Matrix (Fin n) (Fin n) 𝕜} (hM : M.PosDef) : M⁻¹.PosDef :=
  hM.inv

/-- **§9.2.1**: a symmetric positive definite `M` is a preconditioner in the backbone's sense —
`op M⁻¹` is a two-sided linear inverse of the symmetric coercive `op M`. -/
theorem isPreconditioner {M : Matrix (Fin n) (Fin n) 𝕜} (hM : M.PosDef) :
    Krylov.IsPreconditioner (op M) (op M⁻¹) where
  isSymmetricCoercive := (Matrix.posDef_iff_isSymmetricCoercive M).1 hM
  apply_inv x := by
    have h1 : op M ∘ₗ op M⁻¹ = LinearMap.id := by
      rw [← op_mul, Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det M).1 hM.isUnit)]
      exact Matrix.toEuclideanLin_one
    exact DFunLike.congr_fun h1 x

/-! ### §9.2.1: the three self-adjointness observations -/

variable {A M : Matrix (Fin n) (Fin n) 𝕜}

/-- **§9.2.1**: `M⁻¹ A` is self-adjoint for the `M`-inner product `(x, y)_M = (M x, y)`, which
is what lets the conjugate gradient method be run on the preconditioned system even though
`M⁻¹ A` is not symmetric in the Euclidean inner product. -/
theorem isSymmetric_energy (hA : (op A).IsSymmetric)
    (hM : Krylov.IsPreconditioner (op M) (op M⁻¹)) :
    (hM.energyEnd (op M⁻¹ ∘ₗ op A)).IsSymmetric := by
  intro u v
  obtain ⟨x, rfl⟩ := hM.toEnergy.surjective u
  obtain ⟨y, rfl⟩ := hM.toEnergy.surjective v
  rw [hM.inner_energyEnd_left (op A), hM.inner_energyEnd_right (op A), hA]

/-- **§9.2.1**: `(M⁻¹ A x, y)_M = (A x, y)`, the identity that keeps the `M`-inner products out
of Algorithm 9.1. -/
theorem energyInner_leftPreconditioned (hM : Krylov.IsPreconditioner (op M) (op M⁻¹)) (x y : 𝔼) :
    energyInner (op M) (op M⁻¹ (op A x)) y = inner 𝕜 (op A x) y := by
  rw [energyInner, hM.apply_inv]

/-- **§9.2.1**: `(M⁻¹ x, M⁻¹ y)_M = (x, M⁻¹ y)`; with `x = y = r_j` this is
`(z_j, z_j)_M = (r_j, z_j)`, the numerator of Algorithm 9.1, line 3. -/
theorem energyInner_inv (hM : Krylov.IsPreconditioner (op M) (op M⁻¹)) (x y : 𝔼) :
    energyInner (op M) (op M⁻¹ x) (op M⁻¹ y) = inner 𝕜 x (op M⁻¹ y) := by
  rw [energyInner, hM.apply_inv]

/-- **P-9.2(a)**: for positive definite `A`, `M⁻¹ A` is self-adjoint for the `A`-inner product
too. This is the observation Algorithm `pcgEnergyA` rests on. -/
theorem isSymmetric_energyA (hA : (op A).IsSymmetric)
    (hMinv : (op M⁻¹).IsSymmetric) (hAp : Krylov.IsPreconditioner (op A) (op A⁻¹)) :
    (hAp.energyEnd (op M⁻¹ ∘ₗ op A)).IsSymmetric := by
  intro u v
  obtain ⟨x, rfl⟩ := hAp.toEnergy.surjective u
  obtain ⟨y, rfl⟩ := hAp.toEnergy.surjective v
  rw [Krylov.IsPreconditioner.energyEnd_apply, Krylov.IsPreconditioner.energyEnd_apply,
    WithEnergy.inner_equiv, WithEnergy.inner_equiv, energyInner, energyInner,
    LinearMap.comp_apply, LinearMap.comp_apply, hA]
  exact hMinv _ _

/-- **§9.2.1**, closing paragraph: `A M⁻¹` is self-adjoint for the `M⁻¹`-inner product. This is
why right preconditioning in the `M⁻¹`-inner product is as legitimate as left preconditioning in
the `M`-inner product — and, by `rightPcg_eq_pcg`, the same method. -/
theorem isSymmetric_energyInv (hA : (op A).IsSymmetric)
    (hMi : Krylov.IsPreconditioner (op M⁻¹) (op M)) :
    (hMi.energyEnd (op A ∘ₗ op M⁻¹)).IsSymmetric := by
  intro u v
  obtain ⟨x, rfl⟩ := hMi.toEnergy.surjective u
  obtain ⟨y, rfl⟩ := hMi.toEnergy.surjective v
  rw [Krylov.IsPreconditioner.energyEnd_apply, Krylov.IsPreconditioner.energyEnd_apply,
    WithEnergy.inner_equiv, WithEnergy.inner_equiv, energyInner, energyInner,
    LinearMap.comp_apply, LinearMap.comp_apply, hMi.isSymmetricCoercive.isSymmetric]
  exact hA _ _

/-! ### Algorithm 9.1: the preconditioned conjugate gradient method -/

variable (A M : Matrix (Fin n) (Fin n) 𝕜)

/-- The step length `α_j = (r_j, z_j)/(A p_j, p_j)` of Algorithm 9.1, line 3, on the triple
`(x_j, r_j, p_j)`; the preconditioned residual `z_j = M⁻¹ r_j` is recomputed rather than
stored. -/
noncomputable def pcgStepAlpha (s : 𝔼 × 𝔼 × 𝔼) : 𝕜 :=
  inner 𝕜 (op M⁻¹ s.2.1) s.2.1 / inner 𝕜 s.2.2 (op A s.2.2)

/-- The next residual `r_{j+1} = r_j - α_j A p_j` of Algorithm 9.1, line 5. -/
noncomputable def pcgStepR (s : 𝔼 × 𝔼 × 𝔼) : 𝔼 := s.2.1 - pcgStepAlpha A M s • op A s.2.2

/-- The coefficient `β_j = (r_{j+1}, z_{j+1})/(r_j, z_j)` of Algorithm 9.1, line 7. -/
noncomputable def pcgStepBeta (s : 𝔼 × 𝔼 × 𝔼) : 𝕜 :=
  inner 𝕜 (op M⁻¹ (pcgStepR A M s)) (pcgStepR A M s) / inner 𝕜 (op M⁻¹ s.2.1) s.2.1

/-- One pass through lines 3–8 of **Algorithm 9.1**. -/
noncomputable def pcgStep (s : 𝔼 × 𝔼 × 𝔼) : 𝔼 × 𝔼 × 𝔼 :=
  (s.1 + pcgStepAlpha A M s • s.2.2, pcgStepR A M s,
    op M⁻¹ (pcgStepR A M s) + pcgStepBeta A M s • s.2.2)

/-- **Algorithm 9.1** (preconditioned conjugate gradient) run for `j` steps: the triple
`(x_j, r_j, p_j)`, started from `r_0 = b - A x_0` and `p_0 = z_0 = M⁻¹ r_0`. -/
noncomputable def pcg (b x₀ : 𝔼) (j : ℕ) : 𝔼 × 𝔼 × 𝔼 :=
  (pcgStep A M)^[j] (x₀, b - op A x₀, op M⁻¹ (b - op A x₀))

/-- The defining formula for `SaadSparse.Chapter09.pcgStepAlpha`, which the tuple
projections keep `rw` from unfolding on its own. -/
theorem pcgStepAlpha_def (s : 𝔼 × 𝔼 × 𝔼) :
    pcgStepAlpha A M s = inner 𝕜 (op M⁻¹ s.2.1) s.2.1 / inner 𝕜 s.2.2 (op A s.2.2) := rfl

/-- The defining formula for `SaadSparse.Chapter09.pcgStepR`. -/
theorem pcgStepR_def (s : 𝔼 × 𝔼 × 𝔼) :
    pcgStepR A M s = s.2.1 - pcgStepAlpha A M s • op A s.2.2 := rfl

/-- The defining formula for `SaadSparse.Chapter09.pcgStepBeta`. -/
theorem pcgStepBeta_def (s : 𝔼 × 𝔼 × 𝔼) : pcgStepBeta A M s =
    inner 𝕜 (op M⁻¹ (pcgStepR A M s)) (pcgStepR A M s) / inner 𝕜 (op M⁻¹ s.2.1) s.2.1 := rfl

variable (b x₀ : EuclideanSpace 𝕜 (Fin n))

/-- The `j`-th preconditioned conjugate gradient iterate `x_j` of Algorithm 9.1. -/
noncomputable def pcgX (j : ℕ) : 𝔼 := (pcg A M b x₀ j).1

/-- The `j`-th residual `r_j` of Algorithm 9.1. -/
noncomputable def pcgR (j : ℕ) : 𝔼 := (pcg A M b x₀ j).2.1

/-- The `j`-th search direction `p_j` of Algorithm 9.1. -/
noncomputable def pcgP (j : ℕ) : 𝔼 := (pcg A M b x₀ j).2.2

/-- The `j`-th preconditioned residual `z_j = M⁻¹ r_j` of Algorithm 9.1, line 6. -/
noncomputable def pcgZ (j : ℕ) : 𝔼 := op M⁻¹ (pcgR A M b x₀ j)

/-- The step length `α_j` of Algorithm 9.1 at step `j`. -/
noncomputable def pcgAlpha (j : ℕ) : 𝕜 := pcgStepAlpha A M (pcg A M b x₀ j)

/-- The direction coefficient `β_j` of Algorithm 9.1 at step `j`. -/
noncomputable def pcgBeta (j : ℕ) : 𝕜 := pcgStepBeta A M (pcg A M b x₀ j)

/-- The recurrence: state `j + 1` is one pass of Algorithm 9.1 applied to state `j`. -/
theorem pcg_succ (j : ℕ) : pcg A M b x₀ (j + 1) = pcgStep A M (pcg A M b x₀ j) :=
  Function.iterate_succ_apply' _ _ _

/-- Algorithm 9.1, line 1: the iteration starts at `x_0`. -/
@[simp] theorem pcgX_zero : pcgX A M b x₀ 0 = x₀ := rfl

/-- Algorithm 9.1, line 1: `r_0 = b - A x_0`. -/
@[simp] theorem pcgR_zero : pcgR A M b x₀ 0 = b - op A x₀ := rfl

/-- Algorithm 9.1, line 1: `p_0 = z_0`. -/
@[simp] theorem pcgP_zero : pcgP A M b x₀ 0 = pcgZ A M b x₀ 0 := rfl

/-- Algorithm 9.1, line 3: `α_j = (r_j, z_j)/(A p_j, p_j)`. -/
theorem pcgAlpha_eq (j : ℕ) : pcgAlpha A M b x₀ j =
    inner 𝕜 (pcgZ A M b x₀ j) (pcgR A M b x₀ j) /
      inner 𝕜 (pcgP A M b x₀ j) (op A (pcgP A M b x₀ j)) := rfl

/-- Algorithm 9.1, line 4: `x_{j+1} = x_j + α_j p_j`. -/
theorem pcgX_succ (j : ℕ) :
    pcgX A M b x₀ (j + 1) = pcgX A M b x₀ j + pcgAlpha A M b x₀ j • pcgP A M b x₀ j := by
  rw [pcgX, pcg_succ]; rfl

/-- Algorithm 9.1, line 5: `r_{j+1} = r_j - α_j A p_j`. -/
theorem pcgR_succ (j : ℕ) :
    pcgR A M b x₀ (j + 1) = pcgR A M b x₀ j - pcgAlpha A M b x₀ j • op A (pcgP A M b x₀ j) := by
  rw [pcgR, pcg_succ]; rfl

private theorem pcgR_succ_eq_pcgStepR (j : ℕ) :
    pcgR A M b x₀ (j + 1) = pcgStepR A M (pcg A M b x₀ j) := by
  rw [pcgR, pcg_succ]; rfl

/-- Algorithm 9.1, line 7: `β_j = (r_{j+1}, z_{j+1})/(r_j, z_j)`. -/
theorem pcgBeta_eq (j : ℕ) : pcgBeta A M b x₀ j =
    inner 𝕜 (pcgZ A M b x₀ (j + 1)) (pcgR A M b x₀ (j + 1)) /
      inner 𝕜 (pcgZ A M b x₀ j) (pcgR A M b x₀ j) := by
  rw [pcgBeta, pcgStepBeta_def, pcgZ, pcgZ, pcgR_succ_eq_pcgStepR]
  rfl

/-- Algorithm 9.1, line 8: `p_{j+1} = z_{j+1} + β_j p_j`. -/
theorem pcgP_succ (j : ℕ) :
    pcgP A M b x₀ (j + 1) = pcgZ A M b x₀ (j + 1) + pcgBeta A M b x₀ j • pcgP A M b x₀ j := by
  rw [pcgP, pcg_succ, pcgZ, pcgR_succ_eq_pcgStepR]
  rfl

/-! ### The bridge to the backbone preconditioned conjugate gradient recurrence -/

variable {A M}

private theorem pcgStepAlpha_eq_PCG (hA : (op A).IsSymmetric) (hMinv : (op M⁻¹).IsSymmetric)
    (s : Krylov.PCG.State 𝔼) :
    pcgStepAlpha A M (s.x, s.r, s.p) = Krylov.PCG.alpha (op A) (op M⁻¹) s := by
  rw [pcgStepAlpha_def, Krylov.PCG.alpha, hMinv s.r s.r, ← hA s.p s.p]

private theorem pcgStepR_eq_PCG (hA : (op A).IsSymmetric) (hMinv : (op M⁻¹).IsSymmetric)
    (s : Krylov.PCG.State 𝔼) :
    pcgStepR A M (s.x, s.r, s.p) = (Krylov.PCG.step (op A) (op M⁻¹) s).r := by
  rw [pcgStepR_def, pcgStepAlpha_eq_PCG hA hMinv s, Krylov.PCG.step_r]

private theorem pcgStepBeta_eq_PCG (hA : (op A).IsSymmetric) (hMinv : (op M⁻¹).IsSymmetric)
    (s : Krylov.PCG.State 𝔼) :
    pcgStepBeta A M (s.x, s.r, s.p) = Krylov.PCG.beta (op A) (op M⁻¹) s := by
  rw [pcgStepBeta_def, pcgStepR_eq_PCG hA hMinv s, Krylov.PCG.beta,
    hMinv (Krylov.PCG.step (op A) (op M⁻¹) s).r _, hMinv s.r s.r]

private theorem pcgStep_eq_PCG (hA : (op A).IsSymmetric) (hMinv : (op M⁻¹).IsSymmetric)
    (s : Krylov.PCG.State 𝔼) :
    pcgStep A M (s.x, s.r, s.p) = ((Krylov.PCG.step (op A) (op M⁻¹) s).x,
      (Krylov.PCG.step (op A) (op M⁻¹) s).r, (Krylov.PCG.step (op A) (op M⁻¹) s).p) := by
  rw [pcgStep, pcgStepAlpha_eq_PCG hA hMinv s, pcgStepR_eq_PCG hA hMinv s,
    pcgStepBeta_eq_PCG hA hMinv s, Krylov.PCG.step_x, Krylov.PCG.step_p]

/-- **The bridge to the backbone**: Algorithm 9.1 is the backbone preconditioned conjugate
gradient recurrence `Krylov.PCG.iterate`. Only the symmetry of `A` and of `M⁻¹` is needed, to
move each operator across the inner products of lines 3 and 7. -/
theorem pcg_eq (hA : (op A).IsSymmetric) (hMinv : (op M⁻¹).IsSymmetric) (b x₀ : 𝔼) (j : ℕ) :
    pcg A M b x₀ j = ((Krylov.PCG.iterate (op A) (op M⁻¹) b x₀ j).x,
      (Krylov.PCG.iterate (op A) (op M⁻¹) b x₀ j).r,
      (Krylov.PCG.iterate (op A) (op M⁻¹) b x₀ j).p) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pcg_succ, ih, Krylov.PCG.iterate_succ, pcgStep_eq_PCG hA hMinv]

/-- The iterate `x_j` of Algorithm 9.1 is the backbone one. -/
theorem pcgX_eq (hA : (op A).IsSymmetric) (hMinv : (op M⁻¹).IsSymmetric) (b x₀ : 𝔼) (j : ℕ) :
    pcgX A M b x₀ j = (Krylov.PCG.iterate (op A) (op M⁻¹) b x₀ j).x := by
  rw [pcgX, pcg_eq hA hMinv]

/-- The residual `r_j` of Algorithm 9.1 is the backbone one. -/
theorem pcgR_eq (hA : (op A).IsSymmetric) (hMinv : (op M⁻¹).IsSymmetric) (b x₀ : 𝔼) (j : ℕ) :
    pcgR A M b x₀ j = (Krylov.PCG.iterate (op A) (op M⁻¹) b x₀ j).r := by
  rw [pcgR, pcg_eq hA hMinv]

/-- The search direction `p_j` of Algorithm 9.1 is the backbone one. -/
theorem pcgP_eq (hA : (op A).IsSymmetric) (hMinv : (op M⁻¹).IsSymmetric) (b x₀ : 𝔼) (j : ℕ) :
    pcgP A M b x₀ j = (Krylov.PCG.iterate (op A) (op M⁻¹) b x₀ j).p := by
  rw [pcgP, pcg_eq hA hMinv]

/-- The state's residual is the true residual, `r_j = b - A x_j`. -/
theorem pcgR_eq_residual (hM : Krylov.IsPreconditioner (op M) (op M⁻¹))
    (hA : (op A).IsSymmetric) (b x₀ : 𝔼) (j : ℕ) :
    pcgR A M b x₀ j = b - op A (pcgX A M b x₀ j) := by
  rw [pcgR_eq hA hM.isSymmetric_inv, pcgX_eq hA hM.isSymmetric_inv,
    Krylov.PCG.residual_eq _ _ _ _ hM]

/-- **Algorithm 9.1 is a projection method**: its iterate is the Galerkin iterate of `A x = b`
over the preconditioned Krylov space `x₀ + 𝒦_j(M⁻¹ A, M⁻¹ r₀)`, hence minimizes the `A`-norm of
the error there. -/
theorem pcg_isGalerkinIterate (hM : Krylov.IsPreconditioner (op M) (op M⁻¹))
    (hA : (op A).IsSymmetric) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x : 𝔼, c * RCLike.re (inner 𝕜 (op M x) x) ≤ RCLike.re (inner 𝕜 (op A x) x))
    (b x₀ : 𝔼) (j : ℕ) :
    IsGalerkin (op A) b x₀ (Chapter06.krylov (M⁻¹ * A) (op M⁻¹ (b - op A x₀)) j)
      (pcgX A M b x₀ j) := by
  rw [pcgX_eq hA hM.isSymmetric_inv, Chapter06.krylov_eq, op_mul]
  exact Krylov.PCG.isGalerkinIterate hM hA hc hcoer j

/-- **P-9.6**: the conjugate gradient convergence bound for Algorithm 9.1,
`‖x_* - x_j‖_A ≤ 2 ((√κ - 1)/(√κ + 1))^j ‖x_* - x_0‖_A`, with `κ = λ_max/λ_min` the condition
number of the generalized eigenvalue problem `A x = λ M x` — that is, of `M⁻¹ A` in the
`M`-inner product. Preconditioning changes only which condition number appears. -/
theorem problem_9_6 (hM : Krylov.IsPreconditioner (op M) (op M⁻¹)) (hA : (op A).IsSymmetric)
    {lmin lmax : ℝ} (hl : 0 < lmin) (hll : lmin ≤ lmax)
    (hmin : ∀ x : 𝔼, lmin * RCLike.re (inner 𝕜 (op M x) x) ≤ RCLike.re (inner 𝕜 (op A x) x))
    (hmax : ∀ x : 𝔼, RCLike.re (inner 𝕜 (op A x) x) ≤ lmax * RCLike.re (inner 𝕜 (op M x) x))
    {b x₀ xstar : 𝔼} (hstar : op A xstar = b) (j : ℕ) :
    energyNorm (op A) (xstar - pcgX A M b x₀ j) ≤
      2 * ((Real.sqrt (lmax / lmin) - 1) / (Real.sqrt (lmax / lmin) + 1)) ^ j *
        energyNorm (op A) (xstar - x₀) := by
  rw [pcgX_eq hA hM.isSymmetric_inv]
  exact Krylov.PCG.energyNorm_error_le hM hA hl hll hmin hmax hstar j

/-! ### Algorithm 9.2: the split-preconditioner conjugate gradient method -/

variable (A) (L : Matrix (Fin n) (Fin n) 𝕜)

/-- The step length `α_j = (r̂_j, r̂_j)/(A p_j, p_j)` of Algorithm 9.2, line 3, on the triple
`(x_j, r̂_j, p_j)`. -/
noncomputable def splitPcgStepAlpha (s : 𝔼 × 𝔼 × 𝔼) : 𝕜 :=
  inner 𝕜 s.2.1 s.2.1 / inner 𝕜 s.2.2 (op A s.2.2)

/-- `r̂_{j+1} = r̂_j - α_j L⁻¹ A p_j`, Algorithm 9.2, line 5. -/
noncomputable def splitPcgStepR (s : 𝔼 × 𝔼 × 𝔼) : 𝔼 :=
  s.2.1 - splitPcgStepAlpha A s • op L⁻¹ (op A s.2.2)

/-- `β_j = (r̂_{j+1}, r̂_{j+1})/(r̂_j, r̂_j)`, Algorithm 9.2, line 6. -/
noncomputable def splitPcgStepBeta (s : 𝔼 × 𝔼 × 𝔼) : 𝕜 :=
  inner 𝕜 (splitPcgStepR A L s) (splitPcgStepR A L s) / inner 𝕜 s.2.1 s.2.1

/-- One pass through lines 3–7 of **Algorithm 9.2**. -/
noncomputable def splitPcgStep (s : 𝔼 × 𝔼 × 𝔼) : 𝔼 × 𝔼 × 𝔼 :=
  (s.1 + splitPcgStepAlpha A s • s.2.2, splitPcgStepR A L s,
    op (Lᴴ)⁻¹ (splitPcgStepR A L s) + splitPcgStepBeta A L s • s.2.2)

/-- **Algorithm 9.2** (conjugate gradient with the split preconditioner `M = L Lᴴ`) run for `j`
steps: the triple `(x_j, r̂_j, p_j)`, started from `r̂_0 = L⁻¹ r_0` and `p_0 = L⁻ᴴ r̂_0`. -/
noncomputable def splitPcg (b x₀ : 𝔼) (j : ℕ) : 𝔼 × 𝔼 × 𝔼 :=
  (splitPcgStep A L)^[j] (x₀, op L⁻¹ (b - op A x₀), op (Lᴴ)⁻¹ (op L⁻¹ (b - op A x₀)))

/-- The recurrence: state `j + 1` is one pass of Algorithm 9.2 applied to state `j`. -/
theorem splitPcg_succ (b x₀ : 𝔼) (j : ℕ) :
    splitPcg A L b x₀ (j + 1) = splitPcgStep A L (splitPcg A L b x₀ j) :=
  Function.iterate_succ_apply' _ _ _

variable {A L}

/-- `L⁻ᴴ L⁻¹ = M⁻¹` for `M = L Lᴴ`: applying the two triangular solves of Algorithm 9.2 is
applying `M⁻¹`. -/
private theorem op_inv_split {M : Matrix (Fin n) (Fin n) 𝕜} (hM : M = L * Lᴴ) (y : 𝔼) :
    op (Lᴴ)⁻¹ (op L⁻¹ y) = op M⁻¹ y := by
  rw [← op_mul_apply, ← Matrix.mul_inv_rev, ← hM]

/-- `(M⁻¹ x, y) = (L⁻¹ x, L⁻¹ y)` for `M = L Lᴴ`: the `M⁻¹`-inner product of Algorithm 9.1 is
the Euclidean inner product of the split residuals of Algorithm 9.2. -/
private theorem inner_op_inv_split {M : Matrix (Fin n) (Fin n) 𝕜} (hM : M = L * Lᴴ) (x y : 𝔼) :
    inner 𝕜 (op M⁻¹ x) y = inner 𝕜 (op L⁻¹ x) (op L⁻¹ y) := by
  have hc : (((Lᴴ)⁻¹)ᴴ) = L⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_conjTranspose]
  rw [← op_inv_split hM, inner_op_conjTranspose, hc]

private theorem splitPcgStep_eq_pcgStep {M : Matrix (Fin n) (Fin n) 𝕜} (hM : M = L * Lᴴ)
    (s : 𝔼 × 𝔼 × 𝔼) :
    splitPcgStep A L (s.1, op L⁻¹ s.2.1, s.2.2)
      = ((pcgStep A M s).1, op L⁻¹ (pcgStep A M s).2.1, (pcgStep A M s).2.2) := by
  have halpha : splitPcgStepAlpha A (s.1, op L⁻¹ s.2.1, s.2.2) = pcgStepAlpha A M s := by
    rw [splitPcgStepAlpha, pcgStepAlpha_def, inner_op_inv_split hM]
  have hr : splitPcgStepR A L (s.1, op L⁻¹ s.2.1, s.2.2) = op L⁻¹ (pcgStepR A M s) := by
    rw [splitPcgStepR, pcgStepR_def, halpha, map_sub, map_smul]
  have hbeta : splitPcgStepBeta A L (s.1, op L⁻¹ s.2.1, s.2.2) = pcgStepBeta A M s := by
    rw [splitPcgStepBeta, hr, pcgStepBeta_def, inner_op_inv_split hM, inner_op_inv_split hM]
  rw [splitPcgStep, pcgStep, halpha, hr, hbeta, op_inv_split hM]

/-- **§9.2.1** and **P-9.3**: Algorithms 9.1 and 9.2 produce *identical* iterates and identical
search directions from the same `x₀`, and the split residual of Algorithm 9.2 is `L⁻¹` of the
residual of Algorithm 9.1. The change of variables `r̂_j = L⁻¹ r_j` turns one recurrence into the
other; nothing is assumed of `L` beyond `M = L Lᴴ`. -/
theorem splitPcg_eq_pcg {M : Matrix (Fin n) (Fin n) 𝕜} (hM : M = L * Lᴴ) (b x₀ : 𝔼) (j : ℕ) :
    splitPcg A L b x₀ j =
      ((pcg A M b x₀ j).1, op L⁻¹ (pcg A M b x₀ j).2.1, (pcg A M b x₀ j).2.2) := by
  induction j with
  | zero =>
    exact congrArg (fun z => (x₀, op L⁻¹ (b - op A x₀), z)) (op_inv_split hM (b - op A x₀))
  | succ j ih => rw [splitPcg_succ, ih, pcg_succ, splitPcgStep_eq_pcgStep hM]

/-- **§9.2.1**: both Algorithm 9.1 and Algorithm 9.2 compute the conjugate gradient iterates of
the split-preconditioned system `Â u = L⁻¹ b`, `Â = L⁻¹ A L⁻ᴴ`, read through `u = Lᴴ x`. This is
the second half of the paragraph `splitPcg_eq_pcg` proves the first half of. -/
theorem splitPcg_eq_cg (hA : (op A).IsSymmetric) (hL : IsUnit L) (b x₀ : 𝔼) (j : ℕ) :
    op Lᴴ (splitPcg A L b x₀ j).1
        = (CG.iterate (op (L⁻¹ * A * (Lᴴ)⁻¹)) (op L⁻¹ b) (op Lᴴ x₀) j).x ∧
      (splitPcg A L b x₀ j).2.1
        = (CG.iterate (op (L⁻¹ * A * (Lᴴ)⁻¹)) (op L⁻¹ b) (op Lᴴ x₀) j).r ∧
      op Lᴴ (splitPcg A L b x₀ j).2.2
        = (CG.iterate (op (L⁻¹ * A * (Lᴴ)⁻¹)) (op L⁻¹ b) (op Lᴴ x₀) j).p := by
  have hLu : IsUnit L.det := (isUnit_iff_isUnit_det L).1 hL
  have hLHu : IsUnit (Lᴴ).det := by
    rw [Matrix.det_conjTranspose]; exact hLu.star
  have hinv : ∀ y : 𝔼, op (Lᴴ)⁻¹ (op Lᴴ y) = y := fun y => by
    have h1 : op (Lᴴ)⁻¹ ∘ₗ op Lᴴ = LinearMap.id := by
      rw [← op_mul, Matrix.nonsing_inv_mul _ hLHu]
      exact Matrix.toEuclideanLin_one
    exact DFunLike.congr_fun h1 y
  have hinv' : ∀ y : 𝔼, op Lᴴ (op (Lᴴ)⁻¹ y) = y := fun y => by
    have h1 : op Lᴴ ∘ₗ op (Lᴴ)⁻¹ = LinearMap.id := by
      rw [← op_mul, Matrix.mul_nonsing_inv _ hLHu]
      exact Matrix.toEuclideanLin_one
    exact DFunLike.congr_fun h1 y
  -- `Â` applied to `Lᴴ p` is `L⁻¹ (A p)`
  have hAhat : ∀ p : 𝔼, op (L⁻¹ * A * (Lᴴ)⁻¹) (op Lᴴ p) = op L⁻¹ (op A p) := fun p => by
    rw [op_mul_apply, op_mul_apply, hinv]
  -- the two quadratic forms agree
  have hquad : ∀ p : 𝔼, inner 𝕜 (op (L⁻¹ * A * (Lᴴ)⁻¹) (op Lᴴ p)) (op Lᴴ p)
      = inner 𝕜 p (op A p) := fun p => by
    have hc : (((L : Matrix (Fin n) (Fin n) 𝕜)⁻¹)ᴴ) = (Lᴴ)⁻¹ :=
      Matrix.conjTranspose_nonsing_inv L
    rw [hAhat, inner_op_conjTranspose, hc, hinv, hA]
  induction j with
  | zero =>
    refine ⟨rfl, ?_, ?_⟩
    · change op L⁻¹ (b - op A x₀) = op L⁻¹ b - op (L⁻¹ * A * (Lᴴ)⁻¹) (op Lᴴ x₀)
      rw [hAhat, map_sub]
    · change op Lᴴ (op (Lᴴ)⁻¹ (op L⁻¹ (b - op A x₀)))
        = op L⁻¹ b - op (L⁻¹ * A * (Lᴴ)⁻¹) (op Lᴴ x₀)
      rw [hinv', hAhat, map_sub]
  | succ j ih =>
    obtain ⟨hx, hr, hp⟩ := ih
    have halpha : splitPcgStepAlpha A (splitPcg A L b x₀ j)
        = CG.alpha (op (L⁻¹ * A * (Lᴴ)⁻¹))
          (CG.iterate (op (L⁻¹ * A * (Lᴴ)⁻¹)) (op L⁻¹ b) (op Lᴴ x₀) j) := by
      rw [splitPcgStepAlpha, CG.alpha, hr, ← hp, hquad]
    have hr' : splitPcgStepR A L (splitPcg A L b x₀ j)
        = (CG.iterate (op (L⁻¹ * A * (Lᴴ)⁻¹)) (op L⁻¹ b) (op Lᴴ x₀) (j + 1)).r := by
      rw [splitPcgStepR, CG.iterate_succ_r, ← halpha, hr, ← hp, hAhat]
    have hbeta : splitPcgStepBeta A L (splitPcg A L b x₀ j)
        = CG.beta (op (L⁻¹ * A * (Lᴴ)⁻¹))
          (CG.iterate (op (L⁻¹ * A * (Lᴴ)⁻¹)) (op L⁻¹ b) (op Lᴴ x₀) j) := by
      rw [splitPcgStepBeta, CG.beta_iterate, hr', hr]
    refine ⟨?_, ?_, ?_⟩
    · rw [splitPcg_succ, splitPcgStep, CG.iterate_succ_x, map_add, map_smul, hx, hp, halpha]
    · rw [splitPcg_succ, splitPcgStep]
      exact hr'
    · rw [splitPcg_succ, splitPcgStep, CG.iterate_succ_p, map_add, map_smul, hinv', hr', hp,
        hbeta]

/-! ### §9.2.1, closing paragraph: right preconditioning in the `M⁻¹`-inner product -/

variable (A M)

/-- The step length of the conjugate gradient method for the right-preconditioned system
`A M⁻¹ u = b` in the `M⁻¹`-inner product, `α_j = (ρ_j, ρ_j)_{M⁻¹}/(A M⁻¹ q_j, q_j)_{M⁻¹}`, on
the triple `(u_j, ρ_j, q_j)`; `(x, y)_{M⁻¹} = (M⁻¹ x, y)`. -/
noncomputable def rightPcgStepAlpha (s : 𝔼 × 𝔼 × 𝔼) : 𝕜 :=
  inner 𝕜 (op M⁻¹ s.2.1) s.2.1 / inner 𝕜 (op M⁻¹ (op A (op M⁻¹ s.2.2))) s.2.2

/-- `ρ_{j+1} = ρ_j - α_j A M⁻¹ q_j`. -/
noncomputable def rightPcgStepR (s : 𝔼 × 𝔼 × 𝔼) : 𝔼 :=
  s.2.1 - rightPcgStepAlpha A M s • op A (op M⁻¹ s.2.2)

/-- `β_j = (ρ_{j+1}, ρ_{j+1})_{M⁻¹}/(ρ_j, ρ_j)_{M⁻¹}`. -/
noncomputable def rightPcgStepBeta (s : 𝔼 × 𝔼 × 𝔼) : 𝕜 :=
  inner 𝕜 (op M⁻¹ (rightPcgStepR A M s)) (rightPcgStepR A M s) / inner 𝕜 (op M⁻¹ s.2.1) s.2.1

/-- One step of the conjugate gradient method for `A M⁻¹ u = b` in the `M⁻¹`-inner product. -/
noncomputable def rightPcgStep (s : 𝔼 × 𝔼 × 𝔼) : 𝔼 × 𝔼 × 𝔼 :=
  (s.1 + rightPcgStepAlpha A M s • s.2.2, rightPcgStepR A M s,
    rightPcgStepR A M s + rightPcgStepBeta A M s • s.2.2)

/-- The conjugate gradient method for the right-preconditioned system `A M⁻¹ u = b`, run in the
`M⁻¹`-inner product, for `j` steps. -/
noncomputable def rightPcg (b u₀ : 𝔼) (j : ℕ) : 𝔼 × 𝔼 × 𝔼 :=
  (rightPcgStep A M)^[j] (u₀, b - op A (op M⁻¹ u₀), b - op A (op M⁻¹ u₀))

/-- The recurrence: state `j + 1` is one pass of the right-preconditioned iteration
applied to state `j`. -/
theorem rightPcg_succ (b u₀ : 𝔼) (j : ℕ) :
    rightPcg A M b u₀ (j + 1) = rightPcgStep A M (rightPcg A M b u₀ j) :=
  Function.iterate_succ_apply' _ _ _

variable {A M}

private theorem rightPcgStep_eq_pcgStep (hA : (op A).IsSymmetric)
    (hMinv : (op M⁻¹).IsSymmetric) (s : 𝔼 × 𝔼 × 𝔼) :
    (op M⁻¹ (rightPcgStep A M s).1, (rightPcgStep A M s).2.1, op M⁻¹ (rightPcgStep A M s).2.2)
      = pcgStep A M (op M⁻¹ s.1, s.2.1, op M⁻¹ s.2.2) := by
  have halpha : rightPcgStepAlpha A M s = pcgStepAlpha A M (op M⁻¹ s.1, s.2.1, op M⁻¹ s.2.2) := by
    rw [rightPcgStepAlpha, pcgStepAlpha_def, hMinv (op A (op M⁻¹ s.2.2)) s.2.2, hA]
  have hr : rightPcgStepR A M s = pcgStepR A M (op M⁻¹ s.1, s.2.1, op M⁻¹ s.2.2) := by
    rw [rightPcgStepR, pcgStepR_def, halpha]
  have hbeta : rightPcgStepBeta A M s
      = pcgStepBeta A M (op M⁻¹ s.1, s.2.1, op M⁻¹ s.2.2) := by
    rw [rightPcgStepBeta, pcgStepBeta_def, hr]
  rw [rightPcgStep, pcgStep, halpha, hr, hbeta]
  exact congrArg₂ (fun a c => (a, pcgStepR A M (op M⁻¹ s.1, s.2.1, op M⁻¹ s.2.2), c))
    (map_add _ _ _ |>.trans (by rw [map_smul])) (map_add _ _ _ |>.trans (by rw [map_smul]))

/-- **§9.2.1**, closing paragraph: the conjugate gradient method for the right-preconditioned
system `A M⁻¹ u = b` in the `M⁻¹`-inner product, written in the variables `x = M⁻¹ u`,
`p = M⁻¹ q`, is Algorithm 9.1 verbatim. Left preconditioning with the `M`-inner product and right
preconditioning with the `M⁻¹`-inner product are the same method. -/
theorem rightPcg_eq_pcg (hA : (op A).IsSymmetric) (hMinv : (op M⁻¹).IsSymmetric) (b u₀ : 𝔼)
    (j : ℕ) :
    (op M⁻¹ (rightPcg A M b u₀ j).1, (rightPcg A M b u₀ j).2.1,
        op M⁻¹ (rightPcg A M b u₀ j).2.2) = pcg A M b (op M⁻¹ u₀) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [rightPcg_succ, pcg_succ, ← ih, rightPcgStep_eq_pcgStep hA hMinv]

/-! ### P-9.2: Algorithm 9.1 in the `A`-inner product -/

variable (A M)

/-- The step length of `pcgEnergyA`, `α_j = (z_j, z_j)_A/(M⁻¹ A p_j, p_j)_A`, on the quintuple
`(x_j, z_j, A z_j, p_j, A p_j)`; both `A`-inner products are Euclidean ones,
`(A z_j, z_j)` and `(A M⁻¹ A p_j, p_j)`, and the second reuses the step's one matrix-vector
product. -/
noncomputable def pcgEnergyAStepAlpha (s : 𝔼 × 𝔼 × 𝔼 × 𝔼 × 𝔼) : 𝕜 :=
  inner 𝕜 s.2.2.1 s.2.1 / inner 𝕜 (op A (op M⁻¹ s.2.2.2.2)) s.2.2.2.1

/-- The next preconditioned residual `z_{j+1} = z_j - α_j M⁻¹ A p_j`. -/
noncomputable def pcgEnergyAStepZ (s : 𝔼 × 𝔼 × 𝔼 × 𝔼 × 𝔼) : 𝔼 :=
  s.2.1 - pcgEnergyAStepAlpha A M s • op M⁻¹ s.2.2.2.2

/-- `A z_{j+1}`, obtained with the *single* matrix-vector product of the step: `A` is applied to
`M⁻¹ A p_j` and to nothing else. -/
noncomputable def pcgEnergyAStepW (s : 𝔼 × 𝔼 × 𝔼 × 𝔼 × 𝔼) : 𝔼 :=
  s.2.2.1 - pcgEnergyAStepAlpha A M s • op A (op M⁻¹ s.2.2.2.2)

/-- The direction coefficient `β_j = (z_{j+1}, z_{j+1})_A/(z_j, z_j)_A`. -/
noncomputable def pcgEnergyAStepBeta (s : 𝔼 × 𝔼 × 𝔼 × 𝔼 × 𝔼) : 𝕜 :=
  inner 𝕜 (pcgEnergyAStepW A M s) (pcgEnergyAStepZ A M s) / inner 𝕜 s.2.2.1 s.2.1

/-- One step of **P-9.2**: Algorithm 9.1 run in the `A`-inner product. `A z_j` and `A p_j` are
carried in the state, so that the step applies `A` once and `M⁻¹` once. -/
noncomputable def pcgEnergyAStep (s : 𝔼 × 𝔼 × 𝔼 × 𝔼 × 𝔼) : 𝔼 × 𝔼 × 𝔼 × 𝔼 × 𝔼 :=
  (s.1 + pcgEnergyAStepAlpha A M s • s.2.2.2.1, pcgEnergyAStepZ A M s, pcgEnergyAStepW A M s,
    pcgEnergyAStepZ A M s + pcgEnergyAStepBeta A M s • s.2.2.2.1,
    pcgEnergyAStepW A M s + pcgEnergyAStepBeta A M s • s.2.2.2.2)

/-- **P-9.2**: the analogue of Algorithm 9.1 in the `A`-inner product, run for `j` steps. The
state is `(x_j, z_j, A z_j, p_j, A p_j)`, started from `z_0 = p_0 = M⁻¹ r_0`. -/
noncomputable def pcgEnergyA (b x₀ : 𝔼) (j : ℕ) : 𝔼 × 𝔼 × 𝔼 × 𝔼 × 𝔼 :=
  (pcgEnergyAStep A M)^[j] (x₀, op M⁻¹ (b - op A x₀), op A (op M⁻¹ (b - op A x₀)),
    op M⁻¹ (b - op A x₀), op A (op M⁻¹ (b - op A x₀)))

/-- The recurrence: state `j + 1` is one pass of the `A`-inner-product algorithm applied to
state `j`. -/
theorem pcgEnergyA_succ (b x₀ : 𝔼) (j : ℕ) :
    pcgEnergyA A M b x₀ (j + 1) = pcgEnergyAStep A M (pcgEnergyA A M b x₀ j) :=
  Function.iterate_succ_apply' _ _ _

variable {A M}

/-- `A M⁻¹ A` is symmetric whenever `A` and `M⁻¹` are. -/
theorem isSymmetric_op_mul_inv_mul (hA : (op A).IsSymmetric) (hMinv : (op M⁻¹).IsSymmetric) :
    (op (A * M⁻¹ * A)).IsSymmetric := by
  intro x y
  simp only [op_mul_apply]
  rw [hA, hMinv]
  exact hA _ _

/-- **P-9.2**: the `A`-inner-product algorithm is the backbone preconditioned conjugate gradient
iteration for `A M⁻¹ A x = A M⁻¹ b` preconditioned by `A`. The quintuple's invariants
`A z_j = r̂_j` and `A p_j` are maintained by the recurrence, which is why one matrix-vector
product per step suffices. -/
theorem pcgEnergyA_eq (hAinv : ∀ y : 𝔼, op A⁻¹ (op A y) = y)
    (b x₀ : 𝔼) (j : ℕ) :
    (pcgEnergyA A M b x₀ j).1
        = (Krylov.PCG.iterate (op (A * M⁻¹ * A)) (op A⁻¹) (op (A * M⁻¹) b) x₀ j).x ∧
      (pcgEnergyA A M b x₀ j).2.2.1
        = (Krylov.PCG.iterate (op (A * M⁻¹ * A)) (op A⁻¹) (op (A * M⁻¹) b) x₀ j).r ∧
      (pcgEnergyA A M b x₀ j).2.2.2.1
        = (Krylov.PCG.iterate (op (A * M⁻¹ * A)) (op A⁻¹) (op (A * M⁻¹) b) x₀ j).p ∧
      (pcgEnergyA A M b x₀ j).2.2.1 = op A (pcgEnergyA A M b x₀ j).2.1 ∧
      (pcgEnergyA A M b x₀ j).2.2.2.2 = op A (pcgEnergyA A M b x₀ j).2.2.2.1 := by
  have hAhat : ∀ y : 𝔼, op (A * M⁻¹ * A) y = op A (op M⁻¹ (op A y)) := fun y => by
    simp only [op_mul_apply]
  have hbhat : op (A * M⁻¹) b - op (A * M⁻¹ * A) x₀ = op A (op M⁻¹ (b - op A x₀)) := by
    rw [op_mul_apply, hAhat, ← map_sub, ← map_sub]
  induction j with
  | zero =>
    refine ⟨rfl, hbhat.symm, ?_, rfl, rfl⟩
    change op M⁻¹ (b - op A x₀) = op A⁻¹ (op (A * M⁻¹) b - op (A * M⁻¹ * A) x₀)
    rw [hbhat, hAinv]
  | succ j ih =>
    obtain ⟨hx, hw, hp, hwz, hqp⟩ := ih
    set S := pcgEnergyA A M b x₀ j with hS
    set P := Krylov.PCG.iterate (op (A * M⁻¹ * A)) (op A⁻¹) (op (A * M⁻¹) b) x₀ j with hP
    have hz : op A⁻¹ P.r = S.2.1 := by rw [← hw, hwz, hAinv]
    have halpha : pcgEnergyAStepAlpha A M S
        = Krylov.PCG.alpha (op (A * M⁻¹ * A)) (op A⁻¹) P := by
      rw [pcgEnergyAStepAlpha, Krylov.PCG.alpha, hz, hw, hAhat, ← hp, hqp]
    have hwnew : pcgEnergyAStepW A M S = op A (pcgEnergyAStepZ A M S) := by
      rw [pcgEnergyAStepW, pcgEnergyAStepZ, map_sub, map_smul, hwz]
    have hrnew : pcgEnergyAStepW A M S = (Krylov.PCG.step (op (A * M⁻¹ * A)) (op A⁻¹) P).r := by
      rw [pcgEnergyAStepW, Krylov.PCG.step_r, halpha, hw, hAhat, ← hp, hqp]
    have hznew : op A⁻¹ (Krylov.PCG.step (op (A * M⁻¹ * A)) (op A⁻¹) P).r
        = pcgEnergyAStepZ A M S := by rw [← hrnew, hwnew, hAinv]
    have hbeta : pcgEnergyAStepBeta A M S = Krylov.PCG.beta (op (A * M⁻¹ * A)) (op A⁻¹) P := by
      rw [pcgEnergyAStepBeta, Krylov.PCG.beta, hznew, hrnew, hz, hw]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [pcgEnergyA_succ, pcgEnergyAStep, Krylov.PCG.iterate_succ, Krylov.PCG.step_x, hx, hp,
        halpha]
    · rw [pcgEnergyA_succ, pcgEnergyAStep, Krylov.PCG.iterate_succ]
      exact hrnew
    · rw [pcgEnergyA_succ, pcgEnergyAStep, Krylov.PCG.iterate_succ, Krylov.PCG.step_p, hznew, hp,
        hbeta]
    · rw [pcgEnergyA_succ, pcgEnergyAStep]
      exact hwnew
    · rw [pcgEnergyA_succ, pcgEnergyAStep, hwnew, map_add, map_smul, hqp]

/-- **P-9.2**: the iterates of the `A`-inner-product algorithm are the Galerkin iterates of
`A M⁻¹ A x = A M⁻¹ b` over the *same* preconditioned Krylov space `x₀ + 𝒦_j(M⁻¹ A, M⁻¹ r₀)` that
Algorithm 9.1 searches, so they minimize the `A M⁻¹ A`-norm of the error there: the algorithm is
the preconditioned conjugate residual method. -/
theorem pcgEnergyA_isGalerkinIterate (hA : (op A).IsSymmetric)
    (hAp : Krylov.IsPreconditioner (op A) (op A⁻¹)) (hAu : IsUnit A) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x : 𝔼, c * RCLike.re (inner 𝕜 (op A x) x)
      ≤ RCLike.re (inner 𝕜 (op (A * M⁻¹ * A) x) x))
    (hMinv : (op M⁻¹).IsSymmetric) (b x₀ : 𝔼) (j : ℕ) :
    IsGalerkin (op (A * M⁻¹ * A)) (op (A * M⁻¹) b) x₀
      (Chapter06.krylov (M⁻¹ * A) (op M⁻¹ (b - op A x₀)) j) (pcgEnergyA A M b x₀ j).1 := by
  have hAinv : ∀ y : 𝔼, op A⁻¹ (op A y) = y := hAp.inv_apply
  have hAhat : ∀ y : 𝔼, op (A * M⁻¹ * A) y = op A (op M⁻¹ (op A y)) := fun y => by
    simp only [op_mul_apply]
  have hspace : op A⁻¹ ∘ₗ op (A * M⁻¹ * A) = op (M⁻¹ * A) := by
    rw [← op_mul]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det A).1 hAu), Matrix.one_mul]
  have hres : op A⁻¹ (op (A * M⁻¹) b - op (A * M⁻¹ * A) x₀) = op M⁻¹ (b - op A x₀) := by
    rw [op_mul_apply, hAhat, ← map_sub, ← map_sub, hAinv]
  have h := Krylov.PCG.isGalerkinIterate (A := op (A * M⁻¹ * A)) (Minv := op A⁻¹)
    (b := op (A * M⁻¹) b) (x₀ := x₀) hAp (isSymmetric_op_mul_inv_mul hA hMinv) hc hcoer j
  rw [hspace, hres] at h
  rw [(pcgEnergyA_eq hAinv b x₀ j).1, Chapter06.krylov_eq]
  exact h

/-! ### P-9.12: the preconditioned conjugate residual method -/

section CRStep

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

private theorem crStep_x (B : F →ₗ[𝕜] F) (s : CR.State F) :
    (CR.step B s).x = s.x + CR.alpha B s • s.p := rfl

private theorem crStep_r (B : F →ₗ[𝕜] F) (s : CR.State F) :
    (CR.step B s).r = s.r - CR.alpha B s • s.q := rfl

private theorem crStep_p (B : F →ₗ[𝕜] F) (s : CR.State F) :
    (CR.step B s).p = (CR.step B s).r
      + (inner 𝕜 (CR.step B s).r (B (CR.step B s).r) / inner 𝕜 s.r (B s.r)) • s.p := rfl

private theorem crStep_q (B : F →ₗ[𝕜] F) (s : CR.State F) :
    (CR.step B s).q = B (CR.step B s).r
      + (inner 𝕜 (CR.step B s).r (B (CR.step B s).r) / inner 𝕜 s.r (B s.r)) • s.q := rfl

end CRStep

variable (A M)

/-- The step length `α_j = (z_j, A z_j)/(M⁻¹ A p_j, A p_j)` of the preconditioned conjugate
residual method (**P-9.12**) on the quadruple `(x_j, z_j, p_j, q_j)` with `q_j = A p_j`. As in
Algorithm 9.1, both `M`-inner products of the underlying method are Euclidean ones:
`(z_j, M⁻¹ A z_j)_M = (z_j, A z_j)` and `(M⁻¹ A p_j, M⁻¹ A p_j)_M = (M⁻¹ A p_j, A p_j)`. -/
noncomputable def pcrStepAlpha (s : 𝔼 × 𝔼 × 𝔼 × 𝔼) : 𝕜 :=
  inner 𝕜 s.2.1 (op A s.2.1) / inner 𝕜 (op M⁻¹ s.2.2.2) s.2.2.2

/-- The next preconditioned residual `z_{j+1} = z_j - α_j M⁻¹ A p_j` of P-9.12. -/
noncomputable def pcrStepZ (s : 𝔼 × 𝔼 × 𝔼 × 𝔼) : 𝔼 :=
  s.2.1 - pcrStepAlpha A M s • op M⁻¹ s.2.2.2

/-- The direction coefficient `β_j = (z_{j+1}, A z_{j+1})/(z_j, A z_j)` of P-9.12. -/
noncomputable def pcrStepBeta (s : 𝔼 × 𝔼 × 𝔼 × 𝔼) : 𝕜 :=
  inner 𝕜 (pcrStepZ A M s) (op A (pcrStepZ A M s)) / inner 𝕜 s.2.1 (op A s.2.1)

/-- One pass of **P-9.12**, the analogue of Algorithm 9.1 for the conjugate residual method:
`x := x + α p`, `z := z - α M⁻¹ q`, `p := z + β p`, `q := A z + β q`. It applies `A` once, to the
new preconditioned residual, and `M⁻¹` once, to `q_j = A p_j`. -/
noncomputable def pcrStep (s : 𝔼 × 𝔼 × 𝔼 × 𝔼) : 𝔼 × 𝔼 × 𝔼 × 𝔼 :=
  (s.1 + pcrStepAlpha A M s • s.2.2.1, pcrStepZ A M s,
    pcrStepZ A M s + pcrStepBeta A M s • s.2.2.1,
    op A (pcrStepZ A M s) + pcrStepBeta A M s • s.2.2.2)

/-- **P-9.12** (preconditioned conjugate residual) run for `j` steps: the quadruple
`(x_j, z_j, p_j, q_j)`, started from `z_0 = p_0 = M⁻¹ r_0` and `q_0 = A p_0`. -/
noncomputable def pcr (b x₀ : 𝔼) (j : ℕ) : 𝔼 × 𝔼 × 𝔼 × 𝔼 :=
  (pcrStep A M)^[j] (x₀, op M⁻¹ (b - op A x₀), op M⁻¹ (b - op A x₀),
    op A (op M⁻¹ (b - op A x₀)))

/-- The recurrence: state `j + 1` is one pass of P-9.12 applied to state `j`. -/
theorem pcr_succ (b x₀ : 𝔼) (j : ℕ) : pcr A M b x₀ (j + 1) = pcrStep A M (pcr A M b x₀ j) :=
  Function.iterate_succ_apply' _ _ _

variable {A M}

/-- **P-9.12**: the preconditioned conjugate residual method is the backbone conjugate residual
recurrence `CR.iterate` for `M⁻¹ A` in the `M`-inner product, exactly as Algorithm 9.1 is
`Krylov.PCG.iterate` there. Its state carries the preconditioned residual `z_j = M⁻¹ r_j`, whose
image is the residual of the transported iteration, and `q_j = A p_j`, whose image under `M⁻¹` is
the transported `M⁻¹ A p_j`. -/
theorem pcr_eq (hM : Krylov.IsPreconditioner (op M) (op M⁻¹)) (b x₀ : 𝔼) (j : ℕ) :
    hM.toEnergy (pcr A M b x₀ j).1
        = (CR.iterate (hM.energyEnd (op M⁻¹ ∘ₗ op A)) (hM.toEnergy (op M⁻¹ b))
            (hM.toEnergy x₀) j).x ∧
      hM.toEnergy (pcr A M b x₀ j).2.1
        = (CR.iterate (hM.energyEnd (op M⁻¹ ∘ₗ op A)) (hM.toEnergy (op M⁻¹ b))
            (hM.toEnergy x₀) j).r ∧
      hM.toEnergy (pcr A M b x₀ j).2.2.1
        = (CR.iterate (hM.energyEnd (op M⁻¹ ∘ₗ op A)) (hM.toEnergy (op M⁻¹ b))
            (hM.toEnergy x₀) j).p ∧
      hM.toEnergy (op M⁻¹ (pcr A M b x₀ j).2.2.2)
        = (CR.iterate (hM.energyEnd (op M⁻¹ ∘ₗ op A)) (hM.toEnergy (op M⁻¹ b))
            (hM.toEnergy x₀) j).q := by
  set Ahat := hM.energyEnd (op M⁻¹ ∘ₗ op A) with hAhat
  have hstep : ∀ y : 𝔼, Ahat (hM.toEnergy y) = hM.toEnergy (op M⁻¹ (op A y)) := fun _ => rfl
  have hinit : hM.toEnergy (op M⁻¹ (b - op A x₀))
      = hM.toEnergy (op M⁻¹ b) - Ahat (hM.toEnergy x₀) := by
    rw [hstep, ← map_sub, ← map_sub]
  induction j with
  | zero =>
    refine ⟨rfl, hinit, hinit, ?_⟩
    change hM.toEnergy (op M⁻¹ (op A (op M⁻¹ (b - op A x₀))))
      = Ahat (hM.toEnergy (op M⁻¹ b) - Ahat (hM.toEnergy x₀))
    rw [← hinit, hstep]
  | succ j ih =>
    obtain ⟨hx, hr, hp, hq⟩ := ih
    set S := pcr A M b x₀ j with hS
    set C := CR.iterate Ahat (hM.toEnergy (op M⁻¹ b)) (hM.toEnergy x₀) j with hC
    have hnum : inner 𝕜 C.r (Ahat C.r) = inner 𝕜 S.2.1 (op A S.2.1) := by
      rw [← hr]
      exact hM.inner_energyEnd_right (op A) S.2.1 S.2.1
    have hden : inner 𝕜 C.q C.q = inner 𝕜 (op M⁻¹ S.2.2.2) S.2.2.2 := by
      rw [← hq, hM.inner_toEnergy_inv]
    have halpha : CR.alpha Ahat C = pcrStepAlpha A M S := by
      rw [CR.alpha, pcrStepAlpha, hnum, hden]
    have hznew : hM.toEnergy (pcrStepZ A M S) = (CR.step Ahat C).r := by
      rw [crStep_r, halpha, pcrStepZ, map_sub, map_smul, hr, hq]
    have hnum' : inner 𝕜 (CR.step Ahat C).r (Ahat (CR.step Ahat C).r)
        = inner 𝕜 (pcrStepZ A M S) (op A (pcrStepZ A M S)) := by
      rw [← hznew]
      exact hM.inner_energyEnd_right (op A) (pcrStepZ A M S) (pcrStepZ A M S)
    have hbeta : inner 𝕜 (CR.step Ahat C).r (Ahat (CR.step Ahat C).r) / inner 𝕜 C.r (Ahat C.r)
        = pcrStepBeta A M S := by
      rw [pcrStepBeta, hnum, hnum']
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [pcr_succ, ← hS, pcrStep, CR.iterate_succ, ← hC, crStep_x, map_add, map_smul, hx, hp,
        halpha]
    · rw [pcr_succ, ← hS, pcrStep, CR.iterate_succ, ← hC]
      exact hznew
    · rw [pcr_succ, ← hS, pcrStep, CR.iterate_succ, ← hC, crStep_p, map_add, map_smul, hznew, hp,
        hbeta]
    · rw [pcr_succ, ← hS, pcrStep, CR.iterate_succ, ← hC, crStep_q, map_add, map_add, map_smul,
        map_smul, ← hstep, hznew, hq, hbeta]

/-- **P-9.12**: the state's second component is `M⁻¹` of the true residual, so the stopping test of
Algorithm 9.1 reads the same way here. -/
theorem pcr_residual_eq (hM : Krylov.IsPreconditioner (op M) (op M⁻¹)) (b x₀ : 𝔼) (j : ℕ) :
    (pcr A M b x₀ j).2.1 = op M⁻¹ (b - op A (pcr A M b x₀ j).1) := by
  obtain ⟨hx, hr, -, -⟩ := pcr_eq hM b x₀ j
  refine (hM.toEnergy).injective ?_
  rw [hr, CR.residual_eq, ← hx, Krylov.IsPreconditioner.energyEnd_apply, LinearMap.comp_apply,
    ← map_sub, ← map_sub]

/-! ### §9.2.2: the preconditioned product when `M = A - R` -/

/-- **§9.2.2**, opening paragraph: for a preconditioner `M = A - R` the left-preconditioned
product is `M⁻¹ A v = M⁻¹ (M + R) v = v + M⁻¹ R v`, so applying it costs one solve with `M` and one
product with `R`. This is the general form of the rearrangement `equation_9_8` performs for the
SSOR-type preconditioner, and the reason an incomplete factorization is worth storing together
with the entries it dropped. -/
theorem leftPreconditioned_apply_eq_add {R : Matrix (Fin n) (Fin n) 𝕜} (hM : IsUnit M)
    (hR : M = A - R) (v : 𝔼) :
    op (leftPreconditioned M A) v = v + op M⁻¹ (op R v) := by
  have hA : A = M + R := by rw [hR]; abel
  have hmat : leftPreconditioned M A = 1 + M⁻¹ * R := by
    rw [show leftPreconditioned M A = M⁻¹ * A from rfl, hA, Matrix.mul_add,
      Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det M).1 hM)]
  have hadd : op (1 + M⁻¹ * R) v = op (1 : Matrix (Fin n) (Fin n) 𝕜) v + op (M⁻¹ * R) v := by
    rw [show (op (1 + M⁻¹ * R) : 𝔼 →ₗ[𝕜] 𝔼) = op 1 + op (M⁻¹ * R) from map_add _ _ _]
    rfl
  have hone : op (1 : Matrix (Fin n) (Fin n) 𝕜) v = v := by
    rw [show (op (1 : Matrix (Fin n) (Fin n) 𝕜) : 𝔼 →ₗ[𝕜] 𝔼) = LinearMap.id from
      Matrix.toEuclideanLin_one]
    rfl
  rw [hmat, hadd, op_mul_apply, hone]

end General

/-! ### §9.2.2: Eisenstat's implementation -/

section Eisenstat

variable {n : ℕ} {A D : Matrix (Fin n) (Fin n) ℝ}

/-- For symmetric `A` the strict upper part of (4.2) is the transpose of the strict lower part,
so the splitting reads `A = D₀ - E - Eᵀ`, which is the form §9.2.2 uses. -/
theorem transpose_E (hA : A.IsSymm) : (Chapter04.E A)ᵀ = Chapter04.F A := by
  ext i j
  have hsym : A j i = A i j := congrFun (congrFun hA i) j
  simp [Chapter04.E, Chapter04.F, Matrix.strictLower_apply, Matrix.strictUpper_apply, hsym]

/-- Saad §9.2.2: the splitting `A = D₀ - E - Eᵀ` of a symmetric matrix. -/
theorem decomp_symm (hA : A.IsSymm) : A = Chapter04.D A - Chapter04.E A - (Chapter04.E A)ᵀ := by
  rw [transpose_E hA]
  exact Chapter04.decomp A

/-- The algebra behind (9.8): if `X = Y + B + C` with `B` and `C` invertible then
`B⁻¹ X C⁻¹ = B⁻¹ Y C⁻¹ + B⁻¹ + C⁻¹`. -/
private theorem inv_mul_mul_inv_eq {X Y B C : Matrix (Fin n) (Fin n) ℝ} (hB : B⁻¹ * B = 1)
    (hC : C * C⁻¹ = 1) (h : X = Y + B + C) :
    B⁻¹ * X * C⁻¹ = B⁻¹ * Y * C⁻¹ + B⁻¹ + C⁻¹ := by
  rw [h, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, hB, Matrix.one_mul,
    Matrix.mul_assoc B⁻¹ C C⁻¹, hC, Matrix.mul_one]
  abel

/-- **Saad (9.5)–(9.8)**: for `A = D₀ - E - Eᵀ` and the SSOR preconditioner
`M = (D - E) D⁻¹ (D - Eᵀ)`, the split-preconditioned matrix `Â = (D - E)⁻¹ A (D - Eᵀ)⁻¹` is
`(D - E)⁻¹ D₁ (D - Eᵀ)⁻¹ + (D - E)⁻¹ + (D - Eᵀ)⁻¹` with `D₁ = D₀ - 2D`. That identity is the
whole content of Eisenstat's trick: `Â v` costs one product with the sparse `D₁` and the two
triangular solves that applying `M⁻¹` would need anyway. -/
theorem equation_9_8 (hA : A.IsSymm) (h1 : IsUnit (D - Chapter04.E A))
    (h2 : IsUnit (D - (Chapter04.E A)ᵀ)) :
    (D - Chapter04.E A)⁻¹ * A * (D - (Chapter04.E A)ᵀ)⁻¹
      = (D - Chapter04.E A)⁻¹ * (Chapter04.D A - (2 : ℝ) • D) * (D - (Chapter04.E A)ᵀ)⁻¹
        + (D - Chapter04.E A)⁻¹ + (D - (Chapter04.E A)ᵀ)⁻¹ := by
  refine inv_mul_mul_inv_eq (Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 h1))
    (Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 h2)) ?_
  conv_lhs => rw [decomp_symm hA]
  module

open Chapter06 (op)

/-- **Algorithm 9.3** (Eisenstat's implementation): `z = (D - Eᵀ)⁻¹ v`,
`w = (D - E)⁻¹ (v + D₁ z)`, `w := w + z`. This is the procedure §9.2.2 states just before
Algorithm 9.3; the algorithm itself is its rescaling by `D⁻¹`, which saves one product with
the diagonal but computes the same `Â v`. -/
noncomputable def eisenstat (A D : Matrix (Fin n) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  let z := op (D - (Chapter04.E A)ᵀ)⁻¹ v
  op (D - Chapter04.E A)⁻¹ (v + op (Chapter04.D A - (2 : ℝ) • D) z) + z

/-- `SaadSparse.Chapter09.eisenstat` with its `let`-bindings unfolded. -/
theorem eisenstat_def (A D : Matrix (Fin n) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    eisenstat A D v = op (D - Chapter04.E A)⁻¹
        (v + op (Chapter04.D A - (2 : ℝ) • D) (op (D - (Chapter04.E A)ᵀ)⁻¹ v))
      + op (D - (Chapter04.E A)ᵀ)⁻¹ v := rfl

/-- The action of a sum of matrices is the sum of the actions. -/
private theorem op_add_apply (X Y : Matrix (Fin n) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) : op (X + Y) v = op X v + op Y v := by
  have h : (op (X + Y) : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
      = op X + op Y := map_add _ _ _
  rw [h]
  rfl

/-- **Algorithm 9.3** computes `Â v` for the `Â` of (9.8): two triangular solves and one
product with the diagonal `D₁`, and no product with `A`. -/
theorem eisenstat_eq (hA : A.IsSymm) (h1 : IsUnit (D - Chapter04.E A))
    (h2 : IsUnit (D - (Chapter04.E A)ᵀ)) (v : EuclideanSpace ℝ (Fin n)) :
    eisenstat A D v = op ((D - Chapter04.E A)⁻¹ * A * (D - (Chapter04.E A)ᵀ)⁻¹) v := by
  rw [equation_9_8 hA h1 h2, op_add_apply, op_add_apply, eisenstat_def, map_add,
    op_mul_apply, op_mul_apply]
  abel

/-! ### P-9.8 (c): the split-preconditioning option

The problem scales the system symmetrically by the square root of the diagonal `D` of (9.6):
with `C = D^{1/2} Â D^{1/2}` and `Ê = D^{-1/2} E D^{-1/2}` it asks for a matrix `D₂` with
`C = (1 - Ê)⁻¹ D₂ (1 - Ê)⁻ᵀ + (1 - Ê)⁻¹ + (1 - Ê)⁻ᵀ`.  The answer is `D₂ = D^{-1/2} D₁ D^{-1/2}`
for the `D₁ = D₀ - 2D` of (9.8), and it is `-I` for the SSOR choice `D = D₀`: after the scaling
the triangular factors have unit diagonal and no diagonal need be stored at all.

Nothing below uses that `D^{1/2}` is diagonal, only that it is symmetric, invertible and squares
to `D`; for a positive diagonal `D = diagonal d` the intended matrix is
`diagonal fun i => Real.sqrt (d i)`.
-/

section Sqrt

variable {S : Matrix (Fin n) (Fin n) ℝ} (hSu : IsUnit S) (hSD : S * S = D)

include hSu hSD in
/-- `D^{-1/2} D D^{-1/2} = I`. -/
private theorem inv_mul_self_mul_inv : S⁻¹ * D * S⁻¹ = 1 := by
  have hu := (isUnit_iff_isUnit_det S).1 hSu
  rw [← hSD, ← Matrix.mul_assoc S⁻¹ S S, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul,
    Matrix.mul_nonsing_inv _ hu]

include hSu hSD in
/-- The scaling that turns a triangular factor `D - X` of (9.6) into a unit-diagonal one:
`1 - D^{-1/2} X D^{-1/2} = D^{-1/2} (D - X) D^{-1/2}`, so its inverse is `D^{1/2} (D - X)⁻¹
D^{1/2}`. -/
private theorem inv_one_sub_conj (X : Matrix (Fin n) (Fin n) ℝ) :
    (1 - S⁻¹ * X * S⁻¹)⁻¹ = S * (D - X)⁻¹ * S := by
  have hu := (isUnit_iff_isUnit_det S).1 hSu
  have hconj : 1 - S⁻¹ * X * S⁻¹ = S⁻¹ * (D - X) * S⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, inv_mul_self_mul_inv hSu hSD]
  rw [hconj, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu,
    ← Matrix.mul_assoc]

end Sqrt

/-- **P-9.8 (c)**: the split-preconditioned form of Eisenstat's identity.  Let `D^{1/2}` be a
symmetric square root of the diagonal `D` of (9.6), write `Ê = D^{-1/2} E D^{-1/2}`, and let
`C = D^{1/2} Â D^{1/2}` be the matrix conjugate gradients is applied to in the split-preconditioning
option.  Then

`C = (1 - Ê)⁻¹ D₂ (1 - Ê)⁻ᵀ + (1 - Ê)⁻¹ + (1 - Ê)⁻ᵀ`,   `D₂ = D^{-1/2} (D₀ - 2D) D^{-1/2}`,

the conjugate of the `D₁` of `SaadSparse.Chapter09.equation_9_8`.  The two triangular factors are
now transposes of each other and carry a unit diagonal, which is the point of the exercise. -/
theorem problem_9_8c {S : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (hSs : S.IsSymm)
    (hSu : IsUnit S) (hSD : S * S = D) (h1 : IsUnit (D - Chapter04.E A))
    (h2 : IsUnit (D - (Chapter04.E A)ᵀ)) :
    S * ((D - Chapter04.E A)⁻¹ * A * (D - (Chapter04.E A)ᵀ)⁻¹) * S
      = (1 - S⁻¹ * Chapter04.E A * S⁻¹)⁻¹
          * (S⁻¹ * (Chapter04.D A - (2 : ℝ) • D) * S⁻¹)
          * ((1 - S⁻¹ * Chapter04.E A * S⁻¹)ᵀ)⁻¹
        + (1 - S⁻¹ * Chapter04.E A * S⁻¹)⁻¹ + ((1 - S⁻¹ * Chapter04.E A * S⁻¹)ᵀ)⁻¹ := by
  have hu := (isUnit_iff_isUnit_det S).1 hSu
  have hinvSymm : (S⁻¹)ᵀ = S⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hSs.eq]
  -- the transposed factor is the conjugate of `D - Eᵀ`
  have htr : ((1 - S⁻¹ * Chapter04.E A * S⁻¹)ᵀ)⁻¹ = S * (D - (Chapter04.E A)ᵀ)⁻¹ * S := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_mul,
      hinvSymm, ← Matrix.mul_assoc S⁻¹ (Chapter04.E A)ᵀ S⁻¹, inv_one_sub_conj hSu hSD]
  have hfst : (1 - S⁻¹ * Chapter04.E A * S⁻¹)⁻¹ = S * (D - Chapter04.E A)⁻¹ * S :=
    inv_one_sub_conj hSu hSD _
  -- the middle term reassembles after cancelling `D^{1/2} D^{-1/2}` on both sides
  have hmid : ∀ X Y Z : Matrix (Fin n) (Fin n) ℝ,
      S * X * S * (S⁻¹ * Y * S⁻¹) * (S * Z * S) = S * (X * Y * Z) * S := fun X Y Z => by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc S⁻¹ S (Z * S), Matrix.nonsing_inv_mul _ hu, Matrix.one_mul,
      ← Matrix.mul_assoc S S⁻¹ (Y * (Z * S)), Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
  rw [hfst, htr, hmid, equation_9_8 hA h1 h2]
  simp only [Matrix.mul_add, Matrix.add_mul]

/-- **P-9.8 (c)**, the SSOR case `D = D₀`: the matrix "to be determined" is `-I`, so the scaled
identity is `C = -(1 - Ê)⁻¹ (1 - Ê)⁻ᵀ + (1 - Ê)⁻¹ + (1 - Ê)⁻ᵀ` and no diagonal survives. -/
theorem problem_9_8c_ssor {S : Matrix (Fin n) (Fin n) ℝ} (hSu : IsUnit S)
    (hSD : S * S = Chapter04.D A) :
    S⁻¹ * (Chapter04.D A - (2 : ℝ) • Chapter04.D A) * S⁻¹ = -1 := by
  have h : Chapter04.D A - (2 : ℝ) • Chapter04.D A = -Chapter04.D A := by module
  rw [h, Matrix.mul_neg, Matrix.neg_mul, inv_mul_self_mul_inv hSu hSD]

end Eisenstat

end SaadSparse.Chapter09

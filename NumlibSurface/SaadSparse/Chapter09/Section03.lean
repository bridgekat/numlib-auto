import Numlib.Krylov.Preconditioned
import NumlibSurface.SaadSparse.Chapter06.Section05
import NumlibSurface.SaadSparse.Chapter09.Section02

/-!
# Saad, §9.3: preconditioned GMRES

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
SIAM, 2003, §9.3, with P-9.11 and P-9.13.

Both preconditioned algorithms are Algorithm 6.9 at another operator.

* **Algorithm 9.4** (`gmresLeft`) is GMRES for `M⁻¹ A x = M⁻¹ b`, so it minimizes the
  preconditioned residual `‖M⁻¹(b - A x)‖₂` over `x₀ + 𝒦_m(M⁻¹A, M⁻¹ r₀)`
  (`gmresLeft_isMinRes`).
* **Algorithm 9.5** (`gmresRight`) is GMRES for `A M⁻¹ u = b` started at `u₀ = M x₀`, with the
  iterate returned as `x_m = x₀ + M⁻¹ V_m y_m`; `gmresRight_isMinRes` says that it minimizes the
  *true* residual `‖b - A x‖₂` over the *same* affine space.

The two search spaces agree because of (9.18), `s(M⁻¹A) M⁻¹ r = M⁻¹ s(A M⁻¹) r`
(`equation_9_18`, which is **P-9.11**), and `proposition_9_1` is the resulting common form
`x_m = x₀ + s(M⁻¹A) z₀ = x₀ + M⁻¹ s(A M⁻¹) r₀` with `deg s < m`.  §9.3.3, split preconditioning,
is Algorithm 9.5 with `M = M_L M_R`, so it adds no statement of its own.

§9.3.1 also sketches GMRES in the `M`-inner product for a symmetric positive definite `M` and a
nonsymmetric `A` (**P-9.13**).  `IsGMRESEnergyIterate` is its specification and
`isGMRESEnergyIterate_iff` its optimality: it minimizes the `M⁻¹`-norm of the true residual over
the same preconditioned Krylov space.  `equation_9_12` is (9.12) and (9.14)–(9.15), the reason
the algorithm needs no extra product with `M`: every `M`-inner product it forms is a Euclidean
inner product of vectors it has already computed.
-/

open Matrix Polynomial

open scoped SaadSparse

namespace SaadSparse.Ch09

open Ch06 (op)

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

variable {A M : Matrix (Fin n) (Fin n) 𝕜}

/-! ### Algorithms 9.4 and 9.5 -/

/-- **Algorithm 9.4** (GMRES with left preconditioning): Algorithm 6.9 applied to `M⁻¹ A` with
right-hand side `M⁻¹ b`.  The Arnoldi basis spans `𝒦_m(M⁻¹A, M⁻¹ r₀)` and the residual the
algorithm monitors is the preconditioned one, `M⁻¹(b - A x_m)`. -/
noncomputable def gmresLeft (M A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : EuclideanSpace 𝕜 (Fin n))
    (m : ℕ) : EuclideanSpace 𝕜 (Fin n) :=
  Ch06.gmresFixed (leftPreconditioned M A) (op M⁻¹ b) x₀ m

/-- **Algorithm 9.5** (GMRES with right preconditioning): Algorithm 6.9 applied to `A M⁻¹` with
right-hand side `b` and initial guess `u₀ = M x₀`, the iterate returned as
`x_m = x₀ + M⁻¹ V_m y_m`.  The variable `u` never appears in the algorithm, and the residual it
monitors is the true one, `b - A x_m`.  With `M = M_L M_R` and the initial `M_L⁻¹` and final
`M_R⁻¹` applications this is the split-preconditioned algorithm of §9.3.3. -/
noncomputable def gmresRight (M A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : EuclideanSpace 𝕜 (Fin n))
    (m : ℕ) : EuclideanSpace 𝕜 (Fin n) :=
  x₀ + op M⁻¹ (Ch06.gmresFixed (rightPreconditioned M A) b (op M x₀) m - op M x₀)

/-- `M⁻¹ (M x) = x` for a nonsingular `M`. -/
private theorem inv_apply_apply' (hM : IsUnit M) (x : EuclideanSpace 𝕜 (Fin n)) :
    op M⁻¹ (op M x) = x := by
  have h1 : (op (1 : Matrix (Fin n) (Fin n) 𝕜)) = LinearMap.id := Matrix.toEuclideanLin_one
  rw [← op_mul_apply, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det M).1 hM), h1,
    LinearMap.id_apply]

/-- Saad's `x_m = x₀ + M⁻¹ V_m y_m` is `M⁻¹ u_m`: the two forms of Algorithm 9.5 agree. -/
theorem gmresRight_eq (hM : IsUnit M) (b x₀ : EuclideanSpace 𝕜 (Fin n)) (m : ℕ) :
    gmresRight M A b x₀ m = op M⁻¹ (Ch06.gmresFixed (rightPreconditioned M A) b (op M x₀) m) := by
  rw [gmresRight, map_sub, inv_apply_apply' hM]
  abel

/-- **Algorithm 9.4** minimizes the preconditioned residual `‖M⁻¹(b - A x)‖₂` over
`x₀ + 𝒦_m(M⁻¹A, M⁻¹ r₀)`: it is the minimal-residual Krylov iterate of `M⁻¹ A x = M⁻¹ b`. -/
theorem gmresLeft_isMinRes (b x₀ : EuclideanSpace 𝕜 (Fin n)) {m : ℕ}
    (hMA : IsUnit (leftPreconditioned M A))
    (hm : m ≤ Ch06.grade (leftPreconditioned M A)
      (Ch06.v₁ (leftPreconditioned M A) (op M⁻¹ b) x₀)) :
    Krylov.IsMinResIterate (op (leftPreconditioned M A)) (op M⁻¹ b) x₀ m
      (gmresLeft M A b x₀ m) :=
  Ch06.gmresFixed_isMinResIterate _ _ _ hm (Ch06.isUnit_R_of_isUnit _ _ _ hMA hm)

/-- **Algorithm 9.5** minimizes the *true* residual `‖b - A x‖₂` over the same affine space
`x₀ + 𝒦_m(M⁻¹A, M⁻¹ r₀)` that Algorithm 9.4 searches.  This is the difference between left and
right preconditioning: the space is the same, the norm minimized over it is not. -/
theorem gmresRight_isMinRes (b x₀ : EuclideanSpace 𝕜 (Fin n)) {m : ℕ} (hM : IsUnit M)
    (hAM : IsUnit (rightPreconditioned M A))
    (hm : m ≤ Ch06.grade (rightPreconditioned M A)
      (Ch06.v₁ (rightPreconditioned M A) b (op M x₀))) :
    IsMinRes (op A) b x₀
      (Krylov.subspace (op M⁻¹ ∘ₗ op A) (op M⁻¹ (b - op A x₀)) m) (gmresRight M A b x₀ m) := by
  have hu := Ch06.gmresFixed_isMinResIterate (rightPreconditioned M A) b (op M x₀) hm
    (Ch06.isUnit_R_of_isUnit _ _ _ hAM hm)
  rw [show op (rightPreconditioned M A) = op A ∘ₗ op M⁻¹ from op_mul A M⁻¹] at hu
  rw [gmresRight_eq hM]
  exact Krylov.isMinRes_of_isMinResIterate_rightPreconditioned (inv_apply_apply' hM x₀).symm hu

/-! ### (9.18) and Proposition 9.1 -/

/-- `B` semiconjugates `p(A B)` to `p(B A)`, for every polynomial `p`. -/
private theorem semiconjBy_aeval {E : Type*} [AddCommGroup E] [Module 𝕜 E]
    (B C : Module.End 𝕜 E) (p : 𝕜[X]) :
    SemiconjBy B (aeval (C * B) p) (aeval (B * C) p) := by
  refine Polynomial.induction_on' p (fun q r hq hr => ?_) fun k a => ?_
  · simpa only [map_add] using hq.add_right hr
  · rw [aeval_monomial, aeval_monomial]
    exact SemiconjBy.mul_right (Algebra.commutes a B).symm
      (SemiconjBy.pow_right (mul_assoc B C B).symm k)

/-- **(9.18)** and **P-9.11**: `s(M⁻¹A) M⁻¹ r = M⁻¹ s(A M⁻¹) r` for every polynomial `s`, and
hence `M⁻¹ 𝒦_m(A M⁻¹, r) = 𝒦_m(M⁻¹A, M⁻¹ r)`: the two preconditioned Krylov spaces (9.17) and
(9.20) of the left- and right-preconditioned algorithms are the same space. -/
theorem equation_9_18 (s : 𝕜[X]) (r : EuclideanSpace 𝕜 (Fin n)) (m : ℕ) :
    aeval (op (leftPreconditioned M A)) s (op M⁻¹ r)
        = op M⁻¹ (aeval (op (rightPreconditioned M A)) s r)
      ∧ Submodule.map (op M⁻¹) (Krylov.subspace (op (rightPreconditioned M A)) r m)
          = Krylov.subspace (op (leftPreconditioned M A)) (op M⁻¹ r) m := by
  have hL : op (leftPreconditioned M A) = op M⁻¹ * op A := op_mul M⁻¹ A
  have hR : op (rightPreconditioned M A) = op A * op M⁻¹ := op_mul A M⁻¹
  refine ⟨?_, ?_⟩
  · have h : op M⁻¹ * aeval (op A * op M⁻¹) s = aeval (op M⁻¹ * op A) s * op M⁻¹ :=
      semiconjBy_aeval (op M⁻¹) (op A) s
    rw [hL, hR]
    exact (congrArg (fun T : Module.End 𝕜 (EuclideanSpace 𝕜 (Fin n)) => T r) h).symm
  · rw [hL, hR]
    exact Krylov.map_subspace_comp (op A) (op M⁻¹) r m

/-- **Proposition 9.1**: the approximation produced by preconditioned GMRES has the form
`x_m = x₀ + s(M⁻¹A) z₀ = x₀ + M⁻¹ s(A M⁻¹) r₀` with `deg s < m` and `z₀ = M⁻¹ r₀`.  Which
polynomial `s` it is depends on the side: on the right it minimizes `‖b - A x_m‖₂`
(`gmresRight_isMinRes`), on the left `‖M⁻¹(b - A x_m)‖₂` (`gmresLeft_isMinRes`). -/
theorem proposition_9_1 {b x₀ : EuclideanSpace 𝕜 (Fin n)} {m : ℕ}
    {x : EuclideanSpace 𝕜 (Fin n)}
    (hx : Krylov.IsMinResIterate (op (leftPreconditioned M A)) (op M⁻¹ b) x₀ m x) :
    ∃ s : 𝕜[X], s.degree < m ∧
      x = x₀ + aeval (op (leftPreconditioned M A)) s (op M⁻¹ (b - op A x₀)) ∧
      x = x₀ + op M⁻¹ (aeval (op (rightPreconditioned M A)) s (b - op A x₀)) := by
  have hL : op (leftPreconditioned M A) = op M⁻¹ ∘ₗ op A := op_mul M⁻¹ A
  rw [hL] at hx
  have hb : op M⁻¹ b = op M⁻¹ b := rfl
  obtain ⟨s, hs, hxs⟩ := Krylov.exists_aeval_of_isMinResIterate_preconditioned (b := b) (hb ▸ hx)
  refine ⟨s, hs, by rw [hL]; exact hxs, ?_⟩
  rw [hxs, ← hL, (equation_9_18 (A := A) (M := M) s (b - op A x₀) m).1]

/-! ### §9.3.1, P-9.13: GMRES in the `M`-inner product -/

/-- **P-9.13**: `x` is the GMRES approximation at step `m` of `M⁻¹ A x = M⁻¹ b` computed in the
`M`-inner product `(x, y)_M = (M x, y)`, for a symmetric positive definite `M` and a possibly
nonsymmetric `A`.  This is Arnoldi and GMRES of `Numlib/Krylov` run in the space `WithEnergy M`,
which is the modified Gram–Schmidt process of (9.10)–(9.11). -/
def IsGMRESEnergyIterate (A : Matrix (Fin n) (Fin n) 𝕜)
    {M : Matrix (Fin n) (Fin n) 𝕜} (hM : Krylov.IsPreconditioner (op M) (op M⁻¹))
    (b x₀ : EuclideanSpace 𝕜 (Fin n)) (m : ℕ) (x : EuclideanSpace 𝕜 (Fin n)) : Prop :=
  Krylov.IsMinResIterate (hM.energyEnd (op M⁻¹ ∘ₗ op A)) (hM.toEnergy (op M⁻¹ b))
    (hM.toEnergy x₀) m (hM.toEnergy x)

/-- **P-9.13**, the optimality of the `M`-inner product algorithm: it searches the same
preconditioned Krylov space `x₀ + 𝒦_m(M⁻¹A, M⁻¹ r₀)` as Algorithms 9.4 and 9.5, and over it
minimizes the `M`-norm of the preconditioned residual, which is the `M⁻¹`-norm of the true
residual `b - A x`. -/
theorem isGMRESEnergyIterate_iff (hM : Krylov.IsPreconditioner (op M) (op M⁻¹))
    (b x₀ : EuclideanSpace 𝕜 (Fin n)) (m : ℕ) (x : EuclideanSpace 𝕜 (Fin n)) :
    IsGMRESEnergyIterate A hM b x₀ m x ↔
      (x - x₀ ∈ Krylov.subspace (op M⁻¹ ∘ₗ op A) (op M⁻¹ (b - op A x₀)) m ∧
        ∀ y, y - x₀ ∈ Krylov.subspace (op M⁻¹ ∘ₗ op A) (op M⁻¹ (b - op A x₀)) m →
          energyNorm (op M) (op M⁻¹ (b - op A x))
            ≤ energyNorm (op M) (op M⁻¹ (b - op A y))) := by
  have hres : hM.toEnergy (op M⁻¹ b) - hM.energyEnd (op M⁻¹ ∘ₗ op A) (hM.toEnergy x₀)
      = hM.toEnergy (op M⁻¹ (b - op A x₀)) := by
    rw [Krylov.IsPreconditioner.energyEnd_apply, LinearMap.comp_apply, ← map_sub, ← map_sub]
  have h := hM.isMinRes_energyEnd_iff (op A) b x₀
    (Krylov.subspace (op M⁻¹ ∘ₗ op A) (op M⁻¹ (b - op A x₀)) m) x
  rw [← Krylov.IsPreconditioner.subspace_energyEnd, ← hres] at h
  exact h

/-- **(9.12)** and **(9.14)–(9.15)**: every `M`-inner product the algorithm forms is a Euclidean
inner product of vectors it has already computed — `(z, v)_M = (w, v)` for `z = M⁻¹ w`, and
`‖z‖_M = (z, w)^{1/2}` — so no extra product with `M` is needed.  With `w = A v_j` these are
the coefficients `h_{ij}` and the subdiagonal entry `h_{j+1,j}` of the `M`-orthogonal Arnoldi
process. -/
theorem equation_9_12 (hM : Krylov.IsPreconditioner (op M) (op M⁻¹))
    (v w : EuclideanSpace 𝕜 (Fin n)) :
    energyInner (op M) (op M⁻¹ w) v = inner 𝕜 w v ∧
      energyNorm (op M) (op M⁻¹ w) = Real.sqrt (RCLike.re (inner 𝕜 w (op M⁻¹ w))) := by
  refine ⟨by rw [energyInner, hM.apply_inv], by rw [energyNorm, hM.apply_inv]⟩

end SaadSparse.Ch09

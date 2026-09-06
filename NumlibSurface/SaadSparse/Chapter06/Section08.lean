import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Krylov.CR
import Numlib.Krylov.Iterate
import Numlib.Krylov.Subspace
import NumlibSurface.SaadSparse.Chapter06.Section05
import NumlibSurface.SaadSparse.Chapter06.Section07

/-!
# Saad §6.8: the conjugate residual method

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §6.8.

**Algorithm 6.20** (conjugate residual) is `cr`, whose state is the quadruple
`(x_j, r_j, p_j, A p_j)` that the algorithm carries; `crX`, `crR`, `crP`, `crAp`, `crAlpha`,
`crBeta` read it off. The pivot is `cr_eq_CR`: Algorithm 6.20 *is* the backbone recurrence
`CR.iterate` of `Numlib/Krylov/CR.lean`, the only discrepancy being that the book writes the
step length as `(r_j, A r_j)/(A p_j, A p_j)` with the inner product `(x, y) = ∑ x_i ȳ_i`, so its
numerator is `⟪A r_j, r_j⟫` where the backbone writes `⟪r_j, A r_j⟫`; the two agree because `A`
is Hermitian, which is the standing hypothesis of the section.

Everything else follows: the residuals are `A`-orthogonal (conjugate) and the vectors `A p_i`
are orthogonal, and — this is the sense in which §6.8 derives the algorithm "from GMRES for the
particular case where `A` is Hermitian" — the iterate `x_j` is the minimal-residual iterate on
`𝒦_j(A, r_0)`, hence equals the GMRES approximation `gmresFixed` of `Chapter06/Section05.lean`.

Indices are `0`-based, as in the book. Division by a vanishing quantity is `0` in Lean, which
reproduces the book's breakdown behaviour; the indefinite case is covered by
`crX_isMinResIterate_of_no_breakdown`, which asks only that the quantities the algorithm
divides by are nonzero.

Definitions are polymorphic in `𝕜`; the numbered results are stated over `ℝ` with `A`
symmetric positive definite, the book's generality in §6.8.
-/

open scoped ComplexOrder Matrix

namespace SaadSparse.Chapter06

section General

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-! ### Algorithm 6.20 -/

/-- The step length `α_j = (r_j, A r_j)/(A p_j, A p_j)` of Algorithm 6.20, line 3, on the
state `(x_j, r_j, p_j, A p_j)`. -/
noncomputable def crStepAlpha (A : Matrix (Fin n) (Fin n) 𝕜) (s : 𝔼 × 𝔼 × 𝔼 × 𝔼) : 𝕜 :=
  inner 𝕜 (op A s.2.1) s.2.1 / inner 𝕜 s.2.2.2 s.2.2.2

/-- The next residual `r_{j+1} = r_j - α_j A p_j` of Algorithm 6.20, line 5. -/
noncomputable def crStepR (A : Matrix (Fin n) (Fin n) 𝕜) (s : 𝔼 × 𝔼 × 𝔼 × 𝔼) : 𝔼 :=
  s.2.1 - crStepAlpha A s • s.2.2.2

/-- The coefficient `β_j = (r_{j+1}, A r_{j+1})/(r_j, A r_j)` of Algorithm 6.20, line 6. -/
noncomputable def crStepBeta (A : Matrix (Fin n) (Fin n) 𝕜) (s : 𝔼 × 𝔼 × 𝔼 × 𝔼) : 𝕜 :=
  inner 𝕜 (op A (crStepR A s)) (crStepR A s) / inner 𝕜 (op A s.2.1) s.2.1

/-- One pass through lines 3–8 of **Algorithm 6.20** on the state `(x_j, r_j, p_j, A p_j)`;
line 8 updates `A p_{j+1} = A r_{j+1} + β_j A p_j` without a further matrix-vector product. -/
noncomputable def crStep (A : Matrix (Fin n) (Fin n) 𝕜) (s : 𝔼 × 𝔼 × 𝔼 × 𝔼) : 𝔼 × 𝔼 × 𝔼 × 𝔼 :=
  (s.1 + crStepAlpha A s • s.2.2.1, crStepR A s,
    crStepR A s + crStepBeta A s • s.2.2.1,
    op A (crStepR A s) + crStepBeta A s • s.2.2.2)

/-- **Algorithm 6.20** (conjugate residual) run for `j` steps: the quadruple
`(x_j, r_j, p_j, A p_j)`, started from `r_0 = b - A x_0` and `p_0 = r_0`. -/
noncomputable def cr (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (j : ℕ) : 𝔼 × 𝔼 × 𝔼 × 𝔼 :=
  (crStep A)^[j] (x₀, b - op A x₀, b - op A x₀, op A (b - op A x₀))

theorem crStepAlpha_def (A : Matrix (Fin n) (Fin n) 𝕜) (s : 𝔼 × 𝔼 × 𝔼 × 𝔼) :
    crStepAlpha A s = inner 𝕜 (op A s.2.1) s.2.1 / inner 𝕜 s.2.2.2 s.2.2.2 := rfl

theorem crStepR_def (A : Matrix (Fin n) (Fin n) 𝕜) (s : 𝔼 × 𝔼 × 𝔼 × 𝔼) :
    crStepR A s = s.2.1 - crStepAlpha A s • s.2.2.2 := rfl

theorem crStepBeta_def (A : Matrix (Fin n) (Fin n) 𝕜) (s : 𝔼 × 𝔼 × 𝔼 × 𝔼) :
    crStepBeta A s = inner 𝕜 (op A (crStepR A s)) (crStepR A s) / inner 𝕜 (op A s.2.1) s.2.1 :=
  rfl

variable (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : EuclideanSpace 𝕜 (Fin n))

/-- The `j`-th conjugate residual iterate `x_j` of Algorithm 6.20. -/
noncomputable def crX (j : ℕ) : 𝔼 := (cr A b x₀ j).1

/-- The `j`-th residual `r_j` of Algorithm 6.20. -/
noncomputable def crR (j : ℕ) : 𝔼 := (cr A b x₀ j).2.1

/-- The `j`-th conjugate residual search direction `p_j` of Algorithm 6.20. -/
noncomputable def crP (j : ℕ) : 𝔼 := (cr A b x₀ j).2.2.1

/-- The vector `A p_j` carried by Algorithm 6.20, line 8. -/
noncomputable def crAp (j : ℕ) : 𝔼 := (cr A b x₀ j).2.2.2

/-- The step length `α_j` of Algorithm 6.20 at step `j`. -/
noncomputable def crAlpha (j : ℕ) : 𝕜 := crStepAlpha A (cr A b x₀ j)

/-- The direction coefficient `β_j` of Algorithm 6.20 at step `j`. -/
noncomputable def crBeta (j : ℕ) : 𝕜 := crStepBeta A (cr A b x₀ j)

theorem cr_succ (j : ℕ) : cr A b x₀ (j + 1) = crStep A (cr A b x₀ j) :=
  Function.iterate_succ_apply' _ _ _

@[simp] theorem crX_zero : crX A b x₀ 0 = x₀ := rfl

@[simp] theorem crR_zero : crR A b x₀ 0 = b - op A x₀ := rfl

/-- Algorithm 6.20, line 1: `p_0 = r_0`. -/
@[simp] theorem crP_zero : crP A b x₀ 0 = crR A b x₀ 0 := rfl

@[simp] theorem crAp_zero : crAp A b x₀ 0 = op A (crP A b x₀ 0) := rfl

/-- Algorithm 6.20, line 3: `α_j = (r_j, A r_j)/(A p_j, A p_j)`. -/
theorem crAlpha_eq (j : ℕ) : crAlpha A b x₀ j =
    inner 𝕜 (op A (crR A b x₀ j)) (crR A b x₀ j) /
      inner 𝕜 (crAp A b x₀ j) (crAp A b x₀ j) := rfl

/-- Algorithm 6.20, line 4: `x_{j+1} = x_j + α_j p_j`. -/
theorem crX_succ (j : ℕ) :
    crX A b x₀ (j + 1) = crX A b x₀ j + crAlpha A b x₀ j • crP A b x₀ j := by
  rw [crX, cr_succ]
  rfl

/-- Algorithm 6.20, line 5: `r_{j+1} = r_j - α_j A p_j`. -/
theorem crR_succ (j : ℕ) :
    crR A b x₀ (j + 1) = crR A b x₀ j - crAlpha A b x₀ j • crAp A b x₀ j := by
  rw [crR, cr_succ]
  rfl

theorem crR_succ_eq_crStepR (j : ℕ) : crR A b x₀ (j + 1) = crStepR A (cr A b x₀ j) := by
  rw [crR, cr_succ]
  rfl

/-- Algorithm 6.20, line 6: `β_j = (r_{j+1}, A r_{j+1})/(r_j, A r_j)`. -/
theorem crBeta_eq (j : ℕ) : crBeta A b x₀ j =
    inner 𝕜 (op A (crR A b x₀ (j + 1))) (crR A b x₀ (j + 1)) /
      inner 𝕜 (op A (crR A b x₀ j)) (crR A b x₀ j) := by
  rw [crBeta, crStepBeta_def, crR_succ_eq_crStepR]
  rfl

/-- Algorithm 6.20, line 7: `p_{j+1} = r_{j+1} + β_j p_j`. -/
theorem crP_succ (j : ℕ) :
    crP A b x₀ (j + 1) = crR A b x₀ (j + 1) + crBeta A b x₀ j • crP A b x₀ j := by
  rw [crP, cr_succ, crR_succ_eq_crStepR]
  rfl

/-- Algorithm 6.20, line 8: `A p_{j+1} = A r_{j+1} + β_j A p_j`. -/
theorem crAp_succ (j : ℕ) :
    crAp A b x₀ (j + 1) = op A (crR A b x₀ (j + 1)) + crBeta A b x₀ j • crAp A b x₀ j := by
  rw [crAp, cr_succ, crR_succ_eq_crStepR]
  rfl

/-! ### Identification with the backbone conjugate residual recurrence -/

private theorem crStepAlpha_eq_CR (hA : (op A).IsSymmetric) (s : CR.State 𝔼) :
    crStepAlpha A (s.x, s.r, s.p, s.q) = CR.alpha (op A) s := by
  rw [crStepAlpha_def, CR.alpha, hA s.r s.r]

private theorem crStepR_eq_CR (hA : (op A).IsSymmetric) (s : CR.State 𝔼) :
    crStepR A (s.x, s.r, s.p, s.q) = (CR.step (op A) s).r := by
  rw [crStepR_def, crStepAlpha_eq_CR A hA s, CR.step]

private theorem crStepBeta_eq_CR (hA : (op A).IsSymmetric) (s : CR.State 𝔼) :
    crStepBeta A (s.x, s.r, s.p, s.q) =
      inner 𝕜 (CR.step (op A) s).r (op A (CR.step (op A) s).r) / inner 𝕜 s.r (op A s.r) := by
  rw [crStepBeta_def, crStepR_eq_CR A hA s, hA s.r s.r, hA (CR.step (op A) s).r]

private theorem crStep_eq_CR (hA : (op A).IsSymmetric) (s : CR.State 𝔼) :
    crStep A (s.x, s.r, s.p, s.q) = ((CR.step (op A) s).x, (CR.step (op A) s).r,
      (CR.step (op A) s).p, (CR.step (op A) s).q) := by
  rw [crStep, crStepAlpha_eq_CR A hA s, crStepR_eq_CR A hA s, crStepBeta_eq_CR A hA s, CR.step]

/-- **The bridge to the backbone**: Algorithm 6.20 is the backbone conjugate residual
recurrence `CR.iterate`. Only the symmetry of `A` is needed, to move `A` across the inner
products in `α_j` and `β_j`. -/
theorem cr_eq_CR (hA : (op A).IsSymmetric) (j : ℕ) :
    cr A b x₀ j = ((CR.iterate (op A) b x₀ j).x, (CR.iterate (op A) b x₀ j).r,
      (CR.iterate (op A) b x₀ j).p, (CR.iterate (op A) b x₀ j).q) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [cr_succ, ih, CR.iterate_succ, crStep_eq_CR A hA]

theorem crX_eq_CR (hA : (op A).IsSymmetric) (j : ℕ) :
    crX A b x₀ j = (CR.iterate (op A) b x₀ j).x := by rw [crX, cr_eq_CR A b x₀ hA]

theorem crR_eq_CR (hA : (op A).IsSymmetric) (j : ℕ) :
    crR A b x₀ j = (CR.iterate (op A) b x₀ j).r := by rw [crR, cr_eq_CR A b x₀ hA]

theorem crP_eq_CR (hA : (op A).IsSymmetric) (j : ℕ) :
    crP A b x₀ j = (CR.iterate (op A) b x₀ j).p := by rw [crP, cr_eq_CR A b x₀ hA]

theorem crAp_eq_CR (hA : (op A).IsSymmetric) (j : ℕ) :
    crAp A b x₀ j = (CR.iterate (op A) b x₀ j).q := by rw [crAp, cr_eq_CR A b x₀ hA]

/-- The vector carried by line 8 really is `A p_j`. -/
theorem crAp_eq_apply_crP (hA : (op A).IsSymmetric) (j : ℕ) :
    crAp A b x₀ j = op A (crP A b x₀ j) := by
  rw [crAp_eq_CR A b x₀ hA, crP_eq_CR A b x₀ hA, CR.q_eq]

/-- The state's residual is the true residual, `r_j = b - A x_j`. -/
theorem crR_eq_residual (hA : (op A).IsSymmetric) (j : ℕ) :
    crR A b x₀ j = b - op A (crX A b x₀ j) := by
  rw [crR_eq_CR A b x₀ hA, crX_eq_CR A b x₀ hA, CR.residual_eq]

/-! ### The invariants of §6.8 -/

variable {A b x₀}

/-- §6.8: the vectors `A p_i` produced by Algorithm 6.20 are orthogonal,
`(A p_i, A p_j) = 0` for `i ≠ j`. -/
theorem inner_crAp_eq_zero (hA : A.PosDef) {i j : ℕ} (h : i ≠ j) :
    inner 𝕜 (crAp A b x₀ i) (crAp A b x₀ j) = 0 := by
  have hs := (isSymmetricCoercive_op_of_posDef hA).isSymmetric
  rw [crAp_eq_apply_crP A b x₀ hs, crAp_eq_apply_crP A b x₀ hs, crP_eq_CR A b x₀ hs,
    crP_eq_CR A b x₀ hs]
  exact CR.inner_apply_direction_eq_zero b x₀ (isSymmetricCoercive_op_of_posDef hA) h

/-- §6.8: the residuals produced by Algorithm 6.20 are `A`-orthogonal (conjugate),
`(r_i, A r_j) = 0` for `i ≠ j`. -/
theorem inner_apply_crR_eq_zero (hA : A.PosDef) {i j : ℕ} (h : i ≠ j) :
    inner 𝕜 (crR A b x₀ i) (op A (crR A b x₀ j)) = 0 := by
  have hs := (isSymmetricCoercive_op_of_posDef hA).isSymmetric
  rw [crR_eq_CR A b x₀ hs, crR_eq_CR A b x₀ hs]
  exact CR.inner_residual_apply_residual_eq_zero b x₀ (isSymmetricCoercive_op_of_posDef hA) h

/-- `(r_i, A p_j) = 0` for `j < i`: the residual is orthogonal to the earlier `A p_j`, which is
the Petrov–Galerkin condition behind the minimization. -/
theorem inner_crR_crAp_eq_zero (hA : A.PosDef) {i j : ℕ} (h : j < i) :
    inner 𝕜 (crR A b x₀ i) (crAp A b x₀ j) = 0 := by
  have hs := (isSymmetricCoercive_op_of_posDef hA).isSymmetric
  rw [crAp_eq_apply_crP A b x₀ hs, crR_eq_CR A b x₀ hs, crP_eq_CR A b x₀ hs]
  exact CR.inner_residual_apply_direction_eq_zero b x₀ (isSymmetricCoercive_op_of_posDef hA) h

/-- The directions of Algorithm 6.20 span the Krylov subspaces. -/
theorem span_crP_eq (hA : A.PosDef) (m : ℕ) :
    Submodule.span 𝕜 (Set.range fun i : Fin m => crP A b x₀ (i : ℕ)) =
      krylov A (r₀ A b x₀) m := by
  have hs := (isSymmetricCoercive_op_of_posDef hA).isSymmetric
  rw [krylov_eq]
  simp only [crP_eq_CR A b x₀ hs]
  exact CR.span_direction_eq b x₀ (isSymmetricCoercive_op_of_posDef hA) m

/-- **Algorithm 6.20 realises the minimal-residual specification**: this is the sense in which
§6.8 obtains the conjugate residual algorithm from GMRES for Hermitian `A`. -/
theorem crX_isMinResIterate (hA : A.PosDef) (j : ℕ) :
    Krylov.IsMinResIterate (op A) b x₀ j (crX A b x₀ j) := by
  rw [crX_eq_CR A b x₀ (isSymmetricCoercive_op_of_posDef hA).isSymmetric]
  exact CR.isMinResIterate b x₀ (isSymmetricCoercive_op_of_posDef hA) j

/-- The minimal-residual property in the book's Hermitian (possibly indefinite) generality: as
long as Algorithm 6.20 does not divide by zero, `x_j` minimizes the residual over
`x_0 + 𝒦_j(A, r_0)`. -/
theorem crX_isMinResIterate_of_no_breakdown (hA : (op A).IsSymmetric) {j : ℕ}
    (h1 : ∀ i < j, inner 𝕜 (op A (crR A b x₀ i)) (crR A b x₀ i) ≠ 0)
    (h2 : ∀ i < j, crAp A b x₀ i ≠ 0) :
    Krylov.IsMinResIterate (op A) b x₀ j (crX A b x₀ j) := by
  rw [crX_eq_CR A b x₀ hA]
  refine CR.isMinResIterate_of_no_breakdown b x₀ hA j (fun i hi => ?_) fun i hi => ?_
  · rw [← crR_eq_CR A b x₀ hA, ← hA (crR A b x₀ i) (crR A b x₀ i)]
    exact h1 i hi
  · rw [← crAp_eq_CR A b x₀ hA]
    exact h2 i hi

/-- **CR coincides with GMRES**: for positive definite `A`, Algorithm 6.20 and Algorithm 6.9
produce the same approximation at every step, both being the minimal-residual iterate. -/
theorem crX_eq_gmresFixed (hA : A.PosDef) {j : ℕ} (hj : j ≤ grade A (v₁ A b x₀)) :
    crX A b x₀ j = gmresFixed A b x₀ j := by
  obtain ⟨z, -, hz⟩ :=
    Krylov.existsUnique_isMinResIterate_of_injective (injective_op_of_isUnit hA.isUnit) b x₀ j
  rw [hz _ (crX_isMinResIterate hA j),
    hz _ (gmresFixed_isMinResIterate A b x₀ hj (isUnit_R_of_isUnit A b x₀ hA.isUnit hj))]

end General

/-! ### The results of §6.8, in the book's real setting -/

section BookResults

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {b x₀ : EuclideanSpace ℝ (Fin n)}

/-- **§6.8**, the invariants of **Algorithm 6.20** for a symmetric positive definite `A`: the
residuals are `A`-orthogonal, `(r_i, A r_j) = 0` for `i ≠ j`, and the vectors `A p_i` are
orthogonal, `(A p_i, A p_j) = 0` for `i ≠ j`. -/
theorem algorithm_6_20_orthogonality (hA : A.PosDef) {i j : ℕ} (h : i ≠ j) :
    inner ℝ (crR A b x₀ i) (op A (crR A b x₀ j)) = 0 ∧
      inner ℝ (op A (crP A b x₀ i)) (op A (crP A b x₀ j)) = 0 := by
  have hs := (isSymmetricCoercive_op_of_posDef hA).isSymmetric
  refine ⟨inner_apply_crR_eq_zero hA h, ?_⟩
  rw [← crAp_eq_apply_crP A b x₀ hs, ← crAp_eq_apply_crP A b x₀ hs]
  exact inner_crAp_eq_zero hA h

/-- **§6.8**: Algorithm 6.20 is the Hermitian case of GMRES — its iterate minimizes the residual
norm over `x_0 + 𝒦_j(A, r_0)`. -/
theorem algorithm_6_20_isMinResIterate (hA : A.PosDef) (j : ℕ) :
    Krylov.IsMinResIterate (op A) b x₀ j (crX A b x₀ j) :=
  crX_isMinResIterate hA j

/-- **§6.8**: for Hermitian, possibly indefinite, `A` the conjugate residual iterate still
minimizes the residual, as long as the algorithm does not break down. -/
theorem algorithm_6_20_isMinResIterate_of_no_breakdown (hA : A.IsSymm) {j : ℕ}
    (h1 : ∀ i < j, inner ℝ (op A (crR A b x₀ i)) (crR A b x₀ i) ≠ 0)
    (h2 : ∀ i < j, crAp A b x₀ i ≠ 0) :
    Krylov.IsMinResIterate (op A) b x₀ j (crX A b x₀ j) :=
  crX_isMinResIterate_of_no_breakdown (isSymmetric_op_of_isSymm hA) h1 h2

/-- **§6.8**: the conjugate residual algorithm and full GMRES compute the same approximations
for a symmetric positive definite `A`. -/
theorem algorithm_6_20_eq_alg_6_9 (hA : A.PosDef) {j : ℕ} (hj : j ≤ grade A (v₁ A b x₀)) :
    crX A b x₀ j = gmresFixed A b x₀ j :=
  crX_eq_gmresFixed hA hj

end BookResults

end SaadSparse.Chapter06

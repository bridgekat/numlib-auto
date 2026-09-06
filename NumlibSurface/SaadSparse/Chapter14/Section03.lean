import Numlib.LinearSolve.DomainDecomposition.Schwarz
import NumlibSurface.SaadSparse.Common

/-!
# Saad §14.3: the Schwarz alternating procedures

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §14.3.

The data of the section are index sets `S_i ⊆ {1, …, n}`, not necessarily disjoint, the boolean
restriction matrices `R_i` of §14.3.1 (`restrictSubset`), the local matrices `A_i = R_i A R_iᵀ`
(`localMatrix`), and the operators `T_i = R_iᵀ A_i⁻¹ R_i` of (14.31) (`subdomainInverse`) and
`P_i = T_i A` of (14.24) (`subdomainProjector`).

Everything rests on one identification, `subdomainProjector_eq_energyProjection`: for a symmetric
positive definite `A`, `P_i` **is** the `A`-orthogonal projector onto `Ran(R_iᵀ) = span {e_j :
j ∈ S_i}` (`subdomainSpace`).  The whole convergence theory is then read off
`Numlib/LinearSolve/DomainDecomposition/Schwarz.lean`, whose statements are about the orthogonal
projectors of an inner product space, applied in the energy space of `A`.

* §14.3.1–14.3.3: `multiplicativeSweep` is (14.25), `Q_s` its error operator (14.26), and
  `additiveSweep` the additive procedure.  `error_multiplicativeSweep` is the meaning of `Q_s`,
  `proposition_14_3` the fixed-point form (14.27)–(14.28), and `lemma_14_4` the recurrences
  (14.32)–(14.35) that make Algorithms 14.4 and 14.5 run without `A⁻¹`.
* §14.3.4: `A_J` is the additive Schwarz operator (14.37), `theorem_14_5` and `theorem_14_6` the
  two upper bounds on `λ_max(A_J)`, `IsStableDecomposition` and `IsStrengthenedCauchySchwarz`
  Assumptions 1 and 2, `theorem_14_7` the lower bound `λ_min(A_J) ≥ 1/K₀`, `equation_14_39` the
  telescoping identity of a multiplicative sweep, and `lemma_14_8` and `theorem_14_9` its
  contraction rate.

Indices are `0`-based: the book's `i = 1, …, s` is `i ∈ Finset.range s`, and Saad's `card` of the
family is the cutoff `s`.  `(A u, u)` is written `energyInner A u u`, and `‖u‖_A` is
`energyNorm A u`; over `ℝ` these are Saad's own quantities, and over `ℂ` they are the
Hermitian ones.

Theorem 14.2 is not formalized: it is a translation statement about the vertex-based partitioning
of §14.2.3, whose block structure (14.8)–(14.14) nothing else in the book or the library uses.
-/

open Matrix Finset

open scoped ComplexOrder SaadSparse

namespace SaadSparse.Chapter14

variable {n : ℕ}

/-! ### §14.3.1: the restriction matrices and the subdomain spaces -/

/-- §14.3.1: the boolean restriction matrix `R_S` of an index set `S ⊆ {1, …, n}`, whose rows are
the `e_jᵀ` for `j ∈ S`.  `R_S x` is the sub-vector of `x` indexed by `S`, and `R_Sᵀ y` extends a
vector on `S` by zero. -/
def restrictSubset (𝕜 : Type*) [RCLike 𝕜] (S : Finset (Fin n)) : Matrix ↥S (Fin n) 𝕜 :=
  Matrix.of fun i j => if (i : Fin n) = j then 1 else 0

/-- §14.3.1: the subspace `Ran(R_Sᵀ) = span {e_j : j ∈ S}` of the vectors supported on `S`, on
which the subdomain problem of the Schwarz procedure is solved. -/
def subdomainSpace (𝕜 : Type*) [RCLike 𝕜] (S : Finset (Fin n)) :
    Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n)) :=
  Submodule.span 𝕜 (Set.range fun j : ↥S => EuclideanSpace.single (j : Fin n) (1 : 𝕜))

variable {𝕜 : Type*} [RCLike 𝕜]

theorem restrictSubset_apply (S : Finset (Fin n)) (i : ↥S) (j : Fin n) :
    restrictSubset 𝕜 S i j = if (i : Fin n) = j then 1 else 0 := rfl

/-- The rows of `R_S` are orthonormal: `R_S R_Sᵀ = I`.  In particular `R_Sᵀ` has full column
rank, which is what makes the local matrix `A_S` nonsingular. -/
theorem restrictSubset_mul_transpose (S : Finset (Fin n)) :
    restrictSubset 𝕜 S * (restrictSubset 𝕜 S)ᵀ = 1 := by
  ext i k
  rw [Matrix.mul_apply]
  simp only [restrictSubset_apply, Matrix.transpose_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (i : Fin n)]
  · have h : ((k : Fin n) = (i : Fin n)) ↔ i = k := by
      rw [Subtype.ext_iff]; exact eq_comm
    simp [h]
  · exact fun j _ hj => by rw [ite_eq_right (Ne.symm hj), zero_mul]
  · exact fun h => absurd (Finset.mem_univ (i : Fin n)) h

/-- The entries of `R_S` are `0` and `1`, so its conjugate transpose is its transpose: the
adjoint of the extension `R_Sᵀ` is the restriction `R_S`. -/
theorem conjTranspose_transpose_restrictSubset (S : Finset (Fin n)) :
    ((restrictSubset 𝕜 S)ᵀ)ᴴ = restrictSubset 𝕜 S := by
  ext i j
  rw [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  simp only [restrictSubset_apply]
  split_ifs <;> simp

/-- **Saad §14.3.1**: the range of the extension `R_Sᵀ` is the span of the coordinate vectors of
`S`.  This is the subspace on which the local problem is posed. -/
theorem range_restrictSubset_transpose (S : Finset (Fin n)) :
    LinearMap.range (Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ) = subdomainSpace 𝕜 S := by
  have hbasis : (⊤ : Submodule 𝕜 (EuclideanSpace 𝕜 ↥S))
      = Submodule.span 𝕜 (Set.range fun j : ↥S => EuclideanSpace.single j (1 : 𝕜)) := by
    have h := (EuclideanSpace.basisFun (ι := ↥S) (𝕜 := 𝕜)).toBasis.span_eq
    rw [← h]
    congr 1
    exact congrArg Set.range (funext fun j => by
      rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply])
  have happ : ∀ j : ↥S, Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ
      (EuclideanSpace.single j (1 : 𝕜)) = EuclideanSpace.single (j : Fin n) (1 : 𝕜) := by
    intro j
    have hcol : (restrictSubset 𝕜 S)ᵀ *ᵥ Pi.single j (1 : 𝕜)
        = Pi.single (j : Fin n) (1 : 𝕜) := by
      rw [Matrix.mulVec_single_one]
      funext k
      rw [Matrix.col_apply, Matrix.transpose_apply, restrictSubset_apply, Pi.single_apply]
      by_cases h : (j : Fin n) = k
      · simp [h]
      · simp [h, Ne.symm h]
    rw [Matrix.toLpLin_apply, PiLp.ofLp_single, hcol, PiLp.toLp_single]
  rw [LinearMap.range_eq_map, hbasis, Submodule.map_span, ← Set.range_comp, subdomainSpace]
  exact congrArg _ (congrArg Set.range (funext happ))

/-! ### §14.3.1: the local matrices and the subdomain projectors -/

variable {A : Matrix (Fin n) (Fin n) 𝕜}

/-- §14.3.1: the local matrix `A_S = R_S A R_Sᵀ` of the subdomain `S`, the submatrix of `A` on
the rows and columns of `S`. -/
def localMatrix (A : Matrix (Fin n) (Fin n) 𝕜) (S : Finset (Fin n)) : Matrix ↥S ↥S 𝕜 :=
  restrictSubset 𝕜 S * A * (restrictSubset 𝕜 S)ᵀ

/-- (14.31): the subdomain solve `T_S = R_Sᵀ A_S⁻¹ R_S`, which restricts a residual to `S`,
solves the local system there, and extends the correction by zero. -/
noncomputable def subdomainInverse (A : Matrix (Fin n) (Fin n) 𝕜) (S : Finset (Fin n)) :
    Matrix (Fin n) (Fin n) 𝕜 :=
  (restrictSubset 𝕜 S)ᵀ * (localMatrix A S)⁻¹ * restrictSubset 𝕜 S

/-- (14.24): the subdomain projector `P_S = R_Sᵀ A_S⁻¹ R_S A = T_S A`. -/
noncomputable def subdomainProjector (A : Matrix (Fin n) (Fin n) 𝕜) (S : Finset (Fin n)) :
    Matrix (Fin n) (Fin n) 𝕜 :=
  subdomainInverse A S * A

/-- (14.24) and (14.31): `P_S = T_S A`. -/
theorem subdomainProjector_eq_mul (A : Matrix (Fin n) (Fin n) 𝕜) (S : Finset (Fin n)) :
    subdomainProjector A S = subdomainInverse A S * A := rfl

/-- `(I - M) z = z - M z`: unfolding a projector complement one application at a time, which is
what every error recurrence of the section needs. -/
theorem toEuclideanLin_one_sub_apply (M : Matrix (Fin n) (Fin n) 𝕜)
    (z : EuclideanSpace 𝕜 (Fin n)) : ((1 - M) ⬝ z) = z - (M ⬝ z) := by
  have hmat : Matrix.toEuclideanLin (1 - M)
      = (LinearMap.id : EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n))
        - Matrix.toEuclideanLin M := by
    rw [map_sub, Matrix.toLpLin_one]
  rw [hmat, LinearMap.sub_apply, LinearMap.id_apply]

/-- A symmetric positive definite matrix is a symmetric coercive operator; this is the hypothesis
under which the energy inner product `(x, y)_A` of §14.3.4 exists. -/
theorem isSymmetricCoercive_toEuclideanLin (hA : A.PosDef) :
    (Matrix.toEuclideanLin A).IsSymmetricCoercive :=
  (Matrix.posDef_iff_isSymmetricCoercive A).1 hA

/-- The adjoint of the extension `R_Sᵀ` is the restriction `R_S`. -/
theorem adjoint_toEuclideanLin_transpose (S : Finset (Fin n)) :
    LinearMap.adjoint (Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ)
      = Matrix.toEuclideanLin (restrictSubset 𝕜 S) := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, conjTranspose_transpose_restrictSubset]

/-- The extension `R_Sᵀ` is injective, since `R_S R_Sᵀ = I`. -/
theorem injective_toEuclideanLin_transpose (S : Finset (Fin n)) :
    Function.Injective (Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ) := by
  have h : Matrix.toEuclideanLin (restrictSubset 𝕜 S) ∘ₗ
      Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ = LinearMap.id := by
    rw [← Matrix.toLpLin_mul_same, restrictSubset_mul_transpose, Matrix.toLpLin_one]
  exact Function.LeftInverse.injective (g := Matrix.toEuclideanLin (restrictSubset 𝕜 S))
    fun x => DFunLike.congr_fun h x

/-- The local matrix `A_S = R_S A R_Sᵀ` is the Galerkin coarse operator of the extension `R_Sᵀ`:
this is the sentence that makes the whole section a specialization of the abstract theory. -/
theorem galerkinCoarse_eq (A : Matrix (Fin n) (Fin n) 𝕜) (S : Finset (Fin n)) :
    Multigrid.galerkinCoarse (Matrix.toEuclideanLin A)
        (Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ)
      = Matrix.toEuclideanLin (localMatrix A S) := by
  have hdef : Multigrid.galerkinCoarse (Matrix.toEuclideanLin A)
      (Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ)
        = LinearMap.adjoint (Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ) ∘ₗ
            Matrix.toEuclideanLin A ∘ₗ Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ := rfl
  rw [hdef, adjoint_toEuclideanLin_transpose, localMatrix, Matrix.toLpLin_mul_same,
    Matrix.toLpLin_mul_same, LinearMap.comp_assoc]

/-- **The local problem is well posed**: for symmetric positive definite `A` the local matrix
`A_S` is symmetric positive definite, so `A_S⁻¹` in (14.24) makes sense. -/
theorem posDef_localMatrix (hA : A.PosDef) (S : Finset (Fin n)) : (localMatrix A S).PosDef := by
  rw [Matrix.posDef_iff_isSymmetricCoercive, ← galerkinCoarse_eq]
  exact Multigrid.galerkinCoarse_isSymmetricCoercive (isSymmetricCoercive_toEuclideanLin hA)
    (injective_toEuclideanLin_transpose S)

/-- The subspace argument of `Schwarz.energyProjection` may be rewritten. -/
private theorem energyProjection_congr {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {T : E →ₗ[𝕜] E} (hT : T.IsSymmetricCoercive)
    {K L : Submodule 𝕜 E} [FiniteDimensional 𝕜 K] [FiniteDimensional 𝕜 L] (h : K = L) :
    Schwarz.energyProjection T hT K = Schwarz.energyProjection T hT L := by
  subst h; rfl

/-- **Saad (14.24)**: the subdomain projector `P_S = R_Sᵀ A_S⁻¹ R_S A` is the `A`-orthogonal
projector onto the subdomain space `span {e_j : j ∈ S}`.  Every statement of §14.3 follows from
this identification and the abstract Schwarz theory. -/
theorem subdomainProjector_eq_energyProjection (hA : A.PosDef) (S : Finset (Fin n)) :
    Matrix.toEuclideanLin (subdomainProjector A S)
      = Schwarz.energyProjection (Matrix.toEuclideanLin A)
          (isSymmetricCoercive_toEuclideanLin hA) (subdomainSpace 𝕜 S) := by
  have hinv : localMatrix A S * (localMatrix A S)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (posDef_localMatrix hA S).isUnit)
  refine LinearMap.ext fun x => ?_
  have hy : Multigrid.galerkinCoarse (Matrix.toEuclideanLin A)
      (Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ)
      (Matrix.toEuclideanLin ((localMatrix A S)⁻¹ * restrictSubset 𝕜 S * A) x)
        = LinearMap.adjoint (Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ)
            (Matrix.toEuclideanLin A x) := by
    rw [galerkinCoarse_eq, adjoint_toEuclideanLin_transpose, ← LinearMap.comp_apply,
      ← Matrix.toLpLin_mul_same, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hinv, Matrix.one_mul,
      Matrix.toLpLin_mul_same]
    rfl
  have hproj := Schwarz.energyProjection_eq_of_galerkinCoarse (Matrix.toEuclideanLin A)
    (isSymmetricCoercive_toEuclideanLin hA) (Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ) hy
  rw [energyProjection_congr (isSymmetricCoercive_toEuclideanLin hA)
    (range_restrictSubset_transpose (𝕜 := 𝕜) S).symm, hproj, ← LinearMap.comp_apply,
    ← Matrix.toLpLin_mul_same]
  rw [subdomainProjector, subdomainInverse, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]

/-- Saad's computation that `P_S² = P_S`: the subdomain projector is idempotent. -/
theorem subdomainProjector_mul_self (hA : A.PosDef) (S : Finset (Fin n)) :
    subdomainProjector A S * subdomainProjector A S = subdomainProjector A S := by
  refine (Matrix.toEuclideanLin (𝕜 := 𝕜)).injective ?_
  rw [Matrix.toLpLin_mul_same, subdomainProjector_eq_energyProjection hA S]
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply]
  exact Schwarz.energyProjection_apply_of_mem (Matrix.toEuclideanLin A)
    (isSymmetricCoercive_toEuclideanLin hA) (subdomainSpace 𝕜 S)
    (Schwarz.energyProjection_apply_mem (Matrix.toEuclideanLin A)
      (isSymmetricCoercive_toEuclideanLin hA) (subdomainSpace 𝕜 S) x)

/-! ### §14.3.2–14.3.3: the multiplicative and additive procedures -/

section Procedures

variable (A : Matrix (Fin n) (Fin n) 𝕜) (S : ℕ → Finset (Fin n))

/-- **(14.25)**, the multiplicative Schwarz procedure: sweeping over the subdomains
`S 0, …, S (i-1)` in order, each correction `x ← x + R_jᵀ A_j⁻¹ R_j (b - A x)` being computed
from the iterate the previous one produced. -/
noncomputable def multiplicativeSweep (b : EuclideanSpace 𝕜 (Fin n)) :
    ℕ → EuclideanSpace 𝕜 (Fin n) → EuclideanSpace 𝕜 (Fin n)
  | 0, x => x
  | i + 1, x => multiplicativeSweep b i x +
      (subdomainInverse A (S i) ⬝ (b - (A ⬝ multiplicativeSweep b i x)))

@[simp]
theorem multiplicativeSweep_zero (b x : EuclideanSpace 𝕜 (Fin n)) :
    multiplicativeSweep A S b 0 x = x := rfl

theorem multiplicativeSweep_succ (b : EuclideanSpace 𝕜 (Fin n)) (i : ℕ)
    (x : EuclideanSpace 𝕜 (Fin n)) :
    multiplicativeSweep A S b (i + 1) x = multiplicativeSweep A S b i x +
      (subdomainInverse A (S i) ⬝ (b - (A ⬝ multiplicativeSweep A S b i x))) := rfl

/-- **§14.3.3**, the additive Schwarz procedure: all `s` corrections are computed from the same
iterate and added at once, `x ← x + ∑_{i<s} T_i (b - A x)`. -/
noncomputable def additiveSweep (s : ℕ) (b x : EuclideanSpace 𝕜 (Fin n)) :
    EuclideanSpace 𝕜 (Fin n) :=
  x + ∑ i ∈ Finset.range s, (subdomainInverse A (S i) ⬝ (b - (A ⬝ x)))

/-- **(14.26)**: the error propagation operator `Q_s = (I - P_{s-1}) ⋯ (I - P_0)` of one
multiplicative Schwarz sweep. -/
noncomputable def Q_s : ℕ → Matrix (Fin n) (Fin n) 𝕜
  | 0 => 1
  | i + 1 => (1 - subdomainProjector A (S i)) * Q_s i

@[simp]
theorem Q_s_zero : Q_s A S 0 = 1 := rfl

theorem Q_s_succ (i : ℕ) :
    Q_s A S (i + 1) = (1 - subdomainProjector A (S i)) * Q_s A S i := rfl

/-- **(14.37)**: the additive Schwarz operator `A_J = ∑_{i<s} P_i`. -/
noncomputable def A_J (s : ℕ) : Matrix (Fin n) (Fin n) 𝕜 :=
  ∑ i ∈ Finset.range s, subdomainProjector A (S i)

/-- The additive Schwarz preconditioner `M⁻¹ = ∑ T_i` satisfies `M⁻¹ A = A_J`. -/
theorem sum_subdomainInverse_mul (s : ℕ) :
    (∑ i ∈ Finset.range s, subdomainInverse A (S i)) * A = A_J A S s := by
  rw [A_J, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => (subdomainProjector_eq_mul A (S i)).symm

/-- **(14.26)**: `Q_s` is the error propagation operator of the multiplicative sweep — sweeping
over `S 0, …, S (s-1)` multiplies the error by `Q_s`.  No hypothesis on `A` is needed: this is
the algebra of the corrections, not their optimality. -/
theorem error_multiplicativeSweep {b xstar : EuclideanSpace 𝕜 (Fin n)}
    (hstar : (A ⬝ xstar) = b) (s : ℕ) (x : EuclideanSpace 𝕜 (Fin n)) :
    xstar - multiplicativeSweep A S b s x = (Q_s A S s ⬝ (xstar - x)) := by
  induction s with
  | zero => rw [multiplicativeSweep_zero, Q_s_zero, Matrix.toLpLin_one, LinearMap.id_apply]
  | succ i ih =>
      have hz : b - (A ⬝ multiplicativeSweep A S b i x)
          = (A ⬝ (xstar - multiplicativeSweep A S b i x)) := by rw [map_sub, hstar]
      have hstep : xstar - multiplicativeSweep A S b (i + 1) x
          = ((1 - subdomainProjector A (S i)) ⬝
              (xstar - multiplicativeSweep A S b i x)) := by
        rw [multiplicativeSweep_succ, hz, toEuclideanLin_one_sub_apply,
          subdomainProjector_eq_mul, Matrix.toLpLin_mul_same, LinearMap.comp_apply]
        abel
      rw [hstep, ih, Q_s_succ, Matrix.toLpLin_mul_same, LinearMap.comp_apply]

/-- **Proposition 14.3**: one multiplicative Schwarz sweep is one step of the fixed-point
iteration `x ← x + M⁻¹(b - A x)` for the preconditioned system, with `M⁻¹ = (I - Q_s) A⁻¹`
(14.28) and hence `M⁻¹ A = I - Q_s` (14.27); and one additive Schwarz step is the same iteration
with `M⁻¹ = ∑ T_i`, whose preconditioned operator `M⁻¹ A` is the additive Schwarz operator
`A_J` of (14.37). -/
theorem proposition_14_3 (hA : A.PosDef) {b xstar : EuclideanSpace 𝕜 (Fin n)}
    (hstar : (A ⬝ xstar) = b) (s : ℕ) (x : EuclideanSpace 𝕜 (Fin n)) :
    multiplicativeSweep A S b s x = x + (((1 - Q_s A S s) * A⁻¹) ⬝ (b - (A ⬝ x)))
      ∧ additiveSweep A S s b x
          = x + ((∑ i ∈ Finset.range s, subdomainInverse A (S i)) ⬝ (b - (A ⬝ x)))
      ∧ (∑ i ∈ Finset.range s, subdomainInverse A (S i)) * A = A_J A S s := by
  have hinv : A⁻¹ * A = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hA.isUnit)
  refine ⟨?_, ?_, sum_subdomainInverse_mul A S s⟩
  · have herr := error_multiplicativeSweep A S hstar s x
    have hres : b - (A ⬝ x) = (A ⬝ (xstar - x)) := by rw [map_sub, hstar]
    rw [hres, ← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, mul_assoc, hinv, mul_one,
      toEuclideanLin_one_sub_apply, ← herr]
    abel
  · rw [additiveSweep, map_sum, LinearMap.sum_apply]

end Procedures

/-! ### §14.3.2: Lemma 14.4, the recurrences of Algorithms 14.4 and 14.5 -/

section Lemma144

variable (A : Matrix (Fin n) (Fin n) 𝕜) (S : ℕ → Finset (Fin n))

/-- **(14.35)**: what a multiplicative sweep adds to the iterate is `∑_{i<s} P_i Q_i`. -/
theorem one_sub_Q_s_eq_sum (s : ℕ) :
    1 - Q_s A S s = ∑ j ∈ Finset.range s, subdomainProjector A (S j) * Q_s A S j := by
  induction s with
  | zero => simp
  | succ s ih =>
      rw [Q_s_succ, Finset.sum_range_succ, ← ih]
      noncomm_ring

/-- **Lemma 14.4**: with `Z_i = I - Q_i`, `M_i = Z_i A⁻¹` and `T_i = R_iᵀ A_i⁻¹ R_i`, the
recurrences `Z_{i+1} = Z_i + P_i (I - Z_i)` of (14.32) and `M_{i+1} = M_i + T_i (I - A M_i)` of
(14.33), together with the expansion (14.35) `I - Q_s = ∑_{j<s} P_j Q_{j}`.  The second
recurrence is Algorithm 14.5: it applies `M⁻¹` without ever forming `A⁻¹`. -/
theorem lemma_14_4 (hA : A.PosDef) (i s : ℕ) :
    1 - Q_s A S (i + 1)
        = (1 - Q_s A S i) + subdomainProjector A (S i) * (1 - (1 - Q_s A S i))
      ∧ (1 - Q_s A S (i + 1)) * A⁻¹
          = (1 - Q_s A S i) * A⁻¹
            + subdomainInverse A (S i) * (1 - A * ((1 - Q_s A S i) * A⁻¹))
      ∧ 1 - Q_s A S s = ∑ j ∈ Finset.range s, subdomainProjector A (S j) * Q_s A S j := by
  have hAA : A * A⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hA.isUnit)
  have hPA : subdomainProjector A (S i) * A⁻¹ = subdomainInverse A (S i) := by
    rw [subdomainProjector_eq_mul, mul_assoc, hAA, mul_one]
  have h1 : 1 - Q_s A S (i + 1)
      = (1 - Q_s A S i) + subdomainProjector A (S i) * (1 - (1 - Q_s A S i)) := by
    rw [Q_s_succ]; noncomm_ring
  refine ⟨h1, ?_, one_sub_Q_s_eq_sum A S s⟩
  calc (1 - Q_s A S (i + 1)) * A⁻¹
      = ((1 - Q_s A S i) + subdomainProjector A (S i) * (1 - (1 - Q_s A S i))) * A⁻¹ := by
        rw [h1]
    _ = (1 - Q_s A S i) * A⁻¹ + subdomainProjector A (S i) * A⁻¹
          - subdomainProjector A (S i) * ((1 - Q_s A S i) * A⁻¹) := by noncomm_ring
    _ = (1 - Q_s A S i) * A⁻¹ + subdomainInverse A (S i)
          - subdomainInverse A (S i) * (A * ((1 - Q_s A S i) * A⁻¹)) := by
        rw [hPA, subdomainProjector_eq_mul, mul_assoc]
    _ = (1 - Q_s A S i) * A⁻¹
          + subdomainInverse A (S i) * (1 - A * ((1 - Q_s A S i) * A⁻¹)) := by noncomm_ring

end Lemma144

/-! ### §14.3.4: the convergence theory -/

section Convergence

variable {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.PosDef) (S : ℕ → Finset (Fin n))

include hA

/-- The energy space of `A`: the same vectors, carrying the inner product `(x, y)_A`. -/
private noncomputable abbrev energySpaceType : Type _ :=
  WithEnergy (Matrix.toEuclideanLin A) (isSymmetricCoercive_toEuclideanLin hA)

/-- The subdomain spaces read in the energy inner product, the family the abstract Schwarz
theory is stated over. -/
private noncomputable abbrev energySpace (i : ℕ) : Submodule 𝕜 (energySpaceType hA) :=
  WithEnergy.submoduleMap (Matrix.toEuclideanLin A) (isSymmetricCoercive_toEuclideanLin hA)
    (subdomainSpace 𝕜 (S i))

private theorem energyNorm_eq_norm_equiv (x : EuclideanSpace 𝕜 (Fin n)) :
    energyNorm (Matrix.toEuclideanLin A) x
      = ‖WithEnergy.equiv (Matrix.toEuclideanLin A)
          (isSymmetricCoercive_toEuclideanLin hA) x‖ :=
  (WithEnergy.norm_equiv _ _ x).symm

/-- The bridge: `P_i` read in the energy space is the orthogonal projector onto `V_i`. -/
private theorem equiv_subdomainProjector (i : ℕ) (x : EuclideanSpace 𝕜 (Fin n)) :
    WithEnergy.equiv (Matrix.toEuclideanLin A) (isSymmetricCoercive_toEuclideanLin hA)
        (subdomainProjector A (S i) ⬝ x)
      = (energySpace hA S i).starProjection (WithEnergy.equiv (Matrix.toEuclideanLin A)
          (isSymmetricCoercive_toEuclideanLin hA) x) := by
  rw [subdomainProjector_eq_energyProjection hA]
  exact Schwarz.equiv_energyProjection _ _ _ x

/-- The bridge: `Q_s` read in the energy space is `Schwarz.errorOp`. -/
private theorem equiv_Q_s (s : ℕ) (x : EuclideanSpace 𝕜 (Fin n)) :
    WithEnergy.equiv (Matrix.toEuclideanLin A) (isSymmetricCoercive_toEuclideanLin hA)
        (Q_s A S s ⬝ x)
      = Schwarz.errorOp (energySpace hA S) s (WithEnergy.equiv (Matrix.toEuclideanLin A)
          (isSymmetricCoercive_toEuclideanLin hA) x) := by
  induction s with
  | zero =>
      rw [Q_s_zero, Matrix.toLpLin_one, LinearMap.id_apply, Schwarz.errorOp_zero]
      rfl
  | succ i ih =>
      rw [Q_s_succ, Matrix.toLpLin_mul_same, LinearMap.comp_apply, toEuclideanLin_one_sub_apply,
        map_sub, equiv_subdomainProjector hA S, ih, Schwarz.errorOp_succ_apply]

/-- The bridge: `A_J` read in the energy space is `Schwarz.additiveOperator`. -/
private theorem equiv_A_J (s : ℕ) (x : EuclideanSpace 𝕜 (Fin n)) :
    WithEnergy.equiv (Matrix.toEuclideanLin A) (isSymmetricCoercive_toEuclideanLin hA)
        (A_J A S s ⬝ x)
      = Schwarz.additiveOperator (energySpace hA S) s (WithEnergy.equiv (Matrix.toEuclideanLin A)
          (isSymmetricCoercive_toEuclideanLin hA) x) := by
  have h : (A_J A S s ⬝ x) = ∑ i ∈ Finset.range s, (subdomainProjector A (S i) ⬝ x) := by
    rw [A_J, map_sum, LinearMap.sum_apply]
  rw [h, map_sum, Schwarz.additiveOperator_apply]
  exact Finset.sum_congr rfl fun i _ => equiv_subdomainProjector hA S i x

omit hA in
/-- Eigenvalues of a symmetric operator whose quadratic form lies in `[a, b]`. -/
private theorem re_mem_Icc_of_hasEigenvalue {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] {T : H →ₗ[𝕜] H} {a b : ℝ} (hsym : T.IsSymmetric)
    (hlo : ∀ u, a * ‖u‖ ^ 2 ≤ RCLike.re (inner 𝕜 (T u) u))
    (hhi : ∀ u, RCLike.re (inner 𝕜 (T u) u) ≤ b * ‖u‖ ^ 2) {μ : 𝕜}
    (hμ : Module.End.HasEigenvalue T μ) : RCLike.re μ ∈ Set.Icc a b :=
  LinearMap.IsSymmetricBoundedBy.re_mem_Icc_of_hasEigenvalue ⟨hsym, hlo, hhi⟩ hμ

/-- An eigenvalue of `A_J` is an eigenvalue of the additive Schwarz operator of the energy
space: the two are conjugate by `WithEnergy.equiv`. -/
private theorem hasEigenvalue_additiveOperator (s : ℕ) {μ : 𝕜}
    (hμ : Module.End.HasEigenvalue (Matrix.toEuclideanLin (A_J A S s)) μ) :
    Module.End.HasEigenvalue
      (Schwarz.additiveOperator (energySpace hA S) s : energySpaceType hA →ₗ[𝕜] _) μ := by
  obtain ⟨x, hx, hx0⟩ := hμ.exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff] at hx
  refine Module.End.hasEigenvalue_of_hasEigenvector
    (x := WithEnergy.equiv (Matrix.toEuclideanLin A)
      (isSymmetricCoercive_toEuclideanLin hA) x) ⟨Module.End.mem_eigenspace_iff.2 ?_, ?_⟩
  · rw [ContinuousLinearMap.coe_coe, ← equiv_A_J hA S s x, hx, map_smul]
  · exact fun h => hx0 ((WithEnergy.equiv (Matrix.toEuclideanLin A)
      (isSymmetricCoercive_toEuclideanLin hA)).map_eq_zero_iff.1 h)

/-! #### Theorem 14.5 and Theorem 14.6: the largest eigenvalue of `A_J` -/

/-- **Theorem 14.5** in quadratic-form language: `(A_J u, u)_A ≤ s ‖u‖_A²`, since each `P_i` has
`A`-norm one. -/
theorem re_energyInner_A_J_le (s : ℕ) (u : EuclideanSpace 𝕜 (Fin n)) :
    RCLike.re (energyInner (Matrix.toEuclideanLin A) (A_J A S s ⬝ u) u)
      ≤ s * energyNorm (Matrix.toEuclideanLin A) u ^ 2 := by
  rw [← WithEnergy.inner_equiv (Matrix.toEuclideanLin A)
      (isSymmetricCoercive_toEuclideanLin hA), equiv_A_J hA S, energyNorm_eq_norm_equiv hA]
  exact Schwarz.re_inner_additiveOperator_le (energySpace hA S) s _

/-- The additive Schwarz operator is positive semidefinite in the energy inner product. -/
theorem re_energyInner_A_J_nonneg (s : ℕ) (u : EuclideanSpace 𝕜 (Fin n)) :
    0 ≤ RCLike.re (energyInner (Matrix.toEuclideanLin A) (A_J A S s ⬝ u) u) := by
  rw [← WithEnergy.inner_equiv (Matrix.toEuclideanLin A)
      (isSymmetricCoercive_toEuclideanLin hA), equiv_A_J hA S]
  exact Schwarz.re_inner_additiveOperator_nonneg (energySpace hA S) s _

/-- **(14.37)**: the additive Schwarz operator is self-adjoint for the energy inner product, so
its eigenvalues are real. -/
theorem isSymmetric_energyInner_A_J (s : ℕ) (u v : EuclideanSpace 𝕜 (Fin n)) :
    energyInner (Matrix.toEuclideanLin A) (A_J A S s ⬝ u) v
      = energyInner (Matrix.toEuclideanLin A) u (A_J A S s ⬝ v) := by
  rw [← WithEnergy.inner_equiv (Matrix.toEuclideanLin A)
      (isSymmetricCoercive_toEuclideanLin hA), ← WithEnergy.inner_equiv (Matrix.toEuclideanLin A)
      (isSymmetricCoercive_toEuclideanLin hA), equiv_A_J hA S, equiv_A_J hA S]
  exact Schwarz.additiveOperator_isSymmetric (energySpace hA S) s _ _

/-- **Theorem 14.5**: `λ_max(A_J) ≤ s`, the number of subdomains. -/
theorem theorem_14_5 (s : ℕ) {μ : 𝕜}
    (hμ : Module.End.HasEigenvalue (Matrix.toEuclideanLin (A_J A S s)) μ) :
    RCLike.re μ ≤ s :=
  (re_mem_Icc_of_hasEigenvalue (a := 0)
    (Schwarz.additiveOperator_isSymmetric (energySpace hA S) s)
    (fun u => by simpa using Schwarz.re_inner_additiveOperator_nonneg (energySpace hA S) s u)
    (fun u => Schwarz.re_inner_additiveOperator_le (energySpace hA S) s u)
    (hasEigenvalue_additiveOperator hA S s hμ)).2

/-- Two subdomains with no coupling in `A` span `A`-orthogonal subspaces. -/
private theorem isOrtho_energySpace {i j : ℕ}
    (h : ∀ k ∈ S i, ∀ l ∈ S j, A l k = 0) : energySpace hA S i ⟂ energySpace hA S j := by
  have hgen : ∀ m : ℕ, energySpace hA S m
      = Submodule.span 𝕜 (Set.range fun k : ↥(S m) => WithEnergy.equiv (Matrix.toEuclideanLin A)
            (isSymmetricCoercive_toEuclideanLin hA)
            (EuclideanSpace.single (k : Fin n) (1 : 𝕜))) := by
    intro m
    have h0 : energySpace hA S m = Submodule.map
        (WithEnergy.equiv (Matrix.toEuclideanLin A)
          (isSymmetricCoercive_toEuclideanLin hA)).toLinearMap
        (Submodule.span 𝕜 (Set.range fun k : ↥(S m) =>
          EuclideanSpace.single (k : Fin n) (1 : 𝕜))) := rfl
    rw [h0, Submodule.map_span, ← Set.range_comp]
    rfl
  rw [hgen i, hgen j, Submodule.isOrtho_span]
  rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩
  rw [WithEnergy.inner_equiv, energyInner]
  have hval : (Matrix.toEuclideanLin A (EuclideanSpace.single (k : Fin n) (1 : 𝕜)))
      = WithLp.toLp 2 (fun p => A p (k : Fin n)) := by
    rw [Matrix.toLpLin_apply, PiLp.ofLp_single, Matrix.mulVec_single_one]
    rfl
  rw [hval, EuclideanSpace.inner_single_right]
  simp [h (k : Fin n) k.2 (l : Fin n) l.2]

/-- **Theorem 14.6**: if the subdomains are coloured so that two subdomains of the same colour
have no coupling in `A` — no entry `A_{lk}` with `k` in one and `l` in the other, which for a
positive definite `A` forces them to be disjoint — then `λ_max(A_J) ≤ c`, the number of
colours.  Colouring the interaction graph of the subdomains therefore replaces the crude bound
of Theorem 14.5 by one that does not grow with the number of subdomains. -/
theorem theorem_14_6 {κ : Type*} [Fintype κ] (s : ℕ) (col : ℕ → κ)
    (hcol : ∀ i ∈ Finset.range s, ∀ j ∈ Finset.range s, i ≠ j → col i = col j →
      ∀ k ∈ S i, ∀ l ∈ S j, A l k = 0)
    {μ : 𝕜} (hμ : Module.End.HasEigenvalue (Matrix.toEuclideanLin (A_J A S s)) μ) :
    RCLike.re μ ≤ Fintype.card κ :=
  (re_mem_Icc_of_hasEigenvalue (a := 0)
    (Schwarz.additiveOperator_isSymmetric (energySpace hA S) s)
    (fun u => by simpa using Schwarz.re_inner_additiveOperator_nonneg (energySpace hA S) s u)
    (fun u => Schwarz.re_inner_additiveOperator_le_of_coloring (energySpace hA S) s col
      (fun i hi j hj hij hc => isOrtho_energySpace hA S (hcol i hi j hj hij hc)) u)
    (hasEigenvalue_additiveOperator hA S s hμ)).2

/-! #### Assumptions 1 and 2 -/

end Convergence

section Assumptions

variable (A : Matrix (Fin n) (Fin n) 𝕜) (S : ℕ → Finset (Fin n))

/-- **Assumption 1** of §14.3.4: every vector splits over the subdomain spaces with
`∑ (A u_i, u_i) ≤ K₀ (A u, u)`.  This is the hypothesis that the subdomains cover the domain
stably; for a finite-element family it is what an overlapping partition of unity provides. -/
def IsStableDecomposition (s : ℕ) (K₀ : ℝ) : Prop :=
  ∀ u : EuclideanSpace 𝕜 (Fin n), ∃ w : ℕ → EuclideanSpace 𝕜 (Fin n),
    (∀ i ∈ Finset.range s, w i ∈ subdomainSpace 𝕜 (S i)) ∧
      ∑ i ∈ Finset.range s, w i = u ∧
        ∑ i ∈ Finset.range s, energyNorm (Matrix.toEuclideanLin A) (w i) ^ 2
          ≤ K₀ * energyNorm (Matrix.toEuclideanLin A) u ^ 2

/-- **Assumption 2** of §14.3.4, (14.40): a strengthened Cauchy–Schwarz inequality with constant
`K₁`, measuring how far the subdomain spaces are from being `A`-orthogonal.  Mutually
`A`-orthogonal subdomains admit `K₁ = 0`, and the plain Cauchy–Schwarz inequality always gives
`K₁ = s`. -/
def IsStrengthenedCauchySchwarz (s : ℕ) (K₁ : ℝ) : Prop :=
  ∀ ps : Finset (ℕ × ℕ), ps ⊆ Finset.range s ×ˢ Finset.range s →
    ∀ u v : ℕ → EuclideanSpace 𝕜 (Fin n),
      (∀ i, u i ∈ subdomainSpace 𝕜 (S i)) → (∀ j, v j ∈ subdomainSpace 𝕜 (S j)) →
      ∑ ij ∈ ps, RCLike.re (energyInner (Matrix.toEuclideanLin A) (u ij.1) (v ij.2))
        ≤ K₁ * Real.sqrt (∑ i ∈ Finset.range s,
              energyNorm (Matrix.toEuclideanLin A) (u i) ^ 2)
            * Real.sqrt (∑ j ∈ Finset.range s,
              energyNorm (Matrix.toEuclideanLin A) (v j) ^ 2)

end Assumptions

section Rates

variable {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.PosDef) (S : ℕ → Finset (Fin n))

include hA

private theorem isStableDecompositionWith_of {s : ℕ} {K₀ : ℝ}
    (h : IsStableDecomposition A S s K₀) :
    Schwarz.IsStableDecompositionWith (energySpace hA S) s K₀ := by
  intro u
  obtain ⟨z, rfl⟩ := (WithEnergy.equiv (Matrix.toEuclideanLin A)
    (isSymmetricCoercive_toEuclideanLin hA)).surjective u
  obtain ⟨w, hmem, hsum, hbd⟩ := h z
  refine ⟨fun i => WithEnergy.equiv (Matrix.toEuclideanLin A)
      (isSymmetricCoercive_toEuclideanLin hA) (w i),
    fun i hi => (WithEnergy.equiv_mem_submoduleMap_iff _ _).2 (hmem i hi), ?_, ?_⟩
  · rw [← map_sum, hsum]
  · simpa only [WithEnergy.norm_equiv] using hbd

private theorem isStrengthenedCauchySchwarzWith_of {s : ℕ} {K₁ : ℝ}
    (h : IsStrengthenedCauchySchwarz A S s K₁) :
    Schwarz.IsStrengthenedCauchySchwarzWith (energySpace hA S) s K₁ := by
  intro ps hps x y
  have hmem : ∀ (z : ℕ → energySpaceType hA) (i : ℕ),
      (WithEnergy.equiv (Matrix.toEuclideanLin A)
          (isSymmetricCoercive_toEuclideanLin hA)).symm
        ((energySpace hA S i).starProjection (z i)) ∈ subdomainSpace 𝕜 (S i) := by
    intro z i
    rw [← WithEnergy.equiv_mem_submoduleMap_iff (Matrix.toEuclideanLin A)
      (isSymmetricCoercive_toEuclideanLin hA), LinearEquiv.apply_symm_apply]
    exact Submodule.starProjection_apply_mem _ _
  have key := h ps hps _ _ (hmem x) (hmem y)
  simpa only [← WithEnergy.inner_equiv (Matrix.toEuclideanLin A)
      (isSymmetricCoercive_toEuclideanLin hA),
    ← WithEnergy.norm_equiv (Matrix.toEuclideanLin A)
      (isSymmetricCoercive_toEuclideanLin hA),
    LinearEquiv.apply_symm_apply] using key

/-- **Theorem 14.7** in quadratic-form language: under Assumption 1, `‖u‖_A²/K₀ ≤ (A_J u, u)_A`.
With `re_energyInner_A_J_le` this encloses the spectrum of `A_J` in `[1/K₀, s]`, so the
condition number of the additive Schwarz preconditioned system is at most `s K₀`. -/
theorem le_re_energyInner_A_J {s : ℕ} {K₀ : ℝ} (hst : IsStableDecomposition A S s K₀)
    (u : EuclideanSpace 𝕜 (Fin n)) :
    energyNorm (Matrix.toEuclideanLin A) u ^ 2 / K₀
      ≤ RCLike.re (energyInner (Matrix.toEuclideanLin A) (A_J A S s ⬝ u) u) := by
  rw [← WithEnergy.inner_equiv (Matrix.toEuclideanLin A)
      (isSymmetricCoercive_toEuclideanLin hA), equiv_A_J hA S, energyNorm_eq_norm_equiv hA]
  exact Schwarz.le_re_inner_additiveOperator (energySpace hA S)
    (isStableDecompositionWith_of hA S hst) _

/-- **Theorem 14.7**: under Assumption 1, `λ_min(A_J) ≥ 1/K₀`.  With Theorem 14.5 the spectrum
of the additive Schwarz preconditioned operator lies in `[1/K₀, s]`, so its condition number is
at most `s K₀` and preconditioned conjugate gradients converge at the corresponding rate. -/
theorem theorem_14_7 {s : ℕ} {K₀ : ℝ} (hst : IsStableDecomposition A S s K₀) {μ : 𝕜}
    (hμ : Module.End.HasEigenvalue (Matrix.toEuclideanLin (A_J A S s)) μ) :
    1 / K₀ ≤ RCLike.re μ :=
  (re_mem_Icc_of_hasEigenvalue (Schwarz.additiveOperator_isSymmetric (energySpace hA S) s)
    (fun u => by
      rw [one_div, inv_mul_eq_div]
      exact Schwarz.le_re_inner_additiveOperator (energySpace hA S)
        (isStableDecompositionWith_of hA S hst) u)
    (fun u => Schwarz.re_inner_additiveOperator_le (energySpace hA S) s u)
    (hasEigenvalue_additiveOperator hA S s hμ)).1

/-- **(14.39)**: `‖Q_s v‖_A² = ‖v‖_A² - ∑_{i<s} ‖P_i Q_i v‖_A²`.  In particular the `A`-norm of
the error does not increase at any substep of a multiplicative sweep. -/
theorem equation_14_39 (s : ℕ) (v : EuclideanSpace 𝕜 (Fin n)) :
    energyNorm (Matrix.toEuclideanLin A) (Q_s A S s ⬝ v) ^ 2
      = energyNorm (Matrix.toEuclideanLin A) v ^ 2
        - ∑ i ∈ Finset.range s, energyNorm (Matrix.toEuclideanLin A)
            (subdomainProjector A (S i) ⬝ (Q_s A S i ⬝ v)) ^ 2 := by
  simp only [energyNorm_eq_norm_equiv hA, equiv_Q_s hA S, equiv_subdomainProjector hA S]
  exact Schwarz.norm_errorOp_sq_eq (energySpace hA S) s _

/-- **Lemma 14.8**, (14.41): under Assumption 2 the projections of a vector are controlled by
the projections of the partially swept vectors,
`∑_i ‖P_i v‖_A² ≤ (1 + K₁)² ∑_i ‖P_i Q_i v‖_A²`. -/
theorem lemma_14_8 {s : ℕ} {K₁ : ℝ} (hcs : IsStrengthenedCauchySchwarz A S s K₁)
    (v : EuclideanSpace 𝕜 (Fin n)) :
    ∑ i ∈ Finset.range s, energyNorm (Matrix.toEuclideanLin A)
        (subdomainProjector A (S i) ⬝ v) ^ 2
      ≤ (1 + K₁) ^ 2 * ∑ i ∈ Finset.range s, energyNorm (Matrix.toEuclideanLin A)
          (subdomainProjector A (S i) ⬝ (Q_s A S i ⬝ v)) ^ 2 := by
  simp only [energyNorm_eq_norm_equiv hA, equiv_Q_s hA S, equiv_subdomainProjector hA S]
  exact Schwarz.sum_norm_starProjection_sq_le (energySpace hA S)
    (isStrengthenedCauchySchwarzWith_of hA S hcs) _

/-- **Theorem 14.9**: under Assumptions 1 and 2 one multiplicative Schwarz sweep contracts the
`A`-norm of the error by `√(1 - 1/(K₀ (1 + K₁)²))`, a rate depending only on the two constants —
in particular not on the number of subdomains. -/
theorem theorem_14_9 {s : ℕ} {K₀ K₁ : ℝ} (hK₀ : 0 < K₀) (hK₁ : 0 ≤ K₁)
    (hst : IsStableDecomposition A S s K₀) (hcs : IsStrengthenedCauchySchwarz A S s K₁)
    (v : EuclideanSpace 𝕜 (Fin n)) :
    energyNorm (Matrix.toEuclideanLin A) (Q_s A S s ⬝ v)
      ≤ Real.sqrt (1 - 1 / (K₀ * (1 + K₁) ^ 2)) * energyNorm (Matrix.toEuclideanLin A) v := by
  simp only [energyNorm_eq_norm_equiv hA, equiv_Q_s hA S]
  exact Schwarz.norm_errorOp_le (energySpace hA S) hK₀ hK₁
    (isStableDecompositionWith_of hA S hst) (isStrengthenedCauchySchwarzWith_of hA S hcs) _

end Rates
end SaadSparse.Chapter14

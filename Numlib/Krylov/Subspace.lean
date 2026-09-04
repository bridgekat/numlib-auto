import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Krylov subspaces

`Krylov.subspace A v m = span {v, A v, …, A^(m-1) v}` for an endomorphism `A` of a module over
a commutative ring, the full Krylov space, the polynomial description
`𝒦_m = {p(A) v | deg p < m}`, and — over a field — the grade of `v` (Saad §6.2, Prop 6.1–6.2;
Saad-eig Prop 6.1–6.3; Choi Def 2.1; Meurant §2.1).
-/

open Polynomial

namespace Krylov

section CommRing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The `m`-th Krylov subspace `𝒦_m(A, v) = span {v, A v, …, A^(m-1) v}`. -/
def subspace (A : Module.End R M) (v : M) (m : ℕ) : Submodule R M :=
  Submodule.span R (Set.range fun i : Fin m => (A ^ (i : ℕ)) v)

/-- Notation `𝒦[A, v] m` for `Krylov.subspace A v m`. -/
scoped notation "𝒦[" A ", " v "] " m:max => Krylov.subspace A v m

/-- The full Krylov space `span {A^i v | i : ℕ}`, the smallest `A`-invariant subspace
containing `v`. -/
def fullSubspace (A : Module.End R M) (v : M) : Submodule R M :=
  Submodule.span R (Set.range fun i : ℕ => (A ^ i) v)

/-- The evaluation map `p ↦ p(A) v`. -/
noncomputable def polyEval (A : Module.End R M) (v : M) : R[X] →ₗ[R] M where
  toFun p := aeval A p v
  map_add' p q := by simp [map_add]
  map_smul' c p := by simp

@[simp]
theorem polyEval_apply (A : Module.End R M) (v : M) (p : R[X]) :
    polyEval A v p = aeval A p v := rfl

variable (A : Module.End R M) (v : M)

instance (m : ℕ) : Module.Finite R (subspace A v m) :=
  Module.Finite.span_of_finite R (Set.finite_range _)

@[simp]
theorem subspace_zero : subspace A v 0 = ⊥ := by
  sorry

theorem subspace_one : subspace A v 1 = R ∙ v := by
  sorry

theorem pow_apply_mem_subspace {i m : ℕ} (h : i < m) : (A ^ i) v ∈ subspace A v m := by
  sorry

theorem self_mem_subspace {m : ℕ} (h : 0 < m) : v ∈ subspace A v m := by
  sorry

theorem subspace_mono : Monotone (subspace A v) := by
  sorry

theorem subspace_le_fullSubspace (m : ℕ) : subspace A v m ≤ fullSubspace A v := by
  sorry

theorem iSup_subspace : ⨆ m, subspace A v m = fullSubspace A v := by
  sorry

theorem map_subspace_le (m : ℕ) : (subspace A v m).map A ≤ subspace A v (m + 1) := by
  sorry

theorem fullSubspace_mem_invtSubmodule : fullSubspace A v ∈ Module.End.invtSubmodule A := by
  sorry

/-- Saad Prop 6.1: `𝒦_m = {p(A) v | deg p < m}`. -/
theorem subspace_eq_map_degreeLT (m : ℕ) :
    subspace A v m = (degreeLT R m).map (polyEval A v) := by
  sorry

theorem mem_subspace_iff_exists_aeval {x : M} {m : ℕ} :
    x ∈ subspace A v m ↔ ∃ p : R[X], p.degree < m ∧ aeval A p v = x := by
  sorry

theorem aeval_apply_mem_subspace {p : R[X]} {m : ℕ} (hp : p.degree < m) :
    aeval A p v ∈ subspace A v m := by
  sorry

/-- `𝒦_{m+1} = 𝒦_m` iff `A^m v ∈ 𝒦_m` iff `𝒦_m` is `A`-invariant (for `m ≥ 1` or `v = 0`). -/
theorem subspace_succ_eq_iff (m : ℕ) :
    subspace A v (m + 1) = subspace A v m ↔ (A ^ m) v ∈ subspace A v m := by
  sorry

theorem mem_invtSubmodule_of_subspace_succ_eq {m : ℕ}
    (h : subspace A v (m + 1) = subspace A v m) :
    subspace A v m ∈ Module.End.invtSubmodule A := by
  sorry

/-- The Krylov subspace of a submodule-restricted operator / of a linear map viewed as
`Module.End` (glue for `E →L[𝕜] E` and matrices). -/
theorem subspace_smul (c : R) (m : ℕ) : subspace A (c • v) m ≤ subspace A v m := by
  sorry

end CommRing

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

variable (A : Module.End K V) (v : V)

/-- The grade of `v` w.r.t. `A`: the dimension of the cyclic subspace `𝒦_∞(A, v)` — equivalently
the least `m` with `A^m v ∈ 𝒦_m` (`grade_eq_sInf`) and the degree of the minimal polynomial of
`v` (Saad §6.2, Liesen–Strakoš). Junk value `0` when the cyclic subspace is infinite-dimensional
(Mathlib's `finrank` convention); the finite-grade hypothesis is
`[FiniteDimensional K (fullSubspace A v)]`, automatic when `V` is finite-dimensional. -/
noncomputable def grade : ℕ := Module.finrank K (fullSubspace A v)

/-- The Krylov sequence stabilizes iff the cyclic subspace is finite-dimensional. -/
theorem finiteDimensional_fullSubspace_iff :
    FiniteDimensional K (fullSubspace A v) ↔ ∃ m, (A ^ m) v ∈ subspace A v m := by
  sorry

/-- `A^m v ∈ 𝒦_m` iff `v` is annihilated by a monic polynomial of degree `m` (Saad §6.2 defines
the grade through the minimal polynomial of `v`). -/
theorem pow_apply_mem_subspace_iff_exists_monic (m : ℕ) :
    (A ^ m) v ∈ subspace A v m ↔ ∃ p : K[X], p.Monic ∧ p.natDegree = m ∧ aeval A p v = 0 := by
  sorry

theorem grade_le_finrank [FiniteDimensional K V] : grade A v ≤ Module.finrank K V := by
  sorry

@[simp]
theorem grade_zero : grade A 0 = 0 := by
  sorry

theorem grade_eq_zero_iff :
    grade A v = 0 ↔ v = 0 ∨ ¬ FiniteDimensional K (fullSubspace A v) := by
  sorry

section FiniteGrade

variable [FiniteDimensional K (fullSubspace A v)]

/-- The grade is the least `m` with `A^m v ∈ 𝒦_m` (Saad's definition). -/
theorem grade_eq_sInf : grade A v = sInf {m | (A ^ m) v ∈ subspace A v m} := by
  sorry

theorem pow_grade_apply_mem : (A ^ grade A v) v ∈ subspace A v (grade A v) := by
  sorry

theorem grade_le_iff {m : ℕ} : grade A v ≤ m ↔ (A ^ m) v ∈ subspace A v m := by
  sorry

theorem pow_apply_notMem_subspace_of_lt_grade {m : ℕ} (h : m < grade A v) :
    (A ^ m) v ∉ subspace A v m := by
  sorry

/-- Saad Prop 6.1: `𝒦_m = 𝒦_grade` for `m ≥ grade`. -/
theorem subspace_eq_of_grade_le {m : ℕ} (h : grade A v ≤ m) :
    subspace A v m = subspace A v (grade A v) := by
  sorry

theorem subspace_grade_eq_fullSubspace : subspace A v (grade A v) = fullSubspace A v := by
  sorry

theorem subspace_grade_mem_invtSubmodule :
    subspace A v (grade A v) ∈ Module.End.invtSubmodule A := by
  sorry

/-- The Krylov vectors `v, A v, …, A^(m-1) v` are linearly independent for `m ≤ grade`. -/
theorem linearIndependent_of_le_grade {m : ℕ} (h : m ≤ grade A v) :
    LinearIndependent K (fun i : Fin m => (A ^ (i : ℕ)) v) := by
  sorry

/-- Saad Prop 6.2: `dim 𝒦_m = min m (grade)`. -/
theorem finrank_subspace (m : ℕ) : Module.finrank K (subspace A v m) = min m (grade A v) := by
  sorry

theorem subspace_strictMono_of_le_grade {m : ℕ} (h : m + 1 ≤ grade A v) :
    subspace A v m < subspace A v (m + 1) := by
  sorry

end FiniteGrade

end Field

end Krylov

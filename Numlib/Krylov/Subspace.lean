import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Krylov subspaces

`Krylov.subspace A v m = span {v, A v, …, A^(m-1) v}` for an endomorphism `A` of a module over
a commutative ring, the full Krylov space, the polynomial description
`𝒦_m = {p(A) v | deg p < m}`, and — over a field — the grade of `v`
(Saad, *Iterative Methods*[^saad-iterative] §6.2, Prop 6.1–6.2;
Saad, *Large Eigenvalue Problems*[^saad-eigenvalue] Prop 6.1–6.3; Choi[^choi] Def 2.1;
Meurant–Strakoš[^meurant-strakos] §2.1).

## References

[^saad-iterative]: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
  SIAM, 2003.
[^saad-eigenvalue]: Yousef Saad, *Numerical Methods for Large Eigenvalue Problems*, 2nd edition,
  SIAM, 2011.
[^choi]: Sou-Cheng Choi, *Iterative Methods for Singular Linear Equations and Least-Squares
  Problems*, PhD thesis, Stanford University, 2006.
[^meurant-strakos]: Gérard Meurant and Zdeněk Strakoš, *The Lanczos and conjugate gradient
  algorithms in finite precision arithmetic*, Acta Numerica (2006), 471–542.
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
  simp [subspace]

theorem subspace_one : subspace A v 1 = R ∙ v := by
  simp [subspace, Set.range_unique]

/-- The generators of `𝒦_m`: `A^i v` lies in it for every `i < m`. -/
theorem pow_apply_mem_subspace {i m : ℕ} (h : i < m) : (A ^ i) v ∈ subspace A v m :=
  Submodule.subset_span ⟨⟨i, h⟩, rfl⟩

theorem self_mem_subspace {m : ℕ} (h : 0 < m) : v ∈ subspace A v m := by
  simpa using pow_apply_mem_subspace A v h

/-- The generating set of `𝒦_m` written as an image of `Set.Iio m`; the form in which it matches
Mathlib's Gram–Schmidt spans. -/
theorem subspace_eq_span_image_Iio (m : ℕ) :
    subspace A v m = Submodule.span R ((fun i : ℕ => (A ^ i) v) '' Set.Iio m) := by
  rw [subspace]
  congr 1
  ext x
  simp only [Set.mem_range, Set.mem_image, Set.mem_Iio, Fin.exists_iff]
  tauto

/-- The Krylov subspaces grow with the number of steps: `𝒦_m ≤ 𝒦_n` for `m ≤ n`. -/
theorem subspace_mono : Monotone (subspace A v) := by
  intro m n h
  simp only [subspace_eq_span_image_Iio]
  exact Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio h))

theorem subspace_le_fullSubspace (m : ℕ) : subspace A v m ≤ fullSubspace A v :=
  Submodule.span_mono <| by rintro _ ⟨i, rfl⟩; exact ⟨(i : ℕ), rfl⟩

theorem iSup_subspace : ⨆ m, subspace A v m = fullSubspace A v := by
  refine le_antisymm (iSup_le fun m => subspace_le_fullSubspace A v m) ?_
  rw [fullSubspace, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact le_iSup (subspace A v) (i + 1) (pow_apply_mem_subspace A v i.lt_succ_self)

theorem map_subspace_le (m : ℕ) : (subspace A v m).map A ≤ subspace A v (m + 1) := by
  rw [subspace, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  have h : A ((A ^ (i : ℕ)) v) = (A ^ ((i : ℕ) + 1)) v := by rw [pow_succ']; rfl
  rw [SetLike.mem_coe, h]
  exact pow_apply_mem_subspace A v (Nat.succ_lt_succ i.2)

/-- `A^k` maps `𝒦_m` into `𝒦_{m+k}`. -/
theorem pow_apply_mem_subspace_of_mem {x : M} {m : ℕ} (hx : x ∈ subspace A v m) (k : ℕ) :
    (A ^ k) x ∈ subspace A v (m + k) := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    have h : (A ^ (k + 1)) x = A ((A ^ k) x) := by rw [pow_succ']; rfl
    rw [h, ← Nat.add_assoc]
    exact map_subspace_le A v (m + k) ⟨_, ih, rfl⟩

/-- The full Krylov space is `A`-invariant; since it also contains `v`, it is the smallest
`A`-invariant subspace that does. -/
theorem fullSubspace_mem_invtSubmodule : fullSubspace A v ∈ Module.End.invtSubmodule A := by
  rw [Module.End.mem_invtSubmodule_iff_map_le, fullSubspace, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  refine Submodule.subset_span ⟨i + 1, ?_⟩
  change (A ^ (i + 1)) v = A ((A ^ i) v)
  rw [pow_succ']
  rfl

@[simp]
theorem fullSubspace_zero : fullSubspace A (0 : M) = ⊥ := by
  rw [fullSubspace, Submodule.span_eq_bot]
  rintro _ ⟨i, rfl⟩
  simp

/-- Saad, *Iterative Methods*, Prop 6.1: `𝒦_m = {p(A) v | deg p < m}`. -/
theorem subspace_eq_map_degreeLT (m : ℕ) :
    subspace A v m = (degreeLT R m).map (polyEval A v) := by
  refine le_antisymm ?_ ?_
  · rw [subspace, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨X ^ (i : ℕ), ?_, by simp⟩
    rw [X_pow_eq_monomial]
    exact monomial_coe_mem_degreeLT i 1
  · rintro _ ⟨p, hp, rfl⟩
    rw [SetLike.mem_coe, mem_degreeLT] at hp
    rcases eq_or_ne p 0 with rfl | hp0
    · simp
    rw [polyEval_apply, aeval_eq_sum_range' ((natDegree_lt_iff_degree_lt hp0).2 hp) A,
      LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun i hi => ?_
    rw [LinearMap.smul_apply]
    exact Submodule.smul_mem _ _ (pow_apply_mem_subspace A v (Finset.mem_range.1 hi))

/-- The polynomial description of `𝒦_m` element by element: `x` lies in it exactly when
`x = p(A) v` for some polynomial `p` of degree `< m`. -/
theorem mem_subspace_iff_exists_aeval {x : M} {m : ℕ} :
    x ∈ subspace A v m ↔ ∃ p : R[X], p.degree < m ∧ aeval A p v = x := by
  rw [subspace_eq_map_degreeLT]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, mem_degreeLT.1 hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, mem_degreeLT.2 hp, rfl⟩

/-- Every polynomial of degree `< m` in `A`, applied to `v`, lands in `𝒦_m`. This is the
direction of the polynomial description that the Krylov methods use. -/
theorem aeval_apply_mem_subspace {p : R[X]} {m : ℕ} (hp : p.degree < m) :
    aeval A p v ∈ subspace A v m :=
  (mem_subspace_iff_exists_aeval A v).2 ⟨p, hp, rfl⟩

/-- `𝒦_{m+1} = 𝒦_m` iff `A^m v ∈ 𝒦_m` iff `𝒦_m` is `A`-invariant (for `m ≥ 1` or `v = 0`). -/
theorem subspace_succ_eq_iff (m : ℕ) :
    subspace A v (m + 1) = subspace A v m ↔ (A ^ m) v ∈ subspace A v m := by
  constructor
  · intro h
    rw [← h]
    exact pow_apply_mem_subspace A v m.lt_succ_self
  · intro h
    refine le_antisymm ?_ (subspace_mono A v m.le_succ)
    rw [subspace, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 i.2) with hi | hi
    · exact pow_apply_mem_subspace A v hi
    · rw [SetLike.mem_coe]
      change (A ^ (i : ℕ)) v ∈ subspace A v m
      rw [hi]
      exact h

theorem mem_invtSubmodule_of_subspace_succ_eq {m : ℕ}
    (h : subspace A v (m + 1) = subspace A v m) :
    subspace A v m ∈ Module.End.invtSubmodule A :=
  (Module.End.mem_invtSubmodule_iff_map_le A).2 (h ▸ map_subspace_le A v m)

/-- Once the Krylov sequence closes up at step `n` it stays closed. -/
theorem pow_apply_mem_subspace_of_le {n : ℕ} (h : (A ^ n) v ∈ subspace A v n) {m : ℕ}
    (hm : n ≤ m) : (A ^ m) v ∈ subspace A v m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hk := pow_apply_mem_subspace_of_mem A v h k
  have hpow : (A ^ k) ((A ^ n) v) = (A ^ (n + k)) v := by
    rw [← Module.End.mul_apply, ← pow_add, Nat.add_comm]
  rwa [hpow] at hk

/-- Saad, *Iterative Methods*, Prop 6.1: the Krylov subspaces are constant from the first
closure onwards. -/
theorem subspace_eq_of_pow_apply_mem {n : ℕ} (h : (A ^ n) v ∈ subspace A v n) {m : ℕ}
    (hm : n ≤ m) : subspace A v m = subspace A v n := by
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    rw [(subspace_succ_eq_iff A v m).2 (pow_apply_mem_subspace_of_le A v h hm), ih]

/-- Once the Krylov sequence closes up at step `n`, that subspace is already everything the
sequence will ever reach: `𝒦_∞ = 𝒦_n`. -/
theorem fullSubspace_eq_of_pow_apply_mem {n : ℕ} (h : (A ^ n) v ∈ subspace A v n) :
    fullSubspace A v = subspace A v n := by
  refine le_antisymm ?_ (subspace_le_fullSubspace A v n)
  rw [fullSubspace, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rcases lt_or_ge i n with hi | hi
  · exact pow_apply_mem_subspace A v hi
  · exact subspace_eq_of_pow_apply_mem A v h hi ▸ pow_apply_mem_subspace_of_le A v h hi

/-- Rescaling the starting vector does not enlarge the Krylov subspace. -/
theorem subspace_smul (c : R) (m : ℕ) : subspace A (c • v) m ≤ subspace A v m := by
  rw [subspace, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  simpa using Submodule.smul_mem _ c (pow_apply_mem_subspace A v i.2)

end CommRing

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

variable (A : Module.End K V) (v : V)

/-- The grade of `v` w.r.t. `A`: the dimension of the cyclic subspace `𝒦_∞(A, v)` — equivalently
the least `m` with `A^m v ∈ 𝒦_m` (`grade_eq_sInf`) and the degree of the minimal polynomial of
`v` (Saad, *Iterative Methods*, §6.2; Liesen–Strakoš, *Krylov Subspace Methods: Principles and
Analysis*).
Junk value `0` when the cyclic subspace is infinite-dimensional
(Mathlib's `finrank` convention); the finite-grade hypothesis is
`[FiniteDimensional K (fullSubspace A v)]`, automatic when `V` is finite-dimensional. -/
noncomputable def grade : ℕ := Module.finrank K (fullSubspace A v)

/-- The Krylov vectors `v, A v, …, A^(m-1) v` are linearly independent exactly when no earlier
power of `A` has already fallen into its own Krylov subspace. -/
theorem linearIndependent_iff_forall_pow_notMem {m : ℕ} :
    LinearIndependent K (fun i : Fin m => (A ^ (i : ℕ)) v) ↔
      ∀ k < m, (A ^ k) v ∉ subspace A v k := by
  induction m with
  | zero => exact iff_of_true linearIndependent_empty_type (by simp)
  | succ m ih =>
    have hinit : Fin.init (fun i : Fin (m + 1) => (A ^ (i : ℕ)) v)
        = fun i : Fin m => (A ^ (i : ℕ)) v := rfl
    rw [linearIndependent_finSucc', hinit, ih]
    constructor
    · rintro ⟨h₁, h₂⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk' | rfl
      · exact h₁ k hk'
      · exact h₂
    · intro h
      exact ⟨fun k hk => h k (hk.trans m.lt_succ_self), h m m.lt_succ_self⟩

/-- The Krylov sequence stabilizes iff the cyclic subspace is finite-dimensional. -/
theorem finiteDimensional_fullSubspace_iff :
    FiniteDimensional K (fullSubspace A v) ↔ ∃ m, (A ^ m) v ∈ subspace A v m := by
  constructor
  · intro h
    by_contra hc
    have hc' : ∀ m, (A ^ m) v ∉ subspace A v m := fun m hm => hc ⟨m, hm⟩
    set n := Module.finrank K (fullSubspace A v) with hn
    have hli : LinearIndependent K (fun i : Fin (n + 1) => (A ^ (i : ℕ)) v) :=
      (linearIndependent_iff_forall_pow_notMem A v).2 fun k _ => hc' k
    have h₁ : Module.finrank K (subspace A v (n + 1)) = n + 1 := by
      rw [subspace]
      simpa using finrank_span_eq_card hli
    have h₂ : Module.finrank K (subspace A v (n + 1)) ≤ n :=
      hn ▸ Submodule.finrank_mono (subspace_le_fullSubspace A v (n + 1))
    omega
  · rintro ⟨m, hm⟩
    rw [fullSubspace_eq_of_pow_apply_mem A v hm]
    infer_instance

/-- `A^m v ∈ 𝒦_m` iff `v` is annihilated by a monic polynomial of degree `m`
(Saad, *Iterative Methods*, §6.2 defines the grade through the minimal polynomial of `v`). -/
theorem pow_apply_mem_subspace_iff_exists_monic (m : ℕ) :
    (A ^ m) v ∈ subspace A v m ↔ ∃ p : K[X], p.Monic ∧ p.natDegree = m ∧ aeval A p v = 0 := by
  rw [mem_subspace_iff_exists_aeval]
  constructor
  · rintro ⟨q, hq, hqv⟩
    refine ⟨X ^ m - q, monic_X_pow_sub hq, ?_, by simp [hqv]⟩
    refine natDegree_eq_of_degree_eq_some ?_
    rw [degree_sub_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]
  · rintro ⟨p, hp, hpd, hpv⟩
    refine ⟨X ^ m - p, ?_, by simp [hpv]⟩
    have hdp : p.degree = (m : ℕ) := hpd ▸ degree_eq_natDegree hp.ne_zero
    have hlt := degree_sub_lt_left (p := (X : K[X]) ^ m) (q := p) (by rw [degree_X_pow, hdp])
      (monic_X_pow m).ne_zero (by simp [hp.leadingCoeff])
    rwa [degree_X_pow] at hlt

/-- The grade of a vector never exceeds the dimension of the ambient space, so a Krylov method
in finite dimension terminates in at most `dim V` steps. -/
theorem grade_le_finrank [FiniteDimensional K V] : grade A v ≤ Module.finrank K V :=
  Submodule.finrank_le _

@[simp]
theorem grade_zero : grade A 0 = 0 := by
  rw [grade, fullSubspace_zero, finrank_bot]

theorem grade_eq_zero_iff :
    grade A v = 0 ↔ v = 0 ∨ ¬ FiniteDimensional K (fullSubspace A v) := by
  by_cases h : FiniteDimensional K (fullSubspace A v)
  · have := h
    simp only [h, not_true_eq_false, or_false, grade, Submodule.finrank_eq_zero]
    constructor
    · intro hb
      have hv : v ∈ fullSubspace A v := Submodule.subset_span ⟨0, by simp⟩
      rw [hb] at hv
      simpa using hv
    · rintro rfl
      exact fullSubspace_zero A
  · simp [h, grade, Module.finrank_of_not_finite h]

section FiniteGrade

variable [FiniteDimensional K (fullSubspace A v)]

private theorem exists_pow_apply_mem : {m | (A ^ m) v ∈ subspace A v m}.Nonempty :=
  (finiteDimensional_fullSubspace_iff A v).1 ‹_›

/-- The grade is the least `m` with `A^m v ∈ 𝒦_m` (the definition used by Saad,
*Iterative Methods*, §6.2). -/
theorem grade_eq_sInf : grade A v = sInf {m | (A ^ m) v ∈ subspace A v m} := by
  set n := sInf {m | (A ^ m) v ∈ subspace A v m} with hn
  have hmem : (A ^ n) v ∈ subspace A v n := Nat.sInf_mem (exists_pow_apply_mem A v)
  have hli : LinearIndependent K (fun i : Fin n => (A ^ (i : ℕ)) v) :=
    (linearIndependent_iff_forall_pow_notMem A v).2 fun k hk =>
      Nat.notMem_of_lt_sInf (hn ▸ hk)
  rw [grade, fullSubspace_eq_of_pow_apply_mem A v hmem, subspace]
  simpa using finrank_span_eq_card hli

theorem pow_grade_apply_mem : (A ^ grade A v) v ∈ subspace A v (grade A v) := by
  rw [grade_eq_sInf]
  exact Nat.sInf_mem (exists_pow_apply_mem A v)

/-- The grade is the exact point at which the Krylov sequence stops growing: `grade ≤ m` iff
`A^m v` has already fallen into `𝒦_m`. The working form of `grade_eq_sInf`. -/
theorem grade_le_iff {m : ℕ} : grade A v ≤ m ↔ (A ^ m) v ∈ subspace A v m :=
  ⟨fun h => pow_apply_mem_subspace_of_le A v (pow_grade_apply_mem A v) h, fun h => by
    rw [grade_eq_sInf]; exact Nat.sInf_le h⟩

theorem pow_apply_notMem_subspace_of_lt_grade {m : ℕ} (h : m < grade A v) :
    (A ^ m) v ∉ subspace A v m := fun hm => absurd ((grade_le_iff A v).2 hm) (not_le.2 h)

/-- Saad, *Iterative Methods*, Prop 6.1: `𝒦_m = 𝒦_grade` for `m ≥ grade`. -/
theorem subspace_eq_of_grade_le {m : ℕ} (h : grade A v ≤ m) :
    subspace A v m = subspace A v (grade A v) :=
  subspace_eq_of_pow_apply_mem A v (pow_grade_apply_mem A v) h

/-- `grade` steps already exhaust the cyclic subspace: `𝒦_grade = 𝒦_∞`. -/
theorem subspace_grade_eq_fullSubspace : subspace A v (grade A v) = fullSubspace A v :=
  (fullSubspace_eq_of_pow_apply_mem A v (pow_grade_apply_mem A v)).symm

/-- `𝒦_grade` is `A`-invariant: the invariant subspace a Krylov method has built by the time it
terminates. -/
theorem subspace_grade_mem_invtSubmodule :
    subspace A v (grade A v) ∈ Module.End.invtSubmodule A :=
  mem_invtSubmodule_of_subspace_succ_eq A v
    ((subspace_succ_eq_iff A v _).2 (pow_grade_apply_mem A v))

/-- The Krylov vectors `v, A v, …, A^(m-1) v` are linearly independent for `m ≤ grade`. -/
theorem linearIndependent_of_le_grade {m : ℕ} (h : m ≤ grade A v) :
    LinearIndependent K (fun i : Fin m => (A ^ (i : ℕ)) v) :=
  (linearIndependent_iff_forall_pow_notMem A v).2 fun _ hk =>
    pow_apply_notMem_subspace_of_lt_grade A v (hk.trans_le h)

/-- Saad, *Iterative Methods*, Prop 6.2: `dim 𝒦_m = min m (grade)`. -/
theorem finrank_subspace (m : ℕ) : Module.finrank K (subspace A v m) = min m (grade A v) := by
  rcases le_total m (grade A v) with h | h
  · rw [min_eq_left h, subspace]
    simpa using finrank_span_eq_card (linearIndependent_of_le_grade A v h)
  · rw [min_eq_right h, subspace_eq_of_grade_le A v h, subspace]
    simpa using finrank_span_eq_card (linearIndependent_of_le_grade A v le_rfl)

theorem subspace_strictMono_of_le_grade {m : ℕ} (h : m + 1 ≤ grade A v) :
    subspace A v m < subspace A v (m + 1) :=
  lt_of_le_of_ne (subspace_mono A v m.le_succ) fun he =>
    pow_apply_notMem_subspace_of_lt_grade A v (Nat.lt_of_succ_le h)
      ((subspace_succ_eq_iff A v m).1 he.symm)

end FiniteGrade

end Field

end Krylov

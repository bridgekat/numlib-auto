import Numlib.Analysis.InnerProductSpace.Projection.Compression
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Krylov.Subspace
import Numlib.Krylov.ToEuclideanLin

/-!
# Saad §6.1–6.2: Krylov subspaces and the grade of a vector

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §6.1–6.2.

The chapter's conventions are fixed here: a matrix `A : Matrix (Fin n) (Fin n) 𝕜` acts on
`EuclideanSpace 𝕜 (Fin n)` through `op A = Matrix.toEuclideanLin A`; the Krylov subspace
`𝒦_m(A, v)` of (6.2) is `krylov A v m`; the grade of `v` is `grade A v`, defined as the book
defines it — the degree of the minimal polynomial of `v` with respect to `A`. Both are
identified with the backbone objects `Krylov.subspace` and `Krylov.grade` (`krylov_eq`,
`grade_eq`), from which Propositions 6.1, 6.2, 6.3 and (6.3)–(6.4) follow.

Definitions are polymorphic in `𝕜` (`[RCLike 𝕜]`), since the algorithms of the later sections
are; the numbered results are stated over `ℝ`, the book's generality in §6.2, each a one-line
specialization of a field-agnostic companion lemma proved just above it.
-/

open Polynomial

namespace SaadSparse.Chapter06

section General

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-! ### The operator of a matrix -/

/-- The operator `x ↦ A x` on `𝕜ⁿ` defined by a square matrix; the book writes it `A` too. -/
abbrev op (A : Matrix (Fin n) (Fin n) 𝕜) : 𝔼 →ₗ[𝕜] 𝔼 := Matrix.toEuclideanLin A

/-- `p(A)` as an operator is `p` of the operator: `Matrix.toEuclideanLin` is an algebra map. -/
theorem toEuclideanLin_aeval (A : Matrix (Fin n) (Fin n) 𝕜) (p : 𝕜[X]) :
    Matrix.toEuclideanLin (aeval A p) = aeval (Matrix.toEuclideanLin A) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial k c =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, ← Algebra.smul_def,
      ← Algebra.smul_def, map_smul, Matrix.toEuclideanLin_pow]

/-- `p(A) x = p(op A) x`: the book's `p(A) v` read as an operator applied to `v`. -/
theorem op_aeval (A : Matrix (Fin n) (Fin n) 𝕜) (p : 𝕜[X]) :
    op (aeval A p) = aeval (op A) p :=
  toEuclideanLin_aeval A p

/-! ### The Krylov subspace (6.2) -/

/-- (6.2): the Krylov subspace `𝒦_m(A, v) = span {v, A v, A² v, …, A^{m-1} v}`. -/
def krylov (A : Matrix (Fin n) (Fin n) 𝕜) (v : 𝔼) (m : ℕ) : Submodule 𝕜 𝔼 :=
  Submodule.span 𝕜 (Set.range fun i : Fin m => op (A ^ (i : ℕ)) v)

variable (A : Matrix (Fin n) (Fin n) 𝕜) (v : EuclideanSpace 𝕜 (Fin n))

/-- The book's `𝒦_m(A, v)` is the backbone Krylov subspace of the operator `op A`. -/
theorem krylov_eq (m : ℕ) : krylov A v m = Krylov.subspace (op A) v m :=
  (Matrix.krylov_subspace_toEuclideanLin A v m).symm

/-- Each of the spanning vectors `A^i v`, `i < m`, of (6.2) lies in `𝒦_m(A, v)`. -/
theorem pow_apply_mem_krylov {i m : ℕ} (h : i < m) : (op A ^ i) v ∈ krylov A v m := by
  rw [krylov_eq]
  exact Krylov.pow_apply_mem_subspace _ _ h

/-- `v ∈ 𝒦_m(A, v)` for `m ≥ 1`. -/
theorem self_mem_krylov {m : ℕ} (h : 0 < m) : v ∈ krylov A v m := by
  rw [krylov_eq]
  exact Krylov.self_mem_subspace _ _ h

/-- §6.2: the Krylov subspaces increase with `m`, `𝒦_k ⊆ 𝒦_l` for `k ≤ l`; by Proposition 6.1
they stop increasing at the grade of `v`. -/
theorem krylov_mono {k l : ℕ} (h : k ≤ l) : krylov A v k ≤ krylov A v l := by
  rw [krylov_eq, krylov_eq]
  exact Krylov.subspace_mono (op A) v h

/-! ### The grade of a vector (§6.2) -/

private theorem exists_monic_natDegree_eq :
    ∃ d : ℕ, ∃ p : 𝕜[X], p.Monic ∧ p.natDegree = d ∧ op (aeval A p) v = 0 :=
  ⟨_, A.charpoly, A.charpoly_monic, rfl, by rw [Matrix.aeval_self_charpoly]; simp⟩

/-- §6.2: the grade of `v` with respect to `A`, the degree of the minimal polynomial of `v` —
the least degree of a monic polynomial `p` with `p(A) v = 0`. The set of such degrees is
nonempty by the Cayley–Hamilton theorem, so the infimum is attained
(`monic_natDegree_eq_grade`). -/
noncomputable def grade (A : Matrix (Fin n) (Fin n) 𝕜) (v : 𝔼) : ℕ :=
  sInf {d : ℕ | ∃ p : 𝕜[X], p.Monic ∧ p.natDegree = d ∧ op (aeval A p) v = 0}

/-- The grade is attained: there is a monic annihilator of `v` of degree `grade A v`. -/
theorem monic_natDegree_eq_grade :
    ∃ p : 𝕜[X], p.Monic ∧ p.natDegree = grade A v ∧ op (aeval A p) v = 0 :=
  Nat.sInf_mem (exists_monic_natDegree_eq A v)

/-- The grade is a lower bound: every monic annihilator of `v` has degree at least the grade. -/
theorem grade_le_natDegree {p : 𝕜[X]} (hp : p.Monic) (h : op (aeval A p) v = 0) :
    grade A v ≤ p.natDegree :=
  Nat.sInf_le ⟨p, hp, rfl, h⟩

/-- The minimal polynomial of `v` with respect to `A` (§6.2): a monic annihilator of `v` of the
least possible degree, namely `grade A v`. -/
noncomputable def minpolyVec (A : Matrix (Fin n) (Fin n) 𝕜) (v : 𝔼) : 𝕜[X] :=
  (monic_natDegree_eq_grade A v).choose

/-- The minimal polynomial of `v` is monic, as §6.2 requires. -/
theorem minpolyVec_monic : (minpolyVec A v).Monic :=
  (monic_natDegree_eq_grade A v).choose_spec.1

/-- The minimal polynomial of `v` has degree the grade of `v`, by definition of the grade. -/
theorem natDegree_minpolyVec : (minpolyVec A v).natDegree = grade A v :=
  (monic_natDegree_eq_grade A v).choose_spec.2.1

/-- The minimal polynomial of `v` annihilates `v`: `p(A) v = 0`. -/
theorem op_aeval_minpolyVec : op (aeval A (minpolyVec A v)) v = 0 :=
  (monic_natDegree_eq_grade A v).choose_spec.2.2

/-- The book's grade is the backbone `Krylov.grade` of the operator `op A`. -/
theorem grade_eq : grade A v = Krylov.grade (op A) v := by
  have hset : {d : ℕ | ∃ p : 𝕜[X], p.Monic ∧ p.natDegree = d ∧ op (aeval A p) v = 0}
      = {m : ℕ | ((op A) ^ m) v ∈ Krylov.subspace (op A) v m} := by
    ext d
    simp only [Set.mem_ofPred_eq, Krylov.pow_apply_mem_subspace_iff_exists_monic,
      toEuclideanLin_aeval]
  rw [Krylov.grade_eq_sInf]
  exact congrArg sInf hset

/-- §6.2: the grade of `v` does not exceed `n` (Cayley–Hamilton). -/
theorem grade_le_card : grade A v ≤ n := by
  rw [grade_eq]
  simpa using Krylov.grade_le_finrank (op A) v

/-- Rescaling the starting vector does not change the Krylov subspaces: the bridge between the
book's `𝒦_m(A, r_0)` and `𝒦_m(A, v_1)` with `v_1 = r_0 / ‖r_0‖`. -/
theorem krylov_smul {c : 𝕜} (hc : c ≠ 0) (m : ℕ) : krylov A (c • v) m = krylov A v m := by
  rw [krylov_eq, krylov_eq]
  refine le_antisymm (Krylov.subspace_smul (op A) v c m) ?_
  have h := Krylov.subspace_smul (op A) (c • v) c⁻¹ m
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h

/-- Rescaling the starting vector does not change its grade. -/
theorem grade_smul {c : 𝕜} (hc : c ≠ 0) : grade A (c • v) = grade A v := by
  have hs : ∀ m : ℕ, Krylov.subspace (op A) (c • v) m = Krylov.subspace (op A) v m := fun m => by
    rw [← krylov_eq, ← krylov_eq, krylov_smul A v hc]
  rw [grade_eq, grade_eq, Krylov.grade_eq_sInf, Krylov.grade_eq_sInf]
  congr 1
  ext m
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hs m, map_smul, Submodule.smul_mem_iff _ hc]

/-! ### §6.2, first property: `𝒦_m` is the set of `p(A) v` with `deg p ≤ m - 1` -/

/-- `𝒦_m(A, v) = {p(A) v : deg p < m}` (§6.2, the first property listed after (6.2)). -/
theorem krylov_eq_map_degreeLT (m : ℕ) :
    krylov A v m = (Polynomial.degreeLT 𝕜 m).map (Krylov.polyEval (op A) v) := by
  rw [krylov_eq, Krylov.subspace_eq_map_degreeLT]

/-- §6.2, the first property listed after (6.2), pointwise: `x ∈ 𝒦_m(A, v)` exactly when
`x = p(A) v` for some `p` of degree at most `m - 1`. -/
theorem mem_krylov_iff_exists_aeval {x : 𝔼} {m : ℕ} :
    x ∈ krylov A v m ↔ ∃ p : 𝕜[X], p.degree < m ∧ aeval (op A) p v = x := by
  rw [krylov_eq, Krylov.mem_subspace_iff_exists_aeval]

/-- `p(A) v ∈ 𝒦_m(A, v)` for `deg p < m`. -/
theorem aeval_mem_krylov {p : 𝕜[X]} {m : ℕ} (hp : p.degree < m) :
    aeval (op A) p v ∈ krylov A v m :=
  (mem_krylov_iff_exists_aeval A v).2 ⟨p, hp, rfl⟩

/-! ### Proposition 6.1 -/

/-- `𝒦_μ` is invariant under `A`, where `μ` is the grade of `v` (Proposition 6.1). -/
theorem krylov_grade_mem_invtSubmodule :
    krylov A v (grade A v) ∈ Module.End.invtSubmodule (op A) := by
  rw [krylov_eq, grade_eq]
  exact Krylov.subspace_grade_mem_invtSubmodule (op A) v

/-- `𝒦_m = 𝒦_μ` for `m ≥ μ` (Proposition 6.1). -/
theorem krylov_eq_of_grade_le {m : ℕ} (h : grade A v ≤ m) :
    krylov A v m = krylov A v (grade A v) := by
  rw [krylov_eq, krylov_eq, grade_eq]
  exact Krylov.subspace_eq_of_grade_le (op A) v (by rwa [grade_eq] at h)

/-! ### Proposition 6.2 and (6.3)–(6.4) -/

/-- (6.4): `dim 𝒦_m = min {m, μ}`. -/
theorem finrank_krylov (m : ℕ) : Module.finrank 𝕜 (krylov A v m) = min m (grade A v) := by
  rw [krylov_eq, grade_eq]
  exact Krylov.finrank_subspace (op A) v m

/-- (6.3): `dim 𝒦_m = m` exactly when the grade of `v` is at least `m`. -/
theorem finrank_krylov_eq_iff {m : ℕ} :
    Module.finrank 𝕜 (krylov A v m) = m ↔ m ≤ grade A v := by
  rw [finrank_krylov, min_eq_left_iff]

/-! ### Proposition 6.3: polynomials of `A` versus the section of `A` in `𝒦_m` -/

variable {A v}

/-- A projector `Q` with range `𝒦_m`, viewed as a map into `𝒦_m`. -/
private def toKrylov (m : ℕ) (Q : 𝔼 →ₗ[𝕜] 𝔼) (hQ : LinearMap.range Q = krylov A v m) :
    𝔼 →ₗ[𝕜] krylov A v m :=
  Q.codRestrict (krylov A v m) fun x => by rw [← hQ]; exact LinearMap.mem_range_self Q x

private theorem coe_toKrylov {m : ℕ} {Q : 𝔼 →ₗ[𝕜] 𝔼} (hQ : LinearMap.range Q = krylov A v m)
    (x : 𝔼) : (toKrylov m Q hQ x : 𝔼) = Q x := rfl

/-- A projector onto `𝒦_m` restricts to the identity of `𝒦_m`. -/
private theorem toKrylov_eq_self {m : ℕ} {Q : 𝔼 →ₗ[𝕜] 𝔼} (hidem : IsIdempotentElem Q)
    (hQ : LinearMap.range Q = krylov A v m) (x : krylov A v m) : toKrylov m Q hQ x = x := by
  obtain ⟨y, hy⟩ : (x : 𝔼) ∈ LinearMap.range Q := by rw [hQ]; exact x.2
  refine Subtype.ext ?_
  rw [coe_toKrylov, ← hy, ← Module.End.mul_apply, hidem]

/-- The section `A_m = Q A|_{𝒦_m}` of `A` in `𝒦_m` through an arbitrary projector `Q` onto
`𝒦_m` (Proposition 6.3). -/
noncomputable def section' (m : ℕ) (Q : 𝔼 →ₗ[𝕜] 𝔼) (hQ : LinearMap.range Q = krylov A v m) :
    krylov A v m →ₗ[𝕜] krylov A v m :=
  compressionBy (toKrylov m Q hQ) (op A)

/-- Proposition 6.3, first part: `q(A) v = q(A_m) v` for `deg q ≤ m - 1`. -/
theorem coe_aeval_section' {m : ℕ} (hm : 0 < m) {Q : 𝔼 →ₗ[𝕜] 𝔼} (hidem : IsIdempotentElem Q)
    (hQ : LinearMap.range Q = krylov A v m) {q : 𝕜[X]} (hq : q.degree < m) :
    ((aeval (section' m Q hQ) q ⟨v, self_mem_krylov A v hm⟩ : krylov A v m) : 𝔼)
      = aeval (op A) q v := by
  have hnat : q.natDegree < m := by
    rcases eq_or_ne q 0 with rfl | h0
    · simpa using hm
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).2 hq
  exact compressionBy.aeval_apply_of_forall_pow_mem _ (toKrylov_eq_self hidem hQ) (op A) q
    fun i hi => pow_apply_mem_krylov A v (lt_of_le_of_lt hi hnat)

/-- Proposition 6.3, second part: `Q q(A) v = q(A_m) v` for `deg q ≤ m`. -/
theorem apply_aeval_eq_coe_aeval_section' {m : ℕ} (hm : 0 < m) {Q : 𝔼 →ₗ[𝕜] 𝔼}
    (hidem : IsIdempotentElem Q) (hQ : LinearMap.range Q = krylov A v m) {q : 𝕜[X]}
    (hq : q.degree ≤ m) :
    Q (aeval (op A) q v)
      = ((aeval (section' m Q hQ) q ⟨v, self_mem_krylov A v hm⟩ : krylov A v m) : 𝔼) := by
  have hnat : q.natDegree ≤ m := Polynomial.natDegree_le_iff_degree_le.2 hq
  have h := compressionBy.apply_aeval_of_forall_pow_lt_mem (toKrylov m Q hQ)
    (toKrylov_eq_self hidem hQ) (op A) q (x := ⟨v, self_mem_krylov A v hm⟩)
    fun i hi => pow_apply_mem_krylov A v (lt_of_lt_of_le hi hnat)
  exact congrArg Subtype.val h

end General

/-! ### The numbered results of §6.2, in the book's real setting -/

section BookResults

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n))

/-- **Proposition 6.1**. Let `μ` be the grade of `v`. Then `𝒦_μ` is invariant under `A`, and
`𝒦_m = 𝒦_μ` for all `m ≥ μ`. -/
theorem proposition_6_1 : krylov A v (grade A v) ∈ Module.End.invtSubmodule (op A) ∧
    ∀ m, grade A v ≤ m → krylov A v m = krylov A v (grade A v) :=
  ⟨krylov_grade_mem_invtSubmodule A v, fun _ h => krylov_eq_of_grade_le A v h⟩

/-- **Proposition 6.2**, (6.3): the Krylov subspace `𝒦_m` has dimension `m` if and only if the
grade of `v` with respect to `A` is not less than `m`. -/
theorem proposition_6_2 {m : ℕ} : Module.finrank ℝ (krylov A v m) = m ↔ m ≤ grade A v :=
  finrank_krylov_eq_iff A v

/-- (6.4): `dim 𝒦_m = min {m, μ}`. -/
theorem equation_6_4 (m : ℕ) : Module.finrank ℝ (krylov A v m) = min m (grade A v) :=
  finrank_krylov A v m

/-- §6.2: the grade of `v` does not exceed `n`, by the Cayley–Hamilton theorem. -/
theorem grade_le_dim : grade A v ≤ n :=
  grade_le_card A v

variable {A v}

/-- **Proposition 6.3**. Let `Q_m` be any projector onto `𝒦_m` and `A_m = Q_m A|_{𝒦_m}` the
section of `A` in `𝒦_m`. Then `q(A) v = q(A_m) v` for every polynomial `q` of degree at most
`m - 1`, and `Q_m q(A) v = q(A_m) v` for every polynomial `q` of degree at most `m`. -/
theorem proposition_6_3 {m : ℕ} (hm : 0 < m)
    {Q : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)} (hidem : IsIdempotentElem Q)
    (hQ : LinearMap.range Q = krylov A v m) (q : ℝ[X]) :
    (q.degree < m →
        ((aeval (section' m Q hQ) q ⟨v, self_mem_krylov A v hm⟩ : krylov A v m)
          : EuclideanSpace ℝ (Fin n)) = aeval (op A) q v) ∧
      (q.degree ≤ m →
        Q (aeval (op A) q v)
          = ((aeval (section' m Q hQ) q ⟨v, self_mem_krylov A v hm⟩ : krylov A v m)
            : EuclideanSpace ℝ (Fin n))) :=
  ⟨fun hq => coe_aeval_section' hm hidem hQ hq,
    fun hq => apply_aeval_eq_coe_aeval_section' hm hidem hQ hq⟩

end BookResults

end SaadSparse.Chapter06

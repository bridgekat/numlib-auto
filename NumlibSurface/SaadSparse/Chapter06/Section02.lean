/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.Projection.Compression
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Krylov.Subspace
import Numlib.Krylov.ToEuclideanLin

/-!
# Saad, Sections 6.1–6.2: Krylov subspaces and the grade of a vector

This module formalizes Sections 6.1 and 6.2 of [saad2003iterative]. For a matrix
$A \in \mathbb{K}^{n \times n}$ and a vector $v$, the Krylov subspace (6.2) is
$$\mathcal{K}_m(A, v) = \operatorname{span}\{v, Av, A^2 v, \dots, A^{m-1} v\},$$
and the grade $\mu$ of $v$ is the degree of the minimal polynomial of $v$ with respect to $A$: the
least degree of a monic polynomial $p$ with $p(A) v = 0$. The module proves that $\mathcal{K}_m$ is
the set of the vectors $p(A) v$ with $\deg p \le m - 1$, that $\mathcal{K}_\mu$ is invariant under
$A$ and $\mathcal{K}_m = \mathcal{K}_\mu$ for $m \ge \mu$ (Proposition 6.1), that
$\dim \mathcal{K}_m = \min\{m, \mu\}$ (Proposition 6.2 and (6.4)), and that polynomials of $A$ and
of its section $A_m = Q_m A|_{\mathcal{K}_m}$ agree on $v$ (Proposition 6.3).

The Krylov subspace and the grade are identified with the backbone objects `Krylov.subspace` and
`Krylov.grade` of `Numlib.Krylov.Subspace`, which supply the proofs.

## Main definitions

* Section 6.2, `SaadSparse.Chapter06.op`: the operator $x \mapsto Ax$ of a square matrix.
* Equation (6.2), `SaadSparse.Chapter06.krylov`: the Krylov subspace $\mathcal{K}_m(A, v)$.
* Section 6.2, `SaadSparse.Chapter06.grade`: the grade of $v$ with respect to $A$.
* Section 6.2, `SaadSparse.Chapter06.minpolyVec`: the minimal polynomial of $v$ with respect to $A$.

## Main results

* Section 6.2, `SaadSparse.Chapter06.grade_le_card`: the grade of $v$ does not exceed $n$.
* Proposition 6.1, `SaadSparse.Chapter06.proposition_6_1`: $\mathcal{K}_\mu$ is invariant under $A$,
  and $\mathcal{K}_m = \mathcal{K}_\mu$ for $m \ge \mu$.
* Proposition 6.2, `SaadSparse.Chapter06.proposition_6_2`: $\dim \mathcal{K}_m = m$ if and only if
  $\mu \ge m$.
* Equation (6.4), `SaadSparse.Chapter06.equation_6_4`: $\dim \mathcal{K}_m = \min\{m, \mu\}$.
* Proposition 6.3, `SaadSparse.Chapter06.proposition_6_3`: $q(A) v = q(A_m) v$ for
  $\deg q \le m - 1$, and $Q_m q(A) v = q(A_m) v$ for $\deg q \le m$.

## Implementation notes

* A matrix `A : Matrix (Fin n) (Fin n) 𝕜` acts on `EuclideanSpace 𝕜 (Fin n)` through
  `SaadSparse.Chapter06.op A`, which is `Matrix.toEuclideanLin A`. The vector $p(A) v$ is
  `aeval (op A) p v`, and `SaadSparse.Chapter06.op_aeval` relates it to the matrix polynomial
  `aeval A p`.
* The definitions are polymorphic in the scalar field `𝕜` with `[RCLike 𝕜]`, because the algorithms
  of the later sections are. The numbered results are stated over $\mathbb{R}$, the generality of
  Section 6.2 of the book. Each is a specialization of a lemma for any `𝕜` proved earlier in the
  module.
* Section 6.1 is the introduction of the chapter. Its one substantive paragraph is stated here with
  Section 6.2.
-/

open Polynomial

namespace SaadSparse.Chapter06

section General

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-! ### The operator of a matrix -/

/-- **Section 6.2** of [saad2003iterative]. The **operator** $x \mapsto Ax$ on $\mathbb{K}^n$
defined by a square matrix $A$. The book writes it $A$ too.

It is `Matrix.toEuclideanLin A`. -/
abbrev op (A : Matrix (Fin n) (Fin n) 𝕜) : 𝔼 →ₗ[𝕜] 𝔼 := Matrix.toEuclideanLin A

/-- For a polynomial $p$, the operator of the matrix $p(A)$ is $p$ evaluated at the operator of $A$.
So the book's $p(A) v$ can be read either way. -/
theorem op_aeval (A : Matrix (Fin n) (Fin n) 𝕜) (p : 𝕜[X]) :
    op (aeval A p) = aeval (op A) p :=
  Matrix.toEuclideanLin_aeval A p

/-! ### The Krylov subspace (6.2) -/

/-- **Equation (6.2)** of [saad2003iterative]. The **Krylov subspace** of $A$ and $v$ of dimension
index $m$ is
$$\mathcal{K}_m(A, v) = \operatorname{span}\{v, Av, A^2 v, \dots, A^{m-1} v\}.$$

For $m = 0$ it is the zero subspace. -/
def krylov (A : Matrix (Fin n) (Fin n) 𝕜) (v : 𝔼) (m : ℕ) : Submodule 𝕜 𝔼 :=
  Submodule.span 𝕜 (Set.range fun i : Fin m => op (A ^ (i : ℕ)) v)

variable (A : Matrix (Fin n) (Fin n) 𝕜) (v : EuclideanSpace 𝕜 (Fin n))

/-- The Krylov subspace $\mathcal{K}_m(A, v)$ is the backbone Krylov subspace `Krylov.subspace` of
the operator of $A$. -/
theorem krylov_eq (m : ℕ) : krylov A v m = Krylov.subspace (op A) v m :=
  (Matrix.krylov_subspace_toEuclideanLin A v m).symm

/-- Each spanning vector $A^i v$ with $i < m$ lies in $\mathcal{K}_m(A, v)$. -/
theorem pow_apply_mem_krylov {i m : ℕ} (h : i < m) : (op A ^ i) v ∈ krylov A v m := by
  rw [krylov_eq]
  exact Krylov.pow_apply_mem_subspace _ _ h

/-- If $m \ge 1$, then $v \in \mathcal{K}_m(A, v)$. -/
theorem self_mem_krylov {m : ℕ} (h : 0 < m) : v ∈ krylov A v m := by
  rw [krylov_eq]
  exact Krylov.self_mem_subspace _ _ h

/-- **Section 6.2** of [saad2003iterative]. The Krylov subspaces increase with $m$: if $k \le l$,
then $\mathcal{K}_k(A, v) \subseteq \mathcal{K}_l(A, v)$. By Proposition 6.1 they stop
increasing at the grade of $v$. -/
theorem krylov_mono {k l : ℕ} (h : k ≤ l) : krylov A v k ≤ krylov A v l := by
  rw [krylov_eq, krylov_eq]
  exact Krylov.subspace_mono (op A) v h

/-! ### The grade of a vector -/

private theorem exists_monic_natDegree_eq :
    ∃ d : ℕ, ∃ p : 𝕜[X], p.Monic ∧ p.natDegree = d ∧ op (aeval A p) v = 0 :=
  ⟨_, A.charpoly, A.charpoly_monic, rfl, by rw [Matrix.aeval_self_charpoly]; simp⟩

/-- **Section 6.2** of [saad2003iterative]. The **grade** of $v$ with respect to $A$ is the degree
of the minimal polynomial of $v$: the least degree $d$ of a monic polynomial $p$ with
$p(A) v = 0$.

The set of such degrees is not empty by the Cayley–Hamilton theorem, so the infimum is attained
(`SaadSparse.Chapter06.monic_natDegree_eq_grade`). The grade of $v = 0$ is $0$, since the
constant polynomial $1$ annihilates it. -/
noncomputable def grade (A : Matrix (Fin n) (Fin n) 𝕜) (v : 𝔼) : ℕ :=
  sInf {d : ℕ | ∃ p : 𝕜[X], p.Monic ∧ p.natDegree = d ∧ op (aeval A p) v = 0}

/-- The grade is attained: there is a monic polynomial $p$ of degree $\mu$, the grade of $v$, with
$p(A) v = 0$. -/
theorem monic_natDegree_eq_grade :
    ∃ p : 𝕜[X], p.Monic ∧ p.natDegree = grade A v ∧ op (aeval A p) v = 0 :=
  Nat.sInf_mem (s := {d : ℕ | ∃ p : 𝕜[X], p.Monic ∧ p.natDegree = d ∧ op (aeval A p) v = 0})
    (exists_monic_natDegree_eq A v)

/-- The grade is a lower bound: if $p$ is monic and $p(A) v = 0$, then the grade of $v$ is at most
$\deg p$. -/
theorem grade_le_natDegree {p : 𝕜[X]} (hp : p.Monic) (h : op (aeval A p) v = 0) :
    grade A v ≤ p.natDegree :=
  Nat.sInf_le ⟨p, hp, rfl, h⟩

/-- **Section 6.2** of [saad2003iterative]. The **minimal polynomial** of $v$ with respect to $A$: a
monic polynomial $p$ of the least possible degree with $p(A) v = 0$. Its degree is the grade of
$v$.

It is chosen among the monic annihilators of degree $\mu$
(`SaadSparse.Chapter06.monic_natDegree_eq_grade`). -/
noncomputable def minpolyVec (A : Matrix (Fin n) (Fin n) 𝕜) (v : 𝔼) : 𝕜[X] :=
  (monic_natDegree_eq_grade A v).choose

/-- The minimal polynomial of $v$ is monic. -/
theorem minpolyVec_monic : (minpolyVec A v).Monic :=
  (monic_natDegree_eq_grade A v).choose_spec.1

/-- The degree of the minimal polynomial of $v$ is the grade of $v$. -/
theorem natDegree_minpolyVec : (minpolyVec A v).natDegree = grade A v :=
  (monic_natDegree_eq_grade A v).choose_spec.2.1

/-- The minimal polynomial $p$ of $v$ annihilates $v$: $p(A) v = 0$. -/
theorem op_aeval_minpolyVec : op (aeval A (minpolyVec A v)) v = 0 :=
  (monic_natDegree_eq_grade A v).choose_spec.2.2

/-- The grade of $v$ with respect to $A$ is the backbone grade `Krylov.grade` of $v$ with respect to
the operator of $A$. -/
theorem grade_eq : grade A v = Krylov.grade (op A) v := by
  have hset : {d : ℕ | ∃ p : 𝕜[X], p.Monic ∧ p.natDegree = d ∧ op (aeval A p) v = 0}
      = {m : ℕ | ((op A) ^ m) v ∈ Krylov.subspace (op A) v m} := by
    ext d
    simp only [Set.mem_ofPred_eq, Krylov.pow_apply_mem_subspace_iff_exists_monic,
      Matrix.toEuclideanLin_aeval]
  rw [Krylov.grade_eq_sInf]
  exact congrArg sInf hset

/-- **Section 6.2** of [saad2003iterative]. The grade of every $v \in \mathbb{K}^n$ with respect to
$A \in \mathbb{K}^{n \times n}$ is at most $n$.

The proof uses the Cayley–Hamilton theorem: the characteristic polynomial of $A$ is monic of
degree $n$ and annihilates $v$. -/
theorem grade_le_card : grade A v ≤ n := by
  rw [grade_eq]
  simpa using Krylov.grade_le_finrank (op A) v

/-- For a scalar $c \neq 0$, rescaling the starting vector does not change the Krylov subspaces:
$\mathcal{K}_m(A, cv) = \mathcal{K}_m(A, v)$. This relates the book's $\mathcal{K}_m(A, r_0)$ to
$\mathcal{K}_m(A, v_1)$ with $v_1 = r_0 / \|r_0\|$. -/
theorem krylov_smul {c : 𝕜} (hc : c ≠ 0) (m : ℕ) : krylov A (c • v) m = krylov A v m := by
  rw [krylov_eq, krylov_eq]
  refine le_antisymm (Krylov.subspace_smul (op A) v c m) ?_
  have h := Krylov.subspace_smul (op A) (c • v) c⁻¹ m
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h

/-- For a scalar $c \neq 0$, the grade of $cv$ is the grade of $v$. -/
theorem grade_smul {c : 𝕜} (hc : c ≠ 0) : grade A (c • v) = grade A v := by
  rw [grade_eq, grade_eq, Krylov.grade_smul (op A) v hc]

/-- For a nonzero vector $r$, the grade of $r / \|r\|$ is the grade of $r$. This relates the grade
of $r_0$ to that of $v_1 = r_0 / \|r_0\|$ in every algorithm that starts from a residual. -/
theorem grade_normalize {r : EuclideanSpace 𝕜 (Fin n)} (hr : r ≠ 0) :
    grade A ((‖r‖⁻¹ : 𝕜) • r) = grade A r :=
  grade_smul A r (inv_ne_zero (by simpa using norm_ne_zero_iff.2 hr))

/-!
### Section 6.2, first property: $\mathcal{K}_m$ is the set of the $p(A) v$ with $\deg p \le m - 1$
-/

/-- **Section 6.2** of [saad2003iterative], the first property after (6.2). The Krylov subspace is
the image of the polynomials of degree less than $m$ under $p \mapsto p(A) v$:
$$\mathcal{K}_m(A, v) = \{p(A) v : \deg p < m\}.$$
-/
theorem krylov_eq_map_degreeLT (m : ℕ) :
    krylov A v m = (Polynomial.degreeLT 𝕜 m).map (Krylov.polyEval (op A) v) := by
  rw [krylov_eq, Krylov.subspace_eq_map_degreeLT]

/-- **Section 6.2** of [saad2003iterative], the first property after (6.2), pointwise. A vector $x$
lies in $\mathcal{K}_m(A, v)$ if and only if $x = p(A) v$ for some polynomial $p$ of degree at
most $m - 1$. -/
theorem mem_krylov_iff_exists_aeval {x : 𝔼} {m : ℕ} :
    x ∈ krylov A v m ↔ ∃ p : 𝕜[X], p.degree < m ∧ aeval (op A) p v = x := by
  rw [krylov_eq, Krylov.mem_subspace_iff_exists_aeval]

/-- If $\deg p < m$, then $p(A) v \in \mathcal{K}_m(A, v)$. -/
theorem aeval_mem_krylov {p : 𝕜[X]} {m : ℕ} (hp : p.degree < m) :
    aeval (op A) p v ∈ krylov A v m :=
  (mem_krylov_iff_exists_aeval A v).2 ⟨p, hp, rfl⟩

/-! ### Proposition 6.1 -/

/-- Let $\mu$ be the grade of $v$. Then $\mathcal{K}_\mu(A, v)$ is invariant under $A$. This is the
first part of Proposition 6.1 of [saad2003iterative]. -/
theorem krylov_grade_mem_invtSubmodule :
    krylov A v (grade A v) ∈ Module.End.invtSubmodule (op A) := by
  rw [krylov_eq, grade_eq]
  exact Krylov.subspace_grade_mem_invtSubmodule (op A) v

/-- Let $\mu$ be the grade of $v$. If $m \ge \mu$, then
$\mathcal{K}_m(A, v) = \mathcal{K}_\mu(A, v)$. This is the second part of Proposition 6.1 of
[saad2003iterative]. -/
theorem krylov_eq_of_grade_le {m : ℕ} (h : grade A v ≤ m) :
    krylov A v m = krylov A v (grade A v) := by
  rw [krylov_eq, krylov_eq, grade_eq]
  exact Krylov.subspace_eq_of_grade_le (op A) v (by rwa [grade_eq] at h)

/-! ### Proposition 6.2 and (6.3)–(6.4) -/

/-- For every $m$, $\dim \mathcal{K}_m(A, v) = \min\{m, \mu\}$, where $\mu$ is the grade of $v$.
This is (6.4) of [saad2003iterative] over $\mathbb{R}$ or $\mathbb{C}$. -/
theorem finrank_krylov (m : ℕ) : Module.finrank 𝕜 (krylov A v m) = min m (grade A v) := by
  rw [krylov_eq, grade_eq]
  exact Krylov.finrank_subspace (op A) v m

/-- For every $m$, $\dim \mathcal{K}_m(A, v) = m$ if and only if $m \le \mu$, where $\mu$ is the
grade of $v$. This is (6.3) of [saad2003iterative] over $\mathbb{R}$ or $\mathbb{C}$. -/
theorem finrank_krylov_eq_iff {m : ℕ} :
    Module.finrank 𝕜 (krylov A v m) = m ↔ m ≤ grade A v := by
  rw [finrank_krylov, min_eq_left_iff]

/-! ### Proposition 6.3: polynomials of $A$ and of the section of $A$ in $\mathcal{K}_m$ -/

variable {A v}

/-- A projector $Q$ with range $\mathcal{K}_m$, viewed as a map into $\mathcal{K}_m$. -/
private def toKrylov (m : ℕ) (Q : 𝔼 →ₗ[𝕜] 𝔼) (hQ : LinearMap.range Q = krylov A v m) :
    𝔼 →ₗ[𝕜] krylov A v m :=
  Q.codRestrict (krylov A v m) fun x => by rw [← hQ]; exact LinearMap.mem_range_self Q x

private theorem coe_toKrylov {m : ℕ} {Q : 𝔼 →ₗ[𝕜] 𝔼} (hQ : LinearMap.range Q = krylov A v m)
    (x : 𝔼) : (toKrylov m Q hQ x : 𝔼) = Q x := rfl

/-- A projector onto $\mathcal{K}_m$ restricts to the identity of $\mathcal{K}_m$. -/
private theorem toKrylov_eq_self {m : ℕ} {Q : 𝔼 →ₗ[𝕜] 𝔼} (hidem : IsIdempotentElem Q)
    (hQ : LinearMap.range Q = krylov A v m) (x : krylov A v m) : toKrylov m Q hQ x = x := by
  obtain ⟨y, hy⟩ : (x : 𝔼) ∈ LinearMap.range Q := by rw [hQ]; exact x.2
  refine Subtype.ext ?_
  rw [coe_toKrylov, ← hy, ← Module.End.mul_apply, hidem]

/-- The **section** of $A$ in $\mathcal{K}_m$ through a linear map $Q$ with range $\mathcal{K}_m$:
the operator $A_m = Q A|_{\mathcal{K}_m}$ on $\mathcal{K}_m$. This is the operator of
Proposition 6.3 of [saad2003iterative].

The definition does not require $Q$ to be idempotent; the theorems about it do. -/
noncomputable def section' (m : ℕ) (Q : 𝔼 →ₗ[𝕜] 𝔼) (hQ : LinearMap.range Q = krylov A v m) :
    krylov A v m →ₗ[𝕜] krylov A v m :=
  compressionBy (toKrylov m Q hQ) (op A)

/-- Let $m \ge 1$, let $Q$ be a projector with range $\mathcal{K}_m$, and let
$A_m = Q A|_{\mathcal{K}_m}$. Then for every polynomial $q$ of degree at most $m - 1$,
$q(A) v = q(A_m) v$. This is the first part of Proposition 6.3 of [saad2003iterative], over
$\mathbb{R}$ or $\mathbb{C}$. -/
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

/-- Let $m \ge 1$, let $Q$ be a projector with range $\mathcal{K}_m$, and let
$A_m = Q A|_{\mathcal{K}_m}$. Then for every polynomial $q$ of degree at most $m$,
$Q \, q(A) v = q(A_m) v$. This is the second part of Proposition 6.3 of [saad2003iterative],
over $\mathbb{R}$ or $\mathbb{C}$. -/
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

/-! ### The numbered results of Section 6.2, over the real numbers -/

section BookResults

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n))

/-- **Proposition 6.1** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$, let
$v \in \mathbb{R}^n$, and let $\mu$ be the grade of $v$ with respect to $A$. Then
$\mathcal{K}_\mu$ is invariant under $A$, and $\mathcal{K}_m = \mathcal{K}_\mu$ for all
$m \ge \mu$. -/
theorem proposition_6_1 : krylov A v (grade A v) ∈ Module.End.invtSubmodule (op A) ∧
    ∀ m, grade A v ≤ m → krylov A v m = krylov A v (grade A v) :=
  ⟨krylov_grade_mem_invtSubmodule A v, fun _ h => krylov_eq_of_grade_le A v h⟩

/-- **Proposition 6.2** of [saad2003iterative], formula (6.3). Let $A \in \mathbb{R}^{n \times n}$
and $v \in \mathbb{R}^n$. The Krylov subspace $\mathcal{K}_m$ has dimension $m$ if and only if
the grade of $v$ with respect to $A$ is not less than $m$:
$$\dim \mathcal{K}_m = m \iff \mu \ge m.$$
-/
theorem proposition_6_2 {m : ℕ} : Module.finrank ℝ (krylov A v m) = m ↔ m ≤ grade A v :=
  finrank_krylov_eq_iff A v

/-- **Equation (6.4)** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$, let
$v \in \mathbb{R}^n$, and let $\mu$ be the grade of $v$. Then for every $m$,
$$\dim \mathcal{K}_m = \min\{m, \mu\}.$$
-/
theorem equation_6_4 (m : ℕ) : Module.finrank ℝ (krylov A v m) = min m (grade A v) :=
  finrank_krylov A v m

/-- The grade of $v \in \mathbb{R}^n$ with respect to $A \in \mathbb{R}^{n \times n}$ is at most
$n$, by the Cayley–Hamilton theorem. This is `SaadSparse.Chapter06.grade_le_card` over
$\mathbb{R}$. -/
theorem grade_le_dim : grade A v ≤ n :=
  grade_le_card A v

variable {A v}

/-- **Proposition 6.3** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$,
$v \in \mathbb{R}^n$ and $m \ge 1$. Let $Q_m$ be any projector onto $\mathcal{K}_m$, and let
$A_m = Q_m A|_{\mathcal{K}_m}$ be the section of $A$ in $\mathcal{K}_m$. Then for every
polynomial $q$:

* if $\deg q \le m - 1$, then $q(A) v = q(A_m) v$;
* if $\deg q \le m$, then $Q_m q(A) v = q(A_m) v$.

A projector onto $\mathcal{K}_m$ is an idempotent linear map $Q_m$ with range $\mathcal{K}_m$.
The section is `SaadSparse.Chapter06.section'`, and $v$ is viewed as an element of
$\mathcal{K}_m$, which needs $m \ge 1$. -/
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

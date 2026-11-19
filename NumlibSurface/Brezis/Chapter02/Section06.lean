/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.PSeries
import Numlib.Analysis.Normed.Operator.Unbounded.Adjoint
import Numlib.Analysis.Normed.Operator.Unbounded.Basic

/-!
# Brezis, Section 2.6: Unbounded linear operators, and the definition of the adjoint

This module formalizes Section 2.6 of [brezis2011functional] for real normed spaces $E$ and $F$. An
unbounded linear operator $A : D(A) \subseteq E \to F$ is a linear map defined on a linear subspace
$D(A)$ of $E$, the domain of $A$. It has the graph $G(A) = \{[u, Au] : u \in D(A)\} \subseteq E
\times F$, the range $R(A)$ and the kernel $N(A)$, and it is closed if $G(A)$ is closed. If $A$ is
densely defined, its adjoint $A^\star : D(A^\star) \subseteq F^\star \to E^\star$ has the domain
$$D(A^\star) = \{v \in F^\star : \exists c \ge 0,\ |\langle v, Au \rangle| \le c\|u\| \ \forall u
  \in D(A)\},$$
and $A^\star v$ is the unique $f \in E^\star$ with $\langle v, Au \rangle = \langle f, u \rangle$
for all $u \in D(A)$. The adjoint is closed (Proposition 2.17), and the kernels and ranges of $A$
and $A^\star$ satisfy four orthogonality relations (Corollary 2.18). Examples on $\ell^2$ show that
a bounded operator can have a range that is not closed, and that a closable operator need not be
closed.

The adjoint is the backbone `LinearPMap.strongDualAdjoint` of the module
`Numlib.Analysis.Normed.Operator.Unbounded.Adjoint`. For a bounded operator $T$ it is the dual map
`ContinuousLinearMap.strongDualMap`.

## Main definitions

* Section 2.6, definition of a bounded operator, `Brezis.Chapter02.IsBoundedOperator`: $D(A) = E$
  and $\|Au\| \le c\|u\|$.
* Remark 20, `Brezis.Chapter02.diagOperator`: the operator $Ax = (x_n/n)_{n \ge 1}$ on $\ell^2$.
* Section 2.6, `Brezis.Chapter02.finSuppSubmodule`: the finitely supported sequences in $\ell^2$,
  the domain of the example of Remark 11.

## Main results

* Section 2.6, `Brezis.Chapter02.isBoundedOperator_iff`: a bounded operator is a bounded linear
  operator on all of $E$, and conversely.
* Section 2.6, `Brezis.Chapter02.mem_graph_iff`: the graph $G(A)$.
* Section 2.6, `Brezis.Chapter02.mem_range_iff`: the range $R(A)$.
* Section 2.6, `Brezis.Chapter02.mem_ker_iff`: the kernel $N(A)$.
* Section 2.6, `Brezis.Chapter02.isClosed_iff`: $A$ is closed if and only if $G(A)$ is closed.
* Remark 11, `Brezis.Chapter02.remark_2_11`: the sequential criterion for closedness.
* Remark 11, `Brezis.Chapter02.remark_2_11_not_closed`: a closable operator that is not closed.
* Remark 12, `Brezis.Chapter02.remark_2_12`: the kernel of a closed operator is closed.
* Remark 12, `Brezis.Chapter02.remark_2_12_range_not_closed`: a bounded operator on $\ell^2$ whose
  range is not closed.
* Section 2.6, `Brezis.Chapter02.adjoint_domain_iff`: the domain of $A^\star$.
* Section 2.6, `Brezis.Chapter02.adjoint_apply`: the fundamental relation $\langle v, Au
  \rangle = \langle A^\star v, u \rangle$.
* Section 2.6, `Brezis.Chapter02.adjoint_apply_eq`: $A^\star v$ is the unique extension of
  $u \mapsto \langle v, Au \rangle$.
* Remark 15, `Brezis.Chapter02.remark_2_15`: for $A$ closed and densely defined, $D(A^\star)$ is
  dense in $F^\star$ for $\sigma(F^\star, F)$.
* Remark 16, `Brezis.Chapter02.remark_2_16`: the adjoint of a bounded operator $T$ is the bounded
  operator $T^\star$, with $\|T^\star\| = \|T\|$.
* Proposition 2.17, `Brezis.Chapter02.proposition_2_17`: $A^\star$ is closed.
* Section 2.6, `Brezis.Chapter02.graph_adjoint_eq_annihilator_graph`: the graph identity
  $I[G(A^\star)] = G(A)^\perp$ and the corresponding membership criterion.
* Corollary 2.18, `Brezis.Chapter02.corollary_2_18`: $N(A) = R(A^\star)^\perp$,
  $N(A^\star) = R(A)^\perp$, $N(A)^\perp \supseteq \overline{R(A^\star)}$ and
  $N(A^\star)^\perp = \overline{R(A)}$.
* Remark 17, `Brezis.Chapter02.remark_2_17`: $N(A)^\perp$ is the closure of $R(A^\star)$ for
  $\sigma(E^\star, E)$.
* Remark 17, `Brezis.Chapter02.remark_2_17_reflexive`: if $E$ is reflexive, then
  $N(A)^\perp = \overline{R(A^\star)}$.

## Conventions

* An unbounded operator $A : D(A) \subseteq E \to F$ is Mathlib's `LinearPMap`, `A : E →ₗ.[ℝ] F`,
  and $D(A)$ is `A.domain`. The graph, the range and the kernel are `A.graph`,
  `LinearMap.range A.toFun` and `A.ker`. Closedness is `A.IsClosed`, and "densely defined" is
  `Dense (A.domain : Set E)`.
* $\ell^2$ is `lp (fun _ : ℕ => ℝ) 2`. Sequences are indexed from $0$, so the operator
  $x \mapsto (x_n/n)_{n \ge 1}$ of the source is $x \mapsto (x_n/(n+1))_{n \ge 0}$.

## Implementation notes

* As Remark 14 explains, the adjoint is defined by extension by continuity, without the Hahn–Banach
  theorem; this is the definition of `LinearPMap.strongDualAdjoint`. The domain $D(A^\star)$ is
  defined for every $A$. When $D(A)$ is not dense, the values of `LinearPMap.strongDualAdjoint` are
  $0$, so the results about the values assume that $D(A)$ is dense.

## Deviations from the source

* **Standing setting of Section 2.6** (generalization). The definitions and adjoint results
  apply to normed spaces. The source starts with Banach spaces. See
  `Brezis.Chapter02.IsBoundedOperator`, `Brezis.Chapter02.proposition_2_17` and
  `Brezis.Chapter02.corollary_2_18`.
* **Remark 11, sequential closedness** (generalization). The sufficient condition is stated
  as an equivalence. See `Brezis.Chapter02.remark_2_11`.
* **Domain of the adjoint** (generalization). The boundedness test applies to operators
  with nondense domain. See `Brezis.Chapter02.adjoint_domain_iff`.

## Not formalized

* **Remarks 10, 13 and 14.** They are discussion.
* **Remarks 15 and 17, first clauses (Exercises 2.22 and 2.23).** The counterexamples on $\ell^1$.
* **Remark 15, reflexive clause.** It is Theorem 3.24 in Chapter 3.
-/

open Filter Topology NormedSpace
open scoped ENNReal

noncomputable section

namespace Brezis.Chapter02

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-! ### The definitions -/

/-- **Section 2.6** of [brezis2011functional], definition of a bounded operator. An unbounded linear
operator $A : D(A) \subseteq E \to F$ is **bounded** (or **continuous**) if $D(A) = E$ and there
is a constant $c \ge 0$ such that
$$\|Au\| \le c\|u\| \quad \text{for all } u \in E.$$

**Generalization.** The source starts with Banach spaces. This statement works for arbitrary
real normed spaces.
-/
def IsBoundedOperator (A : E →ₗ.[ℝ] F) : Prop :=
  A.domain = ⊤ ∧ ∃ c : ℝ, 0 ≤ c ∧ ∀ u : A.domain, ‖A u‖ ≤ c * ‖(u : E)‖

/-- An unbounded linear operator $A : D(A) \subseteq E \to F$ is bounded in the sense of
`Brezis.Chapter02.IsBoundedOperator` if and only if $A$ is a bounded linear operator
$T \in \mathcal{L}(E, F)$, viewed as an operator with domain $E$. -/
theorem isBoundedOperator_iff (A : E →ₗ.[ℝ] F) :
    IsBoundedOperator A ↔ ∃ T : E →L[ℝ] F, A = (T : E →ₗ[ℝ] F).toPMap ⊤ := by
  constructor
  · rintro ⟨hdom, c, -, hc⟩
    let e : E ≃ₗ[ℝ] A.domain := (LinearEquiv.ofTop A.domain hdom).symm
    let T : E →L[ℝ] F := (A.toFun.comp e.toLinearMap).mkContinuousOfExistsBound ⟨c, fun x => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearPMap.toFun_eq_coe]
      refine (hc (e x)).trans ?_
      have : ((e x : A.domain) : E) = x := rfl
      rw [this]⟩
    refine ⟨T, LinearPMap.ext hdom fun x hx hx' => ?_⟩
    rfl
  · rintro ⟨T, rfl⟩
    exact ⟨rfl, ‖T‖, norm_nonneg _, fun u => T.le_opNorm u⟩

/-- **Section 2.6** of [brezis2011functional], the graph. The graph of $A : D(A) \subseteq E \to F$
is
$$G(A) = \{[u, Au] : u \in D(A)\} \subseteq E \times F.$$
It is `A.graph`, and the theorem states its membership criterion.

**Generalization.** The source starts with Banach spaces. This statement works for arbitrary
real normed spaces. -/
theorem mem_graph_iff (A : E →ₗ.[ℝ] F) (x : E) (y : F) :
    (x, y) ∈ A.graph ↔ ∃ u : A.domain, (u : E) = x ∧ A u = y :=
  LinearPMap.mem_graph_iff A

/-- **Section 2.6** of [brezis2011functional], the range. The range of $A : D(A) \subseteq E \to F$
is
$$R(A) = \{Au : u \in D(A)\} \subseteq F.$$
It is `LinearMap.range A.toFun`, and the theorem states its membership criterion.

**Generalization.** The source starts with Banach spaces. This statement works for arbitrary
real normed spaces. -/
theorem mem_range_iff (A : E →ₗ.[ℝ] F) (y : F) :
    y ∈ LinearMap.range A.toFun ↔ ∃ u : A.domain, A u = y :=
  LinearMap.mem_range

/-- **Section 2.6** of [brezis2011functional], the kernel. The kernel of
$A : D(A) \subseteq E \to F$ is
$$N(A) = \{u \in D(A) : Au = 0\} \subseteq E.$$
It is `A.ker`, and the theorem states its membership criterion.

**Generalization.** The source starts with Banach spaces. This statement works for arbitrary
real normed spaces. -/
theorem mem_ker_iff (A : E →ₗ.[ℝ] F) (x : E) :
    x ∈ A.ker ↔ ∃ u : A.domain, x = u ∧ A u = 0 :=
  LinearPMap.mem_ker_iff

/-- **Section 2.6** of [brezis2011functional], closed operators. An unbounded operator
$A : D(A) \subseteq E \to F$ is **closed** if and only if its graph $G(A)$ is closed in
$E \times F$. Closedness is Mathlib's `LinearPMap.IsClosed`.

**Generalization.** The source starts with Banach spaces. This statement works for arbitrary
real normed spaces. -/
theorem isClosed_iff (A : E →ₗ.[ℝ] F) : A.IsClosed ↔ IsClosed (A.graph : Set (E × F)) :=
  Iff.rfl

/-- **Remark 11** of [brezis2011functional]. An unbounded operator $A : D(A) \subseteq E \to F$ is
closed if and only if, for every sequence $(u_n)$ in $D(A)$ with $u_n \to u$ in $E$ and
$Au_n \to f$ in $F$, one has (a) $u \in D(A)$ and (b) $f = Au$.

**Generalization.** The source gives the sequential test as sufficient for closedness in Banach
spaces. In metric spaces sequential closedness is equivalent to closedness, so the criterion
is stated in both directions and needs no completeness.

The source gives this as the method to prove that $A$ is closed. -/
theorem remark_2_11 (A : E →ₗ.[ℝ] F) :
    A.IsClosed ↔ ∀ (u : ℕ → A.domain) (x : E) (y : F),
      Tendsto (fun n => (u n : E)) atTop (𝓝 x) → Tendsto (fun n => A (u n)) atTop (𝓝 y) →
        ∃ hx : x ∈ A.domain, A ⟨x, hx⟩ = y :=
  LinearPMap.isClosed_iff_seq A

/-- **Remark 12** of [brezis2011functional], first clause. If $A : D(A) \subseteq E \to F$ is
closed, then $N(A)$ is closed.

**Generalization.** The source starts with Banach spaces. This statement works for arbitrary
real normed spaces. -/
theorem remark_2_12 {A : E →ₗ.[ℝ] F} (hA : A.IsClosed) : IsClosed (A.ker : Set E) :=
  hA.isClosed_ker

/-! ### The $\ell^2$ examples of Remarks 11, 12 and 20 -/

/-- The map $x \mapsto (x_n/(n+1))_{n \ge 0}$ on real sequences, which underlies the operator of
Remark 20 of [brezis2011functional]. -/
private def diagFun (x : ℕ → ℝ) : ℕ → ℝ := fun n => x n / (n + 1)

private theorem norm_diagFun_le (x : ℕ → ℝ) (n : ℕ) : ‖diagFun x n‖ ≤ ‖x n‖ := by
  simp only [diagFun, norm_div, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1)]
  exact div_le_self (abs_nonneg _) (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])

private theorem memℓp_diagFun (x : lp (fun _ : ℕ => ℝ) 2) : Memℓp (diagFun x) 2 :=
  (lp.memℓp x).mono' (norm_diagFun_le x)

/-- **Remark 20** of [brezis2011functional], the operator. On $\ell^2$, the operator
$$Ax = \Big(\frac{x_n}{n}\Big)_{n \ge 1}$$
is a bounded linear operator of norm at most $1$. It is also the example of the second clause of
Remark 12.

Sequences are indexed from $0$, so the operator is $x \mapsto (x_n/(n+1))_{n \ge 0}$. -/
def diagOperator : lp (fun _ : ℕ => ℝ) 2 →L[ℝ] lp (fun _ : ℕ => ℝ) 2 :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨diagFun x, memℓp_diagFun x⟩
      map_add' := fun x y => by
        ext n
        change (x + y) n / (n + 1) = x n / (n + 1) + y n / (n + 1)
        rw [lp.coeFn_add, Pi.add_apply, add_div]
      map_smul' := fun c x => by
        ext n
        change (c • x) n / (n + 1) = c * (x n / (n + 1))
        rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_div_assoc] }
    1 (fun x => by
      rw [one_mul]
      exact lp.norm_mono two_ne_zero (norm_diagFun_le x))

/-- The operator `Brezis.Chapter02.diagOperator` of Remark 20 acts by $(Ax)_n = x_n/(n+1)$ for
$n \ge 0$. -/
@[simp]
theorem diagOperator_apply (x : lp (fun _ : ℕ => ℝ) 2) (n : ℕ) :
    diagOperator x n = x n / (n + 1) :=
  rfl

/-- The operator `Brezis.Chapter02.diagOperator` of Remark 20 is injective. -/
theorem diagOperator_injective : Function.Injective diagOperator := by
  intro x y hxy
  ext n
  have := congrArg (fun z : lp (fun _ : ℕ => ℝ) 2 => z n) hxy
  simp only [diagOperator_apply] at this
  exact (div_left_inj' (by positivity)).1 this

/-- Every finitely supported sequence is in the range of the operator
`Brezis.Chapter02.diagOperator` of Remark 20: $A(e_n \cdot (n+1)a) = e_n \cdot a$, where $e_n$
is the $n$-th unit sequence and $a \in \mathbb{R}$. -/
theorem diagOperator_single (n : ℕ) (a : ℝ) :
    diagOperator (lp.single 2 n ((n + 1) * a)) = lp.single 2 n a := by
  ext m
  simp only [diagOperator_apply, lp.single_apply]
  rcases eq_or_ne m n with rfl | h
  · rw [Pi.single_eq_same, Pi.single_eq_same]
    exact mul_div_cancel_left₀ a (by positivity)
  · simp [h]

/-- The operator `Brezis.Chapter02.diagOperator` of Remark 20 has dense range: every $x \in \ell^2$
is the limit of its truncations, which are in the range. -/
theorem dense_range_diagOperator : Dense (Set.range diagOperator) := by
  intro x
  have hsum := (lp.hasSum_single (E := fun _ : ℕ => ℝ) (p := 2) (by norm_num) x).tendsto_sum_nat
  refine mem_closure_of_tendsto hsum (Eventually.of_forall fun N => ?_)
  refine ⟨∑ i ∈ Finset.range N, lp.single 2 i ((i + 1) * x i), ?_⟩
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => diagOperator_single i (x i)

/-- The sequence $(1/(n+1))_{n \ge 0}$ lies in $\ell^2$. -/
private theorem memℓp_inv_succ : Memℓp (fun n : ℕ => (1 : ℝ) / (n + 1)) 2 := by
  refine memℓp_gen ?_
  have : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have h := (Real.summable_one_div_nat_pow (p := 2)).2 one_lt_two
    have := (summable_nat_add_iff 1).2 h
    simpa using this
  refine this.congr fun n => ?_
  simp [ENNReal.toReal_ofNat, Real.norm_eq_abs]

/-- The operator `Brezis.Chapter02.diagOperator` of Remark 20 is not onto. A preimage of
$(1/(n+1))_{n \ge 0} \in \ell^2$ would be the constant sequence $1$, which is not in $\ell^2$. -/
theorem not_surjective_diagOperator : ¬ Function.Surjective diagOperator := by
  intro h
  obtain ⟨x, hx⟩ := h ⟨fun n => 1 / (n + 1), memℓp_inv_succ⟩
  have hx1 : ∀ n, x n = 1 := fun n => by
    have := congrArg (fun z : lp (fun _ : ℕ => ℝ) 2 => z n) hx
    simp only [diagOperator_apply] at this
    have h := (div_left_inj' (by positivity : ((n : ℝ) + 1) ≠ 0)).1 this
    simpa using h
  have hsum := (lp.memℓp x).summable (p := 2) (by norm_num)
  simp only [hx1, norm_one, Real.one_rpow] at hsum
  have := tendsto_const_nhds_iff.1 hsum.tendsto_atTop_zero
  exact one_ne_zero this

/-- **Remark 12** of [brezis2011functional], second clause. The range of a closed operator, even of
a bounded operator, need not be closed. The operator $Ax = (x_n/n)_{n \ge 1}$ on $\ell^2$, with
domain $\ell^2$, is closed, and its range is not closed.

The operator is `Brezis.Chapter02.diagOperator`, viewed as an unbounded operator with domain
$\ell^2$. Its range is also dense, by `Brezis.Chapter02.dense_range_diagOperator`. -/
theorem remark_2_12_range_not_closed :
    ¬ IsClosed (Set.range diagOperator) ∧
      ((diagOperator : lp (fun _ : ℕ => ℝ) 2 →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2).toPMap ⊤).IsClosed := by
  refine ⟨fun h => not_surjective_diagOperator ?_, diagOperator.isClosed_toPMap isClosed_univ⟩
  rw [← Set.range_eq_univ, ← h.closure_eq, dense_range_diagOperator.closure_eq]

/-- The finitely supported sequences, that is, the $x \in \ell^2$ with $x_n = 0$ for all large $n$,
as a linear subspace of $\ell^2$. -/
def finSuppSubmodule : Submodule ℝ (lp (fun _ : ℕ => ℝ) 2) where
  carrier := {x | ∃ N : ℕ, ∀ n, N ≤ n → x n = 0}
  zero_mem' := ⟨0, fun _ _ => rfl⟩
  add_mem' := fun {x y} ⟨N, hN⟩ ⟨M, hM⟩ => ⟨max N M, fun n hn => by
    rw [lp.coeFn_add, Pi.add_apply, hN n (le_of_max_le_left hn), hM n (le_of_max_le_right hn),
      add_zero]⟩
  smul_mem' := fun c {x} ⟨N, hN⟩ => ⟨N, fun n hn => by
    rw [lp.coeFn_smul, Pi.smul_apply, hN n hn, smul_zero]⟩

/-- The finitely supported sequences are dense in $\ell^2$. -/
theorem dense_finSuppSubmodule : Dense (finSuppSubmodule : Set (lp (fun _ : ℕ => ℝ) 2)) := by
  intro x
  have hsum := (lp.hasSum_single (E := fun _ : ℕ => ℝ) (p := 2) (by norm_num) x).tendsto_sum_nat
  refine mem_closure_of_tendsto hsum (Eventually.of_forall fun N => ⟨N, fun n hn => ?_⟩)
  rw [lp.coeFn_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [lp.single_apply, Pi.single_eq_of_ne]
  exact ne_of_gt (lt_of_lt_of_le (Finset.mem_range.1 hi) hn)

/-- The finitely supported sequences are not all of $\ell^2$. -/
theorem finSuppSubmodule_ne_top : finSuppSubmodule ≠ ⊤ := by
  intro h
  have hmem : (⟨fun n => 1 / (n + 1), memℓp_inv_succ⟩ : lp (fun _ : ℕ => ℝ) 2) ∈
      finSuppSubmodule := h ▸ Submodule.mem_top
  obtain ⟨N, hN⟩ := hmem
  have := hN N le_rfl
  change (1 : ℝ) / (N + 1) = 0 at this
  exact absurd this (by positivity)

/-- **Remark 11** of [brezis2011functional], the warning. In the criterion for closedness it does
not suffice to consider sequences with $u_n \to 0$. The weaker condition is closability, and a
closable operator need not be closed: there is an unbounded operator $A$ on $\ell^2$ that is
closable but not closed.

Closability is Mathlib's `LinearPMap.IsClosable`. The example is the zero operator on the
finitely supported sequences `Brezis.Chapter02.finSuppSubmodule`. It extends to the closed zero
operator on $\ell^2$, and it is not closed because its domain is dense and not all of $\ell^2$. -/
theorem remark_2_11_not_closed :
    ∃ A : lp (fun _ : ℕ => ℝ) 2 →ₗ.[ℝ] lp (fun _ : ℕ => ℝ) 2, A.IsClosable ∧ ¬ A.IsClosed := by
  refine ⟨(0 : lp (fun _ : ℕ => ℝ) 2 →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2).toPMap finSuppSubmodule, ?_, ?_⟩
  · rw [LinearPMap.isClosable_iff_exists_closed_extension]
    refine ⟨((0 : lp (fun _ : ℕ => ℝ) 2 →L[ℝ] lp (fun _ : ℕ => ℝ) 2) :
      lp (fun _ : ℕ => ℝ) 2 →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2).toPMap ⊤,
      ContinuousLinearMap.isClosed_toPMap _ isClosed_univ, LinearPMap.le_of_le_graph ?_⟩
    rintro ⟨x, y⟩ hxy
    rw [LinearPMap.mem_graph_iff] at hxy ⊢
    obtain ⟨u, hu, hy⟩ := hxy
    exact ⟨⟨u, trivial⟩, hu, hy⟩
  · intro h
    have hker := h.isClosed_ker
    rw [LinearMap.toPMap_ker, LinearMap.ker_zero, inf_top_eq] at hker
    exact finSuppSubmodule_ne_top
      (Submodule.dense_iff_topologicalClosure_eq_top.1 dense_finSuppSubmodule ▸
        hker.submodule_topologicalClosure_eq.symm)

/-! ### The adjoint -/

/-- **Section 2.6** of [brezis2011functional], the domain of the adjoint. Let
$A : D(A) \subseteq E \to F$ be an unbounded operator. Then $v \in F^\star$ is in $D(A^\star)$
if and only if there is a constant $c \ge 0$ such that
$$|\langle v, Au \rangle| \le c\|u\| \quad \text{for all } u \in D(A).$$

**Generalization.** The source starts with a densely defined operator between Banach spaces.
The same boundedness test defines the domain for any operator between normed spaces. The
value formula in `Brezis.Chapter02.adjoint_apply` still assumes a dense domain.

The adjoint is the backbone `LinearPMap.strongDualAdjoint`. Its domain is defined for every $A$,
densely defined or not. -/
theorem adjoint_domain_iff (A : E →ₗ.[ℝ] F) (v : StrongDual ℝ F) :
    v ∈ A.strongDualAdjoint.domain ↔
      ∃ c : ℝ, 0 ≤ c ∧ ∀ u : A.domain, |v (A u)| ≤ c * ‖(u : E)‖ := by
  rw [LinearPMap.mem_strongDualAdjoint_domain_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨max c 0, le_max_right _ _, fun u => ?_⟩
    rw [← Real.norm_eq_abs, Submodule.norm_coe]
    exact (hc u).trans (by gcongr; exact le_max_left _ _)
  · rintro ⟨c, -, hc⟩
    exact ⟨c, fun u => by rw [Real.norm_eq_abs, ← Submodule.norm_coe]; exact hc u⟩

/-- **Section 2.6** of [brezis2011functional], the fundamental adjoint relation. Let
$A : D(A) \subseteq E \to F$ be densely defined. Then
$$\langle v, Au \rangle_{F^\star, F} = \langle A^\star v, u \rangle_{E^\star, E} \quad \text{for
  all } u \in D(A),\ v \in D(A^\star).$$

**Generalization.** The source starts with Banach spaces. This statement works for arbitrary
real normed spaces.
-/
theorem adjoint_apply {A : E →ₗ.[ℝ] F} (hA : Dense (A.domain : Set E))
    (v : A.strongDualAdjoint.domain) (u : A.domain) :
    A.strongDualAdjoint v u = (v : StrongDual ℝ F) (A u) :=
  LinearPMap.strongDualAdjoint_apply hA v u

/-- **Section 2.6** of [brezis2011functional], uniqueness of the extension. Let
$A : D(A) \subseteq E \to F$ be densely defined and $v \in D(A^\star)$. If $f \in E^\star$
satisfies $\langle f, u \rangle = \langle v, Au \rangle$ for all $u \in D(A)$, then
$f = A^\star v$.

**Generalization.** The source starts with Banach spaces. This statement works for arbitrary
real normed spaces.

The source notes that the extension is unique since $D(A)$ is dense. -/
theorem adjoint_apply_eq {A : E →ₗ.[ℝ] F} (hA : Dense (A.domain : Set E))
    (v : A.strongDualAdjoint.domain) {f : StrongDual ℝ E}
    (hf : ∀ u : A.domain, f u = (v : StrongDual ℝ F) (A u)) : A.strongDualAdjoint v = f :=
  LinearPMap.strongDualAdjoint_apply_eq hA v hf

/-- **Remark 15** of [brezis2011functional], the weak-$\star$ clause. If
$A : D(A) \subseteq E \to F$ is closed and densely defined, then $D(A^\star)$ is dense in
$F^\star$ for the weak-$\star$ topology $\sigma(F^\star, F)$.

**Generalization.** The source starts with Banach spaces. This statement works for arbitrary
real normed spaces.

The weak-$\star$ topology is that of Mathlib's `WeakDual`, reached through
`StrongDual.toWeakDual`. -/
theorem remark_2_15 {A : E →ₗ.[ℝ] F} (hc : A.IsClosed) (hA : Dense (A.domain : Set E)) :
    Dense (StrongDual.toWeakDual '' (A.strongDualAdjoint.domain : Set (StrongDual ℝ F))) :=
  hc.dense_toWeakDual_domain_strongDualAdjoint hA

/-- **Remark 16** of [brezis2011functional]. Let $T \in \mathcal{L}(E, F)$, viewed as an unbounded
operator $A$ with $D(A) = E$. Then $A^\star$ is the bounded operator
$T^\star : F^\star \to E^\star$, $T^\star v = v \circ T$, with $D(A^\star) = F^\star$, and
$$\|T^\star\|_{\mathcal{L}(F^\star, E^\star)} = \|T\|_{\mathcal{L}(E, F)}.$$
In particular $A^\star$ is a bounded operator.

**Generalization.** The source starts with Banach spaces. This statement works for arbitrary
real normed spaces.

The operator $T^\star$ is `ContinuousLinearMap.strongDualMap`. -/
theorem remark_2_16 (T : E →L[ℝ] F) :
    ((T : E →ₗ[ℝ] F).toPMap ⊤).strongDualAdjoint =
        (T.strongDualMap : StrongDual ℝ F →ₗ[ℝ] StrongDual ℝ E).toPMap ⊤ ∧
      ‖T.strongDualMap‖ = ‖T‖ ∧
      IsBoundedOperator ((T : E →ₗ[ℝ] F).toPMap ⊤).strongDualAdjoint := by
  have hdense : Dense (((⊤ : Submodule ℝ E) : Submodule ℝ E) : Set E) := by
    rw [Submodule.top_coe]
    exact dense_univ
  refine ⟨T.toPMap_strongDualAdjoint hdense, T.opNorm_strongDualMap, ?_⟩
  rw [isBoundedOperator_iff]
  exact ⟨T.strongDualMap, T.toPMap_strongDualAdjoint hdense⟩

/-- **Proposition 2.17** of [brezis2011functional]. Let $A : D(A) \subseteq E \to F$ be a densely
defined unbounded linear operator. Then $A^\star$ is closed.

**Generalization.** The source starts with Banach spaces. This statement works for arbitrary
real normed spaces. -/
theorem proposition_2_17 {A : E →ₗ.[ℝ] F} (hA : Dense (A.domain : Set E)) :
    A.strongDualAdjoint.IsClosed :=
  LinearPMap.strongDualAdjoint_isClosed hA

/-- **Section 2.6** of [brezis2011functional], the graph orthogonality relations. Let
$A : D(A) \subseteq E \to F$ be densely defined, and let $I : F^\star \times E^\star \to E^\star
\times F^\star$ be the isomorphism $I([v, f]) = [-f, v]$. Then
$$I[G(A^\star)] = G(A)^\perp,$$
where $(E \times F)^\star$ is identified with $E^\star \times F^\star$. Moreover, for
$v \in F^\star$ and $f \in E^\star$,
$$[v, f] \in G(A^\star) \iff \langle f, u \rangle = \langle v, Au \rangle \quad \text{for all }
  u \in D(A).$$

**Generalization.** The source starts with Banach spaces. This statement works for arbitrary
real normed spaces.

The map $I$ is `LinearEquiv.skewSwap`, and the identification of $E^\star \times F^\star$ with
$(E \times F)^\star$ is `ContinuousLinearMap.coprodEquivL`. -/
theorem graph_adjoint_eq_annihilator_graph {A : E →ₗ.[ℝ] F} (hA : Dense (A.domain : Set E)) :
    (A.strongDualAdjoint.graph.map
      (LinearEquiv.skewSwap ℝ (StrongDual ℝ F) (StrongDual ℝ E) : _ →ₗ[ℝ] _)).map
        (((ContinuousLinearMap.coprodEquivL ℝ : (StrongDual ℝ E × StrongDual ℝ F) ≃L[ℝ]
          StrongDual ℝ (E × F)) : (StrongDual ℝ E × StrongDual ℝ F) →L[ℝ] StrongDual ℝ (E × F)) :
            (StrongDual ℝ E × StrongDual ℝ F) →ₗ[ℝ] StrongDual ℝ (E × F)) =
      A.graph.strongDualAnnihilator ∧
    ∀ (v : StrongDual ℝ F) (f : StrongDual ℝ E),
      (v, f) ∈ A.strongDualAdjoint.graph ↔ ∀ u : A.domain, f u = v (A u) :=
  ⟨LinearPMap.map_graph_strongDualAdjoint_eq_annihilator_graph hA,
    fun v f => LinearPMap.mem_graph_strongDualAdjoint_iff hA v f⟩

/-- **Corollary 2.18** of [brezis2011functional]. Let $A : D(A) \subseteq E \to F$ be a densely
defined closed unbounded operator. Then

**Generalization.** The source starts with Banach spaces. This statement works for arbitrary
real normed spaces.

(i) $N(A) = R(A^\star)^\perp$,

(ii) $N(A^\star) = R(A)^\perp$,

(iii) $N(A)^\perp \supseteq \overline{R(A^\star)}$,

(iv) $N(A^\star)^\perp = \overline{R(A)}$. -/
theorem corollary_2_18 {A : E →ₗ.[ℝ] F} (hc : A.IsClosed) (hA : Dense (A.domain : Set E)) :
    A.ker = (LinearMap.range A.strongDualAdjoint.toFun).strongDualCoannihilator ∧
      A.strongDualAdjoint.ker = (LinearMap.range A.toFun).strongDualAnnihilator ∧
      (LinearMap.range A.strongDualAdjoint.toFun).topologicalClosure ≤
        A.ker.strongDualAnnihilator ∧
      A.strongDualAdjoint.ker.strongDualCoannihilator =
        (LinearMap.range A.toFun).topologicalClosure :=
  ⟨hc.ker_eq_strongDualCoannihilator_range_strongDualAdjoint hA,
    LinearPMap.ker_strongDualAdjoint_eq_annihilator_range hA,
    LinearPMap.closure_range_strongDualAdjoint_le_annihilator_ker hA,
    LinearPMap.strongDualCoannihilator_ker_strongDualAdjoint_eq_closure_range hA⟩

/-- **Remark 17** of [brezis2011functional], the weak-$\star$ clause. Let
$A : D(A) \subseteq E \to F$ be densely defined and closed. Then $N(A)^\perp$ is the closure of
$R(A^\star)$ for the weak-$\star$ topology $\sigma(E^\star, E)$.

**Generalization.** The source starts with Banach spaces. This statement works for arbitrary
real normed spaces.

The weak-$\star$ topology is that of Mathlib's `WeakDual`, reached through
`StrongDual.toWeakDual`. -/
theorem remark_2_17 {A : E →ₗ.[ℝ] F} (hc : A.IsClosed) (hA : Dense (A.domain : Set E)) :
    StrongDual.toWeakDual '' (A.ker.strongDualAnnihilator : Set (StrongDual ℝ E)) =
      closure (StrongDual.toWeakDual ''
        (LinearMap.range A.strongDualAdjoint.toFun : Set (StrongDual ℝ E))) :=
  hc.annihilator_ker_eq_closure_toWeakDual_range_strongDualAdjoint hA

/-- **Remark 17** of [brezis2011functional], the last clause. Let $E$ be reflexive and let
$A : D(A) \subseteq E \to F$ be densely defined and closed. Then
$$N(A)^\perp = \overline{R(A^\star)},$$
with the closure in the norm topology of $E^\star$.

**Generalization.** The source starts with Banach spaces. This statement works for arbitrary
real normed spaces. -/
theorem remark_2_17_reflexive [IsReflexive ℝ E] {A : E →ₗ.[ℝ] F} (hc : A.IsClosed)
    (hA : Dense (A.domain : Set E)) :
    A.ker.strongDualAnnihilator =
      (LinearMap.range A.strongDualAdjoint.toFun).topologicalClosure := by
  rw [hc.ker_eq_strongDualCoannihilator_range_strongDualAdjoint hA,
    Submodule.strongDualAnnihilator_strongDualCoannihilator]

end Brezis.Chapter02

end

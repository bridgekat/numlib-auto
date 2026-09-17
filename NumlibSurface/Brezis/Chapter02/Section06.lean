import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.PSeries
import Numlib.Analysis.Normed.Operator.Unbounded.Adjoint
import Numlib.Analysis.Normed.Operator.Unbounded.Basic

/-!
# Brezis §2.6: unbounded linear operators, and the definition of the adjoint

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §2.6, over real Banach spaces `E`, `F`. An unbounded
operator `A : D(A) ⊆ E → F` is Mathlib's `LinearPMap`, `A : E →ₗ.[ℝ] F`, with `A.domain` the
book's `D(A)`; its graph, range and kernel are `A.graph`, `LinearMap.range A.toFun` and `A.ker`,
closedness is `A.IsClosed`, and "densely defined" is `Dense (A.domain : Set E)`. The adjoint
`A* : D(A*) ⊆ F* → E*` is the backbone `LinearPMap.strongDualAdjoint`
(`Numlib/Analysis/Normed/Operator/Unbounded/Adjoint`), and for a bounded operator it is
`ContinuousLinearMap.strongDualMap`.

## Main results

* `IsBoundedOperator`, `isBoundedOperator_iff` — the book's "bounded (or continuous)" operator,
  and its identification with a `ContinuousLinearMap` on all of `E`.
* `mem_graph_iff`, `mem_range_iff`, `mem_ker_iff`, `isClosed_iff` — the notation paragraph:
  graph, range, kernel and closedness.
* `remark_2_11`, `remark_2_12` — the sequential criterion for closedness; the kernel of a closed
  operator is closed.
* `adjoint_domain_iff`, `adjoint_apply`, `adjoint_apply_eq` — the definition of `A*`: its domain
  (24), the fundamental relation (25), and the uniqueness of the extension.
* `remark_2_15`, `remark_2_16`, `remark_2_17`, `remark_2_17_reflexive` — the weak-∗ density of
  `D(A*)`, the adjoint of a bounded operator, `N(A)^⊥` as the weak-∗ closure of `R(A*)`, and its
  norm form for reflexive `E`.
* `proposition_2_17`, `graph_adjoint_eq_annihilator_graph`, `corollary_2_18` — `A*` is closed;
  `I[G(A*)] = G(A)^⊥`; the four orthogonality relations between kernels and ranges.
* `diagOperator`, `remark_2_12_range_not_closed`, `remark_2_11_not_closed` — the `ℓ²` examples:
  the bounded operator `x ↦ (xₙ / n)` has dense, non-closed range (Remarks 12 and 20), and the
  zero operator on the finitely supported sequences is closable but not closed (Remark 11's
  warning: sequences `uₙ → 0` do not suffice).

Remarks 10, 13 and 14 are discussion (Remark 14 — the adjoint is defined by extension by
continuity, not Hahn–Banach — is the backbone's definition). The first clauses of Remarks 15 and
17 (the counterexamples on `ℓ¹`, Exercises 2.22–2.23) are not stated; the reflexive clause of
Remark 15 is Theorem 3.24, chapter 3. The `ℓ²` example of Remark 12 (a bounded operator whose
range is not closed) is `diagOperator` and `remark_2_12_range_not_closed`, and Remark 11's
warning is `remark_2_11_not_closed`.
-/

open Filter Topology NormedSpace
open scoped ENNReal

noncomputable section

namespace Brezis.Chapter02

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-! ### The definitions -/

/-- **The Definition of §2.6, "bounded (or continuous)":** an unbounded operator `A` is bounded
when `D(A) = E` and `‖A u‖ ≤ c ‖u‖` for some `c ≥ 0`. -/
def IsBoundedOperator (A : E →ₗ.[ℝ] F) : Prop :=
  A.domain = ⊤ ∧ ∃ c : ℝ, 0 ≤ c ∧ ∀ u : A.domain, ‖A u‖ ≤ c * ‖(u : E)‖

/-- A bounded unbounded operator is a `ContinuousLinearMap` on all of `E`, and conversely. -/
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

/-- **The graph** `G(A) = {[u, A u] | u ∈ D(A)} ⊆ E × F` is `A.graph`. -/
theorem mem_graph_iff (A : E →ₗ.[ℝ] F) (x : E) (y : F) :
    (x, y) ∈ A.graph ↔ ∃ u : A.domain, (u : E) = x ∧ A u = y :=
  LinearPMap.mem_graph_iff A

/-- **The range** `R(A) = {A u | u ∈ D(A)} ⊆ F` is `LinearMap.range A.toFun`. -/
theorem mem_range_iff (A : E →ₗ.[ℝ] F) (y : F) :
    y ∈ LinearMap.range A.toFun ↔ ∃ u : A.domain, A u = y :=
  LinearMap.mem_range

/-- **The kernel** `N(A) = {u ∈ D(A) | A u = 0} ⊆ E` is `A.ker`. -/
theorem mem_ker_iff (A : E →ₗ.[ℝ] F) (x : E) :
    x ∈ A.ker ↔ ∃ u : A.domain, x = u ∧ A u = 0 :=
  LinearPMap.mem_ker_iff

/-- **`A` is closed if `G(A)` is closed** in `E × F`. -/
theorem isClosed_iff (A : E →ₗ.[ℝ] F) : A.IsClosed ↔ IsClosed (A.graph : Set (E × F)) :=
  Iff.rfl

/-- **Remark 11.** To prove that `A` is closed one takes `uₙ ∈ D(A)` with `uₙ → u` and
`A uₙ → f` and checks (a) `u ∈ D(A)` and (b) `f = A u`; this is a characterization. -/
theorem remark_2_11 (A : E →ₗ.[ℝ] F) :
    A.IsClosed ↔ ∀ (u : ℕ → A.domain) (x : E) (y : F),
      Tendsto (fun n => (u n : E)) atTop (𝓝 x) → Tendsto (fun n => A (u n)) atTop (𝓝 y) →
        ∃ hx : x ∈ A.domain, A ⟨x, hx⟩ = y :=
  LinearPMap.isClosed_iff_seq A

/-- **Remark 12, first clause.** If `A` is closed then `N(A)` is closed. -/
theorem remark_2_12 {A : E →ₗ.[ℝ] F} (hA : A.IsClosed) : IsClosed (A.ker : Set E) :=
  hA.isClosed_ker

/-! ### The `ℓ²` examples of Remarks 11, 12 and 20 -/

/-- The pointwise map `x ↦ (xₙ / (n + 1))ₙ` of Remark 20 (the book's `xₙ / n` with `n ≥ 1`,
indexed from `0` here). -/
private def diagFun (x : ℕ → ℝ) : ℕ → ℝ := fun n => x n / (n + 1)

private theorem norm_diagFun_le (x : ℕ → ℝ) (n : ℕ) : ‖diagFun x n‖ ≤ ‖x n‖ := by
  simp only [diagFun, norm_div, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1)]
  exact div_le_self (abs_nonneg _) (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])

private theorem memℓp_diagFun (x : lp (fun _ : ℕ => ℝ) 2) : Memℓp (diagFun x) 2 :=
  (lp.memℓp x).mono' (norm_diagFun_le x)

/-- **The operator of Remark 20** (and of Remark 12's second clause) on `ℓ²`:
`A x = (xₙ / (n + 1))ₙ`, a bounded operator of norm at most `1`. -/
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

/-- The operator of Remark 20 acts by `(A x)ₙ = xₙ / (n + 1)`. -/
@[simp]
theorem diagOperator_apply (x : lp (fun _ : ℕ => ℝ) 2) (n : ℕ) :
    diagOperator x n = x n / (n + 1) :=
  rfl

/-- The operator of Remark 20 is injective. -/
theorem diagOperator_injective : Function.Injective diagOperator := by
  intro x y hxy
  ext n
  have := congrArg (fun z : lp (fun _ : ℕ => ℝ) 2 => z n) hxy
  simp only [diagOperator_apply] at this
  exact (div_left_inj' (by positivity)).1 this

/-- Every finitely supported sequence is in the range of the operator of Remark 20:
`A (lp.single n ((n + 1) a)) = lp.single n a`. -/
theorem diagOperator_single (n : ℕ) (a : ℝ) :
    diagOperator (lp.single 2 n ((n + 1) * a)) = lp.single 2 n a := by
  ext m
  simp only [diagOperator_apply, lp.single_apply]
  rcases eq_or_ne m n with rfl | h
  · rw [Pi.single_eq_same, Pi.single_eq_same]
    exact mul_div_cancel_left₀ a (by positivity)
  · simp [h]

/-- The operator of Remark 20 has dense range: every `x ∈ ℓ²` is the limit of its truncations,
which are in the range. -/
theorem dense_range_diagOperator : Dense (Set.range diagOperator) := by
  intro x
  have hsum := (lp.hasSum_single (E := fun _ : ℕ => ℝ) (p := 2) (by norm_num) x).tendsto_sum_nat
  refine mem_closure_of_tendsto hsum (Eventually.of_forall fun N => ?_)
  refine ⟨∑ i ∈ Finset.range N, lp.single 2 i ((i + 1) * x i), ?_⟩
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => diagOperator_single i (x i)

/-- The sequence `1 / (n + 1)` lies in `ℓ²`. -/
private theorem memℓp_inv_succ : Memℓp (fun n : ℕ => (1 : ℝ) / (n + 1)) 2 := by
  refine memℓp_gen ?_
  have : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have h := (Real.summable_one_div_nat_pow (p := 2)).2 one_lt_two
    have := (summable_nat_add_iff 1).2 h
    simpa using this
  refine this.congr fun n => ?_
  simp [ENNReal.toReal_ofNat, Real.norm_eq_abs]

/-- The operator of Remark 20 is not onto: `(1 / (n + 1))ₙ ∈ ℓ²` would have the constant
sequence `1` as preimage, which is not in `ℓ²`. -/
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

/-- **Remark 12, second clause.** The range of a closed (even bounded) operator need not be
closed: the operator `x ↦ (xₙ / (n + 1))` on `ℓ²` is closed (bounded, defined everywhere), and
its range is dense but not closed. -/
theorem remark_2_12_range_not_closed :
    ¬ IsClosed (Set.range diagOperator) ∧
      ((diagOperator : lp (fun _ : ℕ => ℝ) 2 →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2).toPMap ⊤).IsClosed := by
  refine ⟨fun h => not_surjective_diagOperator ?_, diagOperator.isClosed_toPMap isClosed_univ⟩
  rw [← Set.range_eq_univ, ← h.closure_eq, dense_range_diagOperator.closure_eq]

/-- The finitely supported sequences, as a subspace of `ℓ²`. -/
def finSuppSubmodule : Submodule ℝ (lp (fun _ : ℕ => ℝ) 2) where
  carrier := {x | ∃ N : ℕ, ∀ n, N ≤ n → x n = 0}
  zero_mem' := ⟨0, fun _ _ => rfl⟩
  add_mem' := fun {x y} ⟨N, hN⟩ ⟨M, hM⟩ => ⟨max N M, fun n hn => by
    rw [lp.coeFn_add, Pi.add_apply, hN n (le_of_max_le_left hn), hM n (le_of_max_le_right hn),
      add_zero]⟩
  smul_mem' := fun c {x} ⟨N, hN⟩ => ⟨N, fun n hn => by
    rw [lp.coeFn_smul, Pi.smul_apply, hN n hn, smul_zero]⟩

/-- The finitely supported sequences are dense in `ℓ²`. -/
theorem dense_finSuppSubmodule : Dense (finSuppSubmodule : Set (lp (fun _ : ℕ => ℝ) 2)) := by
  intro x
  have hsum := (lp.hasSum_single (E := fun _ : ℕ => ℝ) (p := 2) (by norm_num) x).tendsto_sum_nat
  refine mem_closure_of_tendsto hsum (Eventually.of_forall fun N => ⟨N, fun n hn => ?_⟩)
  rw [lp.coeFn_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [lp.single_apply, Pi.single_eq_of_ne]
  exact ne_of_gt (lt_of_lt_of_le (Finset.mem_range.1 hi) hn)

/-- The finitely supported sequences are not all of `ℓ²`. -/
theorem finSuppSubmodule_ne_top : finSuppSubmodule ≠ ⊤ := by
  intro h
  have hmem : (⟨fun n => 1 / (n + 1), memℓp_inv_succ⟩ : lp (fun _ : ℕ => ℝ) 2) ∈
      finSuppSubmodule := h ▸ Submodule.mem_top
  obtain ⟨N, hN⟩ := hmem
  have := hN N le_rfl
  change (1 : ℝ) / (N + 1) = 0 at this
  exact absurd this (by positivity)

/-- **Remark 11, the warning.** It does not suffice to consider sequences with `uₙ → 0` in the
criterion for closedness: that weaker condition is closability (`LinearPMap.IsClosable`), and a
closable operator need not be closed. The zero operator on the finitely supported sequences of
`ℓ²` is closable (it extends to the closed zero operator on `ℓ²`) but not closed, its domain being
dense and proper. -/
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

/-- **The definition of the adjoint, (24):** `D(A*)` is the set of `v ∈ F*` for which
`|⟨v, A u⟩| ≤ c ‖u‖` on `D(A)` for some `c ≥ 0`. -/
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

/-- **The fundamental relation (25):** `⟨v, A u⟩_{F*, F} = ⟨A* v, u⟩_{E*, E}` for `u ∈ D(A)`,
`v ∈ D(A*)`. -/
theorem adjoint_apply {A : E →ₗ.[ℝ] F} (hA : Dense (A.domain : Set E))
    (v : A.strongDualAdjoint.domain) (u : A.domain) :
    A.strongDualAdjoint v u = (v : StrongDual ℝ F) (A u) :=
  LinearPMap.strongDualAdjoint_apply hA v u

/-- **"The extension of `g` is unique, since `D(A)` is dense":** a functional `f ∈ E*` with
`f u = ⟨v, A u⟩` on `D(A)` is `A* v`. -/
theorem adjoint_apply_eq {A : E →ₗ.[ℝ] F} (hA : Dense (A.domain : Set E))
    (v : A.strongDualAdjoint.domain) {f : StrongDual ℝ E}
    (hf : ∀ u : A.domain, f u = (v : StrongDual ℝ F) (A u)) : A.strongDualAdjoint v = f :=
  LinearPMap.strongDualAdjoint_apply_eq hA v hf

/-- **Remark 15, the weak-∗ clause.** If `A` is closed and densely defined, `D(A*)` is dense in
`F*` for the weak-∗ topology `σ(F*, F)`. -/
theorem remark_2_15 {A : E →ₗ.[ℝ] F} (hc : A.IsClosed) (hA : Dense (A.domain : Set E)) :
    Dense (StrongDual.toWeakDual '' (A.strongDualAdjoint.domain : Set (StrongDual ℝ F))) :=
  hc.dense_toWeakDual_domain_strongDualAdjoint hA

/-- **Remark 16.** If `A` is a bounded operator, `A = T` on all of `E`, then `A*` is the bounded
operator `T* : F* → E*`, `T* v = v ∘ T`, with `D(A*) = F*` and `‖A*‖ = ‖A‖`. -/
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

/-- **Proposition 2.17.** The adjoint of a densely defined operator is closed. -/
theorem proposition_2_17 {A : E →ₗ.[ℝ] F} (hA : Dense (A.domain : Set E)) :
    A.strongDualAdjoint.IsClosed :=
  LinearPMap.strongDualAdjoint_isClosed hA

/-- **The orthogonality relation (27), `I[G(A*)] = G(A)^⊥`**, with `I [v, f] = [-f, v]` and
`(E × F)* = E* × F*`; and its pointwise form (28), `[v, f] ∈ G(A*) ⟺ ⟨f, u⟩ = ⟨v, A u⟩` on
`D(A)`. -/
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

/-- **Corollary 2.18.** For a densely defined closed `A`: (i) `N(A) = R(A*)^⊥`,
(ii) `N(A*) = R(A)^⊥`, (iii) `N(A)^⊥ ⊇ closure R(A*)`, (iv) `N(A*)^⊥ = closure R(A)`. -/
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

/-- **Remark 17, the weak-∗ clause.** For a densely defined closed `A`, `N(A)^⊥` is the closure
of `R(A*)` for the weak-∗ topology `σ(E*, E)`. -/
theorem remark_2_17 {A : E →ₗ.[ℝ] F} (hc : A.IsClosed) (hA : Dense (A.domain : Set E)) :
    StrongDual.toWeakDual '' (A.ker.strongDualAnnihilator : Set (StrongDual ℝ E)) =
      closure (StrongDual.toWeakDual ''
        (LinearMap.range A.strongDualAdjoint.toFun : Set (StrongDual ℝ E))) :=
  hc.annihilator_ker_eq_closure_toWeakDual_range_strongDualAdjoint hA

/-- **Remark 17, the last clause.** If `E` is reflexive then `N(A)^⊥ = closure R(A*)` in norm. -/
theorem remark_2_17_reflexive [IsReflexive ℝ E] {A : E →ₗ.[ℝ] F} (hc : A.IsClosed)
    (hA : Dense (A.domain : Set E)) :
    A.ker.strongDualAnnihilator =
      (LinearMap.range A.strongDualAdjoint.toFun).topologicalClosure := by
  rw [hc.ker_eq_strongDualCoannihilator_range_strongDualAdjoint hA,
    Submodule.strongDualAnnihilator_strongDualCoannihilator]

end Brezis.Chapter02

end

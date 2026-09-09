import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# Atkinson–Han §1.1: linear spaces

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §1.1.

Chapter 1 is the book's review of functional analysis, and Mathlib has essentially all of it.
Definitions 1.1.1, 1.1.3, 1.1.5, 1.1.8, 1.1.9, 1.1.13, 1.1.14 and 1.1.16 — linear space, subspace,
linear independence, span, basis and dimension, linear map, isomorphism, Cartesian product — are
Mathlib's `Module`, `Submodule`, `LinearIndependent`, `Submodule.span`, `Module.Basis` with
`FiniteDimensional`, `LinearMap`, `LinearEquiv` and `Prod`, and each is restated here under the
book's number.

## Main definitions

* `definition_1_1_3` — a subspace: a subset closed under addition and scalar multiplication.
* `definition_1_1_5` — linear independence of `v₁, …, vₙ`.
* `definition_1_1_8` — the span of `v₁, …, vₙ`, as a set of linear combinations.
* `definition_1_1_9` — a (finite) basis: a maximal linearly independent family.
* `definition_1_1_13` — a linear function: additive and homogeneous.
* `definition_1_1_14` — two spaces are isomorphic when a linear bijection joins them.

## Main results

* `definition_1_1_1` — Mathlib's `Module 𝕜 V` over an `AddCommGroup V` satisfies exactly the rules
  the book lists for a linear space.
* `definition_1_1_3_iff`, `definition_1_1_5_iff`, `definition_1_1_8_iff`, `definition_1_1_9_iff`,
  `definition_1_1_13_iff`, `definition_1_1_14_iff` — each restated definition read back as the
  Mathlib notion; later chapters rewrite along these.
* `definition_1_1_16` — the Cartesian product of two linear spaces, with componentwise operations.
* `theorem_1_1_10` — all bases of a linear space have the same number of elements, namely `dim V`.
* `example_1_1_2`, `example_1_1_4`, `example_1_1_6`, `example_1_1_7`, `example_1_1_11`,
  `example_1_1_12`, `example_1_1_15`, `example_1_1_17` — the illustrations of the section.

## Conventions

A numbered definition of this chapter is restated under its number. A definition naming a
*property of data* — subspace, independence, span, basis, linear map, isomorphism — is a
`def … : Prop` (or a `def … : Set V` for the span) written in the book's words, with a companion
`…_iff` reading it back as the Mathlib notion. A definition naming a *structure carried by a type*
— here the linear space itself and the Cartesian product — is a `theorem` recording that Mathlib's
class satisfies exactly the book's axioms, because in Lean the class *is* the structure and the
book's content is its axiom list.

`ℝ^d` is `EuclideanSpace ℝ (Fin d)` throughout this surface, and `𝔽ₖ`, the polynomials of degree
at most `k`, is `Polynomial.degreeLT ℝ (k + 1)`.

## Not formalized here

The exercises. Example 1.1.12 is stated as its dimension count `dim 𝔽_{n,0} + 2 = dim 𝔽ₙ`; the
explicit basis `x(1 - x), …, x^{n-1}(1 - x)` of `𝔽_{n,0}` the book exhibits along the way is not
part of the statement.
-/

open scoped Real

namespace AtkinsonHan.Chapter01

section LinearSpace

variable {𝕜 U V W : Type*} [DivisionRing 𝕜] [AddCommGroup U] [Module 𝕜 U] [AddCommGroup V]
  [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]

/-- **Definition 1.1.1.** A *linear space* (vector space) over the scalars `𝕂 = ℝ` or `ℂ` is a set
`V` with an addition `(u, v) ↦ u + v` and a scalar multiplication `(α, v) ↦ α v` obeying: the
commutative and associative laws for addition; the existence of a zero and of negatives;
`1 v = v`; `α (β v) = (α β) v`; and the two distributive laws.

This is Mathlib's `Module 𝕜 V` over an `AddCommGroup V`, and the statement below is that the class
satisfies exactly the book's rules. -/
theorem definition_1_1_1 (𝕜 V : Type*) [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] :
    (∀ u v : V, u + v = v + u) ∧
      (∀ u v w : V, u + v + w = u + (v + w)) ∧
      (∀ v : V, (0 : V) + v = v) ∧
      (∀ v : V, ∃ w : V, v + w = 0) ∧
      (∀ v : V, (1 : 𝕜) • v = v) ∧
      (∀ (α β : 𝕜) (v : V), α • β • v = (α * β) • v) ∧
      (∀ (α : 𝕜) (u v : V), α • (u + v) = α • u + α • v) ∧
      (∀ (α β : 𝕜) (v : V), (α + β) • v = α • v + β • v) :=
  ⟨add_comm, add_assoc, zero_add, fun v => ⟨-v, add_neg_cancel v⟩, one_smul 𝕜, smul_smul,
    smul_add, add_smul⟩

/-- **Example 1.1.2.** The standard linear spaces: `ℝ` and `ℂ`; `ℝ^d`; the continuous functions
`C(D)` on a set `D ⊆ ℝ^d`, and `C_p(2π)`, the continuous `2π`-periodic functions; and `Cᵐ(Ω)`. In
each function space the operations are the pointwise ones, and in `ℝ^d` the componentwise ones.

Mathlib has `ℝ`, `ℂ` and `EuclideanSpace ℝ (Fin d)` as modules by instance, the function spaces as
`C(D, ℝ)` and `C(AddCircle (2π), ℝ)`, and `Cᵐ` as the predicate `ContDiff ℝ m`; the statement below
records the operations and the closure of `Cᵐ` under them. -/
theorem example_1_1_2 {d : ℕ} (m : ℕ) (D : Set (EuclideanSpace ℝ (Fin d))) :
    (∀ (x y : EuclideanSpace ℝ (Fin d)) (α : ℝ) (i : Fin d),
        (x + y) i = x i + y i ∧ (α • x) i = α * x i) ∧
      (∀ (f g : C(D, ℝ)) (α : ℝ) (x : D), (f + g) x = f x + g x ∧ (α • f) x = α * f x) ∧
      (∀ (f g : C(AddCircle (2 * π), ℝ)) (α : ℝ) (x : AddCircle (2 * π)),
        (f + g) x = f x + g x ∧ (α • f) x = α * f x) ∧
      (∀ (f g : EuclideanSpace ℝ (Fin d) → ℝ) (α : ℝ), ContDiff ℝ m f → ContDiff ℝ m g →
        ContDiff ℝ m (f + g) ∧ ContDiff ℝ m (α • f)) :=
  ⟨fun _ _ _ _ => ⟨rfl, rfl⟩, fun _ _ _ _ => ⟨rfl, rfl⟩, fun _ _ _ _ => ⟨rfl, rfl⟩,
    fun _ _ α hf hg => ⟨hf.add hg, hf.const_smul α⟩⟩

/-- **Definition 1.1.3.** A *subspace* `W` of a linear space `V` is a subset of `V` closed under
the addition and the scalar multiplication of `V`: `u + v ∈ W` and `α v ∈ W` for `u, v ∈ W` and
`α ∈ 𝕂`. It is itself a linear space.

This is Mathlib's `Submodule 𝕜 V`, read as a predicate on subsets; `definition_1_1_3_iff` is the
correspondence. -/
def definition_1_1_3 (𝕜 : Type*) {V : Type*} [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (W : Set V) : Prop :=
  (∀ u ∈ W, ∀ v ∈ W, u + v ∈ W) ∧ ∀ α : 𝕜, ∀ v ∈ W, α • v ∈ W

/-- A nonempty subset of a linear space is a subspace in the sense of Definition 1.1.3 exactly
when it is the carrier of a `Submodule`. The nonemptiness is what the book leaves implicit: its two
closure conditions hold vacuously for the empty set, which is not a linear space. -/
theorem definition_1_1_3_iff {W : Set V} (hW : W.Nonempty) :
    definition_1_1_3 𝕜 W ↔ ∃ p : Submodule 𝕜 V, (p : Set V) = W := by
  constructor
  · rintro ⟨hadd, hsmul⟩
    obtain ⟨w, hw⟩ := hW
    have hzero : (0 : V) ∈ W := by simpa using hsmul 0 w hw
    exact ⟨{ carrier := W
             add_mem' := fun {a b} ha hb => hadd a ha b hb
             zero_mem' := hzero
             smul_mem' := fun c x hx => hsmul c x hx }, rfl⟩
  · rintro ⟨p, rfl⟩
    exact ⟨fun _ hu _ hv => p.add_mem hu hv, fun α _ hv => p.smul_mem α hv⟩

/-- **Example 1.1.4.** In `ℝ³` the `x₁x₂`-plane `W = {(x₁, x₂, 0)}` is a subspace, while the
translate `Ŵ = {(x₁, x₂, 1)}` is not: it is the affine set `x₀ + W` with `x₀ = (0, 0, 1)`. -/
theorem example_1_1_4 :
    definition_1_1_3 ℝ {x : EuclideanSpace ℝ (Fin 3) | x 2 = 0} ∧
      ¬ definition_1_1_3 ℝ {x : EuclideanSpace ℝ (Fin 3) | x 2 = 1} ∧
      ∀ x : EuclideanSpace ℝ (Fin 3), x 2 = 1 ↔
        ∃ w : EuclideanSpace ℝ (Fin 3), w 2 = 0 ∧ x = EuclideanSpace.single 2 (1 : ℝ) + w := by
  refine ⟨⟨fun u hu v hv => ?_, fun α v hv => ?_⟩, fun h => ?_, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · simp only [Set.mem_ofPred_eq] at hu hv ⊢
    simp [hu, hv]
  · simp only [Set.mem_ofPred_eq] at hv ⊢
    simp [hv]
  · have hx : EuclideanSpace.single (2 : Fin 3) (1 : ℝ) ∈
        {x : EuclideanSpace ℝ (Fin 3) | x 2 = 1} := by simp
    have h0 := h.2 0 _ hx
    simp only [Set.mem_ofPred_eq, zero_smul] at h0
    simp at h0
  · refine ⟨x - EuclideanSpace.single 2 (1 : ℝ), ?_, by abel⟩
    simp [hx]
  · rintro ⟨w, hw, rfl⟩
    simp [hw]

/-- **Definition 1.1.5.** The vectors `v₁, …, vₙ` are *linearly dependent* if some combination
`∑ αᵢ vᵢ = 0` has a nonzero coefficient, and *linearly independent* otherwise, that is if
`∑ αᵢ vᵢ = 0` forces every `αᵢ = 0`.

This is Mathlib's `LinearIndependent`; `definition_1_1_5_iff` is the correspondence. -/
def definition_1_1_5 (𝕜 : Type*) {V : Type*} [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    {n : ℕ} (v : Fin n → V) : Prop :=
  ∀ α : Fin n → 𝕜, ∑ i, α i • v i = 0 → ∀ i, α i = 0

/-- Definition 1.1.5 is Mathlib's `LinearIndependent`. -/
theorem definition_1_1_5_iff {n : ℕ} (v : Fin n → V) :
    definition_1_1_5 𝕜 v ↔ LinearIndependent 𝕜 v :=
  Fintype.linearIndependent_iff.symm

/-- **Example 1.1.6.** In `ℝ^d`, the `d` vectors `x⁽¹⁾, …, x⁽ᵈ⁾` are linearly independent if and
only if the determinant of the matrix whose columns they are is nonzero. -/
theorem example_1_1_6 {d : ℕ} (x : Fin d → EuclideanSpace ℝ (Fin d)) :
    definition_1_1_5 ℝ x ↔ (Matrix.of fun i j => x j i).det ≠ 0 := by
  rw [definition_1_1_5_iff]
  have hker : LinearMap.ker (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).toLinearMap = ⊥ :=
    LinearMap.ker_eq_bot_of_injective (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).injective
  have hmap := (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).toLinearMap.linearIndependent_iff hker
    (v := x)
  rw [← hmap, ← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det,
    ← Matrix.linearIndependent_cols_iff_isUnit]
  rfl

/-- **Example 1.1.7.** Within `C[0, 1]` the vectors `1, x, x², …, xⁿ` are linearly independent: a
vanishing combination is a polynomial with infinitely many roots, hence the zero polynomial, hence
has all coefficients zero. -/
theorem example_1_1_7 (n : ℕ) :
    definition_1_1_5 ℝ (fun j : Fin (n + 1) =>
      (⟨fun x => (x : ℝ) ^ (j : ℕ), by fun_prop⟩ : C(Set.Icc (0 : ℝ) 1, ℝ))) := by
  classical
  intro α hα j
  set p : Polynomial ℝ := ∑ j : Fin (n + 1), Polynomial.C (α j) * Polynomial.X ^ (j : ℕ) with hp
  have hroot : {x : ℝ | p.IsRoot x}.Infinite := by
    refine Set.Infinite.mono (fun x hx => ?_) (Set.Icc_infinite (by norm_num : (0 : ℝ) < 1))
    have hev := congrArg (fun f : C(Set.Icc (0 : ℝ) 1, ℝ) => f ⟨x, hx⟩) hα
    simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul, Pi.smul_apply,
      ContinuousMap.coe_mk, smul_eq_mul, ContinuousMap.zero_apply] at hev
    simpa [Polynomial.IsRoot, hp, Polynomial.eval_finsetSum] using hev
  have hzero : p = 0 := Polynomial.eq_zero_of_infinite_isRoot p hroot
  have hcoeff : p.coeff (j : ℕ) = α j := by
    simp only [hp, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      mul_ite, mul_one, mul_zero, Fin.val_inj]
    simp
  rw [← hcoeff, hzero, Polynomial.coeff_zero]

/-- **Definition 1.1.8.** The *span* of `v₁, …, vₙ ∈ V` is the set of all their linear
combinations, `span {v₁, …, vₙ} = {∑ αᵢ vᵢ | αᵢ ∈ 𝕂}`; it is a subspace of `V`.

This is Mathlib's `Submodule.span 𝕜 (Set.range v)`; `definition_1_1_8_iff` is the
correspondence. -/
def definition_1_1_8 (𝕜 : Type*) {V : Type*} [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    {n : ℕ} (v : Fin n → V) : Set V :=
  {u | ∃ α : Fin n → 𝕜, u = ∑ i, α i • v i}

/-- Definition 1.1.8 is Mathlib's `Submodule.span`. -/
theorem definition_1_1_8_iff {n : ℕ} (v : Fin n → V) :
    definition_1_1_8 𝕜 v = (Submodule.span 𝕜 (Set.range v) : Set V) := by
  ext u
  simp only [definition_1_1_8, Set.mem_ofPred_eq, SetLike.mem_coe,
    Submodule.mem_span_range_iff_exists_fun]
  exact ⟨fun ⟨α, hα⟩ => ⟨α, hα.symm⟩, fun ⟨α, hα⟩ => ⟨α, hα.symm⟩⟩

/-- The span of Definition 1.1.8 is a subspace in the sense of Definition 1.1.3, as the book
observes right after the definition. -/
theorem definition_1_1_8_isSubspace {n : ℕ} (v : Fin n → V) :
    definition_1_1_3 𝕜 (definition_1_1_8 𝕜 v) := by
  rw [definition_1_1_8_iff]
  exact ⟨fun _ hu _ hv => Submodule.add_mem _ hu hv, fun α _ hv => Submodule.smul_mem _ α hv⟩

/-- **Definition 1.1.9.** A linear space is *finite dimensional* if it has a finite maximal
independent set `{v₁, …, vₙ}`: the family is linearly independent, but `{v₁, …, vₙ, v}` is
dependent for every `v ∈ V`. Such a family is called a *basis* of the space; if no finite basis
exists, the space is *infinite dimensional*.

The predicate below is "`v` is a basis of `V`" in this sense; it is Mathlib's `Module.Basis` by
`definition_1_1_9_iff`, and the existence of some such `v` is `FiniteDimensional` by
`definition_1_1_9_finiteDimensional_iff`. -/
def definition_1_1_9 (𝕜 : Type*) {V : Type*} [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    {n : ℕ} (v : Fin n → V) : Prop :=
  definition_1_1_5 𝕜 v ∧ ∀ w : V, ¬ definition_1_1_5 𝕜 (Fin.snoc v w)

/-- A finite maximal independent family is exactly a `Module.Basis`. -/
theorem definition_1_1_9_iff {n : ℕ} (v : Fin n → V) :
    definition_1_1_9 𝕜 v ↔ ∃ b : Module.Basis (Fin n) 𝕜 V, ⇑b = v := by
  simp only [definition_1_1_9, definition_1_1_5_iff, linearIndependent_finSnoc, not_and, not_not]
  constructor
  · rintro ⟨hli, hmax⟩
    have hspan : ⊤ ≤ Submodule.span 𝕜 (Set.range v) := fun w _ => hmax w hli
    exact ⟨Module.Basis.mk hli hspan, by simp⟩
  · rintro ⟨b, rfl⟩
    refine ⟨b.linearIndependent, fun w _ => ?_⟩
    rw [b.span_eq]
    trivial

/-- A linear space is finite dimensional in the sense of Definition 1.1.9 — it has a finite
maximal independent set — exactly when it is Mathlib's `FiniteDimensional`. -/
theorem definition_1_1_9_finiteDimensional_iff (𝕜 V : Type*) [DivisionRing 𝕜] [AddCommGroup V]
    [Module 𝕜 V] :
    (∃ (n : ℕ) (v : Fin n → V), definition_1_1_9 𝕜 v) ↔ FiniteDimensional 𝕜 V := by
  constructor
  · rintro ⟨n, v, hv⟩
    obtain ⟨b, rfl⟩ := (definition_1_1_9_iff _).mp hv
    exact Module.Finite.of_basis b
  · intro _
    obtain ⟨s, b⟩ := Module.Free.exists_basis (R := 𝕜) (M := V)
    have : Fintype s := FiniteDimensional.fintypeBasisIndex b
    exact ⟨Fintype.card s, _, (definition_1_1_9_iff _).mpr ⟨b.reindex (Fintype.equivFin s), rfl⟩⟩

/-- **Theorem 1.1.10.** Any two bases of a linear space have the same number of elements, and that
number is the dimension of the space: for every basis `b : Module.Basis ι 𝕜 V` the cardinality of
the index type is `dim V`. Comparing two bases through this equality is the book's statement. -/
theorem theorem_1_1_10 {ι : Type*} (b : Module.Basis ι 𝕜 V) :
    Nat.card ι = Module.finrank 𝕜 V :=
  (Module.finrank_eq_nat_card_basis b).symm

/-- **Example 1.1.11.** The space `ℝ^d` is `d`-dimensional, with canonical basis the coordinate
vectors `eᵢ = (0, …, 0, 1, 0, …, 0)`. -/
theorem example_1_1_11 (d : ℕ) :
    definition_1_1_9 ℝ (fun i : Fin d => EuclideanSpace.single i (1 : ℝ)) ∧
      Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d :=
  ⟨(definition_1_1_9_iff _).mpr ⟨(EuclideanSpace.basisFun (Fin d) ℝ).toBasis, by ext i : 1; simp⟩,
    finrank_euclideanSpace_fin⟩

/-- **Example 1.1.12.** In the space `𝔽ₙ` of polynomials of degree at most `n` the family
`1, x, …, xⁿ` is a basis, so `dim 𝔽ₙ = n + 1`; and for the subspace
`𝔽_{n,0} = {p ∈ 𝔽ₙ | p 0 = p 1 = 0}` one has `dim 𝔽_{n,0} = dim 𝔽ₙ - 2`, the difference `2`
recording the two zero conditions at `0` and `1`.

The subspace is described by the hypothesis `hW` rather than named, and the count is written
`dim 𝔽_{n,0} + 2 = dim 𝔽ₙ` to stay inside `ℕ`. The book's explicit basis
`x(1 - x), …, x^{n-1}(1 - x)` of `𝔽_{n,0}` is not part of the statement. -/
theorem example_1_1_12 {n : ℕ} (hn : 1 ≤ n) (W : Submodule ℝ (Polynomial.degreeLT ℝ (n + 1)))
    (hW : ∀ p : Polynomial.degreeLT ℝ (n + 1),
      p ∈ W ↔ (p : Polynomial ℝ).eval 0 = 0 ∧ (p : Polynomial ℝ).eval 1 = 0) :
    Module.finrank ℝ (Polynomial.degreeLT ℝ (n + 1)) = n + 1 ∧
      Module.finrank ℝ W + 2 = Module.finrank ℝ (Polynomial.degreeLT ℝ (n + 1)) := by
  have hdim : Module.finrank ℝ (Polynomial.degreeLT ℝ (n + 1)) = n + 1 := by
    rw [(Polynomial.degreeLTEquiv ℝ (n + 1)).finrank_eq, Module.finrank_fin_fun]
  have _ : FiniteDimensional ℝ (Polynomial.degreeLT ℝ (n + 1)) :=
    Module.Finite.equiv (Polynomial.degreeLTEquiv ℝ (n + 1)).symm
  set L : Polynomial.degreeLT ℝ (n + 1) →ₗ[ℝ] ℝ × ℝ :=
    { toFun := fun p => ((p : Polynomial ℝ).eval 0, (p : Polynomial ℝ).eval 1)
      map_add' := fun p q => by simp
      map_smul' := fun c p => by
        simp [Polynomial.smul_eq_C_mul, Prod.smul_mk] } with hL
  have hWker : W = LinearMap.ker L := by
    ext p
    rw [hW p, LinearMap.mem_ker, hL]
    simp [Prod.ext_iff]
  have hrange : LinearMap.range L = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨a, b⟩
    have hdeg : (Polynomial.C a + Polynomial.C (b - a) * Polynomial.X) ∈
        Polynomial.degreeLT ℝ (n + 1) := by
      refine Polynomial.mem_degreeLT.2 (lt_of_le_of_lt (Polynomial.degree_add_le _ _) ?_)
      refine max_lt (lt_of_le_of_lt Polynomial.degree_C_le ?_)
        (lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) ?_)
      · have h0 : ((0 : ℕ) : WithBot ℕ) < ((n + 1 : ℕ) : WithBot ℕ) := by
          exact_mod_cast Nat.succ_pos n
        simpa using h0
      · have h1 : ((1 : ℕ) : WithBot ℕ) < ((n + 1 : ℕ) : WithBot ℕ) := by
          exact_mod_cast (by omega : 1 < n + 1)
        simpa using h1
    refine ⟨⟨_, hdeg⟩, ?_⟩
    simp [hL]
  have hcount := L.finrank_range_add_finrank_ker
  rw [hrange, finrank_top, Module.finrank_prod, Module.finrank_self] at hcount
  refine ⟨hdim, ?_⟩
  rw [hWker]
  omega

/-- **Definition 1.1.13.** A function `L` from a linear space `V` to a linear space `W` is a
*linear function* (mapping, operator, transformation) when it is additive,
`L (u + v) = L u + L v`, and homogeneous, `L (α v) = α L v`.

This is Mathlib's `LinearMap`; `definition_1_1_13_iff` is the correspondence. Chapter 2 of the book
develops the notion, and this surface follows it there. -/
def definition_1_1_13 (𝕜 : Type*) {V W : Type*} [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup W] [Module 𝕜 W] (L : V → W) : Prop :=
  (∀ u v : V, L (u + v) = L u + L v) ∧ ∀ (α : 𝕜) (v : V), L (α • v) = α • L v

/-- Definition 1.1.13 is Mathlib's `LinearMap`. -/
theorem definition_1_1_13_iff (L : V → W) :
    definition_1_1_13 𝕜 L ↔ ∃ T : V →ₗ[𝕜] W, ⇑T = L :=
  ⟨fun h => ⟨⟨⟨L, h.1⟩, h.2⟩, rfl⟩, by rintro ⟨T, rfl⟩; exact ⟨map_add T, map_smul T⟩⟩

/-- **Definition 1.1.14.** Two linear spaces `U` and `V` are *isomorphic* when there is a linear
bijection `ℓ : U → V`.

This is Mathlib's `LinearEquiv`; `definition_1_1_14_iff` is the correspondence. -/
def definition_1_1_14 (𝕜 U V : Type*) [DivisionRing 𝕜] [AddCommGroup U] [Module 𝕜 U]
    [AddCommGroup V] [Module 𝕜 V] : Prop :=
  ∃ l : U → V, definition_1_1_13 𝕜 l ∧ Function.Bijective l

/-- Definition 1.1.14 is Mathlib's `LinearEquiv`. -/
theorem definition_1_1_14_iff (𝕜 U V : Type*) [DivisionRing 𝕜] [AddCommGroup U] [Module 𝕜 U]
    [AddCommGroup V] [Module 𝕜 V] :
    definition_1_1_14 𝕜 U V ↔ Nonempty (U ≃ₗ[𝕜] V) := by
  constructor
  · rintro ⟨l, hl, hbij⟩
    obtain ⟨T, rfl⟩ := (definition_1_1_13_iff (𝕜 := 𝕜) l).mp hl
    exact ⟨LinearEquiv.ofBijective T hbij⟩
  · rintro ⟨e⟩
    exact ⟨e, ⟨map_add e, map_smul e⟩, e.bijective⟩

/-- **Example 1.1.15.** The set `𝔽ₖ` of polynomials of degree at most `k` is a subspace of
`C[0, 1]`, and `a₀ + a₁ x + ⋯ + a_k x^k ↦ (a₀, a₁, …, a_k)` is an isomorphism `𝔽ₖ ≅ ℝ^{k+1}`. -/
theorem example_1_1_15 (k : ℕ) :
    definition_1_1_3 ℝ {f : C(Set.Icc (0 : ℝ) 1, ℝ) |
        ∃ p ∈ Polynomial.degreeLT ℝ (k + 1), ∀ x, f x = p.eval (x : ℝ)} ∧
      definition_1_1_14 ℝ (Polynomial.degreeLT ℝ (k + 1)) (EuclideanSpace ℝ (Fin (k + 1))) := by
  refine ⟨⟨fun f hf g hg => ?_, fun α f hf => ?_⟩, (definition_1_1_14_iff _ _ _).mpr
    ⟨(Polynomial.degreeLTEquiv ℝ (k + 1)).trans (WithLp.linearEquiv 2 ℝ (Fin (k + 1) → ℝ)).symm⟩⟩
  · obtain ⟨p, hp, hfp⟩ := hf
    obtain ⟨q, hq, hgq⟩ := hg
    exact ⟨p + q, Submodule.add_mem _ hp hq, fun x => by simp [hfp x, hgq x]⟩
  · obtain ⟨p, hp, hfp⟩ := hf
    exact ⟨α • p, Submodule.smul_mem _ α hp, fun x => by
      simp only [ContinuousMap.smul_apply, smul_eq_mul, hfp x, Polynomial.smul_eq_C_mul,
        Polynomial.eval_mul, Polynomial.eval_C]⟩

/-- **Definition 1.1.16.** The *Cartesian product* `W = U × V` of two linear spaces is the set of
pairs `(u, v)` with componentwise addition and scalar multiplication,
`(u₁, v₁) + (u₂, v₂) = (u₁ + u₂, v₁ + v₂)` and `α (u, v) = (α u, α v)`; it is a linear space.

This is Mathlib's `Prod` with its `Module` instance, and the statement below is that the instance
is the componentwise one. -/
theorem definition_1_1_16 (u₁ u₂ : U) (v₁ v₂ : V) (α : 𝕜) :
    ((u₁, v₁) + (u₂, v₂) : U × V) = (u₁ + u₂, v₁ + v₂) ∧
      α • ((u₁, v₁) : U × V) = (α • u₁, α • v₁) :=
  ⟨rfl, rfl⟩

/-- **Example 1.1.17.** The real plane is the Cartesian product of two real lines, `ℝ² = ℝ × ℝ`;
in general `ℝ^d` is the `d`-fold product of `ℝ`, which in Mathlib is the dependent product
`Fin d → ℝ` underlying `EuclideanSpace ℝ (Fin d)`. -/
theorem example_1_1_17 (d : ℕ) :
    definition_1_1_14 ℝ (EuclideanSpace ℝ (Fin 2)) (ℝ × ℝ) ∧
      definition_1_1_14 ℝ (EuclideanSpace ℝ (Fin d)) (Fin d → ℝ) :=
  ⟨(definition_1_1_14_iff _ _ _).mpr
      ⟨(WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).trans (LinearEquiv.finTwoArrow ℝ ℝ)⟩,
    (definition_1_1_14_iff _ _ _).mpr ⟨WithLp.linearEquiv 2 ℝ (Fin d → ℝ)⟩⟩

end LinearSpace

end AtkinsonHan.Chapter01

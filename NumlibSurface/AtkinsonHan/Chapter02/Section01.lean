import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.Matrix.Rank
import Numlib.Analysis.Calculus.ContDiffMapIcc

/-!
# Atkinson–Han §2.1: operators

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §2.1: operators, their domain, range and null set,
injectivity and surjectivity, continuity and boundedness.

Definition 2.1.1 is Mathlib's `Function.Injective`, `Function.Surjective` and `Function.Bijective`,
and is restated here under the book's number; the domain, range and null set of an operator are
`Set.univ`, `Set.range` and `T ⁻¹' {0}`, or for a linear map `LinearMap.range` and `LinearMap.ker`,
and none of those is restated.

## Main definitions

* `definition_2_1_1`, `definition_2_1_1_surjective`, `definition_2_1_1_bijection` — the three
  clauses of Definition 2.1.1: an injective operator, an operator of `V` onto `W`, and a bijection.
* `IsBoundedOperator` — Definition 2.1.6, the book's boundedness of a not necessarily linear
  operator: *bounded sets have bounded images*, not "the operator norm is finite". The distinction
  matters, because the two differ for a nonlinear operator and the point of Theorem 2.2.4 is that
  for a linear operator they agree.

## Main results

* `definition_2_1_1_iff`, `definition_2_1_1_surjective_iff`, `definition_2_1_1_bijection_iff` —
  each clause read back as the Mathlib notion; later sections rewrite along these.
* `definition_2_1_1_inverse` — the book's rule `v = T⁻¹ w ⟺ w = T v` determines exactly one inverse
  of a bijection.
* `isBoundedOperator_iff_image_bounded` — the two readings the book gives of Definition 2.1.6.
* `example_2_1_2` — the identity operator is a bijection whose inverse is again the identity.
* `example_2_1_3` — a matrix operator is injective exactly when `rank A = n`, and surjective
  exactly when `rank A = m`.
* `example_2_1_4`, `example_2_1_5` — the differentiation operator read on `C¹[0, 1]`: `d/dx` is
  surjective onto `C[0, 1]` and not injective, its null set the constants, and `D : v ↦ (v', v(0))`
  repairs the injectivity, being a bijection onto `C[0, 1] × ℝ`.
* `example_2_1_7` — the half of Example 2.1.7 that needs no `C¹[0, 1]`: differentiation is
  *unbounded* for the sup norm on `C[0, 1]`.

The bridge to the estimate `‖T v‖ ≤ γ ‖v‖` for a *linear* operator is Proposition 2.2.3, and lives
in §2.2 with the rest of that discussion.

## Conventions

The convention of Chapter 1 continues: a numbered definition naming a property of data is a
`def … : Prop` in the book's own words with a companion `…_iff` reading it back as the Mathlib
notion, and a further clause of a definition takes a descriptive suffix rather than a letter.

Definition 2.1.1 asks nothing of `V` and `W` beyond their being sets, which is how §2.1 opens, so
its three clauses are stated for bare types. Example 2.1.3 is stated over an arbitrary field, which
covers both the real matrices the book writes and the complex ones of the remark after it.

`C¹[0, 1]` is the backbone's `ContDiffMapIcc (zero_le_one : (0 : ℝ) ≤ 1) 1`
(`Numlib.Analysis.Calculus.ContDiffMapIcc`), whose norm is exactly the book's (2.1.2)
`‖v‖_∞ + ‖v'‖_∞`, and `C[0, 1]` is `C(Set.Icc 0 1, ℝ)` as in §1.2. Its `v'` is
`ContDiffMapIcc.deriv v 1`.

## Not formalized here

The *bounded* half of Example 2.1.7, that `d/dx : C¹[0, 1] → C[0, 1]` is bounded for the norm
(2.1.2), is the backbone's `ContDiffMapIcc.derivCLM`, whose operator norm is at most `1`; it is not
restated here. The *unbounded* half needs no `C¹[0, 1]` and is `example_2_1_7`.
-/

open Bornology Metric

namespace AtkinsonHan.Chapter02

/-! ### Definition 2.1.1: injections, surjections and bijections -/

section Bijection

variable {V W : Type*}

/-- **Definition 2.1.1.** An operator `T : V → W` is *one-to-one*, or *injective*, when
`v₁ ≠ v₂ ⇒ T v₁ ≠ T v₂` (2.1.1).

This is Mathlib's `Function.Injective`; `definition_2_1_1_iff` is the correspondence. -/
def definition_2_1_1 (T : V → W) : Prop :=
  ∀ v₁ v₂ : V, v₁ ≠ v₂ → T v₁ ≠ T v₂

/-- Definition 2.1.1 is Mathlib's `Function.Injective`. -/
theorem definition_2_1_1_iff (T : V → W) : definition_2_1_1 T ↔ Function.Injective T :=
  ⟨fun h v₁ v₂ hv => by_contra fun hne => h v₁ v₂ hne hv, fun h _ _ hne hv => hne (h hv)⟩

/-- **Definition 2.1.1**, second clause. `T` *maps `V` onto `W`*, or is *surjective*, when its
range is all of `W`: `R(T) = W`.

This is Mathlib's `Function.Surjective`; `definition_2_1_1_surjective_iff` is the
correspondence. -/
def definition_2_1_1_surjective (T : V → W) : Prop :=
  Set.range T = Set.univ

/-- The second clause of Definition 2.1.1 is Mathlib's `Function.Surjective`. -/
theorem definition_2_1_1_surjective_iff (T : V → W) :
    definition_2_1_1_surjective T ↔ Function.Surjective T :=
  Set.range_eq_univ

/-- **Definition 2.1.1**, third clause. An operator that is both injective and surjective is a
*bijection* from `V` to `W`.

This is Mathlib's `Function.Bijective`; `definition_2_1_1_bijection_iff` is the correspondence. -/
def definition_2_1_1_bijection (T : V → W) : Prop :=
  definition_2_1_1 T ∧ definition_2_1_1_surjective T

/-- The third clause of Definition 2.1.1 is Mathlib's `Function.Bijective`. -/
theorem definition_2_1_1_bijection_iff (T : V → W) :
    definition_2_1_1_bijection T ↔ Function.Bijective T := by
  rw [definition_2_1_1_bijection, definition_2_1_1_iff, definition_2_1_1_surjective_iff,
    Function.Bijective]

/-- The inverse of a bijection, as the book defines it right after Definition 2.1.1: exactly one
`T⁻¹ : W → V` obeys the rule `v = T⁻¹ w ⟺ w = T v`. -/
theorem definition_2_1_1_inverse {T : V → W} (h : definition_2_1_1_bijection T) :
    ∃! S : W → V, ∀ (v : V) (w : W), v = S w ↔ w = T v := by
  obtain ⟨hinj, hsurj⟩ := (definition_2_1_1_bijection_iff T).mp h
  refine ⟨Function.surjInv hsurj, fun v w => ⟨?_, ?_⟩, fun S hS => funext fun w => ?_⟩
  · rintro rfl
    exact (Function.surjInv_eq hsurj w).symm
  · rintro rfl
    exact (hinj (Function.surjInv_eq hsurj (T v))).symm
  · exact ((hS (Function.surjInv hsurj w) w).mpr (Function.surjInv_eq hsurj w).symm).symm

/-- **Example 2.1.2.** The identity operator `I v = v` on a linear space `V` is a bijection from
`V` to `V`, and its inverse is again the identity operator. -/
theorem example_2_1_2 (V : Type*) :
    definition_2_1_1_bijection (id : V → V) ∧
      ∀ S : V → V, (∀ (v w : V), v = S w ↔ w = id v) → S = id :=
  ⟨(definition_2_1_1_bijection_iff _).mpr Function.bijective_id,
    fun _ hS => funext fun w => ((hS w w).mpr rfl).symm⟩

/-- **Example 2.1.3.** For `L v = A v` with `A` an `m × n` matrix, `L` is injective if and only if
`rank A = n`, and surjective if and only if `rank A = m`.

The book states this over `ℝ` and remarks that the same holds over `ℂ`; both are the statement
below over an arbitrary field, the book's `ℝⁿ` being `Fin n → ℝ`. The rank is Mathlib's
`Matrix.rank`, the dimension of the range of `v ↦ A v`, which is the book's maximal number of
independent columns. -/
theorem example_2_1_3 {𝕜 : Type*} [Field 𝕜] {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n 𝕜) :
    (definition_2_1_1 A.mulVec ↔ A.rank = Fintype.card n) ∧
      (definition_2_1_1_surjective A.mulVec ↔ A.rank = Fintype.card m) := by
  have hcoe : ⇑A.mulVecLin = A.mulVec := rfl
  have hrank : A.rank = Module.finrank 𝕜 (LinearMap.range A.mulVecLin) := rfl
  have hcount := A.mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_pi] at hcount
  constructor
  · rw [definition_2_1_1_iff, ← hcoe]
    constructor
    · intro hinj
      have hker : LinearMap.ker A.mulVecLin = ⊥ := LinearMap.ker_eq_bot_of_injective hinj
      rw [hrank, ← hcount, hker, finrank_bot, add_zero]
    · intro hcard
      rw [hrank] at hcard
      have hker : Module.finrank 𝕜 (LinearMap.ker A.mulVecLin) = 0 := by omega
      exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hker)
  · rw [definition_2_1_1_surjective_iff, ← hcoe, ← LinearMap.range_eq_top]
    constructor
    · intro htop
      rw [hrank, htop, finrank_top, Module.finrank_pi]
    · intro hcard
      refine Submodule.eq_top_of_finrank_eq ?_
      rw [← hrank, hcard, Module.finrank_pi]

end Bijection

/-! ### Definition 2.1.6: bounded operators -/

variable {V W : Type*} [SeminormedAddCommGroup V] [SeminormedAddCommGroup W]

/-- **Definition 2.1.6.** An operator `T : V → W` between normed spaces is *bounded* when it maps
bounded sets to bounded sets: for every `r > 0` there is an `R` with `‖T v‖ ≤ R` whenever
`‖v‖ ≤ r`. This is the book's notion, and it is not "the operator norm of `T` is finite": the two
agree for linear operators (Theorem 2.2.4) and differ in general. -/
def IsBoundedOperator (T : V → W) : Prop :=
  ∀ r > 0, ∃ R : ℝ, ∀ v : V, ‖v‖ ≤ r → ‖T v‖ ≤ R

/-- The two readings the book gives of Definition 2.1.6 agree: `T` is bounded on every ball if and
only if it maps every bounded set to a bounded set. -/
theorem isBoundedOperator_iff_image_bounded (T : V → W) :
    IsBoundedOperator T ↔ ∀ B : Set V, IsBounded B → IsBounded (T '' B) := by
  constructor
  · intro hT B hB
    obtain ⟨r, hr⟩ := isBounded_iff_forall_norm_le.mp hB
    obtain ⟨R, hR⟩ := hT (max r 1) (lt_of_lt_of_le zero_lt_one (le_max_right r 1))
    refine isBounded_iff_forall_norm_le.mpr ⟨R, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    exact hR v ((hr v hv).trans (le_max_left r 1))
  · intro hT r _
    obtain ⟨R, hR⟩ :=
      isBounded_iff_forall_norm_le.mp (hT (closedBall 0 r) isBounded_closedBall)
    exact ⟨R, fun v hv => hR _ ⟨v, by simpa using hv, rfl⟩⟩

/-- **Example 2.1.7**, the half that needs no `C¹[0, 1]`: *differentiation is not a bounded
operator for the sup norm on `C[0, 1]`*. There is no `γ` with `‖v'‖_∞ ≤ γ ‖v‖_∞` for every
continuously differentiable `v`, and the book's witnesses show it: `v_n (x) = sin (n x)` has
`‖v_n‖_∞ ≤ 1` while `v_n' (0) = n`.

The statement is the negation in witness form — for every `γ` such a `v` exists — because the
bounded reading of the operator would need `C¹[0, 1]` as a normed space, which Mathlib does not
have; the other half of the Example, that `d/dx` *is* bounded for `‖v‖_∞ + ‖v'‖_∞`, waits on that
space. -/
theorem example_2_1_7 (γ : ℝ) :
    ∃ v v' : ℝ → ℝ, (∀ x, HasDerivAt v (v' x) x) ∧ Continuous v' ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, |v x| ≤ 1) ∧ ∃ x ∈ Set.Icc (0 : ℝ) 1, γ < |v' x| := by
  set n : ℝ := max γ 0 + 1 with hn
  have hn1 : γ < n := by simp [hn]; linarith [le_max_left γ 0]
  refine ⟨fun x => Real.sin (n * x), fun x => n * Real.cos (n * x), fun x => ?_,
    by fun_prop, fun x _ => Real.abs_sin_le_one _, 0, by norm_num, ?_⟩
  · have h := (Real.hasDerivAt_sin (n * x)).comp x ((hasDerivAt_id x).const_mul n)
    simpa [Function.comp_def, mul_comm] using h
  · have hn0 : (0 : ℝ) < n := by positivity
    simp only [mul_zero, Real.cos_zero, mul_one]
    rwa [abs_of_pos hn0]

/-! ### Examples 2.1.4 and 2.1.5: the differentiation operator on `C¹[0, 1]` -/

section Differentiation

open Set ContDiffMapIcc

/-- **Example 2.1.4.** The differentiation operator `d/dx : v ↦ v'`, with domain the proper
subspace `C¹[0, 1]` of `C[0, 1]` and values in `C[0, 1]`, is a surjection; it is not injective, and
its null set is the set of constant functions.

`C¹[0, 1]` is the backbone's `ContDiffMapIcc (zero_le_one : (0 : ℝ) ≤ 1) 1`, whose norm is the
book's (2.1.2); `v'` is its first derivative `ContDiffMapIcc.deriv v 1`. -/
theorem example_2_1_4 :
    Function.Surjective (fun v : ContDiffMapIcc (zero_le_one : (0 : ℝ) ≤ 1) 1 => v.deriv 1) ∧
      ¬Function.Injective (fun v : ContDiffMapIcc (zero_le_one : (0 : ℝ) ≤ 1) 1 => v.deriv 1) ∧
      ∀ v : ContDiffMapIcc (zero_le_one : (0 : ℝ) ≤ 1) 1,
        v.deriv 1 = 0 ↔ ∃ c : ℝ, ∀ t : Icc (0 : ℝ) 1, v t = c := by
  refine ⟨fun w => ⟨cons (ofContinuousMap _ w) 0, rfl⟩, fun hinj => ?_, fun v => ⟨?_, ?_⟩⟩
  · have h : cons (ofContinuousMap _ (0 : C(Icc (0 : ℝ) 1, ℝ))) 1 = 0 := hinj rfl
    have h0 := congrArg (fun v : ContDiffMapIcc (zero_le_one : (0 : ℝ) ≤ 1) 1 =>
      v ⟨0, left_mem_Icc.2 zero_le_one⟩) h
    simp at h0
  · intro h
    refine ⟨v ⟨0, left_mem_Icc.2 zero_le_one⟩, fun t => ?_⟩
    have hv : v.deriv 0 t = v.deriv 0 ⟨0, left_mem_Icc.2 zero_le_one⟩
        + ContinuousMap.integralIccCLM zero_le_one t (v.deriv 1) :=
      (ContinuousMap.hasDerivIcc_iff zero_le_one).1 (v.hasDerivIcc 0) t
    rw [h, map_zero, add_zero] at hv
    exact hv
  · rintro ⟨c, hc⟩
    have hconst : v.deriv 0 = ContinuousMap.const (Icc (0 : ℝ) 1) c := ContinuousMap.ext hc
    have hd : ContinuousMap.HasDerivIcc zero_le_one (v.deriv 0) (v.deriv 1) := v.hasDerivIcc 0
    refine hd.unique zero_lt_one ?_
    rw [hconst]
    exact ContinuousMap.hasDerivIcc_const zero_le_one c

/-- **Example 2.1.5.** The operator `D : v ↦ (v', v(0))` is a bijection from `C¹[0, 1]` onto
`C[0, 1] × ℝ`, repairing the non-injectivity of `d/dx` of Example 2.1.4: the inverse sends `(w, c)`
to the antiderivative of `w` taking the value `c` at `0`. -/
theorem example_2_1_5 :
    Function.Bijective (fun v : ContDiffMapIcc (zero_le_one : (0 : ℝ) ≤ 1) 1 =>
      (v.deriv 1, v ⟨0, left_mem_Icc.2 zero_le_one⟩)) := by
  refine Function.bijective_iff_has_inverse.2
    ⟨fun p => cons (ofContinuousMap _ p.1) p.2, fun v => ?_, fun p => ?_⟩
  · change cons (ofContinuousMap _ (v.deriv 1)) (v ⟨0, left_mem_Icc.2 zero_le_one⟩) = v
    rw [show ofContinuousMap (zero_le_one : (0 : ℝ) ≤ 1) (v.deriv 1) = shift v from
      ofContinuousMap_deriv (shift v)]
    exact cons_shift v
  · exact Prod.ext rfl (cons_left _ _)

end Differentiation

end AtkinsonHan.Chapter02

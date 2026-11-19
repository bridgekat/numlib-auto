/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.Matrix.Rank
import Numlib.Analysis.Calculus.ContDiffMapIcc

/-!
# Atkinson and Han, Section 2.1: Operators

This module formalizes §2.1 of [han2009theoretical]: operators $T : V \to W$, their domain, range
and null set, injectivity, surjectivity and bijectivity, the inverse of a bijection, and boundedness
of a not necessarily linear operator. The examples are the identity operator, matrix operators,
whose injectivity and surjectivity are rank conditions, and the differentiation operator
$v \mapsto v'$ on $C^1[0, 1]$. Differentiation maps $C^1[0, 1]$ onto $C[0, 1]$ with the constants as
null set, the operator $v \mapsto (v', v(0))$ is a bijection onto $C[0, 1] \times \mathbb{R}$, and
differentiation is not bounded for the maximum norm.

Definition 2.1.1 is Mathlib's `Function.Injective`, `Function.Surjective` and `Function.Bijective`,
and it is restated here under the number of the book. The domain, range and null set of an operator
are `Set.univ`, `Set.range` and `T ⁻¹' {0}`, or `LinearMap.range` and `LinearMap.ker` for a linear
map, and they are not restated. The space $C^1[0, 1]$ comes from the backbone module
`Numlib.Analysis.Calculus.ContDiffMapIcc`. For a linear operator, the link between boundedness and
the estimate $\|Tv\| \le \gamma \|v\|$ is Proposition 2.2.3, in §2.2.

## Main definitions

* Definition 2.1.1, `AtkinsonHan.Chapter02.definition_2_1_1`,
  `AtkinsonHan.Chapter02.definition_2_1_1_surjective` and
  `AtkinsonHan.Chapter02.definition_2_1_1_bijection`: an injective operator, an operator of $V$ onto
  $W$, and a bijection.
* Definition 2.1.6, `AtkinsonHan.Chapter02.IsBoundedOperator`: an operator is bounded if it maps
  bounded sets to bounded sets. For a nonlinear operator this differs from the finiteness of an
  operator norm, and Theorem 2.2.4 shows that the two agree for a linear operator.

## Main results

* Definition 2.1.1, `AtkinsonHan.Chapter02.definition_2_1_1_iff`,
  `AtkinsonHan.Chapter02.definition_2_1_1_surjective_iff` and
  `AtkinsonHan.Chapter02.definition_2_1_1_bijection_iff`: each clause is the corresponding Mathlib
  notion.
* Definition 2.1.1, `AtkinsonHan.Chapter02.definition_2_1_1_inverse`: the rule
  $v = T^{-1} w \iff w = Tv$ determines exactly one inverse of a bijection.
* Example 2.1.2, `AtkinsonHan.Chapter02.example_2_1_2`: the identity operator is a bijection, and
  its inverse is the identity.
* Example 2.1.3, `AtkinsonHan.Chapter02.example_2_1_3`: for an $m \times n$ matrix $A$,
  $v \mapsto Av$ is injective if and only if $\operatorname{rank} A = n$, and surjective if and only
  if $\operatorname{rank} A = m$.
* Example 2.1.4, `AtkinsonHan.Chapter02.example_2_1_4`: $d/dx : C^1[0, 1] \to C[0, 1]$ is surjective
  and not injective, and its null set is the constant functions.
* Example 2.1.5, `AtkinsonHan.Chapter02.example_2_1_5`: $v \mapsto (v', v(0))$ is a bijection from
  $C^1[0, 1]$ onto $C[0, 1] \times \mathbb{R}$.
* Definition 2.1.6, `AtkinsonHan.Chapter02.isBoundedOperator_iff_image_bounded`: the two readings of
  Definition 2.1.6 agree.
* Example 2.1.7, `AtkinsonHan.Chapter02.example_2_1_7`: differentiation is not bounded for the
  maximum norm on $C[0, 1]$.

## Conventions

* The space $C^1[0, 1]$ is the backbone's `ContDiffMapIcc (zero_le_one : (0 : ℝ) ≤ 1) 1`, whose norm
  is the book's norm (2.1.2), $\|v\|_\infty + \|v'\|_\infty$. The derivative $v'$ is
  `ContDiffMapIcc.deriv v 1`. The space $C[0, 1]$ is `C(Set.Icc 0 1, ℝ)`, as in §1.2.

## Implementation notes

* As in Chapter 1, a numbered definition that names a property of data is a `def … : Prop` in the
  words of the book, with a companion theorem `…_iff` that identifies it with the Mathlib notion. A
  further clause of a definition takes a descriptive suffix rather than a letter.
* Definition 2.1.1 asks nothing of $V$ and $W$ beyond being sets, so its three clauses are stated
  for arbitrary types.
* Example 2.1.3 is stated over an arbitrary field. This covers the real matrices of the book and the
  complex matrices of the remark after the example.

## Deviations from the source

* **Definition 2.1.1 and Example 2.1.2** (generalization). The three mapping properties,
  the inverse of a bijection, and the identity example apply to arbitrary types.
* **Example 2.1.3** (generalization). The rank criteria apply over any field.
* **Definition 2.1.6, boundedness** (generalization). The boundedness criterion is for total
  maps of seminormed additive groups. Its real bound may be increased to make it positive.
* **Example 2.1.7** (reading). The formalization exhibits functions with bounded supremum norm
  and arbitrarily large derivative norm as witnesses against boundedness.

## Not formalized

* **The general inverse into the range after Definition 2.1.1.** The inverse statement gives
  the case of a bijective map.
* **The continuity criterion in Definition 2.1.6.** `ContinuousOn` handles continuity on a
  specified domain. The surface definition covers boundedness.

* **The bounded half of Example 2.1.7**, that $d/dx : C^1[0, 1] \to C[0, 1]$ is bounded for the norm
  (2.1.2). It is the backbone's `ContDiffMapIcc.derivCLM`, whose operator norm is at most $1$, and
  it is not restated here.
-/

open Bornology Metric

namespace AtkinsonHan.Chapter02

/-! ### Definition 2.1.1: injections, surjections and bijections -/

section Bijection

variable {V W : Type*}

/-- **Definition 2.1.1** of [han2009theoretical]. An operator $T : V \to W$ is **one-to-one**, or
**injective**, if $v_1 \neq v_2$ implies $T v_1 \neq T v_2$ (2.1.1).

The predicate is `Function.Injective` by `AtkinsonHan.Chapter02.definition_2_1_1_iff`.

**Generalization.** The criterion applies to total functions between arbitrary types. -/
def definition_2_1_1 (T : V → W) : Prop :=
  ∀ v₁ v₂ : V, v₁ ≠ v₂ → T v₁ ≠ T v₂

/-- An operator $T : V \to W$ is injective in the sense of Definition 2.1.1 of [han2009theoretical]
if and only if it is `Function.Injective`. -/
theorem definition_2_1_1_iff (T : V → W) : definition_2_1_1 T ↔ Function.Injective T :=
  ⟨fun h v₁ v₂ hv => by_contra fun hne => h v₁ v₂ hne hv, fun h _ _ hne hv => hne (h hv)⟩

/-- **Definition 2.1.1** of [han2009theoretical], second clause. An operator $T : V \to W$ **maps
$V$ onto $W$**, or is **surjective**, if its range is all of $W$: $R(T) = W$.

The predicate is `Function.Surjective` by
`AtkinsonHan.Chapter02.definition_2_1_1_surjective_iff`.

**Generalization.** The criterion applies to total functions between arbitrary types. -/
def definition_2_1_1_surjective (T : V → W) : Prop :=
  Set.range T = Set.univ

/-- An operator $T : V \to W$ maps $V$ onto $W$ in the sense of the second clause of Definition
2.1.1 of [han2009theoretical] if and only if it is `Function.Surjective`. -/
theorem definition_2_1_1_surjective_iff (T : V → W) :
    definition_2_1_1_surjective T ↔ Function.Surjective T :=
  Set.range_eq_univ

/-- **Definition 2.1.1** of [han2009theoretical], third clause. An operator $T : V \to W$ that is
both injective and surjective is a **bijection** from $V$ to $W$.

The predicate is `Function.Bijective` by `AtkinsonHan.Chapter02.definition_2_1_1_bijection_iff`.

**Generalization.** The criterion applies to total functions between arbitrary types. -/
def definition_2_1_1_bijection (T : V → W) : Prop :=
  definition_2_1_1 T ∧ definition_2_1_1_surjective T

/-- An operator $T : V \to W$ is a bijection in the sense of the third clause of Definition 2.1.1 of
[han2009theoretical] if and only if it is `Function.Bijective`. -/
theorem definition_2_1_1_bijection_iff (T : V → W) :
    definition_2_1_1_bijection T ↔ Function.Bijective T := by
  rw [definition_2_1_1_bijection, definition_2_1_1_iff, definition_2_1_1_surjective_iff,
    Function.Bijective]

/-- The inverse of a bijection, as the book defines it after Definition 2.1.1 of
[han2009theoretical]. If $T : V \to W$ is a bijection, then exactly one map $T^{-1} : W \to V$
satisfies $$v = T^{-1} w \iff w = T v \qquad \text{for all } v \in V, \ w \in W.$$

**Generalization.** The inverse characterization applies to bijections between arbitrary types. -/
theorem definition_2_1_1_inverse {T : V → W} (h : definition_2_1_1_bijection T) :
    ∃! S : W → V, ∀ (v : V) (w : W), v = S w ↔ w = T v := by
  obtain ⟨hinj, hsurj⟩ := (definition_2_1_1_bijection_iff T).mp h
  refine ⟨Function.surjInv hsurj, fun v w => ⟨?_, ?_⟩, fun S hS => funext fun w => ?_⟩
  · rintro rfl
    exact (Function.surjInv_eq hsurj w).symm
  · rintro rfl
    exact (hinj (Function.surjInv_eq hsurj (T v))).symm
  · exact ((hS (Function.surjInv hsurj w) w).mpr (Function.surjInv_eq hsurj w).symm).symm

/-- **Example 2.1.2** of [han2009theoretical]. The identity operator $I v = v$ on a set $V$ is a
bijection from $V$ to $V$, and its inverse is again the identity: every $S : V \to V$ with
$v = S w \iff w = v$ for all $v, w \in V$ is the identity.

The book takes $V$ to be a linear space; the statement holds for any set.

**Generalization.** The identity and inverse properties do not need a linear structure. -/
theorem example_2_1_2 (V : Type*) :
    definition_2_1_1_bijection (id : V → V) ∧
      ∀ S : V → V, (∀ (v w : V), v = S w ↔ w = id v) → S = id :=
  ⟨(definition_2_1_1_bijection_iff _).mpr Function.bijective_id,
    fun _ hS => funext fun w => ((hS w w).mpr rfl).symm⟩

/-- **Example 2.1.3** of [han2009theoretical]. Let $A$ be an $m \times n$ matrix over a field
$\mathbb{K}$, and let $L v = A v$. Then $L$ is injective if and only if
$\operatorname{rank} A = n$, and $L$ is surjective if and only if $\operatorname{rank} A = m$.

The book states the example over $\mathbb{R}$ and remarks that the same holds over $\mathbb{C}$;
both are cases of the statement over an arbitrary field. The rows and columns are indexed by
finite types `m` and `n`, the space of column vectors is `n → 𝕜`, and $L$ is `A.mulVec`. The rank
is `Matrix.rank`, the dimension of the range of $v \mapsto Av$, which is the book's maximal
number of linearly independent columns.

**Generalization.** Both rank criteria are generalized from real and complex matrices to matrices
over any field.
-/
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

/-- **Definition 2.1.6** of [han2009theoretical]. Let $V$ and $W$ be normed spaces. An operator
$T : V \to W$, not necessarily linear, is **bounded** if it maps bounded sets to bounded sets:
for every $r > 0$ there is an $R$ with $\|T v\| \le R$ whenever $\|v\| \le r$.

This is not the condition that the operator norm of $T$ be finite. The two conditions agree for
linear operators (Theorem 2.2.4) and differ in general. The equivalence with "bounded sets have
bounded images" is `AtkinsonHan.Chapter02.isBoundedOperator_iff_image_bounded`. The spaces are
seminormed groups, and no linear structure is used.

**Reading.** The function is defined on the whole source type. The bound may be increased to
obtain a strictly positive bound as in the source. -/
def IsBoundedOperator (T : V → W) : Prop :=
  ∀ r > 0, ∃ R : ℝ, ∀ v : V, ‖v‖ ≤ r → ‖T v‖ ≤ R

/-- An operator $T : V \to W$ between normed spaces is bounded in the sense of Definition 2.1.6 of
[han2009theoretical] if and only if, for every bounded set $B \subseteq V$, the image $T(B)$ is
bounded. These are the two readings of the definition that the book gives.

**Generalization.** The equivalence applies to total maps between seminormed additive groups. -/
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

/-- **Example 2.1.7** of [han2009theoretical], the unbounded half. Differentiation is not a bounded
operator for the maximum norm on $C[0, 1]$. Precisely, for every $\gamma \in \mathbb{R}$ there
is a differentiable function $v : \mathbb{R} \to \mathbb{R}$ with continuous derivative $v'$
such that $|v(x)| \le 1$ for all $x \in [0, 1]$ and $|v'(x)| > \gamma$ for some $x \in [0, 1]$.
Hence no $\gamma$ satisfies $\|v'\|_\infty \le \gamma \|v\|_\infty$ for all continuously
differentiable $v$.

**Reading.** The book states discontinuity in the supremum norm. Lean gives unboundedness in
witness form with functions $v_n(x)=\sin(nx)$, for which $\|v_n\|_\infty \le 1$ and $v_n'(0)=n$.
The bounded half of the example, that $d/dx$ is bounded for the norm
$\|v\|_\infty + \|v'\|_\infty$, is the backbone's `ContDiffMapIcc.derivCLM`. -/
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

/-! ### Examples 2.1.4 and 2.1.5: the differentiation operator on $C^1[0, 1]$ -/

section Differentiation

open Set ContDiffMapIcc

/-- **Example 2.1.4** of [han2009theoretical]. The differentiation operator $d/dx : v \mapsto v'$,
with domain the proper subspace $C^1[0, 1]$ of $C[0, 1]$ and values in $C[0, 1]$, is surjective
and not injective. Its null set is the set of constant functions: $v' = 0$ if and only if $v$ is
constant on $[0, 1]$.

The space $C^1[0, 1]$ is the backbone's `ContDiffMapIcc (zero_le_one : (0 : ℝ) ≤ 1) 1`, whose
norm is the book's norm (2.1.2), and $v'$ is its first derivative `ContDiffMapIcc.deriv v 1`. -/
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

/-- **Example 2.1.5** of [han2009theoretical]. The operator $D v = (v', v(0))$ is a bijection from
$C^1[0, 1]$ onto $C[0, 1] \times \mathbb{R}$. It repairs the failure of injectivity of $d/dx$ in
Example 2.1.4: the inverse sends $(w, c)$ to the antiderivative of $w$ with the value $c$ at
$0$. -/
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

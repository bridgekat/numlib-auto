/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Dual
import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Analysis.Normed.Operator.Scaling

/-!
# Bounded sesquilinear forms on Hilbert spaces

Let $V$ be an inner product space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. A bounded
sesquilinear form on $V$ is a continuous map $a \colon V \times V \to \mathbb{K}$ that is
conjugate-linear in its first argument and linear in its second, like the inner product
$\langle u, v \rangle$. This module defines the basic properties of such a form: boundedness with a
constant $M$, $|a(u, v)| \le M \|u\| \|v\|$; coercivity with a constant $c$,
$c \|v\|^2 \le \operatorname{Re} a(v, v)$, which [han2009theoretical] call "$V$-elliptic" or
"strongly positive"; and Hermitian symmetry, $a(u, v) = \overline{a(v, u)}$. On a Hilbert space, the
form has an associated operator $A$ with $\langle Au, v \rangle = a(u, v)$, and every functional
$\ell$ has a Riesz representative $f$ with $\langle f, v \rangle = \ell(v)$. The correspondence
$a \leftrightarrow A$ is an isometric bijection, and it carries coercivity and Hermitian symmetry of
the form to coercivity and symmetry of the operator ([han2009theoretical], §8.3 and §9.4;
[kress1998numerical], §11.3; [saad2003iterative], §5.2 in the language of operators).

The module also defines the energy functional $E(v) = \frac12 \operatorname{Re} a(v, v) -
\operatorname{Re} \ell(v)$ and the energy norm $\|v\|_a = \sqrt{\operatorname{Re} a(v, v)}$, which
satisfies $\sqrt{c} \|v\| \le \|v\|_a \le \sqrt{M} \|v\|$. It defines the restriction of a form to a
subspace, which keeps Hermitian symmetry and coercivity. Finally it defines forms
$a \colon U \times V \to \mathbb{K}$ on two spaces, with the inf–sup condition $\alpha \|u\| \le
\sup_{v \neq 0} |a(u, v)| / \|v\|$ and the nondegeneracy condition that are the hypotheses of the
Babuška–Nečas theorem.

## Main definitions

* `SesqForm`: the bounded sesquilinear forms on $V$.
* `SesqForm.IsBoundedWith`, `SesqForm.IsCoerciveWith`, `SesqForm.IsHermitian`: boundedness with a
  constant $M$, coercivity with a constant $c$, and Hermitian symmetry.
* `SesqForm.toOperator`: the operator $A$ with $\langle Au, v \rangle = a(u, v)$.
* `SesqForm.rieszRep`: the Riesz representative of a functional.
* `SesqForm.energy`, `SesqForm.energyNorm`: the energy functional and the energy norm.
* `SesqForm.restrict`: the restriction of a form to a subspace.
* `SesqForm₂`, `SesqForm₂.InfSupWith`, `SesqForm₂.IsNondegenerate`: forms on two spaces, the inf–sup
  condition and nondegeneracy.

## Main results

* `SesqForm.toOperator_ofOperator`, `SesqForm.ofOperator_toOperator`: forms and operators correspond
  bijectively.
* `SesqForm.norm_toOperator`: the correspondence preserves norms.
* `SesqForm.isCoerciveWith_iff_toOperator`, `SesqForm.isHermitian_iff_toOperator_isSymmetric`: a
  form is coercive or Hermitian if and only if its operator is coercive or symmetric.
* `SesqForm.sqrt_mul_norm_le_energyNorm`, `SesqForm.energyNorm_le_sqrt_mul_norm`:
  $\sqrt{c} \|v\| \le \|v\|_a \le \sqrt{M} \|v\|$.
* `SesqForm.IsCoerciveWith.infSupWith`: a coercive form satisfies the inf–sup condition with the
  same constant.

## Implementation notes

* A form is `V →L⋆[𝕜] V →L[𝕜] 𝕜`, conjugate-linear in the first argument, as `innerSL`. The operator
  norm `‖a‖` of this map is the least boundedness constant of the form.
* Over $\mathbb{R}$, a map `V →L[ℝ] V →L[ℝ] ℝ` is by definition a `V →L⋆[ℝ] V →L[ℝ] ℝ`, as in
  Mathlib's proof of the Lax–Milgram theorem. So real bilinear forms need no conversion, and the
  lemmas with the suffix `_real` remove the real parts and the conjugations.
* The operator of a form is Mathlib's `InnerProductSpace.continuousLinearMapOfBilin`.
* The weak problems on $H^1_0$ in the Sobolev part of the library are posed with
  `SesqForm.restrict`.
-/

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- The type of **bounded sesquilinear forms** on an inner product space $V$ over $\mathbb{K}$:
continuous maps $a \colon V \times V \to \mathbb{K}$, conjugate-linear in the first argument and
linear in the second.

It is `V →L⋆[𝕜] V →L[𝕜] 𝕜`, with the same convention as the inner product `innerSL`. -/
abbrev SesqForm (𝕜 V : Type*) [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] :=
  V →L⋆[𝕜] V →L[𝕜] 𝕜

namespace SesqForm

variable (a : SesqForm 𝕜 V)

/-- A form $a$ is **bounded with constant $M$** if $|a(u, v)| \le M \|u\| \|v\|$ for all
$u, v \in V$. -/
def IsBoundedWith (M : ℝ) : Prop := ∀ u v, ‖a u v‖ ≤ M * ‖u‖ * ‖v‖

/-- A form $a$ is **coercive with constant $c$** if $c \|v\|^2 \le \operatorname{Re} a(v, v)$ for
all $v \in V$.

[han2009theoretical] call such a form $V$-elliptic with constant $c$, or strongly positive. No
sign condition on $c$ is part of the definition; the constant $c = 0$ expresses that $a$ is
positive. -/
def IsCoerciveWith (c : ℝ) : Prop := ∀ v, c * ‖v‖ ^ 2 ≤ RCLike.re (a v v)

/-- A form $a$ is **coercive** if it is coercive with some constant $c > 0$. -/
def IsCoercive : Prop := ∃ c : ℝ, 0 < c ∧ a.IsCoerciveWith c

/-- A form $a$ is **Hermitian** if $a(u, v) = \overline{a(v, u)}$ for all $u, v \in V$. -/
def IsHermitian : Prop := ∀ u v, a u v = starRingEnd 𝕜 (a v u)

/-- Every bounded sesquilinear form $a$ is bounded with its operator norm as constant:
$|a(u, v)| \le \|a\| \|u\| \|v\|$ for all $u, v \in V$. -/
theorem isBoundedWith_opNorm : a.IsBoundedWith ‖a‖ := fun u v => a.le_opNorm₂ u v

/-- Let $a$ be bounded with a constant $M \ge 0$. Then $\|a\| \le M$.

Together with `SesqForm.isBoundedWith_opNorm`, this identifies the operator norm $\|a\|$ with
the least constant in the definition of boundedness. -/
theorem opNorm_le_of_isBoundedWith {M : ℝ} (hM : 0 ≤ M) (h : a.IsBoundedWith M) : ‖a‖ ≤ M :=
  a.opNorm_le_bound₂ hM h

/-- If $a$ is coercive with constant $c$ and $c' \le c$, then $a$ is coercive with constant $c'$. -/
theorem IsCoerciveWith.mono {c c' : ℝ} (h : a.IsCoerciveWith c) (hc : c' ≤ c) :
    a.IsCoerciveWith c' := fun v =>
  (mul_le_mul_of_nonneg_right hc (sq_nonneg _)).trans (h v)

/-- If $a$ is coercive with constant $c$, then $c \|u\| \le \|a(u, \cdot)\|$ for every $u \in V$,
where $\|a(u, \cdot)\|$ is the norm of the functional $v \mapsto a(u, v)$. -/
theorem IsCoerciveWith.norm_le_norm_apply {c : ℝ} (h : a.IsCoerciveWith c) (u : V) :
    c * ‖u‖ ≤ ‖a u‖ := by
  rcases eq_or_lt_of_le (norm_nonneg u) with hu | hu
  · simp [← hu]
  · refine le_of_mul_le_mul_right ?_ hu
    calc c * ‖u‖ * ‖u‖ = c * ‖u‖ ^ 2 := by ring
      _ ≤ RCLike.re (a u u) := h u
      _ ≤ ‖a u u‖ := RCLike.re_le_norm _
      _ ≤ ‖a u‖ * ‖u‖ := (a u).le_opNorm u

/-- Over $\mathbb{R}$, a form $a$ is coercive with constant $c$ if and only if
$c \|v\|^2 \le a(v, v)$ for all $v \in V$. -/
theorem isCoerciveWith_real_iff {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (a : SesqForm ℝ V) (c : ℝ) : a.IsCoerciveWith c ↔ ∀ v, c * ‖v‖ ^ 2 ≤ a v v := Iff.rfl

/-- Over $\mathbb{R}$, a form $a$ is Hermitian if and only if it is symmetric: $a(u, v) = a(v, u)$
for all $u, v \in V$. -/
theorem isHermitian_real_iff {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (a : SesqForm ℝ V) : a.IsHermitian ↔ ∀ u v, a u v = a v u := Iff.rfl

/-- The inner product, as a form, is coercive with constant $1$: $\|v\|^2 \le \operatorname{Re}
\langle v, v \rangle$.

It is the model coercive form, and the projection theorem is the case of the inner product. -/
theorem innerSL_isCoerciveWith : SesqForm.IsCoerciveWith (innerSL 𝕜 : SesqForm 𝕜 V) 1 := fun v => by
  simp

/-- The inner product, as a form, is Hermitian: $\langle u, v \rangle = \overline{\langle v, u
\rangle}$. -/
theorem innerSL_isHermitian : SesqForm.IsHermitian (innerSL 𝕜 : SesqForm 𝕜 V) := fun u v =>
  (inner_conj_symm (𝕜 := 𝕜) u v).symm

/-- The **form of an operator**: for a bounded operator $A$ on $V$, the form
$(u, v) \mapsto \langle Au, v \rangle$. -/
noncomputable def ofOperator (A : V →L[𝕜] V) : SesqForm 𝕜 V := (innerSL 𝕜).comp A

/-- The form of an operator $A$ takes the value $\langle Au, v \rangle$ at $(u, v)$. -/
theorem ofOperator_apply (A : V →L[𝕜] V) (u v : V) : ofOperator A u v = inner 𝕜 (A u) v := rfl

section Operator

variable [CompleteSpace V]

/-- The **operator of a form**: on a Hilbert space $V$, the bounded operator $A$ with
$\langle Au, v \rangle = a(u, v)$ for all $u, v \in V$.

The vector $Au$ is the Riesz representative of the functional $a(u, \cdot)$, as in (8.3.1) and
(9.4.5) of [han2009theoretical]. The definition is Mathlib's
`InnerProductSpace.continuousLinearMapOfBilin`. -/
noncomputable abbrev toOperator : V →L[𝕜] V := InnerProductSpace.continuousLinearMapOfBilin a

/-- On a Hilbert space $V$, the operator $A$ of a form $a$ satisfies
$\langle Au, v \rangle = a(u, v)$ for all $u, v \in V$.

Every fact about a form is transported to its operator, and back, through this identity. -/
theorem inner_toOperator (u v : V) : inner 𝕜 (toOperator a u) v = a u v :=
  InnerProductSpace.continuousLinearMapOfBilin_apply a u v

/-- The **Riesz representative** of a bounded functional $\ell$ on a Hilbert space $V$: the vector
$f \in V$ with $\langle f, v \rangle = \ell(v)$ for all $v \in V$. -/
noncomputable def rieszRep (ℓ : V →L[𝕜] 𝕜) : V := (InnerProductSpace.toDual 𝕜 V).symm ℓ

/-- On a Hilbert space $V$, the Riesz representative $f$ of a bounded functional $\ell$ satisfies
$\langle f, v \rangle = \ell(v)$ for every $v \in V$. -/
theorem inner_rieszRep (ℓ : V →L[𝕜] 𝕜) (v : V) : inner 𝕜 (rieszRep ℓ) v = ℓ v :=
  InnerProductSpace.toDual_symm_apply

/-- On a Hilbert space, the Riesz representative of a bounded functional $\ell$ has the norm
$\|\ell\|$. -/
theorem norm_rieszRep (ℓ : V →L[𝕜] 𝕜) : ‖rieszRep ℓ‖ = ‖ℓ‖ :=
  (InnerProductSpace.toDual 𝕜 V).symm.norm_map ℓ

/-- On a Hilbert space, $Au$ is the Riesz representative of the functional $a(u, \cdot)$, where $A$
is the operator of the form $a$. -/
theorem toOperator_apply_eq_rieszRep (u : V) : toOperator a u = rieszRep (a u) := rfl

/-- On a Hilbert space, the operator of the form $(u, v) \mapsto \langle Au, v \rangle$ is $A$.

Together with `SesqForm.ofOperator_toOperator`, this shows that `SesqForm.ofOperator` and
`SesqForm.toOperator` are inverse to each other: on a Hilbert space, the bounded sesquilinear
forms are exactly the forms $\langle Au, v \rangle$ of bounded operators $A$, and $A$ is unique. -/
theorem toOperator_ofOperator (A : V →L[𝕜] V) : toOperator (ofOperator A) = A := by
  ext u
  exact ext_inner_right 𝕜 fun v => (inner_toOperator _ u v).trans (ofOperator_apply A u v)

/-- On a Hilbert space, a form $a$ is the form $(u, v) \mapsto \langle Au, v \rangle$ of its
operator $A$.

This is the other half of the bijection of `SesqForm.toOperator_ofOperator`. -/
theorem ofOperator_toOperator : ofOperator (toOperator a) = a := by
  ext u v
  exact inner_toOperator a u v

/-- On a Hilbert space, a form $a$ is coercive with constant $c$ if and only if its operator $A$ is
coercive with constant $c$, that is, $c \|v\|^2 \le \operatorname{Re} \langle Av, v \rangle$ for
all $v$.

The two quadratic forms $\operatorname{Re} a(v, v)$ and
$\operatorname{Re} \langle Av, v \rangle$ are the same function of $v$. -/
theorem isCoerciveWith_iff_toOperator (c : ℝ) :
    a.IsCoerciveWith c ↔ (toOperator a : V →ₗ[𝕜] V).IsCoerciveWith c := by
  simp only [IsCoerciveWith, LinearMap.IsCoerciveWith, ContinuousLinearMap.coe_coe,
    inner_toOperator]

/-- On a Hilbert space, a form $a$ is Hermitian if and only if its operator $A$ is symmetric:
$\langle Au, v \rangle = \langle u, Av \rangle$ for all $u, v$.

Since $A$ is bounded and defined on all of $V$, symmetry of $A$ is self-adjointness. -/
theorem isHermitian_iff_toOperator_isSymmetric :
    a.IsHermitian ↔ (toOperator a : V →ₗ[𝕜] V).IsSymmetric := by
  simp only [IsHermitian, LinearMap.IsSymmetric, ContinuousLinearMap.coe_coe]
  refine forall_congr' fun u => forall_congr' fun v => ?_
  rw [← inner_conj_symm (𝕜 := 𝕜) u (toOperator a v), inner_toOperator, inner_toOperator]

/-- On a Hilbert space, the operator $A$ of a form $a$ has the norm $\|A\| = \|a\|$.

The reason is that $Au$ is the Riesz representative of the functional $a(u, \cdot)$, and Riesz
representation preserves norms. So a bound $M$ for the form is a bound for $A$, and conversely. -/
theorem norm_toOperator : ‖toOperator a‖ = ‖a‖ :=
  ContinuousLinearMap.opNorm_ext _ _ fun u => by
    rw [toOperator_apply_eq_rieszRep, norm_rieszRep]

/-- On a Hilbert space, let $A$ be the operator of a form $a$, let $\ell$ be a bounded functional
with Riesz representative $f$, and let $u \in V$. Then $a(u, v) = \ell(v)$ for all $v \in V$ if
and only if $Au = f$. -/
theorem forall_apply_eq_iff_toOperator_eq (ℓ : V →L[𝕜] 𝕜) (u : V) :
    (∀ v, a u v = ℓ v) ↔ toOperator a u = rieszRep ℓ := by
  constructor
  · intro h
    exact ext_inner_right 𝕜 fun v => by rw [inner_toOperator, inner_rieszRep, h]
  · intro h v
    rw [← inner_toOperator, h, inner_rieszRep]

end Operator

section Energy

/-- The **energy functional** of a form $a$ and a bounded functional $\ell$:
$$E(v) = \tfrac12 \operatorname{Re} a(v, v) - \operatorname{Re} \ell(v).$$

When $a$ is Hermitian and coercive, the minimizers of $E$ are exactly the solutions $u$ of
$a(u, v) = \ell(v)$ for all $v$ (Theorem 8.3.3 and (9.1.7) of [han2009theoretical]); see
`SesqForm.isMinOn_energy_iff`. -/
noncomputable def energy (ℓ : V →L[𝕜] 𝕜) (v : V) : ℝ :=
  (1 / 2 : ℝ) * RCLike.re (a v v) - RCLike.re (ℓ v)

/-- The **energy norm** of a form $a$: $\|v\|_a = \sqrt{\operatorname{Re} a(v, v)}$.

It is a norm when $a$ is Hermitian and coercive. The definition applies to every form, and gives
$0$ where $\operatorname{Re} a(v, v) < 0$, because `Real.sqrt` is $0$ on negative numbers. -/
noncomputable def energyNorm (v : V) : ℝ := Real.sqrt (RCLike.re (a v v))

/-- On a Hilbert space, the energy norm of a form $a$ is the energy norm
$\sqrt{\operatorname{Re} \langle Av, v \rangle}$ of its operator $A$.

So every result on energy norms of operators, such as the Cauchy–Schwarz inequality, the energy
inner product and its orthogonal projections, applies to forms. The energy norm of an operator
is `energyNorm` in the root namespace. -/
theorem energyNorm_eq_energyNorm_toOperator [CompleteSpace V] (v : V) :
    a.energyNorm v = _root_.energyNorm (toOperator a : V →ₗ[𝕜] V) v := by
  simp only [energyNorm, _root_.energyNorm, ContinuousLinearMap.coe_coe, inner_toOperator]

/-- Let $a$ be coercive with a constant $c \ge 0$. Then $\sqrt{c} \|v\| \le \|v\|_a$ for every
$v \in V$.

This is the lower half of the equivalence $\sqrt{c} \|v\| \le \|v\|_a \le \sqrt{M} \|v\|$ of the
energy norm and the norm of $V$ for a bounded coercive form (Theorem 8.3.3 and §9.4 of
[han2009theoretical]). The upper half is `SesqForm.energyNorm_le_sqrt_mul_norm`. -/
theorem sqrt_mul_norm_le_energyNorm {c : ℝ} (hc : 0 ≤ c) (h : a.IsCoerciveWith c) (v : V) :
    Real.sqrt c * ‖v‖ ≤ a.energyNorm v := by
  have hcv : Real.sqrt c * ‖v‖ = Real.sqrt (c * ‖v‖ ^ 2) := by
    rw [Real.sqrt_mul hc, Real.sqrt_sq (norm_nonneg v)]
  rw [energyNorm, hcv]
  exact Real.sqrt_le_sqrt (h v)

/-- Let $a$ be bounded with constant $M$. Then $\|v\|_a \le \sqrt{M} \|v\|$ for every $v \in V$.

This is the upper half of the equivalence $\sqrt{c} \|v\| \le \|v\|_a \le \sqrt{M} \|v\|$. The
lower half is `SesqForm.sqrt_mul_norm_le_energyNorm`. -/
theorem energyNorm_le_sqrt_mul_norm {M : ℝ} (h : a.IsBoundedWith M) (v : V) :
    a.energyNorm v ≤ Real.sqrt M * ‖v‖ := by
  have hMv : RCLike.re (a v v) ≤ M * ‖v‖ ^ 2 := by
    calc RCLike.re (a v v) ≤ ‖a v v‖ := RCLike.re_le_norm _
      _ ≤ M * ‖v‖ * ‖v‖ := h v v
      _ = M * ‖v‖ ^ 2 := by ring
  calc a.energyNorm v ≤ Real.sqrt (M * ‖v‖ ^ 2) := Real.sqrt_le_sqrt hMv
    _ = Real.sqrt M * ‖v‖ := by
        rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg v)]

end Energy

end SesqForm

/-! ### Restriction of a form to a subspace -/

section Restrict

/-- The **restriction** of a bounded sesquilinear form $a$ on $V$ to a subspace $K$: the bounded
form $(u, v) \mapsto a(u, v)$ on $K$. -/
noncomputable def SesqForm.restrict (a : SesqForm 𝕜 V) (K : Submodule 𝕜 V) : SesqForm 𝕜 K :=
  ((a.comp K.subtypeL).flip.comp K.subtypeL).flip

/-- The restriction of $a$ to $K$ takes the value $a(u, v)$ at $u, v \in K$. -/
@[simp]
theorem SesqForm.restrict_apply (a : SesqForm 𝕜 V) (K : Submodule 𝕜 V) (u v : K) :
    a.restrict K u v = a u v := rfl

/-- The restriction of a Hermitian form to a subspace is Hermitian. -/
theorem SesqForm.IsHermitian.restrict {a : SesqForm 𝕜 V} (h : a.IsHermitian) (K : Submodule 𝕜 V) :
    (a.restrict K).IsHermitian := fun u v ↦ by
  rw [SesqForm.restrict_apply, SesqForm.restrict_apply]
  exact h u v

/-- If a form is coercive with constant $c$, then its restriction to a subspace is coercive with
constant $c$. -/
theorem SesqForm.IsCoerciveWith.restrict {a : SesqForm 𝕜 V} {c : ℝ} (h : a.IsCoerciveWith c)
    (K : Submodule 𝕜 V) : (a.restrict K).IsCoerciveWith c := fun v ↦ by
  rw [SesqForm.restrict_apply, ← Submodule.norm_coe]
  exact h v

/-- The restriction of a coercive form to a subspace is coercive. -/
theorem SesqForm.IsCoercive.restrict {a : SesqForm 𝕜 V} (h : a.IsCoercive) (K : Submodule 𝕜 V) :
    (a.restrict K).IsCoercive :=
  let ⟨c, hc, h⟩ := h
  ⟨c, hc, h.restrict K⟩

/-- On a Hilbert space, the operator of a Hermitian coercive form is symmetric and coercive.

The two halves are `SesqForm.isHermitian_iff_toOperator_isSymmetric` and
`SesqForm.isCoerciveWith_iff_toOperator`. -/
theorem SesqForm.IsHermitian.isSymmetricCoercive_toOperator [CompleteSpace V] {a : SesqForm 𝕜 V}
    (hsymm : a.IsHermitian) (ha : a.IsCoercive) :
    (SesqForm.toOperator a : V →ₗ[𝕜] V).IsSymmetricCoercive :=
  ⟨(SesqForm.isHermitian_iff_toOperator_isSymmetric a).1 hsymm,
    let ⟨c, hc, h⟩ := ha
    ⟨c, hc, (SesqForm.isCoerciveWith_iff_toOperator a c).1 h⟩⟩

end Restrict

/-- The type of **bounded sesquilinear forms on two spaces**: for inner product spaces $U$ and $V$
over $\mathbb{K}$, continuous maps $a \colon U \times V \to \mathbb{K}$, conjugate-linear in the
first argument and linear in the second.

These forms are the setting of the Petrov–Galerkin method and of the Babuška–Nečas theorem. -/
abbrev SesqForm₂ (𝕜 U V : Type*) [RCLike 𝕜] [NormedAddCommGroup U] [InnerProductSpace 𝕜 U]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] :=
  U →L⋆[𝕜] V →L[𝕜] 𝕜

namespace SesqForm₂

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace 𝕜 U] (a : SesqForm₂ 𝕜 U V)

/-- A form $a$ on $U \times V$ is **bounded with constant $M$** if $|a(u, v)| \le M \|u\| \|v\|$ for
all $u \in U$ and $v \in V$. -/
def IsBoundedWith (M : ℝ) : Prop := ∀ u v, ‖a u v‖ ≤ M * ‖u‖ * ‖v‖

/-- A form on $V$ is bounded with constant $M$ if and only if it is bounded with constant $M$ as a
form on $V \times V$. -/
theorem _root_.SesqForm.isBoundedWith_iff_sesqForm₂ {a : SesqForm 𝕜 V} {M : ℝ} :
    a.IsBoundedWith M ↔ SesqForm₂.IsBoundedWith (a : SesqForm₂ 𝕜 V V) M :=
  Iff.rfl

/-- A form $a$ on $U \times V$ satisfies the **inf–sup condition** (Babuška–Brezzi condition) with
constant $\alpha$ if
$$\alpha \|u\| \le \|a(u, \cdot)\| = \sup_{v \neq 0} \frac{|a(u, v)|}{\|v\|} \quad \text{for all
  } u \in U.$$

This is (8.7.2) and (9.2.3) of [han2009theoretical]. The condition is stated with the norm of
the functional $a(u, \cdot)$; `SesqForm₂.iSup_norm_div_eq_norm` shows that this norm is the
supremum. For a form on one space, the condition is weaker than coercivity. Together with
`SesqForm₂.IsNondegenerate`, it makes the problem $a(u, v) = \ell(v)$ for all $v \in V$ uniquely
solvable; see `SesqForm₂.babuska_necas`. -/
def InfSupWith (α : ℝ) : Prop := ∀ u, α * ‖u‖ ≤ ‖a u‖

/-- A form $a$ on $U \times V$ is **nondegenerate** if for every $v \in V$ with $v \neq 0$ there is
a $u \in U$ with $a(u, v) \neq 0$.

This is (8.7.3) of [han2009theoretical]. Equivalently, no nonzero $v$ is orthogonal to the range
of the operator of $a$. -/
def IsNondegenerate : Prop := ∀ v, v ≠ 0 → ∃ u, a u v ≠ 0

/-- For a form $a$ on $U \times V$ and $u \in U$,
$$\sup_{v \neq 0} \frac{|a(u, v)|}{\|v\|} = \|a(u, \cdot)\|.$$

So the supremum in the usual statement of the inf–sup condition is the operator norm of the
functional $a(u, \cdot)$, and `SesqForm₂.InfSupWith` can be stated with this norm. The proof is
`ContinuousLinearMap.iSup_norm_apply_div_eq_opNorm`. If $V = 0$, both sides are $0$. -/
theorem iSup_norm_div_eq_norm (u : U) :
    (⨆ v : {v : V // v ≠ 0}, ‖a u v‖ / ‖(v : V)‖) = ‖a u‖ :=
  (a u).iSup_norm_apply_div_eq_opNorm

/-- If a form $a$ on $V$ is coercive with constant $c$, then $a$, as a form on $V \times V$,
satisfies the inf–sup condition with constant $c$.

So the theory of forms on two spaces contains the Lax–Milgram theorem as a special case
([han2009theoretical], Exercise 8.7.1). -/
theorem _root_.SesqForm.IsCoerciveWith.infSupWith {a : SesqForm 𝕜 V} {c : ℝ}
    (h : a.IsCoerciveWith c) : SesqForm₂.InfSupWith (a : SesqForm₂ 𝕜 V V) c :=
  fun u => SesqForm.IsCoerciveWith.norm_le_norm_apply a h u

end SesqForm₂

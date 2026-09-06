import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Nonlinear.FixedPoint
import Numlib.Variational.Forms
import Numlib.Variational.LaxMilgram

/-!
# Atkinson–Han §8.3: the Lax–Milgram lemma

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §8.3.

The data of §8.3 is a real bilinear form `a : V × V → ℝ` on a real normed (later Hilbert) space
`V`, together with `ℓ ∈ V'`.  Such a form is a `BilinForm V` (`V →ₗ[ℝ] V →ₗ[ℝ] ℝ`), and the
book's vocabulary -- bounded, positive, strictly positive, strongly positive (= `V`-elliptic),
symmetric -- is the list of predicates below.  §8.7 and the whole of Chapter 9 are stated in that
vocabulary, so the dictionary lives here in full, including the facts the book records only later
as (9.1.3), (9.1.7) and (9.4.2)-(9.4.7); §8.3's own second proof of Theorem 8.3.4 already needs
the operator `A` of (9.4.5).

`BilinForm.toCLM` bundles a bounded form as a `V →L[ℝ] V →L[ℝ] ℝ`, which *is* the backbone's
`SesqForm ℝ V`, so the `Numlib.Variational` API applies to it verbatim; `BilinForm.ofCLM` is the
inverse direction and `theorem_8_3_1` packages the two as the one-to-one correspondence of
Theorem 8.3.1 between `A ∈ L(V, V')` and the bounded bilinear forms on `V`.  On a Hilbert space
`BilinForm.toOperator` is the Riesz operator `A : V → V` of (9.4.5), with `(A u, v) = a(u,v)`,
and `BilinForm.energy` is the energy functional `E(v) = ½ a(v,v) − ℓ(v)` of Theorem 8.3.3.

## Main results

* `theorem_8_3_1` -- the one-to-one correspondence between `L(V, V')` and the bounded forms.
* `theorem_8_3_2` -- the minimizer of `E(v) = ½‖v‖² − ℓ(v)` on a nonempty closed convex set.
* `theorem_8_3_3` -- the same for the energy `E(v) = ½ a(v,v) − ℓ(v)` of a symmetric `V`-elliptic
  form, with the variational inequality (8.3.3) and the variational equation (8.3.4).
* `theorem_8_3_4` -- the Lax–Milgram lemma, with the stability estimate `‖u‖ ≤ ‖ℓ‖/α`.  Both
  proofs the book gives are available: the damped fixed-point iteration `P_θ` of the first
  (`contractingWith_damped_sub_smul`) and the closed-range argument of the second
  (`isClosed_range_toOperator`, `bijective_toOperator`).
* `exercise_8_3_1` -- Lax–Milgram rederived from the strongly monotone Lipschitz theory of §5.1.
-/

open Filter Topology
open scoped InnerProductSpace

namespace AtkinsonHan

/-! ### The bilinear forms of §8.3 and the operators they represent -/

/-- A real bilinear form `a : V × V → ℝ` (Atkinson–Han §8.3). -/
abbrev BilinForm (V : Type*) [AddCommGroup V] [Module ℝ V] := LinearMap.BilinForm ℝ V

namespace BilinForm

section Normed

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- `|a(u,v)| ≤ M ‖u‖ ‖v‖`: the boundedness of §8.3, with an explicit constant. -/
def IsBoundedWith (a : BilinForm V) (M : ℝ) : Prop := ∀ u v, |a u v| ≤ M * ‖u‖ * ‖v‖

/-- A bounded bilinear form: `|a(u,v)| ≤ M ‖u‖ ‖v‖` for some `M > 0` (§8.3). -/
def IsBounded (a : BilinForm V) : Prop := ∃ M > 0, a.IsBoundedWith M

/-- `a(v,v) ≥ 0`: the book's "positive" (§8.3).  Unlike Mathlib's `LinearMap.IsPositive`, this
does not include symmetry. -/
def IsPositive (a : BilinForm V) : Prop := ∀ v, 0 ≤ a v v

/-- `a(v,v) > 0` for `v ≠ 0`: the book's "strictly positive" (§8.3). -/
def IsStrictlyPositive (a : BilinForm V) : Prop := ∀ v, v ≠ 0 → 0 < a v v

/-- `a(v,v) ≥ α ‖v‖²`: the book's "strongly positive", or `V`-elliptic, with constant `α`
(§8.3; (9.1.3) with `α = c₀`). -/
def IsEllipticWith (a : BilinForm V) (α : ℝ) : Prop := ∀ v, α * ‖v‖ ^ 2 ≤ a v v

/-- A `V`-elliptic (strongly positive) form: `a(v,v) ≥ α ‖v‖²` for some `α > 0`. -/
def IsElliptic (a : BilinForm V) : Prop := ∃ α > 0, a.IsEllipticWith α

variable {a : BilinForm V} {M α : ℝ}

theorem IsBoundedWith.isBounded (hM : a.IsBoundedWith M) (hM0 : 0 < M) : a.IsBounded :=
  ⟨M, hM0, hM⟩

theorem IsEllipticWith.isElliptic (ha : a.IsEllipticWith α) (hα : 0 < α) : a.IsElliptic :=
  ⟨α, hα, ha⟩

theorem IsEllipticWith.isPositive (ha : a.IsEllipticWith α) (hα : 0 ≤ α) : a.IsPositive :=
  fun v => le_trans (by positivity) (ha v)

theorem IsEllipticWith.isStrictlyPositive (ha : a.IsEllipticWith α) (hα : 0 < α) :
    a.IsStrictlyPositive := fun v hv => lt_of_lt_of_le (by positivity) (ha v)

/-- The book's symmetry `a(u,v) = a(v,u)` is Mathlib's `LinearMap.BilinForm.IsSymm`. -/
theorem isSymm_iff : LinearMap.BilinForm.IsSymm a ↔ ∀ u v, a u v = a v u :=
  LinearMap.BilinForm.isSymm_def

/-! ### The correspondence `A ↔ a` of Theorem 8.3.1 -/

/-- A bounded bilinear form as an element of `L(V, V')`, that is as a bounded bilinear map
`V →L[ℝ] V →L[ℝ] ℝ` (Atkinson–Han Theorem 8.3.1).  Over `ℝ` this type *is* the backbone's
`SesqForm ℝ V`, so every lemma about bounded sesquilinear forms applies to `a.toCLM hM`. -/
noncomputable def toCLM (a : BilinForm V) (hM : a.IsBoundedWith M) : V →L[ℝ] V →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂ a M fun u v => by rw [Real.norm_eq_abs]; exact hM u v

/-- Bundling a bounded form as an element of `L(V, V')` does not change its values: `a.toCLM hM`
is the same function of `(u, v)` as `a`. -/
@[simp]
theorem toCLM_apply (hM : a.IsBoundedWith M) (u v : V) : a.toCLM hM u v = a u v := rfl

/-- `‖A‖ ≤ M` in Theorem 8.3.1. -/
theorem norm_toCLM_le (hM0 : 0 ≤ M) (hM : a.IsBoundedWith M) : ‖a.toCLM hM‖ ≤ M :=
  LinearMap.mkContinuous₂_norm_le _ hM0 _

/-- The bilinear form `a(u,v) = ⟨A u, v⟩` of an operator `A ∈ L(V, V')` (Atkinson–Han
Theorem 8.3.1). -/
noncomputable def ofCLM (A : V →L[ℝ] StrongDual ℝ V) : BilinForm V :=
  (ContinuousLinearMap.coeLM ℝ).comp (A : V →ₗ[ℝ] StrongDual ℝ V)

/-- The form attached to an operator is `a(u,v) = ⟨A u, v⟩`, the defining relation of
Theorem 8.3.1. -/
@[simp]
theorem ofCLM_apply (A : V →L[ℝ] StrongDual ℝ V) (u v : V) : ofCLM A u v = A u v := rfl

/-- `|a(u,v)| ≤ ‖A‖ ‖u‖ ‖v‖` in Theorem 8.3.1. -/
theorem isBoundedWith_opNorm (A : V →L[ℝ] StrongDual ℝ V) : (ofCLM A).IsBoundedWith ‖A‖ :=
  fun u v => by rw [ofCLM_apply, ← Real.norm_eq_abs]; exact A.le_opNorm₂ u v

theorem isBounded_ofCLM (A : V →L[ℝ] StrongDual ℝ V) : (ofCLM A).IsBounded :=
  ⟨‖A‖ + 1, by positivity, fun u v =>
    (isBoundedWith_opNorm A u v).trans
      (by nlinarith [mul_nonneg (norm_nonneg u) (norm_nonneg v)])⟩

/-- A bounded form is recovered from the operator it induces.  With `toCLM_ofCLM` this is the
one-to-one correspondence of Theorem 8.3.1; note that the recovered form does not depend on which
bound `M` was used to bundle it. -/
theorem ofCLM_toCLM (hM : a.IsBoundedWith M) : ofCLM (a.toCLM hM) = a := by
  ext u v
  rfl

theorem toCLM_ofCLM (A : V →L[ℝ] StrongDual ℝ V) {M : ℝ} (hM : (ofCLM A).IsBoundedWith M) :
    (ofCLM A).toCLM hM = A := by
  ext u v
  rfl

/-- Atkinson–Han Theorem 8.3.1: on a real normed space the operators `A ∈ L(V, V')` correspond
one-to-one with the bounded bilinear forms on `V`, via `⟨A u, v⟩ = a(u,v)`.  The quantitative half
of the theorem is `isBoundedWith_opNorm` (`|a(u,v)| ≤ ‖A‖ ‖u‖ ‖v‖`) together with `norm_toCLM_le`
(`‖A‖ ≤ M`). -/
noncomputable def theorem_8_3_1 : (V →L[ℝ] StrongDual ℝ V) ≃ {a : BilinForm V // a.IsBounded} where
  toFun A := ⟨ofCLM A, isBounded_ofCLM A⟩
  invFun a := a.1.toCLM a.2.choose_spec.2
  left_inv A := toCLM_ofCLM A _
  right_inv _ := Subtype.ext (ofCLM_toCLM _)

/-! ### The dictionary following Theorem 8.3.1

Each property of the form `a = ofCLM A` is the corresponding property of `A`, read through
`⟨A v, v⟩ = a(v,v)`; all but the first are definitional. -/

theorem isBoundedWith_ofCLM_iff (A : V →L[ℝ] StrongDual ℝ V) :
    (ofCLM A).IsBoundedWith M ↔ ∀ v, ‖A v‖ ≤ M * ‖v‖ := by
  constructor
  · intro h v
    have hMv : 0 ≤ M * ‖v‖ := by
      rcases eq_or_lt_of_le (norm_nonneg v) with hv | hv
      · simp [← hv]
      · refine le_of_mul_le_mul_right ?_ hv
        simpa using le_trans (abs_nonneg _) (h v v)
    refine (A v).opNorm_le_bound hMv fun w => ?_
    calc ‖A v w‖ = |A v w| := Real.norm_eq_abs _
      _ ≤ M * ‖v‖ * ‖w‖ := h v w
  · intro h u v
    rw [ofCLM_apply, ← Real.norm_eq_abs]
    calc ‖A u v‖ ≤ ‖A u‖ * ‖v‖ := (A u).le_opNorm v
      _ ≤ M * ‖u‖ * ‖v‖ := by gcongr; exact h u

theorem isPositive_ofCLM_iff (A : V →L[ℝ] StrongDual ℝ V) :
    (ofCLM A).IsPositive ↔ ∀ v, 0 ≤ A v v := Iff.rfl

theorem isStrictlyPositive_ofCLM_iff (A : V →L[ℝ] StrongDual ℝ V) :
    (ofCLM A).IsStrictlyPositive ↔ ∀ v, v ≠ 0 → 0 < A v v := Iff.rfl

theorem isEllipticWith_ofCLM_iff (A : V →L[ℝ] StrongDual ℝ V) :
    (ofCLM A).IsEllipticWith α ↔ ∀ v, α * ‖v‖ ^ 2 ≤ A v v := Iff.rfl

theorem isSymm_ofCLM_iff (A : V →L[ℝ] StrongDual ℝ V) :
    LinearMap.BilinForm.IsSymm (ofCLM A) ↔ ∀ u v, A u v = A v u := isSymm_iff

/-! ### The energy functional and the energy norm (Theorem 8.3.3, (9.1.7)) -/

/-- The energy functional `E(v) = ½ a(v,v) − ℓ(v)` (Atkinson–Han (8.3.2), (9.1.7)). -/
noncomputable def energy (a : BilinForm V) (ℓ : StrongDual ℝ V) (v : V) : ℝ :=
  (1 / 2 : ℝ) * a v v - ℓ v

/-- The energy norm `‖v‖_a = √(a(v,v))` of a symmetric `V`-elliptic form (§8.3, §9.4). -/
noncomputable def energyNorm (a : BilinForm V) (v : V) : ℝ := Real.sqrt (a v v)

theorem energyNorm_nonneg (a : BilinForm V) (v : V) : 0 ≤ a.energyNorm v := Real.sqrt_nonneg _

end Normed

section Inner

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {a : BilinForm V} {M α : ℝ}

/-! ### Bridges to the backbone predicates

`a.toCLM hM` is literally a `SesqForm ℝ V`; these lemmas record that the book's predicates are
the backbone's, with the `RCLike.re`/`starRingEnd` decorations of the general theory erased over
`ℝ` (`SesqForm.isCoerciveWith_real_iff`, `SesqForm.isHermitian_real_iff`). -/

theorem isBoundedWith_iff_toCLM {M' : ℝ} (hM : a.IsBoundedWith M) :
    a.IsBoundedWith M' ↔ SesqForm.IsBoundedWith (𝕜 := ℝ) (a.toCLM hM) M' := Iff.rfl

theorem isBoundedWith_toCLM (hM : a.IsBoundedWith M) :
    SesqForm.IsBoundedWith (𝕜 := ℝ) (a.toCLM hM) M :=
  (isBoundedWith_iff_toCLM hM).mp hM

/-- `V`-ellipticity is the backbone's coercivity, with the same constant. -/
theorem isEllipticWith_iff_isCoerciveWith (hM : a.IsBoundedWith M) :
    a.IsEllipticWith α ↔ SesqForm.IsCoerciveWith (𝕜 := ℝ) (a.toCLM hM) α := Iff.rfl

theorem isElliptic_iff_isCoercive (hM : a.IsBoundedWith M) :
    a.IsElliptic ↔ IsCoercive (a.toCLM hM) := by
  constructor
  · rintro ⟨α', hα', ha⟩
    exact ⟨α', hα', fun u => by simpa [sq, mul_assoc] using ha u⟩
  · rintro ⟨C, hC, h⟩
    exact ⟨C, hC, fun v => by simpa [sq, mul_assoc] using h v⟩

/-- Symmetry is the backbone's Hermitian symmetry, since `conj = id` over `ℝ`. -/
theorem isSymm_iff_isHermitian (hM : a.IsBoundedWith M) :
    LinearMap.BilinForm.IsSymm a ↔ SesqForm.IsHermitian (𝕜 := ℝ) (a.toCLM hM) := isSymm_iff

theorem energy_eq (hM : a.IsBoundedWith M) (ℓ : StrongDual ℝ V) (v : V) :
    a.energy ℓ v = SesqForm.energy (a.toCLM hM) ℓ v := rfl

theorem energyNorm_eq (hM : a.IsBoundedWith M) (v : V) :
    a.energyNorm v = SesqForm.energyNorm (a.toCLM hM) v := rfl

/-- Lower half of the norm equivalence `c₁ ‖v‖ ≤ ‖v‖_a ≤ c₂ ‖v‖` of Theorem 8.3.3, with
`c₁ = √α`. -/
theorem sqrt_mul_norm_le_energyNorm (hM : a.IsBoundedWith M) (hα : 0 ≤ α)
    (ha : a.IsEllipticWith α) (v : V) : Real.sqrt α * ‖v‖ ≤ a.energyNorm v := by
  rw [energyNorm_eq hM]
  exact SesqForm.sqrt_mul_norm_le_energyNorm (a.toCLM hM) hα ha v

/-- Upper half of the norm equivalence of Theorem 8.3.3, with `c₂ = √M`. -/
theorem energyNorm_le_sqrt_mul_norm (hM : a.IsBoundedWith M) (v : V) :
    a.energyNorm v ≤ Real.sqrt M * ‖v‖ := by
  rw [energyNorm_eq hM]
  exact SesqForm.energyNorm_le_sqrt_mul_norm (a.toCLM hM) (isBoundedWith_toCLM hM) v

end Inner

section Hilbert

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable {a : BilinForm V} {M α : ℝ}

/-- The operator `A : V → V` of (9.4.5), characterized by `(A u, v) = a(u,v)`: on a Hilbert space
it is the Riesz representation of the operator `A ∈ L(V, V')` of Theorem 8.3.1. -/
noncomputable abbrev toOperator (a : BilinForm V) (hM : a.IsBoundedWith M) : V →L[ℝ] V :=
  SesqForm.toOperator (a.toCLM hM)

/-- (9.4.5): `(A u, v) = a(u,v)`. -/
theorem inner_toOperator (hM : a.IsBoundedWith M) (u v : V) :
    ⟪toOperator a hM u, v⟫_ℝ = a u v :=
  SesqForm.inner_toOperator _ u v

/-- (9.4.3): `‖A‖ ≤ M`. -/
theorem norm_toOperator_le (hM0 : 0 ≤ M) (hM : a.IsBoundedWith M) : ‖toOperator a hM‖ ≤ M := by
  rw [SesqForm.norm_toOperator]
  exact norm_toCLM_le hM0 hM

/-- (9.4.2): a symmetric form has a self-adjoint operator. -/
theorem isSelfAdjoint_toOperator (hM : a.IsBoundedWith M) (hs : LinearMap.BilinForm.IsSymm a) :
    IsSelfAdjoint (toOperator a hM) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    ((SesqForm.isHermitian_iff_toOperator_isSymmetric _).mp ((isSymm_iff_isHermitian hM).mp hs))

/-- (9.4.3): a `V`-elliptic form has a coercive operator, `(A v, v) ≥ α ‖v‖²`. -/
theorem isCoerciveWith_toOperator (hM : a.IsBoundedWith M) (ha : a.IsEllipticWith α) :
    (toOperator a hM : V →ₗ[ℝ] V).IsCoerciveWith α :=
  (SesqForm.isCoerciveWith_iff_toOperator _ α).mp ha

/-- The symmetric `V`-elliptic case: `A` is symmetric and coercive, so the energy inner product
`(u,v)_a = a(u,v)` of §9.4 really is an inner product. -/
theorem isSymmetricCoercive_toOperator (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) (hs : LinearMap.BilinForm.IsSymm a) :
    (toOperator a hM : V →ₗ[ℝ] V).IsSymmetricCoercive where
  isSymmetric :=
    (SesqForm.isHermitian_iff_toOperator_isSymmetric _).mp ((isSymm_iff_isHermitian hM).mp hs)
  isCoercive := ⟨α, hα, isCoerciveWith_toOperator hM ha⟩

/-- The energy norm of the form is the energy norm of its operator. -/
theorem energyNorm_eq_energyNorm_toOperator (hM : a.IsBoundedWith M) (v : V) :
    a.energyNorm v = _root_.energyNorm (toOperator a hM : V →ₗ[ℝ] V) v := by
  rw [energyNorm_eq hM]
  exact SesqForm.energyNorm_eq_energyNorm_toOperator _ v

/-- (9.4.6): `f ∈ V` with `(f, v) = ℓ(v)` is the Riesz representative of `ℓ`. -/
theorem inner_rieszRep (ℓ : StrongDual ℝ V) (v : V) : ⟪SesqForm.rieszRep ℓ, v⟫_ℝ = ℓ v :=
  SesqForm.inner_rieszRep ℓ v

/-- `‖f‖ = ‖ℓ‖` (§9.4). -/
theorem norm_rieszRep (ℓ : StrongDual ℝ V) : ‖SesqForm.rieszRep (𝕜 := ℝ) (V := V) ℓ‖ = ‖ℓ‖ :=
  SesqForm.norm_rieszRep ℓ

/-- (9.4.7) ⇔ (9.4.4): `A u = f` iff `a(u,v) = ℓ(v)` for all `v`. -/
theorem toOperator_eq_rieszRep_iff (hM : a.IsBoundedWith M) (ℓ : StrongDual ℝ V) (u : V) :
    toOperator a hM u = SesqForm.rieszRep ℓ ↔ ∀ v, a u v = ℓ v :=
  (SesqForm.forall_apply_eq_iff_toOperator_eq _ ℓ u).symm

end Hilbert

end BilinForm

namespace Chapter08

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `u ∈ K` minimizes `f` on `K` iff `f u` is the infimum of `f` over `K`: the passage between
the book's `E(u) = inf_K E` and Mathlib's `IsMinOn`. -/
theorem isMinOn_iff_eq_ciInf {X : Type*} {K : Set X} {f : X → ℝ} {u : X} (hu : u ∈ K)
    (hbdd : BddBelow (Set.range fun v : K => f v)) :
    IsMinOn f K u ↔ f u = ⨅ v : K, f v := by
  have : Nonempty K := ⟨⟨u, hu⟩⟩
  rw [isMinOn_iff]
  constructor
  · intro h
    exact le_antisymm (le_ciInf fun v => h (v : X) v.2) (ciInf_le hbdd ⟨u, hu⟩)
  · intro h v hv
    rw [h]
    exact ciInf_le hbdd ⟨v, hv⟩

/-! ### Theorem 8.3.2: the energy `E(v) = ½‖v‖² − ℓ(v)` -/

theorem energy_innerSL (ℓ : StrongDual ℝ V) (v : V) :
    SesqForm.energy (innerSL ℝ : SesqForm ℝ V) ℓ v = (1 / 2 : ℝ) * ‖v‖ ^ 2 - ℓ v := by
  simp [SesqForm.energy]

private theorem energy_innerSL_eq (ℓ : StrongDual ℝ V) :
    (fun v => (1 / 2 : ℝ) * ‖v‖ ^ 2 - ℓ v) = SesqForm.energy (innerSL ℝ : SesqForm ℝ V) ℓ := by
  funext v
  rw [energy_innerSL]

private theorem innerSL_hermitian : SesqForm.IsHermitian (innerSL ℝ : SesqForm ℝ V) :=
  SesqForm.innerSL_isHermitian

private theorem innerSL_coercive : SesqForm.IsCoerciveWith (innerSL ℝ : SesqForm ℝ V) 1 :=
  SesqForm.innerSL_isCoerciveWith

/-- Theorem 8.3.2: on a nonempty closed convex subset `K` of a Hilbert space the functional
`E(v) = ½‖v‖² − ℓ(v)` has a unique minimizer, and `u ∈ K` is that minimizer exactly when it
satisfies the variational inequality `(u, v − u) ≥ ℓ(v − u)` for all `v ∈ K`. -/
theorem theorem_8_3_2 [CompleteSpace V] {K : Set V} (hne : K.Nonempty) (hcl : IsClosed K)
    (hconv : Convex ℝ K) (ℓ : StrongDual ℝ V) :
    (∃! u, u ∈ K ∧ IsMinOn (fun v => (1 / 2 : ℝ) * ‖v‖ ^ 2 - ℓ v) K u) ∧
      ∀ u ∈ K, (IsMinOn (fun v => (1 / 2 : ℝ) * ‖v‖ ^ 2 - ℓ v) K u ↔
        ∀ v ∈ K, ℓ (v - u) ≤ ⟪u, v - u⟫_ℝ) := by
  rw [energy_innerSL_eq]
  refine ⟨SesqForm.existsUnique_isMinOn_energy (innerSL_hermitian (V := V)) ℓ
      one_pos innerSL_coercive hconv hcl hne, fun u hu => ?_⟩
  exact SesqForm.isMinOn_energy_iff_forall_le (innerSL_hermitian (V := V)) ℓ
    one_pos innerSL_coercive hconv hu

/-- Theorem 8.3.2, subspace case: `u ∈ K` minimizes `E(v) = ½‖v‖² − ℓ(v)` over the subspace `K`
iff `(u, v) = ℓ(v)` for all `v ∈ K`. -/
theorem theorem_8_3_2_subspace [CompleteSpace V] (K : Submodule ℝ V) (ℓ : StrongDual ℝ V) {u : V}
    (hu : u ∈ K) :
    IsMinOn (fun v => (1 / 2 : ℝ) * ‖v‖ ^ 2 - ℓ v) (K : Set V) u ↔ ∀ v ∈ K, ⟪u, v⟫_ℝ = ℓ v := by
  rw [energy_innerSL_eq]
  exact SesqForm.isMinOn_energy_iff ℓ innerSL_hermitian one_pos innerSL_coercive K hu

/-! ### Theorem 8.3.3: the energy of a symmetric `V`-elliptic form -/

variable {a : BilinForm V} {M α : ℝ}

/-- Theorem 8.3.3, existence and uniqueness: the energy `E(v) = ½ a(v,v) − ℓ(v)` of a bounded,
symmetric, `V`-elliptic form has a unique minimizer on any nonempty closed convex set. -/
theorem theorem_8_3_3 [CompleteSpace V] (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) (hs : LinearMap.BilinForm.IsSymm a) (ℓ : StrongDual ℝ V)
    {K : Set V} (hne : K.Nonempty) (hcl : IsClosed K) (hconv : Convex ℝ K) :
    ∃! u, u ∈ K ∧ IsMinOn (a.energy ℓ) K u := by
  have hh := (BilinForm.isSymm_iff_isHermitian hM).mp hs
  exact SesqForm.existsUnique_isMinOn_energy (a := a.toCLM hM) hh ℓ hα ha hconv hcl hne

/-- Theorem 8.3.3, characterization (8.3.3): on a convex set the minimizer of the energy is the
solution of the variational inequality `a(u, v − u) ≥ ℓ(v − u)` for all `v ∈ K`. -/
theorem theorem_8_3_3_iff [CompleteSpace V] (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) (hs : LinearMap.BilinForm.IsSymm a) (ℓ : StrongDual ℝ V)
    {K : Set V} (hconv : Convex ℝ K) {u : V} (hu : u ∈ K) :
    IsMinOn (a.energy ℓ) K u ↔ ∀ v ∈ K, ℓ (v - u) ≤ a u (v - u) := by
  have hh := (BilinForm.isSymm_iff_isHermitian hM).mp hs
  exact SesqForm.isMinOn_energy_iff_forall_le (a := a.toCLM hM) hh ℓ hα ha hconv hu

/-- Theorem 8.3.3, characterization (8.3.4): on a subspace the minimizer of the energy is the
solution of the variational equation `a(u,v) = ℓ(v)` for all `v ∈ K`.  Neither closedness of `K`
nor finite dimension is needed. -/
theorem theorem_8_3_3_subspace [CompleteSpace V] (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) (hs : LinearMap.BilinForm.IsSymm a) (ℓ : StrongDual ℝ V)
    (K : Submodule ℝ V) {u : V} (hu : u ∈ K) :
    IsMinOn (a.energy ℓ) (K : Set V) u ↔ ∀ v ∈ K, a u v = ℓ v := by
  have hh := (BilinForm.isSymm_iff_isHermitian hM).mp hs
  exact SesqForm.isMinOn_energy_iff ℓ hh hα ha K hu

/-- The energy identity at the solution: `E(v) − E(u) = ½ ‖v − u‖_a²` (the computation inside the
proof of Theorem 8.3.3, and (9.1.9)). -/
theorem energy_sub_energy_eq [CompleteSpace V] (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) (hs : LinearMap.BilinForm.IsSymm a) (ℓ : StrongDual ℝ V) {u : V}
    (hu : ∀ v, a u v = ℓ v) (v : V) :
    a.energy ℓ v - a.energy ℓ u = (1 / 2 : ℝ) * a.energyNorm (v - u) ^ 2 := by
  have hh := (BilinForm.isSymm_iff_isHermitian hM).mp hs
  have hpos : SesqForm.IsCoerciveWith (a.toCLM hM) 0 :=
    SesqForm.IsCoerciveWith.mono (a.toCLM hM) ha hα.le
  exact SesqForm.energy_sub_energy_eq ℓ hh hpos hu v

/-! ### Theorem 8.3.4: the Lax–Milgram lemma -/

/-- Theorem 8.3.4 (Lax–Milgram): a bounded `V`-elliptic bilinear form on a Hilbert space makes
the variational problem (8.3.5) `a(u,v) = ℓ(v) ∀ v ∈ V` uniquely solvable. -/
theorem theorem_8_3_4 [CompleteSpace V] (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) (ℓ : StrongDual ℝ V) : ∃! u, ∀ v, a u v = ℓ v :=
  SesqForm.laxMilgram (a.toCLM hM) ℓ hα ha

/-- The stability estimate `‖u‖ ≤ ‖ℓ‖ / α` accompanying Theorem 8.3.4; it is the one-space case
of (8.7.5). -/
theorem theorem_8_3_4_norm_le [CompleteSpace V] (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) (ℓ : StrongDual ℝ V) {u : V} (hu : ∀ v, a u v = ℓ v) :
    ‖u‖ ≤ ‖ℓ‖ / α :=
  SesqForm.norm_le_of_forall_apply_eq (a.toCLM hM) ℓ hα ha hu

/-- The solution depends Lipschitz-continuously on the data, with constant `1/α`. -/
theorem theorem_8_3_4_norm_sub_le [CompleteSpace V] (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) {ℓ₁ ℓ₂ : StrongDual ℝ V} {u₁ u₂ : V} (h₁ : ∀ v, a u₁ v = ℓ₁ v)
    (h₂ : ∀ v, a u₂ v = ℓ₂ v) : ‖u₁ - u₂‖ ≤ ‖ℓ₁ - ℓ₂‖ / α :=
  SesqForm.norm_sub_le_of_forall_apply_eq (a.toCLM hM) hα ha h₁ h₂

/-! ### First proof of Theorem 8.3.4: the damped iteration `P_θ` -/

/-- The estimate `‖(I − θ𝒥A)w‖² ≤ (1 − 2θα + θ²M²)‖w‖²` behind the first proof of
Theorem 8.3.4. -/
theorem norm_sub_smul_toOperator_sq_le [CompleteSpace V] (hM0 : 0 ≤ M) (hM : a.IsBoundedWith M)
    (ha : a.IsEllipticWith α) {θ : ℝ} (hθ : 0 ≤ θ) (w : V) :
    ‖w - θ • BilinForm.toOperator a hM w‖ ^ 2 ≤ (1 - 2 * θ * α + θ ^ 2 * M ^ 2) * ‖w‖ ^ 2 := by
  have hcoer := BilinForm.isCoerciveWith_toOperator hM ha
  have hbase := ContinuousLinearMap.norm_sub_smul_apply_sq_le (𝕜 := ℝ) hcoer hθ w
  refine hbase.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
  have hA : ‖BilinForm.toOperator a hM‖ ≤ M := BilinForm.norm_toOperator_le hM0 hM
  have hA0 : 0 ≤ ‖BilinForm.toOperator a hM‖ := norm_nonneg _
  have hsq : ‖BilinForm.toOperator a hM‖ ^ 2 ≤ M ^ 2 := by nlinarith
  nlinarith [sq_nonneg θ, hsq]

/-- The operator `A = 𝒥 a` of a `V`-elliptic form is strongly monotone (5.1.8) with the same
constant, which is what the §5.1 theory (`zarantonello`, `contractingWith_damped`) asks for. -/
theorem stronglyMonotone_toOperator [CompleteSpace V] (hM : a.IsBoundedWith M)
    (ha : a.IsEllipticWith α) (x y : V) :
    α * ‖x - y‖ ^ 2 ≤ RCLike.re (inner ℝ
      (BilinForm.toOperator a hM x - BilinForm.toOperator a hM y) (x - y)) := by
  rw [← map_sub]
  exact BilinForm.isCoerciveWith_toOperator hM ha (x - y)

/-- The operator of a bounded form is Lipschitz with the constant of (9.4.3). -/
theorem lipschitzWith_toOperator [CompleteSpace V] (hM0 : 0 ≤ M) (hM : a.IsBoundedWith M) :
    LipschitzWith (Real.toNNReal M) (BilinForm.toOperator a hM) := by
  refine (BilinForm.toOperator a hM).lipschitzWith.weaken ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal M hM0]
  exact BilinForm.norm_toOperator_le hM0 hM

/-- The map `P_θ u = u − θ (A u − f)` of the first proof of Theorem 8.3.4 is a contraction for
`0 < θ < 2α/M²`, so Banach's fixed point theorem produces the solution of (8.3.5). -/
theorem contractingWith_damped_sub_smul [CompleteSpace V] (hM0 : 0 < M) (hM : a.IsBoundedWith M)
    (hα : 0 < α) (ha : a.IsEllipticWith α) (ℓ : StrongDual ℝ V) {θ : ℝ} (hθ : 0 < θ)
    (hθ' : θ < 2 * α / M ^ 2) :
    ContractingWith (Real.toNNReal (Real.sqrt (1 - 2 * θ * α + θ ^ 2 * M ^ 2)))
      (fun u => u - θ • (BilinForm.toOperator a hM u - SesqForm.rieszRep ℓ)) :=
  contractingWith_damped (𝕜 := ℝ) hα hM0 (stronglyMonotone_toOperator hM ha)
    (lipschitzWith_toOperator hM0.le hM) (SesqForm.rieszRep ℓ) hθ hθ'

/-! ### Second proof of Theorem 8.3.4: closed range plus dense range -/

/-- `α ‖u‖ ≤ ‖A u‖` for the operator `A = 𝒥 a` of a `V`-elliptic form: the stability estimate
(8.2.2) that drives the second proof of Theorem 8.3.4. -/
theorem norm_le_norm_toOperator [CompleteSpace V] (hM : a.IsBoundedWith M)
    (ha : a.IsEllipticWith α) (u : V) : α * ‖u‖ ≤ ‖BilinForm.toOperator a hM u‖ := by
  rw [SesqForm.toOperator_apply_eq_rieszRep, SesqForm.norm_rieszRep]
  exact SesqForm.IsCoerciveWith.norm_le_norm_apply (a.toCLM hM) ha u

theorem isClosed_range_toOperator [CompleteSpace V] (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) :
    IsClosed (LinearMap.range (BilinForm.toOperator a hM : V →ₗ[ℝ] V) : Set V) :=
  ContinuousLinearMap.isClosed_range_of_le_norm _ hα (norm_le_norm_toOperator hM ha)

theorem orthogonal_range_toOperator [CompleteSpace V] (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) :
    (LinearMap.range (BilinForm.toOperator a hM : V →ₗ[ℝ] V))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  have hz : ⟪BilinForm.toOperator a hM v, v⟫_ℝ = 0 := hv _ ⟨v, rfl⟩
  rw [BilinForm.inner_toOperator] at hz
  have h1 : α * ‖v‖ ^ 2 ≤ 0 := (ha v).trans_eq hz
  have h2 : ‖v‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖v‖]
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm h2 (sq_nonneg _)))

/-- The second proof of Theorem 8.3.4: the operator `A = 𝒥 a` is bounded below, hence has closed
range, and its range is dense, hence `A` is a bijection of `V` (Theorem 8.2.1). -/
theorem bijective_toOperator [CompleteSpace V] (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) : Function.Bijective (BilinForm.toOperator a hM) :=
  ContinuousLinearMap.bijective_of_le_norm_of_orthogonal_range_eq_bot _ hα
    (norm_le_norm_toOperator hM ha) (orthogonal_range_toOperator hM hα ha)

/-! ### Exercise 8.3.1 -/

/-- Exercise 8.3.1: Lax–Milgram follows from the theory of strongly monotone Lipschitz operators
of §5.1 (the backbone's `zarantonello`), applied to `T = A` with `c₁ = α`, `c₂ = M` and `b = f`
the Riesz representative of `ℓ`. -/
theorem exercise_8_3_1 [CompleteSpace V] (hM0 : 0 ≤ M) (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) (ℓ : StrongDual ℝ V) : ∃! u, ∀ v, a u v = ℓ v := by
  obtain ⟨u, hu, huniq⟩ := zarantonello (𝕜 := ℝ) hα (stronglyMonotone_toOperator hM ha)
    (lipschitzWith_toOperator hM0 hM) (SesqForm.rieszRep ℓ)
  refine ⟨u, (BilinForm.toOperator_eq_rieszRep_iff hM ℓ u).mp hu, fun y hy => ?_⟩
  exact huniq y ((BilinForm.toOperator_eq_rieszRep_iff hM ℓ y).mpr hy)

end Chapter08

end AtkinsonHan

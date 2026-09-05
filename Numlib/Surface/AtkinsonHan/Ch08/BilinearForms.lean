import Numlib.Backbone

/-!
# Bilinear forms and the operators they represent (§8.3, §9.4)

Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional Analysis
Framework*, 3rd edition, Springer, 2009.

The data of §8.3 and of Chapter 9 is a real bilinear form `a : V × V → ℝ` on a real normed
(later Hilbert) space `V`, together with `ℓ ∈ V'`.  Such a form is a `BilinForm V`
(`V →ₗ[ℝ] V →ₗ[ℝ] ℝ`), and the book's vocabulary -- bounded, positive, strictly positive,
strongly positive (= `V`-elliptic), symmetric -- is the list of predicates below.

`BilinForm.toCLM` bundles a bounded form as a `V →L[ℝ] V →L[ℝ] ℝ`, which *is* the backbone's
`SesqForm ℝ V`, so the `Numlib.Variational` API applies to it verbatim; `BilinForm.ofCLM` is the
inverse direction and `theorem_8_3_1` packages the two as the one-to-one correspondence of
Theorem 8.3.1 between `A ∈ L(V, V')` and the bounded bilinear forms on `V`.  On a Hilbert space
`BilinForm.toOperator` is the Riesz operator `A : V → V` of (9.4.5), with `(A u, v) = a(u,v)`,
and `BilinForm.energy` is the energy functional `E(v) = ½ a(v,v) − ℓ(v)` of Theorem 8.3.3.
-/

open scoped InnerProductSpace

namespace AtkinsonHan

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

end AtkinsonHan

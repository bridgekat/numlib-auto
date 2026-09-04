import Numlib.InnerProductSpace.Coercive
import Numlib.InnerProductSpace.Energy
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Bounded sesquilinear forms on Hilbert spaces

A bounded form is `a : V →L⋆[𝕜] V →L[𝕜] 𝕜` (conjugate-linear in the first slot, as `innerSL`):
boundedness with constant `M`, coercivity `c ‖v‖² ≤ re (a v v)` (Atkinson–Han's
"`V`-elliptic"/"strongly positive"), Hermitian symmetry, the associated operator
`SesqForm.toOperator a` (`⟪A u, v⟫ = a u v`, Mathlib's
`InnerProductSpace.continuousLinearMapOfBilin`), the Riesz representative of a functional, and
the energy functional `E(v) = ½ re (a v v) - re (ℓ v)` (AH §8.3, §9.4; Kress §3.?; Saad §5.2
in the operator language). Over `ℝ` a `V →L[ℝ] V →L[ℝ] ℝ` *is* a `V →L⋆[ℝ] V →L[ℝ] ℝ` (same
defeq Mathlib's `LaxMilgram.lean` uses), so the real surfaces need no conversion; the `_real`
lemmas remove the `re`/`conj` decorations.
-/

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- Bounded sesquilinear forms on `V`. -/
abbrev SesqForm (𝕜 V : Type*) [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] :=
  V →L⋆[𝕜] V →L[𝕜] 𝕜

namespace SesqForm

variable (a : SesqForm 𝕜 V)

/-- `‖a u v‖ ≤ M ‖u‖ ‖v‖`. -/
def IsBoundedWith (M : ℝ) : Prop := ∀ u v, ‖a u v‖ ≤ M * ‖u‖ * ‖v‖

/-- `c ‖v‖² ≤ re (a v v)` (AH: `V`-elliptic with constant `c`; strongly positive). -/
def IsCoerciveWith (c : ℝ) : Prop := ∀ v, c * ‖v‖ ^ 2 ≤ RCLike.re (a v v)

/-- Coercive for some `c > 0`. -/
def IsCoercive : Prop := ∃ c : ℝ, 0 < c ∧ a.IsCoerciveWith c

/-- `a u v = conj (a v u)`. -/
def IsHermitian : Prop := ∀ u v, a u v = starRingEnd 𝕜 (a v u)

theorem isBoundedWith_opNorm : a.IsBoundedWith ‖a‖ := by
  sorry

theorem opNorm_le_of_isBoundedWith {M : ℝ} (hM : 0 ≤ M) (h : a.IsBoundedWith M) : ‖a‖ ≤ M := by
  sorry

theorem IsCoerciveWith.mono {c c' : ℝ} (h : a.IsCoerciveWith c) (hc : c' ≤ c) :
    a.IsCoerciveWith c' := by
  sorry

/-- Coercivity gives the lower bound `c ‖u‖ ≤ ‖a u‖` on the functional `a u`. -/
theorem IsCoerciveWith.norm_le_norm_apply {c : ℝ} (h : a.IsCoerciveWith c) (u : V) :
    c * ‖u‖ ≤ ‖a u‖ := by
  sorry

/-- Real forms: coercivity without `re`. -/
theorem isCoerciveWith_real_iff {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (a : SesqForm ℝ V) (c : ℝ) : a.IsCoerciveWith c ↔ ∀ v, c * ‖v‖ ^ 2 ≤ a v v := by
  sorry

/-- Real forms: Hermitian = symmetric. -/
theorem isHermitian_real_iff {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (a : SesqForm ℝ V) : a.IsHermitian ↔ ∀ u v, a u v = a v u := by
  sorry

/-- The inner product as a form. -/
theorem innerSL_isCoerciveWith : SesqForm.IsCoerciveWith (innerSL 𝕜 : SesqForm 𝕜 V) 1 := by
  sorry

theorem innerSL_isHermitian : SesqForm.IsHermitian (innerSL 𝕜 : SesqForm 𝕜 V) := by
  sorry

/-- The form of an operator: `ofOperator A u v = ⟪A u, v⟫`. -/
noncomputable def ofOperator (A : V →L[𝕜] V) : SesqForm 𝕜 V := (innerSL 𝕜).comp A

theorem ofOperator_apply (A : V →L[𝕜] V) (u v : V) : ofOperator A u v = inner 𝕜 (A u) v := rfl

section Operator

variable [CompleteSpace V]

/-- The operator `A` with `⟪A u, v⟫ = a u v` (AH (8.3.1) via Riesz, (9.4.5)); Mathlib's
`InnerProductSpace.continuousLinearMapOfBilin`. -/
noncomputable abbrev toOperator : V →L[𝕜] V := InnerProductSpace.continuousLinearMapOfBilin a

theorem inner_toOperator (u v : V) : inner 𝕜 (toOperator a u) v = a u v :=
  InnerProductSpace.continuousLinearMapOfBilin_apply a u v

/-- The Riesz representative `f` of a functional, `⟪f, v⟫ = ℓ v`. -/
noncomputable def rieszRep (ℓ : V →L[𝕜] 𝕜) : V := (InnerProductSpace.toDual 𝕜 V).symm ℓ

theorem inner_rieszRep (ℓ : V →L[𝕜] 𝕜) (v : V) : inner 𝕜 (rieszRep ℓ) v = ℓ v := by
  sorry

theorem norm_rieszRep (ℓ : V →L[𝕜] 𝕜) : ‖rieszRep ℓ‖ = ‖ℓ‖ := by
  sorry

theorem toOperator_ofOperator (A : V →L[𝕜] V) : toOperator (ofOperator A) = A := by
  sorry

theorem ofOperator_toOperator : ofOperator (toOperator a) = a := by
  sorry

theorem isCoerciveWith_iff_toOperator (c : ℝ) :
    a.IsCoerciveWith c ↔ (toOperator a : V →ₗ[𝕜] V).IsCoerciveWith c := by
  sorry

theorem isHermitian_iff_toOperator_isSymmetric :
    a.IsHermitian ↔ (toOperator a : V →ₗ[𝕜] V).IsSymmetric := by
  sorry

theorem norm_toOperator : ‖toOperator a‖ = ‖a‖ := by
  sorry

/-- `a u v = ℓ v` for all `v` iff `A u = f`. -/
theorem forall_apply_eq_iff_toOperator_eq (ℓ : V →L[𝕜] 𝕜) (u : V) :
    (∀ v, a u v = ℓ v) ↔ toOperator a u = rieszRep ℓ := by
  sorry

end Operator

section Energy

/-- The energy functional `E(v) = ½ re (a v v) - re (ℓ v)` (AH Thm 8.3.3, (9.1.7)). -/
noncomputable def energy (ℓ : V →L[𝕜] 𝕜) (v : V) : ℝ :=
  (1 / 2 : ℝ) * RCLike.re (a v v) - RCLike.re (ℓ v)

/-- The energy norm of a Hermitian coercive form. -/
noncomputable def energyNorm (v : V) : ℝ := Real.sqrt (RCLike.re (a v v))

theorem energyNorm_eq_energyNorm_toOperator [CompleteSpace V] (v : V) :
    a.energyNorm v = _root_.energyNorm (toOperator a : V →ₗ[𝕜] V) v := by
  sorry

/-- Norm equivalence `√c ‖v‖ ≤ ‖v‖_a ≤ √M ‖v‖` (AH §9.4, Thm 8.3.3). -/
theorem sqrt_mul_norm_le_energyNorm {c : ℝ} (hc : 0 ≤ c) (h : a.IsCoerciveWith c) (v : V) :
    Real.sqrt c * ‖v‖ ≤ a.energyNorm v := by
  sorry

theorem energyNorm_le_sqrt_mul_norm {M : ℝ} (h : a.IsBoundedWith M) (v : V) :
    a.energyNorm v ≤ Real.sqrt M * ‖v‖ := by
  sorry

end Energy

end SesqForm

/-- Two-space bounded sesquilinear forms `U × V → 𝕜` (Petrov–Galerkin, Babuška–Nečas). -/
abbrev SesqForm₂ (𝕜 U V : Type*) [RCLike 𝕜] [NormedAddCommGroup U] [InnerProductSpace 𝕜 U]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] :=
  U →L⋆[𝕜] V →L[𝕜] 𝕜

namespace SesqForm₂

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace 𝕜 U] (a : SesqForm₂ 𝕜 U V)

/-- The inf–sup (Babuška–Brezzi) condition with constant `α`, in operator-norm form:
`α ‖u‖ ≤ ‖a u‖ = sup_{v ≠ 0} |a u v| / ‖v‖` (AH (8.7.2), (9.2.3)). -/
def InfSupWith (α : ℝ) : Prop := ∀ u, α * ‖u‖ ≤ ‖a u‖

/-- The transposed nondegeneracy condition (AH (8.7.3)): for every `v ≠ 0` some `u` sees it. -/
def IsNondegenerate : Prop := ∀ v, v ≠ 0 → ∃ u, a u v ≠ 0

/-- `sup_{v ≠ 0} |a u v| / ‖v‖ = ‖a u‖`: the book's inf–sup quantity is an operator norm. -/
theorem iSup_norm_div_eq_norm (u : U) :
    (⨆ v : {v : V // v ≠ 0}, ‖a u v‖ / ‖(v : V)‖) = ‖a u‖ := by
  sorry

/-- Coercive one-space forms satisfy the inf–sup condition (AH Ex 8.7.1). -/
theorem _root_.SesqForm.IsCoerciveWith.infSupWith {a : SesqForm 𝕜 V} {c : ℝ}
    (h : a.IsCoerciveWith c) : SesqForm₂.InfSupWith (a : SesqForm₂ 𝕜 V V) c := by
  sorry

end SesqForm₂

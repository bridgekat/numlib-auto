import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Analysis.InnerProductSpace.Energy
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

theorem isBoundedWith_opNorm : a.IsBoundedWith ‖a‖ := fun u v => a.le_opNorm₂ u v

theorem opNorm_le_of_isBoundedWith {M : ℝ} (hM : 0 ≤ M) (h : a.IsBoundedWith M) : ‖a‖ ≤ M :=
  a.opNorm_le_bound₂ hM h

theorem IsCoerciveWith.mono {c c' : ℝ} (h : a.IsCoerciveWith c) (hc : c' ≤ c) :
    a.IsCoerciveWith c' := fun v =>
  (mul_le_mul_of_nonneg_right hc (sq_nonneg _)).trans (h v)

/-- Coercivity gives the lower bound `c ‖u‖ ≤ ‖a u‖` on the functional `a u`. -/
theorem IsCoerciveWith.norm_le_norm_apply {c : ℝ} (h : a.IsCoerciveWith c) (u : V) :
    c * ‖u‖ ≤ ‖a u‖ := by
  rcases eq_or_lt_of_le (norm_nonneg u) with hu | hu
  · simp [← hu]
  · refine le_of_mul_le_mul_right ?_ hu
    calc c * ‖u‖ * ‖u‖ = c * ‖u‖ ^ 2 := by ring
      _ ≤ RCLike.re (a u u) := h u
      _ ≤ ‖a u u‖ := RCLike.re_le_norm _
      _ ≤ ‖a u‖ * ‖u‖ := (a u).le_opNorm u

/-- Real forms: coercivity without `re`. -/
theorem isCoerciveWith_real_iff {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (a : SesqForm ℝ V) (c : ℝ) : a.IsCoerciveWith c ↔ ∀ v, c * ‖v‖ ^ 2 ≤ a v v := Iff.rfl

/-- Real forms: Hermitian = symmetric. -/
theorem isHermitian_real_iff {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (a : SesqForm ℝ V) : a.IsHermitian ↔ ∀ u v, a u v = a v u := Iff.rfl

/-- The inner product as a form. -/
theorem innerSL_isCoerciveWith : SesqForm.IsCoerciveWith (innerSL 𝕜 : SesqForm 𝕜 V) 1 := fun v => by
  simp

theorem innerSL_isHermitian : SesqForm.IsHermitian (innerSL 𝕜 : SesqForm 𝕜 V) := fun u v =>
  (inner_conj_symm (𝕜 := 𝕜) u v).symm

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

theorem inner_rieszRep (ℓ : V →L[𝕜] 𝕜) (v : V) : inner 𝕜 (rieszRep ℓ) v = ℓ v :=
  InnerProductSpace.toDual_symm_apply

theorem norm_rieszRep (ℓ : V →L[𝕜] 𝕜) : ‖rieszRep ℓ‖ = ‖ℓ‖ :=
  (InnerProductSpace.toDual 𝕜 V).symm.norm_map ℓ

/-- `toOperator a u` is the Riesz representative of the functional `a u`; both are built from
`InnerProductSpace.toDual.symm`. -/
theorem toOperator_apply_eq_rieszRep (u : V) : toOperator a u = rieszRep (a u) := rfl

theorem toOperator_ofOperator (A : V →L[𝕜] V) : toOperator (ofOperator A) = A := by
  ext u
  exact ext_inner_right 𝕜 fun v => (inner_toOperator _ u v).trans (ofOperator_apply A u v)

theorem ofOperator_toOperator : ofOperator (toOperator a) = a := by
  ext u v
  exact inner_toOperator a u v

theorem isCoerciveWith_iff_toOperator (c : ℝ) :
    a.IsCoerciveWith c ↔ (toOperator a : V →ₗ[𝕜] V).IsCoerciveWith c := by
  simp only [IsCoerciveWith, LinearMap.IsCoerciveWith, ContinuousLinearMap.coe_coe,
    inner_toOperator]

theorem isHermitian_iff_toOperator_isSymmetric :
    a.IsHermitian ↔ (toOperator a : V →ₗ[𝕜] V).IsSymmetric := by
  simp only [IsHermitian, LinearMap.IsSymmetric, ContinuousLinearMap.coe_coe]
  refine forall_congr' fun u => forall_congr' fun v => ?_
  rw [← inner_conj_symm (𝕜 := 𝕜) u (toOperator a v), inner_toOperator, inner_toOperator]

theorem norm_toOperator : ‖toOperator a‖ = ‖a‖ :=
  ContinuousLinearMap.opNorm_ext _ _ fun u => by
    rw [toOperator_apply_eq_rieszRep, norm_rieszRep]

/-- `a u v = ℓ v` for all `v` iff `A u = f`. -/
theorem forall_apply_eq_iff_toOperator_eq (ℓ : V →L[𝕜] 𝕜) (u : V) :
    (∀ v, a u v = ℓ v) ↔ toOperator a u = rieszRep ℓ := by
  constructor
  · intro h
    exact ext_inner_right 𝕜 fun v => by rw [inner_toOperator, inner_rieszRep, h]
  · intro h v
    rw [← inner_toOperator, h, inner_rieszRep]

end Operator

section Energy

/-- The energy functional `E(v) = ½ re (a v v) - re (ℓ v)` (AH Thm 8.3.3, (9.1.7)). -/
noncomputable def energy (ℓ : V →L[𝕜] 𝕜) (v : V) : ℝ :=
  (1 / 2 : ℝ) * RCLike.re (a v v) - RCLike.re (ℓ v)

/-- The energy norm of a Hermitian coercive form. -/
noncomputable def energyNorm (v : V) : ℝ := Real.sqrt (RCLike.re (a v v))

theorem energyNorm_eq_energyNorm_toOperator [CompleteSpace V] (v : V) :
    a.energyNorm v = _root_.energyNorm (toOperator a : V →ₗ[𝕜] V) v := by
  simp only [energyNorm, _root_.energyNorm, ContinuousLinearMap.coe_coe, inner_toOperator]

/-- Norm equivalence `√c ‖v‖ ≤ ‖v‖_a ≤ √M ‖v‖` (AH §9.4, Thm 8.3.3). -/
theorem sqrt_mul_norm_le_energyNorm {c : ℝ} (hc : 0 ≤ c) (h : a.IsCoerciveWith c) (v : V) :
    Real.sqrt c * ‖v‖ ≤ a.energyNorm v := by
  have hcv : Real.sqrt c * ‖v‖ = Real.sqrt (c * ‖v‖ ^ 2) := by
    rw [Real.sqrt_mul hc, Real.sqrt_sq (norm_nonneg v)]
  rw [energyNorm, hcv]
  exact Real.sqrt_le_sqrt (h v)

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
  have hle : ∀ v : {v : V // v ≠ 0}, ‖a u (v : V)‖ / ‖(v : V)‖ ≤ ‖a u‖ := fun v =>
    (div_le_iff₀ (norm_pos_iff.mpr v.2)).mpr ((a u).le_opNorm _)
  refine le_antisymm (Real.iSup_le hle (norm_nonneg _)) ?_
  refine (a u).opNorm_le_bound (Real.iSup_nonneg fun v => by positivity) fun v => ?_
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · rw [← div_le_iff₀ (norm_pos_iff.mpr hv)]
    exact le_ciSup (f := fun v : {v : V // v ≠ 0} => ‖a u (v : V)‖ / ‖(v : V)‖)
      ⟨‖a u‖, Set.forall_mem_range.2 hle⟩ ⟨v, hv⟩

/-- Coercive one-space forms satisfy the inf–sup condition (AH Ex 8.7.1). -/
theorem _root_.SesqForm.IsCoerciveWith.infSupWith {a : SesqForm 𝕜 V} {c : ℝ}
    (h : a.IsCoerciveWith c) : SesqForm₂.InfSupWith (a : SesqForm₂ 𝕜 V V) c :=
  fun u => SesqForm.IsCoerciveWith.norm_le_norm_apply a h u

end SesqForm₂

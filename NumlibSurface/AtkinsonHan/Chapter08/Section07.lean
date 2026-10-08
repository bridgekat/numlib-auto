import Numlib.Analysis.Normed.Operator.Scaling
import Numlib.Variational.Forms
import Numlib.Variational.LaxMilgram
import NumlibSurface.AtkinsonHan.Chapter08.Section03

/-!
# Atkinson–Han §8.7: the generalized Lax–Milgram lemma

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §8.7.

Theorem 8.7.1, which the book attributes to Nečas: a bilinear form `a : U × V → ℝ` on a pair of
real Hilbert spaces which is bounded (8.7.1), satisfies the inf–sup condition (8.7.2) and is
nondegenerate in its second slot (8.7.3) makes `a(u,v) = ℓ(v) ∀ v ∈ V` uniquely solvable (8.7.4),
with the stability estimate (8.7.5) `‖u‖ ≤ ‖ℓ‖/α`.

The book writes (8.7.2) as `sup_{0 ≠ v ∈ V} a(u,v)/‖v‖ ≥ α ‖u‖`, without absolute values.  The
backbone's `ContinuousLinearMap.iSup_apply_div_eq_opNorm` identifies that real supremum with the
operator norm `‖a u‖` of the functional `a u`, which is the form the backbone's
`SesqForm₂.InfSupWith` takes.  (8.7.3) is printed as
`sup_{u ∈ U} a(u,v) > 0`, but the supremum of a nonzero linear functional is `+∞`, so it is
formalized as `∃ u, 0 < a(u,v)` — equivalent, by the same sign flip, to the backbone's
`SesqForm₂.IsNondegenerate`.

As in §8.3, the unique solvability (8.7.4) and the stability estimate (8.7.5) are separate
declarations: `theorem_8_7_1` and `theorem_8_7_1_norm_le`, and likewise for `exercise_8_7_1`.
-/

open scoped InnerProductSpace

namespace AtkinsonHan

/-! ### Two-space bilinear forms -/

/-- A real bilinear form `a : U × V → ℝ` on a pair of spaces (§8.7, §9.2). -/
abbrev BilinForm₂ (U V : Type*) [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] :=
  U →ₗ[ℝ] V →ₗ[ℝ] ℝ

namespace BilinForm₂

section Normed

variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V]
  [NormedSpace ℝ V]

/-- `|a(u,v)| ≤ M ‖u‖_U ‖v‖_V`: boundedness (8.7.1), (9.2.2). -/
def IsBoundedWith (a : BilinForm₂ U V) (M : ℝ) : Prop := ∀ u v, |a u v| ≤ M * ‖u‖ * ‖v‖

variable {a : BilinForm₂ U V} {M α : ℝ}

/-- A one-space bounded form is a two-space bounded form. -/
theorem isBoundedWith_of_isBoundedWith {b : BilinForm V} (h : b.IsBoundedWith M) :
    IsBoundedWith (U := V) (V := V) b M := h

/-- The bundled bounded form `U →L[ℝ] V →L[ℝ] ℝ`, which over `ℝ` *is* the backbone's
`SesqForm₂ ℝ U V`. -/
noncomputable def toCLM (a : BilinForm₂ U V) (hM : a.IsBoundedWith M) : U →L[ℝ] V →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂ a M fun u v => by rw [Real.norm_eq_abs]; exact hM u v

/-- Bundling a bounded two-space form as an element of `L(U, V')` does not change its values. -/
@[simp]
theorem toCLM_apply (hM : a.IsBoundedWith M) (u : U) (v : V) : a.toCLM hM u v = a u v := rfl

/-- Any nonnegative constant `M` of (8.7.1) bounds the operator norm of the bundled form, so the
book's boundedness constant may be used wherever the backbone asks for `‖a‖`. -/
theorem norm_toCLM_le (hM0 : 0 ≤ M) (hM : a.IsBoundedWith M) : ‖a.toCLM hM‖ ≤ M :=
  LinearMap.mkContinuous₂_norm_le _ hM0 _

/-- The bound used to bundle a two-space form is a bound for the bundled form. -/
theorem isBoundedWith_toCLM (hM : a.IsBoundedWith M) :
    ∀ u v, ‖a.toCLM hM u v‖ ≤ M * ‖u‖ * ‖v‖ := hM

/-- (8.7.2), (9.2.3): the inf–sup condition, with the supremum written as the book writes it,
without absolute values. -/
def InfSup (a : BilinForm₂ U V) (α : ℝ) : Prop :=
  ∀ u, α * ‖u‖ ≤ ⨆ v : {v : V // v ≠ 0}, a u v / ‖(v : V)‖

/-- The book's supremum in (8.7.2) is the operator norm of the functional `a u`. -/
theorem iSup_div_eq_norm_apply (hM : a.IsBoundedWith M) (u : U) :
    (⨆ v : {v : V // v ≠ 0}, a u v / ‖(v : V)‖) = ‖a.toCLM hM u‖ :=
  (a.toCLM hM u).iSup_apply_div_eq_opNorm

/-- (8.7.3), (9.2.4) as printed — `sup_{u ∈ U} a(u,v) > 0` — is `∃ u, 0 < a(u,v)`, and by the
sign flip `u ↦ -u` that is the backbone's `SesqForm₂.IsNondegenerate`. -/
theorem exists_pos_iff_exists_ne_zero (a : BilinForm₂ U V) (v : V) :
    (∃ u, 0 < a u v) ↔ ∃ u, a u v ≠ 0 := by
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, ne_of_gt hu⟩
  · rintro ⟨u, hu⟩
    rcases lt_or_gt_of_ne hu with h | h
    · exact ⟨-u, by simpa using h⟩
    · exact ⟨u, h⟩

end Normed

section Inner

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
variable {a : BilinForm₂ U V} {M α : ℝ}

/-- (8.7.2) is the backbone's `SesqForm₂.InfSupWith`. -/
theorem infSup_iff_infSupWith (hM : a.IsBoundedWith M) :
    a.InfSup α ↔ SesqForm₂.InfSupWith (𝕜 := ℝ) (U := U) (V := V) (a.toCLM hM) α := by
  refine forall_congr' fun u => ?_
  rw [iSup_div_eq_norm_apply hM u]

/-- (8.7.3) is the backbone's `SesqForm₂.IsNondegenerate` for the bundled form. -/
theorem isNondegenerate_toCLM (hM : a.IsBoundedWith M) (h : ∀ v, v ≠ 0 → ∃ u, 0 < a u v) :
    SesqForm₂.IsNondegenerate (𝕜 := ℝ) (U := U) (V := V) (a.toCLM hM) :=
  fun v hv => (exists_pos_iff_exists_ne_zero a v).mp (h v hv)

end Inner

end BilinForm₂

/-! ### Exercise 8.7.1: a `V`-elliptic form satisfies (8.7.2) and (8.7.3)

Stated in the `BilinForm.IsEllipticWith` namespace, so that they are reachable by dot notation
from an ellipticity hypothesis. -/

section Elliptic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {a : BilinForm V} {M α : ℝ}

/-- Exercise 8.7.1, first half: a `V`-elliptic form satisfies the inf–sup condition (8.7.2) with
the same constant `α`, because `v = u` already realizes the bound. -/
theorem BilinForm.IsEllipticWith.infSup (ha : a.IsEllipticWith α) (hM : a.IsBoundedWith M)
    (u : V) : α * ‖u‖ ≤ ⨆ v : {v : V // v ≠ 0}, a u v / ‖(v : V)‖ := by
  rw [BilinForm₂.iSup_div_eq_norm_apply (BilinForm₂.isBoundedWith_of_isBoundedWith hM) u]
  exact SesqForm.IsCoerciveWith.norm_le_norm_apply (a.toCLM hM) ha u

/-- Exercise 8.7.1, second half: a `V`-elliptic form satisfies the nondegeneracy condition
(8.7.3), because `u = v` gives `a(v,v) ≥ α‖v‖² > 0`. -/
theorem BilinForm.IsEllipticWith.exists_pos (ha : a.IsEllipticWith α) (hα : 0 < α) (v : V)
    (hv : v ≠ 0) : ∃ u, 0 < a u v :=
  ⟨v, lt_of_lt_of_le (by positivity) (ha v)⟩

end Elliptic

namespace Chapter08

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]

/-- **Theorem 8.7.1** (the generalized Lax–Milgram lemma, due to Nečas): a bounded bilinear form
on a pair of real Hilbert spaces satisfying the inf–sup condition (8.7.2) and the nondegeneracy
condition (8.7.3) makes the problem (8.7.4) `a(u,v) = ℓ(v) ∀ v ∈ V` uniquely solvable.  The
accompanying stability estimate (8.7.5) is `theorem_8_7_1_norm_le`. -/
theorem theorem_8_7_1 [CompleteSpace U] [CompleteSpace V] (a : BilinForm₂ U V)
    (ℓ : StrongDual ℝ V) {M α : ℝ} (hα : 0 < α)
    (h871 : a.IsBoundedWith M)
    (h872 : ∀ u, α * ‖u‖ ≤ ⨆ v : {v : V // v ≠ 0}, a u v / ‖(v : V)‖)
    (h873 : ∀ v, v ≠ 0 → ∃ u, 0 < a u v) :
    ∃! u, ∀ v, a u v = ℓ v :=
  SesqForm₂.babuska_necas (a.toCLM h871) ℓ hα ((BilinForm₂.infSup_iff_infSupWith h871).mp h872)
    (BilinForm₂.isNondegenerate_toCLM h871 h873)

/-- The stability estimate (8.7.5) `‖u‖_U ≤ ‖ℓ‖_{V'}/α` accompanying Theorem 8.7.1.  Only the
inf–sup condition (8.7.2) is used; nondegeneracy is what makes a solution exist, not what bounds
it. -/
theorem theorem_8_7_1_norm_le [CompleteSpace U] [CompleteSpace V] (a : BilinForm₂ U V)
    (ℓ : StrongDual ℝ V) {M α : ℝ} (hα : 0 < α) (h871 : a.IsBoundedWith M)
    (h872 : ∀ u, α * ‖u‖ ≤ ⨆ v : {v : V // v ≠ 0}, a u v / ‖(v : V)‖) {u : U}
    (hu : ∀ v, a u v = ℓ v) : ‖u‖ ≤ ‖ℓ‖ / α :=
  SesqForm₂.norm_le_of_infSupWith (a.toCLM h871) ℓ hα
    ((BilinForm₂.infSup_iff_infSupWith h871).mp h872) hu

/-- Exercise 8.7.1: Theorem 8.7.1 contains the Lax–Milgram lemma, Theorem 8.3.4. -/
theorem exercise_8_7_1 [CompleteSpace V] (a : BilinForm V) (ℓ : StrongDual ℝ V) {M α : ℝ}
    (hM : a.IsBoundedWith M) (hα : 0 < α) (ha : a.IsEllipticWith α) : ∃! u, ∀ v, a u v = ℓ v :=
  theorem_8_7_1 a ℓ hα (BilinForm₂.isBoundedWith_of_isBoundedWith hM) (ha.infSup hM)
    fun v hv => ha.exists_pos hα v hv

/-- Exercise 8.7.1, the estimate: (8.7.5) specializes to the stability estimate of
Theorem 8.3.4. -/
theorem exercise_8_7_1_norm_le [CompleteSpace V] (a : BilinForm V) (ℓ : StrongDual ℝ V)
    {M α : ℝ} (hM : a.IsBoundedWith M) (hα : 0 < α) (ha : a.IsEllipticWith α) {u : V}
    (hu : ∀ v, a u v = ℓ v) : ‖u‖ ≤ ‖ℓ‖ / α :=
  theorem_8_7_1_norm_le a ℓ hα (BilinForm₂.isBoundedWith_of_isBoundedWith hM) (ha.infSup hM) hu

end Chapter08

end AtkinsonHan

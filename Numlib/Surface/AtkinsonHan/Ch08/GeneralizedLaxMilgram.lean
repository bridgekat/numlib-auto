import Numlib.Surface.AtkinsonHan.Ch08.BilinearForms

/-!
# The generalized Lax–Milgram lemma (§8.7)

Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional Analysis
Framework*, 3rd edition, Springer, 2009.

Theorem 8.7.1, which the book attributes to Nečas: a bilinear form `a : U × V → ℝ` on a pair of
real Hilbert spaces which is bounded (8.7.1), satisfies the inf–sup condition (8.7.2) and is
nondegenerate in its second slot (8.7.3) makes `a(u,v) = ℓ(v) ∀ v ∈ V` uniquely solvable (8.7.4),
with the stability estimate (8.7.5) `‖u‖ ≤ ‖ℓ‖/α`.

The book writes (8.7.2) as `sup_{0 ≠ v ∈ V} a(u,v)/‖v‖ ≥ α ‖u‖`, without absolute values.  The
lemmas `iSup_div_eq_iSup_abs_div` and `iSup_abs_div_eq_opNorm` identify that real supremum with
the operator norm `‖a u‖` of the functional `a u`, which is the form the backbone's
`SesqForm₂.InfSupWith` takes; that is the only real work in this section.  (8.7.3) is printed as
`sup_{u ∈ U} a(u,v) > 0`, but the supremum of a nonzero linear functional is `+∞`, so it is
formalized as `∃ u, 0 < a(u,v)` -- equivalent, by the same sign flip, to the backbone's
`SesqForm₂.IsNondegenerate`.
-/

open scoped InnerProductSpace

namespace AtkinsonHan

/-! ### Real suprema of `f v / ‖v‖`

The book's `sup_{v ≠ 0} f(v)/‖v‖` is the operator norm of `f`.  Over `ℝ` the absolute value may be
dropped because `v ↦ -v` is a bijection of the index set. -/

section Functional

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

private theorem bddAbove_abs_div (f : X →L[ℝ] ℝ) :
    BddAbove (Set.range fun v : {v : X // v ≠ 0} => |f v| / ‖(v : X)‖) := by
  refine ⟨‖f‖, Set.forall_mem_range.2 fun v => ?_⟩
  refine (div_le_iff₀ (norm_pos_iff.mpr v.2)).mpr ?_
  rw [← Real.norm_eq_abs]
  exact f.le_opNorm _

private theorem bddAbove_div (f : X →L[ℝ] ℝ) :
    BddAbove (Set.range fun v : {v : X // v ≠ 0} => f v / ‖(v : X)‖) := by
  refine ⟨‖f‖, Set.forall_mem_range.2 fun v => ?_⟩
  refine (div_le_iff₀ (norm_pos_iff.mpr v.2)).mpr ?_
  calc f (v : X) ≤ |f (v : X)| := le_abs_self _
    _ = ‖f (v : X)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖f‖ * ‖(v : X)‖ := f.le_opNorm _

private theorem abs_div_le_iSup_div (f : X →L[ℝ] ℝ) (v : {v : X // v ≠ 0}) :
    |f v| / ‖(v : X)‖ ≤ ⨆ w : {w : X // w ≠ 0}, f w / ‖(w : X)‖ := by
  have h1 := le_ciSup (bddAbove_div f) v
  have h2 : -(f (v : X)) / ‖(v : X)‖ ≤ ⨆ w : {w : X // w ≠ 0}, f w / ‖(w : X)‖ := by
    have := le_ciSup (bddAbove_div f) (⟨-(v : X), neg_ne_zero.mpr v.2⟩ : {w : X // w ≠ 0})
    rwa [show ((⟨-(v : X), neg_ne_zero.mpr v.2⟩ : {w : X // w ≠ 0}) : X) = -(v : X) from rfl,
      map_neg, norm_neg] at this
  rcases abs_choice (f (v : X)) with h | h
  · rw [h]; exact h1
  · rw [h]; exact h2

private theorem iSup_div_nonneg (f : X →L[ℝ] ℝ) :
    0 ≤ ⨆ w : {w : X // w ≠ 0}, f w / ‖(w : X)‖ := by
  rcases isEmpty_or_nonempty {w : X // w ≠ 0} with _ | hne
  · rw [Real.iSup_of_isEmpty]
  · obtain ⟨v⟩ := hne
    exact le_trans (by positivity) (abs_div_le_iSup_div f v)

/-- Sign symmetry (used once, for (8.7.2) and (9.2.6)): over `ℝ` the supremum of `f(v)/‖v‖` over
`v ≠ 0` is the same as the supremum of `|f(v)|/‖v‖`, because `v ↦ -v` is a bijection of the index
set. -/
theorem iSup_div_eq_iSup_abs_div (f : X →L[ℝ] ℝ) :
    (⨆ v : {v : X // v ≠ 0}, f v / ‖(v : X)‖)
      = ⨆ v : {v : X // v ≠ 0}, |f v| / ‖(v : X)‖ := by
  refine le_antisymm ?_ (Real.iSup_le (abs_div_le_iSup_div f) (iSup_div_nonneg f))
  refine Real.iSup_le (fun v => ?_) (Real.iSup_nonneg fun v => by positivity)
  refine le_trans ?_ (le_ciSup (bddAbove_abs_div f) v)
  gcongr
  exact le_abs_self _

/-- `sup_{v ≠ 0} |f(v)|/‖v‖ = ‖f‖`. -/
theorem iSup_abs_div_eq_opNorm (f : X →L[ℝ] ℝ) :
    (⨆ v : {v : X // v ≠ 0}, |f v| / ‖(v : X)‖) = ‖f‖ := by
  refine le_antisymm (Real.iSup_le ?_ (norm_nonneg _)) ?_
  · intro v
    refine (div_le_iff₀ (norm_pos_iff.mpr v.2)).mpr ?_
    rw [← Real.norm_eq_abs]
    exact f.le_opNorm _
  · refine f.opNorm_le_bound (Real.iSup_nonneg fun v => by positivity) fun v => ?_
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · rw [Real.norm_eq_abs, ← div_le_iff₀ (norm_pos_iff.mpr hv)]
      exact le_ciSup (bddAbove_abs_div f) (⟨v, hv⟩ : {v : X // v ≠ 0})

/-- The book's `sup_{v ≠ 0} f(v)/‖v‖` *is* the operator norm `‖f‖`. -/
theorem iSup_div_eq_opNorm (f : X →L[ℝ] ℝ) :
    (⨆ v : {v : X // v ≠ 0}, f v / ‖(v : X)‖) = ‖f‖ :=
  (iSup_div_eq_iSup_abs_div f).trans (iSup_abs_div_eq_opNorm f)

end Functional

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

theorem isBoundedWith_toCLM (hM : a.IsBoundedWith M) :
    ∀ u v, ‖a.toCLM hM u v‖ ≤ M * ‖u‖ * ‖v‖ := hM

/-- (8.7.2), (9.2.3): the inf–sup condition, with the supremum written as the book writes it,
without absolute values. -/
def InfSup (a : BilinForm₂ U V) (α : ℝ) : Prop :=
  ∀ u, α * ‖u‖ ≤ ⨆ v : {v : V // v ≠ 0}, a u v / ‖(v : V)‖

/-- The book's supremum in (8.7.2) is the operator norm of the functional `a u`. -/
theorem iSup_div_eq_norm_apply (hM : a.IsBoundedWith M) (u : U) :
    (⨆ v : {v : V // v ≠ 0}, a u v / ‖(v : V)‖) = ‖a.toCLM hM u‖ :=
  iSup_div_eq_opNorm (a.toCLM hM u)

/-- (8.7.3), (9.2.4) as printed -- `sup_{u ∈ U} a(u,v) > 0` -- is `∃ u, 0 < a(u,v)`, and by the
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

namespace Ch08

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]

/-- Theorem 8.7.1 (the generalized Lax–Milgram lemma, due to Nečas): a bounded bilinear form on a
pair of real Hilbert spaces satisfying the inf–sup condition (8.7.2) and the nondegeneracy
condition (8.7.3) makes the problem (8.7.4) `a(u,v) = ℓ(v) ∀ v ∈ V` uniquely solvable, with the
stability estimate (8.7.5) `‖u‖_U ≤ ‖ℓ‖_{V'}/α`. -/
theorem thm_8_7_1 [CompleteSpace U] [CompleteSpace V] (a : BilinForm₂ U V)
    (ℓ : StrongDual ℝ V) {M α : ℝ} (hα : 0 < α)
    (h871 : a.IsBoundedWith M)
    (h872 : ∀ u, α * ‖u‖ ≤ ⨆ v : {v : V // v ≠ 0}, a u v / ‖(v : V)‖)
    (h873 : ∀ v, v ≠ 0 → ∃ u, 0 < a u v) :
    (∃! u, ∀ v, a u v = ℓ v) ∧ ∀ u, (∀ v, a u v = ℓ v) → ‖u‖ ≤ ‖ℓ‖ / α := by
  have hinf : SesqForm₂.InfSupWith (𝕜 := ℝ) (U := U) (V := V) (a.toCLM h871) α :=
    (BilinForm₂.infSup_iff_infSupWith h871).mp h872
  have hnd := BilinForm₂.isNondegenerate_toCLM h871 h873
  exact ⟨SesqForm₂.babuska_necas (a.toCLM h871) ℓ hα hinf hnd,
    fun u hu => SesqForm₂.norm_le_of_infSupWith (a.toCLM h871) ℓ hα hinf hu⟩

/-- Exercise 8.7.1: Theorem 8.7.1 contains the Lax–Milgram lemma, Theorem 8.3.4. -/
theorem ex_8_7_1 [CompleteSpace V] (a : BilinForm V) (ℓ : StrongDual ℝ V) {M α : ℝ}
    (hM : a.IsBoundedWith M) (hα : 0 < α) (ha : a.IsEllipticWith α) :
    (∃! u, ∀ v, a u v = ℓ v) ∧ ∀ u, (∀ v, a u v = ℓ v) → ‖u‖ ≤ ‖ℓ‖ / α :=
  thm_8_7_1 a ℓ hα (BilinForm₂.isBoundedWith_of_isBoundedWith hM) (ha.infSup hM)
    (fun v hv => ha.exists_pos hα v hv)

end Ch08

end AtkinsonHan

/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Calculus.ContDiff.Operations`, beside the closure properties of
`ContDiff` and `HasCompactSupport`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Smooth functions constant off a compact set

`IsContDiffConstOffCompact n c` says that the real function `c` on a normed space is of class
`C^n` and agrees with a constant off a compact set. This class of *multipliers* contains the
`C^n` compactly supported functions (`IsContDiffConstOffCompact.of_hasCompactSupport`) and the
constants (`const`), and is closed under sums, products, scalar multiples, finite sums, partial
derivatives (`fderiv_apply`, one order down) and inversion of members bounded below by a
positive constant (`inv`); its members are bounded (`exists_bound`), and so are their
derivatives (`exists_bound_fderiv`). Consequently every derivative of every order of a member
is bounded, which is what makes them multipliers of the Sobolev spaces `H^k` in the
higher-order regularity theory of elliptic equations ([brezis2011functional] §9.6, the
extended coefficients `χ a + (1 − χ) δ` of the proof of Theorem 9.25).
-/

open scoped ContDiff

section ConstOffCompact

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `IsContDiffConstOffCompact n c`: the real function `c` is of class `C^n` on the whole space
and agrees with a constant off a compact set. This is the class of multipliers used in the
higher-order regularity theory: it contains the smooth compactly supported functions, the
constants, the extended coefficients `χ a + (1 − χ) δ`, and it is closed under partial
derivatives, products and inversion of positive members, so that every derivative of every order
of a member is bounded. -/
structure IsContDiffConstOffCompact (n : ℕ) (c : E → ℝ) : Prop where
  /-- A multiplier is `C^n`. -/
  contDiff : ContDiff ℝ n c
  /-- A multiplier agrees with a constant off a compact set. -/
  exists_hasCompactSupport_sub : ∃ κ : ℝ, HasCompactSupport fun x ↦ c x - κ

namespace IsContDiffConstOffCompact

variable {n : ℕ} {c : E → ℝ}

/-- A `C^n` function with compact support is a multiplier. -/
theorem of_hasCompactSupport (hc : ContDiff ℝ n c) (hcs : HasCompactSupport c) :
    IsContDiffConstOffCompact n c :=
  ⟨hc, 0, by simpa using hcs⟩

/-- A constant is a multiplier. -/
theorem const (κ : ℝ) : IsContDiffConstOffCompact n fun _ : E ↦ κ :=
  ⟨contDiff_const, κ, by simp [HasCompactSupport, tsupport]⟩

/-- A multiplier of class `C^n` is one of class `C^m` for `m ≤ n`. -/
theorem of_le {m : ℕ} (h : IsContDiffConstOffCompact n c) (hmn : m ≤ n) :
    IsContDiffConstOffCompact m c :=
  ⟨h.contDiff.of_le (by exact_mod_cast hmn), h.exists_hasCompactSupport_sub⟩

/-- A multiplier is continuous. -/
theorem continuous (h : IsContDiffConstOffCompact n c) : Continuous c := h.contDiff.continuous

/-- A multiplier is bounded. -/
theorem exists_bound (h : IsContDiffConstOffCompact n c) : ∃ C, ∀ x, |c x| ≤ C := by
  obtain ⟨κ, hκ⟩ := h.exists_hasCompactSupport_sub
  obtain ⟨C, hC⟩ := hκ.exists_bound_of_continuous (h.continuous.sub continuous_const)
  refine ⟨C + |κ|, fun x ↦ ?_⟩
  have := hC x
  rw [Real.norm_eq_abs] at this
  calc |c x| = |(c x - κ) + κ| := by ring_nf
    _ ≤ |c x - κ| + |κ| := abs_add_le _ _
    _ ≤ C + |κ| := by linarith

/-- The sum of two multipliers is a multiplier. -/
theorem add {c' : E → ℝ} (h : IsContDiffConstOffCompact n c)
    (h' : IsContDiffConstOffCompact n c') : IsContDiffConstOffCompact n fun x ↦ c x + c' x := by
  obtain ⟨κ, hκ⟩ := h.exists_hasCompactSupport_sub
  obtain ⟨κ', hκ'⟩ := h'.exists_hasCompactSupport_sub
  refine ⟨h.contDiff.add h'.contDiff, κ + κ', ?_⟩
  have e : (fun x ↦ c x + c' x - (κ + κ')) = (fun x ↦ c x - κ) + fun x ↦ c' x - κ' := by
    funext x
    simp only [Pi.add_apply]
    ring
  rw [e]
  exact hκ.add hκ'

/-- The product of two multipliers is a multiplier. -/
theorem mul {c' : E → ℝ} (h : IsContDiffConstOffCompact n c)
    (h' : IsContDiffConstOffCompact n c') : IsContDiffConstOffCompact n fun x ↦ c x * c' x := by
  obtain ⟨κ, hκ⟩ := h.exists_hasCompactSupport_sub
  obtain ⟨κ', hκ'⟩ := h'.exists_hasCompactSupport_sub
  refine ⟨h.contDiff.mul h'.contDiff, κ * κ', ?_⟩
  have h1 : HasCompactSupport fun x ↦ (c x - κ) * c' x := hκ.mul_right
  have h2 : HasCompactSupport fun x ↦ κ * (c' x - κ') := hκ'.mul_left
  have e : (fun x ↦ c x * c' x - κ * κ')
      = (fun x ↦ (c x - κ) * c' x) + fun x ↦ κ * (c' x - κ') := by
    funext x
    simp only [Pi.add_apply]
    ring
  rw [e]
  exact h1.add h2

/-- A scalar multiple of a multiplier is a multiplier. -/
theorem const_mul (h : IsContDiffConstOffCompact n c) (r : ℝ) :
    IsContDiffConstOffCompact n fun x ↦ r * c x :=
  (const r).mul h

/-- The negative of a multiplier is a multiplier. -/
theorem neg (h : IsContDiffConstOffCompact n c) : IsContDiffConstOffCompact n fun x ↦ -c x := by
  have := h.const_mul (-1)
  simpa using this

/-- The difference of two multipliers is a multiplier. -/
theorem sub {c' : E → ℝ} (h : IsContDiffConstOffCompact n c)
    (h' : IsContDiffConstOffCompact n c') : IsContDiffConstOffCompact n fun x ↦ c x - c' x := by
  have := h.add h'.neg
  simpa [sub_eq_add_neg] using this

/-- A finite sum of multipliers is a multiplier. -/
theorem finset_sum {κ : Type*} (s : Finset κ) {c : κ → E → ℝ}
    (h : ∀ i ∈ s, IsContDiffConstOffCompact n (c i)) :
    IsContDiffConstOffCompact n fun x ↦ ∑ i ∈ s, c i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (E := E) (n := n) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

/-- The partial derivative of a multiplier of class `C^{n+1}` is a multiplier of class `C^n`,
with compact support. -/
theorem fderiv_apply (h : IsContDiffConstOffCompact (n + 1) c) (y : E) :
    IsContDiffConstOffCompact n fun x ↦ fderiv ℝ c x y := by
  obtain ⟨κ, hκ⟩ := h.exists_hasCompactSupport_sub
  refine of_hasCompactSupport ?_ ?_
  · exact (h.contDiff.fderiv_right (m := n) (by norm_cast)).clm_apply contDiff_const
  · have := hκ.fderiv_apply (𝕜 := ℝ) y
    have e : (fun x ↦ fderiv ℝ c x y) = fun x ↦ fderiv ℝ (fun x ↦ c x - κ) x y := by
      funext x
      simp only [fderiv_sub_const]
    rw [e]
    exact this

/-- The inverse of a multiplier bounded below by a positive constant is a multiplier. -/
theorem inv (h : IsContDiffConstOffCompact n c) {α : ℝ} (hα : 0 < α) (hc : ∀ x, α ≤ c x) :
    IsContDiffConstOffCompact n fun x ↦ (c x)⁻¹ := by
  obtain ⟨κ, hκ⟩ := h.exists_hasCompactSupport_sub
  have hne : ∀ x, c x ≠ 0 := fun x ↦ (hα.trans_le (hc x)).ne'
  refine ⟨h.contDiff.inv hne, κ⁻¹, ?_⟩
  refine hκ.mono fun x hx ↦ ?_
  simp only [Function.mem_support, ne_eq] at hx ⊢
  intro hcx
  apply hx
  have : c x = κ := by linarith
  rw [this, sub_self]

/-- A multiplier of class `C^{n+1}` has a bounded derivative. -/
theorem exists_bound_fderiv (h : IsContDiffConstOffCompact (n + 1) c) :
    ∃ C, ∀ x, ‖fderiv ℝ c x‖ ≤ C := by
  obtain ⟨κ, hκ⟩ := h.exists_hasCompactSupport_sub
  obtain ⟨C, hC⟩ := (hκ.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    ((h.contDiff.sub contDiff_const).continuous_fderiv (by simp))
  refine ⟨C, fun x ↦ ?_⟩
  have := hC x
  rwa [fderiv_sub_const] at this

end IsContDiffConstOffCompact

end ConstOffCompact

/-! ### Iterated derivatives of compactly supported functions of one variable -/

/-- The iterated derivatives of a compactly supported function have compact support. -/
theorem HasCompactSupport.iteratedDeriv {f : ℝ → ℝ} (hf : HasCompactSupport f) (k : ℕ) :
    HasCompactSupport (iteratedDeriv k f) := by
  induction k with
  | zero => simpa using hf
  | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv

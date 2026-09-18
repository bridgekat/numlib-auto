import Numlib.Variational.EllipticInterval.BoundaryConditions

/-!
# Brezis §8.1: motivation — the model Dirichlet problem and the variational method

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §8.1. The model problem (1) is

  `−u'' + u = f` on `[a, b]`, `u(a) = u(b) = 0`,

for a given `f ∈ C([a, b])`. A *classical solution* is a `C²` function satisfying (1); the
section's provisional *weak solution* is a `C¹` function `u` with

  `∫_a^b u' φ' + ∫_a^b u φ = ∫_a^b f φ` for all `φ ∈ C¹([a, b])` with `φ(a) = φ(b) = 0` (2),

and the variational method has four steps: A (a classical solution is a weak solution: multiply
(1) by `φ` and integrate by parts), B (existence and uniqueness of a weak solution, by
Lax–Milgram in the completion `H_0^1` of the `C¹` functions vanishing at the endpoints), C (the
weak solution is `C²`), D (a `C²` weak solution is a classical solution). The section carries out
Step D and defers the others to §8.2–§8.4; it has no numbered result. The spaces `Cᵏ([a, b])` are
`ContDiffMapIcc hab.le k` of `Numlib/Analysis/Calculus/ContDiffMapIcc.lean`.

## Main definitions

* `IsClassicalSolution hab f u` — `u ∈ C²([a, b])` solves (1): `−u'' + u = f` on `[a, b]` and
  `u(a) = u(b) = 0`.
* `IsWeakSolution hab f u` — `u ∈ C¹([a, b])` satisfies (2).

## Main results

* `dirichlet_stepD` — Step D: if `u ∈ C²([a, b])` with `u(a) = u(b) = 0` satisfies (2) and `f`
  is continuous on `[a, b]`, then `u` is a classical solution.

Where the book's Step D integrates (2) by parts against a `C¹` test function, the proof here
restricts (2) to the smooth test functions `𝓓((a, b), ℝ)` (which are `C¹` and vanish at the
endpoints) and applies the backbone's
`EllipticInterval.isClassicalSolution_of_forall_testFunction` — the general Step D for
`−(α u')' + β u' + γ u = f`, whose proof is the book's: `−(u')' = f − u` in the weak sense on
`(a, b)`, hence a.e. by the fundamental lemma of the calculus of variations, hence everywhere by
continuity. The identity on the open interval `(a, b)` extends to the endpoints by continuity
(`eqOn_Icc_of_ae_eq`).

The definitive weak solution, in `H_0^1`, is §8.4's; the steps in general are Step A
`EllipticInterval.isWeakSolution_of_classical`, Step B Proposition 8.15, Step C
`EllipticInterval.mem_sobolevInterval_two_of_forall_testFunction` and
`EllipticInterval.exists_contDiffMapIcc_of_continuous`, Step D
`EllipticInterval.isClassicalSolution_of_contDiffMapIcc`, all in
`Numlib/Variational/EllipticInterval` and its child `BoundaryConditions`.
-/

open Set MeasureTheory TopologicalSpace intervalIntegral
open scoped Distributions

noncomputable section

namespace Brezis.Chapter08

variable {a b : ℝ}

/-! ### The forgetful map `Cˡ[a, b] → Cᵏ[a, b]`

`Numlib/Analysis/Calculus/ContDiffMapIcc.lean` has the differentiation map `Cᵏ⁺¹ → Cᵏ`
(`ContDiffMapIcc.shift`) but not the inclusion; a `C²` function is read as a `C¹` one through
`ContDiffMapIcc.castLE`, which keeps the first `k` derivatives of the tuple. An upstreaming
candidate for that module. -/

/-- The inclusion `Cˡ[a, b] → Cᵏ[a, b]` for `k ≤ l`: the same function with its first `k`
derivatives. -/
def _root_.ContDiffMapIcc.castLE {hab : a ≤ b} {k l : ℕ} (h : k ≤ l)
    (u : ContDiffMapIcc hab l) : ContDiffMapIcc hab k :=
  ContDiffMapIcc.mk hab (fun j ↦ u.deriv (Fin.castLE (Nat.succ_le_succ h) j)) fun j ↦
    u.hasDerivIcc (Fin.castLE h j)

/-- The derivatives of the inclusion are those of the original. -/
@[simp]
theorem _root_.ContDiffMapIcc.deriv_castLE {hab : a ≤ b} {k l : ℕ} (h : k ≤ l)
    (u : ContDiffMapIcc hab l) (j : Fin (k + 1)) :
    (u.castLE h).deriv j = u.deriv (Fin.castLE (Nat.succ_le_succ h) j) := rfl

/-- The inclusion does not change the function. -/
theorem _root_.ContDiffMapIcc.castLE_extend {hab : a ≤ b} {k l : ℕ} (h : k ≤ l)
    (u : ContDiffMapIcc hab l) : (u.castLE h).extend = u.extend := rfl

/-- The inclusion `C² → C¹` does not change the derivative. -/
theorem _root_.ContDiffMapIcc.castLE_shift_extend {hab : a ≤ b} (u : ContDiffMapIcc hab 2) :
    (u.castLE one_le_two).shift.extend = u.shift.extend := rfl

/-! ### The definitions -/

/-- **Definition (§8.1), classical solution.** A *classical* (or *strong*) solution of the model
problem (1) is a function `u ∈ C²([a, b])` with `−u'' + u = f` on `[a, b]` and `u(a) = u(b) = 0`
(`ContDiffMapIcc.deriv u 2` is `u''` on `[a, b]`). -/
def IsClassicalSolution (hab : a < b) (f : ℝ → ℝ) (u : ContDiffMapIcc hab.le 2) : Prop :=
  (∀ x : Icc a b, -u.deriv 2 x + u x = f x) ∧
    u ⟨a, left_mem_Icc.2 hab.le⟩ = 0 ∧ u ⟨b, right_mem_Icc.2 hab.le⟩ = 0

/-- **Definition (§8.1), weak solution** (the section's provisional one). A function
`u ∈ C¹([a, b])` is a *weak solution* of (1) if it satisfies (2):
`∫_a^b u' φ' + ∫_a^b u φ = ∫_a^b f φ` for every `φ ∈ C¹([a, b])` with `φ(a) = φ(b) = 0`. (The
book notes that (2) makes sense as soon as `u, u' ∈ L¹`, which is the point of §8.2; the
definitive weak solution, in `H_0^1`, is §8.4's — `EllipticInterval.IsWeakSolution`.) -/
def IsWeakSolution (hab : a < b) (f : ℝ → ℝ) (u : ContDiffMapIcc hab.le 1) : Prop :=
  ∀ φ : ContDiffMapIcc hab.le 1, φ ⟨a, left_mem_Icc.2 hab.le⟩ = 0 →
    φ ⟨b, right_mem_Icc.2 hab.le⟩ = 0 →
    (∫ x in a..b, u.shift.extend x * φ.shift.extend x) + ∫ x in a..b, u.extend x * φ.extend x
      = ∫ x in a..b, f x * φ.extend x

/-! ### Step D -/

/-- The second derivative of `u ∈ C²[a, b]` at an interior point is the derivative of `u'`. -/
theorem deriv_shift_extend (hab : a < b) (u : ContDiffMapIcc hab.le 2) {x : ℝ}
    (hx : x ∈ Ioo a b) : deriv u.shift.extend x = u.deriv 2 ⟨x, Ioo_subset_Icc_self hx⟩ :=
  ((u.shift.hasDerivWithinAt_extend ⟨x, Ioo_subset_Icc_self hx⟩).hasDerivAt
    (Icc_mem_nhds hx.1 hx.2)).deriv

/-- A `C²` weak solution satisfies (2) against every smooth test function on `(a, b)`, in the
form `∫_a^b (u' φ' + u φ) = ∫_a^b f φ` over the open interval. -/
theorem integral_eq_of_isWeakSolution (hab : a < b) {f : ℝ → ℝ} (u : ContDiffMapIcc hab.le 2)
    (hu : IsWeakSolution hab f (u.castLE one_le_two)) (φ : 𝓓(Opens.Ioo a b, ℝ)) :
    ∫ x in Ioo a b, (u.shift.extend x * deriv φ x + u.extend x * φ x)
      = ∫ x in Ioo a b, f x * φ x := by
  have hφ1 : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) φ := φ.contDiff.of_le (by simp)
  have hnot : ∀ x, x ∉ Ioo a b → φ x = 0 := fun x hx ↦
    φ.zero_on_compl (by rw [Opens.coe_Ioo]; exact hx)
  have hψa : ContDiffMapIcc.ofContDiff hab.le hφ1 ⟨a, left_mem_Icc.2 hab.le⟩ = 0 := by
    rw [ContDiffMapIcc.coe_ofContDiff]
    exact hnot a (by simp)
  have hψb : ContDiffMapIcc.ofContDiff hab.le hφ1 ⟨b, right_mem_Icc.2 hab.le⟩ = 0 := by
    rw [ContDiffMapIcc.coe_ofContDiff]
    exact hnot b (by simp)
  have e1 : ∀ x ∈ Ioo a b, (ContDiffMapIcc.ofContDiff hab.le hφ1).shift.extend x = deriv φ x :=
    fun x hx ↦ by
      rw [ContDiffMapIcc.extend_of_mem _ (Ioo_subset_Icc_self hx)]
      change (ContDiffMapIcc.ofContDiff hab.le hφ1).deriv 1 ⟨x, Ioo_subset_Icc_self hx⟩ = _
      rw [ContDiffMapIcc.deriv_ofContDiff]
      simp only [Fin.val_one, iteratedDeriv_one]
  have e0 : ∀ x ∈ Ioo a b, (ContDiffMapIcc.ofContDiff hab.le hφ1).extend x = φ x :=
    fun x hx ↦ by
      rw [ContDiffMapIcc.extend_of_mem _ (Ioo_subset_Icc_self hx), ContDiffMapIcc.coe_ofContDiff]
  have h := hu (ContDiffMapIcc.ofContDiff hab.le hφ1) hψa hψb
  have i1 : IntervalIntegrable
      (fun x ↦ u.shift.extend x * (ContDiffMapIcc.ofContDiff hab.le hφ1).shift.extend x)
      volume a b :=
    (u.shift.extend.continuous.mul
      (ContDiffMapIcc.ofContDiff hab.le hφ1).shift.extend.continuous).intervalIntegrable a b
  have i0 : IntervalIntegrable
      (fun x ↦ u.extend x * (ContDiffMapIcc.ofContDiff hab.le hφ1).extend x) volume a b :=
    (u.extend.continuous.mul
      (ContDiffMapIcc.ofContDiff hab.le hφ1).extend.continuous).intervalIntegrable a b
  rw [ContDiffMapIcc.castLE_shift_extend, ContDiffMapIcc.castLE_extend,
    ← intervalIntegral.integral_add i1 i0, integral_of_le hab.le, integral_of_le hab.le,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo] at h
  refine (setIntegral_congr_fun measurableSet_Ioo fun x hx ↦ ?_).trans
    (h.trans (setIntegral_congr_fun measurableSet_Ioo fun x hx ↦ ?_))
  · rw [e1 x hx, e0 x hx]
  · rw [e0 x hx]

/-- **Step D (§8.1).** If `u ∈ C²([a, b])` with `u(a) = u(b) = 0` satisfies (2), i.e. is a weak
solution, and `f` is continuous on `[a, b]`, then `u` is a classical solution of (1): the
equation `−u'' + u = f` holds on `(a, b)` by the general
`EllipticInterval.isClassicalSolution_of_forall_testFunction` (with `α = γ = 1`, `β = 0`), and
at the endpoints by continuity. -/
theorem dirichlet_stepD (hab : a < b) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (u : ContDiffMapIcc hab.le 2) (hua : u ⟨a, left_mem_Icc.2 hab.le⟩ = 0)
    (hub : u ⟨b, right_mem_Icc.2 hab.le⟩ = 0) (hu : IsWeakSolution hab f (u.castLE one_le_two)) :
    IsClassicalSolution hab f u := by
  refine ⟨fun x ↦ ?_, hua, hub⟩
  -- the equation in the interior, from the general Step D
  have hint := EllipticInterval.isClassicalSolution_of_forall_testFunction hab
    (α := fun _ ↦ (1 : ℝ)) (β := fun _ ↦ (0 : ℝ)) (γ := fun _ ↦ (1 : ℝ)) contDiffOn_const
    continuousOn_const continuousOn_const hf u fun φ ↦ by
      simpa only [one_mul, zero_mul, add_zero] using integral_eq_of_isWeakSolution hab u hu φ
  simp only [one_mul, zero_mul, add_zero] at hint
  -- extension to the endpoints by continuity
  have hae : (fun x ↦ -u.shift.shift.extend x + u.extend x) =ᵐ[volume.restrict (Ioo a b)] f := by
    refine (ae_restrict_mem measurableSet_Ioo).mono fun x hx ↦ ?_
    change -u.shift.shift.extend x + u.extend x = f x
    have := hint x hx
    rw [deriv_shift_extend hab u hx] at this
    rw [ContDiffMapIcc.extend_of_mem _ (Ioo_subset_Icc_self hx)]
    exact this
  have hEq := eqOn_Icc_of_ae_eq hab
    (u.shift.shift.extend.continuous.neg.add u.extend.continuous).continuousOn hf hae x.2
  change -u.shift.shift.extend x + u.extend x = f x at hEq
  rw [ContDiffMapIcc.extend_val, ContDiffMapIcc.extend_val] at hEq
  exact hEq

end Brezis.Chapter08

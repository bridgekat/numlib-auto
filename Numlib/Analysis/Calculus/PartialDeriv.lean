/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas`, beside the one-variable iterated
derivative.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Iterated partial derivatives of a function of two real variables

A function of two real variables written curried, `v : ℝ → ℝ → ℝ`, has a partial derivative in
each argument: `HasPartialDerivFst v vx` says that `y ↦ v y t` has derivative `vx x t` at `x` for
every `(x, t)`, and `HasPartialDerivSnd v vt` the same for `s ↦ v x s`. Neither asks for
differentiability of the uncurried function — only the two families of restrictions to the
coordinate lines enter, and that is all the results below use.

`HasPartialDerivs v D` bundles the whole doubly indexed family: `D i j` is `∂ₓ^i ∂ₜ^j v`, with
`D 0 0 = v`, each `D i j` having `D (i + 1) j` as its first partial derivative and `D i (j + 1)`
as its second. It is the hypothesis "`v` is smooth, and here are names for all of its partial
derivatives"; in particular it builds in the symmetry of the mixed partials, since `D (i+1) (j+1)`
is reached from `D i j` either way round.

Two things follow, and they are the point of the interface.

* **Every coordinate slice is `C^∞`**: `HasPartialDerivs.contDiff_fst` and `…_snd` give
  `ContDiff ℝ n` of `y ↦ D i j y t` and of `s ↦ D i j x s` for every `n`, and
  `HasPartialDerivs.iteratedDeriv_fst`, `…_snd` identify the one-variable iterated derivatives of
  those slices with the members of the family, `iteratedDeriv k (fun y => D i j y t) =
  fun y => D (i + k) j y t`. Any one-variable theorem — Taylor's with the Lagrange remainder, a
  difference-quotient bound — therefore applies to a slice with no further work.
* **A pointwise identity between such functions may be differentiated**:
  `HasPartialDerivFst.congr` and `HasPartialDerivSnd.congr` say that two functions with named
  partial derivatives that agree everywhere have partial derivatives that agree everywhere. This
  is how a partial differential equation satisfied by `v` is differentiated into identities
  between the members of `D` (the closure lemmas `HasPartialDerivFst.add`, `.const_mul` and their
  `Snd` companions build the derivative of each side).

The two-variable statements are proved once for the first variable and transported to the second
by `HasPartialDerivs.swap`, which exchanges the arguments of `v` and transposes the family.
-/

open Set

variable {v w vx wx vt wt : ℝ → ℝ → ℝ} {D : ℕ → ℕ → ℝ → ℝ → ℝ}

/-! ### Partial derivatives in one of the two variables -/

/-- **The partial derivative in the first variable**: for every `(x, t)` the restriction
`y ↦ v y t` has derivative `vx x t` at `x`. -/
def HasPartialDerivFst (v vx : ℝ → ℝ → ℝ) : Prop :=
  ∀ x t : ℝ, HasDerivAt (fun y => v y t) (vx x t) x

/-- **The partial derivative in the second variable**: for every `(x, t)` the restriction
`s ↦ v x s` has derivative `vt x t` at `t`. -/
def HasPartialDerivSnd (v vt : ℝ → ℝ → ℝ) : Prop :=
  ∀ x t : ℝ, HasDerivAt (fun s => v x s) (vt x t) t

/-- Exchanging the two arguments turns a partial derivative in the second variable into one in the
first. -/
theorem hasPartialDerivFst_swap_iff :
    HasPartialDerivFst (fun t x => v x t) (fun t x => vt x t) ↔ HasPartialDerivSnd v vt :=
  ⟨fun h x t => h t x, fun h t x => h x t⟩

/-- Exchanging the two arguments turns a partial derivative in the first variable into one in the
second. -/
theorem hasPartialDerivSnd_swap_iff :
    HasPartialDerivSnd (fun t x => v x t) (fun t x => vx x t) ↔ HasPartialDerivFst v vx :=
  ⟨fun h x t => h t x, fun h t x => h x t⟩

/-- A sum of functions has the sum of the first partial derivatives. -/
theorem HasPartialDerivFst.add (hv : HasPartialDerivFst v vx) (hw : HasPartialDerivFst w wx) :
    HasPartialDerivFst (fun x t => v x t + w x t) fun x t => vx x t + wx x t :=
  fun x t => (hv x t).add (hw x t)

/-- A constant multiple of a function has the same multiple of its first partial derivative. -/
theorem HasPartialDerivFst.const_mul (hv : HasPartialDerivFst v vx) (c : ℝ) :
    HasPartialDerivFst (fun x t => c * v x t) fun x t => c * vx x t :=
  fun x t => (hv x t).const_mul c

/-- A sum of functions has the sum of the second partial derivatives. -/
theorem HasPartialDerivSnd.add (hv : HasPartialDerivSnd v vt) (hw : HasPartialDerivSnd w wt) :
    HasPartialDerivSnd (fun x t => v x t + w x t) fun x t => vt x t + wt x t :=
  fun x t => (hv x t).add (hw x t)

/-- A constant multiple of a function has the same multiple of its second partial derivative. -/
theorem HasPartialDerivSnd.const_mul (hv : HasPartialDerivSnd v vt) (c : ℝ) :
    HasPartialDerivSnd (fun x t => c * v x t) fun x t => c * vt x t :=
  fun x t => (hv x t).const_mul c

/-- **A pointwise identity may be differentiated in the first variable**: two functions with named
first partial derivatives that agree everywhere have first partial derivatives that agree
everywhere. -/
theorem HasPartialDerivFst.congr (hv : HasPartialDerivFst v vx) (hw : HasPartialDerivFst w wx)
    (h : ∀ x t, v x t = w x t) (x t : ℝ) : vx x t = wx x t := by
  have hfun : (fun y => v y t) = fun y => w y t := funext fun y => h y t
  exact (hv x t).unique (hfun ▸ hw x t)

/-- **A pointwise identity may be differentiated in the second variable**. -/
theorem HasPartialDerivSnd.congr (hv : HasPartialDerivSnd v vt) (hw : HasPartialDerivSnd w wt)
    (h : ∀ x t, v x t = w x t) (x t : ℝ) : vt x t = wt x t := by
  have hfun : (fun s => v x s) = fun s => w x s := funext fun s => h x s
  exact (hv x t).unique (hfun ▸ hw x t)

/-! ### The whole family of iterated partial derivatives -/

/-- **A smooth function of two real variables together with names for all of its iterated partial
derivatives**: `D i j` is `∂ₓ^i ∂ₜ^j v`. The family is closed under both partial derivatives, so
each `D i j` is smooth along both coordinate directions, and the mixed partials are symmetric by
construction: `D (i + 1) (j + 1)` is the second partial derivative of `D (i + 1) j` as well as the
first partial derivative of `D i (j + 1)`. -/
def HasPartialDerivs (v : ℝ → ℝ → ℝ) (D : ℕ → ℕ → ℝ → ℝ → ℝ) : Prop :=
  D 0 0 = v ∧ (∀ i j, HasPartialDerivFst (D i j) (D (i + 1) j)) ∧
    ∀ i j, HasPartialDerivSnd (D i j) (D i (j + 1))

namespace HasPartialDerivs

variable (h : HasPartialDerivs v D)
include h

/-- The family starts at the function itself. -/
theorem eq_zero_zero : D 0 0 = v := h.1

/-- Each member of the family has the next one as its first partial derivative. -/
theorem hasPartialDerivFst (i j : ℕ) : HasPartialDerivFst (D i j) (D (i + 1) j) := h.2.1 i j

/-- Each member of the family has the next one as its second partial derivative. -/
theorem hasPartialDerivSnd (i j : ℕ) : HasPartialDerivSnd (D i j) (D i (j + 1)) := h.2.2 i j

/-- **Exchanging the two variables** transposes the family of partial derivatives. -/
theorem swap : HasPartialDerivs (fun t x => v x t) fun i j t x => D j i x t :=
  ⟨by rw [← h.eq_zero_zero], fun i j t x => h.hasPartialDerivSnd j i x t,
    fun i j t x => h.hasPartialDerivFst j i x t⟩

/-- Each coordinate slice in the first variable is differentiable. -/
theorem differentiable_fst (i j : ℕ) (t : ℝ) : Differentiable ℝ fun y => D i j y t :=
  fun y => (h.hasPartialDerivFst i j y t).differentiableAt

/-- The one-variable derivative of a slice in the first variable is the next member of the
family. -/
theorem deriv_fst (i j : ℕ) (t : ℝ) : (deriv fun y => D i j y t) = fun y => D (i + 1) j y t :=
  funext fun y => (h.hasPartialDerivFst i j y t).deriv

/-- Each coordinate slice in the second variable is differentiable. -/
theorem differentiable_snd (i j : ℕ) (x : ℝ) : Differentiable ℝ fun s => D i j x s :=
  fun s => (h.hasPartialDerivSnd i j x s).differentiableAt

/-- The one-variable derivative of a slice in the second variable is the next member of the
family. -/
theorem deriv_snd (i j : ℕ) (x : ℝ) : (deriv fun s => D i j x s) = fun s => D i (j + 1) x s :=
  funext fun s => (h.hasPartialDerivSnd i j x s).deriv

/-- **Every coordinate slice in the first variable is `C^n`**, for every `n`. -/
theorem contDiff_fst (n i j : ℕ) (t : ℝ) : ContDiff ℝ n fun y => D i j y t := by
  induction n generalizing i with
  | zero => exact contDiff_zero.2 (h.differentiable_fst i j t).continuous
  | succ n ih =>
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; ring]
    refine contDiff_succ_iff_deriv.2 ⟨h.differentiable_fst i j t, fun hn => ?_, ?_⟩
    · exact absurd hn (by simp)
    · rw [h.deriv_fst]
      exact ih (i + 1)

/-- **Every coordinate slice in the second variable is `C^n`**, for every `n`. -/
theorem contDiff_snd (n i j : ℕ) (x : ℝ) : ContDiff ℝ n fun s => D i j x s :=
  h.swap.contDiff_fst n j i x

/-- **The iterated derivative of a slice in the first variable** is the member of the family with
the first index advanced. -/
theorem iteratedDeriv_fst (k i j : ℕ) (t : ℝ) :
    (iteratedDeriv k fun y => D i j y t) = fun y => D (i + k) j y t := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ', h.deriv_fst, ih (i + 1), show i + 1 + k = i + (k + 1) by omega]

/-- **The iterated derivative of a slice in the second variable** is the member of the family with
the second index advanced. -/
theorem iteratedDeriv_snd (k i j : ℕ) (x : ℝ) :
    (iteratedDeriv k fun s => D i j x s) = fun s => D i (j + k) x s :=
  h.swap.iteratedDeriv_fst k j i x

end HasPartialDerivs

/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Calculus.FDeriv.Symmetric`, whose `ContDiffAt.isSymmSndFDerivAt`
the last theorem here extends to every order.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Iterated derivatives of a smooth function: peeling and symmetry

Two pieces of pure calculus about `iteratedFDeriv ℝ n f` for a `C^∞` function `f`, with no
measure theory in them.

## Commuting an extra derivative past iterated derivatives

Mathlib's `iteratedFDeriv_succ_apply_left` peels the *outermost* derivative off
`iteratedFDeriv ℝ (n + 1) f x m`, and `iteratedFDeriv_succ_apply_right` the innermost one, but at
the *last* index of the tuple `m`. For a smooth function the two may be combined: an extra
directional derivative may be taken either outside or inside the `n` iterated ones
(`ContDiff.fderiv_iteratedFDeriv_apply`), so that the `(n + 1)`-st derivative along `y` is the
`n`-th derivative along `Fin.tail y` of the derivative along `y 0`
(`ContDiff.iteratedFDeriv_succ_apply_left'`, and `ContDiff.iteratedFDeriv_cons` for a tuple
written as `Fin.cons z y`). This is what lets an induction on the order of a derivative peel
directions off the *front* of the tuple, which is the order in which integrating by parts `n` times
moves derivatives from a test function onto the other factor; without it, the weak derivative of
`Numlib/Analysis/Sobolev/WeakDeriv.lean` would relate `∂^n φ (y)` to `∂^n f (y ∘ Fin.rev)`, and the
derivative of a convolution in `Numlib/Analysis/Convolution/Lp.lean` would come out reversed too.

## Symmetry of the iterated derivative

* `ContDiff.iteratedFDeriv_congr_perm`: **the iterated derivative of a `C^∞` function is symmetric
  in its arguments**, which Mathlib has only at order two (`ContDiffAt.isSymmSndFDerivAt`) or, at
  every order, for analytic functions (`ContDiffAt.domDomCongr_iteratedFDeriv`). The vehicle is
  `listFDeriv`, differentiation along the entries of a *list* of directions, along which the
  commutation of two directional derivatives (`ContDiff.fderiv_fderiv_comm`) propagates by an
  induction on `List.Perm`; `ContDiff.listFDeriv_ofFn` identifies it with `iteratedFDeriv`.
-/

open scoped ContDiff

/-! ### Commuting an extra derivative past iterated derivatives -/

section Calculus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {n : ℕ} {x : E}

/-- `iteratedFDeriv_succ_apply_left` with the evaluation at a tuple moved inside the outermost
derivative: the `(n + 1)`-st derivative of `f` along `m` is the derivative along `m 0` of the
`n`-th derivative along `Fin.tail m`. -/
theorem iteratedFDeriv_succ_apply_left_of_differentiableAt
    (h : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) x) (m : Fin (n + 1) → E) :
    iteratedFDeriv ℝ (n + 1) f x m
      = fderiv ℝ (fun z ↦ iteratedFDeriv ℝ n f z (Fin.tail m)) x (m 0) := by
  rw [fderiv_continuousMultilinear_apply_const h, iteratedFDeriv_succ_apply_left]
  rfl

/-- For a smooth function, an extra derivative in the direction `v` may be taken either outside or
inside the `n` iterated derivatives. Iterating this is the symmetry of higher derivatives; only
this one-step form is needed here. -/
theorem ContDiff.fderiv_iteratedFDeriv_apply (hf : ContDiff ℝ ∞ f) (n : ℕ) (m : Fin n → E)
    (v x : E) :
    fderiv ℝ (fun z ↦ iteratedFDeriv ℝ n f z m) x v
      = iteratedFDeriv ℝ n (fun z ↦ fderiv ℝ f z v) x m := by
  induction n generalizing x with
  | zero => simp [iteratedFDeriv_zero_apply]
  | succ n ih =>
    have hd : ∀ g : E → F, ContDiff ℝ ∞ g → ∀ z, DifferentiableAt ℝ (iteratedFDeriv ℝ n g) z :=
      fun g hg z ↦
        (hg.iteratedFDeriv_right (m := 1) (i := n) (by simp)).differentiable one_ne_zero z
    have hG : ContDiff ℝ ∞ fun z ↦ iteratedFDeriv ℝ n f z (Fin.tail m) :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n ↦ E) F (Fin.tail m)).contDiff.comp
        (hf.iteratedFDeriv_right (m := ∞) (i := n) (by simp))
    have hψ : ContDiff ℝ ∞ fun z ↦ fderiv ℝ f z v :=
      (hf.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
    have hGd : Differentiable ℝ (fderiv ℝ fun z ↦ iteratedFDeriv ℝ n f z (Fin.tail m)) :=
      (hG.fderiv_right (m := ∞) le_rfl).differentiable (by simp)
    have hIH : (fun z ↦ iteratedFDeriv ℝ n (fun w ↦ fderiv ℝ f w v) z (Fin.tail m))
        = fun z ↦ fderiv ℝ (fun w ↦ iteratedFDeriv ℝ n f w (Fin.tail m)) z v :=
      funext fun z ↦ (ih _ z).symm
    have h1 : (fun z ↦ iteratedFDeriv ℝ (n + 1) f z m)
        = fun z ↦ fderiv ℝ (fun w ↦ iteratedFDeriv ℝ n f w (Fin.tail m)) z (m 0) :=
      funext fun z ↦ iteratedFDeriv_succ_apply_left_of_differentiableAt (hd f hf z) m
    rw [h1, iteratedFDeriv_succ_apply_left_of_differentiableAt (hd _ hψ x) m, hIH,
      fderiv_clm_apply (hGd x) (differentiableAt_const _),
      fderiv_clm_apply (hGd x) (differentiableAt_const _)]
    simp only [add_apply, ContinuousLinearMap.comp_apply, fderiv_fun_const, Pi.zero_apply,
      zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply]
    exact (ContDiffAt.isSymmSndFDerivAt (x := x) hG.contDiffAt (by simp)).eq _ _

/-- For a smooth function, the `(n + 1)`-st derivative along `y` is the `n`-th derivative along
`Fin.tail y` of the derivative along `y 0`. Contrast `iteratedFDeriv_succ_apply_left`, which peels
off the *outermost* derivative, and `iteratedFDeriv_succ_apply_right`, which peels off the
innermost one but at the *last* index of the tuple. -/
theorem ContDiff.iteratedFDeriv_succ_apply_left' (hf : ContDiff ℝ ∞ f) (n : ℕ)
    (y : Fin (n + 1) → E) (x : E) :
    iteratedFDeriv ℝ (n + 1) f x y
      = iteratedFDeriv ℝ n (fun z ↦ fderiv ℝ f z (y 0)) x (Fin.tail y) := by
  rw [← hf.fderiv_iteratedFDeriv_apply n (Fin.tail y) (y 0) x,
    iteratedFDeriv_succ_apply_left_of_differentiableAt
      ((hf.iteratedFDeriv_right (m := 1) (i := n) (by simp)).differentiable one_ne_zero x) y]

/-- `ContDiff.iteratedFDeriv_succ_apply_left'` with the tuple written as a `Fin.cons`: for a smooth
function, differentiating `n + 1` times along `z :: y` is differentiating `n` times along `y` the
directional derivative in the direction `z`. This is the identity that splits a weak derivative
along a tuple of length `n + 1` into one of length `n` and one of length `1`; see
`HasWeakIteratedLineDerivOn.cons`. -/
theorem ContDiff.iteratedFDeriv_cons (hf : ContDiff ℝ ∞ f) (z : E) (y : Fin n → E) (x : E) :
    iteratedFDeriv ℝ (n + 1) f x (Fin.cons z y)
      = iteratedFDeriv ℝ n (fun t ↦ fderiv ℝ f t z) x y := by
  rw [hf.iteratedFDeriv_succ_apply_left' n (Fin.cons z y) x]
  simp

end Calculus

/-! ### Symmetry of the iterated derivative of a smooth function -/

section Symmetry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}

/-- Differentiating `f` successively along the entries of a list of directions, the head of the
list *innermost*: `listFDeriv [v₁, …, vₙ] f = ∂_{vₙ} ⋯ ∂_{v₁} f`.

Indexing by a list rather than by a tuple is what makes `listFDeriv_congr_perm` an induction on
`List.Perm`, whose `swap` constructor is exactly the transposition of the two innermost
derivatives; `ContDiff.listFDeriv_ofFn` identifies this with `iteratedFDeriv`. -/
noncomputable def listFDeriv (l : List E) (f : E → F) : E → F :=
  l.foldl (fun g v ↦ fun z ↦ fderiv ℝ g z v) f

/-- Differentiating along no directions at all leaves the function alone. -/
@[simp]
theorem listFDeriv_nil (f : E → F) : listFDeriv [] f = f := rfl

/-- Peeling the head of the list off `listFDeriv` takes the derivative along it first. -/
theorem listFDeriv_cons (v : E) (l : List E) (f : E → F) :
    listFDeriv (v :: l) f = listFDeriv l (fun z ↦ fderiv ℝ f z v) := rfl

/-- The derivative of a smooth function in a fixed direction is smooth. -/
theorem ContDiff.fderiv_apply_right (hf : ContDiff ℝ ∞ f) (v : E) :
    ContDiff ℝ ∞ fun z ↦ fderiv ℝ f z v :=
  (hf.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

/-- Differentiating a smooth function along the entries of `List.ofFn y` is its `n`-th derivative
evaluated at the tuple `y`. Each step is `ContDiff.iteratedFDeriv_succ_apply_left'`, which moves one
derivative from the outside of the iterated derivative to the inside. -/
theorem ContDiff.listFDeriv_ofFn (hf : ContDiff ℝ ∞ f) {n : ℕ} (y : Fin n → E) (x : E) :
    listFDeriv (List.ofFn y) f x = iteratedFDeriv ℝ n f x y := by
  induction n generalizing f with
  | zero => simp [iteratedFDeriv_zero_apply]
  | succ n ih =>
    rw [List.ofFn_succ, listFDeriv_cons, ih (hf.fderiv_apply_right (y 0)),
      hf.iteratedFDeriv_succ_apply_left' n y x]
    rfl

/-- **Two directional derivatives of a smooth function commute.** This is the symmetry of the
second derivative, in the form in which `listFDeriv_congr_perm` consumes it: an equality of
functions rather than of values, so that it may be applied under a further derivative. -/
theorem ContDiff.fderiv_fderiv_comm (hf : ContDiff ℝ ∞ f) (v w : E) :
    (fun z ↦ fderiv ℝ (fun y ↦ fderiv ℝ f y v) z w)
      = fun z ↦ fderiv ℝ (fun y ↦ fderiv ℝ f y w) z v := by
  funext x
  have h1 : (fun z ↦ iteratedFDeriv ℝ 1 f z ![v]) = fun z ↦ fderiv ℝ f z v := by
    funext z; rw [iteratedFDeriv_one_apply]; simp
  have h2 := hf.fderiv_iteratedFDeriv_apply 1 ![v] w x
  rw [h1, iteratedFDeriv_one_apply] at h2
  simpa using h2

/-- **Differentiating a smooth function along a list of directions does not depend on the order of
the list.** The induction is on `List.Perm`: its `swap` constructor is the transposition of the two
innermost derivatives, which is `ContDiff.fderiv_fderiv_comm`, and its `cons` constructor peels one
derivative off and applies the induction hypothesis to the differentiated function, which is smooth
again. -/
theorem listFDeriv_congr_perm {l₁ l₂ : List E} (h : l₁.Perm l₂) {f : E → F}
    (hf : ContDiff ℝ ∞ f) : listFDeriv l₁ f = listFDeriv l₂ f := by
  induction h generalizing f with
  | nil => rfl
  | cons a _ ih => rw [listFDeriv_cons, listFDeriv_cons, ih (hf.fderiv_apply_right a)]
  | swap a b l =>
    rw [listFDeriv_cons, listFDeriv_cons, listFDeriv_cons, listFDeriv_cons,
      hf.fderiv_fderiv_comm b a]
  | trans _ _ ih₁ ih₂ => rw [ih₁ hf, ih₂ hf]

/-- **The iterated derivative of a `C^∞` function is symmetric in its arguments**: it takes the same
value at two tuples of directions that are permutations of each other.

Mathlib has this for order two (`ContDiffAt.isSymmSndFDerivAt`) and, for any order, for analytic
functions (`ContDiffAt.domDomCongr_iteratedFDeriv`, which asks for `ω`-smoothness); this is the
`C^∞` statement of any order, obtained by transporting the commutation of two directional
derivatives along a `List.Perm`. The two tuples are allowed to have different lengths — the
hypothesis forces them to be equal — so that it applies to a pair of tuples whose lengths agree only
propositionally, such as `Fin n` and `Fin (∑ i, α i)`. -/
theorem ContDiff.iteratedFDeriv_congr_perm (hf : ContDiff ℝ ∞ f) {n₁ n₂ : ℕ}
    {y₁ : Fin n₁ → E} {y₂ : Fin n₂ → E} (h : (List.ofFn y₁).Perm (List.ofFn y₂)) (x : E) :
    iteratedFDeriv ℝ n₁ f x y₁ = iteratedFDeriv ℝ n₂ f x y₂ := by
  rw [← hf.listFDeriv_ofFn y₁ x, ← hf.listFDeriv_ofFn y₂ x, listFDeriv_congr_perm h hf]

end Symmetry

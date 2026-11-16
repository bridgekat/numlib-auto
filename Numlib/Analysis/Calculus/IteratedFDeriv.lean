/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

This module proves two facts of calculus about the iterated Fréchet derivative $D^n f$
(`iteratedFDeriv ℝ n f`) of a $C^\infty$ function $f : E \to F$ between real normed spaces. First,
an extra directional derivative can be taken either outside or inside the $n$ iterated ones. So the
$(n + 1)$-st derivative along $(y_0, \dots, y_n)$ is the $n$-th derivative along $(y_1, \dots, y_n)$
of the derivative along $y_0$. Second, $D^n f(x)$ is symmetric in its $n$ arguments, at every order
$n$. Mathlib has the symmetry only at order two (`ContDiffAt.isSymmSndFDerivAt`) or, at every order,
for analytic functions (`ContDiffAt.domDomCongr_iteratedFDeriv`).

## Main definitions

* `listFDeriv`: the derivative of $f$ along the entries of a list of directions, the head of the
  list innermost.

## Main results

* `ContDiff.fderiv_iteratedFDeriv_apply`: for a smooth $f$, $\partial_v (D^n f(\cdot)[m]) =
  D^n(\partial_v f)(\cdot)[m]$.
* `ContDiff.iteratedFDeriv_succ_apply_left'`, `ContDiff.iteratedFDeriv_cons`: $D^{n+1} f(x)[y_0,
  y_1, \dots, y_n] = D^n(\partial_{y_0} f)(x)[y_1, \dots, y_n]$.
* `ContDiff.fderiv_fderiv_comm`: two directional derivatives of a smooth function commute.
* `ContDiff.iteratedFDeriv_congr_perm`: the iterated derivative of a $C^\infty$ function takes the
  same value at two tuples of directions that are permutations of each other.

## Proof outline

The symmetry is proved with `listFDeriv`. The commutation of two directional derivatives
(`ContDiff.fderiv_fderiv_comm`) propagates along a permutation of the list by induction on
`List.Perm`, and `ContDiff.listFDeriv_ofFn` identifies `listFDeriv` with `iteratedFDeriv`.

## Implementation notes

* Mathlib's `iteratedFDeriv_succ_apply_left` peels off the outermost derivative of
  $D^{n+1} f(x)[m]$, and `iteratedFDeriv_succ_apply_right` peels off the innermost one, but at the
  last index of the tuple $m$. For a smooth function, `ContDiff.iteratedFDeriv_succ_apply_left'`
  combines the two: it peels the innermost derivative off the front of the tuple. An induction on
  the order of a derivative can then remove directions from the front of the tuple. This is the
  order in which $n$ integrations by parts move derivatives from a test function to the other
  factor. Without it, the weak derivative of `Numlib.Analysis.Sobolev.WeakDeriv` would relate
  $\partial^n \varphi(y)$ to $\partial^n f$ along the reversed tuple, and the derivative of a
  convolution in `Numlib.Analysis.Convolution.Lp` would also come out reversed.
-/

open scoped ContDiff

/-! ### Commuting an extra derivative past iterated derivatives -/

section Calculus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {n : ℕ} {x : E}

/-- If $D^n f$ is differentiable at $x$, then for every $m = (m_0, \dots, m_n) \in E^{n+1}$
$$D^{n+1} f(x)[m] = D\big(z \mapsto D^n f(z)[m_1, \dots, m_n]\big)(x)[m_0].$$

This is `iteratedFDeriv_succ_apply_left` with the evaluation at the tuple moved inside the
outermost derivative. -/
theorem iteratedFDeriv_succ_apply_left_of_differentiableAt
    (h : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) x) (m : Fin (n + 1) → E) :
    iteratedFDeriv ℝ (n + 1) f x m
      = fderiv ℝ (fun z ↦ iteratedFDeriv ℝ n f z (Fin.tail m)) x (m 0) :=
  h.iteratedFDeriv_succ_apply_left'

/-- For a $C^\infty$ function $f$, an extra derivative in the direction $v$ can be taken either
outside or inside the $n$ iterated derivatives: for all $m \in E^n$ and $v, x \in E$,
$$D\big(z \mapsto D^n f(z)[m]\big)(x)[v] = D^n\big(z \mapsto Df(z)[v]\big)(x)[m].$$
-/
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

/-- For a $C^\infty$ function $f$, the $(n + 1)$-st derivative along $y = (y_0, \dots, y_n)$ is the
$n$-th derivative along $(y_1, \dots, y_n)$ of the derivative in the direction $y_0$:
$$D^{n+1} f(x)[y_0, \dots, y_n] = D^n\big(z \mapsto Df(z)[y_0]\big)(x)[y_1, \dots, y_n].$$

Compare `iteratedFDeriv_succ_apply_left`, which peels off the outermost derivative, and
`iteratedFDeriv_succ_apply_right`, which peels off the innermost one but at the last index of
the tuple. -/
theorem ContDiff.iteratedFDeriv_succ_apply_left' (hf : ContDiff ℝ ∞ f) (n : ℕ)
    (y : Fin (n + 1) → E) (x : E) :
    iteratedFDeriv ℝ (n + 1) f x y
      = iteratedFDeriv ℝ n (fun z ↦ fderiv ℝ f z (y 0)) x (Fin.tail y) := by
  rw [← hf.fderiv_iteratedFDeriv_apply n (Fin.tail y) (y 0) x,
    iteratedFDeriv_succ_apply_left_of_differentiableAt
      ((hf.iteratedFDeriv_right (m := 1) (i := n) (by simp)).differentiable one_ne_zero x) y]

/-- For a $C^\infty$ function $f$, differentiating $n + 1$ times along the tuple
$(z, y_1, \dots, y_n)$ is differentiating $n$ times along $(y_1, \dots, y_n)$ the derivative in
the direction $z$:
$$D^{n+1} f(x)[z, y_1, \dots, y_n] = D^n\big(t \mapsto Df(t)[z]\big)(x)[y_1, \dots, y_n].$$

This is `ContDiff.iteratedFDeriv_succ_apply_left'` with the tuple written as `Fin.cons z y`. It
splits a weak derivative along a tuple of length $n + 1$ into one of length $n$ and one of
length $1$; see `HasWeakIteratedLineDerivOn.cons`. -/
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

/-- The derivative of $f$ along the entries of a list of directions, the head of the list innermost:
$$\partial_{[v_1, \dots, v_n]} f = \partial_{v_n} \cdots \partial_{v_1} f,$$
where $\partial_v g(z) = Dg(z)[v]$. Below, $\partial_l f$ denotes `listFDeriv l f`.

The index is a list and not a tuple, so that `listFDeriv_congr_perm` is an induction on
`List.Perm`, whose `swap` constructor is the transposition of the two innermost derivatives.
`ContDiff.listFDeriv_ofFn` identifies `listFDeriv` with `iteratedFDeriv`. -/
noncomputable def listFDeriv (l : List E) (f : E → F) : E → F :=
  l.foldl (fun g v ↦ fun z ↦ fderiv ℝ g z v) f

/-- The derivative along the empty list of directions is $f$ itself. -/
@[simp]
theorem listFDeriv_nil (f : E → F) : listFDeriv [] f = f := rfl

/-- The derivative along $v :: l$ is the derivative along $l$ of $\partial_v f$: the head direction
is taken first. -/
theorem listFDeriv_cons (v : E) (l : List E) (f : E → F) :
    listFDeriv (v :: l) f = listFDeriv l (fun z ↦ fderiv ℝ f z v) := rfl

/-- If $f$ is $C^\infty$, then the directional derivative $z \mapsto Df(z)[v]$ is $C^\infty$ for
every $v \in E$. -/
theorem ContDiff.fderiv_apply_right (hf : ContDiff ℝ ∞ f) (v : E) :
    ContDiff ℝ ∞ fun z ↦ fderiv ℝ f z v :=
  (hf.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

/-- For a $C^\infty$ function $f$ and $y \in E^n$, the derivative along the list
$[y_0, \dots, y_{n-1}]$ is the $n$-th derivative evaluated at $y$:
$\partial_{[y_0, \dots, y_{n-1}]} f(x) = D^n f(x)[y]$.

Each step is `ContDiff.iteratedFDeriv_succ_apply_left'`, which moves one derivative from the
outside of the iterated derivative to the inside. -/
theorem ContDiff.listFDeriv_ofFn (hf : ContDiff ℝ ∞ f) {n : ℕ} (y : Fin n → E) (x : E) :
    listFDeriv (List.ofFn y) f x = iteratedFDeriv ℝ n f x y := by
  induction n generalizing f with
  | zero => simp [iteratedFDeriv_zero_apply]
  | succ n ih =>
    rw [List.ofFn_succ, listFDeriv_cons, ih (hf.fderiv_apply_right (y 0)),
      hf.iteratedFDeriv_succ_apply_left' n y x]
    rfl

/-- **Two directional derivatives of a smooth function commute.** For a $C^\infty$ function $f$ and
$v, w \in E$, $\partial_w \partial_v f = \partial_v \partial_w f$ as functions on $E$.

This is the symmetry of the second derivative, stated as an equality of functions and not of
values, so that it can be used under a further derivative, as `listFDeriv_congr_perm` uses it. -/
theorem ContDiff.fderiv_fderiv_comm (hf : ContDiff ℝ ∞ f) (v w : E) :
    (fun z ↦ fderiv ℝ (fun y ↦ fderiv ℝ f y v) z w)
      = fun z ↦ fderiv ℝ (fun y ↦ fderiv ℝ f y w) z v := by
  funext x
  have h1 : (fun z ↦ iteratedFDeriv ℝ 1 f z ![v]) = fun z ↦ fderiv ℝ f z v := by
    funext z; rw [iteratedFDeriv_one_apply]; simp
  have h2 := hf.fderiv_iteratedFDeriv_apply 1 ![v] w x
  rw [h1, iteratedFDeriv_one_apply] at h2
  simpa using h2

/-- **The derivative of a smooth function along a list of directions does not depend on the order of
the list.** If $f$ is $C^\infty$ and the list $l_2$ is a permutation of $l_1$, then
$\partial_{l_1} f = \partial_{l_2} f$, where $\partial_l f$ is `listFDeriv l f`.

The induction is on `List.Perm`. Its `swap` constructor is the transposition of the two
innermost derivatives, which is `ContDiff.fderiv_fderiv_comm`. Its `cons` constructor peels one
derivative off and applies the induction hypothesis to the differentiated function, which is
smooth again. -/
theorem listFDeriv_congr_perm {l₁ l₂ : List E} (h : l₁.Perm l₂) {f : E → F}
    (hf : ContDiff ℝ ∞ f) : listFDeriv l₁ f = listFDeriv l₂ f := by
  induction h generalizing f with
  | nil => rfl
  | cons a _ ih => rw [listFDeriv_cons, listFDeriv_cons, ih (hf.fderiv_apply_right a)]
  | swap a b l =>
    rw [listFDeriv_cons, listFDeriv_cons, listFDeriv_cons, listFDeriv_cons,
      hf.fderiv_fderiv_comm b a]
  | trans _ _ ih₁ ih₂ => rw [ih₁ hf, ih₂ hf]

/-- **The iterated derivative of a $C^\infty$ function is symmetric in its arguments.** Let $f$ be
$C^\infty$, and let $y_1 \in E^{n_1}$ and $y_2 \in E^{n_2}$ be such that the list of entries of
$y_2$ is a permutation of that of $y_1$. Then for every $x \in E$
$$D^{n_1} f(x)[y_1] = D^{n_2} f(x)[y_2].$$

Mathlib has this at order two (`ContDiffAt.isSymmSndFDerivAt`) and, at every order, for analytic
functions (`ContDiffAt.domDomCongr_iteratedFDeriv`). This is the statement for $C^\infty$
functions at every order. The two tuples can have different lengths in the statement; the
hypothesis forces $n_1 = n_2$. So the theorem applies to two tuples whose lengths are equal only
by a proof, such as tuples indexed by `Fin n` and by `Fin (∑ i, α i)`. -/
theorem ContDiff.iteratedFDeriv_congr_perm (hf : ContDiff ℝ ∞ f) {n₁ n₂ : ℕ}
    {y₁ : Fin n₁ → E} {y₂ : Fin n₂ → E} (h : (List.ofFn y₁).Perm (List.ofFn y₂)) (x : E) :
    iteratedFDeriv ℝ n₁ f x y₁ = iteratedFDeriv ℝ n₂ f x y₂ := by
  rw [← hf.listFDeriv_ofFn y₁ x, ← hf.listFDeriv_ofFn y₂ x, listFDeriv_congr_perm h hf]

end Symmetry

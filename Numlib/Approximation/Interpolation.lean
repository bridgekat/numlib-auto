/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Topology.TietzeExtension
import Numlib.Analysis.Calculus.RootMultiplicity
import Numlib.Analysis.SpecialFunctions.SineSum
import Numlib.Approximation.Partition
import Numlib.Approximation.Unisolvent

/-!
# Interpolation on continuous function spaces

This file studies three interpolation operators on spaces of continuous functions: Lagrange
interpolation at $n + 1$ distinct nodes, piecewise polynomial interpolation on a partition of an
interval, and trigonometric interpolation at the equispaced nodes of a period. For distinct nodes
$x_0, \dots, x_n$ in a compact set $X \subseteq \mathbb{R}$, the Lagrange basis functions $\ell_i$
give the interpolation operator $\Pi_n f = \sum_i f(x_i)\, \ell_i$, a bounded projection of $C(X)$
onto the polynomials of degree at most $n$. For $f$ of class $C^{n+1}$, the error has the classical
form
$$f(t) - \Pi_n f(t) = \frac{f^{(n+1)}(\xi)}{(n + 1)!} \prod_{i=0}^{n} (t - x_i)$$
for some $\xi$ in the interval, a consequence of the generalized Rolle theorem. The operator norm
$\|\Pi_n\|$ is the **Lebesgue constant**, the maximum of the Lebesgue function
$t \mapsto \sum_i |\ell_i(t)|$. It grows at least exponentially for equispaced nodes and at most
logarithmically for the Chebyshev nodes. The material is [han2009theoretical], §3.2, and
[kress1998numerical], §8.1 and §8.3.

Piecewise interpolation of degree $m$ on a partition $a = x_0 < \dots < x_{n+1} = b$ interpolates
$f$ on each panel $[x_j, x_{j+1}]$ at $m + 1$ nodes that include the two endpoints. Its error is
bounded by $(1 + \Lambda)\, \omega(f, h)$, where $\Lambda$ bounds the local Lebesgue constants of
the panels, $\omega(f, \delta)$ is the modulus of continuity of $f$, and $h$ is the mesh size; for
smooth $f$ the error formula gives the order $h^{m+1}$. For $m = 1$ the operator has norm one, and
its error for $f \in C^2$ is at most $h^2 \|f''\|/8$.

## Main definitions

* `Lagrange.basisCM`: the Lagrange basis functions $\ell_i$ as continuous functions on $X$.
* `Lagrange.interpolateCLM`: the Lagrange interpolation operator $\Pi_n$ on $C(X)$.
* `ContinuousMap.modulusOfContinuity`: the modulus of continuity $\omega(f, \delta)$.
* `piecewiseLinearInterpCLM`: piecewise-linear interpolation on a partition of $[a, b]$.
* `IsPanelNodes`: a system of $m + 1$ interpolation nodes on each panel of a partition, with the
  endpoints of the panel among them.
* `piecewisePolyInterpCLM`: piecewise polynomial interpolation of degree $m$.
* `IsPanelLebesgueBound`: a uniform bound for the local Lebesgue constants of the panels.
* `trigInterpCLM`: trigonometric interpolation of degree $n$ at the $2n + 1$ equispaced nodes of a
  period.
* `Lagrange.chebNode`: the Chebyshev nodes $\cos((2j + 1)\pi/(2(n + 1)))$.

## Main results

* `exists_iteratedDeriv_eq_zero_of_forall_eq_zero`: the generalized Rolle theorem.
* `Lagrange.exists_sub_interpolate_eq`: the error formula of Lagrange interpolation.
* `Lagrange.isUnisolvent_polyLE`: Lagrange interpolation is unisolvent.
* `Lagrange.norm_interpolateCLM`: the norm of the interpolation operator is the supremum of the
  Lebesgue function.
* `ContinuousMap.tendsto_modulusOfContinuity`: on a compact space, $\omega(f, \delta) \to 0$ as
  $\delta \to 0$.
* `norm_piecewiseLinearInterpCLM`: piecewise-linear interpolation has norm one.
* `norm_sub_piecewiseLinearInterpCLM_le`: the error of piecewise-linear interpolation of a $C^2$
  function is at most $h^2 \|f''\|/8$.
* `piecewisePolyInterpCLM_apply_of_mem`: on each panel, the piecewise polynomial interpolant is the
  Lagrange interpolant at the nodes of that panel.
* `exists_isPanelLebesgueBound_of_affine`: for nodes at fixed fractions of the panels, one constant
  bounds the local Lebesgue constants of every mesh.
* `norm_sub_piecewisePolyInterpCLM_le`: the error bound $W M/(m + 1)!$ of piecewise polynomial
  interpolation.
* `tendsto_piecewisePolyInterpCLM`: piecewise polynomial interpolation converges uniformly for every
  continuous function.
* `isUnisolvent_trigPolyLE`: trigonometric interpolation at $2n + 1$ distinct nodes of a period is
  unisolvent.
* `Lagrange.norm_interpolateCLM_chebyshev_le`: the Lebesgue constant of the Chebyshev nodes is at
  most $2 + (2/\pi) \log(2n + 2)$.
* `Lagrange.two_pow_div_le_sum_abs_eval_basis_equispaced`: the Lebesgue function of $n + 1$
  equispaced nodes is at least $2^n/(8n^2)$ at the midpoint of the first panel.

## Notation

* $\ell_i$: the Lagrange basis polynomial of the node $x_i$, `Lagrange.basis`.
* $\omega(f, \delta)$: the modulus of continuity, `ContinuousMap.modulusOfContinuity`.

## Implementation notes

* The interpolation operators are bounded linear operators on $C(X)$, written as finite sums of
  evaluation functionals times fixed continuous functions. Linearity, boundedness and continuity are
  then immediate.
* The piecewise interpolation operators are written as the value at the first breakpoint plus a sum
  of clamped increments over the panels, so that nothing has to be glued. The local descriptions
  `piecewiseLinearInterpCLM_apply_of_mem` and `piecewisePolyInterpCLM_apply_of_mem` give the
  interpolant on one panel.
* The breakpoints and the nodes of a partition are given as sequences indexed by `ℕ`, of which only
  the first terms are used, so that the index arithmetic of the panels stays in `ℕ`.
* Functions in $C([a, b])$ carry no derivative. The error bounds for smooth functions take a smooth
  function $\mathbb{R} \to \mathbb{R}$ that agrees with $f$ on $[a, b]$.
* Trigonometric interpolation has no formula for its cardinal basis here. The operator is built from
  unisolvence, which follows from the Haar condition `card_le_two_mul_of_forall_trigFun_eq_zero` of
  `Numlib.Approximation.Chebyshev` (the substitution $z = e^{2\pi i x/T}$ turns a trigonometric
  polynomial into an algebraic one) and the dimension count `finrank_trigPolyLE`.
* Lagrange interpolation is also an instance of the abstract interpolation problem of
  `Numlib.Approximation.Unisolvent`: `Lagrange.interpCLM_isUnisolvent_polyLE` identifies
  `Lagrange.interpolateCLM` with the interpolation projection of that problem.
* Rivlin's sharp bound $\|\Pi_n\| \le (2/\pi) \log(n + 1) + 1$ for the Chebyshev nodes is not
  proved. The bound that is proved has the same factor $2/\pi$ and a larger additive constant; see
  `Lagrange.norm_interpolateCLM_chebyshev_le`.
-/

open scoped Polynomial

namespace Polynomial

/-- The iterated formal derivative is additive: $(P + Q)^{(k)} = P^{(k)} + Q^{(k)}$ for polynomials
$P$ and $Q$ over a commutative ring. -/
theorem iterate_derivative_add {R : Type*} [CommRing R] (k : ℕ) (P Q : R[X]) :
    Polynomial.derivative^[k] (P + Q)
      = Polynomial.derivative^[k] P + Polynomial.derivative^[k] Q := by
  induction k generalizing P Q with
  | zero => simp
  | succ k ih =>
    simp only [Function.iterate_succ_apply, Polynomial.derivative_add]
    exact ih _ _

end Polynomial

/-! ### The generalized Rolle theorem -/

/-- If $F_0$ vanishes at $n + 1$ increasing points of $[a, b]$ and each $F_{k+1}$ is the derivative
of $F_k$ on $(a, b)$, then $F_n$ vanishes at a point between the first and the last of these
points. -/
private theorem exists_eq_zero_aux {a b : ℝ} :
    ∀ (n : ℕ) (F : ℕ → ℝ → ℝ),
      (∀ k < n, ContinuousOn (F k) (Set.Icc a b)) →
      (∀ k < n, ∀ t ∈ Set.Ioo a b, HasDerivAt (F k) (F (k + 1) t) t) →
      ∀ y : Fin (n + 1) → ℝ, StrictMono y → (∀ i, y i ∈ Set.Icc a b) →
      (∀ i, F 0 (y i) = 0) →
      ∃ c ∈ Set.Icc (y 0) (y (Fin.last n)), F n c = 0 := by
  intro n
  induction n with
  | zero =>
    intro F _ _ y _ _ hzero
    exact ⟨y 0, ⟨le_rfl, le_rfl⟩, hzero 0⟩
  | succ n ih =>
    intro F hcont hderiv y hmono hmem hzero
    have hrolle : ∀ i : Fin (n + 1), ∃ c ∈ Set.Ioo (y i.castSucc) (y i.succ), F 1 c = 0 := by
      intro i
      refine exists_hasDerivAt_eq_zero (f := F 0) (hmono (Fin.castSucc_lt_succ (i := i)))
        ?_ ?_ ?_
      · exact (hcont 0 (Nat.succ_pos n)).mono
          (Set.Icc_subset_Icc (hmem i.castSucc).1 (hmem i.succ).2)
      · rw [hzero, hzero]
      · exact fun t htt => hderiv 0 (Nat.succ_pos n) t
          ⟨lt_of_le_of_lt (hmem i.castSucc).1 htt.1, lt_of_lt_of_le htt.2 (hmem i.succ).2⟩
    choose z hz hz0 using hrolle
    have hzmono : StrictMono z := by
      intro i j hij
      calc z i < y i.succ := (hz i).2
        _ ≤ y j.castSucc := hmono.monotone (by
            simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
            omega)
        _ < z j := (hz j).1
    have hzmem : ∀ i, z i ∈ Set.Icc a b := fun i =>
      ⟨le_of_lt (lt_of_le_of_lt (hmem i.castSucc).1 (hz i).1),
        le_of_lt (lt_of_lt_of_le (hz i).2 (hmem i.succ).2)⟩
    obtain ⟨c, hc, hc0⟩ := ih (fun k => F (k + 1)) (fun k hk => hcont (k + 1) (by omega))
      (fun k hk t htt => hderiv (k + 1) (by omega) t htt) z hzmono hzmem hz0
    refine ⟨c, ⟨?_, ?_⟩, hc0⟩
    · refine le_trans (le_of_lt ?_) hc.1
      simpa using (hz 0).1
    · refine le_trans hc.2 (le_of_lt ?_)
      simpa using (hz (Fin.last n)).2

/-- **The generalized Rolle theorem, for a function that is smooth only near the interval.** Let $U$
be an open set that contains $[a, b]$, and let $f$ be of class $C^{n+1}$ on $U$. If $f$ vanishes
at $n + 2$ distinct points of $[a, b]$, then there is $c \in (a, b)$ with $f^{(n+1)}(c) = 0$.

The applications need the local hypothesis: a function of Rice's type $(\gamma, m + 1)$ is
smooth on $(0, 1]$ only, and the interpolation error on a panel away from the origin must still
be available. The theorem follows [kress1998numerical], §8.1. The zeros are a finite set `s`
with at least $n + 2$ elements. -/
theorem exists_iteratedDeriv_eq_zero_of_forall_eq_zero_of_contDiffOn {n : ℕ} {a b : ℝ}
    {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hUsub : Set.Icc a b ⊆ U)
    (hf : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f U) {s : Finset ℝ}
    (hcard : n + 2 ≤ s.card) (hsub : ∀ t ∈ s, t ∈ Set.Icc a b) (hzero : ∀ t ∈ s, f t = 0) :
    ∃ c ∈ Set.Ioo a b, iteratedDeriv (n + 1) f c = 0 := by
  obtain ⟨s', hs's, hs'card⟩ := Finset.exists_subset_card_eq hcard
  set y : Fin (n + 2) → ℝ := ⇑(s'.orderEmbOfFin hs'card) with hy
  have hymem : ∀ i, y i ∈ Set.Icc a b := fun i =>
    hsub _ (hs's (Finset.orderEmbOfFin_mem s' hs'card i))
  have hymono : StrictMono y := (s'.orderEmbOfFin hs'card).strictMono
  have hyzero : ∀ i, f (y i) = 0 := fun i =>
    hzero _ (hs's (Finset.orderEmbOfFin_mem s' hs'card i))
  -- differentiability of the successive derivatives, at the points of the open set
  have hstep : ∀ k < n + 1, ∀ t ∈ U,
      HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f t) t := by
    intro k hk t ht
    have hdw : DifferentiableOn ℝ (iteratedDerivWithin k f U) U :=
      hf.differentiableOn_iteratedDerivWithin (by exact_mod_cast hk) hU.uniqueDiffOn
    have heq : Set.EqOn (iteratedDeriv k f) (iteratedDerivWithin k f U) U :=
      (iteratedDerivWithin_of_isOpen hU).symm
    have hda : DifferentiableAt ℝ (iteratedDeriv k f) t :=
      ((hdw t ht).differentiableAt (hU.mem_nhds ht)).congr_of_eventuallyEq
        (Filter.eventuallyEq_of_mem (hU.mem_nhds ht) heq)
    have hd := hda.hasDerivAt
    rwa [← iteratedDeriv_succ] at hd
  have hcont : ∀ k < n + 1, ContinuousOn (iteratedDeriv k f) (Set.Icc a b) := fun k hk t ht =>
    ((hstep k hk t (hUsub ht)).continuousAt).continuousWithinAt
  -- one Rolle step, then the induction
  have hrolle : ∀ i : Fin (n + 1), ∃ c ∈ Set.Ioo (y i.castSucc) (y i.succ),
      iteratedDeriv 1 f c = 0 := by
    intro i
    refine exists_hasDerivAt_eq_zero (f := iteratedDeriv 0 f)
      (hymono (Fin.castSucc_lt_succ (i := i))) ?_ ?_ ?_
    · exact (hcont 0 (Nat.succ_pos n)).mono
        (Set.Icc_subset_Icc (hymem i.castSucc).1 (hymem i.succ).2)
    · simpa using (hyzero _).trans (hyzero _).symm
    · exact fun t htt => hstep 0 (Nat.succ_pos n) t (hUsub
        ⟨le_of_lt (lt_of_le_of_lt (hymem i.castSucc).1 htt.1),
          le_of_lt (lt_of_lt_of_le htt.2 (hymem i.succ).2)⟩)
  choose z hz hz0 using hrolle
  have hzmono : StrictMono z := by
    intro i j hij
    calc z i < y i.succ := (hz i).2
      _ ≤ y j.castSucc := hymono.monotone (by
          simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
          omega)
      _ < z j := (hz j).1
  have hzmem : ∀ i, z i ∈ Set.Icc a b := fun i =>
    ⟨le_of_lt (lt_of_le_of_lt (hymem i.castSucc).1 (hz i).1),
      le_of_lt (lt_of_lt_of_le (hz i).2 (hymem i.succ).2)⟩
  obtain ⟨c, hc, hc0⟩ := exists_eq_zero_aux n (fun k => iteratedDeriv (k + 1) f)
    (fun k hk => hcont (k + 1) (by omega))
    (fun k hk t htt => hstep (k + 1) (by omega) t (hUsub ⟨htt.1.le, htt.2.le⟩)) z hzmono hzmem hz0
  refine ⟨c, ⟨?_, ?_⟩, hc0⟩
  · exact lt_of_lt_of_le (lt_of_le_of_lt (hymem 0).1 (by simpa using (hz 0).1)) hc.1
  · exact lt_of_le_of_lt hc.2 (lt_of_lt_of_le (by simpa using (hz (Fin.last n)).2)
      (hymem (Fin.last (n + 1))).2)

/-- **The generalized Rolle theorem.** Let $f : \mathbb{R} \to \mathbb{R}$ be of class $C^{n+1}$. If
$f$ vanishes at $n + 2$ distinct points of $[a, b]$, then there is $c \in (a, b)$ with
$$f^{(n+1)}(c) = 0.$$
The theorem follows [kress1998numerical], §8.1.

The zeros are a finite set `s` with at least $n + 2$ elements. The theorem is the case
$U = \mathbb{R}$ of `exists_iteratedDeriv_eq_zero_of_forall_eq_zero_of_contDiffOn`. -/
theorem exists_iteratedDeriv_eq_zero_of_forall_eq_zero {n : ℕ} {a b : ℝ}
    {f : ℝ → ℝ} (hf : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f) {s : Finset ℝ}
    (hcard : n + 2 ≤ s.card) (hsub : ∀ t ∈ s, t ∈ Set.Icc a b) (hzero : ∀ t ∈ s, f t = 0) :
    ∃ c ∈ Set.Ioo a b, iteratedDeriv (n + 1) f c = 0 :=
  exists_iteratedDeriv_eq_zero_of_forall_eq_zero_of_contDiffOn isOpen_univ (Set.subset_univ _)
    hf.contDiffOn hcard hsub hzero

/-! ### The interpolation error formula -/

namespace Lagrange

/-! ### Lagrange basis and nodal polynomials -/

section BasisNodal

open Polynomial

/-- **A polynomial with the values of a Lagrange basis polynomial is that polynomial.** Let $F$ be a
field, let $s$ be a finite index set, and let the nodes $v_j$, $j \in s$, be distinct. Let $p$
be a polynomial of degree less than $|s|$, and let $i \in s$. If $p(v_j) = 1$ for $j = i$ and
$p(v_j) = 0$ for the other $j \in s$, then
$$p = \ell_i,$$
the Lagrange basis polynomial `Lagrange.basis s v i`. -/
theorem eq_basis_of_eval {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {v : ι → F} (hvs : Set.InjOn v s) {p : F[X]} (hp : p.degree < s.card)
    {i : ι} (hi : i ∈ s) (h : ∀ j ∈ s, p.eval (v j) = if j = i then 1 else 0) :
    p = Lagrange.basis s v i := by
  refine Polynomial.eq_of_degrees_lt_of_eval_index_eq s hvs hp ?_ fun j hj => ?_
  · rw [Lagrange.degree_basis hvs hi]
    exact_mod_cast Nat.sub_lt (Finset.card_pos.2 ⟨i, hi⟩) one_pos
  · rw [h j hj]
    split_ifs with hji
    · rw [hji, Lagrange.eval_basis_self hvs hi]
    · rw [Lagrange.eval_basis_of_ne (Ne.symm hji) hj]

/-- The Lagrange basis polynomial is the nodal weight times the nodal polynomial of the other nodes:
if $i \in s$, then $\ell_i = w_i \prod_{j \in s,\, j \neq i} (X - v_j)$, where $w_i$ is
`Lagrange.nodalWeight s v i`. -/
theorem basis_eq_C_nodalWeight_mul_nodal_erase {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {v : ι → F} {i : ι} (hi : i ∈ s) :
    Lagrange.basis s v i = C (Lagrange.nodalWeight s v i) * Lagrange.nodal (s.erase i) v := by
  rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div hi, ← Lagrange.nodal_erase_eq_nodal_div hi]

/-- The Lagrange basis polynomial of an affine image of the nodes is the basis polynomial of the
nodes, composed with the affine map. Let $v_0, \dots, v_n$ be distinct real numbers, let
$c, h \in \mathbb{R}$ with $h \neq 0$, and let $\ell_i$ and $\varphi_i$ be the Lagrange basis
polynomials of the nodes $x_k = c + h v_k$ and $v_k$. Then for every $i$
$$\ell_i(c + hX) = \varphi_i.$$
-/
theorem basis_comp_affine {n : ℕ} {v : Fin (n + 1) → ℝ} (hv : Function.Injective v)
    {c h : ℝ} (hh : h ≠ 0) (i : Fin (n + 1)) :
    (Lagrange.basis Finset.univ (fun k => c + h * v k) i).comp (C h * X + C c)
      = Lagrange.basis Finset.univ v i := by
  have hinj : Function.Injective fun k => c + h * v k := fun k l hkl => by
    have : h * v k = h * v l := by simpa using hkl
    exact hv (mul_left_cancel₀ hh this)
  refine Lagrange.eq_basis_of_eval hv.injOn ?_ (Finset.mem_univ _) fun j _ => ?_
  · refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
    have h1 : (Lagrange.basis Finset.univ (fun k => c + h * v k) i).natDegree ≤ n := by
      rw [Lagrange.natDegree_basis hinj.injOn (Finset.mem_univ i)]
      simp
    have h2 : (C h * X + C c).natDegree ≤ 1 := Polynomial.natDegree_linear_le
    have := Polynomial.natDegree_comp_le (p := Lagrange.basis Finset.univ (fun k => c + h * v k) i)
      (q := C h * X + C c)
    simp only [Finset.card_univ, Fintype.card_fin]
    exact_mod_cast lt_of_le_of_lt this (by nlinarith)
  · rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_C, add_comm (h * v j) c]
    split_ifs with hji
    · rw [hji]
      exact Lagrange.eval_basis_self (v := fun k => c + h * v k) hinj.injOn (Finset.mem_univ i)
    · exact Lagrange.eval_basis_of_ne (v := fun k => c + h * v k) (Ne.symm hji)
        (Finset.mem_univ j)

/-- The derivative of a Lagrange basis polynomial at its own node. Let $x_0, \dots, x_n$ be distinct
real numbers, let $\omega = \prod_j (X - x_j)$ be their nodal polynomial, and let $\ell_k$ be
the Lagrange basis polynomial of $x_k$. Then
$$\ell_k'(x_k) = \frac{\omega''(x_k)}{2\, \omega'(x_k)}.$$

With $\omega = (X - x_k)\, \omega_k$ and $\ell_k = \omega_k/\omega_k(x_k)$, one has
$\omega'(x_k) = \omega_k(x_k)$ and $\omega''(x_k) = 2\, \omega_k'(x_k)$. -/
theorem eval_derivative_basis_self {n : ℕ} {x : Fin (n + 1) → ℝ}
    (hx : Function.Injective x) (k : Fin (n + 1)) :
    (derivative (Lagrange.basis Finset.univ x k)).eval (x k)
      = (derivative (derivative (Lagrange.nodal Finset.univ x))).eval (x k)
        / (2 * (derivative (Lagrange.nodal Finset.univ x)).eval (x k)) := by
  classical
  set ωk : ℝ[X] := Lagrange.nodal (Finset.univ.erase k) x with hωk
  have hbasis : Lagrange.basis Finset.univ x k = C (Lagrange.nodalWeight Finset.univ x k) * ωk := by
    rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div (Finset.mem_univ k),
      ← Lagrange.nodal_erase_eq_nodal_div (Finset.mem_univ k)]
  have hnodal : Lagrange.nodal Finset.univ x = (X - C (x k)) * ωk :=
    Lagrange.nodal_eq_mul_nodal_erase (Finset.mem_univ k)
  have hW : Lagrange.nodalWeight Finset.univ x k = (ωk.eval (x k))⁻¹ :=
    Lagrange.nodalWeight_eq_eval_nodal_erase_inv
  have hωk0 : ωk.eval (x k) ≠ 0 := by
    rw [hωk, Lagrange.eval_nodal]
    exact Finset.prod_ne_zero_iff.2 fun j hj =>
      sub_ne_zero.2 fun h => (Finset.mem_erase.1 hj).1 (hx h).symm
  have hd1 : derivative (Lagrange.nodal Finset.univ x) = ωk + (X - C (x k)) * derivative ωk := by
    rw [hnodal, derivative_mul, derivative_X_sub_C, one_mul]
  have hd2 : derivative (derivative (Lagrange.nodal Finset.univ x))
      = 2 * derivative ωk + (X - C (x k)) * derivative (derivative ωk) := by
    rw [hd1, derivative_add, derivative_mul, derivative_X_sub_C, one_mul]
    ring
  rw [hbasis, derivative_mul, derivative_C, zero_mul, zero_add, eval_mul, eval_C, hW, hd2, hd1]
  simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, eval_ofNat, sub_self, zero_mul,
    add_zero]
  field_simp

/-- Let $x_0, \dots, x_n$ be distinct real numbers. A monic real polynomial $q$ of degree $n + 1$
with $q(x_i) = 0$ for all $i$ is the nodal polynomial: $q = \prod_i (X - x_i)$. -/
theorem nodal_eq_of_forall_eval_eq_zero {n : ℕ} {x : Fin (n + 1) → ℝ}
    (hx : Function.Injective x)
    {q : ℝ[X]} (hq : q.Monic) (hdeg : q.natDegree = n + 1) (hroot : ∀ i, q.eval (x i) = 0) :
    Lagrange.nodal Finset.univ x = q := by
  refine sub_eq_zero.mp (Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero Finset.univ
    hx.injOn ?_ fun i _ => ?_)
  · have := degree_sub_lt_left (p := Lagrange.nodal Finset.univ x) (q := q)
      (by rw [Lagrange.degree_nodal, degree_eq_natDegree hq.ne_zero, hdeg]; simp)
      Lagrange.nodal_ne_zero (by rw [Lagrange.nodal_monic.leadingCoeff, hq.leadingCoeff])
    rwa [Lagrange.degree_nodal] at this
  · rw [eval_sub, hroot i, Lagrange.eval_nodal_at_node (Finset.mem_univ i), sub_zero]

/-- A real number $t$ is a node of the family $x_0, \dots, x_n$ if and only if the nodal polynomial
vanishes there:
$$(\exists i,\ x_i = t) \iff \prod_i (t - x_i) = 0.$$
The nodes need not be distinct. -/
theorem exists_eq_iff_eval_nodal_eq_zero {n : ℕ} (x : Fin (n + 1) → ℝ) (t : ℝ) :
    (∃ i, x i = t) ↔ (Lagrange.nodal Finset.univ x).eval t = 0 := by
  rw [Lagrange.eval_nodal, Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and, sub_eq_zero]
  exact exists_congr fun i => eq_comm

/-- Let $x_0, \dots, x_{m-1}$ be distinct real numbers, let $\sigma$ be a permutation of the
indices, and let $f : \mathbb{R} \to \mathbb{R}$. Then the interpolation polynomial of $f$ at
the reindexed nodes $x_{\sigma(0)}, \dots, x_{\sigma(m-1)}$ equals the interpolation polynomial
of $f$ at $x_0, \dots, x_{m-1}$. -/
theorem interpolate_comp_equiv {m : ℕ} {x : Fin m → ℝ} (hx : Function.Injective x)
    (σ : Equiv.Perm (Fin m)) (f : ℝ → ℝ) :
    (Lagrange.interpolate Finset.univ (x ∘ σ) fun i => f ((x ∘ σ) i)) =
      Lagrange.interpolate Finset.univ x fun i => f (x i) := by
  have hxσ : Function.Injective (x ∘ σ) := hx.comp σ.injective
  have hdeg : (Lagrange.interpolate Finset.univ (x ∘ σ) fun i => f ((x ∘ σ) i)).degree <
      (Finset.univ : Finset (Fin m)).card :=
    Lagrange.degree_interpolate_lt _ hxσ.injOn
  have hev : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      (Lagrange.interpolate Finset.univ (x ∘ σ) fun i => f ((x ∘ σ) i)).eval (x i) = f (x i) := by
    intro i _
    have h := Lagrange.eval_interpolate_at_node (fun i => f ((x ∘ σ) i)) hxσ.injOn
      (Finset.mem_univ (σ.symm i))
    simp only [Function.comp_apply, Equiv.apply_symm_apply] at h
    exact h
  exact Lagrange.eq_interpolate_of_eval_eq _ hx.injOn hdeg hev

end BasisNodal

/-! ### The error formula -/

/-- **The Lagrange interpolation error formula, for a function that is smooth only near the
interval.** Let $a < b$, let $U$ be an open set that contains $[a, b]$, and let $f$ be of class
$C^{n+1}$ on $U$. Let $x_0, \dots, x_n$ be distinct nodes in $[a, b]$, and let $p$ be the
polynomial of degree at most $n$ that interpolates $f$ at them. Then for every $t \in [a, b]$
there is $\xi \in (a, b)$ with
$$f(t) - p(t) = \frac{f^{(n+1)}(\xi)}{(n + 1)!} \prod_{i=0}^{n} (t - x_i).$$
This is Theorem 8.4 of [kress1998numerical], and §3.2 of [han2009theoretical].

The interpolation polynomial is `Lagrange.interpolate`. The proof applies the generalized Rolle
theorem to $s \mapsto f(s) - p(s) - c \prod_i (s - x_i)$, with $c$ chosen so that the value at
$t$ vanishes. -/
theorem exists_sub_interpolate_eq_of_contDiffOn {n : ℕ} {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    {U : Set ℝ} (hU : IsOpen U) (hUsub : Set.Icc a b ⊆ U)
    (hf : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f U) {v : Fin (n + 1) → ℝ}
    (hv : Function.Injective v) (hvmem : ∀ i, v i ∈ Set.Icc a b) {t : ℝ} (ht : t ∈ Set.Icc a b) :
    ∃ ξ ∈ Set.Ioo a b,
      f t - (Lagrange.interpolate Finset.univ v fun i => f (v i)).eval t
        = iteratedDeriv (n + 1) f ξ / (n + 1).factorial * ∏ i, (t - v i) := by
  classical
  set p : ℝ[X] := Lagrange.interpolate Finset.univ v (fun i => f (v i)) with hp
  by_cases hcase : ∃ j, t = v j
  · obtain ⟨j, rfl⟩ := hcase
    obtain ⟨ξ, hξ⟩ := Set.nonempty_Ioo.mpr hab
    refine ⟨ξ, hξ, ?_⟩
    rw [hp, Lagrange.eval_interpolate_at_node _ hv.injOn (Finset.mem_univ j), sub_self,
      Finset.prod_eq_zero (Finset.mem_univ j) (sub_self _), mul_zero]
  · push Not at hcase
    -- the nodal polynomial
    set W : ℝ[X] := ∏ i : Fin (n + 1), (Polynomial.X - Polynomial.C (v i)) with hW
    have hWeval : ∀ s : ℝ, W.eval s = ∏ i, (s - v i) := by
      intro s
      simp [hW, Polynomial.eval_prod]
    have hWt : W.eval t ≠ 0 := by
      rw [hWeval]
      exact Finset.prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr (hcase i)
    set c : ℝ := (f t - p.eval t) / W.eval t with hc
    set Q : ℝ[X] := p + Polynomial.C c * W with hQ
    -- the auxiliary function and its `n + 2` zeros
    set s : Finset ℝ := insert t (Finset.univ.image v) with hs
    have htnot : t ∉ Finset.univ.image v := by
      simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
      exact fun i h => hcase i h.symm
    have hscard : n + 2 ≤ s.card := by
      rw [hs, Finset.card_insert_of_notMem htnot,
        Finset.card_image_of_injective _ hv, Finset.card_univ, Fintype.card_fin]
    have hssub : ∀ u ∈ s, u ∈ Set.Icc a b := by
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact ht
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hu
        exact hvmem i
    have hgzero : ∀ u ∈ s, f u - Q.eval u = 0 := by
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · rw [hQ]
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
        rw [hc]
        field_simp
        ring
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hu
        rw [hQ]
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
        rw [hp, Lagrange.eval_interpolate_at_node _ hv.injOn (Finset.mem_univ i), hWeval,
          Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)]
        ring
    -- the generalized Rolle theorem
    have hQdiff : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) fun u => Q.eval u := by
      simpa [Polynomial.coe_aeval_eq_eval] using
        Q.contDiff_aeval (𝕜 := ℝ) ((n + 1 : ℕ) : WithTop ℕ∞)
    obtain ⟨ξ, hξ, hξ0⟩ := exists_iteratedDeriv_eq_zero_of_forall_eq_zero_of_contDiffOn hU hUsub
      (hf.sub hQdiff.contDiffOn) hscard hssub hgzero
    refine ⟨ξ, hξ, ?_⟩
    -- compute the `(n + 1)`-st derivative of the auxiliary function
    have hpdeg : p.degree < ((n + 1 : ℕ) : WithBot ℕ) := by
      have h := Lagrange.degree_interpolate_lt (s := (Finset.univ : Finset (Fin (n + 1))))
        (r := fun i => f (v i)) hv.injOn
      rw [Finset.card_univ, Fintype.card_fin] at h
      rw [hp]
      exact h
    have hpder : Polynomial.derivative^[n + 1] p = 0 :=
      Polynomial.iterate_derivative_eq_zero_of_degree_lt hpdeg
    have hWder : Polynomial.derivative^[n + 1] W = ((n + 1).factorial : ℝ[X]) := by
      have himg : (Finset.univ.image v).card = n + 1 := by
        rw [Finset.card_image_of_injective _ hv, Finset.card_univ, Fintype.card_fin]
      have hWprod : W = ∏ u ∈ Finset.univ.image v, (Polynomial.X - Polynomial.C u) := by
        rw [hW, Finset.prod_image (fun i _ j _ h => hv h)]
      rw [hWprod, Polynomial.iterate_derivative_prod_X_sub_C (by rw [himg]), himg]
      simp
    have hQder : iteratedDeriv (n + 1) (fun u => Q.eval u) ξ = c * (n + 1).factorial := by
      rw [Polynomial.iteratedDeriv_eval]
      have hQd : Polynomial.derivative^[n + 1] Q
          = Polynomial.derivative^[n + 1] p + Polynomial.C c * Polynomial.derivative^[n + 1] W := by
        rw [hQ, Polynomial.iterate_derivative_add, Polynomial.iterate_derivative_C_mul]
      rw [hQd, hpder, hWder]
      simp
    have hsub' : iteratedDeriv (n + 1) (fun u => f u - Q.eval u) ξ
        = iteratedDeriv (n + 1) f ξ - iteratedDeriv (n + 1) (fun u => Q.eval u) ξ :=
      iteratedDeriv_fun_sub (hf.contDiffAt (hU.mem_nhds (hUsub ⟨hξ.1.le, hξ.2.le⟩)))
        hQdiff.contDiffAt
    rw [hsub', hQder] at hξ0
    have hfact : ((n + 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hceq : c = iteratedDeriv (n + 1) f ξ / (n + 1).factorial := by
      field_simp
      linarith [hξ0]
    rw [← hWeval, ← hceq, hc]
    field_simp

/-- **The Lagrange interpolation error formula.** Let $a < b$, and let
$f : \mathbb{R} \to \mathbb{R}$ be of class $C^{n+1}$. Let $x_0, \dots, x_n$ be distinct nodes
in $[a, b]$, and let $p$ be the polynomial of degree at most $n$ that interpolates $f$ at them.
Then for every $t \in [a, b]$ there is $\xi \in (a, b)$ with
$$f(t) - p(t) = \frac{f^{(n+1)}(\xi)}{(n + 1)!} \prod_{i=0}^{n} (t - x_i).$$
This is Theorem 8.4 of [kress1998numerical], and §3.2 of [han2009theoretical].

The interpolation polynomial is `Lagrange.interpolate`. The theorem is the case $U = \mathbb{R}$
of `Lagrange.exists_sub_interpolate_eq_of_contDiffOn`. -/
theorem exists_sub_interpolate_eq {n : ℕ} {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f) {v : Fin (n + 1) → ℝ}
    (hv : Function.Injective v) (hvmem : ∀ i, v i ∈ Set.Icc a b) {t : ℝ} (ht : t ∈ Set.Icc a b) :
    ∃ ξ ∈ Set.Ioo a b,
      f t - (Lagrange.interpolate Finset.univ v fun i => f (v i)).eval t
        = iteratedDeriv (n + 1) f ξ / (n + 1).factorial * ∏ i, (t - v i) :=
  exists_sub_interpolate_eq_of_contDiffOn hab isOpen_univ (Set.subset_univ _) hf.contDiffOn hv
    hvmem ht

/-- The value of a Lagrange basis polynomial at $t$ is the product of the ratios over the other
nodes: $\ell_i(t) = \prod_{j \in s,\, j \neq i} (t - v_j)/(v_i - v_j)$. -/
theorem eval_basis_eq_prod {F : Type*} [Field F] {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (v : ι → F) (i : ι) (t : F) :
    (Lagrange.basis s v i).eval t = ∏ j ∈ s.erase i, (t - v j) / (v i - v j) := by
  simp only [Lagrange.basis, Polynomial.eval_prod, Lagrange.basisDivisor, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
  exact Finset.prod_congr rfl fun j _ => (div_eq_inv_mul _ _).symm

/-- **A crude bound for a Lagrange basis polynomial.** Let $v$ be a finite family of real nodes, and
let $d > 0$ and $D$ be such that $|t - v_j| \le D$ for every node $v_j$ and $|v_i - v_j| \ge d$
for every $j \neq i$. Then $|\ell_i(t)| \le (D/d)^m$, where $m$ is the number of nodes other
than $v_i$.

The bound is far from sharp; the sharp quantity is the Lebesgue function. But the bound is
uniform over every family of node systems with the same shape, and a piecewise polynomial
interpolation operator on a refining mesh needs this: $D$ and $d$ are then both proportional to
the length of the panel, and their ratio does not depend on the mesh. -/
theorem abs_eval_basis_le {ι : Type*} [DecidableEq ι] [Fintype ι] (v : ι → ℝ) (i : ι)
    {t D d : ℝ} (hd : 0 < d) (hD : ∀ j, |t - v j| ≤ D) (hsep : ∀ j, j ≠ i → d ≤ |v i - v j|) :
    |(Lagrange.basis Finset.univ v i).eval t| ≤ (D / d) ^ ((Finset.univ : Finset ι).erase i).card
    := by
  have hD0 : (0 : ℝ) ≤ D := le_trans (abs_nonneg _) (hD i)
  have hstep : ∀ j ∈ (Finset.univ : Finset ι).erase i, |(t - v j) / (v i - v j)| ≤ D / d := by
    intro j hj
    have hne : j ≠ i := (Finset.mem_erase.mp hj).1
    have hdj : d ≤ |v i - v j| := hsep j hne
    have hpos : (0 : ℝ) < |v i - v j| := lt_of_lt_of_le hd hdj
    rw [abs_div, div_le_div_iff₀ hpos hd]
    nlinarith [hD j, hdj, hd, abs_nonneg (t - v j)]
  rw [eval_basis_eq_prod, Finset.abs_prod]
  calc ∏ j ∈ (Finset.univ : Finset ι).erase i, |(t - v j) / (v i - v j)|
      ≤ ∏ _j ∈ (Finset.univ : Finset ι).erase i, D / d :=
        Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) hstep
    _ = (D / d) ^ ((Finset.univ : Finset ι).erase i).card := Finset.prod_const _


/-! ### The interpolation operator on continuous functions -/

variable {X : Set ℝ} [CompactSpace X] {n : ℕ}

/-- The $i$-th Lagrange basis polynomial $\ell_i$ of the nodes $x_0, \dots, x_n \in X$, as a
continuous function on $X$. -/
noncomputable def basisCM (x : Fin (n + 1) → X) (i : Fin (n + 1)) : C(X, ℝ) :=
  (Lagrange.basis Finset.univ (fun j => (x j : ℝ)) i).toContinuousMapOn X

omit [CompactSpace X] in
/-- The value of the Lagrange basis function `Lagrange.basisCM x i` at $t$ is $\ell_i(t)$. -/
theorem basisCM_apply (x : Fin (n + 1) → X) (i : Fin (n + 1)) (t : X) :
    basisCM x i t = (Lagrange.basis Finset.univ (fun j => (x j : ℝ)) i).eval (t : ℝ) := rfl

/-- The **Lagrange interpolation operator** at the nodes $x_0, \dots, x_n$ of a compact set
$X \subseteq \mathbb{R}$: the bounded operator on $C(X)$
$$\Pi_n f = \sum_{i=0}^{n} f(x_i)\, \ell_i.$$
This is Example 3.6.5 of [han2009theoretical].

For distinct nodes, $\Pi_n$ is a projection onto the polynomials of degree at most $n$
(`Lagrange.range_interpolateCLM`, `Lagrange.isIdempotentElem_interpolateCLM`). It is the
projection $P$ of the Lebesgue lemma `norm_sub_apply_le_of_isIdempotentElem`, and its operator
norm is the Lebesgue constant of the nodes (`Lagrange.norm_interpolateCLM`). The definition
makes sense for any nodes. -/
noncomputable def interpolateCLM (x : Fin (n + 1) → X) : C(X, ℝ) →L[ℝ] C(X, ℝ) :=
  ∑ i, (ContinuousMap.evalCLM (R := ℝ) (x i)).smulRight (basisCM x i)

/-- The value of the Lagrange interpolant at $t \in X$ is $\Pi_n f(t) = \sum_i f(x_i)\, \ell_i(t)$.
-/
theorem interpolateCLM_apply (x : Fin (n + 1) → X) (f : C(X, ℝ)) (t : X) :
    interpolateCLM x f t = ∑ i, f (x i) * basisCM x i t := by
  simp [interpolateCLM]

/-- The Lagrange interpolation operator is the evaluation of Mathlib's interpolation polynomial
`Lagrange.interpolate` of the values $f(x_i)$. -/
theorem interpolateCLM_apply_eq_eval (x : Fin (n + 1) → X) (f : C(X, ℝ)) (t : X) :
    interpolateCLM x f t
      = (Lagrange.interpolate Finset.univ (fun j => (x j : ℝ))
          (fun i => f (x i))).eval (t : ℝ) := by
  rw [interpolateCLM_apply, Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
  simp [basisCM_apply]

/-- If the nodes are distinct, then the Lagrange interpolant agrees with $f$ at the nodes:
$\Pi_n f(x_j) = f(x_j)$. -/
theorem interpolateCLM_apply_node {x : Fin (n + 1) → X} (hx : Function.Injective x)
    (f : C(X, ℝ)) (j : Fin (n + 1)) : interpolateCLM x f (x j) = f (x j) := by
  have hinj : Function.Injective fun j => (x j : ℝ) := Subtype.val_injective.comp hx
  rw [interpolateCLM_apply_eq_eval,
    Lagrange.eval_interpolate_at_node _ hinj.injOn (Finset.mem_univ j)]

/-- Let $X \subseteq \mathbb{R}$ be compact, and let $x_0, \dots, x_n \in X$ be distinct. Then the
range of the Lagrange interpolation operator $\Pi_n$ is the space of polynomials of degree at
most $n$ on $X$, `polyLE X n`. -/
theorem range_interpolateCLM {x : Fin (n + 1) → X} (hx : Function.Injective x) :
    LinearMap.range (interpolateCLM x : C(X, ℝ) →ₗ[ℝ] C(X, ℝ)) = polyLE X n := by
  have hinj : Function.Injective fun j => (x j : ℝ) := Subtype.val_injective.comp hx
  apply le_antisymm
  · rintro g ⟨f, rfl⟩
    refine mem_polyLE_iff.mpr ⟨Lagrange.interpolate Finset.univ (fun j => (x j : ℝ))
      (fun i => f (x i)), ?_, fun t => interpolateCLM_apply_eq_eval x f t⟩
    have h := Lagrange.degree_interpolate_le (s := (Finset.univ : Finset (Fin (n + 1))))
      (r := fun i => f (x i)) hinj.injOn
    rwa [Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel] at h
  · intro g hg
    obtain ⟨P, hPdeg, hPval⟩ := mem_polyLE_iff.mp hg
    refine ⟨g, ?_⟩
    have hPlt : P.degree < ((Finset.univ : Finset (Fin (n + 1))).card : WithBot ℕ) := by
      rw [Finset.card_univ, Fintype.card_fin]
      exact lt_of_le_of_lt hPdeg (by exact_mod_cast Nat.lt_succ_self n)
    have hP := Lagrange.eq_interpolate (v := fun j => (x j : ℝ)) hinj.injOn hPlt
    ext t
    rw [ContinuousLinearMap.coe_coe, interpolateCLM_apply_eq_eval]
    have hnodes : (fun i => g (x i)) = fun i => P.eval ((x i : ℝ)) := by
      funext i
      exact hPval (x i)
    rw [hnodes, ← hP, hPval t]

/-- Let $X \subseteq \mathbb{R}$ be compact, and let $x_0, \dots, x_n \in X$ be distinct. Then the
Lagrange interpolation operator is a projection: $\Pi_n \circ \Pi_n = \Pi_n$. -/
theorem isIdempotentElem_interpolateCLM {x : Fin (n + 1) → X} (hx : Function.Injective x) :
    IsIdempotentElem (interpolateCLM x) := by
  have h : ∀ f : C(X, ℝ), interpolateCLM x (interpolateCLM x f) = interpolateCLM x f := by
    intro f
    ext t
    rw [interpolateCLM_apply, interpolateCLM_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [interpolateCLM_apply_node hx f i]
  exact ContinuousLinearMap.ext h

omit [CompactSpace X] in
/-- If the nodes are distinct, then the Lagrange basis function $\ell_i$ takes the value $1$ at its
own node: $\ell_i(x_i) = 1$. -/
theorem basisCM_apply_node_self {x : Fin (n + 1) → X} (hx : Function.Injective x)
    (i : Fin (n + 1)) : basisCM x i (x i) = 1 := by
  have hinj : Function.Injective fun k => (x k : ℝ) := Subtype.val_injective.comp hx
  rw [basisCM_apply, Lagrange.eval_basis_self hinj.injOn (Finset.mem_univ i)]

omit [CompactSpace X] in
/-- A Lagrange basis function vanishes at the other nodes: $\ell_i(x_j) = 0$ for $i \neq j$. -/
theorem basisCM_apply_node_ne {x : Fin (n + 1) → X} {i j : Fin (n + 1)} (hij : i ≠ j) :
    basisCM x i (x j) = 0 := by
  rw [basisCM_apply]
  exact Lagrange.eval_basis_of_ne (v := fun k => (x k : ℝ)) hij (Finset.mem_univ j)

omit [CompactSpace X] in
/-- If the nodes are distinct, then the combination $\sum_i \sigma_i \ell_i$ of the Lagrange basis
functions takes the value $\sigma_j$ at the node $x_j$. -/
theorem sum_smul_basisCM_apply_node {x : Fin (n + 1) → X} (hx : Function.Injective x)
    (σ : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    (∑ i, σ i • basisCM x i) (x j) = σ j := by
  rw [ContinuousMap.sum_apply, Finset.sum_eq_single j]
  · rw [ContinuousMap.smul_apply, smul_eq_mul, basisCM_apply_node_self hx, mul_one]
  · intro i _ hij
    rw [ContinuousMap.smul_apply, smul_eq_mul, basisCM_apply_node_ne hij, mul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-! ### Lagrange interpolation as a unisolvent problem -/

omit [CompactSpace X] in
/-- If the nodes $x_0, \dots, x_n$ are distinct, then every combination $\sum_i c_i \ell_i$ of their
Lagrange basis functions is a polynomial of degree at most $n$ on $X$. -/
theorem sum_smul_basisCM_mem_polyLE {x : Fin (n + 1) → X} (hx : Function.Injective x)
    (c : Fin (n + 1) → ℝ) : (∑ i, c i • basisCM x i) ∈ polyLE X n := by
  have hinj : Function.Injective fun j => (x j : ℝ) := Subtype.val_injective.comp hx
  refine mem_polyLE_iff.mpr
    ⟨Lagrange.interpolate Finset.univ (fun j => (x j : ℝ)) c, ?_, fun t => ?_⟩
  · have h := Lagrange.degree_interpolate_le (s := (Finset.univ : Finset (Fin (n + 1))))
      (r := c) hinj.injOn
    rwa [Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel] at h
  · rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum, ContinuousMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by simp [basisCM_apply]

/-- **Lagrange interpolation is unisolvent.** Let $X \subseteq \mathbb{R}$ be compact, and let
$x_0, \dots, x_n \in X$ be distinct. Then for all values $b_0, \dots, b_n \in \mathbb{R}$ there
is exactly one polynomial $p$ of degree at most $n$ on $X$ with $p(x_i) = b_i$ for all $i$.

This is `Approximation.IsUnisolvent` of `Numlib.Approximation.Unisolvent` for the space
`polyLE X n` and the point evaluations at the nodes. -/
theorem isUnisolvent_polyLE {x : Fin (n + 1) → X} (hx : Function.Injective x) :
    Approximation.IsUnisolvent (polyLE X n) fun i => ContinuousMap.evalCLM ℝ (x i) := by
  classical
  intro b
  refine ⟨⟨∑ i, b i • basisCM x i, sum_smul_basisCM_mem_polyLE hx b⟩,
    fun i => sum_smul_basisCM_apply_node hx b i, ?_⟩
  rintro ⟨u, hu⟩ hval
  refine Subtype.ext ?_
  by_contra hne
  have hmem : u - ∑ i, b i • basisCM x i ∈ polyLE X n :=
    Submodule.sub_mem _ hu (sum_smul_basisCM_mem_polyLE hx b)
  have hne0 : u - ∑ i, b i • basisCM x i ≠ 0 := sub_ne_zero.mpr hne
  have hzero : ∀ t ∈ Finset.univ.image x, (u - ∑ i, b i • basisCM x i) t = 0 := by
    intro t ht
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
    rw [ContinuousMap.sub_apply, sum_smul_basisCM_apply_node hx b i]
    exact sub_eq_zero.mpr (hval i)
  have hcard : (Finset.univ.image x).card = n + 1 := by
    rw [Finset.card_image_of_injective _ hx, Finset.card_univ, Fintype.card_fin]
  exact absurd (haarCondition_polyLE X n _ hmem hne0 _ hzero) (by omega)

/-- If the nodes are distinct, then the cardinal basis of the Lagrange interpolation problem is the
Lagrange basis: the $i$-th cardinal function is $\ell_i$. -/
theorem cardinalBasisCM_isUnisolvent_polyLE {x : Fin (n + 1) → X} (hx : Function.Injective x)
    (i : Fin (n + 1)) : (isUnisolvent_polyLE hx).cardinalBasisCM i = basisCM x i := by
  have h := (isUnisolvent_polyLE hx).eq_interpolate (b := Pi.single i (1 : ℝ))
    (u := ⟨basisCM x i, ?_⟩) ?_
  · exact congrArg Subtype.val h.symm
  · simpa using sum_smul_basisCM_mem_polyLE hx (Pi.single i (1 : ℝ))
  · intro j
    by_cases hij : j = i
    · subst hij
      simpa using basisCM_apply_node_self hx j
    · simpa [Pi.single_apply, hij] using basisCM_apply_node_ne (Ne.symm hij) (x := x)

/-- **The Lagrange interpolation operator is the interpolation projection** of the unisolvent
problem that it solves: for distinct nodes, `Approximation.IsUnisolvent.interpCLM` of
`Lagrange.isUnisolvent_polyLE` is $\Pi_n$. -/
theorem interpCLM_isUnisolvent_polyLE {x : Fin (n + 1) → X} (hx : Function.Injective x) :
    (isUnisolvent_polyLE hx).interpCLM = interpolateCLM x := by
  refine ContinuousLinearMap.ext fun f => ContinuousMap.ext fun t => ?_
  rw [Approximation.IsUnisolvent.interpCLM_apply, interpolateCLM_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [cardinalBasisCM_isUnisolvent_polyLE hx i]

/-- **The Lebesgue constant.** Let $X \subseteq \mathbb{R}$ be nonempty and compact, and let
$x_0, \dots, x_n \in X$ be distinct. Then the operator norm $\|\Pi_n\|$ is the largest value of
the Lebesgue function $t \mapsto \sum_i |\ell_i(t)|$ on $X$; in particular, the maximum is
attained. This is §3.7.3 of [han2009theoretical].

It is the polynomial case of `Approximation.IsUnisolvent.isGreatest_norm_interpCLM`. -/
theorem isGreatest_norm_interpolateCLM [Nonempty X] {x : Fin (n + 1) → X}
    (hx : Function.Injective x) :
    IsGreatest (Set.range fun t : X => ∑ i, |basisCM x i t|) ‖interpolateCLM x‖ := by
  have h := (isUnisolvent_polyLE hx).isGreatest_norm_interpCLM
  rw [interpCLM_isUnisolvent_polyLE hx] at h
  simpa only [cardinalBasisCM_isUnisolvent_polyLE hx] using h

/-- Let $X \subseteq \mathbb{R}$ be nonempty and compact, and let $x_0, \dots, x_n \in X$ be
distinct. Then the operator norm of the Lagrange interpolation operator is the supremum of the
Lebesgue function:
$$\|\Pi_n\| = \sup_{t \in X} \sum_{i=0}^{n} |\ell_i(t)|.$$
-/
theorem norm_interpolateCLM [Nonempty X] {x : Fin (n + 1) → X} (hx : Function.Injective x) :
    ‖interpolateCLM x‖ = sSup (Set.range fun t : X => ∑ i, |basisCM x i t|) :=
  (isGreatest_norm_interpolateCLM hx).csSup_eq.symm

omit [CompactSpace X] in
/-- Permuting the nodes permutes the Lagrange basis functions: for a permutation $s$ of the indices,
the $i$-th basis function of the nodes $x_{s(0)}, \dots, x_{s(n)}$ is the $s(i)$-th basis
function of $x_0, \dots, x_n$. -/
theorem basisCM_comp_equiv (x : Fin (n + 1) → X) (s : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 1)) : basisCM (x ∘ s) i = basisCM x (s i) := by
  ext t
  rw [basisCM_apply, basisCM_apply, Lagrange.basis, Lagrange.basis]
  refine congrArg (Polynomial.eval (t : ℝ)) ?_
  have hmap : (Finset.univ.erase i).map s.toEmbedding = Finset.univ.erase (s i) := by
    ext c
    simp only [Finset.mem_map, Finset.mem_erase, Finset.mem_univ, Equiv.coe_toEmbedding,
      and_true]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact fun h => hj (s.injective h)
    · intro h
      exact ⟨s.symm c, fun hc => h (by rw [← hc, Equiv.apply_symm_apply]), by simp⟩
  rw [← hmap, Finset.prod_map]
  rfl

/-- **Interpolation depends on the nodes only as a set.** For every permutation $s$ of the indices,
the interpolation operator at the nodes $x_{s(0)}, \dots, x_{s(n)}$ equals the interpolation
operator at $x_0, \dots, x_n$. -/
theorem interpolateCLM_comp_equiv (x : Fin (n + 1) → X) (s : Equiv.Perm (Fin (n + 1))) :
    interpolateCLM (x ∘ s) = interpolateCLM x := by
  rw [interpolateCLM, interpolateCLM, ← Equiv.sum_comp s
    (fun i => (ContinuousMap.evalCLM (R := ℝ) (x i)).smulRight (basisCM x i))]
  exact Finset.sum_congr rfl fun i _ => by rw [basisCM_comp_equiv]; rfl


end Lagrange

/-! ### The modulus of continuity -/

namespace ContinuousMap

variable {X : Type*} [PseudoMetricSpace X]

/-- The **modulus of continuity** of a continuous function $f$ on a pseudometric space $X$ at the
scale $\delta$: the supremum
$$\omega(f, \delta) = \sup \{\, |f(u) - f(v)| : d(u, v) \le \delta \,\}.$$

The supremum is the real `sSup`, so it takes the value $0$ when the set is empty (for
$\delta < 0$ or empty $X$) or unbounded above. On a compact space the set is bounded, and
$\omega(f, \delta)$ is a true supremum (`ContinuousMap.le_modulusOfContinuity`). It tends to $0$
with $\delta$ because a continuous function on a compact space is uniformly continuous
(`ContinuousMap.tendsto_modulusOfContinuity`). -/
noncomputable def modulusOfContinuity (f : C(X, ℝ)) (δ : ℝ) : ℝ :=
  sSup ((fun p : X × X => |f p.1 - f p.2|) '' {p : X × X | dist p.1 p.2 ≤ δ})

variable [CompactSpace X] (f : C(X, ℝ)) {δ : ℝ}

/-- On a compact space, the set of changes $|f(u) - f(v)|$ over pairs with $d(u, v) \le \delta$ is
bounded above. -/
theorem bddAbove_modulusOfContinuity_image :
    BddAbove ((fun p : X × X => |f p.1 - f p.2|) '' {p : X × X | dist p.1 p.2 ≤ δ}) := by
  refine ⟨2 * ‖f‖, ?_⟩
  rintro r ⟨⟨u, v⟩, -, rfl⟩
  have hu : |f u| ≤ ‖f‖ := by simpa using f.norm_coe_le_norm u
  have hv : |f v| ≤ ‖f‖ := by simpa using f.norm_coe_le_norm v
  calc |f u - f v| ≤ |f u| + |f v| := abs_sub _ _
    _ ≤ 2 * ‖f‖ := by linarith

/-- On a compact space, the modulus of continuity bounds every change of value over a distance at
most $\delta$: if $d(u, v) \le \delta$, then $|f(u) - f(v)| \le \omega(f, \delta)$. -/
theorem le_modulusOfContinuity {u v : X} (huv : dist u v ≤ δ) :
    |f u - f v| ≤ f.modulusOfContinuity δ :=
  le_csSup (bddAbove_modulusOfContinuity_image f) ⟨(u, v), huv, rfl⟩

/-- On a nonempty compact space, the modulus of continuity is nonnegative at every scale
$\delta \ge 0$. -/
theorem modulusOfContinuity_nonneg [Nonempty X] (hδ : 0 ≤ δ) : 0 ≤ f.modulusOfContinuity δ := by
  obtain ⟨u⟩ := ‹Nonempty X›
  have := le_modulusOfContinuity f (u := u) (v := u) (by simpa using hδ)
  simpa using this

open Filter Topology in
/-- **The modulus of continuity tends to zero with the scale.** Let $X$ be a nonempty compact
pseudometric space and $f \in C(X)$. Then
$$\omega(f, \delta) \to 0 \qquad \text{as } \delta \to 0,\ \delta \ge 0.$$

This is the uniform continuity of a continuous function on a compact space. It turns every
approximation bound of the form $\|f - Pf\| \le \omega(f, h)$ into a convergence statement as
the mesh $h$ tends to zero. -/
theorem tendsto_modulusOfContinuity [Nonempty X] :
    Tendsto f.modulusOfContinuity (𝓝[≥] (0 : ℝ)) (𝓝 0) := by
  have huc : UniformContinuous f := CompactSpace.uniformContinuous_of_continuous f.continuous
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨d, hd, hdf⟩ := Metric.uniformContinuous_iff.1 huc (ε / 2) (by positivity)
  refine ⟨d / 2, by positivity, fun {r} hr hrd => ?_⟩
  have hr0 : (0 : ℝ) ≤ r := Set.mem_Ici.1 hr
  have hrlt : r < d := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hr0] at hrd
    linarith
  have hle : f.modulusOfContinuity r ≤ ε / 2 := by
    refine Real.sSup_le ?_ (by positivity)
    rintro y ⟨⟨u, v⟩, huv, rfl⟩
    have hd2 := hdf (lt_of_le_of_lt huv hrlt)
    rw [Real.dist_eq] at hd2
    exact hd2.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (f.modulusOfContinuity_nonneg hr0)]
  linarith

end ContinuousMap

/-! ### Piecewise-linear interpolation -/

/-- The **clamped ramp** of $[u, v]$, as a continuous function on $[a, b]$: the function
$t \mapsto \min(\max(t - u, 0), v - u)$, which vanishes below $u$, rises with slope $1$ on
$[u, v]$, and is equal to $v - u$ above $v$.

A continuous piecewise-linear function on a partition is a combination of the ramps of its
subintervals. So the piecewise-linear interpolation operator can be written without gluing. -/
noncomputable def piecewiseLinearRamp (a b u v : ℝ) : C(Set.Icc a b, ℝ) :=
  ⟨fun t => min (max ((t : ℝ) - u) 0) (v - u),
    ((continuous_subtype_val.sub continuous_const).max continuous_const).min continuous_const⟩

/-- The value of the clamped ramp at $t$ is $\min(\max(t - u, 0), v - u)$. -/
@[simp]
theorem piecewiseLinearRamp_apply (a b u v : ℝ) (t : Set.Icc a b) :
    piecewiseLinearRamp a b u v t = min (max ((t : ℝ) - u) 0) (v - u) := rfl

/-- **Piecewise-linear interpolation** on the partition $a = x_0 < x_1 < \dots < x_{n+1} = b$ of
$[a, b]$: the bounded operator on $C([a, b])$ that sends $f$ to the continuous function that
agrees with $f$ at every node and is affine on every subinterval. It is defined as
$$I f = f(x_0) + \sum_{i=0}^{n} \frac{f(x_{i+1}) - f(x_i)}{x_{i+1} - x_i}\, r_i,$$
where $r_i$ is the clamped ramp of $[x_i, x_{i+1}]$. This is §3.2.3 and Exercise 3.6.6 of
[han2009theoretical], and §8.3 of [kress1998numerical].

The form with ramps makes linearity, boundedness and continuity immediate;
`piecewiseLinearInterpCLM_apply_of_mem` is the equivalent local description on one subinterval.
The nodes are given as a sequence, of which only $x_0, \dots, x_{n+1}$ are used, so that the
index arithmetic of the subintervals stays in `ℕ`. The definition makes sense for any sequence
of points of $[a, b]$. -/
noncomputable def piecewiseLinearInterpCLM {a b : ℝ} (n : ℕ) (x : ℕ → Set.Icc a b) :
    C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ) :=
  (ContinuousMap.evalCLM ℝ (x 0)).smulRight 1 +
    ∑ i ∈ Finset.range (n + 1),
      (((x (i + 1) : ℝ) - (x i : ℝ))⁻¹ •
        ContinuousLinearMap.smulRight
          ((ContinuousMap.evalCLM ℝ (x (i + 1)) : C(Set.Icc a b, ℝ) →L[ℝ] ℝ) -
            ContinuousMap.evalCLM ℝ (x i))
          (piecewiseLinearRamp a b (x i) (x (i + 1))))

section PiecewiseLinear

variable {a b : ℝ} {n : ℕ} {x : ℕ → Set.Icc a b}

/-- The value of the piecewise-linear interpolant at $t$ is $f(x_0)$ plus the clamped ramps
$\min(\max(t - x_i, 0), x_{i+1} - x_i)$ of the subintervals, scaled by the divided differences
$(f(x_{i+1}) - f(x_i))/(x_{i+1} - x_i)$. -/
theorem piecewiseLinearInterpCLM_apply (n : ℕ) (x : ℕ → Set.Icc a b) (f : C(Set.Icc a b, ℝ))
    (t : Set.Icc a b) :
    piecewiseLinearInterpCLM n x f t = f (x 0) + ∑ i ∈ Finset.range (n + 1),
      (f (x (i + 1)) - f (x i)) / ((x (i + 1) : ℝ) - (x i : ℝ)) *
        min (max ((t : ℝ) - (x i : ℝ)) 0) ((x (i + 1) : ℝ) - (x i : ℝ)) := by
  simp [piecewiseLinearInterpCLM, div_eq_inv_mul, mul_assoc]

/-- If $x_i < x_{i+1}$ for all $i \le n$, then $x_i \le x_j$ for all $i \le j \le n + 1$. -/
theorem piecewiseLinearInterpCLM.le_node_of_le (hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ))
    {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ n + 1) : (x i : ℝ) ≤ (x j : ℝ) := by
  revert hj
  induction j, hij using Nat.le_induction with
  | base => exact fun _ => le_rfl
  | succ k hk ih => exact fun hk1 => (ih (by omega)).trans (hstep k (by omega)).le

/-- If $x_0 = a$ and $x_{n+1} = b$, then every $t \in [a, b]$ lies in a subinterval $[x_j, x_{j+1}]$
with $j \le n$. -/
theorem exists_mem_subinterval (hfirst : (x 0 : ℝ) = a) (hlast : (x (n + 1) : ℝ) = b)
    (t : Set.Icc a b) :
    ∃ j ≤ n, (x j : ℝ) ≤ (t : ℝ) ∧ (t : ℝ) ≤ (x (j + 1) : ℝ) := by
  classical
  set S : Finset ℕ := (Finset.range (n + 1)).filter fun i => (x i : ℝ) ≤ (t : ℝ) with hS
  have h0 : 0 ∈ S := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
    rw [hfirst]
    exact t.2.1
  set j := S.max' ⟨0, h0⟩ with hj
  have hjS : j ∈ S := S.max'_mem ⟨0, h0⟩
  have hjmem := Finset.mem_filter.mp hjS
  have hjrange : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hjmem.1)
  refine ⟨j, hjrange, hjmem.2, ?_⟩
  by_contra hcon
  push Not at hcon
  have hjn : j + 1 ≤ n := by
    by_contra hjn
    have hje : j = n := by omega
    rw [hje, hlast] at hcon
    exact absurd t.2.2 (not_le.mpr hcon)
  have hmem : j + 1 ∈ S :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hcon.le⟩
  have := S.le_max' _ hmem
  omega

/-- **The local description of the piecewise-linear interpolant.** Let $x_i < x_{i+1}$ for all
$i \le n$, let $j \le n$, and let $t \in [a, b]$ with $x_j \le t \le x_{j+1}$. Then
$$I f(t) = f(x_j) + \bigl(f(x_{j+1}) - f(x_j)\bigr) \frac{t - x_j}{x_{j+1} - x_j}.$$
So on $[x_j, x_{j+1}]$ the interpolant is the affine function through $(x_j, f(x_j))$ and
$(x_{j+1}, f(x_{j+1}))$. -/
theorem piecewiseLinearInterpCLM_apply_of_mem (hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ))
    (f : C(Set.Icc a b, ℝ)) {j : ℕ} (hj : j ≤ n) {t : Set.Icc a b}
    (h1 : (x j : ℝ) ≤ (t : ℝ)) (h2 : (t : ℝ) ≤ (x (j + 1) : ℝ)) :
    piecewiseLinearInterpCLM n x f t = f (x j) +
      (f (x (j + 1)) - f (x j)) * (((t : ℝ) - (x j : ℝ)) / ((x (j + 1) : ℝ) - (x j : ℝ))) := by
  classical
  set F : ℕ → ℝ := fun i => (f (x (i + 1)) - f (x i)) / ((x (i + 1) : ℝ) - (x i : ℝ)) *
    min (max ((t : ℝ) - (x i : ℝ)) 0) ((x (i + 1) : ℝ) - (x i : ℝ)) with hF
  -- the terms before `j` are the full increments
  have hbefore : ∀ i < j, F i = f (x (i + 1)) - f (x i) := by
    intro i hi
    have hd : (0 : ℝ) < (x (i + 1) : ℝ) - (x i : ℝ) := sub_pos.mpr (hstep i (by omega))
    have hle : (x (i + 1) : ℝ) ≤ (t : ℝ) :=
      (piecewiseLinearInterpCLM.le_node_of_le hstep (by omega) (by omega)).trans h1
    have hmax : max ((t : ℝ) - (x i : ℝ)) 0 = (t : ℝ) - (x i : ℝ) := by
      refine max_eq_left ?_
      linarith
    have hmin : min ((t : ℝ) - (x i : ℝ)) ((x (i + 1) : ℝ) - (x i : ℝ))
        = (x (i + 1) : ℝ) - (x i : ℝ) := min_eq_right (by linarith)
    rw [hF]
    simp only [hmax, hmin]
    field_simp
  -- the terms after `j` vanish
  have hafter : ∀ i, j < i → i ≤ n → F i = 0 := by
    intro i hi hin
    have hd : (0 : ℝ) < (x (i + 1) : ℝ) - (x i : ℝ) := sub_pos.mpr (hstep i hin)
    have hge : (t : ℝ) ≤ (x i : ℝ) :=
      h2.trans (piecewiseLinearInterpCLM.le_node_of_le hstep (by omega) (by omega))
    have hmax : max ((t : ℝ) - (x i : ℝ)) 0 = 0 := max_eq_right (by linarith)
    rw [hF]
    simp only [hmax]
    rw [min_eq_left hd.le, mul_zero]
  have hat : F j = (f (x (j + 1)) - f (x j)) *
      (((t : ℝ) - (x j : ℝ)) / ((x (j + 1) : ℝ) - (x j : ℝ))) := by
    have hmax : max ((t : ℝ) - (x j : ℝ)) 0 = (t : ℝ) - (x j : ℝ) := max_eq_left (by linarith)
    have hmin : min ((t : ℝ) - (x j : ℝ)) ((x (j + 1) : ℝ) - (x j : ℝ))
        = (t : ℝ) - (x j : ℝ) := min_eq_left (by linarith)
    rw [hF]
    simp only [hmax, hmin]
    ring
  rw [piecewiseLinearInterpCLM_apply]
  have hsum : ∑ i ∈ Finset.range (n + 1), F i = f (x j) - f (x 0) + F j := by
    have hsplit : ∑ i ∈ Finset.range (n + 1), F i
        = ∑ i ∈ Finset.range j, F i + ∑ i ∈ Finset.Ico j (n + 1), F i := by
      simp only [Finset.range_eq_Ico]
      exact (Finset.sum_Ico_consecutive F (Nat.zero_le j) (by omega)).symm
    have htail : ∑ i ∈ Finset.Ico j (n + 1), F i = F j := by
      rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)]
      have : ∑ i ∈ Finset.Ico (j + 1) (n + 1), F i = 0 :=
        Finset.sum_eq_zero fun i hi => by
          rw [Finset.mem_Ico] at hi
          exact hafter i (by omega) (by omega)
      rw [this, add_zero]
    have hhead : ∑ i ∈ Finset.range j, F i = f (x j) - f (x 0) := by
      rw [Finset.sum_congr rfl fun i hi => hbefore i (Finset.mem_range.mp hi)]
      exact Finset.sum_range_sub (fun i => f (x i)) j
    rw [hsplit, htail, hhead]
  rw [hsum, hat]
  ring

/-- If $x_i < x_{i+1}$ for all $i \le n$, then the piecewise-linear interpolant agrees with $f$ at
every node $x_j$, $j \le n + 1$. -/
theorem piecewiseLinearInterpCLM_apply_node (hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ))
    (f : C(Set.Icc a b, ℝ)) {j : ℕ} (hj : j ≤ n + 1) :
    piecewiseLinearInterpCLM n x f (x j) = f (x j) := by
  rcases Nat.lt_or_ge j (n + 1) with h | h
  · rw [piecewiseLinearInterpCLM_apply_of_mem hstep f (Nat.lt_succ_iff.mp h) le_rfl
      (hstep j (Nat.lt_succ_iff.mp h)).le]
    simp
  · have hje : j = n + 1 := le_antisymm hj h
    subst hje
    have hd : (0 : ℝ) < (x (n + 1) : ℝ) - (x n : ℝ) := sub_pos.mpr (hstep n le_rfl)
    rw [piecewiseLinearInterpCLM_apply_of_mem hstep f (le_refl n) (hstep n le_rfl).le le_rfl]
    field_simp
    ring

/-- On a partition $a = x_0 < \dots < x_{n+1} = b$, the piecewise-linear interpolation operator is a
projection: $I \circ I = I$. -/
theorem isIdempotentElem_piecewiseLinearInterpCLM
    (hx : IsIntervalPartition a b (n + 1) fun i => (x i : ℝ)) :
    IsIdempotentElem (piecewiseLinearInterpCLM n x) := by
  have hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ) := fun i hi => hx.step i (by omega)
  have h : ∀ f, piecewiseLinearInterpCLM n x (piecewiseLinearInterpCLM n x f)
      = piecewiseLinearInterpCLM n x f := by
    intro f
    refine ContinuousMap.ext fun t => ?_
    obtain ⟨j, hj, h1, h2⟩ := exists_mem_subinterval hx.first hx.last t
    rw [piecewiseLinearInterpCLM_apply_of_mem hstep _ hj h1 h2,
      piecewiseLinearInterpCLM_apply_of_mem hstep f hj h1 h2,
      piecewiseLinearInterpCLM_apply_node hstep f (by omega),
      piecewiseLinearInterpCLM_apply_node hstep f (by omega)]
  exact ContinuousLinearMap.ext h

/-- Let $x_i < x_{i+1}$ for all $i \le n$, let $j \le n$, and let $x_j \le t \le x_{j+1}$. Then
there is $\theta \in [0, 1]$ with $I f(t) = (1 - \theta) f(x_j) + \theta f(x_{j+1})$: the
interpolant is a convex combination of the two node values. -/
theorem exists_piecewiseLinearInterpCLM_apply_eq (hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ))
    (f : C(Set.Icc a b, ℝ)) {j : ℕ} (hj : j ≤ n) {t : Set.Icc a b}
    (h1 : (x j : ℝ) ≤ (t : ℝ)) (h2 : (t : ℝ) ≤ (x (j + 1) : ℝ)) :
    ∃ θ ∈ Set.Icc (0 : ℝ) 1,
      piecewiseLinearInterpCLM n x f t = (1 - θ) * f (x j) + θ * f (x (j + 1)) := by
  have hd : (0 : ℝ) < (x (j + 1) : ℝ) - (x j : ℝ) := sub_pos.mpr (hstep j hj)
  refine ⟨((t : ℝ) - (x j : ℝ)) / ((x (j + 1) : ℝ) - (x j : ℝ)),
    ⟨div_nonneg (by linarith) hd.le, (div_le_one hd).mpr (by linarith)⟩, ?_⟩
  rw [piecewiseLinearInterpCLM_apply_of_mem hstep f hj h1 h2]
  ring

/-- On a partition $a = x_0 < \dots < x_{n+1} = b$, the piecewise-linear interpolant satisfies
$\|I f\| \le \|f\|$ in the uniform norm. On each subinterval its value is a convex combination
of two values of $f$. -/
theorem norm_piecewiseLinearInterpCLM_apply_le
    (hx : IsIntervalPartition a b (n + 1) fun i => (x i : ℝ)) (f : C(Set.Icc a b, ℝ)) :
    ‖piecewiseLinearInterpCLM n x f‖ ≤ ‖f‖ := by
  have hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ) := fun i hi => hx.step i (by omega)
  refine (ContinuousMap.norm_le _ (norm_nonneg f)).mpr fun t => ?_
  obtain ⟨j, hj, h1, h2⟩ := exists_mem_subinterval hx.first hx.last t
  obtain ⟨θ, ⟨hθ0, hθ1⟩, hval⟩ := exists_piecewiseLinearInterpCLM_apply_eq hstep f hj h1 h2
  have hb1 : |f (x j)| ≤ ‖f‖ := by simpa using f.norm_coe_le_norm (x j)
  have hb2 : |f (x (j + 1))| ≤ ‖f‖ := by simpa using f.norm_coe_le_norm (x (j + 1))
  rw [Real.norm_eq_abs, hval]
  calc |(1 - θ) * f (x j) + θ * f (x (j + 1))|
      ≤ |(1 - θ) * f (x j)| + |θ * f (x (j + 1))| := abs_add_le _ _
    _ = (1 - θ) * |f (x j)| + θ * |f (x (j + 1))| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - θ), abs_of_nonneg hθ0]
    _ ≤ (1 - θ) * ‖f‖ + θ * ‖f‖ := by gcongr
    _ = ‖f‖ := by ring

/-- **The piecewise-linear interpolation operator has norm one.** On a partition
$a = x_0 < \dots < x_{n+1} = b$ of $[a, b]$,
$$\|I\| = 1.$$
This is Exercise 3.6.6 of [han2009theoretical].

The operator is a projection of norm one onto the continuous piecewise-linear functions of the
partition, so its Lebesgue constant is the best possible. -/
theorem norm_piecewiseLinearInterpCLM (hx : IsIntervalPartition a b (n + 1) fun i => (x i : ℝ)) :
    ‖piecewiseLinearInterpCLM n x‖ = 1 := by
  have hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ) := fun i hi => hx.step i (by omega)
  have hne : Nonempty (Set.Icc a b) := ⟨x 0⟩
  have hone : ‖(1 : C(Set.Icc a b, ℝ))‖ = 1 := by simp
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_) ?_
  · rw [one_mul]
    exact norm_piecewiseLinearInterpCLM_apply_le hx f
  · have hfix : piecewiseLinearInterpCLM n x 1 = 1 := by
      refine ContinuousMap.ext fun t => ?_
      obtain ⟨j, hj, h1, h2⟩ := exists_mem_subinterval hx.first hx.last t
      rw [piecewiseLinearInterpCLM_apply_of_mem hstep 1 hj h1 h2]
      simp
    have := (piecewiseLinearInterpCLM n x).le_opNorm (1 : C(Set.Icc a b, ℝ))
    rw [hfix, hone, mul_one] at this
    exact this

/-- **The error of piecewise-linear interpolation.** Let $a = x_0 < \dots < x_{n+1} = b$ be a
partition of $[a, b]$ with $x_{i+1} - x_i \le h$ for all $i$. Let
$g : \mathbb{R} \to \mathbb{R}$ be of class $C^2$, let $f \in C([a, b])$ agree with $g$ on
$[a, b]$, and let $|g''(t)| \le M$ for all $t \in [a, b]$. Then
$$\|f - I f\| \le \frac{h^2}{8} M.$$
This is (3.2.9) of [han2009theoretical], and §8.3 of [kress1998numerical].

The function $f$ is given through a $C^2$ function $g$ on $\mathbb{R}$, since $C([a, b])$
carries no derivative; only the values of $g''$ on $[a, b]$ are used. By
`piecewiseLinearInterpCLM_apply_of_mem`, on $[x_j, x_{j+1}]$ the interpolant is the Lagrange
interpolant at the two endpoints, so `Lagrange.exists_sub_interpolate_eq` with $n = 1$ applies,
and $|(t - u)(t - v)| \le (v - u)^2/4$ finishes the proof. -/
theorem norm_sub_piecewiseLinearInterpCLM_le
    (hx : IsIntervalPartition a b (n + 1) fun i => (x i : ℝ)) {g : ℝ → ℝ}
    (hg : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) g) {f : C(Set.Icc a b, ℝ)}
    (hf : ∀ t : Set.Icc a b, f t = g (t : ℝ)) {h M : ℝ}
    (hmesh : ∀ i ≤ n, (x (i + 1) : ℝ) - (x i : ℝ) ≤ h)
    (hM : ∀ t ∈ Set.Icc a b, |iteratedDeriv 2 g t| ≤ M) :
    ‖f - piecewiseLinearInterpCLM n x f‖ ≤ h ^ 2 / 8 * M := by
  have hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ) := fun i hi => hx.step i (by omega)
  classical
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM (x 0) (x 0).2)
  have hh0 : 0 ≤ h := le_trans (sub_nonneg.mpr (hstep 0 (Nat.zero_le n)).le)
    (hmesh 0 (Nat.zero_le n))
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro t
  obtain ⟨j, hj, h1, h2⟩ := exists_mem_subinterval hx.first hx.last t
  have huv : (x j : ℝ) < (x (j + 1) : ℝ) := hstep j hj
  -- the two nodes of the subinterval
  have hnodeinj : Function.Injective ![(x j : ℝ), (x (j + 1) : ℝ)] := by
    intro p q hpq
    fin_cases p <;> fin_cases q <;> simp_all [huv.ne, huv.ne']
  have hnodemem : ∀ i : Fin 2, ![(x j : ℝ), (x (j + 1) : ℝ)] i ∈
      Set.Icc ((x j : ℝ)) ((x (j + 1) : ℝ)) := by
    intro i
    fin_cases i <;> simp [Set.mem_Icc, huv.le]
  -- the affine polynomial through the two node values is the Lagrange interpolant
  obtain ⟨L, hL⟩ : ∃ L : ℝ[X], L = Polynomial.C (g (x j)) +
      Polynomial.C ((g (x (j + 1)) - g (x j)) / ((x (j + 1) : ℝ) - (x j : ℝ))) *
        (Polynomial.X - Polynomial.C ((x j : ℝ))) := ⟨_, rfl⟩
  have hne : ((x (j + 1) : ℝ) - (x j : ℝ)) ≠ 0 := sub_ne_zero.mpr huv.ne'
  have hLnat : L.natDegree ≤ 1 := by
    rw [hL]
    compute_degree
  have hLdeg : L.degree < ((Finset.univ : Finset (Fin 2)).card : WithBot ℕ) := by
    have hbound : L.degree ≤ ((1 : ℕ) : WithBot ℕ) :=
      L.degree_le_natDegree.trans (by exact_mod_cast hLnat)
    refine lt_of_le_of_lt hbound ?_
    simp
  have hLu : L.eval ((x j : ℝ)) = g (x j) := by rw [hL]; simp
  have hLv : L.eval ((x (j + 1) : ℝ)) = g (x (j + 1)) := by
    rw [hL]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_sub, Polynomial.eval_X]
    field_simp
    ring
  have hLeq : L = Lagrange.interpolate Finset.univ ![(x j : ℝ), (x (j + 1) : ℝ)]
      fun i => g (![(x j : ℝ), (x (j + 1) : ℝ)] i) :=
    Lagrange.eq_interpolate_of_eval_eq _ hnodeinj.injOn hLdeg (by
      intro i _
      fin_cases i <;> simpa using by first | exact hLu | exact hLv)
  -- the interpolation error on the subinterval
  obtain ⟨ξ, hξ, hξeq⟩ := Lagrange.exists_sub_interpolate_eq (n := 1) huv hg hnodeinj hnodemem
    (Set.mem_Icc.mpr ⟨h1, h2⟩)
  rw [← hLeq] at hξeq
  have hξmem : ξ ∈ Set.Icc a b :=
    ⟨le_trans (x j).2.1 hξ.1.le, le_trans hξ.2.le (x (j + 1)).2.2⟩
  have hprodeq : ∏ i : Fin 2, ((t : ℝ) - ![(x j : ℝ), (x (j + 1) : ℝ)] i)
      = ((t : ℝ) - (x j : ℝ)) * ((t : ℝ) - (x (j + 1) : ℝ)) := by
    simp [Fin.prod_univ_two]
  rw [hprodeq] at hξeq
  -- the local description of the interpolant
  have hPt : (piecewiseLinearInterpCLM n x f) t = L.eval ((t : ℝ)) := by
    rw [piecewiseLinearInterpCLM_apply_of_mem hstep f hj h1 h2, hL, hf (x j), hf (x (j + 1))]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_sub, Polynomial.eval_X]
    ring
  -- the two bounds
  have hprod : |((t : ℝ) - (x j : ℝ)) * ((t : ℝ) - (x (j + 1) : ℝ))| ≤ h ^ 2 / 4 := by
    have hd : (x (j + 1) : ℝ) - (x j : ℝ) ≤ h := hmesh j hj
    have hsq : ((x (j + 1) : ℝ) - (x j : ℝ)) ^ 2 ≤ h ^ 2 := by nlinarith
    have hnonpos : ((t : ℝ) - (x j : ℝ)) * ((t : ℝ) - (x (j + 1) : ℝ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr h1) (sub_nonpos.mpr h2)
    rw [abs_of_nonpos hnonpos, neg_mul_eq_mul_neg, neg_sub]
    nlinarith [sq_nonneg ((x (j + 1) : ℝ) + (x j : ℝ) - 2 * (t : ℝ))]
  have hfact : ((1 + 1).factorial : ℝ) = 2 := by norm_num
  calc ‖(f - piecewiseLinearInterpCLM n x f) t‖
      = |g (t : ℝ) - L.eval ((t : ℝ))| := by
        rw [ContinuousMap.sub_apply, Real.norm_eq_abs, hf t, hPt]
    _ = |iteratedDeriv 2 g ξ| / 2 * |((t : ℝ) - (x j : ℝ)) * ((t : ℝ) - (x (j + 1) : ℝ))| := by
        rw [hξeq, abs_mul, abs_div, hfact]
        norm_num
    _ ≤ M / 2 * (h ^ 2 / 4) :=
        mul_le_mul (by linarith [hM ξ hξmem]) hprod (abs_nonneg _) (by linarith)
    _ = h ^ 2 / 8 * M := by ring

/-- **The piecewise-linear interpolation error for a continuous function.** Let
$a = x_0 < \dots < x_{n+1} = b$ be a partition of $[a, b]$ with $x_{i+1} - x_i \le h$ for all
$i$, and let $f \in C([a, b])$. Then
$$\|f - I f\| \le \omega(f, h).$$
This is (3.2.8) of [han2009theoretical], and §8.3 of [kress1998numerical].

On each subinterval the interpolant is a convex combination of the two node values. So the error
is the same convex combination of $f(t) - f(x_j)$ and $f(t) - f(x_{j+1})$, and both nodes are
within $h$ of $t$. -/
theorem norm_sub_piecewiseLinearInterpCLM_le_modulus
    (hx : IsIntervalPartition a b (n + 1) fun i => (x i : ℝ)) (f : C(Set.Icc a b, ℝ)) {h : ℝ}
    (hmesh : ∀ i ≤ n, (x (i + 1) : ℝ) - (x i : ℝ) ≤ h) :
    ‖f - piecewiseLinearInterpCLM n x f‖ ≤ f.modulusOfContinuity h := by
  have hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ) := fun i hi => hx.step i (by omega)
  have hne : Nonempty (Set.Icc a b) := ⟨x 0⟩
  have hh0 : 0 ≤ h := le_trans (sub_nonneg.mpr (hstep 0 (Nat.zero_le n)).le)
    (hmesh 0 (Nat.zero_le n))
  rw [ContinuousMap.norm_le _ (f.modulusOfContinuity_nonneg hh0)]
  intro t
  obtain ⟨j, hj, h1, h2⟩ := exists_mem_subinterval hx.first hx.last t
  obtain ⟨θ, ⟨hθ0, hθ1⟩, hval⟩ := exists_piecewiseLinearInterpCLM_apply_eq hstep f hj h1 h2
  have e1 : |f t - f (x j)| ≤ f.modulusOfContinuity h := by
    refine ContinuousMap.le_modulusOfContinuity f ?_
    rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (by linarith)]
    exact le_trans (by linarith) (hmesh j hj)
  have e2 : |f t - f (x (j + 1))| ≤ f.modulusOfContinuity h := by
    refine ContinuousMap.le_modulusOfContinuity f ?_
    rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonpos (by linarith)]
    exact le_trans (by linarith) (hmesh j hj)
  have hrw : f t - ((1 - θ) * f (x j) + θ * f (x (j + 1)))
      = (1 - θ) * (f t - f (x j)) + θ * (f t - f (x (j + 1))) := by ring
  rw [ContinuousMap.sub_apply, Real.norm_eq_abs, hval, hrw]
  calc |(1 - θ) * (f t - f (x j)) + θ * (f t - f (x (j + 1)))|
      ≤ |(1 - θ) * (f t - f (x j))| + |θ * (f t - f (x (j + 1)))| := abs_add_le _ _
    _ = (1 - θ) * |f t - f (x j)| + θ * |f t - f (x (j + 1))| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - θ), abs_of_nonneg hθ0]
    _ ≤ (1 - θ) * f.modulusOfContinuity h + θ * f.modulusOfContinuity h := by gcongr
    _ = f.modulusOfContinuity h := by ring

open Filter Topology in
/-- **Piecewise-linear interpolation converges uniformly for every continuous function.** For each
$k$, let $a = y_{k,0} < \dots < y_{k,N_k+1} = b$ be a partition of $[a, b]$ with mesh at most
$h_k$, and let $h_k \to 0$. Then for every $f \in C([a, b])$ the piecewise-linear interpolants
of $f$ on these partitions converge uniformly to $f$. This is (3.2.8) of [han2009theoretical].

The bound is the modulus of continuity (`norm_sub_piecewiseLinearInterpCLM_le_modulus`), which
tends to zero with the mesh (`ContinuousMap.tendsto_modulusOfContinuity`). No differentiability
of $f$ is used. A projection method needs this statement, and not the $h^2$ bound for a $C^2$
function, for the hypothesis $P_n u \to u$ of the Banach–Steinhaus argument. -/
theorem tendsto_piecewiseLinearInterpCLM {N : ℕ → ℕ} {y : ℕ → ℕ → Set.Icc a b} {h : ℕ → ℝ}
    (hstep : ∀ n, ∀ i ≤ N n, (y n i : ℝ) < (y n (i + 1) : ℝ))
    (hfirst : ∀ n, (y n 0 : ℝ) = a) (hlast : ∀ n, (y n (N n + 1) : ℝ) = b)
    (hmesh : ∀ n, ∀ i ≤ N n, (y n (i + 1) : ℝ) - (y n i : ℝ) ≤ h n)
    (hh : Tendsto h atTop (𝓝 0)) (f : C(Set.Icc a b, ℝ)) :
    Tendsto (fun n => piecewiseLinearInterpCLM (N n) (y n) f) atTop (𝓝 f) := by
  have hne : Nonempty (Set.Icc a b) := ⟨y 0 0⟩
  have hh0 : ∀ n, 0 ≤ h n := fun n =>
    le_trans (sub_nonneg.mpr (hstep n 0 (Nat.zero_le _)).le) (hmesh n 0 (Nat.zero_le _))
  have hhw : Tendsto h atTop (𝓝[≥] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hh
      (Filter.Eventually.of_forall fun n => Set.mem_Ici.2 (hh0 n))
  have hmod : Tendsto (fun n => f.modulusOfContinuity (h n)) atTop (𝓝 0) :=
    (ContinuousMap.tendsto_modulusOfContinuity f).comp hhw
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hmod
  rw [norm_sub_rev]
  exact norm_sub_piecewiseLinearInterpCLM_le_modulus
    ⟨fun i hi => hstep n i (by omega), hfirst n, hlast n⟩ f (hmesh n)

end PiecewiseLinear

/-! ### Piecewise polynomial interpolation of degree $m$ -/

/-- **A panel node system of degree $m$.** The breakpoints $a = x_0 < x_1 < \dots < x_{n+1} = b$ cut
$[a, b]$ into $n + 1$ panels, and each panel $[x_j, x_{j+1}]$ carries $m + 1$ distinct
interpolation nodes $\nu_{j,0}, \dots, \nu_{j,m}$ in the panel, of which the first is $x_j$ and
the last is $x_{j+1}$.

The endpoint condition makes the panel interpolants agree where two panels meet, so that the
piecewise polynomial interpolant is continuous. The interior nodes are arbitrary. They are
usually the images of a fixed partition $0 = \mu_0 < \dots < \mu_m = 1$ of the unit interval
under the affine map onto the panel. The node $\nu_{j,i}$ is `node j i`. -/
structure IsPanelNodes {a b : ℝ} (n m : ℕ) (x : ℕ → Set.Icc a b)
    (node : ℕ → Fin (m + 1) → Set.Icc a b) : Prop where
  /-- The breakpoints increase: $x_i < x_{i+1}$ for all $i \le n$. -/
  step : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ)
  /-- The first breakpoint is the left endpoint of the interval: $x_0 = a$. -/
  first : (x 0 : ℝ) = a
  /-- The last breakpoint is the right endpoint of the interval: $x_{n+1} = b$. -/
  last : (x (n + 1) : ℝ) = b
  /-- The nodes of a panel lie in that panel: $\nu_{j,i} \in [x_j, x_{j+1}]$ for all $j \le n$. -/
  mem : ∀ j ≤ n, ∀ i, ((node j i : ℝ)) ∈ Set.Icc ((x j : ℝ)) ((x (j + 1) : ℝ))
  /-- The nodes of a panel are distinct: $i \mapsto \nu_{j,i}$ is injective for all $j \le n$. -/
  injective : ∀ j ≤ n, Function.Injective fun i => ((node j i : ℝ))
  /-- The first node of a panel is its left endpoint: $\nu_{j,0} = x_j$ for all $j \le n$. -/
  node_zero : ∀ j ≤ n, node j 0 = x j
  /-- The last node of a panel is its right endpoint: $\nu_{j,m} = x_{j+1}$ for all $j \le n$. -/
  node_last : ∀ j ≤ n, node j (Fin.last m) = x (j + 1)

/-- The **panel interpolant**: the Lagrange interpolation polynomial of degree at most $m$ of $f$ at
the $m + 1$ nodes $\nu_{j,0}, \dots, \nu_{j,m}$ of the panel $[x_j, x_{j+1}]$. -/
noncomputable def panelPoly {a b : ℝ} {m : ℕ} (node : ℕ → Fin (m + 1) → Set.Icc a b) (j : ℕ)
    (f : C(Set.Icc a b, ℝ)) : ℝ[X] :=
  Lagrange.interpolate Finset.univ (fun p => ((node j p : ℝ))) fun i => f (node j i)

/-- The $i$-th Lagrange basis function of the nodes of the panel $[x_j, x_{j+1}]$, **clamped to that
panel**: its value at $t$ is the value of the basis polynomial at the point of $[x_j, x_{j+1}]$
nearest to $t$.

Clamping lets the piecewise polynomial interpolant be written as a sum over the panels, as
`piecewiseLinearRamp` does for degree one. In `piecewisePolyInterpCLM_apply`, the panels to the
left of the evaluation point contribute their full increment, those to the right contribute
nothing, and the sum telescopes. -/
noncomputable def panelBasis {a b : ℝ} {m : ℕ} (x : ℕ → Set.Icc a b)
    (node : ℕ → Fin (m + 1) → Set.Icc a b) (j : ℕ) (i : Fin (m + 1)) : C(Set.Icc a b, ℝ) :=
  ⟨fun t => (Lagrange.basis Finset.univ (fun p => ((node j p : ℝ))) i).eval
      (min (max (t : ℝ) ((x j : ℝ))) ((x (j + 1) : ℝ))),
    (Polynomial.continuous _).comp
      ((continuous_subtype_val.max continuous_const).min continuous_const)⟩

/-- The value of a clamped panel basis function at $t$ is the value of the basis polynomial at
$\min(\max(t, x_j), x_{j+1})$. -/
@[simp]
theorem panelBasis_apply {a b : ℝ} {m : ℕ} (x : ℕ → Set.Icc a b)
    (node : ℕ → Fin (m + 1) → Set.Icc a b) (j : ℕ) (i : Fin (m + 1)) (t : Set.Icc a b) :
    panelBasis x node j i t = (Lagrange.basis Finset.univ (fun p => ((node j p : ℝ))) i).eval
      (min (max (t : ℝ) ((x j : ℝ))) ((x (j + 1) : ℝ))) := rfl

/-- **The panel interpolation operator**: the operator on $C([a, b])$ that sends $f$ to the function
whose value at $t$ is the panel interpolant of $f$ on $[x_j, x_{j+1}]$, evaluated at the point
of that panel nearest to $t$. -/
noncomputable def panelInterpCLM {a b : ℝ} (m : ℕ) (x : ℕ → Set.Icc a b)
    (node : ℕ → Fin (m + 1) → Set.Icc a b) (j : ℕ) :
    C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ) :=
  ∑ i, (ContinuousMap.evalCLM ℝ (node j i)).smulRight (panelBasis x node j i)

/-- **Piecewise polynomial interpolation of degree $m$** on the partition
$a = x_0 < x_1 < \dots < x_{n+1} = b$ of $[a, b]$: the bounded operator on $C([a, b])$ that
sends $f$ to the continuous function that agrees on each panel $[x_j, x_{j+1}]$ with the
polynomial of degree at most $m$ that interpolates $f$ at the $m + 1$ nodes of that panel. This
is §12.3.2 and (12.5.32) of [han2009theoretical].

The operator is defined as the value at the first breakpoint plus the increments
$Q_j f(t) - Q_j f(x_j)$ of the clamped panel interpolation operators $Q_j$ (`panelInterpCLM`).
This sum telescopes to the interpolant of the panel that contains $t$
(`piecewisePolyInterpCLM_apply_of_mem`). Continuity across a breakpoint holds because both
panels that meet there interpolate $f$ at it. Linearity, boundedness and continuity are
immediate, as they are for `piecewiseLinearInterpCLM`, which is the case $m = 1$. -/
noncomputable def piecewisePolyInterpCLM {a b : ℝ} (n m : ℕ) (x : ℕ → Set.Icc a b)
    (node : ℕ → Fin (m + 1) → Set.Icc a b) : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ) :=
  (ContinuousMap.evalCLM ℝ (x 0)).smulRight 1 +
    ∑ j ∈ Finset.range (n + 1),
      (panelInterpCLM m x node j -
        (ContinuousMap.evalCLM ℝ (x j)).smulRight (1 : C(Set.Icc a b, ℝ)) ∘L
          panelInterpCLM m x node j)

section PiecewisePolynomial

variable {a b : ℝ} {n m : ℕ} {x : ℕ → Set.Icc a b} {node : ℕ → Fin (m + 1) → Set.Icc a b}

/-- The value of the panel interpolation operator at $t$ is the panel interpolant evaluated at
$\min(\max(t, x_j), x_{j+1})$. -/
theorem panelInterpCLM_apply (m : ℕ) (x : ℕ → Set.Icc a b)
    (node : ℕ → Fin (m + 1) → Set.Icc a b) (j : ℕ) (f : C(Set.Icc a b, ℝ)) (t : Set.Icc a b) :
    panelInterpCLM m x node j f t
      = (panelPoly node j f).eval (min (max (t : ℝ) ((x j : ℝ))) ((x (j + 1) : ℝ))) := by
  simp [panelInterpCLM, panelPoly, Lagrange.interpolate_apply, Polynomial.eval_finsetSum]

/-- The value of the piecewise polynomial interpolant at $t$ is $f(x_0) + \sum_{j=0}^{n} \bigl(Q_j
f(t) - Q_j f(x_j)\bigr)$, where $Q_j$ is the panel interpolation operator of the panel
$[x_j, x_{j+1}]$. -/
theorem piecewisePolyInterpCLM_apply (n m : ℕ) (x : ℕ → Set.Icc a b)
    (node : ℕ → Fin (m + 1) → Set.Icc a b) (f : C(Set.Icc a b, ℝ)) (t : Set.Icc a b) :
    piecewisePolyInterpCLM n m x node f t = f (x 0) +
      ∑ j ∈ Finset.range (n + 1),
        (panelInterpCLM m x node j f t - panelInterpCLM m x node j f (x j)) := by
  simp [piecewisePolyInterpCLM]

/-- For a panel node system and $j \le n$, the panel interpolant of the panel $[x_j, x_{j+1}]$ takes
the value $f(x_j)$ at the left endpoint $x_j$. -/
theorem eval_panelPoly_left (h : IsPanelNodes n m x node) (f : C(Set.Icc a b, ℝ)) {j : ℕ}
    (hj : j ≤ n) : (panelPoly node j f).eval ((x j : ℝ)) = f (x j) := by
  have hval := Lagrange.eval_interpolate_at_node (s := (Finset.univ : Finset (Fin (m + 1))))
    (v := fun p => ((node j p : ℝ))) (r := fun i => f (node j i)) (i := (0 : Fin (m + 1)))
    (h.injective j hj).injOn (Finset.mem_univ _)
  rw [h.node_zero j hj] at hval
  exact hval

/-- For a panel node system and $j \le n$, the panel interpolant of the panel $[x_j, x_{j+1}]$ takes
the value $f(x_{j+1})$ at the right endpoint $x_{j+1}$. -/
theorem eval_panelPoly_right (h : IsPanelNodes n m x node) (f : C(Set.Icc a b, ℝ)) {j : ℕ}
    (hj : j ≤ n) : (panelPoly node j f).eval ((x (j + 1) : ℝ)) = f (x (j + 1)) := by
  have hval := Lagrange.eval_interpolate_at_node (s := (Finset.univ : Finset (Fin (m + 1))))
    (v := fun p => ((node j p : ℝ))) (r := fun i => f (node j i)) (i := Fin.last m)
    (h.injective j hj).injOn (Finset.mem_univ _)
  rw [h.node_last j hj] at hval
  exact hval

/-- **The local description of the piecewise polynomial interpolant.** Let the nodes form a panel
node system, let $k \le n$, and let $t \in [a, b]$ with $x_k \le t \le x_{k+1}$. Then
$I f(t) = p_k(t)$, where $p_k$ is the Lagrange interpolation polynomial of $f$ at the nodes of
the panel $[x_k, x_{k+1}]$. -/
theorem piecewisePolyInterpCLM_apply_of_mem (h : IsPanelNodes n m x node) (f : C(Set.Icc a b, ℝ))
    {k : ℕ} (hk : k ≤ n) {t : Set.Icc a b} (h1 : (x k : ℝ) ≤ (t : ℝ))
    (h2 : (t : ℝ) ≤ (x (k + 1) : ℝ)) :
    piecewisePolyInterpCLM n m x node f t = (panelPoly node k f).eval ((t : ℝ)) := by
  classical
  set F : ℕ → ℝ := fun j =>
    panelInterpCLM m x node j f t - panelInterpCLM m x node j f (x j) with hF
  have hself : ∀ j ≤ n, panelInterpCLM m x node j f (x j) = f (x j) := by
    intro j hj
    rw [panelInterpCLM_apply, max_self, min_eq_left (h.step j hj).le, eval_panelPoly_left h f hj]
  -- the panels to the left of `t` contribute their full increment
  have hbefore : ∀ j < k, F j = f (x (j + 1)) - f (x j) := by
    intro j hj
    have hjn : j ≤ n := by omega
    have hle : (x (j + 1) : ℝ) ≤ (t : ℝ) :=
      (piecewiseLinearInterpCLM.le_node_of_le h.step (by omega) (by omega)).trans h1
    have hlej : (x j : ℝ) ≤ (t : ℝ) := (h.step j hjn).le.trans hle
    rw [hF]
    simp only
    rw [panelInterpCLM_apply, max_eq_left hlej, min_eq_right hle,
      eval_panelPoly_right h f hjn, hself j hjn]
  -- the panels to the right of `t` contribute nothing
  have hafter : ∀ j, k < j → j ≤ n → F j = 0 := by
    intro j hj hjn
    have hge : (t : ℝ) ≤ (x j : ℝ) :=
      h2.trans (piecewiseLinearInterpCLM.le_node_of_le h.step (by omega) (by omega))
    rw [hF]
    simp only
    rw [panelInterpCLM_apply, max_eq_right hge, min_eq_left (h.step j hjn).le,
      eval_panelPoly_left h f hjn, hself j hjn, sub_self]
  have hat : F k = (panelPoly node k f).eval ((t : ℝ)) - f (x k) := by
    rw [hF]
    simp only
    rw [panelInterpCLM_apply, max_eq_left h1, min_eq_left h2, hself k hk]
  rw [piecewisePolyInterpCLM_apply]
  have hsum : ∑ j ∈ Finset.range (n + 1), F j = f (x k) - f (x 0) + F k := by
    have hsplit : ∑ j ∈ Finset.range (n + 1), F j
        = ∑ j ∈ Finset.range k, F j + ∑ j ∈ Finset.Ico k (n + 1), F j := by
      simp only [Finset.range_eq_Ico]
      exact (Finset.sum_Ico_consecutive F (Nat.zero_le k) (by omega)).symm
    have htail : ∑ j ∈ Finset.Ico k (n + 1), F j = F k := by
      rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)]
      have hz : ∑ j ∈ Finset.Ico (k + 1) (n + 1), F j = 0 :=
        Finset.sum_eq_zero fun j hj => by
          rw [Finset.mem_Ico] at hj
          exact hafter j (by omega) (by omega)
      rw [hz, add_zero]
    have hhead : ∑ j ∈ Finset.range k, F j = f (x k) - f (x 0) := by
      rw [Finset.sum_congr rfl fun j hj => hbefore j (Finset.mem_range.mp hj)]
      exact Finset.sum_range_sub (fun j => f (x j)) k
    rw [hsplit, htail, hhead]
  rw [hsum, hat]
  ring

end PiecewisePolynomial


/-- **A uniform local Lebesgue constant** for a panel node system: a number $\Lambda$ with
$$\sum_{i=0}^{m} |\ell_{j,i}(s)| \le \Lambda \qquad \text{for all } j \le n \text{ and } s \in
  [x_j, x_{j+1}],$$
where $\ell_{j,0}, \dots, \ell_{j,m}$ are the Lagrange basis polynomials of the nodes of the
panel $[x_j, x_{j+1}]$. It bounds the operator norm of piecewise polynomial interpolation
(`norm_piecewisePolyInterpCLM_le`).

If the nodes of every panel are the images of one fixed partition
$0 = \mu_0 < \dots < \mu_m = 1$ of the unit interval under the affine map onto the panel, then
the basis functions are the same functions of the normalized variable on every panel. Then the
smallest such $\Lambda$ is the Lebesgue constant of that partition alone, and it does not depend
on the mesh. -/
def IsPanelLebesgueBound {a b : ℝ} (n m : ℕ) (x : ℕ → Set.Icc a b)
    (node : ℕ → Fin (m + 1) → Set.Icc a b) (Λ : ℝ) : Prop :=
  ∀ j ≤ n, ∀ s ∈ Set.Icc ((x j : ℝ)) ((x (j + 1) : ℝ)),
    ∑ i, |(Lagrange.basis Finset.univ (fun p => ((node j p : ℝ))) i).eval s| ≤ Λ

section PiecewisePolynomialApi

variable {a b : ℝ} {n m : ℕ} {x : ℕ → Set.Icc a b} {node : ℕ → Fin (m + 1) → Set.Icc a b}

/-- For a panel node system, the piecewise polynomial interpolant agrees with $f$ at every
interpolation node $\nu_{j,i}$, $j \le n$. -/
theorem piecewisePolyInterpCLM_apply_node (h : IsPanelNodes n m x node) (f : C(Set.Icc a b, ℝ))
    {j : ℕ} (hj : j ≤ n) (i : Fin (m + 1)) :
    piecewisePolyInterpCLM n m x node f (node j i) = f (node j i) := by
  have hmem := h.mem j hj i
  rw [piecewisePolyInterpCLM_apply_of_mem h f hj hmem.1 hmem.2, panelPoly]
  exact Lagrange.eval_interpolate_at_node _ (h.injective j hj).injOn (Finset.mem_univ i)

/-- For a panel node system, the piecewise polynomial interpolant agrees with $f$ at every
breakpoint $x_j$, $j \le n + 1$. -/
theorem piecewisePolyInterpCLM_apply_breakpoint (h : IsPanelNodes n m x node)
    (f : C(Set.Icc a b, ℝ)) {j : ℕ} (hj : j ≤ n + 1) :
    piecewisePolyInterpCLM n m x node f (x j) = f (x j) := by
  rcases Nat.lt_or_ge j (n + 1) with hlt | hge
  · have hjn : j ≤ n := by omega
    have hval := piecewisePolyInterpCLM_apply_node h f hjn 0
    rwa [h.node_zero j hjn] at hval
  · have hje : j = n + 1 := le_antisymm hj hge
    subst hje
    have hval := piecewisePolyInterpCLM_apply_node h f (le_refl n) (Fin.last m)
    rwa [h.node_last n le_rfl] at hval

/-- For a panel node system, the piecewise polynomial interpolation operator is a projection:
$I \circ I = I$. A function that is a polynomial of degree at most $m$ on each panel is its own
panel interpolant. -/
theorem isIdempotentElem_piecewisePolyInterpCLM (h : IsPanelNodes n m x node) :
    IsIdempotentElem (piecewisePolyInterpCLM n m x node) := by
  have hfun : ∀ f, piecewisePolyInterpCLM n m x node (piecewisePolyInterpCLM n m x node f)
      = piecewisePolyInterpCLM n m x node f := by
    intro f
    refine ContinuousMap.ext fun t => ?_
    obtain ⟨k, hk, h1, h2⟩ := exists_mem_subinterval h.first h.last t
    have hr : (fun i => (piecewisePolyInterpCLM n m x node f) (node k i))
        = fun i => f (node k i) := funext fun i => piecewisePolyInterpCLM_apply_node h f hk i
    rw [piecewisePolyInterpCLM_apply_of_mem h _ hk h1 h2,
      piecewisePolyInterpCLM_apply_of_mem h f hk h1 h2, panelPoly, panelPoly, hr]
  exact ContinuousLinearMap.ext hfun

/-- For a panel node system, every uniform local Lebesgue constant $\Lambda$ is nonnegative. -/
theorem IsPanelLebesgueBound.nonneg (h : IsPanelNodes n m x node) {Λ : ℝ}
    (hΛ : IsPanelLebesgueBound n m x node Λ) : 0 ≤ Λ :=
  le_trans (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (hΛ 0 (Nat.zero_le n) ((x 0 : ℝ)) ⟨le_rfl, (h.step 0 (Nat.zero_le n)).le⟩)

/-- **A Lebesgue bound from the shape of the panel node systems alone.** Let the nodes form a panel
node system, let $\rho \in \mathbb{R}$, and for each $j \le n$ let $d_j > 0$ be such that
$x_{j+1} - x_j \le \rho\, d_j$ and $|\nu_{j,i} - \nu_{j,i'}| \ge d_j$ for all $i \neq i'$. Then
$$\Lambda = (m + 1)\, \rho^m$$
is a uniform local Lebesgue constant.

The separation $d_j$ may vary from panel to panel; only the ratio $\rho$ is uniform. A graded
mesh needs this: with the nodes at fixed fractions of every panel, $d_j$ and the length of the
panel are both proportional to that length, so $\rho$ is the same for every panel of every mesh
of the family, however unequal the panels are. The proof applies `Lagrange.abs_eval_basis_le` on
each panel. -/
theorem isPanelLebesgueBound_of_sep (h : IsPanelNodes n m x node) {ρ : ℝ} {d : ℕ → ℝ}
    (hd : ∀ j ≤ n, 0 < d j) (hD : ∀ j ≤ n, (x (j + 1) : ℝ) - (x j : ℝ) ≤ ρ * d j)
    (hsep : ∀ j ≤ n, ∀ i i' : Fin (m + 1), i ≠ i' → d j ≤ |((node j i : ℝ)) - ((node j i' : ℝ))|) :
    IsPanelLebesgueBound n m x node ((m + 1) * ρ ^ m) := by
  intro j hj s hs
  have hcard : ∀ i : Fin (m + 1),
      ((Finset.univ : Finset (Fin (m + 1))).erase i).card = m := fun i => by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  have hterm : ∀ i : Fin (m + 1),
      |(Lagrange.basis Finset.univ (fun p => ((node j p : ℝ))) i).eval s| ≤ ρ ^ m := by
    intro i
    have hnear : ∀ q : Fin (m + 1), |s - ((node j q : ℝ))| ≤ ρ * d j := by
      intro q
      have hq := h.mem j hj q
      have hjD := hD j hj
      rw [abs_sub_le_iff]
      exact ⟨by linarith [hs.1, hs.2, hq.1, hq.2], by linarith [hs.1, hs.2, hq.1, hq.2]⟩
    have hbound := Lagrange.abs_eval_basis_le (fun p => ((node j p : ℝ))) i (hd j hj) hnear
      (fun q hq => hsep j hj i q (Ne.symm hq))
    rw [hcard i, mul_div_assoc, div_self (ne_of_gt (hd j hj)), mul_one] at hbound
    exact hbound
  calc ∑ i, |(Lagrange.basis Finset.univ (fun p => ((node j p : ℝ))) i).eval s|
      ≤ ∑ _i : Fin (m + 1), ρ ^ m := Finset.sum_le_sum fun i _ => hterm i
    _ = (m + 1) * ρ ^ m := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num

/-- **A Lebesgue bound for nodes at fixed fractions of the panels.** Let $\iota$ be a finite set of
patterns, and for each $k \in \iota$ let $\mu_k = (\mu_{k,0}, \dots, \mu_{k,m})$ have distinct
entries. Then there is a constant $\Lambda$ with the following property. Let
$a, b \in \mathbb{R}$, let the nodes form a panel node system on $[a, b]$ with $n + 1$ panels,
and let $c$ assign a pattern to each panel such that
$$\nu_{j,i} = x_j + \mu_{c(j),i}\, (x_{j+1} - x_j) \qquad \text{for all } j \le n \text{ and all
  } i.$$
Then $\Lambda$ is a uniform local Lebesgue constant for this system. The interval, the number of
panels and the lengths of the panels are arbitrary.

A graded mesh needs this: its panels shrink towards an endpoint, while the nodes keep their
positions relative to the panel that contains them. Several patterns are allowed because a mesh
graded towards both endpoints uses one pattern on the panels of the left half and its reflection
$i \mapsto 1 - \mu_{m-i}$ on those of the right half. The proof is `isPanelLebesgueBound_of_sep`
with a separation proportional to the length of the panel; the ratio is the reciprocal of the
smallest gap between two entries of a pattern. -/
theorem exists_isPanelLebesgueBound_of_affine {ι : Type*} [Finite ι] {μ : ι → Fin (m + 1) → ℝ}
    (hμ : ∀ k, Function.Injective (μ k)) :
    ∃ Λ : ℝ, ∀ {a b : ℝ} {n : ℕ} {x : ℕ → Set.Icc a b}
      {node : ℕ → Fin (m + 1) → Set.Icc a b} {c : ℕ → ι}, IsPanelNodes n m x node →
      (∀ j ≤ n, ∀ i, (node j i : ℝ)
        = (x j : ℝ) + μ (c j) i * ((x (j + 1) : ℝ) - (x j : ℝ))) →
      IsPanelLebesgueBound n m x node Λ := by
  classical
  cases nonempty_fintype ι
  -- a uniform separation of the entries of the patterns
  obtain ⟨d, hd0, hd⟩ : ∃ d : ℝ, 0 < d ∧
      ∀ (k : ι) (i i' : Fin (m + 1)), i ≠ i' → d ≤ |μ k i - μ k i'| := by
    by_cases hS : (Finset.univ.filter
        fun p : ι × Fin (m + 1) × Fin (m + 1) => p.2.1 ≠ p.2.2).Nonempty
    · refine ⟨(Finset.univ.filter fun p : ι × Fin (m + 1) × Fin (m + 1) => p.2.1 ≠ p.2.2).inf' hS
        (fun p => |μ p.1 p.2.1 - μ p.1 p.2.2|), ?_, fun k i i' hii => ?_⟩
      · rw [Finset.lt_inf'_iff]
        intro p hp
        exact abs_pos.mpr (sub_ne_zero.mpr fun hcon =>
          (Finset.mem_filter.mp hp).2 (hμ p.1 hcon))
      · exact Finset.inf'_le (fun p : ι × Fin (m + 1) × Fin (m + 1) => |μ p.1 p.2.1 - μ p.1 p.2.2|)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ (k, i, i'), hii⟩)
    · exact ⟨1, one_pos, fun k i i' hii =>
        absurd ⟨(k, i, i'), Finset.mem_filter.mpr ⟨Finset.mem_univ (k, i, i'), hii⟩⟩ hS⟩
  refine ⟨(m + 1) * (1 / d) ^ m, ?_⟩
  intro a b n x node c h hnode
  refine isPanelLebesgueBound_of_sep h
    (d := fun j => d * ((x (j + 1) : ℝ) - (x j : ℝ))) (ρ := 1 / d)
    (fun j hj => mul_pos hd0 (sub_pos.mpr (h.step j hj))) (fun j hj => ?_)
    (fun j hj i i' hii => ?_)
  · rw [← mul_assoc, one_div, inv_mul_cancel₀ (ne_of_gt hd0), one_mul]
  · have hlen : (0 : ℝ) < (x (j + 1) : ℝ) - (x j : ℝ) := sub_pos.mpr (h.step j hj)
    rw [hnode j hj i, hnode j hj i']
    have hrw : ((x j : ℝ) + μ (c j) i * ((x (j + 1) : ℝ) - (x j : ℝ)))
        - ((x j : ℝ) + μ (c j) i' * ((x (j + 1) : ℝ) - (x j : ℝ)))
        = (μ (c j) i - μ (c j) i') * ((x (j + 1) : ℝ) - (x j : ℝ)) := by ring
    rw [hrw, abs_mul, abs_of_pos hlen]
    exact mul_le_mul_of_nonneg_right (hd (c j) i i' hii) hlen.le

/-- **The piecewise polynomial interpolant is bounded by the local Lebesgue constant.** For a panel
node system with a uniform local Lebesgue constant $\Lambda$ and every $f \in C([a, b])$,
$\|I f\| \le \Lambda \|f\|$. On the panel that contains the evaluation point, the interpolant is
the combination $\sum_i f(\nu_{k,i})\, \ell_{k,i}$ of the basis functions of the panel. -/
theorem norm_piecewisePolyInterpCLM_apply_le (h : IsPanelNodes n m x node) {Λ : ℝ}
    (hΛ : IsPanelLebesgueBound n m x node Λ) (f : C(Set.Icc a b, ℝ)) :
    ‖piecewisePolyInterpCLM n m x node f‖ ≤ Λ * ‖f‖ := by
  have hΛ0 : 0 ≤ Λ := hΛ.nonneg h
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro t
  obtain ⟨k, hk, h1, h2⟩ := exists_mem_subinterval h.first h.last t
  rw [Real.norm_eq_abs, piecewisePolyInterpCLM_apply_of_mem h f hk h1 h2, panelPoly,
    Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
  calc |∑ i, (Polynomial.C (f (node k i)) *
        Lagrange.basis Finset.univ (fun p => ((node k p : ℝ))) i).eval ((t : ℝ))|
      ≤ ∑ i, |(Polynomial.C (f (node k i)) *
          Lagrange.basis Finset.univ (fun p => ((node k p : ℝ))) i).eval ((t : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ‖f‖ *
          |(Lagrange.basis Finset.univ (fun p => ((node k p : ℝ))) i).eval ((t : ℝ))| := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [Polynomial.eval_mul, Polynomial.eval_C, abs_mul]
        exact mul_le_mul_of_nonneg_right (by simpa using f.norm_coe_le_norm (node k i))
          (abs_nonneg _)
    _ = ‖f‖ * ∑ i, |(Lagrange.basis Finset.univ (fun p => ((node k p : ℝ))) i).eval ((t : ℝ))| :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ ‖f‖ * Λ :=
        mul_le_mul_of_nonneg_left (hΛ k hk ((t : ℝ)) ⟨h1, h2⟩) (norm_nonneg f)
    _ = Λ * ‖f‖ := mul_comm _ _

/-- **The operator norm of piecewise polynomial interpolation is at most the local Lebesgue
constant.** Let the nodes form a panel node system, and let $\Lambda$ be a uniform local
Lebesgue constant for it. Then
$$\|I\| \le \Lambda.$$
The bound is uniform in the mesh whenever $\Lambda$ is. -/
theorem norm_piecewisePolyInterpCLM_le (h : IsPanelNodes n m x node) {Λ : ℝ}
    (hΛ : IsPanelLebesgueBound n m x node Λ) : ‖piecewisePolyInterpCLM n m x node‖ ≤ Λ :=
  ContinuousLinearMap.opNorm_le_bound _ (hΛ.nonneg h) fun f =>
    norm_piecewisePolyInterpCLM_apply_le h hΛ f

/-- **The error formula of piecewise polynomial interpolation on one panel, for a function that is
smooth only near that panel.** Let the nodes form a panel node system, let $k \le n$, let $U$ be
an open set that contains $[x_k, x_{k+1}]$, and let $G$ be of class $C^{m+1}$ on $U$. Let
$f \in C([a, b])$ agree with $G$ on $[a, b]$, and let $x_k \le t \le x_{k+1}$. Then there is
$\xi \in (x_k, x_{k+1})$ with
$$f(t) - I f(t) = \frac{G^{(m+1)}(\xi)}{(m + 1)!} \prod_{i=0}^{m} (t - \nu_{k,i}).$$

Only the smoothness of $G$ near the panel is used. So a function that is singular at an endpoint
of $[a, b]$, as the solution of a weakly singular equation is, still obeys the formula on every
panel away from the singularity. -/
theorem exists_sub_piecewisePolyInterpCLM_apply_eq_of_contDiffOn (h : IsPanelNodes n m x node)
    {G : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) {k : ℕ} (hk : k ≤ n)
    (hUsub : Set.Icc ((x k : ℝ)) ((x (k + 1) : ℝ)) ⊆ U)
    (hG : ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) G U) {f : C(Set.Icc a b, ℝ)}
    (hf : ∀ t : Set.Icc a b, f t = G ((t : ℝ))) {t : Set.Icc a b}
    (h1 : (x k : ℝ) ≤ (t : ℝ)) (h2 : (t : ℝ) ≤ (x (k + 1) : ℝ)) :
    ∃ ξ ∈ Set.Ioo ((x k : ℝ)) ((x (k + 1) : ℝ)),
      f t - piecewisePolyInterpCLM n m x node f t
        = iteratedDeriv (m + 1) G ξ / (m + 1).factorial * ∏ i, ((t : ℝ) - ((node k i : ℝ))) := by
  obtain ⟨ξ, hξ, hξeq⟩ := Lagrange.exists_sub_interpolate_eq_of_contDiffOn (n := m) (h.step k hk)
    hU hUsub hG (h.injective k hk) (h.mem k hk) (Set.mem_Icc.mpr ⟨h1, h2⟩)
  refine ⟨ξ, hξ, ?_⟩
  have hr : (fun i => f (node k i)) = fun i => G ((node k i : ℝ)) := funext fun i => hf _
  rw [piecewisePolyInterpCLM_apply_of_mem h f hk h1 h2, hf t, panelPoly, hr]
  exact hξeq

/-- **The error formula of piecewise polynomial interpolation.** Let the nodes form a panel node
system, let $G : \mathbb{R} \to \mathbb{R}$ be of class $C^{m+1}$, and let $f \in C([a, b])$
agree with $G$ on $[a, b]$. Let $k \le n$ and $x_k \le t \le x_{k+1}$. Then there is
$\xi \in (x_k, x_{k+1})$ with
$$f(t) - I f(t) = \frac{G^{(m+1)}(\xi)}{(m + 1)!} \prod_{i=0}^{m} (t - \nu_{k,i}).$$

The function $f$ is given through a $C^{m+1}$ function $G$ on $\mathbb{R}$, since $C([a, b])$
carries no derivative. On the panel that contains $t$, the interpolant is the Lagrange
interpolant at the nodes of that panel, so the Lagrange error formula applies on the panel. -/
theorem exists_sub_piecewisePolyInterpCLM_apply_eq (h : IsPanelNodes n m x node) {G : ℝ → ℝ}
    (hG : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) G) {f : C(Set.Icc a b, ℝ)}
    (hf : ∀ t : Set.Icc a b, f t = G ((t : ℝ))) {k : ℕ} (hk : k ≤ n) {t : Set.Icc a b}
    (h1 : (x k : ℝ) ≤ (t : ℝ)) (h2 : (t : ℝ) ≤ (x (k + 1) : ℝ)) :
    ∃ ξ ∈ Set.Ioo ((x k : ℝ)) ((x (k + 1) : ℝ)),
      f t - piecewisePolyInterpCLM n m x node f t
        = iteratedDeriv (m + 1) G ξ / (m + 1).factorial * ∏ i, ((t : ℝ) - ((node k i : ℝ))) :=
  exists_sub_piecewisePolyInterpCLM_apply_eq_of_contDiffOn h isOpen_univ hk (Set.subset_univ _)
    hG.contDiffOn hf h1 h2

/-- **The error of piecewise polynomial interpolation of degree $m$.** Let the nodes form a panel
node system, let $G : \mathbb{R} \to \mathbb{R}$ be of class $C^{m+1}$, and let
$f \in C([a, b])$ agree with $G$ on $[a, b]$. Let $W$ bound the nodal polynomial of every panel
on that panel, $|\prod_i (s - \nu_{j,i})| \le W$ for all $j \le n$ and $s \in [x_j, x_{j+1}]$,
and let $|G^{(m+1)}(s)| \le M$ for all $s \in [a, b]$. Then
$$\|f - I f\| \le \frac{W}{(m + 1)!} M.$$

For equally spaced panels of length $h$ with the nodes at the breakpoints, one may take
$W = h^{m+1}$. The sharp value of $W$ is smaller and gives the classical constants: $W = h^2/4$
for $m = 1$, which gives $h^2 \|G''\|/8$, and $W = 2\sqrt{3} h^3/9$ on a panel of length $2h$
with three equispaced nodes for $m = 2$ (`abs_add_mul_mul_sub_le`), which gives
$\sqrt{3} h^3 \|G'''\|/27$. -/
theorem norm_sub_piecewisePolyInterpCLM_le (h : IsPanelNodes n m x node) {G : ℝ → ℝ}
    (hG : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) G) {f : C(Set.Icc a b, ℝ)}
    (hf : ∀ t : Set.Icc a b, f t = G ((t : ℝ))) {W M : ℝ}
    (hW : ∀ j ≤ n, ∀ s ∈ Set.Icc ((x j : ℝ)) ((x (j + 1) : ℝ)),
      |∏ i, (s - ((node j i : ℝ)))| ≤ W)
    (hM : ∀ s ∈ Set.Icc a b, |iteratedDeriv (m + 1) G s| ≤ M) :
    ‖f - piecewisePolyInterpCLM n m x node f‖ ≤ W / (m + 1).factorial * M := by
  have hab : a ≤ b := (x 0).2.1.trans (x 0).2.2
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM a ⟨le_rfl, hab⟩)
  have hW0 : 0 ≤ W := le_trans (abs_nonneg _)
    (hW 0 (Nat.zero_le n) ((x 0 : ℝ)) ⟨le_rfl, (h.step 0 (Nat.zero_le n)).le⟩)
  have hfact : (0 : ℝ) < (m + 1).factorial := by
    exact_mod_cast Nat.factorial_pos (m + 1)
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro t
  obtain ⟨k, hk, h1, h2⟩ := exists_mem_subinterval h.first h.last t
  obtain ⟨ξ, hξ, hξeq⟩ := exists_sub_piecewisePolyInterpCLM_apply_eq h hG hf hk h1 h2
  have hξmem : ξ ∈ Set.Icc a b :=
    ⟨le_trans (x k).2.1 hξ.1.le, le_trans hξ.2.le (x (k + 1)).2.2⟩
  rw [ContinuousMap.sub_apply, Real.norm_eq_abs, hξeq, abs_mul, abs_div]
  calc |iteratedDeriv (m + 1) G ξ| / |((m + 1).factorial : ℝ)| *
        |∏ i, ((t : ℝ) - ((node k i : ℝ)))|
      ≤ M / ((m + 1).factorial : ℝ) * W := by
        rw [abs_of_pos hfact]
        exact mul_le_mul (by gcongr; exact hM ξ hξmem) (hW k hk ((t : ℝ)) ⟨h1, h2⟩)
          (abs_nonneg _) (by positivity)
    _ = W / (m + 1).factorial * M := by ring

/-- **The piecewise polynomial interpolation error on one panel, from the oscillation of $f$
there.** Let the nodes form a panel node system with a uniform local Lebesgue constant
$\Lambda$, let $f \in C([a, b])$, let $k \le n$, and let $x_k \le t \le x_{k+1}$. If
$|f(s) - f(x_k)| \le \omega$ for all $s \in [x_k, x_{k+1}]$, then
$$|f(t) - I f(t)| \le (1 + \Lambda)\, \omega.$$

On the panel that contains $t$, the interpolant is $\sum_i f(\nu_{k,i})\, \ell_{k,i}$, and the
basis functions sum to one. Subtracting $f(x_k)$ from every value turns the error into $(f(t) -
f(x_k)) - \sum_i (f(\nu_{k,i}) - f(x_k))\, \ell_{k,i}(t)$, in which every difference of values
of $f$ is taken between two points of the panel. Only the oscillation on that panel enters. A
graded mesh needs this: the panel next to a singularity is handled by a Hölder bound and the
other panels by the derivative bound. -/
theorem abs_sub_piecewisePolyInterpCLM_apply_le_of_osc (h : IsPanelNodes n m x node) {Λ : ℝ}
    (hΛ : IsPanelLebesgueBound n m x node Λ) (f : C(Set.Icc a b, ℝ)) {k : ℕ} (hk : k ≤ n)
    {t : Set.Icc a b} (h1 : (x k : ℝ) ≤ (t : ℝ)) (h2 : (t : ℝ) ≤ (x (k + 1) : ℝ)) {ω : ℝ}
    (hω : ∀ s : Set.Icc a b, (x k : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ (x (k + 1) : ℝ) →
      |f s - f (x k)| ≤ ω) :
    |f t - piecewisePolyInterpCLM n m x node f t| ≤ (1 + Λ) * ω := by
  have hω0 : 0 ≤ ω := le_trans (abs_nonneg _) (hω (x k) le_rfl (h.step k hk).le)
  set ℓ : Fin (m + 1) → ℝ :=
    fun i => (Lagrange.basis Finset.univ (fun p => ((node k p : ℝ))) i).eval ((t : ℝ)) with hℓ
  have hsum : ∑ i, ℓ i = 1 := by
    have hb := Lagrange.sum_basis (s := (Finset.univ : Finset (Fin (m + 1))))
      (v := fun p => ((node k p : ℝ))) (h.injective k hk).injOn Finset.univ_nonempty
    calc ∑ i, ℓ i
        = (∑ i ∈ Finset.univ, Lagrange.basis Finset.univ
            (fun p => ((node k p : ℝ))) i).eval ((t : ℝ)) := by
          rw [Polynomial.eval_finsetSum]
      _ = 1 := by rw [hb, Polynomial.eval_one]
  have hval : piecewisePolyInterpCLM n m x node f t = ∑ i, f (node k i) * ℓ i := by
    rw [piecewisePolyInterpCLM_apply_of_mem h f hk h1 h2, panelPoly,
      Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
    exact Finset.sum_congr rfl fun i _ => by rw [Polynomial.eval_mul, Polynomial.eval_C, hℓ]
  have hexp : ∑ i, (f (node k i) - f (x k)) * ℓ i = (∑ i, f (node k i) * ℓ i) - f (x k) := by
    have hmul : ∀ i : Fin (m + 1), (f (node k i) - f (x k)) * ℓ i
        = f (node k i) * ℓ i - f (x k) * ℓ i := fun i => sub_mul _ _ _
    rw [Finset.sum_congr rfl fun i _ => hmul i, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum,
      mul_one]
  have hrw : f t - piecewisePolyInterpCLM n m x node f t
      = (f t - f (x k)) - ∑ i, (f (node k i) - f (x k)) * ℓ i := by
    rw [hval, hexp]
    ring
  have hdt : |f t - f (x k)| ≤ ω := hω t h1 h2
  have hdi : ∀ i, |f (node k i) - f (x k)| ≤ ω := fun i =>
    hω (node k i) (h.mem k hk i).1 (h.mem k hk i).2
  rw [hrw]
  calc |(f t - f (x k)) - ∑ i, (f (node k i) - f (x k)) * ℓ i|
      ≤ |f t - f (x k)| + |∑ i, (f (node k i) - f (x k)) * ℓ i| := abs_sub _ _
    _ ≤ ω + ∑ i, |(f (node k i) - f (x k)) * ℓ i| :=
        add_le_add hdt (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ω + ∑ i, ω * |ℓ i| := by
        refine add_le_add le_rfl (Finset.sum_le_sum fun i _ => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hdi i) (abs_nonneg _)
    _ = ω + ω * ∑ i, |ℓ i| := by rw [← Finset.mul_sum]
    _ ≤ ω + ω * Λ := by
        refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hω0)
        exact hΛ k hk ((t : ℝ)) ⟨h1, h2⟩
    _ = (1 + Λ) * ω := by ring

/-- **The piecewise polynomial interpolation error for a continuous function.** Let the nodes form a
panel node system with a uniform local Lebesgue constant $\Lambda$, and let every panel have
length at most $h$. Then for every $f \in C([a, b])$
$$\|f - I f\| \le (1 + \Lambda)\, \omega(f, h).$$
This is `abs_sub_piecewisePolyInterpCLM_apply_le_of_osc` with the modulus of continuity as the
bound for the oscillation on each panel. -/
theorem norm_sub_piecewisePolyInterpCLM_le_modulus (h : IsPanelNodes n m x node) {Λ : ℝ}
    (hΛ : IsPanelLebesgueBound n m x node Λ) (f : C(Set.Icc a b, ℝ)) {hs : ℝ}
    (hmesh : ∀ j ≤ n, (x (j + 1) : ℝ) - (x j : ℝ) ≤ hs) :
    ‖f - piecewisePolyInterpCLM n m x node f‖ ≤ (1 + Λ) * f.modulusOfContinuity hs := by
  have hne : Nonempty (Set.Icc a b) := ⟨x 0⟩
  have hΛ0 : 0 ≤ Λ := hΛ.nonneg h
  have hh0 : 0 ≤ hs :=
    le_trans (sub_nonneg.mpr (h.step 0 (Nat.zero_le n)).le) (hmesh 0 (Nat.zero_le n))
  have hω0 : 0 ≤ f.modulusOfContinuity hs := f.modulusOfContinuity_nonneg hh0
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro t
  obtain ⟨k, hk, h1, h2⟩ := exists_mem_subinterval h.first h.last t
  rw [ContinuousMap.sub_apply, Real.norm_eq_abs]
  refine abs_sub_piecewisePolyInterpCLM_apply_le_of_osc h hΛ f hk h1 h2 fun s hs1 hs2 => ?_
  refine ContinuousMap.le_modulusOfContinuity f ?_
  rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (by linarith)]
  exact le_trans (by linarith) (hmesh k hk)

open Filter Topology in
/-- **Piecewise polynomial interpolation of degree $m$ converges uniformly for every continuous
function**, provided that the local Lebesgue constants stay bounded. For each $p$, let the nodes
$\nu_p$ on the breakpoints $y_{p,0}, \dots, y_{p,N_p+1}$ form a panel node system of degree $m$
on $[a, b]$ with the uniform local Lebesgue constant $\Lambda$ (the same for every $p$), and let
every panel have length at most $h_p$, with $h_p \to 0$. Then for every $f \in C([a, b])$ the
piecewise polynomial interpolants $I_p f$ converge uniformly to $f$.

This is the hypothesis $P_n u \to u$ that a projection method or a product integration method
needs. -/
theorem tendsto_piecewisePolyInterpCLM {N : ℕ → ℕ} {y : ℕ → ℕ → Set.Icc a b}
    {nd : ℕ → ℕ → Fin (m + 1) → Set.Icc a b} {hs : ℕ → ℝ} {Λ : ℝ}
    (h : ∀ p, IsPanelNodes (N p) m (y p) (nd p))
    (hΛ : ∀ p, IsPanelLebesgueBound (N p) m (y p) (nd p) Λ)
    (hmesh : ∀ p, ∀ j ≤ N p, (y p (j + 1) : ℝ) - (y p j : ℝ) ≤ hs p)
    (hh : Tendsto hs atTop (𝓝 0)) (f : C(Set.Icc a b, ℝ)) :
    Tendsto (fun p => piecewisePolyInterpCLM (N p) m (y p) (nd p) f) atTop (𝓝 f) := by
  have hne : Nonempty (Set.Icc a b) := ⟨y 0 0⟩
  have hh0 : ∀ p, 0 ≤ hs p := fun p =>
    le_trans (sub_nonneg.mpr ((h p).step 0 (Nat.zero_le _)).le) (hmesh p 0 (Nat.zero_le _))
  have hhw : Tendsto hs atTop (𝓝[≥] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hh
      (Filter.Eventually.of_forall fun p => Set.mem_Ici.2 (hh0 p))
  have hmod : Tendsto (fun p => (1 + Λ) * f.modulusOfContinuity (hs p)) atTop (𝓝 0) := by
    have := ((ContinuousMap.tendsto_modulusOfContinuity f).comp hhw).const_mul (1 + Λ)
    simpa using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun p => norm_nonneg _) (fun p => ?_) hmod
  rw [norm_sub_rev]
  exact norm_sub_piecewisePolyInterpCLM_le_modulus (h p) (hΛ p) f (hmesh p)

/-- **The nodal polynomial of three equispaced nodes.** Let $\delta > 0$ and $|w| \le \delta$. Then
$$|(w + \delta)\, w\, (w - \delta)| \le \frac{2\sqrt{3}\, \delta^3}{9}.$$

In the variable $w$ centred at the middle node, $(w + \delta) w (w - \delta)$ is the nodal
polynomial of the nodes $-\delta, 0, \delta$. The identity $4\delta^6 - 27 w^2 (w^2 -
\delta^2)^2 = (3w^2 - \delta^2)^2 (4\delta^2 - 3w^2)$ shows that the bound holds for
$|w| \le \delta$, with equality at $w = \mp \delta/\sqrt{3}$. Divided by $3! = 6$, it gives the
constant $\sqrt{3}/27$ of piecewise quadratic interpolation on a uniform mesh of width $\delta$
((12.3.27) of [han2009theoretical]), through `norm_sub_piecewisePolyInterpCLM_le`. -/
theorem abs_add_mul_mul_sub_le {δ w : ℝ} (hδ : 0 < δ) (hw : |w| ≤ δ) :
    |(w + δ) * w * (w - δ)| ≤ 2 * Real.sqrt 3 * δ ^ 3 / 9 := by
  have hwle := abs_le.mp hw
  have hsq : w ^ 2 ≤ δ ^ 2 := by nlinarith [hwle.1, hwle.2]
  have hc0 : (0 : ℝ) ≤ 2 * Real.sqrt 3 * δ ^ 3 / 9 := by positivity
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hkey : ((w + δ) * w * (w - δ)) ^ 2 ≤ (2 * Real.sqrt 3 * δ ^ 3 / 9) ^ 2 := by
    have hrhs : (2 * Real.sqrt 3 * δ ^ 3 / 9) ^ 2 = 4 * δ ^ 6 / 27 := by
      have hexp : (2 * Real.sqrt 3 * δ ^ 3 / 9) ^ 2
          = 4 * Real.sqrt 3 ^ 2 * δ ^ 6 / 81 := by ring
      rw [hexp, hs3]
      ring
    rw [hrhs]
    nlinarith [mul_nonneg (sq_nonneg (3 * w ^ 2 - δ ^ 2))
      (show (0 : ℝ) ≤ 4 * δ ^ 2 - 3 * w ^ 2 by nlinarith)]
  have hsqrt := Real.sqrt_le_sqrt hkey
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq hc0] at hsqrt

end PiecewisePolynomialApi


/-! ### Trigonometric interpolation -/

section Trigonometric

/-- **Trigonometric interpolation at $2n + 1$ distinct nodes of a period is unisolvent.** Let
$T > 0$, and let $x_0, \dots, x_{2n}$ be distinct points of the circle $\mathbb{R}/T\mathbb{Z}$.
Then for all values $b_0, \dots, b_{2n} \in \mathbb{R}$ there is exactly one trigonometric
polynomial $q$ of degree at most $n$ with $q(x_i) = b_i$ for all $i$.

The proof uses the Haar condition `haarCondition_trigPolyLE` of
`Numlib.Approximation.Chebyshev`. -/
theorem isUnisolvent_trigPolyLE (T : ℝ) [hT : Fact (0 < T)] {n : ℕ}
    {x : Fin (2 * n + 1) → AddCircle T} (hx : Function.Injective x) :
    Approximation.IsUnisolvent (trigPolyLE T n) fun i => ContinuousMap.evalCLM ℝ (x i) :=
  (Approximation.haarCondition_iff_isUnisolvent (trigPolyLE T n)
    (finrank_trigPolyLE T n)).mp (haarCondition_trigPolyLE hT.out.ne' n) x hx

/-- The $2n + 1$ **equispaced nodes** of a period $T$: $x_j = jT/(2n + 1)$, $j = 0, \dots, 2n$, as
points of the circle $\mathbb{R}/T\mathbb{Z}$. -/
noncomputable def trigInterpNode (T : ℝ) (n : ℕ) (j : Fin (2 * n + 1)) : AddCircle T :=
  (((j : ℕ) * T / (2 * n + 1) : ℝ) : AddCircle T)

/-- For $T > 0$, the $2n + 1$ equispaced nodes are distinct points of the circle. -/
theorem injective_trigInterpNode (T : ℝ) [hT : Fact (0 < T)] (n : ℕ) :
    Function.Injective (trigInterpNode T n) := by
  have hd : (0 : ℝ) < 2 * n + 1 := by positivity
  have hmem : ∀ j : Fin (2 * n + 1),
      ((j : ℕ) * T / (2 * n + 1) : ℝ) ∈ Set.Ico (0 : ℝ) (0 + T) := by
    intro j
    have hj : ((j : ℕ) : ℝ) < 2 * n + 1 := by exact_mod_cast j.2
    refine ⟨div_nonneg (mul_nonneg (Nat.cast_nonneg _) hT.out.le) hd.le, ?_⟩
    rw [zero_add, div_lt_iff₀ hd]
    nlinarith [hT.out]
  intro j k hjk
  have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ico (hmem j) (hmem k)).mp hjk
  have h3 : ((j : ℕ) : ℝ) * T = ((k : ℕ) : ℝ) * T := by
    have := congrArg (fun r : ℝ => r * (2 * (n : ℝ) + 1)) heq
    simpa [div_mul_cancel₀, hd.ne'] using this
  exact Fin.ext (by exact_mod_cast mul_right_cancel₀ hT.out.ne' h3)

/-- **Trigonometric interpolation** at the $2n + 1$ equispaced nodes of a period $T > 0$: the
bounded projection of $C(\mathbb{R}/T\mathbb{Z})$ onto the trigonometric polynomials of degree
at most $n$ that sends $f$ to the unique such polynomial that agrees with $f$ at the nodes.

It is the interpolation projection `Approximation.IsUnisolvent.interpCLM` of
`isUnisolvent_trigPolyLE`. -/
noncomputable def trigInterpCLM (T : ℝ) [Fact (0 < T)] (n : ℕ) :
    C(AddCircle T, ℝ) →L[ℝ] C(AddCircle T, ℝ) :=
  (isUnisolvent_trigPolyLE T (injective_trigInterpNode T n)).interpCLM

variable {T : ℝ} [Fact (0 < T)] {n : ℕ}

/-- The trigonometric interpolant agrees with $f$ at every equispaced node. -/
@[simp]
theorem trigInterpCLM_apply_node (f : C(AddCircle T, ℝ)) (j : Fin (2 * n + 1)) :
    trigInterpCLM T n f (trigInterpNode T n j) = f (trigInterpNode T n j) :=
  (isUnisolvent_trigPolyLE T (injective_trigInterpNode T n)).interpCLM_apply_node f j

/-- The trigonometric interpolant of $f$ is a trigonometric polynomial of degree at most $n$. -/
theorem trigInterpCLM_mem (f : C(AddCircle T, ℝ)) : trigInterpCLM T n f ∈ trigPolyLE T n :=
  (isUnisolvent_trigPolyLE T (injective_trigInterpNode T n)).interpCLM_mem f

/-- Trigonometric interpolation fixes every trigonometric polynomial of degree at most $n$. -/
theorem trigInterpCLM_eq_self {g : C(AddCircle T, ℝ)} (hg : g ∈ trigPolyLE T n) :
    trigInterpCLM T n g = g :=
  (isUnisolvent_trigPolyLE T (injective_trigInterpNode T n)).interpCLM_eq_self hg

/-- The range of trigonometric interpolation is the space of trigonometric polynomials of degree at
most $n$. -/
theorem range_trigInterpCLM :
    LinearMap.range (trigInterpCLM T n : C(AddCircle T, ℝ) →ₗ[ℝ] C(AddCircle T, ℝ))
      = trigPolyLE T n :=
  (isUnisolvent_trigPolyLE T (injective_trigInterpNode T n)).range_interpCLM

/-- Trigonometric interpolation is a projection. -/
theorem isIdempotentElem_trigInterpCLM : IsIdempotentElem (trigInterpCLM T n) :=
  (isUnisolvent_trigPolyLE T (injective_trigInterpNode T n)).isIdempotentElem_interpCLM

/-- A trigonometric polynomial $g$ of degree at most $n$ that agrees with $f$ at the $2n + 1$
equispaced nodes is the trigonometric interpolant of $f$. -/
theorem eq_trigInterpCLM {f g : C(AddCircle T, ℝ)} (hg : g ∈ trigPolyLE T n)
    (hval : ∀ j, g (trigInterpNode T n j) = f (trigInterpNode T n j)) :
    g = trigInterpCLM T n f := by
  set h := isUnisolvent_trigPolyLE T (injective_trigInterpNode T n)
  have h1 : (⟨g, hg⟩ : trigPolyLE T n)
      = h.interpolate fun j => f (trigInterpNode T n j) := h.eq_interpolate hval
  have h2 : (⟨trigInterpCLM T n f, trigInterpCLM_mem f⟩ : trigPolyLE T n)
      = h.interpolate fun j => f (trigInterpNode T n j) :=
    h.eq_interpolate fun j => trigInterpCLM_apply_node f j
  exact congrArg Subtype.val (h1.trans h2.symm)

end Trigonometric

open Real Set Polynomial
open scoped Real

/-!
### The Lebesgue constant of the Chebyshev nodes

The $n + 1$ Chebyshev nodes of $[-1, 1]$ are $x_j = \cos\theta_j$ with
$\theta_j = (2j + 1)\pi/(2(n + 1))$, the zeros of the Chebyshev polynomial $T_{n+1}$. Their Lagrange
basis functions have the closed form
$$\ell_j(\cos\theta) = \frac{(-1)^j \cos((n + 1)\theta) \sin\theta_j}{(n + 1)(\cos\theta - x_j)}.$$
So the Lebesgue function is a sum of reciprocal sines of the half sums and the half differences
$(\theta_j \pm \theta)/2$. These angles are $\pi(k + \delta)/(2n + 2)$ for $2n + 2$ consecutive
integers $k$, and `SineSum.sum_term_le` applies.
-/


namespace Lagrange

variable {n : ℕ}

/-- The angle $\theta_j = (2j + 1)\pi/(2(n + 1))$ of the $j$-th Chebyshev node of order $n + 1$. -/
noncomputable def chebAngle (n j : ℕ) : ℝ := (2 * j + 1) * π / (2 * (n + 1))

/-- The $n + 1$ **Chebyshev nodes** $x_j = \cos\theta_j = \cos((2j + 1)\pi/(2(n + 1)))$,
$j = 0, \dots, n$. -/
noncomputable def chebNode (n : ℕ) (j : Fin (n + 1)) : ℝ := Real.cos (chebAngle n j)

/-- For $j \le n$, the angle of the $j$-th Chebyshev node lies in $(0, \pi)$. -/
theorem chebAngle_mem (n j : ℕ) (hj : j ≤ n) : chebAngle n j ∈ Ioo 0 π := by
  have hpi := Real.pi_pos
  constructor
  · exact div_pos (by positivity) (by positivity)
  · rw [chebAngle, div_lt_iff₀ (by positivity)]
    have : (j:ℝ) ≤ n := by exact_mod_cast hj
    nlinarith

/-- For $j \le n$, the sine of the angle of the $j$-th Chebyshev node is positive. -/
theorem sin_chebAngle_pos (n j : ℕ) (hj : j ≤ n) : 0 < Real.sin (chebAngle n j) :=
  Real.sin_pos_of_pos_of_lt_pi (chebAngle_mem n j hj).1 (chebAngle_mem n j hj).2

/-- The $n + 1$ Chebyshev nodes are distinct. -/
theorem chebNode_injective (n : ℕ) : Function.Injective (chebNode n) := by
  intro i j hij
  have hi := chebAngle_mem n i (Nat.lt_succ_iff.1 i.2)
  have hj := chebAngle_mem n j (Nat.lt_succ_iff.1 j.2)
  have : chebAngle n i = chebAngle n j :=
    Real.injOn_cos ⟨hi.1.le, hi.2.le⟩ ⟨hj.1.le, hj.2.le⟩ hij
  have h2 : ((i:ℕ):ℝ) = ((j:ℕ):ℝ) := by
    simp only [chebAngle] at this
    field_simp at this
    linarith
  exact Fin.ext (by exact_mod_cast h2)


/-- The Chebyshev nodes are zeros of the Chebyshev polynomial: $T_{n+1}(x_j) = 0$. -/
theorem eval_chebyshevT_chebNode (n : ℕ) (j : Fin (n + 1)) :
    (Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).eval (chebNode n j) = 0 := by
  rw [chebNode, chebAngle, Chebyshev.T_real_cos, Real.cos_eq_zero_iff]
  refine ⟨(j : ℕ), ?_⟩
  have h : ((n : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp

/-- The Chebyshev polynomial is $2^n$ times the nodal polynomial of its own zeros:
$$T_{n+1} = 2^n \prod_{j=0}^{n} (X - x_j).$$
Both sides have degree $n + 1$ and leading coefficient $2^n$, and they agree at the $n + 1$
distinct nodes. -/
theorem chebyshevT_eq_nodal (n : ℕ) :
    Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)
      = Polynomial.C ((2 : ℝ) ^ n) * Lagrange.nodal Finset.univ (chebNode n) := by
  have hcard : (Finset.univ : Finset (Fin (n + 1))).card = n + 1 := by simp
  have hdegT : (Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).degree = ((n + 1 : ℕ) : WithBot ℕ) := by
    rw [Chebyshev.degree_T]
    norm_cast
  have hdegN : (Polynomial.C ((2 : ℝ) ^ n) * Lagrange.nodal Finset.univ (chebNode n)).degree
      = ((n + 1 : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_C_mul (by positivity), Lagrange.degree_nodal, hcard]
  refine Polynomial.eq_of_degree_le_of_eval_index_eq Finset.univ
    (chebNode_injective n).injOn ?_ ?_ ?_ ?_
  · rw [hdegT, hcard]
  · rw [hdegT, hdegN]
  · rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      (Lagrange.nodal_monic).leadingCoeff, mul_one, Chebyshev.leadingCoeff_T]
    congr 1
  · intro j _
    rw [eval_chebyshevT_chebNode, Polynomial.eval_mul, Polynomial.eval_C, Lagrange.eval_nodal,
      Finset.prod_eq_zero (Finset.mem_univ j) (by ring), mul_zero]

/-- At the angle of the $j$-th Chebyshev node, $\sin((n + 1)\theta_j) = (-1)^j$. -/
theorem sin_succ_mul_chebAngle (n j : ℕ) :
    Real.sin (((n : ℝ) + 1) * chebAngle n j) = (-1) ^ j := by
  have h : ((n : ℝ) + 1) * chebAngle n j = (j : ℝ) * π + π / 2 := by
    rw [chebAngle]
    field_simp
  rw [h, Real.sin_add_pi_div_two, Real.cos_nat_mul_pi]

/-- The derivative of the nodal polynomial $\omega$ of the Chebyshev nodes at a node: $2^n\,
\omega'(x_j) \sin\theta_j = (n + 1)(-1)^j$. It follows from $T_{n+1}' = (n + 1) U_n$ and
$U_n(\cos\theta) \sin\theta = \sin((n + 1)\theta)$. -/
theorem eval_derivative_nodal_chebNode (n : ℕ) (j : Fin (n + 1)) :
    (2 : ℝ) ^ n * (Polynomial.derivative (Lagrange.nodal Finset.univ (chebNode n))).eval
        (chebNode n j) * Real.sin (chebAngle n j) = ((n : ℝ) + 1) * (-1) ^ (j : ℕ) := by
  have hT := congrArg Polynomial.derivative (chebyshevT_eq_nodal n)
  rw [Chebyshev.T_derivative_eq_U, Polynomial.derivative_C_mul] at hT
  have hev := congrArg (fun p : ℝ[X] => p.eval (chebNode n j)) hT
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_intCast] at hev
  rw [show ((n + 1 : ℕ) : ℤ) - 1 = ((n : ℕ) : ℤ) by push_cast; ring] at hev
  have hU : (Chebyshev.U ℝ ((n : ℕ) : ℤ)).eval (chebNode n j) * Real.sin (chebAngle n j)
      = (-1) ^ (j : ℕ) := by
    rw [chebNode, Chebyshev.U_real_cos, ← sin_succ_mul_chebAngle n j]
    norm_num
  calc (2 : ℝ) ^ n * (Polynomial.derivative (Lagrange.nodal Finset.univ (chebNode n))).eval
        (chebNode n j) * Real.sin (chebAngle n j)
      = (((n + 1 : ℕ) : ℤ) : ℝ) * ((Chebyshev.U ℝ ((n : ℕ) : ℤ)).eval (chebNode n j)
          * Real.sin (chebAngle n j)) := by rw [← hev]; ring
    _ = ((n : ℝ) + 1) * (-1) ^ (j : ℕ) := by rw [hU]; push_cast; ring

/-- **The Lagrange basis functions of the Chebyshev nodes**, in a form without division. Let
$\ell_j$ be the Lagrange basis polynomial of the Chebyshev node $x_j$, and let $t \neq x_j$.
Then
$$\ell_j(t)\, (n + 1)(t - x_j) = T_{n+1}(t)\, (-1)^j \sin\theta_j.$$
-/
theorem eval_basis_chebNode (n : ℕ) (j : Fin (n + 1)) {t : ℝ} (ht : t ≠ chebNode n j) :
    (Lagrange.basis Finset.univ (chebNode n) j).eval t * (((n : ℝ) + 1) * (t - chebNode n j))
      = (Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).eval t * ((-1) ^ (j : ℕ) * Real.sin (chebAngle n j)) := by
  set D := (Polynomial.derivative (Lagrange.nodal Finset.univ (chebNode n))).eval (chebNode n j)
    with hD
  have hkey := eval_derivative_nodal_chebNode n j
  have hsign : ((-1 : ℝ)) ^ (j : ℕ) * (-1) ^ (j : ℕ) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have hD0 : D ≠ 0 := by
    intro h
    rw [← hD, h] at hkey
    have : ((n : ℝ) + 1) * (-1) ^ (j : ℕ) ≠ 0 := by
      refine mul_ne_zero (by positivity) ?_
      exact pow_ne_zero _ (by norm_num)
    simp only [mul_zero, zero_mul] at hkey
    exact this hkey.symm
  have hnw : Lagrange.nodalWeight Finset.univ (chebNode n) j = D⁻¹ := by
    rw [Lagrange.nodalWeight_eq_eval_derivative_nodal (Finset.mem_univ j), hD]
  have hbasis := Lagrange.eval_basis_not_at_node (s := Finset.univ) (v := chebNode n)
    (Finset.mem_univ j) ht
  rw [hnw] at hbasis
  have hnodal : (Lagrange.nodal Finset.univ (chebNode n)).eval t * 2 ^ n
      = (Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).eval t := by
    rw [chebyshevT_eq_nodal, Polynomial.eval_mul, Polynomial.eval_C]; ring
  rw [← hD] at hkey
  rw [hbasis, ← hnodal]
  field_simp
  linear_combination (-(Lagrange.nodal Finset.univ (chebNode n)).eval t * (-1 : ℝ) ^ (j : ℕ))
      * hkey - ((Lagrange.nodal Finset.univ (chebNode n)).eval t * ((n : ℝ) + 1)) * hsign

/-- The Chebyshev nodes lie in $[-1, 1]$. -/
theorem chebNode_mem_Icc (n : ℕ) (j : Fin (n + 1)) : chebNode n j ∈ Icc (-1 : ℝ) 1 :=
  ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

/-- Let $\theta \in [0, \pi]$ with $\cos\theta \neq x_j$. Then $\sin((\theta_j - \theta)/2) \neq 0$:
the sine of the half difference of the angles vanishes only at the node itself. -/
theorem sin_half_sub_chebAngle_ne_zero (n : ℕ) (j : Fin (n + 1)) {θ : ℝ} (hθ : θ ∈ Icc 0 π)
    (hne : Real.cos θ ≠ chebNode n j) : Real.sin ((chebAngle n j - θ) / 2) ≠ 0 := by
  have hj := chebAngle_mem n j (Nat.lt_succ_iff.1 j.2)
  intro h
  have h1 : (chebAngle n j - θ) / 2 ∈ Ioo (-(π / 2)) (π / 2) := by
    constructor <;> [linarith [hθ.2, hj.1]; linarith [hθ.1, hj.2]]
  have h2 : (chebAngle n j - θ) / 2 = 0 := by
    by_contra hz
    rcases lt_or_gt_of_ne hz with hlt | hgt
    · exact absurd h (Real.sin_neg_of_neg_of_neg_pi_lt hlt (by linarith [h1.1,
        Real.pi_pos])).ne
    · exact absurd h (Real.sin_pos_of_pos_of_lt_pi hgt (by linarith [h1.2, Real.pi_pos])).ne'
  exact hne (by rw [chebNode, show θ = chebAngle n j by linarith])

/-- For $\theta \in [0, \pi]$, the sine of the half sum of the angles is positive:
$\sin((\theta_j + \theta)/2) > 0$. -/
theorem sin_half_add_chebAngle_pos (n : ℕ) (j : Fin (n + 1)) {θ : ℝ} (hθ : θ ∈ Icc 0 π) :
    0 < Real.sin ((chebAngle n j + θ) / 2) := by
  have hj := chebAngle_mem n j (Nat.lt_succ_iff.1 j.2)
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, hj.1]) (by linarith [hθ.2, hj.2])

/-- **The Lebesgue function of the Chebyshev nodes, term by term.** Let $\theta \in [0, \pi]$ with
$\cos\theta \neq x_j$. Then
$$|\ell_j(\cos\theta)| \le \frac{|\cos((n + 1)\theta)|}{2(n + 1)\, |\sin((\theta_j -
  \theta)/2)|} + \frac{|\cos((n + 1)\theta)|}{2(n + 1)\, |\sin((\theta_j + \theta)/2)|}.$$
-/
theorem abs_eval_basis_chebNode_le (n : ℕ) (j : Fin (n + 1)) {θ : ℝ} (hθ : θ ∈ Icc 0 π)
    (hne : Real.cos θ ≠ chebNode n j) :
    |(Lagrange.basis Finset.univ (chebNode n) j).eval (Real.cos θ)|
      ≤ |Real.cos (((n : ℝ) + 1) * θ)| / (2 * ((n : ℝ) + 1) * |Real.sin ((chebAngle n j - θ) / 2)|)
        + |Real.cos (((n : ℝ) + 1) * θ)|
            / (2 * ((n : ℝ) + 1) * |Real.sin ((chebAngle n j + θ) / 2)|) := by
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  set A := (chebAngle n j - θ) / 2 with hA
  set B := (chebAngle n j + θ) / 2 with hB
  have hsA : Real.sin A ≠ 0 := sin_half_sub_chebAngle_ne_zero n j hθ hne
  have hsB : 0 < Real.sin B := sin_half_add_chebAngle_pos n j hθ
  have hdiff : |Real.cos θ - chebNode n j| = 2 * (|Real.sin A| * |Real.sin B|) := by
    have h : Real.cos θ - chebNode n j = 2 * Real.sin B * Real.sin A := by
      rw [chebNode, Real.cos_sub_cos, hA, hB]
      rw [show (θ - chebAngle n ↑j) / 2 = -((chebAngle n ↑j - θ) / 2) by ring, Real.sin_neg,
        show (θ + chebAngle n ↑j) / 2 = (chebAngle n ↑j + θ) / 2 by ring]
      ring
    rw [h, abs_mul, abs_mul, abs_two]
    ring
  have hsum : Real.sin (chebAngle n j) = Real.sin A * Real.cos B + Real.cos A * Real.sin B := by
    rw [← Real.sin_add, hA, hB]
    congr 1
    ring
  have hkey := eval_basis_chebNode n j (t := Real.cos θ) hne
  rw [Chebyshev.T_real_cos, show (((n + 1 : ℕ) : ℤ) : ℝ) = (n : ℝ) + 1 by push_cast; ring] at hkey
  have habs : |(Lagrange.basis Finset.univ (chebNode n) j).eval (Real.cos θ)|
      * (((n : ℝ) + 1) * (2 * (|Real.sin A| * |Real.sin B|)))
      = |Real.cos (((n : ℝ) + 1) * θ)| * |Real.sin (chebAngle n j)| := by
    have h := congrArg abs hkey
    simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos hN, hdiff] at h
    exact h
  have hsinle : |Real.sin (chebAngle n j)| ≤ |Real.sin A| + |Real.sin B| := by
    rw [hsum]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have c1 : |Real.sin A| * |Real.cos B| ≤ |Real.sin A| * 1 := by
      gcongr; exact Real.abs_cos_le_one _
    have c2 : |Real.cos A| * |Real.sin B| ≤ 1 * |Real.sin B| := by
      gcongr; exact Real.abs_cos_le_one _
    linarith
  have hrhs : |Real.cos (((n : ℝ) + 1) * θ)| / (2 * ((n : ℝ) + 1) * |Real.sin A|)
      + |Real.cos (((n : ℝ) + 1) * θ)| / (2 * ((n : ℝ) + 1) * |Real.sin B|)
      = |Real.cos (((n : ℝ) + 1) * θ)| * (|Real.sin B| + |Real.sin A|)
        / (2 * ((n : ℝ) + 1) * (|Real.sin A| * |Real.sin B|)) := by
    field_simp
  rw [hrhs, le_div_iff₀ (by positivity)]
  calc |(Lagrange.basis Finset.univ (chebNode n) j).eval (Real.cos θ)|
        * (2 * ((n : ℝ) + 1) * (|Real.sin A| * |Real.sin B|))
      = |Real.cos (((n : ℝ) + 1) * θ)| * |Real.sin (chebAngle n j)| := by rw [← habs]; ring
    _ ≤ |Real.cos (((n : ℝ) + 1) * θ)| * (|Real.sin B| + |Real.sin A|) := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        linarith

/-- At a node, the Lebesgue function of distinct nodes equals $1$: if $v_0, \dots, v_m$ are distinct
real numbers, then $\sum_j |\ell_j(v_i)| = 1$ for every $i$. -/
theorem sum_abs_eval_basis_at_node {m : ℕ} {v : Fin (m + 1) → ℝ} (hv : Function.Injective v)
    (i : Fin (m + 1)) : ∑ j, |(Lagrange.basis Finset.univ v j).eval (v i)| = 1 := by
  rw [Finset.sum_eq_single i]
  · rw [Lagrange.eval_basis_self hv.injOn (Finset.mem_univ i), abs_one]
  · intro j _ hji
    rw [Lagrange.eval_basis_of_ne hji (Finset.mem_univ i), abs_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **The Lebesgue function of the $n + 1$ Chebyshev nodes is at most $2 + (2/\pi) \log(2n + 2)$.**
For every $\theta \in [0, \pi]$,
$$\sum_{j=0}^{n} |\ell_j(\cos\theta)| \le 2 + \frac{2}{\pi} \log(2n + 2),$$
where $\ell_0, \dots, \ell_n$ are the Lagrange basis polynomials of the Chebyshev nodes.

The evaluation point $t \in [-1, 1]$ is written as $\cos\theta$ with $\theta \in [0, \pi]$. -/
theorem sum_abs_eval_basis_chebNode_le (n : ℕ) {θ : ℝ} (hθ : θ ∈ Icc 0 π) :
    ∑ j : Fin (n + 1), |(Lagrange.basis Finset.univ (chebNode n) j).eval (Real.cos θ)|
      ≤ 2 + 2 / π * Real.log (2 * (n : ℝ) + 2) := by
  have hlog : 0 ≤ Real.log (2 * (n : ℝ) + 2) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hone : (1 : ℝ) ≤ 2 + 2 / π * Real.log (2 * (n : ℝ) + 2) := by
    have : 0 ≤ 2 / π * Real.log (2 * (n : ℝ) + 2) := by positivity
    linarith
  -- at a node the Lebesgue function is `1`
  by_cases hnode : ∃ i : Fin (n + 1), Real.cos θ = chebNode n i
  · obtain ⟨i, hi⟩ := hnode
    rw [hi, sum_abs_eval_basis_at_node (chebNode_injective n) i]
    exact hone
  simp only [not_exists] at hnode
  -- the case `n = 0`: a single node, the Lebesgue function is the constant `1`
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine le_trans (le_of_eq ?_) hone
    simp [Lagrange.basis]
  -- the general case
  set N : ℕ := n + 1 with hNdef
  set M : ℕ := 2 * N with hMdef
  have hM3 : 3 ≤ M := by omega
  have hMr : (M : ℝ) = 2 * ((n : ℝ) + 1) := by rw [hMdef, hNdef]; push_cast; ring
  set mu : ℝ := (N : ℝ) * θ / π - 1 / 2 with hmu
  set c0 : ℤ := ⌊mu⌋ with hc0
  set δ : ℝ := Int.fract mu with hδ
  have hδ0 : 0 ≤ δ := Int.fract_nonneg _
  have hδ1 : δ < 1 := Int.fract_lt_one _
  have hmuval : (c0 : ℝ) + δ = mu := by rw [hc0, hδ]; exact Int.floor_add_fract mu
  have hNr : (N : ℝ) = (n : ℝ) + 1 := by rw [hNdef]; push_cast; ring
  -- the numerator of every term is `|cos ((n+1) θ)|`
  have hnum : ∀ k : ℤ, |Real.sin (π * ((k : ℝ) + δ))| = |Real.cos (((n : ℝ) + 1) * θ)| := by
    intro k
    have h : π * ((k : ℝ) + δ) = ((n : ℝ) + 1) * θ - π / 2 + ((k - c0 : ℤ) : ℝ) * π := by
      have : (δ : ℝ) = mu - (c0 : ℝ) := by linarith [hmuval]
      rw [this, hmu, hNr]
      push_cast
      field_simp
      ring
    rw [h, SineSum.abs_sin_add_intCast_mul_pi, Real.sin_sub_pi_div_two, abs_neg]
  -- the two denominators
  have hden1 : ∀ j : Fin (n + 1), π * (((c0 - (j : ℕ) : ℤ) : ℝ) + δ) / (M : ℝ)
      = -((chebAngle n j - θ) / 2) := by
    intro j
    have hδv : (δ : ℝ) = mu - (c0 : ℝ) := by linarith [hmuval]
    rw [hδv, hmu, hNr, chebAngle, hMr]
    push_cast
    field_simp
    ring
  have hden2 : ∀ j : Fin (n + 1), π * (((c0 + (j : ℕ) + 1 : ℤ) : ℝ) + δ) / (M : ℝ)
      = (chebAngle n j + θ) / 2 := by
    intro j
    have hδv : (δ : ℝ) = mu - (c0 : ℝ) := by linarith [hmuval]
    rw [hδv, hmu, hNr, chebAngle, hMr]
    push_cast
    field_simp
    ring
  -- the term-by-term bound
  have hterm : ∀ j : Fin (n + 1),
      |(Lagrange.basis Finset.univ (chebNode n) j).eval (Real.cos θ)|
        ≤ SineSum.term M δ (c0 - (j : ℕ)) + SineSum.term M δ (c0 + (j : ℕ) + 1) := by
    intro j
    refine (abs_eval_basis_chebNode_le n j hθ (hnode j)).trans (le_of_eq ?_)
    rw [SineSum.term, SineSum.term, hnum, hnum, hden1, hden2, Real.sin_neg, abs_neg, hMr]
  -- sum and reindex
  have hsum : ∑ j : Fin (n + 1), (SineSum.term M δ (c0 - (j : ℕ))
      + SineSum.term M δ (c0 + (j : ℕ) + 1))
      = ∑ i ∈ Finset.range M, SineSum.term M δ ((c0 - (N : ℤ) + 1) + i) := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => SineSum.term M δ (c0 - (j : ℤ))
      + SineSum.term M δ (c0 + (j : ℤ) + 1)) (n + 1), Finset.sum_add_distrib]
    have hleft : ∑ j ∈ Finset.range N, SineSum.term M δ (c0 - (j : ℤ))
        = ∑ j ∈ Finset.range N, SineSum.term M δ ((c0 - (N : ℤ) + 1) + j) := by
      rw [← Finset.sum_range_reflect (fun j : ℕ => SineSum.term M δ (c0 - (j : ℤ))) N]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjN : j < N := Finset.mem_range.1 hj
      congr 1
      have h1 : ((N - 1 - j : ℕ) : ℤ) = (N : ℤ) - 1 - j := by
        have : j ≤ N - 1 := by omega
        push_cast [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_sub this]
        ring
      rw [h1]
      ring
    have hright : ∑ j ∈ Finset.range N, SineSum.term M δ (c0 + (j : ℤ) + 1)
        = ∑ j ∈ Finset.range N, SineSum.term M δ ((c0 - (N : ℤ) + 1) + ((N : ℕ) + j : ℕ)) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      push_cast
      ring
    rw [hleft, hright, hMdef, two_mul]
    exact (Finset.sum_range_add _ N N).symm
  calc ∑ j : Fin (n + 1), |(Lagrange.basis Finset.univ (chebNode n) j).eval (Real.cos θ)|
      ≤ ∑ j : Fin (n + 1), (SineSum.term M δ (c0 - (j : ℕ))
          + SineSum.term M δ (c0 + (j : ℕ) + 1)) := Finset.sum_le_sum fun j _ => hterm j
    _ = ∑ i ∈ Finset.range M, SineSum.term M δ ((c0 - (N : ℤ) + 1) + i) := hsum
    _ ≤ 2 + 2 / π * Real.log (M : ℝ) := SineSum.sum_term_le hM3 hδ0 hδ1 _
    _ = 2 + 2 / π * Real.log (2 * (n : ℝ) + 2) := by rw [hMr]; ring_nf

/-- The $n + 1$ Chebyshev nodes as points of $[-1, 1]$. -/
noncomputable def chebNodeIcc (n : ℕ) (j : Fin (n + 1)) : Icc (-1 : ℝ) 1 :=
  ⟨chebNode n j, chebNode_mem_Icc n j⟩

/-- **The Lebesgue constant of the Chebyshev nodes grows logarithmically.** The Lagrange
interpolation operator $\Pi_n$ on $C[-1, 1]$ at the $n + 1$ Chebyshev nodes
$x_j = \cos((2j + 1)\pi/(2(n + 1)))$ satisfies
$$\|\Pi_n\| \le 2 + \frac{2}{\pi} \log(2n + 2).$$

Rivlin's sharp form of this estimate, $\|\Pi_n\| \le (2/\pi) \log(n + 1) + 1$ (Theorem 1.2 of
[rivlin1969introduction], and (10.25) of [quarteroni2000numerical]), is not proved here. The
bound proved here has the sharp factor $2/\pi$, and so the growth rate that the applications
use, but its additive constant is larger by $1.441\ldots$. The sharp form is not a longer
version of the same argument but two further theorems: the Lebesgue function attains its maximum
at $t = \pm 1$, where it equals $\frac{1}{n + 1} \sum_{j \le n} \cot((2j + 1)\pi/(4(n + 1)))$
(the monotonicity of the successive local maxima towards the endpoints is of Ehlich–Zeller type,
and is the whole difficulty); and this cotangent sum is at most $(2/\pi) \log(n + 1) + 1$.
Neither step may give anything away: the Lebesgue constant is $(2/\pi)(\log(n + 1) + \gamma +
\log(8/\pi)) + o(1) = (2/\pi) \log(n + 1) + 0.9625\ldots$, so the sharp constant has an
asymptotic margin of $0.0375$, and at $n = 0$ the two sides are both equal to $1$. The argument
through `SineSum.sum_term_le` cannot reach the sharp form. It loses $(2/\pi) \log 2$ in the
passage from the $n + 1$ nodes to the $2n + 2$ reflected angles $\pm\theta_j$, and it loses more
in the triangle inequality $|\sin(A + B)| \le |\sin A| + |\sin B|$ on the two halves and in the
bound $1$ on each of the two terms nearest the evaluation point: $1.441\ldots$ in all, against a
margin of $0.0375$. -/
theorem norm_interpolateCLM_chebyshev_le (n : ℕ) :
    ‖Lagrange.interpolateCLM (chebNodeIcc n)‖ ≤ 2 + 2 / π * Real.log (2 * (n : ℝ) + 2) := by
  have hinj : Function.Injective (chebNodeIcc n) := fun i j hij =>
    chebNode_injective n (congrArg Subtype.val hij)
  have : Nonempty (Icc (-1 : ℝ) 1) := ⟨⟨1, by norm_num⟩⟩
  obtain ⟨t, ht⟩ := (Lagrange.isGreatest_norm_interpolateCLM hinj).1
  rw [← ht]
  have htmem : (t : ℝ) ∈ Icc (-1 : ℝ) 1 := t.2
  have hcos : Real.cos (Real.arccos (t : ℝ)) = (t : ℝ) := Real.cos_arccos htmem.1 htmem.2
  have hθ : Real.arccos (t : ℝ) ∈ Icc 0 π := ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  have := sum_abs_eval_basis_chebNode_le n hθ
  rw [hcos] at this
  refine le_trans (le_of_eq ?_) this
  exact Finset.sum_congr rfl fun i _ => by rw [Lagrange.basisCM_apply]; rfl


/-! ### A lower bound for the equispaced Lebesgue constants -/

section Equispaced

open Finset
open scoped Nat

/-- Over $\mathbb{R}$, $\prod_{j<m} (m - j) = m!$. -/
private theorem prod_range_sub_cast (m : ℕ) : ∏ j ∈ range m, ((m : ℝ) - j) = (m ! : ℝ) := by
  have h : ∀ j ∈ range m, ((m : ℝ) - (j : ℝ)) = ((m - j : ℕ) : ℝ) := fun j hj => by
    rw [Nat.cast_sub (le_of_lt (mem_range.mp hj))]
  rw [Finset.prod_congr rfl h, ← Nat.cast_prod, ← Nat.descFactorial_eq_prod_range,
    Nat.descFactorial_self]

/-- Over $\mathbb{R}$, $\prod_{m < j \le n} (j - m) = (n - m)!$. -/
private theorem prod_Ico_sub_cast {m n : ℕ} :
    ∏ j ∈ Ico (m + 1) (n + 1), ((j : ℝ) - m) = ((n - m)! : ℝ) := by
  rw [Finset.prod_Ico_eq_prod_range]
  simp only [Nat.add_sub_add_right]
  rw [← Finset.prod_range_add_one_eq_factorial (n - m), Nat.cast_prod]
  exact Finset.prod_congr rfl fun i _ => by push_cast; ring

/-- For $m \le n$, the product of the distances $|m - k|$ from $m$ to the other integers
$k = 0, \dots, n$, with the factor at $k = m$ replaced by $1$, is $m!\, (n - m)!$. -/
private theorem prod_range_ite_abs_sub {m n : ℕ} (hmn : m ≤ n) :
    ∏ k ∈ range (n + 1), (if k = m then (1 : ℝ) else |(m : ℝ) - (k : ℝ)|)
      = (m ! : ℝ) * ((n - m)! : ℝ) := by
  rw [Finset.range_eq_Ico,
    ← Finset.prod_Ico_consecutive _ (Nat.zero_le m) (Nat.le_succ_of_le hmn),
    ← Finset.prod_Ico_consecutive _ (Nat.le_succ m) (Nat.succ_le_succ hmn)]
  have h1 : ∏ k ∈ Ico 0 m, (if k = m then (1 : ℝ) else |(m : ℝ) - (k : ℝ)|) = (m ! : ℝ) := by
    rw [← Finset.range_eq_Ico, ← prod_range_sub_cast m]
    refine Finset.prod_congr rfl fun k hk => ?_
    have hk' : k < m := mem_range.mp hk
    have hkm : (k : ℝ) < (m : ℝ) := by exact_mod_cast hk'
    rw [ite_eq_right (Nat.ne_of_lt hk')]
    exact abs_of_nonneg (by linarith)
  have h2 : ∏ k ∈ Ico m (m + 1), (if k = m then (1 : ℝ) else |(m : ℝ) - (k : ℝ)|) = 1 := by
    rw [Finset.prod_Ico_succ_top (le_refl m), Finset.Ico_self, Finset.prod_empty, one_mul]
    simp
  have h3 : ∏ k ∈ Ico (m + 1) (n + 1), (if k = m then (1 : ℝ) else |(m : ℝ) - (k : ℝ)|)
      = ((n - m)! : ℝ) := by
    rw [← prod_Ico_sub_cast (m := m) (n := n)]
    refine Finset.prod_congr rfl fun k hk => ?_
    have hk' : m + 1 ≤ k := (Finset.mem_Ico.mp hk).1
    have hkm : (m : ℝ) < (k : ℝ) := by
      have h : ((m : ℝ) + 1) ≤ (k : ℝ) := by exact_mod_cast hk'
      linarith
    rw [ite_eq_right (by omega : k ≠ m), abs_sub_comm]
    exact abs_of_nonneg (by linarith)
  rw [h1, h2, h3, one_mul]

/-- The denominator of the $i$-th Lagrange basis polynomial of equispaced nodes, with the node
spacing scaled away: $\prod_{j \neq i} |i - j| = i!\, (n - i)!$. -/
private theorem prod_erase_abs_sub (n : ℕ) (i : Fin (n + 1)) :
    ∏ j ∈ (univ : Finset (Fin (n + 1))).erase i, |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)|
      = ((i : ℕ)! : ℝ) * (((n - (i : ℕ))! : ℝ)) := by
  have hmn : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.isLt
  have hstep : ∏ j ∈ (univ : Finset (Fin (n + 1))).erase i, |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)|
      = ∏ j ∈ (univ : Finset (Fin (n + 1))),
          (if (j : ℕ) = (i : ℕ) then (1 : ℝ) else |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)|) := by
    rw [← Finset.prod_erase (univ : Finset (Fin (n + 1)))
      (f := fun j : Fin (n + 1) =>
        if (j : ℕ) = (i : ℕ) then (1 : ℝ) else |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)|)
      (a := i) (by simp)]
    refine Finset.prod_congr rfl fun j hj => ?_
    have hne : (j : ℕ) ≠ (i : ℕ) := fun hc => (Finset.mem_erase.mp hj).1 (Fin.ext hc)
    rw [ite_eq_right hne]
  rw [hstep, Fin.prod_univ_eq_prod_range
    (fun k => if k = (i : ℕ) then (1 : ℝ) else |((i : ℕ) : ℝ) - (k : ℝ)|) (n + 1),
    prod_range_ite_abs_sub hmn]

/-- The numerator of the Lebesgue function at the midpoint of the first panel, before the node $i$
is removed: $\prod_{j=0}^{n} |1/2 - j| = (2n)!/(2^{2n+1}\, n!)$. -/
private theorem prod_range_abs_half (n : ℕ) :
    ∏ j ∈ range (n + 1), |1 / 2 - (j : ℝ)| = ((2 * n)! : ℝ) / (2 ^ (2 * n + 1) * (n ! : ℝ)) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hfn : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast n.factorial_pos
    have habs : |1 / 2 - ((n + 1 : ℕ) : ℝ)| = (n : ℝ) + 1 / 2 := by
      push_cast
      rw [abs_of_nonpos (by linarith)]
      ring
    have hfac2 : (((2 * (n + 1))! : ℕ) : ℝ)
        = (2 * (n : ℝ) + 2) * (2 * (n : ℝ) + 1) * (((2 * n)! : ℕ) : ℝ) := by
      have h : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
      rw [h, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    have hfac1 : (((n + 1)! : ℕ) : ℝ) = ((n : ℝ) + 1) * (n ! : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    rw [Finset.prod_range_succ, ih, habs, hfac2, hfac1]
    have hmul : 2 * (n + 1) + 1 = 2 * n + 1 + 2 := by ring
    rw [hmul, pow_add]
    field_simp
    ring

/-- The binomial theorem in the form that the Lebesgue function needs:
$\sum_{i=0}^{n} 1/(i!\, (n - i)!) = 2^n/n!$. -/
private theorem sum_inv_factorial_mul (n : ℕ) :
    ∑ i ∈ range (n + 1), 1 / ((i ! : ℝ) * ((n - i)! : ℝ)) = 2 ^ n / (n ! : ℝ) := by
  have hfn : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast n.factorial_pos
  have key : ∀ i ∈ range (n + 1),
      1 / ((i ! : ℝ) * ((n - i)! : ℝ)) = (n.choose i : ℝ) / (n ! : ℝ) := by
    intro i hi
    have hle : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have h : ((n.choose i : ℝ)) * (i ! : ℝ) * ((n - i)! : ℝ) = (n ! : ℝ) := by
      exact_mod_cast congrArg (fun k : ℕ => (k : ℝ))
        (Nat.choose_mul_factorial_mul_factorial hle)
    have hfi : (0 : ℝ) < (i ! : ℝ) := by exact_mod_cast i.factorial_pos
    have hfni : (0 : ℝ) < ((n - i)! : ℝ) := by exact_mod_cast (n - i).factorial_pos
    rw [div_eq_div_iff (by positivity) (ne_of_gt hfn)]
    linarith [h]
  rw [Finset.sum_congr rfl key, ← Finset.sum_div, ← Nat.cast_sum, Nat.sum_range_choose]
  norm_num

/-- Every factor $|1/2 - k|$ of the Lebesgue function at the midpoint of the first panel is at least
$1/2$. -/
private theorem half_le_abs_half_sub (k : ℕ) : (1 : ℝ) / 2 ≤ |1 / 2 - (k : ℝ)| := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · norm_num
  · have h : (1 : ℝ) ≤ k := by exact_mod_cast hk
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- For $k \le n$ and $n \ge 1$, the factor $|1/2 - k|$ is at most $(2n - 1)/2$, its value at
$k = n$. -/
private theorem abs_half_sub_le {k n : ℕ} (hk : k ≤ n) (hn : 1 ≤ n) :
    |1 / 2 - (k : ℝ)| ≤ (2 * (n : ℝ) - 1) / 2 := by
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [abs_le]
  constructor <;> linarith

/-- For $n \ge 1$, the value $2 (2n)!\, 2^n/((2n - 1)\, 2^{2n+1}\, (n!)^2)$ that the Lebesgue
function reaches at the midpoint of the first panel is at least $2^n/(8n^2)$, by
$\binom{2n}{n} \ge 4^n/(2n)$ (`Nat.four_pow_le_two_mul_self_mul_centralBinom`). -/
private theorem two_pow_div_le_of_centralBinom {n : ℕ} (hn : 1 ≤ n) :
    (2 : ℝ) ^ n / (8 * (n : ℝ) ^ 2)
      ≤ 2 * (((2 * n)! : ℝ) / (2 ^ (2 * n + 1) * (n ! : ℝ))) / (2 * (n : ℝ) - 1)
          * ((2 : ℝ) ^ n / (n ! : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hfn : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast n.factorial_pos
  have hcb : ((Nat.centralBinom n : ℕ) : ℝ) * (n ! : ℝ) * (n ! : ℝ) = (((2 * n)! : ℕ) : ℝ) := by
    have hle : n ≤ 2 * n := Nat.le_mul_of_pos_left n (by norm_num)
    have h := Nat.choose_mul_factorial_mul_factorial hle
    have h2 : 2 * n - n = n := by omega
    rw [h2] at h
    rw [Nat.centralBinom_eq_two_mul_choose]
    exact_mod_cast h
  have hcb2 : (4 : ℝ) ^ n ≤ 2 * (n : ℝ) * ((Nat.centralBinom n : ℕ) : ℝ) := by
    have h := Nat.four_pow_le_two_mul_self_mul_centralBinom n hn
    have h' : ((4 ^ n : ℕ) : ℝ) ≤ ((2 * n * Nat.centralBinom n : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    linarith
  have hpow : (2 : ℝ) ^ (2 * n + 1) = 2 * 4 ^ n := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  have h4 : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
  have h2p : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have h2n1 : (0 : ℝ) < 2 * (n : ℝ) - 1 := by linarith
  have key : 2 * (((2 * n)! : ℝ) / (2 ^ (2 * n + 1) * (n ! : ℝ))) / (2 * (n : ℝ) - 1)
      * ((2 : ℝ) ^ n / (n ! : ℝ))
      = ((Nat.centralBinom n : ℕ) : ℝ) * 2 ^ n / (4 ^ n * (2 * (n : ℝ) - 1)) := by
    rw [hpow, ← hcb]
    field_simp
  have h8n : (0 : ℝ) < 8 * (n : ℝ) ^ 2 := by nlinarith
  rw [key, div_le_div_iff₀ h8n (mul_pos h4 h2n1)]
  have e1 : (4 : ℝ) ^ n * (2 * (n : ℝ) - 1)
      ≤ (2 * (n : ℝ) * ((Nat.centralBinom n : ℕ) : ℝ)) * (2 * (n : ℝ) - 1) :=
    mul_le_mul_of_nonneg_right hcb2 h2n1.le
  have e2 : (2 * (n : ℝ) * ((Nat.centralBinom n : ℕ) : ℝ)) * (2 * (n : ℝ) - 1)
      ≤ ((Nat.centralBinom n : ℕ) : ℝ) * (8 * (n : ℝ) ^ 2) := by nlinarith [hn0]
  nlinarith [e1, e2, h2p]

/-- **The equispaced Lebesgue function is exponentially large** (Schönhage). Let $a < b$, let
$n \ge 1$, and let $\ell_0, \dots, \ell_n$ be the Lagrange basis polynomials of the $n + 1$
equispaced nodes $x_j = a + j(b - a)/n$ of $[a, b]$. Then at the midpoint $t = a + (b - a)/(2n)$
of the first panel
$$\sum_{i=0}^{n} |\ell_i(t)| \ge \frac{2^n}{8n^2} = \frac{2^{n-3}}{n^2}.$$
This is §8.1.3 of [quarteroni2000numerical].

So, by `Lagrange.norm_interpolateCLM`, the Lebesgue constant of equispaced interpolation grows
exponentially. This is the one-sided half of Turetskii's asymptotics
$\Lambda_n \simeq 2^{n+1}/(e\, n \log n)$. At $t$ the node spacing cancels from every basis
polynomial, $\ell_i(t) = \prod_{j \neq i} (1/2 - j)/(i - j)$. The denominators give
$i!\, (n - i)!$ and the common numerator gives $(2n)!/(2^{2n+1} n!)$; the largest omitted factor
is $(2n - 1)/2$. Summation with $\sum_i 1/(i!\, (n - i)!) = 2^n/n!$ gives
$\binom{2n}{n} 2^n/(4^n (2n - 1))$, which `Nat.four_pow_le_two_mul_self_mul_centralBinom` bounds
below by $2^n/(8n^2)$. -/
theorem two_pow_div_le_sum_abs_eval_basis_equispaced {a b : ℝ} (hab : a < b) {n : ℕ}
    (hn : 1 ≤ n) :
    (2 : ℝ) ^ n / (8 * (n : ℝ) ^ 2) ≤
      ∑ i : Fin (n + 1),
        |(Lagrange.basis univ (fun j : Fin (n + 1) => a + ((j : ℕ) : ℝ) * (b - a) / n) i).eval
          (a + (b - a) / (2 * n))| := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hc : (b - a) / (n : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hval : ∀ i : Fin (n + 1),
      |(Lagrange.basis univ (fun j : Fin (n + 1) => a + ((j : ℕ) : ℝ) * (b - a) / n) i).eval
          (a + (b - a) / (2 * n))|
        = (∏ j ∈ (univ : Finset (Fin (n + 1))).erase i, |1 / 2 - ((j : ℕ) : ℝ)|)
            / (((i : ℕ)! : ℝ) * ((n - (i : ℕ))! : ℝ)) := by
    intro i
    have hprod : (Lagrange.basis univ (fun j : Fin (n + 1) => a + ((j : ℕ) : ℝ) * (b - a) / n)
          i).eval (a + (b - a) / (2 * n))
        = ∏ j ∈ (univ : Finset (Fin (n + 1))).erase i,
            (1 / 2 - ((j : ℕ) : ℝ)) / (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) := by
      rw [Lagrange.eval_basis_eq_prod]
      refine Finset.prod_congr rfl fun j hj => ?_
      have e1 : a + (b - a) / (2 * n) - (a + ((j : ℕ) : ℝ) * (b - a) / n)
          = ((b - a) / n) * (1 / 2 - ((j : ℕ) : ℝ)) := by
        field_simp
        ring
      have e2 : a + ((i : ℕ) : ℝ) * (b - a) / n - (a + ((j : ℕ) : ℝ) * (b - a) / n)
          = ((b - a) / n) * (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) := by
        field_simp
        ring
      rw [e1, e2, mul_div_mul_left _ _ hc]
    have hsplit : (∏ j ∈ (univ : Finset (Fin (n + 1))).erase i,
        |(1 / 2 - ((j : ℕ) : ℝ)) / (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ))|)
        = (∏ j ∈ (univ : Finset (Fin (n + 1))).erase i, |1 / 2 - ((j : ℕ) : ℝ)|)
          / ∏ j ∈ (univ : Finset (Fin (n + 1))).erase i, |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| := by
      rw [← Finset.prod_div_distrib]
      exact Finset.prod_congr rfl fun j _ => abs_div _ _
    rw [hprod, Finset.abs_prod, hsplit, prod_erase_abs_sub]
  have hPeq : ∏ j ∈ (univ : Finset (Fin (n + 1))), |1 / 2 - ((j : ℕ) : ℝ)|
      = ((2 * n)! : ℝ) / (2 ^ (2 * n + 1) * (n ! : ℝ)) := by
    rw [← prod_range_abs_half n]
    exact Fin.prod_univ_eq_prod_range (fun k => |1 / 2 - (k : ℝ)|) (n + 1)
  have h2n1 : (0 : ℝ) < 2 * (n : ℝ) - 1 := by linarith
  have hlower : ∀ i : Fin (n + 1),
      2 * (((2 * n)! : ℝ) / (2 ^ (2 * n + 1) * (n ! : ℝ))) / (2 * (n : ℝ) - 1)
        ≤ ∏ j ∈ (univ : Finset (Fin (n + 1))).erase i, |1 / 2 - ((j : ℕ) : ℝ)| := by
    intro i
    have hprodpos : (0 : ℝ) < ∏ j ∈ (univ : Finset (Fin (n + 1))).erase i,
        |1 / 2 - ((j : ℕ) : ℝ)| :=
      Finset.prod_pos fun j _ => lt_of_lt_of_le (by norm_num) (half_le_abs_half_sub _)
    have hmul : |1 / 2 - ((i : ℕ) : ℝ)|
        * (∏ j ∈ (univ : Finset (Fin (n + 1))).erase i, |1 / 2 - ((j : ℕ) : ℝ)|)
        = ((2 * n)! : ℝ) / (2 ^ (2 * n + 1) * (n ! : ℝ)) := by
      rw [← hPeq]
      exact Finset.mul_prod_erase (univ : Finset (Fin (n + 1)))
        (fun j : Fin (n + 1) => |1 / 2 - ((j : ℕ) : ℝ)|) (Finset.mem_univ i)
    have hub := abs_half_sub_le (Nat.lt_succ_iff.mp i.isLt) hn
    have step : ((2 * n)! : ℝ) / (2 ^ (2 * n + 1) * (n ! : ℝ))
        ≤ ((2 * (n : ℝ) - 1) / 2)
          * (∏ j ∈ (univ : Finset (Fin (n + 1))).erase i, |1 / 2 - ((j : ℕ) : ℝ)|) := by
      rw [← hmul]
      exact mul_le_mul_of_nonneg_right hub hprodpos.le
    rw [div_le_iff₀ h2n1]
    linarith
  have hsum1 : ∑ i : Fin (n + 1), (1 : ℝ) / (((i : ℕ)! : ℝ) * ((n - (i : ℕ))! : ℝ))
      = 2 ^ n / (n ! : ℝ) := by
    rw [Fin.sum_univ_eq_sum_range (fun k => (1 : ℝ) / ((k ! : ℝ) * ((n - k)! : ℝ))) (n + 1)]
    exact sum_inv_factorial_mul n
  refine le_trans (two_pow_div_le_of_centralBinom hn) ?_
  calc 2 * (((2 * n)! : ℝ) / (2 ^ (2 * n + 1) * (n ! : ℝ))) / (2 * (n : ℝ) - 1)
        * ((2 : ℝ) ^ n / (n ! : ℝ))
      = ∑ i : Fin (n + 1), 2 * (((2 * n)! : ℝ) / (2 ^ (2 * n + 1) * (n ! : ℝ)))
            / (2 * (n : ℝ) - 1) * ((1 : ℝ) / (((i : ℕ)! : ℝ) * ((n - (i : ℕ))! : ℝ))) := by
        rw [← Finset.mul_sum, hsum1]
    _ ≤ ∑ i : Fin (n + 1),
          |(Lagrange.basis univ (fun j : Fin (n + 1) => a + ((j : ℕ) : ℝ) * (b - a) / n) i).eval
            (a + (b - a) / (2 * n))| := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hfi : (0 : ℝ) < ((i : ℕ)! : ℝ) := by exact_mod_cast (i : ℕ).factorial_pos
        have hfni : (0 : ℝ) < ((n - (i : ℕ))! : ℝ) := by
          exact_mod_cast (n - (i : ℕ)).factorial_pos
        rw [hval i, mul_one_div, div_le_div_iff_of_pos_right (mul_pos hfi hfni)]
        exact hlower i


end Equispaced

end Lagrange

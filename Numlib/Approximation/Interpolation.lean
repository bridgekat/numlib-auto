import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Topology.TietzeExtension
import Numlib.Approximation.Unisolvent

/-!
# Interpolation on continuous function spaces

Lagrange interpolation at `n + 1` distinct nodes, with the classical error formula `f(t) - p(t) =
f^{(n+1)}(ξ)/(n+1)! ∏ (t - x_i)`; piecewise-linear interpolation on a partition; and trigonometric
interpolation at the equispaced nodes of a period. The material is [han2009theoretical] §3.2 and
[kress1998numerical] §8.1 and §8.3.

## Main definitions

* `Lagrange.basisCM x i` and `Lagrange.interpolateCLM x` are the Lagrange basis functions and the
  interpolation operator on `C(X, ℝ)`, for a compact `X ⊆ ℝ`.
* `piecewiseLinearRamp` and `piecewiseLinearInterpCLM` are the clamped ramp of a subinterval and the
  piecewise-linear interpolation operator on a partition, which is a combination of ramps.
* `IsPanelNodes n m x node` is a system of `m + 1` interpolation nodes on each panel `[x j, x
  (j + 1)]` of a partition, the first and the last of which are the panel's endpoints, and
  `piecewisePolyInterpCLM n m x node` is the resulting **piecewise polynomial interpolation
  operator of degree `m`**, of which the piecewise-linear one is the case `m = 1`.
  `IsPanelLebesgueBound` is a uniform bound for the local Lebesgue constants of the panels.
* `trigInterpNode T n` are the `2 n + 1` equispaced nodes `j T / (2 n + 1)` of a period, and
  `trigInterpCLM T n` is trigonometric interpolation at them.
* `ContinuousMap.modulusOfContinuity f δ` is the modulus of continuity `ω(f, δ)`, the largest change
  of `f` over pairs of points at distance at most `δ`.

## Main results

* `exists_iteratedDeriv_eq_zero_of_forall_eq_zero` is the **generalized Rolle theorem**: a `C^{n+1}`
  function vanishing at `n + 2` points of `[a, b]` has a zero of its `(n+1)`-st derivative strictly
  inside `[a, b]`. Applied to `s ↦ f s - p s - c ∏ (s - x_i)` with `c` chosen to make the value at
  `t` vanish, it gives the error formula `Lagrange.exists_sub_interpolate_eq`.
* `Lagrange.isGreatest_norm_interpolateCLM` and `Lagrange.norm_interpolateCLM` identify the operator
  norm of the interpolation operator with the **Lebesgue constant** of its nodes, the largest value
  of `t ↦ ∑ i, |ℓ_i t|`.
* `norm_piecewiseLinearInterpCLM` says that piecewise-linear interpolation has norm one, and
  `norm_sub_piecewiseLinearInterpCLM_le` bounds its error on a mesh of size `h` by `h² ‖f''‖ / 8` —
  the two-node case of the same error formula. `norm_sub_piecewiseLinearInterpCLM_le_modulus` is the
  companion bound `ω(f, h)` for a merely continuous `f`.
* `piecewisePolyInterpCLM_apply_of_mem` is the local description of the degree-`m` piecewise
  polynomial interpolant — on each panel it is the Lagrange interpolant at that panel's nodes — and
  everything else about the operator follows from it: `norm_piecewisePolyInterpCLM_le`,
  `exists_sub_piecewisePolyInterpCLM_apply_eq` and its consequence
  `norm_sub_piecewisePolyInterpCLM_le`, the bound `(1 + Λ) ω(f, h)` of
  `norm_sub_piecewisePolyInterpCLM_le_modulus`, and the uniform convergence
  `tendsto_piecewisePolyInterpCLM`.
* `Lagrange.isUnisolvent_polyLE` reads Lagrange interpolation as the abstract interpolation problem
  of `Numlib/Approximation/Unisolvent` for the subspace `polyLE X n` and the point evaluations at
  the nodes, and `Lagrange.interpCLM_isUnisolvent_polyLE` identifies `Lagrange.interpolateCLM` with
  the interpolation projection of that problem.
* `isUnisolvent_trigPolyLE`: a nonzero trigonometric polynomial of degree at most `n` has at most
  `2 n` zeros in a period (`haarCondition_trigPolyLE`, in `Numlib.Approximation.Chebyshev`), so
  interpolation by such polynomials at `2 n + 1` distinct nodes has exactly one solution.
  `trigInterpCLM` is the resulting bounded projection onto `trigPolyLE T n` at the equispaced nodes.

## Implementation notes

Trigonometric interpolation has no formula for its cardinal basis here: the operator is built from
unisolvence, which is the Haar condition `card_le_two_mul_of_forall_trigFun_eq_zero` of
`Numlib/Approximation/Chebyshev` — the substitution `z = e^{2 π i x / T}` turning a trigonometric
polynomial into an algebraic one — together with the dimension count `finrank_trigPolyLE`.
-/

open scoped Polynomial

namespace Polynomial

/-- The iterated derivative of a polynomial function is the polynomial function of the iterated
formal derivative. -/
theorem iteratedDeriv_eval (P : ℝ[X]) (k : ℕ) :
    iteratedDeriv k (fun s => P.eval s) = fun s => (Polynomial.derivative^[k] P).eval s := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    rw [Function.iterate_succ_apply']
    exact _root_.Polynomial.deriv (𝕜 := ℝ) _

/-- The iterated formal derivative is additive. -/
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

/-- The induction behind the generalized Rolle theorem, phrased over an explicit sequence `F` of
successive derivatives: if `F 0` vanishes at `n + 1` increasing points of `[a, b]` then `F n`
vanishes somewhere between the extreme two. -/
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

/-- **The generalized Rolle theorem, for a function smooth only near the interval.** A function
that is `C^{n+1}` on an open set containing `[a, b]` and vanishes at `n + 2` distinct points of
`[a, b]` has a zero of its `(n + 1)`-st derivative strictly inside `[a, b]`.

The hypothesis is local because the applications are: a function of Rice's type `(γ, m + 1)` is
smooth on `(0, 1]` only, and the interpolation error on a panel that stays away from the origin
must still be available.

Reference: [kress1998numerical], §8.1. -/
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

/-- **The generalized Rolle theorem.** A function of class `C^{n+1}` that vanishes at `n + 2`
distinct points of `[a, b]` has a zero of its `(n + 1)`-st derivative strictly inside `[a, b]`.

Reference: [kress1998numerical], §8.1. -/
theorem exists_iteratedDeriv_eq_zero_of_forall_eq_zero {n : ℕ} {a b : ℝ}
    {f : ℝ → ℝ} (hf : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f) {s : Finset ℝ}
    (hcard : n + 2 ≤ s.card) (hsub : ∀ t ∈ s, t ∈ Set.Icc a b) (hzero : ∀ t ∈ s, f t = 0) :
    ∃ c ∈ Set.Ioo a b, iteratedDeriv (n + 1) f c = 0 :=
  exists_iteratedDeriv_eq_zero_of_forall_eq_zero_of_contDiffOn isOpen_univ (Set.subset_univ _)
    hf.contDiffOn hcard hsub hzero

/-! ### The interpolation error formula -/

namespace Lagrange

/-- **The Lagrange interpolation error formula, for a function smooth only near the interval.**
For `f` of class `C^{n+1}` on an open set containing `[a, b]` and `n + 1` distinct nodes in
`[a, b]`, the error of the interpolating polynomial at a point `t` of `[a, b]` is
`f^{(n+1)}(ξ)/(n+1)!` times the nodal polynomial `∏ (t - x_i)`, for some `ξ` strictly inside
`[a, b]`.

Reference: [kress1998numerical], Theorem 8.4; [han2009theoretical], §3.2. -/
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

/-- **The Lagrange interpolation error formula.** For `f` of class `C^{n+1}` and `n + 1` distinct
nodes in `[a, b]`, the error of the interpolating polynomial at a point `t` of `[a, b]` is
`f^{(n+1)}(ξ)/(n+1)!` times the nodal polynomial `∏ (t - x_i)`, for some `ξ` strictly inside `[a,
b]`.

Reference: [kress1998numerical], Theorem 8.4; [han2009theoretical], §3.2. -/
theorem exists_sub_interpolate_eq {n : ℕ} {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f) {v : Fin (n + 1) → ℝ}
    (hv : Function.Injective v) (hvmem : ∀ i, v i ∈ Set.Icc a b) {t : ℝ} (ht : t ∈ Set.Icc a b) :
    ∃ ξ ∈ Set.Ioo a b,
      f t - (Lagrange.interpolate Finset.univ v fun i => f (v i)).eval t
        = iteratedDeriv (n + 1) f ξ / (n + 1).factorial * ∏ i, (t - v i) :=
  exists_sub_interpolate_eq_of_contDiffOn hab isOpen_univ (Set.subset_univ _) hf.contDiffOn hv
    hvmem ht

/-- The value of a Lagrange basis function, as the product of the ratios
`(t - v j)/(v i - v j)` over the other nodes. -/
theorem eval_basis_eq_prod {F : Type*} [Field F] {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (v : ι → F) (i : ι) (t : F) :
    (Lagrange.basis s v i).eval t = ∏ j ∈ s.erase i, (t - v j) / (v i - v j) := by
  simp only [Lagrange.basis, Polynomial.eval_prod, Lagrange.basisDivisor, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
  exact Finset.prod_congr rfl fun j _ => (div_eq_inv_mul _ _).symm

/-- **A crude bound for a Lagrange basis function**: if the evaluation point is within `D` of every
node and the node `v i` is at distance at least `d` from every other node, then `|ℓ_i| ≤ (D/d)^m`,
with `m` the number of other nodes.

The bound is far from sharp — the sharp one is the Lebesgue function — but it is uniform over any
family of node systems with the same *shape*, which is what a piecewise polynomial interpolation
operator on a refining mesh needs: `D` and `d` are then both proportional to the panel length and
the ratio does not depend on the mesh. -/
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
        Finset.prod_le_prod (fun j _ => abs_nonneg _) hstep
    _ = (D / d) ^ ((Finset.univ : Finset ι).erase i).card := Finset.prod_const _


/-! ### The interpolation operator on continuous functions -/

variable {X : Set ℝ} [CompactSpace X] {n : ℕ}

/-- The `i`-th Lagrange basis polynomial for the nodes `x`, as a continuous function on `X`. -/
noncomputable def basisCM (x : Fin (n + 1) → X) (i : Fin (n + 1)) : C(X, ℝ) :=
  (Lagrange.basis Finset.univ (fun j => (x j : ℝ)) i).toContinuousMapOn X

omit [CompactSpace X] in
/-- The value of a Lagrange basis function is the value of the Lagrange basis polynomial. -/
theorem basisCM_apply (x : Fin (n + 1) → X) (i : Fin (n + 1)) (t : X) :
    basisCM x i t = (Lagrange.basis Finset.univ (fun j => (x j : ℝ)) i).eval (t : ℝ) := rfl

/-- The **Lagrange interpolation operator** at `n + 1` distinct nodes of a compact `X ⊆ ℝ`: the
bounded projection `f ↦ ∑ i, f (x i) • ℓ_i` of `C(X, ℝ)` onto the polynomials of degree at most `n`.
It is the projection `P` of the Lebesgue lemma `norm_sub_apply_le_of_isIdempotentElem`, whose
operator norm is the Lebesgue constant of the nodes.

Reference: [han2009theoretical], Example 3.6.5. -/
noncomputable def interpolateCLM (x : Fin (n + 1) → X) : C(X, ℝ) →L[ℝ] C(X, ℝ) :=
  ∑ i, (ContinuousMap.evalCLM (R := ℝ) (x i)).smulRight (basisCM x i)

/-- The Lagrange interpolant, as the combination `∑ i, f (x i) • ℓ_i` of the basis functions. -/
theorem interpolateCLM_apply (x : Fin (n + 1) → X) (f : C(X, ℝ)) (t : X) :
    interpolateCLM x f t = ∑ i, f (x i) * basisCM x i t := by
  simp [interpolateCLM]

/-- The interpolation operator is the evaluation of Mathlib's polynomial-valued
`Lagrange.interpolate`. -/
theorem interpolateCLM_apply_eq_eval (x : Fin (n + 1) → X) (f : C(X, ℝ)) (t : X) :
    interpolateCLM x f t
      = (Lagrange.interpolate Finset.univ (fun j => (x j : ℝ))
          (fun i => f (x i))).eval (t : ℝ) := by
  rw [interpolateCLM_apply, Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
  simp [basisCM_apply]

/-- The interpolant agrees with the function at the nodes. -/
theorem interpolateCLM_apply_node {x : Fin (n + 1) → X} (hx : Function.Injective x)
    (f : C(X, ℝ)) (j : Fin (n + 1)) : interpolateCLM x f (x j) = f (x j) := by
  have hinj : Function.Injective fun j => (x j : ℝ) := Subtype.val_injective.comp hx
  rw [interpolateCLM_apply_eq_eval,
    Lagrange.eval_interpolate_at_node _ hinj.injOn (Finset.mem_univ j)]

/-- The range of the interpolation operator is the space of polynomials of degree at most `n`. -/
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

/-- The interpolation operator is a projection: it fixes the polynomials of degree at most `n`, in
particular its own values. -/
theorem isIdempotentElem_interpolateCLM {x : Fin (n + 1) → X} (hx : Function.Injective x) :
    IsIdempotentElem (interpolateCLM x) := by
  have h : ∀ f : C(X, ℝ), interpolateCLM x (interpolateCLM x f) = interpolateCLM x f := by
    intro f
    ext t
    rw [interpolateCLM_apply, interpolateCLM_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [interpolateCLM_apply_node hx f i]
  exact ContinuousLinearMap.ext h

omit [CompactSpace X] in
/-- A Lagrange basis function takes the value `1` at its own node. -/
theorem basisCM_apply_node_self {x : Fin (n + 1) → X} (hx : Function.Injective x)
    (i : Fin (n + 1)) : basisCM x i (x i) = 1 := by
  have hinj : Function.Injective fun k => (x k : ℝ) := Subtype.val_injective.comp hx
  rw [basisCM_apply, Lagrange.eval_basis_self hinj.injOn (Finset.mem_univ i)]

omit [CompactSpace X] in
/-- A Lagrange basis function vanishes at the other nodes. -/
theorem basisCM_apply_node_ne {x : Fin (n + 1) → X} {i j : Fin (n + 1)} (hij : i ≠ j) :
    basisCM x i (x j) = 0 := by
  rw [basisCM_apply]
  exact Lagrange.eval_basis_of_ne (v := fun k => (x k : ℝ)) hij (Finset.mem_univ j)

omit [CompactSpace X] in
/-- A combination of the Lagrange basis functions takes the prescribed values at the nodes. -/
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
/-- The Lagrange basis functions of `n + 1` distinct nodes are polynomials of degree at most `n`,
so every combination of them is. -/
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

/-- **Lagrange interpolation is unisolvent**: at `n + 1` distinct nodes of `X` there is exactly one
polynomial of degree at most `n` taking prescribed values. This is the interpolation problem of
`Numlib/Approximation/Unisolvent` for the space `polyLE X n` and the point evaluations at the
nodes. -/
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

/-- The cardinal basis of the Lagrange interpolation problem is the Lagrange basis. -/
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
problem it solves. -/
theorem interpCLM_isUnisolvent_polyLE {x : Fin (n + 1) → X} (hx : Function.Injective x) :
    (isUnisolvent_polyLE hx).interpCLM = interpolateCLM x := by
  refine ContinuousLinearMap.ext fun f => ContinuousMap.ext fun t => ?_
  rw [Approximation.IsUnisolvent.interpCLM_apply, interpolateCLM_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [cardinalBasisCM_isUnisolvent_polyLE hx i]

/-- **The Lebesgue constant.** The operator norm of the interpolation operator is the largest value
of the Lebesgue function `t ↦ ∑ i, |ℓ_i t|`. It is the polynomial case of
`Approximation.IsUnisolvent.isGreatest_norm_interpCLM`.

Reference: [han2009theoretical], §3.7.3. -/
theorem isGreatest_norm_interpolateCLM [Nonempty X] {x : Fin (n + 1) → X}
    (hx : Function.Injective x) :
    IsGreatest (Set.range fun t : X => ∑ i, |basisCM x i t|) ‖interpolateCLM x‖ := by
  have h := (isUnisolvent_polyLE hx).isGreatest_norm_interpCLM
  rw [interpCLM_isUnisolvent_polyLE hx] at h
  simpa only [cardinalBasisCM_isUnisolvent_polyLE hx] using h

/-- The operator norm of the interpolation operator is the supremum of the Lebesgue function. -/
theorem norm_interpolateCLM [Nonempty X] {x : Fin (n + 1) → X} (hx : Function.Injective x) :
    ‖interpolateCLM x‖ = sSup (Set.range fun t : X => ∑ i, |basisCM x i t|) :=
  (isGreatest_norm_interpolateCLM hx).csSup_eq.symm

end Lagrange

/-! ### The modulus of continuity -/

namespace ContinuousMap

variable {X : Type*} [PseudoMetricSpace X]

/-- The **modulus of continuity** of a continuous function at the scale `δ`: the largest change
`|f u - f v|` of its value over pairs of points at distance at most `δ`.

It is a supremum, so it takes the junk value `0` when the set of such changes is empty or unbounded;
on a compact space it is a genuine supremum (`ContinuousMap.le_modulusOfContinuity`), and it tends
to `0` with `δ` exactly because a continuous function on a compact space is uniformly continuous. -/
noncomputable def modulusOfContinuity (f : C(X, ℝ)) (δ : ℝ) : ℝ :=
  sSup ((fun p : X × X => |f p.1 - f p.2|) '' {p : X × X | dist p.1 p.2 ≤ δ})

variable [CompactSpace X] (f : C(X, ℝ)) {δ : ℝ}

theorem bddAbove_modulusOfContinuity_image :
    BddAbove ((fun p : X × X => |f p.1 - f p.2|) '' {p : X × X | dist p.1 p.2 ≤ δ}) := by
  refine ⟨2 * ‖f‖, ?_⟩
  rintro r ⟨⟨u, v⟩, -, rfl⟩
  have hu : |f u| ≤ ‖f‖ := by simpa using f.norm_coe_le_norm u
  have hv : |f v| ≤ ‖f‖ := by simpa using f.norm_coe_le_norm v
  calc |f u - f v| ≤ |f u| + |f v| := abs_sub _ _
    _ ≤ 2 * ‖f‖ := by linarith

/-- The modulus of continuity bounds every change of value over a distance at most `δ`. -/
theorem le_modulusOfContinuity {u v : X} (huv : dist u v ≤ δ) :
    |f u - f v| ≤ f.modulusOfContinuity δ :=
  le_csSup (bddAbove_modulusOfContinuity_image f) ⟨(u, v), huv, rfl⟩

/-- The modulus of continuity is nonnegative at every nonnegative scale. -/
theorem modulusOfContinuity_nonneg [Nonempty X] (hδ : 0 ≤ δ) : 0 ≤ f.modulusOfContinuity δ := by
  obtain ⟨u⟩ := ‹Nonempty X›
  have := le_modulusOfContinuity f (u := u) (v := u) (by simpa using hδ)
  simpa using this

open Filter Topology in
/-- **The modulus of continuity tends to zero with the scale.** This is the uniform continuity of a
continuous function on a compact space, restated for the modulus: it is what turns every
approximation bound of the form `‖f - P f‖ ≤ ω(f, h)` into a convergence statement as the mesh `h`
tends to zero. -/
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

/-- The **clamped ramp** of `[u, v]`: the continuous function that vanishes below `u`, rises with
slope `1` on `[u, v]` and is constant equal to `v - u` above `v`.

A continuous piecewise-linear function on a partition is a combination of the ramps of its
subintervals, which is what lets the piecewise-linear interpolation operator be written without
gluing anything. -/
noncomputable def piecewiseLinearRamp (a b u v : ℝ) : C(Set.Icc a b, ℝ) :=
  ⟨fun t => min (max ((t : ℝ) - u) 0) (v - u),
    ((continuous_subtype_val.sub continuous_const).max continuous_const).min continuous_const⟩

/-- The value of the clamped ramp. -/
@[simp]
theorem piecewiseLinearRamp_apply (a b u v : ℝ) (t : Set.Icc a b) :
    piecewiseLinearRamp a b u v t = min (max ((t : ℝ) - u) 0) (v - u) := rfl

/-- **Piecewise-linear interpolation** on the partition `a = x 0 < x 1 < ⋯ < x (n + 1) = b` of `[a,
b]`: the bounded operator on `C([a, b], ℝ)` sending `f` to the continuous function that agrees with
`f` at every node and is affine on every subinterval.

The operator is written as the value at the first node plus the ramps of the subintervals scaled by
the divided differences of `f`, which makes linearity, boundedness and continuity immediate;
`piecewiseLinearInterpCLM_apply_of_mem` is the equivalent local description on one subinterval. The
nodes are given as a sequence, of which only `x 0, …, x (n + 1)` are used, so that the index
arithmetic of the subintervals stays in `ℕ`.

Reference: [han2009theoretical], §3.2.3 and Exercise 3.6.6; [kress1998numerical], §8.3. -/
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

/-- The piecewise-linear interpolant, as the value at the first node plus the ramps of the
subintervals scaled by the divided differences of `f`. -/
theorem piecewiseLinearInterpCLM_apply (n : ℕ) (x : ℕ → Set.Icc a b) (f : C(Set.Icc a b, ℝ))
    (t : Set.Icc a b) :
    piecewiseLinearInterpCLM n x f t = f (x 0) + ∑ i ∈ Finset.range (n + 1),
      (f (x (i + 1)) - f (x i)) / ((x (i + 1) : ℝ) - (x i : ℝ)) *
        min (max ((t : ℝ) - (x i : ℝ)) 0) ((x (i + 1) : ℝ) - (x i : ℝ)) := by
  simp [piecewiseLinearInterpCLM, div_eq_inv_mul, mul_assoc]

/-- The nodes of a partition increase along the used range. -/
private theorem le_node_of_le (hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ)) {i j : ℕ}
    (hij : i ≤ j)
    (hj : j ≤ n + 1) : (x i : ℝ) ≤ (x j : ℝ) := by
  revert hj
  induction j, hij using Nat.le_induction with
  | base => exact fun _ => le_rfl
  | succ k hk ih => exact fun hk1 => (ih (by omega)).trans (hstep k (by omega)).le

/-- Every point of `[a, b]` lies in one of the subintervals of the partition. -/
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

/-- **The local description of the piecewise-linear interpolant.** On the subinterval `[x j, x (j +
1)]` it is the affine function through `(x j, f (x j))` and `(x (j + 1), f (x (j + 1)))`. -/
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
    have hle : (x (i + 1) : ℝ) ≤ (t : ℝ) := (le_node_of_le hstep (by omega) (by omega)).trans h1
    have hmax : max ((t : ℝ) - (x i : ℝ)) 0 = (t : ℝ) - (x i : ℝ) := by
      refine max_eq_left ?_
      have : (x i : ℝ) ≤ (t : ℝ) := (le_node_of_le hstep (by omega) (by omega)).trans h1
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
    have hge : (t : ℝ) ≤ (x i : ℝ) := h2.trans (le_node_of_le hstep (by omega) (by omega))
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

/-- The piecewise-linear interpolant agrees with the function at every node. -/
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

/-- The piecewise-linear interpolation operator is a projection. -/
theorem isIdempotentElem_piecewiseLinearInterpCLM
    (hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ)) (hfirst : (x 0 : ℝ) = a)
    (hlast : (x (n + 1) : ℝ) = b) : IsIdempotentElem (piecewiseLinearInterpCLM n x) := by
  have h : ∀ f, piecewiseLinearInterpCLM n x (piecewiseLinearInterpCLM n x f)
      = piecewiseLinearInterpCLM n x f := by
    intro f
    refine ContinuousMap.ext fun t => ?_
    obtain ⟨j, hj, h1, h2⟩ := exists_mem_subinterval hfirst hlast t
    rw [piecewiseLinearInterpCLM_apply_of_mem hstep _ hj h1 h2,
      piecewiseLinearInterpCLM_apply_of_mem hstep f hj h1 h2,
      piecewiseLinearInterpCLM_apply_node hstep f (by omega),
      piecewiseLinearInterpCLM_apply_node hstep f (by omega)]
  exact ContinuousLinearMap.ext h

/-- The piecewise-linear interpolant never exceeds the function in sup norm: on each subinterval its
value is a convex combination of two values of the function. -/
theorem norm_piecewiseLinearInterpCLM_apply_le
    (hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ)) (hfirst : (x 0 : ℝ) = a)
    (hlast : (x (n + 1) : ℝ) = b) (f : C(Set.Icc a b, ℝ)) :
    ‖piecewiseLinearInterpCLM n x f‖ ≤ ‖f‖ := by
  refine (ContinuousMap.norm_le _ (norm_nonneg f)).mpr fun t => ?_
  obtain ⟨j, hj, h1, h2⟩ := exists_mem_subinterval hfirst hlast t
  have hd : (0 : ℝ) < (x (j + 1) : ℝ) - (x j : ℝ) := sub_pos.mpr (hstep j hj)
  set θ : ℝ := ((t : ℝ) - (x j : ℝ)) / ((x (j + 1) : ℝ) - (x j : ℝ)) with hθ
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hd.le
  have hθ1 : θ ≤ 1 := (div_le_one hd).mpr (by linarith)
  have hval : piecewiseLinearInterpCLM n x f t = (1 - θ) * f (x j) + θ * f (x (j + 1)) := by
    rw [piecewiseLinearInterpCLM_apply_of_mem hstep f hj h1 h2, ← hθ]
    ring
  have hb1 : |f (x j)| ≤ ‖f‖ := by simpa using f.norm_coe_le_norm (x j)
  have hb2 : |f (x (j + 1))| ≤ ‖f‖ := by simpa using f.norm_coe_le_norm (x (j + 1))
  rw [Real.norm_eq_abs, hval]
  calc |(1 - θ) * f (x j) + θ * f (x (j + 1))|
      ≤ |(1 - θ) * f (x j)| + |θ * f (x (j + 1))| := abs_add_le _ _
    _ = (1 - θ) * |f (x j)| + θ * |f (x (j + 1))| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - θ), abs_of_nonneg hθ0]
    _ ≤ (1 - θ) * ‖f‖ + θ * ‖f‖ := by gcongr
    _ = ‖f‖ := by ring

/-- **The piecewise-linear interpolation operator has norm one.** It is a projection of norm one
onto the continuous piecewise-linear functions of the partition, which is what makes its Lebesgue
constant the best possible.

Reference: [han2009theoretical], Exercise 3.6.6. -/
theorem norm_piecewiseLinearInterpCLM (hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ))
    (hfirst : (x 0 : ℝ) = a) (hlast : (x (n + 1) : ℝ) = b) :
    ‖piecewiseLinearInterpCLM n x‖ = 1 := by
  have hne : Nonempty (Set.Icc a b) := ⟨x 0⟩
  have hone : ‖(1 : C(Set.Icc a b, ℝ))‖ = 1 := by simp
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_) ?_
  · rw [one_mul]
    exact norm_piecewiseLinearInterpCLM_apply_le hstep hfirst hlast f
  · have hfix : piecewiseLinearInterpCLM n x 1 = 1 := by
      refine ContinuousMap.ext fun t => ?_
      obtain ⟨j, hj, h1, h2⟩ := exists_mem_subinterval hfirst hlast t
      rw [piecewiseLinearInterpCLM_apply_of_mem hstep 1 hj h1 h2]
      simp
    have := (piecewiseLinearInterpCLM n x).le_opNorm (1 : C(Set.Icc a b, ℝ))
    rw [hfix, hone, mul_one] at this
    exact this

/-- **The error of piecewise-linear interpolation.** On a partition of `[a, b]` of mesh at most `h`,
the piecewise-linear interpolant of a `C²` function differs from it by at most `h² ‖f''‖ / 8`.

The function is given as a `C²` map `ℝ → ℝ` agreeing with `f` on `[a, b]`, since `C(Icc a b, ℝ)`
carries no derivative; only the values of the second derivative on `[a, b]` are used.

The route is `piecewiseLinearInterpCLM_apply_of_mem`: on `[x j, x (j+1)]` the interpolant is the
affine function through the two node values, hence the Lagrange interpolant at those two nodes, so
`Lagrange.exists_sub_interpolate_eq` at `n = 1` applies on the subinterval, and `|(t - u)(t - v)| ≤
(v - u)²/4` finishes it.

Reference: [han2009theoretical], (3.2.9); [kress1998numerical], §8.3. -/
theorem norm_sub_piecewiseLinearInterpCLM_le (hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ))
    (hfirst : (x 0 : ℝ) = a) (hlast : (x (n + 1) : ℝ) = b) {g : ℝ → ℝ}
    (hg : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) g) {f : C(Set.Icc a b, ℝ)}
    (hf : ∀ t : Set.Icc a b, f t = g (t : ℝ)) {h M : ℝ}
    (hmesh : ∀ i ≤ n, (x (i + 1) : ℝ) - (x i : ℝ) ≤ h)
    (hM : ∀ t ∈ Set.Icc a b, |iteratedDeriv 2 g t| ≤ M) :
    ‖f - piecewiseLinearInterpCLM n x f‖ ≤ h ^ 2 / 8 * M := by
  classical
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM (x 0) (x 0).2)
  have hh0 : 0 ≤ h := le_trans (sub_nonneg.mpr (hstep 0 (Nat.zero_le n)).le)
    (hmesh 0 (Nat.zero_le n))
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro t
  obtain ⟨j, hj, h1, h2⟩ := exists_mem_subinterval hfirst hlast t
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
    have hvu : (0 : ℝ) ≤ (x (j + 1) : ℝ) - (x j : ℝ) := sub_nonneg.mpr huv.le
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

/-- **The piecewise-linear interpolation error for a merely continuous function.** On a partition
of `[a, b]` of mesh at most `h`, the piecewise-linear interpolant of a continuous `f` differs from
it by at most the modulus of continuity `ω(f, h)`.

On each subinterval the interpolant is a convex combination of the two node values, so the error is
the same convex combination of `f(t) - f(x j)` and `f(t) - f(x (j+1))`, and both nodes are within
`h` of `t`.

Reference: [han2009theoretical], (3.2.8); [kress1998numerical], §8.3. -/
theorem norm_sub_piecewiseLinearInterpCLM_le_modulus
    (hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ)) (hfirst : (x 0 : ℝ) = a)
    (hlast : (x (n + 1) : ℝ) = b) (f : C(Set.Icc a b, ℝ)) {h : ℝ}
    (hmesh : ∀ i ≤ n, (x (i + 1) : ℝ) - (x i : ℝ) ≤ h) :
    ‖f - piecewiseLinearInterpCLM n x f‖ ≤ f.modulusOfContinuity h := by
  have hne : Nonempty (Set.Icc a b) := ⟨x 0⟩
  have hh0 : 0 ≤ h := le_trans (sub_nonneg.mpr (hstep 0 (Nat.zero_le n)).le)
    (hmesh 0 (Nat.zero_le n))
  rw [ContinuousMap.norm_le _ (f.modulusOfContinuity_nonneg hh0)]
  intro t
  obtain ⟨j, hj, h1, h2⟩ := exists_mem_subinterval hfirst hlast t
  have hd : (0 : ℝ) < (x (j + 1) : ℝ) - (x j : ℝ) := sub_pos.mpr (hstep j hj)
  set θ : ℝ := ((t : ℝ) - (x j : ℝ)) / ((x (j + 1) : ℝ) - (x j : ℝ)) with hθ
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hd.le
  have hθ1 : θ ≤ 1 := (div_le_one hd).mpr (by linarith)
  have hval : piecewiseLinearInterpCLM n x f t = (1 - θ) * f (x j) + θ * f (x (j + 1)) := by
    rw [piecewiseLinearInterpCLM_apply_of_mem hstep f hj h1 h2, ← hθ]
    ring
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
/-- **Piecewise-linear interpolation converges uniformly for every continuous function** as the
mesh of the partitions tends to zero. The bound is the modulus of continuity
(`norm_sub_piecewiseLinearInterpCLM_le_modulus`), which tends to zero with the mesh
(`ContinuousMap.tendsto_modulusOfContinuity`); no differentiability of `f` is used, and it is this
statement — not the `h²` bound for a `C²` function — that a projection method needs in order to
satisfy the hypothesis `P_n u → u` of the Banach–Steinhaus argument.

Reference: [han2009theoretical], (3.2.8). -/
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
  exact norm_sub_piecewiseLinearInterpCLM_le_modulus (hstep n) (hfirst n) (hlast n) f (hmesh n)

end PiecewiseLinear

/-! ### Piecewise polynomial interpolation of degree `m` -/

/-- **A panel node system of degree `m`.** The breakpoints `a = x 0 < x 1 < ⋯ < x (n + 1) = b` cut
`[a, b]` into `n + 1` panels, and each panel `[x j, x (j + 1)]` carries `m + 1` distinct
interpolation nodes `node j 0, …, node j m`, of which the first and the last are the endpoints of
the panel.

The endpoint condition is what makes the panel interpolants agree where two panels meet, so that
the piecewise polynomial interpolant is continuous; the interior nodes are arbitrary, and are
usually the images of a fixed partition `0 = μ_0 < ⋯ < μ_m = 1` of the unit interval under the
affine map onto the panel. -/
structure IsPanelNodes {a b : ℝ} (n m : ℕ) (x : ℕ → Set.Icc a b)
    (node : ℕ → Fin (m + 1) → Set.Icc a b) : Prop where
  /-- The breakpoints increase along the used range. -/
  step : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ)
  /-- The first breakpoint is the left endpoint of the interval. -/
  first : (x 0 : ℝ) = a
  /-- The last breakpoint is the right endpoint of the interval. -/
  last : (x (n + 1) : ℝ) = b
  /-- The nodes of a panel lie in that panel. -/
  mem : ∀ j ≤ n, ∀ i, ((node j i : ℝ)) ∈ Set.Icc ((x j : ℝ)) ((x (j + 1) : ℝ))
  /-- The nodes of a panel are distinct. -/
  injective : ∀ j ≤ n, Function.Injective fun i => ((node j i : ℝ))
  /-- The first node of a panel is its left endpoint. -/
  node_zero : ∀ j ≤ n, node j 0 = x j
  /-- The last node of a panel is its right endpoint. -/
  node_last : ∀ j ≤ n, node j (Fin.last m) = x (j + 1)

/-- The **panel interpolant**: the Lagrange interpolation polynomial of `f` at the `m + 1` nodes of
the panel `[x j, x (j + 1)]`. -/
noncomputable def panelPoly {a b : ℝ} {m : ℕ} (node : ℕ → Fin (m + 1) → Set.Icc a b) (j : ℕ)
    (f : C(Set.Icc a b, ℝ)) : ℝ[X] :=
  Lagrange.interpolate Finset.univ (fun p => ((node j p : ℝ))) fun i => f (node j i)

/-- The `i`-th Lagrange basis function of the nodes of the panel `[x j, x (j + 1)]`, **clamped to
that panel**: at a point outside the panel it takes the value it has at the nearer endpoint.

Clamping is what lets the piecewise polynomial interpolant be written as a *sum* over the panels,
exactly as `piecewiseLinearRamp` does for degree one: in `piecewisePolyInterpCLM_apply` the panels
to the left of the evaluation point contribute their full increment, those to the right contribute
nothing, and the sum telescopes. -/
noncomputable def panelBasis {a b : ℝ} {m : ℕ} (x : ℕ → Set.Icc a b)
    (node : ℕ → Fin (m + 1) → Set.Icc a b) (j : ℕ) (i : Fin (m + 1)) : C(Set.Icc a b, ℝ) :=
  ⟨fun t => (Lagrange.basis Finset.univ (fun p => ((node j p : ℝ))) i).eval
      (min (max (t : ℝ) ((x j : ℝ))) ((x (j + 1) : ℝ))),
    (Polynomial.continuous _).comp
      ((continuous_subtype_val.max continuous_const).min continuous_const)⟩

/-- The value of a clamped panel basis function. -/
@[simp]
theorem panelBasis_apply {a b : ℝ} {m : ℕ} (x : ℕ → Set.Icc a b)
    (node : ℕ → Fin (m + 1) → Set.Icc a b) (j : ℕ) (i : Fin (m + 1)) (t : Set.Icc a b) :
    panelBasis x node j i t = (Lagrange.basis Finset.univ (fun p => ((node j p : ℝ))) i).eval
      (min (max (t : ℝ) ((x j : ℝ))) ((x (j + 1) : ℝ))) := rfl

/-- **The panel interpolation operator**: the Lagrange interpolant at the nodes of the panel
`[x j, x (j + 1)]`, evaluated at the point of that panel nearest to the argument. -/
noncomputable def panelInterpCLM {a b : ℝ} (m : ℕ) (x : ℕ → Set.Icc a b)
    (node : ℕ → Fin (m + 1) → Set.Icc a b) (j : ℕ) :
    C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ) :=
  ∑ i, (ContinuousMap.evalCLM ℝ (node j i)).smulRight (panelBasis x node j i)

/-- **Piecewise polynomial interpolation of degree `m`** on the partition
`a = x 0 < x 1 < ⋯ < x (n + 1) = b` of `[a, b]`: the bounded operator on `C([a, b], ℝ)` sending `f`
to the continuous function that agrees on each panel `[x j, x (j + 1)]` with the polynomial of
degree at most `m` interpolating `f` at the `m + 1` nodes of that panel.

Continuity across a breakpoint holds because both panels meeting there interpolate `f` at it, and
the operator is written so that this is all it takes: it is the value at the first breakpoint plus
the increments `panelInterpCLM j f t - panelInterpCLM j f (x j)` of the clamped panel interpolants,
a sum which telescopes to the interpolant of the panel containing `t`
(`piecewisePolyInterpCLM_apply_of_mem`).  Linearity, boundedness and continuity are therefore
immediate, as they are for `piecewiseLinearInterpCLM`, which is the case `m = 1`.

Reference: [han2009theoretical], §12.3.2 and (12.5.32). -/
noncomputable def piecewisePolyInterpCLM {a b : ℝ} (n m : ℕ) (x : ℕ → Set.Icc a b)
    (node : ℕ → Fin (m + 1) → Set.Icc a b) : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ) :=
  (ContinuousMap.evalCLM ℝ (x 0)).smulRight 1 +
    ∑ j ∈ Finset.range (n + 1),
      (panelInterpCLM m x node j -
        (ContinuousMap.evalCLM ℝ (x j)).smulRight (1 : C(Set.Icc a b, ℝ)) ∘L
          panelInterpCLM m x node j)

section PiecewisePolynomial

variable {a b : ℝ} {n m : ℕ} {x : ℕ → Set.Icc a b} {node : ℕ → Fin (m + 1) → Set.Icc a b}

/-- The panel interpolation operator evaluates the panel interpolant at the clamped argument. -/
theorem panelInterpCLM_apply (m : ℕ) (x : ℕ → Set.Icc a b)
    (node : ℕ → Fin (m + 1) → Set.Icc a b) (j : ℕ) (f : C(Set.Icc a b, ℝ)) (t : Set.Icc a b) :
    panelInterpCLM m x node j f t
      = (panelPoly node j f).eval (min (max (t : ℝ) ((x j : ℝ))) ((x (j + 1) : ℝ))) := by
  simp [panelInterpCLM, panelPoly, Lagrange.interpolate_apply, Polynomial.eval_finsetSum]

/-- The piecewise polynomial interpolant, as the value at the first breakpoint plus the increments
of the clamped panel interpolants. -/
theorem piecewisePolyInterpCLM_apply (n m : ℕ) (x : ℕ → Set.Icc a b)
    (node : ℕ → Fin (m + 1) → Set.Icc a b) (f : C(Set.Icc a b, ℝ)) (t : Set.Icc a b) :
    piecewisePolyInterpCLM n m x node f t = f (x 0) +
      ∑ j ∈ Finset.range (n + 1),
        (panelInterpCLM m x node j f t - panelInterpCLM m x node j f (x j)) := by
  simp [piecewisePolyInterpCLM]

/-- A panel interpolant reproduces the value of `f` at the left endpoint of its panel. -/
theorem eval_panelPoly_left (h : IsPanelNodes n m x node) (f : C(Set.Icc a b, ℝ)) {j : ℕ}
    (hj : j ≤ n) : (panelPoly node j f).eval ((x j : ℝ)) = f (x j) := by
  have hval := Lagrange.eval_interpolate_at_node (s := (Finset.univ : Finset (Fin (m + 1))))
    (v := fun p => ((node j p : ℝ))) (r := fun i => f (node j i)) (i := (0 : Fin (m + 1)))
    (h.injective j hj).injOn (Finset.mem_univ _)
  rw [h.node_zero j hj] at hval
  exact hval

/-- A panel interpolant reproduces the value of `f` at the right endpoint of its panel. -/
theorem eval_panelPoly_right (h : IsPanelNodes n m x node) (f : C(Set.Icc a b, ℝ)) {j : ℕ}
    (hj : j ≤ n) : (panelPoly node j f).eval ((x (j + 1) : ℝ)) = f (x (j + 1)) := by
  have hval := Lagrange.eval_interpolate_at_node (s := (Finset.univ : Finset (Fin (m + 1))))
    (v := fun p => ((node j p : ℝ))) (r := fun i => f (node j i)) (i := Fin.last m)
    (h.injective j hj).injOn (Finset.mem_univ _)
  rw [h.node_last j hj] at hval
  exact hval

/-- **The local description of the piecewise polynomial interpolant.** On the panel
`[x k, x (k + 1)]` it is the Lagrange interpolant of `f` at the nodes of that panel. -/
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
    have hle : (x (j + 1) : ℝ) ≤ (t : ℝ) := (le_node_of_le h.step (by omega) (by omega)).trans h1
    have hlej : (x j : ℝ) ≤ (t : ℝ) := (h.step j hjn).le.trans hle
    rw [hF]
    simp only
    rw [panelInterpCLM_apply, max_eq_left hlej, min_eq_right hle,
      eval_panelPoly_right h f hjn, hself j hjn]
  -- the panels to the right of `t` contribute nothing
  have hafter : ∀ j, k < j → j ≤ n → F j = 0 := by
    intro j hj hjn
    have hge : (t : ℝ) ≤ (x j : ℝ) := h2.trans (le_node_of_le h.step (by omega) (by omega))
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


/-- **A uniform local Lebesgue constant** for a panel node system: `Λ` bounds, on every panel, the
sum of the absolute values of the Lagrange basis functions of that panel's nodes.  It is the
operator norm bound of `norm_piecewisePolyInterpCLM_le`.

When the nodes of every panel are the images of one fixed partition `0 = μ_0 < ⋯ < μ_m = 1` of the
unit interval under the affine map onto the panel, the basis functions are the same functions of
the normalized variable on every panel, so the smallest such `Λ` is the Lebesgue constant of that
partition alone and does not depend on the mesh. -/
def IsPanelLebesgueBound {a b : ℝ} (n m : ℕ) (x : ℕ → Set.Icc a b)
    (node : ℕ → Fin (m + 1) → Set.Icc a b) (Λ : ℝ) : Prop :=
  ∀ j ≤ n, ∀ s ∈ Set.Icc ((x j : ℝ)) ((x (j + 1) : ℝ)),
    ∑ i, |(Lagrange.basis Finset.univ (fun p => ((node j p : ℝ))) i).eval s| ≤ Λ

section PiecewisePolynomialApi

variable {a b : ℝ} {n m : ℕ} {x : ℕ → Set.Icc a b} {node : ℕ → Fin (m + 1) → Set.Icc a b}

/-- The piecewise polynomial interpolant agrees with the function at every interpolation node. -/
theorem piecewisePolyInterpCLM_apply_node (h : IsPanelNodes n m x node) (f : C(Set.Icc a b, ℝ))
    {j : ℕ} (hj : j ≤ n) (i : Fin (m + 1)) :
    piecewisePolyInterpCLM n m x node f (node j i) = f (node j i) := by
  have hmem := h.mem j hj i
  rw [piecewisePolyInterpCLM_apply_of_mem h f hj hmem.1 hmem.2, panelPoly]
  exact Lagrange.eval_interpolate_at_node _ (h.injective j hj).injOn (Finset.mem_univ i)

/-- The piecewise polynomial interpolant agrees with the function at every breakpoint. -/
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

/-- The piecewise polynomial interpolation operator is a projection: it fixes every function that
is already a polynomial of degree at most `m` on each panel, since such a function is its own
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

/-- A Lebesgue bound is nonnegative. -/
theorem IsPanelLebesgueBound.nonneg (h : IsPanelNodes n m x node) {Λ : ℝ}
    (hΛ : IsPanelLebesgueBound n m x node Λ) : 0 ≤ Λ :=
  le_trans (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (hΛ 0 (Nat.zero_le n) ((x 0 : ℝ)) ⟨le_rfl, (h.step 0 (Nat.zero_le n)).le⟩)

/-- **A Lebesgue bound from the shape of the panel node systems alone.**  If the nodes of the panel
`j` are at mutual distance at least `d j` and the panel is at most `ρ (d j)` long, then
`(m + 1) ρ^m` is a Lebesgue bound.

The separation is allowed to vary from panel to panel, only the *ratio* `ρ` being uniform, which is
what a graded mesh needs: with the nodes placed at fixed fractions of every panel, `d j` and the
length of the panel are both proportional to that length, so `ρ` is the same for every panel of
every mesh of the family however unequal the panels are. -/
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

/-- **The piecewise polynomial interpolant is bounded by the local Lebesgue constant**: on the
panel containing the evaluation point it is the combination `∑ f (node k i) ℓ_i` of the panel's
basis functions. -/
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
constant**, uniformly in the mesh. -/
theorem norm_piecewisePolyInterpCLM_le (h : IsPanelNodes n m x node) {Λ : ℝ}
    (hΛ : IsPanelLebesgueBound n m x node Λ) : ‖piecewisePolyInterpCLM n m x node‖ ≤ Λ :=
  ContinuousLinearMap.opNorm_le_bound _ (hΛ.nonneg h) fun f =>
    norm_piecewisePolyInterpCLM_apply_le h hΛ f

/-- **The error formula of piecewise polynomial interpolation on one panel, for a function smooth
only near that panel.** Only the smoothness of `G` on an open set containing the panel is used, so
a function singular at an endpoint of `[a, b]` — as the solution of a weakly singular equation is —
still obeys the formula on every panel that stays away from the singularity. -/
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

/-- **The error formula of piecewise polynomial interpolation.** On the panel containing `t` the
interpolant is the Lagrange interpolant at that panel's nodes, so the Lagrange error formula
applies on the panel: the error is `G^{(m+1)}(ξ)/(m+1)!` times the nodal polynomial of the panel,
for some `ξ` strictly inside it.

The function is given as a `C^{m+1}` map `ℝ → ℝ` agreeing with `f` on `[a, b]`, since
`C(Icc a b, ℝ)` carries no derivative. -/
theorem exists_sub_piecewisePolyInterpCLM_apply_eq (h : IsPanelNodes n m x node) {G : ℝ → ℝ}
    (hG : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) G) {f : C(Set.Icc a b, ℝ)}
    (hf : ∀ t : Set.Icc a b, f t = G ((t : ℝ))) {k : ℕ} (hk : k ≤ n) {t : Set.Icc a b}
    (h1 : (x k : ℝ) ≤ (t : ℝ)) (h2 : (t : ℝ) ≤ (x (k + 1) : ℝ)) :
    ∃ ξ ∈ Set.Ioo ((x k : ℝ)) ((x (k + 1) : ℝ)),
      f t - piecewisePolyInterpCLM n m x node f t
        = iteratedDeriv (m + 1) G ξ / (m + 1).factorial * ∏ i, ((t : ℝ) - ((node k i : ℝ))) :=
  exists_sub_piecewisePolyInterpCLM_apply_eq_of_contDiffOn h isOpen_univ hk (Set.subset_univ _)
    hG.contDiffOn hf h1 h2

/-- **The error of piecewise polynomial interpolation of degree `m`.** If the nodal polynomial of
every panel is bounded by `W` on that panel and `|G^{(m+1)}| ≤ M` on `[a, b]`, the interpolation
error is at most `W M / (m + 1)!`.

For equally spaced panels of length `h` with the nodes at the breakpoints one may take
`W = h^{m+1}`, but the sharp value of `W` is smaller and is what produces the classical constants:
`h²/4` for `m = 1`, giving `h² ‖G''‖/8`, and `2 √3 h³/9` on a panel of length `2 h` for `m = 2`,
giving `√3 h³ ‖G'''‖/27`. -/
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

/-- **The piecewise polynomial interpolation error on one panel, from the oscillation of `f`
there**: at most `(1 + Λ) ω`, where `ω` bounds `|f - f (x k)|` on the panel and `Λ` is the local
Lebesgue constant.

On the panel containing `t` the interpolant is `∑ f (node k i) ℓ_i`, and the basis functions sum to
one, so subtracting `f (x k)` from every value turns the error into
`(f t - f (x k)) - ∑ (f (node k i) - f (x k)) ℓ_i (t)`, in which every difference of values of `f`
is taken between two points of the panel.  Only the oscillation on *that* panel enters, which is
what a graded mesh needs: the panel adjacent to a singularity is handled by a Hölder bound and the
others by the derivative bound. -/
theorem abs_sub_piecewisePolyInterpCLM_apply_le_of_osc (h : IsPanelNodes n m x node) {Λ : ℝ}
    (hΛ : IsPanelLebesgueBound n m x node Λ) (f : C(Set.Icc a b, ℝ)) {k : ℕ} (hk : k ≤ n)
    {t : Set.Icc a b} (h1 : (x k : ℝ) ≤ (t : ℝ)) (h2 : (t : ℝ) ≤ (x (k + 1) : ℝ)) {ω : ℝ}
    (hω : ∀ s : Set.Icc a b, (x k : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ (x (k + 1) : ℝ) →
      |f s - f (x k)| ≤ ω) :
    |f t - piecewisePolyInterpCLM n m x node f t| ≤ (1 + Λ) * ω := by
  have hΛ0 : 0 ≤ Λ := hΛ.nonneg h
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

/-- **The piecewise polynomial interpolation error for a merely continuous function**: at most
`(1 + Λ) ω(f, h)` on a mesh of size `h`, with `Λ` the local Lebesgue constant.  This is
`abs_sub_piecewisePolyInterpCLM_apply_le_of_osc` with the modulus of continuity as the panel
oscillation bound. -/
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
/-- **Piecewise polynomial interpolation of degree `m` converges uniformly for every continuous
function** as the mesh tends to zero, provided the local Lebesgue constants stay bounded.  This is
the hypothesis `P_n u → u` that a projection or a product integration method needs. -/
theorem tendsto_piecewisePolyInterpCLM {N : ℕ → ℕ} {y : ℕ → ℕ → Set.Icc a b}
    {nd : ℕ → ℕ → Fin (m + 1) → Set.Icc a b} {hs : ℕ → ℝ} {Λ : ℝ}
    (h : ∀ p, IsPanelNodes (N p) m (y p) (nd p))
    (hΛ : ∀ p, IsPanelLebesgueBound (N p) m (y p) (nd p) Λ)
    (hmesh : ∀ p, ∀ j ≤ N p, (y p (j + 1) : ℝ) - (y p j : ℝ) ≤ hs p)
    (hh : Tendsto hs atTop (𝓝 0)) (f : C(Set.Icc a b, ℝ)) :
    Tendsto (fun p => piecewisePolyInterpCLM (N p) m (y p) (nd p) f) atTop (𝓝 f) := by
  have hne : Nonempty (Set.Icc a b) := ⟨y 0 0⟩
  have hΛ0 : 0 ≤ Λ := (hΛ 0).nonneg (h 0)
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

end PiecewisePolynomialApi


/-! ### Trigonometric interpolation -/

section Trigonometric

/-- **Trigonometric interpolation at `2 n + 1` distinct nodes of a period is unisolvent.** The
Haar condition it feeds on is `haarCondition_trigPolyLE`, proved with the rest of the Haar theory
in `Numlib.Approximation.Chebyshev`. -/
theorem isUnisolvent_trigPolyLE (T : ℝ) [hT : Fact (0 < T)] {n : ℕ}
    {x : Fin (2 * n + 1) → AddCircle T} (hx : Function.Injective x) :
    Approximation.IsUnisolvent (trigPolyLE T n) fun i => ContinuousMap.evalCLM ℝ (x i) :=
  (Approximation.haarCondition_iff_isUnisolvent (trigPolyLE T n)
    (finrank_trigPolyLE T n)).mp (haarCondition_trigPolyLE hT.out.ne' n) x hx

/-- The `2 n + 1` **equispaced nodes** of a period: `x j = j T / (2 n + 1)`. -/
noncomputable def trigInterpNode (T : ℝ) (n : ℕ) (j : Fin (2 * n + 1)) : AddCircle T :=
  (((j : ℕ) * T / (2 * n + 1) : ℝ) : AddCircle T)

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

/-- **Trigonometric interpolation** at the `2 n + 1` equispaced nodes of a period: the bounded
projection of `C(AddCircle T, ℝ)` onto the trigonometric polynomials of degree at most `n`. -/
noncomputable def trigInterpCLM (T : ℝ) [Fact (0 < T)] (n : ℕ) :
    C(AddCircle T, ℝ) →L[ℝ] C(AddCircle T, ℝ) :=
  (isUnisolvent_trigPolyLE T (injective_trigInterpNode T n)).interpCLM

variable {T : ℝ} [Fact (0 < T)] {n : ℕ}

@[simp]
theorem trigInterpCLM_apply_node (f : C(AddCircle T, ℝ)) (j : Fin (2 * n + 1)) :
    trigInterpCLM T n f (trigInterpNode T n j) = f (trigInterpNode T n j) :=
  (isUnisolvent_trigPolyLE T (injective_trigInterpNode T n)).interpCLM_apply_node f j

theorem trigInterpCLM_mem (f : C(AddCircle T, ℝ)) : trigInterpCLM T n f ∈ trigPolyLE T n :=
  (isUnisolvent_trigPolyLE T (injective_trigInterpNode T n)).interpCLM_mem f

theorem trigInterpCLM_eq_self {g : C(AddCircle T, ℝ)} (hg : g ∈ trigPolyLE T n) :
    trigInterpCLM T n g = g :=
  (isUnisolvent_trigPolyLE T (injective_trigInterpNode T n)).interpCLM_eq_self hg

theorem range_trigInterpCLM :
    LinearMap.range (trigInterpCLM T n : C(AddCircle T, ℝ) →ₗ[ℝ] C(AddCircle T, ℝ))
      = trigPolyLE T n :=
  (isUnisolvent_trigPolyLE T (injective_trigInterpNode T n)).range_interpCLM

theorem isIdempotentElem_trigInterpCLM : IsIdempotentElem (trigInterpCLM T n) :=
  (isUnisolvent_trigPolyLE T (injective_trigInterpNode T n)).isIdempotentElem_interpCLM

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

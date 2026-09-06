import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Topology.TietzeExtension
import Numlib.Approximation.Chebyshev

/-!
# Polynomial interpolation and its error

Lagrange interpolation at `n + 1` distinct nodes, with the classical error formula `f(t) - p(t) =
f^{(n+1)}(ξ)/(n+1)! ∏ (t - x_i)`. The material is [Atkinson–Han, *Theoretical Numerical
Analysis*][han2009theoretical] §3.2 and [Kress, *Numerical Analysis*][kress1998numerical] §8.1 and
§8.3.

## Main definitions

* `Lagrange.basisCM x i` and `Lagrange.interpolateCLM x` are the Lagrange basis functions and the
  interpolation operator on `C(X, ℝ)`, for a compact `X ⊆ ℝ`.
* `piecewiseLinearRamp` and `piecewiseLinearInterpCLM` are the clamped ramp of a subinterval and
  the piecewise-linear interpolation operator on a partition, which is a combination of ramps.

## Main results

* `exists_iteratedDeriv_eq_zero_of_forall_eq_zero` is the **generalized Rolle theorem**: a
  `C^{n+1}` function vanishing at `n + 2` points of `[a, b]` has a zero of its `(n+1)`-st
  derivative strictly inside `[a, b]`. Applied to `s ↦ f s - p s - c ∏ (s - x_i)` with `c` chosen
  to make the value at `t` vanish, it gives the error formula
  `Lagrange.exists_sub_interpolate_eq`.
* `Lagrange.isGreatest_norm_interpolateCLM` and `Lagrange.norm_interpolateCLM` identify the
  operator norm of the interpolation operator with the **Lebesgue constant** of its nodes, the
  largest value of `t ↦ ∑ i, |ℓ_i t|`.
* `norm_piecewiseLinearInterpCLM` says that piecewise-linear interpolation has norm one, and
  `norm_sub_piecewiseLinearInterpCLM_le` bounds its error on a mesh of size `h` by
  `h² ‖f''‖ / 8` — the two-node case of the same error formula.

## Implementation notes

The bound on the piecewise-linear error by the modulus of continuity of a merely continuous `f`
is not stated: nothing in the library defines a modulus of continuity yet.
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

/-- **The generalized Rolle theorem.** A function of class `C^{n+1}` that vanishes at `n + 2`
distinct points of `[a, b]` has a zero of its `(n + 1)`-st derivative strictly inside `[a, b]`.

Reference: Kress, *Numerical Analysis*, §8.1. -/
theorem exists_iteratedDeriv_eq_zero_of_forall_eq_zero {n : ℕ} {a b : ℝ}
    {f : ℝ → ℝ} (hf : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f) {s : Finset ℝ}
    (hcard : n + 2 ≤ s.card) (hsub : ∀ t ∈ s, t ∈ Set.Icc a b) (hzero : ∀ t ∈ s, f t = 0) :
    ∃ c ∈ Set.Ioo a b, iteratedDeriv (n + 1) f c = 0 := by
  obtain ⟨s', hs's, hs'card⟩ := Finset.exists_subset_card_eq hcard
  set y : Fin (n + 2) → ℝ := ⇑(s'.orderEmbOfFin hs'card) with hy
  have hymem : ∀ i, y i ∈ Set.Icc a b := fun i =>
    hsub _ (hs's (Finset.orderEmbOfFin_mem s' hs'card i))
  have hymono : StrictMono y := (s'.orderEmbOfFin hs'card).strictMono
  have hyzero : ∀ i, f (y i) = 0 := fun i =>
    hzero _ (hs's (Finset.orderEmbOfFin_mem s' hs'card i))
  -- differentiability of the successive derivatives
  have hdiff : ∀ k < n + 1, Differentiable ℝ (iteratedDeriv k f) := by
    intro k hk
    exact hf.differentiable_iteratedDeriv k (by exact_mod_cast hk)
  have hstep : ∀ k < n + 1, ∀ t : ℝ,
      HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f t) t := by
    intro k hk t
    have h := ((hdiff k hk) t).hasDerivAt
    rwa [← iteratedDeriv_succ] at h
  -- one Rolle step, then the induction
  have hrolle : ∀ i : Fin (n + 1), ∃ c ∈ Set.Ioo (y i.castSucc) (y i.succ),
      iteratedDeriv 1 f c = 0 := by
    intro i
    refine exists_hasDerivAt_eq_zero (f := iteratedDeriv 0 f)
      (hymono (Fin.castSucc_lt_succ (i := i))) ?_ ?_ ?_
    · exact (hdiff 0 (Nat.succ_pos n)).continuous.continuousOn
    · simpa using (hyzero _).trans (hyzero _).symm
    · exact fun t _ => hstep 0 (Nat.succ_pos n) t
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
    (fun k hk => (hdiff (k + 1) (by omega)).continuous.continuousOn)
    (fun k hk t _ => hstep (k + 1) (by omega) t) z hzmono hzmem hz0
  refine ⟨c, ⟨?_, ?_⟩, hc0⟩
  · exact lt_of_lt_of_le (lt_of_le_of_lt (hymem 0).1 (by simpa using (hz 0).1)) hc.1
  · exact lt_of_le_of_lt hc.2 (lt_of_lt_of_le (by simpa using (hz (Fin.last n)).2)
      (hymem (Fin.last (n + 1))).2)

/-! ### The interpolation error formula -/

namespace Lagrange

/-- **The Lagrange interpolation error formula.** For `f` of class `C^{n+1}` and `n + 1` distinct
nodes in `[a, b]`, the error of the interpolating polynomial at a point `t` of `[a, b]` is
`f^{(n+1)}(ξ)/(n+1)!` times the nodal polynomial `∏ (t - x_i)`, for some `ξ` strictly inside
`[a, b]`.

Reference: Kress, *Numerical Analysis*, Theorem 8.4; Atkinson–Han, *Theoretical Numerical Analysis*,
§3.2. -/
theorem exists_sub_interpolate_eq {n : ℕ} {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f) {v : Fin (n + 1) → ℝ}
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
    obtain ⟨ξ, hξ, hξ0⟩ :=
      exists_iteratedDeriv_eq_zero_of_forall_eq_zero (hf.sub hQdiff) hscard hssub hgzero
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
      iteratedDeriv_fun_sub hf.contDiffAt hQdiff.contDiffAt
    rw [hsub', hQder] at hξ0
    have hfact : ((n + 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hceq : c = iteratedDeriv (n + 1) f ξ / (n + 1).factorial := by
      field_simp
      linarith [hξ0]
    rw [← hWeval, ← hceq, hc]
    field_simp

/-! ### The interpolation operator on continuous functions -/

variable {X : Set ℝ} [CompactSpace X] {n : ℕ}

/-- The `i`-th Lagrange basis polynomial for the nodes `x`, as a continuous function on `X`. -/
noncomputable def basisCM (x : Fin (n + 1) → X) (i : Fin (n + 1)) : C(X, ℝ) :=
  (Lagrange.basis Finset.univ (fun j => (x j : ℝ)) i).toContinuousMapOn X

omit [CompactSpace X] in
/-- The value of a Lagrange basis function is the value of the Lagrange basis polynomial. -/
theorem basisCM_apply (x : Fin (n + 1) → X) (i : Fin (n + 1)) (t : X) :
    basisCM x i t = (Lagrange.basis Finset.univ (fun j => (x j : ℝ)) i).eval (t : ℝ) := rfl

/-- The **Lagrange interpolation operator** at `n + 1` distinct nodes of a compact `X ⊆ ℝ`:
the bounded projection `f ↦ ∑ i, f (x i) • ℓ_i` of `C(X, ℝ)` onto the polynomials of degree at
most `n`. It is the projection `P` of the Lebesgue lemma
`norm_sub_apply_le_of_isIdempotentElem`, whose operator norm is the Lebesgue constant of the
nodes.

Reference: Atkinson–Han, *Theoretical Numerical Analysis*, Example 3.6.5. -/
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

/-- The interpolation operator is a projection: it fixes the polynomials of degree at most
`n`, in particular its own values. -/
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

/-- **The Lebesgue constant.** The operator norm of the interpolation operator is the largest
value of the Lebesgue function `t ↦ ∑ i, |ℓ_i t|`.

The upper bound is the triangle inequality. The lower bound needs a continuous function of norm
at most `1` taking the sign of `ℓ_i t₀` at the node `x i`: the combination
`∑ i, sign (ℓ_i t₀) • ℓ_i` already takes those values at the nodes, and the Tietze extension
theorem replaces it by a function with the same values whose range lies in `[-1, 1]`.

Reference: Atkinson–Han, *Theoretical Numerical Analysis*, §3.7.3. -/
theorem isGreatest_norm_interpolateCLM [Nonempty X] {x : Fin (n + 1) → X}
    (hx : Function.Injective x) :
    IsGreatest (Set.range fun t : X => ∑ i, |basisCM x i t|) ‖interpolateCLM x‖ := by
  classical
  have hcont : Continuous fun t : X => ∑ i, |basisCM x i t| :=
    continuous_finsetSum _ fun i _ => (basisCM x i).continuous.abs
  obtain ⟨t₀, -, hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hcont.continuousOn
  set M : ℝ := ∑ i, |basisCM x i t₀| with hM
  have hmax' : ∀ t : X, (∑ i, |basisCM x i t|) ≤ M := fun t => hmax (Set.mem_univ t)
  have hMnn : (0 : ℝ) ≤ M := by
    rw [hM]
    positivity
  -- the upper bound
  have hle : ‖interpolateCLM x‖ ≤ M := by
    refine ContinuousLinearMap.opNorm_le_bound _ hMnn fun f => ?_
    rw [ContinuousMap.norm_le _ (by positivity)]
    intro t
    rw [Real.norm_eq_abs, interpolateCLM_apply]
    calc |∑ i, f (x i) * basisCM x i t| ≤ ∑ i, |f (x i) * basisCM x i t| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |f (x i)| * |basisCM x i t| := by simp [abs_mul]
      _ ≤ ∑ i, ‖f‖ * |basisCM x i t| := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hfi := f.norm_coe_le_norm (x i)
          rw [Real.norm_eq_abs] at hfi
          exact mul_le_mul_of_nonneg_right hfi (abs_nonneg _)
      _ = ‖f‖ * ∑ i, |basisCM x i t| := by rw [Finset.mul_sum]
      _ ≤ M * ‖f‖ := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right (hmax' t) (norm_nonneg _)
  -- the lower bound
  have hge : M ≤ ‖interpolateCLM x‖ := by
    set σ : Fin (n + 1) → ℝ := fun i => if 0 ≤ basisCM x i t₀ then 1 else -1 with hσ
    have hσmul : ∀ i, σ i * basisCM x i t₀ = |basisCM x i t₀| := by
      intro i
      by_cases hb : 0 ≤ basisCM x i t₀
      · simp [hσ, hb, abs_of_nonneg hb]
      · simp [hσ, hb, abs_of_neg (not_le.mp hb)]
    have hσmem : ∀ i, σ i ∈ Set.Icc (-1 : ℝ) 1 := by
      intro i
      by_cases hb : 0 ≤ basisCM x i t₀ <;> simp [hσ, hb, Set.mem_Icc]
    set h : C(X, ℝ) := ∑ i, σ i • basisCM x i with hh
    have hnode : ∀ j, h (x j) = σ j := fun j => by
      rw [hh]
      exact sum_smul_basisCM_apply_node hx σ j
    have hclosed : IsClosed (Set.range x) := (Set.finite_range x).isClosed
    have hrange : ∀ u : (Set.range x : Set X),
        (h.restrict (Set.range x)) u ∈ Set.Icc (-1 : ℝ) 1 := by
      rintro ⟨-, i, rfl⟩
      rw [ContinuousMap.restrict_apply, hnode i]
      exact hσmem i
    obtain ⟨f, hfmem, hfeq⟩ := ContinuousMap.exists_restrict_eq_forall_mem_of_closed
      (h.restrict (Set.range x)) hrange ⟨0, by norm_num⟩ hclosed
    have hfnode : ∀ j, f (x j) = σ j := by
      intro j
      have hcongr := congrArg (fun g : C((Set.range x : Set X), ℝ) => g ⟨x j, ⟨j, rfl⟩⟩) hfeq
      simp only [ContinuousMap.restrict_apply] at hcongr
      rw [hcongr, hnode j]
    have hfnorm : ‖f‖ ≤ 1 := by
      rw [ContinuousMap.norm_le _ zero_le_one]
      intro u
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨(hfmem u).1, (hfmem u).2⟩
    have hval : interpolateCLM x f t₀ = M := by
      rw [interpolateCLM_apply, hM]
      exact Finset.sum_congr rfl fun i _ => by rw [hfnode i, hσmul i]
    calc M = |interpolateCLM x f t₀| := by rw [hval, abs_of_nonneg hMnn]
      _ ≤ ‖interpolateCLM x f‖ := by
          have hb := (interpolateCLM x f).norm_coe_le_norm t₀
          rwa [Real.norm_eq_abs] at hb
      _ ≤ ‖interpolateCLM x‖ * ‖f‖ := (interpolateCLM x).le_opNorm f
      _ ≤ ‖interpolateCLM x‖ * 1 := mul_le_mul_of_nonneg_left hfnorm (norm_nonneg _)
      _ = ‖interpolateCLM x‖ := mul_one _
  exact ⟨⟨t₀, (le_antisymm hle hge).symm⟩, by rintro _ ⟨t, rfl⟩; exact (hmax' t).trans hge⟩

/-- The operator norm of the interpolation operator is the supremum of the Lebesgue function. -/
theorem norm_interpolateCLM [Nonempty X] {x : Fin (n + 1) → X} (hx : Function.Injective x) :
    ‖interpolateCLM x‖ = sSup (Set.range fun t : X => ∑ i, |basisCM x i t|) :=
  (isGreatest_norm_interpolateCLM hx).csSup_eq.symm

end Lagrange

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

/-- **Piecewise-linear interpolation** on the partition `a = x 0 < x 1 < ⋯ < x (n + 1) = b` of
`[a, b]`: the bounded operator on `C([a, b], ℝ)` sending `f` to the continuous function that
agrees with `f` at every node and is affine on every subinterval.

The operator is written as the value at the first node plus the ramps of the subintervals scaled
by the divided differences of `f`, which makes linearity, boundedness and continuity immediate;
`piecewiseLinearInterpCLM_apply_of_mem` is the equivalent local description on one subinterval.
The nodes are given as a sequence, of which only `x 0, …, x (n + 1)` are used, so that the index
arithmetic of the subintervals stays in `ℕ`.

Reference: Atkinson–Han, *Theoretical Numerical Analysis*, §3.2.3 and Exercise 3.6.6; Kress,
*Numerical Analysis*, §8.3. -/
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
private theorem exists_mem_subinterval (hfirst : (x 0 : ℝ) = a) (hlast : (x (n + 1) : ℝ) = b)
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

/-- **The local description of the piecewise-linear interpolant.** On the subinterval
`[x j, x (j + 1)]` it is the affine function through `(x j, f (x j))` and
`(x (j + 1), f (x (j + 1)))`. -/
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

/-- The piecewise-linear interpolant never exceeds the function in sup norm: on each subinterval
its value is a convex combination of two values of the function. -/
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

Reference: Atkinson–Han, *Theoretical Numerical Analysis*, Exercise 3.6.6. -/
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

/-- **The error of piecewise-linear interpolation.** On a partition of `[a, b]` of mesh at most
`h`, the piecewise-linear interpolant of a `C²` function differs from it by at most
`h² ‖f''‖ / 8`.

The function is given as a `C²` map `ℝ → ℝ` agreeing with `f` on `[a, b]`, since `C(Icc a b, ℝ)`
carries no derivative; only the values of the second derivative on `[a, b]` are used.

The route is `piecewiseLinearInterpCLM_apply_of_mem`: on `[x j, x (j+1)]` the interpolant is the
affine function through the two node values, hence the Lagrange interpolant at those two nodes, so
`Lagrange.exists_sub_interpolate_eq` at `n = 1` applies on the subinterval, and
`|(t - u)(t - v)| ≤ (v - u)²/4` finishes it.

Reference: Atkinson–Han, *Theoretical Numerical Analysis*, (3.2.9); Kress, *Numerical Analysis*,
§8.3. -/
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

end PiecewiseLinear

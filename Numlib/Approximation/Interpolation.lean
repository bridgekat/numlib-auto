import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Topology.TietzeExtension
import Numlib.Approximation.Chebyshev

/-!
# Polynomial interpolation and its error

Lagrange interpolation at `n + 1` distinct nodes, with the classical error formula
`f(t) - p(t) = f^{(n+1)}(ξ)/(n+1)! ∏ (t - x_i)`.

The route is the generalized Rolle theorem
`exists_iteratedDeriv_eq_zero_of_forall_eq_zero`: a `C^{n+1}` function vanishing at `n + 2`
points of `[a, b]` has a zero of its `(n+1)`-st derivative strictly inside `[a, b]`. Applied to
`s ↦ f s - p s - c ∏ (s - x_i)` with `c` chosen to make the value at `t` vanish, it gives
`Lagrange.exists_sub_interpolate_eq`.

## References

[^atkinson-han]: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
  Analysis Framework*, 3rd edition, Springer, 2009. (§3.2, (3.2.6).)
[^kress]: Rainer Kress, *Numerical Analysis*, Graduate Texts in Mathematics 181, Springer, 1998.
  (§8.1, Theorem 8.4.)
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

Reference: Rainer Kress, *Numerical Analysis*, Graduate Texts in Mathematics 181, Springer, 1998,
§8.1. -/
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

Reference: Rainer Kress, *Numerical Analysis*, Graduate Texts in Mathematics 181, Springer, 1998,
Theorem 8.4; Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §3.2. -/
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

Reference: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, Example 3.6.5. -/
noncomputable def interpolateCLM (x : Fin (n + 1) → X) : C(X, ℝ) →L[ℝ] C(X, ℝ) :=
  ∑ i, (ContinuousMap.evalCLM (R := ℝ) (x i)).smulRight (basisCM x i)

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

Reference: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §3.7.3. -/
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

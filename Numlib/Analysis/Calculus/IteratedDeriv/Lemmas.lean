/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas`, whose name this module mirrors.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Iterated derivatives: polynomials, conjugation, open sets and compositions

One-variable facts about `iteratedDeriv` that Mathlib lacks, for functions on a nontrivially
normed field `𝕜`.

## Main results

* `Polynomial.iteratedDeriv_eval`: the iterated derivative of a polynomial function is the
  function of the iterated `Polynomial.derivative`.
* `iteratedDeriv_conj_conj`: the iterated derivatives of `conj ∘ f ∘ conj` are
  `conj ∘ f⁽ʲ⁾ ∘ conj`.
* `ContDiffOn.hasDerivAt_iteratedDeriv_of_isOpen`,
  `ContDiffOn.continuousOn_iteratedDeriv_of_isOpen`: on an open set where `f` is `C^N`, the
  iterated derivatives are the successive derivatives, and the last one is continuous.
* `contDiffOn_of_hasDerivAt_chain`: conversely, a chain of functions on an open set, each the
  derivative of the previous one and the last continuous, is the chain of iterated derivatives
  of a `C^n` function.
* `iteratedDeriv_comp_congr`: the jets of a composition depend only on the jets of the factors
  (the formal content of Faà di Bruno's formula).
-/

open Polynomial

section Polynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The iterated derivative of a polynomial function is the function of the iterated
`derivative`. -/
theorem Polynomial.iteratedDeriv_eval (p : 𝕜[X]) (n : ℕ) :
    iteratedDeriv n (fun x => p.eval x) = fun x => (derivative^[n] p).eval x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
    ext x
    exact Polynomial.deriv _

end Polynomial

section Conj

open ComplexConjugate

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [StarRing 𝕜] [NormedStarGroup 𝕜]

/-- The iterated derivatives of `conj ∘ f ∘ conj` are `conj ∘ f⁽ʲ⁾ ∘ conj`, junk values
included. -/
theorem iteratedDeriv_conj_conj (f : 𝕜 → 𝕜) (j : ℕ) :
    iteratedDeriv j (conj ∘ f ∘ conj) = conj ∘ iteratedDeriv j f ∘ conj := by
  induction j with
  | zero => simp
  | succ j ih => rw [iteratedDeriv_succ, ih, deriv_conj_conj, iteratedDeriv_succ]

end Conj

section OpenSet

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] {f : 𝕜 → F} {U : Set 𝕜}

/-- On an open set where `f` is `C^N`, the `j`-th derivative (`j < N`) is differentiable with the
`(j + 1)`-st derivative as its derivative. -/
theorem ContDiffOn.hasDerivAt_iteratedDeriv_of_isOpen (hU : IsOpen U) {N : ℕ}
    (hf : ContDiffOn 𝕜 N f U) {j : ℕ} (hj : j < N) {b : 𝕜} (hb : b ∈ U) :
    HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f b) b := by
  have hd : DifferentiableOn 𝕜 (iteratedDerivWithin j f U) U :=
    hf.differentiableOn_iteratedDerivWithin (by exact_mod_cast hj) hU.uniqueDiffOn
  have hd' : DifferentiableOn 𝕜 (iteratedDeriv j f) U :=
    hd.congr (iteratedDerivWithin_of_isOpen hU).symm
  rw [iteratedDeriv_succ]
  exact (hd'.differentiableAt (hU.mem_nhds hb)).hasDerivAt

/-- On an open set where `f` is `C^N`, the `j`-th derivative (`j ≤ N`) is continuous. -/
theorem ContDiffOn.continuousOn_iteratedDeriv_of_isOpen (hU : IsOpen U) {N : ℕ}
    (hf : ContDiffOn 𝕜 N f U) {j : ℕ} (hj : j ≤ N) : ContinuousOn (iteratedDeriv j f) U :=
  (hf.continuousOn_iteratedDerivWithin (by exact_mod_cast hj) hU.uniqueDiffOn).congr
    (iteratedDerivWithin_of_isOpen hU).symm

/-- A chain `G 0, G 1, …, G n` of functions on an open set, each the derivative of the previous
one and the last continuous, makes `G 0` a `C^n` function whose iterated derivatives are the
`G k`. -/
theorem contDiffOn_of_hasDerivAt_chain {G : ℕ → 𝕜 → F} (hU : IsOpen U) {n : ℕ}
    (hd : ∀ k < n, ∀ b ∈ U, HasDerivAt (G k) (G (k + 1) b) b) (hc : ContinuousOn (G n) U) :
    ContDiffOn 𝕜 n (G 0) U ∧ ∀ k ≤ n, Set.EqOn (iteratedDeriv k (G 0)) (G k) U := by
  induction n generalizing G with
  | zero =>
    refine ⟨contDiffOn_zero.2 hc, fun k hk => ?_⟩
    obtain rfl : k = 0 := Nat.le_zero.1 hk
    simp [Set.EqOn]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih (G := fun k => G (k + 1))
      (fun k hk b hb => hd (k + 1) (by omega) b hb) hc
    have hderiv : Set.EqOn (deriv (G 0)) (G 1) U := fun b hb => (hd 0 (by omega) b hb).deriv
    refine ⟨?_, fun k hk => ?_⟩
    · rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen hU]
      refine ⟨fun b hb => (hd 0 (by omega) b hb).differentiableAt.differentiableWithinAt, ?_,
        h1.congr hderiv⟩
      simp
    · cases k with
      | zero => simp [Set.EqOn]
      | succ k =>
        intro b hb
        rw [iteratedDeriv_succ', ← iteratedDerivWithin_of_isOpen hU hb,
          iteratedDerivWithin_congr hderiv hb, iteratedDerivWithin_of_isOpen hU hb]
        exact h2 k (by omega) hb

end OpenSet

section Composition

/-- The Faà di Bruno composition of two Taylor series at order `n` reads only the terms of order
`≤ n`. -/
private theorem taylorComp_congr {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {q q' p p' : FormalMultilinearSeries 𝕜 𝕜 𝕜} {n : ℕ} (hq : ∀ k ≤ n, q k = q' k)
    (hp : ∀ k ≤ n, p k = p' k) : q.taylorComp p n = q'.taylorComp p' n := by
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [FormalMultilinearSeries.compAlongOrderedFinpartition]
  rw [hq _ c.length_le]
  congr 1
  funext m
  exact hp _ (c.partSize_le m)

/-- **The jets of a composition depend only on the jets of the factors**: if `f, f'` agree with
their derivatives to order `n` at `x`, and `g, g'` agree to order `n` at `f x`, then
`(g ∘ f)⁽ⁿ⁾(x) = (g' ∘ f')⁽ⁿ⁾(x)` (all four `Cⁿ` there). The formal content of Faà di Bruno's
formula (`iteratedFDeriv_comp`). -/
theorem iteratedDeriv_comp_congr {𝕜 : Type*} [NontriviallyNormedField 𝕜] {f f' g g' : 𝕜 → 𝕜}
    {x : 𝕜} {n : ℕ} (hf : ContDiffAt 𝕜 n f x) (hf' : ContDiffAt 𝕜 n f' x)
    (hg : ContDiffAt 𝕜 n g (f x)) (hg' : ContDiffAt 𝕜 n g' (f x))
    (hff : ∀ k ≤ n, iteratedDeriv k f x = iteratedDeriv k f' x)
    (hgg : ∀ k ≤ n, iteratedDeriv k g (f x) = iteratedDeriv k g' (f x)) :
    iteratedDeriv n (g ∘ f) x = iteratedDeriv n (g' ∘ f') x := by
  have hx : f x = f' x := by simpa using hff 0 (Nat.zero_le n)
  rw [hx] at hg'
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv,
    iteratedFDeriv_comp hg hf le_rfl, iteratedFDeriv_comp hg' hf' le_rfl]
  congr 1
  refine taylorComp_congr (fun k hk => ?_) (fun k hk => ?_)
  · ext
    simp only [ftaylorSeries, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
    rw [hgg k hk, hx]
  · ext
    simp only [ftaylorSeries, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
    rw [hff k hk]

end Composition

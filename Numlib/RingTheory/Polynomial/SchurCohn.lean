import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Basic

/-!
# The Schur–Cohn test: roots of a real polynomial inside the unit disc

A real polynomial is **Schur stable** when all of its complex roots have modulus `< 1`
(`Polynomial.IsSchurStable`). This is the condition on the first characteristic polynomial of a
linear multistep method that makes every solution of the associated difference equation bounded,
and it is decided by the classical *Schur–Cohn* (Jury) recursion: writing `P^♯` for the
coefficient-reversed polynomial `reflect n P`, the polynomial

`Q = (a_n P - a_0 P^♯) / X`,  `a_n = P.coeff n`, `a_0 = P.coeff 0`,

has degree one less than `P`, and — provided `|a_0| < |a_n|` — `P` is Schur stable as soon as `Q`
is. Iterating down to a nonzero constant decides Schur stability by rational arithmetic alone.

## The invariant

The recursion is proved here without Rouché's theorem or the argument principle, neither of which
Mathlib has, by carrying a *stronger* invariant down the chain:

`Polynomial.IsSchurCohnPair P Ps` — for every `z` with `‖z‖ ≥ 1`, `P(z) ≠ 0` and
`‖Ps(z)‖ ≤ ‖P(z)‖`,

where `Ps` is the companion `P^♯`. The two identities

`c · X · Q = A · P - B · Ps`  and  `c · Qs = A · Ps - B · P`  (`A = a_n`, `B = a_0`)

— the second obtained from the first by reflecting, `IsSchurCohnPair.reflect_step` — give
`c (A z Q + B Qs) = (A² - B²) P` and `c (B z Q + A Qs) = (A² - B²) Ps`, and then

* `‖A z Q(z) + B Qs(z)‖ ≥ (|A| - |B|) ‖Q(z)‖ > 0`, so `P(z) ≠ 0`;
* the cross terms of `‖A u + B v‖² - ‖B u + A v‖² = (A² - B²)(‖u‖² - ‖v‖²)` cancel exactly, so
  with `u = z Q(z)`, `v = Qs(z)` and `‖z‖ ≥ 1` one gets `‖Ps(z)‖ ≤ ‖P(z)‖`.

The base of the recursion is a nonzero constant, where the invariant is trivial. `IsSchurCohnPair`
is stated for an *arbitrary* companion `Ps` rather than for `reflect n P`, so that a concrete chain
is checked by two polynomial identities per step (`ring`) and one numerical inequality
(`norm_num`), with no `natDegree` bookkeeping; `IsSchurCohnPair.reflect_step` is the classical
statement, in which the companion is the reflection and the second identity is automatic.

Only the sufficiency half of the Schur–Cohn criterion is proved: it is what decides a concrete
polynomial. The converse (Schur stability forces `|a_0| < |a_n|` and passes to `Q`) is not needed
here.

The recursion itself is the classical criterion of Schur (1918) and Cohn (1922), tabulated by Jury;
the consumer in this library is the root condition of [quarteroni2000numerical] §11.6.3, where the
zero-stability of the backward differentiation formulae is exactly Schur stability of the spurious
factor of `ρ`. Upstreaming candidate (natural home: `Mathlib.Analysis.Polynomial`).
-/

open Polynomial

namespace Polynomial

/-- **Schur stability**: every complex root of the real polynomial `P` has modulus `< 1`. For the
first characteristic polynomial of a difference equation this is the condition that makes every
solution tend to zero ([quarteroni2000numerical] §11.6.3). -/
def IsSchurStable (P : ℝ[X]) : Prop := ∀ z : ℂ, aeval z P = 0 → ‖z‖ < 1

/-- **The Schur–Cohn invariant** carried down the recursion: outside the open unit disc `P` does
not vanish and its companion `Ps` — in the intended use the coefficient reversal `reflect n P`, see
`IsSchurCohnPair.reflect_step` — is no larger in modulus. -/
def IsSchurCohnPair (P Ps : ℝ[X]) : Prop :=
  ∀ z : ℂ, 1 ≤ ‖z‖ → aeval z P ≠ 0 ∧ ‖aeval z Ps‖ ≤ ‖aeval z P‖

variable {P Ps Q Qs : ℝ[X]}

/-- The invariant contains Schur stability: a polynomial that does not vanish outside the open
unit disc has all its roots inside it. -/
theorem IsSchurCohnPair.isSchurStable (h : IsSchurCohnPair P Ps) : IsSchurStable P := by
  refine fun z hz => ?_
  by_contra hlt
  exact (h z (not_lt.1 hlt)).1 hz

/-- A Schur stable polynomial does not vanish outside the open unit disc. -/
theorem IsSchurStable.aeval_ne_zero (h : IsSchurStable P) {z : ℂ} (hz : 1 ≤ ‖z‖) :
    aeval z P ≠ 0 := fun h0 => absurd (h z h0) (not_lt.2 hz)

/-- A Schur stable polynomial is nonzero. -/
theorem IsSchurStable.ne_zero (h : IsSchurStable P) : P ≠ 0 := by
  intro h0
  exact h.aeval_ne_zero (z := 1) (by simp) (by simp [h0])

/-- **The base of the Schur–Cohn recursion**: a nonzero constant, whose companion is itself. -/
theorem isSchurCohnPair_C {c : ℝ} (hc : c ≠ 0) : IsSchurCohnPair (C c) (C c) := by
  refine fun z _ => ?_
  refine ⟨?_, le_rfl⟩
  simpa using hc

/-- The cross terms cancel: for real `A`, `B` and complex `u`, `v`,
`‖A u + B v‖² - ‖B u + A v‖² = (A² - B²)(‖u‖² - ‖v‖²)`. -/
private theorem normSq_add_sub_normSq_add_swap (A B : ℝ) (u v : ℂ) :
    Complex.normSq ((A : ℂ) * u + (B : ℂ) * v) - Complex.normSq ((B : ℂ) * u + (A : ℂ) * v) =
      (A ^ 2 - B ^ 2) * (Complex.normSq u - Complex.normSq v) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **One step of the Schur–Cohn recursion.** If `|B| < |A|`, `c ≠ 0` and the two identities
`c X Q = A P - B Ps`, `c Qs = A Ps - B P` hold, then the invariant passes from the pair `(Q, Qs)`
to the pair `(P, Ps)`. In the intended use `A = P.coeff n`, `B = P.coeff 0`, `Ps = reflect n P`,
`Qs = reflect (n - 1) Q` and `c` is any nonzero factor scaled out of `Q`; see
`IsSchurCohnPair.reflect_step`. -/
theorem IsSchurCohnPair.step {A B c : ℝ} (hc : c ≠ 0) (hAB : |B| < |A|)
    (h1 : C c * (X * Q) = C A * P - C B * Ps)
    (h2 : C c * Qs = C A * Ps - C B * P)
    (h : IsSchurCohnPair Q Qs) : IsSchurCohnPair P Ps := by
  refine fun z hz => ?_
  obtain ⟨hq, hqs⟩ := h z hz
  have hD : 0 < A ^ 2 - B ^ 2 := by nlinarith [sq_abs A, sq_abs B, abs_nonneg B]
  have e1 : (c : ℂ) * (z * aeval z Q) = (A : ℂ) * aeval z P - (B : ℂ) * aeval z Ps := by
    have := congrArg (aeval z) h1
    simpa using this
  have e2 : (c : ℂ) * aeval z Qs = (A : ℂ) * aeval z Ps - (B : ℂ) * aeval z P := by
    have := congrArg (aeval z) h2
    simpa using this
  set p := aeval z P with hpdef
  set ps := aeval z Ps with hpsdef
  set q := aeval z Q with hqdef
  set qs := aeval z Qs with hqsdef
  set S : ℂ := (A : ℂ) * (z * q) + (B : ℂ) * qs with hSdef
  set T : ℂ := (B : ℂ) * (z * q) + (A : ℂ) * qs with hTdef
  have hS : (c : ℂ) * S = ((A ^ 2 - B ^ 2 : ℝ) : ℂ) * p := by
    rw [hSdef]; push_cast; linear_combination (A : ℂ) * e1 + (B : ℂ) * e2
  have hT : (c : ℂ) * T = ((A ^ 2 - B ^ 2 : ℝ) : ℂ) * ps := by
    rw [hTdef]; push_cast; linear_combination (B : ℂ) * e1 + (A : ℂ) * e2
  have hqpos : 0 < ‖q‖ := norm_pos_iff.2 hq
  have hzq : ‖q‖ ≤ ‖z * q‖ := by
    rw [norm_mul]; nlinarith
  have hlt : ‖(B : ℂ) * qs‖ < ‖(A : ℂ) * (z * q)‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    calc |B| * ‖qs‖ ≤ |B| * ‖q‖ := by gcongr
      _ < |A| * ‖q‖ := mul_lt_mul_of_pos_right hAB hqpos
      _ ≤ |A| * ‖z * q‖ := by gcongr
  have hSne : S ≠ 0 := by
    intro h0
    have he : (A : ℂ) * (z * q) = -((B : ℂ) * qs) := by
      rw [hSdef] at h0; linear_combination h0
    rw [he, norm_neg] at hlt
    exact lt_irrefl _ hlt
  refine ⟨?_, ?_⟩
  · intro h0
    rw [h0, mul_zero] at hS
    exact (mul_ne_zero (by exact_mod_cast hc) hSne) hS
  · have hkey := normSq_add_sub_normSq_add_swap A B (z * q) qs
    rw [← hSdef, ← hTdef] at hkey
    have hns : Complex.normSq qs ≤ Complex.normSq (z * q) := by
      rw [← Complex.sq_norm, ← Complex.sq_norm]
      have : ‖qs‖ ≤ ‖z * q‖ := hqs.trans hzq
      nlinarith [norm_nonneg qs, norm_nonneg (z * q)]
    have hTS : Complex.normSq T ≤ Complex.normSq S := by nlinarith
    have hnTS : ‖T‖ ≤ ‖S‖ := by
      rw [← Complex.sq_norm, ← Complex.sq_norm] at hTS
      nlinarith [norm_nonneg T, norm_nonneg S]
    have hnS := congrArg norm hS
    have hnT := congrArg norm hT
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hD] at hnS hnT
    nlinarith [abs_nonneg c, norm_nonneg S, norm_nonneg T]

/-- **One step of the Schur–Cohn recursion, in its classical form.** For `P` of formal degree
`m + 1` with `|P.coeff 0| < |P.coeff (m + 1)|`, if the reduced polynomial `Q` of degree at most `m`
satisfies `c X Q = P.coeff (m+1) · P - P.coeff 0 · reflect (m+1) P` for some `c ≠ 0`, then the
invariant for `Q` with companion `reflect m Q` gives it for `P` with companion `reflect (m+1) P`.
The second identity of `IsSchurCohnPair.step` is the reflection of the first, using
`reflect (m+1) (X * Q) = reflect m Q` and the involutivity of `reflect`. -/
theorem IsSchurCohnPair.reflect_step {m : ℕ} {c : ℝ} (hc : c ≠ 0) (hQ : Q.natDegree ≤ m)
    (hAB : |P.coeff 0| < |P.coeff (m + 1)|)
    (h1 : C c * (X * Q) = C (P.coeff (m + 1)) * P - C (P.coeff 0) * P.reflect (m + 1))
    (h : IsSchurCohnPair Q (Q.reflect m)) : IsSchurCohnPair P (P.reflect (m + 1)) := by
  refine h.step hc hAB h1 ?_
  have hXQ : reflect (m + 1) (X * Q) = reflect m Q := by
    rw [show m + 1 = 1 + m from Nat.add_comm _ _, reflect_mul _ _ natDegree_X_le hQ,
      reflect_one_X, one_mul]
  have h2 := congrArg (reflect (m + 1)) h1
  rwa [reflect_C_mul, hXQ, reflect_sub, reflect_C_mul, reflect_C_mul, reflect_reflect] at h2

end Polynomial

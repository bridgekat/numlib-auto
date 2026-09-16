import NumlibSurface.QuarteroniSaccoSaleri.Chapter06.Section02

/-!
# Quarteroni–Sacco–Saleri §6.3: fixed-point iterations for nonlinear equations

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §6.3: the fixed-point iteration `x^{(k+1)} = φ(x^{(k)})` — which is
`φ^[k] x₀` and needs no definition — with Theorem 6.1 and its limit (6.18), the asymptotic
convergence rate (6.20), Ostrowski's Property 6.3, Remark 6.2, Example 6.6 and Property 6.4, and
§6.3.1's application to the chord and Newton methods of `Section02`, including the multiple-root
formula (6.22), the modified Newton method (6.23) and Exercise 6.2. The backbone is
`Numlib/Nonlinear/{FixedPoint, Order, ScalarNewton}`.

## Readings

* Theorem 6.1's `φ ∈ C¹[a, b]` is carried for fidelity; the backbone needs only the derivative
  bound within the interval. Every error-ratio limit ((6.18), (6.21), (6.22)) needs the orbit to
  avoid the fixed point, which the book never says: a term equal to `α` makes the quotient `0/0`.
* (6.20) prints `R = -log(1 / |φ'(α)|)`, which is `≤ 0` for a convergent method; by analogy with
  (4.5) the intended rate is `R = -log|φ'(α)|` (`notes/book-errata.md`).
* Property 6.4's range `0 ≤ i ≤ p` must read `1 ≤ i ≤ p`, and the property presupposes
  convergence: for `p = 0` only the limit (6.21) holds, for `p ≥ 1` the order `p + 1` follows.
* Newton's order 2 and its constant `f''(α) / (2 f'(α))` are proved under `f ∈ C²`, where reading
  them off `φ''_Newt(α) = f''(α) / f'(α)` through Property 6.4 would need `C³`.
-/

open Filter Set Topology

namespace QuarteroniSaccoSaleri.Chapter06

/-! ### Theorem 6.1 and its consequences -/

section Theorem61

variable {φ φ' : ℝ → ℝ} {a b : ℝ}

-- `φ ∈ C¹[a, b]` (the continuity `hφ'` of the derivative) is the book's hypothesis 2; the proof
-- uses only the derivative bound within the interval
-- (`exists_unique_fixedPoint_Icc_of_abs_deriv_le`).
set_option linter.unusedVariables false in
/-- **Theorem 6.1 (convergence of fixed-point iterations).** Let `φ : [a, b] → [a, b]` be `C¹`
with `|φ'(x)| ≤ K < 1` on `[a, b]`. Then `φ` has a unique fixed point `α ∈ [a, b]`, and the
sequence `x^{(k+1)} = φ(x^{(k)})` converges to `α` for any `x^{(0)} ∈ [a, b]`.
`exists_unique_fixedPoint_Icc_of_abs_deriv_le` and `tendsto_iterate_Icc_of_abs_deriv_le`. -/
theorem theorem_6_1 (hab : a ≤ b) (hmaps : MapsTo φ (Icc a b) (Icc a b))
    (hφ : ∀ x ∈ Icc a b, HasDerivWithinAt φ (φ' x) (Icc a b) x) (hφ' : ContinuousOn φ' (Icc a b))
    (hK : ∃ K < 1, ∀ x ∈ Icc a b, |φ' x| ≤ K) :
    (∃! α, α ∈ Icc a b ∧ φ α = α) ∧
      ∀ α, α ∈ Icc a b → φ α = α → ∀ x₀ ∈ Icc a b, Tendsto (fun k => φ^[k] x₀) atTop (𝓝 α) := by
  obtain ⟨K, hK1, hK⟩ := hK
  exact ⟨exists_unique_fixedPoint_Icc_of_abs_deriv_le hab hmaps hφ hK hK1,
    fun α hα hfix x₀ hx₀ => tendsto_iterate_Icc_of_abs_deriv_le hmaps hφ hK hK1 hα hfix hx₀⟩

/-- **Theorem 6.1, the limit (6.18).** Under the hypotheses of `theorem_6_1`, for the fixed point
`α` and every `x^{(0)} ∈ [a, b]` whose orbit never equals `α`,
`(x^{(k+1)} - α) / (x^{(k)} - α) → φ'(α)`. The book omits the "never equals `α`" clause, without
which the quotient is `0/0` from some index on; at an endpoint `α ∈ {a, b}` the orbit approaches
`α` from inside `[a, b]`, and the one-sided derivative is what is used. -/
theorem theorem_6_1_limit (hab : a ≤ b) (hmaps : MapsTo φ (Icc a b) (Icc a b))
    (hφ : ∀ x ∈ Icc a b, HasDerivWithinAt φ (φ' x) (Icc a b) x) (hφ' : ContinuousOn φ' (Icc a b))
    (hK : ∃ K < 1, ∀ x ∈ Icc a b, |φ' x| ≤ K) {α : ℝ} (hα : α ∈ Icc a b) (hfix : φ α = α)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Icc a b) (hne : ∀ k, φ^[k] x₀ ≠ α) :
    Tendsto (fun k => (φ^[k + 1] x₀ - α) / (φ^[k] x₀ - α)) atTop (𝓝 (φ' α)) :=
  tendsto_sub_div_sub_of_hasDerivWithinAt (hφ α hα) hfix
    (fun k => Function.iterate_succ_apply' φ k x₀) (fun k => hmaps.iterate k hx₀) hne
    ((theorem_6_1 hab hmaps hφ hφ' hK).2 α hα hfix x₀ hx₀)

/-- **(6.20), the asymptotic convergence rate** `R = -log|φ'(α)|`, with `|φ'(α)|` the asymptotic
convergence factor of the fixed-point method. The book prints `R = -log(1 / |φ'(α)|)`, which is
`≤ 0` for a convergent method; the intended quantity, by analogy with (4.5) `R(B) = -log ρ(B)`,
is `-log|φ'(α)|`. -/
noncomputable def equation_6_20 (φ' : ℝ → ℝ) (α : ℝ) : ℝ := -Real.log |φ' α|

end Theorem61

section Ostrowski

variable {φ : ℝ → ℝ} {α : ℝ}

/-- **Property 6.3 (Ostrowski's theorem).** Let `α` be a fixed point of `φ`, continuous and
differentiable in a neighbourhood of `α`. If `|φ'(α)| < 1` then there is `δ > 0` such that
`x^{(k)} → α` for every `x^{(0)}` with `|x^{(0)} - α| < δ`. `tendsto_iterate_of_abs_deriv_lt_one`,
which needs only differentiability at `α`. -/
theorem property_6_3 (hα : φ α = α) (hJ : ∀ᶠ x in 𝓝 α, DifferentiableAt ℝ φ x)
    (h : |deriv φ α| < 1) :
    ∃ δ > 0, ∀ x₀, |x₀ - α| < δ → Tendsto (fun k => φ^[k] x₀) atTop (𝓝 α) :=
  tendsto_iterate_of_abs_deriv_lt_one hα hJ.self_of_nhds.hasDerivAt h

/-- **Remark 6.2.** If `|φ'(α)| > 1` then no orbit `x^{(k+1)} = φ(x^{(k)})` that never lands on the
fixed point `α` can converge to it: near `α` the error grows at every step. The case
`|φ'(α)| = 1` is undecided (Example 6.6). `not_tendsto_iterate_of_one_lt_abs_deriv`. -/
theorem remark_6_2 (hα : φ α = α) (hφ : DifferentiableAt ℝ φ α) (h : 1 < |deriv φ α|) {x₀ : ℝ}
    (hne : ∀ k, φ^[k] x₀ ≠ α) : ¬ Tendsto (fun k => φ^[k] x₀) atTop (𝓝 α) :=
  not_tendsto_iterate_of_one_lt_abs_deriv hα hφ.hasDerivAt h
    (fun k => Function.iterate_succ_apply' φ k x₀) hne

end Ostrowski

/-! ### Example 6.6: `x - x³` and `x + x³` at the fixed point `0`, where `φ'(0) = 1` -/

section Example66

/-- The step `y ↦ y - y³` on `[0, 1]` stays in `[0, 1]` and does not increase. -/
private theorem sub_cube_mem_Icc {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) : y - y ^ 3 ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := hy
  constructor <;> nlinarith [pow_le_one₀ h0 h1 (n := 2), pow_nonneg h0 2, pow_nonneg h0 3]

/-- `|x - x³| = |x| - |x|³` for `|x| ≤ 1`. -/
private theorem abs_sub_cube {x : ℝ} (hx : |x| ≤ 1) : |x - x ^ 3| = |x| - |x| ^ 3 := by
  have h3 : |x| ^ 3 = |x ^ 3| := (abs_pow x 3).symm
  have h : x - x ^ 3 = x * (1 - x ^ 2) := by ring
  have hsq : x ^ 2 ≤ 1 := by
    rw [← sq_abs]
    exact pow_le_one₀ (abs_nonneg x) hx
  rw [h, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - x ^ 2)]
  nlinarith [sq_abs x]

/-- **Example 6.6, first half.** For `φ(x) = x - x³`, with the fixed point `α = 0` and
`φ'(0) = 1`, every orbit started in `[-1, 1]` lies in `(-1, 1)` from the first step on and
converges (very slowly) to `0`; for `x^{(0)} = ±1` the orbit is `0` from the first step on.
The absolute values `y_k = |x^{(k)}|` satisfy `y_{k+1} = y_k - y_k³ ∈ [0, 1]`, decrease to a limit
`L` with `L = L - L³`, hence `L = 0`. -/
theorem example_6_6_tendsto {x₀ : ℝ} (hx₀ : x₀ ∈ Icc (-1 : ℝ) 1) :
    (∀ k, 1 ≤ k → (fun x : ℝ => x - x ^ 3)^[k] x₀ ∈ Ioo (-1 : ℝ) 1) ∧
      Tendsto (fun k => (fun x : ℝ => x - x ^ 3)^[k] x₀) atTop (𝓝 0) := by
  set φ : ℝ → ℝ := fun x => x - x ^ 3 with hφ
  set y : ℕ → ℝ := fun k => |φ^[k] x₀| with hy
  have hx₀' : |x₀| ≤ 1 := abs_le.2 hx₀
  -- the recursion of the absolute values
  have hy_mem : ∀ k, y k ∈ Icc (0 : ℝ) 1 := by
    intro k
    induction k with
    | zero => exact ⟨abs_nonneg _, hx₀'⟩
    | succ k ih =>
      have : y (k + 1) = y k - y k ^ 3 := by
        simp only [hy, Function.iterate_succ_apply', hφ]
        exact abs_sub_cube ih.2
      rw [this]
      exact sub_cube_mem_Icc ih
  have hy_succ : ∀ k, y (k + 1) = y k - y k ^ 3 := fun k => by
    simp only [hy, Function.iterate_succ_apply', hφ]
    exact abs_sub_cube (hy_mem k).2
  have hanti : Antitone y := antitone_nat_of_succ_le fun k => by
    rw [hy_succ]
    have := (hy_mem k).1
    nlinarith [pow_nonneg this 3]
  have hbdd : BddBelow (range y) := ⟨0, by rintro _ ⟨k, rfl⟩; exact (hy_mem k).1⟩
  have hlimL : Tendsto y atTop (𝓝 (⨅ k, y k)) := tendsto_atTop_ciInf hanti hbdd
  set L := ⨅ k, y k with hL
  have hL0 : 0 ≤ L := le_ciInf fun k => (hy_mem k).1
  -- the limit satisfies `L = L - L ^ 3`
  have hL' : Tendsto (fun k => y (k + 1)) atTop (𝓝 (L - L ^ 3)) := by
    have := hlimL.sub (hlimL.pow 3)
    refine this.congr fun k => ?_
    simp [hy_succ]
  have hL'' : Tendsto (fun k => y (k + 1)) atTop (𝓝 L) := hlimL.comp (tendsto_add_atTop_nat 1)
  have hLeq : L = L - L ^ 3 := tendsto_nhds_unique hL'' hL'
  have hLzero : L = 0 := by
    have : L ^ 3 = 0 := by linarith
    exact pow_eq_zero_iff (by norm_num) |>.1 this
  rw [hLzero] at hlimL
  refine ⟨fun k hk => ?_, ?_⟩
  · -- the orbit is in the open interval from the first step on
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have h1 : y (j + 1) < 1 := by
      rw [hy_succ]
      rcases (hy_mem j).1.lt_or_eq with h0 | h0
      · have := (hy_mem j).2
        nlinarith [pow_pos h0 3]
      · rw [← h0]; norm_num
    have := abs_lt.1 h1
    exact ⟨this.1, this.2⟩
  · exact tendsto_iff_norm_sub_tendsto_zero.2 (by simpa [hy] using hlimL)

/-- **Example 6.6, second half.** For `φ(x) = x + x³`, with the fixed point `α = 0` and
`φ'(0) = 1`, no orbit started at `x^{(0)} ≠ 0` converges to `0`: `|x + x³| ≥ |x|`, so
`|x^{(k)}| ≥ |x^{(0)}| > 0` for all `k` (in fact the orbit diverges). -/
theorem example_6_6_not_tendsto {x₀ : ℝ} (hx₀ : x₀ ≠ 0) :
    ¬ Tendsto (fun k => (fun x : ℝ => x + x ^ 3)^[k] x₀) atTop (𝓝 0) := by
  set φ : ℝ → ℝ := fun x => x + x ^ 3 with hφ
  have hgrow : ∀ k, |x₀| ≤ |φ^[k] x₀| := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      refine ih.trans ?_
      rw [Function.iterate_succ_apply', hφ]
      simp only
      set z := φ^[k] x₀
      rw [show z + z ^ 3 = z * (1 + z ^ 2) by ring, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < 1 + z ^ 2)]
      exact le_mul_of_one_le_right (abs_nonneg z) (by nlinarith [sq_nonneg z])
  intro hlim
  have hpos : 0 < |x₀| := abs_pos.2 hx₀
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((tendsto_iff_norm_sub_tendsto_zero.1 hlim).eventually (gt_mem_nhds hpos))
  have := hN N le_rfl
  simp only [sub_zero, Real.norm_eq_abs] at this
  exact absurd (hgrow N) (not_le.2 this)

end Example66

section Property64

variable {φ : ℝ → ℝ} {α : ℝ}

-- `φ^{(p+1)}(α) ≠ 0` is part of the book's statement; it makes the order exactly `p + 1` and is
-- not needed for the order bound or the limit.
set_option linter.unusedVariables false in
/-- **Property 6.4.** Let `φ ∈ C^{p+1}(J)` on a neighbourhood of a fixed point `α`, with
`φ^{(i)}(α) = 0` for `1 ≤ i ≤ p` (the book's `0 ≤ i ≤ p` is a misprint) and
`φ^{(p+1)}(α) ≠ 0`. Then, for `p ≥ 1`, the fixed-point method has order `p + 1`, and along every
orbit converging to `α` without reaching it the limit (6.21) holds:
`(x^{(k+1)} - α) / (x^{(k)} - α)^{p+1} → φ^{(p+1)}(α) / (p + 1)!`. For `p = 0` only the limit
holds, convergence having to be assumed as the proof's first line does.
`hasIterationOrder_of_iteratedDeriv_eq_zero` and `tendsto_sub_div_pow_of_iteratedDeriv_eq_zero`. -/
theorem property_6_4 {p : ℕ} (hφ : ContDiffAt ℝ (p + 1 : ℕ) φ α) (hα : φ α = α)
    (hzero : ∀ i, 1 ≤ i → i ≤ p → iteratedDeriv i φ α = 0) (hp' : iteratedDeriv (p + 1) φ α ≠ 0) :
    (1 ≤ p → ∃ ε > 0, ∀ x₀ ∈ Metric.ball α ε, definition_6_1 (fun k => φ^[k] x₀) α (p + 1)) ∧
      ∀ x₀, (∀ k, φ^[k] x₀ ≠ α) → Tendsto (fun k => φ^[k] x₀) atTop (𝓝 α) →
        Tendsto (fun k => (φ^[k + 1] x₀ - α) / (φ^[k] x₀ - α) ^ (p + 1)) atTop
          (𝓝 (iteratedDeriv (p + 1) φ α / (p + 1).factorial)) := by
  refine ⟨fun hp => ?_, fun x₀ hne hlim => ?_⟩
  · obtain ⟨ε, hε, h⟩ := hasIterationOrder_of_iteratedDeriv_eq_zero hp hφ hα hzero
    refine ⟨ε, hε, fun x₀ hx₀ => definition_6_1_of_convergesWithOrder ?_ ?_⟩
    · have : (1 : ℝ) ≤ p := by exact_mod_cast hp
      linarith
    · have := h x₀ hx₀
      simpa using this
  · exact tendsto_sub_div_pow_of_iteratedDeriv_eq_zero hφ hα hzero
      (fun k => Function.iterate_succ_apply' φ k x₀) hne hlim

end Property64

/-! ### §6.3.1 Convergence results for some fixed-point methods -/

section Chord631

variable {f : ℝ → ℝ} {a b α f' : ℝ}

/-- **The iteration function of the chord method**, `φ_chord(x) = x - (b - a) / (f(b) - f(a)) f(x)`,
whose iteration is `chord f a b`. -/
noncomputable def chordIterationFunction (f : ℝ → ℝ) (a b : ℝ) (x : ℝ) : ℝ :=
  x - (b - a) / (f b - f a) * f x

/-- `φ_chord` is the backbone's `Chord.step` with the slope `q = (f(b) - f(a)) / (b - a)`. -/
theorem chordIterationFunction_eq (f : ℝ → ℝ) (a b : ℝ) :
    chordIterationFunction f a b = Chord.step f ((f b - f a) / (b - a)) := by
  funext x
  simp only [chordIterationFunction, Chord.step, div_div_eq_mul_div]
  ring

/-- The chord method is the fixed-point iteration of `φ_chord`. -/
theorem chord_eq_iterate (f : ℝ → ℝ) (a b x₀ : ℝ) (k : ℕ) :
    chord f a b x₀ k = (chordIterationFunction f a b)^[k] x₀ := by
  rw [chord, chordIterationFunction_eq]

/-- **§6.3.1, the chord method.** With `q = (f(b) - f(a)) / (b - a)` and `f'(α)` the derivative
of `f` at the root, `φ_chord'(α) = 1 - f'(α) / q` — so `φ_chord'(α) = 1` when `f'(α) = 0` — and
`|φ_chord'(α)| < 1` iff `0 < f'(α) / q < 2`, i.e. `q` has the sign of `f'(α)` and
`(b - a) < 2 (f(b) - f(a)) / f'(α)`. `Chord.hasDerivAt_step`, `Chord.abs_one_sub_div_lt_one_iff`.
-/
theorem chordIterationFunction_deriv (hf : HasDerivAt f f' α) :
    HasDerivAt (chordIterationFunction f a b) (1 - f' / ((f b - f a) / (b - a))) α ∧
      (f' = 0 → 1 - f' / ((f b - f a) / (b - a)) = 1) ∧
      (|1 - f' / ((f b - f a) / (b - a))| < 1 ↔
        0 < f' / ((f b - f a) / (b - a)) ∧ f' / ((f b - f a) / (b - a)) < 2) := by
  rw [chordIterationFunction_eq]
  exact ⟨Chord.hasDerivAt_step hf, fun h => by simp [h], Chord.abs_one_sub_div_lt_one_iff⟩

/-- **§6.3.1: the chord method converges linearly** when `0 < f'(α) / q < 2`,
`q = (f(b) - f(a)) / (b - a)`: from every `x^{(0)}` close enough to the root `α` the chord
iterates converge to `α` with order `1` in the sense of Definition 6.1, and along an orbit
avoiding `α` the error ratios tend to `1 - f'(α) / q` — the convergence factor `|1 - f'(α) / q|`,
which is `0` in the "lucky case" `f'(α) = q`. Ostrowski's theorem for `φ_chord`
(`Chord.tendsto_iterate`, `Chord.tendsto_sub_div_sub`). -/
theorem chord_tendsto (hα : f α = 0) (hf : HasDerivAt f f' α)
    (h0 : 0 < f' / ((f b - f a) / (b - a))) (h2 : f' / ((f b - f a) / (b - a)) < 2) :
    ∃ δ > 0, ∀ x₀, |x₀ - α| < δ →
      Tendsto (chord f a b x₀) atTop (𝓝 α) ∧ definition_6_1 (chord f a b x₀) α 1 ∧
        ((∀ k, chord f a b x₀ k ≠ α) →
          Tendsto (fun k => (chord f a b x₀ (k + 1) - α) / (chord f a b x₀ k - α)) atTop
            (𝓝 (1 - f' / ((f b - f a) / (b - a))))) := by
  set q := (f b - f a) / (b - a) with hq
  have hlt : |1 - f' / q| < 1 := Chord.abs_one_sub_div_lt_one_iff.2 ⟨h0, h2⟩
  obtain ⟨c, hc, hc1⟩ := exists_between hlt
  have hc0 : 0 < c := (abs_nonneg _).trans_lt hc
  obtain ⟨δ, hδ, hconv⟩ := Chord.tendsto_iterate hα hf h0 h2
  refine ⟨δ, hδ, fun x₀ hx₀ => ⟨hconv x₀ hx₀, ?_, fun hne => ?_⟩⟩
  · refine definition_6_1_of_convergesWithOrder le_rfl
      (convergesWithOrder_one_of_eventually_norm_sub_succ_le hc0 hc1 ?_)
    have hev := eventually_abs_sub_le_mul_of_hasDerivAt (by simp [Chord.step, hα])
      (Chord.hasDerivAt_step (q := q) hf) hc
    filter_upwards [(hconv x₀ hx₀).eventually hev] with k hk
    simpa [chord, Function.iterate_succ_apply', Real.norm_eq_abs] using hk
  · exact Chord.tendsto_sub_div_sub hα hf (fun k => Function.iterate_succ_apply' _ k x₀) hne
      (hconv x₀ hx₀)

end Chord631

section Newton631

variable {f : ℝ → ℝ} {α : ℝ}

/-- **§6.3.1, Newton's method at a simple root.** For `φ_Newt(x) = x - f(x) / f'(x)` with `f α = 0`,
`f ∈ C²` near `α` and `f'(α) ≠ 0`: `φ_Newt'(α) = 0`; and for `f ∈ C³`,
`φ_Newt''(α) = f''(α) / f'(α)`. `Newton.hasDerivAt_scalarStep`, `Newton.deriv2_scalarStep_root`. -/
theorem newtonIterationFunction_deriv (hα : f α = 0) (hf : ContDiffAt ℝ 2 f α)
    (hf' : deriv f α ≠ 0) :
    HasDerivAt (Newton.scalarStep f (deriv f)) 0 α ∧
      (ContDiffAt ℝ 3 f α →
        iteratedDeriv 2 (Newton.scalarStep f (deriv f)) α = iteratedDeriv 2 f α / deriv f α) := by
  refine ⟨?_, fun hf3 => Newton.deriv2_scalarStep_root hf3 hα hf'⟩
  have h := Newton.hasDerivAt_scalarStep (hf.differentiableAt (by norm_num)).hasDerivAt
    (hasDerivAt_deriv_of_contDiffAt_two hf) hf'
  rwa [hα, zero_mul, zero_div] at h

/-- **Newton's method is of order 2** (§6.2.2, "see Section 6.3.1"): for `f α = 0`, `f ∈ C²`
near `α` and `f'(α) ≠ 0`, from every `x^{(0)}` close enough to `α` the Newton iterates converge
to `α` with order `2`, and along an orbit avoiding `α`,
`(x^{(k+1)} - α) / (x^{(k)} - α)² → f''(α) / (2 f'(α))` — the constant `φ''_Newt(α) / 2!` of
Property 6.4 with `p = 1`, obtained here under `C²` alone.
`Newton.hasIterationOrder_scalarStep_two`, `Newton.tendsto_scalarStep_sub_div_sq`. -/
theorem newton_order_two (hα : f α = 0) (hf : ContDiffAt ℝ 2 f α) (hf' : deriv f α ≠ 0) :
    (∃ ε > 0, ∀ x₀ ∈ Metric.ball α ε, definition_6_1 (newton f (deriv f) x₀) α 2) ∧
      ∀ x₀, (∀ k, newton f (deriv f) x₀ k ≠ α) → Tendsto (newton f (deriv f) x₀) atTop (𝓝 α) →
        Tendsto (fun k => (newton f (deriv f) x₀ (k + 1) - α) / (newton f (deriv f) x₀ k - α) ^ 2)
          atTop (𝓝 (iteratedDeriv 2 f α / (2 * deriv f α))) := by
  refine ⟨?_, fun x₀ hne hlim => ?_⟩
  · obtain ⟨ε, hε, h⟩ := Newton.hasIterationOrder_scalarStep_two hα hf hf'
    exact ⟨ε, hε, fun x₀ hx₀ => definition_6_1_of_convergesWithOrder one_le_two (h x₀ hx₀)⟩
  · have := (Newton.tendsto_scalarStep_sub_div_sq hα hf hf').comp
      (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hne⟩)
    refine this.congr fun k => ?_
    simp [Function.comp, newton, Function.iterate_succ_apply']

/-- **(6.22).** If `α` is a root of `f` of multiplicity `m > 1` (`f ∈ C^{m+1}` near `α`), then
`φ_Newt'(α) = 1 - 1/m` in the sense `(φ_Newt(x) - α) / (x - α) → 1 - 1/m` as `x → α`, `x ≠ α`;
consequently Newton's method is no longer second-order convergent, but converges linearly with
factor `1 - 1/m`. `Newton.tendsto_scalarStep_sub_div_of_isRootOfMultiplicity`,
`Newton.hasIterationOrder_scalarStep_one_of_isRootOfMultiplicity`. -/
theorem equation_6_22 {m : ℕ} (hm : 1 < m) (hf : ContDiffAt ℝ (m + 1 : ℕ) f α)
    (hα : IsRootOfMultiplicity f α m) :
    Tendsto (fun x => (Newton.scalarStep f (deriv f) x - α) / (x - α)) (𝓝[≠] α)
        (𝓝 (1 - 1 / m)) ∧
      ∃ ε > 0, ∀ x₀ ∈ Metric.ball α ε, definition_6_1 (newton f (deriv f) x₀) α 1 := by
  refine ⟨Newton.tendsto_scalarStep_sub_div_of_isRootOfMultiplicity (by omega) hf hα, ?_⟩
  obtain ⟨ε, hε, h⟩ := Newton.hasIterationOrder_scalarStep_one_of_isRootOfMultiplicity hm hf hα
  exact ⟨ε, hε, fun x₀ hx₀ => definition_6_1_of_convergesWithOrder le_rfl (h x₀ hx₀)⟩

/-- **(6.23), the modified Newton method** for a root of known multiplicity `m`:
`x^{(k+1)} = x^{(k)} - m f(x^{(k)}) / f'(x^{(k)})`, the iteration of `Newton.modifiedScalarStep`. -/
noncomputable def equation_6_23 (f f' : ℝ → ℝ) (m : ℕ) (x₀ : ℝ) (k : ℕ) : ℝ :=
  (Newton.modifiedScalarStep f f' m)^[k] x₀

/-- **Exercise 6.2** (cited by §6.3.1 for (6.22) and (6.23)). Let `α` be a root of `f` of
multiplicity `m ≥ 1` (`f ∈ C^{m+1}` near `α`). Then (6.22) holds — the limit `1 - 1/m` of the
Newton error ratios, which is `0` for `m = 1` — and the modified Newton method (6.23) has order
`2`. The hint `f(x) = (x - α)^m h(x)`, `h(α) ≠ 0`, is `IsRootOfMultiplicity.exists_eq_pow_mul`;
`Newton.hasIterationOrder_modifiedScalarStep_two`. -/
theorem exercise_6_2 {m : ℕ} (hm : 1 ≤ m) (hf : ContDiffAt ℝ (m + 1 : ℕ) f α)
    (hα : IsRootOfMultiplicity f α m) :
    Tendsto (fun x => (Newton.scalarStep f (deriv f) x - α) / (x - α)) (𝓝[≠] α)
        (𝓝 (1 - 1 / m)) ∧
      ∃ ε > 0, ∀ x₀ ∈ Metric.ball α ε, definition_6_1 (equation_6_23 f (deriv f) m x₀) α 2 := by
  refine ⟨Newton.tendsto_scalarStep_sub_div_of_isRootOfMultiplicity hm hf hα, ?_⟩
  obtain ⟨ε, hε, h⟩ := Newton.hasIterationOrder_modifiedScalarStep_two hm hf hα
  exact ⟨ε, hε, fun x₀ hx₀ => definition_6_1_of_convergesWithOrder one_le_two (h x₀ hx₀)⟩

end Newton631

end QuarteroniSaccoSaleri.Chapter06

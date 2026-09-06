import Mathlib.Analysis.InnerProductSpace.l2Space
import Numlib.Nonlinear.CompletelyContinuous

/-!
# Atkinson–Han §5.5: completely continuous vector fields

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §5.5.

The section is a summary: Brouwer's theorem (5.5.1), Schauder's theorem (5.5.4), Proposition 5.5.5
and the properties P1–P5 of the rotation of a completely continuous vector field are all quoted
without proof, from Krasnosel'skii, *Topological Methods in the Theory of Nonlinear Integral
Equations*, Krasnosel'skii and Zabreyko, *Geometric Methods of Nonlinear Analysis*, Berger,
*Nonlinearity and Functional Analysis*, and Kantorovich and Akilov, *Functional Analysis in Normed
Spaces*. Mathlib has neither Brouwer's theorem nor degree theory, so the two quoted fixed-point
theorems and the whole of the rotation theory are out; what is formalized is Definition 5.5.3 and
Proposition 5.5.5, which later chapters use, and the counterexample of Example 5.5.2.

## Main definitions

* `IsCompletelyContinuousOn` — Definition 5.5.3: a compact map that is in addition continuous. The
  first half is the backbone `IsCompactMap` (`Numlib/Nonlinear/CompletelyContinuous`); the two
  halves are separate because for a nonlinear map compactness does not imply continuity, unlike
  for a linear one, where the notion is Mathlib's `IsCompactOperator`.
* `prepend`, `prependLp` — the unilateral shift on `ℓ²(ℕ, ℝ)` with a prescribed first coordinate,
  the coordinate form of the map of Example 5.5.2; `shiftMap` transports it to a Hilbert space
  through `HilbertBasis.repr`.

## Main results

* `proposition_5_5_5` — the Fréchet derivative of a completely continuous operator at an interior
  point is a compact linear operator, so the Fredholm alternative applies to `I - T'(v₀)`. This is
  what lets §12.7 linearize a nonlinear fixed point problem into a second-kind linear equation.
* `example_5_5_2` — Example 5.5.2: for `1 < k` and `0 < t ≤ min(1, √(k² - 1))` the map `shiftMap`
  sends the closed unit ball into itself, is `k`-Lipschitz, and has no fixed point, which is what
  shows that the hypotheses of Schauder's theorem cannot be relaxed to a Lipschitz condition.  Its
  doc comment records that the book's `0 < t ≤ √(k² - 1)` alone does not give `T(K) ⊆ K`.

## Not formalized here

Theorem 5.5.1 (Brouwer), Theorem 5.5.4 (Schauder) and §5.5.1 in its entirety — the rotation of a
completely continuous vector field and its properties P1–P5.  The obstruction is the same for all
three and is a missing theory, not a missing proof: Mathlib has no Brouwer fixed-point theorem and
no degree theory of any kind, and the book quotes each of them without proof.
-/

namespace AtkinsonHan.Chapter05

/-- **Definition 5.5.3.** An operator `T` is **completely continuous** on `K` when it is a compact
map on `K` — the image of every bounded subset of `K` is relatively compact — and is continuous
on `K`. -/
def IsCompletelyContinuousOn {V W : Type*} [SeminormedAddCommGroup V] [TopologicalSpace W]
    (T : V → W) (K : Set V) : Prop :=
  IsCompactMap T K ∧ ContinuousOn T K

/-- **Proposition 5.5.5.** Let `T` be completely continuous on an open set `K` of a Banach space
and Fréchet differentiable at `v₀ ∈ K`. Then the derivative `T'(v₀)` is a compact linear operator,
and so the Fredholm alternative applies to `I - T'(v₀)`.

The backbone proves more: continuity of `T` is not used, only differentiability at `v₀` together
with compactness on bounded sets. -/
theorem proposition_5_5_5 {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] {T : V → W} {K : Set V}
    (hT : IsCompletelyContinuousOn T K) (hK : IsOpen K) {v₀ : V} (hv₀ : v₀ ∈ K) {A : V →L[ℝ] W}
    (hA : HasFDerivAt T A v₀) : IsCompactOperator A :=
  hT.1.isCompactOperator_hasFDerivAt (hK.mem_nhds hv₀) hA

/-! ### Example 5.5.2: a Lipschitz self-map of the unit ball with no fixed point -/

section Example552

open Filter Metric Topology Set
open scoped ENNReal

/-- Prefixing a real number to a sequence.  On `ℓ²(ℕ, ℝ)` this is the **unilateral shift** together
with a rank-one correction placing `c` in the first coordinate, which is Example 5.5.2's map read in
the coordinates of the orthonormal basis. -/
def prepend (c : ℝ) (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => c
  | n + 1 => f n

@[simp] theorem prepend_zero (c : ℝ) (f : ℕ → ℝ) : prepend c f 0 = c := rfl

@[simp] theorem prepend_succ (c : ℝ) (f : ℕ → ℝ) (n : ℕ) : prepend c f (n + 1) = f n := rfl

theorem prepend_sub (c d : ℝ) (f g : ℕ → ℝ) :
    prepend c f - prepend d g = prepend (c - d) (f - g) := by
  funext n
  cases n <;> simp

/-- Prefixing preserves square-summability: it only moves the terms along by one. -/
theorem memℓp_prepend (c : ℝ) {f : ℕ → ℝ} (hf : Memℓp f 2) : Memℓp (prepend c f) 2 := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  rw [memℓp_gen_iff hp] at hf ⊢
  exact (summable_nat_add_iff 1).mp (by simpa using hf)

/-- Example 5.5.2's map in coordinates: the unilateral shift on `ℓ²(ℕ, ℝ)` with `c` inserted in the
first coordinate. -/
noncomputable def prependLp (c : ℝ) (f : lp (fun _ : ℕ => ℝ) 2) : lp (fun _ : ℕ => ℝ) 2 :=
  ⟨prepend c f, memℓp_prepend c f.2⟩

@[simp] theorem prependLp_coe (c : ℝ) (f : lp (fun _ : ℕ => ℝ) 2) :
    ⇑(prependLp c f) = prepend c ⇑f := rfl

/-- `‖(c, f₀, f₁, …)‖² = c² + ‖f‖²`: the inserted coordinate is orthogonal to the shifted ones. -/
theorem norm_prependLp_sq (c : ℝ) (f : lp (fun _ : ℕ => ℝ) 2) :
    ‖prependLp c f‖ ^ 2 = c ^ 2 + ‖f‖ ^ 2 := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have hsq : ∀ g : lp (fun _ : ℕ => ℝ) 2, ‖g‖ ^ 2 = ∑' n, ‖g n‖ ^ 2 := by
    intro g
    have h := lp.norm_rpow_eq_tsum hp g
    simpa using h
  have hsum : Summable fun n => ‖prepend c (f : ℕ → ℝ) n‖ ^ 2 := by
    have h := memℓp_prepend c (lp.memℓp f)
    rw [memℓp_gen_iff hp] at h
    simpa using h
  rw [hsq, hsq]
  simp only [prependLp_coe]
  rw [hsum.tsum_eq_zero_add]
  simp [Real.norm_eq_abs, sq_abs]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Example 5.5.2**'s map: `T(v) = t(1 - ‖v‖) φ₀ + ∑_j ⟪φ_j, v⟫ φ_{j+1}`, written through the
coordinate isomorphism `HilbertBasis.repr` of the orthonormal basis `φ`. -/
noncomputable def shiftMap (b : HilbertBasis ℕ ℝ V) (t : ℝ) (v : V) : V :=
  b.repr.symm (prependLp (t * (1 - ‖v‖)) (b.repr v))

/-- `‖T v‖² = t²(1 - ‖v‖)² + ‖v‖²`. -/
theorem norm_shiftMap_sq (b : HilbertBasis ℕ ℝ V) (t : ℝ) (v : V) :
    ‖shiftMap b t v‖ ^ 2 = (t * (1 - ‖v‖)) ^ 2 + ‖v‖ ^ 2 := by
  rw [shiftMap, LinearIsometryEquiv.norm_map, norm_prependLp_sq, LinearIsometryEquiv.norm_map]

/-- `‖T v - T w‖² = t²(‖v‖ - ‖w‖)² + ‖v - w‖²`, the shift being an isometry. -/
theorem norm_shiftMap_sub_sq (b : HilbertBasis ℕ ℝ V) (t : ℝ) (v w : V) :
    ‖shiftMap b t v - shiftMap b t w‖ ^ 2 = (t * (‖w‖ - ‖v‖)) ^ 2 + ‖v - w‖ ^ 2 := by
  have hsub : prependLp (t * (1 - ‖v‖)) (b.repr v) - prependLp (t * (1 - ‖w‖)) (b.repr w)
      = prependLp (t * (‖w‖ - ‖v‖)) (b.repr v - b.repr w) := by
    refine Subtype.ext ?_
    have h : ⇑(prependLp (t * (1 - ‖v‖)) (b.repr v) - prependLp (t * (1 - ‖w‖)) (b.repr w))
        = prepend (t * (1 - ‖v‖)) (b.repr v) - prepend (t * (1 - ‖w‖)) (b.repr w) :=
      lp.coeFn_sub _ _
    rw [h, prepend_sub]
    have hc : t * (1 - ‖v‖) - t * (1 - ‖w‖) = t * (‖w‖ - ‖v‖) := by ring
    rw [hc]
    rfl
  rw [shiftMap, shiftMap, ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map, hsub,
    norm_prependLp_sq, ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map]

/-- **Example 5.5.2.**  On a Hilbert space with orthonormal basis `{φ_j}`, let `K` be the closed
unit ball and let `T(v) = t(1 - ‖v‖) φ₀ + ∑_j ⟪φ_j, v⟫ φ_{j+1}`.  For `1 < k` and
`0 < t ≤ min(1, √(k² - 1))` the map `T` sends `K` into `K`, is Lipschitz with constant `k`, and has
no fixed point — anywhere, not merely in `K`.  This is what shows that the hypotheses of Schauder's
theorem cannot be relaxed to a Lipschitz condition, and that Theorem 5.1.3 needs its constant to be
*less* than one.

**The book's hypothesis `0 < t ≤ √(k² - 1)` is not enough for `T(K) ⊆ K`, and `t ≤ 1` is added
here.**  With `k = 2` and `t = √3` the printed condition holds, yet `‖T 0‖² = t² = 3 > 1`.  The
constraint `t ≤ 1` is exactly what `‖T v‖² = t²(1 - ‖v‖)² + ‖v‖² ≤ 1` for every `‖v‖ ≤ 1` demands,
as `v = 0` shows; `t ≤ √(k² - 1)` is the separate constraint that makes `√(1 + t²) ≤ k`.  Neither
implies the other, and the example is unaffected: `t = 1` gives a `√2`-Lipschitz self-map of the
ball with no fixed point. -/
theorem example_5_5_2 (b : HilbertBasis ℕ ℝ V) {t k : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hk : 1 < k)
    (htk : t ≤ Real.sqrt (k ^ 2 - 1)) :
    MapsTo (shiftMap b t) (closedBall 0 1) (closedBall 0 1) ∧
      (∀ v w : V, ‖shiftMap b t v - shiftMap b t w‖ ≤ k * ‖v - w‖) ∧
      ∀ v : V, shiftMap b t v ≠ v := by
  have hk0 : (0 : ℝ) ≤ k := by linarith
  have htk2 : t ^ 2 ≤ k ^ 2 - 1 := by
    have h := Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ k ^ 2 - 1)
    nlinarith [Real.sqrt_nonneg (k ^ 2 - 1)]
  refine ⟨fun v hv => ?_, fun v w => ?_, fun v hfix => ?_⟩
  · -- `T` maps the closed unit ball into itself
    simp only [mem_closedBall, dist_zero_right] at hv ⊢
    have hv0 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
    have ht2 : t ^ 2 ≤ 1 := by nlinarith
    have hsq : ‖shiftMap b t v‖ ^ 2 ≤ 1 := by
      rw [norm_shiftMap_sq]
      nlinarith [mul_nonneg hv0 (sub_nonneg.2 hv), sq_nonneg (1 - ‖v‖),
        mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - t ^ 2) (sq_nonneg (1 - ‖v‖))]
    nlinarith [norm_nonneg (shiftMap b t v)]
  · -- `T` is `k`-Lipschitz, since `√(1 + t²) ≤ k`
    have hsq : ‖shiftMap b t v - shiftMap b t w‖ ^ 2 ≤ (k * ‖v - w‖) ^ 2 := by
      rw [norm_shiftMap_sub_sq]
      have h1 : (‖w‖ - ‖v‖) ^ 2 ≤ ‖v - w‖ ^ 2 := by
        have h2 : |‖w‖ - ‖v‖| ≤ ‖v - w‖ := by
          rw [abs_sub_comm]; exact abs_norm_sub_norm_le v w
        nlinarith [abs_nonneg (‖w‖ - ‖v‖), sq_abs (‖w‖ - ‖v‖)]
      nlinarith [sq_nonneg t, norm_nonneg (v - w)]
    nlinarith [norm_nonneg (shiftMap b t v - shiftMap b t w),
      mul_nonneg hk0 (norm_nonneg (v - w))]
  · -- a fixed point would have all its coordinates equal, hence zero
    set f : lp (fun _ : ℕ => ℝ) 2 := b.repr v with hfdef
    have hcoord : prepend (t * (1 - ‖v‖)) ⇑f = ⇑f := by
      have h : prependLp (t * (1 - ‖v‖)) f = f := by
        have h1 := congrArg b.repr hfix
        rw [shiftMap, LinearIsometryEquiv.apply_symm_apply] at h1
        exact h1
      exact congrArg (fun g : lp (fun _ : ℕ => ℝ) 2 => ⇑g) h
    have hconst : ∀ n : ℕ, (f : ℕ → ℝ) n = (f : ℕ → ℝ) 0 := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [← ih, ← congrFun hcoord (n + 1), prepend_succ]
    have hsum : Summable fun n => ‖(f : ℕ → ℝ) n‖ ^ 2 := by
      have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
      have h := lp.memℓp f
      rw [memℓp_gen_iff hp] at h
      simpa using h
    have hzero : ‖(f : ℕ → ℝ) 0‖ ^ 2 = 0 := by
      have htend := hsum.tendsto_atTop_zero
      have hcongr : (fun n => ‖(f : ℕ → ℝ) n‖ ^ 2) = fun _ : ℕ => ‖(f : ℕ → ℝ) 0‖ ^ 2 :=
        funext fun n => by rw [hconst n]
      rw [hcongr] at htend
      exact tendsto_nhds_unique tendsto_const_nhds htend
    have hf0 : (f : ℕ → ℝ) 0 = 0 := by
      have h : ‖(f : ℕ → ℝ) 0‖ = 0 := by nlinarith [norm_nonneg ((f : ℕ → ℝ) 0)]
      simpa using h
    have hv0 : ‖v‖ = 0 := by
      have hz : v = 0 := by
        have hfzero : f = 0 := by
          refine Subtype.ext (funext fun n => ?_)
          rw [hconst n, hf0]
          rfl
        rw [← b.repr.symm_apply_apply v, ← hfdef, hfzero, map_zero]
      rw [hz, norm_zero]
    have hend := congrFun hcoord 0
    rw [prepend_zero, hf0, hv0] at hend
    simp only [sub_zero, mul_one] at hend
    exact ht.ne' hend

end Example552

end AtkinsonHan.Chapter05

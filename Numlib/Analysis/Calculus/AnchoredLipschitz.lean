import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.Analysis.Calculus.LipschitzIteratedFDeriv

/-!
# Anchored Lipschitz continuity of iterated derivatives

`IteratedFDerivLipschitzAnchored f j L A D` says that
`‖∇^j f(x) - ∇^j f(y)‖ ≤ L ‖x - y‖` for `x` in an anchor set `A` (in applications a sublevel set)
and `y` in a larger set `D` ([cartis2022evaluation], assumption f.D1qLaB.X, (14.2.9)). With
`A = D` it is `IteratedFDerivLipschitzOn f j L D`.

The point of the notion is that products inherit it with constants that are affine in the size of
the order-zero factors on the anchor set only ([cartis2022evaluation], Lemma 14.3.6, whose proof
is (B.14.9)–(B.14.18)): if `u` and `v` have anchored-Lipschitz and bounded derivatives of orders
`1, …, p` on `D` and `|u| ≤ U`, `|v| ≤ V` on `A`, then `∇^j (u v)` is anchored-Lipschitz with
constant `K₀ + Lv_j U + Lu_j V` and bounded on `A` by `K₂ + Bv_j U + Bu_j V`, where `K₀` and `K₂`
depend only on the derivative constants. Applied to `½ (f - t)²` this gives constants independent
of the target `t`.

## Main definitions

* `IteratedFDerivLipschitzAnchored f j L A D`;
* `AnchoredJetBounds u p L B U A D`: the hypotheses on each factor (smoothness on `D`, anchored
  Lipschitz constants `L i` and bounds `B i` for the derivatives of orders `1 ≤ i ≤ p`, and the
  anchor bound `|u| ≤ U` on `A`);
* `anchoredMulLipConst`, `anchoredMulBoundConst`: the constants `K₀` and `K₂`.

## Main results

* monotonicity, `IteratedFDerivLipschitzOn.anchored`, `IteratedFDerivLipschitzAnchored.add`,
  `.const_smul`, `.sum`;
* `AnchoredJetBounds.norm_iteratedFDeriv_mul_le`: the derivative bound for `u v` on `A`;
* `IteratedFDerivLipschitzAnchored.mul`: the anchored Lipschitz bound for `u v`;
* `AnchoredJetBounds.lipschitzAnchored_half_sq`, `.norm_iteratedFDeriv_half_sq_le`: `u² / 2`;
* `AnchoredJetBounds.lipschitzAnchored_half_norm_sq`, `.norm_iteratedFDeriv_half_norm_sq_le`:
  `‖c‖² / 2` for `c` with values in `EuclideanSpace ℝ (Fin m)` (Lemma 14.3.6(i)).

## Implementation notes

The book expands `∇^j (u v)` by the Leibniz rule and splits each difference of products by hand.
Here only Mathlib's Leibniz *bound* `norm_iteratedFDerivWithin_mul_le` is used: with
`a = u(x)`, `b = v(x)` one writes `u v = (u - a)(v - b) + a v + b u - a b`, and for
`y = x + t` the difference of the `j`-th derivatives of `w = (u - a)(v - b)` at `x` and `y` is the
`j`-th derivative at `x` of `z ↦ w(z) - w(z + t) = (u(z) - u(z + t)) (v(z) - b) +
(u(z + t) - a) (v(z) - v(z + t))`, which is bounded by the Leibniz bound since `v - b` vanishes at
`x` and the increments are `O(‖t‖)`.
-/

open Finset
open scoped Nat

section Basic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The `j`-th derivative of `f` is `L`-Lipschitz *anchored* in `A` with respect to `D`:
`‖∇^j f(x) - ∇^j f(y)‖ ≤ L ‖x - y‖` for all `x ∈ A` and `y ∈ D` ([cartis2022evaluation],
(14.2.9)). -/
def IteratedFDerivLipschitzAnchored (f : E → F) (j : ℕ) (L : ℝ) (A D : Set E) : Prop :=
  ∀ x ∈ A, ∀ y ∈ D, ‖iteratedFDeriv ℝ j f x - iteratedFDeriv ℝ j f y‖ ≤ L * ‖x - y‖

variable {f g : E → F} {j : ℕ} {L L' : ℝ} {A A' D D' : Set E}

theorem iteratedFDerivLipschitzAnchored_iff : IteratedFDerivLipschitzAnchored f j L A D ↔
    ∀ x ∈ A, ∀ y ∈ D, ‖iteratedFDeriv ℝ j f x - iteratedFDeriv ℝ j f y‖ ≤ L * ‖x - y‖ :=
  Iff.rfl

namespace IteratedFDerivLipschitzAnchored

theorem mono (h : IteratedFDerivLipschitzAnchored f j L A D) (hA : A' ⊆ A) (hD : D' ⊆ D)
    (hL : L ≤ L') : IteratedFDerivLipschitzAnchored f j L' A' D' :=
  fun x hx y hy => (h x (hA hx) y (hD hy)).trans (by gcongr)

theorem mono_left (h : IteratedFDerivLipschitzAnchored f j L A D) (hA : A' ⊆ A) :
    IteratedFDerivLipschitzAnchored f j L A' D :=
  h.mono hA subset_rfl le_rfl

theorem mono_right (h : IteratedFDerivLipschitzAnchored f j L A D) (hD : D' ⊆ D) :
    IteratedFDerivLipschitzAnchored f j L A D' :=
  h.mono subset_rfl hD le_rfl

theorem mono_const (h : IteratedFDerivLipschitzAnchored f j L A D) (hL : L ≤ L') :
    IteratedFDerivLipschitzAnchored f j L' A D :=
  h.mono subset_rfl subset_rfl hL

/-- Sums: the constants add. Both functions are assumed `C^j` on `D ⊇ A`. -/
theorem add (hf : IteratedFDerivLipschitzAnchored f j L A D)
    (hg : IteratedFDerivLipschitzAnchored g j L' A D) (hfd : ∀ y ∈ D, ContDiffAt ℝ j f y)
    (hgd : ∀ y ∈ D, ContDiffAt ℝ j g y) (hAD : A ⊆ D) :
    IteratedFDerivLipschitzAnchored (f + g) j (L + L') A D := by
  intro x hx y hy
  rw [iteratedFDeriv_add_apply (hfd x (hAD hx)) (hgd x (hAD hx)),
    iteratedFDeriv_add_apply (hfd y hy) (hgd y hy), add_sub_add_comm, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hf x hx y hy) (hg x hx y hy))

/-- Constant multiples: the constant is multiplied by `|c|`. -/
theorem const_smul (hf : IteratedFDerivLipschitzAnchored f j L A D)
    (hfd : ∀ y ∈ D, ContDiffAt ℝ j f y) (hAD : A ⊆ D) (c : ℝ) :
    IteratedFDerivLipschitzAnchored (fun z => c • f z) j (|c| * L) A D := by
  intro x hx y hy
  rw [iteratedFDeriv_const_smul_apply' (hfd x (hAD hx)),
    iteratedFDeriv_const_smul_apply' (hfd y hy), ← smul_sub, norm_smul, Real.norm_eq_abs, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf x hx y hy) (abs_nonneg c)

/-- Finite sums: the constants add. -/
theorem sum {ι : Type*} {t : Finset ι} {f : ι → E → F} {L : ι → ℝ}
    (hf : ∀ i ∈ t, IteratedFDerivLipschitzAnchored (f i) j (L i) A D)
    (hfd : ∀ i ∈ t, ∀ y ∈ D, ContDiffAt ℝ j (f i) y) (hAD : A ⊆ D) :
    IteratedFDerivLipschitzAnchored (fun z => ∑ i ∈ t, f i z) j (∑ i ∈ t, L i) A D := by
  intro x hx y hy
  rw [iteratedFDeriv_fun_sum_apply fun i hi => hfd i hi x (hAD hx),
    iteratedFDeriv_fun_sum_apply fun i hi => hfd i hi y hy, ← sum_sub_distrib, sum_mul]
  exact (norm_sum_le _ _).trans (sum_le_sum fun i hi => hf i hi x hx y hy)

end IteratedFDerivLipschitzAnchored

/-- A Lipschitz `j`-th derivative on `D` is anchored-Lipschitz for every anchor set `A ⊆ D`. -/
theorem IteratedFDerivLipschitzOn.anchored (h : IteratedFDerivLipschitzOn f j L D)
    (hAD : A ⊆ D) : IteratedFDerivLipschitzAnchored f j L A D :=
  fun x hx y hy => iteratedFDerivLipschitzOn_iff.1 h x (hAD hx) y hy

/-- With `A = D` the anchored condition is the Lipschitz condition on `D`. -/
theorem iteratedFDerivLipschitzAnchored_self_iff :
    IteratedFDerivLipschitzAnchored f j L D D ↔ IteratedFDerivLipschitzOn f j L D := by
  rw [iteratedFDerivLipschitzOn_iff]
  rfl

end Basic

section Product

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Leibniz bound on an open set: if `f` and `g` are `C^n` on an open set `S ∋ x`, then
`‖∇^n (f g)(x)‖ ≤ ∑_{i ≤ n} C(n, i) ‖∇^i f(x)‖ ‖∇^{n-i} g(x)‖`. -/
theorem norm_iteratedFDeriv_mul_le_of_isOpen {f g : E → ℝ} {S : Set E} (hS : IsOpen S) {n : ℕ}
    (hf : ContDiffOn ℝ n f S) (hg : ContDiffOn ℝ n g S) {x : E} (hx : x ∈ S) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤ ∑ i ∈ range (n + 1),
      (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖ := by
  have h := norm_iteratedFDerivWithin_mul_le hf hg hS.uniqueDiffOn hx le_rfl
  rw [iteratedFDerivWithin_of_isOpen n hS hx] at h
  refine h.trans (le_of_eq (sum_congr rfl fun i _ => ?_))
  rw [iteratedFDerivWithin_of_isOpen i hS hx, iteratedFDerivWithin_of_isOpen (n - i) hS hx]

/-- Leibniz bound with given bounds `α i`, `β i` on the derivatives of the factors at `x`. -/
theorem norm_iteratedFDeriv_mul_le_of_le {f g : E → ℝ} {S : Set E} (hS : IsOpen S) {n : ℕ}
    (hf : ContDiffOn ℝ n f S) (hg : ContDiffOn ℝ n g S) {x : E} (hx : x ∈ S) {α β : ℕ → ℝ}
    (hα : ∀ i ≤ n, ‖iteratedFDeriv ℝ i f x‖ ≤ α i) (hβ : ∀ i ≤ n, ‖iteratedFDeriv ℝ i g x‖ ≤ β i) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤
      ∑ i ∈ range (n + 1), (n.choose i : ℝ) * (α i * β (n - i)) := by
  refine (norm_iteratedFDeriv_mul_le_of_isOpen hS hf hg hx).trans (sum_le_sum fun i hi => ?_)
  have hi' : i ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hi)
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul (hα i hi') (hβ _ (Nat.sub_le n i)) (norm_nonneg _)
    ((norm_nonneg _).trans (hα i hi'))) (Nat.cast_nonneg _)

/-- The increment constant of the `i`-th derivative: `L i` for `i ≥ 1`, and `B 1` (the mean
value theorem) for `i = 0`. -/
def anchoredIncr (B L : ℕ → ℝ) (i : ℕ) : ℝ := if i = 0 then B 1 else L i

/-- The bound `B k` of the `k`-th derivative for `k ≥ 1`, and `0` for `k = 0`. -/
def anchoredJet (B : ℕ → ℝ) (k : ℕ) : ℝ := if k = 0 then 0 else B k

/-- The part `K₀` of the anchored Lipschitz constant of `∇^j (u v)` that does not involve the
anchor bounds `U`, `V`:
`∑_{i ≤ j} C(j, i) (λᵤ(i) β_v(j - i) + γ(i))`, with `λᵤ = anchoredIncr Bu Lu`,
`β_v = anchoredJet Bv`, `γ(0) = 2 Bu₁ Bv_j` and `γ(i) = Bu_i λ_v(j - i)` for `i ≥ 1`. -/
noncomputable def anchoredMulLipConst (Lu Lv Bu Bv : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ range (j + 1), (j.choose i : ℝ) *
    (anchoredIncr Bu Lu i * anchoredJet Bv (j - i) +
      if i = 0 then 2 * Bu 1 * Bv j else Bu i * anchoredIncr Bv Lv (j - i))

/-- The part `K₂ = ∑_{0 < i < j} C(j, i) Bu_i Bv_{j-i}` of the bound on `∇^j (u v)` that does not
involve the anchor bounds `U`, `V`. -/
noncomputable def anchoredMulBoundConst (Bu Bv : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ range (j + 1), (j.choose i : ℝ) * (anchoredJet Bu i * anchoredJet Bv (j - i))

/-- Hypotheses on a factor `u` of a product, [cartis2022evaluation] f.D1pLaB.X together with a
bound on the anchor set: `u` is `C^p` on `D`, its derivatives of orders `1 ≤ i ≤ p` are
`L i`-Lipschitz anchored in `A` and bounded by `B i` on `D`, and `|u| ≤ U` on `A`. -/
structure AnchoredJetBounds (u : E → ℝ) (p : ℕ) (L B : ℕ → ℝ) (U : ℝ) (A D : Set E) : Prop where
  contDiffOn : ContDiffOn ℝ p u D
  lipschitzAnchored : ∀ i ∈ Icc 1 p, IteratedFDerivLipschitzAnchored u i (L i) A D
  norm_le : ∀ i ∈ Icc 1 p, ∀ y ∈ D, ‖iteratedFDeriv ℝ i u y‖ ≤ B i
  abs_le : ∀ x ∈ A, |u x| ≤ U

/-- `‖∇⁰ f(x) - ∇⁰ f(y)‖ = ‖f(x) - f(y)‖`. -/
theorem norm_iteratedFDeriv_zero_sub (w : E → ℝ) (x y : E) :
    ‖iteratedFDeriv ℝ 0 w x - iteratedFDeriv ℝ 0 w y‖ = ‖w x - w y‖ := by
  rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply, Function.comp_apply, ← map_sub,
    LinearIsometryEquiv.norm_map]

/-- The derivatives of the increment `z ↦ w(z) - w(z + t)` at `x` are the increments of the
derivatives of `w` between `x` and `x + t`. -/
theorem iteratedFDeriv_sub_comp_add_right {w : E → ℝ} {i : ℕ} {x t : E}
    (hw : ContDiffAt ℝ i w x) (hwt : ContDiffAt ℝ i w (x + t)) :
    iteratedFDeriv ℝ i (fun z => w z - w (z + t)) x =
      iteratedFDeriv ℝ i w x - iteratedFDeriv ℝ i w (x + t) := by
  have hwt' : ContDiffAt ℝ i (fun z => w (z + t)) x :=
    hwt.comp x (contDiffAt_id.add contDiffAt_const)
  change iteratedFDeriv ℝ i (w - fun z => w (z + t)) x = _
  rw [iteratedFDeriv_sub_apply hw hwt', iteratedFDeriv_comp_add_right]

/-- Decomposition `u v = (u - a)(v - b) + a v + b u - a b` at the level of the `j`-th derivative,
`j ≥ 1`. -/
theorem iteratedFDeriv_mul_eq_add {u v : E → ℝ} {j : ℕ} {z : E} (hu : ContDiffAt ℝ j u z)
    (hv : ContDiffAt ℝ j v z) (hj : j ≠ 0) (a b : ℝ) :
    iteratedFDeriv ℝ j (fun y => u y * v y) z =
      a • iteratedFDeriv ℝ j v z + b • iteratedFDeriv ℝ j u z +
        iteratedFDeriv ℝ j (fun y => (u y - a) * (v y - b)) z := by
  have hw : ContDiffAt ℝ j (fun y => (u y - a) * (v y - b)) z :=
    (hu.sub contDiffAt_const).mul (hv.sub contDiffAt_const)
  have hfun : (fun y => u y * v y) =
      (fun y => (u y - a) * (v y - b)) + ((fun y => a • v y) + fun y => b • u y) -
        fun _ => a * b := by
    funext y
    simp only [Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hsum : ContDiffAt ℝ j ((fun y => (u y - a) * (v y - b)) +
      ((fun y => a • v y) + fun y => b • u y)) z :=
    hw.add ((hv.const_smul a).add (hu.const_smul b))
  rw [hfun, iteratedFDeriv_sub_apply hsum (contDiffAt_const (c := a * b)),
    iteratedFDeriv_const_of_ne hj, Pi.zero_apply, sub_zero,
    iteratedFDeriv_add_apply (f := fun y => (u y - a) * (v y - b))
      (g := (fun y => a • v y) + fun y => b • u y) hw ((hv.const_smul a).add (hu.const_smul b)),
    iteratedFDeriv_add_apply (f := fun y => a • v y) (g := fun y => b • u y) (hv.const_smul a)
      (hu.const_smul b),
    iteratedFDeriv_const_smul_apply' hv, iteratedFDeriv_const_smul_apply' hu]
  abel

namespace AnchoredJetBounds

variable {u v : E → ℝ} {p : ℕ} {Lu Lv Bu Bv : ℕ → ℝ} {U V : ℝ} {A D : Set E}

theorem contDiffAt (h : AnchoredJetBounds u p Lu Bu U A D) (hD : IsOpen D) {y : E} (hy : y ∈ D)
    {i : ℕ} (hi : i ≤ p) : ContDiffAt ℝ i u y :=
  (h.contDiffOn.contDiffAt (hD.mem_nhds hy)).of_le (by exact_mod_cast hi)

/-- The increments of the derivatives of orders `0 ≤ i ≤ p` between an anchor `x ∈ A` and
`y ∈ D` (the order `0` by the mean value theorem on the convex set `D`). -/
theorem norm_sub_le (h : AnchoredJetBounds u p Lu Bu U A D) (hD : IsOpen D) (hDc : Convex ℝ D)
    (hAD : A ⊆ D) (hp : 1 ≤ p) {x y : E} (hx : x ∈ A) (hy : y ∈ D) {i : ℕ} (hi : i ≤ p) :
    ‖iteratedFDeriv ℝ i u x - iteratedFDeriv ℝ i u y‖ ≤ anchoredIncr Bu Lu i * ‖x - y‖ := by
  unfold anchoredIncr
  split_ifs with h0
  · subst h0
    have hlip : IteratedFDerivLipschitzOn u 0 (Bu 1) D :=
      iteratedFDerivLipschitzOn_of_norm_le hDc (fun z hz => h.contDiffAt hD hz hp)
        fun z hz => h.norm_le 1 (mem_Icc.2 ⟨le_rfl, hp⟩) z hz
    exact iteratedFDerivLipschitzOn_iff.1 hlip x (hAD hx) y hy
  · exact h.lipschitzAnchored i (mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 h0, hi⟩) x hx y hy

/-- The derivatives of `u` at an anchor `x ∈ A`: `|u(x)| ≤ U` and `‖∇^i u(x)‖ ≤ B i` for
`1 ≤ i ≤ p`. -/
theorem norm_iteratedFDeriv_le (h : AnchoredJetBounds u p Lu Bu U A D) (hAD : A ⊆ D) {x : E}
    (hx : x ∈ A) {i : ℕ} (hi : i ≤ p) :
    ‖iteratedFDeriv ℝ i u x‖ ≤ if i = 0 then U else Bu i := by
  split_ifs with h0
  · subst h0
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    exact h.abs_le x hx
  · exact h.norm_le i (mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 h0, hi⟩) x (hAD hx)

/-- The derivatives of `u - c` are those of `u` in positive order. -/
theorem iteratedFDeriv_sub_const {w : E → ℝ} {i : ℕ} {z : E} (hw : ContDiffAt ℝ i w z) (c : ℝ)
    (hi : i ≠ 0) : iteratedFDeriv ℝ i (fun y => w y - c) z = iteratedFDeriv ℝ i w z := by
  change iteratedFDeriv ℝ i (w - fun _ => c) z = _
  rw [iteratedFDeriv_sub_apply hw contDiffAt_const, iteratedFDeriv_const_of_ne hi,
    Pi.zero_apply, sub_zero]

/-- **Derivative bound for products on the anchor set** ([cartis2022evaluation], (14.3.61),
(14.3.63)): for `1 ≤ j ≤ p` and `x ∈ A`,
`‖∇^j (u v)(x)‖ ≤ K₂ + Bv_j U + Bu_j V`. -/
theorem norm_iteratedFDeriv_mul_le (hu : AnchoredJetBounds u p Lu Bu U A D)
    (hv : AnchoredJetBounds v p Lv Bv V A D) (hD : IsOpen D) (hAD : A ⊆ D) {j : ℕ}
    (hj : j ∈ Icc 1 p) {x : E} (hx : x ∈ A) :
    ‖iteratedFDeriv ℝ j (fun y => u y * v y) x‖ ≤
      anchoredMulBoundConst Bu Bv j + Bv j * U + Bu j * V := by
  obtain ⟨hj1, hjp⟩ := mem_Icc.1 hj
  have hcd : ∀ {w : E → ℝ}, ContDiffOn ℝ p w D → ContDiffOn ℝ j w D :=
    fun hw => hw.of_le (by exact_mod_cast hjp)
  refine (norm_iteratedFDeriv_mul_le_of_le hD (hcd hu.contDiffOn) (hcd hv.contDiffOn) (hAD hx)
    (fun i hi => hu.norm_iteratedFDeriv_le hAD hx (hi.trans hjp))
    (fun i hi => hv.norm_iteratedFDeriv_le hAD hx (hi.trans hjp))).trans ?_
  have hU : 0 ≤ U := (abs_nonneg _).trans (hu.abs_le x hx)
  have hV : 0 ≤ V := (abs_nonneg _).trans (hv.abs_le x hx)
  have hterm : ∀ i ∈ range (j + 1),
      (j.choose i : ℝ) * ((if i = 0 then U else Bu i) * (if j - i = 0 then V else Bv (j - i))) =
        (j.choose i : ℝ) * (anchoredJet Bu i * anchoredJet Bv (j - i)) +
          ((if i = 0 then Bv j * U else 0) + if i = j then Bu j * V else 0) := by
    intro i hi
    have hi' : i ≤ j := Nat.lt_succ_iff.1 (mem_range.1 hi)
    unfold anchoredJet
    by_cases h0 : i = 0
    · subst h0
      have h1 : j ≠ 0 := by omega
      have h2 : (0 : ℕ) ≠ j := by omega
      simp [h1, h2, mul_comm]
    · by_cases hij : i = j
      · subst hij
        simp [h0]
      · have : j - i ≠ 0 := by omega
        simp [h0, hij, this]
  rw [sum_congr rfl hterm, sum_add_distrib, sum_add_distrib, sum_ite_eq' (range (j + 1)) 0,
    sum_ite_eq' (range (j + 1)) j]
  simp only [anchoredMulBoundConst, mem_range, Nat.lt_succ_iff, zero_le, le_rfl, ite_true]
  linarith




/-- Shifting by a constant changes only the anchor bound: if `|u - c| ≤ U'` on `A`, then `u - c`
satisfies the same derivative hypotheses as `u`. -/
theorem sub_const (hu : AnchoredJetBounds u p Lu Bu U A D) (hD : IsOpen D) (hAD : A ⊆ D) (c : ℝ)
    {U' : ℝ} (hU' : ∀ x ∈ A, |u x - c| ≤ U') :
    AnchoredJetBounds (fun y => u y - c) p Lu Bu U' A D where
  contDiffOn := hu.contDiffOn.sub contDiffOn_const
  lipschitzAnchored i hi x hx y hy := by
    obtain ⟨hi1, hip⟩ := mem_Icc.1 hi
    have hi0 : i ≠ 0 := by omega
    rw [iteratedFDeriv_sub_const (hu.contDiffAt hD (hAD hx) hip) c hi0,
      iteratedFDeriv_sub_const (hu.contDiffAt hD hy hip) c hi0]
    exact hu.lipschitzAnchored i hi x hx y hy
  norm_le i hi y hy := by
    obtain ⟨hi1, hip⟩ := mem_Icc.1 hi
    rw [iteratedFDeriv_sub_const (hu.contDiffAt hD hy hip) c (by omega)]
    exact hu.norm_le i hi y hy
  abs_le := hU'

/-- **Anchored Lipschitz bound for products** ([cartis2022evaluation], Lemma 14.3.6, (14.3.60),
(14.3.62), proof (B.14.9)–(B.14.18)). Let `D` be open and convex, `A ⊆ D`, and let `u`, `v`
satisfy `AnchoredJetBounds` with constants `Lu, Bu, U` and `Lv, Bv, V`. Then for `1 ≤ j ≤ p` the
`j`-th derivative of `u v` is anchored-Lipschitz with constant `K₀ + Lv_j U + Lu_j V`, where
`K₀ = anchoredMulLipConst Lu Lv Bu Bv j` does not depend on `U`, `V`. -/
theorem _root_.IteratedFDerivLipschitzAnchored.mul (hu : AnchoredJetBounds u p Lu Bu U A D)
    (hv : AnchoredJetBounds v p Lv Bv V A D)
    (hD : IsOpen D) (hDc : Convex ℝ D) (hAD : A ⊆ D) {j : ℕ} (hj : j ∈ Icc 1 p) :
    IteratedFDerivLipschitzAnchored (fun y => u y * v y) j
      (anchoredMulLipConst Lu Lv Bu Bv j + Lv j * U + Lu j * V) A D := by
  obtain ⟨hj1, hjp⟩ := mem_Icc.1 hj
  have hp : 1 ≤ p := hj1.trans hjp
  have hj0 : j ≠ 0 := by omega
  intro x hx y hy
  have hxD := hAD hx
  set t := y - x with ht
  have hxt : x + t = y := by rw [ht]; abel
  set a := u x
  set b := v x
  set r := ‖x - y‖
  have hr : 0 ≤ r := norm_nonneg _
  have hU : 0 ≤ U := (abs_nonneg _).trans (hu.abs_le x hx)
  have hV : 0 ≤ V := (abs_nonneg _).trans (hv.abs_le x hx)
  -- smoothness on the open set `S = D ∩ (D - t)` containing `x`
  set S := D ∩ (fun z => z + t) ⁻¹' D with hS
  have hSo : IsOpen S := hD.inter (hD.preimage (continuous_id.add continuous_const))
  have hxS : x ∈ S := ⟨hxD, by simp [hxt, hy]⟩
  have hcd : ∀ {w : E → ℝ}, ContDiffOn ℝ p w D → ContDiffOn ℝ j w S := fun hw =>
    (hw.of_le (by exact_mod_cast hjp)).mono Set.inter_subset_left
  have hcdt : ∀ {w : E → ℝ}, ContDiffOn ℝ p w D → ContDiffOn ℝ j (fun z => w (z + t)) S :=
    fun hw => (hw.of_le (by exact_mod_cast hjp)).comp
      (contDiff_id.add contDiff_const).contDiffOn fun _ hz => hz.2
  have hδu : ContDiffOn ℝ j (fun z => u z - u (z + t)) S :=
    (hcd hu.contDiffOn).sub (hcdt hu.contDiffOn)
  have hvb : ContDiffOn ℝ j (fun z => v z - b) S := (hcd hv.contDiffOn).sub contDiffOn_const
  have hua : ContDiffOn ℝ j (fun z => u (z + t) - a) S :=
    (hcdt hu.contDiffOn).sub contDiffOn_const
  have hδv : ContDiffOn ℝ j (fun z => v z - v (z + t)) S :=
    (hcd hv.contDiffOn).sub (hcdt hv.contDiffOn)
  have hSn : S ∈ nhds x := hSo.mem_nhds hxS
  -- bounds on the derivatives of the four factors at `x`
  have B1 : ∀ i ≤ j, ‖iteratedFDeriv ℝ i (fun z => u z - u (z + t)) x‖ ≤
      anchoredIncr Bu Lu i * r := by
    intro i hi
    rw [iteratedFDeriv_sub_comp_add_right (hu.contDiffAt hD hxD (hi.trans hjp))
      (hxt ▸ hu.contDiffAt hD hy (hi.trans hjp)), hxt]
    exact hu.norm_sub_le hD hDc hAD hp hx hy (hi.trans hjp)
  have B2 : ∀ k ≤ j, ‖iteratedFDeriv ℝ k (fun z => v z - b) x‖ ≤ anchoredJet Bv k := by
    intro k hk
    unfold anchoredJet
    split_ifs with h0
    · subst h0
      simp [norm_iteratedFDeriv_zero, b]
    · rw [iteratedFDeriv_sub_const (hv.contDiffAt hD hxD (hk.trans hjp)) b h0]
      exact hv.norm_le k (mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 h0, hk.trans hjp⟩) x hxD
  have B3 : ∀ i ≤ j, ‖iteratedFDeriv ℝ i (fun z => u (z + t) - a) x‖ ≤
      if i = 0 then Bu 1 * r else Bu i := by
    intro i hi
    split_ifs with h0
    · subst h0
      rw [norm_iteratedFDeriv_zero, hxt, norm_sub_rev, ← norm_iteratedFDeriv_zero_sub]
      simpa [anchoredIncr] using hu.norm_sub_le hD hDc hAD hp hx hy (Nat.zero_le p)
    · have hc : ContDiffAt ℝ i (fun z => u (z + t)) x :=
        (hxt ▸ hu.contDiffAt hD hy (hi.trans hjp)).comp x (contDiffAt_id.add contDiffAt_const)
      rw [iteratedFDeriv_sub_const hc a h0, iteratedFDeriv_comp_add_right, hxt]
      exact hu.norm_le i (mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 h0, hi.trans hjp⟩) y hy
  have B4 : ∀ k ≤ j, ‖iteratedFDeriv ℝ k (fun z => v z - v (z + t)) x‖ ≤
      if k = j then 2 * Bv j else anchoredIncr Bv Lv k * r := by
    intro k hk
    rw [iteratedFDeriv_sub_comp_add_right (hv.contDiffAt hD hxD (hk.trans hjp))
      (hxt ▸ hv.contDiffAt hD hy (hk.trans hjp)), hxt]
    split_ifs with hkj
    · subst hkj
      have hjI : k ∈ Icc 1 p := mem_Icc.2 ⟨hj1, hjp⟩
      have h1 := hv.norm_le k hjI x hxD
      have h2 := hv.norm_le k hjI y hy
      exact (_root_.norm_sub_le _ _).trans (by linarith)
    · exact hv.norm_sub_le hD hDc hAD hp hx hy (hk.trans hjp)
  -- the product part
  have hw : iteratedFDeriv ℝ j (fun z => (u z - a) * (v z - b)) x -
      iteratedFDeriv ℝ j (fun z => (u z - a) * (v z - b)) y =
      iteratedFDeriv ℝ j (fun z => (u z - u (z + t)) * (v z - b)) x +
        iteratedFDeriv ℝ j (fun z => (u (z + t) - a) * (v z - v (z + t))) x := by
    have hwx : ContDiffAt ℝ j (fun z => (u z - a) * (v z - b)) x :=
      ((hu.contDiffAt hD hxD hjp).sub contDiffAt_const).mul
        ((hv.contDiffAt hD hxD hjp).sub contDiffAt_const)
    have hwy : ContDiffAt ℝ j (fun z => (u z - a) * (v z - b)) (x + t) := by
      rw [hxt]
      exact ((hu.contDiffAt hD hy hjp).sub contDiffAt_const).mul
        ((hv.contDiffAt hD hy hjp).sub contDiffAt_const)
    rw [← hxt, ← iteratedFDeriv_sub_comp_add_right hwx hwy]
    have hfun : (fun z => (u z - a) * (v z - b) - (u (z + t) - a) * (v (z + t) - b)) =
        (fun z => (u z - u (z + t)) * (v z - b)) +
          fun z => (u (z + t) - a) * (v z - v (z + t)) := by
      funext z
      simp only [Pi.add_apply]
      ring
    rw [hfun, iteratedFDeriv_add_apply ((hδu.mul hvb).contDiffAt hSn)
      ((hua.mul hδv).contDiffAt hSn)]
  have hT1 := norm_iteratedFDeriv_mul_le_of_le hSo hδu hvb hxS B1 B2
  have hT2 := norm_iteratedFDeriv_mul_le_of_le hSo hua hδv hxS B3 B4
  have hsum : (∑ i ∈ range (j + 1), (j.choose i : ℝ) *
      (anchoredIncr Bu Lu i * r * anchoredJet Bv (j - i))) +
      (∑ i ∈ range (j + 1), (j.choose i : ℝ) * ((if i = 0 then Bu 1 * r else Bu i) *
        (if j - i = j then 2 * Bv j else anchoredIncr Bv Lv (j - i) * r))) =
      anchoredMulLipConst Lu Lv Bu Bv j * r := by
    rw [← sum_add_distrib, anchoredMulLipConst, sum_mul]
    refine sum_congr rfl fun i hi => ?_
    have hi' : i ≤ j := Nat.lt_succ_iff.1 (mem_range.1 hi)
    by_cases h0 : i = 0
    · subst h0
      simp only [Nat.sub_zero, ite_true]
      ring
    · have : j - i ≠ j := by omega
      simp only [h0, this, ite_false]
      ring
  -- assemble
  have hdx := iteratedFDeriv_mul_eq_add (hu.contDiffAt hD hxD hjp) (hv.contDiffAt hD hxD hjp) hj0
    a b
  have hdy := iteratedFDeriv_mul_eq_add (hu.contDiffAt hD hy hjp) (hv.contDiffAt hD hy hjp) hj0
    a b
  have hjI : j ∈ Icc 1 p := mem_Icc.2 ⟨hj1, hjp⟩
  have hLv := hv.lipschitzAnchored j hjI x hx y hy
  have hLu := hu.lipschitzAnchored j hjI x hx y hy
  have ha : |a| ≤ U := hu.abs_le x hx
  have hb : |b| ≤ V := hv.abs_le x hx
  rw [hdx, hdy]
  calc ‖a • iteratedFDeriv ℝ j v x + b • iteratedFDeriv ℝ j u x +
        iteratedFDeriv ℝ j (fun z => (u z - a) * (v z - b)) x -
        (a • iteratedFDeriv ℝ j v y + b • iteratedFDeriv ℝ j u y +
          iteratedFDeriv ℝ j (fun z => (u z - a) * (v z - b)) y)‖
      = ‖a • (iteratedFDeriv ℝ j v x - iteratedFDeriv ℝ j v y) +
          b • (iteratedFDeriv ℝ j u x - iteratedFDeriv ℝ j u y) +
          (iteratedFDeriv ℝ j (fun z => (u z - u (z + t)) * (v z - b)) x +
            iteratedFDeriv ℝ j (fun z => (u (z + t) - a) * (v z - v (z + t))) x)‖ := by
        rw [← hw, smul_sub, smul_sub]
        congr 1
        abel
    _ ≤ |a| * ‖iteratedFDeriv ℝ j v x - iteratedFDeriv ℝ j v y‖ +
          |b| * ‖iteratedFDeriv ℝ j u x - iteratedFDeriv ℝ j u y‖ +
          (‖iteratedFDeriv ℝ j (fun z => (u z - u (z + t)) * (v z - b)) x‖ +
            ‖iteratedFDeriv ℝ j (fun z => (u (z + t) - a) * (v z - v (z + t))) x‖) := by
        refine (norm_add₃_le).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        gcongr
        exact norm_add_le _ _
    _ ≤ U * (Lv j * r) + V * (Lu j * r) + anchoredMulLipConst Lu Lv Bu Bv j * r := by
        rw [← hsum]
        gcongr
    _ = (anchoredMulLipConst Lu Lv Bu Bv j + Lv j * U + Lu j * V) * r := by ring

/-- **Half squares, Lipschitz part** ([cartis2022evaluation], Lemma 14.3.6(ii) for
`½ (f - t)²`): for `1 ≤ j ≤ p`, `∇^j (u² / 2)` is anchored-Lipschitz with constant
`K₀ / 2 + Lu_j U`, `K₀ = anchoredMulLipConst Lu Lu Bu Bu j`. -/
theorem lipschitzAnchored_half_sq (hu : AnchoredJetBounds u p Lu Bu U A D) (hD : IsOpen D)
    (hDc : Convex ℝ D) (hAD : A ⊆ D) {j : ℕ} (hj : j ∈ Icc 1 p) :
    IteratedFDerivLipschitzAnchored (fun y => u y ^ 2 / 2) j
      (anchoredMulLipConst Lu Lu Bu Bu j / 2 + Lu j * U) A D := by
  have hjp := (mem_Icc.1 hj).2
  have h := (IteratedFDerivLipschitzAnchored.mul hu hu hD hDc hAD hj).const_smul
    (fun y hy => (hu.contDiffAt hD hy hjp).mul (hu.contDiffAt hD hy hjp)) hAD (1 / 2)
  have hfun : (fun y => u y ^ 2 / 2) = fun y => (1 / 2 : ℝ) • (u y * u y) := by
    funext y
    rw [smul_eq_mul]
    ring
  rw [hfun]
  refine h.mono_const (le_of_eq ?_)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  ring

/-- **Half squares, bound part** ([cartis2022evaluation], (14.3.63)): for `1 ≤ j ≤ p` and
`x ∈ A`, `‖∇^j (u² / 2)(x)‖ ≤ K₂ / 2 + Bu_j U`, `K₂ = anchoredMulBoundConst Bu Bu j`. -/
theorem norm_iteratedFDeriv_half_sq_le (hu : AnchoredJetBounds u p Lu Bu U A D) (hD : IsOpen D)
    (hAD : A ⊆ D) {j : ℕ} (hj : j ∈ Icc 1 p) {x : E} (hx : x ∈ A) :
    ‖iteratedFDeriv ℝ j (fun y => u y ^ 2 / 2) x‖ ≤
      anchoredMulBoundConst Bu Bu j / 2 + Bu j * U := by
  have hjp := (mem_Icc.1 hj).2
  have hfun : (fun y => u y ^ 2 / 2) = fun y => (1 / 2 : ℝ) • (u y * u y) := by
    funext y
    rw [smul_eq_mul]
    ring
  have hc := (hu.contDiffAt hD (hAD hx) hjp).mul (hu.contDiffAt hD (hAD hx) hjp)
  rw [hfun, iteratedFDeriv_const_smul_apply' hc, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have := hu.norm_iteratedFDeriv_mul_le hu hD hAD hj hx
  linarith

/-- **Half squared norms** ([cartis2022evaluation], Lemma 14.3.6(i), (14.3.60)): if every
component `cᵢ` of `c : E → EuclideanSpace ℝ (Fin m)` satisfies `AnchoredJetBounds` with common
constants `L, B, U`, then `∇^j (½ ‖c‖²)` is anchored-Lipschitz with constant
`m (K₀ / 2 + L_j U)`, `K₀ = anchoredMulLipConst L L B B j`, for `1 ≤ j ≤ p`. -/
theorem lipschitzAnchored_half_norm_sq {m : ℕ} {c : E → EuclideanSpace ℝ (Fin m)}
    {L B : ℕ → ℝ} (hc : ∀ i, AnchoredJetBounds (fun y => c y i) p L B U A D) (hD : IsOpen D)
    (hDc : Convex ℝ D) (hAD : A ⊆ D) {j : ℕ} (hj : j ∈ Icc 1 p) :
    IteratedFDerivLipschitzAnchored (fun y => ‖c y‖ ^ 2 / 2) j
      (m * (anchoredMulLipConst L L B B j / 2 + L j * U)) A D := by
  have hjp := (mem_Icc.1 hj).2
  have hfun : (fun y => ‖c y‖ ^ 2 / 2) = fun y => ∑ i : Fin m, c y i ^ 2 / 2 := by
    funext y
    rw [EuclideanSpace.norm_sq_eq, sum_div]
    simp [Real.norm_eq_abs, sq_abs]
  rw [hfun]
  have h := IteratedFDerivLipschitzAnchored.sum (t := univ)
    (fun i _ => (hc i).lipschitzAnchored_half_sq hD hDc hAD hj)
    (fun i _ y hy => (((hc i).contDiffAt hD hy hjp).pow 2).div_const 2) hAD
  simpa [mul_add] using h

/-- **Half squared norms, bound part** ([cartis2022evaluation], (14.3.61)): under the hypotheses
of `lipschitzAnchored_half_norm_sq`, `‖∇^j (½ ‖c‖²)(x)‖ ≤ m (K₂ / 2 + B_j U)` for `x ∈ A`,
`K₂ = anchoredMulBoundConst B B j`. -/
theorem norm_iteratedFDeriv_half_norm_sq_le {m : ℕ} {c : E → EuclideanSpace ℝ (Fin m)}
    {L B : ℕ → ℝ} (hc : ∀ i, AnchoredJetBounds (fun y => c y i) p L B U A D) (hD : IsOpen D)
    (hAD : A ⊆ D) {j : ℕ} (hj : j ∈ Icc 1 p) {x : E} (hx : x ∈ A) :
    ‖iteratedFDeriv ℝ j (fun y => ‖c y‖ ^ 2 / 2) x‖ ≤
      m * (anchoredMulBoundConst B B j / 2 + B j * U) := by
  have hjp := (mem_Icc.1 hj).2
  have hfun : (fun y => ‖c y‖ ^ 2 / 2) = fun y => ∑ i : Fin m, c y i ^ 2 / 2 := by
    funext y
    rw [EuclideanSpace.norm_sq_eq, sum_div]
    simp [Real.norm_eq_abs, sq_abs]
  rw [hfun, iteratedFDeriv_fun_sum_apply fun i _ =>
    (((hc i).contDiffAt hD (hAD hx) hjp).pow 2).div_const 2]
  refine (norm_sum_le _ _).trans ?_
  have := sum_le_sum fun i (_ : i ∈ univ) => (hc i).norm_iteratedFDeriv_half_sq_le hD hAD hj hx
  simpa [mul_add] using this

end AnchoredJetBounds

end Product

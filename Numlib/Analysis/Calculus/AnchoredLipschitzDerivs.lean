import Numlib.Analysis.Calculus.AnchoredLipschitz
import Numlib.Analysis.Calculus.MultivariateTaylor.Basic

/-!
# Anchored Lipschitz continuity of the derivatives of several orders

`LipschitzDerivsAnchored f C A j₀ p L` bundles the smoothness hypothesis of the high-order
model-based methods ([cartis2022evaluation], Chapters 12–14): `C` is open and convex, the anchor
set `A` lies in `C`, `f` is `C^p` near every point of `C`, and for every order `j ∈ [j₀, p]` the
`j`-th derivative is `L j`-Lipschitz *anchored* in `A` with respect to `C`
(`IteratedFDerivLipschitzAnchored`):
`‖∇^j f(x) - ∇^j f(y)‖ ≤ L_j ‖x - y‖` for `x ∈ A`, `y ∈ C`.

The usual assumptions are instances:
* global Lipschitz derivatives on the whole space are the case `C = A = univ`
  (`LipschitzDerivsAnchored.of_contDiff`);
* Lipschitz derivatives on an open convex set `C` are the case `A = C`
  (`LipschitzDerivsAnchored.of_lipschitzOn`, `lipschitzDerivsAnchored_self_iff`);
* the assumptions anchored on a sublevel set ([cartis2022evaluation] f.D1qLaB.X, (14.2.9)) take
  for `A` a set containing `{y ∈ X | f(y) ≤ f(x₀)}`, which contains the iterates of a monotone
  method, so that the models built at the iterates are related to the trial points by Taylor's
  theorem anchored at the iterate (`LipschitzDerivsAnchored.abs_sub_taylorDecrement_le`).

The lowest order `j₀` is `1` for the conditions on the derivatives only (f.D1pL) and `0` when the
function itself is Lipschitz as well (f.D0pL).

## Main results

* monotonicity in the anchor set, the orders and the constants;
* `LipschitzDerivsAnchored.norm_iteratedFDeriv_le`: the derivative of order `j + 1` is bounded by
  `L_j` at the anchors;
* `LipschitzDerivsAnchored.abs_sub_taylorDecrement_le`: Taylor's theorem anchored at an anchor,
  `|f(x + s) - (f(x) - ΔT_{f,j}(x, s))| ≤ L_j/(j+1)! ‖s‖^{j+1}`.
-/

open Finset
open scoped Nat

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- `f` is `C^p` near every point of the open convex set `C` and, for every order `j ∈ [j₀, p]`,
its `j`-th derivative is `L j`-Lipschitz anchored in `A ⊆ C` with respect to `C`
([cartis2022evaluation], (14.2.9)). -/
structure LipschitzDerivsAnchored (f : E → F) (C A : Set E) (j₀ p : ℕ) (L : ℕ → ℝ) : Prop where
  /-- `C` is open. -/
  isOpen : IsOpen C
  /-- `C` is convex. -/
  convex : Convex ℝ C
  /-- The anchors lie in `C`. -/
  subset : A ⊆ C
  /-- `f` is `C^p` near every point of `C`. -/
  contDiffAt : ∀ y ∈ C, ContDiffAt ℝ p f y
  /-- The `j`-th derivative is `L j`-Lipschitz anchored in `A` with respect to `C`. -/
  lipschitzAnchored : ∀ j ∈ Icc j₀ p, IteratedFDerivLipschitzAnchored f j (L j) A C

namespace LipschitzDerivsAnchored

variable {f : E → F} {C A A' : Set E} {j₀ p : ℕ} {L L' : ℕ → ℝ}

/-- Lipschitz derivatives on an open convex set `C` are anchored at every `A ⊆ C`. -/
theorem of_lipschitzOn (hC : IsOpen C) (hCc : Convex ℝ C) (hA : A ⊆ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y)
    (hL : ∀ j ∈ Icc j₀ p, IteratedFDerivLipschitzOn f j (L j) C) :
    LipschitzDerivsAnchored f C A j₀ p L :=
  ⟨hC, hCc, hA, hf, fun j hj => (hL j hj).anchored hA⟩

/-- Globally Lipschitz derivatives of a `C^p` function are anchored at every set, with
`C = univ`. -/
theorem of_contDiff (hf : ContDiff ℝ p f)
    (hL : ∀ j ∈ Icc j₀ p, IteratedFDerivLipschitzOn f j (L j) Set.univ) (A : Set E) :
    LipschitzDerivsAnchored f Set.univ A j₀ p L :=
  of_lipschitzOn isOpen_univ convex_univ (Set.subset_univ A) (fun _ _ => hf.contDiffAt) hL

/-- With `A = C`, the anchored condition is the Lipschitz condition on `C`. -/
theorem lipschitzOn (h : LipschitzDerivsAnchored f C C j₀ p L) {j : ℕ} (hj : j ∈ Icc j₀ p) :
    IteratedFDerivLipschitzOn f j (L j) C :=
  iteratedFDerivLipschitzAnchored_self_iff.1 (h.lipschitzAnchored j hj)

/-- The zero function has anchored Lipschitz derivatives of all orders, with constants `0`. -/
theorem zero_fun (hC : IsOpen C) (hCc : Convex ℝ C) (hA : A ⊆ C) :
    LipschitzDerivsAnchored (0 : E → F) C A j₀ p (fun _ => 0) :=
  of_lipschitzOn hC hCc hA (fun _ _ => contDiffAt_const) fun j _ =>
    iteratedFDerivLipschitzOn_iff.2 fun x _ y _ => by
      have h0 : iteratedFDeriv ℝ j (0 : E → F) = 0 := iteratedFDeriv_fun_zero
      simp [h0]

/-- Shrinking the anchor set. -/
theorem mono_left (h : LipschitzDerivsAnchored f C A j₀ p L) (hA : A' ⊆ A) :
    LipschitzDerivsAnchored f C A' j₀ p L :=
  ⟨h.isOpen, h.convex, hA.trans h.subset, h.contDiffAt,
    fun j hj => (h.lipschitzAnchored j hj).mono_left hA⟩

/-- Restricting the orders to `[j₁, q] ⊆ [j₀, p]`. -/
theorem mono {j₁ q : ℕ} (h : LipschitzDerivsAnchored f C A j₀ p L) (hj : j₀ ≤ j₁) (hq : q ≤ p) :
    LipschitzDerivsAnchored f C A j₁ q L :=
  ⟨h.isOpen, h.convex, h.subset, fun y hy => (h.contDiffAt y hy).of_le (by exact_mod_cast hq),
    fun j hj' => h.lipschitzAnchored j (Icc_subset_Icc hj hq hj')⟩

/-- Increasing the constants. -/
theorem mono_const (h : LipschitzDerivsAnchored f C A j₀ p L)
    (hL : ∀ j ∈ Icc j₀ p, L j ≤ L' j) : LipschitzDerivsAnchored f C A j₀ p L' :=
  ⟨h.isOpen, h.convex, h.subset, h.contDiffAt,
    fun j hj => (h.lipschitzAnchored j hj).mono_const (hL j hj)⟩

/-- Only the orders `[j₀, p]` of the constants matter. -/
theorem congr_const (h : LipschitzDerivsAnchored f C A j₀ p L)
    (hL : ∀ j ∈ Icc j₀ p, L j = L' j) : LipschitzDerivsAnchored f C A j₀ p L' :=
  h.mono_const fun j hj => (hL j hj).le

/-- `f` is `C^j` near every point of `C` for `j ≤ p`. -/
theorem contDiffAt_of_le (h : LipschitzDerivsAnchored f C A j₀ p L) {j : ℕ} (hj : j ≤ p) {y : E}
    (hy : y ∈ C) : ContDiffAt ℝ j f y :=
  (h.contDiffAt y hy).of_le (by exact_mod_cast hj)

/-- The anchored condition at an anchor `x ∈ A`:
`‖∇^j f(y) - ∇^j f(x)‖ ≤ L_j ‖y - x‖` for `y ∈ C`. -/
theorem lipschitzAt (h : LipschitzDerivsAnchored f C A j₀ p L) {j : ℕ} (hj : j ∈ Icc j₀ p)
    {x : E} (hx : x ∈ A) :
    ∀ y ∈ C, ‖iteratedFDeriv ℝ j f y - iteratedFDeriv ℝ j f x‖ ≤ L j * ‖y - x‖ :=
  (h.lipschitzAnchored j hj).lipschitzAt hx

/-- At an anchor, the derivative of order `j + 1` is bounded by the anchored Lipschitz constant
of the derivative of order `j` ([cartis2022evaluation], Theorem A.8.5): `‖∇^{j+1} f(x)‖ ≤ L_j`. -/
theorem norm_iteratedFDeriv_le (h : LipschitzDerivsAnchored f C A j₀ p L) {j : ℕ}
    (hj : j ∈ Icc j₀ p) (hL : 0 ≤ L j) {x : E} (hx : x ∈ A) :
    ‖iteratedFDeriv ℝ (j + 1) f x‖ ≤ L j := by
  rw [← norm_fderiv_iteratedFDeriv]
  refine norm_fderiv_le_of_lip' ℝ hL ?_
  filter_upwards [h.isOpen.mem_nhds (h.subset hx)] with y hy
  exact h.lipschitzAt hj hx y hy

end LipschitzDerivsAnchored

/-- With `A = C`, the anchored condition is the Lipschitz condition on the open convex set `C`. -/
theorem lipschitzDerivsAnchored_self_iff {f : E → F} {C : Set E} {j₀ p : ℕ} {L : ℕ → ℝ} :
    LipschitzDerivsAnchored f C C j₀ p L ↔ IsOpen C ∧ Convex ℝ C ∧
      (∀ y ∈ C, ContDiffAt ℝ p f y) ∧ ∀ j ∈ Icc j₀ p, IteratedFDerivLipschitzOn f j (L j) C :=
  ⟨fun h => ⟨h.isOpen, h.convex, h.contDiffAt, fun _ hj => h.lipschitzOn hj⟩,
    fun ⟨hC, hCc, hf, hL⟩ => .of_lipschitzOn hC hCc Set.Subset.rfl hf hL⟩

namespace LipschitzDerivsAnchored

variable {f : E → ℝ} {C A : Set E} {j₀ p : ℕ} {L : ℕ → ℝ}

/-- **Taylor's theorem anchored at an anchor** ([cartis2022evaluation], (A.19) with (14.2.9)): for
`x ∈ A`, `x + s ∈ C` and `j ∈ [j₀, p]`,
`|f(x + s) - (f(x) - ΔT_{f,j}(x, s))| ≤ L_j/(j+1)! ‖s‖^{j+1}`. -/
theorem abs_sub_taylorDecrement_le (h : LipschitzDerivsAnchored f C A j₀ p L) {j : ℕ}
    (hj : j ∈ Icc j₀ p) {x s : E} (hx : x ∈ A) (hxs : x + s ∈ C) :
    |f (x + s) - (f x - (ftaylorSeries ℝ f x).taylorDecrement j s)| ≤
      L j / ((j + 1)! : ℝ) * ‖s‖ ^ (j + 1) := by
  rw [ftaylorSeries_taylorDecrement_eq, sub_sub_cancel, ← Real.norm_eq_abs]
  exact norm_sub_taylorPolynomial_le_of_lipschitzAnchored h.convex
    (fun y hy => h.contDiffAt_of_le (Finset.mem_Icc.1 hj).2 hy) (h.lipschitzAt hj hx)
    (h.subset hx) hxs

end LipschitzDerivsAnchored

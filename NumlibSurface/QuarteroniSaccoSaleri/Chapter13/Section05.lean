import Numlib.Analysis.PDE.Transport

/-!
# Quarteroni–Sacco–Saleri §13.5: a scalar transport problem

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §13.5.

The Cauchy problem (13.26) `u_t + a u_x = 0`, `u(·, 0) = u₀` on `ℝ × [0, ∞)` is solved by the
travelling wave `u(x, t) = u₀(x - a t)`, and that is its only solution. The reason is the
*characteristic curves* (13.27), the integral curves `x' = a` of the speed field: a solution is
constant along them, because `du/dt = u_t + u_x x' = 0` there. For the general problem (13.28)
`u_t + a u_x + a₀ u = f` with coefficients depending on `(x, t)` the same chain rule gives the
ordinary differential equation `du/dt = f - a₀ u` along a characteristic.

Example 13.3 is the Burgers equation (13.29) with the piecewise linear datum `burgersDatum`: the
characteristic issuing from `(x₀, 0)` is the line `x₀ + t u₀(x₀)`, and those lines are pairwise
disjoint exactly while `t < 1`.

The backbone home of all of this is `Numlib/Analysis/PDE/Transport`: the restatements here are
specializations of `Transport.IsSolution`, `Transport.IsCharacteristic` and their theorems.
Inflow points and weak solutions are prose in the book and are not formalized.
-/

open Set

namespace QuarteroniSaccoSaleri.Chapter13

/-! ### The Cauchy problem (13.26) -/

/-- **(13.26)**: `u` is a classical solution of `u_t + a u_x = 0` on `ℝ × [0, ∞)` with the datum
`u₀`. This is `Transport.IsSolution` with the constant speed `a` and no zero-order term or
source. -/
def equation_13_26 (a : ℝ) (u₀ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  Transport.IsSolution (fun _ _ => a) 0 0 u₀ u

/-- **The solution of (13.26) is the travelling wave** `u(x, t) = u₀(x - a t)`, and it is the only
one (Quarteroni–Sacco–Saleri, *Numerical Mathematics*, §13.5). -/
theorem equation_13_26_solution {a : ℝ} {u₀ : ℝ → ℝ} (hu₀ : Differentiable ℝ u₀) :
    equation_13_26 a u₀ (fun x t => u₀ (x - a * t)) ∧
      ∀ u : ℝ → ℝ → ℝ, equation_13_26 a u₀ u → ∀ (x t : ℝ), 0 ≤ t → u x t = u₀ (x - a * t) :=
  ⟨Transport.isSolution_comp_sub hu₀, fun _ hu x _ ht => hu.eq_comp_sub x ht⟩

/-! ### The characteristic curves (13.27) -/

/-- **(13.27)**: `x` is the characteristic curve of the speed field `a` through `x₀`, the solution
of `x'(t) = a(x(t), t)` on `[0, ∞)` with `x(0) = x₀`. -/
def equation_13_27 (a : ℝ → ℝ → ℝ) (x₀ : ℝ) (x : ℝ → ℝ) : Prop :=
  Transport.IsCharacteristic a x₀ x

/-- **The characteristics of a constant speed are the straight lines** `x(t) = x₀ + a t`, and
those are the only ones (Quarteroni–Sacco–Saleri, *Numerical Mathematics*, §13.5). -/
theorem equation_13_27_line (a x₀ : ℝ) :
    equation_13_27 (fun _ _ => a) x₀ (fun t => x₀ + a * t) ∧
      ∀ x : ℝ → ℝ, equation_13_27 (fun _ _ => a) x₀ x → ∀ t : ℝ, 0 ≤ t → x t = x₀ + a * t :=
  ⟨Transport.characteristic_const a x₀, fun _ hx _ ht => hx.eq_of_const ht⟩

/-- **The solution of (13.26) is constant along the characteristics**, `du/dt = 0` on
`(x(t), t)`: `u(x₀ + a t, t) = u₀(x₀)` (Quarteroni–Sacco–Saleri, *Numerical Mathematics*,
§13.5). -/
theorem equation_13_27_const_along {a : ℝ} {u₀ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hu : equation_13_26 a u₀ u) (x₀ : ℝ) {t : ℝ} (ht : 0 ≤ t) : u (x₀ + a * t) t = u₀ x₀ :=
  hu.comp_characteristic_const (Transport.characteristic_const a x₀) ht

/-- **(13.28)**: for the general transport problem `u_t + a u_x + a₀ u = f` with coefficients
depending on `(x, t)`, a solution satisfies `du/dt = f - a₀ u` along a characteristic
(Quarteroni–Sacco–Saleri, *Numerical Mathematics*, equation (13.28)). -/
theorem equation_13_28 {a a₀ f : ℝ → ℝ → ℝ} {u₀ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hu : Transport.IsSolution a a₀ f u₀ u) {x₀ : ℝ} {x : ℝ → ℝ}
    (hx : equation_13_27 a x₀ x) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => u (x s) s) (f (x t) t - a₀ (x t) t * u (x t) t) (Ici 0) t :=
  hu.hasDerivAt_comp_characteristic hx ht

/-! ### Example 13.3, the Burgers equation -/

/-- **The initial datum of Example 13.3**: `1` for `x ≤ 0`, `1 - x` on `[0, 1]`, `0` for
`x ≥ 1`. -/
noncomputable def burgersDatum (x : ℝ) : ℝ := if x ≤ 0 then 1 else if x ≤ 1 then 1 - x else 0

/-- The datum of Example 13.3 is nonincreasing and `1`-Lipschitz. -/
theorem burgersDatum_sub_le {x y : ℝ} (hxy : x ≤ y) :
    0 ≤ burgersDatum x - burgersDatum y ∧ burgersDatum x - burgersDatum y ≤ y - x := by
  unfold burgersDatum
  split_ifs <;> constructor <;> linarith

/-- **Example 13.3** (the Burgers equation (13.29)): the characteristic issuing from `(x₀, 0)` is
the straight line `x(t) = x₀ + t u₀(x₀)`, since the solution is constant along it; and the map
`x₀ ↦ x₀ + t u₀(x₀)` carrying the feet to the grid at time `t` is injective exactly while
`t < 1` — at `t = 1` the characteristics from `x₀ = 0` and `x₀ = 1` meet. -/
theorem example_13_3 :
    (∀ x₀ : ℝ, equation_13_27 (fun _ _ => burgersDatum x₀) x₀
        (fun t => x₀ + burgersDatum x₀ * t)) ∧
      (∀ t : ℝ, 0 ≤ t → t < 1 → Function.Injective fun x₀ : ℝ => x₀ + t * burgersDatum x₀) ∧
      ∀ t : ℝ, 1 ≤ t → ¬Function.Injective fun x₀ : ℝ => x₀ + t * burgersDatum x₀ := by
  refine ⟨fun x₀ => Transport.characteristic_const _ x₀, fun t ht0 ht1 => ?_, fun t ht => ?_⟩
  · refine StrictMono.injective fun x y hxy => ?_
    obtain ⟨h1, h2⟩ := burgersDatum_sub_le hxy.le
    nlinarith [mul_le_mul_of_nonneg_left h2 ht0]
  · intro h
    have h0 : burgersDatum 0 = 1 := by unfold burgersDatum; norm_num
    have ht0 : burgersDatum t = 0 := by
      unfold burgersDatum
      split_ifs with h2 h3
      · linarith
      · linarith
      · rfl
    have := h (a₁ := (0 : ℝ)) (a₂ := t) (by simp [h0, ht0])
    linarith

end QuarteroniSaccoSaleri.Chapter13

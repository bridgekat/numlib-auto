/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The full multigrid error bound

Full multigrid sweeps once through a hierarchy of grids, from the coarsest level upwards. On each
level, it takes as initial guess the interpolant of the approximation from the previous level, and
it applies $\mu$ cycles of the multigrid iteration ([saad2003iterative], §13.4.4). Let $u_l$ be the
exact discrete solution and $\tilde u_l$ the full multigrid approximation on level $l$, with mesh
size $h_l$. Suppose that the interpolation is accurate to the discretization order $\kappa$ with the
constant $c_1$, that the cycle contracts the error by a uniform factor $\xi^\mu$, that the
interpolation operators have norm at most $c_2 2^{-\kappa}$, and that $c_2 \xi^\mu < 1$. Then the
full multigrid approximation is accurate to the discretization order on every level:
$$\|u_l - \tilde u_l\| \le \frac{\xi^\mu}{1 - c_2 \xi^\mu}\, c_1 h_l^\kappa.$$
This is Theorem 13.2 of [saad2003iterative].

## Main results

* `Multigrid.le_of_rec_of_half`: a real sequence with $a_0 = 0$ and $a_{l+1} \le \xi^\mu (c_1
  h_{l+1}^\kappa + c_2 2^{-\kappa} a_l)$ for halving $h_l$ satisfies $a_l \le c_3 c_1 h_l^\kappa$
  with $c_3 = \xi^\mu / (1 - c_2 \xi^\mu)$.
* `Multigrid.norm_sub_fullMultigrid_le`: the full multigrid error bound on a family of normed
  spaces, one per level.

## Proof outline

The proof uses no analysis. With $a_l = \|u_l - \tilde u_l\|$, the hypotheses give the scalar
recursion $a_{l+1} \le \xi^\mu (c_1 h_{l+1}^\kappa + c_2 2^{-\kappa} a_l)$ with $h_{l+1} = h_l / 2$
and $a_0 = 0$. Induction on $l$ gives $a_l \le c_3 c_1 h_l^\kappa$.

## Implementation notes

* The scalar recursion `Multigrid.le_of_rec_of_half` is stated in $\mathbb{R}$ alone, so that other
  analyses of nested iterations can use it. The normed-space form
  `Multigrid.norm_sub_fullMultigrid_le` is the theorem itself.
* The order of accuracy $\kappa$ is a real exponent (`Real.rpow`), since it need not be an integer.
* The hypotheses are not verified here for any concrete discretization, and they cannot be: the
  accuracy of the interpolation is a statement about the solution of a differential equation, not
  about linear algebra. They are named and assumed, in the same way as the smoothing and
  approximation properties of `Numlib.Multigrid.TwoGrid`.
-/

namespace Multigrid

/-! ### The scalar recursion -/

/-- Let $(a_l)$ and $(h_l)$ be real sequences, let $c_1, c_2, \xi, \kappa \in \mathbb{R}$, and let
$\mu \in \mathbb{N}$. Suppose that $h_l > 0$ and $h_{l+1} = h_l / 2$ for all $l$, that
$a_0 = 0$, that $c_1, c_2, \xi \ge 0$ and $c_2 \xi^\mu < 1$, and that for all $l$
$$a_{l+1} \le \xi^\mu \bigl(c_1 h_{l+1}^\kappa + c_2 2^{-\kappa} a_l\bigr).$$
Then for every level $l$,
$$a_l \le \frac{\xi^\mu}{1 - c_2 \xi^\mu}\, c_1 h_l^\kappa.$$

This is the recursion behind the full multigrid bound of Theorem 13.2 of [saad2003iterative]:
the sequence stays accurate to the order $\kappa$ of the mesh size, with a constant that does
not depend on the level. The powers $h_l^\kappa$ and $2^{-\kappa}$ are `Real.rpow`. -/
theorem le_of_rec_of_half {a h : ℕ → ℝ} {c₁ c₂ ξ κ : ℝ} {μ : ℕ}
    (hh : ∀ l, h (l + 1) = h l / 2) (hhpos : ∀ l, 0 < h l) (ha0 : a 0 = 0) (hc₁ : 0 ≤ c₁)
    (hc₂ : 0 ≤ c₂) (hξ : 0 ≤ ξ) (hlt : c₂ * ξ ^ μ < 1)
    (hrec : ∀ l, a (l + 1) ≤ ξ ^ μ * (c₁ * h (l + 1) ^ κ + c₂ * (2 : ℝ) ^ (-κ) * a l)) (l : ℕ) :
    a l ≤ ξ ^ μ / (1 - c₂ * ξ ^ μ) * c₁ * h l ^ κ := by
  have ht : (0 : ℝ) ≤ ξ ^ μ := pow_nonneg hξ μ
  have hden : (0 : ℝ) < 1 - c₂ * ξ ^ μ := by linarith
  have hne : (1 : ℝ) - c₂ * ξ ^ μ ≠ 0 := ne_of_gt hden
  have hkey : ξ ^ μ * (1 + c₂ * (ξ ^ μ / (1 - c₂ * ξ ^ μ))) = ξ ^ μ / (1 - c₂ * ξ ^ μ) := by
    have hinv : (1 - c₂ * ξ ^ μ) * (1 - c₂ * ξ ^ μ)⁻¹ = 1 := mul_inv_cancel₀ hne
    rw [div_eq_mul_inv]
    linear_combination (-(ξ ^ μ)) * hinv
  have hpow : ∀ l, h (l + 1) ^ κ = (2 : ℝ) ^ (-κ) * h l ^ κ := fun l => by
    rw [hh l, Real.div_rpow (hhpos l).le (by norm_num), Real.rpow_neg (by norm_num)]
    ring
  induction l with
  | zero =>
    rw [ha0]
    have : (0 : ℝ) < h 0 ^ κ := Real.rpow_pos_of_pos (hhpos 0) κ
    positivity
  | succ l ih =>
    have hstep : c₂ * (2 : ℝ) ^ (-κ) * a l
        ≤ c₂ * (ξ ^ μ / (1 - c₂ * ξ ^ μ)) * c₁ * h (l + 1) ^ κ := by
      have h2 : (0 : ℝ) ≤ c₂ * (2 : ℝ) ^ (-κ) := by positivity
      calc c₂ * (2 : ℝ) ^ (-κ) * a l
          ≤ c₂ * (2 : ℝ) ^ (-κ) * (ξ ^ μ / (1 - c₂ * ξ ^ μ) * c₁ * h l ^ κ) :=
            mul_le_mul_of_nonneg_left ih h2
        _ = c₂ * (ξ ^ μ / (1 - c₂ * ξ ^ μ)) * c₁ * ((2 : ℝ) ^ (-κ) * h l ^ κ) := by ring
        _ = c₂ * (ξ ^ μ / (1 - c₂ * ξ ^ μ)) * c₁ * h (l + 1) ^ κ := by rw [hpow l]
    calc a (l + 1)
        ≤ ξ ^ μ * (c₁ * h (l + 1) ^ κ + c₂ * (2 : ℝ) ^ (-κ) * a l) := hrec l
      _ ≤ ξ ^ μ * (c₁ * h (l + 1) ^ κ
            + c₂ * (ξ ^ μ / (1 - c₂ * ξ ^ μ)) * c₁ * h (l + 1) ^ κ) :=
          mul_le_mul_of_nonneg_left (by linarith) ht
      _ = ξ ^ μ * (1 + c₂ * (ξ ^ μ / (1 - c₂ * ξ ^ μ))) * c₁ * h (l + 1) ^ κ := by ring
      _ = ξ ^ μ / (1 - c₂ * ξ ^ μ) * c₁ * h (l + 1) ^ κ := by rw [hkey]

/-! ### The full multigrid bound -/

/-- Let $(E_l)_{l \in \mathbb{N}}$ be real normed spaces, one per level, with continuous linear
interpolations $I_l \colon E_l \to E_{l+1}$. Let $u_l, \tilde u_l \in E_l$, let $(h_l)$ be mesh
sizes with $h_l > 0$ and $h_{l+1} = h_l / 2$, let $c_1, c_2, \xi, \kappa \in \mathbb{R}$ with
$c_1, \xi \ge 0$, and let $\mu \in \mathbb{N}$. Suppose that:

* the coarsest problem is solved exactly, $\tilde u_0 = u_0$;
* the interpolation is accurate to the discretization order,
  $\|u_{l+1} - I_l u_l\| \le c_1 h_{l+1}^\kappa$ for all $l$;
* the $\mu$ cycles on level $l + 1$ contract the error by $\xi^\mu$, $\|u_{l+1} - \tilde
  u_{l+1}\| \le \xi^\mu \|u_{l+1} - I_l \tilde u_l\|$ for all $l$;
* the interpolations are bounded, $\|I_l\| \le c_2 2^{-\kappa}$ for all $l$.

If moreover $c_2 \xi^\mu < 1$, then the full multigrid approximation is accurate to the
discretization order on every level:
$$\|u_l - \tilde u_l\| \le \frac{\xi^\mu}{1 - c_2 \xi^\mu}\, c_1 h_l^\kappa.$$

This is Theorem 13.2 of [saad2003iterative], the full multigrid error bound. The exact solutions
are `u`, the approximations are `utilde`, and the interpolations are `interp`. The proof
specializes `Multigrid.le_of_rec_of_half` to $a_l = \|u_l - \tilde u_l\|$. -/
theorem norm_sub_fullMultigrid_le {E : ℕ → Type*} [∀ l, NormedAddCommGroup (E l)]
    [∀ l, NormedSpace ℝ (E l)] {u utilde : ∀ l, E l} {interp : ∀ l, E l →L[ℝ] E (l + 1)}
    {h : ℕ → ℝ} {c₁ c₂ ξ κ : ℝ} {μ : ℕ} (hh : ∀ l, h (l + 1) = h l / 2) (hhpos : ∀ l, 0 < h l)
    (hexact : utilde 0 = u 0) (hc₁ : 0 ≤ c₁) (hξ : 0 ≤ ξ) (hlt : c₂ * ξ ^ μ < 1)
    (hinterp : ∀ l, ‖u (l + 1) - interp l (u l)‖ ≤ c₁ * h (l + 1) ^ κ)
    (hcycle : ∀ l, ‖u (l + 1) - utilde (l + 1)‖ ≤ ξ ^ μ * ‖u (l + 1) - interp l (utilde l)‖)
    (hnorm : ∀ l, ‖interp l‖ ≤ c₂ * (2 : ℝ) ^ (-κ)) (l : ℕ) :
    ‖u l - utilde l‖ ≤ ξ ^ μ / (1 - c₂ * ξ ^ μ) * c₁ * h l ^ κ := by
  have hhalf : (0 : ℝ) < (2 : ℝ) ^ (-κ) := Real.rpow_pos_of_pos (by norm_num) _
  have hc₂ : 0 ≤ c₂ := by
    have h0 := (norm_nonneg (interp 0)).trans (hnorm 0)
    nlinarith
  have ht : (0 : ℝ) ≤ ξ ^ μ := pow_nonneg hξ μ
  refine le_of_rec_of_half (a := fun l => ‖u l - utilde l‖) hh hhpos (by simp [hexact]) hc₁ hc₂
    hξ hlt (fun l => ?_) l
  have hsplit : ‖u (l + 1) - interp l (utilde l)‖
      ≤ c₁ * h (l + 1) ^ κ + c₂ * (2 : ℝ) ^ (-κ) * ‖u l - utilde l‖ := by
    have htri : ‖u (l + 1) - interp l (utilde l)‖
        ≤ ‖u (l + 1) - interp l (u l)‖ + ‖interp l (u l) - interp l (utilde l)‖ := by
      have harg : u (l + 1) - interp l (utilde l)
          = (u (l + 1) - interp l (u l)) + (interp l (u l) - interp l (utilde l)) := by abel
      rw [harg]
      exact norm_add_le _ _
    have hop : ‖interp l (u l) - interp l (utilde l)‖
        ≤ c₂ * (2 : ℝ) ^ (-κ) * ‖u l - utilde l‖ := by
      rw [← map_sub]
      exact ((interp l).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hnorm l) (norm_nonneg _))
    linarith [hinterp l]
  exact (hcycle l).trans (mul_le_mul_of_nonneg_left hsplit ht)

end Multigrid

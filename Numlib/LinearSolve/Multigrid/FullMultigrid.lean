import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The full multigrid error bound

Full multigrid sweeps once from the coarsest level upwards, taking as initial guess on each level
the interpolant of the previous level's approximation and applying `μ` cycles of the multigrid
iteration.  If the interpolation is accurate to the discretization order, the cycle is uniformly
contractive, and the interpolation operators are bounded by `c₂ 2^{-κ}`, then the full multigrid
approximation is accurate to the discretization order on *every* level.

There is no analysis in the proof.  Its whole content is a scalar recursion:
`a_{l+1} ≤ ξ^μ (c₁ h_{l+1}^κ + c₂ 2^{-κ} a_l)` with `h_{l+1} = h_l / 2` and `a_0 = 0` implies
`a_l ≤ c₃ c₁ h_l^κ` with `c₃ = ξ^μ / (1 - c₂ ξ^μ)`.  That recursion is
`Multigrid.le_of_rec_of_half`, stated in `ℝ` alone, and the statement over a family of normed
spaces — one per level, with continuous linear interpolations between consecutive levels — is
`Multigrid.norm_sub_fullMultigrid_le`.  Both are worth having: the scalar lemma is what any other
nested-iteration analysis reuses, and the normed-space form is the theorem itself.

The order of accuracy `κ` is a real exponent (`Real.rpow`), since it need not be an integer.

The hypotheses are *not* verified here for any concrete discretization, and cannot be: the
accuracy of the interpolation is a statement about the solution of a differential equation, not
about linear algebra.  They are named and assumed, following the convention of the rest of the
multigrid development.

## References

[^saad-iterative]: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
  SIAM, 2003, §13.4.4.  The theorem is his Theorem 13.2 and the three hypotheses are his
  (13.49)–(13.51).
-/

namespace Multigrid

/-! ### The scalar recursion -/

/-- **The recursion behind the full multigrid bound**: if `h` halves at every step, `a 0 = 0` and
`a_{l+1} ≤ ξ^μ (c₁ h_{l+1}^κ + c₂ 2^{-κ} a_l)`, with `c₂ ξ^μ < 1`, then
`a_l ≤ ξ^μ/(1 - c₂ ξ^μ) c₁ h_l^κ` on every level: the sequence stays accurate to the order `κ`
of the mesh size, with a constant independent of the level. -/
theorem le_of_rec_of_half {a h : ℕ → ℝ} {c₁ c₂ ξ κ : ℝ} {μ : ℕ}
    (hh : ∀ l, h (l + 1) = h l / 2) (hhpos : ∀ l, 0 < h l) (ha0 : a 0 = 0) (hc₁ : 0 ≤ c₁)
    (hc₂ : 0 ≤ c₂) (hξ : 0 ≤ ξ) (hlt : c₂ * ξ ^ μ < 1)
    (hrec : ∀ l, a (l + 1) ≤ ξ ^ μ * (c₁ * h (l + 1) ^ κ + c₂ * (2 : ℝ) ^ (-κ) * a l)) (l : ℕ) :
    a l ≤ ξ ^ μ / (1 - c₂ * ξ ^ μ) * c₁ * h l ^ κ := by
  have ht : (0 : ℝ) ≤ ξ ^ μ := pow_nonneg hξ μ
  have hden : (0 : ℝ) < 1 - c₂ * ξ ^ μ := by linarith
  have hc₃ : (0 : ℝ) ≤ ξ ^ μ / (1 - c₂ * ξ ^ μ) := div_nonneg ht hden.le
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
    have hpos : (0 : ℝ) < h (l + 1) ^ κ := Real.rpow_pos_of_pos (hhpos (l + 1)) κ
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

/-- **Saad's Theorem 13.2**, the full multigrid error bound.  On a hierarchy of levels — one
normed space `E l` per level, with a continuous linear interpolation `I l : E l →L[ℝ] E (l+1)` and
mesh sizes `h l` that halve — suppose that

* the coarsest problem is solved exactly, `ũ 0 = u 0`;
* the interpolation is accurate to the discretization order,
  `‖u (l+1) - I l (u l)‖ ≤ c₁ h_{l+1}^κ`;
* the `μ` cycles applied on level `l+1` contract the error by `ξ^μ`,
  `‖u (l+1) - ũ (l+1)‖ ≤ ξ^μ ‖u (l+1) - I l (ũ l)‖`;
* the interpolations are bounded, `‖I l‖ ≤ c₂ 2^{-κ}`.

If moreover `c₂ ξ^μ < 1`, then the full multigrid approximation is accurate to the discretization
order on every level, `‖u l - ũ l‖ ≤ (ξ^μ/(1 - c₂ ξ^μ)) c₁ h_l^κ`. -/
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

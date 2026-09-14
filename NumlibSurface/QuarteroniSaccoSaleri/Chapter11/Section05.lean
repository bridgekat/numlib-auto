import Numlib.ODE.Multistep
import NumlibSurface.QuarteroniSaccoSaleri.Chapter11.Section02
import NumlibSurface.QuarteroniSaccoSaleri.Chapter11.Section04

/-!
# Quarteroni–Sacco–Saleri §11.5: multistep methods

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §11.5.

Definition 11.7 (`q`-step methods), the midpoint method (11.43) and the Simpson method (11.44),
the linear multistep method (11.45) and its reformulation (11.46) as a linear difference equation
(11.28), the local truncation error (Definition 11.8, (11.47)) and the global one `τ(h)`,
consistency and order (Definition 11.9), the linear operator `L` (11.48) with the principal local
truncation error and the error constant, the Adams methods (11.49) — Adams–Bashforth (11.50) and
Adams–Moulton (11.51) with their orders — Table 11.1 of error constants, and the backward
differentiation formulae of Table 11.2 (§11.5.2).

Everything is the scalar case `E = ℝ` of `Numlib/ODE/Multistep`; the surface states the book and
delegates.

## Main definitions

* `definition_11_7 M q` — `M` is a `q`-step method.
* `equation_11_43`, `equation_11_44` — the midpoint and Simpson methods.
* `equation_11_45 M f h t₀ u` — `u` is a sequence produced by the method `M`.
* `definition_11_8 M h y t₀ n`, `definition_11_8_global M t₀ T y h` — `τ_{n+1}(h)` and `τ(h)`.
* `definition_11_9 M t₀ T y`, `definition_11_9_method M`, `definition_11_9_order M t₀ T y q`,
  `definition_11_9_order_method M q` — consistency and order, along a solution and as properties
  of the method.
* `equation_11_48 M h w t`, `errorConstant M q` — the operator `L` and the error constant.
* `equation_11_49 M` — `M` is an Adams method (`a = (1, 0, …, 0)`).
* `bdf k` — the BDF methods of Table 11.2.

## Main results

* `equation_11_46` — the difference-equation form of (11.45).
* `equation_11_48_principal` — the principal local truncation error `C_{q+1} h^{q+1} y^{(q+1)}`.
* `equation_11_50`, `adamsBashforth_order`, `equation_11_51`, `adamsMoulton_order`,
  `adamsErrorConstants` — the Adams families.
* `bdf_order` — the BDF methods have order `p + 1`.

## Conventions

A method is `M : ODE.LinearMultistep`, the coefficients `a_j = M.a j`, `b_j = M.b j`
(`j = 0, …, p`) and `b_{-1} = M.bm1`; `M` has `M.p + 1` steps. The `q`-step Adams–Moulton method
of the book's index `p = q - 1` is `ODE.LinearMultistep.adamsMoulton q`. Sequences are indexed by
`ℕ`, and the recursion (11.45) is imposed for every `n ≥ p`.
-/

open Set Filter Topology Asymptotics ODE
open Finset (range)

namespace QuarteroniSaccoSaleri.Chapter11

variable {f : ℝ → ℝ → ℝ} {t₀ T h t : ℝ} {y : ℝ → ℝ} {n : ℕ}

/-! ### Definition 11.7 and the two classical two-step methods -/

/-- **Definition 11.7 (`q`-step methods)**: a numerical method for the Cauchy problem is a
`q`-step method (`q ≥ 1`) if, for `n ≥ q - 1`, `u_{n+1}` depends on `u_{n+1-q}` but not on the
values `u_k` with `k < n + 1 - q`. For a linear multistep method `M` this is `M.p + 1 = q` with
the normalization `a_p ≠ 0 ∨ b_p ≠ 0` (`ODE.LinearMultistep.IsGenuine`). -/
def definition_11_7 (M : LinearMultistep) (q : ℕ) : Prop :=
  M.p + 1 = q ∧ M.IsGenuine

/-- Definition 11.7, unfolded. -/
theorem definition_11_7_iff (M : LinearMultistep) (q : ℕ) :
    definition_11_7 M q ↔
      M.p + 1 = q ∧ (M.a (Fin.last M.p) ≠ 0 ∨ M.b (Fin.last M.p) ≠ 0) :=
  Iff.rfl

/-- The one-step methods of §11.2 are the case `q = 1` (`ODE.LinearMultistep.ofOneStep`): the
method `u_{n+1} = a₀ u_n + h (b₀ f_n + b_{-1} f_{n+1})` is a one-step method iff `a₀ ≠ 0` or
`b₀ ≠ 0`. -/
theorem definition_11_7_ofOneStep (a₀ b₀ bm1 : ℝ) :
    definition_11_7 (LinearMultistep.ofOneStep a₀ b₀ bm1) 1 ↔ a₀ ≠ 0 ∨ b₀ ≠ 0 := by
  simp [definition_11_7, LinearMultistep.IsGenuine, LinearMultistep.ofOneStep]

/-- **The midpoint method (11.43)**: `u_{n+1} = u_{n-1} + 2h f_n`, `n ≥ 1`;
`ODE.LinearMultistep.midpoint`. -/
noncomputable def equation_11_43 : LinearMultistep := LinearMultistep.midpoint

/-- (11.43), unfolded: `u_{n+2} = u_n + 2h f(t_{n+1}, u_{n+1})` for every `n`. -/
theorem equation_11_43_isOrbit_iff (u : ℕ → ℝ) :
    equation_11_43.IsOrbit f h t₀ u ↔
      ∀ n, u (n + 2) = u n + 2 * h * f (grid t₀ h (n + 1)) (u (n + 1)) := by
  rw [equation_11_43, LinearMultistep.isOrbit_midpoint_iff]
  simp only [smul_eq_mul, grid]

/-- The midpoint method is an explicit two-step method. -/
theorem equation_11_43_twoStep :
    definition_11_7 equation_11_43 2 ∧ ¬ equation_11_43.IsImplicit := by
  refine ⟨⟨rfl, Or.inl ?_⟩, ?_⟩
  · change (![(0 : ℝ), 1] : Fin 2 → ℝ) 1 ≠ 0
    simp
  · change ¬ (0 : ℝ) ≠ 0
    simp

/-- **The Simpson method (11.44)**: `u_{n+1} = u_{n-1} + (h/3)(f_{n-1} + 4 f_n + f_{n+1})`,
`n ≥ 1`; `ODE.LinearMultistep.simpson`. -/
noncomputable def equation_11_44 : LinearMultistep := LinearMultistep.simpson

/-- (11.44), unfolded:
`u_{n+2} = u_n + (h/3)(f(t_n, u_n) + 4 f(t_{n+1}, u_{n+1}) + f(t_{n+2}, u_{n+2}))`. -/
theorem equation_11_44_isOrbit_iff (u : ℕ → ℝ) :
    equation_11_44.IsOrbit f h t₀ u ↔ ∀ n, u (n + 2) = u n + h / 3 *
      (f (grid t₀ h n) (u n) + 4 * f (grid t₀ h (n + 1)) (u (n + 1)) +
        f (grid t₀ h (n + 2)) (u (n + 2))) := by
  rw [equation_11_44, LinearMultistep.isOrbit_simpson_iff]
  simp only [smul_eq_mul, grid]

/-- The Simpson method is an implicit two-step method. -/
theorem equation_11_44_twoStep : definition_11_7 equation_11_44 2 ∧ equation_11_44.IsImplicit := by
  refine ⟨⟨rfl, Or.inl ?_⟩, ?_⟩
  · change (![(0 : ℝ), 1] : Fin 2 → ℝ) 1 ≠ 0
    simp
  · change (1 / 3 : ℝ) ≠ 0
    norm_num

/-! ### (11.45)–(11.46): the linear multistep method and its difference-equation form -/

/-- **The linear multistep method (11.45)**:
`u_{n+1} = ∑_{j=0}^p a_j u_{n-j} + h ∑_{j=0}^p b_j f_{n-j} + h b_{-1} f_{n+1}` for `n ≥ p`, with
`f_k = f(t_k, u_k)`; `u` is an orbit of `M : ODE.LinearMultistep` for the field `f`, the step `h`
and the initial time `t₀`. The starting values `u_0, …, u_p` are unconstrained. -/
def equation_11_45 (M : LinearMultistep) (f : ℝ → ℝ → ℝ) (h t₀ : ℝ) (u : ℕ → ℝ) : Prop :=
  M.IsOrbit f h t₀ u

/-- (11.45), unfolded, for every `n ≥ p`. -/
theorem equation_11_45_iff (M : LinearMultistep) (u : ℕ → ℝ) :
    equation_11_45 M f h t₀ u ↔ ∀ n, M.p ≤ n → u (n + 1) =
      ∑ j : Fin (M.p + 1), M.a j * u (n - j) +
        h * ∑ j : Fin (M.p + 1), M.b j * f (grid t₀ h (n - j)) (u (n - j)) +
        h * M.bm1 * f (grid t₀ h (n + 1)) (u (n + 1)) := by
  rw [equation_11_45, LinearMultistep.isOrbit_iff]
  simp only [smul_eq_mul, grid]
  constructor
  · intro H n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    exact H m
  · intro H n
    exact H (n + M.p) (Nat.le_add_left _ _)

/-- The method (11.45) is **implicit** iff `b_{-1} ≠ 0` (`ODE.LinearMultistep.IsImplicit`). -/
theorem equation_11_45_implicit_iff (M : LinearMultistep) : M.IsImplicit ↔ M.bm1 ≠ 0 :=
  Iff.rfl

/-- The coefficients `β_s` of (11.46): `β_s = b_{p-s}` for `s = 0, …, p` and `β_{p+1} = b_{-1}`.
-/
noncomputable def equation_11_46_beta (M : LinearMultistep) : Fin (M.p + 1 + 1) → ℝ :=
  Fin.snoc (fun s : Fin (M.p + 1) => M.b (Fin.rev s)) M.bm1

/-- **(11.46)**: the method (11.45) is the linear difference equation
`∑_{s=0}^{p+1} α_s u_{n+s} = h ∑_{s=0}^{p+1} β_s f(t_{n+s}, u_{n+s})` of order `k = p + 1`, with
`α_{p+1} = 1`, `α_s = -a_{p-s}` and `β_s = b_{p-s}` (`β_{p+1} = b_{-1}`): `u` is produced by the
method iff it solves the equation (11.28) with coefficients `α_0, …, α_p` and the source
`φ_{n+p+1} = h ∑_s β_s f(t_{n+s}, u_{n+s})` (the values of `φ` below the index `p + 1` are
irrelevant). -/
theorem equation_11_46 (M : LinearMultistep) (u : ℕ → ℝ) :
    equation_11_45 M f h t₀ u ↔
      (equation_11_28 fun s : Fin (M.p + 1) => -M.a (Fin.rev s)).IsSolutionWith
        (fun n => h * ∑ s : Fin (M.p + 1 + 1), equation_11_46_beta M s *
          f (grid t₀ h (n - (M.p + 1) + s)) (u (n - (M.p + 1) + s))) u := by
  rw [equation_11_45, LinearMultistep.isOrbit_iff, equation_11_28_iff]
  refine forall_congr' fun n => ?_
  rw [Fin.sum_univ_castSucc (n := M.p + 1)]
  simp only [neg_mul, Finset.sum_neg_distrib, Nat.add_sub_cancel, equation_11_46_beta,
    Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last, smul_eq_mul, grid]
  rw [show ∑ i : Fin (M.p + 1), M.a (Fin.rev i) * u (n + i) =
      ∑ j : Fin (M.p + 1), M.a j * u (n + M.p - j) from M.sum_rev_smul M.a u n,
    show ∑ s : Fin (M.p + 1), M.b (Fin.rev s) * f (node t₀ h (n + s)) (u (n + s)) =
      ∑ j : Fin (M.p + 1), M.b j * f (node t₀ h (n + M.p - j)) (u (n + M.p - j)) from
      M.sum_rev_smul M.b (fun m => f (node t₀ h m) (u m)) n, ← add_assoc]
  constructor <;> intro H <;> linear_combination H

/-- The recurrence of (11.46) is the real recurrence `ODE.LinearMultistep.toLinearRecurrenceZero`
of the method, whose characteristic polynomial is `ρ`. -/
theorem equation_11_46_eq (M : LinearMultistep) :
    (equation_11_28 fun s : Fin (M.p + 1) => -M.a (Fin.rev s)) = M.toLinearRecurrenceZero := by
  simp [equation_11_28, LinearMultistep.toLinearRecurrenceZero]

/-! ### Definitions 11.8–11.9: the truncation error, consistency and order -/

/-- **Definition 11.8, the local truncation error (11.47)** `τ_{n+1}(h)` of (11.45) at the
node `t_{n+1}`, `n ≥ p`, defined along the exact solution `y` by
`h τ_{n+1}(h) = y_{n+1} - [∑_{j=0}^p a_j y_{n-j} + h ∑_{j=-1}^p b_j y'_{n-j}]`;
`ODE.LinearMultistep.lte` at the node `t_n`. -/
noncomputable def definition_11_8 (M : LinearMultistep) (h : ℝ) (y : ℝ → ℝ) (t₀ : ℝ) (n : ℕ) :
    ℝ :=
  M.lte h y (grid t₀ h n)

/-- (11.47): `h τ_{n+1}(h) = y_{n+1} - [∑_{j=0}^p a_j y_{n-j} + h ∑_{j=-1}^p b_j y'_{n-j}]` for
`n ≥ p`, with `y' = deriv y`. -/
theorem definition_11_8_spec (M : LinearMultistep) (hh : h ≠ 0) (y : ℝ → ℝ) (hn : M.p ≤ n) :
    h * definition_11_8 M h y t₀ n = y (grid t₀ h (n + 1)) -
      (∑ j : Fin (M.p + 1), M.a j * y (grid t₀ h (n - j)) +
        h * (M.bm1 * deriv y (grid t₀ h (n + 1)) +
          ∑ j : Fin (M.p + 1), M.b j * deriv y (grid t₀ h (n - j)))) := by
  have e : ∀ j : Fin (M.p + 1), node t₀ h n - j * h = node t₀ h (n - j) := fun j =>
    LinearMultistep.node_sub_mul (by have := j.is_lt; omega)
  rw [definition_11_8, LinearMultistep.lte, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hh, one_mul,
    LinearMultistep.opL]
  simp only [grid, smul_eq_mul, e, node_succ, sub_sub]

/-- **The global truncation error** `τ(h) = max_{p ≤ n ≤ N_h - 1} |τ_{n+1}(h)|`;
`ODE.LinearMultistep.globalLte`. -/
noncomputable def definition_11_8_global (M : LinearMultistep) (t₀ T : ℝ) (y : ℝ → ℝ) (h : ℝ) :
    ℝ :=
  M.globalLte t₀ T y h

/-- `τ(h)` is the maximum of the `|τ_{n+1}(h)|` over the steps `p ≤ n < N_h` the method takes.
-/
theorem definition_11_8_global_eq (M : LinearMultistep) (t₀ T : ℝ) (y : ℝ → ℝ) (h : ℝ) :
    definition_11_8_global M t₀ T y h =
      ⨆ n : Fin (gridCount T h), if M.p ≤ (n : ℕ) then |definition_11_8 M h y t₀ n| else 0 :=
  rfl

/-- **Definition 11.9, consistency along the solution**: `τ(h) → 0` as `h → 0`;
`ODE.LinearMultistep.IsConsistentFor`. -/
def definition_11_9 (M : LinearMultistep) (t₀ T : ℝ) (y : ℝ → ℝ) : Prop :=
  M.IsConsistentFor t₀ T y

/-- Consistency along `y`, unfolded. -/
theorem definition_11_9_iff (M : LinearMultistep) :
    definition_11_9 M t₀ T y ↔ Tendsto (definition_11_8_global M t₀ T y) (𝓝[>] 0) (𝓝 0) :=
  Iff.rfl

/-- **Definition 11.9, consistency of the method**: consistent along every `C¹` solution on
every horizon (every `C¹` curve solves a Cauchy problem, for the field `f(t, v) = y'(t)`);
`ODE.LinearMultistep.IsConsistent`. -/
def definition_11_9_method (M : LinearMultistep) : Prop :=
  M.IsConsistent

/-- Consistency of the method, unfolded. -/
theorem definition_11_9_method_iff (M : LinearMultistep) :
    definition_11_9_method M ↔
      ∀ t₀ T : ℝ, 0 < T → ∀ y : ℝ → ℝ, ContDiff ℝ 1 y → definition_11_9 M t₀ T y :=
  Iff.rfl

/-- **Definition 11.9, order `q` along the solution**: `τ(h) = O(h^q)` as `h → 0`;
`ODE.LinearMultistep.HasOrderFor`. -/
def definition_11_9_order (M : LinearMultistep) (t₀ T : ℝ) (y : ℝ → ℝ) (q : ℕ) : Prop :=
  M.HasOrderFor t₀ T y q

/-- Order `q` along `y`, unfolded. -/
theorem definition_11_9_order_iff (M : LinearMultistep) {q : ℕ} :
    definition_11_9_order M t₀ T y q ↔
      definition_11_8_global M t₀ T y =O[𝓝[>] 0] fun h => h ^ q :=
  Iff.rfl

/-- **Definition 11.9, order `q` of the method**: order `q` along every `C^{q+1}` solution on
every horizon; `ODE.LinearMultistep.HasOrder`. -/
def definition_11_9_order_method (M : LinearMultistep) (q : ℕ) : Prop :=
  M.HasOrder q

/-- Order `q` of the method, unfolded. -/
theorem definition_11_9_order_method_iff (M : LinearMultistep) (q : ℕ) :
    definition_11_9_order_method M q ↔
      ∀ t₀ T : ℝ, 0 < T → ∀ y : ℝ → ℝ, ContDiff ℝ (q + 1) y → definition_11_9_order M t₀ T y q :=
  Iff.rfl

/-- A method of order `q ≥ 1` is consistent. -/
theorem definition_11_9_of_order (M : LinearMultistep) {q : ℕ} (hq : 1 ≤ q)
    (H : definition_11_9_order_method M q) : definition_11_9_method M :=
  LinearMultistep.HasOrder.isConsistent M hq H

/-! ### (11.48): the operator `L`, the principal truncation error and the error constant -/

/-- **The linear operator `L` (11.48)** associated with the method:
`L[w; h](t) = w(t + h) - ∑_{j=0}^p a_j w(t - jh) - h ∑_{j=-1}^p b_j w'(t - jh)` for a
differentiable `w`; `ODE.LinearMultistep.opL`. -/
noncomputable def equation_11_48 (M : LinearMultistep) (h : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  M.opL h w t

/-- (11.48), unfolded, with `w' = deriv w`. -/
theorem equation_11_48_eq (M : LinearMultistep) (h : ℝ) (w : ℝ → ℝ) (t : ℝ) :
    equation_11_48 M h w t = w (t + h) - ∑ j : Fin (M.p + 1), M.a j * w (t - j * h) -
      h * (M.bm1 * deriv w (t + h) + ∑ j : Fin (M.p + 1), M.b j * deriv w (t - j * h)) :=
  rfl

/-- The local truncation error is `τ_{n+1}(h) = L[y; h](t_n) / h`. -/
theorem equation_11_48_lte (M : LinearMultistep) (h : ℝ) (y : ℝ → ℝ) (t₀ : ℝ) (n : ℕ) :
    definition_11_8 M h y t₀ n = equation_11_48 M h y (grid t₀ h n) / h := by
  rw [definition_11_8, LinearMultistep.lte, smul_eq_mul, div_eq_inv_mul]
  rfl

/-- `L` is linear: additive and homogeneous in `w` (for differentiable arguments). -/
theorem equation_11_48_linear (M : LinearMultistep) (h : ℝ) (w v : ℝ → ℝ) (t c : ℝ)
    (hw : Differentiable ℝ w) (hv : Differentiable ℝ v) :
    equation_11_48 M h (w + v) t = equation_11_48 M h w t + equation_11_48 M h v t ∧
      equation_11_48 M h (c • w) t = c * equation_11_48 M h w t :=
  ⟨M.opL_add h w v t (fun s => hw s) (fun s => hv s), M.opL_smul h c w t (fun s => hw s)⟩

/-- **The error constant** `C_{q+1}` of a method of order `q` (§11.5): the coefficient of
`h^{q+1} y^{(q+1)}(t_n)` in the principal local truncation error,
`C_{q+1} = (1 - ∑_{j=0}^p (-j)^{q+1} a_j - (q + 1) ∑_{j=-1}^p (-j)^q b_j) / (q + 1)!`;
`ODE.LinearMultistep.errorConstant`. -/
noncomputable def errorConstant (M : LinearMultistep) (q : ℕ) : ℝ :=
  M.errorConstant q

/-- The error constant, unfolded. -/
theorem errorConstant_eq (M : LinearMultistep) (q : ℕ) :
    errorConstant M q =
      (1 - ∑ j : Fin (M.p + 1), (-(j : ℝ)) ^ (q + 1) * M.a j -
        (q + 1 : ℕ) * (M.bm1 + ∑ j : Fin (M.p + 1), (-(j : ℝ)) ^ q * M.b j)) /
        (q + 1).factorial := by
  rw [errorConstant, LinearMultistep.errorConstant, LinearMultistep.taylorCoeff,
    Nat.add_sub_cancel]

/-- **The principal local truncation error** (§11.5): for a method of order `q` and a `C^{q+2}`
function `y`, `L[y; h](t) = C_{q+1} h^{q+1} y^{(q+1)}(t) + O(h^{q+2})`, precisely
`|L[y; h](t) - C_{q+1} h^{q+1} y^{(q+1)}(t)| ≤ K R h^{q+2}` whenever `|y^{(q+2)}| ≤ K` on an
interval `[a, b]` containing `[t - ph, t + h]`, with the constant
`R = ODE.LinearMultistep.remainderConst M (q + 1)` of the method. The coefficients
`C_0, …, C_q` of the Taylor expansion of `L` vanish by Theorem 11.3
(`ODE.LinearMultistep.hasOrder_iff`), and `ODE.LinearMultistep.opL_eq_sum_add_remainder` bounds
the remainder. -/
theorem equation_11_48_principal (M : LinearMultistep) {q : ℕ}
    (hq : definition_11_9_order_method M q) (hy : ContDiff ℝ (q + 2) y) {a b K : ℝ}
    (hK : ∀ s ∈ Icc a b, |iteratedDeriv (q + 2) y s| ≤ K) (hh : 0 < h)
    (ht : t - M.p * h ∈ Icc a b) (hth : t + h ∈ Icc a b) :
    |equation_11_48 M h y t - errorConstant M q * h ^ (q + 1) * iteratedDeriv (q + 1) y t| ≤
      K * M.remainderConst (q + 1) * h ^ (q + 2) := by
  have hder : ∀ m ≤ q + 1, ∀ s, HasDerivAt (iteratedDeriv m y) (iteratedDeriv (m + 1) y s) s := by
    intro m hm s
    have hdiff : Differentiable ℝ (iteratedDeriv m y) :=
      hy.differentiable_iteratedDeriv m (by exact_mod_cast Nat.lt_succ_of_le hm)
    rw [iteratedDeriv_succ]
    exact (hdiff s).hasDerivAt
  have hexp := M.opL_eq_sum_add_remainder (q := q + 1) (y := fun m => iteratedDeriv m y)
    (fun m hm s _ => (hder m hm s).hasDerivWithinAt)
    (fun s _ => (hder 0 (Nat.zero_le _) s).deriv) hK hh ht hth
  have hzero : ∀ m ∈ range (q + 1), (h ^ m / m.factorial * M.taylorCoeff m) •
      iteratedDeriv m y t = 0 := fun m hm => by
    rw [Finset.mem_range] at hm
    rw [(M.orderCondition_iff_taylorCoeff_eq_zero m).1
      (M.hasOrder_iff.1 hq m (Nat.lt_succ_iff.1 hm)), mul_zero, zero_smul]
  rw [Finset.sum_range_succ, Finset.sum_eq_zero hzero, zero_add, iteratedDeriv_zero,
    Real.norm_eq_abs] at hexp
  rw [equation_11_48, errorConstant, LinearMultistep.errorConstant]
  convert hexp using 3
  rw [smul_eq_mul]
  ring

/-! ### (11.49)–(11.51): the Adams methods -/

/-- **The Adams methods (11.49)**: `u_{n+1} = u_n + h ∑_{j=-1}^p b_j f_{n-j}`, the linear
multistep methods with `a_0 = 1` and `a_1 = ⋯ = a_p = 0`, obtained by integrating over
`[t_n, t_{n+1}]` the polynomial interpolating `f` at the nodes `t_{n+1}, t_n, …, t_{n-p}` (the
implicit Adams–Moulton methods) or at `t_n, …, t_{n-p}` (the explicit Adams–Bashforth methods,
`b_{-1} = 0`). -/
def equation_11_49 (M : LinearMultistep) : Prop :=
  M.a = Pi.single 0 1

/-- (11.49), unfolded: an Adams method is `u_{n+1} = u_n + h ∑_{j=-1}^p b_j f_{n-j}`, `n ≥ p`. -/
theorem equation_11_49_iff {M : LinearMultistep} (hM : equation_11_49 M) (u : ℕ → ℝ) :
    equation_11_45 M f h t₀ u ↔ ∀ n, M.p ≤ n → u (n + 1) = u n +
      h * (∑ j : Fin (M.p + 1), M.b j * f (grid t₀ h (n - j)) (u (n - j)) +
        M.bm1 * f (grid t₀ h (n + 1)) (u (n + 1))) := by
  rw [equation_11_45_iff]
  refine forall₂_congr fun n _ => ?_
  rw [equation_11_49] at hM
  rw [hM, Fin.sum_univ_succ, Pi.single_eq_same, Finset.sum_eq_zero fun j _ =>
    by rw [Pi.single_eq_of_ne (Fin.succ_ne_zero j), zero_mul]]
  simp only [Fin.val_zero, Nat.sub_zero, one_mul, add_zero]
  constructor <;> intro H <;> linear_combination H

/-- **The Adams–Bashforth methods** `ODE.LinearMultistep.adamsBashforth p` (`p + 1` steps,
nodes `t_n, …, t_{n-p}`) are the explicit Adams methods: `a = (1, 0, …, 0)`, `b_{-1} = 0`, and
the weights are the integrals `b_j = ∫_0^1 ℓ_j(s) ds` of the Lagrange basis of the normalized
nodes `s = 0, -1, …, -p`. -/
theorem equation_11_49_adamsBashforth (p : ℕ) :
    equation_11_49 (LinearMultistep.adamsBashforth p) ∧
      (LinearMultistep.adamsBashforth p).bm1 = 0 ∧
      ∀ j : Fin (p + 1), (LinearMultistep.adamsBashforth p).b j = ∫ s in (0 : ℝ)..1,
        (Lagrange.basis Finset.univ (fun i : Fin (p + 1) => -(i : ℝ)) j).eval s :=
  ⟨rfl, rfl, fun _ => rfl⟩

/-- **The Adams–Moulton methods** `ODE.LinearMultistep.adamsMoulton (p + 1)` (`p + 1` steps,
nodes `t_{n+1}, t_n, …, t_{n-p}`, the book's index `p`) are the implicit Adams methods:
`a = (1, 0, …, 0)`, and the weights `b_{-1}, b_0, …, b_p` are the integrals `∫_0^1 ℓ_i(s) ds`
of the Lagrange basis of the normalized nodes `s = 1, 0, …, -p`. -/
theorem equation_11_49_adamsMoulton (p : ℕ) :
    equation_11_49 (LinearMultistep.adamsMoulton (p + 1)) ∧
      (LinearMultistep.adamsMoulton (p + 1)).bm1 = ∫ s in (0 : ℝ)..1,
        (Lagrange.basis Finset.univ (fun i : Fin (p + 2) => 1 - (i : ℝ)) 0).eval s ∧
      ∀ k : Fin (p + 1), (LinearMultistep.adamsMoulton (p + 1)).b k = ∫ s in (0 : ℝ)..1,
        (Lagrange.basis Finset.univ (fun i : Fin (p + 2) => 1 - (i : ℝ)) k.succ).eval s := by
  refine ⟨rfl, ?_, fun k => ?_⟩
  · have h0 : 0 < p + 1 + 1 := Nat.succ_pos _
    change LinearMultistep.adamsMoultonWeight (p + 1) 0 = _
    simp only [LinearMultistep.adamsMoultonWeight, h0, ↓reduceDIte]
    rfl
  · have hk : (k : ℕ) + 1 < p + 1 + 1 := by have := k.is_lt; omega
    change LinearMultistep.adamsMoultonWeight (p + 1) ((k : ℕ) + 1) = _
    simp only [LinearMultistep.adamsMoultonWeight, hk, ↓reduceDIte]
    rfl

/-- **(11.50), the Adams–Bashforth methods**: the two-step method is
`u_{n+1} = u_n + (h/2)(3 f_n - f_{n-1})` (`b = (3/2, -1/2)`); the one-step method
`adamsBashforth 0` is forward Euler; the three- and four-step methods have
`b = (23/12, -16/12, 5/12)` and `b = (55/24, -59/24, 37/24, -9/24)`. -/
theorem equation_11_50 :
    (∀ u : ℕ → ℝ, equation_11_45 (LinearMultistep.adamsBashforth 1) f h t₀ u ↔
      ∀ n, 1 ≤ n → u (n + 1) = u n +
        h / 2 * (3 * f (grid t₀ h n) (u n) - f (grid t₀ h (n - 1)) (u (n - 1)))) ∧
    (∀ u : ℕ → ℝ, equation_11_45 (LinearMultistep.adamsBashforth 0) f h t₀ u ↔
      OneStep.IsOrbit (OneStep.ofIncrement (equation_11_7 f)) h t₀ u) ∧
    LinearMultistep.adamsBashforth 1 = ⟨1, ![1, 0], ![3 / 2, -1 / 2], 0⟩ ∧
    LinearMultistep.adamsBashforth 2 = ⟨2, ![1, 0, 0], ![23 / 12, -16 / 12, 5 / 12], 0⟩ ∧
    LinearMultistep.adamsBashforth 3 =
      ⟨3, ![1, 0, 0, 0], ![55 / 24, -59 / 24, 37 / 24, -9 / 24], 0⟩ := by
  refine ⟨fun u => ?_, fun u => ?_, LinearMultistep.adamsBashforth_one_eq,
    LinearMultistep.adamsBashforth_two_eq, LinearMultistep.adamsBashforth_three_eq⟩
  · rw [equation_11_45_iff, LinearMultistep.adamsBashforth_one_eq]
    change (∀ n, 1 ≤ n → u (n + 1) = ∑ j : Fin 2, ![(1 : ℝ), 0] j * u (n - j) +
      h * ∑ j : Fin 2, ![(3 / 2 : ℝ), -1 / 2] j * f (grid t₀ h (n - j)) (u (n - j)) +
      h * 0 * f (grid t₀ h (n + 1)) (u (n + 1))) ↔ _
    refine forall₂_congr fun n _ => ?_
    simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, Nat.sub_zero, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul, zero_mul, add_zero, mul_zero]
    constructor <;> intro H <;> linear_combination H
  · rw [equation_11_45, LinearMultistep.adamsBashforth_zero_eq,
      LinearMultistep.isOrbit_ofOneStep_forwardEuler_iff]
    rfl

/-- **`q`-step Adams–Bashforth methods have order `q`** (§11.5.1):
`(adamsBashforth p).HasOrder (p + 1)`; `ODE.LinearMultistep.adamsBashforth_hasOrder`. -/
theorem adamsBashforth_order (p : ℕ) :
    definition_11_9_order_method (LinearMultistep.adamsBashforth p) (p + 1) :=
  LinearMultistep.adamsBashforth_hasOrder p

/-- **(11.51), the Adams–Moulton methods**: the two-step method is
`u_{n+1} = u_n + (h/12)(5 f_{n+1} + 8 f_n - f_{n-1})` (`b_{-1} = 5/12`, `b = (8/12, -1/12)`);
the one-step methods `adamsMoulton 0` and `adamsMoulton 1` are backward Euler and
Crank–Nicolson; the three- and four-step methods have `(b_{-1}; b) = (9/24; 19/24, -5/24, 1/24)`
and `(251/720; 646/720, -264/720, 106/720, -19/720)`. -/
theorem equation_11_51 :
    (∀ u : ℕ → ℝ, equation_11_45 (LinearMultistep.adamsMoulton 2) f h t₀ u ↔
      ∀ n, 1 ≤ n → u (n + 1) = u n + h / 12 * (5 * f (grid t₀ h (n + 1)) (u (n + 1)) +
        8 * f (grid t₀ h n) (u n) - f (grid t₀ h (n - 1)) (u (n - 1)))) ∧
    (∀ u : ℕ → ℝ, equation_11_45 (LinearMultistep.adamsMoulton 0) f h t₀ u ↔
      OneStep.IsOrbit (OneStep.ofIncrement (equation_11_8 f)) h t₀ u) ∧
    (∀ u : ℕ → ℝ, equation_11_45 (LinearMultistep.adamsMoulton 1) f h t₀ u ↔
      OneStep.IsOrbit (OneStep.ofIncrement (equation_11_9 f)) h t₀ u) ∧
    LinearMultistep.adamsMoulton 2 = ⟨1, ![1, 0], ![8 / 12, -1 / 12], 5 / 12⟩ ∧
    LinearMultistep.adamsMoulton 3 = ⟨2, ![1, 0, 0], ![19 / 24, -5 / 24, 1 / 24], 9 / 24⟩ ∧
    LinearMultistep.adamsMoulton 4 =
      ⟨3, ![1, 0, 0, 0], ![646 / 720, -264 / 720, 106 / 720, -19 / 720], 251 / 720⟩ := by
  refine ⟨fun u => ?_, fun u => ?_, fun u => ?_, LinearMultistep.adamsMoulton_two_eq,
    LinearMultistep.adamsMoulton_three_eq, LinearMultistep.adamsMoulton_four_eq⟩
  · rw [equation_11_45_iff, LinearMultistep.adamsMoulton_two_eq]
    change (∀ n, 1 ≤ n → u (n + 1) = ∑ j : Fin 2, ![(1 : ℝ), 0] j * u (n - j) +
      h * ∑ j : Fin 2, ![(8 / 12 : ℝ), -1 / 12] j * f (grid t₀ h (n - j)) (u (n - j)) +
      h * (5 / 12) * f (grid t₀ h (n + 1)) (u (n + 1))) ↔ _
    refine forall₂_congr fun n _ => ?_
    simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, Nat.sub_zero, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul, zero_mul, add_zero]
    constructor <;> intro H <;> linear_combination H
  · rw [equation_11_45, LinearMultistep.adamsMoulton_zero_eq,
      LinearMultistep.isOrbit_ofOneStep_backwardEuler_iff]
    rfl
  · rw [equation_11_45, LinearMultistep.adamsMoulton_one_eq,
      LinearMultistep.isOrbit_ofOneStep_crankNicolson_iff]
    rfl

/-- **`q`-step Adams–Moulton methods have order `q + 1`** (§11.5.1):
`(adamsMoulton p).HasOrder (p + 1)` (for every `p`, the case `p = 0` being backward Euler);
`ODE.LinearMultistep.adamsMoulton_hasOrder`. -/
theorem adamsMoulton_order (p : ℕ) :
    definition_11_9_order_method (LinearMultistep.adamsMoulton p) (p + 1) :=
  LinearMultistep.adamsMoulton_hasOrder p

/-- **Table 11.1**: the error constants `C*_{q+1}` of the Adams–Bashforth methods of orders
`q = 1, …, 4` are `1/2, 5/12, 3/8, 251/720`, and the error constants `C_{q+1}` of the
Adams–Moulton methods of orders `q = 1, …, 4` are `-1/2, -1/12, -1/24, -19/720`. The table's
index `q` is the order in both columns (its caption "having order `q + 1`" for the Adams–Moulton
column would place `-1/2` at Crank–Nicolson, whose constant is `-1/12`);
`ODE.LinearMultistep.adamsBashforth_errorConstant`,
`ODE.LinearMultistep.adamsMoulton_errorConstant`. -/
theorem adamsErrorConstants :
    (errorConstant (LinearMultistep.adamsBashforth 0) 1 = 1 / 2 ∧
      errorConstant (LinearMultistep.adamsBashforth 1) 2 = 5 / 12 ∧
      errorConstant (LinearMultistep.adamsBashforth 2) 3 = 3 / 8 ∧
      errorConstant (LinearMultistep.adamsBashforth 3) 4 = 251 / 720) ∧
    (errorConstant (LinearMultistep.adamsMoulton 0) 1 = -1 / 2 ∧
      errorConstant (LinearMultistep.adamsMoulton 1) 2 = -1 / 12 ∧
      errorConstant (LinearMultistep.adamsMoulton 2) 3 = -1 / 24 ∧
      errorConstant (LinearMultistep.adamsMoulton 3) 4 = -19 / 720) :=
  ⟨LinearMultistep.adamsBashforth_errorConstant, LinearMultistep.adamsMoulton_errorConstant⟩

/-! ### §11.5.2, Table 11.2: the BDF methods -/

/-- **The backward differentiation formulae (§11.5.2, Table 11.2)**:
`u_{n+1} = ∑_{j=0}^p a_j u_{n-j} + h b_{-1} f_{n+1}` for `p = 0, …, 5`, the implicit methods with
`b_0 = ⋯ = b_p = 0` obtained by differentiating the polynomial interpolating `u` at
`t_{n+1}, …, t_{n-p}`; `bdf 0` is backward Euler. The printed `b_{-1} = 60/137` of the row
`p = 5` is `60/147`; `ODE.LinearMultistep.bdf`. -/
noncomputable def bdf : Fin 6 → LinearMultistep := LinearMultistep.bdf

/-- The row `p` of Table 11.2 has `p + 1` steps and `b_0 = ⋯ = b_p = 0`. -/
theorem bdf_p_b (k : Fin 6) : (bdf k).p = k ∧ (bdf k).b = 0 := by
  fin_cases k <;> refine ⟨rfl, ?_⟩ <;> funext j <;> fin_cases j <;> rfl

/-- The BDF methods, unfolded: `u_{n+1} = ∑_{j=0}^p a_j u_{n-j} + h b_{-1} f(t_{n+1}, u_{n+1})`
for `n ≥ p` (`p = (bdf k).p = k`). -/
theorem bdf_isOrbit_iff (k : Fin 6) (u : ℕ → ℝ) :
    equation_11_45 (bdf k) f h t₀ u ↔ ∀ n, (bdf k).p ≤ n → u (n + 1) =
      ∑ j : Fin ((bdf k).p + 1), (bdf k).a j * u (n - j) +
        h * (bdf k).bm1 * f (grid t₀ h (n + 1)) (u (n + 1)) := by
  rw [equation_11_45_iff]
  refine forall₂_congr fun n _ => ?_
  rw [(bdf_p_b k).2]
  simp

/-- **Table 11.2**, the coefficients: `bdf 0` is backward Euler, and the rows `p = 1, …, 5`
are `(a; b_{-1}) = (4/3, -1/3; 2/3)`, `(18/11, -9/11, 2/11; 6/11)`,
`(48/25, -36/25, 16/25, -3/25; 12/25)`, `(300/137, -300/137, 200/137, -75/137, 12/137; 60/137)`,
`(360/147, -450/147, 400/147, -225/147, 72/147, -10/147; 60/147)`. -/
theorem bdf_table :
    (∀ u : ℕ → ℝ, equation_11_45 (bdf 0) f h t₀ u ↔
      OneStep.IsOrbit (OneStep.ofIncrement (equation_11_8 f)) h t₀ u) ∧
    bdf 1 = ⟨1, ![4 / 3, -1 / 3], 0, 2 / 3⟩ ∧
    bdf 2 = ⟨2, ![18 / 11, -9 / 11, 2 / 11], 0, 6 / 11⟩ ∧
    bdf 3 = ⟨3, ![48 / 25, -36 / 25, 16 / 25, -3 / 25], 0, 12 / 25⟩ ∧
    bdf 4 = ⟨4, ![300 / 137, -300 / 137, 200 / 137, -75 / 137, 12 / 137], 0, 60 / 137⟩ ∧
    bdf 5 = ⟨5, ![360 / 147, -450 / 147, 400 / 147, -225 / 147, 72 / 147, -10 / 147], 0,
      60 / 147⟩ :=
  ⟨fun u => by
    rw [equation_11_45, bdf, LinearMultistep.bdf_zero_eq,
      LinearMultistep.isOrbit_ofOneStep_backwardEuler_iff]
    rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The BDF methods have order `p + 1`** (§11.5.2): `(bdf k).HasOrder (k + 1)` for
`k = 0, …, 5`; `ODE.LinearMultistep.bdf_hasOrder`. -/
theorem bdf_order (k : Fin 6) : definition_11_9_order_method (bdf k) (k + 1) :=
  LinearMultistep.bdf_hasOrder k

end QuarteroniSaccoSaleri.Chapter11

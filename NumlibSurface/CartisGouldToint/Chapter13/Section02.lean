import Numlib.FiniteDifference.Gradient
import NumlibSurface.CartisGouldToint.Chapter13.Section01

/-!
# Cartis–Gould–Toint §13.2: Fast convergence using low-degree oracles

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §13.2. Inexact derivatives of
degrees `o + 1, …, r` (`r = q` for TRqIDA, `p` for ARqpIDA) may be produced by a *finite
derivative-approximation scheme* from oracles of degree at most `o` (finite differences,
multivariate interpolation), with errors of the IDA form (13.1.2). Theorem 13.2.1 then follows from
Theorems 13.1.8 and 13.1.19 once oracle calls are counted: each function value costs one oracle
call and each derivative estimate `c` calls, so the number of oracle calls before the first
approximately optimal iterate is at most `#F + c · #D`.

## Modelling

A scheme (`FiniteDerivativeApproxScheme`) is a deterministic map from a point and requested
accuracies to an inexact jet satisfying `Optimization.JetApprox` (13.1.2), exact in the degrees
`≤ o` (computed by the oracles), with a declared number `cost` of oracle calls per estimate. The
oracle-call semantics are a counting convention, as for all evaluation counts of the book. The
forward-difference gradient (`o = 0`, `r = 1`, `n` function values) and Hessian (`o = 1`,
`r = 2`, `n` gradients) of `FiniteDifference` are schemes (`fdGradientScheme`,
`fdHessianScheme`).

## Deviations from the book

* (13.2.5)–(13.2.7) print `O(min_j ε_j^{-…})`; the bounds are `O(max_j ε_j^{-…})`, i.e.
  `O(ε_min^{-(q+1)})` for TRqIDA and `O(1/min_j ε_j^{π_j})` for ARqpIDA (with `π_j` as in
  Lemma 13.1.18), consistent with Theorems 13.1.8 and 13.1.19.
* The general stencil claim (13.2.1) (unproved in the literature, footnote 93), the interpolation
  bound (13.2.4) and the derivative-free discussion are not formalized.
-/

open Set Finset Optimization
open scoped Nat

namespace CartisGouldToint.Chapter13

variable {n : ℕ}

set_option hygiene false in
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- A **finite derivative-approximation scheme** ([cartis2022evaluation], §13.2) for `f` from
oracles of degree at most `o`, producing inexact derivatives up to degree `r` with the errors
(13.1.2): `est x h` is the inexact jet at `x` for requested accuracies `h > 0`, exact in the degrees
`≤ o`, and each estimate costs `cost` oracle calls (of degree `≤ o`). -/
structure FiniteDerivativeApproxScheme (f : ℝⁿ → ℝ) (o r : ℕ) (κg : ℕ → ℝ) where
  /-- The inexact jet at a point for given requested accuracies. -/
  est : ℝⁿ → (ℕ → ℝ) → FormalMultilinearSeries ℝ ℝⁿ ℝ
  /-- The number of oracle calls per estimate. -/
  cost : ℕ
  /-- The error model (13.1.2). -/
  approx : ∀ x h, (∀ i ∈ Finset.Icc 1 r, 0 < h i) →
    JetApprox (ftaylorSeries ℝ f x) (est x h) r (fun i => κg i * h i)
  /-- The degrees available from the oracles are exact. -/
  exact_low : ∀ x h, ∀ i ≤ o, est x h i = iteratedFDeriv ℝ i f x

/-- **Forward-difference gradients form a scheme** with `o = 0`, `r = 1` and `n` function values
per estimate, `κ_{∇,1} = √n L/2`, when `∇f` is `L`-Lipschitz (§13.2, first display). -/
noncomputable def fdGradientScheme (f : ℝⁿ → ℝ) {L : ℝ} (hf : ContDiff ℝ 1 f)
    (hL : ∀ y z, ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ L * ‖y - z‖) :
    FiniteDerivativeApproxScheme f 0 1 (fun _ => √n * L / 2) where
  est x h := gradientJet (ftaylorSeries ℝ f x) (FiniteDifference.fdGradient f (h 1) x)
  cost := n
  approx x h hh := by
    refine (FiniteDifference.jetApprox_fdGradient hf hL (hh 1 (by simp)) x).mono_err ?_
    intro i hi
    obtain rfl : i = 1 := by simpa using hi
    exact le_rfl
  exact_low x h i hi := by
    obtain rfl : i = 0 := Nat.le_zero.1 hi
    rw [gradientJet_apply_of_ne _ _ (by norm_num)]
    rfl

/-- **Forward-difference Hessians form a scheme** with `o = 1`, `r = 2` and `n` gradient values
per estimate, `κ_{∇,2} = √n L/2` (`κ_{∇,1} = 0`, the gradient is exact), when the Hessian is
`L`-Lipschitz (§13.2, fourth display). -/
noncomputable def fdHessianScheme (f : ℝⁿ → ℝ) {L : ℝ} (hf : ContDiff ℝ 2 f)
    (hL : ∀ y z, ‖hessianOperator f y - hessianOperator f z‖ ≤ L * ‖y - z‖) :
    FiniteDerivativeApproxScheme f 1 2 (fun i => if i = 2 then √n * L / 2 else 0) where
  est x h := hessianJet (ftaylorSeries ℝ f x) (FiniteDifference.fdHessian f (h 2) x)
  cost := n
  approx x h hh := by
    refine (FiniteDifference.jetApprox_fdHessian hf hL (hh 2 (by simp)) x).mono_err ?_
    intro i hi
    by_cases h2 : i = 2 <;> simp [h2]
  exact_low x h i hi := by
    rw [hessianJet_apply_of_ne _ _ (by omega)]
    rfl

/-- `|log t| ≤ 1/t` for `t ∈ (0, 1]`. -/
theorem abs_log_le_inv {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) : |Real.log t| ≤ 1 / t := by
  rw [abs_of_nonpos (Real.log_nonpos ht.le ht1), ← Real.log_inv, one_div]
  have := Real.log_le_sub_one_of_pos (inv_pos.2 ht)
  linarith

/-- `a + b |log t| + c ≤ (a' + b + c)/t^m` for `t ∈ (0, 1]`, `m ≥ 1`, `b, c ≥ 0` and
`a ≤ a'/t^m`. -/
private theorem le_div_pow_of_log {a a' b c t : ℝ} {m : ℕ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hm : 1 ≤ m) (hb : 0 ≤ b) (hc : 0 ≤ c) (ha : a ≤ a' / t ^ m) :
    a + b * |Real.log t| + c ≤ (a' + b + c) / t ^ m := by
  have htm : 0 < t ^ m := pow_pos ht m
  have htm1 : t ^ m ≤ t := by
    calc t ^ m ≤ t ^ 1 := pow_le_pow_of_le_one ht.le ht1 hm
      _ = t := pow_one t
  have h1 : |Real.log t| ≤ 1 / t ^ m :=
    (abs_log_le_inv ht ht1).trans (one_div_le_one_div_of_le htm htm1)
  have h2 : c ≤ c / t ^ m := le_div_self hc htm (pow_le_one₀ ht.le ht1)
  rw [add_div, add_div]
  have := mul_le_mul_of_nonneg_left h1 hb
  rw [mul_one_div] at this
  linarith

section TR

variable {f : ℝⁿ → ℝ} {κg : ℕ → ℝ} {P : TRqIDAParams} {L : ℕ → ℝ} {x₀ : ℝⁿ}

/-- **Theorem 13.2.1, trust-region part** ([cartis2022evaluation], corrected): let f.D0qL and f.Bb
hold, `o ≤ q`, `S` a finite derivative-approximation scheme for `f` from oracles of degree `≤ o`
producing inexact derivatives up to degree `q`. There is a constant `C`
(independent of the tolerances) such that every TRqIDA run whose derivatives are those of the
scheme (`D_k = S.est x_k h_k`) reaches a first iterate that is an `(ε, δ)`-approximate `q`-th
order minimizer (`trTest`) after at most `C/ε_min^{q+1} = C max_j ε_j^{-(q+1)}` calls to the
oracles of degree `≤ o` (one per function value, `S.cost` per derivative estimate). The book
prints `O(min_j ε_j^{-(q+1)})`. -/
theorem theorem_13_2_1_i (hf : AssumptionD0qL f P.q L) {flow : ℝ}
    (hb : Chapter02.AssumptionBb f flow) {o : ℕ} (S : FiniteDerivativeApproxScheme f o P.q κg) :
    ∃ C, ∀ (ε : ℕ → ℝ) (x : ℕ → ℝⁿ) (Δ : ℕ → ℝ) (h : ℕ → ℕ → ℝ)
      (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ) (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ)
      (acc : ℕ → Prop), algorithm_13_1_1 f κg P ε x₀ x Δ h D dd jk s acc →
      (∀ k, D k = S.est (x k) (h k)) →
      ∃ kε, IsFirstHit (trTest f P ε x Δ) kε ∧
        (derivEvalCount (fun i => ¬ acc i) kε : ℝ) + S.cost *
          derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ trqRatio f D x s jk i)) kε ≤
        C / epsMin P.q ε ^ (P.q + 1) := by
  set κΔ := min 1 (P.γ₁ * ((1 - P.η₂) /
    (lipMax L P.q + 4 * (P.q + 1)! * P.κs * ordMax P.q κg)))
  set A := trKappaS P κΔ * (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * (f x₀ - flow)
  set B := 1 / |Real.log P.γ₂|
  set Cc := |Real.log (P.ς * (κΔ / 2) / P.Δ₀)| / |Real.log P.γ₂| + 1
  set E := P.q * (P.q + 1) / |Real.log P.γh|
  set F := |Real.log (trKappaAcc P κΔ (lipMax L P.q + ordMax P.q κg * P.κh) (ordMax P.q κg) /
    P.κh)| / |Real.log P.γh| + 2 with hF_def
  refine ⟨(A + B + Cc) + S.cost * (A + E + F), fun ε x Δ h D dd jk s acc hrun _ => ?_⟩
  have hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ := by
    have := hf.one_le_lipMax; have := hrun.kappaMax_nonneg; have := P.κs_pos
    exact ⟨lt_min one_pos (mul_pos P.γ₁_pos (div_pos P.one_sub_η₂_pos (by positivity))),
      min_le_left _ _, min_le_right _ _⟩
  obtain ⟨kε, hk, -, -, h1, h2⟩ := theorem_13_1_8 hf hb hrun hκΔ
  refine ⟨kε, hk, ?_⟩
  have hε := hrun.epsMin_pos
  have hε1 := hrun.epsMin_le_one
  have hq : 1 ≤ P.q + 1 := by omega
  have hB : 0 ≤ B := by positivity
  have hC : 0 ≤ Cc := by positivity
  have hE : 0 ≤ E := by positivity
  have hF : 0 ≤ F := by positivity
  have h1' := h1.trans (le_div_pow_of_log hε hε1 hq hB hC le_rfl)
  have h2' := (h2.trans (le_of_eq (by rw [hF_def]; ring))).trans
    (le_div_pow_of_log hε hε1 hq hE hF (le_refl (A / epsMin P.q ε ^ (P.q + 1))))
  have hcost : (0 : ℝ) ≤ S.cost := Nat.cast_nonneg _
  calc (derivEvalCount (fun i => ¬ acc i) kε : ℝ) + S.cost *
        derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ trqRatio f D x s jk i)) kε
      ≤ (A + B + Cc) / epsMin P.q ε ^ (P.q + 1) +
          S.cost * ((A + E + F) / epsMin P.q ε ^ (P.q + 1)) :=
        add_le_add h1' (mul_le_mul_of_nonneg_left h2' hcost)
    _ = ((A + B + Cc) + S.cost * (A + E + F)) / epsMin P.q ε ^ (P.q + 1) := by ring

end TR

section AR

variable {f : ℝⁿ → ℝ} {κg : ℕ → ℝ} {P : ARqpIDAParams} {L : ℕ → ℝ} {x₀ : ℝⁿ}

/-- `min_j ε_j^{π_j} ≤ ε_min` for `ε ∈ (0, 1]^q` (the exponents `π_j ≥ 1`). -/
theorem epsMin_rpow_arPi_le {ε : ℕ → ℝ} (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1) :
    epsMin P.q (fun j => ε j ^ arPi P.q P.p j) ≤ epsMin P.q ε := by
  obtain ⟨j, hj, he⟩ := exists_epsMin_eq (ε := ε) P.one_le_q
  rw [he]
  refine (epsMin_le hj).trans ?_
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  have hp := P.one_le_p
  have hπ : 1 ≤ arPi P.q P.p j := by
    unfold arPi arPiOf
    split_ifs
    · rw [le_div_iff₀ (by exact_mod_cast (show 0 < P.p - j + 1 by omega)), one_mul]
      have : P.p - j + 1 ≤ P.p + 1 := by omega
      exact_mod_cast this
    · rw [le_div_iff₀ (by exact_mod_cast (show 0 < P.p by omega)), one_mul]
      have : (1 : ℝ) ≤ j := by exact_mod_cast hj1
      nlinarith
  calc ε j ^ arPi P.q P.p j ≤ ε j ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge (hε j hj).1 (hε j hj).2 hπ
    _ = ε j := Real.rpow_one _

/-- **Theorem 13.2.1, regularization part** ([cartis2022evaluation], corrected): let f.D0pL and
f.Bb hold, and `S` a finite derivative-approximation scheme for `f` from
oracles of degree `≤ o` producing inexact derivatives up to degree `p`. There is a constant `C`
(independent of the tolerances) such that every ARqpIDA run with the radii control
(13.1.69)–(13.1.70) whose derivatives are those of the scheme reaches a first iterate that is
approximately optimal (`arTest`) after at most `C / min_j ε_j^{π_j}` oracle calls, with
`π_j = (p+1)/(p-j+1)` if `q ≤ 2` and `π_j = j(p+1)/p` if `q > 2` (`arPi`), i.e.
`O(max_j ε_j^{-π_j})`. The book prints `min_j` for `max_j`. -/
theorem theorem_13_2_1_ii (hf : AssumptionD0pL f P.p L) {flow : ℝ}
    (hb : Chapter02.AssumptionBb f flow) {o : ℕ}
    (S : FiniteDerivativeApproxScheme f o P.p κg) :
    ∃ C, ∀ (ε : ℕ → ℝ) (x : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ)
      (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ) (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ)
      (acc : ℕ → Prop), algorithm_13_1_2 f κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc →
      (∀ i, RadiiControl P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i) →
      (∀ k, D k = S.est (x k) (h k)) →
      ∃ kε, IsFirstHit (arTest f P ε x) kε ∧
        (derivEvalCount (fun i => ¬ acc i) kε : ℝ) + S.cost *
          derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i)) kε ≤
        C / epsMin P.q (fun j => ε j ^ arPi P.q P.p j) := by
  set κΔm := P.σmin / ((P.p + 1)! : ℝ) * arStepConst P.q P.p (1 - P.θ)
    (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
      (arSigmaMax P (L P.p) (ordMax P.p κg)))
  set cT := 1 + |Real.log P.γ₁| / Real.log P.γ₂
  set A := (f x₀ - flow) / (P.η₁ * κΔm / 2)
  set Cc := Real.log (arSigmaMax P (L P.p) (ordMax P.p κg) / P.σ₀) / Real.log P.γ₂ + 2 +
    |Real.log P.γ₁| / Real.log P.γ₂
  set E := P.p * (P.q + 1) / |Real.log P.γh|
  set F := |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
    (arSigmaMax P (L P.p) (ordMax P.p κg))) (lipMax L P.p + ordMax P.p κg * P.κh)
    (arSigmaMax P (L P.p) (ordMax P.p κg)) (ordMax P.p κg) / P.κh)| / |Real.log P.γh| + 3
  refine ⟨(cT * A + |Cc|) + S.cost * (A + E + F),
    fun ε x σ δ δ₁ δs h D dd jk s acc hrun hrc _ => ?_⟩
  set m := epsMin P.q (fun j => ε j ^ arPi P.q P.p j)
  have hm : 0 < m := Chapter13.epsMin_pos P.one_le_q fun j hj =>
    Real.rpow_pos_of_pos (hrun.eps_mem j hj).1 _
  have hmε : m ≤ epsMin P.q ε := epsMin_rpow_arPi_le hrun.eps_mem
  have hε := hrun.epsMin_pos
  have hε1 := hrun.epsMin_le_one
  have hm1 : m ≤ 1 := hmε.trans hε1
  have hA := one_le_arConstA (hf.one_le le_rfl) hrun.kappaMax_nonneg (P := P) (L := L)
  have hLb := hrun.one_le_Lbar hf.on_univ
  have hκpos : 0 < κΔm := by
    have hk0 : 0 < arKappaHat P.q (1 - P.θ) (arConstA P L (ordMax P.p κg))
        (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
          (arSigmaMax P (L P.p) (ordMax P.p κg))) :=
      lt_min (arKappaDelta1_pos (by linarith))
        (div_pos (sub_pos.2 P.θ_lt_one) (by positivity))
    have hC : 0 < arStepConst P.q P.p (1 - P.θ) (arConstA P L (ordMax P.p κg))
        (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
          (arSigmaMax P (L P.p) (ordMax P.p κg))) := by
      have := sub_pos.2 P.θ_lt_one
      unfold arStepConst arStepConstOf
      split_ifs <;> positivity
    have := P.σmin_pos
    positivity
  have hc : 0 < P.η₁ * κΔm / 2 * m := by have := P.η₁_pos; positivity
  obtain ⟨kε, hk, h1, h2⟩ := arqpIDA_complexity hf hb hrun hrc hc fun k hk hρ hnot =>
    (lemma_13_1_18 hf hrun (hrc k) hk hρ hnot).2
  refine ⟨kε, hk, ?_⟩
  have hdiv : (f x₀ - flow) / (P.η₁ * κΔm / 2 * m) = A / m := (div_div _ _ _).symm
  rw [hdiv] at h1 h2
  have hlog : |Real.log (epsMin P.q ε)| ≤ 1 / m :=
    (abs_log_le_inv hε hε1).trans (one_div_le_one_div_of_le hm hmε)
  have hcT : 0 ≤ cT := by have := P.log_γ₂_pos; positivity
  have hE : 0 ≤ E := by positivity
  have hF : 0 ≤ F := by positivity
  have hdivm : ∀ {c : ℝ}, 0 ≤ c → c ≤ c / m := fun hc => le_div_self hc hm hm1
  have h1' : (derivEvalCount (fun i => ¬ acc i) kε : ℝ) ≤ (cT * A + |Cc|) / m := by
    calc _ ≤ cT * (A / m) + Cc := h1
      _ ≤ cT * (A / m) + |Cc| / m :=
          add_le_add le_rfl ((le_abs_self _).trans (hdivm (abs_nonneg _)))
      _ = (cT * A + |Cc|) / m := by ring
  have h2' : (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i)) kε :
      ℝ) ≤ (A + E + F) / m := by
    calc _ ≤ A / m + E * |Real.log (epsMin P.q ε)| + F := by
          have := h2; simp only [E, F] at this ⊢; linarith
      _ ≤ A / m + E * (1 / m) + F / m :=
          add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hlog hE)) (hdivm hF)
      _ = (A + E + F) / m := by ring
  have hcost : (0 : ℝ) ≤ S.cost := Nat.cast_nonneg _
  calc (derivEvalCount (fun i => ¬ acc i) kε : ℝ) + S.cost *
        derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i)) kε
      ≤ (cT * A + |Cc|) / m + S.cost * ((A + E + F) / m) :=
        add_le_add h1' (mul_le_mul_of_nonneg_left h2' hcost)
    _ = ((cT * A + |Cc|) + S.cost * (A + E + F)) / m := by ring

end AR

/-! ### Runs driven by a scheme -/

section Existence

/-- **TRqIDA runs driven by a scheme exist**: for every finite derivative-approximation scheme `S`
producing derivatives up to degree `q`, there is a TRqIDA run with `D_k = S.est x_k h_k`
(the hypothesis of `theorem_13_2_1_i`). -/
theorem exists_algorithm_13_1_1_of_scheme {f : ℝⁿ → ℝ} {κg : ℕ → ℝ} {P : TRqIDAParams}
    {ε : ℕ → ℝ} (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1) (hϑ : epsMin P.q ε ≤ P.ϑ)
    (hκg : ∀ i ∈ Finset.Icc 1 P.q, 0 ≤ κg i) {o : ℕ} (S : FiniteDerivativeApproxScheme f o P.q κg)
    (x₀ : ℝⁿ) :
    ∃ (x : ℕ → ℝⁿ) (Δ : ℕ → ℝ) (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ)
      (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ) (acc : ℕ → Prop),
      algorithm_13_1_1 f κg P ε x₀ x Δ h D dd jk s acc ∧ ∀ k, D k = S.est (x k) (h k) :=
  exists_algorithm_13_1_1 hε hϑ hκg x₀ S.est S.approx

/-- **ARqpIDA runs driven by a scheme exist**: for every finite derivative-approximation scheme
`S` producing derivatives up to degree `p` and positive initial accuracies, there is an ARqpIDA
run with `D_k = S.est x_k h_k` and the radii control (the hypotheses of `theorem_13_2_1_ii`). -/
theorem exists_algorithm_13_1_2_of_scheme {f : ℝⁿ → ℝ} {κg : ℕ → ℝ} {P : ARqpIDAParams}
    {ε : ℕ → ℝ} {L : ℕ → ℝ} (hf : AssumptionD0pL f P.p L)
    (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1) (hεδ : ∀ j ∈ Finset.Icc 1 P.q, ε j ≤ P.δ₀ j)
    (hκg : ∀ i ∈ Finset.Icc 1 P.p, 0 ≤ κg i) (hh₀ : ∀ i ∈ Finset.Icc 1 P.p, 0 < P.h₀ i) {o : ℕ}
    (S : FiniteDerivativeApproxScheme f o P.p κg) (x₀ : ℝⁿ) :
    ∃ (x : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ)
      (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ) (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ)
      (acc : ℕ → Prop), algorithm_13_1_2 f κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc ∧
        (∀ k, D k = S.est (x k) (h k)) ∧
        ∀ k, RadiiControl P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc k :=
  exists_algorithm_13_1_2 S.est hf hε hεδ hκg hh₀ x₀ fun y h' hh =>
    S.approx y h' fun i hi => (hh i hi).1

/-- **TRqIDA with forward-difference gradients** (`q = 1`, function values only): runs exist with
`D_k = gradientJet (∇ f(x_k) estimated by forward differences with step h_{k,1})`, for `∇f`
`L`-Lipschitz (`κ_{∇,1} = √n L/2`). -/
theorem exists_algorithm_13_1_1_fdGradient {f : ℝⁿ → ℝ} {P : TRqIDAParams} {ε : ℕ → ℝ}
    {L : ℝ} (hq : P.q = 1) (hf : ContDiff ℝ 1 f)
    (hL : ∀ y z, ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ L * ‖y - z‖) (hL0 : 0 ≤ L)
    (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1) (hϑ : epsMin P.q ε ≤ P.ϑ) (x₀ : ℝⁿ) :
    ∃ (x : ℕ → ℝⁿ) (Δ : ℕ → ℝ) (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ)
      (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ) (acc : ℕ → Prop),
      algorithm_13_1_1 f (fun _ => √n * L / 2) P ε x₀ x Δ h D dd jk s acc ∧
        ∀ k, D k = gradientJet (ftaylorSeries ℝ f (x k))
          (FiniteDifference.fdGradient f (h k 1) (x k)) :=
  exists_algorithm_13_1_1 hε hϑ (fun _ _ => by positivity) x₀
    (fdGradientScheme f hf hL).est fun y h' hh => by
      rw [hq]; exact (fdGradientScheme f hf hL).approx y h' (hq ▸ hh)

end Existence

end CartisGouldToint.Chapter13

import Mathlib.MeasureTheory.Integral.Prod
import Numlib.Analysis.Normed.Operator.CollectivelyCompact
import Numlib.Approximation.Quadrature
import Numlib.IntegralEquations.Basic

/-!
# Nyström operators

The **Nyström operator** of a quadrature rule `(w, x)` and a continuous kernel `k` is

`K_n u (t) = ∑ j, w j * k (t, x j) * u (x j)`,

the operator obtained from the kernel integral operator `IntegralOperator.kernelCLM` by replacing
the integral with the rule. It is a finite-rank operator on `C(X, ℝ)`, and the family of Nyström
operators attached to a sequence of rules with uniformly bounded absolute weight sums is
*collectively compact* — it converges pointwise to the integral operator without converging in
operator norm, which is precisely the situation Anselone's theory was built for.

Everything here is one observation: for a fixed row index `t`, both `kernelCLM μ k u t` and
`nystromCLM w x k u t` are *bounded linear functionals evaluated at the same integrand*
`IntegralOperator.rowMul k u t : C(X, ℝ)`, namely `y ↦ k (t, y) * u y`. The integrand depends
continuously on `t`, so it ranges over a compact subset of `C(X, ℝ)`, on which pointwise
convergence of functionals is uniform (`tendstoUniformlyOn_of_tendsto_of_isCompact`). That single
argument gives the pointwise convergence `K_n u → K u` in the *uniform* norm and the uniform
convergence of the composition kernels below.

## Main definitions

* `IntegralOperator.integralCLM` — integration against a finite measure, as a functional on
  `C(X, ℝ)`; it is the target functional of which a quadrature rule is an approximation.
* `IntegralOperator.nystromCLM` — the Nyström operator, with `IntegralOperator.norm_nystromCLM`
  computing its operator norm as `max_t ∑ j |w j * k (t, x j)|`.
* `IntegralOperator.compKernel` — the kernel `e (t, s) = ∫ k (t, v) k (v, s) dv - ∑ j w j k (t, x j)
  k (x j, s)` measuring the quadrature error on the composed kernel.

## Main statements

* `IntegralOperator.tendsto_nystromCLM` — a convergent quadrature rule makes `K_n u → K u` in
  `C(X, ℝ)`, uniformly in the argument.
* `IntegralOperator.isCollectivelyCompact_nystromCLM` — uniformly bounded absolute weight sums make
  the family collectively compact, by Arzelà–Ascoli.
* `IntegralOperator.kernelCLM_sub_nystromCLM_comp_kernelCLM` and
  `IntegralOperator.kernelCLM_sub_nystromCLM_comp_nystromCLM` — the two composition identities
  `(K - K_n) K = kernelCLM e` and `(K - K_n) K_n = nystromCLM e`, which turn the operator norms of
  the compositions into norms of the single kernel `e`.
* `IntegralOperator.tendsto_norm_compKernel` — and `‖e‖ → 0` for a convergent rule.

## References

[han2009theoretical], §12.4 (Lemma 12.4.2 and Theorem 12.4.4); [anselone1971collectively];
[kress1989linear], §12.2.
-/

open Filter MeasureTheory Metric Set Topology

namespace IntegralOperator

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-! ### Rows and columns of a kernel -/

/-- The **row** `y ↦ k (t, y)` of a continuous kernel, as a continuous family of continuous
functions indexed by the row index. -/
noncomputable def row (k : C(X × X, ℝ)) : C(X, C(X, ℝ)) := k.curry

omit [CompactSpace X] in
@[simp]
theorem row_apply (k : C(X × X, ℝ)) (t s : X) : row k t s = k (t, s) := rfl

/-- The **column** `t ↦ k (t, s)` of a continuous kernel. -/
def col (k : C(X × X, ℝ)) (s : X) : C(X, ℝ) :=
  ⟨fun t => k (t, s), by fun_prop⟩

omit [CompactSpace X] in
@[simp]
theorem col_apply (k : C(X × X, ℝ)) (s t : X) : col k s t = k (t, s) := rfl

/-- The integrand `y ↦ k (t, y) * u y` of a kernel operator, as a continuous family indexed by the
row index `t`. Both the integral operator and its Nyström approximation are a bounded functional
applied to this family. -/
noncomputable def rowMul (k : C(X × X, ℝ)) (u : C(X, ℝ)) : C(X, C(X, ℝ)) :=
  ContinuousMap.curry ⟨fun p => k p * u p.2, by fun_prop⟩

omit [CompactSpace X] in
@[simp]
theorem rowMul_apply (k : C(X × X, ℝ)) (u : C(X, ℝ)) (t s : X) :
    rowMul k u t s = k (t, s) * u s := rfl

/-- The integrand `v ↦ k (t, v) * k (v, s)` of the composed kernel, as a continuous family indexed
by the pair `(t, s)`. -/
noncomputable def rowCol (k : C(X × X, ℝ)) : C(X × X, C(X, ℝ)) :=
  ContinuousMap.curry ⟨fun p : (X × X) × X => k (p.1.1, p.2) * k (p.2, p.1.2), by fun_prop⟩

omit [CompactSpace X] in
@[simp]
theorem rowCol_apply (k : C(X × X, ℝ)) (p : X × X) (v : X) :
    rowCol k p v = k (p.1, v) * k (v, p.2) := rfl

/-! ### Integration as a functional -/

section Integral

variable [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]

/-- **Integration against a finite measure**, as a bounded linear functional on the continuous
functions of a compact space. A quadrature rule (`Quadrature.functional`) is an approximation to
this functional. -/
noncomputable def integralCLM : C(X, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun u => ∫ y, u y ∂μ
      map_add' := fun u v => by
        simp only [ContinuousMap.add_apply]
        exact integral_add (integrable_of_continuousMap μ u) (integrable_of_continuousMap μ v)
      map_smul' := fun r u => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        exact integral_const_mul r _ }
    (μ.real univ) fun u => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      calc ‖∫ y, u y ∂μ‖
          ≤ ‖u‖ * μ.real univ :=
            norm_integral_le_of_norm_le_const
              (Filter.Eventually.of_forall fun y => u.norm_coe_le_norm y)
        _ = μ.real univ * ‖u‖ := mul_comm _ _

@[simp]
theorem integralCLM_apply (u : C(X, ℝ)) : integralCLM μ u = ∫ y, u y ∂μ := rfl

/-- A continuous function on a compact space is integrable for every finite measure; the unbundled
form of `IntegralOperator.integrable_of_continuousMap`. -/
theorem integrable_of_continuous {f : X → ℝ} (hf : Continuous f) : Integrable f μ :=
  integrable_of_continuousMap μ ⟨f, hf⟩

/-- A kernel operator is integration applied to the row integrands. -/
theorem kernelCLM_apply_eq_integralCLM (k : C(X × X, ℝ)) (u : C(X, ℝ)) (t : X) :
    kernelCLM μ k u t = integralCLM μ (rowMul k u t) := rfl

/-- Negating the kernel negates the kernel operator. -/
@[simp]
theorem kernelCLM_neg (k : C(X × X, ℝ)) : kernelCLM μ (-k) = -kernelCLM μ k := by
  refine ContinuousLinearMap.ext fun u => ContinuousMap.ext fun t => ?_
  rw [neg_apply, ContinuousMap.neg_apply, kernelCLM_apply, kernelCLM_apply, ← integral_neg]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => by simp)

end Integral

/-! ### The Nyström operator -/

section Nystrom

variable {m : ℕ} {w : Fin m → ℝ} {x : Fin m → X} {k : C(X × X, ℝ)}

/-- **The Nyström operator** of a quadrature rule with weights `w` and nodes `x` and a continuous
kernel `k`: the finite-rank operator

`K_n u (t) = ∑ j, w j * k (t, x j) * u (x j)`

on `C(X, ℝ)`, obtained from `IntegralOperator.kernelCLM` by replacing the integral with the rule.

Reference: [han2009theoretical], (12.4.4). -/
noncomputable def nystromCLM {m : ℕ} (w : Fin m → ℝ) (x : Fin m → X) (k : C(X × X, ℝ)) :
    C(X, ℝ) →L[ℝ] C(X, ℝ) :=
  ∑ j, (w j • ContinuousMap.evalCLM ℝ (x j)).smulRight (col k (x j))

/-- The defining formula of the Nyström operator. -/
@[simp]
theorem nystromCLM_apply (w : Fin m → ℝ) (x : Fin m → X) (k : C(X × X, ℝ)) (u : C(X, ℝ)) (t : X) :
    nystromCLM w x k u t = ∑ j, w j * k (t, x j) * u (x j) := by
  simp only [nystromCLM, sum_apply, ContinuousMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, smul_apply,
    ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply, smul_eq_mul, col_apply]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Negating the kernel negates the Nyström operator. -/
@[simp]
theorem nystromCLM_neg (w : Fin m → ℝ) (x : Fin m → X) (k : C(X × X, ℝ)) :
    nystromCLM w x (-k) = -nystromCLM w x k := by
  refine ContinuousLinearMap.ext fun u => ContinuousMap.ext fun t => ?_
  rw [neg_apply, ContinuousMap.neg_apply, nystromCLM_apply, nystromCLM_apply,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by simp

/-- The Nyström operator is the quadrature rule applied to the row integrands, exactly as the
kernel operator is the integral applied to them. -/
theorem nystromCLM_apply_eq_functional (w : Fin m → ℝ) (x : Fin m → X) (k : C(X × X, ℝ))
    (u : C(X, ℝ)) (t : X) :
    nystromCLM w x k u t = Quadrature.functional w x (rowMul k u t) := by
  rw [Quadrature.functional_apply, nystromCLM_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [rowMul_apply, mul_assoc]

/-- Every uniform bound on the absolute sums `∑ j |w j k (t, x j)|` bounds the operator norm of a
Nyström operator; this is the easy half of `IntegralOperator.norm_nystromCLM`. -/
theorem norm_nystromCLM_le {C : ℝ} (hC : 0 ≤ C) (h : ∀ t, ∑ j, |w j * k (t, x j)| ≤ C) :
    ‖nystromCLM w x k‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun u => ?_
  rw [ContinuousMap.norm_le _ (mul_nonneg hC (norm_nonneg u))]
  intro t
  rw [nystromCLM_apply, Real.norm_eq_abs]
  calc |∑ j, w j * k (t, x j) * u (x j)|
      ≤ ∑ j, |w j * k (t, x j) * u (x j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |w j * k (t, x j)| * ‖u‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (u.norm_coe_le_norm _) (abs_nonneg _)
    _ = (∑ j, |w j * k (t, x j)|) * ‖u‖ := by rw [Finset.sum_mul]
    _ ≤ C * ‖u‖ := mul_le_mul_of_nonneg_right (h t) (norm_nonneg u)

/-- **The operator norm of a Nyström operator** is the largest absolute weight sum of its rows,
`‖K_n‖ = max_t ∑ j |w j k (t, x j)|`, the exact analogue of
`IntegralOperator.norm_kernelCLM` for a quadrature rule in place of an integral.

The lower bound is `Quadrature.norm_functional`, applied to the rule with weights
`w j * k (t₀, x j)` at a row index `t₀` maximizing the sum: that rule is the Nyström operator read
off at `t₀`, so its norm is at most `‖K_n‖`.

Reference: [han2009theoretical], (12.4.17). -/
theorem norm_nystromCLM [T2Space X] [Nonempty X] (hx : Function.Injective x) :
    ‖nystromCLM w x k‖ = ⨆ t, ∑ j, |w j * k (t, x j)| := by
  set g : C(X, ℝ) :=
    ⟨fun t => ∑ j, |w j * k (t, x j)|, by fun_prop⟩ with hg
  have hgapp : ∀ t, g t = ∑ j, |w j * k (t, x j)| := fun _ => rfl
  have hgnonneg : ∀ t, 0 ≤ g t := fun t => by
    rw [hgapp]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨t₀, -, ht₀⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty g.continuous.continuousOn
  have hmax : ∀ t, g t ≤ g t₀ := fun t => isMaxOn_iff.1 ht₀ t (mem_univ t)
  have hsup : ⨆ t, ∑ j, |w j * k (t, x j)| = g t₀ :=
    le_antisymm (ciSup_le hmax) (le_ciSup ⟨g t₀, by rintro _ ⟨t, rfl⟩; exact hmax t⟩ t₀)
  rw [hsup]
  refine le_antisymm (norm_nystromCLM_le (hgnonneg t₀) hmax) ?_
  -- the rule with weights `w j * k (t₀, x j)` is the Nyström operator read off at `t₀`
  have hrow : ‖Quadrature.functional (fun j => w j * k (t₀, x j)) x‖ ≤ ‖nystromCLM w x k‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun u => ?_
    have hval : Quadrature.functional (fun j => w j * k (t₀, x j)) x u
        = nystromCLM w x k u t₀ := by
      rw [Quadrature.functional_apply, nystromCLM_apply]
    rw [hval, Real.norm_eq_abs, ← Real.norm_eq_abs]
    calc ‖nystromCLM w x k u t₀‖ ≤ ‖nystromCLM w x k u‖ :=
          (nystromCLM w x k u).norm_coe_le_norm t₀
      _ ≤ ‖nystromCLM w x k‖ * ‖u‖ := (nystromCLM w x k).le_opNorm u
  rwa [Quadrature.norm_functional _ hx, ← hgapp] at hrow

end Nystrom

/-! ### Uniform convergence along a continuous family of integrands -/

/-- **Pointwise convergence of functionals is uniform along a continuous family of integrands.**
If `A n → L` pointwise on `C(X, ℝ)` and `F` is a continuous family of integrands indexed by a
compact space, then `sup_y |L (F y) - A n (F y)| → 0`.

The range of `F` is a compact subset of `C(X, ℝ)`, and a pointwise convergent sequence of bounded
operators converges uniformly on compact sets
(`tendstoUniformlyOn_of_tendsto_of_isCompact`). This is the only analytic ingredient of the
Nyström theory below. -/
theorem tendsto_norm_of_tendsto_functional {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    {A : ℕ → C(X, ℝ) →L[ℝ] ℝ} {L : C(X, ℝ) →L[ℝ] ℝ}
    (hA : ∀ v, Tendsto (fun n => A n v) atTop (𝓝 (L v))) (F : C(Y, C(X, ℝ)))
    {g : ℕ → C(Y, ℝ)} (hg : ∀ n y, g n y = L (F y) - A n (F y)) :
    Tendsto (fun n => ‖g n‖) atTop (𝓝 0) := by
  have hS : IsCompact (Set.range F) := isCompact_range (map_continuous F)
  have hunif : TendstoUniformlyOn (fun n => (A n : C(X, ℝ) → ℝ)) L atTop (Set.range F) :=
    tendstoUniformlyOn_of_tendsto_of_isCompact hA hS
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hunif (ε / 2) (by positivity))
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  have hle : ‖g n‖ ≤ ε / 2 := by
    rw [ContinuousMap.norm_le _ (by positivity)]
    intro y
    rw [hg n y, Real.norm_eq_abs, ← Real.dist_eq]
    exact (hN n hn (F y) ⟨y, rfl⟩).le
  linarith

/-! ### The Nyström family of a sequence of quadrature rules -/

section Family

variable [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
  {m : ℕ → ℕ} {w : ∀ n, Fin (m n) → ℝ} {x : ∀ n, Fin (m n) → X} {k : C(X × X, ℝ)}

/-- **A convergent quadrature rule makes the Nyström operators converge pointwise** to the integral
operator, in the uniform norm of `C(X, ℝ)`.

This is assumption A2 of the collectively compact framework; note that it is *not* accompanied by
convergence in operator norm, which fails. [han2009theoretical], §12.4.1. -/
theorem tendsto_nystromCLM
    (hQ : ∀ v : C(X, ℝ), Tendsto (fun n => Quadrature.functional (w n) (x n) v) atTop
      (𝓝 (integralCLM μ v))) (u : C(X, ℝ)) :
    Tendsto (fun n => nystromCLM (w n) (x n) k u) atTop (𝓝 (kernelCLM μ k u)) := by
  have hg : ∀ n t, (kernelCLM μ k u - nystromCLM (w n) (x n) k u) t
      = integralCLM μ (rowMul k u t) - Quadrature.functional (w n) (x n) (rowMul k u t) := by
    intro n t
    rw [ContinuousMap.sub_apply, kernelCLM_apply_eq_integralCLM,
      nystromCLM_apply_eq_functional]
  have h := tendsto_norm_of_tendsto_functional hQ (rowMul k u) hg
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [norm_sub_rev] using h

omit [MeasurableSpace X] [BorelSpace X] in
/-- **The Nyström family of a sequence of rules with uniformly bounded absolute weight sums is
collectively compact.**

The images of the closed unit ball are uniformly bounded by `W ‖k‖` and equicontinuous, because
the oscillation of `K_n u` between two row indices is at most `W ‖u‖` times the uniform distance
between the corresponding rows of `k`; Arzelà–Ascoli then applies. This is assumption A3, and the
book's (12.4.3) is exactly the hypothesis `hW`. [han2009theoretical], §12.4.1. -/
theorem isCollectivelyCompact_nystromCLM (k : C(X × X, ℝ)) {W : ℝ}
    (hW : ∀ n, ∑ j, |w n j| ≤ W) :
    IsCollectivelyCompact (fun n => nystromCLM (w n) (x n) k) := by
  have hW0 : 0 ≤ W := le_trans (Finset.sum_nonneg fun _ _ => abs_nonneg _) (hW 0)
  refine ⟨closedBall 0 1, closedBall_mem_nhds 0 one_pos, ?_⟩
  -- the pointwise bound `|K_n u t| ≤ W ‖k‖`, uniform in `n`, `u` and `t`
  have hbdd : ∀ n (u : C(X, ℝ)), ‖u‖ ≤ 1 → ∀ t s : X,
      |nystromCLM (w n) (x n) k u t - nystromCLM (w n) (x n) k u s|
        ≤ W * ‖row k t - row k s‖ := by
    intro n u hu t s
    have hstep : ∀ j, |w n j * k (t, x n j) * u (x n j) - w n j * k (s, x n j) * u (x n j)|
        ≤ |w n j| * ‖row k t - row k s‖ := by
      intro j
      have h1 : |k (t, x n j) - k (s, x n j)| ≤ ‖row k t - row k s‖ := by
        have := (row k t - row k s).norm_coe_le_norm (x n j)
        simpa [Real.norm_eq_abs] using this
      have h2 : |u (x n j)| ≤ 1 := le_trans (by simpa using u.norm_coe_le_norm (x n j)) hu
      have hrw : w n j * k (t, x n j) * u (x n j) - w n j * k (s, x n j) * u (x n j)
          = w n j * ((k (t, x n j) - k (s, x n j)) * u (x n j)) := by ring
      rw [hrw, abs_mul, abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      calc |k (t, x n j) - k (s, x n j)| * |u (x n j)|
          ≤ ‖row k t - row k s‖ * 1 := by
            refine mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
        _ = ‖row k t - row k s‖ := mul_one _
    rw [nystromCLM_apply, nystromCLM_apply, ← Finset.sum_sub_distrib]
    calc |∑ j, (w n j * k (t, x n j) * u (x n j) - w n j * k (s, x n j) * u (x n j))|
        ≤ ∑ j, |w n j * k (t, x n j) * u (x n j) - w n j * k (s, x n j) * u (x n j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |w n j| * ‖row k t - row k s‖ := Finset.sum_le_sum fun j _ => hstep j
      _ = (∑ j, |w n j|) * ‖row k t - row k s‖ := by rw [Finset.sum_mul]
      _ ≤ W * ‖row k t - row k s‖ :=
          mul_le_mul_of_nonneg_right (hW n) (norm_nonneg _)
  refine ContinuousMap.isCompact_closure_of_forall_norm_le (M := W * ‖k‖) ?_ ?_
  · rintro f hf t
    obtain ⟨n, u, hu, rfl⟩ := Set.mem_iUnion.1 hf
    have hu1 : ‖u‖ ≤ 1 := mem_closedBall_zero_iff.1 hu
    have hstep : ∀ j, |w n j * k (t, x n j) * u (x n j)| ≤ |w n j| * ‖k‖ := by
      intro j
      have h1 : |k (t, x n j)| ≤ ‖k‖ := by simpa using k.norm_coe_le_norm (t, x n j)
      have h2 : |u (x n j)| ≤ 1 := le_trans (by simpa using u.norm_coe_le_norm (x n j)) hu1
      rw [abs_mul, abs_mul, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      calc |k (t, x n j)| * |u (x n j)| ≤ ‖k‖ * 1 :=
            mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
        _ = ‖k‖ := mul_one _
    rw [nystromCLM_apply, Real.norm_eq_abs]
    calc |∑ j, w n j * k (t, x n j) * u (x n j)|
        ≤ ∑ j, |w n j * k (t, x n j) * u (x n j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |w n j| * ‖k‖ := Finset.sum_le_sum fun j _ => hstep j
      _ = (∑ j, |w n j|) * ‖k‖ := by rw [Finset.sum_mul]
      _ ≤ W * ‖k‖ := mul_le_mul_of_nonneg_right (hW n) (norm_nonneg _)
  · intro t₀
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    have hcont : Continuous fun t => W * ‖row k t₀ - row k t‖ := by fun_prop
    have hlim : Tendsto (fun t => W * ‖row k t₀ - row k t‖) (𝓝 t₀) (𝓝 0) := by
      have := hcont.tendsto t₀
      simpa using this
    filter_upwards [hlim.eventually_lt_const hε] with t ht
    rintro ⟨f, hf⟩
    obtain ⟨n, u, hu, rfl⟩ := Set.mem_iUnion.1 hf
    have hu1 : ‖u‖ ≤ 1 := mem_closedBall_zero_iff.1 hu
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (hbdd n u hu1 t₀ t) ht

end Family

/-! ### The composition kernel -/

section Composition

variable [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]

/-- **The quadrature error of the composed kernel**,

`e (t, s) = ∫ k (t, v) k (v, s) dv - ∑ j w j k (t, x j) k (x j, s)`.

The two compositions `(K - K_n) K` and `(K - K_n) K_n` are the kernel operator and the Nyström
operator of this single kernel, so their operator norms are read off it.

Reference: [han2009theoretical], (12.4.15). -/
noncomputable def compKernel {m : ℕ} (w : Fin m → ℝ) (x : Fin m → X) (k : C(X × X, ℝ)) :
    C(X × X, ℝ) :=
  ⟨fun p => integralCLM μ (rowCol k p) - Quadrature.functional w x (rowCol k p), by
    exact ((integralCLM μ).continuous.comp (map_continuous (rowCol k))).sub
      ((Quadrature.functional w x).continuous.comp (map_continuous (rowCol k)))⟩

@[simp]
theorem compKernel_apply {m : ℕ} (w : Fin m → ℝ) (x : Fin m → X) (k : C(X × X, ℝ)) (p : X × X) :
    compKernel μ w x k p =
      (∫ v, k (p.1, v) * k (v, p.2) ∂μ) - ∑ j, w j * (k (p.1, x j) * k (x j, p.2)) := by
  change integralCLM μ (rowCol k p) - Quadrature.functional w x (rowCol k p) = _
  rw [integralCLM_apply, Quadrature.functional_apply]
  simp only [rowCol_apply]

/-- **The quadrature error of the composed kernel tends to zero uniformly** for a convergent
quadrature rule: the integrands `v ↦ k (t, v) k (v, s)` form a continuous family indexed by the
compact space `X × X`. [han2009theoretical], (12.4.18). -/
theorem tendsto_norm_compKernel {m : ℕ → ℕ} {w : ∀ n, Fin (m n) → ℝ} {x : ∀ n, Fin (m n) → X}
    (k : C(X × X, ℝ))
    (hQ : ∀ v : C(X, ℝ), Tendsto (fun n => Quadrature.functional (w n) (x n) v) atTop
      (𝓝 (integralCLM μ v))) :
    Tendsto (fun n => ‖compKernel μ (w n) (x n) k‖) atTop (𝓝 0) :=
  tendsto_norm_of_tendsto_functional hQ (rowCol k) fun _ _ => rfl

variable {m : ℕ} (w : Fin m → ℝ) (x : Fin m → X) (k : C(X × X, ℝ))

/-- **The first composition identity**: `(K - K_n) K` is the kernel operator of the composition
kernel `e`.

This is where Fubini's theorem enters, and the only place: the double integral
`∫ k (t, v) ∫ k (v, s) u s ds dv` is rewritten with the order of integration reversed, which is why
a second-countable domain is assumed here and nowhere else.

Reference: [han2009theoretical], (12.4.14). -/
theorem kernelCLM_sub_nystromCLM_comp_kernelCLM [SecondCountableTopology X] :
    (kernelCLM μ k - nystromCLM w x k) ∘L kernelCLM μ k = kernelCLM μ (compKernel μ w x k) := by
  refine ContinuousLinearMap.ext fun u => ContinuousMap.ext fun t => ?_
  -- the two halves of the composition kernel, as continuous functions of the column index
  have hAcont : Continuous fun s : X => ∫ v, k (t, v) * k (v, s) ∂μ :=
    continuous_integral_row μ ⟨fun p => k (t, p.2) * k (p.2, p.1), by fun_prop⟩
  have hBcont : Continuous fun s : X => ∑ j, w j * (k (t, x j) * k (x j, s)) := by fun_prop
  have hA : Integrable (fun s => (∫ v, k (t, v) * k (v, s) ∂μ) * u s) μ :=
    integrable_of_continuous μ (hAcont.mul u.continuous)
  have hB : Integrable (fun s => (∑ j, w j * (k (t, x j) * k (x j, s))) * u s) μ :=
    integrable_of_continuous μ (hBcont.mul u.continuous)
  -- Fubini on the double integral
  have hint : Integrable
      (Function.uncurry fun v s : X => k (t, v) * k (v, s) * u s) (μ.prod μ) := by
    have hc : Continuous (Function.uncurry fun v s : X => k (t, v) * k (v, s) * u s) := by
      unfold Function.uncurry
      fun_prop
    refine (integrable_const (‖k‖ * ‖k‖ * ‖u‖)).mono' hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    have h1 : |k (t, p.1)| ≤ ‖k‖ := by simpa using k.norm_coe_le_norm (t, p.1)
    have h2 : |k (p.1, p.2)| ≤ ‖k‖ := by simpa using k.norm_coe_le_norm (p.1, p.2)
    have h3 : |u p.2| ≤ ‖u‖ := by simpa using u.norm_coe_le_norm p.2
    have hk : (0 : ℝ) ≤ ‖k‖ := norm_nonneg k
    change ‖k (t, p.1) * k (p.1, p.2) * u p.2‖ ≤ ‖k‖ * ‖k‖ * ‖u‖
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) hk) h3 (abs_nonneg _)
      (mul_nonneg hk hk)
  have hL : ∀ v : X, (∫ s, k (t, v) * k (v, s) * u s ∂μ) = k (t, v) * ∫ s, k (v, s) * u s ∂μ := by
    intro v
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun s => by ring)
  have hfub : (∫ v, k (t, v) * (∫ s, k (v, s) * u s ∂μ) ∂μ)
      = ∫ s, (∫ v, k (t, v) * k (v, s) ∂μ) * u s ∂μ :=
    calc (∫ v, k (t, v) * (∫ s, k (v, s) * u s ∂μ) ∂μ)
        = ∫ v, ∫ s, k (t, v) * k (v, s) * u s ∂μ ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall fun v => (hL v).symm)
      _ = ∫ s, ∫ v, k (t, v) * k (v, s) * u s ∂μ ∂μ := integral_integral_swap hint
      _ = ∫ s, (∫ v, k (t, v) * k (v, s) ∂μ) * u s ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall fun s => integral_mul_const _ _)
  -- the finite sum comes out of the integral
  have hterm : ∀ j : Fin m,
      Integrable (fun s => w j * k (t, x j) * (k (x j, s) * u s)) μ := fun j =>
    (integrable_kernel_mul μ k u (x j)).const_mul _
  have hsum : (∫ s, (∑ j, w j * (k (t, x j) * k (x j, s))) * u s ∂μ)
      = ∑ j, w j * k (t, x j) * ∫ s, k (x j, s) * u s ∂μ := by
    rw [show (fun s => (∑ j, w j * (k (t, x j) * k (x j, s))) * u s)
        = fun s => ∑ j, w j * k (t, x j) * (k (x j, s) * u s) from
      funext fun s => by rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring,
      integral_finsetSum _ fun j _ => hterm j]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  rw [ContinuousLinearMap.comp_apply, sub_apply, ContinuousMap.sub_apply,
    kernelCLM_apply, nystromCLM_apply, kernelCLM_apply]
  simp only [kernelCLM_apply, compKernel_apply]
  rw [integral_congr_ae (Filter.Eventually.of_forall fun s =>
      (sub_mul (∫ v, k (t, v) * k (v, s) ∂μ) (∑ j, w j * (k (t, x j) * k (x j, s))) (u s))),
    integral_sub hA hB, ← hfub, ← hsum]

/-- **The second composition identity**: `(K - K_n) K_n` is the *Nyström* operator of the same
composition kernel `e`. Only linearity of the integral over a finite sum is used, so no
second-countability is needed here.

Reference: [han2009theoretical], (12.4.14). -/
theorem kernelCLM_sub_nystromCLM_comp_nystromCLM :
    (kernelCLM μ k - nystromCLM w x k) ∘L nystromCLM w x k
      = nystromCLM w x (compKernel μ w x k) := by
  refine ContinuousLinearMap.ext fun u => ContinuousMap.ext fun t => ?_
  have hterm : ∀ i : Fin m, Integrable (fun v => w i * u (x i) * (k (t, v) * k (v, x i))) μ :=
    fun i => (integrable_kernel_mul μ k (col k (x i)) t).const_mul _
  have hfirst : (∫ v, k (t, v) * ∑ i, w i * k (v, x i) * u (x i) ∂μ)
      = ∑ i, w i * u (x i) * ∫ v, k (t, v) * k (v, x i) ∂μ := by
    rw [show (fun v => k (t, v) * ∑ i, w i * k (v, x i) * u (x i))
        = fun v => ∑ i, w i * u (x i) * (k (t, v) * k (v, x i)) from
      funext fun v => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring,
      integral_finsetSum _ fun i _ => hterm i]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  have hswap : (∑ j, w j * k (t, x j) * ∑ i, w i * k (x j, x i) * u (x i))
      = ∑ i, w i * u (x i) * ∑ j, w j * (k (t, x j) * k (x j, x i)) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [ContinuousLinearMap.comp_apply, sub_apply, ContinuousMap.sub_apply,
    kernelCLM_apply, nystromCLM_apply, nystromCLM_apply]
  simp only [nystromCLM_apply, compKernel_apply]
  rw [hfirst, hswap, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

end Composition

end IntegralOperator

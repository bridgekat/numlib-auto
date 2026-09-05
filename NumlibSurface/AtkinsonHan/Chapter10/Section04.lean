import Numlib.Variational.AubinNitsche
import NumlibSurface.AtkinsonHan.Chapter09.Section01

/-!
# Atkinson–Han §10.4: the Aubin–Nitsche lemma

Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional Analysis
Framework*, 3rd edition, Springer, 2009.

The book states Theorem 10.4.3 for `V ⊆ H¹(Ω)` and `H = L²(Ω)`; the surface states it for a real
inner product space `V`, a real inner product space `H`, and a continuous linear `ι : V →L[ℝ] H`
standing for the embedding, which is the whole of what the proof uses.  The supremum over the data
`g ∈ H` and the infimum over the finite element space are kept, since they are the book's statement
(10.4.5); both are junk-free because the quantities involved are nonnegative and bounded, and the
boundedness comes from the Lax–Milgram bound `norm_le_of_dualProblem` on the dual solution.

## Main results

* `DualProblem` — the dual (adjoint) problem (10.4.4) `a(v, φ_g) = (g, ι v)_H`.
* `norm_le_of_dualProblem` — its Lax–Milgram stability estimate `‖φ_g‖ ≤ (‖ι‖/c₀) ‖g‖`, which is
  what makes the supremum in (10.4.5) finite.
* `theorem_10_4_3` — the Aubin–Nitsche lemma (10.4.5).
* `corollary_10_4_4_abstract` — Corollary 10.4.4 with its regularity hypothesis made abstract.

## Not formalized here

Almost the whole of Chapter 10 is out of scope for want of Sobolev spaces in Mathlib.  Left out of
this file: Theorem 10.4.1 (the convergence order of the finite element method, which needs the
interpolation error estimate of §10.3), Corollary 10.4.4 in its stated form (its hypothesis
(10.4.9) is an elliptic regularity bound), and (10.4.11).  The abstract half of Corollary 10.4.4,
in which the approximation power of the dual solutions is a hypothesis, is
`corollary_10_4_4_abstract`.
-/

namespace AtkinsonHan

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H]

/-- The dual problem (10.4.4) for the datum `g ∈ H`: `φ ∈ V` with `a(v, φ) = (g, ι v)_H` for every
`v ∈ V`.  It is the variational problem for the adjoint form, so on a `V`-elliptic `a` it is
uniquely solvable by Lax–Milgram (Theorem 8.3.4) applied to `a(·, ·)ᵀ`. -/
def DualProblem (a : BilinForm V) (ι : V →L[ℝ] H) (g : H) (φ : V) : Prop :=
  ∀ v : V, a v φ = inner ℝ (ι v) g

namespace Ch10

variable {a : BilinForm V} {ℓ : StrongDual ℝ V} {M c₀ δ : ℝ} {Vh : Submodule ℝ V} {u uh : V}

/-- The infimum over a subspace, as the book writes it, is the distance to that subspace.  This is
the bridge between the `inf_{v_h ∈ V_h}` of (10.4.5) and the `Metric.infDist` in which
`corollary_10_4_4_abstract` states its approximation hypothesis. -/
theorem iInf_norm_sub_eq_infDist (w : V) (K : Submodule ℝ V) :
    (⨅ v : K, ‖w - (v : V)‖) = Metric.infDist w (K : Set V) := by
  simp [Metric.infDist_eq_iInf, dist_eq_norm]

/-- The infimum over a subspace is bounded below by `0`. -/
private theorem bddBelow_norm_sub (w : V) (K : Submodule ℝ V) :
    BddBelow (Set.range fun v : K => ‖w - (v : V)‖) :=
  ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩

/-- Lax–Milgram stability for the dual problem (10.4.4): a solution `φ_g` of the dual problem for a
`V`-elliptic form satisfies `‖φ_g‖ ≤ (‖ι‖/c₀) ‖g‖`.  This is what bounds the supremum in
(10.4.5). -/
theorem norm_le_of_dualProblem (hc₀ : 0 < c₀) (ha : a.IsEllipticWith c₀) (ι : V →L[ℝ] H) {g : H}
    {φ : V} (hφ : DualProblem a ι g φ) : ‖φ‖ ≤ ‖ι‖ / c₀ * ‖g‖ := by
  have hkey : c₀ * ‖φ‖ ^ 2 ≤ ‖ι‖ * ‖φ‖ * ‖g‖ := by
    refine (ha φ).trans ?_
    rw [hφ φ]
    exact (real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (ι.le_opNorm φ) (norm_nonneg g))
  rcases eq_or_lt_of_le (norm_nonneg φ) with h0 | h0
  · rw [← h0]
    positivity
  · rw [div_mul_eq_mul_div, le_div_iff₀ hc₀]
    nlinarith [hkey, h0]

/-- The supremum in (10.4.5) is finite: the dual solutions are approximated from `V_h` at least as
well as by `0`, and their norms are bounded by `(‖ι‖/c₀) ‖g‖`. -/
private theorem bddAbove_dualRatio (hc₀ : 0 < c₀) (ha : a.IsEllipticWith c₀) (ι : V →L[ℝ] H)
    (Vh : Submodule ℝ V) {φ : H → V} (hφ : ∀ g, DualProblem a ι g (φ g)) :
    BddAbove (Set.range fun g : {g : H // g ≠ 0} =>
      (⨅ vh : Vh, ‖φ (g : H) - (vh : V)‖) / ‖(g : H)‖) := by
  refine ⟨‖ι‖ / c₀, Set.forall_mem_range.2 fun g => ?_⟩
  have hg : (0 : ℝ) < ‖(g : H)‖ := norm_pos_iff.mpr g.2
  have hzero : (⨅ vh : Vh, ‖φ (g : H) - (vh : V)‖) ≤ ‖φ (g : H)‖ := by
    refine (ciInf_le (bddBelow_norm_sub _ _) (⟨0, Vh.zero_mem⟩ : Vh)).trans_eq ?_
    simp
  rw [div_le_iff₀ hg]
  exact hzero.trans (norm_le_of_dualProblem hc₀ ha ι (hφ (g : H)))

/-- **Theorem 10.4.3**, the Aubin–Nitsche lemma, (10.4.5).  For a bounded, `V`-elliptic form `a`,
`u` the solution of (10.4.1), `u_h` the Galerkin solution on `V_h ⊆ V`, and `φ_g` a solution of the
dual problem (10.4.4) for each datum `g ∈ H`,

  `‖ι (u − u_h)‖_H ≤ M ‖u − u_h‖_V · sup_{g ≠ 0} (1/‖g‖_H) inf_{v_h ∈ V_h} ‖φ_g − v_h‖_V`.

The duality argument itself is the backbone's `norm_map_sq_le_of_dual`; ellipticity enters only to
make the supremum finite (`bddAbove_dualRatio`). -/
theorem theorem_10_4_3 (hM : a.IsBoundedWith M) (hc₀ : 0 < c₀) (ha : a.IsEllipticWith c₀)
    (ι : V →L[ℝ] H) (hu : ∀ v, a u v = ℓ v) (huh : GalerkinProblem a ℓ Vh uh) {φ : H → V}
    (hφ : ∀ g, DualProblem a ι g (φ g)) :
    ‖ι (u - uh)‖ ≤ M * ‖u - uh‖ *
      ⨆ g : {g : H // g ≠ 0}, (⨅ vh : Vh, ‖φ (g : H) - (vh : V)‖) / ‖(g : H)‖ := by
  set e := u - uh with he
  set S := ⨆ g : {g : H // g ≠ 0}, (⨅ vh : Vh, ‖φ (g : H) - (vh : V)‖) / ‖(g : H)‖ with hS
  have hbdd := bddAbove_dualRatio hc₀ ha ι Vh hφ
  have hS0 : 0 ≤ S := by
    refine Real.iSup_nonneg fun g => ?_
    exact div_nonneg (Real.iInf_nonneg fun _ => norm_nonneg _) (norm_nonneg _)
  have hMe : 0 ≤ M * ‖e‖ := by
    rcases eq_or_lt_of_le (norm_nonneg e) with h | h
    · simp [← h]
    · nlinarith [abs_nonneg (a e e), hM e e]
  have horth : ∀ v ∈ Vh, a e v = 0 := fun v hv => Ch09.galerkin_orthogonality hM hu huh hv
  rcases eq_or_lt_of_le (norm_nonneg (ι e)) with h0 | h0
  · rw [← h0]
    positivity
  -- The pointwise duality bound, for every `v_h ∈ V_h`.
  have hpt : ∀ vh : Vh, ‖ι e‖ ^ 2 ≤ M * ‖e‖ * ‖φ (ι e) - (vh : V)‖ := fun vh =>
    norm_map_sq_le_of_dual (BilinForm.isBoundedWith_toCLM hM) ι horth (hφ (ι e)) vh.2
  have hMe0 : 0 < M * ‖e‖ := by
    rcases eq_or_lt_of_le hMe with h | h
    · exfalso
      have hz := hpt ⟨0, Vh.zero_mem⟩
      rw [← h, zero_mul] at hz
      nlinarith [h0]
    · exact h
  -- Take the infimum on the right.
  have hinf : ‖ι e‖ ^ 2 ≤ M * ‖e‖ * ⨅ vh : Vh, ‖φ (ι e) - (vh : V)‖ := by
    rw [← div_le_iff₀' hMe0]
    refine le_ciInf fun vh => ?_
    rw [div_le_iff₀' hMe0]
    exact hpt vh
  -- and bound that infimum by `S ‖ι e‖`, which is the definition of the supremum.
  have hratio : (⨅ vh : Vh, ‖φ (ι e) - (vh : V)‖) / ‖ι e‖ ≤ S :=
    le_ciSup hbdd (⟨ι e, norm_pos_iff.mp h0⟩ : {g : H // g ≠ 0})
  rw [div_le_iff₀ h0] at hratio
  nlinarith [hinf, hratio, hMe0, h0]

/-- **Corollary 10.4.4**, with its regularity hypothesis made abstract: if the dual solutions can
be approximated from `V_h` to within `δ ‖g‖_H`, then

  `‖ι (u − u_h)‖_H ≤ M δ ‖u − u_h‖_V`.

In the book `δ = c h` follows from the `H²` regularity bound (10.4.9) together with the
interpolation error estimate, neither of which is available here.  The approximation hypothesis is
stated with `Metric.infDist`, the form the backbone's `norm_map_le_of_dual_approx` takes it in;
`iInf_norm_sub_eq_infDist` identifies it with the book's `inf_{v_h ∈ V_h} ‖φ_g − v_h‖_V`. -/
theorem corollary_10_4_4_abstract (hM : a.IsBoundedWith M) (hδ : 0 ≤ δ) (ι : V →L[ℝ] H)
    (hu : ∀ v, a u v = ℓ v) (huh : GalerkinProblem a ℓ Vh uh)
    (hdual : ∀ g : H, ∃ φ : V, DualProblem a ι g φ ∧
      Metric.infDist φ (Vh : Set V) ≤ δ * ‖g‖) :
    ‖ι (u - uh)‖ ≤ M * δ * ‖u - uh‖ :=
  norm_map_le_of_dual_approx (BilinForm.isBoundedWith_toCLM hM) hδ ι
    (fun _ hv => Ch09.galerkin_orthogonality hM hu huh hv) hdual

end Ch10

end AtkinsonHan

import Numlib.Analysis.Calculus.CurvilinearLaplacian
import Numlib.Variational.AubinNitsche
import NumlibSurface.AtkinsonHan.Chapter09.Section01

/-!
# Atkinson–Han §10.4: the Aubin–Nitsche lemma

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §10.4.

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
* `exercise_10_4_5_polar` and `exercise_10_4_5_spherical` — Exercise 10.4.5, the Laplacian in
  polar coordinates on `ℝ²` and in spherical coordinates on `ℝ³`.

## Not formalized here

Theorem 10.4.1, the convergence order `‖u − u_h‖_{1,Ω} ≤ c h^k |u|_{k+1,Ω}` of the finite element
method; Corollary 10.4.4 in its stated form, whose hypothesis (10.4.9) is an `H²` elliptic
regularity bound; and (10.4.11).  Each is a Sobolev statement: 10.4.1 is Céa's inequality together
with the interpolation error estimate of §10.3 (Theorem 10.3.9), whose *abstract* half — Galerkin
solutions on a monotone family of subspaces with dense union converge — is already
`Chapter09.corollary_9_1_4`, so what is missing is only the density of the finite element spaces in
`H¹`.  The abstract half of Corollary 10.4.4, in which the approximation power of the dual
solutions is a hypothesis rather than a consequence of regularity, is `corollary_10_4_4_abstract`.

Exercises 10.4.1–4.4 and 10.4.6 and Example 10.4.2 all name a domain.

The rest of the chapter is *not* out of scope, and the sections that hold it say what they hold:
`Chapter10.Section01` (the §10.1 algebra), `Chapter10.Section02` (Lemma 10.2.2) and
`Chapter10.Section03` (Theorem 10.3.1, Example 10.3.2, Definition 10.3.6).
-/

open scoped Laplacian

namespace AtkinsonHan

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H]

/-- The dual problem (10.4.4) for the datum `g ∈ H`: `φ ∈ V` with `a(v, φ) = (g, ι v)_H` for every
`v ∈ V`.  It is the variational problem for the adjoint form, so on a `V`-elliptic `a` it is
uniquely solvable by Lax–Milgram (Theorem 8.3.4) applied to `a(·, ·)ᵀ`. -/
def DualProblem (a : BilinForm V) (ι : V →L[ℝ] H) (g : H) (φ : V) : Prop :=
  ∀ v : V, a v φ = inner ℝ (ι v) g

namespace Chapter10

variable {a : BilinForm V} {ℓ : StrongDual ℝ V} {M c₀ δ : ℝ} {Vh : Submodule ℝ V} {u uh : V}

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
  have horth : ∀ v ∈ Vh, a e v = 0 := fun v hv => Chapter09.galerkin_orthogonality hM hu huh hv
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
`AtkinsonHan.Chapter09.iInf_norm_sub_eq_infDist` identifies it with the book's
`inf_{v_h ∈ V_h} ‖φ_g − v_h‖_V`. -/
theorem corollary_10_4_4_abstract (hM : a.IsBoundedWith M) (hδ : 0 ≤ δ) (ι : V →L[ℝ] H)
    (hu : ∀ v, a u v = ℓ v) (huh : GalerkinProblem a ℓ Vh uh)
    (hdual : ∀ g : H, ∃ φ : V, DualProblem a ι g φ ∧
      Metric.infDist φ (Vh : Set V) ≤ δ * ‖g‖) :
    ‖ι (u - uh)‖ ≤ M * δ * ‖u - uh‖ :=
  norm_map_le_of_dual_approx (BilinForm.isBoundedWith_toCLM hM) hδ ι
    (fun _ hv => Chapter09.galerkin_orthogonality hM hu huh hv) hdual


/-! ### Exercise 10.4.5: the Laplacian in polar and in spherical coordinates

The exercise is the chain rule on a `C²` function, not a Sobolev statement.  The plane and
three-space are `EuclideanSpace ℝ (Fin 2)` and `EuclideanSpace ℝ (Fin 3)`, and `Δ` is Mathlib's
`InnerProductSpace.laplacian`; the identities themselves are
`Curvilinear.laplacian_eq_polar` and `Curvilinear.laplacian_eq_spherical` of the backbone,
specialized to the standard orthonormal basis.

The book writes the two identities as identities of operators.  Here they are stated pointwise, at
one point of the domain, with the coordinate derivatives written as derivatives of the composition
of `f` with the coordinate curve through that point — which is what "`∂/∂r`" means. -/

/-- The point of `ℝ²` with polar coordinates `(r, θ)`: `x₁ = r cos θ` and `x₂ = r sin θ`. -/
noncomputable def polarPt (r θ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[r * Real.cos θ, r * Real.sin θ]

/-- The book's polar point is the backbone's `Curvilinear.polarPoint` in the standard frame. -/
theorem polarPt_eq (r θ : ℝ) :
    polarPt r θ = Curvilinear.polarPoint (EuclideanSpace.basisFun (Fin 2) ℝ) r θ := by
  ext i
  fin_cases i <;> simp [polarPt, Curvilinear.polarPoint, EuclideanSpace.basisFun_apply]

/-- **Exercise 10.4.5** in `ℝ²`: in polar coordinates `x₁ = r cos θ`, `x₂ = r sin θ` the Laplacian
takes the form

  `Δ = ∂²/∂r² + r⁻¹ ∂/∂r + r⁻² ∂²/∂θ²`. -/
theorem exercise_10_4_5_polar {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : ContDiff ℝ 2 f)
    {r : ℝ} (hr : r ≠ 0) (θ : ℝ) :
    Δ f (polarPt r θ)
      = deriv (deriv fun s : ℝ => f (polarPt s θ)) r
        + r⁻¹ * deriv (fun s : ℝ => f (polarPt s θ)) r
        + (r ^ 2)⁻¹ * deriv (deriv fun ψ : ℝ => f (polarPt r ψ)) θ := by
  simp only [polarPt_eq]
  simpa using Curvilinear.laplacian_eq_polar _ hf hr θ

/-- The point of `ℝ³` with spherical coordinates `(r, θ, φ)`: `x₁ = r cos θ sin φ`,
`x₂ = r sin θ sin φ` and `x₃ = r cos φ`. -/
noncomputable def sphericalPt (r θ φ : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  !₂[r * Real.cos θ * Real.sin φ, r * Real.sin θ * Real.sin φ, r * Real.cos φ]

/-- The book's spherical point is the backbone's `Curvilinear.sphericalPoint` in the standard
frame. -/
theorem sphericalPt_eq (r θ φ : ℝ) :
    sphericalPt r θ φ = Curvilinear.sphericalPoint (EuclideanSpace.basisFun (Fin 3) ℝ) r θ φ := by
  ext i
  fin_cases i <;> simp [sphericalPt, Curvilinear.sphericalPoint, EuclideanSpace.basisFun_apply]

/-- **Exercise 10.4.5** in `ℝ³`: in spherical coordinates `x₁ = r cos θ sin φ`,
`x₂ = r sin θ sin φ`, `x₃ = r cos φ` the Laplacian takes the form

  `Δ = ∂²/∂r² + (2/r) ∂/∂r + r⁻² ((sin φ)⁻² ∂²/∂θ² + cot φ ∂/∂φ + ∂²/∂φ²)`. -/
theorem exercise_10_4_5_spherical {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : ContDiff ℝ 2 f)
    {r φ : ℝ} (hr : r ≠ 0) (hφ : Real.sin φ ≠ 0) (θ : ℝ) :
    Δ f (sphericalPt r θ φ)
      = deriv (deriv fun s : ℝ => f (sphericalPt s θ φ)) r
        + (2 / r) * deriv (fun s : ℝ => f (sphericalPt s θ φ)) r
        + (r ^ 2)⁻¹ * ((Real.sin φ ^ 2)⁻¹ * deriv (deriv fun ψ : ℝ => f (sphericalPt r ψ φ)) θ
            + (Real.cos φ / Real.sin φ) * deriv (fun χ : ℝ => f (sphericalPt r θ χ)) φ
            + deriv (deriv fun χ : ℝ => f (sphericalPt r θ χ)) φ) := by
  simp only [sphericalPt_eq]
  simpa using Curvilinear.laplacian_eq_spherical _ hf hr hφ θ

end Chapter10

end AtkinsonHan
